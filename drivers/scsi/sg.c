// SPDX-License-Identifier: GPL-2.0-or-later
/*
 *  History:
 *  Started: Aug 9 by Lawrence Foard (entropy@world.std.com),
 *           to allow user process control of SCSI devices.
 *  Development Sponsored by Killy Corp. NY NY   [guess: 1992]
 *
 * Original driver (sg.c):
 *        Copyright (C) 1992 Lawrence Foard
 * Version 2 and 3 extensions to driver:
 *        Copyright (C) 1998 - 2019 Douglas Gilbert
 */

static int sg_version_num = 30901;  /* [x]xyyzz where [x] empty when x=0 */
#define SG_VERSION_STR "3.9.01"		/* [x]x.[y]y.zz */
static char *sg_version_date = "20190606";

#include <linux/module.h>

#include <linux/fs.h>
#include <linux/kernel.h>
#include <linux/sched.h>
#include <linux/string.h>
#include <linux/mm.h>
#include <linux/errno.h>
#include <linux/mtio.h>
#include <linux/ioctl.h>
#include <linux/slab.h>
#include <linux/fcntl.h>
#include <linux/init.h>
#include <linux/poll.h>
#include <linux/moduleparam.h>
#include <linux/cdev.h>
#include <linux/idr.h>
#include <linux/seq_file.h>
#include <linux/blkdev.h>
#include <linux/delay.h>
#include <linux/blktrace_api.h>
#include <linux/mutex.h>
#include <linux/atomic.h>
#include <linux/ratelimit.h>
#include <linux/uio.h>
#include <linux/cred.h> /* for sg_check_file_access() */
#include <linux/proc_fs.h>
#include <linux/xarray.h>

#include "scsi.h"
#include <scsi/scsi_dbg.h>
#include <scsi/scsi_host.h>
#include <scsi/scsi_driver.h>
#include <scsi/scsi_ioctl.h>
#include <scsi/sg.h>

#include "scsi_logging.h"

#define SG_ALLOW_DIO_DEF 0

#define SG_MAX_DEVS 32768

/* Comment out the following line to compile out SCSI_LOGGING stuff */
#define SG_DEBUG 1

#if !IS_ENABLED(SG_DEBUG)
#if IS_ENABLED(DEBUG)	/* If SG_DEBUG not defined, check for DEBUG */
#define SG_DEBUG DEBUG
#endif
#endif

/* SG_MAX_CDB_SIZE should be 260 (spc4r37 section 3.1.30) however the type
 * of sg_io_hdr::cmd_len can only represent 255. All SCSI commands greater
 * than 16 bytes are "variable length" whose length is a multiple of 4, so:
 */
#define SG_MAX_CDB_SIZE 252

/* Following enum contains the states of sg_request::rq_st */
enum sg_rq_state {	/* N.B. sg_rq_state_arr assumes SG_RS_AWAIT_RCV==2 */
	SG_RS_INACTIVE = 0,	/* request not in use (e.g. on fl) */
	SG_RS_INFLIGHT,		/* active: cmd/req issued, no response yet */
	SG_RS_AWAIT_RCV,	/* have response from LLD, awaiting receive */
	SG_RS_RCV_DONE,		/* receive is ongoing or done */
	SG_RS_BUSY,		/* temporary state should rarely be seen */
};

#define SG_TIME_UNIT_MS 0	/* milliseconds */
#define SG_DEF_TIME_UNIT SG_TIME_UNIT_MS
#define SG_DEFAULT_TIMEOUT mult_frac(SG_DEFAULT_TIMEOUT_USER, HZ, USER_HZ)
#define SG_FD_Q_AT_HEAD 0
#define SG_DEFAULT_Q_AT SG_FD_Q_AT_HEAD /* for backward compatibility */
#define SG_FL_MMAP_DIRECT (SG_FLAG_MMAP_IO | SG_FLAG_DIRECT_IO)

/* Only take lower 4 bits of driver byte, all host byte and sense byte */
#define SG_ML_RESULT_MSK 0x0fff00ff	/* mid-level's 32 bit result value */

#define SG_PACK_ID_WILDCARD (-1)

#define SG_ADD_RQ_MAX_RETRIES 40	/* to stop infinite _trylock(s) */

/* Bit positions (flags) for sg_request::frq_bm bitmask follow */
#define SG_FRQ_IS_ORPHAN	1	/* owner of request gone */
#define SG_FRQ_SYNC_INVOC	2	/* synchronous (blocking) invocation */
#define SG_FRQ_NO_US_XFER	3	/* no user space transfer of data */
#define SG_FRQ_DEACT_ORPHAN	6	/* not keeping orphan so de-activate */
#define SG_FRQ_BLK_PUT_REQ	8	/* set when blk_put_request() called */

/* Bit positions (flags) for sg_fd::ffd_bm bitmask follow */
#define SG_FFD_FORCE_PACKID	0	/* receive only given pack_id/tag */
#define SG_FFD_CMD_Q		1	/* clear: only 1 active req per fd */
#define SG_FFD_KEEP_ORPHAN	2	/* policy for this fd */
#define SG_FFD_MMAP_CALLED	3	/* mmap(2) system call made on fd */
#define SG_FFD_Q_AT_TAIL	5	/* set: queue reqs at tail of blk q */

/* Bit positions (flags) for sg_device::fdev_bm bitmask follow */
#define SG_FDEV_EXCLUDE		0	/* have fd open with O_EXCL */
#define SG_FDEV_DETACHING	1	/* may be unexpected device removal */
#define SG_FDEV_LOG_SENSE	2	/* set by ioctl(SG_SET_DEBUG) */

/* xarray 'mark's allow sub-lists within main array/list. */
#define SG_XA_RQ_FREE XA_MARK_0	/* xarray sets+clears */
#define SG_XA_RQ_INACTIVE XA_MARK_1
#define SG_XA_RQ_AWAIT XA_MARK_2

int sg_big_buff = SG_DEF_RESERVED_SIZE;
/*
 * This variable is accessible via /proc/scsi/sg/def_reserved_size . Each
 * time sg_open() is called a sg_request of this size (or less if there is
 * not enough memory) will be reserved for use by this file descriptor.
 */
static int def_reserved_size = -1;	/* picks up init parameter */
static int sg_allow_dio = SG_ALLOW_DIO_DEF;

static int scatter_elem_sz = SG_SCATTER_SZ;

#define SG_DEF_SECTOR_SZ 512

static int sg_add_device(struct device *, struct class_interface *);
static void sg_remove_device(struct device *, struct class_interface *);

static DEFINE_IDR(sg_index_idr);
static DEFINE_RWLOCK(sg_index_lock); /* Also used to lock fd list for device */

static struct class_interface sg_interface = {
	.add_dev        = sg_add_device,
	.remove_dev     = sg_remove_device,
};

/* Subset of sg_io_hdr found in <scsi/sg.h>, has only [i] and [i->o] fields */
struct sg_slice_hdr3 {
	int interface_id;
	int dxfer_direction;
	u8 cmd_len;
	u8 mx_sb_len;
	u16 iovec_count;
	unsigned int dxfer_len;
	void __user *dxferp;
	u8 __user *cmdp;
	void __user *sbp;
	unsigned int timeout;
	unsigned int flags;
	int pack_id;
	void __user *usr_ptr;
};

struct sg_scatter_hold {     /* holding area for scsi scatter gather info */
	struct page **pages;	/* num_sgat element array of struct page* */
	int buflen;		/* capacity in bytes (dlen<=buflen) */
	int dlen;		/* current valid data length of this req */
	u16 page_order;		/* byte_len = (page_size*(2**page_order)) */
	u16 num_sgat;		/* actual number of scatter-gather segments */
};

struct sg_device;		/* forward declarations */
struct sg_fd;

struct sg_request {	/* active SCSI command or inactive request */
	struct sg_scatter_hold sgat_h;	/* hold buffer, perhaps scatter list */
	struct sg_slice_hdr3 s_hdr3;  /* subset of sg_io_hdr */
	u8 sense_b[SCSI_SENSE_BUFFERSIZE];
	u32 duration;		/* cmd duration in milliseconds */
	u32 rq_flags;		/* hold user supplied flags */
	u32 rq_idx;		/* my index within parent's srp_arr */
	u32 rq_info;		/* info supplied by v3 and v4 interfaces */
	u32 rq_result;		/* packed scsi request result from LLD */
	int in_resid;		/* requested-actual byte count on data-in */
	int pack_id;		/* user provided packet identifier field */
	int sense_len;		/* actual sense buffer length (data-in) */
	atomic_t rq_st;		/* request state, holds a enum sg_rq_state */
	u8 cmd_opcode;		/* first byte of SCSI cdb */
	u64 start_ns;		/* starting point of command duration calc */
	unsigned long frq_bm[1];	/* see SG_FRQ_* defines above */
	struct sg_fd *parentfp;	/* pointer to owning fd, even when on fl */
	struct request *rq;	/* released in sg_rq_end_io(), bio kept */
	struct bio *bio;	/* kept until this req -->SG_RS_INACTIVE */
	struct execute_work ew_orph;	/* harvest orphan request */
};

struct sg_fd {		/* holds the state of a file descriptor */
	struct sg_device *parentdp;	/* owning device */
	wait_queue_head_t read_wait;	/* queue read until command done */
	struct mutex f_mutex;	/* serialize ioctls on this fd */
	int timeout;		/* defaults to SG_DEFAULT_TIMEOUT      */
	int timeout_user;	/* defaults to SG_DEFAULT_TIMEOUT_USER */
	u32 idx;		/* my index within parent's sfp_arr */
	atomic_t submitted;	/* number inflight or awaiting receive */
	atomic_t waiting;	/* number of requests awaiting receive */
	atomic_t req_cnt;	/* number of requests */
	int sgat_elem_sz;	/* initialized to scatter_elem_sz */
	unsigned long ffd_bm[1];	/* see SG_FFD_* defines above */
	pid_t tid;		/* thread id when opened */
	u8 next_cmd_len;	/* 0: automatic, >0: use on next write() */
	struct sg_request *rsv_srp;/* one reserve request per fd */
	struct fasync_struct *async_qp; /* used by asynchronous notification */
	struct xarray srp_arr;	/* xarray of sg_request object pointers */
	struct kref f_ref;
	struct execute_work ew_fd;  /* harvest all fd resources and lists */
};

struct sg_device { /* holds the state of each scsi generic device */
	struct scsi_device *device;
	wait_queue_head_t open_wait;    /* queue open() when O_EXCL present */
	struct mutex open_rel_lock;     /* held when in open() or release() */
	struct list_head sfds;
	int max_sgat_elems;     /* adapter's max number of elements in sgat */
	int max_sgat_sz;	/* max number of bytes in sgat list */
	u32 index;		/* device index number */
	atomic_t open_cnt;	/* count of opens (perhaps < num(sfds) ) */
	unsigned long fdev_bm[1];	/* see SG_FDEV_* defines above */
	struct gendisk *disk;
	struct cdev *cdev;
	struct xarray sfp_arr;
	struct kref d_ref;
};

struct sg_comm_wr_t {  /* arguments to sg_common_write() */
	int timeout;
	unsigned long frq_bm[1];	/* see SG_FRQ_* defines above */
	struct sg_io_hdr *h3p;
	u8 *cmnd;
};

/* tasklet or soft irq callback */
static void sg_rq_end_io(struct request *rq, blk_status_t status);
/* Declarations of other static functions used before they are defined */
static int sg_proc_init(void);
static int sg_start_req(struct sg_request *srp, u8 *cmd, int cmd_len,
			int dxfer_dir);
static void sg_finish_scsi_blk_rq(struct sg_request *srp);
static int sg_mk_sgat(struct sg_request *srp, struct sg_fd *sfp, int minlen);
static int sg_submit(struct file *filp, struct sg_fd *sfp,
		     struct sg_io_hdr *hp, bool sync,
		     struct sg_request **o_srp);
static struct sg_request *sg_common_write(struct sg_fd *sfp,
					  struct sg_comm_wr_t *cwrp);
static int sg_read_append(struct sg_request *srp, void __user *outp,
			  int num_xfer);
static void sg_remove_sgat(struct sg_request *srp);
static struct sg_fd *sg_add_sfp(struct sg_device *sdp);
static void sg_remove_sfp(struct kref *);
static struct sg_request *sg_find_srp_by_id(struct sg_fd *sfp, int pack_id);
static struct sg_request *sg_setup_req(struct sg_fd *sfp, int dxfr_len,
				       struct sg_comm_wr_t *cwrp);
static void sg_deact_request(struct sg_fd *sfp, struct sg_request *srp);
static struct sg_device *sg_get_dev(int dev);
static void sg_device_destroy(struct kref *kref);
static struct sg_request *sg_mk_srp_sgat(struct sg_fd *sfp, bool first,
					 int db_len);
static const char *sg_rq_st_str(enum sg_rq_state rq_st, bool long_str);

#define SG_WRITE_COUNT_LIMIT (32 * 1024 * 1024)

#define SZ_SG_HEADER ((int)sizeof(struct sg_header))	/* v1 and v2 header */
#define SZ_SG_IO_HDR ((int)sizeof(struct sg_io_hdr))	/* v3 header */
#define SZ_SG_REQ_INFO ((int)sizeof(struct sg_req_info))

#define SG_IS_DETACHING(sdp) test_bit(SG_FDEV_DETACHING, (sdp)->fdev_bm)
#define SG_HAVE_EXCLUDE(sdp) test_bit(SG_FDEV_EXCLUDE, (sdp)->fdev_bm)
#define SG_RS_ACTIVE(srp) (atomic_read(&(srp)->rq_st) != SG_RS_INACTIVE)

/*
 * Kernel needs to be built with CONFIG_SCSI_LOGGING to see log messages.
 * 'depth' is a number between 1 (most severe) and 7 (most noisy, most
 * information). All messages are logged as informational (KERN_INFO). In
 * the unexpected situation where sfp or sdp is NULL the macro reverts to
 * a pr_info and ignores SCSI_LOG_TIMEOUT and always prints to the log.
 * Example: this invocation: 'scsi_logging_level -s -T 3' will print
 * depth (aka level) 1 and 2 SG_LOG() messages.
 */

#define SG_PROC_DEBUG_SZ 8192

#if IS_ENABLED(CONFIG_SCSI_LOGGING) && IS_ENABLED(SG_DEBUG)
#define SG_LOG_BUFF_SZ 48
#define SG_LOG_ACTIVE 1

#define SG_LOG(depth, sfp, fmt, a...)					\
	do {								\
		char _b[SG_LOG_BUFF_SZ];				\
		int _tid = (current ? current->pid : -1);		\
		struct sg_fd *_fp = sfp;				\
		struct sg_device *_sdp = _fp ? _fp->parentdp : NULL;	\
									\
		if (likely(_sdp && _sdp->disk)) {			\
			snprintf(_b, sizeof(_b), "sg%u: tid=%d",	\
				 _sdp->index, _tid);			\
			SCSI_LOG_TIMEOUT(depth,				\
					 sdev_prefix_printk(KERN_INFO,	\
					 _sdp->device, _b, fmt, ##a));	\
		} else							\
			pr_info("sg: sdp or sfp NULL, " fmt, ##a);	\
	} while (0)
#else
#define SG_LOG(depth, sfp, fmt, a...) { }
#endif	/* end of CONFIG_SCSI_LOGGING && SG_DEBUG conditional */


/*
 * The SCSI interfaces that use read() and write() as an asynchronous variant of
 * ioctl(..., SG_IO, ...) are fundamentally unsafe, since there are lots of ways
 * to trigger read() and write() calls from various contexts with elevated
 * privileges. This can lead to kernel memory corruption (e.g. if these
 * interfaces are called through splice()) and privilege escalation inside
 * userspace (e.g. if a process with access to such a device passes a file
 * descriptor to a SUID binary as stdin/stdout/stderr).
 *
 * This function provides protection for the legacy API by restricting the
 * calling context.
 */
static int
sg_check_file_access(struct file *filp, const char *caller)
{
	if (filp->f_cred != current_real_cred()) {
		pr_err_once("%s: process %d (%s) changed security contexts after opening file descriptor, this is not allowed.\n",
			caller, task_tgid_vnr(current), current->comm);
		return -EPERM;
	}
	if (uaccess_kernel()) {
		pr_err_once("%s: process %d (%s) called from kernel context, this is not allowed.\n",
			caller, task_tgid_vnr(current), current->comm);
		return -EACCES;
	}
	return 0;
}

static int
sg_wait_open_event(struct sg_device *sdp, bool o_excl)
{
	int res = 0;

	if (o_excl) {
		while (atomic_read(&sdp->open_cnt) > 0) {
			mutex_unlock(&sdp->open_rel_lock);
			res = wait_event_interruptible
					(sdp->open_wait,
					 (SG_IS_DETACHING(sdp) ||
					  atomic_read(&sdp->open_cnt) == 0));
			mutex_lock(&sdp->open_rel_lock);

			if (res) /* -ERESTARTSYS */
				return res;
			if (SG_IS_DETACHING(sdp))
				return -ENODEV;
		}
	} else {
		while (SG_HAVE_EXCLUDE(sdp)) {
			mutex_unlock(&sdp->open_rel_lock);
			res = wait_event_interruptible
					(sdp->open_wait,
					 (SG_IS_DETACHING(sdp) ||
					  !SG_HAVE_EXCLUDE(sdp)));
			mutex_lock(&sdp->open_rel_lock);

			if (res) /* -ERESTARTSYS */
				return res;
			if (SG_IS_DETACHING(sdp))
				return -ENODEV;
		}
	}

	return res;
}

/*
 * scsi_block_when_processing_errors() returns 0 when dev was taken offline by
 * error recovery, 1 otherwise (i.e. okay). Even if in error recovery, let
 * user continue if O_NONBLOCK set. Permits SCSI commands to be issued during
 * error recovery. Tread carefully.
 * Returns 0 for ok (i.e. allow), -EPROTO if sdp is NULL, otherwise -ENXIO .
 */
static inline int
sg_allow_if_err_recovery(struct sg_device *sdp, bool non_block)
{
	if (!sdp)
		return -EPROTO;
	if (SG_IS_DETACHING(sdp))
		return -ENODEV;
	if (non_block)
		return 0;
	if (likely(scsi_block_when_processing_errors(sdp->device)))
		return 0;
	return -ENXIO;
}

/*
 * Corresponds to the open() system call on sg devices. Implements O_EXCL on
 * a per device basis using 'open_cnt'. If O_EXCL and O_NONBLOCK and there is
 * already a sg handle open on this device then it fails with an errno of
 * EBUSY. Without the O_NONBLOCK flag then this thread enters an interruptible
 * wait until the other handle(s) are closed.
 */
static int
sg_open(struct inode *inode, struct file *filp)
{
	bool o_excl, non_block;
	int min_dev = iminor(inode);
	int op_flags = filp->f_flags;
	int res;
	__maybe_unused int o_count;
	struct sg_device *sdp;
	struct sg_fd *sfp;

	nonseekable_open(inode, filp);
	o_excl = !!(op_flags & O_EXCL);
	non_block = !!(op_flags & O_NONBLOCK);
	if (o_excl && ((op_flags & O_ACCMODE) == O_RDONLY))
		return -EPERM; /* Can't lock it with read only access */
	sdp = sg_get_dev(min_dev);	/* increments sdp->d_ref */
	if (IS_ERR(sdp))
		return PTR_ERR(sdp);

	/* This driver's module count bumped by fops_get in <linux/fs.h> */
	/* Prevent the device driver from vanishing while we sleep */
	res = scsi_device_get(sdp->device);
	if (res)
		goto sg_put;

	res = scsi_autopm_get_device(sdp->device);
	if (res)
		goto sdp_put;

	res = sg_allow_if_err_recovery(sdp, non_block);
	if (res)
		goto error_out;

	mutex_lock(&sdp->open_rel_lock);
	if (op_flags & O_NONBLOCK) {
		if (o_excl) {
			if (atomic_read(&sdp->open_cnt) > 0) {
				res = -EBUSY;
				goto error_mutex_locked;
			}
		} else {
			if (SG_HAVE_EXCLUDE(sdp)) {
				res = -EBUSY;
				goto error_mutex_locked;
			}
		}
	} else {
		res = sg_wait_open_event(sdp, o_excl);
		if (res) /* -ERESTARTSYS or -ENODEV */
			goto error_mutex_locked;
	}

	/* N.B. at this point we are holding the open_rel_lock */
	if (o_excl)
		set_bit(SG_FDEV_EXCLUDE, sdp->fdev_bm);

	o_count = atomic_inc_return(&sdp->open_cnt);
	sfp = sg_add_sfp(sdp);		/* increments sdp->d_ref */
	if (IS_ERR(sfp)) {
		atomic_dec(&sdp->open_cnt);
		res = PTR_ERR(sfp);
		goto out_undo;
	}

	filp->private_data = sfp;
	mutex_unlock(&sdp->open_rel_lock);
	SG_LOG(3, sfp, "%s: minor=%d, op_flags=0x%x; %s count after=%d%s\n",
	       __func__, min_dev, op_flags, "device open", o_count,
	       ((op_flags & O_NONBLOCK) ? " O_NONBLOCK" : ""));

	res = 0;
sg_put:
	kref_put(&sdp->d_ref, sg_device_destroy);
	/* if success, sdp->d_ref is incremented twice, decremented once */
	return res;

out_undo:
	if (o_excl) {		/* undo if error */
		clear_bit(SG_FDEV_EXCLUDE, sdp->fdev_bm);
		wake_up_interruptible(&sdp->open_wait);
	}
error_mutex_locked:
	mutex_unlock(&sdp->open_rel_lock);
error_out:
	scsi_autopm_put_device(sdp->device);
sdp_put:
	scsi_device_put(sdp->device);
	goto sg_put;
}

/* Release resources associated with a successful sg_open()
 * Returns 0 on success, else a negated errno value */
static int
sg_release(struct inode *inode, struct file *filp)
{
	int o_count;
	struct sg_device *sdp;
	struct sg_fd *sfp;

	sfp = filp->private_data;
	sdp = sfp ? sfp->parentdp : NULL;
	if (unlikely(!sdp))
		return -ENXIO;

	mutex_lock(&sdp->open_rel_lock);
	o_count = atomic_read(&sdp->open_cnt);
	SG_LOG(3, sfp, "%s: open count before=%d\n", __func__, o_count);
	scsi_autopm_put_device(sdp->device);
	kref_put(&sfp->f_ref, sg_remove_sfp);

	/*
	 * Possibly many open()s waiting on exlude clearing, start many;
	 * only open(O_EXCL)'s wait when open_cnt<2 and only start one.
	 */
	/* possibly many open()s waiting on exlude clearing, start many;
	 * only open(O_EXCL)s wait on 0==open_cnt so only start one */
	if (test_and_clear_bit(SG_FDEV_EXCLUDE, sdp->fdev_bm))
		wake_up_interruptible_all(&sdp->open_wait);
	else if (o_count < 2)
		wake_up_interruptible(&sdp->open_wait);
	mutex_unlock(&sdp->open_rel_lock);
	return 0;
}

static ssize_t
sg_write(struct file *filp, const char __user *p, size_t count, loff_t *ppos)
{
	bool get_v3_hdr;
	int mxsize, cmd_size, input_size, res;
	u8 opcode;
	struct sg_device *sdp;
	struct sg_fd *sfp;
	struct sg_request *srp;
	u8 cmnd[SG_MAX_CDB_SIZE];
	struct sg_header ov2hdr;
	struct sg_io_hdr v3hdr;
	struct sg_header *ohp = &ov2hdr;
	struct sg_io_hdr *h3p = &v3hdr;
	struct sg_comm_wr_t cwr;

	res = sg_check_file_access(filp, __func__);
	if (res)
		return res;

	sfp = filp->private_data;
	sdp = sfp->parentdp;
	SG_LOG(3, sfp, "%s: write(3rd arg) count=%d\n", __func__, (int)count);
	res = sg_allow_if_err_recovery(sdp, !!(filp->f_flags & O_NONBLOCK));
	if (res)
		return res;
	if (count < SZ_SG_HEADER || count > SG_WRITE_COUNT_LIMIT)
		return -EIO;
#ifdef CONFIG_COMPAT
	if (in_compat_syscall())
		get_v3_hdr = (count == sizeof(struct compat_sg_io_hdr));
	else
		get_v3_hdr = (count == sizeof(struct sg_io_hdr));
#else
	get_v3_hdr = (count == sizeof(struct sg_io_hdr));
#endif
	if (get_v3_hdr) {
		if (get_sg_io_hdr(h3p, p))
			return -EFAULT;
	} else {
		if (copy_from_user(ohp, p, SZ_SG_HEADER))
			return -EFAULT;
		if (ohp->reply_len < 0) {	/* not v2, may be v3 */
			bool lt = false;

#ifdef CONFIG_COMPAT
			if (in_compat_syscall())
				lt = (count < sizeof(struct compat_sg_io_hdr));
			else
				lt = (count < sizeof(struct sg_io_hdr));
#else
			lt = (count < sizeof(struct sg_io_hdr));
#endif
			if (lt)
				return -EIO;
			get_v3_hdr = true;
			if (get_sg_io_hdr(h3p, p))
				return -EFAULT;
		}
	}
	if (get_v3_hdr) {
		/* v3 dxfer_direction_s are all negative values by design */
		if (h3p->dxfer_direction >= 0) {	/* so it is not v3 */
			memcpy(ohp, h3p, count);
			goto to_v2;
		}
		if (h3p->interface_id != 'S') {
			pr_info_once("sg: %s: v3 interface only here\n",
				     __func__);
			return -EPERM;
		}
		res = sg_submit(filp, sfp, h3p, false, NULL);
		return res < 0 ? res : (int)count;
	}
to_v2:
	/* v1 and v2 interfaces processed below this point */
	if (count < (SZ_SG_HEADER + 6))
		return -EIO;    /* minimum scsi command length is 6 bytes */
	p += SZ_SG_HEADER;
	if (get_user(opcode, p))
		return -EFAULT;
	mutex_lock(&sfp->f_mutex);
	if (sfp->next_cmd_len > 0) {
		cmd_size = sfp->next_cmd_len;
		sfp->next_cmd_len = 0;	/* reset, only this write() effected */
	} else {
		cmd_size = COMMAND_SIZE(opcode);  /* old: SCSI command group */
		if (opcode >= 0xc0 && ohp->twelve_byte)
			cmd_size = 12;
	}
	mutex_unlock(&sfp->f_mutex);
	SG_LOG(4, sfp, "%s:   scsi opcode=0x%02x, cmd_size=%d\n", __func__,
	       (unsigned int)opcode, cmd_size);
	input_size = count - cmd_size;
	mxsize = max_t(int, input_size, ohp->reply_len);
	mxsize -= SZ_SG_HEADER;
	input_size -= SZ_SG_HEADER;
	if (input_size < 0)
		return -EIO; /* Insufficient bytes passed for this command. */
	memset(h3p, 0, sizeof(*h3p));
	h3p->interface_id = '\0';/* indicate v1 or v2 interface (tunnelled) */
	h3p->cmd_len = (u8)cmd_size;
	h3p->iovec_count = 0;
	h3p->mx_sb_len = 0;
	if (input_size > 0)
		h3p->dxfer_direction = (ohp->reply_len > SZ_SG_HEADER) ?
		    SG_DXFER_TO_FROM_DEV : SG_DXFER_TO_DEV;
	else
		h3p->dxfer_direction = (mxsize > 0) ? SG_DXFER_FROM_DEV :
						      SG_DXFER_NONE;
	h3p->dxfer_len = mxsize;
	if (h3p->dxfer_direction == SG_DXFER_TO_DEV ||
	    h3p->dxfer_direction == SG_DXFER_TO_FROM_DEV)
		h3p->dxferp = (u8 __user *)p + cmd_size;
	else
		h3p->dxferp = NULL;
	h3p->sbp = NULL;
	h3p->timeout = ohp->reply_len;	/* structure abuse ... */
	h3p->flags = input_size;	/* structure abuse ... */
	h3p->pack_id = ohp->pack_id;
	h3p->usr_ptr = NULL;
	cmnd[0] = opcode;
	if (copy_from_user(cmnd + 1, p + 1, cmd_size - 1))
		return -EFAULT;
	/*
	 * SG_DXFER_TO_FROM_DEV is functionally equivalent to SG_DXFER_FROM_DEV,
	 * but it is possible that the app intended SG_DXFER_TO_DEV, because
	 * there is a non-zero input_size, so emit a warning.
	 */
	if (h3p->dxfer_direction == SG_DXFER_TO_FROM_DEV) {
		printk_ratelimited
			(KERN_WARNING
			 "%s: data in/out %d/%d bytes for SCSI command 0x%x-- guessing data in;\n"
			 "   program %s not setting count and/or reply_len properly\n",
			 __func__, ohp->reply_len - (int)SZ_SG_HEADER,
			 input_size, (unsigned int)cmnd[0], current->comm);
	}
	cwr.frq_bm[0] = 0;	/* initial state clear for all req flags */
	cwr.h3p = h3p;
	cwr.timeout = sfp->timeout;
	cwr.cmnd = cmnd;
	srp = sg_common_write(sfp, &cwr);
	return (IS_ERR(srp)) ? PTR_ERR(srp) : (int)count;
}

static inline int
sg_chk_mmap(struct sg_fd *sfp, int rq_flags, int len)
{
	if (!xa_empty(&sfp->srp_arr))
		return -EBUSY;  /* already active requests on fd */
	if (len > sfp->rsv_srp->sgat_h.buflen)
		return -ENOMEM; /* MMAP_IO size must fit in reserve */
	if (rq_flags & SG_FLAG_DIRECT_IO)
		return -EINVAL; /* not both MMAP_IO and DIRECT_IO */
	return 0;
}

static int
sg_fetch_cmnd(struct file *filp, struct sg_fd *sfp, const u8 __user *u_cdbp,
	      int len, u8 *cdbp)
{
	if (!u_cdbp || len < 6 || len > SG_MAX_CDB_SIZE)
		return -EMSGSIZE;
	if (copy_from_user(cdbp, u_cdbp, len))
		return -EFAULT;
	if (O_RDWR != (filp->f_flags & O_ACCMODE)) {	/* read-only */
		switch (sfp->parentdp->device->type) {
		case TYPE_DISK:
		case TYPE_RBC:
		case TYPE_ZBC:
			return blk_verify_command(cdbp, filp->f_mode);
		default:	/* SSC, SES, etc cbd_s may differ from SBC */
			break;
		}
	}
	return 0;
}

static int
sg_submit(struct file *filp, struct sg_fd *sfp, struct sg_io_hdr *hp,
	  bool sync, struct sg_request **o_srp)
{
	int res, timeout;
	unsigned long ul_timeout;
	struct sg_request *srp;
	struct sg_comm_wr_t cwr;
	u8 cmnd[SG_MAX_CDB_SIZE];

	/* now doing v3 blocking (sync) or non-blocking submission */
	if (hp->flags & SG_FLAG_MMAP_IO) {
		res = sg_chk_mmap(sfp, hp->flags, hp->dxfer_len);
		if (res)
			return res;
	}
	/* when v3 seen, allow cmd_q on this fd (def: no cmd_q) */
	set_bit(SG_FFD_CMD_Q, sfp->ffd_bm);
	ul_timeout = msecs_to_jiffies(hp->timeout);
	timeout = min_t(unsigned long, ul_timeout, INT_MAX);
	res = sg_fetch_cmnd(filp, sfp, hp->cmdp, hp->cmd_len, cmnd);
	if (res)
		return res;
	cwr.frq_bm[0] = 0;
	__assign_bit(SG_FRQ_SYNC_INVOC, cwr.frq_bm, (int)sync);
	cwr.h3p = hp;
	cwr.timeout = timeout;
	cwr.cmnd = cmnd;
	srp = sg_common_write(sfp, &cwr);
	if (IS_ERR(srp))
		return PTR_ERR(srp);
	if (o_srp)
		*o_srp = srp;
	return 0;
}

#if IS_ENABLED(SG_LOG_ACTIVE)
static void
sg_rq_state_fail_msg(struct sg_fd *sfp, enum sg_rq_state exp_old_st,
		     enum sg_rq_state want_st, enum sg_rq_state act_old_st,
		     const char *fromp)
{
	const char *eaw_rs = "expected_old,actual_old,wanted rq_st";

	if (IS_ENABLED(CONFIG_SCSI_PROC_FS))
		SG_LOG(1, sfp, "%s: %s: %s: %s,%s,%s\n",
		       __func__, fromp, eaw_rs,
		       sg_rq_st_str(exp_old_st, false),
		       sg_rq_st_str(act_old_st, false),
		       sg_rq_st_str(want_st, false));
	else
		pr_info("sg: %s: %s: %s: %d,%d,%d\n", __func__, fromp, eaw_rs,
			(int)exp_old_st, (int)act_old_st, (int)want_st);
}
#endif

static void
sg_rq_state_force(struct sg_request *srp, enum sg_rq_state new_st)
{
	bool prev, want;
	struct xarray *xafp = &srp->parentfp->srp_arr;

	atomic_set(&srp->rq_st, new_st);
	want = (new_st == SG_RS_AWAIT_RCV);
	prev = xa_get_mark(xafp, srp->rq_idx, SG_XA_RQ_AWAIT);
	if (prev != want) {
		if (want)
			__xa_set_mark(xafp, srp->rq_idx, SG_XA_RQ_AWAIT);
		else
			__xa_clear_mark(xafp, srp->rq_idx, SG_XA_RQ_AWAIT);
	}
	want = (new_st == SG_RS_INACTIVE);
	prev = xa_get_mark(xafp, srp->rq_idx, SG_XA_RQ_INACTIVE);
	if (prev != want) {
		if (want)
			__xa_set_mark(xafp, srp->rq_idx, SG_XA_RQ_INACTIVE);
		else
			__xa_clear_mark(xafp, srp->rq_idx, SG_XA_RQ_INACTIVE);
	}
}

static void
sg_rq_state_helper(struct xarray *xafp, struct sg_request *srp, int indic)
{
	if (indic & 1)		/* from inactive state */
		__xa_clear_mark(xafp, srp->rq_idx, SG_XA_RQ_INACTIVE);
	else if (indic & 2)	/* to inactive state */
		__xa_set_mark(xafp, srp->rq_idx, SG_XA_RQ_INACTIVE);

	if (indic & 4)		/* from await state */
		__xa_clear_mark(xafp, srp->rq_idx, SG_XA_RQ_AWAIT);
	else if (indic & 8)	/* to await state */
		__xa_set_mark(xafp, srp->rq_idx, SG_XA_RQ_AWAIT);
}

/* Following array indexed by enum sg_rq_state, 0 means no xa mark change */
static const int sg_rq_state_arr[] = {1, 0, 4, 0, 0};
static const int sg_rq_state_mul2arr[] = {2, 0, 8, 0, 0};

/*
 * This function keeps the srp->rq_st state and associated marks on the
 * owning xarray's element in sync. If force is true then new_st is stored
 * in srp->rq_st and xarray marks are set accordingly (and old_st is
 * ignored); and 0 is returned.
 * If force is false, then atomic_cmpxchg() is called. If the actual
 * srp->rq_st is not old_st, then -EPROTOTYPE is returned. If the actual
 * srp->rq_st is old_st then it is replaced by new_st and the xarray marks
 * are setup accordingly and 0 is returned. This assumes srp_arr xarray
 * spinlock is held.
 */
static int
sg_rq_state_chg(struct sg_request *srp, enum sg_rq_state old_st,
		enum sg_rq_state new_st, bool force, const char *fromp)
{
	enum sg_rq_state act_old_st;
	int indic;
	unsigned long iflags;
	struct xarray *xafp = &srp->parentfp->srp_arr;

	if (force) {
		xa_lock_irqsave(xafp, iflags);
		sg_rq_state_force(srp, new_st);
		xa_unlock_irqrestore(xafp, iflags);
		return 0;
	}
	indic = sg_rq_state_arr[(int)old_st] +
		sg_rq_state_mul2arr[(int)new_st];
	act_old_st = (enum sg_rq_state)atomic_cmpxchg(&srp->rq_st, old_st,
						      new_st);
	if (act_old_st != old_st) {
#if IS_ENABLED(SG_LOG_ACTIVE)
		if (fromp)
			sg_rq_state_fail_msg(srp->parentfp, old_st, new_st,
					     act_old_st, fromp);
#endif
		return -EPROTOTYPE;	/* only used for this error type */
	}
	if (indic) {
		xa_lock_irqsave(xafp, iflags);
		sg_rq_state_helper(xafp, srp, indic);
		xa_unlock_irqrestore(xafp, iflags);
	}
	return 0;
}

/*
 * All writes and submits converge on this function to launch the SCSI
 * command/request (via blk_execute_rq_nowait). Returns a pointer to a
 * sg_request object holding the request just issued or a negated errno
 * value twisted by ERR_PTR.
 */
static struct sg_request *
sg_common_write(struct sg_fd *sfp, struct sg_comm_wr_t *cwrp)
{
	bool at_head;
	int res = 0;
	int dxfr_len, dir, cmd_len;
	int pack_id = SG_PACK_ID_WILDCARD;
	u32 rq_flags;
	struct sg_device *sdp = sfp->parentdp;
	struct sg_request *srp;
	struct sg_io_hdr *hi_p;

	hi_p = cwrp->h3p;
	dir = hi_p->dxfer_direction;
	dxfr_len = hi_p->dxfer_len;
	rq_flags = hi_p->flags;
	pack_id = hi_p->pack_id;
	if (dxfr_len >= SZ_256M)
		return ERR_PTR(-EINVAL);

	srp = sg_setup_req(sfp, dxfr_len, cwrp);
	if (IS_ERR(srp))
		return srp;
	srp->rq_flags = rq_flags;
	srp->pack_id = pack_id;

	cmd_len = hi_p->cmd_len;
	memcpy(&srp->s_hdr3, hi_p, sizeof(srp->s_hdr3));
	srp->cmd_opcode = cwrp->cmnd[0];/* hold opcode of command for debug */
	SG_LOG(4, sfp, "%s: opcode=0x%02x, cdb_sz=%d, pack_id=%d\n", __func__,
	       (int)cwrp->cmnd[0], cmd_len, pack_id);

	res = sg_start_req(srp, cwrp->cmnd, cmd_len, dir);
	if (res < 0)		/* probably out of space --> -ENOMEM */
		goto err_out;
	if (unlikely(SG_IS_DETACHING(sdp))) {
		res = -ENODEV;
		goto err_out;
	}
	if (unlikely(test_bit(SG_FRQ_BLK_PUT_REQ, srp->frq_bm) || !srp->rq)) {
		res = -EIDRM;	/* this failure unexpected but observed */
		goto err_out;
	}
	if (xa_get_mark(&sfp->srp_arr, srp->rq_idx, SG_XA_RQ_FREE)) {
		SG_LOG(1, sfp, "%s: ahhh, request erased!!!\n", __func__);
		res = -ENODEV;
		goto err_out;
	}
	srp->rq->timeout = cwrp->timeout;
	kref_get(&sfp->f_ref); /* sg_rq_end_io() does kref_put(). */
	res = sg_rq_state_chg(srp, SG_RS_BUSY, SG_RS_INFLIGHT, false,
			      __func__);
	if (res)
		goto err_out;
	srp->start_ns = ktime_get_boottime_ns();
	srp->duration = 0;

	if (srp->s_hdr3.interface_id == '\0')
		at_head = true; /* backward compatibility: v1+v2 interfaces */
	else if (test_bit(SG_FFD_Q_AT_TAIL, sfp->ffd_bm))
	/* cmd flags can override sfd setting */
		at_head = !!(srp->rq_flags & SG_FLAG_Q_AT_HEAD);
	else            /* this sfd is defaulting to head */
		at_head = !(srp->rq_flags & SG_FLAG_Q_AT_TAIL);
	if (!test_bit(SG_FRQ_SYNC_INVOC, srp->frq_bm))
		atomic_inc(&sfp->submitted);
	blk_execute_rq_nowait(sdp->device->request_queue, sdp->disk,
			      srp->rq, at_head, sg_rq_end_io);
	return srp;
err_out:
	sg_finish_scsi_blk_rq(srp);
	sg_deact_request(sfp, srp);
	return ERR_PTR(res);
}

/*
 * This function is called by wait_event_interruptible in sg_read() and
 * sg_ctl_ioreceive(). wait_event_interruptible will return if this one
 * returns true (or an event like a signal (e.g. control-C) occurs).
 */

static inline bool
sg_get_ready_srp(struct sg_fd *sfp, struct sg_request **srpp, int pack_id)
{
	struct sg_request *srp;

	if (unlikely(SG_IS_DETACHING(sfp->parentdp))) {
		*srpp = NULL;
		return true;
	}
	srp = sg_find_srp_by_id(sfp, pack_id);
	*srpp = srp;
	return !!srp;
}

/*
 * Returns number of bytes copied to user space provided sense buffer or
 * negated errno value.
 */
static int
sg_copy_sense(struct sg_request *srp)
{
	int sb_len_ret = 0;
	int scsi_stat;

	/* If need be, copy the sense buffer to the user space */
	scsi_stat = srp->rq_result & 0xff;
	if ((scsi_stat & SAM_STAT_CHECK_CONDITION) ||
	    (driver_byte(srp->rq_result) & DRIVER_SENSE)) {
		int sb_len = min_t(int, SCSI_SENSE_BUFFERSIZE, srp->sense_len);
		int mx_sb_len = srp->s_hdr3.mx_sb_len;
		void __user *up = srp->s_hdr3.sbp;

		if (up && mx_sb_len > 0) {
			sb_len = min_t(int, mx_sb_len, sb_len);
			/* Additional sense length field */
			sb_len_ret = 8 + (int)srp->sense_b[7];
			sb_len_ret = min_t(int, sb_len_ret, sb_len);
			if (copy_to_user(up, srp->sense_b, sb_len_ret))
				sb_len_ret = -EFAULT;
		} else {
			sb_len_ret = 0;
		}
	}
	return sb_len_ret;
}

static int
sg_rec_state_v3(struct sg_fd *sfp, struct sg_request *srp)
{
	int sb_len_wr;
	u32 rq_res = srp->rq_result;

	sb_len_wr = sg_copy_sense(srp);
	if (sb_len_wr < 0)
		return sb_len_wr;
	if (rq_res & SG_ML_RESULT_MSK)
		srp->rq_info |= SG_INFO_CHECK;
	if (unlikely(SG_IS_DETACHING(sfp->parentdp)))
		srp->rq_info |= SG_INFO_DEVICE_DETACHING;
	return 0;
}

static ssize_t
sg_receive_v3(struct sg_fd *sfp, struct sg_request *srp, size_t count,
	      void __user *p)
{
	int err, err2;
	int rq_result = srp->rq_result;
	struct sg_io_hdr hdr3;
	struct sg_io_hdr *hp = &hdr3;

	if (in_compat_syscall()) {
		if (count < sizeof(struct compat_sg_io_hdr)) {
			err = -EINVAL;
			goto err_out;
		}
	} else if (count < SZ_SG_IO_HDR) {
		err = -EINVAL;
		goto err_out;
	}
	SG_LOG(3, sfp, "%s: srp=0x%pK\n", __func__, srp);
	err = sg_rec_state_v3(sfp, srp);
	memset(hp, 0, sizeof(*hp));
	memcpy(hp, &srp->s_hdr3, sizeof(srp->s_hdr3));
	hp->sb_len_wr = srp->sense_len;
	hp->info = srp->rq_info;
	hp->resid = srp->in_resid;
	hp->duration = srp->duration;
	hp->status = rq_result & 0xff;
	hp->masked_status = status_byte(rq_result);
	hp->msg_status = msg_byte(rq_result);
	hp->host_status = host_byte(rq_result);
	hp->driver_status = driver_byte(rq_result);
	err2 = put_sg_io_hdr(hp, p);
	err = err ? err : err2;
	err2 = sg_rq_state_chg(srp, atomic_read(&srp->rq_st), SG_RS_RCV_DONE,
			       false, __func__);
	if (err2)
		err = err ? err : err2;
err_out:
	sg_finish_scsi_blk_rq(srp);
	sg_deact_request(sfp, srp);
	return err;
}

/*
 * Completes a v3 request/command. Called from sg_read {v2 or v3},
 * ioctl(SG_IO) {for v3}, or from ioctl(SG_IORECEIVE) when its
 * completing a v3 request/command.
 */
static int
sg_read_v1v2(void __user *buf, int count, struct sg_fd *sfp,
	     struct sg_request *srp)
{
	int res = 0;
	u32 rq_result = srp->rq_result;
	struct sg_header *h2p;
	struct sg_slice_hdr3 *sh3p;
	struct sg_header a_v2hdr;

	h2p = &a_v2hdr;
	memset(h2p, 0, SZ_SG_HEADER);
	sh3p = &srp->s_hdr3;
	h2p->reply_len = (int)sh3p->timeout;
	h2p->pack_len = h2p->reply_len; /* old, strange behaviour */
	h2p->pack_id = sh3p->pack_id;
	h2p->twelve_byte = (srp->cmd_opcode >= 0xc0 && sh3p->cmd_len == 12);
	h2p->target_status = status_byte(rq_result);
	h2p->host_status = host_byte(rq_result);
	h2p->driver_status = driver_byte(rq_result);
	if ((CHECK_CONDITION & status_byte(rq_result)) ||
	    (DRIVER_SENSE & driver_byte(rq_result))) {
		memcpy(h2p->sense_buffer, srp->sense_b,
		       sizeof(h2p->sense_buffer));
	}
	switch (host_byte(rq_result)) {
	/*
	 * This following setting of 'result' is for backward compatibility
	 * and is best ignored by the user who should use target, host and
	 * driver status.
	 */
	case DID_OK:
	case DID_PASSTHROUGH:
	case DID_SOFT_ERROR:
		h2p->result = 0;
		break;
	case DID_NO_CONNECT:
	case DID_BUS_BUSY:
	case DID_TIME_OUT:
		h2p->result = EBUSY;
		break;
	case DID_BAD_TARGET:
	case DID_ABORT:
	case DID_PARITY:
	case DID_RESET:
	case DID_BAD_INTR:
		h2p->result = EIO;
		break;
	case DID_ERROR:
		h2p->result = (status_byte(rq_result) == GOOD) ? 0 : EIO;
		break;
	default:
		h2p->result = EIO;
		break;
	}

	/* Now copy the result back to the user buffer.  */
	if (count >= SZ_SG_HEADER) {
		if (copy_to_user(buf, h2p, SZ_SG_HEADER))
			return -EFAULT;
		buf += SZ_SG_HEADER;
		if (count > h2p->reply_len)
			count = h2p->reply_len;
		if (count > SZ_SG_HEADER) {
			if (sg_read_append(srp, buf, count - SZ_SG_HEADER))
				return -EFAULT;
		}
	} else {
		res = (h2p->result == 0) ? 0 : -EIO;
	}
	atomic_set(&srp->rq_st, SG_RS_RCV_DONE);
	sg_finish_scsi_blk_rq(srp);
	sg_deact_request(sfp, srp);
	return res;
}

/*
 * This is the read(2) system call entry point (see sg_fops) for this driver.
 * Accepts v1, v2 or v3 type headers (not v4). Returns count or negated
 * errno; if count is 0 then v3: returns -EINVAL; v1+v2: 0 when no other
 * error detected or -EIO.
 */
static ssize_t
sg_read(struct file *filp, char __user *p, size_t count, loff_t *ppos)
{
	bool could_be_v3;
	bool non_block = !!(filp->f_flags & O_NONBLOCK);
	int want_id = SG_PACK_ID_WILDCARD;
	int hlen, ret;
	struct sg_device *sdp = NULL;
	struct sg_fd *sfp;
	struct sg_request *srp = NULL;
	struct sg_header *h2p = NULL;
	struct sg_io_hdr a_sg_io_hdr;

	/*
	 * This could cause a response to be stranded. Close the associated
	 * file descriptor to free up any resources being held.
	 */
	ret = sg_check_file_access(filp, __func__);
	if (ret)
		return ret;

	sfp = filp->private_data;
	sdp = sfp->parentdp;
	SG_LOG(3, sfp, "%s: read() count=%d\n", __func__, (int)count);
	ret = sg_allow_if_err_recovery(sdp, non_block);
	if (ret)
		return ret;

	could_be_v3 = (count >= SZ_SG_IO_HDR);
	hlen = could_be_v3 ? SZ_SG_IO_HDR : SZ_SG_HEADER;
	h2p = (struct sg_header *)&a_sg_io_hdr;

	if (test_bit(SG_FFD_FORCE_PACKID, sfp->ffd_bm) && (int)count >= hlen) {
		/*
		 * Even though this is a user space read() system call, this
		 * code is cheating to fetch the pack_id.
		 * Only need first three 32 bit ints to determine interface.
		 */
		if (copy_from_user(h2p, p, 3 * sizeof(int)))
			return -EFAULT;
		if (h2p->reply_len < 0 && could_be_v3) {
			struct sg_io_hdr *v3_hdr = (struct sg_io_hdr *)h2p;

			if (v3_hdr->interface_id == 'S') {
				struct sg_io_hdr __user *h3_up;

				h3_up = (struct sg_io_hdr __user *)p;
				ret = get_user(want_id, &h3_up->pack_id);
				if (ret)
					return ret;
			} else {
				return -EPERM;
			}
		} else { /* for v1+v2 interfaces, this is the 3rd integer */
			want_id = h2p->pack_id;
		}
	}
	srp = sg_find_srp_by_id(sfp, want_id);
	if (!srp) {	/* nothing available so wait on packet to arrive or */
		if (unlikely(SG_IS_DETACHING(sdp)))
			return -ENODEV;
		if (non_block) /* O_NONBLOCK or v3::flags & SGV4_FLAG_IMMED */
			return -EAGAIN;
		ret = wait_event_interruptible(sfp->read_wait,
					       sg_get_ready_srp(sfp, &srp,
								want_id));
		if (unlikely(SG_IS_DETACHING(sdp)))
			return -ENODEV;
		if (ret)	/* -ERESTARTSYS as signal hit process */
			return ret;
		/* otherwise srp should be valid */
	}
	if (srp->s_hdr3.interface_id == '\0')
		ret = sg_read_v1v2(p, (int)count, sfp, srp);
	else
		ret = sg_receive_v3(sfp, srp, count, p);
	if (ret < 0)
		SG_LOG(1, sfp, "%s: negated errno: %d\n", __func__, ret);
	return ret < 0 ? ret : (int)count;
}

static int
max_sectors_bytes(struct request_queue *q)
{
	unsigned int max_sectors = queue_max_sectors(q);

	max_sectors = min_t(unsigned int, max_sectors, INT_MAX >> 9);
	return max_sectors << 9;
}

/*
 * Calculates sg_device::max_sgat_elems and sg_device::max_sgat_sz. It uses
 * the device's request queue. If q not available sets max_sgat_elems to 1
 * and max_sgat_sz to PAGE_SIZE. If potential max_sgat_sz is greater than
 * 2^30 scales down the implied max_segment_size so the product of the
 * max_segment_size and max_sgat_elems is less than or equal to 2^30 .
 */
static void
sg_calc_sgat_param(struct sg_device *sdp)
{
	int sz;
	u64 m;
	struct scsi_device *sdev = sdp->device;
	struct request_queue *q = sdev ? sdev->request_queue : NULL;

	clear_bit(SG_FDEV_LOG_SENSE, sdp->fdev_bm);
	if (!q) {
		sdp->max_sgat_elems = 1;
		sdp->max_sgat_sz = PAGE_SIZE;
		return;
	}
	sdp->max_sgat_elems = queue_max_segments(q);
	m = (u64)queue_max_segment_size(q) * queue_max_segments(q);
	if (m < PAGE_SIZE) {
		sdp->max_sgat_elems = 1;
		sdp->max_sgat_sz = PAGE_SIZE;
		return;
	}
	sz = (int)min_t(u64, m, 1 << 30);
	if (sz == (1 << 30))	/* round down so: sz = elems * elem_sz */
		sz = ((1 << 30) / sdp->max_sgat_elems) * sdp->max_sgat_elems;
	sdp->max_sgat_sz = sz;
}

static u32
sg_calc_rq_dur(const struct sg_request *srp)
{
	ktime_t ts0 = ns_to_ktime(srp->start_ns);
	ktime_t now_ts;
	s64 diff;

	if (ts0 == 0)
		return 0;
	if (unlikely(ts0 == S64_MAX))	/* _prior_ to issuing req */
		return 999999999;	/* eye catching */
	now_ts = ktime_get_boottime();
	if (unlikely(ts0 > now_ts))
		return 999999998;
	/* unlikely req duration will exceed 2**32 milliseconds */
	diff = ktime_ms_delta(now_ts, ts0);
	return (diff > (s64)U32_MAX) ? 3999999999U : (u32)diff;
}

/* Return of U32_MAX means srp is inactive state */
static u32
sg_get_dur(struct sg_request *srp, const enum sg_rq_state *sr_stp,
	   bool *is_durp)
{
	bool is_dur = false;
	u32 res = U32_MAX;

	switch (sr_stp ? *sr_stp : atomic_read(&srp->rq_st)) {
	case SG_RS_INFLIGHT:
	case SG_RS_BUSY:
		res = sg_calc_rq_dur(srp);
		break;
	case SG_RS_AWAIT_RCV:
	case SG_RS_RCV_DONE:
	case SG_RS_INACTIVE:
		res = srp->duration;
		is_dur = true;	/* completion has occurred, timing finished */
		break;
	default:
		break;
	}
	if (is_durp)
		*is_durp = is_dur;
	return res;
}

static void
sg_fill_request_element(struct sg_fd *sfp, struct sg_request *srp,
			struct sg_req_info *rip)
{
	unsigned long iflags;

	xa_lock_irqsave(&sfp->srp_arr, iflags);
	rip->duration = sg_get_dur(srp, NULL, NULL);
	if (rip->duration == U32_MAX)
		rip->duration = 0;
	rip->orphan = test_bit(SG_FRQ_IS_ORPHAN, srp->frq_bm);
	rip->sg_io_owned = test_bit(SG_FRQ_SYNC_INVOC, srp->frq_bm);
	rip->problem = !!(srp->rq_result & SG_ML_RESULT_MSK);
	rip->pack_id = srp->pack_id;
	rip->usr_ptr = srp->s_hdr3.usr_ptr;
	xa_unlock_irqrestore(&sfp->srp_arr, iflags);
}

static inline bool
sg_rq_landed(struct sg_device *sdp, struct sg_request *srp)
{
	return atomic_read(&srp->rq_st) != SG_RS_INFLIGHT ||
	       unlikely(SG_IS_DETACHING(sdp));
}

/*
 * This is a blocking wait for a specific srp. When h4p is non-NULL, it is
 * the blocking multiple request case
 */
static int
sg_wait_event_srp(struct file *filp, struct sg_fd *sfp, void __user *p,
		  struct sg_request *srp)
{
	int res;
	enum sg_rq_state sr_st;
	struct sg_device *sdp = sfp->parentdp;

	SG_LOG(3, sfp, "%s: about to wait_event...()\n", __func__);
	/* usually will be woken up by sg_rq_end_io() callback */
	res = wait_event_interruptible(sfp->read_wait,
				       sg_rq_landed(sdp, srp));
	if (unlikely(res)) { /* -ERESTARTSYS because signal hit thread */
		set_bit(SG_FRQ_IS_ORPHAN, srp->frq_bm);
		/* orphans harvested when sfp->keep_orphan is false */
		atomic_set(&srp->rq_st, SG_RS_INFLIGHT);
		SG_LOG(1, sfp, "%s:  wait_event_interruptible gave %d\n",
		       __func__, res);
		return res;
	}
	if (unlikely(SG_IS_DETACHING(sdp))) {
		atomic_set(&srp->rq_st, SG_RS_INACTIVE);
		return -ENODEV;
	}
	sr_st = atomic_read(&srp->rq_st);
	if (unlikely(sr_st != SG_RS_AWAIT_RCV))
		return -EPROTO;         /* Logic error */
	res = sg_rq_state_chg(srp, sr_st, SG_RS_BUSY, false, __func__);
	if (unlikely(res))
		return res;
	res = sg_receive_v3(sfp, srp, SZ_SG_IO_HDR, p);
	return (res < 0) ? res : 0;
}

/*
 * Handles ioctl(SG_IO) for blocking (sync) usage of v3 or v4 interface.
 * Returns 0 on success else a negated errno.
 */
static int
sg_ctl_sg_io(struct file *filp, struct sg_device *sdp, struct sg_fd *sfp,
	     void __user *p)
{
	int res;
	struct sg_request *srp = NULL;
	u8 hu8arr[SZ_SG_IO_HDR];
	struct sg_io_hdr *h3p = (struct sg_io_hdr *)hu8arr;

	SG_LOG(3, sfp, "%s:  SG_IO%s\n", __func__,
	       ((filp->f_flags & O_NONBLOCK) ? " O_NONBLOCK ignored" : ""));
	res = sg_allow_if_err_recovery(sdp, false);
	if (res)
		return res;
	if (get_sg_io_hdr(h3p, p))
		return -EFAULT;
	if (h3p->interface_id == 'S')
		res = sg_submit(filp, sfp, h3p, true, &srp);
	else
		return -EPERM;
	if (unlikely(res < 0))
		return res;
	if (!srp)	/* mrq case: already processed all responses */
		return res;
	res = sg_wait_event_srp(filp, sfp, p, srp);
	if (res)
		SG_LOG(1, sfp, "%s: %s=0x%pK  state: %s\n", __func__,
		       "unexpected srp", srp,
		       sg_rq_st_str(atomic_read(&srp->rq_st), false));
	return res;
}

/*
 * First normalize want_rsv_sz to be >= sfp->sgat_elem_sz and
 * <= max_segment_size. Exit if that is the same as old size; otherwise
 * create a new candidate request of the new size. Then decide whether to
 * re-use an existing free list request (least buflen >= required size) or
 * use the new candidate. If new one used, leave old one but it is no longer
 * the reserved request. Returns 0 on success, else a negated errno value.
 */
static int
sg_set_reserved_sz(struct sg_fd *sfp, int want_rsv_sz)
{
	bool use_new_srp = false;
	int res = 0;
	int new_sz, blen;
	unsigned long idx, iflags;
	struct sg_request *o_srp;       /* prior reserve sg_request */
	struct sg_request *n_srp;       /* new sg_request, may be used */
	struct sg_request *t_srp;       /* other fl entries */
	struct sg_device *sdp = sfp->parentdp;
	struct xarray *xafp = &sfp->srp_arr;

	o_srp = sfp->rsv_srp;
	if (!o_srp)
		return -EPROTO;
	new_sz = min_t(int, want_rsv_sz, sdp->max_sgat_sz);
	new_sz = max_t(int, new_sz, sfp->sgat_elem_sz);
	blen = o_srp->sgat_h.buflen;
	SG_LOG(3, sfp, "%s: was=%d, ask=%d, new=%d (sgat_elem_sz=%d)\n",
	       __func__, blen, want_rsv_sz, new_sz, sfp->sgat_elem_sz);
	if (blen == new_sz)
		return 0;
	n_srp = sg_mk_srp_sgat(sfp, true /* can take time */, new_sz);
	if (IS_ERR(n_srp))
		return PTR_ERR(n_srp);
	sg_rq_state_force(n_srp, SG_RS_INACTIVE);
	/* new sg_request object, sized correctly is now available */
try_again:
	o_srp = sfp->rsv_srp;
	if (!o_srp) {
		res = -EPROTO;
		goto fini;
	}
	if (SG_RS_ACTIVE(o_srp) ||
	    test_bit(SG_FFD_MMAP_CALLED, sfp->ffd_bm)) {
		res = -EBUSY;
		goto fini;
	}
	use_new_srp = true;
	xa_for_each(xafp, idx, t_srp) {
		if (t_srp != o_srp && new_sz <= t_srp->sgat_h.buflen &&
		    !SG_RS_ACTIVE(t_srp)) {
			/* good candidate on free list, use */
			use_new_srp = false;
			sfp->rsv_srp = t_srp;
			break;
		}
	}
	if (use_new_srp) {
		struct sg_request *cxc_srp;

		xa_lock_irqsave(xafp, iflags);
		n_srp->rq_idx = o_srp->rq_idx;
		idx = o_srp->rq_idx;
		cxc_srp = __xa_cmpxchg(xafp, idx, o_srp, n_srp, GFP_ATOMIC);
		if (o_srp == cxc_srp) {
			sfp->rsv_srp = n_srp;
			sg_rq_state_force(n_srp, SG_RS_INACTIVE);
			xa_unlock_irqrestore(xafp, iflags);
			SG_LOG(6, sfp, "%s: new rsv srp=0x%pK ++\n", __func__,
			       n_srp);
			sg_remove_sgat(o_srp);
			kfree(o_srp);
		} else {
			xa_unlock_irqrestore(xafp, iflags);
			SG_LOG(1, sfp, "%s: xa_cmpxchg() failed, again\n",
			       __func__);
			goto try_again;
		}
	}
fini:
	if (!use_new_srp) {
		sg_remove_sgat(n_srp);
		kfree(n_srp);   /* no-one else has seen n_srp, so safe */
	}
	return res;
}

#ifdef CONFIG_COMPAT
struct compat_sg_req_info { /* used by SG_GET_REQUEST_TABLE ioctl() */
	char req_state;
	char orphan;
	char sg_io_owned;
	char problem;
	int pack_id;
	compat_uptr_t usr_ptr;
	unsigned int duration;
	int unused;
};

static int put_compat_request_table(struct compat_sg_req_info __user *o,
				    struct sg_req_info *rinfo)
{
	int i;
	for (i = 0; i < SG_MAX_QUEUE; i++) {
		if (copy_to_user(o + i, rinfo + i, offsetof(sg_req_info_t, usr_ptr)) ||
		    put_user((uintptr_t)rinfo[i].usr_ptr, &o[i].usr_ptr) ||
		    put_user(rinfo[i].duration, &o[i].duration) ||
		    put_user(rinfo[i].unused, &o[i].unused))
			return -EFAULT;
	}
	return 0;
}
#endif

/*
 * For backward compatibility, output SG_MAX_QUEUE sg_req_info objects. First
 * fetch from the active list then, if there is still room, from the free
 * list. Some of the trailing elements may be empty which is indicated by all
 * fields being zero. Any requests beyond SG_MAX_QUEUE are ignored.
 */
static int
sg_ctl_req_tbl(struct sg_fd *sfp, void __user *p)
{
	int k, result, val;
	unsigned long idx;
	struct sg_request *srp;
	struct sg_req_info *rinfop;

	SG_LOG(3, sfp, "%s:    SG_GET_REQUEST_TABLE\n", __func__);
	k = SG_MAX_QUEUE;
	rinfop = kcalloc(k, SZ_SG_REQ_INFO, GFP_KERNEL);
	if (!rinfop)
		return -ENOMEM;
	val = 0;
	xa_for_each(&sfp->srp_arr, idx, srp) {
		if (!srp)
			continue;
		if (val >= SG_MAX_QUEUE)
			break;
		if (xa_get_mark(&sfp->srp_arr, idx, SG_XA_RQ_INACTIVE))
			continue;
		sg_fill_request_element(sfp, srp, rinfop + val);
		val++;
	}
	xa_for_each(&sfp->srp_arr, idx, srp) {
		if (!srp)
			continue;
		if (val >= SG_MAX_QUEUE)
			break;
		if (!xa_get_mark(&sfp->srp_arr, idx, SG_XA_RQ_INACTIVE))
			continue;
		sg_fill_request_element(sfp, srp, rinfop + val);
		val++;
	}
#ifdef CONFIG_COMPAT
	if (in_compat_syscall())
		result = put_compat_request_table(p, rinfop);
	else
		result = copy_to_user(p, rinfop,
				      SZ_SG_REQ_INFO * SG_MAX_QUEUE);
#else
	result = copy_to_user(p, rinfop,
			      SZ_SG_REQ_INFO * SG_MAX_QUEUE);
#endif
	kfree(rinfop);
	return result;
}

static int
sg_ctl_scsi_id(struct scsi_device *sdev, struct sg_fd *sfp, void __user *p)
{
	struct sg_scsi_id ss_id;

	SG_LOG(3, sfp, "%s:    SG_GET_SCSI_ID\n", __func__);
	ss_id.host_no = sdev->host->host_no;
	ss_id.channel = sdev->channel;
	ss_id.scsi_id = sdev->id;
	ss_id.lun = sdev->lun;
	ss_id.scsi_type = sdev->type;
	ss_id.h_cmd_per_lun = sdev->host->cmd_per_lun;
	ss_id.d_queue_depth = sdev->queue_depth;
	ss_id.unused[0] = 0;
	ss_id.unused[1] = 0;
	if (copy_to_user(p, &ss_id, sizeof(struct sg_scsi_id)))
		return -EFAULT;
	return 0;
}

static long
sg_ioctl_common(struct file *filp, struct sg_device *sdp, struct sg_fd *sfp,
		unsigned int cmd_in, void __user *p)
{
	bool read_only = O_RDWR != (filp->f_flags & O_ACCMODE);
	int val;
	int result = 0;
	int __user *ip = p;
	struct sg_request *srp;
	struct scsi_device *sdev;
	unsigned long idx;
	__maybe_unused const char *pmlp = ", pass to mid-level";

	SG_LOG(6, sfp, "%s: cmd=0x%x, O_NONBLOCK=%d\n", __func__, cmd_in,
	       !!(filp->f_flags & O_NONBLOCK));
	if (unlikely(SG_IS_DETACHING(sdp)))
		return -ENODEV;
	sdev = sdp->device;

	switch (cmd_in) {
	case SG_IO:
		return sg_ctl_sg_io(filp, sdp, sfp, p);
	case SG_GET_SCSI_ID:
		return sg_ctl_scsi_id(sdev, sfp, p);
	case SG_SET_FORCE_PACK_ID:
		SG_LOG(3, sfp, "%s:    SG_SET_FORCE_PACK_ID\n", __func__);
		result = get_user(val, ip);
		if (result)
			return result;
		assign_bit(SG_FFD_FORCE_PACKID, sfp->ffd_bm, !!val);
		return 0;
	case SG_GET_PACK_ID:    /* or tag of oldest "read"-able, -1 if none */
		val = -1;
		xa_for_each_marked(&sfp->srp_arr, idx, srp, SG_XA_RQ_AWAIT) {
			if (!srp)
				continue;
			val = srp->pack_id;
			break;
		}
		SG_LOG(3, sfp, "%s:    SG_GET_PACK_ID=%d\n", __func__, val);
		return put_user(val, ip);
	case SG_GET_NUM_WAITING:
		return put_user(atomic_read(&sfp->waiting), ip);
	case SG_GET_SG_TABLESIZE:
		SG_LOG(3, sfp, "%s:    SG_GET_SG_TABLESIZE=%d\n", __func__,
		       sdp->max_sgat_sz);
		return put_user(sdp->max_sgat_sz, ip);
	case SG_SET_RESERVED_SIZE:
		result = get_user(val, ip);
		if (!result) {
			if (val >= 0 && val <= (1024 * 1024 * 1024)) {
				mutex_lock(&sfp->f_mutex);
				result = sg_set_reserved_sz(sfp, val);
				mutex_unlock(&sfp->f_mutex);
			} else {
				SG_LOG(3, sfp, "%s: invalid size\n", __func__);
				result = -EINVAL;
			}
		}
		return result;
	case SG_GET_RESERVED_SIZE:
		mutex_lock(&sfp->f_mutex);
		val = min_t(int, sfp->rsv_srp->sgat_h.buflen,
			    sdp->max_sgat_sz);
		mutex_unlock(&sfp->f_mutex);
		SG_LOG(3, sfp, "%s:    SG_GET_RESERVED_SIZE=%d\n",
		       __func__, val);
		result = put_user(val, ip);
		return result;
	case SG_SET_COMMAND_Q:
		SG_LOG(3, sfp, "%s:    SG_SET_COMMAND_Q\n", __func__);
		result = get_user(val, ip);
		if (result)
			return result;
		assign_bit(SG_FFD_CMD_Q, sfp->ffd_bm, !!val);
		return 0;
	case SG_GET_COMMAND_Q:
		SG_LOG(3, sfp, "%s:    SG_GET_COMMAND_Q\n", __func__);
		return put_user(test_bit(SG_FFD_CMD_Q, sfp->ffd_bm), ip);
	case SG_SET_KEEP_ORPHAN:
		SG_LOG(3, sfp, "%s:    SG_SET_KEEP_ORPHAN\n", __func__);
		result = get_user(val, ip);
		if (result)
			return result;
		assign_bit(SG_FFD_KEEP_ORPHAN, sfp->ffd_bm, !!val);
		return 0;
	case SG_GET_KEEP_ORPHAN:
		SG_LOG(3, sfp, "%s:    SG_GET_KEEP_ORPHAN\n", __func__);
		return put_user(test_bit(SG_FFD_KEEP_ORPHAN, sfp->ffd_bm),
				ip);
	case SG_GET_VERSION_NUM:
		SG_LOG(3, sfp, "%s:    SG_GET_VERSION_NUM\n", __func__);
		return put_user(sg_version_num, ip);
	case SG_GET_REQUEST_TABLE:
		return sg_ctl_req_tbl(sfp, p);
	case SG_SCSI_RESET:
		SG_LOG(3, sfp, "%s:    SG_SCSI_RESET\n", __func__);
		break;
	case SG_SET_TIMEOUT:
		SG_LOG(3, sfp, "%s:    SG_SET_TIMEOUT\n", __func__);
		result = get_user(val, ip);
		if (result)
			return result;
		if (val < 0)
			return -EIO;
		if (val >= mult_frac((s64)INT_MAX, USER_HZ, HZ))
			val = min_t(s64, mult_frac((s64)INT_MAX, USER_HZ, HZ),
				    INT_MAX);
		sfp->timeout_user = val;
		sfp->timeout = mult_frac(val, HZ, USER_HZ);
		return 0;
	case SG_GET_TIMEOUT:    /* N.B. User receives timeout as return value */
				/* strange ..., for backward compatibility */
		SG_LOG(3, sfp, "%s:    SG_GET_TIMEOUT\n", __func__);
		return sfp->timeout_user;
	case SG_SET_FORCE_LOW_DMA:
		/*
		 * N.B. This ioctl never worked properly, but failed to
		 * return an error value. So returning '0' to keep
		 * compatibility with legacy applications.
		 */
		SG_LOG(3, sfp, "%s:    SG_SET_FORCE_LOW_DMA\n", __func__);
		return 0;
	case SG_GET_LOW_DMA:
		SG_LOG(3, sfp, "%s:    SG_GET_LOW_DMA\n", __func__);
		return put_user((int)sdev->host->unchecked_isa_dma, ip);
	case SG_NEXT_CMD_LEN:	/* active only in v2 interface */
		SG_LOG(3, sfp, "%s:    SG_NEXT_CMD_LEN\n", __func__);
		result = get_user(val, ip);
		if (result)
			return result;
		if (val > SG_MAX_CDB_SIZE)
			return -ENOMEM;
		mutex_lock(&sfp->f_mutex);
		sfp->next_cmd_len = max_t(int, val, 0);
		mutex_unlock(&sfp->f_mutex);
		return 0;
	case SG_GET_ACCESS_COUNT:
		SG_LOG(3, sfp, "%s:    SG_GET_ACCESS_COUNT\n", __func__);
		/* faked - we don't have a real access count anymore */
		val = (sdev ? 1 : 0);
		return put_user(val, ip);
	case SG_EMULATED_HOST:
		SG_LOG(3, sfp, "%s:    SG_EMULATED_HOST\n", __func__);
		if (unlikely(SG_IS_DETACHING(sdp)))
			return -ENODEV;
		return put_user(sdev->host->hostt->emulated, ip);
	case SCSI_IOCTL_SEND_COMMAND:
		SG_LOG(3, sfp, "%s:    SCSI_IOCTL_SEND_COMMAND\n", __func__);
		return sg_scsi_ioctl(sdev->request_queue, NULL, filp->f_mode,
				     p);
	case SG_SET_DEBUG:
		SG_LOG(3, sfp, "%s:    SG_SET_DEBUG\n", __func__);
		result = get_user(val, ip);
		if (result)
			return result;
		assign_bit(SG_FDEV_LOG_SENSE, sdp->fdev_bm, !!val);
		if (val == 0)	/* user can force recalculation */
			sg_calc_sgat_param(sdp);
		return 0;
	case BLKSECTGET:
		SG_LOG(3, sfp, "%s:    BLKSECTGET\n", __func__);
		return put_user(max_sectors_bytes(sdev->request_queue), ip);
	case BLKTRACESETUP:
		SG_LOG(3, sfp, "%s:    BLKTRACESETUP\n", __func__);
		return blk_trace_setup(sdev->request_queue,
				       sdp->disk->disk_name,
				       MKDEV(SCSI_GENERIC_MAJOR, sdp->index),
				       NULL, p);
	case BLKTRACESTART:
		SG_LOG(3, sfp, "%s:    BLKTRACESTART\n", __func__);
		return blk_trace_startstop(sdev->request_queue, 1);
	case BLKTRACESTOP:
		SG_LOG(3, sfp, "%s:    BLKTRACESTOP\n", __func__);
		return blk_trace_startstop(sdev->request_queue, 0);
	case BLKTRACETEARDOWN:
		SG_LOG(3, sfp, "%s:    BLKTRACETEARDOWN\n", __func__);
		return blk_trace_remove(sdev->request_queue);
	case SCSI_IOCTL_GET_IDLUN:
		SG_LOG(3, sfp, "%s:    SCSI_IOCTL_GET_IDLUN %s\n", __func__,
		       pmlp);
		break;
	case SCSI_IOCTL_GET_BUS_NUMBER:
		SG_LOG(3, sfp, "%s:    SCSI_IOCTL_GET_BUS_NUMBER%s\n",
		       __func__, pmlp);
		break;
	case SCSI_IOCTL_PROBE_HOST:
		SG_LOG(3, sfp, "%s:    SCSI_IOCTL_PROBE_HOST%s",
		       __func__, pmlp);
		break;
	case SG_GET_TRANSFORM:
		SG_LOG(3, sfp, "%s:    SG_GET_TRANSFORM%s\n", __func__, pmlp);
		break;
	default:
		SG_LOG(3, sfp, "%s:    unrecognized ioctl [0x%x]%s\n",
		       __func__, cmd_in, pmlp);
		if (read_only)
			return -EPERM;	/* don't know, so take safer approach */
		break;
	}
	result = sg_allow_if_err_recovery(sdp, filp->f_flags & O_NDELAY);
	if (unlikely(result))
		return result;
	return -ENOIOCTLCMD;
}

static long
sg_ioctl(struct file *filp, unsigned int cmd_in, unsigned long arg)
{
	void __user *p = (void __user *)arg;
	struct sg_device *sdp;
	struct sg_fd *sfp;
	int ret;

	sfp = filp->private_data;
	sdp = sfp->parentdp;
	if (!sdp)
		return -ENXIO;

	ret = sg_ioctl_common(filp, sdp, sfp, cmd_in, p);
	if (ret != -ENOIOCTLCMD)
		return ret;

	return scsi_ioctl(sdp->device, cmd_in, p);
}

#if IS_ENABLED(CONFIG_COMPAT)
static long
sg_compat_ioctl(struct file *filp, unsigned int cmd_in, unsigned long arg)
{
	void __user *p = compat_ptr(arg);
	struct sg_device *sdp;
	struct sg_fd *sfp;
	int ret;

	sfp = filp->private_data;
	sdp = sfp->parentdp;
	if (!sdp)
		return -ENXIO;

	ret = sg_ioctl_common(filp, sdp, sfp, cmd_in, p);
	if (ret != -ENOIOCTLCMD)
		return ret;

	return scsi_compat_ioctl(sdp->device, cmd_in, p);
}
#endif

/*
 * Implements the poll(2) system call for this driver. Returns various EPOLL*
 * flags OR-ed together.
 */
static __poll_t
sg_poll(struct file *filp, poll_table * wait)
{
	__poll_t p_res = 0;
	struct sg_fd *sfp = filp->private_data;

	poll_wait(filp, &sfp->read_wait, wait);
	if (atomic_read(&sfp->waiting) > 0)
		p_res = EPOLLIN | EPOLLRDNORM;

	if (unlikely(SG_IS_DETACHING(sfp->parentdp)))
		p_res |= EPOLLHUP;
	else if (likely(test_bit(SG_FFD_CMD_Q, sfp->ffd_bm)))
		p_res |= EPOLLOUT | EPOLLWRNORM;
	else if (atomic_read(&sfp->submitted) == 0)
		p_res |= EPOLLOUT | EPOLLWRNORM;
	SG_LOG(3, sfp, "%s: p_res=0x%x\n", __func__, (__force u32)p_res);
	return p_res;
}

static int
sg_fasync(int fd, struct file *filp, int mode)
{
	struct sg_fd *sfp = filp->private_data;

	SG_LOG(3, sfp, "%s: mode(%s)\n", __func__, (mode ? "add" : "remove"));
	return fasync_helper(fd, filp, mode, &sfp->async_qp);
}

/* Note: the error return: VM_FAULT_SIGBUS causes a "bus error" */
static vm_fault_t
sg_vma_fault(struct vm_fault *vmf)
{
	int k, length;
	unsigned long offset, len, sa, iflags;
	struct vm_area_struct *vma = vmf->vma;
	struct sg_scatter_hold *rsv_schp;
	struct sg_request *srp;
	struct sg_device *sdp;
	struct sg_fd *sfp;
	const char *nbp = "==NULL, bad";

	if (!vma) {
		pr_warn("%s: vma%s\n", __func__, nbp);
		goto out_err;
	}
	sfp = vma->vm_private_data;
	if (!sfp) {
		pr_warn("%s: sfp%s\n", __func__, nbp);
		goto out_err;
	}
	sdp = sfp->parentdp;
	if (sdp && unlikely(SG_IS_DETACHING(sdp))) {
		SG_LOG(1, sfp, "%s: device detaching\n", __func__);
		goto out_err;
	}
	srp = sfp->rsv_srp;
	if (!srp) {
		SG_LOG(1, sfp, "%s: srp%s\n", __func__, nbp);
		goto out_err;
	}
	xa_lock_irqsave(&sfp->srp_arr, iflags);
	rsv_schp = &srp->sgat_h;
	offset = vmf->pgoff << PAGE_SHIFT;
	if (offset >= (unsigned int)rsv_schp->buflen) {
		SG_LOG(1, sfp, "%s: offset[%lu] >= rsv.buflen\n", __func__,
		       offset);
		goto out_err_unlock;
	}
	sa = vma->vm_start;
	SG_LOG(3, sfp, "%s: vm_start=0x%lx, off=%lu\n", __func__, sa, offset);
	length = 1 << (PAGE_SHIFT + rsv_schp->page_order);
	for (k = 0; k < rsv_schp->num_sgat && sa < vma->vm_end; ++k) {
		len = vma->vm_end - sa;
		len = min_t(int, len, (int)length);
		if (offset < len) {
			struct page *page;
			struct page *pp;

			pp = rsv_schp->pages[k];
			xa_unlock_irqrestore(&sfp->srp_arr, iflags);
			page = nth_page(pp, offset >> PAGE_SHIFT);
			get_page(page); /* increment page count */
			vmf->page = page;
			return 0; /* success */
		}
		sa += len;
		offset -= len;
	}
out_err_unlock:
	xa_unlock_irqrestore(&sfp->srp_arr, iflags);
out_err:
	return VM_FAULT_SIGBUS;
}

static const struct vm_operations_struct sg_mmap_vm_ops = {
	.fault = sg_vma_fault,
};

/* Entry point for mmap(2) system call */
static int
sg_mmap(struct file *filp, struct vm_area_struct *vma)
{
	int k, length;
	int ret = 0;
	unsigned long req_sz, len, sa, iflags;
	struct sg_scatter_hold *rsv_schp;
	struct sg_fd *sfp;
	struct sg_request *srp;

	if (!filp || !vma)
		return -ENXIO;
	sfp = filp->private_data;
	if (!sfp) {
		pr_warn("sg: %s: sfp is NULL\n", __func__);
		return -ENXIO;
	}
	req_sz = vma->vm_end - vma->vm_start;
	SG_LOG(3, sfp, "%s: vm_start=%pK, len=%d\n", __func__,
	       (void *)vma->vm_start, (int)req_sz);
	if (vma->vm_pgoff)
		return -EINVAL; /* only an offset of 0 accepted */
	/* Check reserve request is inactive and has large enough buffer */
	mutex_lock(&sfp->f_mutex);
	srp = sfp->rsv_srp;
	xa_lock_irqsave(&sfp->srp_arr, iflags);
	if (SG_RS_ACTIVE(srp)) {
		ret = -EBUSY;
		goto out;
	}
	rsv_schp = &srp->sgat_h;
	if (req_sz > (unsigned long)rsv_schp->buflen) {
		ret = -ENOMEM;
		goto out;
	}
	sa = vma->vm_start;
	length = 1 << (PAGE_SHIFT + rsv_schp->page_order);
	for (k = 0; k < rsv_schp->num_sgat && sa < vma->vm_end; ++k) {
		len = vma->vm_end - sa;
		len = min_t(unsigned long, len, (unsigned long)length);
		sa += len;
	}

	set_bit(SG_FFD_MMAP_CALLED, sfp->ffd_bm);
	vma->vm_flags |= VM_IO | VM_DONTEXPAND | VM_DONTDUMP;
	vma->vm_private_data = sfp;
	vma->vm_ops = &sg_mmap_vm_ops;
out:
	xa_unlock_irqrestore(&sfp->srp_arr, iflags);
	mutex_unlock(&sfp->f_mutex);
	return ret;
}

static void
sg_rq_end_io_usercontext(struct work_struct *work)
{
	struct sg_request *srp = container_of(work, struct sg_request,
					      ew_orph.work);
	struct sg_fd *sfp;

	if (!srp) {
		WARN_ONCE("%s: srp unexpectedly NULL\n", __func__);
		return;
	}
	sfp = srp->parentfp;
	if (!sfp) {
		WARN_ONCE(1, "%s: sfp unexpectedly NULL\n", __func__);
		return;
	}
	SG_LOG(3, sfp, "%s: srp=0x%pK\n", __func__, srp);
	if (test_bit(SG_FRQ_DEACT_ORPHAN, srp->frq_bm)) {
		sg_finish_scsi_blk_rq(srp);	/* clean up orphan case */
		sg_deact_request(sfp, srp);
	}
	kref_put(&sfp->f_ref, sg_remove_sfp);
}

static void
sg_check_sense(struct sg_device *sdp, struct sg_request *srp, int sense_len)
{
	int driver_stat;
	u32 rq_res = srp->rq_result;
	struct scsi_request *scsi_rp = scsi_req(srp->rq);
	u8 *sbp = scsi_rp ? scsi_rp->sense : NULL;

	if (!sbp)
		return;
	driver_stat = driver_byte(rq_res);
	if (driver_stat & DRIVER_SENSE) {
		struct scsi_sense_hdr ssh;

		if (scsi_normalize_sense(sbp, sense_len, &ssh)) {
			if (!scsi_sense_is_deferred(&ssh)) {
				if (ssh.sense_key == UNIT_ATTENTION) {
					if (sdp->device->removable)
						sdp->device->changed = 1;
				}
			}
		}
	}
	if (test_bit(SG_FDEV_LOG_SENSE, sdp->fdev_bm) > 0) {
		int scsi_stat = rq_res & 0xff;

		if (scsi_stat == SAM_STAT_CHECK_CONDITION ||
		    scsi_stat == SAM_STAT_COMMAND_TERMINATED)
			__scsi_print_sense(sdp->device, __func__, sbp,
					   sense_len);
	}
}

/*
 * This "bottom half" (soft interrupt) handler is called by the mid-level
 * when a request has completed or failed. This callback is registered in a
 * blk_execute_rq_nowait() call in the sg_common_write(). For ioctl(SG_IO)
 * (sync) usage, sg_ctl_sg_io() waits to be woken up by this callback.
 */
static void
sg_rq_end_io(struct request *rq, blk_status_t status)
{
	enum sg_rq_state rqq_state = SG_RS_AWAIT_RCV;
	int a_resid, slen;
	struct sg_request *srp = rq->end_io_data;
	struct scsi_request *scsi_rp = scsi_req(rq);
	struct sg_device *sdp;
	struct sg_fd *sfp;

	if (!scsi_rp) {
		WARN_ONCE("%s: scsi_req(rq) unexpectedly NULL\n", __func__);
		return;
	}
	if (!srp) {
		WARN_ONCE("%s: srp unexpectedly NULL\n", __func__);
		return;
	}
	/* Expect 0 --> 1 transition, otherwise processed elsewhere */
	if (unlikely(test_and_set_bit(SG_FRQ_BLK_PUT_REQ, srp->frq_bm))) {
		pr_info("%s: srp=%pK already completed\n", __func__, srp);
		return;
	}
	if (WARN_ON(atomic_read(&srp->rq_st) != SG_RS_INFLIGHT)) {
		pr_warn("%s: bad rq_st=%d\n", __func__,
			atomic_read(&srp->rq_st));
		goto early_err;
	}
	sfp = srp->parentfp;
	if (unlikely(!sfp)) {
		WARN_ONCE(1, "%s: sfp unexpectedly NULL", __func__);
		goto early_err;
	}
	sdp = sfp->parentdp;
	if (unlikely(SG_IS_DETACHING(sdp)))
		pr_info("%s: device detaching\n", __func__);

	srp->rq_result = scsi_rp->result;
	slen = min_t(int, scsi_rp->sense_len, SCSI_SENSE_BUFFERSIZE);
	a_resid = scsi_rp->resid_len;

	if (a_resid)
		srp->in_resid = a_resid;

	SG_LOG(6, sfp, "%s: pack_id=%d, res=0x%x\n", __func__, srp->pack_id,
	       srp->rq_result);
	srp->duration = sg_calc_rq_dur(srp);
	if (unlikely((srp->rq_result & SG_ML_RESULT_MSK) && slen > 0))
		sg_check_sense(sdp, srp, slen);
	if (slen > 0)
		memcpy(srp->sense_b, scsi_rp->sense, slen);
	srp->sense_len = slen;
	if (unlikely(test_bit(SG_FRQ_IS_ORPHAN, srp->frq_bm))) {
		if (test_bit(SG_FFD_KEEP_ORPHAN, sfp->ffd_bm)) {
			clear_bit(SG_FRQ_SYNC_INVOC, srp->frq_bm);
		} else {
			rqq_state = SG_RS_BUSY;
			set_bit(SG_FRQ_DEACT_ORPHAN, srp->frq_bm);
		}
	}
	if (!test_bit(SG_FRQ_SYNC_INVOC, srp->frq_bm))
		atomic_inc(&sfp->waiting);
	if (unlikely(sg_rq_state_chg(srp, SG_RS_INFLIGHT, rqq_state,
				     false, __func__)))
		pr_warn("%s: can't set rq_st\n", __func__);
	/*
	 * Free the mid-level resources apart from the bio (if any). The bio's
	 * blk_rq_unmap_user() can be called later from user context.
	 */
	srp->rq = NULL;
	scsi_req_free_cmd(scsi_rp);
	blk_put_request(rq);

	if (likely(rqq_state == SG_RS_AWAIT_RCV)) {
		/* Wake any sg_read()/ioctl(SG_IORECEIVE) awaiting this req */
		wake_up_interruptible(&sfp->read_wait);
		kill_fasync(&sfp->async_qp, SIGPOLL, POLL_IN);
		kref_put(&sfp->f_ref, sg_remove_sfp);
	} else {        /* clean up orphaned request that aren't being kept */
		INIT_WORK(&srp->ew_orph.work, sg_rq_end_io_usercontext);
		schedule_work(&srp->ew_orph.work);
	}
	return;

early_err:
	srp->rq = NULL;
	if (scsi_rp)
		scsi_req_free_cmd(scsi_rp);
	blk_put_request(rq);
}

static const struct file_operations sg_fops = {
	.owner = THIS_MODULE,
	.read = sg_read,
	.write = sg_write,
	.poll = sg_poll,
	.unlocked_ioctl = sg_ioctl,
#if IS_ENABLED(CONFIG_COMPAT)
	.compat_ioctl = sg_compat_ioctl,
#endif
	.open = sg_open,
	.mmap = sg_mmap,
	.release = sg_release,
	.fasync = sg_fasync,
	.llseek = no_llseek,
};

static struct class *sg_sysfs_class;

static bool sg_sysfs_valid;

/* Returns valid pointer to sg_device or negated errno twisted by ERR_PTR */
static struct sg_device *
sg_add_device_helper(struct gendisk *disk, struct scsi_device *scsidp)
{
	struct sg_device *sdp;
	int error;
	u32 k;
	unsigned long iflags;

	sdp = kzalloc(sizeof(*sdp), GFP_KERNEL);
	if (!sdp)
		return ERR_PTR(-ENOMEM);

	idr_preload(GFP_KERNEL);
	write_lock_irqsave(&sg_index_lock, iflags);

	error = idr_alloc(&sg_index_idr, sdp, 0, SG_MAX_DEVS, GFP_NOWAIT);
	if (error < 0) {
		if (error == -ENOSPC) {
			sdev_printk(KERN_WARNING, scsidp,
				    "Unable to attach sg device type=%d, minor number exceeds %d\n",
				    scsidp->type, SG_MAX_DEVS - 1);
			error = -ENODEV;
		} else {
			sdev_printk(KERN_WARNING, scsidp,
				"%s: idr allocation sg_device failure: %d\n",
				    __func__, error);
		}
		goto out_unlock;
	}
	k = error;

	SCSI_LOG_TIMEOUT(3, sdev_printk(KERN_INFO, scsidp,
			 "%s: dev=%d, sdp=0x%pK ++\n", __func__, k, sdp));
	sprintf(disk->disk_name, "sg%d", k);
	disk->first_minor = k;
	sdp->disk = disk;
	sdp->device = scsidp;
	mutex_init(&sdp->open_rel_lock);
	xa_init_flags(&sdp->sfp_arr, XA_FLAGS_ALLOC | XA_FLAGS_LOCK_IRQ);
	init_waitqueue_head(&sdp->open_wait);
	clear_bit(SG_FDEV_DETACHING, sdp->fdev_bm);
	sdp->index = k;
	kref_init(&sdp->d_ref);
	error = 0;

out_unlock:
	write_unlock_irqrestore(&sg_index_lock, iflags);
	idr_preload_end();

	if (error) {
		kfree(sdp);
		return ERR_PTR(error);
	}
	return sdp;
}

static int
sg_add_device(struct device *cl_dev, struct class_interface *cl_intf)
{
	struct scsi_device *scsidp = to_scsi_device(cl_dev->parent);
	struct gendisk *disk;
	struct sg_device *sdp = NULL;
	struct cdev * cdev = NULL;
	int error;
	unsigned long iflags;

	disk = alloc_disk(1);
	if (!disk) {
		pr_warn("%s: alloc_disk failed\n", __func__);
		return -ENOMEM;
	}
	disk->major = SCSI_GENERIC_MAJOR;

	error = -ENOMEM;
	cdev = cdev_alloc();
	if (!cdev) {
		pr_warn("%s: cdev_alloc failed\n", __func__);
		goto out;
	}
	cdev->owner = THIS_MODULE;
	cdev->ops = &sg_fops;

	sdp = sg_add_device_helper(disk, scsidp);
	if (IS_ERR(sdp)) {
		error = PTR_ERR(sdp);
		goto out;
	}

	error = cdev_add(cdev, MKDEV(SCSI_GENERIC_MAJOR, sdp->index), 1);
	if (error)
		goto cdev_add_err;

	sdp->cdev = cdev;
	if (sg_sysfs_valid) {
		struct device *sg_class_member;

		sg_class_member = device_create(sg_sysfs_class, cl_dev->parent,
						MKDEV(SCSI_GENERIC_MAJOR,
						      sdp->index),
						sdp, "%s", disk->disk_name);
		if (IS_ERR(sg_class_member)) {
			pr_err("%s: device_create failed\n", __func__);
			error = PTR_ERR(sg_class_member);
			goto cdev_add_err;
		}
		error = sysfs_create_link(&scsidp->sdev_gendev.kobj,
					  &sg_class_member->kobj, "generic");
		if (error)
			pr_err("%s: unable to make symlink 'generic' back "
			       "to sg%d\n", __func__, sdp->index);
	} else
		pr_warn("%s: sg_sys Invalid\n", __func__);

	sg_calc_sgat_param(sdp);
	sdev_printk(KERN_NOTICE, scsidp, "Attached scsi generic sg%d "
		    "type %d\n", sdp->index, scsidp->type);

	dev_set_drvdata(cl_dev, sdp);

	return 0;

cdev_add_err:
	write_lock_irqsave(&sg_index_lock, iflags);
	idr_remove(&sg_index_idr, sdp->index);
	write_unlock_irqrestore(&sg_index_lock, iflags);
	kfree(sdp);

out:
	put_disk(disk);
	if (cdev)
		cdev_del(cdev);
	return error;
}

static void
sg_device_destroy(struct kref *kref)
{
	struct sg_device *sdp = container_of(kref, struct sg_device, d_ref);
	unsigned long flags;

	SCSI_LOG_TIMEOUT(1, pr_info("[tid=%d] %s: sdp idx=%d, sdp=0x%pK --\n",
				    (current ? current->pid : -1), __func__,
				    sdp->index, sdp));
	/*
	 * CAUTION!  Note that the device can still be found via idr_find()
	 * even though the refcount is 0.  Therefore, do idr_remove() BEFORE
	 * any other cleanup.
	 */

	xa_destroy(&sdp->sfp_arr);
	write_lock_irqsave(&sg_index_lock, flags);
	idr_remove(&sg_index_idr, sdp->index);
	write_unlock_irqrestore(&sg_index_lock, flags);

	put_disk(sdp->disk);
	kfree(sdp);
}

static void
sg_remove_device(struct device *cl_dev, struct class_interface *cl_intf)
{
	struct scsi_device *scsidp = to_scsi_device(cl_dev->parent);
	struct sg_device *sdp = dev_get_drvdata(cl_dev);
	unsigned long idx;
	struct sg_fd *sfp;

	if (!sdp)
		return;
	/* set this flag as soon as possible as it could be a surprise */
	if (test_and_set_bit(SG_FDEV_DETACHING, sdp->fdev_bm))
		return; /* only want to do following once per device */

	SCSI_LOG_TIMEOUT(3, sdev_printk(KERN_INFO, sdp->device,
					"%s: 0x%pK\n", __func__, sdp));

	xa_for_each(&sdp->sfp_arr, idx, sfp) {
		if (!sfp)
			continue;
		wake_up_interruptible_all(&sfp->read_wait);
		kill_fasync(&sfp->async_qp, SIGPOLL, POLL_HUP);
	}
	wake_up_interruptible_all(&sdp->open_wait);

	sysfs_remove_link(&scsidp->sdev_gendev.kobj, "generic");
	device_destroy(sg_sysfs_class, MKDEV(SCSI_GENERIC_MAJOR, sdp->index));
	cdev_del(sdp->cdev);
	sdp->cdev = NULL;

	kref_put(&sdp->d_ref, sg_device_destroy);
}

module_param_named(scatter_elem_sz, scatter_elem_sz, int, S_IRUGO | S_IWUSR);
module_param_named(def_reserved_size, def_reserved_size, int,
		   S_IRUGO | S_IWUSR);
module_param_named(allow_dio, sg_allow_dio, int, S_IRUGO | S_IWUSR);

MODULE_AUTHOR("Douglas Gilbert");
MODULE_DESCRIPTION("SCSI generic (sg) driver");
MODULE_LICENSE("GPL");
MODULE_VERSION(SG_VERSION_STR);
MODULE_ALIAS_CHARDEV_MAJOR(SCSI_GENERIC_MAJOR);

MODULE_PARM_DESC(scatter_elem_sz, "scatter gather element "
                "size (default: max(SG_SCATTER_SZ, PAGE_SIZE))");
MODULE_PARM_DESC(def_reserved_size, "size of buffer reserved for each fd");
MODULE_PARM_DESC(allow_dio, "allow direct I/O (default: 0 (disallow))");

static int __init
init_sg(void)
{
	int rc;

	/* check scatter_elem_sz module parameter, change if inappropriate */
	if (scatter_elem_sz < (int)PAGE_SIZE)
		scatter_elem_sz = PAGE_SIZE;
	else if (!is_power_of_2(scatter_elem_sz))
		scatter_elem_sz = roundup_pow_of_two(scatter_elem_sz);
	if (def_reserved_size >= 0)
		sg_big_buff = def_reserved_size;
	else
		def_reserved_size = sg_big_buff;

	rc = register_chrdev_region(MKDEV(SCSI_GENERIC_MAJOR, 0),
				    SG_MAX_DEVS, "sg");
	if (rc)
		return rc;

	pr_info("Registered %s[char major=0x%x], version: %s, date: %s\n",
		"sg device ", SCSI_GENERIC_MAJOR, SG_VERSION_STR,
		sg_version_date);
	sg_sysfs_class = class_create(THIS_MODULE, "scsi_generic");
	if (IS_ERR(sg_sysfs_class)) {
		rc = PTR_ERR(sg_sysfs_class);
		goto err_out_unreg;
	}
	sg_sysfs_valid = true;
	rc = scsi_register_interface(&sg_interface);
	if (0 == rc) {
		sg_proc_init();
		return 0;
	}
	class_destroy(sg_sysfs_class);

err_out_unreg:
	unregister_chrdev_region(MKDEV(SCSI_GENERIC_MAJOR, 0), SG_MAX_DEVS);
	return rc;
}

#if !IS_ENABLED(CONFIG_SCSI_PROC_FS)
static int
sg_proc_init(void)
{
	return 0;
}
#endif

static void __exit
exit_sg(void)
{
	if (IS_ENABLED(CONFIG_SCSI_PROC_FS))
		remove_proc_subtree("scsi/sg", NULL);
	scsi_unregister_interface(&sg_interface);
	class_destroy(sg_sysfs_class);
	sg_sysfs_valid = false;
	unregister_chrdev_region(MKDEV(SCSI_GENERIC_MAJOR, 0),
				 SG_MAX_DEVS);
	idr_destroy(&sg_index_idr);
}

static inline bool
sg_chk_dio_allowed(struct sg_device *sdp, struct sg_request *srp,
		   int iov_count, int dir)
{
	if (sg_allow_dio && (srp->rq_flags & SG_FLAG_DIRECT_IO)) {
		if (dir != SG_DXFER_UNKNOWN && !iov_count) {
			if (!sdp->device->host->unchecked_isa_dma)
				return true;
		}
	}
	return false;
}

static void
sg_set_map_data(const struct sg_scatter_hold *schp, bool up_valid,
		struct rq_map_data *mdp)
{
	memset(mdp, 0, sizeof(*mdp));
	mdp->pages = schp->pages;
	mdp->page_order = schp->page_order;
	mdp->nr_entries = schp->num_sgat;
	mdp->offset = 0;
	mdp->null_mapped = !up_valid;
}

static int
sg_start_req(struct sg_request *srp, u8 *cmd, int cmd_len, int dxfer_dir)
{
	bool reserved, us_xfer;
	int res = 0;
	int dxfer_len = 0;
	int r0w = READ;
	unsigned int iov_count = 0;
	void __user *up;
	struct request *rq;
	struct scsi_request *scsi_rp;
	struct sg_fd *sfp = srp->parentfp;
	struct sg_device *sdp;
	struct sg_scatter_hold *req_schp;
	struct request_queue *q;
	struct rq_map_data *md = (void *)srp; /* want any non-NULL value */
	u8 *long_cmdp = NULL;
	__maybe_unused const char *cp = "";
	struct sg_slice_hdr3 *sh3p = &srp->s_hdr3;
	struct rq_map_data map_data;

	sdp = sfp->parentdp;
	if (cmd_len > BLK_MAX_CDB) {	/* for longer SCSI cdb_s */
		long_cmdp = kzalloc(cmd_len, GFP_KERNEL);
		if (!long_cmdp)
			return -ENOMEM;
		SG_LOG(5, sfp, "%s: long_cmdp=0x%pK ++\n", __func__, long_cmdp);
	}
	up = sh3p->dxferp;
	dxfer_len = (int)sh3p->dxfer_len;
	iov_count = sh3p->iovec_count;
	r0w = dxfer_dir == SG_DXFER_TO_DEV ? WRITE : READ;
	SG_LOG(4, sfp, "%s: dxfer_len=%d, data-%s\n", __func__, dxfer_len,
	       (r0w ? "OUT" : "IN"));
	q = sdp->device->request_queue;

	/*
	 * NOTE
	 *
	 * With scsi-mq enabled, there are a fixed number of preallocated
	 * requests equal in number to shost->can_queue.  If all of the
	 * preallocated requests are already in use, then blk_get_request()
	 * will sleep until an active command completes, freeing up a request.
	 * Although waiting in an asynchronous interface is less than ideal, we
	 * do not want to use BLK_MQ_REQ_NOWAIT here because userspace might
	 * not expect an EWOULDBLOCK from this condition.
	 */
	rq = blk_get_request(q, (r0w ? REQ_OP_SCSI_OUT : REQ_OP_SCSI_IN), 0);
	if (IS_ERR(rq)) {
		kfree(long_cmdp);
		return PTR_ERR(rq);
	}
	/* current sg_request protected by SG_RS_BUSY state */
	scsi_rp = scsi_req(rq);
	srp->rq = rq;

	if (cmd_len > BLK_MAX_CDB)
		scsi_rp->cmd = long_cmdp;
	memcpy(scsi_rp->cmd, cmd, cmd_len);
	scsi_rp->cmd_len = cmd_len;
	us_xfer = !(srp->rq_flags & SG_FLAG_NO_DXFER);
	assign_bit(SG_FRQ_NO_US_XFER, srp->frq_bm, !us_xfer);
	reserved = (sfp->rsv_srp == srp);
	rq->end_io_data = srp;
	scsi_rp->retries = SG_DEFAULT_RETRIES;
	req_schp = &srp->sgat_h;

	if (dxfer_len <= 0 || dxfer_dir == SG_DXFER_NONE) {
		SG_LOG(4, sfp, "%s: no data xfer [0x%pK]\n", __func__, srp);
		set_bit(SG_FRQ_NO_US_XFER, srp->frq_bm);
		goto fini;	/* path of reqs with no din nor dout */
	} else if (sg_chk_dio_allowed(sdp, srp, iov_count, dxfer_dir) &&
		   blk_rq_aligned(q, (unsigned long)up, dxfer_len)) {
		srp->rq_info |= SG_INFO_DIRECT_IO;
		md = NULL;
		if (IS_ENABLED(CONFIG_SCSI_PROC_FS))
			cp = "direct_io, ";
	} else {	/* normal IO and failed conditions for dio path */
		md = &map_data;
	}

	if (likely(md)) {	/* normal, "indirect" IO */
		if (unlikely((srp->rq_flags & SG_FLAG_MMAP_IO))) {
			/* mmap IO must use and fit in reserve request */
			if (!reserved || dxfer_len > req_schp->buflen)
				res = reserved ? -ENOMEM : -EBUSY;
		} else if (req_schp->buflen == 0) {
			int up_sz = max_t(int, dxfer_len, sfp->sgat_elem_sz);

			res = sg_mk_sgat(srp, sfp, up_sz);
		}
		if (res)
			goto fini;

		sg_set_map_data(req_schp, !!up, md);
		md->from_user = (dxfer_dir == SG_DXFER_TO_FROM_DEV);
	}

	if (unlikely(iov_count)) {
		struct iovec *iov = NULL;
		struct iov_iter i;

		res = import_iovec(r0w, up, iov_count, 0, &iov, &i);
		if (res < 0)
			goto fini;

		iov_iter_truncate(&i, dxfer_len);
		if (!iov_iter_count(&i)) {
			kfree(iov);
			res = -EINVAL;
			goto fini;
		}

		if (us_xfer)
			res = blk_rq_map_user_iov(q, rq, md, &i, GFP_ATOMIC);
		kfree(iov);
		if (IS_ENABLED(CONFIG_SCSI_PROC_FS))
			cp = "iov_count > 0";
	} else if (us_xfer) { /* setup for transfer data to/from user space */
		res = blk_rq_map_user(q, rq, md, up, dxfer_len, GFP_ATOMIC);
		if (IS_ENABLED(CONFIG_SCSI_PROC_FS) && res)
			SG_LOG(1, sfp, "%s: blk_rq_map_user() res=%d\n",
			       __func__, res);
	}
fini:
	if (unlikely(res)) {		/* failure, free up resources */
		scsi_req_free_cmd(scsi_rp);
		if (likely(!test_and_set_bit(SG_FRQ_BLK_PUT_REQ,
					     srp->frq_bm))) {
			srp->rq = NULL;
			blk_put_request(rq);
		}
	} else {
		srp->bio = rq->bio;
	}
	SG_LOG((res ? 1 : 4), sfp, "%s: %s res=%d [0x%pK]\n", __func__, cp,
	       res, srp);
	return res;
}

/*
 * Clean up mid-level and block layer resources of finished request. Sometimes
 * blk_rq_unmap_user() returns -4 (-EINTR) and this is why: "If we're in a
 * workqueue, the request is orphaned, so don't copy into a random user
 * address space, just free and return -EINTR so user space doesn't expect
 * any data." [block/bio.c]
 */
static void
sg_finish_scsi_blk_rq(struct sg_request *srp)
{
	int ret;
	struct sg_fd *sfp = srp->parentfp;

	SG_LOG(4, sfp, "%s: srp=0x%pK%s\n", __func__, srp,
	       (srp->parentfp->rsv_srp == srp) ? " rsv" : "");
	if (!test_bit(SG_FRQ_SYNC_INVOC, srp->frq_bm)) {
		atomic_dec(&sfp->submitted);
		atomic_dec(&sfp->waiting);
	}
	if (srp->bio) {
		bool us_xfer = !test_bit(SG_FRQ_NO_US_XFER, srp->frq_bm);

		if (us_xfer) {
			ret = blk_rq_unmap_user(srp->bio);
			if (ret) {	/* -EINTR (-4) can be ignored */
				SG_LOG(6, sfp,
				       "%s: blk_rq_unmap_user() --> %d\n",
				       __func__, ret);
			}
		}
		srp->bio = NULL;
	}
	/* In worst case READ data returned to user space by this point */

	/* Expect blk_put_request(rq) already called in sg_rq_end_io() */
	if (unlikely(!test_and_set_bit(SG_FRQ_BLK_PUT_REQ, srp->frq_bm))) {
		struct request *rq = srp->rq;

		if (rq) {       /* blk_get_request() may have failed */
			if (scsi_req(rq))
				scsi_req_free_cmd(scsi_req(rq));
			srp->rq = NULL;
			blk_put_request(rq);
		}
	}
}

static int
sg_mk_sgat(struct sg_request *srp, struct sg_fd *sfp, int minlen)
{
	int j, k, rem_sz, align_sz;
	int mx_sgat_elems = sfp->parentdp->max_sgat_elems;
	unsigned int elem_sz, order, o_order;
	const size_t ptr_sz = sizeof(struct page *);
	gfp_t mask_ap = GFP_ATOMIC | __GFP_COMP | __GFP_NOWARN | __GFP_ZERO;
	gfp_t mask_kz = GFP_ATOMIC | __GFP_NOWARN;
	struct sg_device *sdp = sfp->parentdp;
	struct sg_scatter_hold *schp = &srp->sgat_h;

	if (unlikely(minlen <= 0)) {
		if (minlen < 0)
			return -EFAULT;
		++minlen;	/* don't remember why */
	}
	/* round request up to next highest SG_DEF_SECTOR_SZ byte boundary */
	align_sz = ALIGN(minlen, SG_DEF_SECTOR_SZ);

	schp->pages = kcalloc(mx_sgat_elems, ptr_sz, mask_kz);
	SG_LOG(4, sfp, "%s: minlen=%d [sz=%zu, 0x%pK ++]\n", __func__, minlen,
	       mx_sgat_elems * ptr_sz, schp->pages);
	if (unlikely(!schp->pages))
		return -ENOMEM;

	elem_sz = sfp->sgat_elem_sz;    /* power of 2 and >= PAGE_SIZE */
	if (sdp && unlikely(sdp->device->host->unchecked_isa_dma))
		mask_ap |= GFP_DMA;
	o_order = get_order(elem_sz);
	order = o_order;

again:
	for (k = 0, rem_sz = align_sz; rem_sz > 0 && k < mx_sgat_elems;
	     ++k, rem_sz -= elem_sz) {
		schp->pages[k] = alloc_pages(mask_ap, order);
		if (!schp->pages[k])
			goto err_out;
		SG_LOG(5, sfp, "%s: k=%d, order=%d [0x%pK ++]\n", __func__, k,
		       order, schp->pages[k]);
	}
	schp->page_order = order;
	schp->num_sgat = k;
	SG_LOG(((order != o_order || rem_sz > 0) ? 2 : 5), sfp,
	       "%s: num_sgat=%d, order=%d,%d\n", __func__, k, o_order, order);
	if (unlikely(rem_sz > 0)) {	/* hit mx_sgat_elems */
		order = 0;		/* force exit */
		goto err_out;
	}
	schp->buflen = align_sz;
	return 0;
err_out:
	for (j = 0; j < k; ++j)
		__free_pages(schp->pages[j], order);

	if (--order >= 0) {
		elem_sz >>= 1;
		goto again;
	}
	kfree(schp->pages);
	schp->pages = NULL;
	return -ENOMEM;
}

static void
sg_remove_sgat_helper(struct sg_fd *sfp, struct sg_scatter_hold *schp)
{
	int k;
	void *p;

	if (!schp->pages)
		return;
	for (k = 0; k < schp->num_sgat; ++k) {
		p = schp->pages[k];
		SG_LOG(5, sfp, "%s: pg[%d]=0x%pK --\n", __func__, k, p);
		if (unlikely(!p))
			continue;
		__free_pages(p, schp->page_order);
	}
	SG_LOG(5, sfp, "%s: pg_order=%u, free pgs=0x%pK --\n", __func__,
	       schp->page_order, schp->pages);
	kfree(schp->pages);
}

/* Remove the data (possibly a sgat list) held by srp, not srp itself */
static void
sg_remove_sgat(struct sg_request *srp)
{
	struct sg_scatter_hold *schp = &srp->sgat_h; /* care: remove own data */
	struct sg_fd *sfp = srp->parentfp;

	SG_LOG(4, sfp, "%s: num_sgat=%d%s\n", __func__, schp->num_sgat,
	       ((srp->parentfp ? (sfp->rsv_srp == srp) : false) ?
		" [rsv]" : ""));
	sg_remove_sgat_helper(sfp, schp);

	memset(schp, 0, sizeof(*schp));         /* zeros buflen and dlen */
}

/*
 * For sg v1 and v2 interface: with a command yielding a data-in buffer, after
 * it has arrived in kernel memory, this function copies it to the user space,
 * appended to given struct sg_header object.
 */
static int
sg_read_append(struct sg_request *srp, void __user *outp, int num_xfer)
{
	int k, num, res;
	struct page *pgp;
	struct sg_scatter_hold *schp = &srp->sgat_h;

	SG_LOG(4, srp->parentfp, "%s: num_xfer=%d\n", __func__, num_xfer);
	if (unlikely(!outp || num_xfer <= 0))
		return (num_xfer == 0 && outp) ? 0 : -EINVAL;

	num = 1 << (PAGE_SHIFT + schp->page_order);
	for (k = 0, res = 0; k < schp->num_sgat; ++k) {
		pgp = schp->pages[k];
		if (unlikely(!pgp)) {
			res = -ENXIO;
			break;
		}
		if (num > num_xfer) {
			if (copy_to_user(outp, page_address(pgp), num_xfer))
				res = -EFAULT;
			break;
		} else {
			if (copy_to_user(outp, page_address(pgp), num)) {
				res = -EFAULT;
				break;
			}
			num_xfer -= num;
			if (num_xfer <= 0)
				break;
			outp += num;
		}
	}
	return res;
}

/*
 * If there are multiple requests outstanding, the speed of this function is
 * important. SG_PACK_ID_WILDCARD is -1 and that case is typically
 * the fast path. This function is only used in the non-blocking cases.
 * Returns pointer to (first) matching sg_request or NULL. If found,
 * sg_request state is moved from SG_RS_AWAIT_RCV to SG_RS_BUSY.
 */
static struct sg_request *
sg_find_srp_by_id(struct sg_fd *sfp, int pack_id)
{
	__maybe_unused bool is_bad_st = false;
	__maybe_unused enum sg_rq_state bad_sr_st = SG_RS_INACTIVE;
	bool search_for_1 = (pack_id != SG_PACK_ID_WILDCARD);
	int res;
	int num_waiting = atomic_read(&sfp->waiting);
	unsigned long idx;
	struct sg_request *srp = NULL;
	struct xarray *xafp = &sfp->srp_arr;

	if (num_waiting < 1)
		return NULL;
	if (unlikely(search_for_1)) {
		xa_for_each_marked(xafp, idx, srp, SG_XA_RQ_AWAIT) {
			if (!srp)
				continue;
			if (srp->pack_id != pack_id)
				continue;
			res = sg_rq_state_chg(srp, SG_RS_AWAIT_RCV, SG_RS_BUSY,
					      false, __func__);
			if (likely(res == 0))
				goto good;
			/* else another caller got it, move on */
			if (IS_ENABLED(CONFIG_SCSI_PROC_FS)) {
				is_bad_st = true;
				bad_sr_st = atomic_read(&srp->rq_st);
			}
			break;
		}
	} else {        /* search for any request is more likely */
		xa_for_each_marked(xafp, idx, srp, SG_XA_RQ_AWAIT) {
			if (!srp)
				continue;
			res = sg_rq_state_chg(srp, SG_RS_AWAIT_RCV, SG_RS_BUSY,
					      false, __func__);
			if (likely(res == 0))
				goto good;
		}
	}
	/* here if one of above loops does _not_ find a match */
	if (IS_ENABLED(CONFIG_SCSI_PROC_FS)) {
		if (search_for_1) {
			const char *cptp = "pack_id=";

			if (is_bad_st)
				SG_LOG(1, sfp, "%s: %s%d wrong state: %s\n",
				       __func__, cptp, pack_id,
				       sg_rq_st_str(bad_sr_st, true));
			else
				SG_LOG(6, sfp, "%s: %s%d not awaiting read\n",
				       __func__, cptp, pack_id);
		}
	}
	return NULL;
good:
	SG_LOG(6, sfp, "%s: %s%d found [srp=0x%pK]\n", __func__, "pack_id=",
	       pack_id, srp);
	return srp;
}

/*
 * Makes a new sg_request object. If 'first' is set then use GFP_KERNEL which
 * may take time but has improved chance of success, otherwise use GFP_ATOMIC.
 * Note that basic initialization is done but srp is not added to either sfp
 * list. On error returns twisted negated errno value (not NULL).
 */
static struct sg_request *
sg_mk_srp(struct sg_fd *sfp, bool first)
{
	struct sg_request *srp;
	gfp_t gfp =  __GFP_NOWARN;

	if (first)      /* prepared to wait if none already outstanding */
		srp = kzalloc(sizeof(*srp), gfp | GFP_KERNEL);
	else
		srp = kzalloc(sizeof(*srp), gfp | GFP_ATOMIC);
	if (srp) {
		atomic_set(&srp->rq_st, SG_RS_BUSY);
		srp->parentfp = sfp;
		return srp;
	} else {
		return ERR_PTR(-ENOMEM);
	}
}

static struct sg_request *
sg_mk_srp_sgat(struct sg_fd *sfp, bool first, int db_len)
{
	int res;
	struct sg_request *n_srp = sg_mk_srp(sfp, first);

	if (IS_ERR(n_srp))
		return n_srp;
	if (db_len > 0) {
		res = sg_mk_sgat(n_srp, sfp, db_len);
		if (res) {
			kfree(n_srp);
			return ERR_PTR(res);
		}
	}
	return n_srp;
}

/*
 * Irrespective of the given reserve request size, the minimum size requested
 * will be PAGE_SIZE (often 4096 bytes). Returns a pointer to reserve object or
 * a negated errno value twisted by ERR_PTR() macro. The actual number of bytes
 * allocated (maybe less than buflen) is in srp->sgat_h.buflen . Note that this
 * function is only called in contexts where locking is not required.
 */
static struct sg_request *
sg_build_reserve(struct sg_fd *sfp, int buflen)
{
	bool go_out = false;
	int res;
	struct sg_request *srp;

	SG_LOG(3, sfp, "%s: buflen=%d\n", __func__, buflen);
	srp = sg_mk_srp(sfp, xa_empty(&sfp->srp_arr));
	if (IS_ERR(srp))
		return srp;
	sfp->rsv_srp = srp;
	do {
		if (buflen < (int)PAGE_SIZE) {
			buflen = PAGE_SIZE;
			go_out = true;
		}
		res = sg_mk_sgat(srp, sfp, buflen);
		if (res == 0) {
			SG_LOG(4, sfp, "%s: final buflen=%d, srp=0x%pK ++\n",
			       __func__, buflen, srp);
			return srp;
		}
		if (go_out)
			return ERR_PTR(res);
		/* failed so remove, halve buflen, try again */
		sg_remove_sgat(srp);
		buflen >>= 1;   /* divide by 2 */
	} while (true);
}

/*
 * Setup an active request (soon to carry a SCSI command) to the current file
 * descriptor by creating a new one or re-using a request from the free
 * list (fl). If successful returns a valid pointer in SG_RS_BUSY state. On
 * failure returns a negated errno value twisted by ERR_PTR() macro.
 */
static struct sg_request *
sg_setup_req(struct sg_fd *sfp, int dxfr_len, struct sg_comm_wr_t *cwrp)
{
	bool act_empty = false;
	bool found = false;
	bool mk_new_srp = false;
	bool try_harder = false;
	int res;
	int num_inactive = 0;
	unsigned long idx, last_idx, iflags;
	struct sg_request *r_srp = NULL;	/* request to return */
	struct xarray *xafp = &sfp->srp_arr;
	__maybe_unused const char *cp;

start_again:
	cp = "";
	if (xa_empty(xafp)) {
		act_empty = true;
		mk_new_srp = true;
	} else if (!try_harder && dxfr_len < SG_DEF_SECTOR_SZ) {
		last_idx = ~0UL;
		xa_for_each_marked(xafp, idx, r_srp, SG_XA_RQ_INACTIVE) {
			if (!r_srp)
				continue;
			++num_inactive;
			if (dxfr_len < SG_DEF_SECTOR_SZ) {
				last_idx = idx;
				continue;
			}
		}
		/* If dxfr_len is small, use last inactive request */
		if (last_idx != ~0UL) {
			idx = last_idx;
			r_srp = xa_load(xafp, idx);
			if (!r_srp)
				goto start_again;
			if (sg_rq_state_chg(r_srp, SG_RS_INACTIVE, SG_RS_BUSY,
					    false, __func__))
				goto start_again; /* gone to another thread */
			cp = "toward back of srp_arr";
			found = true;
		}
	} else {
		xa_for_each_marked(xafp, idx, r_srp, SG_XA_RQ_INACTIVE) {
			if (!r_srp)
				continue;
			if (r_srp->sgat_h.buflen >= dxfr_len) {
				if (sg_rq_state_chg
					(r_srp, SG_RS_INACTIVE, SG_RS_BUSY,
					 false, __func__))
					continue;
				cp = "from front of srp_arr";
				found = true;
				break;
			}
		}
	}
	if (found) {
		r_srp->in_resid = 0;
		r_srp->rq_info = 0;
		r_srp->sense_len = 0;
		mk_new_srp = false;
	} else {
		mk_new_srp = true;
	}
	if (mk_new_srp) {
		bool allow_cmd_q = test_bit(SG_FFD_CMD_Q, sfp->ffd_bm);
		u32 n_idx;
		struct xa_limit xal = { .max = 0, .min = 0 };

		cp = "new";
		if (!allow_cmd_q && atomic_read(&sfp->submitted) > 0) {
			r_srp = ERR_PTR(-EDOM);
			SG_LOG(6, sfp, "%s: trying 2nd req but cmd_q=false\n",
			       __func__);
			goto fini;
		}
		r_srp = sg_mk_srp_sgat(sfp, act_empty, dxfr_len);
		if (IS_ERR(r_srp)) {
			if (!try_harder && dxfr_len < SG_DEF_SECTOR_SZ &&
			    num_inactive > 0) {
				try_harder = true;
				goto start_again;
			}
			goto fini;
		}
		atomic_set(&r_srp->rq_st, SG_RS_BUSY);
		xa_lock_irqsave(xafp, iflags);
		xal.max = atomic_inc_return(&sfp->req_cnt);
		res = __xa_alloc(xafp, &n_idx, r_srp, xal, GFP_KERNEL);
		xa_unlock_irqrestore(xafp, iflags);
		if (res < 0) {
			SG_LOG(1, sfp, "%s: xa_alloc() failed, errno=%d\n",
			       __func__,  -res);
			sg_remove_sgat(r_srp);
			kfree(r_srp);
			r_srp = ERR_PTR(-EPROTOTYPE);
			goto fini;
		}
		idx = n_idx;
		r_srp->rq_idx = idx;
		r_srp->parentfp = sfp;
		SG_LOG(4, sfp, "%s: mk_new_srp=0x%pK ++\n", __func__, r_srp);
	}
	r_srp->frq_bm[0] = cwrp->frq_bm[0];	/* assumes <= 32 req flags */
	r_srp->sgat_h.dlen = dxfr_len;/* must be <= r_srp->sgat_h.buflen */
	r_srp->cmd_opcode = 0xff;  /* set invalid opcode (VS), 0x0 is TUR */
fini:
	if (IS_ERR(r_srp))
		SG_LOG(1, sfp, "%s: err=%ld\n", __func__, PTR_ERR(r_srp));
	if (!IS_ERR(r_srp))
		SG_LOG(4, sfp, "%s: %s r_srp=0x%pK\n", __func__, cp, r_srp);
	return r_srp;
}

/*
 * Moves a completed sg_request object to the free list and sets it to
 * SG_RS_INACTIVE which makes it available for re-use. Requests with no data
 * associated are appended to the tail of the free list while other requests
 * are prepended to the head of the free list.
 */
static void
sg_deact_request(struct sg_fd *sfp, struct sg_request *srp)
{
	unsigned long iflags;

	if (WARN_ON(!sfp || !srp))
		return;
	atomic_set(&srp->rq_st, SG_RS_INACTIVE);
	xa_lock_irqsave(&sfp->srp_arr, iflags);
	__xa_set_mark(&sfp->srp_arr, srp->rq_idx, SG_XA_RQ_INACTIVE);
	__xa_clear_mark(&sfp->srp_arr, srp->rq_idx, SG_XA_RQ_AWAIT);
	xa_unlock_irqrestore(&sfp->srp_arr, iflags);
}

/* Returns pointer to sg_fd object or negated errno twisted by ERR_PTR */
static struct sg_fd *
sg_add_sfp(struct sg_device *sdp)
{
	bool reduced = false;
	int rbuf_len, res;
	u32 idx;
	long err;
	unsigned long iflags;
	struct sg_fd *sfp;
	struct sg_request *srp = NULL;
	struct xarray *xadp = &sdp->sfp_arr;
	struct xarray *xafp;
	struct xa_limit xal;

	sfp = kzalloc(sizeof(*sfp), GFP_ATOMIC | __GFP_NOWARN);
	if (!sfp)
		return ERR_PTR(-ENOMEM);
	init_waitqueue_head(&sfp->read_wait);
	xa_init_flags(&sfp->srp_arr, XA_FLAGS_ALLOC | XA_FLAGS_LOCK_IRQ);
	xafp = &sfp->srp_arr;
	kref_init(&sfp->f_ref);
	mutex_init(&sfp->f_mutex);
	sfp->timeout = SG_DEFAULT_TIMEOUT;
	sfp->timeout_user = SG_DEFAULT_TIMEOUT_USER;
	/* other bits in sfp->ffd_bm[1] cleared by kzalloc() above */
	__assign_bit(SG_FFD_FORCE_PACKID, sfp->ffd_bm, SG_DEF_FORCE_PACK_ID);
	__assign_bit(SG_FFD_CMD_Q, sfp->ffd_bm, SG_DEF_COMMAND_Q);
	__assign_bit(SG_FFD_KEEP_ORPHAN, sfp->ffd_bm, SG_DEF_KEEP_ORPHAN);
	__assign_bit(SG_FFD_Q_AT_TAIL, sfp->ffd_bm, SG_DEFAULT_Q_AT);
	/*
	 * SG_SCATTER_SZ initializes scatter_elem_sz but different value may
	 * be given as driver/module parameter (e.g. 'scatter_elem_sz=8192').
	 * Any user provided number will be changed to be PAGE_SIZE as a
	 * minimum, otherwise it will be rounded down (if required) to a
	 * power of 2. So it will always be a power of 2.
	 */
	sfp->sgat_elem_sz = scatter_elem_sz;
	sfp->parentdp = sdp;
	atomic_set(&sfp->submitted, 0);
	atomic_set(&sfp->waiting, 0);
	atomic_set(&sfp->req_cnt, 0);

	if (unlikely(SG_IS_DETACHING(sdp))) {
		SG_LOG(1, sfp, "%s: detaching\n", __func__);
		kfree(sfp);
		return ERR_PTR(-ENODEV);
	}
	if (unlikely(sg_big_buff != def_reserved_size))
		sg_big_buff = def_reserved_size;

	rbuf_len = min_t(int, sg_big_buff, sdp->max_sgat_sz);
	if (rbuf_len > 0) {
		struct xa_limit xalrq = { .max = 0, .min = 0 };

		srp = sg_build_reserve(sfp, rbuf_len);
		if (IS_ERR(srp)) {
			kfree(sfp);
			err = PTR_ERR(srp);
			SG_LOG(1, sfp, "%s: build reserve err=%ld\n", __func__,
			       -err);
			return ERR_PTR(err);
		}
		if (srp->sgat_h.buflen < rbuf_len) {
			reduced = true;
			SG_LOG(2, sfp,
			       "%s: reserve reduced from %d to buflen=%d\n",
			       __func__, rbuf_len, srp->sgat_h.buflen);
		}
		xa_lock_irqsave(xafp, iflags);
		xalrq.max = atomic_inc_return(&sfp->req_cnt);
		res = __xa_alloc(xafp, &idx, srp, xalrq, GFP_ATOMIC);
		xa_unlock_irqrestore(xafp, iflags);
		if (res < 0) {
			SG_LOG(1, sfp, "%s: xa_alloc(srp) bad, errno=%d\n",
			       __func__,  -res);
			sg_remove_sgat(srp);
			kfree(srp);
			kfree(sfp);
			return ERR_PTR(-EPROTOTYPE);
		}
		srp->rq_idx = idx;
		srp->parentfp = sfp;
		sg_rq_state_chg(srp, 0, SG_RS_INACTIVE, true, __func__);
	}
	if (!reduced) {
		SG_LOG(4, sfp, "%s: built reserve buflen=%d\n", __func__,
		       rbuf_len);
	}
	xa_lock_irqsave(xadp, iflags);
	xal.min = 0;
	xal.max = atomic_read(&sdp->open_cnt);
	res = __xa_alloc(xadp, &idx, sfp, xal, GFP_KERNEL);
	xa_unlock_irqrestore(xadp, iflags);
	if (res < 0) {
		pr_warn("%s: xa_alloc(sdp) bad, o_count=%d, errno=%d\n",
			__func__, xal.max, -res);
		if (srp) {
			sg_remove_sgat(srp);
			kfree(srp);
		}
		kfree(sfp);
		return ERR_PTR(res);
	}
	sfp->idx = idx;
	kref_get(&sdp->d_ref);
	__module_get(THIS_MODULE);
	SG_LOG(3, sfp, "%s: success, sfp=0x%pK ++\n", __func__, sfp);
	return sfp;
}

/*
 * A successful call to sg_release() will result, at some later time, to this
 * function being invoked. All requests associated with this file descriptor
 * should be completed or cancelled when this function is called (due to
 * sfp->f_ref). Also the file descriptor itself has not been accessible since
 * it was list_del()-ed by the preceding sg_remove_sfp() call. So no locking
 * is required. sdp should never be NULL but to make debugging more robust,
 * this function will not blow up in that case.
 */
static void
sg_remove_sfp_usercontext(struct work_struct *work)
{
	__maybe_unused int o_count;
	unsigned long idx, iflags;
	struct sg_device *sdp;
	struct sg_fd *sfp = container_of(work, struct sg_fd, ew_fd.work);
	struct sg_fd *e_sfp;
	struct sg_request *srp;
	struct sg_request *e_srp;
	struct xarray *xafp = &sfp->srp_arr;
	struct xarray *xadp;

	if (!sfp) {
		pr_warn("sg: %s: sfp is NULL\n", __func__);
		return;
	}
	sdp = sfp->parentdp;
	xadp = &sdp->sfp_arr;

	/* Cleanup any responses which were never read(). */
	xa_for_each(xafp, idx, srp) {
		if (!srp)
			continue;
		if (!xa_get_mark(xafp, srp->rq_idx, SG_XA_RQ_INACTIVE))
			sg_finish_scsi_blk_rq(srp);
		sg_remove_sgat(srp);
		xa_lock_irqsave(xafp, iflags);
		e_srp = __xa_erase(xafp, srp->rq_idx);
		xa_unlock_irqrestore(xafp, iflags);
		if (srp != e_srp)
			SG_LOG(1, sfp, "%s: xa_erase() return unexpected\n",
			       __func__);
		SG_LOG(6, sfp, "%s: kfree: srp=%pK --\n", __func__, srp);
		kfree(srp);
	}
	xa_destroy(xafp);
	xa_lock_irqsave(xadp, iflags);
	e_sfp = __xa_erase(xadp, sfp->idx);
	xa_unlock_irqrestore(xadp, iflags);
	if (unlikely(sfp != e_sfp))
		SG_LOG(1, sfp, "%s: xa_erase() return unexpected\n",
		       __func__);
	o_count = atomic_dec_return(&sdp->open_cnt);
	SG_LOG(3, sfp, "%s: dev o_count after=%d: sfp=0x%pK --\n", __func__,
	       o_count, sfp);
	kfree(sfp);

	if (sdp) {
		scsi_device_put(sdp->device);
		kref_put(&sdp->d_ref, sg_device_destroy);
	}
	module_put(THIS_MODULE);
}

static void
sg_remove_sfp(struct kref *kref)
{
	struct sg_fd *sfp = container_of(kref, struct sg_fd, f_ref);

	INIT_WORK(&sfp->ew_fd.work, sg_remove_sfp_usercontext);
	schedule_work(&sfp->ew_fd.work);
}

static int
sg_idr_max_id(int id, void *p, void *data)
{
	int *k = data;

	if (*k < id)
		*k = id;

	return 0;
}

/* must be called with sg_index_lock held */
static struct sg_device *
sg_lookup_dev(int dev)
{
	return idr_find(&sg_index_idr, dev);
}

static struct sg_device *
sg_get_dev(int dev)
{
	struct sg_device *sdp;
	unsigned long flags;

	read_lock_irqsave(&sg_index_lock, flags);
	sdp = sg_lookup_dev(dev);
	if (!sdp)
		sdp = ERR_PTR(-ENXIO);
	else if (SG_IS_DETACHING(sdp)) {
		/* If detaching, then the refcount may already be 0, in
		 * which case it would be a bug to do kref_get().
		 */
		sdp = ERR_PTR(-ENODEV);
	} else
		kref_get(&sdp->d_ref);
	read_unlock_irqrestore(&sg_index_lock, flags);

	return sdp;
}

#if IS_ENABLED(CONFIG_SCSI_PROC_FS)
static const char *
sg_rq_st_str(enum sg_rq_state rq_st, bool long_str)
{
	switch (rq_st) {	/* request state */
	case SG_RS_INACTIVE:
		return long_str ? "inactive" :  "ina";
	case SG_RS_INFLIGHT:
		return long_str ? "inflight" : "act";
	case SG_RS_AWAIT_RCV:
		return long_str ? "await_receive" : "rcv";
	case SG_RS_RCV_DONE:
		return long_str ? "receive_done" : "fin";
	case SG_RS_BUSY:
		return long_str ? "busy" : "bsy";
	default:
		return long_str ? "unknown" : "unk";
	}
}

#elif IS_ENABLED(SG_LOG_ACTIVE)

static const char *
sg_rq_st_str(enum sg_rq_state rq_st, bool long_str)
{
	return "";
}
#endif

#if IS_ENABLED(CONFIG_SCSI_PROC_FS)     /* long, almost to end of file */
static int sg_proc_seq_show_int(struct seq_file *s, void *v);

static int sg_proc_single_open_adio(struct inode *inode, struct file *filp);
static ssize_t sg_proc_write_adio(struct file *filp, const char __user *buffer,
			          size_t count, loff_t *off);
static const struct proc_ops adio_proc_ops = {
	.proc_open	= sg_proc_single_open_adio,
	.proc_read	= seq_read,
	.proc_lseek	= seq_lseek,
	.proc_write	= sg_proc_write_adio,
	.proc_release	= single_release,
};

static int sg_proc_single_open_dressz(struct inode *inode, struct file *filp);
static ssize_t sg_proc_write_dressz(struct file *filp, 
		const char __user *buffer, size_t count, loff_t *off);
static const struct proc_ops dressz_proc_ops = {
	.proc_open	= sg_proc_single_open_dressz,
	.proc_read	= seq_read,
	.proc_lseek	= seq_lseek,
	.proc_write	= sg_proc_write_dressz,
	.proc_release	= single_release,
};

static int sg_proc_seq_show_version(struct seq_file *s, void *v);
static int sg_proc_seq_show_devhdr(struct seq_file *s, void *v);
static int sg_proc_seq_show_dev(struct seq_file *s, void *v);
static void * dev_seq_start(struct seq_file *s, loff_t *pos);
static void * dev_seq_next(struct seq_file *s, void *v, loff_t *pos);
static void dev_seq_stop(struct seq_file *s, void *v);
static const struct seq_operations dev_seq_ops = {
	.start = dev_seq_start,
	.next  = dev_seq_next,
	.stop  = dev_seq_stop,
	.show  = sg_proc_seq_show_dev,
};

static int sg_proc_seq_show_devstrs(struct seq_file *s, void *v);
static const struct seq_operations devstrs_seq_ops = {
	.start = dev_seq_start,
	.next  = dev_seq_next,
	.stop  = dev_seq_stop,
	.show  = sg_proc_seq_show_devstrs,
};

static int sg_proc_seq_show_debug(struct seq_file *s, void *v);
static const struct seq_operations debug_seq_ops = {
	.start = dev_seq_start,
	.next  = dev_seq_next,
	.stop  = dev_seq_stop,
	.show  = sg_proc_seq_show_debug,
};

static int
sg_proc_init(void)
{
	struct proc_dir_entry *p;

	p = proc_mkdir("scsi/sg", NULL);
	if (!p)
		return 1;

	proc_create("allow_dio", 0644, p, &adio_proc_ops);
	proc_create_seq("debug", 0444, p, &debug_seq_ops);
	proc_create("def_reserved_size", 0644, p, &dressz_proc_ops);
	proc_create_single("device_hdr", 0444, p, sg_proc_seq_show_devhdr);
	proc_create_seq("devices", 0444, p, &dev_seq_ops);
	proc_create_seq("device_strs", 0444, p, &devstrs_seq_ops);
	proc_create_single("version", 0444, p, sg_proc_seq_show_version);
	return 0;
}

static int
sg_last_dev(void)
{
	int k = -1;
	unsigned long iflags;

	read_lock_irqsave(&sg_index_lock, iflags);
	idr_for_each(&sg_index_idr, sg_idr_max_id, &k);
	read_unlock_irqrestore(&sg_index_lock, iflags);
	return k + 1;		/* origin 1 */
}

static int
sg_proc_seq_show_int(struct seq_file *s, void *v)
{
	seq_printf(s, "%d\n", *((int *)s->private));
	return 0;
}

static int
sg_proc_single_open_adio(struct inode *inode, struct file *filp)
{
	return single_open(filp, sg_proc_seq_show_int, &sg_allow_dio);
}

static ssize_t 
sg_proc_write_adio(struct file *filp, const char __user *buffer,
		   size_t count, loff_t *off)
{
	int err;
	unsigned long num;

	if (!capable(CAP_SYS_ADMIN) || !capable(CAP_SYS_RAWIO))
		return -EACCES;
	err = kstrtoul_from_user(buffer, count, 0, &num);
	if (err)
		return err;
	sg_allow_dio = num ? 1 : 0;
	return count;
}

static int
sg_proc_single_open_dressz(struct inode *inode, struct file *filp)
{
	return single_open(filp, sg_proc_seq_show_int, &sg_big_buff);
}

static ssize_t 
sg_proc_write_dressz(struct file *filp, const char __user *buffer,
		     size_t count, loff_t *off)
{
	int err;
	unsigned long k = ULONG_MAX;

	if (!capable(CAP_SYS_ADMIN) || !capable(CAP_SYS_RAWIO))
		return -EACCES;

	err = kstrtoul_from_user(buffer, count, 0, &k);
	if (err)
		return err;
	if (k <= 1048576) {	/* limit "big buff" to 1 MB */
		sg_big_buff = k;
		return count;
	}
	return -ERANGE;
}

static int
sg_proc_seq_show_version(struct seq_file *s, void *v)
{
	seq_printf(s, "%d\t%s [%s]\n", sg_version_num, SG_VERSION_STR,
		   sg_version_date);
	return 0;
}

static int
sg_proc_seq_show_devhdr(struct seq_file *s, void *v)
{
	seq_puts(s, "host\tchan\tid\tlun\ttype\topens\tqdepth\tbusy\tonline\n");
	return 0;
}

struct sg_proc_deviter {
	loff_t	index;
	size_t	max;
	int fd_index;
};

static void *
dev_seq_start(struct seq_file *s, loff_t *pos)
{
	struct sg_proc_deviter *it = kzalloc(sizeof(*it), GFP_KERNEL);

	s->private = it;
	if (! it)
		return NULL;

	it->index = *pos;
	it->max = sg_last_dev();
	if (it->index >= it->max)
		return NULL;
	return it;
}

static void *
dev_seq_next(struct seq_file *s, void *v, loff_t *pos)
{
	struct sg_proc_deviter *it = s->private;

	*pos = ++it->index;
	return (it->index < it->max) ? it : NULL;
}

static void
dev_seq_stop(struct seq_file *s, void *v)
{
	kfree(s->private);
}

static int
sg_proc_seq_show_dev(struct seq_file *s, void *v)
{
	struct sg_proc_deviter *it = (struct sg_proc_deviter *)v;
	struct sg_device *sdp;
	struct scsi_device *scsidp;
	unsigned long iflags;

	read_lock_irqsave(&sg_index_lock, iflags);
	sdp = it ? sg_lookup_dev(it->index) : NULL;
	if (!sdp || !sdp->device || SG_IS_DETACHING(sdp))
		seq_puts(s, "-1\t-1\t-1\t-1\t-1\t-1\t-1\t-1\t-1\n");
	else {
		scsidp = sdp->device;
		seq_printf(s, "%d\t%d\t%d\t%llu\t%d\t%d\t%d\t%d\t%d\n",
			      scsidp->host->host_no, scsidp->channel,
			      scsidp->id, scsidp->lun, (int) scsidp->type,
			      1,
			      (int) scsidp->queue_depth,
			      (int) atomic_read(&scsidp->device_busy),
			      (int) scsi_device_online(scsidp));
	}
	read_unlock_irqrestore(&sg_index_lock, iflags);
	return 0;
}

static int
sg_proc_seq_show_devstrs(struct seq_file *s, void *v)
{
	struct sg_proc_deviter *it = (struct sg_proc_deviter *)v;
	struct sg_device *sdp;
	struct scsi_device *scsidp;
	unsigned long iflags;

	read_lock_irqsave(&sg_index_lock, iflags);
	sdp = it ? sg_lookup_dev(it->index) : NULL;
	scsidp = sdp ? sdp->device : NULL;
	if (sdp && scsidp && !SG_IS_DETACHING(sdp))
		seq_printf(s, "%8.8s\t%16.16s\t%4.4s\n",
			   scsidp->vendor, scsidp->model, scsidp->rev);
	else
		seq_puts(s, "<no active device>\n");
	read_unlock_irqrestore(&sg_index_lock, iflags);
	return 0;
}

/* must be called while holding sg_index_lock */
static void
sg_proc_debug_helper(struct seq_file *s, struct sg_device *sdp)
{
	int k;
	unsigned long idx, idx2;
	struct sg_request *srp;
	struct sg_fd *fp;
	const char * cp;
	unsigned int ms;

	k = 0;
	xa_for_each(&sdp->sfp_arr, idx, fp) {
		if (!fp)
			continue;
		k++;
		seq_printf(s, "   FD(%d): timeout=%dms buflen=%d (res)sgat=%d low_dma=%d idx=%lu\n",
			   k, jiffies_to_msecs(fp->timeout),
			   fp->rsv_srp->sgat_h.buflen,
			   (int)fp->rsv_srp->sgat_h.num_sgat,
			   (int)sdp->device->host->unchecked_isa_dma, idx);
		seq_printf(s, "   cmd_q=%d f_packid=%d k_orphan=%d closed=0\n",
			   (int)test_bit(SG_FFD_CMD_Q, fp->ffd_bm),
			   (int)test_bit(SG_FFD_FORCE_PACKID, fp->ffd_bm),
			   (int)test_bit(SG_FFD_KEEP_ORPHAN, fp->ffd_bm));
		seq_printf(s, "   submitted=%d waiting=%d\n",
			   atomic_read(&fp->submitted),
			   atomic_read(&fp->waiting));
		xa_for_each(&fp->srp_arr, idx2, srp) {
			const struct sg_slice_hdr3 *sh3p = &srp->s_hdr3;
			bool is_v3 = (sh3p->interface_id != '\0');
			enum sg_rq_state rq_st = atomic_read(&srp->rq_st);

			if (!srp)
				continue;
			if (srp->parentfp->rsv_srp == srp) {
				if (is_v3 && (SG_FLAG_MMAP_IO & sh3p->flags))
					cp = "     mmap>> ";
				else
					cp = "     rb>> ";
			} else {
				if (SG_INFO_DIRECT_IO_MASK & srp->rq_info)
					cp = "     dio>> ";
				else
					cp = "     ";
			}
			seq_puts(s, cp);
			seq_puts(s, sg_rq_st_str(rq_st, false));
			seq_printf(s, ": id=%d len/blen=%d/%d",
				   srp->pack_id, srp->sgat_h.dlen,
				   srp->sgat_h.buflen);
			if (rq_st == SG_RS_AWAIT_RCV ||
			    rq_st == SG_RS_RCV_DONE) {
				seq_printf(s, " dur=%d", srp->duration);
				goto fin_line;
			}
			ms = jiffies_to_msecs(jiffies);
			seq_printf(s, " t_o/elap=%d/%d",
				   (is_v3 ? sh3p->timeout :
					    jiffies_to_msecs(fp->timeout)),
				   (ms > srp->duration ?  ms - srp->duration :
							  0));
fin_line:
			seq_printf(s, "ms sgat=%d op=0x%02x\n",
				   srp->sgat_h.num_sgat, (int)srp->cmd_opcode);
		}
		if (xa_empty(&fp->srp_arr))
			seq_puts(s, "     No requests active\n");
	}
}

static int
sg_proc_seq_show_debug(struct seq_file *s, void *v)
{
	struct sg_proc_deviter *it = (struct sg_proc_deviter *)v;
	struct sg_device *sdp;
	unsigned long iflags;

	if (it && (0 == it->index))
		seq_printf(s, "max_active_device=%d  def_reserved_size=%d\n",
			   (int)it->max, sg_big_buff);

	read_lock_irqsave(&sg_index_lock, iflags);
	sdp = it ? sg_lookup_dev(it->index) : NULL;
	if (NULL == sdp)
		goto skip;
	if (!xa_empty(&sdp->sfp_arr)) {
		seq_printf(s, " >>> device=%s ", sdp->disk->disk_name);
		if (SG_IS_DETACHING(sdp))
			seq_puts(s, "detaching pending close ");
		else if (sdp->device) {
			struct scsi_device *scsidp = sdp->device;

			seq_printf(s, "%d:%d:%d:%llu   em=%d",
				   scsidp->host->host_no,
				   scsidp->channel, scsidp->id,
				   scsidp->lun,
				   scsidp->host->hostt->emulated);
		}
		seq_printf(s, " max_sgat_sz=%d excl=%d open_cnt=%d\n",
			   sdp->max_sgat_sz, SG_HAVE_EXCLUDE(sdp),
			   atomic_read(&sdp->open_cnt));
		sg_proc_debug_helper(s, sdp);
	}
skip:
	read_unlock_irqrestore(&sg_index_lock, iflags);
	return 0;
}

#endif				/* CONFIG_SCSI_PROC_FS (~300 lines back) */

module_init(init_sg);
module_exit(exit_sg);

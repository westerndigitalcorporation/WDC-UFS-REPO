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

#define SG_DEFAULT_TIMEOUT mult_frac(SG_DEFAULT_TIMEOUT_USER, HZ, USER_HZ)

/* Bit positions (flags) for sg_device::fdev_bm bitmask follow */
#define SG_FDEV_EXCLUDE		0	/* have fd open with O_EXCL */
#define SG_FDEV_DETACHING	1	/* may be unexpected device removal */
#define SG_FDEV_LOG_SENSE	2	/* set by ioctl(SG_SET_DEBUG) */

int sg_big_buff = SG_DEF_RESERVED_SIZE;
/* N.B. This variable is readable and writeable via
   /proc/scsi/sg/def_reserved_size . Each time sg_open() is called a buffer
   of this size (or less if there is not enough memory) will be reserved
   for use by this file descriptor. [Deprecated usage: this variable is also
   readable via /proc/sys/kernel/sg-big-buff if the sg driver is built into
   the kernel (i.e. it is not a module).] */
static int def_reserved_size = -1;	/* picks up init parameter */
static int sg_allow_dio = SG_ALLOW_DIO_DEF;

static int scatter_elem_sz = SG_SCATTER_SZ;
static int scatter_elem_sz_prev = SG_SCATTER_SZ;

#define SG_DEF_SECTOR_SZ 512

static int sg_add_device(struct device *, struct class_interface *);
static void sg_remove_device(struct device *, struct class_interface *);

static DEFINE_IDR(sg_index_idr);
static DEFINE_RWLOCK(sg_index_lock); /* Also used to lock fd list for device */

static struct class_interface sg_interface = {
	.add_dev        = sg_add_device,
	.remove_dev     = sg_remove_device,
};

struct sg_scatter_hold {     /* holding area for scsi scatter gather info */
	struct page **pages;	/* num_sgat element array of struct page* */
	int buflen;		/* capacity in bytes (dlen<=buflen) */
	int dlen;		/* current valid data length of this req */
	u16 page_order;		/* byte_len = (page_size*(2**page_order)) */
	u16 num_sgat;		/* actual number of scatter-gather segments */
	unsigned int sglist_len; /* size of malloc'd scatter-gather list ++ */
	char dio_in_use;	/* 0->indirect IO (or mmap), 1->dio */
	u8 cmd_opcode;		/* first byte of command */
};

struct sg_device;		/* forward declarations */
struct sg_fd;

struct sg_request {	/* SG_MAX_QUEUE requests outstanding per file */
	struct list_head entry;	/* list entry */
	struct sg_fd *parentfp;	/* NULL -> not in use */
	struct sg_scatter_hold data;	/* hold buffer, perhaps scatter list */
	struct sg_io_hdr header;  /* scsi command+info, see <scsi/sg.h> */
	u8 sense_b[SCSI_SENSE_BUFFERSIZE];
	char res_used;		/* 1 -> using reserve buffer, 0 -> not ... */
	char orphan;		/* 1 -> drop on sight, 0 -> normal */
	char sg_io_owned;	/* 1 -> packet belongs to SG_IO */
	/* done protected by rq_list_lock */
	char done;		/* 0->before bh, 1->before read, 2->read */
	struct request *rq;	/* released in sg_rq_end_io(), bio kept */
	struct bio *bio;	/* kept until this req -->SG_RS_INACTIVE */
	struct execute_work ew_orph;	/* harvest orphan request */
};

struct sg_fd {		/* holds the state of a file descriptor */
	struct list_head sfd_entry;	/* member sg_device::sfds list */
	struct sg_device *parentdp;	/* owning device */
	wait_queue_head_t read_wait;	/* queue read until command done */
	spinlock_t rq_list_lock;	/* protect access to list in req_arr */
	struct mutex f_mutex;	/* protect against changes in this fd */
	int timeout;		/* defaults to SG_DEFAULT_TIMEOUT      */
	int timeout_user;	/* defaults to SG_DEFAULT_TIMEOUT_USER */
	atomic_t submitted;	/* number inflight or awaiting read */
	atomic_t waiting;	/* number of requests awaiting read */
	struct sg_scatter_hold reserve;	/* buffer for this file descriptor */
	struct list_head rq_list; /* head of request list */
	struct fasync_struct *async_qp;	/* used by asynchronous notification */
	struct sg_request req_arr[SG_MAX_QUEUE];/* use as singly-linked list */
	char force_packid;	/* 1 -> pack_id input to read(), 0 -> ignored */
	char cmd_q;		/* 1 -> allow command queuing, 0 -> don't */
	u8 next_cmd_len;	/* 0: automatic, >0: use on next write() */
	char keep_orphan;	/* 0 -> drop orphan (def), 1 -> keep for read() */
	char mmap_called;	/* 0 -> mmap() never called on this fd */
	char res_in_use;	/* 1 -> 'reserve' array in use */
	struct kref f_ref;
	struct execute_work ew_fd;  /* harvest all fd resources and lists */
};

struct sg_device { /* holds the state of each scsi generic device */
	struct scsi_device *device;
	wait_queue_head_t open_wait;    /* queue open() when O_EXCL present */
	struct mutex open_rel_lock;     /* held when in open() or release() */
	struct list_head sfds;
	rwlock_t sfd_lock;      /* protect access to sfd list */
	int max_sgat_sz;	/* max number of bytes in sgat list */
	u32 index;		/* device index number */
	atomic_t open_cnt;	/* count of opens (perhaps < num(sfds) ) */
	unsigned long fdev_bm[1];	/* see SG_FDEV_* defines above */
	struct gendisk *disk;
	struct cdev *cdev;
	struct kref d_ref;
};

struct sg_comm_wr_t {  /* arguments to sg_common_write() */
	int timeout;
	int blocking;
	struct sg_request *srp;
	u8 *cmnd;
};

/* tasklet or soft irq callback */
static void sg_rq_end_io(struct request *rq, blk_status_t status);
/* Declarations of other static functions used before they are defined */
static int sg_proc_init(void);
static int sg_start_req(struct sg_request *srp, u8 *cmd);
static int sg_finish_scsi_blk_rq(struct sg_request *srp);
static int sg_build_indirect(struct sg_scatter_hold *schp, struct sg_fd *sfp,
			     int buff_size);
static ssize_t sg_submit(struct sg_fd *sfp, struct file *filp,
			 const char __user *buf, size_t count, bool blocking,
			 bool read_only, bool sg_io_owned,
			 struct sg_request **o_srp);
static int sg_common_write(struct sg_fd *sfp, struct sg_comm_wr_t *cwp);
static int sg_read_append(struct sg_request *srp, void __user *outp,
			  int num_xfer);
static void sg_remove_scat(struct sg_fd *sfp, struct sg_scatter_hold *schp);
static void sg_build_reserve(struct sg_fd *sfp, int req_size);
static void sg_link_reserve(struct sg_fd *sfp, struct sg_request *srp,
			    int size);
static void sg_unlink_reserve(struct sg_fd *sfp, struct sg_request *srp);
static struct sg_fd *sg_add_sfp(struct sg_device *sdp);
static void sg_remove_sfp(struct kref *);
static struct sg_request *sg_setup_req(struct sg_fd *sfp);
static int sg_remove_request(struct sg_fd *sfp, struct sg_request *srp);
static struct sg_device *sg_get_dev(int dev);
static void sg_device_destroy(struct kref *kref);

#define SZ_SG_HEADER ((int)sizeof(struct sg_header))	/* v1 and v2 header */
#define SZ_SG_IO_HDR ((int)sizeof(struct sg_io_hdr))	/* v3 header */
#define SZ_SG_REQ_INFO ((int)sizeof(struct sg_req_info))

#define SG_IS_DETACHING(sdp) test_bit(SG_FDEV_DETACHING, (sdp)->fdev_bm)
#define SG_HAVE_EXCLUDE(sdp) test_bit(SG_FDEV_EXCLUDE, (sdp)->fdev_bm)

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
	struct request_queue *q;
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
	/* scsi_block_when_processing_errors() may block so bypass
	 * check if O_NONBLOCK. Permits SCSI commands to be issued
	 * during error recovery. Tread carefully. */
	if (!((op_flags & O_NONBLOCK) ||
	      scsi_block_when_processing_errors(sdp->device))) {
		res = -ENXIO;
		/* we are in error recovery for this device */
		goto error_out;
	}

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

	if (atomic_read(&sdp->open_cnt) < 1) {  /* no existing opens */
		clear_bit(SG_FDEV_LOG_SENSE, sdp->fdev_bm);
		q = sdp->device->request_queue;
		sdp->max_sgat_sz = queue_max_segments(q);
	}
	sfp = sg_add_sfp(sdp);		/* increments sdp->d_ref */
	if (IS_ERR(sfp)) {
		res = PTR_ERR(sfp);
		goto out_undo;
	}

	filp->private_data = sfp;
	atomic_inc(&sdp->open_cnt);
	mutex_unlock(&sdp->open_rel_lock);
	SG_LOG(3, sfp, "%s: minor=%d, op_flags=0x%x; %s count prior=%d%s\n",
	       __func__, min_dev, op_flags, "device open",
	       atomic_read(&sdp->open_cnt),
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
	struct sg_device *sdp;
	struct sg_fd *sfp;

	sfp = filp->private_data;
	sdp = sfp->parentdp;
	SG_LOG(3, sfp, "%s: device open count prior=%d\n", __func__,
	       atomic_read(&sdp->open_cnt));
	if (!sdp)
		return -ENXIO;

	mutex_lock(&sdp->open_rel_lock);
	scsi_autopm_put_device(sdp->device);
	kref_put(&sfp->f_ref, sg_remove_sfp);
	atomic_dec(&sdp->open_cnt);

	/* possibly many open()s waiting on exlude clearing, start many;
	 * only open(O_EXCL)s wait on 0==open_cnt so only start one */
	if (test_and_clear_bit(SG_FDEV_EXCLUDE, sdp->fdev_bm))
		wake_up_interruptible_all(&sdp->open_wait);
	else if (atomic_read(&sdp->open_cnt) == 0)
		wake_up_interruptible(&sdp->open_wait);
	mutex_unlock(&sdp->open_rel_lock);
	return 0;
}

static ssize_t
sg_write(struct file *filp, const char __user *p, size_t count, loff_t *ppos)
{
	bool blocking = !(filp->f_flags & O_NONBLOCK);
	int mxsize, cmd_size, input_size, res;
	u8 opcode;
	struct sg_device *sdp;
	struct sg_fd *sfp;
	struct sg_request *srp;
	struct sg_header ov2hdr;
	struct sg_io_hdr v3hdr;
	struct sg_header *ohp = &ov2hdr;
	struct sg_io_hdr *h3p = &v3hdr;
	struct sg_comm_wr_t cwr;
	u8 cmnd[SG_MAX_CDB_SIZE];

	res = sg_check_file_access(filp, __func__);
	if (res)
		return res;

	sfp = filp->private_data;
	sdp = sfp->parentdp;
	SG_LOG(3, sfp, "%s: write(3rd arg) count=%d\n", __func__, (int)count);
	res = sg_allow_if_err_recovery(sdp, !!(filp->f_flags & O_NONBLOCK));
	if (res)
		return res;

	if (count < SZ_SG_HEADER)
		return -EIO;
	if (copy_from_user(ohp, p, SZ_SG_HEADER))
		return -EFAULT;
	if (ohp->reply_len < 0) {	/* assume this is v3 */
		struct sg_io_hdr *reinter_2p = (struct sg_io_hdr *)ohp;

		if (count < SZ_SG_IO_HDR)
			return -EIO;
		if (reinter_2p->interface_id != 'S') {
			pr_info_once("sg: %s: v3 interface only here\n",
				     __func__);
			return -EPERM;
		}
		return sg_submit(sfp, filp, p, count,
				 !(filp->f_flags & O_NONBLOCK), false, false,
				 NULL);
	}
	if (count < (SZ_SG_HEADER + 6))
		return -EIO;	/* The minimum scsi command length is 6 bytes. */

	p += SZ_SG_HEADER;
	if (get_user(opcode, p))
		return -EFAULT;

	if (!(srp = sg_setup_req(sfp))) {
		SG_LOG(1, sfp, "%s: queue full\n", __func__);
		return -EDOM;
	}
	mutex_lock(&sfp->f_mutex);
	if (sfp->next_cmd_len > 0) {
		cmd_size = sfp->next_cmd_len;
		sfp->next_cmd_len = 0;	/* reset so only this write() effected */
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
	if (input_size < 0) {
		sg_remove_request(sfp, srp);
		return -EIO;	/* User did not pass enough bytes for this command. */
	}
	h3p = &srp->header;
	h3p->interface_id = '\0';  /* indicator of old interface tunnelled */
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
		h3p->dxferp = (char __user *)p + cmd_size;
	else
		h3p->dxferp = NULL;
	h3p->sbp = NULL;
	h3p->timeout = ohp->reply_len;	/* structure abuse ... */
	h3p->flags = input_size;	/* structure abuse ... */
	h3p->pack_id = ohp->pack_id;
	h3p->usr_ptr = NULL;
	if (copy_from_user(cmnd, p, cmd_size)) {
		sg_remove_request(sfp, srp);
		return -EFAULT;
	}
	/*
	 * SG_DXFER_TO_FROM_DEV is functionally equivalent to SG_DXFER_FROM_DEV,
	 * but is is possible that the app intended SG_DXFER_TO_DEV, because there
	 * is a non-zero input_size, so emit a warning.
	 */
	if (h3p->dxfer_direction == SG_DXFER_TO_FROM_DEV) {
		printk_ratelimited(KERN_WARNING
				   "sg_write: data in/out %d/%d bytes "
				   "for SCSI command 0x%x-- guessing "
				   "data in;\n   program %s not setting "
				   "count and/or reply_len properly\n",
				   ohp->reply_len - (int)SZ_SG_HEADER,
				   input_size, (unsigned int) cmnd[0],
				   current->comm);
	}
	cwr.timeout = sfp->timeout;
	cwr.blocking = blocking;
	cwr.srp = srp;
	cwr.cmnd = cmnd;
	res = sg_common_write(sfp, &cwr);
	return (res < 0) ? res : count;
}

static int
sg_allow_access(struct file *filp, u8 *cmd)
{
	struct sg_fd *sfp = filp->private_data;

	if (sfp->parentdp->device->type == TYPE_SCANNER)
		return 0;

	return blk_verify_command(cmd, filp->f_mode);
}

static ssize_t
sg_submit(struct sg_fd *sfp, struct file *filp, const char __user *buf,
	  size_t count, bool blocking, bool read_only, bool sg_io_owned,
	  struct sg_request **o_srp)
{
	int k;
	struct sg_request *srp;
	struct sg_io_hdr *hp;
	struct sg_comm_wr_t cwr;
	u8 cmnd[SG_MAX_CDB_SIZE];
	int timeout;
	unsigned long ul_timeout;

	if (count < SZ_SG_IO_HDR)
		return -EINVAL;

	sfp->cmd_q = 1;	/* when sg_io_hdr seen, set command queuing on */
	if (!(srp = sg_setup_req(sfp))) {
		SG_LOG(1, sfp, "%s: queue full\n", __func__);
		return -EDOM;
	}
	srp->sg_io_owned = sg_io_owned;
	hp = &srp->header;
	if (get_sg_io_hdr(hp, buf)) {
		sg_remove_request(sfp, srp);
		return -EFAULT;
	}
	if (hp->interface_id != 'S') {
		sg_remove_request(sfp, srp);
		return -ENOSYS;
	}
	if (hp->flags & SG_FLAG_MMAP_IO) {
		if (hp->dxfer_len > sfp->reserve.buflen) {
			sg_remove_request(sfp, srp);
			return -ENOMEM;	/* MMAP_IO size must fit in reserve buffer */
		}
		if (hp->flags & SG_FLAG_DIRECT_IO) {
			sg_remove_request(sfp, srp);
			return -EINVAL;	/* either MMAP_IO or DIRECT_IO (not both) */
		}
		if (sfp->res_in_use) {
			sg_remove_request(sfp, srp);
			return -EBUSY;	/* reserve buffer already being used */
		}
	}
	ul_timeout = msecs_to_jiffies(srp->header.timeout);
	timeout = (ul_timeout < INT_MAX) ? ul_timeout : INT_MAX;
	if ((!hp->cmdp) || (hp->cmd_len < 6) || (hp->cmd_len > sizeof (cmnd))) {
		sg_remove_request(sfp, srp);
		return -EMSGSIZE;
	}
	if (copy_from_user(cmnd, hp->cmdp, hp->cmd_len)) {
		sg_remove_request(sfp, srp);
		return -EFAULT;
	}
	if (read_only && sg_allow_access(filp, cmnd)) {
		sg_remove_request(sfp, srp);
		return -EPERM;
	}
	cwr.timeout = timeout;
	cwr.blocking = blocking;
	cwr.srp = srp;
	cwr.cmnd = cmnd;
	k = sg_common_write(sfp, &cwr);
	if (k < 0)
		return k;
	if (o_srp)
		*o_srp = cwr.srp;
	return count;
}

static int
sg_common_write(struct sg_fd *sfp, struct sg_comm_wr_t *cwrp)
{
	bool at_head;
	int k;
	struct sg_device *sdp = sfp->parentdp;
	struct sg_request *srp = cwrp->srp;
	struct sg_io_hdr *hp = &srp->header;

	srp->data.cmd_opcode = cwrp->cmnd[0];	/* hold opcode of command */
	hp->status = 0;
	hp->masked_status = 0;
	hp->msg_status = 0;
	hp->info = 0;
	hp->host_status = 0;
	hp->driver_status = 0;
	hp->resid = 0;
	SG_LOG(4, sfp, "%s:  opcode=0x%02x, cmd_sz=%d\n", __func__,
	       (int)cwrp->cmnd[0], hp->cmd_len);

	if (hp->dxfer_len >= SZ_256M) {
		sg_remove_request(sfp, srp);
		return -EINVAL;
	}

	k = sg_start_req(srp, cwrp->cmnd);
	if (k) {
		SG_LOG(1, sfp, "%s: start_req err=%d\n", __func__, k);
		sg_finish_scsi_blk_rq(srp);
		sg_remove_request(sfp, srp);
		return k;	/* probably out of space --> ENOMEM */
	}
	if (SG_IS_DETACHING(sdp)) {
		if (srp->bio) {
			scsi_req_free_cmd(scsi_req(srp->rq));
			blk_put_request(srp->rq);
			srp->rq = NULL;
		}

		sg_finish_scsi_blk_rq(srp);
		sg_remove_request(sfp, srp);
		return -ENODEV;
	}

	hp->duration = jiffies_to_msecs(jiffies);
	if (hp->interface_id != '\0' &&	/* v3 (or later) interface */
	    (SG_FLAG_Q_AT_TAIL & hp->flags))
		at_head = false;
	else
		at_head = true;

	if (!srp->sg_io_owned)
		atomic_inc(&sfp->submitted);
	srp->rq->timeout = cwrp->timeout;
	kref_get(&sfp->f_ref); /* sg_rq_end_io() does kref_put(). */
	blk_execute_rq_nowait(sdp->device->request_queue, sdp->disk,
			      srp->rq, at_head, sg_rq_end_io);
	return 0;
}

/*
 * read(2) related functions follow. They are shown after write(2) related
 * functions. Apart from read(2) itself, ioctl(SG_IORECEIVE) and the second
 * half of the ioctl(SG_IO) share code with read(2).
 */

static struct sg_request *
sg_get_rq_mark(struct sg_fd *sfp, int pack_id)
{
	struct sg_request *resp;
	unsigned long iflags;

	spin_lock_irqsave(&sfp->rq_list_lock, iflags);
	list_for_each_entry(resp, &sfp->rq_list, entry) {
		/* look for requests that are ready + not SG_IO owned */
		if (resp->done == 1 && !resp->sg_io_owned &&
		    (-1 == pack_id || resp->header.pack_id == pack_id)) {
			resp->done = 2;	/* guard against other readers */
			spin_unlock_irqrestore(&sfp->rq_list_lock, iflags);
			return resp;
		}
	}
	spin_unlock_irqrestore(&sfp->rq_list_lock, iflags);
	return NULL;
}

static ssize_t
sg_receive_v3(struct sg_fd *sfp, char __user *buf, size_t count,
	      struct sg_request *srp)
{
	struct sg_io_hdr *hp = &srp->header;
	int err = 0, err2;
	int len;

	if (in_compat_syscall()) {
		if (count < sizeof(struct compat_sg_io_hdr)) {
			err = -EINVAL;
			goto err_out;
		}
	} else if (count < SZ_SG_IO_HDR) {
		err = -EINVAL;
		goto err_out;
	}
	hp->sb_len_wr = 0;
	if (hp->mx_sb_len > 0 && hp->sbp) {
		if ((CHECK_CONDITION & hp->masked_status) ||
		    (DRIVER_SENSE & hp->driver_status)) {
			int sb_len = SCSI_SENSE_BUFFERSIZE;

			sb_len = (hp->mx_sb_len > sb_len) ? sb_len :
							    hp->mx_sb_len;
			/* Additional sense length field */
			len = 8 + (int)srp->sense_b[7];
			len = (len > sb_len) ? sb_len : len;
			if (copy_to_user(hp->sbp, srp->sense_b, len)) {
				err = -EFAULT;
				goto err_out;
			}
			hp->sb_len_wr = len;
		}
	}
	if (hp->masked_status || hp->host_status || hp->driver_status)
		hp->info |= SG_INFO_CHECK;
	err = put_sg_io_hdr(hp, buf);
err_out:
	err2 = sg_finish_scsi_blk_rq(srp);
	sg_remove_request(sfp, srp);
	return err ? : err2 ? : count;
}

static int
srp_done(struct sg_fd *sfp, struct sg_request *srp)
{
	unsigned long flags;
	int ret;

	spin_lock_irqsave(&sfp->rq_list_lock, flags);
	ret = srp->done;
	spin_unlock_irqrestore(&sfp->rq_list_lock, flags);
	return ret;
}

static int
sg_read_v1v2(void __user *buf, int count, struct sg_fd *sfp,
	     struct sg_request *srp)
{
	int res = 0;
	struct sg_io_hdr *sh3p = &srp->header;
	struct sg_header *h2p;
	struct sg_header a_v2hdr;

	h2p = &a_v2hdr;
	memset(h2p, 0, SZ_SG_HEADER);
	h2p->reply_len = (int)sh3p->timeout;
	h2p->pack_len = h2p->reply_len; /* old, strange behaviour */
	h2p->pack_id = sh3p->pack_id;
	h2p->twelve_byte = (srp->data.cmd_opcode >= 0xc0 &&
			    sh3p->cmd_len == 12);
	h2p->target_status = sh3p->masked_status;
	h2p->host_status = sh3p->host_status;
	h2p->driver_status = sh3p->driver_status;
	if ((CHECK_CONDITION & h2p->target_status) ||
	    (DRIVER_SENSE & sh3p->driver_status)) {
		memcpy(h2p->sense_buffer, srp->sense_b,
		       sizeof(h2p->sense_buffer));
	}
	switch (h2p->host_status) {
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
		h2p->result = (h2p->target_status == GOOD) ? 0 : EIO;
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
	sg_finish_scsi_blk_rq(srp);
	sg_remove_request(sfp, srp);
	return res;
}

static ssize_t
sg_read(struct file *filp, char __user *p, size_t count, loff_t *ppos)
{
	bool could_be_v3;
	bool non_block = !!(filp->f_flags & O_NONBLOCK);
	int want_id = -1;
	int hlen, ret;
	struct sg_device *sdp;
	struct sg_fd *sfp;
	struct sg_request *srp;
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
	ret = sg_allow_if_err_recovery(sdp, false);
	if (ret)
		return ret;

	could_be_v3 = (count >= SZ_SG_IO_HDR);
	hlen = could_be_v3 ? SZ_SG_IO_HDR : SZ_SG_HEADER;
	h2p = (struct sg_header *)&a_sg_io_hdr;

	if (sfp->force_packid && count >= hlen) {
		/*
		 * Even though this is a user space read() system call, this
		 * code is cheating to fetch the pack_id.
		 * Only need first three 32 bit ints to determine interface.
		 */
		if (unlikely(copy_from_user(h2p, p, 3 * sizeof(int))))
			return -EFAULT;
		if (h2p->reply_len < 0 && could_be_v3) {
			struct sg_io_hdr *v3_hdr = (struct sg_io_hdr *)h2p;

			if (likely(v3_hdr->interface_id == 'S')) {
				struct sg_io_hdr __user *h3_up;

				h3_up = (struct sg_io_hdr __user *)p;
				ret = get_user(want_id, &h3_up->pack_id);
				if (unlikely(ret))
					return ret;
			} else if (v3_hdr->interface_id == 'Q') {
				pr_info_once("sg: %s: v4 interface%s here\n",
					     __func__, " disallowed");
				return -EPERM;
			} else {
				return -EPERM;
			}
		} else { /* for v1+v2 interfaces, this is the 3rd integer */
			want_id = h2p->pack_id;
		}
	}
	srp = sg_get_rq_mark(sfp, want_id);
	if (!srp) {		/* now wait on packet to arrive */
		if (SG_IS_DETACHING(sdp))
			return -ENODEV;
		if (non_block) /* O_NONBLOCK or v3::flags & SGV4_FLAG_IMMED */
			return -EAGAIN;
		ret = wait_event_interruptible
				(sfp->read_wait,
				 (SG_IS_DETACHING(sdp) ||
				  (srp = sg_get_rq_mark(sfp, want_id))));
		if (SG_IS_DETACHING(sdp))
			return -ENODEV;
		if (ret)	/* -ERESTARTSYS as signal hit process */
			return ret;
	}
	if (srp->header.interface_id == '\0')
		ret = sg_read_v1v2(p, (int)count, sfp, srp);
	else
		ret = sg_receive_v3(sfp, p, count, srp);
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

static void
sg_fill_request_table(struct sg_fd *sfp, struct sg_req_info *rinfo)
{
	struct sg_request *srp;
	int val;
	unsigned int ms;

	val = 0;
	list_for_each_entry(srp, &sfp->rq_list, entry) {
		if (val >= SG_MAX_QUEUE)
			break;
		rinfo[val].req_state = srp->done + 1;
		rinfo[val].problem =
			srp->header.masked_status &
			srp->header.host_status &
			srp->header.driver_status;
		if (srp->done)
			rinfo[val].duration =
				srp->header.duration;
		else {
			ms = jiffies_to_msecs(jiffies);
			rinfo[val].duration =
				(ms > srp->header.duration) ?
				(ms - srp->header.duration) : 0;
		}
		rinfo[val].orphan = srp->orphan;
		rinfo[val].sg_io_owned = srp->sg_io_owned;
		rinfo[val].pack_id = srp->header.pack_id;
		rinfo[val].usr_ptr = srp->header.usr_ptr;
		val++;
	}
}

/*
 * Handles ioctl(SG_IO) for blocking (sync) usage of v3 or v4 interface.
 * Returns 0 on success else a negated errno.
 */
static int
sg_ctl_sg_io(struct file *filp, struct sg_device *sdp, struct sg_fd *sfp,
	     void __user *p)
{
	bool read_only = O_RDWR != (filp->f_flags & O_ACCMODE);
	int res;
	struct sg_request *srp;

	res = sg_allow_if_err_recovery(sdp, false);
	if (res)
		return res;
	res = sg_submit(sfp, filp, p, SZ_SG_IO_HDR, true, read_only,
			true, &srp);
	if (res < 0)
		return res;
	res = wait_event_interruptible
		(sfp->read_wait, (srp_done(sfp, srp) || SG_IS_DETACHING(sdp)));
	if (SG_IS_DETACHING(sdp))
		return -ENODEV;
	spin_lock_irq(&sfp->rq_list_lock);
	if (srp->done) {
		srp->done = 2;
		spin_unlock_irq(&sfp->rq_list_lock);
		res = sg_receive_v3(sfp, p, SZ_SG_IO_HDR, srp);
		return (res < 0) ? res : 0;
	}
	srp->orphan = 1;
	spin_unlock_irq(&sfp->rq_list_lock);
	return res;	/* -ERESTARTSYS because signal hit process */
}

static int
sg_set_reserved_sz(struct sg_fd *sfp, int want_rsv_sz)
{
	if (want_rsv_sz != sfp->reserve.buflen) {
		if (sfp->mmap_called ||
		    sfp->res_in_use) {
			return -EBUSY;
		}

		sg_remove_scat(sfp, &sfp->reserve);
		sg_build_reserve(sfp, want_rsv_sz);
	}
	return 0;
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

static int
sg_ctl_req_tbl(struct sg_fd *sfp, void __user *p)
{
	int result;
	unsigned long iflags;
	sg_req_info_t *rinfo;

	rinfo = kcalloc(SG_MAX_QUEUE, SZ_SG_REQ_INFO,
			GFP_KERNEL);
	if (!rinfo)
		return -ENOMEM;
	spin_lock_irqsave(&sfp->rq_list_lock, iflags);
	sg_fill_request_table(sfp, rinfo);
	spin_unlock_irqrestore(&sfp->rq_list_lock, iflags);
#ifdef CONFIG_COMPAT
	if (in_compat_syscall())
		result = put_compat_request_table(p, rinfo);
	else
		result = copy_to_user(p, rinfo,
				      SZ_SG_REQ_INFO * SG_MAX_QUEUE);
#else
	result = copy_to_user(p, rinfo,
			      SZ_SG_REQ_INFO * SG_MAX_QUEUE);
#endif
	kfree(rinfo);
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
	unsigned long iflags;
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
		sfp->force_packid = val ? 1 : 0;
		return 0;
	case SG_GET_PACK_ID:
		val = -1;
		spin_lock_irqsave(&sfp->rq_list_lock, iflags);
		list_for_each_entry(srp, &sfp->rq_list, entry) {
			if ((1 == srp->done) && (!srp->sg_io_owned)) {
				val = srp->header.pack_id;
				break;
			}
		}
		spin_unlock_irqrestore(&sfp->rq_list_lock, iflags);
		SG_LOG(3, sfp, "%s:    SG_GET_PACK_ID=%d\n", __func__, val);
		return put_user(val, ip);
	case SG_GET_NUM_WAITING:
		return put_user(atomic_read(&sfp->waiting), ip);
	case SG_GET_SG_TABLESIZE:
		SG_LOG(3, sfp, "%s:    SG_GET_SG_TABLESIZE=%d\n", __func__,
		       sdp->max_sgat_sz);
		return put_user(sdp->max_sgat_sz, ip);
	case SG_SET_RESERVED_SIZE:
		mutex_lock(&sfp->f_mutex);
		result = get_user(val, ip);
		if (!result) {
			if (val >= 0 && val <= (1024 * 1024 * 1024)) {
				result = sg_set_reserved_sz(sfp, val);
			} else {
				SG_LOG(3, sfp, "%s: invalid size\n", __func__);
				result = -EINVAL;
			}
		}
		mutex_unlock(&sfp->f_mutex);
		return result;
	case SG_GET_RESERVED_SIZE:
		val = min_t(int, sfp->reserve.buflen,
			    max_sectors_bytes(sdev->request_queue));
		SG_LOG(3, sfp, "%s:    SG_GET_RESERVED_SIZE=%d\n",
		       __func__, val);
		return put_user(val, ip);
	case SG_SET_COMMAND_Q:
		SG_LOG(3, sfp, "%s:    SG_SET_COMMAND_Q\n", __func__);
		result = get_user(val, ip);
		if (result)
			return result;
		sfp->cmd_q = val ? 1 : 0;
		return 0;
	case SG_GET_COMMAND_Q:
		SG_LOG(3, sfp, "%s:    SG_GET_COMMAND_Q\n", __func__);
		return put_user((int) sfp->cmd_q, ip);
	case SG_SET_KEEP_ORPHAN:
		SG_LOG(3, sfp, "%s:    SG_SET_KEEP_ORPHAN\n", __func__);
		result = get_user(val, ip);
		if (result)
			return result;
		sfp->keep_orphan = val;
		return 0;
	case SG_GET_KEEP_ORPHAN:
		SG_LOG(3, sfp, "%s:    SG_GET_KEEP_ORPHAN\n", __func__);
		return put_user((int) sfp->keep_orphan, ip);
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
	case SG_NEXT_CMD_LEN:
		SG_LOG(3, sfp, "%s:    SG_NEXT_CMD_LEN\n", __func__);
		result = get_user(val, ip);
		if (result)
			return result;
		if (val > SG_MAX_CDB_SIZE)
			return -ENOMEM;
		sfp->next_cmd_len = (val > 0) ? val : 0;
		return 0;
	case SG_GET_ACCESS_COUNT:
		SG_LOG(3, sfp, "%s:    SG_GET_ACCESS_COUNT\n", __func__);
		/* faked - we don't have a real access count anymore */
		val = (sdev ? 1 : 0);
		return put_user(val, ip);
	case SG_EMULATED_HOST:
		SG_LOG(3, sfp, "%s:    SG_EMULATED_HOST\n", __func__);
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
		assign_bit(SG_FDEV_LOG_SENSE, sdp->fdev_bm, val);
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
	if (result)
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
	else if (likely(sfp->cmd_q))
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

static vm_fault_t
sg_vma_fault(struct vm_fault *vmf)
{
	struct vm_area_struct *vma = vmf->vma;
	struct sg_fd *sfp;
	unsigned long offset, len, sa;
	struct sg_scatter_hold *rsv_schp;
	int k, length;
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
	rsv_schp = &sfp->reserve;
	offset = vmf->pgoff << PAGE_SHIFT;
	if (offset >= rsv_schp->buflen)
		return VM_FAULT_SIGBUS;
	sa = vma->vm_start;
	SG_LOG(3, sfp, "%s: vm_start=0x%lx, off=%lu\n", __func__, sa, offset);
	length = 1 << (PAGE_SHIFT + rsv_schp->page_order);
	for (k = 0; k < rsv_schp->num_sgat && sa < vma->vm_end; k++) {
		len = vma->vm_end - sa;
		len = (len < length) ? len : length;
		if (offset < len) {
			struct page *page = nth_page(rsv_schp->pages[k],
						     offset >> PAGE_SHIFT);
			get_page(page);	/* increment page count */
			vmf->page = page;
			return 0; /* success */
		}
		sa += len;
		offset -= len;
	}
out_err:
	return VM_FAULT_SIGBUS;
}

static const struct vm_operations_struct sg_mmap_vm_ops = {
	.fault = sg_vma_fault,
};

static int
sg_mmap(struct file *filp, struct vm_area_struct *vma)
{
	struct sg_fd *sfp;
	unsigned long req_sz, len, sa;
	struct sg_scatter_hold *rsv_schp;
	int k, length;
	int ret = 0;

	if (!filp || !vma)
		return -ENXIO;
	sfp = filp->private_data;
	if (!sfp) {
		pr_warn("sg: %s: sfp is NULL\n", __func__);
		return -ENXIO;
	}
	req_sz = vma->vm_end - vma->vm_start;
	SG_LOG(3, sfp, "%s: vm_start=%p, len=%d\n", __func__,
	       (void *)vma->vm_start, (int)req_sz);
	if (vma->vm_pgoff)
		return -EINVAL;	/* want no offset */
	rsv_schp = &sfp->reserve;
	mutex_lock(&sfp->f_mutex);
	if (req_sz > rsv_schp->buflen) {
		ret = -ENOMEM;	/* cannot map more than reserved buffer */
		goto out;
	}

	sa = vma->vm_start;
	length = 1 << (PAGE_SHIFT + rsv_schp->page_order);
	for (k = 0; k < rsv_schp->num_sgat && sa < vma->vm_end; k++) {
		len = vma->vm_end - sa;
		len = (len < length) ? len : length;
		sa += len;
	}

	sfp->mmap_called = 1;
	vma->vm_flags |= VM_IO | VM_DONTEXPAND | VM_DONTDUMP;
	vma->vm_private_data = sfp;
	vma->vm_ops = &sg_mmap_vm_ops;
out:
	mutex_unlock(&sfp->f_mutex);
	return ret;
}

static void
sg_rq_end_io_usercontext(struct work_struct *work)
{
	struct sg_request *srp = container_of(work, struct sg_request,
					      ew_orph.work);
	struct sg_fd *sfp = srp->parentfp;

	sg_finish_scsi_blk_rq(srp);
	sg_remove_request(sfp, srp);
	kref_put(&sfp->f_ref, sg_remove_sfp);
}

/*
 * This function is a "bottom half" handler that is called by the mid
 * level when a command is completed (or has failed).
 */
static void
sg_rq_end_io(struct request *rq, blk_status_t status)
{
	struct sg_request *srp = rq->end_io_data;
	struct scsi_request *req = scsi_req(rq);
	struct sg_device *sdp;
	struct sg_fd *sfp;
	unsigned long iflags;
	unsigned int ms;
	char *sense;
	int result, resid, done = 1;

	if (WARN_ON(srp->done != 0))
		return;

	sfp = srp->parentfp;
	if (WARN_ON(sfp == NULL))
		return;

	sdp = sfp->parentdp;
	if (unlikely(SG_IS_DETACHING(sdp)))
		pr_info("%s: device detaching\n", __func__);

	sense = req->sense;
	result = req->result;
	resid = req->resid_len;

	srp->header.resid = resid;
	SG_LOG(6, sfp, "%s: pack_id=%d, res=0x%x\n", __func__,
	       srp->header.pack_id, result);
	ms = jiffies_to_msecs(jiffies);
	srp->header.duration = (ms > srp->header.duration) ?
				(ms - srp->header.duration) : 0;
	if (0 != result) {
		struct scsi_sense_hdr sshdr;

		srp->header.status = 0xff & result;
		srp->header.masked_status = status_byte(result);
		srp->header.msg_status = msg_byte(result);
		srp->header.host_status = host_byte(result);
		srp->header.driver_status = driver_byte(result);
		if (test_bit(SG_FDEV_LOG_SENSE, sdp->fdev_bm) &&
		    (srp->header.masked_status == CHECK_CONDITION ||
		     srp->header.masked_status == COMMAND_TERMINATED))
			__scsi_print_sense(sdp->device, __func__, sense,
					   SCSI_SENSE_BUFFERSIZE);

		/* Following if statement is a patch supplied by Eric Youngdale */
		if (driver_byte(result) != 0
		    && scsi_normalize_sense(sense, SCSI_SENSE_BUFFERSIZE, &sshdr)
		    && !scsi_sense_is_deferred(&sshdr)
		    && sshdr.sense_key == UNIT_ATTENTION
		    && sdp->device->removable) {
			/* Detected possible disc change. Set the bit - this */
			/* may be used if there are filesystems using this device */
			sdp->device->changed = 1;
		}
	}

	if (req->sense_len)
		memcpy(srp->sense_b, req->sense, SCSI_SENSE_BUFFERSIZE);

	/* Rely on write phase to clean out srp status values, so no "else" */

	if (!srp->sg_io_owned)
		atomic_inc(&sfp->waiting);
	/*
	 * Free the request as soon as it is complete so that its resources
	 * can be reused without waiting for userspace to read() the
	 * result.  But keep the associated bio (if any) around until
	 * blk_rq_unmap_user() can be called from user context.
	 */
	srp->rq = NULL;
	scsi_req_free_cmd(scsi_req(rq));
	blk_put_request(rq);

	spin_lock_irqsave(&sfp->rq_list_lock, iflags);
	if (unlikely(srp->orphan)) {
		if (sfp->keep_orphan)
			srp->sg_io_owned = 0;
		else
			done = 0;
	}
	srp->done = done;
	spin_unlock_irqrestore(&sfp->rq_list_lock, iflags);

	if (likely(done)) {
		/* Now wake up any sg_read() that is waiting for this
		 * packet.
		 */
		wake_up_interruptible(&sfp->read_wait);
		kill_fasync(&sfp->async_qp, SIGPOLL, POLL_IN);
		kref_put(&sfp->f_ref, sg_remove_sfp);
	} else {
		INIT_WORK(&srp->ew_orph.work, sg_rq_end_io_usercontext);
		schedule_work(&srp->ew_orph.work);
	}
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

static int sg_sysfs_valid = 0;

static struct sg_device *
sg_add_device_helper(struct gendisk *disk, struct scsi_device *scsidp)
{
	struct request_queue *q = scsidp->request_queue;
	struct sg_device *sdp;
	unsigned long iflags;
	int error;
	u32 k;

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
				    "%s: idr alloc sg_device failure: %d\n",
				    __func__, error);
		}
		goto out_unlock;
	}
	k = error;

	SCSI_LOG_TIMEOUT(3, sdev_printk(KERN_INFO, scsidp,
			 "%s: dev=%d, sdp=0x%p ++\n", __func__, k, sdp));
	sprintf(disk->disk_name, "sg%d", k);
	disk->first_minor = k;
	sdp->disk = disk;
	sdp->device = scsidp;
	mutex_init(&sdp->open_rel_lock);
	INIT_LIST_HEAD(&sdp->sfds);
	init_waitqueue_head(&sdp->open_wait);
	clear_bit(SG_FDEV_DETACHING, sdp->fdev_bm);
	rwlock_init(&sdp->sfd_lock);
	sdp->max_sgat_sz = queue_max_segments(q);
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

	SCSI_LOG_TIMEOUT(1, pr_info("[tid=%d] %s: sdp idx=%d, sdp=0x%p --\n",
				    (current ? current->pid : -1), __func__,
				    sdp->index, sdp));
	/*
	 * CAUTION!  Note that the device can still be found via idr_find()
	 * even though the refcount is 0.  Therefore, do idr_remove() BEFORE
	 * any other cleanup.
	 */

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
	unsigned long iflags;
	struct sg_fd *sfp;

	if (!sdp)
		return;
	/* set this flag as soon as possible as it could be a surprise */
	if (test_and_set_bit(SG_FDEV_DETACHING, sdp->fdev_bm))
		return; /* only want to do following once per device */

	SCSI_LOG_TIMEOUT(3, sdev_printk(KERN_INFO, sdp->device,
					"%s: 0x%p\n", __func__, sdp));

	read_lock_irqsave(&sdp->sfd_lock, iflags);
	list_for_each_entry(sfp, &sdp->sfds, sfd_entry) {
		wake_up_interruptible_all(&sfp->read_wait);
		kill_fasync(&sfp->async_qp, SIGPOLL, POLL_HUP);
	}
	wake_up_interruptible_all(&sdp->open_wait);
	read_unlock_irqrestore(&sdp->sfd_lock, iflags);

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

	if (scatter_elem_sz < PAGE_SIZE) {
		scatter_elem_sz = PAGE_SIZE;
		scatter_elem_sz_prev = scatter_elem_sz;
	}
	if (def_reserved_size >= 0)
		sg_big_buff = def_reserved_size;
	else
		def_reserved_size = sg_big_buff;

	rc = register_chrdev_region(MKDEV(SCSI_GENERIC_MAJOR, 0), 
				    SG_MAX_DEVS, "sg");
	if (rc)
		return rc;
        sg_sysfs_class = class_create(THIS_MODULE, "scsi_generic");
        if ( IS_ERR(sg_sysfs_class) ) {
		rc = PTR_ERR(sg_sysfs_class);
		goto err_out;
        }
	sg_sysfs_valid = 1;
	rc = scsi_register_interface(&sg_interface);
	if (0 == rc) {
		sg_proc_init();
		return 0;
	}
	class_destroy(sg_sysfs_class);
err_out:
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
	sg_sysfs_valid = 0;
	unregister_chrdev_region(MKDEV(SCSI_GENERIC_MAJOR, 0),
				 SG_MAX_DEVS);
	idr_destroy(&sg_index_idr);
}

static int
sg_start_req(struct sg_request *srp, u8 *cmd)
{
	int res;
	struct request *rq;
	struct scsi_request *req;
	struct sg_fd *sfp = srp->parentfp;
	struct sg_io_hdr *hp = &srp->header;
	int dxfer_len = (int) hp->dxfer_len;
	int dxfer_dir = hp->dxfer_direction;
	unsigned int iov_count = hp->iovec_count;
	struct sg_scatter_hold *req_schp = &srp->data;
	struct sg_scatter_hold *rsv_schp = &sfp->reserve;
	struct request_queue *q = sfp->parentdp->device->request_queue;
	struct rq_map_data *md, map_data;
	int r0w = hp->dxfer_direction == SG_DXFER_TO_DEV ? WRITE : READ;
	u8 *long_cmdp = NULL;

	if (hp->cmd_len > BLK_MAX_CDB) {
		long_cmdp = kzalloc(hp->cmd_len, GFP_KERNEL);
		if (!long_cmdp)
			return -ENOMEM;
		SG_LOG(5, sfp, "%s: long_cmdp=0x%p ++\n", __func__, long_cmdp);
	}
	SG_LOG(4, sfp, "%s: dxfer_len=%d, data-%s\n", __func__, dxfer_len,
	       (r0w ? "OUT" : "IN"));

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
	rq = blk_get_request(q, hp->dxfer_direction == SG_DXFER_TO_DEV ?
			REQ_OP_SCSI_OUT : REQ_OP_SCSI_IN, 0);
	if (IS_ERR(rq)) {
		kfree(long_cmdp);
		return PTR_ERR(rq);
	}
	req = scsi_req(rq);

	if (hp->cmd_len > BLK_MAX_CDB)
		req->cmd = long_cmdp;
	memcpy(req->cmd, cmd, hp->cmd_len);
	req->cmd_len = hp->cmd_len;

	srp->rq = rq;
	rq->end_io_data = srp;
	req->retries = SG_DEFAULT_RETRIES;

	if ((dxfer_len <= 0) || (dxfer_dir == SG_DXFER_NONE))
		return 0;

	if (sg_allow_dio && hp->flags & SG_FLAG_DIRECT_IO &&
	    dxfer_dir != SG_DXFER_UNKNOWN && !iov_count &&
	    !sfp->parentdp->device->host->unchecked_isa_dma &&
	    blk_rq_aligned(q, (unsigned long)hp->dxferp, dxfer_len))
		md = NULL;
	else
		md = &map_data;

	if (md) {
		mutex_lock(&sfp->f_mutex);
		if (dxfer_len <= rsv_schp->buflen &&
		    !sfp->res_in_use) {
			sfp->res_in_use = 1;
			sg_link_reserve(sfp, srp, dxfer_len);
		} else if (hp->flags & SG_FLAG_MMAP_IO) {
			res = -EBUSY; /* sfp->res_in_use == 1 */
			if (dxfer_len > rsv_schp->buflen)
				res = -ENOMEM;
			mutex_unlock(&sfp->f_mutex);
			return res;
		} else {
			res = sg_build_indirect(req_schp, sfp, dxfer_len);
			if (res) {
				mutex_unlock(&sfp->f_mutex);
				return res;
			}
		}
		mutex_unlock(&sfp->f_mutex);

		md->pages = req_schp->pages;
		md->page_order = req_schp->page_order;
		md->nr_entries = req_schp->num_sgat;
		md->offset = 0;
		md->null_mapped = hp->dxferp ? 0 : 1;
		if (dxfer_dir == SG_DXFER_TO_FROM_DEV)
			md->from_user = 1;
		else
			md->from_user = 0;
	}

	if (iov_count) {
		struct iovec *iov = NULL;
		struct iov_iter i;

		res = import_iovec(rw, hp->dxferp, iov_count, 0, &iov, &i);
		if (res < 0)
			return res;

		iov_iter_truncate(&i, hp->dxfer_len);
		if (!iov_iter_count(&i)) {
			kfree(iov);
			return -EINVAL;
		}

		res = blk_rq_map_user_iov(q, rq, md, &i, GFP_ATOMIC);
		kfree(iov);
	} else
		res = blk_rq_map_user(q, rq, md, hp->dxferp,
				      hp->dxfer_len, GFP_ATOMIC);

	if (!res) {
		srp->bio = rq->bio;

		if (!md) {
			req_schp->dio_in_use = 1;
			hp->info |= SG_INFO_DIRECT_IO;
		}
	}
	return res;
}

static int
sg_finish_scsi_blk_rq(struct sg_request *srp)
{
	int ret = 0;

	struct sg_fd *sfp = srp->parentfp;
	struct sg_scatter_hold *req_schp = &srp->data;

	SG_LOG(4, sfp, "%s: srp=0x%p%s\n", __func__, srp,
	       (srp->res_used) ? " rsv" : "");
	if (!srp->sg_io_owned) {
		atomic_dec(&sfp->submitted);
		atomic_dec(&sfp->waiting);
	}
	if (srp->bio)
		ret = blk_rq_unmap_user(srp->bio);

	if (srp->rq) {
		scsi_req_free_cmd(scsi_req(srp->rq));
		blk_put_request(srp->rq);
	}

	if (srp->res_used)
		sg_unlink_reserve(sfp, srp);
	else
		sg_remove_scat(sfp, req_schp);

	return ret;
}

static int
sg_build_sgat(struct sg_scatter_hold *schp, const struct sg_fd *sfp,
	      int tablesize)
{
	int sg_buflen = tablesize * sizeof(struct page *);
	gfp_t gfp_flags = GFP_ATOMIC | __GFP_NOWARN;

	schp->pages = kzalloc(sg_buflen, gfp_flags);
	if (!schp->pages)
		return -ENOMEM;
	schp->sglist_len = sg_buflen;
	return tablesize;	/* number of scat_gath elements allocated */
}

static int
sg_build_indirect(struct sg_scatter_hold *schp, struct sg_fd *sfp,
		  int buff_size)
{
	int ret_sz = 0, i, k, rem_sz, num, mx_sc_elems;
	int max_sgat_sz = sfp->parentdp->max_sgat_sz;
	int blk_size = buff_size, order;
	gfp_t gfp_mask = GFP_ATOMIC | __GFP_COMP | __GFP_NOWARN | __GFP_ZERO;
	struct sg_device *sdp = sfp->parentdp;

	if (blk_size < 0)
		return -EFAULT;
	if (0 == blk_size)
		++blk_size;	/* don't know why */
	/* round request up to next highest SG_DEF_SECTOR_SZ byte boundary */
	blk_size = ALIGN(blk_size, SG_DEF_SECTOR_SZ);
	SG_LOG(4, sfp, "%s: buff_size=%d, blk_size=%d\n", __func__, buff_size,
	       blk_size);

	/* N.B. ret_sz carried into this block ... */
	mx_sc_elems = sg_build_sgat(schp, sfp, max_sgat_sz);
	if (mx_sc_elems < 0)
		return mx_sc_elems;	/* most likely -ENOMEM */

	num = scatter_elem_sz;
	if (unlikely(num != scatter_elem_sz_prev)) {
		if (num < PAGE_SIZE) {
			scatter_elem_sz = PAGE_SIZE;
			scatter_elem_sz_prev = PAGE_SIZE;
		} else
			scatter_elem_sz_prev = num;
	}

	if (sdp->device->host->unchecked_isa_dma)
		gfp_mask |= GFP_DMA;

	order = get_order(num);
retry:
	ret_sz = 1 << (PAGE_SHIFT + order);

	for (k = 0, rem_sz = blk_size; rem_sz > 0 && k < mx_sc_elems;
	     k++, rem_sz -= ret_sz) {

		num = (rem_sz > scatter_elem_sz_prev) ?
			scatter_elem_sz_prev : rem_sz;

		schp->pages[k] = alloc_pages(gfp_mask, order);
		if (!schp->pages[k])
			goto out;

		if (num == scatter_elem_sz_prev) {
			if (unlikely(ret_sz > scatter_elem_sz_prev)) {
				scatter_elem_sz = ret_sz;
				scatter_elem_sz_prev = ret_sz;
			}
		}
		SG_LOG(5, sfp, "%s: k=%d, num=%d, ret_sz=%d\n", __func__, k,
		       num, ret_sz);
	}		/* end of for loop */

	schp->page_order = order;
	schp->num_sgat = k;
	SG_LOG(5, sfp, "%s: num_sgat=%d, order=%d\n", __func__, k, order);
	schp->buflen = blk_size;
	if (rem_sz > 0)	/* must have failed */
		return -ENOMEM;
	return 0;
out:
	for (i = 0; i < k; i++)
		__free_pages(schp->pages[i], order);

	if (--order >= 0)
		goto retry;

	return -ENOMEM;
}

static void
sg_remove_scat(struct sg_fd *sfp, struct sg_scatter_hold *schp)
{
	SG_LOG(4, sfp, "%s: num_sgat=%d\n", __func__, schp->num_sgat);
	if (schp->pages && schp->sglist_len > 0) {
		if (!schp->dio_in_use) {
			int k;

			for (k = 0; k < schp->num_sgat && schp->pages[k]; k++) {
				SG_LOG(5, sfp, "%s: pg[%d]=0x%p --\n",
				       __func__, k, schp->pages[k]);
				__free_pages(schp->pages[k], schp->page_order);
			}
			kfree(schp->pages);
		}
	}
	memset(schp, 0, sizeof (*schp));
}

/*
 * For sg v1 and v2 interface: with a command yielding a data-in buffer, after
 * it has arrived in kernel memory, this function copies it to the user space,
 * appended to given struct sg_header object.
 */
static int
sg_read_append(struct sg_request *srp, void __user *outp, int num_xfer)
{
	struct sg_scatter_hold *schp = &srp->data;
	int k, num;

	SG_LOG(4, srp->parentfp, "%s: num_xfer=%d\n", __func__, num_xfer);
	if (!outp || num_xfer <= 0)
		return 0;

	num = 1 << (PAGE_SHIFT + schp->page_order);
	for (k = 0; k < schp->num_sgat && schp->pages[k]; k++) {
		if (num > num_xfer) {
			if (copy_to_user(outp, page_address(schp->pages[k]),
					   num_xfer))
				return -EFAULT;
			break;
		} else {
			if (copy_to_user(outp, page_address(schp->pages[k]),
					   num))
				return -EFAULT;
			num_xfer -= num;
			if (num_xfer <= 0)
				break;
			outp += num;
		}
	}
	return 0;
}

static void
sg_build_reserve(struct sg_fd *sfp, int req_size)
{
	struct sg_scatter_hold *schp = &sfp->reserve;

	SG_LOG(3, sfp, "%s: buflen=%d\n", __func__, req_size);
	do {
		if (req_size < PAGE_SIZE)
			req_size = PAGE_SIZE;
		if (0 == sg_build_indirect(schp, sfp, req_size))
			return;
		else
			sg_remove_scat(sfp, schp);
		req_size >>= 1;	/* divide by 2 */
	} while (req_size > (PAGE_SIZE / 2));
}

static void
sg_link_reserve(struct sg_fd *sfp, struct sg_request *srp, int size)
{
	struct sg_scatter_hold *req_schp = &srp->data;
	struct sg_scatter_hold *rsv_schp = &sfp->reserve;
	int k, num, rem;

	srp->res_used = 1;
	SG_LOG(4, sfp, "%s: size=%d\n", __func__, size);
	rem = size;

	num = 1 << (PAGE_SHIFT + rsv_schp->page_order);
	for (k = 0; k < rsv_schp->num_sgat; k++) {
		if (rem <= num) {
			req_schp->num_sgat = k + 1;
			req_schp->sglist_len = rsv_schp->sglist_len;
			req_schp->pages = rsv_schp->pages;

			req_schp->buflen = size;
			req_schp->page_order = rsv_schp->page_order;
			break;
		} else
			rem -= num;
	}

	if (k >= rsv_schp->num_sgat)
		SG_LOG(1, sfp, "%s: BAD size\n", __func__);
}

static void
sg_unlink_reserve(struct sg_fd *sfp, struct sg_request *srp)
{
	struct sg_scatter_hold *req_schp = &srp->data;

	SG_LOG(4, srp->parentfp, "%s: req->num_sgat=%d\n", __func__,
	       (int)req_schp->num_sgat);
	req_schp->num_sgat = 0;
	req_schp->buflen = 0;
	req_schp->pages = NULL;
	req_schp->page_order = 0;
	req_schp->sglist_len = 0;
	srp->res_used = 0;
	/* Called without mutex lock to avoid deadlock */
	sfp->res_in_use = 0;
}

/* always adds to end of list */
static struct sg_request *
sg_setup_req(struct sg_fd *sfp)
{
	int k;
	unsigned long iflags;
	struct sg_request *rp = sfp->req_arr;

	spin_lock_irqsave(&sfp->rq_list_lock, iflags);
	if (!list_empty(&sfp->rq_list)) {
		if (!sfp->cmd_q)
			goto out_unlock;

		for (k = 0; k < SG_MAX_QUEUE; ++k, ++rp) {
			if (!rp->parentfp)
				break;
		}
		if (k >= SG_MAX_QUEUE)
			goto out_unlock;
	}
	memset(rp, 0, sizeof(struct sg_request));
	rp->parentfp = sfp;
	rp->header.duration = jiffies_to_msecs(jiffies);
	list_add_tail(&rp->entry, &sfp->rq_list);
	spin_unlock_irqrestore(&sfp->rq_list_lock, iflags);
	return rp;
out_unlock:
	spin_unlock_irqrestore(&sfp->rq_list_lock, iflags);
	return NULL;
}

/* Return of 1 for found; 0 for not found */
static int
sg_remove_request(struct sg_fd *sfp, struct sg_request *srp)
{
	unsigned long iflags;
	int res = 0;

	if (!sfp || !srp || list_empty(&sfp->rq_list))
		return res;
	spin_lock_irqsave(&sfp->rq_list_lock, iflags);
	if (!list_empty(&srp->entry)) {
		list_del(&srp->entry);
		srp->parentfp = NULL;
		res = 1;
	}
	spin_unlock_irqrestore(&sfp->rq_list_lock, iflags);
	return res;
}

static struct sg_fd *
sg_add_sfp(struct sg_device *sdp)
{
	struct sg_fd *sfp;
	unsigned long iflags;
	int bufflen;

	sfp = kzalloc(sizeof(*sfp), GFP_ATOMIC | __GFP_NOWARN);
	if (!sfp)
		return ERR_PTR(-ENOMEM);

	init_waitqueue_head(&sfp->read_wait);
	spin_lock_init(&sfp->rq_list_lock);
	INIT_LIST_HEAD(&sfp->rq_list);
	kref_init(&sfp->f_ref);
	mutex_init(&sfp->f_mutex);
	sfp->timeout = SG_DEFAULT_TIMEOUT;
	sfp->timeout_user = SG_DEFAULT_TIMEOUT_USER;
	sfp->force_packid = SG_DEF_FORCE_PACK_ID;
	sfp->cmd_q = SG_DEF_COMMAND_Q;
	sfp->keep_orphan = SG_DEF_KEEP_ORPHAN;
	sfp->parentdp = sdp;
	atomic_set(&sfp->submitted, 0);
	atomic_set(&sfp->waiting, 0);

	write_lock_irqsave(&sdp->sfd_lock, iflags);
	if (SG_IS_DETACHING(sdp)) {
		write_unlock_irqrestore(&sdp->sfd_lock, iflags);
		kfree(sfp);
		return ERR_PTR(-ENODEV);
	}
	list_add_tail(&sfp->sfd_entry, &sdp->sfds);
	write_unlock_irqrestore(&sdp->sfd_lock, iflags);
	SG_LOG(3, sfp, "%s: sfp=0x%p\n", __func__, sfp);
	if (unlikely(sg_big_buff != def_reserved_size))
		sg_big_buff = def_reserved_size;

	bufflen = min_t(int, sg_big_buff,
			max_sectors_bytes(sdp->device->request_queue));
	sg_build_reserve(sfp, bufflen);
	SG_LOG(3, sfp, "%s: bufflen=%d, num_sgat=%d\n", __func__,
	       sfp->reserve.buflen, sfp->reserve.num_sgat);

	kref_get(&sdp->d_ref);
	__module_get(THIS_MODULE);
	return sfp;
}

static void
sg_remove_sfp_usercontext(struct work_struct *work)
{
	struct sg_fd *sfp = container_of(work, struct sg_fd, ew_fd.work);
	struct sg_device *sdp = sfp->parentdp;
	struct sg_request *srp;
	unsigned long iflags;

	/* Cleanup any responses which were never read(). */
	spin_lock_irqsave(&sfp->rq_list_lock, iflags);
	while (!list_empty(&sfp->rq_list)) {
		srp = list_first_entry(&sfp->rq_list, struct sg_request, entry);
		sg_finish_scsi_blk_rq(srp);
		list_del(&srp->entry);
		srp->parentfp = NULL;
	}
	spin_unlock_irqrestore(&sfp->rq_list_lock, iflags);

	if (sfp->reserve.buflen > 0) {
		SG_LOG(6, sfp, "%s:    buflen=%d, num_sgat=%d\n", __func__,
		       (int)sfp->reserve.buflen, (int)sfp->reserve.num_sgat);
		sg_remove_scat(sfp, &sfp->reserve);
	}

	SG_LOG(6, sfp, "%s: sfp=0x%p\n", __func__, sfp);
	kfree(sfp);

	scsi_device_put(sdp->device);
	kref_put(&sdp->d_ref, sg_device_destroy);
	module_put(THIS_MODULE);
}

static void
sg_remove_sfp(struct kref *kref)
{
	struct sg_fd *sfp = container_of(kref, struct sg_fd, f_ref);
	struct sg_device *sdp = sfp->parentdp;
	unsigned long iflags;

	write_lock_irqsave(&sdp->sfd_lock, iflags);
	list_del(&sfp->sfd_entry);
	write_unlock_irqrestore(&sdp->sfd_lock, iflags);

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
};

static void *
dev_seq_start(struct seq_file *s, loff_t *pos)
{
	struct sg_proc_deviter * it = kmalloc(sizeof(*it), GFP_KERNEL);

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
	int k, new_interface, blen, usg;
	struct sg_request *srp;
	struct sg_fd *fp;
	const struct sg_io_hdr *hp;
	const char * cp;
	unsigned int ms;

	k = 0;
	list_for_each_entry(fp, &sdp->sfds, sfd_entry) {
		k++;
		spin_lock(&fp->rq_list_lock); /* irqs already disabled */
		seq_printf(s, "   FD(%d): timeout=%dms buflen=%d "
			   "(res)sgat=%d low_dma=%d\n", k,
			   jiffies_to_msecs(fp->timeout),
			   fp->reserve.buflen,
			   (int)fp->reserve.num_sgat,
			   (int) sdp->device->host->unchecked_isa_dma);
		seq_printf(s, "   cmd_q=%d f_packid=%d k_orphan=%d closed=0\n",
			   (int) fp->cmd_q, (int) fp->force_packid,
			   (int) fp->keep_orphan);
		seq_printf(s, "   submitted=%d waiting=%d\n",
			   atomic_read(&fp->submitted),
			   atomic_read(&fp->waiting));
		list_for_each_entry(srp, &fp->rq_list, entry) {
			hp = &srp->header;
			new_interface = (hp->interface_id == '\0') ? 0 : 1;
			if (srp->res_used) {
				if (new_interface &&
				    (SG_FLAG_MMAP_IO & hp->flags))
					cp = "     mmap>> ";
				else
					cp = "     rb>> ";
			} else {
				if (SG_INFO_DIRECT_IO_MASK & hp->info)
					cp = "     dio>> ";
				else
					cp = "     ";
			}
			seq_puts(s, cp);
			blen = srp->data.buflen;
			usg = srp->data.num_sgat;
			seq_puts(s, srp->done ?
				 ((1 == srp->done) ?  "rcv:" : "fin:")
				  : "act:");
			seq_printf(s, " id=%d blen=%d",
				   srp->header.pack_id, blen);
			if (srp->done)
				seq_printf(s, " dur=%d", hp->duration);
			else {
				ms = jiffies_to_msecs(jiffies);
				seq_printf(s, " t_o/elap=%d/%d",
					(new_interface ? hp->timeout :
						  jiffies_to_msecs(fp->timeout)),
					(ms > hp->duration ? ms - hp->duration : 0));
			}
			seq_printf(s, "ms sgat=%d op=0x%02x\n", usg,
				   (int) srp->data.cmd_opcode);
		}
		if (list_empty(&fp->rq_list))
			seq_puts(s, "     No requests active\n");
		spin_unlock(&fp->rq_list_lock);
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
	read_lock(&sdp->sfd_lock);
	if (!list_empty(&sdp->sfds)) {
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
	read_unlock(&sdp->sfd_lock);
skip:
	read_unlock_irqrestore(&sg_index_lock, iflags);
	return 0;
}

#endif				/* CONFIG_SCSI_PROC_FS (~300 lines back) */

module_init(init_sg);
module_exit(exit_sg);

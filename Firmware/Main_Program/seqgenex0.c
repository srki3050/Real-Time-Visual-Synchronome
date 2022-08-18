/* Name         : Sricharan Kidambi
 * Brief        : Build a visual synchronome at 1HZ frequency and test it against an analog clock
 * Date         : 8th August 2022
 * file         : seqgenex0
 * References   : Attended Professor's Debug sessions to get an Idea of how tick detect works and how well you can differentiate the required frames to the unnecessary and motion blur frames
 *                Once the initial design is completed, I asked Abijith Ananda Krishnan on how to target stuff to cores so that your RMA is deasible and how well to time your circuit for analysis
 */
#define _GNU_SOURCE

#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>

#include <pthread.h>
#include <sched.h>
#include <time.h>
#include <semaphore.h>

#include <syslog.h>
#include <sys/time.h>
#include <errno.h>
#include "seqgen.h"
#include <sys/sysinfo.h>

#include <string.h>
#include <assert.h>
#include <fcntl.h>
#include <errno.h>
#include <syslog.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <sys/time.h>
#include <sys/mman.h>
#include <sys/ioctl.h>
#include <stdbool.h>

#include <linux/videodev2.h>

#include <time.h>

#define ABS_DELAY
#define DRIFT_CONTROL
// create 3 threads plus a main sequencer thread
#define NUM_THREADS (3+1)

int abortTest=FALSE;
// creating 3 abort variables and 3 semaphores
int abortS1=FALSE, abortS2=FALSE, abortS3=FALSE, abortS4=FALSE;
sem_t semS1, semS2, semS3, semS4;
static double start_time = 0;
// create thread array of 4 threads
pthread_t threads[NUM_THREADS];
// create schedule attributes for all the 4
pthread_attr_t rt_sched_attr[NUM_THREADS];
// create a main attribute
pthread_attr_t main_attr;
// set the maximum and minimimum priority with the help of the bhelow variables
int rt_max_prio, rt_min_prio;
// sched parameters
struct sched_param rt_param[NUM_THREADS];
// threadParams_t threadParams - 4 THREAD PARAMETERS
threadParams_t threadParams[NUM_THREADS];
bool can_dump = false;
/**************************************************************************Web cam process begin********************************************************/
#define CLEAR(x) memset(&(x), 0, sizeof(x))

#define HRES 640
#define VRES 480
#define HRES_STR "640"
#define VRES_STR "480"

#define START_UP_FRAMES (8)
#define LAST_FRAMES (1)
#define CAPTURE_FRAMES (1810+LAST_FRAMES)
#define FRAMES_TO_ACQUIRE (CAPTURE_FRAMES + START_UP_FRAMES + LAST_FRAMES)
 
#define FRAMES_PER_SEC (30)
// Format is used by a number of functions, so made as a file global
static struct v4l2_format fmt;

struct buffer 
{
        void   *start;
        size_t  length;
};

static char            *dev_name;  // pointer to store the device name
static int              fd = -1;
struct buffer          *buffers;
static unsigned int     n_buffers;
static int              out_buf;
static int              force_format=1;

static int              frame_count = (FRAMES_TO_ACQUIRE);

static double fnow=0.0, fstart=0.0, fstop=0.0;
static struct timespec time_now, time_start, time_stop;

static void errno_exit(const char *s)
{
  fprintf(stderr, "%s error %d, %s\n", s, errno, strerror(errno));
  exit(EXIT_FAILURE);
}

static int xioctl(int fh, int request, void *arg)
{
  int r;
  do 
   {
     r = ioctl(fh, request, arg);
   } while (-1 == r && EINTR == errno);
   return r;
}
struct timespec start_time_val,current_time_val;
char pgm_header[]="P5\n#9999999999 sec 9999999999 msec \n"HRES_STR" "VRES_STR"\n255\n";
char pgm_dumpname[]="frames/test0000.pgm";
//function call - dump_pgm(bigbuffer, frame_size, framecnt, &write_back_time);

unsigned long long seqCnt=0;
static void dump_pgm(const void *p, int size, unsigned int tag, struct timespec *time)
{
    int written, i, total, dumpfd;
   
    snprintf(&pgm_dumpname[11], 9, "%04d", tag);
    strncat(&pgm_dumpname[15], ".pgm", 5);
    dumpfd = open(pgm_dumpname, O_WRONLY | O_NONBLOCK | O_CREAT, 00666);

    snprintf(&pgm_header[4], 11, "%010d", (int)time->tv_sec);
    strncat(&pgm_header[14], " sec ", 5);
    snprintf(&pgm_header[19], 11, "%010d", (int)((time->tv_nsec)/1000000));
    strncat(&pgm_header[29], " msec \n"HRES_STR" "VRES_STR"\n255\n", 19);

    // subtract 1 from sizeof header because it includes the null terminator for the string
    written=write(dumpfd, pgm_header, sizeof(pgm_header)-1);

    total=0;

    do
    {
        written=write(dumpfd, p, size);
        total+=written;
    } while(total < size);

    clock_gettime(CLOCK_MONOTONIC, &time_now);
    fnow = (double)time_now.tv_sec + (double)time_now.tv_nsec / 1000000000.0;

    close(dumpfd);
}
// always ignore first 8 frames
int framecnt=-8;

int frame_size;
/********************************************************************************************************************Array and buffer declarations**************************************************************************************************************************************/
int position = 0;
unsigned char bigbuffer[(640 * 480)];
//unsigned char newbuffer[(640 * 480)] = {0};
//int diff_array[1800];

typedef struct store_frames{
    unsigned char big_buffer[(640 * 480)];
    int framesize;
    int framecount;
    bool tick;
    struct timespec write_back_time;
} frames_t;

frames_t dump_frames[2000],select_frame[200];  
/********************************************************************************************************Timing Measurement Parameters - Frame Acquisition***************************************************************************************/
double start_frame_acquisition;
double stop_frame_acquisition;
double current_frame_acquisition = 0.0;
double WCET_frame_acquisition = 0.0;
static double total_frame_acq = 0.0;
static double frame_acq_fstart=0.0, frame_acq_fstop=0.0;
/********************************************************************************************************Timee Measurement Parameters - Frame Differentiation***********************************************************************************/
double start_frame_differentiation;
double stop_frame_differentiation;
double current_frame_differentiation = 0.0;
double WCET_frame_differentiation = 0.0;
static double total_frame_differentiation = 0.0;
static double frame_diff_fstart=0.0, frame_diff_fstop = 0.0;
/********************************************************************************************************Timee Measurement Parameters - Frame Selection*****************************************************************************************/
double start_frame_selection;
double stop_frame_selection;
double current_frame_selection = 0.0;
double WCET_frame_selection = 0.0;
static double total_frame_selection = 0.0;
static double frame_select_fstart=0.0, frame_select_fstop = 0.0;
/***********************************************************************************************************************************************************************************************************************************************/
/* Purpose - process_image, process the incoming frame and save it in bigbuffer
 * Parameters - None, pointer to point to big buffer, size of the current frame
 * Returns - None
 */
static void process_image(const void *p, int size)
{
    int i, newi, newsize=0;
    
    struct timespec write_back_time;
    
    int y_temp, y2_temp, u_temp, v_temp;
    unsigned char *pptr = (unsigned char *)p;

    framecnt++;

    if(fmt.fmt.pix.pixelformat == V4L2_PIX_FMT_YUYV)
    {
     if(framecnt > -1){
        if(framecnt == 0) 
        {
            frame_acq_fstart=getTimeMsec();                                         // Measure the time to acquire the image acquisition        -   Start here
            frame_diff_fstart=getTimeMsec();
            frame_select_fstart=getTimeMsec();
        }
        for(i=0, newi=0; i<size; i=i+4, newi=newi+2)
        {
            // Y1=first byte and Y2=third byte
            bigbuffer[newi]=pptr[i];
            bigbuffer[newi+1]=pptr[i+2];
        }
            memcpy(dump_frames[position].big_buffer,bigbuffer,sizeof(bigbuffer));
            dump_frames[position].framesize = size/2;
            dump_frames[position].framecount = framecnt;
            dump_frames[position].write_back_time = write_back_time;
            position++;
            
            frame_acq_fstop = getTimeMsec();                                        // Measure the time to acquire the image acquisition        -   Stop here
            stop_frame_acquisition = getTimeMsec();
            current_frame_acquisition = stop_frame_acquisition - start_frame_acquisition;
            
            total_frame_acq += current_frame_acquisition;
            if(current_frame_acquisition > WCET_frame_acquisition)
                WCET_frame_acquisition = current_frame_acquisition;
     }
    }
    else{
        printf("ERROR - unknown dump format\n");
    }
}
/* Purpose - read frame, reads the image and directs to process block
 * Parameters - None
 * Returns - If frame is readable or not
 */
static int read_frame(void)
{
    start_frame_acquisition = getTimeMsec();
    struct v4l2_buffer buf;
    unsigned int i;
    CLEAR(buf);
    buf.type = V4L2_BUF_TYPE_VIDEO_CAPTURE;
    buf.memory = V4L2_MEMORY_MMAP;

    if (-1 == xioctl(fd, VIDIOC_DQBUF, &buf))
    {
      switch (errno)
      {
        case EAGAIN:
          return 0;

        case EIO:
          /* Could ignore EIO, but drivers should only set for serious errors, although some set for
             non-fatal errors too.
              */
          return 0;
        default:
            printf("mmap failure\n");
            errno_exit("VIDIOC_DQBUF");
      }
    }
    assert(buf.index < n_buffers);
    process_image(buffers[buf.index].start, buf.bytesused);
    if (-1 == xioctl(fd, VIDIOC_QBUF, &buf))
          errno_exit("VIDIOC_QBUF");
    return 1;
}
/**************************************************************************************************Web cam process end*******************************************************************************************/
/*******************************************************************************************Web camera device driver functions***********************************************************************************/
// stop the frame capturing ability for the v4l2 camera
static void stop_capturing(void)
{
        enum v4l2_buf_type type;
        type = V4L2_BUF_TYPE_VIDEO_CAPTURE;
                if (-1 == xioctl(fd, VIDIOC_STREAMOFF, &type))
                        errno_exit("VIDIOC_STREAMOFF");
}
// enable frame capturing for the v4l2 camera
static void start_capturing(void)
{
        unsigned int i;
        enum v4l2_buf_type type;
        for (i = 0; i < n_buffers; ++i) 
        {
             printf("allocated buffer %d\n", i);
             struct v4l2_buffer buf;
             CLEAR(buf);
             buf.type = V4L2_BUF_TYPE_VIDEO_CAPTURE;
             buf.memory = V4L2_MEMORY_MMAP;
             buf.index = i;

             if (-1 == xioctl(fd, VIDIOC_QBUF, &buf))
                   errno_exit("VIDIOC_QBUF");
        }
             type = V4L2_BUF_TYPE_VIDEO_CAPTURE;
             if (-1 == xioctl(fd, VIDIOC_STREAMON, &type))
                    errno_exit("VIDIOC_STREAMON");
}
// uninitialize the device so that you can close that seamlessly, otherwise it consumes a lot of power
static void uninit_device(void)
{
        unsigned int i;
        for (i = 0; i < n_buffers; ++i)
                if (-1 == munmap(buffers[i].start, buffers[i].length))
                        errno_exit("munmap");
        free(buffers);
}
// Write an mmap method to call in the init function to enable the init routine
static void init_mmap(void)
{
        struct v4l2_requestbuffers req;

        CLEAR(req);

        req.count = 6;
        req.type = V4L2_BUF_TYPE_VIDEO_CAPTURE;
        req.memory = V4L2_MEMORY_MMAP;

        if (-1 == xioctl(fd, VIDIOC_REQBUFS, &req)) 
        {
                if (EINVAL == errno) 
                {
                        fprintf(stderr, "%s does not support "
                                 "memory mapping\n", dev_name);
                        exit(EXIT_FAILURE);
                } else 
                {
                        errno_exit("VIDIOC_REQBUFS");
                }
        }

        if (req.count < 2) 
        {
                fprintf(stderr, "Insufficient buffer memory on %s\n", dev_name);
                exit(EXIT_FAILURE);
        }

        buffers = calloc(req.count, sizeof(*buffers));

        if (!buffers) 
        {
                fprintf(stderr, "Out of memory\n");
                exit(EXIT_FAILURE);
        }

        for (n_buffers = 0; n_buffers < req.count; ++n_buffers) {
                struct v4l2_buffer buf;

                CLEAR(buf);

                buf.type        = V4L2_BUF_TYPE_VIDEO_CAPTURE;
                buf.memory      = V4L2_MEMORY_MMAP;
                buf.index       = n_buffers;

                if (-1 == xioctl(fd, VIDIOC_QUERYBUF, &buf))
                        errno_exit("VIDIOC_QUERYBUF");

                buffers[n_buffers].length = buf.length;
                buffers[n_buffers].start =
                        mmap(NULL /* start anywhere */,
                              buf.length,
                              PROT_READ | PROT_WRITE /* required */,
                              MAP_SHARED /* recommended */,
                              fd, buf.m.offset);

                if (MAP_FAILED == buffers[n_buffers].start)
                        errno_exit("mmap");
        }
}
// Initialize the webcamera with IO_MMAP capabilities of v4l2
static void init_device(void)
{
    struct v4l2_capability cap;
    struct v4l2_cropcap cropcap;
    struct v4l2_crop crop;
    unsigned int min;

    if (-1 == xioctl(fd, VIDIOC_QUERYCAP, &cap))
    {
        if (EINVAL == errno) {
            fprintf(stderr, "%s is no V4L2 device\n",
                     dev_name);
            exit(EXIT_FAILURE);
        }
        else
        {
                errno_exit("VIDIOC_QUERYCAP");
        }
    }

    if (!(cap.capabilities & V4L2_CAP_VIDEO_CAPTURE))
    {
        fprintf(stderr, "%s is no video capture device\n",
                 dev_name);
        exit(EXIT_FAILURE);
    }
    if (!(cap.capabilities & V4L2_CAP_STREAMING))
    {
      fprintf(stderr, "%s does not support streaming i/o\n", dev_name);
      exit(EXIT_FAILURE);
    }

    /* Select video input, video standard and tune here. */

    CLEAR(cropcap);

    cropcap.type = V4L2_BUF_TYPE_VIDEO_CAPTURE;

    if (0 == xioctl(fd, VIDIOC_CROPCAP, &cropcap))
    {
        crop.type = V4L2_BUF_TYPE_VIDEO_CAPTURE;
        crop.c = cropcap.defrect; /* reset to default */

        if (-1 == xioctl(fd, VIDIOC_S_CROP, &crop))
        {
            switch (errno)
            {
                case EINVAL:
                    /* Cropping not supported. */
                    break;
                default:
                    /* Errors ignored. */
                        break;
            }
        }
    }
    else
    {
        /* Errors ignored. */
    }

    CLEAR(fmt);

    fmt.type = V4L2_BUF_TYPE_VIDEO_CAPTURE;

    if (force_format)
    {
        printf("FORCING FORMAT\n");
        fmt.fmt.pix.width       = HRES;
        fmt.fmt.pix.height      = VRES;
        // This one works for Logitech C200
        fmt.fmt.pix.pixelformat = V4L2_PIX_FMT_YUYV;
        fmt.fmt.pix.field       = V4L2_FIELD_NONE;

        if (-1 == xioctl(fd, VIDIOC_S_FMT, &fmt))
                errno_exit("VIDIOC_S_FMT");

        /* Note VIDIOC_S_FMT may change width and height. */
    }
    else
    {
        printf("ASSUMING FORMAT\n");
        /* Preserve original settings as set by v4l2-ctl for example */
        if (-1 == xioctl(fd, VIDIOC_G_FMT, &fmt))
                    errno_exit("VIDIOC_G_FMT");
    }

    /* Buggy driver paranoia. */
    min = fmt.fmt.pix.width * 2;
    if (fmt.fmt.pix.bytesperline < min)
            fmt.fmt.pix.bytesperline = min;
    min = fmt.fmt.pix.bytesperline * fmt.fmt.pix.height;
    if (fmt.fmt.pix.sizeimage < min)
            fmt.fmt.pix.sizeimage = min;
    init_mmap();
}
/* Function - Close Device
 * Performs - Closes the web camera functionality
 * Parameters - void
 * Parameters - void
 */
static void close_device(void)
{
        if (-1 == close(fd))
                errno_exit("close");

        fd = -1;
}
/* Function - Open Device
 * Performs - Open the web camera functionality
 * Parameters - void
 * Parameters - void
 */
static void open_device(void)
{
  struct stat st;

  if (-1 == stat(dev_name, &st)) {
    fprintf(stderr, "Cannot identify '%s': %d, %s\n",
                  dev_name, errno, strerror(errno));
    exit(EXIT_FAILURE);
  }

  if (!S_ISCHR(st.st_mode)) {
    fprintf(stderr, "%s is no device\n", dev_name);
    exit(EXIT_FAILURE);
  }

  fd = open(dev_name, O_RDWR /* required */ | O_NONBLOCK, 0);

  if (-1 == fd) {
    fprintf(stderr, "Cannot open '%s': %d, %s\n",
                 dev_name, errno, strerror(errno));
    exit(EXIT_FAILURE);
  }
}
/*********************************************************************************************************Web camera device driver functions end***********************************************************************/
//Transform function prototype
void convert_to_transform(unsigned char *arr);
/***************************************************************************************************************Functional Routines Start*****************************************************************************/
/* Function - Frame differentiation
 * Purpose - Takes into account of the ranges in which the difference between initial and final frames reside. Values in most ranges indicates tick detect.
 * Returns - total number of frames differentiation is performed so far
 * Parameters - Size of the frames
 */
int frames_differenced_so_far = 0;
int frame_differentiation(int size)
{
    start_frame_differentiation=getTimeMsec();
    
    static int frames_received;
    frames_received = framecnt;
    static int frames_sent_so_far = 0;
    int diff;
    for(int frame_location = frames_sent_so_far;frame_location < frames_received;frame_location++){
        long int range_less_than_10 = 0, range_less_than_20 = 0, range_less_than_30 = 0, range_less_than_40 = 0, range_less_than_50 = 0, range_less_than_60 = 0, range_less_than_70 = 0, range_less_than_80 = 0, range_less_than_90 = 0, range_less_than_100 = 0, range_less_than_110 = 0,
             range_less_than_120 = 0, range_less_than_130 = 0, range_less_than_140 = 0, range_less_than_150 = 0, range_less_than_160 = 0, range_less_than_170 = 0, range_less_than_180 = 0, range_less_than_190 = 0, range_less_than_200 = 0, range_less_than_210 = 0,
             range_less_than_220 = 0, range_less_than_230 = 0, range_less_than_240 = 0, range_less_than_250 = 0, range_less_than_260 = 0;
        int count = 0;
        for(int i = 0;i < size;i++){
            diff = dump_frames[frame_location+1].big_buffer[i] - dump_frames[frame_location].big_buffer[i];
            diff = diff < 0?diff * -1:diff;
            if(count >= 6){
                dump_frames[frame_location+1].tick = TRUE;
                break;
            }   
            if((diff > 0) && (diff <= 10)){
                range_less_than_10++;
                if(range_less_than_10 == 1){
                    count++;
                }    
            }
            else if((diff > 10) && (diff <= 20)){
                range_less_than_20++;
                if(range_less_than_20 == 1){
                    count++;
                }
            }
            else if((diff > 20) && (diff <= 30)){
                range_less_than_30++;
                if(range_less_than_30 == 1){
                    count++;
                }
            }
            else if((diff > 30) && (diff <= 40)){
                range_less_than_40++;
                if(range_less_than_40 == 1){
                    count++;
                }
            }
            else if((diff > 40) && (diff <= 50)){
                range_less_than_50++;
                if(range_less_than_50 == 1){
                    count++;
                }
            }
            else if((diff > 50) && (diff <= 60)){
                range_less_than_60++;
                if(range_less_than_60 == 1){
                    count++;
                }
            }
            else if((diff > 60) && (diff <= 70)){
                range_less_than_70++;
                if(range_less_than_70 == 1){
                    count++;
                }
            } 
            else if((diff > 70) && (diff <= 80)){
                range_less_than_80++;
                if(range_less_than_80 == 1){
                    count++;
                }
            }  
            else if((diff > 80) && (diff <= 90)){
                range_less_than_90++;
                if(range_less_than_90 == 1){
                    count++;
                }
            }  
            else if((diff > 90) && (diff <= 100)){
                range_less_than_100++;
                if(range_less_than_100 == 1){
                    count++;
                }
            }  
            else if((diff > 100) && (diff <= 110)){
                range_less_than_110++;
                if(range_less_than_110 == 1){
                    count++;
                }
            }
            else if((diff > 110) && (diff <= 120)){
                range_less_than_120++;
                if(range_less_than_120 == 1){
                    count++;
                }
            }    
            else if((diff > 120) && (diff <= 130)){
                range_less_than_130++;
                if(range_less_than_130 == 1){
                    count++;
                }
            }    
            else if((diff > 130) && (diff <= 140)){
                range_less_than_140++;
                if(range_less_than_140 == 1){
                    count++;
                }
            }    
            else if((diff > 140) && (diff <= 150)){
                range_less_than_150++;
                if(range_less_than_150 == 1){
                    count++;
                }
            }
            else if((diff > 150) && (diff <= 160)){
                range_less_than_160++;
                if(range_less_than_160 == 1){
                    count++;
                }
            }  
            else if((diff > 160) && (diff <= 170)){
                range_less_than_170++;
                if(range_less_than_170 == 1){
                    count++;
                }
            }  
            else if((diff > 170) && (diff <= 180)){
                range_less_than_180++;
                if(range_less_than_180 == 1){
                    count++;
                }
            }  
            else if((diff > 180) && (diff <= 190)){
                range_less_than_190++;
                if(range_less_than_190 == 1){
                    count++;
                }
            }
            else if((diff > 190) && (diff <= 200)){
                range_less_than_200++;
                if(range_less_than_200 == 1){
                    count++;
                }
            }    
            else if((diff > 200) && (diff <= 210)){
                range_less_than_210++;
                if(range_less_than_210 == 1){
                    count++;
                }
            }    
            else if((diff > 210) && (diff <= 220)){
                range_less_than_220++;
                if(range_less_than_220 == 1){
                    count++;
                }
            }    
            else if((diff > 220) && (diff <= 230)){
                range_less_than_230++;
                if(range_less_than_230 == 1){
                    count++;
                }
            }
            else if((diff > 230) && (diff <= 240)){
                range_less_than_240++;
                if(range_less_than_240 == 1){
                    count++;
                }
            }
            else if((diff > 240) && (diff <= 250)){
                range_less_than_250++;
                if(range_less_than_250 == 1){
                    count++;
                }
            }    
            else if((diff > 250) && (diff <= 260)){
                range_less_than_260++;
                if(range_less_than_260 == 1){
                    count++;
                }
            }
        }
        frames_differenced_so_far += (frames_received - frames_sent_so_far);
        frames_sent_so_far = frames_received;  
        stop_frame_differentiation=getTimeMsec();
        frame_diff_fstop=getTimeMsec();
        current_frame_differentiation= stop_frame_differentiation - start_frame_differentiation;
        total_frame_differentiation += current_frame_differentiation;
        printf("Frame %d has diff jitter of %lf",position, current_frame_differentiation - ((total_frame_differentiation/362)*100));
        if(current_frame_differentiation > WCET_frame_differentiation)
            WCET_frame_differentiation = current_frame_differentiation;
    }
    return frames_differenced_so_far;    
}
/*******************************************************************************************************************************************************/
/* Function frame selection
 * Purpose - select the function at 1HZ and dump it into SD card memory
 * Parameters - Frame size
 * Returns - None
 */ 
static int dump_position = 0;
static int frames_selected_so_far = 0;
static int arr[250] = {0};
void perform_selection(int size){
    start_frame_selection=getTimeMsec();
    static int frames_received_for_selection;
    frames_received_for_selection = frames_differenced_so_far;
    for(int i = frames_selected_so_far;i < frames_received_for_selection;i++){
        if(dump_frames[i].tick){
            if(dump_frames[i+1].tick){
                arr[dump_position++] = i+1;
                dump_pgm(dump_frames[i+2].big_buffer, dump_frames[i+2].framesize, dump_frames[i+2].framecount, &dump_frames[i+2].write_back_time);
                i++;
            }
            else
                arr[dump_position++] = i;
                dump_pgm(dump_frames[i+1].big_buffer, dump_frames[i+1].framesize, dump_frames[i+1].framecount, &dump_frames[i+1].write_back_time);
        }
    }
    frames_selected_so_far = frames_received_for_selection;  
    stop_frame_selection=getTimeMsec();
    frame_select_fstop=getTimeMsec();
    current_frame_selection = stop_frame_selection - start_frame_selection;
    total_frame_selection += current_frame_selection;
    printf("Frame %d has select jitter of %lf",dump_position, current_frame_selection - (total_frame_selection/181)*100);
    if(current_frame_selection > WCET_frame_selection)
        WCET_frame_selection = current_frame_selection;
}    
/********************************************************************************************************************************************************/
/* Function - Convert grey scale to negative
 * Returns - None
 * Parameters - Current frame array
 */
void convert_to_transform(unsigned char *arr){
    for(int i = 0; i < dump_frames[0].framesize;i++){
        arr[i] = 255 - arr[i];
        if(arr[i] < 0)
            arr[i] = 0;
    }    
}   
/******************************************************************************************************************************************************/
/* Function - Perform Dump
 * Purpose - flashes the selected frame to the sd card
 * Returns None
 * Parameters - None
 */
void perform_dump(){
    int pos = 0;
    for(int i = 0;i < 1804;i++){
        if(i == arr[pos]){
            printf("Frame %d is dumped",i);
            convert_to_transform(dump_frames[i+1].big_buffer);
            dump_pgm(dump_frames[i+1].big_buffer, dump_frames[i+1].framesize, dump_frames[i+1].framecount, &dump_frames[i+1].write_back_time);
            pos++;
        }
    }   
}
/*****************************************************************************************************************  Functional Routines End ****************************************************************************************************/
/****************************************************************************************************** Store frame in ring buffer and frame differentiation **********************************************************************************/
void main(void)
{
    dev_name = "/dev/video0";
    double current_time;
    struct timespec rt_res, monotonic_res;
    int i, rc, cpuidx;
    cpu_set_t threadcpu;
    // CREATE SCHEDULING ATTRIBUTES for the main thread
    struct sched_param main_param;
    pid_t mainpid;

    start_time=getTimeMsec();
    printf("\rCurrent start time = %lf\n",start_time);
    // delay start for a second
    usleep(1000000);

    printf("Starting High Rate Sequencer Example\n");
    // print the number of running cores on the CPU
    get_cpu_core_config();
    // clock_getres prints the clock resolution
    clock_getres(CLOCK_REALTIME, &rt_res);
    printf("RT clock resolution is %ld sec, %ld nsec\n", rt_res.tv_sec, rt_res.tv_nsec);
    // print the total number of processor - get_nprocs_conf, prints the total number of available processors - get_nprocs();
    printf("System has %d processors configured and %d available.\n", get_nprocs_conf(), get_nprocs());

    // initialize the sequencer semaphores
    if (sem_init (&semS1, 0, 0))
        { printf ("Failed to initialize S1 semaphore\n"); exit (-1); }
    if (sem_init (&semS2, 0, 0)) 
        { printf ("Failed to initialize S2 semaphore\n"); exit (-1); }
    if (sem_init (&semS3, 0, 0)) 
        { printf ("Failed to initialize S3 semaphore\n"); exit (-1); }
    //if (sem_init (&semS4, 0, 0)) 
    //    { printf ("Failed to initialize S4 semaphore\n"); exit (-1); }
    
    mainpid=getpid();

    rt_max_prio = sched_get_priority_max(SCHED_FIFO);
    rt_min_prio = sched_get_priority_min(SCHED_FIFO);

    rc=sched_getparam(mainpid, &main_param);
    main_param.sched_priority=rt_max_prio;
    rc=sched_setscheduler(getpid(), SCHED_FIFO, &main_param);
    if(rc < 0) perror("main_param");

    print_scheduler();

    printf("rt_max_prio=%d\n", rt_max_prio);
    printf("rt_min_prio=%d\n", rt_min_prio);
    
     // sequencer
    CPU_ZERO(&threadcpu);
	CPU_SET(1, &threadcpu);
	rc=pthread_attr_init(&rt_sched_attr[0]);
	rc=pthread_attr_setinheritsched(&rt_sched_attr[0], PTHREAD_EXPLICIT_SCHED);
	rc=pthread_attr_setschedpolicy(&rt_sched_attr[0], SCHED_FIFO);
	rc=pthread_attr_setaffinity_np(&rt_sched_attr[0], sizeof(cpu_set_t), &threadcpu);
	rt_param[0].sched_priority=rt_max_prio-0;
	pthread_attr_setschedparam(&rt_sched_attr[0], &rt_param[0]);
	threadParams[0].threadIdx=0;
	
	// frame acquisition
	CPU_SET(2, &threadcpu);
	rc=pthread_attr_init(&rt_sched_attr[1]);
	rc=pthread_attr_setinheritsched(&rt_sched_attr[1], PTHREAD_EXPLICIT_SCHED);
	rc=pthread_attr_setschedpolicy(&rt_sched_attr[1], SCHED_FIFO);
	rc=pthread_attr_setaffinity_np(&rt_sched_attr[1], sizeof(cpu_set_t), &threadcpu);
	rt_param[1].sched_priority=rt_max_prio-1;
	pthread_attr_setschedparam(&rt_sched_attr[1], &rt_param[1]);
	threadParams[1].threadIdx=1;

	// frame differencing
	CPU_SET(3, &threadcpu);
	rc=pthread_attr_init(&rt_sched_attr[2]);
	rc=pthread_attr_setinheritsched(&rt_sched_attr[2], PTHREAD_EXPLICIT_SCHED);
	rc=pthread_attr_setschedpolicy(&rt_sched_attr[2], SCHED_FIFO);
	rc=pthread_attr_setaffinity_np(&rt_sched_attr[2], sizeof(cpu_set_t), &threadcpu);
	rt_param[2].sched_priority=rt_max_prio-2;
	pthread_attr_setschedparam(&rt_sched_attr[2], &rt_param[2]);
	threadParams[2].threadIdx=2;
    
    // frame selection
	CPU_SET(3, &threadcpu);
	rc=pthread_attr_init(&rt_sched_attr[3]);
	rc=pthread_attr_setinheritsched(&rt_sched_attr[3], PTHREAD_EXPLICIT_SCHED);
	rc=pthread_attr_setschedpolicy(&rt_sched_attr[3], SCHED_FIFO);
	rc=pthread_attr_setaffinity_np(&rt_sched_attr[3], sizeof(cpu_set_t), &threadcpu);
	rt_param[3].sched_priority=rt_max_prio-3;
	pthread_attr_setschedparam(&rt_sched_attr[3], &rt_param[3]);
	threadParams[3].threadIdx=3;

    current_time=getTimeMsec();
    //syslog(LOG_CRIT, "RTMAIN: on cpu=%d @ sec=%lf, elapsed=%lf\n", sched_getcpu(), start_time, current_time);

    // Create Service threads which will block awaiting release for:
    //
    open_device();
    init_device();

    start_capturing();
    // Servcie_1 = RT_MAX-1	@ 10 Hz
    //
    clock_gettime(CLOCK_REALTIME, &start_time_val);
    clock_gettime(CLOCK_REALTIME, &current_time_val);
    
    rt_param[1].sched_priority=rt_max_prio-1;
    pthread_attr_setschedparam(&rt_sched_attr[1], &rt_param[1]);
    rc=pthread_create(&threads[1],               // pointer to thread descriptor
                      &rt_sched_attr[1],         // use specific attributes
                      //(void *)0,               // default attributes
                      Service_1,                 // thread function entry point
                      (void *)&(threadParams[1]) // parameters to pass in
                     );
    if(rc < 0)
        perror("pthread_create for service 1");
    else
        printf("pthread_create successful for service 1\n");


    // Service_2 = RT_MAX-2	@ 2 Hz
    //
    rt_param[2].sched_priority=rt_max_prio-2;
    pthread_attr_setschedparam(&rt_sched_attr[2], &rt_param[2]);
    rc=pthread_create(&threads[2], &rt_sched_attr[2], Service_2, (void *)&(threadParams[2]));
    if(rc < 0)
        perror("pthread_create for service 2");
    else
        printf("pthread_create successful for service 2\n");


    // Service_3 = RT_MAX-3	@ 1 Hz
    //
    rt_param[3].sched_priority=rt_max_prio-3;
    pthread_attr_setschedparam(&rt_sched_attr[3], &rt_param[3]);
    rc=pthread_create(&threads[3], &rt_sched_attr[3], Service_3, (void *)&(threadParams[3]));
    if(rc < 0)
        perror("pthread_create for service 3");
    else
        printf("pthread_create successful for service 3\n");

    // Create Sequencer thread, which like a cyclic executive, is highest prio 
    printf("Start sequencer\n");
    threadParams[0].sequencePeriods=RTSEQ_PERIODS;

    // Sequencer = RT_MAX	@ 120 Hz
    //
    rt_param[0].sched_priority=rt_max_prio;
    pthread_attr_setschedparam(&rt_sched_attr[0], &rt_param[0]);
    rc=pthread_create(&threads[0], &rt_sched_attr[0], Sequencer, (void *)&(threadParams[0]));
    if(rc < 0)
        perror("pthread_create for sequencer service 0");
    else
        printf("pthread_create successful for sequeencer service 0\n");


   for(i=0;i<NUM_THREADS;i++)
       pthread_join(threads[i], NULL);
       
   stop_capturing();

   uninit_device();
   close_device();
   
   printf("Total frames Stored = %d\n",framecnt);
   /******************************************************************************** Print the WCET time for all the 3 essential process *********************************************************/
   printf("Worst Case acquisition Time = %lf Worst Case Differentiation Time = %lf Worst Case Selection Time = %lf\n",WCET_frame_acquisition*100,WCET_frame_differentiation*100,WCET_frame_selection*100); 
   /******************************************************************************** Print the Average time for all the 3 essential process *********************************************************/
   printf("Average acquisition Time = %lf Average differentiation Time = %lf Average Selection time = %lf\n",(total_frame_acq/framecnt)*100,(total_frame_differentiation/362)*100,(total_frame_selection/181)*100);
   printf("Frame acquisition FPS = %lf Frame differentiation FPS = %lf, Selection FPS = %lf\n",(frame_acq_fstop - frame_acq_fstart)/181,(frame_diff_fstop - frame_diff_fstart)/181,(frame_select_fstop - frame_select_fstart)/181);
   printf("\nTEST COMPLETE\n");
}
/***************************************************************************************************End of Main Method********************************************************************************************/
/* Function     - Service_0
 * Brief        - The sequencer routine runs at 120Hz on Core 0 that handles sequencing of other events 
 * parameters   - a pointer to the current thread
 * Returns      - None
 */
void *Sequencer(void *threadp)
{
    struct timespec delay_time = {0, RTSEQ_DELAY_NSEC};
    struct timespec std_delay_time = {0, RTSEQ_DELAY_NSEC};
    struct timeval current_time_val={0,0};

    struct timespec remaining_time;
    double current_time, last_time, scaleDelay;
    double delta_t=(RTSEQ_DELAY_NSEC/(double)NANOSEC_PER_SEC);
    double scale_dt;
    int rc, delay_cnt=0;
    threadParams_t *threadParams = (threadParams_t *)threadp;

    current_time=getTimeMsec(); last_time=current_time-delta_t;

    //syslog(LOG_CRIT, "RTSEQ: start on cpu=%d @ sec=%lf after %lf with dt=%lf\n", sched_getcpu(), current_time, last_time, delta_t);

    do
    {
        current_time=getTimeMsec(); delay_cnt=0;

#ifdef DRIFT_CONTROL
        scale_dt = (current_time - last_time) - delta_t;
        delay_time.tv_nsec = std_delay_time.tv_nsec - (scale_dt * (NANOSEC_PER_SEC+DT_SCALING_UNCERTAINTY_NANOSEC))-CLOCK_BIAS_NANOSEC;
        //syslog(LOG_CRIT, "RTSEQ: scale dt=%lf @ sec=%lf after=%lf with dt=%lf\n", scale_dt, current_time, last_time, delta_t);
#else
        delay_time=std_delay_time; scale_dt=delta_t;
#endif


#ifdef ABS_DELAY
        clock_gettime(CLOCK_REALTIME, &current_time_val);
        delay_time.tv_sec = current_time_val.tv_sec;
        delay_time.tv_nsec = current_time_val.tv_usec + delay_time.tv_nsec;

        if(delay_time.tv_nsec > NANOSEC_PER_SEC)
        {
            delay_time.tv_sec = delay_time.tv_sec + 1;
            delay_time.tv_nsec = delay_time.tv_nsec - NANOSEC_PER_SEC;
        }
        //syslog(LOG_CRIT, "RTSEQ: cycle %08llu delay for dt=%lf @ sec=%d, nsec=%d to sec=%d, nsec=%d\n", seqCnt, scale_dt, current_time_val.tv_sec, current_time_val.tv_nsec, delay_time.tv_sec, delay_time.tv_nsec);
#endif
        // Delay loop with check for early wake-up
        do
        {
#ifdef ABS_DELAY
            rc=clock_nanosleep(CLOCK_REALTIME, TIMER_ABSTIME, &delay_time, (struct timespec *)0);
#else
            rc=clock_nanosleep(CLOCK_REALTIME, 0, &delay_time, &remaining_time);
#endif

            if(rc == EINTR)
            { 
                // syslog(LOG_CRIT, "RTSEQ: EINTR @ sec=%lf\n", current_time);
                delay_cnt++;
            }
            else if(rc < 0)
            {
                perror("RTSEQ: nanosleep");
                exit(-1);
            }

            //syslog(LOG_CRIT, "RTSEQ: WOKE UP\n");
           
        } while(rc == EINTR);

        // Release each service at a sub-rate of the generic sequencer rate

        // Service_1 = RT_MAX-1	@ 10 Hz
        if((seqCnt % 12) == 0) sem_post(&semS1);

        // Service_2 = RT_MAX-2	@ 2 Hz
        if((seqCnt % 60) == 0) sem_post(&semS2);

        // Service_3 = RT_MAX-3	@ 1 Hz
        if((seqCnt % 120) == 0) sem_post(&semS3);

        seqCnt++;
        last_time=current_time;

    } while(!abortTest && (seqCnt < threadParams->sequencePeriods));

    sem_post(&semS1); sem_post(&semS2); sem_post(&semS3); sem_post(&semS4);
    abortS1=TRUE; abortS2=TRUE; abortS3=TRUE; abortS4=TRUE;

    pthread_exit((void *)0);
}
/* Function     - Service_1
 * Brief        - Frame acquisition routine running on core 2 at 10Hz 
 * parameters   - a pointer to the current thread
 * Returns      - None
 */
void *Service_1(void *threadp)
{
    double current_time, previous_time = 0.0;
    unsigned long long S1Cnt=0;
    threadParams_t *threadParams = (threadParams_t *)threadp;

    current_time=getTimeMsec();
    while(!abortS1)
    {
        sem_wait(&semS1);
        S1Cnt++;
        current_time=getTimeMsec();
        read_frame();
        //syslog(LOG_CRIT, "S1: release %llu @ sec=%lf with obtained frequency=%lf\n", S1Cnt, current_time, 1/(current_time - previous_time));
        previous_time = current_time;
    }
    pthread_exit((void *)0);
}
/* Function     - Service_2
 * Brief        - This calls the frame differential routine running on CPU(3) core at 2Hz 
 * parameters   - a pointer to the current thread
 * Returns      - None
 */
int total_frames;
void *Service_2(void *threadp)
{
    double current_time;
    unsigned long long S2Cnt=0;
    threadParams_t *threadParams = (threadParams_t *)threadp;
    int pos = 0;
    current_time=getTimeMsec();
    // syslog(LOG_CRIT, "S2: start on cpu=%d @ sec=%lf\n", sched_getcpu(), current_time);
    while(!abortS2)
    {
        sem_wait(&semS2);
        S2Cnt++;
        total_frames = frame_differentiation(dump_frames[0].framesize);
        //printf("Total frames differenced = %d\n",total_frames);
        current_time=getTimeMsec();
    }
    pthread_exit((void *)0);
}
/* Function     - Service_3
 * Brief        - This calls the frame Selection routine running on CPU(3) core at 1Hz 
 * parameters   - a pointer to the current thread
 * Returns      - None
 */
void *Service_3(void *threadp)
{
    struct timespec write_back;
    printf("Control Reaches here");
    double current_time;
    unsigned long long S3Cnt=0;
    threadParams_t *threadParams = (threadParams_t *)threadp;

    current_time=getTimeMsec();
    // syslog(LOG_CRIT, "S3: start on cpu=%d @ sec=%lf\n", sched_getcpu(), current_time);

    while(!abortS3)
    {
        sem_wait(&semS3);
        S3Cnt++;
        perform_selection(dump_frames[0].framesize);
        current_time=getTimeMsec();
        // syslog(LOG_CRIT, "S3: release %llu @ sec=%lf\n", S3Cnt, current_time);
    }
    can_dump = true;
    pthread_exit((void *)0);
}
/* Function - getTimeMsec()
 * Brief    - Subtract the current time to the start time
 * Parameters - void
 * Returns - Double, - The time taken from to complete the current process
 */
double getTimeMsec(void)
{
  struct timespec event_ts = {0, 0};
  double event_time=0;
  
  clock_gettime(CLOCK_REALTIME, &event_ts);
  event_time = ((event_ts.tv_sec) + ((event_ts.tv_nsec)/(double)NANOSEC_PER_SEC));
  return (event_time - start_time);
}
/* Function     - print_scheduler()
 * Brief        - Print the current scheduler mechanism
 * Parameters   - None
 * Returns      - None
 */
void print_scheduler(void)
{
   int schedType, scope;

   schedType = sched_getscheduler(getpid());

   switch(schedType)
   {
       case SCHED_FIFO:
           printf("Pthread Policy is SCHED_FIFO\n");
           break;
       case SCHED_OTHER:
           printf("Pthread Policy is SCHED_OTHER\n"); exit(-1);
         break;
       case SCHED_RR:
           printf("Pthread Policy is SCHED_RR\n"); exit(-1);
           break;
       default:
           printf("Pthread Policy is UNKNOWN\n"); exit(-1);
   }

   pthread_attr_getscope(&main_attr, &scope);

   if(scope == PTHREAD_SCOPE_SYSTEM)
       printf("PTHREAD SCOPE SYSTEM\n");
   else if (scope == PTHREAD_SCOPE_PROCESS)
       printf("PTHREAD SCOPE PROCESS\n");
   else
       printf("PTHREAD SCOPE UNKNOWN\n");
}
/* Function - print_scheduler()
 * Brief- Print the total number of CPU's running concurrently
 * Parameters - None
 * Returns - None
 */
void get_cpu_core_config(void)
{
   cpu_set_t cpuset;
   pthread_t callingThread;
   int rc, idx;

   CPU_ZERO(&cpuset);

   // get affinity set for main thread
   callingThread = pthread_self();

   // Check the affinity mask assigned to the thread 
   rc = pthread_getaffinity_np(callingThread, sizeof(cpu_set_t), &cpuset);
   if (rc != 0)
       perror("pthread_getaffinity_np");
   else
   {
       printf("thread running on CPU=%d, CPUs =", sched_getcpu());
       
       for (idx = 0; idx < CPU_SETSIZE; idx++)
           if (CPU_ISSET(idx, &cpuset))
               printf(" %d", idx);

       printf("\n");
   }

   printf("Using CPUS=%d from total available.\n", CPU_COUNT(&cpuset));
}

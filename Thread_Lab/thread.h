#ifndef MY_THREAD_H
#define MY_THREAD_H

#include <stdbool.h>
#include <sys/time.h>
#include <stdio.h>
#include <pthread.h>
#include <stdlib.h>
#include <semaphore.h>

#define DATA_SIZE 100000000
#define NTHREADS 8
#define STEP (DATA_SIZE/NTHREADS)
#define DATA_MAX 255
#define BUCKET_SIZE 8

extern int bucket[BUCKET_SIZE];  // record correct bucket result
extern int global_histogram[BUCKET_SIZE];
extern unsigned char data[DATA_SIZE];

typedef struct {
    char *name;  /* Your full name */
    char *id;    /* Your UID */
} info_t;

extern info_t info;

int printHistogram(int *hist, int n);

void *histo_0(void *vargp);

void *histo_1(void *vargp);

void *histo_2(void *vargp);

void *histo_3(void *vargp);

void *histo_4(void *vargp);

typedef void* (*f)(void* );
extern f thread_routine[5];  

void run_threads(void);

bool check_info(info_t info);

#endif MY_THREAD_H

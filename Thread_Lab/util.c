#include "thread.h"

int bucket[BUCKET_SIZE] = {0};  // record correct bucket result
int global_histogram[BUCKET_SIZE] = {0};
unsigned char data[DATA_SIZE];

int lower_range[5] = {0, 13000, 10000, 1000, 0};
int upper_range[5] = {200, 45000, 20000, 5000, 1000};

int flag_range[5] = {0};
int correctness[5] = {0};

f thread_routine[5] = {&histo_0, &histo_1, &histo_2, &histo_3, &histo_4};

void run_threads(){
  // time variables
	struct timeval start, end;
	long mtime, secs, usecs; 

	// thread id
	pthread_t thread_id[NTHREADS];

	long int i;

	// generate data
	for (i = 0; i < DATA_SIZE; i++) { 
		int datum = rand() % DATA_MAX; 
		data[i] = datum;
		bucket[datum%BUCKET_SIZE]++;
	}

	// run through each thread routine
	int thread_rt_id;
	for (thread_rt_id = 0; thread_rt_id < 5; thread_rt_id++){

		int buc_id;
		for (buc_id=0; buc_id<BUCKET_SIZE; buc_id++){
			global_histogram[buc_id] = 0;
		}

		printf("\nRunning thread_%d: \n", thread_rt_id);
		// get start time
		gettimeofday(&start, NULL);

		for(i=0; i<NTHREADS; i++){
			pthread_create(&thread_id[i], NULL, thread_routine[thread_rt_id], (void*)i);
		}		

		for(i=0; i < NTHREADS; i++)
		{
			pthread_join( thread_id[i], NULL); 
		}

		// visualize the histogram
		int sum = printHistogram(global_histogram, BUCKET_SIZE);
    if (sum == DATA_SIZE){
      correctness[thread_rt_id] = 1;
    } else {
      printf("Wrong result. Please check the correctness of your code.\n");
    }

		// print the total time
		gettimeofday(&end, NULL);
		secs  = end.tv_sec  - start.tv_sec;
		usecs = end.tv_usec - start.tv_usec;
		mtime = ((secs) * 1000 + usecs/1000.0) + 0.5;
		printf("Elapsed time: %ld millisecs\n", mtime);
    
    if (correctness[thread_rt_id] && (mtime < lower_range[thread_rt_id] || mtime > upper_range[thread_rt_id])){
      flag_range[thread_rt_id] = 1;
      printf("Hmm, this is a strange range for this task! The TA will check this solution manually.\n");
    }
		
	}
 
}


int printHistogram(int *hist, int n) {

	int i, sum=0;
	for (i = 0; i < n; i++) {
		printf("Bucket [%d] ", i);
		printf("%d", hist[i]);
		printf("\n");
		sum += hist[i];
	}
	printf("Calculated sum: %d, correct sum: %d\n", sum, DATA_SIZE);
 
  return sum;
}

bool check_info(info_t info){
    char hash_cmd[64];
    
	  /* Students must fill in their team information */
  	if (!strcmp(info.name, "") || !strcmp(info.name, "YOUR_NAME")) {
  	    printf("ERROR: Please provide your name in thread.c.\n");
  	    return false;
  	} else
  	    printf("YOUR NAME: %s\n", info.name);
           
  	if ((*info.id == '\0') || !strcmp(info.name, "YOUR_UID")) {
  	    printf("ERROR.  You must fill in your UID in thread.c!\n");
  	    return false;
  	} 
	  else {
	      printf("YOUR UID: %s\n", info.id);
	      /* Check that UID is number (not malicious code) */
        int uid_len = strlen(info.id);
        int i;
        for (i=0; i<uid_len; i++){
      		if (isdigit(info.id[i]) == 0) {
      	            printf("ERROR.  UID must be a number!\n");
      		    return false;
      		}
        }
    }
    system("echo -n 'YOUR HASH: ' ");
    sprintf(hash_cmd, "echo -n %s | md5sum | cut -c -6", info.name);
    system(hash_cmd);
    printf("\n");
    
    return true;
}
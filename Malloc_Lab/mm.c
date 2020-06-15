/* 
 * mm.c -  Simple allocator based on implicit free lists, 
 *         next fit placement, and boundary tag coalescing. 
 *
 * Each block has header and footer of the form:
 * 
 *      31                     3  2  1  0 
 *      -----------------------------------
 *     | s  s  s  s  ... s  s  s  0  0  a/f
 *      ----------------------------------- 
 * 
 * where s are the meaningful size bits and a/f is set 
 * iff the block is allocated. The list has the following form:
 *
 * begin                                                          end
 * heap                                                           heap  
 *  -----------------------------------------------------------------   
 * |  pad   | hdr(8:a) | ftr(8:a) | zero or more usr blks | hdr(8:a) |
 *  -----------------------------------------------------------------
 *          |       prologue      |                       | epilogue |
 *          |         block       |                       | block    |
 *
 * The allocated prologue and epilogue blocks are overhead that
 * eliminate edge conditions during coalescing.
 *
 * NEXT FIT IMPLEMENTATION
 * A global ptr next_fit_ptr keeps track of the last allocated block, 
 * so next time mm_malloc is called, search begins at next_fit_ptr
 *
 * Commented-Out Unused Optimizations: 
 * freed_blks optimization: keep track of global number of freed blocks,
 * if there is a large amount, wrap around in find_fit
 *
 * global_bfree optimization: after large block is freed, store ptr
 * to block, then return this block at next call to mm_malloc without
 * searching through heap
 *
 *NOTE: because of selected traces, setting next_fit_ptr = last coalesced
 *block in coalesce and setting next_fit_ptr = heap_listp instead of wrapping
 *in find_fit resulted in better score than with above opts
 */

#include <stdio.h>
#include <unistd.h>
#include <string.h>
#include <stdlib.h>
#include "mm.h"
#include "memlib.h"
#include <stdint.h>

/* Your info */
team_t team = { 
    /* First and last name */
    "Faith Twardzik",
    /* UID */
    "105083037"
}; 

/* $begin mallocmacros */
/* Basic constants and macros */
#define WSIZE       4       /* word size (bytes) */  
#define DSIZE       8       /* doubleword size (bytes) */
#define CHUNKSIZE  (1<<16)  /* initial heap size (bytes) */
#define OVERHEAD    8       /* overhead of header and footer (bytes) */

#define MAX(x, y) ((x) > (y)? (x) : (y))  

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc)  ((size) | (alloc))

/* Read and write a word at address p */
#define GET(p)       (*(uint32_t *)(p))
#define PUT(p, val)  (*(uint32_t *)(p) = (val))  

/* Read the size and allocated fields from address p */
#define GET_SIZE(p)  (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp)       ((char *)(bp) - WSIZE)  
#define FTRP(bp)       ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp)  ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp)  ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))
/* $end mallocmacros */

/* Global variables */
static char *heap_listp;  /* pointer to first block */  
static char *next_fit_ptr; /* pointer to block after previously allocated block */

/* unused optimization vars */
//static int freed_blks;
//static char *global_bfree;

/* function prototypes for internal helper routines */
static void *extend_heap(size_t words);
static void place(void *bp, size_t asize);
static void *find_fit(size_t asize);
static void *coalesce(void *bp);
static void printblock(void *bp); 
static void checkblock(void *bp);

/* 
 * mm_init - Initialize the memory manager 
 */
/* $begin mminit */
int mm_init(void) 
{
    /* create the initial empty heap */
    if ((heap_listp = mem_sbrk(4*WSIZE)) == NULL)
	return -1;
    PUT(heap_listp, 0);                        /* alignment padding */
    PUT(heap_listp+WSIZE, PACK(OVERHEAD, 1));  /* prologue header */
	heap_listp += DSIZE;

    PUT(heap_listp, PACK(OVERHEAD, 1));  /* prologue footer */ 
    PUT(heap_listp+WSIZE, PACK(0, 1));   /* epilogue header */ 

	next_fit_ptr = heap_listp; /* initialize nfp to beginning of heap */

// unused opt initializations
//  global_bfree = NULL;
//  freed_blks = 0;

    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL)
	return -1;
    return 0;
}
/* $end mminit */

/* 
 * mm_malloc - Allocate a block with at least size bytes of payload 
 */
/* $begin mmmalloc */
void *mm_malloc(size_t size) 
{
    uint32_t asize;      /* adjusted block size */
    uint32_t extendsize; /* amount to extend heap if no fit */
    char *bp;      

    /* Ignore spurious requests */
    if (size <= 0)
	return NULL;

    /* Adjust block size to include overhead and alignment reqs. */
    if (size <= DSIZE)
	asize = DSIZE + OVERHEAD;
    else
	asize = DSIZE * ((size + (OVERHEAD) + (DSIZE-1)) / DSIZE);
    
    /* Search the free list for a fit */
    if ((bp = find_fit(asize)) != NULL) {
	place(bp, asize);
    /* start next find_fit search at next block, this one is already allocated */
    next_fit_ptr = NEXT_BLKP(bp); 
	return bp;
    }

    /* No fit found. Get more memory and place the block */
    extendsize = MAX(asize,CHUNKSIZE);
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL)
	return NULL;
    place(bp, asize);
    next_fit_ptr = NEXT_BLKP(bp);
    return bp;
} 
/* $end mmmalloc */

/* 
 * mm_free - Free a block 
 */
/* $begin mmfree */
void mm_free(void *bp)
{
    uint32_t size = GET_SIZE(HDRP(bp));

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    coalesce(bp);

/* unused utilization optimizations, worse throughput */
/*    freed_blks++;
    if (freed_blks > 400) {
        next_fit_ptr = coalesce(bp); 
    }
    else {
        coalesce(bp);
        char *new_bp = coalesce(bp);
        if (GET_SIZE(HDRP(new_bp)) >= 4072)
           global_bfree = new_bp; 
    }
*/
}

/* $end mmfree */

/*
 * mm_realloc - naive implementation of mm_realloc
 */
void *mm_realloc(void *ptr, size_t size)
{
    void *newp;
    size_t copySize;

    if ((newp = mm_malloc(size)) == NULL) {
	printf("ERROR: mm_malloc failed in mm_realloc\n");
	exit(1);
    }
    copySize = GET_SIZE(HDRP(ptr));
    if (size < copySize)
      copySize = size;
    memcpy(newp, ptr, copySize);
    mm_free(ptr);
    return newp;
}

/* 
 * mm_checkheap - Check the heap for consistency 
 */
void mm_checkheap(int verbose) 
{
    char *bp = heap_listp;

    if (verbose)
	printf("Heap (%p):\n", heap_listp);

    if ((GET_SIZE(HDRP(heap_listp)) != DSIZE) || !GET_ALLOC(HDRP(heap_listp)))
	printf("Bad prologue header\n");
    checkblock(heap_listp);

    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
	if (verbose) 
	    printblock(bp);
	checkblock(bp);
    // if (global_bfree && GET_ALLOC(HDRP(global_bfree)))
    // printf("global_bfree allocated. Error.\n");
    }
     
    if (verbose)
	printblock(bp);
    if ((GET_SIZE(HDRP(bp)) != 0) || !(GET_ALLOC(HDRP(bp))))
	printf("Bad epilogue header\n");
}

/* 
 * extend_heap - Extend heap with free block and return its block pointer
 */
/* $begin mmextendheap */
static void *extend_heap(size_t words) 
{
    char *bp;
    uint32_t size;
	
    /* Allocate an even number of words to maintain alignment */
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;
    if ((bp = mem_sbrk(size)) == (void *)-1) 
	return NULL;

    /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(bp), PACK(size, 0));         /* free block header */
    PUT(FTRP(bp), PACK(size, 0));         /* free block footer */
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* new epilogue header */

    /* Coalesce if the previous block was free */
    return coalesce(bp);
}
/* $end mmextendheap */

/* 
 * place - Place block of asize bytes at start of free block bp 
 *         and split if remainder would be at least minimum block size
 */
/* $begin mmplace */
/* $begin mmplace-proto */
static void place(void *bp, size_t asize)
/* $end mmplace-proto */
{

    uint32_t csize = GET_SIZE(HDRP(bp));   

    if ((csize - asize) >= (DSIZE + OVERHEAD)) { 
	PUT(HDRP(bp), PACK(asize, 1));
	PUT(FTRP(bp), PACK(asize, 1));
	bp = NEXT_BLKP(bp);
	PUT(HDRP(bp), PACK(csize-asize, 0));
	PUT(FTRP(bp), PACK(csize-asize, 0));
    }
    else { 
    PUT(HDRP(bp), PACK(csize, 1));
	PUT(FTRP(bp), PACK(csize, 1));
    }

}
/* $end mmplace */

/* 
 * find_fit - Find a fit for a block with asize bytes 
 */
static void *find_fit(size_t asize)
{ 
/*  NEXT FIT IMPLEMENTATION */
   
     char *bp = next_fit_ptr;

// unused global_bfree optimization 
/*    if ((global_bfree) && (!GET_ALLOC(HDRP(global_bfree))) && (asize <= GET_SIZE(HDRP(global_bfree)))) {
         char *free = global_bfree;
         global_bfree = NULL;
         return free;
    }
*/  
  
    /* starting at next_fit_ptr, search for free block of at least asize */
    for (; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
    
    if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) {
      	 next_fit_ptr = bp;  
		 return bp;
		}
    }

/* did not find a block, so set next_fit_ptr to beginning of heap and return */
 next_fit_ptr = heap_listp;
 return NULL;    


/* utilization optimization: wrap around to beginning of heap & keep searching
 * enormous decrease in throughput */
/*
	// did not find free block starting at next_fit_ptr 
	bp = heap_listp;
    
//    if (freed_blks <= 375)
//        return extend_heap(CHUNKSIZE);

//    if (((size_t)(mem_heap_hi() - (void *)next_fit_ptr) / 8) >= (mem_heapsize() / 10))
//        return extend_heap(CHUNKSIZE);        
 
	void *end_point = next_fit_ptr;
	for (; bp < end_point; bp = NEXT_BLKP(bp)) {

		if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) {
			next_fit_ptr = bp;
//            if (freed_blks % 2 == 0)
//                 freed_blks--;  
			return bp;
		}
          
	}

   return NULL; // no fit 
*/
}

/*
 * coalesce - boundary tag coalescing. Return ptr to coalesced block
 */
static void *coalesce(void *bp) 
{
    uint32_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    uint32_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    uint32_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && next_alloc) {            /* Case 1 */
	return bp;
    }

    else if (prev_alloc && !next_alloc) {      /* Case 2 */
	size += GET_SIZE(HDRP(NEXT_BLKP(bp)));

//   char *next = NEXT_BLKP(bp);
    
	PUT(HDRP(bp), PACK(size, 0));
	PUT(FTRP(bp), PACK(size, 0));

// if (global_bfree == next)
//   global_bfree = bp;

    }

    else if (!prev_alloc && next_alloc) {      /* Case 3 */
	size += GET_SIZE(HDRP(PREV_BLKP(bp)));

	PUT(FTRP(bp), PACK(size, 0));
	PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
	bp = PREV_BLKP(bp);
    
   }

    else {                                     /* Case 4 */

	size += GET_SIZE(HDRP(PREV_BLKP(bp))) + 
	 GET_SIZE(FTRP(NEXT_BLKP(bp)));

//   char *next = NEXT_BLKP(bp);

	PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
	PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
	bp = PREV_BLKP(bp);

//   if (next == global_bfree)
//     global_bfree = bp;
	
    }

/* good chance of having large freed block, so set nfp to coalesced block */
    next_fit_ptr = bp;
    return bp;
}


static void printblock(void *bp) 
{
    uint32_t hsize, halloc, fsize, falloc;

    hsize = GET_SIZE(HDRP(bp));
    halloc = GET_ALLOC(HDRP(bp));  
    fsize = GET_SIZE(FTRP(bp));
    falloc = GET_ALLOC(FTRP(bp));  
    
    if (hsize == 0) {
	printf("%p: EOL\n", bp);
	return;
    }

    printf("%p: header: [%d:%c] footer: [%d:%c]\n", bp, 
	   hsize, (halloc ? 'a' : 'f'), 
	   fsize, (falloc ? 'a' : 'f')); 
}

static void checkblock(void *bp) 
{
    if ((uint32_t)bp % 8)
	printf("Error: %p is not doubleword aligned\n", bp);
    if (GET(HDRP(bp)) != GET(FTRP(bp)))
	printf("Error: header does not match footer\n");
}


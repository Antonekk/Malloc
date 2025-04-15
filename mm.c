/*
 * Author:  Antoni Strasz 339096
 * Algorithm : Segregated explicit list
 * Placement policy : LIFO (gave better results than FIFO)
 * Search : Best fit within bucket (after testing, this option gave the best
 * results)
 *
 * Buckets : From MINBLOCK, by *2
 *
 * Buckets and chunks sizes were chosen to be opt for given traces, and seem to
 * produce the best results
 *
 * Blocks structure :
 *
 *  Allocated Block :
 *  [Block size | used][payload][padding][Block size | used]
 *
 *  Free Block :
 *  [Block size | used][prev ptr][next ptr][payload][Block size | used] -> Min
 * Block minsize = header(4) + footer(4) + prev(8) + next(8) = 24 ->(Allign) 32
 *
 * Source code structure inspired by implicit list implementation from CSAPP
 * Other sources :
 *  https://moss.cs.iit.edu/cs351/slides/slides-malloc.pdf
 *  https://gee.cs.oswego.edu/dl/html/malloc.html
 */
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdbool.h>
#include <stdint.h>
#include <stddef.h>
#include <unistd.h>

#include "mm.h"
#include "memlib.h"

/* If you want debugging output, use the following macro.  When you hand
 * in, remove the #define DEBUG line. */
//#define DEBUG
#ifdef DEBUG
#define debug(...) printf(__VA_ARGS__)
#else
#define debug(...)
#endif

/* do not change the following! */
#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#endif /* def DRIVER */

// Comment this line to change to first fit
// After testing, best fit seems to perform better overall
#define BESTFIT

/*
  Define debugging output for Phisical and Logical Representation
*/
#define PDEBUG
#define LDEBUG

/*
  Basic Macros and definitions
  Basics form CSAPP
  Implementation specific by me

*/

static size_t round_up(size_t size) {
  return (size + ALIGNMENT - 1) & -ALIGNMENT; //-ALIGMENT = ~(ALIGMENT - 1)
}

typedef uint32_t word_t; // let word be 4 byte chunk

typedef enum {
  FREE = 0, /* Block is free */
  USED = 1, /* Block is used */
} bt_flags;

#define WSIZE 4                  // word size
#define DWSIZE 8                 // double word size
#define MINBLOCK (2 * ALIGNMENT) // min block size

#define HEADER_SIZE WSIZE    // size of header
#define FOOTER_SIZE WSIZE    // size of footer
#define METADATA_SIZE DWSIZE // size of header and footer

#define BUCKETS 16         // Number of buckets
#define MIN_BUCKET_SIZE 64 // Limit for block size in first bucket
#define GETBUCKETPTR(id)                                                       \
  ((char *)segregated_fits +                                                   \
   (sizeof(void *) * (id))) // Get pointer to bin of given id

// Blocks -> 0 : 64 | 65 : 128 | 129 : 256 | ...
// Simple search for test purposes, (could be optimised using builtins)
static inline size_t get_bucket_id(size_t size) {
  int s = MIN_BUCKET_SIZE;
  for (int i = 0; i < BUCKETS; i++) {
    if (size <= s)
      return i;
    s *= 2;
  }
  return BUCKETS - 1;
}

#define MAX(a, b) ((a) > (b) ? (a) : (b))

// Pack both size and allocation information into word
#define PACK(size, alloc) ((size) | (alloc))

// Get/Put data form/to pointer p
#define GET(p) (*(word_t *)(p))
#define PUT(p, x) (*(word_t *)(p) = (x))

// Get size and alloc state from block
#define GET_SIZE(p) ((GET(p)) & ~0x7)
#define GET_ALLOC(p) ((GET(p)) & 0x1)
#define GET_PAYLOAD_SIZE(p) (GET_SIZE(p) - DWSIZE) // Subtract metadata

// Get pointer to header/footer (cast to char in order to sub bytes)
#define HDPTR(p) ((char *)(p)-WSIZE)
#define FTPTR(p)                                                               \
  ((char *)(p) + GET_SIZE(HDPTR(p)) -                                          \
   DWSIZE) // subtract double to skip next footer

// Get pointers to logical predecesor and succesor
#define PRED(p) (p)
#define SUCC(p) ((char *)(p) + sizeof(void *))

// Manage logical pointers
#define GETPTR(p) (*((void **)(p)))
#define PUTPTR(p, x) (*((void **)(p)) = (x))

// Get physical next and previous blocks
#define GET_NEXTBLCK(p) ((char *)(p) + GET_SIZE(HDPTR(p)))
#define GET_PREVBLCK(p) ((char *)(p)-GET_SIZE(((char *)(p)-DWSIZE)))

// Smallest heap extention unit, 64 seems to perform best
#define CHUNK (64)

// wrapper for mem_sbrk
static void *wsbrk(size_t size) {
  void *ptr = mem_sbrk(size);
  if (ptr == (void *)-1) {
    printf("sbrk error");
    return NULL;
  }
  return ptr;
}

/*
  Bucket maniputaion
*/

static void explicit_push(void *bp);
static void explicit_remove(void *bp);

/*
Global variables
*/

// pointer to seg list structure
static void *segregated_fits;

// Points to first block in physical representation
static void *heap_start;

/*
  Merge free blocks with bp
  Invariant : bp already on freelist
*/
static void *coalesce(void *bp) {

  // check if prev and next blocks are free or allocated
  size_t prev_alloc = GET_ALLOC(HDPTR(GET_PREVBLCK(bp)));
  size_t next_alloc = GET_ALLOC(HDPTR(GET_NEXTBLCK(bp)));

  // get current block size
  size_t size = GET_SIZE(HDPTR(bp));

  // Case 1, both prev and next are allocated -> No coalesce neededs
  if (prev_alloc && next_alloc) {
    return bp;
  }

  // In every case, current free block will be removed
  explicit_remove(bp);

  // Case 2, prev is allocated and next is free
  if (prev_alloc && !next_alloc) {
    size += GET_SIZE(HDPTR(GET_NEXTBLCK(bp))); // update block size

    // Fix free list
    explicit_remove(GET_NEXTBLCK(bp));

    // Set metadata
    PUT(HDPTR(bp), PACK(size, FREE));
    PUT(FTPTR(bp), PACK(size, FREE));
  }
  // Case 3, prev is free and next is allocated
  else if (!prev_alloc && next_alloc) {
    size += GET_SIZE(HDPTR(GET_PREVBLCK(bp))); // update block size

    // Fix free list
    explicit_remove(GET_PREVBLCK(bp));

    // Set metadata
    PUT(FTPTR(bp), PACK(size, FREE));
    PUT(HDPTR(GET_PREVBLCK(bp)), PACK(size, FREE));

    // get to prevblock payload start
    bp = GET_PREVBLCK(bp);
  }
  // Case 4, both prev and next are free
  else {
    size +=
      GET_SIZE(HDPTR(GET_PREVBLCK(bp))) +
      GET_SIZE(HDPTR(GET_NEXTBLCK(bp))); // get new size by adding prev and next

    // Fix free list
    explicit_remove(GET_NEXTBLCK(bp));
    explicit_remove(GET_PREVBLCK(bp));

    // Set metadata (header of prev and footer of next)
    PUT(HDPTR(GET_PREVBLCK(bp)), PACK(size, FREE));
    PUT(FTPTR(GET_NEXTBLCK(bp)), PACK(size, FREE));

    // get to prevblock payload start
    bp = GET_PREVBLCK(bp);
  }

  // Add newly created coalesed block to explicit list
  explicit_push(bp);

  return bp;
}

/*
  Extend heap by size bytes, add empty block to list
*/
static void *extend_heap(size_t size) {

  char *bp;

  // Round up to 16 and extend heap
  size = round_up(size);
  bp = wsbrk(size);
  if (!bp)
    return NULL;

  PUT(HDPTR(bp), PACK(size, FREE)); // Set header
  PUT(FTPTR(bp), PACK(size, FREE)); // Set footer

  PUT(HDPTR(GET_NEXTBLCK(bp)), PACK(0, USED)); // Add Epilogue block

  // add bp to free list to preserve invariant
  explicit_push(bp);

  // coalesce if previous block is free
  return coalesce(bp);
}

/*
 * mm_init - Called when a new trace starts.
 */
int mm_init(void) {

  // allocate segregated fits buckets
  segregated_fits = wsbrk(round_up(BUCKETS * sizeof(void *)));
  if (!segregated_fits)
    return -1;

  // Init every bucket
  void *bucket;
  for (size_t i = 0; i < BUCKETS; i++) {
    bucket = GETBUCKETPTR(i);
    PUTPTR(bucket, NULL);
  }

  // Prologue block will never be freed -> doesn't need full 32B as free block
  // does
  word_t prologue_length = ALIGNMENT;

  // Set aligment for first block (offset of 4B for header)
  heap_start = wsbrk(ALIGNMENT - WSIZE);
  if (!heap_start)
    return -1;

  // Get mem for sentinels
  heap_start = wsbrk(prologue_length + WSIZE); // Prologue and Epilogue Block
  if (!heap_start)
    return -1;

  // Set initial sentinel blocks
  PUT(heap_start, PACK(prologue_length, USED)); // Header for Prologue Block
  memset(heap_start + (1 * WSIZE), 0, DWSIZE);  // Set padding to aligment
  PUT(heap_start + (3 * WSIZE),
      PACK(prologue_length, USED));             // Footer for Prologue Block
  PUT(heap_start + (4 * WSIZE), PACK(0, USED)); // Epilogue block

  // Set heap start
  heap_start += WSIZE;

  // Extend heap by first chunk size
  void *fb;
  if ((fb = extend_heap(CHUNK)) == NULL)
    return -1;

  return 0;
}

/*
  Find block in explicit list
  Implementing basic first fit and best fit
*/
static void *find_fit(size_t asize) {

/*
  First Fit
  Traverse explicit list to find first fitting block
*/
#ifndef BESTFIT

  for (size_t bucket_id = get_bucket_id(asize); bucket_id < BUCKETS;
       bucket_id++) {

    for (void *bucket = GETPTR(GETBUCKETPTR(bucket_id)); bucket != NULL;
         bucket = GETPTR(SUCC(bucket))) {
      if (GET_ALLOC(HDPTR(bucket)) == FREE &&
          GET_SIZE(HDPTR(bucket)) >= asize) {
        return bucket;
      }
    }
  }

  return NULL;

#else
  /*
    Best Fit within bucket, if not a single block found in given bucket move to
    the next one
  */
  void *fit;
  for (size_t bucket_id = get_bucket_id(asize); bucket_id < BUCKETS;
       bucket_id++) {
    fit = NULL;
    for (void *bucket = GETPTR(GETBUCKETPTR(bucket_id)); bucket != NULL;
         bucket = GETPTR(SUCC(bucket))) {
      if (GET_ALLOC(HDPTR(bucket)) == FREE &&
          GET_SIZE(HDPTR(bucket)) >= asize) {
        if (fit == NULL || GET_SIZE(HDPTR(bucket)) < GET_SIZE(HDPTR(fit)))
          fit = bucket;
      }
    }
    if (fit != NULL)
      break;
  }

  return fit;

#endif
}

/*
  Add block given by bp pointer to bucket structure
*/
static void explicit_push(void *bp) {

  // Should never enter if asserts fail
  assert(bp != NULL);

  // Get pointer to bucket
  size_t bucket_id = get_bucket_id(GET_SIZE(HDPTR(bp)));
  void *bucket = GETBUCKETPTR(bucket_id);
  void *explicit_list = GETPTR(bucket);

  // Case 1 : explicit list is already empty -> set first element
  if (explicit_list == NULL) {
    PUTPTR(SUCC(bp), NULL); // set succ for bp to null
    PUTPTR(PRED(bp), NULL); // set pred for bp to null
  } else {                  // Case 2 : Push bp as new head

    PUTPTR(PRED(explicit_list), bp); // pred for previous start
    PUTPTR(SUCC(bp), explicit_list); // set succ for new start
    PUTPTR(PRED(bp), NULL);          // set pred for succ to null
  }

  // Swap pointer to new head
  PUTPTR(bucket, bp);
}

/*
  Remove free block given by bp from bucket structure
*/
static void explicit_remove(void *bp) {

  // Should never enter if asserts fail
  assert(bp != NULL);

  // Get pointer to bucket
  size_t bucket_id = get_bucket_id(GET_SIZE(HDPTR(bp)));
  void *bucket = GETBUCKETPTR(bucket_id);
  void *explicit_list = GETPTR(bucket);
  assert(GETPTR(bucket) != NULL);

  // If bp is the only remaining block in list
  if ((GETPTR(PRED(explicit_list)) == NULL) &&
      (GETPTR(SUCC(explicit_list)) == NULL)) {
    PUTPTR(bucket, NULL);
  }

  // Check if bp current list head
  if (explicit_list == bp) {
    PUTPTR(bucket, GETPTR(SUCC(explicit_list)));
    return;
  } else if (GETPTR(PRED(bp)) != NULL) { // if pred is not null
    PUTPTR(SUCC(GETPTR(PRED(bp))), GETPTR(SUCC(bp)));
  }

  if (GETPTR(SUCC(bp)) != NULL)
    PUTPTR(PRED(GETPTR(SUCC(bp))), GETPTR(PRED(bp)));
}

/*

If possible, split block given by pointer by, rest becomes new free block (and
is pushed to bucket structure)
*/
static void split_and_place(void *bp, size_t asize, size_t bsize) {

  if ((bsize - asize) >= MINBLOCK) {
    size_t remaining = (bsize - asize);

    PUT(HDPTR(bp), PACK(asize, USED));
    PUT(FTPTR(bp), PACK(asize, USED));

    // Set bp pointer to remaining free part
    bp = GET_NEXTBLCK(bp);

    // Set Header and Footer data
    PUT(HDPTR(bp), PACK(remaining, FREE));
    PUT(FTPTR(bp), PACK(remaining, FREE));

    // Push rest to free list
    explicit_push(bp);

    coalesce(bp);

  } else { // Set as used
    PUT(HDPTR(bp), PACK(bsize, USED));
    PUT(FTPTR(bp), PACK(bsize, USED));
  }
}

/*
  Place word in bucket explicit list at given by bp free block
  Split block in nessesary
*/
static void place(void *bp, size_t asize) {

  // Should never enter place if block given by bp is illegible for placement
  assert(GET_ALLOC(HDPTR(bp)) != USED);
  assert(GET_SIZE(HDPTR(bp)) >= asize);

  // Get size of bp block
  size_t bsize = GET_SIZE(HDPTR(bp));

  // Remove current free block from list
  explicit_remove(bp);

  // Split if enough remaining space
  split_and_place(bp, asize, bsize);
}

/*
 * malloc - Allocate a block by incrementing the brk pointer.
 *      First, search for available block
 *      If block can't be found, extend heap
 */
void *malloc(size_t size) {

  // user expected size plus metadata size
  size = round_up(size + HEADER_SIZE + FOOTER_SIZE);
  size = size >= MINBLOCK ? size : MINBLOCK;

  // payload pointer
  char *bp;

  // if appropriate placement exists, place block and return
  if ((bp = find_fit(size)) != NULL) {
    place(bp, size);
    return bp;
  }

  // extend heap by appropriate size, and place block
  size_t heap_extend = MAX(size, CHUNK);
  if ((bp = extend_heap(heap_extend)) == NULL)
    return NULL;

  place(bp, size);
  return bp;
}

/*
 * free - free pointer given by ptr
 */
void free(void *ptr) {

  if (ptr == NULL)
    return;

  // get block size
  size_t size = GET_SIZE(HDPTR(ptr));

  // Set header and footer metadata to free
  PUT(HDPTR(ptr), PACK(size, FREE));
  PUT(FTPTR(ptr), PACK(size, FREE));

  // Add newly freed block to explicit list
  explicit_push(ptr);

  // merge free blocks if needed
  coalesce(ptr);
}

/*
 * realloc - Change the size of the block
    if new size is lower than old, shring and potentialy split block
    id size is higher, check for possible merge, if not possible malloc new
 memory
 **/
void *realloc(void *old_ptr, size_t size) {
  /* If size == 0 then this is just free, and we return NULL. */
  if (size == 0) {
    free(old_ptr);
    return NULL;
  }

  /* If old_ptr is NULL, then this is just malloc. */
  if (!old_ptr)
    return malloc(size);

  size_t current_block_size = GET_SIZE(HDPTR(old_ptr));

  // Round size, and check if it's bigger than MINBLOCK size
  size_t new_block_size = round_up(size + HEADER_SIZE + FOOTER_SIZE);
  new_block_size = new_block_size >= MINBLOCK ? new_block_size : MINBLOCK;

  if (current_block_size ==
      new_block_size) { // if sizes are the same, just return pointer
    return old_ptr;
  } else if (new_block_size <
             current_block_size) { // new size is smaller than current, split
                                   // block (if possible) and add remaining to
                                   // free list
    split_and_place(old_ptr, new_block_size, current_block_size);
    return old_ptr;
  } else { // New size is bigger than current

    // Check size after merging with neighbours
    size_t merge_size = current_block_size;
    if (GET_ALLOC(HDPTR(GET_NEXTBLCK(old_ptr))) == FREE) {
      merge_size += GET_SIZE(HDPTR(GET_NEXTBLCK(old_ptr)));
    }

    if (merge_size >= new_block_size) { // Enough space after merge -> coalesce

      // Fix free list
      explicit_remove(GET_NEXTBLCK(old_ptr));

      // Set metadata
      PUT(HDPTR(old_ptr), PACK(merge_size, FREE));
      PUT(FTPTR(old_ptr), PACK(merge_size, FREE));

      split_and_place(old_ptr, new_block_size, merge_size);

      return old_ptr;
    } else { // Worst case, malloc new memory, and move data
      void *new_ptr = malloc(new_block_size);

      memcpy(new_ptr, old_ptr,
             (current_block_size - HEADER_SIZE - FOOTER_SIZE));
      free(old_ptr);
      return new_ptr;
    }
  }
}

/*
 * calloc - Allocate the block and set it to zero.
 */
void *calloc(size_t nmemb, size_t size) {
  size_t bytes = nmemb * size;
  void *new_ptr = malloc(bytes);

  /* If malloc() fails, skip zeroing out the memory. */
  if (new_ptr)
    memset(new_ptr, 0, bytes);

  return new_ptr;
}

/*

Displays blocks in human readable format
Used for debuging
Define DEBUG to use
*/
static void print_block(void *block, size_t block_count) {

#ifdef DEBUG

  size_t block_size, alloc_status, payload, block_size_f, alloc_status_f;

  block_size = GET_SIZE(HDPTR(block));
  alloc_status = GET_ALLOC(HDPTR(block));

  printf("%ld : [H: %ld | %ld]", block_count, block_size, alloc_status);

  if (block_size != 0) {
    payload = block_size - HEADER_SIZE - FOOTER_SIZE;
    block_size_f = GET_SIZE(FTPTR(block));
    alloc_status_f = GET_ALLOC(FTPTR(block));

    printf("[P: %p | %ld][F: %ld | %ld]", block, payload, block_size_f,
           alloc_status_f);
  }

#endif
}

/*
 * Prints phyical and logical structure if debug options defined

 Tests if:
  - Free block count on physical and logical representation is the same
  - Each block marked as free is on the list of all free blocks
  - Every free block doesn't have free neighbor
  - Is every payload alligned
 */
void mm_checkheap(int verbose) {

// Heap checks for physical representation
#ifdef DEBUG
  printf(
    "=========================== CHEACKHEAP ===========================\n\n\n");
#endif

  int physical_block_count = 0;
  int physical_free_count = 0;

  for (void *current = heap_start; GET_SIZE(HDPTR(current)) != 0;
       current = GET_NEXTBLCK(current)) {

#ifdef PDEBUG
    print_block(current, physical_block_count);
    printf("\n");
#endif

    size_t curr_alloc = GET_ALLOC(HDPTR(current));
    size_t next_alloc = GET_ALLOC(HDPTR(GET_NEXTBLCK(current)));
    if (curr_alloc == FREE && next_alloc == FREE) {
      printf("Error : Free blocks next to each other");
    }

    physical_block_count++;
    if (curr_alloc == FREE) {
      physical_free_count++;
    }
  }

#ifdef LDEBUG
  printf("\n------------------------ BUCKETS -------------------------\n");
#endif

  int logical_block_count = 0;
  void *bucket;
  for (size_t i = 0; i < BUCKETS; i++) {
    bucket = GETBUCKETPTR(i);

#ifdef LDEBUG
    printf("%p : [P: %p] === ", bucket, GETPTR(bucket));
#endif

    int count = 0;
    for (void *current = GETPTR(bucket); current != NULL;
         current = GETPTR(SUCC(current))) {
      count++;
      logical_block_count++;

#ifdef LDEBUG
      print_block(current, 0);
      printf(" -> ");
#endif

      if ((size_t)current % 16 != 0) {
        printf("Error : Alligment error\n");
        exit(-1);
      }
      // If allocated block is found on free lists -> Error
      if (GET_ALLOC(HDPTR(current))) {
        printf("Error : Allocated block on free list\n");
        exit(-1);
      }
    }
    printf("%d", count);
    printf("\n");
  }

  if (physical_free_count != logical_block_count) {
    printf("Error: Some blocks are missing from bucket list");
    exit(-1);
  }
}
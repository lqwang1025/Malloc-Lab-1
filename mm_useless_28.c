/*
 * mm.c -  Simple allocator based on implicit free lists,
 *         first fit placement, and boundary tag coalescing.
 *
 * Each block has header and footer of the form:
 *
 *      63       32   31        1   0
 *      --------------------------------
 *     |   unused   | block_size | a/f |
 *      --------------------------------
 *
 * a/f is 1 iff the block is allocated. The list has the following form:
 *
 * begin                                       end
 * heap                                       heap
 *  ----------------------------------------------
 * | hdr(8:a) | zero or more usr blks | hdr(0:a) |
 *  ----------------------------------------------
 * | prologue |                       | epilogue |
 * | block    |                       | block    |
 *
 * The allocated prologue and epilogue blocks are overhead that
 * eliminate edge conditions during coalescing.
 */
#include "memlib.h"
#include "mm.h"
#include <assert.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

/* Your info */
team_t team = {
    /* First and last name */
    "Sneha Raghuram",
    /* UID */
    "605510159",
    /* Custom message (16 chars) */
    "hello",
};

//CHANGES IN THIS FILE: made changes in coalesce, block -24

typedef struct {
    uint32_t allocated : 1;
    uint32_t block_size : 31;
    uint32_t _;
} header_t;

typedef header_t footer_t;

typedef struct {
    uint32_t allocated : 1;
    uint32_t block_size : 31;
    uint32_t _;
    struct{
    //union {  
        struct {
            struct block_t* next;
            struct block_t* prev;
        };
        int payload[0]; 
    } body;
} block_t;

/* This enum can be used to set the allocated bit in the block */
enum block_state { FREE,
                   ALLOC };

#define CHUNKSIZE (1 << 16) /* initial heap size (bytes) */
#define OVERHEAD (sizeof(header_t) + sizeof(footer_t) + 16)

/* overhead of the header and footer of an allocated block */
#define MIN_BLOCK_SIZE (32) /* the minimum block size needed to keep in a freelist (header + footer + next pointer + prev pointer) */

/* Global variables */
static block_t *prologue; /* pointer to first block */
static block_t *epilogue_global; /* pointer to first block */
//static size_t split_size_global; /* global splitsize*/

/* function prototypes for internal helper routines */
static block_t *extend_heap(size_t words);
static block_t *place(block_t *block, size_t asize);
static block_t *find_fit(size_t asize);
static block_t *coalesce(block_t *block);
static footer_t *get_footer(block_t *block);
static void printblock(block_t *block);
static void checkblock(block_t *block);
static void debug_explicit_list(int depth, int verbose);
static void check_if_block_is_freed(block_t *block);

static uint32_t global_counter = 0;
static void debug_explicit_list(int depth, int verbose) {
  global_counter++;
  printf("\nDEBUG EXPLICIT LIST: %d\n", global_counter);

  if (prologue->body.next == NULL) {
    printf("0 elements.\n");
    return;
  }

  int f_len = 0;
  int b_len = 0;

  // Traverse forward.
  block_t *forward = prologue;
  int f_idx = 0;

  for (; f_idx < depth; f_idx++) {
    if (forward->body.next == NULL) {
     
        printf("%p (%d bytes) TAIL\n", forward, forward->block_size);
        f_len++;
        printf("  Forward traversal: %d elements.\n", f_len);
        
      break;
    }

    if (verbose) printf("%p (%d bytes) -> ", forward, forward->block_size);
    forward = forward->body.next;
    f_len++;
  }

  if (f_idx == depth) {
    printf("\nWARNING: Reached forward depth limit.\n");
  }

  // Traverse backwards.
  block_t *backward = forward;
  int b_idx = 0;

  for (; b_idx < depth; b_idx++) {
    if (backward->body.prev == NULL) {
      printf("%p (%d bytes) HEAD\n", backward, backward->block_size);
      b_len++;
      printf("  Backward traversal: %d elements.\n", b_len);
      break;
    }

    if (verbose) printf("%p (%d bytes) -> ", backward, backward->block_size);
    backward = backward->body.prev;
    b_len++;
  }

  if (b_idx == depth) {
    printf("\nWARNING: Reached backward depth limit.\n");
  }

  if (f_len != b_len) {
    printf("ERROR: length mismatch for forward and backward traversal.\n");
    exit(1);
  } else {
    printf(
        "Validated: equal lengths (%d) for forward and backward traversal.\n",
        f_len);
  }

}

//checks for if freed block exists in free list
static void check_if_block_is_freed(block_t *block)
{
    block_t *b;
    for (b = prologue->body.next ; b != NULL; b = b->body.next)
    {
        footer_t *prev_footer = (void *)b - sizeof(header_t);
        header_t *next_header = (void *)b + b->block_size;

        bool prev_alloc = prev_footer->allocated;
        bool next_alloc = next_header->allocated;

        if (!prev_alloc && ((void*)b - 24) != prologue) printf("Previous block not coalesced!!\n");
        if (!next_alloc) printf("Next block not coalesced!!\n");
        
        if (block == b) 
        {
            if (block->allocated) printf("Block not marked as free!!");
            if (block->block_size != b->block_size) printf("Block sizes don't match!!");
            //printf("Block is in free list \n");
            return;
        }
    }
    printf("Block at address %p not in free list!! \n", block);
}


/*
 * mm_init - Initialize the memory manager
 */
/* $begin mminit */
int mm_init(void) {
    /* create the initial empty heap */
    if ((prologue = mem_sbrk(CHUNKSIZE)) == (void*)-1)
        return -1;
    /* initialize the prologue */
    prologue->allocated = ALLOC;
    prologue->block_size = sizeof(block_t);
    //prologue->block_size = sizeof(header_t);
    /* initialize the first free block */

    block_t *init_block = (void *)prologue + sizeof(block_t);
    //block_t *init_block = (void *)prologue + sizeof(header_t);
    init_block->allocated = FREE;
    init_block->block_size = CHUNKSIZE - OVERHEAD - 16; //because epilogue has previous and next pointers
    footer_t *init_footer = get_footer(init_block);
    init_footer->allocated = FREE;
    init_footer->block_size = init_block->block_size;
    /* initialize the epilogue - block size 0 will be used as a terminating condition */
    block_t *epilogue = (void *)init_block + init_block->block_size;
    epilogue->allocated = ALLOC;
    epilogue->block_size = 0;

    //updating pointers
    prologue->body.prev = NULL;
    prologue->body.next = init_block;//add to free list
    init_block->body.next = epilogue; //end of freelist
    init_block->body.prev = prologue; //add to free list
    epilogue->body.prev = init_block;
    epilogue->body.next = NULL;

    epilogue_global = epilogue;
    //printf("Heap checker AFTER MM_INIT \n");
    //mm_checkheap(1);
    return 0;
}
/* $end mminit */

/*
 * mm_malloc - Allocate a block with at least size bytes of payload
 */
/* $begin mmmalloc */
void *mm_malloc(size_t size) {

    //printf("Heap checker BEFORE MM_MALLOC \n");
    //mm_checkheap(1);

    uint32_t asize;       /* adjusted block size */
    uint32_t extendsize;  /* amount to extend heap if no fit */
    uint32_t extendwords; /* number of words to extend heap if no fit */
    block_t *block;

    /* Ignore spurious requests */
    if (size == 0)
        return NULL;

    /* Adjust block size to include overhead and alignment reqs. */
    size += OVERHEAD;

    asize = ((size + 7) >> 3) << 3; /* align to multiple of 8 */
    
    if (asize < MIN_BLOCK_SIZE) {
        asize = MIN_BLOCK_SIZE;
    }

    /* Search the free list for a fit */
    if ((block = find_fit(asize)) != NULL) {
        block_t* b = place(block, asize);
        return b->body.payload;
    }

    /* No fit found. Get more memory and place the block */
    extendsize = (asize > CHUNKSIZE) // extend by the larger of the two
                     ? asize
                     : CHUNKSIZE;
    extendwords = extendsize >> 3; // extendsize/8
    if ((block = extend_heap(extendwords)) != NULL) {
        
        block_t* b = place(block, asize);
        return b->body.payload;
    }
    /* no more memory :( */
    return NULL;
}
/* $end mmmalloc */

/*
 * mm_free - Free a block
 */
/* $begin mmfree */
void mm_free(void *payload) {

    //printf("Heap checker BEFORE MM_FREE \n");
    //mm_checkheap(1);

    //size of header - 16 bytes for pointer
    block_t *block = payload - sizeof(header_t) - sizeof(block->body.next) - sizeof(block->body.prev);
    block->allocated = FREE;
    footer_t *footer = get_footer(block);
    footer->allocated = FREE;

    if(block->block_size - OVERHEAD <= 100){
        block_t *n = prologue->body.next;
        prologue->body.next = block;
        block->body.prev = prologue;
        block->body.next = n;
        n->body.prev = block;
    } else {
        block_t *n = epilogue_global->body.prev;
        epilogue_global->body.prev = block;
        block->body.next = epilogue_global;
        block->body.prev = n;
        n->body.next = block;
    }
    //updating pointers

    //printf("Heap checker AFTER MM_FREE \n");
    //mm_checkheap(1);
    coalesce(block);

}

/* $end mmfree */

/*
 * mm_realloc - naive implementation of mm_realloc
 * NO NEED TO CHANGE THIS CODE!
 */
void *mm_realloc(void *ptr, size_t size) {
    void *newp;
    size_t copySize;

    if ((newp = mm_malloc(size)) == NULL) {
        //printf("ERROR: mm_malloc failed in mm_realloc\n");
        exit(1);
    }
    block_t* block = ptr - sizeof(header_t);
    copySize = block->block_size;
    if (size < copySize)
        copySize = size;
    memcpy(newp, ptr, copySize);
    mm_free(ptr);
    return newp;
}

/*
 * mm_checkheap - Check the heap for consistency
 */
void mm_checkheap(int verbose) {

    block_t *block = prologue;

    if (verbose)
        printf("Heap (%p):\n", prologue);

    //changing sizeof prologue from header_t to block_t
    if (block->block_size != sizeof(block_t) || !block->allocated)
        //printf("Bad prologue header\n");
    checkblock(prologue);

    /* iterate through the heap (both free and allocated blocks will be present) */
    for (block = (void*)prologue + prologue->block_size; block->block_size > 0; block = (void *)block + block->block_size) {
        if (verbose)
            printblock(block);
        checkblock(block);
    }

    if (verbose)
        printblock(block);
    if (block->block_size != 0 || !block->allocated)
        printf("Bad epilogue header\n");
}

/* The remaining routines are internal helper routines */

/*
 * extend_heap - Extend heap with free block and return its block pointer
 */
/* $begin mmextendheap */
static block_t *extend_heap(size_t words) {

    //printf("Heap checker BEFORE EXTENDHEAP \n");
    //mm_checkheap(1);

    //old code
    block_t *block;
    uint32_t size;
    size = words << 3; // words*8
    if (size == 0 || (block = mem_sbrk(size)) == (void *)-1)
        return NULL;
    /* The newly acquired region will start directly after the epilogue block */ 
    /* Initialize free block header/footer and the new epilogue header */

    /* use old epilogue as new free block header */
    //block = (void *)block - sizeof(header_t);
    
    //epilogue is actually sizeof(block_t)
    
    block = (void *)block - sizeof(block_t);
    block->allocated = FREE;
    block->block_size = size;
    /* free block footer */
    footer_t *block_footer = get_footer(block);
    block_footer->allocated = FREE;
    block_footer->block_size = block->block_size;
    /* new epilogue header - has changed to block_t
    header_t *new_epilogue = (void *)block_footer + sizeof(header_t); */
    block_t *new_epilogue = (void *)block_footer + sizeof(header_t);
    new_epilogue->allocated = ALLOC;
    new_epilogue->block_size = 0;

    //update pointers
    //block_t *new_epilogue_block = (void *)new_epilogue;
    block->body.next = new_epilogue;
    new_epilogue->body.prev = block;
    new_epilogue->body.next = NULL;

    epilogue_global = new_epilogue;
     
    /* Coalesce if the previous block was free */
    //printf("Heap checker AFTER EXTENDHEAP \n");
    //mm_checkheap(1);

    //debug_explicit_list(200, 0);
    return coalesce(block);
}
/* $end mmextendheap */

/*
 * place - Place block of asize bytes at start of free block block
 *         and split if remainder would be at least minimum block size
 */
/* $begin mmplace */
static block_t *place(block_t *block, size_t asize) {

    size_t split_size = block->block_size - asize;

    //printf("Heap checker BEFORE PLACE \n");
    //mm_checkheap(1);
    //printf("after checkheap, trying to place a block of size: %zu \n",asize);
    
    if (split_size >= MIN_BLOCK_SIZE) {

        if (asize - OVERHEAD <= 100) {
        //printf("splitting and split_size is: %zu \n", split_size);

        /* split the block by updating the header and marking it allocated */
        block->block_size = asize; 
        block->allocated = ALLOC;

        /* set footer of allocated block*/
        footer_t *footer = get_footer(block);
        footer->block_size = asize;
        footer->allocated = ALLOC;

        /* update the header of the new free block */
        block_t *new_block = (void *)block + block->block_size;
        new_block->block_size = split_size;
        new_block->allocated = FREE;

        /* update the footer of the new free block */
        footer_t *new_footer = get_footer(new_block);
        new_footer->block_size = split_size;
        new_footer->allocated = FREE;

        block_t *p = block->body.prev;
        block_t *t = block->body.next;
        new_block->body.prev = p;
        new_block->body.next = t;
        p->body.next = new_block;
        t->body.prev = new_block;
            
        return block;

        }
        else
        {
            footer_t *footer = get_footer(block); //update footer
            footer->block_size = asize;
            footer->allocated = ALLOC;
            block_t *b = (void*)footer - footer->block_size + sizeof(header_t); //find header
            b->block_size = asize; //update header
            b->allocated = ALLOC;
            
            //creating new block at the beginning
            block->block_size = split_size;
            block->allocated = FREE; //already marked free 
            footer = get_footer(block);
            footer->block_size = split_size;
            footer->allocated = FREE;

            //make pointers point to new block
            //prev and next pointer already points to correct place

            return b;
        }

    } 
    else {

        //printf("not splitting \n");

        /* splitting the block will cause a splinter so we just include it in the allocated block */
        block->allocated = ALLOC;
        footer_t *footer = get_footer(block);
        footer->allocated = ALLOC;

        //updating pointers
        block_t *p = block->body.prev;
        block_t *t = block->body.next;
        p->body.next = t;
        t->body.prev = p;

        return block;
    }

    //printf("Heap checker AFTER PLACE \n");
    //mm_checkheap(1);
}
/* $end mmplace */

/*
 * find_fit - Find a fit for a block with asize bytes
 */
static block_t *find_fit(size_t asize) {
    /* first fit search */
    block_t *b;

    //printf("Heap checker BEFORE FINDFIT \n");
    //mm_checkheap(1);

    if ((asize - OVERHEAD) <= 100)
    {
        for (b = prologue->body.next; b->body.next != NULL /* epilogue */; b = b->body.next )
        {
            //printblock(b);
            if (!b->allocated && asize <= b->block_size) {
                //printf("Heap checker AFTER FINDFIT \n");
                //printf("found free block at address: %p \n", b);
                //mm_checkheap(1);
                return b;
            }
        
        }
    }
    else
    {
        for (b = epilogue_global->body.prev; b->body.prev != NULL /* prologue */; b = b->body.prev )
        {
            //printblock(b);
            if (!b->allocated && asize <= b->block_size) {
                //printf("Heap checker AFTER FINDFIT \n");
                //printf("found free block at address: %p \n", b);
                //mm_checkheap(1);
                return b;
            }
        
        }
    }
    return NULL; /* no fit */
}

/*
 * coalesce - boundary tag coalescing. Return ptr to coalesced block
 */
static block_t *coalesce(block_t *block) {

    //calling checkheap
    //printf("Heap checker BEFORE COALESCE \n");
    //mm_checkheap(1);

    footer_t *prev_footer = (void *)block - sizeof(header_t);
    header_t *next_header = (void *)block + block->block_size;

    bool prev_alloc = prev_footer->allocated;
    bool next_alloc = next_header->allocated;

    if ((void*)block - 24 == prologue) prev_alloc = 1; //prologue does not have a footer 

    if (prev_alloc && next_alloc) { /* Case 1s */
        /* no coalesceing */
        //printf("Case 1\n");
        //no update pointers
        //check_if_block_is_freed(block); 
        return block;
    }

    else if (prev_alloc && !next_alloc) { /* Case 2 */

        //printf("Case 2\n");
        /* Update header of current block to include next block's size */
        block->block_size += next_header->block_size;
        /* Update footer of next block to reflect new size */
        footer_t *next_footer = get_footer(block);
        next_footer->block_size = block->block_size;

        //casting
        block_t *next_block = (void*)next_header;

        //updating pointers
        block_t *p = next_block->body.prev; 
        block_t *t = next_block->body.next;
        p->body.next = t;
        t->body.prev = p;

    }

    else if (!prev_alloc && next_alloc) { /* Case 3 */
        //printf("Case 3\n");
        /* Update header of prev block to include current block's size */
        block_t *prev_block = (void *)prev_footer - prev_footer->block_size + sizeof(header_t);
        prev_block->block_size += block->block_size;
        /* Update footer of current block to reflect new size */
        footer_t *footer = get_footer(prev_block);
        footer->block_size = prev_block->block_size;
       
        //updating pointers
        block_t *p = block->body.prev;
        block_t *t = block->body.next;
        p->body.next = t;
        t->body.prev = p;

        block = prev_block;
    }

    else { /* Case 4 */
        //printf("Case 4\n");
        /* Update header of prev block to include current and next block's size */
        block_t *prev_block = (void *)prev_footer - prev_footer->block_size + sizeof(header_t);
        prev_block->block_size += block->block_size + next_header->block_size;
        /* Update footer of next block to reflect new size */
        footer_t *next_footer = get_footer(prev_block);
        next_footer->block_size = prev_block->block_size;
        //block = prev_block;

        //casting
        block_t *next_block = (void*)next_header;

        //updating pointers
        block_t *p = block->body.prev;
        block_t *t = block->body.next;
        p->body.next = t;
        t->body.prev = p;

        block_t *p1 = next_block->body.prev; 
        block_t *t1 = next_block->body.next;
        p1->body.next = t1;
        t1->body.prev = p1;

        block = prev_block;
    }
    //printf("Heap checker AFTER COALESCE \n");
    //mm_checkheap(1);

    //mm_checkheap(1);
    //check_if_block_is_freed(block); 
    return block;
}

static footer_t* get_footer(block_t *block) {
    return (void*)block + block->block_size - sizeof(footer_t);
}

static void printblock(block_t *block) {
    uint32_t hsize, halloc, fsize, falloc;

    hsize = block->block_size;
    halloc = block->allocated;
    footer_t *footer = get_footer(block);
    fsize = footer->block_size;
    falloc = footer->allocated;

    if (hsize == 0) {
        printf("%p: EOL\n", block);
        return;
    }

    printf("%p: header: [%d:%c] footer: [%d:%c] next: %p \n", block, hsize,
           (halloc ? 'a' : 'f'), fsize, (falloc ? 'a' : 'f'), block->body.next);
}

static void checkblock(block_t *block) {
    if ((uint64_t)block->body.payload % 8) {
        printf("Error: payload for block at %p is not aligned\n", block);
    }
    //changed prologue to block_t so update this
    footer_t *footer = get_footer(block);
    /*
    if (block->block_size != footer->block_size) {
        //printf("Error: header does not match footer\n");
    }
    */
    if ((block->block_size != footer->block_size) && (block != prologue)) {
        printf("Error: header does not match footer\n");
    }
}

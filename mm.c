

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
    union {
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
#define OVERHEAD (sizeof(header_t) + sizeof(footer_t)) /* overhead of the header 
and footer of an allocated block */
#define MIN_BLOCK_SIZE (32) /* the minimum block size needed to keep in a freelist 
(header + footer + next pointer + prev pointer) */
/* Global variables */
static block_t *prologue; /* pointer to first block */
static block_t *epilogue_global; /* pointer to epilogue */
/* function prototypes for internal helper routines */
static block_t *extend_heap(size_t words);
static block_t *place(block_t *block, size_t asize);
static block_t *find_fit(size_t asize);
static block_t *coalesce(block_t *block);
static footer_t *get_footer(block_t *block);
static void printblock(block_t *block);
static void checkblock(block_t *block);
/*
 * mm_init - Initialize the memory manager: prologue, epilogue and first free block
 Prologue is the start of the memory heap but also the start of the free list. It 
has two pointers: prev and next that 
 point to previous and next blocks respectively. Prologue points to the first free 
block on the list (prev points to null).
 Epilogue is the end of the free list but also the end of the memory heap. It also 
has two pointers: prev and next.
 Initial structure of the heap:
 Prologue -> init_block -> Epilogue
 */
/* $begin mminit */
int mm_init(void) {
    /* create the initial empty heap */
    if ((prologue = mem_sbrk(CHUNKSIZE)) == (void*)-1)
        return -1;
    /* initialize the prologue */
    prologue->allocated = ALLOC;
    prologue->block_size = sizeof(block_t);
    /* initialize the first free block */
    block_t *init_block = (void *)prologue + sizeof(block_t);
    init_block->allocated = FREE;
    init_block->block_size = CHUNKSIZE - OVERHEAD - 32; //prologue and epilogue 
have two pointers each
    footer_t *init_footer = get_footer(init_block);
    init_footer->allocated = FREE;
    init_footer->block_size = init_block->block_size;
    /* initialize the epilogue - block size 0 will be used as a terminating 
condition */
    block_t *epilogue = (void *)init_block + init_block->block_size;
    epilogue->allocated = ALLOC;
    epilogue->block_size = 0;
    prologue->body.prev = NULL;
    prologue->body.next = init_block;//add to free list
    init_block->body.next = epilogue; //end of freelist
    init_block->body.prev = prologue; //add to free list
    epilogue->body.prev = init_block;
    epilogue->body.next = NULL;
    epilogue_global = epilogue;
    return 0;
}
/* $end mminit */
/*
 * mm_malloc - Allocate a block with at least size bytes of payload
 mm_malloc recieves the size of the payload and adds the size of header, footer to 
it and aligns it to nearest multiple of 8.
 It searches find_fit for a free block and calls place function accordingly. If 
free block is not available (find_fit returns null), 
 it extends heap and calls find_fit again.
 mm_malloc returns pointer to the start of payload
 */
/* $begin mmmalloc */
void *mm_malloc(size_t size) {
  
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
                     : 6 * CHUNKSIZE;
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
 mm_free frees the block and adds it to the free list according to size.
 If blocksize - OVERHEAD is less than or equal to 100 it places it at the beginning
of free list: prologue -> freed block ->....
 If blocksize - OVERHEAD is more than 100, it places it at the end of the free 
list: ... -> freed block -> epilogue
 */
/* $begin mmfree */
void mm_free(void *payload) {
    //finding the start of the block
    block_t *block = payload - sizeof(header_t);
    block->allocated = FREE;
    footer_t *footer = get_footer(block);
    footer->allocated = FREE;
    //updating pointers
    if(block->block_size - OVERHEAD <= 100){
        //adding to start of free list
        block_t *n = prologue->body.next;
        prologue->body.next = block;
        block->body.prev = prologue;
        block->body.next = n;
        n->body.prev = block;
    } else {
        //adding to end of free list
        block_t *n = epilogue_global->body.prev;
        epilogue_global->body.prev = block;
        block->body.next = epilogue_global;
        block->body.prev = n;
        n->body.next = block;
    }
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
        printf("ERROR: mm_malloc failed in mm_realloc\n");
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
 Prints prologue, and checks if it it's size of blocksize and if it allocated.
 Traverses the entire heap and prints out all the blocks.
 Prints epilogue and checks if it's size if zero and if it is allocated.
 */
void mm_checkheap(int verbose) {
    block_t *block = prologue;
    if (verbose)
        printf("Heap (%p):\n", prologue);
    if (block->block_size != sizeof(block_t) || !block->allocated)
        printf("Bad prologue header\n");
    checkblock(prologue);
    /* iterate through the heap (both free and allocated blocks will be present) */
    for (block = (void*)prologue+prologue->block_size; block->block_size > 0; block
= (void *)block + block->block_size) {
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
 Make the old epilogue head of new free block and coalesce
 Find new epilogue which is at the end of the heap 
 Update pointers of new free blcok to point to new epilogue 
 */
/* $begin mmextendheap */
static block_t *extend_heap(size_t words) {
    //if (debug_mode) printf("extend_heap: %i\n", words);
    block_t *block;
    uint32_t size;
    size = words << 3; // words*8
    if (size == 0 || (block = mem_sbrk(size)) == (void *)-1)
        return NULL;
    /* The newly acquired region will start directly after the epilogue block */ 
    /* Initialize free block header/footer and the new epilogue header */
    /* use old epilogue as new free block header */
    block = (void *)block - sizeof(block_t);
    block->allocated = FREE;
    block->block_size = size;
    /* free block footer */
    footer_t *block_footer = get_footer(block);
    block_footer->allocated = FREE;
    block_footer->block_size = block->block_size;
    /* new epilogue header */
    block_t *new_epilogue = (void *)block_footer + sizeof(header_t);
    new_epilogue->allocated = ALLOC;
    new_epilogue->block_size = 0;
    //update pointers
    block->body.next = new_epilogue;
    new_epilogue->body.prev = block;
    new_epilogue->body.next = NULL;
    epilogue_global = new_epilogue;
    /* Coalesce if the previous block was free */
    return coalesce(block);
}
/* $end mmextendheap */
/*
 * place - 
 Case 1: Leftover space in block after allocating block is greater than or equal to
Minimum Block size
    Case 1a: Payload is less than or equal to 100
        Split the block according to block size such that the first part of free 
block is allocated and the second part is free.
        This way all the smaller block will be at the beginning of the heap.
        Update pointers to include new smaller free block in free list.
    Case 1b: Payload is greater than 100
        Split the block such that the latter part (the latter block_size bytes of 
free block are marked as allocated).
        All larger blocks are placed towards the end of the heap.
        Update pointers to include new larger free block to the free list.
 Case 2: Leftover psace in block is smaller than Minimum block size
    Mark block as allocated
    Update pointers of previous block and next bloxk to point to each other
 */
/* $begin mmplace */
static block_t *place(block_t *block, size_t asize) {
    size_t split_size = block->block_size - asize;
    if (split_size >= MIN_BLOCK_SIZE) {
        if (asize - OVERHEAD <= 100) {
            /* split the block by updating the header and marking it allocated*/
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
            //update pointers to point to new smaller free block
            block_t *p = block->body.prev;
            block_t *t = block->body.next;
            new_block->body.prev = p;
            new_block->body.next = t;
            p->body.next = new_block;
            t->body.prev = new_block;
            return block;
        } else {
            //find footer of free block
            footer_t *footer = get_footer(block); //update footer
            footer->block_size = asize;
            footer->allocated = ALLOC;
            //find header of this new block with updated size thats at the end of 
the free block
            block_t *b = (void*)footer - footer->block_size + sizeof(header_t); 
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
    } else {
        /* splitting the block will cause a splinter so we just include it in the 
allocated block */
        block->allocated = ALLOC;
        footer_t *footer = get_footer(block);
        footer->allocated = ALLOC;
        //updating pointers to make the previous and next free block to point to 
each other
        block_t *p = block->body.prev;
        block_t *t = block->body.next;
        p->body.next = t;
        t->body.prev = p;
        return block;
    }
}
/* $end mmplace */
/*
 * find_fit - Find a fit for a block with asize bytes
 Case 1: payload is less than or equal to 100 
    Start searching from the beginning of the free list 
Case 2: payload is greater than 100
    Start searching from end of free list
 */
static block_t *find_fit(size_t asize) {
    //if (debug_mode) printf("find_fit: %i\n", asize);
    /* first fit search */
    block_t *b;
    if ((asize - OVERHEAD) <= 100) {
        //searching from beginning
        for (b = prologue->body.next; b->body.next != NULL /* epilogue */; b = b-
>body.next ) {
            if (!b->allocated && asize <= b->block_size) {
                return b;
            }
        }
    } else {
        //searching from end
        for (b = epilogue_global->body.prev; b->body.prev != NULL /* prologue */; b
= b->body.prev ) {
            if (!b->allocated && asize <= b->block_size) {
                return b;
            }
        }
    }
    return NULL; /* no fit */
}
/*
 * coalesce - boundary tag coalescing. Return ptr to coalesced block
 The status (free or allocated) of the adjacent blocks are found
 Blocks are coalesced accordingly and pointers are updated.
 */
static block_t *coalesce(block_t *block) {
    footer_t *prev_footer = (void *)block - sizeof(header_t);
    header_t *next_header = (void *)block + block->block_size;
    bool prev_alloc = prev_footer->allocated;
    bool next_alloc = next_header->allocated;
    //prologue does not have a footer so prev_alloc will be always 1 if this block 
is the beginning of heap
    if ((void*)block - 24 == prologue) prev_alloc = 1;
    if (prev_alloc && next_alloc) { /* Case 1 */
        /* no coalesceing */
        return block;
    }
    else if (prev_alloc && !next_alloc) { /* Case 2 */
        /* Update header of current block to include next block's size */
        block->block_size += next_header->block_size;
        /* Update footer of next block to reflect new size */
        footer_t *next_footer = get_footer(block);
        next_footer->block_size = block->block_size;
        //casting
        block_t *next_block = (void*)next_header;
        //updating pointers
        //making blocks pointed to by previous and next pointers of block point to 
each other (*block is already part of free list)
        block_t *p = next_block->body.prev; 
        block_t *t = next_block->body.next;
        p->body.next = t;
        t->body.prev = p;
    }
    else if (!prev_alloc && next_alloc) { /* Case 3 */
        /* Update header of prev block to include current block's size */
        block_t *prev_block = (void *)prev_footer - prev_footer->block_size + 
sizeof(header_t);
        prev_block->block_size += block->block_size;
        /* Update footer of current block to reflect new size */
        footer_t *footer = get_footer(prev_block);
        footer->block_size = prev_block->block_size;
        //updating pointers 
        //making the free blocks pointed to by prev_block next and previous 
pointers point to each other
        block_t *p = block->body.prev;
        block_t *t = block->body.next;
        p->body.next = t;
        t->body.prev = p;
        block = prev_block;
    }
    else { /* Case 4 */
        /* Update header of prev block to include current and next block's size */
        block_t *prev_block = (void *)prev_footer - prev_footer->block_size + 
sizeof(header_t);
        prev_block->block_size += block->block_size + next_header->block_size;
        /* Update footer of next block to reflect new size */
        footer_t *next_footer = get_footer(prev_block);
        next_footer->block_size = prev_block->block_size;
        
        //casting 
        block_t *next_block = (void*)next_header;
        //making the free blocks pointed to by block next and previous pointers 
point to each other
        block_t *p = block->body.prev;
        block_t *t = block->body.next;
        p->body.next = t;
        t->body.prev = p;
        //making the free blocks pointed to by next_block next and previous 
pointers point to each other
        block_t *p1 = next_block->body.prev; 
        block_t *t1 = next_block->body.next;
        p1->body.next = t1;
        t1->body.prev = p1;
        block = prev_block;
    }
    return block;
}
//finding footer of the block 
static footer_t* get_footer(block_t *block) {
    return (void*)block + block->block_size - sizeof(footer_t);
}
//prints address, header and footer of block
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
    printf("%p: header: [%d:%c] footer: [%d:%c] prev: %p next %p\n", block, hsize,
           (halloc ? 'a' : 'f'), fsize, (falloc ? 'a' : 'f'), block->body.prev, 
block->body.next);
}
static void checkblock(block_t *block) {
    if ((uint64_t)block->body.payload % 8) {
        printf("Error: payload for block at %p is not aligned\n", block);
    }
    footer_t *footer = get_footer(block);
    if (block->block_size != footer->block_size && (block != prologue)) {
        printf("Error: header does not match footer\n");
    }
}

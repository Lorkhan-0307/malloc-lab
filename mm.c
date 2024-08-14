/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 * 
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.  A block is pure payload. There are no headers or
 * footers.  Blocks are never coalesced or reused. Realloc is
 * implemented directly using mm_malloc and mm_free.
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "ateam",
    /* First member's full name */
    "Harry Bovik",
    /* First member's email address */
    "bovik@cs.cmu.edu",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)


#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))


/* 가용 리스트 조작을 위한 기본 상수 및 매크로 정의*/
#define WSIZE             4
#define DSIZE             8
// 4096 바이트씩 한번 추가할때마다 공간을 증가시킨다.
#define CHUNKSIZE        (1<<12)

#define MAX(x, y)        (x > y) ? x : y

#define GET(p)          (*(unsigned int *) (p))
#define SET(p, val)     (*(unsigned int *)(p) = (int)(val))

#define GET_SIZE(p)     (GET(p) & ~0x7)
#define GET_ALLOC(p)    (GET(p) & 0x1)

#define PACK(size,alloc) ((size)| (alloc))

#define HDRP(bp)        ((char *)(bp) - WSIZE)
#define FTRP(bp)        ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

#define NEXT_BLKP(bp) ((char*)(bp) + GET_SIZE(((char*)(bp)-WSIZE)))
#define PREV_BLKP(bp) ((char*)(bp) - GET_SIZE(((char*)(bp) - DSIZE)))

static char * heap_list_p;

static char * next_fit_p;

static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t adjusted_size);
static void *place(void *bp, size_t adjusted_size);

/* 
 * mm_init - initialize the malloc package.
 * mm_malloc이나 mm_free 함수를 호출하기 전에 어플리케이션은 mm_init 함수를 호출해서 힙을 초기화해야 한다.
 * 
 */
int mm_init(void)
{
    // WSIZE(블럭) 4칸을 먼저 할당한다. 이것이 불가능할 경우, 취소함.
    if((heap_list_p = mem_sbrk(4*WSIZE)) == (void*)-1) return -1;

    // 먼저, padding 공간을 할당.
    SET(heap_list_p, 0);
    SET(heap_list_p + (1 * WSIZE), PACK(DSIZE, 1)); // prologue header
    SET(heap_list_p + (2 * WSIZE), PACK(DSIZE, 1)); // prologue footer
    SET(heap_list_p + (3 * WSIZE), PACK(0, 1)); // epilogue block header
    heap_list_p += (2*WSIZE); // prologue header와 footer 사이로 포인터를 옮긴다.

    if(extend_heap(CHUNKSIZE/WSIZE) == NULL) return -1;
    next_fit_p = (char *)heap_list_p;
    return 0;
}

static void *extend_heap(size_t words){
    char *bp;
    size_t size;

    size = (words%2) ? (words + 1) * WSIZE : words * WSIZE;

    if((long)(bp = mem_sbrk(size)) == -1) return NULL;

    SET(HDRP(bp), PACK(size, 0));
    SET(FTRP(bp), PACK(size, 0));
    SET(HDRP(NEXT_BLKP(bp)), PACK(0, 1));

    return coalesce(bp);
}

static void *coalesce(void *bp){
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if(prev_alloc && next_alloc){
        next_fit_p = bp;
        next_fit_p = bp;
        return bp;
    }

    if(prev_alloc && !next_alloc){
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        SET(HDRP(bp), PACK(size, 0));
        SET(FTRP(bp), PACK(size, 0));
        next_fit_p = bp;
        return bp;
    }
    if(!prev_alloc && next_alloc){
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        SET(FTRP(bp), PACK(size, 0));
        SET(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
        next_fit_p = bp;
        return bp;
    }
    size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
    SET(HDRP(PREV_BLKP(bp)), PACK(size, 0));
    SET(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
    bp = PREV_BLKP(bp);
    next_fit_p = bp;
    return bp;
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    // 기존 작성되어 있던 malloc 함수.
    // int newsize = ALIGN(size + SIZE_T_SIZE);
    // void *p = mem_sbrk(newsize);
    // if (p == (void *)-1) return NULL;
    // else {
    //     *(size_t *)p = size;
    //     return (void *)((char *)p + SIZE_T_SIZE);
    // }

    if(size == 0) return NULL;

    size_t adjusted_size;
    size_t extend_size;
    char *bp;

    if(size <= DSIZE){
        adjusted_size = 2*DSIZE;
    }
    else{
        adjusted_size = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE);
    }

    if((bp = find_fit(adjusted_size)) != NULL){
        // 알맞은 공간을 찾으면
        place(bp, adjusted_size);
        next_fit_p = bp;
        return bp;
    }

    // 알맞은 공간이 없다면
    extend_size = MAX(adjusted_size, CHUNKSIZE);
    if((bp = extend_heap(extend_size/WSIZE)) == NULL) return NULL;
    
    place(bp, adjusted_size);
    next_fit_p = bp;
    return bp;
}

static void *find_fit(size_t adjusted_size){

    // first fit
    // void *bp;
    // for(bp = heap_list_p; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)){
    //     // ep header == 0
    //     if(!GET_ALLOC(HDRP(bp)) && (adjusted_size <= GET_SIZE(HDRP(bp)))) return bp;
    // }
    // return NULL;


    // next fit

    void *bp = next_fit_p;
    for(bp = NEXT_BLKP(bp); GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)){
        if(!GET_ALLOC(HDRP(bp)) && (adjusted_size <= GET_SIZE(HDRP(bp)))) {
            next_fit_p = bp;
            return bp;
        }
    }

    bp = heap_list_p;

    // for(bp = HDRP(bp); GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)){
    //     if(!GET_ALLOC(HDRP(bp)) && (adjusted_size <= GET_SIZE(HDRP(bp)))) {
    //         next_fit_p = bp;
    //         return bp;
    //     }
    // }

    while(bp < next_fit_p){
        bp = NEXT_BLKP(bp);
        if(!GET_ALLOC(HDRP(bp)) && GET_SIZE(HDRP(bp)) >= adjusted_size){
            next_fit_p = bp;
            return bp;
        }
    }

    return NULL;
}

static void *place(void *bp, size_t adjusted_size){
    size_t block_size = GET_SIZE(HDRP(bp));
    if(((block_size - adjusted_size) >= (2*DSIZE))){
        SET(HDRP(bp), PACK(adjusted_size, 1));
        SET(FTRP(bp), PACK(adjusted_size, 1));
        bp = NEXT_BLKP(bp);
        SET(HDRP(bp), PACK(block_size - adjusted_size, 0));
        SET(FTRP(bp), PACK(block_size - adjusted_size, 0));
    }
    else{
        SET(HDRP(bp), PACK(block_size, 1));
        SET(FTRP(bp), PACK(block_size, 1));
    }
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr)
{
    size_t size = GET_SIZE(HDRP(ptr));
    SET(HDRP(ptr), PACK(size, 0));
    SET(FTRP(ptr), PACK(size, 0));;
    coalesce(ptr);
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    /* 
    void *oldptr = ptr;
    void *newptr;
    size_t copySize;
    
    newptr = mm_malloc(size);
    if (newptr == NULL)
      return NULL;
    copySize = *(size_t *)((char *)oldptr - SIZE_T_SIZE);
    if (size < copySize)
      copySize = size;
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;
    */

   if(size <= 0){ 
        mm_free(ptr);
        return 0;
    }
    if(ptr == NULL){
        return mm_malloc(size); 
    }
    void *newp = mm_malloc(size); 
    if(newp == NULL){
        return 0;
    }
    size_t oldsize = GET_SIZE(HDRP(ptr));
    if(size < oldsize){
    	oldsize = size; 
	}
    memcpy(newp, ptr, oldsize); 
    mm_free(ptr);
    return newp;
}















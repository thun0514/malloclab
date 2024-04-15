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
    "8team",
    /* First member's full name */
    "Harry Bovik",
    /* First member's email address */
    "bovik@cs.cmu.edu",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""};

#define WSIZE 4
#define DSIZE 8
#define CHUNKSIZE (1 << 12)

#define MAX(x, y) ((x) > (y) ? (x) : (y))

#define PACK(size, alloc) ((size) | (alloc))

#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))

#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

#define HDRP(bp) ((char *)(bp)-WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

#define NEXT_BLKP(bp) (((char *)(bp) + GET_SIZE((char *)(bp)-WSIZE)))
#define PREV_BLKP(bp) (((char *)(bp)-GET_SIZE((char *)(bp)-DSIZE)))

// 추가된 선언
/* Given ptr in free list, get next and previous ptr in the list */
#define GET_NEXT_PTR(bp) (*(char **)(bp + WSIZE))
#define GET_PREV_PTR(bp) (*(char **)(bp))

/* Puts pointers in the next and previous elements of free list */
#define SET_NEXT_PTR(bp, qp) (GET_NEXT_PTR(bp) = qp)
#define SET_PREV_PTR(bp, qp) (GET_PREV_PTR(bp) = qp)

static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);
static void *heap_listp;

// 추가된 함수
static void insert_in_free_list(void *bp);
static void remove_from_free_list(void *bp);
static char *free_list_start;

/*
 * mm_init - initialize the malloc package.
 */
int mm_init(void) {
    if ((heap_listp = mem_sbrk(8 * WSIZE)) == (void *)-1)
        return -1;

    PUT(heap_listp, 0);
    PUT(heap_listp + (1 * WSIZE), PACK(2 * DSIZE, 1)); /* Prologue header */
    PUT(heap_listp + (2 * WSIZE), NULL);               /* prev free block pointer 는 null */
    PUT(heap_listp + (3 * WSIZE), NULL);               /* succ free block pointer 는 null */
    PUT(heap_listp + (4 * WSIZE), PACK(2 * DSIZE, 1)); /* Prologue footer */
    PUT(heap_listp + (5 * WSIZE), PACK(0, 1));         /* Epilogue header */

    free_list_start = heap_listp + (2 * WSIZE);

    if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
        return -1;

    return 0;
}

/*
    extend_heap이 사용되는 경우 2가지
        1. 힙이 초기화될 때,
        2. mm_malloc이 적당한 fit을 찾지 못했을 때
*/
static void *extend_heap(size_t words) {
    char *bp;
    size_t size;

    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));

    return coalesce(bp);
}

static void *coalesce(void *bp) {
    // PREV_BLK(bp) == bp: epilogue block을 만났을 때. Extend했을 때 epilogue를 만나는 유일한 경우
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp))) || PREV_BLKP(bp) == bp;
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));
    
    /* case 1 */
    if (prev_alloc && next_alloc) { 
        insert_in_free_list(bp);
        return bp;
    
    /* case 2 */
    } else if (prev_alloc && !next_alloc) {
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        remove_from_free_list(NEXT_BLKP(bp));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    
    /* case 3 */
    } else if (!prev_alloc && next_alloc) {
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        remove_from_free_list(PREV_BLKP(bp));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    
    /* case 4 */
    } else {
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        remove_from_free_list(NEXT_BLKP(bp));
        remove_from_free_list(PREV_BLKP(bp));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    insert_in_free_list(bp);
    return bp;
}

/*
 * mm_free - 공간 할당 해제.
 */
void mm_free(void *bp) {
    if (bp == NULL)
        return;
    size_t size = GET_SIZE(HDRP(bp));
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    coalesce(bp);
}

static void *find_fit(size_t asize) {
    /* First-fit search */
    void *bp;

    for (bp = free_list_start; !GET_ALLOC(HDRP(bp)); bp = GET_NEXT_PTR(bp)) {
        if (asize <= (size_t)GET_SIZE(HDRP(bp))) {
            return bp;
        }
    }
    return NULL;
}

/*
 * place - 할당할 크기를 담을 수 있는 블록을 분할 해줌
 *         분할 해서 뒤에 공간은 가용 공간으로 만들어줌, 내부 단편화를 줄여줌
 */
static void place(void *bp, size_t asize) {
    size_t csize = GET_SIZE(HDRP(bp));

    if ((csize - asize) >= (2 * DSIZE)) {
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        remove_from_free_list(bp);
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize - asize, 0));
        PUT(FTRP(bp), PACK(csize - asize, 0));
        coalesce(bp);
    } else {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
        remove_from_free_list(bp);
    }
}

/*
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size) {
    size_t asize;
    size_t extendsize;
    char *bp;

    /* Ignore spurious requests */
    if (size == 0)
        return NULL;

    if (size <= DSIZE) {
        asize = 2 * DSIZE;
    } else {
        asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);
    }

    if ((bp = find_fit(asize)) != NULL) {
        place(bp, asize);
        return bp;
    }

    extendsize = MAX(asize, CHUNKSIZE);

    if ((bp = extend_heap(extendsize / WSIZE)) == NULL)
        return NULL;

    place(bp, asize);
    return bp;
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size) {
    if ((int)size <= 0) {
        mm_free(ptr);
        return NULL;
    } else {
        size_t old_size = GET_SIZE(HDRP(ptr));
        size_t new_size = size + (2 * WSIZE);

        if (new_size <= old_size) {
            return ptr;
        } else {
            size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(ptr)));
            size_t csize;

            if (!next_alloc && ((csize = old_size + GET_SIZE(HDRP(NEXT_BLKP(ptr))))) >= new_size) {
                remove_from_free_list(NEXT_BLKP(ptr));
                PUT(HDRP(ptr), PACK(csize, 1));
                PUT(FTRP(ptr), PACK(csize, 1));
                return ptr;
            } else {
                void *new_ptr = mm_malloc(new_size);
                place(new_ptr, new_size);
                memcpy(new_ptr, ptr, new_size);
                mm_free(ptr);
                return new_ptr;
            }
        }
    }
}

/* 연결리스트에 추가 */
static void insert_in_free_list(void *bp) {
    SET_NEXT_PTR(bp, free_list_start);
    SET_PREV_PTR(free_list_start, bp);
    SET_PREV_PTR(bp, NULL);
    free_list_start = bp;
}

/* 연결리스트에 제거 */
static void remove_from_free_list(void *bp) {
    /* 다음 블록이 있다면*/
    if (GET_PREV_PTR(bp)) {
        /* 다음 블록의 주소에, 이전 블록의 주소를 넣는다. */
        SET_NEXT_PTR(GET_PREV_PTR(bp), GET_NEXT_PTR(bp));
        /* 다음 블록이 없다면, 즉 자신이 젤 앞 블록이라면 */
    } else {
        /* 이전 노드를 젤 앞 블록으로 만들어준다. */
        free_list_start = GET_NEXT_PTR(bp);
    }
    SET_PREV_PTR(GET_NEXT_PTR(bp), GET_PREV_PTR(bp));
}
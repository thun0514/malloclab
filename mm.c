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

#define HDRP(bp) ((char *)(bp) - WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

#define NEXT_BLKP(bp) (((char *)(bp) + GET_SIZE((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp) (((char *)(bp ) -GET_SIZE((char *)(bp) - DSIZE)))

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

static void insert_in_free_list(void *bp);
static void remove_from_free_list(void *bp);
static char *free_list_start;

/*
 * mm_init - 메모리 할당기를 초기화
 */
int mm_init(void) {
    /* 힙 확장에 필요한 초기 공간을 할당 */
    if ((heap_listp = mem_sbrk(6 * WSIZE)) == (void *)-1)
        return -1;

    /* Prologue header */
    PUT(heap_listp, 0);
    /* Prologue footer */
    PUT(heap_listp + (1 * WSIZE), PACK(2 * DSIZE, 1));
    /* prev free block pointer */
    PUT(heap_listp + (2 * WSIZE), NULL);
    /* succ free block pointer */
    PUT(heap_listp + (3 * WSIZE), NULL);
    /* Epilogue header */
    PUT(heap_listp + (4 * WSIZE), PACK(2 * DSIZE, 1));
    /* Epilogue footer */
    PUT(heap_listp + (5 * WSIZE), PACK(0, 1));

    /* 초기 가용 블록을 가리키는 포인터를 설정 */
    free_list_start = heap_listp + (2 * WSIZE);

    /* 초기 힙 확장 */
    if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
        return -1;

    return 0;
}

/*
 *  extend_heap이 사용되는 경우 2가지
 *    1. 힙이 초기화될 때,
 *    2. mm_malloc이 적당한 fit을 찾지 못했을 때
*/
static void *extend_heap(size_t words) {
     /* 새로운 heap을 확장 */
    char *bp;
    size_t size;

    /* 정렬을 유지하기 위해 짝수 크기로 조정 */
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;

    /* 새 블록의 헤더와 풋터를 설정 */
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));

    /* coalesce를 호출하여 연속된 가용 블록이 있는 경우 병합 요청 */
    return coalesce(bp);
}

static void *coalesce(void *bp) {
    /* 이전 블록과 다음 블록의 할당 여부를 확인 */

    /* 
     * PREV_BLK(bp) == bp: epilogue block을 만났을 때. 
     * Extend했을 때 epilogue를 만나는 유일한 경우
     */
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp))) || PREV_BLKP(bp) == bp;
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));
    
    /* case 1: 전, 후 모두 할당되어 있을 때 */
    if (prev_alloc && next_alloc) { 
        insert_in_free_list(bp);
        return bp;
    
    /* case 2: 전만 할당되어 있고 후는 가용상태 일 때 */
    } else if (prev_alloc && !next_alloc) {
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        remove_from_free_list(NEXT_BLKP(bp));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    
    /* case 3: 전은 가용 상태이고 후만 할당되어 있을 떄 */
    } else if (!prev_alloc && next_alloc) {
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        remove_from_free_list(PREV_BLKP(bp));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    
    /* case 4: 전, 후 모두 가용상태 일 때 */
    } else {
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        remove_from_free_list(NEXT_BLKP(bp));
        remove_from_free_list(PREV_BLKP(bp));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    /* 병합한 블록을 가용 리스트에 삽입 */
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
 * place - 할당할 크기를 담을 수 있는 블록을 분할
 *         분할 해서 뒤에 공간은 가용 공간으로 만들어줌으로서 내부 단편화를 줄임
 */
static void place(void *bp, size_t asize) {
    size_t csize = GET_SIZE(HDRP(bp));

    if ((csize - asize) >= (2 * DSIZE)) {
        /* 새로운 블록을 할당하고 남은 공간을 가용 리스트에 추가 */
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        remove_from_free_list(bp);
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize - asize, 0));
        PUT(FTRP(bp), PACK(csize - asize, 0));
        coalesce(bp);
    } else {
        /* 새로운 블록을 할당 */
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
        remove_from_free_list(bp);
    }
}

/*
 * mm_malloc -  메모리 블록을 할당
 *              brk 포인터를 증가시켜 블록을 할당
 *              항상 할당된 블록의 크기는 정렬된 크기의 배수
 */
void *mm_malloc(size_t size) {
    size_t asize;
    size_t extendsize;
    char *bp;

    /* Ignore spurious requests */
    if (size == 0)
        return NULL;

    /* 요청 크기를 정렬하기 위해 조정 */
    if (size <= DSIZE) {
        asize = 2 * DSIZE;
    } else {
        asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);
    }

    /* 적합한 가용 블록을 찾음 */
    if ((bp = find_fit(asize)) != NULL) {
        place(bp, asize);
        return bp;
    }

    /* 적합한 가용 블록을 찾을 수 없는 경우 힙을 확장 */
    extendsize = MAX(asize, CHUNKSIZE);

    if ((bp = extend_heap(extendsize / WSIZE)) == NULL)
        return NULL;

    place(bp, asize);
    return bp;
}

/*
 * mm_realloc - 메모리 재할당
 */
void *mm_realloc(void *ptr, size_t size) {
    /* 크기가 0보다 작거나 같은 경우 메모리를 해제 */
    if ((int)size <= 0) {
        mm_free(ptr);
        return NULL;
    } else {
        size_t old_size = GET_SIZE(HDRP(ptr));
        size_t new_size = size + (2 * WSIZE);

        /* 새로운 크기가 이전 크기보다 작은 경우 */
        if (new_size <= old_size) {
            return ptr;
        } else {
            size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(ptr)));
            size_t csize;

            /* 다음 블록이 가용 상태이고 충분한 공간이 있는 경우 */
            if (!next_alloc && ((csize = old_size + GET_SIZE(HDRP(NEXT_BLKP(ptr))))) >= new_size) {
                remove_from_free_list(NEXT_BLKP(ptr));
                PUT(HDRP(ptr), PACK(csize, 1));
                PUT(FTRP(ptr), PACK(csize, 1));
                return ptr;
            } else {
                /* 새로운 메모리를 할당하고 데이터를 복사 */
                void *new_ptr = mm_malloc(new_size);
                place(new_ptr, new_size);
                memcpy(new_ptr, ptr, new_size);
                mm_free(ptr);
                return new_ptr;
            }
        }
    }
}

/* 
 * insert_in_free_list - 가용 리스트에 블록 추가
 */ 
static void insert_in_free_list(void *bp) {
    SET_NEXT_PTR(bp, free_list_start);
    SET_PREV_PTR(free_list_start, bp);
    SET_PREV_PTR(bp, NULL);
    free_list_start = bp;
}

/*
 * remove_from_free_list - 가용 리스트에서 블록 제거
 */
static void remove_from_free_list(void *bp) {
    /* 이전 블록이 존재할 경우 */
    if (GET_PREV_PTR(bp)) {
        /* 이전 블록의 다음 블록 포인터를 현재 블록의 다음 블록 포인터로 설정 */
        SET_NEXT_PTR(GET_PREV_PTR(bp), GET_NEXT_PTR(bp));

    /* 이전 블록이 존재하지 않는 경우 */
    } else {
        /* 가용 리스트의 시작 포인터를 현재 블록의 다음 블록 포인터로 설정 */
        free_list_start = GET_NEXT_PTR(bp);
    }
    /* 다음 블록의 이전 포인터를 현재 블록의 이전 블록 포인터로 설정 */
    SET_PREV_PTR(GET_NEXT_PTR(bp), GET_PREV_PTR(bp));
}
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

/*
 * mm.c - 묵시적 가용 리스트(Implicit Free List) 기반 할당기
 *
 * 이 할당기는 CS:APP 교재 9.9.12절을 바탕으로 구현되었습니다.
 * 블록은 헤더와 풋터를 가지며, 경계 태그(Boundary Tag)를 이용해 
 * 상수 시간에 가용 블록을 연결(Coalesce)합니다.
 * 탐색은 First-fit 방식을 사용합니다.
 */
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "memlib.h"
#include "mm.h"

/*********************************************************
 * 팀 정보
 ********************************************************/
team_t team = {
    /* Team name */
    "444 team",
    /* First member's full name */
    "CHOI HYUN JIN",
    /* First member's email address */
    "guswls1478@gmail.com",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};

/* 정렬을 위한 기본 매크로 */
#define ALIGNMENT 8
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)
#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

/* ========================================================== */
/* 가용 리스트 조작을 위한 기본 상수 및 매크로 (그림 9.43) */
/* ========================================================== */
#define WSIZE       4       /* 워드(Word)와 헤더/풋터 크기 (bytes) */
#define DSIZE       8       /* 더블 워드(Double word) 크기 (bytes) */
#define CHUNKSIZE   (1<<12) /* 힙 공간 확장 기본 크기 (4KB) */

#define MAX(x, y) ((x) > (y) ? (x) : (y))

/* 크기와 할당 비트를 통합해서 헤더와 풋터에 저장할 값 리턴 */
#define PACK(size, alloc)  ((size) | (alloc))

/* 주소 p에 있는 워드를 읽고 쓰기 */
#define GET(p)       (*(unsigned int *)(p))
#define PUT(p, val)  (*(unsigned int *)(p) = (val))

/* 주소 p에서 블록 크기와 할당 상태를 읽기 */
#define GET_SIZE(p)  (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

/* 블록 포인터 bp가 주어지면, 헤더와 풋터 주소 계산 */
#define HDRP(bp)  ((char *)(bp) - WSIZE)
#define FTRP(bp)  ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* 블록 포인터 bp가 주어지면, 다음/이전 블록의 주소 계산 */
#define NEXT_BLKP(bp)  ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp)  ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))


/* ========================================================== */
/* 전역 변수 및 내부 헬퍼 함수 사전 선언 */
/* ========================================================== */
static char *heap_listp;

static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);


/* ========================================================== */
/* 할당기 핵심 함수 구현 */
/* ========================================================== */

/*
 * mm_init - 할당기를 초기화합니다. (그림 9.44)
 */
int mm_init(void) {
    /* 1. 초기 빈 힙 생성 (4워드 크기) */
    if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *)-1)
        return -1;

    PUT(heap_listp, 0);                            /* 정렬 패딩 */
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1)); /* 프롤로그 헤더 */
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1)); /* 프롤로그 풋터 */
    PUT(heap_listp + (3 * WSIZE), PACK(0, 1));     /* 에필로그 헤더 */
    heap_listp += (2 * WSIZE);                     /* 포인터를 프롤로그 블록으로 이동 */

    /* 2. 빈 힙을 CHUNKSIZE 바이트의 가용 블록으로 확장 */
    if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
        return -1;
    return 0;
}

/*
 * extend_heap - 워드 단위로 요청을 받아 힙을 확장합니다. (그림 9.45)
 */
static void *extend_heap(size_t words) {
    char *bp;
    size_t size;

    /* 정렬을 유지하기 위해 짝수 개수의 워드를 할당 */
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;

    /* 가용 블록의 헤더/풋터와 에필로그 헤더 초기화 */
    PUT(HDRP(bp), PACK(size, 0));         /* 가용 블록 헤더 */
    PUT(FTRP(bp), PACK(size, 0));         /* 가용 블록 풋터 */
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* 새 에필로그 헤더 */

    /* 이전 블록이 가용 상태라면 물리적으로 병합 */
    return coalesce(bp);
}

/*
 * mm_free - 블록 반환 및 경계 태그 연결 (그림 9.46)
 */
void mm_free(void *bp) {
    size_t size = GET_SIZE(HDRP(bp));

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    coalesce(bp);
}

/*
 * coalesce - 인접한 가용 블록들을 하나로 통합합니다. (그림 9.46)
 */
static void *coalesce(void *bp) {
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && next_alloc) {            /* Case 1 */
        return bp;
    }
    else if (prev_alloc && !next_alloc) {      /* Case 2 */
        size += GET_SIZE(HDRP(NEXT_BLKP(bp))); 
        PUT(HDRP(bp), PACK(size, 0));          
        PUT(FTRP(bp), PACK(size, 0));          
    }
    else if (!prev_alloc && next_alloc) {      /* Case 3 */
        size += GET_SIZE(HDRP(PREV_BLKP(bp))); 
        PUT(FTRP(bp), PACK(size, 0));          
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0)); 
        bp = PREV_BLKP(bp);                    
    }
    else {                                     /* Case 4 */
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp))); 
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0)); 
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0)); 
        bp = PREV_BLKP(bp);                    
    }
    return bp;
}

/*
 * mm_malloc - 가용 리스트에서 블록 할당하기 (그림 9.47)
 */
void *mm_malloc(size_t size) {
    size_t asize;      /* 조정된 블록 크기 */
    size_t extendsize; /* 맞는 블록이 없을 때 힙을 확장할 크기 */
    char *bp;

    if (size == 0)
        return NULL;

    /* 오버헤드와 정렬 요구사항을 포함하여 블록 크기 조정 */
    if (size <= DSIZE)
        asize = 2 * DSIZE;
    else
        asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);

    /* 가용 리스트에서 크기가 맞는 블록 검색 */
    if ((bp = find_fit(asize)) != NULL) {
        place(bp, asize);
        return bp;
    }

    /* 맞는 블록을 찾지 못함. 힙을 확장하여 배치 */
    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize / WSIZE)) == NULL)
        return NULL;
    
    place(bp, asize);
    return bp;
}

/*
 * find_fit - First-fit 검색을 수행합니다.
 */
static void *find_fit(size_t asize) {
    void *bp;
    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) {
            return bp;
        }
    }
    return NULL; /* No fit */
}

/*
 * place - 요청한 블록을 가용 블록의 시작 부분에 배치하고, 
 *         나머지가 최소 블록 크기 이상이면 분할합니다.
 */
static void place(void *bp, size_t asize) {
    size_t csize = GET_SIZE(HDRP(bp));

    if ((csize - asize) >= (2 * DSIZE)) {
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize - asize, 0));
        PUT(FTRP(bp), PACK(csize - asize, 0));
    } 
    else {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}

/*
 * mm_realloc - 기존 블록 크기에 맞게 구현된 단순한 realloc
 */
void *mm_realloc(void *ptr, size_t size) {
    void *oldptr = ptr;
    void *newptr;
    size_t copySize;

    if (size == 0) {
        mm_free(ptr);
        return NULL;
    }
    if (ptr == NULL) {
        return mm_malloc(size);
    }

    newptr = mm_malloc(size);
    if (newptr == NULL)
        return NULL;

    /* 이전 블록의 크기를 헤더에서 가져옴 (오버헤드 1워드 제외) */
    copySize = GET_SIZE(HDRP(oldptr)) - WSIZE; 
    if (size < copySize)
        copySize = size;
    
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;
}
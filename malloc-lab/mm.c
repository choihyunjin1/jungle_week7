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
 * mm.c - 분리 가용 리스트(Segregated Free List) 기반 할당기
 */

/*
 * 구현 전환 가이드
 * - 현재 활성 버전: [seg n단계] 라벨이 붙은 코드
 * - explicit 단계 맵:
 *   1단계 MINBLOCKSIZE와 mm_malloc/place의 최소 블록 크기 규칙
 *   2단계 PRED/SUCC, free_listp, mm_init의 free_listp 초기화
 *   3단계 insert_free_block / remove_free_block
 *   4단계 coalesce에서 free list 반영
 *   5단계 place에서 remove/insert 반영
 *   6단계 find_fit이 free_listp만 순회
 * - seg 단계 맵:
 *   1단계 LISTLIMIT
 *   2단계 seg_free_lists[]
 *   3단계 get_list_index()
 *   4단계 insert_free_block의 크기 클래스 삽입
 *   5단계 remove_free_block의 크기 클래스 제거
 *   6단계 mm_init의 seg_free_lists 초기화
 *   7단계 find_fit의 클래스별 탐색
 * - explicit로 되돌릴 때:
 *   1. free list head를 [기존 explicit 코드]의 free_listp로 복원
 *   2. insert_free_block / remove_free_block / find_fit / mm_init 초기화에서
 *      [seg n단계] 코드를 주석 처리하고 [기존 explicit 코드]를 복원
 *   3. coalesce / place는 insert/remove 인터페이스를 그대로 써서 대부분 재사용 가능
 * - implicit로 되돌릴 때:
 *   1. MINBLOCKSIZE, PRED/SUCC, free list 관련 전역/헬퍼를 끄기
 *   2. mm_malloc / find_fit / place / coalesce 안의 [기존 implicit 코드] 블록을 복원
 *   3. explicit/seg용 insert/remove 호출은 함께 제거
 */

/* ========================================================== */
/* [원래 제공된 코드] 기본 헤더 포함                          */
/* ========================================================== */
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "memlib.h"
#include "mm.h"

/* ========================================================== */
/* [원래 제공된 코드] 팀 정보 구조체                          */
/* ========================================================== */
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
    ""};

/* ========================================================== */
/* [원래 제공된 코드] 기본 정렬 관롨 샥수 및 매크로           */
/* ========================================================== */
/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)
#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))


/* ========================================================== */
/* [우리가 추가한 코드] 가용 리스트 조작을 위한 기본 상수 및 매크로 */
/* ========================================================== */
#define WSIZE       4       /* 워드(Word)와 헤더/풋터 크기 (4바이트) */
#define DSIZE       8       /* 더블 워드(Double word) 크기 (8바이트) */
#define CHUNKSIZE   (1<<12) /* 힙 공간 확장 기본 크기 (4KB) */

#define MAX(x, y) ((x) > (y) ? (x) : (y))

/* 크기와 할당 상태 비트를 통합하여 헤더/풋터에 저장할 값 생성 [1] */
#define PACK(size, alloc)  ((size) | (alloc))

/* 주소 p에 있는 워드(4바이트)를 읽거나 씀 [1] */
#define GET(p)       (*(unsigned int *)(p))
#define PUT(p, val)  (*(unsigned int *)(p) = (val))

/* 주소 p(헤더나 풋터)에서 블록의 크기와 할당 상태를 읽어옴 [1] */
#define GET_SIZE(p)  (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

/* 블록 포인터 bp(페이로드의 시작점)를 기준으로 헤더와 풋터 주소 계산 [1] */
#define HDRP(bp)  ((char *)(bp) - WSIZE)
#define FTRP(bp)  ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* 블록 포인터 bp를 기준으로 다음/이전 블록의 페이로드 시작 주소 계산 [1] */
#define NEXT_BLKP(bp)  ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp)  ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

/* [explicit 1단계] free block에 pred/succ를 담기 위한 최소 블록 크기 */
#define MINBLOCKSIZE ALIGN(DSIZE +2 * sizeof(void *))

/* [explicit 2단계] free block payload를 prev/next 포인터 저장 공간으로 사용 */
#define PRED(bp) (*(void **)(bp))
#define SUCC(bp) (*(void **)((char *)(bp) + sizeof(void *)))

/* [seg 1단계] 크기별로 free list를 나누기 위한 클래스 개수 */
#define LISTLIMIT 10

/* [explicit 3단계] free list 조작 함수 원형 */
static void insert_free_block(void *bp);
static void remove_free_block(void *bp);
static int get_list_index(size_t size);


/* ========================================================== */
/* [우리가 추가한 코드] 전역 변수 및 내부 헬퍼 함수 사전 선언 */
/* ========================================================== */
static char *heap_listp; /* 프롤로그 블록을 가리키는 전역 포인터 [2] */

static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);

/* [기존 explicit 2단계 코드]
 * static void *free_listp;
 */
/* [seg 2단계] 크기 클래스별 free list head 배열 */
static void *seg_free_lists[LISTLIMIT];

/* [seg 3단계] 블록 크기를 기준으로 어떤 리스트를 사용할지 계산 */
static int get_list_index(size_t size) {
    int index = 0;

    while ((index < LISTLIMIT - 1) && (size > 1)) {
        size >>= 1;
        index++;
    }
    return index;
}

/* [기존 explicit 3단계 코드]
 * static void insert_free_block(void *bp)
 * {
 *   PRED(bp) = NULL;
 *   SUCC(bp) = free_listp;
 *
 *   if (free_listp != NULL)
 *     PRED(free_listp) = bp;
 *
 *   free_listp = bp;
 * }
 */
/* [seg 4단계] free block을 크기 클래스에 맞는 리스트 맨 앞에 삽입 */
static void insert_free_block(void *bp)
{
    int index = get_list_index(GET_SIZE(HDRP(bp)));
    void *head = seg_free_lists[index];

    PRED(bp) = NULL;
    SUCC(bp) = head;

    if (head != NULL)
        PRED(head) = bp;

    seg_free_lists[index] = bp;
}

/* [기존 explicit 3단계 코드]
 * static void remove_free_block(void *bp)
 * {
 *   if (PRED(bp) != NULL)
 *     SUCC(PRED(bp)) = SUCC(bp);
 *   else
 *     free_listp = SUCC(bp);
 *
 *   if (SUCC(bp) != NULL)
 *     PRED(SUCC(bp)) = PRED(bp);
 *
 *   PRED(bp) = NULL;
 *   SUCC(bp) = NULL;
 * }
 */
/* [seg 5단계] free block을 자신이 속한 크기 클래스 리스트에서 제거 */
static void remove_free_block(void *bp)
{
    int index = get_list_index(GET_SIZE(HDRP(bp)));

    if (PRED(bp) != NULL)
        SUCC(PRED(bp)) = SUCC(bp);
    else
        seg_free_lists[index] = SUCC(bp);

    if (SUCC(bp) != NULL)
        PRED(SUCC(bp)) = PRED(bp);

    PRED(bp) = NULL;
    SUCC(bp) = NULL;
}


/* ========================================================== */
/* [우리가 순정한 코드] mm_init - 할당기 초기화 함수          */
/* (기존의 return 0; 만 있던 코드를 힙 초기화 로직으로 교체)  */
/* ========================================================== */
int mm_init(void) {
    int i;

    /* 1. 초기 빈 힙 생성 (4워드 크기) [2] */
    if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *)-1)
        return -1;

    /* [기존 explicit 2단계 코드] free_listp = NULL; */
    /* [seg 6단계] 모든 크기 클래스의 head를 NULL로 초기화 */
    for (i = 0; i < LISTLIMIT; i++)
        seg_free_lists[i] = NULL;

    PUT(heap_listp, 0);                            /* 정렬 패딩 [2] */
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1)); /* 프롤로그 헤더 [2] */
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1)); /* 프롤로그 풋터 [2] */
    PUT(heap_listp + (3 * WSIZE), PACK(0, 1));     /* 에필로그 헤더 [2] */
    heap_listp += (2 * WSIZE);                     /* 포인터를 프롤로그 블록 데이터로 이동 [2] */

    /* 2. 빈 힙을 CHUNKSIZE 바이트의 가용 블록으로 확장 [2] */
    if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
        return -1;
    return 0;
}


/* ========================================================== */
/* [우리가 추가한 코드] extend_heap - 힙 공간 확장 함수       */
/* ========================================================== */
static void *extend_heap(size_t words) {
    char *bp;
    size_t size;

    /* 1. 정렬을 유지하기 위해 집수 개수의 워드를 할당 */
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;

    /* 2. 가용 블록의 헤더/풋터와 새 에필로그 헤더 초기화 */
    PUT(HDRP(bp), PACK(size, 0));         /* 새 가용 블록 헤더 */
    PUT(FTRP(bp), PACK(size, 0));         /* 새 가용 블록 풋터 */
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* 새 에필로그 헤더 */

    /* 3. 인접한 가용 블록이 있다면 병합(coalesce) [3] */
    return coalesce(bp);
}


/* ========================================================== */
/* [우리가 순정한 코드] mm_free - 블록 반환 및 병합 함수      */
/* (기존의 아무것도 하지 않던 빈 함수를 풋터/헤더 변경 로직으로 교체) */
/* ========================================================== */
void mm_free(void *bp) {
    size_t size = GET_SIZE(HDRP(bp)); /* [4] */

    PUT(HDRP(bp), PACK(size, 0)); /* 헤더의 할당 비트를 0(가용)으로 변경 [4] */
    PUT(FTRP(bp), PACK(size, 0)); /* 풋터의 할당 비트를 0(가용)으로 변경 [4] */
    coalesce(bp);                 /* 인접한 가용 블록과 병합 [4] */
}


/* ========================================================== */
/* [우리가 추가한 코드] coalesce - 경계 태그를 이용한 블록 병합 함수 */
/* ========================================================== */
static void *coalesce(void *bp) {
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp))); /* 이전 블록 할당 여부 */
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp))); /* 다음 블록 할당 여부 */
    size_t size = GET_SIZE(HDRP(bp));                   /* 현재 블록 크기 */

    if (prev_alloc && next_alloc) {            /* Case 1: 앞뒤 모두 할당됨 */
        /* [explicit 4단계, seg 재사용] 기존 implicit 버전: return bp; */
        insert_free_block(bp);
        return bp;
    }
    else if (prev_alloc && !next_alloc) {      /* Case 2: 다음 블록만 가용 */
        /* [기존 implicit 코드]
         * size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
         * PUT(HDRP(bp), PACK(size, 0));
         * PUT(FTRP(bp), PACK(size, 0));
         */
        remove_free_block(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }
    else if (!prev_alloc && next_alloc) {      /* Case 3: 이전 블록만 가용 */
        /* [기존 implicit 코드]
         * size += GET_SIZE(HDRP(PREV_BLKP(bp)));
         * PUT(FTRP(bp), PACK(size, 0));
         * PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
         * bp = PREV_BLKP(bp);
         */
        remove_free_block(PREV_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    else {                                     /* Case 4: 앞뒤 모두 가용 */
        /* [기존 implicit 코드]
         * size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
         * PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
         * PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
         * bp = PREV_BLKP(bp);
         */
        remove_free_block(PREV_BLKP(bp));
        remove_free_block(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    /* [explicit 4단계, seg 재사용] 병합이 끝난 free block을 다시 리스트에 연결 */
    /* 기존 implicit 버전: return bp; */
    insert_free_block(bp);
    return bp;
}


/* ========================================================== */
/* [우리가 수정한 코드] mm_malloc - 블록 할당 함수            */
/* (단순히 brk만 올리던 방식을 가용 리스트 검색 방식으로 교체)*/
/* ========================================================== */
void *mm_malloc(size_t size) {
    size_t asize;      /* 조정된 블록 크기 [3] */
    size_t extendsize; /* 맞는 블록이 없을 때 확장할 크기 [3] */
    char *bp;

    /* 가짜 요청 무시 [3] */
    if (size == 0)
        return NULL;

    /* 오버헤드와 정렬 조건을 포함하여 블록 크기 조정 [3] */
    // if (size <= DSIZE)
    //     asize = 2 * DSIZE;
    // else
    //     asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);

    /* [explicit 1단계, seg 재사용] 최소 free block 크기를 MINBLOCKSIZE로 확장 */
    asize = MAX(ALIGN(size + DSIZE), MINBLOCKSIZE);
    /* 가용 리스트에서 맞는 블록 검색 [3] */
    if ((bp = find_fit(asize)) != NULL) {
        place(bp, asize);
        return bp;
    }

    /* 맞는 블록을 찾지 못하면 힙을 확장하여 배치 [3] */
    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize / WSIZE)) == NULL)
        return NULL;
    
    place(bp, asize);
    return bp;
}


/* ========================================================== */
/* [우리가 추가한 코드] find_fit - First-fit 검색 함수        */
/* ========================================================== */
static void *find_fit(size_t asize) {
    void *bp;
    int index;

    /* [기존 implicit 코드]
     * for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
     *     if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) {
     *         return bp;
     *     }
     * }
     */

    /* [기존 explicit 6단계 코드]
     * for (bp = free_listp; bp != NULL; bp = SUCC(bp)) {
     *     if (asize <= GET_SIZE(HDRP(bp))) {
     *         return bp;
     *     }
     * }
     */

    /* [seg 7단계] 요청 크기에 맞는 클래스부터 위쪽 클래스로 first-fit 탐색 */
    for (index = get_list_index(asize); index < LISTLIMIT; index++) {
        for (bp = seg_free_lists[index]; bp != NULL; bp = SUCC(bp)) {
            if (asize <= GET_SIZE(HDRP(bp))) {
                return bp;
            }
        }
    }
    return NULL; /* 맞는 블록이 없음 [5] */
}


/* ========================================================== */
/* [우리가 추가한 코드] place - 찾은 블록에 데이터를 배치하고 분할 */
/* ========================================================== */
static void place(void *bp, size_t asize) {
    size_t csize = GET_SIZE(HDRP(bp)); /* 현재 가용 블록의 전체 크기 */

    /* [explicit 5단계, seg 재사용] 할당 대상 free block을 리스트에서 제거 */
    remove_free_block(bp);

    /* 분할 후 남은 크기가 최소 블록 크기(16바이트) 이상일 경우 분할 수행 */
   //if ((csize - asize) >= (2 * DSIZE)) { 
    
    /* [explicit 1단계, seg 재사용] 남는 블록이 MINBLOCKSIZE 이상일 때만 분할 */
    if ((csize - asize) >= MINBLOCKSIZE) {
        void *next_bp;

        /* [기존 implicit 코드]
         * PUT(HDRP(bp), PACK(asize, 1));
         * PUT(FTRP(bp), PACK(asize, 1));
         *
         * bp = NEXT_BLKP(bp);
         * PUT(HDRP(bp), PACK(csize - asize, 0));
         * PUT(FTRP(bp), PACK(csize - asize, 0));
         */
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));

        next_bp = NEXT_BLKP(bp);
        PUT(HDRP(next_bp), PACK(csize - asize, 0));
        PUT(FTRP(next_bp), PACK(csize - asize, 0));
        insert_free_block(next_bp);
    } 
    /* 남은 크기가 최소 블록 크기보다 작을 경우 분할 없이 전체 할당 */
    else {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}


/* ========================================================== */
/* [우리가 수정한 코드] mm_realloc - 재할당 함수              */
/* (기존 Naive 구조를 헤더 정보를 읽어오도록 수정)            */
/* ========================================================== */
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

    /* [변경점] 기존 코드는 SIZE_T_SIZE를 뺐으나, 
       우리의 새 할당기는 블록 크기를 헤더(HDRP)에서 가져옴 */
    copySize = GET_SIZE(HDRP(oldptr)) - WSIZE; 
    if (size < copySize)
        copySize = size;
    
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;
}

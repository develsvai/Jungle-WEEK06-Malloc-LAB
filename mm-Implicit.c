/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 *
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.  A block is pure payload. There are no headers or
 * footers.  Blocks are never coalesced or reused. Realloc is
 * implemented directly using mm_malloc and mm_free.
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

/* 기본 상수와 매크로 */
#define ALIGNMENT 8
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)
#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))
#define WSIZE 4             /* 워드 크기 */
#define DSIZE 8             /* 더블 워드 크기 */
#define CHUNKSIZE (1 << 12) /* 초기 확장 힙 크기 */
#define MAX(x, y) ((x) > (y) ? (x) : (y))

/* 헤더와 푸터 조작 */
#define HEADER(size, alloc) ((size) | (alloc))           /* 헤더/푸터에 크기 및 할당 비트 저장 */

#define GET(p) (*(unsigned int *)(p))                  /* 포인터 p에 저장된 값 반환 */
#define PUT(p, val) (*(unsigned int *)(p) = (val))     /* 포인터 p에 값 저장 */
#define GET_SIZE(p) (GET(p) & ~0x7)                    /* 크기만 추출 */
#define GET_ALLOC(p) (GET(p) & 0x1)                    /* 할당 여부 추출 */

/* 블록의 주소 계산 */
#define HDR_ADDR(bp) ((char *)(bp) - WSIZE)                /* 헤더의 주소 */
#define FTR_ADDR(bp) ((char *)(bp) + GET_SIZE(HDR_ADDR(bp)) - DSIZE) /* 푸터의 주소 */
#define NEXT_BLK(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE))) /* 다음 블록 */
#define PREV_BLK(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE))) /* 이전 블록 */
#define GET_SUCC(bp) (*(void **)((char *)(bp) + WSIZE)) // 다음 가용 블록의 주소
#define GET_PRED(bp) (*(void **)(bp))                   // 이전 가용 블록의 주소

//가용 블록 리스트 의 첫번째 블럭 을 가리키는 포인터
static char *heap_listp = NULL;

static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void place(void *bp , size_t asize);

int mm_init(void){
    if((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1) return -1;

    //정렬패딩
    PUT(heap_listp, 0);
    //프롤로그 헤더 추가
    PUT(heap_listp + (1 * WSIZE), HEADER(DSIZE, 1));
    //프롤로그 푸터 추가
    PUT(heap_listp + (2  * WSIZE), HEADER(DSIZE, 1));
    //에필로그 헤더 추가
    PUT(heap_listp + (3  * WSIZE), HEADER(0, 1));
    //힙의 시작 위치를 에필로그 헤더 앞으로 이동
    heap_listp += (2+WSIZE);

    if(extend_heap(CHUNKSIZE /WSIZE) == NULL)
          return -1;
    return 0;
}

//static void *find_fit(size_t asize)
//{
//    void *bp = mem_heap_lo() + 2 * WSIZE; // 첫번째 블록(주소: 힙의 첫 부분 + 8bytes)부터 탐색 시작
//    while (GET_SIZE(HDR_ADDR(bp)) > 0)
//    {
//        if (!GET_ALLOC(HDR_ADDR(bp)) && (asize <= GET_SIZE(HDR_ADDR(bp)))) // 가용 상태이고, 사이즈가 적합하면
//            return bp;                                             // 해당 블록 포인터 리턴
//        bp = NEXT_BLK(bp);                                        // 조건에 맞지 않으면 다음 블록으로 이동해서 탐색을 이어감
//    }
//    return NULL;
//}

static void *find_fit(size_t asize)
{
    void *bp = mem_heap_lo() + 2 * WSIZE; // 첫번째 블록(주소: 힙의 첫 부분 + 8bytes)부터 탐색 시작
    void *best_bp = NULL; // 최적 블록 포인터 초기화
    size_t best_size = 0; // 최적 블록의 크기 초기화

    while (GET_SIZE(HDR_ADDR(bp)) > 0) // 블록의 크기가 0보다 큰 동안 탐색
    {
        size_t block_size = GET_SIZE(HDR_ADDR(bp)); // 현재 블록의 크기 가져오기

        // 가용 상태이고, 요청된 크기보다 크거나 같다면
        if (!GET_ALLOC(HDR_ADDR(bp)) && (asize <= block_size))
        {
            // 첫 번째 적합 블록 또는 현재 블록이 더 작다면
            if (best_bp == NULL || block_size < best_size)
            {
                best_bp = bp; // 최적 블록 업데이트
                best_size = block_size; // 최적 크기 업데이트
            }
        }
        bp = NEXT_BLK(bp); // 다음 블록으로 이동
    }
    return best_bp; // 최적 블록 포인터 리턴 (없으면 NULL)
}


void *mm_malloc(size_t size)
{
    size_t asize;      // 조정된 블록 사이즈
    size_t extendsize; // 확장할 사이즈
    char *bp;

    // 잘못된 요청 분기
    if (size == 0)
        return NULL;

    /* 사이즈 조정 */
    if (size <= DSIZE)     // 8바이트 이하이면
        asize = 2 * DSIZE; // 최소 블록 크기 16바이트 할당 (헤더 4 + 푸터 4 + 저장공간 8)
    else
        asize = DSIZE * ((size + DSIZE + DSIZE - 1) / DSIZE); // 8배수로 올림 처리

    /* 가용 블록 검색 */
    if ((bp = find_fit(asize)) != NULL)
    {
        place(bp, asize); // 할당
        return bp;        // 새로 할당된 블록의 포인터 리턴
    }

    /* 적합한 블록이 없을 경우 힙확장 */
    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize / WSIZE)) == NULL)
        return NULL;
    place(bp, asize);
    return bp;
}

static void place(void *bp, size_t asize)
{
  //
    size_t csize = GET_SIZE(HDR_ADDR(bp)); // 현재 블록의 크기

    if ((csize - asize) >= (2 * DSIZE)) // 차이가 최소 블록 크기 16보다 같거나 크면 분할
    {
        PUT(HDR_ADDR(bp), HEADER(asize, 1)); // 현재 블록에는 필요한 만큼만 할당
        PUT(FTR_ADDR(bp), HEADER(asize, 1));

        PUT(HDR_ADDR(NEXT_BLK(bp)), HEADER((csize - asize), 0)); // 남은 크기를 다음 블록에 할당(가용 블록)
        PUT(FTR_ADDR(NEXT_BLK(bp)), HEADER((csize - asize), 0));
    }
    else
    {
        PUT(HDR_ADDR(bp), HEADER(csize, 1)); // 해당 블록 전부 사용
        PUT(FTR_ADDR(bp), HEADER(csize, 1));
    }
}
static void *extend_heap(size_t words) {
    char *bp;
    size_t size;


    size = (words % 2 ) ? (words + 1) * WSIZE : words * WSIZE;

    if((long)(bp = mem_sbrk(size)) == -1)
      return NULL;

    //프리 블록 헤더
    PUT(HDR_ADDR(bp), HEADER(size,0));
    PUT(FTR_ADDR(bp), HEADER(size,0));
    PUT(HDR_ADDR(NEXT_BLK(bp)), HEADER(0,1));

    return coalesce(bp);
 }
static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTR_ADDR(PREV_BLK(bp))); // 이전 블록 할당 상태
    size_t next_alloc = GET_ALLOC(HDR_ADDR(NEXT_BLK(bp))); // 다음 블록 할당 상태
    size_t size = GET_SIZE(HDR_ADDR(bp));                   // 현재 블록 사이즈

    if (prev_alloc && next_alloc) // 모두 할당된 경우
        return bp;

    else if (prev_alloc && !next_alloc) // 다음 블록만 빈 경우
    {
        size += GET_SIZE(HDR_ADDR(NEXT_BLK(bp)));
        PUT(HDR_ADDR(bp), HEADER(size, 0)); // 현재 블록 헤더 재설정
        PUT(FTR_ADDR(bp), HEADER(size, 0)); // 다음 블록 푸터 재설정 (위에서 헤더를 재설정했으므로, FTRP(bp)는 합쳐질 다음 블록의 푸터가 됨)
    }
    else if (!prev_alloc && next_alloc) // 이전 블록만 빈 경우
    {
        size += GET_SIZE(HDR_ADDR(PREV_BLK(bp)));
        PUT(HDR_ADDR(PREV_BLK(bp)), HEADER(size, 0)); // 이전 블록 헤더 재설정
        PUT(FTR_ADDR(bp), HEADER(size, 0));            // 현재 블록 푸터 재설정
        bp = PREV_BLK(bp);                      // 이전 블록의 시작점으로 포인터 변경
    }
    else // 이전 블록과 다음 블록 모두 빈 경우
    {
        size += GET_SIZE(HDR_ADDR(PREV_BLK(bp))) + GET_SIZE(FTR_ADDR(NEXT_BLK(bp)));
        PUT(HDR_ADDR(PREV_BLK(bp)), HEADER(size, 0)); // 이전 블록 헤더 재설정
        PUT(FTR_ADDR(NEXT_BLK(bp)), HEADER(size, 0)); // 다음 블록 푸터 재설정
        bp = PREV_BLK(bp);                      // 이전 블록의 시작점으로 포인터 변경
    }

    return bp; // 병합된 블록의 포인터 반환
}

void mm_free(void *bp)
{
    size_t size = GET_SIZE(HDR_ADDR(bp));
    PUT(HDR_ADDR(bp), HEADER(size, 0));
    PUT(FTR_ADDR(bp), HEADER(size, 0));
    coalesce(bp);
}

void *mm_realloc(void *ptr, size_t size)
{
    /* 예외 처리 */
    if (ptr == NULL) // 포인터가 NULL인 경우 할당만 수행
        return mm_malloc(size);

    if (size <= 0) // size가 0인 경우 메모리 반환만 수행
    {
        mm_free(ptr);
        return 0;
    }

    /* 새 블록에 할당 */
    void *newptr = mm_malloc(size); // 새로 할당한 블록의 포인터
    if (newptr == NULL)
        return NULL; // 할당 실패

    /* 데이터 복사 */
    size_t copySize = GET_SIZE(HDR_ADDR(ptr)) - DSIZE; // payload만큼 복사
    if (size < copySize)                           // 기존 사이즈가 새 크기보다 더 크면
        copySize = size;                           // size로 크기 변경 (기존 메모리 블록보다 작은 크기에 할당하면, 일부 데이터만 복사)

    memcpy(newptr, ptr, copySize); // 새 블록으로 데이터 복사

    /* 기존 블록 반환 */
    mm_free(ptr);

    return newptr;
}












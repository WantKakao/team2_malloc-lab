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
    ""};

/* Vasic constants and macros */
#define WSIZE 4             // 워드 사이즈
#define DSIZE 8             // 더블워드 사이즈
#define CHUNKSIZE (1 << 10) // 최소 확장 사이즈

#define MAX(x, y) ((x) > (y) ? (x) : (y))

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc) ((size) | (alloc)) // 헤더에 들어갈 내용 (사이즈 + 할당여부)

/* Read and write a word at address p */
#define GET(p) (*(unsigned int *)(p))              // p 주소에 저장된 값
#define PUT(p, val) (*(unsigned int *)(p) = (val)) // p 주소에 저장된 값을 val 로 변경

/* Read the size and allocated fields from header/footer address p */
#define GET_SIZE(p) (GET(p) & ~0x7) // p 주소(헤더 or 푸터)에 저장된 사이즈의 값
#define GET_ALLOC(p) (GET(p) & 0x1) // p 주소(헤더 or 푸터)에 저장된 할당여부의 값

/* Given block ptr bp, compute address of its headr and footer */
// char * 로 캐스팅하는 이유는 4바이트 단위를 빼주기위해서!!
#define HDRP(bp) ((char *)(bp)-WSIZE)                        // bp 주소에 저장된 블록의 헤더
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE) // bp 주소에 저장된 블록의 푸터(헤더 정보 이용)

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp)-WSIZE))) // 현재 블록의 헤더를 참고해 다음블록 주소 반환
#define PREV_BLKP(bp) ((char *)(bp)-GET_SIZE(((char *)(bp)-DSIZE)))   // 이전 블록의 푸터를 참고해 이전블록 주소 반환

/* single word (4) or double word (8) alignment */
/* #define ALIGNMENT 8 // 8바이트로 정렬(더블워드) */

/* rounds up to the nearest multiple of ALIGNMENT */
/* #define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7) */ // ?

/* #define SIZE_T_SIZE (ALIGN(sizeof(size_t))) */ // ?

/* The only global variable is a pointer to the first block */
char *heap_listp; // 힙 시작 블럭의 주소를 가리키는 포인터
char *curr_listp; // 현재 힙 주소를 가리키는 포인터

int mm_init(void);
static void *extend_heap(size_t words);
static void *coalesce(void *bp);
void *mm_malloc(size_t size);
void mm_free(void *ptr);
void *mm_realloc(void *ptr, size_t size);
void *first_fit(size_t asize);
static void place(void *bp, size_t asize);
void *next_fit(size_t asize);
void *best_fit(size_t asize);
void *worst_fit(size_t asize);

/*
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    /* Create the initial empty heap */
    /* sbrk(n) 시 n byte 만큼 확장이 된다!! */
    if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *)-1) // mem_sbrk 성공시 heap_listp 에 힙의 시작 주소 저장 실패시 -1 return
        return -1;
    /* Put alignment padding, prologue header/footer, epilogue header */
    PUT(heap_listp, 0);
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1));
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1));
    PUT(heap_listp + (3 * WSIZE), PACK(0, 1));
    heap_listp += (2 * WSIZE); // 프롤로그 블록의 푸터에 포인터 위치 (프롤로그 블럭의 payload 와 같음), 불변
    curr_listp = heap_listp;   // 현재 힙 주소를 시작 힙 주소로 초기화

    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    if (extend_heap(CHUNKSIZE / WSIZE) == NULL) // CHUNKSIZE 만큼의 힙 확장 실패시 1, 성공시 0 return
        return 1;
    return 0;
}

static void *extend_heap(size_t words) // 힙 확장 실패시 NULL, 성공시 확장 bp 주소 return
{
    char *bp;
    size_t size;

    /* Allocate a padding to maintain alignment */
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE; // size + 패딩
    if ((long)(bp = mem_sbrk(size)) == -1)                    // mem_sbrk 성공시 bp 에 이전 힙의 끝 주소 저장
        return NULL;

    /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(bp), PACK(size, 0));         // 힙 끝의 에필로그 헤더를 블록의 헤더로 변경 (할당 X)
    PUT(FTRP(bp), PACK(size, 0));         // 힙 끝으로 가서 푸터 추가 (할당 X)
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); // 힙 끝을 새로운 에필로그 헤더로 등록 (사이즈 0 할당 O)

    /* Coalesce if the previous block was free */
    return coalesce(bp);
}

static void *coalesce(void *bp) // bp 에 위치한 블럭은 무조건 free 상태, 합쳐진 블록의 주소 bp return
{
    size_t prev_alloc = GET_ALLOC(bp - (DSIZE));        // 이전 블록 푸터를 확인해서 할당여부 체크 (푸터는 bp - DSIZE)
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp))); // 다음 블록 헤더(푸터)를 확인해서 할당여부 체크
    size_t size = GET_SIZE(HDRP(bp));

    /* In order, both allocated, prev allocated, next allocated and both unallocated */
    if (prev_alloc && next_alloc)
        return bp;

    else if (prev_alloc && !next_alloc)
    {
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0)); // 현재 블록 헤더 정보 변경
        PUT(FTRP(bp), PACK(size, 0)); // 위에서 헤더 정보를 바꿨으므로 현재 블록 푸터 위치 갱신됨 (순서 변경시 오작동)
    }

    else if (!prev_alloc && next_alloc)
    {
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));            // 현재 블록 푸터 정보 변경
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0)); // 이전 블록 헤더 정보 변경
        bp = PREV_BLKP(bp);
    }

    else
    {
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0)); // 이전 블록 헤더
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0)); // 다음 블록 푸터
        bp = PREV_BLKP(bp);
    }
    curr_listp = bp;
    return bp;
}

/*
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size) // size 가 0 또는 음수일 시 NULL, 그 외에 빈공간 주소 bp return
{
    size_t asize;      /* adjusted block size */
    size_t extendsize; /* amount to extend heap if no fit */
    char *bp;

    /* Ignore spurious requests */
    if (size <= 0)
        return NULL;

    /* Adjust block size to include overhead and alignment reqs. */
    asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE); // 헤더 푸터 추가 후 DSIZE 단위로 올림

    /* Search the free list for a fit */
    if ((bp = next_fit(asize)) != NULL) // 빈공간 있을시 거기에 할당
    {
        place(bp, asize);
        curr_listp = bp;
        return bp;
    }

    /* No fit found. Get more memory and place the block */
    extendsize = MAX(asize, CHUNKSIZE);                 // 힙 확장 최소단위 = CHUNKSIZE
    if ((bp = extend_heap(extendsize / WSIZE)) == NULL) // extend_heap 안될경우 return
        return NULL;
    place(bp, asize); // extend_heap 시 맨 뒤 빈 블럭의 bp 주소 return
    curr_listp = bp;
    return bp;
}

void *first_fit(size_t asize) // 빈 공간 있을시 bp, 없을시 NULL return
{
    void *bp;

    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) // heap_listp 는 프롤로그 블록의 푸터(payload)를 가리키고 있음
    {
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp))))
            return bp;
    }
    return NULL;
}

/* next_fit 의 포인터는 free 시에 움직여줘야하나? */
void *next_fit(size_t asize) // 빈 공간 있을시 bp, 없을시 NULL return
{
    char *bp = curr_listp;

    for (bp = NEXT_BLKP(bp); GET_SIZE(HDRP(bp)) != 0; bp = NEXT_BLKP(bp))
    {
        if (!GET_ALLOC(HDRP(bp)) && GET_SIZE(HDRP(bp)) >= asize)
            return bp;
    }

    bp = heap_listp;
    while (bp < curr_listp)
    {
        bp = NEXT_BLKP(bp);
        if (!GET_ALLOC(HDRP(bp)) && GET_SIZE(HDRP(bp)) >= asize)
            return bp;
    }

    return NULL;
}

void *best_fit(size_t asize) // 빈 공간 있을시 bp, 없을시 NULL return
{
    void *bp;
    void *temp = NULL;
    size_t csize = (1 << 31);

    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) // heap_listp 는 프롤로그 블록의 푸터(payload)를 가리키고 있음
    {
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp))))
        {
            if (csize > GET_SIZE(HDRP(bp)))
            {
                temp = bp;
                csize = GET_SIZE(HDRP(bp));
            }
        }
    }
    return temp;
}

void *worst_fit(size_t asize) // 빈 공간 있을시 bp, 없을시 NULL return
{
    void *bp;
    void *temp = NULL;
    size_t csize = 0;

    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) // heap_listp 는 프롤로그 블록의 푸터(payload)를 가리키고 있음
    {
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp))))
        {
            if (csize < GET_SIZE(HDRP(bp)))
            {
                temp = bp;
                csize = GET_SIZE(HDRP(bp));
            }
        }
    }
    return temp;
}

static void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp));

    if ((csize - asize) >= (2 * DSIZE)) // 할당 후 남은 블록에 헤더와 푸터를 저장할 만큼의 공간이 있으면 (WSIZE 로 쓰면 payload 못받음)
    {
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize - asize, 0));
        PUT(FTRP(bp), PACK(csize - asize, 0));
    }

    else
    {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp));

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    coalesce(bp);
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *bp, size_t size)
{
    size_t old_size = GET_SIZE(HDRP(bp));
    size_t new_size = size + (2 * WSIZE); // 2*WISE는 헤더와 풋터

    // if (size <= 0)
    // {
    //     mm_free(bp);
    //     return 0;
    // }

    // new_size가 old_size보다 작거나 같으면 기존 블럭 그대로 사용
    if (new_size <= old_size)
        return bp;

    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t current_size = old_size + GET_SIZE(HDRP(NEXT_BLKP(bp)));

    // next block이 가용상태이고 old, next block의 사이즈 합이 new_size보다 크면 그냥 쓰기
    if (!next_alloc && current_size >= new_size)
    {
        PUT(HDRP(bp), PACK(current_size, 1));
        PUT(FTRP(bp), PACK(current_size, 1));
        return bp;
    }
    // prev block ??
    else
    {
        void *new_bp = mm_malloc(new_size); // 왜 new_size ?
        memcpy(new_bp, bp, new_size);
        mm_free(bp);
        return new_bp;
    }

    // void *oldbp = bp;
    // void *newbp;
    // size_t oldsize;

    // oldsize = GET_SIZE(HDRP(oldbp));
    // if (size < oldsize)
    //     oldsize = size;

    // mm_free(oldbp);
    // newbp = mm_malloc(size);

    // memcpy(newbp, oldbp, size);
    // return newbp;
}
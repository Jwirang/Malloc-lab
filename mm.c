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

static void *coalesce(void*);
static void *extend_heap(size_t);
static void place(void*, size_t);
static void *find_fit(size_t);
static void *next_fit(size_t);
static void *best_fit(size_t);
void removeBlock(void*);
void putFreeBlock(void*);


/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "12jo",
    /* First member's full name */
    "NamCheongWoo",
    /* First member's email address */
    "skacjddn7@gmail.com",
    /* Second member's full name (leave blank if none) */
    "BangJiWon",
    /* Second member's email address (leave blank if none) */
    "haha71119@gmail.com"
};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)


#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

#define WSIZE 4 // word and header footer 사이즈를 byte로
#define DSIZE 8 //  double word size를 byte로
#define CHUNKSIZE   (1<<12) // heap을 늘릴 때  얼만큼 늘릴거냐> 4kb 분량

#define MAX(x, y) ((x) > (y) ? (x) : (y)) // x,y 중 큰 값을 가진다.

// size를 pack하고 개별 word 안의 bit를 할당 (size와 alloc을 비트 연산)
#define PACK(size, alloc) ((size) | (alloc)) // alloc : 가용 여부 / size : block size를 의미

// address p위치에 words를 read와 write를 한다.
#define GET(p)  (*(unsigned int *) (p)) // 포인터를 써서 p를 참조한다. 주소와 값(값에는 다른 블록의 주소를 담는다.)을 알 수 있다. 다른 블록을 가리키거나 이동할 때 쓸 수 있다.
#define PUT(p, val) (*(unsigned int *) (p) = (val)) // 블록의 주소를 담는다. 위치를 담아야지 나중에 헤더나 푸터를 읽어서 이동 혹은 연결할 수 있다.

//address p위치로부터 size를 읽고 field를 할당
#define GET_SIZE(p)  (GET(p) & ~0x7) // '~'은 역수니까 11111000이 됨. 비트 연산하면 000 앞에거만 가져올 수 있음. 즉, 헤더에서 블록 size만 가져오겠다.
#define GET_ALLOC(p)    (GET(p) & 0x1) // 00000001이 됨. 헤더에서 가용여부만 가져오겠다.

// given block ptr bp, header와 footer의 주소를 계산
#define HDRP(bp)    ((char *) (bp) - WSIZE) // bp가 어디에있던 상관없이 WSIZE 앞에 위치한다.
#define FTRP(bp)    ((char *) (bp) + GET_SIZE(HDRP(bp)) - DSIZE) // 헤더의 끝 지점부터 GET SIZE(블록의 사이즈)만큼 더한 다음 word를 2번 빼는게(그 뒤 블록의 헤드에서 앞으로 2번) footer의 시작 위치가 된다.

// GIVEN block ptr bp, 이전 블록과 다음 블록의 주소를 계산
#define NEXT_BLKP(bp)   ((char *) (bp) + GET_SIZE(((char *) (bp) - WSIZE))) // 그 다음 블록의 bp 위치로 이동한다.(bp에서 해당 블록의 크기만큼 이동 -> 그 다음 블록의 헤더 뒤로 감)
#define PREV_BLKP(bp)   ((char *) (bp) - GET_SIZE(((char *) (bp) - DSIZE))) // 그 전 블록의 bp 위치로 이동.(이전 블록 footer로 이동하면 그 전 블록의 사이즈를 알 수 있으니 그만큼 그 전으로 이동)

#define PRED_FREEP(bp) (*(void**)(bp))
#define SUCC_FREEP(bp) (*(void**)(bp + WSIZE))

static char *heap_listp;
static char *pointp;
static void *free_listp;
/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    heap_listp = mem_sbrk(24);// 24byte를 늘려주고, 함수의 시작부분을 가리키는 주소를 반환,mem_brk는 끝에 가있음
    if (heap_listp == (void*)-1){
        return -1;
    }
    PUT(heap_listp, 0);
    PUT(heap_listp + WSIZE, PACK(16, 1));
    PUT(heap_listp + (2*WSIZE), NULL);
    PUT(heap_listp + (3*WSIZE), NULL);
    PUT(heap_listp + (4*WSIZE), PACK(16, 1));
    PUT(heap_listp + (5*WSIZE), PACK(0, 1));
    free_listp = heap_listp + DSIZE;

    if (extend_heap(4) == NULL) return -1;

    if (extend_heap(CHUNKSIZE/WSIZE) == NULL) return -1;
    //pointp = (char *)heap_listp;
    return 0;
}

/**
 * 아래와 같은 경우에 호출
 1. 힙이 초기화 될 때
 2. mm_malloc()이 적당한 fit을 찾지 못할때
 정렬을 유지하기 위해 extend_heap()은 요청한 크기를 인접 2워드의 배수(8의 배수)로 반올림 하며,
 그 후에 메모리 시스템으로 부터 추가적인 힙 공간을 요청한다.
*/
static void *extend_heap(size_t words) {
    char *bp;
    size_t size;
    
    // Allocate an even number of words to maintain alignment
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    if (((bp = mem_sbrk(size)) == (void*)-1)) //size를 불러올 수 없으면
        return NULL;

    PUT(HDRP(bp), PACK(size, 0));  
    PUT(FTRP(bp), PACK(size, 0));    
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));

    return coalesce(bp);
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    size_t asize;
    size_t extendsize;
    char *bp;

    if(size <= 0) return NULL;
    if(size <= DSIZE) asize = 2*DSIZE;
    else asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);

    if((bp = find_fit(asize)) != NULL) {
        place(bp, asize);
        //pointp = bp;
        return bp;
    }

    extendsize = MAX(asize, CHUNKSIZE);
    if((bp = extend_heap(extendsize/WSIZE)) == NULL) return NULL;
    
    place(bp, asize);
    //pointp = bp;
    return bp;
}

/**
 * LIFO 방식으로 새로 반환되거나 생성된 가용 블록을 가용리스트 맨 앞에 추가
*/
void putFreeBlock(void *bp) {
    SUCC_FREEP(bp) = free_listp;
    PRED_FREEP(bp) = NULL;
    PRED_FREEP(free_listp) = bp;
    free_listp = bp;
}

/**
 * free list 맨 앞에 프롤로그 블록이 존재
*/
void removeBlock(void *bp) {
    if(bp == free_listp) {
        PRED_FREEP(SUCC_FREEP(bp)) = NULL;
        free_listp = SUCC_FREEP(bp);
    } else {
        SUCC_FREEP(PRED_FREEP(bp)) = SUCC_FREEP(bp);
        PRED_FREEP(SUCC_FREEP(bp)) = PRED_FREEP(bp);
    }
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr)
{
    size_t size = GET_SIZE(HDRP(ptr));

    PUT(HDRP(ptr), PACK(size, 0));
    PUT(FTRP(ptr), PACK(size,  0));
    coalesce(ptr);
}

/**
 * 할당 된 블록을 합치는 함수. 4가지 경우가 있음
*/
static void *coalesce(void *bp) 
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if(prev_alloc && !next_alloc) {
        removeBlock(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    } 
    else if (!prev_alloc && next_alloc) {
        removeBlock(PREV_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        bp = PREV_BLKP(bp);
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    } 
    else if (!prev_alloc && !next_alloc){
        removeBlock(PREV_BLKP(bp));
        removeBlock(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    putFreeBlock(bp);
    //pointp = bp;
    return bp;
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    if(size <= 0){ 
        mm_free(ptr);
        return 0;
    }
    if(ptr == NULL) return mm_malloc(size);
    void *newptr = mm_malloc(size);
    if (newptr == NULL) return 0;
    size_t oldsize = GET_SIZE(HDRP(ptr));
    if (size < oldsize)
      oldsize = size;
    memcpy(newptr, ptr, oldsize);
    mm_free(ptr);
    return newptr;
}

/**
 * 메모리 영역에 메모리 블록을 위치시킴
*/
static void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp));
    removeBlock(bp);

    if ((csize - asize) >= (2 * DSIZE)) 
    {
        PUT(HDRP(bp), PACK(asize, 1)); 
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize - asize, 0)); 
        PUT(FTRP(bp), PACK(csize - asize, 0));
        putFreeBlock(bp);
    }
    else
    {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}

/**
 * 처음부터 검사하여 적합한 메모리 반환
*/
static void *find_fit(size_t asize)
{
    void *bp;
    for (bp = free_listp; GET_ALLOC(HDRP(bp)) != 1; bp = SUCC_FREEP(bp))
    {
        if (GET_SIZE(HDRP(bp)) >= asize) return bp; 
    }

    return NULL;
}

/**
 * 가장 마지막 부터 검사하여 적합한 메모리 반환
*/
static void *next_fit(size_t asize)
{
    char *bp = pointp;

    while (GET_SIZE(HDRP(bp)) != 0) {
        if (!GET_ALLOC(HDRP(bp)) && GET_SIZE(HDRP(bp)) >= asize) {
            pointp = bp;
            return bp;
        }
        bp = NEXT_BLKP(bp);
    }

    bp = heap_listp;
    while (bp < pointp) {
        if (!GET_ALLOC(HDRP(bp)) && GET_SIZE(HDRP(bp)) >= asize) {
            pointp = bp;
            return bp;
        }
        bp = NEXT_BLKP(bp);
    }

    return NULL;
}

/**
 * 처음부터 끝까지 탐색하여 요청된 크기와 가장 근접한 크기의 메모리를 반환
*/
static void *best_fit(size_t asize)
{
    char *bp;
    char *best_bp = NULL;
    size_t min_size = ~0;

    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp))
    {
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp))) && (GET_SIZE(HDRP(bp)) < min_size))
        {
            min_size = GET_SIZE(HDRP(bp));
            best_bp = bp;
        }
    }

    return best_bp;
}
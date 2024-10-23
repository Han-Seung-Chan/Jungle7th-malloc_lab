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
    "team 10",
    /* First member's full name */
    "dongyeop ko",
    /* First member's email address */
    "ds06041@gmail.com",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""};

// /* single word (4) or double word (8) alignment */
// #define ALIGNMENT 8

// /* rounds up to the nearest multiple of ALIGNMENT */
// #define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)

// #define SIZE_T_SIZE (ALIGN(sizeof(size_t)))
static void *extend_heap(size_t words);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);
static void *coalesce(void *bp);

/* 기본 상수 및 매크로 */
/* 기본 size 상수를 정의*/
#define WSIZE 4                           // 워드 크기 (bytes)
#define DSIZE 8                           // 더블 워드 (bytes)
#define CHUNKSIZE (1 << 12)               // 초기 가용 블록과 힙 확장을 위한 기본 크기(1 << 12 는 2의 12승 = 4096-> 약 4kb-> 힙을 늘릴 때 약  4kb 분량을 늘린다. )(bytes)
                                          // 1을 이진수로 표기하면 0000 0000 0000 0001 -> 1 << 12(시프트 연산) -> 0001 0000 0000 0000 -> 2^12
#define MAX(x, y) ((x) > (y) ? (x) : (y)) // 삼항 연산자를 활용해 ? 앞에 있는 조건인 x가 더 크다는 조건이 참이면 왼쪽 표현식 반환(x를 반환), 조건이 참이 아니라면 그 다음 표현식 반환(y 반환)

/*하나의 word에 size(메모리 블록의 크기)와 allocated bit (해당 메모리 블록이 할당되었는지 여부를 확인)를 패킹한다. */
#define PACK(size, alloc) ((size) | (alloc)) // 크기와 할당 비트를 통합해서 헤더와 풋터에 저장할 수 있는 값을 리턴한다.

/*메모리 주소 'p'가 가리키는 위치에서 메모리를 읽거나 쓰기*/
#define GET(p) (*(unsigned int *)(p))              // 인자 p가 참조하는 워드를 읽어서 리턴한다.
#define PUT(p, val) (*(unsigned int *)(p) = (val)) // 인자 p가 가리키는 워드에 val을 저장한다.

/* 주소 'p'에서 사이즈와 할당 여부를 읽는 것은 해당 주소에서 워드를 읽고, 그 값을 해석한다.*/
// 각각 주소 p에 있는 헤더 또는 풋터의 size와 할당 비트를 리턴한다.
#define GET_SIZE(p) (GET(p) & ~0x7) // size만 가져오기
#define GET_ALLOC(p) (GET(p) & 0x1) // 가용여부만 가져오기

/* 주어진 블록 포인터 'bp'로부터 해당 블록의 헤더와 풋터의 주소를 계산한다.*/
// bp는 header와 payload 사이의 경계를 가르키고 있다.
#define HDRP(bp) ((char *)(bp) - WSIZE)                      // 블록 헤더를 가리키는 포인터를 리턴한다.
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE) // 블록 풋터를 가리키는 포인터를 리턴한다.

/* 주어진 블록 포인터 'bp'로부터 다음 블록과 이전 블록의 주소를 계산한다.*/
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE))) // 다음 블록의 포인터 주소를 리턴한다.
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE))) // 이전 블록의 포인터 주소를 리턴한다.

static void *heap_listp = NULL;
static void *last_bp = NULL;

// 할당기(힙) 초기화하기(성공이면 0 아니면 -1을 리턴한다.)
int mm_init(void)
{
    if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *)-1) // mem_sbrk 함수는 memlib.c에서 불러와 사용하고 있다. incur 값이 음수 이거나 mex_heap 범위를 초과하면 -1 return
        return -1;
    PUT(heap_listp, 0);                            // 정렬 요건을 맞추기 위한 1워드(value = 0)(alignment padding)
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1)); // 다음 블록에 크기(DSIZE=8)와 할당 비트(1)를 통합한 값을 넣는다.(prologue header)
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1)); // 다음 블록도 동일(prologue footer)
    PUT(heap_listp + (3 * WSIZE), PACK(0, 1));     // 다음 블록은 epilogue header를 나타내며 크기는 0이고 할당비트는 1이다.
    heap_listp += (2 * WSIZE);                     // 포인터를 prologue header와 prologue footer 사이에 위치 시킨다.

    if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
        return -1;
    return 0;
}

/* 새 가용블록으로 힙 확장하기 */
static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;
    /*만약 words가 홀수라면 정렬을 유지하기 위해 한 블록을 추가하여 짝수 개의 words를 할당할 수 있도록 한다.*/
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    if ((long)(bp = mem_sbrk(size)) == -1) // bp는 mem_sbrk 함수에서 반환한 old_brk를 가지고 있다.
        return NULL;

    /*할당되지 않은 free 상태인 블록의 헤더 / 풋터와 에필로그 헤더를 초기화한다 */
    PUT(HDRP(bp), PACK(size, 0));         // 원래있던 epilogue 블록에 덮어씌여져 새로운 블록의 header가 된다.
    PUT(FTRP(bp), PACK(size, 0));         // 원래있던 epilogue 블록에 덮어씌여져 새로운 블록의 footer가 된다.
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); // 가장 마지막 블록은 새로운 epilogue가 된다.

    return coalesce(bp); // 이전블록과 다음 블록의 가용상태를 체크하고 통합해준다.
}

// bkr 포인터를 증가시켜 블록을 할당한다. 항상 크기가 정렬의 배수인 블록을 할당한다.
void *mm_malloc(size_t size)
{
    size_t asize; // 블록 사이즈 정의
    size_t extendsize;
    char *bp;

    if (size == 0)
        return NULL;

    // 만약 payload에 넣으려고하는 데이터가 2byte라면 header(4byte) + footer(4byte) + payload(2byte) = 10byte 이지만, 더블워드 정렬 조건을 충족시키기 위해서 패딩 6byte를 추가해야한다. 따라서 총 16byte의 블록이 만들어지는데 이 과정을 계산하는 식이 아래 식이다.
    if (size <= DSIZE)     // size가 8바이트 이하일 경우
        asize = 2 * DSIZE; // 헤더(4byte) + 풋터(4byte) + 정렬 조건을 맞춰주기 위한 패딩 바이트 추가 => asize = 최소 16바이트
    else
        asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE); // 블록이 가질 수 있는 크기 중에 최적화된 크기로 재조정

    if ((bp = find_fit(asize)) != NULL) // find_fit을 통해 정상적으로 할당이 되었을 경우
    {
        place(bp, asize); // 메모리 할당
        return bp;
    }
    // 적절한 블록을 찾지 못했을 경우
    extendsize = MAX(asize, CHUNKSIZE);                 // 힙을 확장할 때 적어도 asize 보다 큰 블록을 할당할 수 있도록 한다. asize가 더 작다면 chunksize만큼 공간을 늘리고 asize만큼 남은 부분은 place에서 처리해준다.
    if ((bp = extend_heap(extendsize / WSIZE)) == NULL) // 힙을 정상적으로 늘리지 못했다면 NULL  (bp는 마지막 블록의 )
        return NULL;
    place(bp, asize); // asize만큼 할당하고 남은 공간을 처리한다.

    return bp;
}

/* 적절한 메모리 블록찾기 */
static void *find_fit(size_t asize) // last_bp는 이전에 탐색을 종료한 위치를 기억한다.
{
    void *bp;
    if (last_bp == NULL) // 이전에 탐색한 적이 없을 경우
    {
        last_bp = heap_listp; // 초기 bp값을 last_bp에 저장
    }
    for (bp = last_bp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) // last_bp에서 시작해서 epilogue블록(힙의 끝)에 도달할때까지 순회
    {
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) // 가용상태 블록에 size가 들어갈 수 있는 경우
        {
            last_bp = bp; // last_bp갱신
            return bp;
        }
    }
    for (bp = heap_listp; bp != last_bp; bp = NEXT_BLKP(bp)) // epilogue블록까지 할당가능한 블록을 찾지 못했을 경우, 다시 처음부터 last_bp까지 탐색
    {
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) // 가용상태 블록에 size가 들어갈 수 있는 경우
        {
            last_bp = bp; // last_bp 갱신
            return bp;
        }
    }
    return NULL; // 없을 경우 null 반환
}

/* 메모리 블록의 할당 및 분할 */
static void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp)); // csize = 현재 bp블록의 사이즈 // chunksize보다 asize가 작을경우 -> csize= chunksize

    if ((csize - asize) >= (2 * DSIZE)) // csize와 asize의 차이가 4개 블럭 이상일경우 (헤더와 풋터를 제외하고 데이터를 저장할 수 있는 공간이 두블럭 이상일 때)
    {
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp);                    // 가용블록에 할당이후 다음블록의 포인터로 bp 갱신
        PUT(HDRP(bp), PACK(csize - asize, 0)); // 남은 블록의 size와 할당상태 = 0 으로 갱신
        PUT(FTRP(bp), PACK(csize - asize, 0));
    }
    else // 블록 내의 할당 부분을 제외한 나머지 공간의 크기가 2 * 더블 워드(8byte)보다 작을 경우에는, 그냥 해당 블록의 크기를 그대로 사용한다
    {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}

void *mm_realloc(void *bp, size_t size)
{
    if (bp == NULL) //  만약 bp == NULL 이면, `mm_malloc(size)`과 동일한 동작을 수행한다.
    {
        return mm_malloc(size);
    }

    if (size == 0) // 만약 size가 0 이면, `mm_free(bp)`와 동일한 동작을 수행한다.
    {
        mm_free(bp);
        return;
    }

    void *new_bp = mm_malloc(size);
    if (new_bp == NULL)
    {
        return NULL;
    }
    size_t csize = GET_SIZE(HDRP(bp));
    if (size < csize) // 재할당 요청에 들어온 크기보다, 기존 블록의 크기가 크다면
    {
        csize = size; // 기존 블록의 크기를 요청에 들어온 크기 만큼으로 줄인다.
    }
    memcpy(new_bp, bp, csize); // bp 위치에서 csize만큼의 크기를 new_bp의 위치에 복사함
    mm_free(bp);               // 기존 bp의 메모리는 할당 해제해줌
    return new_bp;
}

/*할당된 블록 해제하기*/
void mm_free(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp)); // header에 담겨 있는 크기 정보 = size

    PUT(HDRP(bp), PACK(size, 0)); // block header를 업데이트 -> 할당 비트를 0으로
    PUT(FTRP(bp), PACK(size, 0)); // block footer를 업데이트 -> 할당 비트를 0으로
    coalesce(bp);
}

/* 인접한 블록들과 병합하기 */
static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp))); // 이전 블록의 footer 정보를 읽어와서 할당여부 저장
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp))); // 다음 블록의 header 정보를 읽어와서 할당여부 저장
    size_t size = GET_SIZE(HDRP(bp));                   // 현재 블록의 header 정보를 읽어와서 size 저장

    if (prev_alloc && next_alloc) // 둘 다 사용중일 경우 (case1)
    {
        return bp; // 현재 블록의 포인터 return
    }
    else if (prev_alloc && !next_alloc) // 다음 블록만 가용블록 (case2)
    {
        size += GET_SIZE(HDRP(NEXT_BLKP(bp))); // 다음 블록의 header정보를 읽어와서 size값 만큼 +
        PUT(HDRP(bp), PACK(size, 0));          // size값 갱신
        PUT(FTRP(bp), PACK(size, 0));          // header 값 갱신 후 footer size 갱신
    }
    else if (!prev_alloc && next_alloc) // 이전 블록만 가용블록 (case3)
    {
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));   // 이전 블록의 header에서 size값 만큼 +
        PUT(FTRP(bp), PACK(size, 0));            // 현재 블록의 footer에 size값 갱신
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0)); // 이전 블록의 header에 size값 갱신
        bp = PREV_BLKP(bp);                      // bp를 이전 블록의 포인터로 변경
    }
    else
    {                                                                          //  이전블록과 다음 볼록이 모두 가용상태일 경우 (case 4)
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp))); // size = 이전블록의 header-> size + 다음 블록의 footer -> size
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));                               // 이전 블록의 header에 size값 갱신
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));                               // 다음 블록의 footer에 size값 갱신
        bp = PREV_BLKP(bp);                                                    // bp를 이전 블록의 포인터로 변경
    }
    last_bp = bp;
    return bp; // 현재 블록의 포인터 return
}
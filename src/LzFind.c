/* LzFind.c -- Match finder for LZ algorithms
2009-04-22 : Igor Pavlov : Public domain */

/* Modified by Felix Hanau*/
#include <string.h>
#include <stdlib.h>

#include "LzFind.h"
#include "zopfli/util.h"
#include "zopfli/match.h"

void MatchFinder_Free(CMatchFinder *p)
{
  free(p->hash);
}

void MatchFinder_Create(CMatchFinder *p)
{
  //256kb hash, 256kb binary tree
  p->hash = (UInt32*)malloc(131072 * sizeof(UInt32));
  if (!p->hash)
  {
    exit(1);
  }
  p->son = p->hash + 65536;

  memset(p->hash, 0, 65536 * sizeof(unsigned));
  p->cyclicBufferPos = 0;
  p->pos = ZOPFLI_WINDOW_SIZE;
}
static inline int distgroup();
static inline int distgroup_equal();

static inline unsigned short * GetMatches(UInt32 lenLimit, UInt32 curMatch, UInt32 pos, const Byte *cur, UInt32 *son,
                         UInt32 _cyclicBufferPos, unsigned short *distances, UInt32 maxLen)
{
  UInt32 *ptr0 = son + (_cyclicBufferPos << 1) + 1;
  UInt32 *ptr1 = son + (_cyclicBufferPos << 1);
  UInt32 len0 = 0, len1 = 0;
  UInt32 last_Delta = 30;
  for (;;)
  {
    UInt32 delta = pos - curMatch;
    if (delta >= ZOPFLI_WINDOW_SIZE)
    {
      *ptr0 = *ptr1 = 0;
      return distances;
    }
    UInt32 *pair = son + ((_cyclicBufferPos - delta + ((delta > _cyclicBufferPos) ? ZOPFLI_WINDOW_SIZE : 0)) << 1);
    const Byte *pb = cur - delta;
    UInt32 len = (len0 < len1 ? len0 : len1);
    if (pb[len] == cur[len])
    {
        //We are allowed to omit ==len and len != lenLimit and pb[len] == cur[len] and even the prev if condition
      ++len;
      if (len != lenLimit && pb[len] == cur[len])
      {
        len = GetMatch(&cur[len], &pb[len], cur + lenLimit, cur + lenLimit - 8) - cur;
      }

      if (maxLen < len)
      {
        if(ZopfliGetDistSymbol(delta) == last_Delta && 1) {
          *(distances - 2) = maxLen = len;
          *(distances - 1) = delta;
        }
        else {
        *distances++ = maxLen = len;
        *distances++ = delta;
        }
        last_Delta = ZopfliGetDistSymbol(delta);
        //Match eliminator pass: eliminate all matches that have the same dist group and are shorter, i. e. the entire dist group. This way we can guarantee a maximum of 32 matches given back and reduce memory requirements.

        if (len == lenLimit)
        {
          *ptr1 = pair[0];
          *ptr0 = pair[1];
          return distances;
        }
      }
    }
    if (pb[len] < cur[len])
    {
      *ptr1 = curMatch;
      ptr1 = pair + 1;
      curMatch = *ptr1;
      len1 = len;
    }
    else
    {
      *ptr0 = curMatch;
      ptr0 = pair;
      curMatch = *ptr0;
      len0 = len;
    }
  }
}

static inline void SkipMatches(UInt32 lenLimit, UInt32 curMatch, UInt32 pos, const Byte *cur, UInt32 *son,
                        UInt32 _cyclicBufferPos)
{
  UInt32 *ptr0 = son + (_cyclicBufferPos << 1) + 1;
  UInt32 *ptr1 = son + (_cyclicBufferPos << 1);
  UInt32 len0 = 0, len1 = 0;
  for (;;)
  {
    UInt32 delta = pos - curMatch;
    if (delta >= ZOPFLI_WINDOW_SIZE)
    {
      *ptr0 = *ptr1 = 0;
      return;
    }

    UInt32 *pair = son + ((_cyclicBufferPos - delta + ((delta > _cyclicBufferPos) ? (ZOPFLI_WINDOW_SIZE) : 0)) << 1);
    const Byte *pb = cur - delta;
    UInt32 len = (len0 < len1 ? len0 : len1);
    if (pb[len] == cur[len]) {
      len = GetMatch(&cur[len], &pb[len], cur + lenLimit, cur + lenLimit - 8) - cur;
      if (len == lenLimit) {
        *ptr1 = pair[0];
        *ptr0 = pair[1];
        return;
      }
    }
    if (pb[len] < cur[len])
    {
      *ptr1 = curMatch;
      ptr1 = pair + 1;
      curMatch = *ptr1;
      len1 = len;
    }
    else
    {
      *ptr0 = curMatch;
      ptr0 = pair;
      curMatch = *ptr0;
      len0 = len;
    }
  }
}

static void SkipMatches2(UInt32 *son, UInt32 _cyclicBufferPos)
{
    UInt32 *ptr0 = son + (_cyclicBufferPos << 1) + 1;
    UInt32 *ptr1 = son + (_cyclicBufferPos << 1);
    
        UInt32 *pair = son + ((_cyclicBufferPos - 1 + ((1 > _cyclicBufferPos) ? (ZOPFLI_WINDOW_SIZE) : 0)) << 1);
        *ptr1 = pair[0];
            *ptr0 = pair[1];
}



static void SkipMatches3(UInt32 *son, UInt32 _cyclicBufferPos)
{
    UInt32 * ptr = son + (_cyclicBufferPos << 1);
    ptr[0] = ptr[-2];
    ptr[1] = ptr[-1];
}

/*static void SkipMatches4(UInt32 *son, UInt32 _cyclicBufferPos)
{
    size_t* ptr = (size_t*)(son + (_cyclicBufferPos << 1));
    
    
    
    
    UInt32 * ptr = son + (_cyclicBufferPos << 1);
    
    
    UInt32 *pair = son + (ZOPFLI_WINDOW_MASK << 1);

    
    ptr[0] = ptr[-2];
    ptr[1] = ptr[-1];
}*/

#define MOVE_POS \
  ++p->cyclicBufferPos; \
  p->cyclicBufferPos &= ZOPFLI_WINDOW_MASK; \
  p->buffer++; \
  ++p->pos;

#define MF_PARAMS(p) p->pos, p->buffer, p->son, p->cyclicBufferPos

unsigned short Bt3Zip_MatchFinder_GetMatches(CMatchFinder *p, unsigned short *distances)
{
  unsigned lenl = p->bufend - p->buffer; { if (lenl < ZOPFLI_MIN_MATCH) {return 0;}}
  const Byte *cur = p->buffer;
  UInt32 hashValue = ((cur[2] | ((UInt32)cur[0] << 8)) ^ crc[cur[1]]) & 0xFFFF;
  UInt32 curMatch = p->hash[hashValue];
  p->hash[hashValue] = p->pos;
  UInt32 offset = (UInt32)(GetMatches(lenl > ZOPFLI_MAX_MATCH ? ZOPFLI_MAX_MATCH : lenl, curMatch, MF_PARAMS(p), distances, 2) - distances);
  MOVE_POS;
  return offset;
}

void Bt3Zip_MatchFinder_Skip(CMatchFinder* p, UInt32 num)
{
  while (num--)
  {
    const Byte *cur = p->buffer;
    UInt32 hashValue = ((cur[2] | ((UInt32)cur[0] << 8)) ^ crc[cur[1]]) & 0xFFFF;
    UInt32 curMatch = p->hash[hashValue];
    p->hash[hashValue] = p->pos;
    unsigned lenlimit = p->bufend - p->buffer;
    SkipMatches(lenlimit > ZOPFLI_MAX_MATCH ? ZOPFLI_MAX_MATCH : lenlimit, curMatch, MF_PARAMS(p));
    MOVE_POS;
  }
}

void Bt3Zip_MatchFinder_Skip2(CMatchFinder* p, UInt32 num)
{
    const Byte *cur = p->buffer;
    UInt32 hashValue = ((cur[0] | ((UInt32)cur[0] << 8)) ^ crc[cur[0]]) & 0xFFFF;
    p->pos += num;
    p->buffer += num;
    while (num--)
    {
        SkipMatches2(p->son, p->cyclicBufferPos);
        
        
        
        
        ++p->cyclicBufferPos;
        p->cyclicBufferPos &= ZOPFLI_WINDOW_MASK;
    }
    p->hash[hashValue] = p->pos - 1;
}

void CopyMF(const CMatchFinder *p, CMatchFinder* copy){
  copy->hash = (UInt32*)malloc(131072 * sizeof(UInt32));
  if (!copy->hash)
  {
    exit(1);
  }
  copy->son = copy->hash + 65536;
  memcpy(copy->hash, p->hash, 131072 * sizeof(UInt32));

  copy->cyclicBufferPos = p->cyclicBufferPos;
  copy->pos = p->pos;
  copy->buffer = p->buffer;
}

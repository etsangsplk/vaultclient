#include "vcBPA.h"

#include "vcMath.h"
#include "vcConvert.h"

#include "vdkConvert.h"
#include "vdkConvertCustom.h"
#include "vdkQuery.h"

#include "udChunkedArray.h"
#include "udWorkerPool.h"
#include "udSafeDeque.h"
#include "udJSON.h"
#include "udPlatformUtil.h"
#include "udStringUtil.h"

#if VC_HASCONVERT

// small array
#define LOW_MEMORY 1

#if LOW_MEMORY
// for data structure
typedef uint8_t TINDEX; // max 255, needs bigger than BLOCK_SIZE
static const uint32_t BLOCK_SIZE = 128; // 1 << 7
static const uint32_t HASH_ARRAY_LEN = 512; // (111 111 111) + 1, 3 bits for x/y/z
static const uint32_t HASH_ARRAY_MASK = 7; // 111
#define GET_HASHINDEX(x, y, z) (((uint32_t)(x) & HASH_ARRAY_MASK) << 6 | ((uint32_t)(y) & HASH_ARRAY_MASK) << 3 | ((uint32_t)(z) & HASH_ARRAY_MASK) )

// for BPA
typedef uint32_t HASHKEY;
static const uint32_t BPA_LEVEL_LEN = 1024; // max voxel (1<<10) supported by uint32.
static const uint32_t BPA_LEVEL_MASK = 1023; // max voxel index (1<<10 - 1) (11 1111 1111)supported by uint32.
static const uint32_t MAX_POINTNUM = 1 << 25; // can read maximum 33,554,432 points in cube(2r*2r*2r*LEVEL_LEN*LEVEL_LEN*LEVEL_LEN)meter
#define GET_HASHKEY(x, y, z) (((uint32_t)(x) & BPA_LEVEL_MASK) << 20 | ((uint32_t)(y) & BPA_LEVEL_MASK) << 10 | ((uint32_t)(z) & BPA_LEVEL_MASK) )
#define GET_X(code) ( ((HASHKEY)(code) >> 20) & BPA_LEVEL_MASK )
#define GET_Y(code) ( ((HASHKEY)(code) >> 10) & BPA_LEVEL_MASK )
#define GET_Z(code) ( (HASHKEY)(code) & BPA_LEVEL_MASK )

#else
// for data structure
typedef uint16_t TINDEX; // max 65535, needs bigger than BLOCK_SIZE
static const uint32_t BLOCK_SIZE = 1 << 15; // 21 - 6
static const uint32_t HASH_ARRAY_LEN = 262144; // 1 << 18 + 1, 6 bits for x/y/z
static const uint32_t HASH_ARRAY_MASK = 63; // 111111, 1 << 6 -1
#define GET_HASHINDEX(gridX, gridY, gridZ) (((uint32_t)(gridX) & HASH_ARRAY_MASK) << 8 | ((uint32_t)(gridY) & HASH_ARRAY_MASK) << 4 | ((uint32_t)(gridZ) & HASH_ARRAY_MASK) )

// for BPA
typedef uint64_t HASHKEY;
static const uint32_t BPA_LEVEL_LEN = 2097152; // max voxel (1<<21) supported by uint64.
static const uint32_t BPA_LEVEL_MASK = 2097151; // (1<<21 -1)
static const uint32_t MAX_POINTNUM = 1 << 30; // can read maximum 1,073,741,824 points in cube(2r*2r*2r*LEVEL_LEN*LEVEL_LEN*LEVEL_LEN)meter

#define GET_HASHKEY(vx, vy, vz) (((uint32_t)(vx) & BPA_LEVEL_MASK) << 42 | ((uint32_t)(vy) & BPA_LEVEL_MASK) << 21 | ((uint32_t)(vz) & BPA_LEVEL_MASK) )
#define GET_X(code) ( ((VCODE)code >> 42) & BPA_LEVEL_MASK )
#define GET_Y(code) ( ((VCODE)code >> 21) & BPA_LEVEL_MASK )
#define GET_Z(code) ( (VCODE)(code) & BPA_LEVEL_MASK )

#endif

template<typename TData>
struct DataBlock
{
  TData *pBlockData;
  DataBlock *pNext; // next linked LinkedArray
  TINDEX index; // avaliable index  

  int blocklen;

  void Init()
  {
    pBlockData = udAllocType(TData, BLOCK_SIZE, udAF_Zero);
    index = 0;
    pNext = nullptr;
  }

  void Deinit()
  {
    DataBlock *pCurrTemp = this;
    DataBlock *pNextTemp = this->pNext;
    while (pNextTemp != nullptr)
    {
      while (pNextTemp->pNext != nullptr)
      {
        pCurrTemp = pNextTemp;
        pNextTemp = pCurrTemp->pNext;
      }

      udFree(pCurrTemp->pNext);
      pCurrTemp = this;
      pNextTemp = this->pNext;
    }
  }

  TData *AddData()
  {
    DataBlock *pFind = this;
    while (pFind->pNext != nullptr)
      pFind = pFind->pNext;

    if (pFind->index == BLOCK_SIZE)
    {
      pFind->pNext = udAllocType(DataBlock, 1, udAF_Zero);
      pFind = pFind->pNext;
      pFind->Init();
      blocklen++;
    }

    return &(pFind->pBlockData[pFind->index++]);
  }

};

template<typename TKey, typename TData>
struct vcBPAHashMap
{
  struct HashNode
  {
    TData data; // first block
    TKey hashKey; // hash value
  };

  struct HashNodeBlock
  {
    HashNode **pBlockData;
    HashNodeBlock *pNext;
    TINDEX index; // avaliable index

    int blocklen;

    void Init()
    {
      pBlockData = udAllocType(HashNode*, BLOCK_SIZE, udAF_Zero);
      index = 0;
      pNext = nullptr;
    }

    void Deinit()
    {
      HashNodeBlock *pCurrTemp = this;
      HashNodeBlock *pNexTemp = this->pNext;
      while (pNexTemp != nullptr)
      {
        while (pNexTemp->pNext != nullptr)
        {
          pCurrTemp = pNexTemp;
          pNexTemp = pCurrTemp->pNext;
        }

        for (TINDEX i = 0; i < pCurrTemp->pNext->index; i++)
        {
          if (pCurrTemp->pNext->pBlockData[i])
          {
            pCurrTemp->pNext->pBlockData[i]->hashKey = 0;
            udFree(pCurrTemp->pNext->pBlockData[i]);
          }
        }          
        udFree(pCurrTemp->pNext);
        pCurrTemp = this;
        pNexTemp = this->pNext;
      }
    }

    HashNode *AddHashNode(TKey hashKey)
    {
      HashNodeBlock *pFind = this;
      while (pFind->pNext != nullptr)
        pFind = pFind->pNext;

      if (pFind->index == BLOCK_SIZE)
      {
        pFind->pNext = udAllocType(HashNodeBlock, 1, udAF_Zero);
        pFind = pFind->pNext;
        pFind->Init();

        blocklen++;
      }

      pFind->pBlockData[pFind->index] = udAllocType(HashNode, 1, udAF_Zero);
      pFind->pBlockData[pFind->index]->hashKey = hashKey;

      return pFind->pBlockData[pFind->index++];
    }

    HashNode *FindHashNode(TKey hashKey)
    {
      HashNodeBlock *pFind = this;
      while (pFind != nullptr)
      {
        for (TINDEX i = 0; i < pFind->index; i++)
        {
          HashNode *p = pFind->pBlockData[i];
          if (p->hashKey == hashKey)
            return p;
        }
        pFind = pFind->pNext;
      }

      return nullptr;
    }
  };

  HashNodeBlock **pArray;

  void Init()
  {
    pArray = udAllocType(HashNodeBlock*, HASH_ARRAY_LEN, udAF_Zero);
  }

  TData *AddNode(uint32_t x, uint32_t y, uint32_t z)
  {
    TINDEX hashIndex = GET_HASHINDEX(x, y, z);
    TKey hashKey = GET_HASHKEY(x, y, z);

    HashNodeBlock **pFirst = &pArray[hashIndex];
    if (*pFirst == nullptr)
    {
      *pFirst = udAllocType(HashNodeBlock, 1, udAF_Zero);
      (*pFirst)->Init();
    }

    HashNode *pNode = (*pFirst)->FindHashNode(hashKey);
    if (pNode == nullptr)
    {
      pNode = (*pFirst)->AddHashNode(hashKey);
    }

    return &pNode->data;
  }

  void Deinit()
  {
    if (!pArray) return;

    for (TINDEX i = 0; i < HASH_ARRAY_LEN; i++)
    {
      if (pArray[i])
      {
        pArray[i]->Deinit();
        udFree(pArray[i]);
      }
    }
    udFree(pArray);
  }

  TData *FindData(uint32_t x, uint32_t y, uint32_t z)
  {
    TINDEX hashIndex = GET_HASHINDEX(x, y, z);
    TKey hashKey = GET_HASHKEY(x, y, z);
    HashNodeBlock **pFirst = &pArray[hashIndex];
    if (*pFirst == nullptr)
      return nullptr;

    HashNode *pNode = (*pFirst)->FindHashNode(hashKey);
    if (pNode != nullptr)
      return &pNode->data;

    return nullptr;
  }

};


template<typename TStackArray>
TStackArray *FindAvailableStackArray(TStackArray *pBottomArray, int32_t arrayLen)
{
  TStackArray *pFind = pBottomArray;
  while (pFind->pTop != nullptr)
    pFind = pFind->pTop;

  if (pFind->index == arrayLen)
  {
    pFind->pTop = udAllocType(TStackArray, 1, udAF_Zero);
    pFind->pTop->pBottom = pFind;
    pFind = pFind->pTop;
  }

  return pFind;
}

enum vcBPARunningStatus
{
  vcBPARS_Active,
  vcBPARS_Failed,
  vcBPARS_Success,
  vcBPARS_Cancel,
  vcBPARS_End
};

//4+1=5byte
struct vcBPAVertex
{
  udDouble3 position;
  uint32_t j; // position from buffer
  bool used; // 0 not // 0x0001 triangle // 
};

struct vcBPAVoxel
{
  DataBlock<vcBPAVertex> data;
  uint32_t pointNum;

  void Init()
  {
    data.Init();
    pointNum = 0;
  }
  void Deinit()
  {
    data.Deinit();
  }
  void ToArray(vcBPAVertex **pArray)
  {
    DataBlock<vcBPAVertex> *pFind = &data;
    uint32_t t = 0;
    while (pFind != nullptr)
    {
      for (uint32_t i = 0; i < pFind->index; i++)
      {
        pArray[t++] = &pFind->pBlockData[i];
      }
      pFind = pFind->pNext;
    }      
  }
};

struct vcBPATriangle
{
  udDouble3 vertices[3];
  udDouble3 ballCenter; // Ball used to construct triangle
};

struct vcBPATriangleArray
{
  DataBlock<vcBPATriangle> data;
  uint32_t pointNum;
  void Init()
  {
    data.Init();
    pointNum = 0;
  }
  void Deinit()
  {
    data.Deinit();
  }
};

struct vcBPAEdge
{
  udDouble3 *vertices[2];
  udDouble3 triangleZ;
  udDouble3 ballCenter;  
};

struct vcBPAEdgeArray
{
  enum { ElementCount = 512 };
  vcBPAEdge edges[ElementCount];

  vcBPAEdgeArray *pTop;
  vcBPAEdgeArray *pBottom;
  int16_t index;
};

struct vcBPAFrozenEdge
{
  udDouble3 vertices[2];
  udDouble3 ballCenter;
  udDouble3 triangleZ;
};

struct vcBPAFrozenEdgeArray
{
  enum { ElementCount = 32 };
  vcBPAFrozenEdge edges[ElementCount];

  vcBPAFrozenEdgeArray *pTop;
  vcBPAFrozenEdgeArray *pBottom;
  uint16_t index;
};

// old model
struct vcBPAGridHashNode
{
  vcBPAHashMap<HASHKEY, vcBPAVoxel> voxelHashMap; // linked hash array, never change after being created unitil .
  vcBPAHashMap<HASHKEY, vcBPATriangleArray> triangleHashMap; // linked hash array will be used to compare data
  vcBPAEdgeArray *pActiveEdgesStack;
  vcBPAFrozenEdgeArray *pFrozenEdgesStack;
  int32_t frozenEdgeCount;

  udDouble3 zero;
  udDouble3 end;
  uint32_t vxSize;
  uint32_t vySize;
  uint32_t vzSize;
  uint32_t pointNum;
  uint32_t triangleSize;
  vdkPointBufferF64 *pBuffer;

  void Init()
  {
    voxelHashMap.Init();
    triangleHashMap.Init();
    pActiveEdgesStack = udAllocType(vcBPAEdgeArray, 1, udAF_Zero);
    pFrozenEdgesStack = udAllocType(vcBPAFrozenEdgeArray, 1, udAF_Zero);
  }

  static void CleanBPAData(vcBPAGridHashNode *pGrid)
  {
    // release all active edges(should be anyone left)
    RemoveAllEdge<vcBPAEdgeArray>(pGrid->pActiveEdgesStack);
    udFree(pGrid->pActiveEdgesStack);

    // release all voxels
    pGrid->voxelHashMap.Deinit();
  }

  void Deinit()
  {
    // release all left frozen edges
    if (pFrozenEdgesStack != nullptr)
    {
      RemoveAllEdge<vcBPAFrozenEdgeArray>(pFrozenEdgesStack);
      udFree(pFrozenEdgesStack);
    }

    // release all triangles
    triangleHashMap.Deinit();

    vdkPointBufferF64_Destroy(&pBuffer);
  }

  static bool FindPointInActiveEdges(vcBPAGridHashNode *pGrid, udDouble3 *p0)
  {
    vcBPAEdgeArray *pFind = pGrid->pActiveEdgesStack;
    while (pFind->pTop != nullptr)
      pFind = pFind->pTop;

    do
    {
      for (int32_t i = pFind->index - 1; i >= 0; i--)
      {
        vcBPAEdge &edge = pFind->edges[i];
        if (edge.vertices[0] == p0 || edge.vertices[1] == p0)
          return true;
      }
      pFind = pFind->pBottom;
    } while (pFind != nullptr);

    return false;
  }

  static bool FindEdgeInActiveEdges(vcBPAGridHashNode *pGrid, udDouble3 *p0, udDouble3 *p1)
  {
    vcBPAEdgeArray *pFind = pGrid->pActiveEdgesStack;
    while (pFind->pTop != nullptr)
      pFind = pFind->pTop;

    do
    {
      for (int32_t i = pFind->index - 1; i >= 0; i--)
      {
        vcBPAEdge &edge = pFind->edges[i];
        if ((edge.vertices[0] == p0 && edge.vertices[1] == p1) || (edge.vertices[1] == p0 && edge.vertices[0] == p1))
          return true;
      }
      pFind = pFind->pBottom;
    } while (pFind != nullptr);

    return false;
  }

  template<typename T_ARRAY, typename TEdge>
  static bool PopEdge(T_ARRAY * pArray, TEdge &edge)
  {
    T_ARRAY *pFind = pArray;
    // empty
    if (pFind->index == 0)
      return false;

    while (pFind->pTop != nullptr)
      pFind = pFind->pTop;

    edge = pFind->edges[--pFind->index];
    if (pFind->index == 0 && pFind != pArray)
    {
      pFind = pFind->pBottom;
      udFree(pFind->pTop);
    }

    return true;
  }

  template<typename T_ARRAY, typename TEdge, typename TPoint>
  static void RemoveEdge(T_ARRAY *pBottomArray, TPoint p0, TPoint p1)
  {    
    // empty
    if (pBottomArray->index == 0)
      return;

    TEdge top;
    PopEdge<T_ARRAY, TEdge>(pBottomArray, top);
    if ((top.vertices[0] == p0 && top.vertices[1] == p1) || (top.vertices[1] == p0 && top.vertices[0] == p1))
      return;

    T_ARRAY *pFind = pBottomArray;
    while (pFind->pTop != nullptr)
      pFind = pFind->pTop;

    // swap from the bottom
    do
    {
      for (int32_t i = pFind->index - 1; i >= 0; i--)
      {
        TEdge &edge = pFind->edges[i];
        if ((edge.vertices[0] == p0 && edge.vertices[1] == p1) || (edge.vertices[1] == p0 && edge.vertices[0] == p1))
        {
          edge.vertices[0] = top.vertices[0];
          edge.vertices[1] = top.vertices[1];
          edge.triangleZ = top.triangleZ;
          edge.ballCenter = top.ballCenter;
          return;
        }
      }
      pFind = pFind->pBottom;
    } while (pFind != nullptr);
  }

   template<typename T_ARRAY>
  static void RemoveAllEdge(T_ARRAY *pArray)
  {
    T_ARRAY *pFind = pArray;
    if (pFind->index == 0) return;

    while (pFind->pTop != nullptr)
      pFind = pFind->pTop;

    while (pFind != pArray)
    {
      pFind = pFind->pBottom;
      udFree(pFind->pTop);
    }
    pArray->index = 0;
  }
 
  static bool IfTriangleDuplicated(vcBPAGridHashNode *pGrid, uint32_t x, uint32_t y, uint32_t z, const udDouble3 &p0, const udDouble3 &p1, const udDouble3 &p2)
  {
    vcBPATriangleArray *pArray = pGrid->triangleHashMap.FindData(x, y, z);
    if (!pArray)
      return true;    

    DataBlock<vcBPATriangle> *pData = &pArray->data;
    while (pData != nullptr)
    {
      for (int32_t i = 0; i < pData->index; i++)
      {
        vcBPATriangle &t = pData->pBlockData[i];
        if ((t.vertices[0] == p0 && t.vertices[1] == p1 && t.vertices[2] == p2) || (t.vertices[0] == p1 && t.vertices[1] == p2 && t.vertices[2] == p0) || (t.vertices[0] == p2 && t.vertices[1] == p0 && t.vertices[2] == p1))
          return true;
      }
      pData = pData->pNext;
    }

    return false;
  }

};

// new model grid
struct vcVoxelGridHashNode
{
  vcBPAHashMap<HASHKEY, vcBPAVoxel> voxelHashMap; // linked hash array
  udDouble3 zero;
  udDouble3 end;
  uint32_t vxSize;
  uint32_t vySize;
  uint32_t vzSize;
  uint32_t pointNum;
  vdkPointBufferF64 *pBuffer;

  //for hash array
  uint64_t hashKey;
  vcVoxelGridHashNode *pNext;
  void Init()
  {
    voxelHashMap.Init();
  }
  void Deinit()
  {
    voxelHashMap.Deinit();
    vdkPointBufferF64_Destroy(&pBuffer);
  }
};

struct vcBPAManifold
{
  udWorkerPool *pPool;
  vdkContext* pContext;

  vcBPAHashMap< HASHKEY, vcBPAGridHashNode> oldModelMap;
  vcBPAHashMap< HASHKEY, vcVoxelGridHashNode> newModelMap;

  double baseGridSize;
  double ballRadius;
  double voxelSize;

  void Init()
  {
    oldModelMap.Init();
    newModelMap.Init();
  }

  void Deinit()
  {
    oldModelMap.Deinit();
    newModelMap.Deinit();

    pContext = nullptr;
    udWorkerPool_Destroy(&pPool);
  }

};

void vcBPA_QueryPoints(vdkContext* pContext, vdkPointCloud *pModel, const double centrePoint[3], const double halfSize[3], vdkPointBufferF64* pBuffer)
{
  vdkQueryFilter *pFilter = nullptr;
  vdkQueryFilter_Create(&pFilter);
  static double zero[3] = {0, 0, 0};
  vdkQueryFilter_SetAsBox(pFilter, centrePoint, halfSize, zero);

  vdkQuery *pQuery = nullptr;
  vdkQuery_Create(pContext, &pQuery, pModel, pFilter);
  vdkQuery_ExecuteF64(pQuery, pBuffer);
  vdkQuery_Destroy(&pQuery);

  vdkQueryFilter_Destroy(&pFilter);
}

void vcBPA_AddPoints(uint32_t j, double x, double y, double z, const udDouble3 &zero, vcBPAHashMap<HASHKEY, vcBPAVoxel> *voxelHashMap, double voxelSize)
{
  uint32_t vx = (uint32_t)((x - zero.x) / voxelSize);
  uint32_t vy = (uint32_t)((y - zero.y) / voxelSize);
  uint32_t vz = (uint32_t)((z - zero.z) / voxelSize);

  //add a point into the voxel
  vcBPAVoxel *pVoxel = voxelHashMap->FindData(vx, vy, vz);
  if (pVoxel == nullptr)
  {
    pVoxel = voxelHashMap->AddNode(vx, vy, vz);
    pVoxel->Init();
  }
  ++pVoxel->pointNum;

  vcBPAVertex *point = pVoxel->data.AddData();
  point->position = udDouble3::create(x, y, z);
  point->j = j;
  point->used = false;
}

udDouble3 vcBPA_GetTriangleNormal(const udDouble3 & p0, const udDouble3 & p1, const udDouble3 & p2)
{
  udDouble3 a = p1 - p0;
  udDouble3 b = p2 - p0;
  return udNormalize(udCross(a, b));
}

void vcBPA_FindUnusePoints(vcBPAVertex **pUnuseArray, vcBPAVoxel *pVoxel, uint32_t &unuseNum)
{
  unuseNum = 0;
  DataBlock<vcBPAVertex> *pPointArray = &pVoxel->data;
  while (pPointArray != nullptr)
  {
    for (int i = 0; i < pPointArray->index; i++)
    {
      if (!pPointArray->pBlockData[i].used)
        pUnuseArray[unuseNum++] = &pPointArray->pBlockData[i];
    }
    pPointArray = pPointArray->pNext;
  }  
}

struct SortPoint
{
  vcBPAVertex *p;
  double d;
};

size_t vcBPA_GetNearbyPoints(vcBPAVertex **&pp, vcBPAGridHashNode* pGrid, vcBPAVertex* pVertex, uint32_t x, uint32_t y, uint32_t z, double ballDiameterSq)
{
  udChunkedArray<SortPoint> nearbyPoints;
  nearbyPoints.Init(32);

  int32_t vcx = (int32_t)x;
  int32_t vcy = (int32_t)y;
  int32_t vcz = (int32_t)z;

  SortPoint sp;
  for (int32_t vx = udMax(vcx - 1, 0); vx <= udMin(vcx + 1, pGrid->vxSize-1); vx++)
  {
    for (int32_t vy = udMax(vcy - 1, 0); vy <= udMin(vcy + 1, pGrid->vySize-1); vy++)
    {
      for (int32_t vz = udMax(vcz - 1, 0); vz <= udMin(vcz + 1, pGrid->vzSize-1); vz++)
      {
        vcBPAVoxel *pVoxel = pGrid->voxelHashMap.FindData(vx, vy, vz);
        if (pVoxel == nullptr)
          continue;

        // check all points
        DataBlock<vcBPAVertex> *pPointArray = &pVoxel->data;
        while (pPointArray != nullptr)
        {
          for (int i = 0; i <= pPointArray->index; i++)
          {
            if (pPointArray->pBlockData[i].used)
              continue;
            if (pVertex && pVertex == &pPointArray->pBlockData[i] )
              continue;

            udDouble3& point = pPointArray->pBlockData[i].position;
            double dsqr = udMagSq3(pVertex->position - point);
            if (dsqr > ballDiameterSq)
              continue;

            sp.p = &pPointArray->pBlockData[i];
            sp.d = dsqr;
            size_t j = 0;
            for (; j < nearbyPoints.length; ++j)
            {
              double d = nearbyPoints.GetElement(j)->d;
              if (d > dsqr)
                break;
            }
            nearbyPoints.Insert(j, &sp);
          }

          pPointArray = pPointArray->pNext;
        }
      }
    }
  }

  size_t nearbyNum = nearbyPoints.length;
  pp = udAllocType(vcBPAVertex *, nearbyNum, udAF_Zero);
  for (size_t i = 0; i < nearbyPoints.length; ++i)
    pp[i] = nearbyPoints[i].p;
  nearbyPoints.Deinit();

  return nearbyNum;
}

void vcBPA_InsertEdge(vcBPAGridHashNode *pGrid, const udDouble3 &ballCenter, const udDouble3 &triangleZ, udDouble3 *e1, udDouble3 *e2, uint32_t x, uint32_t y, uint32_t z, double voxelSize, uint32_t gridXSize, uint32_t gridYSize, uint32_t gridZSize)
{
  // Mark edge as frozen if any point lies outside the grid
  udDouble3 d1 = *e1 - pGrid->zero;
  udDouble3 d2 = *e2 - pGrid->zero;
  bool d1Frozen = false;
  bool d2Frozen = false;
  if (x < gridXSize - 1)
  {
    if (d1.x >= pGrid->end.x - voxelSize)
      d1Frozen = true;
    if (d2.x >= pGrid->end.x - voxelSize)
      d2Frozen = true;
  }

  if (y < gridYSize - 1)
  {
    if (d1.y >= pGrid->end.y - voxelSize)
      d1Frozen = true;
    if (d2.y >= pGrid->end.y - voxelSize)
      d2Frozen = true;
  }

  if (z < gridZSize - 1)
  {
    if (d1.z >= pGrid->end.z - voxelSize)
      d1Frozen = true;
    if (d2.z >= pGrid->end.z - voxelSize)
      d2Frozen = true;
  }

  // frozen edge
  if (d1Frozen && d2Frozen)
  {
    vcBPAFrozenEdgeArray *pFind = FindAvailableStackArray<vcBPAFrozenEdgeArray>(pGrid->pFrozenEdgesStack, vcBPAFrozenEdgeArray::ElementCount);
    ++ pGrid->frozenEdgeCount;
    vcBPAFrozenEdge &edge = pFind->edges[pFind->index++];
    edge.vertices[0] = *e1;
    edge.vertices[1] = *e2;
    edge.ballCenter = ballCenter;
    edge.triangleZ = triangleZ;
  }
  else
  {
    vcBPAEdgeArray *pFind = FindAvailableStackArray<vcBPAEdgeArray>(pGrid->pActiveEdgesStack, vcBPAEdgeArray::ElementCount);
    vcBPAEdge &edge = pFind->edges[pFind->index++];
    edge.vertices[0] = e1;
    edge.vertices[1] = e2;
    edge.ballCenter = ballCenter;
    edge.triangleZ = triangleZ;
  }

}

vcBPATriangle *vcBPA_CreateTriangle(vcBPAGridHashNode *pGrid, const udDouble3 &ballCenter, const udDouble3 &p0, const udDouble3 &p1, const udDouble3 &p2, double voxelSize)
{
  udDouble3 d = (ballCenter - pGrid->zero)/ voxelSize;
  vcBPATriangleArray *pArray = pGrid->triangleHashMap.FindData((uint32_t)d.x, (uint32_t)d.y, (uint32_t)d.z);
  if (pArray == nullptr)
  {
    pArray = pGrid->triangleHashMap.AddNode((uint32_t)d.x, (uint32_t)d.y, (uint32_t)d.z);
    pArray->Init();
  }
    
  vcBPATriangle *t = pArray->data.AddData();
  t->vertices[0] = p0;
  t->vertices[1] = p1;
  t->vertices[2] = p2;
  t->ballCenter = ballCenter;

  ++pGrid->triangleSize;

  printf("vcBPA_CreateTriangle %d\n", pGrid->triangleSize);
  return t;
}

bool vcBPA_FindSeedTriangle(vcBPAGridHashNode *pGrid, vcBPAVertex *pVertex, uint32_t vx, uint32_t vy, uint32_t vz, uint32_t gridX, uint32_t gridY, uint32_t gridZ, double ballRadius, double voxelSize, uint32_t gridXSize, uint32_t gridYSize, uint32_t gridZSize)
{
  // find all points within 2r  
  double ballRadiusSq = ballRadius * ballRadius;
  vcBPAVertex **nearbyPoints = nullptr;
  size_t nearbyNum = vcBPA_GetNearbyPoints(nearbyPoints, pGrid, pVertex, vx, vy, vz, ballRadiusSq*4);
  printf("grid(%d,%d,%d) voxel(%d,%d,%d) nearby %d\n", gridX, gridY, gridZ, vx, vy, vz, nearbyNum);
  if(nearbyNum == 0)
    return false;

  udDouble3 triangleNormal;
  bool inside = false;
  udDouble3 ballCenter;

  for (size_t i = 0; i < nearbyNum; ++i)
  {
    vcBPAVertex *p1 = nearbyPoints[i];
    for (size_t j = i + 1; j < nearbyNum; ++j)
    {
      vcBPAVertex *p2 = nearbyPoints[j];

      double d12 = udMagSq3(p1->position - p2->position);
      if (d12 > ballRadiusSq * 4) continue;

      // Check that the triangle normal is consistent with the vertex normals - i.e. pointing outward
      triangleNormal = vcBPA_GetTriangleNormal(pVertex->position, p1->position, p2->position);
      if (triangleNormal.z < 0) // Normal is pointing down, that's bad!
        ballCenter = udGetSphereCenterFromPoints(ballRadius, p1->position, pVertex->position, p2->position);
      else
        ballCenter = udGetSphereCenterFromPoints(ballRadius, pVertex->position, p1->position, p2->position);
      
      // Invalid triangle
      if (ballCenter == udDouble3::zero())
        continue;

      // Test that a p-ball with center in the outward halfspace touches all three vertices and contains no other points
      for (size_t k = 0; k < nearbyNum; k++)
      {
        if (nearbyPoints[k] == pVertex || nearbyPoints[k] == p1 || nearbyPoints[k] == p2) continue;
        if (ballRadiusSq - udMagSq3(nearbyPoints[k]->position - ballCenter) > FLT_EPSILON)
        {
          inside = true;
          break;
        }
      }

      // Check failed, find another
      if (!inside)
      {
        pVertex->used = true;
        p1->used = true;
        p2->used = true;

        udDouble3 *n0 = nullptr;
        udDouble3 *n1 = nullptr;
        udDouble3 *n2 = &p2->position;

        if (triangleNormal.z < 0)
        {
          n0 = &p1->position;
          n1 = &pVertex->position;
        } 
        else
        {
          n0 = &pVertex->position;
          n1 = &p1->position;          
        }

        vcBPA_InsertEdge(pGrid, ballCenter, *n1, n2, n0, gridX, gridY, gridZ, voxelSize, gridXSize, gridYSize, gridZSize);
        vcBPA_InsertEdge(pGrid, ballCenter, *n0, n1, n2, gridX, gridY, gridZ, voxelSize, gridXSize, gridYSize, gridZSize);
        vcBPA_InsertEdge(pGrid, ballCenter, *n2, n0, n1, gridX, gridY, gridZ, voxelSize, gridXSize, gridYSize, gridZSize);

        vcBPA_CreateTriangle(pGrid, ballCenter, *n0, *n1, p2->position, voxelSize);
        return true;
      }
    }
  }

  return false;

}

struct vcBPATriangleSeek
{
  udDouble3 *vertices[3];
  udDouble3 ballCenter;
};

bool vcBPA_BallPivot(vcBPAGridHashNode *pGrid, double ballRadius, vcBPAEdge &edge, udDouble3 *&pVertex, udDouble3 &ballCenter, double voxelSize)
{
  // find all points within 2r
  vcBPAVertex temp = {};
  temp.position = (*edge.vertices[0] + *edge.vertices[1])*0.5; // middle point
  double ballRadiusSq = ballRadius * ballRadius;

  udDouble3 d = (temp.position - pGrid->zero) / voxelSize;
  vcBPAVertex **nearbyPoints = nullptr;
  size_t nearbyNum = vcBPA_GetNearbyPoints(nearbyPoints, pGrid, &temp, (uint32_t)(d.x), (uint32_t)(d.y), (uint32_t)(d.z), ballRadiusSq*4);
  if (nearbyNum == 0)
    return false;

  udChunkedArray<vcBPATriangleSeek> triangles;
  triangles.Init(32);
  for (size_t i = 0; i < nearbyNum; ++i)
  {
    // Skip denegerate triangles and the triangle that made this edge
    if (&nearbyPoints[i]->position == edge.vertices[0] || &nearbyPoints[i]->position == edge.vertices[1] || nearbyPoints[i]->position == edge.triangleZ)
      continue;

    // Build potential seed triangle
    vcBPATriangleSeek t;
    t.vertices[0] = edge.vertices[0];
    t.vertices[1] = &nearbyPoints[i]->position;
    t.vertices[2] = edge.vertices[1];

    // Check that the triangle normal is consistent with the vertex normals - i.e. pointing outward
    udDouble3 triangleNormal = vcBPA_GetTriangleNormal(*t.vertices[0], *t.vertices[1], *t.vertices[2]);
    if (triangleNormal.z < 0) // Normal is pointing down, that's bad!
      continue;

    udDouble3 distances = {
      udMagSq3(*t.vertices[0] - *t.vertices[1]),
      udMagSq3(*t.vertices[1] - *t.vertices[2]),
      udMagSq3(*t.vertices[2] - *t.vertices[0])
    };
    
    if (distances.x > ballRadiusSq * 4 || distances.y > ballRadiusSq * 4 || distances.z > ballRadiusSq * 4)
      continue;

    udDouble3 ballCenterTest = udGetSphereCenterFromPoints(ballRadius, *t.vertices[0], *t.vertices[1], *t.vertices[2]);

    // Invalid triangle
    if (ballCenterTest == udDouble3::zero())
      continue;

    bool inside = false;
    for (size_t k = 0; k < nearbyNum; k++)
    {
      if (&nearbyPoints[k]->position == edge.vertices[0] || &nearbyPoints[k]->position == edge.vertices[1] || nearbyPoints[k]->position == edge.triangleZ)
        continue;
      if (ballRadiusSq - udMagSq3(nearbyPoints[k]->position - ballCenter) > FLT_EPSILON)
      {
        inside = true;
        break;
      }
    }

    // Ball contains points, invalid triangle
    if (inside)
      continue;

    t.ballCenter = ballCenterTest;
    triangles.PushBack(t);
  }

  if (triangles.length == 0)
  {
    triangles.Deinit();
    return false;
  }

  vcBPATriangleSeek &triangle = triangles[0];

  for (size_t i = 1; i < triangles.length; ++i)
  {
    udDouble3 points[3] = {
      edge.ballCenter - temp.position,
      triangle.ballCenter - temp.position,
      triangles[i].ballCenter - temp.position
    };

    double dots[2] = {
      udDot(points[0], points[1]),
      udDot(points[0], points[2]),
    };

    double angles[2] = {
      udACos(dots[0]),
      udACos(dots[1]),
    };

    // When points[1] is above the pivot point and points[2] is below the pivot point,
    // points[1] is the next in line.
    if (points[1].z > 0 && points[2].z < 0)
      continue;

    // When points[1] is below the pivot point and points[2] is above the pivot point,
    // points[2] is the next in line.
    if (points[1].z < 0 && points[2].z > 0)
    {
      triangle = triangles[i];
      continue;
    }

    if (points[1].z > 0) // Both are above the pivot point
    {
      if (angles[0] < angles[1])
        continue;

      if (angles[1] < angles[0])
      {
        triangle = triangles[i];
        continue;
      }
    }
    else // Both are below the pivot point
    {
      if (angles[0] > angles[1])
        continue;

      if (angles[1] > angles[0])
      {
        triangle = triangles[i];
        continue;
      }
    }
  }

  pVertex = triangle.vertices[1];
  ballCenter = triangle.ballCenter;
  triangles.Deinit();

  return true;
}


struct vcBPAConvertItemData
{
  vcBPAManifold *pManifold;

  vcVoxelGridHashNode *pNewModelGrid;
  vcBPAGridHashNode *pOldModelGrid;
  uint32_t gridx;
  uint32_t gridy;
  uint32_t gridz;
  vdkPointCloud *pOldModel;
  uint32_t leftPoint;
};

struct vcBPAConvertProcessInfo
{
  uint32_t voxelX;
  uint32_t voxelY;
  uint32_t voxelZ;
  vcBPAVertex **pArray;
  uint32_t currIndex;
  uint32_t arrayLen;
};

struct vcBPAData
{
  udDouble3 zero;
  udDouble3 gridSize;
  uint32_t gridx;
  uint32_t gridy;
  uint32_t gridz;  
  uint32_t gridXSize;
  uint32_t gridYSize;
  uint32_t gridZSize;
};

struct vcBPAConvertItem
{
  vcBPAManifold *pManifold;
  vdkContext *pContext;
  vdkPointCloud *pOldModel;
  vdkPointCloud *pNewModel;
  vcConvertItem *pConvertItem;
  double gridSize;
  double ballRadius;

  udSafeDeque<vcBPAConvertItemData> *pConvertItemData;
  vcBPAConvertItemData *pActiveItem;
  vcBPAConvertProcessInfo processInfo;
  udThread *pThread;
  udInterlockedInt32 running;
};

void vcBPA_DoGrid(void* pDataPtr, vcBPAGridHashNode *pGrid, double ballRadius, double voxelSize, uint32_t gridX, uint32_t gridY, uint32_t gridZ, uint32_t gridXSize, uint32_t gridYSize, uint32_t gridZSize)
{
  printf("vcBPA_DoGrid\n");

  vcBPAConvertItem *pData = (vcBPAConvertItem *)pDataPtr;

  vcBPAHashMap<HASHKEY, vcBPAVoxel>::HashNodeBlock *pCurrBlock = nullptr;
  uint32_t currBlockIndex = 0;
  uint32_t currHashIndex = 0;
  vcBPAHashMap<HASHKEY, vcBPAVoxel>::HashNode *pNode = nullptr;

  uint32_t unUseIndex = 0;
  uint32_t unuseNum = 0;
  HASHKEY hashKey = 0;
  vcBPAVertex **pUnuseArray = nullptr;

  vcBPAEdge edge = {};
  udDouble3 *pVertex = nullptr;
  udDouble3 ballCenter = {};

  while (pData->running.Get() == vcBPARS_Active)
  {
    if (vcBPAGridHashNode::PopEdge<vcBPAEdgeArray, vcBPAEdge>(pGrid->pActiveEdgesStack, edge))
    {
      pVertex = nullptr;
      ballCenter = {};

      double _time = udGetEpochMilliSecsUTCf() ;

      if (vcBPA_BallPivot(pGrid, ballRadius, edge, pVertex, ballCenter, voxelSize))
      {
        if (vcBPAGridHashNode::FindPointInActiveEdges(pGrid, pVertex))
        {
          if (vcBPAGridHashNode::IfTriangleDuplicated(pGrid, gridX, gridY, gridZ, *edge.vertices[0], *pVertex, *edge.vertices[1]))
            continue;

          vcBPA_CreateTriangle(pGrid, ballCenter, *edge.vertices[0], *pVertex, *edge.vertices[1], voxelSize);
          if (!vcBPAGridHashNode::FindEdgeInActiveEdges(pGrid, pVertex, edge.vertices[1]))
            vcBPA_InsertEdge(pGrid, ballCenter, *edge.vertices[0], pVertex, edge.vertices[1], gridX, gridY, gridZ, voxelSize, gridXSize, gridYSize, gridZSize);
          else
            vcBPAGridHashNode::RemoveEdge<vcBPAEdgeArray, vcBPAEdge, udDouble3*>(pGrid->pActiveEdgesStack, pVertex, edge.vertices[1]);

          if (!vcBPAGridHashNode::FindEdgeInActiveEdges(pGrid, edge.vertices[0], pVertex))
            vcBPA_InsertEdge(pGrid, ballCenter, *edge.vertices[1], edge.vertices[0], pVertex, gridX, gridY, gridZ, voxelSize, gridXSize, gridYSize, gridZSize);
          else
            vcBPAGridHashNode::RemoveEdge<vcBPAEdgeArray, vcBPAEdge, udDouble3 *>(pGrid->pActiveEdgesStack, pVertex, edge.vertices[0]);
        }        
      }

      printf("vcBPA_BallPivot %f\n", udGetEpochMilliSecsUTCf() - _time);
    }
    else
    {
      static uint32_t number = 0;
      if (pUnuseArray == nullptr)
      {
        double nt = udGetEpochMilliSecsUTCf();
        if (pCurrBlock == nullptr)
        {
          while(currHashIndex < HASH_ARRAY_LEN)
          {
            pCurrBlock = pGrid->voxelHashMap.pArray[currHashIndex++];
            if (pCurrBlock == nullptr)
              continue;

            break;
          }

          if(pCurrBlock == nullptr && currHashIndex == HASH_ARRAY_LEN)
          {
            printf("done.\n");
            return;
          }

          // next block, reset index
          currBlockIndex = 0;
        }

        if (pNode == nullptr)
        {
          while (currBlockIndex < pCurrBlock->index)
          {
            pNode = pCurrBlock->pBlockData[currBlockIndex++];
            if (pNode == nullptr)
              continue;
            break;
          }

          if (pNode == nullptr && currBlockIndex == pCurrBlock->index)
          {
            pCurrBlock = pCurrBlock->pNext;
            currBlockIndex = 0;
            continue;
          }          
        }

        vcBPAVoxel *pVoxel = &pNode->data;
        number += pVoxel->pointNum;
        unUseIndex = 0;
        pUnuseArray = udAllocType(vcBPAVertex *, pVoxel->pointNum, udAF_Zero);
        vcBPA_FindUnusePoints(pUnuseArray, pVoxel, unuseNum);

        if (unuseNum == 0)
        {
g          printf(" no unuse points, to search a new position \n");
          udFree(pUnuseArray);
          unUseIndex = 0;
          pNode = nullptr;
          continue;
        }

        hashKey = pNode->hashKey;        
        printf("points get time %f count %d of total %d\n", udGetEpochMilliSecsUTCf() - nt, number, pGrid->pBuffer->pointCount);
      }

      double tt = udGetEpochMilliSecsUTCf();
      // points might used after vcBPA_FindSeedTriangle, so they need to be checked again.
      while (unUseIndex < unuseNum)
      {
        if (!pUnuseArray[unUseIndex]->used)
        {
          printf("points %d of %d ", unUseIndex, unuseNum);
          bool bRet = vcBPA_FindSeedTriangle(pGrid, pUnuseArray[unUseIndex++], GET_X(hashKey), GET_Y(hashKey), GET_Z(hashKey), gridX, gridY, gridZ, ballRadius, voxelSize, gridXSize, gridYSize, gridZSize);
          if (bRet)
          {
            tt = udGetEpochMilliSecsUTCf() - tt;
            printf("vcBPA_FindSeedTriangle succ at %d/%d taks: %f(ms) %f(s)\n", unUseIndex - 1, unuseNum, tt, tt / 1000);
            break;
          }
        }
        else
        {
          ++unUseIndex;
        }
      }

      if (unUseIndex == unuseNum)
      {
        printf("all points were checked, to search a new voxel \n");
        udFree(pUnuseArray);
        unuseNum = 0;
        unUseIndex = 0;
        pNode = nullptr;
      }             
    }    
  }
}


// the max index number is 0x11 1111 1111, and it needs to include the last frozen zoom, as |0-1022 frozen | 0-1022 frozen | 0-1023 |
// the max voxel count in one grid is 1024*1024*1024
bool vcBPA_CanSlice(vcBPAManifold *pManifold, const udDouble3 boundingBoxExtents)
{  
  double largestGridSize = BPA_LEVEL_LEN * pManifold->voxelSize;
  double maxBox = udMax(udAbs(boundingBoxExtents.x), udAbs(boundingBoxExtents.y));
  maxBox = udMax(maxBox, udAbs(boundingBoxExtents.z));
  if (maxBox / largestGridSize <= BPA_LEVEL_MASK)
  {
    pManifold->baseGridSize = largestGridSize; // could work
    return true;
  }

  return false;
}
udDouble3 *vcBPA_FindPoint(vcBPAGridHashNode *pGrid, uint32_t x, uint32_t y, uint32_t z, udDouble3 &point)
{
  vcBPAVoxel *pVoxel = pGrid->voxelHashMap.FindData(x, y, z);
  if (!pVoxel) return nullptr;

  DataBlock<vcBPAVertex> *pPointArray = &pVoxel->data;
  while (pPointArray != nullptr)
  {
    for (int i = 0; i <= pPointArray->index; i++)
    {
      if (pPointArray->pBlockData[i].position == point)
        return &pPointArray->pBlockData[i].position;
    }
    pPointArray = pPointArray->pNext;
  }

  return nullptr;
}

void vcBPA_UnfrozenEdges(vcBPAGridHashNode *pDestGrid, vcBPAGridHashNode *pSourceGrid, double minx, double maxx, double miny, double maxy, double minz, double maxz, double voxelSize)
{
  vcBPAFrozenEdgeArray *pArr = pSourceGrid->pFrozenEdgesStack;
  if (pArr == nullptr) return;

  while (pArr->pTop != nullptr)
    pArr = pArr->pTop;
  do
  {
    if (pSourceGrid->frozenEdgeCount == 0) break;
    for (int32_t i = pArr->index - 1; i >= 0; i--)
    {
      if (pSourceGrid->frozenEdgeCount == 0) break;
      vcBPAFrozenEdge &frozenEdge = pArr->edges[i];
      bool p0here = (udClamp(frozenEdge.vertices[0].x, minx, maxx) != frozenEdge.vertices[0].x) && (udClamp(frozenEdge.vertices[0].y, miny, maxy) != frozenEdge.vertices[0].y) && (udClamp(frozenEdge.vertices[0].z, minz, maxz) != frozenEdge.vertices[0].z);
      bool p1here = (udClamp(frozenEdge.vertices[1].x, minx, maxx) != frozenEdge.vertices[1].x) && (udClamp(frozenEdge.vertices[1].y, miny, maxy) != frozenEdge.vertices[1].y) && (udClamp(frozenEdge.vertices[1].z, minz, maxz) != frozenEdge.vertices[1].z);
      if (p0here && p1here)
      {
        uint32_t c0x = uint32_t((frozenEdge.vertices[0].x - pDestGrid->zero.x) / voxelSize);
        uint32_t c0y = uint32_t((frozenEdge.vertices[0].y - pDestGrid->zero.y) / voxelSize);
        uint32_t c0z = uint32_t((frozenEdge.vertices[0].z - pDestGrid->zero.z) / voxelSize);
        udDouble3 *p0 = vcBPA_FindPoint(pDestGrid, c0x, c0y, c0z, frozenEdge.vertices[0]);
        if (p0 != nullptr)
        {
          uint32_t c1x = uint32_t((frozenEdge.vertices[1].x - pDestGrid->zero.x) / voxelSize);
          uint32_t c1y = uint32_t((frozenEdge.vertices[1].y - pDestGrid->zero.y) / voxelSize);
          uint32_t c1z = uint32_t((frozenEdge.vertices[1].z - pDestGrid->zero.z) / voxelSize);
          udDouble3 *p1 = vcBPA_FindPoint(pDestGrid, c1x, c1y, c1z, frozenEdge.vertices[1]);
          if (p1 != nullptr)
          {
            -- pSourceGrid->frozenEdgeCount;

            vcBPAEdgeArray *pFind = FindAvailableStackArray<vcBPAEdgeArray>(pDestGrid->pActiveEdgesStack, vcBPAEdgeArray::ElementCount);
            ++ pDestGrid->frozenEdgeCount;
            vcBPAEdge &newEdge = pFind->edges[pFind->index++];
            newEdge.vertices[0] = p0;
            newEdge.vertices[1] = p1;
            newEdge.ballCenter = frozenEdge.ballCenter;
            newEdge.triangleZ = frozenEdge.triangleZ;
          }
        }
      }
    }

    pArr = pArr->pBottom;
  } while (pArr != nullptr);

  if (pSourceGrid->frozenEdgeCount == 0)
  {
    vcBPAGridHashNode::RemoveAllEdge<vcBPAFrozenEdgeArray>(pSourceGrid->pFrozenEdgesStack);
    udFree(pSourceGrid->pFrozenEdgesStack);
  }
}

void vcBPA_RunGridPopulation(void *pDataPtr, const vcBPAData &data, vdkAttributeSet *pAttributes)
{
  printf("vcBPA_RunGridPopulation %d %d %d\n", data.gridx, data.gridy, data.gridz);

  vcBPAConvertItem *pData = (vcBPAConvertItem *)pDataPtr;
  udDouble3 halfSize = data.gridSize * 0.5;
  udDouble3 center = data.zero + halfSize;

  //------------------------------------------------------------
  // add a hash node for the new model
  vcVoxelGridHashNode *pNewModelGrid = pData->pManifold->newModelMap.AddNode(data.gridx, data.gridy, data.gridz);
  pNewModelGrid->Init();
  pNewModelGrid->zero = data.zero;
  pNewModelGrid->end = data.zero + data.gridSize;
  pNewModelGrid->vxSize = (uint32_t)((data.gridSize.x + pData->pManifold->voxelSize - UD_EPSILON) / pData->pManifold->voxelSize);
  pNewModelGrid->vySize = (uint32_t)((data.gridSize.y + pData->pManifold->voxelSize - UD_EPSILON) / pData->pManifold->voxelSize);
  pNewModelGrid->vzSize = (uint32_t)((data.gridSize.z + pData->pManifold->voxelSize - UD_EPSILON) / pData->pManifold->voxelSize);

  vdkPointBufferF64_Create(&pNewModelGrid->pBuffer, MAX_POINTNUM, pAttributes);
  vcBPA_QueryPoints(pData->pManifold->pContext, pData->pNewModel, &center.x, &halfSize.x, pNewModelGrid->pBuffer);

  double _time = udGetEpochMilliSecsUTCf();
  for (uint32_t j = 0; j < pNewModelGrid->pBuffer->pointCount; ++j)
    vcBPA_AddPoints(j, pNewModelGrid->pBuffer->pPositions[j * 3 + 0], pNewModelGrid->pBuffer->pPositions[j * 3 + 1], pNewModelGrid->pBuffer->pPositions[j * 3 + 2], pNewModelGrid->zero, &pNewModelGrid->voxelHashMap, pData->pManifold->voxelSize);
  pNewModelGrid->pointNum = pNewModelGrid->pBuffer->pointCount;

  _time = udGetEpochMilliSecsUTCf() - _time;
  printf("vcBPA_AddPoints from new model: num: %d, time costs: %f ms %f s %f min\n", pNewModelGrid->pBuffer->pointCount, _time, _time/1000, _time/60000);

  
  // get points in the grid of old model, if empty, skip
  vdkPointBufferF64 *pBuffer;
  vdkPointBufferF64_Create(&pBuffer, MAX_POINTNUM, nullptr);
  vcBPA_QueryPoints(pData->pManifold->pContext, pData->pOldModel, &center.x, &halfSize.x, pBuffer);
  if (pBuffer->pointCount == 0)
  {
    vdkPointBufferF64_Destroy(&pBuffer);

    vcBPAConvertItemData item = {};
    item.pManifold = pData->pManifold;
    item.pNewModelGrid = pNewModelGrid;
    item.pOldModelGrid = nullptr;
    item.gridx = data.gridx;
    item.gridy = data.gridy;
    item.gridz = data.gridz;
    item.leftPoint = pNewModelGrid->pointNum;
    item.pOldModel = pData->pOldModel;
    udSafeDeque_PushBack(pData->pConvertItemData, item);

    return;
  }

  vcBPAGridHashNode *pOldModelGrid = pData->pManifold->oldModelMap.AddNode(data.gridx, data.gridy, data.gridz);
  pOldModelGrid->Init();
  pOldModelGrid->pBuffer = pBuffer;
  pOldModelGrid->zero = pNewModelGrid->zero;
  pOldModelGrid->end = pNewModelGrid->end;

  //add frozen area
  if (data.gridx > 0) pOldModelGrid->zero.x -= pData->pManifold->voxelSize;
  if (data.gridy > 0) pOldModelGrid->zero.y -= pData->pManifold->voxelSize;
  if (data.gridz > 0) pOldModelGrid->zero.z -= pData->pManifold->voxelSize;
  pOldModelGrid->vxSize = (uint32_t)((pOldModelGrid->end.x - pOldModelGrid->zero.x + pData->pManifold->voxelSize - UD_EPSILON) / pData->pManifold->voxelSize);
  pOldModelGrid->vySize = (uint32_t)((pOldModelGrid->end.y - pOldModelGrid->zero.y + pData->pManifold->voxelSize - UD_EPSILON) / pData->pManifold->voxelSize);
  pOldModelGrid->vzSize = (uint32_t)((pOldModelGrid->end.z - pOldModelGrid->zero.z + pData->pManifold->voxelSize - UD_EPSILON) / pData->pManifold->voxelSize);

  _time = udGetEpochMilliSecsUTCf();
  for (uint32_t j = 0; j < pOldModelGrid->pBuffer->pointCount; ++j)
    vcBPA_AddPoints(j, pOldModelGrid->pBuffer->pPositions[j * 3 + 0], pOldModelGrid->pBuffer->pPositions[j * 3 + 1], pOldModelGrid->pBuffer->pPositions[j * 3 + 2], pOldModelGrid->zero, &pOldModelGrid->voxelHashMap, pData->pManifold->voxelSize);
  pOldModelGrid->pointNum = pOldModelGrid->pBuffer->pointCount;

  _time = udGetEpochMilliSecsUTCf() - _time;
  printf("vcBPA_AddPoints from old model: num: %d, time costs: %f ms %f s %f min\n", pOldModelGrid->pBuffer->pointCount, _time, _time / 1000, _time / 60000);

  if (data.gridx > 0)
  {
    vcBPAGridHashNode *lastX = pData->pManifold->oldModelMap.FindData(data.gridx - 1, data.gridy, data.gridz);
    if (lastX != nullptr)
      vcBPA_UnfrozenEdges(pOldModelGrid, lastX, pOldModelGrid->zero.x, data.zero.x, lastX->zero.y, lastX->zero.y + pData->pManifold->baseGridSize, lastX->zero.z, lastX->zero.z + pData->pManifold->baseGridSize, pData->pManifold->voxelSize);
  }

  if (data.gridy > 0)
  {
    vcBPAGridHashNode *lastY = pData->pManifold->oldModelMap.FindData(data.gridx, data.gridy - 1, data.gridz);
    if (lastY != nullptr)
      vcBPA_UnfrozenEdges(pOldModelGrid, lastY, lastY->zero.x, lastY->zero.x + pData->pManifold->baseGridSize - pData->pManifold->voxelSize, pOldModelGrid->zero.y, data.zero.y, lastY->zero.z, lastY->zero.z + pData->pManifold->baseGridSize - pData->pManifold->voxelSize, pData->pManifold->voxelSize);
  }

  if (data.gridz > 0)
  {
    vcBPAGridHashNode *lastZ = pData->pManifold->oldModelMap.FindData(data.gridx, data.gridy, data.gridz - 1);
    vcBPA_UnfrozenEdges(pOldModelGrid, lastZ, lastZ->zero.x, lastZ->zero.x + pData->pManifold->baseGridSize - pData->pManifold->voxelSize, lastZ->zero.y, lastZ->zero.y + pData->pManifold->baseGridSize, pOldModelGrid->zero.z, data.zero.z, pData->pManifold->voxelSize);
  }

  vcBPA_DoGrid(pDataPtr, pOldModelGrid, pData->pManifold->ballRadius, pData->pManifold->voxelSize, data.gridx, data.gridy, data.gridz, data.gridXSize, data.gridYSize, data.gridZSize);
  vcBPAGridHashNode::CleanBPAData(pOldModelGrid);

  printf("vcBPA_DoGrid done. triangleSize:%d. \n", pOldModelGrid->triangleSize);

  vcBPAConvertItemData item = {};
  item.pManifold = pData->pManifold;
  item.pNewModelGrid = pNewModelGrid;
  item.pOldModelGrid = pOldModelGrid;
  item.gridx = data.gridx;
  item.gridy = data.gridy;
  item.gridz = data.gridz;
  item.leftPoint = pNewModelGrid->pointNum;
  item.pOldModel = pData->pOldModel;
  udSafeDeque_PushBack(pData->pConvertItemData, item);

}

uint32_t vcBPA_ProcessThread(void *pDataPtr)
{
  printf("vcBPA_ProcessThread \n");
  vcBPAConvertItem *pData = (vcBPAConvertItem *)pDataPtr;

  // data from new model
  vdkPointCloudHeader header = {};
  vdkPointCloud_GetHeader(pData->pNewModel, &header);
  udDouble4x4 m_sceneMatrix = udDouble4x4::create(header.storedMatrix);
  udDouble3 localZero = udDouble3::create(header.boundingBoxCenter[0] - header.boundingBoxExtents[0], header.boundingBoxCenter[1] - header.boundingBoxExtents[1], header.boundingBoxCenter[2] - header.boundingBoxExtents[2]);
  udDouble3 unitSpaceExtents = udDouble3::create(header.boundingBoxExtents[0] * 2, header.boundingBoxExtents[1] * 2, header.boundingBoxExtents[2] * 2);
  udDouble3 newModelExtents = unitSpaceExtents * udDouble3::create(udMag3(m_sceneMatrix.axis.x), udMag3(m_sceneMatrix.axis.y), udMag3(m_sceneMatrix.axis.z));
  udDouble3 newModelZero = (m_sceneMatrix * udDouble4::create(localZero, 1.0)).toVector3();
  udDouble3 newModelCenter = (m_sceneMatrix * udDouble4::create(header.boundingBoxCenter[0], header.boundingBoxCenter[1], header.boundingBoxCenter[2], 1.0)).toVector3();

  //try to slice
  if (!vcBPA_CanSlice(pData->pManifold, newModelExtents))
  {
    printf("slice failed, release pManifold \n");

    pData->pManifold->Deinit();
    udFree(pData->pManifold);

    pData->running.Set(vcBPARS_Failed);
    return 0;
  } 

  uint32_t gridXSize = (uint32_t)((newModelExtents.x + pData->pManifold->baseGridSize - UD_EPSILON) / pData->pManifold->baseGridSize);
  uint32_t gridYSize = (uint32_t)((newModelExtents.y + pData->pManifold->baseGridSize - UD_EPSILON) / pData->pManifold->baseGridSize);
  uint32_t gridZSize = (uint32_t)((newModelExtents.z + pData->pManifold->baseGridSize - UD_EPSILON) / pData->pManifold->baseGridSize);

  printf("slice success: gridsize %f gridXSize %d gridYSize %d gridZSize %d \n", pData->pManifold->baseGridSize, gridXSize, gridYSize, gridZSize);

  static const int NUM = 1;
  vdkPointBufferF64 *pBuffer = nullptr;
  vdkPointBufferF64_Create(&pBuffer, NUM, nullptr);

  udDouble3 zero;
  udDouble3 gridSize;
  uint32_t gridx = 0;
  uint32_t gridy = 0;
  uint32_t gridz = 0;
  for (gridx = 0, zero.x = newModelZero.x; gridx < gridXSize; gridx++, zero.x += pData->pManifold->baseGridSize)
  {
    // real grid x size
    gridSize.x = udMin(pData->pManifold->baseGridSize, newModelExtents.x - zero.x);
    for (gridy = 0, zero.y = newModelZero.y; gridy < gridYSize; gridy++, zero.y += pData->pManifold->baseGridSize)
    {
      // real grid y size
      gridSize.y = udMin(pData->pManifold->baseGridSize, newModelExtents.y - zero.y);
      for (gridz = 0, zero.z = newModelZero.z; gridz < gridZSize; gridz++, zero.z += pData->pManifold->baseGridSize)
      {
        if (pData->running.Get() != vcBPARS_Active)
          break;

        printf("running: %s check grid(%d, %d, %d)\n", (pData->running.Get() == vcBPARS_Active) ? "true" : "false" , gridx, gridy, gridz);

        // real grid z size
        gridSize.z = udMin(pData->pManifold->baseGridSize, newModelExtents.z - zero.z);
        udDouble3 halfSize = gridSize * 0.5;
        udDouble3 center = zero + halfSize;

        // Don't descend if there's no data        
        vcBPA_QueryPoints(pData->pManifold->pContext, pData->pNewModel, &center.x, &halfSize.x, pBuffer);        
        if (0 == pBuffer->pointCount)
        {
          printf("no points \n");
          continue;
        }          

        // run grid BPA
        vcBPAData data;
        data.zero = zero;
        data.gridSize = gridSize;
        data.gridx = gridx;
        data.gridy = gridy;
        data.gridz = gridz;
        data.gridXSize = gridXSize;
        data.gridYSize = gridYSize;
        data.gridZSize = gridZSize;
        vcBPA_RunGridPopulation(pDataPtr, data, &header.attributes);
      }
    }      
  }

  vdkPointBufferF64_Destroy(&pBuffer);

  // done
  if (pData->running.Get() == vcBPARS_Active && gridx == gridXSize && gridy == gridYSize && gridz == gridZSize)
  {
    vcBPAConvertItemData data = {};
    data.pManifold = pData->pManifold;
    data.pNewModelGrid = nullptr;
    data.pOldModelGrid = nullptr;
    data.pOldModel = pData->pOldModel;
    udSafeDeque_PushBack(pData->pConvertItemData, data);
  }    
  else
  {
    if (pData->running.Get() == vcBPARS_Active)
      pData->running.Set(vcBPARS_Failed);

    pData->pManifold->Deinit();
    udFree(pData->pManifold);      
  }

  return 0;
}

vdkError vcBPA_ConvertOpen(vdkConvertCustomItem *pConvertInput, uint32_t everyNth, const double origin[3], double pointResolution, vdkConvertCustomItemFlags flags)
{
  printf("vcBPA_ConvertOpen \n");

  udUnused(everyNth);
  udUnused(origin);
  udUnused(pointResolution);
  udUnused(flags);

  vcBPAConvertItem *pData = (vcBPAConvertItem*)pConvertInput->pData;
  udSafeDeque_Create(&pData->pConvertItemData, 128);

  pData->pManifold = udAllocType(vcBPAManifold, 1, udAF_Zero);
  pData->pManifold->Init();
  udWorkerPool_Create(&pData->pManifold->pPool, (uint8_t)udGetHardwareThreadCount(), "vcBPAPool");
  pData->pManifold->pContext = pData->pContext;
  pData->pManifold->ballRadius = pData->ballRadius;
  pData->pManifold->voxelSize = pData->ballRadius * 2; // d = 2r   

  udThread_Create(&pData->pThread, vcBPA_ProcessThread, pData, udTCF_None, "BPAGridGeneratorThread");
  return vE_Success;
}


vcBPATriangle *vcBPA_FindClosestTriangle(double &minDistance, vcBPAGridHashNode *pGrid, udDouble3 &position, uint32_t x, uint32_t y, uint32_t z, udDouble3 *cloestPoint)
{
  int32_t vcx = (int32_t)x;
  int32_t vcy = (int32_t)y;
  int32_t vcz = (int32_t)z;

  vcBPATriangle *find = nullptr;

  for (int32_t vx = udMax(vcx - 1, 0); vx <= udMin(vcx + 1, pGrid->vxSize - 1); vx++)
  {
    for (int32_t vy = udMax(vcy - 1, 0); vy <= udMin(vcy + 1, pGrid->vySize - 1); vy++)
    {
      for (int32_t vz = udMax(vcz - 1, 0); vz <= udMin(vcz + 1, pGrid->vzSize - 1); vz++)
      {
        vcBPATriangleArray *pVoxel = pGrid->triangleHashMap.FindData(vx, vy, vz);
        if (pVoxel == nullptr)
          continue;

        // check all points
        DataBlock<vcBPATriangle> *pArray = &pVoxel->data;
        while (pArray != nullptr)
        {
          for (int i = 0; i <= pArray->index; i++)
          {
            vcBPATriangle *t = &pArray->pBlockData[i];
            double distance = udDistanceToTriangle(t->vertices[0], t->vertices[1], t->vertices[2], position, cloestPoint);
            if (distance < minDistance)
            {
              find = t;
              minDistance = distance;
            }
          }
          pArray = pArray->pNext;
        }
      }
    }
  }

  return find;
}

vdkError vcBPA_ConvertReadPoints(vdkConvertCustomItem *pConvertInput, vdkPointBufferF64 *pBuffer)
{
  printf("pBuffer->pointsAllocated: %d pBuffer->pointCount: %d\n", pBuffer->pointsAllocated, pBuffer->pointCount);

  vcBPAConvertItem *pData = (vcBPAConvertItem *)pConvertInput->pData;
  uint32_t toFill = pBuffer->pointsAllocated - pBuffer->pointCount;
  uint32_t canRead = 0;

  if (toFill == 0)
  {
    memset(pBuffer->pAttributes, 0, pBuffer->attributeStride * pBuffer->pointsAllocated);
    pBuffer->pointCount = 0;
    toFill = pBuffer->pointsAllocated;
  }

  if (pData->pActiveItem == nullptr)
  {
    pData->processInfo = {};
    pData->pActiveItem = udAllocType(vcBPAConvertItemData, 1, udAF_Zero);
    do 
    {
      if (udSafeDeque_PopFront(pData->pConvertItemData, pData->pActiveItem) == udR_Success)
      {
        canRead = pData->pActiveItem->leftPoint;
        if (canRead > 0)
        {
          printf("new block %d can read\n", canRead);
          break;
        }

        // done
        if (pData->pActiveItem->pNewModelGrid == nullptr)
        {
          udFree(pData->pActiveItem);
          pData->running.Set(vcBPARS_Success);
          return vE_Success;
        }

      }
      
      udSleep(100);

    } while (pData->running.Get() == vcBPARS_Active);
   
  }

  canRead = udMin(canRead, toFill);
  pData->pActiveItem->leftPoint -= canRead;
  pBuffer->pointCount += canRead;

  uint32_t displacementOffset = 0;
  udUInt3 displacementDistanceOffset = {};
  vdkError error = vE_Failure;

  error = vdkAttributeSet_GetOffsetOfNamedAttribute(&pBuffer->attributes, "udDisplacement", &displacementOffset);
  if (error != vE_Success)
    return error;

  error = vdkAttributeSet_GetOffsetOfNamedAttribute(&pBuffer->attributes, "udDisplacementDirectionX", &displacementDistanceOffset.x);
  if (error != vE_Success)
    return error;

  error = vdkAttributeSet_GetOffsetOfNamedAttribute(&pBuffer->attributes, "udDisplacementDirectionY", &displacementDistanceOffset.y);
  if (error != vE_Success)
    return error;

  error = vdkAttributeSet_GetOffsetOfNamedAttribute(&pBuffer->attributes, "udDisplacementDirectionZ", &displacementDistanceOffset.z);
  if (error != vE_Success)
    return error;

  vcVoxelGridHashNode *pNewModelGrid = pData->pActiveItem->pNewModelGrid;
  for (; pData->processInfo.voxelX < pNewModelGrid->vxSize; ++pData->processInfo.voxelX)
  {
    for (; pData->processInfo.voxelY < pNewModelGrid->vySize; ++pData->processInfo.voxelY)
    {
      for (; pData->processInfo.voxelZ < pNewModelGrid->vzSize; ++pData->processInfo.voxelZ)
      {
        // to read voxel one by one until get enough 'canRead' points
        if (pData->processInfo.pArray == nullptr)
        {
          vcBPAVoxel *pVoxel = pNewModelGrid->voxelHashMap.FindData(pData->processInfo.voxelX, pData->processInfo.voxelY, pData->processInfo.voxelZ);
          if (pVoxel == nullptr)
            continue;
          pData->processInfo.pArray = udAllocType(vcBPAVertex *, pVoxel->pointNum, udAF_Zero);
          pVoxel->ToArray(pData->processInfo.pArray);
          pData->processInfo.currIndex = 0;
          pData->processInfo.arrayLen = pVoxel->pointNum;
        }

        for (; pData->processInfo.currIndex < pData->processInfo.arrayLen; pData->processInfo.currIndex++)
        {
          vcBPAVertex *pPoint = pData->processInfo.pArray[pData->processInfo.currIndex];

          double distance = FLT_MAX;
          udDouble3 cloestPoint = {};
          vcBPATriangle *t = vcBPA_FindClosestTriangle(distance, pData->pActiveItem->pOldModelGrid, pPoint->position, pData->processInfo.voxelX, pData->processInfo.voxelY, pData->processInfo.voxelZ, &cloestPoint);
          
          if (t != nullptr)
          {
            // new point
            udDouble3 normal = vcBPA_GetTriangleNormal(t->vertices[0], t->vertices[1], t->vertices[2]);
            udDouble3 p0_to_position = pPoint->position - t->vertices[0];
            if (udDot3(p0_to_position, normal) < 0.0)
              distance = -distance;
          }

          // Position XYZ
          memcpy(&pBuffer->pPositions[pBuffer->pointCount * 3], &pNewModelGrid->pBuffer->pPositions[pPoint->j * 3], sizeof(double) * 3);

          // Copy all of the original attributes
          vdkAttributeDescriptor &oldAttrDesc = pNewModelGrid->pBuffer->attributes.pDescriptors[pPoint->j];
          uint32_t attributeSize = (oldAttrDesc.typeInfo & (vdkAttributeTypeInfo_SizeMask << vdkAttributeTypeInfo_SizeShift));

          // Get attribute old offset and pointer
          uint32_t attrOldOffset = 0;
          vdkAttributeSet_GetOffsetOfNamedAttribute(&pNewModelGrid->pBuffer->attributes, oldAttrDesc.name, &attrOldOffset);
          void *pOldAttr = udAddBytes(pNewModelGrid->pBuffer->pAttributes, attrOldOffset);

          // Get attribute new offset and pointer
          uint32_t attrNewOffset = 0;
          vdkAttributeSet_GetOffsetOfNamedAttribute(&pBuffer->attributes, oldAttrDesc.name, &attrNewOffset);

          void *pNewAttr = udAddBytes(pBuffer->pAttributes, attrNewOffset);
          // Copy attribute data
          memcpy(pNewAttr, pOldAttr, attributeSize);

          // Displacement
          float *pDisplacement = (float *)udAddBytes(pBuffer->pAttributes, displacementOffset);
          *pDisplacement = (float)distance;

          for (int elementIndex = 0; elementIndex < 3; ++elementIndex) //X,Y,Z
          {
            float *pDisplacementDistance = (float *)udAddBytes(pBuffer->pAttributes, displacementDistanceOffset[elementIndex]);
            if (distance != FLT_MAX)
              *pDisplacementDistance = (float)((cloestPoint[elementIndex] - pPoint->position[elementIndex]) / distance);
            else
              *pDisplacementDistance = 0.0;
          }

          ++pBuffer->pointCount;
          
          canRead--;
          if (canRead == 0)
            goto check;
        }

        udFree(pData->processInfo.pArray);
        pData->processInfo.currIndex = 0;
      }
    }
  }
    
check:

  if (pData->processInfo.voxelX == pNewModelGrid->vxSize && pData->processInfo.voxelY == pNewModelGrid->vySize && pData->processInfo.voxelZ == pNewModelGrid->vzSize)
    udFree(pData->pActiveItem);

  return vE_Pending;

}

void vcBPA_ConvertClose(vdkConvertCustomItem *pConvertInput)
{
  printf("vcBPA_ConvertClose \n");

  vcBPAConvertItem *pData = (vcBPAConvertItem *)pConvertInput->pData;
  if (pData->running.Get() == vcBPARS_Active)
  {
    pData->running.Set(vcBPARS_Cancel);
    return;
  }  
}

void vcBPA_ConvertDestroy(vdkConvertCustomItem *pConvertInput)
{
  printf("vcBPA_ConvertDestroy \n");

  vcBPAConvertItem *pData = (vcBPAConvertItem *)pConvertInput->pData;

  udThread_Join(pData->pThread);
  udThread_Destroy(&pData->pThread);
  pData->pActiveItem = {};
  udSafeDeque_Destroy(&pData->pConvertItemData);

  if (pData->running.Get() != vcBPARS_End)
  {
    pData->running.Set(vcBPARS_End);
    pData->pManifold->Deinit();
    udFree(pData->pManifold);
  }

  vcBPAConvertItem *pBPA = (vcBPAConvertItem*)pConvertInput->pData;
  vdkPointCloud_Unload(&pBPA->pOldModel);
  vdkPointCloud_Unload(&pBPA->pNewModel);
  vdkAttributeSet_Free(&pConvertInput->attributes);
  udFree(pConvertInput->pData);
}




void vcBPA_CompareExport(vcState *pProgramState, const char *pOldModelPath, const char *pNewModelPath, double ballRadius, double gridSize, const char *pName)
{
  printf("vcBPA_CompareExport \n");

  vcConvertItem *pConvertItem = nullptr;
  vcConvert_AddEmptyJob(pProgramState, &pConvertItem);

  udLockMutex(pConvertItem->pMutex);

  vdkPointCloudHeader header = {};

  vcBPAConvertItem *pBPA = udAllocType(vcBPAConvertItem, 1, udAF_Zero);
  pBPA->pContext = pProgramState->pVDKContext;
  vdkPointCloud_Load(pBPA->pContext, &pBPA->pOldModel, pOldModelPath, nullptr);
  vdkPointCloud_Load(pBPA->pContext, &pBPA->pNewModel, pNewModelPath, &header);
  pBPA->pConvertItem = pConvertItem;
  pBPA->running.Set(vcBPARS_Active);
  pBPA->ballRadius = ballRadius;
  pBPA->gridSize = gridSize; // metres

  udDouble4x4 storedMatrix = udDouble4x4::create(header.storedMatrix);
  udDouble3 boundingBoxCenter = udDouble3::create(header.boundingBoxCenter[0], header.boundingBoxCenter[1], header.boundingBoxCenter[2]);
  udDouble3 boundingBoxExtents = udDouble3::create(header.boundingBoxExtents[0], header.boundingBoxExtents[1], header.boundingBoxExtents[2]);

  const char *pMetadata = nullptr;
  vdkPointCloud_GetMetadata(pBPA->pNewModel, &pMetadata);
  udJSON metadata = {};
  metadata.Parse(pMetadata);

  for (uint32_t i = 0; i < metadata.MemberCount() ; ++i)
  {
    const udJSON *pElement = metadata.GetMember(i);
    // Removed error checking because convertInfo metadata triggers vE_NotSupported
    vdkConvert_SetMetadata(pConvertItem->pConvertContext, metadata.GetMemberName(i), pElement->AsString());
  }

  vdkConvertCustomItem item = {};
  item.pName = pName;

  uint32_t displacementOffset = 0;
  bool addDisplacement = true;

  uint32_t displacementDirectionOffset = 0;
  bool addDisplacementDirection = true;

  if (vdkAttributeSet_GetOffsetOfNamedAttribute(&header.attributes, "udDisplacement", &displacementOffset) == vE_Success)
    addDisplacement = false;

  if (vdkAttributeSet_GetOffsetOfNamedAttribute(&header.attributes, "udDisplacementDirectionX", &displacementDirectionOffset) == vE_Success)
    addDisplacementDirection = false;

  vdkAttributeSet_Generate(&item.attributes, vdkSAC_None, header.attributes.count + (addDisplacement ? 1 : 0) + (addDisplacementDirection ? 3 : 0));

  for (uint32_t i = 0; i < header.attributes.count; ++i)
  {
    item.attributes.pDescriptors[i].blendMode = header.attributes.pDescriptors[i].blendMode;
    item.attributes.pDescriptors[i].typeInfo = header.attributes.pDescriptors[i].typeInfo;
    udStrcpy(item.attributes.pDescriptors[i].name, header.attributes.pDescriptors[i].name);
    ++item.attributes.count;
  }

  if (addDisplacement)
  {
    item.attributes.pDescriptors[item.attributes.count].blendMode = vdkABM_SingleValue;
    item.attributes.pDescriptors[item.attributes.count].typeInfo = vdkAttributeTypeInfo_float32;
    udStrcpy(item.attributes.pDescriptors[item.attributes.count].name, "udDisplacement");
    ++item.attributes.count;
  }

  if (addDisplacementDirection)
  {
    item.attributes.pDescriptors[item.attributes.count].blendMode = vdkABM_SingleValue;
    item.attributes.pDescriptors[item.attributes.count].typeInfo = vdkAttributeTypeInfo_float32;
    udStrcpy(item.attributes.pDescriptors[item.attributes.count].name, "udDisplacementDirectionX");
    ++item.attributes.count;

    item.attributes.pDescriptors[item.attributes.count].blendMode = vdkABM_SingleValue;
    item.attributes.pDescriptors[item.attributes.count].typeInfo = vdkAttributeTypeInfo_float32;
    udStrcpy(item.attributes.pDescriptors[item.attributes.count].name, "udDisplacementDirectionY");
    ++item.attributes.count;

    item.attributes.pDescriptors[item.attributes.count].blendMode = vdkABM_SingleValue;
    item.attributes.pDescriptors[item.attributes.count].typeInfo = vdkAttributeTypeInfo_float32;
    udStrcpy(item.attributes.pDescriptors[item.attributes.count].name, "udDisplacementDirectionZ");
    ++item.attributes.count;
  }

  item.sourceResolution = header.convertedResolution;
  item.pointCount = metadata.Get("UniquePointCount").AsInt64(); // This will need a small scale applied (~1.2 seems to be correct for models pfox tested)
  item.pointCountIsEstimate = true;
  item.pData = pBPA;
  item.pOpen = vcBPA_ConvertOpen;
  item.pReadPointsFloat = vcBPA_ConvertReadPoints;
  item.pClose = vcBPA_ConvertClose;
  item.pDestroy = vcBPA_ConvertDestroy;
  udDouble4 temp = storedMatrix * udDouble4::create(boundingBoxCenter - boundingBoxExtents, 1.0);
  for (uint32_t i = 0; i < udLengthOf(item.boundMin); ++i)
    item.boundMin[i] = temp[i];

  temp = storedMatrix * udDouble4::create(boundingBoxCenter + boundingBoxExtents, 1.0);
  for (uint32_t i = 0; i < udLengthOf(item.boundMax); ++i)
    item.boundMax[i] = temp[i];

  item.boundsKnown = true;
  vdkConvert_AddCustomItem(pConvertItem->pConvertContext, &item);

  udFree(item.pName);
  udReleaseMutex(pBPA->pConvertItem->pMutex);
}

#endif //VC_HASCONVERT

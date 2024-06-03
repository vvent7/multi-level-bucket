/*
 * Multi-level bucket heap by Fernando Ventilari
 * May 2024
 */

#ifndef _MLB_H_
#define _MLB_H_

#include <utility> // std::pair

namespace mlb {

#define NEXT(pNode) ((pNode)->sBckInfo.next)
#define PREV(pNode) ((pNode)->sBckInfo.prev)
#define BUCKET(pNode) ((pNode)->sBckInfo.bucket)

#ifdef STATS  // expensive stats to calculate
#define EMPTY_BUCKET ++statEmpty
#define EXPANDED_NODE ++statExpandedNodes
#define EXPANDED_BUCKET ++statExpandedBuckets
#define INSERT_TO_BUCKET ++statInsert
#define POS_EVAL ++statPosEval
#else
#define EMPTY_BUCKET
#define EXPANDED_NODE
#define EXPANDED_BUCKET
#define INSERT_TO_BUCKET
#define POS_EVAL
#endif

template <typename key_t, typename data_t>
struct Node;

template <typename key_t, typename data_t>
struct Bucket;

template <typename key_t, typename data_t>
struct Level;

template <typename key_t, typename data_t>
struct Node {
  key_t dist;
  data_t data;

  struct {
    Node<key_t, data_t> *next;      // next in bucket
    Node<key_t, data_t> *prev;      // prev in bucket
    Bucket<key_t, data_t> *bucket;  // you should cast this
  } sBckInfo;

  Node() : dist(0), data(0) {}
  Node(key_t dist, data_t data) : dist(dist), data(data) {}
};

template <typename key_t, typename data_t>
struct Bucket {
  Node<key_t, data_t> *pNode;    // list of nodes at this level (circular)
  Level<key_t, data_t> *pLevel;  // what level this bucket is on
};

template <typename key_t, typename data_t>
struct Level {
  unsigned long cNodes;  // number of nodes currently stored at this level
  Bucket<key_t, data_t> *rgBin;  // points to the cBuckets buckets at our level
  Bucket<key_t, data_t> *pBucket;  // the current bucket at level i
  unsigned long digShift;          // shifting distance and the applying
  unsigned long digMask;           // digMask gives the digit
};

// md = LEVEL: param = number of levels
// md = LOG_DELTA: param = log_2(delta)
// md = NONE: param is ignored
enum Mode { LEVEL, LOG_DELTA, NONE };

template <typename key_t, typename data_t>
class MultiLevelBucketHeap {
  using _Node = Node<key_t, data_t>;
  using _Bucket = Bucket<key_t, data_t>;
  using _Level = Level<key_t, data_t>;

 public:
  MultiLevelBucketHeap(key_t minKeyVariation, key_t maxKeyVariation,
                       enum Mode md, unsigned long param) {
    // logBottom = floor(log_2(minKeyVariation))
    logBottom = 0;
    while ((1ULL << logBottom) < minKeyVariation) ++logBottom;

    // 2^logMax > maxKeyVariation -> logMax = floor(log_2(maxKeyVariation)) + 1
    unsigned long logMax = 1;
    while ((1ULL << logMax) <= maxKeyVariation) ++logMax;

    // delta^k * minKeyVariation >= 2^logMax > maxKeyVariation
    switch (md) {
      case LEVEL: {  // param is number of levels
        kLevels = param;
        logDelta = 1;
        while (logDelta * kLevels + logBottom < logMax) ++logDelta;
        break;
      }
      case LOG_DELTA: {  // param is log2(delta)
        kLevels = 0;
        logDelta = param;
        while (logDelta * kLevels + logBottom < logMax) ++kLevels;
        break;
      }
      case NONE:
      default: {
        // optimize kLevels and delta for the worst case
        // RHO*kLevels ~= delta
        // rho = log(RHO)
        unsigned long rho = 4;  // adjustable

        if (logMax - logBottom <= rho) {
          kLevels = 1;
          logDelta = logMax - logBottom;
          assert(logDelta > 0);
        }
        else {
          logDelta = rho;
          kLevels = 1UL << (logDelta - rho);  // = delta/RHO
          while (logDelta * kLevels + logBottom < logMax) {
            logDelta++;
            kLevels = 1UL << (logDelta - rho);  // = delta/RHO
          }

          // kLevels and logDelta should not be too big
          while (logDelta * kLevels + logBottom >= logMax) --kLevels;
          ++kLevels;

          while (logDelta * kLevels + logBottom >= logMax) --logDelta;
          ++logDelta;
        }
      }
    }

    // printf("c lengths min=%lld max=%lld; delta=%d levels=%ld\n",
    //        minKeyVariation, maxKeyVariation, 1 << logDelta, kLevels);
    // printf("c logMax=%ld logBottom=%ld\n", logMax, logBottom);

    logTopDelta = logDelta + 1;

    // ulong i;

    relBitMask = 0;
    for (unsigned long i = 1; i <= (kLevels - 1) * logDelta + logTopDelta; ++i)
      relBitMask = 1 + (relBitMask << 1);

    delta = (1UL << logDelta);
    topDelta = (1UL << logTopDelta);

    // initialize levels
    rgLevels = new _Level[kLevels + 1];  // a pointer may run one over topLevel
    assert(rgLevels);
    topLevel = rgLevels + kLevels - 1;

    // Level *pLevel;
    for (_Level *pLevel = rgLevels; pLevel < topLevel; pLevel++) {
      pLevel->rgBin = new _Bucket[delta];
      for (unsigned long i = 0; i < delta; ++i)
        pLevel->rgBin[i].pLevel = pLevel;  // store level info
                                           // do shifts and masks
      pLevel->digShift = logBottom + logDelta * (pLevel - rgLevels);
      // set relevant bit mask
      pLevel->digMask = 0;
      for (unsigned long i = 0; i < logDelta; ++i)
        pLevel->digMask = 1 + ((pLevel->digMask) << 1);
    }
    // now the top level
    topLevel->rgBin = new _Bucket[topDelta];
    for (unsigned long i = 0; i < topDelta; ++i)
      topLevel->rgBin[i].pLevel = topLevel;  // store level info
    topLevel->digShift = logBottom + logDelta * (topLevel - rgLevels);
    topLevel->digMask = 0;
    for (unsigned long i = 0; i < logTopDelta; ++i)
      topLevel->digMask = 1 + ((topLevel->digMask) << 1);

    Init();
  }

  void Init() {  // Reset Structure
    for (_Level *pLevel = rgLevels; pLevel <= topLevel; ++pLevel) {
      pLevel->cNodes = 0;
      pLevel->pBucket = pLevel->rgBin;  // curr bucket is leftmost
      if (pLevel != topLevel)
        for (unsigned long iBucket = 0; iBucket < delta; ++iBucket)
          pLevel->rgBin[iBucket].pNode = NULL;
      else
        for (unsigned long iBucket = 0; iBucket < topDelta; ++iBucket)
          pLevel->rgBin[iBucket].pNode = NULL;
    }
    minLevel = topLevel;

#ifdef STATS
    statEmpty = 0;
    statExpandedNodes = 0;
    statExpandedBuckets = 0;
    statInsert = 0;
    statPosEval = 0;
#endif
  }

  ~MultiLevelBucketHeap() {
    for (_Level *pLevel = rgLevels; pLevel <= topLevel; pLevel++){
      for(_Bucket *pBucket = pLevel->rgBin; pBucket < pLevel->rgBin + (pLevel == topLevel ? topDelta : delta); ++pBucket){
        if(pBucket->pNode)
          delete extract(pBucket->pNode);
      }
      delete pLevel->rgBin;
    }
    delete rgLevels;
  }

  size_t size() const { return sz; }

  bool empty() const { return sz == 0; }

  _Node *insert(key_t key, data_t data) {
    _Bucket *bckNew = DistToBucket(&key, DistToLevel(&key));
    _Node *node = new _Node(key, data);
    ++sz;
    return place(node, bckNew);
  }

  void erase(_Node *node) { delete extract(node); --sz; }

  void change_key(_Node *node, key_t new_key) {
    _Bucket *bckNew = DistToBucket(&new_key, DistToLevel(&new_key));
    Move(node, bckNew);
    node->dist = new_key;
  }

  bool decrease_key(_Node *node, key_t new_key) {
    if (new_key >= node->dist) return false;
    change_key(node, new_key);
    return true;
  }

  std::pair<key_t, data_t> extract_min() {
    while ((!minLevel->cNodes) && (minLevel <= topLevel)) ++minLevel;

    if (minLevel > topLevel) {
      minLevel = topLevel;
      return {-1,-1};
    }

    _Level *pLevel = minLevel;
    assert(pLevel->cNodes);

    // find first nonempty bucket
    if (pLevel->pBucket->pNode == NULL) {  // empty (current min) bucket
      if (pLevel < topLevel) {
        assert(DistToBucket(&mu, pLevel) == pLevel->pBucket);
        do {
          EMPTY_BUCKET;
          ++(pLevel->pBucket);
        } while (pLevel->pBucket->pNode == NULL);
        assert(pLevel->pBucket - pLevel->rgBin < (long)delta);
      }
      else {
        do {
          EMPTY_BUCKET;
          if (pLevel->pBucket - pLevel->rgBin < (long)topDelta - 1)
            ++(pLevel->pBucket);
          else
            pLevel->pBucket = pLevel->rgBin;
        } while (pLevel->pBucket->pNode == NULL);
      }
    }

    assert(pLevel->pBucket != NULL);

    _Node *ans;
    if (pLevel == rgLevels) {  // bootom level (special case)
      ans = extract(pLevel->pBucket->pNode);
      assert(mu <= ans->dist);
      // if logBottom > 0, need to erase last bits
      mu = (ans->dist >> logBottom) << logBottom;
    }
    else {
      // do other levels all the same.
      ans = SortBucket(pLevel);  // this updates mu
    }

    std::pair<key_t, data_t> ret(ans->dist, ans->data);
    delete ans; // not needed anymore
    --sz;

    return ret;
  }

 private:
  _Level *rgLevels;  // first level (all memory)
  _Level *topLevel;  // last levels (rgLevels + kLevels - 1)
  _Level *minLevel;  // levels below are empty

  unsigned long kLevels;  // number of levels
  unsigned long delta;  // number of buckets per level (except top) - power of 2
  unsigned long logDelta;         // log2(delta)
  unsigned long topDelta;         // number of top level buckets: 2*delta
  unsigned long logTopDelta;      // log2(topDelta)
  unsigned long logBottom;        // floor(log2(minKeyVariation))
  unsigned long long relBitMask;  // bits determining node position

  key_t mu;  // minimum removed until now (needed for monotonicity)

  size_t sz;  // number of nodes in the heap

#ifdef STATS
  //==========STATISTICS==========
  long long statEmpty;       // statistic: number of empty buckets scanned
  long statExpandedNodes;    // statistic: number of nodes expanded out
  long statExpandedBuckets;  // statistic: number of buckets expanded out of
  long statInsert;           // statistic: number of insert operations
  long statPosEval;          // statistic: number of distToBucket operations
#endif

  // CHANGE TO: KeyToLevel, CHANGE TO (key_t key);
  _Level *DistToLevel(key_t *pDist) {
    assert(mu <= *pDist);
    key_t tDist = (*pDist >> logBottom) & relBitMask;
    key_t tMu = (mu >> logBottom) & relBitMask;

    _Level *lev = rgLevels;
    while (lev < topLevel) {
      tDist >>= logDelta;
      tMu >>= logDelta;
      if (tDist == tMu) break;
      ++lev;
    }
    return lev;
  }

  // CHANGE TO: KeyToBucket, CHANGE TO (key_t key, Level *lev)
  _Bucket *DistToBucket(key_t *pDist, _Level *lev) {
    POS_EVAL;
    return (lev->rgBin +
            (((size_t)((*pDist) >> (lev->digShift))) & (lev->digMask)));
  }

  _Node *place(_Node *node, _Bucket *bckNew) {
    INSERT_TO_BUCKET;

    node->sBckInfo.bucket = bckNew;  // setting new bucket
    if (bckNew->pNode == NULL) {     // first node in Bucket (circular)
      bckNew->pNode = NEXT(node) = PREV(node) = node;  // 1-length cycle
    }
    else {  // update neighbor nodes (insert in cycle)
      PREV(node) = PREV(bckNew->pNode);
      NEXT(node) = bckNew->pNode;
      NEXT(PREV(bckNew->pNode)) = node;
      PREV(bckNew->pNode) = node;
    }

    // new node at level
    if (++(bckNew->pLevel->cNodes) == 1) {  // set pBucket
      bckNew->pLevel->pBucket = DistToBucket(&mu, bckNew->pLevel);
    }

    if (minLevel > bckNew->pLevel) minLevel = bckNew->pLevel;

    return node;
  }

  _Node *extract(_Node *node) {
    _Bucket *bckOld = BUCKET(node);
    if (NEXT(node) == node) {  // last node in Bucket (circular)
      bckOld->pNode = NULL;    // empty bucket
    }
    else {  // update neighbor nodes (insert in cycle)
      NEXT(PREV(node)) = NEXT(node);
      PREV(NEXT(node)) = PREV(node);
      bckOld->pNode = NEXT(node);  // if node == pNode (precaution)
    }
    assert(bckOld->pLevel->cNodes > 0);
    --(bckOld->pLevel->cNodes);

    return node;
  }

  _Node *Move(_Node *node, _Bucket *bckNew) {
    return place(extract(node), bckNew);
  }

  _Node *SortBucket(_Level *pLevel) {
    assert(pLevel != rgLevels);
    EXPANDED_BUCKET;
    _Node *pNode = pLevel->pBucket->pNode;  // minimum bucket
    assert(pNode != NULL);
    NEXT(PREV(pNode)) = NULL;  // turn into list (previously cycle)

    // find minimum
    _Node *ans = pNode;
    key_t dMin = pNode->dist;
    for (pNode = NEXT(pNode); pNode; pNode = NEXT(pNode)) {
      if (pNode->dist < dMin) {
        dMin = pNode->dist;
        ans = pNode;
      }
    }

    assert(mu <= ans->dist);
    // if logBottom > 0, need to erase last bits
    mu = (ans->dist >> logBottom) << logBottom;

    // sort (expand) the bucket
    pNode = pLevel->pBucket->pNode;
    pLevel->pBucket->pNode = NULL;  // empty bucket
    for (_Node *nextNode; pNode; pNode = nextNode) {
      nextNode = NEXT(pNode);

      --(pLevel->cNodes);
      EXPANDED_NODE;               // node moved to another bucket
      if (pNode == ans) continue;  // do not insert answer (mu)

      assert(pLevel > rgLevels);
      _Bucket *bckNew =
          DistToBucket(&(pNode->dist), DistToLevel(&(pNode->dist)));
      assert(bckNew->pLevel < pLevel);
      place(pNode, bckNew);  // Insert increases cNodes
    }

    assert(ans != NULL);
    return ans;
  }
};

}  // namespace mlb

#endif
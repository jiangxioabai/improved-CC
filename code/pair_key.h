#pragma once
#include <cstdint>
#include <cassert>
#include <unordered_map>
#include <unordered_set>
#include <vector>

using PairKey = uint64_t;
inline PairKey pair_key_directed(int x,int y) noexcept
{ return (PairKey(uint32_t(x))<<32)|uint32_t(y); }

inline int key_hi(PairKey k){ return int(k>>32); }
inline int key_lo(PairKey k){ return int(k&0xFFFFFFFF); }

/* ---- 仅声明，全局定义放某个 .cpp ---- */
extern std::unordered_set<PairKey>       criticalDir;
extern std::unordered_map<PairKey,uint32_t> dir_key2cid;
extern std::vector<std::pair<int,int>>   crit_pairs;
static std::vector<uint32_t> cid_of_key;   // 全局声明（pair_key.h 或 basis.h）
uint32_t MASK = 0;     





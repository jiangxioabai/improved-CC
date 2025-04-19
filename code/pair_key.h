#pragma once
#include <cstdint>

using PairKey = std::uint64_t;

/* 方向有区分的键：高 32 位 = a，低 32 位 = b */
static inline PairKey pair_key_directed(int a, int b)
{
    return (PairKey(uint32_t(a)) << 32) | uint32_t(b);
}

/* 无向键：把 (a,b) 与 (b,a) 统一到同一个 64‑bit 值 */
static inline PairKey pair_key_canonical(int a, int b)
{
    return (a < b) ? pair_key_directed(a,b)
                   : pair_key_directed(b,a);
}

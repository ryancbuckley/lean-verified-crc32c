/*
 * Reed–Solomon erasure coding over GF(2^8) (field polynomial 0x11D).
 *
 * A stripe of k data shards is extended to k + m shards; any k of them give
 * back all the others. Shard number p (0 <= p < 256) of a stripe is the value
 * at the point p of the unique polynomial of degree < k through the data, one
 * polynomial per byte position; data shards are numbers 0..k-1.
 *
 * The one operation is interpolation: from the shards at k distinct points xs,
 * compute the shards at r points ys. Encoding is xs = 0..k-1, ys = k..k+m-1;
 * reconstruction is xs = any k surviving shard numbers, ys = the lost ones.
 *
 * What is proven (Lean, ReedSolomon/): the scheme itself (any k shards
 * determine the stripe; it is MDS), that `leanrs_prepare` builds exactly the
 * Lagrange coefficients and lookup tables, and that the AArch64 kernel's
 * machine code computes the shards from them. Not proven: this C wrapper
 * (argument checks, padding of short shards, the portable dispatch) and the
 * portable kernel, which is tested.
 */
#ifndef LEANRS_H
#define LEANRS_H

#include <stddef.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

/* Bytes of the table for k input and r output shards: 32 * k * r. */
size_t leanrs_table_size(size_t k, size_t r);

/* Fill `tab` (leanrs_table_size(k, r) bytes) for computing the shards at the
 * points ys[0..r) from the shards at the k distinct points xs[0..k). Returns 0,
 * or -1 if k or r is 0 or the xs are not distinct. */
int leanrs_prepare(const uint8_t* xs, size_t k, const uint8_t* ys, size_t r, uint8_t* tab);

/* Compute the r output shards out[0..r) of `len` bytes from the k input shards
 * in[0..k) with a table from leanrs_prepare. No output shard may overlap
 * another, an input shard, the table or either pointer array. Returns 0, or -1
 * on invalid arguments (including overlap). */
int leanrs_run(const uint8_t* tab, size_t k, size_t r, size_t len, const uint8_t* const* in,
               uint8_t* const* out);

/* As leanrs_run, always on the portable path. For tests and benchmarks. */
int leanrs_run_portable(const uint8_t* tab, size_t k, size_t r, size_t len,
                        const uint8_t* const* in, uint8_t* const* out);

/* Whether leanrs_run uses the verified AArch64 kernel. */
int leanrs_has_verified_kernel(void);

#ifdef __cplusplus
}
#endif

#endif

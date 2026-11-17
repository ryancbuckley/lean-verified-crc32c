// leanrs_apply: multiply `k` input shards by an `r x k` matrix over GF(2^8),
// producing `r` output shards, with split-nibble table lookups (TBL).
//
//   void leanrs_apply(const uint8_t* tab          /*x0*/,
//                     const uint8_t* const* in    /*x1: k pointers*/,
//                     uint8_t* const* out         /*x2: r pointers*/,
//                     size_t k /*x3*/, size_t r /*x4*/, size_t len /*x5*/);
//
// `tab` holds 32 bytes per matrix entry, row-major: for the coefficient `c` of
// output row `j` and input `i`, at tab + 32*(j*k + i),
//     bytes  0..15:  c * v          for v = 0..15   (low-nibble table)
//     bytes 16..31:  c * (v << 4)   for v = 0..15   (high-nibble table)
// so that c * x = lo[x & 15] ^ hi[x >> 4] for every byte x.
//
// Preconditions: k >= 1, r >= 1, len >= 64; no output shard overlaps anything
// the routine reads or another output shard. Every output byte is written;
// reads only the table, the two pointer arrays and the input shards. Needs the
// SHA3 extension for EOR3 (baseline on Apple silicon; elsewhere the caller must
// check for it). Uses
// x6-x16, v0-v7 and v16-v30 (all caller-saved), no stack, no calls.
//
// Shape: 64-byte blocks at offsets 0, 64, 128, ... and a final block at
// len - 64 (which may overlap the one before it; it recomputes the same
// bytes). Within a block the output rows are produced two at a time, then one
// if `r` is odd, each by a loop over the inputs that accumulates the looked-up
// products in registers. Hand-written so that the bytes proven in Lean
// (ReedSolomon/Arm64/*.lean) do not depend on a compiler.

#if defined(__aarch64__)

#if defined(__APPLE__)
#define SYM(x) _##x
#else
#define SYM(x) x
#endif

// acc ^= lo[x & 15] ^ hi[x >> 4], with the low nibbles in \lon and the high in \hin
.macro  MULACC acc, lot, hit, lon, hin
        tbl     v29.16b, {\lot\().16b}, \lon\().16b
        tbl     v30.16b, {\hit\().16b}, \hin\().16b
        eor3    \acc\().16b, \acc\().16b, v29.16b, v30.16b
.endm

// Load the 64-byte block of the next input and split it into nibbles:
// v16..v19 = low nibbles, v20..v23 = high nibbles.
.macro  LOADSPLIT
        ldr     x15, [x13]                  // next input shard
        add     x13, x13, #8
        add     x15, x15, x8
        ldp     q16, q17, [x15]
        ldp     q18, q19, [x15, #32]
        ushr    v20.16b, v16.16b, #4
        ushr    v21.16b, v17.16b, #4
        ushr    v22.16b, v18.16b, #4
        ushr    v23.16b, v19.16b, #4
        and     v16.16b, v16.16b, v28.16b
        and     v17.16b, v17.16b, v28.16b
        and     v18.16b, v18.16b, v28.16b
        and     v19.16b, v19.16b, v28.16b
.endm

        .arch   armv8.2-a+sha3
        .text
        .p2align 4
        .globl  SYM(leanrs_apply)
SYM(leanrs_apply):
        movi    v28.16b, #0x0f
        sub     x6, x5, #64                 // offset of the last block
        lsl     x7, x3, #5                  // bytes of table per row
        mov     x8, #0                      // block offset
1:      mov     x9, x0                      // tables of the next row
        mov     x10, x2                     // next output pointer
        mov     x11, x4                     // rows left
2:      cmp     x11, #2
        b.lo    5f
        // two rows
        add     x12, x9, x7                 // tables of the second row
        mov     x13, x1
        mov     x14, x3                     // inputs left
        movi    v0.16b, #0
        movi    v1.16b, #0
        movi    v2.16b, #0
        movi    v3.16b, #0
        movi    v4.16b, #0
        movi    v5.16b, #0
        movi    v6.16b, #0
        movi    v7.16b, #0
3:      LOADSPLIT
        ldp     q24, q25, [x9], #32
        ldp     q26, q27, [x12], #32
        MULACC  v0, v24, v25, v16, v20
        MULACC  v1, v24, v25, v17, v21
        MULACC  v2, v24, v25, v18, v22
        MULACC  v3, v24, v25, v19, v23
        MULACC  v4, v26, v27, v16, v20
        MULACC  v5, v26, v27, v17, v21
        MULACC  v6, v26, v27, v18, v22
        MULACC  v7, v26, v27, v19, v23
        subs    x14, x14, #1
        b.ne    3b
        ldp     x15, x16, [x10], #16        // the two output shards
        add     x15, x15, x8
        add     x16, x16, x8
        stp     q0, q1, [x15]
        stp     q2, q3, [x15, #32]
        stp     q4, q5, [x16]
        stp     q6, q7, [x16, #32]
        mov     x9, x12                     // skip the second row's tables
        sub     x11, x11, #2
        b       2b
5:      cbz     x11, 7f
        // one row
        mov     x13, x1
        mov     x14, x3
        movi    v0.16b, #0
        movi    v1.16b, #0
        movi    v2.16b, #0
        movi    v3.16b, #0
6:      LOADSPLIT
        ldp     q24, q25, [x9], #32
        MULACC  v0, v24, v25, v16, v20
        MULACC  v1, v24, v25, v17, v21
        MULACC  v2, v24, v25, v18, v22
        MULACC  v3, v24, v25, v19, v23
        subs    x14, x14, #1
        b.ne    6b
        ldr     x15, [x10]
        add     x15, x15, x8
        stp     q0, q1, [x15]
        stp     q2, q3, [x15, #32]
7:      cmp     x8, x6
        b.hs    8f
        add     x8, x8, #64
        cmp     x8, x6
        csel    x8, x8, x6, lo              // min(offset + 64, len - 64)
        b       1b
8:      ret

#endif

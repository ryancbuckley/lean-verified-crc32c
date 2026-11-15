// leancrc32c_copy_large: copy `n >= 64` bytes from `src` to `dst`.
//
//   void leancrc32c_copy_large(void* dst /*x0*/, const void* src /*x1*/, size_t n /*x2*/);
//
// Preconditions: n >= 64, and [src, src+n) and [dst, dst+n) do not overlap.
// Reads only [src, src+n), writes only [dst, dst+n). Uses x0-x7 and v0-v5
// (all caller-saved), no stack, no calls.
//
// Hand-written so that the bytes proven in Lean (MemcpyCrc32c/Arm64/Copy*.lean)
// do not depend on a compiler. Shape:
//   1. Load the last 64 source bytes and the first 32.
//   2. Store the first 32, then copy 32-byte blocks to 32-byte-aligned
//      destinations until fewer than 64 bytes remain before the end.
//   3. Store the saved last 64 bytes.
// Below 128 KiB the block loop uses ldp/stp; from 128 KiB it uses the
// non-temporal ldnp/stnp forms, which are architecturally the same loads and
// stores with a cache hint.

#if defined(__aarch64__)

#if defined(__APPLE__)
#define SYM(x) _##x
#else
#define SYM(x) x
#endif

        .text
        .p2align 4
        .globl  SYM(leancrc32c_copy_large)
SYM(leancrc32c_copy_large):
        add     x4, x1, x2                  // src end
        ldp     q2, q3, [x4, #-64]          // last 64 source bytes
        ldp     q4, q5, [x4, #-32]
        ldp     q0, q1, [x1]                // first 32 source bytes
        add     x5, x0, x2                  // dst end
        add     x3, x0, #32
        and     x3, x3, #0xffffffffffffffe0 // first 32-aligned dst above dst
        sub     x6, x3, x0                  // 1..32 bytes covered by the head
        add     x1, x1, x6
        stp     q0, q1, [x0]
        sub     x7, x5, #64                 // block loop runs while x3 < x7
        cmp     x3, x7
        b.hs    3f
        cmp     x2, #0x20, lsl #12          // 128 KiB
        b.hs    2f
1:      ldp     q0, q1, [x1]
        add     x1, x1, #32
        stp     q0, q1, [x3]
        add     x3, x3, #32
        cmp     x3, x7
        b.lo    1b
        b       3f
2:      ldnp    q0, q1, [x1]
        add     x1, x1, #32
        stnp    q0, q1, [x3]
        add     x3, x3, #32
        cmp     x3, x7
        b.lo    2b
3:      stp     q2, q3, [x5, #-64]          // last 64 bytes
        stp     q4, q5, [x5, #-32]
        ret

// leancrc32c_copy_small: copy `1 <= n <= 64` bytes from `src` to `dst`.
//
//   uint32_t leancrc32c_copy_small(void* dst /*x0*/, const void* src /*x1*/, size_t n /*x2*/,
//                                  uint32_t crc /*w3*/);
//
// Preconditions: 1 <= n <= 64, and the ranges do not overlap. Returns `crc`
// unchanged, so a caller that has just computed a CRC can tail-call it. Reads only
// [src, src+n), writes only [dst, dst+n). Uses x0-x11 and v0-v3, no stack, no
// calls. Every size class loads a head and a tail that together cover the
// range (overlapping in the middle), then stores both; all loads come before
// any store. Proven in MemcpyCrc32c/Arm64/CopySmall.lean.
        .p2align 4
        .globl  SYM(leancrc32c_copy_small)
SYM(leancrc32c_copy_small):
        add     x4, x1, x2                  // src end
        add     x5, x0, x2                  // dst end
        cmp     x2, #16
        b.lo    4f
        cmp     x2, #32
        b.hi    1f
        ldp     x6, x7, [x1]                // 16..32: two 16-byte halves
        ldp     x8, x9, [x4, #-16]
        stp     x6, x7, [x0]
        stp     x8, x9, [x5, #-16]
        mov     w0, w3                      // pass the CRC through
        ret
1:      ldp     q0, q1, [x1]                // 33..64: two 32-byte halves
        ldp     q2, q3, [x4, #-32]
        stp     q0, q1, [x0]
        stp     q2, q3, [x5, #-32]
        mov     w0, w3                      // pass the CRC through
        ret
4:      cmp     x2, #8
        b.lo    5f
        ldp     w6, w7, [x1]                // 8..15: two 8-byte halves
        ldp     w8, w9, [x4, #-8]
        stp     w6, w7, [x0]
        stp     w8, w9, [x5, #-8]
        mov     w0, w3                      // pass the CRC through
        ret
5:      cmp     x2, #4
        b.lo    6f
        ldr     w6, [x1]                    // 4..7: two 4-byte halves
        sub     x8, x4, #4
        ldr     w7, [x8]
        str     w6, [x0]
        sub     x9, x5, #4
        str     w7, [x9]
        mov     w0, w3                      // pass the CRC through
        ret
6:      lsr     x9, x2, #1                  // 1..3: first, middle, last byte
        ldrb    w6, [x1]
        ldrb    w7, [x1, x9]
        sub     x8, x4, #1
        ldrb    w8, [x8]
        strb    w6, [x0]
        add     x10, x0, x9
        strb    w7, [x10]
        sub     x11, x5, #1
        strb    w8, [x11]
        mov     w0, w3                      // pass the CRC through
        ret

#endif

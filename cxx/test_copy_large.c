// Differential and guard-page test for leancrc32c_copy_large
// (cxx/leancrc32c_copy_arm64.S): sizes 64..399 at every source offset 0..32 and
// destination offset 0..65, plus sizes around the 128 KiB loop switch; each case
// in the interior with canaries and flush against PROT_NONE pages on each side.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <sys/mman.h>
#include <unistd.h>
void leancrc32c_copy_large(void *, const void *, size_t);
int main(void) {
  size_t pg = (size_t)getpagesize(), span = 1 << 20;
  // guard pages on both sides of src and dst
  uint8_t *sm = mmap(0, span + 2 * pg, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANON, -1, 0);
  uint8_t *dm = mmap(0, span + 2 * pg, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANON, -1, 0);
  mprotect(sm, pg, PROT_NONE); mprotect(sm + pg + span, pg, PROT_NONE);
  mprotect(dm, pg, PROT_NONE); mprotect(dm + pg + span, pg, PROT_NONE);
  uint8_t *sb = sm + pg, *db = dm + pg; unsigned long cases = 0;
  for (size_t i = 0; i < span; i++) sb[i] = (uint8_t)(i * 131 + (i >> 8) * 7 + 3);
  size_t big[] = {4095, 4096, 65537, 131071, 131072, 131073, 300001, span - 400};
  for (int pass = 0; pass < 2; pass++) {
    size_t nmax = pass ? sizeof big / sizeof *big : 400;
    for (size_t k = pass ? 0 : 64; k < nmax; k++) {
      size_t n = pass ? big[k] : k;
      for (size_t so = 0; so < 33; so += (pass ? 11 : 1))
        for (size_t dof = 0; dof < 66; dof += (pass ? 13 : 1))
          for (int edge = 0; edge < 3; edge++) {
            // edge 0: interior with canaries; 1: flush against start guard; 2: flush against end guard
            uint8_t *s = edge == 1 ? sb : edge == 2 ? sb + span - n : sb + 64 + so;
            uint8_t *d = edge == 1 ? db : edge == 2 ? db + span - n : db + 128 + dof;
            if (edge == 0) memset(d - 64, 0xA5, n + 128); else memset(d, 0xA5, n);
            leancrc32c_copy_large(d, s, n);
            if (memcmp(d, s, n)) { printf("MISMATCH n=%zu so=%zu do=%zu edge=%d\n", n, so, dof, edge); return 1; }
            if (edge == 0) for (int j = 1; j <= 64; j++)
              if (d[-j] != 0xA5 || d[n + j - 1] != 0xA5) { printf("OVERRUN n=%zu so=%zu do=%zu\n", n, so, dof); return 1; }
            cases++;
          }
    }
  }
  printf("ok: %lu cases\n", cases);
  return 0;
}

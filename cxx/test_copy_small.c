// Differential and guard-page test for leancrc32c_copy_small
// (cxx/leancrc32c_copy_arm64.S): every size 1..64 at source and destination
// offsets 0..69, each in the interior with canaries and flush against
// PROT_NONE pages on each side. Also checks the CRC argument is returned.
#include <stdio.h>
#include <string.h>
#include <stdint.h>
#include <sys/mman.h>
#include <unistd.h>
uint32_t leancrc32c_copy_small(void *, const void *, size_t, uint32_t);
int main(void) {
  size_t pg = (size_t)getpagesize();
  uint8_t *sm = mmap(0, 3 * pg, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANON, -1, 0);
  uint8_t *dm = mmap(0, 3 * pg, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANON, -1, 0);
  mprotect(sm, pg, PROT_NONE); mprotect(sm + 2 * pg, pg, PROT_NONE);
  mprotect(dm, pg, PROT_NONE); mprotect(dm + 2 * pg, pg, PROT_NONE);
  uint8_t *sb = sm + pg, *db = dm + pg; unsigned long cases = 0;
  for (size_t i = 0; i < pg; i++) sb[i] = (uint8_t)(i * 131 + (i >> 8) * 7 + 3);
  for (size_t n = 1; n <= 64; n++)
    for (size_t so = 0; so < 70; so++)
      for (size_t dof = 0; dof < 70; dof++)
        for (int edge = 0; edge < 3; edge++) {
          uint8_t *s = edge == 1 ? sb : edge == 2 ? sb + pg - n : sb + 64 + so;
          uint8_t *d = edge == 1 ? db : edge == 2 ? db + pg - n : db + 128 + dof;
          if (edge == 0) memset(d - 64, 0xA5, n + 128); else memset(d, 0xA5, n);
          uint32_t tag = (uint32_t)(0x9E3779B9u * (uint32_t)(cases + 1));
          if (leancrc32c_copy_small(d, s, n, tag) != tag) { printf("CRC NOT RETURNED n=%zu\n", n); return 1; }
          if (memcmp(d, s, n)) { printf("MISMATCH n=%zu so=%zu do=%zu edge=%d\n", n, so, dof, edge); return 1; }
          if (edge == 0) for (int j = 1; j <= 64; j++)
            if (d[-j] != 0xA5 || d[n + j - 1] != 0xA5) { printf("OVERRUN n=%zu so=%zu do=%zu\n", n, so, dof); return 1; }
          cases++;
        }
  printf("ok: %lu cases\n", cases);
  return 0;
}

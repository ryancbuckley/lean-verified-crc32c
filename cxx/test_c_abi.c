/* Pure C11 ABI smoke and edge-case test for leancrc32c.h. */
#include "leancrc32c.h"

#include <stdio.h>
#include <string.h>

int main(void) {
  /* Null pointers are permitted when count == 0. */
  if (leancrc32c_compute_crc32c(NULL, 0) != 0u) return 1;
  if (leancrc32c_extend_crc32c(0x12345678u, NULL, 0) != 0x12345678u) return 2;
  if (leancrc32c_extend_crc32c_portable(0x12345678u, NULL, 0) != 0x12345678u) return 3;
  if (leancrc32c_memcpy_crc32c(NULL, NULL, 0, 0xCAFEBABEu) != 0xCAFEBABEu) return 4;
  if (leancrc32c_memcpy_crc32c_portable(NULL, NULL, 0, 0xCAFEBABEu) != 0xCAFEBABEu) return 5;

  /* Standard RFC 3720 / Castagnoli check value for "123456789" at unaligned offsets. */
  unsigned char src_storage[32];
  unsigned char dst_storage[32];
  for (size_t off = 0; off < 8; ++off) {
    memset(src_storage, 0x5A, sizeof(src_storage));
    memset(dst_storage, 0xA5, sizeof(dst_storage));
    memcpy(src_storage + off, "123456789", 9);

    const uint32_t want = 0xE3069283u;
    if (leancrc32c_compute_crc32c(src_storage + off, 9) != want) return 6;
    if (leancrc32c_extend_crc32c_portable(0, src_storage + off, 9) != want) return 7;
    if (leancrc32c_memcpy_crc32c(dst_storage + off, src_storage + off, 9, 0) != want) return 8;
    if (memcmp(dst_storage + off, "123456789", 9) != 0) return 9;
    if (off > 0 && dst_storage[off - 1] != 0xA5) return 10;
    if (dst_storage[off + 9] != 0xA5) return 11;

    memset(dst_storage, 0xA5, sizeof(dst_storage));
    if (leancrc32c_memcpy_crc32c_portable(dst_storage + off, src_storage + off, 9, 0) != want)
      return 12;
    if (memcmp(dst_storage + off, "123456789", 9) != 0) return 13;
  }

  printf("OK: C11 ABI checks passed (hardware available: %d)\n",
         (int)leancrc32c_hardware_available());
  return 0;
}

/-
Published CRC32C test vectors, checked by kernel evaluation of the bitwise
reference (and therefore, by `crc32c_eq_spec`, of the polynomial spec).
-/
import MemcpyCrc32c.Arith

namespace Crc32c

/-- CRC32C of a list of bytes, for stating vectors without `ByteArray` literals. -/
def crcList (bs : List UInt8) : UInt32 := rawExtend 0xFFFFFFFF bs ^^^ 0xFFFFFFFF

theorem crc32c_eq_crcList (bs : ByteArray) : crc32c bs = crcList bs.data.toList := by
  simp [crc32c, extend, crcList]

theorem spec_crc32c_eq_crcList (bs : ByteArray) : Spec.crc32c bs = crcList bs.data.toList := by
  rw [← crc32c_eq_spec, crc32c_eq_crcList]

/-- The standard check value: CRC32C("123456789") = 0xE3069283. -/
theorem check_123456789 :
    crcList [0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39] = 0xE3069283 := by decide +kernel

theorem check_empty : crcList [] = 0 := by decide +kernel

/-- abseil `crc32c_test.cc`: "hello world". -/
theorem check_hello_world :
    crcList [0x68, 0x65, 0x6c, 0x6c, 0x6f, 0x20, 0x77, 0x6f, 0x72, 0x6c, 0x64] = 0xc99465aa := by
  decide +kernel

/-! RFC 3720 appendix B.4 -/

theorem rfc3720_zeros : crcList (List.replicate 32 0x00) = 0x8a9136aa := by decide +kernel
theorem rfc3720_ones : crcList (List.replicate 32 0xff) = 0x62a8ab43 := by decide +kernel
theorem rfc3720_incr : crcList ((List.range 32).map UInt8.ofNat) = 0x46dd794e := by decide +kernel
theorem rfc3720_decr : crcList ((List.range 32).map fun i => UInt8.ofNat (31 - i)) = 0x113fdb5c := by
  decide +kernel

/-- RFC 3720 appendix B.4: 48-byte iSCSI SCSI Read (10) Command PDU
(wire digest bytes `56 3a 96 d9`, little-endian 32-bit CRC `0xd9963a56`). -/
theorem rfc3720_iscsi_read :
    crcList [
      0x01, 0xc0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
      0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
      0x14, 0x00, 0x00, 0x00, 0x00, 0x00, 0x04, 0x00,
      0x00, 0x00, 0x00, 0x14, 0x00, 0x00, 0x00, 0x18,
      0x28, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
      0x02, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00
    ] = 0xd9963a56 := by decide +kernel

/-! abseil `ExtendByZeroesAllLengthBits` -/

theorem zeroes_0 : extendZeroes 0xc99465aa 0 = 0xc99465aa := by decide +kernel
theorem zeroes_u32max : extendZeroes 0xc99465aa 0xFFFFFFFF = 0x9b1d5aaa := by decide +kernel
theorem zeroes_12345678 : extendZeroes 0xc99465aa 0x12345678 = 0xcf0e9553 := by decide +kernel
theorem zeroes_u64max : extendZeroes 0xc99465aa 0xFFFFFFFFFFFFFFFF = 0xf5bff489 := by decide +kernel
theorem zeroes_big : extendZeroes 0xc99465aa 0x12345678abcdefff = 0xaa1ffb0b := by decide +kernel

end Crc32c

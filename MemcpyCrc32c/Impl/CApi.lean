/-
Entry points for the C++ wrapper (`cxx/`). Core-only executable code; proven
in `MemcpyCrc32c.CApi`.

The wrapper presents caller memory to these functions as a borrowed
`ByteArray` whose object header does not exist: only the data pointer is
valid. So these functions must never read the array's size or touch its
reference count. They take the length as a `USize` and reach the bytes only
through `ByteArray.uget` and the trusted `loadU64LE`, both of which use the
data pointer alone. `scripts/check_capi.sh` checks the generated C for this.

Lean does not allow `@[export]` on functions with borrowed parameters (an
exported function owns its arguments and would release the array, which
writes to the header). The wrapper therefore calls these by their compiled
symbol names, `lp_leanmemcpy_Crc32c_extendRaw` and so on.

The proof arguments are the wrapper's contract: the pointer is valid for
`len` bytes. They are erased at run time and cannot be checked there.
-/
import MemcpyCrc32c.Impl.Dispatch

namespace Crc32c

/-- `absl::ExtendCrc32c` over the first `len` bytes of `a`, dispatched. -/
@[noinline] def extendRaw (c : UInt32) (a : @& ByteArray) (len : USize) (hs : a.size < USize.size)
    (h : len.toNat ≤ a.size) : UInt32 :=
  have h0 : (0 : USize).toNat + len.toNat ≤ a.size := by simp; exact h
  if hwAvailable then rawExtendHwUSize (c ^^^ 0xFFFFFFFF) a hs 0 len h0 ^^^ 0xFFFFFFFF
  else rawExtendPortableUSize (c ^^^ 0xFFFFFFFF) a hs 0 len h0 ^^^ 0xFFFFFFFF

/-- As `extendRaw`, always on the portable path. For benchmarks and tests. -/
@[noinline] def extendPortableRaw (c : UInt32) (a : @& ByteArray) (len : USize) (hs : a.size < USize.size)
    (h : len.toNat ≤ a.size) : UInt32 :=
  have h0 : (0 : USize).toNat + len.toNat ≤ a.size := by simp; exact h
  rawExtendPortableUSize (c ^^^ 0xFFFFFFFF) a hs 0 len h0 ^^^ 0xFFFFFFFF

/-- Whether the hardware path is in use. -/
@[noinline] def hwAvailableRaw (_ : Unit) : Bool := hwAvailable

end Crc32c

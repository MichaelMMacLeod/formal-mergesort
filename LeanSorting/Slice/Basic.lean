import Mathlib.Data.Nat.Defs

structure Slice (arr : Array α) (low high : ℕ) : Prop where
  low_le_high : low ≤ high
  high_le_size : high ≤ arr.size

structure SlicePtrExclusive (arr : Array α) (low high : ℕ) (ptr : ℕ)
    extends Slice arr low high : Prop where
  ptr_ge_low : ptr ≥ low
  ptr_lt_high : ptr < high

structure SlicePtrInclusive (arr : Array α) (low high : ℕ) (ptr : ℕ)
    extends Slice arr low high : Prop where
  ptr_ge_low : ptr ≥ low
  ptr_le_high : ptr ≤ high

theorem Slice.swap_array
    (s : Slice arr low high)
    (size_eq : arr.size = aux.size)
    : Slice aux low high :=
  { s with high_le_size := by rw [← size_eq]; exact s.high_le_size }

theorem SlicePtrInclusive.swap_arr
    (s : SlicePtrInclusive arr low high ptr)
    (size_eq : arr.size = aux.size)
    : SlicePtrInclusive aux low high ptr :=
  { s with high_le_size := by rw [← size_eq]; exact s.high_le_size }

theorem SlicePtrExclusive.swap_array
    (s : SlicePtrExclusive arr low high ptr)
    (size_eq : arr.size = aux.size)
    : SlicePtrExclusive aux low high ptr :=
  { s with high_le_size := by rw [← size_eq]; exact s.high_le_size }

theorem SlicePtrInclusive.ptr_le_size
    (s : SlicePtrInclusive arr low high ptr)
    : ptr ≤ arr.size :=
  Nat.le_trans s.ptr_le_high s.high_le_size

theorem SlicePtrExclusive.ptr_lt_size
    (s : SlicePtrExclusive arr low high ptr)
    : ptr < arr.size :=
  Nat.le_trans s.ptr_lt_high s.high_le_size

theorem SlicePtrInclusive.left
    (s : SlicePtrInclusive arr low high ptr)
    : Slice arr low ptr :=
  { low_le_high := s.ptr_ge_low
    high_le_size := Nat.le_trans s.ptr_le_high s.high_le_size
  }

theorem SlicePtrInclusive.right
    (s : SlicePtrInclusive arr low high ptr)
    : Slice arr ptr high :=
  { low_le_high := s.ptr_le_high
    high_le_size := s.high_le_size
  }

theorem SlicePtrExclusive.increment_ptr
    (s : SlicePtrExclusive arr low high ptr)
    : SlicePtrInclusive arr low high ptr.succ :=
  { s with
    ptr_ge_low := by have := s.ptr_ge_low; omega,
    ptr_le_high := s.ptr_lt_high,
  }

def SlicePtrInclusive.make_exclusive
    (s : SlicePtrInclusive arr low high ptr)
    (ptr_lt_high : ptr < high)
    : SlicePtrExclusive arr low high ptr :=
  { s with ptr_lt_high }

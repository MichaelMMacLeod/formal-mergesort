import Mathlib.Data.Nat.Defs
import Batteries.Classes.Order
import LeanSorting.Nat.Extras

set_option pp.proofs true
set_option linter.unusedSectionVars false

open Batteries

variable
  {α : Type}
  -- [Ord α]
  -- [LE α]
  -- [LT α]
  -- [BEq α]
  -- [LawfulOrd α]
  {arr arr₁ arr₂ arr_i aux : Array α}
  {low high low₁ high₁ low₂ high₂ ptr ptr₁ ptr₂ mid : ℕ}

structure Slice (arr : Array α) (low high : ℕ) : Prop where
  low_le_high : low ≤ high
  high_le_size : high ≤ arr.size

def Slice.append
    (s₁ : Slice arr low mid)
    (s₂ : Slice arr mid high)
    : Slice arr low high :=
  { low_le_high := Nat.le_trans s₁.low_le_high s₂.low_le_high,
    high_le_size := s₂.high_le_size
  }

variable
  (s : @Slice α arr low high)

structure SlicePtrExclusive (arr : Array α) (low high : ℕ) (ptr : ℕ)
    extends Slice arr low high : Prop where
  ptr_ge_low : ptr ≥ low
  ptr_lt_high : ptr < high

structure SlicePtrInclusive (arr : Array α) (low high : ℕ) (ptr : ℕ)
    extends Slice arr low high : Prop where
  ptr_ge_low : ptr ≥ low
  ptr_le_high : ptr ≤ high

theorem SlicePtrExclusive.make_inclusive
    (s : SlicePtrExclusive arr low high ptr)
    : SlicePtrInclusive arr low high ptr :=
  { s with ptr_le_high := Nat.le_of_lt s.ptr_lt_high }

theorem SlicePtrExclusive.nonempty
    (s : SlicePtrExclusive arr low high ptr)
    : low < high :=
  Nat.lt_of_le_of_lt s.ptr_ge_low s.ptr_lt_high

theorem Slice.swap_array
    (s : Slice arr low high)
    (size_eq : arr.size = aux.size)
    : Slice aux low high :=
  { s with high_le_size := by rw [← size_eq]; exact s.high_le_size }

theorem SlicePtrInclusive.swap_array
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

theorem SlicePtrExclusive.low_lt_size
    (s : SlicePtrExclusive arr low high ptr)
    : low < arr.size :=
  Nat.le_trans s.nonempty s.high_le_size

def SlicePtrExclusive.ptrFin
    (s : SlicePtrExclusive arr low high ptr)
    : Fin arr.size :=
  ⟨ptr, s.ptr_lt_size⟩

def SlicePtrExclusive.ptrFin_eq
    (s : SlicePtrExclusive arr low high ptr)
    : s.ptrFin = ⟨ptr, s.ptr_lt_size⟩ :=
  rfl

def SlicePtrExclusive.ptrFin_val_eq
    (s : SlicePtrExclusive arr low high ptr)
    : s.ptrFin.val = ptr :=
  rfl

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

theorem SlicePtrExclusive.left
    (s : SlicePtrExclusive arr low high ptr)
    : Slice arr low ptr :=
  s.make_inclusive.left

theorem SlicePtrExclusive.right
    (s : SlicePtrExclusive arr low high ptr)
    : Slice arr ptr high :=
  s.make_inclusive.right

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

variable
  [Ord α]
  [LE α]
  [LT α]
  [BEq α]
  [LawfulOrd α]

-- TODO: must also be a permutation of input
def Slice.sorted (_s : Slice arr low high) : Prop :=
  ∀ (i₁ i₂ : Fin arr.size)
    (_adjacent_in_range : i₁.val.adjacent_in_range i₂ low high),
      Ord.compare arr[i₁] arr[i₂] ≠ Ordering.gt

/--
A slice s₁ is less than or equal to a slice s₂ if every element of s₁
is less than or equal to every element of s₂.
-/
def Slice.le
    (_s₁ : Slice arr₁ low₁ high₁)
    (_s₂ : Slice arr₂ low₂ high₂)
    : Prop :=
  ∀ (i₁ : Fin arr₁.size) (i₂ : Fin arr₂.size),
      i₁.val.in_range low₁ high₁
    ∧ i₂.val.in_range low₂ high₂
    → Ord.compare arr₁[i₁] arr₂[i₂] ≠ Ordering.gt

/--
A `Slice` `s` is less than or equal to an element `a` if every element of
`s` is less than or equal to `a`.
-/
def Slice.le_elem (s : Slice arr low high) (a : α) : Prop :=
  ∀ (i : ℕ) (in_range : i ≥ low ∧ i < high),
    have high_le_size := s.high_le_size
    Ord.compare arr[i] a ≠ Ordering.gt

/--
A `Slice` `s` is greater than or equal to an element `a` if every element of
`s` is greater than or equal to `a`.
-/
def Slice.ge_elem (s : Slice arr low high) (a : α) :=
  ∀ (i : ℕ) (in_range : i ≥ low ∧ i < high),
    have high_le_size := s.high_le_size
    Ord.compare a arr[i] ≠ Ordering.gt

theorem Slice.sorted_of_empty
    {s : Slice arr low high}
    (empty : low = high)
    : s.sorted := by
  intro i₁ i₂ adjacent_in_range
  simp [Nat.adjacent_in_range] at adjacent_in_range
  omega

theorem Slice.le_of_empty
    {s₁ : Slice arr₁ low₁ high₁}
    {s₂ : Slice arr₂ low₂ high₂}
    (empty : low₁ = high₁)
    : s₁.le s₂ := by
  intro i₁ i₂ i₁_i₂_in_range
  simp [Nat.in_range] at i₁_i₂_in_range
  omega

/--
For slices `s₁` and `s₂`, `s₁.le s₂` implies `s₁.le_elem a`, where `a` is any
element of `s₂`.
-/
theorem Slice.le_elem_of_le
    (s₁ : Slice arr₁ low₁ high₁)
    {s₂ : Slice arr₂ low₂ high₂}
    (s₁_le_s₂ : s₁.le s₂)
    (ptr_in_range₂ : ptr ≥ low₂ ∧ ptr < high₂)
    : have high_le_size := s₂.high_le_size
      s₁.le_elem arr₂[ptr] := by
  intro high_le_size
  unfold Slice.le_elem
  intro i in_range high_le_size
  unfold Slice.le at s₁_le_s₂
  have i_lt_arr₁_size : i < arr₁.size := by omega
  have ptr_lt_arr₂_size : ptr < arr₂.size := by omega
  have h : i.in_range low₁ high₁ ∧ ptr.in_range low₂ high₂ := by
    simp [Nat.in_range]
    omega
  exact s₁_le_s₂ ⟨i, i_lt_arr₁_size⟩ ⟨ptr, ptr_lt_arr₂_size⟩ h

lemma not_gt_of_compare_same {a : α} : compare a a ≠ Ordering.gt := by
  have compare_refl : compare a a = .eq := Batteries.OrientedCmp.cmp_refl
  intro compare_eq_gt
  have : Ordering.eq = Ordering.gt := by rw [← compare_refl, ← compare_eq_gt]
  contradiction

/--
If a Slice `s` is sorted and `a` is its first element, then `s.ge_elem a` is true.
-/
theorem Slice.ge_elem_low_of_sorted
    (s_sorted : s.sorted)
    (nonempty : low < high)
    : have := s.high_le_size
      s.ge_elem arr[low]
    := by
  simp [Slice.ge_elem]
  intro i in_range
  simp [Slice.sorted] at s_sorted
  have := s.low_le_high
  have := s.high_le_size
  let rec loop (i : ℕ) (in_range : i ≥ low ∧ i < high)
      : compare arr[low] arr[i] ≠ Ordering.gt := by
    if i_eq_low : i = low then
      simp [i_eq_low]
      exact not_gt_of_compare_same
    else
      let j := i - 1
      have j_in_range : j ≥ low ∧ j < high := by omega
      have ih := loop j j_in_range
      let j_f : Fin arr.size := ⟨j, by omega⟩
      let i_f : Fin arr.size := ⟨i, by omega⟩
      have adj : j_f.val.adjacent_in_range i_f low high := by
        simp [Nat.adjacent_in_range]
        omega
      have h := s_sorted j_f i_f adj
      exact TransCmp.le_trans ih h
  exact loop i in_range

theorem Slice.ge_elem_low_succ_of_sorted
    (s_sorted : s.sorted)
    (nonempty : low < high)
    (s' : Slice arr low.succ high)
    : have := s.high_le_size
      s'.ge_elem arr[low]
    := by
  have h := s.ge_elem_low_of_sorted s_sorted nonempty
  simp [Slice.ge_elem]
  intro i in_range
  simp [Slice.ge_elem] at h
  have i_in_range : low ≤ i ∧ i < high := by omega
  exact h i i_in_range

/-- Two slices, `s₁` and `s₂`, remain less than or equal when we take the first
element off of `s₂` and put it on the end of `s₁`.

For example:
```
[1,2,3] ≤ [4,5,6]   is true, thus
[1,2,3,4] ≤ [5,6]   is true as well
```
-/
theorem Slice.le_of_swap_ends_le
    {aux : Slice arr₁ low₁ high₁}
    {arr : Slice arr₂ low₂ high₂}
    (arr_sorted : arr.sorted)
    (aux_le_arr : aux.le arr)
    (high₁_lt_arr₁_size : high₁ < arr₁.size)
    (low₂_lt_arr₂_size : low₂ < arr₂.size)
    (arr₁'_def : arr₁' = arr₁.set ⟨high₁, high₁_lt_arr₁_size⟩ arr₂[low₂])
    (s₁' : Slice arr₁' low₁ high₁.succ)
    (s₂' : Slice arr₂ low₂.succ high₂)
    (size_eq : arr₂.size = arr₁.size)
    : s₁'.le s₂' := by
  unfold Slice.le
  intro i₁' i₂' i₂'_i₂'_in_range
  unfold Nat.in_range at i₂'_i₂'_in_range
  unfold Slice.le at aux_le_arr
  by_cases h : i₁' = high₁
  . simp [h, arr₁'_def]
    rw [Slice.sorted] at arr_sorted
    have low₂_lt_high₂ : low₂ < high₂ := by omega
    have x := arr.ge_elem_low_succ_of_sorted arr_sorted low₂_lt_high₂ s₂'
    simp [Slice.ge_elem] at x
    have i₂'_in_range : low₂ + 1 ≤ ↑i₂' ∧ ↑i₂' < high₂ := by omega
    have x2 := x i₂' i₂'_in_range
    exact x2
  . have i₁'_lt_arr₁_size : i₁'.val < arr₁.size := by omega
    have i₂'_lt_arr₂_size : i₂'.val < arr₂.size := by omega
    let i₁ : Fin arr₁.size := ⟨i₁', i₁'_lt_arr₁_size⟩
    let i₂ : Fin arr₂.size := ⟨i₂', i₂'_lt_arr₂_size⟩
    simp [arr₁'_def]
    have high_ne_i₁' : high₁ ≠ i₁' := by omega
    have i₁'_same := arr₁.get_set_ne
      ⟨high₁, high₁_lt_arr₁_size⟩
      arr₂[low₂]
      i₁'_lt_arr₁_size
      high_ne_i₁'
    simp [i₁'_same]
    have i₁_i₂_in_range : i₁.val.in_range low₁ high₁ ∧ i₂.val.in_range low₂ high₂ := by
      simp [Nat.in_range]
      omega
    exact aux_le_arr i₁ i₂ i₁_i₂_in_range

/--
The elements at and following a pointer into a sorted slice are themselves
sorted.
-/
theorem SlicePtrInclusive.sorted_of_right_sorted
    (s : SlicePtrInclusive arr low high ptr)
    (s_sorted : s.sorted)
    : s.right.sorted := by
  unfold Slice.sorted at *
  intro i₁ i₂ adjacent_in_range
  have adjacent_in_range' : i₁.val.adjacent_in_range i₂ low high := by
    unfold Nat.adjacent_in_range at *
    have := s.ptr_ge_low
    omega
  exact s_sorted i₁ i₂ adjacent_in_range'

/--
If `a` is greater or equal to all elements of a sorted slice `s`, then `s` remains sorted
when `a` is appended on the right.
-/
theorem Slice.sorted_after_sorted_push
    (s : Slice arr low high)
    (s_sorted : s.sorted)
    (high_lt_size : high < arr.size)
    (arr'_def : arr' = arr.set ⟨high, high_lt_size⟩ a)
    (s' : Slice arr' low high.succ)
    (s_le_elem_a : s.le_elem a)
    : s'.sorted := by
  unfold Slice.sorted
  intro i₁' i₂' adjacent_in_range'
  simp [Nat.adjacent_in_range] at adjacent_in_range'
  by_cases i₂'_eq_high : i₂' = high
  . simp [i₂'_eq_high, arr'_def]
    have i₁'_lt_arr_size : i₁'.val < arr.size := by omega
    have high_ne_i₁' : high ≠ i₁' := by omega
    have i₁'_same := arr.get_set_ne ⟨high, high_lt_size⟩ a i₁'_lt_arr_size high_ne_i₁'
    rw [i₁'_same]
    have in_range : i₁'.val.in_range low high := by simp [Nat.in_range]; omega
    unfold Slice.le_elem at s_le_elem_a
    exact s_le_elem_a i₁' in_range
  . unfold Slice.sorted at s_sorted
    have i₁'_lt_arr_size : i₁'.val < arr.size := by omega
    have i₂'_lt_arr_size : i₂'.val < arr.size := by omega
    simp [arr'_def]
    have high_ne_i₁' : high ≠ i₁' := by omega
    have high_ne_i₂' : high ≠ i₂' := by omega
    have i₁'_same := arr.get_set_ne ⟨high, high_lt_size⟩ a i₁'_lt_arr_size high_ne_i₁'
    have i₂'_same := arr.get_set_ne ⟨high, high_lt_size⟩ a i₂'_lt_arr_size high_ne_i₂'
    simp [i₁'_same, i₂'_same]
    let i₁ : Fin arr.size := ⟨i₁', i₁'_lt_arr_size⟩
    let i₂ : Fin arr.size := ⟨i₂', i₂'_lt_arr_size⟩
    have i₁_def : i₁ = ⟨i₁', i₁'_lt_arr_size⟩ := by rfl
    have i₁_eq_i₁' : i₁' = i₁.val := by rw [i₁_def]
    have adjacent_in_range : i₁.val.adjacent_in_range i₂ low high := by
      simp [Nat.adjacent_in_range, i₂'_eq_high]
      omega
    exact s_sorted i₁ i₂ adjacent_in_range

/--
If `a` is less than or equal to the pointed-at element in a sorted slice, all elements of the
the slice at and after the pointed-at element are greater than or equal to `a`.

For example, if `a ≤ 10`, then because `[1,5,10,15,20]` is sorted, it is the case that all
`[10,15,20]` are greater than or equal to `a`.
-/
theorem SlicePtrExclusive.right_ge_elem_of_sorted_le_ptr
    (s : SlicePtrExclusive arr low high ptr)
    (s_sorted : s.sorted)
    {a : α}
    (a_le_ptr :
      have := s.ptr_lt_size
      Ord.compare a arr[ptr] ≠ .gt)
    : s.right.ge_elem a := by
  simp [Slice.ge_elem]
  intro i in_range
  let rec loop
      (i : ℕ)
      (in_range : ptr ≤ i ∧ i < high)
      : have := s.high_le_size
        Ord.compare a arr[i] ≠ .gt := by
    if i_eq_ptr : i = ptr then
      simp [i_eq_ptr, a_le_ptr]
    else
      let i' := i - 1
      have i'_in_range : ptr ≤ i' ∧ i' < high := by omega
      have ih := loop i' i'_in_range
      have := s.high_le_size
      have i'_le_i : Ord.compare arr[i'] arr[i] ≠ .gt := by
        simp [Slice.sorted] at s_sorted
        let i'_f : Fin arr.size := ⟨i', by omega⟩
        let i_f : Fin arr.size := ⟨i, by omega⟩
        have adj : i'_f.val.adjacent_in_range i_f low high := by
          simp [Nat.adjacent_in_range]
          have := s.ptr_ge_low
          omega
        exact s_sorted i'_f i_f adj
      exact TransCmp.le_trans ih i'_le_i
  exact loop i in_range

-- theorem SlicePtrExclusive.right_ge_elem_of_sorted_le_ptr'
--     (s : SlicePtrExclusive arr low high ptr)
--     (s_sorted : s.sorted)
--     {a : α}
--     (a_le_ptr :
--       have := s.ptr_lt_size
--       Ord.compare a arr[ptr] ≠ .gt)
--     : s.right.ge_elem a := by
--   sorry

/--
While merging two slices into an auxiliary slice, if it is determined that the first element
of `s₁` is less than or equal to the first element of `s₂`, then all elements of the resulting
auxiliary slice, created by appending the first element of `s₁` on its end, are each less than
or equal to all elements of `s₂` (the slice we didn't take any elements from).

For example,

```
s₁   = [10, 20, 30]
s₂   = [100, 200, 300]
aux := [1, 2, 3]
-- Given that 10 ≤ 100, we will merge 10 into aux, giving us:
aux' := [1, 2, 3, 10]
-- Because it was true that all elements of aux were less than all elements
-- of s₂, and because 10 ≤ 100, it remains the case that all elements of
-- aux' are less than all elements of s₂.
```
-/
theorem slice₁_ptr_le_of_succ
    (slice₁_ptr : SlicePtrExclusive arr low mid ptr₁)
    (slice₂_ptr : SlicePtrExclusive arr mid high ptr₂)
    (slice₂_sorted : slice₂_ptr.sorted)
    (slice_aux_ptr : SlicePtrExclusive aux low high i)
    (slice_aux_ptr' : SlicePtrInclusive aux' low high i.succ)
    (aux'_def :
      have h₁ := slice_aux_ptr.ptr_lt_size
      have h₂ := slice₁_ptr.ptr_lt_size
      aux' = aux.set ⟨i, h₁⟩ (arr[ptr₁]'h₂))
    (slice_aux_left_le_slice₂_right : slice_aux_ptr.left.le slice₂_ptr.right)
    (slice₁_ptr_le_slice₂_ptr :
      have h₁ := slice₁_ptr.ptr_lt_size
      have h₂ := slice₂_ptr.ptr_lt_size
      Ord.compare arr[ptr₁] arr[ptr₂] ≠ .gt)
    : slice_aux_ptr'.left.le slice₂_ptr.right
    := by
  simp [Slice.le]
  intro i₁ i₂ i₁_in_range i₂_in_range
  by_cases i₁_lt_i : i₁ < i
  . simp [Slice.le] at slice_aux_left_le_slice₂_right
    simp [aux'_def]
    have i₁_lt_aux_size : i₁ < aux.size := by
      have := slice_aux_ptr.ptr_lt_size
      omega
    let i_f : Fin aux.size := ⟨i, slice_aux_ptr.ptr_lt_size⟩
    have ptr₁_lt_arr_size := slice₁_ptr.ptr_lt_size
    have i₁_ne_i : i_f.val ≠ i₁ := by
      simp [i_f]
      omega
    rw [Array.get_set_ne aux i_f arr[ptr₁] i₁_lt_aux_size i₁_ne_i]
    let i₁_orig : Fin aux.size := ⟨i₁, i₁_lt_aux_size⟩
    have i₁_orig_eq_i₁ : i₁_orig.val = i₁.val := rfl
    have i₁_orig_in_range : i₁_orig.val.in_range low i := by
      simp [Nat.in_range] at *
      omega
    have h :=
      slice_aux_left_le_slice₂_right
        i₁_orig
        i₂
        i₁_orig_in_range
        i₂_in_range
    simp [i₁_orig] at h
    simp [aux'_def, Array.get_set_ne]
    exact h
  . simp [Nat.in_range] at i₁_in_range i₂_in_range
    have i₁_eq_i : i₁ = i := by omega
    simp [i₁_eq_i, aux'_def]
    have := slice₁_ptr.ptr_lt_size
    have h :=
      slice₂_ptr.right_ge_elem_of_sorted_le_ptr
        slice₂_sorted
        slice₁_ptr_le_slice₂_ptr
    have i₂_in_range : ptr₂ ≤ i₂ ∧ i₂ < high := by
      have := slice₂_ptr.ptr_ge_low
      omega
    simp [Slice.ge_elem] at h
    exact h i₂ i₂_in_range

theorem slice₂_ptr_le_of_succ
    (slice₁_ptr : SlicePtrExclusive arr low mid ptr₁)
    (slice₂_ptr : SlicePtrExclusive arr mid high ptr₂)
    (slice₁_sorted : slice₁_ptr.sorted)
    (slice_aux_ptr : SlicePtrExclusive aux low high i)
    (slice_aux_ptr' : SlicePtrInclusive aux' low high i.succ)
    (aux'_def :
      have h₁ := slice_aux_ptr.ptr_lt_size
      have h₂ := slice₂_ptr.ptr_lt_size
      aux' = aux.set ⟨i, h₁⟩ (arr[ptr₂]'h₂))
    (slice_aux_left_le_slice₁_right : slice_aux_ptr.left.le slice₁_ptr.right)
    (slice₂_ptr_lt_slice₁_ptr :
      have h₁ := slice₁_ptr.ptr_lt_size
      have h₂ := slice₂_ptr.ptr_lt_size
      Ord.compare arr[ptr₁] arr[ptr₂] = .gt)
    : slice_aux_ptr'.left.le slice₁_ptr.right
    := by
  simp [Slice.le]
  intro i₁ i₂ i₁_in_range i₂_in_range
  by_cases i₁_lt_i : i₁ < i
  . simp [Slice.le] at slice_aux_left_le_slice₁_right
    simp [aux'_def]
    have i₁_lt_aux_size : i₁ < aux.size := by
      have := slice_aux_ptr.ptr_lt_size
      omega
    let i_f : Fin aux.size := ⟨i, slice_aux_ptr.ptr_lt_size⟩
    have ptr₂_lt_arr_size := slice₂_ptr.ptr_lt_size
    have i₁_ne_i : i_f.val ≠ i₁ := by
      simp [i_f]
      omega
    rw [Array.get_set_ne aux i_f arr[ptr₂] i₁_lt_aux_size i₁_ne_i]
    let i₁_orig : Fin aux.size := ⟨i₁, i₁_lt_aux_size⟩
    have i₁_orig_eq_i₁ : i₁_orig.val = i₁.val := rfl
    have i₁_orig_in_range : i₁_orig.val.in_range low i := by
      simp [Nat.in_range] at *
      omega
    have h :=
      slice_aux_left_le_slice₁_right
        i₁_orig
        i₂
        i₁_orig_in_range
        i₂_in_range
    simp [i₁_orig] at h
    simp [aux'_def, Array.get_set_ne]
    exact h
  . simp [Nat.in_range] at i₁_in_range i₂_in_range
    have i₁_eq_i : i₁ = i := by omega
    simp [i₁_eq_i, aux'_def]
    have := slice₂_ptr.ptr_lt_size
    have ptr₂_lt_ptr₁ : Ord.compare arr[ptr₂] arr[ptr₁] ≠ .gt :=
      TransCmp.gt_asymm slice₂_ptr_lt_slice₁_ptr
    have h :=
      slice₁_ptr.right_ge_elem_of_sorted_le_ptr
        slice₁_sorted
        ptr₂_lt_ptr₁
    have i₂_in_range : ptr₁ ≤ i₂ ∧ i₂ < mid := by
      have := slice₂_ptr.ptr_ge_low
      omega
    simp [Slice.ge_elem] at h
    exact h i₂ i₂_in_range

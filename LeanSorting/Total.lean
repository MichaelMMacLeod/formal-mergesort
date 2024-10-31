import Mathlib.Data.Nat.ModEq
import Batteries.Classes.Order
import Init.Data.Array.Lemmas
import LeanSorting.Slice.Basic

set_option pp.proofs true

open Batteries

theorem Nat.lt_of_lt_le {a b c : ℕ} (h : a < b) : b ≤ c → a < c := by omega
theorem Nat.lt_of_le_lt {a b c : ℕ} (h : a ≤ b) : b < c → a < c := by omega
theorem Nat.sub_succ_lt_sub_of_lt {a b : ℕ} (h : a < b) : b - a.succ < b - a := by omega

variable
  {α : Type}
  [Ord α]
  [LE α]
  [LT α]
  [BEq α]
  [LawfulOrd α]
  {arr arr₁ arr₂ arr_i aux : Array α}
  {low high low₁ high₁ low₂ high₂ ptr ptr₁ ptr₂ mid : ℕ}
  (s : @Slice α arr low high)
  (s_i : @Slice α arr_i low_i high_i)

structure H₁ (arr aux : Array α) (low mid high : ℕ) : Prop where
  slice₁ : Slice arr low mid
  slice₂ : Slice arr mid high
  size_eq : arr.size = aux.size
  slice₁_sorted : slice₁.sorted
  slice₂_sorted : slice₂.sorted

structure H₂ (arr aux : Array α) (low mid high ptr₁ ptr₂ i : ℕ)
    extends H₁ arr aux low mid high : Prop where
  slice₁_inclusive : SlicePtrInclusive arr low mid ptr₁
  slice₂_inclusive : SlicePtrInclusive arr mid high ptr₂
  slice_i : SlicePtrInclusive aux low high i
  i_def : i = ptr₁ + ptr₂ - mid
  slice_i_left_sorted : slice_i.left.sorted
  slice_i_left_le_right₁ : slice_i.left.le slice₁_inclusive.right
  slice_i_left_le_right₂ : slice_i.left.le slice₂_inclusive.right

structure H₄ (arr aux : Array α) (low mid high ptr₁ ptr₂ i : ℕ)
    extends H₂ arr aux low mid high ptr₁ ptr₂ i : Prop where
  not_ptr₁_ptr₂_in_range : ptr₁ = mid ∨ ptr₂ = high

def H₂.make_H₄
  (h₂ : H₂ arr aux low mid high ptr₁ ptr₂ i)
  (not_ptr₁_ptr₂_in_range : ¬(ptr₁ < mid ∧ ptr₂ < high))
  : H₄ arr aux low mid high ptr₁ ptr₂ i :=
  { h₂ with
    not_ptr₁_ptr₂_in_range := by
      have := h₂.slice₁_inclusive.ptr_le_high
      have := h₂.slice₂_inclusive.ptr_le_high
      omega
  }

structure H₅ (arr aux : Array α) (low mid high ptr₁ ptr₂ i : ℕ)
    extends H₄ arr aux low mid high ptr₁ ptr₂ i : Prop where
  ptr₁_lt_mid : ptr₁ < mid

structure H₆ (arr aux : Array α) (low mid high ptr₁ ptr₂ i : ℕ)
    extends H₄ arr aux low mid high ptr₁ ptr₂ i : Prop where
  ptr₁_eq_mid : ptr₁ = mid

structure H₇ (arr aux : Array α) (low mid high ptr₁ ptr₂ i : ℕ)
    extends H₆ arr aux low mid high ptr₁ ptr₂ i : Prop where
  ptr₂_lt_high : ptr₂ < high

def H₆.make_H₇
    (h₆ : H₆ arr aux low mid high ptr₁ ptr₂ i)
    (ptr₂_lt_high : ptr₂ < high)
    : H₇ arr aux low mid high ptr₁ ptr₂ i :=
  { h₆ with ptr₂_lt_high }

def H₄.make_H₆
    (h₄ : H₄ arr aux low mid high ptr₁ ptr₂ i)
    (not_ptr₁_lt_mid : ¬ptr₁ < mid)
    : H₆ arr aux low mid high ptr₁ ptr₂ i :=
  { h₄ with
    ptr₁_eq_mid := by
      have := h₄.not_ptr₁_ptr₂_in_range
      have := h₄.slice₁_inclusive.ptr_le_high
      omega
  }

def H₁.make_H₂
    (h₁ : H₁ arr aux low mid high)
    (ptr₁_def : ptr₁ = low)
    (ptr₂_def : ptr₂ = mid)
    (i_def : i = ptr₁)
    : H₂ arr aux low mid high ptr₁ ptr₂ i :=
  have slice₁_inclusive : SlicePtrInclusive arr low mid ptr₁ :=
    { h₁.slice₁ with
      ptr_ge_low := Nat.le_of_eq (Eq.symm ptr₁_def)
      ptr_le_high := le_of_eq_of_le ptr₁_def h₁.slice₁.low_le_high
    }
  have slice₂_inclusive : SlicePtrInclusive arr mid high ptr₂ :=
    { h₁.slice₂ with
      ptr_ge_low := Nat.le_of_eq (Eq.symm ptr₂_def)
      ptr_le_high := le_of_eq_of_le ptr₂_def h₁.slice₂.low_le_high
    }
  have slice_i : SlicePtrInclusive aux low high i :=
    let s : Slice arr low high := h₁.slice₁.append slice₂_inclusive.toSlice
    let s : Slice aux low high := s.swap_array h₁.size_eq
    { s with
      ptr_ge_low := by omega
      ptr_le_high := by
        have := slice₁_inclusive.ptr_le_high
        have := slice₂_inclusive.ptr_le_high
        omega
    }
  have i_def : i = ptr₁ + ptr₂ - mid := by omega
  have slice_i_empty : low = i := by omega
  have slice_i_left_sorted : slice_i.left.sorted :=
    slice_i.left.sorted_of_empty slice_i_empty
  have slice_i_left_le_right₁ : slice_i.left.le slice₁_inclusive.right :=
    slice_i.left.le_of_empty slice_i_empty
  have slice_i_left_le_right₂ : slice_i.left.le slice₂_inclusive.right :=
    slice_i.left.le_of_empty slice_i_empty
  { h₁ with
    slice₁_inclusive,
    slice₂_inclusive,
    slice_i,
    i_def,
    slice_i_left_sorted,
    slice_i_left_le_right₁,
    slice_i_left_le_right₂
  }

def H₂.ptr₁_lt_arr_size
    (h₂ : H₂ arr aux low mid high ptr₁ ptr₂ i)
    (ptr₁_lt_mid : ptr₁ < mid)
    : ptr₁ < arr.size :=
  Nat.le_trans ptr₁_lt_mid h₂.slice₁.high_le_size

def H₂.i_lt_aux_size
    (h₂ : H₂ arr aux low mid high ptr₁ ptr₂ i)
    (ptr₁_lt_mid : ptr₁ < mid)
    (ptr₂_eq_high : ptr₂ = high)
    : i < aux.size := by
  have : i = ptr₁ + ptr₂ - mid := h₂.i_def
  have : ptr₁ < high := Nat.le_trans ptr₁_lt_mid h₂.slice₂.low_le_high
  have i_lt_high : i < high := by omega
  exact (h₂.slice_i.make_exclusive i_lt_high).ptr_lt_size

structure H₃ (arr aux : Array α) (low mid high ptr₁ ptr₂ i : ℕ)
    extends H₂ arr aux low mid high ptr₁ ptr₂ i : Prop where
  slice₁_exclusive : SlicePtrExclusive arr low mid ptr₁
  slice₂_exclusive : SlicePtrExclusive arr mid high ptr₂
  slice_i_exclusive : SlicePtrExclusive aux low high i

def H₂.make_H₃
    (h₂ : H₂ arr aux low mid high ptr₁ ptr₂ i)
    (ptr₁_ptr₂_in_range : ptr₁ < mid ∧ ptr₂ < high)
    : H₃ arr aux low mid high ptr₁ ptr₂ i :=
  have slice_i_exclusive : SlicePtrExclusive aux low high i := by
    have i_lt_high : i < high := by
      have := h₂.i_def
      omega
    exact h₂.slice_i.make_exclusive i_lt_high
  { h₂ with
    slice₁_exclusive := h₂.slice₁_inclusive.make_exclusive ptr₁_ptr₂_in_range.left,
    slice₂_exclusive := h₂.slice₂_inclusive.make_exclusive ptr₁_ptr₂_in_range.right,
    slice_i_exclusive
  }

def H₃.i_lt_aux_size (h₃ : H₃ arr aux low mid high ptr₁ ptr₂ i) : i < aux.size :=
  h₃.slice_i_exclusive.ptr_lt_size

def H₃.ptr₁_lt_arr_size (h₃ : H₃ arr aux low mid high ptr₁ ptr₂ i) : ptr₁ < arr.size :=
  h₃.slice₁_exclusive.ptr_lt_size

def H₃.ptr₂_lt_arr_size (h₃ : H₃ arr aux low mid high ptr₁ ptr₂ i) : ptr₂ < arr.size :=
  h₃.slice₂_exclusive.ptr_lt_size

def H₃.next₁
    (h₃ : H₃ arr aux low mid high ptr₁ ptr₂ i)
    (arr_ptr₁_le_arr_ptr₂ :
      have ptr₁_lt_arr_size := h₃.ptr₁_lt_arr_size
      have ptr₂_lt_arr_size := h₃.ptr₂_lt_arr_size
      Ord.compare arr[ptr₁] arr[ptr₂] ≠ Ordering.gt)
    : have ptr₁_lt_arr_size := h₃.ptr₁_lt_arr_size
      let aux' := aux.set ⟨i, h₃.i_lt_aux_size⟩ arr[ptr₁]
      H₂ arr aux' low mid high ptr₁.succ ptr₂ i.succ
    := by
  intro ptr₁_lt_arr_size aux'
  have aux'_def : aux' = aux.set ⟨i, h₃.i_lt_aux_size⟩ arr[ptr₁] := by rfl
  have slice₁_inclusive := h₃.slice₁_exclusive.increment_ptr
  have size_eq : arr.size = aux'.size := by simp [aux']; exact h₃.size_eq
  have aux_size_eq : aux.size = aux'.size := by simp [aux']
  have slice_i : SlicePtrInclusive aux' low high i.succ :=
    h₃.slice_i_exclusive.increment_ptr.swap_array aux_size_eq
  have i_def : i.succ = ptr₁.succ + ptr₂ - mid := by
    have := h₃.i_def
    have := h₃.slice₂_inclusive.ptr_ge_low
    omega
  have slice_i_left_sorted : slice_i.left.sorted :=
    have ptr₁_in_range : ptr₁ ≥ ptr₁ ∧ ptr₁ < mid := by
      simp [h₃.slice₁_inclusive.ptr_ge_low, h₃.slice₁_exclusive.ptr_lt_high]
    have s_le_arr_ptr₁ : h₃.slice_i.left.le_elem arr[ptr₁] :=
      h₃.slice_i.left.le_elem_of_le h₃.slice_i_left_le_right₁ ptr₁_in_range
    h₃.slice_i.left.sorted_after_sorted_push
      h₃.slice_i_left_sorted
      h₃.i_lt_aux_size
      aux'_def
      slice_i.left
      s_le_arr_ptr₁
  have slice_i_left_le_right₁ : slice_i.left.le slice₁_inclusive.right :=
    h₃.slice_i.left.le_of_swap_ends_le
      (h₃.slice₁_inclusive.sorted_of_right_sorted h₃.slice₁_sorted)
      h₃.slice_i_left_le_right₁
      h₃.i_lt_aux_size
      h₃.ptr₁_lt_arr_size
      aux'_def
      slice_i.left
      slice₁_inclusive.right
      h₃.size_eq
  have slice_i_left_le_right₂ : slice_i.left.le h₃.slice₂_inclusive.right :=
    slice₁_ptr_le_of_succ
      h₃.slice₁_exclusive
      h₃.slice₂_exclusive
      h₃.slice₂_sorted
      h₃.slice_i_exclusive
      slice_i
      aux'_def
      h₃.slice_i_left_le_right₂
      arr_ptr₁_le_arr_ptr₂
  exact {
    h₃ with
    slice₁_inclusive,
    size_eq,
    slice_i,
    i_def,
    slice_i_left_sorted,
    slice_i_left_le_right₁,
    slice_i_left_le_right₂,
  }

def H₃.next₂
    (h₃ : H₃ arr aux low mid high ptr₁ ptr₂ i)
    (arr_ptr₂_lt_arr_ptr₁ :
      have ptr₁_lt_arr_size := h₃.ptr₁_lt_arr_size
      have ptr₂_lt_arr_size := h₃.ptr₂_lt_arr_size
      Ord.compare arr[ptr₁] arr[ptr₂] = Ordering.gt)
    : have ptr₂_lt_arr_size := h₃.ptr₂_lt_arr_size
      let aux' := aux.set ⟨i, h₃.i_lt_aux_size⟩ arr[ptr₂]
      H₂ arr aux' low mid high ptr₁ ptr₂.succ i.succ
    := by
  intro ptr₂_lt_arr_size aux'
  have aux'_def : aux' = aux.set ⟨i, h₃.i_lt_aux_size⟩ arr[ptr₂] := by rfl
  have slice₂_inclusive := h₃.slice₂_exclusive.increment_ptr
  have size_eq : arr.size = aux'.size := by simp [aux']; exact h₃.size_eq
  have aux_size_eq : aux.size = aux'.size := by simp [aux']
  have slice_i : SlicePtrInclusive aux' low high i.succ :=
    h₃.slice_i_exclusive.increment_ptr.swap_array aux_size_eq
  have i_def : i.succ = ptr₁ + ptr₂.succ - mid := by
    have := h₃.i_def
    have := h₃.slice₂_inclusive.ptr_ge_low
    omega
  have slice_i_left_sorted : slice_i.left.sorted :=
    have ptr₂_in_range : ptr₂ ≥ ptr₂ ∧ ptr₂ < high := by
      simp [h₃.slice₂_inclusive.ptr_ge_low, h₃.slice₂_exclusive.ptr_lt_high]
    have s_le_arr_ptr₁ : h₃.slice_i.left.le_elem arr[ptr₂] :=
      h₃.slice_i.left.le_elem_of_le h₃.slice_i_left_le_right₂ ptr₂_in_range
    h₃.slice_i.left.sorted_after_sorted_push
      h₃.slice_i_left_sorted
      h₃.i_lt_aux_size
      aux'_def
      slice_i.left
      s_le_arr_ptr₁
  have slice_i_left_le_right₂ : slice_i.left.le slice₂_inclusive.right :=
    h₃.slice_i.left.le_of_swap_ends_le
      (h₃.slice₂_inclusive.sorted_of_right_sorted h₃.slice₂_sorted)
      h₃.slice_i_left_le_right₂
      h₃.i_lt_aux_size
      h₃.ptr₂_lt_arr_size
      aux'_def
      slice_i.left
      slice₂_inclusive.right
      h₃.size_eq
  have slice_i_left_le_right₁ : slice_i.left.le h₃.slice₁_inclusive.right :=
    slice₂_ptr_le_of_succ
      h₃.slice₁_exclusive
      h₃.slice₂_exclusive
      h₃.slice₁_sorted
      h₃.slice_i_exclusive
      slice_i
      aux'_def
      h₃.slice_i_left_le_right₁
      arr_ptr₂_lt_arr_ptr₁
  exact {
    h₃ with
    slice₂_inclusive,
    size_eq,
    slice_i,
    i_def,
    slice_i_left_sorted,
    slice_i_left_le_right₁,
    slice_i_left_le_right₂,
  }

def H₄.make_H₅
    (h₄ : H₄ arr aux low mid high ptr₁ ptr₂ i)
    (ptr₁_lt_mid : ptr₁ < mid)
    : H₅ arr aux low mid high ptr₁ ptr₂ i :=
  { h₄ with ptr₁_lt_mid }

def H₅.ptr₂_eq_high
    (h₅ : H₅ arr aux low mid high ptr₁ ptr₂ i)
    : ptr₂ = high := by
  have := h₅.ptr₁_lt_mid
  have := h₅.not_ptr₁_ptr₂_in_range
  omega

def H₅.slice₁_exclusive
    (h₅ : H₅ arr aux low mid high ptr₁ ptr₂ i)
    : SlicePtrExclusive arr low mid ptr₁ :=
  h₅.slice₁_inclusive.make_exclusive h₅.ptr₁_lt_mid

def H₅.ptr₁_lt_arr_size
    (h₅ : H₅ arr aux low mid high ptr₁ ptr₂ i)
    : ptr₁ < arr.size :=
  h₅.slice₁_exclusive.ptr_lt_size

def H₅.i_lt_high
    (h₅ : H₅ arr aux low mid high ptr₁ ptr₂ i)
    : i < high := by
  have := h₅.not_ptr₁_ptr₂_in_range
  have := h₅.ptr₁_lt_mid
  have : i = ptr₁ + ptr₂ - mid := h₅.i_def
  have : ptr₁ < high := Nat.le_trans h₅.ptr₁_lt_mid h₅.slice₂.low_le_high
  omega

def H₅.slice_i_exclusive
    (h₅ : H₅ arr aux low mid high ptr₁ ptr₂ i)
    : SlicePtrExclusive aux low high i :=
  h₅.slice_i.make_exclusive h₅.i_lt_high

def H₅.i_lt_aux_size
    (h₅ : H₅ arr aux low mid high ptr₁ ptr₂ i)
    : i < aux.size :=
  h₅.slice_i_exclusive.ptr_lt_size

def H₅.next
    (h₅ : H₅ arr aux low mid high ptr₁ ptr₂ i)
    : have ptr₁_lt_arr_size := h₅.ptr₁_lt_arr_size
      let aux' := aux.set ⟨i, h₅.i_lt_aux_size⟩ arr[ptr₁]
      H₄ arr aux' low mid high ptr₁.succ ptr₂ i.succ := by
  intro ptr₁_lt_arr_size aux'
  have not_ptr₁_ptr₂_in_range : ptr₁.succ = mid ∨ ptr₂ = high := by
    apply Or.intro_right
    exact h₅.ptr₂_eq_high
  have size_eq : arr.size = aux'.size := by simp [aux']; exact h₅.size_eq
  have aux_size_eq : aux.size = aux'.size := by simp [aux']
  have slice_i : SlicePtrInclusive aux' low high i.succ :=
    h₅.slice_i_exclusive.increment_ptr.swap_array aux_size_eq
  have slice₁_inclusive : SlicePtrInclusive arr low mid ptr₁.succ :=
    h₅.slice₁_exclusive.increment_ptr
  have i_def : i.succ = ptr₁.succ + ptr₂ - mid := by
    have := h₅.i_def
    have := h₅.slice₂_inclusive.ptr_ge_low
    omega
  have slice_i_left_sorted : slice_i.left.sorted :=
    have ptr₁_in_range : ptr₁ ≥ ptr₁ ∧ ptr₁ < mid := by
      simp [h₅.slice₁_inclusive.ptr_ge_low, h₅.slice₁_exclusive.ptr_lt_high]
    have s_le_arr_ptr₁ : h₅.slice_i.left.le_elem arr[ptr₁] :=
      h₅.slice_i.left.le_elem_of_le h₅.slice_i_left_le_right₁ ptr₁_in_range
    h₅.slice_i.left.sorted_after_sorted_push
      h₅.slice_i_left_sorted
      h₅.i_lt_aux_size
      rfl
      slice_i.left
      s_le_arr_ptr₁
  have slice_i_left_le_right₁ : slice_i.left.le slice₁_inclusive.right :=
    h₅.slice_i.left.le_of_swap_ends_le
      (h₅.slice₁_inclusive.sorted_of_right_sorted h₅.slice₁_sorted)
      h₅.slice_i_left_le_right₁
      h₅.i_lt_aux_size
      h₅.ptr₁_lt_arr_size
      rfl
      slice_i.left
      slice₁_inclusive.right
      h₅.size_eq
  have slice_i_left_le_right₂ : slice_i.left.le h₅.slice₂_inclusive.right :=
    slice_i.left.le_of_empty₂ (s₂ := h₅.slice₂_inclusive.right) h₅.ptr₂_eq_high
  exact {
    h₅ with
    slice₁_inclusive,
    slice_i,
    not_ptr₁_ptr₂_in_range,
    i_def,
    slice_i_left_sorted,
    slice_i_left_le_right₁,
    slice_i_left_le_right₂,
    size_eq,
  }

def H₇.slice₂_exclusive
    (h₇ : H₇ arr aux low mid high ptr₁ ptr₂ i)
    : SlicePtrExclusive arr mid high ptr₂ :=
  h₇.slice₂_inclusive.make_exclusive h₇.ptr₂_lt_high

def H₇.ptr₂_lt_arr_size
    (h₇ : H₇ arr aux low mid high ptr₁ ptr₂ i)
    : ptr₂ < arr.size :=
  h₇.slice₂_exclusive.ptr_lt_size

def H₇.i_lt_high
    (h₇ : H₇ arr aux low mid high ptr₁ ptr₂ i)
    : i < high := by
  have : i = ptr₁ + ptr₂ - mid := h₇.i_def
  have := h₇.ptr₁_eq_mid
  have := h₇.slice₂_exclusive.ptr_lt_high
  omega

def H₇.slice_i_exclusive
    (h₇ : H₇ arr aux low mid high ptr₁ ptr₂ i)
    : SlicePtrExclusive aux low high i :=
  h₇.slice_i.make_exclusive h₇.i_lt_high

def H₇.i_lt_aux_size
    (h₇ : H₇ arr aux low mid high ptr₁ ptr₂ i)
    : i < aux.size :=
  h₇.slice_i_exclusive.ptr_lt_size

def H₇.next
    (h₇ : H₇ arr aux low mid high ptr₁ ptr₂ i)
    : have ptr₂_lt_arr_size := h₇.ptr₂_lt_arr_size
      let aux' := aux.set ⟨i, h₇.i_lt_aux_size⟩ arr[ptr₂]
      H₆ arr aux' low mid high ptr₁ ptr₂.succ i.succ := by
  intro ptr₂_lt_arr_size aux'
  have size_eq : arr.size = aux'.size := by simp [aux']; exact h₇.size_eq
  have aux_size_eq : aux.size = aux'.size := by simp [aux']
  have slice₂_inclusive : SlicePtrInclusive arr mid high ptr₂.succ :=
    h₇.slice₂_exclusive.increment_ptr
  have slice_i : SlicePtrInclusive aux' low high i.succ :=
    h₇.slice_i_exclusive.increment_ptr.swap_array aux_size_eq
  have not_ptr₁_ptr₂_in_range : ptr₁ = mid ∨ ptr₂.succ = high := by
    apply Or.intro_left
    exact h₇.ptr₁_eq_mid
  have i_def : i.succ = ptr₁ + ptr₂.succ - mid := by
    have := h₇.i_def
    have := h₇.slice₂_inclusive.ptr_ge_low
    omega
  have slice_i_left_sorted : slice_i.left.sorted :=
    have ptr₂_in_range : ptr₂ ≥ ptr₂ ∧ ptr₂ < high := by
      simp [h₇.slice₂_inclusive.ptr_ge_low, h₇.slice₂_exclusive.ptr_lt_high]
    have s_le_arr_ptr₁ : h₇.slice_i.left.le_elem arr[ptr₂] :=
      h₇.slice_i.left.le_elem_of_le h₇.slice_i_left_le_right₂ ptr₂_in_range
    h₇.slice_i.left.sorted_after_sorted_push
      h₇.slice_i_left_sorted
      h₇.i_lt_aux_size
      rfl
      slice_i.left
      s_le_arr_ptr₁
  have slice_i_left_le_right₁ : slice_i.left.le h₇.slice₁_inclusive.right :=
    slice_i.left.le_of_empty₂ h₇.ptr₁_eq_mid
  have slice_i_left_le_right₂ : slice_i.left.le slice₂_inclusive.right :=
    h₇.slice_i.left.le_of_swap_ends_le
      (h₇.slice₂_inclusive.sorted_of_right_sorted h₇.slice₂_sorted)
      h₇.slice_i_left_le_right₂
      h₇.i_lt_aux_size
      h₇.ptr₂_lt_arr_size
      rfl
      slice_i.left
      slice₂_inclusive.right
      h₇.size_eq
  exact {
    h₇ with
    slice₂_inclusive,
    slice_i,
    not_ptr₁_ptr₂_in_range,
    i_def,
    slice_i_left_sorted,
    slice_i_left_le_right₁,
    slice_i_left_le_right₂,
    size_eq,
  }

@[specialize, inline]
def mergeAdjacentChunksIntoAux
    (h₁ : H₁ arr aux low mid high)
    : Array α :=
  -- Copy the lowest element from the left (slice₁) and right (slice₂)
  -- regions until one of them is fully copied.
  let rec @[specialize] loop
      (aux : Array α)
      (i ptr₁ ptr₂ : ℕ)
      (h₂ : H₂ arr aux low mid high ptr₁ ptr₂ i)
      : Array α :=
    if ptr₁_ptr₂_in_range : ptr₁ < mid ∧ ptr₂ < high then
      have h₃ := h₂.make_H₃ ptr₁_ptr₂_in_range
      have ptr₁_lt_arr_size := h₃.ptr₁_lt_arr_size
      have ptr₂_lt_arr_size := h₃.ptr₂_lt_arr_size
      let comparison := Ord.compare arr[ptr₁] arr[ptr₂]
      if h : comparison ≠ .gt then
        let aux' := aux.set ⟨i, h₃.i_lt_aux_size⟩ arr[ptr₁]
        loop aux' i.succ ptr₁.succ ptr₂ (h₃.next₁ h)
      else
        have h : comparison = .gt := by simp at h; exact h
        let aux' := aux.set ⟨i, h₃.i_lt_aux_size⟩ arr[ptr₂]
        loop aux' i.succ ptr₁ ptr₂.succ (h₃.next₂ h)
    else
      -- If the left region (slice₁) is not yet empty, finish copying it.
      let rec @[specialize] loopLeft
          (aux : Array α)
          (i ptr₁ : ℕ)
          (h₄ : H₄ arr aux low mid high ptr₁ ptr₂ i)
          : Array α :=
        if ptr₁_lt_mid : ptr₁ < mid then
          have h₅ := h₄.make_H₅ ptr₁_lt_mid
          have : ptr₁ < arr.size := h₅.ptr₁_lt_arr_size
          have i_lt_aux_size : i < aux.size := h₅.i_lt_aux_size
          let aux' := aux.set ⟨i, i_lt_aux_size⟩ arr[ptr₁]
          loopLeft aux' i.succ ptr₁.succ h₅.next
        else
          -- If the right region (slice₂) is not yet empty, finish copying it.
          let rec @[specialize] loopRight
              (aux : Array α)
              (i ptr₂ : ℕ)
              (h₆ : H₆ arr aux low mid high ptr₁ ptr₂ i)
              : Array α :=
            if ptr₂_lt_high : ptr₂ < high then
              have h₇ := h₆.make_H₇ ptr₂_lt_high
              have : ptr₂ < arr.size := h₇.ptr₂_lt_arr_size
              have i_lt_aux_size : i < aux.size := h₇.i_lt_aux_size
              let aux' := aux.set ⟨i, i_lt_aux_size⟩ arr[ptr₂]
              loopRight aux' i.succ ptr₂.succ h₇.next
            else
              aux
          loopRight aux i ptr₂ (h₄.make_H₆ ptr₁_lt_mid)
      loopLeft aux i ptr₁ (h₂.make_H₄ ptr₁_ptr₂_in_range)
  let ptr₁ := low
  let ptr₂ := mid
  let i := ptr₁
  have h₂ := h₁.make_H₂ rfl rfl rfl
  loop aux i ptr₁ ptr₂ h₂

-- structure H₅ : Prop where
--   arr_size_eq_aux_size : arr.size = aux.size
--   chunkSize_gt_0 : chunkSize > 0

-- def H₅.mkH₁
--     (h₅ : H₅ arr aux chunkSize)
--     (start₁_plus_chunkSize_lt_arr_size : start₁ + chunkSize < arr.size)
--     : have start₂' := start₁ + chunkSize
--       have end₂' := min (start₂' + chunkSize) arr.size
--       H₁ arr aux start₁ start₂' end₂'
--     := by
--   intro start₂' end₂'
--   have start₁_lt_start₂ : start₁ < start₂' := by
--     have := h₅.chunkSize_gt_0
--     omega
--   have start₂_lt_end₂ : start₂' < end₂' := by
--     simp [end₂']
--     apply And.intro
--     . case left =>
--       exact h₅.chunkSize_gt_0
--     . case right =>
--       exact start₁_plus_chunkSize_lt_arr_size
--   have end₂_le_arr_size : end₂' ≤ arr.size := by omega
--   exact {
--     h₅ with
--     start₁_lt_start₂,
--     start₂_lt_end₂,
--     end₂_le_arr_size
--   }

-- theorem mergeAdjacentChunksIntoAux.loop.loopLeft.loopRight_size_eq
--     {aux : Array α}
--     {i k₂ : ℕ}
--     {h₄Right : H₄Right arr aux start₁ start₂ end₂ i k₁ k₂}
--     : have aux' := mergeAdjacentChunksIntoAux.loop.loopLeft.loopRight arr start₁ start₂ end₂ k₁ aux i k₂ h₄Right
--       arr.size = aux'.size
--     := by
--   unfold loopRight
--   if k₂_lt_end₂ : k₂ < end₂ then
--     simp [k₂_lt_end₂]
--     exact mergeAdjacentChunksIntoAux.loop.loopLeft.loopRight_size_eq
--   else
--     simp [k₂_lt_end₂, h₄Right.arr_size_eq_aux_size]

-- theorem mergeAdjacentChunksIntoAux.loop.loopLeft_size_eq
--     {aux : Array α}
--     {i k₁ : ℕ}
--     {h₂ : H₂ arr aux start₁ start₂ end₂ i k₁ k₂}
--     : have aux' := mergeAdjacentChunksIntoAux.loop.loopLeft arr start₁ start₂ end₂ k₂ aux i k₁ h₂
--       arr.size = aux'.size
--     := by
--   unfold loopLeft
--   if k₂_lt_start₂ : k₁ < start₂ then
--     simp [k₂_lt_start₂]
--     exact mergeAdjacentChunksIntoAux.loop.loopLeft_size_eq
--   else
--     simp [k₂_lt_start₂, ← mergeAdjacentChunksIntoAux.loop.loopLeft.loopRight_size_eq]

-- theorem mergeAdjacentChunksIntoAux.loop_size_eq
--     {aux : Array α}
--     {i k₁ k₂ : ℕ}
--     {h₂ : H₂ arr aux start₁ start₂ end₂ i k₁ k₂}
--     : have aux' := mergeAdjacentChunksIntoAux.loop arr start₁ start₂ end₂ aux i k₁ k₂ h₂
--       arr.size = aux'.size
--     := by
--   unfold loop
--   if k₁_k₂_in_range : k₁ < start₂ ∧ k₂ < end₂ then
--     simp [k₁_k₂_in_range]
--     split <;> rw [← mergeAdjacentChunksIntoAux.loop_size_eq]
--   else
--     simp [k₁_k₂_in_range, ← mergeAdjacentChunksIntoAux.loop.loopLeft_size_eq]
-- termination_by aux.size - i
-- decreasing_by
--   all_goals
--     simp_wf
--     have h₃ := h₂.make_H₃ k₁_k₂_in_range
--     have i_lt_aux_size : i < aux.size := h₃.i_lt_aux_size
--     exact loop.loopLeft.loopRight_decreasing aux.size i i_lt_aux_size

-- theorem mergeAdjacentChunksIntoAux_size_eq
--     {aux : Array α}
--     {h₁ : H₁ arr aux start₁ start₂ end₂}
--     : have aux' := mergeAdjacentChunksIntoAux arr aux start₁ start₂ end₂ h₁
--       arr.size = aux'.size
--     := by
--   exact mergeAdjacentChunksIntoAux.loop_size_eq arr start₁ start₂ end₂

-- def H₅.next
--     {chunkSize : ℕ}
--     (h₅ : H₅ arr aux chunkSize)
--     (start₁_plus_chunkSize_lt_arr_size : start₁ + chunkSize < arr.size)
--     : let start₂' := start₁ + chunkSize
--       have start₂'_def : start₂' = start₁ + chunkSize := by rfl
--       let end₂' := min (start₂' + chunkSize) arr.size
--       have end₂'_def : end₂' = min (start₂' + chunkSize) arr.size := by rfl
--       have h₁ : H₁ arr aux start₁ start₂' end₂' := by
--         have h₁ := h₅.mkH₁ arr aux start₁ chunkSize start₁_plus_chunkSize_lt_arr_size
--         simp at h₁
--         simp [start₂'_def, end₂'_def]
--         exact h₁
--       have aux' := mergeAdjacentChunksIntoAux arr aux start₁ start₂' end₂' h₁
--       H₅ arr aux' chunkSize
--     := by
--   intro start₂' start₂'_def end₂' end₂'_def h₁ aux'
--   have arr_size_eq_aux'_size : arr.size = aux'.size := by
--     simp [aux']
--     exact mergeAdjacentChunksIntoAux_size_eq arr start₁ start₂' end₂'
--   exact {
--     h₅ with
--     arr_size_eq_aux_size := arr_size_eq_aux'_size,
--   }

-- def H₅.nextFinal
--     {arr aux : Array α}
--     {chunkSize start₁ : ℕ}
--     (h₅ : H₅ arr aux chunkSize)
--     (start₁_lt_aux_size : start₁ < aux.size)
--     : have := h₅.arr_size_eq_aux_size
--       let aux' := aux.set ⟨start₁, start₁_lt_aux_size⟩ arr[start₁]
--       H₅ arr aux' chunkSize
--     := by
--   intro arr_size_eq_aux_size aux'
--   have arr_size_eq_aux'_size : arr.size = aux'.size := by
--     simp [aux', h₅.arr_size_eq_aux_size]
--   exact {
--     h₅ with
--     arr_size_eq_aux_size := arr_size_eq_aux'_size
--   }

-- @[specialize, inline]
-- def mergeChunksIntoAux
--   (arr aux : Array α)
--   (chunkSize : ℕ)
--   (h₅ : H₅ arr aux chunkSize) :=
--   -- Merge every two adjacent chunks while the second chunk has at least one
--   -- element.
--   let rec @[specialize] loop
--       (aux : Array α)
--       (start₁ : ℕ)
--       (h₅ : H₅ arr aux chunkSize)
--       : Array α :=
--     if start₁_plus_chunkSize_lt_arr_size : start₁ + chunkSize < arr.size then
--       let start₂ := start₁ + chunkSize
--       let end₂ := min (start₂ + chunkSize) arr.size
--       have h₁ := h₅.mkH₁ arr aux start₁ chunkSize start₁_plus_chunkSize_lt_arr_size
--       let aux' := mergeAdjacentChunksIntoAux arr aux start₁ start₂ end₂ h₁
--       have h₅ := h₅.next arr aux start₁ start₁_plus_chunkSize_lt_arr_size
--       loop aux' (start₁ + 2 * chunkSize) h₅
--     else
--       -- Copy any leftover elements directly to `aux`.
--       --
--       -- This can happen, for example, when calling this function with
--       --       `arr  := #[1, 2, 3, 10, 20, 30, 100, 200]`
--       --   and `size := 3`,
--       -- as the first loop with merge `#[1, 2, 3]` and `#[20, 30, 100]` together, but
--       -- because there are too few leftover elements to form two adjacent chunks,
--       -- it is unable to do any further merging. Thus, the leftover elements, `100`
--       -- and `200`, must be directly copied over into `aux`.
--       let rec @[specialize] loopFinal
--           (aux : Array α)
--           (start₁' : ℕ)
--           (h₅ : H₅ arr aux chunkSize)
--           : Array α :=
--         if start₁_lt_aux_size : start₁' < aux.size then
--           have := h₅.arr_size_eq_aux_size
--           let aux' := aux.set ⟨start₁', start₁_lt_aux_size⟩ arr[start₁']
--           have h₅ := h₅.nextFinal start₁_lt_aux_size
--           loopFinal aux' start₁'.succ h₅
--         else
--           aux
--       loopFinal aux start₁ h₅
--   termination_by arr.size - start₁
--   decreasing_by
--     simp_wf
--     have := h₅.chunkSize_gt_0
--     omega
--   loop aux 0 h₅

-- theorem mergeChunksIntoAux.loop.loopFinal_size_eq
--     {arr aux : Array α}
--     {start₁ chunkSize : ℕ}
--     {h₅ : H₅ arr aux chunkSize}
--     : let aux' := mergeChunksIntoAux.loop.loopFinal arr chunkSize start₁ aux start₁' h₅
--       arr.size = aux'.size
--     := by
--   unfold loopFinal
--   if start₁_lt_aux_size : start₁' < aux.size then
--     simp [start₁_lt_aux_size]
--     have := h₅.arr_size_eq_aux_size
--     have h₅ := h₅.nextFinal start₁_lt_aux_size
--     simp at h₅
--     exact mergeChunksIntoAux.loop.loopFinal_size_eq
--       (start₁ := start₁)
--       (start₁' := start₁'.succ)
--       (h₅ := h₅)
--   else
--     simp [start₁_lt_aux_size]
--     exact h₅.arr_size_eq_aux_size

-- theorem mergeChunksIntoAux.loop_size_eq
--     {arr aux : Array α}
--     {start₁ chunkSize : ℕ}
--     {h₅ : H₅ arr aux chunkSize}
--     : let aux' := mergeChunksIntoAux.loop arr chunkSize aux start₁ h₅
--       arr.size = aux'.size
--     := by
--   unfold loop
--   if start₁_plus_chunkSize_lt_arr_size : start₁ + chunkSize < arr.size then
--     simp [start₁_plus_chunkSize_lt_arr_size]
--     exact mergeChunksIntoAux.loop_size_eq
--   else
--     simp [start₁_plus_chunkSize_lt_arr_size]
--     exact mergeChunksIntoAux.loop.loopFinal_size_eq
-- termination_by arr.size - start₁
-- decreasing_by
--   simp_wf
--   have := h₅.chunkSize_gt_0
--   omega

-- theorem mergeChunksIntoAux_size_eq
--     {arr aux : Array α}
--     {h₅ : H₅ arr aux chunkSize}
--     : let aux' := mergeChunksIntoAux arr aux chunkSize h₅
--       arr.size = aux'.size
--     := by
--   exact mergeChunksIntoAux.loop_size_eq

-- def H₅.nextChunk
--     (h₅ : H₅ arr aux chunkSize)
--     : let aux' := mergeChunksIntoAux arr aux chunkSize h₅
--       H₅ aux' arr (chunkSize * 2)
--     := by
--   intro aux'
--   have aux'_size_eq_arr_size : aux'.size = arr.size := by
--     symm
--     have h := @mergeChunksIntoAux_size_eq α ord_a chunkSize arr aux h₅
--     exact h
--   have chunkSize_mul_two_gt_0 : chunkSize * 2 > 0 := by
--     have := h₅.chunkSize_gt_0
--     omega
--   exact {
--     arr_size_eq_aux_size := aux'_size_eq_arr_size
--     chunkSize_gt_0 := chunkSize_mul_two_gt_0
--   }

-- @[specialize]
-- def Array.mergeSort : Array α :=
--   let rec @[specialize] loop
--       (arr aux : Array α)
--       (chunkSize : ℕ)
--       (h₅ : H₅ arr aux chunkSize)
--       : Array α :=
--     if chunkSize < arr.size then
--       let aux' := mergeChunksIntoAux arr aux chunkSize h₅
--       have h₅' : H₅ aux' arr (chunkSize * 2) := h₅.nextChunk

--       -- Note: `aux` and `arr` are intentionally swapped in the recursive call
--       loop aux' arr (chunkSize * 2) h₅'
--     else
--       arr
--   termination_by arr.size - chunkSize
--   decreasing_by
--     simp_wf
--     have := h₅.chunkSize_gt_0
--     have := @mergeChunksIntoAux_size_eq α ord_a chunkSize arr aux h₅
--     omega
--   let aux := arr
--   have h₅ := {
--     arr_size_eq_aux_size := by rfl
--     chunkSize_gt_0 := by decide
--   }
--   loop arr aux 1 h₅

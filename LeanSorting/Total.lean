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

structure H₂a (arr aux : Array α) (low mid high ptr₁ ptr₂ i : ℕ)
    extends H₂ arr aux low mid high ptr₁ ptr₂ i : Prop where
  not_ptr₁_ptr₂_in_range : ptr₁ = mid ∨ ptr₂ = high

structure H₂a₁ (arr aux : Array α) (low mid high ptr₁ ptr₂ i : ℕ)
    extends H₂a arr aux low mid high ptr₁ ptr₂ i : Prop where
  ptr₁_lt_mid : ptr₁ < mid

def H₁.make_h₂
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


-- def H₂.mk_i_lt_aux_size
--     (h₂ : H₂ arr aux start₁ start₂ end₂ i k₁ k₂)
--     (k₁_lt_start₂ : k₁ < start₂)
--     : i < aux.size := by
--   have := h₂.start₂_lt_end₂
--   have := h₂.end₂_le_arr_size
--   have := h₂.arr_size_eq_aux_size
--   have := h₂.i_def
--   have := h₂.k₂_lt_end₂_succ
--   omega

def H₂.i_lt_aux_size
    (h₂ : H₂ arr aux low mid high ptr₁ ptr₂ i)
    (ptr₁_lt_mid : ptr₁ < mid)
    (ptr₂_eq_high : ptr₂ = high)
    : i < aux.size := by
  have : i = ptr₁ + ptr₂ - mid := h₂.i_def
  have : ptr₁ < high := Nat.le_trans ptr₁_lt_mid h₂.slice₂.low_le_high
  have i_lt_high : i < high := by omega
  exact (h₂.slice_i.make_exclusive i_lt_high).ptr_lt_size
  -- have : mid < high := by
  --   -- have := h₂.
  --   omega
  -- have : high ≤ arr.size := sorry
  -- have : arr.size = aux.size := sorry
  -- have : i = ptr₁ + ptr₂ - mid := sorry
  -- have : ptr₂ < high.succ := sorry
  -- omega

structure H₃ (arr aux : Array α) (low mid high ptr₁ ptr₂ i : ℕ)
    extends H₂ arr aux low mid high ptr₁ ptr₂ i : Prop where
  slice₁_exclusive : SlicePtrExclusive arr low mid ptr₁
  slice₂_exclusive : SlicePtrExclusive arr mid high ptr₂
  slice_i_exclusive : SlicePtrExclusive aux low high i

def H₂.mkH₃
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

def H₃.nextLeft
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

def H₃.nextRight
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

-- def H₂.mk_i_lt_aux_size
--     (h₂ : H₂ arr aux start₁ start₂ end₂ i k₁ k₂)
--     (k₁_lt_start₂ : k₁ < start₂)
--     : i < aux.size := by
--   have := h₂.start₂_lt_end₂
--   have := h₂.end₂_le_arr_size
--   have := h₂.arr_size_eq_aux_size
--   have := h₂.i_def
--   have := h₂.k₂_lt_end₂_succ
--   omega

-- def H₂.mk_k₁_lt_arr_size
--     (h₂ : H₂ arr aux start₁ start₂ end₂ i k₁ k₂)
--     (k₁_lt_start₂ : k₁ < start₂)
--     : k₁ < arr.size := by
--   have := h₂.start₂_lt_end₂
--   have := h₂.end₂_le_arr_size
--   omega

-- def H₂.nextLeft
--     (h₂ : H₂ arr aux start₁ start₂ end₂ i k₁ k₂)
--     (k₁_lt_start₂ : k₁ < start₂)
--     : have i_lt_aux_size : i < aux.size := h₂.mk_i_lt_aux_size k₁_lt_start₂
--       have k₁_lt_arr_size : k₁ < arr.size := h₂.mk_k₁_lt_arr_size k₁_lt_start₂
--       have aux' := aux.set ⟨i, i_lt_aux_size⟩ arr[k₁]
--       H₂ arr aux' start₁ start₂ end₂ i.succ k₁.succ k₂
--     := by
--   intro i_lt_aux_size k₁_lt_arr_size aux'
--   let arr_size_eq_aux'_size : arr.size = aux'.size := by
--     simp [aux']
--     exact h₂.arr_size_eq_aux_size
--   have i_succ_def : i.succ = k₁.succ + k₂ - start₂ := by
--     have := h₂.i_def
--     have := h₂.k₂_ge_start₂
--     omega
--   have k₁_succ_lt_start₂_succ : k₁.succ < start₂.succ := by
--     omega
--   exact
--     { h₂ with
--       arr_size_eq_aux_size := arr_size_eq_aux'_size
--       i_def := i_succ_def
--       k₁_lt_start₂_succ := k₁_succ_lt_start₂_succ
--     }

-- structure H₄Right extends H₁ arr aux start₁ start₂ end₂ : Prop where
--   i_def : i = k₁ + k₂ - start₂
--   k₂_ge_start₂ : k₂ ≥ start₂
--   k₁_lt_start₂_succ : k₁ < start₂.succ
--   not_k₁_lt_start₂ : ¬k₁ < start₂

-- def H₂.mkH₄Right
--     (h₂ : H₂ arr aux start₁ start₂ end₂ i k₁ k₂)
--     (not_k₁_lt_start₂ : ¬k₁ < start₂)
--     : H₄Right arr aux start₁ start₂ end₂ i k₁ k₂ :=
--   { h₂ with not_k₁_lt_start₂ }

-- def H₄Right.mk_i_lt_aux_size
--     (h₄Right : H₄Right arr aux start₁ start₂ end₂ i k₁ k₂)
--     (k₂_lt_end₂ : k₂ < end₂)
--     : i < aux.size := by
--   have := h₄Right.end₂_le_arr_size
--   have := h₄Right.arr_size_eq_aux_size
--   have := h₄Right.i_def
--   have := h₄Right.k₁_lt_start₂_succ
--   omega

-- def H₄Right.mk_k₂_lt_arr_size
--     (h₄Right : H₄Right arr aux start₁ start₂ end₂ i k₁ k₂)
--     (k₂_lt_end₂ : k₂ < end₂)
--     : k₂ < arr.size := by
--   have := h₄Right.end₂_le_arr_size
--   omega

-- def H₄Right.next
--     (h₄Right : H₄Right arr aux start₁ start₂ end₂ i k₁ k₂)
--     (k₂_lt_end₂ : k₂ < end₂)
--     : have i_lt_aux_size := h₄Right.mk_i_lt_aux_size k₂_lt_end₂
--       have k₂_lt_arr_Size := h₄Right.mk_k₂_lt_arr_size k₂_lt_end₂
--       let aux' := aux.set ⟨i, i_lt_aux_size⟩ arr[k₂]
--       H₄Right arr aux' start₁ start₂ end₂ i.succ k₁ k₂.succ
--     := by
--   intro i_lt_aux_size k₂_lt_arr_size aux'
--   have arr_size_eq_aux'_size : arr.size = aux'.size := by
--     simp [aux']
--     exact h₄Right.arr_size_eq_aux_size
--   have i_succ_def : i.succ = k₁ + k₂.succ - start₂ := by
--     have := h₄Right.i_def
--     have := h₄Right.k₂_ge_start₂
--     omega
--   have k₂_succ_ge_start₂ : k₂.succ ≥ start₂ := by
--     have := h₄Right.k₂_ge_start₂
--     omega
--   exact
--     { h₄Right with
--       arr_size_eq_aux_size := arr_size_eq_aux'_size
--       i_def := i_succ_def
--       k₂_ge_start₂ := k₂_succ_ge_start₂
--     }

-- def mergeAdjacentChunksIntoAux.loop.loopLeft_decreasing
--     (k₁_lt_start₂ : k₁ < start₂)
--     : start₂ - (k₁ + 1) < start₂ - k₁ := by
--   omega

-- def mergeAdjacentChunksIntoAux.loop.loopLeft.loopRight_decreasing
--     (k₂_lt_end₂ : k₂ < end₂)
--     : end₂ - (k₂ + 1) < end₂ - k₂ := by
--   omega

def H₂a.make_h₂a₁
    (h₂a : H₂a arr aux low mid high ptr₁ ptr₂ i)
    (ptr₁_lt_mid : ptr₁ < mid)
    : H₂a₁ arr aux low mid high ptr₁ ptr₂ i :=
  { h₂a with ptr₁_lt_mid }

def H₂a₁.ptr₂_eq_high
    (h₂a₁ : H₂a₁ arr aux low mid high ptr₁ ptr₂ i)
    : ptr₂ = high := by
  have := h₂a₁.ptr₁_lt_mid
  have := h₂a₁.not_ptr₁_ptr₂_in_range
  omega

def H₂a₁.slice₁_exclusive
    (h₂a₁ : H₂a₁ arr aux low mid high ptr₁ ptr₂ i)
    : SlicePtrExclusive arr low mid ptr₁ :=
  h₂a₁.slice₁_inclusive.make_exclusive h₂a₁.ptr₁_lt_mid

def H₂a₁.ptr₁_lt_arr_size
    (h₂a₁ : H₂a₁ arr aux low mid high ptr₁ ptr₂ i)
    : ptr₁ < arr.size :=
  h₂a₁.slice₁_exclusive.ptr_lt_size

def H₂a₁.i_lt_high
    (h₂a₁ : H₂a₁ arr aux low mid high ptr₁ ptr₂ i)
    : i < high := by
  have := h₂a₁.not_ptr₁_ptr₂_in_range
  have := h₂a₁.ptr₁_lt_mid
  have : i = ptr₁ + ptr₂ - mid := h₂a₁.i_def
  have : ptr₁ < high := Nat.le_trans h₂a₁.ptr₁_lt_mid h₂a₁.slice₂.low_le_high
  omega

def H₂a₁.slice_i_exclusive
    (h₂a₁ : H₂a₁ arr aux low mid high ptr₁ ptr₂ i)
    : SlicePtrExclusive aux low high i :=
  h₂a₁.slice_i.make_exclusive h₂a₁.i_lt_high

def H₂a₁.i_lt_aux_size
    (h₂a₁ : H₂a₁ arr aux low mid high ptr₁ ptr₂ i)
    : i < aux.size := by
  exact h₂a₁.slice_i_exclusive.ptr_lt_size

def H₂a₁.nextLeft
    (h₂a₁ : H₂a₁ arr aux low mid high ptr₁ ptr₂ i)
    : have ptr₁_lt_arr_size := h₂a₁.ptr₁_lt_arr_size
      let aux' := aux.set ⟨i, h₂a₁.i_lt_aux_size⟩ arr[ptr₁]
      H₂a arr aux' low mid high ptr₁.succ ptr₂ i.succ := by
  intro ptr₁_lt_arr_size aux'
  have not_ptr₁_ptr₂_in_range : ptr₁.succ = mid ∨ ptr₂ = high := by
    apply Or.intro_right
    exact h₂a₁.ptr₂_eq_high
  have size_eq : arr.size = aux'.size := by simp [aux']; exact h₂a₁.size_eq
  have aux_size_eq : aux.size = aux'.size := by simp [aux']
  have slice_i : SlicePtrInclusive aux' low high i.succ :=
    h₂a₁.slice_i_exclusive.increment_ptr.swap_array aux_size_eq
  have slice₁_inclusive : SlicePtrInclusive arr low mid ptr₁.succ := sorry
  have i_def : i.succ = ptr₁.succ + ptr₂ - mid := sorry
  have slice_i_left_sorted : slice_i.left.sorted := sorry
  have slice_i_left_le_right₁ : slice_i.left.le slice₁_inclusive.right := sorry
  have slice_i_left_le_right₂ : slice_i.left.le h₂a₁.slice₂_inclusive.right := sorry
  exact {
    h₂a₁ with
    slice₁_inclusive,
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
  -- Copy the lowest element from the left and right regions until one of them is fully copied.
  let rec @[specialize] loop
      (aux : Array α)
      (i ptr₁ ptr₂ : ℕ)
      (h₂ : H₂ arr aux low mid high ptr₁ ptr₂ i)
      : Array α :=
    if ptr₁_ptr₂_in_range : ptr₁ < mid ∧ ptr₂ < high then
      have h₃ := h₂.mkH₃ ptr₁_ptr₂_in_range
      have ptr₁_lt_arr_size := h₃.ptr₁_lt_arr_size
      have ptr₂_lt_arr_size := h₃.ptr₂_lt_arr_size
      let comparison := Ord.compare arr[ptr₁] arr[ptr₂]
      if h : comparison ≠ .gt then
        let aux' := aux.set ⟨i, h₃.i_lt_aux_size⟩ arr[ptr₁]
        loop aux' i.succ ptr₁.succ ptr₂ (h₃.nextLeft h)
      else
        have h : comparison = .gt := by simp at h; exact h
        let aux' := aux.set ⟨i, h₃.i_lt_aux_size⟩ arr[ptr₂]
        loop aux' i.succ ptr₁ ptr₂.succ (h₃.nextRight h)
    else
      -- If the left region is not yet empty, finish copying it.
      let rec @[specialize] loopLeft
          (aux : Array α)
          (i ptr₁ : ℕ)
          (h₂a : H₂a arr aux low mid high ptr₁ ptr₂ i)
          : Array α :=
        if ptr₁_lt_mid : ptr₁ < mid then
          have h₂a₁ := h₂a.make_h₂a₁ ptr₁_lt_mid
          have : ptr₁ < arr.size := h₂a₁.ptr₁_lt_arr_size
          have i_lt_aux_size : i < aux.size := h₂a₁.i_lt_aux_size
          let aux' := aux.set ⟨i, i_lt_aux_size⟩ arr[ptr₁]
          loopLeft aux' i.succ ptr₁.succ h₂a₁.nextLeft
        else
          sorry
          -- If the right region is not yet empty, finish copying it.
          -- let rec @[specialize] loopRight
          --     (aux : Array α)
          --     (i k₂ : ℕ)
          --     (h₄Right : H₄Right arr aux start₁ start₂ end₂ i k₁ k₂)
          --     : Array α :=
          --   if k₂_lt_end₂ : k₂ < end₂ then
          --     have : k₂ < arr.size := h₄Right.mk_k₂_lt_arr_size k₂_lt_end₂
          --     have i_lt_aux_size : i < aux.size := h₄Right.mk_i_lt_aux_size k₂_lt_end₂
          --     let aux' := aux.set ⟨i, i_lt_aux_size⟩ arr[k₂]
          --     loopRight aux' i.succ k₂.succ (h₄Right.next k₂_lt_end₂)
          --   else
          --     aux
          -- -- These termination proofs can be automatically inferred, but stating
          -- -- them explicitly makes this function compile a lot faster.
          -- termination_by end₂ - k₂
          -- decreasing_by exact mergeAdjacentChunksIntoAux.loop.loopLeft.loopRight_decreasing end₂ k₂ k₂_lt_end₂
          -- loopRight aux i k₂ (h₂.mkH₄Right k₁_lt_start₂)
      -- termination_by start₂ - k₁
      -- decreasing_by exact mergeAdjacentChunksIntoAux.loop.loopLeft_decreasing start₂ k₁ k₁_lt_start₂
      loopLeft aux i ptr₁
        { h₂ with
          not_ptr₁_ptr₂_in_range := by
            have := h₂.slice₁_inclusive.ptr_le_high
            have := h₂.slice₂_inclusive.ptr_le_high
            omega
        }
  -- termination_by arr.size - i
  -- decreasing_by
  --   all_goals
  --     have i_lt_arr_size : i < arr.size := by
  --       rw [h₂.arr_size_eq_aux_size]
  --       exact (h₂.mkH₃ k₁_k₂_in_range).i_lt_aux_size
  --     exact (Nat.sub_succ_lt_sub_of_lt i_lt_arr_size)
  let ptr₁ := low
  let ptr₂ := mid
  let i := ptr₁
  have h₂ := h₁.make_h₂ rfl rfl rfl
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
--     have h₃ := h₂.mkH₃ k₁_k₂_in_range
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

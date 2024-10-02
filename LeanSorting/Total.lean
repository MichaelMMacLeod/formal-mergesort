import Mathlib.Data.Nat.ModEq
import Batteries.Classes.Order
import Init.Data.Array.Lemmas

open Batteries

theorem Nat.lt_of_lt_le {a b c : ℕ} (h : a < b) : b ≤ c → a < c := by omega
theorem Nat.lt_of_le_lt {a b c : ℕ} (h : a ≤ b) : b < c → a < c := by omega
theorem Nat.sub_succ_lt_sub_of_lt {a b : ℕ} (h : a < b) : b - a.succ < b - a := by omega

def Nat.in_range (n : ℕ) (low high : ℕ) : Prop := n ≥ low ∧ n < high
def Nat.adjacent_in_range (n m low high : ℕ) : Prop := n.succ = m ∧ n ≥ low ∧ m < high

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

structure Slice (arr : Array α) (low high : ℕ) : Prop where
  low_le_high : low ≤ high
  high_le_size : high ≤ arr.size

-- def Slice.mkEmpty (arr : Array α) (low high : ℕ) (h_empty : low = high) : Slice arr low high :=
--   { low_le_high := h_empty,
--     high_le_size :=

--   }

-- inductive Slice.pairwise : Slice arr low high → Prop where
--   | empty : ∀ {s : Slice arr low high}, low = high → s.pairwise
--   |

structure SlicePtrExclusive (arr : Array α) (low high : ℕ) (ptr : ℕ)
    extends Slice arr low high : Prop where
  ptr_ge_low : ptr ≥ low
  ptr_lt_high : ptr < high

structure SlicePtrInclusive (arr : Array α) (low high : ℕ) (ptr : ℕ)
    extends Slice arr low high : Prop where
  ptr_ge_low : ptr ≥ low
  ptr_le_high : ptr ≤ high

-- In a slice [a, b, c, d, e, >f<, g] with pointer at 'f', the left half is [a, b, c, d, e].
def SlicePtrInclusive.left (s : SlicePtrInclusive arr low high ptr) : Slice arr low ptr :=
  { low_le_high := s.ptr_ge_low
    high_le_size := Nat.le_trans s.ptr_le_high s.high_le_size
  }

def SlicePtrInclusive.right (s : SlicePtrInclusive arr low high ptr) : Slice arr ptr high :=
  { low_le_high := s.ptr_le_high
    high_le_size := s.high_le_size
  }

def Slice.swap_arr
    (s : Slice arr low high)
    (size_eq : arr.size = aux.size)
    : Slice aux low high :=
  { s with high_le_size := by rw [← size_eq]; exact s.high_le_size }

def SlicePtrExclusive.swap_arr
    (s : SlicePtrExclusive arr low high ptr)
    (size_eq : arr.size = aux.size)
    : SlicePtrExclusive aux low high ptr :=
  { s with
    high_le_size := by rw [← size_eq]; exact s.high_le_size
  }

def SlicePtrInclusive.swap_arr
    (s : SlicePtrInclusive arr low high ptr)
    (size_eq : arr.size = aux.size)
    : SlicePtrInclusive aux low high ptr :=
  { s with
    high_le_size := by rw [← size_eq]; exact s.high_le_size
  }

def SlicePtrExclusive.next
    (s : SlicePtrExclusive arr low high ptr)
    : SlicePtrInclusive arr low high ptr.succ :=
  { s with
    ptr_ge_low := by have := s.ptr_ge_low; omega,
    ptr_le_high := s.ptr_lt_high,
  }

def SlicePtrInclusive.mkExclusive
    (s : SlicePtrInclusive arr low high ptr)
    (ptr_lt_high : ptr < high)
    : SlicePtrExclusive arr low high ptr :=
  { s with ptr_lt_high }

def Slice.sorted [Batteries.LawfulOrd α] (_s : Slice arr low high) : Prop :=
  ∀ (i₁ i₂ : Fin arr.size)
    (_adjacent_in_range : i₁.val.adjacent_in_range i₂ low high),
      Ord.compare arr[i₁] arr[i₂] ≠ Ordering.gt

-- def Slice.sorted₂ {arr : Array α} {low high : ℕ} (s : Slice arr low high) : Prop :=
--   (low_succ_lt_high : low.succ < high) →
--     let high_le_size := s.high_le_size
--     let s' : Slice arr low.succ high := {
--       low_le_high := by omega
--       high_le_size := by omega
--     }
--     let x := arr[low]
--     let y := arr[low.succ]
--     let le := Ord.compare x y ≠ Ordering.gt
--     le ∧ Slice.sorted₂ s'

-- theorem Slice.sorted_of_sorted₂ : s.sorted₂ → s.sorted := by
--   sorry

-- theorem Slice.sorted₂_of_sorted : s.sorted → s.sorted₂ := by
--   sorry

-- theorem Slice.sorted_iff_sorted₂ : s.sorted ↔ s.sorted₂ := by
--   apply Iff.intro
--   . exact s.sorted₂_of_sorted
--   . exact s.sorted_of_sorted₂

-- A slice, s₁, is less than or equal to a slice s₂ if no element of s₁ is greater
-- than an element of s₂.
def Slice.le (_s₁ : Slice arr₁ low₁ high₁) (_s₂ : Slice arr₂ low₂ high₂) : Prop :=
  ∀ (i₁ : Fin arr₁.size) (i₂ : Fin arr₂.size),
      i₁.val.in_range low₁ high₁
    ∧ i₂.val.in_range low₂ high₂
    → Ord.compare arr₁[i₁] arr₂[i₂] ≠ Ordering.gt

structure H₁ (arr aux : Array α) (low mid high ptr₁ ptr₂ : ℕ) : Prop where
  slice₁ : SlicePtrInclusive arr low mid ptr₁
  slice₂ : SlicePtrInclusive arr mid high ptr₂
  size_eq : arr.size = aux.size
  slice₁_sorted : slice₁.sorted
  slice₂_sorted : slice₂.sorted

structure H₂ (arr aux : Array α) (low mid high ptr₁ ptr₂ i : ℕ)
    extends H₁ arr aux low mid high ptr₁ ptr₂ : Prop where
  slice_i : SlicePtrInclusive aux low high i
  i_def : i = ptr₁ + ptr₂ - mid
  slice_i_left_sorted : slice_i.left.sorted
  slice_i_left_le_right₁ : slice_i.left.le slice₁.right
  slice_i_left_le_right₂ : slice_i.left.le slice₂.right

structure H₃ (arr aux : Array α) (low mid high ptr₁ ptr₂ i : ℕ)
    extends H₂ arr aux low mid high ptr₁ ptr₂ i : Prop where
  slice₁_exclusive : SlicePtrExclusive arr low mid ptr₁
  slice₂_exclusive : SlicePtrExclusive arr mid high ptr₂
  slice_i_exclusive : SlicePtrExclusive aux low high i

def H₂.mkH₃
    (h₂ : H₂ arr aux low mid high ptr₁ ptr₂ i)
    (ptr₁_ptr₂_in_bounds : ptr₁ < mid ∧ ptr₂ < high)
    : H₃ arr aux low mid high ptr₁ ptr₂ i :=
  have slice_i_exclusive : SlicePtrExclusive aux low high i := by
    have i_lt_high : i < high := by
      have := h₂.i_def
      omega
    exact h₂.slice_i.mkExclusive i_lt_high
  { h₂ with
    slice₁_exclusive := h₂.slice₁.mkExclusive ptr₁_ptr₂_in_bounds.left,
    slice₂_exclusive := h₂.slice₂.mkExclusive ptr₁_ptr₂_in_bounds.right,
    slice_i_exclusive
  }

def H₃.i_lt_aux_size (h₃ : H₃ arr aux low mid high ptr₁ ptr₂ i) : i < aux.size :=
  have s := h₃.slice_i_exclusive
  Nat.le_trans s.ptr_lt_high s.high_le_size

def H₃.ptr₁_lt_arr_size (h₃ : H₃ arr aux low mid high ptr₁ ptr₂ i) : ptr₁ < arr.size :=
  have s := h₃.slice₁_exclusive
  Nat.le_trans s.ptr_lt_high s.high_le_size

def H₃.ptr₂_lt_arr_size (h₃ : H₃ arr aux low mid high ptr₁ ptr₂ i) : ptr₂ < arr.size :=
  have s := h₃.slice₂_exclusive
  Nat.le_trans s.ptr_lt_high s.high_le_size

-- -- If an array is modified, but the element changed is outside the slice on the
-- -- right, then none of the elements in the slice changed, thus it is still sorted.
-- def Slice.sorted_outside_write_sorted
--     {arr : Array α}
--     {low high : ℕ}
--     (s : Slice arr low high)
--     (s_sorted : s.sorted)
--     {arr' : Array α}
--     {i : Fin arr.size}
--     {a : α}
--     {i_ge_high : i ≥ high}
--     {arr'_def : arr' = arr.set i a}
--     : have s' : Slice arr' low high :=
--         { low_le_high := s.low_le_high,
--           high_le_size := by simp [arr'_def]; exact s.high_le_size
--         }
--       s'.sorted := by
--   intro s'
--   unfold Slice.sorted
--   intro i₁' i₂' adjacent_in_bounds'
--   unfold Slice.sorted at s_sorted
--   have i₁'_lt_arr_size : i₁' < arr.size := by omega
--   have i₂'_lt_arr_size : i₂' < arr.size := by omega
--   let i₁ : Fin arr.size := ⟨i₁', i₁'_lt_arr_size⟩
--   let i₂ : Fin arr.size := ⟨i₂', i₂'_lt_arr_size⟩
--   have i₁'_eq_i₁ : i₁'.val = i₁.val := by rfl
--   have i₂'_eq_i₂ : i₂'.val = i₂.val := by rfl
--   rw [i₁'_eq_i₁, i₂'_eq_i₂] at adjacent_in_bounds'
--   have h := s_sorted i₁ i₂ adjacent_in_bounds'
--   simp [arr'_def]
--   have i_ne_i₁' : i.val ≠ i₁' := by omega
--   have i_ne_i₂' : i.val ≠ i₂' := by omega
--   have set_get₁ := arr.get_set_ne i a i₁'_lt_arr_size i_ne_i₁'
--   have set_get₂ := arr.get_set_ne i a i₂'_lt_arr_size i_ne_i₂'
--   rw [set_get₁, set_get₂]
--   exact h

def Slice.le_elem (s : Slice arr low high) (a : α) : Prop :=
  ∀ (i : ℕ) (in_bounds : i ≥ low ∧ i < high),
    have high_le_size := s.high_le_size
    Ord.compare arr[i] a ≠ Ordering.gt

def Slice.ge_elem (s : Slice arr low high) (a : α) : Prop :=
  ∀ (i : ℕ) (in_bounds : i ≥ low ∧ i < high),
    have high_le_size := s.high_le_size
    Ord.compare a arr[i] ≠ Ordering.gt

def Slice.le_elem_of_le
    (s₁ : Slice arr₁ low₁ high₁)
    {s₂ : Slice arr₂ low₂ high₂}
    (s₁_le_s₂ : s₁.le s₂)
    (ptr_in_bounds₂ : ptr ≥ low₂ ∧ ptr < high₂)
    : have high_le_size := s₂.high_le_size
      s₁.le_elem arr₂[ptr] := by
  intro high_le_size
  unfold Slice.le_elem
  intro i in_bounds high_le_size
  unfold Slice.le at s₁_le_s₂
  have i_lt_arr₁_size : i < arr₁.size := by omega
  have ptr_lt_arr₂_size : ptr < arr₂.size := by omega
  have h : i.in_range low₁ high₁ ∧ ptr.in_range low₂ high₂ := by
    simp [Nat.in_range]
    omega
  exact s₁_le_s₂ ⟨i, i_lt_arr₁_size⟩ ⟨ptr, ptr_lt_arr₂_size⟩ h

theorem not_gt_of_compare_same {a : α} : compare a a ≠ Ordering.gt := by
  have compare_refl : compare a a = .eq := by exact OrientedCmp.cmp_refl
  intro compare_eq_gt
  have : Ordering.eq = Ordering.gt := by rw [← compare_refl, ← compare_eq_gt]
  contradiction

def Slice.ge_elem_low_of_sorted
    (s_sorted : s.sorted)
    (nonempty : low < high)
    : by have := s.high_le_size
         exact s.ge_elem arr[low]
    := by
  simp [Slice.ge_elem]
  intro i in_bounds
  simp [Slice.sorted] at s_sorted
  have := s.low_le_high
  have := s.high_le_size
  let rec loop (i : ℕ) (in_bounds : i ≥ low ∧ i < high)
      : compare arr[low] arr[i] ≠ Ordering.gt := by
    if i_eq_low : i = low then
      simp [i_eq_low]
      exact not_gt_of_compare_same
    else
      let j := i - 1
      have j_in_bounds : j ≥ low ∧ j < high := by omega
      have ih := loop j j_in_bounds
      let j_f : Fin arr.size := ⟨j, by omega⟩
      let i_f : Fin arr.size := ⟨i, by omega⟩
      have adj : j_f.val.adjacent_in_range i_f low high := by
        simp [Nat.adjacent_in_range]
        omega
      have h := s_sorted j_f i_f adj
      exact TransCmp.le_trans ih h
  exact loop i in_bounds

def Slice.ge_elem_low_succ_of_sorted
    (s_sorted : s.sorted)
    (nonempty : low < high)
    (s' : Slice arr low.succ high)
    : by have := s.high_le_size
         exact s'.ge_elem arr[low]
    := by
  have h := s.ge_elem_low_of_sorted s_sorted nonempty
  simp [Slice.ge_elem]
  intro i in_bounds
  simp [Slice.ge_elem] at h
  have i_in_bounds : low ≤ i ∧ i < high := by omega
  exact h i i_in_bounds

set_option pp.proofs true

def Slice.sorted_after_sorted_push
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
    have in_bounds : i₁'.val.in_range low high := by simp [Nat.in_range]; omega
    unfold Slice.le_elem at s_le_elem_a
    exact s_le_elem_a i₁' in_bounds
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

def SlicePtrInclusive.sorted_of_right_sorted
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

def Slice.le_of_swap_ends_le
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
  have slice₁ := h₃.slice₁_exclusive.next
  have size_eq : arr.size = aux'.size := by simp [aux']; exact h₃.size_eq
  have aux_size_eq : aux.size = aux'.size := by simp [aux']
  have slice_i : SlicePtrInclusive aux' low high i.succ :=
    h₃.slice_i_exclusive.next.swap_arr aux_size_eq
  have i_def : i.succ = ptr₁.succ + ptr₂ - mid := by
    have := h₃.i_def
    have := h₃.slice₂.ptr_ge_low
    omega
  have slice_i_left_sorted : slice_i.left.sorted :=
    have ptr₁_in_bounds : ptr₁ ≥ ptr₁ ∧ ptr₁ < mid := by
      simp [h₃.slice₁.ptr_ge_low, h₃.slice₁_exclusive.ptr_lt_high]
    have s_le_arr_ptr₁ : h₃.slice_i.left.le_elem arr[ptr₁] :=
      h₃.slice_i.left.le_elem_of_le h₃.slice_i_left_le_right₁ ptr₁_in_bounds
    h₃.slice_i.left.sorted_after_sorted_push
      h₃.slice_i_left_sorted
      h₃.i_lt_aux_size
      aux'_def
      slice_i.left
      s_le_arr_ptr₁
  have slice_i_left_le_right₁ : slice_i.left.le slice₁.right :=
    h₃.slice_i.left.le_of_swap_ends_le
      (h₃.slice₁.sorted_of_right_sorted h₃.slice₁_sorted)
      h₃.slice_i_left_le_right₁
      h₃.i_lt_aux_size
      h₃.ptr₁_lt_arr_size
      aux'_def
      slice_i.left
      slice₁.right
      h₃.size_eq
  have slice_i_left_le_right₂ : slice_i.left.le h₃.slice₂.right := sorry
  exact {
    h₃ with
    slice₁,
    size_eq,
    slice_i,
    i_def,
    slice_i_left_sorted,
    slice_i_left_le_right₁,
    slice_i_left_le_right₂,
  }
  -- have i_succ_def : i.succ = k₁.succ + k₂ - start₂ := by
  --   have := h₃.i_def
  --   have := h₃.k₂_ge_start₂
  --   omega
  -- have k₁_succ_lt_start₂_succ : k₁.succ < start₂.succ := by
  --   have := h₃.k₁_k₂_in_bounds
  --   omega
  -- have arr_size_eq_aux'_size : arr.size = aux'.size := by
  --   simp [aux']
  --   exact h₃.arr_size_eq_aux_size
  -- have aux'_sorted : aux'.sorted_slice start₁ i.succ := by
  --   have aux_sorted := h₃.aux_sorted
  --   have aux_le_left := h₃.aux_le_left
  --   rw [Array.sorted_slice]
  --   intro c₁ c₂ in_bounds
  --   if c₂_eq_i : c₂ = i then
  --     have c₁_eq_k₁ : c₁ = k₁ := by sorry
  --     subst c₂ c₁
  --     sorry
  --   else
  --     sorry
  --   -- if i₂_eq_i : c₁ = ⟨i, ⟩ then
  --   --   subst c₁
  --   --   intro in_bounds
  --   --   rw [Array.slice_has_no_greater_element] at aux_le_left
  --   --   exact aux_le_left ⟨i, sorry⟩ ⟨k₁, sorry⟩
  --   -- else

  --   --   sorry
  -- have aux'_le_left : aux'.Array.slice_le start₁ i.succ arr k₁.succ start₂ := by
  --   sorry
  -- have aux'_le_right : aux'.Array.slice_le start₁ i.succ arr k₂ end₂ := by
  --   sorry
  -- exact
  --   { h₃ with
  --     arr_size_eq_aux_size := arr_size_eq_aux'_size
  --     i_def := i_succ_def
  --     k₁_lt_start₂_succ := k₁_succ_lt_start₂_succ
  --     aux_sorted := aux'_sorted
  --     aux_le_left := aux'_le_left
  --     aux_le_right := aux'_le_right
  --   }

-- def H₃.nextRight
--     (h₃ : H₃ arr aux start₁ start₂ end₂ i k₁ k₂)
--     : have i_lt_aux_size := h₃.i_lt_aux_size
--       have k₂_lt_arr_size := h₃.k₂_lt_arr_size
--       have aux' := aux.set ⟨i, i_lt_aux_size⟩ arr[k₂]
--       H₂ arr aux' start₁ start₂ end₂ i.succ k₁ k₂.succ := by
--   intro i_lt_aux_size k₂_lt_arr_size aux'
--   have arr_size_eq_aux'_size : arr.size = aux'.size := by
--     simp [aux']
--     exact h₃.arr_size_eq_aux_size
--   have i_succ_def : i.succ = k₁ + k₂.succ - start₂ := by
--     have := h₃.i_def
--     have := h₃.k₂_ge_start₂
--     omega
--   have k₂_succ_lt_end₂_succ : k₂.succ < end₂.succ := by
--     have := h₃.k₁_k₂_in_bounds
--     omega
--   have k₂_succ_ge_start₂ : k₂.succ ≥ start₂ := by
--     have := h₃.k₂_ge_start₂
--     omega
--   exact
--     { h₃ with
--       arr_size_eq_aux_size := arr_size_eq_aux'_size
--       i_def := i_succ_def
--       k₂_lt_end₂_succ := k₂_succ_lt_end₂_succ
--       k₂_ge_start₂ := k₂_succ_ge_start₂
--     }

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

-- @[specialize, inline]
-- def mergeAdjacentChunksIntoAux
--     (h₁ : H₁ arr aux start₁ start₂ end₂)
--     : Array α :=
--   -- Copy the lowest element from the left and right regions until one of them is fully copied.
--   let rec @[specialize] loop
--       (aux : Array α)
--       (i k₁ k₂ : ℕ)
--       (h₂ : H₂ arr aux start₁ start₂ end₂ i k₁ k₂)
--       : Array α :=
--     if k₁_k₂_in_bounds : k₁ < start₂ ∧ k₂ < end₂ then
--       have h₃ := h₂.mkH₃ k₁_k₂_in_bounds
--       have k₁_lt_arr_size : k₁ < arr.size := h₃.k₁_lt_arr_size
--       have k₂_lt_arr_size : k₂ < arr.size := h₃.k₂_lt_arr_size
--       match Ord.compare arr[k₁] arr[k₂] with
--       | .lt | .eq =>
--         let aux' := aux.set ⟨i, h₃.i_lt_aux_size⟩ arr[k₁]
--         loop aux' i.succ k₁.succ k₂ h₃.nextLeft
--       | .gt =>
--         let aux' := aux.set ⟨i, h₃.i_lt_aux_size⟩ arr[k₂]
--         loop aux' i.succ k₁ k₂.succ h₃.nextRight
--     else
--       -- If the left region is not yet empty, finish copying it.
--       let rec @[specialize] loopLeft
--           (aux : Array α)
--           (i k₁ : ℕ)
--           (h₂ : H₂ arr aux start₁ start₂ end₂ i k₁ k₂)
--           : Array α :=
--         if k₁_lt_start₂ : k₁ < start₂ then
--           have : k₁ < arr.size := h₂.mk_k₁_lt_arr_size k₁_lt_start₂
--           have i_lt_aux_size : i < aux.size := h₂.mk_i_lt_aux_size k₁_lt_start₂
--           let aux' := aux.set ⟨i, i_lt_aux_size⟩ arr[k₁]
--           loopLeft aux' i.succ k₁.succ (h₂.nextLeft k₁_lt_start₂)
--         else
--           -- If the right region is not yet empty, finish copying it.
--           let rec @[specialize] loopRight
--               (aux : Array α)
--               (i k₂ : ℕ)
--               (h₄Right : H₄Right arr aux start₁ start₂ end₂ i k₁ k₂)
--               : Array α :=
--             if k₂_lt_end₂ : k₂ < end₂ then
--               have : k₂ < arr.size := h₄Right.mk_k₂_lt_arr_size k₂_lt_end₂
--               have i_lt_aux_size : i < aux.size := h₄Right.mk_i_lt_aux_size k₂_lt_end₂
--               let aux' := aux.set ⟨i, i_lt_aux_size⟩ arr[k₂]
--               loopRight aux' i.succ k₂.succ (h₄Right.next k₂_lt_end₂)
--             else
--               aux
--           -- These termination proofs can be automatically inferred, but stating
--           -- them explicitly makes this function compile a lot faster.
--           termination_by end₂ - k₂
--           decreasing_by exact mergeAdjacentChunksIntoAux.loop.loopLeft.loopRight_decreasing end₂ k₂ k₂_lt_end₂
--           loopRight aux i k₂ (h₂.mkH₄Right k₁_lt_start₂)
--       termination_by start₂ - k₁
--       decreasing_by exact mergeAdjacentChunksIntoAux.loop.loopLeft_decreasing start₂ k₁ k₁_lt_start₂
--       loopLeft aux i k₁ h₂
--   termination_by arr.size - i
--   decreasing_by
--     all_goals
--       have i_lt_arr_size : i < arr.size := by
--         rw [h₂.arr_size_eq_aux_size]
--         exact (h₂.mkH₃ k₁_k₂_in_bounds).i_lt_aux_size
--       exact (Nat.sub_succ_lt_sub_of_lt i_lt_arr_size)
--   let h₂ :=
--     { h₁ with
--       i_def := Nat.eq_sub_of_add_eq rfl
--       k₂_ge_start₂ := Nat.le_refl start₂
--       k₁_lt_start₂_succ := Nat.lt_succ_of_lt h₁.start₁_lt_start₂
--       k₂_lt_end₂_succ := Nat.lt_succ_of_lt h₁.start₂_lt_end₂
--     }
--   loop aux start₁ start₁ start₂ h₂

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
--   if k₁_k₂_in_bounds : k₁ < start₂ ∧ k₂ < end₂ then
--     simp [k₁_k₂_in_bounds]
--     split <;> rw [← mergeAdjacentChunksIntoAux.loop_size_eq]
--   else
--     simp [k₁_k₂_in_bounds, ← mergeAdjacentChunksIntoAux.loop.loopLeft_size_eq]
-- termination_by aux.size - i
-- decreasing_by
--   all_goals
--     simp_wf
--     have h₃ := h₂.mkH₃ k₁_k₂_in_bounds
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

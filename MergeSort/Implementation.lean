import Init.Data.Array.Basic
import Init.Data.UInt.Lemmas
import Lean.Elab.Tactic
import MergeSort.USize.Extras

variable
  {α : Type}
  {arr aux : Array α}
  {low mid high ptr₁ ptr₂ i chunkSize : USize}

structure H₁ (arr aux : Array α) (low mid high : USize) : Prop where
  arr_size_lt_usize_size : arr.size < USize.size
  low_le_mid : low ≤ mid
  mid_le_size : mid ≤ arr.usize
  mid_le_high : mid ≤ high
  high_le_size : high ≤ arr.usize
  size_eq : arr.size = aux.size

structure H₂ (arr aux : Array α) (low mid high ptr₁ ptr₂ i : USize) : Prop
    extends H₁ arr aux low mid high where
  ptr₁_ge_low : ptr₁ ≥ low
  ptr₁_le_mid : ptr₁ ≤ mid
  ptr₂_ge_mid : ptr₂ ≥ mid
  ptr₂_le_high : ptr₂ ≤ high
  i_ge_low : i ≥ low
  i_le_high : i ≤ high
  i_def : i = ptr₁ + ptr₂ - mid

def H₁.make_H₂'
    (high : Subtype (H₁ arr aux low mid))
    (ptr₁_def : ptr₁ = low)
    (ptr₂_def : ptr₂ = mid)
    (i_def : i = ptr₁)
    : Subtype (H₂ arr aux low mid high ptr₁ ptr₂) :=
  have i_eq_low := ptr₁_def ▸ i_def
  Subtype.mk i {
    high.property with
    ptr₁_ge_low := USize.ge_of_eq ptr₁_def
    ptr₁_le_mid := USize.le_trans (USize.le_of_eq ptr₁_def) high.property.low_le_mid
    ptr₂_ge_mid := USize.ge_of_eq ptr₂_def
    ptr₂_le_high := USize.le_trans (USize.le_of_eq ptr₂_def) high.property.mid_le_high
    i_ge_low := USize.ge_of_eq i_eq_low
    i_le_high := USize.le_trans (USize.le_of_eq i_eq_low) (USize.le_trans high.property.low_le_mid high.property.mid_le_high)
    i_def := by simp only [ptr₁_def, ptr₂_def, USize.add_sub_cancel, i_eq_low]
  }

def H₁.make_H₂
    (h₁ : H₁ arr aux low mid high)
    (ptr₁_def : ptr₁ = low)
    (ptr₂_def : ptr₂ = mid)
    (i_def : i = ptr₁)
    : H₂ arr aux low mid high ptr₁ ptr₂ i :=
  have i_eq_low := ptr₁_def ▸ i_def
  {
    h₁ with
    ptr₁_ge_low := USize.ge_of_eq ptr₁_def
    ptr₁_le_mid := USize.le_trans (USize.le_of_eq ptr₁_def) h₁.low_le_mid
    ptr₂_ge_mid := USize.ge_of_eq ptr₂_def
    ptr₂_le_high := USize.le_trans (USize.le_of_eq ptr₂_def) h₁.mid_le_high
    i_ge_low := USize.ge_of_eq i_eq_low
    i_le_high := USize.le_trans (USize.le_of_eq i_eq_low) (USize.le_trans h₁.low_le_mid h₁.mid_le_high)
    i_def := by simp only [ptr₁_def, ptr₂_def, USize.add_sub_cancel, i_eq_low]
  }

structure H₃ (arr aux : Array α) (low mid high ptr₁ ptr₂ i : USize) : Prop
    extends H₂ arr aux low mid high ptr₁ ptr₂ i where
  ptr₁_lt_mid : ptr₁ < mid
  ptr₂_lt_high : ptr₂ < high
  i_lt_high : i < high

def H₂.make_H₃
    (h₂ : H₂ arr aux low mid high ptr₁ ptr₂ i)
    (ptr₁_ptr₂_in_range : ptr₁ < mid ∧ ptr₂ < high)
    : H₃ arr aux low mid high ptr₁ ptr₂ i :=
  { h₂ with
    ptr₁_lt_mid := ptr₁_ptr₂_in_range.left
    ptr₂_lt_high := ptr₁_ptr₂_in_range.right
    i_lt_high := by
      rw [h₂.i_def]
      exact USize.sub_add_lt_of_and_lt_lt h₂.ptr₂_ge_mid ptr₁_ptr₂_in_range
  }

def H₃.ptr₁_lt_arr_size
    (h₃ : H₃ arr aux low mid high ptr₁ ptr₂ i)
    : ptr₁.toNat < arr.size :=
  USize.ptr₁_lt_arr_size h₃.i_lt_high h₃.ptr₁_le_mid h₃.ptr₂_ge_mid h₃.i_def
    h₃.arr_size_lt_usize_size h₃.high_le_size

def H₃.ptr₂_lt_arr_size
    (h₃ : H₃ arr aux low mid high ptr₁ ptr₂ i)
    : ptr₂.toNat < arr.size :=
  USize.ptr₂_lt_arr_size h₃.arr_size_lt_usize_size h₃.high_le_size h₃.ptr₂_lt_high

def H₃.i_lt_aux_size
    (h₃ : H₃ arr aux low mid high ptr₁ ptr₂ i)
    : i.toNat < aux.size :=
  USize.i_lt_aux_size h₃.arr_size_lt_usize_size h₃.high_le_size h₃.size_eq h₃.i_lt_high

def H₃.next₁
    (h₃ : H₃ arr aux low mid high ptr₁ ptr₂ i)
    : have ptr₁_lt_arr_size := h₃.ptr₁_lt_arr_size
      let aux' := aux.uset i arr[ptr₁] h₃.i_lt_aux_size
      H₂ arr aux' low mid high ptr₁.succ ptr₂ i.succ :=
  { h₃ with
    size_eq := by
      simp only [Array.uset, Array.ugetElem_eq_getElem, Array.size_set]
      exact h₃.size_eq
    ptr₁_ge_low := USize.add_one_ge_of_lt_of_ge h₃.ptr₁_ge_low h₃.ptr₁_lt_mid
    ptr₁_le_mid := USize.add_one_le_of_lt h₃.ptr₁_lt_mid
    i_ge_low := USize.add_one_ge_of_lt_of_ge h₃.i_ge_low h₃.i_lt_high
    i_le_high := USize.add_one_le_of_lt h₃.i_lt_high
    i_def := USize.succ_eq_succ_add_sub_of_add_sub h₃.i_def
  }

def H₃.next₂
    (h₃ : H₃ arr aux low mid high ptr₁ ptr₂ i)
    : have ptr₂_lt_arr_size := h₃.ptr₂_lt_arr_size
      let aux' := aux.uset i arr[ptr₂] h₃.i_lt_aux_size
      H₂ arr aux' low mid high ptr₁ ptr₂.succ i.succ :=
  { h₃ with
    size_eq := by
      simp only [Array.uset, Array.ugetElem_eq_getElem, Array.size_set]
      exact h₃.size_eq
    ptr₂_ge_mid := USize.add_one_ge_of_lt_of_ge h₃.ptr₂_ge_mid h₃.ptr₂_lt_high
    ptr₂_le_high := USize.add_one_le_of_lt h₃.ptr₂_lt_high
    i_ge_low := USize.add_one_ge_of_lt_of_ge h₃.i_ge_low h₃.i_lt_high
    i_le_high := USize.add_one_le_of_lt h₃.i_lt_high
    i_def := USize.succ_eq_add_succ_sub_of_add_sub h₃.i_def
  }

structure H₄ (arr aux : Array α) (low mid high ptr₁ ptr₂ i : USize) : Prop
    extends H₂ arr aux low mid high ptr₁ ptr₂ i where
  not_ptr₁_ptr₂_in_range : ptr₁ = mid ∨ ptr₂ = high

def H₂.make_H₄
    (h₂ : H₂ arr aux low mid high ptr₁ ptr₂ i)
    (not_ptr₁_ptr₂_in_range : ¬(ptr₁ < mid ∧ ptr₂ < high))
    : H₄ arr aux low mid high ptr₁ ptr₂ i :=
  { h₂ with
    not_ptr₁_ptr₂_in_range := USize.ptr₁_eq_mid_or_ptr₂_eq_high h₂.ptr₁_le_mid
      h₂.ptr₂_le_high not_ptr₁_ptr₂_in_range
  }

structure H₅ (arr aux : Array α) (low mid high ptr₁ ptr₂ i : USize) : Prop
    extends H₄ arr aux low mid high ptr₁ ptr₂ i where
  ptr₁_lt_mid : ptr₁ < mid

def H₄.make_H₅
    (h₄ : H₄ arr aux low mid high ptr₁ ptr₂ i)
    (ptr₁_lt_mid : ptr₁ < mid)
    : H₅ arr aux low mid high ptr₁ ptr₂ i :=
  { h₄ with ptr₁_lt_mid }

def H₅.ptr₁_lt_arr_size
    (h₅ : H₅ arr aux low mid high ptr₁ ptr₂ i)
    : ptr₁.toNat < arr.size := by
  have ptr₁_lt_size : ptr₁ < arr.usize :=
    USize.lt_of_lt_of_le h₅.ptr₁_lt_mid h₅.mid_le_size
  exact (USize.lt_ofNat_iff h₅.arr_size_lt_usize_size).mp ptr₁_lt_size

def H₅.i_lt_aux_size
    (h₅ : H₅ arr aux low mid high ptr₁ ptr₂ i)
    : i.toNat < aux.size := by
  have i_lt_size : i < arr.usize :=
    USize.i_lt_arr_usize h₅.high_le_size h₅.i_le_high h₅.i_def
      h₅.not_ptr₁_ptr₂_in_range h₅.ptr₁_lt_mid
  rw [← h₅.size_eq]
  exact (USize.lt_ofNat_iff h₅.arr_size_lt_usize_size).mp i_lt_size

def H₅.next
    (h₅ : H₅ arr aux low mid high ptr₁ ptr₂ i)
    : have ptr₁_lt_arr_size := h₅.ptr₁_lt_arr_size
      let aux' := aux.uset i arr[ptr₁] h₅.i_lt_aux_size
      H₄ arr aux' low mid high ptr₁.succ ptr₂ i.succ :=
  { h₅ with
    size_eq := by
      simp only [Array.uset, Array.ugetElem_eq_getElem, Array.size_set]
      exact h₅.size_eq
    ptr₁_ge_low := USize.add_one_ge_of_lt_of_ge h₅.ptr₁_ge_low h₅.ptr₁_lt_mid
    ptr₁_le_mid := USize.add_one_le_of_lt h₅.ptr₁_lt_mid
    i_ge_low := USize.i_succ_ge_low h₅.i_ge_low h₅.i_le_high h₅.i_def
      h₅.not_ptr₁_ptr₂_in_range h₅.ptr₁_lt_mid
    i_le_high := USize.i_succ_le_high h₅.i_le_high h₅.i_def h₅.not_ptr₁_ptr₂_in_range
      h₅.ptr₁_lt_mid
    i_def := USize.succ_eq_succ_add_sub_of_add_sub h₅.i_def
    not_ptr₁_ptr₂_in_range := USize.not_ptr₁_succ_ptr₂_in_range h₅.not_ptr₁_ptr₂_in_range
      h₅.ptr₁_lt_mid
  }

structure H₆ (arr aux : Array α) (low mid high ptr₁ ptr₂ i : USize) : Prop
    extends H₄ arr aux low mid high ptr₁ ptr₂ i where
  ptr₁_eq_mid : ptr₁ = mid

def H₄.make_H₆
    (h₄ : H₄ arr aux low mid high ptr₁ ptr₂ i)
    (not_ptr₁_lt_mid : ¬ptr₁ < mid)
    : H₆ arr aux low mid high ptr₁ ptr₂ i :=
  { h₄ with
    ptr₁_eq_mid := by
      cases System.Platform.numBits_eq
      . bv_decide
      . bv_decide
  }

structure H₇ (arr aux : Array α) (low mid high ptr₁ ptr₂ i : USize) : Prop
    extends H₆ arr aux low mid high ptr₁ ptr₂ i where
  ptr₂_lt_high : ptr₂ < high

def H₆.make_H₇
    (h₆ : H₆ arr aux low mid high ptr₁ ptr₂ i)
    (ptr₂_lt_high : ptr₂ < high)
    : H₇ arr aux low mid high ptr₁ ptr₂ i :=
  { h₆ with ptr₂_lt_high }

def H₇.ptr₂_lt_arr_size
    (h₇ : H₇ arr aux low mid high ptr₁ ptr₂ i)
    : ptr₂.toNat < arr.size := by
  have ptr₂_lt_size : ptr₂ < arr.usize := by
    cases System.Platform.numBits_eq
    . bv_decide
    . bv_decide
  exact (USize.lt_ofNat_iff h₇.arr_size_lt_usize_size).mp ptr₂_lt_size

def H₇.i_lt_aux_size
    (h₇ : H₇ arr aux low mid high ptr₁ ptr₂ i)
    : i.toNat < aux.size := by
  have i_lt_size : i < arr.usize := by
    cases System.Platform.numBits_eq
    . bv_decide
    . bv_decide
  rw [← h₇.size_eq]
  exact (USize.lt_ofNat_iff h₇.arr_size_lt_usize_size).mp i_lt_size

def ptr₂_add_one_ge_mid
    (ptr₂_ge_mid : ptr₂ ≥ mid)
    (ptr₂_lt_high : ptr₂ < high)
    : ptr₂ + 1 ≥ mid := by
  exact USize.add_one_ge_of_lt_of_ge ptr₂_ge_mid ptr₂_lt_high

def ptr₂_add_one_le_high
    (ptr₂_lt_high : ptr₂ < high)
    : ptr₂ + 1 ≤ high := by
  exact USize.add_one_le_of_lt ptr₂_lt_high

def i_add_one_ge_low
    (i_ge_low : i ≥ low)
    (i_def : i = ptr₁ + ptr₂ - mid)
    (ptr₁_eq_mid : ptr₁ = mid)
    (ptr₂_lt_high : ptr₂ < high)
    : i + 1 ≥ low := by
  rw [ptr₁_eq_mid] at i_def
  rw [i_def]
  rw [i_def] at i_ge_low
  exact USize.add_one_sub_add_ge_of_mid_lt_of_ge i_ge_low ptr₂_lt_high

def i_add_one_le_high
    (i_def : i = ptr₁ + ptr₂ - mid)
    (ptr₁_eq_mid : ptr₁ = mid)
    (ptr₂_lt_high : ptr₂ < high)
    : i + 1 ≤ high := by
  rw [i_def, ptr₁_eq_mid]
  exact USize.add_sub_add_one_le_of_lt ptr₂_lt_high

def i_add_one_def₂
    (i_def : i = ptr₁ + ptr₂ - mid)
    : i + 1 = ptr₁ + (ptr₂ + 1) - mid := by
  rw [i_def]
  exact USize.add_one_sub_right_comm

def not_ptr₁_ptr₂_in_range₂
    (ptr₁_eq_mid : ptr₁ = mid)
    : ptr₁ = mid ∨ ptr₂.succ = high := by
  apply Or.intro_left
  exact ptr₁_eq_mid

def H₇.next
    (h₇ : H₇ arr aux low mid high ptr₁ ptr₂ i)
    : have ptr₂_lt_arr_size := h₇.ptr₂_lt_arr_size
      let aux' := aux.uset i arr[ptr₂] h₇.i_lt_aux_size
      H₆ arr aux' low mid high ptr₁ ptr₂.succ i.succ :=
  { h₇ with
    size_eq := by
      simp only [Array.uset, Array.ugetElem_eq_getElem, Array.size_set]
      exact h₇.size_eq
    ptr₂_ge_mid := ptr₂_add_one_ge_mid h₇.ptr₂_ge_mid h₇.ptr₂_lt_high
    ptr₂_le_high := ptr₂_add_one_le_high h₇.ptr₂_lt_high
    i_ge_low := i_add_one_ge_low h₇.i_ge_low h₇.i_def h₇.ptr₁_eq_mid h₇.ptr₂_lt_high
    i_le_high := i_add_one_le_high h₇.i_def h₇.ptr₁_eq_mid h₇.ptr₂_lt_high
    i_def := i_add_one_def₂ h₇.i_def
    not_ptr₁_ptr₂_in_range := not_ptr₁_ptr₂_in_range₂ h₇.ptr₁_eq_mid
  }

def H₃.decreasing
    (h₃ : H₃ arr aux low mid high ptr₁ ptr₂ i)
    : arr.size - i.succ.toNat < arr.size - i.toNat := by
  rw [h₃.size_eq]
  refine Nat.sub_lt_sub_left h₃.i_lt_aux_size ?_
  refine USize.lt_iff_toNat_lt.mp ?_
  . cases System.Platform.numBits_eq
    . bv_decide
    . bv_decide

def H₅.decreasing
    (h₅ : H₅ arr aux low mid high ptr₁ ptr₂ i)
    : arr.size - i.succ.toNat < arr.size - i.toNat := by
  rw [h₅.size_eq]
  refine Nat.sub_lt_sub_left h₅.i_lt_aux_size ?_
  refine USize.lt_iff_toNat_lt.mp ?_
  . cases System.Platform.numBits_eq
    . bv_decide
    . bv_decide

def H₇.decreasing
    (h₇ : H₇ arr aux low mid high ptr₁ ptr₂ i)
    : arr.size - i.succ.toNat < arr.size - i.toNat := by
  rw [h₇.size_eq]
  refine Nat.sub_lt_sub_left h₇.i_lt_aux_size ?_
  refine USize.lt_iff_toNat_lt.mp ?_
  . cases System.Platform.numBits_eq
    . bv_decide
    . bv_decide

@[specialize, inline]
def mergeAdjacentChunksIntoAux
    [Ord α]
    (arr : Array α)
    (low mid high : USize)
    (aux : Subtype (H₁ arr · low mid high))
    : Array α :=
  let rec @[specialize] loop
      (ptr₁ ptr₂ i : USize)
      (aux : Subtype (H₂ arr · low mid high ptr₁ ptr₂ i))
      : Array α :=
    if ptr₁_ptr₂_in_range : ptr₁ < mid ∧ ptr₂ < high then
      have h₃ := aux.property.make_H₃ ptr₁_ptr₂_in_range
      have := h₃.ptr₁_lt_arr_size
      have := h₃.ptr₂_lt_arr_size
      match Ord.compare arr[ptr₁] arr[ptr₂] with
      | .lt | .eq =>
        let aux' := aux.val.uset i arr[ptr₁] h₃.i_lt_aux_size
        loop ptr₁.succ ptr₂ i.succ ⟨aux', h₃.next₁⟩
      | .gt =>
        let aux' := aux.val.uset i arr[ptr₂] h₃.i_lt_aux_size
        loop ptr₁ ptr₂.succ i.succ ⟨aux', h₃.next₂⟩
    else
      let rec @[specialize] loopLeft
          (ptr₁ i : USize)
          (aux : Subtype (H₄ arr · low mid high ptr₁ ptr₂ i))
          : Array α :=
        if ptr₁_lt_mid : ptr₁ < mid then
          have h₅ := aux.property.make_H₅ ptr₁_lt_mid
          have := h₅.ptr₁_lt_arr_size
          let aux' := aux.val.uset i arr[ptr₁] h₅.i_lt_aux_size
          loopLeft ptr₁.succ i.succ ⟨aux', h₅.next⟩
        else
          let rec @[specialize] loopRight
              (ptr₂ i : USize)
              (aux : Subtype (H₆ arr · low mid high ptr₁ ptr₂ i))
              : Array α :=
            if ptr₂_lt_high : ptr₂ < high then
              have h₇ := aux.property.make_H₇ ptr₂_lt_high
              have := h₇.ptr₂_lt_arr_size
              let aux' := aux.val.uset i arr[ptr₂] h₇.i_lt_aux_size
              loopRight ptr₂.succ i.succ ⟨aux', h₇.next⟩
            else
              aux
          termination_by arr.size - i.toNat
          decreasing_by all_goals exact h₇.decreasing
          loopRight ptr₂ i ⟨aux, aux.property.make_H₆ ptr₁_lt_mid⟩
      termination_by arr.size - i.toNat
      decreasing_by all_goals exact h₅.decreasing
      loopLeft ptr₁ i ⟨aux, aux.property.make_H₄ ptr₁_ptr₂_in_range⟩
  termination_by arr.size - i.toNat
  decreasing_by all_goals exact h₃.decreasing
  loop (ptr₁ := low) (ptr₂ := mid) (i := low) ⟨aux, aux.property.make_H₂ rfl rfl rfl⟩

structure H₈ (arr aux : Array α) (low chunkSize : USize) : Prop where
  arr_size_lt_usize_size : arr.size < USize.size
  size_eq : arr.size = aux.size
  low_le_arr_usize : low ≤ arr.usize
  chunkSize_gt_zero : chunkSize > 0
  chunkSize_lt_arr_usize : chunkSize < arr.usize

structure H₉ (arr aux : Array α) (low chunkSize : USize) : Prop
    extends H₈ arr aux low chunkSize where
  size_minus_low_gt_chunkSize : arr.usize - low > chunkSize

def H₈.make_H₉
    (h₈ : H₈ arr aux low chunkSize)
    (size_minus_low_gt_chunkSize : arr.usize - low > chunkSize)
    : H₉ arr aux low chunkSize :=
  { h₈ with size_minus_low_gt_chunkSize }

theorem Fin.add_val_eq_val_add_of_nonoverflowing
    {n : Nat}
    {a b : Fin n}
    (h : a.val + b.val < n)
    : (a + b).val = a.val + b.val :=
  Nat.mod_eq_of_lt h

theorem Fin.self_le_add_of_nonoverflowing
    {n}
    {a b : Fin n}
    (h : a.val + b.val < n)
    : a ≤ a + b := by
  suffices hp : a.val ≤ (a + b).val by exact hp
  simp only [Fin.add_val_eq_val_add_of_nonoverflowing h, Nat.le_add_right]

theorem USize.self_le_add_of_nonoverflowing
    {a b : USize}
    (h : a.toNat + b.toNat < USize.size)
    : a ≤ a + b := by
  suffices hp : a.toFin ≤ a.toFin + b.toFin by exact hp
  exact Fin.self_le_add_of_nonoverflowing h

theorem USize.le_add_of_sub_gt
    {a b c : USize}
    (h : b ≤ a)
    : a - b > c → b ≤ b + c := by
  cases System.Platform.numBits_eq
  . bv_decide
  . bv_decide

theorem USize.add_lt_of_sub
    {a b c : USize}
    (h : b ≤ a)
    : a - b > c → b + c < a := by
  cases System.Platform.numBits_eq
  . bv_decide
  . bv_decide

theorem USize.mid_le_high
    {mid size chunkSize : USize}
    (mid_le_size : mid ≤ size)
    (chunkSize_gt_zero : chunkSize > 0)
    : mid ≤ mid + min (size - mid) chunkSize := by
  if h : size - mid ≤ chunkSize then
    simp only [instMinUSize, minOfLe, min, h, ↓reduceIte]
    cases System.Platform.numBits_eq
    . bv_decide
    . bv_decide
  else
    simp only [instMinUSize, minOfLe, min, h, ↓reduceIte]
    cases System.Platform.numBits_eq
    . bv_decide
    . bv_decide

theorem USize.high_le_size
    {mid size chunkSize : USize}
    (mid_le_size : mid ≤ size)
    (chunkSize_gt_zero : chunkSize > 0)
    : mid + min (size - mid) chunkSize ≤ size := by
  if h : size - mid ≤ chunkSize then
    simp only [instMinUSize, minOfLe, min, h, ↓reduceIte]
    cases System.Platform.numBits_eq
    . bv_decide
    . bv_decide
  else
    simp only [instMinUSize, minOfLe, min, h, ↓reduceIte]
    cases System.Platform.numBits_eq
    . bv_decide
    . bv_decide

def H₉.mid_le_size
    (h₉ : H₉ arr aux low chunkSize)
    (mid_def : mid = low + chunkSize)
    : mid ≤ arr.usize := by
  rw [mid_def]
  refine USize.le_of_lt ?_
  exact USize.add_lt_of_sub h₉.low_le_arr_usize h₉.size_minus_low_gt_chunkSize

def H₉.make_H₁
    (h₉ : H₉ arr aux low chunkSize)
    : let mid := low + chunkSize
      let high := mid + min (arr.usize - mid) chunkSize
      H₁ arr aux low mid high := by
  intro mid high
  have mid_le_size := h₉.mid_le_size rfl
  exact {
    arr_size_lt_usize_size := h₉.arr_size_lt_usize_size
    low_le_mid := USize.le_add_of_sub_gt h₉.low_le_arr_usize h₉.size_minus_low_gt_chunkSize
    mid_le_size
    mid_le_high := USize.mid_le_high mid_le_size h₉.chunkSize_gt_zero
    high_le_size := USize.high_le_size mid_le_size h₉.chunkSize_gt_zero
    size_eq := h₉.size_eq
  }

theorem mergeAdjacentChunksIntoAux.loop.loopLeft.loopRight.size_eq
    [Ord α]
    {ptr₂ i : USize}
    {aux : Subtype (H₆ arr · low mid high ptr₁ ptr₂ i)}
    : aux.val.size = (loopRight arr low mid high ptr₁ ptr₂ i aux).size := by
  unfold loopRight
  if ptr₂_lt_high : ptr₂ < high then
    simp [ptr₂_lt_high, ← size_eq (i := i.succ)]
  else
    simp [ptr₂_lt_high]
termination_by arr.size - i.toNat
decreasing_by exact aux.property.make_H₇ ptr₂_lt_high |>.decreasing

theorem mergeAdjacentChunksIntoAux.loop.loopLeft.size_eq
    [Ord α]
    {ptr₁ i : USize}
    {aux : Subtype (H₄ arr · low mid high ptr₁ ptr₂ i)}
    : aux.val.size = (loopLeft arr low mid high ptr₂ ptr₁ i aux).size := by
  unfold loopLeft
  if ptr₁_lt_mid : ptr₁ < mid then
    simp [ptr₁_lt_mid, Array.uset, Array.ugetElem_eq_getElem, ← size_eq (i := i.succ)]
  else
    simp [ptr₁_lt_mid, ← loopRight.size_eq]
termination_by arr.size - i.toNat
decreasing_by exact aux.property.make_H₅ ptr₁_lt_mid |>.decreasing

theorem mergeAdjacentChunksIntoAux.loop.size_eq
    [Ord α]
    {ptr₁ ptr₂ i : USize}
    {aux : Subtype (H₂ arr · low mid high ptr₁ ptr₂ i)}
    : aux.val.size = (loop arr low mid high ptr₁ ptr₂ i aux).size := by
  unfold loop
  if ptr₁_ptr₂_in_range : ptr₁ < mid ∧ ptr₂ < high then
    simp only [ptr₁_ptr₂_in_range, and_self, ↓reduceDIte, Array.ugetElem_eq_getElem, Array.uset]
    split <;> rw [← size_eq, Array.size_set]
  else
    simp only [ptr₁_ptr₂_in_range, ↓reduceDIte, ← loopLeft.size_eq]
termination_by arr.size - i.toNat
decreasing_by all_goals exact aux.property.make_H₃ ptr₁_ptr₂_in_range |>.decreasing

theorem mergeAdjacentChunksIntoAux.size_eq
    [Ord α]
    (aux : Subtype (H₁ arr · low mid high))
    : aux.val.size = (mergeAdjacentChunksIntoAux arr low mid high aux).size :=
  mergeAdjacentChunksIntoAux.loop.size_eq (α := α) (aux := ⟨aux, aux.property.make_H₂ rfl rfl rfl⟩)

def H₉.next
    [Ord α]
    (h₉ : H₉ arr aux low chunkSize)
    : let mid := low + chunkSize
      let high := mid + min (arr.usize - mid) chunkSize
      have aux' := mergeAdjacentChunksIntoAux arr low mid high ⟨aux, h₉.make_H₁⟩
      H₈ arr aux' high chunkSize := by
  intro mid high aux'
  have mid_def : mid = low + chunkSize := rfl
  have high_def : high = mid + min (arr.usize - mid) chunkSize := rfl
  have mid_le_size : mid ≤ arr.usize := by
    rw [mid_def]
    refine USize.le_of_lt ?_
    exact USize.add_lt_of_sub h₉.low_le_arr_usize h₉.size_minus_low_gt_chunkSize
  exact {
    h₉ with
    size_eq := by
      simp only [h₉.size_eq, aux']
      exact mergeAdjacentChunksIntoAux.size_eq ⟨aux, h₉.make_H₁⟩
    low_le_arr_usize := by
      rw [high_def]
      exact USize.high_le_size mid_le_size h₉.chunkSize_gt_zero
  }

structure H₁₀ (arr aux : Array α) (low chunkSize : USize) : Prop
    extends H₈ arr aux low chunkSize where
  -- not_size_minus_low_gt_chunkSize : ¬arr.usize - low > chunkSize

def H₈.make_H₁₀
    (h₈ : H₈ arr aux low chunkSize)
    (_not_size_minus_low_gt_chunkSize : ¬arr.usize - low > chunkSize)
    : H₁₀ arr aux low chunkSize :=
  { h₈ with /-not_size_minus_low_gt_chunkSize-/ }

structure H₁₁ (arr aux : Array α) (low chunkSize : USize) : Prop
    extends H₁₀ arr aux low chunkSize where
  low_lt_aux_usize : low < aux.usize

def H₁₀.make_H₁₁
    (h₁₀ : H₁₀ arr aux low chunkSize)
    (low_lt_aux_usize : low < aux.usize)
    : H₁₁ arr aux low chunkSize :=
  { h₁₀ with low_lt_aux_usize }

def H₁₁.low_lt_arr_size
    (h₁₁ : H₁₁ arr aux low chunkSize)
    : low.toNat < arr.size := by
  rw [h₁₁.size_eq]
  have aux_size_lt_usize_size : aux.size < USize.size := by
    rw [← h₁₁.size_eq]
    exact h₁₁.arr_size_lt_usize_size
  refine (USize.lt_ofNat_iff aux_size_lt_usize_size).mp h₁₁.low_lt_aux_usize

def H₁₁.low_toNat_lt_aux_size
    (h₁₁ : H₁₁ arr aux low chunkSize)
    : low.toNat < aux.size := by
  rw [← h₁₁.size_eq]
  exact h₁₁.low_lt_arr_size

def H₁₁.next
    (h₁₁ : H₁₁ arr aux low chunkSize)
    : have := h₁₁.low_lt_arr_size
      let aux' := aux.uset low arr[low] h₁₁.low_toNat_lt_aux_size
      H₁₀ arr aux' low.succ chunkSize := by
  intro low_lt_arr_size aux'
  have aux'_def : aux' = aux.uset low arr[low] h₁₁.low_toNat_lt_aux_size := rfl
  exact {
    h₁₁ with
    size_eq := by
      simp only [h₁₁.size_eq, aux'_def, Array.uset, Array.ugetElem_eq_getElem, Array.size_set]
    low_le_arr_usize := by
      have usize_eq : arr.usize = aux.usize := by
        simp only [Array.usize, h₁₁.size_eq, Nat.toUSize_eq]
      suffices hp : low.succ ≤ aux.usize by
        rw [usize_eq]
        exact hp
      have := h₁₁.low_lt_aux_usize
      cases System.Platform.numBits_eq
      . bv_decide
      . bv_decide
  }

theorem USize.lt_of_sub_gt_zero_of_le {m n : USize} (h : n ≤ m) : m - n > 0 → n < m := by
  cases System.Platform.numBits_eq
  . bv_decide
  . bv_decide

def H₉.decreasing
    [Ord α]
    (h₉ : H₉ arr aux low chunkSize)
    : let mid := low + chunkSize
      let high := mid + min (arr.usize - mid) chunkSize
      arr.size - high.toNat < arr.size - low.toNat := by
  intro mid high
  have mid_def : mid = low + chunkSize := rfl
  refine Nat.sub_lt_sub_left ?_ ?_
  . have arr_usize_minus_low_gt_zero : arr.usize - low > 0 :=
      USize.lt_trans h₉.chunkSize_gt_zero h₉.size_minus_low_gt_chunkSize
    have low_lt_arr_usize : low < arr.usize :=
      USize.lt_of_sub_gt_zero_of_le h₉.low_le_arr_usize arr_usize_minus_low_gt_zero
    exact (USize.lt_ofNat_iff h₉.arr_size_lt_usize_size).mp low_lt_arr_usize
  . have low_lt_mid : low < mid := by
      have := h₉.size_minus_low_gt_chunkSize
      have := h₉.low_le_arr_usize
      have := h₉.chunkSize_gt_zero
      cases System.Platform.numBits_eq
      . bv_decide
      . bv_decide
    have mid_le_high :=
      USize.mid_le_high (h₉.mid_le_size rfl) (h₉.chunkSize_gt_zero)
    exact Nat.lt_of_lt_of_le low_lt_mid mid_le_high

def H₁₁.decreasing
    (h₁₁ : H₁₁ arr aux low chunkSize)
    : arr.size - low.succ.toNat < arr.size - low.toNat := by
  refine Nat.sub_lt_sub_left h₁₁.low_lt_arr_size ?_
  refine USize.lt_iff_toNat_lt.mp ?_
  cases System.Platform.numBits_eq
  . bv_decide
  . bv_decide

@[specialize, inline]
def mergeChunksIntoAux
    [Ord α]
    (arr : Array α)
    (chunkSize : USize)
    (aux : Subtype (H₈ arr · 0 chunkSize))
    : Array α :=
  let rec @[specialize] loop
      (low : USize)
      (aux : Subtype (H₈ arr · low chunkSize))
      : Array α :=
    if size_minus_low_gt_chunkSize : chunkSize < arr.usize - low then
      have h₉ := aux.property.make_H₉ size_minus_low_gt_chunkSize
      let mid := low + chunkSize
      let high := mid + min (arr.usize - mid) chunkSize
      let aux' := mergeAdjacentChunksIntoAux arr low mid high ⟨aux, h₉.make_H₁⟩
      loop high ⟨aux', h₉.next⟩
    else
      let rec @[specialize] loopFinal
          (low : USize)
          (aux : Subtype (H₁₀ arr · low chunkSize))
          : Array α :=
        if low_lt_aux_usize : low < aux.val.usize then
          have h₁₁ := aux.property.make_H₁₁ low_lt_aux_usize
          have := h₁₁.low_lt_arr_size
          let aux' := aux.val.uset low arr[low] h₁₁.low_toNat_lt_aux_size
          loopFinal low.succ ⟨aux', h₁₁.next⟩
        else
          aux
      termination_by arr.size - low.toNat
      decreasing_by exact h₁₁.decreasing
      loopFinal low ⟨aux, aux.property.make_H₁₀ size_minus_low_gt_chunkSize⟩
  termination_by arr.size - low.toNat
  decreasing_by exact h₉.decreasing
  loop 0 aux

structure H₁₂ (arr aux : Array α) (chunkSize : USize) : Prop where
  size_eq : arr.size = aux.size
  chunkSize_gt_zero : chunkSize > 0
  arr_size_lt_usize_size : arr.size < USize.size

structure H₁₃ (arr aux : Array α) (chunkSize : USize) : Prop
    extends H₁₂ arr aux chunkSize where
  chunkSize_lt_arr_usize : chunkSize < arr.usize

def H₁₂.make_H₁₃
    (h₁₂ : H₁₂ arr aux chunkSize)
    (chunkSize_lt_arr_usize : chunkSize < arr.usize)
    : H₁₃ arr aux chunkSize :=
  { h₁₂ with chunkSize_lt_arr_usize }

def H₁₃.make_H₈
    (h₁₃ : H₁₃ arr aux chunkSize)
    : H₈ arr aux 0 chunkSize :=
  { h₁₃ with low_le_arr_usize := USize.zero_le }

theorem mergeChunksIntoAux.loop.loopFinal.size_eq
    [Ord α]
    {arr : Array α}
    {low chunkSize : USize}
    {aux : Subtype (H₁₀ arr · low chunkSize)}
    : aux.val.size = (loopFinal arr chunkSize low aux).size := by
  unfold loopFinal
  if low_lt_aux_usize : low < aux.val.usize then
    simp only [low_lt_aux_usize, ↓reduceDIte, Array.uset, Array.ugetElem_eq_getElem]
    rw [← size_eq, Array.size_set]
  else
    simp only [low_lt_aux_usize, ↓reduceDIte]
termination_by arr.size - low.toNat
decreasing_by exact aux.property.make_H₁₁ low_lt_aux_usize |>.decreasing

theorem mergeChunksIntoAux.loop.size_eq
    [Ord α]
    {arr : Array α}
    {low chunkSize : USize}
    {aux : Subtype (H₈ arr · low chunkSize)}
    : aux.val.size = (loop arr chunkSize low aux).size := by
  unfold loop
  if size_minus_low_gt_chunkSize : chunkSize < arr.usize - low then
    simp only [size_minus_low_gt_chunkSize]
    simp only [↓reduceDIte, Array.usize, Nat.toUSize_eq]
    rw [← size_eq, ← mergeAdjacentChunksIntoAux.size_eq]
  else
    simp only [size_minus_low_gt_chunkSize]
    exact loopFinal.size_eq (α := α) (aux := ⟨aux, aux.property.make_H₁₀ size_minus_low_gt_chunkSize⟩)
termination_by arr.size - low.toNat
decreasing_by exact aux.property.make_H₉ size_minus_low_gt_chunkSize |>.decreasing

theorem mergeChunksIntoAux.size_eq
    [Ord α]
    (aux : Subtype (H₁₃ arr · chunkSize))
    : aux.val.size = (mergeChunksIntoAux arr chunkSize ⟨aux, aux.property.make_H₈⟩).size := by
  exact loop.size_eq (α := α) (aux := ⟨aux, aux.property.make_H₈⟩)

def H₁₃.next
    [Ord α]
    (h₁₃ : H₁₃ arr aux chunkSize)
    : let aux' := mergeChunksIntoAux arr chunkSize ⟨aux, h₁₃.make_H₈⟩
      H₁₂ aux' arr (chunkSize + min (arr.usize - chunkSize) chunkSize) := by
  intro aux'
  have aux'_def : aux' = mergeChunksIntoAux arr chunkSize ⟨aux, h₁₃.make_H₈⟩ := rfl
  have size_eq : aux'.size = arr.size := by
    rw [aux'_def, h₁₃.size_eq]
    exact Eq.symm (mergeChunksIntoAux.size_eq ⟨aux, h₁₃⟩)
  exact {
    h₁₃ with
    size_eq
    chunkSize_gt_zero := by
      if h : arr.usize - chunkSize ≤ chunkSize then
        simp only [instMinUSize, minOfLe, min, h, ↓reduceIte, gt_iff_lt]
        have := h₁₃.chunkSize_lt_arr_usize
        cases System.Platform.numBits_eq
        . bv_decide
        . bv_decide
      else
        simp only [instMinUSize, minOfLe, min, h, ↓reduceIte, gt_iff_lt]
        have := h₁₃.chunkSize_lt_arr_usize
        have := h₁₃.chunkSize_gt_zero
        cases System.Platform.numBits_eq
        . bv_decide
        . bv_decide
    arr_size_lt_usize_size := by
      rw [size_eq]
      exact h₁₃.arr_size_lt_usize_size
  }

def H₁₂.make
    (size_eq : arr.size = aux.size)
    (arr_size_lt_usize_size : arr.size < USize.size)
    : H₁₂ arr aux 1 :=
  { size_eq, arr_size_lt_usize_size, chunkSize_gt_zero := USize.zero_lt_one }

def H₁₃.decreasing
    [Ord α]
    (h₁₃ : H₁₃ arr aux chunkSize)
    : let aux' := mergeChunksIntoAux arr chunkSize ⟨aux, h₁₃.make_H₈⟩
      let chunkSize' := chunkSize + min (arr.usize - chunkSize) chunkSize
      aux'.size - chunkSize'.toNat < arr.size - chunkSize.toNat := by
  intro aux' chunkSize'
  have chunkSize'_def : chunkSize' = chunkSize + min (arr.usize - chunkSize) chunkSize := rfl
  rw [← mergeChunksIntoAux.size_eq ⟨aux, h₁₃⟩, h₁₃.size_eq]
  refine Nat.sub_lt_sub_left ?_ ?_
  . rw [← h₁₃.size_eq]
    exact (USize.lt_ofNat_iff h₁₃.arr_size_lt_usize_size).mp h₁₃.chunkSize_lt_arr_usize
  . rw [chunkSize'_def]
    refine USize.lt_iff_toNat_lt.mp ?_
    if h : arr.usize - chunkSize ≤ chunkSize then
      simp only [instMinUSize, minOfLe, min, h, ↓reduceIte]
      have := h₁₃.chunkSize_lt_arr_usize
      cases System.Platform.numBits_eq
      . bv_decide
      . bv_decide
    else
      simp only [instMinUSize, minOfLe, min, h, ↓reduceIte]
      have := h₁₃.chunkSize_lt_arr_usize
      have := h₁₃.chunkSize_gt_zero
      cases System.Platform.numBits_eq
      . bv_decide
      . bv_decide

@[specialize, inline]
def Array.mergeSortWithAuxiliary
    [Ord α]
    (arr : Array α)
    (aux : Subtype (H₁₂ arr · 1))
    : Array α :=
  let rec @[specialize] loop
      (arr : Array α)
      (chunkSize : USize)
      (aux : Subtype (H₁₂ arr · chunkSize))
      : Array α :=
    if chunkSize_lt_arr_usize : chunkSize < arr.usize then
      have h₁₃ := aux.property.make_H₁₃ chunkSize_lt_arr_usize
      let aux' := mergeChunksIntoAux arr chunkSize ⟨aux, h₁₃.make_H₈⟩
      let chunkSize' := chunkSize + min (arr.usize - chunkSize) chunkSize
      loop aux' chunkSize' ⟨arr, h₁₃.next⟩
    else
      arr
  termination_by arr.size - chunkSize.toNat
  decreasing_by exact aux.property.make_H₁₃ chunkSize_lt_arr_usize |>.decreasing
  loop arr 1 aux

@[specialize, inline]
def Array.mergeSort
    [Inhabited α]
    [Ord α]
    (arr : Array α)
    (arr_size_lt_usize_size : arr.size < USize.size)
    : Array α :=
  let aux := .replicate arr.size default
  have size_eq := Eq.symm size_replicate
  have h₁₂ := H₁₂.make size_eq arr_size_lt_usize_size
  let aux := ⟨aux, h₁₂⟩
  mergeSortWithAuxiliary arr aux

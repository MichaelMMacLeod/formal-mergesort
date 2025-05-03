import Mathlib.Data.Multiset.Basic
import Init.Data.Array.Basic
import Init.Data.UInt.Lemmas
import Lean.Elab.Tactic

#check List.mergeSort
#check List.sorted_mergeSort
-- #check USize.le_of_eq

variable
  {α : Type}
  {arr aux : Array α}
  {low mid high ptr₁ ptr₂ i chunkSize : USize}

def Array.toMultiset (a : Array α) : Multiset α := Multiset.ofList a.toList

def Array.sorted_by (arr : Array α) (le : α → α → Prop) : Prop :=
  ∀ l r : Fin arr.size,
    l.val.succ = r →
      le arr[l] arr[r]

#check Array.sorted_by (α := USize) #[1, 2, 3] (· ≤ ·)

abbrev USize.succ (n : USize) := n + 1

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

/--
arr_size_lt_usize_size
low_le_mid
mid_le_size
mid_le_high
high_le_size
size_eq
ptr₁_ge_low
ptr₁_le_mid
ptr₂_ge_mid
ptr₂_le_high
i_ge_low
i_le_high
i_def
--/

def USize.ge_of_eq {a b : USize} (h : a = b) : a ≥ b := USize.le_of_eq (Eq.symm h)

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
    ptr₁_lt_mid := by cases System.Platform.numBits_eq <;> bv_normalize
    ptr₂_lt_high := by cases System.Platform.numBits_eq <;> bv_normalize
    i_lt_high := by
      rw [h₂.i_def]
      cases System.Platform.numBits_eq
      . bv_decide
      . bv_decide
  }

def H₃.ptr₁_lt_arr_size
    (h₃ : H₃ arr aux low mid high ptr₁ ptr₂ i)
    : ptr₁.toNat < arr.size := by
  have ptr₁_lt_size : ptr₁ < arr.usize := by
    cases System.Platform.numBits_eq
    . bv_decide
    . bv_decide
  exact (USize.lt_ofNat_iff h₃.arr_size_lt_usize_size).mp ptr₁_lt_size

def H₃.ptr₂_lt_arr_size
    (h₃ : H₃ arr aux low mid high ptr₁ ptr₂ i)
    : ptr₂.toNat < arr.size := by
  have ptr₂_lt_size : ptr₂ < arr.usize := by
    cases System.Platform.numBits_eq
    . bv_decide
    . bv_decide
  exact (USize.lt_ofNat_iff h₃.arr_size_lt_usize_size).mp ptr₂_lt_size

def H₃.i_lt_aux_size
    (h₃ : H₃ arr aux low mid high ptr₁ ptr₂ i)
    : i.toNat < aux.size := by
  have i_lt_size : i < arr.usize := by
    cases System.Platform.numBits_eq
    . bv_decide
    . bv_decide
  rw [← h₃.size_eq]
  exact (USize.lt_ofNat_iff h₃.arr_size_lt_usize_size).mp i_lt_size

def H₃.next₁
    (h₃ : H₃ arr aux low mid high ptr₁ ptr₂ i)
    : have ptr₁_lt_arr_size := h₃.ptr₁_lt_arr_size
      let aux' := aux.uset i arr[ptr₁] h₃.i_lt_aux_size
      H₂ arr aux' low mid high ptr₁.succ ptr₂ i.succ :=
  { h₃ with
    size_eq := by
      simp only [Array.uset, Array.ugetElem_eq_getElem, Array.size_set]
      exact h₃.size_eq
    ptr₁_ge_low := by
      cases System.Platform.numBits_eq
      . bv_decide
      . bv_decide
    ptr₁_le_mid := by
      cases System.Platform.numBits_eq
      . bv_decide
      . bv_decide
    i_ge_low := by
      cases System.Platform.numBits_eq
      . bv_decide
      . bv_decide
    i_le_high := by
      cases System.Platform.numBits_eq
      . bv_decide
      . bv_decide
    i_def := by
      cases System.Platform.numBits_eq
      . bv_decide
      . bv_decide
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
    ptr₂_ge_mid := by
      cases System.Platform.numBits_eq
      . bv_decide
      . bv_decide
    ptr₂_le_high := by
      cases System.Platform.numBits_eq
      . bv_decide
      . bv_decide
    i_ge_low := by
      cases System.Platform.numBits_eq
      . bv_decide
      . bv_decide
    i_le_high := by
      cases System.Platform.numBits_eq
      . bv_decide
      . bv_decide
    i_def := by
      cases System.Platform.numBits_eq
      . bv_decide
      . bv_decide
  }

structure H₄ (arr aux : Array α) (low mid high ptr₁ ptr₂ i : USize) : Prop
    extends H₂ arr aux low mid high ptr₁ ptr₂ i where
  not_ptr₁_ptr₂_in_range : ptr₁ = mid ∨ ptr₂ = high

def H₂.make_H₄
    (h₂ : H₂ arr aux low mid high ptr₁ ptr₂ i)
    (not_ptr₁_ptr₂_in_range : ¬(ptr₁ < mid ∧ ptr₂ < high))
    : H₄ arr aux low mid high ptr₁ ptr₂ i :=
  { h₂ with
    not_ptr₁_ptr₂_in_range := by
      cases System.Platform.numBits_eq
      . bv_decide
      . bv_decide
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
  have ptr₁_lt_size : ptr₁ < arr.usize := by
    cases System.Platform.numBits_eq
    . bv_decide
    . bv_decide
  exact (USize.lt_ofNat_iff h₅.arr_size_lt_usize_size).mp ptr₁_lt_size

def H₅.i_lt_aux_size
    (h₅ : H₅ arr aux low mid high ptr₁ ptr₂ i)
    : i.toNat < aux.size := by
  have i_lt_size : i < arr.usize := by
    cases System.Platform.numBits_eq
    . bv_decide
    . bv_decide
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
    ptr₁_ge_low := by
      cases System.Platform.numBits_eq
      . bv_decide
      . bv_decide
    ptr₁_le_mid := by
      cases System.Platform.numBits_eq
      . bv_decide
      . bv_decide
    i_ge_low := by
      cases System.Platform.numBits_eq
      . bv_decide
      . bv_decide
    i_le_high := by
      cases System.Platform.numBits_eq
      . bv_decide
      . bv_decide
    i_def := by
      cases System.Platform.numBits_eq
      . bv_decide
      . bv_decide
    not_ptr₁_ptr₂_in_range := by
      cases System.Platform.numBits_eq
      . bv_decide
      . bv_decide
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

def H₇.next
    (h₇ : H₇ arr aux low mid high ptr₁ ptr₂ i)
    : have ptr₂_lt_arr_size := h₇.ptr₂_lt_arr_size
      let aux' := aux.uset i arr[ptr₂] h₇.i_lt_aux_size
      H₆ arr aux' low mid high ptr₁ ptr₂.succ i.succ :=
  { h₇ with
    size_eq := by
      simp only [Array.uset, Array.ugetElem_eq_getElem, Array.size_set]
      exact h₇.size_eq
    ptr₂_ge_mid := by
      cases System.Platform.numBits_eq
      . bv_decide
      . bv_decide
    ptr₂_le_high := by
      cases System.Platform.numBits_eq
      . bv_decide
      . bv_decide
    i_ge_low := by
      cases System.Platform.numBits_eq
      . bv_decide
      . bv_decide
    i_le_high := by
      cases System.Platform.numBits_eq
      . bv_decide
      . bv_decide
    i_def := by
      cases System.Platform.numBits_eq
      . bv_decide
      . bv_decide
    not_ptr₁_ptr₂_in_range := by
      cases System.Platform.numBits_eq
      . bv_decide
      . bv_decide
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
    (arr aux : Array α)
    (low mid high : USize)
    (h₁ : H₁ arr aux low mid high)
    : Array α :=
  let rec @[specialize] loop
      (aux : Array α)
      (ptr₁ ptr₂ i : USize)
      (h₂ : H₂ arr aux low mid high ptr₁ ptr₂ i)
      : Array α :=
    if ptr₁_ptr₂_in_range : ptr₁ < mid ∧ ptr₂ < high then
      have h₃ := h₂.make_H₃ ptr₁_ptr₂_in_range
      have := h₃.ptr₁_lt_arr_size
      have := h₃.ptr₂_lt_arr_size
      match Ord.compare arr[ptr₁] arr[ptr₂] with
      | .lt | .eq =>
        let aux' := aux.uset i arr[ptr₁] h₃.i_lt_aux_size
        loop aux' ptr₁.succ ptr₂ i.succ h₃.next₁
      | .gt =>
        let aux' := aux.uset i arr[ptr₂] h₃.i_lt_aux_size
        loop aux' ptr₁ ptr₂.succ i.succ h₃.next₂
    else
      let rec @[specialize] loopLeft
          (aux : Array α)
          (ptr₁ i : USize)
          (h₄ : H₄ arr aux low mid high ptr₁ ptr₂ i)
          : Array α :=
        if ptr₁_lt_mid : ptr₁ < mid then
          have h₅ := h₄.make_H₅ ptr₁_lt_mid
          have := h₅.ptr₁_lt_arr_size
          let aux' := aux.uset i arr[ptr₁] h₅.i_lt_aux_size
          loopLeft aux' ptr₁.succ i.succ h₅.next
        else
          let rec @[specialize] loopRight
              (aux : Array α)
              (ptr₂ i : USize)
              (h₆ : H₆ arr aux low mid high ptr₁ ptr₂ i)
              : Array α :=
            if ptr₂_lt_high : ptr₂ < high then
              have h₇ := h₆.make_H₇ ptr₂_lt_high
              have := h₇.ptr₂_lt_arr_size
              let aux' := aux.uset i arr[ptr₂] h₇.i_lt_aux_size
              loopRight aux' ptr₂.succ i.succ h₇.next
            else
              aux
          termination_by arr.size - i.toNat
          decreasing_by all_goals exact h₇.decreasing
          loopRight aux ptr₂ i (h₄.make_H₆ ptr₁_lt_mid)
      termination_by arr.size - i.toNat
      decreasing_by all_goals exact h₅.decreasing
      loopLeft aux ptr₁ i (h₂.make_H₄ ptr₁_ptr₂_in_range)
  termination_by arr.size - i.toNat
  decreasing_by all_goals exact h₃.decreasing
  loop aux (ptr₁ := low) (ptr₂ := mid) (i := low) (h₁.make_H₂ rfl rfl rfl)

structure H₈ (arr aux : Array α) (low chunkSize : USize) : Prop where
  arr_size_lt_usize_size : arr.size < USize.size
  size_eq : arr.size = aux.size
  low_le_arr_size : low ≤ arr.usize
  chunkSize_gt_zero : chunkSize > 0
  chunkSize_lt_arr_size : chunkSize < arr.usize

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
  . cases System.Platform.numBits_eq
    . bv_decide
    . bv_decide

theorem USize.add_lt_of_sub
    {a b c : USize}
    (h : b ≤ a)
    : a - b > c → b + c < a := by
  . cases System.Platform.numBits_eq
    . bv_decide
    . bv_decide

theorem USize.mid_le_high
    {mid size chunkSize : USize}
    (mid_le_size : mid ≤ size)
    (chunkSize_gt_zero : chunkSize > 0)
    : mid ≤ mid + (size - mid) ⊓ chunkSize := by
  if h : size - mid ≤ chunkSize then
    simp only [instMinUSize, minOfLe, min, h, ↓reduceIte]
    . cases System.Platform.numBits_eq
      . bv_decide
      . bv_decide
  else
    simp only [instMinUSize, minOfLe, min, h, ↓reduceIte]
    . cases System.Platform.numBits_eq
      . bv_decide
      . bv_decide

theorem USize.high_le_size
    {mid size chunkSize : USize}
    (mid_le_size : mid ≤ size)
    (chunkSize_gt_zero : chunkSize > 0)
    : mid + (size - mid) ⊓ chunkSize ≤ size := by
  if h : size - mid ≤ chunkSize then
    simp only [instMinUSize, minOfLe, min, h, ↓reduceIte]
    . cases System.Platform.numBits_eq
      . bv_decide
      . bv_decide
  else
    simp only [instMinUSize, minOfLe, min, h, ↓reduceIte]
    . cases System.Platform.numBits_eq
      . bv_decide
      . bv_decide

def H₉.make_H₁
    (h₉ : H₉ arr aux low chunkSize)
    : let mid := low + chunkSize
      let high := mid + min (arr.usize - mid) chunkSize
      H₁ arr aux low mid high := by
  intro mid high
  have mid_def : mid = low + chunkSize := rfl
  have high_def : high = mid + min (arr.usize - mid) chunkSize := rfl
  have low_le_mid : low ≤ mid :=
    USize.le_add_of_sub_gt h₉.low_le_arr_size h₉.size_minus_low_gt_chunkSize
  have mid_le_size : mid ≤ arr.usize := by
    rw [mid_def]
    refine USize.le_of_lt ?_
    exact USize.add_lt_of_sub h₉.low_le_arr_size h₉.size_minus_low_gt_chunkSize
  exact {
    arr_size_lt_usize_size := h₉.arr_size_lt_usize_size
    low_le_mid
    mid_le_size
    mid_le_high := USize.mid_le_high mid_le_size h₉.chunkSize_gt_zero
    high_le_size := USize.high_le_size mid_le_size h₉.chunkSize_gt_zero
    size_eq := h₉.size_eq
  }

theorem mergeAdjacentChunksIntoAux.loop.loopLeft.loopRight.size_eq
    [Ord α]
    {aux : Array α}
    {ptr₂ i : USize}
    {h₆ : H₆ arr aux low mid high ptr₁ ptr₂ i}
    : aux.size = (mergeAdjacentChunksIntoAux.loop.loopLeft.loopRight arr low mid high ptr₁ aux ptr₂ i h₆).size := by
  unfold loopRight
  if ptr₂_lt_high : ptr₂ < high then
    simp [ptr₂_lt_high, ← size_eq (i := i.succ)]
  else
    simp [ptr₂_lt_high]
termination_by arr.size - i.toNat
decreasing_by exact h₆.make_H₇ ptr₂_lt_high |>.decreasing

theorem mergeAdjacentChunksIntoAux.loop.loopLeft.size_eq
    [Ord α]
    {aux : Array α}
    {ptr₁ i : USize}
    {h₄ : H₄ arr aux low mid high ptr₁ ptr₂ i}
    : aux.size = (mergeAdjacentChunksIntoAux.loop.loopLeft arr low mid high ptr₂ aux ptr₁ i h₄).size := by
  unfold loopLeft
  if ptr₁_lt_mid : ptr₁ < mid then
    simp [ptr₁_lt_mid, Array.uset, Array.ugetElem_eq_getElem, ← size_eq (i := i.succ)]
  else
    simp [ptr₁_lt_mid, ← loopRight.size_eq]
termination_by arr.size - i.toNat
decreasing_by exact h₄.make_H₅ ptr₁_lt_mid |>.decreasing

theorem mergeAdjacentChunksIntoAux.loop.size_eq
    [Ord α]
    {aux : Array α}
    {ptr₁ ptr₂ i : USize}
    {h₂ : H₂ arr aux low mid high ptr₁ ptr₂ i}
    : aux.size = (loop arr low mid high aux ptr₁ ptr₂ i h₂).size := by
  unfold loop
  if ptr₁_ptr₂_in_range : ptr₁ < mid ∧ ptr₂ < high then
    simp only [ptr₁_ptr₂_in_range, and_self, ↓reduceDIte, Array.ugetElem_eq_getElem, Array.uset]
    split <;> rw [← size_eq, Array.size_set]
  else
    simp only [ptr₁_ptr₂_in_range, ↓reduceDIte, ← loopLeft.size_eq]
termination_by arr.size - i.toNat
decreasing_by all_goals exact h₂.make_H₃ ptr₁_ptr₂_in_range |>.decreasing

theorem mergeAdjacentChunksIntoAux.size_eq
    [Ord α]
    (h₁ : H₁ arr aux low mid high)
    : aux.size = (mergeAdjacentChunksIntoAux arr aux low mid high h₁).size :=
  mergeAdjacentChunksIntoAux.loop.size_eq

def H₉.next
    [Ord α]
    (h₉ : H₉ arr aux low chunkSize)
    : let mid := low + chunkSize
      let high := mid + min (arr.usize - mid) chunkSize
      have aux' := mergeAdjacentChunksIntoAux arr aux low mid high h₉.make_H₁
      H₈ arr aux' high chunkSize := by
  intro mid high aux'
  have mid_def : mid = low + chunkSize := rfl
  have high_def : high = mid + min (arr.usize - mid) chunkSize := rfl
  have mid_le_size : mid ≤ arr.usize := by
    rw [mid_def]
    refine USize.le_of_lt ?_
    exact USize.add_lt_of_sub h₉.low_le_arr_size h₉.size_minus_low_gt_chunkSize
  exact {
    h₉ with
    size_eq := by
      simp only [h₉.size_eq, aux']
      exact mergeAdjacentChunksIntoAux.size_eq h₉.make_H₁
    low_le_arr_size := by
      rw [high_def]
      exact USize.high_le_size mid_le_size h₉.chunkSize_gt_zero
  }

@[specialize, inline]
def mergeChunksIntoAux
    [Ord α]
    (arr aux : Array α)
    (chunkSize : USize)
    (h₈ : H₈ arr aux low chunkSize) :=
  let rec @[specialize] loop
      (aux : Array α)
      (low : USize)
      (h₈ : H₈ arr aux low chunkSize)
      : Array α :=
    if size_minus_low_gt_chunkSize : arr.usize - low > chunkSize then
      have h₉ := h₈.make_H₉ size_minus_low_gt_chunkSize
      let mid := low + chunkSize
      let high := mid + min (arr.usize - mid) chunkSize
      let aux' := mergeAdjacentChunksIntoAux arr aux low mid high h₉.make_H₁
      loop aux' high h₉.next
    else
      let rec @[specialize] loop (aux : Array α) (low : USize) : Array α :=
        if low < aux.usize then
          let aux' := aux.uset low (arr[low]'sorry) sorry
          loop aux' low.succ
        else
          aux
      loop aux low
  loop aux 0

@[specialize, inline]
def Array.mergeSortWithAuxiliary
    [Inhabited α]
    [Ord α]
    (arr aux : Array α)
    (_size_eq : aux.size = arr.size)
  : Array α :=
  let rec @[specialize] loop
      (arr aux : Array α)
      (chunkSize : USize)
      : Array α :=
    if chunkSize < arr.usize then
      let aux' := mergeChunksIntoAux arr aux chunkSize
      loop aux' arr (chunkSize * 2)
    else
      arr
  loop arr aux 1

@[specialize, inline]
def Array.mergeSort [Inhabited α] [Ord α] (arr : Array α) : Array α :=
  mergeSortWithAuxiliary arr (aux := .replicate arr.size default) size_replicate

-- def USize.maxValue : USize := 2 ^ 64 |>.toUSize

-- class ArraySortingAlgorithm
--   (cmp : α → α → Bool)
--   (algo : Array α → Array α)
--     -- (trans : ∀ a b c : α, cmp a b → cmp b c → cmp a c)
--     -- (total : ∀ a b : α, cmp a b ∨ cmp b a)
--     -- (algo : Cmp → Array α → Array α)
--   where
--   sorted :
--     ∀ arr : Array α,
--       ∀ l r : Fin (algo arr).size,
--         l.val.succ = r →
--           cmp (algo arr)[l] (algo arr)[r]
--   permutation :
--     ∀ arr : Array α,
--       arr.toMultiset = (algo arr).toMultiset

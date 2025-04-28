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
  {low mid high ptr₁ ptr₂ i : USize}

def Array.toMultiset (a : Array α) : Multiset α := Multiset.ofList a.toList

def Array.sorted_by (arr : Array α) (le : α → α → Prop) : Prop :=
  ∀ l r : Fin arr.size,
    l.val.succ = r →
      le arr[l] arr[r]

#check Array.sorted_by (α := USize) #[1, 2, 3] (· ≤ ·)

abbrev USize.succ (n : USize) := n + 1

structure H₁ (arr aux : Array α) (low mid high : USize) : Prop where
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
      . bv_check "Basic.lean-H₂.make_H₃-94-8.lrat"
      . bv_check "Basic.lean-H₂.make_H₃-95-8.lrat"
  }

def H₃.ptr₁_lt_size
    (h₃ : H₃ arr aux low mid high ptr₁ ptr₂ i)
    (v : high < (10 |>.toUSize))
    : ptr₁.toNat < arr.size := by
  cases System.Platform.numBits_eq
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
      have v := h₃.ptr₁_lt_size
      match Ord.compare arr[ptr₁] (arr[ptr₂]'sorry) with
      | .lt | .eq =>
        let aux' := aux.uset i (arr[ptr₁]'sorry) sorry
        loop aux' ptr₁.succ ptr₂ i.succ sorry
      | .gt =>
        let aux' := aux.uset i (arr[ptr₂]'sorry) sorry
        loop aux' ptr₁ ptr₂.succ i.succ sorry
    else
      let rec @[specialize] loopLeft
          (aux : Array α)
          (ptr₁ i : USize)
          : Array α :=
        if ptr₁ < mid then
          let aux' := aux.uset i (arr[ptr₁]'sorry) sorry
          loopLeft aux' ptr₁.succ i.succ
        else
          let rec @[specialize] loopRight
              (aux : Array α)
              (ptr₂ i : USize)
              : Array α :=
            if ptr₂ < high then
              let aux' := aux.uset i (arr[ptr₂]'sorry) sorry
              loopRight aux' ptr₂.succ i.succ
            else
              aux
          loopRight aux ptr₂ i
      loopLeft aux ptr₁ i
  loop aux (ptr₁ := low) (ptr₂ := mid) (i := low) (h₁.make_H₂ rfl rfl rfl)

@[specialize, inline]
def mergeChunksIntoAux
    [Ord α]
    (arr aux : Array α)
    (size : USize) :=
  let rec @[specialize] loop (aux : Array α) (start₁: USize)
      : Array α :=
    if start₁ + size < arr.usize then
      let start₂ := start₁ + size
      let end₂ := min (start₂ + size) arr.usize
      let aux' := mergeAdjacentChunksIntoAux arr aux start₁ start₂ end₂ sorry
      loop aux' (start₁ + 2 * size)
    else
      let rec @[specialize] loopFinal (aux : Array α) (start₁ : USize) : Array α :=
        if start₁ < aux.usize then
          let aux' := aux.uset start₁ (arr[start₁]'sorry) sorry
          loopFinal aux' start₁.succ
        else
          aux
      loopFinal aux start₁
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

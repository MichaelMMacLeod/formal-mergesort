import Mathlib.Data.Multiset.Basic
import Init.Data.Array.Basic
import Init.Data.UInt.Lemmas
import Lean.Elab.Tactic

#check List.mergeSort
#check List.sorted_mergeSort
-- #check UInt64.le_of_eq

variable
  {α : Type}
  {arr aux : Array α}
  {low mid high ptr₁ ptr₂ i : UInt64}

def Array.toMultiset (a : Array α) : Multiset α := Multiset.ofList a.toList

def Array.sorted_by (arr : Array α) (le : α → α → Prop) : Prop :=
  ∀ l r : Fin arr.size,
    l.val.succ = r →
      le arr[l] arr[r]

#check Array.sorted_by (α := UInt64) #[1, 2, 3] (· ≤ ·)

abbrev UInt64.succ (n : UInt64) := n + 1
abbrev Array.uint64Size (arr : Array α) : UInt64 := arr.usize.toUInt64

structure H₁ (arr aux : Array α) (low mid high : UInt64) : Prop where
  low_le_mid : low ≤ mid
  mid_le_size : mid ≤ arr.uint64Size
  mid_le_high : mid ≤ high
  high_le_size : high ≤ arr.uint64Size
  size_eq : arr.size = aux.size

structure H₂ (arr aux : Array α) (low mid high ptr₁ ptr₂ i : UInt64) : Prop
    extends H₁ arr aux low mid high where
  ptr₁_ge_low : ptr₁ ≥ low
  ptr₁_le_mid : ptr₁ ≤ mid
  ptr₂_ge_mid : ptr₂ ≥ mid
  ptr₂_le_high : ptr₂ ≤ high
  i_ge_low : i ≥ low
  i_le_high : i ≤ high
  i_def : i = ptr₁ + ptr₂ - mid


def UInt64.ge_of_eq {a b : UInt64} (h : a = b) : a ≥ b := UInt64.le_of_eq (Eq.symm h)

def H₁.make_H₂
    (h₁ : H₁ arr aux low mid high)
    (ptr₁_def : ptr₁ = low)
    (ptr₂_def : ptr₂ = mid)
    (i_def : i = ptr₁)
    : H₂ arr aux low mid high ptr₁ ptr₂ i :=
  {
    h₁ with
    ptr₁_ge_low := UInt64.ge_of_eq ptr₁_def
    ptr₁_le_mid := UInt64.le_trans (UInt64.le_of_eq ptr₁_def) h₁.low_le_mid
    ptr₂_ge_mid := UInt64.ge_of_eq ptr₂_def
    ptr₂_le_high := UInt64.le_trans (UInt64.le_of_eq ptr₂_def) h₁.mid_le_high
    i_ge_low := UInt64.ge_of_eq (ptr₁_def ▸ i_def)
    i_le_high := UInt64.le_trans (UInt64.le_of_eq <| ptr₁_def ▸ i_def) (UInt64.le_trans h₁.low_le_mid h₁.mid_le_high)
    i_def := by simp only [ptr₁_def, ptr₂_def, UInt64.add_sub_cancel, ptr₁_def ▸ i_def]
  }

@[specialize, inline]
def mergeAdjacentChunksIntoAux
    [Ord α]
    (arr aux : Array α)
    (start₁ start₂ end₂ : UInt64)
    (h₁ : H₁ arr aux low mid high)
    : Array α :=
  let rec @[specialize] loop
      (aux : Array α)
      (ptr₁ ptr₂ i : UInt64)
      (h₂ : H₂ arr aux low mid high ptr₁ ptr₂ i)
      : Array α :=
    if ptr₁ < start₂ ∧ ptr₂ < end₂ then
      match Ord.compare (arr[ptr₁.toUSize]'sorry) (arr[ptr₂.toUSize]'sorry) with
      | .lt | .eq =>
        let aux' := aux.uset i.toUSize (arr[ptr₁.toUSize]'sorry) sorry
        loop aux' ptr₁.succ ptr₂ i.succ sorry
      | .gt =>
        let aux' := aux.uset i.toUSize (arr[ptr₂.toUSize]'sorry) sorry
        loop aux' ptr₁ ptr₂.succ i.succ sorry
    else
      let rec @[specialize] loopLeft
          (aux : Array α)
          (ptr₁ i : UInt64)
          : Array α :=
        if ptr₁ < start₂ then
          let aux' := aux.uset i.toUSize (arr[ptr₁.toUSize]'sorry) sorry
          loopLeft aux' ptr₁.succ i.succ
        else
          let rec @[specialize] loopRight
              (aux : Array α)
              (ptr₂ i : UInt64)
              : Array α :=
            if ptr₂ < end₂ then
              let aux' := aux.uset i.toUSize (arr[ptr₂.toUSize]'sorry) sorry
              loopRight aux' ptr₂.succ i.succ
            else
              aux
          loopRight aux ptr₂ i
      loopLeft aux ptr₁ i
  let ptr₁ := low
  let ptr₂ := mid
  let i := ptr₁
  loop aux low mid ptr₁ (h₁.make_H₂ rfl rfl rfl)

@[specialize, inline]
def mergeChunksIntoAux
    [Ord α]
    (arr aux : Array α)
    (size : UInt64) :=
  let rec @[specialize] loop (aux : Array α) (start₁: UInt64)
      : Array α :=
    if start₁ + size < arr.uint64Size then
      let start₂ := start₁ + size
      let end₂ := min (start₂ + size) arr.uint64Size
      let aux' := mergeAdjacentChunksIntoAux arr aux start₁ start₂ end₂ sorry
      loop aux' (start₁ + 2 * size)
    else
      let rec @[specialize] loopFinal (aux : Array α) (start₁ : UInt64) : Array α :=
        if start₁ < aux.uint64Size then
          let aux' := aux.uset start₁.toUSize (arr[start₁.toUSize]'sorry) sorry
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
      (chunkSize : UInt64)
      : Array α :=
    if chunkSize < arr.uint64Size then
      let aux' := mergeChunksIntoAux arr aux chunkSize
      loop aux' arr (chunkSize * 2)
    else
      arr
  loop arr aux 1

@[specialize, inline]
def Array.mergeSort [Inhabited α] [Ord α] (arr : Array α) : Array α :=
  mergeSortWithAuxiliary arr (aux := .replicate arr.size default) size_replicate

-- def UInt64.maxValue : UInt64 := 2 ^ 64 |>.toUInt64

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

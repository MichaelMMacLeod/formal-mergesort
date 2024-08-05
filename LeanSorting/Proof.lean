import Mathlib.Data.Multiset.Basic
import «LeanSorting».Total

def Array.non_decreasing [Ord α] {as : Array α} : Prop :=
  ∀ i j : Fin as.size,
    i.val.succ = j.val →
      Ord.compare as[i] as[j] != Ordering.gt

def Array.permutation_of (as : Array α) (bs : Array α) : Prop :=
  Multiset.ofList as.data = Multiset.ofList bs.data

def Array.sorting_algorithm [Ord α] (f : Array α → Array α) : Prop :=
  ∀ arr : Array α,
      (f arr).non_decreasing
    ∧ (f arr).permutation_of arr

def Array.non_decreasing_slice [Ord α] (arr : Array α) (low high : ℕ) : Prop :=
  ∀ i j : Fin arr.size,
    i.val.succ = j.val ∧ i ≥ low ∧ j < high →
      Ord.compare arr[i] arr[j] != Ordering.gt

def Array.contains_sorted_slices [Ord α] (arr : Array α) (chunkSize : ℕ) : Prop :=
  ∀ start : Fin arr.size,
    start % chunkSize = 0 →
      arr.non_decreasing_slice start (min (start + chunkSize) arr.size)

variable
  {α : Type}
  [ord_a : Ord α]
  (arr aux : Array α)
  (start₁ start₂ end₂ i k₁ k₂ chunkSize : ℕ)

theorem mergeAdjacentChunksIntoAux.loop.loopLeft.loopRight_non_decreasing_slice
    (slice₂_sorted : arr.non_decreasing_slice start₂ end₂)
    : mergeAdjacentChunksIntoAux.loop.loopLeft.loopRight arr start₁ start₂ end₂ k₁ aux i k₂ h₄Right
        |>.non_decreasing_slice start₁ end₂
    := by
  sorry

theorem mergeAdjacentChunksIntoAux_non_decreasing_slice
    (slice₁_sorted : arr.non_decreasing_slice start₁ start₂)
    (slice₂_sorted : arr.non_decreasing_slice start₂ end₂)
    : mergeAdjacentChunksIntoAux arr aux start₁ start₂ end₂ h₁
        |>.non_decreasing_slice start₁ end₂
    := by
  sorry

-- structure Slice (arr : Array α) : Prop where
--   start : ℕ
--   count : ℕ
--   start_plus_count_le_size : start + count < arr.size

-- structure NonDecreasingSlice (arr : Array α) extends Slice arr where
--   non_decreasing : arr.non_decreasing

-- theorem mergeChunksIntoAux_runs
--     : mergeChunksIntoAux

theorem mergesort_non_decreasing
    [Ord α]
    {arr : Array α}
    : arr.mergeSort.non_decreasing := by
  simp [Array.non_decreasing]
  intro i j
  intro i_succ_eq_j
  simp [Array.mergeSort]
  sorry

theorem mergesort_preserves_elements
    [Ord α]
    {arr : Array α}
    : (Array.mergeSort arr).permutation_of arr := by
  sorry

theorem sorting_algorithm_mergeSort
    [Ord α]
    : Array.sorting_algorithm Array.mergeSort (α := α) := by
  simp [Array.sorting_algorithm]
  intro arr
  apply And.intro
  . case left =>
    exact mergesort_non_decreasing
  . case right =>
    exact mergesort_preserves_elements

-- Sketch of proof:
--
-- 1. We need to prove that the returned array is in non-decreasing order.
--
-- mergeSort runs with chunk size 1, 2, 4, 8, 16, ..., until the chunk
-- size is ≥ arr.size.
--
-- We need to show that when (chunkSize * 2 ≥ arr.size),
-- it is the case that after running mergeChunksIntoAux, elements
-- 0..arr.size of aux form a non-decreasing run.
--
-- Our induction hypothesis is that for a given chunkSize C (with C < arr.size),
-- it is the case that after running mergeChunksIntoAux, elements
-- 0..2C, 2C..4C, 4C..6C, ... and so on each form non-decreasing runs of aux.
--
-- When C=1 (our base case), mergeChunksIntoAux checks if the two elements are in order
-- and swaps them if they are not, so it follows that elements 0..2 are in order.
--
-- For C>1, we can assume that 0..2C, 2C..4C, 4C..6C, ... and so on form non-decreasing
-- runs. We then can show that mergeAdjacentChunksIntoAux, when given a non-decreasing run,
-- merges 0..C and C..2C, 2C..3C and 3C..4C and so on into non-decreasing runs spanning
-- both.

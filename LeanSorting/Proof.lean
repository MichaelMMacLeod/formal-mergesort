import «LeanSorting».Basic

structure Slice (α : Type) where
  arr : Array α
  start : ℕ
  endExclusive : ℕ
  start_lt_arr_size : start < arr.size
  endExclusive_le_arr_size : endExclusive ≤ arr.size
  start_le_endExclusive : start ≤ endExclusive

def Slice.indices [Ord α] (s : Slice α) : Set ℕ :=
  { i | i ≥ s.start ∧ i < s.endExclusive }

def Slice.non_decreasing [Ord α] (s : Slice α) : Prop :=
  (i j : ℕ) →
    (hp : i ∈ s.indices ∧ j ∈ s.indices ∧ i.succ = j) →
      have : i < s.arr.size := by
        apply And.left at hp
        simp [Slice.indices] at hp
        apply And.right at hp
        exact (Nat.lt_of_lt_le hp s.endExclusive_le_arr_size)
      have : j < s.arr.size := by
        apply And.right at hp
        apply And.left at hp
        simp [Slice.indices] at hp
        apply And.right at hp
        exact (Nat.lt_of_lt_le hp s.endExclusive_le_arr_size)
      Ord.compare s.arr[i] s.arr[j] != Ordering.gt

def mergeAdjacentChunksIntoAuxSlice
    [Ord α]
    (m₁ : M₁ α)
    : Slice α :=
  let m₁' := mergeAdjacentChunksIntoAux m₁
  have start_lt_arr_size : m₁'.start₁ < m₁'.aux.size := by sorry
  have endExclusive_le_arr_size : m₁'.end₂ ≤ m₁'.aux.size := by sorry
  have start_le_endExclusive : m₁'.start₁ ≤ m₁'.end₂ := by sorry
  {
    arr := m₁'.aux,
    start := m₁'.start₁,
    endExclusive := m₁'.end₂,
    start_lt_arr_size,
    endExclusive_le_arr_size,
    start_le_endExclusive,
  }

def mergeAdjacentChunksIntoAux_non_decreasing
    [Ord α]
    (m₁ : M₁ α)
    : Prop :=
  (mergeAdjacentChunksIntoAuxSlice m₁).non_decreasing

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

-- theorem mergeChunksIntoAuxRuns
--   [Ord α]


theorem mergesort_non_decreasing
    [Inhabited α]
    [Ord α]
    {arr : Array α}
    : arr.mergeSort.non_decreasing := by

  simp [Array.non_decreasing]
  intro i j
  intro i_succ_eq_j
  simp [Array.mergeSort]
  sorry

theorem mergesort_preserves_elements
    [Inhabited α]
    [Ord α]
    {arr : Array α}
    : (Array.mergeSort arr).permutation_of arr := by
  sorry

theorem sorting_algorithm_mergeSort
    [Inhabited α]
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
-- and swaps them if they are not, so it follows that elements 0..2,
--
-- For C>1, we can assume that 0..2C, 2C..4C, 4C..6C, ... and so on form non-decreasing
-- runs. We then can show that mergeAdjacentChunksIntoAux, when given a non-decreasing run,
-- merges 0..C and C..2C, 2C..3C and 3C..4C and so on into non-decreasing runs spanning
-- both.

import Mathlib.Data.Nat.ModEq

-- We define 'mergeSortPartial' here which is the exact same algorithm as 'mergeSort' from
-- «LeanSorting».Total, except that 'mergeSortPartial' uses panic-based (instead of Fin-based)
-- array indexing. Hopefully, given that the code here is much simpler, this may help you
-- get a better sense of how it all works.

/--
Copies the regions `start₁`..`start₂` and `start₂`..`end₂` (exclusive endpoints) from `arr` into
`aux`. If the regions themselves are each sorted, the resulting region (spanning indices
`start₁`..`end₂` in `aux`) will also be sorted. It should be the case that `arr.size = aux.size`.
-/
@[specialize, inline]
partial def mergeAdjacentChunksIntoAuxPartial
    [Inhabited α]
    [Ord α]
    (arr aux : Array α)
    (start₁ start₂ end₂ : ℕ)
    : Array α :=
  -- Copy the lowest element from the left and right regions until one of them is fully copied.
  let rec @[specialize] loop
      (aux : Array α)
      (i k₁ k₂ : ℕ)
      : Array α :=
    if k₁ < start₂ ∧ k₂ < end₂ then
      match Ord.compare arr[k₁]! arr[k₂]! with
      | .lt | .eq =>
        let aux' := aux.set! i arr[k₁]!
        loop aux' i.succ k₁.succ k₂
      | .gt =>
        let aux' := aux.set! i arr[k₂]!
        loop aux' i.succ k₁ k₂.succ
    else
      -- If the left region is not yet empty, finish copying it.
      let rec @[specialize] loopLeft
          (aux : Array α)
          (i k₁ : ℕ)
          : Array α :=
        if k₁ < start₂ then
          let aux' := aux.set! i arr[k₁]!
          loopLeft aux' i.succ k₁.succ
        else
          -- If the right region is not yet empty, finish copying it.
          let rec @[specialize] loopRight
              (aux : Array α)
              (i k₂ : ℕ)
              : Array α :=
            if k₂ < end₂ then
              let aux' := aux.set! i arr[k₂]!
              loopRight aux' i.succ k₂.succ
            else
              aux
          loopRight aux i k₂
      loopLeft aux i k₁
  loop aux start₁ start₁ start₂

/--
Merges every two adjacent chunks of length `size` in `arr` together into `aux`. If the last chunk ends after
the end of `arr` it is shortened so that it fits. No merging is performed if `size` is greater than or
equal to the size of `arr`. It should be the case that `arr.size = aux.size`.
-/
@[specialize, inline]
partial def mergeChunksIntoAuxPartial
    [Inhabited α]
    [Ord α]
    (arr aux : Array α)
    (size : ℕ) :=
  -- Merge every two adjacent chunks while the second chunk has at least one
  -- element.
  let rec @[specialize] loop (aux : Array α) (start₁: ℕ)
      : Array α :=
    if start₁ + size < arr.size then
      let start₂ := start₁ + size
      let end₂ := min (start₂ + size) arr.size
      let aux' := mergeAdjacentChunksIntoAuxPartial arr aux start₁ start₂ end₂
      loop aux' (start₁ + 2 * size)
    else
      -- Copy any leftover elements directly to `aux`.
      --
      -- This can happen, for example, when calling this function with
      --       `arr  := #[1, 2, 3, 10, 20, 30, 100, 200]`
      --   and `size := 3`,
      -- as the first loop with merge `#[1, 2, 3]` and `#[20, 30, 100]` together, but
      -- because there are too few leftover elements to form two adjacent chunks,
      -- it is unable to do any further merging. Thus, the leftover elements, `100`
      -- and `200`, must be directly copied over into `aux`.
      let rec @[specialize] loopFinal (aux : Array α) (start₁ : ℕ) : Array α :=
        if start₁ < aux.size then
          let aux' := aux.set! start₁ arr[start₁]!
          loopFinal aux' start₁.succ
        else
          aux
      loopFinal aux start₁
  loop aux 0

/--
An implementation of the 'mergesort' algorithm that only allocates one auxiliary array
and uses panic-based indexing.
-/
partial def Array.mergeSortPartial [Inhabited α] [Ord α] (arr : Array α) : Array α :=
  let rec @[specialize] loop
      (arr aux : Array α)
      (chunkSize : ℕ)
      : Array α :=
    if chunkSize < arr.size then
      let aux' := mergeChunksIntoAuxPartial arr aux chunkSize

      -- Note: `aux'` becomes `arr` and `arr` becomes `aux`.
      loop aux' arr (chunkSize * 2)
    else
      arr
  let aux : Array α := Array.mkArray arr.size default
  loop arr aux 1

-- All of the following should evaluate to 'true'. We can't use 'example' here to test these
-- more nicely because 'mergeSortPartial' is, well, partial.

#eval #[].mergeSortPartial (α := Nat) = #[]
#eval #[0].mergeSortPartial = #[0]
#eval #[0, 1].mergeSortPartial = #[0, 1]
#eval #[1, 0].mergeSortPartial = #[0, 1]
#eval #[0, 0].mergeSortPartial = #[0, 0]
#eval #[1, 1].mergeSortPartial = #[1, 1]
#eval #[0, 1, 2].mergeSortPartial = #[0, 1, 2]
#eval #[0, 2, 1].mergeSortPartial = #[0, 1, 2]
#eval #[1, 0, 2].mergeSortPartial = #[0, 1, 2]
#eval #[1, 2, 0].mergeSortPartial = #[0, 1, 2]
#eval #[2, 0, 1].mergeSortPartial = #[0, 1, 2]
#eval #[2, 1, 0].mergeSortPartial = #[0, 1, 2]
#eval #[0, 0, 0].mergeSortPartial = #[0, 0, 0]
#eval #[1, 1, 1].mergeSortPartial = #[1, 1, 1]
#eval #[2, 2, 2].mergeSortPartial = #[2, 2, 2]
#eval #[10, 9, 8, 7, 6, 5, 4, 3, 2, 1].mergeSortPartial = #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
#eval #[10, 0, 100, 1, 200, 2].mergeSortPartial = #[0, 1, 2, 10, 100, 200]

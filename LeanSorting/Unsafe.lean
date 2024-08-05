import Mathlib.Data.Nat.ModEq

@[specialize, inline]
def mergeAdjacentChunksIntoAuxUnsafe
    [Ord α]
    (arr aux : Array α)
    (start₁ start₂ end₂ : ℕ)
    : Array α :=
  let rec @[specialize] loop
      (aux : Array α)
      (i k₁ k₂ : ℕ)
      : Array α :=
    if k₁ < start₂ ∧ k₂ < end₂ then
      match Ord.compare (arr[k₁]'sorry) (arr[k₂]'sorry) with
      | .lt | .eq =>
        let aux' := aux.set ⟨i, sorry⟩ (arr[k₁]'sorry)
        loop aux' i.succ k₁.succ k₂
      | .gt =>
        let aux' := aux.set ⟨i, sorry⟩ (arr[k₂]'sorry)
        loop aux' i.succ k₁ k₂.succ
    else
      let rec @[specialize] loopLeft
          (aux : Array α)
          (i k₁ : ℕ)
          : Array α :=
        if k₁ < start₂ then
          let aux' := aux.set ⟨i, sorry⟩ (arr[k₁]'sorry)
          loopLeft aux' i.succ k₁.succ
        else
          let rec @[specialize] loopRight
              (aux : Array α)
              (i k₂ : ℕ)
              : Array α :=
            if k₂ < end₂ then
              let aux' := aux.set ⟨i, sorry⟩ (arr[k₂]'sorry)
              loopRight aux' i.succ k₂.succ
            else
              aux
          loopRight aux i k₂
      loopLeft aux i k₁
  termination_by arr.size - i
  decreasing_by all_goals sorry
  loop aux start₁ start₁ start₂

@[specialize, inline]
def mergeChunksIntoAuxUnsafe
    [Ord α]
    (arr aux : Array α)
    (size : ℕ) :=
  let rec @[specialize] loop (aux : Array α) (start₁: ℕ)
      : Array α :=
    if start₁ + size < arr.size then
      let start₂ := start₁ + size
      let end₂ := min (start₂ + size) arr.size
      let aux' := mergeAdjacentChunksIntoAuxUnsafe arr aux start₁ start₂ end₂
      loop aux' (start₁ + 2 * size)
    else
      let rec @[specialize] loopFinal (aux : Array α) (start₁ : ℕ) : Array α :=
        if start₁ < aux.size then
          let aux' := aux.set ⟨start₁, sorry⟩ (arr[start₁]'sorry)
          loopFinal aux' start₁.succ
        else
          aux
      loopFinal aux start₁
  termination_by arr.size - start₁
  decreasing_by sorry
  loop aux 0

@[specialize]
def Array.mergeSortUnsafe [Inhabited α] [Ord α] (arr : Array α) : Array α :=
  let rec @[specialize] loop
      (arr aux : Array α)
      (chunkSize : ℕ)
      : Array α :=
    if chunkSize < arr.size then
      let aux' := mergeChunksIntoAuxUnsafe arr aux chunkSize
      loop aux' arr (chunkSize * 2)
    else
      arr
  termination_by arr.size - chunkSize
  decreasing_by sorry
  let aux : Array α := Array.mkArray arr.size default
  loop arr aux 1

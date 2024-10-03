import Init.Data.Array.Basic

-- TODO: replace calls to Array.size.toUsize with Array.usize when lean 4.12.0 comes out
--       see: https://github.com/leanprover/lean4/commit/8f0631ab1f30cf0dbd64194967f7705d4821cf51

abbrev USize.succ (n : USize) := n + 1

@[specialize, inline]
partial def mergeAdjacentChunksIntoAuxPartialUSizeUnsafe
    [Ord α]
    (arr aux : Array α)
    (start₁ start₂ end₂ : USize)
    : Array α :=
  let rec @[specialize] loop
      (aux : Array α)
      (i k₁ k₂ : USize)
      : Array α :=
    if k₁ < start₂ ∧ k₂ < end₂ then
      match Ord.compare (arr[k₁]'sorry) (arr[k₂]'sorry) with
      | .lt | .eq =>
        let aux' := aux.uset i (arr[k₁]'sorry) sorry
        loop aux' i.succ k₁.succ k₂
      | .gt =>
        let aux' := aux.uset i (arr[k₂]'sorry) sorry
        loop aux' i.succ k₁ k₂.succ
    else
      let rec @[specialize] loopLeft
          (aux : Array α)
          (i k₁ : USize)
          : Array α :=
        if k₁ < start₂ then
          let aux' := aux.uset i (arr[k₁]'sorry) sorry
          loopLeft aux' i.succ k₁.succ
        else
          let rec @[specialize] loopRight
              (aux : Array α)
              (i k₂ : USize)
              : Array α :=
            if k₂ < end₂ then
              let aux' := aux.uset i (arr[k₂]'sorry) sorry
              loopRight aux' i.succ k₂.succ
            else
              aux
          loopRight aux i k₂
      loopLeft aux i k₁
  loop aux start₁ start₁ start₂

@[specialize, inline]
partial def mergeChunksIntoAuxPartialUSizeUnsafe
    [Ord α]
    (arr aux : Array α)
    (size : USize) :=
  let rec @[specialize] loop (aux : Array α) (start₁: USize)
      : Array α :=
    if start₁ + size < arr.size.toUSize then
      let start₂ := start₁ + size
      let end₂ := min (start₂ + size) arr.size.toUSize
      let aux' := mergeAdjacentChunksIntoAuxPartialUSizeUnsafe arr aux start₁ start₂ end₂
      loop aux' (start₁ + 2 * size)
    else
      let rec @[specialize] loopFinal (aux : Array α) (start₁ : USize) : Array α :=
        if start₁ < aux.size.toUSize then
          let aux' := aux.uset start₁ (arr[start₁]'sorry) sorry
          loopFinal aux' start₁.succ
        else
          aux
      loopFinal aux start₁
  loop aux 0

@[specialize]
partial def Array.mergeSortPartialUSizeUnsafe [Inhabited α] [Ord α] (arr : Array α) : Array α :=
  let rec @[specialize] loop
      (arr aux : Array α)
      (chunkSize : USize)
      : Array α :=
    if chunkSize < arr.size.toUSize then
      let aux' := mergeChunksIntoAuxPartialUSizeUnsafe arr aux chunkSize
      loop aux' arr (chunkSize * 2)
    else
      arr
  let aux : Array α := Array.mkArray arr.size default
  loop arr aux 1

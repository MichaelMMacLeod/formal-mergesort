import SortingBenchmark

variable
  {α : Type}
  {arr aux : Array α}
  {low mid high ptr₁ ptr₂ i chunkSize : USize}

abbrev USize.succ (n : USize) := n + 1

@[specialize, inline, simp]
partial def mergeAdjacentChunksIntoAux
    [Inhabited α]
    [Ord α]
    (arr aux : Array α)
    (low mid high : USize)
    : Array α :=
  let rec @[specialize] loop
      (aux : Array α)
      (ptr₁ ptr₂ i : USize)
      : Array α :=
    if ptr₁ < mid ∧ ptr₂ < high then
      match Ord.compare arr[ptr₁]! arr[ptr₂]! with
      | .lt | .eq =>
        let aux' := aux.set! i.toNat arr[ptr₁]!
        loop aux' ptr₁.succ ptr₂ i.succ
      | .gt =>
        let aux' := aux.set! i.toNat arr[ptr₂]!
        loop aux' ptr₁ ptr₂.succ i.succ
    else
      let rec @[specialize] loopLeft
          (aux : Array α)
          (ptr₁ i : USize)
          : Array α :=
        if ptr₁ < mid then
          let aux' := aux.set! i.toNat arr[ptr₁]!
          loopLeft aux' ptr₁.succ i.succ
        else
          let rec @[specialize] loopRight
              (aux : Array α)
              (ptr₂ i : USize)
              : Array α :=
            if ptr₂ < high then
              let aux' := aux.set! i.toNat arr[ptr₂]!
              loopRight aux' ptr₂.succ i.succ
            else
              aux
          loopRight aux ptr₂ i
      loopLeft aux ptr₁ i
  loop aux (ptr₁ := low) (ptr₂ := mid) (i := low)

@[specialize, inline, simp]
partial def mergeChunksIntoAux
    [Inhabited α]
    [Ord α]
    (arr aux : Array α)
    (chunkSize : USize) :=
  let rec @[specialize] loop
      (aux : Array α)
      (low : USize)
      : Array α :=
    if arr.usize - low > chunkSize then
      let mid := low + chunkSize
      let high := mid + min (arr.usize - mid) chunkSize
      let aux' := mergeAdjacentChunksIntoAux arr aux low mid high
      loop aux' high
    else
      let rec @[specialize] loopFinal (aux : Array α) (low : USize) : Array α :=
        if low < aux.usize then
          let aux' := aux.set! low.toNat arr[low]!
          loopFinal aux' low.succ
        else
          aux
      loopFinal aux low
  loop aux 0

@[specialize, inline, simp]
partial def Array.mergeSortWithAuxiliary
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
      loop aux' arr (chunkSize + min (arr.usize - chunkSize) chunkSize)
    else
      arr
  loop arr aux 1

@[specialize, inline, simp]
def Array.mergeSort [Inhabited α] [Ord α] (arr : Array α) : Array α :=
  mergeSortWithAuxiliary arr (aux := .replicate arr.size default) size_replicate

#eval #[].mergeSort (α := Nat) = #[]
#eval #[0].mergeSort = #[0]
#eval #[0, 1].mergeSort = #[0, 1]
#eval #[1, 0].mergeSort = #[0, 1]
#eval #[0, 0].mergeSort = #[0, 0]
#eval #[1, 1].mergeSort = #[1, 1]
#eval #[0, 1, 2].mergeSort = #[0, 1, 2]
#eval #[0, 2, 1].mergeSort = #[0, 1, 2]
#eval #[1, 0, 2].mergeSort = #[0, 1, 2]
#eval #[1, 2, 0].mergeSort = #[0, 1, 2]
#eval #[2, 0, 1].mergeSort = #[0, 1, 2]
#eval #[2, 1, 0].mergeSort = #[0, 1, 2]
#eval #[0, 0, 0].mergeSort = #[0, 0, 0]
#eval #[1, 1, 1].mergeSort = #[1, 1, 1]
#eval #[2, 2, 2].mergeSort = #[2, 2, 2]
#eval #[10, 9, 8, 7, 6, 5, 4, 3, 2, 1].mergeSort = #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
#eval #[10, 0, 100, 1, 200, 2].mergeSort = #[0, 1, 2, 10, 100, 200]

@[simp]
def Array.is_non_decreasing [Ord α] (arr : Array α) : Bool :=
  if h1 : arr.size = 0 then
    true
  else
    let rec @[simp] loop (last_x : α) (i : Nat) : Bool :=
      if h2 : i < arr.size then
        let x := arr[i]
        match Ord.compare last_x x with
        | .lt | .eq =>
          loop x i.succ
        | .gt =>
          false
      else
        true
    loop arr[0] 0

-- Testing is_non_decreasing; should be true
#eval #[].is_non_decreasing (α := Nat)
#eval #[0].is_non_decreasing
#eval #[0, 0].is_non_decreasing
#eval #[0, 1].is_non_decreasing
#eval #[0, 1, 10, 100].is_non_decreasing

-- Testing is_non_decreasing; should be false
#eval #[1, 0].is_non_decreasing
#eval #[0, 1, 10, 5].is_non_decreasing

#eval (Array.randomWithStdGen (seed := 0) (size := 10)).mergeSort.is_non_decreasing
#eval (Array.randomWithStdGen (seed := 1) (size := 10)).mergeSort.is_non_decreasing
#eval (Array.randomWithStdGen (seed := 2) (size := 10)).mergeSort.is_non_decreasing
#eval (Array.randomWithStdGen (seed := 3) (size := 10)).mergeSort.is_non_decreasing
#eval (Array.randomWithStdGen (seed := 4) (size := 10)).mergeSort.is_non_decreasing
#eval (Array.randomWithStdGen (seed := 5) (size := 10)).mergeSort.is_non_decreasing
#eval (Array.randomWithStdGen (seed := 6) (size := 10)).mergeSort.is_non_decreasing
#eval (Array.randomWithStdGen (seed := 7) (size := 10)).mergeSort.is_non_decreasing
#eval (Array.randomWithStdGen (seed := 8) (size := 10)).mergeSort.is_non_decreasing
#eval (Array.randomWithStdGen (seed := 9) (size := 10)).mergeSort.is_non_decreasing

#eval (Array.randomWithStdGen (seed := 10) (size := 0)).mergeSort.is_non_decreasing
#eval (Array.randomWithStdGen (seed := 11) (size := 1)).mergeSort.is_non_decreasing
#eval (Array.randomWithStdGen (seed := 12) (size := 2)).mergeSort.is_non_decreasing
#eval (Array.randomWithStdGen (seed := 13) (size := 3)).mergeSort.is_non_decreasing
#eval (Array.randomWithStdGen (seed := 14) (size := 4)).mergeSort.is_non_decreasing
#eval (Array.randomWithStdGen (seed := 15) (size := 5)).mergeSort.is_non_decreasing
#eval (Array.randomWithStdGen (seed := 16) (size := 6)).mergeSort.is_non_decreasing
#eval (Array.randomWithStdGen (seed := 17) (size := 7)).mergeSort.is_non_decreasing
#eval (Array.randomWithStdGen (seed := 18) (size := 8)).mergeSort.is_non_decreasing
#eval (Array.randomWithStdGen (seed := 19) (size := 9)).mergeSort.is_non_decreasing

#eval Array.randomWithStdGen (seed := 0) (size := 100)

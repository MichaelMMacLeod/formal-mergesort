def Array.randomWithGen
    {γ}
    (seed : γ)
    (generate : γ → Nat × γ)
    (size : Nat)
    : Array Nat :=
  let rec loop (arr : Array Nat) (i : Nat) (seed : γ) : Array Nat :=
    if i_lt_arr_size : i < arr.size then
      let (n, seed) := generate seed
      let idx : Fin arr.size := ⟨i, i_lt_arr_size⟩
      loop (arr.set idx n) i.succ seed
    else
      arr
  let arr := .replicate size default
  loop arr 0 seed

def Array.randomWithStdGen (size : Nat) (seed : Nat := 0) : Array Nat :=
  .randomWithGen (mkStdGen seed) stdNext size

def Array.randomWithDuplicates
    (size : Nat)
    (seed : Nat := 0)
    (numberOfDistinctNats : Nat)
    [NeZero numberOfDistinctNats]
    : Array Nat :=
  let distinctNats : Array Nat := .range numberOfDistinctNats
  .randomWithGen
    (seed := mkStdGen seed)
    (generate := fun seed =>
      let (n, seed) := stdNext seed
      have : n % distinctNats.size < distinctNats.size := by
        rw [Array.size_range]
        exact Nat.mod_lt n (Nat.pos_of_neZero numberOfDistinctNats)
      let result := distinctNats[n % distinctNats.size]
      (result, seed))
    size

def Array.mostlyAscending
    (size : Nat)
    (seed : Nat := 0)
    (numberOfSwaps : Nat := size / 2)
    (maxSwapDistance : Nat := Nat.log2 size)
    : Array Nat :=
  makeSwaps (.range size) (mkStdGen seed) numberOfSwaps
where
  swap (arr : Array Nat) (left : Nat) (right : Nat) : Array Nat :=
    if h : left < arr.size ∧ right < arr.size then
      arr.swap left right
    else
      arr
  makeSwaps (arr : Array Nat) (gen : StdGen) : Nat → Array Nat
    | 0 => arr
    | numberOfRemainingSwaps + 1 =>
      let (left, gen) := stdNext gen
      let left := left % arr.size
      let (distance, gen) := stdNext gen
      let distance := distance % maxSwapDistance
      let right := left + min distance (arr.size - left)
      let arr := swap arr left right
      makeSwaps arr gen numberOfRemainingSwaps

#eval Array.mostlyAscending 5

inductive Benchmark.Kind
  | Ascending
  | Descending
  | Random
  | RandomManyDuplicates
  | AscendingThenRandom

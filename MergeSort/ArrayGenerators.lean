/--
Helper utility for generating `Array Nat` values using a custom random generator.
-/
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

/--
Returns an `Array` of random `Nat` values selected from the list
`[0, 1, 2, ..., numberOfDistinctNats - 1]`. Useful for creating arrays with many duplicate elements.
-/
def Array.randomWithDuplicates
    (size : Nat)
    (seed : Nat := 0)
    (numberOfDistinctNats : Nat := 1 + Nat.log2 size)
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

/--
Returns an `Array` of `Nat` values that are mostly in ascending order.

Returns the `Array` `[0, 1, 2, ..., size - 1]`, except that exactly `numberOfSwaps` two-element
swaps are made, where the distance between every two swap indices is no more than `maxSwapDistance`.
-/
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
      let distance := distance % (maxSwapDistance + 1)
      let right := (left + distance) % size
      let (left, right) := if left < right then (left, right) else (right, left)
      let arr := swap arr left right
      makeSwaps arr gen numberOfRemainingSwaps

/--
Returns a randomly shuffled `Array` containing the values `[0, 1, 2, ..., size - 1]`.
-/
def Array.random (size : Nat) (seed : Nat := 0) : Array Nat :=
  Array.mostlyAscending size seed size size

/--
Returns the `Array` `[0, 1, 2, ..., size - 1]`.
-/
def Array.ascending (size : Nat) : Array Nat := .range size

/--
Returns the `Array` `[size - 1, size - 2, size - 3, ..., 0]`.
-/
def Array.descending (size : Nat) : Array Nat := .ofFn (n := size) fun v => size - v - 1

/--
Returns the `Array` `[0, 1, 2, .., size - 1]`, except that the last several values are randomly shuffled.
The number of random values is given as a percentage of the overall size as `tailPercent`.
-/
def Array.ascendingWithRandomTail
    (size : Nat)
    (seed : Nat := 0)
    (tailPercent : Float := 0.10)
    : Array Nat :=
  let tailPercent := if tailPercent.isNaN ∨ tailPercent.isInf then 0 else tailPercent
  let tailPercent := max 0 (min 1 tailPercent)
  let tailCount : Nat := size.toFloat * tailPercent |>.toUSize.toNat
  let initialCount := size - tailCount
  let initial := Array.ascending initialCount
  let tail := Array.random tailCount seed |>.map (· + initialCount)
  initial ++ tail

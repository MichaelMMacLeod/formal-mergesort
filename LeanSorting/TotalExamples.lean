import «LeanSorting».Total

example : #[].mergeSort (α := Nat) = #[] := by rfl
example : #[0].mergeSort = #[0] := by rfl
example : #[0, 1].mergeSort = #[0, 1] := by rfl
example : #[1, 0].mergeSort = #[0, 1] := by rfl
example : #[0, 0].mergeSort = #[0, 0] := by rfl
example : #[1, 1].mergeSort = #[1, 1] := by rfl
example : #[0, 1, 2].mergeSort = #[0, 1, 2] := by rfl
example : #[0, 2, 1].mergeSort = #[0, 1, 2] := by rfl
example : #[1, 0, 2].mergeSort = #[0, 1, 2] := by rfl
example : #[1, 2, 0].mergeSort = #[0, 1, 2] := by rfl
example : #[2, 0, 1].mergeSort = #[0, 1, 2] := by rfl
example : #[2, 1, 0].mergeSort = #[0, 1, 2] := by rfl
example : #[0, 0, 0].mergeSort = #[0, 0, 0] := by rfl
example : #[1, 1, 1].mergeSort = #[1, 1, 1] := by rfl
example : #[2, 2, 2].mergeSort = #[2, 2, 2] := by rfl
example : #[10, 9, 8, 7, 6, 5, 4, 3, 2, 1].mergeSort = #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10] := by rfl
example : #[10, 0, 100, 1, 200, 2].mergeSort = #[0, 1, 2, 10, 100, 200] := by rfl

def Array.random (seed : ℕ) (size : ℕ) : Array ℕ :=
  let rec loop (arr : Array ℕ) (i : ℕ) (gen : StdGen) : Array ℕ :=
    if i_lt_arr_size : i < arr.size then
      let (n, gen) := stdNext gen
      loop
        (arr.set ⟨i, i_lt_arr_size⟩ n)
        i.succ
        gen
    else
      arr
  loop
    (Array.mkArray size default)
    0
    (mkStdGen seed)

def Array.is_non_decreasing [Ord α] (arr : Array α) : Bool :=
  if h1 : arr.size = 0 then
    true
  else
    let rec loop (last_x : α) (i : ℕ) : Bool :=
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

example : #[].is_non_decreasing (α := ℕ) = true := by rfl
example : #[0].is_non_decreasing = true := by rfl
example : #[0, 0].is_non_decreasing = true := by rfl
example : #[0, 1].is_non_decreasing = true := by rfl
example : #[0, 1, 10, 100].is_non_decreasing = true := by rfl

example : #[1, 0].is_non_decreasing = false := by rfl
example : #[0, 1, 10, 5].is_non_decreasing = false := by rfl

-- Generate a bunch of random arrays and check that the result of 'mergeSort' is in sorted order.
-- For some reason these take a long time to evaluate. Sizes larger than 10 are very slow. There's
-- got to be a way around this limitation...

example : (Array.random (seed := 0) (size := 10)).mergeSort.is_non_decreasing = true := by rfl
example : (Array.random (seed := 1) (size := 10)).mergeSort.is_non_decreasing = true := by rfl
example : (Array.random (seed := 2) (size := 10)).mergeSort.is_non_decreasing = true := by rfl
example : (Array.random (seed := 3) (size := 10)).mergeSort.is_non_decreasing = true := by rfl
example : (Array.random (seed := 4) (size := 10)).mergeSort.is_non_decreasing = true := by rfl
example : (Array.random (seed := 5) (size := 10)).mergeSort.is_non_decreasing = true := by rfl
example : (Array.random (seed := 6) (size := 10)).mergeSort.is_non_decreasing = true := by rfl
example : (Array.random (seed := 7) (size := 10)).mergeSort.is_non_decreasing = true := by rfl
example : (Array.random (seed := 8) (size := 10)).mergeSort.is_non_decreasing = true := by rfl
example : (Array.random (seed := 9) (size := 10)).mergeSort.is_non_decreasing = true := by rfl

example : (Array.random (seed := 10) (size := 0)).mergeSort.is_non_decreasing = true := by rfl
example : (Array.random (seed := 11) (size := 1)).mergeSort.is_non_decreasing = true := by rfl
example : (Array.random (seed := 12) (size := 2)).mergeSort.is_non_decreasing = true := by rfl
example : (Array.random (seed := 13) (size := 3)).mergeSort.is_non_decreasing = true := by rfl
example : (Array.random (seed := 14) (size := 4)).mergeSort.is_non_decreasing = true := by rfl
example : (Array.random (seed := 15) (size := 5)).mergeSort.is_non_decreasing = true := by rfl
example : (Array.random (seed := 16) (size := 6)).mergeSort.is_non_decreasing = true := by rfl
example : (Array.random (seed := 17) (size := 7)).mergeSort.is_non_decreasing = true := by rfl
example : (Array.random (seed := 18) (size := 8)).mergeSort.is_non_decreasing = true := by rfl
example : (Array.random (seed := 19) (size := 9)).mergeSort.is_non_decreasing = true := by rfl

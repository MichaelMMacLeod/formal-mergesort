import Mathlib.Data.Bool.Basic
import Mathlib.Data.Nat.ModEq

theorem Nat.lt_of_lt_le {a b c : ℕ} (h : a < b) : b ≤ c → a < c := by
  omega
theorem Nat.lt_of_le_lt {a b c : ℕ} (h : a ≤ b) : b < c → a < c := by
  omega
theorem Nat.succ_ge_of_ge {a b : ℕ} (h : a ≥ b) : a.succ ≥ b := by
  omega
theorem Nat.succ_eq_succ_of_self {a b : ℕ} (h : a = b) : a.succ = b.succ := by
  simp[*]
theorem idk2 {p a : Prop} {h : p} (h_imp : p → a) : a :=
  by simp[*]
theorem idk3 {k₁ k₂ start₂ end₂ : ℕ} {h : ¬(k₁ < start₂ ∧ k₂ < end₂)}
    : (¬(k₁ < start₂)) ∨ (¬(k₂ < end₂)) := by
  omega
set_option diagnostics true
/--
Merges two ordered contiguous portions of `arr` into `aux`, returning `aux`.
If there are no other references to `aux`, it will be mutated in-place.

For example,
```
                        chunk1     chunk2
arr: 1 2 3 100 200 300 [10 20 30 │ 21 22 23] 400 500 600
aux: 1 2 3 100 200 300 [0  0  0  │ 0  0  0 ] 0   0   0    ; before merge
---> 1 2 3 100 200 300 [10 20 21 │ 22 23 30] 0   0   0    ; after merge
                        │          │         │
start1 ─────────────────┘          │         │
start2 ────────────────────────────┘         │
end2 ────────────────────────────────────────┘
```
-/
def mergeAdjacentChunksIntoAux [Ord α] (arr : Array α) (aux : Array α)
    (start₁ : ℕ) (start₂ : ℕ) (end₂ : ℕ)
    (start₁_lt_start₂ : start₁ < start₂)
    (start₂_lt_end₂ : start₂ < end₂)
    (end₂_le_arr_size : end₂ ≤ arr.size)
    (arr_size_eq_aux_size : arr.size = aux.size)
    : Array α :=
  -- Copy from both the left and right chunk (in sorted order) until one of the chunks
  -- is fully copied.
  let rec loop (aux : Array α) (i : ℕ) (k₁ : ℕ) (k₂ : ℕ)
      (arr_size_eq_aux_size : arr.size = aux.size)
      (i_def : i = k₁ + k₂ - start₂)
      (k₂_ge_start₂ : k₂ ≥ start₂)
      (k₁_lt_start₂_succ : k₁ < start₂.succ)
      (k₂_lt_end₂_succ : k₂ < end₂.succ)
      (k₂_lt_end₂_of_not_k₁_lt_start₂ : ¬k₁ < start₂ → k₂ < end₂)
      : Array α :=
    if k₁_k₂_in_bounds : k₁ < start₂ ∧ k₂ < end₂ then
      have k₁_lt_arr_size : k₁ < arr.size := by
        apply And.left at k₁_k₂_in_bounds
        let start₂_lt_arr_size := Nat.lt_of_lt_le start₂_lt_end₂ end₂_le_arr_size
        exact (Nat.lt_trans k₁_k₂_in_bounds start₂_lt_arr_size)
      have k₂_lt_arr_size : k₂ < arr.size := by
        apply And.right at k₁_k₂_in_bounds
        exact (Nat.lt_of_lt_le k₁_k₂_in_bounds end₂_le_arr_size)
      have i_lt_aux_size : i < aux.size := by
        omega
      match Ord.compare arr[k₁] arr[k₂] with
      | .lt | .eq =>
        let aux' := aux.set ⟨i, i_lt_aux_size⟩ arr[k₁]
        have arr_size_eq_aux'_size : arr.size = aux'.size := by
          have aux'_def : aux' = aux.set ⟨i, i_lt_aux_size⟩ arr[k₁] := by rfl
          rw [aux'_def, Array.size_set]
          exact arr_size_eq_aux_size
        have i_succ_def : i.succ = k₁.succ + k₂ - start₂ := by
          omega
        have k₁_succ_lt_start₂_succ : k₁.succ < start₂.succ := by omega
        have k₂_lt_end₂_of_not_k₁_succ_lt_start₂ : ¬k₁.succ < start₂ → k₂ < end₂ := by omega
        loop aux' i.succ k₁.succ k₂
          arr_size_eq_aux'_size
          i_succ_def
          k₂_ge_start₂
          k₁_succ_lt_start₂_succ
          k₂_lt_end₂_succ
          k₂_lt_end₂_of_not_k₁_succ_lt_start₂
      | .gt =>
        let aux' := aux.set ⟨i, i_lt_aux_size⟩ arr[k₂]
        have arr_size_eq_aux'_size : arr.size = aux'.size := by
          have aux'_def : aux' = aux.set ⟨i, i_lt_aux_size⟩ arr[k₂] := by rfl
          rw [aux'_def, Array.size_set]
          exact arr_size_eq_aux_size
        have i_succ_def : i.succ = k₁ + k₂.succ - start₂ := by omega
        have k₂_succ_ge_start₂ : k₂.succ ≥ start₂ := by omega
        have k₂_succ_lt_end₂_succ : k₂.succ < end₂.succ := by omega
        have k₂_lt_end₂_of_not_k₁_lt_start₂ : ¬k₁ < start₂ → k₂.succ < end₂ := by omega
        loop aux' i.succ k₁ k₂.succ
          arr_size_eq_aux'_size
          i_succ_def
          k₂_succ_ge_start₂
          k₁_lt_start₂_succ
          k₂_succ_lt_end₂_succ
          k₂_lt_end₂_of_not_k₁_lt_start₂
    else
      if k₁_lt_start₂ : k₁ < start₂ then
        -- Copy what remains of the left chunk (the right chunk has been fully copied).
        have : k₁ < arr.size := by omega
        have i_lt_aux_size : i < aux.size := by omega
        let aux' := aux.set ⟨i, i_lt_aux_size⟩ arr[k₁]
        have arr_size_eq_aux'_size : arr.size = aux'.size := by
          have aux'_def : aux' = aux.set ⟨i, i_lt_aux_size⟩ arr[k₁] := by rfl
          rw [aux'_def, Array.size_set]
          exact arr_size_eq_aux_size
        have i_succ_def : i.succ = k₁.succ + k₂ - start₂ := by omega
        let rec loop_left (aux : Array α) (i : ℕ) (k₁ : ℕ)
            (arr_size_eq_aux_size : arr.size = aux.size)
            (i_def : i = k₁ + k₂ - start₂)
            : Array α :=
          if k₁_lt_start₂ : k₁ < start₂ then
            have : k₁ < arr.size := by omega
            have : k₂ = end₂ := by omega
            have i_lt_aux_size : i < aux.size := by omega
            let aux' := aux.set ⟨i, i_lt_aux_size⟩ arr[k₁]
            have arr_size_eq_aux'_size : arr.size = aux'.size := by
              have aux'_def : aux' = aux.set ⟨i, i_lt_aux_size⟩ arr[k₁] := by rfl
              rw [aux'_def, Array.size_set]
              exact arr_size_eq_aux_size
            have i_succ_def : i.succ = k₁.succ + k₂ - start₂ := by omega
            loop_left aux' i.succ k₁.succ
              arr_size_eq_aux'_size
              i_succ_def
          else
            aux
        termination_by aux.size - k₁
        loop_left aux' i.succ k₁.succ
          arr_size_eq_aux'_size
          i_succ_def
      else
        -- Copy what remains of the right chunk (the left chunk has been fully copied).
        have : k₂ < arr.size := by omega
        have i_lt_aux_size : i < aux.size := by omega
        let aux' := aux.set ⟨i, i_lt_aux_size⟩ arr[k₂]
        have arr_size_eq_aux'_size : arr.size = aux'.size := by
          have aux'_def : aux' = aux.set ⟨i, i_lt_aux_size⟩ arr[k₂] := by rfl
          rw [aux'_def, Array.size_set]
          exact arr_size_eq_aux_size
        have i_succ_def : i.succ = k₁ + k₂.succ - start₂ := by omega
        let rec loop_right (aux : Array α) (i : ℕ) (k₂ : ℕ)
            (arr_size_eq_aux_size : arr.size = aux.size)
            (i_def : i = k₁ + k₂ - start₂)
            : Array α :=
          if k₂_lt_end₂ : k₂ < end₂ then
            have : k₂ < arr.size := by omega
            have i_lt_aux_size : i < aux.size := by omega
            let aux' := aux.set ⟨i, i_lt_aux_size⟩ arr[k₂]
            have arr_size_eq_aux'_size : arr.size = aux'.size := by
              have aux'_def : aux' = aux.set ⟨i, i_lt_aux_size⟩ arr[k₂] := by rfl
              rw [aux'_def, Array.size_set]
              exact arr_size_eq_aux_size
            have i_succ_def : i.succ = k₁ + k₂.succ - start₂ := by omega
            loop_right aux' i.succ k₂.succ
              arr_size_eq_aux'_size
              i_succ_def
          else
            aux
        termination_by aux.size - k₂
        loop_right aux' i.succ k₂.succ
          arr_size_eq_aux'_size
          i_succ_def
  termination_by aux.size - i
  loop aux start₁ start₁ start₂
    arr_size_eq_aux_size
    (Nat.eq_sub_of_add_eq rfl)
    (Nat.le_refl start₂)
    (Nat.lt_succ_of_lt start₁_lt_start₂)
    (Nat.lt_succ_of_lt start₂_lt_end₂)
    (fun a ↦ start₂_lt_end₂)

-- theorem mergeAdjacentChunksIntoAux_loop_size_eq
--     [Ord α]
--     (arr : Array α) (aux : Array α) (i : ℕ) (k₁ : ℕ) (k₂ : ℕ)
--     (start₁_lt_stat₂ : i < k₁)
--     (k₁_lt_k₂ : k₁ < k₂)
--     (k₂_le_arr_size : k₂ ≤ arr.size)
--     (arr_size_eq_aux_size : arr.size = aux.size)
--     (i_def : i = k₁ + k₂ - start₂)
--     (k₂_ge_start₂ : k₂ ≥ start₂)
--     (k₁_lt_start₂_succ : k₁ < start₂.succ)
--     (k₂_lt_end₂_succ : k₂ < end₂.succ)
--     (k₂_lt_end₂_of_not_k₁_lt_start₂ : ¬k₁ < start₂ → k₂ < end₂)
--     : (mergeAdjacentChunksIntoAux.loop
--         arr aux i k₁ k₂
--         start₁_lt_stat₂
--         k₁_lt_k₂
--         k₂_le_arr_size
--         arr_size_eq_aux_size
--         ).size = aux.size := by
--   sorry

#check mergeAdjacentChunksIntoAux.loop.induct 

theorem mergeAdjacentChunksIntoAux_size_eq [Ord α] (arr : Array α) (aux : Array α)
    (start₁ : ℕ) (start₂ : ℕ) (end₂ : ℕ)
    (start₁_lt_start₂ : start₁ < start₂)
    (start₂_lt_end₂ : start₂ < end₂)
    (end₂_le_arr_size : end₂ ≤ arr.size)
    (arr_size_eq_aux_size : arr.size = aux.size)
    : (mergeAdjacentChunksIntoAux arr aux start₁ start₂ end₂
        start₁_lt_start₂
        start₂_lt_end₂
        end₂_le_arr_size
        arr_size_eq_aux_size).size = aux.size := by
  unfold mergeAdjacentChunksIntoAux
  unfold mergeAdjacentChunksIntoAux.loop
  split
  next k₁_k₂_in_bounds =>
    simp []
    split
    induction aux, start₁, start₂, end₂,  using mergeAdjacentChunksIntoAux.loop.induct with
    | case1 => sorry
    | case2 => sorry
    | case3 => sorry
    | case4 => sorry
    | case5 => sorry
    -- have ih := (mergeAdjacentChunksIntoAux.loop arr aux start₁ start₂ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).size = aux.size
    sorry
  next k₁_k₁_out_of_bounds =>
    sorry
  -- simp? only [mergeAdjacentChunksIntoAux.loop]
  -- simp [*]

  -- induction (end₂ - start₂) with
  -- | zero =>
  --   rw [mergeAdjacentChunksIntoAux.loop]
  --   simp [*]

  --   split
  --   . case zero.h_1 =>
  --     sorry
  --   . case zero.h_2 =>
  --     sorry
  --   . case zero.h_3 =>
  --     sorry
  -- | succ n8 =>
  --   sorry
  -- -- rw [mergeAdjacentChunksIntoAux.loop]
  -- -- simp []
  -- -- split
  -- -- . case isTrue =>
  -- --   simp []
  -- --   split
  -- --   . case h_1 =>
  -- --     sorry
  -- --   . case h_2 =>
  -- --     sorry
  -- --   . case h_3 =>
  -- --     sorry
  -- -- . case isFalse =>
  -- --   simp []
  -- --   rw [mergeAdjacentChunksIntoAux.loop.loop_left]
  -- --   simp []
  -- --   split
  -- --   . case isTrue =>
  -- --     sorry
  -- --   . case isFalse =>
  -- --     rw [Array.size_set]

-- Sorts every two adjacent chunks in `arr` of length `size` into `aux`.
def mergeChunksIntoAux [Inhabited α] [Ord α] (arr : Array α) (aux : Array α) (size : ℕ)
    (arr_size_eq_aux_size : arr.size = aux.size)
    (size_gt_0 : size > 0)
    : Array α := Id.run do
  let mut aux := aux
  let mut start₁ := 0
  let rec loop₁ (aux : Array α) (start₁ : ℕ)
      (arr_size_eq_aux_size : arr.size = aux.size)
      : Array α :=
    if start₁ + size < arr.size then
      let start₂ := start₁ + size
      let end₂ := min (start₂ + size) arr.size
      have start₁_lt_start₂ : start₁ < start₂ := by omega
      have start₂_lt_end₂ : start₂ < end₂ := by omega
      have end₂_le_arr_size : end₂ ≤ arr.size := by omega
      let aux' := mergeAdjacentChunksIntoAux
                   arr aux start₁ start₂ end₂
                   start₁_lt_start₂
                   start₂_lt_end₂
                   end₂_le_arr_size
                   arr_size_eq_aux_size
      let start₁' := start₁ + 2 * size
      have arr_size_eq_aux'_size : arr.size = aux'.size := by
        apply mergeAdjacentChunksIntoAux_size_eq at aux'

        -- have aux'_def : aux' =
      loop₁ aux' start₁'
        arr_size_eq_aux'_size
    else
      let rec loop₂ (aux : Array α) (start₁ : ℕ)
          : Array α :=
        if start₁ < arr.size then
          have : start₁ < arr.size := by omega
          have chunkStart₁_lt_aux_size : start₁ < aux.size := by omega
          let aux' := aux.set ⟨start₁, chunkStart₁_lt_aux_size⟩ arr[start₁]
          let start₁' := start₁ + 1
          loop₂ aux' start₁'
        else
          aux
      loop₂ aux start₁
  loop₁ aux start₁
    arr_size_eq_aux_size

@[specialize] def Array.mergeSort [Inhabited α] [Ord α] (arr : Array α) : Array α := Id.run do
  let mut arr := arr
  let mut aux : Array α := Array.mkArray arr.size default
  let mut chunkSize := 1
  let mut auxIsAux := true
  while chunkSize < arr.size do
    if auxIsAux then
      aux := mergeChunksIntoAux arr aux chunkSize
    else
      arr := mergeChunksIntoAux aux arr chunkSize
    chunkSize := chunkSize * 2
    auxIsAux := !auxIsAux
  if auxIsAux then
    pure arr
  else
    pure aux

-- #eval mergeChunksIntoAux #[3, 2, 1] #[0, 0, 0] 1
-- #eval #[15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1].mergeSort

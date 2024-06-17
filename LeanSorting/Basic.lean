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

/--
Merges two ordered contiguous portions of `arr` into `aux`, returning `aux`.
If there are no other references to `aux`, it will be mutated in-place.

For example,
```
                        region1    region2
arr: 1 2 3 100 200 300 [10 20 30 │ 21 22 23] 400 500 600
aux: 1 2 3 100 200 300 [0  0  0  │ 0  0  0 ] 0   0   0
---> 1 2 3 100 200 300 [10 20 21 │ 22 23 30] 0   0   0
                        │          │         │
chunkStart1 ────────────┘          │         │
chunkStart2 ───────────────────────┘         │
end2 ────────────────────────────────────────┘
```
-/
partial def mergeAdjacentChunksIntoAux [Inhabited α] [Ord α] (arr : Array α) (aux : Array α)
    (chunkStart₁ : ℕ) (chunkStart₂ : ℕ) (chunkEnd₂ : ℕ)
    (start₁_lt_start₂ : chunkStart₁ < chunkStart₂)
    (start₂_lt_end₂ : chunkStart₂ < chunkEnd₂)
    (end₂_lt_arr_size : chunkEnd₂ < arr.size)
    (arr_size_eq_aux_size : arr.size = aux.size)
    : Array α :=
  -- Copy from both the left and right chunk until one of the chunks is fully copied.
  let rec loop (aux : Array α) (i : ℕ) (k₁ : ℕ) (k₂ : ℕ)
      (k₁_ge_chunkStart₁ : k₁ ≥ chunkStart₁)
      (arr_size_eq_aux_size : arr.size = aux.size)
      (i_in_single_chunk :
        Xor' (i ≥ chunkStart₁ ∧ i < chunkStart₂)
             (i ≥ chunkStart₂ ∧ i < chunkEnd₂))
      : Array α :=
    if k₁_k₂_in_bounds : k₁ < chunkStart₂ ∧ k₂ < chunkEnd₂ then

      -- Without the following two proofs, the proofs required for arr[k₁] and arr[k₂] are
      -- automatically inferred (via `omega`?), which for whatever reason messes with the
      -- reference counter for `aux`, resulting in a full copy when we do `aux.set`.
      have k₁_lt_arr_size : k₁ < arr.size := by
        apply And.left at k₁_k₂_in_bounds
        let start₂_lt_arr_size := Nat.lt_trans start₂_lt_end₂ end₂_lt_arr_size
        exact (Nat.lt_trans k₁_k₂_in_bounds start₂_lt_arr_size)
      have k₂_st_arr_size : k₂ < arr.size := by
        apply And.right at k₁_k₂_in_bounds
        exact (Nat.lt_trans k₁_k₂_in_bounds end₂_lt_arr_size)

      have i_lt_aux_size : i < aux.size := by
        rw [Xor'] at i_in_single_chunk
        omega

      match Ord.compare arr[k₁] arr[k₂] with
      | .lt | .eq =>
        let aux' := (dbgTraceIfShared "mergeChunks1" aux).set ⟨i, i_lt_aux_size⟩ arr[k₁]
        have arr_size_eq_aux'_size : arr.size = aux'.size := by
          have aux'_def : aux' = aux.set ⟨i, i_lt_aux_size⟩ arr[k₁] := by rfl
          rw [aux'_def]
          rw [Array.size_set]
          exact arr_size_eq_aux_size
        have k₁_succ_ge_chunkStart₁ : k₁.succ ≥ chunkStart₁ := by
          exact (Nat.succ_ge_of_ge k₁_ge_chunkStart₁)
        have i_in_single_chunk' :
            Xor' (i.succ ≥ chunkStart₁ ∧ i.succ < chunkStart₂)
                 (i.succ ≥ chunkStart₂ ∧ i.succ < chunkEnd₂) := by
          rw [Xor'] at i_in_single_chunk
          rw [Xor']

        loop aux' i.succ k₁.succ k₂
          k₁_succ_ge_chunkStart₁
          arr_size_eq_aux'_size
          i_in_single_chunk'
      | .gt =>
        let aux' := (dbgTraceIfShared "mergeChunks2" aux).set ⟨i, i_lt_aux_size⟩ arr[k₂]
        have arr_size_eq_aux'_size : arr.size = aux'.size := by
          have aux'_def : aux' = aux.set ⟨i, i_lt_aux_size⟩ arr[k₂] := by rfl
          rw [aux'_def]
          rw [Array.size_set]
          exact arr_size_eq_aux_size
        have i_in_single_chunk' :
            Xor' (i.succ ≥ chunkStart₁ ∧ i.succ < chunkStart₂)
                 (i.succ ≥ chunkStart₂ ∧ i.succ < chunkEnd₂) :=
          sorry
        loop aux' i.succ k₁ k₂.succ
          k₁_ge_chunkStart₁
          arr_size_eq_aux'_size
          i_in_single_chunk'
    else
      -- Finish copying everything from the left chunk (if there was anything left to copy).
      let rec loop₁ (aux : Array α) (i : ℕ) (k₁ : ℕ) :=
        if k₁ < chunkStart₂ then
          have i_lt_aux_size : i < aux.size := sorry
          have k₁_lt_arr_size : k₁ < arr.size := sorry
          let aux' := (dbgTraceIfShared "mergeChunks" aux).set ⟨i, i_lt_aux_size⟩ arr[k₁]
          loop₁ aux' i.succ k₁.succ
        else
          -- Finish copying everything from the right chunk (if there was anything left to copy).
          let rec loop₂ (aux : Array α) (i : ℕ) (k₂ : ℕ) :=
            if k₂ < chunkEnd₂ then
              have i_lt_aux_size : i < aux.size := sorry
              have k₂_lt_arr_size : k₂ < arr.size := sorry
              let aux' := (dbgTraceIfShared "mergeChunks" aux).set ⟨i, i_lt_aux_size⟩ arr[k₂]
              loop₂ aux' i.succ k₂.succ
            else
              aux
          loop₂ aux i k₂
      loop₁ aux i k₁
  loop aux chunkStart₁ chunkStart₁ chunkStart₂
    (by simp [*])
    arr_size_eq_aux_size
    (by simp [*])

-- def mergeAdjacentChunksIntoAux2
      -- have k₁_lt_arr_size : k₁ < arr.size := by
      --   -- apply And.left at k₁_k₂_in_bounds
      --   -- have h3 := Nat.lt_trans start₂_lt_end₂ end₂_lt_arr_size
      --   omega
      -- have k₂_lt_arr_size : k₂ < arr.size := sorry

--[Inhabited α] [Ord α] (arr : Array α) (aux : Array α)
--     (chunkStart₁ : ℕ) (chunkStart₂ : ℕ) (chunkEnd₂ : ℕ) : Array α := Id.run do
--   let mut i := chunkStart₁
--   let mut aux := aux
--   let mut k₁ := chunkStart₁
--   let mut k₂ := chunkStart₂
--   while k₁ < chunkStart₂ ∧ k₂ < chunkEnd₂ do
--     match Ord.compare arr[k₁]! arr[k₂]! with
--     | .lt | .eq =>
--       aux := (dbgTraceIfShared "mergeChunks" aux).set! i arr[k₁]!
--       k₁ := k₁ + 1
--     | .gt =>
--       aux := (dbgTraceIfShared "mergeChunks" aux).set! i arr[k₂]!
--       k₂ := k₂ + 1
--     i := i + 1
--   while k₁ < chunkStart₂ do
--     aux := (dbgTraceIfShared "mergeChunks" aux).set! i arr[k₁]!
--     k₁ := k₁ + 1
--     i := i + 1
--   while k₂ < chunkEnd₂ do
--     aux := (dbgTraceIfShared "mergeChunks" aux).set! i arr[k₂]!
--     k₂ := k₂ + 1
--     i := i + 1
--   while i < aux.size do
--     aux := (dbgTraceIfShared "mergeChunks" aux).set! i arr[i]!
--     i := i + 1
--   pure aux

def mergeChunksIntoAux [Inhabited α] [Ord α] (arr : Array α) (aux : Array α)
    (chunkSize : ℕ) : Array α := Id.run do
  let mut aux := aux
  let mut chunkStart₁ := 0
  while chunkStart₁ + chunkSize < arr.size do
    let chunkStart₂ := chunkStart₁ + chunkSize
    let chunkEnd₂ := min (chunkStart₂ + chunkSize) arr.size
    aux := mergeAdjacentChunksIntoAux
                arr aux chunkStart₁ chunkStart₂ chunkEnd₂
                (by sorry) (by sorry) (by sorry) (by sorry)
    chunkStart₁ := chunkStart₁ + 2 * chunkSize

  pure aux

def Array.overwrite_with (dest : Array α) (src : Array α) (hp : src.size = dest.size) : Array α :=
  let rec loop (i : ℕ) (dest : Array α) (ih : src.size = dest.size) :=
    if h : i < dest.size then
      let dest' := dest.set ⟨i, h⟩ src[i]
      have ih' : src.size = dest'.size := by
        let h1 := Array.size_set dest ⟨i, h⟩ src[i]
        let h2 : dest.set ⟨i, h⟩ src[i] = dest' := by rfl
        rw [h2] at h1
        rw [h1]
        exact ih
      loop (i + 1) dest' ih'
    else
      dest
  loop 0 dest hp

def Array.mergeSort [Inhabited α] [Ord α] (arr : Array α) : Array α := Id.run do
  let mut arr := arr
  let mut aux : Array α := Array.ofFn (n := arr.size) (fun _ => default)
  let mut chunkSize := 1
  while chunkSize < arr.size do
    aux := mergeChunksIntoAux arr aux chunkSize
    have h : aux.size = arr.size := by sorry
    arr := arr.overwrite_with aux h
    chunkSize := chunkSize * 2
  pure arr

#eval mergeChunksIntoAux #[3, 2, 1] #[0, 0, 0] 1
#eval #[3, 2, 1].mergeSort

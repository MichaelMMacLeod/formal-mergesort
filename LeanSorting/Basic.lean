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
theorem idk1 {k₁ k₂ start₂ end₂ : ℕ} {h : k₁ < start₂}
    : (Xor' (k₁ < start₂ ∧ k₂ = end₂) (k₂ < end₂ ∧ k₁ = start₂))
    → (k₁ < start₂ ∧ k₂ = end₂) := by sorry
theorem idk2 {p a : Prop} {h : p} (h_imp : p → a) : a :=
  by simp[*]
theorem idk3 {k₁ k₂ start₂ end₂ : ℕ} {h : ¬(k₁ < start₂ ∧ k₂ < end₂)}
    : (¬(k₁ < start₂)) ∨ (¬(k₂ < end₂)) := by
  omega

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
start1 ─────────────────┘          │         │
start2 ────────────────────────────┘         │
end2 ────────────────────────────────────────┘
```
-/
partial def mergeAdjacentChunksIntoAux [Inhabited α] [Ord α] (arr : Array α) (aux : Array α)
    (start₁ : ℕ) (start₂ : ℕ) (end₂ : ℕ)
    (start₁_lt_start₂ : start₁ < start₂)
    (start₂_lt_end₂ : start₂ < end₂)
    (end₂_le_arr_size : end₂ ≤ arr.size)
    (arr_size_eq_aux_size : arr.size = aux.size)
    : Array α :=
  -- Copy from both the left and right chunk until one of the chunks is fully copied.
  let rec loop (aux : Array α) (i : ℕ) (k₁ : ℕ) (k₂ : ℕ)
      (arr_size_eq_aux_size : arr.size = aux.size)
      (i_def : i = k₁ + k₂ - start₂)
      (k₂_ge_start₂ : k₂ ≥ start₂)
      (k₁_lt_start₂_succ : k₁ < start₂.succ)
      (k₂_lt_end₂_succ : k₂ < end₂.succ)
      : Array α :=
    if k₁_k₂_in_bounds : k₁ < start₂ ∧ k₂ < end₂ then
      -- Without the following two proofs, the proofs required for arr[k₁] and arr[k₂] are
      -- automatically inferred (via `omega`?), which for whatever reason messes with the
      -- reference counter for `aux`, resulting in a full copy when we do `aux.set`.
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
        let aux' := (dbgTraceIfShared "mergeChunks1" aux).set ⟨i, i_lt_aux_size⟩ arr[k₁]
        have arr_size_eq_aux'_size : arr.size = aux'.size := by
          have aux'_def : aux' = aux.set ⟨i, i_lt_aux_size⟩ arr[k₁] := by rfl
          rw [aux'_def, Array.size_set]
          exact arr_size_eq_aux_size
        have i_succ_def : i.succ = k₁.succ + k₂ - start₂ := by
          omega
        have k₁_succ_lt_start₂_succ : k₁.succ < start₂.succ := by omega
        loop aux' i.succ k₁.succ k₂
          arr_size_eq_aux'_size
          i_succ_def
          k₂_ge_start₂
          k₁_succ_lt_start₂_succ
          k₂_lt_end₂_succ
      | .gt =>
        let aux' := (dbgTraceIfShared "mergeChunks2" aux).set ⟨i, i_lt_aux_size⟩ arr[k₂]
        have arr_size_eq_aux'_size : arr.size = aux'.size := by
          have aux'_def : aux' = aux.set ⟨i, i_lt_aux_size⟩ arr[k₂] := by rfl
          rw [aux'_def, Array.size_set]
          exact arr_size_eq_aux_size
        have i_succ_def : i.succ = k₁ + k₂.succ - start₂ := by omega
        have k₂_succ_ge_start₂ : k₂.succ ≥ start₂ := by omega
        have k₂_succ_lt_end₂_succ : k₂.succ < end₂.succ := by omega
        loop aux' i.succ k₁ k₂.succ
          arr_size_eq_aux'_size
          i_succ_def
          k₂_succ_ge_start₂
          k₁_lt_start₂_succ
          k₂_succ_lt_end₂_succ
    else
      have : ¬k₁ < start₂ → k₂ < end₂ := by sorry
      if k₁_lt_start₂ : k₁ < start₂ then
        have i_lt_aux_size : i < aux.size := by omega
        let aux' := (dbgTraceIfShared "mergeChunks" aux).set ⟨i, i_lt_aux_size⟩ arr[k₁]
        have arr_size_eq_aux'_size : arr.size = aux'.size := by
          have aux'_def : aux' = aux.set ⟨i, i_lt_aux_size⟩ arr[k₁] := by rfl
          rw [aux'_def, Array.size_set]
          exact arr_size_eq_aux_size
        have i_succ_def : i.succ = k₁.succ + k₂ - start₂ := by omega
        let rec loop₁ (aux : Array α) (i : ℕ) (k₁ : ℕ)
            (arr_size_eq_aux_size : arr.size = aux.size)
            (i_def : i = k₁ + k₂ - start₂)
            : Array α :=
          if k₁_lt_start₂ : k₁ < start₂ then
            have : k₂ = end₂ := by omega
            have i_lt_aux_size : i < aux.size := by omega
            let aux' := (dbgTraceIfShared "mergeChunks" aux).set ⟨i, i_lt_aux_size⟩ arr[k₁]
            have arr_size_eq_aux'_size : arr.size = aux'.size := by
              have aux'_def : aux' = aux.set ⟨i, i_lt_aux_size⟩ arr[k₁] := by rfl
              rw [aux'_def, Array.size_set]
              exact arr_size_eq_aux_size
            have i_succ_def : i.succ = k₁.succ + k₂ - start₂ := by omega
            loop₁ aux' i.succ k₁.succ
              arr_size_eq_aux'_size
              i_succ_def
          else
            aux
        loop₁ aux' i.succ k₁.succ
          arr_size_eq_aux'_size
          i_succ_def
      else
        have i_lt_aux_size : i < aux.size := by omega
        let aux' := (dbgTraceIfShared "mergeChunks" aux).set ⟨i, i_lt_aux_size⟩ arr[k₂]
        have arr_size_eq_aux'_size : arr.size = aux'.size := by
          have aux'_def : aux' = aux.set ⟨i, i_lt_aux_size⟩ arr[k₂] := by rfl
          rw [aux'_def, Array.size_set]
          exact arr_size_eq_aux_size
        have i_succ_def : i.succ = k₁ + k₂.succ - start₂ := by omega
        let rec loop₂ (aux : Array α) (i : ℕ) (k₂ : ℕ)
            (arr_size_eq_aux_size : arr.size = aux.size)
            (i_def : i = k₁ + k₂ - start₂)
            : Array α :=
          if k₂_lt_end₂ : k₂ < end₂ then
            have i_lt_aux_size : i < aux.size := by omega
            let aux' := (dbgTraceIfShared "mergeChunks" aux).set ⟨i, i_lt_aux_size⟩ arr[k₂]
            have arr_size_eq_aux'_size : arr.size = aux'.size := by
              have aux'_def : aux' = aux.set ⟨i, i_lt_aux_size⟩ arr[k₂] := by rfl
              rw [aux'_def, Array.size_set]
              exact arr_size_eq_aux_size
            have i_succ_def : i.succ = k₁ + k₂.succ - start₂ := by omega
            loop₂ aux' i.succ k₂.succ
              arr_size_eq_aux'_size
              i_succ_def
          else
            aux
        loop₂ aux' i.succ k₂.succ
          arr_size_eq_aux'_size
          i_succ_def
  loop aux start₁ start₁ start₂
    (by omega)
    (by omega)
    (by omega)
    (by omega)
    (by omega)

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
  while chunkStart₁ < arr.size do
    aux := (dbgTraceIfShared "mergeChunksIntoAux" aux).set! chunkStart₁ arr[chunkStart₁]!
    chunkStart₁ := chunkStart₁ + 1
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
#eval #[8, 7, 6, 5, 4, 3, 2, 1].mergeSort

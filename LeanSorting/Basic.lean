import Mathlib.Data.Bool.Basic
import Mathlib.Data.Nat.ModEq

theorem Nat.lt_of_lt_le {a b c : ℕ} (h : a < b) : b ≤ c → a < c := by
  omega
theorem Nat.lt_of_le_lt {a b c : ℕ} (h : a ≤ b) : b < c → a < c := by
  omega

-- theorem idk3 {a b c : ℕ} (h : a < b)

partial def mergeAdjacentChunksIntoAux [Inhabited α] [Ord α] (arr : Array α) (aux : Array α)
    (chunkStart₁ : ℕ) (chunkStart₂ : ℕ) (chunkEnd₂ : ℕ)
    (start₁_lt_start₂ : chunkStart₁ < chunkStart₂)
    (start₂_lt_end₂ : chunkStart₂ < chunkEnd₂)
    (end₂_lt_arr_size : chunkEnd₂ < arr.size)
    (arr_size_eq_aux_size : arr.size = aux.size)
    : Array α :=
  let rec loop (aux : Array α) (i : ℕ) (k₁ : ℕ) (k₂ : ℕ)
      --(k₁_ge_chunkStart₁ : k₁ ≥ chunkStart₁)
      --(chunkEnd₂_leq_aux_size : chunkEnd₂ ≤ aux.size)
      : Array α :=
    if k₁_k₂_in_bounds : k₁ < chunkStart₂ ∧ k₂ < chunkEnd₂ then
      have htmp1 : k₁ < arr.size := sorry
      have htmp2 : k₂ < arr.size := sorry
      have i_le_k₂ : i ≤ k₂ := sorry
      have i_lt_aux_size : i < aux.size := sorry -- by
        -- apply And.right at k₁_k₂_in_bounds
        -- have k₂_lt_aux_size := Nat.lt_of_lt_le k₁_k₂_in_bounds chunkEnd₂_leq_aux_size
        -- exact (Nat.lt_of_le_lt i_le_k₂ k₂_lt_aux_size)
      match Ord.compare arr[k₁] arr[k₂] with
      | .lt | .eq =>
        -- let aux' := (dbgTraceIfShared "mergeChunks1" aux).set ⟨i, i_lt_aux_size⟩ arr[k₁]
        -- have k₁_succ_ge_chunkStart₁ : k₁.succ ≥ chunkStart₁ := sorry
        -- have chunkEnd₂_leq_aux'_size : chunkEnd₂ ≤ aux'.size := sorry
        -- loop aux' i.succ k₁.succ k₂ k₁_succ_ge_chunkStart₁ chunkEnd₂_leq_aux'_size
        loop ((dbgTraceIfShared "mergeChunks1" aux).set ⟨i, i_lt_aux_size⟩ arr[k₁]) i.succ k₁.succ k₂ -- sorry sorry
      | .gt =>
        -- let aux' := (dbgTraceIfShared "mergeChunks2" aux).set ⟨i, i_lt_aux_size⟩ arr[k₂]
        -- have chunkEnd₂_leq_aux'_size : chunkEnd₂ ≤ aux'.size := sorry
        -- loop aux' i.succ k₁ k₂.succ k₁_ge_chunkStart₁ chunkEnd₂_leq_aux'_size
        loop ((dbgTraceIfShared "mergeChunks2" aux).set ⟨i, i_lt_aux_size⟩ arr[k₂]) i.succ k₁ k₂.succ -- sorry sorry
    else
      let rec loop₁ (aux : Array α) (i : ℕ) (k₁ : ℕ) :=
        if k₁ < chunkStart₂ then
          have i_lt_aux_size : i < aux.size := sorry
          have k₁_lt_arr_size : k₁ < arr.size := sorry
          let aux' := (dbgTraceIfShared "mergeChunks" aux).set ⟨i, i_lt_aux_size⟩ arr[k₁]
          loop₁ aux' i.succ k₁.succ
        else
          let rec loop₂ (aux : Array α) (i : ℕ) (k₂ : ℕ) :=
            if k₂ < chunkEnd₂ then
              have i_lt_aux_size : i < aux.size := sorry
              have k₂_lt_arr_size : k₂ < arr.size := sorry
              let aux' := (dbgTraceIfShared "mergeChunks" aux).set ⟨i, i_lt_aux_size⟩ arr[k₂]
              loop₂ aux' i.succ k₂.succ
            else
              let rec loop₃ (aux : Array α) (i : ℕ) :=
                if i < aux.size then
                  have i_lt_aux_size : i < aux.size := sorry
                  have i_lt_arr_size : i < arr.size := sorry
                  let aux' := (dbgTraceIfShared "mergeChunks" aux).set ⟨i, i_lt_aux_size⟩ arr[i]
                  loop₃ aux' i.succ
                else
                  aux
              loop₃ aux i
          loop₂ aux i k₂
      loop₁ aux i k₁
  loop aux chunkStart₁ chunkStart₁ chunkStart₂ -- sorry sorry -- (by simp [*]) (by omega)

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
                (by sorry)
                (by sorry)
                (by sorry)
                (by sorry)
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

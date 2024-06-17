import Mathlib.Data.Bool.Basic
import Mathlib.Data.Nat.ModEq

def mergeAdjacentChunksIntoAux [Inhabited α] [Ord α] (arr : Array α) (aux : Array α)
    (chunkStart₁ : ℕ) (chunkStart₂ : ℕ) (chunkEnd₂ : ℕ) : Array α := Id.run do
  let mut i := chunkStart₁
  let mut aux := aux
  let mut k₁ := chunkStart₁
  let mut k₂ := chunkStart₂
  while k₁ < chunkStart₂ ∧ k₂ < chunkEnd₂ do
    match Ord.compare arr[k₁]! arr[k₂]! with
    | .lt | .eq =>
      aux := (dbgTraceIfShared "mergeChunks" aux).set! i arr[k₁]!
      k₁ := k₁ + 1
    | .gt =>
      aux := (dbgTraceIfShared "mergeChunks" aux).set! i arr[k₂]!
      k₂ := k₂ + 1
    i := i + 1
  while k₁ < chunkStart₂ do
    aux := (dbgTraceIfShared "mergeChunks" aux).set! i arr[k₁]!
    k₁ := k₁ + 1
    i := i + 1
  while k₂ < chunkEnd₂ do
    aux := (dbgTraceIfShared "mergeChunks" aux).set! i arr[k₂]!
    k₂ := k₂ + 1
    i := i + 1
  while i < aux.size do
    aux := (dbgTraceIfShared "mergeChunks" aux).set! i arr[i]!
    i := i + 1
  pure aux

def mergeChunksIntoAux [Inhabited α] [Ord α] (arr : Array α) (aux : Array α)
    (chunkSize : ℕ) : Array α := Id.run do
  let mut aux := aux
  let mut chunkStart₁ := 0
  while chunkStart₁ + chunkSize < arr.size do
    let chunkStart₂ := chunkStart₁ + chunkSize
    let chunkEnd₂ := min (chunkStart₂ + chunkSize) arr.size
    aux := mergeAdjacentChunksIntoAux arr aux chunkStart₁ chunkStart₂ chunkEnd₂
    chunkStart₁ := chunkStart₁ + 2 * chunkSize
  pure aux

def Array.copy (dest : Array α) (src : Array α) (hp : src.size = dest.size) : Array α :=
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

def mergeSort [Inhabited α] [Ord α] (arr : Array α) : Array α := Id.run do
  let mut arr := arr
  let mut aux : Array α := Array.ofFn (n := arr.size) (fun _ => default)
  let mut chunkSize := 1
  while chunkSize < arr.size do
    aux := mergeChunksIntoAux arr aux chunkSize
    have h : aux.size = arr.size := by sorry
    arr := arr.copy aux h
    chunkSize := chunkSize * 2
  pure arr

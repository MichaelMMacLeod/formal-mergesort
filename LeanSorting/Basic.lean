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

def mergeSort [Inhabited α] [Ord α] (arr : Array α) : Array α := Id.run do
  let mut arr := arr
  let mut aux : Array α := Array.ofFn (n := arr.size) (fun _ => default)
  let mut chunkSize := 1
  while chunkSize < arr.size do
    arr := mergeChunksIntoAux arr aux chunkSize
    chunkSize := chunkSize * 2
  pure arr

-- def Array.partitionIdx (as : Array α) (n : Fin as.size.succ) : Array α × Array α := Id.run do
--   let mut left := #[]
--   let mut right := #[]
--   let mut i := 0
--   while h : i < as.size ∧ i ≠ n do
--     left := left.push as[i]
--     i := i + 1
--   while h : i < as.size do
--     right := right.push as[i]
--     i := i + 1
--   (left, right)

-- theorem Array.partitionIdx_left_size_lt {as : Array α} {n : Fin as.size.succ} :
--     (as.partitionIdx n).1.size < as.size := by
--     simp [Array.partitionIdx, Id.run]
--     sorry

-- def mergeRuns [Ord α] (left : Array α) (right : Array α) : Array α := Id.run do
--   let mut iLeft := 0
--   let mut iRight := 0
--   let mut result := #[]
--   while h : iLeft < left.size ∧ iRight < right.size do
--     match Ord.compare left[iLeft] right[iRight] with
--       | .lt | .eq => do
--         result := result.push left[iLeft]
--         iLeft := iLeft + 1
--       | .gt => do
--         result := result.push right[iRight]
--         iRight := iRight + 1
--   for h : i in [iLeft:left.size] do
--     result := result.push left[i]
--   for h : i in [iRight:right.size] do
--     result := result.push right[i]
--   result

-- partial def mergeSort [Ord α] (arr : Array α) : Array α :=
--   if arr.size ≤ 1 then
--     arr
--   else
--     let idx := Fin.mk (arr.size / 2) (by omega)
--     let (left, right) := arr.partitionIdx idx
--     mergeRuns (mergeSort left) (mergeSort right)

-- structure Cut (n : ℕ) where
--   start₁ : ℕ
--   start₂ : ℕ
--   end₂ : ℕ
--   start₁_lt_start₂ : start₁ < start₂
--   start₂_lt_end₂ : start₂ < end₂
--   end₂_lt_n : end₂ < n

-- def Cut.start₂_lt_n {n : ℕ} {c : Cut n} : c.start₂ < n :=
--   Nat.lt_trans c.start₂_lt_end₂ c.end₂_lt_n

-- def Cut.start₁_lt_n {n : ℕ} {c : Cut n} : c.start₁ < n :=
--   Nat.lt_trans c.start₁_lt_start₂ c.start₂_lt_n

-- structure MergeMemory (α : Type) where
--   primary : Array α
--   auxiliary : Array α
--   primary_size_eq_auxiliary_size := primary.size = auxiliary.size
-- def MergeMemory.size (m : MergeMemory α) : ℕ := m.primary.size

-- theorem MergeMemory.size_eq_primary_size {m : MergeMemory α} : m.size = m.primary.size := by
--   rw [MergeMemory.size]

-- theorem MergeMemory.size_eq_auxiliary_size {m : MergeMemory α} : m.size = m.auxiliary.size := by
--   have h : m.primary.size = m.auxiliary.size := m.primary_size_eq_auxiliary_size
--   simp [MergeMemory.size, *]

-- def sortCutIntoAuxLoop
--     [Ord α]
--     (primary : Array α)
--     (auxiliary : Array α)
--     (cut : Cut primary.size)
--     (primary_size_eq_auxiliary_size : primary.size = auxiliary.size)
--     (i : ℕ)
--     (i₁ : ℕ)
--     (i₂ : ℕ)
--     : Array α :=
--   if h : i₁ < cut.start₂ ∧ i₂ < cut.end₂ then
--     match Ord.compare primary[i₁] primary[i₂] with
--     | .lt | .eq =>
--       let auxiliary' := auxiliary.set! i primary[i₁]
--       let i' := i + 1
--       let i₁' := i₁ + 1
--       have primary_size_eq_auxiliary_size' : primary.size = auxiliary'.size := by
--         sorry
--       have th : auxiliary.size = auxiliary'.size := by
--         sorry
--       -- have th : i' - auxiliary.size < i - auxiliary.size := by
--       --   _
--       sortCutIntoAuxLoop primary auxiliary' cut primary_size_eq_auxiliary_size' i' i₁' i₂
--     | .gt =>
--       let auxiliary' := auxiliary.set! i primary[i₂]
--       let i' := i + 1
--       let i₂' := i₂ + 1
--       have primary_size_eq_auxiliary_size' : primary.size = auxiliary'.size := by
--         sorry
--       sortCutIntoAuxLoop primary auxiliary' cut primary_size_eq_auxiliary_size' i' i₁ i₂'
--   else
--     auxiliary

-- def sortCutIntoAux3
--     [Ord α]
--     {primary auxiliary : Array α}
--     (primary_size_eq_auxiliary_size : primary.size = auxiliary.size)
--     (cut : Cut primary.size) :
--     Array α :=
--   let rec loop : Array α × ℕ × ℕ × ℕ → Array α
--     | (auxiliary, i, i₁, i₂) =>
--       if h : i₁ < cut.start₂ ∧ i₂ < cut.end₂ then
--         match Ord.compare primary[i₁] primary[i₂] with
--         | .lt | .eq =>
--           let auxiliary' := auxiliary.set! i primary[i₁]
--           let i' := i + 1
--           let i₁' := i₁ + 1
--           loop (auxiliary', i', i₁', i₂)
--         | .gt =>
--           let auxiliary' := auxiliary.set! i primary[i₂]
--           let i' := i + 1
--           let i₂' := i₂ + 1
--           loop (auxiliary', i', i₁, i₂')
--       else
--         auxiliary
--   termination_by
--   loop (auxiliary, cut.start₁, cut.start₁, cut.start₂)
  -- let mut auxiliary := auxiliary
  -- let mut i := cut.start₁
  -- let mut i₁ := cut.start₁
  -- let mut i₂ := cut.start₂
  -- while h : i₁ < cut.start₂ ∧ i₂ < cut.end₂ do
  --   have i₁_lt_primary_size : i₁ < primary.size := by
  --     apply And.left at h
  --     have h2 := Nat.lt_trans h cut.start₂_lt_n
  --     exact h2
  --   have i₁_lt_auxiliary_size : i₁ < auxiliary.size := by
  --     apply And.left at h
  --     have h2 := Nat.lt_trans h cut.start₂_lt_n
  --     rw [primary_size_eq_auxiliary_size] at h2

  --     -- have h2 := Nat.lt_trans h cut.start₂_lt_n
  --     -- rw [m.size_eq_auxiliary_size] at h2
  --     -- -- have h3 : m.auxiliary.size = auxiliary.size := by

  --     -- exact h2
  --   -- have i₂_lt_primary_size : i₂ < primary.size := by
  --   --   sorry
  --   -- have i₂_lt_auxiliary_size : i₂ < auxiliary.size := by
  --   --   sorry
  --   -- have i_lt_auxiliary_size : i < auxiliary.size := by
  --   --   sorry
  --   let k : Fin auxiliary.size := ⟨i, i_lt_auxiliary_size⟩
  --   match Ord.compare primary[i₁] primary[i₂] with
  --   | .lt | .eq =>
  --     auxiliary := auxiliary.set k auxiliary[i₁]
  --     i₁ := i₁ + 1
  --   | .gt =>
  --     auxiliary := auxiliary.set k auxiliary[i₂]
  --     i₂ := i₂ + 1
  --   i := i + 1
  -- pure auxiliary

-- def sortCutIntoAux2 [Ord α] {primary auxiliary : Array α}
--     (primary_size_eq_auxiliary_size : primary.size = auxiliary.size) (cut : Cut primary.size) :
--     Array α := Id.run do
--   let mut auxiliary := auxiliary
--   let mut i := cut.start₁
--   let mut i₁ := cut.start₁
--   let mut i₂ := cut.start₂
--   while h : i₁ < cut.start₂ ∧ i₂ < cut.end₂ do
--     have i₁_lt_primary_size : i₁ < primary.size := by
--       apply And.left at h
--       have h2 := Nat.lt_trans h cut.start₂_lt_n
--       exact h2
--     have i₁_lt_auxiliary_size : i₁ < auxiliary.size := by
--       apply And.left at h
--       have h2 := Nat.lt_trans h cut.start₂_lt_n
--       rw [primary_size_eq_auxiliary_size] at h2

--       -- have h2 := Nat.lt_trans h cut.start₂_lt_n
--       -- rw [m.size_eq_auxiliary_size] at h2
--       -- -- have h3 : m.auxiliary.size = auxiliary.size := by

--       -- exact h2
--     -- have i₂_lt_primary_size : i₂ < primary.size := by
--     --   sorry
--     -- have i₂_lt_auxiliary_size : i₂ < auxiliary.size := by
--     --   sorry
--     -- have i_lt_auxiliary_size : i < auxiliary.size := by
--     --   sorry
--     let k : Fin auxiliary.size := ⟨i, i_lt_auxiliary_size⟩
--     match Ord.compare primary[i₁] primary[i₂] with
--     | .lt | .eq =>
--       auxiliary := auxiliary.set k auxiliary[i₁]
--       i₁ := i₁ + 1
--     | .gt =>
--       auxiliary := auxiliary.set k auxiliary[i₂]
--       i₂ := i₂ + 1
--     i := i + 1
--   pure auxiliary

-- def sortCutIntoAux [Ord α] {m : MergeMemory α} (cut : Cut m.size) :
--     MergeMemory α := Id.run do
--   let primary := m.primary
--   let mut auxiliary := m.auxiliary
--   let mut i := cut.start₁
--   let mut i₁ := cut.start₁
--   let mut i₂ := cut.start₂
--   while h : i₁ < cut.start₂ ∧ i₂ < cut.end₂ do
--     have i₁_lt_primary_size : i₁ < primary.size := by
--       apply And.left at h
--       have h2 := Nat.lt_trans h cut.start₂_lt_n
--       rw [m.size_eq_primary_size] at h2
--       exact h2
--     have i₁_lt_auxiliary_size : i₁ < auxiliary.size := by
--       apply And.left at h
--       have h2 := Nat.lt_trans h cut.start₂_lt_n
--       rw [m.size_eq_auxiliary_size] at h2
--       -- have h3 : m.auxiliary.size = auxiliary.size := by

--       exact h2
--     have i₂_lt_primary_size : i₂ < primary.size := by
--       sorry
--     have i₂_lt_auxiliary_size : i₂ < auxiliary.size := by
--       sorry
--     have i_lt_auxiliary_size : i < auxiliary.size := by
--       sorry
--     let k : Fin auxiliary.size := ⟨i, i_lt_auxiliary_size⟩
--     match Ord.compare primary[i₁] primary[i₂] with
--     | .lt | .eq =>
--       auxiliary := auxiliary.set k auxiliary[i₁]
--       i₁ := i₁ + 1
--     | .gt =>
--       auxiliary := auxiliary.set k auxiliary[i₂]
--       i₂ := i₂ + 1
--     i := i + 1
--   pure { m with auxiliary }
-- def experiment1 [Inhabited α] (arr : Array α) (n : Fin arr.size): Array α := Id.run do
--   let mut arr := arr
--   arr := (dbgTraceIfShared "1" arr).set n default
--   pure arr

-- def experiment2 [Inhabited α] (arr : Array α) (n : Fin arr.size): Array α :=
--   (dbgTraceIfShared "2" arr).set n default

-- def experiment3 [Inhabited α] (arr : Array α) (n : ℕ): Array α :=
--   (dbgTraceIfShared "3" arr).set! n default




-- def mergeAdjacentChunksIntoAux2 [Inhabited α] [Ord α] (arr : Array α) (aux : Array α)
--     (chunkStart₁ : ℕ) (chunkStart₂ : ℕ) (chunkEnd₂ : ℕ) : Array α := Id.run do
--   let mut i := chunkStart₁
--   let mut aux := aux
--   let mut k₁ := chunkStart₁
--   let mut k₂ := chunkStart₂
--   while k₁ < chunkStart₂ ∧ k₂ < chunkEnd₂ do
--     have k₁_lt_arr_size : k₁ < arr.size := sorry
--     have k₂_lt_arr_size : k₂ < arr.size := sorry
--     let iFin := ⟨i, sorry⟩
--     match Ord.compare arr[k₁] arr[k₂] with
--     | .lt | .eq =>
--       aux := (dbgTraceIfShared "mergeChunks" aux).set iFin arr[k₁]
--       k₁ := k₁ + 1
--     | .gt =>
--       aux := (dbgTraceIfShared "mergeChunks" aux).set iFin arr[k₂]
--       k₂ := k₂ + 1
--     i := i + 1
--   while k₁ < chunkStart₂ do
--     have k₁_lt_arr_size : k₁ < arr.size := sorry
--     have k₂_lt_arr_size : k₂ < arr.size := sorry
--     let iFin := ⟨i, sorry⟩
--     aux := (dbgTraceIfShared "mergeChunks" aux).set iFin arr[k₁]
--     k₁ := k₁ + 1
--     i := i + 1
--   while k₂ < chunkEnd₂ do
--     have k₁_lt_arr_size : k₁ < arr.size := sorry
--     have k₂_lt_arr_size : k₂ < arr.size := sorry
--     let iFin := ⟨i, sorry⟩
--     aux := (dbgTraceIfShared "mergeChunks" aux).set iFin arr[k₂]
--     k₂ := k₂ + 1
--     i := i + 1
--   while i < aux.size do
--     have i_lt_arr_size : i < arr.size := sorry
--     let iFin := ⟨i, sorry⟩
--     aux := (dbgTraceIfShared "mergeChunks" aux).set iFin arr[i]
--     i := i + 1
--   pure aux

-- #eval mergeChunksIntoAux #[1, 2, 3] #[0, 0, 0] 1
-- def size := 10
-- #eval mergeSort2 (Array.ofFn (n := size) (λ x => size - x)).reverse
-- #eval experiment1 #[0, 1, 2] ⟨1, by decide⟩
-- #eval experiment2 #[0, 1, 2] ⟨1, by decide⟩
-- #eval experiment3 #[7, 2, 5] 1

-- #eval mergeAdjacentChunksIntoAux #[5, 4, 3, 2, 1] #[0, 0, 0, 0, 0] 0 1 2
-- #eval mergeAdjacentChunksIntoAux #[5, 4, 3, 2, 1] #[4, 5, 0, 0, 0] 2 3 4
-- #eval mergeAdjacentChunksIntoAux #[5, 4, 3, 2, 1] #[4, 5, 2, 3, 0] 4 5 5
-- #eval mergeChunksIntoAux #[5, 4, 3, 2, 1] #[0, 0, 0, 0, 0] 1

-- #eval mergeAdjacentChunksIntoAux #[1, 3, 7, 4, 5, 6] #[0, 0, 0, 0, 0, 0] 0 3 6
-- #eval mergeAdjacentChunksIntoAux #[2, 1, 4, 3, 5, 6] #[0, 0, 0, 0, 0, 0] 5
-- #eval mergeChunksIntoAux #[2, 1] #[0, 0] 1
-- #eval mergeChunksIntoAux #[1, 3, 5, 2, 4, 8] #[0, 0, 0, 0, 0, 0] 1
-- -- #eval mergeChunksIntoAux #[2, 1, 4, 3, 5, 6] #[0, 0, 0, 0, 0, 0] 1
-- #eval mergeAdjacentChunksIntoAux #[1, 2, 3, 4, 5] #[0, 0, 0, 0, 0] 0 2 4
-- #eval mergeAdjacentChunksIntoAux #[1, 2, 3, 4, 5] #[1, 2, 3, 4, 0] 4 6 5
-- #eval mergeChunksIntoAux #[1, 2, 3, 4, 5] #[0, 0, 0, 0, 0] 1

-- #eval #[3, 2, 1].partitionIdx 2
-- #eval mergeRuns #[1, 2, 3] #[4, 5, 6]
-- def size : Nat := 100
-- #eval mergeSort (Array.ofFn (n := size) (λ n => size - n))

-- structure Slice (srcSize : Nat) where
--   start₁ : Nat
--   start₂ : Nat
--   size₂ : Nat
--   start1_lt_start2 : start₁ < start₂
--   start2_plus_size2_lt_size : start₂ + size₂ ≤ srcSize
--   size_gt_0 : size₂ > 0
-- deriving Repr

-- def Slice.end₁ (s : Slice n) : Nat :=
--   s.start₂

-- def Slice.end₂ (s : Slice n) : Nat :=
--   s.start₂ + s.size₂

-- theorem Nat.lt_of_add_left_lt {a b c : Nat} : a + b < c → a < c := by
--   intro h
--   induction b with
--   | zero =>
--     rw [Nat.add_zero] at h
--     exact h
--   | succ n ih =>
--     rw [Nat.add_one, Nat.add_succ] at h
--     exact ih (Nat.lt_of_succ_lt h)

-- theorem start₂_lt_srcSize (slice : Slice n) : slice.start₂ < n :=
--   -- Nat.lt_of_add_left_lt slice.start2_plus_size2_lt_size
--   sorry

-- theorem lt_srcSize_of_lt_end₁ (slice : Slice n) (i : Nat) : i < slice.end₁ → i < n := by
--   intro h
--   rewrite [Slice.end₁] at h
--   sorry

-- theorem lt_srcSize_of_lt_end₂ (slice : Slice n) (i : Nat) : i < slice.end₂ → i < n := by
--   -- intro h
--   -- have h2 := slice.start2_plus_size2_lt_size
--   -- rw [← Slice.end₂] at h2
--   -- exact (Nat.lt_trans h h2)
--   sorry

-- structure MergeMemory (α : Type) where
--   primary : Array α
--   auxiliary : Array α
--   primary_size_eq_auxiliary_size : primary.size = auxiliary.size
-- deriving Repr

-- def mkMergeMem {α : Type} [Inhabited α] (primary : Array α) : MergeMemory α :=
--   let auxiliary : Array α := Array.ofFn (n := primary.size) (fun _ => default)
--   { primary,
--     auxiliary,
--     primary_size_eq_auxiliary_size := by rw [Array.size_ofFn]
--   }

-- -- def merge : [Ord α] (m : MergeMem α)

-- -- def merge [Ord α] (aux : Array α) (arr : Array α) (h : aux.size == arr.size)
-- --     (slice : Slice arr.size) : Array α := Id.run do
-- --   let mut aux := aux
-- --   let mut i₁ := slice.start₁
-- --   let mut i₂ := slice.start₂
-- --   let mut ai := slice.start₁
-- --   while h : i₁ < slice.end₁ && i₂ < slice.end₂ do
-- --     have : i₁ < arr.size := by
-- --       have h := Bool.and_elim_left h
-- --       have h := of_decide_eq_true h
-- --       have h := lt_srcSize_of_lt_end₁ slice i₁ h
-- --       exact h
-- --     have : i₂ < arr.size := by
-- --       have h := Bool.and_elim_right h
-- --       have h := of_decide_eq_true h
-- --       have h := lt_srcSize_of_lt_end₂ slice i₂ h
-- --       exact h
-- --     match Ord.compare arr[i₁] arr[i₂] with
-- --     | .lt | .eq =>
-- --       have h3 : ai < aux.size := sorry
-- --       let aifin : Fin aux.size := Fin.mk ai h3
-- --       aux := aux.set aifin arr[i₁]
-- --       ai := ai + 1
-- --       i₁ := i₁ + 1
-- --     | .gt =>
-- --       have h3 : ai < aux.size := sorry
-- --       let aifin : Fin aux.size := Fin.mk ai h3
-- --       aux := aux.set aifin arr[i₂]
-- --       ai := ai + 1
-- --       i₂ := i₂ + 1
-- --   pure aux

-- -- #check merge #[0, 0] #[20, 10] rfl ⟨0, 1, 1, by decide, by decide, by decide⟩

-- -- def mergeSort [Ord α] (arr : Array α) : Array α :=
-- --   match arr.size with
-- --   | 0 => arr
-- --   | 1 => arr
-- --   |

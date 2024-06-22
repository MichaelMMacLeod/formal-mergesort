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
theorem Nat.not_lt_of_lt_not_lt_and_lt {a b c d : ℕ} {a_lt_b : a < b}
    : (¬(a < b ∧ c < d)) → ¬c < d := by
  omega
theorem Nat.eq_of_not_lt_lt_succ {a b : ℕ} {not_a_lt_b : ¬a < b}
    : a < b.succ → a = b := by
  omega
theorem Nat.sub_succ_lt_sub_of_lt {a b : ℕ} (h : a < b) : b - a.succ < b - a := by omega

set_option pp.proofs true

structure M₁ (α : Type) where
  arr : Array α
  aux : Array α
  start₁ : ℕ
  start₂ : ℕ
  end₂ : ℕ
  start₁_lt_start₂ : start₁ < start₂
  start₂_lt_end₂ : start₂ < end₂
  end₂_le_arr_size : end₂ ≤ arr.size
  arr_size_eq_aux_size : arr.size = aux.size
deriving Repr

structure M₂ (α : Type) extends M₁ α where
  i : ℕ
  k₁ : ℕ
  k₂ : ℕ
  i_def : i = k₁ + k₂ - start₂
  k₂_ge_start₂ : k₂ ≥ start₂
  k₁_lt_start₂_succ : k₁ < start₂.succ
  k₂_lt_end₂_succ : k₂ < end₂.succ
  k₂_lt_end₂_of_not_k₁_lt_start₂ : ¬k₁ < start₂ → k₂ < end₂
deriving Repr

structure M₃ (α : Type) extends M₂ α where
  k₁_k₂_in_bounds : k₁ < start₂ ∧ k₂ < end₂
  k₁_lt_arr_size : k₁ < arr.size
  k₂_lt_arr_size : k₂ < arr.size
  i_lt_aux_size : i < aux.size
deriving Repr

def M₂.mkM₃ [Ord α] (m₂ : M₂ α) (k₁_k₂_in_bounds : m₂.k₁ < m₂.start₂ ∧ m₂.k₂ < m₂.end₂) : M₃ α :=
  have k₁_lt_arr_size := by
    apply And.left at k₁_k₂_in_bounds
    have start₂_lt_arr_size := Nat.lt_of_lt_le m₂.start₂_lt_end₂ m₂.end₂_le_arr_size
    exact (Nat.lt_trans k₁_k₂_in_bounds start₂_lt_arr_size)
  have k₂_lt_arr_size := by
    apply And.right at k₁_k₂_in_bounds
    exact (Nat.lt_of_lt_le k₁_k₂_in_bounds m₂.end₂_le_arr_size)
  have i_lt_aux_size := by
    have := m₂.i_def
    have := m₂.arr_size_eq_aux_size
    omega
  { m₂ with
    k₁_k₂_in_bounds
    k₁_lt_arr_size
    k₂_lt_arr_size
    i_lt_aux_size
  }

def M₃.nextLeft (m₃ : M₃ α) : M₂ α :=
  have := m₃.k₁_lt_arr_size
  let aux' := m₃.aux.set ⟨m₃.i, m₃.i_lt_aux_size⟩ m₃.arr[m₃.k₁]
  have arr_size_eq_aux'_size : m₃.arr.size = aux'.size := by
    simp [aux']
    exact m₃.arr_size_eq_aux_size
  have i_succ_def : m₃.i.succ = m₃.k₁.succ + m₃.k₂ - m₃.start₂ := by
    have := m₃.i_def
    have := m₃.k₂_ge_start₂
    omega
  have k₁_succ_lt_start₂_succ : m₃.k₁.succ < m₃.start₂.succ := by
    have := m₃.k₁_k₂_in_bounds
    omega
  have k₂_lt_end₂_of_not_k₁_succ_lt_start₂ : ¬m₃.k₁.succ < m₃.start₂ → m₃.k₂ < m₃.end₂ := by
    have := m₃.k₁_k₂_in_bounds
    omega
  { m₃ with
    aux := aux'
    arr_size_eq_aux_size := arr_size_eq_aux'_size
    i := m₃.i.succ
    k₁ := m₃.k₁.succ
    i_def := i_succ_def
    k₁_lt_start₂_succ := k₁_succ_lt_start₂_succ
    k₂_lt_end₂_of_not_k₁_lt_start₂ := k₂_lt_end₂_of_not_k₁_succ_lt_start₂
  }

def M₃.nextRight (m₃ : M₃ α) : M₂ α :=
  have := m₃.k₂_lt_arr_size
  let aux' := m₃.aux.set ⟨m₃.i, m₃.i_lt_aux_size⟩ m₃.arr[m₃.k₂]
  have arr_size_eq_aux'_size : m₃.arr.size = aux'.size := by
    simp [aux']
    exact m₃.arr_size_eq_aux_size
  have i_succ_def : m₃.i.succ = m₃.k₁ + m₃.k₂.succ - m₃.start₂ := by
    have := m₃.i_def
    have := m₃.k₂_ge_start₂
    omega
  have k₂_succ_lt_end₂_succ : m₃.k₂.succ < m₃.end₂.succ := by
    have := m₃.k₁_k₂_in_bounds
    omega
  have k₂_succ_ge_start₂ : m₃.k₂.succ ≥ m₃.start₂ := by
    have := m₃.k₂_ge_start₂
    omega
  have k₂_succ_lt_end₂_of_not_k₁_lt_start₂ : ¬m₃.k₁ < m₃.start₂ → m₃.k₂.succ < m₃.end₂ := by
    have := m₃.k₁_k₂_in_bounds
    omega
  { m₃ with
    aux := aux'
    arr_size_eq_aux_size := arr_size_eq_aux'_size
    i := m₃.i.succ
    k₂ := m₃.k₂.succ
    i_def := i_succ_def
    k₂_lt_end₂_succ := k₂_succ_lt_end₂_succ
    k₂_ge_start₂ := k₂_succ_ge_start₂
    k₂_lt_end₂_of_not_k₁_lt_start₂ := k₂_succ_lt_end₂_of_not_k₁_lt_start₂
  }

structure M₄Left (α : Type) extends M₁ α where
  i : ℕ
  k₁ : ℕ
  k₂ : ℕ
  i_def : i = k₁ + k₂ - start₂
  k₂_ge_start₂ : k₂ ≥ start₂
  k₁_lt_start₂_succ : k₁ < start₂.succ
  k₂_lt_end₂_succ : k₂ < end₂.succ

def M₂.mkM₄Left [Ord α] (m₂ : M₂ α) (k₁_lt_start₂ : m₂.k₁ < m₂.start₂) : M₄Left α :=
  have i_lt_aux_size : m₂.i < m₂.aux.size := by
    have := m₂.start₂_lt_end₂
    have := m₂.end₂_le_arr_size
    have := m₂.arr_size_eq_aux_size
    have := m₂.i_def
    have := m₂.k₂_lt_end₂_succ
    omega
  have k₁_lt_arr_size : m₂.k₁ < m₂.arr.size := by
    have := m₂.start₂_lt_end₂
    have := m₂.end₂_le_arr_size
    omega
  let aux' := m₂.aux.set ⟨m₂.i, i_lt_aux_size⟩ m₂.arr[m₂.k₁]
  let arr_size_eq_aux'_size : m₂.arr.size = aux'.size := by
    simp [aux']
    exact m₂.arr_size_eq_aux_size
  have i_succ_def : m₂.i.succ = m₂.k₁.succ + m₂.k₂ - m₂.start₂ := by
    have := m₂.i_def
    have := m₂.k₂_ge_start₂
    omega
  have k₁_succ_lt_start₂_succ : m₂.k₁.succ < m₂.start₂.succ := by
    omega
  { m₂ with
    aux := aux'
    arr_size_eq_aux_size := arr_size_eq_aux'_size
    k₁ := m₂.k₁.succ
    i := m₂.i.succ
    i_def := i_succ_def
    k₁_lt_start₂_succ := k₁_succ_lt_start₂_succ
  }

def M₄Left.next [Ord α] (m₄Left : M₄Left α) (k₁_lt_start₂ : m₄Left.k₁ < m₄Left.start₂): M₄Left α :=
  have i_lt_aux_size : m₄Left.i < m₄Left.aux.size := by
    have := m₄Left.start₂_lt_end₂
    have := m₄Left.end₂_le_arr_size
    have := m₄Left.arr_size_eq_aux_size
    have := m₄Left.i_def
    have := m₄Left.k₂_lt_end₂_succ
    omega
  have k₁_lt_arr_size : m₄Left.k₁ < m₄Left.arr.size := by
    have := m₄Left.start₂_lt_end₂
    have := m₄Left.end₂_le_arr_size
    omega
  let aux' := m₄Left.aux.set ⟨m₄Left.i, i_lt_aux_size⟩ m₄Left.arr[m₄Left.k₁]
  let arr_size_eq_aux'_size : m₄Left.arr.size = aux'.size := by
    simp [aux']
    exact m₄Left.arr_size_eq_aux_size
  have i_succ_def : m₄Left.i.succ = m₄Left.k₁.succ + m₄Left.k₂ - m₄Left.start₂ := by
    have := m₄Left.i_def
    have := m₄Left.k₂_ge_start₂
    omega
  have k₁_succ_lt_start₂_succ : m₄Left.k₁.succ < m₄Left.start₂.succ := by
    omega
  { m₄Left with
    aux := aux'
    arr_size_eq_aux_size := arr_size_eq_aux'_size
    k₁ := m₄Left.k₁.succ
    i := m₄Left.i.succ
    i_def := i_succ_def
    k₁_lt_start₂_succ := k₁_succ_lt_start₂_succ
  }

structure M₄Right (α : Type) extends M₁ α where
  i : ℕ
  k₁ : ℕ
  k₂ : ℕ
  i_def : i = k₁ + k₂ - start₂
  k₂_ge_start₂ : k₂ ≥ start₂
  k₁_lt_start₂_succ : k₁ < start₂.succ
  not_k₁_lt_start₂ : ¬k₁ < start₂

def M₂.mkM₄Right
    [Ord α]
    (m₂ : M₂ α)
    (not_k₁_lt_start₂ : ¬m₂.k₁ < m₂.start₂)
    : M₄Right α :=
  have i_lt_aux_size : m₂.i < m₂.aux.size := by
    have := m₂.end₂_le_arr_size
    have := m₂.arr_size_eq_aux_size
    have := m₂.i_def
    have := m₂.k₁_lt_start₂_succ
    have := m₂.k₂_lt_end₂_of_not_k₁_lt_start₂
    omega
  have k₂_lt_arr_size : m₂.k₂ < m₂.arr.size := by
    have := m₂.arr_size_eq_aux_size
    have := m₂.i_def
    omega
  let aux' := m₂.aux.set ⟨m₂.i, i_lt_aux_size⟩ m₂.arr[m₂.k₂]
  let arr_size_eq_aux'_size : m₂.arr.size = aux'.size := by
    simp [aux']
    exact m₂.arr_size_eq_aux_size
  have i_succ_def : m₂.i.succ = m₂.k₁ + m₂.k₂.succ - m₂.start₂ := by
    have := m₂.i_def
    have := m₂.k₂_ge_start₂
    omega
  have k₂_succ_ge_start₂ : m₂.k₂.succ ≥ m₂.start₂ := by
    have := m₂.k₂_ge_start₂
    omega
  { m₂ with
    aux := aux'
    arr_size_eq_aux_size := arr_size_eq_aux'_size
    k₂ := m₂.k₂.succ
    i := m₂.i.succ
    i_def := i_succ_def
    k₂_ge_start₂ := k₂_succ_ge_start₂
    not_k₁_lt_start₂
  }

def M₄Right.next
    [Ord α]
    (m₄Right : M₄Right α)
    (k₂_lt_end₂ : m₄Right.k₂ < m₄Right.end₂)
    : M₄Right α :=
  have i_lt_aux_size : m₄Right.i < m₄Right.aux.size := by
    have := m₄Right.end₂_le_arr_size
    have := m₄Right.arr_size_eq_aux_size
    have := m₄Right.i_def
    have := m₄Right.k₁_lt_start₂_succ
    omega
  have k₂_lt_arr_size : m₄Right.k₂ < m₄Right.arr.size := by
    have := m₄Right.arr_size_eq_aux_size
    have := m₄Right.i_def
    have := m₄Right.not_k₁_lt_start₂
    omega
  let aux' := m₄Right.aux.set ⟨m₄Right.i, i_lt_aux_size⟩ m₄Right.arr[m₄Right.k₂]
  let arr_size_eq_aux'_size : m₄Right.arr.size = aux'.size := by
    simp [aux']
    exact m₄Right.arr_size_eq_aux_size
  have i_succ_def : m₄Right.i.succ = m₄Right.k₁ + m₄Right.k₂.succ - m₄Right.start₂ := by
    have := m₄Right.i_def
    have := m₄Right.k₂_ge_start₂
    omega
  have k₂_succ_ge_start₂ : m₄Right.k₂.succ ≥ m₄Right.start₂ := by
    have := m₄Right.k₂_ge_start₂
    omega
  { m₄Right with
    aux := aux'
    arr_size_eq_aux_size := arr_size_eq_aux'_size
    k₂ := m₄Right.k₂.succ
    i := m₄Right.i.succ
    i_def := i_succ_def
    k₂_ge_start₂ := k₂_succ_ge_start₂
  }

def mergeAdjacentChunksIntoAux [Ord α] (m₁ : M₁ α) : Array α :=
  let m₂ : M₂ α :=
    { m₁ with
      i := m₁.start₁
      k₁ := m₁.start₁
      k₂ := m₁.start₂
      i_def := Nat.eq_sub_of_add_eq rfl
      k₂_ge_start₂ := Nat.le_refl m₁.start₂
      k₁_lt_start₂_succ := Nat.lt_succ_of_lt m₁.start₁_lt_start₂
      k₂_lt_end₂_succ := Nat.lt_succ_of_lt m₁.start₂_lt_end₂
      k₂_lt_end₂_of_not_k₁_lt_start₂ := fun _ ↦ m₁.start₂_lt_end₂
    }
  let rec loop (m₂ : M₂ α) : Array α :=
    if k₁_k₂_in_bounds : m₂.k₁ < m₂.start₂ ∧ m₂.k₂ < m₂.end₂ then
      let m₃ := m₂.mkM₃ k₁_k₂_in_bounds
      have := m₃.k₁_lt_arr_size
      have := m₃.k₂_lt_arr_size
      match Ord.compare m₂.arr[m₂.k₁] m₂.arr[m₂.k₂] with
      | .lt | .eq =>
        loop m₃.nextLeft
      | .gt =>
        loop m₃.nextRight
    else if k₁_lt_start₂ : m₂.k₁ < m₂.start₂ then
      let rec loopLeft (m₄Left : M₄Left α) : Array α :=
        if k₁_lt_start₂ : m₄Left.k₁ < m₄Left.start₂ then
          loopLeft (m₄Left.next k₁_lt_start₂)
        else
          m₄Left.aux
      termination_by m₄Left.start₂ - m₄Left.k₁
      decreasing_by
        simp_wf
        have start₂_def : (m₄Left.next k₁_lt_start₂).start₂ = m₄Left.start₂ := by rfl
        have k₁_def : (m₄Left.next k₁_lt_start₂).k₁ = m₄Left.k₁.succ := by rfl
        omega
      loopLeft (m₂.mkM₄Left k₁_lt_start₂)
    else
      let rec loopRight (m₄Right : M₄Right α) : Array α :=
        if k₂_lt_end₂ : m₄Right.k₂ < m₄Right.end₂ then
          loopRight (m₄Right.next k₂_lt_end₂)
        else
          m₄Right.aux
      termination_by m₄Right.end₂ - m₄Right.k₂
      decreasing_by
        simp_wf
        have end₂_def : (m₄Right.next k₂_lt_end₂).end₂ = m₄Right.end₂ := by rfl
        have k₂_def : (m₄Right.next k₂_lt_end₂).k₂ = m₄Right.k₂.succ := by rfl
        omega
      loopRight (m₂.mkM₄Right k₁_lt_start₂)
  termination_by m₂.arr.size - m₂.i
  decreasing_by
    . have nextLeft_i_def : (m₂.mkM₃ k₁_k₂_in_bounds).nextLeft.i = m₂.i.succ := by rfl
      repeat rw [nextLeft_i_def]
      have i_lt_arr_size : m₂.i < m₂.arr.size := by
        rw [m₂.arr_size_eq_aux_size]
        exact (m₂.mkM₃ k₁_k₂_in_bounds).i_lt_aux_size
      exact (Nat.sub_succ_lt_sub_of_lt i_lt_arr_size)
    . have nextRight_i_def : (m₂.mkM₃ k₁_k₂_in_bounds).nextRight.i = m₂.i.succ := by rfl
      repeat rw [nextRight_i_def]
      have i_lt_arr_size : m₂.i < m₂.arr.size := by
        rw [m₂.arr_size_eq_aux_size]
        exact (m₂.mkM₃ k₁_k₂_in_bounds).i_lt_aux_size
      exact (Nat.sub_succ_lt_sub_of_lt i_lt_arr_size)
  loop m₂

-- Sorts every two adjacent chunks in `arr` of length `size` into `aux`.
def mergeChunksIntoAux [Inhabited α] [Ord α] (arr : Array α) (aux : Array α) (size : ℕ)
    (arr_size_eq_aux_size : arr.size = aux.size)
    (size_gt_0 : size > 0)
    (size_lt_aux_size : size < aux.size)
    : Array α := Id.run do
  let start₁ := 0
  let start₂ := start₁ + size
  let end₂ := min (start₂ + size) arr.size
  have start₁_lt_start₂ := by omega
  have start₂_lt_end₂ : start₂ < end₂ := by omega
  have end₂_le_arr_size := by omega
  let m₁ : M₁ α :=
    { arr,
      aux,
      start₁,
      start₂,
      end₂,
      start₁_lt_start₂,
      start₂_lt_end₂,
      end₂_le_arr_size,
      arr_size_eq_aux_size,
    }
  let rec loop (m₁ : M₁ α) : Array α :=
    if m₁.start₁ + size < m₁.arr.size then
      let aux' := mergeAdjacentChunksIntoAux m₁
      loop m₁'
    else
      sorry
  loop m₁
  -- let rec loop₁ (aux : Array α) (start₁ : ℕ)
  --     (arr_size_eq_aux_size : arr.size = aux.size)
  --     : Array α :=
  --   if start₁ + size < arr.size then
  --     let start₂ := start₁ + size
  --     let end₂ := min (start₂ + size) arr.size
  --     have start₁_lt_start₂ : start₁ < start₂ := by omega
  --     have start₂_lt_end₂ : start₂ < end₂ := by sorry
  --     have end₂_le_arr_size : end₂ ≤ arr.size := by omega
  --     let m₁ : M₁ α :=
  --       { arr,
  --         aux,
  --         start₁,
  --         start₂,
  --         end₂,
  --         start₁_lt_start₂,
  --         start₂_lt_end₂,
  --         end₂_le_arr_size,
  --         arr_size_eq_aux_size,
  --       }
  --     let aux' := mergeAdjacentChunksIntoAux m₁
  --     let start₁' := start₁ + 2 * size
  --     have arr_size_eq_aux'_size : arr.size = aux'.size := by
  --       sorry
  --     loop₁ aux' start₁'
  --       arr_size_eq_aux'_size
  --   else
  --     let rec loop₂ (aux : Array α) (start₁ : ℕ)
  --         : Array α :=
  --       if start₁ < arr.size then
  --         have : start₁ < arr.size := by sorry
  --         have chunkStart₁_lt_aux_size : start₁ < aux.size := by sorry
  --         let aux' := aux.set ⟨start₁, chunkStart₁_lt_aux_size⟩ arr[start₁]
  --         let start₁' := start₁ + 1
  --         loop₂ aux' start₁'
  --       else
  --         aux
  --     loop₂ aux start₁
  -- loop₁ aux 0
  --   arr_size_eq_aux_size

@[specialize] def Array.mergeSort [Inhabited α] [Ord α] (arr : Array α) : Array α := Id.run do
  let mut arr := arr
  let mut aux : Array α := Array.mkArray arr.size default
  let mut chunkSize := 1
  let mut auxIsAux := true
  while chunkSize < arr.size do
    if auxIsAux then
      aux := mergeChunksIntoAux arr aux chunkSize (by sorry) (by sorry)
    else
      arr := mergeChunksIntoAux aux arr chunkSize (by sorry) (by sorry)
    chunkSize := chunkSize * 2
    auxIsAux := !auxIsAux
  if auxIsAux then
    pure arr
  else
    pure aux

#eval #[15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1].mergeSort

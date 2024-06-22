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

@[ext]
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

@[ext]
structure M₂ (α : Type) extends M₁ α where
  i : ℕ
  k₁ : ℕ
  k₂ : ℕ
  i_def : i = k₁ + k₂ - start₂
  k₂_ge_start₂ : k₂ ≥ start₂
  k₁_lt_start₂_succ : k₁ < start₂.succ
  k₂_lt_end₂_succ : k₂ < end₂.succ
  k₂_lt_end₂_of_not_k₁_lt_start₂ : ¬start₁ < start₂ → start₂ < end₂
deriving Repr

@[ext]
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
  { m₃ with
    aux := aux'
    arr_size_eq_aux_size := arr_size_eq_aux'_size
    i := m₃.i.succ
    k₁ := m₃.k₁.succ
    i_def := i_succ_def
    k₁_lt_start₂_succ := k₁_succ_lt_start₂_succ
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
  { m₃ with
    aux := aux'
    arr_size_eq_aux_size := arr_size_eq_aux'_size
    i := m₃.i.succ
    k₂ := m₃.k₂.succ
    i_def := i_succ_def
    k₂_lt_end₂_succ := k₂_succ_lt_end₂_succ
    k₂_ge_start₂ := k₂_succ_ge_start₂
  }

structure M₄Left (α : Type) extends M₂ α where
  not_k₁_k₂_in_bounds : ¬(k₁ < start₂ ∧ k₂ < end₂)
  k₁_lt_start₂ : k₁ < start₂
  k₁_lt_arr_size : k₁ < arr.size
  i_lt_aux_size : i < aux.size

def M₂.mkM₄Left [Ord α] (m₂ : M₂ α)
    (not_k₁_k₂_in_bounds : ¬(m₂.k₁ < m₂.start₂ ∧ m₂.k₂ < m₂.end₂))
    (k₁_lt_start₂ : m₂.k₁ < m₂.start₂)
    : M₄Left α :=
  have k₁_lt_arr_size : m₂.k₁ < m₂.arr.size := by
    have := m₂.start₂_lt_end₂
    have := m₂.end₂_le_arr_size
    omega
  have i_lt_aux_size : m₂.i < m₂.aux.size := by
    have := m₂.end₂_le_arr_size
    have := m₂.arr_size_eq_aux_size
    have := m₂.i_def
    have := m₂.k₂_lt_end₂_succ
    omega
  { m₂ with
    not_k₁_k₂_in_bounds
    k₁_lt_start₂
    k₁_lt_arr_size
    i_lt_aux_size
  }

def M₄Left.next [Ord α] (m₄Left : M₄Left α) : M₂ α :=
  have := m₄Left.k₁_lt_arr_size
  let aux' := m₄Left.aux.set ⟨m₄Left.i, m₄Left.i_lt_aux_size⟩ m₄Left.arr[m₄Left.k₁]
  let arr_size_eq_aux'_size : m₄Left.arr.size = aux'.size := by
    simp [aux']
    exact m₄Left.arr_size_eq_aux_size
  have i_succ_def : m₄Left.i.succ = m₄Left.k₁.succ + m₄Left.k₂ - m₄Left.start₂ := by
    have := m₄Left.i_def
    have := m₄Left.k₂_ge_start₂
    omega
  have k₁_succ_lt_start₂_succ : m₄Left.k₁.succ < m₄Left.start₂.succ := by
    have := m₄Left.k₁_lt_start₂
    omega
  { m₄Left with
    aux := aux'
    arr_size_eq_aux_size := arr_size_eq_aux'_size
    k₁ := m₄Left.k₁.succ
    i := m₄Left.i.succ
    i_def := i_succ_def
    k₁_lt_start₂_succ := k₁_succ_lt_start₂_succ
  }

def mergeAdjacentChunksIntoAuxM [Ord α] (m₁ : M₁ α) : Array α :=
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
      let not_k₁_k₂_in_bounds := k₁_k₂_in_bounds
      let m₄Left := m₂.mkM₄Left not_k₁_k₂_in_bounds k₁_lt_start₂
      let rec loop (m₂ : M₂ α) : Array α :=
        if k₁_lt_start₂ : m₂.k₁ < m₂.start₂ then
          let m₄Left := m₂.mkM₄Left not_k₁_k₂_in_bounds k₁_lt_start₂
          loop m₄Left.next
        else
          m₂.aux
      loop m₄Left.next
    else
      sorry
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

def mergeAdjacentChunksIntoAuxLoopLeft
    [Ord α]
    (arr aux : Array α)
    (i k₁ k₂ start₁ start₂ end₂ : ℕ)
    (start₁_lt_start₂ : start₁ < start₂)
    (start₂_lt_end₂ : start₂ < end₂)
    (end₂_le_arr_size : end₂ ≤ arr.size)
    (arr_size_eq_aux_size : arr.size = aux.size)
    (i_def : i = k₁ + k₂ - start₂)
    (k₂_ge_start₂ : k₂ ≥ start₂)
    (k₁_lt_start₂_succ : k₁ < start₂.succ)
    (k₂_lt_end₂_succ : k₂ < end₂.succ)
    (k₂_lt_end₂_of_not_k₁_lt_start₂ : ¬k₁ < start₂ → k₂ < end₂)
    (k₁_lt_start₂ : k₁ < start₂)
    (not_k₁_k₂_in_bounds : ¬(k₁ < start₂ ∧ k₂ < end₂))
    : Array α :=
  have : k₁ < arr.size := by
    have k₁_lt_end₂ : k₁ < end₂ := Nat.lt_trans k₁_lt_start₂ start₂_lt_end₂
    exact (Nat.lt_of_lt_le k₁_lt_end₂ end₂_le_arr_size)
  have i_lt_aux_size : i < aux.size := by omega
  let aux' := aux.set ⟨i, i_lt_aux_size⟩ arr[k₁]
  have arr_size_eq_aux'_size : arr.size = aux'.size := by
    have aux'_def : aux' = aux.set ⟨i, i_lt_aux_size⟩ arr[k₁] := by rfl
    rw [aux'_def, Array.size_set]
    exact arr_size_eq_aux_size
  have i_succ_def : i.succ = k₁.succ + k₂ - start₂ := by omega
  let rec loop (aux : Array α) (i k₁ : ℕ)
      (arr_size_eq_aux_size : arr.size = aux.size)
      (i_def : i = k₁ + k₂ - start₂)
      : Array α :=
    if k₁_lt_start₂ : k₁ < start₂ then
      have : k₁ < arr.size := by
        have k₁_lt_end₂ : k₁ < end₂ := Nat.lt_trans k₁_lt_start₂ start₂_lt_end₂
        exact (Nat.lt_of_lt_le k₁_lt_end₂ end₂_le_arr_size)
      have : k₂ = end₂ := by
        have not_k₂_lt_end₂ : ¬k₂ < end₂ := by omega
        exact (Nat.eq_of_not_lt_lt_succ k₂_lt_end₂_succ (not_a_lt_b := not_k₂_lt_end₂))
      have i_lt_aux_size : i < aux.size := by omega
      let aux' := aux.set ⟨i, i_lt_aux_size⟩ arr[k₁]
      have arr_size_eq_aux'_size : arr.size = aux'.size := by
        have aux'_def : aux' = aux.set ⟨i, i_lt_aux_size⟩ arr[k₁] := by rfl
        rw [aux'_def, Array.size_set]
        exact arr_size_eq_aux_size
      have i_succ_def : i.succ = k₁.succ + k₂ - start₂ := by omega
      loop aux' i.succ k₁.succ arr_size_eq_aux'_size i_succ_def
    else
      aux
  termination_by start₂ - k₁
  loop aux' i.succ k₁.succ arr_size_eq_aux'_size i_succ_def

def mergeAdjacentChunksIntoAuxLoopRight
    [Ord α]
    (arr aux : Array α)
    (i k₁ k₂ start₁ start₂ end₂ : ℕ)
    (start₁_lt_start₂ : start₁ < start₂)
    (start₂_lt_end₂ : start₂ < end₂)
    (end₂_le_arr_size : end₂ ≤ arr.size)
    (arr_size_eq_aux_size : arr.size = aux.size)
    (i_def : i = k₁ + k₂ - start₂)
    (k₂_ge_start₂ : k₂ ≥ start₂)
    (k₁_lt_start₂_succ : k₁ < start₂.succ)
    (k₂_lt_end₂_succ : k₂ < end₂.succ)
    (k₂_lt_end₂_of_not_k₁_lt_start₂ : ¬k₁ < start₂ → k₂ < end₂)
    (not_k₁_lt_start₂ : ¬k₁ < start₂)
    (not_k₁_k₂_in_bounds : ¬(k₁ < start₂ ∧ k₂ < end₂))
    : Array α :=
  have : k₂ < arr.size := by omega
  have i_lt_aux_size : i < aux.size := by omega
  let aux' := aux.set ⟨i, i_lt_aux_size⟩ arr[k₂]
  have arr_size_eq_aux'_size : arr.size = aux'.size := by
    have aux'_def : aux' = aux.set ⟨i, i_lt_aux_size⟩ arr[k₂] := by rfl
    rw [aux'_def, Array.size_set]
    exact arr_size_eq_aux_size
  have i_succ_def : i.succ = k₁ + k₂.succ - start₂ := by omega
  let rec loop (aux : Array α) (i k₂ : ℕ)
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
      loop aux' i.succ k₂.succ
        arr_size_eq_aux'_size
        i_succ_def
    else
      aux
  termination_by end₂ - k₂
  loop aux' i.succ k₂.succ arr_size_eq_aux'_size i_succ_def

-- theorem mergeAdjacentChunksIntoAuxLoop.termination {}

def mergeAdjacentChunksIntoAuxLoop
    [Ord α]
    (arr aux : Array α)
    (i k₁ k₂ start₁ start₂ end₂ : ℕ)
    (start₁_lt_start₂ : start₁ < start₂)
    (start₂_lt_end₂ : start₂ < end₂)
    (end₂_le_arr_size : end₂ ≤ arr.size)
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
      mergeAdjacentChunksIntoAuxLoop
        (arr := arr)
        (aux := aux')
        (i := i.succ)
        (k₁ := k₁.succ)
        (k₂ := k₂)
        (start₁ := start₁)
        (start₂ := start₂)
        (end₂ := end₂)
        (start₁_lt_start₂ := start₁_lt_start₂)
        (start₂_lt_end₂ := start₂_lt_end₂)
        (end₂_le_arr_size := end₂_le_arr_size)
        (arr_size_eq_aux_size := arr_size_eq_aux'_size)
        (i_def := i_succ_def)
        (k₂_ge_start₂ := k₂_ge_start₂)
        (k₁_lt_start₂_succ := k₁_succ_lt_start₂_succ)
        (k₂_lt_end₂_succ := k₂_lt_end₂_succ)
        (k₂_lt_end₂_of_not_k₁_lt_start₂ := k₂_lt_end₂_of_not_k₁_succ_lt_start₂)
    | .gt =>
      let aux' := aux.set ⟨i, i_lt_aux_size⟩ arr[k₂]
      have arr_size_eq_aux'_size : arr.size = aux'.size := by
        have aux'_def : aux' = aux.set ⟨i, i_lt_aux_size⟩ arr[k₂] := by rfl
        rw [aux'_def, Array.size_set]
        exact arr_size_eq_aux_size
      have i_succ_def : i.succ = k₁ + k₂.succ - start₂ := by omega
      have k₂_succ_ge_start₂ : k₂.succ ≥ start₂ := by omega
      have k₂_succ_lt_end₂_succ : k₂.succ < end₂.succ := by omega
      have k₂_succ_lt_end₂_of_not_k₁_lt_start₂ : ¬k₁ < start₂ → k₂.succ < end₂ := by omega
      mergeAdjacentChunksIntoAuxLoop
        (arr := arr)
        (aux := aux')
        (i := i.succ)
        (k₁ := k₁)
        (k₂ := k₂.succ)
        (start₁ := start₁)
        (start₂ := start₂)
        (end₂ := end₂)
        (start₁_lt_start₂ := start₁_lt_start₂)
        (start₂_lt_end₂ := start₂_lt_end₂)
        (end₂_le_arr_size := end₂_le_arr_size)
        (arr_size_eq_aux_size := arr_size_eq_aux'_size)
        (i_def := i_succ_def)
        (k₂_ge_start₂ := k₂_succ_ge_start₂)
        (k₁_lt_start₂_succ := k₁_lt_start₂_succ)
        (k₂_lt_end₂_succ := k₂_succ_lt_end₂_succ)
        (k₂_lt_end₂_of_not_k₁_lt_start₂ := k₂_succ_lt_end₂_of_not_k₁_lt_start₂)
  else if k₁_lt_start₂ : k₁ < start₂ then
    mergeAdjacentChunksIntoAuxLoopLeft
      (arr := arr)
      (aux := aux)
      (i := i)
      (k₁ := k₁)
      (k₂ := k₂)
      (start₁ := start₁)
      (start₂ := start₂)
      (end₂ := end₂)
      (start₁_lt_start₂ := start₁_lt_start₂)
      (start₂_lt_end₂ := start₂_lt_end₂)
      (end₂_le_arr_size := end₂_le_arr_size)
      (arr_size_eq_aux_size := arr_size_eq_aux_size)
      (i_def := i_def)
      (k₂_ge_start₂ := k₂_ge_start₂)
      (k₁_lt_start₂_succ := k₁_lt_start₂_succ)
      (k₂_lt_end₂_succ := k₂_lt_end₂_succ)
      (k₂_lt_end₂_of_not_k₁_lt_start₂ := k₂_lt_end₂_of_not_k₁_lt_start₂)
      (k₁_lt_start₂ := k₁_lt_start₂)
      (not_k₁_k₂_in_bounds := k₁_k₂_in_bounds)
  else
    mergeAdjacentChunksIntoAuxLoopRight
      (arr := arr)
      (aux := aux)
      (i := i)
      (k₁ := k₁)
      (k₂ := k₂)
      (start₁ := start₁)
      (start₂ := start₂)
      (end₂ := end₂)
      (start₁_lt_start₂ := start₁_lt_start₂)
      (start₂_lt_end₂ := start₂_lt_end₂)
      (end₂_le_arr_size := end₂_le_arr_size)
      (arr_size_eq_aux_size := arr_size_eq_aux_size)
      (i_def := i_def)
      (k₂_ge_start₂ := k₂_ge_start₂)
      (k₁_lt_start₂_succ := k₁_lt_start₂_succ)
      (k₂_lt_end₂_succ := k₂_lt_end₂_succ)
      (k₂_lt_end₂_of_not_k₁_lt_start₂ := k₂_lt_end₂_of_not_k₁_lt_start₂)
      (not_k₁_lt_start₂ := k₁_lt_start₂)
      (not_k₁_k₂_in_bounds := k₁_k₂_in_bounds)
termination_by (start₂ - k₁, end₂ - k₂)

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
def mergeAdjacentChunksIntoAux
    [Ord α]
    (arr aux : Array α)
    (start₁ start₂ end₂ : ℕ)
    (start₁_lt_start₂ : start₁ < start₂)
    (start₂_lt_end₂ : start₂ < end₂)
    (end₂_le_arr_size : end₂ ≤ arr.size)
    (arr_size_eq_aux_size : arr.size = aux.size)
    : Array α :=
  have i_def : start₁ = start₁ + start₂ - start₂ := Nat.eq_sub_of_add_eq rfl
  have k₂_ge_start₂ : start₂ ≥ start₂ := Nat.le_refl start₂
  have k₁_lt_start₂_succ : start₁ < start₂.succ := Nat.lt_succ_of_lt start₁_lt_start₂
  have k₂_lt_end₂_succ : start₂ < end₂.succ := Nat.lt_succ_of_lt start₂_lt_end₂
  have k₂_lt_end₂_of_not_k₁_lt_start₂ : ¬start₁ < start₂ → start₂ < end₂ :=
    fun _ ↦ start₂_lt_end₂
  mergeAdjacentChunksIntoAuxLoop
    (arr := arr)
    (aux := aux)
    (i := start₁)
    (k₁ := start₁)
    (k₂ := start₂)
    (start₁ := start₁)
    (start₂ := start₂)
    (end₂ := end₂)
    (start₁_lt_start₂ := start₁_lt_start₂)
    (start₂_lt_end₂ := start₂_lt_end₂)
    (end₂_le_arr_size := end₂_le_arr_size)
    (arr_size_eq_aux_size := arr_size_eq_aux_size)
    (i_def := i_def)
    (k₂_ge_start₂ := k₂_ge_start₂)
    (k₁_lt_start₂_succ := k₁_lt_start₂_succ)
    (k₂_lt_end₂_succ := k₂_lt_end₂_succ)
    (k₂_lt_end₂_of_not_k₁_lt_start₂ := k₂_lt_end₂_of_not_k₁_lt_start₂)

-- #check mergeAdjacentChunksIntoAuxLoop.induct

-- theorem mergeAdjacentChunksIntoAuxLoopLeft_size_eq
--     [Ord α]
--     (arr aux : Array α)
--     (i k₁ k₂ start₁ start₂ end₂ : ℕ)
--     (start₁_lt_start₂ : start₁ < start₂)
--     (start₂_lt_end₂ : start₂ < end₂)
--     (end₂_le_arr_size : end₂ ≤ arr.size)
--     (arr_size_eq_aux_size : arr.size = aux.size)
--     (i_def : i = k₁ + k₂ - start₂)
--     (k₂_ge_start₂ : k₂ ≥ start₂)
--     (k₁_lt_start₂_succ : k₁ < start₂.succ)
--     (k₂_lt_end₂_succ : k₂ < end₂.succ)
--     (k₂_lt_end₂_of_not_k₁_lt_start₂ : ¬k₁ < start₂ → k₂ < end₂)
--     (k₁_lt_start₂ : k₁ < start₂)
--     (not_k₁_k₂_in_bounds : ¬(k₁ < start₂ ∧ k₂ < end₂))
--     : (mergeAdjacentChunksIntoAuxLoopLeft
--         (arr := arr)
--         (aux := aux)
--         (i := i)
--         (k₁ := k₁)
--         (k₂ := k₂)
--         (start₁ := start₁)
--         (start₂ := start₂)
--         (end₂ := end₂)
--         (start₁_lt_start₂ := start₁_lt_start₂)
--         (start₂_lt_end₂ := start₂_lt_end₂)
--         (end₂_le_arr_size := end₂_le_arr_size)
--         (arr_size_eq_aux_size := arr_size_eq_aux_size)
--         (i_def := i_def)
--         (k₂_ge_start₂ := k₂_ge_start₂)
--         (k₁_lt_start₂_succ := k₁_lt_start₂_succ)
--         (k₂_lt_end₂_succ := k₂_lt_end₂_succ)
--         (k₂_lt_end₂_of_not_k₁_lt_start₂ := k₂_lt_end₂_of_not_k₁_lt_start₂)
--         (k₁_lt_start₂ := k₁_lt_start₂)
--         (not_k₁_k₂_in_bounds := not_k₁_k₂_in_bounds)
--       ).size = aux.size := by
--   rw [mergeAdjacentChunksIntoAuxLoopLeft]
--   have : k₁ < arr.size := by
--     have k₁_lt_end₂ : k₁ < end₂ := Nat.lt_trans k₁_lt_start₂ start₂_lt_end₂
--     exact (Nat.lt_of_lt_le k₁_lt_end₂ end₂_le_arr_size)
--   have i_lt_aux_size : i < aux.size := by omega
--   let aux' := aux.set ⟨i, i_lt_aux_size⟩ arr[k₁]
--   have arr_size_eq_aux'_size : arr.size = aux'.size := by
--     have aux'_def : aux' = aux.set ⟨i, i_lt_aux_size⟩ arr[k₁] := by rfl
--     rw [aux'_def, Array.size_set]
--     exact arr_size_eq_aux_size
--   have i_succ_def : i.succ = k₁.succ + k₂ - start₂ := by omega
--   simp [*]
--   let rec go
--       : (mergeAdjacentChunksIntoAuxLoopLeft.loop
--           (arr := arr)
--           (aux := aux')
--           (i := i.succ)
--           (k₁ := k₁.succ)
--           (k₂ := k₂)
--           (start₁ := start₁)
--           (start₂ := start₂)
--           (end₂ := end₂)
--           (start₂_lt_end₂ := start₂_lt_end₂)
--           (end₂_le_arr_size := end₂_le_arr_size)
--           (arr_size_eq_aux_size := arr_size_eq_aux'_size)
--           (i_def := i_succ_def)
--           (k₂_ge_start₂ := k₂_ge_start₂)
--           (k₂_lt_end₂_succ := k₂_lt_end₂_succ)
--           (k₁_lt_start₂ := by omega)
--           (not_k₁_k₂_in_bounds := ·)

--         ).size = aux.size := by
--     sorry
--   rw [mergeAdjacentChunksIntoAuxLoopLeft.loop]
--   if k₁_lt_start₂ : k₁ + 1 < start₂ then
--     simp [k₁_lt_start₂]
--   else
--     simp [k₁_lt_start₂]

-- theorem mergeAdjacentChunksIntoAuxLoop_size_eq
--     [Ord α]
--     (arr aux : Array α)
--     (i k₁ k₂ start₁ start₂ end₂ : ℕ)
--     (start₁_lt_start₂ : start₁ < start₂)
--     (start₂_lt_end₂ : start₂ < end₂)
--     (end₂_le_arr_size : end₂ ≤ arr.size)
--     (arr_size_eq_aux_size : arr.size = aux.size)
--     (i_def : i = k₁ + k₂ - start₂)
--     (k₂_ge_start₂ : k₂ ≥ start₂)
--     (k₁_lt_start₂_succ : k₁ < start₂.succ)
--     (k₂_lt_end₂_succ : k₂ < end₂.succ)
--     (k₂_lt_end₂_of_not_k₁_lt_start₂ : ¬k₁ < start₂ → k₂ < end₂)
--     : (mergeAdjacentChunksIntoAuxLoop
--         (arr := arr)
--         (aux := aux)
--         (i := i)
--         (k₁ := k₁)
--         (k₂ := k₂)
--         (start₁ := start₁)
--         (start₂ := start₂)
--         (end₂ := end₂)
--         (start₁_lt_start₂ := start₁_lt_start₂)
--         (start₂_lt_end₂ := start₂_lt_end₂)
--         (end₂_le_arr_size := end₂_le_arr_size)
--         (arr_size_eq_aux_size := arr_size_eq_aux_size)
--         (i_def := i_def)
--         (k₂_ge_start₂ := k₂_ge_start₂)
--         (k₁_lt_start₂_succ := k₁_lt_start₂_succ)
--         (k₂_lt_end₂_succ := k₂_lt_end₂_succ)
--         (k₂_lt_end₂_of_not_k₁_lt_start₂ := k₂_lt_end₂_of_not_k₁_lt_start₂)
--       ).size = aux.size := by
--   rw [mergeAdjacentChunksIntoAuxLoop]
--   if k₁_k₂_in_bounds : k₁ < start₂ ∧ k₂ < end₂ then
--     simp [k₁_k₂_in_bounds]
--     split
--     . case h_1 =>
--       simp [(mergeAdjacentChunksIntoAuxLoop_size_eq · · · · · · · · · · · · · · · · ·), k₁_k₂_in_bounds]
--     . case h_2 =>
--       simp [(mergeAdjacentChunksIntoAuxLoop_size_eq · · · · · · · · · · · · · · · · ·), k₁_k₂_in_bounds]
--     . case h_3 =>
--       simp [(mergeAdjacentChunksIntoAuxLoop_size_eq · · · · · · · · · · · · · · · · ·), k₁_k₂_in_bounds]

--     -- split <;> simp [mergeAdjacentChunksIntoAuxLoop_size_eq, k₁_k₂_in_bounds]
--   else
--     unfold mergeAdjacentChunksIntoAuxLoop
--     split <;> simp [k₁_k₂_in_bounds]

--     -- split
--     -- . case isTrue h =>
--     --   sorry
--     -- . case isFalse h =>
--     --   sorry
-- -- termination_by (start₂ - k₁, end₂ - k₂)

-- theorem mergeAdjacentChunksIntoAux_size_eq
--     [Ord α]
--     (arr aux : Array α)
--     (start₁ start₂ end₂ : ℕ)
--     (start₁_lt_start₂ : start₁ < start₂)
--     (start₂_lt_end₂ : start₂ < end₂)
--     (end₂_le_arr_size : end₂ ≤ arr.size)
--     (arr_size_eq_aux_size : arr.size = aux.size)
--     : (mergeAdjacentChunksIntoAux
--         (arr := arr)
--         (aux := aux)
--         (start₁ := start₁)
--         (start₂ := start₂)
--         (end₂ := end₂)
--         (start₁_lt_start₂ := start₁_lt_start₂)
--         (start₂_lt_end₂ := start₂_lt_end₂)
--         (end₂_le_arr_size := end₂_le_arr_size)
--         (arr_size_eq_aux_size := arr_size_eq_aux_size)
--       ).size = aux.size :=
--   sorry

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
        have aux'_def
            : aux' =
              mergeAdjacentChunksIntoAux
                arr
                aux
                start₁
                start₂
                end₂
                start₁_lt_start₂
                start₂_lt_end₂
                end₂_le_arr_size
                arr_size_eq_aux_size := by
          rfl
        have h := mergeAdjacentChunksIntoAux_size_eq
                    arr
                    aux
                    start₁
                    start₂
                    end₂
                    start₁_lt_start₂
                    start₂_lt_end₂
                    end₂_le_arr_size
                    arr_size_eq_aux_size
        rw [aux'_def, h]
        exact arr_size_eq_aux_size
      loop₁ aux' start₁'
        arr_size_eq_aux'_size
    else
      let rec loop₂ (aux : Array α) (start₁ : ℕ)
          : Array α :=
        if start₁ < arr.size then
          have : start₁ < arr.size := by sorry
          have chunkStart₁_lt_aux_size : start₁ < aux.size := by sorry
          let aux' := aux.set ⟨start₁, chunkStart₁_lt_aux_size⟩ arr[start₁]
          let start₁' := start₁ + 1
          loop₂ aux' start₁'
        else
          aux
      loop₂ aux start₁
  loop₁ aux start₁
    arr_size_eq_aux_size

-- @[specialize] def Array.mergeSort [Inhabited α] [Ord α] (arr : Array α) : Array α := Id.run do
--   let mut arr := arr
--   let mut aux : Array α := Array.mkArray arr.size default
--   let mut chunkSize := 1
--   let mut auxIsAux := true
--   while chunkSize < arr.size do
--     if auxIsAux then
--       aux := mergeChunksIntoAux arr aux chunkSize
--     else
--       arr := mergeChunksIntoAux aux arr chunkSize
--     chunkSize := chunkSize * 2
--     auxIsAux := !auxIsAux
--   if auxIsAux then
--     pure arr
--   else
--     pure aux

-- -- #eval mergeChunksIntoAux #[3, 2, 1] #[0, 0, 0] 1
-- -- #eval #[15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1].mergeSort

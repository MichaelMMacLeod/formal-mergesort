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

structure M₂ (α : Type) extends M₁ α where
  i : ℕ
  k₁ : ℕ
  k₂ : ℕ
  i_def : i = k₁ + k₂ - start₂
  k₂_ge_start₂ : k₂ ≥ start₂
  k₁_lt_start₂_succ : k₁ < start₂.succ
  k₂_lt_end₂_succ : k₂ < end₂.succ
  k₂_lt_end₂_of_not_k₁_lt_start₂ : ¬k₁ < start₂ → k₂ < end₂

structure M₃ (α : Type) extends M₂ α where
  k₁_k₂_in_bounds : k₁ < start₂ ∧ k₂ < end₂
  k₁_lt_arr_size : k₁ < arr.size
  k₂_lt_arr_size : k₂ < arr.size
  i_lt_aux_size : i < aux.size

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

def mergeAdjacentChunksIntoAux [Ord α] (m₁ : M₁ α) : M₁ α :=
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
  let rec loop (m₂ : M₂ α) : M₁ α :=
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
      let rec loopLeft (m₄Left : M₄Left α) : M₁ α :=
        if k₁_lt_start₂ : m₄Left.k₁ < m₄Left.start₂ then
          loopLeft (m₄Left.next k₁_lt_start₂)
        else
          { m₄Left with }
      termination_by m₄Left.start₂ - m₄Left.k₁
      decreasing_by
        simp_wf
        have start₂_def : (m₄Left.next k₁_lt_start₂).start₂ = m₄Left.start₂ := by rfl
        have k₁_def : (m₄Left.next k₁_lt_start₂).k₁ = m₄Left.k₁.succ := by rfl
        omega
      loopLeft (m₂.mkM₄Left k₁_lt_start₂)
    else
      let rec loopRight (m₄Right : M₄Right α) : M₁ α :=
        if k₂_lt_end₂ : m₄Right.k₂ < m₄Right.end₂ then
          loopRight (m₄Right.next k₂_lt_end₂)
        else
          { m₄Right with }
      termination_by m₄Right.end₂ - m₄Right.k₂
      decreasing_by
        simp_wf
        have end₂_def : (m₄Right.next k₂_lt_end₂).end₂ = m₄Right.end₂ := by rfl
        have k₂_def : (m₄Right.next k₂_lt_end₂).k₂ = m₄Right.k₂.succ := by rfl
        omega
      loopRight (m₂.mkM₄Right k₁_lt_start₂)
  termination_by m₂.arr.size - m₂.i
  decreasing_by
    all_goals
      have i_lt_arr_size : m₂.i < m₂.arr.size := by
        rw [m₂.arr_size_eq_aux_size]
        exact (m₂.mkM₃ k₁_k₂_in_bounds).i_lt_aux_size
      exact (Nat.sub_succ_lt_sub_of_lt i_lt_arr_size)
  loop m₂

theorem M₄Left.next_arr_eq
    [Ord α]
    {m₄Left : M₄Left α}
    (k₁_lt_start₂ : m₄Left.k₁ < m₄Left.start₂)
    : (m₄Left.next k₁_lt_start₂).arr = m₄Left.arr := by rfl

theorem merge_adjacent_loopLeft_arr_eq
    [Ord α]
    {m₄Left : M₄Left α}
    : (mergeAdjacentChunksIntoAux.loop.loopLeft m₄Left).arr = m₄Left.arr := by
  unfold mergeAdjacentChunksIntoAux.loop.loopLeft
  if k₁_lt_start₂ : m₄Left.k₁ < m₄Left.start₂ then
    simp [k₁_lt_start₂]
    have := m₄Left.next_arr_eq
    exact (merge_adjacent_loopLeft_arr_eq (m₄Left := m₄Left.next k₁_lt_start₂))
  else
    simp [k₁_lt_start₂]
termination_by m₄Left.start₂ - m₄Left.k₁
decreasing_by
  simp_wf
  have start₂_def : (m₄Left.next k₁_lt_start₂).start₂ = m₄Left.start₂ := by rfl
  have k₁_def : (m₄Left.next k₁_lt_start₂).k₁ = m₄Left.k₁.succ := by rfl
  omega

theorem M₄Right.next_arr_eq
    [Ord α]
    {m₄Right : M₄Right α}
    (k₂_lt_end₂ : m₄Right.k₂ < m₄Right.end₂)
    : (m₄Right.next k₂_lt_end₂).arr = m₄Right.arr := by rfl

theorem merge_adjacent_loopRight_arr_eq
    [Ord α]
    {m₄Right : M₄Right α}
    : (mergeAdjacentChunksIntoAux.loop.loopRight m₄Right).arr = m₄Right.arr := by
  unfold mergeAdjacentChunksIntoAux.loop.loopRight
  if k₂_lt_end₂ : m₄Right.k₂ < m₄Right.end₂ then
    simp [k₂_lt_end₂]
    have := m₄Right.next_arr_eq
    exact (merge_adjacent_loopRight_arr_eq (m₄Right := m₄Right.next k₂_lt_end₂))
  else
    simp [k₂_lt_end₂]
termination_by m₄Right.end₂ - m₄Right.k₂
decreasing_by
  simp_wf
  have end₂_def : (m₄Right.next k₂_lt_end₂).end₂ = m₄Right.end₂ := by rfl
  have k₂_def : (m₄Right.next k₂_lt_end₂).k₂ = m₄Right.k₂.succ := by rfl
  omega

theorem M₂.mkM₄Left_arr_eq
    [Ord α]
    {m₂ : M₂ α}
    {k₁_lt_start₂ : m₂.k₁ < m₂.start₂}
    : (m₂.mkM₄Left k₁_lt_start₂).arr = m₂.arr := by
  rfl

theorem M₂.mkM₄Right_arr_eq
    [Ord α]
    {m₂ : M₂ α}
    {not_k₁_lt_start₂ : ¬m₂.k₁ < m₂.start₂}
    : (m₂.mkM₄Right not_k₁_lt_start₂).arr = m₂.arr := by
  rfl

theorem merge_adjacent_loop_arr_eq
    [Ord α]
    {m₂ : M₂ α}
    : (mergeAdjacentChunksIntoAux.loop m₂).arr = m₂.arr := by
  unfold mergeAdjacentChunksIntoAux.loop
  if k₁_k₂_in_bounds : m₂.k₁ < m₂.start₂ ∧ m₂.k₂ < m₂.end₂ then
    simp [k₁_k₂_in_bounds]
    split
    . case h_1 =>
      have : (m₂.mkM₃ k₁_k₂_in_bounds).nextLeft.arr = m₂.arr := by rfl
      exact (merge_adjacent_loop_arr_eq (m₂ := (m₂.mkM₃ k₁_k₂_in_bounds).nextLeft))
    . case h_2 =>
      have : (m₂.mkM₃ k₁_k₂_in_bounds).nextLeft.arr = m₂.arr := by rfl
      exact (merge_adjacent_loop_arr_eq (m₂ := (m₂.mkM₃ k₁_k₂_in_bounds).nextLeft))
    . case h_3 =>
      have : (m₂.mkM₃ k₁_k₂_in_bounds).nextRight.arr = m₂.arr := by rfl
      exact (merge_adjacent_loop_arr_eq (m₂ := (m₂.mkM₃ k₁_k₂_in_bounds).nextRight))
  else
    simp [k₁_k₂_in_bounds]
    split
    . case isTrue =>
        simp [merge_adjacent_loopLeft_arr_eq, M₂.mkM₄Left_arr_eq]
    . case isFalse =>
        simp [merge_adjacent_loopRight_arr_eq, M₂.mkM₄Right_arr_eq]
termination_by m₂.arr.size - m₂.i
decreasing_by
  all_goals
    have i_lt_arr_size : m₂.i < m₂.arr.size := by
      rw [m₂.arr_size_eq_aux_size]
      exact (m₂.mkM₃ k₁_k₂_in_bounds).i_lt_aux_size
    exact (Nat.sub_succ_lt_sub_of_lt i_lt_arr_size)

theorem merge_adjacent_arr_eq
    [Ord α]
    {m₁ : M₁ α}
    : (mergeAdjacentChunksIntoAux m₁).arr = m₁.arr := by
  simp [mergeAdjacentChunksIntoAux, merge_adjacent_loop_arr_eq]

theorem M₄Left.next_aux_size_eq_arr
    [Ord α]
    {m₄Left : M₄Left α}
    (k₁_lt_start₂ : m₄Left.k₁ < m₄Left.start₂)
    : (m₄Left.next k₁_lt_start₂).aux.size = m₄Left.arr.size := by
  simp [M₄Left.next, m₄Left.arr_size_eq_aux_size]

theorem merge_adjacent_loopLeft_aux_size_eq_arr
    [Ord α]
    {m₄Left : M₄Left α}
    : (mergeAdjacentChunksIntoAux.loop.loopLeft m₄Left).aux.size = m₄Left.arr.size := by
  unfold mergeAdjacentChunksIntoAux.loop.loopLeft
  if k₁_lt_start₂ : m₄Left.k₁ < m₄Left.start₂ then
    simp [k₁_lt_start₂]
    have := m₄Left.next_arr_eq
    exact (merge_adjacent_loopLeft_aux_size_eq_arr (m₄Left := m₄Left.next k₁_lt_start₂))
  else
    simp [k₁_lt_start₂, m₄Left.arr_size_eq_aux_size]
termination_by m₄Left.start₂ - m₄Left.k₁
decreasing_by
  simp_wf
  have start₂_def : (m₄Left.next k₁_lt_start₂).start₂ = m₄Left.start₂ := by rfl
  have k₁_def : (m₄Left.next k₁_lt_start₂).k₁ = m₄Left.k₁.succ := by rfl
  omega

theorem M₄Right.next_aux_size_eq_arr
    [Ord α]
    {m₄Right : M₄Right α}
    (k₂_lt_end₂ : m₄Right.k₂ < m₄Right.end₂)
    : (m₄Right.next k₂_lt_end₂).aux.size = m₄Right.arr.size := by
  simp [M₄Right.next, m₄Right.arr_size_eq_aux_size]

theorem merge_adjacent_loopRight_aux_size_eq_arr
    [Ord α]
    {m₄Right : M₄Right α}
    : (mergeAdjacentChunksIntoAux.loop.loopRight m₄Right).aux.size = m₄Right.arr.size := by
  unfold mergeAdjacentChunksIntoAux.loop.loopRight
  if k₂_lt_end₂ : m₄Right.k₂ < m₄Right.end₂ then
    simp [k₂_lt_end₂]
    have := m₄Right.next_arr_eq
    exact (merge_adjacent_loopRight_aux_size_eq_arr (m₄Right := m₄Right.next k₂_lt_end₂))
  else
    simp [k₂_lt_end₂, m₄Right.arr_size_eq_aux_size]
termination_by m₄Right.end₂ - m₄Right.k₂
decreasing_by
  simp_wf
  have end₂_def : (m₄Right.next k₂_lt_end₂).end₂ = m₄Right.end₂ := by rfl
  have k₂_def : (m₄Right.next k₂_lt_end₂).k₂ = m₄Right.k₂.succ := by rfl
  omega

theorem merge_adjacent_loop_aux_size_eq_arr
    [Ord α]
    {m₂ : M₂ α}
    : (mergeAdjacentChunksIntoAux.loop m₂).aux.size = m₂.arr.size := by
  unfold mergeAdjacentChunksIntoAux.loop
  if k₁_k₂_in_bounds : m₂.k₁ < m₂.start₂ ∧ m₂.k₂ < m₂.end₂ then
    simp [k₁_k₂_in_bounds]
    split
    . case h_1 =>
      have : (m₂.mkM₃ k₁_k₂_in_bounds).nextLeft.aux.size = m₂.aux.size := by
        simp [M₂.mkM₃, M₃.nextLeft]
      exact (merge_adjacent_loop_aux_size_eq_arr (m₂ := (m₂.mkM₃ k₁_k₂_in_bounds).nextLeft))
    . case h_2 =>
      have : (m₂.mkM₃ k₁_k₂_in_bounds).nextLeft.aux.size = m₂.aux.size := by
        simp [M₂.mkM₃, M₃.nextLeft]
      exact (merge_adjacent_loop_aux_size_eq_arr (m₂ := (m₂.mkM₃ k₁_k₂_in_bounds).nextLeft))
    . case h_3 =>
      have : (m₂.mkM₃ k₁_k₂_in_bounds).nextRight.aux.size = m₂.aux.size := by
        simp [M₂.mkM₃, M₃.nextRight]
      exact (merge_adjacent_loop_aux_size_eq_arr (m₂ := (m₂.mkM₃ k₁_k₂_in_bounds).nextRight))
  else
    simp [k₁_k₂_in_bounds]
    split
    . case isTrue =>
        simp [merge_adjacent_loopLeft_aux_size_eq_arr, M₂.mkM₄Left]
    . case isFalse =>
        simp [merge_adjacent_loopRight_aux_size_eq_arr, M₂.mkM₄Right]
termination_by m₂.arr.size - m₂.i
decreasing_by
  all_goals
    have i_lt_arr_size : m₂.i < m₂.arr.size := by
      rw [m₂.arr_size_eq_aux_size]
      exact (m₂.mkM₃ k₁_k₂_in_bounds).i_lt_aux_size
    exact (Nat.sub_succ_lt_sub_of_lt i_lt_arr_size)

theorem merge_adjacent_aux_size_eq_arr
    [Ord α]
    {m₁ : M₁ α}
    : (mergeAdjacentChunksIntoAux m₁).aux.size = m₁.arr.size := by
  simp [mergeAdjacentChunksIntoAux, merge_adjacent_loop_aux_size_eq_arr]

structure M₅ (α : Type) where
  arr : Array α
  aux : Array α
  size : ℕ
  start₁ : ℕ
  arr_size_eq_aux_size : arr.size = aux.size
  size_gt_0 : size > 0

def M₅.next
    [Ord α]
    (m₅ : M₅ α)
    (start₁_plus_size_lt_arr_size : m₅.start₁ + m₅.size < m₅.arr.size)
    : M₅ α :=
  let start₂ := m₅.start₁ + m₅.size
  let end₂ := min (start₂ + m₅.size) m₅.arr.size
  have start₁_lt_start₂ : m₅.start₁ < start₂ := by
    have := m₅.size_gt_0
    omega
  have start₂_lt_end₂ : start₂ < end₂ := by
    simp [end₂]
    apply And.intro
    . case left =>
      exact m₅.size_gt_0
    . case right =>
      exact start₁_plus_size_lt_arr_size
  have end₂_le_arr_size : end₂ ≤ m₅.arr.size := by omega
  let m₁ : M₁ α :=
    { m₅ with
      start₂,
      end₂,
      start₁_lt_start₂,
      start₂_lt_end₂,
      end₂_le_arr_size,
    }
  let m₁' : M₁ α := mergeAdjacentChunksIntoAux m₁
  have arr_size_eq_m₁'_aux_size : m₁'.arr.size = m₁'.aux.size := by
    simp [m₁', merge_adjacent_aux_size_eq_arr, merge_adjacent_arr_eq]
  { arr := m₁'.arr
    aux := m₁'.aux
    size := m₅.size
    start₁ := m₅.start₁ + 2 * m₅.size
    arr_size_eq_aux_size := arr_size_eq_m₁'_aux_size
    size_gt_0 := m₅.size_gt_0
  }

def M₅.nextFinal
    [Ord α]
    (m₅ : M₅ α)
    (start₁_lt_aux_size : m₅.start₁ < m₅.aux.size)
    : M₅ α :=
    have start₁_lt_arr_size : m₅.start₁ < m₅.arr.size := by
      rw [m₅.arr_size_eq_aux_size]
      exact start₁_lt_aux_size
    let aux' := m₅.aux.set ⟨m₅.start₁, start₁_lt_aux_size⟩ m₅.arr[m₅.start₁]
    have arr_size_eq_aux'_size := by
      simp [aux']
      exact m₅.arr_size_eq_aux_size
  { m₅ with
    aux := aux'
    start₁ := m₅.start₁.succ
    arr_size_eq_aux_size := arr_size_eq_aux'_size
  }

def mergeChunksIntoAux
    [Ord α]
    (arr aux : Array α)
    (size : ℕ)
    (arr_size_eq_aux_size : arr.size = aux.size)
    (size_gt_0 : size > 0)
    : Array α :=
  let rec loop (m₅ : M₅ α) : Array α :=
    if start₁_plus_size_lt_arr_size : m₅.start₁ + m₅.size < m₅.arr.size then
      loop (m₅.next start₁_plus_size_lt_arr_size)
    else
      let rec loopFinal (m₅ : M₅ α) : Array α :=
        if start₁_lt_aux_size : m₅.start₁ < m₅.aux.size then
          loopFinal (m₅.nextFinal start₁_lt_aux_size)
        else
          m₅.aux
      termination_by m₅.arr.size - m₅.start₁
      decreasing_by
        simp_wf
        have : (m₅.nextFinal start₁_lt_aux_size).arr.size = m₅.arr.size := by
          rfl
        have : (m₅.nextFinal start₁_lt_aux_size).start₁ = m₅.start₁.succ := by
          rfl
        have := m₅.arr_size_eq_aux_size
        omega
      loopFinal m₅
  termination_by m₅.arr.size - m₅.start₁
  decreasing_by
    simp_wf
    have : (m₅.next start₁_plus_size_lt_arr_size).arr.size = m₅.arr.size := by
      have : (m₅.next start₁_plus_size_lt_arr_size).arr = m₅.arr := by
        simp [M₅.next]
        exact (merge_adjacent_arr_eq)
      simp [*]
    have : (m₅.next start₁_plus_size_lt_arr_size).start₁ = m₅.start₁ + 2 * m₅.size := by
      simp [M₅.next]
    have := m₅.size_gt_0
    omega
  let m₅ : M₅ α :=
    { arr,
      aux,
      size,
      start₁ := 0,
      arr_size_eq_aux_size,
      size_gt_0,
    }
  loop m₅

theorem mergeChunksIntoAux.loop.loopFinal_size_eq_arr_size
    [Ord α]
    { arr aux : Array α}
    { arr_size_eq_aux_size : arr.size = aux.size }
    { start₁ : ℕ}
    : (mergeChunksIntoAux.loop.loopFinal
        arr
        aux
        start₁
        arr_size_eq_aux_size
      ).size = arr.size := by
  unfold mergeChunksIntoAux.loop.loopFinal
  sorry

theorem mergeChunksIntoAux.loop_size_eq_arr_size
    [Ord α]
    { arr aux : Array α}
    { chunkSize : ℕ }
    { arr_size_eq_aux_size : arr.size = aux.size }
    { chunkSize_gt_0 : chunkSize > 0 }
    { start₁ : ℕ}
    : (mergeChunksIntoAux.loop
        arr
        aux
        chunkSize
        arr_size_eq_aux_size
        chunkSize_gt_0
        aux
        start₁
        arr_size_eq_aux_size
      ).size = arr.size := by
  unfold mergeChunksIntoAux.loop
  if start₁_plus_size_lt_arr_size : start₁ + chunkSize < arr.size then
    simp only [start₁_plus_size_lt_arr_size]
    exact (mergeChunksIntoAux.loop_size_eq_arr_size
            )
  else
    simp [
      start₁_plus_size_lt_arr_size,
      mergeChunksIntoAux.loop.loopFinal_size_eq_arr_size
    ]

theorem mergeChunksIntoAux_size_eq_arr_size
    [Ord α]
    { arr aux : Array α}
    { chunkSize : ℕ }
    { arr_size_eq_aux_size : arr.size = aux.size }
    { chunkSize_gt_0 : chunkSize > 0 }
    : (mergeChunksIntoAux
        arr
        aux
        chunkSize
        arr_size_eq_aux_size
        chunkSize_gt_0
      ).size = arr.size := by
  unfold mergeChunksIntoAux
  let rec mergeChunksIntoAux.loop_size_eq_arr_size
      { start₁ : ℕ}
      : (mergeChunksIntoAux.loop
          arr
          aux
          chunkSize
          arr_size_eq_aux_size
          chunkSize_gt_0
          aux
          start₁
          arr_size_eq_aux_size
        ).size = arr.size := by
    unfold mergeChunksIntoAux.loop

  simp [mergeChunksIntoAux.loop_size_eq_arr_size]


def Array.mergeSort [Inhabited α] [Ord α] (arr : Array α) : Array α := Id.run do
  let rec loop
      (arr aux : Array α)
      (chunkSize : ℕ)
      (chunkSize_gt_0 : chunkSize > 0)
      (arr_size_eq_aux_size : arr.size = aux.size)
      : Array α :=
    if chunkSize < arr.size then
      let aux' := mergeChunksIntoAux arr aux chunkSize arr_size_eq_aux_size chunkSize_gt_0
      have aux'_size_eq_arr_size : aux'.size = arr.size := by
        simp [aux', mergeChunksIntoAux_size_eq_arr_size]
      have chunkSize_mul_2_gt_0 : chunkSize * 2 > 0 := by simp [*]
      loop aux' arr (chunkSize * 2) chunkSize_mul_2_gt_0 aux'_size_eq_arr_size
    else
      arr
  termination_by arr.size - chunkSize
  decreasing_by
    simp_wf
    simp [mergeChunksIntoAux_size_eq_arr_size]
    omega
  let initialChunkSize := 1
  let aux : Array α := Array.mkArray arr.size default
  have initialChunkSize_gt_0 : initialChunkSize > 0 := by decide
  have arr_size_eq_aux_size : arr.size = aux.size := by simp [aux]
  loop arr aux 1 initialChunkSize_gt_0 arr_size_eq_aux_size

#eval #[1, 2, 3, 4, 5, 4, 3, 2, 1].mergeSort
#eval #[15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1].mergeSort

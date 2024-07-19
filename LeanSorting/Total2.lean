import Mathlib.Data.Nat.ModEq

theorem Nat.lt_of_lt_le {a b c : ℕ} (h : a < b) : b ≤ c → a < c := by omega
theorem Nat.lt_of_le_lt {a b c : ℕ} (h : a ≤ b) : b < c → a < c := by omega
theorem Nat.sub_succ_lt_sub_of_lt {a b : ℕ} (h : a < b) : b - a.succ < b - a := by omega

variable
  {α : Type}
  [Ord α]
  (arr aux : Array α)
  (start₁ start₂ end₂ i k₁ k₂ : ℕ)

structure H₁ : Prop where
  start₁_lt_start₂ : start₁ < start₂
  start₂_lt_end₂ : start₂ < end₂
  end₂_le_arr_size : end₂ ≤ arr.size
  arr_size_eq_aux_size : arr.size = aux.size

structure H₂ extends H₁ arr aux start₁ start₂ end₂ : Prop where
  i_def : i = k₁ + k₂ - start₂
  k₂_ge_start₂ : k₂ ≥ start₂
  k₁_lt_start₂_succ : k₁ < start₂.succ
  k₂_lt_end₂_succ : k₂ < end₂.succ

structure H₃ extends H₂ arr aux start₁ start₂ end₂ i k₁ k₂ : Prop where
  k₁_k₂_in_bounds : k₁ < start₂ ∧ k₂ < end₂
  k₁_lt_arr_size : k₁ < arr.size
  k₂_lt_arr_size : k₂ < arr.size
  i_lt_aux_size : i < aux.size

def H₂.mkH₃
    (h₂ : H₂ arr aux start₁ start₂ end₂ i k₁ k₂)
    (k₁_k₂_in_bounds : k₁ < start₂ ∧ k₂ < end₂)
    : H₃ arr aux start₁ start₂ end₂ i k₁ k₂ :=
  have k₁_lt_arr_size := by
    apply And.left at k₁_k₂_in_bounds
    have start₂_lt_arr_size := Nat.lt_of_lt_le h₂.start₂_lt_end₂ h₂.end₂_le_arr_size
    exact (Nat.lt_trans k₁_k₂_in_bounds start₂_lt_arr_size)
  have k₂_lt_arr_size := by
    apply And.right at k₁_k₂_in_bounds
    exact (Nat.lt_of_lt_le k₁_k₂_in_bounds h₂.end₂_le_arr_size)
  have i_lt_aux_size := by
    have := h₂.i_def
    have := h₂.arr_size_eq_aux_size
    omega
  { h₂ with
    k₁_k₂_in_bounds
    k₁_lt_arr_size
    k₂_lt_arr_size
    i_lt_aux_size
  }

def H₃.nextLeft
    (h₃ : H₃ arr aux start₁ start₂ end₂ i k₁ k₂)
    : H₂ arr (aux.set ⟨i, h₃.i_lt_aux_size⟩ (arr[k₁]'h₃.k₁_lt_arr_size)) start₁ start₂ end₂ i.succ k₁.succ k₂ :=
  have i_succ_def : i.succ = k₁.succ + k₂ - start₂ := by
    have := h₃.i_def
    have := h₃.k₂_ge_start₂
    omega
  have k₁_succ_lt_start₂_succ : k₁.succ < start₂.succ := by
    have := h₃.k₁_k₂_in_bounds
    omega
  have arr_size_eq_aux'_size : arr.size = (aux.set ⟨i, h₃.i_lt_aux_size⟩ (arr[k₁]'h₃.k₁_lt_arr_size)).size := by
    simp
    exact h₃.arr_size_eq_aux_size
  { h₃ with
    arr_size_eq_aux_size := arr_size_eq_aux'_size
    i_def := i_succ_def
    k₁_lt_start₂_succ := k₁_succ_lt_start₂_succ
  }

def H₃.nextRight
    (h₃ : H₃ arr aux start₁ start₂ end₂ i k₁ k₂)
    : H₂ arr (aux.set ⟨i, h₃.i_lt_aux_size⟩ (arr[k₂]'h₃.k₂_lt_arr_size)) start₁ start₂ end₂ i.succ k₁ k₂.succ :=
  have := h₃.k₂_lt_arr_size
  have arr_size_eq_aux'_size : arr.size = (aux.set ⟨i, h₃.i_lt_aux_size⟩ (arr[k₂]'h₃.k₂_lt_arr_size)).size := by
    simp
    exact h₃.arr_size_eq_aux_size
  have i_succ_def : i.succ = k₁ + k₂.succ - start₂ := by
    have := h₃.i_def
    have := h₃.k₂_ge_start₂
    omega
  have k₂_succ_lt_end₂_succ : k₂.succ < end₂.succ := by
    have := h₃.k₁_k₂_in_bounds
    omega
  have k₂_succ_ge_start₂ : k₂.succ ≥ start₂ := by
    have := h₃.k₂_ge_start₂
    omega
  { h₃ with
    arr_size_eq_aux_size := arr_size_eq_aux'_size
    i_def := i_succ_def
    k₂_lt_end₂_succ := k₂_succ_lt_end₂_succ
    k₂_ge_start₂ := k₂_succ_ge_start₂
  }

def H₂.mk_i_lt_aux_size
    (h₂ : H₂ arr aux start₁ start₂ end₂ i k₁ k₂)
    (k₁_lt_start₂ : k₁ < start₂)
    : i < aux.size := by
  have := h₂.start₂_lt_end₂
  have := h₂.end₂_le_arr_size
  have := h₂.arr_size_eq_aux_size
  have := h₂.i_def
  have := h₂.k₂_lt_end₂_succ
  omega

def H₂.mk_k₁_lt_arr_size
    (h₂ : H₂ arr aux start₁ start₂ end₂ i k₁ k₂)
    (k₁_lt_start₂ : k₁ < start₂)
    : k₁ < arr.size := by
  have := h₂.start₂_lt_end₂
  have := h₂.end₂_le_arr_size
  omega

def H₂.nextLeft [Ord α]
    (h₂ : H₂ arr aux start₁ start₂ end₂ i k₁ k₂)
    (k₁_lt_start₂ : k₁ < start₂)
    : ( have i_lt_aux_size : i < aux.size := h₂.mk_i_lt_aux_size k₁_lt_start₂
        have k₁_lt_arr_size : k₁ < arr.size := h₂.mk_k₁_lt_arr_size k₁_lt_start₂
        H₂ arr (aux.set ⟨i, i_lt_aux_size⟩ (arr[k₁]'k₁_lt_arr_size)) start₁ start₂ end₂ i.succ k₁.succ k₂
      ) :=
  have i_lt_aux_size : i < aux.size := h₂.mk_i_lt_aux_size k₁_lt_start₂
  have k₁_lt_arr_size : k₁ < arr.size := h₂.mk_k₁_lt_arr_size k₁_lt_start₂
  let arr_size_eq_aux'_size : arr.size = (aux.set ⟨i, i_lt_aux_size⟩ (arr[k₁]'k₁_lt_arr_size)).size := by
    simp []
    exact h₂.arr_size_eq_aux_size
  have i_succ_def : i.succ = k₁.succ + k₂ - start₂ := by
    have := h₂.i_def
    have := h₂.k₂_ge_start₂
    omega
  have k₁_succ_lt_start₂_succ : k₁.succ < start₂.succ := by
    omega
  { h₂ with
    arr_size_eq_aux_size := arr_size_eq_aux'_size
    i_def := i_succ_def
    k₁_lt_start₂_succ := k₁_succ_lt_start₂_succ
  }


structure H₄Right extends H₁ arr aux start₁ start₂ end₂ : Prop where
  i_def : i = k₁ + k₂ - start₂
  k₂_ge_start₂ : k₂ ≥ start₂
  k₁_lt_start₂_succ : k₁ < start₂.succ
  not_k₁_lt_start₂ : ¬k₁ < start₂

def H₂.mkH₄Right
    (h₂ : H₂ arr aux start₁ start₂ end₂ i k₁ k₂)
    (not_k₁_lt_start₂ : ¬k₁ < start₂)
    : H₄Right arr aux start₁ start₂ end₂ i k₁ k₂ :=
  { h₂ with not_k₁_lt_start₂ }

def H₄Right.mk_i_lt_aux_size
    (h₄Right : H₄Right arr aux start₁ start₂ end₂ i k₁ k₂)
    (k₂_lt_end₂ : k₂ < end₂)
    : i < aux.size := by
  have := h₄Right.end₂_le_arr_size
  have := h₄Right.arr_size_eq_aux_size
  have := h₄Right.i_def
  have := h₄Right.k₁_lt_start₂_succ
  omega

def H₄Right.mk_k₂_lt_arr_size
    (h₄Right : H₄Right arr aux start₁ start₂ end₂ i k₁ k₂)
    (k₂_lt_end₂ : k₂ < end₂)
    : k₂ < arr.size := by
  have := h₄Right.end₂_le_arr_size
  omega

def H₄Right.next
    (h₄Right : H₄Right arr aux start₁ start₂ end₂ i k₁ k₂)
    (k₂_lt_end₂ : k₂ < end₂)
    : have i_lt_aux_size := h₄Right.mk_i_lt_aux_size k₂_lt_end₂
      have k₂_lt_arr_Size := h₄Right.mk_k₂_lt_arr_size k₂_lt_end₂
      let aux' := aux.set ⟨i, i_lt_aux_size⟩ arr[k₂]
      H₄Right arr aux' start₁ start₂ end₂ i.succ k₁ k₂.succ
    := by
  intro i_lt_aux_size k₂_lt_arr_size aux'
  have arr_size_eq_aux'_size : arr.size = aux'.size := by
    simp [aux']
    exact h₄Right.arr_size_eq_aux_size
  have i_succ_def : i.succ = k₁ + k₂.succ - start₂ := by
    have := h₄Right.i_def
    have := h₄Right.k₂_ge_start₂
    omega
  have k₂_succ_ge_start₂ : k₂.succ ≥ start₂ := by
    have := h₄Right.k₂_ge_start₂
    omega
  exact
    { h₄Right with
      arr_size_eq_aux_size := arr_size_eq_aux'_size
      i_def := i_succ_def
      k₂_ge_start₂ := k₂_succ_ge_start₂
    }

def mergeAdjacentChunksIntoAux.loop.loopLeft_decreasing
    (k₁_lt_start₂ : k₁ < start₂)
    : start₂ - (k₁ + 1) < start₂ - k₁ := by
  omega

def mergeAdjacentChunksIntoAux.loop.loopLeft.loopRight_decreasing
    (k₂_lt_end₂ : k₂ < end₂)
    : end₂ - (k₂ + 1) < end₂ - k₂ := by
  omega

@[specialize, inline]
def mergeAdjacentChunksIntoAux
    (h₁ : H₁ arr aux start₁ start₂ end₂)
    : Array α :=
  -- Copy the lowest element from the left and right regions until one of them is fully copied.
  let rec @[specialize] loop
      (aux : Array α)
      (i k₁ k₂ : ℕ)
      (h₂ : H₂ arr aux start₁ start₂ end₂ i k₁ k₂)
      : Array α :=
    if k₁_k₂_in_bounds : k₁ < start₂ ∧ k₂ < end₂ then
      have h₃ := h₂.mkH₃ k₁_k₂_in_bounds
      have : k₁ < arr.size := h₃.k₁_lt_arr_size
      have : k₂ < arr.size := h₃.k₂_lt_arr_size
      match Ord.compare arr[k₁] arr[k₂] with
      | .lt | .eq =>
        let aux' := aux.set ⟨i, h₃.i_lt_aux_size⟩ arr[k₁]
        loop aux' i.succ k₁.succ k₂ h₃.nextLeft
      | .gt =>
        let aux' := aux.set ⟨i, h₃.i_lt_aux_size⟩ arr[k₂]
        loop aux' i.succ k₁ k₂.succ h₃.nextRight
    else
      -- If the left region is not yet empty, finish copying it.
      let rec @[specialize] loopLeft
          (aux : Array α)
          (i k₁ : ℕ)
          (h₂ : H₂ arr aux start₁ start₂ end₂ i k₁ k₂)
          : Array α :=
        if k₁_lt_start₂ : k₁ < start₂ then
          have : k₁ < arr.size := h₂.mk_k₁_lt_arr_size k₁_lt_start₂
          have i_lt_aux_size : i < aux.size := h₂.mk_i_lt_aux_size k₁_lt_start₂
          let aux' := aux.set ⟨i, i_lt_aux_size⟩ arr[k₁]
          loopLeft aux' i.succ k₁.succ (h₂.nextLeft k₁_lt_start₂)
        else
          -- If the right region is not yet empty, finish copying it.
          let rec @[specialize] loopRight
              (aux : Array α)
              (i k₂ : ℕ)
              (h₄Right : H₄Right arr aux start₁ start₂ end₂ i k₁ k₂)
              : Array α :=
            if k₂_lt_end₂ : k₂ < end₂ then
              have : k₂ < arr.size := h₄Right.mk_k₂_lt_arr_size k₂_lt_end₂
              have i_lt_aux_size : i < aux.size := h₄Right.mk_i_lt_aux_size k₂_lt_end₂
              let aux' := aux.set ⟨i, i_lt_aux_size⟩ arr[k₂]
              loopRight aux' i.succ k₂.succ (h₄Right.next k₂_lt_end₂)
            else
              aux
          -- These termination proofs can be automatically inferred, but stating
          -- them explicitly makes this function compile a lot faster.
          termination_by end₂ - k₂
          decreasing_by exact mergeAdjacentChunksIntoAux.loop.loopLeft.loopRight_decreasing end₂ k₂ k₂_lt_end₂
          loopRight aux i k₂ (h₂.mkH₄Right k₁_lt_start₂)
      termination_by start₂ - k₁
      decreasing_by exact mergeAdjacentChunksIntoAux.loop.loopLeft_decreasing start₂ k₁ k₁_lt_start₂
      loopLeft aux i k₁ h₂
  termination_by arr.size - i
  decreasing_by
    all_goals
      have i_lt_arr_size : i < arr.size := by
        rw [h₂.arr_size_eq_aux_size]
        exact (h₂.mkH₃ k₁_k₂_in_bounds).i_lt_aux_size
      exact (Nat.sub_succ_lt_sub_of_lt i_lt_arr_size)
  let h₂ :=
    { h₁ with
      i_def := Nat.eq_sub_of_add_eq rfl
      k₂_ge_start₂ := Nat.le_refl start₂
      k₁_lt_start₂_succ := Nat.lt_succ_of_lt h₁.start₁_lt_start₂
      k₂_lt_end₂_succ := Nat.lt_succ_of_lt h₁.start₂_lt_end₂
    }
  loop aux start₁ start₁ start₂ h₂

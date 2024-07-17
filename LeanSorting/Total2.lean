import Mathlib.Data.Nat.ModEq

-- variable
--   (arr aux : Array α)
--   (start₁ start₂ end₂ i k₁ k₂ : ℕ)

structure H₁
  {α : Type}
  (arr aux : Array α)
  (start₁ start₂ end₂ : ℕ)
where
  start₁_lt_start₂ : start₁ < start₂
  start₂_lt_end₂ : start₂ < end₂
  end₂_le_arr_size : end₂ ≤ arr.size
  arr_size_eq_aux_size : arr.size = aux.size

structure H₂
  {α : Type}
  (arr aux : Array α)
  (start₁ start₂ end₂ : ℕ)
  (i k₁ k₂ : ℕ)
  extends H₁ arr aux start₁ start₂ end₂
where
  i_def : i = k₁ + k₂ - start₂
  k₂_ge_start₂ : k₂ ≥ start₂
  k₁_lt_start₂_succ : k₁ < start₂.succ
  k₂_lt_end₂_succ : k₂ < end₂.succ

def H₂.nextLeft
    [Ord α]
    (arr aux : Array α)
    (start₁ start₂ end₂ : ℕ)
    (i k₁ k₂ : ℕ)
    (h₂ : H₂ arr aux start₁ start₂ end₂ i k₁ k₂ )
    (k₁_lt_start₂ : k₁ < start₂)
    : H₂  :=
  have i_lt_aux_size : h₂.i < h₂.aux.size := by
    have := h₂.start₂_lt_end₂
    have := h₂.end₂_le_arr_size
    have := h₂.arr_size_eq_aux_size
    have := h₂.i_def
    have := h₂.k₂_lt_end₂_succ
    omega
  have k₁_lt_arr_size : h₂.k₁ < h₂.arr.size := by
    have := h₂.start₂_lt_end₂
    have := h₂.end₂_le_arr_size
    omega
  let aux' := h₂.aux.set ⟨h₂.i, i_lt_aux_size⟩ h₂.arr[h₂.k₁]
  let arr_size_eq_aux'_size : h₂.arr.size = aux'.size := by
    simp [aux']
    exact h₂.arr_size_eq_aux_size
  have i_succ_def : h₂.i.succ = h₂.k₁.succ + h₂.k₂ - h₂.start₂ := by
    have := h₂.i_def
    have := h₂.k₂_ge_start₂
    omega
  have k₁_succ_lt_start₂_succ : h₂.k₁.succ < h₂.start₂.succ := by
    omega
  { h₂ with
    aux := aux'
    arr_size_eq_aux_size := arr_size_eq_aux'_size
    k₁ := h₂.k₁.succ
    i := h₂.i.succ
    i_def := i_succ_def
    k₁_lt_start₂_succ := k₁_succ_lt_start₂_succ
  }

@[specialize, inline]
partial def mergeAdjacentChunksIntoAux
    [Inhabited α]
    [Ord α]
    (arr aux : Array α)
    (start₁ start₂ end₂ : ℕ)
    : Array α :=
  -- Copy the lowest element from the left and right regions until one of them is fully copied.
  let rec @[specialize] loop
      (aux : Array α)
      (i k₁ k₂ : ℕ)
      (h₂ : H₂ α)
      : Array α :=
    if k₁_k₂_in_bounds : k₁ < start₂ ∧ k₂ < end₂ then
      have : k₁ < arr.size := sorry
      have : k₂ < arr.size := sorry
      have i_lt_aux_size : i < aux.size := sorry
      match Ord.compare arr[k₁] arr[k₂] with
      | .lt | .eq =>
        let aux' := aux.set ⟨i, i_lt_aux_size⟩ arr[k₁]
        loop aux' i.succ k₁.succ k₂ h₂.nextLeft
      | .gt =>
        let aux' := aux.set ⟨i, i_lt_aux_size⟩ arr[k₂]
        loop aux' i.succ k₁ k₂.succ h₂.nextRight
    else
      -- If the left region is not yet empty, finish copying it.
      let rec @[specialize] loopLeft
          (aux : Array α)
          (i k₁ : ℕ)
          : Array α :=
        if k₁ < start₂ then
          have : k₁ < arr.size := sorry
          have i_lt_aux_size : i < aux.size := sorry
          let aux' := aux.set ⟨i, i_lt_aux_size⟩ arr[k₁]
          loopLeft aux' i.succ k₁.succ
        else
          -- If the right region is not yet empty, finish copying it.
          let rec @[specialize] loopRight
              (aux : Array α)
              (i k₂ : ℕ)
              : Array α :=
            if k₂ < end₂ then
              have : k₂ < arr.size := sorry
              have i_lt_aux_size : i < aux.size := sorry
              let aux' := aux.set ⟨i, i_lt_aux_size⟩ arr[k₂]
              loopRight aux' i.succ k₂.succ
            else
              aux
          loopRight aux i k₂
      loopLeft aux i k₁
  loop aux start₁ start₁ start₂

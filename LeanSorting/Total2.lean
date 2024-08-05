import Mathlib.Data.Nat.ModEq

theorem Nat.lt_of_lt_le {a b c : ℕ} (h : a < b) : b ≤ c → a < c := by omega
theorem Nat.lt_of_le_lt {a b c : ℕ} (h : a ≤ b) : b < c → a < c := by omega
theorem Nat.sub_succ_lt_sub_of_lt {a b : ℕ} (h : a < b) : b - a.succ < b - a := by omega

variable
  {α : Type}
  [Ord α]
  (arr aux : Array α)
  (start₁ start₂ end₂ i k₁ k₂ chunkSize : ℕ)

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
    : have i_lt_aux_size := h₃.i_lt_aux_size
      have k₁_lt_arr_size := h₃.k₁_lt_arr_size
      have aux' := aux.set ⟨i, i_lt_aux_size⟩ arr[k₁]
      H₂ arr aux' start₁ start₂ end₂ i.succ k₁.succ k₂ := by
  intro i_lt_aux_size k₁_lt_arr_size aux'
  have i_succ_def : i.succ = k₁.succ + k₂ - start₂ := by
    have := h₃.i_def
    have := h₃.k₂_ge_start₂
    omega
  have k₁_succ_lt_start₂_succ : k₁.succ < start₂.succ := by
    have := h₃.k₁_k₂_in_bounds
    omega
  have arr_size_eq_aux'_size : arr.size = aux'.size := by
    simp [aux']
    exact h₃.arr_size_eq_aux_size
  exact
    { h₃ with
      arr_size_eq_aux_size := arr_size_eq_aux'_size
      i_def := i_succ_def
      k₁_lt_start₂_succ := k₁_succ_lt_start₂_succ
    }

def H₃.nextRight
    (h₃ : H₃ arr aux start₁ start₂ end₂ i k₁ k₂)
    : have i_lt_aux_size := h₃.i_lt_aux_size
      have k₂_lt_arr_size := h₃.k₂_lt_arr_size
      have aux' := aux.set ⟨i, i_lt_aux_size⟩ arr[k₂]
      H₂ arr aux' start₁ start₂ end₂ i.succ k₁ k₂.succ := by
  intro i_lt_aux_size k₂_lt_arr_size aux'
  have arr_size_eq_aux'_size : arr.size = aux'.size := by
    simp [aux']
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
  exact
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

def H₂.nextLeft
    (h₂ : H₂ arr aux start₁ start₂ end₂ i k₁ k₂)
    (k₁_lt_start₂ : k₁ < start₂)
    : have i_lt_aux_size : i < aux.size := h₂.mk_i_lt_aux_size k₁_lt_start₂
      have k₁_lt_arr_size : k₁ < arr.size := h₂.mk_k₁_lt_arr_size k₁_lt_start₂
      have aux' := aux.set ⟨i, i_lt_aux_size⟩ arr[k₁]
      H₂ arr aux' start₁ start₂ end₂ i.succ k₁.succ k₂
    := by
  intro i_lt_aux_size k₁_lt_arr_size aux'
  let arr_size_eq_aux'_size : arr.size = aux'.size := by
    simp [aux']
    exact h₂.arr_size_eq_aux_size
  have i_succ_def : i.succ = k₁.succ + k₂ - start₂ := by
    have := h₂.i_def
    have := h₂.k₂_ge_start₂
    omega
  have k₁_succ_lt_start₂_succ : k₁.succ < start₂.succ := by
    omega
  exact
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
      have k₁_lt_arr_size : k₁ < arr.size := h₃.k₁_lt_arr_size
      have k₂_lt_arr_size : k₂ < arr.size := h₃.k₂_lt_arr_size
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

structure H₅ : Prop where
  arr_size_eq_aux_size : arr.size = aux.size
  chunkSize_gt_0 : chunkSize > 0

def H₅.mkH₁
    (h₅ : H₅ arr aux chunkSize)
    (start₁_plus_chunkSize_lt_arr_size : start₁ + chunkSize < arr.size)
    : have start₂' := start₁ + chunkSize
      have end₂' := min (start₂' + chunkSize) arr.size
      H₁ arr aux start₁ start₂' end₂'
    := by
  intro start₂' end₂'
  have start₁_lt_start₂ : start₁ < start₂' := by
    have := h₅.chunkSize_gt_0
    omega
  have start₂_lt_end₂ : start₂' < end₂' := by
    simp [end₂']
    apply And.intro
    . case left =>
      exact h₅.chunkSize_gt_0
    . case right =>
      exact start₁_plus_chunkSize_lt_arr_size
  have end₂_le_arr_size : end₂' ≤ arr.size := by omega
  exact {
    h₅ with
    start₁_lt_start₂,
    start₂_lt_end₂,
    end₂_le_arr_size
  }

theorem mergeAdjacentChunksIntoAux.loop.loopLeft.loopRight_size_eq
    {aux : Array α}
    {i k₂ : ℕ}
    {h₄Right : H₄Right arr aux start₁ start₂ end₂ i k₁ k₂}
    : have aux' := mergeAdjacentChunksIntoAux.loop.loopLeft.loopRight arr start₁ start₂ end₂ k₁ aux i k₂ h₄Right
      arr.size = aux'.size
    := by
  unfold loopRight
  if k₂_lt_end₂ : k₂ < end₂ then
    simp [k₂_lt_end₂]
    exact mergeAdjacentChunksIntoAux.loop.loopLeft.loopRight_size_eq
  else
    simp [k₂_lt_end₂, h₄Right.arr_size_eq_aux_size]

theorem mergeAdjacentChunksIntoAux.loop.loopLeft_size_eq
    {aux : Array α}
    {i k₁ : ℕ}
    {h₂ : H₂ arr aux start₁ start₂ end₂ i k₁ k₂}
    : have aux' := mergeAdjacentChunksIntoAux.loop.loopLeft arr start₁ start₂ end₂ k₂ aux i k₁ h₂
      arr.size = aux'.size
    := by
  unfold loopLeft
  if k₂_lt_start₂ : k₁ < start₂ then
    simp [k₂_lt_start₂]
    exact mergeAdjacentChunksIntoAux.loop.loopLeft_size_eq
  else
    simp [k₂_lt_start₂, ← mergeAdjacentChunksIntoAux.loop.loopLeft.loopRight_size_eq]

theorem mergeAdjacentChunksIntoAux.loop_size_eq
    {aux : Array α}
    {i k₁ k₂ : ℕ}
    {h₂ : H₂ arr aux start₁ start₂ end₂ i k₁ k₂}
    : have aux' := mergeAdjacentChunksIntoAux.loop arr start₁ start₂ end₂ aux i k₁ k₂ h₂
      arr.size = aux'.size
    := by
  unfold loop
  if k₁_k₂_in_bounds : k₁ < start₂ ∧ k₂ < end₂ then
    simp [k₁_k₂_in_bounds]
    split <;> rw [← mergeAdjacentChunksIntoAux.loop_size_eq]
  else
    simp [k₁_k₂_in_bounds, ← mergeAdjacentChunksIntoAux.loop.loopLeft_size_eq]
termination_by aux.size - i
decreasing_by
  all_goals
    simp_wf
    have h₃ := h₂.mkH₃ k₁_k₂_in_bounds
    have i_lt_aux_size : i < aux.size := h₃.i_lt_aux_size
    exact loop.loopLeft.loopRight_decreasing aux.size i i_lt_aux_size

theorem mergeAdjacentChunksIntoAux_size_eq
    {aux : Array α}
    {h₁ : H₁ arr aux start₁ start₂ end₂}
    : have aux' := mergeAdjacentChunksIntoAux arr aux start₁ start₂ end₂ h₁
      arr.size = aux'.size
    := by
  unfold mergeAdjacentChunksIntoAux
  exact mergeAdjacentChunksIntoAux.loop_size_eq arr start₁ start₂ end₂

def H₅.next
    {chunkSize : ℕ}
    (h₅ : H₅ arr aux chunkSize)
    (start₁_plus_chunkSize_lt_arr_size : start₁ + chunkSize < arr.size)
    : let start₂' := start₁ + chunkSize
      have start₂'_def : start₂' = start₁ + chunkSize := by rfl
      let end₂' := min (start₂' + chunkSize) arr.size
      have end₂'_def : end₂' = min (start₂' + chunkSize) arr.size := by rfl
      have h₁ : H₁ arr aux start₁ start₂' end₂' := by
        have h₁ := h₅.mkH₁ arr aux start₁ chunkSize start₁_plus_chunkSize_lt_arr_size
        simp at h₁
        simp [start₂'_def, end₂'_def]
        exact h₁
      have aux' := mergeAdjacentChunksIntoAux arr aux start₁ start₂' end₂' h₁
      H₅ arr aux' chunkSize
    := by
  intro start₂' start₂'_def end₂' end₂'_def h₁ aux'
  have arr_size_eq_aux'_size : arr.size = aux'.size := by
    simp [aux']
    exact mergeAdjacentChunksIntoAux_size_eq arr start₁ start₂' end₂'
  exact {
    h₅ with
    arr_size_eq_aux_size := arr_size_eq_aux'_size,
  }

def H₅.nextFinal
    (h₅ : H₅ arr aux chunkSize)
    (start₁_lt_aux_size : start₁ < aux.size)
    : have := h₅.arr_size_eq_aux_size
      let aux' := aux.set ⟨start₁, start₁_lt_aux_size⟩ arr[start₁]
      H₅ arr aux' chunkSize
    := by
  intro arr_size_eq_aux_size aux'
  have arr_size_eq_aux'_size : arr.size = aux'.size := by
    simp [aux', h₅.arr_size_eq_aux_size]
  exact {
    h₅ with
    arr_size_eq_aux_size := arr_size_eq_aux'_size
  }

@[specialize, inline]
def mergeChunksIntoAux (h₅ : H₅ arr aux chunkSize) :=
  -- Merge every two adjacent chunks while the second chunk has at least one
  -- element.
  let rec @[specialize] loop
      (aux : Array α)
      (start₁ : ℕ)
      (h₅ : H₅ arr aux chunkSize)
      : Array α :=
    if start₁_plus_chunkSize_lt_arr_size : start₁ + chunkSize < arr.size then
      let start₂ := start₁ + chunkSize
      let end₂ := min (start₂ + chunkSize) arr.size
      have h₁ := h₅.mkH₁ arr aux start₁ chunkSize start₁_plus_chunkSize_lt_arr_size
      let aux' := mergeAdjacentChunksIntoAux arr aux start₁ start₂ end₂ h₁
      have h₅ := h₅.next arr aux start₁ start₁_plus_chunkSize_lt_arr_size
      loop aux' (start₁ + 2 * chunkSize) h₅
    else
      -- Copy any leftover elements directly to `aux`.
      --
      -- This can happen, for example, when calling this function with
      --       `arr  := #[1, 2, 3, 10, 20, 30, 100, 200]`
      --   and `size := 3`,
      -- as the first loop with merge `#[1, 2, 3]` and `#[20, 30, 100]` together, but
      -- because there are too few leftover elements to form two adjacent chunks,
      -- it is unable to do any further merging. Thus, the leftover elements, `100`
      -- and `200`, must be directly copied over into `aux`.
      let rec @[specialize] loopFinal
          (aux : Array α)
          (start₁ : ℕ)
          (h₅ : H₅ arr aux chunkSize)
          : Array α :=
        if start₁_lt_aux_size : start₁ < aux.size then
          have := h₅.arr_size_eq_aux_size
          let aux' := aux.set ⟨start₁, start₁_lt_aux_size⟩ arr[start₁]
          have h₅ := h₅.nextFinal arr aux start₁ chunkSize start₁_lt_aux_size
          loopFinal aux' start₁.succ h₅
        else
          aux
      termination_by arr.size - start₁
      decreasing_by sorry
      loopFinal aux start₁ h₅
  termination_by arr.size - start₁
  decreasing_by sorry
  loop aux 0 h₅

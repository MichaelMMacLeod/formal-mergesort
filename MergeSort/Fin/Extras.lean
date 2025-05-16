theorem Fin.add_one_le_of_lt
    {a b : Fin (2 ^ System.Platform.numBits)}
    (h : a < b)
    : a + 1 ≤ b := by
  cases System.Platform.numBits_eq
  case inl hs | inr hs =>
    revert a b h
    rw [hs]
    intro a b h
    simp only [Nat.reducePow] at a b
    show a + 1 ≤ b
    omega

theorem Fin.add_one_sub_add_ge_of_mid_lt_of_ge
    {a b c d : Fin (2 ^ System.Platform.numBits)}
    (h1 : a + b - a ≥ c)
    (h2 : b < d)
    : a + b - a + 1 ≥ c := by
  cases System.Platform.numBits_eq
  case inl h | inr h =>
    revert a b c d h1 h2
    rw [h]
    intro a b c d h1 h2
    simp only [Nat.reducePow] at *
    omega

theorem Fin.add_one_ge_of_lt_of_ge
    {a b c : Fin (2 ^ System.Platform.numBits)}
    (h1 : a ≥ b)
    (h2 : a < c)
    : a + 1 ≥ b := by
  cases System.Platform.numBits_eq
  case inl h | inr h =>
    revert a b c h1 h2
    rw [h]
    intro a b c h1 h2
    simp only [Nat.reducePow] at *
    omega

theorem Fin.sub_add_lt_of_and_lt_lt
    {a b c d : Fin (2 ^ System.Platform.numBits)}
    (h1 : b ≥ c)
    (h2 : a < c ∧ b < d)
    : a + b - c < d := by
  cases System.Platform.numBits_eq
  case inl h | inr h =>
    revert a b c d h1 h2
    rw [h]
    intro a b c d h1 h2
    simp only [Nat.reducePow] at *
    omega

theorem Fin.ptr₁_lt_size
    {α : Type}
    {arr : Array α}
    {mid high ptr₁ ptr₂ i arrUsize : Fin (2 ^ System.Platform.numBits)}
    (i_lt_high : i < high)
    (ptr₁_le_mid : ptr₁ ≤ mid)
    (ptr₂_ge_mid : ptr₂ ≥ mid)
    (i_def : i = ptr₁ + ptr₂ - mid)
    (arr_size_lt_usize_size : arr.size < USize.size)
    (high_le_size : high ≤ arrUsize)
    : ptr₁ < arrUsize := by
  cases System.Platform.numBits_eq
  case inl h | inr h =>
    revert high_le_size arr_size_lt_usize_size i_def ptr₂_ge_mid ptr₁_le_mid
      i_lt_high arrUsize i ptr₂ ptr₁ high mid
    rw [h]
    intro mid high ptr₁ ptr₂ i arrUsize i_lt_high ptr₁_le_mid ptr₂_ge_mid
      i_def arr_size_lt_usize_size high_le_size
    simp only [Nat.reducePow] at *
    omega

theorem Fin.succ_eq_succ_add_sub_of_add_sub
    {mid ptr₁ ptr₂ i : Fin (2 ^ System.Platform.numBits)}
    (i_def : i = ptr₁ + ptr₂ - mid)
    : i + 1 = (ptr₁ + 1) + ptr₂ - mid := by
  cases System.Platform.numBits_eq
  case inl h | inr h =>
    revert i_def i ptr₂ ptr₁ mid
    rw [h]
    intro mid ptr₁ ptr₂ i i_def
    simp only [Nat.reducePow] at *
    omega

theorem Fin.succ_eq_add_succ_sub_of_add_sub
    {mid ptr₁ ptr₂ i : Fin (2 ^ System.Platform.numBits)}
    (i_def : i = ptr₁ + ptr₂ - mid)
    : i + 1 = ptr₁ + (ptr₂ + 1) - mid := by
  cases System.Platform.numBits_eq
  case inl h | inr h =>
    revert i_def i ptr₂ ptr₁ mid
    rw [h]
    intro mid ptr₁ ptr₂ i i_def
    simp only [Nat.reducePow] at *
    omega

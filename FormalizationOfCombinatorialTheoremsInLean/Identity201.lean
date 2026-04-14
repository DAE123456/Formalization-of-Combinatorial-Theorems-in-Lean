import Mathlib


variable {α β α' β' γ  γ' : ℝ }



noncomputable def arrayAux  (n k : ℤ) :=
    if n < 0 ∨ k < 0 ∨ k > n then 0
    else
    if n = 0 ∧ k = 0 then 1
    else
    if n = 0 ∧ k ≠ 0 then 0
    else
      (α * (n-1) + β * k + γ) * arrayAux (n - 1) k +  (α' * (n-1) + β' * (k - 1) + γ') * arrayAux (n - 1) (k - 1) + if (n = 0 ∧ k = 0) then 1 else 0
  termination_by n.toNat
  decreasing_by
    simp
    rename_i H1 H2
    simp_all
    . omega
    . simp_all
      omega


lemma arrayAux_neg_eq_zero  (n : ℕ)  : arrayAux (n - 1) (0 - 1 : ℤ) (β := β) (β' := β') (γ := γ) (α := α) (α' := α') (γ' := γ') = 0 := by
  unfold arrayAux
  simp

lemma arrayAux_le_eq_zero (n : ℕ) : arrayAux (n - 1) n (β := β) (β' := β') (γ := γ) (α := α) (α' := α') (γ' := γ') = 0 := by
  unfold arrayAux
  simp

lemma arrayAux_zero_eq_one : arrayAux 0 0 (β := β) (β' := β') (γ := γ) (α := α) (α' := α') (γ' := γ') = 1 := by
  unfold arrayAux
  simp



lemma sum_range_arrayAux_trans (n : ℕ) (h : β + β'= 0) (hn : n > 0) : ∑ k ∈ Finset.range (n + 1), arrayAux n k (β := β) (β' := β') (γ := γ) (α := α) (α' := α') (γ' := γ') =
  ((α + α') * (n - 1) + γ + γ') * ∑ k ∈ Finset.range n, arrayAux (n - 1) k (β := β) (β' := β') (γ := γ) (α := α) (α' := α') (γ' := γ') := by
  unfold arrayAux
  simp_all
  calc
    _ = ∑ k ∈ Finset.range (n + 1), ((α * (n - 1) + β * k + γ) * arrayAux (n - 1) k (β := β) (β' := β') + (α' * (n - 1) + β' * (k - 1) + γ') * arrayAux (n - 1) (k - 1)) := by
      refine' Finset.sum_congr rfl (fun k hk => _)
      simp_all
      split_ifs
      . omega
      . omega
      . omega
      . rfl
    _ = ∑ k ∈ Finset.range (n + 1), (α * (n - 1) + β * k + γ) * arrayAux (n - 1) k (β := β) (β' := β') + ∑ k ∈ Finset.range (n + 1), (α' * (n - 1) + β' * (k - 1) + γ') * arrayAux (n - 1) (k - 1)  := by
      rw [Finset.sum_add_distrib]
    _ = ∑ k ∈ Finset.Ico 1 (n + 1 + 1), (α * (n - 1) + β * (k - 1) + γ) * arrayAux (n - 1) (k - 1) (β := β) (β' := β') + ∑ k ∈ Finset.range (n + 1), (α' * (n - 1) + β' * (k - 1) + γ') * arrayAux (n - 1) (k - 1)  := by
      rw [Finset.sum_Ico_eq_sum_range]; simp
      congr 1
    _ = (α * (n - 1) + β * (0 - 1) + γ) * arrayAux (n - 1) (0 - 1) (β := β) (β' := β') (γ := γ) (α := α) (α' := α') (γ' := γ') + ∑ k ∈ Finset.Ico 1 (n + 1), (α * (n - 1) + β * (k - 1) + γ) * arrayAux (n - 1) (k - 1) (β := β) (β' := β')  + ∑ k ∈  Finset.range (n + 1), (α' * (n - 1) + β' * (k - 1) + γ') * arrayAux (n - 1) (k - 1) (β := β) (β' := β') := by
      obtain hl := arrayAux_neg_eq_zero n
      obtain hp := arrayAux_le_eq_zero n
      rw [hl]; simp
      rw [Finset.sum_Ico_succ_top]; simp
      rw [hp]; simp
      rfl
      linarith
    _ = ∑ k ∈ Finset.range (n + 1), (α * (n - 1) + β * (k - 1) + γ) * arrayAux (n - 1) (k - 1) (β := β) (β' := β') + ∑ k ∈  Finset.range (n + 1), (α' * (n - 1) + β' * (k - 1) + γ') * arrayAux (n - 1) (k - 1) (β := β) (β' := β') := by
      symm
      rw [← Finset.sum_range_add_sum_Ico (m := 1)]
      simp
      obtain hl := arrayAux_neg_eq_zero n
      simp at hl
      rw [hl]
      simp
    _ = ∑ k ∈ Finset.range (n + 1),(((α + α') * (n - 1) + (β + β') * (k - 1) + γ + γ') * arrayAux (n - 1) (k - 1)) := by
      rw [← Finset.sum_add_distrib]
      congr 1; ext k
      rw [add_mul, add_mul, add_mul, add_mul, add_mul, add_mul, add_mul, add_mul, add_mul, add_mul, add_mul]
      ring
    _ = ∑ k ∈ Finset.range (n + 1),(((α + α') * (n - 1) + γ + γ') * arrayAux (n - 1) (k - 1)) := by
      rw [h]; simp
      rfl
    _ = ((α + α') * (n - 1) + γ + γ') * ∑ k ∈ Finset.range (n + 1), arrayAux (n - 1) (k - 1) := by
      rw [Finset.mul_sum]
    _ = ((α + α') * (n - 1) + γ + γ') * ∑ k ∈ Finset.range n, arrayAux (n - 1) k := by
      rw [Finset.sum_range_succ']
      obtain hl := arrayAux_neg_eq_zero n
    -- norm_num
      simp_all
      left
      rw [hl]
      linarith
  symm
  simp; left
  apply Finset.sum_congr rfl
  intro k hk
  split_ifs
  . simp_all
    omega
  . simp_all
    rw [arrayAux_zero_eq_one]
  . simp_all
    omega
  . simp_all
    conv_rhs => unfold arrayAux
    split_ifs
    . simp_all
      omega
    . simp_all
    . omega
    . simp_all



theorem idt_201  (n : ℕ) (h : β + β'= 0) :
    ∑ k ∈ Finset.range (n + 1), arrayAux n k (β := β) (β' := β') (γ := γ) (α := α) (α' := α') (γ' := γ') = ∏ i ∈ Finset.range n, ((α + α') * i + γ + γ') := by
  rcases Decidable.em (n > 0) with (h0 | h0)
  . induction' n with n ih generalizing α β α' β' γ γ'
    . simp_all
    rcases Decidable.em (n > 0) with (h1 | h1)
    . have l0 : n > 0 := by linarith
      obtain ih' := ih (α := α) (β := β) (α' := α') (β' := β') (γ := γ) (γ' := γ') (h := h)
      obtain H := sum_range_arrayAux_trans (n := n + 1) (α := α) (β := β) (α' := α') (β' := β') (γ := γ) (γ' := γ') (h := h)
      rw [Finset.prod_range_succ, ← ih']
      rw [H]; simp
      rw [mul_comm]
      . linarith
      . linarith
    . simp_all
      rw [Finset.sum_range_succ']
      simp
      unfold arrayAux
      simp
      rw [arrayAux_zero_eq_one]
      unfold arrayAux
      simp
      ring
  . simp_all
    rw [arrayAux_zero_eq_one]

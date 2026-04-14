
import Mathlib


--variable {x : Type} [AddCommMonoid x] [TopologicalSpace x]
variable {x : ℝ}
variable {n : ℕ}

--variable [AddCommMonoid x] [TopologicalSpace x]

lemma one_add_sqrt_x : (1 + x.sqrt) ^ n =
    ∑ k ∈ Finset.range (n + 1), n.choose k * (x.sqrt) ^ k := by
  rw [add_comm, add_pow];simp
  apply Finset.sum_congr rfl
  intro k hk
  rw [mul_comm]


lemma one_asub_sqrt_x : (1 - x.sqrt) ^ n =
    ∑ k ∈ Finset.range (n + 1), n.choose k * (- x.sqrt) ^ k := by
  rw [sub_eq_add_neg, add_comm, add_pow];simp
  apply Finset.sum_congr rfl
  intro k hk
  rw [mul_comm]


lemma add_pow_sub_add_neg_pow : (1 + x.sqrt) ^ n - (1 - x.sqrt) ^ n =
  ∑ k ∈ Finset.range (n + 1), if Odd k then 2 * n.choose k * (x.sqrt) ^ k else 0 := by
  rw [one_add_sqrt_x, one_asub_sqrt_x]
  rw [← Finset.sum_sub_distrib]
  conv_lhs => enter [2]; ext k; rw [← mul_sub, neg_eq_neg_one_mul]
  conv_lhs => enter [2]; ext k; enter [2, 2]; rw [mul_pow]
  congr 1; ext k
  split_ifs with h
  . rw [Odd.neg_one_pow]
    nth_rw 1 [← one_mul (a := x.sqrt ^ k), ← sub_mul];simp
    rw [one_add_one_eq_two]
    linarith
    exact h
  . nth_rw 1 [← one_mul (a := x.sqrt ^ k)]
    rw [Even.neg_one_pow]
    simp only [one_mul, sub_self, mul_zero]
    rw [Nat.not_odd_iff_even] at h
    exact h



theorem Odd_binomial_Generating (hx : x > 0) : ∑' (k : ℕ), n.choose (2 * k + 1) * x ^ k
         = 1 / (2 * x.sqrt) * ((1 + x.sqrt) ^ n - (1 - x.sqrt) ^ n) := by

  rw [add_pow_sub_add_neg_pow]
  rw [mul_comm]
  rw [← mul_left_inj' (c := x.sqrt)]
  rw [mul_assoc, ← div_div, div_mul_cancel₀]
  simp
  rw [tsum_eq_sum (s := Finset.range (n / 2 + 1))]
  rcases Decidable.em (Odd n) with H | H
  . let T := (Finset.range (n / 2 + 1)).image (λ i =>  2 * i + 1)

    have l0 : (x.sqrt) ^ (1 : ℕ) = (x.sqrt) ^ (1 : ℝ) := by simp
    have step1 : ∑ i ∈  Finset.range (n / 2 + 1), n.choose (2 * i + 1) * x ^ i =
      ∑ k ∈ T, n.choose k * (x.sqrt) ^ k * (x.sqrt) ^ (-1 :ℝ):= by
      simp [T]
      conv_rhs => enter [2]; ext i; rw [mul_assoc];enter [2];rw [← Real.rpow_natCast]
      norm_num
      conv_rhs => enter [2]; ext i; rw [← Real.rpow_add (hx := by simp; omega) (x := x.sqrt)  (y := 2 * i+ 1) (z := (-1 : ℝ ))]
      simp_all
      congr 1
      ext k
      simp
      left
      rw [Real.rpow_mul]
      · simp
        rw [Real.sq_sqrt (by linarith)]
      · simp
    rw [step1]
    rw [Finset.sum_mul]
    conv_lhs => enter [2]; ext i; rw [mul_assoc]; enter [2, 2]; rw [← pow_one (a := x.sqrt), l0]
    rw [← Real.rpow_add (x := x.sqrt) (y := -1) (z := 1)]
    simp
    rw [← mul_left_inj' (c := 2 ^ 1)]; simp
    rw [Finset.sum_mul]
    have hT : T = (Finset.range (n + 1)).filter (λ k => Odd k):= by
      ext x
      simp only [T, Finset.mem_filter, Finset.mem_range, Finset.mem_image]
      constructor
      . rintro ⟨a, ⟨i, hi, rfl⟩⟩
        constructor
        apply Nat.le_of_lt_add_one at i
        apply Nat.mul_le_mul_left 2 at i
        nth_rw 2 [mul_comm] at i
        apply Nat.add_le_add_right (k := 1) at i
        rw [Nat.div_two_mul_two_add_one_of_odd] at i
        . linarith
        . exact H
        . simp
      . rintro ⟨h1, h2⟩
        use (x - 1) / 2
        constructor

        rw [← Nat.mul_lt_mul_right (a := 2)]
        rw [add_mul, Nat.div_two_mul_two_of_even]
        simp
        . omega
        . rw [Nat.even_sub']
          constructor
          . simp only [odd_one, implies_true]
          . simp
            exact h2
          . have hx : x ≥  1 := by
              obtain h := Nat.eq_zero_or_pos x
              . simp_all
                rcases h with h₁ | h₂
                . simp_all
                . linarith
            exact hx
        . linarith
        . ring_nf
          rw [Nat.div_mul_cancel]
          rw [add_comm, Nat.sub_add_cancel]
          obtain h := Nat.eq_zero_or_pos x
          . simp_all
            rcases h with h₁ | h₂
            . simp_all
            . linarith
          . rw [← even_iff_two_dvd]
            rw [Nat.even_sub']
            constructor
            . simp only [odd_one, implies_true]
            . simp
              exact h2
            . obtain h := Nat.eq_zero_or_pos x
              simp_all
              rcases h with h₁ | h₂
              . simp_all
              . linarith
    . rw  [hT, Finset.sum_filter]
      simp_all
      congr 1 ;ext k
      split_ifs
      . ring
      . simp
    . simp
    . simp
      exact hx
  . let T := (Finset.range (n / 2)).image (λ i =>  2 * i + 1)
    have l0 : (x.sqrt) ^ (1 : ℕ) = (x.sqrt) ^ (1 : ℝ) := by simp
    have step1 : ∑ i ∈ Finset.range (n / 2 + 1), n.choose (2 * i + 1) * x ^ i = ∑ k ∈  T, n.choose k * (x.sqrt) ^ k * (x.sqrt) ^ (-1 :ℝ):= by
      simp [T]

      rw [Finset.sum_range_add]
      simp
      rw [Nat.two_mul_div_two_of_even];simp
      · conv_rhs => enter [2]; ext i; rw [mul_assoc];enter [2];rw [← Real.rpow_natCast]
        norm_num
        conv_rhs => enter [2]; ext i; rw [← Real.rpow_add (hx := by simp; omega) (x := x.sqrt)  (y := 2 * i+ 1) (z := (-1 : ℝ ))]
        simp_all
        congr 1
        ext k

        simp
        left

        rw [Real.rpow_mul]

        ·
          simp_all
          rw [Real.sq_sqrt (by linarith)]
        · simp

      simp at H
      omega

    rw [step1]
    rw [Finset.sum_mul]
    conv_lhs => enter [2]; ext i; rw [mul_assoc]; enter [2, 2]; rw [← pow_one (a := x.sqrt), l0]
    rw [← Real.rpow_add (x := x.sqrt) (y := -1) (z := 1)]
    simp
    rw [← mul_left_inj' (c := 2 ^ 1)]; simp
    rw [Finset.sum_mul]
    have hT : T = (Finset.range (n + 1)).filter (λ k => Odd k):= by
      ext x
      simp only [T, Finset.mem_filter, Finset.mem_range, Finset.mem_image]
      constructor
      . rintro ⟨a, ⟨i, hi, rfl⟩⟩
        constructor
        simp
        simp_all
        rw [← Nat.mul_lt_mul_left (a := 2)] at i
        rw [Nat.two_mul_div_two_of_even] at i
        · omega

        . exact H
        . simp
        . simp

      . rintro ⟨h1, h2⟩
        use (x - 1) / 2
        constructor
        rw [← Nat.mul_lt_mul_right (a := 2)]
        rw [Nat.div_two_mul_two_of_even, Nat.div_two_mul_two_of_even]
        rw [← Nat.add_one_lt_add_one_iff]
        rw [Nat.sub_add_cancel]
        exact h1
        have hx : x ≥  1 := by
          obtain h := Nat.eq_zero_or_pos x
          . simp_all
            rcases h with h₁ | h₂
            . simp_all
            . linarith
        . exact hx
        . simp_all
        . rw [Nat.even_sub']
          constructor
          . simp only [odd_one, implies_true]
          . simp
            exact h2
          . obtain h := Nat.eq_zero_or_pos x
            simp_all
            rcases h with h₁ | h₂
            . simp_all
            . linarith
        . linarith
        . ring_nf
          rw [Nat.div_mul_cancel]
          rw [add_comm, Nat.sub_add_cancel]
          obtain h := Nat.eq_zero_or_pos x
          . simp_all
            rcases h with h₁ | h₂
            . simp_all
            . linarith
          . rw [← even_iff_two_dvd]
            rw [Nat.even_sub']
            constructor
            . simp only [odd_one, implies_true]
            . simp
              exact h2
            . obtain h := Nat.eq_zero_or_pos x
              simp_all
              rcases h with h₁ | h₂
              . simp_all
              . linarith
    . rw  [hT, Finset.sum_filter]
      simp_all
      congr 1 ;ext k
      split_ifs
      . ring
      . simp
    . simp
    . simp
      exact hx
  . simp
    intro b hb
    left
    rw [Nat.choose_eq_zero_iff]
    apply Nat.mul_le_mul_left 2 at hb
    rcases Decidable.em (Even n) with h | h
    . rw [mul_comm, Nat.succ_eq_one_add,add_mul, Nat.div_two_mul_two_of_even] at hb
      simp_all
      . omega
      . simp_all
    . rw [mul_comm, Nat.succ_eq_one_add, add_mul] at hb
      apply Nat.lt_add_one_iff.2
      simp at hb
      simp_all
      --conv at hb =>
      rw [← Nat.one_add_div_two_mul_two_of_odd (h := h) (n := n)]
      omega
  . rw [Real.sqrt_ne_zero]
    linarith
    linarith
  . rw [Real.sqrt_ne_zero]
    linarith
    linarith

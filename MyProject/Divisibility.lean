import MyProject

namespace my

-- CHAPTER 1

theorem comm_eq_one (a b : ℤ) (h₁ : a + b = 1) : b + a = 1 := by
  rw[add_comm] at h₁
  exact h₁

-- CHAPTER 2

section
variable {R : Type*} [CommSemiring R]
variable {a b c d x y : R}

-- SECTION 2.1

lemma dvd_reflex : a ∣ a := by
  use 1
  rw[mul_one]

lemma dvd_mul_right : a ∣ a * b := by
  use b

lemma dvd_mul_left : a ∣ b * a := by
  rw[mul_comm]
  exact my.dvd_mul_right

lemma dvd_mul_right_general (h₁ : a ∣ b) : a ∣ b * x := by
  rcases h₁ with ⟨c, h₁⟩
  rw[h₁, mul_assoc]
  exact my.dvd_mul_right

lemma dvd_mul_left_general (h₁ : a ∣ b) : a ∣ x * b := by
  rw[mul_comm]
  exact my.dvd_mul_right_general h₁

lemma prod_left_dvd (h₁ : a * b ∣ c) : a ∣ c := by
  rcases h₁ with ⟨x, h₁⟩
  rw[h₁, mul_assoc]
  exact my.dvd_mul_right

lemma prod_right_dvd (h₁ : a * b ∣ c) : b ∣ c := by
  rw[mul_comm] at h₁
  exact my.prod_left_dvd h₁

lemma prod_left_right_dvd (h₁ : a * b ∣ c) : a ∣ c ∧ b ∣ c := by
  constructor
  · exact my.prod_left_dvd h₁
  · exact my.prod_right_dvd h₁
  -- Alternatively, exact ⟨my.prod_left_dvd h₁, my.prod_right_dvd h₁⟩

theorem dvd_trans (h₁ : a ∣ b) (h₂ : b ∣ c) :  a ∣ c := by
  rcases h₁ with ⟨x, h₁⟩
  rcases h₂ with ⟨y, h₂⟩
  rw[h₂, h₁, mul_assoc]
  exact my.dvd_mul_right

theorem mul_dvd_mul (h₁ : a ∣ b) (h₂ : c ∣ d) : a * c ∣ b * d := by
  rcases h₁ with ⟨x, h₁⟩
  rcases h₂ with ⟨y, h₂⟩
  rw[h₁, h₂, ← mul_assoc]
  nth_rw 2 [mul_assoc]
  nth_rw 4 [mul_comm]
  rw[← mul_assoc, mul_assoc]
  exact my.dvd_mul_right
  -- Alternatively, use ring_nf after rw[h₁, h₂]

-- SECTION 2.2

theorem dvd_add_of_two_mul (h₁ : a ∣ b) (h₂ : a ∣ c) : a ∣ b * x + c * y := by
  rcases h₁ with ⟨s, h₁⟩
  rcases h₂ with ⟨t, h₂⟩
  rw[h₁, h₂]
  repeat rw[mul_assoc]
  rw[← mul_add]
  exact my.dvd_mul_right

lemma dvd_add (h₁ : a ∣ b) (h₂ : a ∣ c) : a ∣ (b + c) := by
  rw[← mul_one (b + c), add_mul]
  exact my.dvd_add_of_two_mul h₁ h₂

variable {n : ℕ} {b c : ℕ → R}

lemma dvd_sum (h₁ : ∀ i ∈ Finset.range (n + 1), a ∣ b i) : a ∣ ∑ i ∈ Finset.range (n + 1), b i := by
  induction' n with k ih
  · simp at *
    assumption
  · rw[Finset.sum_range_succ]
    apply my.dvd_add
    · apply ih
      intro i h₂
      apply h₁
      rw[Finset.mem_range] at h₂
      rw[Finset.mem_range]
      linarith
      -- Alternatively, exact Nat.lt_add_right 1 h₂ can be used
    · apply h₁
      rw[Finset.mem_range]
      linarith

theorem dvd_sum_linear_combination (h₁ : ∀ i ∈ Finset.range (n + 1), a ∣ b i) : a ∣ ∑ i ∈ Finset.range (n + 1), c i * b i := by
  apply my.dvd_sum
  intro i h₂
  apply my.dvd_mul_left_general
  apply h₁
  assumption

end

-- APPENDIX RESULTS RELATING TO DIVISIBILITY

lemma dvd_neg {a b : ℤ} : a ∣ b ↔ a ∣ -b := by
  constructor
  · intro h₁
    rw[← one_mul b]
    rw [Int.neg_mul_eq_neg_mul]
    exact dvd_mul_left_general h₁
  · intro h₁
    rcases h₁ with ⟨x, h₁⟩
    rw [Int.neg_eq_comm] at h₁
    rw[← h₁]
    rw [Int.neg_mul_eq_mul_neg]
    exact dvd_mul_right

lemma dvd_sub {a b c : ℕ} (h₁ : a ∣ b) (h₂ : a ∣ c) : a ∣ b - c := by
  rcases h₁ with ⟨x, h₁⟩
  rcases h₂ with ⟨y, h₂⟩
  rw[h₁, h₂, ← Nat.mul_sub]
  exact my.dvd_mul_right

lemma dvd_iff_eq {a b : ℕ} : a ∣ b ∧ b ∣ a ↔ a = b := by
  constructor
  · rintro ⟨h₁, h₂⟩
    rcases h₁ with ⟨x, h₁⟩
    rcases h₂ with ⟨y, h₂⟩
    by_cases case : a = 0
    · rw[case, zero_mul] at h₁
      rw[case, h₁]
    · push_neg at case
      rw[h₁, mul_assoc] at h₂
      nth_rw 1 [← mul_one a] at h₂
      apply (Nat.mul_right_inj case).mp at h₂
      symm at h₂
      apply Nat.eq_one_of_mul_eq_one_right at h₂
      rw[h₂, mul_one] at h₁
      symm at h₁
      exact h₁
  · intro h₁
    rw[h₁]
    exact ⟨my.dvd_reflex, my.dvd_reflex⟩

lemma neg_dvd_reflexive {a : ℤ} : -a ∣ a := by
  use -1
  rw[mul_neg, mul_one, neg_neg]

lemma dvd_reflexive_neg {a : ℤ} : a ∣ -a := by
  use -1
  rw[mul_neg, mul_one]

lemma dvd_iff_eq_or_neg_eq {a b : ℤ} : a ∣ b ∧ b ∣ a ↔ a = b ∨ a = -b := by
  constructor
  · rintro ⟨h₁, h₂⟩
    rcases h₁ with ⟨x, h₁⟩
    rcases h₂ with ⟨y, h₂⟩
    by_cases case : a = 0
    · rw[case, zero_mul] at h₁
      rw[case, h₁]
      left
      rfl
    · push_neg at case
      rw[h₁, mul_assoc] at h₂
      nth_rw 1 [← mul_one a] at h₂
      apply (Int.mul_eq_mul_left_iff case).mp at h₂
      symm at h₂
      apply Int.eq_one_or_neg_one_of_mul_eq_one at h₂
      cases' h₂ with h₃ h₄
      · rw[h₃, mul_one] at h₁
        symm at h₁
        left
        assumption
      · rw[h₄, mul_neg, mul_one] at h₁
        apply Int.eq_neg_comm.mpr at h₁
        right
        assumption
  · intro h₁
    obtain h₂ | h₃ := h₁
    · constructor
      · rw[h₂]
      · rw[h₂]
    · constructor
      · rw[h₃]
        exact my.neg_dvd_reflexive
      · rw[h₃]
        exact my.dvd_reflexive_neg

lemma dvd_sub_comm {a b c : ℤ} (h₁ : a ∣ b - c) : a ∣ c - b := by
  have : a ∣ -1 * (b - c) := dvd_mul_left_general h₁
  simp at this
  exact this

lemma dvd_def {a b c : ℤ} (h₁ : a * b = c) : a ∣ c := by
  rw[← h₁]
  exact my.dvd_mul_right

lemma mul_dvd_mul' {a b c : ℤ} (h₁ : a ≠ 0) (h₂ : a * b ∣ a * c): b ∣ c := by
  rcases h₂ with ⟨x, h₂⟩
  rw[mul_assoc] at h₂
  rw[Int.mul_eq_mul_left_iff h₁] at h₂
  exact my.dvd_def h₂.symm

lemma dvd_add_iff_dvd_both {a b c : ℤ} (h₁ : a ∣ b + c) : a ∣ b ↔ a ∣ c := by
  constructor
  · rintro ⟨x, h₂⟩
    rcases h₁ with ⟨y, h₁⟩
    rw[h₂] at h₁
    apply eq_sub_of_add_eq' at h₁
    rw[← mul_sub] at h₁
    use (y - x)
  · rintro ⟨x, h₂⟩
    rcases h₁ with ⟨y, h₁⟩
    rw[h₂, add_comm] at h₁
    apply eq_sub_of_add_eq' at h₁
    rw[← mul_sub] at h₁
    use (y - x)

lemma dvd_common_divisors {a b d m r : ℤ} (h₁ : a = m * b + r) : d ∣ a ∧ d ∣ b ↔ d ∣ b ∧ d ∣ r := by
  constructor
  · rintro ⟨h₂, h₃⟩
    constructor
    · assumption
    · rcases h₂ with ⟨x, h₂⟩
      rcases h₃ with ⟨y, h₃⟩
      rw[h₂, h₃] at h₁
      have : r = d * (x - m * y) := by
        linarith
      rw[this]
      exact my.dvd_mul_right
  · rintro ⟨h₂, h₃⟩
    constructor
    · rcases h₂ with ⟨x, h₂⟩
      rcases h₃ with ⟨y, h₃⟩
      rw[h₂, h₃] at h₁
      have : a = d * (m * x + y) := by
        linarith
      rw[this]
      exact my.dvd_mul_right
    · assumption

lemma two_dvd_even_mul_odd {n : ℕ} : 2 ∣ (n * (n + 1)) := by
  by_cases h₁ : Even n
  · have h₂ : 2 ∣ n := even_iff_two_dvd.mp h₁
    exact my.dvd_mul_right_general h₂
  · apply Nat.not_even_iff_odd.mp at h₁
    have h₂ : Even (n + 1) := Odd.add_one h₁
    apply even_iff_two_dvd.mp at h₂
    exact my.dvd_mul_left_general h₂

theorem sum_nat {n : ℕ} : ∑ i ∈ Finset.Ico 1 (n + 1), i = n * (n + 1) / 2 := by
  induction' n with k ih
  · simp
  · have h₁ : 1 ≤ k + 1 := by linarith
    rw[Finset.sum_Ico_succ_top h₁, ih]
    have h₂ : 2 > 0 := by linarith
    apply Nat.mul_left_cancel h₂
    rw[mul_add]
    have h₃ : 2 ∣ k * (k + 1) := my.two_dvd_even_mul_odd
    have h₄ : 2 ∣ (k + 1) * (k + 2) := my.two_dvd_even_mul_odd
    rw[Nat.mul_div_cancel' h₃, Nat.mul_div_cancel' h₄]
    linarith

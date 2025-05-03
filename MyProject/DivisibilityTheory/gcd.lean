import MyProject
import MyProject.DivisibilityTheory.divisibility_theory

set_option trace.Meta.Tactic.simp.rewrite true

namespace my

variable {a b d : ℤ}

-- a.gcd b uses Int.gcd a b OR Nat.gcd a b depending on if a, b are in ℕ or ℤ

theorem dvd_gcd : d ∣ a ∧ d ∣ b ↔ d ∣ (a.gcd b : ℤ) := by
  constructor
  · rintro ⟨h₁, h₂⟩
    rw[Int.gcd_eq_gcd_ab] -- SWAP TO MY BEZOUTS LEMMA
    apply my.dvd_add_of_two_mul h₁ h₂
  · intro h₁
    constructor
    · rcases h₁ with ⟨x, h₁⟩
      have : (a.gcd b : ℤ) ∣ a := Int.gcd_dvd_left -- We neglect to prove that a.gcd b ∣ a ∧ a.gcd b ∣ b
      rw[h₁] at this
      exact my.prod_left_dvd this
    · rcases h₁ with ⟨y, h₁⟩
      have : (a.gcd b : ℤ) ∣ b := Int.gcd_dvd_right
      rw[h₁] at this
      exact my.prod_left_dvd this


theorem gcd_comm : a.gcd b = b.gcd a := by
  have h₁ : (a.gcd b : ℤ) ∣ b := Int.gcd_dvd_right
  have h₂ : (a.gcd b : ℤ) ∣ a := Int.gcd_dvd_left
  have h₃ : (b.gcd a : ℤ) ∣ a := Int.gcd_dvd_right
  have h₄ : (b.gcd a : ℤ) ∣ b := Int.gcd_dvd_left
  have h₅ : (a.gcd b : ℤ) ∣ (b.gcd a : ℤ) := my.dvd_gcd.mp ⟨h₁, h₂⟩
  have h₆ : (b.gcd a : ℤ) ∣ (a.gcd b : ℤ) := my.dvd_gcd.mp ⟨h₃, h₄⟩
  norm_cast at *
  exact my.dvd_iff_eq.mp ⟨h₅, h₆⟩

/- theorem gcd_coprime (c : ℕ): (a.gcd b : ℤ) = 1 ↔ (c : ℤ) ∣ a → (c : ℤ) ∣ b → c = 1 := by
  constructor
  · intro h₁ h₂ h₃
    have h₄ : (c : ℤ) ∣ (a.gcd b : ℤ) := my.dvd_gcd.mp ⟨h₂, h₃⟩
    rw[h₁] at h₄
    norm_cast at h₄
    have h₅ : 1 ∣ c := my.one_dvd
    exact my.dvd_iff_eq.mp ⟨h₄, h₅⟩ -/

theorem gcd_div (m n d : ℤ) (h₁ : (m.gcd n : ℤ) > 0) : (m.gcd n : ℤ) = d → ((m / d).gcd (n / d) : ℤ) = 1 := by -- m ≠ 0 or n ≠ 0
  intro h₂
  have h₃ : (m.gcd n : ℤ) ≠ 0 := by
    norm_cast at *
    exact Nat.ne_zero_of_lt h₁
  rw[h₂] at h₃
  have h₄ : (m.gcd n : ℤ) ∣ m := Int.gcd_dvd_left
  have h₅ : (m.gcd n : ℤ) ∣ n := Int.gcd_dvd_right
  rw[h₂] at h₄ h₅
  rcases h₄ with ⟨a, h₄⟩
  rcases h₅ with ⟨b, h₅⟩
  rw[h₄, h₅]
  rw[Int.mul_ediv_cancel_left a h₃, Int.mul_ediv_cancel_left b h₃]
  have a_b_coprime : ∀ (c : ℕ), (c : ℤ) ∣ a → (c : ℤ) ∣ b → c = 1 := by
    intro c h₆ h₇
    rcases h₆ with ⟨x, h₆⟩
    rw[h₆, ← mul_assoc] at h₄
    symm at h₄
    apply my.dvd_def at h₄
    rcases h₇ with ⟨y, h₇⟩
    rw[h₇, ← mul_assoc] at h₅
    symm at h₅
    apply my.dvd_def at h₅
    obtain h₈ := my.dvd_gcd.mp ⟨h₄, h₅⟩
    rw [h₂] at h₈
    rcases h₈ with ⟨k, h₈⟩
    rw[mul_assoc, mul_comm] at h₈
    apply Int.ediv_eq_of_eq_mul_left h₃ at h₈
    rw[Int.ediv_self h₃] at h₈
    obtain h₉ := Int.eq_one_or_neg_one_of_mul_eq_one h₈.symm
    norm_cast at h₉
    obtain h₉ | h₁₀ := h₉
    · exact h₉
    · exfalso
      exact h₁₀
  have h₆ : (a.gcd b : ℤ) ∣ a := Int.gcd_dvd_left
  have h₇ : (a.gcd b : ℤ) ∣ b := Int.gcd_dvd_right
  norm_cast
  exact a_b_coprime (a.gcd b) h₆ h₇

theorem gcd_eq_gcd_add_mul (a b m : ℤ) : a.gcd b = a.gcd (a * m + b) := by
  have h₁ : (a.gcd b : ℤ) ∣ a := Int.gcd_dvd_left
  have h₂ : (a.gcd b : ℤ) ∣ b := Int.gcd_dvd_right
  have h₃ : (a.gcd b : ℤ) ∣ (a * m) := my.dvd_mul_left_general h₁
  have h₄ : (a.gcd b : ℤ) ∣ (a * m + b) := my.dvd_add h₃ h₂
  have h₅ : (a.gcd b : ℤ) ∣ (a.gcd (a * m + b) : ℤ) :=  my.dvd_gcd.mp ⟨h₁, h₄⟩
  have h₆ : (a.gcd (a * m + b) : ℤ) ∣ a := Int.gcd_dvd_left
  have h₇ : (a.gcd (a * m + b) : ℤ) ∣ (a * m + b) := Int.gcd_dvd_right
  have h₈ : (a.gcd (a * m + b) : ℤ) ∣ (a * m) := my.dvd_mul_left_general h₆
  have h₉ : (a.gcd (a * m + b) : ℤ) ∣ b := (my.dvd_add_iff_dvd_both h₇).mp h₈
  have h₁₀ : (a.gcd (a * m + b) : ℤ) ∣ (a.gcd b : ℤ) := my.dvd_gcd.mp ⟨h₆, h₉⟩
  norm_cast at h₅ h₁₀
  exact my.dvd_iff_eq.mp ⟨h₅, h₁₀⟩

theorem gcd_mul {x : ℤ} (h₁ : x > 0) : ((x * a).gcd (x * b) : ℤ) = (x * a.gcd b : ℤ) := by
  by_cases case : (a.gcd b : ℤ) = 0
  · rw[case, mul_zero]
    have : a = 0 ∧ b = 0 := (gcd_eq_zero_iff a b).mp case
    rw[this.left, this.right, mul_zero]
    rfl
  · have h₂ : x ∣ ((x * a).gcd (x * b) : ℤ) := by
      have h₂ : x ∣ x * a := dvd_mul_right
      have h₃ : x ∣ x * b := dvd_mul_right
      exact my.dvd_gcd.mp ⟨h₂, h₃⟩
    rcases h₂ with ⟨k, h₂⟩
    have h₃ : x * k ∣ x * a ∧ x * k ∣ x * b := by
      apply my.dvd_gcd.mpr
      use 1
      rw[mul_one]
      exact h₂
    rcases h₃ with ⟨h₃, h₄⟩
    have h₅ : x ≠ 0 := Ne.symm (Int.ne_of_lt h₁)
    have h₆ : k ∣ a := by
      rcases h₃ with ⟨y, h₃⟩
      rw[mul_assoc, Int.mul_eq_mul_left_iff h₅] at h₃
      use y
    have h₇ : k ∣ b := by
      rcases h₄ with ⟨y, h₄⟩
      rw[mul_assoc, Int.mul_eq_mul_left_iff h₅] at h₄
      use y
    have h₈ : k ∣ (a.gcd b : ℤ) := my.dvd_gcd.mp ⟨h₆, h₇⟩
    have h₉ : (a.gcd b : ℤ) ∣ k := by
      have h₁₀ : (a.gcd b : ℤ) ∣ a := Int.gcd_dvd_left
      have h₁₁ : (a.gcd b : ℤ) ∣ b := Int.gcd_dvd_right
      have h₁₂ : x * (a.gcd b : ℤ) ∣ x * a := my.mul_dvd_mul (my.dvd_reflexive) h₁₀
      have h₁₃ : x * (a.gcd b : ℤ) ∣ x * b := my.mul_dvd_mul (my.dvd_reflexive) h₁₁
      have h₁₄ : x * (a.gcd b : ℤ) ∣ ((x * a).gcd (x * b) : ℤ) := my.dvd_gcd.mp ⟨h₁₂, h₁₃⟩
      rw [h₂] at h₁₄
      rcases h₁₄ with ⟨y, h₁₄⟩
      rw[mul_assoc, Int.mul_eq_mul_left_iff h₅] at h₁₄
      use y
    obtain h₁₀ := my.dvd_iff_eq_or_neg_eq.mp ⟨h₈, h₉⟩
    obtain h₁₁ | h₁₂ := h₁₀
    · rw [h₂, h₁₁]
    · rw[h₂, h₁₂]
      have h₁₃ : ((x * a).gcd (x * b) : ℤ) ≥ 0 := Int.ofNat_zero_le ((x * a).gcd (x * b))
      rw[h₂] at h₁₃
      have h₁₄ : k ≥ 0 := nonneg_of_mul_nonneg_right h₁₃ h₁
      rw[h₁₂] at h₁₄
      apply Int.nonpos_of_neg_nonneg at h₁₄
      have h₁₅ : (a.gcd b : ℤ) ≥ 0 := Int.ofNat_zero_le (a.gcd b)
      have h₁₆ : (a.gcd b : ℤ) = 0 := Int.le_antisymm h₁₄ h₁₅
      exfalso
      exact case h₁₆


theorem gcd_div' (m n d : ℤ) (h₁ : (m.gcd n : ℤ) > 0) : (m.gcd n : ℤ) = d → ((m / d).gcd (n / d) : ℤ) = 1 := by -- Alternative proof that follows frmo above
  intro h₂
  have h₃ : (m.gcd n : ℤ) ≠ 0 := by
    norm_cast at *
    exact Nat.ne_zero_of_lt h₁
  rw[h₂] at h₃
  rw[h₂] at h₁
  have h₄ : (m.gcd n : ℤ) ∣ m := Int.gcd_dvd_left
  have h₅ : (m.gcd n : ℤ) ∣ n := Int.gcd_dvd_right
  rw[h₂] at h₄ h₅
  rcases h₄ with ⟨a, h₄⟩
  rcases h₅ with ⟨b, h₅⟩
  rw[h₄, h₅] at h₂
  rw[my.gcd_mul h₁] at h₂
  apply Int.eq_one_of_mul_eq_self_right h₃ at h₂
  symm at h₄
  apply Int.eq_ediv_of_mul_eq_right h₃ at h₄
  symm at h₅
  apply Int.eq_ediv_of_mul_eq_right h₃ at h₅
  rw[← h₄, ← h₅]
  assumption

theorem gcd_fib_coprime {n : ℕ}: Int.gcd (Nat.fib (n + 1)) (Nat.fib n) = 1 := by -- We use Int.gcd to save us having to write that both things in the gcd are integers
  induction' n with k ih
  · rw [Nat.fib_zero, Nat.fib_one]
    norm_cast
  · rw[Nat.fib_add_two]
    rw[my.gcd_comm]
    nth_rw 2 [add_comm]
    rw[Nat.cast_add]
    nth_rw 2 [← Int.mul_one (Nat.fib (k + 1))]
    rw[← my.gcd_eq_gcd_add_mul (↑(Nat.fib (k + 1))) (↑(Nat.fib k)) (↑1)]
    exact ih

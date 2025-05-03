import MyProject
import MyProject.DivisibilityTheory.divisibility_theory

set_option trace.Meta.Tactic.simp.rewrite true

namespace my

variable {a b d m x : ℤ}

-- a.gcd b uses Int.gcd a b OR Nat.gcd a b depending on if a, b are in ℕ or ℤ

theorem dvd_gcd : d ∣ a ∧ d ∣ b ↔ d ∣ (a.gcd b : ℤ) := by
  constructor
  · rintro ⟨h₁, h₂⟩
    rw[Int.gcd_eq_gcd_ab]
    exact my.dvd_add_of_two_mul h₁ h₂
  · rintro ⟨z, h₁⟩
    have h₂ : (a.gcd b : ℤ) ∣ a := Int.gcd_dvd_left
    have h₃ : (a.gcd b : ℤ) ∣ b := Int.gcd_dvd_right
    rw[h₁] at h₂ h₃
    exact ⟨my.prod_left_dvd h₂, my.prod_left_dvd h₃⟩


theorem gcd_comm : a.gcd b = b.gcd a := by
  have h₁ : (a.gcd b : ℤ) ∣ (b.gcd a : ℤ) := my.dvd_gcd.mp ⟨Int.gcd_dvd_right, Int.gcd_dvd_left⟩
  have h₂ : (b.gcd a : ℤ) ∣ (a.gcd b : ℤ) := my.dvd_gcd.mp ⟨Int.gcd_dvd_right, Int.gcd_dvd_left⟩
  norm_cast at *
  exact my.dvd_iff_eq.mp ⟨h₁, h₂⟩

/- theorem gcd_coprime (c : ℕ): (a.gcd b : ℤ) = 1 ↔ (c : ℤ) ∣ a → (c : ℤ) ∣ b → c = 1 := by
  constructor
  · intro h₁ h₂ h₃
    have h₄ : (c : ℤ) ∣ (a.gcd b : ℤ) := ₁.dvd_gcd.mp ⟨h₂, h₃⟩
    rw[h₁] at h₄
    norm_cast at h₄
    have h₅ : 1 ∣ c := my.one_dvd
    exact my.dvd_iff_eq.mp ⟨h₄, h₅⟩ -/

theorem gcd_div' (m n d : ℤ) (h₁ : (m.gcd n : ℤ) > 0) : (m.gcd n : ℤ) = d → ((m / d).gcd (n / d) : ℤ) = 1 := by -- m ≠ 0 or n ≠ 0
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

theorem gcd_eq_gcd_mul_add : a.gcd b = a.gcd (a * m + b) := by
  have h₁ : (a.gcd b : ℤ) ∣ (a * m + b) := my.dvd_add (my.dvd_mul_right_general Int.gcd_dvd_left) Int.gcd_dvd_right
  have h₂ : (a.gcd b : ℤ) ∣ (a.gcd (a * m + b) : ℤ) :=  my.dvd_gcd.mp ⟨Int.gcd_dvd_left, h₁⟩
  have h₃ : (a.gcd (a * m + b) : ℤ) ∣ b := (my.dvd_add_iff_dvd_both Int.gcd_dvd_right).mp (my.dvd_mul_right_general Int.gcd_dvd_left)
  have h₄ : (a.gcd (a * m + b) : ℤ) ∣ (a.gcd b : ℤ) := my.dvd_gcd.mp ⟨Int.gcd_dvd_left, h₃⟩
  norm_cast at h₂ h₄
  exact my.dvd_iff_eq.mp ⟨h₂, h₄⟩

theorem gcd_mul (h₁ : x > 0) : ((x * a).gcd (x * b) : ℤ) = (x * a.gcd b : ℤ) := by
  by_cases case : (a.gcd b : ℤ) = 0
  · obtain h₂ := (gcd_eq_zero_iff a b).mp case
    rw[h₂.left, h₂.right]
    simp
  · have h₂ : x ∣ ((x * a).gcd (x * b) : ℤ) := my.dvd_gcd.mp ⟨my.dvd_mul_right, my.dvd_mul_right⟩
    rcases h₂ with ⟨k, h₂⟩
    have h₃ : x * k ∣ x * a := by
      rw[← h₂]
      exact Int.gcd_dvd_left
    have h₄ : x * k ∣ x * b := by
      rw[← h₂]
      exact Int.gcd_dvd_right
    apply my.mul_dvd_mul' (Int.ne_of_lt h₁).symm at h₃
    apply my.mul_dvd_mul' (Int.ne_of_lt h₁).symm at h₄
    obtain h₅ := my.dvd_gcd.mp ⟨h₃, h₄⟩
    have h₆ : x * (a.gcd b : ℤ) ∣ x * a := my.mul_dvd_mul (my.dvd_reflex) Int.gcd_dvd_left
    have h₇ : x * (a.gcd b : ℤ) ∣ x * b := my.mul_dvd_mul (my.dvd_reflex) Int.gcd_dvd_right
    have h₈ : x * (a.gcd b : ℤ) ∣ ((x * a).gcd (x * b) : ℤ) := my.dvd_gcd.mp ⟨h₆, h₇⟩
    rw [h₂] at h₈
    apply my.mul_dvd_mul' (Int.ne_of_lt h₁).symm at h₈
    obtain h₉ := my.dvd_iff_eq_or_neg_eq.mp ⟨h₅, h₈⟩
    obtain h₁₀ | h₁₁ := h₉
    · rw [h₂, h₁₀]
    · exfalso
      have h₁₂ : ((x * a).gcd (x * b) : ℤ) ≥ 0 := by
        norm_cast
        exact Nat.zero_le ((x * a).gcd (x * b))
      rw[h₂] at h₁₂
      obtain h₁₃ := nonneg_of_mul_nonneg_right h₁₂ h₁
      rw[h₁₁] at h₁₃
      apply Int.nonpos_of_neg_nonneg at h₁₃
      obtain h₁₄ := Int.ofNat_zero_le (a.gcd b)
      obtain h₁₅ := Int.le_antisymm h₁₃ h₁₄
      exact case h₁₅


theorem gcd_div (h₁ : (a.gcd b : ℤ) ≠ 0) (h₂ : (a.gcd b : ℤ) = d) : ((a / d).gcd (b / d) : ℤ) = 1 := by -- Alternative proof that follows from above
  have h₃ : (a.gcd b : ℤ) > 0 := by
    norm_cast at *
    exact Nat.zero_lt_of_ne_zero h₁
  rw[h₂] at h₃
  rw[h₂] at h₁
  have h₄ : (a.gcd b : ℤ) ∣ a := Int.gcd_dvd_left
  have h₅ : (a.gcd b : ℤ) ∣ b := Int.gcd_dvd_right
  rw[h₂] at h₄ h₅
  rcases h₄ with ⟨k, h₄⟩
  rcases h₅ with ⟨l, h₅⟩
  rw[h₄, h₅, my.gcd_mul h₃] at h₂
  apply Int.eq_one_of_mul_eq_self_right h₁ at h₂
  symm at h₄ h₅
  apply Int.eq_ediv_of_mul_eq_right h₁ at h₄
  apply Int.eq_ediv_of_mul_eq_right h₁ at h₅
  rw[h₄, h₅] at h₂
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
    rw[← my.gcd_eq_gcd_mul_add]
    exact ih

-- BEZOUTS LEMMA AND RELATED

section
variable {a b : ℤ}

theorem natAbs_mod_lt (h₁ : b ≠ 0) : (a % b).natAbs < b.natAbs := by
  rw [Int.natAbs_lt_iff_sq_lt, sq_lt_sq]
  rw [abs_of_nonneg]
  exact Int.emod_lt a h₁
  exact Int.emod_nonneg a h₁

end

-- FROM HERE WE FOLLOW SIMILAR IDEAS TO https://hrmacbeth.github.io/math2001/06_Induction.html#euclidean-algorithm-def

mutual

def L (a b : ℤ) : ℤ :=
  if h₁ : b > 0 then
    have h₂ : b ≠ 0 := (Int.ne_of_lt h₁).symm
    have : (a % b).natAbs < b.natAbs := natAbs_mod_lt h₂
    R b (a % b)
  else if h₁: b < 0 then
    have h₂ : b ≠ 0 := (Int.ne_of_gt h₁).symm
    have : (a % b).natAbs < b.natAbs := natAbs_mod_lt h₂
    R b (a % (-b))
  else if a ≥ 0 then
    1
  else
    -1
termination_by b.natAbs

def R (a b : ℤ) : ℤ :=
  if h₁ : b > 0 then
    have h₂ : b ≠ 0 := (Int.ne_of_lt h₁).symm
    have : (a % b).natAbs < b.natAbs := natAbs_mod_lt h₂
    L b (a % b) - (a / b) * R b (a % b)
  else if h₁ : b < 0 then
    have h₂ : b ≠ 0 := (Int.ne_of_gt h₁).symm
    have : (a % b).natAbs < b.natAbs := natAbs_mod_lt h₂
    L b (a % (-b)) + (a / (-b)) * R b (a % (-b))
  else
    0
termination_by b.natAbs

end

theorem bezouts_lemma (a b : ℤ) : L a b * a + R a b * b = (a.gcd b : ℤ) := by
  rw [R, L]
  split_ifs with h₁ h₂ h₃
  <;> push_neg at *
  · set q := a / b
    set r := a % b
    simp
    have h₄ : b ≠ 0 := (Int.ne_of_lt h₁).symm
    have termination : r.natAbs < b.natAbs := natAbs_mod_lt h₄
    obtain ih := bezouts_lemma b r
    have h₅ : b * q + r = a := Int.ediv_add_emod a b
    nth_rw 1 [← h₅]
    ring_nf
    rw[add_comm, mul_comm, ih]
    have h₆ : r = b * -q + a := by linarith
    rw[h₆]
    nth_rw 2 [my.gcd_comm]
    rw[← my.gcd_eq_gcd_mul_add]
  · set q := a / (-b)
    set r := a % (-b)
    simp
    have h₄ : b ≠ 0 := Ne.symm (Int.ne_of_gt h₂)
    have termination : (a % b).natAbs < b.natAbs := natAbs_mod_lt h₄
    obtain ih := bezouts_lemma b r
    have h₅ : (-b) * q + r = a := Int.ediv_add_emod a (-b)
    nth_rw 1 [← h₅]
    ring_nf
    rw[add_comm, mul_comm, ih]
    have h₆ : r = b * q + a := by linarith
    rw[h₆]
    nth_rw 2 [my.gcd_comm]
    rw[← my.gcd_eq_gcd_mul_add]
  · ring_nf
    have : b = 0 := Int.le_antisymm h₁ h₂
    rw[this]
    norm_num
    rw[abs_of_nonneg h₃]
  · ring_nf
    have : b = 0 := Int.le_antisymm h₁ h₂
    rw[this]
    norm_num
    rw[abs_of_neg h₃]
termination_by b.natAbs

theorem bezouts_lemma' (a b : ℤ) : ∃ x y : ℤ, x * a + y * b = (a.gcd b : ℤ) := by
  use L a b, R a b
  apply bezouts_lemma

import MyProject
import MyProject.DivisibilityTheory.divisibility_theory

namespace my

section
variable {a b : ℤ}

theorem abs_mod_lt (h₁ : b ≠ 0) : |a % b| < |b| := by
  rw [abs_of_nonneg]
  exact Int.emod_lt a h₁
  exact Int.emod_nonneg a h₁

theorem natAbs_mod_lt (h₁ : b ≠ 0) : (a % b).natAbs < b.natAbs := by
  rw [Int.natAbs_lt_iff_sq_lt, sq_lt_sq]
  exact my.abs_mod_lt h₁

end

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

theorem bezouts_lemma (a b : ℤ) : L a b * a + R a b * b = a.gcd b := by
  rw [R, L]
  split_ifs with h₁ h₂ h₃
  <;> push_neg at *
  · have h₄ : b ≠ 0 := (Int.ne_of_lt h₁).symm
    have termination : (a % b).natAbs < b.natAbs := natAbs_mod_lt h₄
    obtain ih := bezouts_lemma b (a % b)
    have h₅ : (a % b) + b * (a / b) = a := Int.emod_add_ediv a b
    set q := a / b
    set r := a % b
    simp
    calc R b r * a + (L b r - q * R b r) * b
        = R b r * (r + b * q) + (L b r - q * R b r) * b := by rw [h₅]
      _ = L b r * b + R b r * r := by ring
      _ = b.gcd r := ih
    norm_cast
    nth_rw 2 [my.gcd_comm]
    rw[← h₅, add_comm, ← my.gcd_eq_gcd_add_mul]
  · have h₄ : b ≠ 0 := Ne.symm (Int.ne_of_gt h₂)
    have termination : (a % b).natAbs < b.natAbs := natAbs_mod_lt h₄
    obtain ih := bezouts_lemma b (a % (-b))
    have h₅ : (a % -b) + (-b) * (a / (-b)) = a := Int.emod_add_ediv a (-b)
    set q := a / (-b)
    set r := a % (-b)
    calc R b r * a + (L b r + q * R b r) * b
        =  R b r * (r + -b * q) + (L b r + q * R b r) * b := by rw [h₅]
      _ = L b r * b + R b r * r := by ring
      _ = b.gcd r := ih
    norm_cast
    nth_rw 2 [my.gcd_comm]
    have : r + b * (-q) = a := by
      linarith
    rw[← this, add_comm, ← my.gcd_eq_gcd_add_mul]
  · ring
    have : b = 0 := Int.le_antisymm h₁ h₂
    rw[this]
    norm_num
    rw[abs_of_nonneg h₃]
  · ring
    have : b = 0 := Int.le_antisymm h₁ h₂
    rw[this]
    norm_num
    rw[abs_of_neg h₃]
termination_by b.natAbs


theorem bezouts_lemma' (a b : ℤ) : ∃ x y : ℤ, x * a + y * b = a.gcd b := by
  use L a b, R a b
  apply bezouts_lemma

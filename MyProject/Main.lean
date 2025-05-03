import MyProject
import MyProject.Divisibility

namespace my

variable {a b d m p x : ℤ}

-- SECTION 2.3

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

lemma gcd_comm : a.gcd b = b.gcd a := by
  have h₁ : (a.gcd b : ℤ) ∣ (b.gcd a : ℤ) := my.dvd_gcd.mp ⟨Int.gcd_dvd_right, Int.gcd_dvd_left⟩
  have h₂ : (b.gcd a : ℤ) ∣ (a.gcd b : ℤ) := my.dvd_gcd.mp ⟨Int.gcd_dvd_right, Int.gcd_dvd_left⟩
  norm_cast at *
  exact my.dvd_iff_eq.mp ⟨h₁, h₂⟩

theorem gcd_eq_gcd_mul_add : a.gcd b = a.gcd (a * m + b) := by
  have h₁ : (a.gcd b : ℤ) ∣ (a * m + b) := my.dvd_add (my.dvd_mul_right_general Int.gcd_dvd_left) Int.gcd_dvd_right
  have h₂ : (a.gcd b : ℤ) ∣ (a.gcd (a * m + b) : ℤ) :=  my.dvd_gcd.mp ⟨Int.gcd_dvd_left, h₁⟩
  have h₃ : (a.gcd (a * m + b) : ℤ) ∣ b := (my.dvd_add_iff_dvd_both Int.gcd_dvd_right).mp (my.dvd_mul_right_general Int.gcd_dvd_left)
  have h₄ : (a.gcd (a * m + b) : ℤ) ∣ (a.gcd b : ℤ) := my.dvd_gcd.mp ⟨Int.gcd_dvd_left, h₃⟩
  norm_cast at h₂ h₄
  exact my.dvd_iff_eq.mp ⟨h₂, h₄⟩

lemma gcd_mul (h₁ : x > 0) : ((x * a).gcd (x * b) : ℤ) = (x * a.gcd b : ℤ) := by
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

lemma gcd_div (h₁ : (a.gcd b : ℤ) ≠ 0) (h₂ : (a.gcd b : ℤ) = d) : ((a / d).gcd (b / d) : ℤ) = 1 := by
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

-- SECTION 2.4

theorem natAbs_mod_lt (h₁ : b ≠ 0) : (a % b).natAbs < b.natAbs := by
  rw [Int.natAbs_lt_iff_sq_lt, sq_lt_sq]
  rw [abs_of_nonneg]
  exact Int.emod_lt a h₁
  exact Int.emod_nonneg a h₁

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

-- APPENDIX RESULTS RELATING TO GCD

lemma gcd_fib_coprime {n : ℕ}: ((Nat.fib (n + 1)) : ℤ).gcd ((Nat.fib n) : ℤ) = 1 := by
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

-- CHAPTER 3

section

variable {n k p : ℕ}

-- SECTION 3.1

def choose (n k : ℕ) : ℤ := n.factorial / (k.factorial * (n - k).factorial)

lemma choose_helper (h₁ : k > 0) (h₂ : k ≤ n) : k * choose n k = n * choose (n - 1) (k - 1) := by
  unfold choose
  norm_cast
  calc
    _ = k * n.factorial / (k.factorial * (n - k).factorial) := by
      rw[← Nat.mul_div_assoc]
      exact Nat.factorial_mul_factorial_dvd_factorial h₂
    _ = k * (n * (n - 1).factorial) / (k * (k - 1).factorial * (n - k).factorial) := by
      rw[Nat.mul_factorial_pred (Nat.lt_of_lt_of_le h₁ h₂), Nat.mul_factorial_pred h₁]
    _ = n * (n - 1).factorial / ((k - 1).factorial * (n - k).factorial) := by
      rw[mul_assoc, Nat.mul_div_mul_left]
      assumption
    _ = n * ((n - 1).factorial / ((k - 1).factorial * (n - 1 - (k - 1)).factorial)) := by
      rw[Nat.mul_div_assoc, Nat.sub_sub_sub_cancel_right h₁]
      rw[← Nat.sub_sub_sub_cancel_right h₁, Nat.succ_eq_add_one, zero_add]
      have h₃ : (k - 1).factorial * (n - 1 - (k - 1)).factorial ∣ (n - 1).factorial := by
        have h₄ : k - 1 ≤ n - 1 := by
          exact Nat.sub_le_sub_right h₂ 1
        exact Nat.factorial_mul_factorial_dvd_factorial h₄
      exact h₃

-- SECTION 3.2

theorem pascals_rule (h₁ : k > 0) (h₂ : k ≤ n) : choose n k + choose n (k - 1) = choose (n + 1) k := by
  unfold choose
  norm_cast
  calc
    _ = (n.factorial * (n - k + 1)) / ((k.factorial * (n - k).factorial) * (n - k + 1)) + n.factorial / ((k - 1).factorial * (n - (k - 1)).factorial) := by
      rw[Nat.mul_div_mul_right]
      exact Nat.zero_lt_succ (n - k)
    _ = n.factorial * (n - k + 1) / (k.factorial * (n - k).factorial * (n - k + 1)) +
      n.factorial * k / ((k - 1).factorial * (n - k + 1).factorial * k) := by
      rw[tsub_tsub_assoc h₂ h₁, Nat.succ_eq_add_one, zero_add, Nat.mul_div_mul_right n.factorial ((k - 1).factorial * (n - k + 1).factorial) h₁]
    _ = n.factorial * (n - k + 1) / (k.factorial * (n - k + 1).factorial) +
      n.factorial * k / ((k - 1).factorial * (n - k + 1).factorial * k) := by
      nth_rw 1 [mul_assoc]
      nth_rw 3 [mul_comm]
      nth_rw 1 [← Nat.factorial_succ (n - k)]
    _ = n.factorial * (n - k + 1) / (k.factorial * (n - k + 1).factorial) +
      n.factorial * k / (k.factorial * (n - k + 1).factorial) := by
      nth_rw 4 [mul_comm]
      nth_rw 1 [← mul_assoc]
      have : k = k - 1 + 1 := by
        exact (Nat.sub_eq_iff_eq_add h₁).mp rfl
      nth_rw 5 [this]
      rw[← Nat.factorial_succ, ← this]
    _ = (n.factorial * (n - k + 1) + n.factorial * k) / (k.factorial * (n - k + 1).factorial) := by
      rw[← Nat.add_div_of_dvd_right]
      rw[Nat.factorial_succ (n - k)]
      nth_rw 2 [mul_comm]
      rw[← mul_assoc]
      have h₃ : k.factorial * (n - k).factorial ∣ n.factorial := by
        apply Nat.factorial_mul_factorial_dvd_factorial h₂
      have h₄ : n - k + 1 ∣ n - k + 1 := my.dvd_reflex
      exact my.mul_dvd_mul h₃ h₄
    _ = n.factorial * (n + 1) / (k.factorial * (n - k + 1).factorial) := by
      rw[← Nat.mul_add n.factorial, ← Nat.sub_add_comm h₂, Nat.sub_add_cancel (Nat.le_add_right_of_le h₂)]
    _ = (n + 1).factorial / (k.factorial * (n + 1 - k).factorial) := by
      rw[← Nat.sub_add_comm h₂]
      rw[mul_comm]
      rw[Nat.factorial_succ]

-- SECTION 3.3

theorem binomial_theorem : (a + b) ^ n = ∑ i ∈ Finset.range (n + 1), a ^ (n - i) * b ^ (i) * choose n i := by
  induction' n with k ih
  · unfold choose
    simp
  · calc
      _ = (a + b) * (a + b) ^ k := by rw[pow_succ, mul_comm]
      _ = (a + b) * ∑ i ∈ Finset.range (k + 1), a ^ (k - i) * b ^ i * choose k i := by rw[ih]
      _ = ∑ i ∈ Finset.range (k + 1), a * (a ^ (k - i) * b ^ i * choose k i) +
          ∑ i ∈ Finset.range (k + 1), b * (a ^ (k - i) * b ^ i * choose k i) := by
        rw [add_mul, Finset.mul_sum, Finset.mul_sum]
      _ = ∑ i ∈ Finset.range (k + 1), a ^ (k + 1 - i) * b ^ i * choose k i +
          ∑ i ∈ Finset.range (k + 1), b * (a ^ (k - i) * b ^ i * choose k i) := by
        rw[Finset.sum_congr rfl]
        intro i h₁
        nth_rw 1 [← pow_one a]
        rw[← mul_assoc, ← mul_assoc, ← pow_add]
        nth_rw 1 [add_comm]
        rw[← Nat.sub_add_comm (Finset.mem_range_succ_iff.mp h₁)]
      _ = ∑ i ∈ Finset.range (k + 1), a ^ (k + 1 - i) * b ^ i * choose k i +
          ∑ i ∈ Finset.range (k + 1), a ^ (k - i) * b ^ (i + 1) * choose k i := by
        nth_rw 2 [Finset.sum_congr rfl]
        intro i h₁
        nth_rw 1 [← pow_one b]
        rw[← mul_assoc, ← mul_assoc, mul_comm (b ^ 1) (a ^ (k - i))]
        nth_rw 2 [mul_assoc]
        rw[← pow_add]
        nth_rw 1 [add_comm]
      _ = a ^ (k + 1) + ∑ i ∈ Finset.Ico 1 (k + 1), a ^ (k + 1 - i) * b ^ i * choose k i +
          ∑ i ∈ Finset.range (k + 1), a ^ (k - i) * b ^ (i + 1) * choose k i := by
        nth_rw 1 [Finset.range_eq_Ico]
        have h₁ : 0 ∈ Finset.Ico 0 (k + 1) := Finset.insert_eq_self.mp rfl
        have h₂ : 0 ∉ Finset.Ico 1 (k + 1) := by
          intro h₂
          rw[Finset.mem_Ico] at h₂
          linarith
        obtain h₃ := (Finset.erase_eq_iff_eq_insert h₁ h₂).mp rfl
        rw[h₃, Finset.sum_insert h₂]
        unfold choose
        simp
        norm_cast
        have : k.factorial / k.factorial = 1 := Nat.div_self (Nat.factorial_pos k)
        rw[this]
        simp
      _ = a ^ (k + 1) + ∑ i ∈ Finset.Ico 1 (k + 1), a ^ (k + 1 - i) * b ^ i * choose k i +
        (∑ i ∈ Finset.Ico 0 k, a ^ (k - i) * b ^ (i + 1) * choose k i + b ^ (k + 1)) := by
        rw [Finset.range_eq_Ico]
        nth_rw 2 [Finset.sum_Ico_succ_top]
        · unfold choose
          simp
          norm_cast
          have : k.factorial / k.factorial = 1 := Nat.div_self (Nat.factorial_pos k)
          rw[this]
          simp
        · exact Nat.zero_le k
      _ = a ^ (k + 1) + ∑ i ∈ Finset.Ico 1 (k + 1), a ^ (k + 1 - i) * b ^ i * choose k i +
          (∑ j ∈ Finset.Ico 1 (k + 1), a ^ (k + 1 - j) * b ^ j * choose k (j - 1) +
          b ^ (k + 1)) := by
        nth_rw 2 [Finset.sum_bij (λ i h ↦ i + 1)]
        · intro i h₁
          rw[Finset.mem_Ico]
          simp
          obtain h₂ := Finset.mem_Ico.mp h₁
          exact h₂.right
        · intro i h₁ j h₂ h₃
          exact Nat.succ_inj'.mp h₃
        · intro i h₁
          simp
          use i - 1
          rw[Finset.mem_Ico] at h₁
          rcases h₁ with ⟨h₁, h₂⟩
          constructor
          · exact Nat.sub_lt_right_of_lt_add h₁ h₂
          · exact Nat.sub_add_cancel h₁
        · simp
      _ = a ^ (k + 1) + ∑ i ∈ Finset.Ico 1 (k + 1), a ^ (k + 1 - i) * b ^ i * (choose k i + choose k (i - 1)) + b ^ (k + 1) := by
        rw[← add_assoc]
        nth_rw 2 [add_assoc]
        rw[← Finset.sum_add_distrib]
        rw[Finset.sum_congr rfl]
        intro i h₁
        rw[← mul_add]
      _ = a ^ (k + 1) + ∑ i ∈ Finset.Ico 1 (k + 1), a ^ (k + 1 - i) * b ^ i * choose (k + 1) i + b ^ (k + 1) := by
        rw[Finset.sum_congr rfl]
        intro i h₁
        rw[Finset.mem_Ico] at h₁
        rcases h₁ with ⟨h₁, h₂⟩
        rw[my.pascals_rule h₁ (Nat.le_of_lt_succ h₂)]
      _ = ∑ i ∈ Finset.Ico 0 (k + 1), a ^ (k + 1 - i) * b ^ i * choose (k + 1) i + b ^ (k + 1) := by
        have h₁ : ∑ i ∈ Finset.Ico 0 (k + 1), a ^ (k + 1 - i) * b ^ i * choose (k + 1) i = a ^ (k + 1) * b ^ 0 * choose (k + 1) 0 + ∑ i ∈ Finset.Ico 1 (k + 1), a ^ (k + 1 - i) * b ^ i * choose (k + 1) i := by
          exact rfl
        rw[pow_zero, mul_one] at h₁
        have h₂ : choose (k + 1) 0 = 1 := by
          unfold choose
          simp
          norm_cast
          exact Nat.div_self (Nat.factorial_pos (k + 1))
        rw[h₂, mul_one] at h₁
        rw[← h₁]
      _ = ∑ i ∈ Finset.Ico 0 (k + 2), a ^ (k + 1 - i) * b ^ i * choose (k + 1) i := by
        have h₁ : ∑ i ∈ Finset.Ico 0 (k + 2), a ^ (k + 1 - i) * b ^ i * choose (k + 1) i = (∑ i ∈ Finset.Ico 0 (k + 1), a ^ (k + 1 - i) * b ^ i * choose (k + 1) i) + a ^ (k + 1 - (k + 1)) * b ^ (k + 1) * choose (k + 1) (k + 1) := by
          rw[Finset.sum_Ico_succ_top (Nat.le_add_left 0 (k + 1))]
        rw[Nat.add_sub_add_left] at h₁
        rw[pow_zero, one_mul] at h₁
        have h₂ : choose (k + 1) (k + 1) = 1 := by
          unfold choose
          simp
          norm_cast
          exact Nat.div_self (Nat.factorial_pos (k + 1))
        rw[h₂, mul_one] at h₁
        rw[← h₁]
      _ = ∑ i ∈ Finset.range (k + 2), a ^ (k + 1 - i) * b ^ i * choose (k + 1) i := by
        simp

end

-- CHAPTER 4

-- SECTION 4.1

lemma euclids_lemma {p a b : ℤ} (h₁ : p ∣ a * b) (h₂ : (a.gcd p : ℤ) = 1) : p ∣ b := by
  rw[← my.bezouts_lemma] at h₂
  have h₃ : (L a p * a + R a p * p) * b = 1 * b := by rw[h₂]
  rw[one_mul, add_mul, mul_assoc, mul_comm] at h₃
  nth_rw 4 [mul_comm] at h₃
  rw[← h₃]
  exact my.dvd_add_of_two_mul h₁ my.dvd_mul_right

section

variable {k n p : ℕ} {S : Multiset ℕ}

lemma prime_dvd_choose (h₁ : Prime (p : ℤ)) (h₂ : (k : ℤ) > 0) (h₃ : (k : ℤ) < (p : ℤ)) : (p : ℤ) ∣ choose p k := by
  have h₄ : (k : ℤ) ≤ (p : ℤ) := le_of_lt h₃
  have h₅ : (p : ℤ) ∣ ((k : ℤ) * choose p k) := by
    use (choose (p - 1) (k - 1))
    norm_cast at h₂ h₄
    exact my.choose_helper h₂ h₄
  apply Prime.dvd_or_dvd h₁ at h₅
  by_contra contra
  obtain h₅ | h₆ := h₅
  · have : (k : ℤ) ≥ (p : ℤ) := by
      exact Int.le_of_dvd h₂ h₅
    linarith
  · exact contra h₆

theorem form_of_primes (h₁ : Nat.Prime p) (h₂ : p > 3) : ∃ k, p = 6*k+1 ∨ p = 6*k+5 := by
  let k := p / 6
  let r := p % 6
  have h₃ : p = 6 * k + r := (Nat.div_add_mod p 6).symm
  have h₄ : r < 6 := by
    apply Nat.mod_lt p
    linarith
  match r with
  | 0 =>
    exfalso
    have : p = 2 * (3 * k) := by linarith
    rw[this] at h₁
    apply Nat.not_prime_mul at h₁
    assumption
    all_goals linarith
  | 1 =>
    use k
    left
    assumption
  | 2 =>
    exfalso
    have : p = 2 * (3 * k + 1) := by linarith
    rw[this] at h₁
    apply Nat.not_prime_mul at h₁
    assumption
    all_goals linarith
  | 3 =>
    exfalso
    have : p = 3 * (2 * k + 1) := by linarith
    rw[this] at h₁
    apply Nat.not_prime_mul at h₁
    assumption
    all_goals linarith
  | 4 =>
    exfalso
    have : p = 2 * (3 * k + 2) := by linarith
    rw[this] at h₁
    apply Nat.not_prime_mul at h₁
    assumption
    all_goals linarith
  | 5 =>
    use k
    right
    assumption

-- SECTION 4.2

lemma every_nat_has_prime_factor (h₁ : n ≥ 2) : ∃ p, p ∣ n ∧ Nat.Prime p := by
  induction' n using Nat.strong_induction_on with n ih
  by_cases h₂ : Nat.Prime n
  · use n
  · rw [Nat.not_prime_iff_exists_dvd_lt h₁] at h₂
    rcases h₂ with ⟨l, h₂, h₃, h₄⟩
    obtain h₅ := ih l h₄ h₃
    rcases h₅ with ⟨q, h₅, h₆⟩
    rcases h₅ with ⟨k, h₇⟩
    rw[h₇] at h₂
    obtain h₈ := my.prod_left_dvd h₂
    use q

theorem euclids_theorem : ∃ p, Nat.Prime p ∧ p > n := by
  let m := n.factorial + 1
  have h₁ : m ≥ 2 := by
    unfold m
    obtain h₁ := Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero n)
    linarith
  obtain ⟨q, h₂, h₃⟩ := every_nat_has_prime_factor h₁
  have h₄ : ¬ q ∣ n.factorial := by
    intro h₅
    apply my.dvd_sub h₂ at h₅
    unfold m at h₅
    simp at h₅
    have h₆ : q ≥ 2 := Nat.Prime.two_le h₃
    linarith
  have h₅ : q > n := by
    by_contra h₆
    push_neg at h₆
    apply Nat.dvd_factorial (Nat.Prime.pos h₃) at h₆
    exact h₄ h₆
  use q

-- SECTION 4.3

lemma ftoa_existence (h₁ : n ≥ 2) : ∃ (S : Multiset ℕ), (∀ p ∈ S, Nat.Prime p) ∧ n = S.prod := by
  induction' n using Nat.strong_induction_on with n ih
  by_cases case : Nat.Prime n
  · use {n}
    simp
    assumption
  · rw[Nat.not_prime_iff_exists_dvd_lt h₁] at case
    obtain ⟨k, h₂, h₃, h₄⟩ := case
    rcases h₂ with ⟨l, h₂⟩
    have h₅ : l ≥ 2 := by
      rw[h₂] at h₄
      exact one_lt_of_lt_mul_right h₄
    have h₆ : l < n := by
      rw[h₂]
      rw[mul_comm]
      have : l > 0 := by linarith
      exact (Nat.lt_mul_iff_one_lt_right this).mpr h₃
    obtain h₇ := ih k h₄ h₃
    obtain h₈ := ih l h₆ h₅
    rcases h₇ with ⟨S₁, h₇⟩
    rcases h₈ with ⟨S₂, h₈⟩
    obtain ⟨h₉, h₁₀⟩ := h₇
    obtain ⟨h₁₁,h₁₂⟩ := h₈
    rw[h₂, h₁₀, h₁₂]
    use S₁ + S₂
    constructor
    · intro p hp
      rw [Multiset.mem_add] at hp
      obtain hp₁ | hp₂ := hp
      · exact h₉ p hp₁
      · exact h₁₁ p hp₂
    · rw[Multiset.prod_add]

lemma prime_dvd_multiset_element (h₁ : Nat.Prime p) (h₂ : p ∣ (Multiset.cons k S).prod) : ∃ x ∈ Multiset.cons k S, p ∣ x := by
  induction' S using Multiset.induction_on with l S ih
  · simp at *
    assumption
  · rw [Multiset.prod_cons, Multiset.prod_cons, mul_comm, mul_assoc, Nat.Prime.dvd_mul h₁] at h₂
    obtain h₂ | h₃ := h₂
    · use l
      constructor
      · simp
      · assumption
    · rw[mul_comm, ← Multiset.prod_cons] at h₃
      apply ih at h₃
      rcases h₃ with ⟨x, h₃, h₄⟩
      use x
      constructor
      · rw[Multiset.cons_swap]
        exact Multiset.mem_cons_of_mem h₃
      · assumption

lemma prod_primes_eq_one_empty (h₁ : S.prod = 1) (h₂ : ∀ p ∈ S, Nat.Prime p) : S = ∅ := by
  by_contra h₃
  apply Multiset.exists_mem_of_ne_zero at h₃
  rcases h₃ with ⟨p, h₃⟩
  obtain h₄ := Nat.Prime.two_le (h₂ p h₃)
  have h₅ : S.prod = p * (S.erase p).prod := (Multiset.prod_erase h₃).symm
  rw[h₅] at h₁
  apply mul_eq_one.mp at h₁
  linarith

lemma ftoa_uniqueness (h₁ : n ≥ 2) : ∀ (S₁ S₂ : Multiset ℕ), (∀ p ∈ S₁, Nat.Prime p) ∧ n = S₁.prod → (∀ p ∈ S₂, Nat.Prime p) ∧ n = S₂.prod → S₁ = S₂ := by
  induction' n using Nat.strong_induction_on with n ih
  intro S₁ S₂ hS₁ hS₂
  rcases hS₁ with ⟨hS₁_prime, hS₁_eq⟩
  rcases hS₂ with ⟨hS₂_prime, hS₂_eq⟩
  have S₁_nonempty : S₁ ≠ ∅ := by
    intro h
    rw[h, Multiset.empty_eq_zero, Multiset.prod_zero] at hS₁_eq
    linarith
  obtain ⟨p, hp⟩ := Multiset.exists_mem_of_ne_zero S₁_nonempty
  have p_prime : Nat.Prime p := hS₁_prime p hp
  let S₁' := S₁.erase p
  have S₁'_eq : S₁ = Multiset.cons p S₁' := (Multiset.cons_erase hp).symm
  have n_eq : n = p * (S₁').prod := by
    rw[hS₁_eq, S₁'_eq]
    simp
  have p_dvd_n : p ∣ n := Dvd.intro (S₁').prod n_eq.symm
  have p_dvd_S₂_prod : p ∣ S₂.prod := by
    rw [hS₂_eq] at p_dvd_n
    exact p_dvd_n
  have S₂_nonempty : S₂ ≠ ∅ := by
    intro h
    rw[h, Multiset.empty_eq_zero, Multiset.prod_zero] at hS₂_eq
    linarith
  obtain ⟨a, ha⟩ := Multiset.exists_mem_of_ne_zero S₂_nonempty
  rw[← Multiset.cons_erase ha] at p_dvd_S₂_prod
  obtain ⟨q, hq, p_dvd_q⟩ := my.prime_dvd_multiset_element p_prime p_dvd_S₂_prod
  rw[Multiset.cons_erase ha] at hq
  have q_prime : Nat.Prime q := hS₂_prime q hq
  have p_eq_q : p = q := (Nat.prime_dvd_prime_iff_eq p_prime q_prime).mp p_dvd_q
  let S₂' := S₂.erase q
  have S₂'_eq : S₂ = Multiset.cons q S₂' := (Multiset.cons_erase hq).symm
  have n_eq' : n = p * S₂'.prod := by
    rw[hS₂_eq, S₂'_eq]
    rw[p_eq_q]
    simp
  have h₂ : p > 0 := Nat.Prime.pos p_prime
  have frac_eq : n / p = S₁'.prod := by
    rw [n_eq]
    exact Nat.mul_div_right S₁'.prod h₂
  have frac_eq' : n / p = S₂'.prod := by
    rw[n_eq']
    exact Nat.mul_div_right S₂'.prod h₂
  by_cases case₂ : n / p = 1
  · rw[case₂] at frac_eq frac_eq'
    symm at frac_eq frac_eq'
    have S₁'_empty : S₁' = ∅ := by
      apply my.prod_primes_eq_one_empty frac_eq
      intro r hr
      apply Multiset.mem_of_mem_erase at hr
      exact hS₁_prime r hr
    have S₂'_empty : S₂' = ∅ := by
      apply my.prod_primes_eq_one_empty frac_eq'
      intro r hr
      apply Multiset.mem_of_mem_erase at hr
      exact hS₂_prime r hr
    rw [S₁'_eq, S₁'_empty, S₂'_eq, S₂'_empty]
    simp
    exact p_eq_q
  · push_neg at case₂
    have frac_gr_one : n / p ≥ 2 := by
      have : n / p ≠ 0 := by
        apply Nat.div_ne_zero_iff.mpr
        constructor
        · exact Nat.ne_zero_of_lt h₂
        · apply Nat.le_of_dvd _ p_dvd_n
          · exact Nat.zero_lt_of_lt h₁
      have : n / p > 0 := Nat.zero_lt_of_ne_zero this
      exact Nat.lt_of_le_of_ne this case₂.symm
    have frac_lt : n / p < n := by
      apply Nat.div_lt_self
      exact Nat.zero_lt_of_lt h₁
      exact Nat.Prime.one_lt (hS₁_prime p hp)
    have ih_result : S₁' = S₂' := by
      apply ih (n / p) frac_lt frac_gr_one
      constructor
      · intro r hr
        apply hS₁_prime r
        exact Multiset.mem_of_mem_erase hr
      · exact frac_eq
      constructor
      · intro r hr
        apply hS₂_prime r
        exact Multiset.mem_of_mem_erase hr
      · exact frac_eq'
    rw [S₁'_eq, S₂'_eq, ih_result, p_eq_q]

theorem fundamental_theorem_of_arithmetic (h₁ : n ≥ 2) : ∃! (S : Multiset ℕ), (∀ p ∈ S, Nat.Prime p) ∧ n = S.prod := by
  obtain ⟨S, hS⟩ := ftoa_existence h₁
  use S
  constructor
  · exact hS
  · intro S' hS'
    exact ftoa_uniqueness h₁ S' S hS' hS

end

-- APPENDIX RESULTS RELATING TO PRIMES

theorem two_only_even_prime {p : ℕ} (h₁ : Nat.Prime p) : Even p ↔ p = 2 := by
  constructor
  · intro h₂
    apply Even.exists_two_nsmul at h₂
    rcases h₂ with ⟨k, h₂⟩
    have h₃ : 2 ∣ p := Dvd.intro k h₂.symm
    rw[Nat.dvd_prime h₁] at h₃
    obtain h₄ | h₅ := h₃
    · exfalso
      have : 2 ≠ 1 := by
        exact Nat.succ_succ_ne_one 0
      exact this h₄
    · exact h₅.symm
  · intro h₂
    rw[h₂]
    exact even_two

lemma prime_not_dvd_one {p : ℤ} (h₁ : Prime p) : ¬ p ∣ 1 := by
  by_contra h₂
  rcases h₂ with ⟨k, h₂⟩
  have h₃ : IsUnit p := isUnit_of_mul_eq_one p k h₂.symm
  have h₄ : ¬ IsUnit p := Prime.not_unit h₁
  exact h₄ h₃

theorem prime_not_dvd_succ {a p : ℤ} (h₁ : Prime p) (h₂ : p ∣ a) : ¬ p ∣ (a + 1) := by
  rcases h₂ with ⟨k, h₂⟩
  by_contra h₃
  rcases h₃ with ⟨l, h₃⟩
  have h₄ : 1 = p * (l - k) := by
    rw[mul_sub, ← h₂, ← h₃]
    linarith
  symm at h₄
  apply Dvd.intro (l - k) at h₄
  have h₅ : ¬ p ∣ 1 := my.prime_not_dvd_one h₁
  exact h₅ h₄

-- CHAPTER 5

section

variable {p k : ℕ} {n a b c : ℤ}

-- SECTION 5.1

theorem congr_iff_dvd : a ≡ b [ZMOD n] ↔ n ∣ b - a := by
  constructor
  · intro h₁
    rw[Int.ModEq] at h₁
    apply Int.emod_eq_emod_iff_emod_sub_eq_zero.mp at h₁
    apply Int.dvd_of_emod_eq_zero at h₁
    exact my.dvd_sub_comm h₁
  · intro h₁
    apply my.dvd_sub_comm at h₁
    apply Int.emod_eq_zero_of_dvd at h₁
    apply Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr at h₁
    rw[← Int.ModEq] at h₁
    exact h₁

lemma mod_trans (h₁ : a ≡ b [ZMOD n]) (h₂ : b ≡ c [ZMOD n]): a ≡ c [ZMOD n] := by
  rw[my.congr_iff_dvd] at h₁ h₂
  rcases h₁ with ⟨x, h₁⟩
  rcases h₂ with ⟨y, h₂⟩
  have h₃ : a = b - n * x := by
    linarith
  have h₄ : c = b + n * y := by
    linarith
  rw[my.congr_iff_dvd]
  rw[h₃, h₄]
  ring_nf
  rw[← mul_add]
  exact my.dvd_mul_right

theorem wilsons_theorem_only_if (h₁ : p ≥ 2) (h₂ : (p - 1).factorial ≡ -1 [ZMOD p]) : Nat.Prime p := by
  rw[my.congr_iff_dvd] at h₂
  rcases h₂ with ⟨k, h₂⟩
  by_contra contra
  rw[Nat.not_prime_iff_exists_dvd_lt h₁] at contra
  rcases contra with ⟨l, h₃, h₄, h₅⟩
  apply Int.ofNat_dvd.mpr at h₃
  apply my.dvd_mul_right_general at h₃
  rw[← h₂, Int.sub_eq_add_neg] at h₃
  have h₆ : l ∣ (p - 1).factorial := Nat.dvd_factorial (Nat.zero_lt_of_lt h₄) (Nat.le_sub_one_of_lt h₅)
  apply Int.ofNat_dvd.mpr at h₆
  apply my.dvd_neg.mp at h₆
  have h₇ : (l : ℤ) ∣ -1 := (my.dvd_add_iff_dvd_both h₃).mpr h₆
  apply my.dvd_neg.mpr at h₇
  norm_cast at h₇
  apply Nat.eq_one_of_dvd_one at h₇
  apply Nat.ne_of_lt at h₄
  exact h₄ h₇.symm

-- SECTION 5.2

lemma flt_nat {n p : ℕ} (h₁ : Nat.Prime p) : n ^ p ≡ n [ZMOD p] := by
  induction' n with n ih
  <;> rw [my.congr_iff_dvd]
  <;> have h₂ : p > 0 := Nat.Prime.pos h₁
  · ring_nf
    rw [← my.dvd_neg, zero_pow (Nat.ne_zero_of_lt h₂)]
    exact Int.dvd_zero ↑p
  · have : ↑(n + 1) - ↑(n + 1) ^ p = ↑n - ↑n ^ p - ∑ i ∈ Finset.Ico 1 p, ↑n ^ i * choose p i := by
      calc
        ↑n + 1 - (↑n + 1) ^ p = 1 + ↑n - ∑ i ∈ Finset.range (p + 1), 1 ^ (p - i) * ↑n ^ i * choose p i := by
          rw[add_comm, binomial_theorem]
        _ = 1 + ↑n - (∑ i ∈ Finset.range (p + 1), ↑n ^ i * choose p i) := by simp
        _ = 1 + ↑n - (∑ i ∈ Finset.range p, ↑n ^ i * choose p i + ↑n ^ p * choose p p) := by rw[Finset.sum_range_succ]
        _ = 1 + ↑n - (↑n ^ 0 * choose p 0 + ∑ i ∈ Finset.Ico 1 p, ↑n ^ i * choose p i + ↑n ^ p * choose p p) := by
          have h₄ : 0 ∉ Finset.Ico 1 p := by simp
          rw[← Nat.Ico_zero_eq_range, (Nat.Ico_insert_succ_left h₂).symm, Finset.sum_insert h₄]
        _ = 1 + ↑n - (1 + ∑ i ∈ Finset.Ico 1 p, ↑n ^ i * choose p i + ↑n ^ p) := by
          simp
          have h₅ : choose p 0 = 1 := by
            unfold choose
            simp
            norm_cast
            exact Nat.div_self (Nat.factorial_pos p)
          have h₆ : choose p p = 1 := by
            unfold choose
            simp
            norm_cast
            apply Nat.div_self (Nat.factorial_pos p)
          rw[h₅, h₆, mul_one]
        _ = ↑n - ↑n ^ p - ∑ i ∈ Finset.Ico 1 p, ↑n ^ i * choose p i := by
          nth_rw 2 [add_comm]
          rw[sub_add_eq_sub_sub, sub_add_eq_sub_sub]
          ring_nf
    rw[this]
    apply my.dvd_add
    · rw[my.congr_iff_dvd] at ih
      assumption
    · rw[← my.dvd_neg]
      apply Finset.dvd_sum
      intro i h₇
      rw[Finset.mem_Ico] at h₇
      have h₈ : (p : ℤ) ∣ choose p i := by
        apply my.prime_dvd_choose (Nat.prime_iff_prime_int.mp h₁)
        <;> norm_cast
        · exact h₇.left
        · exact h₇.right
      exact my.dvd_mul_left_general h₈

lemma flt_pos_int (h₁ : Nat.Prime p) (h₂ : n ≥ 0): n ^ p ≡ n [ZMOD p] := by
  have h₃ : ∃ m : ℕ, m = n := CanLift.prf n h₂
  rcases h₃ with ⟨m, h₃⟩
  rw[← h₃]
  exact flt_nat h₁

lemma flt_neg_int (h₁ : Nat.Prime p) (h₂ : n < 0) : n ^ p ≡ n [ZMOD p] := by
  let l := -n
  have h₃ : l ≥ 0 := by
    ring_nf
    apply Int.neg_nonneg_of_nonpos
    exact Int.le_of_lt h₂
  have h₄ : l ^ p ≡ l [ZMOD p] := flt_pos_int h₁ h₃
  have h₅ : n = -l := by ring_nf
  rw[h₅]
  rw [neg_pow]
  by_cases case₁ : Odd p
  · have : (-1) ^ p = -1 := Odd.neg_one_pow case₁
    rw[this]
    simp
    exact h₄
  · apply Nat.not_odd_iff_even.mp at case₁
    have : p = 2 := (my.two_only_even_prime h₁).mp case₁
    rw[this]
    rw[this] at h₄
    simp
    have h₆ : l ≡ -l [ZMOD 2] := by
      rw[my.congr_iff_dvd, Int.sub_eq_add_neg, ← Int.two_mul]
      exact my.dvd_mul_right
    exact my.mod_trans h₄ h₆

theorem alternative_flt (h₁ : Nat.Prime p) : n ^ p ≡ n [ZMOD p] := by
  by_cases case : n ≥ 0
  · exact flt_pos_int h₁ case
  · push_neg at case
    exact flt_neg_int h₁ case

theorem fermats_little_theorem (h₁ : Nat.Prime p) (h₂ : ¬ (p : ℤ) ∣ n) : n ^ (p - 1) ≡ 1 [ZMOD p] := by
  have h₃ : n ^ p ≡ n [ZMOD p] := alternative_flt h₁
  rw[my.congr_iff_dvd, ← mul_pow_sub_one (Nat.Prime.ne_zero h₁) n] at h₃
  nth_rw 1 [← mul_one n] at h₃
  rw[← Int.mul_sub] at h₃
  apply Prime.dvd_or_dvd (Nat.prime_iff_prime_int.mp h₁) at h₃
  obtain h₄ | h₅ := h₃
  · exfalso
    exact h₂ h₄
  · rw[← my.congr_iff_dvd] at h₅
    exact h₅

end

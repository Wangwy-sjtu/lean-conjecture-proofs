import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.Ring

/-!
# Five decimal rotate-and-add steps cannot preserve primality

Chuck Seggelin, OEIS A086004, Conjecture 2 (2003). The rotation rule
is OEIS A086002. Each application recalculates the number of digits.
-/

namespace RotateAdd

/-- Decimal width in the usual notation, including one digit for zero. -/
def digits (n : ℕ) : ℕ := Nat.log 10 n + 1

/-- The place value above the right half of the digits. -/
def halfBase (n : ℕ) : ℕ := 10 ^ (digits n / 2)

/-- On an odd-width number, the middle decimal digit. -/
def middle (n : ℕ) : ℕ := n / halfBase n % 10

/-- Swap the first and last halves, keeping an odd-length central digit in place. -/
def rotate (n : ℕ) : ℕ :=
  if digits n % 2 = 0 then
    halfBase n * (n % halfBase n) + n / halfBase n
  else
    halfBase n * (10 * (n % halfBase n) + middle n) + n / halfBase n / 10

/-- One rotate-and-add step. -/
def step (n : ℕ) : ℕ := n + rotate n

-- The explicit digit-count bounds make the published numerical examples quick to check.
private theorem digits_of_bounds (n e : ℕ) (lo : 10^e ≤ n) (hi : n < 10^(e+1)) :
    digits n = e+1 := congrArg (· + 1) (Nat.log_eq_of_pow_le_of_lt_pow lo hi)

local macro "check_rotation" n:num e:num : tactic =>
  `(tactic| (have hd := digits_of_bounds $n $e (by decide) (by decide)
             simp only [step, rotate, middle, halfBase, hd]
             decide))

example : rotate 1234 = 3412 := by check_rotation 1234 3
example : rotate 12345 = 45312 := by check_rotation 12345 4
example : rotate 12003 = 3012 := by check_rotation 12003 4

-- The four iterates in Chai Wah Wu's published example (OEIS A261458).
example : [step^[1] 10010905789, step^[2] 10010905789,
    step^[3] 10010905789, step^[4] 10010905789] =
    [15800815799, 31600631599, 63200263199, 126399526399] := by
  have h₁ : step 10010905789 = 15800815799 := by check_rotation 10010905789 10
  have h₂ : step 15800815799 = 31600631599 := by check_rotation 15800815799 10
  have h₃ : step 31600631599 = 63200263199 := by check_rotation 31600631599 10
  have h₄ : step 63200263199 = 126399526399 := by check_rotation 63200263199 10
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply, h₁, h₂, h₃, h₄]

private theorem halfBase_pos (n : ℕ) : 0 < halfBase n := Nat.pow_pos (by decide)

private theorem middle_lt (n : ℕ) : middle n < 10 := Nat.mod_lt _ (by decide)

private theorem below_width (n : ℕ) : n < 10 ^ digits n :=
  Nat.lt_pow_succ_log_self (by decide) n

private theorem even_scale {n : ℕ} (he : digits n % 2 = 0) :
    10 ^ digits n = halfBase n * halfBase n := by
  have h : digits n = digits n / 2 + digits n / 2 := by omega
  exact (congrArg (fun e : ℕ => 10 ^ e) h).trans (pow_add ..)

private theorem odd_scale {n : ℕ} (ho : digits n % 2 = 1) :
    10 ^ digits n = halfBase n * (10 * halfBase n) := by
  have h : digits n = digits n / 2 + digits n / 2 + 1 := by omega
  calc
    10 ^ digits n = 10 ^ (digits n / 2 + digits n / 2 + 1) := congrArg _ h
    _ = _ := by rw [pow_succ, pow_add]; unfold halfBase; ring

private theorem packed_lt {base high low limit : ℕ} (hl : low < base) (hh : high < limit) :
    base * high + low < base * limit := by
  calc
    base * high + low < base * high + base := Nat.add_lt_add_left hl _
    _ = base * (high + 1) := by ring
    _ ≤ base * limit := Nat.mul_le_mul_left _ hh

private theorem rotate_below_width (n : ℕ) : rotate n < 10 ^ digits n := by
  have hm := halfBase_pos n
  have hb := Nat.mod_lt n hm
  have hn := below_width n
  by_cases he : digits n % 2 = 0
  · rw [rotate, if_pos he, even_scale he]
    rw [even_scale he] at hn
    exact packed_lt ((Nat.div_lt_iff_lt_mul hm).2 hn) hb
  · have ho : digits n % 2 = 1 := by omega
    rw [rotate, if_neg he, odd_scale ho]
    rw [odd_scale ho] at hn
    have ha : n / halfBase n / 10 < halfBase n := by
      apply (Nat.div_lt_iff_lt_mul (by decide : 0 < 10)).2
      apply (Nat.div_lt_iff_lt_mul hm).2
      simpa [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm] using hn
    exact packed_lt ha (packed_lt (middle_lt n) hb)

private theorem width_after (n : ℕ) (hp : (step n).Prime) :
    digits n ≤ digits (step n) ∧ digits (step n) ≤ digits n + 1 := by
  have hg : n ≤ step n := Nat.le_add_right _ _
  have hu : step n < 10 ^ (digits n + 1) := by
    rw [step, pow_succ]
    have hx := below_width n
    have hr := rotate_below_width n
    omega
  have hlog := Nat.log_lt_of_lt_pow (b := 10) hp.ne_zero hu
  have hlo := Nat.log_mono_right (b := 10) hg
  unfold digits at *
  omega

private theorem odd_of_prime_step {n : ℕ} (hp : n.Prime) (hq : (step n).Prime) :
    digits n % 2 = 1 := by
  by_contra hc
  have he : digits n % 2 = 0 := by omega
  have hd : 0 < digits n := by simp [digits]
  obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero (show digits n / 2 ≠ 0 by omega)
  have hBase : ¬ (halfBase n).Prime := by
    simp [halfBase, hj, pow_succ, Nat.prime_mul_iff, show ¬Nat.Prime 10 by decide]
  have hdecomp := Nat.div_add_mod n (halfBase n)
  have hn : n / halfBase n + n % halfBase n ≠ 1 := by
    intro heq
    by_cases h0 : n / halfBase n = 0
    · have hb : n % halfBase n = 1 := by omega
      rw [h0, hb, Nat.mul_zero, Nat.zero_add] at hdecomp
      exact hp.ne_one hdecomp.symm
    · have hle : n / halfBase n ≤ 1 := (Nat.le_add_right _ _).trans_eq heq
      have ha : n / halfBase n = 1 := Nat.le_antisymm hle (Nat.pos_of_ne_zero h0)
      have hb : n % halfBase n = 0 := by omega
      rw [ha, hb, Nat.mul_one, Nat.add_zero] at hdecomp
      exact hBase (hdecomp.symm ▸ hp)
  have hfactor : step n = (halfBase n + 1) * (n / halfBase n + n % halfBase n) := by
    calc
      step n = (halfBase n * (n / halfBase n) + n % halfBase n) + rotate n :=
        congrArg (fun x => x + rotate n) hdecomp.symm
      _ = _ := by rw [rotate, if_pos he]; ring
  have hm := halfBase_pos n
  exact (Nat.not_prime_mul (by omega : halfBase n + 1 ≠ 1) hn) (hfactor ▸ hq)

private theorem same_width {n : ℕ} (p : n.Prime) (q : (step n).Prime)
    (r : (step (step n)).Prime) : digits (step n) = digits n := by
  have := odd_of_prime_step p q
  have := odd_of_prime_step q r
  obtain ⟨_, _⟩ := width_after n q
  omega

/-- When three successive values are prime, a carry from the middle digit is forced. -/
private theorem central_carry {n : ℕ} (p : n.Prime) (q : (step n).Prime)
    (r : (step (step n)).Prime) : middle (step n) + 10 = 2 * middle n := by
  let M := halfBase n
  let a := n / M / 10
  let b := n % M
  let c := middle n
  let s := a + b
  let y := step n
  have hm : 0 < M := halfBase_pos _
  have hc : c < 10 := middle_lt n
  have hodd := odd_of_prime_step p q
  have hyodd : digits y % 2 = 1 := odd_of_prime_step q r
  have hw : digits y = digits n := same_width p q r
  have hmy : halfBase y = M := by
    unfold halfBase
    rw [hw]
    rfl
  have hn : n = M * (10 * a + c) + b := by
    have t : 10 * a + c = n / M := Nat.div_add_mod (n / M) 10
    rw [t]
    exact (Nat.div_add_mod n M).symm
  have hrotate : rotate n = M * (10 * b + c) + a := by
    rw [rotate, if_neg (by omega : digits n % 2 ≠ 0)]
  have hy : y = M * (10 * s + 2 * c) + s := by
    calc
      y = (M * (10 * a + c) + b) + (M * (10 * b + c) + a) := congrArg₂ (· + ·) hn hrotate
      _ = _ := by dsimp only [s]; ring
  have hylt : y < M * (10 * M) := by
    have h := below_width y
    rwa [hw, odd_scale hodd] at h
  have hs : s < M := by
    by_contra h
    have hx : 10 * M ≤ 10 * s + 2 * c := by omega
    have hx' := Nat.mul_le_mul_left M hx
    omega
  have low : y % M = s := by rw [hy, Nat.mul_add_mod, Nat.mod_eq_of_lt hs]
  have quot : y / M = 10 * s + 2 * c := by
    rw [hy, Nat.mul_add_div hm, Nat.div_eq_of_lt hs, Nat.add_zero]
  have mid : middle y = (2 * c) % 10 := by
    rw [middle, hmy, quot, Nat.mul_add_mod]
  have carry : 10 ≤ 2 * c := by
    by_contra h
    have small : 2 * c < 10 := by omega
    have fix : rotate y = y := by
      calc
        rotate y = M * (10 * s + 2 * c) + s := by
          rw [rotate, if_neg (by omega : digits y % 2 ≠ 0), hmy, low, mid, Nat.mod_eq_of_lt small,
            quot, Nat.mul_add_div (by decide : 0 < 10), Nat.div_eq_of_lt small, Nat.add_zero]
        _ = y := hy.symm
    have hdouble : step y = 2 * y := by rw [step, fix, two_mul]
    exact (Nat.not_prime_mul (by decide : 2 ≠ 1) q.ne_one) (hdouble ▸ r)
  change middle y + 10 = 2 * c
  omega

/-- No prime survives the first through fifth applications of rotate-and-add. -/
theorem no_five_rotation_cycle_primes (p : ℕ) :
    ¬ (∀ j : ℕ, j ≤ 5 → Nat.Prime (step^[j] p)) := by
  intro h
  let x₁ := step p
  let x₂ := step x₁
  let x₃ := step x₂
  let x₄ := step x₃
  let x₅ := step x₄
  have p₀ : p.Prime := h 0 (by decide)
  have p₁ : x₁.Prime := h 1 (by decide)
  have p₂ : x₂.Prime := h 2 (by decide)
  have p₃ : x₃.Prime := h 3 (by decide)
  have p₄ : x₄.Prime := h 4 (by decide)
  have p₅ : x₅.Prime := h 5 (by decide)
  have h₁ : middle x₁ + 10 = 2 * middle p := central_carry p₀ p₁ p₂
  have h₂ : middle x₂ + 10 = 2 * middle x₁ := central_carry p₁ p₂ p₃
  have h₃ : middle x₃ + 10 = 2 * middle x₂ := central_carry p₂ p₃ p₄
  have h₄ : middle x₄ + 10 = 2 * middle x₃ := central_carry p₃ p₄ p₅
  have h₀ := middle_lt p
  omega

#print axioms no_five_rotation_cycle_primes

end RotateAdd

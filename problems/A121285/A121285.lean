import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Mathar's four-term recurrence for OEIS A121285

The sequence is defined by the binomial formula in the OEIS entry. Its initial
values are written separately to avoid negative exponents and negative indices.
-/

namespace Permutomino

def a : ℕ → ℤ
  | 0 => 1
  | 1 => 1
  | t + 2 => ((t : ℤ) + 5) * 2 ^ t
      - ((t : ℤ) + 2) * Nat.choose (t+1) ((t+1)/2)
      - ((t : ℤ) + 1) * Nat.choose t (t/2)

private def b (t : ℕ) : ℚ := Nat.choose t (t/2)

private theorem b_odd (m : ℕ) :
    b (2*m+1) = (2*(m:ℚ)+1) * b (2*m) / (m+1) := by
  have h := Nat.choose_mul_succ_eq (2*m) m
  have hsub : 2*m+1-m=m+1 := by omega
  rw [hsub] at h
  apply (eq_div_iff (by positivity)).2
  unfold b
  rw [show (2*m+1)/2=m by omega, show 2*m/2=m by omega]
  have heq : (2*m+1).choose m * (m+1) = (2*m+1) * (2*m).choose m :=
    h.symm.trans (Nat.mul_comm _ _)
  exact_mod_cast heq

private theorem b_even (m : ℕ) : b (2*m+2) = 2 * b (2*m+1) := by
  unfold b
  rw [show (2*m+2)/2=m+1 by omega, show (2*m+1)/2=m by omega]
  have heq : (2*m+2).choose (m+1) = 2 * (2*m+1).choose m := by
    rw [Nat.choose_succ_succ, Nat.choose_symm_half]
    omega
  exact_mod_cast heq

private theorem a_cast (t : ℕ) :
    (a (t+2) : ℚ) = ((t:ℚ)+5) * 2^t - (t+2) * b (t+1) - (t+1) * b t := by
  simp [a, b]

example : [a 0, a 1, a 2, a 3, a 4, a 5, a 6] = [1,1,2,4,10,22,54] := by decide

/-- The left side in Mathar's conjecture, newest term first. -/
def residual {R : Type*} [CommRing R] (n x y z w : R) : R :=
  -(n-1)*(3*n^2-27*n+56)*x + 2*(n-5)*(3*n^2-12*n+5)*y
   + 4*(3*n^3-33*n^2+110*n-118)*z - 8*(n-3)*(3*n^2-21*n+32)*w

-- Substitution of the four explicit coefficients at n=t+5.  The common
-- exponential factor is v=2^t and the five adjacent middle binomials are u₀,...,u₄.
private def expanded (t v u₀ u₁ u₂ u₃ u₄ : ℚ) : ℚ :=
  residual (t+5)
    ((t+8)*(8*v) - (t+5)*u₄ - (t+4)*u₃)
    ((t+7)*(4*v) - (t+4)*u₃ - (t+3)*u₂)
    ((t+6)*(2*v) - (t+3)*u₂ - (t+2)*u₁)
    ((t+5)*v - (t+2)*u₁ - (t+1)*u₀)

private theorem expanded_even (m : ℕ) (v : ℚ) :
    expanded (2*m) v (b (2*m)) (b (2*m+1)) (b (2*m+2))
      (b (2*m+3)) (b (2*m+4)) = 0 := by
  have h₃ := b_odd (m+1)
  have h₄ := b_even (m+1)
  norm_num [Nat.mul_add, Nat.add_assoc] at h₃ h₄
  rw [h₄, h₃, b_even m, b_odd m]
  unfold expanded residual
  have h₁ : (m:ℚ)+1 ≠ 0 := by positivity
  have h₂ : (m:ℚ)+1+1 ≠ 0 := by positivity
  field_simp
  ring

private theorem expanded_odd (m : ℕ) (v : ℚ) :
    expanded (2*m+1) v (b (2*m+1)) (b (2*m+2)) (b (2*m+3))
      (b (2*m+4)) (b (2*m+5)) = 0 := by
  have h₃ := b_odd (m+1)
  have h₄ := b_even (m+1)
  have h₅ := b_odd (m+2)
  norm_num [Nat.mul_add, Nat.add_assoc] at h₃ h₄ h₅
  rw [h₅, h₄, h₃, b_even m]
  unfold expanded residual
  have h₂ : (m:ℚ)+1+1 ≠ 0 := by positivity
  have h₃' : (m:ℚ)+2+1 ≠ 0 := by positivity
  field_simp
  ring

private theorem expanded_zero (t : ℕ) (v : ℚ) :
    expanded t v (b t) (b (t+1)) (b (t+2)) (b (t+3)) (b (t+4)) = 0 := by
  obtain ⟨m, hm | hm⟩ : ∃ m, t = 2*m ∨ t = 2*m+1 := ⟨t/2, by omega⟩
  · subst t
    simpa using expanded_even m v
  · subst t
    simpa [Nat.add_assoc] using expanded_odd m v

private theorem cast_residual (n x y z w : ℤ) :
    ((residual n x y z w : ℤ) : ℚ) = residual (n:ℚ) (x:ℚ) (y:ℚ) (z:ℚ) (w:ℚ) := by
  simp [residual]

private theorem large (t : ℕ) :
    residual ((t:ℤ)+5) (a (t+5)) (a (t+4)) (a (t+3)) (a (t+2)) = 0 := by
  apply (Int.cast_injective (α := ℚ))
  rw [cast_residual, Int.cast_zero]
  push_cast
  have h₃ := a_cast (t+3)
  have h₂ := a_cast (t+2)
  have h₁ := a_cast (t+1)
  norm_num [Nat.add_assoc, pow_add] at h₃ h₂ h₁
  rw [h₃, h₂, h₁, a_cast t]
  calc
    _ = expanded t (2^t) (b t) (b (t+1)) (b (t+2)) (b (t+3)) (b (t+4)) := by
      unfold expanded residual
      ring
    _ = 0 := expanded_zero t _

/-- R. J. Mathar's conjecture (2017), for every index at which its four terms exist. -/
theorem mathar_recurrence (n : ℕ) (hn : 3 ≤ n) :
    -((n:ℤ)-1)*(3*(n:ℤ)^2-27*n+56)*a n
    + 2*((n:ℤ)-5)*(3*(n:ℤ)^2-12*n+5)*a (n-1)
    + 4*(3*(n:ℤ)^3-33*(n:ℤ)^2+110*n-118)*a (n-2)
    - 8*((n:ℤ)-3)*(3*(n:ℤ)^2-21*n+32)*a (n-3) = 0 := by
  change residual (n:ℤ) (a n) (a (n-1)) (a (n-2)) (a (n-3)) = 0
  by_cases h : 5 ≤ n
  · obtain ⟨t, rfl⟩ : ∃ t, n = t + 5 := ⟨n-5, by omega⟩
    simpa using large t
  · have hsmall : n=3 ∨ n=4 := by omega
    rcases hsmall with rfl | rfl <;> decide

#print axioms mathar_recurrence

end Permutomino

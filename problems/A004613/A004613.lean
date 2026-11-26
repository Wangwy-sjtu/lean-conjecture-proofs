import Std

/-!
Counterexamples to the final, fixed-n observation in Richard R. Forberg's
2026-11-05 comment on OEIS A004613.  The sequence itself consists of
positive integers whose prime divisors are all 1 modulo 4.

https://oeis.org/A004613
Lean 4.24.0, standard distribution.
-/

namespace A004613

/-- The integer square root r is represented by a nonnegative witness. -/
def hitsNat (n m : Nat) : Prop :=
  m ≤ n ∧ ∃ r : Nat, r*r = n*n + m*m + 1

def hitsInt (n m : Int) : Prop :=
  m ≤ n ∧ ∃ r : Int, 0 ≤ r ∧ r*r = n*n + m*m + 1

/-- For n=8 the sole nonnegative m is 4, strictly between 0 and 8. -/
theorem natural_solutions (m : Nat) : hitsNat 8 m ↔ m = 4 := by
  constructor
  · rintro ⟨hm, r, eq⟩
    have hm2 := Nat.mul_le_mul hm hm
    have hr : r < 12 := by
      by_cases h : r < 12
      · exact h
      have hr2 := Nat.mul_le_mul (show 12 ≤ r by omega) (show 12 ≤ r by omega)
      omega
    have table : ∀ i : Fin 9, ∀ j : Fin 12,
        j.val*j.val = 8*8 + i.val*i.val + 1 → i.val = 4 := by decide
    exact table ⟨m, by omega⟩ ⟨r, hr⟩ eq
  · rintro rfl
    exact ⟨by decide, 9, by decide⟩

private theorem small_factor {u v : Int} (hu : 0 < u) (hsmall : u ≤ 4)
    (eq : u*v = 17) : u = 1 ∧ v = 17 := by
  have choices : u=1 ∨ u=2 ∨ u=3 ∨ u=4 := by omega
  rcases choices with h | h | h | h <;> subst u <;> omega

private theorem factor_seventeen {u v : Int} (hu : 0 < u) (hv : 0 < v)
    (eq : u*v = 17) : (u=1 ∧ v=17) ∨ (u=17 ∧ v=1) := by
  by_cases su : u ≤ 4
  · exact Or.inl (small_factor hu su eq)
  by_cases sv : v ≤ 4
  · have h := small_factor hv sv (by rw [Int.mul_comm]; exact eq)
    exact Or.inr ⟨h.2, h.1⟩
  have lower : (5:Int)*5 ≤ u*v := Int.le_trans
    (Int.mul_le_mul_of_nonneg_right (by omega : 5 ≤ u) (by decide : 0 ≤ (5:Int)))
    (Int.mul_le_mul_of_nonneg_left (by omega : 5 ≤ v) (by omega))
  omega

/-- With signed m and only m ≤ n, n=4 has the single solution m=-8. -/
theorem integer_solutions (m : Int) : hitsInt 4 m ↔ m = -8 := by
  constructor
  · rintro ⟨hm, r, hr, eq⟩
    have product : (r-m)*(r+m) = 17 := by grobner
    have left : 0 < r-m := by
      by_cases h : 0 < r-m
      · exact h
      have nonneg := Int.mul_nonneg (by omega : 0 ≤ m-r) (by omega : 0 ≤ r+m)
      have opposite : (m-r)*(r+m) = -17 := by grobner
      omega
    have right : 0 < r+m := by
      by_cases h : 0 < r+m
      · exact h
      have nonneg := Int.mul_nonneg (by omega : 0 ≤ r-m) (by omega : 0 ≤ -(r+m))
      have opposite : (r-m)*(-(r+m)) = -17 := by grobner
      omega
    rcases factor_seventeen left right product with h | h <;> omega
  · rintro rfl
    exact ⟨by decide, 9, by decide, by decide⟩

/-- A set with an element can satisfy "zero or at least two" only if there
    is a different element as well. -/
def noSingleton {α : Type} (S : α → Prop) : Prop :=
  ∀ m, S m → ∃ j, S j ∧ j ≠ m

theorem natural_refutation : ¬ (∀ n : Nat, 0 < n → noSingleton (hitsNat n)) := by
  intro claim
  obtain ⟨m, hm, different⟩ := claim 8 (by decide) 4 ((natural_solutions 4).2 rfl)
  exact different ((natural_solutions m).1 hm)

theorem integer_refutation : ¬ (∀ n : Int, 0 < n → noSingleton (hitsInt n)) := by
  intro claim
  obtain ⟨m, hm, different⟩ := claim 4 (by decide) (-8) ((integer_solutions (-8)).2 rfl)
  exact different ((integer_solutions m).1 hm)

#print axioms natural_refutation
#print axioms integer_refutation
end A004613

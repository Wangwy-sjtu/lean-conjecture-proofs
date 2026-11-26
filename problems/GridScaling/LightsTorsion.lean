import Mathlib.Algebra.CharP.Two
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-! Three-power torsion on the characteristic-two Lights Out spectral curve. -/

namespace LightsTorsion
open scoped CharTwo
attribute [local instance] Classical.propDecidable

theorem fourth_power_residue (j : ℕ) :
    ∃ u : ℕ, 4^(3^j) = 1+3^(j+1)*(1+3*u) := by
  induction j with
  | zero => exact ⟨0,by decide⟩
  | succ j ih =>
    obtain ⟨u,old⟩ := ih
    refine ⟨u+3^j*(1+3*u)^2+(3^j)^2*(1+3*u)^3,?_⟩
    calc
      4^(3^(j+1)) = (4^(3^j))^3 := by rw [← pow_mul,pow_succ 3 j]
      _ = _ := by rw [old]; simp only [pow_succ 3]; ring

variable {K : Type*} [Field K] [CharP K 2]

def wave (x : K) : K := x+x⁻¹

private def traceThree (q : ℕ) (x : K) := x+x^q+(x^q)^q

private theorem trace_add (d : ℕ) (a b : K) :
    traceThree (4^d) (a+b) = traceThree (4^d) a + traceThree (4^d) b := by
  have q : 4^d = 2^(2*d) := by rw [pow_mul]; rfl
  simp only [traceThree,q,add_pow_char_pow]
  ring

private theorem trace_one (q : ℕ) : traceThree q (1 : K)=1 := by
  simp [traceThree]

private theorem trace_layer (d t : ℕ) (x : K) (hx : x^((3*d)*3)=1) :
    traceThree (1+(3*d)*(1+3*t)) x = if x^(3*d)=1 then x else 0 := by
  let z := x^(3*d)
  let q := 1+(3*d)*(1+3*t)
  have z3 : z^3=1 := by simpa [z,← pow_mul] using hx
  have twist : x^q=x*z := by
    change x^(1+(3*d)*(1+3*t))=x*z
    rw [pow_add,pow_one,pow_mul]; change x*z^(1+3*t)=x*z
    rw [pow_add,pow_one,pow_mul,z3]; simp
  have fixed : z^q=z := by
    have form : q=1+3*(d*(1+3*t)) := by dsimp [q]; ring
    rw [form,pow_add,pow_one,pow_mul,z3]; simp
  change x+x^q+(x^q)^q = if z=1 then x else 0
  rw [twist,mul_pow,twist,fixed]
  by_cases one : z=1
  · simp [one]
  · have fac : (z-1)*(1+z+z^2)=0 := by linear_combination z3
    have zero := (mul_eq_zero.mp fac).resolve_left (sub_ne_zero.mpr one)
    rw [if_neg one]
    linear_combination x*zero

theorem wave_zero {x : K} (nz : x≠0) (h : wave x=0) : x=1 := by
  have inv : x=x⁻¹ := CharTwo.add_eq_zero.mp h
  have sq : x^2=1 := by calc
    x^2=x*x := pow_two x
    _=x*x⁻¹ := congrArg (x*·) inv
    _=1 := mul_inv_cancel₀ nz
  have van : (x+1)^2=0 := by rw [CharTwo.add_sq,sq,one_pow]; simp
  exact CharTwo.add_eq_zero.mp (pow_eq_zero_iff (by decide : 2≠0) |>.mp van)

private theorem wave_trace_layer (j : ℕ) (x : K) (hx : x^(3^(j+2))=1) :
    traceThree (4^(3^j)) (wave x) = if x^(3^(j+1))=1 then wave x else 0 := by
  obtain ⟨t,form⟩ := fourth_power_residue j
  have a : 3^(j+1)=3*3^j := pow_succ' 3 j
  have b : 3^(j+2)=(3*3^j)*3 := by rw [show j+2=(j+1)+1 by omega,pow_succ,a]
  have hi : (x⁻¹)^(3^(j+2))=1 := by simp [inv_pow,hx]
  rw [wave,trace_add,form,a]
  rw [trace_layer _ _ _ (b ▸ hx),trace_layer _ _ _ (b ▸ hi),inv_pow]
  by_cases e : x^(3*3^j)=1 <;> simp [e]

/-- If both coordinates on the Lights Out spectral curve have 3-power order,
at least one coordinate must be trivial. This holds over every field of characteristic two. -/
theorem three_power_curve (k : ℕ) (x y : K) (hx : x^(3^k)=1) (hy : y^(3^k)=1)
    (curve : wave x + wave y=1) : x=1 ∨ y=1 := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    obtain ⟨x0,y0⟩ : x≠0 ∧ y≠0 := by
      constructor <;> rintro rfl <;> simp_all
    cases k with
    | zero => exact Or.inl (by simpa using hx)
    | succ k =>
      cases k with
      | zero =>
        have base (z : K) (h : z^3=1) (ne : z≠1) : wave z=1 := by
          have nz : z≠0 := by rintro rfl; simp at h
          have fac : (z-1)*(1+z+z^2)=0 := by linear_combination h
          have van := (mul_eq_zero.mp fac).resolve_left (sub_ne_zero.mpr ne)
          have zi : z⁻¹=z^2 := by
            apply (mul_right_cancel₀ nz)
            rw [inv_mul_cancel₀ nz,← pow_succ,h]
          rw [wave,zi]
          exact (CharTwo.add_eq_zero.mp (by linear_combination van : (z+z^2)+1=0))
        by_cases a : x=1
        · exact Or.inl a
        by_cases b : y=1
        · exact Or.inr b
        rw [base x hx a,base y hy b] at curve
        simp at curve
      | succ j =>
        have sum := congrArg (traceThree (4^(3^j)) : K → K) curve
        rw [trace_add,trace_one,wave_trace_layer j x hx,wave_trace_layer j y hy] at sum
        by_cases a : x^(3^(j+1))=1 <;> by_cases b : y^(3^(j+1))=1
        · exact ih (j+1) (by omega) a b
        · simp [a,b] at sum
          exact Or.inr (wave_zero y0 (by rw [sum,add_eq_left] at curve; exact curve))
        · simp [a,b] at sum
          exact Or.inl (wave_zero x0 (by rw [sum,add_eq_right] at curve; exact curve))
        · simp [a,b] at sum

#print axioms three_power_curve

end LightsTorsion

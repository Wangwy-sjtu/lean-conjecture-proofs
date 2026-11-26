import LightsTorsion
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod

/-! The exact polynomial gcd for the ternary family of square Lights Out boards. -/

namespace LightsPolynomial
open Polynomial LightsTorsion
open scoped Polynomial CharTwo

/-- Path recurrence, indexed so that a path with n vertices uses index n+1. -/
def fib {R : Type*} [Semiring R] (t : R) : ℕ → R
  | 0 => 0
  | 1 => 1
  | n+2 => t*fib t (n+1)+fib t n

theorem map_fib {R S : Type*} [Semiring R] [Semiring S] (f : R →+* S) (t : R) (n : ℕ) :
    f (fib t n)=fib (f t) n := by
  induction n using Nat.twoStepInduction with
  | zero => simp [fib]
  | one => simp [fib]
  | more n a b => simp [fib,map_add,map_mul,a,b]

section Algebra
variable {R : Type*} [CommRing R] [CharP R 2]

theorem double (t : R) (n : ℕ) :
    fib t (2*n)=t*(fib t n)^2 ∧
    fib t (2*n+1)=(fib t (n+1))^2+(fib t n)^2 := by
  induction n with
  | zero => simp [fib]
  | succ n ih =>
    have even : fib t (2*n+2)=t*(fib t (n+1))^2 := by
      rw [fib,ih.1,ih.2,mul_add,CharTwo.add_cancel_right]
    constructor
    · simpa only [Nat.mul_succ] using even
    · rw [show 2*(n+1)+1=(2*n+1)+2 by omega,fib,show 2*n+1+1=2*n+2 by omega,
          even,ih.2,fib,CharTwo.add_sq,mul_pow]
      ring

omit [CharP R 2] in
private theorem fib_at_zero (r : ℕ) : fib (0 : R) (2*r+1)=1 := by
  induction r with
  | zero => rfl
  | succ r ih => simpa [show 2*(r+1)+1=(2*r+1)+2 by omega,fib] using ih

private theorem fib_at_one (r : ℕ) :
    fib (1 : R) (3*r)=0 ∧ fib (1 : R) (3*r+1)=1 := by
  induction r with
  | zero => simp [fib]
  | succ r ih =>
    have a : fib (1 : R) (3*r+2)=1 := by rw [fib,ih.1,ih.2]; simp
    have b : fib (1 : R) (3*r+3)=0 := by
      change fib (1 : R) ((3*r+1)+2)=0
      rw [fib,ih.2,a]; simp
    constructor
    · simpa only [Nat.mul_succ] using b
    · change fib (1 : R) (3*(r+1)+1)=1
      rw [show 3*(r+1)+1=(3*r+2)+2 by omega,fib,a,b]; simp

end Algebra

variable {K : Type*} [Field K] [CharP K 2]

private theorem fib_wave (x : K) (nz : x≠0) (n : ℕ) :
    wave x * fib (wave x) n = x^n+(x⁻¹)^n := by
  induction n using Nat.twoStepInduction with
  | zero => simp [fib]
  | one => simp [fib,wave]
  | more n a b =>
    rw [fib,mul_add,← mul_assoc (wave x),mul_assoc,b,a]
    simp only [wave,pow_succ]
    have cancel : x*x⁻¹=1 := mul_inv_cancel₀ nz
    linear_combination (x^n+(x⁻¹)^n)*(cancel) + (CharTwo.add_self_eq_zero (x^n+(x⁻¹)^n))

private theorem wave_parameter [IsAlgClosed K] (t : K) : ∃ x : K, x≠0 ∧ wave x=t := by
  let p : K[X] := X^2+C t*X+1
  have degree : p.natDegree=2 := by
    dsimp [p]
    rw [add_assoc,natDegree_add_eq_left_of_natDegree_lt]
    · simp
    · apply lt_of_le_of_lt (Polynomial.natDegree_add_le ..)
      simp only [natDegree_one,Nat.max_zero,natDegree_X_pow]
      apply lt_of_le_of_lt (Polynomial.natDegree_mul_le ..)
      simp
  obtain ⟨x,h⟩ := IsAlgClosed.exists_root p (by
    intro eq
    have nd := Polynomial.natDegree_eq_zero_iff_degree_le_zero.mpr eq.le
    omega)
  have hx : x^2+t*x+1=0 := by simpa [Polynomial.IsRoot,p] using h
  have nz : x≠0 := by rintro rfl; simp at hx
  refine ⟨x,nz,?_⟩
  apply mul_right_cancel₀ nz
  rw [wave,add_mul,inv_mul_cancel₀ nz]
  apply CharTwo.add_eq_zero.mp
  linear_combination hx

private theorem root_coordinate [IsAlgClosed K] (t : K) (k : ℕ) (root : fib t (3^k)=0) :
    ∃ x : K, wave x=t ∧ x≠1 ∧ x^(3^k)=1 := by
  obtain ⟨x,nz,w⟩ := wave_parameter t
  have odd : Odd (3^k) := (by decide : Odd 3).pow
  have t0 : t≠0 := by
    rintro rfl
    obtain ⟨u,hu⟩ := odd
    rw [hu,fib_at_zero] at root
    exact one_ne_zero root
  have ident := fib_wave x nz (3^k)
  rw [w,root,mul_zero,eq_comm,CharTwo.add_eq_zero,inv_pow] at ident
  have zn : x^(3^k)≠0 := pow_ne_zero _ nz
  have sq : (x^(3^k))^2=1 := by
    calc
      (x^(3^k))^2 = x^(3^k)*x^(3^k) := pow_two _
      _ = x^(3^k)*(x^(3^k))⁻¹ := congrArg (x^(3^k)*·) ident
      _ = 1 := mul_inv_cancel₀ zn
  have h : (x^(3^k)+1)^2=0 := by rw [CharTwo.add_sq,sq,one_pow]; simp
  refine ⟨x,w,?_,CharTwo.add_eq_zero.mp ((pow_eq_zero_iff (by decide : 2≠0)).mp h)⟩
  rintro rfl
  exact t0 (by simpa [wave] using w.symm)

abbrev F := ZMod 2
abbrev P := Polynomial F

/-- Coprimality for all three-power indices is the step needed to settle
the infinite-family conjecture. -/
theorem ternary_coprime (k : ℕ) :
    IsCoprime (fib (X : P) (3^k)) (fib (X+1 : P) (3^k)) := by
  apply (Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed (k:=F) (AlgebraicClosure F) _ _).2
  intro t
  by_contra! ht
  have a := ht.1
  have b := ht.2
  rw [show aeval t (fib (X : P) (3^k)) = fib t (3^k) by
        simpa using map_fib (aeval t).toRingHom (X : P) (3^k)] at a
  rw [show aeval t (fib (X+1 : P) (3^k)) = fib (t+1) (3^k) by
        have h := map_fib (aeval t).toRingHom (X+1 : P) (3^k)
        change aeval t (fib (X+1 : P) (3^k)) = fib (aeval t (X+1 : P)) (3^k) at h
        simpa only [map_add,aeval_X,map_one] using h] at b
  obtain ⟨x,wx,x1,xt⟩ := root_coordinate t k a
  obtain ⟨y,wy,y1,yt⟩ := root_coordinate (t+1) k b
  exact (three_power_curve k x y xt yt (by rw [wx,wy]; simp)).elim x1 y1

#print axioms ternary_coprime

/-- An explicit ideal membership, used to eliminate the two grid recurrences. -/
theorem bezout_bound (k : ℕ) : ∃ u v : P,
    u*fib X (2*3^k)+v*fib (X+1) (2*3^k)=X*(X+1) := by
  obtain ⟨s,t,st⟩ := (ternary_coprime k).pow (m:=2) (n:=2)
  refine ⟨s*(X+1),t*X,?_⟩
  rw [(double (X : P) _).1,(double (X+1 : P) _).1]
  linear_combination (X*(X+1))*st

theorem boundary (k : ℕ) : fib (0 : F) (2*3^(k+1))=0 ∧ fib (1 : F) (2*3^(k+1))=0 := by
  refine ⟨by rw [(double (0 : F) _).1,zero_mul],?_⟩
  rw [pow_succ,show 2*(3^k*3)=3*(2*3^k) by omega]
  exact (fib_at_one _).1

theorem exact_common_divisors (k : ℕ) (q : P) :
    (q∣fib X (2*3^(k+1)) ∧ q∣fib (X+1) (2*3^(k+1))) ↔ q∣X*(X+1) := by
  constructor
  · rintro ⟨a,b⟩
    obtain ⟨u,v,h⟩ := bezout_bound (k+1)
    rw [← h]
    exact dvd_add (dvd_mul_of_dvd_right a u) (dvd_mul_of_dvd_right b v)
  · intro h
    let n := 2*3^(k+1)
    have linears (p : P) (zero : p.eval 0=0) (one : p.eval 1=0) : X*(X+1)∣p := by
      have x : X∣p := by simpa [Polynomial.IsRoot] using
        (Polynomial.dvd_iff_isRoot.mpr (show p.IsRoot 0 from zero))
      have y : X+1∣p := by simpa [CharTwo.sub_eq_add] using
        (Polynomial.dvd_iff_isRoot.mpr (show p.IsRoot 1 from one))
      have co : IsCoprime (X : P) (X+1) := ⟨-1,1,by ring⟩
      exact co.mul_dvd x y
    have value (s : P) (z : F) : (fib s n).eval z=fib (s.eval z) n := map_fib (evalRingHom z) s n
    obtain ⟨a,b⟩ := boundary k
    constructor
    · apply h.trans (linears _ ?_ ?_) <;> rw [value] <;> simp [n,a,b]
    · apply h.trans (linears _ ?_ ?_) <;> rw [value] <;> simp [n,a,b]

#print axioms exact_common_divisors

end LightsPolynomial

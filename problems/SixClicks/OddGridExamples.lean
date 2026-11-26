import OddStabilization
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Size

/-! Binary certificates for actual square-grid nullities in the 57-power tower. -/
namespace OddGridExamples
open Polynomial LightsPolynomial LightsGrid GridGcd OddStabilization
open scoped Polynomial CharTwo
noncomputable section

def rep (n : ℕ) : P :=
  Nat.binaryRec (motive:=fun _ => P) 0 (fun b _ p => X*p+if b then 1 else 0) n

@[simp] theorem rep_zero : rep 0=0 := by simp [rep]
@[simp] theorem rep_one : rep 1=1 := by simp [rep]

theorem rep_bit (b : Bool) (n : ℕ) :
    rep (Nat.bit b n) = X*rep n + if b then 1 else 0 := by
  unfold rep
  rw [Nat.binaryRec_eq b n (Or.inl (by simp))]

theorem rep_xor (a b : ℕ) : rep (a^^^b) = rep a+rep b := by
  induction a using Nat.binaryRec generalizing b with
  | zero => simp
  | bit i a ih =>
    cases b using Nat.bitCasesOn with
    | bit j b =>
      rw [Nat.xor_bit,rep_bit,rep_bit,rep_bit,ih,mul_add]
      cases i <;> cases j <;> simp <;> abel_nf
      simp [CharTwo.two_eq_zero]

theorem rep_twice (a : ℕ) : rep (2*a)=X*rep a := by
  rw [← Nat.bit_false_apply,rep_bit]; simp

theorem rep_shift (a j : ℕ) : rep (a<<<j) = X^j*rep a := by
  induction j with
  | zero => simp
  | succ j ih => rw [Nat.shiftLeft_succ,rep_twice,ih,pow_succ]; ring

theorem rep_degree {a : ℕ} (nz : a≠0) :
    rep a≠0 ∧ (rep a).natDegree+1=a.size := by
  induction a using Nat.binaryRec with
  | zero => contradiction
  | bit b a ih =>
    rw [Nat.size_bit nz,rep_bit]
    by_cases ha : a=0
    · subst a; cases b <;> simp_all
    obtain ⟨h,d⟩ := ih ha
    have c : (if b then (1:P) else 0).natDegree=0 := by cases b <;> simp
    have deg : (X*rep a+(if b then 1 else 0)).natDegree=(rep a).natDegree+1 := by
      rw [Polynomial.natDegree_add_eq_left_of_natDegree_lt ?_,natDegree_X_mul h]
      rw [c,natDegree_X_mul h]; omega
    constructor
    · intro zero; rw [zero,natDegree_zero] at deg; omega
    · omega

private def fibPair (translated : Bool) : ℕ → ℕ×ℕ
  | 0 => (0,1)
  | n+1 =>
    let (a,b) := fibPair translated n
    (b, ((2*b)^^^(if translated then b else 0))^^^a)

private theorem pair_correct (s : Bool) (n : ℕ) :
    rep (fibPair s n).1=fib (if s then X+1 else X) n ∧
    rep (fibPair s n).2=fib (if s then X+1 else X) (n+1) := by
  induction n with
  | zero => simp [fibPair,fib]
  | succ n ih =>
    refine ⟨ih.2,?_⟩
    change rep (((2*(fibPair s n).2)^^^(if s then (fibPair s n).2 else 0))^^^(fibPair s n).1)=_
    rw [rep_xor,rep_xor,rep_twice,ih.1,ih.2,fib]
    cases s <;> simp_all [add_mul]

private def reduce : ℕ → ℕ → ℕ → ℕ×ℕ
  | 0,a,b => (a,b)
  | f+1,a,b =>
    if b=0 then (a,0) else if a=0 then (b,0) else if b.log2≤a.log2 then
      reduce f (a^^^(b<<<(a.log2-b.log2))) b else reduce f b a

private theorem same_divisors (p : P) (a b j : ℕ) :
    (p∣rep (a^^^(b<<<j)) ∧ p∣rep b) ↔ (p∣rep a ∧ p∣rep b) := by
  rw [rep_xor,rep_shift]
  constructor
  · rintro ⟨ha,hb⟩
    have d := dvd_add ha (dvd_mul_of_dvd_right hb (X^j))
    exact ⟨by simpa [add_assoc] using d,hb⟩
  · rintro ⟨ha,hb⟩
    exact ⟨dvd_add ha (dvd_mul_of_dvd_right hb _),hb⟩

private theorem reduce_correct (p : P) (fuel a b : ℕ) :
    (p∣rep (reduce fuel a b).1 ∧ p∣rep (reduce fuel a b).2) ↔ (p∣rep a ∧ p∣rep b) := by
  induction fuel generalizing a b with
  | zero => rfl
  | succ f ih =>
    rw [reduce]
    by_cases hb : b=0
    · simp [hb]
    rw [if_neg hb]
    by_cases ha : a=0
    · simp [ha]
    rw [if_neg ha]
    split
    · exact (ih _ _).trans (same_divisors _ _ _ _)
    · exact (ih _ _).trans and_comm

theorem certificate (n fuel g d : ℕ)
    (checked : reduce fuel (fibPair false n).1 (fibPair true n).1=(g,0))
    (nz : g≠0) (bits : 2^d≤g ∧ g<2^(d+1)) : (common n).natDegree=d := by
  have divisors (p:P) : p∣rep g ↔ (p∣fib X n ∧ p∣fib (X+1) n) := by
    have h := reduce_correct p fuel (fibPair false n).1 (fibPair true n).1
    rw [checked] at h
    simpa only [rep_zero,dvd_zero,and_true,(pair_correct false n).1,(pair_correct true n).1,
      Bool.false_eq_true,if_false,if_true] using h
  have ass : Associated (common n) (rep g) := associated_of_dvd_dvd
    ((divisors _).2 ⟨EuclideanDomain.gcd_dvd_left ..,EuclideanDomain.gcd_dvd_right ..⟩)
    (EuclideanDomain.dvd_gcd ((divisors _).1 dvd_rfl).1 ((divisors _).1 dvd_rfl).2)
  have d1 := natDegree_eq_of_degree_eq (degree_eq_degree_of_associated ass)
  have d2 := (rep_degree nz).2
  have lo := Nat.lt_size.mpr bits.1
  have hi := Nat.size_le.mpr bits.2
  omega


private theorem deg57 : (common 57).natDegree=0 :=
  certificate 57 29 0x1 0 (by decide +kernel) (by decide) (by decide +kernel)

private theorem deg171 : (common 171).natDegree=36 :=
  certificate 171 66 0x1415555511 36 (by decide +kernel) (by decide) (by decide +kernel)

private theorem deg513 : (common 513).natDegree=252 :=
  certificate 513 137 0x1541550554145051414010550150455441541115155105415444555005154041 252 (by decide +kernel) (by decide) (by decide +kernel)

/-- The full tower with base 57 has a second and a third distinct nullity;
every higher exponent retains the third value. -/
theorem tower57 :
    Module.finrank F (quietSpace (57-1))=0 ∧
    Module.finrank F (quietSpace (57^2-1))=36 ∧
    ∀ k : ℕ, Module.finrank F (quietSpace (57^(k+3)-1))=252 := by
  have small (k : ℕ) := nullity_reduction 57 18 k (by decide) (by decide)
  have h1 := physical 57 (by decide)
  refine ⟨h1.trans deg57,?_,?_⟩
  · rw [small 2,show Nat.gcd (57^2) (2^18-1)=171 by decide,physical _ (by decide)]
    exact deg171
  intro k
  have mod : Nat.gcd (57^(k+3)) (2^18-1)=513 := by
    have co : (361*57^k).Coprime 511 :=
      (by decide : Nat.Coprime 361 511).mul_left ((by decide : Nat.Coprime 57 511).pow_left k)
    rw [pow_add,show (57:ℕ)^3=361*513 by decide,show 2^18-1=511*513 by decide,
      show 57^k*(361*513)=(361*57^k)*513 by ring,Nat.gcd_mul_right,co.gcd_eq_one,one_mul]
  rw [small,mod,physical _ (by decide)]
  exact deg513

/-- The proposed immediate cutoff away from multiples of 21 fails. -/
theorem immediate_cutoff_fails :
    ¬ (∀ a : ℕ, Odd a → ¬21∣a → ∀ k : ℕ, 0<k →
      Module.finrank F (quietSpace (a^k-1))=Module.finrank F (quietSpace (a-1))) := by
  intro h
  have e := h 57 (by decide) (by decide) 2 (by decide)
  rw [tower57.1,tower57.2.1] at e
  contradiction

/-- The proposed universal cutoff at exponent two also fails at base 57. -/
theorem second_cutoff_fails :
    ¬ (∀ a : ℕ, Odd a → ∀ k : ℕ, 2≤k →
      Module.finrank F (quietSpace (a^k-1))=Module.finrank F (quietSpace (a^2-1))) := by
  intro h
  have e := h 57 (by decide) 3 (by decide)
  rw [tower57.2.2 0,tower57.2.1] at e
  contradiction

#print axioms tower57
#print axioms immediate_cutoff_fails
#print axioms second_cutoff_fails
end
end OddGridExamples


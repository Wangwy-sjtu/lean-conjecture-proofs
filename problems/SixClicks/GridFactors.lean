import OddGridExamples
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Algebra.Polynomial.Degree.Lemmas

/-! Translation symmetry and the dyadic factorization of square-grid boundary polynomials. -/
namespace GridFactors
open Polynomial LightsPolynomial GridGcd
open scoped Polynomial CharTwo
noncomputable section

def U : P := X*(X+1)
def flip (p : P) : P := p.comp (X+1)

theorem monic {p : P} (h : p≠0) : p.Monic := by
  have nz := leadingCoeff_ne_zero.mpr h
  exact (by decide : ∀ a : F, a≠0 → a=1) _ nz

private theorem literal {p q : P} (h : Associated p q) : p=q := by
  by_cases hp : p=0
  · subst p; exact (show q=0 by simpa using h.symm).symm
  have hq : q≠0 := by rintro rfl; exact hp (by simpa using h)
  exact eq_of_monic_of_associated (monic hp) (monic hq) h

private theorem flip_flip (p : P) : flip (flip p)=p := by
  simp [flip,comp_assoc]

theorem flip_fib (p : P) (n : ℕ) : flip (fib p n)=fib (flip p) n := by
  exact map_fib (aeval (X+1:P)).toRingHom p n

private theorem flip_dvd {p q : P} (h : p∣q) : flip p∣flip q := by
  obtain ⟨s,rfl⟩ := h
  exact ⟨flip s,mul_comp ..⟩

def commonPair (p : P) : P := EuclideanDomain.gcd p (flip p)

theorem symmetric (p : P) : flip (commonPair p)=commonPair p := by
  have divides : flip (commonPair p)∣commonPair p := EuclideanDomain.dvd_gcd
    (by simpa only [flip_flip] using flip_dvd (EuclideanDomain.gcd_dvd_right p (flip p)))
    (flip_dvd (EuclideanDomain.gcd_dvd_left p (flip p)))
  exact literal (associated_of_dvd_dvd divides (by simpa only [flip_flip] using flip_dvd divides))

private theorem decomposition (p : P) : ∃ a b : P, p=a.comp U+X*b.comp U := by
  induction p using Polynomial.induction_on with
  | C c => exact ⟨C c,0,by simp⟩
  | add p q hp hq =>
    obtain ⟨a,b,hp⟩ := hp
    obtain ⟨d,e,hq⟩ := hq
    exact ⟨a+d,b+e,by rw [hp,hq,add_comp,add_comp]; ring⟩
  | monomial j c ih =>
    obtain ⟨a,b,h⟩ := ih
    refine ⟨X*b,a+b,?_⟩
    rw [show C c*X^(j+1)=(X:P)*(C c*X^j) by ring,h,mul_comp,X_comp,add_comp]
    unfold U
    linear_combination -(X*b.comp (X*(X+1)))*(CharTwo.two_eq_zero : (2:P)=0)

theorem fixed_comp {p : P} (fixed : flip p=p) : ∃ a : P, p=a.comp U := by
  obtain ⟨a,b,h⟩ := decomposition p
  have invol : flip U=U := by simp [flip,U,mul_comp,add_comp,mul_comm]
  rw [h] at fixed
  change (a.comp U+X*b.comp U).comp (X+1)=_ at fixed
  simp only [add_comp,mul_comp,X_comp,comp_assoc,show U.comp (X+1)=U from invol,add_mul,one_mul] at fixed
  have bz : b.comp U=0 := by linear_combination fixed
  exact ⟨a,by simpa [bz] using h⟩

theorem deg_U : U.natDegree=2 := by
  rw [U,natDegree_mul X_ne_zero (by exact X_add_C_ne_zero (1:F))]
  rw [show (X+1:P)=(X+C (1:F)) by simp,natDegree_X_add_C,natDegree_X]

theorem even_degree {p : P} (h : flip p=p) : Even p.natDegree := by
  obtain ⟨a,rfl⟩ := fixed_comp h
  rw [natDegree_comp,deg_U]
  exact ⟨a.natDegree,by omega⟩

theorem common_as_pair (N : ℕ) : common N=commonPair (fib X N) := by
  unfold common commonPair
  rw [flip_fib]; simp [flip]

private theorem commonPair_sq (p : P) : commonPair (p^2) = commonPair p^2 := by
  have f : flip (p^2)=(flip p)^2 := pow_comp .. 
  have h := EuclideanDomain.gcd_eq_gcd_ab p (flip p)
  change commonPair p=_ at h
  apply literal; apply associated_of_dvd_dvd
  · rw [h,CharTwo.add_sq,mul_pow,mul_pow]
    apply dvd_add <;> apply dvd_mul_of_dvd_left
    · exact EuclideanDomain.gcd_dvd_left .. 
    · rw [commonPair,f]; exact EuclideanDomain.gcd_dvd_right ..
  · change commonPair p^2∣EuclideanDomain.gcd (p^2) (flip (p^2))
    rw [f]; apply EuclideanDomain.dvd_gcd
    · exact pow_dvd_pow_of_dvd (EuclideanDomain.gcd_dvd_left ..) 2
    · exact pow_dvd_pow_of_dvd (EuclideanDomain.gcd_dvd_right ..) 2

/-- At an odd index the common polynomial is the square of a translation-invariant polynomial. -/
theorem odd_square (m : ℕ) (odd : Odd m) :
    ∃ p : P, flip p=p ∧ common m=p^2 := by
  obtain ⟨u,rfl⟩ := odd
  let f := fib (X:P) (u+1)+fib X u
  have square : fib (X:P) (2*u+1)=f^2 := by rw [(double X u).2]; exact (CharTwo.add_sq ..).symm
  refine ⟨commonPair f,symmetric f,?_⟩
  rw [common_as_pair,square,commonPair_sq]

theorem natDegree_sq (p : P) : (p^2).natDegree=2*p.natDegree := by simp [natDegree_pow]

theorem unit_value (m : ℕ) : fib (1:F) m=0 ↔ 3∣m := by
  have tr := fib_at_one (R:=F) (m/3)
  have v2 : fib (1:F) (3*(m/3)+2)=1 := by rw [fib,tr.1,tr.2]; simp
  have d := Nat.mod_add_div m 3
  rcases (by omega : m%3=0 ∨ m%3=1 ∨ m%3=2) with h|h|h
  · have eq : m=3*(m/3) := by omega
    exact ⟨fun _ => ⟨_,eq⟩,fun _ => eq ▸ tr.1⟩
  · have eq : m=3*(m/3)+1 := by omega
    rw [show fib (1:F) m=1 from eq ▸ tr.2]; simp [Nat.dvd_iff_mod_eq_zero,h]
  · have eq : m=3*(m/3)+2 := by omega
    rw [show fib (1:F) m=1 from eq ▸ v2]; simp [Nat.dvd_iff_mod_eq_zero,h]

theorem dyadic (T : P) (s m : ℕ) :
    fib T (2^s*m)=T^(2^s-1)*(fib T m)^(2^s) := by
  induction s with
  | zero => simp
  | succ s ih =>
    have pos : 0<2^s := by positivity
    rw [pow_succ' 2, Nat.mul_assoc, (double T _).1,ih,mul_pow,← pow_mul,← pow_mul]
    rw [show 2*2^s-1=1+(2^s-1)*2 by omega,pow_add,pow_one,
      Nat.mul_comm 2 (2^s)]; ring

private theorem co_linear (p : P) (a : F) (nz : p.eval a≠0) :
    IsCoprime (X-C a) p := by
  apply (isCoprime_iff_aeval_ne_zero_of_isAlgClosed (k:=F) (AlgebraicClosure F) _ _).2
  intro t
  by_cases h : t=algebraMap F _ a
  · right
    rw [h,aeval_algebraMap_apply]
    simpa using (algebraMap F (AlgebraicClosure F)).injective.ne nz
  · left; simpa only [map_sub,aeval_X,aeval_C,sub_ne_zero] using h

private theorem eval_fib (a : F) (T : P) (m : ℕ) : (fib T m).eval a=fib (T.eval a) m :=
  map_fib (evalRingHom a) T m

private theorem coprimeU {N : ℕ} (no0 : (fib (X:P) N).eval 0≠0)
    (no1 : (fib (X+1:P) N).eval 1≠0) : IsCoprime U (common N) := by
  have h0 : IsCoprime (X:P) (fib X N) := by simpa using co_linear _ 0 no0
  have h1 : IsCoprime (X+1:P) (fib (X+1) N) := by
    simpa [CharTwo.sub_eq_add] using co_linear _ 1 no1
  exact (h0.of_isCoprime_of_dvd_right (EuclideanDomain.gcd_dvd_left ..)).mul_left
    (h1.of_isCoprime_of_dvd_right (EuclideanDomain.gcd_dvd_right ..))

private theorem coprimeU_cross {N : ℕ} (no1 : (fib (X:P) N).eval 1≠0)
    (no0 : (fib (X+1:P) N).eval 0≠0) : IsCoprime U (common N) := by
  have h0 : IsCoprime (X:P) (fib (X+1) N) := by simpa using co_linear _ 0 no0
  have h1 : IsCoprime (X+1:P) (fib X N) := by simpa [CharTwo.sub_eq_add] using co_linear _ 1 no1
  exact (h0.of_isCoprime_of_dvd_right (EuclideanDomain.gcd_dvd_right ..)).mul_left
    (h1.of_isCoprime_of_dvd_right (EuclideanDomain.gcd_dvd_left ..))

/-- Exact characteristic-two multiplicity factors at a dyadic extension of an odd index. -/
theorem dyadic_common (s m : ℕ) (odd : Odd m) :
    common (2^s*m) = (if 3∣m then U^(2^s-1) else 1)*(common m)^(2^s) := by
  let t := 2^s
  let j := t-1
  let A := fib (X:P) m
  let B := fib (X+1:P) m
  let g := common m
  let G := common (t*m)
  have ltj : j≤t := Nat.sub_le t 1
  have dA : G∣X^j*A^t := by rw [← dyadic X s m]; exact EuclideanDomain.gcd_dvd_left ..
  have dB : G∣(X+1)^j*B^t := by rw [← dyadic (X+1) s m]; exact EuclideanDomain.gcd_dvd_right ..
  have dg : g^t∣G := by
    apply EuclideanDomain.dvd_gcd
    · rw [dyadic X s m]; exact dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd (EuclideanDomain.gcd_dvd_left ..) _) _
    · rw [dyadic (X+1) s m]; exact dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd (EuclideanDomain.gcd_dvd_right ..) _) _
  have upper : G∣U^j*g^t := by
    have bz := EuclideanDomain.gcd_eq_gcd_ab A B
    change g=_ at bz
    have diff : U^j*g^t=((X+1)^j*(EuclideanDomain.gcdA A B)^t)*(X^j*A^t)+
        (X^j*(EuclideanDomain.gcdB A B)^t)*((X+1)^j*B^t) := by
      rw [bz,show t=2^s from rfl,add_pow_char_pow,mul_pow,mul_pow,U,mul_pow];ring
    rw [diff]; exact dvd_add (dvd_mul_of_dvd_right dA _) (dvd_mul_of_dvd_right dB _)
  obtain ⟨u,hu⟩ := odd
  have fzero : fib (0:F) m=1 := by rw [hu,fib_at_zero]
  by_cases three : 3∣m
  · rw [if_pos three]
    have eo : fib (1:F) m=0 := (unit_value m).2 three
    have aff : (X+1:P)∣A := by simpa [Polynomial.IsRoot,A,eval_fib,CharTwo.sub_eq_add] using
      (dvd_iff_isRoot.mpr (show (fib (X:P) m).IsRoot 1 by simpa [Polynomial.IsRoot,eval_fib] using eo))
    have lin : (X:P)∣B := by simpa using
      (dvd_iff_isRoot.mpr (show (fib (X+1:P) m).IsRoot 0 by simpa [Polynomial.IsRoot,eval_fib] using eo))
    have Udiv : U^j∣G := by
      apply EuclideanDomain.dvd_gcd
      · rw [dyadic X s m,U,mul_pow]
        exact mul_dvd_mul_left _ ((pow_dvd_pow _ ltj).trans (pow_dvd_pow_of_dvd aff _))
      · rw [dyadic (X+1) s m,U,mul_pow,mul_comm (X^j)]
        exact mul_dvd_mul_left _ ((pow_dvd_pow _ ltj).trans (pow_dvd_pow_of_dvd lin _))
    have co : IsCoprime U g := coprimeU (by simp [eval_fib,fzero]) (by simp [eval_fib,fzero])
    exact literal (associated_of_dvd_dvd upper (co.pow.mul_dvd Udiv dg))
  · rw [if_neg three,one_mul]
    have eo : fib (1:F) m≠0 := (unit_value m).not.mpr three
    have co : IsCoprime U G := coprimeU_cross
      (by simp [t,dyadic,eval_fib,eo]) (by simp [t,dyadic,eval_fib,eo])
    exact literal (associated_of_dvd_dvd (co.symm.pow_right.dvd_of_dvd_mul_left upper) dg)

#print axioms dyadic_common
end
end GridFactors

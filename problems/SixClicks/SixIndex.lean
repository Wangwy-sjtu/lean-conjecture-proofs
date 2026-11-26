import GridFactors
import OddGridExamples

/-! The known size congruence for nullity six, restated from the physical board. -/
namespace SixIndex
open LightsPolynomial LightsGrid Polynomial GridGcd GridFactors OddStabilization
open scoped Polynomial
noncomputable section

private theorem common_nz (m : ℕ) (odd : Odd m) : common m≠0 := by
  intro z
  have h : common m∣fib X m := EuclideanDomain.gcd_dvd_left ..
  rw [z,zero_dvd_iff] at h
  have e := congrArg (evalRingHom (0:F)) h
  rw [map_fib,map_zero] at e
  change fib ((X:P).eval 0) m=0 at e
  obtain ⟨u,rfl⟩ := odd
  rw [eval_X,fib_at_zero] at e
  exact one_ne_zero e

theorem base : Module.finrank F (quietSpace 11)=6 :=
  (physical 12 (by decide)).trans
    (OddGridExamples.certificate 12 30 0x78 6 (by decide +kernel) (by decide) (by decide))

theorem size (n : ℕ) (dim : Module.finrank F (quietSpace n)=6) :
    ∃ q : ℕ, Odd q ∧ n=12*q-1 := by
  have val : (common (n+1)).natDegree=6 :=
    (by simpa using (physical (n+1) (by omega)).symm.trans dim)
  obtain ⟨s,m,odd,form⟩ := Nat.exists_eq_two_pow_mul_odd (by omega : n+1≠0)
  rw [form,dyadic_common s m odd] at val
  obtain ⟨p,fix,sp⟩ := odd_square m odd
  obtain ⟨u,pu⟩ := even_degree fix
  have dm : (common m).natDegree=4*u := by rw [sp,natDegree_sq,pu];omega
  have unum : U≠0 := by change (X:P)*(X+1)≠0; exact mul_ne_zero X_ne_zero (X_add_C_ne_zero (1:F))
  by_cases three : 3∣m
  · rw [if_pos three,natDegree_mul (pow_ne_zero _ unum) (pow_ne_zero _ (common_nz m odd)),
      natDegree_pow,natDegree_pow,deg_U,dm] at val
    have hp : 0<2^s := by positivity
    have eq : 8=2^s*(4*u+2) := by
      have h : 2^s-1+1=2^s := by omega
      nlinarith only [val,h]
    have ss : s=2 := by
      by_contra bad
      rcases (by omega : s=0 ∨ s=1 ∨ 3≤s) with z|o|many
      · subst s;norm_num at eq;omega
      · subst s;norm_num at eq;omega
      · have big : 2^3≤2^s := Nat.pow_le_pow_right (by decide) many
        have high := Nat.mul_le_mul_right (4*u+2) big
        norm_num at high;omega
    obtain ⟨q,mq⟩ := three
    refine ⟨q,(Nat.odd_mul.mp (mq ▸ odd)).2,?_⟩
    rw [ss,mq] at form
    omega
  · rw [if_neg three,one_mul,natDegree_pow,dm] at val
    have impossible : 6=4*(2^s*u) := by nlinarith only [val]
    omega

/-- The known dimension formula on the entire 12 times powers of three family. -/
theorem ternary (k : ℕ) : Module.finrank F (quietSpace (12*3^k-1))=6 := by
  let z := 3^(k+1)
  have odd : Odd z := (by decide : Odd (3:ℕ)).pow
  have div : 3∣z := dvd_pow_self _ (by omega : k+1≠0)
  have one : common z∣1 := by
    obtain ⟨a,b,bez⟩ := ternary_coprime (k+1)
    rw [← bez]
    exact dvd_add (dvd_mul_of_dvd_right (EuclideanDomain.gcd_dvd_left ..) _)
      (dvd_mul_of_dvd_right (EuclideanDomain.gcd_dvd_right ..) _)
  have deg : (common z).natDegree=0 := by
    have h := natDegree_le_of_dvd one (one_ne_zero : (1:P)≠0)
    simpa using h
  have idx : 12*3^k=2^2*z := by dsimp [z];rw [pow_succ];ring
  have un : U≠0 := by change (X:P)*(X+1)≠0;exact mul_ne_zero X_ne_zero (X_add_C_ne_zero (1:F))
  rw [physical _ (by positivity),idx,dyadic_common _ _ odd,if_pos div,
    natDegree_mul (pow_ne_zero _ un) (pow_ne_zero _ (common_nz z odd)),
    natDegree_pow,natDegree_pow,deg_U,deg]
  decide

#print axioms size
#print axioms ternary
end
end SixIndex

import GridGcd
import OddTorsion

/-! A finite reduction for all odd-base power towers of square Lights Out grids. -/
namespace OddStabilization
open Polynomial LightsPolynomial LightsTorsion LightsGrid GridGcd
open scoped Polynomial CharTwo
noncomputable section

private abbrev K := AlgebraicClosure F

private theorem odd_zero {R : Type*} [CommRing R] {m : ℕ} (h : Odd m) : fib (0:R) m=1 := by
  obtain ⟨u,rfl⟩ := h
  exact fib_at_zero u

private theorem eval_fib (z : K) (p : P) (i : ℕ) :
    aeval z (fib p i) = fib (aeval z p) i := map_fib (aeval z).toRingHom p i

private theorem scalar_multiple (t : K) {m n : ℕ} (om : Odd m) (on : Odd n) :
    fib t (m*n) = fib t m * fib (t*fib t m) n := by
  by_cases zero : t=0
  · subst t; simp only [zero_mul,odd_zero om,odd_zero on,odd_zero (om.mul on),one_mul]
  obtain ⟨x,nz,wx⟩ := wave_parameter t
  have w : wave (x^m)=t*fib t m := by
    rw [← wx]; exact (by simpa only [wave,inv_pow] using (fib_wave x nz m).symm)
  have h := fib_wave (x^m) (pow_ne_zero _ nz) n
  rw [← pow_mul,inv_pow,← pow_mul,w] at h
  have l := fib_wave x nz (m*n)
  rw [wx] at l
  apply mul_left_cancel₀ zero
  rw [l,← mul_assoc,h,inv_pow]

theorem polynomial_multiple (p : P) {m n : ℕ} (om : Odd m) (on : Odd n) :
    fib p (m*n) = fib p m * fib (p*fib p m) n := by
  apply Polynomial.map_injective (algebraMap F K) (algebraMap F K).injective
  apply Polynomial.funext
  intro t
  simp only [eval_map_algebraMap,map_mul,eval_fib]
  exact scalar_multiple _ om on

private theorem new_factor {A B : P} {m n : ℕ} (om : Odd m) (on : Odd n)
    (old : ∀ t : K, fib (aeval t A) (m*n)=0 → fib (aeval t B) (m*n)=0 →
      fib (aeval t A) m=0) :
    IsCoprime (fib (A*fib A m) n) (fib B (m*n)) := by
  apply (Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed (k:=F) K _ _).2
  intro t
  by_contra! h
  have hu := h.1
  have hb := h.2
  rw [eval_fib,map_mul,eval_fib] at hu
  rw [eval_fib] at hb
  have ha : fib (aeval t A) (m*n)=0 := by rw [scalar_multiple _ om on,hu,mul_zero]
  rw [old t ha hb,mul_zero,odd_zero on] at hu
  exact one_ne_zero hu

private theorem common_descent {m n : ℕ} (om : Odd m) (on : Odd n)
    (old : ∀ t : K, fib t (m*n)=0 → fib (t+1) (m*n)=0 → fib t m=0 ∧ fib (t+1) m=0) :
    Associated (common (m*n)) (common m) := by
  have a : IsCoprime (fib ((X:P)*fib X m) n) (fib (X+1) (m*n)) := by
    apply new_factor om on
    simpa only [aeval_X,map_add,map_one] using fun t a b => (old t a b).1
  have b : IsCoprime (fib ((X+1:P)*fib (X+1) m) n) (fib X (m*n)) := by
    apply new_factor om on
    simpa only [aeval_X,map_add,map_one] using fun t b a => (old t a b).2
  let h := common (m*n)
  have hl : h∣fib X (m*n) := EuclideanDomain.gcd_dvd_left .. 
  have hr : h∣fib (X+1) (m*n) := EuclideanDomain.gcd_dvd_right ..
  have co0 := a.symm.of_isCoprime_of_dvd_left hr
  have co1 := b.symm.of_isCoprime_of_dvd_left hl
  rw [polynomial_multiple X om on] at hl
  rw [polynomial_multiple (X+1) om on] at hr
  apply associated_of_dvd_dvd
  · exact EuclideanDomain.dvd_gcd (co0.dvd_of_dvd_mul_right hl) (co1.dvd_of_dvd_mul_right hr)
  · apply EuclideanDomain.dvd_gcd
    · rw [polynomial_multiple X om on]
      exact dvd_mul_of_dvd_left (EuclideanDomain.gcd_dvd_left ..) _
    · rw [polynomial_multiple (X+1) om on]
      exact dvd_mul_of_dvd_left (EuclideanDomain.gcd_dvd_right ..) _

private theorem old_at_gcd (a e k : ℕ) (odd : Odd a) (base : a∣2^e-1) (t : K)
    (ha : fib t (a^k)=0) (hb : fib (t+1) (a^k)=0) :
    fib t ((a^k).gcd (2^e-1))=0 ∧ fib (t+1) ((a^k).gcd (2^e-1))=0 := by
  obtain ⟨x,wx,nonx,xt⟩ := odd_root_coordinate t _ odd.pow ha
  obtain ⟨y,wy,nony,yt⟩ := odd_root_coordinate (t+1) _ odd.pow hb
  obtain ⟨xd,yd⟩ := OddTorsion.odd_torsion_bound a e k odd base x y xt yt nonx nony
    (by rw [wx,wy]; simp)
  have get (z : K) (s : K) (w : wave z=s) (zn : z^(a^k)=1) (zd : z^(2^e-1)=1)
      (root : fib s (a^k)=0) : fib s ((a^k).gcd (2^e-1))=0 := by
    have zg : z^((a^k).gcd (2^e-1))=1 := orderOf_dvd_iff_pow_eq_one.mp
      (Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one zn) (orderOf_dvd_of_pow_eq_one zd))
    have zz : z≠0 := by rintro rfl; simp [odd.pos.ne'] at zn
    have ss : s≠0 := by rintro rfl; rw [odd_zero odd.pow] at root; exact one_ne_zero root
    have eq := fib_wave z zz ((a^k).gcd (2^e-1))
    rw [w,inv_pow,zg,inv_one,CharTwo.add_self_eq_zero,mul_eq_zero] at eq
    exact eq.resolve_left ss
  exact ⟨get x t wx xt xd ha,get y (t+1) wy yt yd hb⟩

/-- For every exponent, the full grid polynomial reduces to an index dividing
the fixed group order. Both polynomials have the same factors with multiplicity. -/
theorem gcd_reduction (a e k : ℕ) (odd : Odd a) (base : a∣2^e-1) :
    Associated (common (a^k)) (common ((a^k).gcd (2^e-1))) := by
  let m := (a^k).gcd (2^e-1)
  obtain ⟨n,hn⟩ := (Nat.gcd_dvd_left (a^k) (2^e-1) : m∣a^k)
  have o : Odd (m*n) := hn ▸ (odd.pow : Odd (a^k))
  have h := old_at_gcd a e k odd base
  change (∀ t : K, fib t (a^k)=0 → fib (t+1) (a^k)=0 → fib t m=0 ∧ fib (t+1) m=0) at h
  have hh : Associated (common (m*n)) (common m) :=
    common_descent (Nat.odd_mul.mp o).1 (Nat.odd_mul.mp o).2 (fun t ha hb => h t (by rwa [hn]) (by rwa [hn]))
  change Associated (common (a^k)) (common m)
  rwa [← hn] at hh

theorem physical (N : ℕ) (pos : 0<N) :
    Module.finrank F (quietSpace (N-1))=(common N).natDegree := by
  rcases N with _|n
  · omega
  rcases n with _|n
  · have h : common 1=1 := by simp [common,fib]
    rw [h,natDegree_one]
    letI : Subsingleton (Board 0) := ⟨fun b c => funext fun i => i.elim0⟩
    change Module.finrank F (quietSpace 0)=0
    exact Module.finrank_zero_of_subsingleton
  · simpa using nullity_from_gcd (n:=n+1) (by omega)

/-- The reduction is on the nullity of actual zero-boundary square boards. -/
theorem nullity_reduction (a e k : ℕ) (odd : Odd a) (base : a∣2^e-1) :
    Module.finrank F (quietSpace (a^k-1)) =
    Module.finrank F (quietSpace ((a^k).gcd (2^e-1)-1)) := by
  have pos : 0<a^k := pow_pos odd.pos _
  rw [physical _ pos,physical _ (Nat.gcd_pos_of_pos_left _ pos)]
  exact natDegree_eq_of_degree_eq (degree_eq_degree_of_associated (gcd_reduction a e k odd base))

/-- Boyles's eventual-stability question for all odd integers. -/
theorem eventually_constant (a : ℕ) (odd : Odd a) :
    ∃ k₀ : ℕ, ∀ k≥k₀,
    Module.finrank F (quietSpace (a^k-1)) = Module.finrank F (quietSpace (a^k₀-1)) := by
  classical
  let e := a.totient
  let c := 2^e-1
  have ep : 0<e := Nat.totient_pos.mpr odd.pos
  have cp : 0<c := by
    have h : (1:ℕ)<2^e := one_lt_pow₀ (by decide) ep.ne'
    dsimp [c]; omega
  have base : a∣2^e-1 := (Nat.modEq_iff_dvd' (Nat.succ_le_of_lt (pow_pos (by decide : 0<2) e))).mp
    (Nat.ModEq.pow_totient (Nat.coprime_two_left.mpr odd)).symm
  let d (j : ℕ) := (a^j).gcd c
  let s := (Finset.range (c+1)).filter (fun v => ∃ j, d j=v)
  have bound (j : ℕ) : d j ≤ c := Nat.le_of_dvd cp (Nat.gcd_dvd_right ..)
  have inside (j : ℕ) : d j∈s := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by have:=bound j; omega),⟨j,rfl⟩⟩
  have ne : s.Nonempty := ⟨_,inside 0⟩
  obtain ⟨j,hj⟩ := (Finset.mem_filter.mp (s.max'_mem ne)).2
  refine ⟨j,fun k hk => ?_⟩
  have mono : d j ∣ d k := Nat.dvd_gcd
    ((Nat.gcd_dvd_left ..).trans (pow_dvd_pow a hk)) (Nat.gcd_dvd_right ..)
  have eq : d k=d j := le_antisymm (hj ▸ s.le_max' _ (inside k))
    (Nat.le_of_dvd (Nat.gcd_pos_of_pos_left _ (pow_pos odd.pos _)) mono)
  rw [nullity_reduction a e k odd base,nullity_reduction a e j odd base]
  change Module.finrank F (quietSpace (d k-1))=Module.finrank F (quietSpace (d j-1))
  rw [eq]

#print axioms gcd_reduction
#print axioms nullity_reduction
#print axioms eventually_constant

end
end OddStabilization

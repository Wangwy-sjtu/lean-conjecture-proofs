import OddStabilization
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-! A jump of the square-grid nullity can occur at any prescribed positive exponent. -/
namespace LateJumps
open Polynomial LightsPolynomial LightsTorsion LightsGrid GridGcd OddStabilization
open scoped CharTwo
noncomputable section

private abbrev K := AlgebraicClosure F

private theorem common_root (t : K) (N : ℕ) : aeval t (common N)=0 ↔
    fib t N=0 ∧ fib (t+1) N=0 := by
  have e (p : P) : aeval t (fib p N)=fib (aeval t p) N := map_fib (aeval t).toRingHom p N
  have h : aeval t (common N)=0 ↔
      (aeval t (fib (X:P) N)=0 ∧ aeval t (fib (X+1:P) N)=0) := root_gcd_iff_root_left_right
  rw [h,e,e,map_add,aeval_X,map_one]

private theorem root_forces_power {x : K} (nz : x≠0) (N : ℕ) (root : fib (wave x) N=0) : x^N=1 := by
  apply wave_zero (pow_ne_zero _ nz)
  have h := fib_wave x nz N
  rw [root,mul_zero] at h
  simpa only [wave,inv_pow] using h.symm

private theorem power_forces_root {x : K} (nz : x≠0) (t : K) (w : wave x=t)
    (t0 : t≠0) (N : ℕ) (p : x^N=1) : fib t N=0 := by
  have h := fib_wave x nz N
  rw [w,inv_pow,p,inv_one,CharTwo.add_self_eq_zero,mul_eq_zero] at h
  exact h.resolve_left t0

private theorem wave_fiber {x y : K} (hx : x≠0) (hy : y≠0) (same : wave x=wave y) :
    x=y ∨ x=y⁻¹ := by
  unfold wave at same
  field_simp [hx,hy] at same
  have h : (x-y)*(x*y-1)=0 := by linear_combination same
  rcases mul_eq_zero.mp h with a|b
  · exact Or.inl (sub_eq_zero.mp a)
  · right; apply mul_right_cancel₀ hy
    rw [inv_mul_cancel₀ hy]; exact sub_eq_zero.mp b

private theorem power_extend {b m : ℕ} (d : b∣m) {x : K} (h : x^b=1) : x^m=1 := by
  obtain ⟨u,rfl⟩ := d; rw [pow_mul,h,one_pow]

private theorem strict_from_root (m n : ℕ) (om : Odd m) (on : Odd n) (t : K)
    (lo : fib t m≠0) (hi : fib t (m*n)=0) (hi' : fib (t+1) (m*n)=0) :
    (common m).natDegree < (common (m*n)).natDegree := by
  have d : common m∣common (m*n) := by
    apply EuclideanDomain.dvd_gcd
    · rw [polynomial_multiple X om on]
      exact dvd_mul_of_dvd_left (EuclideanDomain.gcd_dvd_left ..) _
    · rw [polynomial_multiple (X+1) om on]
      exact dvd_mul_of_dvd_left (EuclideanDomain.gcd_dvd_right ..) _
  have nz : common (m*n)≠0 := by
    intro zero
    have p := EuclideanDomain.gcd_dvd_left (fib (X:P) (m*n)) (fib (X+1) (m*n))
    change common (m*n)∣_ at p
    rw [zero,zero_dvd_iff] at p
    obtain ⟨s,os⟩ := om.mul on
    have z := congrArg (evalRingHom (0:F)) p
    rw [map_fib,map_zero] at z
    change fib ((X:P).eval 0) (m*n)=0 at z
    rw [eval_X,os,fib_at_zero] at z
    exact one_ne_zero z
  by_contra! cmp
  obtain ⟨q,h⟩ := (associated_of_dvd_of_natDegree_le d nz cmp).dvd'
  have newroot := (common_root t _).2 ⟨hi,hi'⟩
  have oldroot : aeval t (common m)=0 := by rw [h,map_mul,newroot,zero_mul]
  exact lo ((common_root t _).1 oldroot).1

/-- For every s≥1 there is an odd base at which the jump from s to s+1
is strict. The base is explicit in the proof. -/
theorem prescribed_jump (s : ℕ) (pos : 0<s) :
    ∃ a : ℕ, Odd a ∧
      Module.finrank F (quietSpace (a^s-1)) < Module.finrank F (quietSpace (a^(s+1)-1)) := by
  let q := 4^(3^s)
  let r := 3^(s+1)
  obtain ⟨u,qu⟩ := fourth_power_residue s
  let b := 1+3*u
  let c := b*(q+1)
  let a := 3*c
  have eq : q=1+r*b := qu
  have rr : r=3*3^s := pow_succ' 3 s
  have q2 : q*q=1+r*c := by change q*q=1+r*(b*(q+1)); nlinarith [congrArg (·*(q+1)) eq]
  have evenq : Even q := (by decide : Even 4).pow_of_ne_zero (by positivity : 3^s≠0)
  have oddc : Odd c := by
    have ev := evenq.mul_right q
    obtain ⟨d,hd⟩ := ev
    have oc : Odd (r*c) := Nat.odd_iff.mpr (by omega)
    exact (Nat.odd_mul.mp oc).2
  have odda : Odd a := (by decide : Odd 3).mul oddc
  have co : Nat.Coprime 3 c := by
    have q1 : q+1=2+3*(3^s*b) := by rw [eq,rr]; ring
    change Nat.Coprime 3 ((1+3*u)*(q+1))
    rw [q1]
    exact (by simp [Nat.coprime_add_mul_left_right] : Nat.Coprime 3 (1+3*u)).mul_right
      (by simpa [Nat.coprime_add_mul_left_right] using (by decide : Nat.Coprime 3 2))
  have bad : ¬ r∣a^s := by
    change ¬3^(s+1)∣(3*c)^s
    rw [mul_pow,pow_succ,Nat.mul_dvd_mul_iff_left (by positivity : 0<3^s)]
    intro h
    have d := Nat.dvd_gcd (dvd_refl 3) h
    rw [(co.pow_right s).gcd_eq_one] at d
    contradiction
  have high : r*c∣a^(s+1) := by
    change r*c∣(3*c)^(s+1)
    rw [mul_pow]
    exact Nat.mul_dvd_mul_left r (dvd_pow_self c (by omega))
  letI : NeZero (3:F) := ⟨by decide⟩
  obtain ⟨x,px⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K (3^(s+1))
  have xp : x^r=1 := px.pow_eq_one
  have xn : x≠0 := fun z => by rw [z,zero_pow (by dsimp [r]; positivity)] at xp; exact zero_ne_one xp
  have rg : 3<r := by
    have hh : (1:ℕ)<3^s := one_lt_pow₀ (by decide) pos.ne'
    rw [rr]; omega
  let t := wave x
  have tn : t≠0 := fun h => px.ne_one (by change 1<r; omega) (wave_zero xn h)
  have tnext : t+1≠0 := by
    intro zero
    have t1 : t=1 := CharTwo.add_eq_zero.mp zero
    have f3 : fib t 3=0 := by simp [t1,fib]
    exact px.pow_ne_one_of_pos_of_lt (by decide : 3≠0) rg (root_forces_power xn 3 f3)
  obtain ⟨y,yn,wy⟩ := wave_parameter (t+1)
  have qf : q=2^(2*3^s) := by rw [pow_mul]; rfl
  have xf : x^q=x := by rw [eq,pow_add,pow_one,pow_mul,xp,one_pow,mul_one]
  have frob (z : K) : (wave z)^q=wave (z^q) := by simp only [wave,qf,add_pow_char_pow,inv_pow]
  have yf : wave (y^q)=wave y := by
    rw [← frob,wy,qf,add_pow_char_pow,one_pow,← qf]
    change (wave x)^q+1=wave x+1
    rw [frob,xf]
  have yqq : y^(q*q)=y := by
    rcases wave_fiber (pow_ne_zero _ yn) yn yf with fixed|inv
    · rw [pow_mul,fixed,fixed]
    · rw [pow_mul,inv,inv_pow,inv,inv_inv]
  have yd : y^(r*c)=1 := by
    rw [q2,pow_add,pow_one] at yqq
    exact (mul_eq_left₀ yn).mp yqq
  have xhigh := power_extend ((dvd_mul_right r c).trans high) xp
  have yhigh := power_extend high yd
  have low : fib t (a^s)≠0 := fun h => bad (px.dvd_of_pow_eq_one _ (root_forces_power xn _ h))
  have h := strict_from_root (a^s) a odda.pow odda t low
    (by rw [← pow_succ]; exact power_forces_root xn t rfl tn _ xhigh)
    (by rw [← pow_succ]; exact power_forces_root yn _ wy tnext _ yhigh)
  refine ⟨a,odda,?_⟩
  rw [physical _ (pow_pos odda.pos _),physical _ (pow_pos odda.pos _),pow_succ]
  exact h

theorem no_universal_cutoff : ¬∃ k₀ : ℕ, ∀ a : ℕ, Odd a → ∀ k≥k₀,
    Module.finrank F (quietSpace (a^k-1))=Module.finrank F (quietSpace (a^k₀-1)) := by
  rintro ⟨k,h⟩
  obtain ⟨a,odd,jump⟩ := prescribed_jump (k+1) (by omega)
  rw [h a odd (k+1) (by omega),h a odd (k+1+1) (by omega)] at jump
  exact (lt_irrefl _ jump)

#print axioms prescribed_jump
#print axioms no_universal_cutoff
end
end LateJumps

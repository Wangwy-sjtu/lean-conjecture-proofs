import LightsTorsion
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.FieldTheory.Finite.Basic

/-! Finite-field descent for arbitrary odd bases on the Lights Out spectral curve. -/

namespace OddTorsion
open Finset LightsTorsion
open scoped CharTwo
attribute [local instance] Classical.propDecidable

private theorem expansion (c m : ℕ) : ∃ t : ℕ,
    (1+c)^m=1+m*c+m.choose 2*c^2+c^3*t := by
  induction m with
  | zero => exact ⟨0,by simp⟩
  | succ m ih =>
    obtain ⟨t,old⟩ := ih
    refine ⟨t+m.choose 2+c*t,?_⟩
    rw [pow_succ,old,Nat.choose_succ_succ]
    simp only [Nat.choose_one_right]
    ring

/-- The extra cofactor at each descent is congruent to 1 modulo c. -/
private theorem next_layer {a c : ℕ} (odd : Odd a) (div : a∣c) :
    ∃ t : ℕ, (1+c)^a=1+(a*c)*(1+c*t) := by
  obtain ⟨s,hs⟩ := odd
  have choose : a.choose 2=a*s := by
    rw [Nat.choose_two_right,hs,show 2*s+1-1=2*s by omega]
    rw [show (2*s+1)*(2*s)=((2*s+1)*s)*2 by ring,Nat.mul_div_cancel _ (by decide : 0<2)]
  obtain ⟨m,rfl⟩ := div
  obtain ⟨u,h⟩ := expansion (a*m) a
  refine ⟨s+m*u,?_⟩
  rw [h,choose]
  ring

variable {K : Type*} [Field K] [CharP K 2]

private def frobSum (a q : ℕ) (x : K) : K := ∑ i∈range a,x^(q^i)

private theorem frob_add (a e : ℕ) (x y : K) :
    frobSum a (2^e) (x+y)=frobSum a (2^e) x + frobSum a (2^e) y := by
  simp only [frobSum,← pow_mul,add_pow_char_pow,sum_add_distrib]

private theorem odd_cast {a : ℕ} (odd : Odd a) : (a : K)=1 := by
  obtain ⟨s,rfl⟩ := odd
  simp [CharTwo.two_eq_zero]

private theorem frob_one {a : ℕ} (odd : Odd a) (q : ℕ) : frobSum a q (1 : K)=1 := by
  simpa [frobSum] using (odd_cast (K:=K) odd)

private theorem frob_layer {a c : ℕ} (odd : Odd a) (div : a∣c) (x : K) (h : x^(c*a)=1) :
    frobSum a (1+c) x = if x^c=1 then x else 0 := by
  let z := x^c
  have za : z^a=1 := by simpa only [z,← pow_mul] using h
  have zc : z^c=1 := by
    obtain ⟨s,hs⟩ := div
    rw [hs,pow_mul,za,one_pow]
  have fixed : z^(1+c)=z := by rw [pow_add,pow_one,zc,mul_one]
  have twist : x^(1+c)=x*z := by rw [pow_add,pow_one]
  have orbit (i : ℕ) : x^((1+c)^i)=x*z^i := by
    induction i with
    | zero => simp
    | succ i ih =>
      rw [pow_succ (1+c),pow_mul,ih,mul_pow,twist,pow_right_comm z,fixed,pow_succ]
      ring
  simp only [frobSum,orbit,← mul_sum]
  change x*(∑ i∈range a,z^i) = if z=1 then x else 0
  by_cases trivial : z=1
  · simp [trivial,odd_cast (K:=K) odd]
  · have van : (∑ i∈range a,z^i) * (z-1)=0 := by rw [geom_sum_mul,za,sub_self]
    rw [if_neg trivial,(mul_eq_zero.mp van).resolve_right (sub_ne_zero.mpr trivial),mul_zero]

private theorem wave_layer {a c e : ℕ} (odd : Odd a) (div : a∣c) (q : 2^e=1+c)
    (x : K) (h : x^(c*a)=1) :
    frobSum a (2^e) (wave x) = if x^c=1 then wave x else 0 := by
  have hi : (x⁻¹)^(c*a)=1 := by simp [inv_pow,h]
  rw [wave,frob_add,q,frob_layer odd div x h,frob_layer odd div _ hi,inv_pow]
  by_cases fixed : x^c=1 <;> simp [fixed]

private theorem nonzero_wave {x : K} (nz : x≠0) (nontrivial : x≠1) : wave x≠0 := by
  intro zero
  have e : x=x⁻¹ := CharTwo.add_eq_zero.mp zero
  have sq : x^2=1 := by calc
    x^2=x*x := pow_two _
    _=x*x⁻¹ := congrArg (x*·) e
    _=1 := mul_inv_cancel₀ nz
  have z : (x+1)^2=0 := by rw [CharTwo.add_sq,sq,one_pow]; simp
  exact nontrivial (CharTwo.add_eq_zero.mp ((pow_eq_zero_iff (by decide : 2≠0)).mp z))

private theorem descend_curve {a c e : ℕ} (odd : Odd a) (div : a∣c) (q : 2^e=1+c)
    (x y : K) (nx : wave x≠0) (ny : wave y≠0) (curve : wave x+wave y=1)
    (xt : x^(c*a)=1) (yt : y^(c*a)=1) : x^c=1 ∧ y^c=1 := by
  have trace := congrArg (frobSum a (2^e) : K→K) curve
  rw [frob_add,frob_one odd,wave_layer odd div q x xt,wave_layer odd div q y yt] at trace
  by_cases fx : x^c=1 <;> by_cases fy : y^c=1
  · exact ⟨fx,fy⟩
  · simp [fx,fy] at trace
    rw [trace,add_eq_left] at curve
    exact (ny curve).elim
  · simp [fx,fy] at trace
    rw [trace,add_eq_right] at curve
    exact (nx curve).elim
  · simp [fx,fy] at trace

omit [CharP K 2] in
private theorem drop_coprime {M d t : ℕ} (co : Nat.Coprime M t) (x : K)
    (hx : x^M=1) (h : x^(d*t)=1) : x^d=1 := by
  have u : (x^d)^M=1 := by rw [pow_right_comm,hx,one_pow]
  have v : (x^d)^t=1 := by rwa [← pow_mul]
  have dv := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one u) (orderOf_dvd_of_pow_eq_one v)
  rw [co.gcd_eq_one] at dv
  simpa using orderOf_dvd_iff_pow_eq_one.mp dv

/-- With a fixed odd base a, all nontrivial a-power torsion solutions already
have orders dividing 2^e-1 as soon as a divides 2^e-1. -/
theorem odd_torsion_bound (a e k : ℕ) (odd : Odd a) (base : a∣2^e-1)
    (x y : K) (xt : x^(a^k)=1) (yt : y^(a^k)=1) (nonx : x≠1) (nony : y≠1)
    (curve : wave x+wave y=1) : x^(2^e-1)=1 ∧ y^(2^e-1)=1 := by
  let c (j : ℕ) := (2^e)^(a^j)-1
  have pos (j : ℕ) : 0<(2^e)^(a^j) := by positivity
  have eq (j : ℕ) : (2^e)^(a^j)=1+c j := by dsimp [c]; have := pos j; omega
  have grow (j : ℕ) (d : a∣c j) : ∃ t, c (j+1)=a*c j*(1+c j*t) := by
    obtain ⟨t,h⟩ := next_layer odd d
    refine ⟨t,?_⟩
    change (2^e)^(a^(j+1))-1=_
    rw [pow_succ,pow_mul,eq j,h]; omega
  have div (j : ℕ) : a∣c j := by
    induction j with
    | zero => simpa [c] using base
    | succ j ih =>
      obtain ⟨t,h⟩ := grow j ih
      rw [h]; exact dvd_mul_of_dvd_left (dvd_mul_right ..) _
  have high (j : ℕ) : a^j∣c j := by
    induction j with
    | zero => simp
    | succ j ih =>
      obtain ⟨t,h⟩ := grow j (div j)
      rw [pow_succ',h]; exact dvd_mul_of_dvd_left (Nat.mul_dvd_mul_left a ih) _
  have extend {b m : ℕ} (h : b∣m) (z : K) (hz : z^b=1) : z^m=1 := by
    obtain ⟨s,rfl⟩ := h
    rw [pow_mul,hz,one_pow]
  have nx : wave x≠0 := nonzero_wave (fun z => by subst x; simp_all [odd.pos.ne']) nonx
  have ny : wave y≠0 := nonzero_wave (fun z => by subst y; simp_all [odd.pos.ne']) nony
  have back (j : ℕ) : x^(c j)=1 → y^(c j)=1 → x^(c 0)=1 ∧ y^(c 0)=1 := by
    induction j with
    | zero => exact fun u v => ⟨u,v⟩
    | succ j ih =>
      intro hx hy
      obtain ⟨t,h⟩ := grow j (div j)
      have co0 : Nat.Coprime a (1+c j*t) := by
        obtain ⟨m,hm⟩ := div j
        rw [hm,Nat.mul_assoc,Nat.coprime_add_mul_left_right]
        exact Nat.coprime_one_right _
      have co := co0.pow_left k
      rw [h,Nat.mul_comm a (c j)] at hx hy
      have eq' : 2^(e*a^j)=1+c j := by rw [pow_mul,eq j]
      obtain ⟨fx,fy⟩ := descend_curve odd (div j) eq' x y nx ny curve
        (drop_coprime co x xt hx) (drop_coprime co y yt hy)
      exact ih fx fy
  simpa [c] using back k (extend (high k) x xt) (extend (high k) y yt)

#print axioms odd_torsion_bound

end OddTorsion

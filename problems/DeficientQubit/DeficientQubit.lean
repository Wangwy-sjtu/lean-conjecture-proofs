import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

namespace QubitGain
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1500000
abbrev Mat := Fin 3 → Fin 3 → ℝ
abbrev Vec := Fin 3 → ℝ

/-- Entrywise subgradient of the sum of absolute Pauli coefficients. -/
def Admissible (O S : Mat) : Prop := ∀ i j, |S i j| ≤ 1 ∧ S i j * O i j = |O i j|

/-- Quadratic form of S Oᵀ + O Sᵀ − ⟨S,O⟩ I, including arbitrary zero completions. -/
def compression (O S : Mat) (x : Vec) : ℝ :=
  2*(∑ j, (∑ i, S i j * x i)*(∑ i, O i j * x i)) -
    (∑ j, ∑ i, S i j * O i j) * ∑ i, x i ^ 2

def HasCertificate (O : Mat) : Prop :=
  ∃ S : Mat, Admissible O S ∧ ∀ x : Vec, compression O S x ≤ 0

/-- Orthonormal rows and columns of the real Pauli correlation matrix. -/
def Orthogonal (O : Mat) : Prop :=
  (∀ i k, ∑ j, O i j * O k j = if i=k then 1 else 0) ∧
  (∀ j k, ∑ i, O i j * O i k = if j=k then 1 else 0)

private def base (p q r s : ℝ) : Mat :=
  ![![-q*s,q*r,p], ![p*s,-p*r,q], ![r,s,0]]

private def baseSign : Mat := ![![-1,1,1], ![1,-1,1], ![1,1,0]]

private theorem elementary (p q : ℝ) (hp : 0≤p) (hq : 0≤q) (h : p^2+q^2=1) :
    p≤1 ∧ q≤1 ∧ 1≤p+q ∧ p+q≤2 := by
  have hp1 : p ≤ 1 := by nlinarith [sq_nonneg q, sq_nonneg (p-1)]
  have hq1 : q ≤ 1 := by nlinarith [sq_nonneg p, sq_nonneg (q-1)]
  refine ⟨hp1,hq1,?_,by linarith⟩
  nlinarith [mul_nonneg hp hq, mul_nonneg hp (sub_nonneg.mpr hp1), mul_nonneg hq (sub_nonneg.mpr hq1)]

private theorem base_admissible (p q r s : ℝ) (hp : 0≤p) (hq : 0≤q) (hr : 0≤r) (hs : 0≤s) :
    Admissible (base p q r s) baseSign := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [base,baseSign,abs_mul,abs_of_nonneg hp,
    abs_of_nonneg hq,abs_of_nonneg hr,abs_of_nonneg hs]

/-- Each off-diagonal cross term is paid for by its two diagonal entries. -/
private theorem pair_estimate (k t a b : ℝ) (h : |k|≤t) : 2*k*a*b ≤ t*a^2+t*b^2 := by
  have hp : 0 ≤ t+k := by linarith [(abs_le.mp h).1]
  have hm : 0 ≤ t-k := by linarith [(abs_le.mp h).2]
  nlinarith only [mul_nonneg hp (sq_nonneg (a-b)), mul_nonneg hm (sq_nonneg (a+b))]

private theorem base_negative (p q r s : ℝ) (hp : 0≤p) (hq : 0≤q) (hr : 0≤r) (hs : 0≤s)
    (hA : p^2+q^2=1) (hB : r^2+s^2=1) (x : Vec) : compression (base p q r s) baseSign x ≤ 0 := by
  obtain ⟨hp1,hq1,hA1,_⟩ := elementary p q hp hq hA
  obtain ⟨hr1,hs1,hB1,hB2⟩ := elementary r s hr hs hB
  let A := p+q
  let B := r+s
  let b := |r-s|
  have hbB : b ≤ B := abs_le.mpr ⟨by dsimp [B]; linarith, by dsimp [B]; linarith⟩
  have hb1 : b ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have h01 : |A*(1-B)| ≤ A*(B-1) := by
    rw [abs_mul,abs_of_nonneg hA,abs_of_nonpos (by dsimp [B]; linarith : 1-B≤0)]
    linarith
  have h02 : |(1-q)*(s-r)| ≤ (1-q)*b := by
    rw [abs_mul,abs_of_nonneg (by linarith : 0≤1-q),abs_sub_comm]
  have h12 : |(1-p)*(r-s)| ≤ (1-p)*b := by
    rw [abs_mul,abs_of_nonneg (by linarith : 0≤1-p)]
  have D0 : 0 ≤ B+(p-q)*(B-1) - (A*(B-1)+(1-q)*b) := by
    dsimp only [A]; nlinarith only [mul_nonneg (sub_nonneg.mpr hq1) (sub_nonneg.mpr hbB),
        mul_nonneg hq (sub_nonneg.mpr hB2)]
  have D1 : 0 ≤ B-(p-q)*(B-1) - (A*(B-1)+(1-p)*b) := by
    dsimp only [A]; nlinarith only [mul_nonneg (sub_nonneg.mpr hp1) (sub_nonneg.mpr hbB),
        mul_nonneg hp (sub_nonneg.mpr hB2)]
  have D2 : 0 ≤ A+(A-1)*B-((1-q)*b+(1-p)*b) := by
    have h2 : 0≤2-A := by dsimp [A]; linarith
    nlinarith only [mul_nonneg (sub_nonneg.mpr hA1) (show 0≤B+2 by linarith),
      mul_nonneg h2 (sub_nonneg.mpr hb1), show A=p+q by rfl]
  have M01 := pair_estimate _ _ (x 0) (x 1) h01
  have M02 := pair_estimate _ _ (x 0) (x 2) h02
  have M12 := pair_estimate _ _ (x 1) (x 2) h12
  have Q0 := mul_nonneg D0 (sq_nonneg (x 0))
  have Q1 := mul_nonneg D1 (sq_nonneg (x 1))
  have Q2 := mul_nonneg D2 (sq_nonneg (x 2))
  simp [compression,base,baseSign,Fin.sum_univ_succ]
  dsimp only [A,B] at M01 M02 M12 Q0 Q1 Q2
  nlinarith only [M01,M02,M12,Q0,Q1,Q2]
private def relabel (O : Mat) (e f : Equiv.Perm (Fin 3)) : Mat := fun i j => O (e i) (f j)
private def signed (O : Mat) (a b : Vec) : Mat := fun i j => a i*b j*O i j

private theorem compression_relabel (O S : Mat) (e f : Equiv.Perm (Fin 3)) (x : Vec) :
    compression (relabel O e f) (relabel S e f) x = compression O S (fun i => x (e.symm i)) := by
  let y := fun i => x (e.symm i)
  have column (A : Mat) (j : Fin 3) :
      (∑ i, relabel A e f i j * x i) = ∑ i, A i (f j) * y i :=
    Fintype.sum_equiv e _ _ (by intro i; simp [relabel,y])
  have total (j : Fin 3) : (∑ i, relabel S e f i j * relabel O e f i j) =
      ∑ i, S i (f j) * O i (f j) := e.bijective.sum_comp (fun i => S i (f j) * O i (f j))
  have norm : (∑ i, x i^2) = ∑ i, y i^2 := Fintype.sum_equiv e _ _ (by intro i; simp [y])
  unfold compression
  simp_rw [column,total]
  rw [f.bijective.sum_comp (fun j => (∑ i, S i j * y i)*(∑ i, O i j * y i)),
      f.bijective.sum_comp (fun j => ∑ i, S i j * O i j),norm]

private theorem certificate_relabel (O : Mat) (e f : Equiv.Perm (Fin 3)) (h : HasCertificate O) :
    HasCertificate (relabel O e f) := by
  obtain ⟨S,hS,hM⟩ := h
  exact ⟨relabel S e f,fun i j=>hS (e i) (f j),fun x=>by rw [compression_relabel]; apply hM⟩

private theorem ortho_relabel (O : Mat) (e f : Equiv.Perm (Fin 3)) (h : Orthogonal O) :
    Orthogonal (relabel O e f) := by
  constructor
  · intro i k
    exact (f.bijective.sum_comp (fun j => O (e i) j * O (e k) j)).trans (by simpa using h.1 (e i) (e k))
  · intro j k
    exact (e.bijective.sum_comp (fun i => O i (f j) * O i (f k))).trans (by simpa using h.2 (f j) (f k))

private theorem signed_product (a b x y : ℝ) (ha : a^2=1) (hb : b^2=1) :
    (a*b*x)*(a*b*y)=x*y := by
  calc
    _ = a^2*b^2*(x*y) := by ring
    _ = _ := by rw [ha,hb]; ring

private theorem compression_signed (O S : Mat) (a b x : Vec) (ha : ∀ i, (a i)^2=1)
    (hb : ∀ j, (b j)^2=1) :
    compression (signed O a b) (signed S a b) x = compression O S (fun i=>a i*x i) := by
  let y := fun i=>a i*x i
  have column (C : Mat) (j : Fin 3) :
      (∑ i, signed C a b i j * x i) = b j * ∑ i, C i j * y i := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; dsimp [signed,y]; ring
  have paired (j : Fin 3) : (∑ i, signed S a b i j * x i)*(∑ i, signed O a b i j * x i) =
      (∑ i, S i j * y i)*(∑ i, O i j * y i) := by
    rw [column,column,mul_mul_mul_comm, ←sq, hb,one_mul]
  have total (i j : Fin 3) : signed S a b i j * signed O a b i j = S i j * O i j :=
    signed_product _ _ _ _ (ha i) (hb j)
  have norm (i : Fin 3) : y i^2 = x i^2 := by dsimp [y]; rw [mul_pow,ha,one_mul]
  unfold compression
  change _ = _ - _ * ∑ i, y i ^ 2
  simp_rw [paired, total, norm]
  rfl

private theorem abs_unit (a : ℝ) (h : a^2=1) : |a|=1 := by
  rcases (sq_eq_one_iff).mp h with e|e <;> norm_num [e]

private theorem certificate_signed (O : Mat) (a b : Vec) (ha : ∀ i, (a i)^2=1)
    (hb : ∀ j, (b j)^2=1) (h : HasCertificate O) : HasCertificate (signed O a b) := by
  obtain ⟨S,hS,hM⟩ := h
  refine ⟨signed S a b, ?_, fun x=>by rw [compression_signed O S a b x ha hb]; apply hM⟩
  intro i j
  obtain ⟨h1,h2⟩ := hS i j
  constructor
  · simpa [signed,abs_mul,abs_unit _ (ha i),abs_unit _ (hb j)] using h1
  · change (a i*b j*S i j)*(a i*b j*O i j)=_
    rw [signed_product _ _ _ _ (ha i) (hb j),h2]
    simp [signed,abs_mul,abs_unit _ (ha i),abs_unit _ (hb j)]
private def param (t p q r s : ℝ) : Mat :=
  ![![t*q*s,-t*q*r,p], ![-t*p*s,t*p*r,q], ![r,s,0]]

private def eps (x : ℝ) := if x<0 then (-1:ℝ) else 1
private theorem eps_sq (x : ℝ) : (eps x)^2=1 := by unfold eps; split <;> norm_num
private theorem eps_four (x : ℝ) : (eps x)^4=1 := by unfold eps; split <;> norm_num
private theorem abs_eps (x : ℝ) : |x|=eps x*x := by
  unfold eps; split <;> rename_i h
  · rw [abs_of_neg h]; ring
  · rw [abs_of_nonneg (by linarith)]; ring

private theorem param_certificate (t p q r s : ℝ) (ht : t^2=1) (ha : p^2+q^2=1) (hb : r^2+s^2=1) :
    HasCertificate (param t p q r s) := by
  let d := -t * eps p * eps q * eps r * eps s
  let a : Vec := ![eps p,eps q,d]
  let b : Vec := ![d*eps r,d*eps s,1]
  have hd : d^2=1 := by simp [d,mul_pow,eps_sq,ht]
  have da : ∀ i, (a i)^2=1 := by intro i; fin_cases i <;> simp [a,eps_sq,hd]
  have db : ∀ i, (b i)^2=1 := by intro i; fin_cases i <;> simp [b,mul_pow,eps_sq,hd]
  have form : param t p q r s = signed (base |p| |q| |r| |s|) a b := by
    funext i j
    fin_cases i <;> fin_cases j <;> simp [param,signed,base,a,b,d,abs_eps] <;> ring_nf
    all_goals simp only [eps_sq,eps_four,ht]
    all_goals ring
  rw [form]
  apply certificate_signed _ a b da db
  exact ⟨baseSign,base_admissible _ _ _ _ (abs_nonneg _) (abs_nonneg _) (abs_nonneg _) (abs_nonneg _),
    base_negative _ _ _ _ (abs_nonneg _) (abs_nonneg _) (abs_nonneg _) (abs_nonneg _)
      (by simpa using ha) (by simpa using hb)⟩

/-- Unit vector (r,s) has (−s,r) as its real orthogonal complement. -/
private theorem perpendicular (r s x y : ℝ) (h : r^2+s^2=1) (v : r*x+s*y=0) :
    x = -s*(r*y-s*x) ∧ y = r*(r*y-s*x) := by
  constructor
  · linear_combination r*v - x*h
  · linear_combination s*v - y*h

private theorem corner (O : Mat) (ho : Orthogonal O) (hz : O 2 2=0) : HasCertificate O := by
  let A := O 0 0
  let B := O 0 1
  let C := O 1 0
  let D := O 1 1
  let p := O 0 2
  let q := O 1 2
  let r := O 2 0
  let s := O 2 1
  have ha : p^2+q^2=1 := by simpa [Fin.sum_univ_succ,hz,p,q,pow_two] using ho.2 2 2
  have hb : r^2+s^2=1 := by simpa [Fin.sum_univ_succ,hz,r,s,pow_two] using ho.1 2 2
  have h0 : r*A+s*B=0 := by simpa [Fin.sum_univ_succ,hz,A,B,r,s] using ho.1 2 0
  have h1 : r*C+s*D=0 := by simpa [Fin.sum_univ_succ,hz,C,D,r,s] using ho.1 2 1
  have h2 : p*A+q*C=0 := by simpa [Fin.sum_univ_succ,hz,A,C,p,q] using ho.2 2 0
  have h3 : p*B+q*D=0 := by simpa [Fin.sum_univ_succ,hz,B,D,p,q] using ho.2 2 1
  let k := r*B-s*A
  let l := r*D-s*C
  let t := p*l-q*k
  have hk : A= -s*k ∧ B=r*k := perpendicular _ _ _ _ hb h0
  have hl : C= -s*l ∧ D=r*l := perpendicular _ _ _ _ hb h1
  have hkl : p*k+q*l=0 := by dsimp [k,l]; linear_combination r*h3-s*h2
  have ht : k= -q*t ∧ l=p*t := perpendicular _ _ _ _ ha hkl
  have ea : A=t*q*s := by rw [hk.1,ht.1]; ring
  have eb : B= -t*q*r := by rw [hk.2,ht.1]; ring
  have ec : C= -t*p*s := by rw [hl.1,ht.2]; ring
  have ed : D=t*p*r := by rw [hl.2,ht.2]; ring
  have n0 : A^2+B^2+p^2=1 := by simpa [Fin.sum_univ_succ,A,B,p,pow_two,add_assoc] using ho.1 0 0
  have n1 : C^2+D^2+q^2=1 := by simpa [Fin.sum_univ_succ,C,D,q,pow_two,add_assoc] using ho.1 1 1
  have norm : A^2+B^2+C^2+D^2=1 := by linarith
  have tsq : t^2=1 := calc
    _ = (p^2+q^2)*(r^2+s^2)*t^2 := by rw [ha,hb]; ring
    _ = A^2+B^2+C^2+D^2 := by rw [ea,eb,ec,ed]; ring
    _ = 1 := norm
  have shape : O=param t p q r s := by
    funext i j
    fin_cases i <;> fin_cases j <;> first | exact ea | exact eb | exact ec | exact ed | exact hz | rfl
  rw [shape]; exact param_certificate _ _ _ _ _ tsq ha hb

/-- Every real orthogonal three by three matrix with a zero entry admits an
entrywise ℓ₁ subgradient with negative semidefinite Pauli compression. -/
theorem deficient_certificate (O : Mat) (ho : Orthogonal O) (hz : ∃ i j, O i j = 0) :
    HasCertificate O := by
  obtain ⟨i,j,hij⟩ := hz
  let e := Equiv.swap (2 : Fin 3) i
  let f := Equiv.swap (2 : Fin 3) j
  have h : HasCertificate (relabel O e f) := corner _ (ortho_relabel O e f ho) (by simpa [relabel,e,f] using hij)
  have h' := certificate_relabel _ e.symm f.symm h
  have undo : relabel (relabel O e f) e.symm f.symm = O := by funext u v; simp [relabel]
  rwa [undo] at h'

#print axioms deficient_certificate
end
end QubitGain
namespace QubitGain
open scoped BigOperators ComplexConjugate
open Matrix
noncomputable section
set_option maxHeartbeats 4000000
abbrev Gate := Matrix (Fin 2) (Fin 2) ℂ

/-- The usual Hermitian X,Y,Z matrices in that order. -/
def pauli : Fin 3 → Gate :=
  ![!![0,1;1,0], !![0,-Complex.I;Complex.I,0], !![1,0;0,-1]]

/-- Eq. (65) and Appendix A.7, incorporating transposition on the reference
qubit in the normalized Choi convention. -/
def correlation (U : Gate) (i j : Fin 3) : ℝ :=
  (pauli i * U * (pauli j)ᵀ * Uᴴ).trace.re / 2

private def ck (u v : ℂ) : Gate := !![u,-conj v;v,conj u]

private def quaternionCorrelation (a b c d : ℝ) : Mat :=
  ![![a^2+b^2-c^2-d^2, -2*(b*c-a*d), 2*(b*d+a*c)],
    ![2*(b*c+a*d), -(a^2-b^2+c^2-d^2), 2*(c*d-a*b)],
    ![2*(b*d-a*c), -2*(c*d+a*b), a^2-b^2-c^2+d^2]]

private theorem ck_correlations (u v : ℂ) :
    correlation (ck u v) = quaternionCorrelation u.re (-v.im) v.re (-u.im) := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp only [correlation,Matrix.trace_fin_two,Matrix.mul_apply,Matrix.conjTranspose_apply,
      Matrix.transpose_apply,Fin.sum_univ_two] <;>
    norm_num [ck,pauli,quaternionCorrelation,Complex.mul_re,Complex.mul_im,
      Complex.add_re,Complex.add_im] <;> ring

private theorem ck_orthogonal (u v : ℂ) (huv : u.re^2+u.im^2+v.re^2+v.im^2=1) :
    Orthogonal (correlation (ck u v)) := by
  rw [ck_correlations]
  have hh : (u.re^2+u.im^2+v.re^2+v.im^2)^2=1 := by rw [huv]; norm_num
  constructor <;> intro i k <;> fin_cases i <;> fin_cases k <;>
    norm_num [quaternionCorrelation,Fin.sum_univ_succ] <;> first | linear_combination hh | ring

/-- Every special unitary 2×2 complex matrix is a normalized Cayley–Klein
matrix. The proof obtains the second column from its adjugate. -/
private theorem exists_ck (U : Gate) (hu : Uᴴ*U=1) (hd : U.det=1) :
    ∃ u v : ℂ, U=ck u v ∧ u.re^2+u.im^2+v.re^2+v.im^2=1 := by
  have hma : U*U.adjugate=1 := by rw [Matrix.mul_adjugate,hd,one_smul]
  have adj : Uᴴ=U.adjugate := calc
    _ = Uᴴ*1 := (Matrix.mul_one _).symm
    _ = Uᴴ*(U*U.adjugate) := by rw [hma]
    _ = (Uᴴ*U)*U.adjugate := (Matrix.mul_assoc _ _ _).symm
    _ = _ := by rw [hu,Matrix.one_mul]
  rw [Matrix.adjugate_fin_two] at adj
  have e00 := congrArg (fun M : Gate => M 0 0) adj
  have e01 := congrArg (fun M : Gate => M 0 1) adj
  have h00 : conj (U 0 0) = U 1 1 := by simpa using e00
  have h01 : conj (U 1 0) = -U 0 1 := by simpa using e01
  refine ⟨U 0 0,U 1 0,?_,?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [ck,h00,h01]
  · have h := congrArg (fun M : Gate => (M 0 0).re) hu
    simp [Matrix.mul_apply,Fin.sum_univ_succ,Matrix.conjTranspose_apply,Complex.mul_re] at h
    nlinarith

/-- Unconditional zero-subgradient completion certificate for the actual
Choi correlations of every support-deficient single-qubit special unitary. -/
theorem gate_certificate (U : Gate) (hu : Uᴴ*U=1) (hd : U.det=1)
    (hz : ∃ i j, correlation U i j=0) : HasCertificate (correlation U) := by
  obtain ⟨u,v,rfl,hn⟩ := exists_ck U hu hd
  exact deficient_certificate _ (ck_orthogonal u v hn) hz

#print axioms gate_certificate
end
end QubitGain

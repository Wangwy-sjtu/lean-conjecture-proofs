import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Push

namespace StabilizerHalf
open scoped BigOperators ComplexConjugate ComplexOrder
open Matrix
noncomputable section
set_option maxHeartbeats 25000000
set_option maxRecDepth 20000

def sign (b : Bool) : ℤ := if b then 1 else -1

private def times (a b : Bool) : Bool := a == b

private theorem sign_times (a b : Bool) : sign (times a b) = sign a * sign b := by
  cases a <;> cases b <;> decide

/-- Lexicographic Pauli labels IX, IY, IZ, XI, ..., ZZ. -/
def pauli : Fin 15 → Matrix (Fin 4) (Fin 4) ℂ :=
  ![!![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0],
    !![0, -Complex.I, 0, 0; Complex.I, 0, 0, 0; 0, 0, 0, -Complex.I; 0, 0, Complex.I, 0],
    !![1, 0, 0, 0; 0, -1, 0, 0; 0, 0, 1, 0; 0, 0, 0, -1],
    !![0, 0, 1, 0; 0, 0, 0, 1; 1, 0, 0, 0; 0, 1, 0, 0],
    !![0, 0, 0, 1; 0, 0, 1, 0; 0, 1, 0, 0; 1, 0, 0, 0],
    !![0, 0, 0, -Complex.I; 0, 0, Complex.I, 0; 0, -Complex.I, 0, 0; Complex.I, 0, 0, 0],
    !![0, 0, 1, 0; 0, 0, 0, -1; 1, 0, 0, 0; 0, -1, 0, 0],
    !![0, 0, -Complex.I, 0; 0, 0, 0, -Complex.I; Complex.I, 0, 0, 0; 0, Complex.I, 0, 0],
    !![0, 0, 0, -Complex.I; 0, 0, -Complex.I, 0; 0, Complex.I, 0, 0; Complex.I, 0, 0, 0],
    !![0, 0, 0, -1; 0, 0, 1, 0; 0, 1, 0, 0; -1, 0, 0, 0],
    !![0, 0, -Complex.I, 0; 0, 0, 0, Complex.I; Complex.I, 0, 0, 0; 0, -Complex.I, 0, 0],
    !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, -1, 0; 0, 0, 0, -1],
    !![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, -1; 0, 0, -1, 0],
    !![0, -Complex.I, 0, 0; Complex.I, 0, 0, 0; 0, 0, 0, Complex.I; 0, 0, -Complex.I, 0],
    !![1, 0, 0, 0; 0, -1, 0, 0; 0, 0, -1, 0; 0, 0, 0, 1]]

def signed (s : Fin 15 → Bool) : Matrix (Fin 4) (Fin 4) ℂ :=
  ∑ i, ((sign (s i) : ℤ) : ℂ) • pauli i

private def u (s : Fin 15 → Bool) : Fin 3 → Bool := ![s 3,s 7,s 11]
private def v (s : Fin 15 → Bool) : Fin 3 → Bool := ![s 0,s 1,s 2]
private def C (s : Fin 15 → Bool) : Fin 3 → Fin 3 → Bool := ![![s 4,s 5,s 6],![s 8,s 9,s 10],![s 12,s 13,s 14]]

private def gauged (s : Fin 15 → Bool) (i j : Fin 3) : Bool := times (times (u s i) (v s j)) (C s i j)

private def orientation (s : Fin 15 → Bool) : Bool :=
  times (times (times (u s 0) (u s 1)) (u s 2)) (times (times (v s 0) (v s 1)) (v s 2))

private def minor (d : Fin 3 → Fin 3 → Bool) (i j : Fin 3) : ℤ :=
  sign (d (i+1) (j+1)) * sign (d (i+2) (j+2)) -
  sign (d (i+1) (j+2)) * sign (d (i+2) (j+1))

private def linearCoeff (d : Fin 3 → Fin 3 → Bool) (h : Bool) : ℤ :=
  -8 * ((∑ i, ∑ j, sign (d i j)) -
    sign h * ∑ j, sign (d 0 j) * minor d 0 j)

private def constantCoeff (d : Fin 3 → Fin 3 → Bool) (h : Bool) : ℤ :=
  225 - 4 * ((∑ i, (∑ j, sign (d i j))^2) + (∑ j, (∑ i, sign (d i j))^2) +
     ∑ i, ∑ j, (1-sign h * minor d i j)^2)

private theorem finite_bound : ∀ (d : Fin 3 → Fin 3 → Bool) (h : Bool),
    -72 ≤ linearCoeff d h ∧ -27 ≤ constantCoeff d h := by decide +kernel

private def c0 (s : Fin 15 → Bool) : ℤ :=
    45
    - 8 * sign (s 0) * sign (s 1) * sign (s 4) * sign (s 5)
    - 8 * sign (s 0) * sign (s 2) * sign (s 4) * sign (s 6)
    - 8 * sign (s 1) * sign (s 2) * sign (s 5) * sign (s 6)
    - 8 * sign (s 3) * sign (s 4) * sign (s 7) * sign (s 8)
    - 8 * sign (s 3) * sign (s 5) * sign (s 7) * sign (s 9)
    - 8 * sign (s 0) * sign (s 1) * sign (s 8) * sign (s 9)
    + 8 * sign (s 4) * sign (s 5) * sign (s 8) * sign (s 9)
    - 8 * sign (s 3) * sign (s 6) * sign (s 7) * sign (s 10)
    - 8 * sign (s 0) * sign (s 2) * sign (s 8) * sign (s 10)
    + 8 * sign (s 4) * sign (s 6) * sign (s 8) * sign (s 10)
    - 8 * sign (s 1) * sign (s 2) * sign (s 9) * sign (s 10)
    + 8 * sign (s 5) * sign (s 6) * sign (s 9) * sign (s 10)
    - 8 * sign (s 2) * sign (s 5) * sign (s 8) * sign (s 11)
    + 8 * sign (s 1) * sign (s 6) * sign (s 8) * sign (s 11)
    + 8 * sign (s 2) * sign (s 4) * sign (s 9) * sign (s 11)
    - 8 * sign (s 0) * sign (s 6) * sign (s 9) * sign (s 11)
    - 8 * sign (s 1) * sign (s 4) * sign (s 10) * sign (s 11)
    + 8 * sign (s 0) * sign (s 5) * sign (s 10) * sign (s 11)
    + 8 * sign (s 2) * sign (s 5) * sign (s 7) * sign (s 12)
    - 8 * sign (s 1) * sign (s 6) * sign (s 7) * sign (s 12)
    - 8 * sign (s 2) * sign (s 3) * sign (s 9) * sign (s 12)
    + 8 * sign (s 1) * sign (s 3) * sign (s 10) * sign (s 12)
    - 8 * sign (s 3) * sign (s 4) * sign (s 11) * sign (s 12)
    - 8 * sign (s 7) * sign (s 8) * sign (s 11) * sign (s 12)
    - 8 * sign (s 2) * sign (s 4) * sign (s 7) * sign (s 13)
    + 8 * sign (s 0) * sign (s 6) * sign (s 7) * sign (s 13)
    + 8 * sign (s 2) * sign (s 3) * sign (s 8) * sign (s 13)
    - 8 * sign (s 0) * sign (s 3) * sign (s 10) * sign (s 13)
    - 8 * sign (s 3) * sign (s 5) * sign (s 11) * sign (s 13)
    - 8 * sign (s 7) * sign (s 9) * sign (s 11) * sign (s 13)
    - 8 * sign (s 0) * sign (s 1) * sign (s 12) * sign (s 13)
    + 8 * sign (s 4) * sign (s 5) * sign (s 12) * sign (s 13)
    + 8 * sign (s 8) * sign (s 9) * sign (s 12) * sign (s 13)
    + 8 * sign (s 1) * sign (s 4) * sign (s 7) * sign (s 14)
    - 8 * sign (s 0) * sign (s 5) * sign (s 7) * sign (s 14)
    - 8 * sign (s 1) * sign (s 3) * sign (s 8) * sign (s 14)
    + 8 * sign (s 0) * sign (s 3) * sign (s 9) * sign (s 14)
    - 8 * sign (s 3) * sign (s 6) * sign (s 11) * sign (s 14)
    - 8 * sign (s 7) * sign (s 10) * sign (s 11) * sign (s 14)
    - 8 * sign (s 0) * sign (s 2) * sign (s 12) * sign (s 14)
    + 8 * sign (s 4) * sign (s 6) * sign (s 12) * sign (s 14)
    + 8 * sign (s 8) * sign (s 10) * sign (s 12) * sign (s 14)
    - 8 * sign (s 1) * sign (s 2) * sign (s 13) * sign (s 14)
    + 8 * sign (s 5) * sign (s 6) * sign (s 13) * sign (s 14)
    + 8 * sign (s 9) * sign (s 10) * sign (s 13) * sign (s 14)

private def c1 (s : Fin 15 → Bool) : ℤ :=
    -8 * sign (s 0) * sign (s 3) * sign (s 4)
    - 8 * sign (s 1) * sign (s 3) * sign (s 5)
    - 8 * sign (s 2) * sign (s 3) * sign (s 6)
    - 8 * sign (s 0) * sign (s 7) * sign (s 8)
    - 8 * sign (s 1) * sign (s 7) * sign (s 9)
    - 8 * sign (s 2) * sign (s 7) * sign (s 10)
    - 8 * sign (s 6) * sign (s 9) * sign (s 12)
    + 8 * sign (s 5) * sign (s 10) * sign (s 12)
    - 8 * sign (s 0) * sign (s 11) * sign (s 12)
    + 8 * sign (s 6) * sign (s 8) * sign (s 13)
    - 8 * sign (s 4) * sign (s 10) * sign (s 13)
    - 8 * sign (s 1) * sign (s 11) * sign (s 13)
    - 8 * sign (s 5) * sign (s 8) * sign (s 14)
    + 8 * sign (s 4) * sign (s 9) * sign (s 14)
    - 8 * sign (s 2) * sign (s 11) * sign (s 14)

private theorem powZ2 (b : Bool) : (sign b)^2 = 1 := by cases b <;> norm_num [sign]
private theorem powR2 (b : Bool) : ((sign b : ℝ))^2 = 1 := by cases b <;> norm_num [sign]
private theorem powZ4 (b : Bool) : (sign b)^4 = 1 := by cases b <;> norm_num [sign]
private theorem powR4 (b : Bool) : ((sign b : ℝ))^4 = 1 := by cases b <;> norm_num [sign]


private theorem gauge_coeffs (s : Fin 15 → Bool) :
    c1 s = linearCoeff (gauged s) (orientation s) ∧ c0 s = constantCoeff (gauged s) (orientation s) := by
  constructor <;> simp [c1,c0,linearCoeff,constantCoeff,gauged,orientation,C,u,v,minor, sign_times,Fin.sum_univ_succ,Fin.reduceAdd] <;> ring_nf <;> simp only [powZ2,powZ4] <;> ring


private def explicitMatrix (s : Fin 15 → Bool) : Matrix (Fin 4) (Fin 4) ℂ :=
  !![(sign (s 2) : ℂ) + (sign (s 11) : ℂ) + (sign (s 14) : ℂ), (sign (s 0) : ℂ) - (sign (s 1) : ℂ) * Complex.I + (sign (s 12) : ℂ) - (sign (s 13) : ℂ) * Complex.I, (sign (s 3) : ℂ) + (sign (s 6) : ℂ) - (sign (s 7) : ℂ) * Complex.I - (sign (s 10) : ℂ) * Complex.I, (sign (s 4) : ℂ) - (sign (s 5) : ℂ) * Complex.I - (sign (s 8) : ℂ) * Complex.I - (sign (s 9) : ℂ); (sign (s 0) : ℂ) + (sign (s 1) : ℂ) * Complex.I + (sign (s 12) : ℂ) + (sign (s 13) : ℂ) * Complex.I, -(sign (s 2) : ℂ) + (sign (s 11) : ℂ) - (sign (s 14) : ℂ), (sign (s 4) : ℂ) + (sign (s 5) : ℂ) * Complex.I - (sign (s 8) : ℂ) * Complex.I + (sign (s 9) : ℂ), (sign (s 3) : ℂ) - (sign (s 6) : ℂ) - (sign (s 7) : ℂ) * Complex.I + (sign (s 10) : ℂ) * Complex.I; (sign (s 3) : ℂ) + (sign (s 6) : ℂ) + (sign (s 7) : ℂ) * Complex.I + (sign (s 10) : ℂ) * Complex.I, (sign (s 4) : ℂ) - (sign (s 5) : ℂ) * Complex.I + (sign (s 8) : ℂ) * Complex.I + (sign (s 9) : ℂ), (sign (s 2) : ℂ) - (sign (s 11) : ℂ) - (sign (s 14) : ℂ), (sign (s 0) : ℂ) - (sign (s 1) : ℂ) * Complex.I - (sign (s 12) : ℂ) + (sign (s 13) : ℂ) * Complex.I; (sign (s 4) : ℂ) + (sign (s 5) : ℂ) * Complex.I + (sign (s 8) : ℂ) * Complex.I - (sign (s 9) : ℂ), (sign (s 3) : ℂ) - (sign (s 6) : ℂ) + (sign (s 7) : ℂ) * Complex.I - (sign (s 10) : ℂ) * Complex.I, (sign (s 0) : ℂ) + (sign (s 1) : ℂ) * Complex.I - (sign (s 12) : ℂ) - (sign (s 13) : ℂ) * Complex.I, -(sign (s 2) : ℂ) - (sign (s 11) : ℂ) + (sign (s 14) : ℂ)]

private theorem signed_explicit (s : Fin 15 → Bool) : signed s = explicitMatrix s := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [signed,pauli,explicitMatrix,Fin.sum_univ_succ] <;> ring

theorem signed_hermitian (s : Fin 15 → Bool) : (signed s).IsHermitian := by
  rw [signed_explicit]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [explicitMatrix, Matrix.conjTranspose_apply] <;> ring

private theorem determinant_four (A : Matrix (Fin 4) (Fin 4) ℂ) : A.det =
    A 0 0 * A 1 1 * A 2 2 * A 3 3
     - A 0 0 * A 1 1 * A 2 3 * A 3 2
     - A 0 0 * A 1 2 * A 2 1 * A 3 3
     + A 0 0 * A 1 2 * A 2 3 * A 3 1
     + A 0 0 * A 1 3 * A 2 1 * A 3 2
     - A 0 0 * A 1 3 * A 2 2 * A 3 1
     - A 0 1 * A 1 0 * A 2 2 * A 3 3
     + A 0 1 * A 1 0 * A 2 3 * A 3 2
     + A 0 1 * A 1 2 * A 2 0 * A 3 3
     - A 0 1 * A 1 2 * A 2 3 * A 3 0
     - A 0 1 * A 1 3 * A 2 0 * A 3 2
     + A 0 1 * A 1 3 * A 2 2 * A 3 0
     + A 0 2 * A 1 0 * A 2 1 * A 3 3
     - A 0 2 * A 1 0 * A 2 3 * A 3 1
     - A 0 2 * A 1 1 * A 2 0 * A 3 3
     + A 0 2 * A 1 1 * A 2 3 * A 3 0
     + A 0 2 * A 1 3 * A 2 0 * A 3 1
     - A 0 2 * A 1 3 * A 2 1 * A 3 0
     - A 0 3 * A 1 0 * A 2 1 * A 3 2
     + A 0 3 * A 1 0 * A 2 2 * A 3 1
     + A 0 3 * A 1 1 * A 2 0 * A 3 2
     - A 0 3 * A 1 1 * A 2 2 * A 3 0
     - A 0 3 * A 1 2 * A 2 0 * A 3 1
     + A 0 3 * A 1 2 * A 2 1 * A 3 0
    := by
  rw [Matrix.det_succ_row_zero]
  simp [Matrix.det_fin_three, Matrix.submatrix_apply, Fin.sum_univ_succ,
    show (1:Fin 4).succAbove 2 = 3 by decide, show (2:Fin 4).succAbove 2 = 3 by decide,
    show (3:Fin 4).succAbove 2 = 2 by decide]
  ring

private theorem det_formula (s : Fin 15 → Bool) (t : ℝ) :
    (Matrix.scalar (Fin 4) (t : ℂ) - signed s).det =
      ((t^4-30*t^2+(c1 s : ℝ)*t+(c0 s : ℝ) : ℝ) : ℂ) := by
  rw [signed_explicit, determinant_four]
  apply Complex.ext <;>
    simp [explicitMatrix, c0, c1, Matrix.scalar_apply, Complex.mul_re,
      Complex.mul_im, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
      Complex.neg_re, Complex.neg_im] <;>
    (try ring_nf) <;> (try simp only [← Complex.ofReal_pow, Complex.ofReal_re, Complex.ofReal_im, powR2,powR4]) <;> ring

/-- The extremal sum of the absolute values of the fifteen nonidentity expectations. -/
def limit : ℝ := 3 + 2 * Real.sqrt 3

private theorem upper_quartic (a b t : ℝ) (ha : -72 ≤ a) (hb : -27 ≤ b) (ht : limit < t) :
    0 < t^4 - 30*t^2 + a*t + b := by
  have hr : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg _
  have hsq : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h1 : 0 < t - (3 + 2*Real.sqrt 3) := sub_pos.mpr ht
  have h2 : 0 < t - (3 - 2*Real.sqrt 3) := by linarith
  have h3 : 0 < t+3 := by linarith
  have hprod := mul_pos (sq_pos_of_pos h3) (mul_pos h1 h2)
  have hid : (t+3)^2 * ((t-(3+2*Real.sqrt 3))*(t-(3-2*Real.sqrt 3))) =
      t^4-30*t^2-72*t-27 := by ring_nf; rw [hsq]; ring
  rw [hid] at hprod
  have hterm : 0 ≤ (a+72)*t := mul_nonneg (by linarith) (by linarith)
  linarith

def rawExpectation (A : Matrix (Fin 4) (Fin 4) ℂ) (w : Fin 4 → ℂ) : ℝ :=
  (star w ⬝ᵥ (A *ᵥ w)).re

def mass (w : Fin 4 → ℂ) : ℝ := (star w ⬝ᵥ w).re

/-- A nonzero vector representing a two-qubit pure state. Dividing by mass removes its norm. -/
structure PureState where
  amplitude : Fin 4 → ℂ
  positive_mass : 0 < mass amplitude

def expectation (s : PureState) (i : Fin 15) : ℝ :=
  rawExpectation (pauli i) s.amplitude / mass s.amplitude

private theorem rayleigh_bound (A : Matrix (Fin 4) (Fin 4) ℂ) (hA : A.IsHermitian)
    (hdet : ∀ t : ℝ, limit < t → (Matrix.scalar (Fin 4) (t : ℂ) - A).det ≠ 0)
    (w : Fin 4 → ℂ) : rawExpectation A w ≤ limit * mass w := by
  let B := Matrix.scalar (Fin 4) (limit : ℂ) - A
  have hId : (Matrix.scalar (Fin 4) (limit : ℂ)).IsHermitian := by
    rw [Matrix.scalar_apply,Matrix.isHermitian_diagonal_iff]
    intro i
    simp [IsSelfAdjoint]
  have hB : B.IsHermitian := hId.sub hA
  have hp : B.PosSemidef := by
    apply hB.posSemidef_iff_eigenvalues_nonneg.mpr
    intro i
    let r := hB.eigenvalues i
    by_contra! neg
    have hr : (r : ℂ) ∈ spectrum ℂ B :=
      (spectrum.algebraMap_mem_iff ℂ).mpr (hB.eigenvalues_mem_spectrum_real i)
    have hzero : (Matrix.scalar (Fin 4) (r : ℂ) - B).det = 0 := by
      simpa [Polynomial.IsRoot, Matrix.eval_charpoly] using Matrix.mem_spectrum_iff_isRoot_charpoly.mp hr
    have hid : Matrix.scalar (Fin 4) (r : ℂ) - B = -(Matrix.scalar (Fin 4) ((limit-r : ℝ) : ℂ)-A) := by
      unfold B
      push_cast
      rw [map_sub]
      abel
    rw [hid, Matrix.det_neg] at hzero
    have hz : (Matrix.scalar (Fin 4) ((limit-r : ℝ) : ℂ)-A).det = 0 := by
      simpa using hzero
    exact hdet (limit-r) (by change hB.eigenvalues i < 0 at neg; dsimp [r]; linarith) hz
  have h := hp.re_dotProduct_nonneg w
  change 0 ≤ (star w ⬝ᵥ (B *ᵥ w)).re at h
  have hid : Matrix.scalar (Fin 4) (limit : ℂ) *ᵥ w = (limit : ℂ) • w := by
    rw [Matrix.scalar_apply]; ext i; simp [Matrix.mulVec_diagonal]
  simp only [B, Matrix.sub_mulVec, dotProduct_sub, hid, dotProduct_smul,
    smul_eq_mul, Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero] at h
  exact sub_nonneg.mp h

private theorem combine_expectations (s : Fin 15 → Bool) (w : Fin 4 → ℂ) :
    rawExpectation (signed s) w = ∑ i, (sign (s i) : ℝ)*rawExpectation (pauli i) w := by
  simp [signed, rawExpectation, Matrix.sum_mulVec, dotProduct_sum,
     Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, Complex.mul_re]

private def toSign (a : ℝ) : Bool := decide (0 ≤ a)

private theorem toSign_abs (x : ℝ) : (sign (toSign x) : ℝ)*x = |x| := by
  by_cases h : 0 ≤ x
  · simp [toSign,sign,h,abs_of_nonneg h]
  · simp [toSign,sign,h,abs_of_neg (lt_of_not_ge h)]

def stabilizerNorm (s : PureState) : ℝ := (1+∑ i, |expectation s i|)/4

def halfEntropy (s : PureState) : ℝ := 2 * Real.log (stabilizerNorm s)

/-- The vector in footnote 2 of the Liu–Low–Yin preprint (footnote 4 in the journal). Its squared norm is 12. -/
private def footnoteVector : Fin 4 → ℂ :=
  ![0, -1 + Complex.I * (Real.sqrt 3 : ℝ), (Real.sqrt 3 : ℝ) - Complex.I, 2]

private theorem footnote_mass : mass footnoteVector = 12 := by
  have hs : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  simp [mass,footnoteVector, dotProduct, Fin.sum_univ_succ, Complex.mul_re,
    Complex.mul_im, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im]
  nlinarith

def footnote : PureState := ⟨footnoteVector, footnote_mass ▸ (by norm_num)⟩

private theorem footnote_expected : (fun i => rawExpectation (pauli i) footnoteVector) =
    ![4*Real.sqrt 3,4,-4,-4,-4*Real.sqrt 3,4,4,-4*Real.sqrt 3,-4,-4*Real.sqrt 3,
      4*Real.sqrt 3,-4,-4*Real.sqrt 3,-4,-4] := by
  have hs : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  funext i
  fin_cases i <;>
    simp [rawExpectation,pauli,footnoteVector,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,
      Complex.mul_re,Complex.mul_im,Complex.add_re,Complex.add_im,Complex.sub_re,Complex.sub_im,
      Complex.neg_re,Complex.neg_im] <;>
    nlinarith

theorem footnote_norm : stabilizerNorm footnote = 1 + Real.sqrt 3 / 2 := by
  have hs : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg _
  unfold stabilizerNorm expectation footnote
  simp only [footnote_mass]
  change (1 + ∑ i, |(fun j => rawExpectation (pauli j) footnoteVector) i / 12|) / 4 = _
  rw [footnote_expected]
  simp [Fin.sum_univ_succ, abs_div, abs_mul, abs_of_nonneg hs]
  ring

private abbrev Canonical := (Fin 3 → Fin 3 → Bool) × Bool
private abbrev Free := Fin 5 → Bool

private def splitSign (s : Fin 15 → Bool) : Canonical × Free :=
  ((gauged s,orientation s), ![u s 0,u s 1,u s 2,v s 0,v s 1])

private def rebuild (w : Canonical × Free) : Fin 15 → Bool :=
  let d := w.1.1
  let h := w.1.2
  let f := w.2
  let u : Fin 3 → Bool := ![f 0,f 1,f 2]
  let v : Fin 3 → Bool := ![f 3,f 4,times (times (times (f 0) (f 1)) (f 2)) (times (times (f 3) (f 4)) h)]
  let c := fun i j => times (times (u i) (v j)) (d i j)
  ![v 0,v 1,v 2,u 0,c 0 0,c 0 1,c 0 2,u 1,c 1 0,c 1 1,c 1 2,u 2,c 2 0,c 2 1,c 2 2]

private theorem sign_injective : Function.Injective sign := by
  intro a b h
  cases a <;> cases b <;> simp_all [sign]

private def signEquiv : (Fin 15 → Bool) ≃ Canonical × Free where
  toFun := splitSign
  invFun := rebuild
  left_inv s := by
    funext i
    fin_cases i <;> apply sign_injective <;> simp [rebuild,splitSign,u,v,C,gauged,orientation,sign_times]
    all_goals ring_nf
    all_goals simp only [powZ2,powZ4]
    all_goals ring
  right_inv w := by
    obtain ⟨⟨d,h⟩,f⟩ := w
    apply Prod.ext
    · apply Prod.ext
      · funext i j
        fin_cases i <;> fin_cases j <;> apply sign_injective <;> simp [rebuild,splitSign,u,v,C,gauged,orientation,sign_times]
        all_goals ring_nf
        all_goals simp only [powZ2,powZ4]
        all_goals ring
      · apply sign_injective
        simp [rebuild,splitSign,u,v,orientation,sign_times]
        ring_nf
        simp only [powZ2]
        ring
    · funext i
      fin_cases i <;> simp [rebuild,splitSign,u,v,orientation,times]

private def winning (z : Canonical) : Prop :=
  linearCoeff z.1 z.2 = -72 ∧ constantCoeff z.1 z.2 = -27

private instance (z : Canonical) : Decidable (winning z) := by unfold winning; infer_instance

private theorem twenty_sign_classes : Fintype.card {z : Canonical // winning z} = 20 := by
  decide +kernel

private def winningEquiv :
    {s : Fin 15 → Bool // winning (splitSign s).1} ≃ {z : Canonical // winning z} × Free where
  toFun s := (⟨(splitSign s.val).1,s.property⟩,(splitSign s.val).2)
  invFun w := ⟨rebuild (w.1.val,w.2), by
    have h := signEquiv.right_inv (w.1.val,w.2)
    change splitSign (rebuild (w.1.val,w.2)) = (w.1.val,w.2) at h
    rw [h]; exact w.1.property⟩
  left_inv s := Subtype.ext (signEquiv.left_inv s.val)
  right_inv w := by
    obtain ⟨⟨z,hz⟩,f⟩ := w
    have h := signEquiv.right_inv (z,f)
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg Prod.fst h
    · change (splitSign (rebuild (z,f))).2 = f
      exact congrArg (fun w : Canonical × Free => w.2) h

/-- Exactly 640 signs have the largest possible real spectral root. -/
private theorem count_winning_signs :
    Fintype.card {s : Fin 15 → Bool // winning (splitSign s).1} = 640 := by
  rw [Fintype.card_congr winningEquiv, Fintype.card_prod, twenty_sign_classes]
  decide

private theorem winning_iff_det (s : Fin 15 → Bool) :
    winning (splitSign s).1 ↔ (Matrix.scalar (Fin 4) (limit : ℂ) - signed s).det = 0 := by
  obtain ⟨ha,hb⟩ := finite_bound (gauged s) (orientation s)
  rw [← (gauge_coeffs s).1] at ha
  rw [← (gauge_coeffs s).2] at hb
  change (linearCoeff (gauged s) (orientation s) = -72 ∧ constantCoeff (gauged s) (orientation s) = -27) ↔ _
  rw [← (gauge_coeffs s).1, ← (gauge_coeffs s).2, det_formula]
  have hs : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg _
  have hs2 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hp : 0 < limit := by unfold limit; linarith
  have base : limit^4-30*limit^2-72*limit-27 = 0 := by
    unfold limit
    nlinarith [hs2, congrArg (fun t : ℝ => t*t) hs2, congrArg (fun t : ℝ => t*Real.sqrt 3) hs2]
  have idn : limit^4-30*limit^2+(c1 s:ℝ)*limit+(c0 s:ℝ) =
      ((c1 s:ℝ)+72)*limit+((c0 s:ℝ)+27) := by linarith
  rw [idn]
  constructor
  · rintro ⟨hn,hm⟩
    rw [hn,hm]
    norm_num
  · intro he
    have z : ((c1 s:ℝ)+72)*limit+((c0 s:ℝ)+27)=0 := by exact_mod_cast he
    have u : -72 ≤ (c1 s : ℝ) := by exact_mod_cast ha
    have v : -27 ≤ (c0 s : ℝ) := by exact_mod_cast hb
    have v1 : (c1 s:ℝ)+72=0 := by
      by_contra hh
      have hprod := mul_pos (lt_of_le_of_ne (by linarith : 0 ≤ (c1 s:ℝ)+72) (Ne.symm hh)) hp
      linarith
    have v2 : (c0 s:ℝ)+27=0 := by rw [v1, zero_mul, zero_add] at z; exact z
    exact ⟨by exact_mod_cast (show (c1 s : ℝ) = -72 by linarith),
      by exact_mod_cast (show (c0 s : ℝ) = -27 by linarith)⟩

/-- Exactly 640 of the 2^15 signed Hermitian Pauli sums attain the upper spectral endpoint. -/
theorem count_extremal_signs :
    Nat.card {s : Fin 15 → Bool // (Matrix.scalar (Fin 4) (limit : ℂ) - signed s).det = 0} = 640 := by
  rw [Nat.card_congr (Equiv.subtypeEquivRight fun s => (winning_iff_det s).symm)]
  rw [Nat.card_eq_fintype_card, count_winning_signs]

/-- The two-qubit spectral upper bound proposed in Liabøtrø (2017), expressed
as a quadratic-form bound applying to every complex vector and every sign choice. -/
theorem signed_rayleigh (s : Fin 15 → Bool) (w : Fin 4 → ℂ) :
    rawExpectation (signed s) w ≤ limit * mass w := by
  obtain ⟨ha,hb⟩ := finite_bound (gauged s) (orientation s)
  rw [← (gauge_coeffs s).1] at ha
  rw [← (gauge_coeffs s).2] at hb
  apply rayleigh_bound (signed s) (signed_hermitian s) _ w
  intro t ht
  rw [det_formula]
  have h := upper_quartic (c1 s) (c0 s) t (by exact_mod_cast ha) (by exact_mod_cast hb) ht
  exact_mod_cast h.ne'

/-- The sharp physical bound on the 15 nonidentity absolute Pauli means. -/
theorem pauli_l1_le (s : PureState) : (∑ i, |expectation s i|) ≤ limit := by
  let w := s.amplitude
  let mask := fun i => toSign (rawExpectation (pauli i) w)
  have h := signed_rayleigh mask w
  rw [combine_expectations] at h
  simp only [mask, toSign_abs] at h
  unfold expectation
  simp_rw [abs_div, abs_of_pos s.positive_mass]
  rw [← Finset.sum_div]
  exact (div_le_iff₀ s.positive_mass).mpr h

theorem norm_le (s : PureState) : stabilizerNorm s ≤ 1 + Real.sqrt 3 / 2 := by
  have h := pauli_l1_le s
  unfold limit at h
  unfold stabilizerNorm
  linarith

theorem stabilizer_norm_maximum : IsGreatest (Set.range stabilizerNorm) (1 + Real.sqrt 3 / 2) :=
  ⟨⟨footnote,footnote_norm⟩, fun _ ⟨s, h⟩ => h ▸ norm_le s⟩

/-- Exact order-one-half SRE maximum, with natural logarithms. -/
theorem half_entropy_maximum : IsGreatest (Set.range halfEntropy) (2*Real.log (1+Real.sqrt 3/2)) := by
  constructor
  · exact ⟨footnote, by simp [halfEntropy,footnote_norm]⟩
  · rintro _ ⟨s,rfl⟩
    have h : 0 < stabilizerNorm s := by
      unfold stabilizerNorm
      have hh : 0 ≤ ∑ i, |expectation s i| := Finset.sum_nonneg fun _ _ => abs_nonneg _
      linarith
    exact mul_le_mul_of_nonneg_left (Real.log_le_log h (norm_le s)) (by norm_num)

#print axioms det_formula
#print axioms gauge_coeffs
#print axioms count_extremal_signs
#print axioms signed_rayleigh
#print axioms footnote_norm
#print axioms stabilizer_norm_maximum
#print axioms half_entropy_maximum
end
end StabilizerHalf

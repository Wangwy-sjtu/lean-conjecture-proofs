import Mathlib.Analysis.Fourier.ZMod
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open Finset Complex AddChar
open scoped BigOperators ComplexConjugate
namespace OneSidedSchmidt
variable {N : ℕ} [NeZero N]

private theorem char_conjugate (x : ZMod N) : conj (ZMod.stdAddChar x) = ZMod.stdAddChar (-x) := by
  change conj (ZMod.toCircle x : ℂ) = (ZMod.toCircle (-x) : ℂ)
  rw [AddChar.map_neg_eq_inv, Circle.coe_inv_eq_conj]

private theorem orthogonal (s : ZMod N) : (∑ b : ZMod N, ZMod.stdAddChar (s*b)) = if s=0 then (N:ℂ) else 0 := by
  split_ifs with h
  · simp [h, ZMod.card, map_zero_eq_one]
  · exact sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar N h)

private theorem norm_sq_complex (z : ℂ) : ((‖z‖^2 : ℝ) : ℂ) = z*conj z := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]

private theorem summation {T : Type*} [Fintype T] (f : ZMod N → T → T → ℂ) :
    (∑ b, ∑ x, ∑ y, f b x y) = ∑ x, ∑ y, ∑ b, f b x y := by
  rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro x _; rw [Finset.sum_comm]

noncomputable def fourier {T : Type*} [Fintype T] (label : T → ZMod N) (u : T → ℂ) (b : ZMod N) : ℂ :=
  ∑ i, u i * ZMod.stdAddChar (label i * b)

private theorem fourier_square {T : Type*} [Fintype T] (label : T → ZMod N) (u : T → ℂ) :
    ((∑ b : ZMod N, ‖fourier label u b‖^2 : ℝ) : ℂ) =
    (N:ℂ) * ∑ i, ∑ j, if label i = label j then u i * conj (u j) else 0 := by
  classical
  have product_sum (b : ZMod N) : fourier label u b * conj (fourier label u b) =
      ∑ i, ∑ j, (u i*conj (u j)) * ZMod.stdAddChar ((label i-label j)*b) := by
    simp only [fourier, map_sum, map_mul, char_conjugate, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _
    rw [sub_mul, sub_eq_add_neg, AddChar.map_add_eq_mul]; ring
  simp only [Complex.ofReal_sum, norm_sq_complex, product_sum]
  rw [summation]; simp only [← Finset.mul_sum, orthogonal, sub_eq_zero]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _
  split_ifs <;> ring

private theorem char_sum {I : Type*} (s : Finset I) (u : I → ZMod N) :
    ZMod.stdAddChar (∑ i ∈ s, u i) = ∏ i ∈ s, ZMod.stdAddChar (u i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [AddChar.map_zero_eq_one]
  | insert i s hi ih => simp [hi, AddChar.map_add_eq_mul, ih]

private def labelSum {m : ℕ} (x : Fin m → ZMod N) := ∑ i, x i
private noncomputable def tupleProd {I : Type*} {m : ℕ} (f : I → ℂ) (x : Fin m → I) := ∏ i, f (x i)

private theorem fourier_power (f : ZMod N → ℂ) (b : ZMod N) (m : ℕ) :
    (fourier id f b)^m = fourier (labelSum (N:=N) (m:=m)) (tupleProd f) b := by
  classical
  simp only [fourier, Fintype.sum_pow, Finset.prod_mul_distrib, id_eq, tupleProd, labelSum,
    Finset.sum_mul, char_sum]

private theorem fourier_real_square {T : Type*} [Fintype T] (label : T → ZMod N) (u : T → ℂ) :
    (∑ b : ZMod N, ‖fourier label u b‖^2) =
    (N:ℝ) * ∑ i, ∑ j, if label i=label j then (u i*conj (u j)).re else 0 := by
  classical
  have h := congrArg Complex.re (fourier_square label u)
  simp only [Complex.ofReal_re, Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
    zero_mul, sub_zero, Complex.re_sum, apply_ite Complex.re, Complex.zero_re] at h
  exact h

/-- Sum of even powers of the unnormalized Fourier transform. -/
noncomputable def moment (m : ℕ) (f : ZMod N → ℂ) : ℝ := ∑ b, ‖fourier id f b‖^(2*m)

private theorem moment_tuple (m : ℕ) (f : ZMod N → ℂ) :
    moment m f = ∑ b, ‖fourier (labelSum (N:=N) (m:=m)) (tupleProd f) b‖^2 := by
  unfold moment; apply Finset.sum_congr rfl; intro b _
  rw [← fourier_power, norm_pow, ← pow_mul, Nat.mul_comm]

private theorem parseval (f : ZMod N → ℂ) :
    (∑ b, ‖fourier id f b‖^2) = (N:ℝ) * ∑ x, ‖f x‖^2 := by
  rw [fourier_real_square]
  simp only [id_eq, Fintype.sum_ite_eq, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
private theorem commute_real {P T : Type*} [Fintype P] [Fintype T] (f : P → T → T → ℝ) :
    (∑ p, ∑ x, ∑ y, f p x y) = ∑ x, ∑ y, ∑ p, f p x y := by
  rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro x _; rw [Finset.sum_comm]

private theorem kernel_majorant {P T : Type*} [Fintype P] [Fintype T]
    (l : T → ZMod N) (w : T → ℝ) (hw : ∀ x, 0 ≤ w x) (K : P → T → ℂ)
    (hK : ∀ x y, (∑ p, ‖K p x‖ * ‖K p y‖) ≤ (N:ℝ)) :
    (∑ p, ∑ b, ‖fourier l (fun x => (w x:ℂ)*K p x) b‖^2) ≤
      (N:ℝ) * ∑ b, ‖fourier l (fun x => (w x:ℂ)) b‖^2 := by
  classical
  have hpoint (p : P) (x y : T) :
      ((w x*K p x)*conj (w y*K p y)).re ≤ (w x*w y)*(‖K p x‖*‖K p y‖) := by
    refine (Complex.re_le_norm _).trans_eq ?_
    simp only [norm_mul, norm_conj, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw x),
      abs_of_nonneg (hw y)]; ring
  simp_rw [fourier_real_square]
  rw [← Finset.mul_sum, commute_real]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg N)
  rw [Finset.mul_sum]; apply Finset.sum_le_sum; intro x _
  rw [Finset.mul_sum]; apply Finset.sum_le_sum; intro y _
  by_cases h : l x = l y
  · simp only [h, if_true, Complex.conj_ofReal, ← Complex.ofReal_mul, Complex.ofReal_re]
    calc
      _ ≤ ∑ p, (w x*w y)*(‖K p x‖*‖K p y‖) := Finset.sum_le_sum (fun p _ => hpoint p x y)
      _ = (w x*w y)*∑ p, ‖K p x‖*‖K p y‖ := (Finset.mul_sum ..).symm
      _ ≤ (w x*w y)*N := mul_le_mul_of_nonneg_left (hK x y) (mul_nonneg (hw x) (hw y))
      _ = _ := mul_comm _ _
  · simp [h]
private theorem pair_bound {P : Type*} [Fintype P] (a b : P → ℝ) (D : ℝ)
    (ha : ∑ p, a p^2 ≤ D) (hb : ∑ p, b p^2 ≤ D) : ∑ p, a p*b p ≤ D := by
  have h := Finset.sum_le_sum (s:=Finset.univ) (fun p _ => show 2*(a p*b p) ≤ a p^2+b p^2 by
    nlinarith [sq_nonneg (a p-b p)])
  rw [← Finset.mul_sum, Finset.sum_add_distrib] at h; linarith

private theorem tuple_bound {I : Type*} (k : ℕ) (f : I → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1)
    (x : Fin (k+1) → I) : ‖tupleProd f x‖ ≤ ‖f (x 0)‖ := by
  rw [tupleProd, norm_prod, Fin.prod_univ_succ]
  exact mul_le_of_le_one_right (norm_nonneg _) (Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun i _ => hf _))

/-- Vector-valued even Fourier majorant for a contractive tight matrix frame. -/
theorem even_fourier_majorant {P : Type*} [Fintype P] (k : ℕ) (w : ZMod N → ℝ) (hw : ∀ x, 0≤w x)
    (K : P → ZMod N → ℂ) (hunit : ∀ p x, ‖K p x‖≤1) (hmass : ∀ x, ∑ p, ‖K p x‖^2 ≤ (N:ℝ)) :
    ∑ p, moment (k+1) (fun x => (w x:ℂ)*K p x) ≤ (N:ℝ)*moment (k+1) (fun x => (w x:ℂ)) := by
  let T := Fin (k+1) → ZMod N
  have hK (x y : T) : ∑ p, ‖tupleProd (K p) x‖*‖tupleProd (K p) y‖ ≤ (N:ℝ) := by
    refine (Finset.sum_le_sum (fun p _ => mul_le_mul (tuple_bound k (K p) (hunit p) x)
      (tuple_bound k (K p) (hunit p) y) (norm_nonneg _) (norm_nonneg _))).trans ?_
    exact pair_bound _ _ _ (hmass (x 0)) (hmass (y 0))
  have h := kernel_majorant (labelSum (N:=N) (m:=k+1)) (fun x => ∏ i, w (x i))
    (fun x => Finset.prod_nonneg (fun i _ => hw _)) (fun p x => tupleProd (K p) x) hK
  have hprod (p : P) : tupleProd (m:=k+1) (fun j => (w j:ℂ)*K p j) =
      (fun x => ((∏ i, w (x i) : ℝ):ℂ)*tupleProd (K p) x) := by
    funext x; simp only [tupleProd, Finset.prod_mul_distrib, Complex.ofReal_prod]
  have hwprod : tupleProd (m:=k+1) (fun j => (w j:ℂ)) = (fun x => ((∏ i, w (x i) : ℝ):ℂ)) := by
    funext x; simp only [tupleProd, Complex.ofReal_prod]
  simpa only [moment_tuple, hprod, hwprod] using h
/-- Matrix element of the shift-and-phase Weyl operator between two columns. -/
noncomputable def weyl (u v : ZMod N → ℂ) (p : ZMod N × ZMod N) : ℂ :=
  fourier id (fun j => conj (u (j+p.1)) * v j) p.2

private theorem shift_norm (u : ZMod N → ℂ) (a : ZMod N) :
    (∑ j, ‖u (j+a)‖^2) = ∑ j, ‖u j‖^2 :=
  Fintype.sum_equiv (Equiv.addRight a) _ _ (fun _ => rfl)

private theorem weyl_bounded (u v : ZMod N → ℂ) (hu : ∑ j, ‖u j‖^2=1) (hv : ∑ j, ‖v j‖^2=1)
    (p : ZMod N × ZMod N) : ‖weyl u v p‖ ≤ 1 := by
  unfold weyl fourier
  refine (norm_sum_le _ _).trans ?_
  simp only [norm_mul, norm_conj, ZMod.stdAddChar_apply, Circle.norm_coe, mul_one]
  exact pair_bound _ _ 1 (le_of_eq ((shift_norm u p.1).trans hu)) hv.le

private theorem weyl_tight (u v : ZMod N → ℂ) (hu : ∑ j, ‖u j‖^2=1) (hv : ∑ j, ‖v j‖^2=1) :
    (∑ p : ZMod N × ZMod N, ‖weyl u v p‖^2) = N := by
  rw [Fintype.sum_prod_type]; simp only [weyl, parseval, norm_mul, norm_conj, mul_pow]
  rw [← Finset.mul_sum, Finset.sum_comm]
  have hx (j : ZMod N) : (∑ a, ‖u (j+a)‖^2*‖v j‖^2) = ‖v j‖^2 := by
    rw [← Finset.sum_mul]; simp_rw [add_comm j]; rw [shift_norm,hu,one_mul]
  simp only [hx, hv, mul_one]

/-- Fourth and higher even Weyl moments after allowing a general basis on side A. -/
noncomputable def oneSideMoment (m : ℕ) (z : ZMod N → ℝ) (u : ZMod N → ZMod N → ℂ) : ℝ :=
  ∑ h, ∑ p : ZMod N × ZMod N,
    moment m (fun j => ((z j*z (j+h):ℝ):ℂ)*weyl (u (j+h)) (u j) p)

private theorem unilateral_le (k : ℕ) (z : ZMod N → ℝ) (hz : ∀ j, 0≤z j)
    (u : ZMod N → ZMod N → ℂ) (hu : ∀ j, ∑ a, ‖u j a‖^2=1) :
    oneSideMoment (k+1) z u ≤ (N:ℝ)*∑ h, moment (k+1) (fun j => ((z j*z (j+h):ℝ):ℂ)) := by
  unfold oneSideMoment; rw [Finset.mul_sum]; apply Finset.sum_le_sum; intro h _
  exact even_fourier_majorant k _ (fun j => mul_nonneg (hz j) (hz (j+h))) _
    (fun p j => weyl_bounded _ _ (hu (j+h)) (hu j) p) (fun j => (weyl_tight _ _ (hu (j+h)) (hu j)).le)
/-- Computational unit vector with label `x`. -/
noncomputable def coordinate (x j : ZMod N) : ℂ := if x=j then 1 else 0

private theorem weyl_coordinate (y x : ZMod N) (p : ZMod N × ZMod N) :
    weyl (coordinate y) (coordinate x) p = if y=x+p.1 then ZMod.stdAddChar (x*p.2) else 0 := by
  unfold weyl fourier; rw [Finset.sum_eq_single x]
  · by_cases h : y=x+p.1 <;> simp [coordinate, h]
  · intro j _ h; simp [coordinate, Ne.symm h]
  · simp

private theorem modulated_moment (m : ℕ) (f : ZMod N → ℂ) (b : ZMod N) :
    moment m (fun j => f j * ZMod.stdAddChar (j*b)) = moment m f := by
  have he (d : ZMod N) : fourier id (fun j => f j * ZMod.stdAddChar (j*b)) d = fourier id f (b+d) := by
    simp only [fourier, id_eq, mul_add, AddChar.map_add_eq_mul, mul_assoc]
  unfold moment; simp only [he]
  exact Fintype.sum_equiv (Equiv.addLeft b) _ _ (fun _ => rfl)

private theorem coordinate_attains (k : ℕ) (z : ZMod N → ℝ) :
    oneSideMoment (k+1) z coordinate = (N:ℝ)*∑ h, moment (k+1) (fun j => ((z j*z (j+h):ℝ):ℂ)) := by
  unfold oneSideMoment; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro h _
  rw [Fintype.sum_prod_type, Finset.sum_eq_single h]
  · simp only [weyl_coordinate, if_true, modulated_moment, Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
  · intro a _ ha
    have hh (j : ZMod N) : j+h ≠ j+a := fun h' => ha (add_left_cancel h').symm
    have hpow : (2*(k+1))≠0 := by omega
    simp [weyl_coordinate, hh, moment, fourier, zero_pow hpow]
  · simp

/-- Pure-state computational amplitudes, with side B in its labeled Schmidt basis. -/
noncomputable def state (z : ZMod N → ℝ) (u : ZMod N → ZMod N → ℂ) (i j : ZMod N) := (z j:ℂ)*u j i

/-- Expectation of the bipartite tensor Weyl with local shift/phase labels. -/
noncomputable def correlation (v : ZMod N → ZMod N → ℂ) (a b h d : ZMod N) : ℂ :=
  ∑ i, ∑ j, conj (v (i+a) (j+h)) * v i j * ZMod.stdAddChar (i*b+j*d)

/-- Unnormalized 2m-th moment of all bipartite cyclic Weyl expectations. -/
noncomputable def bipartiteMoment (m : ℕ) (v : ZMod N → ZMod N → ℂ) : ℝ :=
  ∑ h, ∑ p : ZMod N × ZMod N, ∑ d, ‖correlation v p.1 p.2 h d‖^(2*m)

private theorem correlation_state (z : ZMod N → ℝ) (u : ZMod N → ZMod N → ℂ)
    (p : ZMod N × ZMod N) (h d : ZMod N) :
    correlation (state z u) p.1 p.2 h d =
      fourier id (fun j => ((z j*z (j+h):ℝ):ℂ)*weyl (u (j+h)) (u j) p) d := by
  unfold correlation; rw [Finset.sum_comm]
  simp only [state, weyl, fourier, id_eq, map_mul, Complex.conj_ofReal, Complex.ofReal_mul,
    AddChar.map_add_eq_mul, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl; intro j _; apply Finset.sum_congr rfl; intro i _; ring

private theorem physical_eq (m : ℕ) (z : ZMod N → ℝ) (u : ZMod N → ZMod N → ℂ) :
    bipartiteMoment m (state z u) = oneSideMoment m z u := by
  simp only [bipartiteMoment, oneSideMoment, moment, correlation_state]

/-- For every cyclic local dimension, fixing one Schmidt basis in the
computational coordinates makes the aligned choice on the other side optimal
at every positive integer moment order. Each moving column may in fact be an
arbitrary unit vector; orthogonality is unnecessary for this inequality. -/
theorem unilateral_optimality (k : ℕ) (z : ZMod N → ℝ) (hz : ∀ j, 0≤z j)
    (u : ZMod N → ZMod N → ℂ) (hu : ∀ j, ∑ a, ‖u j a‖^2=1) :
    bipartiteMoment (k+1) (state z u) ≤ bipartiteMoment (k+1) (state z coordinate) := by
  rw [physical_eq, physical_eq, coordinate_attains]
  exact unilateral_le k z hz u hu

#print axioms even_fourier_majorant
#print axioms unilateral_optimality
private theorem conj_mul_norm (t : ℂ) : conj t*t=((‖t‖^2:ℝ):ℂ) := by
  rw [mul_comm, ← norm_sq_complex]

private theorem identity_weyl (u : ZMod N → ℂ) (hu : ∑ j, ‖u j‖^2=1) : weyl u u (0,0)=1 := by
  simp only [weyl, fourier, id_eq, add_zero, mul_zero, AddChar.map_zero_eq_one, mul_one,
    conj_mul_norm, ← Complex.ofReal_sum, hu, Complex.ofReal_one]

private theorem identity_correlation (z : ZMod N → ℝ) (u : ZMod N → ZMod N → ℂ)
    (hn : ∑ j, z j^2=1) (hu : ∀ j, ∑ a, ‖u j a‖^2=1) : correlation (state z u) 0 0 0 0=1 := by
  rw [correlation_state z u (0,0) 0 0]
  simp only [fourier, id_eq, add_zero, identity_weyl _ (hu _), mul_zero,
    AddChar.map_zero_eq_one, mul_one, ←sq, ← Complex.ofReal_sum, hn, Complex.ofReal_one]

private theorem identity_le_moment (m : ℕ) (z : ZMod N → ℝ) (u : ZMod N → ZMod N → ℂ)
    (hn : ∑ j, z j^2=1) (hu : ∀ j, ∑ a, ‖u j a‖^2=1) : 1≤ bipartiteMoment m (state z u) := by
  let P := ZMod N × ZMod N
  let f := fun (h : ZMod N) (p : P) (d : ZMod N) => ‖correlation (state z u) p.1 p.2 h d‖^(2*m)
  have hf (h : ZMod N) (p : P) (d : ZMod N) : 0≤f h p d := pow_nonneg (norm_nonneg _) _
  have h0 : f 0 (0,0) 0=1 := by simp [f, identity_correlation z u hn hu]
  rw [← h0]; change f 0 (0,0) 0 ≤ ∑ h, ∑ p, ∑ d, f h p d
  calc
    _ ≤ ∑ d, f 0 (0,0) d := Finset.single_le_sum (fun d _ => hf 0 (0,0) d) (Finset.mem_univ 0)
    _ ≤ ∑ p, ∑ d, f 0 p d := Finset.single_le_sum (fun p _ => Finset.sum_nonneg (fun d _ => hf 0 p d)) (Finset.mem_univ (0,0))
    _ ≤ _ := Finset.single_le_sum (fun h _ => Finset.sum_nonneg (fun p _ => Finset.sum_nonneg (fun d _ => hf h p d))) (Finset.mem_univ 0)

private theorem unitary_column_mass (U : Matrix.unitaryGroup (ZMod N) ℂ) (j : ZMod N) :
    ∑ i, ‖U i j‖^2 = 1 := by
  have h := congrArg (fun A : Matrix (ZMod N) (ZMod N) ℂ => A j j) (Matrix.mem_unitaryGroup_iff'.mp U.2)
  dsimp only at h
  rw [Matrix.mul_apply, Matrix.one_apply_eq] at h
  simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply] at h
  change (∑ i, conj (U i j)*U i j) = (1:ℂ) at h
  simp only [conj_mul_norm, ← Complex.ofReal_sum] at h
  exact_mod_cast h

/-- Stabilizer Rényi entropy of a normalized two-qudit state, with natural logarithms. -/
noncomputable def renyi (m : ℕ) (v : ZMod N → ZMod N → ℂ) : ℝ :=
  -Real.log (bipartiteMoment m v / (N:ℝ)^2) / ((m:ℝ)-1)

/-- The computationally aligned reference minimizes every integer stabilizer
Rényi entropy of order at least two over the full one-sided unitary orbit. -/
theorem one_sided_unitary_renyi (k : ℕ) (z : ZMod N → ℝ) (hz : ∀ j, 0≤z j)
    (hn : ∑ j, z j^2=1) (U : Matrix.unitaryGroup (ZMod N) ℂ) :
    renyi (k+2) (state z coordinate) ≤ renyi (k+2) (state z (fun j i => U i j)) := by
  let u := fun j i => U i j
  have hu (j) := unitary_column_mass U j
  have h := unilateral_optimality (k+1) z hz u hu
  have hm := identity_le_moment (k+2) z u hn hu
  have hnpos : (0:ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hq := div_le_div_of_nonneg_right h (sq_nonneg (N:ℝ))
  have hp : 0 < bipartiteMoment (k+2) (state z u) / (N:ℝ)^2 := div_pos (by linarith) (sq_pos_of_pos hnpos)
  have hlog := Real.log_le_log hp hq
  unfold renyi
  exact div_le_div_of_nonneg_right (neg_le_neg hlog) (by push_cast; linarith [Nat.cast_nonneg (α:=ℝ) k])

#print axioms one_sided_unitary_renyi

end OneSidedSchmidt

import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! One-step, vertex-only, check-later rendezvous on a labelled cycle. -/

namespace CycleRendezvous
open Finset Complex
open scoped InnerProductSpace ComplexConjugate
noncomputable section

variable {N : ℕ} [NeZero N]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

private lemma char_conj (j : ZMod N) :
    conj (ZMod.stdAddChar j) = ZMod.stdAddChar (-j) := by
  rw [ZMod.stdAddChar_apply,ZMod.stdAddChar_apply,AddChar.map_neg_eq_inv,Circle.coe_inv_eq_conj]

private lemma fourier_duality (f g : ZMod N → E) :
    ∑ k, ⟪ZMod.dft f k,g k⟫_ℂ = ∑ j, ⟪f j,ZMod.dft g (-j)⟫_ℂ := by
  simp only [ZMod.dft_apply,sum_inner,inner_sum,inner_smul_left,inner_smul_right,char_conj,
    neg_neg,mul_neg]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  rw [mul_comm j k]

private lemma parseval (f : ZMod N → E) :
    ∑ k, ‖ZMod.dft f k‖^2 = (N:ℝ)*∑ j, ‖f j‖^2 := by
  have h := fourier_duality f (ZMod.dft f)
  simp only [ZMod.dft_dft,neg_neg,inner_smul_right,inner_self_eq_norm_sq_to_K,
    ← Finset.mul_sum] at h
  apply Complex.ofReal_injective
  push_cast
  exact h

private lemma fourier_shift (f : ZMod N → E) (k s : ZMod N) :
    ZMod.dft (fun j => f (j+s)) k = ZMod.stdAddChar (s*k) • ZMod.dft f k := by
  simp only [ZMod.dft_apply,Finset.smul_sum,smul_smul,← AddChar.map_add_eq_mul]
  apply Fintype.sum_equiv (Equiv.addRight s)
  intro j
  simp only [Equiv.coe_addRight]
  congr 2
  ring

private def diff (f : ZMod N → E) (s : ZMod N) (j : ZMod N) := f j - f (j+s)

private lemma fourier_diff (f : ZMod N → E) (s k : ZMod N) :
    ZMod.dft (diff f s) k = (1-ZMod.stdAddChar (s*k)) • ZMod.dft f k := by
  change ZMod.dft (f-(fun j => f (j+s))) k = _
  rw [map_sub,Pi.sub_apply,fourier_shift,sub_smul,one_smul]

/-- The sharp squared norm of a cyclic difference is its largest Fourier multiplier. -/
theorem difference_energy (f : ZMod N → E) (s : ZMod N) (B : ℝ)
    (hB : ∀ k, ‖1-ZMod.stdAddChar (s*k)‖^2 ≤ B) :
    ∑ j, ‖diff f s j‖^2 ≤ B*∑ j, ‖f j‖^2 := by
  have ht (k : ZMod N) : ‖ZMod.dft (diff f s) k‖^2 ≤ B*‖ZMod.dft f k‖^2 := by
    rw [fourier_diff,norm_smul,mul_pow]
    exact mul_le_mul_of_nonneg_right (hB k) (sq_nonneg _)
  have total := Finset.sum_le_sum (s:=univ) fun k _ => ht k
  rw [parseval,← Finset.mul_sum,parseval,mul_left_comm] at total
  exact (mul_le_mul_iff_right₀ (show (0:ℝ)<N by exact_mod_cast NeZero.pos N)).mp total

private lemma sum_shift {T : Type*} [AddCommMonoid T] (f : ZMod N → T) (s : ZMod N) :
    (∑ j, f (j+s)) = ∑ j, f j :=
  Fintype.sum_equiv (Equiv.addRight s) _ _ fun _ => rfl

def sign (a : Bool) : ℝ := if a then 1 else -1

/-- Sum the four ways of reaching each destination, divided by the number of
ordered pairs of independent uniform starting positions. True means clockwise. -/
def meeting (p : ZMod N → ZMod N → Bool → Bool → ℝ) : ℝ :=
  (∑ y, (p (y-1) (y-1) true true + p (y-1) (y+1) true false +
    p (y+1) (y-1) false true + p (y+1) (y+1) false false)) / (N:ℝ)^2

def displacement (i : Bool) : ZMod N := if i then 1 else -1

/-- The direct enumeration of independent starting sites and observable moves
agrees with the destination form, so diagonal starts and C4 are counted correctly. -/
theorem meeting_from_starts (p : ZMod N → ZMod N → Bool → Bool → ℝ) :
    (∑ i : Bool, ∑ j : Bool, ∑ x : ZMod N, ∑ y : ZMod N,
      if x+displacement i=y+displacement j then p x y i j else 0) / (N:ℝ)^2 = meeting p := by
  have moves (i j : Bool) :
      (∑ x : ZMod N, ∑ y : ZMod N, if x+displacement i=y+displacement j then p x y i j else 0) =
      ∑ z : ZMod N, p (z-displacement i) (z-displacement j) i j := by
    have eq (x y : ZMod N) : x+displacement i=y+displacement j ↔ y=x+displacement i-displacement j := by
      exact ⟨fun h => eq_sub_of_add_eq h.symm,fun h => sub_eq_iff_eq_add.mp h.symm⟩
    simp only [eq,Finset.sum_ite_eq',Finset.mem_univ,if_true]
    apply Fintype.sum_equiv (Equiv.addRight (displacement i))
    intro x
    change p x (x+displacement i-displacement j) i j =
      p (x+displacement i-displacement i) (x+displacement i-displacement j) i j
    rw [show x+displacement i-displacement i=x by ring]
  simp only [moves]
  simp [displacement,meeting,Finset.sum_add_distrib]
  ring

/-- Binary joint law in terms of its two marginal expectations and correlator. -/
def binaryLaw (a b : ZMod N → ℝ) (c : ZMod N → ZMod N → ℝ)
    (x y : ZMod N) (i j : Bool) : ℝ :=
  (1+sign i*a x+sign j*b y+sign i*sign j*c x y)/4

def correlator (u v : ZMod N → E) (x y : ZMod N) := (⟪u x,v y⟫_ℂ).re

/-- The game forgets the one-party marginal biases. Its bilinear form is the
step-two cycle Laplacian, including the two routes to the opposite site on C4. -/
theorem meeting_identity (a b : ZMod N → ℝ) (u v : ZMod N → E) :
    meeting (binaryLaw a b (correlator u v)) =
      ((N:ℝ)+(∑ j, (⟪diff u 2 j,diff v 2 j⟫_ℂ).re)/4)/(N:ℝ)^2 := by
  let h := fun j => (⟪diff u 2 j,diff v 2 j⟫_ℂ).re
  let p := binaryLaw a b (correlator u v)
  have one (y : ZMod N) : p (y-1) (y-1) true true + p (y-1) (y+1) true false +
      p (y+1) (y-1) false true + p (y+1) (y+1) false false =
      1+(a (y-1)-a (y+1))/2+(b (y-1)-b (y+1))/2+h (y-1)/4 := by
    dsimp [p,binaryLaw,sign,correlator,h,diff]
    rw [show y-1+2=y+1 by ring]
    simp only [inner_sub_left,inner_sub_right,Complex.sub_re]
    ring
  change (∑ y, (_ : ℝ)) / (N:ℝ)^2 = ((N:ℝ)+(∑j, h j)/4)/(N:ℝ)^2
  congr 1
  change (∑ y, (p (y-1) (y-1) true true + p (y-1) (y+1) true false +
    p (y+1) (y-1) false true+p (y+1) (y+1) false false)) = _
  simp only [one]
  simp only [div_eq_mul_inv,Finset.sum_add_distrib,← Finset.sum_mul,
    sub_eq_add_neg,Finset.sum_neg_distrib,sum_shift,Finset.sum_const,Finset.card_univ,ZMod.card,nsmul_eq_mul]
  ring

theorem vector_upper (a b : ZMod N → ℝ) (u v : ZMod N → E)
    (hu : ∀ x, ‖u x‖≤1) (hv : ∀ x, ‖v x‖≤1) (B : ℝ)
    (hb : ∀ k : ZMod N, ‖1-ZMod.stdAddChar (2*k)‖^2 ≤ B) :
    meeting (binaryLaw a b (correlator u v)) ≤ (1+B/4)/(N:ℝ) := by
  have un (f : ZMod N → E) (hf : ∀ x, ‖f x‖≤1) : (∑ x, ‖f x‖^2) ≤ (N:ℝ) := by
    have pt (x : ZMod N) : ‖f x‖^2 ≤ 1 := by
      simpa using (sq_le_sq₀ (norm_nonneg (f x)) (by norm_num : (0:ℝ)≤1)).2 (hf x)
    simpa using Finset.sum_le_sum (s:=univ) fun x _ => pt x
  have hB : 0 ≤ B := (sq_nonneg _).trans (hb 0)
  have en (f : ZMod N → E) (hf : ∀ x, ‖f x‖≤1) :
      (∑ x, ‖diff f 2 x‖^2) ≤ B*(N:ℝ) :=
    (difference_energy f 2 B hb).trans (mul_le_mul_of_nonneg_left (un f hf) hB)
  have pt (x : ZMod N) : 2*(⟪diff u 2 x,diff v 2 x⟫_ℂ).re ≤
      ‖diff u 2 x‖^2+‖diff v 2 x‖^2 := by
    have hs := norm_sub_sq (𝕜:=ℂ) (diff u 2 x) (diff v 2 x)
    change _ = _ - 2*(⟪diff u 2 x,diff v 2 x⟫_ℂ).re + _ at hs
    linarith [sq_nonneg ‖diff u 2 x-diff v 2 x‖]
  have hsum := Finset.sum_le_sum (s:=univ) fun x _ => pt x
  rw [← Finset.mul_sum,Finset.sum_add_distrib] at hsum
  rw [meeting_identity]
  have hn : 0 < (N:ℝ) := by exact_mod_cast NeZero.pos N
  apply (div_le_div_iff₀ (sq_pos_of_pos hn) hn).mpr
  have h := mul_le_mul_of_nonneg_right (by linarith [en u hu,en v hv] :
    (∑ x, (⟪diff u 2 x,diff v 2 x⟫_ℂ).re) ≤ B*(N:ℝ)) hn.le
  nlinarith

/-- The loss in the optimum number of classical meetings relative to 2N. -/
def defect (N : ℕ) : ℕ := if N%4=0 then 0 else if N%4=2 then 2 else 1

private lemma char_norm (j : ZMod N) : ‖ZMod.stdAddChar j‖ = 1 := by
  simp [ZMod.stdAddChar_apply]

private lemma char_real (j : ZMod N) : (ZMod.stdAddChar j).re = Real.cos (2*Real.pi*j.val/N) := by
  rw [ZMod.stdAddChar_apply,ZMod.toCircle_eq_circleExp,Circle.coe_exp,Complex.exp_ofReal_mul_I_re]
  congr 1
  ring

private lemma char_multiplier (j : ZMod N) :
    ‖1-ZMod.stdAddChar j‖^2 = 2+2*Real.cos (Real.pi*|(N:ℝ)-2*j.val|/N) := by
  have hn : (N:ℝ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have hh : Real.cos (Real.pi*|(N:ℝ)-2*j.val|/N) =
      -Real.cos (2*Real.pi*j.val/N) := by
    by_cases h : 0≤(N:ℝ)-2*j.val
    · rw [abs_of_nonneg h,show Real.pi*((N:ℝ)-2*j.val)/N =
         Real.pi-(2*Real.pi*j.val/N) by field_simp,Real.cos_pi_sub]
    · rw [abs_of_neg (lt_of_not_ge h),show Real.pi*(-((N:ℝ)-2*j.val))/N =
         2*Real.pi*j.val/N-Real.pi by field_simp; ring,Real.cos_sub_pi]
  rw [norm_sub_sq (𝕜:=ℂ),char_norm,hh]
  simp [RCLike.inner_apply,char_real]
  ring

private lemma gap_lower (hN : 3≤N) (k : ZMod N) :
    (defect N:ℝ) ≤ |(N:ℝ)-2*(2*k).val| := by
  have evenPos (h2 : N%2=0) : (2*k).val%2=0 := by
    have htwo : (2 : ZMod N).val=2 := ZMod.val_natCast_of_lt (by omega : 2<N)
    rw [ZMod.val_mul,htwo,Nat.mod_mod_of_dvd _ (Nat.dvd_of_mod_eq_zero h2)]
    omega
  have h : (defect N:ℤ) ≤ |(N:ℤ)-2*(2*k).val| := by
    unfold defect
    split_ifs with h0 h2
    · simp
    · have hh := evenPos (by omega)
      by_cases hs : (0:ℤ) ≤ N-2*((2*k).val:ℤ)
      · rw [abs_of_nonneg hs]; omega
      · rw [abs_of_neg (lt_of_not_ge hs)]; omega
    · by_cases hs : (0:ℤ) ≤ N-2*((2*k).val:ℤ)
      · rw [abs_of_nonneg hs]; omega
      · rw [abs_of_neg (lt_of_not_ge hs)]; omega
  exact_mod_cast h

private def peak (N : ℕ) : ℕ := (N+2)/4

omit [NeZero N] in
private lemma gap_peak (hN : 3≤N) :
    |(N:ℝ)-2*(2*(peak N:ZMod N)).val| = defect N := by
  have hj : 2*peak N<N := by unfold peak; omega
  have hz : (2*(peak N:ZMod N)).val = 2*peak N := by
    rw [show (2:ZMod N)*(peak N:ZMod N) = ((2*peak N:ℕ):ZMod N) by push_cast; rfl]
    exact ZMod.val_natCast_of_lt hj
  rw [hz]
  have h : |(N:ℤ)-2*((2*peak N:ℕ):ℤ)| = defect N := by
    unfold defect peak
    split_ifs <;> push_cast <;> rw [abs_eq_max_neg] <;> omega
  exact_mod_cast h

def spectralBound (N : ℕ) : ℝ := 2+2*Real.cos (Real.pi*defect N/N)

private lemma multiplier_bound (hN : 3≤N) (k : ZMod N) :
    ‖1-ZMod.stdAddChar (2*k)‖^2 ≤ spectralBound N := by
  rw [char_multiplier]
  have hn : 0 < (N:ℝ) := by exact_mod_cast NeZero.pos N
  have h0 : (0:ℝ) ≤ Real.pi*defect N/N := by positivity
  have hj : ((2*k).val:ℝ)≤N := by exact_mod_cast (ZMod.val_lt (2*k)).le
  have hd : |(N:ℝ)-2*(2*k).val|≤N := by
    exact abs_le.mpr ⟨by linarith,by linarith [Nat.cast_nonneg (α:=ℝ) (2*k).val]⟩
  have hu : Real.pi*|(N:ℝ)-2*(2*k).val|/N ≤ Real.pi := by
    apply (div_le_iff₀ hn).mpr
    exact mul_le_mul_of_nonneg_left hd Real.pi_pos.le
  have hl := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (gap_lower hN k) Real.pi_pos.le) hn.le
  unfold spectralBound
  linarith [Real.cos_le_cos_of_nonneg_of_le_pi h0 hu hl]

private lemma multiplier_peak (hN : 3≤N) :
    ‖1-ZMod.stdAddChar (2*(peak N:ZMod N))‖^2 = spectralBound N := by
  rw [char_multiplier,gap_peak hN,spectralBound]

/-- The usual Born expression for binary local observables, written as
Re ⟨ψ,(I+σA)(I+τB)ψ⟩/4. For commuting self-adjoint contractions the two
effects are the outcomes of arbitrary binary POVMs on the two parties. -/
def operatorLaw (ψ : E) (A B : ZMod N → E →ₗ[ℂ] E)
    (x y : ZMod N) (i j : Bool) : ℝ :=
  let w := ψ + (sign j:ℂ) • B y ψ
  (⟪ψ,w+(sign i:ℂ) • A x w⟫_ℂ).re / 4

/-- The all-size upper bound applies to arbitrary local observables. Only
Alice's symmetry and the norms on the state are needed for the estimate. -/
theorem quantum_upper (hN : 3≤N) (ψ : E) (hn : ‖ψ‖=1)
    (A B : ZMod N → E →ₗ[ℂ] E)
    (ha : ∀ x v w, ⟪A x v,w⟫_ℂ = ⟪v,A x w⟫_ℂ)
    (hu : ∀ x, ‖A x ψ‖≤1) (hv : ∀ x, ‖B x ψ‖≤1) :
    meeting (operatorLaw ψ A B) ≤ (1+spectralBound N/4)/(N:ℝ) := by
  have self : (⟪ψ,ψ⟫_ℂ).re=1 := by
    change RCLike.re (⟪ψ,ψ⟫_ℂ)=1
    rw [← norm_sq_eq_re_inner,hn]
    norm_num
  let l := fun x => (⟪A x ψ,ψ⟫_ℂ).re
  let r := fun y => (⟪ψ,B y ψ⟫_ℂ).re
  have law : operatorLaw ψ A B = binaryLaw l r (correlator (fun x => A x ψ) (fun x => B x ψ)) := by
    funext x y i j
    cases i <;> cases j <;>
      simp [operatorLaw,binaryLaw,correlator,sign,l,r,inner_add_right,inner_neg_right,
        ← ha,self,Complex.add_re] <;> ring
  rw [law]
  exact vector_upper l r _ _ hu hv _ (multiplier_bound hN)

private def phase (k j : ZMod N) : ℂ := ZMod.stdAddChar (j*k)

private lemma phase_difference (k j : ZMod N) :
    ‖diff (phase k) 2 j‖^2 = ‖1-ZMod.stdAddChar (2*k)‖^2 := by
  have eq : diff (phase k) 2 j = ZMod.stdAddChar (j*k)*(1-ZMod.stdAddChar (2*k)) := by
    simp [diff,phase,add_mul,AddChar.map_add_eq_mul,mul_sub]
  rw [eq,norm_mul,char_norm,one_mul]

/-- Born probability for equatorial measurements of a Bell pair. In the
computational basis the two nonzero Bell amplitudes give (1+στ z̄ w)/(2√2). -/
def bellLaw (z : ZMod N → ℂ) (x y : ZMod N) (i j : Bool) : ℝ :=
  ‖(1+(sign i:ℂ)*(sign j:ℂ)*(conj (z x)*z y)) / (2*(Real.sqrt 2:ℂ))‖^2

omit [NeZero N] in
private lemma bell_identity (z : ZMod N → ℂ) (hz : ∀ x, ‖z x‖=1) :
    bellLaw z = binaryLaw (fun _=>0) (fun _=>0) (correlator z z) := by
  have den : ‖(2:ℂ)*(Real.sqrt 2:ℂ)‖^2 = 8 := by
    rw [norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _),Real.sq_sqrt (by norm_num)]
    norm_num
  funext x y i j
  let w := (sign i:ℂ)*(sign j:ℂ)*(conj (z x)*z y)
  have hw : ‖w‖=1 := by cases i <;> cases j <;> simp [w,sign,hz]
  have wr : w.re = sign i*sign j*(conj (z x)*z y).re := by
    cases i <;> cases j <;> simp [w,sign]
  have hh := norm_add_sq (𝕜:=ℂ) (1:ℂ) w
  simp [hw,RCLike.inner_apply] at hh
  change ‖(1+w)/(2*(Real.sqrt 2:ℂ))‖^2 = _
  rw [norm_div,div_pow,den,hh]
  simp [binaryLaw,correlator,RCLike.inner_apply,wr]
  ring

private def qubitScale : ℝ := (Real.sqrt 2)⁻¹

private lemma scale_sq : (qubitScale:ℂ)^2 = (2:ℂ)⁻¹ := by
  have h : (Real.sqrt 2:ℂ)^2=2 := by exact_mod_cast Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
  simp [qubitScale,inv_pow,h]

/-- Equatorial qubit basis, in the order of the two standard basis states. -/
def qubitKet (z : ℂ) (out bit : Bool) : ℂ :=
  if bit then qubitScale*(sign out:ℂ)*z else qubitScale

theorem qubit_orthonormal (z : ℂ) (hz : ‖z‖=1) (i j : Bool) :
    (∑ t : Bool, conj (qubitKet z i t)*qubitKet z j t) = if i=j then 1 else 0 := by
  have cc : conj z * z = 1 := by simp [Complex.conj_mul',hz]
  have form : (∑ t : Bool, conj (qubitKet z i t)*qubitKet z j t) =
      (qubitScale:ℂ)^2+(sign i:ℂ)*(sign j:ℂ)*((qubitScale:ℂ)^2*(conj z*z)) := by
    cases i <;> cases j <;> simp [qubitKet,sign] <;> ring
  rw [form,cc,scale_sq]
  cases i <;> cases j <;> norm_num [sign]

/-- The Bell-state amplitudes in the standard tensor-product basis. -/
def bellKet (s t : Bool) : ℂ := if s=t then qubitScale else 0

theorem bell_normalized : ∑ s : Bool, ∑ t : Bool, ‖bellKet s t‖^2 = 1 := by
  have h : qubitScale^2 = (2:ℝ)⁻¹ := by
    simp [qubitScale,inv_pow,Real.sq_sqrt (by norm_num : (0:ℝ)≤2)]
  simp [bellKet,Complex.norm_real,Real.norm_eq_abs,sq_abs,h]
  norm_num

omit [NeZero N] in
/-- The actual two-qubit product projectors on |Φ⁺⟩ give the displayed joint law. -/
theorem bell_from_qubits (z : ZMod N → ℂ) (x y : ZMod N) (i j : Bool) :
    ‖∑ s : Bool, ∑ t : Bool, conj (qubitKet (z x) i s) *
      conj (qubitKet (conj (z y)) j t) * bellKet s t‖^2 = bellLaw z x y i j := by
  have scale : (qubitScale:ℂ)^3 = 1/(2*(Real.sqrt 2:ℂ)) := by
    rw [pow_succ,scale_sq]
    simp [qubitScale,div_eq_mul_inv,mul_comm]
  have amp : (∑ s : Bool, ∑ t : Bool, conj (qubitKet (z x) i s) *
        conj (qubitKet (conj (z y)) j t) * bellKet s t) =
      (qubitScale:ℂ)^3*(1+(sign i:ℂ)*(sign j:ℂ)*(conj (z x)*z y)) := by
    cases i <;> cases j <;> simp [qubitKet,bellKet,sign] <;> ring
  rw [amp,scale,bellLaw]
  congr 2
  ring

/-- The global upper bound is attained by one Bell pair and planar
measurements at the phases of a single Fourier mode. -/
theorem bell_attains (hN : 3≤N) : ∃ z : ZMod N → ℂ, (∀ x, ‖z x‖=1) ∧
    meeting (bellLaw z) = (1+spectralBound N/4)/(N:ℝ) := by
  let k : ZMod N := peak N
  have hz (x : ZMod N) : ‖phase k x‖=1 := char_norm _
  refine ⟨phase k,hz,?_⟩
  rw [bell_identity _ hz,meeting_identity]
  have term (j : ZMod N) :
      (⟪diff (phase k) 2 j,diff (phase k) 2 j⟫_ℂ).re = spectralBound N := by
    change RCLike.re (⟪diff (phase k) 2 j,diff (phase k) 2 j⟫_ℂ) = _
    rw [← norm_sq_eq_re_inner,phase_difference,multiplier_peak hN]
  simp only [term,Finset.sum_const,Finset.card_univ,ZMod.card,nsmul_eq_mul]
  have hn : (N:ℝ) ≠ 0 := by exact_mod_cast NeZero.ne N
  field_simp

/-- Joint probabilities of two deterministic local moves. -/
def classicalLaw (f g : ZMod N → Bool) (x y : ZMod N) (i j : Bool) : ℝ :=
  if f x=i ∧ g y=j then 1 else 0

private def direction (f : ZMod N → Bool) (x : ZMod N) : ℂ := (sign (f x):ℝ)

omit [NeZero N] in
private lemma classical_identity (f g : ZMod N → Bool) :
    classicalLaw f g = binaryLaw (fun x => sign (f x)) (fun y => sign (g y))
      (correlator (direction f) (direction g)) := by
  funext x y i j
  cases h : f x <;> cases h' : g y <;> cases i <;> cases j <;>
    norm_num [classicalLaw,binaryLaw,correlator,direction,sign,h,h',RCLike.inner_apply]

private def changes (f : ZMod N → Bool) : ℕ :=
  ∑ j, if f j=f (j+2) then 0 else 1

private lemma changes_energy (f : ZMod N → Bool) :
    (∑ j, ‖diff (direction f) 2 j‖^2) = 4*(changes f:ℝ) := by
  simp only [changes,Nat.cast_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  cases h : f j <;> cases h' : f (j+2) <;> norm_num [diff,direction,h,h',sign]

private lemma changes_even (f : ZMod N → Bool) : ∃ k, changes f = k+k := by
  let up := fun j => if f j=false ∧ f (j+2)=true then (1:ℕ) else 0
  let down := fun j => if f j=true ∧ f (j+2)=false then (1:ℕ) else 0
  let b := fun j => if f j=true then (1:ℕ) else 0
  have total (j : ZMod N) : (if f j=f (j+2) then (0:ℕ) else 1) = up j+down j := by
    cases h : f j <;> cases h' : f (j+2) <;> simp [h,h',up,down]
  have flow (j : ZMod N) : up j+b j = down j+b (j+2) := by
    cases h : f j <;> cases h' : f (j+2) <;> simp [h,h',up,down,b]
  have mass := Finset.sum_congr (s₁:=univ) rfl (fun j _ => flow j)
  rw [Finset.sum_add_distrib,Finset.sum_add_distrib,sum_shift] at mass
  have eq := Nat.add_right_cancel mass
  exact ⟨∑j,down j,by simp only [changes,total,Finset.sum_add_distrib,eq]⟩

omit [NeZero N] in
private lemma defect_le (hN : 3≤N) : defect N≤N := by unfold defect; split_ifs <;> omega

private lemma spectral_strict (hN : 3≤N) (hd : 0<defect N) : spectralBound N < 4 := by
  have hn : (0:ℝ)<N := by exact_mod_cast NeZero.pos N
  have da : (0:ℝ)<defect N := by exact_mod_cast hd
  have db : (defect N:ℝ)≤N := by exact_mod_cast defect_le hN
  have hu : Real.pi*defect N/N≤Real.pi :=
    (div_le_iff₀ hn).mpr (mul_le_mul_of_nonneg_left db Real.pi_pos.le)
  have hl : 0<Real.pi*defect N/N := by positivity
  have h := Real.cos_lt_cos_of_nonneg_of_le_pi (x:=0) (by norm_num) hu hl
  rw [Real.cos_zero] at h
  unfold spectralBound
  linarith

private lemma changes_bound (f : ZMod N → Bool) (hN : 3≤N) : changes f + defect N ≤ N := by
  have one (j : ZMod N) : (if f j=f (j+2) then (0:ℕ) else 1) ≤ 1 := by split_ifs <;> omega
  have all : changes f ≤ N := by simpa [changes] using Finset.sum_le_sum (s:=univ) fun j _ => one j
  by_cases hd : defect N=0
  · omega
  have hn : (0:ℝ)<N := by exact_mod_cast NeZero.pos N
  have en := difference_energy (direction f) 2 (spectralBound N) (multiplier_bound hN)
  have norm (j : ZMod N) : ‖direction f j‖^2=1 := by cases h : f j <;> norm_num [direction,sign,h]
  simp only [changes_energy,norm,Finset.sum_const,Finset.card_univ,ZMod.card,nsmul_eq_mul,mul_one] at en
  have hh := mul_lt_mul_of_pos_right (spectral_strict hN (Nat.pos_of_ne_zero hd)) hn
  have less : changes f < N := by exact_mod_cast (by linarith : (changes f:ℝ)<N)
  obtain ⟨k,hk⟩ := changes_even f
  unfold defect
  split_ifs <;> omega

/-- Blocks of two equal directions, alternating along the labelled cycle. -/
def blockRule (j : ZMod N) : Bool := decide ((j.val/2)%2=0)

private lemma block_optimal (hN : 3≤N) : changes (blockRule (N:=N)) + defect N = N := by
  let f := blockRule (N:=N)
  let a : ZMod N := (N-2:ℕ)
  let b : ZMod N := (N-1:ℕ)
  let lost := fun x : ZMod N => if f x=f (x+2) then (1:ℕ) else 0
  let flag := fun i : ℕ => if (i/2)%2=0 then (1:ℕ) else 0
  have av : a.val=N-2 := ZMod.val_natCast_of_lt (by omega)
  have bv : b.val=N-1 := ZMod.val_natCast_of_lt (by omega)
  have tv : (2:ZMod N).val=2 := ZMod.val_natCast_of_lt (by omega : 2<N)
  have ab : a≠b := by intro he; have hh := congrArg ZMod.val he; omega
  have pt (x : ZMod N) : lost x =
      (if x=a then flag (N-2) else 0)+(if x=b then flag (N-1) else 0) := by
    by_cases ha : x=a
    · subst x
      have uv : (a+2).val=0 := by rw [ZMod.val_add_of_le (by omega),av,tv]; omega
      simp [lost,f,blockRule,av,uv,ab,flag]
    by_cases hb : x=b
    · subst x
      have uv : (b+2).val=1 := by rw [ZMod.val_add_of_le (by omega),bv,tv]; omega
      simp [lost,f,blockRule,bv,uv,ab.symm,flag]
    have h1 : x.val≠N-2 := fun he => ha (ZMod.val_injective _ (he.trans av.symm))
    have h2 : x.val≠N-1 := fun he => hb (ZMod.val_injective _ (he.trans bv.symm))
    have h3 := ZMod.val_lt x
    have uv : (x+2).val=x.val+2 := by rw [ZMod.val_add_of_lt (by omega),tv]
    by_cases hp : (x.val/2)%2=0
    · simp [lost,f,blockRule,uv,hp,ha,hb]
      omega
    · simp [lost,f,blockRule,uv,hp,ha,hb]
      omega
  have hl : ∑ x, lost x = defect N := by
    simp only [pt,Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.mem_univ,if_true]
    unfold flag defect
    split_ifs <;> omega
  have sumall (x : ZMod N) : (if f x=f (x+2) then (0:ℕ) else 1)+lost x = 1 := by
    by_cases h : f x=f (x+2) <;> simp [lost,h]
  have H := Finset.sum_congr (s₁:=univ) rfl (fun x _ => sumall x)
  simpa only [Finset.sum_add_distrib,hl,Finset.sum_const,Finset.card_univ,ZMod.card,
    nsmul_eq_mul,mul_one,changes,f] using H

private lemma self_meeting (f : ZMod N → Bool) :
    meeting (classicalLaw f f) = ((N:ℝ)+changes f)/(N:ℝ)^2 := by
  rw [classical_identity,meeting_identity]
  have term (x : ZMod N) :
      (⟪diff (direction f) 2 x,diff (direction f) 2 x⟫_ℂ).re = ‖diff (direction f) 2 x‖^2 := by
    exact (norm_sq_eq_re_inner (𝕜:=ℂ) (diff (direction f) 2 x)).symm
  simp only [term,changes_energy]
  ring

/-- Exact classical optimum for independent strategies on every cycle. The
same optimal deterministic responses are available to both parties. -/
theorem classical_optimum (hN : 3≤N) :
    (∀ f g : ZMod N → Bool, meeting (classicalLaw f g) ≤
      (2*(N:ℝ)-defect N)/(N:ℝ)^2) ∧
      meeting (classicalLaw (blockRule (N:=N)) blockRule) = (2*(N:ℝ)-defect N)/(N:ℝ)^2 := by
  constructor
  · intro f g
    rw [classical_identity,meeting_identity]
    apply div_le_div_of_nonneg_right _ (sq_nonneg _)
    have each (j : ZMod N) : 2*(⟪diff (direction f) 2 j,diff (direction g) 2 j⟫_ℂ).re ≤
        ‖diff (direction f) 2 j‖^2+‖diff (direction g) 2 j‖^2 := by
      have hs := norm_sub_sq (𝕜:=ℂ) (diff (direction f) 2 j) (diff (direction g) 2 j)
      change _ = _ - 2*(⟪diff (direction f) 2 j,diff (direction g) 2 j⟫_ℂ).re+_ at hs
      linarith [sq_nonneg ‖diff (direction f) 2 j-diff (direction g) 2 j‖]
    have total := Finset.sum_le_sum (s:=univ) fun j _ => each j
    rw [← Finset.mul_sum,Finset.sum_add_distrib,changes_energy,changes_energy] at total
    have bf : (changes f:ℝ)+defect N ≤ N := by exact_mod_cast changes_bound f hN
    have bg : (changes g:ℝ)+defect N ≤ N := by exact_mod_cast changes_bound g hN
    linarith
  · rw [self_meeting]
    congr 1
    have h : (changes (blockRule (N:=N)):ℝ)+defect N=N := by exact_mod_cast block_optimal hN
    linarith

/-- Finite shared randomness and mixtures of input-independent preparations
preserve any universal bound on the component laws. -/
theorem mixture_bound {L : Type*} [Fintype L] (w : L→ℝ) (hw : ∀ l, 0≤w l)
    (ht : ∑ l, w l=1) (p : L → ZMod N → ZMod N → Bool → Bool → ℝ) (B : ℝ)
    (h : ∀ l, meeting (p l)≤B) :
    meeting (fun x y i j => ∑ l, w l*p l x y i j) ≤ B := by
  have eq : meeting (fun x y i j => ∑ l, w l*p l x y i j) = ∑ l,w l*meeting (p l) := by
    simp only [meeting,← Finset.sum_add_distrib,← mul_add]
    rw [Finset.sum_comm]
    simp only [div_eq_mul_inv,Finset.sum_mul,Finset.mul_sum,mul_assoc]
  rw [eq]
  calc
    _ ≤ ∑l,w l*B := Finset.sum_le_sum fun l _=>mul_le_mul_of_nonneg_left (h l) (hw l)
    _ = B := by rw [← Finset.sum_mul,ht,one_mul]

/-- There is a strict quantum advantage exactly for cycle lengths that are
not divisible by four. -/
theorem advantage_iff (hN : 3≤N) :
    (2*(N:ℝ)-defect N)/(N:ℝ)^2 < (1+spectralBound N/4)/(N:ℝ) ↔ N%4≠0 := by
  have hn : 0<(N:ℝ) := by exact_mod_cast NeZero.pos N
  rw [show (2*(N:ℝ)-defect N)/(N:ℝ)^2 = (2-defect N/(N:ℝ))/(N:ℝ) by
    field_simp,div_lt_div_iff_of_pos_right hn]
  by_cases h : N%4=0
  · norm_num [defect,spectralBound,h]
  · have hd : 0<defect N := by unfold defect; split_ifs <;> omega
    have hsmall : 2*defect N<N := by unfold defect; split_ifs <;> omega
    have h1 : (0:ℝ)<2*(defect N:ℝ)/(N:ℝ) := by positivity
    have h2 : 2*(defect N:ℝ)/(N:ℝ)<1 := by
      rw [div_lt_one hn]
      exact_mod_cast hsmall
    have H := Real.lt_sin_mul (x:=1-2*(defect N:ℝ)/N) (by linarith) (by linarith)
    rw [show Real.pi/2*(1-2*(defect N:ℝ)/N)=Real.pi/2-Real.pi*defect N/N by ring,
      Real.sin_pi_div_two_sub] at H
    constructor
    · exact fun _ => h
    · intro _
      unfold spectralBound
      rw [mul_div_assoc] at H
      linarith

/-- The advantage relative to optimal classical play has an explicit
finite-size bound tending to one. -/
theorem ratio_window (hN : 3≤N) :
    let c := (2*(N:ℝ)-defect N)/(N:ℝ)^2
    let q := (1+spectralBound N/4)/(N:ℝ)
    1≤q/c ∧ q/c≤(N:ℝ)/(N-1) := by
  intro c q
  have hn : (2:ℝ)<N := by exact_mod_cast hN
  have dh : defect N≤2 := by unfold defect; split_ifs <;> omega
  have hd : (defect N:ℝ)≤2 := by exact_mod_cast dh
  have hn0 : (0:ℝ)<N := by linarith
  have hden : (0:ℝ)<2*N-defect N := by linarith
  have hc : 0<c := div_pos hden (sq_pos_of_pos hn0)
  have hqc : c≤q := by
    by_cases h : N%4=0
    · dsimp [c,q]
      norm_num [defect,spectralBound,h]
      field_simp
      norm_num
    · exact ((advantage_iff hN).2 h).le
  have hnum : 1+spectralBound N/4 ≤ 2 := by
    unfold spectralBound
    linarith [Real.cos_le_one (Real.pi*defect N/N)]
  have eq : q/c = ((1+spectralBound N/4)*(N:ℝ))/(2*(N:ℝ)-defect N) := by
    dsimp [q,c]
    field_simp
  have hm : 0<(N:ℝ)-1 := by linarith
  refine ⟨(one_le_div hc).2 hqc,?_⟩
  rw [eq,div_le_div_iff₀ hden hm]
  have hi := mul_le_mul_of_nonneg_right hnum hm.le
  have hj : (1+spectralBound N/4)*((N:ℝ)-1) ≤ 2*N-defect N := by linarith
  nlinarith [mul_le_mul_of_nonneg_right hj hn0.le]

omit [NeZero N] in
theorem optimal_ratio_limit :
    Filter.Tendsto (fun n : ℕ =>
      ((1+spectralBound n/4)/(n:ℝ)) / ((2*(n:ℝ)-defect n)/(n:ℝ)^2))
      Filter.atTop (nhds 1) := by
  apply Metric.tendsto_atTop.mpr
  intro ε he
  obtain ⟨K,hK⟩ := exists_nat_gt (max 3 (1/ε+2))
  refine ⟨K,?_⟩
  intro n hn
  have hn' : (K:ℝ)≤n := by exact_mod_cast hn
  have h3r : (3:ℝ)≤n := by linarith [le_max_left (3:ℝ) (1/ε+2)]
  have h3 : 3≤n := by exact_mod_cast h3r
  letI : NeZero n := ⟨by omega⟩
  have H := ratio_window (N:=n) h3
  dsimp only at H
  rw [Real.dist_eq,abs_of_nonneg (sub_nonneg.mpr H.1)]
  have hm : 0<(n:ℝ)-1 := by linarith
  calc
    _ ≤ (n:ℝ)/(n-1)-1 := sub_le_sub_right H.2 1
    _ = 1/((n:ℝ)-1) := by field_simp; ring
    _ < ε := by
      apply (div_lt_iff₀ hm).mpr
      have hs : 1/ε < (n:ℝ)-1 := by linarith [le_max_right (3:ℝ) (1/ε+2)]
      have heq := (div_lt_iff₀ he).mp hs
      linarith only [heq]


/-- With vertex labels increasing around the cycle, choose the neighbour with
the smaller label. This is the specific rule in the paper's conjecture. -/
def lowestRule (x : ZMod N) : Bool := decide ((x+1).val < (x-1).val)

private lemma lowest_true (hN : 3≤N) (x : ZMod N) :
    lowestRule x=true ↔ x.val=0 ∨ x.val=N-1 := by
  have onev : (1:ZMod N).val=1 := by
    simpa only [Nat.cast_one] using (ZMod.val_natCast_of_lt (by omega : 1<N))
  have one0 : (1:ZMod N)≠0 := by
    intro h
    have hh := congrArg ZMod.val h
    rw [onev,ZMod.val_zero] at hh
    omega
  have nv : (-1:ZMod N).val=N-1 := by rw [ZMod.neg_val,if_neg one0,onev]
  simp only [lowestRule,decide_eq_true_eq]
  by_cases h0 : x=0
  · subst x
    rw [zero_add,zero_sub,onev,nv,ZMod.val_zero]
    exact iff_of_true (by omega) (Or.inl rfl)
  have xp : x.val≠0 := fun h => h0 ((ZMod.val_eq_zero x).mp h)
  have xb := ZMod.val_lt x
  rw [ZMod.val_sub (by omega : (1:ZMod N).val≤x.val),onev]
  by_cases h : x.val+1<N
  · rw [ZMod.val_add_of_lt (by omega),onev]
    omega
  · rw [ZMod.val_add_of_le (by omega),onev]
    omega

private lemma lowest_changes (hN : 4≤N) : changes (lowestRule (N:=N))=4 := by
  have two : (2:ZMod N).val=2 := ZMod.val_natCast_of_lt (by omega : 2<N)
  have h3 : 3≤N := by omega
  have shifted (x : ZMod N) : lowestRule (x+2)=true ↔ x.val=N-2 ∨ x.val=N-3 := by
    rw [lowest_true h3]
    have hx := ZMod.val_lt x
    by_cases he : x.val+2<N
    · rw [ZMod.val_add_of_lt (by omega),two]
      omega
    · rw [ZMod.val_add_of_le (by omega),two]
      omega
  let a : ZMod N := (N-1:ℕ)
  let b : ZMod N := (N-2:ℕ)
  let c : ZMod N := (N-3:ℕ)
  have valiff (x t : ZMod N) : x=t ↔ x.val=t.val := ZMod.val_injective N |>.eq_iff.symm
  have av : a.val=N-1 := ZMod.val_natCast_of_lt (by omega)
  have bv : b.val=N-2 := ZMod.val_natCast_of_lt (by omega)
  have cv : c.val=N-3 := ZMod.val_natCast_of_lt (by omega)
  have bits (x : ZMod N) : (if lowestRule x=lowestRule (x+2) then (0:ℕ) else 1) =
      (if x=0 then 1 else 0)+(if x=a then 1 else 0)+
      (if x=b then 1 else 0)+(if x=c then 1 else 0) := by
    simp only [valiff x,ZMod.val_zero,av,bv,cv]
    have v : lowestRule x=decide (x.val=0 ∨ x.val=N-1) :=
      Bool.eq_iff_iff.mpr (by simpa only [decide_eq_true_eq] using lowest_true h3 x)
    have w : lowestRule (x+2)=decide (x.val=N-2 ∨ x.val=N-3) :=
      Bool.eq_iff_iff.mpr (by simpa only [decide_eq_true_eq] using shifted x)
    rw [v,w]
    by_cases hz : x.val=0 <;> by_cases ha : x.val=N-1 <;>
      by_cases hb : x.val=N-2 <;> by_cases hc : x.val=N-3 <;>
        first | (exfalso; omega) | simp [hz,ha,hb,hc]
    all_goals split_ifs <;> omega
  simp only [changes,bits,Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.mem_univ,if_true]

/-- The paper's rule is strictly suboptimal at precisely the sizes N≥7. -/
theorem lowest_rule_loses_iff (hN : 3≤N) :
    meeting (classicalLaw (lowestRule (N:=N)) lowestRule) <
      meeting (classicalLaw (blockRule (N:=N)) blockRule) ↔ 7≤N := by
  rw [self_meeting,self_meeting]
  have hn : (0:ℝ)<N := by exact_mod_cast NeZero.pos N
  rw [div_lt_div_iff_of_pos_right (sq_pos_of_pos hn),add_lt_add_iff_left]
  rw [Nat.cast_lt]
  by_cases h : N=3
  · have small : changes (lowestRule (N:=3)) = 2 := by decide
    subst N
    have hk := block_optimal (show 3≤3 by decide)
    norm_num [defect] at hk
    omega
  · rw [lowest_changes (by omega : 4≤N)]
    have hk := block_optimal hN
    unfold defect at hk
    split_ifs at hk <;> omega

#print axioms lowest_rule_loses_iff
#print axioms meeting_identity
#print axioms meeting_from_starts
#print axioms classical_optimum
#print axioms quantum_upper
#print axioms bell_attains
#print axioms qubit_orthonormal
#print axioms bell_normalized
#print axioms bell_from_qubits
#print axioms mixture_bound
#print axioms advantage_iff
#print axioms ratio_window
#print axioms optimal_ratio_limit

end
end CycleRendezvous

import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

namespace PauliSkew
open scoped BigOperators
set_option maxHeartbeats 3500000
set_option maxRecDepth 100000
abbrev Point := Fin 15
abbrev Test := Fin 90
abbrev Role := Fin 3
abbrev Bit := ZMod 2

/-- Nonidentity labels 0..14 denote IX,IY,IZ,XI,...,ZZ. The 90 ordered
lines use three four-bit entries each, least significant entry first.
The independent script constructs this table from Gaussian Pauli matrices. -/
def point (e : Test) (r : Role) : Point :=
  Fin.ofNat 15 (((0x69c96c6c9c699c6c9668d86d6d8d688d6d865aca5c5cac5aac5ca558e85e5e8e588e5e854ada4d4dad4aad4da449e94e4e9e499e4e942beb2e2ebe2bbe2eb227a72a2a7a277a2a722363262636233626321bdb1d1dbd1bbd1db11797191979177919711353151535133515310bcb0c0cbc0bbc0cb0078708087807780870034304043403340430 : ℕ) >>> (4*(3*e.val+r.val))) % 16)

def negative (e : Test) : Bit :=
  ((((0xfff000fc0000000000000 : ℕ) >>> e.val) % 2 : ℕ) : Bit)

/-- Multiplication phases in the one-qubit I,X,Y,Z table, in powers of i. -/
private def phase : Fin 4 → Fin 4 → Fin 4 :=
  ![![0,0,0,0],![0,0,1,3],![0,3,0,1],![0,1,3,0]]
private def code (x : Point) := x.val+1
private def angle (x y : Point) : Fin 4 :=
  phase (Fin.ofNat 4 (code x / 4)) (Fin.ofNat 4 (code y / 4)) +
  phase (Fin.ofNat 4 (code x % 4)) (Fin.ofNat 4 (code y % 4))

private def inversePair (x y : Point) : Test :=
  Fin.ofNat 90 (((0x1a80771c0008ce80340000000008e080a602900800002200000002336c800162600000001066847800000000000000064807007f2c000000178094f802e0001c80ae000000076b00700001c011688000000001742200000000a00000005a6c480000000058684009f54000a93800000014a8000218092024008400000005c01600dde8000f1b0000000000a00004000000000000004e541804c50131000182b00015250001200000001f007801900600130048000000000d18000070c000010000000 : ℕ) >>> (7*(15*x.val+y.val))) % 128)

private theorem inverse_left : ∀ e : Test, inversePair (point e 0) (point e 1)=e := by decide +kernel
private theorem inverse_right : ∀ x y : Point, x ≠ y → (angle x y).val % 2=0 →
    point (inversePair x y) 0=x ∧ point (inversePair x y) 1=y := by decide +kernel

/-- The 90 tests enumerate every ordered pair of distinct, commuting nonidentity
two-qubit Paulis exactly once. Their third point is their unsigned product and
their bit records its sign. -/
theorem pauli_geometry :
    (∀ e : Test, point e 0 ≠ point e 1 ∧ (angle (point e 0) (point e 1)).val % 2 = 0 ∧
      code (point e 2) = (code (point e 0)) ^^^ (code (point e 1)) ∧
      negative e = ((angle (point e 0) (point e 1)).val / 2 : ℕ)) ∧
    (∀ x y : Point, x ≠ y → (angle x y).val % 2 = 0 →
      ∃! e : Test, point e 0=x ∧ point e 1=y) := by
  constructor
  · decide +kernel
  · intro x y h₁ h₂
    refine ⟨inversePair x y,inverse_right x y h₁ h₂,?_⟩
    intro e h
    simpa only [h.1,h.2] using (inverse_left e).symm

/-- Six roles recolor each of the ten two-qubit Peres–Mermin grids with a
3-color Latin square. Each row here contains the six resulting oriented lines.
The proof below verifies odd parity, paired incidences, and fourfold coverage. -/
private def context (c : Fin 60) (k : Fin 6) : Test :=
  Fin.ofNat 90 (((0xad0e0d290e6a467f3e53baf0a05392e2ac77d3a5bab311ed198dac4579426b770a91c06075b2c42f591b72ad1416271bad40f199a76b8fbf6865d2f3cf9a9884911d3605e22643459158695152625a2a741419948ca0fcf684e3a93d39a929290ed7545e62637656159094e56565a6a7356169494a0cd45c4e5a9315579288a88cc602e12c1f259098aac84d622a1ad1d219888eb86cb681e32f1929a86a0608d83c2e71a1f55009a2648593e2a79b1d51088a6706d7441e91d19591866c908d96015c261f5d9036e948586211ca71d5998274a06d56805da91951a807a905d15416026134d603789455056120a711496827ca03ce5c05fa90d3d78078488cd3c15f141f2d0037a4c84c3e11f951d2908280586c9440609719211806e485c53015d14131cd036c4c5443211d951118d8270583c23805c970d0ce80 : ℕ) >>> (7*(6*c.val+k.val))) % 128)

private theorem context_geometry :
    (∀ c : Fin 60, (∑ k, negative (context c k))=1) ∧
    (∀ (c : Fin 60) (r : Role) (v : Point), (∑ k, if point (context c k) r=v then (1:Bit) else 0)=0) ∧
    (∀ e : Test, (∑ c, ∑ k, if context c k=e then (1:ℕ) else 0)=4) ∧
    (∑ e : Test, negative e)=0 ∧
    (∀ (r : Role) (v : Point), (∑ e : Test, if point e r=v then (1:Bit) else 0)=0) := by
  decide +kernel


/-- Collect a function summed over an incidence map by its target. -/
private theorem collect {I V R : Type*} [Fintype I] [Fintype V] [DecidableEq V] [CommSemiring R]
    (p : I → V) (f : V → R) :
    (∑ i, f (p i)) = ∑ v, (∑ i, if p i=v then (1:R) else 0)*f v := by
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  simp [ite_mul]

def errorBit (bias : Bit) (X : Role → Point → Bit) (e : Test) : Bit :=
  bias+negative e+∑ r, X r (point e r)

private def bitNat (x : Bit) : ℕ := if x=0 then 0 else 1
private theorem bit_cases : ∀ x : Bit, x=0 ∨ x=1 := by decide
private theorem cast_bit (x : Bit) : (bitNat x : Bit)=x := by
  rcases bit_cases x with rfl|rfl <;> decide

/-- All six constraints in a colored grid together demand odd parity. -/
private theorem context_sum (c : Fin 60) (bias : Bit) (X : Role → Point → Bit) :
    (∑ k, errorBit bias X (context c k))=1 := by
  have oneRole (r : Role) : (∑ k, X r (point (context c k) r))=0 := by
    rw [collect (fun k => point (context c k) r) (X r)]
    simp only [context_geometry.2.1 c r,zero_mul,Finset.sum_const_zero]
  simp only [errorBit,Finset.sum_add_distrib,context_geometry.1 c]
  rw [Finset.sum_comm]
  simp only [oneRole,Finset.sum_const_zero,add_zero]
  rcases bit_cases bias with rfl|rfl <;> decide

private theorem global_sum (bias : Bit) (X : Role → Point → Bit) :
    (∑ e, errorBit bias X e)=0 := by
  have oneRole (r : Role) : (∑ e, X r (point e r))=0 := by
    rw [collect (fun e => point e r) (X r)]
    simp only [context_geometry.2.2.2.2 r,zero_mul,Finset.sum_const_zero]
  simp only [errorBit,Finset.sum_add_distrib,context_geometry.2.2.2.1]
  rw [Finset.sum_comm]
  simp only [oneRole,Finset.sum_const_zero,add_zero]
  rcases bit_cases bias with rfl|rfl <;> decide

private theorem cover (f : Test → ℕ) : (∑ c, ∑ k, f (context c k)) = 4 * ∑ e, f e := by
  have collectOne (c : Fin 60) :=
    collect (context c) f
  simp_rw [collectOne]
  rw [Finset.sum_comm,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  rw [←Finset.sum_mul,context_geometry.2.2.1]

/-- Of ninety ordered lines, at least sixteen have the wrong sign. This
quantifies over three independently assigned sign functions on the 15 Paulis. -/
theorem at_least_sixteen (bias : Bit) (X : Role → Point → Bit) :
    16 ≤ ∑ e, bitNat (errorBit bias X e) := by
  let f := fun e => bitNat (errorBit bias X e)
  have row (c : Fin 60) : 1 ≤ ∑ k, f (context c k) := by
    by_contra! h
    have hz : (∑ k, f (context c k))=0 := by omega
    have hc := congrArg (fun n : ℕ => (n : Bit)) hz
    simp only [Nat.cast_sum,Nat.cast_zero,f,cast_bit] at hc
    rw [context_sum] at hc
    exact one_ne_zero hc
  have hrows := Finset.sum_le_sum (s := Finset.univ) (fun c _ => row c)
  rw [cover] at hrows
  norm_num at hrows
  have even : 2 ∣ ∑ e, f e := by
    apply (ZMod.natCast_eq_zero_iff _ _).mp
    push_cast
    simp only [f,cast_bit,global_sum]
  change 16 ≤ ∑ e, f e
  omega

def toSign (v : Bit) : ℤ := 1-2*(bitNat v : ℤ)

private theorem row_upper (bias : Bit) (X : Role → Point → Bit) :
    (∑ e, toSign (errorBit bias X e)) ≤ 58 := by
  have h : (16:ℤ) ≤ ∑ e, (bitNat (errorBit bias X e) : ℤ) := by
    exact_mod_cast at_least_sixteen bias X
  simp only [toSign,Finset.sum_sub_distrib,←Finset.mul_sum]
  norm_num
  omega

private theorem sign_opp (v : Bit) : toSign (1+v)= -toSign v := by
  rcases bit_cases v with rfl|rfl <;> decide

/-- Signed commuting-triangle statistic in Eq. (52). Each register supplies
one oriented line, verified by pauli_geometry. Bits 0 and 1 encode +1 and −1. -/
def triangle (S : Point → Point → Bit) : ℤ :=
  ∑ e, ∑ f, toSign (negative e+negative f+∑ r, S (point e r) (point f r))

theorem triangle_bound (S : Point → Point → Bit) : |triangle S| ≤ 5220 := by
  have up (e : Test) := row_upper (negative e) (fun r=> S (point e r))
  have lo (e : Test) := row_upper (1+negative e) (fun r=> S (point e r))
  have flip (e f : Test) : toSign (errorBit (1+negative e) (fun r => S (point e r)) f) =
      -toSign (errorBit (negative e) (fun r => S (point e r)) f) := by
    simp only [errorBit,add_assoc,sign_opp]
  simp_rw [flip,Finset.sum_neg_distrib] at lo
  have upper := Finset.sum_le_sum (s:=Finset.univ) (fun e _=>up e)
  have lower := Finset.sum_le_sum (s:=Finset.univ) (fun e _=>lo e)
  simp only [Finset.sum_neg_distrib] at lower
  change |∑ e, ∑ f, toSign (errorBit (negative e) (fun r => S (point e r)) f)| ≤ 5220
  norm_num at upper lower
  exact abs_le.mpr ⟨by omega,upper⟩

/-- An actual ordered pair of distinct, commuting, nonidentity Paulis. -/
abbrev CommutingPair := {p : Point × Point // p.1≠p.2 ∧ (angle p.1 p.2).val % 2=0}

private def testEquiv : Test ≃ CommutingPair where
  toFun e := ⟨(point e 0,point e 1),(pauli_geometry.1 e).1,(pauli_geometry.1 e).2.1⟩
  invFun p := inversePair p.val.1 p.val.2
  left_inv := inverse_left
  right_inv p := by
    apply Subtype.ext
    exact Prod.ext (inverse_right p.val.1 p.val.2 p.property.1 p.property.2).1
      (inverse_right p.val.1 p.val.2 p.property.1 p.property.2).2

private def third (x y : Point) : Point :=
  Fin.ofNat 15 (((code x) ^^^ (code y)) - 1)

private def labels (q : CommutingPair) : Role → Point :=
  ![q.val.1,q.val.2,third q.val.1 q.val.2]

private def productSign (q : CommutingPair) : Bit :=
  ((angle q.val.1 q.val.2).val/2 : ℕ)

private theorem test_labels : ∀ e : Test, ∀ r : Role, labels (testEquiv e) r=point e r := by
  decide +kernel

private theorem test_sign (e : Test) : productSign (testEquiv e)=negative e :=
  (pauli_geometry.1 e).2.2.2.symm

/-- Eq. (52) summed directly over the Pauli pairs A,A′ and B,B′, their
multiplication signs, and the three signs in the target array. -/
def commutingTriangles (S : Point → Point → Bit) : ℤ :=
  ∑ a : CommutingPair, ∑ b : CommutingPair, toSign
    (productSign a + productSign b + ∑ r, S (labels a r) (labels b r))

theorem commutingTriangles_eq (S : Point → Point → Bit) : commutingTriangles S=triangle S := by
  symm
  unfold commutingTriangles triangle
  apply Fintype.sum_equiv testEquiv
  intro a
  apply Fintype.sum_equiv testEquiv
  intro b
  simp only [test_labels,test_sign]

/-- Eq. (57) after inserting the paper's second and third Haar moments,
E tr(R²)=180 and E tr(R³)=(4/15) Δ. -/
noncomputable def averagedSkew (S : Point → Point → Bit) : ℝ :=
  ((4:ℝ)/15 * commutingTriangles S) / (180 * Real.sqrt 180)

/-- Strict uniform separation from the two-qubit Clifford reference 1/√3. -/
theorem skew_bound (S : Point → Point → Bit) :
    |averagedSkew S| ≤ 58/(45*Real.sqrt 5) ∧ 58/(45*Real.sqrt 5)<1/Real.sqrt 3 := by
  have bound : |(triangle S : ℝ)| ≤ 5220 := by exact_mod_cast triangle_bound S
  have s5 : 0 < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num)
  have s3 : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have s180 : Real.sqrt 180 = 6*Real.sqrt 5 := by
    rw [show (180:ℝ)=36*5 by norm_num,Real.sqrt_mul (by norm_num : 0≤(36:ℝ))]
    rw [show (36:ℝ)=(6:ℝ)^2 by norm_num,Real.sqrt_sq (by norm_num : 0≤(6:ℝ))]
  constructor
  · unfold averagedSkew
    rw [commutingTriangles_eq,s180,abs_div,abs_mul]
    rw [abs_of_pos (by norm_num : 0 < (4:ℝ)/15),abs_of_pos (by positivity : 0 < 180*(6*Real.sqrt 5))]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith only [mul_nonneg (sub_nonneg.mpr bound) s5.le]
  · apply (div_lt_div_iff₀ (by positivity) s3).mpr
    have h5 := Real.sq_sqrt (by norm_num : 0≤(5:ℝ))
    have h3 := Real.sq_sqrt (by norm_num : 0≤(3:ℝ))
    nlinarith only [h5,h3, sq_nonneg (45*Real.sqrt 5-58*Real.sqrt 3),
      s3,s5, mul_pos s5 s3]

#print axioms pauli_geometry
#print axioms at_least_sixteen
#print axioms triangle_bound
#print axioms commutingTriangles_eq
#print axioms skew_bound
end PauliSkew

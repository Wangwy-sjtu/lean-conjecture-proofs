import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace BandRect
noncomputable section
open Finset Polynomial

abbrev Poly := Polynomial ℚ

/-- Integer-indexed coefficients extend the sequence by zero at negative indices. -/
def coeffZ (P : Poly) (z : ℤ) : ℚ := if 0≤z then P.coeff z.toNat else 0

@[simp] theorem coeffZ_nat (P : Poly) (k : ℕ) : coeffZ P k=P.coeff k := by simp [coeffZ]

private theorem coeffZ_shift (P : Poly) (d : ℕ) (z : ℤ) : coeffZ (X^d*P) z=coeffZ P (z-d) := by
  by_cases h : 0≤z
  · let n := z.toNat
    have e : (n:ℤ)=z := by dsimp [n];omega
    rw [←e,coeffZ_nat,Polynomial.coeff_X_pow_mul']
    by_cases hd : d≤n
    · rw [if_pos hd,←Nat.cast_sub hd,coeffZ_nat]
    · simp only [if_neg hd,coeffZ,if_neg (show ¬0≤(n:ℤ)-d by omega)]
  · simp only [coeffZ,if_neg h,if_neg (show ¬0≤z-d by omega)]

/-- A finite convolution formula with any common upper bound for the first factor's support. -/
private theorem conv (P Q : Poly) (z : ℤ) (D : ℕ) (hD : ∀ i>D, P.coeff i=0) :
    coeffZ (P*Q) z=∑ i∈range (D+1),P.coeff i*coeffZ Q (z-i) := by
  by_cases zero : z<0
  · rw [coeffZ,if_neg (by omega)]
    apply (Finset.sum_eq_zero _).symm
    intro i _
    simp only [coeffZ,if_neg (show ¬0≤z-i by omega),mul_zero]
  · let n := z.toNat
    have e : (n:ℤ)=z := by dsimp [n];omega
    rw [←e,coeffZ_nat,Polynomial.coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j=>P.coeff i*Q.coeff j)]
    let f : ℕ→ℚ := fun i=>P.coeff i*coeffZ Q ((n:ℤ)-i)
    trans ∑i∈range (n+1),f i
    · apply Finset.sum_congr rfl
      intro i hi
      have h : i≤n := Nat.le_of_lt_succ (mem_range.1 hi)
      simp [f,←Nat.cast_sub h]
    · by_cases h : n≤D
      · apply Finset.sum_subset (Finset.range_mono (by omega : n+1≤D+1))
        intro i _ hi
        have no : ¬i<n+1 := fun c=>hi (mem_range.2 c)
        simp only [f,coeffZ,if_neg (show ¬0≤(n:ℤ)-i by omega),mul_zero]
      · apply (Finset.sum_subset (Finset.range_mono (by omega : D+1≤n+1)) ?_).symm
        intro i _ hi
        have no : ¬i<D+1 := fun c=>hi (mem_range.2 c)
        simp [f,hD i (by omega)]

/-- Order-two total positivity of the Toeplitz matrix of coefficients. -/
def TP (P : Poly) : Prop := ∀ (i j : ℤ) (d : ℕ), i≤j →
  coeffZ P i*coeffZ P (j+d) ≤ coeffZ P (i+d)*coeffZ P j

/-- Order-two Cauchy--Binet, in the form of an inequality between four dot products. -/
private theorem dot_det (f g p q : ℕ→ℚ) (N : ℕ)
    (row : ∀ i j, i≤j → f j*g i≤f i*g j) (col : ∀ i j, i≤j → p j*q i≤p i*q j) :
    (∑i∈range N,f i*q i)*(∑i∈range N,g i*p i) ≤ (∑i∈range N,f i*p i)*(∑i∈range N,g i*q i) := by
  induction N with
  | zero => simp
  | succ n ih =>
    have bound (i : ℕ) (hi : i∈range n) :=
      mul_nonneg (sub_nonneg.2 (row i n (le_of_lt (mem_range.1 hi))))
        (sub_nonneg.2 (col i n (le_of_lt (mem_range.1 hi))))
    have extra : 0 ≤ (g n*q n)*(∑i∈range n,f i*p i)+(f n*p n)*(∑i∈range n,g i*q i)-
        (g n*p n)*(∑i∈range n,f i*q i)-(f n*q n)*(∑i∈range n,g i*p i) := by
      simp only [Finset.mul_sum,←Finset.sum_add_distrib,←Finset.sum_sub_distrib]
      apply Finset.sum_nonneg
      intro i hi
      linarith only [bound i hi]
    simp only [Finset.sum_range_succ]
    linarith only [ih,extra]

/-- Rank sequences with order-two total positivity are closed under convolution. -/
theorem tp_mul {P Q : Poly} (a : TP P) (b : TP Q) : TP (P*Q) := by
  intro x y d hxy
  let f : ℕ→ℚ := fun i=>coeffZ P i
  let g : ℕ→ℚ := fun i=>coeffZ P ((i:ℤ)-d)
  let p : ℕ→ℚ := fun i=>coeffZ Q (x+d-i)
  let q : ℕ→ℚ := fun i=>coeffZ Q (y+d-i)
  let N := max P.natDegree (X^d*P).natDegree
  have so (z : ℤ) : coeffZ (P*Q) z=∑i∈range (N+1),f i*coeffZ Q (z-i) := by
    simpa [f] using conv P Q z N (fun i hi=>Polynomial.coeff_eq_zero_of_natDegree_lt
      (lt_of_le_of_lt (le_max_left ..) hi))
  have sh (z : ℤ) : coeffZ (P*Q) (z-d)=∑i∈range (N+1),g i*coeffZ Q (z-i) := by
    rw [←coeffZ_shift,←mul_assoc,conv (X^d*P) Q z N (fun i hi=>Polynomial.coeff_eq_zero_of_natDegree_lt
      (lt_of_le_of_lt (le_max_right ..) hi))]
    apply Finset.sum_congr rfl
    intro i _
    rw [←coeffZ_nat (X^d*P),coeffZ_shift]
  have row (i j : ℕ) (h : i≤j) : f j*g i≤f i*g j := by
    have z := a ((i:ℤ)-d) ((j:ℤ)-d) d (by omega)
    simpa [f,g,mul_comm] using z
  have col (i j : ℕ) (h : i≤j) : p j*q i≤p i*q j := by
    have z := b (x+d-j) (y+d-j) (j-i) (by omega)
    have e (t : ℤ) : t+d-j+(j-i:ℕ)=t+d-i := by rw [Nat.cast_sub h];omega
    simpa only [p,q,e] using z
  have main := dot_det f g p q (N+1) row col
  dsimp only [p,q] at main
  rw [←so (y+d),←sh (x+d),←so (x+d),←sh (y+d)] at main
  simpa [mul_comm] using main

/-- One inclusive interval of permitted counts for a finite class. -/
structure Segment where
  size : ℕ
  lo : ℕ
  hi : ℕ
  valid : lo≤hi
  fits : hi≤size

/-- Ordinary generating polynomial for labelled choices from this class. -/
def Segment.poly (c : Segment) : Poly := ∑i∈Icc c.lo c.hi, monomial i (c.size.choose i:ℚ)

@[simp] theorem coeff_interval (c : Segment) (i : ℕ) :
    c.poly.coeff i=if c.lo≤i ∧ i≤c.hi then (c.size.choose i:ℚ) else 0 := by
  simp [Segment.poly,Polynomial.coeff_monomial]

private theorem coeffZ_interval (c : Segment) (i : ℤ) :
    coeffZ c.poly i=if (c.lo:ℤ)≤i ∧ i≤c.hi then (c.size.choose i.toNat:ℚ) else 0 := by
  by_cases h : 0≤i
  · rw [coeffZ,if_pos h,coeff_interval]
    split_ifs <;> first | rfl | omega
  · rw [coeffZ,if_neg h,if_neg (by omega)]

private theorem interval_nn (c : Segment) (i : ℤ) : 0≤coeffZ c.poly i := by
  rw [coeffZ_interval]
  split <;> positivity

private theorem choose_step (s i : ℕ) (hi : i≤s) :
    ((i:ℚ)+1)*(s.choose (i+1):ℚ)=((s:ℚ)-i)*(s.choose i:ℚ) := by
  rw [← Nat.cast_sub hi,mul_comm ((i:ℚ)+1),mul_comm _ (s.choose i:ℚ)]
  exact_mod_cast Nat.choose_succ_right_eq s i

private theorem interval_cross (c : Segment) (i j : ℤ) (hij : i≤j) :
    coeffZ c.poly i*coeffZ c.poly (j+1)≤coeffZ c.poly (i+1)*coeffZ c.poly j := by
  by_cases h : (c.lo:ℤ)≤i ∧ j+1≤c.hi
  · let l := i.toNat
    let r := j.toNat
    have li : (l:ℤ)=i := by dsimp [l];omega
    have rj : (r:ℤ)=j := by dsimp [r];omega
    rw [←li,←rj,← Nat.cast_one,← Nat.cast_add,← Nat.cast_add]
    simp only [coeffZ_nat,coeff_interval,if_pos (show c.lo≤l ∧ l≤c.hi by omega),
      if_pos (show c.lo≤r ∧ r≤c.hi by omega),if_pos (show c.lo≤l+1 ∧ l+1≤c.hi by omega),
      if_pos (show c.lo≤r+1 ∧ r+1≤c.hi by omega)]
    have eq (u : ℕ) (hu : u≤c.size) : (c.size.choose (u+1):ℚ)=
        (c.size.choose u:ℚ)*(((c.size:ℚ)-u)/(u+1)) := by
      have step := choose_step c.size u hu
      field_simp
      linarith
    have ord : (((c.size:ℚ)-r)/(r+1))≤((c.size:ℚ)-l)/(l+1) := by
      have le : (l:ℚ)≤r := by exact_mod_cast (by omega : l≤r)
      have fits := c.fits
      apply div_le_div₀ (sub_nonneg.2 (by exact_mod_cast (by omega : l≤c.size))) (by linarith)
        (by positivity) (by linarith)
    have fits := c.fits
    rw [eq r (by omega),eq l (by omega)]
    have nn : 0≤(c.size.choose l:ℚ)*(c.size.choose r:ℚ) := by positivity
    linarith only [mul_le_mul_of_nonneg_left ord nn]
  · have z : coeffZ c.poly i=0 ∨ coeffZ c.poly (j+1)=0 := by
      simp only [coeffZ_interval]
      by_cases hi : i<c.lo
      · exact Or.inl (if_neg (by omega))
      · exact Or.inr (if_neg (by omega))
    rcases z with z|z <;> rw [z] <;> simpa using mul_nonneg (interval_nn c (i+1)) (interval_nn c j)

theorem tp_interval (c : Segment) : TP c.poly := by
  intro i j d hij
  induction d with
  | zero => simp
  | succ d ih =>
    push_cast
    have fits := c.fits
    by_cases h : (c.lo:ℤ)≤i ∧ j+(d+1)≤c.hi
    · have wp : 0<coeffZ c.poly (i+d) := by
        rw [coeffZ_interval,if_pos (by omega)]
        exact_mod_cast Nat.choose_pos (by omega : (i+(d:ℤ)).toNat≤c.size)
      have add (x : ℤ) : x+(d+1)=x+d+1 := by omega
      rw [add,add]
      apply le_of_mul_le_mul_right (a:=coeffZ c.poly (i+d)) _ wp
      have x := mul_le_mul_of_nonneg_left (interval_cross c (i+d) (j+d) (by omega)) (interval_nn c i)
      have y := mul_le_mul_of_nonneg_right ih (interval_nn c (i+d+1))
      linarith only [x,y]
    · have z : coeffZ c.poly i=0 ∨ coeffZ c.poly (j+(d+1))=0 := by
        by_cases hi : i<c.lo
        · exact Or.inl (by rw [coeffZ_interval,if_neg (by omega)])
        · exact Or.inr (by rw [coeffZ_interval,if_neg (by omega)])
      rcases z with z|z <;> rw [z] <;> simpa using mul_nonneg (interval_nn c (i+(d+1))) (interval_nn c j)

/-- A polynomial has positive coefficients precisely on the prescribed integer interval. -/
structure PositiveRange (P : Poly) (l a : ℕ) : Prop where
  nn : ∀ i,0≤P.coeff i
  pos : ∀ i,l≤i→i≤a→0<P.coeff i
  out : ∀ i,i<l ∨ a<i→P.coeff i=0

theorem positive_interval (c : Segment) : PositiveRange c.poly c.lo c.hi := by
  refine ⟨fun i=>by simpa using interval_nn c i,?_,?_⟩
  · intro i hl hu
    rw [coeff_interval,if_pos ⟨hl,hu⟩]
    exact_mod_cast Nat.choose_pos (hu.trans c.fits)
  · intro i h
    rw [coeff_interval,if_neg (by omega)]

set_option maxHeartbeats 1200000 in
theorem PositiveRange.mul {P Q : Poly} {l a m b : ℕ} (hp : PositiveRange P l a)
    (hq : PositiveRange Q m b) (hla : l≤a) (hmb : m≤b) : PositiveRange (P*Q) (l+m) (a+b) := by
  have nz (p : ℕ×ℕ) : 0≤P.coeff p.1*Q.coeff p.2 := mul_nonneg (hp.nn _) (hq.nn _)
  refine ⟨fun i=>by rw [Polynomial.coeff_mul];exact Finset.sum_nonneg (fun p _=>nz p),?_,?_⟩
  · intro k low high
    let i := min a (k-m)
    let j := k-i
    have e : i+j=k := by dsimp [i,j];omega
    have pos := mul_pos (hp.pos i (by dsimp [i];omega) (by dsimp [i];omega))
      (hq.pos j (by dsimp [i,j];omega) (by dsimp [i,j];omega))
    rw [Polynomial.coeff_mul]
    exact pos.trans_le (Finset.single_le_sum (f:=fun p:ℕ×ℕ => P.coeff p.1*Q.coeff p.2)
      (fun p _=>nz p) (show (i,j)∈antidiagonal k from Finset.mem_antidiagonal.2 e))
  · intro k hk
    rw [Polynomial.coeff_mul]
    apply Finset.sum_eq_zero
    intro p h
    have e := Finset.mem_antidiagonal.1 h
    by_cases h : p.1<l ∨ a<p.1
    · rw [hp.out _ h,zero_mul]
    · rw [hq.out _ (by omega),mul_zero]

/-- The likelihood ratio of the second coefficient sequence to the first increases. -/
def LR (P Q : Poly) : Prop := ∀ i j : ℕ, i≤j → Q.coeff i*P.coeff j≤P.coeff i*Q.coeff j

private theorem lr_mul {A B C : Poly} (h : LR A B) (lc : TP C) : LR (A*C) (B*C) := by
  intro x y xy
  let N := max A.natDegree B.natDegree
  let p : ℕ→ℚ := fun i=>coeffZ C ((x:ℤ)-i)
  let q : ℕ→ℚ := fun i=>coeffZ C ((y:ℤ)-i)
  have col (i j : ℕ) (ij : i≤j) : p j*q i≤p i*q j := by
    have z := lc ((x:ℤ)-j) ((y:ℤ)-j) (j-i) (by omega)
    have e (t : ℤ) : t-j+(j-i:ℕ)=t-i := by rw [Nat.cast_sub ij];omega
    simpa only [p,q,e] using z
  have cb (z : ℕ) : (B*C).coeff z=∑i∈range (N+1),B.coeff i*coeffZ C ((z:ℤ)-i) := by
    rw [←coeffZ_nat,conv B C _ N (fun i hi=>coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (le_max_right ..) hi))]
  have ca (z : ℕ) : (A*C).coeff z=∑i∈range (N+1),A.coeff i*coeffZ C ((z:ℤ)-i) := by
    rw [←coeffZ_nat,conv A C _ N (fun i hi=>coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (le_max_left ..) hi))]
  rw [cb,ca,ca,cb,mul_comm (∑i∈range (N+1),B.coeff i*_)]
  exact dot_det A.coeff B.coeff p q (N+1) (fun i j ij=>by simpa only [mul_comm] using h i j ij) col

private theorem lr_add_right {P A B : Poly} (a : LR P A) (b : LR P B) : LR P (A+B) := by
  intro i j ij
  simp only [coeff_add]
  linarith only [a i j ij,b i j ij]

private theorem lr_add_left {P A B : Poly} (a : LR A P) (b : LR B P) : LR (A+B) P := by
  intro i j ij
  simp only [coeff_add]
  linarith only [a i j ij,b i j ij]

private def NN (P : Poly) := ∀i,0≤P.coeff i

private theorem nn_mul {P Q : Poly} (p : NN P) (q : NN Q) : NN (P*Q) := by
  intro k
  rw [coeff_mul]
  exact Finset.sum_nonneg (fun i _=>mul_nonneg (p i.1) (q i.2))

private theorem nn_add {P Q : Poly} (p : NN P) (q : NN Q) : NN (P+Q) :=
  fun k=>by rw [coeff_add];exact add_nonneg (p k) (q k)

private theorem coeff_bound_mul {A B P : Poly} {c : ℚ} (h : ∀i,A.coeff i≤c*B.coeff i)
    (p : NN P) (k : ℕ) : (A*P).coeff k≤c*(B*P).coeff k := by
  rw [coeff_mul,coeff_mul,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro t _
  linarith only [mul_le_mul_of_nonneg_right (h t.1) (p t.2)]

/-- A rectangle certificate records the two weighted boundary faces at each total size. -/
structure Box where
  poly : Poly
  low : Poly
  high : Poly
  size : ℕ
  lo : ℕ
  hi : ℕ
  valid : lo≤hi
  fits : hi≤size
  tp : TP poly
  support : PositiveRange poly lo hi
  lowNN : ∀i,0≤low.coeff i
  highNN : ∀i,0≤high.coeff i
  lower : LR low poly
  upper : LR poly high
  bound : ∀i,low.coeff i≤(lo:ℚ)*poly.coeff i
  moves : X*(1+X)*poly.derivative-C (size:ℚ)*X*poly=low-X*high

/-- Joining independent rank classes multiplies their generating polynomials. -/
def Box.mul (A B : Box) : Box where
  poly := A.poly*B.poly
  low := A.low*B.poly+A.poly*B.low
  high := A.high*B.poly+A.poly*B.high
  size := A.size+B.size
  lo := A.lo+B.lo
  hi := A.hi+B.hi
  valid := by have := A.valid;have := B.valid;omega
  fits := by have := A.fits;have := B.fits;omega
  tp := tp_mul A.tp B.tp
  support := A.support.mul B.support A.valid B.valid
  lowNN := nn_add (nn_mul A.lowNN B.support.nn) (nn_mul A.support.nn B.lowNN)
  highNN := nn_add (nn_mul A.highNN B.support.nn) (nn_mul A.support.nn B.highNN)
  lower := lr_add_left (lr_mul A.lower B.tp) (by simpa only [mul_comm] using lr_mul B.lower A.tp)
  upper := lr_add_right (lr_mul A.upper B.tp) (by simpa only [mul_comm] using lr_mul B.upper A.tp)
  bound := by
    intro k
    rw [coeff_add,mul_comm A.poly B.low]
    have a := coeff_bound_mul A.bound B.support.nn k
    have b := coeff_bound_mul B.bound A.support.nn k
    rw [mul_comm B.poly A.poly] at b
    push_cast
    linarith only [a,b]
  moves := by
    rw [Polynomial.derivative_mul,Nat.cast_add,map_add]
    have a := congrArg (fun v : Poly=>v*B.poly) A.moves
    have b := congrArg (fun v : Poly=>A.poly*v) B.moves
    dsimp at a b
    linear_combination a+b

private def face (P : Poly) (r : ℕ) (v : ℚ) : Poly := monomial r (v*P.coeff r)

@[simp] private theorem coeff_face (P : Poly) (r i : ℕ) (v : ℚ) :
    (face P r v).coeff i=if i=r then v*P.coeff i else 0 := by
  by_cases h : i=r
  · simp [face,h]
  · simp [face,Polynomial.coeff_monomial,h,Ne.symm h]

private theorem euler (P : Poly) (k : ℕ) : (X*P.derivative).coeff k=(k:ℚ)*P.coeff k := by
  cases k with
  | zero => simp
  | succ k => simp [Polynomial.coeff_derivative,mul_comm]

private theorem formal_step (P L H : Poly) (S k : ℕ) :
    (X*(1+X)*P.derivative-C (S:ℚ)*X*P).coeff (k+1) - (L-X*H).coeff (k+1) =
    ((k:ℚ)+1)*P.coeff (k+1)-L.coeff (k+1)-(((S:ℚ)-k)*P.coeff k-H.coeff k) := by
  rw [show X*(1+X)*P.derivative-C (S:ℚ)*X*P=
      X*P.derivative+X*(X*P.derivative-C (S:ℚ)*P) by ring]
  simp only [coeff_add,coeff_sub,euler,coeff_X_mul,coeff_C_mul,coeff_derivative]
  ring

private theorem interval_step (c : Segment) (k : ℕ) :
    ((k:ℚ)+1)*c.poly.coeff (k+1)-(face c.poly c.lo c.lo).coeff (k+1)=
    ((c.size:ℚ)-k)*c.poly.coeff k-(face c.poly c.hi ((c.size:ℚ)-c.hi)).coeff k := by
  have v := c.valid
  have fits := c.fits
  simp only [coeff_face]
  by_cases low : k<c.lo
  · have p := (positive_interval c).out k (Or.inl low)
    rw [p,if_neg (show k≠c.hi by omega),mul_zero,sub_zero]
    by_cases e : k+1=c.lo
    · rw [if_pos e,←e,Nat.cast_add,Nat.cast_one,sub_self]
    · rw [if_neg e,(positive_interval c).out (k+1) (Or.inl (by omega)),mul_zero,sub_zero]
  · rw [if_neg (show k+1≠c.lo by omega),sub_zero]
    by_cases high : k<c.hi
    · rw [if_neg high.ne,sub_zero,coeff_interval,coeff_interval,if_pos (by omega),if_pos (by omega)]
      exact choose_step c.size k (by omega)
    · rw [(positive_interval c).out (k+1) (Or.inr (by omega)),mul_zero]
      by_cases e : k=c.hi
      · rw [if_pos e,e,sub_self]
      · rw [if_neg e,(positive_interval c).out k (Or.inr (by omega)),mul_zero,sub_zero]

/-- A single interval supplies both boundary faces used by the rectangle proof. -/
def Segment.box (c : Segment) : Box where
  poly := c.poly
  low := face c.poly c.lo c.lo
  high := face c.poly c.hi ((c.size:ℚ)-c.hi)
  size := c.size
  lo := c.lo
  hi := c.hi
  valid := c.valid
  fits := c.fits
  tp := tp_interval c
  support := positive_interval c
  lowNN := by
    intro i
    rw [coeff_face]
    split
    · exact mul_nonneg (by positivity) ((positive_interval c).nn i)
    · rfl
  highNN := by
    intro i
    rw [coeff_face]
    split
    · exact mul_nonneg (sub_nonneg.2 (by exact_mod_cast c.fits)) ((positive_interval c).nn i)
    · rfl
  lower := by
    intro i j hij
    simp only [coeff_face]
    by_cases j0 : j=c.lo
    · by_cases i0 : i=c.lo
      · rw [i0,j0];simp [mul_comm]
      · rw [(positive_interval c).out i (Or.inl (by omega)),if_neg i0,zero_mul,zero_mul]
    · rw [if_neg j0,mul_zero]
      by_cases i0 : i=c.lo
      · rw [if_pos i0]
        exact mul_nonneg (mul_nonneg (by positivity) ((positive_interval c).nn i)) ((positive_interval c).nn j)
      · rw [if_neg i0,zero_mul]
  upper := by
    intro i j hij
    simp only [coeff_face]
    by_cases i0 : i=c.hi
    · by_cases j0 : j=c.hi
      · rw [i0,j0];simp [mul_comm]
      · rw [(positive_interval c).out j (Or.inr (by omega)),if_neg j0,mul_zero,mul_zero]
    · rw [if_neg i0,zero_mul]
      by_cases j0 : j=c.hi
      · rw [if_pos j0]
        exact mul_nonneg ((positive_interval c).nn i) (mul_nonneg (sub_nonneg.2 (by exact_mod_cast c.fits))
          ((positive_interval c).nn j))
      · rw [if_neg j0,mul_zero]
  bound := by
    intro i
    rw [coeff_face]
    split
    · rfl
    · exact mul_nonneg (by positivity) ((positive_interval c).nn i)
  moves := by
    ext k
    cases k with
    | zero =>
      rw [show X*(1+X)*c.poly.derivative-C (c.size:ℚ)*X*c.poly =
          X*((1+X)*c.poly.derivative-C (c.size:ℚ)*c.poly) by ring]
      simp only [mul_coeff_zero,coeff_X_zero,zero_mul,coeff_sub,coeff_face,sub_zero]
      split
      · rename_i e
        simp [←e]
      · rfl
    | succ k =>
      apply sub_eq_zero.1
      rw [formal_step,interval_step c k,sub_self]

/-- Probability of the rectangle for a uniformly sampled hand of the prescribed size. -/
def Box.mass (A : Box) (k : ℕ) : ℚ := A.poly.coeff k/(A.size.choose k:ℚ)

private def up (A : Box) (k : ℕ) : ℚ := 1-A.high.coeff k/A.poly.coeff k/((A.size:ℚ)-k)
private def down (A : Box) (k : ℕ) : ℚ := 1-A.low.coeff k/A.poly.coeff k/k

private theorem move (A : Box) (k : ℕ) :
    ((k:ℚ)+1)*A.poly.coeff (k+1)-A.low.coeff (k+1)=
    ((A.size:ℚ)-k)*A.poly.coeff k-A.high.coeff k := by
  have h := formal_step A.poly A.low A.high A.size k
  rw [A.moves,sub_self] at h
  linarith only [h]

private theorem down_pos (A : Box) (k : ℕ) (hk : A.lo<k) (hhi : k≤A.hi) : 0<down A k := by
  have p := A.support.pos k hk.le hhi
  have lower := (div_le_iff₀ p).2 (A.bound k)
  have z : (A.lo:ℚ)<k := by exact_mod_cast hk
  have pos : 0<(k:ℚ) := by exact_mod_cast (by omega : 0<k)
  apply sub_pos.2
  apply (div_lt_iff₀ pos).2
  linarith

private theorem up_pos (A : Box) (k : ℕ) (hk : A.lo≤k) (hhi : k<A.hi) : 0<up A k := by
  have p := A.support.pos k hk hhi.le
  have p1 := A.support.pos (k+1) (by omega) (by omega)
  have delta : (A.lo:ℚ)<(k:ℚ)+1 := by exact_mod_cast (by omega : A.lo<k+1)
  have zero := mul_lt_mul_of_pos_right delta p1
  have den : 0<(A.size:ℚ)-k := sub_pos.2 (by exact_mod_cast hhi.trans_le A.fits)
  apply sub_pos.2
  apply (div_lt_iff₀ den).2
  rw [one_mul]
  apply (div_lt_iff₀ p).2
  linarith only [A.bound (k+1),zero,move A k]

private theorem mass_up_down (A : Box) (k : ℕ) (hk : A.lo≤k) (hhi : k<A.hi) :
    A.mass (k+1)*down A (k+1)=A.mass k*up A k := by
  have x := A.support.pos k hk hhi.le
  have y := A.support.pos (k+1) (by omega) (by omega)
  have fits := A.fits
  have b : 0<(A.size.choose k:ℚ) := by exact_mod_cast Nat.choose_pos (by omega : k≤A.size)
  have b1 : 0<(A.size.choose (k+1):ℚ) := by exact_mod_cast Nat.choose_pos (by omega : k+1≤A.size)
  have den : 0<(A.size:ℚ)-k := sub_pos.2 (by exact_mod_cast hhi.trans_le fits)
  have d : 0<(k:ℚ)+1 := by positivity
  have xu : A.mass k*up A k=(((A.size:ℚ)-k)*A.poly.coeff k-A.high.coeff k)/
      (((A.size:ℚ)-k)*(A.size.choose k:ℚ)) := by
    unfold Box.mass up
    field_simp [x.ne',b.ne',den.ne']
  have yd : A.mass (k+1)*down A (k+1)=(((k:ℚ)+1)*A.poly.coeff (k+1)-A.low.coeff (k+1))/
      (((k:ℚ)+1)*(A.size.choose (k+1):ℚ)) := by
    unfold Box.mass down
    push_cast
    field_simp [y.ne',b1.ne',d.ne']
  rw [xu,yd,choose_step A.size k (by omega),move A k]

private theorem up_drop (A : Box) (k : ℕ) (hk : A.lo≤k) (hhi : k+2≤A.hi) : up A (k+1)≤up A k := by
  have fits := A.fits
  have p := A.support.pos k hk (by omega)
  have p1 := A.support.pos (k+1) (by omega) (by omega)
  have r : A.high.coeff k/A.poly.coeff k ≤ A.high.coeff (k+1)/A.poly.coeff (k+1) :=
    (div_le_div_iff₀ p p1).2 (by linarith only [A.upper k (k+1) (by omega)])
  have d : 0<(A.size:ℚ)-((k:ℚ)+1) := by
    exact_mod_cast (show 0<(A.size:ℤ)-(k+1) by omega)
  unfold up
  push_cast
  apply sub_le_sub_left
  exact div_le_div₀ (div_nonneg (A.highNN _) p1.le) r d (by linarith)

private theorem down_rise (A : Box) (k : ℕ) (hk : A.lo≤k) (hhi : k+2≤A.hi) :
    down A (k+1)≤down A (k+2) := by
  have p := A.support.pos (k+1) (by omega) (by omega)
  have q := A.support.pos (k+2) (by omega) hhi
  have r : A.low.coeff (k+2)/A.poly.coeff (k+2)≤A.low.coeff (k+1)/A.poly.coeff (k+1) :=
    (div_le_div_iff₀ q p).2 (by linarith only [A.lower (k+1) (k+2) (by omega)])
  unfold down
  push_cast
  apply sub_le_sub_left
  exact div_le_div₀ (div_nonneg (A.lowNN _) p.le) r (by positivity) (by linarith)

/-- Rectangular multivariate-hypergeometric events are log-concave in the sample size. -/
theorem Box.log_concave (A : Box) (k : ℕ) : A.mass k*A.mass (k+2)≤(A.mass (k+1))^2 := by
  by_cases l : A.lo≤k
  · by_cases h : k+2≤A.hi
    · have d1 := down_pos A (k+1) (by omega) (by omega)
      have d2 := down_pos A (k+2) (by omega) h
      have g (j : ℕ) (lo : A.lo≤j) (hi : j<A.hi) : A.mass (j+1)=A.mass j*(up A j/down A (j+1)) := by
        rw [←mul_div_assoc]
        exact (eq_div_iff (down_pos A (j+1) (by omega) (by omega)).ne').2 (mass_up_down A j lo hi)
      have cmp := div_le_div₀ (up_pos A k l (by omega)).le (up_drop A k l h) d1 (down_rise A k l h)
      have nn (j : ℕ) : 0≤A.mass j := div_nonneg (A.support.nn j) (by positivity)
      have mono := mul_le_mul_of_nonneg_left cmp (mul_nonneg (nn k) (nn (k+1)))
      have x := congrArg (fun w : ℚ=>w*A.mass (k+1)) (g k l (by omega))
      have y := congrArg (fun w : ℚ=>A.mass k*w) (g (k+1) (by omega) (by omega))
      dsimp at x y
      linarith only [mono,x,y]
    · have z : A.mass (k+2)=0 := by simp [Box.mass,A.support.out _ (Or.inr (by omega : A.hi<k+2))]
      rw [z,mul_zero]
      exact sq_nonneg _
  · have z : A.mass k=0 := by simp [Box.mass,A.support.out _ (Or.inl (by omega : k<A.lo))]
    rw [z,zero_mul]
    exact sq_nonneg _

/-- Any nonempty finite list of rank classes, each with an arbitrary count interval. -/
def rectangle (first : Segment) (rest : List Segment) : Box :=
  rest.foldl (fun acc c => acc.mul c.box) first.box

/-- A finite-sampling rectangle has a contiguous positive support. -/
theorem Box.mass_pos_iff (A : Box) (k : ℕ) : 0<A.mass k ↔ A.lo≤k ∧ k≤A.hi := by
  by_cases h : A.lo≤k ∧ k≤A.hi
  · have den : 0<(A.size.choose k:ℚ) := by exact_mod_cast Nat.choose_pos (h.2.trans A.fits)
    exact iff_of_true (div_pos (A.support.pos k h.1 h.2) den) h
  · simp only [Box.mass,A.support.out k (by omega),zero_div,lt_self_iff_false,false_iff]
    exact h

end
end BandRect

namespace FourRankBump
open Finset Polynomial BandRect
noncomputable section

/-- A formal sum that counts labelled objects according to their integer sizes. -/
private def inventory {α : Type*} (S : Finset α) (w : α→ℕ) : Poly := ∑ h∈S,X^(w h)

private theorem inventory_coeff {α : Type*} (S : Finset α) (w : α→ℕ) (k : ℕ) :
    (inventory S w).coeff k=((S.filter (fun h=>w h=k)).card:ℚ) := by
  simp [inventory,coeff_X_pow,Finset.sum_boole,eq_comm]

private theorem inventory_prod {α β : Type*} (S : Finset α) (T : Finset β) (w : α→ℕ) (v : β→ℕ) :
    inventory S w*inventory T v=inventory (S×ˢ T) (fun h=>w h.1+v h.2) := by
  simp only [inventory,Finset.sum_mul,Finset.mul_sum,Finset.sum_product,pow_add]
  rw [Finset.sum_comm]

/-- Choices from one rank are subsets of its distinguishable cards. -/
def choices (c : Segment) : Finset (Finset (Fin c.size)) :=
  (univ : Finset (Fin c.size)).powerset.filter fun H=>c.lo≤H.card ∧ H.card≤c.hi

private theorem choices_poly (c : Segment) : inventory (choices c) Finset.card=c.poly := by
  ext k
  rw [inventory_coeff,coeff_interval]
  by_cases h : c.lo≤k ∧ k≤c.hi
  · have eq : (choices c).filter (fun H=>H.card=k)=(univ : Finset (Fin c.size)).powersetCard k := by
      ext H
      simp [choices]
      omega
    rw [if_pos h,eq,Finset.card_powersetCard]
    simp
  · have eq : (choices c).filter (fun H=>H.card=k)=∅ := by
      ext H
      simp [choices]
      omega
    simp [eq,h]

abbrev Hands (a b c d : ℕ) :=
  ((Finset (Fin a) × Finset (Fin b)) × Finset (Fin c)) × Finset (Fin d)

def countCards {a b c d : ℕ} (H : Hands a b c d) : ℕ :=
  H.1.1.1.card+H.1.1.2.card+H.1.2.card+H.2.card

private def hands4 (a b c d : Segment) (t : ℕ) : Finset (Hands a.size b.size c.size d.size) :=
  ((((choices a×ˢ choices b)×ˢ choices c)×ˢ choices d)).filter (fun H=>countCards H=t)

private def rect4 (a b c d : Segment) : Box := ((a.box.mul b.box).mul c.box).mul d.box

private theorem count4 (a b c d : Segment) (t : ℕ) : ((hands4 a b c d t).card:ℚ)=
    (rect4 a b c d).poly.coeff t := by
  change _=(a.poly*b.poly*c.poly*d.poly).coeff t
  rw [←choices_poly a,←choices_poly b,←choices_poly c,←choices_poly d,
    inventory_prod,inventory_prod,inventory_prod,inventory_coeff]
  rfl

/-- Four equally populous ranks and the nondegenerate parameters of Levin's game. -/
structure Game where
  s : ℕ
  l : ℕ
  u : ℕ
  low_pos : 0<l
  ordered : l≤u
  room : u<s

private def marked (g : Game) : Segment := ⟨g.s-1,g.u,g.u,le_rfl,by have := g.room;omega⟩
private def cap (g : Game) : Segment := ⟨g.s,0,g.u,Nat.zero_le _,g.room.le⟩
private def high (g : Game) : Segment := ⟨g.s,g.l,g.u,g.ordered,g.room.le⟩
private def low (g : Game) : Segment := ⟨g.s,0,g.l-1,Nat.zero_le _,by have := g.room;have := g.ordered;omega⟩

private def full (g : Game) := rect4 (marked g) (cap g) (cap g) (cap g)
private def allHigh (g : Game) := rect4 (marked g) (high g) (high g) (high g)
private def mixed (g : Game) := rect4 (marked g) (low g) (cap g) (high g)
private def allLow (g : Game) := rect4 (marked g) (low g) (low g) (low g)

private theorem split_interval (g : Game) : (cap g).poly=(low g).poly+(high g).poly := by
  ext i
  simp only [coeff_interval,coeff_add,cap,low,high]
  have p := g.low_pos
  have r := g.ordered
  split_ifs <;> first | omega | ring

/-- From the labelled remaining deck all three unmarked counts are capped and some is low. -/
def bumpHands (g : Game) (t : ℕ) : Finset (Hands (g.s-1) g.s g.s g.s) :=
  hands4 (marked g) (cap g) (cap g) (cap g) t \ hands4 (marked g) (high g) (high g) (high g) t

private theorem hands_mem (g : Game) (t : ℕ) (H : Hands (g.s-1) g.s g.s g.s) :
    H∈bumpHands g t ↔ countCards H=t ∧ H.1.1.1.card=g.u ∧ H.1.1.2.card≤g.u ∧ H.1.2.card≤g.u ∧
    H.2.card≤g.u ∧ (H.1.1.2.card<g.l ∨ H.1.2.card<g.l ∨ H.2.card<g.l) := by
  simp [bumpHands,hands4,choices,marked,cap,high,Finset.mem_product]
  omega

private theorem bump_count (g : Game) (t : ℕ) : ((bumpHands g t).card:ℚ) =
    (full g).poly.coeff t-(allHigh g).poly.coeff t := by
  unfold bumpHands
  have sub : hands4 (marked g) (high g) (high g) (high g) t⊆
      hands4 (marked g) (cap g) (cap g) (cap g) t := by
    intro H
    simp [hands4,choices,marked,cap,high,Finset.mem_product]
    omega
  rw [Finset.card_sdiff_of_subset sub,Nat.cast_sub (Finset.card_le_card sub),count4,count4]
  rfl

private theorem cubic_count (g : Game) (t : ℕ) : ((bumpHands g t).card:ℚ)=
    3*(mixed g).poly.coeff t+(allLow g).poly.coeff t := by
  have identity : (full g).poly-(allHigh g).poly=C (3:ℚ)*(mixed g).poly+(allLow g).poly := by
    change (marked g).poly*(cap g).poly*(cap g).poly*(cap g).poly-
        (marked g).poly*(high g).poly*(high g).poly*(high g).poly =
      C (3:ℚ)*((marked g).poly*(low g).poly*(cap g).poly*(high g).poly)+
        (marked g).poly*(low g).poly*(low g).poly*(low g).poly
    rw [split_interval,show C (3:ℚ)=(3:Poly) from Polynomial.C_eq_natCast 3]
    ring
  rw [bump_count,←coeff_sub,identity,coeff_add,coeff_C_mul]

/-- Mass at positive draw `t+1` after fixing the label of that draw. -/
private def priorMass (g : Game) (t : ℕ) : ℚ :=
  ((bumpHands g t).card:ℚ)/((4*g.s-1).choose t:ℚ)

/-- Bump probability by draw number, using actual labelled subsets for favorable outcomes. -/
def bumpProbability (g : Game) : ℕ→ℚ
  | 0 => 0
  | n+1 => priorMass g n

private theorem size_eq (g : Game) : (marked g).size+(cap g).size+(cap g).size+(cap g).size=4*g.s-1 := by
  change g.s-1+g.s+g.s+g.s=4*g.s-1
  have := g.room
  omega

private theorem lower_full (g : Game) (t : ℕ) : priorMass g t≤(full g).mass t := by
  have pos := (allHigh g).support.nn t
  unfold priorMass Box.mass
  rw [show (full g).size=4*g.s-1 from size_eq g,bump_count]
  apply div_le_div_of_nonneg_right (by linarith) (by positivity)

private theorem tight_full (g : Game) (t : ℕ) (ht : t<g.u+3*g.l) : priorMass g t=(full g).mass t := by
  have z := (allHigh g).support.out t (Or.inl (show t<(allHigh g).lo by
    change t<g.u+g.l+g.l+g.l;omega))
  unfold priorMass Box.mass
  rw [show (full g).size=4*g.s-1 from size_eq g,bump_count,z,sub_zero]

private theorem tight_mixed (g : Game) (t : ℕ) (ht : g.u+3*(g.l-1)<t) :
    priorMass g t=3*(mixed g).mass t := by
  have z := (allLow g).support.out t (Or.inr (show (allLow g).hi<t by
    change g.u+(g.l-1)+(g.l-1)+(g.l-1)<t;omega))
  unfold priorMass Box.mass
  rw [show (mixed g).size=4*g.s-1 from size_eq g,cubic_count,z,add_zero,mul_div_assoc]

/-- Levin's bump-side log-concavity conjecture for the four-rank model. -/
theorem four_ranks_bump_log_concave (g : Game) (n : ℕ) :
    bumpProbability g n*bumpProbability g (n+2)≤(bumpProbability g (n+1))^2 := by
  cases n with
  | zero =>
    change 0*_≤_^2
    rw [zero_mul]
    exact sq_nonneg _
  | succ t =>
    change priorMass g t*priorMass g (t+2)≤(priorMass g (t+1))^2
    by_cases early : t+1<g.u+3*g.l
    · rw [tight_full g (t+1) early]
      have n1 : 0≤priorMass g (t+2) := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      have n2 : 0≤(full g).mass t := div_nonneg ((full g).support.nn t) (by positivity)
      exact (mul_le_mul (lower_full g t) (lower_full g (t+2)) n1 n2).trans ((full g).log_concave t)
    · have p := g.low_pos
      rw [tight_mixed g t (by omega),tight_mixed g (t+2) (by omega),tight_mixed g (t+1) (by omega)]
      linarith only [(mixed g).log_concave t]

/-- The support of the four-rank bump event is exactly the full possible interval. -/
theorem four_ranks_support (g : Game) (n : ℕ) : 0<bumpProbability g n ↔ g.u+1≤n ∧ n≤3*g.u+g.l := by
  cases n with
  | zero =>
    simp only [bumpProbability,lt_self_iff_false,false_iff]
    omega
  | succ t =>
    change 0<priorMass g t ↔ _
    have lowpos := g.low_pos
    have ordered := g.ordered
    by_cases early : t<g.u+3*g.l
    · rw [tight_full g t early,Box.mass_pos_iff]
      change g.u+0+0+0≤t ∧ t≤g.u+g.u+g.u+g.u ↔ _
      omega
    · rw [tight_mixed g t (by omega),mul_pos_iff_of_pos_left (by norm_num),Box.mass_pos_iff]
      change g.u+0+0+g.l≤t ∧ t≤g.u+(g.l-1)+g.u+g.u ↔ _
      omega

/-- Rank names after distinguishing the rank of the last drawn card. -/
inductive Rank where | marked | a | b | c
  deriving DecidableEq

/-- All cumulative rank counts have entered the permitted band. -/
def inBand (g : Game) (w : List Rank) : Prop :=
  g.l≤w.count .marked ∧ w.count .marked≤g.u ∧ g.l≤w.count .a ∧ w.count .a≤g.u ∧
  g.l≤w.count .b ∧ w.count .b≤g.u ∧ g.l≤w.count .c ∧ w.count .c≤g.u

/-- Some rank has exceeded its allowed tally. -/
def hasBump (g : Game) (w : List Rank) : Prop :=
  g.u<w.count .marked ∨ g.u<w.count .a ∨ g.u<w.count .b ∨ g.u<w.count .c

/-- The last marked card triggers the bump, and each earlier prefix avoided both terminal events. -/
def firstBump (g : Game) (w : List Rank) : Prop :=
  hasBump g (w++[.marked]) ∧ ∀ v, v.IsPrefix w → ¬inBand g v ∧ ¬hasBump g v

private theorem first_iff (g : Game) (w : List Rank) : firstBump g w ↔
    w.count .marked=g.u ∧ w.count .a≤g.u ∧ w.count .b≤g.u ∧ w.count .c≤g.u ∧
    (w.count .a<g.l ∨ w.count .b<g.l ∨ w.count .c<g.l) := by
  have ordered := g.ordered
  have app : hasBump g (w++[.marked]) ↔ g.u<w.count .marked+1 ∨ g.u<w.count .a ∨
    g.u<w.count .b ∨ g.u<w.count .c := by simp [hasBump,List.count_append]
  constructor
  · rintro ⟨h,quiet⟩
    obtain ⟨noband,nobump⟩ := quiet w ⟨[],by simp⟩
    unfold inBand at noband
    unfold hasBump at nobump
    have fin := app.1 h
    omega
  · rintro ⟨hm,ha,hb,hc,low⟩
    refine ⟨app.2 (Or.inl (by omega)),?_⟩
    rintro v ⟨tail,r⟩
    have le (z : Rank) : v.count z≤w.count z := by rw [←r,List.count_append];omega
    have m := le .marked
    have a := le .a
    have b := le .b
    have c := le .c
    unfold inBand hasBump
    omega

/-- For every ordering of a labelled hand, the cardinality filter selects exactly first-bump paths. -/
theorem bump_hand_iff_first_bump (g : Game) (H : Hands (g.s-1) g.s g.s g.s) (w : List Rank)
    (hm : w.count .marked=H.1.1.1.card) (ha : w.count .a=H.1.1.2.card)
    (hb : w.count .b=H.1.2.card) (hc : w.count .c=H.2.card) :
    H∈bumpHands g (countCards H) ↔ firstBump g w := by
  simp only [hands_mem,first_iff,hm,ha,hb,hc,true_and]

#print axioms BandRect.Box.log_concave
#print axioms four_ranks_bump_log_concave
#print axioms four_ranks_support
#print axioms bump_hand_iff_first_bump
end
end FourRankBump

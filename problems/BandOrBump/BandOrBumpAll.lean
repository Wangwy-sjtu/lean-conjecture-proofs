import Mathlib.Logic.Equiv.Fin.Basic
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

theorem coeffZ_shift (P : Poly) (d : ℕ) (z : ℤ) : coeffZ (X^d*P) z=coeffZ P (z-d) := by
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

theorem choose_step (s i : ℕ) (hi : i≤s) :
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

theorem lr_mul {A B C : Poly} (h : LR A B) (lc : TP C) : LR (A*C) (B*C) := by
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

theorem lr_add_right {P A B : Poly} (a : LR P A) (b : LR P B) : LR P (A+B) := by
  intro i j ij
  simp only [coeff_add]
  linarith only [a i j ij,b i j ij]

theorem lr_add_left {P A B : Poly} (a : LR A P) (b : LR B P) : LR (A+B) P := by
  intro i j ij
  simp only [coeff_add]
  linarith only [a i j ij,b i j ij]

def NN (P : Poly) := ∀i,0≤P.coeff i

theorem nn_mul {P Q : Poly} (p : NN P) (q : NN Q) : NN (P*Q) := by
  intro k
  rw [coeff_mul]
  exact Finset.sum_nonneg (fun i _=>mul_nonneg (p i.1) (q i.2))

theorem nn_add {P Q : Poly} (p : NN P) (q : NN Q) : NN (P+Q) :=
  fun k=>by rw [coeff_add];exact add_nonneg (p k) (q k)

theorem coeff_bound_mul {A B P : Poly} {c : ℚ} (h : ∀i,A.coeff i≤c*B.coeff i)
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

def face (P : Poly) (r : ℕ) (v : ℚ) : Poly := monomial r (v*P.coeff r)

@[simp] theorem coeff_face (P : Poly) (r i : ℕ) (v : ℚ) :
    (face P r v).coeff i=if i=r then v*P.coeff i else 0 := by
  by_cases h : i=r
  · simp [face,h]
  · simp [face,Polynomial.coeff_monomial,h,Ne.symm h]

private theorem euler (P : Poly) (k : ℕ) : (X*P.derivative).coeff k=(k:ℚ)*P.coeff k := by
  cases k with
  | zero => simp
  | succ k => simp [Polynomial.coeff_derivative,mul_comm]

theorem formal_step (P L H : Poly) (S k : ℕ) :
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

theorem move (A : Box) (k : ℕ) :
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

namespace BandAll
open BandRect Polynomial Finset
noncomputable section

/-- Likelihood-ratio order is transitive through a nonzero, nonnegative middle sequence. -/
private theorem lr_trans {A B C : Poly} (hb : ∃k,0<B.coeff k) (ha : NN A) (hn : NN B) (hc : NN C)
    (ab : LR A B) (bc : LR B C) : LR A C := by
  intro i j ij
  by_cases h : 0<C.coeff i ∧ 0<A.coeff j
  · obtain ⟨t,pt⟩ := hb
    have bb : 0<B.coeff i ∧ 0<B.coeff j := by
      by_cases tj : t≤j
      · have q := (mul_pos pt h.2).trans_le (ab t j tj)
        have z : 0<B.coeff j := pos_of_mul_pos_right q (ha _)
        exact ⟨pos_of_mul_pos_left ((mul_pos h.1 z).trans_le (bc i j ij)) (hc _),z⟩
      · have q := (mul_pos h.1 pt).trans_le (bc i t (by omega))
        have z : 0<B.coeff i := pos_of_mul_pos_left q (hc _)
        exact ⟨z,pos_of_mul_pos_right ((mul_pos z h.2).trans_le (ab i j ij)) (ha _)⟩
    apply le_of_mul_le_mul_right (a:=B.coeff i*B.coeff j) _ (mul_pos bb.1 bb.2)
    have z := mul_le_mul (ab i j ij) (bc i j ij) (mul_nonneg (hc _) (hn _)) (mul_nonneg (ha _) (hn _))
    linarith only [z]
  · have z : C.coeff i=0 ∨ A.coeff j=0 := by
      by_cases ci : C.coeff i=0
      · exact Or.inl ci
      · exact Or.inr (le_antisymm (le_of_not_gt (fun q=>h ⟨lt_of_le_of_ne (hc i) (Ne.symm ci),q⟩)) (ha _))
    rcases z with z|z <;> rw [z] <;> simpa using mul_nonneg (ha i) (hc j)

private theorem positive_nonempty {P : Poly} {l u : ℕ} (h : PositiveRange P l u) (v : l≤u) : ∃k,0<P.coeff k :=
  ⟨l,h.pos l le_rfl v⟩

private theorem lr_scalar_right {P Q : Poly} (c : ℚ) (nn : 0≤c) (h : LR P Q) : LR P (C c*Q) := by
  intro i j ij
  simp only [coeff_C_mul]
  linarith only [mul_le_mul_of_nonneg_left (h i j ij) nn]

private theorem scalar_nn {P : Poly} (c : ℚ) (nn : 0≤c) (h : NN P) : NN (C c*P) :=
  fun k=>by rw [coeff_C_mul];exact mul_nonneg nn (h k)

private def spike (d : ℕ) : Segment := ⟨d,d,d,le_rfl,le_rfl⟩

private theorem spike_eq (d : ℕ) : (spike d).poly=X^d := by
  ext i
  simp [coeff_interval,spike,Polynomial.coeff_X_pow]
  split_ifs <;> first | omega | simp_all

private theorem spike_tp (d : ℕ) : TP ((X:Poly)^d) := spike_eq d ▸ tp_interval (spike d)
private theorem spike_pos (d : ℕ) : PositiveRange ((X:Poly)^d) d d := spike_eq d ▸ positive_interval (spike d)

private theorem lr_ceiling {P : Poly} {l u : ℕ} (v : PositiveRange P l u) : LR P (X^u) := by
  intro i j ij
  simp only [Polynomial.coeff_X_pow]
  by_cases e : i=u
  · by_cases ej : j=u
    · simp [e,ej]
    · simp [e,ej,v.out j (Or.inr (by omega))]
  · simp [e]
    split <;> simp [v.nn]

private theorem tp_step_from_boundary (P B : Poly) (S U : ℕ) (hp : PositiveRange P 0 U)
    (order : LR P B)
    (moves : ∀ k : ℕ,((k:ℚ)+1)*P.coeff (k+1)=((S:ℚ)-k)*P.coeff k-B.coeff k) : TP P := by
  have nn (t : ℤ) : 0≤coeffZ P t := by unfold coeffZ;split <;> first | exact hp.nn _ | rfl
  have out (t : ℤ) (h : t<0 ∨ (U:ℤ)<t) : coeffZ P t=0 := by
    unfold coeffZ
    split
    · exact hp.out _ (Or.inr (by omega))
    · rfl
  have inner (t : ℤ) (lo : 0≤t) (hi : t≤U) : 0<coeffZ P t := by
    rw [coeffZ,if_pos lo]
    exact hp.pos _ (Nat.zero_le _) (by omega)
  have one (i j : ℤ) (ij : i≤j) : coeffZ P i*coeffZ P (j+1)≤coeffZ P (i+1)*coeffZ P j := by
    by_cases h : 0≤i ∧ j+1≤U
    · let l := i.toNat
      let r := j.toNat
      have li : (l:ℤ)=i := by dsimp [l];omega
      have rj : (r:ℤ)=j := by dsimp [r];omega
      rw [←li,←rj,←Nat.cast_one,←Nat.cast_add,←Nat.cast_add]
      simp only [coeffZ_nat]
      have p := hp.pos l (Nat.zero_le _) (by omega)
      have q := hp.pos r (Nat.zero_le _) (by omega)
      have z (k : ℕ) (pk : 0<P.coeff k) : P.coeff (k+1)/P.coeff k=
          ((S:ℚ)-k-B.coeff k/P.coeff k)/(k+1) := by
        field_simp [pk.ne']
        linarith only [moves k]
      have e : B.coeff l/P.coeff l ≤ B.coeff r/P.coeff r := (div_le_div_iff₀ p q).2 (by linarith only [order l r (by omega)])
      have posnum : 0≤(S:ℚ)-l-B.coeff l/P.coeff l := by
        have p1 := mul_nonneg (show (0:ℚ)≤l+1 by positivity) (hp.nn (l+1))
        have bd : B.coeff l/P.coeff l≤(S:ℚ)-l := (div_le_iff₀ p).2 (by linarith only [p1,moves l])
        linarith
      have le : (l:ℚ)≤r := by exact_mod_cast (by omega : l≤r)
      have cmp : P.coeff (r+1)/P.coeff r≤P.coeff (l+1)/P.coeff l := by
        rw [z r q,z l p]
        apply div_le_div₀ posnum (by linarith only [le,e]) (by positivity) (by linarith)
      linarith only [(div_le_div_iff₀ q p).1 cmp]
    · have z : coeffZ P i=0 ∨ coeffZ P (j+1)=0 := by
        by_cases hi : i<0
        · exact Or.inl (out _ (Or.inl hi))
        · exact Or.inr (out _ (Or.inr (by omega)))
      rcases z with z|z <;> rw [z] <;> simpa using mul_nonneg (nn (i+1)) (nn j)
  intro i j d ij
  induction d with
  | zero => simp
  | succ d ih =>
    push_cast
    by_cases h : 0≤i ∧ j+(d+1)≤U
    · have wp := inner (i+d) (by omega) (by omega)
      have add (x : ℤ) : x+(d+1)=x+d+1 := by omega
      rw [add,add]
      apply le_of_mul_le_mul_right (a:=coeffZ P (i+d)) _ wp
      have x := mul_le_mul_of_nonneg_left (one (i+d) (j+d) (by omega)) (nn i)
      have y := mul_le_mul_of_nonneg_right ih (nn (i+d+1))
      linarith only [x,y]
    · have z : coeffZ P i=0 ∨ coeffZ P (j+(d+1))=0 := by
        by_cases hi : i<0
        · exact Or.inl (out _ (Or.inl hi))
        · exact Or.inr (out _ (Or.inr (by omega)))
      rcases z with z|z <;> rw [z] <;> simpa using mul_nonneg (nn (i+(d+1))) (nn j)

private theorem tensor (A B C D : Box) (a : LR A.poly B.poly) (b : LR C.poly D.poly) :
    LR (A.poly*C.poly) (B.poly*D.poly) := by
  have x := lr_mul a C.tp
  have y : LR (B.poly*C.poly) (B.poly*D.poly) := by simpa only [mul_comm] using lr_mul b B.tp
  exact lr_trans (positive_nonempty (B.mul C).support (B.mul C).valid)
    (A.mul C).support.nn (B.mul C).support.nn (B.mul D).support.nn x y

private def power (A : Box) : ℕ→Box
  | 0 => (spike 0).box
  | n+1 => (power A n).mul A

@[simp] private theorem power_poly (A : Box) (n : ℕ) : (power A n).poly=A.poly^n := by
  induction n with
  | zero => change (spike 0).poly=_;simp [spike_eq]
  | succ n ih => change (power A n).poly*A.poly=_;rw [ih,pow_succ]

@[simp] private theorem power_hi (A : Box) (n : ℕ) : (power A n).hi=n*A.hi := by
  induction n with
  | zero => simp [power,spike,Segment.box]
  | succ n ih => change (power A n).hi+A.hi=_;rw [ih,Nat.succ_mul]

@[simp] private theorem power_lo (A : Box) (n : ℕ) : (power A n).lo=n*A.lo := by
  induction n with
  | zero => simp [power,spike,Segment.box]
  | succ n ih => change (power A n).lo+A.lo=_;rw [ih,Nat.succ_mul]

/-- Equal rank sizes and the two stopping thresholds of Levin's game. -/
structure Game where
  s : ℕ
  l : ℕ
  u : ℕ
  low_pos : 0<l
  ordered : l≤u
  room : u<s

private def cap (g : Game) : Segment := ⟨g.s,0,g.u,Nat.zero_le _,g.room.le⟩
private def high (g : Game) : Segment := ⟨g.s,g.l,g.u,g.ordered,g.room.le⟩
private def low (g : Game) : Segment := ⟨g.s,0,g.l-1,Nat.zero_le _,by have := g.ordered;have := g.room;omega⟩
private def marked (g : Game) : Segment := ⟨g.s-1,g.u,g.u,le_rfl,by have := g.room;omega⟩
private def delta (g : Game) := g.u-(g.l-1)

private abbrev F (g : Game) := (cap g).poly
private abbrev G (g : Game) := (high g).poly
private abbrev L (g : Game) := (low g).poly

private theorem split_interval (g : Game) : F g=L g+G g := by
  ext i
  simp only [F,L,G,coeff_interval,coeff_add,cap,low,high]
  have p := g.low_pos
  have r := g.ordered
  split_ifs <;> first | omega | ring

private theorem cap_high_lr (g : Game) : LR (F g) (G g) := by
  intro i j ij
  have pick (k : ℕ) : (G g).coeff k=if g.l≤k then (F g).coeff k else 0 := by
    by_cases lk : g.l≤k <;> simp [G,F,high,cap,lk]
  rw [pick i,pick j]
  by_cases li : g.l≤i
  · rw [if_pos li,if_pos (li.trans ij)]
  · rw [if_neg li,zero_mul]
    by_cases lj : g.l≤j
    · rw [if_pos lj]
      exact mul_nonneg ((positive_interval (cap g)).nn i) ((positive_interval (cap g)).nn j)
    · rw [if_neg lj,mul_zero]

private theorem shift_low_lr (g : Game) : LR (F g) (X^(delta g)*L g) := by
  intro i j ij
  have p := g.low_pos
  have r := g.ordered
  have e : g.l-1+delta g=g.u := by unfold delta;omega
  by_cases h : delta g≤i ∧ j≤g.u
  · have z := tp_interval (cap g) ((i:ℤ)-delta g) ((j:ℤ)-delta g) (delta g) (by omega)
    rw [sub_add_cancel,sub_add_cancel,←Nat.cast_sub h.1,←Nat.cast_sub (by omega : delta g≤j)] at z
    simp only [coeffZ_nat] at z
    rw [coeff_X_pow_mul',coeff_X_pow_mul',if_pos h.1,if_pos (by omega : delta g≤j)]
    have eq (k : ℕ) (le : k≤g.l-1) : (L g).coeff k=(F g).coeff k := by
      simp [L,F,coeff_interval,low,cap,le,show k≤g.u by omega]
    rw [eq _ (by omega),eq _ (by omega)]
    linarith only [z]
  · by_cases hi : i<delta g
    · rw [coeff_X_pow_mul',if_neg (by omega),zero_mul]
      exact mul_nonneg ((positive_interval (cap g)).nn i)
        (nn_mul (spike_pos (delta g)).nn (positive_interval (low g)).nn j)
    · rw [(positive_interval (cap g)).out j (Or.inr (by change g.u<j;omega)),mul_zero]
      exact mul_nonneg ((positive_interval (cap g)).nn i)
        (nn_mul (spike_pos (delta g)).nn (positive_interval (low g)).nn j)

/-- Unnormalized mass with at least one of the `h` ranks below the band. -/
def missing (g : Game) (h : ℕ) := (F g)^h-(G g)^h

private theorem decompositions (g : Game) (h : ℕ) :
    missing g (h+1)=L g*(F g)^h+G g*missing g h ∧
    missing g (h+1)=F g*missing g h+L g*(G g)^h := by
  unfold missing
  rw [split_interval]
  simp only [pow_succ]
  constructor <;> ring

private def riseCost (g : Game) : ℚ := ((g.s:ℚ)-g.u)*(g.s.choose g.u:ℚ)
private def completeCost (g : Game) : ℚ := (g.l:ℚ)*(g.s.choose g.l:ℚ)

private theorem cutoff_poly (g : Game) : (cap g).box.low=0 ∧
    (cap g).box.high=C (riseCost g)*X^g.u ∧ (high g).box.high=C (riseCost g)*X^g.u ∧
    (high g).box.low=X*(C (completeCost g)*X^(g.l-1)) := by
  have ord := g.ordered
  have p := g.low_pos
  have e : g.l-1+1=g.l := by omega
  change face (F g) 0 0=0 ∧ face (F g) g.u ((g.s:ℚ)-g.u)=_ ∧
    face (G g) g.u ((g.s:ℚ)-g.u)=_ ∧ face (G g) g.l (g.l:ℚ)=_
  simp [face,F,G,cap,high,ord,riseCost,completeCost,←Polynomial.C_mul_X_pow_eq_monomial]
  rw [show (X:Poly)^g.l=X^(g.l-1)*X by rw [←pow_succ,e]]
  ring

/-- Upward failures come from a capped rank or from filling the last deficient rank. -/
private def boundary (g : Game) (h : ℕ) : Poly :=
  C ((h+1:ℕ)*riseCost g)*(X^g.u*missing g h)+
  C ((h+1:ℕ)*completeCost g)*(X^(g.l-1)*(G g)^h)

private theorem moves_missing (g : Game) (h : ℕ) :
    X*(1+X)*(missing g (h+1)).derivative-C (((h+1)*g.s:ℕ):ℚ)*X*missing g (h+1)=
    0-X*boundary g h := by
  obtain ⟨l,f,b,glo⟩ := cutoff_poly g
  have fm := (cap g).box.moves
  have gm := (high g).box.moves
  rw [l,f] at fm
  rw [b,glo] at gm
  change X*(1+X)*(F g).derivative-C (g.s:ℚ)*X*F g=0-X*(C (riseCost g)*X^g.u) at fm
  change X*(1+X)*(G g).derivative-C (g.s:ℚ)*X*G g=
    X*(C (completeCost g)*X^(g.l-1))-X*(C (riseCost g)*X^g.u) at gm
  unfold missing boundary
  simp only [derivative_sub,derivative_pow,add_tsub_cancel_right,missing,Nat.cast_mul,
    Nat.cast_add,Nat.cast_one,map_mul,map_add,map_one]
  rw [pow_succ (F g) h,pow_succ (G g) h]
  linear_combination (C (h:ℚ)+1)*(F g)^h*fm-(C (h:ℚ)+1)*(G g)^h*gm

/-- The induction certificate for `r+1` nontrigger ranks. -/
private structure State (g : Game) (r : ℕ) where
  box : Box
  poly_eq : box.poly=missing g (r+1)
  size_eq : box.size=(r+1)*g.s
  lo_eq : box.lo=0
  hi_eq : box.hi=r*g.u+(g.l-1)
  last_lr : LR box.poly (X^(g.l-1)*(G g)^r)
  shift_lr : LR ((F g)^(r+1)) (X^(delta g)*box.poly)

private def firstState (g : Game) : State g 0 where
  box := (low g).box
  poly_eq := by change L g=missing g 1;simp [missing,split_interval]
  size_eq := by change g.s=(0+1)*g.s;simp
  lo_eq := rfl
  hi_eq := by change g.l-1=0*g.u+(g.l-1);simp
  last_lr := by simpa using lr_ceiling (positive_interval (low g))
  shift_lr := by simpa using shift_low_lr g

private theorem add_support {A B : Poly} {l u : ℕ} (a : PositiveRange A 0 u) (b : PositiveRange B l u) :
    PositiveRange (A+B) 0 u := by
  refine ⟨nn_add a.nn b.nn,?_,?_⟩
  · intro i lo hi
    rw [coeff_add]
    linarith only [a.pos i lo hi,b.nn i]
  · intro i h
    rw [coeff_add,a.out i h,b.out i (by omega),zero_add]

private theorem next_support (g : Game) (r : ℕ) (st : State g r) :
    PositiveRange (missing g (r+2)) 0 ((r+1)*g.u+(g.l-1)) := by
  have x := ((low g).box.mul (power (cap g).box (r+1))).support
  have y := ((high g).box.mul st.box).support
  rw [(decompositions g (r+1)).1,←st.poly_eq]
  apply add_support (l:=g.l)
  · change PositiveRange ((L g)*(power (cap g).box (r+1)).poly)
      (0+(power (cap g).box (r+1)).lo) ((g.l-1)+(power (cap g).box (r+1)).hi) at x
    simpa only [power_poly,power_lo,power_hi,show (cap g).box.hi=g.u from rfl,
      show (cap g).box.lo=0 from rfl,Nat.mul_zero,Nat.zero_add,Nat.add_comm] using x
  · change PositiveRange ((G g)*st.box.poly) (g.l+st.box.lo) (g.u+st.box.hi) at y
    rw [st.lo_eq,st.hi_eq,Nat.add_zero] at y
    convert y using 1
    rw [Nat.add_mul,one_mul]
    omega

private theorem next_last (g : Game) (r : ℕ) (st : State g r) :
    LR (missing g (r+2)) (X^(g.l-1)*(G g)^(r+1)) := by
  rw [(decompositions g (r+1)).2,←st.poly_eq]
  apply lr_add_left
  · have cmp := tensor (cap g).box (high g).box st.box
      ((spike (g.l-1)).box.mul (power (high g).box r)) (cap_high_lr g)
      (by simpa only [Box.mul,Segment.box,spike_eq,power_poly] using st.last_lr)
    change LR (F g*st.box.poly) (G g*((spike (g.l-1)).poly*(power (high g).box r).poly)) at cmp
    rw [spike_eq,power_poly] at cmp
    convert cmp using 1
    change _=G g*(X^(g.l-1)*(G g)^r)
    rw [pow_succ]
    ring
  · have cmp := lr_mul (lr_ceiling (positive_interval (low g))) (power (high g).box (r+1)).tp
    simpa only [power_poly] using cmp

private theorem next_shift (g : Game) (r : ℕ) (st : State g r) :
    LR ((F g)^(r+2)) (X^(delta g)*missing g (r+2)) := by
  rw [(decompositions g (r+1)).1,←st.poly_eq,mul_add]
  apply lr_add_right
  · have cmp := lr_mul (shift_low_lr g) (power (cap g).box (r+1)).tp
    rw [power_poly] at cmp
    convert cmp using 1
    · change (F g)^(r+1+1)=F g*(F g)^(r+1)
      rw [pow_succ,mul_comm]
    · change X^(delta g)*(L g*(F g)^(r+1))=X^(delta g)*L g*(F g)^(r+1)
      ring
  · have cmp := tensor (cap g).box (high g).box (power (cap g).box (r+1))
      ((spike (delta g)).box.mul st.box) (cap_high_lr g)
      (by simpa only [Box.mul,Segment.box,spike_eq,power_poly] using st.shift_lr)
    change LR (F g*(power (cap g).box (r+1)).poly) (G g*((spike (delta g)).poly*st.box.poly)) at cmp
    rw [spike_eq,power_poly] at cmp
    convert cmp using 1
    · change (F g)^(r+1+1)=F g*(F g)^(r+1)
      rw [pow_succ,mul_comm]
    · ring

private theorem next_ceiling (g : Game) (r : ℕ) (st : State g r) :
    LR (missing g (r+2)) (X^g.u*st.box.poly) := by
  rw [(decompositions g (r+1)).1,←st.poly_eq]
  apply lr_add_left
  · have cmp := tensor (low g).box (spike (g.l-1)).box (power (cap g).box (r+1))
      ((spike (delta g)).box.mul st.box)
      (by simpa only [Segment.box,spike_eq] using lr_ceiling (positive_interval (low g)))
      (by simpa only [Box.mul,Segment.box,spike_eq,power_poly] using st.shift_lr)
    change LR (L g*(power (cap g).box (r+1)).poly)
      ((spike (g.l-1)).poly*((spike (delta g)).poly*st.box.poly)) at cmp
    rw [spike_eq,spike_eq,power_poly,←mul_assoc,←pow_add,
      show g.l-1+delta g=g.u by unfold delta;have := g.ordered;omega] at cmp
    exact cmp
  · exact lr_mul (lr_ceiling (positive_interval (high g))) st.box.tp

private theorem rise_nn (g : Game) : 0≤riseCost g :=
  mul_nonneg (sub_nonneg.2 (by exact_mod_cast g.room.le)) (by positivity)

private theorem complete_nn (g : Game) : 0≤completeCost g := mul_nonneg (by positivity) (by positivity)

private def nextState (g : Game) (r : ℕ) (st : State g r) : State g (r+1) := by
  let h := r+1
  let A := missing g (h+1)
  let B := boundary g h
  have vs : 0≤h*g.u+(g.l-1) := Nat.zero_le _
  have overs : h*g.u+(g.l-1)≤(h+1)*g.s := by
    have hu := g.room.le
    have hl := g.ordered
    calc
      _ ≤ h*g.s+g.s := Nat.add_le_add (Nat.mul_le_mul_left h hu) (by omega)
      _ = _ := (Nat.succ_mul _ _).symm
  have sup : PositiveRange A 0 (h*g.u+(g.l-1)) := next_support g r st
  have last : LR A (X^(g.l-1)*(G g)^h) := next_last g r st
  have edge : LR A (X^g.u*missing g h) := by
    change LR (missing g (r+2)) (X^g.u*missing g (r+1))
    rw [←st.poly_eq]
    exact next_ceiling g r st
  have up : LR A B := lr_add_right
    (lr_scalar_right _ (mul_nonneg (Nat.cast_nonneg _) (rise_nn g)) edge)
    (lr_scalar_right _ (mul_nonneg (Nat.cast_nonneg _) (complete_nn g)) last)
  have nnF : NN B := by
    apply nn_add
    · apply scalar_nn _ (mul_nonneg (Nat.cast_nonneg _) (rise_nn g))
      apply nn_mul (spike_pos g.u).nn
      change NN (missing g (r+1))
      rw [←st.poly_eq]
      exact st.box.support.nn
    · apply scalar_nn _ (mul_nonneg (Nat.cast_nonneg _) (complete_nn g))
      apply nn_mul (spike_pos (g.l-1)).nn
      simpa only [power_poly] using (power (high g).box h).support.nn
  have equation : X*(1+X)*A.derivative-C (((h+1)*g.s:ℕ):ℚ)*X*A=0-X*B := moves_missing g h
  have step (k : ℕ) : ((k:ℚ)+1)*A.coeff (k+1)=(((h+1)*g.s:ℕ):ℚ)*A.coeff k-
      (k:ℚ)*A.coeff k-B.coeff k := by
    have z := formal_step A 0 B ((h+1)*g.s) k
    rw [equation,sub_self,coeff_zero,sub_zero] at z
    linarith only [z]
  let bs : Box := {
    poly := A, low := 0, high := B, size := (h+1)*g.s, lo := 0, hi := h*g.u+(g.l-1),
    valid := vs, fits := overs,
    support := sup,
    tp := tp_step_from_boundary A B _ _ sup up (fun k=>by linarith only [step k]),
    lowNN := fun _=>by simp, highNN := nnF,
    lower := fun i j _=>by simp, upper := up,
    bound := fun _=>by simp, moves := equation }
  exact ⟨bs,rfl,rfl,rfl,rfl,last,next_shift g r st⟩

private def state (g : Game) : (r : ℕ)→State g r
  | 0 => firstState g
  | r+1 => nextState g r (state g r)

/-- Coefficients for capped ranks with at least one deficient rank are ultra-log-concave. -/
theorem missing_log_concave (g : Game) (h k : ℕ) :
    ((missing g (h+1)).coeff k/(((h+1)*g.s).choose k:ℚ))*
      ((missing g (h+1)).coeff (k+2)/(((h+1)*g.s).choose (k+2):ℚ))≤
    ((missing g (h+1)).coeff (k+1)/(((h+1)*g.s).choose (k+1):ℚ))^2 := by
  have st := state g h
  simpa only [Box.mass,st.poly_eq,st.size_eq] using st.box.log_concave k

/-- A generating polynomial of finite labelled objects, sorted by integer size. -/
private def inventory {α : Type*} (S : Finset α) (w : α→ℕ) : Poly := ∑ h∈S,X^(w h)

private theorem inventory_coeff {α : Type*} (S : Finset α) (w : α→ℕ) (k : ℕ) :
    (inventory S w).coeff k=((S.filter (fun h=>w h=k)).card:ℚ) := by
  simp [inventory,coeff_X_pow,Finset.sum_boole,eq_comm]

private theorem inventory_prod {α β : Type*} (S : Finset α) (T : Finset β) (w : α→ℕ) (v : β→ℕ) :
    inventory S w*inventory T v=inventory (S×ˢ T) (fun h=>w h.1+v h.2) := by
  simp only [inventory,Finset.sum_mul,Finset.mul_sum,Finset.sum_product,pow_add]
  rw [Finset.sum_comm]

private def choices (c : Segment) : Finset (Finset (Fin c.size)) :=
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
  · have eq : (choices c).filter (fun H=>H.card=k)=∅ := by ext H;simp [choices];omega
    simp [eq,h]

private def consEmbedding (α : Type*) : α×List α ↪ List α where
  toFun p := p.1::p.2
  inj' := by rintro ⟨i,x⟩ ⟨j,y⟩ h;simpa using h

/-- Distinct positions of a list represent distinct ranks; each component is a labelled subset. -/
private def selections {α : Type*} [DecidableEq α] (S : Finset α) : ℕ→Finset (List α)
  | 0 => {[]}
  | h+1 => (S×ˢ selections S h).map (consEmbedding α)

private theorem selections_mem {α : Type*} [DecidableEq α] (S : Finset α) (h : ℕ) (v : List α) :
    v∈selections S h ↔ v.length=h ∧ ∀z∈v,z∈S := by
  induction h generalizing v with
  | zero => cases v <;> simp [selections]
  | succ h ih =>
    cases v with
    | nil => simp [selections,consEmbedding]
    | cons x xs => simp [selections,consEmbedding,ih,Finset.mem_product,and_assoc,and_left_comm,and_comm]

private def value {α : Type*} (w : α→ℕ) (v : List α) : ℕ := (v.map w).sum

private theorem selections_poly {α : Type*} [DecidableEq α] (S : Finset α) (w : α→ℕ) (h : ℕ) :
    inventory (selections S h) (value w)=(inventory S w)^h := by
  induction h with
  | zero => simp [selections,inventory,value]
  | succ h ih =>
    rw [pow_succ,mul_comm _ (inventory S w),←ih,inventory_prod]
    simp only [selections,inventory,Finset.sum_map,consEmbedding,Function.Embedding.coeFn_mk,
      value,List.map_cons,List.sum_cons]

/-- Labelled hand, with the last card's rank distinguished. -/
abbrev Hand (s : ℕ) := Finset (Fin (s-1)) × List (Finset (Fin s))

def countCards {s : ℕ} (H : Hand s) : ℕ := H.1.card+value Finset.card H.2

private def sample (g : Game) (a : Segment) (h t : ℕ) :
    Finset (Finset (Fin (g.s-1))×List (Finset (Fin a.size))) :=
  (choices (marked g)×ˢ selections (choices a) h).filter
    (fun H=>H.1.card+value Finset.card H.2=t)

private theorem sample_count (g : Game) (a : Segment) (h t : ℕ) :
    ((sample g a h t).card:ℚ)=((marked g).poly*a.poly^h).coeff t := by
  rw [←choices_poly (marked g),←choices_poly a,←selections_poly,inventory_prod,inventory_coeff]
  rfl

/-- Favorable hands on the `h` nondistinguished ranks, before the marked next card. -/
def bumpHands (g : Game) (h t : ℕ) : Finset (Hand g.s) :=
  sample g (cap g) h t \ sample g (high g) h t

private theorem sample_membership (g : Game) (h t : ℕ) (H : Hand g.s) :
    H∈bumpHands g h t ↔ H.2.length=h ∧ countCards H=t ∧ H.1.card=g.u ∧
    (∀K∈H.2,K.card≤g.u) ∧ ∃K∈H.2,K.card<g.l := by
  classical
  simp [bumpHands,sample,choices,marked,cap,high,Finset.mem_product,selections_mem,countCards]
  aesop (add unsafe (by omega))

private theorem hand_count (g : Game) (h t : ℕ) :
    ((bumpHands g h t).card:ℚ)=((marked g).poly*missing g h).coeff t := by
  have sub : sample g (high g) h t⊆sample g (cap g) h t := by
    intro H
    simp [sample,selections_mem,choices,marked,cap,high,Finset.mem_product]
    aesop
  rw [bumpHands,Finset.card_sdiff_of_subset sub,Nat.cast_sub (Finset.card_le_card sub),
    sample_count,sample_count,missing,mul_sub,coeff_sub]

/-- Exact joint probability at draw `n` for an `m`-rank deck. -/
def bumpProbability (g : Game) : ℕ→ℕ→ℚ
  | 0,_ => 0
  | _+1,0 => 0
  | h+1,t+1 => ((bumpHands g h t).card:ℚ)/(((h+1)*g.s-1).choose t:ℚ)

private theorem actual_mass (g : Game) (r t : ℕ) :
    bumpProbability g (r+2) (t+1)=((marked g).box.mul (state g r).box).mass t := by
  change ((bumpHands g (r+1) t).card:ℚ)/_=(((marked g).poly*(state g r).box.poly).coeff t)/
    (((g.s-1)+(state g r).box.size).choose t:ℚ)
  rw [hand_count,(state g r).poly_eq,(state g r).size_eq]
  rw [show g.s-1+(r+1)*g.s=(r+2)*g.s-1 by rw [show (r+2)*g.s=(r+1)*g.s+g.s from Nat.succ_mul (r+1) g.s];have := g.room;omega]

private theorem one_rank (g : Game) (n : ℕ) : bumpProbability g 1 n=0 := by
  cases n with
  | zero => rfl
  | succ n => change ((bumpHands g 0 n).card:ℚ)/_=0;simp [hand_count,missing]

/-- Levin's bump-side log-concavity conjecture for every number of ranks and every draw time. -/
theorem all_ranks_bump_log_concave (g : Game) (m n : ℕ) :
    bumpProbability g m n*bumpProbability g m (n+2)≤(bumpProbability g m (n+1))^2 := by
  cases m with
  | zero => simp [bumpProbability]
  | succ m =>
    cases m with
    | zero => simp [one_rank]
    | succ r =>
      cases n with
      | zero => change 0*_≤_^2;rw [zero_mul];exact sq_nonneg _
      | succ t =>
        change bumpProbability g (r+2) (t+1)*bumpProbability g (r+2) ((t+2)+1)≤
          (bumpProbability g (r+2) ((t+1)+1))^2
        simp only [actual_mass]
        exact ((marked g).box.mul (state g r).box).log_concave t

/-- The support is the entire feasible integer interval for every deck with at least two ranks. -/
theorem all_ranks_support (g : Game) (m n : ℕ) :
    0<bumpProbability g m n ↔ 2≤m ∧ g.u+1≤n ∧ n≤(m-1)*g.u+g.l := by
  cases m with
  | zero => simp [bumpProbability]
  | succ m =>
    cases m with
    | zero => simp [one_rank]
    | succ r =>
      cases n with
      | zero => simp [bumpProbability]
      | succ t =>
        rw [actual_mass g r t,Box.mass_pos_iff]
        change g.u+(state g r).box.lo≤t ∧ t≤g.u+(state g r).box.hi ↔ _
        rw [(state g r).hi_eq,(state g r).lo_eq]
        have p := g.low_pos
        simp only [Nat.succ_sub_one,Nat.succ_mul]
        omega

private def unrestricted (s : ℕ) : Segment := ⟨s,0,s,Nat.zero_le _,le_rfl⟩

private theorem unrestricted_poly (s : ℕ) : (unrestricted s).poly=(1+X)^s := by
  ext k
  rw [coeff_interval,coeff_one_add_X_pow]
  by_cases h : k≤s
  · simp [unrestricted,h]
  · simp [unrestricted,h,Nat.choose_eq_zero_of_lt (by omega : s<k)]

/-- The complete labelled underlying sample space, represented by one subset per rank. -/
def allHands (s h t : ℕ) : Finset (Hand s) :=
  (choices (unrestricted (s-1))×ˢ selections (choices (unrestricted s)) h).filter (fun H=>countCards H=t)

/-- The denominator in the probability is the size of the same labelled sample space. -/
theorem all_hands_card (g : Game) (h t : ℕ) : (allHands g.s h t).card=((h+1)*g.s-1).choose t := by
  have book := inventory_coeff (choices (unrestricted (g.s-1))×ˢ selections (choices (unrestricted g.s)) h)
    (fun H=>H.1.card+value Finset.card H.2) t
  rw [←inventory_prod,selections_poly,choices_poly,choices_poly,unrestricted_poly,unrestricted_poly,
    ←pow_mul,←pow_add,coeff_one_add_X_pow] at book
  have total : g.s-1+g.s*h=(h+1)*g.s-1 := by
    rw [Nat.succ_mul,Nat.mul_comm h g.s]
    have := g.room
    omega
  change (allHands g.s h t).card=_
  rw [total] at book
  exact_mod_cast book.symm

theorem probability_is_card_ratio (g : Game) (h t : ℕ) :
    bumpProbability g (h+1) (t+1)=((bumpHands g h t).card:ℚ)/(allHands g.s h t).card := by
  rw [all_hands_card]
  rfl

/-- The band and bump rules apply to the prefix counts of all ranks, `none` being the last rank. -/
def inBand (g : Game) {h : ℕ} (w : List (Option (Fin h))) : Prop :=
  ∀i,g.l≤w.count i ∧ w.count i≤g.u

def hasBump (g : Game) {h : ℕ} (w : List (Option (Fin h))) : Prop := ∃i,g.u<w.count i

/-- The appended marked card causes the first terminal event, which is a bump. -/
def firstBump (g : Game) {h : ℕ} (w : List (Option (Fin h))) : Prop :=
  hasBump g (w++[none]) ∧ ∀v,v.IsPrefix w → ¬inBand g v ∧ ¬hasBump g v

private theorem first_iff (g : Game) {h : ℕ} (w : List (Option (Fin h))) : firstBump g w ↔
    w.count none=g.u ∧ (∀i : Fin h,w.count (some i)≤g.u) ∧ ∃i : Fin h,w.count (some i)<g.l := by
  classical
  constructor
  · rintro ⟨⟨last,ex⟩,quiet⟩
    obtain ⟨noband,nobump⟩ := quiet w ⟨[],by simp⟩
    have le (i : Option (Fin h)) : w.count i≤g.u := by
      exact le_of_not_gt (fun v=>nobump ⟨i,v⟩)
    have val : w.count none=g.u := by
      cases last with
      | none => simp [List.count_append] at ex;have z := le none;omega
      | some i => simp [List.count_append] at ex;have z := le (some i);omega
    refine ⟨val,fun i=>le (some i),?_⟩
    by_contra! nl
    apply noband
    intro i
    cases i with
    | none => exact ⟨val ▸ g.ordered,le none⟩
    | some i => exact ⟨nl i,le _⟩
  · rintro ⟨hm,good,⟨i,low⟩⟩
    refine ⟨⟨none,by simp [List.count_append,hm]⟩,?_⟩
    rintro v ⟨tail,e⟩
    have le (j : Option (Fin h)) : v.count j≤w.count j := by rw [←e,List.count_append];omega
    constructor
    · intro b
      exact (Nat.not_le_of_lt ((le (some i)).trans_lt low)) (b (some i)).1
    · rintro ⟨j,ex⟩
      cases j with
      | none => have := le none;omega
      | some j => have := le (some j);have := good j;omega

/-- Every ordering of a labelled prior hand obeys exactly the first-bump predicate used in counting. -/
theorem bump_hand_iff_first_bump (g : Game) {h : ℕ} (H : Hand g.s) (w : List (Option (Fin h)))
    (len : H.2.length=h) (hm : w.count none=H.1.card)
    (others : H.2.map Finset.card=List.ofFn (fun i : Fin h=>w.count (some i))) :
    H∈bumpHands g h (countCards H) ↔ firstBump g w := by
  have mem (v : ℕ) : (∃K∈H.2,K.card=v) ↔ ∃i : Fin h,w.count (some i)=v := by
    rw [←List.mem_map,others,List.mem_ofFn]
  have all : (∀K∈H.2,K.card≤g.u) ↔ ∀i : Fin h,w.count (some i)≤g.u := by
    constructor
    · intro z i
      obtain ⟨K,hK,e⟩ := (mem _).2 ⟨i,rfl⟩
      exact e ▸ z K hK
    · intro z K hK
      obtain ⟨i,e⟩ := (mem _).1 ⟨K,hK,rfl⟩
      exact e ▸ z i
  have some : (∃K∈H.2,K.card<g.l) ↔ ∃ i : Fin h,w.count (Option.some i)<g.l := by
    constructor
    · rintro ⟨K,hK,low⟩
      obtain ⟨i,e⟩ := (mem _).1 ⟨K,hK,rfl⟩
      exact ⟨i,e ▸ low⟩
    · rintro ⟨i,low⟩
      obtain ⟨K,hK,e⟩ := (mem _).2 ⟨i,rfl⟩
      exact ⟨K,hK,e ▸ low⟩
  simp only [sample_membership,len,first_iff,hm,all,some,true_and]

/-- Restoring the original rank and label identifies the relabelled deck after *any* final card. -/
def remainingDeckEquiv {h s : ℕ} (last : Fin (h+1)×Fin (s+1)) :
    (Fin s ⊕ (Fin h×Fin (s+1))) ≃ {v : Fin (h+1)×Fin (s+1) // v≠last} := by
  let restore : (Fin s ⊕ (Fin h×Fin (s+1)))→{v : Fin (h+1)×Fin (s+1) // v≠last} := fun v=>
    match v with
    | .inl i => ⟨(last.1,last.2.succAbove i),fun e=>last.2.succAbove_ne i (congrArg Prod.snd e)⟩
    | .inr (r,i) => ⟨(last.1.succAbove r,i),fun e=>last.1.succAbove_ne r (congrArg Prod.fst e)⟩
  refine Equiv.ofBijective restore ⟨?_,?_⟩
  · rintro (a|⟨r,a⟩) (b|⟨t,b⟩) e
    · exact congrArg Sum.inl (last.2.succAbove_right_injective (congrArg (fun x=>x.val.2) e))
    · exact False.elim (last.1.ne_succAbove t (congrArg (fun x=>x.val.1) e))
    · exact False.elim (last.1.succAbove_ne r (congrArg (fun x=>x.val.1) e))
    · exact congrArg Sum.inr (Prod.ext (last.1.succAbove_right_injective (congrArg (fun x=>x.val.1) e))
        (congrArg (fun x=>x.val.2) e))
  · rintro ⟨⟨r,i⟩,ne⟩
    by_cases e : r=last.1
    · have diff : i≠last.2 := fun z=>ne (Prod.ext e z)
      obtain ⟨j,hj⟩ := Fin.exists_succAbove_eq diff
      exact ⟨Sum.inl j,Subtype.ext (Prod.ext e.symm hj)⟩
    · obtain ⟨a,ha⟩ := Fin.exists_succAbove_eq e
      exact ⟨Sum.inr (a,i),Subtype.ext (Prod.ext ha rfl)⟩

/-- Averaging over the uniformly labelled final card leaves the same probability. -/
theorem all_final_cards_ratio (g : Game) (h t : ℕ) :
    bumpProbability g (h+1) (t+1)=
      (((univ : Finset (Fin (h+1)×Fin g.s))×ˢbumpHands g h t).card:ℚ)/
        (((univ : Finset (Fin (h+1)×Fin g.s))×ˢallHands g.s h t).card:ℚ) := by
  have hs : 0<(g.s:ℚ) := by exact_mod_cast (by have := g.room;omega : 0<g.s)
  rw [probability_is_card_ratio]
  simp only [Finset.card_product,Finset.card_univ,Fintype.card_prod,Fintype.card_fin,Nat.cast_mul,
    Nat.cast_add,Nat.cast_one]
  rw [mul_div_mul_left _ _ (mul_ne_zero (by positivity : (h:ℚ)+1≠0) hs.ne')]

/-- A legal nonempty deck, including the boundary conventions on page 7 of Levin's paper. -/
structure Deck where
  ranks : ℕ
  s : ℕ
  l : ℕ
  u : ℕ
  ranks_pos : 0<ranks
  size_pos : 0<s
  ordered : l≤u
  within : u≤s

/-- At cap zero the first card causes a bump. With lower limit zero and positive cap the first
card is a band. At cap `s` a bump is impossible. Otherwise use the labelled stopping game. -/
def Deck.bumpMass (d : Deck) (n : ℕ) : ℚ :=
  if d.u=0 then (if n=1 then 1 else 0) else
  if g : 0<d.l ∧ d.u<d.s then bumpProbability ⟨d.s,d.l,d.u,g.1,d.ordered,g.2⟩ d.ranks n else 0

/-- The bump side of Remark 2 in every permitted parameter case and at every draw time. -/
theorem all_legal_thresholds (d : Deck) (n : ℕ) :
    d.bumpMass n*d.bumpMass (n+2)≤(d.bumpMass (n+1))^2 := by
  by_cases z : d.u=0
  · simp only [Deck.bumpMass,if_pos z,if_neg (show n+2≠1 by omega),mul_zero]
    exact sq_nonneg _
  by_cases h : 0<d.l ∧ d.u<d.s
  · simpa only [Deck.bumpMass,if_neg z,dif_pos h] using
      all_ranks_bump_log_concave ⟨d.s,d.l,d.u,h.1,d.ordered,h.2⟩ d.ranks n
  · simp [Deck.bumpMass,z,h]

#print axioms all_legal_thresholds
#print axioms all_ranks_bump_log_concave
#print axioms all_ranks_support
#print axioms missing_log_concave
#print axioms probability_is_card_ratio
#print axioms bump_hand_iff_first_bump
#print axioms all_final_cards_ratio
#print axioms remainingDeckEquiv
end
end BandAll

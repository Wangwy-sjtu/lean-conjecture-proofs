import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Comparison of vertex first-hitting means for the simple and non-backtracking
random walks in Section 5 Question 4 of Breen–Kempton–Knudson–Shumway. -/

namespace VertexHitting
open Finset Filter Topology
noncomputable section
universe u

/-- A finite simple undirected graph on which a non-backtracking walk can
continue after any incoming edge. -/
structure Network (V : Type u) [Fintype V] [DecidableEq V] where
  neighbors : V → Finset V
  symmetric : ∀ {i j}, j ∈ neighbors i ↔ i ∈ neighbors j
  loopless : ∀ i, i ∉ neighbors i
  two_le : ∀ i, 2 ≤ (neighbors i).card

namespace Network
variable {V : Type u} [Fintype V] [DecidableEq V] (G : Network V)

def deg (i : V) : ℝ := (G.neighbors i).card

theorem deg_ge_two (i : V) : 2 ≤ G.deg i := by unfold deg; exact_mod_cast G.two_le i

theorem deg_pos (i : V) : 0 < G.deg i := lt_of_lt_of_le (by norm_num) (G.deg_ge_two i)

def row (i : V) (f : V → ℝ) : ℝ := ∑ j ∈ G.neighbors i, f j
def arcs (f : V → V → ℝ) : ℝ := ∑ i, G.row i (f i)
def div (f : V → V → ℝ) (i : V) : ℝ := G.row i (f i)

private theorem row_eq_of_adj (i : V) {f g : V → ℝ}
    (h : ∀ j ∈ G.neighbors i, f j = g j) : G.row i f = G.row i g :=
  Finset.sum_congr rfl h

private theorem row_add (i : V) (f g : V → ℝ) :
    G.row i (fun j => f j+g j) = G.row i f + G.row i g := Finset.sum_add_distrib

private theorem row_sub (i : V) (f g : V → ℝ) :
    G.row i (fun j => f j-g j) = G.row i f - G.row i g := Finset.sum_sub_distrib _ _

private theorem row_mul (i : V) (x : ℝ) (f : V → ℝ) :
    G.row i (fun j => x*f j) = x*G.row i f := (Finset.mul_sum ..).symm

private theorem row_const (i : V) (x : ℝ) : G.row i (fun _ => x) = G.deg i*x := by
  simp [row,deg]

private theorem arcs_eq_of_adj {f g : V → V → ℝ} (h : ∀ i j, j ∈ G.neighbors i → f i j = g i j) :
    G.arcs f = G.arcs g := Finset.sum_congr rfl (fun i _ => G.row_eq_of_adj i (h i))

private theorem arcs_add (f g : V → V → ℝ) :
    G.arcs (fun i j => f i j+g i j) = G.arcs f+G.arcs g := by
  simp [arcs, row_add, Finset.sum_add_distrib]

private theorem arcs_sub (f g : V → V → ℝ) :
    G.arcs (fun i j => f i j-g i j) = G.arcs f-G.arcs g := by
  simp [arcs, row_sub]

private theorem arcs_mul (x : ℝ) (f : V → V → ℝ) :
    G.arcs (fun i j => x*f i j) = x*G.arcs f := by
  simp [arcs, row_mul, Finset.mul_sum]

private theorem arcs_fst (f : V → ℝ) :
    G.arcs (fun i _ => f i) = ∑ i, G.deg i*f i := by simp [arcs, row_const]

private theorem arcs_flip (f : V → V → ℝ) : G.arcs (fun i j => f j i) = G.arcs f := by
  have eqrow (i : V) (h : V → ℝ) : G.row i h = ∑ j, if j ∈ G.neighbors i then h j else 0 := by
    rw [← Finset.sum_filter]
    simp [row]
  simp only [arcs, eqrow]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : j ∈ G.neighbors i
  · simp [h, G.symmetric.mp h]
  · have hn : i ∉ G.neighbors j := fun h' => h (G.symmetric.mpr h')
    simp [h, hn]

/-- Discrete integration by parts over both orientations of each edge. -/
private theorem green (p : V → ℝ) (f : V → V → ℝ)
    (anti : ∀ i j, f j i = -f i j) :
    G.arcs (fun i j => (p i-p j)*f i j) = 2*∑ i, p i*G.div f i := by
  have flip : G.arcs (fun i j => p j*f i j) = -G.arcs (fun i j => p i*f i j) := by
    rw [← G.arcs_flip (fun i j => p j*f i j)]
    calc
      _ = G.arcs (fun i j => (-1)*(p i*f i j)) :=
        G.arcs_eq_of_adj (fun i j _ => by rw [anti i j]; ring)
      _ = _ := by rw [G.arcs_mul]; ring
  calc
    _ = G.arcs (fun i j => p i * f i j - p j * f i j) :=
      G.arcs_eq_of_adj (fun _ _ _ => by ring)
    _ = 2*G.arcs (fun i j => p i*f i j) := by rw [G.arcs_sub,flip]; ring
    _ = _ := by simp [arcs, div, row_mul]

/-- First-step equations. The value after seeing previous vertex j and
current vertex i is stored in reversed order as arc i j. -/
structure FirstStep (t : V) where
  simple : V → ℝ
  fresh : V → ℝ
  arc : V → V → ℝ
  simple_sink : simple t = 0
  fresh_sink : fresh t = 0
  arc_sink : ∀ j ∈ G.neighbors t, arc t j = 0
  simple_step : ∀ i, i ≠ t → G.deg i * simple i = G.deg i + G.row i simple
  fresh_step : ∀ i, i ≠ t → G.deg i * fresh i = G.deg i + G.row i (fun j => arc j i)
  arc_step : ∀ i j, i ≠ t → j ∈ G.neighbors i →
    (G.deg i-1)*arc i j = G.deg i-1 + G.row i (fun k => arc k i) - arc j i

namespace FirstStep
variable {G} {t : V} (H : G.FirstStep t)

def c (i : V) : ℝ := if i=t then 0 else 1/G.deg i
def potential (i : V) : ℝ := H.fresh i - c (G := G) (t := t) i
def current (i j : V) : ℝ := H.arc i j - H.arc j i
def ordinary (i j : V) : ℝ := H.simple i - H.simple j
def resistance (i j : V) : ℝ := 1-c (G := G) (t := t) i-c (G := G) (t := t) j

private theorem current_flip (i j : V) : H.current j i = -H.current i j := by simp [current]
private theorem ordinary_flip (i j : V) : H.ordinary j i = -H.ordinary i j := by simp [ordinary]

private theorem c_nonneg (i : V) : 0 ≤ c (G := G) (t := t) i := by
  simp only [c]
  split
  · exact le_refl 0
  · exact div_nonneg (by norm_num) (G.deg_pos i).le

private theorem c_le_half (i : V) : c (G := G) (t := t) i ≤ 1/2 := by
  simp only [c]
  split
  · norm_num
  · gcongr; exact G.deg_ge_two i

private theorem resistance_nonneg (i j : V) : 0 ≤ resistance (G := G) (t := t) i j := by
  have := c_le_half (G := G) (t := t) i
  have := c_le_half (G := G) (t := t) j
  unfold resistance
  linarith

private theorem current_div (i : V) (hi : i ≠ t) : G.div H.current i = G.deg i := by
  let D := G.deg i
  let incoming := G.row i (fun j => H.arc j i)
  have summation : (D-1)*G.row i (H.arc i) = D*(D-1+incoming)-incoming := by
    rw [← G.row_mul]
    calc
      _ = G.row i (fun j => (D-1+incoming)-H.arc j i) :=
        G.row_eq_of_adj i (fun j hj => H.arc_step i j hi hj)
      _ = _ := by rw [G.row_sub,G.row_const]
  have nz : D-1 ≠ 0 := by have := G.deg_ge_two i; dsimp [D]; linarith
  unfold div current
  rw [G.row_sub]
  change G.row i (H.arc i)-incoming = D
  apply mul_left_cancel₀ nz
  linarith

private theorem ordinary_div (i : V) (hi : i ≠ t) : G.div H.ordinary i = G.deg i := by
  unfold div ordinary
  rw [G.row_sub,G.row_const]
  linarith [H.simple_step i hi]

private theorem arc_potential (i j : V) (hj : j ∈ G.neighbors i) :
    H.arc i j = H.potential i + c (G := G) (t := t) i*H.current i j := by
  by_cases hi : i=t
  · subst i
    simp [c,potential,H.fresh_sink,H.arc_sink j hj]
  · have hs := H.arc_step i j hi hj
    have hf := H.fresh_step i hi
    simp only [potential,c,if_neg hi,current]
    field_simp [(G.deg_pos i).ne']
    linarith

private theorem ohm (i j : V) (h : j ∈ G.neighbors i) :
    resistance (G := G) (t := t) i j * H.current i j = H.potential i-H.potential j := by
  have hi := H.arc_potential i j h
  have hj := H.arc_potential j i (G.symmetric.mp h)
  rw [H.current_flip i j] at hj
  unfold resistance
  have dc : H.current i j = H.arc i j-H.arc j i := rfl
  linarith

def degreeSum (f : V → ℝ) : ℝ := ∑ i, G.deg i*f i

private theorem grounded_sum (p : V → ℝ) (pt : p t=0) (f : V → V → ℝ)
    (div : ∀ i, i ≠ t → G.div f i = G.deg i) :
    ∑ i, p i*G.div f i = degreeSum (G := G) p := by
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i=t
  · simp [hi,pt]
  · rw [div _ hi, mul_comm]

private theorem ordinary_energy :
    G.arcs (fun i j => H.ordinary i j ^ 2) = 2*degreeSum (G := G) H.simple := by
  calc
    _ = G.arcs (fun i j => (H.simple i-H.simple j)*H.ordinary i j) :=
      G.arcs_eq_of_adj (fun _ _ _ => by unfold ordinary; ring)
    _ = _ := by rw [G.green _ _ H.ordinary_flip, grounded_sum _ H.simple_sink _ H.ordinary_div]

private theorem cross_energy (f : V → V → ℝ) (anti : ∀ i j, f j i = -f i j)
    (df : ∀ i, i ≠ t → G.div f i = G.deg i) :
    G.arcs (fun i j => resistance (G := G) (t := t) i j*H.current i j*f i j)
      = 2*degreeSum (G := G) H.potential := by
  calc
    _ = G.arcs (fun i j => (H.potential i-H.potential j)*f i j) :=
      G.arcs_eq_of_adj (fun i j h => by rw [H.ohm i j h])
    _ = _ := by
      rw [G.green _ _ anti, grounded_sum _ (by simp [potential, c, H.fresh_sink]) _ df]

private theorem arcs_nonneg {f : V → V → ℝ} (hf : ∀ i j, j ∈ G.neighbors i → 0 ≤ f i j) :
    0 ≤ G.arcs f :=
  Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j hj => hf i j hj))

private theorem arcs_pos {f : V → V → ℝ} (hf : ∀ i j, j ∈ G.neighbors i → 0 ≤ f i j)
    {i j : V} (h : j ∈ G.neighbors i) (hp : 0 < f i j) : 0 < G.arcs f := by
  apply Finset.sum_pos' (fun a _ => Finset.sum_nonneg (fun b hb => hf a b hb))
  exact ⟨i, Finset.mem_univ _, Finset.sum_pos' (fun b hb => hf i b hb) ⟨j,h,hp⟩⟩

private theorem thomson_remainder :
    G.arcs (fun i j => resistance (G := G) (t := t) i j*(H.ordinary i j-H.current i j)^2) =
      G.arcs (fun i j => resistance (G := G) (t := t) i j*H.ordinary i j ^ 2)
        -2*degreeSum (G := G) H.potential := by
  let R := resistance (G := G) (t := t)
  let J := H.current
  let F := H.ordinary
  have expansion :
      G.arcs (fun i j => R i j*(F i j-J i j)^2) =
      G.arcs (fun i j => R i j*F i j^2)
        -2*G.arcs (fun i j => R i j*J i j*F i j) +
        G.arcs (fun i j => R i j*J i j*J i j) := by
    calc
      _ = G.arcs (fun i j => (R i j*F i j^2-2*(R i j*J i j*F i j))+R i j*J i j*J i j) :=
        G.arcs_eq_of_adj (fun _ _ _ => by ring)
      _ = _ := by rw [G.arcs_add,G.arcs_sub,G.arcs_mul]
  have h₁ := H.cross_energy H.current H.current_flip H.current_div
  have h₂ := H.cross_energy H.ordinary H.ordinary_flip H.ordinary_div
  change G.arcs (fun i j => R i j*J i j*J i j)=_ at h₁
  change G.arcs (fun i j => R i j*J i j*F i j)=_ at h₂
  change G.arcs (fun i j => R i j*(F i j-J i j)^2) =
    G.arcs (fun i j => R i j*F i j^2)-2*degreeSum (G := G) H.potential
  rw [expansion,h₁,h₂]
  ring

private theorem interior_edge (G : Network V) (t : V) :
    ∃ i j, i ≠ t ∧ j ≠ t ∧ j ∈ G.neighbors i := by
  have hn : (G.neighbors t).Nonempty := Finset.card_pos.mp (by have := G.two_le t; omega)
  obtain ⟨i,hit⟩ := hn
  have hi : i ≠ t := fun he => G.loopless t (he ▸ hit)
  obtain ⟨j,hj,k,hk,hjk⟩ := Finset.one_lt_card_iff_nontrivial.mp (G.two_le i)
  by_cases he : j=t
  · exact ⟨i,k,hi,by intro h; exact hjk (he.trans h.symm),hk⟩
  · exact ⟨i,j,hi,he,hj⟩

private theorem strict_dissipation :
    0 < G.arcs (fun i j => c (G := G) (t := t) i*(H.ordinary i j-1)^2) := by
  let f := fun i j => c (G := G) (t := t) i*(H.ordinary i j-1)^2
  have nn : ∀ i j, j ∈ G.neighbors i → 0 ≤ f i j :=
    fun i j _ => mul_nonneg (c_nonneg i) (sq_nonneg _)
  have positive {i j : V} (hi : i ≠ t) (hne : H.ordinary i j ≠ 1) : 0 < f i j := by
    have hc : 0 < c (G := G) (t := t) i := by
      simp only [c,if_neg hi]
      exact div_pos (by norm_num) (G.deg_pos i)
    exact mul_pos hc (sq_pos_of_ne_zero (sub_ne_zero.mpr hne))
  obtain ⟨i,j,hi,hj,adj⟩ := interior_edge G t
  by_cases eq : H.ordinary i j = 1
  · have ne : H.ordinary j i ≠ 1 := by rw [H.ordinary_flip,eq]; norm_num
    exact arcs_pos nn (G.symmetric.mp adj) (positive hj ne)
  · exact arcs_pos nn adj (positive hi eq)

/-- Exact weighted gap as the sum of the network discrepancy and the
ordinary walk's local current variations. The edge sum uses both directions. -/
theorem energy_gap :
    2*(degreeSum (G := G) H.simple - degreeSum (G := G) H.fresh) =
      G.arcs (fun i j => resistance (G := G) (t := t) i j*(H.ordinary i j-H.current i j)^2)
      +2*G.arcs (fun i j => c (G := G) (t := t) i*(H.ordinary i j-1)^2) := by
  let C := c (G := G) (t := t)
  let R := resistance (G := G) (t := t)
  let F := H.ordinary
  let mass := degreeSum (G := G) C
  let loss := G.arcs (fun i j => C i*F i j^2)
  have flipLoss : G.arcs (fun i j => C j*F i j^2) = loss := by
    rw [← G.arcs_flip (fun i j => C j*F i j^2)]
    exact G.arcs_eq_of_adj (fun i j _ => by
      change C i*(H.ordinary j i)^2=C i*(H.ordinary i j)^2
      rw [H.ordinary_flip]; ring)
  have resistanceEnergy : G.arcs (fun i j => R i j*F i j^2) =
      2*degreeSum (G := G) H.simple-2*loss := by
    calc
      _ = G.arcs (fun i j => (F i j^2-C i*F i j^2)-C j*F i j^2) :=
        G.arcs_eq_of_adj (fun i j _ => by dsimp [R,resistance,C]; ring)
      _ = _ := by rw [G.arcs_sub,G.arcs_sub,flipLoss,H.ordinary_energy]; dsimp [loss,F]; ring
  have weightedDiv : G.arcs (fun i j => C i*F i j) = mass := by
    change (∑ i, G.row i (fun j => C i*F i j)) = _
    simp only [row_mul]
    exact grounded_sum C (by simp [C,c]) F H.ordinary_div
  have constSum : G.arcs (fun i _ => C i) = mass := G.arcs_fst C
  have sourceCost : degreeSum (G := G) H.potential = degreeSum (G := G) H.fresh-mass := by
    simp [mass,degreeSum,potential,C,mul_sub,Finset.sum_sub_distrib]
  have variance : G.arcs (fun i j => C i*(F i j-1)^2) = loss - mass := by
    calc
      _ = G.arcs (fun i j => (C i*F i j^2-2*(C i*F i j))+C i) :=
        G.arcs_eq_of_adj (fun _ _ _ => by ring)
      _ = _ := by rw [G.arcs_add,G.arcs_sub,G.arcs_mul,weightedDiv,constSum]; dsimp [loss]; ring
  have ht := H.thomson_remainder
  change _ = G.arcs (fun i j => R i j*F i j^2)-_ at ht
  rw [resistanceEnergy,sourceCost] at ht
  change _ = _+2*G.arcs (fun i j => C i*(F i j-1)^2)
  rw [variance,ht]
  ring

/-- Strict comparison of stationary-source target costs for every target,
before division by the common graph volume. -/
theorem degree_weighted_strict :
    degreeSum (G := G) H.fresh < degreeSum (G := G) H.simple := by
  have hgap := H.energy_gap
  have pos := H.strict_dissipation
  have hzero : 0 ≤ G.arcs
      (fun i j => resistance (G := G) (t := t) i j*(H.ordinary i j-H.current i j)^2) :=
    arcs_nonneg (fun i j _ => mul_nonneg (resistance_nonneg i j) (sq_nonneg _))
  linarith

end FirstStep

/-- False is the simple walk, true is the non-backtracking walk. A fresh
start has no incoming edge and uses the whole neighbor set in either model. -/
def allowed (nb : Bool) (prev : Option V) (i : V) : Finset V :=
  match nb, prev with
  | true, some p => (G.neighbors i).erase p
  | _, _ => G.neighbors i

private theorem allowed_subset (nb : Bool) (prev : Option V) (i : V) :
    G.allowed nb prev i ⊆ G.neighbors i := by
  cases nb <;> cases prev <;> simp [allowed, Finset.erase_subset]

private theorem allowed_pos (nb : Bool) (prev : Option V) (i : V) :
    0 < (G.allowed nb prev i).card := by
  have hn := G.two_le i
  cases nb <;> cases prev with
  | none => simpa [allowed] using (show 0 < (G.neighbors i).card by omega)
  | some p =>
    simp only [allowed]
    first
    | omega
    | by_cases hp : p ∈ G.neighbors i
      · rw [Finset.card_erase_of_mem hp]; omega
      · rw [Finset.erase_eq_of_notMem hp]; omega

/-- Expected hitting time capped at n. At a fresh or directed-edge state the
next vertex is sampled uniformly from exactly the legal choices above. -/
def capped (nb : Bool) (t : V) : ℕ → Option V → V → ℝ
  | 0, _, _ => 0
  | n+1, p, i => if i=t then 0 else
      1+(∑ j ∈ G.allowed nb p i, capped nb t n (some i) j)/(G.allowed nb p i).card

/-- Survival probability P(T>n), computed by summing over n genuine transitions. -/
def survival (nb : Bool) (t : V) : ℕ → Option V → V → ℝ
  | 0, _, i => if i=t then 0 else 1
  | n+1, p, i => if i=t then 0 else
      (∑ j ∈ G.allowed nb p i, survival nb t n (some i) j)/(G.allowed nb p i).card

theorem capped_eq_survival_sum (nb : Bool) (t : V) (n : ℕ) (p : Option V) (i : V) :
    G.capped nb t n p i = ∑ r ∈ Finset.range n, G.survival nb t r p i := by
  have increments : ∀ n (p : Option V) (i : V),
      G.capped nb t (n+1) p i = G.capped nb t n p i + G.survival nb t n p i := by
    intro r
    induction r with
    | zero => intro p i; by_cases h : i=t <;> simp [capped,survival,h]
    | succ r ih =>
      intro p i
      by_cases h : i=t
      · simp [capped,survival,h]
      · simp only [capped, survival, if_neg h]
        change 1+(∑ j ∈ G.allowed nb p i,G.capped nb t (r+1) (some i) j)/(G.allowed nb p i).card
          = (1+(∑ j ∈ G.allowed nb p i,G.capped nb t r (some i) j)/(G.allowed nb p i).card)
            +(∑ j ∈ G.allowed nb p i,G.survival nb t r (some i) j)/(G.allowed nb p i).card
        have e := Finset.sum_congr (s₁ := G.allowed nb p i) rfl
          (fun j _ => ih (some i) j)
        rw [e, Finset.sum_add_distrib, add_div]
        ring
  induction n with
  | zero => simp [capped]
  | succ n ih => rw [increments, ih, Finset.sum_range_succ]

private theorem survival_nonneg (nb : Bool) (t : V) (n : ℕ) (p : Option V) (i : V) :
    0 ≤ G.survival nb t n p i := by
  induction n generalizing p i with
  | zero => simp [survival]; split <;> norm_num
  | succ n ih =>
    simp only [survival]
    split
    · exact le_refl 0
    · exact div_nonneg (Finset.sum_nonneg fun _ _ => ih _ _) (by positivity)

private theorem capped_nonneg (nb : Bool) (t : V) (n : ℕ) (p : Option V) (i : V) :
    0 ≤ G.capped nb t n p i := by
  rw [G.capped_eq_survival_sum]
  exact Finset.sum_nonneg (fun _ _ => G.survival_nonneg ..)

/-- The finite-first-hitting hypothesis in the question, solely for fresh
vertex starts. -/
def FiniteHitting (nb : Bool) (t : V) : Prop :=
  ∀ i, BddAbove (Set.range (fun n => G.capped nb t n none i))

/-- The first-hitting mean: the supremum of the capped means. -/
def mean (nb : Bool) (t : V) (p : Option V) (i : V) : ℝ :=
  ⨆ n : ℕ, G.capped nb t n p i

private theorem capped_mono (nb : Bool) (t : V) (p : Option V) (i : V) :
    Monotone (fun n => G.capped nb t n p i) := by
  apply monotone_nat_of_le_succ
  intro n
  simp only [G.capped_eq_survival_sum, Finset.sum_range_succ]
  exact le_add_of_nonneg_right (G.survival_nonneg ..)

private theorem fresh_allowed (nb : Bool) (i : V) : G.allowed nb none i = G.neighbors i := by
  cases nb <;> rfl

private theorem capped_prev_le (nb : Bool) (t : V) (n : ℕ) (p : Option V) (i : V) :
    G.capped nb t n p i ≤ G.deg i * G.capped nb t n none i := by
  cases n with
  | zero => simp [capped]
  | succ n =>
    by_cases h : i=t
    · simp [capped,h]
    · simp only [capped,if_neg h,G.fresh_allowed]
      let s := G.allowed nb p i
      let f := fun j => G.capped nb t n (some i) j
      have hsub : ∑ j ∈ s, f j ≤ ∑ j ∈ G.neighbors i, f j :=
        Finset.sum_le_sum_of_subset_of_nonneg (G.allowed_subset ..)
          (fun _ _ _ => G.capped_nonneg ..)
      have hzero : 0 ≤ ∑ j ∈ s, f j := Finset.sum_nonneg (fun _ _ => G.capped_nonneg ..)
      have hsc : 1 ≤ (s.card : ℝ) := by exact_mod_cast G.allowed_pos nb p i
      have hdiv := div_le_self hzero hsc
      have hd := G.deg_ge_two i
      have dpos := G.deg_pos i
      change 1+(∑ j ∈ s,f j)/(s.card : ℝ) ≤
        G.deg i*(1+(∑ j ∈ G.neighbors i,f j)/G.deg i)
      rw [mul_add,mul_one,mul_div_cancel₀ _ dpos.ne']
      linarith

private theorem mean_tendsto {nb : Bool} {t : V} (hf : G.FiniteHitting nb t)
    (p : Option V) (i : V) : Tendsto (fun n => G.capped nb t n p i) atTop (𝓝 (G.mean nb t p i)) := by
  obtain ⟨B,hB⟩ := hf i
  apply tendsto_atTop_ciSup (G.capped_mono nb t p i)
  refine ⟨G.deg i*B, ?_⟩
  rintro _ ⟨n,rfl⟩
  exact (G.capped_prev_le nb t n p i).trans
    (mul_le_mul_of_nonneg_left (hB ⟨n,rfl⟩) (G.deg_pos i).le)

theorem mean_sink (nb : Bool) (t : V) (p : Option V) : G.mean nb t p t=0 := by
  have h : ∀ n, G.capped nb t n p t = 0 := by intro n; cases n <;> simp [capped]
  simp [mean,h]

private theorem mean_step {nb : Bool} {t : V} (hf : G.FiniteHitting nb t)
    (p : Option V) (i : V) (hi : i ≠ t) :
    G.mean nb t p i =
      1+(∑ j ∈ G.allowed nb p i,G.mean nb t (some i) j)/(G.allowed nb p i).card := by
  have left := (G.mean_tendsto hf p i).comp (tendsto_add_atTop_nat 1)
  have right : Tendsto (fun n => 1+
      (∑ j ∈ G.allowed nb p i, G.capped nb t n (some i) j)/(G.allowed nb p i).card)
      atTop (𝓝 (1+(∑ j ∈ G.allowed nb p i,G.mean nb t (some i) j)/(G.allowed nb p i).card)) :=
    tendsto_const_nhds.add ((tendsto_finset_sum _ (fun j _ => G.mean_tendsto hf (some i) j)).div_const _)
  apply tendsto_nhds_unique _ right
  simpa [Function.comp_def,capped,hi] using left

private theorem simple_forgets (t i : V) (p : Option V) :
    G.mean false t p i = G.mean false t none i := by
  unfold mean
  congr 1
  funext n
  cases n <;> simp [capped,allowed]

/-- Derive all boundary and first-step equations from the finite first-hitting
means defined by the walk, including uniform choice on a fresh start. -/
def hittingData (t : V) (hs : G.FiniteHitting false t) (hn : G.FiniteHitting true t) :
    G.FirstStep t where
  simple := G.mean false t none
  fresh := G.mean true t none
  arc i j := G.mean true t (some j) i
  simple_sink := G.mean_sink false t none
  fresh_sink := G.mean_sink true t none
  arc_sink := fun j _ => G.mean_sink true t (some j)
  simple_step := by
    intro i hi
    have h := G.mean_step hs none i hi
    simp only [fresh_allowed, simple_forgets] at h
    change G.mean false t none i = 1 + G.row i (G.mean false t none)/G.deg i at h
    have h' := (eq_div_iff (G.deg_pos i).ne').mp
      (show G.mean false t none i-1=G.row i (G.mean false t none)/G.deg i by linarith)
    linarith
  fresh_step := by
    intro i hi
    have h := G.mean_step hn none i hi
    simp only [fresh_allowed] at h
    let s := G.row i (fun j => G.mean true t (some i) j)
    change G.mean true t none i = 1+s/G.deg i at h
    have h' := (eq_div_iff (G.deg_pos i).ne').mp
      (show G.mean true t none i-1=s/G.deg i by linarith)
    change G.deg i*G.mean true t none i= G.deg i+s
    linarith
  arc_step := by
    intro i j hi hj
    let f := fun k => G.mean true t (some i) k
    have h := G.mean_step hn (some j) i hi
    change G.mean true t (some j) i = 1+(∑ k ∈ (G.neighbors i).erase j,f k) /
      ((G.neighbors i).erase j).card at h
    have hc : (((G.neighbors i).erase j).card : ℝ) = G.deg i-1 := by
      rw [Finset.card_erase_of_mem hj, Nat.cast_sub (by have := G.two_le i; omega)]
      simp [deg]
    rw [hc] at h
    have hne : G.deg i - 1 ≠ 0 := by have := G.deg_ge_two i; linarith
    have h' := (eq_div_iff hne).mp
      (show G.mean true t (some j) i-1=(∑ k ∈ (G.neighbors i).erase j,f k)/(G.deg i-1)
        by linarith)
    have add := Finset.sum_erase_add (G.neighbors i) f hj
    change (G.deg i-1)*G.mean true t (some j) i =
      G.deg i-1+(∑ k ∈ G.neighbors i,f k)-f j
    linarith

def volume : ℝ := ∑ i, G.deg i
def stationary (i : V) : ℝ := G.deg i/G.volume
def stationaryTo (nb : Bool) (t : V) : ℝ := ∑ i, G.stationary i*G.mean nb t none i
def kemeny (nb : Bool) : ℝ := ∑ t, G.stationary t*G.stationaryTo nb t

theorem volume_pos [Nonempty V] : 0 < G.volume :=
  Finset.sum_pos (fun i _ => G.deg_pos i) Finset.univ_nonempty

theorem stationary_pos (i : V) : 0 < G.stationary i := by
  letI : Nonempty V := ⟨i⟩
  exact div_pos (G.deg_pos i) G.volume_pos

theorem stationary_sum [Nonempty V] : ∑ i, G.stationary i = 1 := by
  calc
    _ = G.volume / G.volume := by simp [stationary,volume,div_eq_mul_inv,Finset.sum_mul]
    _ = _ := div_self G.volume_pos.ne'

private theorem stationaryTo_eq (nb : Bool) (t : V) :
    G.stationaryTo nb t = FirstStep.degreeSum (G := G) (G.mean nb t none)/G.volume := by
  unfold stationaryTo stationary FirstStep.degreeSum
  simp only [div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The comparison already holds before the random choice of the target. -/
theorem stationary_target_strict (t : V) (hs : G.FiniteHitting false t)
    (hn : G.FiniteHitting true t) : G.stationaryTo true t < G.stationaryTo false t := by
  letI : Nonempty V := ⟨t⟩
  rw [G.stationaryTo_eq,G.stationaryTo_eq]
  exact div_lt_div_of_pos_right (G.hittingData t hs hn).degree_weighted_strict G.volume_pos

/-- Section 5, Question 4: strictness on the full domain where the two
vertex first-hitting means are finite. -/
theorem kemeny_nonbacktracking_lt_simple [Nonempty V]
    (hs : ∀ t, G.FiniteHitting false t) (hn : ∀ t, G.FiniteHitting true t) :
    G.kemeny true < G.kemeny false := by
  apply Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
  intro t _
  exact mul_lt_mul_of_pos_left (G.stationary_target_strict t (hs t) (hn t)) (G.stationary_pos t)

#print axioms capped_eq_survival_sum
#print axioms FirstStep.energy_gap
#print axioms FirstStep.degree_weighted_strict
#print axioms stationary_target_strict
#print axioms kemeny_nonbacktracking_lt_simple

end Network
end
end VertexHitting

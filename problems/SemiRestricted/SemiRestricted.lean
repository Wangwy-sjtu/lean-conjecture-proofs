import Mathlib.Data.Real.Sqrt
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Spiro–Surya–Zeng, semi-restricted games, Question 22. The restricted
player exposes a uniformly shuffled multiset. All individual copies are
labelled, and the opponent can use its entire observed action history. -/

namespace SemiRestricted
open Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {R C : Type*} [Fintype R]

/-- The expected payoff of a uniform draw from a finite set. -/
def avg (S : Finset C) (f : C → ℝ) : ℝ := (∑ x ∈ S, f x) / S.card

private lemma avg_const {S : Finset C} (hn : S.Nonempty) (b : ℝ) :
    avg S (fun _ => b) = b := by
  have h : (S.card : ℝ) ≠ 0 := by exact_mod_cast (Finset.card_pos.mpr hn).ne'
  simp [avg,h]

private lemma avg_add (S : Finset C) (f g : C → ℝ) :
    avg S (fun x => f x + g x) = avg S f + avg S g := by
  simp [avg,Finset.sum_add_distrib,add_div]

private lemma avg_mul (S : Finset C) (b : ℝ) (f : C → ℝ) :
    avg S (fun x => b*f x) = b*avg S f := by
  simp [avg, ← Finset.mul_sum,mul_div_assoc]

private lemma avg_sum (S : Finset C) (f : R → C → ℝ) :
    avg S (fun x => ∑ r, f r x) = ∑ r, avg S (f r) := by
  simp only [avg,div_eq_mul_inv, ← Finset.sum_mul]
  rw [Finset.sum_comm]

private lemma avg_mono {S : Finset C} {f g : C → ℝ} (h : ∀ x ∈ S, f x ≤ g x) :
    avg S f ≤ avg S g := div_le_div_of_nonneg_right (Finset.sum_le_sum h) (Nat.cast_nonneg _)

private lemma average_bounds {S : Finset C} (hn : S.Nonempty) (f : C → ℝ)
    (hf : ∀ x ∈ S, |f x| ≤ 1) : |avg S f| ≤ 1 := by
  apply abs_le.mpr
  constructor
  · rw [← avg_const hn (-1)]
    exact avg_mono (fun x hx => (abs_le.mp (hf x hx)).1)
  · rw [← avg_const hn 1]
    exact avg_mono (fun x hx => (abs_le.mp (hf x hx)).2)

private lemma avg_congr {S : Finset C} {f g : C → ℝ} (h : ∀ x ∈ S, f x = g x) :
    avg S f = avg S g := by rw [avg,avg,Finset.sum_congr rfl h]

variable [DecidableEq C]

/-- A stochastic strategy may use both players' complete public history, newest move first. -/
structure Policy (R C : Type*) [Fintype R] where
  prob : List (R × C) → R → ℝ
  nonneg : ∀ h a, 0 ≤ prob h a
  total : ∀ h, ∑ a, prob h a = 1

/-- A general legal policy for the player who must exhaust the deck.
    A zero-probability card is never drawn; every surviving card may have a distinct law. -/
structure DrawPolicy (R C : Type*) [DecidableEq C] where
  prob : List (R × C) → Finset C → C → ℝ
  nonneg : ∀ h S x, x ∈ S → 0 ≤ prob h S x
  total : ∀ h S, S.Nonempty → ∑ x ∈ S, prob h S x = 1

def uniform (R C : Type*) [DecidableEq C] : DrawPolicy R C where
  prob := fun _ S _ => ((S.card : ℝ))⁻¹
  nonneg := fun _ _ _ _ => by positivity
  total := by
    intro _ S hn
    have h : (S.card : ℝ) ≠ 0 := by exact_mod_cast (Finset.card_pos.mpr hn).ne'
    simp [h]

/-- Play exactly the given number of rounds. Starting at the deck size consumes
each individual card once. A new action and card are sampled independently given the past. -/
def score (pay : R → C → ℝ) (P : Policy R C) (D : DrawPolicy R C) :
    ℕ → Finset C → List (R × C) → ℝ
  | 0, _, _ => 0
  | t+1, S, h => ∑ a, P.prob h a * ∑ x ∈ S, D.prob h S x *
      (pay a x + score pay P D t (S.erase x) ((a,x)::h))

private lemma score_uniform_step (pay : R → C → ℝ) (P : Policy R C) (n : ℕ)
    (S : Finset C) (h : List (R × C)) :
    score pay P (uniform R C) (n+1) S h = ∑ a, P.prob h a *
      avg S (fun x => pay a x + score pay P (uniform R C) n (S.erase x) ((a,x)::h)) := by
  simp only [score,uniform,avg, ← Finset.mul_sum,div_eq_inv_mul]

private lemma mean_erase {S : Finset C} {n : ℕ} (hs : S.card = n+1) (hn : 0<n)
    (f : C → ℝ) {x : C} (hx : x ∈ S) :
    avg (S.erase x) f = avg S f + (avg S f - f x)/n := by
  have he : (S.erase x).card = n := by rw [Finset.card_erase_of_mem hx,hs]; omega
  have h0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have h1 : (n:ℝ)+1 ≠ 0 := by positivity
  have hsum := Finset.sum_erase_add _ f hx
  simp only [avg,he,hs,Nat.cast_add_one]
  field_simp
  nlinarith [congrArg (fun v : ℝ => v * (n:ℝ)) hsum]

private lemma variance_after_draw {S : Finset C} {n : ℕ} (hs : S.card = n+1)
    (hn : 0<n) (f : C → ℝ) (hf : ∀ x ∈ S, |f x|≤1) (c : ℝ) :
    avg S (fun x => (avg (S.erase x) f - c)^2) ≤
      (avg S f - c)^2 + 4/(n:ℝ)^2 := by
  have hS : S.Nonempty := Finset.card_pos.mp (by omega)
  let m := avg S f
  let d := fun x => (m-f x)/(n:ℝ)
  have hmean : avg S d = 0 := by
    have hi := avg_add S (fun _ => m/(n:ℝ)) (fun x => (-(n:ℝ)⁻¹) * f x)
    have hsame (x : C) : d x = m/(n:ℝ) + (-(n:ℝ)⁻¹)*f x := by dsimp [d]; ring
    calc
      _ = avg S (fun x => m/(n:ℝ) + (-(n:ℝ)⁻¹)*f x) := avg_congr (fun x _ => hsame x)
      _ = 0 := by rw [hi,avg_const hS,avg_mul]; dsimp [m]; ring
  have hd2 : avg S (fun x => (d x)^2) ≤ 4/(n:ℝ)^2 := by
    rw [← avg_const hS (4/(n:ℝ)^2)]
    apply avg_mono
    intro x hx
    have hm := abs_le.mp (average_bounds hS f hf)
    have hfx := abs_le.mp (hf x hx)
    have hlt : |m-f x| ≤ 2 := abs_le.mpr ⟨by dsimp[m];linarith,by dsimp[m];linarith⟩
    have hsq : (m-f x)^2 ≤ 4 := by
      nlinarith [sq_abs (m-f x),sq_nonneg (2-|m-f x|),
        mul_nonneg (sub_nonneg.mpr hlt) (show 0≤2+|m-f x| by positivity)]
    simpa only [d,div_pow] using (div_le_div_of_nonneg_right hsq (sq_nonneg (n:ℝ)))
  calc
    _ = avg S (fun x => ((m-c)^2 + (2*(m-c))*d x) + (d x)^2) := by
      apply avg_congr
      intro x hx
      rw [mean_erase hs hn f hx]
      dsimp [m,d]
      ring
    _ = (m-c)^2 + avg S (fun x => (d x)^2) := by
      rw [avg_add,avg_add,avg_const hS,avg_mul,hmean]
      ring
    _ ≤ _ := add_le_add_left hd2 _

/-- Per-action potential absorbs the sampling variance at every remaining deck size. -/
private lemma potential_step {n : ℕ} (hn : 0 < n) (d : ℝ) :
    |d| + (n:ℝ)*Real.sqrt n*(d^2+4/(n:ℝ)^2) + 15*Real.sqrt n ≤
      ((n:ℝ)+1)*Real.sqrt ((n:ℝ)+1)*d^2 + 15*Real.sqrt ((n:ℝ)+1) := by
  let x := Real.sqrt (n:ℝ)
  let y := Real.sqrt ((n:ℝ)+1)
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hx : 0 < x := Real.sqrt_pos.mpr (by linarith)
  have hx2 : x^2 = n := Real.sq_sqrt (by positivity)
  have hy : 0 ≤ y := Real.sqrt_nonneg _
  have hy2 : y^2 = (n:ℝ)+1 := Real.sq_sqrt (by positivity)
  have hxy : x ≤ y := Real.sqrt_le_sqrt (by linarith)
  have hyx : y ≤ 2*x := by
    by_contra! hh
    nlinarith [mul_pos (sub_pos.mpr hh) (show 0<y+2*x by positivity)]
  have hdelta : (y-x)*(x+y) = 1 := by nlinarith
  have hsmall : 1/x ≤ 3*(y-x) := by
    apply (div_le_iff₀ hx).mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr hxy) (show 0 ≤ 2*x-y by linarith)]
  have hYoung : |d| ≤ x*d^2 + 1/x := by
    have hmul : |d| * x ≤ x*d^2*x+1 := by
      rw [← sq_abs d]
      nlinarith [sq_nonneg (x*|d| - 1/2)]
    calc
      _ ≤ (x*d^2*x+1)/x := (le_div_iff₀ hx).mpr hmul
      _ = _ := by field_simp
  have hscale : (n:ℝ)*x * (4/(n:ℝ)^2) = 4/x := by
    rw [← hx2]
    field_simp
  change |d| + (n:ℝ)*x*(d^2+4/(n:ℝ)^2) + 15*x ≤ ((n:ℝ)+1)*y*d^2 + 15*y
  rw [mul_add,hscale,show 4/x = 4*(1/x) by ring]
  nlinarith [mul_nonneg (mul_nonneg (show 0 ≤ (n:ℝ)+1 by positivity) (sub_nonneg.mpr hxy)) (sq_nonneg d)]

private def budget (S : Finset C) (f : C → ℝ) (c : ℝ) : ℝ :=
  (S.card : ℝ)*Real.sqrt S.card*(avg S f-c)^2 + 15*Real.sqrt S.card

private lemma budget_after_draw {S : Finset C} {n : ℕ} (hs : S.card = n+1)
    (f : C → ℝ) (hf : ∀ x ∈ S, |f x| ≤ 1) (c : ℝ) :
    |avg S f-c| + avg S (fun x => budget (S.erase x) f c) ≤ budget S f c := by
  have hS : S.Nonempty := Finset.card_pos.mp (by omega)
  have hcard (x : C) (hx : x ∈ S) : (S.erase x).card = n := by
    rw [Finset.card_erase_of_mem hx,hs]; omega
  have havg : avg S (fun x => budget (S.erase x) f c) =
      (n:ℝ)*Real.sqrt n * avg S (fun x => (avg (S.erase x) f-c)^2) + 15*Real.sqrt n := by
    calc
      _ = avg S (fun x => (n:ℝ)*Real.sqrt n*(avg (S.erase x) f-c)^2 + 15*Real.sqrt n) :=
        avg_congr (fun x hx => by unfold budget; rw [hcard x hx])
      _ = _ := by rw [avg_add,avg_mul,avg_const hS]
  rw [havg,budget,hs,Nat.cast_add_one]
  obtain rfl | hn := Nat.eq_zero_or_pos n
  · simp
    nlinarith [sq_nonneg (|avg S f-c| - 1/2),sq_abs (avg S f-c)]
  · have hvar := variance_after_draw hs hn f hf c
    have hm := mul_le_mul_of_nonneg_left hvar (show 0 ≤ (n:ℝ)*Real.sqrt n by positivity)
    linarith [potential_step hn (avg S f-c)]

omit [DecidableEq C] in
private lemma mix_le (P : Policy R C) (h : List (R × C)) {F : R → ℝ} {b : ℝ}
    (hF : ∀ r, F r ≤ b) : ∑ r, P.prob h r * F r ≤ b := by
  calc
    _ ≤ ∑ r, P.prob h r*b := Finset.sum_le_sum (fun r _ =>
      mul_le_mul_of_nonneg_left (hF r) (P.nonneg h r))
    _ = b := by rw [← Finset.sum_mul,P.total,one_mul]

private theorem score_budget (pay : R → C → ℝ) (P : Policy R C)
    (c : R → ℝ) (b : ℝ) (hc : ∀ r, c r ≤ b) :
    ∀ n (S : Finset C), S.card = n → (∀ r x, x ∈ S → |pay r x|≤1) →
      ∀ h, score pay P (uniform R C) n S h ≤ (n:ℝ)*b + ∑ r, budget S (pay r) (c r) := by
  intro n
  induction n with
  | zero =>
    intro S hs _ h
    simp [score,budget,hs]
  | succ n ih =>
    intro S hs hf h
    have hS : S.Nonempty := Finset.card_pos.mp (by omega)
    rw [score_uniform_step]
    apply mix_le
    intro a
    have hnext (x : C) (hx : x ∈ S) :
        score pay P (uniform R C) n (S.erase x) ((a,x)::h) ≤
          (n:ℝ)*b + ∑ r, budget (S.erase x) (pay r) (c r) := by
      refine ih (S.erase x) ?_ (fun r y hy => hf r y (Finset.mem_of_mem_erase hy)) _
      rw [Finset.card_erase_of_mem hx,hs]; omega
    have hdev : avg S (pay a) ≤ b + ∑ r, |avg S (pay r)-c r| := by
      have hsingle : |avg S (pay a)-c a| ≤ ∑ r, |avg S (pay r)-c r| :=
        Finset.single_le_sum (fun r _ => abs_nonneg (avg S (pay r)-c r)) (Finset.mem_univ a)
      linarith [le_abs_self (avg S (pay a)-c a),hc a]
    have hsum := Finset.sum_le_sum (s:=Finset.univ) (fun r _ =>
      budget_after_draw hs (pay r) (hf r) (c r))
    rw [Finset.sum_add_distrib] at hsum
    calc
      _ ≤ avg S (fun x => pay a x + ((n:ℝ)*b+∑ r, budget (S.erase x) (pay r) (c r))) :=
        avg_mono (fun x hx => add_le_add_left (hnext x hx) _)
      _ = avg S (pay a) + ((n:ℝ)*b + ∑ r, avg S (fun x => budget (S.erase x) (pay r) (c r))) := by
        rw [avg_add,avg_add,avg_const hS,avg_sum]
      _ ≤ _ := by rw [Nat.cast_add_one]; linarith

/-- The guarantee holds against every history-dependent stochastic opponent and
even if the identity of every previously drawn individual card is disclosed. -/
theorem uniformly_shuffled_score_le (pay : R → C → ℝ) (S : Finset C) (P : Policy R C)
    (hf : ∀ r x, x ∈ S → |pay r x| ≤ 1) (b : ℝ) (hb : ∀ r, avg S (pay r) ≤ b)
    (h : List (R × C)) :
    score pay P (uniform R C) S.card S h ≤ (S.card:ℝ)*b +
      15*(Fintype.card R : ℝ)*Real.sqrt S.card := by
  have H := score_budget pay P (fun r => avg S (pay r)) b hb S.card S rfl hf h
  simpa [budget,Nat.cast_ofNat,mul_assoc,mul_left_comm,mul_comm] using H

variable {K : Type*}

/-- Public observations may discard the labels distinguishing copies of one type. -/
def observed (kind : C → K) (P : Policy R K) : Policy R C where
  prob h := P.prob (h.map (fun ax => (ax.1,kind ax.2)))
  nonneg _ := P.nonneg _
  total _ := P.total _

def fixed (a : R) (K : Type*) : Policy R K where
  prob _ r := if r=a then 1 else 0
  nonneg _ _ := by split <;> norm_num
  total _ := by simp

private theorem fixed_score (pay : R → C → ℝ) (D : DrawPolicy R C) (a : R) :
    ∀ n (S : Finset C), S.card = n → ∀ h,
      score pay (fixed a C) D n S h = ∑ x ∈ S, pay a x := by
  intro n
  induction n with
  | zero =>
    intro S hs h
    have he := Finset.card_eq_zero.mp hs
    simp [he,score]
  | succ n ih =>
    intro S hs h
    have hS : S.Nonempty := Finset.card_pos.mp (by omega)
    have branch (x : C) (hx : x ∈ S) :
        pay a x + score pay (fixed a C) D n (S.erase x) ((a,x)::h) = ∑ y ∈ S,pay a y := by
      rw [ih (S.erase x) (by rw [Finset.card_erase_of_mem hx,hs]; omega)]
      simpa only [add_comm] using Finset.sum_erase_add S (pay a) hx
    simp only [score,fixed,ite_mul,one_mul,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,if_true]
    calc
      _ = ∑ x ∈ S, D.prob h S x * (∑ y ∈ S,pay a y) :=
        Finset.sum_congr rfl (fun x hx => congrArg (D.prob h S x * ·) (branch x hx))
      _ = _ := by rw [← Finset.sum_mul,D.total h S hS,one_mul]

/-- Scores the restricted player can guarantee as upper bounds against every public-history policy. -/
def attainable (kind : C → K) (pay : R → C → ℝ) (S : Finset C) : Set ℝ :=
  {b | ∃ D : DrawPolicy R C, ∀ P : Policy R K, score pay (observed kind P) D S.card S [] ≤ b}

/-- The upper minimax value (restricted player minimizes the maximal expected score). -/
def value (kind : C → K) (pay : R → C → ℝ) (S : Finset C) : ℝ :=
  sInf (attainable kind pay S)

def bestFixed [Nonempty R] (pay : R → C → ℝ) (S : Finset C) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun r => ∑ x ∈ S, pay r x)

theorem matrix_game_sandwich [Nonempty R] (kind : C → K) (pay : R → C → ℝ)
    (S : Finset C) (hf : ∀ r x, x ∈ S → |pay r x| ≤ 1) :
    bestFixed pay S ≤ value kind pay S ∧ value kind pay S ≤
      bestFixed pay S + 15*(Fintype.card R:ℝ)*Real.sqrt S.card := by
  have lower : ∀ b ∈ attainable kind pay S, bestFixed pay S ≤ b := by
    rintro b ⟨D,hD⟩
    apply Finset.sup'_le
    intro a _
    have h := hD (fixed a K)
    change score pay (fixed a C) D S.card S [] ≤ b at h
    rwa [fixed_score pay D a S.card S rfl] at h
  have upper : bestFixed pay S + 15*(Fintype.card R:ℝ)*Real.sqrt S.card ∈ attainable kind pay S := by
    refine ⟨uniform R C,?_⟩
    intro P
    have row (a : R) : (∑ x ∈ S, pay a x) ≤ bestFixed pay S :=
      Finset.le_sup' (fun r => ∑ x ∈ S, pay r x) (Finset.mem_univ a)
    by_cases hn : S.Nonempty
    · have h0 : (0:ℝ) < S.card := by exact_mod_cast Finset.card_pos.mpr hn
      have hmean (a : R) : avg S (pay a) ≤ bestFixed pay S / S.card :=
        div_le_div_of_nonneg_right (row a) h0.le
      have H := uniformly_shuffled_score_le pay S (observed kind P) hf _ hmean []
      rwa [mul_div_cancel₀ _ h0.ne'] at H
    · have he := Finset.not_nonempty_iff_eq_empty.mp hn
      subst S
      simpa [score] using row (Classical.choice ‹Nonempty R›)
  exact ⟨le_csInf ⟨_,upper⟩ lower,csInf_le ⟨_,lower⟩ upper⟩

section Digraph
variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

/-- One individually labelled copy for each use granted in the restriction vector. -/
abbrev Card (r : V → ℕ) := Σ v : V, Fin (r v)

def arcPay (D : V → V → Prop) (a u : V) : ℝ :=
  (if D a u then 1 else 0) - (if D u a then 1 else 0)

def fixedScore (D : V → V → Prop) (r : V → ℕ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun a =>
    (∑ u ∈ Finset.univ.filter (D a), (r u : ℝ)) -
      ∑ u ∈ Finset.univ.filter (fun u => D u a), (r u : ℝ))

def digraphValue (D : V → V → Prop) (r : V → ℕ) : ℝ :=
  value Sigma.fst (fun a (i : Card r) => arcPay D a i.1) Finset.univ

omit [DecidableEq V] [Nonempty V] in
private lemma card_total (r : V → ℕ) : Fintype.card (Card r) = ∑ u, r u := by
  simp [Card,Fintype.card_sigma]

omit [DecidableEq V] in
private lemma baseline_digraph (D : V → V → Prop) (r : V → ℕ) :
    bestFixed (fun a (i : Card r) => arcPay D a i.1) Finset.univ = fixedScore D r := by
  unfold bestFixed fixedScore
  congr 1
  funext a
  rw [Fintype.sum_sigma]
  simp only [arcPay,Finset.sum_sub_distrib,Finset.sum_filter]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro u _ <;> split_ifs <;> simp

/-- Electronic Journal of Combinatorics 30(4), P4.32, Question 22. The explicit
constant depends only on the number of vertices. Any common upper bound on the
quotas can be used for M, including their maximum and the all-zero case. -/
theorem question22 (D : V → V → Prop) (r : V → ℕ) (M : ℕ) (hM : ∀ v, r v ≤ M) :
    fixedScore D r ≤ digraphValue D r ∧ digraphValue D r ≤
      fixedScore D r + (15*(Fintype.card V:ℝ)*Real.sqrt (Fintype.card V))*Real.sqrt M := by
  let pay := fun a (i : Card r) => arcPay D a i.1
  have hf (a : V) (x : Card r) (_ : x ∈ (Finset.univ : Finset (Card r))) : |pay a x| ≤ 1 := by
    dsimp [pay,arcPay]
    split_ifs <;> norm_num
  have H := matrix_game_sandwich Sigma.fst pay Finset.univ hf
  change bestFixed pay Finset.univ ≤ digraphValue D r ∧ digraphValue D r ≤ _ at H
  rw [show bestFixed pay Finset.univ = fixedScore D r from baseline_digraph D r,
    Finset.card_univ,card_total] at H
  have hs : ∑ v : V, r v ≤ Fintype.card V*M := by
    simpa using Finset.sum_le_sum (s:=Finset.univ) (fun v _ => hM v)
  have hreal : ((∑ v, r v : ℕ):ℝ) ≤ (Fintype.card V:ℝ)*(M:ℝ) := by exact_mod_cast hs
  have hb := Real.sqrt_le_sqrt hreal
  rw [Real.sqrt_mul (Nat.cast_nonneg _)] at hb
  refine ⟨H.1,H.2.trans ?_⟩
  rw [mul_assoc (15*(Fintype.card V:ℝ))]
  exact add_le_add_left (mul_le_mul_of_nonneg_left hb (by positivity)) _

end Digraph

#print axioms uniformly_shuffled_score_le
#print axioms matrix_game_sandwich
#print axioms question22

end
end SemiRestricted

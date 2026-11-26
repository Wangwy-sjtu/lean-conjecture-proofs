import BandOrBumpAll

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

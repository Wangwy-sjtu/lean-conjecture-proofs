import Mathlib.Data.Finset.Card
import Mathlib.Data.List.Infix
import Mathlib.Order.Bounds.Defs

/-!
# Distinct abelian-square factors in a binary word with four copies of one letter

Theorem `four_letter_minimum` answers the first unchecked letter multiplicity in
Section 6 of Fazekas, Mammoliti, Mercaş and Simpson, arXiv:2604.23188v1.
For `B ≥ 4` the minimum over words containing four a's and `B` b's is
`1 + (B + 2)/4` (natural division). The five run lengths below are arbitrary.
-/

namespace FourSquares

/-- Number of admissible sums of endpoint lengths of two-a squares
with internal b-run `g` and external b-run bounds `l` and `r`. -/
def capacity (l g r : ℕ) : ℕ :=
  (min (l + r) (min (2*l + g) (2*r + g)) + 2 - g % 2) / 2

private theorem capacity_cases {l g r h : ℕ} (hh : capacity l g r ≤ h) :
    l + r + 1 ≤ 2*h + g%2 ∨ 2*l + g + 1 ≤ 2*h + g%2 ∨ 2*r + g + 1 ≤ 2*h + g%2 := by
  unfold capacity at hh
  simp only [min_def] at hh
  split at hh <;> split at hh <;> omega

/-- The biggest b-run and one of the three two-a families give the
target for the minimum up to one. Each capacity has three linear cases. -/
theorem basic {a b c d e m h : ℕ}
    (ha : a ≤ m) (hb : b ≤ m) (hc : c ≤ m) (hd : d ≤ m) (he : e ≤ m)
    (h1 : capacity a b c ≤ h) (h2 : capacity b c d ≤ h) (h3 : capacity c d e ≤ h) :
    (a + b + c + d + e + 2)/4 ≤ m/2 + h := by
  rcases capacity_cases h1 with h1 | h1 | h1 <;>
    rcases capacity_cases h2 with h2 | h2 | h2 <;>
    rcases capacity_cases h3 with h3 | h3 | h3 <;> omega

theorem capacity_symm (l g r : ℕ) : capacity l g r = capacity r g l := by
  simp only [capacity, Nat.add_comm l r, Nat.min_comm (2*l+g) (2*r+g)]

/-- The cut between equal halves splits the middle run as `u + v`. -/
def FourPossible (a b c d e : ℕ) : Prop :=
  ∃ x z u v : ℕ, x ≤ a ∧ z ≤ e ∧ u+v=c ∧ x+b+u=v+d+z

theorem four_symm {a b c d e : ℕ} (h : FourPossible a b c d e) :
    FourPossible e d c b a := by
  obtain ⟨x,z,u,v,hx,hz,hc,he⟩ := h
  exact ⟨z,x,v,u,hz,hx,by omega,by omega⟩

/-- Two nonempty two-a families have different internal gaps. -/
def DistinctPositive (a b c d e : ℕ) : Prop :=
  (0 < capacity a b c ∧ 0 < capacity b c d ∧ b ≠ c) ∨
  (0 < capacity a b c ∧ 0 < capacity c d e ∧ b ≠ d) ∨
  (0 < capacity b c d ∧ 0 < capacity c d e ∧ c ≠ d)

theorem distinct_symm {a b c d e : ℕ} (h : DistinctPositive a b c d e) :
    DistinctPositive e d c b a := by
  unfold DistinctPositive at *
  rw [capacity_symm e d c, capacity_symm d c b, capacity_symm c b a]
  rcases h with h|h|h
  · exact Or.inr (Or.inr ⟨h.2.1,h.1,Ne.symm h.2.2⟩)
  · exact Or.inr (Or.inl ⟨h.2.1,h.1,Ne.symm h.2.2⟩)
  · exact Or.inl ⟨h.2.1,h.1,Ne.symm h.2.2⟩

private theorem cap_zero {l g r : ℕ} (h : capacity l g r = 0) :
    l=0 ∧ r=0 ∧ g%2=1 := by
  rcases capacity_cases (Nat.le_zero.mpr h) with h|h|h <;> omega

private theorem equal_outer (a g c e : ℕ) (h : c%2=0 ∨ 0<a ∨ 0<e) :
    FourPossible a g c g e := by
  by_cases he : c%2=0
  · exact ⟨0,0,c/2,c/2,by omega,by omega,by omega,by omega⟩
  rcases h with h|h|h
  · contradiction
  · exact ⟨1,0,c/2,c/2+1,by omega,by omega,by omega,by omega⟩
  · exact ⟨0,1,c/2+1,c/2,by omega,by omega,by omega,by omega⟩

private theorem disabled_left {a b c d e m h : ℕ}
    (hb : b ≤ m) (hd : d ≤ m) (he : e ≤ m)
    (h2 : capacity b c d ≤ h) (hz : capacity a b c=0)
    (hs : ¬DistinctPositive a b c d e) (hf : ¬FourPossible a b c d e) :
    1+(a+b+c+d+e+2)/4 ≤ m/2+h := by
  obtain ⟨rfl,rfl,hbOdd⟩ := cap_zero hz
  have pos : 0 < capacity b 0 d := by
    unfold capacity
    omega
  by_cases hzD : d=0
  · subst d
    have heb : e < b := by
      by_contra! h'
      exact hf ⟨0,b,0,0,by omega,h',by omega,by omega⟩
    omega
  have hz' : capacity 0 d e = 0 := by
    by_contra! h'
    exact hs (Or.inr (Or.inr ⟨pos,by omega,Ne.symm hzD⟩))
  obtain ⟨_,rfl,_⟩ := cap_zero hz'
  unfold capacity at h2
  simp only [Nat.zero_mod, Nat.sub_zero, Nat.add_zero, min_def] at h2
  split at h2 <;> split at h2 <;> omega

/-- When neither an additional gap nor a four-a square is available, the
biggest b-run and one two-a family already give the full lower bound. -/
theorem exceptional {a b c d e m h : ℕ}
    (ha : a ≤ m) (hb : b ≤ m) (hc : c ≤ m) (hd : d ≤ m) (he : e ≤ m)
    (hB : 4 ≤ a+b+c+d+e) (h2 : capacity b c d ≤ h)
    (hs : ¬DistinctPositive a b c d e) (hf : ¬FourPossible a b c d e) :
    1+(a+b+c+d+e+2)/4 ≤ m/2+h := by
  by_cases hbd : b=d
  · subst d
    have no : ¬(c%2=0 ∨ 0<a ∨ 0<e) := fun hh => hf (equal_outer a b c e hh)
    have az : a=0 := by omega
    have ez : e=0 := by omega
    subst a; subst e
    unfold capacity at h2
    simp only [min_self, min_def] at h2
    split at h2 <;> omega
  by_cases hc1 : capacity a b c = 0
  · exact disabled_left hb hd he h2 hc1 hs hf
  have hc3 : capacity c d e = 0 := by
    by_contra! hn
    exact hs (Or.inr (Or.inl ⟨by omega,by omega,hbd⟩))
  rw [capacity_symm] at hc3 h2
  have q := disabled_left hd hb ha h2 hc3 (fun q => hs (distinct_symm q))
    (fun q => hf (four_symm q))
  omega

/-- Different indices of this range yield two-a squares of different lengths. -/
theorem endpoints {l g r i : ℕ} (hi : i < capacity l g r) :
    ∃ x z u v : ℕ, x ≤ l ∧ z ≤ r ∧ x+z=2*i+g%2 ∧ u+v=g ∧ x+u=v+z := by
  let s := 2*i+g%2
  let t := (s+g)/2
  let x := max (s-r) (t-g)
  have h1 := Nat.min_le_left (l+r) (min (2*l+g) (2*r+g))
  have h2 := (Nat.min_le_right (l+r) (min (2*l+g) (2*r+g))).trans (Nat.min_le_left _ _)
  have h3 := (Nat.min_le_right (l+r) (min (2*l+g) (2*r+g))).trans (Nat.min_le_right _ _)
  unfold capacity at hi
  refine ⟨x,s-x,t-x,g-(t-x),?_,?_,?_,?_,?_⟩ <;>
    dsimp [x,s,t] <;> simp only [max_def] <;> split <;> omega

abbrev Word := List Bool
def bs (k : ℕ) : Word := List.replicate k false
def letter : Word := [true]

theorem bs_add (i j : ℕ) : bs (i+j) = bs i ++ bs j := List.replicate_add ..

def two (x g z : ℕ) : Word := bs x ++ letter ++ bs g ++ letter ++ bs z
def four (a b c d e : ℕ) : Word :=
  bs a ++ letter ++ bs b ++ letter ++ bs c ++ letter ++ bs d ++ letter ++ bs e

/-- Both coordinates of the half-word Parikh vectors are compared. -/
def IsAbelianSquare (s : Word) : Prop :=
  ∃ p q : Word, s=p++q ∧ 0<p.length ∧ p.length=q.length ∧
    p.count true=q.count true ∧ p.count false=q.count false

/-- Each distinct nonempty factor word is counted once. -/
noncomputable def squares (w : Word) : Finset Word := by
  classical
  exact (w.tails.flatMap List.inits).toFinset.filter IsAbelianSquare

theorem mem_squares {s w : Word} : s ∈ squares w ↔ s <:+: w ∧ IsAbelianSquare s := by
  simp only [squares, Finset.mem_filter, List.mem_toFinset, List.mem_flatMap,
    List.mem_tails, List.mem_inits, List.infix_iff_prefix_suffix]
  tauto

private theorem trim {x L z R : ℕ} (q : Word) (hx : x ≤ L) (hz : z ≤ R) :
    bs x ++ q ++ bs z <:+: bs L ++ q ++ bs R := by
  refine ⟨bs (L-x), bs (R-z), ?_⟩
  conv_rhs => rw [show L = (L-x)+x by omega, show R = z+(R-z) by omega, bs_add, bs_add z]
  simp [List.append_assoc]

theorem trim_two {x L g z R : ℕ} (hx : x ≤ L) (hz : z ≤ R) :
    two x g z <:+: two L g R := by
  simpa only [two,List.append_assoc] using trim (letter ++ bs g ++ letter) hx hz

theorem trim_four {x a b c d z e : ℕ} (hx : x ≤ a) (hz : z ≤ e) :
    four x b c d z <:+: four a b c d e := by
  simpa only [four,List.append_assoc] using trim (letter++bs b++letter++bs c++letter++bs d++letter) hx hz

theorem adjacent (a b c d e : ℕ) : two a b c <:+: four a b c d e ∧
    two b c d <:+: four a b c d e ∧ two c d e <:+: four a b c d e := by
  refine ⟨⟨[],letter++bs d++letter++bs e,?_⟩,
    ⟨bs a++letter,letter++bs e,?_⟩, ⟨bs a++letter++bs b++letter,[],?_⟩⟩ <;>
    simp [two,four,List.append_assoc]

theorem square_two {x g z u v : ℕ} (h : u+v=g) (he : x+u=v+z) : IsAbelianSquare (two x g z) := by
  subst g
  refine ⟨bs x++letter++bs u,bs v++letter++bs z,?_,?_,?_,?_,?_⟩
  · simp only [two, bs_add, List.append_assoc]
  all_goals simp [bs,letter,List.count_replicate] <;> omega

theorem square_four {x b c d z u v : ℕ} (h : u+v=c) (he : x+b+u=v+d+z) :
    IsAbelianSquare (four x b c d z) := by
  subst c
  refine ⟨bs x++letter++bs b++letter++bs u,bs v++letter++bs d++letter++bs z,?_,?_,?_,?_,?_⟩
  · simp only [four, bs_add, List.append_assoc]
  all_goals simp [bs,letter,List.count_replicate] <;> omega

private def leadingBs : Word → ℕ
  | false::s => leadingBs s+1
  | _ => 0

def innerGap : Word → ℕ
  | false::s => innerGap s
  | true::s => leadingBs s
  | [] => 0

private theorem leading_run (g : ℕ) (s : Word) : leadingBs (bs g ++ true::s) = g := by
  induction g with
  | zero => rfl
  | succ g ih => simpa [bs,List.replicate_succ,leadingBs] using ih

private theorem skip_run (g : ℕ) (s : Word) : innerGap (bs g ++ s) = innerGap s := by
  induction g with
  | zero => rfl
  | succ g ih => simpa [bs,List.replicate_succ,innerGap] using ih

@[simp] theorem gap_two (x g z : ℕ) : innerGap (two x g z) = g := by
  simp only [two,List.append_assoc,skip_run,letter,List.nil_append,List.cons_append,
    innerGap,leading_run]

@[simp] theorem count_two (x g z : ℕ) : (two x g z).count true=2 := by simp [two,bs,letter,List.count_replicate]
@[simp] theorem count_four (a b c d e : ℕ) : (four a b c d e).count true=4 := by simp [four,bs,letter,List.count_replicate]
@[simp] theorem len_two (x g z : ℕ) : (two x g z).length = x+g+z+2 := by
  simp [two,bs,letter]; omega

noncomputable def slice (w : Word) (j : ℕ) : Finset Word :=
  (squares w).filter fun s => s.count true=j

noncomputable def gapSlice (w : Word) (g : ℕ) : Finset Word :=
  (slice w 2).filter fun s => innerGap s=g

private theorem by_lengths (S : Finset Word) (k offset : ℕ)
    (h : ∀ i < k, ∃ s ∈ S, s.length=2*i+offset) : k ≤ S.card := by
  classical
  let f (i : ℕ) := if hi : i < k then (h i hi).choose else []
  have spec (i : ℕ) (hi : i < k) : f i ∈ S ∧ (f i).length=2*i+offset := by
    simpa [f,hi] using (h i hi).choose_spec
  apply Finset.le_card_of_inj_on_range f (fun i hi => (spec i hi).1)
  intro i hi j hj he
  have e := congrArg List.length he
  rw [(spec i hi).2,(spec j hj).2] at e
  omega

theorem pair_bound {w : Word} {L g R : ℕ} (ht : two L g R <:+: w) :
    capacity L g R ≤ (gapSlice w g).card := by
  apply by_lengths _ _ (g%2+g+2)
  intro i hi
  obtain ⟨x,z,u,v,hx,hz,hs,hg,he⟩ := endpoints hi
  refine ⟨two x g z,?_,by rw [len_two]; omega⟩
  simp only [gapSlice,slice,Finset.mem_filter,mem_squares,count_two,gap_two,and_true]
  exact ⟨(trim_two hx hz).trans ht,square_two hg he⟩

theorem zero_bound {w : Word} {m : ℕ} (ht : bs m <:+: w) : m/2 ≤ (slice w 0).card := by
  apply by_lengths _ _ 2
  intro i hi
  let j := i+1
  have hj : j+j ≤ m := by dsimp [j]; omega
  have hm : bs (j+j) <:+: bs m := by
    refine ⟨[],bs (m-(j+j)),?_⟩
    simp only [List.nil_append,←bs_add]
    congr 1; omega
  refine ⟨bs (j+j),?_,by simp [bs,j]; omega⟩
  simp only [slice,Finset.mem_filter,mem_squares]
  refine ⟨⟨hm.trans ht,bs j,bs j,bs_add j j,?_,rfl,rfl,rfl⟩,?_⟩
  · simp [bs,j]
  · simp [bs,List.count_replicate]

private theorem four_pos {a b c d e : ℕ} (h : FourPossible a b c d e) :
    0 < (slice (four a b c d e) 4).card := by
  obtain ⟨x,z,u,v,hx,hz,hm,he⟩ := h
  apply Finset.card_pos.mpr
  refine ⟨four x b c d z,?_⟩
  simp only [slice,Finset.mem_filter,mem_squares,count_four,and_true]
  exact ⟨trim_four hx hz,square_four hm he⟩

private theorem slice_disjoint (w : Word) {j k : ℕ} (hne : j ≠ k) :
    Disjoint (slice w j) (slice w k) := by
  apply Finset.disjoint_left.mpr
  intro s hs ht
  exact hne ((Finset.mem_filter.mp hs).2.symm.trans (Finset.mem_filter.mp ht).2)

private theorem sum_slices (w : Word) :
    (slice w 0).card + (slice w 2).card + (slice w 4).card ≤ (squares w).card := by
  have hal : Disjoint (slice w 0 ∪ slice w 2) (slice w 4) :=
    Finset.disjoint_union_left.mpr ⟨slice_disjoint _ (by decide),slice_disjoint _ (by decide)⟩
  rw [←Finset.card_union_of_disjoint (slice_disjoint w (by decide : 0≠2)),
    ←Finset.card_union_of_disjoint hal]
  apply Finset.card_le_card
  exact Finset.union_subset (Finset.union_subset (Finset.filter_subset ..) (Finset.filter_subset ..))
    (Finset.filter_subset ..)

private theorem other_gap {w : Word} {g d : ℕ} (hg : g ≠ d) (hp : 0 < (gapSlice w d).card) :
    (gapSlice w g).card < (slice w 2).card := by
  obtain ⟨s,hs⟩ := Finset.card_pos.mp hp
  apply Finset.card_lt_card (Finset.filter_ssubset.mpr ?_)
  have q := Finset.mem_filter.mp hs
  exact ⟨s,q.1,fun h => hg (h.symm.trans q.2)⟩

private theorem any_gap_strict {w : Word} {i j : ℕ} (hne : i ≠ j)
    (hi : 0 < (gapSlice w i).card) (hj : 0 < (gapSlice w j).card) (g : ℕ) :
    (gapSlice w g).card < (slice w 2).card := by
  by_cases h : g=i
  · subst g; exact other_gap hne hj
  · exact other_gap h hi

private theorem choose_max {P : ℕ → Prop} {a b : ℕ} (ha : P a) (hb : P b) : P (max a b) := by
  rcases le_total a b with h|h
  · simpa [max_eq_right h] using hb
  · simpa [max_eq_left h] using ha

theorem maxrun (a b c d e : ℕ) :
    bs (max a (max b (max c (max d e)))) <:+: four a b c d e := by
  let P (k : ℕ) := bs k <:+: four a b c d e
  have combine {i j : ℕ} (hi : P i) (hj : P j) : P (max i j) := choose_max (P:=P) hi hj
  refine combine ?_ (combine ?_ (combine ?_ (combine ?_ ?_)))
  · exact ⟨[],letter++bs b++letter++bs c++letter++bs d++letter++bs e,by simp [four,List.append_assoc]⟩
  · exact ⟨bs a++letter,letter++bs c++letter++bs d++letter++bs e,by simp [four,List.append_assoc]⟩
  · exact ⟨bs a++letter++bs b++letter,letter++bs d++letter++bs e,by simp [four,List.append_assoc]⟩
  · exact ⟨bs a++letter++bs b++letter++bs c++letter,letter++bs e,by simp [four,List.append_assoc]⟩
  · exact ⟨bs a++letter++bs b++letter++bs c++letter++bs d++letter,[],by simp [four,List.append_assoc]⟩

/-- Assemble disjoint sets of genuine factor words by their a-count,
internal b-gap and length. -/
theorem lower_runs (a b c d e : ℕ) (hB : 4 ≤ a+b+c+d+e) :
    1+(a+b+c+d+e+2)/4 ≤ (squares (four a b c d e)).card := by
  let w := four a b c d e
  let m := max a (max b (max c (max d e)))
  let h := max (capacity a b c) (max (capacity b c d) (capacity c d e))
  have M : a≤m ∧ b≤m ∧ c≤m ∧ d≤m ∧ e≤m := by dsimp [m]; omega
  have H : capacity a b c≤h ∧ capacity b c d≤h ∧ capacity c d e≤h := by dsimp [h]; omega
  obtain ⟨ma,mb,mc,md,me⟩ := M
  obtain ⟨h1,h2,h3⟩ := H
  obtain ⟨r1,r2,r3⟩ := adjacent a b c d e
  have c1 : capacity a b c ≤ (gapSlice w b).card := pair_bound r1
  have c2 : capacity b c d ≤ (gapSlice w c).card := pair_bound r2
  have c3 : capacity c d e ≤ (gapSlice w d).card := pair_bound r3
  have hc (g : ℕ) : (gapSlice w g).card ≤ (slice w 2).card := Finset.card_le_card (Finset.filter_subset ..)
  have hcount : h ≤ (slice w 2).card := max_le (c1.trans (hc b)) (max_le (c2.trans (hc c)) (c3.trans (hc d)))
  have zcount : m/2 ≤ (slice w 0).card := zero_bound (maxrun a b c d e)
  have tot := sum_slices w
  have base := basic ma mb mc md me h1 h2 h3
  change _ ≤ (squares w).card
  by_cases hf : FourPossible a b c d e
  · have big : 0 < (slice w 4).card := four_pos hf
    omega
  by_cases hs : DistinctPositive a b c d e
  · have H' (g : ℕ) : (gapSlice w g).card < (slice w 2).card := by
      rcases hs with h'|h'|h'
      · exact any_gap_strict h'.2.2 (h'.1.trans_le c1) (h'.2.1.trans_le c2) g
      · exact any_gap_strict h'.2.2 (h'.1.trans_le c1) (h'.2.1.trans_le c3) g
      · exact any_gap_strict h'.2.2 (h'.1.trans_le c2) (h'.2.1.trans_le c3) g
    have strict : h < (slice w 2).card := max_lt (c1.trans_lt (H' b)) (max_lt (c2.trans_lt (H' c)) (c3.trans_lt (H' d)))
    omega
  have ex := exceptional ma mb mc md me hB h2 hs hf
  omega

private def encode : ℕ → List ℕ → Word
  | a, [] => bs a
  | a, b::xs => bs a ++ true :: encode b xs

private theorem encode_succ (a : ℕ) (xs : List ℕ) : encode (a+1) xs = false :: encode a xs := by
  cases xs <;> simp [encode,bs,List.replicate_succ]

private theorem exists_encode (w : Word) : ∃ a xs, encode a xs=w := by
  induction w with
  | nil => exact ⟨0,[],rfl⟩
  | cons t w ih =>
    obtain ⟨a,xs,rfl⟩ := ih
    cases t with
    | false => exact ⟨a+1,xs,encode_succ ..⟩
    | true => exact ⟨0,a::xs,rfl⟩

private theorem count_encode (a : ℕ) (xs : List ℕ) : (encode a xs).count true=xs.length := by
  induction xs generalizing a with
  | nil => simp [encode,bs,List.count_replicate]
  | cons b xs ih => simp [encode,bs,List.count_replicate,ih]

theorem decompose (w : Word) (hw : w.count true=4) : ∃ a b c d e, w=four a b c d e := by
  obtain ⟨a,xs,rfl⟩ := exists_encode w
  rw [count_encode] at hw
  obtain ⟨b,c,d,e,rfl⟩ := List.length_eq_four.mp hw
  exact ⟨a,b,c,d,e,by simp [encode,four,letter,List.append_assoc]⟩

/-- First unhandled multiplicity in Section 6 of Fazekas–Mammoliti–Mercaş–Simpson.
`true` denotes a, `false` denotes b. This is the universal sharp lower bound. -/
theorem four_letter_lower_bound (w : Word) (ha : w.count true=4) (hb : 4 ≤ w.count false) :
    1+(w.count false+2)/4 ≤ (squares w).card := by
  obtain ⟨a,b,c,d,e,rfl⟩ := decompose w ha
  have eq : (four a b c d e).count false = a+b+c+d+e := by
    simp [four,bs,letter]; omega
  rw [eq] at hb ⊢
  exact lower_runs a b c d e hb

#print axioms four_letter_lower_bound

/-- The extremizer from the effective-word construction in source Theorem 12. -/
def effective (j h : ℕ) : Word := true :: (bs j ++ (List.replicate 3 true ++ bs h))

private def tally (j i : ℕ) := if i=0 then 0 else 1+min 3 (i-(j+1))

private theorem take_effective (j h i : ℕ) :
    ((effective j h).take i).count true = tally j i := by
  cases i with
  | zero => rfl
  | succ i =>
    simp only [effective,bs,List.take_succ_cons,List.count_cons_self,List.take_append,
      List.take_replicate,List.length_replicate,List.count_append,List.count_replicate]
    simp [tally,Nat.min_comm 3]; omega

private theorem tally_cases (j t : ℕ) :
    (t=0 ∧ tally j t=0) ∨ (1≤t ∧ t≤j+1 ∧ tally j t=1) ∨
    (j+1≤t ∧ t≤j+4 ∧ tally j t+j=t) ∨ (j+4≤t ∧ tally j t=4) := by
  unfold tally
  split <;> omega

private theorem midpoints {j h i k p u : ℕ} (hj : j%2=1) (hh : h<j)
    (hk : 0<k) (hend : i+2*k ≤ j+h+4) (ha : p=tally j i)
    (hb : p+u=tally j (i+k)) (hc : p+2*u=tally j (i+2*k)) :
    (u=0 ∧ 2*k≤j) ∨ (u=1 ∧ k=1) := by
  rcases tally_cases j i with H|H|H|H <;>
    rcases tally_cases j (i+k) with I|I|I|I <;>
    rcases tally_cases j (i+2*k) with J|J|J|J <;> omega

private theorem prefix_tally {j h : ℕ} (p r : Word) (he : effective j h=p++r) :
    p.count true=tally j p.length := by
  rw [←take_effective j h,he,List.take_left]

private theorem all_bs (s : Word) (hc : s.count true=0) : s=bs s.length := by
  apply List.eq_replicate_length.mpr
  intro t ht
  cases t with
  | false => rfl
  | true => exact False.elim ((List.count_eq_zero.mp hc) ht)

private theorem singleton_a (u : Word) (hlen : u.length=1) (hc : u.count true=1) : u=[true] := by
  obtain ⟨t,rfl⟩ := List.length_eq_one_iff.mp hlen
  cases t <;> simp_all

theorem effective_classification {j h : ℕ} (hj : j%2=1) (hh : h<j) {s : Word}
    (hs : s ∈ squares (effective j h)) :
    s=[true,true] ∨ ∃ k, 0<k ∧ 2*k≤j ∧ s=bs (2*k) := by
  obtain ⟨⟨p,r,hw⟩,u,v,rfl,hu,hv,ht,_⟩ := mem_squares.mp hs
  have pa := prefix_tally p (u++v++r) (by simpa [List.append_assoc] using hw.symm)
  have pb := prefix_tally (p++u) (v++r) (by simpa [List.append_assoc] using hw.symm)
  have pc := prefix_tally (p++u++v) r (by simpa [List.append_assoc] using hw.symm)
  simp only [List.count_append,List.length_append,←ht,←hv] at pb pc
  have he := congrArg List.length hw
  simp [effective,bs,←hv] at he
  have hc : p.count true+2*u.count true=tally j (p.length+2*u.length) := by
    simpa only [Nat.two_mul,Nat.add_assoc] using pc
  obtain ⟨ha,hlen⟩|⟨ha,hlen⟩ := midpoints hj hh hu (by omega) pa pb hc
  · right
    refine ⟨u.length,hu,hlen,?_⟩
    have hzero : (u++v).count true=0 := by simp [List.count_append,←ht,ha]
    have lengths : (u++v).length=2*u.length := by simp [←hv]; omega
    simpa only [lengths] using all_bs (u++v) hzero
  · left
    rw [singleton_a u hlen ha,singleton_a v (by omega) (by omega)]
    rfl

theorem effective_upper {j h : ℕ} (hj : j%2=1) (hh : h<j) :
    (squares (effective j h)).card ≤ 1+j/2 := by
  let G := (Finset.range (j/2)).image (fun i => bs (2*(i+1)))
  have sub : squares (effective j h) ⊆ insert [true,true] G := by
    intro s hs
    rcases effective_classification hj hh hs with h|⟨k,hk,hl,he⟩
    · exact Finset.mem_insert.mpr (Or.inl h)
    · apply Finset.mem_insert.mpr (Or.inr ?_)
      exact Finset.mem_image.mpr ⟨k-1,Finset.mem_range.mpr (by omega),by rw [he]; congr 2; omega⟩
  have hs := Finset.card_le_card sub
  have hi := Finset.card_insert_le [true,true] G
  have hg : G.card ≤ j/2 := (Finset.card_image_le).trans_eq (Finset.card_range _)
  omega

/-- Sharp minimum over all linear words with the prescribed two letter counts. -/
theorem four_letter_minimum (B : ℕ) (hB : 4≤B) :
    IsLeast {n : ℕ | ∃ w : Word, w.count true=4 ∧ w.count false=B ∧ (squares w).card=n}
      (1+(B+2)/4) := by
  let j := 2*((B+2)/4)+1
  let h := B-j
  have hj : j%2=1 := by dsimp [j]; omega
  have hh : h<j := by dsimp [h,j]; omega
  have ha : (effective j h).count true=4 := by simp [effective,bs,List.count_replicate]
  have hb : (effective j h).count false=B := by simp [effective,bs,h,j]; omega
  constructor
  · refine ⟨effective j h,ha,hb,?_⟩
    have lo := four_letter_lower_bound _ ha (by simpa only [hb] using hB)
    rw [hb] at lo
    have hi := effective_upper hj hh
    have eqj : j/2=(B+2)/4 := by dsimp [j]; omega
    rw [eqj] at hi
    exact le_antisymm hi lo
  · rintro n ⟨w,ha,hb,rfl⟩
    simpa only [hb] using four_letter_lower_bound w ha (by simpa only [hb] using hB)

#print axioms four_letter_minimum

end FourSquares

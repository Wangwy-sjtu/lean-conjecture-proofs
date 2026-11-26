import VisiblyPushdownSubtraction

/-! Remove the extra left cut. Here the domain of point variables is exactly
the ordinary letter positions `1,...,n`. In particular it is empty on the
empty word. The construction works in both directions of representability. -/
namespace WordSubtractionMSO

open Formula

def ordinary {A P V : Type} (M : Model A) (n : ℕ) (p : P → ℕ) (v : V → ℕ → Prop)
    (φ : Formula A P V) : Prop :=
  match φ with
  | .lt x y => p x < p y
  | .letter a x => M.letter (p x) a
  | .edge x y => M.edge (p x) (p y)
  | .mem x s => v s (p x)
  | .neg ψ => ¬ ordinary M n p v ψ
  | .conj ψ χ => ordinary M n p v ψ ∧ ordinary M n p v χ
  | .exPoint ψ => ∃ t, 0 < t ∧ t ≤ n ∧ ordinary M n (push t p) v ψ
  | .exSet ψ => ∃ s : ℕ → Prop, ordinary M n p (push s v) ψ

private def absurdF {A P V : Type} : Formula A P V := .exPoint (.lt none none)

private def truthF {A P V : Type} (b : Bool) : Formula A P V :=
  if b then .neg absurdF else absurdF

private def eitherF {A P V : Type} (φ ψ : Formula A P V) : Formula A P V :=
  .neg (.conj (.neg φ) (.neg ψ))

private theorem ordinary_truth {A P V : Type} (M : Model A) (n : ℕ) (p : P → ℕ)
    (v : V → ℕ → Prop) (b : Bool) : ordinary M n p v (truthF b) ↔ b = true := by
  cases b <;> simp [truthF, absurdF, ordinary, push]

private theorem ordinary_either {A P V : Type} (M : Model A) (n : ℕ) (p : P → ℕ)
    (v : V → ℕ → Prop) (φ ψ : Formula A P V) :
    ordinary M n p v (eitherF φ ψ) ↔ ordinary M n p v φ ∨ ordinary M n p v ψ := by
  classical
  by_cases h : ordinary M n p v φ <;> simp [eitherF, ordinary, h]

/-- Eliminate the initial cut. A missing first-order variable means the cut.
The single Boolean attached to each set records whether it contains that cut. -/
def removeCut {A P V Q W : Type} (φ : Formula A P V) (fp : P → Option Q)
    (fv : V → W) (bit : V → Bool) : Formula A Q W :=
  match φ with
  | .lt x y => match fp x, fp y with
    | none, some _ => truthF true
    | some x', some y' => .lt x' y'
    | _, none => truthF false
  | .letter a x => match fp x with
    | none => truthF false
    | some x' => .letter a x'
  | .edge x y => match fp x, fp y with
    | some x', some y' => .edge x' y'
    | _, _ => truthF false
  | .mem x s => match fp x with
    | none => truthF (bit s)
    | some x' => .mem x' (fv s)
  | .neg ψ => .neg (removeCut ψ fp fv bit)
  | .conj ψ χ => .conj (removeCut ψ fp fv bit) (removeCut χ fp fv bit)
  | .exPoint ψ => eitherF (removeCut ψ (push none fp) fv bit)
      (.exPoint (removeCut ψ (push (some none) (fun x => (fp x).map some)) fv bit))
  | .exSet ψ => .exSet (eitherF (removeCut ψ fp (Option.map fv) (push false bit))
      (removeCut ψ fp (Option.map fv) (push true bit)))

private theorem ordinary_removeCut {A P V : Type} (φ : Formula A P V) {Q W : Type}
    (fp : P → Option Q) (fv : V → W) (bit : V → Bool) (M : Model A) (n : ℕ)
    (p : P → ℕ) (q : Q → ℕ) (u : V → ℕ → Prop) (v : W → ℕ → Prop)
    (hp : ∀ x, p x = (fp x).elim 0 q) (hq : ∀ x, 0 < q x)
    (hz : ∀ s, u s 0 ↔ bit s = true) (hv : ∀ s i, 0 < i → (u s i ↔ v (fv s) i)) :
    ordinary M n q v (removeCut φ fp fv bit) ↔ Holds M 0 n p u φ := by
  classical
  induction φ generalizing Q W with
  | lt x y =>
    cases ex : fp x <;> cases ey : fp y <;>
      simp [removeCut, ex, ey, ordinary_truth, ordinary, Holds, hp, hq]
  | letter a x =>
    cases ex : fp x <;> simp [removeCut, ex, ordinary_truth, ordinary, Holds, hp, hq]
  | edge x y =>
    cases ex : fp x <;> cases ey : fp y <;>
      simp [removeCut, ex, ey, ordinary_truth, ordinary, Holds, hp, hq]
  | mem x s =>
    cases ex : fp x with
    | none => simpa [removeCut, ex, ordinary_truth, Holds, hp] using (hz s).symm
    | some y => simpa [removeCut, ex, ordinary, Holds, hp] using (hv s (q y) (hq y)).symm
  | neg ψ ih => exact not_congr (ih fp fv bit p q u v hp hq hz hv)
  | conj ψ χ ih jh =>
    exact and_congr (ih fp fv bit p q u v hp hq hz hv) (jh fp fv bit p q u v hp hq hz hv)
  | exPoint ψ ih =>
    rw [removeCut, ordinary_either]
    have atZ := ih (push none fp) fv bit (push 0 p) q u v
      (by rintro (_ | x); exact rfl; exact hp x) hq hz hv
    have atP (t) (ht : 0 < t) := ih
      (push (some none) (fun x => (fp x).map some)) fv bit (push t p) (push t q) u v
      (by
        rintro (_ | x)
        · rfl
        · cases e : fp x <;> simp [push, hp, e])
      (by rintro (_ | x); exact ht; exact hq x) hz hv
    constructor
    · rintro (h | ⟨t, ht, hu, h⟩)
      · exact ⟨0, le_rfl, Nat.zero_le _, atZ.mp h⟩
      · exact ⟨t, Nat.zero_le _, hu, (atP t ht).mp h⟩
    · rintro ⟨t, _, hu, h⟩
      by_cases ht : t = 0
      · subst t
        exact Or.inl (atZ.mpr h)
      · exact Or.inr ⟨t, by omega, hu, (atP t (by omega)).mpr h⟩
  | exSet ψ ih =>
    change (∃ t, ordinary M n q (push t v) (eitherF _ _)) ↔ (∃ s, _)
    have step (s t : ℕ → Prop) (b : Bool) (h0 : s 0 ↔ b = true)
        (hs : ∀ i, 0<i → (s i ↔ t i)) :=
      ih fp (Option.map fv) (push b bit) p q (push s u) (push t v) hp hq
        (by rintro (_ | x); exact h0; exact hz x)
        (by rintro (_ | x) i hi; exact hs i hi; exact hv x i hi)
    constructor
    · rintro ⟨t, h⟩
      rcases (ordinary_either _ _ _ _ _ _).mp h with h | h
      · let s : ℕ → Prop := fun i => 0 < i ∧ t i
        exact ⟨s, (step s t false (by simp [s]) (by intro i hi; simp [s, hi])).mp h⟩
      · let s : ℕ → Prop := fun i => i = 0 ∨ t i
        exact ⟨s, (step s t true (by simp [s]) (by intro i hi; simp [s, hi.ne'])).mp h⟩
    · rintro ⟨s, h⟩
      refine ⟨s, (ordinary_either _ _ _ _ _ _).mpr ?_⟩
      by_cases h0 : s 0
      · exact Or.inr ((step s s true (by simp [h0]) (fun _ _ => Iff.rfl)).mpr h)
      · exact Or.inl ((step s s false (by simp [h0]) (fun _ _ => Iff.rfl)).mpr h)

def onLetters {A : Type} (φ : Sentence A) : Sentence A :=
  removeCut φ Empty.elim Empty.elim Empty.elim

theorem onLetters_correct {A : Type} (φ : Sentence A) (M : Model A) (n : ℕ) :
    ordinary M n Empty.elim Empty.elim (onLetters φ) ↔ models φ M 0 n :=
  ordinary_removeCut φ Empty.elim Empty.elim Empty.elim M n Empty.elim Empty.elim
    Empty.elim Empty.elim (fun x => x.elim) (fun x => x.elim) (fun x => x.elim) (fun x => x.elim)

private def positivePoint {A P V : Type} (x : P) : Formula A P V :=
  .exPoint (.lt none (some x))

private theorem holds_positivePoint {A P V : Type} (M : Model A) (n : ℕ)
    (p : P → ℕ) (v : V → ℕ → Prop) (x : P) :
    Holds M 0 n p v (positivePoint x) ↔ 0 < p x := by
  change (∃ i, 0 ≤ i ∧ i ≤ n ∧ i < p x) ↔ _
  exact ⟨fun ⟨i,_,_,h⟩ => (Nat.zero_le i).trans_lt h, fun h => ⟨0, le_rfl, Nat.zero_le _, h⟩⟩

def addCut {A P V : Type} (φ : Formula A P V) : Formula A P V :=
  match φ with
  | .lt x y => .lt x y
  | .letter a x => .letter a x
  | .edge x y => .edge x y
  | .mem x s => .mem x s
  | .neg ψ => .neg (addCut ψ)
  | .conj ψ χ => .conj (addCut ψ) (addCut χ)
  | .exPoint ψ => .exPoint (.conj (positivePoint none) (addCut ψ))
  | .exSet ψ => .exSet (addCut ψ)

private theorem holds_addCut {A P V : Type} (φ : Formula A P V) (M : Model A) (n : ℕ)
    (p : P → ℕ) (v : V → ℕ → Prop) (hp : ∀ x, 0 < p x) :
    Holds M 0 n p v (addCut φ) ↔ ordinary M n p v φ := by
  induction φ with
  | lt => rfl
  | mem => rfl
  | letter => simp [addCut, Holds, ordinary, hp]
  | edge => simp [addCut, Holds, ordinary, hp]
  | neg ψ ih => exact not_congr (ih p v hp)
  | conj ψ χ ih jh => exact and_congr (ih p v hp) (jh p v hp)
  | exSet ψ ih => exact exists_congr (fun s => ih p (push s v) hp)
  | exPoint ψ ih =>
    change (∃ t, 0 ≤ t ∧ t ≤ n ∧ Holds M 0 n (push t p) v (positivePoint none) ∧ _) ↔
      (∃ t, 0 < t ∧ t ≤ n ∧ _)
    simp only [holds_positivePoint]
    constructor
    · rintro ⟨t, _, ht, hpos, body⟩
      exact ⟨t, hpos, ht, (ih (push t p) v (by rintro (_ | x); exact hpos; exact hp x)).mp body⟩
    · rintro ⟨t, hpos, ht, body⟩
      exact ⟨t, Nat.zero_le _, ht, hpos,
        (ih (push t p) v (by rintro (_ | x); exact hpos; exact hp x)).mpr body⟩

/-- VPL in the usual, unpadded letter-position semantics of nested-word MSO.
The formula reads the original alphabet, with its original, fixed visible partition. -/
def StandardVPL {A : Type} (kind : A → Kind) (L : List A → Prop) : Prop :=
  ∃ φ : Sentence A, ∀ (f : ℕ → A) (n : ℕ), L (segment f 0 n) ↔
    ordinary (wordModel (matched kind) f) n Empty.elim Empty.elim φ

theorem standardVPL_iff {A : Type} (kind : A → Kind) (L : List A → Prop) :
    StandardVPL kind L ↔ VisiblyPushdownLanguage kind L := by
  constructor
  · rintro ⟨φ, hf⟩
    exact ⟨addCut φ, fun f n => (hf f n).trans
      (holds_addCut φ _ n Empty.elim Empty.elim (fun x => x.elim)).symm⟩
  · rintro ⟨φ, hf⟩
    exact ⟨onLetters φ, fun f n => (hf f n).trans (onLetters_correct φ _ n).symm⟩

theorem standardVPL_losing_positions {A : Type} (kind : A → Kind) (S : List A → Prop)
    (h : StandardVPL kind S) : StandardVPL kind (losingPosition S) :=
  (standardVPL_iff _ _).mpr (visiblyPushdown_losing_positions kind S ((standardVPL_iff _ _).mp h))

theorem standardVPL_winning_positions {A : Type} (kind : A → Kind) (S : List A → Prop)
    (h : StandardVPL kind S) : StandardVPL kind (fun w => ¬losingPosition S w) :=
  (standardVPL_iff _ _).mpr (visiblyPushdown_winning_positions kind S ((standardVPL_iff _ _).mp h))

#print axioms standardVPL_losing_positions
#print axioms standardVPL_winning_positions

end WordSubtractionMSO

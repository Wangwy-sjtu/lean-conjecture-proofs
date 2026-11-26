import VisibleWords

/-! Inoue and Inazu, *Word Subtraction Games*, Problem 4.1. We use the MSO
characterization of visibly pushdown languages of Alur and Madhusudan.
The proof constructs the output sentence and starts from literal suffix removal. -/
namespace WordSubtractionMSO

/-- A position is losing when none of its nonempty allowed suffix deletions
leads to a losing position. This is the paper's normal-play P-position language. -/
def losingPosition {A : Type} (S : List A → Prop) (w : List A) : Prop :=
  ∀ (u v : List A), (_ : u.length < w.length) → w = u ++ v → S v → ¬ losingPosition S u
termination_by w.length

theorem losingPosition_iff {A : Type} (S : List A → Prop) (w : List A) :
    losingPosition S w ↔
      ∀ u v, v ≠ [] → w = u ++ v → S v → ¬ losingPosition S u := by
  rw [losingPosition]
  constructor
  · intro h u v hn he hs
    apply h u v _ he hs
    subst w
    simp only [List.length_append]
    have := List.length_pos_iff.mpr hn
    omega
  · intro h u v hl he hs
    apply h u v _ he hs
    rintro rfl
    simp only [List.append_nil] at he
    exact (Nat.lt_irrefl _) (he ▸ hl)

private theorem prefix_game {A : Type} {edgeWord S : List A → Prop} {rule : Sentence A}
    (h : Defines edgeWord S rule) (f : ℕ → A) (n : ℕ) :
    losingPosition S (segment f 0 n) ↔
      losesAt (fun i j => models rule (wordModel edgeWord f) i j) 0 n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [losingPosition, losesAt]
    constructor
    · intro native i _ hin legal losing
      have hij := defines_on_factor h f i n hin.le
      have hi : i + (n-i) = n := by omega
      have split := segment_append f 0 i (n-i)
      rw [hi, Nat.zero_add] at split
      exact native (segment f 0 i) (segment f i (n-i)) (by simpa using hin) split
        (hij.mpr legal) ((ih i hin).mpr losing)
    · intro cuts u v hu append legal losing
      have hin : u.length < n := by simpa using hu
      have len : u.length + (n-u.length) = n := by omega
      have split := segment_append f 0 u.length (n-u.length)
      rw [len, Nat.zero_add] at split
      have same := List.append_inj (append.symm.trans split) (by simp)
      have ruleH := (defines_on_factor h f u.length n hin.le).mp (same.2 ▸ legal)
      apply cuts u.length (Nat.zero_le _) hin ruleH
      apply (ih u.length hin).mp
      rwa [← same.1]

/-- Any rule definable on factors by MSO with a factor-local matching relation
has an effective, uniform sentence recognizing the native losing language. -/
theorem losing_defines {A : Type} {edgeWord S : List A → Prop} {rule : Sentence A}
    (h : Defines edgeWord S rule) : Defines edgeWord (losingPosition S) (losingSentence rule) := by
  intro f n
  exact (prefix_game h f n).trans (losingSentence_correct rule (wordModel edgeWord f) 0 n
    (Nat.zero_le _)).symm

/-- Standard logical characterization of VPLs over a fixed visibly partitioned
alphabet. On finite alphabets, this is equivalent to finite visibly pushdown
automata (Alur--Madhusudan, JACM 2009, Theorem 4.1 and Section 5.1). -/
def VisiblyPushdownLanguage {A : Type} (kind : A → Kind) (L : List A → Prop) : Prop :=
  ∃ φ : Sentence A, Defines (matched kind) L φ

theorem visiblyPushdown_losing_positions {A : Type} (kind : A → Kind) (S : List A → Prop)
    (h : VisiblyPushdownLanguage kind S) : VisiblyPushdownLanguage kind (losingPosition S) := by
  obtain ⟨rule, h⟩ := h
  exact ⟨losingSentence rule, losing_defines h⟩

theorem visiblyPushdown_winning_positions {A : Type} (kind : A → Kind) (S : List A → Prop)
    (h : VisiblyPushdownLanguage kind S) :
    VisiblyPushdownLanguage kind (fun w => ¬ losingPosition S w) := by
  obtain ⟨rule, h⟩ := visiblyPushdown_losing_positions kind S h
  exact ⟨.neg rule, fun f n => not_congr (h f n)⟩

#print axioms losing_defines
#print axioms visiblyPushdown_losing_positions
#print axioms visiblyPushdown_winning_positions

end WordSubtractionMSO

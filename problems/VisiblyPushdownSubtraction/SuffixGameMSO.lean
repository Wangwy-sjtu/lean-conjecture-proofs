import IntervalMSO

/-! A sentence defining the losing positions of every word-subtraction game whose
legal factors are given by a monadic second-order sentence. -/
namespace WordSubtractionMSO

open Formula

def factorAtom {A P V : Type} (rule : Sentence A) (left right : P) : Formula A P V :=
  onFactor rule Empty.elim Empty.elim left right

theorem holds_factorAtom {A P V : Type} (rule : Sentence A) (left right : P)
    (M : Model A) (lo hi : ℕ) (p : P → ℕ) (v : V → ℕ → Prop)
    (hl : lo ≤ p left) (hr : p right ≤ hi) :
    Holds M lo hi p v (factorAtom rule left right) ↔ models rule M (p left) (p right) := by
  have hp : p ∘ (Empty.elim : Empty → P) = Empty.elim := by funext x; exact x.elim
  have hv : v ∘ (Empty.elim : Empty → V) = Empty.elim := by funext x; exact x.elim
  simpa only [factorAtom, models, hp, hv] using
    holds_onFactor rule Empty.elim Empty.elim left right M lo hi p v hl hr

/-- At cut `j`, the set `s` must contain `j` exactly when no legal suffix leads to
an earlier cut in `s`. In the bound variables of `exPoint`, `none` is that earlier cut. -/
def previousPlayerAt {A P V : Type} (rule : Sentence A) (j : P) (s : V) : Formula A P V :=
  equiv (.mem j s) (.neg (.exPoint (.conj (.lt none (some j))
    (.conj (.mem none s) (factorAtom rule none (some j))))))

private theorem holds_previousPlayerAt {A P V : Type} (rule : Sentence A) (j : P) (s : V)
    (M : Model A) (lo hi : ℕ) (p : P → ℕ) (v : V → ℕ → Prop) (hj : p j ≤ hi) :
    Holds M lo hi p v (previousPlayerAt rule j s) ↔
      (v s (p j) ↔ ∀ i, lo ≤ i → i < p j → models rule M i (p j) → ¬ v s i) := by
  classical
  rw [previousPlayerAt, holds_equiv]
  apply iff_congr Iff.rfl
  change (¬ ∃ i, lo ≤ i ∧ i ≤ hi ∧ i < p j ∧ v s i ∧
      Holds M lo hi (push i p) v (factorAtom rule none (some j))) ↔ _
  constructor
  · intro absent i hiLo hiJ legal mark
    exact absent ⟨i, hiLo, hiJ.le.trans hj, hiJ, mark,
      (holds_factorAtom rule none (some j) M lo hi (push i p) v hiLo hj).mpr legal⟩
  · rintro h ⟨i, hiLo, _, hiJ, mark, legal⟩
    exact h i hiLo hiJ ((holds_factorAtom rule none (some j) M lo hi
      (push i p) v hiLo hj).mp legal) mark

def isLast {A P V : Type} (j : P) : Formula A P V := .neg (.exPoint (.lt (some j) none))

private theorem holds_isLast {A P V : Type} (M : Model A) (lo hi : ℕ)
    (p : P → ℕ) (v : V → ℕ → Prop) (j : P) (hlo : lo ≤ p j) (hhi : p j ≤ hi) :
    Holds M lo hi p v (isLast j) ↔ p j = hi := by
  change (¬ ∃ t, lo ≤ t ∧ t ≤ hi ∧ p j < t) ↔ _
  constructor
  · intro h
    by_contra he
    exact h ⟨hi, hlo.trans hhi, le_rfl, by omega⟩
  · rintro h ⟨t, _, ht, ht'⟩
    omega

def losingSentence {A : Type} (rule : Sentence A) : Sentence A :=
  .exSet (.conj (allPoint (previousPlayerAt rule none none))
    (.exPoint (.conj (isLast none) (.mem none none))))

/-- Normal play along word cuts. The empty prefix has no options, and every legal
move strictly decreases the cut. An edge `legal i j` removes the factor `(i,j]`. -/
def losesAt (legal : ℕ → ℕ → Prop) (lo j : ℕ) : Prop :=
  ∀ i, lo ≤ i → (_ : i < j) → legal i j → ¬ losesAt legal lo i
termination_by j

private theorem unique_mark (legal : ℕ → ℕ → Prop) (lo hi : ℕ) (mark : ℕ → Prop)
    (h : ∀ j, lo ≤ j → j ≤ hi →
      (mark j ↔ ∀ i, lo ≤ i → i < j → legal i j → ¬ mark i)) :
    ∀ j, lo ≤ j → j ≤ hi → (mark j ↔ losesAt legal lo j) := by
  intro j
  induction j using Nat.strong_induction_on with
  | h j ih =>
    intro hlj hjh
    rw [h j hlj hjh, losesAt]
    constructor
    · intro hm i hil hij he
      exact fun hp => hm i hil hij he ((ih i hij hil (hij.le.trans hjh)).mpr hp)
    · intro hm i hil hij he
      exact fun hp => hm i hil hij he ((ih i hij hil (hij.le.trans hjh)).mp hp)

theorem losingSentence_correct {A : Type} (rule : Sentence A) (M : Model A) (lo hi : ℕ)
    (h : lo ≤ hi) :
    models (losingSentence rule) M lo hi ↔ losesAt (fun i j => models rule M i j) lo hi := by
  classical
  change (∃ mark : ℕ → Prop, Holds M lo hi Empty.elim (push mark Empty.elim)
    (allPoint (previousPlayerAt rule none none)) ∧ ∃ j, lo ≤ j ∧ j ≤ hi ∧
      Holds M lo hi (push j Empty.elim) (push mark Empty.elim) (isLast none) ∧ mark j) ↔ _
  constructor
  · rintro ⟨mark, rec, j, hlj, hjh, last, member⟩
    have eqj := (holds_isLast M lo hi (push j Empty.elim) (push mark Empty.elim)
      none hlj hjh).mp last
    change j = hi at eqj
    subst j
    apply (unique_mark (fun i j => models rule M i j) lo hi mark ?_ hi h le_rfl).mp member
    intro k hk hk'
    exact (holds_previousPlayerAt rule none none M lo hi (push k Empty.elim)
      (push mark Empty.elim) hk').mp ((holds_allPoint _).mp rec k hk hk')
  · intro atLast
    let mark := losesAt (fun i j => models rule M i j) lo
    refine ⟨mark, (holds_allPoint _).mpr ?_, hi, h, le_rfl, ?_, atLast⟩
    · intro k _ hk
      apply (holds_previousPlayerAt rule none none M lo hi (push k Empty.elim)
        (push mark Empty.elim) hk).mpr
      change losesAt _ lo k ↔ ∀ i, lo ≤ i → i < k → _ → _
      rw [losesAt]
      rfl
    · exact (holds_isLast M lo hi (push hi Empty.elim) (push mark Empty.elim)
        none h le_rfl).mpr rfl

end WordSubtractionMSO

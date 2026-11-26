import Mathlib.Data.List.OfFn
import Mathlib.Tactic.Push

/-! Monadic second-order formulas on finite word intervals, with one left boundary cut.
Each noninitial cut names the letter immediately preceding it. Every interval keeps
its own initial cut, with neither a letter nor a matching edge at that cut. -/
namespace WordSubtractionMSO

structure Model (A : Type) where
  letter : ℕ → A → Prop
  edge : ℕ → ℕ → Prop

inductive Formula (A : Type) : Type → Type → Type 1 where
  | lt {P V} (x y : P) : Formula A P V
  | letter {P V} (a : A) (x : P) : Formula A P V
  | edge {P V} (x y : P) : Formula A P V
  | mem {P V} (x : P) (s : V) : Formula A P V
  | neg {P V} (φ : Formula A P V) : Formula A P V
  | conj {P V} (φ ψ : Formula A P V) : Formula A P V
  | exPoint {P V} (φ : Formula A (Option P) V) : Formula A P V
  | exSet {P V} (φ : Formula A P (Option V)) : Formula A P V

abbrev Sentence (A : Type) := Formula A Empty Empty

def push {I B : Type} (v : B) (f : I → B) : Option I → B
  | none => v
  | some x => f x

namespace Formula

def Holds {A P V : Type} (M : Model A) (lo hi : ℕ) (p : P → ℕ) (v : V → ℕ → Prop)
    (φ : Formula A P V) : Prop :=
  match φ with
  | .lt x y => p x < p y
  | .letter a x => lo < p x ∧ M.letter (p x) a
  | .edge x y => lo < p x ∧ lo < p y ∧ M.edge (p x) (p y)
  | .mem x s => v s (p x)
  | .neg ψ => ¬ Holds M lo hi p v ψ
  | .conj ψ χ => Holds M lo hi p v ψ ∧ Holds M lo hi p v χ
  | .exPoint ψ => ∃ t, lo ≤ t ∧ t ≤ hi ∧ Holds M lo hi (push t p) v ψ
  | .exSet ψ => ∃ s : ℕ → Prop, Holds M lo hi p (push s v) ψ

def allPoint {A P V : Type} (φ : Formula A (Option P) V) : Formula A P V :=
  .neg (.exPoint (.neg φ))

def equiv {A P V : Type} (φ ψ : Formula A P V) : Formula A P V :=
  .conj (.neg (.conj φ (.neg ψ))) (.neg (.conj ψ (.neg φ)))

theorem holds_allPoint {A P V : Type} {M : Model A} {lo hi : ℕ} {p : P → ℕ}
    {v : V → ℕ → Prop} (φ : Formula A (Option P) V) :
    Holds M lo hi p v (allPoint φ) ↔
      ∀ t, lo ≤ t → t ≤ hi → Holds M lo hi (push t p) v φ := by
  classical
  simp [allPoint, Holds]

theorem holds_equiv {A P V : Type} {M : Model A} {lo hi : ℕ} {p : P → ℕ}
    {v : V → ℕ → Prop} (φ ψ : Formula A P V) :
    Holds M lo hi p v (equiv φ ψ) ↔ (Holds M lo hi p v φ ↔ Holds M lo hi p v ψ) := by
  classical
  simp only [equiv, Holds, not_and, Classical.not_not]
  exact ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.mp, h.mpr⟩⟩

/-- Replace the word on which a formula is evaluated by the factor whose left and
right cuts are `left` and `right`. Fresh first- and second-order variables have
separate sorts. `Option.map` renames variables safely under each quantifier. -/
def onFactor {A P V : Type} (φ : Formula A P V) {Q W : Type}
    (fp : P → Q) (fv : V → W) (left right : Q) : Formula A Q W :=
  match φ with
  | .lt x y => .lt (fp x) (fp y)
  | .letter a x => .conj (.lt left (fp x)) (.letter a (fp x))
  | .edge x y => .conj (.lt left (fp x)) (.conj (.lt left (fp y)) (.edge (fp x) (fp y)))
  | .mem x s => .mem (fp x) (fv s)
  | .neg ψ => .neg (onFactor ψ fp fv left right)
  | .conj ψ χ => .conj (onFactor ψ fp fv left right) (onFactor χ fp fv left right)
  | .exPoint ψ => .exPoint (.conj (.neg (.lt none (some left)))
      (.conj (.neg (.lt (some right) none))
        (onFactor ψ (Option.map fp) fv (some left) (some right))))
  | .exSet ψ => .exSet (onFactor ψ fp (Option.map fv) left right)

private theorem push_comp {I J B : Type} (x : B) (f : J → B) (g : I → J) :
    push x f ∘ Option.map g = push x (f ∘ g) := by
  funext a
  cases a <;> rfl

theorem holds_onFactor {A P V : Type} (φ : Formula A P V) {Q W : Type}
    (fp : P → Q) (fv : V → W) (left right : Q) (M : Model A) (lo hi : ℕ)
    (p : Q → ℕ) (v : W → ℕ → Prop) (hl : lo ≤ p left) (hr : p right ≤ hi) :
    Holds M lo hi p v (onFactor φ fp fv left right) ↔
      Holds M (p left) (p right) (p ∘ fp) (v ∘ fv) φ := by
  induction φ generalizing Q W with
  | lt => rfl
  | mem => rfl
  | letter =>
    simp only [onFactor, Holds, Function.comp_apply]
    exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, hl.trans_lt h.1, h.2⟩⟩
  | edge =>
    simp only [onFactor, Holds, Function.comp_apply]
    exact ⟨fun h => ⟨h.1, h.2.1, h.2.2.2.2⟩,
      fun h => ⟨h.1, h.2.1, hl.trans_lt h.1, hl.trans_lt h.2.1, h.2.2⟩⟩
  | neg ψ ih => exact not_congr (ih fp fv left right p v hl hr)
  | conj ψ χ ih jh =>
    exact and_congr (ih fp fv left right p v hl hr) (jh fp fv left right p v hl hr)
  | exPoint ψ ih =>
    simp only [onFactor, Holds, not_lt, push]
    constructor
    · rintro ⟨t, _, _, ht, hu, h⟩
      refine ⟨t, ht, hu, ?_⟩
      have e := (ih (Option.map fp) fv (some left) (some right) (push t p) v hl hr).mp h
      simpa only [push_comp, push] using e
    · rintro ⟨t, ht, hu, h⟩
      refine ⟨t, hl.trans ht, hu.trans hr, ht, hu, ?_⟩
      apply (ih (Option.map fp) fv (some left) (some right) (push t p) v hl hr).mpr
      simpa only [push_comp, push] using h
  | exSet ψ ih =>
    change (∃ s, _) ↔ (∃ s, _)
    apply exists_congr
    intro s
    simpa only [push_comp] using ih fp (Option.map fv) left right p (push s v) hl hr

end Formula

def models {A : Type} (φ : Sentence A) (M : Model A) (lo hi : ℕ) : Prop :=
  Formula.Holds M lo hi Empty.elim Empty.elim φ

end WordSubtractionMSO

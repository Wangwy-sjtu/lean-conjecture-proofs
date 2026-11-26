import SuffixGameMSO

/-! The ordinary tagged-word presentation of visibly pushdown languages. The
matching relation is determined inside the interval between its endpoints,
so a pair survives passage to a factor exactly when both endpoints survive. -/
namespace WordSubtractionMSO

open Formula

def segment {A : Type} (f : ℕ → A) (left len : ℕ) : List A :=
  List.ofFn fun i : Fin len => f (left + i.val + 1)

@[simp] theorem segment_length {A : Type} (f : ℕ → A) (left len : ℕ) :
    (segment f left len).length = len := List.length_ofFn

theorem segment_append {A : Type} (f : ℕ → A) (left n m : ℕ) :
    segment f left (n+m) = segment f left n ++ segment f (left+n) m := by
  unfold segment
  rw [List.ofFn_add]
  congr 1
  apply congrArg List.ofFn
  funext i
  simp [Nat.add_assoc]

/-- Every concrete finite word has a stream presentation. Only its first `w.length`
letters will matter. `f 0` supplies no letter because cut zero is the left boundary. -/
theorem present_word {A : Type} (default : A) (w : List A) :
    ∃ f : ℕ → A, segment f 0 w.length = w := by
  refine ⟨fun k => w[k-1]?.getD default, ?_⟩
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp [segment]

inductive Kind where
  | call | ret | internal
  deriving DecidableEq

/-- The well-matched words, including internal letters, juxtaposition, and a
matched call/return enclosing another well-matched word. -/
inductive Balanced {A : Type} (kind : A → Kind) : List A → Prop where
  | nil : Balanced kind []
  | internal {a w} : kind a = .internal → Balanced kind w → Balanced kind (a :: w)
  | nest {c r u v} : kind c = .call → kind r = .ret → Balanced kind u → Balanced kind v →
      Balanced kind (c :: (u ++ r :: v))

def matched {A : Type} (kind : A → Kind) (w : List A) : Prop :=
  ∃ c u r, w = c :: (u ++ [r]) ∧ kind c = .call ∧ kind r = .ret ∧ Balanced kind u

/-- `edgeWord` is tested on the entire factor from the first endpoint through the
second. Tagged nesting uses `matched`; fixed-endpoint factor locality also holds
for every other predicate on that intervening word. -/
def wordModel {A : Type} (edgeWord : List A → Prop) (f : ℕ → A) : Model A where
  letter i a := f i = a
  edge i j := i < j ∧ edgeWord (f i :: segment f i (j-i))

private def shiftModel {A : Type} (M : Model A) (d : ℕ) : Model A where
  letter i a := M.letter (d+i) a
  edge i j := M.edge (d+i) (d+j)

private theorem wordModel_shift {A : Type} (edgeWord : List A → Prop) (f : ℕ → A) (d : ℕ) :
    wordModel edgeWord (fun i => f (d+i)) = shiftModel (wordModel edgeWord f) d := by
  unfold wordModel shiftModel
  congr 1
  funext i j
  change (i < j ∧ edgeWord (_ :: _)) = (d+i < d+j ∧ edgeWord (_ :: _))
  rw [show d+j-(d+i) = j-i by omega]
  simp [segment, Nat.add_assoc]

private theorem holds_shift {A P V : Type} (φ : Formula A P V) (M : Model A) (d lo hi : ℕ)
    (p q : P → ℕ) (u v : V → ℕ → Prop) (hp : ∀ x, q x = d+p x)
    (hv : ∀ x i, u x i ↔ v x (d+i)) :
    Holds (shiftModel M d) lo hi p u φ ↔ Holds M (d+lo) (d+hi) q v φ := by
  induction φ with
  | lt x y => simp only [Holds, hp, Nat.add_lt_add_iff_left]
  | letter a x => simp only [Holds, shiftModel, hp, Nat.add_lt_add_iff_left]
  | edge x y => simp only [Holds, shiftModel, hp, Nat.add_lt_add_iff_left]
  | mem x s => simpa only [Holds, hp] using hv s (p x)
  | neg ψ ih => exact not_congr (ih p q u v hp hv)
  | conj ψ χ ih jh => exact and_congr (ih p q u v hp hv) (jh p q u v hp hv)
  | exPoint ψ ih =>
    change (∃ t, _ ∧ _ ∧ _) ↔ (∃ t, _ ∧ _ ∧ _)
    constructor
    · rintro ⟨t, hl, hr, ht⟩
      refine ⟨d+t, by omega, by omega, (ih (push t p) (push (d+t) q) u v ?_ hv).mp ht⟩
      rintro (_ | x)
      · rfl
      · exact hp x
    · rintro ⟨t, hl, hr, ht⟩
      refine ⟨t-d, by omega, by omega, (ih (push (t-d) p) (push t q) u v ?_ hv).mpr ht⟩
      rintro (_ | x)
      · change t = d + (t-d)
        omega
      · exact hp x
  | exSet ψ ih =>
    change (∃ s, _) ↔ (∃ s, _)
    constructor
    · rintro ⟨s, hs⟩
      refine ⟨fun k => s (k-d), (ih p q (push s u) (push (fun k => s (k-d)) v) hp ?_).mp hs⟩
      rintro (_ | x) i
      · simp [push]
      · exact hv x i
    · rintro ⟨s, hs⟩
      refine ⟨fun k => s (d+k), (ih p q (push (fun k => s (d+k)) u) (push s v) hp ?_).mpr hs⟩
      rintro (_ | x) i
      · rfl
      · exact hv x i

theorem models_shift {A : Type} (φ : Sentence A) (edgeWord : List A → Prop)
    (f : ℕ → A) (d n : ℕ) :
    models φ (wordModel edgeWord (fun i => f (d+i))) 0 n ↔
      models φ (wordModel edgeWord f) d (d+n) := by
  rw [wordModel_shift]
  simpa only [Nat.add_zero] using holds_shift φ (wordModel edgeWord f) d 0 n
    Empty.elim Empty.elim Empty.elim Empty.elim (fun x => x.elim) (fun x => x.elim)

/-- Recognition on every finite input, with its left boundary cut distinguished.
Every concrete word over a nonempty alphabet has such a presentation (`present_word`). -/
def Defines {A : Type} (edgeWord L : List A → Prop) (rule : Sentence A) : Prop :=
  ∀ (f : ℕ → A) (n : ℕ), L (segment f 0 n) ↔ models rule (wordModel edgeWord f) 0 n

theorem defines_on_factor {A : Type} {edgeWord L : List A → Prop} {rule : Sentence A}
    (h : Defines edgeWord L rule) (f : ℕ → A) (i j : ℕ) (hij : i ≤ j) :
    L (segment f i (j-i)) ↔ models rule (wordModel edgeWord f) i j := by
  have post := (h (fun k => f (i+k)) (j-i)).trans (models_shift rule edgeWord f i (j-i))
  have hi : i + (j-i) = j := by omega
  simpa only [segment, Nat.zero_add, Nat.add_assoc, hi] using post

end WordSubtractionMSO

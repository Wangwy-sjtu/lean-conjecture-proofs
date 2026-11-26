import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Tactic.ByContra
import Mathlib.Algebra.Order.Ring.Unbundled.Basic
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Tactic.Ring

/-!
# A large Nim heap in a selective compound

An impartial normal-play ruleset is specified by its finite legal option sets
and a well-founded move relation. The depth and the Sprague–Grundy function
below are computed from this relation itself.
-/

namespace SelectiveCompound

open Finset
noncomputable section

private theorem missing (s : Finset ℕ) : ∃ n, n ∉ s := by
  refine ⟨s.sup id + 1, fun h => ?_⟩
  have h' : s.sup id + 1 ≤ s.sup id := Finset.le_sup (f := id) h
  omega

/-- The least natural number outside a finite set. -/
def mex (s : Finset ℕ) : ℕ := Nat.find (missing s)

theorem mex_notMem (s : Finset ℕ) : mex s ∉ s := Nat.find_spec (missing s)

theorem mem_of_lt_mex {s : Finset ℕ} {v : ℕ} (h : v < mex s) : v ∈ s :=
  by_contra fun hn => Nat.find_min (missing s) h hn

theorem mex_le_of_notMem {s : Finset ℕ} {v : ℕ} (h : v ∉ s) : mex s ≤ v :=
  Nat.find_min' (missing s) h

theorem mex_le_card (s : Finset ℕ) : mex s ≤ s.card := by
  have hs : Finset.range (mex s) ⊆ s := fun _ hm =>
    mem_of_lt_mex (Finset.mem_range.mp hm)
  simpa using Finset.card_le_card hs

universe u

/-- A finitely branching impartial game with no infinite sequence of moves. -/
structure Game (α : Type u) where
  moves : α → Finset α
  terminates : WellFounded (fun b a => b ∈ moves a)

namespace Game

variable {α : Type u} (G : Game α)

/-- Maximum possible number of remaining turns from this position. -/
def depth : α → ℕ :=
  G.terminates.fix fun a ih => (G.moves a).attach.sup (fun b => ih b.1 b.2 + 1)

theorem depth_eq (a : α) :
    G.depth a = (G.moves a).sup (fun b => G.depth b + 1) := by
  change G.terminates.fix _ a = _
  rw [WellFounded.fix_eq]
  exact Finset.sup_attach (G.moves a) (fun b => G.depth b + 1)

theorem depth_lt_of_move {a b : α} (hb : b ∈ G.moves a) :
    G.depth b < G.depth a := by
  rw [G.depth_eq a]
  exact Finset.le_sup (f := fun b => G.depth b + 1) hb

theorem exists_deepest_move {a : α} {d : ℕ} (h : G.depth a = d + 1) :
    ∃ b ∈ G.moves a, G.depth b = d := by
  have hn : (G.moves a).Nonempty := by
    by_contra hnone
    have he := Finset.not_nonempty_iff_eq_empty.mp hnone
    rw [G.depth_eq, he] at h
    simp at h
  obtain ⟨b, hb, hmax⟩ := Finset.exists_mem_eq_sup (G.moves a) hn (fun b => G.depth b + 1)
  rw [← G.depth_eq, h] at hmax
  exact ⟨b, hb, by omega⟩

/-- The ordinary normal-play nimber, recursively the mex of the option nimbers. -/
def grundy : α → ℕ :=
  G.terminates.fix fun a ih => mex ((G.moves a).attach.image (fun b => ih b.1 b.2))

theorem grundy_eq (a : α) :
    G.grundy a = mex ((G.moves a).image G.grundy) := by
  classical
  change G.terminates.fix _ a = _
  rw [WellFounded.fix_eq]
  congr 1
  ext v
  simp [grundy]

theorem grundy_ne_of_move {a b : α} (hb : b ∈ G.moves a) :
    G.grundy a ≠ G.grundy b := by
  intro h
  have hm : G.grundy a ∈ (G.moves a).image G.grundy :=
    Finset.mem_image.mpr ⟨b, hb, h.symm⟩
  rw [G.grundy_eq a] at hm
  exact mex_notMem _ hm

theorem reachable_of_lt_grundy {a : α} {v : ℕ} (h : v < G.grundy a) :
    ∃ b ∈ G.moves a, G.grundy b = v := by
  rw [G.grundy_eq] at h
  exact Finset.mem_image.mp (mem_of_lt_mex h)

theorem grundy_le_move_count (a : α) : G.grundy a ≤ (G.moves a).card := by
  rw [G.grundy_eq]
  exact (mex_le_card _).trans Finset.card_image_le

theorem grundy_le_depth (a : α) : G.grundy a ≤ G.depth a := by
  induction a using G.terminates.induction with
  | h a ih =>
    rw [G.grundy_eq]
    apply mex_le_of_notMem
    intro hmem
    obtain ⟨b, hb, hv⟩ := Finset.mem_image.mp hmem
    have h₁ := ih b hb
    have h₂ := G.depth_lt_of_move hb
    omega

/-- The first set consists of Nim-only moves. The second permits a move in
the original game with the heap either retained or reduced. -/
def compoundMoves [DecidableEq α] (p : α × ℕ) : Finset (α × ℕ) :=
  ({p.1} ×ˢ Finset.range p.2) ∪ ((G.moves p.1) ×ˢ Finset.range (p.2 + 1))

theorem compoundMoves_iff [DecidableEq α] {a b : α} {j k : ℕ} :
    (b, j) ∈ G.compoundMoves (a, k) ↔
    (b = a ∧ j < k) ∨ (b ∈ G.moves a ∧ j ≤ k) := by
  simp [compoundMoves, Nat.lt_succ_iff, and_comm, eq_comm]

/-- The game obtained by adjoining a selectively playable Nim heap. -/
def withHeap [DecidableEq α] : Game (α × ℕ) where
  moves := G.compoundMoves
  terminates := by
    apply Subrelation.wf (r := (measure (fun p : α × ℕ => G.depth p.1 + p.2)).rel) _ (measure _).wf
    rintro ⟨b, j⟩ ⟨a, k⟩ hm
    change G.depth b + j < G.depth a + k
    rcases G.compoundMoves_iff.mp hm with ⟨rfl, hj⟩ | ⟨hb, hj⟩
    · omega
    · have := G.depth_lt_of_move hb
      omega

variable [DecidableEq α]

theorem withHeap_move_iff {a b : α} {j k : ℕ} :
    (b, j) ∈ G.withHeap.moves (a, k) ↔
    (b = a ∧ j < k) ∨ (b ∈ G.moves a ∧ j ≤ k) := G.compoundMoves_iff

theorem value_lt_succ (a : α) (k : ℕ) :
    G.withHeap.grundy (a, k) < G.withHeap.grundy (a, k + 1) := by
  by_contra! h
  rcases lt_or_eq_of_le h with hl | he
  · obtain ⟨⟨b,j⟩, hm, hj⟩ := G.withHeap.reachable_of_lt_grundy hl
    have hm' : (b,j) ∈ G.withHeap.moves (a,k+1) := by
      apply G.withHeap_move_iff.mpr
      rcases G.withHeap_move_iff.mp hm with ⟨rfl, h⟩ | ⟨hb, h⟩
      · exact Or.inl ⟨rfl, by omega⟩
      · exact Or.inr ⟨hb, by omega⟩
    exact G.withHeap.grundy_ne_of_move hm' hj.symm
  · exact G.withHeap.grundy_ne_of_move (G.withHeap_move_iff.mpr (Or.inl ⟨rfl, Nat.lt_succ_self k⟩)) he

theorem heap_le_value (a : α) (k : ℕ) :
    k ≤ G.withHeap.grundy (a,k) := by
  induction k with
  | zero => exact Nat.zero_le _
  | succ k ih => exact Nat.succ_le_of_lt (lt_of_le_of_lt ih (G.value_lt_succ a k))

/-- Longest plays can spend all turns in the two components separately. -/
theorem withHeap_depth (a : α) (k : ℕ) :
    G.withHeap.depth (a,k) = k + G.depth a := by
  suffices allp : ∀ p : α × ℕ, G.withHeap.depth p = p.2 + G.depth p.1 from allp (a,k)
  intro p
  induction p using G.withHeap.terminates.induction with
  | h p ih =>
    obtain ⟨a,k⟩ := p
    change G.withHeap.depth (a,k) = k + G.depth a
    apply Nat.le_antisymm
    · rw [G.withHeap.depth_eq]
      apply Finset.sup_le
      rintro ⟨b,j⟩ hm
      rw [ih _ hm]
      change j + G.depth b + 1 ≤ k + G.depth a
      rcases G.withHeap_move_iff.mp hm with ⟨rfl, hj⟩ | ⟨hb, hj⟩
      · omega
      · have := G.depth_lt_of_move hb
        omega
    · cases k with
      | succ k =>
        have hm : (a,k) ∈ G.withHeap.moves (a,k+1) :=
          G.withHeap_move_iff.mpr (Or.inl ⟨rfl, Nat.lt_succ_self k⟩)
        have hlt := G.withHeap.depth_lt_of_move hm
        rw [ih _ hm] at hlt
        simpa [Nat.succ_add] using hlt
      | zero =>
        cases hd : G.depth a with
        | zero => simp
        | succ n =>
          obtain ⟨b, hb, hd'⟩ := G.exists_deepest_move hd
          have hm : (b,0) ∈ G.withHeap.moves (a,0) :=
            G.withHeap_move_iff.mpr (Or.inr ⟨hb, le_refl 0⟩)
          have hlt := G.withHeap.depth_lt_of_move hm
          rw [ih _ hm] at hlt
          simpa [hd'] using hlt

/-- The printed Question 3 holds at every fixed position, with a threshold
depending only on the maximum length of a play from the position. -/
theorem large_heap_grundy (a : α) (k : ℕ) (hk : (G.depth a).choose 2 ≤ k) :
    G.withHeap.grundy (a,k) = k + G.depth a := by
  suffices aux : ∀ d : ℕ, ∀ a : α, G.depth a = d →
      ∀ k : ℕ, d.choose 2 ≤ k → G.withHeap.grundy (a,k) = k + d from
    aux (G.depth a) a rfl k hk
  intro d
  induction d with
  | zero =>
    intro a hd k _
    have lower := G.heap_le_value a k
    have upper := G.withHeap.grundy_le_depth (a,k)
    rw [G.withHeap_depth, hd] at upper
    omega
  | succ d ih =>
    intro a hd k hk
    obtain ⟨b, hb, hd'⟩ := G.exists_deepest_move hd
    have upper := G.withHeap.grundy_le_depth (a,k)
    rw [G.withHeap_depth, hd] at upper
    have lower := G.heap_le_value a k
    have hchoose : (d+1).choose 2 = d + d.choose 2 := by
      simpa using Nat.choose_succ_succ d 1
    rw [hchoose] at hk
    by_contra hne
    let j := G.withHeap.grundy (a,k) - d
    have hj : j ≤ k := by dsimp [j]; omega
    have hcut : d.choose 2 ≤ j := by dsimp [j]; omega
    have hjv := ih b hd' j hcut
    have hm : (b,j) ∈ G.withHeap.moves (a,k) :=
      G.withHeap_move_iff.mpr (Or.inr ⟨hb, hj⟩)
    apply G.withHeap.grundy_ne_of_move hm
    rw [hjv]
    dsimp [j]
    omega

theorem fixed_position_threshold (a : α) :
    ∃ cutoff : ℕ, ∀ k > cutoff, G.withHeap.grundy (a,k) = k + G.depth a :=
  ⟨(G.depth a).choose 2, fun k hk => G.large_heap_grundy a k (Nat.le_of_lt hk)⟩

/-- There are k heap-only moves and at most k+1 moves for every original option. -/
theorem grundy_le_degree_bound (a : α) (k : ℕ) :
    G.withHeap.grundy (a,k) ≤ k + (G.moves a).card * (k+1) := by
  apply (G.withHeap.grundy_le_move_count _).trans
  change (G.compoundMoves (a,k)).card ≤ _
  unfold compoundMoves
  apply (Finset.card_union_le _ _).trans
  simp

/-- For an entire ruleset of uniformly bounded outdegree, a common heap cutoff
exists exactly when the lengths of plays are uniformly bounded. -/
theorem uniform_cutoff_iff_bounded_depth {M : ℕ} (hM : ∀ a, (G.moves a).card ≤ M) :
    (∃ K : ℕ, ∀ k ≥ K, ∀ a : α, G.withHeap.grundy (a,k) = k + G.depth a) ↔
    ∃ D : ℕ, ∀ a : α, G.depth a ≤ D := by
  constructor
  · rintro ⟨K, hK⟩
    refine ⟨M*(K+1), fun a => ?_⟩
    have h := G.grundy_le_degree_bound a K
    rw [hK K (le_refl K) a] at h
    exact (Nat.le_of_add_le_add_left h).trans (Nat.mul_le_mul_right _ (hM a))
  · rintro ⟨D, hD⟩
    exact ⟨D.choose 2, fun k hk a =>
      G.large_heap_grundy a k ((Nat.choose_le_choose _ (hD a)).trans hk)⟩

end Game

/-- Subtraction by exactly one, with position n having n moves left. -/
def takeOne : Game ℕ where
  moves
    | 0 => ∅
    | n + 1 => {n}
  terminates := by
    apply Subrelation.wf (r := (· < ·)) _ Nat.lt_wfRel.wf
    intro b a hm
    cases a with
    | zero => simp at hm
    | succ n => have : b = n := Finset.mem_singleton.mp hm; omega

theorem takeOne_depth (n : ℕ) : takeOne.depth n = n := by
  induction n with
  | zero => rw [Game.depth_eq]; rfl
  | succ n ih =>
    rw [Game.depth_eq]
    change ({n} : Finset ℕ).sup (fun a => takeOne.depth a + 1) = n + 1
    simp [ih]

theorem takeOne_grundy_le (n k : ℕ) :
    takeOne.withHeap.grundy (n,k) ≤ 2*k+1 := by
  apply (takeOne.grundy_le_degree_bound n k).trans
  cases n <;> simp [takeOne] <;> omega

/-- Every fixed heap fails to attain depth on the explicit longer path k+2. -/
theorem takeOne_fails_uniformly (k : ℕ) :
    takeOne.withHeap.grundy (k+2,k) < k + takeOne.depth (k+2) := by
  have := takeOne_grundy_le (k+2) k
  rw [takeOne_depth]
  omega

/-- The inverse quantifier order already fails for the one-step subtraction rule. -/
theorem no_uniform_cutoff_for_takeOne :
    ¬ ∃ cutoff : ℕ, ∀ k > cutoff, ∀ n : ℕ,
      takeOne.withHeap.grundy (n,k) = k + takeOne.depth n := by
  rintro ⟨c,h⟩
  have he := h (c+1) (Nat.lt_succ_self _) (c+1+2)
  exact (takeOne_fails_uniformly (c+1)).ne he

#print axioms Game.withHeap_depth
#print axioms Game.large_heap_grundy
#print axioms Game.fixed_position_threshold
#print axioms Game.uniform_cutoff_iff_bounded_depth
#print axioms no_uniform_cutoff_for_takeOne

end
end SelectiveCompound

namespace SelectiveCompound
namespace QuadraticFamily

open Finset
noncomputable section

/-- A pile of up to m stones is ordinary Nim. Above it, each turn is forced
to remove exactly one stone until the ordinary Nim part has been reached. -/
def stack (m : ℕ) : Game ℕ where
  moves n := if n ≤ m then Finset.range n else {n-1}
  terminates := by
    apply Subrelation.wf (r := (· < ·)) _ Nat.lt_wfRel.wf
    intro b a h
    split at h
    · exact Finset.mem_range.mp h
    · have := Finset.mem_singleton.mp h
      omega

theorem stack_move_lt {m a b : ℕ} (h : b ∈ (stack m).moves a) : b < a := by
  change b ∈ (if a ≤ m then Finset.range a else {a-1}) at h
  split at h
  · exact Finset.mem_range.mp h
  · have := Finset.mem_singleton.mp h
    omega

theorem predecessor_move (m n : ℕ) : n ∈ (stack m).moves (n+1) := by
  by_cases h : n+1 ≤ m <;> simp [stack, h]

theorem stack_depth (m n : ℕ) : (stack m).depth n = n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    apply Nat.le_antisymm
    · rw [Game.depth_eq]
      apply Finset.sup_le
      intro b hb
      have hlt := stack_move_lt hb
      rw [ih b hlt]
      omega
    · cases n with
      | zero => exact Nat.zero_le _
      | succ n =>
        have hlt := (stack m).depth_lt_of_move (predecessor_move m n)
        rw [ih n (Nat.lt_succ_self n)] at hlt
        exact hlt

/-- The SG function of the actual selective compound starting at position n. -/
abbrev value (m n k : ℕ) := (stack m).withHeap.grundy (n,k)

theorem value_upper (m n k : ℕ) : value m n k ≤ k+n := by
  have h := (stack m).withHeap.grundy_le_depth (n,k)
  simpa [Game.withHeap_depth, stack_depth] using h

theorem propagate_offset {m n j k r : ℕ} (hj : j ≤ k) (h : j+r ≤ value m n j) :
    k+r ≤ value m n k := by
  obtain ⟨s,rfl⟩ := Nat.exists_eq_add_of_le hj
  induction s with
  | zero => simpa using h
  | succ s ih =>
    have hs := (stack m).value_lt_succ n (j+s)
    change value m n (j+s) < value m n (j+s+1) at hs
    change (j+s+1)+r ≤ value m n (j+s+1)
    omega

theorem nim_base (m n k : ℕ) (hn : n ≤ m) : value m n k = k+n := by
  have zero_heap : ∀ n ≤ m, value m n 0 = n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hn
      have upper := value_upper m n 0
      by_contra hne
      have hlt : value m n 0 < n := by omega
      let b := value m n 0
      have hb : b ∈ (stack m).moves n := by
        simp [stack, hn, b, hlt]
      have he := ih b hlt (by omega)
      have hm : (b,0) ∈ (stack m).withHeap.moves (n,0) :=
        (stack m).withHeap_move_iff.mpr (Or.inr ⟨hb, le_refl 0⟩)
      exact (stack m).withHeap.grundy_ne_of_move hm he.symm
  have lower := propagate_offset (m := m) (n := n) (r := n) (Nat.zero_le k)
    (by rw [zero_heap n hn]; omega)
  exact Nat.le_antisymm (value_upper m n k) lower

private theorem only_predecessor (m t : ℕ) {b : ℕ} :
    b ∈ (stack m).moves (m+t+1) ↔ b = m+t := by
  have h : ¬m+t+1 ≤ m := by omega
  simp [stack, h]

private theorem child_ne (m n j k : ℕ) (hj : j ≤ k) :
    value m (n+1) k ≠ value m n j :=
  (stack m).withHeap.grundy_ne_of_move
    ((stack m).withHeap_move_iff.mpr (Or.inr ⟨predecessor_move m n, hj⟩))

private theorem first_stage (m : ℕ) :
    (∀ k < m, value m (m+1) k = k) ∧
    (∀ k ≥ m, value m (m+1) k = k+(m+1)) := by
  constructor
  · intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro hk
      have lower := (stack m).heap_le_value (m+1) k
      change k ≤ value m (m+1) k at lower
      by_contra hne
      have hl : k < value m (m+1) k := by omega
      obtain ⟨⟨b,j⟩, hm, he⟩ := (stack m).withHeap.reachable_of_lt_grundy hl
      change value m b j = k at he
      rcases (stack m).withHeap_move_iff.mp hm with ⟨rfl,hj⟩ | ⟨hb,hj⟩
      · rw [ih j hj (by omega)] at he
        omega
      · have hb' := (only_predecessor m 0).mp (by simpa using hb)
        simp at hb'
        subst b
        rw [nim_base m m j (le_refl m)] at he
        omega
  · intro k hk
    have lower := (stack m).heap_le_value (m+1) k
    change k ≤ value m (m+1) k at lower
    have upper := value_upper m (m+1) k
    by_contra hne
    let j := value m (m+1) k - m
    have hj : j ≤ k := by dsimp [j]; omega
    have hchild := nim_base m m j (le_refl m)
    apply child_ne m m j k hj
    rw [hchild]
    dsimp [j]
    omega

/-- At the vertex of depth m+t+1 the exact stabilization threshold is
m(t+1), for 0 ≤ t ≤ m. The middle interval records the last linear segment
before the jump and makes the induction uniform in m and t. -/
theorem stack_profile (m t : ℕ) (ht : t ≤ m) :
    (∀ k < m*(t+1), value m (m+t+1) k ≤ k+t) ∧
    (∀ k ≥ m*t, k < m*(t+1) → value m (m+t+1) k = k+t) ∧
    (∀ k ≥ m*(t+1), value m (m+t+1) k = k+(m+t+1)) := by
  induction t with
  | zero =>
    obtain ⟨lo,hi⟩ := first_stage m
    simpa using And.intro (fun k hk => (lo k hk).le)
      (And.intro (fun k (_ : k ≥ 0) hk => lo k hk) hi)
  | succ t ih =>
    obtain ⟨low,mid,high⟩ := ih (by omega)
    let B := m+t+1
    let A := B+1
    let S := m*(t+1)
    let K := S+m
    change (∀ k < m*(t+2), value m (m+(t+1)+1) k ≤ k+(t+1)) ∧
      (∀ k ≥ m*(t+1), k < m*(t+2) → value m (m+(t+1)+1) k = k+(t+1)) ∧
      (∀ k ≥ m*(t+2), value m (m+(t+1)+1) k = k+(m+(t+1)+1))
    rw [show m*(t+2) = K from Nat.mul_succ m (t+1)]
    change (∀ k < K, value m A k ≤ k+(t+1)) ∧
      (∀ k ≥ S, k < K → value m A k = k+(t+1)) ∧
      (∀ k ≥ K, value m A k = k+A)
    have hS : S = m*t+m := Nat.mul_succ m t
    have hK : K = S+m := rfl
    have hB : B = m+t+1 := rfl
    have lowA : ∀ k < K, value m A k ≤ k+(t+1) := by
      intro k
      induction k using Nat.strong_induction_on with
      | h k prev =>
        intro hk
        by_contra! hl
        obtain ⟨⟨b,j⟩, hm, he⟩ := (stack m).withHeap.reachable_of_lt_grundy hl
        change value m b j = k+(t+1) at he
        rcases (stack m).withHeap_move_iff.mp hm with ⟨rfl,hj⟩ | ⟨hb,hj⟩
        · have bound := prev j hj (by omega)
          omega
        · have hb' : b = B := (only_predecessor m (t+1)).mp hb
          subst b
          by_cases hs : j < S
          · have bound : value m B j ≤ j+t := low j hs
            omega
          · have eqn : value m B j = j+B := high j (by omega)
            omega
    let c := S-1
    have hc : c+1 = S := by dsimp [c]; omega
    have base : c+(t+1) ≤ value m A c := by
      have lower := (stack m).heap_le_value A c
      change c ≤ value m A c at lower
      by_contra! hlt
      let j := value m A c - t
      have hj : j ≤ c := by dsimp [j]; omega
      have hstart : m*t ≤ j := by dsimp [j]; omega
      have hsmall : j < S := by omega
      have eqn : value m B j = j+t := mid j hstart hsmall
      apply child_ne m B j c hj
      change value m A c = value m B j
      rw [eqn]
      dsimp [j]
      omega
    refine ⟨lowA, ?_, ?_⟩
    · intro k hs hk
      exact Nat.le_antisymm (lowA k hk) (propagate_offset (by omega) base)
    · intro k hk
      have upper := value_upper m A k
      have lower := propagate_offset (k := k) (by omega) base
      by_contra hne
      let j := value m A k - B
      have hA : A = B+1 := rfl
      have hj : j ≤ k := by dsimp [j]; omega
      have hlarge : S ≤ j := by dsimp [j]; omega
      have eqn : value m B j = j+B := high j hlarge
      apply child_ne m B j k hj
      change value m A k = value m B j
      rw [eqn]
      dsimp [j]
      omega

/-- The cutoff is attained for this family: the upper value is reached at
and after m(t+1), and never earlier. -/
theorem stack_cutoff_iff (m t k : ℕ) (ht : t ≤ m) :
    value m (m+t+1) k = k + (stack m).depth (m+t+1) ↔ m*(t+1) ≤ k := by
  rw [stack_depth]
  obtain ⟨low, _, high⟩ := stack_profile m t ht
  constructor
  · intro he
    by_contra! hl
    have := low k hl
    omega
  · exact high k

/-- A board of depth 2m whose first saturated heap is m². -/
theorem even_depth_exact_square (m k : ℕ) (hm : 0 < m) :
    value m (2*m) k = k + 2*m ↔ m*m ≤ k := by
  have e : m+(m-1)+1 = 2*m := by omega
  have c := stack_cutoff_iff m (m-1) k (Nat.sub_le _ _)
  rw [stack_depth, e, show m-1+1 = m by omega] at c
  exact c

/-- At depth 2m+1 the same construction requires a heap of size m(m+1). -/
theorem odd_depth_exact_product (m k : ℕ) :
    value m (2*m+1) k = k + (2*m+1) ↔ m*(m+1) ≤ k := by
  have c := stack_cutoff_iff m m k (le_refl m)
  rw [stack_depth, show m+m+1 = 2*m+1 by omega] at c
  exact c

#print axioms stack_cutoff_iff
#print axioms even_depth_exact_square
#print axioms odd_depth_exact_product

end
end QuadraticFamily
end SelectiveCompound

namespace SelectiveCompound
namespace Game

open Finset
noncomputable section
universe u
variable {α : Type u} [DecidableEq α] (G : Game α)

/-- Nimber values absent below n in the strictly increasing heap row of a. -/
def holes (a : α) (n : ℕ) : ℕ := by
  classical
  exact ((Finset.range n).filter
    (fun x => ¬ ∃ j, G.withHeap.grundy (a,j) = x)).card

theorem strict_heap_row (a : α) : StrictMono (fun j => G.withHeap.grundy (a,j)) :=
  strictMono_nat_of_lt_succ (G.value_lt_succ a)

private theorem holes_zero (a : α) : G.holes a 0 = 0 := by simp [holes]

private theorem holes_succ_hit {a : α} {n : ℕ}
    (h : ∃ j, G.withHeap.grundy (a,j) = n) : G.holes a (n+1) = G.holes a n := by
  classical
  simp only [holes, Finset.range_add_one, Finset.filter_insert]
  rw [if_neg (not_not_intro h)]

private theorem holes_succ_miss {a : α} {n : ℕ}
    (h : ¬ ∃ j, G.withHeap.grundy (a,j) = n) : G.holes a (n+1) = G.holes a n + 1 := by
  classical
  simp only [holes, Finset.range_add_one, Finset.filter_insert, if_pos h]
  apply Finset.card_insert_of_notMem
  simp

private theorem holes_step (a : α) (n : ℕ) :
    G.holes a (n+1) = G.holes a n ∨ G.holes a (n+1) = G.holes a n + 1 := by
  by_cases hit : ∃ j, G.withHeap.grundy (a,j) = n
  · exact Or.inl (G.holes_succ_hit hit)
  · exact Or.inr (G.holes_succ_miss hit)

private theorem holes_mono (a : α) : Monotone (G.holes a) :=
  monotone_nat_of_le_succ (fun n => by rcases G.holes_step a n with h | h <;> omega)

private theorem holes_le_index (a : α) (n : ℕ) : G.holes a n ≤ n := by
  classical
  simpa [holes] using Finset.card_le_card
    (Finset.filter_subset (fun x => ¬ ∃ j, G.withHeap.grundy (a,j) = x) (Finset.range n))

private theorem holes_at_value (a : α) (k : ℕ) :
    G.holes a (G.withHeap.grundy (a,k)) + k = G.withHeap.grundy (a,k) := by
  classical
  let f : ℕ → ℕ := fun j => G.withHeap.grundy (a,j)
  have hf : StrictMono f := G.strict_heap_row a
  let hit : ℕ → Prop := fun x => ∃ j, f j = x
  have hset : (Finset.range (f k)).filter hit = (Finset.range k).image f := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨h, j, rfl⟩
      exact ⟨j, hf.lt_iff_lt.mp h, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      exact ⟨hf hj,j,rfl⟩
  have hcard := Finset.filter_card_add_filter_neg_card_eq_card hit (s := Finset.range (f k))
  rw [hset, Finset.card_image_of_injective _ hf.injective, Finset.card_range,
    Finset.card_range] at hcard
  change ((Finset.range (f k)).filter (fun x => ¬ hit x)).card + k = f k
  omega

private theorem holes_le_depth (a : α) (n : ℕ) : G.holes a n ≤ G.depth a := by
  have h₁ := G.holes_mono a (G.heap_le_value a n)
  have h₂ := G.holes_at_value a n
  have h₃ := G.withHeap.grundy_le_depth (a,n)
  rw [G.withHeap_depth] at h₃
  omega

/-- When both rows take the same value n, the child must take it at a larger
heap. Thus its hole count is strictly smaller just before processing n. -/
private theorem two_hits {a b : α} {n : ℕ} (hb : b ∈ G.moves a)
    (ha : G.holes a (n+1) = G.holes a n) (h₂ : G.holes b (n+1) = G.holes b n) :
    G.holes b n < G.holes a n := by
  have hit (c : α) (hh : G.holes c (n+1) = G.holes c n) :
      ∃ j, G.withHeap.grundy (c,j) = n := by
    by_contra hn
    have := G.holes_succ_miss hn
    omega
  obtain ⟨j,hj⟩ := hit a ha
  obtain ⟨k,hk⟩ := hit b h₂
  have h₁ := G.holes_at_value a j
  have h₃ := G.holes_at_value b k
  rw [hj] at h₁
  rw [hk] at h₃
  by_contra! hge
  have hkj : k ≤ j := by omega
  apply G.withHeap.grundy_ne_of_move
    (G.withHeap_move_iff.mpr (Or.inr ⟨hb,hkj⟩))
  exact hj.trans hk.symm

/-- Before i holes have occurred, at most u(d-u) labels have been used for
some u ≤ i, where d is the depth. -/
theorem prefix_rectangle (a : α) (n i : ℕ) (hi : i ≤ G.depth a)
    (ha : G.holes a n < i) :
    ∃ u ≤ i, n - G.holes a n ≤ u * (G.depth a - u) := by
  suffices result : ∀ d : ℕ, ∀ a : α, G.depth a = d → ∀ n i : ℕ,
      i ≤ d → G.holes a n < i → ∃ u ≤ i, n - G.holes a n ≤ u*(d-u) from
    result (G.depth a) a rfl n i hi ha
  intro d
  induction d with
  | zero =>
    intro a _ n i hi ha
    omega
  | succ d ih =>
    intro a hd
    obtain ⟨b, hb, hd'⟩ := G.exists_deepest_move hd
    /- While the child has at least as many holes, each label used by the
    parent consumes a child hole. At a crossing, apply depth induction. -/
    have balance : ∀ n i : ℕ, i ≤ d+1 → G.holes a n < i →
        G.holes a n ≤ G.holes b n → ∃ u ≤ i,
        n - G.holes a n + (d - G.holes b n) ≤ u*(d+1-u) := by
      intro n
      induction n with
      | zero =>
        intro i _ ha _
        rw [G.holes_zero] at ha
        refine ⟨1, by omega, ?_⟩
        simp [holes_zero]
      | succ n prev =>
        intro i hi ha hab
        have stepA := G.holes_step a n
        have stepB := G.holes_step b n
        have boundA := G.holes_le_index a n
        have boundB := G.holes_le_index b n
        have cap := G.holes_le_depth b (n+1)
        rw [hd'] at cap
        by_cases hold : G.holes a n ≤ G.holes b n
        · obtain ⟨u, hui, hu⟩ := prev i hi (by omega) hold
          refine ⟨u, hui, le_trans ?_ hu⟩
          have noHits := G.two_hits (n := n) hb
          omega
        · have crossing : G.holes b n + 1 = G.holes a n := by omega
          have newA : G.holes a (n+1) = G.holes a n := by omega
          have newB : G.holes b (n+1) = G.holes a n := by omega
          let q := G.holes a n
          obtain ⟨u,hu, hcount⟩ := ih b hd' n q (by dsimp [q]; omega)
            (by dsimp [q]; omega)
          refine ⟨u+1, by dsimp [q] at hu; omega, ?_⟩
          have hu' : u ≤ d := by dsimp [q] at hu; omega
          have left : n+1-G.holes a (n+1) = n-G.holes b n := by omega
          rw [left, newB]
          have hrest : d-G.holes a n ≤ d-u := by dsimp [q] at hu; omega
          calc
            n-G.holes b n + (d-G.holes a n)
                ≤ u*(d-u) + (d-u) := Nat.add_le_add hcount hrest
            _ = (u+1)*(d+1-(u+1)) := by simp [Nat.add_mul]
    intro n i hi ha
    by_cases h : G.holes a n ≤ G.holes b n
    · obtain ⟨u,hui,hu⟩ := balance n i hi ha h
      exact ⟨u, hui, by omega⟩
    · have hb' : G.holes b n < G.holes a n := by omega
      have hbc := G.holes_le_depth b n
      rw [hd'] at hbc
      by_cases full : G.holes b n = d
      · omega
      · obtain ⟨u, hu, hcount⟩ := ih b hd' n (G.holes b n + 1) (by omega) (by omega)
        refine ⟨u, by omega, ?_⟩
        exact (show n-G.holes a n ≤ n-G.holes b n by omega).trans
          (hcount.trans (Nat.mul_le_mul_left u (by omega)))

/-- The optimal depth-only universal bound, rounded down. -/
theorem large_heap_grundy_optimal (a : α) (k : ℕ) (hk : (G.depth a)^2 / 4 ≤ k) :
    G.withHeap.grundy (a,k) = k + G.depth a := by
  let v := G.withHeap.grundy (a,k)
  let d := G.depth a
  have cap : v ≤ k+d := by
    simpa [v,d,G.withHeap_depth] using G.withHeap.grundy_le_depth (a,k)
  by_contra hne
  change v ≠ k+d at hne
  have mixed := G.holes_at_value a k
  change G.holes a v + k = v at mixed
  have same := G.holes_succ_hit (a := a) (n := v) ⟨k,rfl⟩
  have hlow : G.holes a (v+1) < d := by omega
  obtain ⟨u,hu,hcount⟩ := G.prefix_rectangle a (v+1) d (le_refl d) hlow
  change v+1-G.holes a (v+1) ≤ u*(d-u) at hcount
  have hmean := four_mul_le_sq_add u (d-u)
  rw [Nat.add_sub_of_le hu] at hmean
  have hbound : u*(d-u) ≤ d^2/4 := by
    apply (Nat.le_div_iff_mul_le (by decide : 0 < 4)).mpr
    simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hmean
  change d^2/4 ≤ k at hk
  omega

#print axioms prefix_rectangle
#print axioms large_heap_grundy_optimal

end
end Game

namespace QuadraticFamily

/-- For every depth there is an explicit ruleset and a starting position
where the universal cutoff is also necessary, including depths 0 and 1. -/
theorem exact_witness_at_every_depth (d : ℕ) :
    ∃ (G : Game ℕ) (a : ℕ), G.depth a = d ∧
      ∀ k, G.withHeap.grundy (a,k) = k+d ↔ d^2/4 ≤ k := by
  let m := d/2
  have parity : d = 2*m ∨ d = 2*m+1 := by dsimp [m]; omega
  refine ⟨stack m, d, stack_depth m d, ?_⟩
  intro k
  change value m d k = k+d ↔ d^2/4 ≤ k
  rcases parity with even | odd
  · by_cases hz : m = 0
    · have hd : d = 0 := by omega
      simp [hd, hz, nim_base]
    · have hs : (2*m)^2 = 4*(m*m) := by ring
      rw [even, hs]
      simpa using even_depth_exact_square m k (Nat.pos_of_ne_zero hz)
  · have hs : (2*m+1)^2 = 4*(m*(m+1))+1 := by ring
    rw [odd, hs]
    have round : (4*(m*(m+1))+1)/4 = m*(m+1) := by omega
    rw [round]
    exact odd_depth_exact_product m k

/-- A number K works simultaneously on all games at depth d exactly when
it is at least floor(d²/4). Finite games can always be numbered in ℕ. -/
theorem universal_cutoff_iff (d K : ℕ) :
    (∀ (G : Game ℕ) (a : ℕ), G.depth a = d → ∀ k ≥ K,
      G.withHeap.grundy (a,k) = k+d) ↔ d^2/4 ≤ K := by
  constructor
  · intro all
    obtain ⟨G,a,hd,h⟩ := exact_witness_at_every_depth d
    exact (h K).mp (all G a hd K (le_refl K))
  · intro h G a hd k hk
    have hcut : (G.depth a)^2/4 ≤ k := by rw [hd]; exact h.trans hk
    simpa only [hd] using G.large_heap_grundy_optimal a k hcut

#print axioms exact_witness_at_every_depth
#print axioms universal_cutoff_iff

end QuadraticFamily
end SelectiveCompound

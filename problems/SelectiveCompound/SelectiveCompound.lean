import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Tactic.ByContra

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

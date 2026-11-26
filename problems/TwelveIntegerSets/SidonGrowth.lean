import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Union
import Mathlib.Tactic.Linarith

namespace SmallSumProduct

def shift (x : ℚ) (B : Finset ℚ) : Finset ℚ := B.image (x + ·)

def sums (A B : Finset ℚ) : Finset ℚ := A.biUnion (fun x => shift x B)

theorem mem_shift {B : Finset ℚ} {x s : ℚ} : s∈shift x B ↔ ∃ a∈B, x+a=s :=
  Finset.mem_image

theorem mem_sums {A B : Finset ℚ} {s : ℚ} : s∈sums A B ↔ ∃ a∈A, ∃ b∈B, a+b=s := by
  simp only [sums, Finset.mem_biUnion, mem_shift]

@[simp] theorem card_shift (x : ℚ) (B : Finset ℚ) : (shift x B).card=B.card :=
  Finset.card_image_of_injective _ (fun _ _ h => add_left_cancel h)

def IsSidon (B : Finset ℚ) : Prop :=
  ∀ a∈B, ∀ b∈B, ∀ c∈B, ∀ d∈B, a+b=c+d → (a=c ∧ b=d) ∨ (a=d ∧ b=c)

private theorem sums_insert_both (x : ℚ) (B : Finset ℚ) :
    sums (insert x B) (insert x B) = sums B B ∪ shift x (insert x B) := by
  ext s
  simp only [mem_sums, Finset.mem_union, mem_shift, Finset.mem_insert]
  constructor
  · rintro ⟨a, (rfl | ha), b, hb, rfl⟩
    · exact Or.inr ⟨b,hb,rfl⟩
    · rcases hb with rfl | hb
      · exact Or.inr ⟨a,Or.inr ha,add_comm _ _⟩
      · exact Or.inl ⟨a,ha,b,hb,rfl⟩
  · rintro (⟨a,ha,b,hb,rfl⟩ | ⟨b,hb,rfl⟩)
    · exact ⟨a,Or.inr ha,b,Or.inr hb,rfl⟩
    · exact ⟨x,Or.inl rfl,b,hb,rfl⟩

theorem sidon_card (B : Finset ℚ) (hs : IsSidon B) :
    2*(sums B B).card=B.card*(B.card+1) := by
  induction B using Finset.induction_on with
  | empty => simp [sums]
  | @insert x B hx ih =>
    have hB : IsSidon B := fun a ha b hb c hc d hd => hs a (Finset.mem_insert_of_mem ha)
      b (Finset.mem_insert_of_mem hb) c (Finset.mem_insert_of_mem hc) d (Finset.mem_insert_of_mem hd)
    have disj : Disjoint (sums B B) (shift x (insert x B)) := by
      apply Finset.disjoint_left.mpr
      intro s h1 h2
      obtain ⟨a,ha,b,hb,e⟩ := mem_sums.mp h1
      obtain ⟨v,hv,ev⟩ := mem_shift.mp h2
      rcases hs a (Finset.mem_insert_of_mem ha) b (Finset.mem_insert_of_mem hb) x (by simp)
        v hv (e.trans ev.symm) with h | h
      · exact hx (h.1 ▸ ha)
      · exact hx (h.2 ▸ hb)
    rw [sums_insert_both, Finset.card_union_of_disjoint disj, card_shift, Finset.card_insert_of_notMem hx]
    nlinarith [ih hB]

theorem meet_shifts (B : Finset ℚ) (hs : IsSidon B) (x y : ℚ) (hxy : x≠y) :
    (shift x B ∩ shift y B).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro s u t v
  obtain ⟨a,ha,ha'⟩ := mem_shift.mp (Finset.mem_inter.mp u).1
  obtain ⟨b,hb,hb'⟩ := mem_shift.mp (Finset.mem_inter.mp u).2
  obtain ⟨c,hc,hc'⟩ := mem_shift.mp (Finset.mem_inter.mp v).1
  obtain ⟨d,hd,hd'⟩ := mem_shift.mp (Finset.mem_inter.mp v).2
  rcases hs a ha d hd c hc b hb (by linarith) with h | h
  · linarith [h.1]
  · exact False.elim (hxy (by linarith [h.1]))

private theorem meet_all_shifts (B : Finset ℚ) (hs : IsSidon B) (x : ℚ) (T : Finset ℚ)
    (hout : x∉T) : (shift x B ∩ sums T B).card ≤ T.card := by
  induction T using Finset.induction_on with
  | empty => simp [sums]
  | @insert y T hy ih =>
    have hxy : x≠y := fun e => hout (e ▸ Finset.mem_insert_self _ _)
    have hx : x∉T := fun h => hout (Finset.mem_insert_of_mem h)
    rw [show sums (insert y T) B=shift y B ∪ sums T B by simp [sums],
      Finset.inter_union_distrib_left, Finset.card_insert_of_notMem hy]
    have b := Finset.card_union_le (shift x B ∩ shift y B) (shift x B ∩ sums T B)
    have c := meet_shifts B hs x y hxy
    have d := ih hx
    omega

/-- A Sidon core with a two-point intersection bound has this quantitative
sumset-growth inequality for any number of arbitrary additional elements. -/
theorem sumset_growth (B T : Finset ℚ) (hs : IsSidon B)
    (hinter : ∀ x∈T, (shift x B ∩ sums B B).card≤2) :
    B.card*(B.card+1) + 2*B.card*T.card ≤
      2*(sums B B ∪ sums T B).card + T.card*(T.card+3) := by
  induction T using Finset.induction_on with
  | empty => simpa [sums] using (le_of_eq (sidon_card B hs).symm)
  | @insert x T hx ih =>
    have prev := ih (fun y hy => hinter y (Finset.mem_insert_of_mem hy))
    let G := sums B B ∪ sums T B
    have hcap : (shift x B ∩ G).card ≤ 2+T.card := by
      dsimp [G]
      rw [Finset.inter_union_distrib_left]
      exact (Finset.card_union_le _ _).trans (Nat.add_le_add (hinter x (by simp)) (meet_all_shifts B hs x T hx))
    have step := Finset.card_union_add_card_inter (shift x B) G
    rw [card_shift] at step
    have eq : sums B B ∪ sums (insert x T) B = shift x B ∪ G := by
      simp only [sums, Finset.biUnion_insert, G, Finset.union_left_comm]
    rw [eq, Finset.card_insert_of_notMem hx]
    change B.card*(B.card+1)+2*B.card*T.card ≤ 2*G.card + T.card*(T.card+3) at prev
    nlinarith

end SmallSumProduct

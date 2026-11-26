import PressCost
import Mathlib.Data.Finset.Max

/-! Stabilization of the normalized covering radius for repeated active coordinates. -/
namespace RepeatedCover
open LightsPolynomial GridClicks
open scoped BigOperators
noncomputable section
variable {A V : Type*} [Fintype A] [Fintype V] [Nonempty V]

def dist (entry : V → A → F) {T : Type*} [Fintype T] (x : T → A → F) (v : V) : ℕ :=
  ∑ t,∑ c,click (x t c+entry v c)

def IsRadius (entry : V → A → F) (T : Type*) [Fintype T] (R : ℕ) : Prop :=
  (∀ x : T → A → F, ∃ v, dist entry x v≤R) ∧
  (∃ x : T → A → F, ∀ v, R≤dist entry x v)

private theorem radius_exists (entry : V → A → F) (T : Type*) [Fintype T] :
    ∃ R, IsRadius entry T R := by
  classical
  have minimum (x : T → A → F) : ∃ v : V, ∀ w, dist entry x v≤dist entry x w := by
    obtain ⟨v,_,hv⟩ := Finset.exists_min_image Finset.univ (dist entry x) Finset.univ_nonempty
    exact ⟨v,fun w => hv w (Finset.mem_univ _)⟩
  choose best hb using minimum
  obtain ⟨hard,_,hh⟩ := Finset.exists_max_image Finset.univ
    (fun x : T → A → F => dist entry x (best x)) Finset.univ_nonempty
  exact ⟨dist entry hard (best hard),⟨fun x => ⟨best x,hh x (Finset.mem_univ _)⟩,⟨hard,hb hard⟩⟩⟩

def radius (entry : V → A → F) (r : ℕ) : ℕ := Classical.choose (radius_exists entry (Fin r))

theorem radius_spec (entry : V → A → F) (r : ℕ) : IsRadius entry (Fin r) (radius entry r) :=
  Classical.choose_spec (radius_exists entry (Fin r))

omit [Fintype V] [Nonempty V] in
private theorem reindex (entry : V → A → F) {T S : Type*} [Fintype T] [Fintype S]
    (e : T ≃ S) (x : S → A → F) (v : V) :
    dist entry (fun t => x (e t)) v=dist entry x v :=
  e.sum_comp (fun t => ∑ c,click (x t c+entry v c))

theorem radius_transfer (entry : V → A → F) (T : Type*) [Fintype T] :
    IsRadius entry T (radius entry (Fintype.card T)) := by
  classical
  let e := Fintype.equivFin T
  obtain ⟨upper,lower⟩ := radius_spec entry (Fintype.card T)
  constructor
  · intro x
    obtain ⟨v,h⟩ := upper (fun i => x (e.symm i))
    exact ⟨v,by rwa [reindex entry e.symm x v] at h⟩
  · obtain ⟨x,hx⟩ := lower
    exact ⟨fun t => x (e t),fun v => by rw [reindex entry e x v];exact hx v⟩

def Balanced (entry : V → A → F) : Prop := ∀ (a : A) (x : F),
  2*(∑ v,click (x+entry v a))=Fintype.card V

omit [Nonempty V] in
private theorem row_sum (entry : V → A → F) (bal : Balanced entry)
    {T : Type*} [Fintype T] (x : T → A → F) :
    (∑ v,2*dist entry x v)=Fintype.card V*(Fintype.card T*Fintype.card A) := by
  simp only [dist,Finset.mul_sum]
  rw [Finset.sum_comm]
  have h (t : T) : (∑ v,∑ a,2*click (x t a+entry v a))=Fintype.card A*Fintype.card V := by
    rw [Finset.sum_comm]
    have col (c : A) : (∑ v,2*click (x t c+entry v c))=Fintype.card V := by
      rw [← Finset.mul_sum];exact bal _ _
    simp_rw [col];simp
  simp_rw [h]
  simp [Nat.mul_comm,Nat.mul_left_comm]

theorem radius_bound (entry : V → A → F) (bal : Balanced entry) (r : ℕ) :
    2*radius entry r≤r*Fintype.card A := by
  classical
  obtain ⟨x,h⟩ := (radius_spec entry r).2
  have le := Finset.sum_le_sum (s:=(Finset.univ : Finset V))
    (fun v _ => Nat.mul_le_mul_left 2 (h v))
  rw [row_sum entry bal] at le
  simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul,Fintype.card_fin] at le
  exact Nat.le_of_mul_le_mul_left le Fintype.card_pos

private theorem complementary (z : F) : click (0+z)+click (1+z)=1 :=
  (by decide : ∀ x : F, click (0+x)+click (1+x)=1) z

theorem two_more (entry : V → A → F) (r : ℕ) :
    radius entry r+Fintype.card A≤radius entry (r+2) := by
  classical
  obtain ⟨x,hard⟩ := (radius_spec entry r).2
  let S := Fin r ⊕ Fin 2
  let e : S ≃ Fin (r+2) := finSumFinEquiv
  let y : S → A → F := Sum.elim x (fun j _ => if j=0 then 0 else 1)
  obtain ⟨v,small⟩ := (radius_spec entry (r+2)).1 (fun i => y (e.symm i))
  have splitcost : dist entry (fun i => y (e.symm i)) v=dist entry x v+Fintype.card A := by
    rw [reindex entry e.symm y v]
    unfold dist
    rw [Fintype.sum_sum_type]
    dsimp only [y,Sum.elim_inl,Sum.elim_inr]
    congr 1
    rw [Fin.sum_univ_two]
    simp only [if_true,one_ne_zero,if_false]
    rw [← Finset.sum_add_distrib]
    simp_rw [complementary];simp
  rw [splitcost] at small
  exact (Nat.add_le_add_right (hard v) _).trans small

def deficit (entry : V → A → F) (r : ℕ) := r*Fintype.card A-2*radius entry r

theorem twice_radius (entry : V → A → F) (bal : Balanced entry) (r : ℕ) :
    2*radius entry r+deficit entry r=r*Fintype.card A := by
  exact Nat.add_sub_of_le (radius_bound entry bal r)

private theorem decreasing (entry : V → A → F) (bal : Balanced entry) (r : ℕ) :
    deficit entry (r+2)≤deficit entry r := by
  have grow := two_more entry r
  have a := twice_radius entry bal r
  have b := twice_radius entry bal (r+2)
  rw [Nat.add_mul] at b
  omega

theorem even_deficit (entry : V → A → F) (bal : Balanced entry) (r : ℕ) :
    deficit entry (2*r)=0 := by
  induction r with
  | zero => simp [deficit]
  | succ r ih =>
    rw [Nat.mul_succ]
    have h := decreasing entry bal (2*r)
    omega

theorem odd_stable (entry : V → A → F) (bal : Balanced entry) :
    ∃ k D : ℕ, ∀ j≥k, deficit entry (2*j+1)=D := by
  classical
  let f := fun k => deficit entry (2*k+1)
  have anti : Antitone f := antitone_nat_of_succ_le (fun j => by
    simpa only [f,show 2*(j+1)+1=(2*j+1)+2 by omega] using decreasing entry bal (2*j+1))
  have range : ∃ d, ∃ k, d=f k := ⟨f 0,0,rfl⟩
  obtain ⟨k,hk⟩ := Nat.find_spec range
  refine ⟨k,Nat.find range,fun j hj => le_antisymm ?_ ?_⟩
  · rw [hk];exact anti hj
  · exact Nat.find_min' range ⟨j,rfl⟩

#print axioms odd_stable
end
end RepeatedCover

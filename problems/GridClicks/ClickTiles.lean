import LightsGrid
import Mathlib.FieldTheory.Finiteness
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.IntervalCases

/-! The sixteen reflected 4 by 4 patterns on a square with side 5q−1. -/
namespace ClickTiles
open LightsPolynomial LightsGrid
abbrev Key := Fin 16
abbrev Small := Fin 4 × Fin 4
abbrev Tiles (q : ℕ) := Fin q × Fin q
abbrev Coord (q : ℕ) := Fin (q-1) ⊕ (Fin q × Fin 4)
abbrev Inactive (q : ℕ) :=
    (Fin (q-1) × Fin (q-1)) ⊕ (Fin (q-1) × (Fin q × Fin 4)) ⊕ ((Fin q × Fin 4) × Fin (q-1))

def mask : Key → ℕ := ![0x0,0xe531,0xb872,0x5d43,0xd1e4,0x34d5,0x6996,0x8ca7,
  0x7ac8,0x9ff9,0xc2ba,0x278b,0xab2c,0x4e1d,0x135e,0xf66f]

def bit (k : Key) (c : Small) : F :=
  if (mask k).testBit (4*c.1.val+c.2.val) then 1 else 0

private def axis (t : Fin 10) : Option (Fin 4) :=
  ![none,some 0,some 1,some 2,some 3,none,some 3,some 2,some 1,some 0] t

private abbrev phase (t : ℕ) : Fin 10 := ⟨t%10,by omega⟩

private def atPhase (k : Key) (r c : Fin 10) : F :=
  match axis r,axis c with
  | some i,some j => bit k (i,j)
  | _,_ => 0

def pattern (n : ℕ) (k : Key) : Board n := fun i j =>
  atPhase k (phase (i.val+1)) (phase (j.val+1))

private theorem local_rule : ∀ (k : Key) (i j : Fin 10),
    atPhase k (i+1) (j+1) + atPhase k (i+1) j + atPhase k (i+1) (j+2) +
      atPhase k i (j+1) + atPhase k (i+2) (j+1) = 0 := by decide +kernel

private theorem boundary (q : ℕ) : axis (phase (5*q))=none := by
  rcases (by omega : (5*q)%10=0 ∨ (5*q)%10=5) with h|h
  · rw [show (phase (5*q))=0 from Fin.ext h]; decide
  · rw [show (phase (5*q))=5 from Fin.ext h]; decide

private theorem read_periodic {n : ℕ} (f : ℕ → F) (zero : f 0=0) (last : f (n+1)=0)
    (j : ℕ) (b : j≤n+1) : LightsGrid.read (fun i : Fin n => f (i.val+1)) j = f j := by
  cases j with
  | zero => exact zero.symm
  | succ j =>
    by_cases h : j<n
    · simp [LightsGrid.read,h]
    · have eq : j=n := by omega
      subst j; simp [LightsGrid.read,last]

theorem quiet (q : ℕ) (positive : 0<q) (k : Key) :
    pattern (5*q-1) k∈quietSpace (5*q-1) := by
  rw [quiet_iff_toggles]
  intro i j
  let f := fun r c : ℕ => atPhase k (phase r) (phase c)
  have edge : 5*q-1+1=5*q := by omega
  have hz : axis 0=none := by decide
  have hr (c t : ℕ) (h : t≤5*q-1+1) :
      LightsGrid.read (fun v : Fin (5*q-1) => f (v.val+1) c) t=f t c :=
    read_periodic (fun r => f r c) (by change atPhase k 0 _=0; simp [atPhase,hz]) (by simp [f,atPhase,edge,boundary]) _ h
  have hc (r t : ℕ) (h : t≤5*q-1+1) :
      LightsGrid.read (fun v : Fin (5*q-1) => f r (v.val+1)) t=f r t :=
    read_periodic (fun c => f r c) (by change atPhase k _ 0=0; cases h : axis (phase r) <;> simp [atPhase,hz,h])
      (by cases h : axis (phase r) <;> simp [f,atPhase,edge,boundary,h]) _ h
  have read_col (b : Board (5*q-1)) (t : ℕ) :
      LightsGrid.read b t j=LightsGrid.read (fun v => b v j) t := by
    cases t with
    | zero => rfl
    | succ t => by_cases h : t<5*q-1 <;> simp [LightsGrid.read,h]
  rw [read_col,read_col]
  let row := fun v : Fin (5*q-1) => f (i.val+1) (v.val+1)
  let col := fun v : Fin (5*q-1) => f (v.val+1) (j.val+1)
  change f (i.val+1) (j.val+1) + LightsGrid.read row j.val + LightsGrid.read row (j.val+2) +
    LightsGrid.read col i.val + LightsGrid.read col (i.val+2) = 0
  dsimp only [row,col]
  rw [hc (i.val+1) _ (by omega),hc (i.val+1) _ (by omega),
    hr (j.val+1) _ (by omega),hr (j.val+1) _ (by omega)]
  have succ1 (t : ℕ) : phase (t+1)=phase t+1 :=
    Fin.ext (show (t+1)%10=(t%10+1)%10 by omega)
  have succ2 (t : ℕ) : phase (t+2)=phase t+2 :=
    Fin.ext (show (t+2)%10=(t%10+2)%10 by omega)
  dsimp only [f]
  rw [succ2 i.val,succ2 j.val,succ1 i.val,succ1 j.val]
  exact local_rule k (phase i.val) (phase j.val)

private theorem top_identifies : ∀ k l : Key,
    (∀ j : Fin 4, atPhase k 1 (phase (j.val+1))=atPhase l 1 (phase (j.val+1))) →
      k=l := by decide +kernel

theorem exhaustive (q : ℕ) (positive : 0<q)
    (dim : Module.finrank F (quietSpace (5*q-1))=4) (b : Board (5*q-1))
    (hb : b∈quietSpace (5*q-1)) : ∃ k, pattern (5*q-1) k=b := by
  classical
  let K := quietSpace (5*q-1)
  letI : Fintype K := Fintype.ofFinite K
  let f : Key → K := fun k => ⟨_,quiet q positive k⟩
  have inj : Function.Injective f := by
    intro k l eq
    apply top_identifies
    intro j
    exact congrArg (fun v : K => (v : Board (5*q-1)) ⟨0,by omega⟩ ⟨j.val,by omega⟩) eq
  have card : Fintype.card Key=Fintype.card K := by
    rw [Module.card_eq_pow_finrank (K:=F) (V:=↥K),show Module.finrank F (↥K)=4 from dim,ZMod.card,Fintype.card_fin]
    decide
  obtain ⟨k,hk⟩ := (Fintype.bijective_iff_injective_and_card f).2 ⟨inj,card⟩ |>.2 ⟨b,hb⟩
  exact ⟨k,congrArg Subtype.val hk⟩

private def reverseSlot (b : ℕ) (j : Fin 4) : Fin 4 :=
  if b%2=0 then j else ⟨3-j.val,by omega⟩

private theorem reverse_twice (b : ℕ) (j : Fin 4) : reverseSlot b (reverseSlot b j)=j := by
  apply Fin.ext
  by_cases h : b%2=0
  · simp [reverseSlot,h]
  · simp [reverseSlot,h]; omega

def places (q : ℕ) : Coord q ≃ Fin (5*q-1) where
  toFun
    | .inl s => ⟨5*s.val+4,by omega⟩
    | .inr (b,j) => ⟨5*b.val+(reverseSlot b j).val,by have := (reverseSlot b j).isLt; omega⟩
  invFun i := if h : i.val%5<4 then
    .inr (⟨i.val/5,by omega⟩,reverseSlot (i.val/5) ⟨i.val%5,h⟩)
    else .inl ⟨i.val/5,by omega⟩
  left_inv := by
    rintro (s|⟨b,j⟩)
    · simp
      apply Fin.ext; dsimp; omega
    · let t := reverseSlot b j
      have ht := t.isLt
      have dm : (5*b.val+t.val)%5=t.val := by omega
      have dq : (5*b.val+t.val)/5=b.val := by omega
      dsimp only
      change (if h : (5*b.val+t.val)%5<4 then _ else _) = _
      rw [dif_pos (by omega)]
      congr 1
      apply Prod.ext
      · exact Fin.ext dq
      · change reverseSlot ((5*b.val+t.val)/5) ⟨(5*b.val+t.val)%5,_⟩=j
        have v : (⟨(5*b.val+t.val)%5,by omega⟩ : Fin 4)=t := Fin.ext dm
        rw [dq,v]; exact reverse_twice _ _
  right_inv i := by
    dsimp only
    by_cases h : i.val%5<4
    · rw [dif_pos h]
      apply Fin.ext
      change 5*(i.val/5)+(reverseSlot (i.val/5) (reverseSlot (i.val/5) _)).val=i.val
      rw [reverse_twice]; change 5*(i.val/5)+i.val%5=i.val; omega
    · rw [dif_neg h]
      apply Fin.ext
      change 5*(i.val/5)+4=i.val
      omega

private theorem valid_phase (k : ℕ) (j : Fin 4) :
    axis (phase (5*k+(reverseSlot k j).val+1))=some j := by
  by_cases h : k%2=0
  · have pv : phase (5*k+(reverseSlot k j).val+1)=phase (j.val+1) :=
      Fin.ext (by simp only [reverseSlot,h,if_true];omega)
    rw [pv]; exact (by decide : ∀ i : Fin 4, axis (phase (i.val+1))=some i) j
  · have pv : phase (5*k+(reverseSlot k j).val+1)=phase (9-j.val) :=
      Fin.ext (by simp only [reverseSlot,h,if_false];omega)
    rw [pv]; exact (by decide : ∀ i : Fin 4, axis (phase (9-i.val))=some i) j


def positions (q : ℕ) : (Inactive q ⊕ (Tiles q × Small)) ≃ Fin (5*q-1) × Fin (5*q-1) :=
  Equiv.trans (Equiv.mk
    (fun p => match p with
      | .inl (.inl (i,j)) => (Sum.inl i,Sum.inl j)
      | .inl (.inr (.inl (i,j))) => (.inl i,.inr j)
      | .inl (.inr (.inr (i,j))) => (.inr i,.inl j)
      | .inr ((u,v),(i,j)) => (.inr (u,i),.inr (v,j)))
    (fun p => match p with
      | (.inl i,.inl j) => .inl (.inl (i,j))
      | (.inl i,.inr j) => .inl (.inr (.inl (i,j)))
      | (.inr i,.inl j) => .inl (.inr (.inr (i,j)))
      | (.inr (u,i),.inr (v,j)) => .inr ((u,v),(i,j)))
    (by rintro ((⟨_,_⟩|⟨_,_⟩|⟨_,_⟩)|⟨⟨_,_⟩,⟨_,_⟩⟩) <;> rfl)
    (by rintro ⟨(i|⟨u,i⟩),(j|⟨v,j⟩)⟩ <;> rfl))
    ((places q).prodCongr (places q))

theorem pattern_at (q : ℕ) (k : Key) (x : Inactive q ⊕ (Tiles q × Small)) :
    pattern (5*q-1) k ((positions q x).1) ((positions q x).2) =
      (match x with | .inl _ => 0 | .inr (_,c) => bit k c) := by
  have gap (i : ℕ) : axis (phase (5*i+4+1))=none := by
    rw [show 5*i+4+1=5*(i+1) by omega]; exact boundary _
  rcases x with (⟨i,j⟩|⟨i,v,j⟩|⟨⟨u,i⟩,j⟩)|⟨⟨u,v⟩,⟨i,j⟩⟩ <;>
    simp [pattern,positions,places,atPhase,gap,valid_phase]

theorem cardinal_inactive (q : ℕ) : Fintype.card (Inactive q)=(q-1)*(q-1)+8*(q-1)*q := by
  simp [Inactive,Fintype.card_sum,Fintype.card_prod];ring

end ClickTiles

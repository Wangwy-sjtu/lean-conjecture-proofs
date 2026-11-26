import ReflectionTiles
import Mathlib.Data.Fintype.EquivFin

/-! Coordinate bijections for arbitrary reflected seed squares and their active supports. -/
namespace ReflectionLayout
open LightsGrid LightsPolynomial ReflectionTiles
abbrev Cell (m : ℕ) := Fin m × Fin m
abbrev Copies (q : ℕ) := Fin (q+1) × Fin (q+1)
abbrev Coord (m q : ℕ) := Fin q ⊕ (Fin (q+1) × Fin m)
abbrev Gaps (m q : ℕ) :=
  (Fin q × Fin q) ⊕ (Fin q × (Fin (q+1) × Fin m)) ⊕ ((Fin (q+1) × Fin m) × Fin q)

private def slot {m : ℕ} (b : ℕ) (i : Fin m) := if b%2=0 then i else i.rev

private theorem slot_twice {m : ℕ} (b : ℕ) (i : Fin m) : slot b (slot b i)=i := by
  by_cases h : b%2=0 <;> simp [slot,h]

private def digits {m q : ℕ} : Coord m q → ℕ × ℕ
  | .inl s => (s.val,m)
  | .inr (b,i) => (b.val,(slot b i).val)

private theorem digits_inj {m q : ℕ} : Function.Injective (digits (m:=m) (q:=q)) := by
  rintro (s|⟨b,i⟩) (t|⟨c,j⟩) eq
  · exact congrArg Sum.inl (Fin.ext (congrArg Prod.fst eq))
  · have e : m=(slot c j).val := congrArg Prod.snd eq
    have h := (slot c j).isLt
    omega
  · have e : (slot b i).val=m := congrArg Prod.snd eq
    have h := (slot b i).isLt
    omega
  · have e : b=c := Fin.ext (congrArg Prod.fst eq)
    subst c
    have h : slot b i=slot b j := Fin.ext (congrArg Prod.snd eq)
    have ij := congrArg (slot b) h
    rw [slot_twice,slot_twice] at ij
    subst j;rfl

private def place {m q : ℕ} (x : Coord m q) : Fin (side m q) :=
  ⟨(m+1)*(digits x).1+(digits x).2,by
    cases x with
    | inl s =>
      have h := Nat.mul_lt_mul_of_pos_left s.isLt (by omega : 0<m+1)
      change (m+1)*s.val+m<(m+1)*q+m
      omega
    | inr p =>
      obtain ⟨b,i⟩ := p
      have h := Nat.mul_le_mul_left (m+1) (show b.val≤q by omega)
      have z := (slot b i).isLt
      change (m+1)*b.val+(slot b i).val<(m+1)*q+m
      omega⟩

private theorem place_inj {m q : ℕ} : Function.Injective (place (m:=m) (q:=q)) := by
  have good (x : Coord m q) : (digits x).2<m+1 := by
    rcases x with s|⟨b,i⟩
    · simp [digits]
    · exact Nat.lt_succ_of_lt (slot b i).isLt
  intro x y eq
  have v : (m+1)*(digits x).1+(digits x).2=(m+1)*(digits y).1+(digits y).2 := congrArg Fin.val eq
  apply digits_inj
  apply Prod.ext
  · have e := congrArg (fun n => n/(m+1)) v
    simpa only [Nat.mul_add_div (by omega : 0<m+1),Nat.div_eq_of_lt (good x),
      Nat.div_eq_of_lt (good y),Nat.add_zero] using e
  · have e := congrArg (fun n => n%(m+1)) v
    simpa only [Nat.mul_add_mod_self_left,Nat.mod_eq_of_lt (good x),Nat.mod_eq_of_lt (good y)] using e

noncomputable def places (m q : ℕ) : Coord m q ≃ Fin (side m q) :=
  Equiv.ofBijective place ((Fintype.bijective_iff_injective_and_card _).2
    ⟨place_inj,by simp [Coord,side,Fintype.card_sum,Fintype.card_prod];ring⟩)

private theorem valid_fold {m : ℕ} (k : ℕ) (j : Fin m) :
    fold m ((m+1)*k+(slot k j).val+1)=j.val+1 := by
  let L := m+1
  let p := 2*L
  have jl := j.isLt
  rcases (by omega : k=2*(k/2) ∨ k=2*(k/2)+1) with even|odd
  · have par : k%2=0 := by omega
    have eq : (m+1)*k+(slot k j).val+1=p*(k/2)+(j.val+1) := by
      simp only [slot,par,if_true];dsimp only [p,L]
      calc
        (m+1)*k+j.val+1=(m+1)*(2*(k/2))+j.val+1 := congrArg (fun a=>(m+1)*a+j.val+1) even
        _ = _ := by ring
    rw [eq]; unfold fold
    change (if (p*(k/2)+(j.val+1))%p≤L then (p*(k/2)+(j.val+1))%p else p-(p*(k/2)+(j.val+1))%p)=_
    simp [Nat.mod_eq_of_lt (show j.val+1<p by dsimp [p,L];omega),L,show j.val+1≤m+1 by omega]
  · have par : k%2≠0 := by omega
    let z := L+(m-(j.val+1))+1
    have hz : L<z ∧ z<p ∧ p-z=j.val+1 := by dsimp [L,p,z];omega
    have eq : (m+1)*k+(slot k j).val+1=p*(k/2)+z := by
      simp only [slot,par,if_false,Fin.val_rev];dsimp only [p,L,z]
      calc
        (m+1)*k+(m-(j.val+1))+1=(m+1)*(2*(k/2)+1)+(m-(j.val+1))+1 :=
          congrArg (fun a=>(m+1)*a+(m-(j.val+1))+1) odd
        _ = _ := by ring
    rw [eq];unfold fold
    change (if (p*(k/2)+z)%p≤L then (p*(k/2)+z)%p else p-(p*(k/2)+z)%p)=_
    simp only [Nat.mul_add_mod_self_left,Nat.mod_eq_of_lt hz.2.1,if_neg (by omega : ¬z≤L)]
    exact hz.2.2

noncomputable def positions (m q : ℕ) : (Gaps m q ⊕ (Copies q × Cell m)) ≃ Cell (side m q) :=
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
    ((places m q).prodCongr (places m q))

theorem lift_at {m q : ℕ} (b : Board m) (x : Gaps m q ⊕ (Copies q × Cell m)) :
    lift q b ((positions m q x).1) ((positions m q x).2) =
      (match x with | .inl _ => 0 | .inr (_,c) => b c.1 c.2) := by
  have gap (i : ℕ) : fold m ((m+1)*i+m+1)=0 ∨ fold m ((m+1)*i+m+1)=m+1 := by
    rw [show (m+1)*i+m+1=(m+1)*(i+1) by ring];exact multiple _ _
  rcases x with (⟨i,j⟩|⟨i,v,j⟩|⟨⟨u,i⟩,j⟩)|⟨⟨u,v⟩,⟨i,j⟩⟩
  · exact border b _ _ ((gap i).elim Or.inl (fun h=>Or.inr (Or.inl h)))
  · exact border b _ _ ((gap i).elim Or.inl (fun h=>Or.inr (Or.inl h)))
  · exact border b _ _ (Or.inr (Or.inr (gap j)))
  · change seedAt b (fold m ((m+1)*u.val+(slot u i).val+1))
      (fold m ((m+1)*v.val+(slot v j).val+1))=_
    simp only [valid_fold,seedAt,LightsGrid.read_cell]

end ReflectionLayout

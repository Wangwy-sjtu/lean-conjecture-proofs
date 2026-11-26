import LightsGrid
import Mathlib.FieldTheory.Finiteness

/-! Mirror extension of square-board quiet patterns across zero separator lines. -/
namespace ReflectionTiles
open LightsGrid LightsPolynomial
open scoped CharTwo

/-- Side length when there are q+1 copies of a seed of side m along each axis. -/
def side (m q : ℕ) := (m+1)*q+m

def fold (m t : ℕ) : ℕ :=
  let a := t%(2*(m+1))
  if a≤m+1 then a else 2*(m+1)-a

private theorem next_rem (a t : ℕ) (a2 : 1<a) :
    (t+1)%a = if t%a+1<a then t%a+1 else 0 := by
  rw [Nat.add_mod, Nat.mod_eq_of_lt a2]
  have b := Nat.mod_lt t (by omega : 0<a)
  split <;> rename_i h
  · exact Nat.mod_eq_of_lt h
  · rw [show t%a+1=a by omega,Nat.mod_self]

private def AdjacentValues (m a b c : ℕ) : Prop :=
  ((b=0 ∨ b=m+1) ∧ a=c) ∨
  (∃ i : Fin m, b=i.val+1 ∧ ((a=i.val ∧ c=i.val+2) ∨ (a=i.val+2 ∧ c=i.val)))

private theorem neighbors (m t : ℕ) :
    AdjacentValues m (fold m t) (fold m (t+1)) (fold m (t+2)) := by
  let h := m+1
  let z := t%(2*h)
  have low : z<2*h := Nat.mod_lt _ (by dsimp [h];omega)
  have n1 := next_rem (2*h) t (by dsimp [h];omega)
  have n2 := next_rem (2*h) (t+1) (by dsimp [h];omega)
  change (t+2)%(2*h)=_ at n2
  have up : fold m t = if z≤h then z else 2*h-z := rfl
  have mid : fold m (t+1) = if z+1<2*h then
      (if z+1≤h then z+1 else 2*h-(z+1)) else 0 := by
    dsimp only [fold];change (if (t+1)%(2*h)≤h then _ else _)=_
    rw [n1]; change (if (if z+1<2*h then z+1 else 0)≤h then _ else _)=_
    split_ifs <;> omega
  have nxt : fold m (t+2) = if z+1<2*h then
      (if z+2<2*h then (if z+2≤h then z+2 else 2*h-(z+2)) else 0) else 1 := by
    dsimp only [fold];change (if (t+2)%(2*h)≤h then _ else _)=_
    rw [n2,n1];change (if (if (if z+1<2*h then z+1 else 0)+1<2*h then _ else 0)≤h then _ else _)=_
    split_ifs <;> simp only [z,h] at * <;> omega
  rw [up,mid,nxt]
  clear n1 n2 up mid nxt
  have mh : h=m+1 := rfl
  unfold AdjacentValues
  by_cases gap : z+1=h ∨ z+1=2*h
  · left;split_ifs <;> omega
  · right
    by_cases b : z+1<h
    · refine ⟨⟨z,by omega⟩,?_⟩
      dsimp only;split_ifs <;> omega
    · refine ⟨⟨2*h-z-2,by omega⟩,?_⟩
      dsimp only;split_ifs <;> omega

theorem multiple (m q : ℕ) : fold m ((m+1)*q)=0 ∨ fold m ((m+1)*q)=m+1 := by
  unfold fold
  rw [show 2*(m+1)=(m+1)*2 by omega,Nat.mul_mod_mul_left]
  rcases (by omega : q%2=0 ∨ q%2=1) with h|h <;> simp [h]

private theorem interior (m t : ℕ) (h : t≤m+1) : fold m t=t := by
  simp [fold,Nat.mod_eq_of_lt (by omega : t<2*(m+1)),h]

def seedAt {m : ℕ} (b : Board m) (r c : ℕ) : F :=
  LightsGrid.read (fun i : Fin m => LightsGrid.read (b i) c) r

private theorem read_column {m : ℕ} (b : Board m) (r : ℕ) (j : Fin m) :
    LightsGrid.read (fun i => b i j) r=LightsGrid.read b r j := by
  cases r with
  | zero => rfl
  | succ r => by_cases h : r<m <;> simp [LightsGrid.read,h]

theorem border {m : ℕ} (b : Board m) (r c : ℕ) :
    (r=0 ∨ r=m+1 ∨ c=0 ∨ c=m+1) → seedAt b r c=0 := by
  rintro (rfl|rfl|rfl|rfl)
  · rfl
  · exact LightsGrid.read_end _
  · cases r with
    | zero => rfl
    | succ r => by_cases h : r<m <;> simp [seedAt,LightsGrid.read,h]
  · cases r with
    | zero => rfl
    | succ r => by_cases h : r<m <;> simp [seedAt,LightsGrid.read,h]

private theorem seed_rule {m : ℕ} (b : Board m) (quiet : b∈quietSpace m) (i j : Fin m) :
    seedAt b (i.val+1) (j.val+1)+seedAt b (i.val+1) j.val+seedAt b (i.val+1) (j.val+2)+
      seedAt b i.val (j.val+1)+seedAt b (i.val+2) (j.val+1)=0 := by
  simpa only [seedAt,LightsGrid.read_cell,read_column] using (quiet_iff_toggles b).mp quiet i j

def plane {m : ℕ} (b : Board m) (r c : ℕ) := seedAt b (fold m r) (fold m c)

private theorem plane_rule {m : ℕ} (b : Board m) (quiet : b∈quietSpace m) (r c : ℕ) :
    plane b (r+1) (c+1)+plane b (r+1) c+plane b (r+1) (c+2)+
      plane b r (c+1)+plane b (r+2) (c+1)=0 := by
  unfold plane
  rcases neighbors m r with ⟨rg,same⟩|⟨i,midR,dirR⟩
  · have e (a : ℕ) := border b _ a (Or.elim rg (fun h => Or.inl h) (fun h => Or.inr (Or.inl h)))
    rw [e,e,e,same];simp [CharTwo.add_self_eq_zero]
  rcases neighbors m c with ⟨cg,same⟩|⟨j,midC,dirC⟩
  · have e (a : ℕ) := border b a _ (Or.inr (Or.inr cg))
    rw [e,e,e,same];simp [CharTwo.add_self_eq_zero]
  · rw [midR,midC]
    rcases dirR with ⟨rr,rr'⟩|⟨rr,rr'⟩ <;> rcases dirC with ⟨cc,cc'⟩|⟨cc,cc'⟩ <;>
      rw [rr,rr',cc,cc'] <;> linear_combination seed_rule b quiet i j

def lift (q : ℕ) {m : ℕ} (b : Board m) : Board (side m q) :=
  fun i j => plane b (i.val+1) (j.val+1)

private theorem read_strip {n : ℕ} (f : ℕ → F) (at0 : f 0=0) (atEnd : f (n+1)=0)
    (j : ℕ) (h : j≤n+1) : LightsGrid.read (fun i : Fin n => f (i.val+1)) j=f j := by
  cases j with
  | zero => exact at0.symm
  | succ j => by_cases inside : j<n
              · simp [LightsGrid.read,inside]
              · have eq : j=n := by omega
                subst j;simp [LightsGrid.read,atEnd]

theorem lift_quiet {m : ℕ} (q : ℕ) (b : Board m) (hb : b∈quietSpace m) :
    lift q b∈quietSpace (side m q) := by
  rw [quiet_iff_toggles]
  intro i j
  let n := side m q
  have eq : n+1=(m+1)*(q+1) := by dsimp [n,side];ring
  have last : fold m (n+1)=0 ∨ fold m (n+1)=m+1 := eq ▸ multiple m (q+1)
  have first : fold m 0=0 := interior m 0 (by omega)
  have hr (c t : ℕ) (bd : t≤n+1) : LightsGrid.read (fun v : Fin n => plane b (v.val+1) c) t=plane b t c :=
    read_strip (fun r => plane b r c) (border b _ _ (Or.inl first))
      (border b _ _ (last.elim Or.inl (fun h => Or.inr (Or.inl h)))) _ bd
  have hc (r t : ℕ) (bd : t≤n+1) : LightsGrid.read (fun v : Fin n => plane b r (v.val+1)) t=plane b r t :=
    read_strip (fun c => plane b r c) (border b _ _ (Or.inr (Or.inr (Or.inl first))))
      (border b _ _ (Or.inr (Or.inr last))) _ bd
  rw [← read_column,← read_column]
  change plane b (i.val+1) (j.val+1)+
    LightsGrid.read (fun v : Fin n => plane b (i.val+1) (v.val+1)) j.val+
    LightsGrid.read (fun v : Fin n => plane b (i.val+1) (v.val+1)) (j.val+2)+
    LightsGrid.read (fun v : Fin n => plane b (v.val+1) (j.val+1)) i.val+
    LightsGrid.read (fun v : Fin n => plane b (v.val+1) (j.val+1)) (i.val+2)=0
  rw [hc _ _ (by omega),hc _ _ (by omega),hr _ _ (by omega),hr _ _ (by omega)]
  exact plane_rule b hb _ _

theorem lift_injective (m q : ℕ) : Function.Injective (lift q (m:=m)) := by
  intro b c eq
  ext i j
  have h : m≤side m q := by dsimp [side];omega
  have e := congrArg (fun v : Board (side m q) => v ⟨i.val,by omega⟩ ⟨j.val,by omega⟩) eq
  simpa only [lift,plane,interior m (i.val+1) (by omega),interior m (j.val+1) (by omega),
    seedAt,LightsGrid.read_cell] using e

theorem lift_exhausts {m q : ℕ} (dim : Module.finrank F (quietSpace (side m q))=Module.finrank F (quietSpace m))
    (x : Board (side m q)) (hx : x∈quietSpace (side m q)) :
    ∃ b : quietSpace m, lift q b.val=x := by
  classical
  let K := quietSpace m
  let L := quietSpace (side m q)
  letI : Fintype K := Fintype.ofFinite K
  letI : Fintype L := Fintype.ofFinite L
  let f : K → L := fun b => ⟨_,lift_quiet q b.val b.property⟩
  have inj : Function.Injective f := fun _ _ eq =>
    Subtype.ext (lift_injective m q (congrArg Subtype.val eq))
  have cards : Fintype.card K=Fintype.card L := by
    rw [Module.card_eq_pow_finrank (K:=F) (V:=↥K),Module.card_eq_pow_finrank (K:=F) (V:=↥L)]
    rw [show Module.finrank F (↥L)=Module.finrank F (↥K) from dim]
  obtain ⟨b,eq⟩ := (Fintype.bijective_iff_injective_and_card f).2 ⟨inj,cards⟩ |>.2 ⟨x,hx⟩
  exact ⟨b,congrArg Subtype.val eq⟩

end ReflectionTiles

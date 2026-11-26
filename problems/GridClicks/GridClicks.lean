import ClickTiles
import FourIndex

/-! Boyles's higher-nullity Most Clicks Problem on the nullity-four family. -/
namespace GridClicks
open LightsPolynomial LightsGrid ClickTiles
open scoped BigOperators CharTwo

def click (v : F) : ℕ := if v=0 then 0 else 1
def block (x : Small → F) (k : Key) : ℕ := ∑ c, click (x c+bit k c)
private def focus : Small := (0,1)
private def groupBit (g : Fin 2) : F := if g=0 then 0 else 1
private def member (g : Fin 2) (h : Fin 8) : Key :=
  ⟨4*(h.val/2)+2*g.val+h.val%2,by omega⟩

private theorem column_count : ∀ (g : Fin 2) (c : Small) (v : F),
    (∑ h, click (v+bit (member g h) c)) =
      (if c=focus then 8*click (v+groupBit g) else 4) := by decide +kernel

private theorem group_sum (x : Small → F) (g : Fin 2) :
    (∑ h, block x (member g h))=60+8*click (x focus+groupBit g) := by
  unfold block
  rw [Finset.sum_comm]
  simp_rw [column_count]
  let z := 8*click (x focus+groupBit g)
  have splitc (c : Small) : (if c=focus then 8*click (x c+groupBit g) else 4) =
      (if c=focus then z else 0)+(if c=focus then 0 else 4) := by
    by_cases h : c=focus <;> simp [h,z]
  simp_rw [splitc,Finset.sum_add_distrib]
  have residue : (∑ c : Small, if c=focus then 0 else 4)=60 := by decide +kernel
  simp [residue,z,Nat.add_comm]

private theorem flip_count : ∀ v : F, click (v+groupBit 0)+click (v+groupBit 1)=1 := by decide

theorem active_upper {T : Type*} [Fintype T] (odd : Odd (Fintype.card T))
    (x : T → Small → F) : ∃ k, (∑ t, block (x t) k)<8*Fintype.card T := by
  classical
  let h (g : Fin 2) := ∑ t, click (x t focus+groupBit g)
  have total : h 0+h 1=Fintype.card T := by
    dsimp [h]; rw [← Finset.sum_add_distrib]; simp_rw [flip_count]; simp
  obtain ⟨d,hd⟩ := odd
  obtain ⟨g,low⟩ : ∃ g, 2*h g<Fintype.card T := by
    by_cases b : 2*h 0<Fintype.card T
    · exact ⟨0,b⟩
    · exact ⟨1,by omega⟩
  have agg : (∑ j, ∑ t, block (x t) (member g j))=60*Fintype.card T+8*h g := by
    rw [Finset.sum_comm]; simp_rw [group_sum]; rw [Finset.sum_add_distrib]
    simp [h,Finset.mul_sum,Nat.mul_comm]
  by_contra! bad
  have hh := Finset.sum_le_sum (s:=(Finset.univ : Finset (Fin 8)))
    (fun j _ => bad (member g j))
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] at hh
  omega

private def hard (c : Small) : F :=
  if (0x1bd:ℕ).testBit (4*c.1.val+c.2.val) then 1 else 0
private theorem seed_hard : ∀ k, 7≤block hard k := by decide +kernel
private theorem complements : ∀ k, block (fun _ => 0) k+block (fun _ => 1) k=16 := by
  decide +kernel

theorem active_lower {T : Type*} [Fintype T] (odd : Odd (Fintype.card T)) :
    ∃ x : T → Small → F, ∀ k, 8*Fintype.card T≤(∑ t,block (x t) k)+1 := by
  classical
  obtain ⟨s,h⟩ := odd
  let A := Unit ⊕ Fin s ⊕ Fin s
  let e : T ≃ A := Fintype.equivOfCardEq (by simp [A,h];omega)
  let tiles : A → Small → F := fun a => match a with
    | .inl _ => hard
    | .inr (.inl _) => fun _ => 0
    | .inr (.inr _) => fun _ => 1
  refine ⟨fun t => tiles (e t),fun k => ?_⟩
  rw [e.sum_comp (fun t => block (tiles t) k)]
  have groups : (∑ t, block (tiles t) k)=block hard k+
      (s*block (fun _=>0) k+s*block (fun _=>1) k) := by
    simp [A,tiles,Fintype.sum_sum_type]
  rw [groups,← Nat.mul_add,complements]
  have := seed_hard k
  omega

def weight {n : ℕ} (b : Board n) : ℕ :=
  ∑ c : Fin n × Fin n, click (b c.1 c.2)

/-- The output of one complete pattern of presses on the actual five-cell board. -/
def effect {n : ℕ} (b : Board n) : Board n := fun i j =>
  b i j + LightsGrid.read (b i) j.val + LightsGrid.read (b i) (j.val+2) +
    LightsGrid.read b i.val j + LightsGrid.read b (i.val+2) j

private theorem read_linear {V : Type*} [AddMonoid V] {n : ℕ} (b c : Fin n → V) (t : ℕ) :
    LightsGrid.read (b+c) t=LightsGrid.read b t+LightsGrid.read c t := by
  cases t with
  | zero => simp [LightsGrid.read]
  | succ t => by_cases h : t<n <;> simp [LightsGrid.read,h]

private theorem same_effect {n : ℕ} (x y : Board n) :
    effect x=effect y ↔ x+y∈quietSpace n := by
  rw [quiet_iff_toggles]
  have linear (i j : Fin n) :
      effect (x+y) i j=effect x i j+effect y i j := by
    simp only [effect,Pi.add_apply,read_linear];abel
  change effect x=effect y ↔ ∀ i j, effect (x+y) i j=0
  constructor
  · intro eq i j; rw [linear,eq,CharTwo.add_self_eq_zero]
  · intro eq; ext i j
    exact CharTwo.add_eq_zero.mp ((linear i j).symm.trans (eq i j))

/-- The largest minimum number of presses over all solvable light states. -/
def IsMostClicks (n M : ℕ) : Prop :=
  (∀ a : Board n, (∃ x, effect x=a) → ∃ y, effect y=a ∧ weight y≤M) ∧
  (∃ a : Board n, (∃ x, effect x=a) ∧ ∀ y, effect y=a → M≤weight y)

private abbrev Shape (q : ℕ) := Inactive q ⊕ (Tiles q × Small)
private def tilesOf {q : ℕ} (x : Board (5*q-1)) (s : Shape q) : F :=
  x ((positions q s).1) ((positions q s).2)
private def boardOf {q : ℕ} (f : Shape q → F) : Board (5*q-1) :=
  fun i j => f ((positions q).symm (i,j))

private theorem unpack {q : ℕ} (f : Shape q → F) (s : Shape q) :
    tilesOf (boardOf f) s=f s := by simp [tilesOf,boardOf]

private theorem weight_tiles {q : ℕ} (x : Board (5*q-1)) (k : Key) :
    weight (x+pattern (5*q-1) k)=
      (∑ i : Inactive q,click (tilesOf x (.inl i)))+
        ∑ t : Tiles q,block (fun c => tilesOf x (.inr (t,c))) k := by
  let value := fun s : Shape q => click (tilesOf x s+
    (match s with | .inl _ => 0 | .inr (_,c) => bit k c))
  have total : weight (x+pattern (5*q-1) k)=∑ s, value s := by
    symm; apply Fintype.sum_equiv (positions q)
    intro s; change click (tilesOf x s+_)=click (_+pattern _ k _ _)
    rw [pattern_at];rfl
  rw [total,Fintype.sum_sum_type]
  congr 1
  · apply Finset.sum_congr rfl; intro i _
    change click (tilesOf x (.inl i)+0)=_; rw [add_zero]
  · rw [Fintype.sum_prod_type]; rfl

private theorem board_twice {n : ℕ} (x : Board n) : x+x=0 := by
  ext i j; exact CharTwo.add_self_eq_zero (x i j)

/-- The nullity-four empirical fit in the author's revised conjecture list. -/
theorem four (q : ℕ) (odd : Odd q) (dim : Module.finrank F (quietSpace (5*q-1))=4) :
    IsMostClicks (5*q-1) (17*q^2-10*q) := by
  classical
  let n := 5*q-1
  have cards : Fintype.card (Tiles q)=q*q := by simp [Tiles]
  have ot : Odd (Fintype.card (Tiles q)) := cards ▸ odd.mul odd
  have qp := odd.pos
  have formula : 17*q^2-10*q+1=Fintype.card (Inactive q)+8*Fintype.card (Tiles q) := by
    rw [cardinal_inactive,cards]
    obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero qp.ne'
    have sub : j.succ-1=j := by omega
    rw [sub]
    have h : 10*(j+1)≤17*(j+1)^2 := by nlinarith
    have addback := Nat.sub_add_cancel h
    nlinarith only [addback]
  constructor
  · rintro _ ⟨x,rfl⟩
    obtain ⟨k,hk⟩ := active_upper ot (fun t c => tilesOf x (.inr (t,c)))
    refine ⟨x+pattern n k,?_,?_⟩
    · apply (same_effect _ _).2
      rw [add_right_comm,board_twice,zero_add]; exact quiet q qp k
    · rw [weight_tiles]
      have single (i : Inactive q) : click (tilesOf x (.inl i))≤1 := by unfold click;split <;> decide
      have bound := Finset.sum_le_sum (s:=Finset.univ) (fun i _ => single i)
      simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul,mul_one] at bound
      omega
  · obtain ⟨active,far⟩ := active_lower ot
    let f : Shape q → F := Sum.elim (fun _ => 1) (fun tc => active tc.1 tc.2)
    let x := boardOf f
    refine ⟨effect x,⟨x,rfl⟩,?_⟩
    intro y eq
    obtain ⟨k,form⟩ := exhaustive q qp dim (x+y) ((same_effect x y).mp eq.symm)
    have py : y=x+pattern n k := by rw [form,← add_assoc,board_twice,zero_add]
    rw [py,weight_tiles]
    simp only [x,unpack,f,Sum.elim_inl,Sum.elim_inr]
    have ones : click 1=1 := by decide
    simp only [ones,Finset.sum_const,Finset.card_univ,smul_eq_mul,mul_one]
    change 17*q^2-10*q≤Fintype.card (Inactive q)+∑ t,block (active t) k
    have h := far k
    omega

/-- In terms of the physical grid alone, every square of nullity four has the
predicted worst-case cost. The size congruence was previously known. -/
theorem every_nullity_four (n : ℕ) (dim : Module.finrank F (quietSpace n)=4) :
    ∃ q : ℕ, Odd q ∧ n=5*q-1 ∧ IsMostClicks n (17*q^2-10*q) := by
  obtain ⟨q,odd,rfl⟩ := FourIndex.size n dim
  exact ⟨q,odd,rfl,four q odd dim⟩

/-- An explicit infinite family with no nullity hypothesis. These are the actual
squares of side 5^(k+1)−1, with the multiplier q=5^k. -/
theorem five_powers (k : ℕ) :
    IsMostClicks (5^(k+1)-1) (17*(5^k)^2-10*5^k) := by
  have cp : Nat.Coprime (5^k) 3 := (by decide : Nat.Coprime 5 3).pow_left k
  have gg : Nat.gcd (5^(k+1)) (2^4-1)=5 := by
    change Nat.gcd (5^(k+1)) (5*3)=5
    rw [pow_succ',Nat.gcd_mul_left,cp.gcd_eq_one,Nat.mul_one]
  have red := OddStabilization.nullity_reduction 5 4 (k+1) (by decide) (by decide)
  rw [gg] at red
  have base : Module.finrank F (quietSpace (5-1))=4 :=
    (OddStabilization.physical 5 (by decide)).trans
      (OddGridExamples.certificate 5 2 0x15 4 (by decide +kernel) (by decide) (by decide +kernel))
  rw [pow_succ'] at red ⊢
  exact four (5^k) ((by decide : Odd (5:ℕ)).pow) (red.trans base)

#print axioms four
#print axioms every_nullity_four
#print axioms five_powers
end GridClicks

import PressCost
import ReflectionLayout

/-! A finite seed average bound with a matching single-seed witness scales to
all reflected copies whose quiet patterns lift from the seed. -/
namespace SeedCosts
open LightsGrid LightsPolynomial GridClicks ReflectionTiles ReflectionLayout
open scoped BigOperators

def baseCost {m : ℕ} (x : Cell m → F) (b : Board m) :=
  ∑ c,click (x c+b c.1 c.2)

private abbrev Shape (m q : ℕ) := Gaps m q ⊕ (Copies q × Cell m)
private noncomputable def tilesOf {m q : ℕ} (x : Board (side m q)) (s : Shape m q) :=
  x (positions m q s).1 (positions m q s).2
private noncomputable def boardOf {m q : ℕ} (f : Shape m q → F) : Board (side m q) :=
  fun i j => f ((positions m q).symm (i,j))
private theorem unpack {m q : ℕ} (f : Shape m q → F) (s : Shape m q) :
    tilesOf (boardOf f) s=f s := by simp [tilesOf,boardOf]

private theorem weight_tiles {m q : ℕ} (x : Board (side m q)) (b : Board m) :
    weight (x+lift q b)=(∑ g : Gaps m q,click (tilesOf x (.inl g)))+
      ∑ t : Copies q,baseCost (fun c => tilesOf x (.inr (t,c))) b := by
  let val := fun s : Shape m q => click (tilesOf x s+
    (match s with | .inl _ => 0 | .inr (_,c) => b c.1 c.2))
  have total : weight (x+lift q b)=∑ s,val s := by
    symm;apply Fintype.sum_equiv (positions m q)
    intro s;change click (tilesOf x s+_)=click (_+lift q b _ _)
    rw [lift_at];rfl
  rw [total,Fintype.sum_sum_type]
  congr 1
  · apply Finset.sum_congr rfl
    intro c _
    change click (tilesOf x (.inl c)+0)=_
    rw [add_zero]
  · rw [Fintype.sum_prod_type];rfl

private theorem some_small {K : Type*} [Fintype K] [Nonempty K] (a : K → ℕ) (L : ℕ)
    (h : ∑ k,a k≤Fintype.card K*L) : ∃ k,a k≤L := by
  by_contra! greater
  have more := Finset.sum_le_sum (s:=(Finset.univ : Finset K))
    (fun k _ => Nat.succ_le_of_lt (greater k))
  simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul,Nat.mul_succ] at more
  have hp := Fintype.card_pos (α:=K)
  omega

/-- An upper bound on the average distance to the enumerated quiet patterns
and a single seed attaining that bound from below suffice for all copies. -/
theorem flat {m : ℕ} {K : Type*} [Fintype K] [Nonempty K] (code : K → Board m)
    (quiet : ∀ k,code k∈quietSpace m)
    (all : ∀ b : quietSpace m, ∃ k,code k=b.val)
    (B : ℕ) (average : ∀ x, (∑ k,baseCost x (code k))≤Fintype.card K*B)
    (witness : ∃ x,∀ k,B≤baseCost x (code k)) (q : ℕ)
    (dim : Module.finrank F (quietSpace (side m q))=Module.finrank F (quietSpace m)) :
    IsMostClicks (side m q) (Fintype.card (Gaps m q)+(q+1)^2*B) := by
  classical
  have ct : Fintype.card (Copies q)=(q+1)^2 := by simp [Copies,pow_two]
  constructor
  · rintro _ ⟨x,rfl⟩
    let block := fun (t : Copies q) k => baseCost (fun c => tilesOf x (.inr (t,c))) (code k)
    have avg : (∑ k,∑ t,block t k)≤Fintype.card K*((q+1)^2*B) := by
      rw [Finset.sum_comm]
      have b := Finset.sum_le_sum (s:=Finset.univ) (fun t _ => average (fun c => tilesOf x (.inr (t,c))))
      simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul,ct] at b
      simpa only [block,Nat.mul_left_comm] using b
    obtain ⟨k,hk⟩ := some_small _ _ avg
    refine ⟨x+lift q (code k),?_,?_⟩
    · apply (same_effect _ _).2
      rw [add_right_comm,board_twice,zero_add];exact lift_quiet q _ (quiet k)
    · rw [weight_tiles]
      have single (g : Gaps m q) : click (tilesOf x (.inl g))≤1 := by unfold click;split <;> decide
      have bound := Finset.sum_le_sum (s:=Finset.univ) (fun g _ => single g)
      simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul,mul_one] at bound
      exact Nat.add_le_add bound hk
  · obtain ⟨seed,far⟩ := witness
    let f : Shape m q → F := Sum.elim (fun _ => 1) (fun p => seed p.2)
    let x := boardOf f
    refine ⟨effect x,⟨x,rfl⟩,?_⟩
    intro y he
    obtain ⟨b,hb⟩ := lift_exhausts dim (x+y) ((same_effect _ _).mp he.symm)
    obtain ⟨k,hk⟩ := all b
    have py : y=x+lift q (code k) := by rw [hk,hb,← add_assoc,board_twice,zero_add]
    rw [py,weight_tiles]
    simp only [x,unpack,f,Sum.elim_inl,Sum.elim_inr]
    have ones : click 1=1 := by decide
    simp only [ones,Finset.sum_const,Finset.card_univ,smul_eq_mul,mul_one,ct]
    exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (far k)) _

end SeedCosts

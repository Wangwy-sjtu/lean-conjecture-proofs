import SeedCosts
import SixIndex

/-! The nullity-six Most Clicks formula. Six seed patterns encode the actual
11 by 11 square. Every nonconstant seed column occurs an even number of times. -/
namespace SixClicks
open LightsPolynomial LightsGrid GridClicks ReflectionLayout ReflectionTiles SeedCosts
open scoped BigOperators

abbrev Key := Fin 64
private def seedMask (k : Key) : ℕ :=
  (if k.val.testBit 0 then 0x1bb822e0328358228bbb28236022835 else 0) ^^^
  (if k.val.testBit 1 then 0x114769046c74436dd106c641076845 else 0) ^^^
  (if k.val.testBit 2 then 0x1918f4c89c6d72145313c6c948f489d else 0) ^^^
  (if k.val.testBit 3 then 0x411c7451aaa4136d904aab145c7104 else 0) ^^^
  (if k.val.testBit 4 then 0x133399603c6dd0a28999c6c36399217 else 0) ^^^
  (if k.val.testBit 5 then 0x10531b5556c6504001416c75571b414 else 0)
private def pos (c : Cell 11) := 11*c.1.val+c.2.val
private def readBit (a j : ℕ) : F := if a.testBit j then 1 else 0
private def code (k : Key) : Board 11 := fun i j => readBit (seedMask k) (pos (i,j))

private def hard (c : Cell 11) := readBit 0x201100009fffffffffffffff (pos c)
private def cap (c : Cell 11) : ℕ := if (0x201100009200011008000000:ℕ).testBit (pos c) then 64 else 32
private def top (b : Board 11) : ℕ :=
  ∑ i : Fin 6, if b 0 ⟨i.val+5,by omega⟩=1 then 2^i.val else 0

set_option maxHeartbeats 0 in
private theorem distinct_tags : ∀ k : Key,top (code k)=k.val := by decide +kernel

set_option maxHeartbeats 0 in
private theorem rules : ∀ (k : Key) (i j : Fin 11),effect (code k) i j=0 := by decide +kernel

private theorem quiet (k : Key) : code k∈quietSpace 11 :=
  (quiet_iff_toggles _).2 (rules k)

private theorem exhaustive (b : quietSpace 11) : ∃ k,code k=b.val := by
  classical
  let K := quietSpace 11
  letI : Fintype K := Fintype.ofFinite _
  let f : Key → K := fun k => ⟨_,quiet k⟩
  have inj : Function.Injective f := fun k l eq => Fin.ext (by
    have e := congrArg (fun v : K => top v.val) eq
    change top (code k)=top (code l) at e
    simpa only [distinct_tags] using e)
  have card : Fintype.card Key=Fintype.card K := by
    rw [Module.card_eq_pow_finrank (K:=F) (V:=↥K),show Module.finrank F (↥K)=6 from SixIndex.base,ZMod.card,Fintype.card_fin]
    decide
  obtain ⟨k,hk⟩ := (Fintype.bijective_iff_injective_and_card f).2 ⟨inj,card⟩ |>.2 b
  exact ⟨k,congrArg Subtype.val hk⟩

set_option maxHeartbeats 0 in
private theorem columns : ∀ (c : Cell 11) (x : F), (∑ k,click (x+code k c.1 c.2))≤cap c := by
  decide +kernel

private theorem total : (∑ c : Cell 11,cap c)=64*65 := by decide +kernel

private theorem average (x : Cell 11 → F) : (∑ k,baseCost x (code k))≤Fintype.card Key*65 := by
  unfold baseCost
  rw [Finset.sum_comm]
  change (∑ c,∑ k,click (x c+code k c.1 c.2))≤64*65
  rw [← total]
  exact Finset.sum_le_sum (fun c _ => columns c (x c))

set_option maxHeartbeats 0 in
private theorem level : ∀ k,65≤baseCost hard (code k) := by decide +kernel

/-- The conjectured value holds at every stated multiplier. -/
theorem six (q : ℕ) (positive : 0<q) (dim : Module.finrank F (quietSpace (12*q-1))=6) :
    IsMostClicks (12*q-1) (88*q^2-24*q+1) := by
  obtain ⟨t,rfl⟩ := Nat.exists_eq_succ_of_ne_zero positive.ne'
  have board : 12*(t+1)-1=side 11 t := by unfold side;omega
  rw [board] at dim ⊢
  have h := flat code quiet exhaustive 65 average ⟨hard,level⟩ t (dim.trans SixIndex.base.symm)
  convert h using 1
  have gaps : Fintype.card (Gaps 11 t)=t*t+2*t*((t+1)*11) := by
    simp [Gaps,Fintype.card_sum,Fintype.card_prod];ring
  rw [gaps]
  have bd : 24*(t+1)≤88*(t+1)^2 := by nlinarith
  have sub := Nat.sub_add_cancel bd
  change 88*(t+1)^2-24*(t+1)+1=_
  nlinarith only [sub]

/-- Every physical nullity-six square has the indicated size and worst cost. -/
theorem every_nullity_six (n : ℕ) (dim : Module.finrank F (quietSpace n)=6) :
    ∃ q : ℕ, Odd q ∧ n=12*q-1 ∧ IsMostClicks n (88*q^2-24*q+1) := by
  obtain ⟨q,odd,rfl⟩ := SixIndex.size n dim
  exact ⟨q,odd,rfl,six q odd.pos dim⟩

theorem three_powers (k : ℕ) :
    IsMostClicks (12*3^k-1) (88*(3^k)^2-24*3^k+1) := six _ (by positivity) (SixIndex.ternary k)

#print axioms three_powers
#print axioms six
#print axioms every_nullity_six
end SixClicks

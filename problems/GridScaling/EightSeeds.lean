import GridScaling
import GridFactors
import OddGridExamples

/-! Exact support of the two nullity-eight seeds. -/
namespace EightSeeds
open LightsPolynomial LightsGrid GridClicks ReflectionLayout GridScaling
open Polynomial GridGcd OddStabilization GridFactors
open scoped Polynomial

private def bits {m : ℕ} (w : ℕ) : Board m := fun i j =>
  if w.testBit (m*i.val+j.val) then 1 else 0

private def words9 : Fin 8 → ℕ := ![
  0xa8d6228ee280d8200e02,
  0x104c7545aa441d8501a05,
  0x8aed82b80aa358883808,
  0x556ad036b456c1047611,
  0xa2dba800eaad6220e020,
  0x140b01437044ab455c641,
  0x2a35a8bb828d80838080,
  0x101c1d15dc00775170701]

set_option maxHeartbeats 0 in
private theorem patterns9 : ∀ (k : Fin 8) (i j : Fin 9), effect (bits (words9 k)) i j=0 := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem coverage9 : ∀ c : Cell 9, c≠(4,4) → ∃ k : Fin 8, bits (words9 k) c.1 c.2≠0 := by
  decide +kernel

private def words16 : Fin 8 → ℕ := ![
  0xd6ee1045ee0355413b600551363b4401d838405538ed15140d5b0454038d0105,
  0xc6ab28a8ab0780226b70080a776baa02dc6ca0806dac20a21c1b0a8206dc0288,
  0xee034504038d4055e3581411d5630105d6ee1140ed8e5115363b10450ed60454,
  0x6dac8022addb20a2dc6c2a20b71ca88a1ac78aa0c077aa026b70222a1c1b080a,
  0x38d05510ed6114035b65541e0d50454ee0341500d5b5010d563450438ed1045,
  0x6b708828b71c0a82addbaa0206dca208b1c028a8dc6c222aab078aa071b720a2,
  0x363b4150d5635444038d5115d83855410d5b4401e3581045dbb51140e0d54055,
  0x1c1b2a20776b8828ab0720a2dab0222aaddb82aa6b700a8271b7a080c0778022]

set_option maxHeartbeats 0 in
private theorem patterns16 : ∀ (k : Fin 8) (i j : Fin 16), effect (bits (words16 k)) i j=0 := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem coverage16 : ∀ c : Cell 16, ∃ k : Fin 8, bits (words16 k) c.1 c.2≠0 := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem center (v : quietSpace 9) : v.val 4 4=0 := by
  have eq (i j : Fin 9) := (quiet_iff_toggles v.val).mp v.property i j
  let x (i j : ℕ) : F := v.val ⟨i%9,by omega⟩ ⟨j%9,by omega⟩
  have two : (2:F)=0 := by decide
  have four : (4:F)=0 := by decide
  have e00 : x 0 0+0+x 0 1+0+x 1 0=0 := eq 0 0
  have e10 : x 1 0+0+x 1 1+x 0 0+x 2 0=0 := eq 1 0
  have e11 : x 1 1+x 1 0+x 1 2+x 0 1+x 2 1=0 := eq 1 1
  have e20 : x 2 0+0+x 2 1+x 1 0+x 3 0=0 := eq 2 0
  have e22 : x 2 2+x 2 1+x 2 3+x 1 2+x 3 2=0 := eq 2 2
  have e31 : x 3 1+x 3 0+x 3 2+x 2 1+x 4 1=0 := eq 3 1
  have e32 : x 3 2+x 3 1+x 3 3+x 2 2+x 4 2=0 := eq 3 2
  have e33 : x 3 3+x 3 2+x 3 4+x 2 3+x 4 3=0 := eq 3 3
  have e44 : x 4 4+x 4 3+x 4 5+x 3 4+x 5 4=0 := eq 4 4
  have e51 : x 5 1+x 5 0+x 5 2+x 4 1+x 6 1=0 := eq 5 1
  have e52 : x 5 2+x 5 1+x 5 3+x 4 2+x 6 2=0 := eq 5 2
  have e55 : x 5 5+x 5 4+x 5 6+x 4 5+x 6 5=0 := eq 5 5
  have e60 : x 6 0+0+x 6 1+x 5 0+x 7 0=0 := eq 6 0
  have e63 : x 6 3+x 6 2+x 6 4+x 5 3+x 7 3=0 := eq 6 3
  have e65 : x 6 5+x 6 4+x 6 6+x 5 5+x 7 5=0 := eq 6 5
  have e66 : x 6 6+x 6 5+x 6 7+x 5 6+x 7 6=0 := eq 6 6
  have e70 : x 7 0+0+x 7 1+x 6 0+x 8 0=0 := eq 7 0
  have e73 : x 7 3+x 7 2+x 7 4+x 6 3+x 8 3=0 := eq 7 3
  have e75 : x 7 5+x 7 4+x 7 6+x 6 5+x 8 5=0 := eq 7 5
  have e77 : x 7 7+x 7 6+x 7 8+x 6 7+x 8 7=0 := eq 7 7
  have e81 : x 8 1+x 8 0+x 8 2+x 7 1+0=0 := eq 8 1
  have e82 : x 8 2+x 8 1+x 8 3+x 7 2+0=0 := eq 8 2
  have e86 : x 8 6+x 8 5+x 8 7+x 7 6+0=0 := eq 8 6
  have e87 : x 8 7+x 8 6+x 8 8+x 7 7+0=0 := eq 8 7
  have e88 : x 8 8+x 8 7+0+x 7 8+0=0 := eq 8 8
  change x 4 4=0
  linear_combination (norm := (ring_nf;simp [two,four]))
    e00+
    e10+
    e11+
    e20+
    e22+
    e31+
    e32+
    e33+
    e44+
    e51+
    e52+
    e55+
    e60+
    e63+
    e65+
    e66+
    e70+
    e73+
    e75+
    e77+
    e81+
    e82+
    e86+
    e87+
    e88

theorem active9 : activeCount 9=80 := by
  have criterion (c : Cell 9) : IsActive c ↔ c≠(4,4) := by
    constructor
    · rintro ⟨v,h⟩ rfl;exact h (center v)
    · intro nc
      obtain ⟨k,hk⟩ := coverage9 c nc
      exact ⟨⟨_,(quiet_iff_toggles _).2 (patterns9 k)⟩,hk⟩
  let e : Active 9 ≃ {c : Cell 9 // c≠(4,4)} :=
    Equiv.subtypeEquivRight criterion
  exact (Fintype.card_congr e).trans (by decide +kernel)

theorem active16 : activeCount 16=256 := by
  have all (c : Cell 16) : IsActive c := by
    obtain ⟨k,hk⟩ := coverage16 c
    exact ⟨⟨_,(quiet_iff_toggles _).2 (patterns16 k)⟩,hk⟩
  let e : Active 16 ≃ Cell 16 :=
    ⟨Subtype.val,fun c=>⟨c,all c⟩,fun _=>rfl,fun _=>rfl⟩
  exact (Fintype.card_congr e).trans (by simp [Cell,Fintype.card_prod])

theorem base9 : Module.finrank F (quietSpace 9)=8 :=
  (physical 10 (by decide)).trans
    (OddGridExamples.certificate 10 15 0x111 8 (by decide +kernel) (by decide) (by decide))

theorem base16 : Module.finrank F (quietSpace 16)=8 :=
  (physical 17 (by decide)).trans
    (OddGridExamples.certificate 17 15 0x105 8 (by decide +kernel) (by decide) (by decide))

theorem family17 (k : ℕ) : Module.finrank F (quietSpace (17*17^k-1))=8 := by
  have cp : Nat.Coprime (17^k) 15 := (by decide : Nat.Coprime 17 15).pow_left k
  have gg : Nat.gcd (17^(k+1)) (2^8-1)=17 := by
    change Nat.gcd (17^(k+1)) (17*15)=17
    rw [pow_succ',Nat.gcd_mul_left,cp.gcd_eq_one,Nat.mul_one]
  have z := nullity_reduction 17 8 (k+1) (by decide) (by decide)
  rw [gg,pow_succ'] at z
  exact z.trans base16

theorem family10 (k : ℕ) : Module.finrank F (quietSpace (10*5^k-1))=8 := by
  have cp : Nat.Coprime (5^k) 3 := (by decide : Nat.Coprime 5 3).pow_left k
  have gg : Nat.gcd (5^(k+1)) (2^4-1)=5 := by
    change Nat.gcd (5^(k+1)) (5*3)=5
    rw [pow_succ',Nat.gcd_mul_left,cp.gcd_eq_one,Nat.mul_one]
  have z := nullity_reduction 5 4 (k+1) (by decide) (by decide)
  rw [gg,physical _ (by positivity),physical 5 (by decide)] at z
  have deg := z.trans (OddGridExamples.certificate 5 10 0x15 4 (by decide +kernel) (by decide) (by decide))
  have idx : 10*5^k=2^1*5^(k+1) := by rw [pow_succ];ring
  have three : ¬3∣5^(k+1) := fun h => (by decide : ¬3∣5) ((by decide : Nat.Prime 3).dvd_of_dvd_pow h)
  rw [physical _ (by positivity),idx,dyadic_common 1 _ ((by decide : Odd (5:ℕ)).pow),
    if_neg three,one_mul,natDegree_pow,deg]
  decide

#print axioms active9
#print axioms active16
#print axioms family10
#print axioms family17
end EightSeeds

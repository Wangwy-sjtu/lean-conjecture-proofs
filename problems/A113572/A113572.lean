import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.Ring

/-!
# Murthy's restricted-digit multiples, OEIS A113572

Positions are counted from the most significant digit starting at one.
The construction uses the pairs (2,3) and (8,9). All residues modulo `m`
with `5 ∤ m` can be realized with `m-1` binary-valued decimal digits.
-/

namespace RestrictedMultiple

/-- Least significant digit first, as in `Nat.digits`. The most significant
position uses `1`. Other positions and their digits have matching primality,
and composite digits must exceed one. -/
def pattern : List ℕ → Prop
  | [] => False
  | [d] => d = 1
  | d :: e :: ds =>
    (if Nat.Prime (ds.length + 2) then Nat.Prime d else 1 < d ∧ ¬ Nat.Prime d) ∧
      pattern (e :: ds)

/-- An actual decimal expansion with the required width, divisibility, and digits. -/
def admissible (n x : ℕ) : Prop :=
  n ∣ x ∧ (Nat.digits 10 x).length = n ∧ pattern (Nat.digits 10 x)

/-- Every digit in this word is either zero or one. The list is least significant first. -/
def BinaryDigits (bs : List ℕ) : Prop := ∀ d ∈ bs, d = 0 ∨ d = 1

private def residues (m : ℕ) [NeZero m] : ℕ → Finset (ZMod m)
  | 0 => {0}
  | k+1 =>
    let shifted := (residues m k).image (fun z => 10 * z)
    shifted ∪ shifted.image (· + 1)

private theorem residues_nonempty (m : ℕ) [NeZero m] (k : ℕ) : (residues m k).Nonempty := by
  induction k with
  | zero => exact ⟨0, by simp [residues]⟩
  | succ k ih => exact (ih.image (fun z => 10*z)).mono Finset.subset_union_left

private theorem successor_growth {m : ℕ} [NeZero m] (s : Finset (ZMod m)) (hs : s.Nonempty) :
    s = Finset.univ ∨ s.card < (s ∪ s.image (· + 1)).card := by
  classical
  by_cases hall : s = Finset.univ
  · exact Or.inl hall
  right
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_union_left, ?_⟩
  intro heq
  have hclosed (x : ZMod m) (hx : x ∈ s) : x+1 ∈ s := by
    rw [heq]
    exact Finset.mem_union_right _ (Finset.mem_image_of_mem (· + 1) hx)
  obtain ⟨x, hx⟩ := hs
  have hallx (j : ℕ) : x+(j : ZMod m) ∈ s := by
    induction j with
    | zero => simpa using hx
    | succ j ih => simpa [Nat.cast_succ, add_assoc] using hclosed _ ih
  apply hall
  apply Finset.eq_univ_iff_forall.mpr
  intro y
  simpa using hallx (y-x).val

private theorem residues_card (m : ℕ) [NeZero m] (hcop : Nat.Coprime 10 m) (k : ℕ) :
    min (k+1) m ≤ (residues m k).card := by
  classical
  induction k with
  | zero => simp [residues]
  | succ k ih =>
    let s := (residues m k).image (fun z => 10*z)
    have hu : IsUnit (10 : ZMod m) := (ZMod.isUnit_iff_coprime 10 m).2 hcop
    have hc : s.card = (residues m k).card :=
      Finset.card_image_of_injective _ hu.mul_right_injective
    have hb := (residues m k).card_le_univ
    rw [ZMod.card] at hb
    change min (k+1+1) m ≤ (s ∪ s.image (· + 1)).card
    rcases successor_growth s ((residues_nonempty m k).image _) with h | h
    · have hsub : s.card ≤ (s ∪ s.image (· + 1)).card := Finset.card_le_card Finset.subset_union_left
      rw [show s.card = m by rw [h, Finset.card_univ, ZMod.card]] at hsub
      exact (min_le_right _ _).trans hsub
    · omega

private theorem residues_witness {m : ℕ} [NeZero m] {k : ℕ} {z : ZMod m}
    (hz : z ∈ residues m k) : ∃ bs : List ℕ,
    bs.length = k ∧ BinaryDigits bs ∧
    ((Nat.ofDigits 10 bs : ℕ) : ZMod m) = z := by
  induction k generalizing z with
  | zero =>
    have he : z = 0 := by simpa [residues] using hz
    exact ⟨[], rfl, by simp [BinaryDigits], by simp [he]⟩
  | succ k ih =>
    simp only [residues, Finset.mem_union, Finset.mem_image] at hz
    rcases hz with ⟨a, ha, rfl⟩ | ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    · obtain ⟨bs, hl, hb, he⟩ := ih ha
      exact ⟨0 :: bs, by simp [hl], by simpa [BinaryDigits] using hb,
        by simp [Nat.ofDigits_cons, he]⟩
    · obtain ⟨bs, hl, hb, he⟩ := ih ha
      exact ⟨1 :: bs, by simp [hl], by simpa [BinaryDigits] using hb,
        by simp [Nat.ofDigits_cons, he, add_comm]⟩

/-- A length-`k` word of zeros and ones, interpreted in base ten, can realize
any residue modulo `m` coprime to five, once `k+1 ≥ m`. Leading zeros are allowed. -/
theorem binary_coverage (m : ℕ) (hm : 0 < m) (h5 : ¬5 ∣ m) (k t : ℕ) (hk : m ≤ k+1) :
    ∃ bs : List ℕ, bs.length = k ∧ BinaryDigits bs ∧ Nat.ofDigits 10 bs ≡ t [MOD m] := by
  induction m using Nat.strong_induction_on generalizing k t with
  | h m ih =>
    by_cases heven : 2 ∣ m
    · obtain ⟨j, hj⟩ := heven
      have hjpos : 0 < j := by omega
      have hjlt : j < m := by omega
      have hj5 : ¬5 ∣ j := fun h => h5 (hj ▸ dvd_mul_of_dvd_right h 2)
      cases k with
      | zero => omega
      | succ k =>
        haveI : NeZero j := ⟨by omega⟩
        let u : ZMod j := ((5 : ZMod j)⁻¹ * ((t/2 : ℕ) : ZMod j))
        obtain ⟨bs, hl, hb, he⟩ := ih j hjlt hjpos hj5 k u.val (by omega)
        have hc := (ZMod.natCast_eq_natCast_iff _ _ _).2 he
        rw [ZMod.natCast_zmod_val] at hc
        have hcop : Nat.Coprime 5 j := (Nat.prime_five.coprime_iff_not_dvd).2 hj5
        have hmul : 5 * Nat.ofDigits 10 bs ≡ t/2 [MOD j] := by
          apply (ZMod.natCast_eq_natCast_iff _ _ _).1
          rw [Nat.cast_mul, hc]
          change (5 : ZMod j) * (5⁻¹ * _) = _
          rw [← mul_assoc, show (5 : ZMod j) * 5⁻¹ = 1 from ZMod.coe_mul_inv_eq_one 5 hcop, one_mul]
        refine ⟨t%2 :: bs, by simp [hl], ?_, ?_⟩
        · intro d hd
          rcases List.mem_cons.mp hd with rfl | hd
          · omega
          · exact hb d hd
        · have hm' := (hmul.mul_left' 2).add_left (t%2)
          rw [← hj, Nat.mod_add_div _ _] at hm'
          simpa [Nat.ofDigits_cons, ← Nat.mul_assoc] using hm'
    · haveI : NeZero m := ⟨by omega⟩
      have hcop : Nat.Coprime 10 m := Nat.coprime_mul_iff_left.mpr
        ⟨Nat.prime_two.coprime_iff_not_dvd.mpr heven, Nat.prime_five.coprime_iff_not_dvd.mpr h5⟩
      have hb := residues_card m hcop k
      rw [min_eq_right hk] at hb
      have hu : residues m k = Finset.univ := Finset.eq_univ_of_card _
        (le_antisymm (Finset.card_le_univ _) (by simpa [ZMod.card] using hb))
      obtain ⟨bs, hl, hbin, hz⟩ := residues_witness (z := (t : ZMod m)) (by rw [hu]; simp)
      exact ⟨bs, hl, hbin, (ZMod.natCast_eq_natCast_iff _ _ _).1 hz⟩

/-- Divisibility by five is exactly the obstruction to representing every residue
by an arbitrary-length word at or above the uniform bound. -/
theorem binary_coverage_iff (m k : ℕ) (hm : 0 < m) (hk : m ≤ k+1) :
    (∀ t : ℕ, ∃ bs : List ℕ, bs.length = k ∧ BinaryDigits bs ∧
      Nat.ofDigits 10 bs ≡ t [MOD m]) ↔ ¬5 ∣ m := by
  constructor
  · intro hall h5
    obtain ⟨bs, _, hb, hr⟩ := hall 2
    have h := hr.of_dvd h5
    cases bs with
    | nil => exact (by decide : ¬(0 ≡ 2 [MOD 5])) h
    | cons d ds =>
      have hd := hb d List.mem_cons_self
      rw [Nat.ofDigits_cons] at h
      unfold Nat.ModEq at h
      omega
  · exact fun h t => binary_coverage m hm h k t hk

/-- At modulus nine, seven binary-valued positions cannot realize eight.
Thus the uniform sufficient length `m-1` cannot everywhere be replaced by `m-2`. -/
theorem modulus_nine_sharp : ¬∃ bs : List ℕ, bs.length = 7 ∧ BinaryDigits bs ∧
    Nat.ofDigits 10 bs ≡ 8 [MOD 9] := by
  rintro ⟨bs, hl, hb, hr⟩
  have hsum (ds : List ℕ) (hd : BinaryDigits ds) : ds.sum ≤ ds.length := by
    induction ds with
    | nil => decide
    | cons d ds ih =>
      have hhead := hd d List.mem_cons_self
      have htail := ih (fun e he => hd e (List.mem_cons_of_mem d he))
      simp only [List.sum_cons, List.length_cons]
      omega
  have hcast (ds : List ℕ) : Nat.ofDigits 10 ds ≡ ds.sum [MOD 9] := by
    induction ds with
    | nil => rfl
    | cons d ds ih =>
      simpa [Nat.ofDigits_cons] using (((by decide : 10 ≡ 1 [MOD 9]).mul ih).add_left d)
  have he := (hcast bs).symm.trans hr
  have hle := hsum bs hb
  unfold Nat.ModEq at he
  omega

private def low (j : ℕ) : ℕ := if Nat.Prime j then 2 else 8

private theorem low_spec (j b : ℕ) (hb : b = 0 ∨ b = 1) :
    (0 < low j+b ∧ low j+b < 10) ∧
    (if Nat.Prime j then Nat.Prime (low j+b) else 1 < low j+b ∧ ¬Nat.Prime (low j+b)) := by
  by_cases h : Nat.Prime j <;> rcases hb with rfl | rfl <;> simp [low, h] <;> decide

/-- Add the correct baseline to each free position, and give the leading position its `1`. -/
private def decorate : List ℕ → List ℕ
  | [] => [1]
  | b :: bs => (low (bs.length+2) + b) :: decorate bs

private def offset : ℕ → ℕ
  | 0 => 1
  | k+1 => low (k+2) + 10*offset k

private theorem decorate_length (bs : List ℕ) : (decorate bs).length = bs.length+1 := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simpa only [decorate, List.length_cons] using congrArg (·+1) ih

private theorem decorate_value (bs : List ℕ) :
    Nat.ofDigits 10 (decorate bs) = offset bs.length + Nat.ofDigits 10 bs := by
  induction bs with
  | nil => decide
  | cons b bs ih => simp only [decorate, List.length_cons, offset, Nat.ofDigits_cons, ih]; omega

private theorem pattern_cons (d : ℕ) {ds : List ℕ} (hds : ds ≠ []) :
    pattern (d :: ds) ↔
      (if Nat.Prime (ds.length+1) then Nat.Prime d else 1 < d ∧ ¬Nat.Prime d) ∧ pattern ds := by
  cases ds with
  | nil => contradiction
  | cons e ds => rfl

private theorem decorate_spec (bs : List ℕ) (hb : BinaryDigits bs) :
    (∀ d ∈ decorate bs, 0 < d ∧ d < 10) ∧ pattern (decorate bs) := by
  induction bs with
  | nil => simp [decorate, pattern]
  | cons b bs ih =>
    have ht : BinaryDigits bs := fun d hd => hb d (List.mem_cons_of_mem b hd)
    obtain ⟨hr, hp⟩ := ih ht
    have hs := low_spec (bs.length+2) b (hb b List.mem_cons_self)
    refine ⟨?_, ?_⟩
    · intro d hd
      rcases List.mem_cons.mp hd with rfl | hd
      · exact hs.1
      · exact hr d hd
    · rw [decorate, pattern_cons _ (by
          intro he
          have hl := decorate_length bs
          rw [he] at hl
          simp at hl), decorate_length]
      exact ⟨hs.2, hp⟩

private theorem exists_of_not_five_dvd (n : ℕ) (hn : 0 < n) (h5 : ¬5 ∣ n) :
    ∃ x, admissible n x := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  haveI : NeZero (k+1) := ⟨by omega⟩
  let t : ZMod (k+1) := -(offset k : ℕ)
  obtain ⟨bs, hl, hb, hmod⟩ := binary_coverage (k+1) (by omega) h5 k t.val (by omega)
  have hcast := (ZMod.natCast_eq_natCast_iff _ _ _).2 hmod
  rw [ZMod.natCast_zmod_val] at hcast
  obtain ⟨hlim, hp⟩ := decorate_spec bs hb
  have hd : Nat.digits 10 (Nat.ofDigits 10 (decorate bs)) = decorate bs :=
    Nat.digits_ofDigits 10 (by decide) (decorate bs) (fun d hd => (hlim d hd).2)
      (fun h => (hlim _ (List.getLast_mem h)).1.ne')
  refine ⟨Nat.ofDigits 10 (decorate bs), ?_, by rw [hd, decorate_length, hl], by rwa [hd]⟩
  apply (ZMod.natCast_eq_zero_iff _ _).1
  rw [decorate_value, hl, Nat.cast_add, hcast]
  exact add_neg_cancel _

private theorem five_dvd_forces_five (n x : ℕ) (hn : 0 < n) (h5 : 5 ∣ n) (hx : admissible n x) : n = 5 := by
  obtain ⟨hdvd, hlen, hpat⟩ := hx
  have hxn : 5 ∣ x := dvd_trans h5 hdvd
  have hle : 5 ≤ n := Nat.le_of_dvd hn h5
  have hrepr := Nat.ofDigits_digits 10 x
  cases he : Nat.digits 10 x with
  | nil => rw [he] at hlen; simp at hlen; omega
  | cons d ds =>
    have hbound := Nat.digits_lt_base (b := 10) (m := x) (d := d) (by decide)
      (by rw [he]; exact List.mem_cons_self)
    rw [he, Nat.ofDigits_cons] at hrepr
    rw [he, List.length_cons] at hlen
    have hne : ds ≠ [] := by intro h; rw [h] at hlen; simp at hlen; omega
    rw [he, pattern_cons _ hne, hlen] at hpat
    by_contra hneq
    have hcomp : ¬Nat.Prime n := by
      intro hp
      have := hp.eq_one_or_self_of_dvd 5 h5
      omega
    rw [if_neg hcomp] at hpat
    have hd5 : d = 5 := by obtain ⟨a, ha⟩ := hxn; obtain ⟨⟨hlo, _⟩, _⟩ := hpat; omega
    exact hpat.1.2 (hd5 ▸ Nat.prime_five)

/-- The positive indices admitting an allowed decimal multiple are exactly the
indices not divisible by five together with the exceptional index `5`. -/
theorem murthy_classification (n : ℕ) (hn : 0 < n) :
    (∃ x, admissible n x) ↔ ¬5 ∣ n ∨ n = 5 := by
  constructor
  · rintro ⟨x, hx⟩
    by_cases h : 5 ∣ n
    · exact Or.inr (five_dvd_forces_five n x hn h hx)
    · exact Or.inl h
  · rintro (h | rfl)
    · exact exists_of_not_five_dvd n hn h
    · refine ⟨12245, ?_⟩
      unfold admissible
      rw [show Nat.digits 10 12245 = [5, 4, 2, 2, 1] by decide]
      simp only [pattern, List.length_cons, List.length_nil]
      decide

/-- The OEIS convention selects the least qualifying number, and assigns zero
at every index for which there is no qualifying number. -/
noncomputable def term (n : ℕ) : ℕ := by
  classical
  exact if h : ∃ x, admissible n x then Nat.find h else 0

theorem term_eq_zero_iff (n : ℕ) (hn : 0 < n) : term n = 0 ↔ 5 ∣ n ∧ n ≠ 5 := by
  classical
  have he : term n = 0 ↔ ¬∃ x, admissible n x := by
    by_cases hw : ∃ x, admissible n x
    · simp only [term, hw, dif_pos, not_true_eq_false, iff_false]
      intro hzero
      have hx := (Nat.find_spec hw).2.1
      rw [hzero] at hx
      simp at hx
      omega
    · simp [term, hw]
  rw [he, murthy_classification n hn]
  tauto

#print axioms binary_coverage_iff
#print axioms modulus_nine_sharp
#print axioms murthy_classification
#print axioms term_eq_zero_iff

end RestrictedMultiple

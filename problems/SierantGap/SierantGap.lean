import Mathlib.GroupTheory.Index
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases




open Finset
open scoped BigOperators

namespace SierantGap

private theorem ker_twice {X : Type*} [AddGroup X] [Fintype X] (l : X →+ ZMod 2) :
    Nat.card X ≤ Nat.card l.ker * 2 := by
  rw [← l.ker.card_mul_index, AddSubgroup.index_ker]
  apply Nat.mul_le_mul_left
  classical
  have := Fintype.card_subtype_le (fun v : ZMod 2 => v ∈ l.range)
  rw [← Nat.card_eq_fintype_card, ZMod.card] at this
  exact this

/-- For any zero-system already imposed in the column, further binary
linear tests are simultaneously zero with probability at least the product
of the independent unbiased-bit probabilities. The weighted version below
allows different nonnegative two-point factors in each row. -/
theorem linear_bit_product {ι : Type*} (s : Finset ι) (a d : ι → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hd : ∀ i, 0 ≤ d i) :
    ∀ {X : Type} [AddGroup X] [Fintype X] (l : ι → X →+ ZMod 2),
    (Fintype.card X : ℝ) * (∏ i ∈ s, (a i + d i / 2)) ≤
      ∑ x : X, ∏ i ∈ s, (a i + if l i x = 0 then d i else 0) := by
  classical
  induction s using Finset.induction_on with
  | empty => intros; simp
  | @insert i s hi ih =>
    intro X _ _ l
    let K := (l i).ker
    let target := ∏ j ∈ s, (a j + d j / 2)
    let F := fun x : X => ∏ j ∈ s, (a j + if l j x = 0 then d j else 0)
    have hF : (Fintype.card X : ℝ) * target ≤ ∑ x : X, F x := ih l
    have hK : (Fintype.card K : ℝ) * target ≤ ∑ x : K, F x :=
      ih (fun j => (l j).comp K.subtype)
    have hcard : (Fintype.card X : ℝ) ≤ (Fintype.card K : ℝ) * 2 := by
      exact_mod_cast (by simpa only [Nat.card_eq_fintype_card] using ker_twice (l i) :
        Fintype.card X ≤ Fintype.card K * 2)
    have hnon : 0 ≤ target := Finset.prod_nonneg (fun j _ => add_nonneg (ha j) (div_nonneg (hd j) (by norm_num)))
    have hsplit : (∑ x : X, if l i x = 0 then F x else 0) = ∑ x : K, F x := by
      rw [← Finset.sum_filter]
      exact Finset.sum_subtype _ (by intro x; simp [K]) F
    have hsum : (∑ x : X, (a i + if l i x = 0 then d i else 0) * F x) =
        a i * (∑ x : X, F x) + d i * (∑ x : K, F x) := by
      rw [← hsplit, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro x _
      by_cases hx : l i x = 0 <;> simp [hx, add_mul]
    simp only [Finset.prod_insert hi]
    change (Fintype.card X : ℝ) * ((a i + d i / 2) * target) ≤
      ∑ x : X, (a i + if l i x = 0 then d i else 0) * F x
    rw [hsum]
    have ht := mul_le_mul_of_nonneg_right hcard hnon
    have hKt : (Fintype.card X : ℝ) * target / 2 ≤ ∑ x : K, F x := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hF (ha i), mul_le_mul_of_nonneg_left hKt (hd i)]


/-- Number of possible higher-bit labels when the low output bit is fixed. -/
def halfBound (r : ℕ) (b : ZMod 2) : ℕ := (r + if b = 0 then 1 else 0) / 2

/-- A bit-column consists of a uniformly free element of `X`. Each row reads
one binary linear form of the column. A row is accepted when the ordinary
unsigned integer formed by its `n` bits belongs to the initial interval `[0,r)`. -/
noncomputable def boxCount {ι X : Type} [Fintype ι] [AddGroup X] [Fintype X]
    (l : ι → X →+ ZMod 2) : ℕ → (ι → ℕ) → ℕ
  | 0, r => if ∀ i, 0 < r i then 1 else 0
  | n+1, r => ∑ x : X, boxCount l n (fun i => halfBound (r i) (l i x))

private theorem half_zero (b : ZMod 2) : halfBound 0 b = 0 := by
  by_cases h : b = 0 <;> simp [halfBound, h]

private theorem boxCount_zero {ι X : Type} [Fintype ι] [AddGroup X] [Fintype X]
    (l : ι → X →+ ZMod 2) (n : ℕ) (r : ι → ℕ) (j : ι) (h : r j = 0) :
    boxCount l n r = 0 := by
  induction n generalizing r with
  | zero => simp [boxCount, show ¬(∀ i, 0 < r i) by intro h'; simpa [h] using h' j]
  | succ n ih =>
    apply Finset.sum_eq_zero
    intro x _; apply ih; simp [h, half_zero]

/-- Columns allowed in the least significant bit by the dyadic rectangle. -/
def lowColumn {ι X : Type} [AddGroup X] (l : ι → X →+ ZMod 2) (k : ι → ℕ) :
    AddSubgroup X where
  carrier := {x | ∀ i, k i = 0 → l i x = 0}
  zero_mem' := by simp
  add_mem' := by intro x y hx hy i hi; simp [map_add, hx i hi, hy i hi]
  neg_mem' := by intro x hx i hi; simp [hx i hi]

private theorem half_pow (k : ℕ) (b : ZMod 2) (hb : k = 0 → b = 0) :
    halfBound (2^k) b = 2^(k-1) := by
  cases k with
  | zero => simp [halfBound, hb rfl]
  | succ k =>
    simp only [Nat.succ_sub_one, pow_succ, halfBound]
    by_cases h : b = 0 <;> simp only [h, if_true, if_false] <;> omega

private theorem half_le_half_pow (k r : ℕ) (b : ZMod 2) (hr : r ≤ 2^k) :
    halfBound r b ≤ 2^(k-1) := by
  cases k with
  | zero => simp only [pow_zero] at hr; by_cases h : b = 0 <;> simp [halfBound, h] <;> omega
  | succ k =>
    simp only [Nat.succ_sub_one, pow_succ] at *
    by_cases h : b = 0 <;> simp [halfBound, h] <;> omega

private theorem dyadic_count_succ {ι X : Type} [Fintype ι] [AddGroup X] [Fintype X]
    (l : ι → X →+ ZMod 2) (n : ℕ) (k : ι → ℕ) :
    boxCount l (n+1) (fun i => 2^(k i)) =
    Nat.card (lowColumn l k) * boxCount l n (fun i => 2^(k i-1)) := by
  classical
  rw [Nat.card_eq_fintype_card]
  let H := lowColumn l k
  let C := boxCount l n (fun i => 2^(k i-1))
  change (∑ x : X, boxCount l n (fun i => halfBound (2^(k i)) (l i x))) = Fintype.card H * C
  calc
    _ = ∑ x : X, (if x ∈ H then C else 0) := by
      apply Finset.sum_congr rfl; intro x _
      by_cases hx : x ∈ H
      · rw [if_pos hx]; have hh : ∀ i, k i = 0 → l i x = 0 := hx
        congr 1; funext i; exact half_pow (k i) (l i x) (hh i)
      · rw [if_neg hx]; change ¬(∀ i, k i = 0 → l i x = 0) at hx
        push_neg at hx; obtain ⟨j, hj, hb⟩ := hx
        apply boxCount_zero l n _ j; simp [hj, halfBound, hb]
    _ = _ := by
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      congr 1
      exact (Fintype.card_subtype (fun x : X => x ∈ H)).symm

private noncomputable def lowValue (k r : ℕ) : ℝ :=
  if k = 0 then r else (r/2 : ℕ) / (2:ℝ)^(k-1)

private noncomputable def bitGain (k r : ℕ) : ℝ :=
  if k = 0 then 0 else (r%2 : ℕ) / (2:ℝ)^(k-1)

private theorem half_ratio (k r : ℕ) (b : ZMod 2) (hb : k=0 → b=0) (hr : r ≤ 2^k) :
    (halfBound r b : ℝ) / (2:ℝ)^(k-1) = lowValue k r + if b=0 then bitGain k r else 0 := by
  cases k with
  | zero =>
    have hh : (r+1)/2 = r := by simp at hr; omega
    simp [halfBound, hb rfl, lowValue, bitGain, hh]
  | succ k =>
    have hh : (r+1)/2 = r/2 + r%2 := by omega
    by_cases h : b=0 <;> simp [halfBound, lowValue, bitGain, h, hh, add_div]

private theorem mean_half_ratio (k r : ℕ) :
    lowValue k r + bitGain k r / 2 = (r : ℝ) / (2:ℝ)^k := by
  cases k with
  | zero => simp [lowValue, bitGain]
  | succ k =>
    have heq : (r:ℝ) = 2 * (r/2 : ℕ) + (r%2 : ℕ) := by exact_mod_cast (show r = 2*(r/2) + r%2 by omega)
    simp only [lowValue, bitGain, Nat.succ_ne_zero, if_false, Nat.succ_sub_one, pow_succ]
    field_simp
    linarith


/-- Dyadic rectangle approximation for the actual unrestricted count of a
binary linear configuration. The unrounded widths are bounded above by the
chosen dyadic widths; a subsequent monotonicity step handles every rounding. -/
theorem dyadic_rectangle {ι X : Type} [Fintype ι] [AddGroup X] [Fintype X]
    (l : ι → X →+ ZMod 2) (n : ℕ) (k r : ι → ℕ)
    (hk : ∀ i, k i ≤ n) (hr : ∀ i, r i ≤ 2^(k i)) :
    (boxCount l n (fun i => 2^(k i)) : ℝ) *
      (∏ i, ((r i : ℝ) / (2:ℝ)^(k i))) ≤ boxCount l n r := by
  classical
  induction n generalizing k r with
  | zero =>
    have hzero : ∀ i, k i = 0 := fun i => Nat.eq_zero_of_le_zero (hk i)
    by_cases hpos : ∀ i, 0 < r i
    · have hone : ∀ i, r i = 1 := by intro i; have := hr i; rw [hzero i, pow_zero] at this; have := hpos i; omega
      simp [hzero, hone, boxCount]
    · push_neg at hpos; obtain ⟨j, hj⟩ := hpos
      have hj' : r j = 0 := Nat.eq_zero_of_le_zero hj
      have hz : (∏ i, ((r i : ℝ) / (2:ℝ)^(k i))) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hj'])
      rw [hz, mul_zero]; positivity
  | succ n ih =>
    let H := lowColumn l k
    let kp := fun i => k i - 1
    let C : ℝ := boxCount l n (fun i => 2^(kp i))
    let q := fun (x : X) (i : ι) => halfBound (r i) (l i x)
    have hC : 0 ≤ C := by dsimp [C]; positivity
    have hk' : ∀ i, kp i ≤ n := by intro i; have := hk i; dsimp [kp]; omega
    have rowBound (x : H) : C * (∏ i, ((q x i : ℝ) / 2^(kp i))) ≤ boxCount l n (q x) :=
      ih kp (q x) hk' (fun i => half_le_half_pow (k i) (r i) (l i x) (hr i))
    have corr := linear_bit_product (Finset.univ : Finset ι)
      (fun i => lowValue (k i) (r i)) (fun i => bitGain (k i) (r i))
      (by intro i; dsimp only [lowValue]; split <;> positivity)
      (by intro i; dsimp only [bitGain]; split <;> positivity)
      (fun j => (l j).comp H.subtype)
    have hc : (Fintype.card H : ℝ) * (∏ i, ((r i : ℝ) / 2^(k i))) ≤
        ∑ x : H, ∏ i, ((q x i : ℝ)/ 2^(kp i)) := by
      simpa only [mean_half_ratio] using (by
        convert corr using 2 with x
        apply Finset.prod_congr rfl; intro i _
        exact half_ratio (k i) (r i) (l i x) (x.property i) (hr i) :
        (Fintype.card H : ℝ) * (∏ i, (lowValue (k i) (r i) + bitGain (k i) (r i)/2)) ≤
          ∑ x : H, ∏ i, ((q x i : ℝ) / 2^(kp i)))
    have sub : (∑ x : H, (boxCount l n (q x) : ℝ)) ≤ ∑ x : X, (boxCount l n (q x) : ℝ) := by
      let f := fun x : X => (boxCount l n (q x) : ℝ)
      have eqsub : (∑ x : H, f x) = ∑ x : X, if x ∈ H then f x else 0 := by
        rw [← Finset.sum_filter]; symm; exact Finset.sum_subtype _ (by intro x; simp) f
      change (∑ x : H, f x) ≤ ∑ x : X, f x
      rw [eqsub]; apply Finset.sum_le_sum; intro x _; split <;> simp [f]
    rw [dyadic_count_succ, Nat.cast_mul, Nat.card_eq_fintype_card]
    change (Fintype.card H : ℝ) * C * _ ≤ ((∑ x : X, boxCount l n (q x) : ℕ) : ℝ)
    rw [Nat.cast_sum]
    calc
      _ = C * ((Fintype.card H : ℝ) * ∏ i, ((r i : ℝ)/2^(k i))) := by ring
      _ ≤ C * (∑ x : H, ∏ i, ((q x i : ℝ)/2^(kp i))) := mul_le_mul_of_nonneg_left hc hC
      _ = ∑ x : H, C * ∏ i, ((q x i : ℝ)/2^(kp i)) := Finset.mul_sum _ _ _
      _ ≤ ∑ x : H, (boxCount l n (q x) : ℝ) := Finset.sum_le_sum (fun x _ => rowBound x)
      _ ≤ _ := sub


/-- Enlarging the integer intervals cannot discard any assignment. -/
theorem boxCount_mono {ι X : Type} [Fintype ι] [AddGroup X] [Fintype X]
    (l : ι → X →+ ZMod 2) (n : ℕ) {r s : ι → ℕ} (hs : ∀ i, r i ≤ s i) :
    boxCount l n r ≤ boxCount l n s := by
  classical
  induction n generalizing r s with
  | zero =>
    by_cases h : ∀ i, 0 < r i
    · simp [boxCount, h, show ∀ i, 0 < s i from fun i => (h i).trans_le (hs i)]
    · simp [boxCount, h]
  | succ n ih =>
    apply Finset.sum_le_sum; intro x _; apply ih; intro i
    exact Nat.div_le_div_right (Nat.add_le_add_right (hs i) _)

/-- Rectangle approximation at an arbitrary vector of dyadic widths. -/
theorem clipped_dyadic_rectangle {ι X : Type} [Fintype ι] [AddGroup X] [Fintype X]
    (l : ι → X →+ ZMod 2) (n : ℕ) (k r : ι → ℕ) (hk : ∀ i, k i ≤ n) :
    (boxCount l n (fun i => 2^(k i)) : ℝ) *
      (∏ i, ((min (r i) (2^(k i)) : ℕ) : ℝ) / (2:ℝ)^(k i)) ≤ boxCount l n r :=
  (dyadic_rectangle l n k (fun i => min (r i) (2^(k i))) hk
    (fun i => min_le_right ..)).trans (by exact_mod_cast
      (boxCount_mono l n (r := fun i => min (r i) (2^(k i))) (s := r) (fun i => min_le_left ..)))

end SierantGap



open Set MeasureTheory
open scoped BigOperators

namespace SierantGap

/-- When a common threshold rounds a coordinate, the loss is paid at a basis
coordinate rounded down or a nonbasis coordinate rounded up. The variable
`u` is the fractional part of its base-two logarithm. -/
noncomputable def roundingCost (inBasis : Prop) [Decidable inBasis] (u t : ℝ) : ℝ :=
  if inBasis then (Ici u).indicator (fun _ => u) t
  else (Iio u).indicator (fun _ => 1 - u) t

private theorem roundingCost_integrable (inBasis : Prop) [Decidable inBasis] (u : ℝ) :
    IntegrableOn (roundingCost inBasis u) (Icc (0:ℝ) 1) := by
  unfold roundingCost
  by_cases h : inBasis
  · simpa only [if_pos h] using
      (integrableOn_const (C := u) (s := Icc (0:ℝ) 1) (μ := volume) (by simp [Real.volume_Icc])).indicator (measurableSet_Ici (a := u))
  · simpa only [if_neg h] using
      (integrableOn_const (C := 1-u) (s := Icc (0:ℝ) 1) (μ := volume) (by simp [Real.volume_Icc])).indicator (measurableSet_Iio (a := u))

private theorem mean_roundingCost (inBasis : Prop) [Decidable inBasis] (u : ℝ)
    (hu : u ∈ Icc (0:ℝ) 1) :
    (∫ t in Icc (0:ℝ) 1, roundingCost inBasis u t) = u * (1 - u) := by
  obtain ⟨h0, h1⟩ := hu
  by_cases h : inBasis
  · simp only [roundingCost, if_pos h]
    rw [setIntegral_indicator measurableSet_Ici]
    have hs : Icc (0:ℝ) 1 ∩ Ici u = Icc u 1 := by
      ext t
      exact ⟨fun z => ⟨z.2, z.1.2⟩, fun z => ⟨⟨h0.trans z.1, z.2⟩, z.1⟩⟩
    rw [hs, setIntegral_const, Real.volume_real_Icc_of_le h1, smul_eq_mul, mul_comm]
  · simp only [roundingCost, if_neg h]
    rw [setIntegral_indicator measurableSet_Iio]
    have hs : Icc (0:ℝ) 1 ∩ Iio u = Ico 0 u := by
      ext t
      exact ⟨fun z => ⟨z.1.1, z.2⟩, fun z => ⟨⟨z.1, z.2.le.trans h1⟩, z.2⟩⟩
    rw [hs, setIntegral_const, Real.volume_real_Ico_of_le h0, smul_eq_mul, sub_zero]

/-- Any common lower bound on all eight threshold-rounding losses is at most
2, the sum of eight variances of Bernoulli random variables. -/
theorem eight_coordinate_rounding (basis : Finset (Fin 8)) (u : Fin 8 → ℝ)
    (hu : ∀ i, u i ∈ Icc (0:ℝ) 1) (D : ℝ)
    (bound : ∀ t ∈ Icc (0:ℝ) 1, D ≤ ∑ i, roundingCost (i ∈ basis) (u i) t) :
    D ≤ 2 := by
  classical
  let f := fun i : Fin 8 => roundingCost (i ∈ basis) (u i)
  have hint : ∀ i, IntegrableOn (f i) (Icc (0:ℝ) 1) :=
    fun i => roundingCost_integrable (i ∈ basis) (u i)
  have h := setIntegral_mono_on (μ := volume) (integrableOn_const (C := D) (by simp [Real.volume_Icc]))
    (integrable_finset_sum _ (fun i _ => hint i)) measurableSet_Icc bound
  rw [setIntegral_const, Real.volume_real_Icc_of_le (by norm_num : (0:ℝ) ≤ 1), smul_eq_mul] at h
  have hh : (∫ t in Icc (0:ℝ) 1, ∑ i, f i t) = ∑ i, (∫ t in Icc (0:ℝ) 1, f i t) :=
    integral_finset_sum _ (fun i _ => hint i)
  change (1 - 0) * D ≤ ∫ t in Icc (0:ℝ) 1, ∑ i, f i t at h
  rw [hh] at h
  have hm : ∀ i, (∫ t in Icc (0:ℝ) 1, f i t) ≤ 1 / 4 := by
    intro i
    rw [show (∫ t in Icc (0:ℝ) 1, f i t) = u i * (1-u i) from
      mean_roundingCost (i ∈ basis) (u i) (hu i)]
    nlinarith [sq_nonneg (u i - 1/2)]
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hm i)
  norm_num at hs h ⊢
  linarith

end SierantGap



open Set Finset
open scoped BigOperators
namespace SierantGap

/-- Fractional part and common-threshold rounding of nonnegative logarithmic widths. -/
noncomputable def frac (w : ℝ) : ℝ := w - ⌊w⌋₊
noncomputable def roundLog (t w : ℝ) : ℕ := ⌊w⌋₊ + if t < frac w then 1 else 0

private theorem frac_mem (w : ℝ) (hw : 0 ≤ w) : frac w ∈ Icc (0:ℝ) 1 :=
  ⟨sub_nonneg.mpr (Nat.floor_le hw), (sub_lt_iff_lt_add'.mpr (Nat.lt_floor_add_one w)).le⟩

private theorem roundLog_mono (t : ℝ) : Monotone (roundLog t) := by
  intro x y h
  have hF := Nat.floor_mono h
  rcases hF.lt_or_eq with hf | hf
  · unfold roundLog; split <;> split <;> omega
  · have hfrac : frac x ≤ frac y := by simpa only [frac, hf] using sub_le_sub_right h (⌊y⌋₊ : ℝ)
    unfold roundLog; rw [hf]; split <;> split <;> try omega
    exfalso; exact (by assumption : ¬t < frac y) ((by assumption : t < frac x).trans_le hfrac)

private theorem roundLog_le {w t : ℝ} {n : ℕ} (ht : 0 ≤ t) (hw : w ≤ (n : ℝ)) :
    roundLog t w ≤ n := by
  have hf := Nat.floor_le_of_le hw
  unfold roundLog; split <;> rename_i h
  · by_contra hh; have he : ⌊w⌋₊ = n := by omega
    unfold frac at h; rw [he] at h; linarith
  · omega

private theorem row_loss (b : Prop) [Decidable b] (w t : ℝ) (hw : 0 ≤ w) :
    (if b then w else 0) - ((if b then (roundLog t w : ℝ) else 0) +
      min w (roundLog t w : ℝ) - (roundLog t w : ℝ)) = roundingCost b (frac w) t := by
  have hf := Nat.floor_le hw
  have hg := Nat.lt_floor_add_one w
  by_cases hup : t < frac w
  · have hh : w ≤ (roundLog t w : ℝ) := by simpa [roundLog, hup] using hg.le
    rw [min_eq_left hh]
    by_cases hb : b <;> simp only [roundingCost, hb, if_true, if_false, Set.indicator_apply, Set.mem_Ici, Set.mem_Iio, roundLog, hup, not_le.mpr hup, Nat.cast_add, Nat.cast_one]
    all_goals try (unfold frac)
    all_goals ring
  · have hh : (roundLog t w : ℝ) ≤ w := by simpa [roundLog, hup] using hf
    rw [min_eq_right hh]
    by_cases hb : b <;> simp only [roundingCost, hb, if_true, if_false, Set.indicator_apply, Set.mem_Ici, Set.mem_Iio, roundLog, hup, le_of_not_gt hup, Nat.add_zero]
    all_goals try (unfold frac)
    all_goals ring

private theorem pow_sum_real {ι : Type*} (s : Finset ι) (u : ι → ℝ) :
    (2:ℝ) ^ (∑ i ∈ s, u i) = ∏ i ∈ s, (2:ℝ) ^ u i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => simp [Finset.sum_insert hi, Finset.prod_insert hi, Real.rpow_add (by norm_num : (0:ℝ)<2), ih]

private theorem clipped_exponent {r k : ℕ} {w : ℝ} (hr : (2:ℝ)^w = r) :
    (2:ℝ) ^ (min w (k:ℝ) - (k:ℝ)) = ((min r (2^k) : ℕ) : ℝ) / (2:ℝ)^k := by
  rw [Real.rpow_sub (by norm_num), Real.rpow_natCast]
  have hm : Monotone (fun w : ℝ => (2:ℝ)^w) := fun _ _ h => Real.rpow_le_rpow_of_exponent_le (by norm_num) h
  rw [show (2:ℝ)^(min w (k:ℝ)) = min ((2:ℝ)^w) ((2:ℝ)^(k:ℝ)) from hm.map_min]
  rw [hr, Real.rpow_natCast, Nat.cast_min, Nat.cast_pow, Nat.cast_ofNat]

/-- A minimum-weight basis chosen by a fixed ordering remains a basis at all
monotone dyadic roundings of that ordering. This definition spells out the
exact counting identity that the flag basis supplies. -/
def FlagCounts {X : Type} [AddGroup X] [Fintype X] (l : Fin 8 → X →+ ZMod 2)
    (n : ℕ) (r : Fin 8 → ℕ) (B : Finset (Fin 8)) : Prop :=
  ∀ k : Fin 8 → ℕ, (∀ i, k i ≤ n) → (∀ i j, r i ≤ r j → k i ≤ k j) →
    boxCount l n (fun i => 2^(k i)) = ∏ i ∈ B, 2^(k i)

private theorem boxCount_pos {ι X : Type} [Fintype ι] [AddGroup X] [Fintype X]
    (l : ι → X →+ ZMod 2) (n : ℕ) (r : ι → ℕ) (hr : ∀ i, 0 < r i) :
    0 < boxCount l n r := by
  classical
  induction n generalizing r with
  | zero => simp [boxCount, hr]
  | succ n ih =>
    apply lt_of_lt_of_le (b := boxCount l n (fun i => halfBound (r i) (l i 0)))
    · apply ih; intro i; simp [halfBound]; have := hr i; omega
    · change _ ≤ ∑ x : X, boxCount l n (fun i => halfBound (r i) (l i x))
      exact Finset.single_le_sum (f := fun x : X => boxCount l n (fun i => halfBound (r i) (l i x))) (fun _ _ => Nat.zero_le _) (Finset.mem_univ (0:X))


/-- For eight rows the product bound of a dyadically optimal flag basis
is at most four times the exact count at the original, unrestricted widths. -/
theorem flag_product_le_four_count {X : Type} [AddGroup X] [Fintype X]
    (l : Fin 8 → X →+ ZMod 2) (n : ℕ) (r : Fin 8 → ℕ) (B : Finset (Fin 8))
    (hr : ∀ i, 0 < r i) (hcap : ∀ i, r i ≤ 2^n) (hb : FlagCounts l n r B) :
    (∏ i ∈ B, r i) ≤ 4 * boxCount l n r := by
  classical
  let C : ℝ := boxCount l n r
  let w := fun i => Real.logb 2 (r i : ℝ)
  let W := ∑ i ∈ B, w i
  have Cpos : 0 < C := by dsimp [C]; exact_mod_cast boxCount_pos l n r hr
  have rpos (i) : 0 < (r i : ℝ) := by exact_mod_cast hr i
  have wnon (i) : 0 ≤ w i := Real.logb_nonneg (by norm_num) (by exact_mod_cast hr i)
  have wto (i) : (2:ℝ)^(w i) = r i := Real.rpow_logb (by norm_num) (by norm_num) (rpos i)
  have wcap (i) : w i ≤ (n:ℝ) := by
    apply (Real.logb_le_iff_le_rpow (by norm_num : (1:ℝ)<2) (rpos i)).mpr
    rw [Real.rpow_natCast]; exact_mod_cast hcap i
  have main : W - Real.logb 2 C ≤ 2 := by
    apply eight_coordinate_rounding B (fun i => frac (w i)) (fun i => frac_mem _ (wnon i))
    intro t ht
    let k := fun i => roundLog t (w i)
    have hk (i) : k i ≤ n := roundLog_le ht.1 (wcap i)
    have hm (i j : Fin 8) (hij : r i ≤ r j) : k i ≤ k j :=
      roundLog_mono t (Real.logb_le_logb_of_le (by norm_num) (rpos i) (by exact_mod_cast hij))
    have hcount := clipped_dyadic_rectangle l n k r hk
    rw [hb k hk hm, Nat.cast_prod] at hcount
    let Q := ∑ i ∈ B, (k i : ℝ)
    let U := ∑ i, (min (w i) (k i : ℝ) - (k i : ℝ))
    have hpower : (2:ℝ) ^ (Q + U) ≤ C := by
      rw [Real.rpow_add (by norm_num), show (2:ℝ)^Q = ∏ i ∈ B, (2:ℝ)^(k i) by
            simpa only [Q, Real.rpow_natCast] using pow_sum_real B (fun i => (k i : ℝ)),
          show (2:ℝ)^U = ∏ i, ((min (r i) (2^(k i)) : ℕ) : ℝ)/(2:ℝ)^(k i) by
            dsimp [U]; rw [pow_sum_real]; apply Finset.prod_congr rfl; intro i _; exact clipped_exponent (wto i)]
      exact_mod_cast hcount
    have hlog : Q+U ≤ Real.logb 2 C := (Real.le_logb_iff_rpow_le (by norm_num) Cpos).mpr hpower
    have hpoint := fun i => row_loss (i ∈ B) (w i) t (wnon i)
    have hsum := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl (fun i _ => hpoint i)
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.univ_inter] at hsum
    dsimp only [W, Q, U, k] at *
    rw [Finset.sum_sub_distrib] at hlog
    linarith
  have upper : W ≤ Real.logb 2 C + 2 := by linarith
  have e := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) upper
  rw [Real.rpow_add (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) Cpos,
    show (2:ℝ) ^ (2:ℝ) = 4 by norm_num, show (2:ℝ)^W = ∏ i ∈ B, (r i : ℝ) by
      dsimp [W]; rw [pow_sum_real]; apply Finset.prod_congr rfl; intro i _; exact wto i] at e
  dsimp only [C] at e
  exact_mod_cast (by linarith : (∏ i ∈ B, (r i : ℝ)) ≤ 4 * (boxCount l n r : ℝ))

end SierantGap



open Finset Set
open scoped BigOperators
namespace SierantGap

/-- The selected rows give every binary address on a single bit column. -/
def rowEval {X : Type} [AddGroup X] (l : Fin 8 → X →+ ZMod 2)
    (B : Finset (Fin 8)) (x : X) : B → ZMod 2 := fun j => l j x

def RowBasis {X : Type} [AddGroup X] (l : Fin 8 → X →+ ZMod 2)
    (B : Finset (Fin 8)) : Prop := Function.Bijective (rowEval l B)

/-- Zero tests on earlier basis ranks imply the corresponding test on any row. -/
def RankFlag {X : Type} [AddGroup X] (l : Fin 8 → X →+ ZMod 2) (r : Fin 8 → ℕ)
    (B : Finset (Fin 8)) : Prop :=
  ∀ i x, (∀ j ∈ B, r j ≤ r i → l j x = 0) → l i x = 0

private theorem flag_column_card {X : Type} [AddGroup X] [Fintype X]
    (l : Fin 8 → X →+ ZMod 2) (r k : Fin 8 → ℕ) (B : Finset (Fin 8))
    (hb : RowBasis l B) (hf : RankFlag l r B) (hk : ∀ i j, r i ≤ r j → k i ≤ k j) :
    Nat.card (lowColumn l k) = 2^(B.filter (fun i => k i ≠ 0)).card := by
  classical
  let H := lowColumn l k
  let A := B.filter (fun i => k i ≠ 0)
  let T := fun (x : H) (j : A) => l j x
  have hinj : Function.Injective T := by
    intro x y eqxy
    apply Subtype.ext; apply hb.1; funext j
    by_cases h : k j = 0
    · exact (x.property j h).trans (y.property j h).symm
    · exact congrFun eqxy ⟨j, Finset.mem_filter.mpr ⟨j.property, h⟩⟩
  have hsurj : Function.Surjective T := by
    intro z
    let v := fun j : B => if h : k j = 0 then (0:ZMod 2) else z ⟨j, Finset.mem_filter.mpr ⟨j.property, h⟩⟩
    obtain ⟨x, hx⟩ := hb.2 v
    have hmem : x ∈ H := by
      intro i hi; apply hf i x; intro j hj hji
      have hj0 : k j = 0 := Nat.eq_zero_of_le_zero (hi ▸ hk j i hji)
      have hxj := congrFun hx ⟨j,hj⟩
      simpa [rowEval, v, hj0] using hxj
    refine ⟨⟨x, hmem⟩, ?_⟩; funext j
    obtain ⟨hj, h0⟩ := Finset.mem_filter.mp j.property
    simpa [T, v, rowEval, h0] using congrFun hx ⟨j,hj⟩
  have ec := Fintype.card_congr (Equiv.ofBijective T ⟨hinj,hsurj⟩)
  simpa only [Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card, Fintype.card_coe, A, H] using ec

/-- A rank-adapted coordinate basis yields the dyadic factorization at every
width rounding that preserves rank order, including at equal ranks. -/
theorem flag_counts_of_basis {X : Type} [AddGroup X] [Fintype X]
    (l : Fin 8 → X →+ ZMod 2) (n : ℕ) (r : Fin 8 → ℕ) (B : Finset (Fin 8))
    (hb : RowBasis l B) (hf : RankFlag l r B) : FlagCounts l n r B := by
  classical
  intro k hcap hm
  induction n generalizing k with
  | zero =>
    have hk : ∀ i, k i = 0 := fun i => Nat.eq_zero_of_le_zero (hcap i)
    simp [hk, boxCount]
  | succ n ih =>
    rw [dyadic_count_succ, flag_column_card l r k B hb hf hm, ih (fun i => k i - 1)
      (by intro i; change k i - 1 ≤ n; have := hcap i; omega) (fun i j h => Nat.sub_le_sub_right (hm i j h) 1)]
    have ha : 2 ^ (B.filter (fun i => k i ≠ 0)).card =
        ∏ i ∈ B, (if k i ≠ 0 then (2:ℕ) else 1) := by
      rw [← Finset.prod_filter]; simp
    rw [ha, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl; intro i _
    cases h : k i with
    | zero => simp
    | succ u => simp [pow_succ, Nat.mul_comm]


private theorem binary_toggle (a b c : ZMod 2) (h : a ≠ b) (hc : c ≠ 0) : a + c = b := by
  revert a b c; decide

/-- Every separating family of eight binary linear forms has a coordinate
basis adapted to arbitrary integer ranks. A row enters the basis precisely
when its bit can vary while the preceding bits vanish. -/
theorem exists_rank_basis {X : Type} [AddGroup X]
    (l : Fin 8 → X →+ ZMod 2) (r : Fin 8 → ℕ)
    (sep : ∀ x, (∀ i, l i x = 0) → x = 0) :
    ∃ B : Finset (Fin 8), RowBasis l B ∧ RankFlag l r B := by
  classical
  let key := fun i : Fin 8 => 8 * r i + i.val
  have hkey : Function.Injective key := by
    intro i j hij; apply Fin.ext; dsimp [key] at hij; have hi := i.isLt; have hj := j.isLt; omega
  have rank_le (i j : Fin 8) (h : key i ≤ key j) : r i ≤ r j := by
    dsimp [key] at h; have hi := i.isLt; have hj := j.isLt; omega
  let newRow := fun i : Fin 8 => ∃ x : X, (∀ j, key j < key i → l j x = 0) ∧ l i x ≠ 0
  let B := Finset.univ.filter newRow
  have hB (i : Fin 8) : i ∈ B ↔ newRow i := by simp [B]
  have rankflag : RankFlag l r B := by
    intro i x hx
    by_contra hxi
    let S := Finset.univ.filter (fun j => l j x ≠ 0)
    have hi : i ∈ S := by simpa [S] using hxi
    obtain ⟨j, hj, hmin⟩ := Finset.exists_min_image S key ⟨i,hi⟩
    have hjx : l j x ≠ 0 := (Finset.mem_filter.mp hj).2
    have hbefore (a : Fin 8) (ha : key a < key j) : l a x = 0 := by
      by_contra hax
      have ham : a ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hax⟩
      exact ha.not_ge (hmin a ham)
    exact hjx (hx j ((hB j).mpr ⟨x,hbefore,hjx⟩) (rank_le j i (hmin i hi)))
  refine ⟨B, ⟨?_, ?_⟩, rankflag⟩
  · intro x y hxy; apply sub_eq_zero.mp; apply sep; intro i
    apply rankflag i (x-y); intro j hj _
    exact (map_sub (l j) x y).trans (sub_eq_zero.mpr (congrFun hxy ⟨j,hj⟩))
  · intro z
    have matching (m : ℕ) : ∃ x : X, ∀ j : B, key j < m → l j x = z j := by
      induction m with
      | zero => exact ⟨0, fun _ h => False.elim (Nat.not_lt_zero _ h)⟩
      | succ m ih =>
        obtain ⟨x, hx⟩ := ih
        by_cases has : ∃ i : B, key i = m
        · obtain ⟨i, hi⟩ := has
          by_cases he : l i x = z i
          · refine ⟨x, ?_⟩; intro j hj
            rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with h | h
            · exact hx j h
            · have hji : j = i := Subtype.ext (hkey (h.trans hi.symm)); simpa [hji] using he
          · obtain ⟨v, hv, hn⟩ := (hB i).mp i.property
            refine ⟨x+v, ?_⟩; intro j hj
            rw [map_add]
            rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with h | h
            · rw [hv j (hi ▸ h : key j < key i), add_zero]; exact hx j h
            · have hji : j = i := Subtype.ext (hkey (h.trans hi.symm))
              subst j; exact binary_toggle _ _ _ he hn
        · refine ⟨x, ?_⟩; intro j hj
          apply hx j; have hn : key j ≠ m := fun h => has ⟨j,h⟩; omega
    obtain ⟨x, hx⟩ := matching (Finset.univ.sup key + 1)
    exact ⟨x, funext fun j => hx j (Nat.lt_succ_of_le
      (Finset.le_sup (f := key) (Finset.mem_univ (j:Fin 8))))⟩

/-- Main combinatorial estimate, with the rank-adapted basis constructed
inside the proof. All cube dimensions and all positive integer widths occur. -/
theorem exists_basis_product_le_four_count {X : Type} [AddGroup X] [Fintype X]
    (l : Fin 8 → X →+ ZMod 2) (sep : ∀ x, (∀ i, l i x = 0) → x = 0)
    (n : ℕ) (r : Fin 8 → ℕ) (hr : ∀ i, 0 < r i) (hcap : ∀ i, r i ≤ 2^n) :
    ∃ B : Finset (Fin 8), RowBasis l B ∧ (∏ i ∈ B, r i) ≤ 4 * boxCount l n r := by
  obtain ⟨B,hb,hf⟩ := exists_rank_basis l r sep
  exact ⟨B,hb,flag_product_le_four_count l n r B hr hcap (flag_counts_of_basis l n r B hb hf)⟩

end SierantGap



open Finset Set
open scoped BigOperators
namespace SierantGap

/-- Natural label obtained from little-endian output bits of a specified row. -/
def rowLabel {ι X : Type} [AddGroup X] (l : ι → X →+ ZMod 2) :
    (n : ℕ) → (Fin n → X) → ι → ℕ
  | 0, _, _ => 0
  | n+1, v, i => 2 * rowLabel l n (Fin.tail v) i + if l i (v 0) = 0 then 0 else 1

/-- Direct cardinality interpretation of the recursive box count. -/
theorem direct_count {ι X : Type} [Fintype ι] [AddGroup X] [Fintype X]
    (l : ι → X →+ ZMod 2) (n : ℕ) (r : ι → ℕ) :
    boxCount l n r = ∑ v : Fin n → X, if ∀ i, rowLabel l n v i < r i then 1 else 0 := by
  classical
  induction n generalizing r with
  | zero => by_cases hp : ∀ i, 0 < r i <;> simp [boxCount, rowLabel, hp]
  | succ n ih =>
    let f := fun (v : Fin (n+1) → X) => if ∀ i, rowLabel l (n+1) v i < r i then 1 else 0
    change (∑ x : X, boxCount l n (fun i => halfBound (r i) (l i x))) = ∑ v, f v
    rw [← (Fin.consEquiv (fun _ : Fin (n+1) => X)).sum_comp f, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl; intro x _
    rw [ih]; apply Finset.sum_congr rfl; intro tail _
    dsimp [f, Fin.consEquiv, rowLabel]
    congr 1; apply propext; constructor <;> intro h i <;> specialize h i <;>
      by_cases hb : l i x = 0 <;> simp [halfBound, hb] at * <;> omega

/-- Sierant, Appendix A.3, equations (86) and (88), with coordinates in
order `(x,u,v,y)` and binary addition in every row. -/
abbrev FourBits := Fin 4 → ZMod 2

def coordinate (i : Fin 4) : FourBits →+ ZMod 2 where
  toFun x := x i
  map_zero' := rfl
  map_add' _ _ := rfl

def cubeRows : Fin 8 → FourBits →+ ZMod 2 :=
  ![coordinate 0, coordinate 0 + coordinate 1, coordinate 0 + coordinate 2,
    coordinate 0 + coordinate 1 + coordinate 2, coordinate 3, coordinate 3 + coordinate 1,
    coordinate 3 + coordinate 2, coordinate 3 + coordinate 1 + coordinate 2]

private theorem cubeRows_separate (x : FourBits) (h : ∀ i, cubeRows i x = 0) : x = 0 := by
  have h0 : x 0 = 0 := h 0
  have h1 : x 0 + x 1 = 0 := h 1
  have h2 : x 0 + x 2 = 0 := h 2
  have h3 : x 3 = 0 := h 4
  funext j; fin_cases j <;> simp_all

/-- Sierant's dimension-squared-rescaled rank bounds are products on a
coordinate basis of the eight binary rows. This theorem gives the single
factor four for arbitrary integer ranks and constructs the basis it uses. -/
theorem cube_basis_bound (n : ℕ) (r : Fin 8 → ℕ)
    (hr : ∀ i, 0 < r i) (hcap : ∀ i, r i ≤ 2^n) :
    ∃ B : Finset (Fin 8), RowBasis cubeRows B ∧
      (∏ i ∈ B, r i) ≤ 4 * boxCount cubeRows n r :=
  exists_basis_product_le_four_count cubeRows cubeRows_separate n r hr hcap


/-- Indices 0--3 read the `A` ranks, and 4--7 the `B` ranks. -/
def position (i : Fin 8) : Fin 4 := ⟨i.val % 4, Nat.mod_lt _ (by decide)⟩
def firstSide (i : Fin 8) : Bool := decide (i.val < 4)

def crossSupport (pivot : Fin 4) (side : Bool) : Finset (Fin 8) :=
  Finset.univ.filter (fun j => if position j = pivot then firstSide j ≠ side else firstSide j = side)

def dropSupport (omitted both : Fin 4) (pick : Fin 4 → Bool) : Finset (Fin 8) :=
  Finset.univ.filter (fun j => position j ≠ omitted ∧ (position j = both ∨ firstSide j = pick (position j)))

/-- Supports of the eight cross products and the twelve drop-one bounds
when the two coordinatewise minima in a drop-one bound are expanded. -/
def publishedSupports : Finset (Finset (Fin 8)) :=
  Finset.univ.image (fun a : Fin 4 × Bool => crossSupport a.1 a.2) ∪
  (Finset.univ.filter (fun a : Fin 4 × Fin 4 × (Fin 4 → Bool) => a.1 ≠ a.2.1)).image
    (fun a => dropSupport a.1 a.2.1 a.2.2)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
private theorem complete_supports : ∀ B : Finset (Fin 8), B.card = 4 →
    (∀ x : FourBits, (∀ i ∈ B, cubeRows i x = 0) → x = 0) → B ∈ publishedSupports := by decide

theorem rowBasis_mem_supports (B : Finset (Fin 8)) (h : RowBasis cubeRows B) :
    B ∈ publishedSupports := by
  have cd := Fintype.card_congr (Equiv.ofBijective _ h)
  have hc : 2^4 = 2^B.card := by simpa only [FourBits, Fintype.card_fun, ZMod.card, Fintype.card_fin, Fintype.card_coe] using cd
  apply complete_supports B ((Nat.pow_right_injective (by decide : 2 ≤ 2)) hc.symm)
  intro x hx; apply h.1; funext j
  exact (hx j j.property).trans (map_zero (cubeRows j)).symm


/-- Every rank tuple in the fourth-power expansion of each trace factor. -/
abbrev RankTuple (n : ℕ) := Fin 8 → Fin (2^n)
def width {n : ℕ} (q : RankTuple n) (i : Fin 8) : ℕ := (q i).val + 1

/-- Rescale each matrix trace by `d²`, as in the purity expansion (33). -/
def PublishedRankCaps {n : ℕ} (K : RankTuple n → ℝ) : Prop :=
  ∀ q B, B ∈ publishedSupports → K q ≤ ∏ i ∈ B, (width q i : ℝ)

/-- The reference value of the same rescaled matrix trace by (87). -/
noncomputable def cbKernel (n : ℕ) (q : RankTuple n) : ℝ := boxCount cubeRows n (width q)

noncomputable def pureSum {n : ℕ} (delta : Fin (2^n) → ℝ) (K : RankTuple n → ℝ) : ℝ :=
  ∑ q : RankTuple n, (∏ i, delta (q i)) * K q

/-- The consequence of the published projector bounds for one rank tuple. -/
theorem kernel_le_four_cb {n : ℕ} {K : RankTuple n → ℝ} (hK : PublishedRankCaps K)
    (q : RankTuple n) : K q ≤ 4 * cbKernel n q := by
  have hr (i : Fin 8) : 0 < width q i := Nat.succ_pos _
  have hn (i : Fin 8) : width q i ≤ 2^n := (q i).isLt
  obtain ⟨B, hb, hu⟩ := cube_basis_bound n (width q) hr hn
  apply (hK q B (rowBasis_mem_supports B hb)).trans
  dsimp [cbKernel]; exact_mod_cast hu

/-- Summing against the nonnegative products of successive Schmidt gaps. -/
theorem pureSum_le_four_cb {n : ℕ} {K : RankTuple n → ℝ} (hK : PublishedRankCaps K)
    (delta : Fin (2^n) → ℝ) (hd : ∀ i, 0 ≤ delta i) :
    pureSum delta K ≤ 4 * pureSum delta (cbKernel n) := by
  unfold pureSum; rw [Finset.mul_sum]; apply Finset.sum_le_sum; intro q _
  have hn := Finset.prod_nonneg (s := Finset.univ) (fun i _ => hd (q i))
  have h := mul_le_mul_of_nonneg_left (kernel_le_four_cb hK q) hn
  linarith

private theorem cb_pureSum_pos {n : ℕ} (delta : Fin (2^n) → ℝ) (hd : ∀ i, 0 ≤ delta i)
    (hne : ∃ i, 0 < delta i) : 0 < pureSum delta (cbKernel n) := by
  obtain ⟨a, ha⟩ := hne
  let q : RankTuple n := fun _ => a
  have hpos : 0 < cbKernel n q := by
    dsimp [cbKernel]; exact_mod_cast boxCount_pos cubeRows n (width q) (fun _ => Nat.succ_pos _)
  have hs : 0 < (∏ i, delta (q i)) * cbKernel n q :=
    mul_pos (Finset.prod_pos (fun _ _ => ha)) hpos
  apply hs.trans_le
  apply Finset.single_le_sum (f := fun u : RankTuple n => (∏ i, delta (u i)) * cbKernel n u) _ (Finset.mem_univ q)
  intro u _; apply mul_nonneg (Finset.prod_nonneg (fun i _ => hd (u i)))
  dsimp [cbKernel]; positivity

/-- The logarithmic objective uses the base-two convention of Sierant. -/
noncomputable def entropy2 (purity : ℝ) := - Real.logb 2 purity

/-- The optimized purity ranges over all admissible local frames in `V`.
The sole physical inputs are Sierant's published matrix-trace caps (83),(85)
and the exact reference trace (87). The Schmidt weights and optimization
are explicit. -/
theorem entropy_gap_le_two {V : Type*} {n : ℕ} (ref : V)
    (mu : Fin (2^n+1) → ℝ) (sorted : Antitone mu)
    (nonzeroGap : ∃ j : Fin (2^n), mu j.succ < mu j.castSucc)
    (K : V → RankTuple n → ℝ) (caps : ∀ v, PublishedRankCaps (K v))
    (refTrace : K ref = cbKernel n) :
    let delta := fun j : Fin (2^n) => mu j.castSucc - mu j.succ
    let cb := pureSum delta (cbKernel n)
    let best := sSup (Set.range (fun v => pureSum delta (K v)))
    0 ≤ entropy2 cb - entropy2 best ∧ entropy2 cb - entropy2 best ≤ 2 := by
  classical
  let delta := fun j : Fin (2^n) => mu j.castSucc - mu j.succ
  let cb := pureSum delta (cbKernel n)
  let S := Set.range (fun v => pureSum delta (K v))
  change 0 ≤ entropy2 cb - entropy2 (sSup S) ∧ entropy2 cb - entropy2 (sSup S) ≤ 2
  have hd (j) : 0 ≤ delta j := sub_nonneg.mpr (sorted j.castSucc_lt_succ.le)
  have hne : ∃ j, 0 < delta j := by obtain ⟨j,h⟩ := nonzeroGap; exact ⟨j, sub_pos.mpr h⟩
  have positive : 0 < cb := cb_pureSum_pos delta hd hne
  have hc : cb ∈ S := ⟨ref, congrArg (pureSum delta) refTrace⟩
  have hu (x : ℝ) (hx : x ∈ S) : x ≤ 4 * cb := by
    obtain ⟨v, rfl⟩ := hx; exact pureSum_le_four_cb (caps v) delta hd
  have upper : sSup S ≤ 4 * cb := csSup_le ⟨cb,hc⟩ hu
  have lower : cb ≤ sSup S := le_csSup ⟨4*cb,hu⟩ hc
  have l0 := Real.logb_le_logb_of_le (by norm_num : (1:ℝ)<2) positive lower
  have l1 := Real.logb_le_logb_of_le (by norm_num : (1:ℝ)<2) (positive.trans_le lower) upper
  rw [Real.logb_mul (by norm_num) positive.ne', show Real.logb 2 4 = 2 by
    rw [show (4:ℝ) = 2^2 by norm_num, Real.logb_pow, Real.logb_self_eq_one (by norm_num)]; norm_num] at l1
  unfold entropy2; constructor <;> linarith

#print axioms direct_count
#print axioms dyadic_rectangle
#print axioms eight_coordinate_rounding
#print axioms exists_basis_product_le_four_count
#print axioms cube_basis_bound
#print axioms rowBasis_mem_supports
#print axioms entropy_gap_le_two

end SierantGap

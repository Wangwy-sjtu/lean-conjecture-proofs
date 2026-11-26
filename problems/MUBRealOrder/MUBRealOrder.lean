import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

noncomputable section

open scoped BigOperators
namespace MUBRealOrder

/-- Size-biased Jensen for a finite, nonnegative array of positive total mass. -/
theorem size_biased_power {ι : Type*} [Fintype ι] (q : ι → ℝ) (S α : ℝ)
    (hq : ∀ i, 0 ≤ q i) (hS : 0 < S) (hsum : ∑ i, q i = S) (hα : 2 ≤ α) :
    S * ((∑ i, q i ^ 2) / S) ^ (α-1) ≤ ∑ i, (q i) ^ α := by
  have hdec (i : ι) : q i ^ (α-1) * q i = q i ^ α := by
    convert (Real.rpow_add_one' (hq i) (show (α-1)+1 ≠ 0 by linarith)).symm using 1; ring_nf
  have wsum : ∑ i, q i / S = 1 := by rw [← Finset.sum_div, hsum, div_self hS.ne']
  have h := Real.rpow_arith_mean_le_arith_mean_rpow Finset.univ (fun i => q i / S) q
    (fun i _ => div_nonneg (hq i) hS.le) wsum (fun i _ => hq i) (show 1 ≤ α-1 by linarith)
  have a : ∑ i, q i / S * q i = (∑ i, q i ^ 2) / S := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun i _ => by ring
  have b : ∑ i, q i / S * q i ^ (α-1) = (∑ i, q i ^ α) / S := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun i _ => by rw [← hdec]; ring
  rw [a,b] at h
  simpa [mul_comm] using (le_div_iff₀ hS).mp h

/-- A strict excess at order two remains strict at every real order at least two. -/
theorem strict_transfer {ι : Type*} [Fintype ι] (q : ι → ℝ) (S t α : ℝ)
    (hq : ∀ i, 0 ≤ q i) (hS : 0 < S) (ht : 0 ≤ t) (hsum : ∑ i, q i = S)
    (h2 : S*t < ∑ i, q i ^ 2) (hα : 2 ≤ α) :
    S * t ^ (α-1) < ∑ i, q i ^ α := by
  have hmean : t < (∑ i, q i ^ 2) / S := (lt_div_iff₀ hS).mpr (by linarith)
  exact (mul_lt_mul_of_pos_left (Real.rpow_lt_rpow ht hmean (by linarith)) hS).trans_le
    (size_biased_power q S α hq hS hsum hα)

/-- If all nonzero entries have the same size, all real power sums are explicit. -/
theorem flat_power {ι : Type*} [Fintype ι] (q : ι → ℝ) (S t α : ℝ)
    (ht : 0 ≤ t) (hsum : ∑ i, q i = S) (hflat : ∀ i, q i = 0 ∨ q i = t) (hα : 2 ≤ α) :
    ∑ i, q i ^ α = S * t ^ (α-1) := by
  rw [← hsum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rcases hflat i with h | h
  · rw [h, Real.zero_rpow (show α ≠ 0 by linarith), zero_mul]
  · rw [h, mul_comm, ← Real.rpow_add_one' ht (show (α-1)+1 ≠ 0 by linarith)]
    congr 1
    ring

/-- Two binary digits, ordered 00, 01, 10, 11. -/
private def shift : Fin 4 → Fin 4 → Fin 4 :=
  ![![0,1,2,3], ![1,0,3,2], ![2,3,0,1], ![3,2,1,0]]

private def phase : Fin 4 → Fin 4 → ℝ :=
  ![![1,1,1,1], ![1,-1,1,-1], ![1,1,-1,-1], ![1,-1,-1,1]]

structure State where
  re : Fin 4 → ℝ
  im : Fin 4 → ℝ
  unit : ∑ j, (re j ^ 2 + im j ^ 2) = 1

/-- Squared modulus of the expectation of the two-qubit Weyl operator X^x Z^z. -/
def weylSquare (u v : Fin 4 → ℝ) (x z : Fin 4) : ℝ :=
  (∑ j, phase z j * (u (shift x j) * u j + v (shift x j) * v j)) ^ 2 +
  (∑ j, phase z j * (u (shift x j) * v j - v (shift x j) * u j)) ^ 2

/-- All fifteen nonidentity Weyl labels. -/
private def labels : Fin 15 → Fin 4 × Fin 4 :=
  ![(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),
    (3,0),(3,1),(3,2),(3,3)]

theorem labels_complete (x z : Fin 4) :
    (∃ i, labels i = (x,z)) ↔ (x,z) ≠ (0,0) := by
  fin_cases x <;> fin_cases z <;> decide

def payload (s : State) (i : Fin 15) : ℝ :=
  weylSquare s.re s.im (labels i).1 (labels i).2

theorem payload_nonneg (s : State) (i : Fin 15) : 0 ≤ payload s i :=
  add_nonneg (sq_nonneg _) (sq_nonneg _)

theorem purity (s : State) : ∑ i, payload s i = 3 := by
  have h : (∑ i, payload s i) = 3 * (∑ j, (s.re j ^ 2 + s.im j ^ 2)) ^ 2 := by
    simp [payload, labels, weylSquare, phase, shift, Fin.sum_univ_succ]
    ring
  rw [h, s.unit]
  norm_num

/-- Natural logarithms, consistent with Liu, Low and Yin (Eq. 2). -/
def entropy (α : ℝ) (s : State) : ℝ :=
  Real.log ((1 + ∑ i, (payload s i) ^ α) / 4) / (1-α)

def upper (α : ℝ) : ℝ := Real.log ((1+3*(1/4:ℝ)^(α-1))/4) / (1-α)

def flat (s : State) : Prop := ∀ i, payload s i = 0 ∨ payload s i = 1/4

/-- The published two-qubit order-two lower bound on the sum without the identity. -/
def orderTwoBound : Prop := ∀ s : State, 3/4 ≤ ∑ i, payload s i ^ 2

/-- Published classification of tight states, in terms of their squared Pauli overlaps. -/
def orderTwoEquality : Prop := ∀ s : State, (∑ i, payload s i ^ 2) = 3/4 → flat s

theorem entropy_le (H : orderTwoBound) (α : ℝ) (hα : 2 ≤ α) (s : State) :
    entropy α s ≤ upper α := by
  have hmean : (1/4:ℝ) ≤ (∑ i, payload s i ^ 2) / 3 := by
    have := H s
    linarith
  have hbound := (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (show (0:ℝ) ≤ 1/4 by norm_num) hmean (show 0 ≤ α-1 by linarith))
    (show (0:ℝ) ≤ 3 by norm_num)).trans (size_biased_power (payload s) 3 α
      (payload_nonneg s) (by norm_num) (purity s) hα)
  have hbase : 0 < (1+3*(1/4:ℝ)^(α-1))/4 := by positivity
  exact div_le_div_of_nonpos_of_le (by linarith) (Real.log_le_log hbase (by linarith))

theorem entropy_eq_iff (H : orderTwoBound) (E : orderTwoEquality) (α : ℝ) (hα : 2 ≤ α)
    (s : State) : entropy α s = upper α ↔ flat s := by
  constructor
  · intro he
    apply E s
    by_contra! hn
    have hstrict : 3 * (1/4:ℝ) < ∑ i, payload s i ^ 2 := by
      have := H s
      rcases lt_or_gt_of_ne hn with h | h <;> linarith
    have h := strict_transfer (payload s) 3 (1/4) α (payload_nonneg s) (by norm_num)
      (by norm_num) (purity s) hstrict hα
    have hlog : Real.log ((1+3*(1/4:ℝ)^(α-1))/4) <
        Real.log ((1+∑ i, (payload s i)^α)/4) := Real.log_lt_log (by positivity) (by linarith)
    have hf : entropy α s < upper α := div_lt_div_of_neg_of_lt (by linarith) hlog
    exact hf.ne he
  · intro hs
    unfold entropy upper
    rw [flat_power (payload s) 3 (1/4) α (by norm_num) (purity s) hs hα]

/-- Above order two, strict Jensen proves flatness from the numerical second-order
bound alone. The published classification of the second-order extremizers is unnecessary. -/
theorem entropy_eq_iff_above_two (H : orderTwoBound) (α : ℝ) (hα : 2 < α) (s : State) :
    entropy α s = upper α ↔ flat s := by
  let q := payload s
  have hq : ∀ i, 0 ≤ q i := payload_nonneg s
  have hs : ∑ i, q i = 3 := purity s
  have hs2 : (1/4:ℝ) ≤ (∑ i, q i ^ 2) / 3 := by have := H s; dsimp [q]; linarith
  have hsum : ∑ i, q i / 3 = 1 := by rw [← Finset.sum_div, hs]; norm_num
  have hdec (i : Fin 15) : q i ^ (α-1) * q i = q i ^ α := by
    convert (Real.rpow_add_one' (hq i) (show (α-1)+1 ≠ 0 by linarith)).symm using 1
    ring_nf
  have a : ∑ i, q i / 3 * q i = (∑ i, q i ^ 2) / 3 := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun i _ => by ring
  have b : ∑ i, q i / 3 * q i ^ (α-1) = (∑ i, q i ^ α) / 3 := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun i _ => by rw [← hdec]; ring
  constructor
  · intro he
    have hlog := (div_left_inj' (show 1-α ≠ 0 by linarith)).mp he
    have hpos : 0 < (1+∑ i, q i ^ α)/4 := by
      have hh : 0 ≤ ∑ i, q i ^ α := Finset.sum_nonneg fun i _ => Real.rpow_nonneg (hq i) _
      linarith
    have heq := Real.log_injOn_pos hpos (show 0 < (1+3*(1/4:ℝ)^(α-1))/4 by positivity) hlog
    have hval : (∑ i, q i ^ α) / 3 = (1/4:ℝ)^(α-1) := by linarith
    have hj := size_biased_power q 3 α hq (by norm_num) hs hα.le
    have hupper : ((∑ i, q i ^ 2)/3)^(α-1) ≤ (1/4:ℝ)^(α-1) := by linarith
    have hmean : (∑ i, q i ^ 2)/3 = 1/4 := le_antisymm
      ((Real.rpow_le_rpow_iff (by linarith) (by norm_num) (by linarith : 0 < α-1)).mp hupper)
      hs2
    have hf := (strictConvexOn_rpow (show 1 < α-1 by linarith)).map_sum_eq_iff'
      (t := Finset.univ) (w := fun i => q i / 3) (p := q)
      (fun i _ => div_nonneg (hq i) (by norm_num)) hsum (fun i _ => hq i)
    simp only [smul_eq_mul, a, b, hmean, hval, Finset.mem_univ, forall_true_left] at hf
    intro i
    by_cases hi : q i = 0
    · exact Or.inl hi
    · exact Or.inr (hf.mp trivial i (div_ne_zero hi (by norm_num)))
  · intro hf
    unfold entropy upper
    rw [flat_power (payload s) 3 (1/4) α (by norm_num) (purity s) hf hα.le]

/-- The WH–MUB fiducial (1,i,i,i)/2, in computational-basis order. -/
def witness : State :=
  ⟨![1/2,0,0,0], ![0,1/2,1/2,1/2], by norm_num [Fin.sum_univ_succ]⟩

theorem witness_flat : flat witness := by
  intro i
  fin_cases i <;> simp [payload, labels, weylSquare, phase, shift, witness, Fin.sum_univ_succ] <;> norm_num

theorem maximum_all_real_orders (H : orderTwoBound) (α : ℝ) (hα : 2 ≤ α) :
    IsGreatest (Set.range (entropy α)) (upper α) := by
  constructor
  · refine ⟨witness, ?_⟩
    unfold entropy upper
    rw [flat_power (payload witness) 3 (1/4) α (by norm_num) (purity witness) witness_flat hα]
  · rintro _ ⟨s, rfl⟩
    exact entropy_le H α hα s

#print axioms size_biased_power
#print axioms purity
#print axioms witness_flat
#print axioms entropy_eq_iff
#print axioms entropy_eq_iff_above_two
#print axioms maximum_all_real_orders

end MUBRealOrder

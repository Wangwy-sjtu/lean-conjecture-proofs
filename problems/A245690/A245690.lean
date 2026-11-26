import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic.NormNum

/-! OEIS A245690. For n ≥ 3, let p be the least prime that does not divide n,
and d the least divisor of n strictly larger than p. The value is d modulo p. -/

namespace A245690

set_option maxRecDepth 16000
set_option maxHeartbeats 3000000

/-- A certificate of the two minima in the original sequence definition. -/
def Witness (n p d : ℕ) : Prop :=
  3 ≤ n ∧ Nat.Prime p ∧ ¬p ∣ n ∧ (∀ q : Fin p, Nat.Prime q.val → q.val ∣ n) ∧
  p < d ∧ d ∣ n ∧ (∀ e : Fin d, p < e.val → ¬e.val ∣ n)

def HasValue (n x : ℕ) : Prop := ∃ p d, Witness n p d ∧ d % p = x

/-- Product of the primes strictly below the bound. -/
def before : ℕ → ℕ
  | 0 => 1
  | k+1 => if Nat.Prime k then before k * k else before k

/-- A prime at least as large as the strict prefix bound is absent. -/
theorem larger_prime_absent (q : ℕ) (hq : Nat.Prime q) (k : ℕ) (hk : k ≤ q) :
    ¬q ∣ before k := by
  induction k with
  | zero => exact hq.not_dvd_one
  | succ k ih =>
    rw [before]
    split_ifs with hp
    · intro hd
      rcases hq.dvd_mul.mp hd with ha | hb
      · exact ih (by omega) ha
      · have := Nat.le_of_dvd hp.pos hb
        omega
    · exact ih (by omega)

private theorem prefix_dvd (n k : ℕ) (h : ∀ q : Fin k, Nat.Prime q.val → q.val ∣ n) :
    before k ∣ n := by
  induction k with
  | zero => exact one_dvd _
  | succ k ih =>
    have old : before k ∣ n := ih fun q hq => h ⟨q, by omega⟩ hq
    rw [before]
    split_ifs with hp
    · have cop := hp.coprime_iff_not_dvd.mpr (larger_prime_absent k hp k (by omega))
      exact cop.symm.mul_dvd_of_dvd_of_dvd old (h ⟨k, by omega⟩ hp)
    · exact old

/-- Every prime below the bound divides the strict prime prefix. -/
theorem prime_in_prefix (q : ℕ) (hq : Nat.Prime q) (k : ℕ) (hk : q < k) :
    q ∣ before k := by
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases heq : q=k
    · subst q
      rw [before, if_pos hq]
      exact dvd_mul_left _ _
    · have old := ih (by omega)
      rw [before]
      split_ifs
      · exact dvd_mul_of_dvd_left old _
      · exact old

theorem before_pos (k : ℕ) : 0 < before k := by
  induction k with
  | zero => decide
  | succ k ih =>
    rw [before]
    split_ifs with hp
    · exact Nat.mul_pos ih hp.pos
    · exact ih

private theorem before_mono {k l : ℕ} (h : k ≤ l) : before k ≤ before l := by
  apply Nat.le_of_dvd (before_pos _)
  apply prefix_dvd
  intro q hq
  exact prime_in_prefix q hq l (lt_of_lt_of_le q.isLt h)

/-- Every feasible pair (p,d) has an exact minimal index: the least common
multiple of the prime prefix and d. Every other index for the pair is a multiple. -/
theorem minimal_index_for_pair {n p d : ℕ} (h : Witness n p d) :
    Witness (Nat.lcm (before p) d) p d ∧ Nat.lcm (before p) d ∣ n := by
  obtain ⟨_,hp,missing,primes,hpd,hd,least⟩ := h
  have hln := Nat.lcm_dvd (prefix_dvd n p primes) hd
  have hdpos : 0<d := lt_trans hp.pos hpd
  have hdL := Nat.dvd_lcm_right (before p) d
  have hdle := Nat.le_of_dvd (Nat.lcm_pos (before_pos p) hdpos) hdL
  have hp2 := hp.two_le
  exact ⟨⟨by omega, hp, fun hb => missing (hb.trans hln),
    fun q hq => (prime_in_prefix q hq p q.isLt).trans (Nat.dvd_lcm_left _ _),
    hpd, hdL, fun e he hb => least e he (hb.trans hln)⟩, hln⟩

/-- Matching witnesses have the same least missing prime, least divisor, and residue. -/
theorem value_unique {n x y : ℕ} (hx : HasValue n x) (hy : HasValue n y) : x=y := by
  obtain ⟨p,d,⟨_,hp,mp,lp,hd,dd,ld⟩,rx⟩ := hx
  obtain ⟨q,e,⟨_,hq,mq,lq,he,de,le⟩,ry⟩ := hy
  have peq : p=q := by
    by_contra h
    rcases lt_or_gt_of_ne h with h₁ | h₁
    · exact mp (lq ⟨p,h₁⟩ hp)
    · exact mq (lp ⟨q,h₁⟩ hq)
  subst q
  have deq : d=e := by
    by_contra h
    rcases lt_or_gt_of_ne h with h₁ | h₁
    · exact le ⟨d,h₁⟩ hd dd
    · exact ld ⟨e,h₁⟩ he de
  rw [deq] at rx
  exact rx.symm.trans ry

/-- The true first index with residue 6 is seven times the product of
the primes below 239, equivalently seven times the primorial through 233. -/
def firstSix : ℕ := 7 * before 239

private theorem first_witness : Witness firstSix 239 245 := by unfold Witness; decide

/-- For these finitely many possible least missing primes, a divisor in the next
five integers is forced by the prime prefix. Checked by Lean's kernel. -/
private theorem small_gaps : ∀ p : Fin 239, 7 ≤ p.val → Nat.Prime p.val →
    ∃ i : Fin 5, (p.val + (i.val+1)) ∣ before p.val := by decide

theorem first_six : HasValue firstSix 6 ∧ ∀ n, HasValue n 6 → firstSix ≤ n := by
  refine ⟨⟨239,245,first_witness,by decide⟩, ?_⟩
  rintro n ⟨p,d,⟨hn,hp,_,primes,hpd,hd,least⟩,hmod⟩
  have p7 : 7 ≤ p := by
    have := Nat.mod_lt d hp.pos
    omega
  have pre : before p ∣ n := prefix_dvd n p primes
  have bound (e : ℕ) (he : p < e) (hed : e ∣ n) : d ≤ e := by
    by_contra! h
    exact least ⟨e,h⟩ he hed
  by_cases small : p < 239
  · obtain ⟨i,hi⟩ := small_gaps ⟨p,small⟩ p7 hp
    have hd' := bound (p+(i.val+1)) (by omega) (hi.trans pre)
    have im := i.isLt
    rw [Nat.mod_eq_sub_mod hpd.le, Nat.mod_eq_of_lt (by omega)] at hmod
    omega
  by_cases same : p=239
  · subst p
    have de := bound 246 (by decide) ((show 246 ∣ before 239 by decide).trans pre)
    rw [Nat.mod_eq_sub_mod hpd.le, Nat.mod_eq_of_lt (by omega)] at hmod
    have hd245 : d=245 := by omega
    subst d
    have hl := Nat.lcm_dvd pre hd
    rw [show Nat.lcm (before 239) 245 = firstSix by decide] at hl
    exact Nat.le_of_dvd (by omega) hl
  · have big : before 240 ∣ n := prefix_dvd n 240 fun q hq => primes ⟨q,by omega⟩ hq
    exact (show firstSix ≤ before 240 by decide).trans (Nat.le_of_dvd (by omega) big)

theorem first_six_not_primorial (k : ℕ) : firstSix ≠ before k := by
  by_cases hk : k ≤ 239
  · have h := before_mono hk
    have hlt : before 239 < firstSix := by decide
    omega
  · intro heq
    have h := prime_in_prefix 239 (by decide) k (by omega)
    rw [← heq] at h
    exact (show ¬239 ∣ firstSix by decide) h

/-- A later base index 353 times the product of the primes below 347. -/
def laterBase : ℕ := before 347 * 353
private theorem other_witness : Witness laterBase 347 353 := by unfold Witness; decide

/-- Multiplying by a power of any prime above the tested divisor preserves both minima. -/
theorem multiply_large_prime {n p d r : ℕ} (h : Witness n p d) (hr : Nat.Prime r)
    (hl : d < r) (k : ℕ) : Witness (n*r^k) p d := by
  obtain ⟨hn,hp,hnp,primes,hpd,hd,least⟩ := h
  have cop (j : ℕ) (hj : 0 < j) (hj' : j < r) : Nat.Coprime j (r^k) := by
    apply hr.coprime_pow_of_not_dvd
    intro hdiv
    have := Nat.le_of_dvd hj hdiv
    omega
  have hpow : 0 < r^k := pow_pos hr.pos _
  refine ⟨?_,hp,fun bad => hnp ((cop p hp.pos (by omega)).dvd_of_dvd_mul_right bad),
    fun q hq => dvd_mul_of_dvd_left (primes q hq) _, hpd, dvd_mul_of_dvd_left hd _, ?_⟩
  · exact hn.trans (Nat.le_mul_of_pos_right _ hpow)
  · intro e he bad
    exact least e he ((cop e (by omega) (by omega)).dvd_of_dvd_mul_right bad)

/-- An infinite family of later occurrences of 6 outside the claimed multiples. -/
theorem later_sixes (k : ℕ) :
    firstSix < laterBase * 359^k ∧ HasValue (laterBase*359^k) 6 ∧
    ¬firstSix ∣ laterBase*359^k := by
  have hpow : 0 < 359^k := pow_pos (by decide) _
  refine ⟨(show firstSix < laterBase by decide).trans_le (Nat.le_mul_of_pos_right _ hpow),
    ⟨347,353,multiply_large_prime other_witness (by decide) (by decide) k, by decide⟩, ?_⟩
  intro h
  have h49 := (show 49 ∣ firstSix by decide).trans h
  have cop : Nat.Coprime 49 (359^k) := (show Nat.Coprime 49 359 by decide).pow_right _
  exact (show ¬49 ∣ laterBase by decide) (cop.dvd_of_dvd_mul_right h49)

theorem later_indices_increase (k : ℕ) :
    laterBase*359^k < laterBase*359^(k+1) := by
  have hp : 0 < 359^k := pow_pos (by decide) _
  have hg := Nat.mul_lt_mul_of_pos_left (show 1 < 359 by decide) hp
  rw [Nat.mul_one] at hg
  rw [pow_succ]
  exact Nat.mul_lt_mul_of_pos_left hg (by decide)

/-- The suggested restriction on the multiplier for residue 4 already fails at 43#. -/
theorem four_filter_counterexample :
    HasValue (before 47) 4 ∧ ∃ k, before 47 = 30030*k ∧ 17 ∣ k ∧ 19 ∣ k := by
  refine ⟨⟨47,51, ?_,by decide⟩, ⟨before 47/30030,?_,?_,?_⟩⟩
  · unfold Witness
    decide
  all_goals decide

end A245690

#print axioms A245690.minimal_index_for_pair
#print axioms A245690.first_six
#print axioms A245690.first_six_not_primorial
#print axioms A245690.later_sixes
#print axioms A245690.four_filter_counterexample

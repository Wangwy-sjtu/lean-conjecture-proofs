import A245690
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.Nat.Squarefree
import Mathlib.Tactic.Linarith

/-! Every positive integer occurs along a full arithmetic progression of indices
in A245690. The least divisor exceeding the first missing prime can moreover
be forced to lie at any prescribed positive distance from that prime. -/

namespace A245690

open scoped Function

/-- No prime square divides a product in which every prime occurs once. -/
private theorem square_absent (q : ℕ) (hq : q.Prime) (k : ℕ) : ¬q^2 ∣ before k := by
  induction k with
  | zero =>
    have h := hq.two_le
    change ¬q^2 ∣ 1
    intro hd
    have := Nat.le_of_dvd (by decide : 0 < 1) hd
    nlinarith
  | succ k ih =>
    rw [before]
    split_ifs with hk
    · by_cases eq : k = q
      · subst k
        rw [pow_two, Nat.mul_dvd_mul_iff_right hq.pos]
        exact larger_prime_absent q hq q le_rfl
      · have cop := ((Nat.coprime_primes hq hk).2 (Ne.symm eq)).pow_left 2
        exact fun h => ih (cop.dvd_of_dvd_mul_right h)
    · exact ih

/-- Arbitrarily far out there is a prime immediately before a prescribed row
of integers each divisible by the square of its own prime larger than `x`. -/
private theorem prime_with_square_divisors (x bound m a₀ : ℕ) (hm : 0 < m)
    (hc₀ : Nat.Coprime a₀ m) :
    ∃ p > bound, p ≡ a₀ [MOD m] ∧ Nat.Prime p ∧ ∀ j : ℕ, 0 < j → j < x →
      ∃ q : ℕ, q.Prime ∧ x < q ∧ q^2 ∣ p+j := by
  classical
  let offsets := Finset.Ico 1 x
  let q (j : ℕ) := Nat.nth Nat.Prime (x+m+j)
  have prime (j : ℕ) : (q j).Prime := Nat.nth_mem_of_infinite Nat.infinite_setOf_prime _
  have very_large (j : ℕ) : x+m < q j := by
    have := Nat.add_two_le_nth_prime (x+m+j)
    dsimp [q]
    omega
  have large (j : ℕ) : x < q j := by have := very_large j; omega
  have inject : Function.Injective q := by
    intro i j h
    exact Nat.add_left_cancel ((Nat.nth_injective Nat.infinite_setOf_prime) h)
  let modulus (j : ℕ) := q j ^ 2
  let residue (j : ℕ) := modulus j - j
  have copairs : Set.Pairwise (↑offsets : Set ℕ) (Nat.Coprime on modulus) := by
    intro i _ j _ hij
    exact Nat.coprime_pow_primes 2 2 (prime i) (prime j) (fun h => hij (inject h))
  have nz (j : ℕ) (_ : j ∈ offsets) : modulus j ≠ 0 := pow_ne_zero _ (prime j).ne_zero
  obtain ⟨a, ha⟩ := Nat.chineseRemainderOfFinset residue modulus offsets nz copairs
  have divides (j : ℕ) (hj : j ∈ offsets) : modulus j ∣ a+j := by
    have hl := (Finset.mem_Ico.mp hj).2
    have hq := large j
    have hpow : q j ≤ modulus j := by dsimp [modulus]; nlinarith [(prime j).two_le]
    have he := (ha j hj).add_right j
    change a+j ≡ modulus j-j+j [MOD modulus j] at he
    rw [Nat.sub_add_cancel (by omega)] at he
    exact Nat.modEq_zero_iff_dvd.mp (he.trans (dvd_refl _).modEq_zero_nat)
  let M := ∏ j ∈ offsets, modulus j
  have hM : M ≠ 0 := Finset.prod_ne_zero_iff.mpr nz
  have cop : Nat.Coprime a M := by
    apply Nat.coprime_prod_right_iff.mpr
    intro j hj
    have jj := Finset.mem_Ico.mp hj
    have qdiv : q j ∣ modulus j := by simp [modulus, pow_two]
    have hn : ¬q j ∣ a := by
      intro hd
      have hj' := (Nat.dvd_add_iff_right hd).mpr (qdiv.trans (divides j hj))
      have := Nat.le_of_dvd jj.1 hj'
      have := large j
      omega
    exact ((prime j).coprime_iff_not_dvd.mpr hn).symm.pow_right 2
  have hMm : Nat.Coprime M m := by
    apply Nat.coprime_prod_left_iff.mpr
    intro j _
    have no : ¬ q j ∣ m := by
      intro h
      have := Nat.le_of_dvd hm h
      have := very_large j
      omega
    exact ((prime j).coprime_iff_not_dvd.mpr no).pow_left 2
  obtain ⟨c, hcM, hcm⟩ := Nat.chineseRemainder hMm a a₀
  have cM : Nat.Coprime c M := hcM.gcd_eq.trans cop
  have cm : Nat.Coprime c m := hcm.gcd_eq.trans hc₀
  haveI : NeZero (M*m) := ⟨Nat.mul_ne_zero hM hm.ne'⟩
  obtain ⟨p, hbound, hp, hpclass⟩ := Nat.forall_exists_prime_gt_and_eq_mod
    ((ZMod.isUnit_iff_coprime c (M*m)).2 (Nat.coprime_mul_iff_right.mpr ⟨cM,cm⟩)) bound
  have hpc := (ZMod.natCast_eq_natCast_iff p c (M*m)).mp hpclass
  have hpa := (hpc.of_dvd (dvd_mul_right M m)).trans hcM
  refine ⟨p, hbound, (hpc.of_dvd (dvd_mul_left m M)).trans hcm, hp, ?_⟩
  intro j hj hx
  have hm : j ∈ offsets := Finset.mem_Ico.mpr ⟨hj,hx⟩
  have hsmall := hpa.of_dvd (Finset.dvd_prod_of_mem modulus hm)
  exact ⟨q j, prime j, large j, Nat.modEq_zero_iff_dvd.mp
    ((hsmall.add_right j).trans (divides j hm).modEq_zero_nat)⟩

/-- The least missing prime can be chosen in any prescribed reduced residue class. -/
theorem gap_in_reduced_class (x bound m a : ℕ) (hx : 0 < x) (hm : 0 < m)
    (ha : Nat.Coprime a m) : ∃ p > bound, p ≡ a [MOD m] ∧ x < p ∧
      Witness (Nat.lcm (before p) (p+x)) p (p+x) := by
  obtain ⟨p, hb, hclass, hp, guards⟩ := prime_with_square_divisors x (max (max bound x) 2) m a hm ha
  have hlarge : max bound x < p := (le_max_left _ _).trans_lt hb
  have hxp : x < p := (le_max_right _ _).trans_lt hlarge
  have hpb : bound < p := (le_max_left _ _).trans_lt hlarge
  let n := before p * (p+x)
  have hdle : p+x ≤ n := Nat.le_mul_of_pos_left _ (before_pos p)
  refine ⟨p, hpb, hclass, hxp, ?_⟩
  apply (fun h : Witness n p (p+x) => (minimal_index_for_pair h).1)
  refine ⟨by omega, hp, ?_, fun q hq => dvd_mul_of_dvd_left (prime_in_prefix q hq p q.isLt) _,
    by omega, dvd_mul_left _ _, ?_⟩
  · intro hd
    rcases hp.dvd_mul.mp hd with h | h
    · exact larger_prime_absent p hp p le_rfl h
    · have hd' : p ∣ x := (Nat.dvd_add_iff_right (dvd_refl p)).mpr h
      exact (Nat.not_le.mpr hxp) (Nat.le_of_dvd hx hd')
  · intro e he
    let j := e.val-p
    have heq : e.val = p+j := by dsimp [j]; omega
    have hj : 0 < j := by omega
    have hjx : j < x := by have ht := e.isLt; omega
    obtain ⟨q,hq,hqx,hblock⟩ := guards j hj hjx
    have qdiv : q ∣ p+j := (show q ∣ q^2 by simp [pow_two]).trans hblock
    have hlast : ¬q ∣ p+x := by
      intro hd
      have hdiff := Nat.dvd_sub hd qdiv
      rw [show p+x-(p+j) = x-j by omega] at hdiff
      have := Nat.le_of_dvd (show 0 < x-j by omega) hdiff
      omega
    have hcop := (hq.coprime_iff_not_dvd.mpr hlast).pow_left 2
    intro divides
    rw [heq] at divides
    exact square_absent q hq p (hcop.dvd_of_dvd_mul_right (hblock.trans divides))

/-- Every positive residue is attained with exact divisor gap `x` and an
arbitrarily large least missing prime. -/
theorem every_positive_gap (x bound : ℕ) (hx : 0 < x) :
    ∃ p > bound, ∃ n > bound, Witness n p (p+x) ∧ (p+x) % p = x := by
  obtain ⟨p, hp, _, hxp, w⟩ := gap_in_reduced_class x bound 1 0 hx (by decide) (by decide)
  have hdiv : p+x ∣ Nat.lcm (before p) (p+x) := Nat.dvd_lcm_right _ _
  have hl := Nat.le_of_dvd (Nat.lcm_pos (before_pos p) (by omega)) hdiv
  exact ⟨p,hp,_,by omega,w,by simp [Nat.mod_eq_of_lt hxp]⟩

/-- The range is exactly the positive integers, even after deleting any finite prefix. -/
theorem value_range_after (x bound : ℕ) : (∃ n > bound, HasValue n x) ↔ 0 < x := by
  constructor
  · rintro ⟨n, _, p, d, w, rfl⟩
    exact Nat.pos_of_ne_zero (fun h => w.2.2.1 ((Nat.dvd_of_mod_eq_zero h).trans w.2.2.2.2.2.1))
  · intro hx
    obtain ⟨p, _, n, hn, w, hv⟩ := every_positive_gap x bound hx
    exact ⟨n, hn, p, p+x, w, hv⟩

/-- Adding any multiple of `d!` preserves all divisibility checks through `d`. -/
theorem witness_on_progression {n p d : ℕ} (w : Witness n p d) (t : ℕ) :
    Witness (n+t*d.factorial) p d := by
  obtain ⟨hn, hp, hmiss, hbefore, hpd, hdiv, hleast⟩ := w
  have keep (j : ℕ) (hj : 0 < j) (hjd : j ≤ d) : j ∣ n+t*d.factorial ↔ j ∣ n :=
    (Nat.dvd_add_iff_left (dvd_mul_of_dvd_right (Nat.dvd_factorial hj hjd) t)).symm
  refine ⟨by omega, hp, fun h => hmiss ((keep p hp.pos hpd.le).mp h),
    fun q hq => (keep q hq.pos (q.isLt.trans hpd).le).mpr (hbefore q hq), hpd,
    (keep d (hp.pos.trans hpd) le_rfl).mpr hdiv, ?_⟩
  intro e hpe he
  exact hleast e hpe ((keep e (hp.pos.trans hpe) e.isLt.le).mp he)

/-- For every positive residue there is an entire arithmetic progression of
indices exhibiting that residue, with any prescribed lower bound on the start. -/
theorem progression_for_each_value (x bound : ℕ) (hx : 0 < x) :
    ∃ n > bound, ∃ v > 0, ∀ t : ℕ, HasValue (n+t*v) x := by
  obtain ⟨p, _, n, hn, w, hv⟩ := every_positive_gap x bound hx
  exact ⟨n, hn, (p+x).factorial, Nat.factorial_pos _,
    fun t => ⟨p, p+x, witness_on_progression w t, hv⟩⟩

/-- Choose a unit modulo `l²` that makes `a+x` nonzero modulo `l²`. -/
private theorem choose_class_avoiding_square (x l : ℕ) (hl : l.Prime) :
    ∃ a : ℕ, Nat.Coprime a (l^2) ∧ ¬l^2 ∣ a+x := by
  by_cases h : l^2 ∣ 1+x
  · refine ⟨1+l, ?_, ?_⟩
    · apply Nat.Coprime.pow_right
      apply (hl.coprime_iff_not_dvd.mpr ?_).symm
      exact fun hd => hl.not_dvd_one ((Nat.dvd_add_iff_left (dvd_refl l)).mpr hd)
    · intro hd
      have diff := Nat.dvd_sub hd h
      rw [show 1+l+x-(1+x)=l by omega] at diff
      have hle := Nat.le_of_dvd hl.pos diff
      nlinarith [hl.two_le]
  · exact ⟨1, Nat.coprime_one_left _, h⟩

/-- No specified prime square is unavoidable among occurrences of a positive
value, even arbitrarily far out. -/
theorem occurrence_avoiding_prime_square (x l bound : ℕ) (hx : 0 < x) (hl : l.Prime) :
    ∃ n > bound, HasValue n x ∧ ¬l^2 ∣ n := by
  obtain ⟨a,hcop,ha⟩ := choose_class_avoiding_square x l hl
  obtain ⟨p,hp,hclass,hxp,w⟩ := gap_in_reduced_class x bound (l^2) a hx (pow_pos hl.pos _) hcop
  have hd : 0 < p+x := by omega
  have hpos := Nat.lcm_pos (before_pos p) hd
  have hval : (p+x)%p=x := by simp [Nat.mod_eq_of_lt hxp]
  have hlow := Nat.le_of_dvd hpos (Nat.dvd_lcm_right (before p) (p+x))
  refine ⟨_, by omega, ⟨p,p+x,w,hval⟩, ?_⟩
  intro hs
  have fac := (hl.pow_dvd_iff_le_factorization hpos.ne').mp hs
  rw [Nat.factorization_lcm (before_pos p).ne' hd.ne', Finsupp.sup_apply] at fac
  rcases le_max_iff.mp fac with h | h
  · exact square_absent l hl p ((hl.pow_dvd_iff_le_factorization (before_pos p).ne').mpr h)
  · have hpd := (hl.pow_dvd_iff_le_factorization hd.ne').mpr h
    exact ha (Nat.modEq_zero_iff_dvd.mp ((hclass.add_right x).symm.trans hpd.modEq_zero_nat))

/-- Any divisor common to all occurrences of a positive value after any fixed
index is squarefree. -/
theorem common_divisor_squarefree (x g bound : ℕ) (hx : 0 < x)
    (common : ∀ n > bound, HasValue n x → g ∣ n) : Squarefree g := by
  apply Nat.squarefree_iff_prime_squarefree.mpr
  intro l hl hdiv
  obtain ⟨n,hn,hv,hs⟩ := occurrence_avoiding_prime_square x l bound hx hl
  exact hs ((pow_two l ▸ hdiv).trans (common n hn hv))

#print axioms gap_in_reduced_class
#print axioms every_positive_gap
#print axioms value_range_after
#print axioms progression_for_each_value
#print axioms occurrence_avoiding_prime_square
#print axioms common_divisor_squarefree

end A245690

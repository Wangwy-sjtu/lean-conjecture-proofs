import Mathlib.NumberTheory.LucasPrimality
import Mathlib.Tactic.NormNum.Prime

/-!
A347225, comment by Lamine Ngom (2021): at most two twin-prime pairs for
one common decimal-period difference other than 1 or 2.
https://oeis.org/A347225 . The period at p coprime to 10 is ord_p(10).
Lean and mathlib v4.24.0. All certificate checks below reduce in the kernel.
-/

namespace A347225

/-- Binary exponentiation with an explicit number of bits. -/
private def powBits (p b : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 1 % p
  | bits+1, n =>
    let u := powBits p b bits (n/2)
    if n%2 = 0 then u*u % p else (u*u % p)*b % p

private theorem powBits_spec (p b bits d : ℕ) (h : d < 2^bits) :
    powBits p b bits d = b^d % p := by
  induction bits generalizing d with
  | zero =>
    have : d = 0 := by simpa using h
    simp [this, powBits]
  | succ bits ih =>
    rw [Nat.pow_succ] at h
    rw [powBits, ih (d/2) (by omega)]
    split
    · rename_i even
      have e : d = d/2 + d/2 := by omega
      conv => rhs; rw [e, Nat.pow_add]
      simp
    · rename_i odd
      have e : d = (d/2 + d/2) + 1 := by omega
      conv => rhs; rw [e, Nat.pow_succ, Nat.pow_add]
      simp

private def powMod (p b d : ℕ) := powBits p b (d.log2+1) d

private theorem powMod_spec (p b d : ℕ) : powMod p b d = b^d % p :=
  powBits_spec _ _ _ _ Nat.lt_log2_self

private theorem zmod_test {m b d : ℕ} (hm : 1 < m) :
    ((b : ZMod m)^d = 1) ↔ powMod m b d = 1 := by
  rw [powMod_spec, ← Nat.cast_pow, ← Nat.cast_one (R := ZMod m),
    ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hm]

/-- Every prime divisor of a product of listed primes is on the list. -/
private theorem factor_mem {q : ℕ} (hq : q.Prime) (fs : List ℕ)
    (allPrime : ∀ r ∈ fs, Nat.Prime r) (hdiv : q ∣ fs.prod) : q ∈ fs := by
  induction fs with
  | nil =>
    have : q ∣ 1 := by simpa using hdiv
    exact (hq.not_dvd_one this).elim
  | cons r rs ih =>
    obtain ⟨hr, hrest⟩ := List.forall_mem_cons.mp allPrime
    rcases hq.dvd_mul.mp (show q ∣ r * rs.prod from hdiv) with h | h
    · have eq := ((Nat.dvd_prime hr).mp h).resolve_left hq.ne_one
      simp [eq]
    · exact List.mem_cons_of_mem r (ih hrest h)

/-- A complete prime factorization and a modular computation for each factor. -/
private def Certificate (m b d : ℕ) : Prop :=
  ∃ fs : List ℕ, (∀ q ∈ fs, Nat.Prime q) ∧
    (1 < m ∧ 0 < d ∧ fs.prod = d ∧ powMod m b d = 1 ∧
      (fs.all fun q => powMod m b (d/q) != 1) = true)

private theorem certificate_sound {m b d : ℕ} (h : Certificate m b d) :
    0 < d ∧ (b : ZMod m)^d = 1 ∧
    ∀ q : ℕ, Nat.Prime q → q ∣ d → (b : ZMod m)^(d/q) ≠ 1 := by
  obtain ⟨fs, primes, hm, hd, product, hit, miss⟩ := h
  refine ⟨hd, (zmod_test hm).2 hit, ?_⟩
  intro q hq hdiv heq
  have hmem := factor_mem hq fs primes (product.symm ▸ hdiv)
  have hne := List.all_eq_true.mp miss q hmem
  have hne' : powMod m b (d/q) ≠ 1 := by simpa using hne
  exact hne' ((zmod_test hm).1 heq)

private theorem certified_order {m b d : ℕ} (h : Certificate m b d) :
    orderOf (b : ZMod m) = d :=
  let ⟨hd, hit, miss⟩ := certificate_sound h
  orderOf_eq_of_pow_and_pow_div_prime hd hit miss

private theorem certified_prime {m b : ℕ} (h : Certificate m b (m-1)) : Nat.Prime m :=
  let ⟨_, hit, miss⟩ := certificate_sound h
  lucas_primality m (b : ZMod m) hit miss

def TwinPeriods (p d e : ℕ) : Prop :=
  p.Prime ∧ (p+2).Prime ∧ orderOf (10 : ZMod p) = d ∧ orderOf (10 : ZMod (p+2)) = e

private theorem twin_cert (p g h d e : ℕ)
    (cp : Certificate p g (p-1)) (cq : Certificate (p+2) h (p+2-1))
    (cd : Certificate p 10 d) (ce : Certificate (p+2) 10 e) :
    TwinPeriods p d e :=
  ⟨certified_prime cp, certified_prime cq, certified_order cd, certified_order ce⟩

/-- The factor list is supplied as evidence. Its product and all remaining
    modular tests are computed inside Lean; small factors use mathlib's prime tactic. -/
local macro "factors " fs:term : tactic =>
  `(tactic| (refine ⟨$fs, ?_, by decide⟩
             simp [List.forall_mem_cons] <;> norm_num))

@[local simp] private theorem prime_136281751 : Nat.Prime 136281751 :=
  certified_prime (b := 6) (by factors [2, 3, 5, 5, 5, 11, 16519])

@[local simp] private theorem prime_817690507 : Nat.Prime 817690507 :=
  certified_prime (b := 2) (by factors [2, 3, 136281751])

theorem directed_one : TwinPeriods 18690068729 9345034364 18690068730 :=
  twin_cert _ 3 2 _ _
    (by factors [2, 2, 2, 509, 1433, 3203])
    (by factors [2, 3, 5, 13241, 47051])
    (by factors [2, 2, 509, 1433, 3203])
    (by factors [2, 3, 5, 13241, 47051])

theorem directed_two : TwinPeriods 24920091641 3115011455 12460045821 :=
  twin_cert _ 3 2 _ _
    (by factors [2, 2, 2, 5, 13241, 47051])
    (by factors [2, 3, 79, 1987, 26459])
    (by factors [5, 13241, 47051])
    (by factors [3, 79, 1987, 26459])

theorem directed_three : TwinPeriods 49061430419 7008775774 16353810140 :=
  twin_cert _ 2 2 _ _
    (by factors [2, 7, 7, 11, 13, 13, 197, 1367])
    (by factors [2, 2, 3, 5, 817690507])
    (by factors [2, 7, 11, 13, 13, 197, 1367])
    (by factors [2, 2, 5, 817690507])

theorem absolute_one : TwinPeriods 1733909 1733908 866955 :=
  twin_cert _ 2 3 _ _
    (by factors [2, 2, 11, 157, 251])
    (by factors [2, 3, 5, 29, 1993])
    (by factors [2, 2, 11, 157, 251])
    (by factors [3, 5, 29, 1993])

theorem absolute_two : TwinPeriods 3715511 371551 1238504 :=
  twin_cert _ 7 5 _ _
    (by factors [2, 5, 61, 6091])
    (by factors [2, 2, 2, 3, 23, 53, 127])
    (by factors [61, 6091])
    (by factors [2, 2, 2, 23, 53, 127])

theorem absolute_three : TwinPeriods 10403441 2600860 1733907 :=
  twin_cert _ 3 2 _ _
    (by factors [2, 2, 2, 2, 5, 130043])
    (by factors [2, 3, 3, 7, 82567])
    (by factors [2, 2, 5, 130043])
    (by factors [3, 7, 82567])

/-- Increasing the smaller prime by 2 increases the decimal period by k. -/
def DirectedGap (k p : ℕ) : Prop :=
  p.Prime ∧ (p+2).Prime ∧ orderOf (10 : ZMod (p+2)) = orderOf (10 : ZMod p) + k

/-- The absolute difference of the two decimal periods is k. -/
def AbsoluteGap (k p : ℕ) : Prop :=
  p.Prime ∧ (p+2).Prime ∧
    max (orderOf (10 : ZMod p)) (orderOf (10 : ZMod (p+2))) -
    min (orderOf (10 : ZMod p)) (orderOf (10 : ZMod (p+2))) = k

def AtMostTwo (property : ℕ → Prop) : Prop :=
  ∀ a b c, property a → property b → property c → a = b ∨ a = c ∨ b = c

private theorem directed_of_periods {p d e k} (t : TwinPeriods p d e) (v : e = d+k) :
    DirectedGap k p :=
  ⟨t.1, t.2.1, by rw [t.2.2.1, t.2.2.2, v]⟩

private theorem absolute_of_periods {p d e k} (t : TwinPeriods p d e)
    (v : max d e - min d e = k) : AbsoluteGap k p :=
  ⟨t.1, t.2.1, by rw [t.2.2.1, t.2.2.2, v]⟩

theorem directed_counterexample : ¬ AtMostTwo (DirectedGap 9345034366) := by
  intro h
  have equal := h _ _ _ (directed_of_periods directed_one (by decide))
    (directed_of_periods directed_two (by decide)) (directed_of_periods directed_three (by decide))
  exact (by decide : ¬ (18690068729 = 24920091641 ∨ 18690068729 = 49061430419 ∨
                          24920091641 = 49061430419)) equal

theorem ngoms_claim_false : ¬ (∀ k : ℕ, 2 < k → AtMostTwo (DirectedGap k)) :=
  fun h => directed_counterexample (h _ (by decide))

theorem absolute_counterexample_below_billion :
    ¬ AtMostTwo (fun p => p+2 < 10^9 ∧ AbsoluteGap 866953 p) := by
  intro h
  have equal := h 1733909 3715511 10403441
    ⟨by decide, absolute_of_periods absolute_one (by decide)⟩
    ⟨by decide, absolute_of_periods absolute_two (by decide)⟩
    ⟨by decide, absolute_of_periods absolute_three (by decide)⟩
  exact (by decide : ¬ (1733909 = 3715511 ∨ 1733909 = 10403441 ∨ 3715511 = 10403441)) equal

#print axioms ngoms_claim_false
#print axioms absolute_counterexample_below_billion
end A347225

import Mathlib.Data.Nat.ModEq
import Mathlib.Data.List.Count
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Equal-cardinality additive uniqueness of rational geometric progressions.
The reduced numerator controls the maximum allowed number of summands. -/
namespace SmallSumProduct

def powerSum (r : ℚ) (xs : List ℕ) : ℚ := (xs.map (r ^ ·)).sum

private def homogenized (p q n : ℕ) (xs : List ℕ) : ℕ :=
  (xs.map (fun i => p^i * q^(n-i))).sum

private theorem clear_denom (p q n : ℕ) (hq : 0 < q) (xs : List ℕ)
    (h : ∀ i ∈ xs, i ≤ n) :
    (homogenized p q n xs : ℚ) = (q : ℚ)^n * powerSum ((p : ℚ)/q) xs := by
  induction xs with
  | nil => simp [homogenized, powerSum]
  | cons a xs ih =>
    have ha := h a (by simp)
    have ht := ih (fun i hi => h i (by simp [hi]))
    change ((p^a*q^(n-a) + homogenized p q n xs : ℕ) : ℚ) =
      (q : ℚ)^n * (((p : ℚ)/q)^a + powerSum ((p : ℚ)/q) xs)
    push_cast
    rw [ht, mul_add, div_pow, ← Nat.add_sub_of_le ha, add_comm a (n-a), pow_add]
    have hq' : (q : ℚ) ≠ 0 := by positivity
    field_simp
    simp only [Nat.add_sub_cancel]
    ring

private theorem zero_mod (p q n : ℕ) (xs : List ℕ) :
    Nat.ModEq p (homogenized p q n xs) (xs.count 0 * q^n) := by
  induction xs with
  | nil => simpa [homogenized] using (Nat.ModEq.refl 0 : Nat.ModEq p 0 0)
  | cons a xs ih =>
    cases a with
    | zero =>
      simpa [homogenized, List.count_cons, Nat.succ_mul, add_comm, Nat.add_mul] using
        Nat.ModEq.add_left (q^n) ih
    | succ a =>
      have hd : p ∣ p^(a+1) * q^(n-(a+1)) := dvd_mul_of_dvd_left (dvd_pow_self _ (by omega)) _
      have hc : Nat.ModEq p (p^(a+1) * q^(n-(a+1))) 0 := Nat.modEq_zero_iff_dvd.mpr hd
      simpa [homogenized, List.count_cons] using hc.add ih

private theorem zero_congr {p q : ℕ} (hq : 0<q) (hcop : p.Coprime q) (xs ys : List ℕ)
    (h : powerSum ((p : ℚ)/q) xs = powerSum ((p : ℚ)/q) ys) :
    Nat.ModEq p (xs.count 0) (ys.count 0) := by
  let n := xs.sum + ys.sum
  have hx (i) (hi : i ∈ xs) : i ≤ n := by
    have ht := List.le_sum_of_mem (M := ℕ) hi
    dsimp [n]; omega
  have hy (i) (hi : i ∈ ys) : i ≤ n := by
    have ht := List.le_sum_of_mem (M := ℕ) hi
    dsimp [n]; omega
  have e : homogenized p q n xs = homogenized p q n ys := by
    exact_mod_cast ((clear_denom p q n hq xs hx).trans
      ((congrArg ((q : ℚ)^n * ·) h).trans (clear_denom p q n hq ys hy).symm))
  apply Nat.ModEq.cancel_right_of_coprime (hcop.pow_right n)
  exact (zero_mod p q n xs).symm.trans (e ▸ zero_mod p q n ys)

private theorem length_le_powerSum {r : ℚ} (hr : 1 ≤ r) (xs : List ℕ) :
    (xs.length : ℚ) ≤ powerSum r xs := by
  induction xs with
  | nil => simp [powerSum]
  | cons i xs ih =>
    change ((xs.length+1 : ℕ) : ℚ) ≤ r^i + powerSum r xs
    push_cast
    linarith [one_le_pow₀ hr (n := i)]

private theorem sum_eq_length_iff {r : ℚ} (hr : 1 < r) (xs : List ℕ) :
    powerSum r xs = (xs.length : ℚ) ↔ ∀ i ∈ xs, i = 0 := by
  induction xs with
  | nil => simp [powerSum]
  | cons i xs ih =>
    change r^i + powerSum r xs = ((xs.length+1 : ℕ) : ℚ) ↔ _
    push_cast
    constructor
    · intro h
      have hz : i = 0 := by
        by_contra hn
        have := one_lt_pow₀ hr hn
        linarith [length_le_powerSum hr.le xs]
      rw [hz, pow_zero] at h
      simpa [hz] using ih.mp (by linarith)
    · intro h
      have hi := h i (by simp)
      rw [hi, pow_zero, ih.mpr (fun j hj => h j (by simp [hj]))]
      ring

private theorem count_zero_eq {p q : ℕ} (hq : 0<q) (hcop : p.Coprime q) (hpq : q<p)
    (xs ys : List ℕ) (hlen : xs.length = ys.length) (hb : xs.length ≤ p)
    (h : powerSum ((p : ℚ)/q) xs = powerSum ((p : ℚ)/q) ys) : xs.count 0 = ys.count 0 := by
  let r := (p : ℚ)/q
  have hr : 1 < r := by
    dsimp [r]; apply (lt_div_iff₀ (by positivity : (0:ℚ)<q)).mpr; exact_mod_cast (by simpa using hpq)
  have extreme (as bs : List ℕ) (hs : as.length=bs.length) (he : powerSum r as=powerSum r bs)
      (hz : as.count 0=as.length) : as.count 0=bs.count 0 := by
    have az := List.count_eq_length.mp hz
    have ea := (sum_eq_length_iff hr as).mpr (fun i hi => (az i hi).symm)
    have eb : powerSum r bs = (bs.length : ℚ) := by rw [← he, ea, hs]
    have bz := (sum_eq_length_iff hr bs).mp eb
    rw [hz, hs, List.count_eq_length.mpr (fun i hi => (bz i hi).symm)]
  by_cases ex : xs.count 0 = xs.length
  · exact extreme xs ys hlen h ex
  by_cases ey : ys.count 0 = ys.length
  · exact (extreme ys xs hlen.symm h.symm ey).symm
  have hx := List.count_le_length (a:=0) (l:=xs)
  have hy := List.count_le_length (a:=0) (l:=ys)
  exact (zero_congr hq hcop xs ys h).eq_of_lt_of_lt (by omega) (by omega)

private def lower : List ℕ → List ℕ
  | [] => []
  | 0 :: xs => lower xs
  | (i+1) :: xs => i :: lower xs

private theorem lower_length (xs : List ℕ) : (lower xs).length + xs.count 0 = xs.length := by
  induction xs with
  | nil => rfl
  | cons a xs ih => cases a <;> simp [lower] <;> omega

private theorem lower_count (xs : List ℕ) (i : ℕ) : (lower xs).count i = xs.count (i+1) := by
  induction xs with
  | nil => rfl
  | cons a xs ih => cases a <;> simp [lower, List.count_cons, ih]

private theorem lower_sum (r : ℚ) (xs : List ℕ) :
    powerSum r xs = xs.count 0 + r * powerSum r (lower xs) := by
  induction xs with
  | nil => simp [powerSum, lower]
  | cons a xs ih =>
    cases a <;> simp [powerSum, lower, pow_succ] at ih ⊢ <;> linarith

/-- Equal sums of at most `p` powers of `p/q`, with equal numbers of terms,
have the same exponent multiset when `p/q > 1` is in lowest terms. -/
theorem rational_power_counts {p q : ℕ} (hq : 0 < q) (hpq : q < p) (hcop : p.Coprime q)
    (xs ys : List ℕ) (hlen : xs.length=ys.length) (hb : xs.length≤p)
    (hs : powerSum ((p : ℚ)/q) xs=powerSum ((p : ℚ)/q) ys) (i : ℕ) :
    xs.count i = ys.count i := by
  induction i generalizing xs ys with
  | zero => exact count_zero_eq hq hcop hpq xs ys hlen hb hs
  | succ i ih =>
    have zero := count_zero_eq hq hcop hpq xs ys hlen hb hs
    have lx := lower_length xs
    have ly := lower_length ys
    have scaled : powerSum ((p : ℚ)/q) (lower xs)=powerSum ((p : ℚ)/q) (lower ys) := by
      have e := hs
      rw [lower_sum _ xs, lower_sum _ ys, zero] at e
      have hp : 0 < p := by omega
      have nz : ((p:ℚ)/q) ≠ 0 := div_ne_zero (by exact_mod_cast hp.ne') (by exact_mod_cast hq.ne')
      exact mul_left_cancel₀ nz (add_left_cancel e)
    simpa only [lower_count] using ih (lower xs) (lower ys) (by omega) (by omega) scaled

end SmallSumProduct

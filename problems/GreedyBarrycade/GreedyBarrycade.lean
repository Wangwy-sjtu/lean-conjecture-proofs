import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Every row of the greedy infinite quasi-barrycade omits finitely many positive integers

The construction is Section 3.1 of Dębski et al., *Finite and infinite
barrycades*, arXiv:2609.18476. Rows and entry indices in this file start at
zero. The values written into the rows are strictly positive, just as in the
paper. Finiteness is a partial result toward the assertion in Conjecture 2(1)
that every row after the first omits exactly one value.
-/

open Finset
namespace GreedyBarrycade

/-- The sum of the distinct entries used in a prefix. -/
def mass (u : Finset ℕ) := ∑ x ∈ u, x

/-- A legal entry is positive, fresh in this row, and produces a prefix sum
which occurs in none of the preceding complete rows. -/
def legal (forbidden : Set ℕ) (u : Finset ℕ) (x : ℕ) : Prop :=
  0 < x ∧ x ∉ u ∧ mass u + x ∉ forbidden

private noncomputable def next (f : Set ℕ) (u : Finset ℕ) : ℕ := by
  classical
  exact if h : ∃ x, legal f u x then Nat.find h else 0

private noncomputable def used (f : Set ℕ) : ℕ → Finset ℕ
  | 0 => ∅
  | n+1 => insert (next f (used f n)) (used f n)

/-- All positive-length prefix sums from all complete strictly earlier rows. -/
noncomputable def forbidden : ℕ → Set ℕ
  | 0 => ∅
  | r+1 => forbidden r ∪ {s | ∃ n, mass (used (forbidden r) (n+1)) = s}

/-- Entries already chosen in the first `n` positions of row `r`. -/
noncomputable def entriesUsed (r n : ℕ) : Finset ℕ := used (forbidden r) n

/-- The actual value at zero-based position `n` in zero-based row `r`. -/
noncomputable def entry (r n : ℕ) : ℕ := next (forbidden r) (entriesUsed r n)

private theorem prefix_succ (r n : ℕ) : entriesUsed r (n+1) = insert (entry r n) (entriesUsed r n) := rfl

private theorem forbidden_iff (r s : ℕ) : s ∈ forbidden r ↔
    ∃ i < r, ∃ j, 0 < j ∧ mass (entriesUsed i j) = s := by
  induction r with
  | zero => simp [forbidden]
  | succ r ih =>
    change (s ∈ forbidden r ∨ ∃ k, mass (entriesUsed r (k+1)) = s) ↔ _
    rw [ih]
    constructor
    · rintro (⟨i, hi, j, hj, he⟩ | ⟨k, hk⟩)
      · exact ⟨i, by omega, j, hj, he⟩
      · exact ⟨r, by omega, k+1, by omega, hk⟩
    · rintro ⟨i, hi, j, hj, he⟩
      by_cases hir : i < r
      · exact Or.inl ⟨i, hir, j, hj, he⟩
      · have : i = r := by omega
        subst i
        cases j with
        | zero => omega
        | succ k => exact Or.inr ⟨k, he⟩

/-- The sum of the first `n` positive integers. -/
def tri : ℕ → ℕ
  | 0 => 0
  | n+1 => tri n + (n+1)

private theorem tri_double (n : ℕ) : 2*tri n = n*(n+1) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [tri]; nlinarith

private theorem tri_mono : StrictMono tri :=
  strictMono_nat_of_lt_succ (fun n => by rw [tri]; omega)

private theorem triangle_at (s : ℕ) : ∃ j, tri j ≤ s ∧ s < tri (j+1) := by
  induction s with
  | zero => exact ⟨0, by decide, by decide⟩
  | succ s ih =>
    obtain ⟨j, hlo, hhi⟩ := ih
    by_cases h : s+1 < tri (j+1)
    · exact ⟨j, by omega, h⟩
    · exact ⟨j+1, by omega, by have ht : tri (j+1) < tri (j+1+1) := tri_mono (by omega); omega⟩

private theorem triangle_window (j d : ℕ) : tri (j+1) + j + d*d ≤ tri (j+2*d+2) := by
  nlinarith [tri_double (j+1), tri_double (j+2*d+2), Nat.zero_le (j*d)]

private theorem mass_icc (n : ℕ) : mass (Icc 1 n) = tri n := by
  induction n with
  | zero => simp [mass, tri]
  | succ n ih =>
    have hh : Icc 1 (n+1) = insert (n+1) (Icc 1 n) := by
      ext a
      simp only [mem_Icc, mem_insert]
      omega
    rw [hh, mass, Finset.sum_insert (by simp), ← mass, ih, tri]
    omega

private theorem mass_ge_tri (u : Finset ℕ) (hpos : ∀ x ∈ u, 0 < x) : tri u.card ≤ mass u := by
  classical
  induction u using Finset.strongInductionOn with
  | _ u ih =>
    rcases u.eq_empty_or_nonempty with h | h
    · subst u; simp [tri, mass]
    · let a := u.max' h
      have ha : a ∈ u := u.max'_mem h
      have hu : u ⊆ Icc 1 a := fun x hx => mem_Icc.mpr ⟨hpos x hx, u.le_max' x hx⟩
      have hc := card_le_card hu
      simp only [Nat.card_Icc] at hc
      have het := ih (u.erase a) (Finset.erase_ssubset ha) (fun x hx => hpos x (mem_of_mem_erase hx))
      have hl : (u.erase a).card + 1 = u.card := by
        rw [card_erase_of_mem ha]
        have := card_pos.mpr h
        omega
      have he : mass (u.erase a) + a = mass u := Finset.sum_erase_add u _ ha
      rw [← hl, tri]
      omega

private theorem mass_le_tri {u : Finset ℕ} {b : ℕ} (h : ∀ x ∈ u, 0 < x ∧ x ≤ b) :
    mass u ≤ tri b := by
  rw [← mass_icc]
  exact Finset.sum_le_sum_of_subset_of_nonneg (fun x hx => mem_Icc.mpr (h x hx)) (by intros; omega)

private def bandWidth (r b : ℕ) : ℕ := 4*r+b+5
private def allowance (r b : ℕ) : ℕ := (bandWidth r b)^2

/-- A row whose `j`-th sum lies between `tri j` and `tri (j+b)` can block
only a bounded number of candidates in any next-step interval. The bound
is uniform in the current prefix length and its current sum. -/
private theorem bounded_candidate (r b n : ℕ) (u : Finset ℕ) (hu : u.card = n)
    (hlo : tri n ≤ mass u)
    (hprev : ∀ i < r, ∀ q, tri q ≤ mass (entriesUsed i q) ∧
      mass (entriesUsed i q) ≤ tri (q+b)) :
    ∃ x, legal (forbidden r) u x ∧ x ≤ n + allowance r b := by
  classical
  let d := bandWidth r b
  have hd : d = 4*r+b+5 := rfl
  have hM : allowance r b = d*d := by simp only [allowance, pow_two, d]
  obtain ⟨j, hjlo, hjhi⟩ := triangle_at (mass u)
  have hnj : n ≤ j := by
    have hh := tri_mono.lt_iff_lt.mp (lt_of_le_of_lt hlo hjhi)
    omega
  let indices := Icc (j-b) (j+2*d+2)
  let bad := ((range r) ×ˢ indices).image (fun p => mass (entriesUsed p.1 p.2) - mass u)
  have hwidth : indices.card ≤ b+2*d+3 := by
    simp only [indices, Nat.card_Icc]
    omega
  have hbcard : bad.card ≤ r*(b+2*d+3) := by
    calc
      bad.card ≤ ((range r) ×ˢ indices).card := card_image_le
      _ = r*indices.card := by rw [card_product, card_range]
      _ ≤ _ := Nat.mul_le_mul_left _ hwidth
  have hbudget : r*(b+2*d+3) < d*d := by
    calc
      _ ≤ r*(3*d) := Nat.mul_le_mul_left _ (by omega)
      _ = (3*r)*d := by ring
      _ < _ := Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
  have hsize : (u ∪ bad).card < (Icc 1 (n+allowance r b)).card := by
    have hcard := card_union_le u bad
    rw [Nat.card_Icc, hM]
    omega
  obtain ⟨x, hx, hnot⟩ := exists_mem_notMem_of_card_lt_card hsize
  obtain ⟨hxpos, hxle⟩ := mem_Icc.mp hx
  refine ⟨x, ⟨hxpos, fun h => hnot (mem_union_left _ h), ?_⟩, hxle⟩
  intro hforb
  obtain ⟨i, hi, q, _, hq⟩ := (forbidden_iff r _).mp hforb
  obtain ⟨hpmin, hpmax⟩ := hprev i hi q
  have hlower : j ≤ q+b := tri_mono.le_iff_le.mp (by omega)
  have hupper : q ≤ j+2*d+2 := by
    apply tri_mono.le_iff_le.mp
    have hw := triangle_window j d
    rw [hM] at hxle
    omega
  have hpair : (i,q) ∈ (range r) ×ˢ indices := by
    exact mem_product.mpr ⟨mem_range.mpr hi, mem_Icc.mpr ⟨by omega, hupper⟩⟩
  apply hnot
  apply mem_union_right u
  exact mem_image.mpr ⟨(i,q), hpair, by simp [hq]⟩

private structure Good (r b : ℕ) : Prop where
  size : ∀ n, (entriesUsed r n).card = n
  bounds : ∀ n x, x ∈ entriesUsed r n → 0 < x ∧ x ≤ n+b
  least : ∀ n, legal (forbidden r) (entriesUsed r n) (entry r n) ∧
    ∀ x, legal (forbidden r) (entriesUsed r n) x → entry r n ≤ x

private theorem Good.widen {r a b : ℕ} (h : Good r a) (hab : a ≤ b) : Good r b :=
  ⟨h.size, fun n x hx => ⟨(h.bounds n x hx).1, by have := (h.bounds n x hx).2; omega⟩, h.least⟩

private theorem Good.band {r b : ℕ} (h : Good r b) (n : ℕ) :
    tri n ≤ mass (entriesUsed r n) ∧ mass (entriesUsed r n) ≤ tri (n+b) := by
  have hp := mass_ge_tri (entriesUsed r n) (fun x hx => (h.bounds n x hx).1)
  rw [h.size] at hp
  exact ⟨hp, mass_le_tri (h.bounds n)⟩

private theorem build_row (r b : ℕ) (hprev : ∀ i < r, Good i b) : Good r (allowance r b) := by
  classical
  have hstep (n : ℕ) (hc : (entriesUsed r n).card = n)
      (hp : ∀ x ∈ entriesUsed r n, 0 < x) :
      legal (forbidden r) (entriesUsed r n) (entry r n) ∧ entry r n ≤ n+allowance r b ∧
      ∀ x, legal (forbidden r) (entriesUsed r n) x → entry r n ≤ x := by
    have hl := mass_ge_tri (entriesUsed r n) hp
    rw [hc] at hl
    obtain ⟨x, hlegal, hx⟩ := bounded_candidate r b n _ hc hl (fun i hi => (hprev i hi).band)
    have hex := Exists.intro x hlegal
    have hentry : entry r n = Nat.find hex := by simp [entry, next, hex]
    rw [hentry]
    exact ⟨Nat.find_spec hex, (Nat.find_min' hex hlegal).trans hx, fun _ => Nat.find_min' hex⟩
  have hist (n : ℕ) : (entriesUsed r n).card = n ∧
      ∀ x ∈ entriesUsed r n, 0 < x ∧ x ≤ n+allowance r b := by
    induction n with
    | zero => simp [entriesUsed, used]
    | succ n ih =>
      obtain ⟨hc, hb⟩ := ih
      obtain ⟨hleg, hmax, _⟩ := hstep n hc (fun x hx => (hb x hx).1)
      rw [prefix_succ, card_insert_of_notMem hleg.2.1, hc]
      refine ⟨rfl, ?_⟩
      intro x hx
      rcases mem_insert.mp hx with rfl | hh
      · exact ⟨hleg.1, by omega⟩
      · exact ⟨(hb x hh).1, by have := (hb x hh).2; omega⟩
  refine ⟨fun n => (hist n).1, fun n => (hist n).2, ?_⟩
  intro n
  have hh := hstep n (hist n).1 (fun x hx => ((hist n).2 x hx).1)
  exact ⟨hh.1, hh.2.2⟩

/-- An explicit, nonoptimal upper bound shared by the first `r` rows. -/
def bound : ℕ → ℕ
  | 0 => 0
  | r+1 => max (bound r) ((4*r + bound r + 5)^2)

private theorem good_before (r : ℕ) : ∀ i < r, Good i (bound r) := by
  induction r with
  | zero => intros; omega
  | succ r ih =>
    intro i hi
    change Good i (max (bound r) (allowance r (bound r)))
    rcases Nat.lt_or_eq_of_le (by omega : i ≤ r) with h | h
    · exact (ih i h).widen (le_max_left _ _)
    · subst i
      exact (build_row r (bound r) ih).widen (le_max_right _ _)

private theorem good_row (r : ℕ) : Good r (bound (r+1)) := good_before (r+1) r (by omega)

/-- Each step of the recursively defined table actually attains the least legal
positive number. In particular the fallback in `next` is unreachable. -/
theorem entry_is_least (r n : ℕ) : legal (forbidden r) (entriesUsed r n) (entry r n) ∧
    ∀ x, legal (forbidden r) (entriesUsed r n) x → entry r n ≤ x := by
  exact (good_row r).least n

/-- The finite set used by the construction is exactly the set of earlier entries. -/
theorem mem_entriesUsed (r n x : ℕ) : x ∈ entriesUsed r n ↔ ∃ k < n, entry r k = x := by
  induction n with
  | zero => simp [entriesUsed, used]
  | succ n ih =>
    rw [prefix_succ, mem_insert, ih]
    constructor
    · rintro (rfl | ⟨k, hk, he⟩)
      · exact ⟨n, by omega, rfl⟩
      · exact ⟨k, by omega, he⟩
    · rintro ⟨k, hk, he⟩
      rcases Nat.lt_or_eq_of_le (by omega : k ≤ n) with h | rfl
      · exact Or.inr ⟨k,h,he⟩
      · exact Or.inl he.symm

/-- `mass` is the ordinary sum of the initial segment in its original order. -/
theorem mass_eq_prefix_sum (r n : ℕ) : mass (entriesUsed r n) = ∑ k ∈ range n, entry r k := by
  induction n with
  | zero => simp [entriesUsed, used, mass]
  | succ n ih =>
    have hf := (entry_is_least r n).1.2.1
    rw [prefix_succ, mass, sum_insert hf, ← mass, ih, sum_range_succ]
    omega

/-- The forbidden set used by `entry_is_least` is precisely all ordinary
positive-length partial sums of all preceding complete rows. -/
theorem mem_forbidden (r s : ℕ) : s ∈ forbidden r ↔
    ∃ i < r, ∃ j, 0 < j ∧ (∑ k ∈ range j, entry i k) = s := by
  simp only [forbidden_iff, mass_eq_prefix_sum]

/-- In each fixed row the `n`-th value exceeds its one-based position by at
most a constant depending only on that row. -/
theorem entry_upper_bound (r n : ℕ) : entry r n ≤ n+1+bound (r+1) :=
  ((good_row r).bounds (n+1) _ (by rw [prefix_succ]; exact mem_insert_self _ _)).2

/-- The row's ordinary partial sums stay inside a fixed-width band of
triangular indices. Both bounds hold simultaneously for all prefix lengths. -/
theorem partial_sums_band (r n : ℕ) :
    tri n ≤ (∑ k ∈ range n, entry r k) ∧ (∑ k ∈ range n, entry r k) ≤ tri (n+bound (r+1)) := by
  simpa [mass_eq_prefix_sum] using (good_row r).band n

/-- Positive integers which never occur at any position in the indicated row. -/
def omissions (r : ℕ) : Set ℕ := {x | 0 < x ∧ ∀ k, entry r k ≠ x}

private theorem omissions_bound {r b : ℕ} (hg : Good r b) (H : Finset ℕ)
    (hH : (H : Set ℕ) ⊆ omissions r) : H.card ≤ b := by
  classical
  let n := H.sup id
  have hs : H ∪ entriesUsed r n ⊆ Icc 1 (n+b) := by
    intro x hx
    rcases mem_union.mp hx with hx | hx
    · have hxle : x ≤ n := Finset.le_sup (f := id) hx
      exact mem_Icc.mpr ⟨(hH hx).1, by omega⟩
    · exact mem_Icc.mpr (hg.bounds n x hx)
  have hd : Disjoint H (entriesUsed r n) := by
    refine Finset.disjoint_left.mpr ?_
    intro x hx hi
    obtain ⟨k, _, he⟩ := (mem_entriesUsed r n x).mp hi
    exact (hH hx).2 k he
  have hc := card_le_card hs
  rw [card_union_of_disjoint hd, hg.size, Nat.card_Icc] at hc
  omega

/-- Every row of the actual greedy infinite quasi-barrycade omits only finitely
many positive integers. The number of omissions is not asserted to be one. -/
theorem finite_omissions (r : ℕ) : (omissions r).Finite := by
  by_contra hi
  obtain ⟨H, hH, hc⟩ := Set.Infinite.exists_subset_card_eq hi (bound (r+1)+1)
  have := omissions_bound (good_row r) H hH
  omega

/-- The explicit row-dependent bound also bounds the total number of omissions. -/
theorem omissions_card_bound (r : ℕ) : (finite_omissions r).toFinset.card ≤ bound (r+1) := by
  apply omissions_bound (good_row r)
  intro x hx
  exact (Set.Finite.mem_toFinset _).mp hx

/-- An eventual right-displacement bound does not depend on large entries in
a fixed finite initial segment. -/
private def EventuallyBounded (r b : ℕ) :=
  ∃ N, ∀ n ≥ N, ∀ x ∈ entriesUsed r n, x ≤ n+b

private def budget : ℕ → ℕ
  | 0 => 0
  | r+1 => 2*budget r+2

private theorem budget_sum (r : ℕ) : ∑ i ∈ range r, (budget i+2) = budget r := by
  induction r with
  | zero => rfl
  | succ r ih => rw [sum_range_succ, ih, budget]; omega

private theorem budget_closed (r : ℕ) : budget r + 2 = 2^(r+1) := by
  induction r with
  | zero => rfl
  | succ r ih => rw [pow_succ, ← ih, budget]; omega

private theorem eventual_step (r : ℕ)
    (hprev : ∀ i < r, EventuallyBounded i (budget i)) :
    ∃ N, ∀ n ≥ N, entry r n ≤ n+1+budget r := by
  classical
  let cutoff (i : Fin r) := Classical.choose (hprev i i.isLt)
  let K := (univ : Finset (Fin r)).sup cutoff
  refine ⟨K + bound r + budget r, ?_⟩
  intro n hn
  let u := entriesUsed r n
  obtain ⟨j, hjlo, hjhi⟩ := triangle_at (mass u)
  have hlo : tri n ≤ mass u := ((good_row r).band n).1
  have hnj : n ≤ j := by
    have := tri_mono.lt_iff_lt.mp (lt_of_le_of_lt hlo hjhi)
    omega
  let idx (i : ℕ) := Icc (j+1-budget i) (j+2)
  let badFor (i : ℕ) := (idx i).image (fun q => mass (entriesUsed i q) - mass u)
  let bad := (range r).biUnion badFor
  have hbad : bad.card ≤ budget r := by
    calc
      bad.card ≤ ∑ i ∈ range r, (badFor i).card := card_biUnion_le
      _ ≤ ∑ i ∈ range r, (budget i+2) := by
        apply sum_le_sum
        intro i _
        apply card_image_le.trans
        simp only [idx, Nat.card_Icc]
        omega
      _ = budget r := budget_sum r
  have hc : u.card = n := (good_row r).size n
  have hsize : (u ∪ bad).card < (Icc 1 (n+1+budget r)).card := by
    have := card_union_le u bad
    rw [Nat.card_Icc]
    omega
  obtain ⟨x,hx,hnx⟩ := exists_mem_notMem_of_card_lt_card hsize
  obtain ⟨hxp, hxm⟩ := mem_Icc.mp hx
  apply ((entry_is_least r n).2 x _).trans hxm
  refine ⟨hxp, fun h => hnx (mem_union_left _ h), ?_⟩
  intro hforb
  obtain ⟨i, hi, q, _, hq⟩ := (forbidden_iff r _).mp hforb
  change mass (entriesUsed i q) = mass u + x at hq
  obtain ⟨hmin, hmax⟩ := (good_before r i hi).band q
  have hnq : n ≤ q + bound r := tri_mono.le_iff_le.mp (by omega)
  have hki : cutoff ⟨i,hi⟩ ≤ K := Finset.le_sup (f := cutoff) (mem_univ _)
  have hqcap := Classical.choose_spec (hprev i hi) q (by change cutoff ⟨i,hi⟩ ≤ q; omega)
  have hmax' : mass (entriesUsed i q) ≤ tri (q+budget i) :=
    mass_le_tri (fun e he => ⟨((good_row i).bounds q e he).1, hqcap e he⟩)
  have hjq : j < q+budget i := tri_mono.lt_iff_lt.mp (by omega)
  have hqj : q ≤ j+2 := by
    have hlarge : tri (j+1)+n+1+budget r ≤ tri (j+3) := by
      change tri (j+1)+n+1+budget r ≤ (tri (j+1)+(j+2))+(j+3)
      omega
    have hlt : q < j+3 := tri_mono.lt_iff_lt.mp (by omega)
    omega
  apply hnx
  apply mem_union_right u
  refine mem_biUnion.mpr ⟨i, mem_range.mpr hi, ?_⟩
  exact mem_image.mpr ⟨q, mem_Icc.mpr ⟨by omega, hqj⟩, by simp [hq]⟩

private theorem eventual_row (r : ℕ) : EventuallyBounded r (budget r) := by
  induction r using Nat.strong_induction_on with
  | h r ih =>
    obtain ⟨N, hN⟩ := eventual_step r ih
    refine ⟨N+bound (r+1), ?_⟩
    intro n hn x hx
    obtain ⟨k, hk, rfl⟩ := (mem_entriesUsed r n x).mp hx
    by_cases h : N ≤ k
    · have := hN k h
      omega
    · have := entry_upper_bound r k
      omega

/-- Eventually the right displacement of every entry has the much smaller
row-index bound `2^(r+1)-2`, with `r` zero-based. -/
theorem eventual_entry_upper_bound (r : ℕ) : ∃ N, ∀ n ≥ N,
    entry r n ≤ n+1+(2^(r+1)-2) := by
  obtain ⟨N,hN⟩ := eventual_step r (fun i _ => eventual_row i)
  have hb : 2^(r+1)-2 = budget r := by have := budget_closed r; omega
  exact ⟨N, by simpa only [hb] using hN⟩

private theorem entry_injective (r : ℕ) : Function.Injective (entry r) := by
  intro a b hab
  rcases lt_trichotomy a b with h | h | h
  · exact False.elim ((entry_is_least r b).1.2.1 ((mem_entriesUsed r b _).2 ⟨a,h,hab⟩))
  · exact h
  · exact False.elim ((entry_is_least r a).1.2.1 ((mem_entriesUsed r a _).2 ⟨b,h,hab.symm⟩))

private theorem eventually_large (r m : ℕ) : ∃ N, ∀ n ≥ N, m < entry r n := by
  have hf : ((entry r) ⁻¹' Set.Iic m).Finite := (Set.finite_Iic m).preimage (entry_injective r).injOn
  obtain ⟨N,hN⟩ := hf.bddAbove
  refine ⟨N+1, ?_⟩
  intro n hn
  by_contra h
  have he : n ∈ (entry r) ⁻¹' Set.Iic m := by simpa only [Set.mem_preimage, Set.mem_Iic] using le_of_not_gt h
  have := hN he
  omega

private theorem mass_next (r n : ℕ) :
    mass (entriesUsed r (n+1)) = mass (entriesUsed r n) + entry r n := by
  rw [mass_eq_prefix_sum, mass_eq_prefix_sum, sum_range_succ]

private theorem mass_strict (r : ℕ) : StrictMono (fun n => mass (entriesUsed r n)) :=
  strictMono_nat_of_lt_succ (fun n => by
    change mass (entriesUsed r n) < mass (entriesUsed r (n+1))
    rw [mass_next]
    exact Nat.lt_add_of_pos_right (entry_is_least r n).1.1)

/-- Any finite collection of omitted values must, at one sufficiently late
step, be rejected by distinct preceding rows. -/
private theorem finite_subset_omissions_le (r : ℕ) (H : Finset ℕ)
    (hH : (H : Set ℕ) ⊆ omissions r) : H.card ≤ r := by
  classical
  let m := H.sup id
  let cutoff (i : ℕ) := Classical.choose (eventually_large i m)
  let K := (range (r+1)).sup cutoff
  have hlarge (i k : ℕ) (hi : i ≤ r) (hk : K ≤ k) : m < entry i k := by
    have hki : cutoff i ≤ K := Finset.le_sup (f := cutoff) (mem_range.mpr (by omega))
    exact Classical.choose_spec (eventually_large i m) k (hki.trans hk)
  let maxSum := (range r).sup (fun i => mass (entriesUsed i K))
  let n := K + maxSum
  let s := mass (entriesUsed r n)
  have hs : maxSum ≤ s := by
    have htri : ∀ j, j ≤ tri j := by
      intro j
      cases j with
      | zero => decide
      | succ j => rw [tri]; omega
    have hlo := ((good_row r).band n).1
    have hh := htri n
    change maxSum ≤ mass (entriesUsed r n)
    dsimp [n] at *
    omega
  have hrow : m < entry r n := hlarge r n le_rfl (by dsimp [n]; omega)
  have hhit (x : ℕ) (hx : x ∈ H) : ∃ i < r, ∃ q ≥ K, mass (entriesUsed i q) = s+x := by
    have hm : x ≤ m := Finset.le_sup (f := id) hx
    obtain ⟨hp, hmiss⟩ := hH hx
    have hf : s+x ∈ forbidden r := by
      by_contra hn
      have hnot : x ∉ entriesUsed r n := by
        intro hu
        obtain ⟨k,_,he⟩ := (mem_entriesUsed r n x).mp hu
        exact hmiss k he
      have hle := (entry_is_least r n).2 x ⟨hp, hnot, hn⟩
      omega
    obtain ⟨i,hi,q,_,he⟩ := (forbidden_iff r _).mp hf
    refine ⟨i,hi,q,?_,he⟩
    have hiK : mass (entriesUsed i K) ≤ maxSum := Finset.le_sup (f := fun i => mass (entriesUsed i K))
      (mem_range.mpr hi)
    exact (mass_strict i).le_iff_le.mp (by change mass (entriesUsed i K) ≤ mass (entriesUsed i q); omega)
  let f (x : H) : Fin r := ⟨Classical.choose (hhit x x.property), (Classical.choose_spec (hhit x x.property)).1⟩
  have hrep (x : H) : ∃ q ≥ K, mass (entriesUsed (f x) q) = s+x :=
    (Classical.choose_spec (hhit x x.property)).2
  have hinj : Function.Injective f := by
    intro a b he
    obtain ⟨p, hp, hap⟩ := hrep a
    obtain ⟨q, hq, hbq⟩ := hrep b
    rw [← he] at hbq
    have hi : (f a).val ≤ r := (f a).isLt.le
    have ha : a.val ≤ m := Finset.le_sup (f := id) a.property
    have hb : b.val ≤ m := Finset.le_sup (f := id) b.property
    apply Subtype.ext
    rcases lt_trichotomy p q with h | h | h
    · have hgap := hlarge (f a) p hi hp
      have hle : mass (entriesUsed (f a) (p+1)) ≤ mass (entriesUsed (f a) q) :=
        (mass_strict _).monotone (by omega)
      rw [mass_next] at hle
      omega
    · subst q; omega
    · have hgap := hlarge (f a) q hi hq
      have hle : mass (entriesUsed (f a) (q+1)) ≤ mass (entriesUsed (f a) p) :=
        (mass_strict _).monotone (by omega)
      rw [mass_next] at hle
      omega
  simpa using Fintype.card_le_of_injective f hinj

/-- In paper row `r+1` at most `r` positive integers are missing. -/
theorem omissions_linear_bound (r : ℕ) : (finite_omissions r).toFinset.card ≤ r := by
  apply finite_subset_omissions_le
  intro x hx
  exact (Set.Finite.mem_toFinset _).mp hx

#print axioms entry_is_least
#print axioms partial_sums_band
#print axioms eventual_entry_upper_bound
#print axioms omissions_linear_bound

end GreedyBarrycade

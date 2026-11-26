import GreedyBarrycade

/-!
# Triangular alignment and two-sided displacement for each greedy barrycade row

All definitions and the base results come from `GreedyBarrycade`. Row and term
indices are zero-based, and the entry itself is a positive integer.
-/

open Finset
namespace GreedyBarrycade

noncomputable def partialSum (r n : ℕ) : ℕ := ∑ k ∈ range n, entry r k

private theorem sum_step (r n : ℕ) : partialSum r (n+1) = partialSum r n + entry r n :=
  Finset.sum_range_succ _ _

private theorem triangle_strict : StrictMono tri := strictMono_nat_of_lt_succ
  (fun n => by change tri n < tri n+(n+1); omega)

private theorem injective_entry (r : ℕ) : Function.Injective (entry r) := by
  intro a b hab
  rcases lt_trichotomy a b with h | h | h
  · exact False.elim ((entry_is_least r b).1.2.1 ((mem_entriesUsed r b _).2 ⟨a,h,hab⟩))
  · exact h
  · exact False.elim ((entry_is_least r a).1.2.1 ((mem_entriesUsed r a _).2 ⟨b,h,hab.symm⟩))

private theorem eventually_large_entry (r m : ℕ) : ∃ N, ∀ n ≥ N, m < entry r n := by
  have hf : ((entry r) ⁻¹' Set.Iic m).Finite := (Set.finite_Iic m).preimage (injective_entry r).injOn
  obtain ⟨N,hN⟩ := hf.bddAbove
  refine ⟨N+1, ?_⟩
  intro n hn
  by_contra h
  have he : n ∈ (entry r) ⁻¹' Set.Iic m := le_of_not_gt h
  have := hN he
  omega

/-- For a fixed row the nearby upper triangle eventually advances by exactly
one index at each step, so its index has constant displacement from the prefix length. -/
theorem triangular_alignment (r : ℕ) : ∃ d c N, ∀ n ≥ N,
    partialSum r n ≤ tri (n+d) ∧ tri (n+d) ≤ partialSum r n+c := by
  classical
  obtain ⟨c,h⟩ := partial_sums_below_triangles r
  choose w hw using h
  change ∀ n, partialSum r n ≤ tri (w n) ∧ tri (w n) ≤ partialSum r n+c at hw
  have hge (n : ℕ) : n ≤ w n := triangle_strict.le_iff_le.mp ((partial_sums_band r n).1.trans (hw n).1)
  obtain ⟨K,hK⟩ := eventually_large_entry r c
  let N := K+bound (r+1)+c
  have hstep (n : ℕ) (hn : N ≤ n) : w (n+1) = w n+1 := by
    have hap := hw n
    have hbp := hw (n+1)
    rw [sum_step] at hbp
    have hlow := hK n (by dsimp [N] at hn; omega)
    have ha : w n < w (n+1) := triangle_strict.lt_iff_lt.mp (by omega)
    have hb := entry_upper_bound r n
    have hno : ¬w n+2 ≤ w (n+1) := by
      intro hh
      have ht := triangle_strict.monotone hh
      change tri (w n)+(w n+1)+(w n+2) ≤ tri (w (n+1)) at ht
      have := hge n
      dsimp [N] at hn
      omega
    omega
  let d := w N-N
  have hw' (n : ℕ) (hn : N ≤ n) : w n = n+d := by
    induction n, hn using Nat.le_induction with
    | base => have := hge N; dsimp [d]; omega
    | succ n hn ih => rw [hstep n hn, ih]; omega
  exact ⟨d,c,N,fun n hn => by rw [← hw' n hn]; exact hw n⟩

/-- An eventual lower and upper bound on each actual entry, with the same
central index shift as the partial sums. -/
theorem two_sided_displacement (r : ℕ) : ∃ d c N, ∀ n ≥ N,
    (partialSum r n ≤ tri (n+d) ∧ tri (n+d) ≤ partialSum r n+c) ∧
    (entry r n ≤ n+d+1+c ∧ n+d+1 ≤ entry r n+c) := by
  obtain ⟨d,c,N,h⟩ := triangular_alignment r
  refine ⟨d,c,N,?_⟩
  intro n hn
  have ha := h n hn
  have hb := h (n+1) (by omega)
  have hi : n+1+d = n+d+1 := by omega
  rw [sum_step, hi] at hb
  change partialSum r n+entry r n ≤ tri (n+d)+(n+d+1) ∧
    tri (n+d)+(n+d+1) ≤ partialSum r n+entry r n+c at hb
  exact ⟨ha,by omega⟩

private theorem triangle_double (a : ℕ) : 2*tri a = a*(a+1) := by
  induction a with
  | zero => rfl
  | succ a h => change 2*(tri a+(a+1))=(a+1)*(a+1+1); nlinarith

private theorem triangle_add (a b : ℕ) : tri (a+b) = tri a + b*a + tri b := by
  nlinarith [triangle_double (a+b), triangle_double a, triangle_double b]

private theorem mass_interval (n : ℕ) : mass (Icc 1 n) = tri n := by
  induction n with
  | zero => simp [mass, tri]
  | succ n ih =>
    change (∑ i ∈ Icc 1 (n+1), i) = tri n+(n+1)
    rw [sum_Icc_succ_top (by omega : 1 ≤ n+1), ← mass, ih]

private theorem size_used (r n : ℕ) : (entriesUsed r n).card = n := by
  have he : entriesUsed r n = (range n).image (entry r) := by
    ext x
    simp only [mem_entriesUsed, mem_image, mem_range]
  rw [he, card_image_of_injective _ (injective_entry r), card_range]

private theorem count_determines_shift (r d c N : ℕ) (hshape : ∀ n ≥ N,
    (partialSum r n ≤ tri (n+d) ∧ tri (n+d) ≤ partialSum r n+c) ∧
    (entry r n ≤ n+d+1+c ∧ n+d+1 ≤ entry r n+c)) :
    d = (finite_omissions r).toFinset.card := by
  classical
  let H := (finite_omissions r).toFinset
  let h := H.card
  let m := H.sup id
  let L := N+c+1
  let b := bound (r+1)
  have hHmem (x : ℕ) : x ∈ H ↔ 0<x ∧ ∀ k, entry r k ≠ x := Set.Finite.mem_toFinset _
  have estimate (t : ℕ) (ht : m ≤ t) :
      tri t+(L+h)*t ≤ partialSum r (t+L)+mass H ∧
      partialSum r (t+L)+mass H ≤ tri t+(L+h)*(t+L+b) := by
    let n := t+L
    let u := entriesUsed r n
    let low := Icc 1 t \ H
    have hH : H ⊆ Icc 1 t := by
      intro x hx
      have hxm : x ≤ m := Finset.le_sup (f := id) hx
      exact mem_Icc.mpr ⟨((hHmem x).mp hx).1, hxm.trans ht⟩
    have hlow : low ⊆ u := by
      intro x hx
      obtain ⟨hxt,hnot⟩ := mem_sdiff.mp hx
      obtain ⟨hxp,hxu⟩ := mem_Icc.mp hxt
      have home : ∃ k, entry r k = x := by
        by_contra hz
        exact hnot ((hHmem x).2 ⟨hxp,fun k hk => hz ⟨k,hk⟩⟩)
      obtain ⟨k,hk⟩ := home
      apply (mem_entriesUsed r n x).2
      refine ⟨k,?_,hk⟩
      by_contra hkn
      have hl := (hshape k (by dsimp [n,L] at hkn; omega)).2.2
      dsimp [n,L] at hkn
      omega
    have htcard : (Icc 1 t).card = t := by rw [Nat.card_Icc]; omega
    have hhlet : h ≤ t := (card_le_card hH).trans htcard.le
    have hlcard : low.card = t-h := by rw [card_sdiff_of_subset hH,htcard]
    have hucard : u.card = n := size_used r n
    have hdcard : (u \ low).card = L+h := by
      rw [card_sdiff_of_subset hlow,hucard,hlcard]
      dsimp [n]
      omega
    have hrest (x : ℕ) (hx : x ∈ u \ low) : t ≤ x ∧ x ≤ n+b := by
      obtain ⟨hu,hnlow⟩ := mem_sdiff.mp hx
      obtain ⟨k,hkn,hk⟩ := (mem_entriesUsed r n x).1 hu
      have hp := (entry_is_least r k).1.1
      have hnH : x ∉ H := fun hz => ((hHmem x).1 hz).2 k hk
      have hlower : ¬x≤t := by
        intro hh
        exact hnlow (mem_sdiff.mpr ⟨mem_Icc.mpr ⟨by omega,hh⟩,hnH⟩)
      have hb := entry_upper_bound r k
      dsimp [b]
      omega
    have heLow : mass low+mass H = tri t := (Finset.sum_sdiff hH).trans (mass_interval t)
    have heU : mass (u \ low)+mass low = mass u := Finset.sum_sdiff hlow
    have hsumMin : (L+h)*t ≤ mass (u \ low) := by
      calc
        _ = ∑ _x ∈ u \ low, t := by simp [hdcard]
        _ ≤ _ := sum_le_sum (fun x hx => (hrest x hx).1)
    have hsumMax : mass (u \ low) ≤ (L+h)*(n+b) := by
      calc
        _ ≤ ∑ _x ∈ u \ low, (n+b) := sum_le_sum (fun x hx => (hrest x hx).2)
        _ = _ := by simp [hdcard]
    have heq : mass u = partialSum r (t+L) := mass_eq_prefix_sum _ _
    change _ ∧ _ ≤ tri t+(L+h)*(n+b)
    omega
  let z := L+h
  let y := L+d
  let M := z*(L+b) + tri y + c + mass H
  have coeff (t : ℕ) (ht : m ≤ t) : y*t ≤ z*t+M ∧ z*t ≤ y*t+M := by
    obtain ⟨hl,hu⟩ := estimate t ht
    obtain ⟨ha,hb⟩ := (hshape (t+L) (by dsimp [L]; omega)).1
    have he : tri (t+L+d) = tri t+y*t+tri y := by
      rw [Nat.add_assoc,triangle_add]
    rw [he] at ha hb
    have hz : (L+h)*(t+L+b) = z*t + z*(L+b) := by dsimp [z]; ring
    rw [hz] at hu
    change tri t+z*t ≤ _ at hl
    dsimp only [M]
    omega
  let t := m+M+1
  have hab := coeff t (by dsimp [t]; omega)
  have ht : M<t := by dsimp [t]; omega
  have hzy : z=y := by
    rcases lt_trichotomy z y with hz | hz | hz
    · have hm := Nat.mul_le_mul_right t (show z+1 ≤ y by omega)
      rw [Nat.add_mul, Nat.one_mul] at hm
      omega
    · exact hz
    · have hm := Nat.mul_le_mul_right t (show y+1 ≤ z by omega)
      rw [Nat.add_mul, Nat.one_mul] at hm
      omega
  change d=h
  dsimp [z,y] at hzy
  omega

/-- Let `h` be the actual number of permanently omitted positives. For all
large `n`, the `n`-term prefix sum is at bounded distance below the specific
triangle `tri (n+h)`. Individual entries also have bounded two-sided deviation
from the corresponding shifted positions. -/
theorem alignment_by_omission_count (r : ℕ) :
    let h := (finite_omissions r).toFinset.card
    ∃ c N, ∀ n ≥ N,
      (partialSum r n ≤ tri (n+h) ∧ tri (n+h) ≤ partialSum r n+c) ∧
      (entry r n ≤ n+h+1+c ∧ n+h+1 ≤ entry r n+c) := by
  obtain ⟨d,c,N,hshape⟩ := two_sided_displacement r
  have hd := count_determines_shift r d c N hshape
  exact ⟨c,N,fun n hn => hd ▸ hshape n hn⟩

private theorem mass_min (u : Finset ℕ) (hpos : ∀ x ∈ u, 0 < x) : tri u.card ≤ mass u := by
  classical
  induction u using Finset.strongInductionOn with
  | _ u ih =>
    rcases u.eq_empty_or_nonempty with h | h
    · subst u; simp [tri,mass]
    · let a := u.max' h
      have ha : a ∈ u := u.max'_mem h
      have hu : u ⊆ Icc 1 a := fun x hx => mem_Icc.mpr ⟨hpos x hx,u.le_max' x hx⟩
      have hc := card_le_card hu
      simp only [Nat.card_Icc] at hc
      have hsmall := ih (u.erase a) (Finset.erase_ssubset ha) (fun x hx => hpos x (mem_of_mem_erase hx))
      have hl : (u.erase a).card + 1 = u.card := by
        rw [card_erase_of_mem ha]; have := card_pos.mpr h; omega
      have he : mass (u.erase a)+a = mass u := Finset.sum_erase_add u _ ha
      rw [← hl,tri]
      omega

private theorem lower_from_absent (r n : ℕ) :
    let H := (finite_omissions r).toFinset
    tri (n+H.card) ≤ partialSum r n+mass H := by
  classical
  let H := (finite_omissions r).toFinset
  let u := entriesUsed r n
  have hH (x : ℕ) (hx : x ∈ H) : x ∈ omissions r := (Set.Finite.mem_toFinset (finite_omissions r)).1 hx
  have hdis : Disjoint u H := by
    refine disjoint_left.mpr ?_
    intro x hx hmiss
    obtain ⟨k,_,he⟩ := (mem_entriesUsed r n x).1 hx
    exact (hH x hmiss).2 k he
  have hpositive (x : ℕ) (hx : x ∈ u ∪ H) : 0 < x := by
    rcases mem_union.mp hx with hx | hx
    · obtain ⟨k,_,he⟩ := (mem_entriesUsed r n x).1 hx
      exact he ▸ (entry_is_least r k).1.1
    · exact (hH x hx).1
  have hh := mass_min (u ∪ H) hpositive
  rw [card_union_of_disjoint hdis, size_used] at hh
  have hmass : mass (u ∪ H) = mass u+mass H := Finset.sum_union hdis
  rw [hmass,mass_eq_prefix_sum] at hh
  exact hh

private theorem forbidden_near_one_triangle (r : ℕ) : ∃ c, ∀ s ∈ forbidden r,
    ∃ j, s ≤ tri j ∧ tri j ≤ s+c := by
  classical
  let b (i : ℕ) := Classical.choose (partial_sums_below_triangles i)
  refine ⟨(range r).sup b, ?_⟩
  intro s hs
  obtain ⟨i,hi,n,_,he⟩ := (mem_forbidden r s).1 hs
  obtain ⟨j,hl,hu⟩ := Classical.choose_spec (partial_sums_below_triangles i) n
  have hb : b i ≤ (range r).sup b := Finset.le_sup (f := b) (mem_range.mpr hi)
  change tri j ≤ (∑ k ∈ range n, entry i k)+b i at hu
  rw [he] at hl hu
  exact ⟨j,hl,by omega⟩

/-- Let `H` be the complete finite set of missing positive integers in a row.
Eventually the deficit from `tri (n+|H|)` is between its largest element
(and zero in the empty case) and the sum of all elements of `H`. -/
theorem deficit_bounds (r : ℕ) :
    let H := (finite_omissions r).toFinset
    ∃ N, ∀ n ≥ N,
      partialSum r n+H.sup id ≤ tri (n+H.card) ∧ tri (n+H.card) ≤ partialSum r n+mass H := by
  classical
  let H := (finite_omissions r).toFinset
  let m := H.sup id
  obtain ⟨c,N,hshape⟩ := alignment_by_omission_count r
  obtain ⟨C,hC⟩ := forbidden_near_one_triangle r
  obtain ⟨K,hK⟩ := eventually_large_entry r m
  refine ⟨N+K+C+m, ?_⟩
  intro n hn
  have halign := (hshape n (by omega)).1.1
  change partialSum r n ≤ tri (n+H.card) at halign
  refine ⟨?_,lower_from_absent r n⟩
  by_cases hem : H.Nonempty
  · have hmax : m ∈ H := by
      have hle : H.sup id ≤ H.max' hem := Finset.sup_le (fun x hx => H.le_max' x hx)
      have hge : H.max' hem ≤ H.sup id := Finset.le_sup (f := id) (H.max'_mem hem)
      have hmeq : m = H.max' hem := le_antisymm hle hge
      exact hmeq ▸ H.max'_mem hem
    have hm : m ∈ omissions r := (Set.Finite.mem_toFinset _).mp hmax
    have hf : partialSum r n+m ∈ forbidden r := by
      by_contra hs
      have hnew : m ∉ entriesUsed r n := by
        intro hu
        obtain ⟨k,_,he⟩ := (mem_entriesUsed r n m).mp hu
        exact hm.2 k he
      have hlegal : legal (forbidden r) (entriesUsed r n) m :=
        ⟨hm.1,hnew,by simpa [mass_eq_prefix_sum,partialSum] using hs⟩
      have := (entry_is_least r n).2 m hlegal
      have := hK n (by omega)
      omega
    obtain ⟨j,hlo,hhi⟩ := hC _ hf
    change partialSum r n+m ≤ tri (n+H.card)
    change partialSum r n ≤ tri (n+H.card) at halign
    by_contra hnot
    have hj : n+H.card < j := triangle_strict.lt_iff_lt.mp (by omega)
    have ht : tri (n+H.card+1) ≤ tri j := triangle_strict.monotone (by omega)
    change tri (n+H.card)+(n+H.card+1) ≤ tri j at ht
    omega
  · have he : H = ∅ := not_nonempty_iff_eq_empty.mp hem
    change partialSum r n+H.sup id ≤ tri (n+H.card)
    simpa [he] using halign

/-- If the missing set consists of the single value `a`, then the entire row
is eventually in natural increasing order, with a permanent one-place shift.
The prefix identity also identifies the omitted value as the exact deficit. -/
theorem singleton_tail (r a : ℕ) (ha : (finite_omissions r).toFinset = {a}) :
    ∃ N, ∀ n ≥ N, partialSum r n+a = tri (n+1) ∧ entry r n=n+2 := by
  obtain ⟨N,hN⟩ := deficit_bounds r
  have ht (n : ℕ) (hn : N ≤ n) : partialSum r n+a = tri (n+1) := by
    have hh := hN n hn
    simp only [ha, sup_singleton, id_eq, card_singleton, mass, sum_singleton] at hh
    omega
  refine ⟨N,?_⟩
  intro n hn
  have hnext := ht (n+1) (by omega)
  rw [sum_step] at hnext
  change partialSum r n+entry r n+a = tri (n+1)+(n+2) at hnext
  exact ⟨ht n hn, by have := ht n hn; omega⟩

/-- Exact equivalence with eventual unit-shifted increasing order, for an
individual row. A zero-based entry at `n` is the paper's `(n+1)`-st entry. -/
theorem singleton_iff_tail (r : ℕ) : (∃ a, (finite_omissions r).toFinset = {a}) ↔
    ∃ N, ∀ n ≥ N, entry r n = n+2 := by
  constructor
  · rintro ⟨a,ha⟩
    obtain ⟨N,hN⟩ := singleton_tail r a ha
    exact ⟨N,fun n hn => (hN n hn).2⟩
  · rintro ⟨N,hN⟩
    let H := (finite_omissions r).toFinset
    let u := entriesUsed r N
    have hin (x : ℕ) : x ∈ H ↔ x ∈ omissions r := Set.Finite.mem_toFinset _
    have hrange (x : ℕ) (hx : N+2 ≤ x) : entry r (x-2) = x := by
      rw [hN (x-2) (by omega)]
      omega
    have hsub : u ⊆ Icc 1 (N+1) := by
      intro x hx
      obtain ⟨k,hk,he⟩ := (mem_entriesUsed r N x).1 hx
      have hp := (entry_is_least r k).1.1
      refine mem_Icc.mpr ⟨by omega, ?_⟩
      by_contra h
      have hboth := (injective_entry r) (he.trans (hrange x (by omega)).symm)
      omega
    have hs : H = Icc 1 (N+1) \ u := by
      ext x
      rw [hin,mem_sdiff,mem_Icc]
      constructor
      · intro hx
        obtain ⟨hp,habs⟩ := hx
        refine ⟨⟨hp,?_⟩,?_⟩
        · by_contra h
          exact habs (x-2) (hrange _ (by omega))
        · intro hu
          obtain ⟨k,_,he⟩ := (mem_entriesUsed r N x).1 hu
          exact habs k he
      · rintro ⟨⟨hp,hx⟩,hu⟩
        refine ⟨hp,?_⟩
        intro k he
        by_cases hk : k < N
        · exact hu ((mem_entriesUsed r N x).2 ⟨k,hk,he⟩)
        · have := hN k (by omega)
          omega
    have hc : H.card = 1 := by
      rw [hs,card_sdiff_of_subset hsub,Nat.card_Icc,size_used]
      omega
    exact Finset.card_eq_one.mp hc

#print axioms alignment_by_omission_count
#print axioms deficit_bounds
#print axioms singleton_iff_tail

end GreedyBarrycade

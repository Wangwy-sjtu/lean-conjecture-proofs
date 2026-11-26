import GreedyBarrycadeStructure

/-!
# When a finite prefix certifies a unique permanent omission

A row with an omission exceeding every earlier row's total omitted mass has
no second omission. In particular, once a finite prefix covers the interval
up to that threshold, the nonempty omission set is forced to be a singleton.
-/

open Finset
namespace GreedyBarrycade

/-- The largest of the sums of the missing elements in the earlier rows. -/
noncomputable def previousOmissionMass (r : ℕ) :=
  (range r).sup fun i => mass (finite_omissions i).toFinset

private noncomputable abbrev holes (r : ℕ) := (finite_omissions r).toFinset

private theorem inHoles (r x : ℕ) : x ∈ holes r ↔ x ∈ omissions r :=
  Set.Finite.mem_toFinset _

private theorem triGrowing : StrictMono tri := strictMono_nat_of_lt_succ
  (fun n => by change tri n < tri n+(n+1); omega)

private theorem prefix_large (r n : ℕ) : n ≤ partialSum r n := by
  have htriangle : n ≤ tri n := by
    cases n with
    | zero => simp [tri]
    | succ k => change k+1 ≤ tri k+(k+1); omega
  exact htriangle.trans (partial_sums_band r n).1

private theorem prefix_card (r n : ℕ) : (entriesUsed r n).card = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (insert (entry r n) (entriesUsed r n)).card=n+1
    rw [card_insert_of_notMem (entry_is_least r n).1.2.1, ih]

private theorem before_all_small (r b : ℕ) : ∃ N, ∀ n ≥ N, ∀ x ≤ b, 0<x →
    x ∉ holes r → x ∈ entriesUsed r n := by
  obtain ⟨c,N,hN⟩ := alignment_by_omission_count r
  refine ⟨N+c+b,?_⟩
  intro n hn x hxb hpos hnot
  by_contra hnew
  apply hnot
  apply (inHoles r x).mpr
  refine ⟨hpos,?_⟩
  intro k he
  by_cases hk : k<n
  · exact hnew ((mem_entriesUsed r n x).mpr ⟨k,hk,he⟩)
  · have := (hN k (by omega)).2.2
    omega

private theorem previous_bands (r : ℕ) : ∃ B, ∀ s>B, s ∈ forbidden r →
    ∃ j, s ≤ tri j ∧ tri j ≤ s+previousOmissionMass r := by
  classical
  choose start hs using (fun i : Fin r => deficit_bounds i)
  let highest := (univ : Finset (Fin r)).sup fun i => start i+bound (i+1)
  refine ⟨tri highest,?_⟩
  intro s hb hf
  obtain ⟨i,hi,n,_,he⟩ := (mem_forbidden r s).mp hf
  change partialSum i n=s at he
  let j : Fin r := ⟨i,hi⟩
  have hn : start j≤n := by
    by_contra h
    have hl : start j+bound (i+1)≤highest := le_sup (f:=fun i : Fin r => start i+bound (i+1)) (mem_univ j)
    have ht := triGrowing.monotone (show n+bound (i+1)≤highest by omega)
    have hu := (partial_sums_band i n).2
    change partialSum i n≤tri (n+bound (i+1)) at hu
    omega
  have hboth := hs j n hn
  have hmass : mass (holes i) ≤ previousOmissionMass r :=
    le_sup (f:=fun k => mass (holes k)) (mem_range.mpr hi)
  change partialSum i n+(holes i).sup id ≤ tri (n+(holes i).card) ∧
    tri (n+(holes i).card) ≤ partialSum i n+mass (holes i) at hboth
  exact ⟨n+(holes i).card,by omega,by omega⟩

private theorem between_bands {r C B s k : ℕ}
    (hb : ∀ t>B, t∈forbidden r → ∃ j, t≤tri j ∧ tri j≤t+C)
    (hs : B<s) (hl : tri k<s) (hu : s+C<tri (k+1)) : s ∉ forbidden r := by
  intro hf
  obtain ⟨j,hleft,hright⟩ := hb s hs hf
  have hj : k<j := triGrowing.lt_iff_lt.mp (by omega)
  have := triGrowing.monotone (show k+1≤j by omega)
  omega

private theorem small_step_of_high_hole (r h : ℕ) (hh : h∈holes r)
    (hhigh : previousOmissionMass r<h) : ∃ N, ∀ n ≥ N, entry r n ≤ n+(holes r).card+1 := by
  classical
  obtain ⟨B,hB⟩ := previous_bands r
  obtain ⟨L,hL⟩ := before_all_small r (mass (holes r))
  obtain ⟨K,hK⟩ := deficit_bounds r
  refine ⟨B+L+K+1,?_⟩
  intro n hn
  let p := n+(holes r).card
  have hcard : (entriesUsed r n ∪ holes r).card < (Icc 1 (p+1)).card := by
    have hbound := card_union_le (entriesUsed r n) (holes r)
    rw [prefix_card] at hbound
    rw [Nat.card_Icc]
    dsimp [p]; omega
  obtain ⟨x,hx⟩ := Finset.sdiff_nonempty_of_card_lt_card hcard
  obtain ⟨⟨hxpos,hxle⟩,houtside⟩ := (show x ∈ Icc 1 (p+1) ∧ x∉entriesUsed r n ∪ holes r from mem_sdiff.mp hx).imp_left mem_Icc.mp
  have hnew : x∉entriesUsed r n := fun hu => houtside (mem_union_left _ hu)
  have hnot : x∉holes r := fun hh => houtside (mem_union_right _ hh)
  have hbig : mass (holes r)<x := by
    by_contra hnb
    exact hnew (hL n (by omega) x (by omega) (by omega) hnot)
  have hb := hK n (by omega)
  change partialSum r n+(holes r).sup id≤tri p ∧ tri p≤partialSum r n+mass (holes r) at hb
  have htop : h≤(holes r).sup id := le_sup (f:=id) hh
  have hpos := prefix_large r n
  have hnxt : partialSum r n+x+previousOmissionMass r<tri (p+1) := by
    change partialSum r n+x+previousOmissionMass r<tri p+(p+1)
    omega
  have hfree := between_bands hB (show B<partialSum r n+x by omega) (show tri p<partialSum r n+x by omega) hnxt
  have hlegal : legal (forbidden r) (entriesUsed r n) x :=
    ⟨by omega,hnew,by simpa [mass_eq_prefix_sum,partialSum] using hfree⟩
  exact ((entry_is_least r n).2 x hlegal).trans hxle

private theorem mass_interval_eq (n : ℕ) : mass (Icc 1 n) = tri n := by
  induction n with
  | zero => simp [mass,tri]
  | succ n ih =>
    change (∑ i ∈ Icc 1 (n+1), i) = tri n+(n+1)
    rw [sum_Icc_succ_top (by omega : 1 ≤ n+1), ← mass, ih]

private theorem mass_equality_of_small_steps (r : ℕ)
    (hsmall : ∃ N, ∀ n≥N, entry r n≤n+(holes r).card+1) :
    ∃ N, ∀ n≥N, partialSum r n+mass (holes r)=tri (n+(holes r).card) := by
  classical
  obtain ⟨K,hK⟩ := hsmall
  refine ⟨K+bound (r+1)+(holes r).sup id+1,?_⟩
  intro n hn
  let p := n+(holes r).card
  have hsub : entriesUsed r n ∪ holes r ⊆ Icc 1 p := by
    intro x hx
    rcases mem_union.mp hx with hu | hh
    · obtain ⟨k,hk,he⟩ := (mem_entriesUsed r n x).mp hu
      have hpos := (entry_is_least r k).1.1
      refine mem_Icc.mpr ⟨by omega,?_⟩
      by_cases hlate : K≤k
      · have := hK k hlate; dsimp [p]; omega
      · have := entry_upper_bound r k; dsimp [p]; omega
    · have hpos := ((inHoles r x).mp hh).1
      have htop : x≤(holes r).sup id := le_sup (f:=id) hh
      exact mem_Icc.mpr ⟨by omega,by dsimp [p]; omega⟩
  have hdisj : Disjoint (entriesUsed r n) (holes r) := by
    refine disjoint_left.mpr ?_
    intro x hu hh
    obtain ⟨k,_,he⟩ := (mem_entriesUsed r n x).mp hu
    exact ((inHoles r x).mp hh).2 k he
  have heq : entriesUsed r n ∪ holes r=Icc 1 p := by
    apply eq_of_subset_of_card_le hsub
    rw [card_union_of_disjoint hdisj, prefix_card, Nat.card_Icc]
    dsimp [p]; omega
  have hsum : mass (entriesUsed r n ∪ holes r)=mass (entriesUsed r n)+mass (holes r) := Finset.sum_union hdisj
  rw [heq, mass_interval_eq, mass_eq_prefix_sum] at hsum
  exact hsum.symm

/-- Any missing number exceeding the largest earlier omitted mass is the
unique missing number of its row. This statement uses the original table. -/
theorem singleton_of_omission_above_previous (r h : ℕ) (hh : h∈omissions r)
    (hhigh : previousOmissionMass r<h) : (finite_omissions r).toFinset={h} := by
  classical
  have hmem := (inHoles r h).mpr hh
  obtain ⟨K,hK⟩ := mass_equality_of_small_steps r (small_step_of_high_hole r h hmem hhigh)
  obtain ⟨B,hB⟩ := previous_bands r
  obtain ⟨c,L,hL⟩ := alignment_by_omission_count r
  ext t
  rw [mem_singleton]
  constructor
  · intro ht
    by_contra hdiff
    have htmem := (inHoles r t).mp ht
    have hsub : {h,t} ⊆ holes r := by
      intro x hx
      rw [mem_insert,mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hmem
      · exact ht
    have hmass : h+t ≤ mass (holes r) := by
      have hs := Finset.sum_le_sum_of_subset (f:=fun x : ℕ => x) hsub
      simpa [mass,Ne.symm hdiff] using hs
    let m := B+c+K+L+mass (holes r)+t
    let n := m+1
    let k := m+(holes r).card
    have hmassEq := hK n (by dsimp [n,m]; omega)
    change partialSum r n+mass (holes r)=tri (n+(holes r).card) at hmassEq
    rw [show n+(holes r).card=k+1 by dsimp [n,k]; omega] at hmassEq
    have hsum := prefix_large r n
    have hbetween : tri k < partialSum r n+t := by
      change partialSum r n+mass (holes r)=tri k+(k+1) at hmassEq
      have hk : mass (holes r) ≤ k := by dsimp [k,m]; omega
      omega
    have hBn : B<n := by dsimp [n,m]; omega
    have hfree := between_bands hB (show B<partialSum r n+t by omega)
      hbetween (show partialSum r n+t+previousOmissionMass r<tri (k+1) by omega)
    have hnew : t∉entriesUsed r n := by
      intro hu
      obtain ⟨j,_,hj⟩ := (mem_entriesUsed r n t).mp hu
      exact htmem.2 j hj
    have hlegal : legal (forbidden r) (entriesUsed r n) t :=
      ⟨htmem.1,hnew,by simpa [mass_eq_prefix_sum,partialSum] using hfree⟩
    have hmin := (entry_is_least r n).2 t hlegal
    have hlate := (hL n (by dsimp [n,m]; omega)).2.2
    have hfar : c+t<n := by dsimp [n,m]; omega
    omega
  · intro he; exact he ▸ hmem

/-- Covering the finite initial interval is equivalent to missing exactly one
number above the threshold. A finite prefix supplying this coverage certifies
the entire infinite row, without having to identify its final sorted state. -/
theorem finite_prefix_iff_unique_above (r : ℕ) (hr : 0<r) :
    (∃ n, Icc 1 (previousOmissionMass r) ⊆ entriesUsed r n) ↔
    ∃ h>previousOmissionMass r, (finite_omissions r).toFinset={h} := by
  classical
  constructor
  · rintro ⟨n,hcov⟩
    obtain ⟨h,hh⟩ := nonfirst_has_omission r hr
    have hhigh : previousOmissionMass r<h := by
      by_contra hn
      have hpos := hh.1
      have hu := hcov (mem_Icc.mpr (show 1≤h ∧ h≤previousOmissionMass r by omega))
      obtain ⟨k,_,he⟩ := (mem_entriesUsed r n h).mp hu
      exact hh.2 k he
    exact ⟨h,hhigh,singleton_of_omission_above_previous r h hh hhigh⟩
  · rintro ⟨h,hhigh,honly⟩
    obtain ⟨N,hN⟩ := before_all_small r (previousOmissionMass r)
    refine ⟨N,?_⟩
    intro x hx
    obtain ⟨hpos,hlo⟩ := mem_Icc.mp hx
    apply hN N le_rfl x hlo (by omega)
    change x∉(finite_omissions r).toFinset
    rw [honly,mem_singleton]
    omega

/-- A strictly increasing sequence of actual omitted witnesses, one per row
starting at the second, suffices for all the uniqueness claims simultaneously.
The witnesses need not be assumed smallest or unique. -/
theorem all_singletons_of_increasing_omissions (a : ℕ → ℕ) (hincr : StrictMono a)
    (hmiss : ∀ k, a k ∈ omissions (k+1)) :
    ∀ k, (finite_omissions (k+1)).toFinset={a k} := by
  classical
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    apply singleton_of_omission_above_previous (k+1) (a k) (hmiss k)
    have hpos := (hmiss k).1
    have hbound : previousOmissionMass (k+1) ≤ a k-1 := by
      apply Finset.sup_le
      intro i hi
      have hik : i<k+1 := mem_range.mp hi
      cases i with
      | zero =>
        have he : (holes 0).card=0 := Nat.eq_zero_of_le_zero (omissions_linear_bound 0)
        have hzero : holes 0=∅ := card_eq_zero.mp he
        change mass (holes 0) ≤ a k-1
        simp [hzero,mass]
      | succ j =>
        have hj : j<k := by omega
        rw [ih j hj]
        simp only [mass,sum_singleton]
        have := hincr hj
        omega
    omega

/-- The first entries increase strictly across the actual rows. -/
theorem strictly_increasing_first_entries : StrictMono (fun r => entry r 0) := by
  intro i j hij
  have hempty (r : ℕ) : entriesUsed r 0=∅ := rfl
  have hzero (r : ℕ) : mass (entriesUsed r 0)=0 := by simp [hempty,mass]
  have hj := (entry_is_least j 0).1
  have hf : entry j 0∉forbidden j := by simpa [hzero,legal] using hj.2.2
  have hfi : entry j 0∉forbidden i := by
    intro he
    obtain ⟨k,hki,n,hn,h⟩ := (mem_forbidden i _).mp he
    exact hf ((mem_forbidden j _).mpr ⟨k,by omega,n,hn,h⟩)
  have hleg : legal (forbidden i) (entriesUsed i 0) (entry j 0) :=
    ⟨hj.1,by simp [hempty],by simpa [hzero] using hfi⟩
  have hle := (entry_is_least i 0).2 _ hleg
  have hne : entry i 0≠entry j 0 := by
    intro he
    apply hf
    apply (mem_forbidden j _).mpr
    exact ⟨i,hij,1,by decide,by simpa using he⟩
  exact lt_of_le_of_ne hle hne

private theorem actual_first_row (n : ℕ) : entriesUsed 0 n=Icc 1 n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    obtain ⟨hlegal,hleast⟩ := entry_is_least 0 n
    have hcan : legal (forbidden 0) (entriesUsed 0 n) (n+1) := by simp [legal,ih,forbidden]
    have hle := hleast _ hcan
    have hpos := hlegal.1
    have hnew := hlegal.2.1
    rw [ih,mem_Icc] at hnew
    have he : entry 0 n=n+1 := by omega
    change insert (entry 0 n) (entriesUsed 0 n)=Icc 1 (n+1)
    rw [he,ih]
    ext x
    simp only [mem_insert,mem_Icc]
    omega

private theorem first_row_triangles (n : ℕ) : partialSum 0 n=tri n := by
  change (∑ k ∈ range n, entry 0 k)=tri n
  rw [← mass_eq_prefix_sum,actual_first_row,mass_interval_eq]

private theorem triangle_in_previous (r : ℕ) (hr : 0<r) (j : ℕ) (hj : 0<j) : tri j∈forbidden r :=
  (mem_forbidden r _).mpr ⟨0,hr,j,hj,first_row_triangles j⟩

private theorem missing_after_init (r N h C : ℕ) (hr : 0<r) (hbig : C<h) (hfit : h≤N+1)
    (hstart : entriesUsed r N=Icc 1 (N+1) \ {h})
    (hbands : ∀ s>0, s∈forbidden r → ∃ j, s≤tri j ∧ tri j≤s+C) :
    ∀ n≥N, entriesUsed r n=Icc 1 (n+1) \ {h} ∧ partialSum r n+h=tri (n+1) := by
  classical
  have total (n : ℕ) (hn : N≤n) (hs : entriesUsed r n=Icc 1 (n+1) \ {h}) :
      mass (entriesUsed r n)+h=tri (n+1) := by
    rw [hs,sdiff_singleton_eq_erase]
    have hm : h∈Icc 1 (n+1) := mem_Icc.mpr ⟨by omega,by omega⟩
    exact (Finset.sum_erase_add (Icc 1 (n+1)) (fun x=>x) hm).trans (mass_interval_eq (n+1))
  have evolve (n : ℕ) (hn : N≤n) (hs : entriesUsed r n=Icc 1 (n+1) \ {h}) :
      entriesUsed r (n+1)=Icc 1 (n+2) \ {h} := by
    have hm := total n hn hs
    let s := mass (entriesUsed r n)+(n+2)
    have hfree : s∉forbidden r := by
      apply between_bands (k:=n+1) hbands (by dsimp [s]; omega) (by dsimp [s]; omega)
      change mass (entriesUsed r n)+(n+2)+C<tri (n+1)+(n+2)
      omega
    have hlegal : legal (forbidden r) (entriesUsed r n) (n+2) :=
      ⟨by omega,by simp [hs],hfree⟩
    obtain ⟨hchosen,hleast⟩ := entry_is_least r n
    have hle := hleast _ hlegal
    have hnot := hchosen.2.1
    have hpos := hchosen.1
    have hne : entry r n≠h := by
      intro he
      have hb := hchosen.2.2
      rw [he,hm] at hb
      exact hb (triangle_in_previous r hr (n+1) (by omega))
    rw [hs,mem_sdiff,mem_Icc,mem_singleton] at hnot
    have he : entry r n=n+2 := by omega
    change insert (entry r n) (entriesUsed r n)=Icc 1 (n+2) \ {h}
    rw [he,hs]
    ext x
    simp only [mem_insert,mem_sdiff,mem_Icc,mem_singleton]
    omega
  intro n hn
  have hs : entriesUsed r n=Icc 1 (n+1) \ {h} := by
    induction n, hn using Nat.le_induction with
    | base => exact hstart
    | succ n hn ih => exact evolve n hn ih
  refine ⟨hs,?_⟩
  simpa [mass_eq_prefix_sum,partialSum] using total n hn hs

private theorem actual_second_row (n : ℕ) :
    entriesUsed 1 n=Icc 1 (n+1) \ {1} ∧ partialSum 1 n+1=tri (n+1) := by
  apply missing_after_init 1 0 1 0 (by decide) (by decide) (by decide) (by decide) _ n (Nat.zero_le n)
  intro s _ hs
  obtain ⟨i,hi,j,_,he⟩ := (mem_forbidden 1 s).mp hs
  have hzero : i=0 := by omega
  subst i
  change partialSum 0 j=s at he
  rw [first_row_triangles] at he
  exact ⟨j,by omega,by omega⟩

private theorem previous_for_third (s : ℕ) : s∈forbidden 2 ↔
    ∃ j, 0<j ∧ (s=tri j ∨ s+1=tri (j+1)) := by
  constructor
  · intro hs
    obtain ⟨i,hi,j,hj,he⟩ := (mem_forbidden 2 s).mp hs
    change partialSum i j=s at he
    have hcases : i=0 ∨ i=1 := by omega
    rcases hcases with rfl | rfl
    · exact ⟨j,hj,Or.inl (he.symm.trans (first_row_triangles j))⟩
    · have hval := (actual_second_row j).2
      exact ⟨j,hj,Or.inr (by omega)⟩
  · rintro ⟨j,hj,he | he⟩
    · rw [he]; exact triangle_in_previous 2 (by decide) j hj
    · apply (mem_forbidden 2 s).mpr
      have hval := (actual_second_row j).2
      exact ⟨1,by decide,j,hj,by change partialSum 1 j=s; omega⟩

private def smallForbidden : Finset ℕ := {1,2,3,5,6,9,10}

private theorem initial_forbidden (s : ℕ) (hs : s≤10) : s∈forbidden 2 ↔ s∈smallForbidden := by
  rw [previous_for_third]
  constructor
  · rintro ⟨j,hj,he⟩
    have jsmall : j<5 := by
      by_contra hbad
      have hl := triGrowing.monotone (show 5≤j by omega)
      have hl' := triGrowing.monotone (show 5≤j+1 by omega)
      change 15≤tri j at hl
      change 15≤tri (j+1) at hl'
      omega
    have hc : j=1 ∨ j=2 ∨ j=3 ∨ j=4 := by omega
    rcases hc with rfl | rfl | rfl | rfl <;>
      simp only [smallForbidden,mem_insert,mem_singleton] <;> simp only [tri] at he <;> omega
  · simp only [smallForbidden,mem_insert,mem_singleton]
    rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    · exact ⟨1,by decide,by decide⟩
    · exact ⟨1,by decide,by decide⟩
    · exact ⟨2,by decide,by decide⟩
    · exact ⟨2,by decide,by decide⟩
    · exact ⟨3,by decide,by decide⟩
    · exact ⟨3,by decide,by decide⟩
    · exact ⟨4,by decide,by decide⟩

private theorem early_entry (n x : ℕ) (u : Finset ℕ) (hu : entriesUsed 2 n=u)
    (hcap : mass u+x≤10) (hvalid : 0<x ∧ x∉u ∧ mass u+x∉smallForbidden)
    (hmin : ∀ y : Fin x, 0<(y:ℕ) → (y:ℕ)∈u ∨ mass u+(y:ℕ)∈smallForbidden) : entry 2 n=x := by
  obtain ⟨hleg,hleast⟩ := entry_is_least 2 n
  have hx : legal (forbidden 2) (entriesUsed 2 n) x := by
    rw [hu]
    exact ⟨hvalid.1,hvalid.2.1,fun hs => hvalid.2.2 ((initial_forbidden _ hcap).mp hs)⟩
  have hle := hleast _ hx
  apply le_antisymm hle
  by_contra hlt
  have hnew := hleg.2.1
  have hfree := hleg.2.2
  rw [hu] at hnew hfree
  rcases hmin ⟨entry 2 n,by omega⟩ hleg.1 with hu' | hf
  · exact hnew hu'
  · exact hfree ((initial_forbidden _ (by omega)).mpr hf)

private theorem actual_initial_omissions : 1∈omissions 1 ∧ 2∈omissions 2 := by
  have hzero : entriesUsed 2 0=∅ := rfl
  have first : entry 2 0=4 := early_entry 0 4 ∅ hzero (by decide) (by decide) (by decide)
  have hone : entriesUsed 2 1={4} := by change insert (entry 2 0) (entriesUsed 2 0)={4}; rw [first,hzero]; rfl
  have second : entry 2 1=3 := early_entry 1 3 {4} hone (by decide) (by decide) (by decide)
  have htwo : entriesUsed 2 2={3,4} := by change insert (entry 2 1) (entriesUsed 2 1)={3,4}; rw [second,hone]
  have third : entry 2 2=1 := early_entry 2 1 {3,4} htwo (by decide) (by decide) (by decide)
  have hthree : entriesUsed 2 3=Icc 1 (3+1) \ {2} := by
    change insert (entry 2 2) (entriesUsed 2 2)=Icc 1 (3+1) \ {2}
    rw [third,htwo]; decide
  have hb (s : ℕ) (_ : 0<s) (hs : s∈forbidden 2) : ∃ j, s≤tri j ∧ tri j≤s+1 := by
    obtain ⟨j,_,hh | hh⟩ := (previous_for_third s).mp hs
    · exact ⟨j,by omega,by omega⟩
    · exact ⟨j+1,by omega,by omega⟩
  refine ⟨⟨by decide,?_⟩,⟨by decide,?_⟩⟩
  · intro k he
    have hm := (mem_entriesUsed 1 (k+1) 1).mpr ⟨k,by omega,he⟩
    rw [(actual_second_row (k+1)).1,mem_sdiff,mem_singleton] at hm
    exact hm.2 rfl
  · intro k he
    let n := k+3
    have hm := (mem_entriesUsed 2 n 2).mpr ⟨k,by dsimp [n]; omega,he⟩
    have hd := missing_after_init 2 3 2 1 (by decide) (by decide) (by decide) hthree hb n (by dsimp [n]; omega)
    rw [hd.1,mem_sdiff,mem_singleton] at hm
    exact hm.2 rfl

/-- In paper numbering, if the number one below the first entry is missing
in every row from the fourth onward (the corrected range recorded in OEIS),
then every row after the first has exactly one omission. Merely witnessing
the stated omission is enough; no minimality is needed in the hypothesis. -/
theorem uniqueness_of_corrected_first_entry_relation
    (hrelation : ∀ r≥3, entry r 0-1∈omissions r) :
    ∀ r>0, ∃ a, (finite_omissions r).toFinset={a} := by
  let a : ℕ → ℕ := fun k => if k=0 then 1 else if k=1 then 2 else entry (k+1) 0-1
  have first_ge (j : ℕ) : j+1≤entry j 0 := by
    induction j with
    | zero => exact (entry_is_least 0 0).1.1
    | succ j ih =>
      have := strictly_increasing_first_entries (show j<j+1 by omega)
      change entry j 0<entry (j+1) 0 at this
      omega
  have hincr : StrictMono a := by
    apply strictMono_nat_of_lt_succ
    intro k
    by_cases hzero : k=0
    · subst k; decide
    by_cases hone : k=1
    · subst k
      have := first_ge 3
      change 2<entry 3 0-1
      omega
    · have hlt := strictly_increasing_first_entries (show k+1<k+1+1 by omega)
      change entry (k+1) 0<entry (k+1+1) 0 at hlt
      have hp := first_ge (k+1)
      have h1 : k+1≠1 := by omega
      simp only [a,if_neg hzero,if_neg hone,Nat.add_one_ne_zero,if_neg h1,if_false]
      omega
  have hmiss (k : ℕ) : a k∈omissions (k+1) := by
    by_cases hzero : k=0
    · subst k; exact actual_initial_omissions.1
    by_cases hone : k=1
    · subst k; exact actual_initial_omissions.2
    · simp only [a,if_neg hzero,if_neg hone]
      exact hrelation (k+1) (by omega)
  intro r hr
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r≠0)
  exact ⟨a k,all_singletons_of_increasing_omissions a hincr hmiss k⟩

#print axioms singleton_of_omission_above_previous
#print axioms finite_prefix_iff_unique_above
#print axioms all_singletons_of_increasing_omissions
#print axioms strictly_increasing_first_entries
#print axioms uniqueness_of_corrected_first_entry_relation

end GreedyBarrycade

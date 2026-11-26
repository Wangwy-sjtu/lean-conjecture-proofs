import GeometricTranslate
import SidonGrowth
import Mathlib.Tactic.IntervalCases

namespace SmallSumProduct

def InOrbit (c r x : ℚ) : Prop := ∃ k : ℕ, x=c*r^k

private theorem orbit_sidon {p q : ℕ} (hq : 0<q) (hpq : q<p) (hcop : p.Coprime q)
    (c : ℚ) (hc : 0<c) (B : Finset ℚ) (hB : ∀ x∈B, InOrbit c (Base p q) x) : IsSidon B := by
  intro x hx y hy u hu v hv he
  obtain ⟨i,rfl⟩ := hB x hx
  obtain ⟨j,rfl⟩ := hB y hy
  obtain ⟨k,rfl⟩ := hB u hu
  obtain ⟨l,rfl⟩ := hB v hv
  rw [← mul_add, ← mul_add] at he
  rcases pair_power_unique hq hpq hcop (mul_left_cancel₀ hc.ne' he) with h | h
  · exact Or.inl ⟨by rw [h.1],by rw [h.2]⟩
  · exact Or.inr ⟨by rw [h.1],by rw [h.2]⟩

private theorem off_orbit_meet {p q : ℕ} (hq : 0<q) (hpq : q<p) (hcop : p.Coprime q)
    (c : ℚ) (hc : 0<c) (B : Finset ℚ) (hB : ∀ y∈B, InOrbit c (Base p q) y)
    (x : ℚ) (hx : 0<x) (hout : ¬InOrbit c (Base p q) x) :
    (shift x B ∩ sums B B).card≤2 := by
  have outside (j : ℕ) : x/c≠Base p q^j := by
    intro h
    exact hout ⟨j, by rw [div_eq_iff hc.ne'] at h; linarith⟩
  obtain ⟨z,unique⟩ := hit_classes hq hpq hcop (x/c) (div_pos hx hc) outside
  have extract (s : ℚ) (hs : s∈shift x B ∩ sums B B) :
      ∃ k, s=x+c*Base p q^k ∧ Hits (Base p q) (x/c) k := by
    obtain ⟨y,hy,e⟩ := mem_shift.mp (Finset.mem_inter.mp hs).1
    obtain ⟨a,ha,b,hb,e'⟩ := mem_sums.mp (Finset.mem_inter.mp hs).2
    obtain ⟨k,rfl⟩ := hB y hy
    obtain ⟨i,rfl⟩ := hB a ha
    obtain ⟨j,rfl⟩ := hB b hb
    refine ⟨k,e.symm,i,j,?_⟩
    field_simp
    linarith
  by_contra! ht
  obtain ⟨a,b,d,ha,hb,hd,hab,had,hbd⟩ := Finset.two_lt_card_iff.mp ht
  obtain ⟨i,ei,hi⟩ := extract a ha
  obtain ⟨j,ej,hj⟩ := extract b hb
  obtain ⟨k,ek,hk⟩ := extract d hd
  have ij : i≠j := by rintro rfl; exact hab (ei.trans ej.symm)
  have ik : i≠k := by rintro rfl; exact had (ei.trans ek.symm)
  have jk : j≠k := by rintro rfl; exact hbd (ej.trans ek.symm)
  by_cases ei' : (i : ℤ)=z
  · exact jk (unique j k hj hk (by omega) (by omega))
  by_cases ej' : (j : ℤ)=z
  · exact ik (unique i k hi hk ei' (by omega))
  exact ij (unique i j hi hj ei' ej')

/-- A quantitative bound for a rational geometric orbit with arbitrarily spaced
exponents, in a positive rational set with any number of arbitrary off-orbit elements. -/
theorem geometric_growth {p q : ℕ} (hq : 0<q) (hpq : q<p) (hcop : p.Coprime q)
    (c : ℚ) (hc : 0<c) (A B T : Finset ℚ) (hsubB : B⊆A) (hsubT : T⊆A)
    (hB : ∀ x∈B, InOrbit c (Base p q) x)
    (hT : ∀ x∈T, 0<x ∧ ¬InOrbit c (Base p q) x) :
    B.card*(B.card+1)+2*B.card*T.card ≤ 2*(sums A A).card+T.card*(T.card+3) := by
  have h := sumset_growth B T (orbit_sidon hq hpq hcop c hc B hB)
    (fun x h => off_orbit_meet hq hpq hcop c hc B hB x (hT x h).1 (hT x h).2)
  have subset : sums B B ∪ sums T B ⊆ sums A A := by
    intro s hs
    rcases Finset.mem_union.mp hs with hb | ht
    · obtain ⟨a,ha,b,hb,e⟩ := mem_sums.mp hb
      exact mem_sums.mpr ⟨a,hsubB ha,b,hsubB hb,e⟩
    · obtain ⟨a,ha,b,hb,e⟩ := mem_sums.mp ht
      exact mem_sums.mpr ⟨a,hsubT ha,b,hsubB hb,e⟩
  have cc := Finset.card_le_card subset
  omega

/-- Every twelve-element positive rational set with at most 41 distinct sums
meets each rational geometric orbit in at most six points. -/
theorem twelve_geometric_cap {p q : ℕ} (hq : 0<q) (hpq : q<p) (hcop : p.Coprime q)
    (c : ℚ) (hc : 0<c) (A : Finset ℚ) (pos : ∀ x∈A,0<x) (n : A.card=12)
    (small : (sums A A).card≤41) (B : Finset ℚ) (subset : B⊆A)
    (allOn : ∀ x∈B,InOrbit c (Base p q) x) : B.card≤6 := by
  classical
  let U := A.filter (InOrbit c (Base p q))
  let T := A \ U
  have ua : U⊆A := Finset.filter_subset _ _
  have ta : T⊆A := Finset.sdiff_subset
  have bu : B⊆U := fun x hx => Finset.mem_filter.mpr ⟨subset hx,allOn x hx⟩
  have dist : T.card+U.card=12 := (Finset.card_sdiff_add_card_eq_card ua).trans n
  have g := geometric_growth hq hpq hcop c hc A U T ua ta
    (fun _ h => (Finset.mem_filter.mp h).2) (by
      intro x hx
      have hxx := Finset.mem_sdiff.mp hx
      exact ⟨pos _ hxx.1, fun e => hxx.2 (Finset.mem_filter.mpr ⟨hxx.1,e⟩)⟩)
  apply (Finset.card_le_card bu).trans
  let t := U.card
  let m := T.card
  change m+t=12 at dist
  change t*(t+1)+2*t*m ≤ 2*(sums A A).card+m*(m+3) at g
  change t≤6
  by_contra! hh
  have upper : t≤12 := by omega
  rw [show m=12-t by omega] at g
  interval_cases t <;> omega

def products (A : Finset ℚ) : Finset ℚ := A.biUnion fun x => A.image (x * ·)

def exampleTwelve : Finset ℚ := {1,2,3,4,6,8,9,12,16,18,24,32}

/-- The upper-bound set already in Antis et al. attains the new cap of six. -/
theorem example_sharp : exampleTwelve.card=12 ∧ (sums exampleTwelve exampleTwelve).card=41 ∧
    (products exampleTwelve).card=35 ∧ ∃ B : Finset ℚ, B⊆exampleTwelve ∧ B.card=6 ∧
      ∀ x∈B, InOrbit 1 2 x := by
  refine ⟨by decide +kernel,by decide +kernel,by decide +kernel,{1,2,4,8,16,32},
    by decide +kernel,by decide +kernel, ?_⟩
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨0, by norm_num⟩
  · exact ⟨1, by norm_num⟩
  · exact ⟨2, by norm_num⟩
  · exact ⟨3, by norm_num⟩
  · exact ⟨4, by norm_num⟩
  · exact ⟨5, by norm_num⟩

#print axioms rational_power_counts
#print axioms geometric_growth
#print axioms twelve_geometric_cap
#print axioms example_sharp

end SmallSumProduct

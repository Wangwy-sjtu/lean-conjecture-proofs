import GeometricConcentration

namespace SmallSumProduct

/-- The input ratio may be supplied directly as a rational number. -/
theorem twelve_geometric_cap_rat (r : ℚ) (hr : 1<r) (c : ℚ) (hc : 0<c)
    (A : Finset ℚ) (pos : ∀ x∈A,0<x) (n : A.card=12) (small : (sums A A).card≤41)
    (B : Finset ℚ) (incl : B⊆A) (onOrbit : ∀ x∈B,InOrbit c r x) : B.card≤6 := by
  have hn := (Rat.num_pos.mpr (show 0<r by linarith)).le
  have hn' : (r.num.natAbs : ℚ)=(r.num : ℚ) := by
    rw [← Int.cast_natCast, Int.natAbs_of_nonneg hn]
  have eqr : Base r.num.natAbs r.den=r := by
    rw [Base, hn', Rat.num_div_den]
  have greater := hr
  rw [← eqr,Base,lt_div_iff₀ (show (0:ℚ)<r.den by exact_mod_cast r.pos),one_mul] at greater
  exact twelve_geometric_cap r.pos (by exact_mod_cast greater) r.reduced c hc A pos n small B incl
    (by rwa [eqr])

def natSums (A : Finset ℕ) : Finset ℕ := A.biUnion fun a => A.image (a+·)

def asRationals (A : Finset ℕ) : Finset ℚ := A.image (fun x : ℕ => (x : ℚ))

@[simp] theorem cast_card (A : Finset ℕ) : (asRationals A).card=A.card :=
  Finset.card_image_of_injective _ Nat.cast_injective

theorem cast_sums (A : Finset ℕ) : sums (asRationals A) (asRationals A)=asRationals (natSums A) := by
  ext s
  constructor
  · intro h
    obtain ⟨u,hu,v,hv,rfl⟩ := mem_sums.mp h
    unfold asRationals at hu hv
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hv
    exact Finset.mem_image.mpr ⟨a+b,Finset.mem_biUnion.mpr ⟨a,ha,Finset.mem_image.mpr ⟨b,hb,rfl⟩⟩,
      Nat.cast_add _ _⟩
  · intro h
    obtain ⟨_,hs,rfl⟩ := Finset.mem_image.mp h
    obtain ⟨a,ha,hs⟩ := Finset.mem_biUnion.mp hs
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hs
    exact mem_sums.mpr ⟨a,Finset.mem_image.mpr ⟨a,ha,rfl⟩,b,Finset.mem_image.mpr ⟨b,hb,rfl⟩,
      (Nat.cast_add _ _).symm⟩

/-- A form for the original domain of the small sum-product problem, positive integers. -/
theorem twelve_integer_geometric_cap (A : Finset ℕ) (pos : ∀ x∈A,0<x) (n : A.card=12)
    (small : (natSums A).card≤41) (r c : ℚ) (hr : 1<r) (hc : 0<c)
    (B : Finset ℕ) (incl : B⊆A) (onOrbit : ∀ x∈B,InOrbit c r x) : B.card≤6 := by
  rw [← cast_card B]
  apply twelve_geometric_cap_rat r hr c hc (asRationals A)
  · intro x hx
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hx
    exact_mod_cast pos a ha
  · simpa using n
  · simpa [cast_sums] using small
  · exact Finset.image_subset_image incl
  · intro x hx
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hx
    exact onOrbit b hb

#print axioms twelve_geometric_cap_rat
#print axioms twelve_integer_geometric_cap

end SmallSumProduct

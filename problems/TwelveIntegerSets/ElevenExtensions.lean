import TwelveIntegerSets

namespace SmallSumProduct

def bestEleven : Finset ℚ := {1,2,3,4,6,8,9,12,16,18,24}

private def candidates : Finset ℚ :=
  (sums bestEleven bestEleven).biUnion fun s => bestEleven.image (s-·)

private theorem forced_candidate (x : ℚ)
    (small : (sums (insert x bestEleven) (insert x bestEleven)).card≤41) :
    x∈candidates := by
  by_contra hx
  have dis : Disjoint (sums bestEleven bestEleven) (shift x bestEleven) := by
    apply Finset.disjoint_left.mpr
    intro s hs hit
    obtain ⟨b,hb,he⟩ := mem_shift.mp hit
    exact hx (Finset.mem_biUnion.mpr ⟨s,hs,Finset.mem_image.mpr ⟨b,hb,by linarith⟩⟩)
  have size : (sums bestEleven bestEleven ∪ shift x bestEleven).card=45 := by
    rw [Finset.card_union_of_disjoint dis,card_shift]
    decide +kernel
  have includeAll : sums bestEleven bestEleven ∪ shift x bestEleven ⊆
      sums (insert x bestEleven) (insert x bestEleven) := by
    intro s hs
    rcases Finset.mem_union.mp hs with hb | h
    · obtain ⟨a,ha,b,hb,he⟩ := mem_sums.mp hb
      exact mem_sums.mpr ⟨a,Finset.mem_insert_of_mem ha,b,Finset.mem_insert_of_mem hb,he⟩
    · obtain ⟨b,hb,he⟩ := mem_shift.mp h
      exact mem_sums.mpr ⟨x,Finset.mem_insert_self _ _,b,Finset.mem_insert_of_mem hb,he⟩
  have cc := Finset.card_le_card includeAll
  omega

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
private theorem candidate_test : ∀ x∈candidates, 0<x → x∉bestEleven →
    (sums (insert x bestEleven) (insert x bestEleven)).card≤41 →
    (products (insert x bestEleven)).card≤41 → x=32 := by decide +kernel

/-- The sole positive rational extension of the eleven-element extremizer
at the two thresholds 41 is the published example. -/
theorem unique_extension (x : ℚ) (pos : 0<x) (fresh : x∉bestEleven) :
    ((sums (insert x bestEleven) (insert x bestEleven)).card≤41 ∧
     (products (insert x bestEleven)).card≤41) ↔ x=32 := by
  constructor
  · rintro ⟨hs,hp⟩
    exact candidate_test x (forced_candidate x hs) pos fresh hs hp
  · rintro rfl
    decide +kernel

def dilate (c : ℚ) (A : Finset ℚ) : Finset ℚ := A.image (c*·)

private theorem dilate_card (c : ℚ) (hc : c≠0) (A : Finset ℚ) : (dilate c A).card=A.card :=
  Finset.card_image_of_injective _ (fun _ _ h => mul_left_cancel₀ hc h)

private theorem dilate_sums (c : ℚ) (A : Finset ℚ) :
    sums (dilate c A) (dilate c A)=dilate c (sums A A) := by
  ext s
  constructor
  · intro hs
    obtain ⟨a,ha,b,hb,rfl⟩ := mem_sums.mp hs
    unfold dilate at ha hb
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hb
    exact Finset.mem_image.mpr ⟨u+v,mem_sums.mpr ⟨u,hu,v,hv,rfl⟩,mul_add _ _ _⟩
  · intro hs
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨u,hu,v,hv,rfl⟩ := mem_sums.mp ha
    exact mem_sums.mpr ⟨c*u,Finset.mem_image.mpr ⟨u,hu,rfl⟩,c*v,
      Finset.mem_image.mpr ⟨v,hv,rfl⟩,(mul_add _ _ _).symm⟩

private theorem mem_products {A : Finset ℚ} {s : ℚ} :
    s∈products A ↔ ∃ a∈A,∃ b∈A,a*b=s := by simp [products]

private theorem dilate_products (c : ℚ) (A : Finset ℚ) :
    products (dilate c A)=dilate (c*c) (products A) := by
  ext s
  constructor
  · intro hs
    obtain ⟨a,ha,b,hb,rfl⟩ := mem_products.mp hs
    unfold dilate at ha hb
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hb
    exact Finset.mem_image.mpr ⟨u*v,mem_products.mpr ⟨u,hu,v,hv,rfl⟩,by ring⟩
  · intro hs
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨u,hu,v,hv,rfl⟩ := mem_products.mp ha
    exact mem_products.mpr ⟨c*u,Finset.mem_image.mpr ⟨u,hu,rfl⟩,c*v,
      Finset.mem_image.mpr ⟨v,hv,rfl⟩,by ring⟩

/-- Scale invariant form, for an explicit copy of the unique eleven-point
extremal configuration of Antis et al. -/
theorem unique_extension_scaled (c x : ℚ) (hc : 0<c) (hx : 0<x)
    (fresh : x∉dilate c bestEleven) :
    ((sums (insert x (dilate c bestEleven)) (insert x (dilate c bestEleven))).card≤41 ∧
     (products (insert x (dilate c bestEleven))).card≤41) ↔ x=c*32 := by
  have hmul : c*(x/c)=x := by field_simp
  have s : insert x (dilate c bestEleven)=dilate c (insert (x/c) bestEleven) := by
    simp [dilate,hmul]
  have f : x/c∉bestEleven := fun h => fresh (Finset.mem_image.mpr ⟨x/c,h,hmul⟩)
  rw [s,dilate_sums,dilate_products,dilate_card c hc.ne',dilate_card _ (mul_ne_zero hc.ne' hc.ne'),
    unique_extension _ (div_pos hx hc) f]
  rw [div_eq_iff hc.ne',mul_comm (32:ℚ)]

#print axioms unique_extension
#print axioms unique_extension_scaled

end SmallSumProduct

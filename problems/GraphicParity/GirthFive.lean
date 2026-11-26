import GraphicParity

/-! A quantitative gate bound for graphs without triangles or four-cycles. -/
open GraphicParity Finset
open scoped symmDiff
namespace GirthFive
variable {V : Type} [DecidableEq V]

/-- The XOR identifies an unordered pair of distinct requested terms. -/
def UniqueDifferences (T : Finset (Term V)) : Prop :=
  ∀ a∈T, ∀ b∈T, ∀ c∈T, ∀ d∈T, a ≠ b → c ≠ d →
    a ∆ b = c ∆ d → a = c ∨ a = d

private noncomputable def differences (X S : Finset (Term V)) : Finset (Term V) := by
  classical
  exact X.filter (fun w => ∃ a∈S, ∃ b∈S, a≠b ∧ a ∆ b=w)

private theorem differences_mono (X : Finset (Term V)) {S R : Finset (Term V)} (sub : S⊆R) :
    differences X S ⊆ differences X R := by
  classical
  intro w hw
  obtain ⟨x,a,ha,b,hb,ab,eq⟩ := mem_filter.mp hw
  exact mem_filter.mpr ⟨x,a,sub ha,b,sub hb,ab,eq⟩

private theorem new_difference (T X S : Finset (Term V)) (unique : UniqueDifferences T)
    (sub : S⊆T) (w a : Term V) (fresh : w∉S) (wt : w∈T) (ha : a∈S) (extra : w ∆ a∈X) :
    (differences X S).card < (differences X (insert w S)).card := by
  classical
  apply card_lt_card
  apply (ssubset_iff_of_subset (differences_mono X (subset_insert w S))).mpr
  refine ⟨w ∆ a,?_,?_⟩
  · exact mem_filter.mpr ⟨extra,w,mem_insert_self ..,a,mem_insert_of_mem ha,
      fun h => fresh (h ▸ ha),rfl⟩
  · intro old
    obtain ⟨_,c,hc,d,hd,diff,eq⟩ := mem_filter.mp old
    have wa : w ≠ a := fun h => fresh (h ▸ ha)
    rcases unique w wt a (sub ha) c (sub hc) d (sub hd) wa diff eq.symm with h | h
    · exact fresh (h ▸ hc)
    · exact fresh (h ▸ hd)

/-- Mark a wire when its last gate introduced a previously unvisited request.
A gate either clears an old mark, introduces a new mark, or joins consecutive
marks using a distinct exceptional control. -/
private theorem scan (T X : Finset (Term V)) (simple : SimpleEdges T)
    (free : SumFree T) (unique : UniqueDifferences T) (s : State V) (gs : List (Gate V))
    (seen : Finset (Term V)) (hot : Finset V) (sub : seen⊆T)
    (marked : ∀ v∈hot,s v∈seen)
    (past : ∀ v, (s v).card%2=0 → s v∉T → s v∈X)
    (future : ∀ w∈outputs s gs, w.card%2=0 → w∉T → w∈X)
    (endState : ∀ v, run s gs v ∉ T) :
    ∃ final : Finset (Term V), seen⊆final ∧
      (∀ w∈outputs s gs,w∈T → w∈final) ∧
      2*final.card + (differences X seen).card + hot.card ≤ gs.length + X.card + 2*seen.card := by
  classical
  induction gs generalizing s seen hot with
  | nil =>
    have none : hot=∅ := eq_empty_iff_forall_notMem.mpr
      (fun v h => endState v (sub (marked v h)))
    have cap : (differences X seen).card≤X.card := card_le_card (filter_subset ..)
    exact ⟨seen,Subset.rfl,by simp [outputs],by simp [none]; omega⟩
  | cons g gs ih =>
    let w := output s g
    let u := applyGate s g
    have after (v : V) : (u v).card%2=0 → u v∉T → u v∈X := by
      by_cases eq : v=g.target
      · subst v; simpa [u,applyGate] using future w List.mem_cons_self
      · simpa [u,applyGate,eq] using past v
    have later (z) (hz : z∈outputs u gs) := future z (List.mem_cons_of_mem _ hz)
    by_cases new : w∈T ∧ w∉seen
    · let R := insert w seen
      let J := insert g.target hot
      have subR : R⊆T := insert_subset new.1 sub
      have markR (v) (h : v∈J) : u v∈R := by
        by_cases eq : v=g.target
        · subst v; simp [u,applyGate,R,w]
        · have old : v∈hot := (mem_insert.mp h).resolve_left eq
          have mem : s v∈R := mem_insert_of_mem (marked v old)
          simpa [u,applyGate,eq] using mem
      obtain ⟨final,rf,vis,bound⟩ := ih u R J subR markR after later endState
      have eqR : R.card=seen.card+1 := card_insert_of_notMem new.2
      have cost : (differences X seen).card + hot.card + 1 ≤ (differences X R).card + J.card := by
        by_cases active : g.target ∈ hot
        · have ht := marked g.target active
          have ctrl : w ∆ s g.target=s g.control := by
            change (s g.target ∆ s g.control) ∆ s g.target=_
            rw [symmDiff_right_comm,symmDiff_self,bot_symmDiff]
          have extra : s g.control∈X := by
            apply past
            · have par := card_xor w (s g.target)
              rw [ctrl,simple w new.1,simple _ (sub ht)] at par
              exact par
            · rw [← ctrl]; exact free w new.1 _ (sub ht)
          have grow := new_difference T X seen unique sub w (s g.target) new.2 new.1 ht (ctrl ▸ extra)
          have stay : J.card=hot.card := card_insert_of_mem active
          dsimp [R] at *; omega
        · have grow := card_le_card (differences_mono X (subset_insert w seen))
          have plus : J.card=hot.card+1 := card_insert_of_notMem active
          dsimp [R] at *; omega
      refine ⟨final,(subset_insert w seen).trans rf,?_,?_⟩
      · intro z hz zt
        rcases List.mem_cons.mp hz with rfl | h
        · exact rf (mem_insert_self ..)
        · exact vis z h zt
      · simp only [List.length_cons]; omega
    · let J := hot.erase g.target
      have markJ (v) (h : v∈J) : u v∈seen := by
        obtain ⟨neq,hv⟩ := mem_erase.mp h
        simpa [u,applyGate,neq] using marked v hv
      obtain ⟨final,sf,vis,bound⟩ := ih u seen J sub markJ after later endState
      have size : hot.card ≤ J.card+1 := by
        by_cases h : g.target∈hot
        · exact (card_erase_add_one h).symm.le
        · simp [J,erase_eq_of_notMem h]
      refine ⟨final,sf,?_,?_⟩
      · intro z hz zt
        rcases List.mem_cons.mp hz with rfl | h
        · exact sf (by by_contra hn; exact new ⟨zt,hn⟩)
        · exact vis z h zt
      · simp only [List.length_cons]; omega

/-- The bound counts all CNOT gates, with every input restored. -/
theorem unique_differences_lower [Fintype V] (r : V) (T : Finset (Term V)) (gs : List (Gate V))
    (connected : ∀ v, ConnectedTo T r v) (simple : SimpleEdges T)
    (free : SumFree T) (unique : UniqueDifferences T) (net : Network T gs) :
    3*T.card + (Fintype.card V-1) ≤ 2*gs.length := by
  let X := exceptionalEven T gs
  have ends (v : V) : run initial gs v ∉ T := by
    rw [net.1]; intro ht; have := simple _ ht
    simp [initial] at this
  obtain ⟨final,_,covers,charge⟩ := scan T X simple free unique initial gs ∅ ∅
    (empty_subset _) (by simp) (by simp [initial]) (fun _ => mem_exceptionalEven T gs) ends
  have total := card_le_card (show T ⊆ final from fun _ h => covers _ (net.2 _ h) h)
  have budget := exceptional_even_budget r T gs connected simple net
  change T.card + X.card + (Fintype.card V-1) ≤ gs.length at budget
  simp only [card_empty] at charge
  omega

#print axioms unique_differences_lower

/-- Two distinct vertices have at most one common neighbor. On a simple
graph this is equivalent to excluding a cycle of length four. -/
def FourCycleFree (T : Finset (Term V)) : Prop :=
  ∀ p q x z : V, p≠q → pair x p∈T → pair x q∈T → pair z p∈T → pair z q∈T → x=z

private theorem edge_at {e : Term V} {x : V} (size : e.card=2) (hx : x∈e) :
    ∃ y : V, x≠y ∧ e=pair x y := by
  obtain ⟨a,b,ab,rfl⟩ := card_eq_two.mp size
  rcases mem_insert.mp hx with rfl | h
  · exact ⟨b,ab,(pair_of_ne ab).symm⟩
  · obtain rfl := mem_singleton.mp h
    exact ⟨a,ab.symm,(Finset.pair_comm a x).trans (pair_of_ne ab.symm).symm⟩

private theorem two_edges_delta (x p q : V) : pair x p ∆ pair x q = pair p q := by
  rw [show pair x p=pair p x from symmDiff_comm ..,pair_comp]

private theorem swap_terms {a b c d : Term V} (h : a ∆ b = c ∆ d) : a ∆ c = b ∆ d := by
  ext v
  have eq : v∈a ∆ b ↔ v∈c ∆ d := h ▸ Iff.rfl
  simp only [mem_symmDiff] at eq ⊢
  tauto

private theorem adjacent_pair_unique (T : Finset (Term V)) (simple : SimpleEdges T)
    (square : FourCycleFree T) {e f g h : Term V} (et : e∈T) (ft : f∈T)
    (gt : g∈T) (ht : h∈T) {x : V} (xe : x∈e) (xf : x∈f) (ef : e≠f)
    (eq : e ∆ f = g ∆ h) : e=g ∨ e=h := by
  obtain ⟨p,_,pe⟩ := edge_at (simple e et) xe
  obtain ⟨q,_,qf⟩ := edge_at (simple f ft) xf
  have pq : p≠q := by rintro rfl; exact ef (pe.trans qf.symm)
  have difference : g ∆ h = pair p q := eq.symm.trans (by rw [pe,qf,two_edges_delta])
  have overlap : ∃ z, z∈g ∧ z∈h := by
    by_contra! absent
    have dis : Disjoint g h := disjoint_left.mpr absent
    have sz : (g ∆ h).card=2 := by simp [difference,pair_of_ne pq,pq]
    rw [Finset.symmDiff_eq_union dis,card_union_of_disjoint dis,simple g gt,simple h ht] at sz
    contradiction
  obtain ⟨z,zg,zh⟩ := overlap
  obtain ⟨i,_,ig⟩ := edge_at (simple g gt) zg
  obtain ⟨j,_,jh⟩ := edge_at (simple h ht) zh
  have terms : pair i j = pair p q := by
    simpa only [ig,jh,two_edges_delta] using difference
  have ij : i≠j := by
    intro same
    have s := congrArg Finset.card terms
    rw [same,pair_of_ne pq] at s
    simp [pair,pq] at s
  rw [pair_of_ne ij,pair_of_ne pq] at terms
  have sets := congrArg (fun t : Finset V => (t : Set V)) terms
  simp only [coe_pair,Set.pair_eq_pair_iff] at sets
  rw [pe] at et
  rw [qf] at ft
  rw [ig] at gt
  rw [jh] at ht
  rcases sets with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · have sx := square _ _ x z pq et ft gt ht
    exact Or.inl (by rw [pe,ig,sx])
  · have sx := square _ _ x z pq et ft ht gt
    exact Or.inr (by rw [pe,jh,sx])

theorem unique_of_four_cycle_free (T : Finset (Term V)) (simple : SimpleEdges T)
    (square : FourCycleFree T) : UniqueDifferences T := by
  intro e et f ft c ct d dt ef _ eq
  by_cases ec : e=c
  · exact Or.inl ec
  by_cases ed : e=d
  · exact Or.inr ed
  obtain ⟨x,xe⟩ := card_pos.mp (show 0<e.card by rw [simple e et]; decide)
  by_cases xf : x∈f
  · exact adjacent_pair_unique T simple square et ft ct dt xe xf ef eq
  by_cases xc : x∈c
  · have other := adjacent_pair_unique T simple square et ct ft dt xe xc ec (swap_terms eq)
    exact Or.inr (other.resolve_left ef)
  · have has : x∈e ∆ f := mem_symmDiff.mpr (Or.inl ⟨xe,xf⟩)
    rw [eq] at has
    have xd : x∈d := ((mem_symmDiff.mp has).resolve_left (fun h => xc h.1)).1
    have eq' : e ∆ f=d ∆ c := eq.trans (symmDiff_comm c d)
    have other := adjacent_pair_unique T simple square et dt ft ct xe xd ed (swap_terms eq')
    exact Or.inl (other.resolve_left ef)

/-- On every connected simple graph of girth at least five, twice the
length of any parity network is at least 3|E| + |V| − 1. -/
theorem girth_five_lower [Fintype V] (r : V) (T : Finset (Term V)) (gs : List (Gate V))
    (connected : ∀ v, ConnectedTo T r v) (simple : SimpleEdges T) (tri : TriangleFree T)
    (square : FourCycleFree T) (net : Network T gs) :
    3*T.card + (Fintype.card V-1) ≤ 2*gs.length :=
  unique_differences_lower r T gs connected simple (sumfree_of_triangleFree T simple tri)
    (unique_of_four_cycle_free T simple square) net

#print axioms girth_five_lower

end GirthFive

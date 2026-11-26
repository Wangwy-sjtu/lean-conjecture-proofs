import GraphicParity
import Mathlib.Data.Finset.Prod

/-! Exact CNOT complexity of the complete bipartite graphs on their input wires. -/
open GraphicParity Finset
open scoped symmDiff
namespace BipartiteOptimal

variable {V : Type} [DecidableEq V]

def edgeSet (A B : Finset V) : Finset (Term V) :=
  (A ×ˢ B).image (fun p => pair p.1 p.2)

omit [DecidableEq V] in
private theorem across {A B : Finset V} (dis : Disjoint A B) {x y : V} (hx : x∈A)
    (hy : y∈B) : x≠y := fun eq => (Finset.disjoint_left.mp dis) hx (eq.symm ▸ hy)

private theorem member {A B : Finset V} {x y : V} (hx : x∈A) (hy : y∈B) :
    pair x y∈edgeSet A B := mem_image.mpr ⟨(x,y),mem_product.mpr ⟨hx,hy⟩,rfl⟩

theorem edge_count (A B : Finset V) (dis : Disjoint A B) : (edgeSet A B).card=A.card*B.card := by
  unfold edgeSet
  rw [card_image_of_injOn,card_product]
  intro p hp q hq eq
  obtain ⟨pa,pb⟩ := mem_product.mp hp
  obtain ⟨qa,qb⟩ := mem_product.mp hq
  change pair p.1 p.2 = pair q.1 q.2 at eq
  have h : p.1 ∈ pair q.1 q.2 := eq ▸ (by simp [pair_of_ne (across dis pa pb)])
  rw [pair_of_ne (across dis qa qb)] at h
  have first : p.1=q.1 := (mem_insert.mp h).resolve_right
    (fun last => across dis pa qb (mem_singleton.mp last))
  rw [first] at eq
  exact Prod.ext first (pair_same_root eq)

private theorem edge_simple (A B : Finset V) (dis : Disjoint A B) : SimpleEdges (edgeSet A B) := by
  intro w hw
  obtain ⟨p,hp,rfl⟩ := mem_image.mp hw
  obtain ⟨pa,pb⟩ := mem_product.mp hp
  simp [pair_of_ne (across dis pa pb),across dis pa pb]

private theorem edge_free (A B : Finset V) (dis : Disjoint A B) : SumFree (edgeSet A B) := by
  have one (e : Term V) (he : e∈edgeSet A B) : (e∩A).card=1 := by
    obtain ⟨⟨x,y⟩,hp,rfl⟩ := mem_image.mp he
    obtain ⟨hx,hy⟩ := mem_product.mp hp
    have no : y∉A := fun h => Finset.disjoint_left.mp dis h hy
    have eq : ({x,y} : Finset V)∩A={x} := by
      ext z
      simp only [mem_inter,mem_insert,mem_singleton]
      constructor
      · rintro ⟨h,hz⟩
        exact h.resolve_right (fun e => no (e ▸ hz))
      · rintro rfl; exact ⟨Or.inl rfl,hx⟩
    change ((pair x y)∩A).card=_
    rw [pair_of_ne (across dis hx hy),eq,card_singleton]
  intro e he f hf has
  have parity := card_xor (e∩A) (f∩A)
  rw [← inter_xor,one _ has,one e he,one f hf] at parity
  contradiction

private theorem surviving (A B P : Finset V) (dis : Disjoint A B) :
    (A \ P).card * (B \ P).card ≤
      ((edgeSet A B).filter (fun e => Disjoint e P)).card := by
  have smaller : Disjoint (A \ P) (B \ P) := dis.mono sdiff_subset sdiff_subset
  rw [← edge_count _ _ smaller]
  apply card_le_card
  intro e he
  obtain ⟨⟨x,y⟩,hp,rfl⟩ := mem_image.mp he
  obtain ⟨hx,hy⟩ := mem_product.mp hp
  obtain ⟨ax,px⟩ := mem_sdiff.mp hx
  obtain ⟨by',py⟩ := mem_sdiff.mp hy
  apply mem_filter.mpr
  refine ⟨member ax by',?_⟩
  change Disjoint (pair x y) P
  rw [pair_of_ne (across dis ax by')]
  simp [px,py]

private theorem vertex_bound (A B P : Finset V) (dis : Disjoint A B)
    (ab : A.card≤B.card) (qsmall : P.card+2≤A.card) :
    B.card + 2*A.card-2 ≤ P.card + (A \ P).card * (B \ P).card := by
  let a := A.card
  let b := B.card
  let q := P.card
  let x := (A∩P).card
  let y := (B∩P).card
  let a' := (A \ P).card
  let b' := (B \ P).card
  have eqA : a'+x=a := card_sdiff_add_card_inter A P
  have eqB : b'+y=b := card_sdiff_add_card_inter B P
  have xy : x+y≤q := by
    have ds : Disjoint (A∩P) (B∩P) := dis.mono inter_subset_left inter_subset_left
    have ub : (A∩P) ∪ (B∩P) ⊆ P := union_subset inter_subset_right inter_subset_right
    have h := card_le_card ub
    rwa [card_union_of_disjoint ds] at h
  change a≤b at ab
  change q+2≤a at qsmall
  change b+2*a-2≤q+a'*b'
  have aw : a'≤b := by omega
  have loss : a'*y + x*b ≤ q*b := calc
    a'*y+x*b ≤ b*y+x*b := Nat.add_le_add_right (Nat.mul_le_mul_right y aw) _
    _ = (x+y)*b := by rw [Nat.add_mul,Nat.mul_comm b y,Nat.add_comm]
    _ ≤ q*b := Nat.mul_le_mul_right b xy
  have mul : (a-q)*b ≤ a'*b' := by
    have eq : (a-q)*b + q*b = a'*b'+a'*y+x*b := calc
      _ = a*b := by rw [← Nat.add_mul,Nat.sub_add_cancel (by omega)]
      _ = (a'+x)*b := by rw [eqA]
      _ = a'*(b'+y)+x*b := by rw [eqB,Nat.add_mul]
      _ = _ := by rw [Nat.mul_add]
    omega
  let d := a-q-2
  have de : a-q=d+2 := by dsimp [d]; omega
  have two : 2≤b := by omega
  have h := Nat.mul_le_mul_left d two
  rw [de,Nat.add_mul] at mul
  dsimp [d] at h mul
  omega

theorem bipartite_lower_from [Fintype V] (A B : Finset V) (dis : Disjoint A B)
    (apos : 0<A.card) (ab : A.card≤B.card)
    (s : State V) (gs : List (Gate V)) (initialEven : ∀ v, (s v).card%2=0 → s v=∅)
    (restored : run s gs = s) (covered : ∀ w∈edgeSet A B,w∈outputs s gs) :
    A.card*B.card+B.card+2*A.card-2 ≤ gs.length := by
  obtain ⟨r,hr⟩ := card_pos.mp apos
  obtain ⟨t,ht⟩ := card_pos.mp (apos.trans_le ab)
  have con (v : V) (h : v∈A∪B) : ConnectedTo (edgeSet A B) r v := by
    rcases mem_union.mp h with ha | hb
    · have edge : pair t v∈edgeSet A B := by
        simpa only [pair,symmDiff_comm ({v}:Finset V) {t}] using member ha ht
      exact .edge (.edge .root (member hr ht)) edge
    · exact .edge .root (member hr hb)
  obtain ⟨P,bound⟩ := sumfree_pivot_bound_from (A∪B) r (mem_union_left _ hr)
    (edgeSet A B) s gs con (edge_simple A B dis) (edge_free A B dis) initialEven restored covered
  rw [edge_count A B dis,card_union_of_disjoint dis] at bound
  by_cases qsmall : P.card+2≤A.card
  · have byP := vertex_bound A B P dis ab qsmall
    have intact := surviving A B P dis
    omega
  · omega

theorem complete_bipartite_lower [Fintype V] (A B : Finset V) (dis : Disjoint A B)
    (_all : A∪B=univ) (apos : 0<A.card) (ab : A.card≤B.card)
    (gs : List (Gate V)) (net : Network (edgeSet A B) gs) :
    A.card*B.card+B.card+2*A.card-2 ≤ gs.length := by
  apply bipartite_lower_from A B dis apos ab initial gs (by simp [initial]) net.1 net.2

#print axioms complete_bipartite_lower

/-- Apply a fixed control once to each member of a set of distinct targets.
The equation records the complete final state and all produced parities. -/
private theorem fan (c : V) (B : Finset V) (hc : c∉B) (s : State V) :
    ∃ gs : List (Gate V), gs.length=B.card ∧
      run s gs=(fun x => if x∈B then s x ∆ s c else s x) ∧
      ∀ x∈B,s x ∆ s c ∈ outputs s gs := by
  induction B using Finset.induction_on generalizing s with
  | empty => exact ⟨[],rfl,by simp [run],by simp⟩
  | @insert b B fresh ih =>
    have cb : c≠b := fun e => hc (e ▸ mem_insert_self b B)
    let g : Gate V := ⟨c,b,cb⟩
    let u := applyGate s g
    have uc : u c=s c := by simp [u,applyGate,g,cb]
    have ub : u b=s b ∆ s c := by simp [u,applyGate,g,output]
    have same (x : V) (h : x≠b) : u x=s x := by simp [u,applyGate,g,h]
    obtain ⟨gs,sz,endState,out⟩ := ih (fun h => hc (mem_insert_of_mem h)) u
    refine ⟨g::gs,by simp [sz,card_insert_of_notMem fresh],?_,?_⟩
    · change run u gs=_
      rw [endState]
      funext x
      by_cases xb : x=b
      · subst x; simp [fresh,ub]
      · simp [xb,same x xb,uc]
    · intro x hx
      rcases mem_insert.mp hx with rfl | later
      · exact List.mem_cons_self
      · have xb : x≠b := fun eq => fresh (eq ▸ later)
        exact List.mem_cons_of_mem _ (by simpa [same x xb,uc] using out x later)

private def rowState (h : V) (B : Finset V) (x : V) : Term V :=
  if x∈B then pair h x else {x}

private theorem start_row (h : V) (B : Finset V) (hh : h∉B) :
    ∃ gs : List (Gate V), gs.length=B.card ∧ run initial gs=rowState h B ∧
      ∀ x∈B,pair h x∈outputs initial gs := by
  obtain ⟨gs,len,state,visited⟩ := fan h B hh initial
  refine ⟨gs,len,?_,?_⟩
  · rw [state]; funext x
    by_cases hx : x∈B <;> simp [rowState,hx,initial,pair,symmDiff_comm]
  · intro x hx
    simpa only [initial,pair,symmDiff_comm ({x}:Finset V) {h}] using visited x hx

private theorem end_row (h : V) (B : Finset V) (hh : h∉B) :
    ∃ gs : List (Gate V), gs.length=B.card ∧ run (rowState h B) gs=initial := by
  obtain ⟨gs,len,state,_⟩ := fan h B hh (rowState h B)
  refine ⟨gs,len,?_⟩
  rw [state]; funext x
  by_cases hx : x∈B <;> simp [rowState,hx,hh,initial,pair,symmDiff_comm]

/-- Moving between consecutive hubs costs one gate per leaf plus two gates
to compute and uncompute the difference of the hubs. -/
private theorem move_row (h k : V) (B : Finset V) (different : h≠k) (hh : h∉B) (hk : k∉B) :
    ∃ gs : List (Gate V), gs.length=B.card+2 ∧ run (rowState h B) gs=rowState k B ∧
      ∀ x∈B,pair k x∈outputs (rowState h B) gs := by
  let s := rowState h B
  let g : Gate V := ⟨h,k,different⟩
  let u := applyGate s g
  have eqOut : output s g = pair h k := by
    simp [output,g,s,rowState,hh,hk,pair,symmDiff_comm]
  have uK : u k = pair h k := by
    change Function.update s k (output s g) k = _
    rw [Function.update_self,eqOut]
  have other (x : V) (xk : x≠k) : u x = s x := by simp [u,applyGate,g,xk]
  have leaf (x : V) (hx : x∈B) : u x ∆ u k = pair k x := by
    have xk : x≠k := by rintro rfl; exact hk hx
    rw [other x xk,uK]
    simp [s,rowState,hx,pair,symmDiff_symmDiff_symmDiff_comm,symmDiff_comm]
  obtain ⟨gs,sz,done,out⟩ := fan k B hk u
  let state := run u gs
  have atK : state k = pair h k := by simp [state,done,hk,uK]
  have atH : state h = {h} := by simp [state,done,hh,other h different,s,rowState]
  have restored : applyGate state g = rowState k B := by
    have final : output state g = {k} := by
      change state k ∆ state h=_
      rw [atK,atH]
      simp [pair,symmDiff_comm]
    funext x
    by_cases xk : x=k
    · subst x; simpa [applyGate,g,hk,rowState] using final
    · by_cases hx : x∈B
      · simpa [applyGate,g,xk,state,done,hx,rowState] using leaf x hx
      · simp [applyGate,g,xk,state,done,hx,rowState,other x xk,s]
  refine ⟨g::(gs++[g]),by simp [sz],?_,?_⟩
  · change run u (gs++[g])=rowState k B
    rw [run_append]; exact restored
  · intro x hx
    apply List.mem_cons_of_mem
    rw [outputs_append]
    exact List.mem_append_left _ ((leaf x hx) ▸ out x hx)

private theorem visit_hubs (h : V) (A B : Finset V) (hh : h∉B) (fresh : h∉A)
    (ds : Disjoint A B) :
    ∃ gs : List (Gate V), ∃ last : V, last∉B ∧ gs.length=A.card*(B.card+2) ∧
      run (rowState h B) gs=rowState last B ∧
      ∀ k∈A,∀ x∈B,pair k x∈outputs (rowState h B) gs := by
  induction A using Finset.induction_on generalizing h with
  | empty => exact ⟨[],h,hh,by simp,rfl,by simp⟩
  | @insert k A outside ih =>
    have diff : h≠k := by rintro rfl; exact fresh (mem_insert_self ..)
    have kB : k∉B := Finset.disjoint_left.mp ds (mem_insert_self ..)
    have ds' : Disjoint A B := ds.mono_left (subset_insert ..)
    obtain ⟨steps,size,after,seen⟩ := move_row h k B diff hh kB
    obtain ⟨more,last,lastB,rest,finish,remaining⟩ := ih k kB outside ds'
    refine ⟨steps++more,last,lastB,?_,?_,?_⟩
    · simp [size,rest,card_insert_of_notMem outside,Nat.succ_mul,Nat.add_comm]
    · rw [run_append,after,finish]
    · intro a ha x hx
      rw [outputs_append,after]
      rcases mem_insert.mp ha with rfl | ha
      · exact List.mem_append_left _ (seen x hx)
      · exact List.mem_append_right _ (remaining a ha x hx)

theorem complete_bipartite_upper (A B : Finset V) (ds : Disjoint A B) (apos : 0<A.card) :
    ∃ gs : List (Gate V), Network (edgeSet A B) gs ∧
       gs.length=A.card*B.card+B.card+2*A.card-2 := by
  obtain ⟨r,hr⟩ := card_pos.mp apos
  have rb := Finset.disjoint_left.mp ds hr
  obtain ⟨first,u,atR,seenR⟩ := start_row r B rb
  obtain ⟨middle,last,lb,len,atLast,seenOthers⟩ :=
    visit_hubs r (A.erase r) B rb (by simp) (ds.mono_left (erase_subset ..))
  obtain ⟨final,w,finish⟩ := end_row last B lb
  refine ⟨first++middle++final,⟨?_,?_⟩,?_⟩
  · rw [run_append,run_append,atR,atLast,finish]
  · intro e he
    obtain ⟨⟨h,x⟩,hp,rfl⟩ := mem_image.mp he
    obtain ⟨ha,hx⟩ := mem_product.mp hp
    rw [outputs_append,outputs_append,atR]
    apply List.mem_append_left
    by_cases eq : h=r
    · subst h; exact List.mem_append_left _ (seenR x hx)
    · exact List.mem_append_right _ (seenOthers h (mem_erase.mpr ⟨eq,ha⟩) x hx)
  · have actual := card_erase_add_one hr
    rw [List.length_append,List.length_append,u,w,len]
    rw [Nat.mul_add,← actual,Nat.succ_mul]
    omega

/-- Exact optimum on every nonempty complete bipartite graph, writing
the smaller part first. The circuit uses no auxiliary wires. -/
theorem complete_bipartite_optimum [Fintype V] (A B : Finset V) (ds : Disjoint A B)
    (all : A∪B=univ) (apos : 0<A.card) (ab : A.card≤B.card) :
    IsLeast {k | ∃ gs : List (Gate V), Network (edgeSet A B) gs ∧ gs.length=k}
      (A.card*B.card+B.card+2*A.card-2) := by
  refine ⟨complete_bipartite_upper A B ds apos,?_⟩
  rintro k ⟨gs,net,rfl⟩
  exact complete_bipartite_lower A B ds all apos ab gs net

#print axioms complete_bipartite_optimum

/-- Wires in I initially hold separate inputs. All other wires start at zero. -/
def inputState (I : Finset V) (x : V) : Term V := ({x} : Finset V) ∩ I

private def restrictState (I : Finset V) (s : State V) (x : V) : Term V := s x ∩ I

private theorem restrict_gate (I : Finset V) (s : State V) (g : Gate V) :
    applyGate (restrictState I s) g = restrictState I (applyGate s g) := by
  funext x
  by_cases h : x = g.target
  · subst x
    simpa [applyGate,restrictState,output] using (inter_xor (s g.target) (s g.control) I).symm
  · simp [applyGate,restrictState,h]

private theorem run_restrict (I : Finset V) (s : State V) (gs : List (Gate V)) :
    run (restrictState I s) gs = restrictState I (run s gs) := by
  induction gs generalizing s with
  | nil => rfl
  | cons g gs ih => simp only [run,restrict_gate,ih]

private theorem outputs_restrict (I : Finset V) (s : State V) (gs : List (Gate V)) :
    outputs (restrictState I s) gs = (outputs s gs).map (fun t => t∩I) := by
  induction gs generalizing s with
  | nil => rfl
  | cons g gs ih =>
    simp only [outputs,List.map_cons,restrict_gate,ih,output,restrictState,inter_xor]

/-- Exact gate count allowing arbitrarily many clean and borrowed auxiliaries.
Members of A and B are data wires. Other members of I are borrowed inputs.
Every wire outside I starts at zero. All wires return to their initial values. -/
theorem complete_bipartite_ancilla_optimum [Fintype V] (A B I : Finset V)
    (ds : Disjoint A B) (data : A∪B⊆I) (apos : 0<A.card) (ab : A.card≤B.card) :
    IsLeast {k | ∃ gs : List (Gate V), run (inputState I) gs = inputState I ∧
      (∀ w∈edgeSet A B, w∈outputs (inputState I) gs) ∧ gs.length=k}
      (A.card*B.card+B.card+2*A.card-2) := by
  constructor
  · obtain ⟨gs,⟨restored,covered⟩,size⟩ := complete_bipartite_upper A B ds apos
    refine ⟨gs,?_,?_,size⟩
    · change run (restrictState I initial) gs = restrictState I initial
      rw [run_restrict,restored]
    · intro w hw
      have subset : w⊆I := by
        obtain ⟨⟨h,x⟩,hp,rfl⟩ := mem_image.mp hw
        obtain ⟨ha,xb⟩ := mem_product.mp hp
        rw [pair_of_ne (across ds ha xb)]
        exact insert_subset (data (mem_union_left _ ha))
          (singleton_subset_iff.mpr (data (mem_union_right _ xb)))
      change w∈outputs (restrictState I initial) gs
      rw [outputs_restrict]
      exact List.mem_map.mpr ⟨w,covered w hw,inter_eq_left.mpr subset⟩
  · rintro k ⟨gs,restored,covered,rfl⟩
    apply bipartite_lower_from A B ds apos ab (inputState I) gs _ restored covered
    intro v hv
    by_cases mem : v∈I <;> simp [inputState,mem] at hv ⊢

#print axioms complete_bipartite_ancilla_optimum

end BipartiteOptimal

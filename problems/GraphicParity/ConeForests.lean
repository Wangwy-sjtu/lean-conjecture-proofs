import GraphicParity

/-! Perfect graphic parity networks for cones over unions of two forests. -/
open GraphicParity Finset
open scoped symmDiff
namespace ConeForests
variable {V : Type} [DecidableEq V]

/-- The usual leaf construction of a finite (possibly disconnected) forest. -/
inductive Forest : Finset (Term V) → Prop
  | empty : Forest ∅
  | leaf {F : Finset (Term V)} (old : Forest F) (v w : V) (diff : v≠w)
      (unused : ∀ e∈F,v∉e) : Forest (insert (pair v w) F)

def TwoForests (H : Finset (Term V)) : Prop :=
  ∃ F G : Finset (Term V), Disjoint F G ∧ H=F∪G ∧ Forest F ∧ Forest G

def Supported (H : Finset (Term V)) (D : Finset V) : Prop := ∀ e∈H, e⊆D

def spokes (o : V) (D : Finset V) : Finset (Term V) := D.image (pair o)

def cone (o : V) (D : Finset V) (H : Finset (Term V)) := spokes o D ∪ H

private def value (o : V) (b : Bool) (x : V) : Term V := if b then pair o x else {x}

private def switch (o : V) (D : Finset V) (b : Bool) (s : State V) (x : V) : Term V :=
  if x∈D then value o b x else s x

/-- The local assertions in Cao et al.'s questions (C1) and (C3). -/
def KeepsInput (v : V) (e : Term V) : Prop := v∈e ∧ (e.card=1 ∨ e.card=2)

private theorem value_keeps {o x : V} (ne : o≠x) (b : Bool) : KeepsInput x (value o b x) := by
  cases b <;> simp [KeepsInput,value,pair_of_ne ne,ne]

private theorem toggle (o x : V) (b : Bool) : value o b x ∆ {o} = value o (!b) x := by
  cases b <;> simp [value,pair,symmDiff_comm]

private theorem same_pair (o x y : V) (b : Bool) : value o b x ∆ value o b y=pair x y := by
  cases b <;> simp [value,pair,symmDiff_symmDiff_symmDiff_comm]

private theorem finish_pair (o x y : V) (b : Bool) : pair x y ∆ value o b y=value o b x := by
  rw [← same_pair o x y b,symmDiff_symmDiff_cancel_right]

private theorem fresh_edge {F : Finset (Term V)} {v w : V} (diff : v≠w)
    (unused : ∀ e∈F,v∉e) : pair v w∉F := by
  intro h
  exact unused _ h (by simp [pair_of_ne diff])

/-- The usual edge bound for a forest on a specified nonempty vertex set. -/
theorem Forest.edge_bound {F : Finset (Term V)} (forest : Forest F) (D : Finset V)
    (nonempty : D.Nonempty) (support : Supported F D) : F.card+1≤D.card := by
  induction forest generalizing D with
  | empty => simpa using card_pos.mpr nonempty
  | @leaf F _ v w diff unused ih =>
    have onD := support (pair v w) (mem_insert_self ..)
    have vD : v∈D := onD (by simp [pair_of_ne diff])
    have wD : w∈D := onD (by simp [pair_of_ne diff])
    have inside : Supported F (D.erase v) := by
      intro e he z hz
      exact mem_erase.mpr ⟨fun eq => unused e he (eq ▸ hz), support e (mem_insert_of_mem he) hz⟩
    have bound := ih (D.erase v) ⟨w,mem_erase.mpr ⟨diff.symm,wD⟩⟩ inside
    rw [card_insert_of_notMem (fresh_edge diff unused)]
    have size := card_erase_add_one vD
    omega

theorem two_forests_edge_bound (D : Finset V) {H : Finset (Term V)} (two : TwoForests H)
    (nonempty : D.Nonempty) (support : Supported H D) : H.card+2≤2*D.card := by
  obtain ⟨F,G,dis,rfl,f,g⟩ := two
  have a := f.edge_bound D nonempty (fun e h => support e (mem_union_left _ h))
  have b := g.edge_bound D nonempty (fun e h => support e (mem_union_right _ h))
  rw [card_union_of_disjoint dis]
  omega

/-- Both directions of the path between singletons and the full apex star.
The leaf edge is generated on the outward and on the return path. -/
private theorem forest_half (o : V) {F : Finset (Term V)} (forest : Forest F)
    (D : Finset V) (apart : o∉D) (support : Supported F D)
    (b : Bool) (s : State V) (apex : s o={o}) (ready : ∀ x∈D,s x=value o b x) :
    ∃ gs : List (Gate V), gs.length=D.card+F.card ∧ run s gs=switch o D (!b) s ∧
      (∀ e∈F,e∈outputs s gs) ∧ (b=false → ∀ x∈D,pair o x∈outputs s gs) ∧
      AllGates KeepsInput s gs := by
  induction forest generalizing D s with
  | empty =>
    have ok (x : V) (hx : x∈D) : KeepsInput x (s x ∆ s o) := by
      rw [ready x hx,apex,toggle]
      have ne : o≠x := fun e => apart (e ▸ hx)
      exact value_keeps ne _
    obtain ⟨gs,size,state,seen,safe⟩ := fanout_condition KeepsInput o D apart s ok
    refine ⟨gs,by simpa using size,?_,by simp,?_,safe⟩
    · rw [state]; funext x
      by_cases hx : x∈D
      · simp [switch,hx,ready x hx,apex,toggle]
      · simp [switch,hx]
    · rintro rfl x hx
      simpa [ready x hx,apex,value,pair,symmDiff_comm] using seen x hx
  | @leaf F _ v w diff unused ih =>
    let E := pair v w
    have onD : E⊆D := support _ (mem_insert_self ..)
    have vD : v∈D := onD (by simp [E,pair_of_ne diff])
    have wD : w∈D := onD (by simp [E,pair_of_ne diff])
    let small := D.erase v
    have inside (e : Term V) (he : e∈F) : e⊆small := by
      intro x hx
      exact mem_erase.mpr ⟨fun eq => unused e he (eq ▸ hx),support e (mem_insert_of_mem he) hx⟩
    let g : Gate V := ⟨w,v,diff.symm⟩
    let u := applyGate s g
    have edge : output s g=E := by
      change s v ∆ s w=_
      rw [ready v vD,ready w wD,same_pair]
    have here : u v=E := by simpa [u,applyGate,g] using edge
    have other (x : V) (xv : x≠v) : u x=s x := by simp [u,applyGate,g,xv]
    have ov : o≠v := fun eq => apart (eq ▸ vD)
    have pre (x : V) (hx : x∈small) : u x=value o b x := by
      obtain ⟨xv,xd⟩ := mem_erase.mp hx
      rw [other x xv,ready x xd]
    obtain ⟨gs,size,finish,visited,stars,steady⟩ := ih small
      (fun h => apart (mem_erase.mp h).2) inside u ((other o ov).trans apex) pre
    let t := run u gs
    have atV : t v=E := by simp [t,finish,switch,small,here]
    have atW : t w=value o (!b) w := by simp [t,finish,switch,small,diff.symm,wD]
    have out : output t g=value o (!b) v := by
      change t v ∆ t w=_
      rw [atV,atW]; exact finish_pair o v w (!b)
    have final : applyGate t g=switch o D (!b) s := by
      funext x
      by_cases xv : x=v
      · subst x; simpa [applyGate,g,switch,vD] using out
      · simp [applyGate,g,xv,t,finish,switch,small,other x xv]
    refine ⟨g::(gs++[g]),?_,?_,?_,?_,?_⟩
    · have dsz := card_erase_add_one vD
      have fres := fresh_edge diff unused
      simp only [List.length_cons,List.length_append,List.length_nil,card_insert_of_notMem fres,size]
      dsimp [small] at *; omega
    · change run u (gs++[g])=_
      rw [run_append]; exact final
    · intro e he
      rcases mem_insert.mp he with rfl | he
      · change E∈outputs s (g::(gs++[g]))
        rw [← edge]
        exact List.mem_cons_self
      · apply List.mem_cons_of_mem; rw [outputs_append]
        exact List.mem_append_left _ (visited e he)
    · intro forward x hx
      apply List.mem_cons_of_mem
      rw [outputs_append]
      by_cases xv : x=v
      · subst x
        apply List.mem_append_right
        have h : output t g=pair o v := by simpa [forward,value] using out
        exact h ▸ List.mem_cons_self
      · exact List.mem_append_left _ (stars forward x (mem_erase.mpr ⟨xv,hx⟩))
    · have start : KeepsInput g.target (output s g) := by
        rw [edge]; simp [g,E,KeepsInput,pair_of_ne diff,diff]
      refine ⟨start,(allGates_append KeepsInput u gs [g]).mpr ⟨steady,?_,trivial⟩⟩
      change KeepsInput v (output t g)
      rw [out]; exact value_keeps ov _

theorem cone_size (o : V) (D : Finset V) (apart : o∉D) (H : Finset (Term V))
    (support : Supported H D) : (cone o D H).card=D.card+H.card := by
  have dis : Disjoint (spokes o D) H := by
    apply disjoint_left.mpr
    intro e hs hh
    obtain ⟨x,hx,rfl⟩ := mem_image.mp hs
    have ox : o≠x := fun e => apart (e ▸ hx)
    exact apart (support _ hh (by simp [pair_of_ne ox]))
  rw [cone,card_union_of_disjoint dis,spokes,card_image_of_injective _ (fun _ _ => pair_same_root)]

/-- Coning off two edge-disjoint forests gives a perfect CNOT circuit. -/
theorem two_forests_construction_safe (o : V) (D : Finset V) (apart : o∉D) (H : Finset (Term V))
    (support : Supported H D) (two : TwoForests H) :
    ∃ gs : List (Gate V), Network (cone o D H) gs ∧ gs.length=(cone o D H).card+D.card ∧
      AllGates KeepsInput initial gs := by
  obtain ⟨F,G,dis,rfl,f,g⟩ := two
  have sf : Supported F D := fun e h => support e (mem_union_left _ h)
  have sg : Supported G D := fun e h => support e (mem_union_right _ h)
  obtain ⟨first,len1,one,ef,sp,ok1⟩ := forest_half o f D apart sf false initial rfl (by simp [initial,value])
  let s := switch o D true initial
  obtain ⟨last,len2,two,eg,_,ok2⟩ := forest_half o g D apart sg true s
    (by simp [s,switch,apart,initial]) (by intro x hx; simp [s,switch,hx])
  have clean : switch o D false s=initial := by
    funext x; by_cases hx : x∈D <;> simp [switch,s,value,hx,initial]
  change run initial first=s at one
  change run s last=switch o D false s at two
  refine ⟨first++last,⟨?_,?_⟩,?_,?_⟩
  · rw [run_append,one,two,clean]
  · intro e he
    rw [outputs_append,one]
    rcases mem_union.mp he with spoke | base
    · obtain ⟨x,hx,rfl⟩ := mem_image.mp spoke
      exact List.mem_append_left _ (sp rfl x hx)
    · rcases mem_union.mp base with ff | gg
      · exact List.mem_append_left _ (ef _ ff)
      · exact List.mem_append_right _ (eg _ gg)
  · rw [List.length_append,len1,len2,cone_size o D apart _ support,card_union_of_disjoint dis]
    omega
  · rw [allGates_append,one]; exact ⟨ok1,ok2⟩

theorem two_forests_construction (o : V) (D : Finset V) (apart : o∉D) (H : Finset (Term V))
    (support : Supported H D) (two : TwoForests H) :
    ∃ gs : List (Gate V), Network (cone o D H) gs ∧ gs.length=(cone o D H).card+D.card := by
  obtain ⟨gs,net,len,_⟩ := two_forests_construction_safe o D apart H support two
  exact ⟨gs,net,len⟩

#print axioms two_forests_construction

theorem Forest.subgraph {B H : Finset (Term V)} (forest : Forest B) (sub : H⊆B) : Forest H := by
  induction forest generalizing H with
  | empty => simpa [subset_empty.mp sub] using (Forest.empty (V:=V))
  | @leaf F _ v w diff unused ih =>
    let e := pair v w
    by_cases present : e∈H
    · have subs : H.erase e⊆F := by
        intro t ht
        obtain ⟨ne,h⟩ := mem_erase.mp ht
        exact (mem_insert.mp (sub h)).resolve_left ne
      have added := Forest.leaf (ih subs) v w diff (fun t ht => unused t (subs ht))
      change Forest (insert e (H.erase e)) at added
      rwa [insert_erase present] at added
    · apply ih
      intro t ht
      exact (mem_insert.mp (sub ht)).resolve_left (fun eq => present (by
        change pair v w∈H
        rwa [← eq]))

private theorem crossing (B : Finset (Term V)) (U : Finset V) (r v : V) (inside : r∈U)
    (path : ConnectedTo B r v) (outside : v∉U) :
    ∃ x∈U, ∃ y∉U,pair x y∈B := by
  induction path with
  | root => exact (outside inside).elim
  | @edge x y _ edge ih =>
    by_cases h : x∈U
    · exact ⟨x,h,y,outside,edge⟩
    · exact ih h

private theorem grow_forest [Fintype V] (r : V) (B : Finset (Term V)) (con : ∀ v, ConnectedTo B r v)
    (U : Finset V) (F : Finset (Term V)) (hr : r∈U) (sf : Supported F U)
    (forest : Forest F) (sub : F⊆B) (size : F.card+1=U.card) :
    ∃ out : Finset (Term V), Forest out ∧ out⊆B ∧ out.card+1=Fintype.card V := by
  generalize dist : Fintype.card V-U.card=k
  induction k using Nat.strong_induction_on generalizing F U with
  | h k ih =>
    by_cases all : U=univ
    · exact ⟨F,forest,sub,by simpa [all] using size⟩
    · obtain ⟨v,hv⟩ : ∃ v, v∉U := by
        by_contra! h
        exact all (eq_univ_iff_forall.mpr h)
      obtain ⟨x,hx,y,hy,edge⟩ := crossing B U r v hr (con v) hv
      have ne : y≠x := fun eq => hy (eq ▸ hx)
      have ey : pair y x∈B := by
        simpa only [pair,symmDiff_comm ({x} : Finset V) {y}] using edge
      have unused (e : Term V) (he : e∈F) : y∉e := fun yen => hy (sf e he yen)
      have next := Forest.leaf forest y x ne unused
      have inside : Supported (insert (pair y x) F) (insert y U) := by
        intro e he
        rcases mem_insert.mp he with rfl | he
        · rw [pair_of_ne ne]
          exact insert_subset (mem_insert_self ..) (singleton_subset_iff.mpr (mem_insert_of_mem hx))
        · exact (sf e he).trans (subset_insert ..)
      have ubs : (insert y U).card≤Fintype.card V := card_le_univ _
      rw [card_insert_of_notMem hy] at ubs
      have step : Fintype.card V-(insert y U).card < k := by
        rw [card_insert_of_notMem hy]; omega
      apply ih _ step (insert y U) (insert (pair y x) F) (mem_insert_of_mem hr)
        inside next (insert_subset ey sub)
      · rw [card_insert_of_notMem (fresh_edge ne unused),card_insert_of_notMem hy,size]
      · rfl

theorem connected_minimum_forest [Fintype V] (r : V) (B : Finset (Term V))
    (con : ∀ v, ConnectedTo B r v) (size : B.card=Fintype.card V-1) : Forest B := by
  obtain ⟨F,tree,sub,sz⟩ := grow_forest r B con {r} ∅ (mem_singleton_self _) (by simp [Supported])
    Forest.empty (empty_subset _) (by simp)
  have same := eq_of_subset_of_card_le sub (by omega)
  exact same ▸ tree

private theorem apex_spoke {o x : V} {D : Finset V} (outside : o∉D) (hx : x∈D) :
    o∈pair o x := by
  have ne : o≠x := fun e => outside (e ▸ hx)
  rw [pair_of_ne ne]
  exact mem_insert_self ..

/-- Every even-to-even gate producing a base edge uses two spokes. -/
private theorem slide_shape (o : V) (D : Finset V) (apart : o∉D) (H : Finset (Term V))
    (support : Supported H D) (free : SumFree H)
    {a b : Term V} (ha : a∈cone o D H) (hb : b∈cone o D H) (out : a ∆ b∈H) :
    ∃ x∈D, ∃ y∈D, a=pair o x ∧ b=pair o y ∧ a ∆ b=pair x y := by
  have excludes (p : Term V) (hp : p∈H) : o∉p := fun op => apart (support p hp op)
  have both : o∈a ↔ o∈b := by
    have no := excludes _ out
    simp only [mem_symmDiff] at no
    tauto
  rcases mem_union.mp ha with sa | ba <;> rcases mem_union.mp hb with sb | bb
  · obtain ⟨x,hx,rfl⟩ := mem_image.mp sa
    obtain ⟨y,hy,rfl⟩ := mem_image.mp sb
    exact ⟨x,hx,y,hy,rfl,rfl,two_edges_delta' ..⟩
  · obtain ⟨x,hx,rfl⟩ := mem_image.mp sa
    exact (excludes _ bb (both.mp (apex_spoke apart hx))).elim
  · obtain ⟨y,hy,rfl⟩ := mem_image.mp sb
    exact (excludes _ ba (both.mpr (apex_spoke apart hy))).elim
  · exact (free _ ba _ bb out).elim
where
  two_edges_delta' (o x y : V) : pair o x ∆ pair o y=pair x y := by
    rw [show pair o x=pair x o from symmDiff_comm ..,pair_comp]

private def slides (H : Finset (Term V)) (s : State V) : List (Gate V) → List (Term V)
  | [] => []
  | g::gs => if (s g.target).card%2=0 ∧ (s g.control).card%2=0 ∧ output s g∈H
    then output s g :: slides H (applyGate s g) gs else slides H (applyGate s g) gs

private theorem slides_subset (H : Finset (Term V)) (s : State V) (gs : List (Gate V)) :
    ∀ e∈slides H s gs,e∈H := by
  induction gs generalizing s with
  | nil => simp [slides]
  | cons g gs ih =>
    intro e he
    simp only [slides] at he
    split at he
    · rename_i yes
      rcases List.mem_cons.mp he with rfl | h
      · exact yes.2.2
      · exact ih _ _ h
    · exact ih _ _ he

private theorem born_or_slide (H : Finset (Term V)) (simple : SimpleEdges H)
    (s : State V) (gs : List (Gate V)) {e : Term V} (he : e∈H) (out : e∈outputs s gs) :
    e∈births s gs ∨ e∈slides H s gs := by
  induction gs generalizing s with
  | nil => simp [outputs] at out
  | cons g gs ih =>
    rcases List.mem_cons.mp out with rfl | later
    · have p := card_xor (s g.target) (s g.control)
      change (output s g).card%2=_ at p
      rw [simple _ he] at p
      by_cases even : (s g.target).card%2=0
      · have both : (s g.target).card%2=0 ∧ (s g.control).card%2=0 ∧ output s g∈H :=
          ⟨even,by omega,he⟩
        exact Or.inr (by simp [slides,both])
      · have both : (s g.target).card%2=1 ∧ (s g.control).card%2=1 := by omega
        exact Or.inl (by simp [births,both])
    · rcases ih _ later with birth | slide
      · left; simp only [births]; split <;> simp_all
      · right; simp only [slides]; split <;> simp_all

private def GoodState (T : Finset (Term V)) (s : State V) : Prop :=
  ∀ v, (s v).card%2=0 → s v∈T

private def GoodOutputs (T : Finset (Term V)) (s : State V) (gs : List (Gate V)) : Prop :=
  ∀ e∈outputs s gs,e.card%2=0 → e∈T

private theorem good_step (T : Finset (Term V)) (s : State V) (g : Gate V) (gs : List (Gate V))
    (prior : GoodState T s) (next : GoodOutputs T s (g::gs)) : GoodState T (applyGate s g) := by
  intro v hv
  by_cases eq : v=g.target
  · subst v
    simp only [applyGate,Function.update_self] at hv ⊢
    exact next _ List.mem_cons_self hv
  · simp [applyGate,eq] at hv ⊢; exact prior v hv

private theorem good_tail (T : Finset (Term V)) (s : State V) (g : Gate V) (gs : List (Gate V))
    (next : GoodOutputs T s (g::gs)) : GoodOutputs T (applyGate s g) gs :=
  fun e he hp => next e (List.mem_cons_of_mem _ he) hp

/-- When a spoke has left every wire forever, its vertex cannot belong
to another base edge made from two even input wires. -/
private theorem lost_spoke (o : V) (D : Finset V) (apart : o∉D) (H : Finset (Term V))
    (support : Supported H D) (free : SumFree H) (x : V) (s : State V) (gs : List (Gate V))
    (past : GoodState (cone o D H) s) (future : GoodOutputs (cone o D H) s gs)
    (absent : ∀ v,s v≠pair o x) (gone : pair o x ∉ outputs s gs) :
    ∀ e∈slides H s gs,x∉e := by
  induction gs generalizing s with
  | nil => simp [slides]
  | cons g gs ih =>
    have no : output s g≠pair o x := fun eq => gone (eq ▸ List.mem_cons_self)
    have later : pair o x∉outputs (applyGate s g) gs := fun h => gone (List.mem_cons_of_mem _ h)
    have notLive (v : V) : applyGate s g v≠pair o x := by
      by_cases eq : v=g.target
      · subst v; simpa [applyGate] using no
      · simpa [applyGate,eq] using absent v
    have tail := ih _ (good_step _ _ _ _ past future) (good_tail _ _ _ _ future) notLive later
    intro e he
    simp only [slides] at he
    split at he
    · rename_i yes
      rcases List.mem_cons.mp he with rfl | h
      · obtain ⟨a,_,b,_,ea,eb,shape⟩ := slide_shape o D apart H support free
          (past _ yes.1) (past _ yes.2.1) yes.2.2
        have xa : x≠a := fun eq => absent _ (eq ▸ ea)
        have xb : x≠b := fun eq => absent _ (eq ▸ eb)
        change x∉s g.target ∆ s g.control
        rw [shape]
        simp [pair,mem_symmDiff,xa,xb]
      · exact tail _ h
    · exact tail _ he

private def LiveOnce (s : State V) : Prop :=
  ∀ i j, (s i).card%2=0 → s i=s j → i=j

private def FreshAhead (s : State V) (gs : List (Gate V)) : Prop :=
  ∀ i, (s i).card%2=0 → s i∉evens s gs

private theorem step_unique (s : State V) (g : Gate V) (gs : List (Gate V))
    (once : LiveOnce s) (ahead : FreshAhead s (g::gs)) (unique : (evens s (g::gs)).Nodup) :
    LiveOnce (applyGate s g) ∧ FreshAhead (applyGate s g) gs ∧ (evens (applyGate s g) gs).Nodup := by
  let u := applyGate s g
  let w := output s g
  have head : u g.target=w := Function.update_self ..
  have other (i : V) (ht : i≠g.target) : u i=s i := by simp [u,applyGate,ht]
  have split : evens s (g::gs) = if w.card%2=0 then w :: evens u gs else evens u gs := by
    by_cases even : (output s g).card%2=0 <;> simp [evens,outputs,w,u,even]
  have tail : (evens u gs).Nodup := by split at split <;> simp_all
  have avoid (i : V) (hi : (s i).card%2=0) (even : w.card%2=0) : w≠s i := by
    intro eq
    apply ahead i hi
    rw [split,if_pos even,← eq]; exact List.mem_cons_self
  refine ⟨?_,?_,tail⟩
  · intro i j hi eq
    change (u i).card%2=0 at hi
    change u i=u j at eq
    by_cases it : i=g.target <;> by_cases jt : j=g.target
    · exact it.trans jt.symm
    · subst i; rw [head] at hi eq
      rw [other j jt] at eq
      exact (avoid j (eq ▸ hi) hi eq).elim
    · subst j; rw [other i it] at hi eq
      rw [head] at eq
      exact (avoid i hi (eq ▸ hi) eq.symm).elim
    · rw [other i it] at hi eq
      rw [other j jt] at eq
      exact once i j hi eq
  · intro i hi
    change (u i).card%2=0 at hi
    change u i∉evens u gs
    by_cases it : i=g.target
    · subst i; rw [head] at hi ⊢
      rw [split,if_pos hi] at unique
      exact (List.nodup_cons.mp unique).1
    · rw [other i it] at hi ⊢
      intro hm; apply ahead i hi
      rw [split]; split
      · exact List.mem_cons_of_mem _ hm
      · exact hm

private theorem slide_forest (o : V) (D : Finset V) (apart : o∉D) (H : Finset (Term V))
    (support : Supported H D) (simple : SimpleEdges H) (free : SumFree H)
    (s : State V) (gs : List (Gate V)) (past : GoodState (cone o D H) s)
    (future : GoodOutputs (cone o D H) s gs) (once : LiveOnce s) (ahead : FreshAhead s gs)
    (unique : (evens s gs).Nodup) : Forest (slides H s gs).toFinset := by
  induction gs generalizing s with
  | nil => exact .empty
  | cons g gs ih =>
    let u := applyGate s g
    have priorU := good_step _ _ _ _ past future
    have futureU := good_tail _ _ _ _ future
    obtain ⟨onceU,aheadU,uniqueU⟩ := step_unique s g gs once ahead unique
    have tree := ih u priorU futureU onceU aheadU uniqueU
    simp only [slides]
    split
    · rename_i both
      obtain ⟨x,hx,y,_,target,_,delta⟩ := slide_shape o D apart H support free
        (past _ both.1) (past _ both.2.1) both.2.2
      change output s g=pair x y at delta
      have diff : x≠y := by
        intro eq; have sz := simple _ both.2.2
        simp [delta,eq,pair] at sz
      have notLive (v : V) : u v≠pair o x := by
        by_cases it : v=g.target
        · subst v; intro eq
          have qt : output s g=pair o x := by simpa [u,applyGate] using eq
          have has : o∈output s g := qt ▸ apex_spoke apart hx
          exact apart (support _ both.2.2 has)
        · intro eq
          have h : s v=pair o x := by simpa [u,applyGate,it] using eq
          exact it ((once g.target v both.1 (target.trans h.symm)).symm)
      have gone : pair o x∉outputs u gs := by
        intro h
        apply ahead g.target both.1
        apply List.mem_filter.mpr
        refine ⟨List.mem_cons_of_mem _ ?_,by simp [both.1]⟩
        rw [target]
        exact h
      have later := lost_spoke o D apart H support free x u gs priorU futureU notLive gone
      rw [List.toFinset_cons,delta]
      exact .leaf tree x y diff (fun e he => later e (List.mem_toFinset.mp he))
    · exact tree

/-- A cone over a triangle-free base is perfect exactly when the base edges
can be partitioned into two forests. All n input wires are restored. -/
theorem cone_perfect_iff_two_forests [Fintype V] (o : V) (D : Finset V) (apart : o∉D)
    (all : insert o D=univ) (H : Finset (Term V)) (support : Supported H D)
    (simple : SimpleEdges H) (triangleFree : TriangleFree H) :
    (∃ gs : List (Gate V), Network (cone o D H) gs ∧ gs.length=(cone o D H).card+D.card) ↔
      TwoForests H := by
  refine ⟨?_,two_forests_construction o D apart H support⟩
  rintro ⟨gs,net,tight⟩
  let T := cone o D H
  have con (v : V) : ConnectedTo T o v := by
    have member : v∈insert o D := all ▸ mem_univ v
    rcases mem_insert.mp member with rfl | vd
    · exact .root
    · exact .edge .root (mem_union_left _ (mem_image_of_mem _ vd))
  have simpleT : SimpleEdges T := by
    intro e he
    rcases mem_union.mp he with spoke | base
    · obtain ⟨y,hy,rfl⟩ := mem_image.mp spoke
      have oy : o≠y := fun eq => apart (eq ▸ hy)
      simp [pair_of_ne oy,oy]
    · exact simple e base
  have total : Fintype.card V=D.card+1 := by
    rw [← card_univ,← all,card_insert_of_notMem apart]
  have eq : gs.length=T.card+(Fintype.card V-1) := by simpa [total,T] using tight
  obtain ⟨_,size,linked,_⟩ := perfect_birth_tree o T con simpleT gs net eq
  let F := (slides H initial gs).toFinset
  have se : F⊆H := fun _ h => slides_subset H initial gs _ (List.mem_toFinset.mp h)
  have stem := connected_minimum_forest o _ linked size
  have left : H \ F ⊆ (births initial gs).toFinset := by
    intro e he
    obtain ⟨inH,notS⟩ := mem_sdiff.mp he
    have out := net.2 e (mem_union_right _ inH)
    rcases born_or_slide H simple initial gs inH out with birth | slide
    · exact List.mem_toFinset.mpr birth
    · exact (notS (List.mem_toFinset.mpr slide)).elim
  have unique := perfect_even_nodup o T gs con simpleT net eq
  have future := even_output_saturation o T gs con (fun e he => by rw [simpleT e he]) net eq.le
  have right := slide_forest o D apart H support simple (sumfree_of_triangleFree H simple triangleFree)
    initial gs (by simp [GoodState,initial]) future (by simp [LiveOnce,initial])
      (by simp [FreshAhead,initial]) unique
  refine ⟨H\F,F,disjoint_left.mpr (fun _ h => (mem_sdiff.mp h).2),?_,stem.subgraph left,right⟩
  exact (sdiff_union_of_subset se).symm

#print axioms cone_perfect_iff_two_forests

private theorem all_states (s : State V) (gs : List (Gate V)) (start : ∀ v,KeepsInput v (s v))
    (steps : AllGates KeepsInput s gs) : ∀ t∈gs.scanl applyGate s, ∀ v,KeepsInput v (t v) := by
  induction gs generalizing s with
  | nil => simpa using start
  | cons g gs ih =>
    intro t ht
    rcases List.mem_cons.mp ht with rfl | later
    · exact start
    · apply ih _ _ steps.2 t later
      intro v; by_cases eq : v=g.target
      · subst v; simpa [applyGate] using steps.1
      · simpa [applyGate,eq] using start v

/-- Questions (C1) and (C3) hold simultaneously on every perfect cone over a
triangle-free graph, including ones without any perfect cancellation ordering. -/
theorem cone_c1_c3 [Fintype V] (o : V) (D : Finset V) (apart : o∉D) (all : insert o D=univ)
    (H : Finset (Term V)) (support : Supported H D) (simple : SimpleEdges H)
    (tri : TriangleFree H) (perfect : ∃ gs : List (Gate V),
      Network (cone o D H) gs ∧ gs.length=(cone o D H).card+D.card) :
    ∃ gs : List (Gate V), Network (cone o D H) gs ∧ gs.length=(cone o D H).card+D.card ∧
      ∀ t∈gs.scanl applyGate initial, ∀ v, v∈t v ∧ ((t v).card=1 ∨ (t v).card=2) := by
  have two := (cone_perfect_iff_two_forests o D apart all H support simple tri).mp perfect
  obtain ⟨gs,net,count,safe⟩ := two_forests_construction_safe o D apart H support two
  exact ⟨gs,net,count,all_states initial gs (by simp [KeepsInput,initial]) safe⟩

#print axioms cone_c1_c3

end ConeForests

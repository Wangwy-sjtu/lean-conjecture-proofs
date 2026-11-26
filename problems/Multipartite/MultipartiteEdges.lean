import Multipartite
import Mathlib.Data.Finset.Card
import Mathlib.Data.List.Chain
import Mathlib.Data.List.Nodup

namespace EdgeCompletion

variable {V : Type} [DecidableEq V]

/-- An inserted undirected edge is the unordered pair of its two endpoints. -/
abbrev Edges (V : Type) [DecidableEq V] := Finset (Finset V)

def Adj (c : V → ℕ) (E : Edges V) (x y : V) : Prop :=
  x ≠ y ∧ (c x ≠ c y ∨ ({x,y} : Finset V) ∈ E)

private theorem retained {E : Edges V} {e : Finset V} {z u v : V} (hz : z ∈ e)
    (hu : z ≠ u) (hv : z ≠ v) (h : ({u,v} : Finset V) ∈ E) :
    ({u,v} : Finset V) ∈ E.erase e := by
  refine Finset.mem_erase.mpr ⟨?_, h⟩
  intro eq
  rw [← eq] at hz
  simp [hu, hv] at hz

private theorem retain_chain {c : V → ℕ} {E : Edges V} {e : Finset V} {z : V} {s : List V}
    (hz : z ∈ e) (absent : z ∉ s) (hc : s.IsChain (Adj c E)) :
    s.IsChain (Adj c (E.erase e)) := by
  apply hc.imp_of_mem_imp
  intro x y hx hy h
  refine ⟨h.1, h.2.imp_right ?_⟩
  apply retained hz
  · rintro rfl; exact absent hx
  · rintro rfl; exact absent hy

private def Tagged (c : V → ℕ) (b : ℕ) (v : V) (E : Edges V)
    (small : Finset V) (s : List V) : Prop :=
  ∀ y ∈ s, c y ≠ b → y ∈ small ∨ ({v,y} : Finset V) ∈ E

private theorem retain_tags {c : V → ℕ} {b : ℕ} {v z : V} {E : Edges V}
    {small e : Finset V} {s : List V} (he : z ∈ e) (hz : z ∉ s) (hv : z ≠ v)
    (tags : Tagged c b v E small s) : Tagged c b v (E.erase e) small s := by
  intro y hy hn
  refine (tags y hy hn).imp_right (retained he hv ?_)
  rintro rfl; exact hz hy

/-- Along a pivot's later-neighbour path, repeated members of one independent
part need distinct old separators or distinct newly inserted edges. -/
private theorem path_budget (c : V → ℕ) (b : ℕ) (v : V) (s : List V)
    (E : Edges V) (small : Finset V) (hd : s.Nodup) (hv : v ∉ s)
    (tags : Tagged c b v E small s) (chain : s.IsChain (Adj c E)) :
    s.countP (fun x => decide (c x = b)) ≤ E.card + small.card + 1 := by
  induction s using List.twoStepInduction generalizing E small with
  | nil => simp
  | singleton x => simp [List.countP_cons]; split <;> omega
  | cons_cons x y s tailIH restIH =>
    have ndx := List.nodup_cons.mp hd
    have ndy := List.nodup_cons.mp ndx.2
    have hchain := List.isChain_cons_cons.mp chain
    have tv : v ∉ y::s := fun h => hv (List.mem_cons_of_mem _ h)
    have xv : x ≠ v := by rintro rfl; exact hv (by simp)
    have yv : y ≠ v := by rintro rfl; exact hv (by simp)
    have tvs : v ∉ s := fun h => tv (List.mem_cons_of_mem _ h)
    have tagsTail : Tagged c b v E small (y::s) :=
      fun w hw => tags w (List.mem_cons_of_mem _ hw)
    have tagsRest : Tagged c b v E small s :=
      fun w hw => tagsTail w (List.mem_cons_of_mem _ hw)
    by_cases xb : c x = b
    · by_cases yb : c y = b
      · let e : Finset V := {x,y}
        have he : e ∈ E := hchain.1.2.resolve_left (by simp [xb,yb])
        have hx : x ∈ e := by simp [e]
        have hc := retain_chain hx ndx.1 hchain.2
        have ht := retain_tags hx ndx.1 xv tagsTail
        have ih := restIH y (E.erase e) small ndx.2 tv ht hc
        have card := Finset.card_erase_add_one he
        simp [yb] at ih
        simp [xb,yb]
        omega
      · rcases tagsTail y (by simp) yb with hsmall | hedge
        · have ht : Tagged c b v E (small.erase y) s := by
            intro w hw hn
            refine (tagsRest w hw hn).imp_left (fun h => Finset.mem_erase.mpr ⟨?_,h⟩)
            rintro rfl; exact ndy.1 hw
          have ih := tailIH E (small.erase y) ndy.2 tvs ht hchain.2.tail
          have card := Finset.card_erase_add_one hsmall
          simp [xb,yb]
          omega
        · let e : Finset V := {v,y}
          have hy : y ∈ e := by simp [e]
          have hc := retain_chain hy ndy.1 hchain.2.tail
          have ht := retain_tags hy ndy.1 yv tagsRest
          have ih := tailIH (E.erase e) small ndy.2 tvs ht hc
          have card := Finset.card_erase_add_one hedge
          simp [xb,yb]
          dsimp [e] at ih
          omega
    · have ih := restIH y E small ndx.2 tv tagsTail hchain.2
      simpa [xb] using ih

/-- Reachability along actual edges in the graph induced by the given vertex list. -/
inductive Reach (c : V → ℕ) (E : Edges V) (s : List V) (u : V) : V → Prop
  | self : Reach c E s u u
  | step {x y} : Reach c E s u x → x ∈ s → y ∈ s → Adj c E x y → Reach c E s u y

private theorem cross_adj {c : V → ℕ} (E : Edges V) {x y : V} (hne : c x ≠ c y) :
    Adj c E x y := ⟨fun eq => hne (congrArg c eq), Or.inl hne⟩

private theorem reach_if_two_parts {c : V → ℕ} (E : Edges V) {s : List V} {a b u x : V}
    (ha : a ∈ s) (hb : b ∈ s) (hne : c a ≠ c b) (hu : u ∈ s) (hx : x ∈ s) :
    Reach c E s u x := by
  by_cases eq : c u = c x
  · obtain ⟨z, hz, hzu⟩ : ∃ z ∈ s, c z ≠ c u := by
      by_cases h : c a = c u
      · exact ⟨b,hb,fun hh => hne (h.trans hh.symm)⟩
      · exact ⟨a,ha,h⟩
    exact .step (.step .self hu hz (cross_adj E hzu.symm)) hz hx
      (cross_adj E (fun h => hzu (h.trans eq.symm)))
  · exact .step .self hu hx (cross_adj E eq)

/-- The definition from the paper, using paths after deletion of the current
vertex and the exact order of its later neighbors in each connected component. -/
noncomputable def Ordering (c : V → ℕ) (E : Edges V) (xs : List V) : Prop := by
  classical
  exact ∀ pre v tail, xs = pre ++ v :: tail → ∀ u ∈ pre++tail,
    (tail.filter (fun y => decide (Adj c E v y ∧ Reach c E (pre++tail) u y))).IsChain (Adj c E)

private def pop (c : V → ℕ) (b : ℕ) (s : List V) := s.countP (fun y => decide (c y = b))

omit [DecidableEq V] in
private theorem rem_member (c : V → ℕ) (i : ℕ) (pre : List V) (v : V) (tail : List V)
    (two : 2 ≤ pop c i (pre++v::tail)) : ∃ w ∈ pre++tail, c w=i := by
  by_contra! h
  have hz : pop c i (pre++tail) = 0 := by
    apply List.countP_eq_zero.mpr
    intro x hx
    simpa using h x hx
  simp only [pop, List.countP_append, List.countP_cons] at hz two
  split at two <;> omega

omit [DecidableEq V] in
private theorem first_major (c : V → ℕ) (s : List V) (h : ∃ z ∈ s, c z = 0 ∨ c z = 1) :
    ∃ pre v tail, s = pre ++ v::tail ∧ (c v=0 ∨ c v=1) ∧
      ∀ w ∈ pre, c w ≠ 0 ∧ c w ≠ 1 := by
  induction s with
  | nil => simp at h
  | cons x s ih =>
    by_cases hx : c x = 0 ∨ c x = 1
    · exact ⟨[],x,s,rfl,hx,by simp⟩
    · obtain ⟨z,hz,hz'⟩ := h
      have hz'' : z ∈ s := (List.mem_cons.mp hz).resolve_left (by rintro rfl; exact hx hz')
      obtain ⟨pre,v,t,ht,hm,hp⟩ := ih ⟨z,hz'',hz'⟩
      refine ⟨x::pre,v,t,by simp [ht],hm,?_⟩
      intro w hw
      rcases List.mem_cons.mp hw with rfl | hh
      · exact not_or.mp hx
      · exact hp w hh

private theorem pivot_budget {c : V → ℕ} {E : Edges V} {ord pre tail : List V}
    {v : V} {b : ℕ} (eq : ord=pre++v::tail) (hd : ord.Nodup) (ho : Ordering c E ord)
    (small : Finset V) (diff : c v ≠ b) (clean : ∀ w ∈ pre, c w ≠ b)
    (minor : ∀ w ∈ tail, c w ≠ b → c w ≠ c v → w ∈ small)
    (ha : 2 ≤ pop c 0 ord) (hb : 2 ≤ pop c 1 ord) :
    pop c b ord ≤ E.card + small.card + 1 := by
  classical
  obtain ⟨a,has,ca⟩ := rem_member c 0 pre v tail (eq ▸ ha)
  obtain ⟨d,hds,cd⟩ := rem_member c 1 pre v tail (eq ▸ hb)
  have reach (y : V) (hy : y ∈ tail) : Reach c E (pre++tail) a y :=
    reach_if_two_parts E has hds (by omega) has (List.mem_append_right _ hy)
  let nbr := tail.filter (fun y => decide (Adj c E v y))
  have efilter : tail.filter (fun y => decide (Adj c E v y ∧ Reach c E (pre++tail) a y)) = nbr := by
    apply List.filter_congr
    intro y hy
    simp [reach y hy]
  have hc := ho pre v tail eq a has
  rw [efilter] at hc
  have hd' := (List.nodup_append'.mp (eq ▸ hd)).2.1
  have ht := List.nodup_cons.mp hd'
  have htgs : Tagged c b v E small nbr := by
    intro y hy hyb
    obtain ⟨hym,hya⟩ := List.mem_filter.mp hy
    have ha' : Adj c E v y := of_decide_eq_true hya
    by_cases h : c y = c v
    · exact Or.inr (ha'.2.resolve_left (not_not.mpr h.symm))
    · exact Or.inl (minor y hym hyb h)
  have bh := path_budget c b v nbr E small (ht.2.filter _) (fun hm => ht.1 (List.mem_filter.mp hm).1) htgs hc
  have counts : nbr.countP (fun y => decide (c y = b)) = pop c b tail := by
    rw [List.countP_filter]
    apply List.countP_congr
    intro y _
    by_cases h : c y = b
    · have hy := cross_adj E (c:=c) (x:=v) (y:=y) (by omega)
      simp [h,hy]
    · simp [h]
  rw [counts] at bh
  have hp : pop c b pre = 0 := by
    apply List.countP_eq_zero.mpr
    intro y hy
    simpa using clean y hy
  rw [eq]
  simpa [pop, hp, diff, show pre.countP (fun y => decide (c y=b)) = 0 from hp] using bh

/-- The number of original vertices outside the two distinguished parts. -/
def minorSet (c : V → ℕ) (s : List V) : Finset V :=
  (s.filter (fun w => decide (c w ≠ 0 ∧ c w ≠ 1))).toFinset

/-- In every completed ordering, the edges inserted and the vertices from
the other parts together separate all but one vertex of the smaller part.
The counting is on unordered pairs of individually named vertices. -/
theorem edge_lower_bound (c : V → ℕ) (E : Edges V) (ord : List V) (hd : ord.Nodup)
    (ho : Ordering c E ord) :
    min (pop c 0 ord) (pop c 1 ord) - 1 - (minorSet c ord).card ≤ E.card := by
  by_cases hs : min (pop c 0 ord) (pop c 1 ord) ≤ 1
  · omega
  have h0 : 2 ≤ pop c 0 ord := by omega
  have h1 : 2 ≤ pop c 1 ord := by omega
  have present : ∃ w ∈ ord, c w=0 ∨ c w=1 := by
    by_contra! h
    have hz : pop c 0 ord=0 := by
      apply List.countP_eq_zero.mpr
      intro w hw
      simpa using (h w hw).1
    omega
  obtain ⟨pre,v,tail,eq,majors,hp⟩ := first_major c ord present
  have memSmall (w : V) (hw : w ∈ tail) (hw0 : c w ≠ 0) (hw1 : c w ≠ 1) :
      w ∈ minorSet c ord := by
    have hm : w ∈ ord := eq ▸ List.mem_append_right _ (List.mem_cons_of_mem _ hw)
    simp [minorSet,hm,hw0,hw1]
  rcases majors with cv | cv
  · have bound := pivot_budget eq hd ho (minorSet c ord) (by omega : c v ≠ 1)
      (fun w hw => (hp w hw).2)
      (fun w hw hwb hwv => memSmall w hw (cv ▸ hwv) hwb) h0 h1
    omega
  · have bound := pivot_budget eq hd ho (minorSet c ord) (by omega : c v ≠ 0)
      (fun w hw => (hp w hw).1)
      (fun w hw hwb hwv => memSmall w hw hwb (cv ▸ hwv)) h0 h1
    omega

#print axioms edge_lower_bound

private theorem adj_symm {c : V → ℕ} {E : Edges V} {x y : V} (h : Adj c E x y) :
    Adj c E y x := ⟨h.1.symm, h.2.elim (fun hn => Or.inl hn.symm)
      (fun he => Or.inr (by simpa only [Finset.pair_comm y x] using he))⟩

private theorem Reach.trans {c : V → ℕ} {E : Edges V} {s : List V} {a b z : V}
    (h : Reach c E s a b) (g : Reach c E s b z) : Reach c E s a z := by
  induction g with
  | self => exact h
  | step _ hx hy adj ih => exact .step ih hx hy adj

private theorem joined {c : V → ℕ} {E : Edges V} (s t : List V)
    (sub : ∀ w ∈ t, w ∈ s) (chain : t.IsChain (Adj c E)) (a b : V) (ha : a ∈ t) (hb : b ∈ t) :
    Reach c E s a b := by
  induction t using List.twoStepInduction generalizing a b with
  | nil => simp at ha
  | singleton x =>
    simp only [List.mem_singleton] at ha hb
    subst a; subst b; exact .self
  | cons_cons x y t _ ih =>
    have hyx := (List.isChain_cons_cons.mp chain).1
    have hx := sub x (by simp)
    have hy := sub y (by simp)
    have ih' := ih y (fun z hz => sub z (List.mem_cons_of_mem _ hz)) chain.tail
    by_cases hxA : a = x
    · subst a
      by_cases hxB : b = x
      · subst b; exact .self
      · exact (Reach.step .self hx hy hyx).trans (ih' y b (by simp) ((List.mem_cons.mp hb).resolve_left hxB))
    · have hat := (List.mem_cons.mp ha).resolve_left hxA
      by_cases hxB : b = x
      · subst b
        exact (ih' a y hat (by simp)).trans (.step .self hy hx (adj_symm hyx))
      · exact ih' a b hat ((List.mem_cons.mp hb).resolve_left hxB)

private noncomputable def later (c : V → ℕ) (E : Edges V) (v : V) (s : List V) : List V := by
  classical
  exact s.filter (fun y => decide (Adj c E v y))

private def Strong (c : V → ℕ) (E : Edges V) : List V → Prop
  | [] => True
  | x::xs => (later c E x xs).IsChain (Adj c E) ∧ Strong c E xs

private theorem strong_local {c : V → ℕ} {E : Edges V} (pre : List V) (v : V) (tail : List V)
    (hs : Strong c E (pre++v::tail)) : (later c E v tail).IsChain (Adj c E) := by
  induction pre with
  | nil => exact hs.1
  | cons x pre ih => exact ih hs.2

private theorem strong_ordering {c : V → ℕ} {E : Edges V} {s : List V} (hs : Strong c E s) :
    Ordering c E s := by
  classical
  intro pre v t eq u hu
  let L := later c E v t
  have hc : L.IsChain (Adj c E) := strong_local pre v t (eq ▸ hs)
  have memL (x : V) : x ∈ L ↔ x ∈ t ∧ Adj c E v x := by simp [L,later]
  by_cases h : ∃ x ∈ L, Reach c E (pre++t) u x
  · obtain ⟨x,hx,hur⟩ := h
    have all (y : V) (hy : y ∈ L) : Reach c E (pre++t) u y := hur.trans
      (joined (pre++t) L (fun w hw => List.mem_append_right _ ((memL w).mp hw).1) hc x y hx hy)
    have he : t.filter (fun y => decide (Adj c E v y ∧ Reach c E (pre++t) u y)) = L := by
      apply List.filter_congr
      intro y hy
      by_cases adj : Adj c E v y
      · simp [adj,all y ((memL y).mpr ⟨hy,adj⟩)]
      · simp [adj]
    rwa [he]
  · have he : t.filter (fun y => decide (Adj c E v y ∧ Reach c E (pre++t) u y)) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro y hy
      intro yes
      obtain ⟨adj,hr⟩ := of_decide_eq_true yes
      exact h ⟨y,(memL y).mpr ⟨hy,adj⟩,hr⟩
    rw [he]
    exact List.IsChain.nil

private theorem strong_congr {c : V → ℕ} {E F : Edges V} {s : List V}
    (he : ∀ x ∈ s, ∀ y ∈ s, Adj c E x y ↔ Adj c F x y) (hs : Strong c E s) :
    Strong c F s := by
  classical
  induction s with
  | nil => trivial
  | cons x t ih =>
    have eq : later c E x t = later c F x t := by
      apply List.filter_congr
      intro y hy
      simp only [he x (by simp) y (by simp [hy])]
    constructor
    · rw [← eq]
      apply hs.1.imp_of_mem_imp
      intro a b ha hb ab
      exact (he a (by simp [(List.mem_filter.mp ha).1]) b (by simp [(List.mem_filter.mp hb).1])).mp ab
    · exact ih (fun a ha b hb => he a (by simp [ha]) b (by simp [hb])) hs.2

private def pathEdges : List V → Edges V
  | [] | [_] => ∅
  | x::y::t => insert {x,y} (pathEdges (y::t))

private theorem path_support (s : List V) {e : Finset V} (he : e ∈ pathEdges s) {w : V}
    (hw : w ∈ e) : w ∈ s := by
  induction s using List.twoStepInduction with
  | nil | singleton => simp [pathEdges] at he
  | cons_cons x y t _ ih =>
    rcases Finset.mem_insert.mp he with rfl | he
    · simp only [Finset.mem_insert,Finset.mem_singleton] at hw
      rcases hw with rfl | rfl <;> simp
    · exact List.mem_cons_of_mem _ (ih y he)

private theorem path_card (x : V) (t : List V) : (pathEdges (x::t)).card ≤ t.length := by
  induction t generalizing x with
  | nil => simp [pathEdges]
  | cons y t ih =>
    have h := Finset.card_insert_le ({x,y} : Finset V) (pathEdges (y::t))
    have i := ih y
    simpa only [pathEdges, List.length_cons] using h.trans (Nat.add_le_add_right i 1)

private theorem path_chain (c : V → ℕ) (s : List V) (hd : s.Nodup) :
    s.IsChain (Adj c (pathEdges s)) := by
  induction s using List.twoStepInduction with
  | nil | singleton => simp
  | cons_cons x y t _ ih =>
    have nd := List.nodup_cons.mp hd
    apply List.isChain_cons_cons.mpr
    refine ⟨⟨fun eq => nd.1 (by simp [eq]), Or.inr (by simp [pathEdges])⟩,?_⟩
    apply (ih y nd.2).imp
    intro a b h
    exact ⟨h.1,h.2.imp_right (Finset.mem_insert_of_mem ·)⟩


private theorem outside_path {c : V → ℕ} {s : List V} {x : V} (absent : x ∉ s) (y : V) :
    Adj c (pathEdges s) x y ↔ c x ≠ c y := by
  constructor
  · intro h
    exact h.2.resolve_right (fun he => absent (path_support s he (by simp)))
  · exact cross_adj _

private theorem empty_adj {c : V → ℕ} {x y : V} : Adj c ∅ x y ↔ c x ≠ c y := by
  constructor
  · rintro ⟨_,h⟩
    simpa using h
  · exact cross_adj _

private theorem strong_path (c : V → ℕ) (b : ℕ) (s : List V)
    (hd : s.Nodup) (mono : ∀ x ∈ s, c x=b) : Strong c (pathEdges s) s := by
  classical
  induction s using List.twoStepInduction with
  | nil => trivial
  | singleton x => simp [Strong,later]
  | cons_cons x y t _ ih =>
    have dx := List.nodup_cons.mp hd
    have dy := List.nodup_cons.mp dx.2
    have xy := path_chain c (x::y::t) hd
    have iffNext (z : V) (hz : z ∈ y::t) : Adj c (pathEdges (x::y::t)) x z ↔ z=y := by
      constructor
      · intro h
        have e := h.2.resolve_left (not_not.mpr ((mono x (by simp)).trans (mono z (by simp [hz])).symm))
        rcases Finset.mem_insert.mp e with eq | he
        · have hm : z ∈ ({x,y}:Finset V) := eq ▸ (show z ∈ ({x,z}:Finset V) from by simp)
          simpa [h.1.symm] using hm
        · exact (dx.1 (path_support (y::t) he (by simp))).elim
      · rintro rfl
        exact (List.isChain_cons_cons.mp xy).1
    have ef : later c (pathEdges (x::y::t)) x (y::t) = (y::t).filter (fun z => decide (z=y)) := by
      apply List.filter_congr
      intro z hz
      simp only [iffNext z hz]
    have none : t.filter (fun z => decide (z=y)) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro z hz h
      exact dy.1 ((of_decide_eq_true h) ▸ hz)
    constructor
    · rw [ef]
      simp [none]
    · apply strong_congr (E:=pathEdges (y::t)) _ (ih y dx.2 (fun z hz => mono z (by simp [hz])))
      intro u hu w hw
      have ne : ({u,w}:Finset V) ≠ {x,y} := by
        intro eq
        have hm : x ∈ ({u,w}:Finset V) := eq ▸ (show x ∈ ({x,y}:Finset V) from by simp)
        rcases Finset.mem_insert.mp hm with rfl | h
        · exact dx.1 hu
        · exact dx.1 ((Finset.mem_singleton.mp h).symm ▸ hw)
      simp [Adj,pathEdges,ne]

private theorem empty_later (c : V → ℕ) (x : V) (s : List V) :
    later c ∅ x s = s.filter (fun z => decide (c x ≠ c z)) := by
  classical
  apply List.filter_congr
  intro z _
  simp only [empty_adj]

/-- A terminal vertex of a strong ordering can be replaced by a path of
twins. Its external neighbors see the path consecutively. -/
private theorem grow_terminal_path (c : V → ℕ) (pre : List V) (y : V) (t : List V)
    (hd : (pre++y::t).Nodup) (mono : ∀ z ∈ y::t, c z=c y)
    (base : Strong c ∅ (pre++[y])) :
    Strong c (pathEdges (y::t)) (pre++y::t) := by
  classical
  induction pre with
  | nil => exact strong_path c (c y) (y::t) hd mono
  | cons x pre ih =>
    have nd := List.nodup_cons.mp hd
    have out : x ∉ y::t := fun hx => nd.1 (List.mem_append_right _ hx)
    have ef : later c (pathEdges (y::t)) x (pre++y::t) =
        (pre.filter (fun z => decide (c x ≠ c z))) ++ (y::t).filter (fun z => decide (c x ≠ c z)) := by
      rw [← List.filter_append]
      apply List.filter_congr
      intro z _
      simp only [outside_path out z]
    have old := base.1.imp (S:=Adj c (pathEdges (y::t)))
      (fun a b h => cross_adj _ (empty_adj.mp h))
    change (later c ∅ x (pre++[y])).IsChain (Adj c (pathEdges (y::t))) at old
    rw [empty_later, List.filter_append] at old
    refine ⟨?_, ih nd.2 base.2⟩
    change (later c (pathEdges (y::t)) x (pre++y::t)).IsChain _
    rw [ef]
    by_cases same : c x = c y
    · have none : (y::t).filter (fun z => decide (c x ≠ c z)) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro z hz
        simp [same,mono z hz]
      rw [none, List.append_nil]
      simpa [same] using old
    · have full : (y::t).filter (fun z => decide (c x ≠ c z)) = y::t := by
        apply List.filter_eq_self.mpr
        intro z hz
        simp [mono z hz,same]
      rw [full]
      have old' : ((pre.filter (fun z => decide (c x ≠ c z))) ++ [y]).IsChain (Adj c (pathEdges (y::t))) := by
        simpa [same] using old
      have path : ([y]++t).IsChain (Adj c (pathEdges (y::t))) :=
        path_chain c (y::t) (List.nodup_append'.mp nd.2).2.1
      simpa only [List.append_assoc, List.singleton_append] using old'.append_overlap path (by simp)

private theorem of_color_order (c : V → ℕ) (s : List V)
    (h : Multipartite.StrongColorOrder (s.map c)) : Strong c ∅ s := by
  classical
  induction s with
  | nil => trivial
  | cons x t ih =>
    have hs := h [] (c x) (t.map c) rfl
    have he : (later c ∅ x t).map c = (t.map c).filter (fun z => z != c x) := by
      rw [empty_later, List.filter_map]
      apply congrArg (List.map c)
      apply List.filter_congr
      intro z _
      by_cases eq : c z = c x
      · simp [eq]
      · have be : (c z == c x) = false := beq_eq_false_iff_ne.mpr eq
        simp [bne,be,Ne.symm eq]
    refine ⟨?_,ih ?_⟩
    · rw [← he, List.isChain_map] at hs
      exact hs.imp (fun a b hab => cross_adj _ hab)
    · intro pre v tail eq
      exact h (c x::pre) v tail (by simp [eq])

/-- Every member of the chosen edge set inserts an original missing edge
between two distinct vertices of the prescribed fixed graph. -/
def Allowed (c : V → ℕ) (vertices : List V) (E : Edges V) : Prop :=
  ∀ e ∈ E, ∃ x ∈ vertices, ∃ y ∈ vertices, x ≠ y ∧ c x=c y ∧ e={x,y}

private theorem path_allowed (c : V → ℕ) (b : ℕ) (s : List V) (hd : s.Nodup)
    (mono : ∀ x ∈ s, c x=b) : Allowed c s (pathEdges s) := by
  intro e he
  induction s using List.twoStepInduction with
  | nil | singleton => simp [pathEdges] at he
  | cons_cons x y t _ ih =>
    have nd := List.nodup_cons.mp hd
    rcases Finset.mem_insert.mp he with rfl | he
    · exact ⟨x,by simp,y,by simp,fun h => nd.1 (by simp [h]),
        (mono x (by simp)).trans (mono y (by simp)).symm,rfl⟩
    · obtain ⟨u,hu,v,hv,h⟩ := ih y nd.2 (fun z hz => mono z (by simp [hz])) he
      exact ⟨u,List.mem_cons_of_mem _ hu,v,List.mem_cons_of_mem _ hv,h⟩

/-- A budget counts different unordered edges added on the original labeled
vertex set. The resulting graph is tested against the paper's component-based
perfect cancellation order. -/
def CanComplete (c : V → ℕ) (vertices : List V) (budget : ℕ) : Prop :=
  ∃ E : Edges V, Allowed c vertices E ∧ E.card ≤ budget ∧
    ∃ order, order.Perm vertices ∧ Ordering c E order

private theorem part_le_inventory (ps : Multipartite.Parts) (p : ℕ × ℕ) (hp : p ∈ ps) :
    p.2 ≤ (Multipartite.inventory ps).length := by
  induction ps with
  | nil => simp at hp
  | cons q ps ih =>
    change _ ≤ (List.replicate q.2 q.1 ++ Multipartite.inventory ps).length
    rw [List.length_append, List.length_replicate]
    rcases List.mem_cons.mp hp with rfl | h
    · omega
    · have := ih h; omega

private theorem add_small_part (a b d k : ℕ) (ps : Multipartite.Parts) (sum : d+k=b) :
    ((Multipartite.shape a d ps)++List.replicate k 1).Perm (Multipartite.shape a b ps) := by
  apply List.perm_iff_count.mpr
  intro j
  simp only [Multipartite.shape, List.count_append, List.count_replicate]
  by_cases eq : 1 == j
  · simp [eq]; omega
  · simp [eq]

omit [DecidableEq V] in
private theorem pop_map (c : V → ℕ) (i : ℕ) (ord : List V) :
    pop c i ord = (ord.map c).count i := by
  simp only [pop, List.count_eq_countP, List.countP_map]
  apply List.countP_congr
  intro z _
  simp

private theorem minor_count (c : V → ℕ) (s : List V) (hd : s.Nodup) (a b : ℕ)
    (ps : Multipartite.Parts) (valid : Multipartite.Valid b ps)
    (perm : (s.map c).Perm (Multipartite.shape a b ps)) :
    (minorSet c s).card = (Multipartite.inventory ps).length := by
  let P (z : ℕ) := decide (z ≠ 0 ∧ z ≠ 1)
  have he : (minorSet c s).card = (s.map c).countP P := by
    rw [minorSet, List.toFinset_card_of_nodup (hd.filter _), ← List.countP_eq_length_filter,
      List.countP_map]
    rfl
  rw [he,perm.countP_eq P]
  have clean := Multipartite.inventory_clean b ps valid
  have main : (Multipartite.inventory ps).countP P = (Multipartite.inventory ps).length := by
    apply List.countP_eq_length.mpr
    intro q hq
    apply decide_eq_true
    constructor
    · rintro rfl; exact clean.1 hq
    · rintro rfl; exact clean.2 hq
  simpa [Multipartite.shape, List.countP_replicate,P] using main

open Multipartite (Parts Valid shape inventory)

/-- Exact fixed-vertex edge-completion number for all complete multipartite
graphs. The only inputs are the original named vertices and their part sizes. -/
theorem edge_completion_iff (c : V → ℕ) (vertices : List V) (hd : vertices.Nodup)
    (a b k : ℕ) (ps : Parts) (ba : b ≤ a) (valid : Valid b ps)
    (labels : (vertices.map c).Perm (shape a b ps)) :
    CanComplete c vertices k ↔ b-1-(inventory ps).length ≤ k := by
  classical
  constructor
  · rintro ⟨E, _, card, ord, po, order⟩
    have hp := (po.map c).trans labels
    have hdo := po.nodup_iff.mpr hd
    have hl := edge_lower_bound c E ord hdo order
    obtain ⟨h0,h1⟩ := Multipartite.shape_01 a b ps valid
    rw [pop_map, pop_map, List.perm_iff_count.mp hp 0, List.perm_iff_count.mp hp 1,
      h0,h1, Nat.min_eq_right ba, minor_count c ord hdo a b ps valid hp] at hl
    exact hl.trans card
  · intro budget
    let d := (inventory ps).length+1
    by_cases good : b ≤ d
    · obtain ⟨w,perm,hs,_⟩ := Multipartite.strong_color_construction a b ps ba valid good
      obtain ⟨ord, po, hm⟩ := Multipartite.lift_order c (labels.trans perm.symm) vertices rfl
      exact ⟨∅, by simp [Allowed], by simp, ord,po.symm,
        strong_ordering (of_color_order c ord (hm ▸ hs))⟩
    · let n := b-d
      have db : d+n=b := by dsimp [n]; omega
      have small : Valid d ps := ⟨valid.1,fun p hp =>
        ⟨(valid.2 p hp).1, (part_le_inventory ps p hp).trans (Nat.le_succ _)⟩⟩
      obtain ⟨w,perm,hs,tail⟩ := Multipartite.strong_color_construction a d ps (by omega) small le_rfl
      obtain ⟨pre,hw⟩ := tail rfl
      have newPerm := (perm.append_right (List.replicate n 1)).trans (add_small_part a b d n ps db)
      obtain ⟨ord,po,hm⟩ := Multipartite.lift_order c (labels.trans newPerm.symm) vertices rfl
      have hm' : ord.map c = pre ++ 1 :: List.replicate n 1 := by
        simpa [hw, List.append_assoc] using hm
      obtain ⟨front,block,ordEq,frontEq,blockEq⟩ := List.map_eq_append_iff.mp hm'
      cases block with
      | nil => simp at blockEq
      | cons y t =>
        obtain ⟨cy,ct⟩ := List.cons.inj blockEq
        have tn : t.length=n := by simpa using congrArg List.length ct
        have nd : (front++y::t).Nodup := ordEq ▸ po.nodup_iff.mp hd
        have mono : ∀ z ∈ y::t, c z=c y := by
          intro z hz
          rcases List.mem_cons.mp hz with rfl | hx
          · rfl
          · have h : c z ∈ List.replicate n 1 := ct ▸ List.mem_map_of_mem hx
            exact (List.eq_of_mem_replicate h).trans cy.symm
        have base : Strong c ∅ (front++[y]) := of_color_order c _ (by simpa [frontEq,cy,hw] using hs)
        let E := pathEdges (y::t)
        have validE := path_allowed c (c y) (y::t) (List.nodup_append'.mp nd).2.1 mono
        have sub (z : V) (h : z ∈ y::t) : z ∈ vertices :=
          po.mem_iff.mpr (ordEq ▸ List.mem_append_right front h)
        refine ⟨E,?_,?_,ord,po.symm,?_⟩
        · intro e he
          obtain ⟨x,hx,z,hz,others⟩ := validE e he
          exact ⟨x,sub x hx,z,sub z hz,others⟩
        · have hc := path_card y t
          change (pathEdges (y::t)).card ≤ k
          dsimp [d] at db
          omega
        · rw [ordEq]
          exact strong_ordering (grow_terminal_path c front y t nd mono base)

theorem least_inserted_edges (c : V → ℕ) (vertices : List V) (hd : vertices.Nodup)
    (a b : ℕ) (ps : Parts) (ba : b ≤ a) (valid : Valid b ps)
    (labels : (vertices.map c).Perm (shape a b ps)) :
    IsLeast {k | CanComplete c vertices k} (b-1-(inventory ps).length) :=
  ⟨(edge_completion_iff c vertices hd a b _ ps ba valid labels).mpr le_rfl,
    fun _ hk => (edge_completion_iff c vertices hd a b _ ps ba valid labels).mp hk⟩

#print axioms edge_completion_iff
#print axioms least_inserted_edges

end EdgeCompletion

import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card

/-! Odd-parity output bounds for reversible graphic CNOT networks. -/
open Finset
open scoped symmDiff
namespace GraphicParity

variable {V : Type} [DecidableEq V]

/-- Binary wire terms are supports of linear forms over the field of two elements. -/
abbrev Term (V : Type) := Finset V
abbrev State (V : Type) := V → Term V

def initial (v : V) : Term V := {v}

structure Gate (V : Type) where
  control : V
  target : V
  distinct : control ≠ target

def output (s : State V) (g : Gate V) := s g.target ∆ s g.control

def applyGate (s : State V) (g : Gate V) : State V := Function.update s g.target (output s g)

/-- The list of all CNOT output terms, in their chronological order. -/
def outputs (s : State V) : List (Gate V) → List (Term V)
  | [] => []
  | g::t => output s g :: outputs (applyGate s g) t

def run (s : State V) : List (Gate V) → State V
  | [] => s
  | g::t => run (applyGate s g) t

theorem card_xor (a b : Term V) : (a ∆ b).card % 2 = (a.card + b.card) % 2 := by
  have dis : Disjoint (a \ b) (b \ a) := by
    refine Finset.disjoint_left.mpr ?_
    intro x ha hb
    exact (mem_sdiff.mp ha).2 (mem_sdiff.mp hb).1
  have h := card_union_of_disjoint dis
  change (a ∆ b).card = _ at h
  have h1 := card_sdiff_add_card_inter a b
  have h2 := card_sdiff_add_card_inter b a
  rw [inter_comm b a] at h2
  omega

/-- Birth outputs are precisely the newly even targets obtained from two odd wires. -/
def births (s : State V) : List (Gate V) → List (Term V)
  | [] => []
  | g::t => if (s g.target).card % 2 = 1 ∧ (s g.control).card % 2 = 1
            then output s g :: births (applyGate s g) t else births (applyGate s g) t

/-- All sums over F₂ of sublists of the generators. -/
private def span : List (Term V) → Finset (Term V)
  | [] => {∅}
  | x::xs => span xs ∪ (span xs).image (fun y => y ∆ x)

private theorem span_zero (xs : List (Term V)) : ∅ ∈ span xs := by
  induction xs with
  | nil => simp [span]
  | cons x xs ih => exact mem_union_left _ ih

private theorem span_contains (xs : List (Term V)) {x : Term V} (hx : x ∈ xs) : x ∈ span xs := by
  induction xs with
  | nil => simp at hx
  | cons z zs ih =>
    rcases List.mem_cons.mp hx with rfl | h
    · apply mem_union_right
      exact mem_image.mpr ⟨∅,span_zero _, by simp⟩
    · exact mem_union_left _ (ih h)

private theorem span_add (xs : List (Term V)) {a b : Term V} (ha : a ∈ span xs) (hb : b ∈ span xs) :
    a ∆ b ∈ span xs := by
  induction xs generalizing a b with
  | nil =>
    simp [span] at ha hb
    simp [span,ha,hb]
  | cons x xs ih =>
    rcases mem_union.mp ha with ha | ha <;> rcases mem_union.mp hb with hb | hb
    · exact mem_union_left _ (ih ha hb)
    · obtain ⟨w,hw,rfl⟩ := mem_image.mp hb
      exact mem_union_right _ (mem_image.mpr ⟨a ∆ w,ih ha hw,symmDiff_assoc ..⟩)
    · obtain ⟨w,hw,rfl⟩ := mem_image.mp ha
      exact mem_union_right _ (mem_image.mpr ⟨w ∆ b,ih hw hb,by rw [symmDiff_right_comm]⟩)
    · obtain ⟨w,hw,rfl⟩ := mem_image.mp ha
      obtain ⟨z,hz,rfl⟩ := mem_image.mp hb
      apply mem_union_left
      simpa only [symmDiff_symmDiff_symmDiff_comm w x z x, symmDiff_self, symmDiff_bot] using ih hw hz

private theorem span_size (xs : List (Term V)) : (span xs).card ≤ 2^xs.length := by
  induction xs with
  | nil => simp [span]
  | cons x xs ih =>
    have h := card_union_le (span xs) ((span xs).image (fun y => y ∆ x))
    have hi : ((span xs).image (fun y => y ∆ x)).card ≤ (span xs).card := card_image_le
    change _ ≤ 2^(xs.length+1)
    rw [pow_succ]
    change (span xs ∪ (span xs).image (fun y => y ∆ x)).card ≤ _
    omega

private theorem even_outputs_from_births (S : Finset (Term V))
    (add : ∀ a ∈ S, ∀ b ∈ S, a ∆ b ∈ S) (s : State V) (gates : List (Gate V))
    (prior : ∀ v, (s v).card%2=0 → s v∈S) (birth : ∀ w ∈ births s gates, w ∈ S) :
    ∀ w ∈ outputs s gates, w.card%2=0 → w∈S := by
  induction gates generalizing s with
  | nil => simp [outputs]
  | cons g gs ih =>
    let post := applyGate s g
    have parity := card_xor (s g.target) (s g.control)
    change (output s g).card % 2 = _ at parity
    have new : (output s g).card%2=0 → output s g∈S := by
      intro even
      by_cases ht : (s g.target).card%2=0
      · exact add _ (prior _ ht) _ (prior _ (by omega))
      · apply birth
        have both : (s g.target).card % 2 = 1 ∧ (s g.control).card % 2 = 1 := by omega
        simp [births,both]
    have pre' : ∀ v, (post v).card%2=0 → post v∈S := by
      intro v
      by_cases h : v=g.target
      · subst v; simpa [post,applyGate] using new
      · simpa [post,applyGate,h] using prior v
    have gen : ∀ z∈births post gs, z∈S := by
      intro z hz
      apply birth
      simp only [births]
      split <;> simp_all [post]
    intro w hw even
    rcases List.mem_cons.mp hw with rfl | hw
    · exact new even
    · exact ih post pre' gen w hw even

private theorem all_even (gs : List (Gate V)) {w : Term V} (hw : w∈outputs initial gs)
    (even : w.card%2=0) : w∈span (births initial gs) :=
  even_outputs_from_births _ (fun _ a _ b => span_add _ a b) initial gs
    (by simp [initial]) (fun _ h => span_contains _ h) w hw even

/-- The parity attached to the endpoints of an edge; it is empty at equal endpoints. -/
def pair (x y : V) : Term V := ({x} : Finset V) ∆ {y}

theorem pair_comp (x y z : V) : pair x y ∆ pair y z = pair x z := by
  simp only [pair, ← symmDiff_assoc, symmDiff_symmDiff_cancel_right]

private theorem pair_even (x y : V) : (pair x y).card%2=0 := by
  simp [pair, card_xor]

/-- A path in the original graph whose edges are required parity terms. -/
inductive ConnectedTo (targets : Finset (Term V)) (root : V) : V → Prop
  | root : ConnectedTo targets root root
  | edge {x y} : ConnectedTo targets root x → pair x y ∈ targets → ConnectedTo targets root y

private theorem pair_in_span (S : List (Term V)) (T : Finset (Term V))
    (covered : ∀ e∈T,e∈span S) (r v : V) (h : ConnectedTo T r v) : pair r v ∈ span S := by
  induction h with
  | root => simpa [pair] using span_zero S
  | edge _ he ih => simpa only [pair_comp] using span_add S ih (covered _ he)

private theorem erase_flip {w : Term V} {r v : V} (different : v ≠ r) (fresh : v ∉ w.erase r) :
    (w ∆ pair r v).erase r = insert v (w.erase r) := by
  have hw : v ∉ w := fun hm => fresh (mem_erase.mpr ⟨different,hm⟩)
  ext z
  by_cases hr : z=r
  · subst z; simp [different.symm]
  · by_cases hv : z=v
    · subst z; simp [pair,mem_symmDiff,different,hw]
    · simp [pair,mem_symmDiff,hr,hv]

private theorem spanning_count_on (D : Finset V) (r : V) (hr : r ∈ D) (B : List (Term V))
    (gen : ∀ v ∈ D, pair r v ∈ span B) : D.card - 1 ≤ B.length := by
  have projected (U : Finset V) (within : U ⊆ D) (hU : r ∉ U) : ∃ w ∈ span B, w.erase r = U := by
    induction U using Finset.induction_on with
    | empty => exact ⟨∅,span_zero _,by simp⟩
    | @insert v U fresh ih =>
      obtain ⟨w,hw,eq⟩ := ih (fun _ h => within (mem_insert_of_mem h)) (fun hm => hU (mem_insert_of_mem hm))
      have diff : v ≠ r := by rintro rfl; exact hU (by simp)
      exact ⟨w ∆ pair r v,span_add _ hw (gen v (within (mem_insert_self ..))),by rw [erase_flip diff (eq ▸ fresh),eq]⟩
  have sub : (D.erase r).powerset ⊆ (span B).image (fun w => w.erase r) := by
    intro U hU
    have subset := mem_powerset.mp hU
    exact mem_image.mpr (projected U (subset.trans (erase_subset ..)) (fun hm => (notMem_erase r D) (subset hm)))
  have hs := (card_le_card sub).trans (card_image_le.trans (span_size B))
  rw [card_powerset,card_erase_of_mem hr] at hs
  exact (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp hs

private theorem spanning_count [Fintype V] (r : V) (B : List (Term V))
    (gen : ∀ v : V, pair r v ∈ span B) : Fintype.card V - 1 ≤ B.length := by
  simpa only [card_univ] using spanning_count_on univ r (mem_univ _) B (fun v _ => gen v)

private theorem birth_lower [Fintype V] (r : V) (T : Finset (Term V)) (gs : List (Gate V))
    (connected : ∀ v, ConnectedTo T r v) (even : ∀ w∈T,w.card%2=0)
    (covered : ∀ w∈T,w ∈ outputs initial gs) :
    Fintype.card V - 1 ≤ (births initial gs).length :=
  spanning_count r _ fun v => pair_in_span _ T
    (fun w hw => all_even gs (covered w hw) (even w hw)) r v (connected v)

private def oddPop [Fintype V] (s : State V) := (univ.filter (fun v => (s v).card%2=1)).card

private theorem pop_step [Fintype V] (s : State V) (g : Gate V) :
    oddPop s + (output s g).card%2 = oddPop (applyGate s g) + (s g.target).card%2 := by
  let a := univ.erase g.target
  have hf : a.filter (fun v => (s v).card%2=1) =
      a.filter (fun v => (applyGate s g v).card%2=1) := by
    apply filter_congr
    intro v hv
    simp [applyGate,(mem_erase.mp hv).1]
  have hsplit : univ = insert g.target a := (insert_erase (mem_univ g.target)).symm
  unfold oddPop
  rw [hsplit,filter_insert,filter_insert]
  have absent (f : V → Prop) [DecidablePred f] : g.target ∉ a.filter f :=
    fun h => (notMem_erase g.target univ) (mem_filter.mp h).1
  have post : applyGate s g g.target = output s g := Function.update_self ..
  rw [post]
  by_cases i : (s g.target).card%2=1 <;> by_cases o : (output s g).card%2=1 <;>
    simp only [i,o,if_true,if_false,card_insert_of_notMem (absent _),hf] <;> omega

/-- The number of even target wires changed back to odd by a CNOT. -/
private def deaths (s : State V) : List (Gate V) → ℕ
  | [] => 0
  | g::t => (if (s g.target).card%2=0 ∧ (s g.control).card%2=1 then 1 else 0) +
    deaths (applyGate s g) t

private theorem balance [Fintype V] (s : State V) (gs : List (Gate V)) :
    oddPop (run s gs) + (births s gs).length = oddPop s + deaths s gs := by
  induction gs generalizing s with
  | nil => simp [run,births,deaths]
  | cons g gs ih =>
    have next := ih (applyGate s g)
    have step := pop_step s g
    have pp := card_xor (s g.target) (s g.control)
    change (output s g).card%2 = _ at pp
    simp only [run,births,deaths]
    split <;> split <;> (try simp only [List.length_cons]) <;> omega

private def oddOutputs (s : State V) (gs : List (Gate V)) : ℕ :=
  (outputs s gs).countP (fun t => decide (t.card%2=1))

private theorem deaths_le_odd (s : State V) (gs : List (Gate V)) :
    deaths s gs ≤ oddOutputs s gs := by
  induction gs generalizing s with
  | nil => simp [deaths,oddOutputs,outputs]
  | cons g gs ih =>
    have next := ih (applyGate s g)
    have pp := card_xor (s g.target) (s g.control)
    change (output s g).card%2 = _ at pp
    simp only [deaths,oddOutputs,outputs,List.countP_cons,decide_eq_true_eq] at *
    split <;> split <;> omega

/-- Every restored CNOT network covering the required edge parities of a
connected graph must produce an odd-weight target at least |V|−1 times. -/
theorem odd_output_lower_bound [Fintype V] (r : V) (T : Finset (Term V))
    (gs : List (Gate V)) (connected : ∀ v, ConnectedTo T r v)
    (even : ∀ w∈T,w.card%2=0) (covered : ∀ w∈T,w ∈ outputs initial gs)
    (restored : run initial gs = initial) :
    Fintype.card V - 1 ≤ (outputs initial gs).countP (fun w => decide (w.card%2=1)) := by
  have hb := birth_lower r T gs connected even covered
  have hr := balance initial gs
  rw [restored] at hr
  have ho := deaths_le_odd initial gs
  unfold oddOutputs at ho
  omega

#print axioms odd_output_lower_bound

/-- A closed CNOT circuit realizes a graph by visiting each required edge parity. -/
def Network (T : Finset (Term V)) (gs : List (Gate V)) : Prop :=
  run initial gs = initial ∧ ∀ w∈T, w ∈ outputs initial gs

def evens (s : State V) (gs : List (Gate V)) :=
  (outputs s gs).filter (fun w => decide (w.card%2=0))

private theorem length_outputs (s : State V) (gs : List (Gate V)) :
    (outputs s gs).length=gs.length := by
  induction gs generalizing s with
  | nil => rfl
  | cons g gs ih => simp [outputs,ih]

private theorem counts_split (s : State V) (gs : List (Gate V)) :
    (evens s gs).length + oddOutputs s gs = gs.length := by
  rw [← length_outputs s gs]
  unfold evens oddOutputs
  generalize outputs s gs = l
  induction l with
  | nil => rfl
  | cons w l ih =>
    by_cases h : w.card%2=0
    · simp [h]; omega
    · have yes : w.card%2=1 := by omega
      simp [yes]; omega

private theorem requested_subset (T : Finset (Term V)) (gs : List (Gate V))
    (even : ∀ w∈T,w.card%2=0) (net : Network T gs) : T ⊆ (evens initial gs).toFinset := by
  intro w hw
  simp [evens,net.2 w hw,even w hw]

/-- The usual |E|+|V|−1 lower bound, with odd target gates paying the second term. -/
theorem network_lower_bound [Fintype V] (r : V) (T : Finset (Term V)) (gs : List (Gate V))
    (connected : ∀ v, ConnectedTo T r v) (even : ∀ w∈T,w.card%2=0) (net : Network T gs) :
    T.card + (Fintype.card V-1) ≤ gs.length := by
  have he := (card_le_card (requested_subset T gs even net)).trans (List.toFinset_card_le _)
  have ho : Fintype.card V-1 ≤ oddOutputs initial gs :=
    odd_output_lower_bound r T gs connected even net.2 net.1
  have split := counts_split initial gs
  omega

/-- Equality forces every even intermediate gate output to be a required term. -/
theorem even_output_saturation [Fintype V] (r : V) (T : Finset (Term V)) (gs : List (Gate V))
    (connected : ∀ v, ConnectedTo T r v) (even : ∀ w∈T,w.card%2=0) (net : Network T gs)
    (tight : gs.length ≤ T.card+(Fintype.card V-1)) :
    ∀ w∈outputs initial gs, w.card%2=0 → w∈T := by
  have sub := requested_subset T gs even net
  have ho : Fintype.card V-1 ≤ oddOutputs initial gs :=
    odd_output_lower_bound r T gs connected even net.2 net.1
  have h := counts_split initial gs
  have card : (evens initial gs).toFinset.card ≤ T.card := (List.toFinset_card_le _).trans (by omega)
  have eq := Finset.eq_of_subset_of_card_le sub card
  intro w hw hp
  rw [eq]
  simp [evens,hw,hp]

/-- No sum of two requested parity terms is requested. For edge terms this
is exactly the obstruction supplied by a triangle-free graph. -/
def SumFree (T : Finset (Term V)) : Prop := ∀ a∈T, ∀ b∈T, a ∆ b ∉ T

private theorem every_even_is_born (T : Finset (Term V)) (s : State V) (gs : List (Gate V))
    (free : SumFree T) (prior : ∀ v, (s v).card%2=0 → s v∈T)
    (sat : ∀ w∈outputs s gs, w.card%2=0 → w∈T) :
    (births s gs).length=(evens s gs).length := by
  induction gs generalizing s with
  | nil => rfl
  | cons g gs ih =>
    let u := applyGate s g
    have new (h : (output s g).card%2=0) : output s g∈T := sat _ (by simp [outputs]) h
    have pre' : ∀ v, (u v).card%2=0 → u v∈T := by
      intro v
      by_cases hv : v=g.target
      · subst v; simpa [u,applyGate] using new
      · simpa [u,applyGate,hv] using prior v
    have sat' := fun w (hw : w∈outputs u gs) => sat w (List.mem_cons_of_mem _ hw)
    have tail := ih u pre' sat'
    have hx := card_xor (s g.target) (s g.control)
    change (output s g).card%2 = _ at hx
    have equiv : ((s g.target).card%2=1 ∧ (s g.control).card%2=1) ↔ (output s g).card%2=0 := by
      constructor
      · omega
      · intro he
        by_contra! bad
        have both : (s g.target).card%2=0 ∧ (s g.control).card%2=0 := by omega
        exact free _ (prior _ both.1) _ (prior _ both.2) (new he)
    change (births (applyGate s g) gs).length=(evens (applyGate s g) gs).length at tail
    by_cases ho : (output s g).card%2=0
    · simp [births,evens,outputs,ho,equiv.mpr ho] at tail ⊢
      exact tail
    · have hn := mt equiv.mp ho
      simp [births,evens,outputs,ho,hn] at tail ⊢
      exact tail

/-- At least one extra gate is necessary for a connected graph with a cycle
when its set of requested (even) terms is sum-free. -/
theorem sumfree_extra_gate [Fintype V] (r : V) (T : Finset (Term V)) (gs : List (Gate V))
    (connected : ∀ v, ConnectedTo T r v) (even : ∀ w∈T,w.card%2=0)
    (free : SumFree T) (hm : Fintype.card V ≤ T.card) (net : Network T gs) :
    T.card + Fintype.card V ≤ gs.length := by
  have pos : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨r⟩
  by_contra! few
  have sat := even_output_saturation r T gs connected even net (by omega)
  have hb := every_even_is_born T initial gs free (by simp [initial]) sat
  have bal := balance initial gs
  rw [net.1] at bal
  have he := (card_le_card (requested_subset T gs even net)).trans (List.toFinset_card_le _)
  have ho := deaths_le_odd initial gs
  have hs := counts_split initial gs
  omega

/-- A finite simple graph is represented by the two-element supports of its edges. -/
def SimpleEdges (T : Finset (Term V)) : Prop := ∀ w∈T, w.card=2

def TriangleFree (T : Finset (Term V)) : Prop :=
  ∀ a b c : V, ({a,b} : Finset V) ∈ T → ({b,c} : Finset V) ∈ T → ({c,a} : Finset V) ∉ T

theorem sumfree_of_triangleFree (T : Finset (Term V)) (simple : SimpleEdges T)
    (tf : TriangleFree T) : SumFree T := by
  intro e he f hf hs
  have d : Disjoint (e \ f) (f \ e) :=
    Finset.disjoint_left.mpr (fun _ h₁ h₂ => (mem_sdiff.mp h₁).2 (mem_sdiff.mp h₂).1)
  have h := card_union_of_disjoint d
  change (e ∆ f).card = _ at h
  have ce := simple _ he
  have cf := simple _ hf
  have cs := simple _ hs
  have le := card_sdiff_add_card_inter e f
  have lf := card_sdiff_add_card_inter f e
  rw [inter_comm f e] at lf
  obtain ⟨a,ha⟩ := card_eq_one.mp (by omega : (e \ f).card=1)
  obtain ⟨b,hb⟩ := card_eq_one.mp (by omega : (e ∩ f).card=1)
  obtain ⟨c,hc⟩ := card_eq_one.mp (by omega : (f \ e).card=1)
  have eab : e = {a,b} := by rw [← sdiff_union_inter e f,ha,hb]; simp [Finset.pair_comm b a]
  have fbc : f = {b,c} := by
    rw [← sdiff_union_inter f e,hc,inter_comm f e,hb]
    simp
  have eac : e ∆ f = {c,a} := by
    change e \ f ∪ f \ e = _
    rw [ha,hc]; simp
  exact tf a b c (eab ▸ he) (fbc ▸ hf) (eac ▸ hs)

/-- Direct CNOT lower bound for every connected triangle-free graph with m ≥ n. -/
theorem triangle_free_gate_lower [Fintype V] (r : V) (T : Finset (Term V)) (gs : List (Gate V))
    (connected : ∀ v, ConnectedTo T r v) (simple : SimpleEdges T) (tf : TriangleFree T)
    (hasCycle : Fintype.card V ≤ T.card) (net : Network T gs) :
    T.card + Fintype.card V ≤ gs.length :=
  sumfree_extra_gate r T gs connected (fun w hw => by rw [simple w hw])
    (sumfree_of_triangleFree T simple tf) hasCycle net

#print axioms even_output_saturation
#print axioms triangle_free_gate_lower


theorem pair_of_ne {x y : V} (ne : x ≠ y) : pair x y = {x,y} := by
  ext z
  by_cases h : z=x
  · subst z; simp [pair,mem_symmDiff,ne]
  · simp [pair,mem_symmDiff,h]

private theorem cancel_gate (s : State V) (g : Gate V) : applyGate (applyGate s g) g = s := by
  funext v
  by_cases eq : v=g.target
  · subst v; simp [applyGate,output,g.distinct]
  · simp [applyGate,eq]

/-- Generate each requested edge and uncompute it immediately. -/
theorem two_per_edge (T : Finset (Term V)) (simple : SimpleEdges T) :
    ∃ gs : List (Gate V), Network T gs ∧ gs.length=2*T.card := by
  induction T using Finset.induction_on with
  | empty => exact ⟨[],⟨rfl,by simp⟩,by simp⟩
  | @insert e T fresh ih =>
    obtain ⟨x,y,ne,eq⟩ := card_eq_two.mp (simple e (by simp))
    obtain ⟨gs,net,number⟩ := ih (fun w hw => simple w (mem_insert_of_mem hw))
    let g : Gate V := ⟨y,x,ne.symm⟩
    have o : output initial g=e := (pair_of_ne ne).trans eq.symm
    refine ⟨g::g::gs,⟨?_,?_⟩,?_⟩
    · simpa [run,cancel_gate] using net.1
    · intro w hw
      rcases mem_insert.mp hw with rfl | h
      · simp [outputs,o]
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ ((cancel_gate initial g).symm ▸ net.2 w h))
    · simp [number,card_insert_of_notMem fresh]; omega

/-- A finite connected triangle-free graph admits a perfect graphic parity network
exactly when it has |V|−1 edges, the ordinary tree criterion. -/
theorem triangle_free_perfect_iff [Fintype V] (r : V) (T : Finset (Term V))
    (connected : ∀ v, ConnectedTo T r v) (simple : SimpleEdges T) (tf : TriangleFree T) :
    (∃ gs : List (Gate V), Network T gs ∧ gs.length=T.card+(Fintype.card V-1)) ↔
      T.card=Fintype.card V-1 := by
  obtain ⟨trivialNet,nt,lt⟩ := two_per_edge T simple
  have h := network_lower_bound r T trivialNet connected (fun w hw => by rw [simple w hw]) nt
  have pos := Fintype.card_pos_iff.mpr ⟨r⟩
  constructor
  · rintro ⟨gs,hn,size⟩
    by_contra neq
    have cycle : Fintype.card V≤T.card := by omega
    have := triangle_free_gate_lower r T gs connected simple tf cycle hn
    omega
  · intro size
    exact ⟨trivialNet,nt,by omega⟩

/-- In particular every connected triangle-free graph with exactly one
independent cycle has exact optimal CNOT complexity 2|E|. -/
theorem triangle_free_unicyclic_optimum [Fintype V] (r : V) (T : Finset (Term V))
    (connected : ∀ v, ConnectedTo T r v) (simple : SimpleEdges T) (tf : TriangleFree T)
    (unicyclic : T.card=Fintype.card V) :
    IsLeast {k | ∃ gs : List (Gate V), Network T gs ∧ gs.length=k} (2*T.card) := by
  refine ⟨two_per_edge T simple, ?_⟩
  rintro k ⟨gs,net,rfl⟩
  have := triangle_free_gate_lower r T gs connected simple tf unicyclic.ge net
  omega

#print axioms triangle_free_perfect_iff
#print axioms triangle_free_unicyclic_optimum


theorem run_append (s : State V) (u v : List (Gate V)) :
    run s (u++v) = run (run s u) v := by
  induction u generalizing s with
  | nil => rfl
  | cons g u ih => exact ih (applyGate s g)

theorem outputs_append (s : State V) (u v : List (Gate V)) :
    outputs s (u++v) = outputs s u ++ outputs (run s u) v := by
  induction u generalizing s with
  | nil => rfl
  | cons g u ih => simp [outputs,run,ih]

/-- All edges of the complete bipartite graph between hubs a,b and leaves X. -/
def twoHubEdges (a b : V) (X : Finset V) : Finset (Term V) :=
  X.image (pair a) ∪ X.image (pair b)

theorem pair_same_root {a x y : V} (h : pair a x = pair a y) : x=y := by
  have e := congrArg (fun z : Finset V => ({a}:Finset V) ∆ z) h
  simpa [pair] using e

private theorem twoHub_count (a b : V) (X : Finset V) (ne : a ≠ b)
    (ha : a ∉ X) : (twoHubEdges a b X).card=2*X.card := by
  have dis : Disjoint (X.image (pair a)) (X.image (pair b)) := by
    refine disjoint_left.mpr ?_
    intro e ae be
    obtain ⟨x,hx,rfl⟩ := mem_image.mp ae
    obtain ⟨y,hy,he⟩ := mem_image.mp be
    have ax : a≠x := by rintro rfl; exact ha hx
    have ay : a≠y := by rintro rfl; exact ha hy
    have ma : a∈pair a x := by simp [pair_of_ne ax]
    rw [← he] at ma
    simp [pair, mem_symmDiff,ne,ay] at ma
  rw [twoHubEdges,card_union_of_disjoint dis,Finset.card_image_of_injective _ (fun _ _ => pair_same_root),
    Finset.card_image_of_injective _ (fun _ _ => pair_same_root)]
  omega

private theorem hub_even_free (a b : V) (X : Finset V) (ne : a≠b) (ha : a ∉ X) (hb : b ∉ X) :
    SumFree (twoHubEdges a b X) := by
  let hubs : Finset V := {a,b}
  have one (e : Term V) (h : e ∈ twoHubEdges a b X) : (e ∩ hubs).card=1 := by
    rcases mem_union.mp h with h|h
    · obtain ⟨x,hx,rfl⟩ := mem_image.mp h
      have ax : a≠x := by rintro rfl; exact ha hx
      have bx : b≠x := by rintro rfl; exact hb hx
      have eq : pair a x ∩ hubs={a} := by
        rw [pair_of_ne ax]
        ext z
        by_cases za : z=a <;> by_cases zx : z=x <;> simp_all [hubs]
      simp [eq]
    · obtain ⟨x,hx,rfl⟩ := mem_image.mp h
      have ax : a≠x := by rintro rfl; exact ha hx
      have bx : b≠x := by rintro rfl; exact hb hx
      have eq : pair b x ∩ hubs={b} := by
        rw [pair_of_ne bx]
        ext z
        by_cases zb : z=b <;> by_cases zx : z=x <;> simp_all [hubs]
      simp [eq]
  intro e he f hf ef
  have id : (e ∆ f) ∩ hubs = (e ∩ hubs) ∆ (f ∩ hubs) := by
    ext z; simp only [mem_symmDiff,mem_inter]; tauto
  have hx := card_xor (e∩hubs) (f∩hubs)
  rw [← id,one _ ef,one _ he,one _ hf] at hx
  contradiction

private theorem middle (a b : V) (X : Finset V) (ab : a≠b) (ha : a∉X) (hb : b∉X)
    (s : State V) (as : s a={a}) (bs : s b=pair a b) (fresh : ∀ x∈X,s x={x}) :
    ∃ gs : List (Gate V), gs.length=3*X.card+1 ∧
      run s gs = Function.update s b {b} ∧
      ∀ x∈X, pair a x ∈ outputs s gs ∧ pair b x ∈ outputs s gs := by
  induction X using Finset.induction_on generalizing s with
  | empty =>
    let g : Gate V := ⟨a,b,ab⟩
    have out : output s g={b} := by
      change s b ∆ s a = {b}
      simp [bs,as,pair]
    exact ⟨[g],by simp,by change Function.update s b (output s g) = _; rw [out],by simp⟩
  | @insert x X absent ih =>
    have ax : a≠x := by rintro rfl; exact ha (by simp)
    have bx : b≠x := by rintro rfl; exact hb (by simp)
    let g₁ : Gate V := ⟨a,x,ax⟩
    let g₂ : Gate V := ⟨b,x,bx⟩
    let s₁ := applyGate s g₁
    let s₂ := applyGate s₁ g₂
    have sx := fresh x (by simp)
    have out₁ : output s g₁ = pair a x := by
      change s x ∆ s a = _
      rw [sx,as]; exact symmDiff_comm ..
    have state₁ : s₁=Function.update s x (pair a x) := by
      change Function.update s x (output s g₁) = _
      rw [out₁]
    have out₂ : output s₁ g₂ = pair b x := by
      change s₁ x ∆ s₁ b = _
      rw [state₁,Function.update_self,Function.update_of_ne bx,bs]
      simp [pair,symmDiff_symmDiff_symmDiff_comm, symmDiff_comm]
    have state₂ : s₂=Function.update s x (pair b x) := by
      change Function.update s₁ x (output s₁ g₂) = _
      rw [out₂,state₁,Function.update_idem]
    have sa : s₂ a={a} := by simpa [state₂,ax] using as
    have sb : s₂ b=pair a b := by simpa [state₂,bx] using bs
    have fs (z : V) (hz : z∈X) : s₂ z={z} := by
      have zx : z≠x := by rintro rfl; exact absent hz
      simpa [state₂,zx] using fresh z (mem_insert_of_mem hz)
    obtain ⟨gs,length,hr,visited⟩ := ih (fun h => ha (mem_insert_of_mem h))
      (fun h => hb (mem_insert_of_mem h)) s₂ sa sb fs
    let restored := Function.update s₂ b ({b} : Term V)
    have endOut : output restored g₂={x} := by
      change restored x ∆ restored b = _
      simp [restored,state₂,bx.symm,pair]
    have endState : applyGate restored g₂ = Function.update s b {b} := by
      change Function.update restored x (output restored g₂) = _
      rw [endOut]
      funext z
      by_cases zx : z=x
      · subst z; simp [bx.symm,sx]
      · rw [Function.update_of_ne zx]
        by_cases zb : z=b
        · subst z; simp [restored]
        · simp [restored,state₂,zb,zx]
    refine ⟨g₁::g₂::(gs++[g₂]),by simp [length,card_insert_of_notMem absent]; omega,?_,?_⟩
    · change run s₂ (gs++[g₂]) = _
      rw [run_append,hr]
      exact endState
    · intro z hz
      change pair a z ∈ output s g₁ :: output s₁ g₂ :: outputs s₂ (gs++[g₂]) ∧
        pair b z ∈ output s g₁ :: output s₁ g₂ :: outputs s₂ (gs++[g₂])
      rw [out₁,out₂,outputs_append]
      rcases mem_insert.mp hz with rfl | hz
      · simp
      · obtain ⟨va,vb⟩ := visited z hz
        exact ⟨by simp [va],by simp [vb]⟩

/-- The optimum on K₂,p is 3p+2 for p≥2. The explicit upper circuit restores
every input and visits both hub parities at every leaf. -/
theorem two_hub_optimum [Fintype V] (a b : V) (X : Finset V) (ab : a≠b)
    (ha : a∉X) (hb : b∉X) (all : insert a (insert b X)=univ) (two : 2≤X.card) :
    IsLeast {k | ∃ gs : List (Gate V), Network (twoHubEdges a b X) gs ∧ gs.length=k}
      (3*X.card+2) := by
  have card := twoHub_count a b X ab ha
  have n : Fintype.card V=X.card+2 := by
    have ht := congrArg Finset.card all
    rw [card_insert_of_notMem (by simp [ab,ha]),card_insert_of_notMem hb,card_univ] at ht
    omega
  have even (w : Term V) (hw : w∈twoHubEdges a b X) : w.card%2=0 := by
    rcases mem_union.mp hw with he | he <;> obtain ⟨x,_,rfl⟩ := mem_image.mp he <;> apply pair_even
  have lhs (x : V) (hx : x∈X) : pair a x ∈ twoHubEdges a b X := mem_union_left _ (mem_image_of_mem _ hx)
  have rhs (x : V) (hx : x∈X) : pair b x ∈ twoHubEdges a b X := mem_union_right _ (mem_image_of_mem _ hx)
  have con (v : V) : ConnectedTo (twoHubEdges a b X) a v := by
    have hv : v∈insert a (insert b X) := all ▸ mem_univ v
    rcases mem_insert.mp hv with rfl | hv
    · exact .root
    · rcases mem_insert.mp hv with rfl | hv
      · obtain ⟨x,hx⟩ := card_pos.mp (by omega : 0<X.card)
        exact .edge (.edge .root (lhs x hx)) (by simpa only [pair,symmDiff_comm ({x}:Finset V) {v}] using rhs x hx)
      · exact .edge .root (lhs v hv)
  constructor
  · let g : Gate V := ⟨a,b,ab⟩
    let s := applyGate initial g
    have out : output initial g=pair a b := by
      change ({b}:Finset V) ∆ {a} = _
      exact symmDiff_comm ..
    have state : s=Function.update initial b (pair a b) := by
      change Function.update initial b (output initial g) = _
      rw [out]
    obtain ⟨gs,len,hr,hv⟩ := middle a b X ab ha hb s (by simp [state,ab,initial])
      (by simp [state]) (by intro x hx; have xb : x≠b := by rintro rfl; exact hb hx
                            simp [state,xb,initial])
    refine ⟨g::gs,⟨?_,?_⟩,by simp [len]⟩
    · change run s gs = initial
      rw [hr,state,Function.update_idem]
      exact Function.update_eq_self ..
    · intro w hw
      rcases mem_union.mp hw with h|h <;> obtain ⟨x,hx,rfl⟩ := mem_image.mp h
      · exact List.mem_cons_of_mem _ (hv x hx).1
      · exact List.mem_cons_of_mem _ (hv x hx).2
  · rintro k ⟨gs,net,rfl⟩
    have cycle : Fintype.card V ≤ (twoHubEdges a b X).card := by omega
    have := sumfree_extra_gate a _ gs con even (hub_even_free a b X ab ha hb) cycle net
    omega

#print axioms two_hub_optimum

/-- Start from B and complete a triangle of T whenever its other two edges
are available. For two-element supports, completing a triangle is XOR. -/
inductive TriangleClosure (T B : Finset (Term V)) : Term V → Prop where
  | seed {e} : e ∈ B → TriangleClosure T B e
  | complete {e f} : TriangleClosure T B e → TriangleClosure T B f →
      e ∆ f ∈ T → TriangleClosure T B (e ∆ f)

private theorem birth_is_output (s : State V) (gs : List (Gate V)) {w : Term V}
    (hw : w ∈ births s gs) : w ∈ outputs s gs ∧ w.card % 2 = 0 := by
  induction gs generalizing s with
  | nil => simp [births] at hw
  | cons g gs ih =>
    simp only [births] at hw
    split at hw
    · rename_i ho
      rcases List.mem_cons.mp hw with eq | hw
      · subst w
        refine ⟨by simp [outputs], ?_⟩
        have h := card_xor (s g.target) (s g.control)
        change (output s g).card%2 = _ at h
        omega
      · obtain ⟨h,p⟩ := ih _ hw
        exact ⟨List.mem_cons_of_mem _ h,p⟩
    · obtain ⟨h,p⟩ := ih _ hw
      exact ⟨List.mem_cons_of_mem _ h,p⟩

private theorem activation_from_births (T B : Finset (Term V)) (s : State V)
    (gs : List (Gate V)) (prior : ∀ v, (s v).card%2=0 → TriangleClosure T B (s v))
    (seeds : ∀ e∈births s gs, e∈B)
    (sat : ∀ e∈outputs s gs, e.card%2=0 → e∈T) :
    ∀ e∈outputs s gs, e.card%2=0 → TriangleClosure T B e := by
  induction gs generalizing s with
  | nil => simp [outputs]
  | cons g gs ih =>
    let u := applyGate s g
    have new (he : (output s g).card%2=0) : TriangleClosure T B (output s g) := by
      have p := card_xor (s g.target) (s g.control)
      change (output s g).card%2 = _ at p
      by_cases ht : (s g.target).card%2=0
      · exact .complete (prior _ ht) (prior _ (by omega))
          (sat (output s g) (List.mem_cons_self) he)
      · have both : (s g.target).card%2=1 ∧ (s g.control).card%2=1 := by omega
        exact .seed (seeds _ (by simp [births,both]))
    have pre' : ∀ v, (u v).card%2=0 → TriangleClosure T B (u v) := by
      intro v
      by_cases hv : v=g.target
      · subst v; simpa [u,applyGate] using new
      · simpa [u,applyGate,hv] using prior v
    have seeds' : ∀ e∈births u gs,e∈B := by
      intro e he
      apply seeds
      simp only [births]
      split <;> simp_all [u]
    intro e he hp
    rcases List.mem_cons.mp he with rfl | he
    · exact new hp
    · exact ih u pre' seeds' (fun z hz => sat z (List.mem_cons_of_mem _ hz)) e he hp

theorem inter_xor (e f U : Term V) :
    (e ∆ f) ∩ U = (e ∩ U) ∆ (f ∩ U) := by
  ext z
  simp only [mem_inter,mem_symmDiff]
  tauto

private theorem pair_cut (U : Term V) (x y : V) :
    ((pair x y) ∩ U).card%2=0 ↔ (x∈U ↔ y∈U) := by
  have singleton_cut (z : V) : ({z} : Finset V) ∩ U = if z∈U then {z} else ∅ := by
    split
    · rename_i hz; exact inter_eq_left.mpr (singleton_subset_iff.mpr hz)
    · rename_i hz; ext w; simp only [mem_inter,mem_singleton,notMem_empty,iff_false]
      rintro ⟨rfl,hw⟩; exact hz hw
  rw [pair,inter_xor,card_xor,singleton_cut,singleton_cut]
  by_cases hx : x∈U <;> by_cases hy : y∈U <;> simp [hx,hy]

private theorem activating_edges_connected [Fintype V] (r : V) (T B : Finset (Term V))
    (simple : SimpleEdges T) (sub : B⊆T) (con : ∀ v, ConnectedTo T r v)
    (activation : ∀ e∈T, TriangleClosure T B e) : ∀ v, ConnectedTo B r v := by
  classical
  let U := univ.filter (ConnectedTo B r)
  have side (v : V) : v∈U ↔ ConnectedTo B r v := by simp [U]
  have cuts {w : Term V} (derived : TriangleClosure T B w) : (w∩U).card%2=0 := by
    induction derived with
    | @seed e he =>
      obtain ⟨x,y,ne,eq⟩ := card_eq_two.mp (simple e (sub he))
      have edge : pair x y ∈ B := by rwa [pair_of_ne ne,← eq]
      rw [eq,← pair_of_ne ne,pair_cut,side,side]
      exact ⟨fun h => .edge h edge, fun h => .edge h (by
        simpa only [pair,symmDiff_comm ({x} : Finset V) {y}] using edge)⟩
    | @complete e f _ _ _ h₁ h₂ =>
      rw [inter_xor,card_xor]
      omega
  intro v
  induction con v with
  | root => exact .root
  | @edge v w _ he prev =>
    have h := (pair_cut U v w).mp (cuts (activation _ he))
    exact (side w).mp (h.mp ((side v).mpr prev))

/-- Every connected simple graph attaining the ideal CNOT count has a spanning
tree whose edges generate every required edge by successive triangle completions. -/
theorem perfect_birth_tree [Fintype V] (r : V) (T : Finset (Term V))
    (connected : ∀ v, ConnectedTo T r v) (simple : SimpleEdges T)
    (gs : List (Gate V)) (net : Network T gs)
    (tight : gs.length=T.card+(Fintype.card V-1)) :
    let B := (births initial gs).toFinset
    B ⊆ T ∧ B.card=Fintype.card V-1 ∧
      (∀ v, ConnectedTo B r v) ∧ ∀ e∈T, TriangleClosure T B e := by
  classical
  let B := (births initial gs).toFinset
  change B ⊆ T ∧ B.card=Fintype.card V-1 ∧
    (∀ v, ConnectedTo B r v) ∧ ∀ e∈T, TriangleClosure T B e
  have even (w : Term V) (hw : w∈T) : w.card%2=0 := by rw [simple w hw]
  have sat := even_output_saturation r T gs connected even net tight.le
  have sub : B⊆T := by
    intro e he
    obtain ⟨out,hp⟩ := birth_is_output initial gs (List.mem_toFinset.mp he)
    exact sat e out hp
  have make (e : Term V) (he : e∈T) : TriangleClosure T B e :=
    activation_from_births T B initial gs (by simp [initial])
      (fun _ h => List.mem_toFinset.mpr h) sat e (net.2 e he) (even e he)
  have con := activating_edges_connected r T B simple sub connected make
  have low := spanning_count r B.toList (fun v => pair_in_span B.toList B
    (fun e he => span_contains _ (by simpa using he)) r v (con v))
  simp only [Finset.length_toList] at low
  have upper : B.card ≤ (births initial gs).length := List.toFinset_card_le _
  have balanced := balance initial gs
  rw [net.1] at balanced
  have odd := deaths_le_odd initial gs
  have split := counts_split initial gs
  have needed := (card_le_card (requested_subset T gs even net)).trans (List.toFinset_card_le _)
  exact ⟨sub,by omega,con,make⟩

theorem perfect_has_activating_tree [Fintype V] (r : V) (T : Finset (Term V))
    (connected : ∀ v, ConnectedTo T r v) (simple : SimpleEdges T)
    (gs : List (Gate V)) (net : Network T gs)
    (tight : gs.length=T.card+(Fintype.card V-1)) :
    ∃ B : Finset (Term V), B ⊆ T ∧ B.card=Fintype.card V-1 ∧
      (∀ v, ConnectedTo B r v) ∧ ∀ e∈T, TriangleClosure T B e := by
  exact ⟨(births initial gs).toFinset,
    perfect_birth_tree r T connected simple gs net tight⟩

#print axioms perfect_has_activating_tree

/-- Visit one additional pair and undo that gate before running the given circuit. -/
theorem insert_single_edge (T : Finset (Term V)) (u v : V) (diff : u≠v)
    (gs : List (Gate V)) (net : Network T gs) :
    ∃ hs : List (Gate V), Network (insert (pair v u) T) hs ∧ hs.length=gs.length+2 := by
  let g : Gate V := ⟨u,v,diff⟩
  have eq : output initial g=pair v u := rfl
  refine ⟨g::g::gs,⟨?_,?_⟩,rfl⟩
  · simpa only [run,cancel_gate] using net.1
  · intro w hw
    rcases mem_insert.mp hw with rfl | old
    · exact eq ▸ List.mem_cons_self
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ ((cancel_gate initial g).symm ▸ net.2 w old))

/-- Eliminate a pivot bit by adding one fixed generator when necessary. -/
private def clearBit (p : V) (g t : Term V) : Term V := if p∈t then t ∆ g else t

private theorem clear_add (p : V) (g a b : Term V) :
    clearBit p g (a ∆ b) = clearBit p g a ∆ clearBit p g b := by
  by_cases ha : p∈a <;> by_cases hb : p∈b <;> simp [clearBit,mem_symmDiff,ha,hb] <;>
    ext z <;> simp only [mem_symmDiff] <;> tauto

/-- Elementary elimination on a list of binary generators. Outside the
chosen pivot coordinates the quotient map fixes every supported vector. -/
private theorem pivot_projection (xs : List (Term V)) :
    ∃ P : Finset V, ∃ f : Term V → Term V,
      P.card ≤ xs.length ∧ f ∅=∅ ∧ (∀ a b, f (a ∆ b)=f a ∆ f b) ∧
      (∀ g∈xs, f g=∅) ∧ ∀ t, Disjoint t P → f t=t := by
  generalize hlength : xs.length = k
  induction k generalizing xs with
  | zero =>
    have eq := List.length_eq_zero_iff.mp hlength
    subst xs
    exact ⟨∅,id,by simp,rfl,fun _ _ => rfl,by simp,by simp⟩
  | succ k ih =>
    cases xs with
    | nil => simp at hlength
    | cons g ts =>
      have rest : ts.length=k := Nat.succ.inj hlength
      by_cases empty : g=∅
      · obtain ⟨P,f,bound,zero,linear,kill,fixed⟩ := ih ts rest
        refine ⟨P,f,by omega,zero,linear,?_,fixed⟩
        intro u hu
        rcases List.mem_cons.mp hu with rfl | hu
        · simpa [empty] using zero
        · exact kill u hu
      · obtain ⟨p,hp⟩ := Finset.nonempty_iff_ne_empty.mpr empty
        have next : (ts.map (clearBit p g)).length=k := by simpa using rest
        obtain ⟨P,f,bound,zero,linear,kill,fixed⟩ := ih _ next
        refine ⟨insert p P,f ∘ clearBit p g,?_,?_,?_,?_,?_⟩
        · have h := card_insert_le p P
          simp at bound ⊢
          omega
        · simpa [clearBit] using zero
        · intro a b
          simp only [Function.comp_apply,clear_add,linear]
        · intro u hu
          rcases List.mem_cons.mp hu with rfl | hu
          · simpa [clearBit,hp] using zero
          · exact kill _ (List.mem_map_of_mem hu)
        · intro t dt
          have np : p∉t := fun h => (Finset.disjoint_left.mp dt) h (mem_insert_self ..)
          have d : Disjoint t P := dt.mono_right (subset_insert ..)
          simpa [clearBit,np] using fixed t d

private theorem projected_births (T : Finset (Term V)) (free : SumFree T)
    (f : Term V → Term V) (lin : ∀ a b, f (a ∆ b)=f a ∆ f b)
    (H : Finset (Term V)) (s : State V) (gs : List (Gate V))
    (past : ∀ x, (s x).card%2=0 → (s x∈T ∨ f (s x)=∅) ∧ (f (s x)≠∅ → f (s x)∈H))
    (kill : ∀ w∈outputs s gs, w.card%2=0 → w∉T → f w=∅)
    (born : ∀ w∈births s gs, f w∈H) :
    ∀ w∈outputs s gs, w.card%2=0 → f w≠∅ → f w∈H := by
  induction gs generalizing s with
  | nil => simp [outputs]
  | cons g gs ih =>
    let u := applyGate s g
    have current (he : (output s g).card%2=0) :
        (output s g∈T ∨ f (output s g)=∅) ∧
        (f (output s g)≠∅ → f (output s g)∈H) := by
      have lost := kill (output s g) List.mem_cons_self he
      refine ⟨or_iff_not_imp_left.mpr lost,?_⟩
      intro nonzero
      have target : output s g∈T := by by_contra h; exact nonzero (lost h)
      have parity := card_xor (s g.target) (s g.control)
      change (output s g).card%2=_ at parity
      by_cases ht : (s g.target).card%2=0
      · obtain ⟨targetOrZero,bt⟩ := past g.target ht
        obtain ⟨ac,bc⟩ := past g.control (by omega)
        have one : f (s g.target)=∅ ∨ f (s g.control)=∅ := by
          rcases targetOrZero with et | zt
          · rcases ac with ec | zc
            · exact (free _ et _ ec target).elim
            · exact Or.inr zc
          · exact Or.inl zt
        rcases one with zero | zero
        · have eq : f (output s g)=f (s g.control) := by simp [output,lin,zero]
          rw [eq] at nonzero ⊢
          exact bc nonzero
        · have eq : f (output s g)=f (s g.target) := by simp [output,lin,zero]
          rw [eq] at nonzero ⊢
          exact bt nonzero
      · have both : (s g.target).card%2=1 ∧ (s g.control).card%2=1 := by omega
        exact born _ (by simp [births,both])
    have next (x : V) : (u x).card%2=0 →
        (u x∈T ∨ f (u x)=∅) ∧ (f (u x)≠∅ → f (u x)∈H) := by
      by_cases eq : x=g.target
      · subst x; simpa [u,applyGate] using current
      · simpa [u,applyGate,eq] using past x
    have born' : ∀ w∈births u gs, f w∈H := by
      intro w hw; apply born
      simp only [births]
      split <;> simp_all [u]
    intro w hw he nz
    rcases List.mem_cons.mp hw with rfl | hw
    · exact (current he).2 nz
    · exact ih u next (fun t h => kill t (List.mem_cons_of_mem _ h)) born' w hw he nz

/-- Lower bound for a restored network of sum-free edge targets. There is a
set of pivot vertices paying one excess even output per pivot. Every requested
edge disjoint from the pivot set needs its own nonzero projected birth. -/
theorem sumfree_pivot_bound_from [Fintype V] (D : Finset V) (r : V) (hr : r∈D)
    (T : Finset (Term V)) (s : State V) (gs : List (Gate V))
    (connected : ∀ v∈D, ConnectedTo T r v) (simple : SimpleEdges T) (free : SumFree T)
    (initialEven : ∀ v, (s v).card%2=0 → s v=∅)
    (restored : run s gs=s) (covered : ∀ w∈T,w∈outputs s gs) :
    ∃ P : Finset V, T.card + P.card +
      max (D.card-1) (T.filter (fun e => Disjoint e P)).card ≤ gs.length := by
  classical
  let A := (evens s gs).toFinset
  let X := A \ T
  have even (w : Term V) (hw : w∈T) : w.card%2=0 := by rw [simple w hw]
  have sub : T⊆A := by
    intro w hw
    simp [A,evens,covered w hw,even w hw]
  obtain ⟨P,f,piv,zero,lin,kills,fixed⟩ := pivot_projection X.toList
  simp only [Finset.length_toList] at piv
  let H := (births s gs).toFinset.image f
  have kill (w : Term V) (h : w∈outputs s gs) (he : w.card%2=0) (nt : w∉T) :
      f w=∅ := by
    apply kills
    apply Finset.mem_toList.mpr
    exact mem_sdiff.mpr ⟨by simp [A,evens,h,he],nt⟩
  have generated := projected_births T free f lin H s gs (by
    intro v hv
    rw [initialEven v hv,zero]
    exact ⟨Or.inr rfl,fun h => (h rfl).elim⟩) kill
    (fun w hw => mem_image_of_mem _ (List.mem_toFinset.mpr hw))
  have roots : T.filter (fun e => Disjoint e P) ⊆ H := by
    intro e he
    obtain ⟨ht,dis⟩ := mem_filter.mp he
    have nonempty : e≠∅ := by
      intro empty
      have h := simple e ht
      simp [empty] at h
    have eq := fixed e dis
    have h := generated e (covered e ht) (even e ht) (by rwa [eq])
    rwa [eq] at h
  have count := (card_le_card roots).trans
    ((card_image_le : H.card≤(births s gs).toFinset.card).trans (List.toFinset_card_le _))
  have size := card_sdiff_add_card_eq_card sub
  change X.card+T.card=A.card at size
  have evenLen : A.card≤(evens s gs).length := List.toFinset_card_le _
  have inspan := even_outputs_from_births (span (births s gs))
    (fun _ ha _ hb => span_add _ ha hb) s gs (fun v hv => initialEven v hv ▸ span_zero _)
    (fun _ hw => span_contains _ hw)
  have lower := spanning_count_on D r hr (births s gs) fun v hv => pair_in_span _ T
    (fun w hw => inspan w (covered w hw) (even w hw)) r v (connected v hv)
  have balance' := balance s gs
  rw [restored] at balance'
  have deaths := deaths_le_odd s gs
  have split := counts_split s gs
  exact ⟨P,by omega⟩

theorem sumfree_pivot_bound [Fintype V] (r : V) (T : Finset (Term V)) (gs : List (Gate V))
    (connected : ∀ v, ConnectedTo T r v) (simple : SimpleEdges T) (free : SumFree T)
    (net : Network T gs) :
    ∃ P : Finset V, T.card + P.card +
      max (Fintype.card V-1) (T.filter (fun e => Disjoint e P)).card ≤ gs.length := by
  simpa only [card_univ] using sumfree_pivot_bound_from univ r (mem_univ _) T initial gs
    (fun v _ => connected v) simple free (by simp [initial]) net.1 net.2

#print axioms sumfree_pivot_bound

/-- Distinct even outputs outside the set of requested terms. -/
def exceptionalEven (T : Finset (Term V)) (gs : List (Gate V)) : Finset (Term V) :=
  (evens initial gs).toFinset \ T

theorem mem_exceptionalEven (T : Finset (Term V)) (gs : List (Gate V)) {e : Term V}
    (out : e∈outputs initial gs) (even : e.card%2=0) (extra : e∉T) :
    e∈exceptionalEven T gs := mem_sdiff.mpr ⟨by simp [evens,out,even],extra⟩

theorem exceptional_even_budget [Fintype V] (r : V) (T : Finset (Term V)) (gs : List (Gate V))
    (connected : ∀ v, ConnectedTo T r v) (simple : SimpleEdges T) (net : Network T gs) :
    T.card + (exceptionalEven T gs).card + (Fintype.card V-1) ≤ gs.length := by
  have even (e : Term V) (he : e∈T) : e.card%2=0 := by rw [simple e he]
  have sum := card_sdiff_add_card_eq_card (requested_subset T gs even net)
  change (exceptionalEven T gs).card+T.card=_ at sum
  have c := List.toFinset_card_le (evens initial gs)
  have o := odd_output_lower_bound r T gs connected even net.2 net.1
  change Fintype.card V-1 ≤ oddOutputs initial gs at o
  have l := counts_split initial gs
  omega

/-- In an optimal-length network attaining the connected lower bound, each
even output is generated just once. -/
theorem perfect_even_nodup [Fintype V] (r : V) (T : Finset (Term V)) (gs : List (Gate V))
    (connected : ∀ v, ConnectedTo T r v) (simple : SimpleEdges T) (net : Network T gs)
    (tight : gs.length=T.card+(Fintype.card V-1)) : (evens initial gs).Nodup := by
  have even (w : Term V) (hw : w∈T) : w.card%2=0 := by rw [simple w hw]
  have cover := card_le_card (requested_subset T gs even net)
  have odd := odd_output_lower_bound r T gs connected even net.2 net.1
  change Fintype.card V-1 ≤ oddOutputs initial gs at odd
  have count := counts_split initial gs
  have ub := List.toFinset_card_le (evens initial gs)
  have eq : (evens initial gs).toFinset.card=(evens initial gs).length := by omega
  exact (Multiset.toFinset_card_eq_card_iff_nodup (m := (⟦evens initial gs⟧ : Multiset (Term V)))).mp eq

/-- A local property of every updated target and the term written there. -/
def AllGates (P : V → Term V → Prop) (s : State V) : List (Gate V) → Prop
  | [] => True
  | g::gs => P g.target (output s g) ∧ AllGates P (applyGate s g) gs

theorem allGates_append (P : V → Term V → Prop) (s : State V) (a b : List (Gate V)) :
    AllGates P s (a++b) ↔ AllGates P s a ∧ AllGates P (run s a) b := by
  induction a generalizing s with
  | nil => simp [AllGates,run]
  | cons g a ih => simp [AllGates,run,ih,and_assoc]

/-- Apply a fixed control once to each member of a set of distinct targets.
The local assertion records which value is written to each updated target. -/
theorem fanout_condition (P : V → Term V → Prop) (c : V) (B : Finset V) (hc : c∉B) (s : State V)
    (valid : ∀ x∈B,P x (s x ∆ s c)) :
    ∃ gs : List (Gate V), gs.length=B.card ∧
      run s gs=(fun x => if x∈B then s x ∆ s c else s x) ∧
      (∀ x∈B,s x ∆ s c ∈ outputs s gs) ∧ AllGates P s gs := by
  induction B using Finset.induction_on generalizing s with
  | empty => exact ⟨[],rfl,by simp [run],by simp,trivial⟩
  | @insert b B fresh ih =>
    have cb : c≠b := fun e => hc (e ▸ mem_insert_self b B)
    let g : Gate V := ⟨c,b,cb⟩
    let u := applyGate s g
    have uc : u c=s c := by simp [u,applyGate,g,cb]
    have ub : u b=s b ∆ s c := by simp [u,applyGate,g,output]
    have same (x : V) (h : x≠b) : u x=s x := by simp [u,applyGate,g,h]
    have ok (x : V) (hx : x∈B) : P x (u x ∆ u c) := by
      have xb : x≠b := fun eq => fresh (eq ▸ hx)
      rw [same x xb,uc]; exact valid x (mem_insert_of_mem hx)
    obtain ⟨gs,sz,endState,out,checked⟩ := ih (fun h => hc (mem_insert_of_mem h)) u ok
    refine ⟨g::gs,by simp [sz,card_insert_of_notMem fresh],?_,?_,
      valid b (mem_insert_self ..),checked⟩
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

theorem fanout_exists (c : V) (B : Finset V) (hc : c∉B) (s : State V) :
    ∃ gs : List (Gate V), gs.length=B.card ∧
      run s gs=(fun x => if x∈B then s x ∆ s c else s x) ∧
      ∀ x∈B,s x ∆ s c ∈ outputs s gs := by
  obtain ⟨gs,size,finish,seen,_⟩ := fanout_condition (fun _ _ => True) c B hc s (by simp)
  exact ⟨gs,size,finish,seen⟩

end GraphicParity

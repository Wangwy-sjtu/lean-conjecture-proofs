import CaoCounterexample
import Mathlib.Data.List.Permutation

/-! The seven-wire graph has no perfect network with an unused control.
This addresses question (C2) of Cao, Lu, Nie, Sun and Tian. -/
open Finset GraphicParity
open scoped symmDiff
namespace CaoControlWire

variable {V : Type} [DecidableEq V]

/-- A wire never used as a control cannot transmit its input to another wire. -/
def NeverControls (v : V) (gs : List (Gate V)) := ∀ g ∈ gs, g.control ≠ v

private def marked (v : V) (s : State V) := ∀ x, v∈s x ↔ x=v

private def dropWire (v : V) (gs : List (Gate V)) :=
  gs.filter (fun g => decide (g.target ≠ v))

private def history (v : V) (s : State V) : List (Gate V) → List (Term V)
  | [] => []
  | g::gs =>
    if g.target=v then output s g::history v (applyGate s g) gs
    else history v (applyGate s g) gs

private theorem mark_step (v : V) (s : State V) (g : Gate V) (h : marked v s)
    (nc : g.control≠v) : marked v (applyGate s g) := by
  have absent : v∉s g.control := fun hm => nc ((h _).mp hm)
  intro x
  by_cases eq : x=g.target
  · subst x; simpa [applyGate,output,mem_symmDiff,absent] using h g.target
  · simpa [applyGate,eq] using h x

private theorem target_value (s : State V) (g : Gate V) {v : V} (hv : g.target=v) :
    applyGate s g v = output s g :=
  (congrArg (applyGate s g) hv.symm).trans (Function.update_self ..)

private theorem split_length (v : V) (s : State V) (gs : List (Gate V)) :
    (dropWire v gs).length + (history v s gs).length = gs.length := by
  induction gs generalizing s with
  | nil => rfl
  | cons g gs ih =>
    have h := ih (applyGate s g)
    by_cases eq : g.target=v <;> simp [dropWire,history,eq] at h ⊢ <;> omega

private theorem last_history (v : V) (s : State V) (gs : List (Gate V)) :
    ∃ pre, s v :: history v s gs = pre ++ [run s gs v] := by
  induction gs generalizing s with
  | nil => exact ⟨[],rfl⟩
  | cons g gs ih =>
    obtain ⟨pre,eq⟩ := ih (applyGate s g)
    by_cases ht : g.target=v
    · refine ⟨s v :: pre, ?_⟩
      rw [List.cons_append]
      apply congrArg (List.cons (s v))
      rw [target_value s g ht] at eq
      simpa only [history,if_pos ht,run] using eq
    · refine ⟨pre, ?_⟩
      simpa [history,ht,applyGate,Ne.symm ht,run] using eq

private theorem shadow (v : V) (s q : State V) (gs : List (Gate V))
    (marks : marked v s) (nc : NeverControls v gs) (agree : ∀ x≠v, s x=q x) :
    (∀ x≠v, run s gs x=run q (dropWire v gs) x) ∧ run q (dropWire v gs) v=q v ∧
    (∀ e∈outputs s gs, v∉e → e∈outputs q (dropWire v gs)) ∧
    (∀ e∈outputs s gs, v∈e → e∈history v s gs) := by
  induction gs generalizing s q with
  | nil => exact ⟨agree,rfl,by simp [outputs],by simp [outputs]⟩
  | cons g gs ih =>
    have cn : g.control≠v := nc g (by simp)
    have next := mark_step v s g marks cn
    have tailNC : NeverControls v gs := fun k h => nc k (List.mem_cons_of_mem _ h)
    have marker : v∈output s g ↔ g.target=v := by
      simpa [applyGate] using next g.target
    by_cases tv : g.target=v
    · have agree' (x : V) (h : x≠v) : applyGate s g x = q x := by
        simpa [applyGate,tv,h] using agree x h
      obtain ⟨runE,fix,out,hist⟩ := ih (applyGate s g) q next tailNC agree'
      simp only [dropWire,List.filter_cons,ne_eq,tv,not_true_eq_false,decide_false,
        Bool.false_eq_true,↓reduceIte,run] at runE fix out ⊢
      refine ⟨runE,fix,?_,?_⟩
      · intro e he hv
        rcases List.mem_cons.mp he with rfl | he
        · exact False.elim (hv (marker.mpr tv))
        · exact out e he hv
      · intro e he hv
        rcases List.mem_cons.mp he with rfl | he
        · simp [history,tv]
        · simpa [history,tv] using Or.inr (a:=e=output s g) (hist e he hv)
    · have outEq : output s g=output q g := by unfold output; rw [agree _ tv,agree _ cn]
      have agree' (x : V) (h : x≠v) : applyGate s g x = applyGate q g x := by
        by_cases eq : x=g.target
        · subst x; simpa [applyGate] using outEq
        · simpa [applyGate,eq] using agree x h
      obtain ⟨runE,fix,out,hist⟩ := ih (applyGate s g) (applyGate q g) next tailNC agree'
      have cfg : dropWire v (g::gs) = g::dropWire v gs := by simp [dropWire,tv]
      rw [cfg]
      refine ⟨runE, by simpa [run,applyGate,Ne.symm tv] using fix,?_,?_⟩
      · intro e he hv
        rcases List.mem_cons.mp he with rfl | he
        · simp [outputs,outEq]
        · exact List.mem_cons_of_mem _ (out e he hv)
      · intro e he hv
        rcases List.mem_cons.mp he with rfl | he
        · exact False.elim (tv (marker.mp hv))
        · simpa [history,tv] using hist e he hv

private def admissible (T : Finset (Term V)) (e f : Term V) : Prop :=
  e.card%2=0 → f.card%2=0 → e ∆ f∈T

private instance (T : Finset (Term V)) : DecidableRel (admissible T) :=
  fun _ _ => inferInstanceAs (Decidable (_ → _ → _ ∈ T))

private theorem history_chain (v : V) (T : Finset (Term V)) (s : State V) (gs : List (Gate V))
    (known : ∀ x, (s x).card%2=0 → s x∈T)
    (sat : ∀ e∈outputs s gs, e.card%2=0 → e∈T)
    (xorParity : ∀ e f : Term V,(e ∆ f).card%2=(e.card+f.card)%2) :
    (s v :: history v s gs).IsChain (admissible T) := by
  induction gs generalizing s with
  | nil => simp [history]
  | cons g gs ih =>
    have known' (x : V) : ((applyGate s g) x).card%2=0 → applyGate s g x∈T := by
      by_cases eq : x=g.target
      · subst x; simpa [applyGate] using sat (output s g) List.mem_cons_self
      · simpa [applyGate,eq] using known x
    have h := ih (applyGate s g) known' (fun e he => sat e (List.mem_cons_of_mem _ he))
    by_cases tv : g.target=v
    · have rel : admissible T (s v) (output s g) := by
        intro a b
        have p := xorParity (s g.target) (s g.control)
        change (output s g).card%2=_ at p
        rw [tv] at p
        have fromControl := known g.control (by omega)
        simpa [output,tv] using fromControl
      have eq := target_value s g tv
      simpa [history,tv,eq,List.isChain_cons_cons,rel] using h
    · simpa [history,tv,applyGate,Ne.symm tv] using h

open CaoCounterexample

private def incident (v : Wire) := edges.filter fun e => v∈e
private def outside (v : Wire) := edges.filter fun e => v∉e
private def anchor (v : Wire) : Wire := if v=0 then 1 else 0
private def attached (v : Wire) := insert (pair v (anchor v)) (outside v)

private def incidentList (v : Wire) : List (Term Wire) :=
  ((List.finRange 7).filter fun j => decide (color v≠color j)).map (pair v)

private theorem incident_facts : ∀ v : Wire, (incidentList v).Nodup ∧
    (incidentList v).toFinset=incident v ∧ 0<(incident v).card := by decide

private theorem attached_simple : ∀ v : Wire, SimpleEdges (attached v) := by
  change ∀ v : Wire, ∀ e∈attached v, e.card=2
  decide

private theorem edges_simple : SimpleEdges edges := by
  change ∀ e∈edges, e.card=2
  decide

private theorem attached_connected (v x : Wire) : ConnectedTo (attached v) 0 x := by
  by_cases x0 : x=0
  · subst x; exact .root
  by_cases v0 : v=0
  · subst v
    have p1 : ConnectedTo (attached 0) 0 1 := .edge .root (by decide)
    have p4 : ConnectedTo (attached 0) 0 4 := .edge p1 (by decide)
    by_cases small : x.val≤3
    · exact .edge p4 ((by decide : ∀ y : Wire, y≠0 → y.val≤3 → pair 4 y∈attached 0) x x0 small)
    · exact .edge p1 ((by decide : ∀ y : Wire, ¬y.val≤3 → pair 1 y∈attached 0) x small)
  · exact .edge .root ((by decide : ∀ u w : Wire,u≠0 → w≠0 → pair 0 w∈attached u) v x v0 x0)

private theorem nonapex_no_path (v : Wire) (hv : v≠0) (xs : List (Term Wire))
    (perm : xs.Perm (incidentList v)) : ¬ xs.IsChain (admissible edges) :=
  (by decide : ∀ w : Wire, w≠0 → ∀ ys ∈ (incidentList w).permutations',
    ¬ ys.IsChain (admissible edges)) v hv xs (List.mem_permutations'.mpr perm)

/-- Every perfect network for K₁,₃,₃ uses each of its seven wires as a control.
The quantifier ranges over arbitrary gate lists, independently of the exhibited circuit. -/
theorem no_unused_control (gs : List (Gate Wire)) (net : Network edges gs)
    (tight : gs.length=edges.card+(Fintype.card Wire-1)) (v : Wire) :
    ¬ NeverControls v gs := by
  intro never
  have markedInitial : marked v initial := by intro x; simp only [initial,mem_singleton]; exact eq_comm
  obtain ⟨agree,fix,away,inside⟩ := shadow v initial initial gs markedInitial never
    (fun _ _ => rfl)
  have residual : Network (outside v) (dropWire v gs) := by
    constructor
    · funext x
      by_cases eq : x=v
      · subst x; exact fix
      · exact (agree x eq).symm.trans (congrFun net.1 x)
    · intro e he
      obtain ⟨h₁,h₂⟩ := mem_filter.mp he
      exact away e (net.2 _ h₁) h₂
  have diff := (by decide : ∀ x : Wire,anchor x≠x) v
  obtain ⟨extended,networkE,en⟩ := insert_single_edge _ _ _ diff _ residual
  change Network (attached v) extended at networkE
  have inc (e : Term Wire) (h : e∈incident v) : e∈history v initial gs := by
    obtain ⟨he,hv⟩ := mem_filter.mp h
    exact inside e (net.2 e he) hv
  obtain ⟨i,hi⟩ := card_pos.mp (incident_facts v).2.2
  have hNonempty : history v initial gs ≠ [] := List.ne_nil_of_mem (inc i hi)
  obtain ⟨before,hbefore⟩ := last_history v initial gs
  rw [net.1] at hbefore
  obtain ⟨xs,hxs⟩ : ∃ xs, history v initial gs = xs ++ [initial v] := by
    cases before with
    | nil => exact (hNonempty (List.cons.inj hbefore).2).elim
    | cons a xs => exact ⟨xs,(List.cons.inj hbefore).2⟩
  have sub : incident v ⊆ xs.toFinset := by
    intro e he
    have h := inc e he
    rw [hxs,List.mem_append] at h
    rcases h with good | finalTerm
    · exact List.mem_toFinset.mpr good
    · have eq := List.mem_singleton.mp finalTerm
      have c := edges_simple e (mem_filter.mp he).1
      simp [eq,initial] at c
  have low := card_le_card sub
  have len := split_length v initial gs
  rw [hxs,List.length_append] at len
  have total : gs.length=21 := tight.trans (by decide)
  have small := List.toFinset_card_le xs
  by_cases apex : v=0
  · subst v
    have tri : TriangleFree (attached 0) := by
      unfold TriangleFree
      decide
    have cycle : Fintype.card Wire≤(attached 0).card := by decide
    have bound := triangle_free_gate_lower 0 (attached 0) extended (attached_connected 0)
      (attached_simple 0) tri cycle networkE
    have counts : (incident 0).card=6 ∧ (attached 0).card=10 ∧ Fintype.card Wire=7 := by decide
    simp only [List.length_cons,List.length_nil] at len
    omega
  · have counts := (by decide : ∀ w : Wire,w≠0 →
        (incident w).card=4 ∧ (attached w).card=12) v apex
    have bound := network_lower_bound 0 (attached v) extended (attached_connected v)
      (fun e he => by rw [attached_simple v e he]) networkE
    have seven : Fintype.card Wire=7 := by decide
    simp only [List.length_cons,List.length_nil] at len
    have equal : xs.toFinset.card=xs.length := by omega
    have eqSets : incident v=xs.toFinset := eq_of_subset_of_card_le sub (by omega)
    have nd : xs.Nodup :=
      (Multiset.toFinset_card_eq_card_iff_nodup (m:=(xs : Multiset (Term Wire)))).mp equal
    have perm := List.perm_of_nodup_nodup_toFinset_eq nd (incident_facts v).1
      (eqSets.symm.trans (incident_facts v).2.1.symm)
    have sat := even_output_saturation 0 edges gs connected
      (fun e he => by rw [edges_simple e he]) net tight.le
    have chain := history_chain v edges initial gs (by simp [initial]) sat card_xor
    rw [hxs] at chain
    exact nonapex_no_path v apex xs perm (List.isChain_append.mp chain.tail).1

/-- The seven-vertex graph answers the authors' general existence question (C2) negatively. -/
theorem c2_counterexample :
    (∃ gs : List (Gate Wire), Network edges gs ∧
      gs.length=edges.card+(Fintype.card Wire-1)) ∧
    ¬ ∃ gs : List (Gate Wire), Network edges gs ∧
      gs.length=edges.card+(Fintype.card Wire-1) ∧ ∃ v, NeverControls v gs := by
  refine ⟨CaoCounterexample.counterexample.2.1,?_⟩
  rintro ⟨gs,net,len,v,never⟩
  exact no_unused_control gs net len v never

#print axioms no_unused_control
#print axioms c2_counterexample

end CaoControlWire

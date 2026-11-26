import GraphicParity
import Multipartite

/-! A seven-vertex counterexample to the conjecture of Cao, Lu, Nie, Sun
and Tian that every graph admitting a perfect graphic parity network has
a perfect cancellation ordering. All gates are on the seven input wires. -/
open Finset GraphicParity
namespace CaoCounterexample

abbrev Wire := Fin 7

/-- 0 is the apex; 1,2,3 and 4,5,6 are the independent parts. -/
def color (i : Wire) : ℕ := if i=0 then 2 else if i.val≤3 then 0 else 1

def vertices : List Wire := [1,2,3,4,5,6,0]

def edges : Finset (Term Wire) :=
  univ.biUnion fun i : Wire =>
    (univ.filter (fun j : Wire => color i ≠ color j)).image (pair i)

/-- The graph used by the circuit and the graph used by the order test
have exactly the same adjacency relation, on the same named vertices. -/
theorem edge_iff (i j : Wire) : pair i j ∈ edges ↔ color i ≠ color j :=
  (by decide : ∀ i j : Wire, pair i j ∈ edges ↔ color i ≠ color j) i j

theorem full_list : vertices.Nodup ∧ ∀ v : Wire, v ∈ vertices := by decide

def circuit : List (Gate Wire) :=
  [⟨4,3,by decide⟩, ⟨2,6,by decide⟩, ⟨1,5,by decide⟩, ⟨1,4,by decide⟩,
   ⟨0,2,by decide⟩, ⟨0,1,by decide⟩, ⟨1,4,by decide⟩, ⟨4,3,by decide⟩,
   ⟨2,4,by decide⟩, ⟨1,5,by decide⟩, ⟨2,6,by decide⟩, ⟨6,1,by decide⟩,
   ⟨5,2,by decide⟩, ⟨3,5,by decide⟩, ⟨6,3,by decide⟩, ⟨0,6,by decide⟩,
   ⟨6,1,by decide⟩, ⟨6,3,by decide⟩, ⟨3,5,by decide⟩, ⟨5,2,by decide⟩,
   ⟨2,4,by decide⟩]

theorem connected (v : Wire) : ConnectedTo edges 0 v := by
  by_cases hv : v=0
  · subst v; exact .root
  · exact .edge .root ((edge_iff 0 v).mpr
      ((by decide : ∀ j : Wire, j≠0 → color 0≠color j) v hv))

set_option maxRecDepth 20000 in
theorem network : Network edges circuit := by
  constructor
  · funext i
    exact (by decide : ∀ j : Wire, run initial circuit j = initial j) i
  · exact (by decide : ∀ e ∈ edges, e ∈ outputs initial circuit)

/-- Along the exhibited program each wire keeps its own input in its support,
and every intermediate support is either a singleton or an edge-sized pair. -/
theorem certificate_states :
    ∀ s ∈ circuit.scanl applyGate initial, ∀ x : Wire,
      x ∈ s x ∧ ((s x).card=1 ∨ (s x).card=2) := by decide

theorem counts : edges.card=15 ∧ Fintype.card Wire=7 ∧ circuit.length=21 := by decide

/-- No permutation of all seven named vertices satisfies the component-based
perfect cancellation ordering of the paper. -/
theorem no_perfect_cancellation :
    ¬ ∃ order, order.Perm vertices ∧ Multipartite.graphOrdering color order := by
  have exactShape : (vertices.map color).Perm (Multipartite.shape 3 3 [(2,1)]) :=
    List.Perm.refl _
  have good : Multipartite.Valid 3 [(2,1)] := by
    constructor
    · decide
    · intro p hp
      simp only [List.mem_singleton] at hp
      subst p
      decide
  intro h
  have adm := (Multipartite.named_vertices color vertices full_list.1 3 3 [(2,1)] exactShape).mp h
  have bad := (Multipartite.classification 3 3 [(2,1)] (by decide) good).mp adm
  exact (by decide : ¬3≤(Multipartite.inventory [(2,1)]).length+1) bad

/-- The concrete graph admits an optimal network but has no perfect
cancellation ordering. This refutes the conjectured converse. -/
theorem counterexample :
    (∀ v : Wire, ConnectedTo edges 0 v) ∧
    (∃ gs : List (Gate Wire), Network edges gs ∧
      gs.length=edges.card+(Fintype.card Wire-1)) ∧
    ¬ ∃ order, order.Perm vertices ∧ Multipartite.graphOrdering color order :=
  ⟨connected,⟨circuit,network,by decide⟩,no_perfect_cancellation⟩

#print axioms edge_iff
#print axioms network
#print axioms certificate_states
#print axioms no_perfect_cancellation
#print axioms counterexample

end CaoCounterexample

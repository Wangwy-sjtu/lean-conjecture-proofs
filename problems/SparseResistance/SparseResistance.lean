import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Resistance-nonnegative graphs with pairwise nonadjacent branching vertices,
using the full-support spanning-tree characterization of Devriendt, Theorem 3.8. -/

namespace SparseResistance
open Finset SimpleGraph
noncomputable section
attribute [local instance] Classical.propDecidable

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

def trees (G : SimpleGraph V) : Finset (SimpleGraph V) :=
  Finset.univ.filter (fun T => T ≤ G ∧ T.IsTree)

@[simp] theorem mem_trees {G T : SimpleGraph V} : T ∈ trees G ↔ T ≤ G ∧ T.IsTree := by
  simp [trees]

/-- Every spanning tree must receive positive probability. -/
def RN (G : SimpleGraph V) : Prop :=
  ∃ P : SimpleGraph V → ℝ,
    (∀ T ∈ trees G, 0 < P T) ∧ (∑ T ∈ trees G, P T)=1 ∧
    ∀ v : V, (∑ T ∈ trees G, P T*(T.degree v : ℝ)) ≤ 2

/-- At least one endpoint of every edge has degree at most two. -/
def TwoSparse (G : SimpleGraph V) : Prop :=
  ∀ ⦃u v⦄, G.Adj u v → G.degree u ≤ 2 ∨ G.degree v ≤ 2

def branch (G : SimpleGraph V) : Finset V := Finset.univ.filter (fun v => 2<G.degree v)

omit [DecidableEq V] in
@[simp] theorem mem_branch {G : SimpleGraph V} {v : V} : v ∈ branch G ↔ 2<G.degree v := by
  simp [branch]

private theorem incident_sum (G : SimpleGraph V) (v : V) :
    (G.degree v : ℝ) = ∑ e ∈ G.edgeFinset, (if v ∈ e then (1:ℝ) else 0) := by
  rw [← Finset.sum_filter]
  simp [← G.incidenceFinset_eq_filter, SimpleGraph.card_incidenceFinset_eq_degree]

private theorem degree_in_ambient {G T : SimpleGraph V} (hle : T ≤ G) (v : V) :
    (T.degree v : ℝ) =
      ∑ e ∈ G.edgeFinset, if v ∈ e then (if e ∈ T.edgeFinset then (1:ℝ) else 0) else 0 := by
  rw [incident_sum T]
  calc
    _ = ∑ e ∈ G.edgeFinset, if e ∈ T.edgeFinset then (if v ∈ e then (1:ℝ) else 0) else 0 := by
      have hf : G.edgeFinset.filter (fun e => e ∈ T.edgeFinset) = T.edgeFinset := by
        ext e
        simp only [Finset.mem_filter, and_iff_right_iff_imp]
        exact fun h => SimpleGraph.edgeFinset_mono hle h
      calc
        _ = ∑ e ∈ G.edgeFinset.filter (fun e => e ∈ T.edgeFinset),
            (if v ∈ e then (1:ℝ) else 0) := by rw [hf]
        _ = _ := Finset.sum_filter ..
    _ = _ := Finset.sum_congr rfl (fun e _ => by split_ifs <;> rfl)

/-- The edge omission marginals of a strictly supported spanning-tree law. -/
structure Omissions (G : SimpleGraph V) where
  q : Sym2 V → ℝ
  nonneg : ∀ e, 0 ≤ q e
  positive : ∀ {u v}, G.Adj u v → ¬ G.IsBridge s(u,v) → 0 < q s(u,v)
  total : ∑ e ∈ G.edgeFinset, q e = (G.edgeFinset.card : ℝ) - Fintype.card V + 1
  vertex : ∀ v, (G.degree v : ℝ)-2 ≤ ∑ e ∈ G.edgeFinset, if v ∈ e then q e else 0

theorem omissions_of_RN {G : SimpleGraph V} (hc : G.Connected) (hr : RN G) :
    Nonempty (Omissions G) := by
  obtain ⟨P,hpos,hnorm,hdeg⟩ := hr
  let miss := fun (T : SimpleGraph V) (e : Sym2 V) => if e ∈ T.edgeFinset then (0:ℝ) else 1
  let q := fun e => ∑ T ∈ trees G, P T * miss T e
  have qterm : ∀ T ∈ trees G, ∀ e, 0 ≤ P T*miss T e := by
    intro T hT e
    apply mul_nonneg (hpos _ hT).le
    dsimp [miss]; split <;> norm_num
  refine ⟨⟨q, fun e => Finset.sum_nonneg (fun T hT => qterm T hT e), ?_, ?_, ?_⟩⟩
  · intro u v _ hn
    obtain ⟨T,hsub,hT⟩ := (hc.connected_delete_edge_of_not_isBridge hn).exists_isTree_le
    have hTG : T ≤ G := hsub.trans (G.deleteEdges_le _)
    have ht : T ∈ trees G := mem_trees.mpr ⟨hTG,hT⟩
    have noedge : s(u,v) ∉ T.edgeFinset := by
      intro he
      have := SimpleGraph.edgeFinset_mono hsub he
      simp at this
    apply Finset.sum_pos' (fun T hT => qterm T hT _)
    exact ⟨T,ht,by simpa only [miss,if_neg noedge,mul_one] using hpos T ht⟩
  · dsimp [q]
    rw [Finset.sum_comm]
    calc
      _ = ∑ T ∈ trees G, P T * ((G.edgeFinset.card : ℝ) - Fintype.card V + 1) := by
        apply Finset.sum_congr rfl
        intro T ht
        rw [← Finset.mul_sum]
        congr 1
        have ⟨hs,hT⟩ := mem_trees.mp ht
        have hf : (G.edgeFinset.filter (fun e => e ∉ T.edgeFinset)) = G.edgeFinset \ T.edgeFinset := by
          ext; simp
        have hcount := Finset.card_sdiff_of_subset (SimpleGraph.edgeFinset_mono hs)
        have hcard : (T.edgeFinset.card : ℝ)+1 = (Fintype.card V : ℝ) := by
          exact_mod_cast hT.card_edgeFinset
        have hle := Finset.card_le_card (SimpleGraph.edgeFinset_mono hs)
        calc
          _ = ((G.edgeFinset \ T.edgeFinset).card : ℝ) := by
            rw [← hf, ← Finset.sum_boole]
            exact Finset.sum_congr rfl (fun e _ => by dsimp [miss]; split_ifs <;> rfl)
          _ = _ := by
            rw [hcount,Nat.cast_sub hle]
            linarith
      _ = _ := by rw [← Finset.sum_mul,hnorm,one_mul]
  · intro v
    have expected := hdeg v
    have row (T : SimpleGraph V) (ht : T ∈ trees G) :
        ∑ e ∈ G.edgeFinset, (if v ∈ e then miss T e else 0) = (G.degree v : ℝ)-T.degree v := by
      rw [incident_sum G, degree_in_ambient (mem_trees.mp ht).1, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun e _ => by dsimp [miss]; split_ifs <;> ring)
    have exchange :
        (∑ e ∈ G.edgeFinset, if v ∈ e then q e else 0) =
          ∑ T ∈ trees G, P T*((G.degree v : ℝ)-T.degree v) := by
      calc
        _ = ∑ e ∈ G.edgeFinset, ∑ T ∈ trees G, P T*(if v ∈ e then miss T e else 0) :=
          Finset.sum_congr rfl (fun e _ => by by_cases he : v ∈ e <;> simp [he,q])
        _ = _ := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl (fun T ht => by rw [← Finset.mul_sum, row T ht])
    rw [exchange]
    simp only [mul_sub,Finset.sum_sub_distrib, ← Finset.sum_mul, hnorm,one_mul]
    linarith

private def hits (B : Finset V) (e : Sym2 V) : ℕ := (B.filter (fun v => v ∈ e)).card

private lemma hits_le_one {G : SimpleGraph V} (hs : TwoSparse G) :
    ∀ e ∈ G.edgeFinset, hits (branch G) e ≤ 1 := by
  intro e
  induction e using Sym2.inductionOn with
  | _ u v =>
    intro he
    have h := hs (show G.Adj u v by simpa using he)
    apply Finset.card_le_one.mpr
    intro a ha b hb
    simp only [Finset.mem_filter,mem_branch,Sym2.mem_iff] at ha hb
    rcases ha with ⟨hga,rfl | rfl⟩ <;> rcases hb with ⟨hgb,rfl | rfl⟩ <;> first | rfl | omega

private lemma hits_zero {G : SimpleGraph V} {u v : V}
    (hu : u ∉ branch G) (hv : v ∉ branch G) : hits (branch G) s(u,v) = 0 := by
  rw [hits,Finset.card_eq_zero,Finset.filter_eq_empty_iff]
  intro w hw he
  rcases Sym2.mem_iff.mp he with rfl | rfl
  · exact hu hw
  · exact hv hw

private theorem weighted_excess {G : SimpleGraph V} (D : Omissions G) :
    ∑ v ∈ branch G, ((G.degree v : ℝ)-2) ≤
      ∑ e ∈ G.edgeFinset, (hits (branch G) e : ℝ)*D.q e := by
  calc
    _ ≤ ∑ v ∈ branch G, ∑ e ∈ G.edgeFinset, if v ∈ e then D.q e else 0 :=
      Finset.sum_le_sum (fun v _ => D.vertex v)
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro e _
      rw [← Finset.sum_filter]
      simp [hits]

/-- The independent branching vertices can use at most one copy of each omitted edge. -/
theorem branch_excess_le_cycle_rank {G : SimpleGraph V} (hc : G.Connected)
    (hs : TwoSparse G) (hr : RN G) :
    ∑ v ∈ branch G, ((G.degree v : ℝ)-2) ≤
      (G.edgeFinset.card : ℝ) - Fintype.card V + 1 := by
  obtain ⟨D⟩ := omissions_of_RN hc hr
  rw [← D.total]
  apply (weighted_excess D).trans (Finset.sum_le_sum ?_)
  intro e he
  exact mul_le_of_le_one_left (D.nonneg e) (by exact_mod_cast hits_le_one hs e he)

/-- For a nontrivial connected 2-sparse RN graph, cycle rank plus number of leaves is at most two.
Written without subtractions: |E| + number of leaves ≤ |V| + 1. -/
theorem edges_add_leaves_le_vertices_add_one [Nontrivial V] {G : SimpleGraph V}
    (hc : G.Connected) (hs : TwoSparse G) (hr : RN G) :
    G.edgeFinset.card + (Finset.univ.filter (fun v => G.degree v = 1)).card ≤
      Fintype.card V + 1 := by
  let leaves := Finset.univ.filter (fun v => G.degree v = 1)
  have hdegree : (∑ v : V, (G.degree v : ℝ)) = 2*(G.edgeFinset.card : ℝ) := by
    exact_mod_cast G.sum_degrees_eq_twice_card_edges
  have hf : (∑ v : V, if G.degree v = 1 then (1:ℝ) else 0) = (leaves.card : ℝ) := by
    rw [← Finset.sum_filter]
    simp [leaves]
  have hpos (v : V) := hc.preconnected.degree_pos_of_nontrivial v
  have hid : ∑ v ∈ branch G, ((G.degree v : ℝ)-2) =
      2*(G.edgeFinset.card : ℝ)-2*(Fintype.card V : ℝ)+leaves.card := by
    unfold branch
    rw [Finset.sum_filter]
    calc
      _ = ∑ v : V, (((G.degree v : ℝ)-2)+(if G.degree v = 1 then (1:ℝ) else 0)) := by
        apply Finset.sum_congr rfl
        intro v _
        by_cases hh : 2 < G.degree v
        · simp only [if_pos hh,if_neg (show G.degree v ≠ 1 by omega),add_zero]
        · have d12 : G.degree v = 1 ∨ G.degree v = 2 := by have := hpos v; omega
          rcases d12 with h | h <;> rw [h] <;> norm_num
      _ = _ := by rw [Finset.sum_add_distrib,Finset.sum_sub_distrib,hdegree,hf]; simp; ring
  have hb := branch_excess_le_cycle_rank hc hs hr
  change G.edgeFinset.card + leaves.card ≤ Fintype.card V + 1
  have hreal : (G.edgeFinset.card : ℝ)+leaves.card ≤ (Fintype.card V : ℝ)+1 := by linarith
  exact_mod_cast hreal

private theorem excess_eq_forces_cover {G : SimpleGraph V} (hc : G.Connected)
    (hs : TwoSparse G) (hr : RN G)
    (heq : ∑ v ∈ branch G, ((G.degree v : ℝ)-2)
      = (G.edgeFinset.card : ℝ) - Fintype.card V + 1)
    {u v : V} (hadj : G.Adj u v) (hn : ¬ G.IsBridge s(u,v)) :
    u ∈ branch G ∨ v ∈ branch G := by
  by_contra! h
  obtain ⟨D⟩ := omissions_of_RN hc hr
  have hlt : ∑ e ∈ G.edgeFinset, (hits (branch G) e : ℝ)*D.q e <
      ∑ e ∈ G.edgeFinset, D.q e := by
    apply Finset.sum_lt_sum
    · intro e he
      exact mul_le_of_le_one_left (D.nonneg e) (by exact_mod_cast hits_le_one hs e he)
    · refine ⟨s(u,v),by simpa using hadj,?_⟩
      simpa only [hits_zero h.1 h.2,Nat.cast_zero,zero_mul] using (D.positive hadj hn)
  rw [D.total, ← heq] at hlt
  exact (weighted_excess D).not_gt hlt

omit [DecidableEq V] in
private theorem excess_formula {G : SimpleGraph V} (hm : ∀ v, 2 ≤ G.degree v) :
    ∑ v ∈ branch G, ((G.degree v : ℝ)-2) =
       2 * (G.edgeFinset.card : ℝ) - 2 * Fintype.card V := by
  have hsum : (∑ v : V, (G.degree v : ℝ)) = 2 * (G.edgeFinset.card : ℝ) := by
    exact_mod_cast G.sum_degrees_eq_twice_card_edges
  calc
    _ = ∑ v : V, ((G.degree v : ℝ)-2) := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro v _ hv
      have hd := hm v
      have hx : G.degree v ≤ 2 := by simpa using hv
      rw [show G.degree v = 2 by omega]
      norm_num
    _ = _ := by rw [Finset.sum_sub_distrib,hsum]; simp; ring

/-- A structural formulation of being isomorphic to the complete bipartite graph K₂,₃. -/
def K23Shape (G : SimpleGraph V) : Prop :=
  ∃ B : Finset V, B.card = 2 ∧ Bᶜ.card = 3 ∧
    ∀ u v, G.Adj u v ↔ (u ∈ B ∧ v ∉ B) ∨ (v ∈ B ∧ u ∉ B)

theorem necessary_shape {G : SimpleGraph V} (hc : G.Connected) (hs : TwoSparse G)
    (hm : ∀ v, 2 ≤ G.degree v) (hn : ∀ ⦃u v⦄, G.Adj u v → ¬ G.IsBridge s(u,v))
    (hr : RN G) : (∀ v, G.degree v ≤ 2) ∨ K23Shape G := by
  by_cases hd : ∀ v, G.degree v ≤ 2
  · exact Or.inl hd
  right
  push_neg at hd
  obtain ⟨z,hz⟩ := hd
  have hzB : z ∈ branch G := mem_branch.mpr hz
  have each (v : V) (hv : v ∈ branch G) : (1:ℝ) ≤ (G.degree v : ℝ)-2 := by
    have h : 3 ≤ G.degree v := mem_branch.mp hv
    have h' : (3:ℝ) ≤ G.degree v := by exact_mod_cast h
    linarith
  have hsize : ((branch G).card : ℝ) ≤ ∑ v ∈ branch G, ((G.degree v : ℝ)-2) := by
    simpa using Finset.sum_le_sum each
  have hne : 0 < (branch G).card := Finset.card_pos.mpr ⟨z,hzB⟩
  have hbudget := branch_excess_le_cycle_rank hc hs hr
  have he := excess_formula hm
  have hegt : Fintype.card V < G.edgeFinset.card := by
    by_contra! hcard
    have hc' : (G.edgeFinset.card : ℝ) ≤ Fintype.card V := by exact_mod_cast hcard
    have hb' : (0:ℝ) < (branch G).card := by exact_mod_cast hne
    linarith
  have hdelta : G.edgeFinset.card = Fintype.card V + 1 := by
    have hx : (G.edgeFinset.card : ℝ) ≤ Fintype.card V + 1 := by linarith
    have hx' : G.edgeFinset.card ≤ Fintype.card V + 1 := by exact_mod_cast hx
    omega
  have heq : ∑ v ∈ branch G, ((G.degree v : ℝ)-2) =
      (G.edgeFinset.card : ℝ)-Fintype.card V+1 := by
    rw [hdelta,Nat.cast_add_one] at he ⊢
    linarith
  have heq2 : ∑ v ∈ branch G, ((G.degree v : ℝ)-2) = 2 := by
    rw [heq,hdelta,Nat.cast_add_one]; ring
  have cover {u v : V} (h : G.Adj u v) := excess_eq_forces_cover hc hs hr heq h (hn h)
  have disj {u v : V} (h : G.Adj u v) (hu : u ∈ branch G) : v ∉ branch G := by
    have := hs h
    simp only [mem_branch] at hu ⊢
    omega
  have low_deg {v : V} (hv : v ∉ branch G) : G.degree v = 2 := by
    have h := hm v
    simp only [mem_branch] at hv
    omega
  have low_sub {v : V} (hv : v ∉ branch G) : G.neighborFinset v ⊆ branch G := by
    intro w hw
    exact (cover ((G.mem_neighborFinset _ _).mp hw)).resolve_left hv
  have zn : (G.neighborFinset z).Nonempty := by
    rw [← Finset.card_pos, G.card_neighborFinset_eq_degree]
    omega
  obtain ⟨w,hw⟩ := zn
  have hw' : w ∉ branch G := disj ((G.mem_neighborFinset _ _).mp hw) hzB
  have Bsize : (branch G).card = 2 := by
    have hmin := Finset.card_le_card (low_sub hw')
    rw [G.card_neighborFinset_eq_degree, low_deg hw'] at hmin
    have hh : ((branch G).card : ℝ) ≤ 2 := by linarith
    have hmax : (branch G).card ≤ 2 := by exact_mod_cast hh
    omega
  have high_deg {v : V} (hv : v ∈ branch G) : G.degree v = 3 := by
    have h0 : 3 ≤ G.degree v := mem_branch.mp hv
    by_contra! h
    have hi : (3:ℝ) < G.degree v := by exact_mod_cast (show 3 < G.degree v by omega)
    have hlt := Finset.sum_lt_sum each ⟨v,hv,show (1:ℝ) < (G.degree v : ℝ)-2 by linarith⟩
    simp [Bsize,heq2] at hlt
  have low_all {v : V} (hv : v ∉ branch G) : G.neighborFinset v = branch G := by
    apply Finset.eq_of_subset_of_card_le (low_sub hv)
    rw [Bsize,G.card_neighborFinset_eq_degree,low_deg hv]
  have equiv_adj (u v : V) : G.Adj u v ↔
      (u ∈ branch G ∧ v ∉ branch G) ∨ (v ∈ branch G ∧ u ∉ branch G) := by
    constructor
    · intro h
      rcases cover h with hu | hv
      · exact Or.inl ⟨hu,disj h hu⟩
      · exact Or.inr ⟨hv,disj h.symm hv⟩
    · rintro (⟨hu,hv⟩ | ⟨hv,hu⟩)
      · exact ((G.mem_neighborFinset _ _).mp ((low_all hv).symm ▸ hu)).symm
      · exact (G.mem_neighborFinset _ _).mp ((low_all hu).symm ▸ hv)
  have hc' : G.neighborFinset z = (branch G)ᶜ := by
    ext w
    simp [equiv_adj,hzB]
  exact ⟨branch G,Bsize,by rw [← hc',G.card_neighborFinset_eq_degree,high_deg hzB],equiv_adj⟩

private lemma rn_of_uniform_degree {G : SimpleGraph V} (hc : G.Connected)
    (hbound : ∀ v, ∑ T ∈ trees G, T.degree v ≤ 2 * (trees G).card) : RN G := by
  obtain ⟨T,hle,hT⟩ := hc.exists_isTree_le
  have hcard : 0 < (trees G).card := Finset.card_pos.mpr ⟨T,mem_trees.mpr ⟨hle,hT⟩⟩
  have hpos : (0:ℝ) < (trees G).card := by exact_mod_cast hcard
  refine ⟨fun _ => ((trees G).card : ℝ)⁻¹, fun _ _ => inv_pos.mpr hpos, ?_, ?_⟩
  · simp [hpos.ne']
  · intro v
    have hh : (∑ T ∈ trees G, (T.degree v : ℝ)) ≤ 2 * ((trees G).card : ℝ) := by
      exact_mod_cast hbound v
    rw [← Finset.mul_sum, ← div_eq_inv_mul]
    exact (div_le_iff₀ hpos).mpr hh

theorem rn_of_degree_le_two {G : SimpleGraph V} (hc : G.Connected) (hm : ∀ v, G.degree v ≤ 2) :
    RN G := by
  apply rn_of_uniform_degree hc
  intro v
  calc
    _ ≤ ∑ _T ∈ trees G, 2 := Finset.sum_le_sum (fun T ht =>
      (T.degree_le_of_le (mem_trees.mp ht).1).trans (hm v))
    _ = _ := by simp [Nat.mul_comm]

omit [DecidableEq V] in
private lemma isTree_comap_iff (s : V ≃ V) (T : SimpleGraph V) :
    (T.comap s.toEmbedding).IsTree ↔ T.IsTree := by
  let i := SimpleGraph.Iso.comap s T
  have hcard : Nat.card (T.comap s.toEmbedding).edgeSet = Nat.card T.edgeSet :=
    Nat.card_congr i.mapEdgeSet
  rw [SimpleGraph.isTree_iff_connected_and_card,SimpleGraph.isTree_iff_connected_and_card,
    i.connected_iff,hcard]

omit [DecidableEq V] in
private lemma degree_comap (s : V ≃ V) (T : SimpleGraph V) (v : V) :
    (T.comap s.toEmbedding).degree v = T.degree (s v) := by
  let i := SimpleGraph.Iso.comap s T
  simpa only [SimpleGraph.card_neighborSet_eq_degree,SimpleGraph.Iso.comap_apply,i]
    using Fintype.card_congr (i.mapNeighborSet v)

/-- In K₂,₃ the uniform law on genuine spanning trees has expected hub degree exactly two. -/
theorem rn_of_K23Shape {G : SimpleGraph V} (hc : G.Connected) (h : K23Shape G) : RN G := by
  obtain ⟨B,hB,hC,ha⟩ := h
  obtain ⟨a,b,hab,hpair⟩ := Finset.card_eq_two.mp hB
  have haB : a ∈ B := by simp [hpair]
  have hbB : b ∈ B := by simp [hpair]
  let s := Equiv.swap a b
  have ss (v : V) : s (s v) = v := Equiv.swap_apply_self _ _ _
  have smem (v : V) : s v ∈ B ↔ v ∈ B := by
    by_cases he : v = a
    · subst v; simp [s,haB,hbB]
    by_cases he' : v = b
    · subst v; simp [s,haB,hbB]
    simp [s,Equiv.swap_apply_of_ne_of_ne he he']
  have sadj (v w : V) : G.Adj (s v) (s w) ↔ G.Adj v w := by
    simp only [ha,smem]
  let flip := fun T : SimpleGraph V => T.comap s.toEmbedding
  have into (T : SimpleGraph V) (hT : T ∈ trees G) : flip T ∈ trees G := by
    obtain ⟨hle,ht⟩ := mem_trees.mp hT
    apply mem_trees.mpr
    refine ⟨fun ⦃v w⦄ hvw => (sadj v w).mp (hle hvw), (isTree_comap_iff s T).mpr ht⟩
  have twice (T : SimpleGraph V) : flip (flip T) = T := by
    ext v w
    change T.Adj (s (s v)) (s (s w)) ↔ T.Adj v w
    rw [ss,ss]
  have same : (∑ T ∈ trees G, T.degree a) = ∑ T ∈ trees G, T.degree b := by
    apply Finset.sum_nbij' flip flip into into (fun T _ => twice T) (fun T _ => twice T)
    intro T _
    change T.degree a = (T.comap s.toEmbedding).degree b
    rw [degree_comap]
    rw [show s b = a from Equiv.swap_apply_right a b]
  have totalV : Fintype.card V = 5 := by
    have hh := Finset.card_add_card_compl B
    omega
  have inTree (T : SimpleGraph V) (hT : T ∈ trees G) :
      T.degree a + T.degree b = 4 := by
    obtain ⟨hle,ht⟩ := mem_trees.mp hT
    have hbip : T.IsBipartiteWith (B : Set V) (Bᶜ : Finset V) := by
      constructor
      · exact Set.disjoint_left.mpr (fun _ hx hxc => (Finset.mem_compl.mp hxc) hx)
      · intro v w hadj
        simpa [and_comm] using (ha v w).mp (hle hadj)
    have hh := SimpleGraph.isBipartiteWith_sum_degrees_eq_card_edges hbip
    have hcT := ht.card_edgeFinset
    rw [hpair] at hh
    rw [Finset.sum_insert (by simpa only [Finset.mem_singleton] using hab),
      Finset.sum_singleton] at hh
    omega
  have two : (∑ T ∈ trees G, T.degree a) = 2 * (trees G).card := by
    have hfour : ∑ T ∈ trees G, (T.degree a + T.degree b) = 4 * (trees G).card := by
      calc
        _ = ∑ _T ∈ trees G, 4 := Finset.sum_congr rfl inTree
        _ = _ := by simp [Nat.mul_comm]
    rw [Finset.sum_add_distrib] at hfour
    omega
  apply rn_of_uniform_degree hc
  intro v
  by_cases hv : v ∈ B
  · rw [hpair,Finset.mem_insert,Finset.mem_singleton] at hv
    rcases hv with rfl | rfl
    · exact two.le
    · omega
  have hn : G.neighborFinset v = B := by
    ext w
    simp only [G.mem_neighborFinset,ha,hv,false_and,not_false_eq_true,and_true,false_or]
  have deg : G.degree v = 2 := by
    rw [← G.card_neighborFinset_eq_degree,hn,hB]
  calc
    _ ≤ ∑ _T ∈ trees G, 2 := Finset.sum_le_sum (fun T ht =>
      (T.degree_le_of_le (mem_trees.mp ht).1).trans deg.le)
    _ = _ := by simp [Nat.mul_comm]

/-- This includes every biconnected 2-sparse simple graph on at least three vertices. -/
theorem rn_iff_degree_le_two_or_K23 {G : SimpleGraph V} (hc : G.Connected) (hs : TwoSparse G)
    (hm : ∀ v, 2 ≤ G.degree v) (hn : ∀ ⦃u v⦄, G.Adj u v → ¬ G.IsBridge s(u,v)) :
    RN G ↔ (∀ v, G.degree v ≤ 2) ∨ K23Shape G :=
  ⟨necessary_shape hc hs hm hn,
    fun h => h.elim (rn_of_degree_le_two hc) (rn_of_K23Shape hc)⟩

/-- In a square-free simple graph two distinct vertices share at most one neighbor. -/
def SquareFree (G : SimpleGraph V) : Prop :=
  ∀ ⦃u v x y⦄, u ≠ v → G.Adj u x → G.Adj v x → G.Adj u y → G.Adj v y → x = y

theorem squareFree_rn_iff_degree_le_two {G : SimpleGraph V} (hc : G.Connected)
    (hs : TwoSparse G) (hm : ∀ v, 2 ≤ G.degree v)
    (hn : ∀ ⦃u v⦄, G.Adj u v → ¬ G.IsBridge s(u,v)) (hq : SquareFree G) :
    RN G ↔ ∀ v, G.degree v ≤ 2 := by
  rw [rn_iff_degree_le_two_or_K23 hc hs hm hn]
  refine or_iff_left ?_
  rintro ⟨B,hB,hC,hadj⟩
  obtain ⟨a,ha,b,hb,hab⟩ := Finset.one_lt_card.mp (show 1 < B.card by omega)
  obtain ⟨x,hx,y,hy,hxy⟩ := Finset.one_lt_card.mp (show 1 < Bᶜ.card by omega)
  have edge (v : V) (hv : v ∈ B) (w : V) (hw : w ∈ Bᶜ) : G.Adj v w :=
    (hadj v w).mpr (Or.inl ⟨hv,Finset.mem_compl.mp hw⟩)
  exact hxy (hq hab (edge _ ha _ hx) (edge _ hb _ hx) (edge _ ha _ hy) (edge _ hb _ hy))

#print axioms omissions_of_RN
#print axioms branch_excess_le_cycle_rank
#print axioms edges_add_leaves_le_vertices_add_one
#print axioms rn_of_degree_le_two
#print axioms rn_of_K23Shape
#print axioms rn_iff_degree_le_two_or_K23
#print axioms squareFree_rn_iff_degree_le_two

end
end SparseResistance

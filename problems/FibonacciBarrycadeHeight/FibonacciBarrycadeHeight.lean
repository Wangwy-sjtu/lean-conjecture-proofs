import FibonacciCircle
import Mathlib.Data.List.Perm.Subperm
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Fintype.Prod

/-! Exact maximum heights of finite barrycades on Fibonacci numbers. -/
namespace FibonacciBarrycade

/-- The increasing list `1, 2, 3, 5, ...`, truncated to length `n`. -/
def bricks (n : ℕ) := (List.range n).map value

/-- A finite collection of distinct permutations with pairwise disjoint sets
of nonempty, proper partial sums, as in Dębski et al., Section 4. -/
def IsBarrycade (n : ℕ) (rows : List (List ℕ)) : Prop :=
  rows.Nodup ∧ (∀ r∈rows, r.Perm (bricks n)) ∧
  ∀ r∈rows, ∀ s∈rows, r≠s → ∀ p∈List.range (n-1), ∀ q∈List.range (n-1),
    (r.take (p+1)).sum≠(s.take (q+1)).sum

instance (n : ℕ) (rows : List (List ℕ)) : Decidable (IsBarrycade n rows) := by
  unfold IsBarrycade
  infer_instance

/-- Exact extremal height, including both a realizing family and a bound on all families. -/
def ExactHeight (n h : ℕ) : Prop :=
  (∃ rows : List (List ℕ), IsBarrycade n rows ∧ rows.length=h) ∧
  ∀ rows : List (List ℕ), IsBarrycade n rows → rows.length≤h

private theorem row_length {n : ℕ} {r : List ℕ} (hr : r.Perm (bricks n)) : r.length=n := by
  simpa [bricks] using hr.length_eq

private theorem row_positive {n : ℕ} {r : List ℕ} (hr : r.Perm (bricks n)) : ∀ x∈r, 0<x := by
  intro x hx
  obtain ⟨i,_,he⟩ := List.mem_map.mp (hr.mem_iff.mp hx)
  subst x
  exact Nat.fib_pos.mpr (by omega)

private theorem first_upper (n : ℕ) (hn : 2≤n) (rows : List (List ℕ)) (h : IsBarrycade n rows) :
    rows.length≤n := by
  let fst := fun r : List ℕ => r.headD 0
  have h1 (r : List ℕ) : (r.take 1).sum=fst r := by cases r <;> simp [fst]
  have hzero : 0∈List.range (n-1) := List.mem_range.mpr (by omega)
  have nd : (rows.map fst).Nodup := h.1.map_on (by
    intro a ha b hb hab
    by_contra hne
    exact h.2.2 a ha b hb hne 0 hzero 0 hzero (by simpa only [Nat.zero_add,h1] using hab))
  have sub : rows.map fst ⊆ bricks n := by
    intro x hx
    obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hx
    have rp := h.2.1 r hr
    have m := row_length rp
    apply rp.mem_iff.mp
    cases r with
    | nil => simp at m; omega
    | cons a t => simp [fst]
  simpa [bricks] using (List.subperm_of_subset nd sub).length_le

private theorem strict_prefix (r : List ℕ) (positive : ∀ x∈r, 0<x) (a b : ℕ) (hab : a<b) (hb : b≤r.length) :
    (r.take a).sum < (r.take b).sum := by
  induction r generalizing a b with
  | nil => simp at hb; omega
  | cons x r ih =>
    have hx := positive x (List.mem_cons_self ..)
    have htail : ∀ y∈r, 0<y := fun y hy => positive y (List.mem_cons_of_mem _ hy)
    cases b with
    | zero => omega
    | succ b =>
      cases a with
      | zero => simp; omega
      | succ a =>
        have hh := ih htail a b (by omega) (by simp only [List.length_cons] at hb; omega)
        simpa only [List.take_succ_cons,List.sum_cons,Nat.add_lt_add_iff_left] using hh

private theorem count_upper (n : ℕ) (hn : 2≤n) (rows : List (List ℕ)) (h : IsBarrycade n rows) :
    rows.length*(n-1)≤(bricks n).sum-1 := by
  let row := fun j : Fin rows.length => rows.get j
  let s := fun v : Fin rows.length × Fin (n-1) => ((row v.1).take (v.2.val+1)).sum
  have rp (j : Fin rows.length) := h.2.1 (row j) (rows.get_mem j)
  have bounds (v : Fin rows.length × Fin (n-1)) : 0<s v ∧ s v<(bricks n).sum := by
    have hrlen := row_length (rp v.1)
    have vp := v.2.isLt
    have hpos := row_positive (rp v.1)
    have low := strict_prefix _ hpos 0 (v.2.val+1) (by omega) (by omega)
    have high := strict_prefix _ hpos (v.2.val+1) (row v.1).length (by omega) le_rfl
    rw [List.take_length,(rp v.1).sum_eq] at high
    exact ⟨by simpa [s] using low,high⟩
  let code := fun v : Fin rows.length × Fin (n-1) => (⟨s v-1,by have := bounds v; omega⟩ : Fin ((bricks n).sum-1))
  have hi : Function.Injective code := by
    rintro ⟨i,p⟩ ⟨j,q⟩ he
    have hh := congrArg Fin.val he
    change s (i,p)-1=s (j,q)-1 at hh
    have hpos := (bounds (i,p)).1
    have hpos' := (bounds (j,q)).1
    have same : s (i,p)=s (j,q) := by omega
    have hrows : row i=row j := by
      by_contra hneq
      exact h.2.2 _ (rows.get_mem i) _ (rows.get_mem j) hneq _ (List.mem_range.mpr p.isLt) _ (List.mem_range.mpr q.isLt) same
    have hindices : i=j := h.1.get_inj_iff.mp hrows
    subst j
    have hlen := row_length (rp i)
    have hp := p.isLt
    have hq := q.isLt
    change ((row i).take (p.val+1)).sum=((row i).take (q.val+1)).sum at same
    have heq : p.val=q.val := by
      rcases lt_trichotomy p.val q.val with lt | eq | gt
      · have := strict_prefix _ (row_positive (rp i)) (p.val+1) (q.val+1) (by omega) (by omega)
        omega
      · exact eq
      · have := strict_prefix _ (row_positive (rp i)) (q.val+1) (p.val+1) (by omega) (by omega)
        omega
    rw [Fin.ext heq]
  simpa using Fintype.card_le_of_injective code hi

private theorem large_exists (k : ℕ) : ∃ rows, IsBarrycade (k+9) rows ∧ rows.length=k+9 := by
  let row (i : ℕ) := (((layout (k+3)).order.rotate i).map value)
  let rows := (List.range (k+9)).map row
  have neq (i j p q : ℕ) (hi : i<k+9) (hj : j<k+9) (hij : i≠j)
      (hp : 0<p) (hpn : p<k+9) (hq : 0<q) (hqn : q<k+9) :
      ((row i).take p).sum≠((row j).take q).sum := by
    simpa only [row,List.map_take] using cyclic_prefix_sums_distinct k i j p q hi hj hij hp hpn hq hqn
  have nd : rows.Nodup := List.nodup_range.map_on (by
    intro i hi j hj he
    by_contra hne
    have hf := neq i j 1 1 (List.mem_range.mp hi) (List.mem_range.mp hj) hne (by decide) (by omega) (by decide) (by omega)
    exact hf (congrArg (fun l : List ℕ => (l.take 1).sum) he))
  refine ⟨rows,⟨nd,?_,?_⟩,by simp [rows]⟩
  · intro r hr
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hr
    exact fibonacci_rotations_are_permutations k i
  · intro r hr s hs hrs p hp q hq
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hr
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hs
    have hne : i≠j := fun hij => hrs (hij ▸ rfl)
    have hp := List.mem_range.mp hp
    have hq := List.mem_range.mp hq
    exact neq _ _ _ _ (List.mem_range.mp hi) (List.mem_range.mp hj) hne (by omega) (by omega) (by omega) (by omega)

private def smallRows : ℕ → List (List ℕ)
  | 1 => [[1]]
  | 2 => [[1,2],[2,1]]
  | 3 => [[1,2,3],[2,3,1]]
  | 4 => [[1,3,2,5],[3,2,5,1],[2,5,1,3]]
  | 5 => [[1,3,2,5,8],[3,5,1,8,2],[5,2,8,1,3],[2,8,3,1,5]]
  | 6 => [[1,3,2,5,8,13],[3,13,1,5,2,8],[13,2,3,8,1,5],[8,1,3,13,5,2],[5,2,13,1,8,3],[2,8,13,5,3,1]]
  | 7 => (List.range 7).map (fun i => [5,2,13,3,1,8,21].rotate i)
  | 8 => (List.range 8).map (fun i => [2,5,34,13,3,1,8,21].rotate i)
  | _ => []

private theorem small_exists : ∀ n∈List.range 9, 0<n → IsBarrycade n (smallRows n) ∧
    (smallRows n).length = (if 3≤n ∧ n≤5 then n-1 else n) := by decide +kernel

/-- Complete answer for all positive orders. The maximum height is `n` except
for the three orders `3,4,5`, at which it is `n-1`. -/
theorem fibonacci_barrycade_height (n : ℕ) (hn : 0<n) :
    ExactHeight n (if 3≤n ∧ n≤5 then n-1 else n) := by
  constructor
  · by_cases hlarge : 9≤n
    · obtain ⟨k,rfl⟩ : ∃ k, n=k+9 := ⟨n-9,by omega⟩
      simpa using large_exists k
    · exact ⟨smallRows n,small_exists n (List.mem_range.mpr (by omega)) hn⟩
  · intro rows hr
    by_cases hone : n=1
    · subst n
      have hsub : rows ⊆ [[1]] := by
        intro r hmem
        have h : r.Perm [1] := hr.2.1 r hmem
        simp [h.eq_singleton]
      simpa using (List.subperm_of_subset hr.1 hsub).length_le
    by_cases hex : 3≤n ∧ n≤5
    · rw [if_pos hex]
      have bound := count_upper n (by omega) rows hr
      have hc : n=3 ∨ n=4 ∨ n=5 := by omega
      rcases hc with rfl | rfl | rfl
      · change rows.length*2≤5 at bound; omega
      · change rows.length*3≤10 at bound; omega
      · change rows.length*4≤18 at bound; omega
    · rw [if_neg hex]; exact first_upper n (by omega) rows hr

#print axioms fibonacci_barrycade_height

end FibonacciBarrycade

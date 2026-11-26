import GreedyBarrycadeStructure
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Fintype.Pi

/-!
# Eventual periodicity of each finite family of greedy barrycade rows

Index every row by triangular level `k = prefix length + number of omissions`.
Its deficit from `tri k` and its next entry's deviation from `k+1` are bounded.
The proof compares two identical finite histories and replays one next level.
-/

open Finset
namespace GreedyBarrycade

private noncomputable def countMissing (i : ℕ) := (finite_omissions i).toFinset.card
private noncomputable def atLevel (i k : ℕ) := entry i (k-countMissing i)
private noncomputable def levelSum (i k : ℕ) := partialSum i (k-countMissing i)
private noncomputable def deficit (i k : ℕ) := tri k - levelSum i k

private theorem triangleIncreasing : StrictMono tri := strictMono_nat_of_lt_succ
  (fun n => by change tri n < tri n+(n+1); omega)

private structure Frame (R : ℕ) where
  width : ℕ
  onset : ℕ
  early : ℕ
  start : ∀ i < R, countMissing i ≤ onset
  late : ∀ i < R, ∀ k ≥ onset,
    levelSum i k+deficit i k = tri k ∧ deficit i k ≤ width ∧
    atLevel i k ≤ k+1+width ∧ k+1 ≤ atLevel i k+width
  small : ∀ i < R, ∀ n, n+countMissing i < onset →
    entry i n ≤ early ∧ partialSum i n ≤ early

private noncomputable def makeFrame (R : ℕ) : Frame R := by
  classical
  choose cs ns hs using (fun i : Fin R => alignment_by_omission_count i)
  let W := (univ : Finset (Fin R)).sup cs
  let T := (univ : Finset (Fin R)).sup (fun i => ns i+countMissing i+1)
  let B := (univ : Finset (Fin R)).sup (fun i => bound (i+1))
  let E := tri (T+B)+T+B+1
  have onsetBound (i : Fin R) : ns i+countMissing i+1 ≤ T := le_sup (f := fun i : Fin R => ns i+countMissing i+1) (mem_univ i)
  refine ⟨W,T,E,?_,?_,?_⟩
  · intro i hi
    have := onsetBound ⟨i,hi⟩
    exact le_trans (by change countMissing i ≤ ns ⟨i,hi⟩+countMissing i+1; omega) this
  · intro i hi k hk
    let j : Fin R := ⟨i,hi⟩
    have ht : ns j+countMissing i+1 ≤ T := onsetBound j
    have hw : cs j ≤ W := le_sup (f:=cs) (mem_univ j)
    have hn : ns j ≤ k-countMissing i := by omega
    obtain ⟨htri,hval⟩ := hs j (k-countMissing i) hn
    change partialSum i (k-countMissing i) ≤ tri (k-countMissing i+countMissing i) ∧
      tri (k-countMissing i+countMissing i) ≤ partialSum i (k-countMissing i)+cs j at htri
    change entry i (k-countMissing i) ≤ k-countMissing i+countMissing i+1+cs j ∧
      k-countMissing i+countMissing i+1 ≤ entry i (k-countMissing i)+cs j at hval
    dsimp only [deficit,levelSum,atLevel]
    rw [show k-countMissing i+countMissing i = k by omega] at htri hval
    omega
  · intro i hi n hn
    have hb : bound (i+1) ≤ B := le_sup (f:=fun i : Fin R => bound (i+1)) (mem_univ ⟨i,hi⟩)
    have he := entry_upper_bound i n
    have hp := (partial_sums_band i n).2
    change partialSum i n ≤ tri (n+bound (i+1)) at hp
    have tt : tri (n+bound (i+1)) ≤ tri (T+B) := triangleIncreasing.monotone (by omega)
    dsimp [E]; omega

private def Frame.cut {R : ℕ} (F : Frame R) := F.early+F.onset+5*F.width+5

private theorem Frame.balance {R : ℕ} (F : Frame R) (i : ℕ) (hi : i<R) (k : ℕ) (hk : F.onset≤k) :
    atLevel i k+deficit i (k+1) = k+1+deficit i k := by
  have hd := F.start i hi
  have ha := (F.late i hi k hk).1
  have hb := (F.late i hi (k+1) (by omega)).1
  have hs : levelSum i (k+1) = levelSum i k+atLevel i k := by
    change partialSum i (k+1-countMissing i) = partialSum i (k-countMissing i)+entry i (k-countMissing i)
    rw [show k+1-countMissing i = k-countMissing i+1 by omega]
    exact sum_range_succ _ _
  rw [hs] at hb
  change _ = tri k+(k+1) at hb
  omega

private def History {R : ℕ} (F : Frame R) (k P : ℕ) :=
  ∀ i < R, ∀ q, k ≤ q+2*F.width → q ≤ k → deficit i q = deficit i (q+P)

private theorem Frame.used_recent {R : ℕ} (F : Frame R) {i k x : ℕ} (hi : i<R)
    (hk : F.cut≤k) (hlo : k+1≤x+F.width) :
    x ∈ entriesUsed i (k-countMissing i) ↔
      ∃ q, k ≤ q+2*F.width ∧ q<k ∧ atLevel i q=x := by
  have hd := F.start i hi
  dsimp only [Frame.cut] at hk
  constructor
  · intro hu
    obtain ⟨n,hn,he⟩ := (mem_entriesUsed i _ x).mp hu
    let q := n+countMissing i
    have hq : F.onset≤q := by
      by_contra h
      have hsmall := (F.small i hi n (by change q<F.onset; omega)).1
      omega
    have hbound := (F.late i hi q hq).2.2.1
    have hv : atLevel i q=x := by simpa [atLevel,q] using he
    exact ⟨q,by omega,by dsimp [q]; omega,hv⟩
  · rintro ⟨q,hq,hqk,he⟩
    apply (mem_entriesUsed i _ x).2
    exact ⟨q-countMissing i,by omega,he⟩

private theorem Frame.previous_entry_shift {R : ℕ} (F : Frame R) {i k q P : ℕ}
    (hi : i < R) (hk : F.cut≤k) (h : History F k P) (hq : k≤q+2*F.width) (hlt : q<k) :
    atLevel i (q+P) = atLevel i q+P := by
  dsimp only [Frame.cut] at hk
  have ha := F.balance i hi q (by omega)
  have hb := F.balance i hi (q+P) (by omega)
  have h0 := h i hi q hq (by omega)
  have h1 := h i hi (q+1) (by omega) (by omega)
  rw [show q+1+P = q+P+1 by omega] at h1
  omega

private theorem Frame.used_shift {R : ℕ} (F : Frame R) {i k x P : ℕ} (hi : i<R)
    (hk : F.cut≤k) (h : History F k P) (hlo : k+1≤x+F.width) :
    x ∈ entriesUsed i (k-countMissing i) ↔ x+P ∈ entriesUsed i (k+P-countMissing i) := by
  rw [F.used_recent hi hk hlo, F.used_recent hi (by omega) (by omega)]
  constructor
  · rintro ⟨q,hq,hqk,he⟩
    exact ⟨q+P,by omega,by omega,(F.previous_entry_shift hi hk h hq hqk).trans (by omega)⟩
  · rintro ⟨q,hq,hqk,he⟩
    have hcut := hk
    dsimp only [Frame.cut] at hcut
    have hshift : q-P+P = q := by omega
    have hh := F.previous_entry_shift (q:=q-P) hi hk h (by omega) (by omega)
    rw [hshift,he] at hh
    exact ⟨q-P,by omega,by omega,by omega⟩

private theorem Frame.forbidden_level {R : ℕ} (F : Frame R) {i k x : ℕ} (hi : i<R)
    (hk : F.cut≤k) (hlo : k+1≤x+F.width) (hhi : x≤k+1+F.width) :
    levelSum i k+x ∈ forbidden i ↔
      ∃ j < i, x+deficit j (k+1) = k+1+deficit i k := by
  have hcut := hk
  dsimp only [Frame.cut] at hcut
  have hd := F.start i hi
  obtain ⟨hbase,hwd,_⟩ := F.late i hi k (by omega)
  constructor
  · intro hforb
    obtain ⟨j,hj,n,_,he⟩ := (mem_forbidden i _).mp hforb
    change partialSum j n = levelSum i k+x at he
    have hjR : j<R := by omega
    let q := n+countMissing j
    have hq : F.onset≤q := by
      by_contra h
      have ha := (F.small j hjR n (by change q<F.onset; omega)).2
      omega
    have hsum : levelSum j q = levelSum i k+x := by simpa [levelSum,q] using he
    obtain ⟨htri,hqW,_⟩ := F.late j hjR q hq
    have hql : k < q := by
      by_contra h
      have := triangleIncreasing.monotone (by omega : q≤k)
      omega
    have hqh : q < k+2 := by
      by_contra h
      have hh := triangleIncreasing.monotone (by omega : k+2≤q)
      change tri k+(k+1)+(k+2) ≤ tri q at hh
      omega
    have hmatch : q=k+1 := by omega
    rw [hmatch] at htri hsum
    change levelSum j (k+1)+deficit j (k+1)=tri k+(k+1) at htri
    exact ⟨j,hj,by omega⟩
  · rintro ⟨j,hj,he⟩
    have hjR : j<R := by omega
    have hdd := F.start j hjR
    have hv := (F.late j hjR (k+1) (by omega)).1
    change levelSum j (k+1)+deficit j (k+1)=tri k+(k+1) at hv
    apply (mem_forbidden i _).2
    exact ⟨j,hj,k+1-countMissing j,by omega,by change levelSum j (k+1) = levelSum i k+x; omega⟩

private theorem Frame.legal_shift {R : ℕ} (F : Frame R) {i k x P : ℕ} (hi : i<R)
    (hk : F.cut≤k) (h : History F k P)
    (hnew : ∀ j < i, deficit j (k+1) = deficit j (k+P+1))
    (hlo : k+1≤x+F.width) (hhi : x≤k+1+F.width) :
    legal (forbidden i) (entriesUsed i (k-countMissing i)) x ↔
    legal (forbidden i) (entriesUsed i (k+P-countMissing i)) (x+P) := by
  have hbase := h i hi k (by omega) le_rfl
  have hu := F.used_shift hi hk h hlo
  have hf : levelSum i k+x ∈ forbidden i ↔ levelSum i (k+P)+(x+P) ∈ forbidden i := by
    rw [F.forbidden_level hi hk hlo hhi, F.forbidden_level hi (by omega) (by omega) (by omega)]
    constructor
    · rintro ⟨j,hj,he⟩
      exact ⟨j,hj,by have := hnew j hj; omega⟩
    · rintro ⟨j,hj,he⟩
      exact ⟨j,hj,by have := hnew j hj; omega⟩
  have hs (t : ℕ) : mass (entriesUsed i (t-countMissing i)) = levelSum i t := mass_eq_prefix_sum _ _
  unfold legal
  rw [hs,hs,hu,hf]
  dsimp only [Frame.cut] at hk
  have hxpos : 0<x := by omega
  have hxp : 0<x+P := by omega
  simp [hxpos,hxp]

private theorem Frame.next_deficits {R : ℕ} (F : Frame R) {k P : ℕ} (hk : F.cut≤k)
    (h : History F k P) : ∀ i < R, deficit i (k+1) = deficit i (k+P+1) := by
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
    intro hi
    have hcut := hk
    dsimp only [Frame.cut] at hcut
    have hnew (j : ℕ) (hj : j<i) := ih j hj (lt_trans hj hi)
    have ha := (F.late i hi k (by omega)).2.2
    have hb := (F.late i hi (k+P) (by omega)).2.2
    let a := atLevel i k
    let b := atLevel i (k+P)
    change a ≤ k+1+F.width ∧ k+1≤a+F.width at ha
    change b ≤ k+P+1+F.width ∧ k+P+1≤b+F.width at hb
    have h0 := entry_is_least i (k-countMissing i)
    have h1 := entry_is_least i ((k+P)-countMissing i)
    have haf := (F.legal_shift hi hk h hnew ha.2 ha.1).1 h0.1
    have hbl : b ≤ a+P := h1.2 _ haf
    have hrev := F.legal_shift (x:=b-P) hi hk h hnew (by omega) (by omega)
    have he : b-P+P=b := by omega
    rw [he] at hrev
    have hal : a ≤ b-P := h0.2 _ (hrev.2 h1.1)
    have hcur := h i hi k (by omega) le_rfl
    have halign := F.balance i hi k (by omega)
    have hbalign := F.balance i hi (k+P) (by omega)
    change a+_=_ at halign
    change b+_=_ at hbalign
    omega

/-- A finite stack of rows has a finite history vector. Two occurrences at
sufficiently large triangle levels must give the same future at every level. -/
private theorem Frame.repeats {R : ℕ} (F : Frame R) : ∃ P, 0<P ∧ ∃ K ≥ F.cut,
    ∀ i < R, ∀ q ≥ K, deficit i q = deficit i (q+P) := by
  classical
  let snap (a : ℕ) (i : Fin R) (j : Fin (2*F.width+1)) : Fin (F.width+1) :=
    ⟨deficit i (F.cut+a+j), Nat.lt_succ_of_le ((F.late i i.isLt (F.cut+a+j) (by dsimp [Frame.cut]; omega)).2.1)⟩
  have hdup : ∃ a b : ℕ, a<b ∧ snap a=snap b := by
    obtain ⟨a,b,hn,he⟩ := Finite.exists_ne_map_eq_of_infinite snap
    rcases lt_or_gt_of_ne hn with h | h
    · exact ⟨a,b,h,he⟩
    · exact ⟨b,a,h,he.symm⟩
  obtain ⟨a,b,hab,heq⟩ := hdup
  let P := b-a
  let K := F.cut+a+2*F.width
  have hK : F.cut ≤ K := by dsimp [K]; omega
  have hstart : History F K P := by
    intro i hi q hlow hhi
    let v : Fin (2*F.width+1) := ⟨q-(F.cut+a),by dsimp [K] at hhi; omega⟩
    have hv := congrArg Fin.val (congrFun (congrFun heq ⟨i,hi⟩) v)
    change deficit i (F.cut+a+(q-(F.cut+a))) = deficit i (F.cut+b+(q-(F.cut+a))) at hv
    dsimp only [K] at hlow hhi
    rw [show F.cut+a+(q-(F.cut+a)) = q by omega,
        show F.cut+b+(q-(F.cut+a)) = q+P by dsimp [P]; omega] at hv
    exact hv
  have hseq (t : ℕ) : History F (K+t) P := by
    induction t with
    | zero => exact hstart
    | succ t ih =>
      intro i hi q hlow hhi
      by_cases hbefore : q≤K+t
      · exact ih i hi q (by omega) hbefore
      · have hq : q=K+t+1 := by omega
        rw [hq, show K+t+1+P = K+t+P+1 by omega]
        exact F.next_deficits (by omega) ih i hi
  refine ⟨P,by dsimp [P]; omega,K,hK,?_⟩
  intro i hi q hq
  have hh := hseq (q-K) i hi q (by omega) (by omega)
  exact hh

private theorem triangle_twice (n : ℕ) : 2*tri n = n*(n+1) := by
  induction n with
  | zero => rfl
  | succ n ih => change 2*(tri n+(n+1))=(n+1)*(n+1+1); nlinarith

private theorem add_triangles (n p : ℕ) : tri (n+p) = tri n+p*n+tri p := by
  nlinarith [triangle_twice (n+p),triangle_twice n,triangle_twice p]

/-- At a common eventual period, the sum across a block determines the actual
number of omitted positive integers in each row. The central shift is measured
at the same period and threshold for all rows of the chosen finite stack. -/
theorem common_period_and_block_sum (R : ℕ) : ∃ P, 0<P ∧ ∃ N,
    ∀ i < R, ∀ n ≥ N, entry i (n+P) = entry i n+P ∧
      partialSum i (n+P) = partialSum i n + P*(n+(finite_omissions i).toFinset.card) + tri P := by
  let F := makeFrame R
  obtain ⟨P,hp,N,hN,h⟩ := F.repeats
  refine ⟨P,hp,N,?_⟩
  intro i hi n hn
  let k := n+countMissing i
  have hk : N≤k := by dsimp [k]; omega
  have hcut := hN
  dsimp only [Frame.cut] at hcut
  have ha := F.balance i hi k (by omega)
  have hb := F.balance i hi (k+P) (by omega)
  have hc := h i hi k hk
  have hd := h i hi (k+1) (by omega)
  rw [show k+1+P = k+P+1 by omega] at hd
  have he : atLevel i (k+P) = atLevel i k+P := by omega
  have hs := (F.late i hi k (by omega)).1
  have hs' := (F.late i hi (k+P) (by omega)).1
  rw [add_triangles] at hs'
  have hblock : levelSum i (k+P) = levelSum i k + P*k+tri P := by omega
  dsimp only [atLevel,k] at he
  dsimp only [levelSum,k] at hblock
  rw [show n+countMissing i+P-countMissing i = n+P by omega,
      show n+countMissing i-countMissing i = n by omega] at he hblock
  exact ⟨he,hblock⟩

/-- For every finite height, the rows share an eventual period for their
deviations from their one-based positions. Equivalently, after `P` later
positions every entry increases by exactly `P`, simultaneously in those rows. -/
theorem eventual_common_period (R : ℕ) : ∃ P, 0<P ∧ ∃ N,
    ∀ i < R, ∀ n ≥ N, entry i (n+P) = entry i n+P := by
  obtain ⟨P,hp,N,h⟩ := common_period_and_block_sum R
  exact ⟨P,hp,N,fun i hi n hn => (h i hi n hn).1⟩

#print axioms common_period_and_block_sum

end GreedyBarrycade

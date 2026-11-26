import Mathlib.Order.Bounds.Defs
import Mathlib.Data.List.Chain
import Mathlib.Data.List.Nodup

/-! Universal-vertex completion of complete multipartite graphs for perfect
cancellation orderings in the sense of Cao, Lu, Nie, Sun and Tian,
arXiv:2509.10070. See graph_universal_completion for the original
component-based definition on individually named vertices. -/

namespace Multipartite

abbrev Word := List ℕ
private def without (c : ℕ) (w : Word) : Word := w.filter (fun x => x != c)
private abbrev Linked (w : Word) := w.IsChain (· ≠ ·)
private def Mono (w : Word) : Prop := ∀ x ∈ w, ∀ y ∈ w, x = y

/-- Each position is a vertex, each label is its part. Distinct positions are
adjacent exactly when their labels differ. Deleting one vertex leaves either
a connected multipartite graph or isolated vertices of a single part. -/
def PCO (w : Word) : Prop :=
  ∀ pre v tail, w = pre ++ v :: tail → Mono (pre ++ tail) ∨ Linked (without v tail)

private def Strong (w : Word) : Prop :=
  ∀ pre v tail, w = pre ++ v :: tail → Linked (without v tail)

private theorem strong_pco (w : Word) (h : Strong w) : PCO w :=
  fun pre v tail eq => Or.inr (h pre v tail eq)

private theorem underlying_strong (w : Word) (hw : PCO w)
    (ha : 2 ≤ w.count 0) (hb : 2 ≤ w.count 1) : Strong w := by
  intro pre v tail eq
  rcases hw pre v tail eq with mono | linked
  · have keep (c : ℕ) (h : 2 ≤ w.count c) : c ∈ pre ++ tail := by
      rw [eq, List.count_append, List.count_cons] at h
      rw [← List.count_pos_iff, List.count_append]
      split at h <;> omega
    exact (Nat.zero_ne_one (mono 0 (keep 0 ha) 1 (keep 1 hb))).elim
  · exact linked

private theorem strong_tail (x : ℕ) (w : Word) (h : Strong (x::w)) : Strong w := by
  intro pre v tail eq
  exact h (x::pre) v tail (by simp [eq])

private theorem capacity (l : Word) (c : ℕ) (h : Linked l) :
    l.count c ≤ (without c l).length + if l.head? = some c then 1 else 0 := by
  induction l with
  | nil => simp [without]
  | cons a l ih =>
    have it := ih h.tail
    by_cases ac : a=c
    · subst a
      have hh : l.head? ≠ some c := by
        cases l with
        | nil => simp
        | cons b l =>
          have hb := (List.isChain_cons_cons.mp h).1
          simp [Ne.symm hb]
      simp [without, hh] at it ⊢
      omega
    · simp [without, ac] at it ⊢
      split at it <;> omega

private def extras (w : Word) : Word := (without 0 (without 1 w))

private theorem without_comm (a b : ℕ) (w : Word) :
    without a (without b w) = without b (without a w) := by
  simp [without, List.filter_filter, Bool.and_comm]

private theorem count_without (a b : ℕ) (h : a ≠ b) (w : Word) :
    (without b w).count a = w.count a :=
  List.count_filter (by simpa using h)

/-- The earliest of the two distinguished parts forces a separator between
successive surviving vertices of the other part. -/
private theorem strong_bound (w : Word) (h : Strong w) :
    min (w.count 0) (w.count 1) ≤ (extras w).length+1 := by
  induction w with
  | nil => simp [extras, without]
  | cons v w ih =>
    have ht := ih (strong_tail v w h)
    have hp := h [] v w rfl
    by_cases v0 : v=0
    · subst v
      have hc := capacity _ 1 hp
      rw [count_without 1 0 (by decide), ← without_comm 0 1] at hc
      have hh : (extras (0::w)).length = (extras w).length := by simp [extras, without]
      rw [hh]
      simp only [List.count_cons_self, List.count_cons_of_ne (by decide : (0:ℕ)≠1)]
      apply (min_le_right _ _).trans
      change _ ≤ (without 0 (without 1 w)).length+1
      split at hc <;> omega
    · by_cases v1 : v=1
      · subst v
        have hc := capacity _ 0 hp
        rw [count_without 0 1 (by decide)] at hc
        have hh : (extras (1::w)).length = (extras w).length := by simp [extras, without]
        rw [hh]
        simp only [List.count_cons_self, List.count_cons_of_ne (by decide : (1:ℕ)≠0)]
        apply (min_le_left _ _).trans
        change _ ≤ (without 0 (without 1 w)).length+1
        split at hc <;> omega
      · simp [extras, without, v0, v1] at ht ⊢
        omega

private theorem strong_cons (v : ℕ) (w : Word) (hw : Strong w)
    (h : Linked (without v w)) : Strong (v::w) := by
  intro pre u tail e
  cases pre with
  | nil =>
    have he : v = u ∧ w = tail := List.cons.inj e
    simpa [← he.1, ← he.2] using h
  | cons p pre =>
    exact hw pre u tail (List.cons.inj e).2

private def Safe (w : Word) := ∀ c, Linked (without c w)

private theorem safe_strong (w : Word) (h : Safe w) : Strong w := by
  intro pre c tail e
  have hc := h c
  rw [e] at hc
  simp only [without, List.filter_append, List.filter_cons, bne_self_eq_false, Bool.false_eq_true,
    ↓reduceIte] at hc
  exact hc.suffix ⟨_, rfl⟩

private theorem prepend_zeros (n : ℕ) (w : Word) (h : Safe w) :
    Strong (List.replicate n 0 ++ w) := by
  induction n with
  | zero => simpa using safe_strong w h
  | succ n ih =>
    rw [List.replicate_succ, List.cons_append]
    apply strong_cons 0 _ ih
    simpa [without] using h 0

private def stripe (a : ℕ) (rows : List Word) := rows.flatMap (fun r => a :: r)

/-- The final row may be empty. -/
private def Interior : List Word → Prop
  | [] => True
  | [_] => True
  | r :: s :: t => r ≠ [] ∧ Interior (s::t)

private theorem stripe_linked (a : ℕ) (rows : List Word)
    (hr : ∀ r ∈ rows, r.Nodup ∧ a ∉ r) (hi : Interior rows) : Linked (stripe a rows) := by
  induction rows with
  | nil => exact .nil
  | cons r rows ih =>
    obtain ⟨nr,ar⟩ := hr r (by simp)
    have nd : (a::r).Nodup := List.nodup_cons.mpr ⟨ar,nr⟩
    cases rows with
    | nil => simpa [stripe] using nd.isChain
    | cons s rest =>
      change r ≠ [] ∧ Interior (s::rest) at hi
      have hs := ih (fun t ht => hr t (by simp [ht])) hi.2
      change ((a::r) ++ a :: (s ++ stripe a rest)).IsChain (· ≠ ·)
      rw [List.isChain_split]
      refine ⟨?_, hs⟩
      have last : (r ++ [a]).Nodup := by
        simp [List.nodup_append', nr, ar]
      cases r with
      | nil => exact (hi.1 rfl).elim
      | cons q qs =>
        refine List.isChain_cons_cons.mpr ⟨?_, last.isChain⟩
        exact fun eq => ar (by simp [eq])

private def anchor (c : ℕ) : ℕ := if c=0 then 1 else 0
private def afterAnchor (c : ℕ) (r : Word) : Word :=
  if c=0 ∨ c=1 then r else 1 :: without c r

private theorem without_eq_self (c : ℕ) (r : Word) (h : c ∉ r) : without c r = r := by
  apply List.filter_eq_self.mpr
  intro x hx
  simpa using (fun e => h (e ▸ hx) : x ≠ c)

private theorem block_filter (c : ℕ) (r : Word) (ha : 0 ∉ r) (hb : 1 ∉ r) :
    without c (0::1::r) = anchor c :: afterAnchor c r := by
  by_cases c0 : c=0
  · subst c
    simp [without, anchor, afterAnchor, show r.filter (fun x => x != 0) = r from without_eq_self 0 r ha]
  · by_cases c1 : c=1
    · subst c
      simp [without, anchor, afterAnchor, show r.filter (fun x => x != 1) = r from without_eq_self 1 r hb]
    · simp [without, anchor, afterAnchor, c0, c1, Ne.symm c0, Ne.symm c1]

private theorem interior_map (c : ℕ) (rows : List Word) (h : Interior rows) :
    Interior (rows.map (afterAnchor c)) := by
  induction rows with
  | nil => trivial
  | cons r rows ih =>
    cases rows with
    | nil => trivial
    | cons s rest =>
      change r ≠ [] ∧ Interior (s::rest) at h
      refine ⟨?_, ih h.2⟩
      unfold afterAnchor
      split <;> simp_all

private def core (rows : List Word) : Word := rows.flatMap (fun r => 0::1::r)

private theorem core_safe (rows : List Word)
    (hr : ∀ r ∈ rows, r.Nodup ∧ 0 ∉ r ∧ 1 ∉ r) (hi : Interior rows) : Safe (core rows) := by
  intro c
  have equation : without c (core rows) = stripe (anchor c) (rows.map (afterAnchor c)) := by
    induction rows with
    | nil => rfl
    | cons r rs ih =>
      have h := hr r (by simp)
      have hi' : Interior rs := by
        cases rs with
        | nil => trivial
        | cons _ _ => exact hi.2
      have tail := ih (fun t ht => hr t (by simp [ht])) hi'
      change without c ((0::1::r) ++ core rs) = (anchor c :: afterAnchor c r) ++ _
      rw [show without c ((0::1::r) ++ core rs) = without c (0::1::r) ++ without c (core rs) from List.filter_append _ _, block_filter _ _ h.2.1 h.2.2, tail]
      rfl
  rw [equation]
  refine stripe_linked _ _ ?_ (interior_map c rows hi)
  intro s hs
  obtain ⟨r, hrmem, rfl⟩ := List.mem_map.mp hs
  obtain ⟨hn,h0,h1⟩ := hr r hrmem
  by_cases c0 : c=0
  · simp [anchor,afterAnchor,c0,hn,h1]
  · by_cases c1 : c=1
    · simp [anchor,afterAnchor,c1,hn,h0]
    · have nd : (without c r).Nodup := List.Nodup.filter _ hn
      simp [anchor,afterAnchor,c0,c1,without,show (r.filter (fun x => x != c)).Nodup from nd,h0,h1]

abbrev Parts := List (ℕ × ℕ)

/-- A part (c,m) consists of m vertices with label c. The two distinguished
parts have labels 0 and 1. Arbitrary other labels may be used. -/
def inventory (ps : Parts) : Word := ps.flatMap (fun p => List.replicate p.2 p.1)

def Valid (b : ℕ) (ps : Parts) : Prop :=
  (ps.map Prod.fst).Nodup ∧ ∀ p ∈ ps, 2 ≤ p.1 ∧ p.2 ≤ b

private theorem inventory_avoids (ps : Parts) (c : ℕ) (h : c ∉ ps.map Prod.fst) :
    c ∉ inventory ps := by
  intro hc
  obtain ⟨p, hp, hc⟩ := List.mem_flatMap.mp hc
  have hh := List.eq_of_mem_replicate hc
  exact h (List.mem_map.mpr ⟨p, hp, hh.symm⟩)

private theorem inventory_clean (b : ℕ) (ps : Parts) (v : Valid b ps) :
    0 ∉ inventory ps ∧ 1 ∉ inventory ps := by
  constructor <;> apply inventory_avoids <;> intro h
  all_goals
    obtain ⟨p, hp, eq⟩ := List.mem_map.mp h
    have := (v.2 p hp).1
    omega

private theorem singleton_flatten (n c : ℕ) :
    (List.replicate n [c]).flatten = List.replicate n c := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, ih]

private theorem prepend_count (c j : ℕ) (rows : List Word) :
    ((rows.map (c::·)).flatten).count j =
      rows.flatten.count j + if c=j then rows.length else 0 := by
  induction rows with
  | nil => simp
  | cons r rows ih =>
    by_cases h : c=j
    · subst j
      simp [ih]
      omega
    · simp [ih, h]

private def RowOK (r : Word) := r ≠ [] ∧ r.Nodup ∧ 0 ∉ r ∧ 1 ∉ r

/-- Fill empty rows first, then add the new color to distinct existing rows. -/
private theorem pack (b : ℕ) (ps : Parts) (v : Valid b ps) :
    ∃ rows : List Word, (∀ r ∈ rows, RowOK r) ∧
      rows.length = min b (inventory ps).length ∧
      ∀ j, rows.flatten.count j = (inventory ps).count j := by
  induction ps with
  | nil => exact ⟨[], by simp, by simp [inventory], by simp [inventory]⟩
  | cons p ps ih =>
    rcases p with ⟨c,m⟩
    obtain ⟨hc,hm⟩ := v.2 (c,m) (by simp)
    have distinct := List.nodup_cons.mp v.1
    have old : Valid b ps := ⟨distinct.2, fun q hq => v.2 q (by simp [hq])⟩
    obtain ⟨rows, ok, size, counts⟩ := ih old
    have absent : c ∉ rows.flatten := by
      have h0 : (inventory ps).count c = 0 := List.count_eq_zero.mpr (inventory_avoids ps c distinct.1)
      exact List.count_eq_zero.mp ((counts c).trans h0)
    let e := min m (b - rows.length)
    let d := m-e
    have hd : d ≤ rows.length := by dsimp [d,e]; omega
    have hs : d+e=m := by dsimp [d,e]; omega
    let picked := rows.take d
    let rest := rows.drop d
    let made := List.replicate e [c] ++ picked.map (c::·) ++ rest
    have plen : picked.length = d := by simp [picked, Nat.min_eq_left hd]
    have splitRows : picked ++ rest = rows := List.take_append_drop d rows
    refine ⟨made, ?_, ?_, ?_⟩
    · intro r hr
      simp only [made, List.mem_append, List.mem_map] at hr
      rcases hr with (hf | ⟨s,hs',rfl⟩) | ht
      · have eq := List.eq_of_mem_replicate hf
        subst r
        simp [RowOK]
        omega
      · have mem : s ∈ rows := (List.mem_of_mem_take hs')
        have oldok := ok s mem
        have nc : c ∉ s := fun he => absent (List.mem_flatten.mpr ⟨s,mem,he⟩)
        simp [RowOK, oldok.2.1, oldok.2.2.1, oldok.2.2.2, nc]
        omega
      · exact ok _ (List.mem_of_mem_drop ht)
    · simp only [made, List.length_append, List.length_replicate, List.length_map, plen,
        rest, List.length_drop, inventory, List.flatMap_cons, List.length_append, List.length_replicate]
      change e+d+(rows.length-d) = min b (m+(inventory ps).length)
      dsimp [e]
      omega
    · intro j
      have cs : picked.flatten.count j + rest.flatten.count j = (inventory ps).count j := by
        rw [← counts, ← splitRows, List.flatten_append, List.count_append]
      simp only [made, List.flatten_append, List.count_append, singleton_flatten, prepend_count, plen,
        inventory, List.flatMap_cons, List.count_append]
      change (List.replicate e c).count j + (picked.flatten.count j + (if c=j then d else 0)) +
          rest.flatten.count j = (List.replicate m c).count j + (inventory ps).count j
      by_cases eq : c=j <;> simp [eq, List.count_replicate] <;> omega

private theorem interior_nonempty (rows : List Word) (hr : ∀ r ∈ rows, r ≠ [])
    (last : List Word) (hl : last = [] ∨ last = [[]]) : Interior (rows ++ last) := by
  induction rows with
  | nil => rcases hl with rfl | rfl <;> trivial
  | cons r rs ih =>
    have ht := ih (fun x hx => hr x (by simp [hx]))
    cases h : rs ++ last with
    | nil => simp [h, Interior]
    | cons s rest =>
      change Interior (r :: (rs ++ last))
      rw [h]
      exact ⟨hr r (by simp), h ▸ ht⟩

private theorem core_count (rows : List Word) (j : ℕ) :
    (core rows).count j = rows.flatten.count j +
      (if j=0 then rows.length else 0) + (if j=1 then rows.length else 0) := by
  induction rows with
  | nil => simp [core]
  | cons r rs ih =>
    change ((0::1::r) ++ core rs).count j = _
    rw [List.count_append, ih]
    by_cases h0 : j=0
    · subst j
      simp
      omega
    · by_cases h1 : j=1
      · subst j
        simp
        omega
      · simp [h0,h1,Ne.symm h0,Ne.symm h1]

/-- The underlying graph contains a single vertex per occurrence of its part label. -/
def shape (a b : ℕ) (ps : Parts) : Word :=
  List.replicate a 0 ++ List.replicate b 1 ++ inventory ps

/-- A permutation of the vertices is freely chosen. Equal part labels mean
distinct twins, whose relative names do not affect adjacency or the order test. -/
def admits (a b : ℕ) (ps : Parts) : Prop :=
  ∃ w : Word, w.Perm (shape a b ps) ∧ PCO w

private theorem shape_01 (a b : ℕ) (ps : Parts) (v : Valid b ps) :
    (shape a b ps).count 0 = a ∧ (shape a b ps).count 1 = b := by
  obtain ⟨h0,h1⟩ := inventory_clean b ps v
  simp [shape, List.count_replicate, List.count_eq_zero.mpr h0, List.count_eq_zero.mpr h1]

private theorem extras_shape (a b : ℕ) (ps : Parts) (v : Valid b ps) :
    extras (shape a b ps) = inventory ps := by
  obtain ⟨h0,h1⟩ := inventory_clean b ps v
  have e0 := without_eq_self 0 (inventory ps) h0
  have e1 := without_eq_self 1 (inventory ps) h1
  simpa [extras,shape,without] using (show without 0 (without 1 (inventory ps)) = inventory ps by rw [e1,e0])

/-- A complete multipartite graph admits a perfect cancellation ordering
precisely when all parts other than the two largest provide b−1 separators. -/
theorem classification (a b : ℕ) (ps : Parts) (ba : b ≤ a) (v : Valid b ps) :
    admits a b ps ↔ b ≤ (inventory ps).length+1 := by
  constructor
  · rintro ⟨w,pw,hw⟩
    by_cases small : b ≤ 1
    · omega
    obtain ⟨h0,h1⟩ := shape_01 a b ps v
    have c0 := (List.perm_iff_count.mp pw 0).trans h0
    have c1 := (List.perm_iff_count.mp pw 1).trans h1
    have bound := strong_bound w (underlying_strong w hw (by omega) (by omega))
    have pe : (extras w).Perm (extras (shape a b ps)) :=
      (pw.filter (fun x => x != 1)).filter (fun x => x != 0)
    rw [c0, c1, Nat.min_eq_right ba, pe.length_eq, extras_shape a b ps v] at bound
    exact bound
  · intro hb
    obtain ⟨rows, ok, size, counts⟩ := pack b ps v
    let gap := b-rows.length
    let pad : List Word := List.replicate gap []
    let rows' := rows ++ pad
    have hg : gap=0 ∨ gap=1 := by dsimp [gap]; omega
    have pp : pad = [] ∨ pad = [[]] := by
      rcases hg with h | h <;> simp [pad,h]
    have hp : pad.flatten = [] := by rcases pp with h | h <;> simp [h]
    have lengthRows : rows'.length=b := by simp [rows',pad,gap]; omega
    have safe : Safe (core rows') := by
      apply core_safe
      · intro r hr
        rcases List.mem_append.mp hr with h | h
        · exact (ok r h).2
        · rcases pp with h0 | h1
          · simp [h0] at h
          · simp [h1] at h
            simp [h]
      · exact interior_nonempty rows (fun r hr => (ok r hr).1) pad pp
    let w := List.replicate (a-b) 0 ++ core rows'
    refine ⟨w, List.perm_iff_count.mpr ?_, strong_pco _ (prepend_zeros _ _ safe)⟩
    intro j
    have ctr := core_count rows' j
    simp only [rows', List.flatten_append, hp, List.append_nil, counts] at ctr
    change (List.replicate (a-b) 0 ++ core rows').count j = _
    rw [List.count_append, ctr]
    simp only [shape, List.count_append, List.count_replicate]
    change (if 0 == j then a-b else 0) + ((inventory ps).count j +
        (if j=0 then rows'.length else 0) + (if j=1 then rows'.length else 0)) = _
    rw [lengthRows]
    by_cases j0 : j=0
    · subst j
      simp
      omega
    · by_cases j1 : j=1
      · subst j
        simp [Nat.add_comm]
      · simp [j0,j1,Ne.symm j0,Ne.symm j1]

/-- Add k fresh singleton parts. Original extra labels are shifted by k. -/
def extend (k : ℕ) (ps : Parts) : Parts :=
  (List.range k).map (fun i => (i+2,1)) ++ ps.map (fun p => (p.1+k,p.2))

private theorem valid_extend (b k : ℕ) (ps : Parts) (bpos : 1 ≤ b) (v : Valid b ps) :
    Valid b (extend k ps) := by
  constructor
  · simp only [extend, List.map_append, List.map_map, List.nodup_append']
    constructor
    · exact List.Nodup.map (fun _ _ e => Nat.add_right_cancel e) List.nodup_range
    constructor
    · change (ps.map (((·+k) : ℕ → ℕ) ∘ Prod.fst)).Nodup
      rw [← List.map_map]
      exact List.Nodup.map (fun _ _ e => Nat.add_right_cancel e) v.1
    · intro x h1 h2
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp h1
      obtain ⟨p, hp, eq⟩ := List.mem_map.mp h2
      change p.1+k = i+2 at eq
      have hi' := List.mem_range.mp hi
      have hp' := (v.2 p hp).1
      omega
  · intro p hp
    rcases List.mem_append.mp hp with hs | ho
    · obtain ⟨i,_,rfl⟩ := List.mem_map.mp hs
      exact ⟨by simp,bpos⟩
    · obtain ⟨q,hq,rfl⟩ := List.mem_map.mp ho
      have hv := v.2 q hq
      exact ⟨by simp; omega,hv.2⟩

private theorem extended_size (k : ℕ) (ps : Parts) :
    (inventory (extend k ps)).length = k+(inventory ps).length := by
  have singles (l : List ℕ) :
      (inventory (l.map (fun i => (i+2,1)))).length = l.length := by
    induction l with
    | nil => rfl
    | cons i l ih =>
      change (List.replicate 1 (i+2) ++ _).length = _
      simp only [List.length_append, List.length_replicate, List.length_cons]
      change 1 + (inventory (l.map (fun i => (i+2,1)))).length = l.length+1
      rw [ih, Nat.add_comm]
  have shifted (l : Parts) :
      (inventory (l.map (fun p => (p.1+k,p.2)))).length = (inventory l).length := by
    induction l with
    | nil => rfl
    | cons p l ih =>
      change (List.replicate p.2 (p.1+k) ++ _).length = (List.replicate p.2 p.1 ++ _).length
      simp only [List.length_append, List.length_replicate]
      exact congrArg (p.2+·) ih
  change (List.flatMap _ (_ ++ _)).length = _
  rw [List.flatMap_append, List.length_append]
  change (inventory _).length + (inventory _).length = _
  rw [singles, shifted, List.length_range]

/-- A graph with just one independent part, including the empty graph,
already has a perfect cancellation ordering. -/
theorem independent_needs_no_hubs (a : ℕ) : admits a 0 (extend 0 []) := by
  have v : Valid 0 [] := by simp [Valid]
  simpa [extend] using (classification a 0 [] (Nat.zero_le a) v).mpr (by simp [inventory])

/-- The exact threshold for universal completion, valid for every number
of nonempty parts in addition to the two distinguished positive parts. -/
theorem universal_completion (a b k : ℕ) (ps : Parts) (ba : b ≤ a)
    (bpos : 1 ≤ b) (v : Valid b ps) :
    admits a b (extend k ps) ↔ b-1-(inventory ps).length ≤ k := by
  rw [classification a b _ ba (valid_extend b k ps bpos v), extended_size]
  omega

/-- The least number of added universal vertices is attained. -/
theorem least_universal (a b : ℕ) (ps : Parts) (ba : b ≤ a) (bpos : 1 ≤ b) (v : Valid b ps) :
    IsLeast {k : ℕ | admits a b (extend k ps)} (b-1-(inventory ps).length) :=
  ⟨(universal_completion _ _ _ _ ba bpos v).mpr le_rfl,
    fun _ hk => (universal_completion _ _ _ _ ba bpos v).mp hk⟩

/-- In particular the required minimum for K_{a,b}, when b ≤ a, is b−1. -/
theorem complete_bipartite (a b k : ℕ) (ba : b ≤ a) (bpos : 1 ≤ b) :
    admits a b (extend k []) ↔ b-1 ≤ k := by
  simpa [inventory] using universal_completion a b k [] ba bpos (by simp [Valid])

#print axioms classification
#print axioms universal_completion
#print axioms least_universal
#print axioms complete_bipartite

/-- Reachability by graph edges between remaining vertices. The lists contain
actual vertex identities; the part function can assign twins the same color. -/
inductive Reach {V : Type} (color : V → ℕ) (remaining : List V) (u : V) : V → Prop
  | self : Reach color remaining u u
  | step {x z} : Reach color remaining u x → x ∈ remaining → z ∈ remaining →
      color x ≠ color z → Reach color remaining u z

/-- Deleting the chosen vertex leaves isolates exactly when all remaining
parts coincide. Otherwise every two vertices are joined in at most two steps. -/
theorem component_criterion {V : Type} (color : V → ℕ) (s : List V) (u x : V)
    (hu : u ∈ s) (hx : x ∈ s) :
    Reach color s u x ↔ u=x ∨ ¬ Mono (s.map color) := by
  constructor
  · intro h
    by_cases hm : Mono (s.map color)
    · left
      induction h with
      | self => rfl
      | step _ ha hb ne _ =>
        exact (ne (hm _ (List.mem_map_of_mem ha) _ (List.mem_map_of_mem hb))).elim
    · exact Or.inr hm
  · rintro (rfl | nm)
    · exact .self
    · by_cases eq : color u = color x
      · have other : ∃ z ∈ s, color z ≠ color u := by
          by_contra! same
          apply nm
          intro a ha b hb
          obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ha
          obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hb
          exact (same i hi).trans (same j hj).symm
        obtain ⟨z, hz, hn⟩ := other
        exact .step (.step .self hu hz hn.symm) hz hx (eq ▸ hn)
      · exact .step .self hu hx eq

/-- Apply the source paper's condition in the component of u after removing v.
Every later neighbor in that component is retained, in the given order. -/
noncomputable def componentNeighbors {V : Type} (color : V → ℕ) (pre : List V)
    (v : V) (tail : List V) (u : V) : List V := by
  classical
  exact tail.filter (fun x => decide (color x ≠ color v ∧ Reach color (pre++tail) u x))

def graphLocal {V : Type} (color : V → ℕ) (pre : List V) (v : V) (tail : List V) : Prop :=
  ∀ u ∈ pre ++ tail, Linked ((componentNeighbors color pre v tail u).map color)

/-- The paper's component-wise definition, applied to a list of distinct
named vertices of a complete multipartite graph. -/
def graphOrdering {V : Type} (color : V → ℕ) (order : List V) : Prop :=
  ∀ pre v tail, order = pre ++ v::tail → graphLocal color pre v tail

private theorem in_connected {V : Type} (color : V → ℕ) (pre : List V) (v : V)
    (tail : List V) (u : V) (hu : u ∈ pre++tail) (hm : ¬ Mono ((pre++tail).map color)) :
    (componentNeighbors color pre v tail u).map color = without (color v) (tail.map color) := by
  classical
  rw [componentNeighbors, without, List.filter_map]
  apply congrArg (List.map color)
  apply List.filter_congr
  intro x hx
  have hc := (component_criterion color (pre++tail) u x hu (List.mem_append_right _ hx)).mpr (Or.inr hm)
  by_cases eq : color x = color v <;> simp [Function.comp_apply,hc,eq]

private theorem local_criterion {V : Type} (color : V → ℕ) (pre : List V) (v : V)
    (tail : List V) (hd : tail.Nodup) :
    graphLocal color pre v tail ↔
      Mono ((pre++tail).map color) ∨ Linked (without (color v) (tail.map color)) := by
  classical
  by_cases hm : Mono ((pre++tail).map color)
  · refine ⟨fun _ => Or.inl hm, fun _ u hu => ?_⟩
    let nbr := componentNeighbors color pre v tail u
    have nd : nbr.Nodup := List.Nodup.filter _ hd
    have huOnly (x : V) (hx : x ∈ nbr) : u=x := by
      have eq := List.mem_filter.mp hx
      have hc : color x ≠ color v ∧ Reach color (pre++tail) u x := of_decide_eq_true eq.2
      exact ((component_criterion color _ u x hu (List.mem_append_right _ eq.1)).mp hc.2).resolve_right (not_not.mpr hm)
    change Linked (nbr.map color)
    cases e : nbr with
    | nil => exact .nil
    | cons a l =>
      cases l with
      | nil => exact .singleton _
      | cons b t =>
        have ab : a≠b := fun eq => (List.nodup_cons.mp (e ▸ nd)).1 (by simp [eq])
        exact (ab ((huOnly a (by simp [e])).symm.trans (huOnly b (by simp [e])))).elim
  · constructor
    · intro h
      right
      cases tail with
      | nil => exact .nil
      | cons x xs =>
        have hu : x ∈ pre ++ x::xs := by simp
        have hh := h x hu
        rwa [in_connected _ _ _ _ _ hu hm] at hh
    · rintro (mono | linked) u hu
      · exact (hm mono).elim
      · rwa [in_connected _ _ _ _ _ hu hm]

/-- Exact equivalence to the component-wise graph definition, including
articulation vertices. -/
theorem graphOrdering_iff {V : Type} (color : V → ℕ) (order : List V) (hd : order.Nodup) :
    graphOrdering color order ↔ PCO (order.map color) := by
  constructor
  · intro h pre v tail eq
    obtain ⟨p,q,ho,hp,hq⟩ := List.map_eq_append_iff.mp eq
    obtain ⟨u,s,hq',hu,hs⟩ := List.map_eq_cons_iff.mp hq
    subst q
    subst pre
    subst v
    subst tail
    have ds : s.Nodup := (List.nodup_cons.mp (List.nodup_append'.mp (ho ▸ hd)).2.1).2
    simpa only [List.map_append] using (local_criterion color p u s ds).mp (h p u s ho)
  · intro h pre v tail eq
    have ds := (List.nodup_cons.mp (List.nodup_append'.mp (eq ▸ hd)).2.1).2
    apply (local_criterion color pre v tail ds).mpr
    simpa only [List.map_append] using h (pre.map color) (color v) (tail.map color) (by simp [eq])

#print axioms graphOrdering_iff

private theorem lift_order {V : Type} (color : V → ℕ) {l r : Word} (p : l.Perm r)
    (xs : List V) (eq : xs.map color = l) :
    ∃ ys, xs.Perm ys ∧ ys.map color = r := by
  induction p generalizing xs with
  | nil => cases xs <;> simp_all
  | cons x p ih =>
    obtain ⟨v,t,rfl,hv,ht⟩ := List.map_eq_cons_iff.mp eq
    obtain ⟨s,ps,hs⟩ := ih t ht
    exact ⟨v::s, ps.cons v, by simp [hv,hs]⟩
  | swap x y t =>
    obtain ⟨v,s,rfl,hv,hs⟩ := List.map_eq_cons_iff.mp eq
    obtain ⟨u,q,rfl,hu,hq⟩ := List.map_eq_cons_iff.mp hs
    exact ⟨u::v::q, List.Perm.swap _ _ _, by simp [hu,hv,hq]⟩
  | trans p q ih₁ ih₂ =>
    obtain ⟨s,ps,es⟩ := ih₁ xs eq
    obtain ⟨t,pt,et⟩ := ih₂ s es
    exact ⟨t,ps.trans pt,et⟩

/-- Existence in the color-word model is equivalent to an actual ordering
of the distinct input vertices satisfying the original component definition. -/
theorem named_vertices {V : Type} (color : V → ℕ) (vertices : List V) (hd : vertices.Nodup)
    (a b : ℕ) (ps : Parts) (labels : (vertices.map color).Perm (shape a b ps)) :
    (∃ order, order.Perm vertices ∧ graphOrdering color order) ↔ admits a b ps := by
  constructor
  · rintro ⟨order,perm,ho⟩
    exact ⟨order.map color, (perm.map color).trans labels,
      (graphOrdering_iff color order (perm.nodup_iff.mpr hd)).mp ho⟩
  · rintro ⟨w,pw,hw⟩
    obtain ⟨order,po,eq⟩ := lift_order color (labels.trans pw.symm) vertices rfl
    exact ⟨order,po.symm,(graphOrdering_iff color order (po.nodup_iff.mp hd)).mpr (eq ▸ hw)⟩

/-- The universal-completion threshold, stated on individually named
vertices and the original graph component test. -/
theorem graph_universal_completion {V : Type} (color : V → ℕ) (vertices : List V)
    (hd : vertices.Nodup) (a b k : ℕ) (ps : Parts) (ba : b ≤ a) (bpos : 1 ≤ b)
    (v : Valid b ps) (labels : (vertices.map color).Perm (shape a b (extend k ps))) :
    (∃ order, order.Perm vertices ∧ graphOrdering color order) ↔
      b-1-(inventory ps).length ≤ k :=
  (named_vertices color vertices hd a b (extend k ps) labels).trans
    (universal_completion a b k ps ba bpos v)

#print axioms graph_universal_completion

end Multipartite

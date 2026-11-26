import FibonacciCircleAutomaton
import Mathlib.Data.List.Perm.Basic
import Mathlib.Algebra.BigOperators.Group.List.Lemmas

/-! The circle of Fibonacci indices and its actual cyclic permutation rows. -/
namespace FibonacciBarrycade

/-- The two blocks start with indices 4 and 1. The low indices in the two
blocks are `[4,0,2]` and `[1,5,3]`, respectively. -/
structure Layout where
  evenTail : List ℕ
  oddTail : List ℕ
  nextOdd : Bool
  deriving DecidableEq

def layout : ℕ → Layout
  | 0 => ⟨[0,2],[5,3],false⟩
  | k+1 =>
    let p := layout k
    if p.nextOdd then ⟨p.evenTail,p.oddTail++[k+6],false⟩
    else ⟨p.evenTail++[k+6],p.oddTail,true⟩

def Layout.order (l : Layout) : List ℕ := (4::l.evenTail)++(1::l.oddTail)

def flips (prev : Bool) : List Bool → ℕ
  | [] => 0
  | x::xs => delta prev x+flips x xs

def cyclicFlips : List Bool → ℕ
  | [] => 0
  | x::xs => flips x (xs++[x])

private theorem flips_append (b : Bool) (l t : List Bool) :
    flips b (l++t)=flips b l+flips (l.getLastD b) t := by
  induction l generalizing b with
  | nil => simp [flips]
  | cons a l ih =>
    rw [List.cons_append,flips,flips,ih]
    have hl : (a::l).getLastD b=l.getLastD a := by cases l <;> rfl
    rw [hl]; omega

private theorem cyclic_two (a b : Bool) (u v : List Bool) :
    cyclicFlips ((a::u)++(b::v)) = flips a u+flips b v+
      delta (u.getLastD a) b+delta (v.getLastD b) a := by
  change flips a ((u++b::v)++[a])=_
  rw [List.append_assoc,flips_append]
  change flips a u+(delta (u.getLastD a) b+flips b (v++[a]))=_
  rw [flips_append]
  simp only [flips,Nat.add_zero]
  omega

private theorem cyclic_comm (a b : List Bool) : cyclicFlips (a++b)=cyclicFlips (b++a) := by
  cases a with
  | nil => simp
  | cons a u => cases b with
    | nil => simp
    | cons b v => rw [cyclic_two,cyclic_two]; omega

private theorem cyclic_rotate (l : List Bool) (j : ℕ) : cyclicFlips (l.rotate j)=cyclicFlips l := by
  rw [List.rotate_eq_drop_append_take_mod,cyclic_comm,List.take_append_drop]

private def summarize (L : Layout) (f : ℕ → Colour) : Shape :=
  let a := fun i => (f i).1
  let b := fun i => (f i).2
  ⟨f 4,f (L.evenTail.getLastD 4),f 1,f (L.oddTail.getLastD 1),
    flips (a 4) (L.evenTail.map a)+flips (a 1) (L.oddTail.map a),
    flips (b 4) (L.evenTail.map b)+flips (b 1) (L.oddTail.map b),
    (L.order.any fun i => differs (f i)),L.nextOdd⟩

private theorem shape_exact (f : ℕ → Colour) (k : ℕ) : shape f k=summarize (layout k) f := by
  induction k with
  | zero =>
    simp [shape,layout,summarize,lowShape,Layout.order,flips,Nat.add_assoc,Bool.or_assoc,Bool.or_left_comm,Bool.or_comm]
  | succ k ih =>
    rw [shape,ih,layout]
    generalize layout k = p
    obtain ⟨e,o,b⟩ := p
    cases b <;>
      simp [Shape.push,summarize,Layout.order,flips_append,flips,
        Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,Bool.or_comm,Bool.or_left_comm]

private theorem shape_cyclic (f : ℕ→Colour) (k : ℕ) :
    (shape f k).cyclicA=cyclicFlips ((layout k).order.map fun i=>(f i).1) ∧
    (shape f k).cyclicB=cyclicFlips ((layout k).order.map fun i=>(f i).2) := by
  have h (g : ℕ→Bool) : cyclicFlips ((layout k).order.map g) =
      flips (g 4) ((layout k).evenTail.map g)+flips (g 1) ((layout k).oddTail.map g)+
      delta (g ((layout k).evenTail.getLastD 4)) (g 1)+delta (g ((layout k).oddTail.getLastD 1)) (g 4) := by
    rw [Layout.order,List.map_append,List.map_cons,List.map_cons,cyclic_two]
    rw [List.getLastD_map,List.getLastD_map]
  rw [shape_exact,h,h]
  exact ⟨rfl,rfl⟩

private theorem layout_perm (k : ℕ) : (layout k).order.Perm (List.range (k+6)) := by
  induction k with
  | zero => decide
  | succ k ih =>
    rw [layout,List.range_succ]
    cases h : (layout k).nextOdd
    · simp only [Bool.false_eq_true,if_false,Layout.order]
      have move := List.perm_middle (a:=k+6) (l₁:=4::(layout k).evenTail) (l₂:=1::(layout k).oddTail)
      have step := move.trans (ih.cons (k+6))
      have last := (List.perm_append_singleton (k+6) (List.range (k+6))).symm
      simpa [Layout.order,List.append_assoc] using step.trans last
    · simp only [if_true,Layout.order]
      simpa [Layout.order,List.append_assoc] using ih.append_right [k+6]

private theorem flips_equal_run (b : Bool) (n : ℕ) : flips b (List.replicate n b)=0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ,flips,delta,ih]

private theorem closed_two_runs (m n : ℕ) : cyclicFlips (List.replicate m true ++ List.replicate n false)≤2 := by
  cases m with
  | zero =>
    cases n with
    | zero => decide
    | succ n =>
      simp [List.replicate_succ,cyclicFlips,flips_append,flips,flips_equal_run,delta]; split <;> decide
  | succ m =>
    cases n with
    | zero => simp [List.replicate_succ,cyclicFlips,flips_append,flips,flips_equal_run,delta]; split <;> decide
    | succ n =>
      rw [List.replicate_succ,List.replicate_succ,cyclic_two,flips_equal_run,flips_equal_run]
      simp [delta]; split <;> split <;> decide

private theorem split_disjoint (l : List ℕ) (hl : l.Nodup) (k : ℕ) :
    ∀ x ∈ l.take k, ∀ y ∈ l.drop k, x≠y := by
  have hparts : (l.take k++l.drop k).Nodup := by simpa using hl
  exact (List.nodup_append.mp hparts).2.2

private theorem indicator_variation (l : List ℕ) (hl : l.Nodup) (j k : ℕ) :
    cyclicFlips (l.map fun x => decide (x∈(l.rotate j).take k))≤2 := by
  let rotated := l.rotate j
  let u := rotated.take k
  let v := rotated.drop k
  let bit := fun x : ℕ => decide (x∈u)
  have rotNodup : rotated.Nodup := List.nodup_rotate.mpr hl
  have hu : u.map bit=List.replicate u.length true := List.map_eq_replicate_iff.mpr (fun x hx => by simp [bit,hx])
  have hv : v.map bit=List.replicate v.length false := by
    apply List.map_eq_replicate_iff.mpr
    intro x hx
    have hnot : x∉u := fun hh => split_disjoint rotated rotNodup k x hh x hx rfl
    simp [bit,hnot]
  have hle : cyclicFlips (rotated.map bit)≤2 := by
    rw [← List.take_append_drop k rotated,List.map_append]
    change cyclicFlips (u.map bit++v.map bit)≤2
    rw [hu,hv]
    exact closed_two_runs _ _
  change cyclicFlips (l.map bit)≤2
  rw [← cyclic_rotate (l.map bit) j,← List.map_rotate]
  exact hle

/-- The entries are the positive Fibonacci numbers, starting with 1, 2. -/
def value (i : ℕ) : ℕ := Nat.fib (i+2)

private def zsum (u : List ℕ) : ℤ := (u.map (fun i => (value i : ℤ))).sum

private theorem zsum_eq (u : List ℕ) : zsum u=((u.map value).sum : ℤ) := by
  induction u with
  | nil => rfl
  | cons x u ih => simp [zsum] at ih ⊢; omega

private theorem indicator_weight (l : List ℕ) (hl : l.Nodup) (k : ℕ) :
    (l.map (fun x => if x∈l.take k then (value x : ℤ) else 0)).sum=zsum (l.take k) := by
  let u := l.take k
  let v := l.drop k
  let w := fun x : ℕ => if x∈u then (value x : ℤ) else 0
  have hu : u.map w = u.map (fun x => (value x : ℤ)) := List.map_eq_map_iff.mpr (fun x hx => by simp [w,hx])
  have hv : v.map w = List.replicate v.length 0 := by
    apply List.map_eq_replicate_iff.mpr
    intro x hx
    have hnot : x∉u := fun hh => split_disjoint l hl k x hh x hx rfl
    simp [w,hnot]
  change (l.map w).sum=zsum u
  conv_lhs => rw [← List.take_append_drop k l,List.map_append,List.sum_append]
  change (u.map w).sum+(v.map w).sum=zsum u
  rw [hu,hv]
  simp [zsum]

private theorem signed_range (f : ℕ→Colour) (n : ℕ) :
    signedSum f n=((List.range n).map fun i => sign (f i)*(value i : ℤ)).sum := by
  induction n with
  | zero => rfl
  | succ n ih => simp [signedSum,ih,List.range_succ,value]

private theorem difference_sum (l : List ℕ) (a b : ℕ→ℤ) :
    (l.map (fun i => a i-b i)).sum = (l.map a).sum-(l.map b).sum := by
  induction l with
  | nil => simp
  | cons x l ih => simp only [List.map_cons,List.sum_cons,ih]; omega

private theorem prefix_sets_same (k i j p q : ℕ)
    (he : ((((layout (k+3)).order.rotate i).take p).map value).sum=
      ((((layout (k+3)).order.rotate j).take q).map value).sum) :
    ∀ x, x∈((layout (k+3)).order.rotate i).take p ↔ x∈((layout (k+3)).order.rotate j).take q := by
  let l := (layout (k+3)).order
  let a := (l.rotate i).take p
  let b := (l.rotate j).take q
  let f := fun x : ℕ => (decide (x∈a),decide (x∈b))
  let wa := fun x : ℕ => if x∈a then (value x : ℤ) else 0
  let wb := fun x : ℕ => if x∈b then (value x : ℤ) else 0
  have perm : l.Perm (List.range (k+9)) := layout_perm (k+3)
  have nodup := perm.nodup_iff.mpr List.nodup_range
  have hw (x : ℕ) : sign (f x)*(value x : ℤ)=wa x-wb x := by
    by_cases ha : x∈a <;> by_cases hb : x∈b <;> simp [wa,wb,f,ha,hb,sign]
  have aw : ((List.range (k+9)).map wa).sum=zsum a := by
    have pp := ((l.rotate_perm i).trans perm).map wa
    exact pp.sum_eq.symm.trans (indicator_weight _ (List.nodup_rotate.mpr nodup) _)
  have bw : ((List.range (k+9)).map wb).sum=zsum b := by
    have pp := ((l.rotate_perm j).trans perm).map wb
    exact pp.sum_eq.symm.trans (indicator_weight _ (List.nodup_rotate.mpr nodup) _)
  have sumzero : signedSum f (k+9)=0 := by
    rw [signed_range, show (fun x => sign (f x)*(value x : ℤ))=(fun x => wa x-wb x) by funext x; exact hw x,
      difference_sum,aw,bw,zsum_eq,zsum_eq]
    exact sub_eq_zero.mpr (congrArg Nat.cast (show (a.map value).sum=(b.map value).sum from he))
  have ha := (shape_cyclic f (k+3)).1
  have hb := (shape_cyclic f (k+3)).2
  have hiz : (shape f (k+3)).different=false := checked_fibonacci_circle f k
    (ha ▸ indicator_variation l nodup i p) (hb ▸ indicator_variation l nodup j q) sumzero
  rw [shape_exact] at hiz
  change (l.any fun x => differs (f x))=false at hiz
  intro x
  change x∈a ↔ x∈b
  by_cases hl : x∈l
  · have hx := List.any_eq_false.mp hiz x hl
    by_cases hxA : x∈a <;> by_cases hxB : x∈b <;> simp_all [differs,f]
  · have hnA : x∉a := fun h => hl (List.mem_rotate.mp (List.take_subset _ _ h))
    have hnB : x∉b := fun h => hl (List.mem_rotate.mp (List.take_subset _ _ h))
    simp [hnA,hnB]

private theorem no_common_initial_set (x y : List ℕ) (hx : x≠[]) (hy : y≠[])
    (hn : (x++y).Nodup) (p q : ℕ) (hp : 0<p) (hq : 0<q) (hproper : p<(x++y).length) :
    ¬∀ z, z∈(x++y).take p ↔ z∈(y++x).take q := by
  intro same
  obtain ⟨u,xs,rfl⟩ := List.exists_cons_of_ne_nil hx
  obtain ⟨v,ys,rfl⟩ := List.exists_cons_of_ne_nil hy
  let x := u::xs
  let y := v::ys
  change ∀ z, z∈(x++y).take p ↔ z∈(y++x).take q at same
  have sep := (List.nodup_append.mp hn).2.2
  have hu : u∈(x++y).take p := by cases p with | zero => omega | succ p => simp [x]
  have hv : v∈(y++x).take q := by cases q with | zero => omega | succ q => simp [y]
  have hpy : x.length<p := by
    by_contra hle
    have h := (same v).mpr hv
    rw [List.take_append_of_le_length (by omega : p≤x.length)] at h
    have hxv := List.take_subset _ _ h
    exact sep v hxv v (by simp) rfl
  have hqx : y.length<q := by
    by_contra hle
    have h := (same u).mp hu
    rw [List.take_append_of_le_length (by omega : q≤y.length)] at h
    have hyu := List.take_subset _ _ h
    exact sep u (by simp) u hyu rfl
  have cover : x++y ⊆ (x++y).take p := by
    intro z hz
    rcases List.mem_append.mp hz with hz | hz
    · rw [List.take_append,List.take_of_length_le hpy.le]
      exact List.mem_append_left _ hz
    · apply (same z).mpr
      rw [List.take_append,List.take_of_length_le hqx.le]
      exact List.mem_append_left _ hz
  have hrest : (x++y).drop p≠[] := by
    intro hh
    have len := congrArg List.length hh
    simp only [List.length_drop,List.length_nil] at len
    change p<(x++y).length at hproper
    omega
  obtain ⟨z,hz⟩ := List.exists_mem_of_ne_nil _ hrest
  have hzall := List.drop_subset p (x++y) hz
  exact split_disjoint (x++y) hn p z (cover hzall) z hz rfl

/-- Distinct rotations of the explicit Fibonacci circle have disjoint sets
of proper, nonempty partial sums. The entries and prefix lengths here are
those of actual finite lists. -/
theorem cyclic_prefix_sums_distinct (k i j p q : ℕ) (hi : i<k+9) (hj : j<k+9)
    (hne : i≠j) (hp : 0<p) (hpn : p<k+9) (hq : 0<q) (hqn : q<k+9) :
    ((((layout (k+3)).order.rotate i).take p).map value).sum ≠
      ((((layout (k+3)).order.rotate j).take q).map value).sum := by
  let l := (layout (k+3)).order
  have perm : l.Perm (List.range (k+9)) := layout_perm (k+3)
  have len : l.length=k+9 := by simpa using perm.length_eq
  have nodup := perm.nodup_iff.mpr List.nodup_range
  have go (a b m t : ℕ) (hab : a<b) (hb : b<k+9) (hm : 0<m) (ht : 0<t) (hproper : m<k+9)
      (same : ∀ z, z∈(l.rotate a).take m ↔ z∈(l.rotate b).take t) : False := by
    let row := l.rotate a
    let d := b-a
    let x := row.take d
    let y := row.drop d
    have rowlen : row.length=k+9 := by simpa [row] using len
    have hd : d<row.length := by dsimp [d]; omega
    have dp : 0<d := by dsimp [d]; omega
    have xlen : x.length=d := List.length_take_of_le hd.le
    have ylen : y.length=row.length-d := List.length_drop
    have hx : x≠[] := fun he => by rw [he] at xlen; simp at xlen; omega
    have hy : y≠[] := fun he => by rw [he] at ylen; simp at ylen; omega
    have hrow : x++y=row := List.take_append_drop _ _
    have hrot : y++x=l.rotate b := by
      change row.drop d++row.take d=l.rotate b
      rw [← List.rotate_eq_drop_append_take hd.le]
      change (l.rotate a).rotate d=l.rotate b
      rw [List.rotate_rotate,show a+d=b by dsimp [d]; omega]
    apply no_common_initial_set x y hx hy (hrow ▸ List.nodup_rotate.mpr nodup) m t hm ht
      (by rw [hrow,rowlen]; exact hproper)
    simpa only [hrow,hrot,row] using same
  intro he
  have hs := prefix_sets_same k i j p q he
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact go i j p q hlt hj hp hq hpn hs
  · exact go j i q p hgt hi hq hp hqn (fun z => (hs z).symm)

/-- Rotating this order permutes exactly the first `k+9` distinct Fibonacci numbers. -/
theorem fibonacci_rotations_are_permutations (k i : ℕ) :
    (((layout (k+3)).order.rotate i).map value).Perm ((List.range (k+9)).map value) :=
  (((layout (k+3)).order.rotate_perm i).trans (layout_perm (k+3))).map value

#print axioms cyclic_prefix_sums_distinct
#print axioms fibonacci_rotations_are_permutations

end FibonacciBarrycade

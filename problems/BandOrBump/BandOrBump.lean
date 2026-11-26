import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Finset.Prod
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace BandOrBump

open Finset

/-- The number of ways to select j of s labelled cards of one rank, truncated at cap. -/
private def weight (s cap : ℕ) (j : ℤ) : ℚ :=
  if 0≤j ∧ j≤cap then s.choose j.toNat else 0

private theorem weight_nonneg (s cap : ℕ) (i : ℤ) : 0≤weight s cap i := by
  unfold weight
  split <;> positivity

private theorem wnat (s cap i : ℕ) : weight s cap i=if i≤cap then (s.choose i : ℚ) else 0 := by
  simp [weight]

private theorem woutside (s cap : ℕ) (i : ℤ) (h : i<0 ∨ (cap:ℤ)<i) : weight s cap i=0 :=
  if_neg (by omega)

private theorem choose_step (s i : ℕ) (hi : i≤s) :
    ((i:ℚ)+1)*(s.choose (i+1):ℚ)=((s:ℚ)-i)*(s.choose i:ℚ) := by
  rw [← Nat.cast_sub hi,mul_comm ((i:ℚ)+1),mul_comm _ (s.choose i : ℚ)]
  exact_mod_cast Nat.choose_succ_right_eq s i

private theorem weight_step (s a i : ℕ) (ha : a≤s) :
    ((i:ℚ)+1)*weight s a (i+1 : ℕ)=((s:ℚ)-i)*weight s a i-
    (if i=a then ((s:ℚ)-a)*weight s a i else 0) := by
  simp only [wnat]
  by_cases h : i<a
  · simp only [if_pos (show i+1≤a by omega),if_pos h.le,if_neg h.ne,sub_zero]
    exact choose_step _ _ (by omega)
  · by_cases e : i=a
    · subst i
      simp
    · simp [show ¬i≤a by omega,show ¬i+1≤a by omega,e]

/-- One-step mixed log-concavity, including the zero extension at both edges. -/
private theorem weight_cross (s a : ℕ) (ha : a≤s) (i j : ℤ) (hij : i≤j) :
    weight s a i * weight s a (j+1) ≤ weight s a (i+1) * weight s a j := by
  by_cases h : 0≤i ∧ j+1≤a
  · let l := i.toNat
    let r := j.toNat
    have li : (l:ℤ)=i := by dsimp [l];omega
    have rj : (r:ℤ)=j := by dsimp [r];omega
    rw [←li,←rj,← Nat.cast_one,← Nat.cast_add,← Nat.cast_add]
    simp only [wnat,if_pos (show l≤a by omega),if_pos (show r+1≤a by omega),
      if_pos (show l+1≤a by omega),if_pos (show r≤a by omega)]
    have eq (u : ℕ) (hu : u≤s) : (s.choose (u+1):ℚ)=
        (s.choose u:ℚ)*(((s:ℚ)-u)/(u+1)) := by
      have step := choose_step s u hu
      field_simp
      linarith
    have ord : (((s:ℚ)-r)/(r+1))≤((s:ℚ)-l)/(l+1) := by
      have le : (l:ℚ)≤r := by exact_mod_cast (by omega : l≤r)
      apply div_le_div₀ (sub_nonneg.2 (by exact_mod_cast (by omega : l≤s))) (by linarith)
        (by positivity) (by linarith)
    rw [eq r (by omega),eq l (by omega)]
    have nn : 0≤(s.choose l:ℚ)*(s.choose r:ℚ) := by positivity
    linarith only [mul_le_mul_of_nonneg_left ord nn]
  · have z : weight s a i=0 ∨ weight s a (j+1)=0 := by
      by_cases hi : i<0
      · exact Or.inl (woutside _ _ _ (Or.inl hi))
      · exact Or.inr (woutside _ _ _ (Or.inr (by omega)))
    rcases z with z|z <;> rw [z] <;>
      simpa using mul_nonneg (weight_nonneg s a (i+1)) (weight_nonneg s a j)

private def box (s a b k : ℕ) : ℚ :=
  ∑ p ∈ antidiagonal k, weight s a p.1*weight s b p.2

private theorem box_swap (s a b k : ℕ) : box s a b k=box s b a k := by
  unfold box
  rw [← Finset.Nat.sum_antidiagonal_swap (f:=fun p => weight s b p.1*weight s a p.2)]
  exact Finset.sum_congr rfl (fun _ _ => mul_comm ..)

private theorem box_nonneg (s a b k : ℕ) : 0≤box s a b k := by
  unfold box
  exact Finset.sum_nonneg (fun p _ => mul_nonneg (weight_nonneg s a p.1) (weight_nonneg s b p.2))

set_option maxHeartbeats 1200000 in
private theorem box_pos (s a b k : ℕ) (ha : a≤s) (hb : b≤s) (hk : k≤a+b) : 0<box s a b k := by
  let i := min a k
  let j := k-i
  have ii : i≤a := min_le_left a k 
  have ij : j≤b := by dsimp [j,i];omega
  have mem : (i,j)∈antidiagonal k := Finset.mem_antidiagonal.2 (by dsimp [j,i];omega)
  have p (v c : ℕ) (hvc : v≤c) (hcs : c≤s) : 0<weight s c v := by
    rw [wnat,if_pos hvc]
    exact_mod_cast Nat.choose_pos (hvc.trans hcs)
  unfold box
  exact (mul_pos (p i a ii ha) (p j b ij hb)).trans_le
    (Finset.single_le_sum (f:=fun t : ℕ×ℕ => weight s a t.1*weight s b t.2)
      (fun t _ => mul_nonneg (weight_nonneg s a t.1) (weight_nonneg s b t.2)) mem)

private theorem box_out (s a b k : ℕ) (hk : a+b<k) : box s a b k=0 := by
  apply Finset.sum_eq_zero
  intro p hp
  have e := Finset.mem_antidiagonal.1 hp
  by_cases h : a<p.1
  · rw [woutside s a _ (Or.inr (by exact_mod_cast h)),zero_mul]
  · rw [woutside s b _ (Or.inr (by omega)),mul_zero]

private theorem box_range (s a b k : ℕ) :
    box s a b k=∑ i ∈ range (a+1),weight s a i*weight s b ((k:ℤ)-i) := by
  rw [box,Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j : ℕ => weight s a i*weight s b j)]
  let f : ℕ→ℚ := fun i => weight s a i*weight s b ((k:ℤ)-i)
  trans ∑ i ∈ range (k+1), f i
  · apply Finset.sum_congr rfl
    intro i hi
    have e : i≤k := Nat.le_of_lt_succ (mem_range.1 hi)
    simp [f,Nat.cast_sub e]
  · change (∑ i ∈ range (k+1),f i)=∑ i ∈ range (a+1),f i
    by_cases h : k≤a
    · apply Finset.sum_subset (Finset.range_mono (by omega : k+1≤a+1)) ?_
      intro i _ hi
      have cut : (k:ℤ)-i<0 := by have hh : ¬i<k+1 := fun z => hi (mem_range.2 z);omega
      simp [f,woutside s b _ (Or.inl cut)]
    · apply (Finset.sum_subset (Finset.range_mono (by omega : a+1≤k+1)) ?_).symm
      intro i _ hi
      have cut : (a:ℤ)<i := by have hh : ¬i<a+1 := fun z => hi (mem_range.2 z);omega
      simp [f,woutside s a _ (Or.inr cut)]

private def leftEdge (s a b k : ℕ) : ℚ :=
  ((s:ℚ)-a)*weight s a a*weight s b ((k:ℤ)-a)

private theorem left_nonneg (s a b k : ℕ) (ha : a≤s) : 0≤leftEdge s a b k := by
  apply mul_nonneg _ (weight_nonneg ..)
  exact mul_nonneg (sub_nonneg.2 (by exact_mod_cast ha)) (weight_nonneg ..)

private theorem left_share (s a b k : ℕ) (ha : a≤s) (hb : b≤s) :
    leftEdge s a b k * box s a b (k+1) ≤ leftEdge s a b (k+1)*box s a b k := by
  rw [box_range,box_range,Finset.mul_sum,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  have ii : i≤a := Nat.le_of_lt_succ (mem_range.1 hi)
  have cross := weight_cross s b hb ((k:ℤ)-a) ((k:ℤ)-i) (by omega)
  unfold leftEdge
  push_cast
  rw [show (k:ℤ)+1-i=k-i+1 by omega,show (k:ℤ)+1-a=k-a+1 by omega]
  have nn : 0≤((s:ℚ)-a)*weight s a a*weight s a i :=
    mul_nonneg (mul_nonneg (sub_nonneg.2 (by exact_mod_cast ha)) (weight_nonneg ..))
      (weight_nonneg ..)
  linarith only [mul_le_mul_of_nonneg_left cross nn]

private theorem spike (s a b k : ℕ) :
    (∑ p ∈ antidiagonal k, if p.1=a then ((s:ℚ)-a)*weight s a p.1*weight s b p.2 else 0)=
    leftEdge s a b k := by
  by_cases hk : a≤k
  · let q : ℕ×ℕ := (a,k-a)
    have mq : q∈antidiagonal k := Finset.mem_antidiagonal.2 (by dsimp [q];omega)
    rw [Finset.sum_eq_single_of_mem q mq]
    · simp [q,leftEdge,Nat.cast_sub hk]
    · intro p hp h
      have ep := Finset.mem_antidiagonal.1 hp
      have d : p.1≠a := by
        intro i
        have j : p.2=k-a := by omega
        exact h (Prod.ext i j)
      simp [d]
  · have z := woutside s b ((k:ℤ)-a) (Or.inl (by omega))
    simp only [leftEdge,z,mul_zero]
    apply Finset.sum_eq_zero
    intro p hp
    have ep := Finset.mem_antidiagonal.1 hp
    simp [show p.1≠a by omega]

private theorem spike_right (s a b k : ℕ) :
    (∑ p ∈ antidiagonal k, if p.2=b then ((s:ℚ)-b)*weight s a p.1*weight s b p.2 else 0)=
    leftEdge s b a k := by
  rw [←spike s b a k,←Finset.Nat.sum_antidiagonal_swap
    (f:=fun p : ℕ×ℕ => if p.1=b then ((s:ℚ)-b)*weight s b p.1*weight s a p.2 else 0)]
  apply Finset.sum_congr rfl
  intro p _
  simp only [Prod.fst_swap,Prod.snd_swap]
  split <;> ring

private theorem derivative (f g : ℕ→ℚ) (k : ℕ) :
    ((k:ℚ)+1)*(∑ p∈antidiagonal (k+1),f p.1*g p.2) =
    ∑ p∈antidiagonal k, (((p.1:ℚ)+1)*f (p.1+1)*g p.2 + ((p.2:ℚ)+1)*f p.1*g (p.2+1)) := by
  rw [Finset.mul_sum]
  calc
    _ = ∑ p∈antidiagonal (k+1), ((p.1:ℚ)*f p.1*g p.2 + (p.2:ℚ)*f p.1*g p.2) := by
          apply Finset.sum_congr rfl
          intro p hp
          have e : (p.1:ℚ)+p.2=k+1 := by exact_mod_cast Finset.mem_antidiagonal.1 hp
          rw [←e]
          ring
    _ = _ := by
          rw [Finset.sum_add_distrib,Finset.Nat.sum_antidiagonal_succ,
            Finset.Nat.sum_antidiagonal_succ',Finset.sum_add_distrib]
          simp only [Nat.cast_zero,zero_mul,zero_add,Nat.cast_add,Nat.cast_one]

private def blocked (s a b k : ℕ) := leftEdge s a b k + leftEdge s b a k

private theorem box_step (s a b k : ℕ) (ha : a≤s) (hb : b≤s) :
    ((k:ℚ)+1)*box s a b (k+1)=((2*s:ℚ)-k)*box s a b k-blocked s a b k := by
  rw [box,derivative (fun i => weight s a i) (fun j => weight s b j)]
  unfold blocked
  rw [←spike s a b k,←spike_right s a b k,box,Finset.mul_sum,←Finset.sum_add_distrib,
    ←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  have e : (p.1:ℚ)+p.2=k := by exact_mod_cast Finset.mem_antidiagonal.1 hp
  rw [show ((p.2:ℚ)+1)*weight s a p.1*weight s b (p.2+1:ℕ) =
      (((p.2:ℚ)+1)*weight s b (p.2+1:ℕ))*weight s a p.1 by ring,
    weight_step s a p.1 ha,weight_step s b p.2 hb,←e]
  split_ifs <;> ring

private theorem blocked_share (s a b k : ℕ) (ha : a≤s) (hb : b≤s) :
    blocked s a b k * box s a b (k+1) ≤ blocked s a b (k+1) * box s a b k := by
  have x := left_share s a b k ha hb
  have y := left_share s b a k hb ha
  rw [box_swap s b a, box_swap s b a] at y
  unfold blocked
  linarith

private theorem blocked_nonneg (s a b k : ℕ) (ha : a≤s) (hb : b≤s) : 0≤blocked s a b k :=
  add_nonneg (left_nonneg s a b k ha) (left_nonneg s b a k hb)

/-- A rectangular constraint on the two other ranks, with a specified triggering card. -/
private def rect (s a b u T k : ℕ) : ℚ := box s a b k/(T.choose (u+k):ℚ)

private def firstRatio (u k : ℕ) : ℚ := 1+(u:ℚ)/(k+1)

private def secondRatio (s a b u T k : ℕ) : ℚ :=
  1-((T:ℚ)-u-2*s+blocked s a b k/box s a b k)/(T-u-k)

private theorem rect_nonneg (s a b u T k : ℕ) : 0≤rect s a b u T k :=
  div_nonneg (box_nonneg ..) (by positivity)

private theorem growth (s a b u T k : ℕ) (ha : a≤s) (hb : b≤s)
    (hC : 2*s+u≤T) (hk : k<a+b) :
    rect s a b u T (k+1)=rect s a b u T k *
      (firstRatio u k * secondRatio s a b u T k) := by
  have posk := box_pos s a b k ha hb (by omega)
  have rpos : 0 < (T:ℚ)-u-k := by
    have h : u+k<T := by omega
    exact_mod_cast (show (0:ℤ)<(T:ℤ)-u-k by omega)
  have cnt : 0<(T.choose (u+k):ℚ) := by exact_mod_cast Nat.choose_pos (by omega : u+k≤T)
  have one : 0<(k:ℚ)+1 := by positivity
  have two : 0<(u:ℚ)+k+1 := by positivity
  have bin : (T.choose (u+(k+1)):ℚ) = ((T:ℚ)-u-k)*(T.choose (u+k):ℚ)/(u+k+1) := by
    rw [← Nat.add_assoc]
    apply (eq_div_iff two.ne').2
    have z := choose_step T (u+k) (by omega)
    push_cast at z
    linarith only [z]
  have step : box s a b (k+1)=(((2*s:ℚ)-k)*box s a b k-blocked s a b k)/(k+1) := by
    apply (eq_div_iff one.ne').2
    linarith only [box_step s a b k ha hb]
  unfold rect firstRatio secondRatio
  rw [step,bin]
  field_simp [rpos.ne',posk.ne',one.ne',two.ne',cnt.ne']
  ring

private theorem first_drop (u k : ℕ) : firstRatio u (k+1)≤firstRatio u k := by
  unfold firstRatio
  push_cast
  apply add_le_add_left
  apply div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)

private theorem second_drop (s a b u T k : ℕ) (ha : a≤s) (hb : b≤s)
    (hC : 2*s+u≤T) (hk : k+2≤a+b) :
    secondRatio s a b u T (k+1)≤secondRatio s a b u T k := by
  have pk := box_pos s a b k ha hb (by omega)
  have pk1 := box_pos s a b (k+1) ha hb (by omega)
  have share : blocked s a b k/box s a b k ≤ blocked s a b (k+1)/box s a b (k+1) :=
    (div_le_div_iff₀ pk pk1).2 (blocked_share s a b k ha hb)
  have diff : 0≤(T:ℚ)-u-2*s := by exact_mod_cast (show 0≤(T:ℤ)-u-2*s by omega)
  have pos : 0<(T:ℚ)-u-(k+1) := by exact_mod_cast (show 0<(T:ℤ)-u-(k+1) by omega)
  unfold secondRatio
  push_cast
  apply sub_le_sub_left
  apply div_le_div₀ (add_nonneg diff (div_nonneg (blocked_nonneg s a b (k+1) ha hb) pk1.le))
    (by linarith only [share]) pos (by linarith)

private theorem second_nonneg (s a b u T k : ℕ) (ha : a≤s) (hb : b≤s)
    (hC : 2*s+u≤T) (hk : k<a+b) : 0≤secondRatio s a b u T k := by
  have den : 0<(T:ℚ)-u-k := by exact_mod_cast (show 0<(T:ℤ)-u-k by omega)
  have p := box_pos s a b k ha hb (by omega)
  have v := box_step s a b k ha hb
  have nn : 0≤((k:ℚ)+1)*box s a b (k+1) := mul_nonneg (by positivity) (box_nonneg ..)
  have hh : blocked s a b k/box s a b k≤(2*s:ℚ)-k := (div_le_iff₀ p).2 (by linarith)
  unfold secondRatio
  apply sub_nonneg.2
  apply (div_le_iff₀ den).2
  linarith

/-- The normalized rectangle masses are log-concave at every index, including their ends. -/
private theorem rect_lc (s a b u T k : ℕ) (ha : a≤s) (hb : b≤s) (hC : 2*s+u≤T) :
    rect s a b u T k*rect s a b u T (k+2) ≤ (rect s a b u T (k+1))^2 := by
  by_cases hk : k+2≤a+b
  · have f0 (j : ℕ) : 0≤firstRatio u j := by
      unfold firstRatio
      exact add_nonneg zero_le_one (div_nonneg (by positivity) (by positivity))
    have r := mul_le_mul (first_drop u k) (second_drop s a b u T k ha hb hC hk)
      (second_nonneg s a b u T (k+1) ha hb hC (by omega)) (f0 k)
    have m := mul_le_mul_of_nonneg_left r (mul_nonneg (rect_nonneg s a b u T k)
      (rect_nonneg s a b u T (k+1)))
    have g := congrArg (fun q : ℚ => q*rect s a b u T (k+1)) (growth s a b u T k ha hb hC (by omega))
    have g1 := congrArg (fun q : ℚ => rect s a b u T k*q) (growth s a b u T (k+1) ha hb hC (by omega))
    dsimp at g g1
    linarith only [m,g,g1]
  · have z : rect s a b u T (k+2)=0 := by simp [rect,box_out s a b (k+2) (by omega)]
    rw [z,mul_zero]
    exact sq_nonneg _

/-- Hand count for the two ranks other than the last drawn card's rank. -/
private def favorable (s l u k : ℕ) : ℚ :=
  ∑ p∈antidiagonal k, if p.1<l ∨ p.2<l then weight s u p.1*weight s u p.2 else 0

private theorem low_weight (s l u i : ℕ) (hl : 0<l) (hlu : l≤u) :
    weight s (l-1) i=if i<l then weight s u i else 0 := by
  by_cases h : i<l
  · simp [wnat,h,show i≤l-1 by omega,show i≤u by omega]
  · simp [wnat,h,show ¬i≤l-1 by omega]

private theorem favorable_nonneg (s l u k : ℕ) : 0≤favorable s l u k := by
  apply Finset.sum_nonneg
  intro p _
  split
  · exact mul_nonneg (weight_nonneg ..) (weight_nonneg ..)
  · rfl

private theorem full_bound (s l u k : ℕ) : favorable s l u k≤box s u u k := by
  apply Finset.sum_le_sum
  intro p _
  split
  · rfl
  · exact mul_nonneg (weight_nonneg ..) (weight_nonneg ..)

private theorem full_tight (s l u k : ℕ) (hk : k<2*l) : favorable s l u k=box s u u k := by
  apply Finset.sum_congr rfl
  intro p hp
  have e := Finset.mem_antidiagonal.1 hp
  simp only [if_pos (show p.1<l ∨ p.2<l by omega)]

private def twiceBox (s l u k : ℕ) := box s (l-1) u k+box s u (l-1) k

private theorem twice_eq (s l u k : ℕ) : twiceBox s l u k=2*box s (l-1) u k := by
  unfold twiceBox
  rw [box_swap s u (l-1)]
  ring

private theorem twice_bound (s l u k : ℕ) (hl : 0<l) (hlu : l≤u) :
    favorable s l u k≤twiceBox s l u k := by
  unfold favorable twiceBox box
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro p _
  rw [low_weight s l u p.1 hl hlu,low_weight s l u p.2 hl hlu]
  have nn := mul_nonneg (weight_nonneg s u p.1) (weight_nonneg s u p.2)
  split_ifs <;> first | linarith | omega

private theorem twice_tight (s l u k : ℕ) (hl : 0<l) (hlu : l≤u) (hk : 2*(l-1)<k) :
    favorable s l u k=twiceBox s l u k := by
  unfold favorable twiceBox box
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  have e := Finset.mem_antidiagonal.1 hp
  rw [low_weight s l u p.1 hl hlu,low_weight s l u p.2 hl hlu]
  split_ifs <;> first | omega | ring

private def sampleMass (s l u T k : ℕ) : ℚ := favorable s l u k/(T.choose (u+k):ℚ)

private theorem sample_lc (s l u T k : ℕ) (hl : 0<l) (hlu : l≤u) (hu : u≤s) (hC : 2*s+u≤T) :
    sampleMass s l u T k*sampleMass s l u T (k+2)≤(sampleMass s l u T (k+1))^2 := by
  have nn (j : ℕ) : 0≤sampleMass s l u T j := div_nonneg (favorable_nonneg ..) (by positivity)
  by_cases hk : k+1<2*l
  · have bound (j : ℕ) : sampleMass s l u T j ≤ rect s u u u T j :=
      div_le_div_of_nonneg_right (full_bound s l u j) (by positivity)
    have center : sampleMass s l u T (k+1)=rect s u u u T (k+1) := by
      simp only [sampleMass,rect,full_tight s l u _ hk]
    rw [center]
    exact (mul_le_mul (bound k) (bound (k+2)) (nn _) (rect_nonneg ..)).trans
      (rect_lc s u u u T k hu hu hC)
  · have bound (j : ℕ) : sampleMass s l u T j ≤ 2*rect s (l-1) u u T j := by
      rw [rect,sampleMass,←mul_div_assoc]
      apply div_le_div_of_nonneg_right _ (by positivity)
      rw [←twice_eq]
      exact twice_bound s l u j hl hlu
    have center : sampleMass s l u T (k+1)=2*rect s (l-1) u u T (k+1) := by
      rw [rect,sampleMass,←mul_div_assoc,twice_tight s l u _ hl hlu (by omega),twice_eq]
    rw [center]
    have m := mul_le_mul (bound k) (bound (k+2)) (nn _) (mul_nonneg (by norm_num) (rect_nonneg ..))
    have lc := rect_lc s (l-1) u u T k (by omega) hu hC
    linarith only [m,lc]

/-- Remaining labelled deck when a specific card of the first rank is fixed as the last draw. -/
abbrev Deck (s : ℕ) := Fin (s-1) ⊕ (Fin s ⊕ Fin s)

/-- All possible hands of `t` cards before the distinguished card, equally likely. -/
def priorHands (s t : ℕ) : Finset (Finset (Deck s)) := (univ : Finset (Deck s)).powersetCard t

/-- Hands that allow the distinguished next card to cause the first bump. -/
def bumpHands (s l u t : ℕ) : Finset (Finset (Deck s)) :=
  (priorHands s t).filter fun H => H.toLeft.card=u ∧ H.toRight.toLeft.card≤u ∧
    H.toRight.toRight.card≤u ∧ (H.toRight.toLeft.card<l ∨ H.toRight.toRight.card<l)

private abbrev Triple (s : ℕ) := Finset (Fin (s-1)) × (Finset (Fin s) × Finset (Fin s))

private def merge (s : ℕ) : Triple s ↪ Finset (Deck s) where
  toFun T := T.1.disjSum (T.2.1.disjSum T.2.2)
  inj' := by
    rintro ⟨a,b,c⟩ ⟨x,y,z⟩ h
    simpa only [Finset.disjSum_inj,Prod.mk.injEq] using h

private def fibre (s u i j : ℕ) : Finset (Finset (Deck s)) :=
  (((univ : Finset (Fin (s-1))).powersetCard u) ×ˢ
    (((univ : Finset (Fin s)).powersetCard i) ×ˢ ((univ : Finset (Fin s)).powersetCard j))).map (merge s)

private theorem fibre_mem (s u i j : ℕ) (H : Finset (Deck s)) :
    H∈fibre s u i j ↔ H.toLeft.card=u ∧ H.toRight.toLeft.card=i ∧ H.toRight.toRight.card=j := by
  constructor
  · rintro h
    obtain ⟨⟨x,y,z⟩,hm,e⟩ := Finset.mem_map.1 h
    subst H
    simpa [merge] using hm
  · rintro ⟨x,y,z⟩
    apply Finset.mem_map.2
    refine ⟨(H.toLeft,H.toRight.toLeft,H.toRight.toRight),?_,?_⟩
    · simp [x,y,z]
    · simp [merge,Finset.toLeft_disjSum_toRight]

private def allowed (l u : ℕ) (p : ℕ×ℕ) : Prop :=
  p.1≤u ∧ p.2≤u ∧ (p.1<l ∨ p.2<l)

private instance (l u : ℕ) (p : ℕ×ℕ) : Decidable (allowed l u p) :=
  inferInstanceAs (Decidable (_∧_∧(_∨_)))

private theorem hand_union (s l u k : ℕ) : bumpHands s l u (u+k)=
    ((antidiagonal k).filter (allowed l u)).biUnion (fun p => fibre s u p.1 p.2) := by
  ext H
  have cardeq : H.toLeft.card+(H.toRight.toLeft.card+H.toRight.toRight.card)=H.card := by
    rw [Finset.card_toLeft_add_card_toRight,Finset.card_toLeft_add_card_toRight]
  simp only [bumpHands,priorHands,mem_filter,mem_powersetCard,subset_univ,true_and,mem_biUnion,
    mem_antidiagonal,fibre_mem,allowed]
  constructor
  · rintro ⟨hn,h0,h1,h2,low⟩
    exact ⟨(H.toRight.toLeft.card,H.toRight.toRight.card),⟨by dsimp;omega,h1,h2,low⟩,h0,rfl,rfl⟩
  · rintro ⟨p,⟨sum,h1,h2,low⟩,h0,e1,e2⟩
    exact ⟨by omega,h0,by omega,by omega,by omega⟩

private theorem fibre_card (s u i j : ℕ) : (fibre s u i j).card =
    (s-1).choose u*(s.choose i*s.choose j) := by
  simp [fibre,Finset.card_powersetCard]

private theorem count_hands (s l u k : ℕ) : ((bumpHands s l u (u+k)).card:ℚ)=
    ((s-1).choose u:ℚ)*favorable s l u k := by
  rw [hand_union,Finset.card_biUnion]
  · unfold favorable
    rw [Finset.mul_sum]
    simp only [Nat.cast_sum,Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro p _
    rw [fibre_card,wnat,wnat]
    unfold allowed
    split_ifs <;> push_cast <;> first | omega | ring
  · intro p _ q _ ne
    apply Finset.disjoint_left.2
    intro H hp hq
    have a := (fibre_mem s u p.1 p.2 H).1 hp
    have b := (fibre_mem s u q.1 q.2 H).1 hq
    exact ne (Prod.ext (a.2.1.symm.trans b.2.1) (a.2.2.symm.trans b.2.2))

/-- Exact rational mass of winning by bump on draw `n`, conditioning on its last labelled card. -/
def bumpProbability (s l u n : ℕ) : ℚ :=
  if n=0 then 0 else ((bumpHands s l u (n-1)).card:ℚ)/(priorHands s (n-1)).card

private theorem probability_at (s l u k : ℕ) (hs : 0<s) :
    bumpProbability s l u (u+1+k)=((s-1).choose u:ℚ)*sampleMass s l u (3*s-1) k := by
  have e : u+1+k-1=u+k := by omega
  have t : s-1+(s+s)=3*s-1 := by omega
  simp only [bumpProbability,if_neg (show u+1+k≠0 by omega),e,count_hands,priorHands,
    Finset.card_powersetCard,Finset.card_univ,Fintype.card_sum,Fintype.card_fin,t,sampleMass,mul_div_assoc]

private theorem probability_before (s l u n : ℕ) (hn : n≤u) : bumpProbability s l u n=0 := by
  by_cases z : n=0
  · simp [bumpProbability,z]
  have e : bumpHands s l u (n-1)=∅ := by
    apply Finset.eq_empty_iff_forall_notMem.2
    intro H hh
    obtain ⟨hm,h0,_⟩ := Finset.mem_filter.1 hh
    have t := (Finset.mem_powersetCard.1 hm).2
    have r := H.card_toLeft_add_card_toRight
    omega
  simp [bumpProbability,e]

/-- Levin's Remark 2 for all three-rank decks and all draw numbers. -/
theorem three_ranks_bump_log_concave (s l u : ℕ) (hl : 0<l) (hlu : l≤u) (hu : u<s) (n : ℕ) :
    bumpProbability s l u n * bumpProbability s l u (n+2) ≤ (bumpProbability s l u (n+1))^2 := by
  by_cases early : n≤u
  · rw [probability_before s l u n early,zero_mul]
    exact sq_nonneg _
  · let k := n-(u+1)
    have shift : n=u+1+k := by dsimp [k];omega
    rw [shift,Nat.add_assoc (u+1) k 2,Nat.add_assoc (u+1) k 1]
    simp only [probability_at s l u _ (by omega)]
    have lc := sample_lc s l u (3*s-1) k hl hlu hu.le (by omega)
    have scaled := mul_le_mul_of_nonneg_left lc (sq_nonneg ((s-1).choose u:ℚ))
    linarith only [scaled]

/-- Rank names after fixing and renaming the last drawn card. -/
inductive Rank where | marked | left | right
  deriving DecidableEq

/-- The band in Levin's rule is attained when all three counts lie in the closed interval. -/
def inBand (l u : ℕ) (w : List Rank) : Prop :=
  l≤w.count .marked ∧ w.count .marked≤u ∧ l≤w.count .left ∧ w.count .left≤u ∧
    l≤w.count .right ∧ w.count .right≤u

/-- The monotone event that some rank has exceeded its upper limit. -/
def hasBump (u : ℕ) (w : List Rank) : Prop :=
  u<w.count .marked ∨ u<w.count .left ∨ u<w.count .right

/-- The final card causes a bump and all prefixes before it have avoided both stopping rules. -/
def firstBump (l u : ℕ) (w : List Rank) : Prop :=
  hasBump u (w++[.marked]) ∧ ∀ v, v.IsPrefix w → ¬inBand l u v ∧ ¬hasBump u v

/-- The stopping event depends only on the prior hand, irrespective of its order. -/
theorem first_bump_iff_counts (l u : ℕ) (hlu : l≤u) (w : List Rank) : firstBump l u w ↔
    w.count .marked=u ∧ w.count .left≤u ∧ w.count .right≤u ∧
      (w.count .left<l ∨ w.count .right<l) := by
  have app : hasBump u (w++[.marked]) ↔
      u<w.count .marked+1 ∨ u<w.count .left ∨ u<w.count .right := by
    simp [hasBump,List.count_append]
  constructor
  · rintro ⟨hb,quiet⟩
    obtain ⟨noband,nobump⟩ := quiet w ⟨[],by simp⟩
    unfold inBand at noband
    unfold hasBump at nobump
    have e := app.1 hb
    omega
  · rintro ⟨hm,hx,hy,low⟩
    refine ⟨app.2 (Or.inl (by omega)),?_⟩
    rintro v ⟨rest,e⟩
    have le (r : Rank) : v.count r≤w.count r := by rw [←e,List.count_append];omega
    have em := le .marked
    have ex := le .left
    have ey := le .right
    unfold inBand hasBump
    omega

/-- Every ordering of a labelled prior hand gives exactly the stopping predicate used to count it. -/
theorem bump_hand_iff_first_bump (s l u t : ℕ) (hlu : l≤u) (H : Finset (Deck s))
    (hH : H∈priorHands s t) (w : List Rank) (hm : w.count .marked=H.toLeft.card)
    (hx : w.count .left=H.toRight.toLeft.card) (hy : w.count .right=H.toRight.toRight.card) :
    H∈bumpHands s l u t ↔ firstBump l u w := by
  simp [bumpHands,hH,first_bump_iff_counts l u hlu,hm,hx,hy]

private theorem fav_pos (s l u k : ℕ) (hl : 0<l) (hlu : l≤u) (hu : u≤s) (hk : k≤u+l-1) :
    0<favorable s l u k := by
  by_cases h : k<2*l
  · rw [full_tight s l u k h]
    exact box_pos s u u k hu hu (by omega)
  · rw [twice_tight s l u k hl hlu (by omega),twice_eq]
    exact mul_pos (by norm_num) (box_pos s (l-1) u k (by omega) hu (by omega))

private theorem fav_out (s l u k : ℕ) (hl : 0<l) (hlu : l≤u) (hk : u+l-1<k) :
    favorable s l u k=0 := by
  rw [twice_tight s l u k hl hlu (by omega),twice_eq,box_out s (l-1) u k (by omega),mul_zero]

/-- Exact support of the three-rank bump event. -/
theorem three_ranks_support (s l u : ℕ) (hl : 0<l) (hlu : l≤u) (hu : u<s) (n : ℕ) :
    0<bumpProbability s l u n ↔ u+1≤n ∧ n≤2*u+l := by
  by_cases early : n≤u
  · rw [probability_before s l u n early]
    simp only [lt_self_iff_false,false_iff]
    omega
  let k := n-(u+1)
  have shift : n=u+1+k := by dsimp [k];omega
  rw [shift,probability_at s l u k (by omega)]
  unfold sampleMass
  by_cases hk : k≤u+l-1
  · have a : 0<((s-1).choose u:ℚ) := by exact_mod_cast Nat.choose_pos (by omega : u≤s-1)
    have b : 0<((3*s-1).choose (u+k):ℚ) := by exact_mod_cast Nat.choose_pos (by omega : u+k≤3*s-1)
    exact iff_of_true (mul_pos a (div_pos (fav_pos s l u k hl hlu hu.le hk) b)) (by omega)
  · rw [fav_out s l u k hl hlu (by omega),zero_div,mul_zero]
    simp only [lt_self_iff_false,false_iff]
    omega

#print axioms three_ranks_bump_log_concave
#print axioms three_ranks_support
#print axioms bump_hand_iff_first_bump
end BandOrBump

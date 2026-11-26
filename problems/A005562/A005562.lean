import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.List.Nodup
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Ring

/-! The height-uniform version of Mathar's square-lattice walk recurrence.
The sequence is given by Guy's binomial formula (J. Integer Sequences 3,
article 00.1.6, section 4, after Figure 5), reproduced in OEIS A052174.
The final theorem starts with actual, duplicate-free lists of admissible
compass words and has a natural-number conclusion. Intermediate calculations
use rational coefficients to divide by positive factorials. -/

namespace QuadrantWalks

private abbrev bin (n k : ℕ) : ℚ := n.choose k

/-- The binomial coefficient at index k−1, with index −1 assigned zero. -/
def previous (n : ℕ) : ℕ → ℚ
  | 0 => 0
  | k + 1 => bin n k

def evenCount (y k : ℕ) : ℚ :=
  let n := y + 2*k
  bin (n+1) k * (bin n k - previous n k)

def oddCount (y k : ℕ) : ℚ :=
  let n := y + 2*k+1
  bin (n+1) k * bin n (k+1) - bin (n+1) (k+1) * previous n k

/-- Guy's closed formula for the number of n-step quadrant walks ending
at height y (the final horizontal coordinate is arbitrary). -/
def count (n y : ℕ) : ℚ :=
  if n < y then 0 else if (n-y)%2 = 0 then evenCount y ((n-y)/2)
  else oddCount y ((n-y)/2)

private def fac (n : ℕ) : ℚ := n.factorial

private theorem fac_pos (n : ℕ) : 0 < fac n := by
  unfold fac
  exact_mod_cast Nat.factorial_pos n

private theorem fac_succ (n : ℕ) : fac (n+1) = (n+1 : ℚ) * fac n := by
  unfold fac
  rw [Nat.factorial_succ]
  push_cast
  rfl

private theorem choose_factorials (n k d : ℕ) (h : n = k+d) :
    bin n k = fac n / (fac k * fac d) := by
  apply (eq_div_iff (mul_ne_zero (fac_pos k).ne' (fac_pos d).ne')).2
  have hn : k ≤ n := by omega
  have eq := Nat.choose_mul_factorial_mul_factorial hn
  rw [show n-k = d by omega, mul_assoc] at eq
  unfold bin fac
  exact_mod_cast eq

private theorem previous_factorials (n k d : ℕ) (h : n = k+d) :
    previous n k = k * fac n / (fac k * fac (d+1)) := by
  cases k with
  | zero => simp [previous]
  | succ k =>
    change bin n k = _
    rw [choose_factorials n k (d+1) (by omega), fac_succ k]
    push_cast
    field_simp (disch := positivity)

private def evenProduct (y k : ℕ) : ℚ :=
  (y+1) * fac (y+2*k+1) * fac (y+2*k) / (fac k ^ 2 * fac (y+k+1) ^ 2)

private def oddProduct (y k : ℕ) : ℚ :=
  (y+1) * fac (y+2*k+2) * fac (y+2*k+1) /
    (fac k * fac (k+1) * fac (y+k+2) * fac (y+k+1))

private theorem even_product (y k : ℕ) : evenCount y k = evenProduct y k := by
  simp only [evenCount, evenProduct]
  rw [choose_factorials _ _ (y+k+1) (by omega), choose_factorials _ _ (y+k) (by omega),
    previous_factorials _ _ (y+k) (by omega), fac_succ (y+k)]
  push_cast
  field_simp (disch := positivity)
  ring

private theorem odd_product (y k : ℕ) : oddCount y k = oddProduct y k := by
  simp only [oddCount, oddProduct]
  rw [choose_factorials _ k (y+k+2) (by omega), choose_factorials _ (k+1) (y+k) (by omega),
    choose_factorials _ (k+1) (y+k+1) (by omega), previous_factorials _ k (y+k+1) (by omega)]
  rw [show y+k+2=y+k+1+1 by omega, fac_succ (y+k+1), fac_succ (y+k), fac_succ k]
  push_cast
  field_simp (disch := positivity)
  ring

private theorem even_to_odd (y k : ℕ) :
    oddCount y k = (((y : ℚ)+2*k+2)*(y+2*k+1))/((k+1)*(y+k+2)) * evenCount y k := by
  rw [even_product, odd_product]
  simp only [evenProduct, oddProduct]
  rw [show y+2*k+2=y+2*k+1+1 by omega, fac_succ (y+2*k+1),
    show y+k+2=y+k+1+1 by omega, fac_succ (y+k+1), fac_succ k, fac_succ (y+2*k)]
  push_cast
  field_simp (disch := positivity)
  ring

private theorem odd_to_even (y k : ℕ) :
    evenCount y (k+1) = (((y : ℚ)+2*k+3)*(y+2*k+2))/((k+1)*(y+k+2)) * oddCount y k := by
  rw [even_product, odd_product]
  simp only [evenProduct, oddProduct]
  rw [show y+2*(k+1)+1 = y+2*k+2+1 by omega, show y+2*(k+1)=y+2*k+2 by omega,
    show y+(k+1)+1=y+k+2 by omega, fac_succ (y+2*k+2),
    show y+2*k+2=y+2*k+1+1 by omega, fac_succ (y+2*k+1),
    show y+k+2=y+k+1+1 by omega, fac_succ (y+k+1), fac_succ k]
  push_cast
  field_simp (disch := positivity)
  ring

private theorem count_even (y k : ℕ) : count (y+2*k) y = evenCount y k := by
  unfold count
  rw [if_neg (by omega), if_pos (by omega), show (y+2*k-y)/2=k by omega]

private theorem count_odd (y k : ℕ) : count (y+2*k+1) y = oddCount y k := by
  unfold count
  rw [if_neg (by omega), if_neg (by omega), show (y+2*k+1-y)/2=k by omega]

private def recurrenceAt (n y a b c : ℚ) : Prop :=
  (n-y+1)*(n-y)*(2*n+1)*(n+y+3)*(n+y+2)*a =
    4*n*(n+1)*(2*n^2+4*n+2*y^2+4*y+3)*b + 16*n^2*(n-1)*(2*n+3)*(n+1)*c

private theorem recurrence_even (y k : ℕ) :
    recurrenceAt ((y : ℚ)+2*k+2) y (evenCount y (k+1)) (oddCount y k) (evenCount y k) := by
  rw [odd_to_even, even_to_odd]
  unfold recurrenceAt
  field_simp (disch := positivity)
  ring

private theorem recurrence_odd (y k : ℕ) :
    recurrenceAt ((y : ℚ)+2*k+3) y (oddCount y (k+1)) (evenCount y (k+1)) (oddCount y k) := by
  rw [even_to_odd y (k+1), odd_to_even]
  push_cast
  unfold recurrenceAt
  field_simp (disch := positivity)
  ring

/-- The same polynomial recurrence holds at every terminal height. -/
theorem mathar_recurrence (n y : ℕ) (h : y+2 ≤ n) :
    ((n : ℚ)-y+1)*(n-y)*(2*n+1)*(n+y+3)*(n+y+2)*count n y =
      4*n*(n+1)*(2*n^2+4*n+2*y^2+4*y+3)*count (n-1) y +
      16*n^2*(n-1)*(2*n+3)*(n+1)*count (n-2) y := by
  let k := (n-y-2)/2
  by_cases even : (n-y-2)%2 = 0
  · have hn : n = y+2*k+2 := by dsimp [k]; omega
    rw [show n = y+2*(k+1) by omega, count_even,
      show y+2*(k+1)-1 = y+2*k+1 by omega, count_odd,
      show y+2*(k+1)-2 = y+2*k by omega, count_even]
    have hr := recurrence_even y k
    unfold recurrenceAt at hr
    push_cast
    convert hr using 1 <;> ring
  · have hn : n = y+2*k+3 := by dsimp [k]; omega
    rw [show n = y+2*(k+1)+1 by omega, count_odd,
      show y+2*(k+1)+1-1 = y+2*(k+1) by omega, count_even,
      show y+2*(k+1)+1-2 = y+2*k+1 by omega, count_odd]
    have hr := recurrence_odd y k
    unfold recurrenceAt at hr
    push_cast
    convert hr using 1 <;> ring

#print axioms mathar_recurrence

/-! The remaining definitions start from actual lists of compass steps. -/

private def ibin (n : ℕ) : ℤ → ℚ
  | .ofNat k => bin n k
  | .negSucc _ => 0

private theorem ibin_neg (n : ℕ) (i : ℤ) (h : i < 0) : ibin n i = 0 := by
  cases i with
  | ofNat k => simp at h; omega
  | negSucc k => rfl

private theorem ibin_succ (n : ℕ) (i : ℤ) :
    ibin (n+1) i = ibin n i + ibin n (i-1) := by
  cases i with
  | negSucc i =>
    rw [ibin_neg _ _ (by omega), ibin_neg n _ (by omega), ibin_neg n _ (by omega), add_zero]
  | ofNat i =>
    cases i with
    | zero =>
      change ((n+1).choose 0 : ℚ) = (n.choose 0 : ℚ) + ibin n (-1)
      rw [ibin_neg _ _ (by decide)]
      simp
    | succ i =>
      rw [show (Int.ofNat (i+1))-1 = Int.ofNat i by simp]
      change ((n+1).choose (i+1) : ℚ) = (n.choose (i+1) : ℚ) + (n.choose i : ℚ)
      rw [Nat.choose_succ_succ, Nat.cast_add, add_comm]

private theorem ibin_zero (i : ℤ) : ibin 0 i = if i=0 then 1 else 0 := by
  cases i with
  | ofNat i =>
    cases i with
    | zero => rfl
    | succ i => simp [ibin, bin]; omega
  | negSucc i => simp [ibin]

private def line (n : ℕ) (t : ℤ) : ℚ :=
  if (n-t)%2=0 then ibin n ((n-t)/2) else 0

private theorem line_zero (t : ℤ) : line 0 t = if t=0 then 1 else 0 := by
  simp only [line, Nat.cast_zero, ibin_zero]
  split_ifs <;> first | rfl | omega

private theorem line_succ (n : ℕ) (t : ℤ) :
    line (n+1) t = line n (t-1) + line n (t+1) := by
  simp only [line, Nat.cast_add, Nat.cast_one]
  by_cases h : ((n:ℤ)+1-t)%2=0
  · rw [if_pos h, if_pos (by omega), if_pos (by omega), ibin_succ,
      show ((n:ℤ)-(t-1))/2=(n+1-t)/2 by omega,
      show ((n:ℤ)-(t+1))/2=(n+1-t)/2-1 by omega]
  · rw [if_neg h, if_neg (by omega), if_neg (by omega), add_zero]

private theorem line_neg (n : ℕ) (t : ℤ) : line n (-t) = line n t := by
  induction n generalizing t with
  | zero => simp [line_zero]
  | succ n ih =>
    rw [line_succ, line_succ, show -t-1= -(t+1) by omega,
      show -t+1= -(t-1) by omega, ih, ih, add_comm]

private theorem line_past (n : ℕ) (t : ℤ) (h : n < t) : line n t = 0 := by
  unfold line
  split_ifs with hp
  · exact ibin_neg _ _ (by omega)
  · rfl

private def free (n : ℕ) (x y : ℤ) : ℚ := line n (x+y) * line n (x-y)

private theorem free_succ (n : ℕ) (x y : ℤ) :
    free (n+1) x y = free n (x-1) y + free n (x+1) y +
      free n x (y-1) + free n x (y+1) := by
  simp only [free, line_succ]
  rw [show x-1+y=x+y-1 by omega, show x-1-y=x-y-1 by omega,
    show x+1+y=x+y+1 by omega, show x+1-y=x-y+1 by omega,
    show x+(y-1)=x+y-1 by omega, show x-(y-1)=x-y+1 by omega,
    show x+(y+1)=x+y+1 by omega, show x-(y+1)=x-y-1 by omega]
  ring

private theorem free_neg_x (n : ℕ) (x y : ℤ) : free n (-x) y = free n x y := by
  unfold free
  rw [show -x+y= -(x-y) by omega, show -x-y= -(x+y) by omega, line_neg, line_neg, mul_comm]

private theorem free_neg_y (n : ℕ) (x y : ℤ) : free n x (-y) = free n x y := by
  unfold free
  rw [show x+-y=x-y by omega, show x- -y=x+y by omega, mul_comm]

private def reflected (n : ℕ) (x y : ℤ) : ℚ :=
  free n x y - free n (x+2) y - free n x (y+2) + free n (x+2) (y+2)

private theorem reflected_succ (n : ℕ) (x y : ℤ) :
    reflected (n+1) x y = reflected n (x-1) y + reflected n (x+1) y +
      reflected n x (y-1) + reflected n x (y+1) := by
  simp only [reflected, free_succ]
  rw [show x-1+2=x+2-1 by omega, show x+1+2=x+2+1 by omega,
    show y-1+2=y+2-1 by omega, show y+1+2=y+2+1 by omega]
  ring

private theorem reflected_left (n : ℕ) (y : ℤ) : reflected n (-1) y = 0 := by
  simp only [reflected, free_neg_x, show (-1:ℤ)+2=1 by decide]
  ring

private theorem reflected_bottom (n : ℕ) (x : ℤ) : reflected n x (-1) = 0 := by
  simp only [reflected, free_neg_y, show (-1:ℤ)+2=1 by decide]
  ring

private theorem free_zero (x y : ℤ) :
    free 0 x y = if x=0 ∧ y=0 then 1 else 0 := by
  simp only [free, line_zero]
  split_ifs <;> norm_num <;> omega

/-- Every word consists of unit steps parallel to a coordinate axis. -/
inductive Step where
  | east | west | north | south
  deriving DecidableEq, Repr

/-- Lists of all legal words, with the last step stored first. The initial
point is the origin. Every visited point lies in the closed first quadrant. -/
def paths : ℕ → ℤ → ℤ → List (List Step)
  | 0, x, y => if x=0 ∧ y=0 then [[]] else []
  | n+1, x, y =>
    if 0 ≤ x ∧ 0 ≤ y then
      (paths n (x-1) y).map (Step.east :: ·) ++ (paths n (x+1) y).map (Step.west :: ·) ++
      (paths n x (y-1)).map (Step.north :: ·) ++ (paths n x (y+1)).map (Step.south :: ·)
    else []

private theorem tag_nodup (s : Step) (l : List (List Step)) (h : l.Nodup) :
    (l.map (s :: ·)).Nodup :=
  List.Nodup.map (fun _ _ e => (List.cons.inj e).2) h

private theorem tag_disjoint (s t : Step) (h : s ≠ t) (l m : List (List Step)) :
    (l.map (s :: ·)).Disjoint (m.map (t :: ·)) := by
  intro w hs ht
  obtain ⟨u, _, hu⟩ := List.mem_map.mp hs
  obtain ⟨v, _, hv⟩ := List.mem_map.mp ht
  exact h (List.cons.inj (hu.trans hv.symm)).1

/-- The enumeration counts each admissible word at most once. -/
theorem paths_nodup (n : ℕ) (x y : ℤ) : (paths n x y).Nodup := by
  induction n generalizing x y with
  | zero => simp only [paths]; split <;> simp
  | succ n ih =>
    simp only [paths]
    split
    · simp only [List.nodup_append', List.disjoint_append_left]
      repeat' apply And.intro
      all_goals first | exact tag_nodup _ _ (ih _ _) | exact tag_disjoint _ _ (by decide) _ _
    · simp

private theorem paths_left (n : ℕ) (y : ℤ) : paths n (-1) y = [] := by
  cases n <;> simp [paths]

private theorem paths_bottom (n : ℕ) (x : ℤ) : paths n x (-1) = [] := by
  cases n <;> simp [paths]

private theorem paths_reflected (n : ℕ) (x y : ℤ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    ((paths n x y).length : ℚ) = reflected n x y := by
  induction n generalizing x y with
  | zero =>
    simp only [paths, reflected, free_zero]
    rw [if_neg (show ¬ (x+2=0 ∧ y=0) by omega), if_neg (show ¬ (x=0 ∧ y+2=0) by omega),
      if_neg (show ¬ (x+2=0 ∧ y+2=0) by omega)]
    split_ifs <;> simp
  | succ n ih =>
    simp only [paths, if_pos (And.intro hx hy), List.length_append, List.length_map,
      Nat.cast_add, reflected_succ]
    rw [ih (x+1) y (by omega) hy, ih x (y+1) hx (by omega)]
    have hleft : ((paths n (x-1) y).length : ℚ) = reflected n (x-1) y := by
      by_cases h : x=0
      · subst x
        simp [paths_left, reflected_left]
      · exact ih _ _ (by omega) hy
    have hbottom : ((paths n x (y-1)).length : ℚ) = reflected n x (y-1) := by
      by_cases h : y=0
      · subst y
        simp [paths_bottom, reflected_bottom]
      · exact ih _ _ hx (by omega)
    rw [hleft, hbottom]

/-- Count all the quadrant paths ending at height y, summing over possible
horizontal endpoints. A path of n unit steps can have first coordinate at most n. -/
def walkCount (n y : ℕ) : ℕ := ∑ x ∈ Finset.range (n+1), (paths n x y).length

private theorem telescope (f : ℕ → ℚ) (m : ℕ) :
    ∑ x ∈ Finset.range m, (f x-f (x+2)) = f 0+f 1-f m-f (m+1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    ring

private theorem free_past (n : ℕ) (x y : ℤ) (hx : n < x) (hy : 0 ≤ y) :
    free n x y = 0 := by
  unfold free
  rw [line_past _ _ (by omega), zero_mul]

private theorem walk_boundary (n y : ℕ) :
    (walkCount n y : ℚ) = free n 0 y + free n 1 y - free n 0 (y+2) - free n 1 (y+2) := by
  let f (x : ℕ) := free n x y - free n x (y+2)
  have he (x : ℕ) : ((paths n x y).length : ℚ) = f x - f (x+2) := by
    rw [paths_reflected n _ _ (by omega) (by omega)]
    simp only [reflected, f, Nat.cast_add, Nat.cast_ofNat]
    ring
  simp only [walkCount, Nat.cast_sum, he, telescope, f, Nat.cast_zero, Nat.cast_one]
  rw [free_past n (n+1 : ℕ) y (by omega) (by omega),
    free_past n (n+1 : ℕ) (y+2) (by omega) (by omega),
    free_past n (n+1+1 : ℕ) y (by omega) (by omega),
    free_past n (n+1+1 : ℕ) (y+2) (by omega) (by omega)]
  ring

private theorem walk_line (n y : ℕ) :
    (walkCount n y : ℚ) = (line n y)^2 + line n (y+1)*line n (y-1) -
      (line n (y+2))^2 - line n (y+3)*line n (y+1) := by
  rw [walk_boundary]
  simp only [free, zero_add, zero_sub, line_neg]
  rw [show (1:ℤ)+y=y+1 by omega, show (1:ℤ)-y= -(y-1) by omega, line_neg,
    show (1:ℤ)+(y+2)=y+3 by omega, show (1:ℤ)-(y+2)= -(y+1) by omega, line_neg]
  ring

private theorem centered (n : ℕ) (t i : ℤ) (h : (n:ℤ)-t=2*i) :
    line n t = ibin n i := by
  rw [line, h, if_pos (by omega), show 2*i/2=i by omega]

private theorem opposite (n : ℕ) (t : ℤ) (h : ((n:ℤ)-t)%2 ≠ 0) : line n t = 0 :=
  if_neg h

private theorem ibin_nat (n k : ℕ) : ibin n (k:ℤ) = bin n k := rfl

private theorem ibin_previous (n k : ℕ) : ibin n ((k:ℤ)-1) = previous n k := by
  cases k with
  | zero => rfl
  | succ k => rw [show ((k+1:ℕ):ℤ)-1=k by omega]; rfl

private theorem bin_step (n k : ℕ) : bin (n+1) k = bin n k + previous n k := by
  simpa only [ibin_nat, ibin_previous] using ibin_succ n (k:ℤ)

private theorem walk_even (y k : ℕ) : (walkCount (y+2*k) y : ℚ) = evenCount y k := by
  let n := y+2*k
  change (walkCount n y : ℚ) = bin (n+1) k * (bin n k - previous n k)
  have hn : (n:ℤ) = (y:ℤ)+2*k := by simp [n]
  rw [walk_line, opposite n (y+1) (by omega), centered n y k (by omega),
    centered n (y+2) ((k:ℤ)-1) (by omega), ibin_nat, ibin_previous, bin_step]
  ring

private theorem walk_odd (y k : ℕ) : (walkCount (y+2*k+1) y : ℚ) = oddCount y k := by
  let n := y+2*k+1
  change (walkCount n y : ℚ) = bin (n+1) k * bin n (k+1) - bin (n+1) (k+1) * previous n k
  have hn : (n:ℤ) = (y:ℤ)+2*k+1 := by simp [n]
  rw [walk_line, opposite n y (by omega), opposite n (y+2) (by omega),
    centered n (y+1) k (by omega), centered n (y-1) ((k+1:ℕ):ℤ) (by omega),
    centered n (y+3) ((k:ℤ)-1) (by omega), ibin_nat, ibin_nat, ibin_previous,
    bin_step n k, bin_step n (k+1)]
  change _ = (bin n k + previous n k)*bin n (k+1) - (bin n (k+1) + bin n k)*previous n k
  ring

/-- Starting with the actual legal step words yields Guy's binomial enumeration. -/
theorem walk_eq_count (n y : ℕ) : (walkCount n y : ℚ) = count n y := by
  by_cases h : n < y
  · rw [walk_line, count, if_pos h, line_past n y (by omega),
      line_past n (y+1) (by omega), line_past n (y+2) (by omega)]
    ring
  · let k := (n-y)/2
    by_cases he : (n-y)%2 = 0
    · have hn : n = y+2*k := by dsimp [k]; omega
      rw [hn, count_even, walk_even]
    · have hn : n = y+2*k+1 := by dsimp [k]; omega
      rw [hn, count_odd, walk_odd]

/-- The endpoint sum includes every possible nonnegative horizontal coordinate. -/
theorem no_paths_past (n x y : ℕ) (h : n < x) : (paths n x y).length = 0 := by
  have he := paths_reflected n x y (by omega) (by omega)
  rw [reflected, free_past n x y (by omega) (by omega),
    free_past n (x+2) y (by omega) (by omega), free_past n x (y+2) (by omega) (by omega),
    free_past n (x+2) (y+2) (by omega) (by omega)] at he
  norm_num at he
  simp [he]

/-- Mathar's recurrence for actual finite compass walks in the closed first quadrant. -/
theorem quadrant_walk_recurrence (n y : ℕ) (h : y+2 ≤ n) :
    (n-y+1)*(n-y)*(2*n+1)*(n+y+3)*(n+y+2)*walkCount n y =
      4*n*(n+1)*(2*n^2+4*n+2*y^2+4*y+3)*walkCount (n-1) y +
      16*n^2*(n-1)*(2*n+3)*(n+1)*walkCount (n-2) y := by
  have hr := mathar_recurrence n y h
  rw [← walk_eq_count, ← walk_eq_count, ← walk_eq_count] at hr
  apply (Nat.cast_inj (R := ℚ)).mp
  push_cast [Nat.cast_sub (show y ≤ n by omega), Nat.cast_sub (show 1 ≤ n by omega)]
  exact hr

#print axioms walk_eq_count
#print axioms quadrant_walk_recurrence

end QuadrantWalks

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Data.List.Nodup
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.FieldSimp

namespace ThreeSandpile

/-- Coefficients of (1+X+X²)^n, extended by zero off their support. -/
def tri : ℕ → ℤ → ℚ
  | 0, i => if i=0 then 1 else 0
  | n+1, i => tri n i + tri n (i-1) + tri n (i-2)

private theorem tri_nonneg (n : ℕ) (i : ℤ) : 0 ≤ tri n i := by
  induction n generalizing i with
  | zero => simp only [tri]; split <;> decide
  | succ n ih => exact add_nonneg (add_nonneg (ih _) (ih _)) (ih _)

private theorem tri_pos (n : ℕ) (i : ℤ) (h : 0 ≤ i) (hi : i ≤ 2*n) : 0 < tri n i := by
  induction n generalizing i with
  | zero =>
    have eq : i=0 := by omega
    simp [tri,eq]
  | succ n ih =>
    rw [tri]
    have a := tri_nonneg n i
    have b := tri_nonneg n (i-1)
    have c := tri_nonneg n (i-2)
    by_cases p : i ≤ 2*n
    · linarith [ih i h p]
    · by_cases q : i-1 ≤ 2*n
      · linarith [ih (i-1) (by omega) q]
      · linarith [ih (i-2) (by omega) (by omega)]

private theorem tri_out (n : ℕ) (k : ℤ) (h : k<0 ∨ 2*n<k) : tri n k=0 := by
  induction n generalizing k with
  | zero => simp [tri,show k≠0 by omega]
  | succ n ih => rw [tri, ih k (by omega), ih (k-1) (by omega), ih (k-2) (by omega)]; norm_num

private theorem tri_symm (n : ℕ) (k : ℤ) : tri n (2*n-k) = tri n k := by
  induction n generalizing k with
  | zero => simp [tri]
  | succ n ih =>
    simp only [tri, Nat.cast_add, Nat.cast_one]
    rw [show 2*((n:ℤ)+1)-k=2*n-(k-2) by omega,
      show 2*(n:ℤ)-(k-2)-1=2*n-(k-1) by omega,
      show 2*(n:ℤ)-(k-2)-2=2*n-k by omega, ih, ih, ih]
    ring

private def Cross (f : ℤ → ℚ) : Prop := ∀ i j, i ≤ j → f (i-1)*f (j+1) ≤ f i*f j

private theorem slide {f : ℤ → ℚ} (h : Cross f) :
    Cross (fun i => f i+f (i-1)+f (i-2)) := by
  intro i j ij
  dsimp
  have terms (i j : ℤ) (hij : i ≤ j+1) : f (i-1)*f (j+1) ≤ f i*f j := by
    by_cases he : i ≤ j
    · exact h _ _ he
    · have e : i=j+1 := by omega
      rw [e,show j+1-1=j by omega,mul_comm]
  have a := terms i j (by omega)
  have b := terms i (j-1) (by omega)
  have d := terms (i-1) j (by omega)
  have f' := terms (i-1) (j-2) (by omega)
  have g := terms (i-2) j (by omega)
  have m := terms (i-2) (j-1) (by omega)
  have z := terms (i-2) (j-2) (by omega)
  by_cases he : i=j
  · subst j
    ring_nf at *
    linarith only [a,b,d,f',g,m,z]
  · have c := terms i (j-2) (by omega)
    have e := terms (i-1) (j-1) (by omega)
    ring_nf at *
    linarith only [a,b,c,d,e,f',g,m,z]

private theorem tri_cross (n : ℕ) : Cross (tri n) := by
  induction n with
  | zero =>
    intro i j h
    simp only [tri]
    split_ifs <;> norm_num <;> omega
  | succ n ih => exact slide ih

/-- Counting ternary words with a marked digit. -/
private theorem marked (n : ℕ) (k : ℤ) :
    ((n:ℚ)-k)*tri n k ≤ ((k:ℚ)+1)*tri n (k+1) := by
  induction n generalizing k with
  | zero =>
    simp only [tri, Nat.cast_zero]
    by_cases h : k=0
    · simp [h]
    · by_cases e : k = -1
      · simp [e]
      · simp [h,show k+1 ≠ 0 by omega]
  | succ n ih =>
    have a := ih k
    have b := ih (k-1)
    have c := ih (k-2)
    simp only [tri, Nat.cast_add, Nat.cast_one]
    rw [show k+1-1=k by omega, show k+1-2=k-1 by omega]
    rw [show k-1+1=k by omega] at b
    rw [show k-2+1=k-1 by omega] at c
    push_cast at b c
    linarith [tri_nonneg n (k-1),tri_nonneg n (k-2)]


/-- Coefficients of X^n (1+2X)^n. -/
def binWeight (n k : ℕ) : ℚ :=
  if n ≤ k then (n.choose (k-n) : ℚ) * 2^(k-n) else 0

private theorem weight_nonneg (n k : ℕ) : 0 ≤ binWeight n k := by
  simp only [binWeight]; split <;> positivity

private theorem weight_step (n j : ℕ) (h : j ≤ n) :
    ((j:ℚ)+1)*binWeight n (n+j+1) = 2*(n-j)*binWeight n (n+j) := by
  have e := Nat.choose_succ_right_eq n j
  have ec : ((n.choose (j+1) : ℕ):ℚ) * ((j:ℚ)+1) = (n.choose j:ℚ)*((n:ℚ)-j) := by
    rw [← Nat.cast_sub h]
    exact_mod_cast e
  simp only [binWeight, if_pos (show n≤n+j+1 by omega), if_pos (show n≤n+j by omega),
    show n+j+1-n=j+1 by omega, show n+j-n=j by omega, pow_succ]
  linear_combination (2 * (2:ℚ)^j) * ec

private theorem upper_marked (n j : ℕ) :
    ((j:ℚ)+1)*tri n ((n:ℤ)+j+1) ≤ ((n:ℚ)-j)*tri n ((n:ℤ)+j) := by
  have m := marked n ((n:ℤ)-j-1)
  rw [← tri_symm n ((n:ℤ)-j-1), ← tri_symm n (((n:ℤ)-j-1)+1),
    show 2*(n:ℤ)-(n-j-1)=n+j+1 by omega, show 2*(n:ℤ)-(n-j-1+1)=n+j by omega] at m
  push_cast at m
  linarith

private def ratio (n k : ℕ) := binWeight n k / tri n k

private theorem ratio_nonneg (n k : ℕ) : 0 ≤ ratio n k :=
  div_nonneg (weight_nonneg _ _) (tri_nonneg _ _)

private theorem ratio_double (n k : ℕ) (hk : k<2*n) : 2*ratio n k ≤ ratio n (k+1) := by
  by_cases h : k<n
  · have z : binWeight n k=0 := if_neg (by omega)
    simpa [ratio,z] using ratio_nonneg n (k+1)
  · let j := k-n
    have ej : k=n+j := by dsimp [j]; omega
    have m := upper_marked n j
    have w := weight_step n j (by omega)
    have p : (0:ℚ) < j+1 := by positivity
    have cross : 2*binWeight n (n+j)*tri n ((n:ℤ)+j+1) ≤
        binWeight n (n+j+1)*tri n ((n:ℤ)+j) := by
      apply le_of_mul_le_mul_left (a := (j:ℚ)+1) _ p
      have mult := mul_le_mul_of_nonneg_left m (mul_nonneg (by decide : (0:ℚ)≤2) (weight_nonneg n (n+j)))
      have ex := congrArg (fun t : ℚ => t*tri n ((n:ℤ)+j)) w
      dsimp at ex
      nlinarith only [mult,ex]
    rw [ej]
    unfold ratio
    have pa := tri_pos n (↑(n+j):ℤ) (by omega) (by omega)
    have pb := tri_pos n (↑(n+j+1):ℤ) (by omega) (by omega)
    rw [← mul_div_assoc, div_le_div_iff₀ pa pb]
    push_cast
    exact cross

private def accum (f : ℕ → ℚ) : ℕ → ℚ
  | 0 => f 0
  | k+1 => accum f k + f (k+1)

private def LC (f : ℕ → ℚ) (k : ℕ) := f k*f (k+2) ≤ f (k+1)^2

private theorem accum_pos {f : ℕ → ℚ} (k : ℕ) (h : ∀ i≤k, 0<f i) : 0<accum f k := by
  induction k with
  | zero => exact h 0 (by omega)
  | succ k ih => exact add_pos (ih (fun i hi => h i (by omega))) (h (k+1) (by omega))

private theorem accum_shift {f : ℕ → ℚ} (k : ℕ)
    (hp : ∀ i≤k+2, 0<f i) (hl : ∀ i≤k, LC f i) :
    accum f k*f (k+2) ≤ accum f (k+1)*f (k+1) := by
  induction k with
  | zero =>
    have h := hl 0 (by omega)
    have h1 := hp 1 (by omega)
    have h0 := hp 0 (by omega)
    change f 0*f 2 ≤ (f 0+f 1)*f 1
    change f 0*f 2 ≤ f 1^2 at h
    nlinarith only [h,mul_nonneg h0.le h1.le]
  | succ k ih =>
    have prior := ih (fun i hi => hp i (by omega)) (fun i hi => hl i (by omega))
    have e : accum f (k+1)*f (k+2) ≤ accum f (k+2)*f (k+1) := by
      change accum f (k+1)*f (k+2) ≤ (accum f (k+1)+f (k+2))*f (k+1)
      change (accum f k + f (k+1))*f (k+2) ≤ _
      linarith
    have p1 := hp (k+1) (by omega)
    have p2 := hp (k+2) (by omega)
    have hf := hl (k+1) (by omega)
    change f (k+1)*f (k+3) ≤ f (k+2)^2 at hf
    have pa := accum_pos (k+1) (fun i hi => hp i (by omega))
    have a := mul_le_mul_of_nonneg_left hf pa.le
    have b := mul_le_mul_of_nonneg_right e p2.le
    apply le_of_mul_le_mul_left (a := f (k+1)) _ p1
    nlinarith only [a,b]

private theorem accum_lc {f : ℕ → ℚ} (k : ℕ) (hp : ∀ i≤k+2,0<f i)
    (hl : ∀ i≤k, LC f i) : LC (accum f) k := by
  have h := accum_shift k hp hl
  simp only [LC,accum] at h ⊢
  linarith

private def diff (n k : ℕ) := tri n k - 2*binWeight n k
private def factor (n k : ℕ) := 1-2*ratio n k

private theorem diff_eq (n k : ℕ) (hk : k ≤ 2*n) : diff n k=tri n k * factor n k := by
  have ht := tri_pos n k (by omega) (by omega)
  unfold diff factor ratio
  field_simp

private theorem ratio_mono (n i j : ℕ) (ij : i≤j) (hj : j≤2*n) : ratio n i≤ratio n j := by
  induction j with
  | zero =>
    have e : i=0 := by omega
    rw [e]
  | succ j ih =>
    by_cases eq : i=j+1
    · rw [eq]
    · have h := ratio_double n j (by omega)
      linarith [ratio_nonneg n j, ih (by omega) (by omega)]

private theorem positive_segment (n h : ℕ) (hh : h≤2*n) (hd : 0<diff n h) :
    ∀ i≤h, 0<diff n i := by
  intro i hi
  have ti := tri_pos n i (by omega) (by omega)
  rw [diff_eq n h hh] at hd
  rw [diff_eq n i (by omega)]
  have he : 0 < factor n h := pos_of_mul_pos_right hd (tri_nonneg n h)
  apply mul_pos ti
  have hs := ratio_mono n i h hi hh
  unfold factor at *
  linarith

private theorem nonneg_concave_lc (u v w : ℚ) (hu : 0≤u) (hw : 0≤w) (hc : u+w≤2*v) :
    u*w≤v^2 := by
  have sq := mul_self_le_mul_self (add_nonneg hu hw) hc
  nlinarith only [sq,sq_nonneg (u-w)]

private theorem diff_lc_pos (n k : ℕ) (hk : k+2≤2*n) (h : 0<diff n (k+2)) :
    LC (diff n) k := by
  have ps := positive_segment n (k+2) hk h
  have ff (i : ℕ) (hi : i≤k+2) : 0<factor n i := by
    have dur := ps i hi
    rwa [diff_eq n i (by omega), mul_pos_iff_of_pos_left (tri_pos n i (by omega) (by omega))] at dur
  have dou := ratio_double n (k+1) (by omega)
  have rr := ratio_nonneg n k
  have c : factor n k + factor n (k+2) ≤ 2*factor n (k+1) := by
    unfold factor
    linarith
  have flc := nonneg_concave_lc _ _ _ (ff k (by omega)).le (ff (k+2) (by omega)).le c
  have tr := tri_cross n ((k:ℤ)+1) ((k:ℤ)+1) le_rfl
  rw [show (k:ℤ)+1-1=k by omega] at tr
  have tr' : tri n (k:ℤ)*tri n ((k+2:ℕ):ℤ) ≤ tri n ((k+1:ℕ):ℤ)^2 := by
    simpa [pow_two] using tr
  have comb := mul_le_mul tr' flc (mul_nonneg (ff k (by omega)).le (ff (k+2) (by omega)).le)
    (sq_nonneg _)
  unfold LC
  rw [diff_eq n k (by omega), diff_eq n (k+1) (by omega), diff_eq n (k+2) hk]
  linarith only [comb]

/-- Two partial sums of the second differences, before cutting the sequence
at the maximum possible total lack 2n−2. -/
def coefficients (n : ℕ) : ℕ → ℚ := accum (accum (diff n))

private theorem model_lc (n k : ℕ) (hk : k+2≤2*n)
    (hu : 0≤coefficients n k) (hw : 0≤coefficients n (k+2)) :
    LC (coefficients n) k := by
  by_cases hd : 0<diff n (k+2)
  · have pos := positive_segment n (k+2) hk hd
    have hloc (i : ℕ) (hi : i≤k) : LC (diff n) i :=
      diff_lc_pos n i (by omega) (pos _ (by omega))
    apply accum_lc
    · intro i hi
      exact accum_pos i (fun j hj => pos j (by omega))
    · intro i hi
      exact accum_lc i (fun j hj => pos j (by omega)) (fun j hj => hloc j (by omega))
  · apply nonneg_concave_lc _ _ _ hu hw
    unfold coefficients
    simp only [accum]
    linarith


inductive Gap where
  | zero | one | two
  deriving DecidableEq, Repr

abbrev Word := List Gap

def mass : Word → ℕ
  | [] => 0
  | .zero::w => mass w
  | .one::w => mass w+1
  | .two::w => mass w+2

def occupied : Word → ℕ
  | [] => 0
  | .zero::w => occupied w
  | .one::w | .two::w => occupied w + 1

def twos : Word → ℕ
  | [] => 0
  | .two::w => twos w+1
  | _::w => twos w

private theorem statistics (w : Word) : mass w=occupied w+twos w ∧
    twos w≤occupied w ∧ occupied w≤w.length := by
  induction w with
  | nil => decide
  | cons x w ih => cases x <;> simp [mass,occupied,twos] <;> omega

/-- Enumerate each possible pattern of lack on the n vertices opposite the sink. -/
def words : ℕ → List Word
  | 0 => [[]]
  | n+1 => (words n).map (Gap.zero::·) ++ (words n).map (Gap.one::·) ++
    (words n).map (Gap.two::·)

private theorem mem_words (w : Word) (n : ℕ) : w ∈ words n ↔ w.length=n := by
  induction n generalizing w with
  | zero => cases w <;> simp [words]
  | succ n ih =>
    cases w with
    | nil => simp [words]
    | cons a w => cases a <;> simp [words,ih]

private def total (n : ℕ) (f : Word → ℚ) := ((words n).map f).sum

private theorem total_succ (n : ℕ) (f : Word → ℚ) : total (n+1) f =
    total n (fun w => f (.zero::w)) + total n (fun w => f (.one::w)) +
    total n (fun w => f (.two::w)) := by simp [total, words,Function.comp_def,add_assoc]

private theorem total_zero (n : ℕ) : total n (fun _ => 0)=0 := by simp [total]

private def atom (d k : ℤ) : ℚ := if k=d then 1 else 0

private theorem atom_shift (d a k : ℤ) : atom (d+a) k=atom d (k-a) := by
  simp only [atom]
  split_ifs <;> first | rfl | omega

private theorem tri_words (n : ℕ) (k : ℤ) : tri n k = total n (fun w => atom (mass w) k) := by
  induction n generalizing k with
  | zero => simp [tri,total,words,mass,atom]
  | succ n ih =>
    rw [tri,total_succ, ih, ih, ih]
    simp only [mass,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat,atom_shift]

private theorem ato_succ (s j : ℕ) : atom (s+1 : ℕ) (j+1 : ℕ)=atom s j := by
  simp [atom]

private theorem ato_zero (s : ℕ) : atom (s+1 : ℕ) 0=0 := if_neg (by omega)

private theorem occupied_count (n j : ℕ) :
    total n (fun w => atom (occupied w) j) = (n.choose j : ℚ)*2^j := by
  induction n generalizing j with
  | zero =>
    cases j with
    | zero => simp [total,words,occupied,atom]
    | succ j => simp [total,words,occupied,atom];omega
  | succ n ih =>
    rw [total_succ]
    cases j with
    | zero =>
      change total n (fun w => atom (occupied w) 0) + total n (fun w => atom (occupied w+1 : ℕ) 0) +
        total n (fun w => atom (occupied w+1 : ℕ) 0) = _
      simp only [ato_zero,total_zero,add_zero]
      simpa using ih 0
    | succ j =>
      change total n (fun w => atom (occupied w) (j+1 : ℕ)) +
        total n (fun w => atom (occupied w+1 : ℕ) (j+1 : ℕ)) +
        total n (fun w => atom (occupied w+1 : ℕ) (j+1 : ℕ)) = _
      have eq : (fun w : Word => atom (occupied w+1 : ℕ) (j+1 : ℕ)) =
          fun w => atom (occupied w) j := funext (fun w => ato_succ (occupied w) j)
      rw [eq,ih (j+1),ih j]
      simp only [Nat.choose_succ_succ,Nat.cast_add,pow_succ]
      ring

private theorem weight_words (n k : ℕ) :
    binWeight n k = total n (fun w => atom (n+occupied w : ℕ) k) := by
  by_cases h : n≤k
  · have he (w : Word) : atom (n+occupied w : ℕ) k = atom (occupied w) (k-n : ℕ) := by
      simp only [atom]
      split_ifs <;> first | rfl | omega
    simp only [binWeight,if_pos h,he,occupied_count]
  · have he (w : Word) : atom (n+occupied w : ℕ) k=0 := if_neg (by omega)
    simp only [binWeight,if_neg h,he,total_zero]

private theorem accum_linear (f g : ℕ → ℚ) (k : ℕ) :
    accum (fun i => f i - 2*g i) k = accum f k-2*accum g k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [accum,ih];ring

private theorem accum_list {α : Type} (l : List α) (f : α → ℕ → ℚ) (k : ℕ) :
    accum (fun i => (l.map (fun w => f w i)).sum) k =
      (l.map (fun w => accum (f w) k)).sum := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [accum,ih]
    clear ih
    induction l with
    | nil => simp
    | cons x l il => simp only [List.map_cons,List.sum_cons]; linarith

private theorem prefix_atom (d k : ℕ) :
    accum (fun i : ℕ => atom d i) k = if d≤k then 1 else 0 := by
  induction k with
  | zero =>
    change atom d 0 = _
    simp [atom,eq_comm]
  | succ k ih =>
    rw [accum,ih]
    simp only [atom]
    split_ifs <;> norm_num <;> omega

private theorem double_atom (d k : ℕ) :
    accum (accum (fun i : ℕ => atom d i)) k = (k+1-d : ℕ) := by
  induction k with
  | zero =>
    rw [accum,prefix_atom]
    cases d <;> simp
  | succ k ih =>
    rw [accum,ih,prefix_atom]
    split_ifs with h
    · exact_mod_cast (by omega : k+1-d+1=k+1+1-d)
    · simp [show k+1-d=0 by omega,show k+1+1-d=0 by omega]

private theorem double_total (n : ℕ) (q : Word → ℕ) (k : ℕ) :
    accum (accum (fun i : ℕ => total n (fun w => atom (q w) i))) k =
      total n (fun w => (k+1-q w : ℕ)) := by
  let f : Word → ℕ → ℚ := fun w i => atom (q w) i
  have inner : accum (fun i => total n (fun w => f w i)) =
      fun i => total n (fun w => accum (f w) i) :=
    funext (accum_list (words n) f)
  change accum (accum (fun i => total n (fun w => f w i))) k = _
  rw [inner]
  change accum (fun i => ((words n).map (fun w => accum (f w) i)).sum) k = _
  rw [accum_list (words n) (fun w => accum (f w))]
  simp [f,double_atom,total]

private theorem coefficient_words (n k : ℕ) :
    coefficients n k = total n (fun w => ((k+1-mass w:ℕ):ℚ)) -
      2*total n (fun w => ((k+1-(n+occupied w):ℕ):ℚ)) := by
  let f : ℕ → ℚ := fun i => total n (fun w => atom (mass w) i)
  let g : ℕ → ℚ := fun i => total n (fun w => atom (n+occupied w : ℕ) i)
  have e : diff n = fun i => f i - 2*g i := by
    funext i
    simp only [diff,tri_words,weight_words,f,g]
  have inner : accum (diff n) = fun i => accum f i - 2*accum g i := by
    rw [e]; exact funext (accum_linear f g)
  rw [coefficients,inner,accum_linear,double_total n mass,double_total n (fun w => n+occupied w)]

private def need : Gap → ℕ
  | .zero => 0
  | .one => 1
  | .two => 2

/-- Orient all three edges incident with each right vertex. A true flag points
from its left endpoint towards the right vertex. The indices count outgoing
edges of the two nonsink left vertices. The right indegree must exceed its lack. -/
inductive Supplies : Word → ℕ → ℕ → Prop where
  | nil : Supplies [] 0 0
  | cons {w : Word} {i j : ℕ} (q : Gap) (a b sink : Bool)
      (enough : need q + 1 ≤ a.toNat + b.toNat + sink.toNat)
      (rest : Supplies w i j) : Supplies (q::w) (i+a.toNat) (j+b.toNat)

private theorem supplies_bounds {w : Word} {i j : ℕ} (h : Supplies w i j) :
    twos w≤i ∧ twos w≤j ∧ mass w≤i+j := by
  induction h with
  | nil => decide
  | cons q a b sink enough rest ih =>
    cases q <;> cases a <;> cases b <;> cases sink <;>
      simp_all [need,twos,mass,Bool.toNat] <;> omega

private theorem fill_caps (w : Word) (U V : ℕ) (u : twos w≤U) (v : twos w≤V)
    (s : mass w≤U+V) : ∃ i j, Supplies w i j ∧ i≤U ∧ j≤V := by
  induction w generalizing U V with
  | nil => exact ⟨0,0,.nil,by omega,by omega⟩
  | cons q w ih =>
    cases q with
    | zero =>
      obtain ⟨i,j,h,h1,h2⟩ := ih U V u v s
      exact ⟨_,_,.cons .zero false false true (by decide) h,h1,h2⟩
    | one =>
      change twos w≤U at u
      change twos w≤V at v
      change mass w+1≤U+V at s
      by_cases extra : twos w<U
      · obtain ⟨i,j,h,h1,h2⟩ := ih (U-1) V (by omega) v (by omega)
        exact ⟨_,_,.cons .one true false true (by decide) h,by change i+1≤U;omega,h2⟩
      · have st := statistics w
        have extra' : twos w<V := by omega
        obtain ⟨i,j,h,h1,h2⟩ := ih U (V-1) u (by omega) (by omega)
        exact ⟨_,_,.cons .one false true true (by decide) h,h1,by change j+1≤V;omega⟩
    | two =>
      change twos w+1≤U at u
      change twos w+1≤V at v
      change mass w+2≤U+V at s
      obtain ⟨i,j,h,h1,h2⟩ := ih (U-1) (V-1) (by omega) (by omega) (by omega)
      exact ⟨_,_,.cons .two true true true (by decide) h,by change i+1≤U;omega,
        by change j+1≤V;omega⟩

/-- The compatible-orientation criterion for recurrence from Proposition 4 of
Alofi–Dukes on K₃,ₙ, with sink on the three-vertex side. The remaining left
vertices have lack x and y. The n opposite right vertices carry the word w. -/
def Compatible (n : ℕ) (w : Word) (x y : ℕ) : Prop :=
  ∃ i j, Supplies w i j ∧ x+i<n ∧ y+j<n

theorem compatible_iff (n : ℕ) (w : Word) (x y : ℕ) :
    Compatible n w x y ↔ x+twos w<n ∧ y+twos w<n ∧ x+y+mass w≤2*n-2 := by
  constructor
  · rintro ⟨i,j,h,hi,hj⟩
    have e := supplies_bounds h
    omega
  · rintro ⟨hx,hy,hs⟩
    obtain ⟨i,j,h,hi,hj⟩ := fill_caps w (n-1-x) (n-1-y) (by omega) (by omega) (by omega)
    exact ⟨i,j,h,by omega,by omega⟩

private theorem tag_nodup (s : Gap) (l : List Word) (h : l.Nodup) :
    (l.map (s :: ·)).Nodup :=
  List.Nodup.map (fun _ _ e => (List.cons.inj e).2) h

private theorem tag_disjoint (s t : Gap) (h : s ≠ t) (l m : List Word) :
    (l.map (s :: ·)).Disjoint (m.map (t :: ·)) := by
  intro w hs ht
  obtain ⟨u, _, hu⟩ := List.mem_map.mp hs
  obtain ⟨v, _, hv⟩ := List.mem_map.mp ht
  exact h (List.cons.inj (hu.trans hv.symm)).1

theorem words_nodup (n : ℕ) : (words n).Nodup := by
  induction n with
  | zero => simp [words]
  | succ n ih =>
    simp only [words,List.nodup_append',List.disjoint_append_left]
    repeat' apply And.intro
    all_goals first | exact tag_nodup _ _ ih | exact tag_disjoint _ _ (by decide) _ _

/-- Possible first left lacks for a given mass R and common exclusive upper bound s.
The second left lack is uniquely determined by the total k. -/
def pairChoices (s R k : ℕ) : Finset ℕ := Finset.Ico (k+1-(R+s)) (min s (k+1-R))

private theorem pairChoices_spec (s R k x : ℕ) :
    x∈pairChoices s R k ↔ x<s ∧ ∃ y, y<s ∧ x+y+R=k := by
  rw [pairChoices,Finset.mem_Ico]
  constructor
  · rintro ⟨lo,hi⟩
    exact ⟨by omega,k-x-R,by omega,by omega⟩
  · rintro ⟨hx,y,hy,he⟩
    omega

theorem compatible_choices (n k : ℕ) (w : Word) (x : ℕ) :
    (k≤2*n-2 ∧ x∈pairChoices (n-twos w) (mass w) k) ↔
      ∃! y, Compatible n w x y ∧ x+y+mass w=k := by
  rw [pairChoices_spec]
  constructor
  · rintro ⟨hk,hx,y,hy,he⟩
    exact ⟨y,⟨(compatible_iff ..).2 ⟨by omega,by omega,by omega⟩,he⟩,
      fun y' hy' => by obtain ⟨_,he'⟩ := hy';omega⟩
  · rintro ⟨y,⟨hc,he⟩,_⟩
    have q := (compatible_iff ..).1 hc
    exact ⟨by omega,by omega,y,by omega,he⟩

/-- Coefficient of total lack k: the number of stochastically recurrent stable
configurations, counted once by the right word and the first left lack. -/
def lackCount (n k : ℕ) : ℕ :=
  if k≤2*n-2 then ((words n).map (fun w => (pairChoices (n-twos w) (mass w) k).card)).sum else 0

private noncomputable def triples (n k : ℕ) (w : Word) : List (Word × ℕ × ℕ) :=
  (pairChoices (n-twos w) (mass w) k).toList.map (fun x => (w, x, k-x-mass w))

/-- All configurations of lack k, with labelled vertices on each side. -/
noncomputable def recurrentConfigs (n k : ℕ) : List (Word × ℕ × ℕ) :=
  if k≤2*n-2 then (words n).flatMap (triples n k) else []

/-- The enumeration agrees pointwise with the three-edge orientation model. -/
theorem mem_recurrentConfigs (n k : ℕ) (w : Word) (x y : ℕ) :
    (w,x,y) ∈ recurrentConfigs n k ↔ w.length=n ∧ Compatible n w x y ∧ x+y+mass w=k := by
  by_cases hk : k≤2*n-2
  · simp only [recurrentConfigs,if_pos hk,List.mem_flatMap,triples,List.mem_map,Finset.mem_toList]
    constructor
    · rintro ⟨w',hw',x',hx',eq⟩
      simp only [Prod.mk.injEq] at eq
      obtain ⟨rfl,rfl,rfl⟩ := eq
      obtain ⟨y',⟨hc,he⟩,_⟩ := (compatible_choices n k w' x').1 ⟨hk,hx'⟩
      have eqy : k-x'-mass w'=y' := by omega
      exact ⟨(mem_words ..).1 hw',eqy ▸ hc,by omega⟩
    · rintro ⟨hw,hc,he⟩
      have huniq : ∃! y, Compatible n w x y ∧ x+y+mass w=k :=
        ⟨y,⟨hc,he⟩,fun y' hy => by obtain ⟨_,e⟩ := hy;omega⟩
      exact ⟨w,(mem_words ..).2 hw,x,((compatible_choices ..).2 huniq).2,
        by rw [show k-x-mass w=y by omega]⟩
  · have bound (h : Compatible n w x y) := ((compatible_iff ..).1 h).2.2
    simp only [recurrentConfigs,if_neg hk,List.not_mem_nil,false_iff,not_and]
    intro _ hc he
    have h := bound hc
    omega

theorem recurrentConfigs_nodup (n k : ℕ) : (recurrentConfigs n k).Nodup := by
  rw [recurrentConfigs]
  split
  · apply List.nodup_flatMap.2
    constructor
    · intro w _
      exact List.Nodup.map (fun a b h => congrArg (fun t : Word × ℕ × ℕ => t.2.1) h)
        (Finset.nodup_toList _)
    · apply (words_nodup n).imp
      intro a b h c ac bc
      obtain ⟨i,_,hi⟩ := List.mem_map.1 ac
      obtain ⟨j,_,hj⟩ := List.mem_map.1 bc
      exact h (congrArg Prod.fst (hi.trans hj.symm))
  · simp

theorem length_recurrentConfigs (n k : ℕ) : (recurrentConfigs n k).length=lackCount n k := by
  by_cases hk : k≤2*n-2 <;> simp [recurrentConfigs,lackCount,hk,triples]

private theorem pair_count (n k : ℕ) (hk : k≤2*n-2) (hn : 1≤n) (w : Word)
    (mem : w∈words n) :
    ((pairChoices (n-twos w) (mass w) k).card : ℚ) =
      ((k+1-mass w:ℕ):ℚ) - 2*((k+1-(n+occupied w):ℕ):ℚ) := by
  have len := (mem_words w n).1 mem
  have st := statistics w
  rw [pairChoices,Nat.card_Ico]
  have e : min (n-twos w) (k+1-mass w) - (k+1-(mass w+(n-twos w))) +
      2*(k+1-(n+occupied w))=k+1-mass w := by omega
  exact eq_sub_of_add_eq (by exact_mod_cast e)

private theorem list_count {α : Type} (ws : List α) (f : α → ℕ) (u v : α → ℚ)
    (h : ∀ w∈ws, (f w : ℚ)=u w-2*v w) :
    ((ws.map f).sum : ℚ) = (ws.map u).sum-2*(ws.map v).sum := by
  induction ws with
  | nil => simp
  | cons w ws ih =>
    have first := h w (List.mem_cons_self ..)
    have rest := ih (fun a ha => h a (List.mem_cons_of_mem _ ha))
    simp only [List.map_cons,List.sum_cons,Nat.cast_add]
    linarith

theorem coefficient_count (n k : ℕ) (hn : 1≤n) (hk : k≤2*n-2) :
    (lackCount n k : ℚ)=coefficients n k := by
  rw [lackCount,if_pos hk,coefficient_words]
  exact list_count _ _ _ _ (pair_count n k hk hn)

/-- Conjecture 13(i) of Alofi–Dukes on the entire K₃,ₙ row, for a sink
on the three-vertex side. -/
theorem alofi_dukes_log_concave (n k : ℕ) (hn : 2≤n) (hk : k+2≤2*n-2) :
    lackCount n k * lackCount n (k+2) ≤ (lackCount n (k+1))^2 := by
  have bridge (j : ℕ) (hj : j≤2*n-2) := coefficient_count n j (by omega) hj
  have a := bridge k (by omega)
  have b := bridge (k+1) (by omega)
  have c := bridge (k+2) hk
  have result := model_lc n k (by omega) (a ▸ Nat.cast_nonneg _) (c ▸ Nat.cast_nonneg _)
  unfold LC at result
  rw [← a,← b,← c] at result
  exact_mod_cast result

private theorem zero_stats (n : ℕ) :
    twos (List.replicate n .zero)=0 ∧ mass (List.replicate n .zero)=0 := by
  induction n with
  | zero => decide
  | succ n ih => simpa [List.replicate_succ,twos,mass] using ih

theorem lackCount_pos (n k : ℕ) (hn : 1≤n) (hk : k≤2*n-2) : 0<lackCount n k := by
  rw [lackCount,if_pos hk,Nat.sum_pos_iff_exists_pos]
  let w := List.replicate n Gap.zero
  have hw : w∈words n := (mem_words ..).2 (List.length_replicate ..)
  have stats := zero_stats n
  have mem : min k (n-1) ∈ pairChoices (n-twos w) (mass w) k := by
    rw [show twos w=0 from stats.1,show mass w=0 from stats.2,Nat.sub_zero,pairChoices_spec]
    exact ⟨by omega,k-min k (n-1),by omega,by omega⟩
  exact ⟨_,List.mem_map.mpr ⟨w,hw,rfl⟩,Finset.card_pos.2 ⟨_,mem⟩⟩

/-- A peak on the complete interval from 0 to D, allowing a plateau. -/
def UnimodalOn (f : ℕ → ℕ) (D : ℕ) : Prop :=
  ∃ p≤D, (∀ i, i<p → f i≤f (i+1)) ∧ (∀ i, p≤i → i<D → f (i+1)≤f i)

private theorem unimodal_of_lc (f : ℕ → ℕ) (D : ℕ) (pos : ∀ i, i≤D → 0<f i)
    (lc : ∀ i, i+2≤D → f i * f (i+2)≤ f (i+1)^2) : UnimodalOn f D := by
  by_cases some : ∃ i : ℕ, i<D ∧ f (i+1)<f i
  · let p := Nat.find some
    have hp : p<D ∧ f (p+1)<f p := Nat.find_spec some
    have tail (t : ℕ) : p+t<D → f (p+t+1)≤f (p+t) := by
      induction t with
      | zero => intro _; exact hp.2.le
      | succ t ih =>
        intro last
        have prev := ih (by omega)
        apply Nat.le_of_mul_le_mul_left (c:=f (p+t)) _ (pos _ (by omega))
        calc
          _ ≤ f (p+t+1)^2 := lc _ (by omega)
          _ ≤ _ := by rw [pow_two];exact Nat.mul_le_mul_right _ prev
    refine ⟨p,hp.1.le,?_,?_⟩
    · intro i hip
      have before := Nat.find_min some hip
      by_contra! ht
      exact before ⟨by omega,ht⟩
    · intro i lo hi
      obtain ⟨t,rfl⟩ := Nat.exists_eq_add_of_le lo
      exact tail t hi
  · refine ⟨D,le_rfl,?_,by omega⟩
    intro i hi
    by_contra! ht
    exact some ⟨i,hi,ht⟩

/-- Conjecture 13(ii) of Alofi–Dukes for the same infinite family. -/
theorem alofi_dukes_unimodal (n : ℕ) (hn : 2≤n) :
    UnimodalOn (lackCount n) (2*n-2) :=
  unimodal_of_lc _ _ (fun i hi => lackCount_pos n i (by omega) hi)
    (fun k hk => alofi_dukes_log_concave n k hn hk)

/-- Both conclusions directly for the list proved to contain exactly the
orientation-compatible configurations of the prescribed total lack, once each. -/
theorem alofi_dukes_configurations (n : ℕ) (hn : 2≤n) :
    (∀ k, k+2≤2*n-2 →
      (recurrentConfigs n k).length * (recurrentConfigs n (k+2)).length ≤
      (recurrentConfigs n (k+1)).length^2) ∧
    UnimodalOn (fun k => (recurrentConfigs n k).length) (2*n-2) := by
  simp only [length_recurrentConfigs]
  exact ⟨fun k => alofi_dukes_log_concave n k hn,alofi_dukes_unimodal n hn⟩

#print axioms compatible_iff
#print axioms mem_recurrentConfigs
#print axioms recurrentConfigs_nodup
#print axioms length_recurrentConfigs
#print axioms alofi_dukes_log_concave
#print axioms alofi_dukes_unimodal
#print axioms alofi_dukes_configurations

end ThreeSandpile

namespace ThreeSandpile
namespace Transposed

private def shifted (n : ℕ) : ℕ → ℚ
  | 0 => 0
  | i+1 => binWeight n i

private theorem shifted_nonneg (n k : ℕ) : 0≤shifted n k := by
  cases k with
  | zero => exact le_rfl
  | succ i => exact weight_nonneg n i

private theorem shifted_zero (n k : ℕ) (hk : k≤n) : shifted n k=0 := by
  cases k with
  | zero => rfl
  | succ i => simp [shifted,binWeight,show ¬n≤i by omega]

private def rat (n k : ℕ) := shifted n k / tri n k
private def cseq (n k : ℕ) := tri n k - 3*shifted n k
private def fac (n k : ℕ) := 1-3*rat n k

private theorem rat_nonneg (n k : ℕ) : 0≤rat n k :=
  div_nonneg (shifted_nonneg ..) (tri_nonneg ..)

private theorem rat_double (n k : ℕ) (hk : k<2*n) : 2*rat n k≤rat n (k+1) := by
  by_cases h : k≤n
  · simpa [rat,shifted_zero n k h] using rat_nonneg n (k+1)
  · let j := k-(n+1)
    have ej : k=n+j+1 := by dsimp [j];omega
    have upper := upper_marked n (j+1)
    push_cast at upper
    rw [show (n:ℤ)+(j+1)=n+j+1 by omega] at upper
    have m : ((j:ℚ)+1)*tri n ((n:ℤ)+j+1+1) ≤ (n-j)*tri n ((n:ℤ)+j+1) := by
      linarith [tri_nonneg n ((n:ℤ)+j+1),tri_nonneg n ((n:ℤ)+j+1+1)]
    have w := weight_step n j (by omega)
    have p : (0:ℚ)<j+1 := by positivity
    have cross : 2*binWeight n (n+j)*tri n ((n:ℤ)+j+1+1) ≤
        binWeight n (n+j+1)*tri n ((n:ℤ)+j+1) := by
      apply le_of_mul_le_mul_left (a := (j:ℚ)+1) _ p
      have m' := mul_le_mul_of_nonneg_left m (mul_nonneg (by decide : (0:ℚ)≤2) (weight_nonneg n (n+j)))
      have eq := congrArg (fun t : ℚ => t*tri n ((n:ℤ)+j+1)) w
      dsimp at eq
      nlinarith only [m',eq]
    rw [ej]
    unfold rat
    rw [← mul_div_assoc,div_le_div_iff₀ (tri_pos n _ (by omega) (by omega))
      (tri_pos n _ (by omega) (by omega))]
    simp only [shifted,Nat.cast_add,Nat.cast_one]
    exact cross

private theorem cseq_eq (n k : ℕ) (hk : k≤2*n) : cseq n k=tri n k * fac n k := by
  have ht := tri_pos n k (by omega) (by omega)
  unfold cseq fac rat
  field_simp

private theorem rat_mono (n i j : ℕ) (ij : i≤j) (hj : j≤2*n) : rat n i≤rat n j := by
  induction j with
  | zero => rw [show i=0 by omega]
  | succ j ih =>
    by_cases eq : i=j+1
    · rw [eq]
    · linarith [rat_double n j (by omega),rat_nonneg n j,ih (by omega) (by omega)]

private theorem cseq_prefix (n h : ℕ) (hh : h≤2*n) (hd : 0<cseq n h) :
    ∀ i≤h, 0<cseq n i := by
  intro i hi
  rw [cseq_eq n h hh] at hd
  rw [cseq_eq n i (by omega)]
  have ff : 0 < fac n h := pos_of_mul_pos_right hd (tri_nonneg n h)
  apply mul_pos (tri_pos n i (by omega) (by omega))
  have hs := rat_mono n i h hi hh
  unfold fac at *
  linarith

private theorem cseq_lc (n k : ℕ) (hk : k+2≤2*n) (h : 0<cseq n (k+2)) :
    LC (cseq n) k := by
  have ps := cseq_prefix n (k+2) hk h
  have ff (i : ℕ) (hi : i≤k+2) : 0<fac n i := by
    have d := ps i hi
    rwa [cseq_eq n i (by omega),mul_pos_iff_of_pos_left (tri_pos n i (by omega) (by omega))] at d
  have d := rat_double n (k+1) (by omega)
  have c : fac n k + fac n (k+2)≤2*fac n (k+1) := by
    unfold fac
    linarith [rat_nonneg n k]
  have fLC := nonneg_concave_lc _ _ _ (ff k (by omega)).le (ff (k+2) le_rfl).le c
  have triLC := tri_cross n ((k:ℤ)+1) ((k:ℤ)+1) le_rfl
  rw [show (k:ℤ)+1-1=k by omega] at triLC
  have tr : tri n (k:ℤ)*tri n ((k+2:ℕ):ℤ)≤tri n ((k+1:ℕ):ℤ)^2 := by
    simpa [pow_two] using triLC
  have comb := mul_le_mul tr fLC (mul_nonneg (ff k (by omega)).le (ff _ le_rfl).le) (sq_nonneg _)
  unfold LC
  rw [cseq_eq n k (by omega), cseq_eq n (k+1) (by omega), cseq_eq n (k+2) hk]
  linarith only [comb]

private theorem tri_upper (n k : ℕ) (hk : n≤k) : tri n ((k:ℤ)+1)≤tri n k := by
  have q := tri_cross n (2*(n:ℤ)-k) k (by omega)
  rw [show 2*(n:ℤ)-k-1=2*n-(k+1) by omega,tri_symm,tri_symm] at q
  nlinarith [tri_nonneg n (k:ℤ),tri_nonneg n ((k:ℤ)+1)]

private theorem shifted_increasing (n k : ℕ) (hk : k+1≤n+1+(2*n)/3) :
    shifted n k≤shifted n (k+1) := by
  by_cases h : k≤n
  · rw [shifted_zero n k h]
    exact shifted_nonneg n _
  · let j := k-(n+1)
    have ej : k=n+j+1 := by dsimp [j];omega
    have w := weight_step n j (by omega)
    have coef : (j:ℚ)+1≤2*(n-j) := by
      have nat : j+1 ≤ 2*(n-j) := by omega
      rw [← Nat.cast_sub (by omega : j≤n)]
      exact_mod_cast nat
    rw [ej]
    change binWeight n (n+j)≤binWeight n (n+j+1)
    apply le_of_mul_le_mul_left (a:=(j:ℚ)+1) _ (by positivity)
    rw [w]
    exact mul_le_mul_of_nonneg_right coef (weight_nonneg ..)

private theorem shifted_words (n k : ℕ) :
    shifted n k=total n (fun w => atom (n+1+occupied w : ℕ) k) := by
  cases k with
  | zero =>
    have zero (w : Word) : atom (n+1+occupied w : ℕ) 0=0 := if_neg (by omega)
    simp only [shifted,Nat.cast_zero,zero,total_zero]
  | succ k =>
    rw [shifted,weight_words]
    congr 1
    funext w
    simp only [atom]
    split_ifs <;> first | rfl | omega

private def turn : Gap → Gap
  | .zero => .one
  | .one => .two
  | .two => .zero

private def rotate (w : Word) := w.map turn

private theorem rotation_stats (w : Word) :
    occupied w+occupied (rotate w)+occupied (rotate (rotate w))=2*w.length := by
  induction w with
  | nil => rfl
  | cons q w ih =>
    cases q <;> simp only [rotate,List.map_cons,turn,occupied,List.length_cons] at * <;> omega

private theorem total_rotate (n : ℕ) (f : Word → ℚ) :
    total n (fun w => f (rotate w))=total n f := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
    rw [total_succ,total_succ]
    change total n (fun w => f (.one::rotate w))+total n (fun w => f (.two::rotate w))+
      total n (fun w => f (.zero::rotate w))=_
    rw [ih (fun w => f (.one::w)),ih (fun w => f (.two::w)),ih (fun w => f (.zero::w))]
    ring

private theorem total_compare (n : ℕ) (f g : Word→ℚ) (h : ∀ w, w.length=n → f w≤g w) :
    total n f≤total n g := by
  have e (ws : List Word) (all : ∀ w∈ws, w.length=n) : (ws.map f).sum≤(ws.map g).sum := by
    induction ws with
    | nil => simp
    | cons w ws ih =>
      simp only [List.map_cons,List.sum_cons]
      exact add_le_add (h w (all _ (List.mem_cons_self ..)))
        (ih (fun v hv => all v (List.mem_cons_of_mem _ hv)))
  exact e _ (fun w hw => (mem_words ..).1 hw)

private theorem total_add (n : ℕ) (f g : Word→ℚ) :
    total n (fun w => f w+g w) = total n f + total n g := by
  unfold total
  induction words n with
  | nil => simp
  | cons w ws ih => simp only [List.map_cons,List.sum_cons];linarith

private theorem accum_total (q : Word→ℕ) (n k : ℕ) :
    accum (fun i : ℕ => total n (fun w => atom (q w) i)) k=
    total n (fun w => if q w≤k then 1 else 0) := by
  simpa only [total,prefix_atom] using (accum_list (words n) (fun w i => atom (q w) (i:ℕ)) k)

private theorem accum3 (f g : ℕ→ℚ) (k : ℕ) :
    accum (fun i => f i-3*g i) k = accum f k-3*accum g k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [accum,ih];ring

private def first (n : ℕ) := accum (cseq n)

/-- In each orbit under cyclic relabelling of the three digits, at least one
word has at most floor(2n/3) occupied positions. -/
private theorem first_tail (n k : ℕ) (hk : n+1+(2*n)/3≤k) : first n k≤0 := by
  let g : Word→ℚ := fun w => if n+1+occupied w≤k then 1 else 0
  have point (w : Word) (hn : w.length=n) : 1≤g w+g (rotate w)+g (rotate (rotate w)) := by
    have stats := rotation_stats w
    dsimp [g]
    split_ifs <;> norm_num
    omega
  have comp := total_compare n _ _ point
  rw [total_add,total_add,total_rotate n g,total_rotate n (fun w => g (rotate w)),total_rotate n g] at comp
  have unit := total_compare n (fun w => if mass w≤k then 1 else 0) (fun _ => 1)
    (fun w _ => by dsimp; split <;> norm_num)
  change accum (fun i => tri n (i:ℤ)-3*shifted n i) k≤0
  have a : (fun i : ℕ => tri n (i:ℤ))=fun i : ℕ => total n (fun w => atom (mass w) i) :=
    funext (fun i => tri_words n i)
  have b : shifted n=fun i : ℕ => total n (fun w => atom (n+1+occupied w : ℕ) i) :=
    funext (shifted_words n)
  rw [accum3,a,b]
  rw [accum_total mass,accum_total (fun w => n+1+occupied w)]
  change _ - 3*total n g≤0
  linarith

private theorem first_prefix (n k : ℕ) (hk : k≤2*n) (h : 0<first n k) :
    ∀ i≤k, 0<first n i := by
  induction k with
  | zero => simpa using h
  | succ k ih =>
    have prev : 0<first n k := by
      by_cases c : 0<cseq n (k+1)
      · exact accum_pos k (fun j hj => cseq_prefix n (k+1) hk c j (by omega))
      · change 0<first n k+cseq n (k+1) at h
        linarith
    intro i hi
    by_cases e : i=k+1
    · rwa [e]
    · exact ih (by omega) prev i (by omega)

private theorem first_lc (n k : ℕ) (hk : k+2≤2*n) (h : 0<first n (k+2)) :
    LC (first n) k := by
  by_cases c : 0<cseq n (k+2)
  · have prefix' := cseq_prefix n (k+2) hk c
    exact accum_lc k prefix' (fun i hi => cseq_lc n i (by omega) (prefix' _ (by omega)))
  · have cut : k+2<n+1+(2*n)/3 := by
      by_contra! e
      linarith [first_tail n (k+2) e]
    have lower : n≤k+1 := by
      by_contra! e
      have z := shifted_zero n (k+2) (by omega)
      simp only [cseq,z,mul_zero,sub_zero] at c
      exact c (tri_pos n _ (by omega) (by omega))
    have a := tri_upper n (k+1) lower
    have b := shifted_increasing n (k+1) cut.le
    have down : cseq n (k+2)≤cseq n (k+1) := by
      simp only [cseq,Nat.cast_add,Nat.cast_ofNat,Nat.cast_one] at *
      rw [show (k:ℤ)+2=k+1+1 by omega]
      linarith
    apply nonneg_concave_lc _ _ _ (first_prefix n _ hk h k (by omega)).le h.le
    change first n k+(first n k+cseq n (k+1)+cseq n (k+2))≤2*(first n k+cseq n (k+1))
    linarith

def coefficients (n : ℕ) := accum (accum (first n))

private theorem coefficient_lc (n k : ℕ) (hk : k+2≤2*n)
    (hu : 0≤coefficients n k) (hw : 0≤coefficients n (k+2)) : LC (coefficients n) k := by
  by_cases h : 0<first n (k+2)
  · have ps := first_prefix n _ hk h
    have local' (i : ℕ) (hi : i≤k) := first_lc n i (by omega) (ps (i+2) (by omega))
    apply accum_lc
    · intro i hi
      exact accum_pos i (fun j hj => ps j (by omega))
    · intro i hi
      exact accum_lc i (fun j hj => ps j (by omega)) (fun j hj => local' j (by omega))
  · apply nonneg_concave_lc _ _ _ hu hw
    unfold coefficients
    simp only [accum]
    linarith

private def slots : Gap → ℕ
  | .zero => 2
  | .one => 1
  | .two => 0

private def active : Word → ℕ
  | [] => 0
  | .two::w => active w
  | _::w => active w+1

private def capacity : Word → ℕ
  | [] => 0
  | q::w => capacity w+slots q

private theorem capFacts (w : Word) :
    active w+twos w=w.length ∧ capacity w+mass w=2*w.length ∧
    active w≤capacity w ∧ capacity w≤2*active w := by
  induction w with
  | nil => decide
  | cons q w ih => cases q <;> simp [active,capacity,slots,mass,twos] <;> omega

/-- For each nonsink on the large side, three independent flags specify
outgoing edges to the opposite vertices. Its lack q leaves at most 2−q outgoing
edges. The indices count the contributions to the three opposite indegrees. -/
inductive Rows : Word → ℕ → ℕ → ℕ → Prop where
  | nil : Rows [] 0 0 0
  | cons {w : Word} {i j l : ℕ} (q : Gap) (a b c : Bool)
      (space : a.toNat+b.toNat+c.toNat≤slots q) (rest : Rows w i j l) :
      Rows (q::w) (i+a.toNat) (j+b.toNat) (l+c.toNat)

private theorem rowBounds {w : Word} {i j l : ℕ} (h : Rows w i j l) :
    i≤active w ∧ j≤active w ∧ l≤active w ∧ i+j+l≤capacity w := by
  induction h with
  | nil => decide
  | cons q a b c _ _ ih =>
    cases q <;> cases a <;> cases b <;> cases c <;>
      simp_all [slots,active,capacity,Bool.toNat] <;> omega

set_option maxHeartbeats 500000 in
private theorem reduceRow (t C q x y z : ℕ) (ht : t≤C) (hC : C≤2*t) (qb : q=1 ∨ q=2)
    (hx : x≤t+1) (hy : y≤t+1) (hz : z≤t+1) (h : x+y+z≤C+q) :
    ∃ a b c : Bool, a.toNat+b.toNat+c.toNat≤q ∧ a.toNat≤x ∧ b.toNat≤y ∧ c.toNat≤z ∧
      x-a.toNat≤t ∧ y-b.toNat≤t ∧ z-c.toNat≤t ∧ x-a.toNat+(y-b.toNat)+(z-c.toNat)≤C := by
  rcases qb with rfl|rfl <;> simp [Bool.exists_bool] <;> omega

private theorem fillRows (w : Word) (x y z : ℕ) (hx : x≤active w) (hy : y≤active w)
    (hz : z≤active w) (hs : x+y+z≤capacity w) : Rows w x y z := by
  induction w generalizing x y z with
  | nil =>
    change x≤0 at hx
    change y≤0 at hy
    change z≤0 at hz
    simpa [show x=0 by omega,show y=0 by omega,show z=0 by omega] using Rows.nil
  | cons q w ih =>
    have step (q : Gap) (qb : slots q=1 ∨ slots q=2) (x y z : ℕ)
        (hx : x≤active w+1) (hy : y≤active w+1) (hz : z≤active w+1)
        (hs : x+y+z≤capacity w+slots q) : Rows (q::w) x y z := by
      have f := capFacts w
      obtain ⟨a,b,c,st,ax,by',cz,hx',hy',hz',hs'⟩ :=
        reduceRow _ _ _ _ _ _ f.2.2.1 f.2.2.2 qb hx hy hz hs
      have o := Rows.cons q a b c st (ih _ _ _ hx' hy' hz' hs')
      rwa [Nat.sub_add_cancel ax,Nat.sub_add_cancel by',Nat.sub_add_cancel cz] at o
    cases q with
    | zero => exact step _ (Or.inr rfl) x y z hx hy hz hs
    | one => exact step _ (Or.inl rfl) x y z hx hy hz hs
    | two => exact Rows.cons .two false false false (by decide) (ih x y z hx hy hz hs)

/-- Orient all edges of K_(N+1),3, with the sink on the N+1 side. The word
lists the N nonsink left lacks. Each right vertex has its own independent sink
edge flag as well as its ordinary incoming edges counted by Rows. -/
def Compatible (w : Word) (x y z : ℕ) : Prop :=
  ∃ i j l, Rows w i j l ∧ ∃ a b c : Bool,
    x+1≤i+a.toNat ∧ y+1≤j+b.toNat ∧ z+1≤l+c.toNat

theorem compatible_iff (w : Word) (x y z : ℕ) :
    Compatible w x y z ↔ x≤active w ∧ y≤active w ∧ z≤active w ∧ x+y+z≤capacity w := by
  constructor
  · rintro ⟨i,j,l,h,a,b,c,hx,hy,hz⟩
    have f := rowBounds h
    cases a <;> cases b <;> cases c <;> simp [Bool.toNat] at * <;> omega
  · rintro ⟨hx,hy,hz,hs⟩
    exact ⟨x,y,z,fillRows w x y z hx hy hz hs,true,true,true,le_rfl,le_rfl,le_rfl⟩

private noncomputable def rightPairs (s R k : ℕ) : List (ℕ×ℕ) :=
  (pairChoices s R k).toList.map (fun y => (y,k-y-R))

private theorem mem_rightPairs (s R k y z : ℕ) :
    (y,z)∈rightPairs s R k ↔ y<s ∧ z<s ∧ y+z+R=k := by
  simp only [rightPairs,List.mem_map,Finset.mem_toList,Prod.mk.injEq]
  constructor
  · rintro ⟨y',hy',rfl,rfl⟩
    obtain ⟨hy,z',hz',he⟩ := (pairChoices_spec ..).1 hy'
    omega
  · rintro ⟨hy,hz,he⟩
    exact ⟨y,(pairChoices_spec ..).2 ⟨hy,z,hz,he⟩,rfl,by omega⟩

private def tagged {α β : Type} (xs : List α) (f : α→List β) :=
  xs.flatMap (fun x => (f x).map (fun y => (x,y)))

private theorem mem_tagged {α β : Type} (xs : List α) (f : α→List β) (x : α) (y : β) :
    (x,y)∈tagged xs f ↔ x∈xs ∧ y∈f x := by simp [tagged]

private theorem tagged_nodup {α β : Type} (xs : List α) (f : α→List β)
    (hx : xs.Nodup) (hf : ∀ x, (f x).Nodup) : (tagged xs f).Nodup := by
  apply List.nodup_flatMap.2
  constructor
  · intro x _
    exact List.Nodup.map (fun _ _ h => congrArg Prod.snd h) (hf x)
  · apply hx.imp
    intro a b hab c hac hbc
    obtain ⟨i,_,hi⟩ := List.mem_map.1 hac
    obtain ⟨j,_,hj⟩ := List.mem_map.1 hbc
    exact hab (congrArg Prod.fst (hi.trans hj.symm))

private noncomputable def rightTriples (k : ℕ) (w : Word) : List (ℕ×ℕ×ℕ) :=
  tagged (List.range (active w+1)) (fun x => rightPairs (active w+1) (mass w+x) k)

private theorem mem_rightTriples (k : ℕ) (w : Word) (x y z : ℕ) :
    (x,y,z)∈rightTriples k w ↔ x≤active w ∧ y≤active w ∧ z≤active w ∧ x+y+z+mass w=k := by
  rw [rightTriples,mem_tagged,List.mem_range,mem_rightPairs]
  omega

/-- All labelled compatible configurations of total lack k on K_(N+1),3. -/
noncomputable def recurrentConfigs (N k : ℕ) : List (Word×ℕ×ℕ×ℕ) :=
  if k≤2*N then tagged (words N) (rightTriples k) else []

theorem mem_recurrentConfigs (N k : ℕ) (w : Word) (x y z : ℕ) :
    (w,x,y,z)∈recurrentConfigs N k ↔
    w.length=N ∧ Compatible w x y z ∧ x+y+z+mass w=k := by
  have f := capFacts w
  by_cases hk : k≤2*N
  · rw [recurrentConfigs,if_pos hk,mem_tagged,mem_words,mem_rightTriples,compatible_iff]
    omega
  · simp only [recurrentConfigs,if_neg hk,List.not_mem_nil,false_iff,compatible_iff,not_and]
    omega

theorem recurrentConfigs_nodup (N k : ℕ) : (recurrentConfigs N k).Nodup := by
  rw [recurrentConfigs]
  split
  · apply tagged_nodup _ _ (words_nodup N)
    intro w
    apply tagged_nodup _ _ List.nodup_range
    intro x
    exact List.Nodup.map (fun _ _ h => congrArg Prod.fst h) (Finset.nodup_toList _)
  · simp

private def wordCount (k : ℕ) (w : Word) :=
  ((List.range (active w+1)).map (fun x => (pairChoices (active w+1) (mass w+x) k).card)).sum

def lackCount (N k : ℕ) : ℕ :=
  if k≤2*N then ((words N).map (wordCount k)).sum else 0

theorem length_recurrentConfigs (N k : ℕ) : (recurrentConfigs N k).length=lackCount N k := by
  by_cases hk : k≤2*N <;> simp [recurrentConfigs,lackCount,hk,rightTriples,rightPairs,tagged]
  rfl

private def ramp (d k : ℕ) : ℚ := (k+1-d : ℕ)
private def triangle (d : ℕ) := accum (ramp d)

private theorem triangle_step (d k : ℕ) : triangle d k-triangle (d+1) k=ramp d k := by
  induction k with
  | zero => cases d <;> simp [triangle,accum,ramp]
  | succ k ih =>
    change (triangle d k + ramp d (k+1)) - (triangle (d+1) k + ramp (d+1) (k+1))=ramp d (k+1)
    have eq : ramp (d+1) (k+1)=ramp d k := by
      unfold ramp
      congr 1
      omega
    linarith

private theorem triangle_zero (d k : ℕ) (hk : k<d) : triangle d k=0 := by
  have zero (i : ℕ) (hi : i<d) : ramp d i=0 := by simp [ramp,show i+1-d=0 by omega]
  induction k with
  | zero => exact zero 0 hk
  | succ k ih =>
    change triangle d k + ramp d (k+1)=0
    rw [ih (by omega),zero _ hk,add_zero]

private theorem sum_ramp (s d k : ℕ) :
    ((List.range s).map (fun x => ramp (d+x) k)).sum=triangle d k-triangle (d+s) k := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [List.range_succ,List.map_append,List.sum_append,ih]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Nat.add_succ]
    linarith [triangle_step (d+s) k]

private theorem pair_formula (s R k : ℕ) (hk : k<R+2*s) :
    ((pairChoices s R k).card : ℚ)=ramp R k-2*ramp (R+s) k := by
  rw [pairChoices,Nat.card_Ico]
  have e : min s (k+1-R) - (k+1-(R+s)) + 2*(k+1-(R+s))=k+1-R := by omega
  exact eq_sub_of_add_eq (by unfold ramp;exact_mod_cast e)

private theorem word_formula (N k : ℕ) (w : Word) (hw : w∈words N) (hk : k≤2*N) :
    (wordCount k w : ℚ)=triangle (mass w) k-3*triangle (N+1+occupied w) k := by
  let s := active w+1
  let R := mass w
  have len := (mem_words ..).1 hw
  have facts := capFacts w
  have stats := statistics w
  have eq : R+s=N+1+occupied w := by dsimp [R,s];omega
  have bound : k<R+s+s := by dsimp [R,s];omega
  have e (x : ℕ) (_mem : x∈List.range s) :
      ((pairChoices s (R+x) k).card : ℚ)=ramp (R+x) k-2*ramp (R+s+x) k := by
    rw [pair_formula _ _ _ (by omega),show R+x+s=R+s+x by omega]
  change (((List.range s).map (fun x => (pairChoices s (R+x) k).card)).sum : ℚ)=_
  rw [list_count (List.range s) _ _ _ e,sum_ramp,sum_ramp,triangle_zero _ _ bound,eq]
  ring

private theorem triple_sub (f g : ℕ → ℚ) (k : ℕ) :
    accum (accum (accum (fun i => f i-3*g i))) k =
    accum (accum (accum f)) k - 3*accum (accum (accum g)) k := by
  have a : accum (fun i => f i-3*g i)=fun i => accum f i-3*accum g i := funext (accum3 f g)
  have b : accum (fun i => accum f i-3*accum g i)=
    fun i => accum (accum f) i-3*accum (accum g) i := funext (accum3 _ _)
  rw [a,b,accum3]

private theorem triple_total (N : ℕ) (q : Word→ℕ) (k : ℕ) :
    accum (accum (accum (fun i : ℕ => total N (fun w => atom (q w) i)))) k =
    total N (fun w => triangle (q w) k) := by
  have e := funext (double_total N q)
  rw [e]
  exact accum_list (words N) (fun w => ramp (q w)) k

private theorem coefficient_words (N k : ℕ) :
    coefficients N k=total N (fun w => triangle (mass w) k)-
      3*total N (fun w => triangle (N+1+occupied w) k) := by
  let f : ℕ→ℚ := fun i => total N (fun w => atom (mass w) i)
  let g : ℕ→ℚ := fun i => total N (fun w => atom (N+1+occupied w : ℕ) i)
  have e : cseq N=fun i => f i-3*g i := by
    funext i
    simp only [cseq,tri_words,shifted_words,f,g]
  rw [coefficients,first,e,triple_sub,triple_total N mass,triple_total N (fun w => N+1+occupied w)]

private theorem list_three {α : Type} (ws : List α) (f : α → ℕ) (u v : α → ℚ)
    (h : ∀ w∈ws, (f w : ℚ)=u w-3*v w) :
    ((ws.map f).sum : ℚ) = (ws.map u).sum-3*(ws.map v).sum := by
  induction ws with
  | nil => simp
  | cons w ws ih =>
    have first' := h w (List.mem_cons_self ..)
    have rest := ih (fun a ha => h a (List.mem_cons_of_mem _ ha))
    simp only [List.map_cons,List.sum_cons,Nat.cast_add]
    linarith

theorem coefficient_count (N k : ℕ) (hk : k≤2*N) : (lackCount N k : ℚ)=coefficients N k := by
  rw [lackCount,if_pos hk,coefficient_words]
  exact list_three _ _ _ _ (fun w hw => word_formula N k w hw hk)

theorem lackCount_pos (N k : ℕ) (hk : k≤2*N) : 0<lackCount N k := by
  let w := List.replicate N Gap.zero
  have len : w.length=N := List.length_replicate ..
  obtain ⟨tw,ma⟩ := zero_stats N
  change twos w=0 at tw
  change mass w=0 at ma
  have facts := capFacts w
  rw [← length_recurrentConfigs,List.length_pos_iff_exists_mem]
  refine ⟨(w,min k N,k-min k N,0),(mem_recurrentConfigs ..).2 ⟨len,?_,by omega⟩⟩
  rw [compatible_iff]
  omega

/-- With the sink on the side of N+1 vertices, the coefficients are log-concave. -/
theorem alofi_dukes_log_concave (N k : ℕ) (hk : k+2≤2*N) :
    lackCount N k * lackCount N (k+2)≤(lackCount N (k+1))^2 := by
  have a := coefficient_count N k (by omega)
  have b := coefficient_count N (k+1) (by omega)
  have c := coefficient_count N (k+2) hk
  have result := coefficient_lc N k hk (a ▸ Nat.cast_nonneg _) (c ▸ Nat.cast_nonneg _)
  unfold LC at result
  rw [← a,← b,← c] at result
  exact_mod_cast result

theorem alofi_dukes_unimodal (N : ℕ) : UnimodalOn (lackCount N) (2*N) :=
  unimodal_of_lc _ _ (lackCount_pos N) (alofi_dukes_log_concave N)

/-- Alofi–Dukes Conjecture 13(i,ii) on K_(N+1),3 directly for the lists
characterized by all labelled stable configurations and all edge orientations. -/
theorem alofi_dukes_configurations (N : ℕ) :
    (∀ k, k+2≤2*N →
      (recurrentConfigs N k).length * (recurrentConfigs N (k+2)).length ≤
      (recurrentConfigs N (k+1)).length^2) ∧
    UnimodalOn (fun k => (recurrentConfigs N k).length) (2*N) := by
  simp only [length_recurrentConfigs]
  exact ⟨alofi_dukes_log_concave N,alofi_dukes_unimodal N⟩

#print axioms compatible_iff
#print axioms mem_recurrentConfigs
#print axioms recurrentConfigs_nodup
#print axioms length_recurrentConfigs
#print axioms coefficient_count
#print axioms alofi_dukes_configurations

end Transposed

/-- Counts on the same unrooted K₃,ₙ. A true flag puts the sink in the part
of size three. A false flag puts it in the part of size n. -/
noncomputable def countBySink (n : ℕ) (sinkOnThree : Bool) (k : ℕ) : ℕ :=
  if sinkOnThree then (recurrentConfigs n k).length else (Transposed.recurrentConfigs (n-1) k).length

/-- Both parts of Conjecture 13 for either placement of the sink on K₃,ₙ. -/
theorem three_vertex_part (n : ℕ) (hn : 2≤n) (sinkOnThree : Bool) :
    (∀ k, k+2≤2*n-2 →
      countBySink n sinkOnThree k * countBySink n sinkOnThree (k+2) ≤
      (countBySink n sinkOnThree (k+1))^2) ∧
    UnimodalOn (countBySink n sinkOnThree) (2*n-2) := by
  cases sinkOnThree with
  | false =>
    have bound : 2*(n-1)=2*n-2 := by omega
    simpa only [countBySink,Bool.false_eq_true,if_false,bound] using
      Transposed.alofi_dukes_configurations (n-1)
  | true => simpa only [countBySink,if_true] using alofi_dukes_configurations n hn

#print axioms three_vertex_part

end ThreeSandpile

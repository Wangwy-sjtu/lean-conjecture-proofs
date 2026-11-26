import SemiRestricted

/-! Spiro–Surya–Zeng, Semi-restricted Rock, Paper, Scissors, Question 23.
The same public-history game, score and minimax value as in Question 22 are
imported from the accompanying unchanged file. -/

namespace SemiRestricted
namespace EulerianLower
open Finset
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Fair sign-walk averaging of a terminal payoff. -/
def walk (f : ℝ → ℝ) : ℕ → ℝ → ℝ
  | 0, s => f s
  | t+1, s => (walk f t (s+1) + walk f t (s-1))/2

private lemma walk_mono {f g : ℝ → ℝ} (h : ∀ s, f s ≤ g s) (t : ℕ) (s : ℝ) :
    walk f t s ≤ walk g t s := by
  induction t generalizing s with
  | zero => exact h s
  | succ t ih => simp only [walk]; linarith [ih (s+1), ih (s-1)]

private lemma walk_combo (f g : ℝ → ℝ) (a b : ℝ) (t : ℕ) (s : ℝ) :
    walk (fun y => a*f y + b*g y) t s = a*walk f t s + b*walk g t s := by
  induction t generalizing s with
  | zero => rfl
  | succ t ih => simp only [walk,ih]; ring

private lemma walk_sq (t : ℕ) (s : ℝ) :
    walk (·^2) t s = s^2+t := by
  induction t generalizing s with
  | zero => simp [walk]
  | succ t ih => simp only [walk,ih,Nat.cast_succ]; ring

private lemma walk_fourth (t : ℕ) (s : ℝ) :
    walk (·^4) t s = s^4 + 6*t*s^2 + 3*(t:ℝ)^2 - 2*t := by
  induction t generalizing s with
  | zero => simp [walk]
  | succ t ih => simp only [walk,ih,Nat.cast_succ]; ring

/-- A uniform, non-asymptotic first absolute moment bound for the simple random walk. -/
theorem fair_walk_lower (t : ℕ) : Real.sqrt t / 2 ≤ walk abs t 0 := by
  by_cases ht : t = 0
  · simp [ht,walk]
  let a := 2*Real.sqrt t
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hp (y : ℝ) : 3*a^2*y^2 + 0*y^2 ≤ y^4 + 2*a^3*|y| := by
    have h := mul_nonneg (mul_nonneg (sq_nonneg (|y|-a)) (by linarith [abs_nonneg y] : 0 ≤ |y|+2*a)) (abs_nonneg y)
    have h2 : |y|^2 = y^2 := sq_abs y
    nlinarith [h,congrArg (fun u : ℝ => u^2) h2,congrArg (fun u : ℝ => a^2*u) h2]
  have h := walk_mono (f:=fun y => (3*a^2)*y^2+0*y^2)
    (g:=fun y => 1*y^4+(2*a^3)*|y|) (fun y => by simpa using hp y) t 0
  rw [walk_combo (·^2) (·^2),walk_combo (·^4) abs,walk_sq,walk_fourth] at h
  have hs := Real.sq_sqrt (Nat.cast_nonneg t)
  have hsp : 0 < Real.sqrt t := Real.sqrt_pos.mpr (by exact_mod_cast Nat.pos_of_ne_zero ht)
  dsimp [a] at h
  set x := Real.sqrt t
  rw [← hs] at h
  apply (mul_le_mul_iff_right₀ (show 0 < 16*x^3 by positivity)).mp
  nlinarith only [h,sq_nonneg x,sq_nonneg (x^2)]

private lemma walk_abs_lipschitz (t : ℕ) (s u : ℝ) :
    |walk abs t s - walk abs t u| ≤ |s-u| := by
  induction t generalizing s u with
  | zero => exact abs_abs_sub_abs_le_abs_sub s u
  | succ t ih =>
    have hp := abs_le.mp (ih (s+1) (u+1))
    have hm := abs_le.mp (ih (s-1) (u-1))
    simp only [show s+1-(u+1)=s-u by ring,show s-1-(u-1)=s-u by ring] at hp hm
    simp only [walk]
    exact abs_le.mpr ⟨by linarith [hp.1,hm.1],by linarith [hp.2,hm.2]⟩

/-- The wager used before the next nonzero signal. -/
def wager : ℕ → ℝ → ℝ
  | 0, _ => 0
  | t+1, s => (walk abs t (s-1) - walk abs t (s+1))/2

private lemma wager_bounds (t : ℕ) (s : ℝ) : |wager t s| ≤ 1 := by
  cases t with
  | zero => norm_num [wager]
  | succ t =>
    have h := walk_abs_lipschitz t (s-1) (s+1)
    rw [show s-1-(s+1) = -2 by ring] at h
    norm_num at h
    rw [wager,abs_div]
    norm_num only [Nat.abs_ofNat,abs_of_pos (by norm_num : (0:ℝ)<2)]
    linarith

private def advance (p : ℕ × ℝ) (y : ℝ) : ℕ × ℝ :=
  if y=0 then p else (p.1-1,p.2+y)

private lemma wager_identity (p : ℕ × ℝ) (y : ℝ) (hy : y=0 ∨ y=1 ∨ y= -1)
    (hp : y ≠ 0 → 0 < p.1) :
    wager p.1 p.2*y + walk abs (advance p y).1 (advance p y).2 = walk abs p.1 p.2 := by
  rcases p with ⟨t,s⟩
  rcases hy with rfl | rfl | rfl
  · simp [advance]
  · cases t with
    | zero => exact False.elim ((Nat.lt_irrefl 0) (hp (by norm_num)))
    | succ k => simp [advance,wager,walk]; ring
  · cases t with
    | zero => exact False.elim ((Nat.lt_irrefl 0) (hp (by norm_num)))
    | succ k => simp [advance,wager,walk,sub_eq_add_neg]; ring

variable {R K C : Type*} [Fintype R] [Nonempty R] [DecidableEq R]

private def weight (a : R) (z : ℝ) (b : R) : ℝ :=
  let d : ℝ := Fintype.card R
  (d-z+(if b=a then d*z else 0))/d^2

private lemma weight_nonneg (a b : R) (z : ℝ) (hz : |z|≤1) : 0 ≤ weight a z b := by
  have hd : 1 ≤ (Fintype.card R:ℝ) := by exact_mod_cast Fintype.card_pos (α:=R)
  unfold weight
  apply div_nonneg _ (sq_nonneg _)
  split_ifs
  · nlinarith [mul_nonneg (sub_nonneg.mpr hd) (by linarith [(abs_le.mp hz).1] : 0≤1+z)]
  · linarith [(abs_le.mp hz).2]

private lemma weight_total (a : R) (z : ℝ) : ∑ b, weight a z b = 1 := by
  have hd : (Fintype.card R:ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero (α:=R)
  simp only [weight,div_eq_mul_inv,← Finset.sum_mul,Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,
    nsmul_eq_mul,Finset.sum_ite_eq',Finset.mem_univ,if_true]
  field_simp
  ring

private lemma weight_pay (A : R → K → ℝ) (a : R) (u : K) (z : ℝ)
    (hc : ∑ b, A b u = 0) :
    ∑ b, weight a z b * A b u = z*A a u/(Fintype.card R:ℝ) := by
  let d : ℝ := Fintype.card R
  have hd : d ≠ 0 := by dsimp [d]; exact_mod_cast Fintype.card_ne_zero (α:=R)
  have term (b : R) : weight a z b*A b u =
      ((d-z)*A b u + (if b=a then d*z*A a u else 0))/d^2 := by
    by_cases h : b=a
    · subst b; simp [weight,d]; ring
    · simp [weight,d,h]; ring
  simp only [term,div_eq_mul_inv,← Finset.sum_mul,Finset.sum_add_distrib,← Finset.mul_sum,hc,mul_zero,
    zero_add,Finset.sum_ite_eq',Finset.mem_univ,if_true]
  change d*z*A a u/d^2 = z*A a u/d
  field_simp

/-- Public signs determine the number of nonzero steps left and the signed total so far. -/
private def historyState (f : K → ℝ) (t₀ : ℕ) : List (R × K) → ℕ × ℝ
  | [] => (t₀,0)
  | (_,u)::h => advance (historyState f t₀ h) (f u)

/-- A public-history mixed response implementing a signed bet on row a. -/
def bettingPolicy (f : K → ℝ) (a : R) (t₀ : ℕ) : Policy R K where
  prob h := let p := historyState f t₀ h; weight a (wager p.1 p.2)
  nonneg _ _ := weight_nonneg _ _ _ (wager_bounds _ _)
  total _ := weight_total _ _

variable [DecidableEq C]

private def remaining (g : C → ℝ) (S : Finset C) : ℕ × ℝ :=
  (∑ x ∈ S, if g x=0 then 0 else 1, -(∑ x ∈ S, g x))

private lemma remaining_erase (g : C → ℝ) (S : Finset C) {x : C} (hx : x ∈ S) :
    advance (remaining g S) (g x) = remaining g (S.erase x) := by
  have he := Finset.sum_erase_add S (fun y => if g y=0 then (0:ℕ) else 1) hx
  have hs := Finset.sum_erase_add S g hx
  by_cases hz : g x=0
  · simp [advance,remaining,hz] at he hs ⊢
    exact ⟨he.symm,by linarith⟩
  · simp [advance,remaining,hz] at he ⊢
    exact ⟨by omega,by linarith⟩

private lemma remaining_pos (g : C → ℝ) (S : Finset C) {x : C} (hx : x ∈ S)
    (hz : g x ≠ 0) : 0 < (remaining g S).1 := by
  have he := Finset.sum_erase_add S (fun y => if g y=0 then (0:ℕ) else 1) hx
  simp only [remaining] at ⊢
  simp [hz] at he
  omega

/-- For this response the expectation equals the walk potential for every legal
dealer, including dealers who react to all prior individual cards and actions. -/
private theorem betting_score (A : R → K → ℝ) (kind : C → K) (a : R)
    (hc : ∀ u, ∑ b, A b u = 0) (hsign : ∀ u, A a u=0 ∨ A a u=1 ∨ A a u= -1)
    (D : DrawPolicy R C) (t₀ : ℕ) :
    ∀ n (S : Finset C), S.card=n → ∀ h : List (R×C),
      historyState (A a) t₀ (h.map fun bx => (bx.1,kind bx.2)) =
        remaining (fun x => A a (kind x)) S →
      score (fun b x => A b (kind x)) (observed kind (bettingPolicy (A a) a t₀)) D n S h =
        (let p := remaining (fun x => A a (kind x)) S; walk abs p.1 p.2/(Fintype.card R:ℝ)) := by
  intro n
  induction n with
  | zero =>
    intro S hn h _
    have he := Finset.card_eq_zero.mp hn
    simp [he,remaining,score,walk]
  | succ n ih =>
    intro S hn h hist
    let g := fun x => A a (kind x)
    let p := remaining g S
    let d : ℝ := Fintype.card R
    let P := observed kind (bettingPolicy (A a) a t₀)
    have hS : S.Nonempty := Finset.card_pos.mp (by omega)
    have hp (b : R) : P.prob h b = weight a (wager p.1 p.2) b := by
      change weight a (wager _ _) b = _
      rw [hist]
    have branch (x : C) (hx : x ∈ S) (b : R) :
        score (fun c y => A c (kind y)) P D n (S.erase x) ((b,x)::h) =
        walk abs (advance p (g x)).1 (advance p (g x)).2/d := by
      have he := remaining_erase g S hx
      have hc' : (S.erase x).card=n := by rw [Finset.card_erase_of_mem hx,hn]; omega
      apply (ih (S.erase x) hc' ((b,x)::h) ?_).trans
      · rw [←he]
      · change advance (historyState (A a) t₀ _) (g x) = remaining g (S.erase x)
        rw [hist]
        exact he
    have col (x : C) (hx : x ∈ S) :
        ∑ b, P.prob h b * (A b (kind x) +
          score (fun c y => A c (kind y)) P D n (S.erase x) ((b,x)::h)) =
        walk abs p.1 p.2/d := by
      simp only [branch x hx,mul_add,Finset.sum_add_distrib,← Finset.sum_mul,P.total,one_mul]
      simp only [hp]
      rw [weight_pay A a (kind x) _ (hc _)]
      have hi := wager_identity p (g x) (hsign _) (remaining_pos g S hx)
      change wager p.1 p.2*g x/d+_ = _
      rw [← add_div,hi]
    change (∑ b, P.prob h b * ∑ x ∈ S, D.prob h S x *
      (A b (kind x) + score (fun c y => A c (kind y)) P D n (S.erase x) ((b,x)::h))) = _
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    calc
      _ = ∑ x ∈ S, D.prob h S x * (∑ b, P.prob h b * (A b (kind x) +
          score (fun c y => A c (kind y)) P D n (S.erase x) ((b,x)::h))) := by
            apply Finset.sum_congr rfl
            intro x _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro b _
            ring
      _ = ∑ x ∈ S, D.prob h S x * (walk abs p.1 p.2/d) :=
        Finset.sum_congr rfl fun x hx => congrArg _ (col x hx)
      _ = _ := by rw [← Finset.sum_mul,D.total h S hS,one_mul]

/-- A balanced observable row can be played for a guaranteed signed-walk
premium, with zero-signal cards free to appear at any adaptive times. -/
theorem balanced_deck (A : R → K → ℝ) (kind : C → K) (a : R) (S : Finset C) (t : ℕ)
    (hc : ∀ u, ∑ b, A b u = 0) (hsign : ∀ u, A a u=0 ∨ A a u=1 ∨ A a u= -1)
    (hbound : ∀ b u, |A b u|≤1) (hbal : ∑ x ∈ S, A a (kind x) = 0)
    (hcount : (∑ x ∈ S, if A a (kind x)=0 then (0:ℕ) else 1) = t) :
    (∀ D : DrawPolicy R C,
      score (fun b x => A b (kind x)) (observed kind (bettingPolicy (A a) a t)) D
        S.card S [] = walk abs t 0/(Fintype.card R:ℝ)) ∧
    Real.sqrt t / (2*(Fintype.card R:ℝ)) ≤ value kind (fun b x => A b (kind x)) S := by
  let pay := fun b x => A b (kind x)
  have start : remaining (fun x => A a (kind x)) S = (t,0) := by simp [remaining,hbal,hcount]
  have eq (D : DrawPolicy R C) := betting_score A kind a hc hsign D t S.card S rfl [] (by
    change (t,0) = _
    exact start.symm)
  simp only [start] at eq
  refine ⟨eq,?_⟩
  have hab (b : R) : avg S (pay b) ≤ 1 := by
    have hsum : ∑ x ∈ S, pay b x ≤ (S.card:ℝ) := by
      simpa using Finset.sum_le_sum (s:=S) fun x _ => (abs_le.mp (hbound b (kind x))).2
    exact (div_le_div_of_nonneg_right hsum (Nat.cast_nonneg _)).trans (div_self_le_one _)
  have ne : (attainable kind pay S).Nonempty := by
    refine ⟨(S.card:ℝ)*1+15*(Fintype.card R:ℝ)*Real.sqrt S.card,uniform R C,?_⟩
    intro P
    exact uniformly_shuffled_score_le pay S (observed kind P) (fun b x _=>hbound b (kind x)) 1 hab []
  apply le_csInf ne
  rintro b ⟨D,h⟩
  have H := h (bettingPolicy (A a) a t)
  change score (fun b x => A b (kind x)) _ D S.card S [] ≤ b at H
  rw [eq D] at H
  rw [← div_div]
  exact (div_le_div_of_nonneg_right (fair_walk_lower t) (Nat.cast_nonneg _)).trans H

section Digraph
variable {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]

/-- Equal indegree and outdegree at every vertex. Components may be disconnected. -/
def BalancedDegrees (D : V → V → Prop) : Prop :=
  ∀ v, (univ.filter (D v)).card = (univ.filter (fun u => D u v)).card

omit [Nonempty V] [DecidableEq V] in
private lemma row_zero (D : V → V → Prop) (hE : BalancedDegrees D) (a : V) :
    ∑ u, arcPay D a u = 0 := by
  have cells (p : V → Prop) : (∑ u : V, if p u then (1:ℝ) else 0) =
      ((univ.filter p).card:ℝ) := by
    rw [← Finset.sum_filter]
    simp
  simp only [arcPay,Finset.sum_sub_distrib,cells,hE a,sub_self]

omit [Nonempty V] [DecidableEq V] in
private lemma column_zero (D : V → V → Prop) (hE : BalancedDegrees D) (u : V) :
    ∑ b, arcPay D b u = 0 := by
  have flip (b : V) : arcPay D b u = -arcPay D u b := by unfold arcPay; ring
  simp only [flip,Finset.sum_neg_distrib,row_zero D hE,neg_zero]

/-- Question 23, with positive explicit constants on both sides for every
finite Eulerian oriented graph with at least one arc and every integer quota. -/
theorem question23 (D : V → V → Prop) (hE : BalancedDegrees D)
    (hor : ∀ a u, D a u → ¬D u a) (hedge : ∃ a u, D a u) (n : ℕ) :
    Real.sqrt n / (2*(Fintype.card V:ℝ)) ≤ digraphValue D (fun _ => n) ∧
      digraphValue D (fun _ => n) ≤
        (15*(Fintype.card V:ℝ)*Real.sqrt (Fintype.card V))*Real.sqrt n := by
  obtain ⟨a,u,hau⟩ := hedge
  let g := arcPay D a
  let m : ℕ := ∑ v, if g v=0 then 0 else 1
  have hgu : g u = 1 := by simp [g,arcPay,hau,hor _ _ hau]
  have mh : 1 ≤ m := by
    have H := Finset.single_le_sum (f:=fun v => if g v=0 then (0:ℕ) else 1)
      (fun i _ => Nat.zero_le _) (Finset.mem_univ u)
    simpa [m,hgu] using H
  let r : V → ℕ := fun _ => n
  have bal : (∑ x : Card r, arcPay D a x.1) = 0 := by
    rw [Fintype.sum_sigma]
    simp [r,← Finset.mul_sum,row_zero D hE]
  have count : (∑ x : Card r, if arcPay D a x.1=0 then (0:ℕ) else 1) = n*m := by
    rw [Fintype.sum_sigma]
    simp [m,g,r,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v _
    by_cases h : arcPay D a v=0 <;> simp [h]
  have sig (b v : V) : arcPay D b v=0 ∨ arcPay D b v=1 ∨ arcPay D b v= -1 := by
    unfold arcPay
    split_ifs <;> norm_num
  have bound (b v : V) : |arcPay D b v|≤1 := by
    rcases sig b v with h|h|h <;> rw [h] <;> norm_num
  have H := (balanced_deck (arcPay D) Sigma.fst a (univ : Finset (Card r))
    (n*m) (column_zero D hE) (sig a) bound bal count).2
  have hm : n ≤ n*m := by simpa using Nat.mul_le_mul_left n mh
  have low := Real.sqrt_le_sqrt (show (n:ℝ) ≤ ↑(n*m) by exact_mod_cast hm)
  have zeroBase : fixedScore D r = 0 := by
    have eqZero (v : V) : (∑ u ∈ univ.filter (D v), (r u:ℝ)) -
        (∑ u ∈ univ.filter (fun u => D u v), (r u:ℝ)) = 0 := by simp [r,hE v]
    simp [fixedScore,eqZero]
  have upper := (question22 D r n (fun _ => le_refl _)).2
  rw [zeroBase,zero_add] at upper
  exact ⟨(div_le_div_of_nonneg_right low (by positivity)).trans H,upper⟩

end Digraph

#print axioms fair_walk_lower
#print axioms balanced_deck
#print axioms question23

end
end EulerianLower
end SemiRestricted

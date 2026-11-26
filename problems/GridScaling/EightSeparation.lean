import EightSeeds
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Real.Basic

/-! No single real polynomial agrees eventually with the optimal press count
across all nullity-eight square boards. -/
namespace EightSeparation
open LightsGrid LightsPolynomial GridClicks GridScaling Polynomial
open scoped Polynomial
noncomputable section

private theorem unique_cost {n M N : ℕ} (h : IsMostClicks n M) (g : IsMostClicks n N) : M=N := by
  have bound {L U : ℕ} (low : IsMostClicks n L) (high : IsMostClicks n U) : L≤U := by
    obtain ⟨a,sol,hard⟩ := low.2
    obtain ⟨x,hx,bx⟩ := high.1 a sol
    exact (hard x hx).trans bx
  exact le_antisymm (bound h g) (bound g h)

private def shape (a h D : ℕ) : ℝ[X] :=
  X^2-C ((h:ℝ)/(a:ℝ)^2/2)*(X+1)^2-C ((D:ℝ)/2)

private theorem identifies (m b K₀ : ℕ) (b1 : 1<b) (odd : Odd b)
    (base : Module.finrank F (quietSpace m)=8)
    (tower : ∀ k,Module.finrank F (quietSpace ((m+1)*b^k-1))=8)
    (p : ℝ[X]) (model : ∀ n≥K₀,Module.finrank F (quietSpace n)=8 →
      ∃ M, IsMostClicks n M ∧ p.eval (n:ℝ)=(M:ℝ)) :
    ∃ D, p=shape (m+1) (activeCount m) D := by
  obtain ⟨k,D,S⟩ := eventual_quadratic m
  let j₀ := k+K₀+1
  let q (j : ℕ) := b^(j+j₀)
  let n (j : ℕ) := (m+1)*q j-1
  have positive (j : ℕ) : 0<q j := by dsimp [q];positivity
  have recover (j : ℕ) : n j+1=(m+1)*q j :=
    Nat.sub_add_cancel (Nat.mul_pos (by omega) (positive j))
  have grow (t : ℕ) : t+1≤b^t := by
    induction t with
    | zero => simp
    | succ t ih =>
      rw [pow_succ]
      have h := Nat.mul_le_mul (by omega : t+1≤b^t) (by omega : 2≤b)
      omega
  have mono : StrictMono n := strictMono_nat_of_lt_succ (fun j => by
    have changeq : q j<q (j+1) := Nat.pow_lt_pow_right b1 (by omega : j+j₀<j+1+j₀)
    have h := Nat.mul_lt_mul_of_pos_left changeq (by omega : 0<m+1)
    have h1 := recover j
    have h2 := recover (j+1)
    omega)
  let points (j : ℕ) : ℝ := n j
  have inj : Function.Injective points := by
    intro i j eq
    change (n i:ℝ)=(n j:ℝ) at eq
    exact mono.injective (by exact_mod_cast eq)
  refine ⟨D,Polynomial.eq_of_infinite_eval_eq _ _ ((Set.infinite_range_of_injective inj).mono ?_)⟩
  rintro _ ⟨j,rfl⟩
  have g : j+j₀+1≤q j := grow _
  have nq : q j≤n j+1 := (recover j).symm ▸ Nat.le_mul_of_pos_left _ (by omega)
  have kq : k≤q j := by dsimp [j₀] at g;omega
  have kn : K₀≤n j := by dsimp [j₀] at g;omega
  have dim : Module.finrank F (quietSpace (n j))=8 := tower _
  obtain ⟨M,act,ev⟩ := model (n j) kn dim
  obtain ⟨N,act',_,low⟩ := S (q j) (positive j) (dim.trans base.symm)
  have MN := unique_cost act act'
  have cc := low (odd.pow) kq
  change 2*N+(q j)^2*activeCount m+D=2*(n j)^2 at cc
  rw [← MN] at cc
  have real : 2*(M:ℝ)+(q j:ℝ)^2*(activeCount m:ℝ)+(D:ℝ)=2*(n j:ℝ)^2 := by exact_mod_cast cc
  have rq : (n j:ℝ)+1=((m:ℝ)+1)*(q j:ℝ) := by exact_mod_cast recover j
  have den : (m:ℝ)+1≠0 := by positivity
  change p.eval (n j:ℝ)=(shape (m+1) (activeCount m) D).eval (n j:ℝ)
  rw [ev]
  simp only [shape,eval_sub,eval_pow,eval_X,eval_mul,eval_C,eval_add,eval_one,Nat.cast_add_one]
  have term : ((activeCount m:ℝ)/((m:ℝ)+1)^2/2)*((n j:ℝ)+1)^2=
      (q j:ℝ)^2*(activeCount m:ℝ)/2 := by rw [rq,mul_pow];field_simp
  rw [term]
  linarith

/-- Even after discarding an arbitrary initial segment, no real polynomial in
the side length gives the worst solvable press count on all nullity-eight squares. -/
theorem no_polynomial :
    ¬ ∃ (p : ℝ[X]) (K : ℕ),∀ n≥K,Module.finrank F (quietSpace n)=8 →
      ∃ M, IsMostClicks n M ∧ p.eval (n:ℝ)=(M:ℝ) := by
  rintro ⟨p,K,rule⟩
  obtain ⟨u,h⟩ := identifies 9 5 K (by decide) (by decide) EightSeeds.base9 EightSeeds.family10 p rule
  obtain ⟨v,g⟩ := identifies 16 17 K (by decide) (by decide) EightSeeds.base16 EightSeeds.family17 p rule
  rw [EightSeeds.active9] at h
  rw [EightSeeds.active16] at g
  have eq := h.symm.trans g
  have first := congrArg (Polynomial.eval (-1:ℝ)) eq
  have second := congrArg (Polynomial.eval (0:ℝ)) eq
  norm_num [shape] at first second
  linarith

#print axioms no_polynomial
end
end EightSeparation

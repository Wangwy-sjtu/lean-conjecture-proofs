import OddStabilization
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-! A common modulus selects a seed square for every board of a fixed nullity. -/
namespace FiniteSeeds
open LightsGrid LightsPolynomial GridGcd OddStabilization Polynomial
open scoped BigOperators Polynomial CharTwo
noncomputable section

/-- Shifting a pair of Fibonacci polynomials backwards preserves the determinant
of adjacent recurrence states, since the coefficient field has characteristic two. -/
private theorem back (x : P) (n k : ℕ) :
    fib x (n+k)*fib x (k+1)+fib x (n+k+1)*fib x k=fib x n := by
  induction k with
  | zero => simp [fib]
  | succ k ih =>
    change fib x (n+k+1)*fib x (k+2)+fib x (n+k+2)*fib x (k+1)=_
    rw [show fib x (k+2)=x*fib x (k+1)+fib x k by rfl,
      show fib x (n+k+2)=x*fib x (n+k+1)+fib x (n+k) by rfl]
    calc
      _ = (fib x (n+k)*fib x (k+1)+fib x (n+k+1)*fib x k)+
        ((fib x (n+k+1)*x*fib x (k+1))+(fib x (n+k+1)*x*fib x (k+1))) := by ring
      _ = _ := by rw [CharTwo.add_self_eq_zero,add_zero,ih]

private theorem addition (x : P) (k n : ℕ) :
    fib x (k+(n+1))=fib x (k+1)*fib x (n+1)+fib x k*fib x n := by
  induction n using Nat.twoStepInduction with
  | zero => simp [fib]
  | one => change x*fib x (k+1)+fib x k=fib x (k+1)*(x*1+0)+fib x k*1;ring
  | more n h0 h1 =>
    change x*fib x (k+(n+2))+fib x (k+(n+1))=
      fib x (k+1)*(x*fib x (n+2)+fib x (n+1))+fib x k*(x*fib x (n+1)+fib x n)
    rw [h1,h0];ring

private def Good (p : P) (n : ℕ) := p∣fib X n ∧ p∣fib (X+1) n

private theorem good_add {p : P} {a b : ℕ} (ha : Good p a) (hb : Good p b) : Good p (a+b) := by
  cases b with
  | zero => exact ha
  | succ b =>
    exact ⟨addition X a b ▸ dvd_add (dvd_mul_of_dvd_right hb.1 _) (dvd_mul_of_dvd_left ha.1 _),
      addition (X+1) a b ▸ dvd_add (dvd_mul_of_dvd_right hb.2 _) (dvd_mul_of_dvd_left ha.2 _)⟩

private theorem good_multiple {p : P} {a b : ℕ} (good : Good p a) (dv : a∣b) : Good p b := by
  obtain ⟨z,rfl⟩ := dv
  induction z with
  | zero => exact ⟨dvd_zero _,dvd_zero _⟩
  | succ z ih => rw [Nat.mul_succ];exact good_add ih good

private theorem good_back {p : P} {a b : ℕ} (ha : Good p a) (hb : Good p (b+a)) : Good p b := by
  have go (x : P) (one : p∣fib x a) (two : p∣fib x (b+a)) : p∣fib x b := by
    rw [← back x b a]
    exact dvd_add (dvd_mul_of_dvd_left two _) (dvd_mul_of_dvd_right one _)
  exact ⟨go _ ha.1 hb.1,go _ ha.2 hb.2⟩

private def rank (p : P) : ℕ := by
  classical
  exact if h : ∃ n,0<n ∧ Good p n then Nat.find h else 1

private theorem rank_pos (p : P) : 0<rank p := by
  classical
  unfold rank
  split <;> rename_i h
  · exact (Nat.find_spec h).1
  · decide

private theorem rank_spec {p : P} {N : ℕ} (pos : 0<N) (g : Good p N) :
    Good p (rank p) ∧ rank p≤N := by
  classical
  have h : ∃ n,0<n ∧ Good p n := ⟨N,pos,g⟩
  simp only [rank,dif_pos h]
  exact ⟨(Nat.find_spec h).2,Nat.find_min' h ⟨pos,g⟩⟩

private theorem rank_dvd (p : P) : ∀ N, Good p N → rank p∣N := by
  intro N
  induction N using Nat.strong_induction_on with
  | h N ih =>
    intro g
    by_cases z : N=0
    · rw [z];exact dvd_zero _
    have pos : 0<N := by omega
    obtain ⟨gr,le⟩ := rank_spec pos g
    have rp := rank_pos p
    have eq : N-rank p+rank p=N := Nat.sub_add_cancel le
    have gd : Good p (N-rank p) := good_back gr (eq.symm ▸ g)
    have dv := ih (N-rank p) (by omega) gd
    rw [← eq]
    exact dvd_add dv (dvd_refl _)

private abbrev Bounded (d : ℕ) := {p : P // p.natDegree≤d}

private noncomputable instance boundedFintype (d : ℕ) : Fintype (Bounded d) := by
  let f := fun (p : Bounded d) (i : Fin (d+1)) => p.val.coeff i.val
  have inj : Function.Injective f := by
    intro p q h
    apply Subtype.ext
    ext n
    by_cases small : n<d+1
    · exact congrFun h ⟨n,small⟩
    · rw [coeff_eq_zero_of_natDegree_lt (by have := p.property;omega),
        coeff_eq_zero_of_natDegree_lt (by have := q.property;omega)]
  exact Fintype.ofInjective f inj

/-- One modulus for every board whose nullity is at most d. -/
def modulus (d : ℕ) := ∏ p : Bounded d,rank p.val

theorem modulus_pos (d : ℕ) : 0<modulus d :=
  Finset.prod_pos (fun p _ => rank_pos p.val)

private theorem good_gcd (a : ℕ) : Good (common a) a :=
  ⟨EuclideanDomain.gcd_dvd_left ..,EuclideanDomain.gcd_dvd_right ..⟩

/-- For a square whose physical nullity is at most d, replacing its index n+1
by its gcd with the single fixed modulus preserves the entire common divisor
up to a unit, and hence the physical nullity. -/
theorem reduce (d N : ℕ) (pos : 0<N) (bounded : Module.finrank F (quietSpace (N-1))≤d) :
    Module.finrank F (quietSpace (N.gcd (modulus d)-1))=Module.finrank F (quietSpace (N-1)) := by
  let g := common N
  let a := N.gcd (modulus d)
  have gp : 0<a := Nat.gcd_pos_of_pos_left _ pos
  have deg : g.natDegree≤d := (physical _ pos) ▸ bounded
  let w : Bounded d := ⟨g,deg⟩
  have gl : rank g∣modulus d := Finset.dvd_prod_of_mem (fun p : Bounded d => rank p.val)
    (Finset.mem_univ w)
  have ra : rank g∣a := Nat.dvd_gcd (rank_dvd g N (good_gcd N)) gl
  have h := good_multiple (rank_spec pos (good_gcd N)).1 ra
  have up : g∣common a := EuclideanDomain.dvd_gcd h.1 h.2
  have h' := good_multiple (good_gcd a) (Nat.gcd_dvd_left N (modulus d))
  have down : common a∣g := EuclideanDomain.dvd_gcd h'.1 h'.2
  rw [physical _ gp,physical _ pos]
  exact natDegree_eq_of_degree_eq (degree_eq_degree_of_associated (associated_of_dvd_dvd down up))

#print axioms reduce
end
end FiniteSeeds

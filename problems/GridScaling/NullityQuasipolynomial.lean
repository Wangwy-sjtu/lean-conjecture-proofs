import FiniteSeeds
import GridScaling

/-! On all square boards of bounded nullity, one finite residue table of
quadratics gives the worst solvable press count after an initial finite range. -/
namespace NullityQuasipolynomial
open LightsPolynomial LightsGrid GridClicks GridScaling FiniteSeeds
noncomputable section

private theorem as_quadratic (a Q H e n M : ℕ) (ap : 0<a)
    (factor : n+1=a*Q) (counts : 2*M+Q^2*H+e=2*n^2) :
    (M:ℚ)=(n:ℚ)^2-((H:ℚ)/(a:ℚ)^2/2)*((n:ℚ)+1)^2-(e:ℚ)/2 := by
  have eq : (n:ℚ)+1=(a:ℚ)*(Q:ℚ) := by exact_mod_cast factor
  have c : 2*(M:ℚ)+(Q:ℚ)^2*(H:ℚ)+(e:ℚ)=2*(n:ℚ)^2 := by exact_mod_cast counts
  have nz : (a:ℚ)≠0 := by exact_mod_cast ap.ne'
  have t : ((H:ℚ)/(a:ℚ)^2/2)*((n:ℚ)+1)^2=(Q:ℚ)^2*(H:ℚ)/2 := by
    rw [eq,mul_pow];field_simp
  rw [t]
  linarith

private theorem residue (d : ℕ) (r : Fin (2*modulus d)) :
    ∃ K : ℕ,∃ A C : ℚ, ∀ n : ℕ,K≤n → (n+1)%(2*modulus d)=r.val →
    Module.finrank F (quietSpace n)≤d →
    ∃ M, IsMostClicks n M ∧ (M:ℚ)=(n:ℚ)^2-A*((n:ℚ)+1)^2-C := by
  let L := modulus d
  let a := r.val.gcd L
  have ap : 0<a := Nat.gcd_pos_of_pos_right _ (modulus_pos d)
  let m := a-1
  have seed : m+1=a := by dsimp [m];omega
  obtain ⟨u,ru⟩ := Nat.gcd_dvd_left r.val L
  obtain ⟨v,lv⟩ := Nat.gcd_dvd_right r.val L
  change r.val=a*u at ru
  change L=a*v at lv
  obtain ⟨k,D,stable⟩ := eventual_quadratic m
  let e := if Even u then 0 else D
  refine ⟨a*k,(activeCount m:ℚ)/(a:ℚ)^2/2,(e:ℚ)/2,?_⟩
  intro n large rem dim
  let j := (n+1)/(2*L)
  let Q := u+2*v*j
  have decomp : r.val+(2*L)*j=n+1 := by
    have z := Nat.mod_add_div (n+1) (2*L)
    change (n+1)%(2*L)=r.val at rem
    rwa [rem] at z
  have factor : n+1=a*Q := by rw [← decomp,ru,lv];dsimp only [Q];ring
  have gp : (n+1).gcd L=a := by
    have h : n+1=r.val+L*(2*j) := by rw [← decomp];ring
    rw [h,Nat.gcd_add_mul_left_left]
  have qp : 0<Q := by
    by_contra! z
    have zero : Q=0 := by omega
    rw [zero,Nat.mul_zero] at factor;omega
  have size : (m+1)*Q-1=n := by rw [seed,← factor];omega
  have same := reduce d (n+1) (by omega) (by simpa using dim)
  change Module.finrank F (quietSpace ((n+1).gcd L-1))=
    Module.finrank F (quietSpace (n+1-1)) at same
  rw [gp,Nat.add_sub_cancel] at same
  have S := stable Q qp
  dsimp only at S
  rw [size] at S
  obtain ⟨M,actual,ev,od⟩ := S same.symm
  refine ⟨M,actual,as_quadratic a Q _ e n M ap factor ?_⟩
  have parity : Q%2=u%2 := by dsimp [Q];rw [Nat.mul_assoc];omega
  by_cases even : Even u
  · have good : Even Q := Nat.even_iff.mpr (parity.trans (Nat.even_iff.mp even))
    simpa [e,even] using ev good
  · have good : Odd Q := Nat.odd_iff.mpr (by have z := mt Nat.even_iff.mpr even;omega)
    have small : k≤Q := by
      apply Nat.le_of_mul_le_mul_left _ ap
      rw [← factor]
      omega
    simpa [e,even] using od good small

/-- For every upper bound on the nullity, there is one period, one global
threshold, and rational coefficients for each residue class of n+1. They work
simultaneously for every physical square with that bound on its nullity. -/
theorem on_bounded_nullity (d : ℕ) :
    ∃ P : ℕ,∃ pos : 0<P,∃ K : ℕ,∃ A C : Fin P → ℚ,
    ∀ n : ℕ, K≤n → Module.finrank F (quietSpace n)≤d →
    let i : Fin P := ⟨(n+1)%P,Nat.mod_lt _ pos⟩
    ∃ M, IsMostClicks n M ∧ (M:ℚ)=(n:ℚ)^2-A i*((n:ℚ)+1)^2-C i := by
  classical
  let P := 2*modulus d
  have pp : 0<P := Nat.mul_pos (by decide) (modulus_pos d)
  choose K A C prop using residue d
  refine ⟨P,pp,Finset.univ.sup K,A,C,?_⟩
  intro n large dim
  let i : Fin P := ⟨(n+1)%P,Nat.mod_lt _ pp⟩
  exact prop i n ((Finset.le_sup (f:=K) (Finset.mem_univ i)).trans large) rfl dim

#print axioms on_bounded_nullity
end
end NullityQuasipolynomial

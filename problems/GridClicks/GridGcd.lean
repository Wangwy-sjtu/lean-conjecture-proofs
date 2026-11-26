import LightsGrid
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! The square-grid kernel is dual to the quotient by its two boundary polynomials. -/

namespace GridGcd
open Polynomial LightsGrid LightsPolynomial
open scoped Polynomial CharTwo
noncomputable section

def common (N : ℕ) : P := EuclideanDomain.gcd (fib X N) (fib (X+1) N)
private abbrev Q (n : ℕ) := AdjoinRoot (common (n+1))
private abbrev mk (n : ℕ) := AdjoinRoot.mk (common (n+1))
private abbrev D (n : ℕ) := Module.Dual F (Q n)

private def sample {n : ℕ} (L : D n) (p : P) : Row n :=
  fun j => L (mk n (p*fib X (j.val+1)))

private theorem sample_read {n : ℕ} (L : D n) (p : P) (j : ℕ) (bound : j≤n+1) :
    LightsGrid.read (sample L p) j=L (mk n (p*fib X j)) := by
  cases j with
  | zero => simp [LightsGrid.read,fib]
  | succ j =>
    by_cases h : j<n
    · simp [LightsGrid.read,h,sample]
    · have eq : j=n := by omega
      subst j
      have endzero : mk n (fib X (n+1))=0 :=
        AdjoinRoot.mk_eq_zero.mpr (EuclideanDomain.gcd_dvd_left ..)
      simp [map_mul,endzero]

private theorem sample_add {n : ℕ} (L : D n) (p q : P) :
    sample L (p+q)=sample L p+sample L q := by
  funext j; simp [sample,add_mul]

private theorem sample_step {n : ℕ} (L : D n) (p : P) :
    sample L (X*p) = path n (sample L p) := by
  funext j
  change _=LightsGrid.read (sample L p) j.val+LightsGrid.read (sample L p) (j.val+2)
  rw [sample_read L p _ (by omega),sample_read L p _ (by omega),← L.map_add,← map_add]
  change L (mk n ((X*p)*fib X (j.val+1))) = _
  congr 2
  rw [fib]
  linear_combination -p*(CharTwo.add_self_eq_zero (fib (X:P) j.val))

private theorem sample_eval {n : ℕ} (L : D n) (p : P) :
    sample L p=aeval (path n) p (sample L 1) := by
  induction p using Polynomial.induction_on with
  | C c =>
    funext j
    rw [aeval_C]
    change L (mk n (C c * fib X (j.val+1)))=c • L (mk n (1*fib X (j.val+1)))
    rw [one_mul,← L.map_smul]
    congr 1
    rw [← Polynomial.smul_eq_C_mul]
    exact ((AdjoinRoot.mkₐ (common (n+1))).toLinearMap.map_smul c (fib X (j.val+1)))
  | add p q hp hq => rw [sample_add,hp,hq,map_add]; rfl
  | monomial j c ih =>
    rw [show C c*X^(j+1)=(X:P)*(C c*X^j) by ring,sample_step,ih,map_mul (aeval (path n)) X _,aeval_X]
    rfl

private def pattern {n : ℕ} (L : D n) : Board n :=
  fun i => sample L (fib (X+1) (i.val+1))

private theorem pattern_read {n : ℕ} (L : D n) (i : ℕ) (bound : i≤n+1) :
    LightsGrid.read (pattern L) i=sample L (fib (X+1) i) := by
  cases i with
  | zero => funext j; simp [LightsGrid.read,sample,fib]
  | succ i =>
    by_cases h : i<n
    · simp [LightsGrid.read,h,pattern]
    · have eq : i=n := by omega
      subst i
      have endzero : mk n (fib (X+1) (n+1))=0 :=
        AdjoinRoot.mk_eq_zero.mpr (EuclideanDomain.gcd_dvd_right ..)
      funext j; simp [sample,map_mul,endzero]

private theorem pattern_quiet {n : ℕ} (L : D n) : pattern L∈quietSpace n := by
  intro i
  rw [pattern_read L _ (by omega),pattern_read L _ (by omega)]
  change sample L (fib (X+1) (i.val+2)) =
    (path n+1) (sample L (fib (X+1) (i.val+1)))+_
  rw [fib,add_mul,one_mul,sample_add,sample_add,sample_step]
  rfl

private def synth (n : ℕ) : D n →ₗ[F] quietSpace n where
  toFun L := ⟨pattern L,pattern_quiet L⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def probe {n : ℕ} (pos : 0<n) (v : Row n) : P →ₗ[F] F :=
  (LinearMap.proj (⟨0,pos⟩ : Fin n)).comp
    ((LinearMap.applyₗ v).comp (aeval (path n)).toLinearMap)

private theorem vanishing {n : ℕ} (pos : 0<n) (b : quietSpace n) :
    aeval (path n) (common (n+1)) (LightsGrid.read b.val 1)=0 := by
  let v := LightsGrid.read b.val 1
  have p0 := path_annihilates pos v
  have p1 : fib (path n+1) (n+1) v=0 :=
    (chase b.val b.property (n+1) (le_refl _)).symm.trans (read_end b.val)
  let e : P →+* Module.End F (Row n) := (aeval (path n)).toRingHom
  have evalX : e X = path n := aeval_X _
  have z0 : e (fib X (n+1)) v = 0 := by rw [map_fib,evalX]; exact p0
  have z1 : e (fib (X+1) (n+1)) v=0 := by rw [map_fib,map_add,evalX,map_one]; exact p1
  let p := fib (X:P) (n+1)
  let q := fib (X+1:P) (n+1)
  have h : common (n+1) = EuclideanDomain.gcdA p q*p+EuclideanDomain.gcdB p q*q := by
    rw [mul_comm _ p,mul_comm _ q]; exact EuclideanDomain.gcd_eq_gcd_ab .. 
  change e (common (n+1)) v=0
  rw [h,map_add,map_mul,map_mul]
  change e _ (e p v) + e _ (e q v) = 0
  simp only [p,q,z0,z1,map_zero,add_zero]

private def analysisFn {n : ℕ} (pos : 0<n) (b : quietSpace n) : D n :=
  ((Ideal.span {common (n+1)} : Ideal P).restrictScalars F).liftQ
    (probe pos (LightsGrid.read b.val 1)) (by
      intro p hp
      obtain ⟨s,h⟩ := Ideal.mem_span_singleton.mp (show p∈(Ideal.span {common (n+1)} : Ideal P) from hp)
      change aeval (path n) p (LightsGrid.read b.val 1) ⟨0,pos⟩=0
      rw [h,mul_comm,map_mul]
      change aeval (path n) s (aeval (path n) (common (n+1)) (LightsGrid.read b.val 1)) _=0
      rw [vanishing pos b,map_zero]; rfl)

private theorem analyse_mk {n : ℕ} (pos : 0<n) (b : quietSpace n) (p : P) :
    analysisFn pos b (mk n p)=aeval (path n) p (LightsGrid.read b.val 1) ⟨0,pos⟩ := rfl

/-- The coordinate functional sends a path polynomial to the first entry it
produces on the top row. The inverse propagates the two path recurrences. -/
theorem kernel_equiv {n : ℕ} (pos : 0<n) : Nonempty (quietSpace n ≃ₗ[F] D n) := by
  have left (L : D n) : analysisFn pos (synth n L)=L := by
    ext z
    obtain ⟨p,rfl⟩ := AdjoinRoot.mk_surjective z
    rw [analyse_mk]
    change aeval (path n) p (LightsGrid.read (pattern L) 1) _=_
    rw [pattern_read L 1 (by omega),show fib (X+1:P) 1=1 by rfl,← sample_eval]
    simp [sample,fib]
  have right (b : quietSpace n) : synth n (analysisFn pos b)=b := by
    apply Subtype.ext
    funext i j
    change analysisFn pos b (mk n (fib (X+1) (i.val+1)*fib X (j.val+1)))=b.val i j
    rw [analyse_mk,mul_comm,map_mul]
    let e : P →+* Module.End F (Row n) := (aeval (path n)).toRingHom
    have ex : e X=path n := aeval_X _
    change e (fib X (j.val+1)) (e (fib (X+1) (i.val+1)) (LightsGrid.read b.val 1)) _=_
    rw [map_fib,map_fib,map_add,map_one,ex,first_fib pos _ _ (by omega),read_cell]
    have h := chase b.val b.property (i.val+1) (by omega)
    rw [read_cell] at h
    exact congrFun h.symm j
  exact ⟨(LinearEquiv.ofBijective (synth n)
    ⟨fun L M eq => by simpa [left] using congrArg (analysisFn pos) eq,
      fun b => ⟨_,right b⟩⟩).symm⟩

/-- Sutner's polynomial formula, derived here from the physical five-cell rule. -/
theorem nullity_from_gcd {n : ℕ} (pos : 0<n) :
    Module.finrank F (quietSpace n) = (common (n+1)).natDegree := by
  obtain ⟨e⟩ := kernel_equiv pos
  exact e.finrank_eq.trans (Subspace.dual_finrank_eq.trans finrank_quotient_span_eq_natDegree)

#print axioms nullity_from_gcd
end
end GridGcd

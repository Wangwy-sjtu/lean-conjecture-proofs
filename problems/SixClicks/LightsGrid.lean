import LightsPolynomial
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Order.Preorder.Finite

/-! The physical square grid, with four-neighbor toggles and zero boundary. -/

namespace LightsGrid
open LightsPolynomial Polynomial
open scoped CharTwo
noncomputable section

abbrev Row (n : ℕ) := Fin n → F
abbrev Board (n : ℕ) := Fin n → Row n

/-- One-based coordinates. The two exterior coordinates have value zero. -/
def read {M : Type*} [Zero M] {n : ℕ} (v : Fin n → M) : ℕ → M
  | 0 => 0
  | j+1 => if h : j<n then v ⟨j,h⟩ else 0

@[simp] theorem read_cell {M : Type*} [Zero M] {n : ℕ} (v : Fin n → M)
    (i : Fin n) : read v (i.val+1)=v i := by simp [read,i.isLt]

@[simp] theorem read_end {M : Type*} [Zero M] {n : ℕ} (v : Fin n → M) :
    read v (n+1)=0 := by simp [read]

@[simp] private theorem read_add {M : Type*} [AddMonoid M] {n : ℕ} (x y : Fin n → M) (j : ℕ) :
    read (x+y) j=read x j+read y j := by
  cases j with
  | zero => simp [read]
  | succ j => by_cases h : j<n <;> simp [read,h]

@[simp] private theorem read_smul {M : Type*} [AddCommMonoid M] [Module F M] {n : ℕ}
    (c : F) (x : Fin n → M) (j : ℕ) : read (c • x) j=c • read x j := by
  cases j with
  | zero => simp [read]
  | succ j => by_cases h : j<n <;> simp [read,h]

@[simp] private theorem read_zero {M : Type*} [Zero M] {n : ℕ} (j : ℕ) :
    read (0 : Fin n → M) j=0 := by cases j <;> simp [read]

/-- Adjacency operator of a path, with its actual two neighbor entries. -/
def path (n : ℕ) : Module.End F (Row n) where
  toFun v i := read v i.val + read v (i.val+2)
  map_add' v w := by ext i; simp; abel
  map_smul' c v := by ext i; simp [mul_add]

private theorem commutes {R : Type*} [Semiring R] {a t : R} (c : Commute a t) (j : ℕ) :
    Commute a (fib t j) := by
  induction j using Nat.twoStepInduction with
  | zero => exact Commute.zero_right a
  | one => exact Commute.one_right a
  | more j prev next => exact (c.mul_right next).add_right prev

/-- Looking at the first cell after applying the j-th path polynomial reads
the original j-th entry. This also gives zero at the far boundary. -/
theorem first_fib {n : ℕ} (positive : 0<n) (v : Row n) (j : ℕ) (bound : j≤n+1) :
    (fib (path n) j v) ⟨0,positive⟩ = read v j := by
  induction j using Nat.twoStepInduction generalizing v with
  | zero => rfl
  | one => simp [fib,read,positive]
  | more j left right =>
    have inside : j<n := by omega
    rw [fib,(commutes (Commute.refl (path n)) (j+1)).eq]
    change (fib (path n) (j+1) ((path n) v)) _ + (fib (path n) j v) _ = _
    rw [right _ (by omega),left _ (by omega)]
    have nbr : read ((path n) v) (j+1)=read v j+read v (j+2) := by
      simp only [read,inside,dif_pos]; rfl
    rw [nbr,add_comm (read v j) _,CharTwo.add_cancel_right]

theorem path_annihilates {n : ℕ} (positive : 0<n) (v : Row n) :
    fib (path n) (n+1) v=0 := by
  funext i
  have c := commutes (commutes (Commute.refl (path n)) (i.val+1)).symm (n+1)
  have e := congrArg (fun f : Module.End F (Row n) => f v ⟨0,positive⟩) c.eq
  change (fib (path n) (i.val+1) (fib (path n) (n+1) v)) _ =
    (fib (path n) (n+1) (fib (path n) (i.val+1) v)) _ at e
  rw [first_fib positive _ _ (by omega),first_fib positive _ _ (by omega),
      read_cell,read_end] at e
  exact e

/-- A quiet board is a press pattern whose five contributions at each cell
sum to zero. The equation solves for the row below the cell. -/
def quietSpace (n : ℕ) : Submodule F (Board n) where
  carrier := {b | ∀ i : Fin n, read b (i.val+2) = (path n+1) (b i) + read b i.val}
  zero_mem' i := by simp
  add_mem' {b c} hb hc i := by
    rw [read_add,hb i,hc i,read_add,Pi.add_apply,map_add]
    abel
  smul_mem' c b hb i := by
    rw [read_smul,hb i,read_smul,Pi.smul_apply,map_smul,smul_add]

theorem quiet_iff_toggles {n : ℕ} (b : Board n) : b∈quietSpace n ↔
    ∀ i j : Fin n, b i j + read (b i) j.val + read (b i) (j.val+2) +
      read b i.val j + read b (i.val+2) j = 0 := by
  constructor
  · intro h i j
    have eq := congrFun (h i) j
    change read b (i.val+2) j = ((read (b i) j.val+read (b i) (j.val+2))+b i j) + read b i.val j at eq
    rw [eq]; abel_nf; simp [CharTwo.two_eq_zero]
  · intro h i; funext j
    have eq := CharTwo.add_eq_zero.mp (h i j)
    change read b (i.val+2) j = ((read (b i) j.val+read (b i) (j.val+2))+b i j) + read b i.val j
    rw [← eq]; abel

theorem chase {n : ℕ} (b : Board n) (quiet : b∈quietSpace n) (j : ℕ)
    (bound : j≤n+1) : read b j = (fib (path n+1) j) (read b 1) := by
  induction j using Nat.twoStepInduction with
  | zero => rfl
  | one => rfl
  | more j prev next =>
    have inside : j<n := by omega
    have step := quiet ⟨j,inside⟩
    change read b (j+2) = (path n+1) (b ⟨j,inside⟩) + read b j at step
    rw [← read_cell b ⟨j,inside⟩] at step
    rw [step,next (by omega),prev (by omega)]
    rfl

private theorem quadratic {n : ℕ} (positive : 0<n) (k : ℕ) (index : n+1=2*3^k)
    (b : Board n) (quiet : b∈quietSpace n) :
    path n ((path n+1) (read b 1))=0 := by
  let v := read b 1
  have hP : fib (path n) (2*3^k) v=0 := index ▸ path_annihilates positive v
  have hQ : fib (path n+1) (2*3^k) v=0 := by
    rw [← index]
    exact (chase b quiet (n+1) (le_refl _)).symm.trans (read_end b)
  obtain ⟨u,w,h⟩ := bezout_bound k
  let e : P →+* Module.End F (Row n) := (aeval (path n)).toRingHom
  have ex : e X=path n := aeval_X _
  have sum := congrArg e h
  rw [map_add,map_mul,map_mul,map_mul,map_fib,map_fib,map_add,map_one,ex] at sum
  have applied := congrArg (fun A : Module.End F (Row n) => A v) sum
  change (e u) (fib (path n) (2*3^k) v) + (e w) (fib (path n+1) (2*3^k) v) =
    (path n) ((path n+1) v) at applied
  simpa [hP,hQ] using applied.symm

private theorem eigen_zero {n : ℕ} (v : Row n) (c : F) (eigen : path n v=c • v)
    (first : read v 1=0) : v=0 := by
  have entries (j : ℕ) (bound : j≤n+1) : read v j=0 := by
    induction j using Nat.twoStepInduction with
    | zero => rfl
    | one => exact first
    | more j prev next =>
      have inside : j<n := by omega
      have step := congrFun eigen ⟨j,inside⟩
      change read v j+read v (j+2)=c*v ⟨j,inside⟩ at step
      have cell : v ⟨j,inside⟩=0 := by simpa [read,inside] using next (by omega)
      simpa [prev (by omega),cell] using step
  funext j; simpa using entries (j.val+1) (by omega)

/-- The first two lamps in the first row determine any quiet press pattern. -/
private theorem top_zero {n : ℕ} (k : ℕ) (size : 2≤n) (index : n+1=2*3^k)
    (b : Board n) (quiet : b∈quietSpace n) (first : read (read b 1) 1=0)
    (second : read (read b 1) 2=0) : b=0 := by
  let v := read b 1
  let A := path n
  have quad : A ((A+1) v)=0 := quadratic (by omega) k index b quiet
  have split : (A+1) v=A v+v := rfl
  have eig : A (A v)=A v := by
    rw [split,map_add] at quad
    funext i
    exact CharTwo.add_eq_zero.mp (congrFun quad i)
  have firstA : read (A v) 1=0 := by
    have h : 0<n := by omega
    change (if _ : 0<n then (A v) ⟨0,by omega⟩ else 0)=0
    rw [dif_pos h]; change 0+read v 2=0
    simpa only [zero_add] using second
  have av : A v=0 := eigen_zero _ 1 (by simpa using eig) firstA
  have vz : v=0 := eigen_zero _ 0 (by simpa using av) first
  funext i
  have row := chase b quiet (i.val+1) (by omega)
  rw [read_cell] at row
  change b i=fib (A+1) (i.val+1) v at row
  simpa [vz] using row

private def modeRow (n : ℕ) (d : F) : Row n := fun i => fib d (i.val+1)

private theorem read_mode {n : ℕ} (d : F) (bound : fib d (n+1)=0) (j : ℕ) (hi : j≤n+1) :
    read (modeRow n d) j = fib d j := by
  cases j with
  | zero => rfl
  | succ j =>
    by_cases h : j<n
    · simp [read,h,modeRow]
    · have eq : j=n := by omega
      subst j; simp [bound]

private theorem path_mode {n : ℕ} (d : F) (ends : fib d (n+1)=0) :
    path n (modeRow n d)=d • modeRow n d := by
  funext i
  change read (modeRow n d) i.val+read (modeRow n d) (i.val+2)=d*fib d (i.val+1)
  rw [read_mode d ends _ (by omega),read_mode d ends _ (by omega),fib]
  linear_combination CharTwo.add_self_eq_zero (fib d i.val)

private def mode (n : ℕ) (d : F) : Board n := fun i => (fib (d+1) (i.val+1)) • modeRow n d

private theorem read_board_mode {n : ℕ} (d : F) (ends : fib (d+1) (n+1)=0)
    (j : ℕ) (hi : j≤n+1) : read (mode n d) j = fib (d+1) j • modeRow n d := by
  cases j with
  | zero => simp [read,fib]
  | succ j =>
    by_cases h : j<n
    · simp [read,mode,h]
    · have eq : j=n := by omega
      subst j; simp [ends]

private theorem mode_quiet {n : ℕ} (d : F) (horizontal : fib d (n+1)=0)
    (vertical : fib (d+1) (n+1)=0) : mode n d ∈ quietSpace n := by
  intro i
  have eig : (path n+1) (modeRow n d)=(d+1) • modeRow n d := by
    change (path n) (modeRow n d)+modeRow n d=_
    rw [path_mode d horizontal,add_smul,one_smul]
  rw [read_board_mode d vertical _ (by omega),read_board_mode d vertical _ (by omega)]
  change _=(path n+1) (fib (d+1) (i.val+1) • modeRow n d)+_
  rw [fib,map_smul,eig,add_smul,smul_smul,mul_comm (d+1)]

/-- The first two entries of the physical first row. -/
private def observe (n : ℕ) : quietSpace n →ₗ[F] F×F where
  toFun b := (read (read b.val 1) 1,read (read b.val 1) 2)
  map_add' b c := by simp
  map_smul' c b := by change (_,_) = c • (_,_); simp

private theorem observed_mode {n : ℕ} (size : 2≤n) (d : F) (h : mode n d ∈ quietSpace n) :
    observe n ⟨mode n d,h⟩=(1,d) := by
  have first : 0<n := by omega
  have second : 1<n := by omega
  simp [observe,read,first,second,mode,modeRow,fib]

/-- The two observed lamps give independent binary coordinates for all quiet
press patterns on the square. -/
theorem two_coordinates {n k : ℕ} (size : 2≤n) (index : n+1=2*3^(k+1)) :
    ∃ e : quietSpace n ≃ₗ[F] (F×F), ∀ b, e b=(read (read b.val 1) 1,read (read b.val 1) 2) := by
  have injective : Function.Injective (observe n) := by
    intro b c same
    have obs : observe n (b-c)=0 := by rw [map_sub,same,sub_self]
    have first := congrArg Prod.fst obs
    have second := congrArg Prod.snd obs
    apply Subtype.ext
    apply sub_eq_zero.mp
    exact top_zero (k+1) size index (b-c) (b-c).property first second
  obtain ⟨zero,one⟩ := boundary k
  rw [← index] at zero one
  have q0 := mode_quiet (n:=n) 0 zero (by simpa using one)
  have q1 := mode_quiet (n:=n) 1 one (by simpa using zero)
  have surjective : Function.Surjective (observe n) := by
    rintro ⟨a,b⟩
    refine ⟨(a+b) • ⟨_,q0⟩ + b • (⟨_,q1⟩ : quietSpace n),?_⟩
    rw [map_add,map_smul,map_smul,observed_mode size 0 q0,observed_mode size 1 q1]
    apply Prod.ext <;> simp
  exact ⟨LinearEquiv.ofBijective (observe n) ⟨injective,surjective⟩,fun _ => rfl⟩

/-- Boyles's proposed infinite family, with exponent k+1 covering every
positive exponent. Nullity is the actual dimension of the quiet grid subspace. -/
theorem boyles_family (k : ℕ) : Module.finrank F (quietSpace (2*3^(k+1)-1))=2 := by
  have power : 0<3^k := by positivity
  have size : 2≤2*3^(k+1)-1 := by rw [pow_succ]; omega
  have index : 2*3^(k+1)-1+1=2*3^(k+1) := by omega
  obtain ⟨e,_⟩ := two_coordinates size index
  simpa using e.finrank_eq

/-- Conjecture 5.1 of Boyles: infinitely many square grids have nullity two. -/
theorem infinitely_many_nullity_two : {n : ℕ | Module.finrank F (quietSpace n)=2}.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro a
  refine ⟨2*3^(a+1)-1,boyles_family a,?_⟩
  have h : a<3^a := Nat.lt_pow_self (by decide : 1<3)
  rw [pow_succ]; omega

#print axioms quiet_iff_toggles
#print axioms two_coordinates
#print axioms boyles_family
#print axioms infinitely_many_nullity_two

end
end LightsGrid

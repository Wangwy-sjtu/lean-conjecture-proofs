import LightsGrid

/-! Physical press weight, the five-neighbor toggle map and its worst solvable cost. -/
namespace GridClicks
open LightsPolynomial LightsGrid
open scoped BigOperators CharTwo

def click (v : F) : ℕ := if v=0 then 0 else 1

def weight {n : ℕ} (b : Board n) : ℕ :=
  ∑ c : Fin n × Fin n, click (b c.1 c.2)

/-- The output of one complete pattern of presses on the actual five-cell board. -/
def effect {n : ℕ} (b : Board n) : Board n := fun i j =>
  b i j + LightsGrid.read (b i) j.val + LightsGrid.read (b i) (j.val+2) +
    LightsGrid.read b i.val j + LightsGrid.read b (i.val+2) j

private theorem read_linear {V : Type*} [AddMonoid V] {n : ℕ} (b c : Fin n → V) (t : ℕ) :
    LightsGrid.read (b+c) t=LightsGrid.read b t+LightsGrid.read c t := by
  cases t with
  | zero => simp [LightsGrid.read]
  | succ t => by_cases h : t<n <;> simp [LightsGrid.read,h]

theorem same_effect {n : ℕ} (x y : Board n) :
    effect x=effect y ↔ x+y∈quietSpace n := by
  rw [quiet_iff_toggles]
  have linear (i j : Fin n) :
      effect (x+y) i j=effect x i j+effect y i j := by
    simp only [effect,Pi.add_apply,read_linear];abel
  change effect x=effect y ↔ ∀ i j, effect (x+y) i j=0
  constructor
  · intro eq i j; rw [linear,eq,CharTwo.add_self_eq_zero]
  · intro eq; ext i j
    exact CharTwo.add_eq_zero.mp ((linear i j).symm.trans (eq i j))

/-- The largest minimum number of presses over all solvable light states. -/
def IsMostClicks (n M : ℕ) : Prop :=
  (∀ a : Board n, (∃ x, effect x=a) → ∃ y, effect y=a ∧ weight y≤M) ∧
  (∃ a : Board n, (∃ x, effect x=a) ∧ ∀ y, effect y=a → M≤weight y)

theorem board_twice {n : ℕ} (x : Board n) : x+x=0 := by
  ext i j; exact CharTwo.add_self_eq_zero (x i j)

end GridClicks

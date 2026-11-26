import Std

/-!
OEIS A024399. R. J. Mathar's recurrence dated 2011-10-08.
Source: https://oeis.org/A024399
The numerator formula is also recorded at https://oeis.org/A024392 .
Checked with Lean 4.24.0, using only its standard distribution.
-/

namespace A024399

/-- Elementary symmetric function of degree j. Each subset either omits
    the head or contains the head and j-1 elements of the tail. -/
def elementary : Nat → List Int → Int
  | 0, _ => 1
  | _ + 1, [] => 0
  | j + 1, x :: xs => elementary (j + 1) xs + x * elementary j xs

/-- The first k positive integers congruent to 2 modulo 3, in reverse order. -/
def progression : Nat → List Int
  | 0 => []
  | k + 1 => (3 * (k : Int) + 2) :: progression k

def e (j k : Nat) : Int := elementary j (progression k)

/-- OEIS starts at n=1. The same definition at n=0 gives the harmless extension 0. -/
def a (n : Nat) : Int := e 3 (n + 2) / e 1 (n + 2)

private theorem e_succ (j k : Nat) :
    e (j+1) (k+1) = e (j+1) k + (3*(k:Int)+2) * e j k := by
  simp only [e, progression, elementary]

private theorem e_zero (k : Nat) : e 0 k = 1 := by simp [e, elementary]

private theorem moments (k : Nat) :
    2 * e 1 k = (k : Int) * (3*k+1) ∧
    8 * e 2 k = 9*(k : Int)^4 - 6*(k : Int)^3 - 5*(k : Int)^2 + 2*k ∧
    48 * e 3 k = 27*(k : Int)^6 - 81*(k : Int)^5 + 27*(k : Int)^4
                  + 73*(k : Int)^3 - 30*(k : Int)^2 - 16*k := by
  induction k with
  | zero => decide
  | succ k ih =>
    obtain ⟨h₁, h₂, h₃⟩ := ih
    simp only [e_succ, e_zero, Int.natCast_succ, Int.mul_one]
    exact ⟨by grobner, by grobner, by grobner⟩

/-- Twenty-four times the ratio before taking the floor. -/
def polynomial (x : Int) : Int := x * (x + 1) * (9*x*x + 33*x + 22)

theorem floor_formula (n : Nat) : a n = polynomial n / 24 := by
  obtain ⟨h₁, _, h₃⟩ := moments (n + 2)
  simp only [Int.natCast_add, Int.cast_ofNat_Int] at h₁ h₃
  have hpos : 0 < e 1 (n + 2) := by
    have hn : (0 : Int) ≤ n := Int.natCast_nonneg n
    have hprod : 0 < ((n : Int) + 2) * (3*((n:Int) + 2)+1) :=
      Int.mul_pos (by omega) (by omega)
    omega
  have hratio : 24 * e 3 (n + 2) = e 1 (n + 2) * polynomial n := by
    unfold polynomial
    grobner
  unfold a
  calc
    _ = (24 * e 3 (n+2)) / (24 * e 1 (n+2)) :=
      (Int.mul_ediv_mul_of_pos _ _ (by decide : (0:Int) < 24)).symm
    _ = (e 1 (n+2) * polynomial n) / (e 1 (n+2) * 24) := by
      rw [hratio, Int.mul_comm 24]
    _ = _ := Int.mul_ediv_mul_of_pos _ _ hpos

private theorem addCong {a b c d : Int}
    (h : a % 24 = b % 24) (j : c % 24 = d % 24) :
    (a+c) % 24 = (b+d) % 24 := by
  rw [Int.add_emod a c, Int.add_emod b d, h, j]

private theorem mulCong {a b c d : Int}
    (h : a % 24 = b % 24) (j : c % 24 = d % 24) :
    (a*c) % 24 = (b*d) % 24 := by
  rw [Int.mul_emod a c, Int.mul_emod b d, h, j]

private theorem reduce_polynomial (x : Int) :
    polynomial x % 24 = polynomial (x % 24) % 24 := by
  unfold polynomial
  repeat first | rfl | exact (Int.emod_emod x 24).symm | apply addCong | apply mulCong

def correction (n : Nat) : Int := if n % 3 = 1 then 8 else 0

private theorem remainder (n : Nat) : polynomial n % 24 = correction n := by
  have table : ∀ r : Fin 24, polynomial (r.val : Int) % 24 = correction r.val := by decide
  have h := table ⟨n % 24, Nat.mod_lt _ (by decide)⟩
  change polynomial ((n % 24 : Nat) : Int) % 24 = correction (n % 24) at h
  simp only [Int.natCast_emod, Int.cast_ofNat_Int] at h
  rw [reduce_polynomial, h]
  unfold correction
  have : n % 24 % 3 = n % 3 := by omega
  rw [this]

theorem scaled_formula (n : Nat) : 24 * a n + correction n = polynomial n := by
  rw [floor_formula, ← remainder]
  have h := Int.emod_add_ediv_mul (polynomial n) 24
  omega

private theorem shift_three (n : Nat) : correction (n+3) = correction n := by
  simp [correction]

/-- The recurrence, shifted forward so subtraction of natural-number indices
    can never truncate. At n≥1 this is Mathar's recurrence at index n+7≥8. -/
theorem mathar_recurrence (n : Nat) :
    a (n+7) = 4*a (n+6) - 6*a (n+5) + 5*a (n+4) - 5*a (n+3)
              + 6*a (n+2) - 4*a (n+1) + a n := by
  have h₀ := scaled_formula n
  have h₁ := scaled_formula (n+1)
  have h₂ := scaled_formula (n+2)
  have h₃ := scaled_formula (n+3)
  have h₄ := scaled_formula (n+4)
  have h₅ := scaled_formula (n+5)
  have h₆ := scaled_formula (n+6)
  have h₇ := scaled_formula (n+7)
  rw [shift_three n] at h₃
  rw [shift_three (n+1)] at h₄
  rw [shift_three (n+2)] at h₅
  rw [shift_three (n+3), shift_three n] at h₆
  rw [shift_three (n+4), shift_three (n+1)] at h₇
  have hp : polynomial ((n+7 : Nat) : Int) =
      4*polynomial (↑(n+6 : Nat)) - 6*polynomial (↑(n+5 : Nat)) +
      5*polynomial (↑(n+4 : Nat)) - 5*polynomial (↑(n+3 : Nat)) +
      6*polynomial (↑(n+2 : Nat)) - 4*polynomial (↑(n+1 : Nat)) + polynomial n := by
    simp only [polynomial, Int.natCast_add, Int.cast_ofNat_Int]
    grobner
  omega

/-- Coefficient of x^n in x*(5+11*x+7*x^2+5*x^3-x^4). -/
def numeratorCoeff : Nat → Int
  | 1 => 5 | 2 => 11 | 3 => 7 | 4 => 5 | 5 => -1 | _ => 0

private def past (n j : Nat) : Int := if j ≤ n then a (n-j) else 0

/-- Coefficient of x^n in (1+x+x^2)*(1-x)^5 times the series of a. -/
def productCoeff (n : Nat) : Int :=
  a n - 4*past n 1 + 6*past n 2 - 5*past n 3 + 5*past n 4
       - 6*past n 5 + 4*past n 6 - past n 7

/-- Coefficientwise form of Mathar's ordinary generating function identity.
    The denominator has constant coefficient 1. -/
theorem generating_function_coefficients (n : Nat) : productCoeff n = numeratorCoeff n := by
  by_cases h : n < 7
  · have initial : ∀ r : Fin 7, productCoeff r.val = numeratorCoeff r.val := by decide
    exact initial ⟨n, h⟩
  · obtain ⟨k, rfl⟩ : ∃ k, n = k+7 := ⟨n-7, by omega⟩
    have hr := mathar_recurrence k
    simp only [productCoeff, past, if_pos (show 1 ≤ k+7 by omega),
      if_pos (show 2 ≤ k+7 by omega), if_pos (show 3 ≤ k+7 by omega),
      if_pos (show 4 ≤ k+7 by omega), if_pos (show 5 ≤ k+7 by omega),
      if_pos (show 6 ≤ k+7 by omega), if_pos (show 7 ≤ k+7 by omega)]
    change a (k+7) - 4*a (k+6) + 6*a (k+5) - 5*a (k+4) +
      5*a (k+3) - 6*a (k+2) + 4*a (k+1) - a k = 0
    omega

#print axioms mathar_recurrence
#print axioms generating_function_coefficients
end A024399

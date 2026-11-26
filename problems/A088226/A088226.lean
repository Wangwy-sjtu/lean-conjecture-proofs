import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic.Ring

/-!
A088226. The OEIS indices start at 1. The auxiliary sequence `b t` means
the term at OEIS index `t+1`. Natural distance implements absolute difference.
-/

namespace A088226

/-- Absolute difference of two naturals. -/
def distance (x y : ℕ) : ℕ := (x-y)+(y-x)

def b : ℕ → ℕ
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | t+3 => distance (b (t+2)) (b (t+1) + b t)

/-- A088226, with the OEIS convention a(1)=0, a(2)=0, a(3)=1. -/
def a (n : ℕ) : ℕ := b (n-1)

/-- The square has the same parity as t precisely when the distance is even. -/
def NearestEvenSquare (t value : ℕ) : Prop :=
  (∃ q : ℕ, q*q % 2 = t % 2 ∧ distance t (q*q) = 2*value) ∧
  ∀ q : ℕ, q*q % 2 = t % 2 → 2*value ≤ distance t (q*q)

theorem distance_even_iff (x y : ℕ) : distance x y % 2 = 0 ↔ x%2 = y%2 := by
  unfold distance
  omega

private def Triple (k m : ℕ) : Prop :=
  let t := k*k + 2*m
  b t = m ∧ b (t+1) = k-m ∧ b (t+2) = m+1

private theorem advance {k m : ℕ} (hm : m < k) (h : Triple k m) : Triple k (m+1) := by
  let t := k*k + 2*m
  obtain ⟨h0,h1,h2⟩ := h
  change b t = m at h0
  change b (t+1) = k-m at h1
  change b (t+2) = m+1 at h2
  have h3 : b (t+3) = k-(m+1) := by
    rw [b, h2, h1, h0, distance]
    omega
  have h4 : b (t+4) = m+2 := by
    change distance (b (t+3)) (b (t+2)+b (t+1)) = m+2
    rw [h3,h2,h1,distance]
    omega
  unfold Triple
  rw [show k*k+2*(m+1)=t+2 by dsimp [t]; omega]
  exact ⟨h2,h3,h4⟩

/-- The two alternating runs in the block beginning at a square. -/
theorem block (k m : ℕ) (hm : m ≤ k) :
    b (k*k+2*m) = m ∧ b (k*k+2*m+1) = k-m ∧ b (k*k+2*m+2) = m+1 := by
  have blocks : ∀ k m : ℕ, m ≤ k → Triple k m := by
    intro k
    induction k with
    | zero =>
      intro m hm
      have : m = 0 := by omega
      subst m
      exact ⟨rfl,rfl,rfl⟩
    | succ k ih =>
      have last := ih k (by omega)
      obtain ⟨last0,last1,last2⟩ := last
      let t := k*k + 2*k
      change b t = k at last0
      change b (t+1) = k-k at last1
      change b (t+2) = k+1 at last2
      rw [Nat.sub_self] at last1
      have last3 : b (t+3) = 1 := by
        rw [b,last2,last1,last0,distance]
        omega
      have first : Triple (k+1) 0 := by
        unfold Triple
        simp only [Nat.mul_zero,Nat.add_zero,Nat.sub_zero]
        rw [show (k+1)*(k+1) = t+1 by dsimp [t]; ring]
        exact ⟨last1,last2,last3⟩
      intro m
      induction m with
      | zero => exact fun _ => first
      | succ m im =>
        intro hm
        exact advance (by omega) (im (by omega))
  exact blocks k m hm

/-- The published literal indexing fails already at the nonsquare index 5. -/
theorem literal_refutation : ¬(∀ n : ℕ, 1 ≤ n → NearestEvenSquare n (a n)) := by
  intro h
  obtain ⟨q,_,hq⟩ := (h 5 (by decide)).1
  have ha : a 5 = 0 := by decide
  rw [ha] at hq
  unfold distance at hq
  have hs : 5 = q*q := by omega
  by_cases hq2 : q ≤ 2
  · have := Nat.mul_le_mul hq2 hq2
    omega
  · have hq3 : 3 ≤ q := by omega
    have := Nat.mul_le_mul hq3 hq3
    omega

/-- Every index one past a positive square contradicts the literal formula. -/
theorem refutation_at_squares (k : ℕ) (hk : 0 < k) :
    ¬NearestEvenSquare (k*k+1) (a (k*k+1)) := by
  have ha : a (k*k+1)=0 := by
    simpa [a] using (block k 0 (Nat.zero_le _)).1
  rintro ⟨⟨q,_,hd⟩,_⟩
  rw [ha] at hd
  unfold distance at hd
  have heq : q*q=k*k+1 := by omega
  by_cases hq : q ≤ k
  · have := Nat.mul_le_mul hq hq
    omega
  · have hlt : k+1 ≤ q := by omega
    have hs := Nat.mul_le_mul hlt hlt
    rw [show (k+1)*(k+1)=k*k+2*k+1 by ring] at hs
    omega

private theorem square_parity (k : ℕ) : k*k % 2 = k % 2 := by
  rw [Nat.mul_mod]
  have h : k%2 < 2 := Nat.mod_lt _ (by decide)
  rcases (show k%2=0 ∨ k%2=1 by omega) with h | h <;> rw [h]

private theorem nearest_at_even (k m : ℕ) (hm : m ≤ k) :
    NearestEvenSquare (k*k+2*m) m := by
  constructor
  · exact ⟨k, by omega, by unfold distance; omega⟩
  · intro q hpar
    rw [square_parity q] at hpar
    have pk := square_parity k
    by_cases hq : q ≤ k
    · have hs := Nat.mul_le_mul hq hq
      unfold distance
      omega
    · have hq' : k+2 ≤ q := by omega
      have hs := Nat.mul_le_mul hq' hq'
      rw [show (k+2)*(k+2)=k*k+4*k+4 by ring] at hs
      unfold distance
      omega

private theorem nearest_at_odd (k m : ℕ) (hm : m ≤ k) :
    NearestEvenSquare (k*k+2*m+1) (k-m) := by
  have square : (k+1)*(k+1) = k*k + 2*k+1 := by ring
  constructor
  · exact ⟨k+1, by rw [square]; omega, by rw [square]; unfold distance; omega⟩
  · intro q hpar
    rw [square_parity q] at hpar
    have pk := square_parity k
    by_cases hq : k+1 ≤ q
    · have hs := Nat.mul_le_mul hq hq
      rw [square] at hs
      unfold distance
      omega
    · have hlt : q < k := by omega
      obtain ⟨s,hs⟩ : ∃ s, k=s+1 := ⟨k-1, by omega⟩
      subst k
      have hqs : q ≤ s := by omega
      have hsq := Nat.mul_le_mul hqs hqs
      rw [show (s+1)*(s+1) = s*s+2*s+1 by ring]
      unfold distance
      omega

/-- Every positive OEIS index satisfies the corrected, shifted distance formula. -/
theorem shifted_formula (n : ℕ) (_hn : 1 ≤ n) : NearestEvenSquare (n-1) (a n) := by
  let t := n-1
  change NearestEvenSquare t (b t)
  let k := t.sqrt
  have lower : k*k ≤ t := Nat.sqrt_le t
  have upper : t ≤ k*k+k+k := Nat.sqrt_le_add t
  let m := (t-k*k)/2
  have hm : m ≤ k := by dsimp [m]; omega
  obtain ⟨he,ho,_⟩ := block k m hm
  by_cases hy : (t-k*k)%2=0
  · have ht : t=k*k+2*m := by dsimp [m]; omega
    rw [ht,he]
    exact nearest_at_even k m hm
  · have ht : t=k*k+2*m+1 := by dsimp [m]; omega
    rw [ht,ho]
    exact nearest_at_odd k m hm

end A088226

#print axioms A088226.literal_refutation
#print axioms A088226.refutation_at_squares
#print axioms A088226.shifted_formula

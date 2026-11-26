import RationalPowers
import Mathlib.NumberTheory.Padics.PadicVal.Basic

namespace SmallSumProduct

def Base (p q : ℕ) : ℚ := (p : ℚ)/q

theorem base_gt_one {p q : ℕ} (hq : 0<q) (hpq : q<p) : 1 < Base p q := by
  apply (lt_div_iff₀ (by exact_mod_cast hq : (0 : ℚ)<q)).mpr
  simpa using (show (q:ℚ) < p by exact_mod_cast hpq)

theorem pair_power_unique {p q : ℕ} (hq : 0<q) (hpq : q<p) (hcop : p.Coprime q)
    {a b c d : ℕ} (h : Base p q^a + Base p q^b = Base p q^c + Base p q^d) :
    (a=c ∧ b=d) ∨ (a=d ∧ b=c) := by
  have hs : powerSum (Base p q) [a,b] = powerSum (Base p q) [c,d] := by simpa [powerSum] using h
  have count := rational_power_counts hq hpq hcop [a,b] [c,d] rfl (by simp; omega) hs a
  have hm : a ∈ [c,d] := List.count_pos_iff.mp (by rw [← count]; exact List.count_pos_iff.mpr (by simp))
  have hr := base_gt_one hq hpq
  rcases (show a=c ∨ a=d by simpa using hm) with e | e
  · subst c
    exact Or.inl ⟨rfl, pow_right_injective₀ (by linarith) hr.ne' (add_left_cancel h)⟩
  · subst d
    rw [add_comm (Base p q^c)] at h
    exact Or.inr ⟨rfl, pow_right_injective₀ (by linarith) hr.ne' (add_left_cancel h)⟩

def Hits (r x : ℚ) (k : ℕ) : Prop := ∃ i j : ℕ, x+r^k=r^i+r^j

private theorem nonderepeat {p q : ℕ} (hq : 0<q) (hpq : q<p) (hcop : p.Coprime q)
    (hp : 3≤p) (x : ℚ) (ho : ∀ j : ℕ, x ≠ Base p q^j) (a b : ℕ)
    (ha : Hits (Base p q) x a) (hb : Hits (Base p q) x b) : a=b := by
  obtain ⟨i,j,hij⟩ := ha
  obtain ⟨k,l,hkl⟩ := hb
  have he : powerSum (Base p q) [i,j,b] = powerSum (Base p q) [k,l,a] := by
    simp only [powerSum, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    linarith
  have cnt := rational_power_counts hq hpq hcop [i,j,b] [k,l,a] rfl hp he a
  have hm : a ∈ [i,j,b] := List.count_pos_iff.mp (by rw [cnt]; exact List.count_pos_iff.mpr (by simp))
  rcases (show a=i ∨ a=j ∨ a=b by simpa using hm) with e | e | e
  · subst i; exact False.elim (ho j (by linarith))
  · subst j; exact False.elim (ho i (by linarith))
  · exact e

private def v2 := padicValRat 2

private theorem val_pow (i : ℕ) : v2 ((2:ℚ)^i) = (i : ℤ) := by
  have base : padicValRat 2 (2:ℚ) = 1 := padicValRat.self (p:=2) (by decide)
  unfold v2
  rw [padicValRat.pow (by decide : (2:ℚ)≠0), base, mul_one]

private theorem dyadic_parts {x : ℚ} (hx : 0<x) (ho : ∀ i : ℕ, x≠(2:ℚ)^i)
    {a : ℕ} (ha : Hits 2 x a) (hn : (a : ℤ) ≠ v2 x) :
    ∃ l k : ℕ, (l : ℤ) = v2 x ∧ x + (2:ℚ)^a = 2^l+2^k := by
  obtain ⟨i,j,hi⟩ := ha
  have left : v2 (x+(2:ℚ)^a) = min (v2 x) a := by
    have diff : padicValRat 2 x ≠ padicValRat 2 ((2:ℚ)^a) := by simpa [← val_pow, v2] using hn.symm
    simpa only [v2, ← val_pow] using
      padicValRat.add_eq_min (p:=2) (q:=x) (r:=(2:ℚ)^a) (by positivity) hx.ne' (by positivity) diff
  have neq : i ≠ j := by
    intro e; subst j
    have self : (2:ℚ)^i+2^i = 2^(i+1) := by ring
    rw [self] at hi
    rw [hi, val_pow] at left
    have hia : i+1 ≤ a := by omega
    have order := pow_le_pow_right₀ (show (1:ℚ)≤2 by decide) hia
    linarith
  have right : v2 ((2:ℚ)^i+2^j) = min (i:ℤ) j := by
    have diff : padicValRat 2 ((2:ℚ)^i) ≠ padicValRat 2 ((2:ℚ)^j) := by
      change v2 _ ≠ v2 _; rw [val_pow, val_pow]; exact_mod_cast neq
    simpa only [← val_pow, v2] using padicValRat.add_eq_min (p:=2) (q:=(2:ℚ)^i)
      (r:=(2:ℚ)^j) (by positivity) (by positivity) (by positivity) diff
  rw [hi, right] at left
  have order : v2 x < (a:ℤ) := by
    by_contra hc
    have aa : (i:ℤ) = a ∨ (j:ℤ) = a := by omega
    rcases aa with ei | ej
    · have : i=a := by exact_mod_cast ei
      subst i; exact ho j (by linarith)
    · have : j=a := by exact_mod_cast ej
      subst j; exact ho i (by linarith)
  have ea : (i:ℤ)=v2 x ∨ (j:ℤ)=v2 x := by omega
  rcases ea with ei | ej
  · exact ⟨i,j,ei,hi⟩
  · exact ⟨j,i,ej,hi.trans (add_comm _ _)⟩

private theorem dyadic_repeat {x : ℚ} (hx : 0<x) (ho : ∀ i : ℕ, x≠(2:ℚ)^i)
    (a b : ℕ) (ha : Hits 2 x a) (hb : Hits 2 x b)
    (ea : (a:ℤ)≠v2 x) (eb : (b:ℤ)≠v2 x) : a=b := by
  obtain ⟨i,j,ei,hi⟩ := dyadic_parts hx ho ha ea
  obtain ⟨i',j',ei',hi'⟩ := dyadic_parts hx ho hb eb
  have clean : i'=i := by omega
  subst i'
  have e : (2:ℚ)^j+2^b=2^j'+2^a := by linarith
  have norm : Base 2 1 = 2 := by norm_num [Base]
  rcases pair_power_unique (p:=2) (q:=1) (a:=j) (b:=b) (c:=j') (d:=a)
      (by decide) (by decide) (by decide) (by simpa [norm] using e) with h | h
  · exact h.2.symm
  · rw [h.1] at hi
    exact False.elim (ho i (by linarith))

/-- With a rational base, the exponents giving collisions in a positive
off-orbit translate fall in at most two singleton classes. The exceptional
class is only needed for base two. -/
theorem hit_classes {p q : ℕ} (hq : 0<q) (hpq : q<p) (hcop : p.Coprime q)
    (x : ℚ) (hx : 0<x) (ho : ∀ j : ℕ, x≠Base p q^j) :
    ∃ z : ℤ, ∀ a b : ℕ, Hits (Base p q) x a → Hits (Base p q) x b →
      (a : ℤ) ≠ z → (b : ℤ) ≠ z → a=b := by
  by_cases hp : 3≤p
  · exact ⟨-1,fun a b ha hb _ _ => nonderepeat hq hpq hcop hp x ho a b ha hb⟩
  · have e1 : p=2 := by omega
    have e2 : q=1 := by omega
    subst p; subst q
    have ne : Base 2 1=2 := by norm_num [Base]
    rw [ne] at ho ⊢
    exact ⟨v2 x,dyadic_repeat hx ho⟩

end SmallSumProduct

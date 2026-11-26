import RepeatedCover
import ReflectionLayout

/-! Worst-case optimal press counts on fixed-nullity square-grid dilations. -/
namespace GridScaling
open LightsPolynomial LightsGrid ReflectionTiles ReflectionLayout GridClicks RepeatedCover
open scoped BigOperators CharTwo
noncomputable section

def IsActive {m : ℕ} (c : Cell m) : Prop := ∃ v : quietSpace m, v.val c.1 c.2≠0
abbrev Active (m : ℕ) := {c : Cell m // IsActive c}
abbrev Fixed (m : ℕ) := {c : Cell m // ¬IsActive c}
abbrev Frozen (m q : ℕ) := Gaps m q ⊕ (Copies q × Fixed m)
abbrev Shape (m q : ℕ) := Frozen m q ⊕ (Copies q × Active m)

noncomputable instance activeFintype (m : ℕ) : Fintype (Active m) := Fintype.ofFinite _
noncomputable instance fixedFintype (m : ℕ) : Fintype (Fixed m) := Fintype.ofFinite _
noncomputable instance quietFintype (m : ℕ) : Fintype (quietSpace m) := Fintype.ofFinite _

/-- Number of seed cells changed by some quiet pattern. -/
def activeCount (m : ℕ) := Fintype.card (Active m)

def entry {m : ℕ} (v : quietSpace m) (c : Active m) : F := v.val c.val.1 c.val.2

private def layout (m q : ℕ) : Shape m q ≃ Cell (side m q) := by
  classical
  let cells : Fixed m ⊕ Active m ≃ Cell m := (Equiv.sumComm _ _).trans (Equiv.sumCompl IsActive)
  let tileRows := (Equiv.prodSumDistrib (Copies q) (Fixed m) (Active m)).symm.trans
    ((Equiv.refl (Copies q)).prodCongr cells)
  exact (Equiv.sumAssoc _ _ _).trans
    ((Equiv.sumCongr (Equiv.refl (Gaps m q)) tileRows).trans (positions m q))

private theorem eval_lift {m q : ℕ} (v : quietSpace m) (s : Shape m q) :
    lift q v.val ((layout m q s).1) ((layout m q s).2)=
      (match s with | .inl _ => 0 | .inr (_,c) => entry v c) := by
  rcases s with (g|⟨t,c⟩)|⟨t,c⟩
  · exact lift_at v.val (.inl g)
  · have eq := lift_at (m:=m) (q:=q) v.val (.inr (t,c.val))
    have zero : v.val c.val.1 c.val.2=0 := by
      by_contra h
      exact c.property ⟨v,h⟩
    exact eq.trans zero
  · exact lift_at v.val (.inr (t,c.val))

private theorem balanced (m : ℕ) : Balanced (@entry m) := by
  intro c x
  obtain ⟨w,hw⟩ := c.property
  have one : entry w c=1 := (by decide : ∀ a : F, a≠0 → a=1) _ hw
  let f := fun v : quietSpace m => click (x+entry v c)
  have pair (v : quietSpace m) : f v+f (v+w)=1 := by
    change click (x+entry v c)+click (x+(entry v c+entry w c))=1
    rw [one]
    exact (by decide : ∀ a b : F, click (a+b)+click (a+(b+1))=1) _ _
  have shift : (∑ v, f (v+w))=∑ v,f v := Equiv.sum_comp (Equiv.addRight w) f
  have agg : (∑ v,f v)+(∑ v,f (v+w))=Fintype.card (quietSpace m) := by
    rw [← Finset.sum_add_distrib];simp_rw [pair];simp
  rw [shift] at agg
  change 2*(∑ v,f v)=_
  omega

private def tilesOf {m q : ℕ} (x : Board (side m q)) (s : Shape m q) : F :=
  x (layout m q s).1 (layout m q s).2

private def boardOf {m q : ℕ} (f : Shape m q → F) : Board (side m q) :=
  fun i j => f ((layout m q).symm (i,j))

private theorem unpack {m q : ℕ} (f : Shape m q → F) (s : Shape m q) :
    tilesOf (boardOf f) s=f s := by simp [tilesOf,boardOf]

private theorem weight_layout {m q : ℕ} (x : Board (side m q)) (v : quietSpace m) :
    weight (x+lift q v.val)=(∑ g : Frozen m q,click (tilesOf x (.inl g)))+
      dist entry (fun t c => tilesOf x (.inr (t,c))) v := by
  let val := fun s : Shape m q => click (tilesOf x s+
    (match s with | .inl _ => 0 | .inr (_,c) => entry v c))
  have total : weight (x+lift q v.val)=∑ s,val s := by
    symm;apply Fintype.sum_equiv (layout m q)
    intro s
    change click (tilesOf x s+_)=click (_+lift q v.val _ _)
    rw [eval_lift];rfl
  rw [total,Fintype.sum_sum_type]
  congr 1
  · apply Finset.sum_congr rfl
    intro c _
    change click (tilesOf x (.inl c)+0)=_
    rw [add_zero]
  · rw [Fintype.sum_prod_type];rfl

theorem covering_formula (m q : ℕ)
    (dim : Module.finrank F (quietSpace (side m q))=Module.finrank F (quietSpace m)) :
    IsMostClicks (side m q) (Fintype.card (Frozen m q)+radius (@entry m) ((q+1)^2)) := by
  classical
  let r := (q+1)^2
  have card : Fintype.card (Copies q)=r := by simp [Copies,r,pow_two]
  obtain ⟨upper,lower⟩ := radius_transfer (@entry m) (Copies q)
  rw [card] at upper lower
  constructor
  · rintro _ ⟨x,rfl⟩
    obtain ⟨v,hv⟩ := upper (fun t c => tilesOf x (.inr (t,c)))
    refine ⟨x+lift q v.val,?_,?_⟩
    · apply (same_effect _ _).2
      rw [add_right_comm,board_twice,zero_add];exact lift_quiet q v.val v.property
    · rw [weight_layout]
      have single (g : Frozen m q) : click (tilesOf x (.inl g))≤1 := by unfold click;split <;> decide
      have bd := Finset.sum_le_sum (s:=Finset.univ) (fun g _ => single g)
      simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul,mul_one] at bd
      exact Nat.add_le_add bd hv
  · obtain ⟨far,worst⟩ := lower
    let f : Shape m q → F := Sum.elim (fun _ => 1) (fun p => far p.1 p.2)
    let x := boardOf f
    refine ⟨effect x,⟨x,rfl⟩,?_⟩
    intro y eq
    obtain ⟨v,hv⟩ := lift_exhausts dim (x+y) ((same_effect _ _).mp eq.symm)
    have py : y=x+lift q v.val := by rw [hv,← add_assoc,board_twice,zero_add]
    rw [py,weight_layout]
    simp only [x,unpack,f,Sum.elim_inl,Sum.elim_inr]
    have ones : click 1=1 := by decide
    simp only [ones,Finset.sum_const,Finset.card_univ,smul_eq_mul,mul_one]
    exact Nat.add_le_add_left (worst v) _

private theorem cardinal (m q : ℕ) :
    Fintype.card (Frozen m q)+(q+1)^2*activeCount m=(side m q)^2 := by
  have c := Fintype.card_congr (layout m q)
  simpa only [Shape,Cell,Copies,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin,pow_two,
    activeCount] using c

/-- Along each reflected family with the seed's nullity, twice the worst
press count is a quadratic in the multiplier on each parity class, with
an eventual seed-dependent constant correction on the odd class. -/
theorem eventual_quadratic (m : ℕ) : ∃ K D : ℕ, ∀ Q : ℕ, 0<Q →
    let n := (m+1)*Q-1
    Module.finrank F (quietSpace n)=Module.finrank F (quietSpace m) →
    ∃ M, IsMostClicks n M ∧
      (Even Q → 2*M+Q^2*activeCount m=2*n^2) ∧
      (Odd Q → K≤Q → 2*M+Q^2*activeCount m+D=2*n^2) := by
  obtain ⟨k,D,stable⟩ := odd_stable (@entry m) (balanced m)
  refine ⟨2*k+1,D,?_⟩
  intro Q positive
  obtain ⟨q,rfl⟩ := Nat.exists_eq_succ_of_ne_zero positive.ne'
  have size : (m+1)*(q+1)-1=side m q := by rw [Nat.mul_succ];unfold side;omega
  dsimp only
  rw [size]
  intro dim
  have counts := cardinal m q
  have rad := twice_radius (@entry m) (balanced m) ((q+1)^2)
  change 2*radius (@entry m) ((q+1)^2)+deficit (@entry m) ((q+1)^2)=(q+1)^2*activeCount m at rad
  refine ⟨_,covering_formula m q dim,?_,?_⟩
  · rintro ⟨s,es⟩
    obtain ⟨u,eu⟩ : Even ((q+1)^2) := (show Even (q+1) from ⟨s,es⟩).pow_of_ne_zero (by decide)
    have e : (q+1)^2=2*u := by omega
    have zero : deficit (@entry m) ((q+1)^2)=0 := e ▸ even_deficit (@entry m) (balanced m) u
    change 2*(Fintype.card (Frozen m q)+radius (@entry m) ((q+1)^2))+(q+1)^2*activeCount m=2*(side m q)^2
    rw [zero,Nat.add_zero] at rad
    omega
  · intro odd large
    obtain ⟨u,eu⟩ := odd.pow (n:=2)
    have qq : q+1≤(q+1)^2 := by nlinarith
    change (q+1)^2=2*u+1 at eu
    have ku : k≤u := by omega
    have limit : deficit (@entry m) ((q+1)^2)=D := by rw [eu];exact stable u ku
    change 2*(Fintype.card (Frozen m q)+radius (@entry m) ((q+1)^2))+(q+1)^2*activeCount m+D=2*(side m q)^2
    rw [limit] at rad
    omega

#print axioms covering_formula
#print axioms eventual_quadratic
end
end GridScaling

import GridFactors

/-! The known size condition for nullity four, included to state the
Most Clicks formula directly for every physical square of nullity four. -/
namespace FourIndex
open LightsPolynomial LightsGrid Polynomial GridGcd GridFactors OddStabilization
open scoped Polynomial CharTwo
noncomputable section

private theorem nonzero_odd (m : ℕ) (odd : Odd m) : common m≠0 := by
  intro z
  have h : common m∣fib X m := EuclideanDomain.gcd_dvd_left ..
  rw [z,zero_dvd_iff] at h
  have e := congrArg (evalRingHom (0:F)) h
  rw [map_fib,map_zero] at e
  change fib ((X:P).eval 0) m=0 at e
  obtain ⟨u,rfl⟩ := odd
  rw [eval_X,fib_at_zero] at e
  exact one_ne_zero e

private theorem quadratic_rank {g : P} (deg : g.natDegree=2) (shape : g=U+1)
    (m : ℕ) (dv : g∣fib X m) : 5∣m := by
  let Q := AdjoinRoot g
  let x : Q := AdjoinRoot.root g
  have gd : g.degree≠0 := by
    intro eq; have := natDegree_eq_zero_iff_degree_le_zero.mpr eq.le;omega
  letI : Nontrivial Q := AdjoinRoot.nontrivial _ gd
  letI : CharP Q 2 := charP_of_injective_algebraMap' F Q 2
  have rel : AdjoinRoot.mk g g=0 := AdjoinRoot.mk_self
  conv at rel => lhs;arg 2;rw [shape]
  change AdjoinRoot.mk g (X*(X+1)+1)=0 at rel
  simp only [map_add,map_mul,map_one,AdjoinRoot.mk_X] at rel
  change x*(x+1)+1=0 at rel
  have xx : x*x=x+1 := by
    apply CharTwo.add_eq_zero.mp; linear_combination rel
  have nz : x≠0 := by intro h; rw [h,zero_mul,zero_add] at rel;exact one_ne_zero rel
  have step (j : ℕ) (a : fib x j=0) (b : fib x (j+1)=1) :
      fib x (j+2)=x ∧ fib x (j+3)=x ∧ fib x (j+4)=1 ∧ fib x (j+5)=0 ∧ fib x (j+6)=1 := by
    have c : fib x (j+2)=x := by rw [fib,b,a,mul_one,add_zero]
    have d : fib x (j+3)=x := by
      change x*fib x (j+2)+fib x (j+1)=x
      rw [c,b,xx,add_assoc,CharTwo.add_self_eq_zero,add_zero]
    have e : fib x (j+4)=1 := by
      change x*fib x (j+3)+fib x (j+2)=1
      rw [d,c,xx,add_right_comm,CharTwo.add_self_eq_zero,zero_add]
    have f : fib x (j+5)=0 := by
      change x*fib x (j+4)+fib x (j+3)=0
      rw [e,d,mul_one,CharTwo.add_self_eq_zero]
    exact ⟨c,d,e,f,by change x*fib x (j+5)+fib x (j+4)=1;rw [f,e,mul_zero,zero_add]⟩
  have cycle (k : ℕ) : fib x (5*k)=0 ∧ fib x (5*k+1)=1 := by
    induction k with
    | zero => exact ⟨rfl,rfl⟩
    | succ k h => exact ⟨by simpa only [Nat.mul_succ] using (step _ h.1 h.2).2.2.2.1,
                         by simpa only [Nat.mul_succ] using (step _ h.1 h.2).2.2.2.2⟩
  have root := AdjoinRoot.mk_eq_zero.mpr dv
  rw [map_fib,AdjoinRoot.mk_X] at root
  change fib x m=0 at root
  obtain ⟨a,b⟩ := cycle (m/5)
  obtain ⟨c,d,e,_,_⟩ := step _ a b
  by_contra no
  have rem : m%5≠0 := fun f => no (Nat.dvd_of_mod_eq_zero f)
  rcases (by omega : m=5*(m/5)+1 ∨ m=5*(m/5)+2 ∨ m=5*(m/5)+3 ∨ m=5*(m/5)+4) with h|h|h|h
  · exact one_ne_zero ((h ▸ root : fib x (5*(m/5)+1)=0) ▸ b.symm)
  · exact nz (c.symm.trans (h ▸ root))
  · exact nz (d.symm.trans (h ▸ root))
  · exact one_ne_zero (e.symm.trans (h ▸ root))

/-- Every physical nullity-four grid has index five times a positive odd number. -/
theorem size (n : ℕ) (dim : Module.finrank F (quietSpace n)=4) :
    ∃ q : ℕ, Odd q ∧ n=5*q-1 := by
  have val : (common (n+1)).natDegree=4 :=
    (by simpa using (physical (n+1) (by omega)).symm.trans dim)
  obtain ⟨s,m,odd,form⟩ := Nat.exists_eq_two_pow_mul_odd (by omega : n+1≠0)
  rw [form,dyadic_common s m odd] at val
  obtain ⟨p,fix,sp⟩ := odd_square m odd
  obtain ⟨u,pu⟩ := even_degree fix
  have dm : (common m).natDegree=4*u := by rw [sp,natDegree_sq,pu];omega
  have unum : U≠0 := by change (X:P)*(X+1)≠0; exact mul_ne_zero X_ne_zero (X_add_C_ne_zero (1:F))
  have s0 : s=0 := by
    by_contra bad
    obtain ⟨t,rfl⟩ := Nat.exists_eq_succ_of_ne_zero bad
    by_cases three : 3∣m
    · rw [if_pos three,natDegree_mul (pow_ne_zero _ unum) (pow_ne_zero _ (nonzero_odd m odd)),
        natDegree_pow,natDegree_pow,deg_U,dm,pow_succ] at val
      have hp : 0<2^t := by positivity
      have de : 2*(2^t*2-1)+2=4*2^t := by omega
      have impossible : 6=4*(2^t*(2*u+1)) := by nlinarith only [val,de]
      omega
    · rw [if_neg three,one_mul,natDegree_pow,dm,pow_succ] at val
      have impossible : 4=8*(2^t*u) := by nlinarith only [val]
      omega
  subst s
  have en : n+1=m := by simpa using form
  have nd : (common m).natDegree=4 := by simpa using val
  have pd : p.natDegree=2 := by rw [sp,natDegree_sq] at nd;omega
  obtain ⟨h,comp⟩ := fixed_comp fix
  have hd : h.natDegree=1 := by rw [comp,natDegree_comp,deg_U] at pd;omega
  have hn : h≠0 := by rintro rfl;simp at hd
  have lin := (GridFactors.monic hn).eq_X_add_C hd
  have dv : p∣fib X m := (dvd_pow_self p (by decide : 2≠0)).trans
    (sp ▸ (EuclideanDomain.gcd_dvd_left .. : common m∣fib X m))
  have formp : p=U+C (h.coeff 0) := by
    calc
      p=h.comp U := comp
      _=(X+C (h.coeff 0)).comp U := congrArg (fun f : P => f.comp U) lin
      _=_ := by simp
  have c1 : h.coeff 0=1 := by
    rcases (by decide : ∀ v : F,v=0 ∨ v=1) (h.coeff 0) with z|o
    · rw [z,map_zero,add_zero] at formp
      obtain ⟨v,hv⟩ := dv
      have ev := congrArg (evalRingHom (0:F)) hv
      rw [map_fib,map_mul,formp] at ev
      obtain ⟨j,hm⟩ := odd
      simp [hm,U,fib_at_zero] at ev
    · exact o
  have d5 := quadratic_rank pd (by simpa [c1] using formp) m dv
  obtain ⟨q,eq⟩ := d5
  exact ⟨q,(Nat.odd_mul.mp (eq ▸ odd)).2,by omega⟩

#print axioms size
end
end FourIndex

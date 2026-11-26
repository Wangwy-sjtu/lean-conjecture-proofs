import Mathlib.NumberTheory.LucasPrimality
import Mathlib.Tactic.NormNum.Prime

/-!
Thomas Ordowski's 2023-11-27 observation in OEIS A001122 on primitive root 2
for primes of the form 2^k+3 (k ≠ 2).
Source: https://oeis.org/A001122 .
Lean/mathlib v4.24.0.  The partial factorizations below are untrusted data.
Every factor, modular exponent, and bound is checked inside the kernel.
The OEIS entry A057732 records the exponent; the factorization of
2^2190+1 can be compared against https://factordb.com/index.php?query=2%5E2190%2B1 .
-/
namespace A001122

set_option exponentiation.threshold 3000
set_option maxRecDepth 250000
set_option maxHeartbeats 4000000

/-- Binary exponentiation with an explicit number of bits. -/
private def powBits (p b : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 1 % p
  | bits+1, n =>
    let u := powBits p b bits (n/2)
    if n%2 = 0 then u*u % p else (u*u % p)*b % p

private theorem powBits_spec (p b bits d : ℕ) (h : d < 2^bits) :
    powBits p b bits d = b^d % p := by
  induction bits generalizing d with
  | zero =>
    have : d = 0 := by simpa using h
    simp [this, powBits]
  | succ bits ih =>
    rw [Nat.pow_succ] at h
    rw [powBits, ih (d/2) (by omega)]
    split
    · rename_i even
      have e : d = d/2 + d/2 := by omega
      conv => rhs; rw [e, Nat.pow_add]
      simp
    · rename_i odd
      have e : d = (d/2 + d/2) + 1 := by omega
      conv => rhs; rw [e, Nat.pow_succ, Nat.pow_add]
      simp

private def powMod (p b d : ℕ) := powBits p b (d.log2+1) d

private theorem powMod_spec (p b d : ℕ) : powMod p b d = b^d % p :=
  powBits_spec _ _ _ _ Nat.lt_log2_self

private theorem zmod_test {m b d : ℕ} (hm : 1 < m) :
    ((b : ZMod m)^d = 1) ↔ powMod m b d = 1 := by
  rw [powMod_spec, ← Nat.cast_pow, ← Nat.cast_one (R := ZMod m),
    ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hm]


/-- Every prime divisor of a product of listed primes is on the list. -/
private theorem factor_mem {q : ℕ} (hq : q.Prime) (fs : List ℕ)
    (allPrime : ∀ r ∈ fs, Nat.Prime r) (hdiv : q ∣ fs.prod) : q ∈ fs := by
  induction fs with
  | nil =>
    have : q ∣ 1 := by simpa using hdiv
    exact (hq.not_dvd_one this).elim
  | cons r rs ih =>
    obtain ⟨hr, hrest⟩ := List.forall_mem_cons.mp allPrime
    rcases hq.dvd_mul.mp (show q ∣ r * rs.prod from hdiv) with h | h
    · have eq := ((Nat.dvd_prime hr).mp h).resolve_left hq.ne_one
      simp [eq]
    · exact List.mem_cons_of_mem r (ih hrest h)


private theorem pow_congruence (p : ℕ) {n : ℕ} (hp : p ∣ n) (b d : ℕ) :
    b^d ≡ powMod n b d [MOD p] := by
  rw [powMod_spec]
  exact (Nat.mod_modEq _ _).symm.of_dvd hp

private theorem zpow_one_iff (p b d : ℕ) :
    ((b : ZMod p)^d = 1) ↔ b^d ≡ 1 [MOD p] := by
  rw [← Nat.cast_pow, ← Nat.cast_one (R := ZMod p), ZMod.natCast_eq_natCast_iff]

/-- If a composite has two proper factors equal to 1 modulo F, write them
    as 1+uF and 1+vF. The two lowest base-F digits of (n-1)/F then satisfy
    the displayed inequality, since u+v ≤ uv+1 for positive u,v. -/
private theorem split_bound {n F p c : ℕ}
    (hF : 0 < F) (hp : 1 < p) (hc : 1 < c) (hn : n = p*c)
    (hF₁ : F ∣ n-1) (hp₁ : F ∣ p-1) :
    ((n-1)/F)%F ≤ ((n-1)/F)/F+1 := by
  have hnpos : 1 ≤ n := by rw [hn]; exact Nat.mul_pos (by omega) (by omega)
  have hfpc := (Nat.modEq_iff_dvd' (show 1 ≤ p by omega)).2 hp₁
  have hfn := (Nat.modEq_iff_dvd' hnpos).2 hF₁
  have hfc : 1 ≡ c [MOD F] := by
    rw [hn] at hfn
    exact hfn.trans (by simpa using hfpc.symm.mul_right c)
  obtain ⟨u,hu⟩ := hp₁
  obtain ⟨v,hv⟩ := (Nat.modEq_iff_dvd' (show 1 ≤ c by omega)).1 hfc
  have a : p = F*u+1 := by omega
  have b : c = F*v+1 := by omega
  have hu' : u ≠ 0 := by rintro rfl; simp at a; omega
  have hv' : v ≠ 0 := by rintro rfl; simp at b; omega
  have hs : u+v ≤ u*v+1 := by
    obtain ⟨i,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hu'
    obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hv'
    simp only [Nat.succ_mul, Nat.mul_succ]; omega
  have decomp : n = F*(F*(u*v)+(u+v))+1 := by rw [hn,a,b]; grobner
  have quotient : (n-1)/F = F*(u*v)+(u+v) := by
    rw [decomp, Nat.add_sub_cancel, Nat.mul_div_cancel_left _ hF]
  rw [quotient, Nat.mul_add_mod_self_left]
  have hq : u*v ≤ (F*(u*v)+(u+v))/F := by
    apply (Nat.le_div_iff_mul_le hF).2
    rw [Nat.mul_comm (u*v)]
    omega
  have := Nat.mod_le (u+v) F
  omega

/-- A witness has order F modulo every prime divisor of n. A square bound or
    the preceding split bound excludes a composite n.
    The witness supplied here is already raised to (n-1)/F. -/
private theorem partial_prime (n b F : ℕ) (fs : List ℕ)
    (prime_factors : ∀ q ∈ fs, Nat.Prime q)
    (h : 1 < n ∧ 0 < F ∧ (n < (F+1)^2 ∨ (F ∣ n-1 ∧ ((n-1)/F)/F+1 < ((n-1)/F)%F)) ∧ fs.prod = F ∧
      powMod n b F = 1 ∧ (fs.all fun q =>
        let v := powMod n b (F/q)
        decide (0 < v) && (Nat.gcd (v-1) n == 1)) = true) : n.Prime := by
  obtain ⟨hn, hF, hbound, hprod, hpow, hchecks⟩ := h
  by_contra hnprime
  let p := n.minFac
  have hp : p.Prime := Nat.minFac_prime (by omega)
  have hpdiv : p ∣ n := Nat.minFac_dvd n
  have hp2 : p^2 ≤ n := Nat.minFac_sq_le_self (by omega) hnprime
  letI : NeZero p := ⟨hp.ne_zero⟩
  have hp_pow : (b : ZMod p)^F = 1 := by
    apply (zpow_one_iff _ _ _).2
    simpa only [hpow] using pow_congruence p hpdiv b F
  have horder : orderOf (b : ZMod p) = F := by
    apply orderOf_eq_of_pow_and_pow_div_prime hF hp_pow
    intro q hq hdiv heq
    have hmem := factor_mem hq fs prime_factors (hprod.symm ▸ hdiv)
    obtain ⟨vpos, vgcd⟩ : 0 < powMod n b (F/q) ∧ (powMod n b (F/q)-1).gcd n = 1 := by
      simpa using List.all_eq_true.mp hchecks q hmem
    have hc := ((zpow_one_iff _ _ _).1 heq).symm.trans (pow_congruence p hpdiv b (F/q))
    have hg := Nat.dvd_gcd ((Nat.modEq_iff_dvd' vpos).1 hc) hpdiv
    rw [vgcd] at hg
    exact hp.not_dvd_one hg
  let u : (ZMod p)ˣ := Units.mkOfMulEqOne (b : ZMod p) ((b : ZMod p)^(F-1))
    (by rw [← pow_succ', Nat.sub_add_cancel hF]; exact hp_pow)
  have hle : F ≤ p-1 := calc
    F = orderOf (b : ZMod p) := horder.symm
    _ = orderOf u := orderOf_injective (Units.coeHom _) Units.val_injective u
    _ ≤ Fintype.card (ZMod p)ˣ := orderOf_le_card_univ
    _ ≤ p-1 := Nat.card_units_zmod_lt_sub_one hp.one_lt
  rcases hbound with hs | ⟨hfmod, hsplit⟩
  · have hlt : F+1 ≤ p := by have := hp.one_lt; omega
    exact (Nat.not_lt_of_ge (Nat.le_trans (Nat.pow_le_pow_left hlt 2) hp2)) hs
  · have hdivF : F ∣ p-1 := by
      have ord : orderOf u = F :=
        (orderOf_injective (Units.coeHom _) Units.val_injective u).symm.trans horder
      have dvd_card : orderOf u ∣ Fintype.card (ZMod p)ˣ := orderOf_dvd_card
      rwa [ord, (Nat.prime_iff_card_units p).mp hp] at dvd_card
    obtain ⟨c,hc⟩ := hpdiv
    have hcpos : c ≠ 0 := by rintro rfl; simp at hc; omega
    have hcone : c ≠ 1 := by rintro rfl; simp at hc; exact hnprime (hc ▸ hp)
    exact (Nat.not_lt_of_ge (split_bound hF hp.one_lt (by omega) hc hfmod hdivF)) hsplit

@[local simp] private theorem prime_165709 : Nat.Prime 165709 :=
  partial_prime _ 120145 4603
    [4603]
    (List.forall_mem_cons.mpr ⟨by norm_num, List.forall_mem_nil _⟩) (by decide +kernel)

@[local simp] private theorem prime_19553663 : Nat.Prime 19553663 :=
  partial_prime _ 1122714 165709
    [165709]
    (List.forall_mem_cons.mpr ⟨prime_165709, List.forall_mem_nil _⟩) (by decide +kernel)

@[local simp] private theorem prime_911038126645819 : Nat.Prime 911038126645819 :=
  partial_prime _ 429252162224530 19553663
    [19553663]
    (List.forall_mem_cons.mpr ⟨prime_19553663, List.forall_mem_nil _⟩) (by decide +kernel)

@[local simp] private theorem prime_18478609113710122023550126425157 : Nat.Prime 18478609113710122023550126425157 :=
  partial_prime _ 3632012509421135547514018711325 911038126645819
    [911038126645819]
    (List.forall_mem_cons.mpr ⟨prime_911038126645819, List.forall_mem_nil _⟩) (by decide +kernel)

@[local simp] private theorem prime_32647 : Nat.Prime 32647 :=
  partial_prime _ 64 5441
    [5441]
    (List.forall_mem_cons.mpr ⟨by norm_num, List.forall_mem_nil _⟩) (by decide +kernel)

@[local simp] private theorem prime_39372283 : Nat.Prime 39372283 :=
  partial_prime _ 8307389 32647
    [32647]
    (List.forall_mem_cons.mpr ⟨prime_32647, List.forall_mem_nil _⟩) (by decide +kernel)

@[local simp] private theorem prime_21067 : Nat.Prime 21067 :=
  partial_prime _ 64 3511
    [3511]
    (List.forall_mem_cons.mpr ⟨by norm_num, List.forall_mem_nil _⟩) (by decide +kernel)

@[local simp] private theorem prime_177342007 : Nat.Prime 177342007 :=
  partial_prime _ 14374428 21067
    [21067]
    (List.forall_mem_cons.mpr ⟨prime_21067, List.forall_mem_nil _⟩) (by decide +kernel)

@[local simp] private theorem prime_29694045630754428802476133 : Nat.Prime 29694045630754428802476133 :=
  partial_prime _ 24458469892823812946430950 6982359687391981
    [39372283, 177342007]
    (List.forall_mem_cons.mpr ⟨prime_39372283, List.forall_mem_cons.mpr ⟨prime_177342007, List.forall_mem_nil _⟩⟩) (by decide +kernel)

@[local simp] private theorem prime_87419270336941038394489735553 : Nat.Prime 87419270336941038394489735553 :=
  partial_prime _ 49882666558211259292287010577 29694045630754428802476133
    [29694045630754428802476133]
    (List.forall_mem_cons.mpr ⟨prime_29694045630754428802476133, List.forall_mem_nil _⟩) (by decide +kernel)

@[local simp] private theorem prime_2297061088504243735131288756383674095201931965827193105631611941 : Nat.Prime 2297061088504243735131288756383674095201931965827193105631611941 :=
  partial_prime _ 320951573937494303319199908184147074888960882452955738307507114 87419270336941038394489735553
    [87419270336941038394489735553]
    (List.forall_mem_cons.mpr ⟨prime_87419270336941038394489735553, List.forall_mem_nil _⟩) (by decide +kernel)

@[local simp] private theorem prime_2213923 : Nat.Prime 2213923 :=
  partial_prime _ 392120 5197
    [5197]
    (List.forall_mem_cons.mpr ⟨by norm_num, List.forall_mem_nil _⟩) (by decide +kernel)

@[local simp] private theorem prime_754549 : Nat.Prime 754549 :=
  partial_prime _ 681309 277
    [277]
    (List.forall_mem_cons.mpr ⟨by norm_num, List.forall_mem_nil _⟩) (by decide +kernel)

@[local simp] private theorem prime_144873409 : Nat.Prime 144873409 :=
  partial_prime _ 40929776 754549
    [754549]
    (List.forall_mem_cons.mpr ⟨prime_754549, List.forall_mem_nil _⟩) (by decide +kernel)

@[local simp] private theorem prime_8402657723 : Nat.Prime 8402657723 :=
  partial_prime _ 7777256966 144873409
    [144873409]
    (List.forall_mem_cons.mpr ⟨prime_144873409, List.forall_mem_nil _⟩) (by decide +kernel)

@[local simp] private theorem prime_2017751 : Nat.Prime 2017751 :=
  partial_prime _ 1213820 1153
    [1153]
    (List.forall_mem_cons.mpr ⟨by norm_num, List.forall_mem_nil _⟩) (by decide +kernel)

@[local simp] private theorem prime_18326288025533 : Nat.Prime 18326288025533 :=
  partial_prime _ 7791239976956 2017751
    [2017751]
    (List.forall_mem_cons.mpr ⟨prime_2017751, List.forall_mem_nil _⟩) (by decide +kernel)

@[local simp] private theorem prime_10675784729679713992243592197878625185297616730291770841553592167207738941 : Nat.Prime 10675784729679713992243592197878625185297616730291770841553592167207738941 :=
  partial_prime _ 5069095832050062235660579023421734363717141132146221493752665684151248226 340920952510759267601128441357
    [2213923, 8402657723, 18326288025533]
    (List.forall_mem_cons.mpr ⟨prime_2213923, List.forall_mem_cons.mpr ⟨prime_8402657723, List.forall_mem_cons.mpr ⟨prime_18326288025533, List.forall_mem_nil _⟩⟩⟩) (by decide +kernel)

@[local simp] private theorem prime_114031 : Nat.Prime 114031 :=
  partial_prime _ 109333 181
    [181]
    (List.forall_mem_cons.mpr ⟨by norm_num, List.forall_mem_nil _⟩) (by decide +kernel)

@[local simp] private theorem prime_1409581 : Nat.Prime 1409581 :=
  partial_prime _ 1376816 191
    [191]
    (List.forall_mem_cons.mpr ⟨by norm_num, List.forall_mem_nil _⟩) (by decide +kernel)

@[local simp] private theorem prime_6806669 : Nat.Prime 6806669 :=
  partial_prime _ 5621250 4181
    [37, 113]
    (List.forall_mem_cons.mpr ⟨by norm_num, List.forall_mem_cons.mpr ⟨by norm_num, List.forall_mem_nil _⟩⟩) (by decide +kernel)

@[local simp] private theorem prime_260388090213152722245485411960014340275503208289295000550325920282114359301 : Nat.Prime 260388090213152722245485411960014340275503208289295000550325920282114359301 :=
  partial_prime _ 190730188647139964815106711445636150921775495723572490222179600512143364792 10326876587953166085365100
    [2, 2, 3, 5, 5, 73, 431, 114031, 1409581, 6806669]
    (List.forall_mem_cons.mpr ⟨by norm_num, List.forall_mem_cons.mpr ⟨by norm_num, List.forall_mem_cons.mpr ⟨by norm_num, List.forall_mem_cons.mpr ⟨by norm_num, List.forall_mem_cons.mpr ⟨by norm_num, List.forall_mem_cons.mpr ⟨by norm_num, List.forall_mem_cons.mpr ⟨by norm_num, List.forall_mem_cons.mpr ⟨prime_114031, List.forall_mem_cons.mpr ⟨prime_1409581, List.forall_mem_cons.mpr ⟨prime_6806669, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩) (by decide +kernel)

/-- The specific prime at exponent 2191. -/
def N : ℕ := 2^2191 + 3

theorem prime_N : Nat.Prime N :=
  partial_prime _ 107204054633391037123067503409376010197945402411699356825628262121734444233977671967823377615568255270729439218729662688268358220588668716579236476951652408921328544811225767578698216254827989706177766207523047039722393155616646512537777459666181692865065801365522022676880242215222205214412546923566368561406861965954449442172193083222054576577047388343418939184706517411490479633353716682906363794221198736459499385268159789557227419074051438293077056765657772316985436407508740958085464054495295202636106157678202865702421490377872779428310168427204435666562516341217565723539535701855748222203741980554824363688642286709337995929946539027985856621431765735 117994767282706854944641290663444203308527545683148102074228343179603979001878986735824916374500111465811077847274379193113668506416815113311014384179596315555187292714181257788290924843345941206258452742625664761671081857193480498457871816617
    [18478609113710122023550126425157, 2297061088504243735131288756383674095201931965827193105631611941, 10675784729679713992243592197878625185297616730291770841553592167207738941, 260388090213152722245485411960014340275503208289295000550325920282114359301]
    (List.forall_mem_cons.mpr ⟨prime_18478609113710122023550126425157, List.forall_mem_cons.mpr ⟨prime_2297061088504243735131288756383674095201931965827193105631611941, List.forall_mem_cons.mpr ⟨prime_10675784729679713992243592197878625185297616730291770841553592167207738941, List.forall_mem_cons.mpr ⟨prime_260388090213152722245485411960014340275503208289295000550325920282114359301, List.forall_mem_nil _⟩⟩⟩⟩) (by decide +kernel)

theorem five_divides : 5 ∣ N-1 := by decide +kernel

theorem fifth_power_test : (2 : ZMod N)^((N-1)/5) = 1 :=
  (zmod_test (m := N) (b := 2) (d := (N-1)/5) (by decide)).2 (by decide +kernel)

theorem order_strictly_smaller : orderOf (2 : ZMod N) < N-1 :=
  lt_of_le_of_lt (orderOf_le_of_pow_eq_one (by decide) fifth_power_test) (by decide)

/-- The second observation in Ordowski's 2023 comment is false. -/
theorem ordowski_second_claim_false :
    ¬ (∀ k : ℕ, k ≠ 2 → (2^k+3).Prime → orderOf (2 : ZMod (2^k+3)) = 2^k+3-1) := by
  intro h
  exact order_strictly_smaller.ne (h 2191 (by decide) prime_N)

#print axioms prime_N
#print axioms fifth_power_test
#print axioms ordowski_second_claim_false
end A001122

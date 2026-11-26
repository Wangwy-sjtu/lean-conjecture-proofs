import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Data.List.Rotate
import Mathlib.Tactic.Linarith

/-! A finite automaton for equal sums of two circular blocks of Fibonacci numbers. -/
namespace FibonacciBarrycade

abbrev Colour := Bool × Bool

def sign (v : Colour) : ℤ := (v.1.toNat : ℤ) - (v.2.toNat : ℤ)

def delta (b c : Bool) : ℕ := if b=c then 0 else 1

/-- Summary of two subsequences, the even-index block and the odd-index block.
Only internal bit changes have been counted. -/
structure Shape where
  firstEven : Colour
  lastEven : Colour
  firstOdd : Colour
  lastOdd : Colour
  changesA : ℕ
  changesB : ℕ
  different : Bool
  nextOdd : Bool
  deriving DecidableEq, Inhabited

def differs (v : Colour) : Bool := v.1 != v.2

def lowShape (a b c d e f : Colour) : Shape :=
  ⟨e,c,b,d,delta e.1 a.1+delta a.1 c.1+delta b.1 f.1+delta f.1 d.1,
    delta e.2 a.2+delta a.2 c.2+delta b.2 f.2+delta f.2 d.2,
    differs a || differs b || differs c || differs d || differs e || differs f,false⟩

def Shape.push (s : Shape) (v : Colour) : Shape :=
  let p := if s.nextOdd then s.lastOdd else s.lastEven
  {s with lastEven := if s.nextOdd then s.lastEven else v,
          lastOdd := if s.nextOdd then v else s.lastOdd,
          changesA := s.changesA + delta p.1 v.1,
          changesB := s.changesB + delta p.2 v.2,
          different := s.different || differs v,
          nextOdd := !s.nextOdd}

def Shape.cyclicA (s : Shape) := s.changesA + delta s.lastEven.1 s.firstOdd.1 + delta s.lastOdd.1 s.firstEven.1
def Shape.cyclicB (s : Shape) := s.changesB + delta s.lastEven.2 s.firstOdd.2 + delta s.lastOdd.2 s.firstEven.2

def shape (f : ℕ → Colour) : ℕ → Shape
  | 0 => lowShape (f 0) (f 1) (f 2) (f 3) (f 4) (f 5)
  | k+1 => (shape f k).push (f (k+6))

def signedSum (f : ℕ → Colour) : ℕ → ℤ
  | 0 => 0
  | n+1 => signedSum f n + sign (f n)*(Nat.fib (n+2) : ℤ)

/-- The weight of all available smaller Fibonacci numbers is below the sum
of the next two Fibonacci place values. -/
private theorem sum_small (f : ℕ → Colour) (n : ℕ) :
    -(Nat.fib (n+3) : ℤ)<signedSum f n ∧ signedSum f n<(Nat.fib (n+3) : ℤ) := by
  induction n with
  | zero => change -(2:ℤ)<0 ∧ (0:ℤ)<2; decide
  | succ n ih =>
    have hrec : (Nat.fib (n+1+3) : ℤ) = (Nat.fib (n+2) : ℤ)+(Nat.fib (n+3) : ℤ) := by
      exact_mod_cast Nat.fib_add_two (n:=n+2)
    rw [signedSum]
    generalize hv : f n = v
    obtain ⟨a,b⟩ := v
    cases a <;> cases b <;> simp [sign] <;> omega

inductive Carry | minus | minusBack | zero | plusBack | plus deriving DecidableEq, Inhabited

def Carry.coeffs : Carry → ℤ × ℤ
  | .minus => (-1,0)
  | .minusBack => (0,-1)
  | .zero => (0,0)
  | .plusBack => (0,1)
  | .plus => (1,0)

def Carry.weight (c : Carry) (n : ℕ) : ℤ :=
  c.coeffs.1*(Nat.fib (n+2) : ℤ)+c.coeffs.2*(Nat.fib (n+1) : ℤ)

def compatible (lo hi : Carry) (v : Colour) : Bool :=
  decide (lo.coeffs.1=hi.coeffs.1+hi.coeffs.2+sign v ∧ lo.coeffs.2=hi.coeffs.1)

private theorem downward (f : ℕ → Colour) (n : ℕ) (hi : Carry)
    (h : signedSum f (n+1)+hi.weight (n+1)=0) :
    ∃ lo, compatible lo hi (f n) = true ∧ signedSum f n+lo.weight n=0 := by
  obtain ⟨lower,upper⟩ := sum_small f n
  have hfib : (Nat.fib (n+3) : ℤ)=(Nat.fib (n+1) : ℤ)+(Nat.fib (n+2) : ℤ) := by
    exact_mod_cast Nat.fib_add_two (n:=n+1)
  have mono : (Nat.fib (n+1):ℤ)≤(Nat.fib (n+2):ℤ) := by exact_mod_cast Nat.fib_le_fib_succ
  rw [signedSum] at h
  generalize hv : f n=v at *
  obtain ⟨a,b⟩ := v
  cases hi <;> cases a <;> cases b <;>
    simp [Carry.weight,Carry.coeffs,sign,Nat.add_assoc] at h <;>
    first | (refine ⟨.zero,by decide,?_⟩; simp [Carry.weight,Carry.coeffs]; omega)
          | (refine ⟨.plus,by decide,?_⟩; simp [Carry.weight,Carry.coeffs]; omega)
          | (refine ⟨.minus,by decide,?_⟩; simp [Carry.weight,Carry.coeffs]; omega)
          | (refine ⟨.plusBack,by decide,?_⟩; simp [Carry.weight,Carry.coeffs]; omega)
          | (refine ⟨.minusBack,by decide,?_⟩; simp [Carry.weight,Carry.coeffs]; omega)
          | omega

private def codes6 : List ℕ := [
  206,638,646,1062,1926,2442,2766,2866,3630,3730,3814,4062,4162,4486,7110,7542,
  7966,7990,8830,9242,9342,9666,9766,10038,10654,10714,11086,11410,11582,11590,12006,12262,
  12378,13302,13726,13750,14034,14466,14890,15754,16270,16594,16942,17458,17634,17882,17982,18306,
  18406,18432,18464,18556,18880,18972,19004,19254,19438,19870,19930,20176,20300,20624,20716,20806,
  21982,22422,22966,23146,23682,24106,25306,25360,25484,25808,25900,26158,26242,26674,26850,27072,
  27104,27196,27520,27612,27644,27658,27774,28098,28214,28470,28654,29146,29518,29842,30334,31198,
  31638,32070,32338,32362,32778,33726,33826,34074,34514,34522,34702,35026,35374,35458,36066,36298,
  36414,36738,36854,37234,38098,38122,38538,38970,41602,41926,42042,42298,42358,42474,43222,43338,
  43662,44154,45018,45458,45466,45890]

private def codes7 : List ℕ := [
  715,823,1039,1139,2939,3047,3163,3379,5251,5675,7519,7619,7727,7943,9423,9431,
  9715,9807,9815,9931,10039,10223,10255,10347,10355,11011,11143,11435,11659,11699,11983,12083,
  13279,13379,13535,13703,14467,14891,16195,16327,16619,16711,16735,16835,16943,17027,17159,17251,
  17275,17915,18047,18071,18433,18465,18557,18881,18973,19005,19391,19547,19795,20087,20177,20301,
  20411,20519,20625,20717,20807,21275,22031,22063,22163,22247,22355,22571,22967,23147,23543,23759,
  23867,23927,24043,24083,24839,25307,25361,25485,25595,25703,25809,25901,26027,26311,26567,26699,
  27073,27105,27197,27521,27613,27645,28019,28043,28175,28807,28831,28931,29087,29147,29255,29347,
  29371,29471,29755,29911,31199,31639,32387,32579,32711,32827,34007,34123,34415,34447,34655,34939,
  35095,35727,35735,35851,35891,36067,36175,36267,36275,36391,36675,36683,38147,38363,38471,38587,
  40415,40855,42727,42943,43043,43151,44951,45067,45283,45391]

private def codes8 : List ℕ := [
  206,214,498,638,646,1062,1794,1926,2218,2374,4534,5250,5674,6978,7110,7402,
  7542,7966,7990,8698,8830,8854,9266,9274,9690,9714,9930,9970,10254,10354,10578,10870,
  11010,11302,11434,11590,12130,12262,12378,12670,13030,13750,14326,14542,14758,14866,15622,16194,
  16486,16618,16734,16834,16990,17158,17350,17482,17906,17914,18330,18354,18432,18464,18556,18880,
  18972,19004,19254,19438,19546,19870,19930,20086,20176,20300,20624,20716,22030,22062,22162,22354,
  23758,23926,24042,24082,25360,25484,25808,25900,26026,26158,26242,26566,26674,26850,27072,27104,
  27196,27520,27612,27644,27726,27750,28166,28174,28606,28762,28930,29122,29254,29370,29470,29626,
  29910,30490,31246,31354,31570,31786,32362,33082,33442,33726,33826,33982,34522,34654,34810,35094,
  35242,35526,35734,35850,36142,36174,36366,36390,36806,36814,37234,37258,37390,38098,38122,38538,
  38686,38970,39126,40414,40854,41578,43738,43870,44154,44310,45018,45458,45466,45606,45890,45898]

private def codesLate : List ℕ := [
  206,214,498,638,639,646,647,715,755,1039,1062,1063,1139,1794,1926,2218,
  2374,2915,3047,3163,3455,4534,5110,5327,5542,5543,5651,6406,6978,7110,7402,7519,
  7542,7543,7619,7775,7943,7966,7967,7990,7991,8698,8830,8854,9266,9274,9423,9431,
  9690,9714,9715,9807,9815,9930,9931,9970,10039,10223,10254,10255,10331,10347,10354,10355,
  10578,10870,11010,11011,11143,11302,11434,11435,11591,12130,12262,12378,12670,13751,14327,14542,
  14543,14711,14827,14866,14867,15623,16194,16195,16327,16486,16618,16619,16711,16734,16735,16811,
  16834,16835,16943,16990,17027,17158,17159,17251,17275,17350,17482,17906,17914,17915,18047,18071,
  18330,18354,18432,18433,18464,18465,18556,18557,18880,18881,18972,18973,19004,19005,19391,19438,
  19546,19547,19795,19870,20086,20087,20176,20177,20300,20301,20411,20519,20624,20625,20716,20717,
  20914,20915,22750,22751,23362,23363,25198,25199,25360,25361,25484,25485,25595,25703,25808,25809,
  25900,25901,26026,26027,26242,26311,26566,26567,26674,26699,27072,27073,27104,27105,27196,27197,
  27520,27521,27612,27613,27644,27645,27726,27750,28019,28043,28166,28174,28175,28606,28762,28807,
  28831,28930,28931,29087,29122,29147,29254,29255,29303,29347,29370,29371,29470,29471,29626,29755,
  29910,29911,30491,31246,31247,31279,31379,31570,31571,31787,32363,33442,33726,33826,33982,34523,
  34654,34655,34810,34939,35094,35095,35242,35526,35727,35734,35735,35783,35850,35851,35891,36067,
  36142,36174,36175,36267,36275,36366,36390,36391,36675,36683,36806,36814,37234,37258,37390,38098,
  38099,38122,38123,38147,38339,38471,38538,38539,38587,38686,38970,39126,39706,40463,40570,40571,
  40787,41002,41578,42659,42943,43043,43199,43738,43870,44154,44310,44951,45018,45019,45067,45359,
  45391,45458,45459,45466,45467,45606,45890,45898]

private def decodeColour (k : ℕ) : Colour := (k%2==1,k/2%2==1)

private def decode (k : ℕ) : Carry × Shape :=
  let q := k/4
  let t := q/9
  let c := match t/256 with | 0 => Carry.minus | 1 => .minusBack | 2 => .zero | 3 => .plusBack | _ => .plus
  (c,⟨decodeColour (t/64),decodeColour (t/16),decodeColour (t/4),decodeColour t,
      q/3%3,q%3,k/2%2==1,k%2==1⟩)

private abbrev Table := List (Carry × Shape)
private def T6 : Table := codes6.map decode
private def T7 : Table := codes7.map decode
private def T8 : Table := codes8.map decode
private def invariantTable : Table := codesLate.map decode

private def colours : List Colour := [(false,false),(true,false),(false,true),(true,true)]
private def carries : List Carry := [.minus,.minusBack,.zero,.plusBack,.plus]
private theorem every_colour (v : Colour) : v∈colours := by obtain ⟨a,b⟩ := v; cases a <;> cases b <;> decide
private theorem every_carry (v : Carry) : v∈carries := by cases v <;> decide

private def initialValue (a b c d e f : Colour) : ℤ :=
  sign a+sign b*2+sign c*3+sign d*5+sign e*8+sign f*13

private def within (s : Shape) : Bool := decide (s.changesA≤2 ∧ s.changesB≤2)
private def initCheck : Bool :=
  colours.all fun a => colours.all fun b => colours.all fun c =>
  colours.all fun d => colours.all fun e => colours.all fun f =>
  let s := lowShape a b c d e f
  carries.all fun h => !(within s && decide (initialValue a b c d e f+h.weight 6=0)) || T6.contains (h,s)

private def stepCheck (before after : Table) : Bool :=
  before.all fun (lo,s) => colours.all fun v => carries.all fun hi =>
    !(compatible lo hi v && within (s.push v)) || after.contains (hi,s.push v)

private def soundCheck : Bool := invariantTable.all fun (c,s) =>
  !(decide (c=.zero) && s.different && decide (s.cyclicA≤2 ∧ s.cyclicB≤2))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem initial_checked : initCheck = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem transitions_checked : stepCheck T6 T7 = true ∧ stepCheck T7 T8 = true ∧
    stepCheck T8 invariantTable = true ∧ stepCheck invariantTable invariantTable = true ∧ soundCheck=true := by decide +kernel

private def tableAt : ℕ → Table
  | 0 => T6
  | 1 => T7
  | 2 => T8
  | _+3 => invariantTable

private theorem step_checked_at (k : ℕ) : stepCheck (tableAt k) (tableAt (k+1))=true := by
  rcases k with _|k
  · exact transitions_checked.1
  rcases k with _|k
  · exact transitions_checked.2.1
  rcases k with _|k
  · exact transitions_checked.2.2.1
  exact transitions_checked.2.2.2.1

private theorem propagation {before after : Table} (hc : stepCheck before after=true)
    {lo hi : Carry} {s : Shape} {v : Colour} (hm : (lo,s)∈before)
    (hv : compatible lo hi v=true) (hw : within (s.push v)=true) : (hi,s.push v)∈after := by
  unfold stepCheck at hc
  have a := List.all_eq_true.mp hc (lo,s) hm
  have b := List.all_eq_true.mp a v (every_colour v)
  have c := List.all_eq_true.mp b hi (every_carry hi)
  simpa [hv,hw,List.contains_iff_mem] using c

private theorem initial_sound (f : ℕ → Colour) (c : Carry) (hw : within (shape f 0)=true)
    (he : signedSum f 6+c.weight 6=0) : (c,shape f 0)∈T6 := by
  have hv : initialValue (f 0) (f 1) (f 2) (f 3) (f 4) (f 5)+c.weight 6=0 := by
    change ((((((0+sign (f 0)*1)+sign (f 1)*2)+sign (f 2)*3)+sign (f 3)*5)+sign (f 4)*8)+sign (f 5)*13)+c.weight 6=0 at he
    simpa [initialValue] using he
  have a := List.all_eq_true.mp initial_checked (f 0) (every_colour _)
  have b := List.all_eq_true.mp a (f 1) (every_colour _)
  have t := List.all_eq_true.mp b (f 2) (every_colour _)
  have d := List.all_eq_true.mp t (f 3) (every_colour _)
  have e := List.all_eq_true.mp d (f 4) (every_colour _)
  have g := List.all_eq_true.mp e (f 5) (every_colour _)
  have z := List.all_eq_true.mp g c (every_carry _)
  change within (lowShape (f 0) (f 1) (f 2) (f 3) (f 4) (f 5))=true at hw
  simpa [shape,hv,hw,List.contains_iff_mem] using z

private theorem known (f : ℕ → Colour) (k : ℕ) (c : Carry)
    (hw : within (shape f k)=true) (h : signedSum f (k+6)+c.weight (k+6)=0) :
    (c,shape f k)∈ tableAt k := by
  induction k generalizing c with
  | zero => exact initial_sound f c hw h
  | succ k ih =>
    obtain ⟨lo,hcomp,hprev⟩ := downward f (k+6) c h
    have w := hw
    simp only [shape,within,decide_eq_true_eq,Shape.push] at w
    have hbefore : within (shape f k)=true := by
      simp only [within,decide_eq_true_eq]
      omega
    exact propagation (step_checked_at k) (ih lo hbefore hprev) hcomp hw

/-- For every pair of bit labels with equal sums on the first `k+9` distinct
Fibonacci numbers, if each bit changes at most twice around the constructed
circle, then the two labels are identical at every number. -/
theorem checked_fibonacci_circle (f : ℕ → Colour) (k : ℕ)
    (ha : (shape f (k+3)).cyclicA≤2) (hb : (shape f (k+3)).cyclicB≤2)
    (he : signedSum f (k+9)=0) : (shape f (k+3)).different=false := by
  have hw : within (shape f (k+3))=true := by
    simp only [within,decide_eq_true_eq]
    unfold Shape.cyclicA at ha
    unfold Shape.cyclicB at hb
    omega
  have hm := known f (k+3) .zero hw (by simpa [Carry.weight,Carry.coeffs] using he)
  have hchecked := List.all_eq_true.mp transitions_checked.2.2.2.2 (.zero,shape f (k+3)) hm
  simpa [ha,hb] using hchecked

#print axioms checked_fibonacci_circle

end FibonacciBarrycade

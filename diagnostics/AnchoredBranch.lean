import PEqualNP.Defs
set_option maxHeartbeats 5000000
set_option maxRecDepth 8192
namespace AnchoredBranch9737
abbrev Node := Bool × Nat × Nat
abbrev Store := Nat → Bool
def below (v w : Store) : Prop := ∀i,v i=true → w i=true
def gate (g : Node) (j : Nat) (v m : Store) :=
  let a := v g.2.1 || m (2*j)
  let b := v g.2.2 || m (2*j+1)
  if g.1 then a || b else a && b
theorem gate_mon (g : Node) (j : Nat) {v w m n : Store}
    (hx : below v w) (hy : below m n) :
    gate g j v m = true → gate g j w n = true := by
  rcases g with ⟨b,i,k⟩
  cases b <;> simp [gate,Bool.or_eq_true,Bool.and_eq_true]
  all_goals unfold below at hx hy
  all_goals aesop
def run : List Node → Nat → Store → Store → Store
  | [],_,v,_ => v
  | g::gs,j,v,m => run gs (j+1) (fun i => if i=25+j then gate g j v m else v i) m
theorem run_mon (gs : List Node) (j : Nat) {a b m n : Store}
    (h : below a b) (hm : below m n) : below (run gs j a m) (run gs j b n) := by
  induction gs generalizing j a b with
  | nil => exact h
  | cons g gs ih =>
    apply ih (j+1)
    intro i hi
    by_cases e : i=25+j
    · simpa [e] using gate_mon g j h hm (by simpa [e] using hi)
    · simpa [e] using h i (by simpa [e] using hi)
def net : List Node := [(true,3,5),(true,11,25),(true,2,26),(false,14,27),(true,9,11),(true,4,29),(true,8,30),(false,20,31),(true,7,10),(true,3,33),(true,8,34),(false,19,35),(true,10,11),(true,6,37),(true,0,38),(false,22,39),(true,1,12),(true,7,41),(true,11,42),(false,23,43),(true,5,6),(true,1,45),(true,8,46),(false,17,47),(true,10,12),(true,5,49),(true,9,50),(false,21,51),(true,4,12),(true,6,53),(true,3,54),(false,15,55),(true,0,2),(true,8,12),(true,57,58),(false,24,59),(true,5,7),(true,0,61),(true,4,62),(false,16,63),(true,2,7),(true,9,65),(true,6,66),(false,18,67),(true,56,60),(true,28,44),(true,68,70),(true,48,71),(true,52,72),(true,40,64),(true,32,73),(true,36,69),(true,74,75),(true,76,77)]
def singleton (i : Nat) : Store := fun j => decide (i=j)
def input (r : Nat) : Store := fun i => if i<25 then r.testBit i else false
def output (r : Nat) (m : Store) := run net 0 (input r) m 78
def target (x : Fin 25 → Bool) := (x 0 && x 16) || (x 0 && x 22) || (x 0 && x 24) || (x 1 && x 13) || (x 1 && x 17) || (x 1 && x 23) || (x 2 && x 13) || (x 2 && x 14) || (x 2 && x 18) || (x 2 && x 24) || (x 3 && x 14) || (x 3 && x 15) || (x 3 && x 19) || (x 4 && x 13) || (x 4 && x 15) || (x 4 && x 16) || (x 4 && x 20) || (x 5 && x 14) || (x 5 && x 16) || (x 5 && x 17) || (x 5 && x 21) || (x 6 && x 15) || (x 6 && x 17) || (x 6 && x 18) || (x 6 && x 22) || (x 7 && x 16) || (x 7 && x 18) || (x 7 && x 19) || (x 7 && x 23) || (x 8 && x 17) || (x 8 && x 19) || (x 8 && x 20) || (x 8 && x 24) || (x 9 && x 18) || (x 9 && x 20) || (x 9 && x 21) || (x 10 && x 13) || (x 10 && x 19) || (x 10 && x 21) || (x 10 && x 22) || (x 11 && x 14) || (x 11 && x 20) || (x 11 && x 22) || (x 11 && x 23) || (x 12 && x 15) || (x 12 && x 21) || (x 12 && x 23) || (x 12 && x 24)
def targetAt (r : Nat) := target (fun i => r.testBit i.val)
def witnesses : Fin 108 → Nat := ![33546240,33546240,33546240,33546240,33546240,33546240,15337,33546240,33546240,33546240,33546240,33546240,33546240,33546240,15337,33546240,33546240,33546240,33546240,33546240,33546240,33546240,15337,33546240,33546240,33546240,33546240,33546240,33546240,33546240,15337,33546240,33546240,33546240,33546240,33546240,33546240,33546240,15337,33546240,33546240,33546240,33546240,33546240,33546240,33546240,15337,33546240,33546240,33546240,33546240,33546240,33546240,33546240,15337,33546240,33546240,33546240,33546240,33546240,33546240,33546240,15337,33546240,33546240,33546240,33546240,33546240,33546240,33546240,15337,33546240,33546240,33546240,33546240,33546240,33546240,33546240,15337,33546240,33546240,33546240,33546240,33546240,33546240,33546240,15337,33546240,15337,15337,15337,15337,15337,15337,15337,15337,15337,15337,15337,15337,15337,15337,15337,15337,15337,15337,15337,15337]
theorem onePort : ∀i : Fin 108,
   (witnesses i).testBit 13=true ∧ targetAt (witnesses i)=false ∧
   output (witnesses i) (singleton i.val)=true := by decide +kernel
theorem excludes (m : Store) (legal : ∀ i,m i=true → i<108) :
    ∃ r : Nat,r.testBit 13=true ∧ output r m ≠ targetAt r := by
  classical
  by_cases h : ∃i,m i=true
  · obtain ⟨i,hi⟩ := h
    let u : Fin 108 := ⟨i,legal i hi⟩
    obtain ⟨setBit,neg,pos⟩ := onePort u
    have grows : below (singleton i) m := by
      intro j hj
      have e : i=j := by simpa [singleton] using hj
      exact e ▸ hi
    have marked : output (witnesses u) m=true :=
      run_mon net 0 (fun _ hh => hh) grows 78 pos
    exact ⟨witnesses u,setBit,by simp [marked,neg]⟩
  · have empty : m=fun _ => false := by
      funext i
      cases e : m i with
      | false => rfl
      | true => exact (h ⟨i,e⟩).elim
    rw [empty]
    exact ⟨8194,by decide +kernel⟩
end AnchoredBranch9737

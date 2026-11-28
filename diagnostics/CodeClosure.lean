import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_10025.SplitPencil
abbrev P := Fin 25
abbrev L := Fin 30
abbrev Box := Finset P × Finset L
def rows : List Nat := [34636833, 35719234, 37884036, 42213640, 50872848, 69345793, 71581730, 76022852, 83921032, 68227344, 138938625, 142643714, 151068708, 135413832, 136578192, 276906113, 285345026, 269748740, 271061032, 272670800, 553914433, 538452098, 539017476, 541132296, 545392688]
def inc (p : P) (l : L) := (rows.getD p.val 0).testBit l.val
def lineData : Array (Array L) := #[#[0,25,25,25,25,0,5,10,15,20,0,15,5,20,10,0,10,20,5,15,0,20,15,10,5],#[25,1,25,25,25,21,1,6,11,16,11,1,16,6,21,16,1,11,21,6,6,1,21,16,11],#[25,25,2,25,25,17,22,2,7,12,22,12,2,17,7,7,17,2,12,22,12,7,2,22,17],#[25,25,25,3,25,13,18,23,3,8,8,23,13,3,18,23,8,18,3,13,18,13,8,3,23],#[25,25,25,25,4,9,14,19,24,4,19,9,24,14,4,14,24,9,19,4,24,19,14,9,4],#[0,21,17,13,9,0,26,26,26,26,0,9,13,17,21,0,17,9,21,13,0,13,21,9,17],#[5,1,22,18,14,26,1,26,26,26,22,1,5,14,18,14,1,18,5,22,18,1,14,22,5],#[10,6,2,23,19,26,26,2,26,26,19,23,2,6,10,23,10,2,19,6,6,19,2,10,23],#[15,11,7,3,24,26,26,26,3,26,11,15,24,3,7,7,24,11,3,15,24,7,15,3,11],#[20,16,12,8,4,26,26,26,26,4,8,12,16,20,4,16,8,20,12,4,12,20,8,16,4],#[0,11,22,8,19,0,22,19,11,8,0,27,27,27,27,0,8,11,19,22,0,19,8,22,11],#[15,1,12,23,9,9,1,23,15,12,27,1,27,27,27,23,1,9,12,15,12,1,15,9,23],#[5,16,2,13,24,13,5,2,24,16,27,27,2,27,27,16,24,2,5,13,24,13,2,16,5],#[20,6,17,3,14,17,14,6,3,20,27,27,27,3,27,14,17,20,3,6,6,20,14,3,17],#[10,21,7,18,4,21,18,10,7,4,27,27,27,27,4,7,10,18,21,4,18,7,21,10,4],#[0,16,7,23,14,0,14,23,7,16,0,23,16,14,7,0,28,28,28,28,0,7,14,16,23],#[10,1,17,8,24,17,1,10,24,8,8,1,24,17,10,28,1,28,28,28,24,1,8,10,17],#[20,11,2,18,9,9,18,2,11,20,11,9,2,20,18,28,28,2,28,28,18,20,2,9,11],#[5,21,12,3,19,21,5,19,3,12,19,12,5,3,21,28,28,28,3,28,12,19,21,3,5],#[15,6,22,13,4,13,22,6,15,4,22,15,13,6,4,28,28,28,28,4,6,13,15,22,4],#[0,6,12,18,24,0,18,6,24,12,0,12,24,6,18,0,24,18,12,6,0,29,29,29,29],#[20,1,7,13,19,13,1,19,7,20,19,1,13,20,7,7,1,20,19,13,29,1,29,29,29],#[15,21,2,8,14,21,14,2,15,8,8,15,2,14,21,14,8,2,21,15,29,29,2,29,29],#[10,16,22,3,9,9,22,10,3,16,22,9,16,3,10,16,10,9,3,22,29,29,29,3,29],#[5,11,17,23,4,17,5,23,11,4,11,23,5,17,4,23,17,11,5,4,29,29,29,29,4]]
def through (p q : P) := (lineData[p.val]!)[q.val]!
set_option maxHeartbeats 0
theorem joins : ∀ p q : P,p≠q → inc p (through p q)=true ∧ inc q (through p q)=true := by decide +kernel
theorem uniqueLine : ∀ (p q : P) (l : L),p≠q → inc p l=true → inc q l=true → l=through p q := by
 decide +kernel
theorem alternatives : ∀ p q : P,p≠q → ∃ l : L,inc p l=false ∧ inc q l=true := by decide +kernel
def blank {k : Nat} (R : Fin k → Box) := ∀ t,∀ q∈(R t).1,∀ l∈(R t).2,inc q l=false
def covers {k : Nat} (R : Fin k → Box) := ∀ p l,inc p l=false → ∃ t,p∈(R t).1 ∧ l∈(R t).2
def shared {k : Nat} (R : Fin k → Box) (A : Finset (Fin k)) (q : P) := ∀ t∈A,q∈(R t).1
theorem splitTest {k} (R : Fin k → Box) (legal : blank R) (complete : covers R) {p : P}
    {A B : Finset (Fin k)} (div : ∀ t,p∈(R t).1 → t∈A ∨ t∈B)
    {q r : P} (left : shared R A q) (right : shared R B r) (l : L)
    (ql : inc q l=true) (rl : inc r l=true) : inc p l=true := by
 cases pl : inc p l with
 | true => rfl
 | false =>
   obtain ⟨t,pt,lt⟩ := complete p l pl
   rcases div t pt with ha|hb
   · have bad := legal t q (left t ha) l lt
     rw [ql] at bad
     contradiction
   · have bad := legal t r (right t hb) l lt
     rw [rl] at bad
     contradiction


theorem unionForcesLine {k} (R : Fin k → Box) (legal : blank R) (complete : covers R)
    {p q r : P} (qr : q≠r)
    (contained : ∀ t,p∈(R t).1 → q∈(R t).1 ∨ r∈(R t).1) : inc p (through q r)=true := by
 cases pl : inc p (through q r) with
 | true => rfl
 | false =>
   obtain ⟨t,pt,lt⟩ := complete p (through q r) pl
   rcases contained t pt with h|h
   · have bad := legal t q h _ lt
     rw [(joins q r qr).1] at bad
     contradiction
   · have bad := legal t r h _ lt
     rw [(joins q r qr).2] at bad
     contradiction

theorem closureOnLine {k} (R : Fin k → Box) (legal : blank R) (complete : covers R)
    (l : L) {p : P}
    (coveredCode : ∀ t,p∈(R t).1 → ∃ q∈(R t).1,inc q l=true) : inc p l=true := by
 cases pl : inc p l with
 | true => rfl
 | false =>
   obtain ⟨t,pt,lt⟩ := complete p l pl
   obtain ⟨q,qt,on⟩ := coveredCode t pt
   have bad := legal t q qt l lt
   rw [on] at bad
   contradiction

theorem eachLineFive : ∀ l : L,(Finset.univ.filter (fun p : P => inc p l = true)).card=5 := by
 decide +kernel

theorem unionBound {k} (R : Fin k → Box) (legal : blank R) (complete : covers R)
    {q r : P} (qr : q≠r) (S : Finset P)
    (sub : ∀ p∈S,∀ t,p∈(R t).1 → q∈(R t).1 ∨ r∈(R t).1) : S.card≤5 := by
 have h : S ⊆ Finset.univ.filter (fun p : P => inc p (through q r)=true) := by
   intro p hp
   exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,unionForcesLine R legal complete qr (sub p hp)⟩
 exact (Finset.card_le_card h).trans_eq (eachLineFive _)
end PEqualNP.Outside.L_meta_10025.SplitPencil

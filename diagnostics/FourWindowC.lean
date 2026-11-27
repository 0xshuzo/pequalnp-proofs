import Mathlib
import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_8009.Face
abbrev Pt := Fin 13
def Inc (p l : Pt) : Prop := p=l ∨ p=l+1 ∨ p=l+3 ∨ p=l+9
instance (p l : Pt) : Decidable (Inc p l) := by unfold Inc; infer_instance
def Arc (P : Finset Pt) := ∀ l : Pt, (P.filter (fun p => Inc p l)).card≤2
def avoid (P : Finset Pt) := Finset.univ.filter (fun l : Pt => ∀ p∈P, ¬Inc p l)
def rows : Array Nat := #[115585,316033,346753,362113,608545,623875,808969,824337,1102401,1133089,1333761,1348113,1378821,1595425,1609747,1640483,1841169,2150593,2196611,2379913,2397313,2425989,2641961,2659331,2688035,2888713,3166305,3182659,3211303,3674147,4243905,4278657,4292995,4475017,4524165,4737289,4751635,4786435,4982809,5275731,5310471,5507093,5769235,6308041,6324419,6357127,6553741,7340103,16827201,16859937,16877313,17073681,17106437,17318185,17335569,17368353,17564697,17842785,17859153,17891877,18088469,18890857,18940965,19137549,19399721,19923045,20988233,21004625,21233693,21496089,22020181,23068749]
def ix : Array (Fin 72) := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,4,8,17,30,0,48,0,0,0,0,0,0,1,5,8,17,30,0,48,0,0,0,0,0,0,2,4,9,18,31,0,49,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,1,2,0,1,6,10,19,33,0,51,0,0,4,5,4,0,6,4,13,22,35,0,53,0,0,8,8,9,0,10,13,8,26,39,0,57,0,0,17,17,18,0,19,22,26,17,43,0,61,0,0,30,30,31,0,33,35,39,43,30,0,66,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,48,48,49,0,51,53,57,61,66,0,48,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,5,5,0,0,5,14,18,32,0,0,0,0,0,5,5,0,0,5,15,18,32,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,5,5,0,0,5,14,23,36,0,0,0,0,0,14,15,0,0,14,14,27,39,0,0,0,0,0,18,18,0,0,23,27,18,44,0,0,0,0,0,32,32,0,0,36,39,44,32,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,12,0,12,0,12,21,34,0,52,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,12,0,12,0,12,21,34,0,52,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,12,0,12,0,12,28,40,0,59,0,0,0,0,21,0,21,0,28,21,45,0,62,0,0,0,0,34,0,34,0,40,45,34,0,68,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,52,0,52,0,59,62,68,0,52,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,6,0,0,0,6,6,0,19,33,0,53,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,6,0,0,0,6,6,0,19,33,0,56,0,0,6,0,0,0,6,6,0,22,35,0,53,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,19,0,0,0,19,22,0,19,43,0,61,0,0,33,0,0,0,33,35,0,43,33,0,66,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,53,0,0,0,56,53,0,61,66,0,53,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,7,0,0,7,7,11,0,36,0,51,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,7,0,0,7,7,11,0,38,0,51,0,0,0,7,0,0,7,7,14,0,36,0,54,0,0,0,11,0,0,11,14,11,0,39,0,58,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,36,0,0,38,36,39,0,36,0,67,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,51,0,0,51,54,58,0,67,0,51,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4,0,4,0,0,4,9,22,0,0,49,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4,0,4,0,0,4,9,24,0,0,49,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4,0,4,0,0,4,13,22,0,0,53,0,0,9,0,9,0,0,13,9,26,0,0,57,0,0,22,0,24,0,0,22,26,22,0,0,61,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,49,0,49,0,0,53,57,61,0,0,49,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,8,8,0,0,0,0,8,17,30,0,48,0,0,8,8,0,0,0,0,8,17,30,0,48,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,8,8,0,0,0,0,8,26,39,0,57,0,0,17,17,0,0,0,0,26,17,43,0,61,0,0,30,30,0,0,0,0,39,43,30,0,66,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,48,48,0,0,0,0,57,61,66,0,48,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,17,30,0,0,0,0,0,0,0,0,1,0,0,17,30,0,0,0,0,0,0,0,0,2,0,0,18,31,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,1,2,0,1,0,0,19,33,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,17,17,18,0,19,0,0,17,43,0,0,0,0,30,30,31,0,33,0,0,43,30,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4,0,0,30,0,48,0,0,0,0,0,0,0,5,0,0,30,0,48,0,0,0,0,0,0,0,4,0,0,31,0,49,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4,5,4,0,0,4,0,0,35,0,53,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,30,30,31,0,0,35,0,0,30,0,66,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,48,48,49,0,0,53,0,0,66,0,48,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,8,0,0,0,48,0,0,0,0,0,0,1,0,8,0,0,0,48,0,0,0,0,0,0,2,0,9,0,0,0,49,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,1,2,0,1,0,10,0,0,0,51,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,8,8,9,0,10,0,8,0,0,0,57,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,48,48,49,0,51,0,57,0,0,0,48,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,3,3,0,3,5,0,18,0,0,50,0,0,0,3,3,0,3,5,0,18,0,0,50,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,3,3,0,3,7,0,20,0,0,51,0,0,0,5,5,0,7,5,0,23,0,0,54,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,18,18,0,20,23,0,18,0,0,62,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,50,50,0,51,54,0,62,0,0,50,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,0,2,0,2,4,9,0,31,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,0,2,0,2,4,9,0,31,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,0,2,0,2,6,10,0,33,0,0,0,0,4,0,4,0,6,4,13,0,35,0,0,0,0,9,0,9,0,10,13,9,0,40,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,31,0,31,0,33,35,40,0,31,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,1,0,0,1,6,8,17,0,0,0,0,0,1,1,0,0,1,7,8,17,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,1,0,0,1,6,10,19,0,0,0,0,0,6,7,0,0,6,6,13,22,0,0,0,0,0,8,8,0,0,10,13,8,26,0,0,0,0,0,17,17,0,0,19,22,26,17,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def index (a m b : Pt) : Fin 72 := ix[169*a.val+13*m.val+b.val]?.getD 0
def code (k : Fin 72) : Nat := rows[k.val]?.getD 0
def P (k : Fin 72) : Finset Pt := Finset.univ.filter (fun p : Pt => (code k).testBit p.val)
def L (k : Fin 72) : Finset Pt := Finset.univ.filter (fun l : Pt => (code k).testBit (13+l.val))
instance (S : Finset Pt) : Decidable (Arc S) := by unfold Arc; infer_instance
set_option maxRecDepth 9000 in
set_option maxHeartbeats 3000000 in
theorem shape : ∀ k : Fin 72, (P k).card=4 ∧ Arc (P k) ∧ 0∈P k ∧ L k⊆avoid (P k) := by decide +kernel
set_option maxRecDepth 9000 in
set_option maxHeartbeats 3000000 in
private theorem row0 : ∀ m b : Pt, ¬Inc 0 m → ¬Inc 0 b → ¬Inc 0 m → ¬Inc 0 b →
    let k := index 0 m b
    (code k).testBit 0=true ∧ (code k).testBit (13+m.val)=true ∧ (code k).testBit (13+b.val)=true := by
  have table : ∀ m b : Pt, (¬Inc 0 m ∧ ¬Inc 0 b) →
      let k := index 0 m b
      (code k).testBit 0=true ∧ (code k).testBit (13+m.val)=true ∧ (code k).testBit (13+b.val)=true := by decide +kernel
  intro m b hm hb _ _
  exact table m b ⟨hm,hb⟩
set_option maxRecDepth 9000 in
set_option maxHeartbeats 3000000 in
private theorem row1 : ∀ m b : Pt, ¬Inc 0 m → ¬Inc 0 b → ¬Inc 1 m → ¬Inc 1 b →
    let k := index 1 m b
    (code k).testBit 1=true ∧ (code k).testBit (13+m.val)=true ∧ (code k).testBit (13+b.val)=true := by decide +kernel
set_option maxRecDepth 9000 in
set_option maxHeartbeats 3000000 in
private theorem row2 : ∀ m b : Pt, ¬Inc 0 m → ¬Inc 0 b → ¬Inc 2 m → ¬Inc 2 b →
    let k := index 2 m b
    (code k).testBit 2=true ∧ (code k).testBit (13+m.val)=true ∧ (code k).testBit (13+b.val)=true := by decide +kernel
set_option maxRecDepth 9000 in
set_option maxHeartbeats 3000000 in
private theorem row3 : ∀ m b : Pt, ¬Inc 0 m → ¬Inc 0 b → ¬Inc 3 m → ¬Inc 3 b →
    let k := index 3 m b
    (code k).testBit 3=true ∧ (code k).testBit (13+m.val)=true ∧ (code k).testBit (13+b.val)=true := by decide +kernel
set_option maxRecDepth 9000 in
set_option maxHeartbeats 3000000 in
private theorem row4 : ∀ m b : Pt, ¬Inc 0 m → ¬Inc 0 b → ¬Inc 4 m → ¬Inc 4 b →
    let k := index 4 m b
    (code k).testBit 4=true ∧ (code k).testBit (13+m.val)=true ∧ (code k).testBit (13+b.val)=true := by decide +kernel
set_option maxRecDepth 9000 in
set_option maxHeartbeats 3000000 in
private theorem row5 : ∀ m b : Pt, ¬Inc 0 m → ¬Inc 0 b → ¬Inc 5 m → ¬Inc 5 b →
    let k := index 5 m b
    (code k).testBit 5=true ∧ (code k).testBit (13+m.val)=true ∧ (code k).testBit (13+b.val)=true := by decide +kernel
set_option maxRecDepth 9000 in
set_option maxHeartbeats 3000000 in
private theorem row6 : ∀ m b : Pt, ¬Inc 0 m → ¬Inc 0 b → ¬Inc 6 m → ¬Inc 6 b →
    let k := index 6 m b
    (code k).testBit 6=true ∧ (code k).testBit (13+m.val)=true ∧ (code k).testBit (13+b.val)=true := by decide +kernel
set_option maxRecDepth 9000 in
set_option maxHeartbeats 3000000 in
private theorem row7 : ∀ m b : Pt, ¬Inc 0 m → ¬Inc 0 b → ¬Inc 7 m → ¬Inc 7 b →
    let k := index 7 m b
    (code k).testBit 7=true ∧ (code k).testBit (13+m.val)=true ∧ (code k).testBit (13+b.val)=true := by decide +kernel
set_option maxRecDepth 9000 in
set_option maxHeartbeats 3000000 in
private theorem row8 : ∀ m b : Pt, ¬Inc 0 m → ¬Inc 0 b → ¬Inc 8 m → ¬Inc 8 b →
    let k := index 8 m b
    (code k).testBit 8=true ∧ (code k).testBit (13+m.val)=true ∧ (code k).testBit (13+b.val)=true := by decide +kernel
set_option maxRecDepth 9000 in
set_option maxHeartbeats 3000000 in
private theorem row9 : ∀ m b : Pt, ¬Inc 0 m → ¬Inc 0 b → ¬Inc 9 m → ¬Inc 9 b →
    let k := index 9 m b
    (code k).testBit 9=true ∧ (code k).testBit (13+m.val)=true ∧ (code k).testBit (13+b.val)=true := by decide +kernel
set_option maxRecDepth 9000 in
set_option maxHeartbeats 3000000 in
private theorem row10 : ∀ m b : Pt, ¬Inc 0 m → ¬Inc 0 b → ¬Inc 10 m → ¬Inc 10 b →
    let k := index 10 m b
    (code k).testBit 10=true ∧ (code k).testBit (13+m.val)=true ∧ (code k).testBit (13+b.val)=true := by decide +kernel
set_option maxRecDepth 9000 in
set_option maxHeartbeats 3000000 in
private theorem row11 : ∀ m b : Pt, ¬Inc 0 m → ¬Inc 0 b → ¬Inc 11 m → ¬Inc 11 b →
    let k := index 11 m b
    (code k).testBit 11=true ∧ (code k).testBit (13+m.val)=true ∧ (code k).testBit (13+b.val)=true := by decide +kernel
set_option maxRecDepth 9000 in
set_option maxHeartbeats 3000000 in
private theorem row12 : ∀ m b : Pt, ¬Inc 0 m → ¬Inc 0 b → ¬Inc 12 m → ¬Inc 12 b →
    let k := index 12 m b
    (code k).testBit 12=true ∧ (code k).testBit (13+m.val)=true ∧ (code k).testBit (13+b.val)=true := by decide +kernel
theorem coverage (a m b : Pt) (zm : ¬Inc 0 m) (zb : ¬Inc 0 b) (am : ¬Inc a m) (ab : ¬Inc a b):
    let k := index a m b
    a∈P k ∧ m∈L k ∧ b∈L k := by
  change _ ∧ _ ∧ _
  simp only [P,L,Finset.mem_filter,Finset.mem_univ,true_and]
  have raw : ∀ i : Pt, (∀ m b : Pt, ¬Inc 0 m → ¬Inc 0 b → ¬Inc i m → ¬Inc i b →
      let k := index i m b
      (code k).testBit i.val=true ∧ (code k).testBit (13+m.val)=true ∧ (code k).testBit (13+b.val)=true) := by
    intro i
    fin_cases i
    · exact row0
    · exact row1
    · exact row2
    · exact row3
    · exact row4
    · exact row5
    · exact row6
    · exact row7
    · exact row8
    · exact row9
    · exact row10
    · exact row11
    · exact row12
  exact raw a m b zm zb am ab

def shift (t : Pt) (S : Finset Pt) := S.image (fun p => p+t)
theorem shifted : ∀ t p l : Pt, Inc (p+t) (l+t) ↔ Inc p l := by decide
theorem mix (t p l : Pt) : Inc (p+t) l ↔ Inc p (l-t) := by
  simpa using shifted t p (l-t)
theorem moved (t : Pt) (S : Finset Pt) : (shift t S).card=S.card :=
  Finset.card_image_of_injective _ (fun _ _ h => add_right_cancel h)
theorem arcShift (t : Pt) (S : Finset Pt) (h : Arc S) : Arc (shift t S) := by
  intro l
  have eq : (shift t S).filter (fun p => Inc p l) = shift t (S.filter (fun p => Inc p (l-t))) := by
    ext p
    simp only [shift,Finset.mem_filter,Finset.mem_image]
    constructor
    · rintro ⟨⟨q,hq,rfl⟩,inc⟩
      exact ⟨q,⟨hq,(mix t q l).mp inc⟩,rfl⟩
    · rintro ⟨q,⟨hq,inc⟩,rfl⟩
      exact ⟨⟨q,hq,rfl⟩,(mix t q l).mpr inc⟩
  rw [eq,moved]
  exact h (l-t)

theorem fourCover (q m a b : Pt) (qm : ¬Inc q m) (qb : ¬Inc q b) (am : ¬Inc a m) (ab : ¬Inc a b) :
    ∃ S : Finset Pt, S.card=4 ∧ Arc S ∧ q∈S ∧ a∈S ∧ m∈avoid S ∧ b∈avoid S := by
  let k := index (a-q) (m-q) (b-q)
  have red (p l : Pt) : Inc (p-q) (l-q) ↔ Inc p l := by simpa using (shifted q (p-q) (l-q)).symm
  obtain ⟨pa,pm,pb⟩ := coverage (a-q) (m-q) (b-q)
    (by simpa using (red q m).not.mpr qm) (by simpa using (red q b).not.mpr qb)
    ((red a m).not.mpr am) ((red a b).not.mpr ab)
  obtain ⟨sz,arc,zero,dis⟩ := shape k
  have pIn (p : Pt) (h : p-q∈P k) : p∈shift q (P k) :=
    Finset.mem_image.mpr ⟨p-q,h,sub_add_cancel _ _⟩
  have lIn (l : Pt) (h : l-q∈L k) : l∈avoid (shift q (P k)) := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    intro p hp
    obtain ⟨p0,hp0,rfl⟩ := Finset.mem_image.mp hp
    exact fun active => (Finset.mem_filter.mp (dis h)).2 p0 hp0 ((mix q p0 l).mp active)
  exact ⟨shift q (P k),(moved q _).trans sz,arcShift q _ arc,
    pIn q (by simpa using zero),pIn a pa,lIn m pm,lIn b pb⟩

end PEqualNP.Outside.L_meta_8009.Face

namespace PEqualNP.Outside.L_meta_8009.Physical
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Relation

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wiresFrom_append (gs rest : List Gate) (w : List Bool) :
    wiresFrom (gs ++ rest) w = wiresFrom rest (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    change wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) = _
    rw [ht]; simp

theorem wiresFrom_length (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

theorem prefix_val (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

def val {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : ℕ) : Bool :=
  (wiresFrom C.gates (List.ofFn x)).getD i false

theorem val_input {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : Fin n) :
    val C x i.val = x i := by
  rw [val, prefix_val _ _ _ (by simp), List.getD_eq_getElem _ _ (by simp)]
  simp

theorem val_beyond {n : ℕ} (C : Circuit) (x : Fin n → Bool) {i : ℕ}
    (hi : n + C.gates.length ≤ i) : val C x i = false := by
  rw [val, List.getD_eq_default _ _ (by simpa [wiresFrom_length] using hi)]

def operand {n : ℕ} (C : Circuit) (x : Fin n → Bool) (j i : ℕ) : Bool :=
  if i < j then val C x i else false

theorem val_gate {n : ℕ} (C : Circuit) (x : Fin n → Bool) {p : ℕ} {g : Gate}
    (hp : C.gates[p]? = some g) :
    val C x (n+p) = g.op.eval (g.inputs.map (operand C x (n+p))) := by
  obtain ⟨hb, heq⟩ := List.getElem?_eq_some_iff.1 hp
  have hsplit : C.gates = (C.gates.take p ++ [g]) ++ C.gates.drop (p+1) := by
    conv_lhs => rw [← List.take_append_drop (p+1) C.gates]
    rw [List.take_succ_eq_append_getElem hb, heq]
  let w := wiresFrom (C.gates.take p) (List.ofFn x)
  have hw : w.length = n+p := by
    simp [w, wiresFrom_length, List.length_take, Nat.min_eq_left hb.le]
  have hread (i : ℕ) : w.getD i false = operand C x (n+p) i := by
    by_cases hi : i < n+p
    · have hv : val C x i = w.getD i false := by
        unfold val
        conv_lhs => rw [hsplit, List.append_assoc, wiresFrom_append]
        exact prefix_val _ w i (hw.symm ▸ hi)
      simp only [operand, ite_eq_left hi, hv]
    · rw [operand, ite_eq_right hi, List.getD_eq_default _ _ (by omega)]
  have he : (g.inputs.map fun i => w.getD i false) = g.inputs.map (operand C x (n+p)) :=
    List.map_congr_left fun i _ => hread i
  unfold val
  conv_lhs => rw [hsplit, List.append_assoc, wiresFrom_append]
  change (wiresFrom (C.gates.drop (p+1))
    (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])).getD (n+p) false = _
  rw [prefix_val _ _ _ (by simp [hw]), ← hw, he]
  simp [hw]

section Circ2

variable {n : ℕ} {C : Circuit}

theorem acts_mono (hC : Monotone2 C) {x y : Fin n → Bool}
    (hxy : ∀ i, x i = true → y i = true) :
    ∀ j, val C x j = true → val C y j = true := by
  intro j
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    intro hj
    by_cases hin : j < n
    · let i : Fin n := ⟨j, hin⟩
      simpa only [← val_input C x i, ← val_input C y i] using hxy i (by
        simpa only [← val_input C x i] using hj)
    by_cases hgt : n + C.gates.length ≤ j
    · rw [val_beyond C x hgt] at hj
      contradiction
    obtain ⟨p, hp, rfl⟩ : ∃ p, p < C.gates.length ∧ j = n+p := ⟨j-n, by omega, by omega⟩
    let g := C.gates[p]
    have hg : C.gates[p]? = some g := List.getElem?_eq_some_iff.2 ⟨hp, rfl⟩
    have hgate := (hC g (List.mem_of_getElem? hg)).1
    have hm (a : ℕ) : operand C x (n+p) a = true → operand C y (n+p) a = true := by
      by_cases ha : a < n+p
      · simp only [operand, ite_eq_left ha]
        exact ih a ha
      · simp [operand, ha]
    rw [val_gate C x hg] at hj
    rw [val_gate C y hg]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hgate
    rcases hgate with h | h
    · simp only [h, GateOp.eval, List.all_map, Function.comp_apply, id, List.all_eq_true] at hj ⊢
      exact fun a ha => hm a (hj a ha)
    · simp only [h, GateOp.eval, List.any_map, Function.comp_apply, id, List.any_eq_true] at hj ⊢
      obtain ⟨a, ha, he⟩ := hj
      exact ⟨a, ha, hm a he⟩


end Circ2

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def input {N : ℕ} (P L : Finset (Fin N)) : Fin (N+N) → Bool :=
  Fin.addCases (fun p => decide (p∈P)) (fun l => decide (l∈L))

def Hit {N : ℕ} (I : Fin N → Fin N → Prop) (P L : Finset (Fin N)) : Prop :=
  ∃ p ∈ P, ∃ l ∈ L, I p l

theorem input_l {N} (P L : Finset (Fin N)) (p : Fin N) :
    input P L (Fin.castAdd N p) = decide (p∈P) := Fin.addCases_left ..
theorem input_r {N} (P L : Finset (Fin N)) (l : Fin N) :
    input P L (Fin.natAdd N l) = decide (l∈L) := Fin.addCases_right ..

theorem wire_mono {N} {C : Circuit} (hm : Monotone2 C) {P P' L L' : Finset (Fin N)}
    (hp : P ⊆ P') (hl : L ⊆ L') (w : ℕ) :
    val C (input P L) w = true → val C (input P' L') w = true := by
  apply acts_mono hm
  intro i
  refine Fin.addCases ?_ ?_ i
  · intro p
    simp only [input_l,decide_eq_true_eq]
    exact fun h => hp h
  · intro l
    simp only [input_r,decide_eq_true_eq]
    exact fun h => hl h

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open Face

def test (C : Circuit) := ∀ S : Finset Pt, S.card=4 → Arc S →
    circuitFun 26 C (input S (avoid S))=false

def agree (C : Circuit) := ∀ p l : Pt, Inc p l →
    circuitFun 26 C (fun z : Fin 26 => decide (z=Fin.castAdd 13 p ∨ z=Fin.natAdd 13 l))=true

theorem flag_eq (p l : Pt) : (fun z : Fin 26 => decide (z=Fin.castAdd 13 p ∨ z=Fin.natAdd 13 l))=
    input {p} {l} := by
  have eq : ∀ p l : Pt, (fun z : Fin 26 => decide (z=Fin.castAdd 13 p ∨ z=Fin.natAdd 13 l))=
    input {p} {l} := by decide +kernel
  exact eq p l

abbrev wt (C : Circuit) (w : Nat) (p l : Pt) := val C (input {p} {l}) w

theorem fourOff {C : Circuit} (hm : Monotone2 C) (off : test C) (q m a b : Pt)
    (qm : ¬Inc q m) (qb : ¬Inc q b) (am : ¬Inc a m) (ab : ¬Inc a b) :
    circuitFun 26 C (input ({q,a} : Finset Pt) {m,b})=false := by
  obtain ⟨S,sz,arc,sq,sa,sm,sb⟩ := fourCover q m a b qm qb am ab
  have neg := off S sz arc
  change val C (input S (avoid S)) C.output=false at neg
  cases hx : circuitFun 26 C (input ({q,a} : Finset Pt) {m,b})
  · rfl
  · have bad := wire_mono (C:=C) hm (P:=({q,a}:Finset Pt)) (P':=S) (L:=({m,b}:Finset Pt))
        (L':=avoid S) (by intro i hi; rcases Finset.mem_insert.mp hi with eq|mem; simpa only [eq] using sq; simpa only [Finset.mem_singleton.mp mem] using sa) (by intro i hi; rcases Finset.mem_insert.mp hi with eq|mem; simpa only [eq] using sm; simpa only [Finset.mem_singleton.mp mem] using sb) C.output hx
    rw [neg] at bad
    contradiction

theorem crossOnly {C : Circuit} (hm : Monotone2 C) (off : test C)
    {u v : Nat} (split : ∀ x : Fin 26→Bool, circuitFun 26 C x=(val C x u && val C x v))
    {q m a b : Pt} (qm : ¬Inc q m) (ab : ¬Inc a b)
    (ua : wt C u q m=true) (vb : wt C v a b=true) : Inc q b ∨ Inc a m := by
  by_contra! neg
  have no := fourOff hm off q m a b qm neg.1 neg.2 ab
  have t1 := wire_mono (C:=C) hm (P:={q}) (P':=({q,a}:Finset Pt)) (L:={m}) (L':=({m,b}:Finset Pt))
    (by simp) (by simp) u ua
  have t2 := wire_mono (C:=C) hm (P:={a}) (P':=({q,a}:Finset Pt)) (L:={b}) (L':=({m,b}:Finset Pt))
    (by simp) (by simp) v vb
  rw [split,t1,t2] at no
  contradiction

theorem rootSplit {C : Circuit} (hm : Monotone2 C) (on : agree C) (off : test C)
    (root : (gateAt C (C.output-26)).op=.and ∧ 26≤C.output ∧ C.output<26+C.size) :
    ∃ u v : Nat, u<C.output ∧ v<C.output ∧ ∀ x : Fin 26→Bool,
      circuitFun 26 C x=(val C x u && val C x v) := by
  let k := C.output-26
  have hk : k<C.gates.length := by have lim := root.2.2; change C.output<26+C.gates.length at lim; dsimp [k]; omega
  have kw : 26+k=C.output := by have lo := root.2.1; dsimp [k]; omega
  let g := C.gates[k]
  have hit : C.gates[k]?=some g := List.getElem?_eq_getElem hk
  have op : g.op=.and := by
    have h := root.1
    change (C.gates.getD k ⟨.or,[]⟩).op=.and at h
    rw [List.getD_eq_getElem _ _ hk] at h
    exact h
  have expr (x : Fin 26→Bool) : circuitFun 26 C x =
      (g.inputs.map (operand C x C.output)).all id := by
    have eq := val_gate C x hit
    rw [kw,op] at eq
    exact eq
  have lo (i : Nat) (mi : i∈g.inputs) : i<C.output := by
    have hx := on 0 0 (by decide)
    rw [expr] at hx
    have ai := (List.all_eq_true.mp hx) (operand C _ C.output i) (List.mem_map_of_mem mi)
    by_contra fail
    simp [operand,fail] at ai
  have ar := (hm g (List.mem_of_getElem? hit)).2
  generalize ins : g.inputs=is at ar lo expr
  cases is with
  | nil =>
    obtain ⟨S,sz,arc,_,_,_,_⟩ := fourCover 0 1 0 1 (by decide) (by decide) (by decide) (by decide)
    have z := off S sz arc
    rw [expr] at z
    contradiction
  | cons a tail =>
    cases tail with
    | nil =>
      have aa := lo a (by simp)
      exact ⟨a,a,aa,aa,fun x => by simpa [operand,aa] using expr x⟩
    | cons b t =>
      cases t with
      | nil =>
        have aa := lo a (by simp)
        have bb := lo b (by simp)
        exact ⟨a,b,aa,bb,fun x => by simpa [operand,aa,bb] using expr x⟩
      | cons c t => simp at ar

abbrev Five := Fin 5
abbrev Word := Fin 32
def pack (f : Five→Bool) : Word :=
  ⟨(f 0).toNat+2*(f 1).toNat+4*(f 2).toNat+8*(f 3).toNat+16*(f 4).toNat,
    by cases f 0 <;> cases f 1 <;> cases f 2 <;> cases f 3 <;> cases f 4 <;> decide⟩
theorem bitPack (f : Five→Bool) (i : Five) : (pack f).val.testBit i.val=f i := by
  fin_cases i
  · change (pack f).val.testBit 0=f 0
    simp only [pack]
    cases f 0 <;> cases f 1 <;> cases f 2 <;> cases f 3 <;> cases f 4 <;> rfl
  · change (pack f).val.testBit 1=f 1
    simp only [pack]
    cases f 0 <;> cases f 1 <;> cases f 2 <;> cases f 3 <;> cases f 4 <;> rfl
  · change (pack f).val.testBit 2=f 2
    simp only [pack]
    cases f 0 <;> cases f 1 <;> cases f 2 <;> cases f 3 <;> cases f 4 <;> rfl
  · change (pack f).val.testBit 3=f 3
    simp only [pack]
    cases f 0 <;> cases f 1 <;> cases f 2 <;> cases f 3 <;> cases f 4 <;> rfl
  · change (pack f).val.testBit 4=f 4
    simp only [pack]
    cases f 0 <;> cases f 1 <;> cases f 2 <;> cases f 3 <;> cases f 4 <;> rfl


def ok (a b : Word) := ∀ i j : Five, i≠j →
  ¬(a.val.testBit i.val=b.val.testBit i.val ∧ a.val.testBit j.val=b.val.testBit j.val ∧
    a.val.testBit i.val=a.val.testBit j.val)
instance (a b : Word) : Decidable (ok a b) := by unfold ok; infer_instance

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
theorem noFive : ∀ a b : Word, ok a b → ∀ c : Word, ok a c → ok b c →
    ∀ d : Word, ok a d → ok b d → ok c d →
    ∀ e : Word, ok a e → ok b e → ok c e → ok d e → False := by decide +kernel

theorem squareFree : ∀ a b p q : Pt, a≠b → p≠q →
    ¬(Inc a p ∧ Inc a q ∧ Inc b p ∧ Inc b q) := by decide +kernel

def errors5 (C : Circuit) (w : Nat) := ∃ P L : Five→Pt,
    Function.Injective P ∧ Function.Injective L ∧ ∀ i, ¬Inc (P i) (L i) ∧ wt C w (P i) (L i)=true

theorem noTwoMatchings {C : Circuit} (hm : Monotone2 C) (off : test C)
    {u v : Nat} (split : ∀ x : Fin 26→Bool, circuitFun 26 C x=(val C x u && val C x v)) :
    ¬ errors5 C u ∨ ¬ errors5 C v := by
  classical
  by_contra! both
  obtain ⟨P,L,pinj,linj,ea⟩ := both.1
  obtain ⟨Q,M,qinj,minj,eb⟩ := both.2
  have cross (i j : Five) : Inc (P i) (M j) ∨ Inc (Q j) (L i) :=
    crossOnly hm off split (ea i).1 (eb j).1 (ea i).2 (eb j).2
  let color (i j : Five) := decide (Inc (P i) (M j))
  let w (i : Five) := pack (color i)
  have comp (i k : Five) (distinct : i≠k) : ok (w i) (w k) := by
    intro j h jh eq
    simp only [w,bitPack] at eq
    have ikP : P i≠P k := fun e => distinct (pinj e)
    have jhM : M j≠M h := fun e => jh (minj e)
    have ikL : L i≠L k := fun e => distinct (linj e)
    have jhQ : Q j≠Q h := fun e => jh (qinj e)
    cases e : color i j with
    | true =>
      have uu := e
      have uv := eq.2.2.symm.trans e
      have vu := eq.1.symm.trans e
      have vv := eq.2.1.symm.trans uv
      exact (squareFree _ _ _ _ ikP jhM) ⟨of_decide_eq_true uu,of_decide_eq_true uv,
        of_decide_eq_true vu,of_decide_eq_true vv⟩
    | false =>
      have uv := eq.2.2.symm.trans e
      have vu := eq.1.symm.trans e
      have vv := eq.2.1.symm.trans uv
      have force (a b : Five) (z : color a b=false) := (cross a b).resolve_left (of_decide_eq_false z)
      exact (squareFree _ _ _ _ jhQ ikL) ⟨force i j e,force k j vu,force i h uv,force k h vv⟩
  exact noFive _ _ (comp 0 1 (by decide)) _ (comp 0 2 (by decide)) (comp 1 2 (by decide))
    _ (comp 0 3 (by decide)) (comp 1 3 (by decide)) (comp 2 3 (by decide)) _
    (comp 0 4 (by decide)) (comp 1 4 (by decide)) (comp 2 4 (by decide)) (comp 3 4 (by decide))

theorem physicalMatching {C : Circuit} (hm : Monotone2 C) (on : agree C) (off : test C)
    (root : (gateAt C (C.output-26)).op=.and ∧ 26≤C.output ∧ C.output<26+C.size) :
    ∃ u v : Nat, u<C.output ∧ v<C.output ∧
      (∀ x : Fin 26→Bool, circuitFun 26 C x=(val C x u && val C x v)) ∧
      (¬errors5 C u ∨ ¬errors5 C v) := by
  obtain ⟨u,v,hu,hv,split⟩ := rootSplit hm on off root
  exact ⟨u,v,hu,hv,split,noTwoMatchings hm off split⟩

private theorem saturate {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (r : α → β → Prop) (A : Finset α) (B : Finset β)
    (cov : ∀ a b, r a b → a ∈ A ∨ b ∈ B)
    (minimal : ∀ (X : Finset α) (Y : Finset β),
      (∀ a b, r a b → a ∈ X ∨ b ∈ Y) → A.card+B.card ≤ X.card+Y.card) :
    ∃ f : A → β, Function.Injective f ∧ ∀ a : A, r a (f a) ∧ f a ∉ B := by
  classical
  let adj (a : A) := Finset.univ.filter fun b => r a b ∧ b ∉ B
  have hall (s : Finset A) : s.card ≤ (s.biUnion adj).card := by
    let X : Finset α := s.map (Function.Embedding.subtype _)
    let Y := s.biUnion adj
    have Xsub : X ⊆ A := by
      intro a ha
      obtain ⟨i,_,rfl⟩ := Finset.mem_map.mp ha
      exact i.property
    have replacement : ∀ a b, r a b → a ∈ A \ X ∨ b ∈ B ∪ Y := by
      intro a b h
      by_cases hb : b ∈ B
      · exact Or.inr (Finset.mem_union_left _ hb)
      have ha := (cov a b h).resolve_right hb
      by_cases hx : a ∈ X
      · obtain ⟨i,hi,rfl⟩ := Finset.mem_map.mp hx
        exact Or.inr (Finset.mem_union_right _ (Finset.mem_biUnion.mpr
          ⟨i,hi,Finset.mem_filter.mpr ⟨Finset.mem_univ _,h,hb⟩⟩))
      · exact Or.inl (Finset.mem_sdiff.mpr ⟨ha,hx⟩)
    have bound := minimal _ _ replacement
    have card := Finset.card_sdiff_add_card_eq_card Xsub
    have union := Finset.card_union_le B Y
    have sizeX : X.card = s.card := Finset.card_map _
    change s.card ≤ Y.card
    omega
  obtain ⟨f,inj,mem⟩ := (Finset.all_card_le_biUnion_card_iff_existsInjective' adj).mp hall
  exact ⟨f,inj,fun a => (Finset.mem_filter.mp (mem a)).2⟩

private theorem matchingCover (n m : ℕ) (E : Finset (Fin n × Fin m)) :
    ∃ (M : Finset (Fin n × Fin m)) (A : Finset (Fin n)) (B : Finset (Fin m)),
      M ⊆ E ∧ Set.InjOn Prod.fst (M : Set (Fin n × Fin m)) ∧
      Set.InjOn Prod.snd (M : Set (Fin n × Fin m)) ∧
      (∀ e ∈ E, e.1 ∈ A ∨ e.2 ∈ B) ∧ A.card+B.card ≤ M.card := by
  classical
  let cover (A : Finset (Fin n)) (B : Finset (Fin m)) :=
    ∀ a b, (a,b) ∈ E → a ∈ A ∨ b ∈ B
  have has : ∃ k, ∃ A B, cover A B ∧ A.card+B.card = k :=
    ⟨_,Finset.univ,∅,fun a _ _ => Or.inl (Finset.mem_univ a),rfl⟩
  obtain ⟨A,B,cov,least⟩ := Nat.find_spec has
  have minAB (X Y) (h : cover X Y) : A.card+B.card ≤ X.card+Y.card := by
    rw [least]
    exact Nat.find_min' has ⟨X,Y,h,rfl⟩
  obtain ⟨f,fi,hf⟩ := saturate (fun (a : Fin n) (b : Fin m) => (a,b) ∈ E) A B cov minAB
  obtain ⟨g,gi,hg⟩ := saturate (fun (b : Fin m) (a : Fin n) => (a,b) ∈ E) B A
    (fun b a h => (cov a b h).symm) (fun Y X h => by
      simpa only [Nat.add_comm] using minAB X Y (fun a b he => (h b a he).symm))
  let pair : A ⊕ B → Fin n × Fin m := Sum.elim (fun a => (a.val,f a)) (fun b => (g b,b.val))
  have first : Function.Injective (Prod.fst ∘ pair) := by
    intro i j eq
    cases i with
    | inl a =>
      cases j with
      | inl a' => exact congrArg Sum.inl (Subtype.ext eq)
      | inr b => exact False.elim ((hg b).2 ((show a.val = g b from eq) ▸ a.property))
    | inr b =>
      cases j with
      | inl a => exact False.elim ((hg b).2 ((show a.val = g b from eq.symm) ▸ a.property))
      | inr b' => exact congrArg Sum.inr (gi eq)
  have second : Function.Injective (Prod.snd ∘ pair) := by
    intro i j eq
    cases i with
    | inl a =>
      cases j with
      | inl a' => exact congrArg Sum.inl (fi eq)
      | inr b => exact False.elim ((hf a).2 ((show b.val = f a from eq.symm) ▸ b.property))
    | inr b =>
      cases j with
      | inl a => exact False.elim ((hf a).2 ((show b.val = f a from eq) ▸ b.property))
      | inr b' => exact congrArg Sum.inr (Subtype.ext eq)
  let M := Finset.univ.image pair
  refine ⟨M,A,B,?_,?_,?_,fun e he => cov _ _ he,?_⟩
  · intro e he
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp he
    cases i with
    | inl a => exact (hf a).1
    | inr b => exact (hg b).1
  · intro e he e' he' eq
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp he
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp he'
    exact congrArg pair (first eq)
  · intro e he e' he' eq
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp he
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp he'
    exact congrArg pair (second eq)
  · simp [M,Finset.card_image_of_injective _ (Function.Injective.of_comp first)]

theorem nearExact {C : Circuit} {w : Nat} (no5 : ¬errors5 C w)
    (positive : ∀ p l, Inc p l → wt C w p l=true) :
    ∃ A B : Finset Pt, A.card+B.card≤4 ∧
      ∀ p∉A, ∀ l∉B, wt C w p l=decide (Inc p l) := by
  classical
  let E := Finset.univ.filter fun e : Pt×Pt => ¬Inc e.1 e.2 ∧ wt C w e.1 e.2=true
  obtain ⟨M,A,B,sub,pii,lii,cov,size⟩ := matchingCover 13 13 E
  have small : M.card≤4 := by
    by_contra! big
    have fit : 5≤Fintype.card (↥M) := by simpa using (show 5≤M.card by omega)
    let chooseEdge (i : Five) : ↥M := (Fintype.equivFin (↥M)).symm (Fin.castLE fit i)
    have inj : Function.Injective chooseEdge := by
      intro i j ij
      apply Fin.ext
      have z := (Fintype.equivFin (↥M)).symm.injective ij
      exact congrArg Fin.val z
    apply no5
    refine ⟨fun i => (chooseEdge i).val.1,fun i => (chooseEdge i).val.2,?_,?_,?_⟩
    · intro i j h
      exact inj (Subtype.ext (pii (chooseEdge i).property (chooseEdge j).property h))
    · intro i j h
      exact inj (Subtype.ext (lii (chooseEdge i).property (chooseEdge j).property h))
    · intro i
      exact (Finset.mem_filter.mp (sub (chooseEdge i).property)).2
  refine ⟨A,B,by omega,?_⟩
  intro p hp l hl
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_eq]
  refine ⟨?_,positive p l⟩
  intro on
  by_contra bad
  exact (cov (p,l) (Finset.mem_filter.mpr ⟨Finset.mem_univ _,bad,on⟩)).elim hp hl

def childWindow (C : Circuit) := ∃ w<C.output, ∃ A B : Finset Pt, A.card+B.card≤4 ∧
    ∀ p∉A, ∀ l∉B, wt C w p l=decide (Inc p l)

theorem window {C : Circuit} (hm : Monotone2 C) (on : agree C) (off : test C)
    (root : (gateAt C (C.output-26)).op=.and ∧ 26≤C.output ∧ C.output<26+C.size) : childWindow C := by
  obtain ⟨u,v,hu,hv,split,choice⟩ := physicalMatching hm on off root
  have pos (p l : Pt) (e : Inc p l) : wt C u p l=true ∧ wt C v p l=true := by
    have h := on p l e
    rw [flag_eq,split,Bool.and_eq_true] at h
    exact h
  rcases choice with left | right
  · exact ⟨u,hu,nearExact left (fun p l h => (pos p l h).1)⟩
  · exact ⟨v,hv,nearExact right (fun p l h => (pos p l h).2)⟩

end PEqualNP.Outside.L_meta_8009.Physical

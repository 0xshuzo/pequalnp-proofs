import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_18405.Face
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

end PEqualNP.Outside.L_meta_18405.Face

namespace PEqualNP.Outside.L_meta_18405.Physical
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

private theorem glue {α β : Type} [DecidableEq α] [DecidableEq β] (S T : Finset α)
    (B : Finset β) (adj : α→Finset β) (f g : α→β)
    (fi : Set.InjOn f (T : Set α)) (gi : Set.InjOn g ((S\T : Finset α) : Set α))
    (fs : ∀x∈T,f x∈adj x ∧ f x∈B) (gs : ∀x∈S\T,g x∈adj x ∧ g x∉B) :
    ∃ h : α→β, Set.InjOn h (S : Set α) ∧ ∀x∈S,h x∈adj x := by
  classical
  refine ⟨fun x => if x∈T then f x else g x,?_,?_⟩
  · intro x xs y ys eq
    by_cases xt : x∈T <;> by_cases yt : y∈T <;> simp only [xt,yt,if_true,if_false] at eq
    · exact fi xt yt eq
    · exact False.elim ((gs y (Finset.mem_sdiff.mpr ⟨ys,yt⟩)).2 (eq ▸ (fs x xt).2))
    · exact False.elim ((gs x (Finset.mem_sdiff.mpr ⟨xs,xt⟩)).2 (eq.symm ▸ (fs y yt).2))
    · exact gi (Finset.mem_sdiff.mpr ⟨xs,xt⟩) (Finset.mem_sdiff.mpr ⟨ys,yt⟩) eq
  · intro x xs
    by_cases xt : x∈T
    · simpa [xt] using (fs x xt).1
    · simpa [xt] using (gs x (Finset.mem_sdiff.mpr ⟨xs,xt⟩)).1

private theorem hall_part {α β : Type} [DecidableEq α] [DecidableEq β] [Inhabited β]
    (S : Finset α) (adj : α→Finset β) (hall : ∀ T⊆S,T.card≤(T.biUnion adj).card) :
    ∃ f : α→β,Set.InjOn f (S : Set α) ∧ ∀x∈S,f x∈adj x := by
  classical
  revert adj
  refine Finset.strongInductionOn S ?_
  intro S ih adj hall
  by_cases empty : S=∅
  · subst S; exact ⟨fun _ => default,by simp,by simp⟩
  obtain ⟨a,ha⟩ := Finset.nonempty_iff_ne_empty.mpr empty
  have rem (T : Finset α) (B : Finset β) :
      T.biUnion adj ⊆ T.biUnion (fun x => adj x\B) ∪ B := by
    intro y hy
    by_cases yb : y∈B
    · exact Finset.mem_union_right _ yb
    · obtain ⟨x,hx,xy⟩ := Finset.mem_biUnion.mp hy
      exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨x,hx,Finset.mem_sdiff.mpr ⟨xy,yb⟩⟩)
  by_cases tight : ∃ T : Finset α,T⊂S ∧ T.Nonempty ∧ (T.biUnion adj).card=T.card
  · obtain ⟨T,ts,⟨x,hx⟩,eq⟩ := tight
    let B := T.biUnion adj
    have us : S\T⊂S := by
      refine lt_of_le_of_ne Finset.sdiff_subset ?_
      intro same
      have hx' : x∈S\T := same.symm ▸ ts.le hx
      exact (Finset.mem_sdiff.mp hx').2 hx
    obtain ⟨f,fi,fs⟩ := ih T ts adj (fun V h => hall V (h.trans ts.le))
    obtain ⟨g,gi,gs⟩ := ih (S\T) us (fun x => adj x\B) (by
      intro V vs
      have dis : Disjoint V T := Finset.disjoint_left.mpr (fun z hz => (Finset.mem_sdiff.mp (vs hz)).2)
      have h := hall (V∪T) (Finset.union_subset (vs.trans us.le) ts.le)
      rw [Finset.card_union_of_disjoint dis] at h
      have cover : (V∪T).biUnion adj ⊆ V.biUnion (fun x => adj x\B) ∪ B := by
        intro y hy
        obtain ⟨x,hx,xy⟩ := Finset.mem_biUnion.mp hy
        rcases Finset.mem_union.mp hx with vx|tx
        · exact rem V B (Finset.mem_biUnion.mpr ⟨x,vx,xy⟩)
        · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨x,tx,xy⟩)
      have bound := (Finset.card_le_card cover).trans (Finset.card_union_le ..)
      change B.card=T.card at eq
      omega)
    exact glue S T B adj f g fi gi (fun x hx => ⟨fs x hx,Finset.mem_biUnion.mpr ⟨x,hx,fs x hx⟩⟩)
      (fun x hx => Finset.mem_sdiff.mp (gs x hx))
  · have pos := hall {a} (Finset.singleton_subset_iff.mpr ha)
    simp only [Finset.card_singleton,Finset.singleton_biUnion] at pos
    obtain ⟨b,hb⟩ := Finset.card_pos.mp (show 0<(adj a).card by omega)
    let T : Finset α := {a}
    have us : S\T⊂S := by simpa [T,Finset.sdiff_singleton_eq_erase] using Finset.erase_ssubset ha
    obtain ⟨g,gi,gs⟩ := ih (S\T) us (fun x => adj x\{b}) (by
      intro V vs
      by_cases emptyV : V=∅
      · simp [emptyV]
      have vS : V⊂S := lt_of_le_of_lt vs us
      have h1 := hall V vS.le
      have h2 : (V.biUnion adj).card≠V.card :=
        fun eq => tight ⟨V,vS,Finset.nonempty_iff_ne_empty.mpr emptyV,eq⟩
      have bound := (Finset.card_le_card (rem V {b})).trans (Finset.card_union_le ..)
      simp only [Finset.card_singleton] at bound
      omega)
    apply glue S T {b} adj (fun _ => b) g _ gi _ (fun x hx => Finset.mem_sdiff.mp (gs x hx))
    · intro x hx y hy _; change x∈({a}:Finset α) at hx;change y∈({a}:Finset α) at hy
      exact (Finset.mem_singleton.mp hx).trans (Finset.mem_singleton.mp hy).symm
    · intro x hx
      have e : x=a := Finset.mem_singleton.mp hx
      exact ⟨e.symm ▸ hb,by simp⟩

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
  by_cases non : Nonempty (↥A)
  · obtain ⟨a⟩ := non
    have pos := hall {a}
    simp only [Finset.card_singleton,Finset.singleton_biUnion] at pos
    obtain ⟨b,_⟩ := Finset.card_pos.mp (show 0<(adj a).card by omega)
    letI : Inhabited β := ⟨b⟩
    obtain ⟨f,fi,fs⟩ := hall_part (Finset.univ : Finset (↥A)) adj (fun T _ => hall T)
    exact ⟨f,fun x y e => fi (Finset.mem_univ x) (Finset.mem_univ y) e,fun x => (Finset.mem_filter.mp (fs x (Finset.mem_univ x))).2⟩
  · exact ⟨fun a => False.elim (non ⟨a⟩),fun {a} => False.elim (non ⟨a⟩),fun a => False.elim (non ⟨a⟩)⟩

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

abbrev Board := Finset (Pt×Pt)
def rel (d : Bool) (p l : Pt) : Prop := if d then Inc l p else Inc p l
instance (d : Bool) (p l : Pt) : Decidable (rel d p l) := by unfold rel; infer_instance
def tr (E : Board) := E.image Prod.swap
theorem memTr {p l : Pt} {E : Board} : (l,p)∈tr E ↔ (p,l)∈E := by
  constructor
  · rintro h
    obtain ⟨⟨a,b⟩,e,eq⟩ := Finset.mem_image.mp h
    cases eq
    exact e
  · exact fun h => Finset.mem_image.mpr ⟨(p,l),h,rfl⟩
theorem cardTr (E : Board) : (tr E).card=E.card :=
  Finset.card_image_of_injective _ (fun a b h => by simpa using congrArg Prod.swap h)

def fibre (E : Board) (p : Pt) := Finset.univ.filter fun l : Pt => (p,l)∈E
def fat (E : Board) := ∃ p, 4≤(fibre E p).card
def wrong (d : Bool) (E : Board) := ∀ e∈E, ¬rel d e.1 e.2
def compatible (d : Bool) (E F : Board) := ∀ e∈E, ∀ f∈F, rel d e.1 f.2 ∨ rel d f.1 e.2
theorem wrongTr {d E} (h : wrong d E) : wrong (!d) (tr E) := by
  rintro ⟨l,p⟩ mem
  have no := h (p,l) (memTr.mp mem)
  cases d <;> simpa [rel] using no
theorem compatSwap {d E F} (h : compatible d E F) : compatible d F E :=
  fun f hf e he => (h e he f hf).symm
theorem compatTr {d E F} (h : compatible d E F) : compatible (!d) (tr E) (tr F) := by
  rintro ⟨l,p⟩ e ⟨m,q⟩ f
  have z := (h (p,l) (memTr.mp e) (q,m) (memTr.mp f)).symm
  cases d <;> simpa [rel] using z

def cylinders (E : Board) (P : Finset Pt) : Board := P.biUnion fun p => (fibre E p).image (fun l => (p,l))
theorem inCyl {p l : Pt} {E : Board} {P : Finset Pt} (h : (p,l)∈E) (hp : p∈P) :
    (p,l)∈cylinders E P := Finset.mem_biUnion.mpr ⟨p,hp,Finset.mem_image.mpr
      ⟨l,Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩,rfl⟩⟩
theorem cylCost (E : Board) (P : Finset Pt) (no : ¬fat E) : (cylinders E P).card≤3*P.card := by
  calc
    _ ≤ ∑ p∈P, ((fibre E p).image fun l => (p,l)).card := Finset.card_biUnion_le
    _ ≤ ∑ _p∈P, 3 := Finset.sum_le_sum (fun p _ => Finset.card_image_le.trans (by
      have h : ¬4≤(fibre E p).card := fun z => no ⟨p,z⟩
      omega))
    _ = _ := by simp [Nat.mul_comm]

theorem coverFat {E : Board} (big : 13≤E.card) {P L : Finset Pt}
    (cov : ∀ e∈E, e.1∈P ∨ e.2∈L) (sz : P.card+L.card≤4) : fat E ∨ fat (tr E) := by
  by_contra! absent
  have sub : E ⊆ cylinders E P ∪ tr (cylinders (tr E) L) := by
    rintro ⟨p,l⟩ h
    rcases cov (p,l) h with hp|hl
    · exact Finset.mem_union_left _ (inCyl h hp)
    · exact Finset.mem_union_right _ (memTr.mpr (inCyl (memTr.mpr h) hl))
  have cap := (Finset.card_le_card sub).trans (Finset.card_union_le _ _)
  rw [cardTr] at cap
  have x := cylCost E P absent.1
  have y := cylCost (tr E) L absent.2
  omega

theorem fourAxes : ∀ d : Bool, ∀ p : Pt, (Finset.univ.filter (fun l : Pt => rel d p l)).card=4 ∧
    (Finset.univ.filter (fun l : Pt => ¬rel d p l)).card=9 := by decide +kernel
theorem missCommon : ∀ d : Bool, ∀ p q : Pt,
    (Finset.univ.filter (fun l : Pt => ¬rel d p l ∧ rel d q l)).card≤3 := by decide +kernel
theorem squareDir (d : Bool) (p q l m : Pt) (pq : p≠q) (lm : l≠m) :
    ¬(rel d p l ∧ rel d p m ∧ rel d q l ∧ rel d q m) := by
  cases d
  · exact squareFree p q l m pq lm
  · rintro ⟨a,b,c,e⟩
    exact squareFree l m p q lm pq ⟨a,c,b,e⟩
theorem forcesPencil {d : Bool} {E F : Board} (error : wrong d E) (cross : compatible d E F)
    (p : Pt) (large : 4≤(fibre E p).card) : ∀ f∈F, rel d p f.2 := by
  intro f mem
  by_contra no
  have sub : fibre E p ⊆ Finset.univ.filter (fun l : Pt => ¬rel d p l ∧ rel d f.1 l) := by
    intro l hl
    have e := (Finset.mem_filter.mp hl).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,error (p,l) e,(cross (p,l) e f mem).resolve_left no⟩
  have cost := (Finset.card_le_card sub).trans (missCommon d p f.1)
  omega

def extras (E : Board) (p : Pt) := (E.filter fun e => e.1≠p).image Prod.snd

theorem extraTwo {d : Bool} {E : Board} {p l : Pt} (error : wrong d E) (inc : rel d p l)
    (pencil : ∀ e∈E, rel d e.1 l) (big : 13≤E.card) : 2≤(extras E p).card := by
  let X := (Finset.univ : Finset Pt).filter (fun n => ¬rel d p n)
  let Y := (Finset.univ : Finset Pt).filter (fun r => rel d r l ∧ r≠p)
  have cn : X.card=9 := (fourAxes d p).2
  have yn : Y.card≤3 := by
    have ff : ∀ d : Bool, ∀ p l : Pt, rel d p l →
        (Finset.univ.filter (fun r : Pt => rel d r l ∧ r≠p)).card=3 := by decide +kernel
    exact (ff d p l inc).le
  have sub : E ⊆ ({p}:Finset Pt) ×ˢ X ∪ Y ×ˢ (extras E p) := by
    rintro ⟨r,n⟩ en
    by_cases rEq : r=p
    · subst r
      exact Finset.mem_union_left _ (Finset.mem_product.mpr ⟨by simp,Finset.mem_filter.mpr ⟨Finset.mem_univ _,error _ en⟩⟩)
    · exact Finset.mem_union_right _ (Finset.mem_product.mpr
        ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,pencil _ en,rEq⟩,
         Finset.mem_image.mpr ⟨(r,n),Finset.mem_filter.mpr ⟨en,rEq⟩,rfl⟩⟩)
  have cost := (Finset.card_le_card sub).trans (Finset.card_union_le _ _)
  simp only [Finset.card_product,Finset.card_singleton,one_mul,cn] at cost
  by_contra! tiny
  have small := Nat.mul_le_mul yn (show (extras E p).card≤1 by omega)
  omega

theorem rowImpossible {d : Bool} {E F : Board} (e : wrong d E) (f : wrong d F) (cross : compatible d E F)
    (e13 : 13≤E.card) (f13 : 13≤F.card) (heavy : fat E) : False := by
  obtain ⟨p,hp⟩ := heavy
  have allF := forcesPencil e cross p hp
  let P := Finset.univ.filter (fun m : Pt => rel d p m)
  have sz : P.card=4 := (fourAxes d p).1
  have fHeavy : fat (tr F) := by
    by_contra nf
    have sub : tr F ⊆ cylinders (tr F) P := by
      rintro ⟨m,q⟩ h
      exact inCyl h (Finset.mem_filter.mpr ⟨Finset.mem_univ _,allF (q,m) (memTr.mp h)⟩)
    have cost := (Finset.card_le_card sub).trans (cylCost (tr F) P nf)
    rw [cardTr,sz] at cost
    omega
  obtain ⟨l,hl⟩ := fHeavy
  have el (r n : Pt) (h : (r,n)∈E) : rel d r l := by
    have z := forcesPencil (wrongTr f) (compatTr (compatSwap cross)) l hl (n,r) (memTr.mpr h)
    cases d <;> simpa [rel] using z
  obtain ⟨q,hq⟩ := Finset.card_pos.mp (show 0<(fibre (tr F) l).card by omega)
  have pl := allF (q,l) (memTr.mp (Finset.mem_filter.mp hq).2)
  have exA := extraTwo e pl (fun a ha => el a.1 a.2 ha) e13
  have lp : rel (!d) l p := by cases d <;> simpa [rel] using pl
  have ff : ∀ a∈tr F, rel (!d) a.1 p := by
    rintro ⟨m,v⟩ hm
    have z := allF (v,m) (memTr.mp hm)
    cases d <;> simpa [rel] using z
  have exB := extraTwo (wrongTr f) lp ff (by rwa [cardTr])
  have rectangle (v : Pt) (hv : v∈extras (tr F) l) (n : Pt) (hn : n∈extras E p) : rel d v n := by
    obtain ⟨⟨m,z⟩,hz,zz⟩ := Finset.mem_image.mp hv
    change z=v at zz
    subst z
    obtain ⟨⟨r,k⟩,hk,kk⟩ := Finset.mem_image.mp hn
    change k=n at kk
    subst k
    obtain ⟨hm,ml⟩ := Finset.mem_filter.mp hz
    obtain ⟨hr,rp⟩ := Finset.mem_filter.mp hk
    have vf := memTr.mp hm
    have possible := cross (r,n) hr (v,m) vf
    apply possible.resolve_left
    intro rm
    exact squareDir d r p m l rp ml ⟨rm,el r n hr,allF _ vf,pl⟩
  obtain ⟨v,hv,w,hw,vw⟩ := Finset.one_lt_card.mp exB
  obtain ⟨n,hn,m,hm,nm⟩ := Finset.one_lt_card.mp exA
  exact squareDir d v w n m vw nm ⟨rectangle v hv n hn,rectangle v hv m hm,
    rectangle w hw n hn,rectangle w hw m hm⟩

theorem atMostTwelve {E F : Board} (e : wrong false E) (f : wrong false F)
    (cross : compatible false E F) {P L : Finset Pt} (cov : ∀ z∈E, z.1∈P ∨ z.2∈L)
    (sz : P.card+L.card≤4) : E.card≤12 ∨ F.card≤12 := by
  by_contra! both
  obtain fe|fe := coverFat both.1 cov sz
  · exact rowImpossible e f cross both.1 both.2 fe
  · exact rowImpossible (wrongTr e) (wrongTr f) (compatTr cross) (by rw [cardTr]; exact both.1) (by rw [cardTr]; exact both.2) fe

def mistakes (C : Circuit) (w : Nat) : Board := Finset.univ.filter fun z => ¬Inc z.1 z.2 ∧ wt C w z.1 z.2=true


def FiveMatch (E : Board) := ∃ P L : Five→Pt, Function.Injective P ∧ Function.Injective L ∧ ∀ i,(P i,L i)∈E

theorem match_exclusion {E F : Board} (cr : compatible false E F) : ¬FiveMatch E ∨ ¬FiveMatch F := by
  classical
  by_contra! both
  obtain ⟨P,L,pinj,linj,ea⟩ := both.1
  obtain ⟨Q,M,qinj,minj,eb⟩ := both.2
  have cross (i j : Five) : Inc (P i) (M j) ∨ Inc (Q j) (L i) := cr _ (ea i) _ (eb j)
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


theorem smallCover {E : Board} (no5 : ¬FiveMatch E) :
  ∃ A B : Finset Pt,(∀ z∈E,z.1∈A ∨ z.2∈B) ∧ A.card+B.card≤4 := by
  classical
  obtain ⟨M,A,B,sub,pii,lii,cov,size⟩ := matchingCover 13 13 E
  have small : M.card≤4 := by
    by_contra! big
    have fit : 5≤Fintype.card (↥M) := by simpa using (show 5≤M.card by omega)
    let chooseEdge (i : Five) : ↥M := (Fintype.equivFin (↥M)).symm (Fin.castLE fit i)
    have inj : Function.Injective chooseEdge := by
      intro i j ij
      apply Fin.ext
      have z := (Fintype.equivFin (↥M)).symm.injective ij
      exact congrArg (fun k : Fin (Fintype.card (↥M)) => k.val) z
    apply no5
    refine ⟨fun i => (chooseEdge i).val.1,fun i => (chooseEdge i).val.2,?_,?_,?_⟩
    · intro i j h
      exact inj (Subtype.ext (pii (chooseEdge i).property (chooseEdge j).property h))
    · intro i j h
      exact inj (Subtype.ext (lii (chooseEdge i).property (chooseEdge j).property h))
    · intro i
      exact sub (chooseEdge i).property
  exact ⟨A,B,cov,by omega⟩

theorem sharp_cross {E F : Board} (e : wrong false E) (f : wrong false F) (cr : compatible false E F) :
    E.card≤12 ∨ F.card≤12 := by
  rcases match_exclusion cr with m|m
  · obtain ⟨A,B,c,s⟩ := smallCover m
    exact atMostTwelve e f cr c s
  · obtain ⟨A,B,c,s⟩ := smallCover m
    exact (atMostTwelve f e (compatSwap cr) c s).symm

def tap (pre : List Gate) (g : Gate) : Circuit := ⟨pre++[g],26+pre.length⟩
def up (pre post : List Gate) (o : ℕ) : Circuit := ⟨pre++⟨.and,[]⟩::post,o⟩
def original (pre : List Gate) (g : Gate) (post : List Gate) (o : ℕ) : Circuit := ⟨pre++g::post,o⟩

theorem cut (pre post : List Gate) (g : Gate) (o : ℕ) (x : Fin 26→Bool) :
  circuitFun 26 (tap pre g) x=true →
  circuitFun 26 (up pre post o) x=circuitFun 26 (original pre g post o) x := by
  let w := wiresFrom pre (List.ofFn x)
  let b := g.op.eval (g.inputs.map fun i => w.getD i false)
  have len : w.length=26+pre.length := by simp [w,wiresFrom_length]
  have val : circuitFun 26 (tap pre g) x=b := by
    change (wiresFrom (pre++[g]) (List.ofFn x)).getD (26+pre.length) false=b
    rw [wiresFrom_append]
    change (w++[b]).getD (26+pre.length) false=b
    rw [←len];simp [List.getD_eq_getElem?_getD]
  rw [val]; intro on
  change (wiresFrom (pre++⟨.and,[]⟩::post) (List.ofFn x)).getD o false =
    (wiresFrom (pre++g::post) (List.ofFn x)).getD o false
  rw [wiresFrom_append,wiresFrom_append]
  change (wiresFrom post (w++[true])).getD o false=(wiresFrom post (w++[b])).getD o false
  rw [on]

theorem gate_window (pre post : List Gate) (g : Gate) (o : ℕ)
    (hm : Monotone2 (original pre g post o)) (off : test (original pre g post o)) :
  (mistakes (tap pre g) (26+pre.length)).card≤12 ∨ (mistakes (up pre post o) o).card≤12 := by
  let C := original pre g post o
  let U := tap pre g
  let V := up pre post o
  have mu : Monotone2 U := by
    intro h mem
    rcases List.mem_append.mp mem with hp|hg
    · exact hm h (List.mem_append_left _ hp)
    · have id : h=g := by simpa using hg
      subst h; exact hm g (List.mem_append_right _ List.mem_cons_self)
  have mv : Monotone2 V := by
    intro h mem
    rcases List.mem_append.mp mem with hp|t
    · exact hm h (List.mem_append_left _ hp)
    · rcases List.mem_cons.mp t with hx|t
      · subst h;simp
      · exact hm h (List.mem_append_right _ (List.mem_cons_of_mem _ t))
  have wrongs (K : Circuit) (w : ℕ) : wrong false (mistakes K w) := fun z h => (Finset.mem_filter.mp h).2.1
  apply sharp_cross (wrongs U _) (wrongs V _)
  rintro ⟨p,l⟩ h ⟨q,m⟩ h'
  obtain ⟨pe,po⟩ := (Finset.mem_filter.mp h).2
  obtain ⟨qe,qo⟩ := (Finset.mem_filter.mp h').2
  change Inc p m ∨ Inc q l
  by_contra! no
  have fail := fourOff hm off p l q m pe no.1 no.2 qe
  have yesU := wire_mono (C:=U) mu (P:={p}) (P':=({p,q}:Finset Pt)) (L:={l}) (L':=({l,m}:Finset Pt))
    (by simp) (by simp) U.output po
  have yesV := wire_mono (C:=V) mv (P:={q}) (P':=({p,q}:Finset Pt)) (L:={m}) (L':=({l,m}:Finset Pt))
    (by simp) (by simp) V.output qo
  have eq := cut pre post g o (input {p,q} {l,m}) yesU
  change circuitFun 26 V (input {p,q} {l,m})=true at yesV
  rw [eq,fail] at yesV
  contradiction

end PEqualNP.Outside.L_meta_18405.Physical

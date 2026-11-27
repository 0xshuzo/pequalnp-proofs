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

def mistakes (C : Circuit) (w : Nat) : Finset (Pt×Pt) := Finset.univ.filter fun z => ¬Inc z.1 z.2 ∧ wt C w z.1 z.2=true


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

def supportP (K : Circuit) : Finset Pt := Finset.univ.filter fun p => val K (input {p} ∅) K.output=true
def supportL (K : Circuit) : Finset Pt := Finset.univ.filter fun l => val K (input ∅ {l}) K.output=true

theorem upMono (pre post : List Gate) (g : Gate) (o : ℕ) (hm : Monotone2 (original pre g post o)) :
    Monotone2 (up pre post o) := by
  intro h mem
  rcases List.mem_append.mp mem with hh|hh
  · exact hm h (List.mem_append_left _ hh)
  · rcases List.mem_cons.mp hh with eq|tail
    · subst h; exact ⟨Or.inl rfl,by decide⟩
    · exact hm h (List.mem_append_right _ (List.mem_cons_of_mem _ tail))

theorem tapMono (pre post : List Gate) (g : Gate) (o : ℕ) (hm : Monotone2 (original pre g post o)) :
    Monotone2 (tap pre g) := by
  intro h mem
  rcases List.mem_append.mp mem with hh|hh
  · exact hm h (List.mem_append_left _ hh)
  · have id : h=g := by simpa using hh
    subst h;exact hm g (List.mem_append_right _ List.mem_cons_self)

theorem cage (pre post : List Gate) (g : Gate) (o : ℕ)
    (hm : Monotone2 (original pre g post o)) (off : test (original pre g post o)) :
    ∀ e∈mistakes (up pre post o) o,
    (∀ p∈supportP (tap pre g),Inc p e.2) ∧ (∀ l∈supportL (tap pre g),Inc e.1 l) := by
  intro e he
  obtain ⟨bad,on⟩ := (Finset.mem_filter.mp he).2
  have hu := tapMono pre post g o hm
  have hv := upMono pre post g o hm
  constructor
  · intro p hp
    by_contra miss
    have a := wire_mono hu (P:={p}) (P':=({p,e.1}:Finset Pt)) (L:=∅) (L':=({e.2,e.2}:Finset Pt))
      (by simp) (by simp) _ (Finset.mem_filter.mp hp).2
    have b := wire_mono hv (P:={e.1}) (P':=({p,e.1}:Finset Pt)) (L:={e.2}) (L':=({e.2,e.2}:Finset Pt))
      (by simp) (by simp) _ on
    have eq := cut pre post g o _ a
    have fail := fourOff hm off p e.2 e.1 e.2 miss miss bad bad
    change circuitFun 26 (up pre post o) _=true at b
    rw [eq,fail] at b
    contradiction
  · intro l hl
    by_contra miss
    have a := wire_mono hu (P:=∅) (P':=({e.1,e.1}:Finset Pt)) (L:={l}) (L':=({l,e.2}:Finset Pt))
      (by simp) (by simp) _ (Finset.mem_filter.mp hl).2
    have b := wire_mono hv (P:={e.1}) (P':=({e.1,e.1}:Finset Pt)) (L:={e.2}) (L':=({l,e.2}:Finset Pt))
      (by simp) (by simp) _ on
    have eq := cut pre post g o _ a
    have fail := fourOff hm off e.1 l e.1 e.2 miss bad miss bad
    change circuitFun 26 (up pre post o) _=true at b
    rw [eq,fail] at b
    contradiction

theorem noDyad (pre post : List Gate) (g : Gate) (o : ℕ)
    (hm : Monotone2 (original pre g post o)) (off : test (original pre g post o))
    (noncollinear : ∀ l : Pt,∃ p∈supportP (tap pre g),¬ Inc p l) :
    mistakes (up pre post o) o=∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro e he
  obtain ⟨p,hp,miss⟩ := noncollinear e.2
  exact miss ((cage pre post g o hm off e he).1 p hp)

theorem twoPure (pre post : List Gate) (g : Gate) (o : ℕ)
    (hm : Monotone2 (original pre g post o)) (off : test (original pre g post o))
    (p q : Pt) (hp : p∈supportP (tap pre g)) (hq : q∈supportP (tap pre g)) (pq : p≠q) :
    (mistakes (up pre post o) o).card≤9 := by
  have tab : ∀ p q : Pt,p≠q → (Finset.univ.filter (fun z : Pt×Pt => Inc p z.2 ∧ Inc q z.2 ∧ ¬Inc z.1 z.2)).card=9 := by decide +kernel
  apply (Finset.card_le_card (s:=(mistakes (up pre post o) o)) (t:=Finset.univ.filter (fun z : Pt×Pt => Inc p z.2 ∧ Inc q z.2 ∧ ¬Inc z.1 z.2)) ?_).trans
  · exact (tab p q pq).le
  · intro z hz
    have c := (cage pre post g o hm off z hz).1
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,c p hp,c q hq,(Finset.mem_filter.mp hz).2.1⟩

theorem mixed (pre post : List Gate) (g : Gate) (o : ℕ)
    (hm : Monotone2 (original pre g post o)) (off : test (original pre g post o))
    (p l : Pt) (hp : p∈supportP (tap pre g)) (hl : l∈supportL (tap pre g)) :
    (mistakes (up pre post o) o).card ≤ (if Inc p l then 9 else 12) := by
  have tab : ∀ p l : Pt,(Finset.univ.filter (fun z : Pt×Pt => Inc p z.2 ∧ Inc z.1 l ∧ ¬Inc z.1 z.2)).card = (if Inc p l then 9 else 12) := by decide +kernel
  have sub : mistakes (up pre post o) o ⊆ Finset.univ.filter (fun z : Pt×Pt => Inc p z.2 ∧ Inc z.1 l ∧ ¬Inc z.1 z.2) := by
    intro z hz
    have c := cage pre post g o hm off z hz
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,c.1 p hp,c.2 l hl,(Finset.mem_filter.mp hz).2.1⟩
  exact (Finset.card_le_card sub).trans (tab p l).le

end PEqualNP.Outside.L_meta_18405.Physical

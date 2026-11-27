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
    (code k).testBit 0=true ∧ (code k).testBit (13+m.val)=true ∧ (code k).testBit (13+b.val)=true := by decide +kernel
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

import PEqualNP.Defs
namespace Research10009.GapsFive
abbrev V := Fin 31
abbrev Cell := V × V
abbrev Box := Finset V × Finset V
def rows : Array (Nat) := #[1141899472,136315297,272630594,545261188,1090522376,33561105,67122210,134244420,268488840,536977680,1073955360,427073,854146,1708292,3416584,6833168,13666336,27332672,54665344,109330688,218661376,437322752,874645504,1749291008,1351098369,554713091,1109426182,71368717,142737434,285474868,570949736]
def wits : Array (Cell) := #[(0, 23),(7, 26),(17, 14),(19, 29),(23, 6)]
def original : Array (Nat × Nat) := #[(809517128, 1112129857),(1829405248, 135400064),(16818375, 587563016),(125109256, 266584),(1080048066, 1103102480),(310527750, 101190660),(271745281, 537143589),(940644373, 572551168),(178274452, 9076912),(27535880, 69224490),(134857226, 1359089730),(34408529, 405340676),(1074792080, 284430467),(1078857732, 1209041941),(1417748480, 352413313),(604304688, 746586176),(34213928, 1480761384),(482347040, 18375072),(1628438945, 6489346)]
def additions : Array (Nat × Nat) := #[(603984897, 12591368),(132266, 68452354),(139591682, 1074029570),(17302816, 554696708),(8388608, 64)]

def hit (b : Nat × Nat) (x : Cell) := b.1.testBit x.1.val && b.2.testBit x.2.val
def flag (x : Cell) := (rows[x.1.val]!).testBit x.2.val
def miss (x : Cell) := !flag x && !(original.any (fun b => hit b x))
def wit (i : Fin 5) := wits[i.val]!
theorem control : (∀i : Fin 5,miss (wit i)=true) ∧
    (∀i j : Fin 5,i≠j → flag ((wit i).1,(wit j).2)=true ∨ flag ((wit j).1,(wit i).2)=true) ∧
    ∀i j : V,(miss (i,j)=true → additions.any (fun b => hit b (i,j))=true) ∧
      (additions.any (fun b => hit b (i,j))=true → flag (i,j)=false) := by decide +kernel

theorem minimum (n : Nat) (B : Fin n → Box)
    (ok : ∀ i,∀p∈(B i).1,∀q∈(B i).2,flag (p,q)=false)
    (cov : ∀x,miss x=true → ∃i,x.1∈(B i).1 ∧ x.2∈(B i).2) : 5≤n := by
  classical
  have get : ∀i : Fin 5,∃t,(wit i).1∈(B t).1 ∧ (wit i).2∈(B t).2 := fun i => cov (wit i) (control.1 i)
  choose h p q using get
  have inj : Function.Injective h := by
    intro i j eq
    by_contra neq
    have pi:=p i
    have qi:=q i
    rw [eq] at pi qi
    rcases control.2.1 i j neq with no|no
    · exact Bool.noConfusion ((ok _ _ pi _ (q j)).symm.trans no)
    · exact Bool.noConfusion ((ok _ _ (p j) _ qi).symm.trans no)
  simpa using Fintype.card_le_of_injective h inj
end Research10009.GapsFive

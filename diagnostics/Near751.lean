import PEqualNP.Defs

-- The mask-to-Finset verifier is adapted from L-meta-10015.

namespace PEqualNP.Outside.L_meta_10009.Near19

def boxes : List (ℕ × ℕ) := [(809517128, 1112129857), (1829405248, 135400064), (16818375, 587563016), (125109256, 266584), (1080048066, 1103102480), (310527750, 101190660), (271745281, 537143589), (940644373, 572551168), (178274452, 9076912), (27535880, 69224490), (134857226, 1359089730), (34408529, 405340676), (1074792080, 284430467), (1078857732, 1209041941), (1417748480, 352413313), (604304688, 746586176), (34213928, 1480761384), (482347040, 18375072), (1628438945, 6489346)]
def rows : List ℕ := [1141899472, 136315297, 272630594, 545261188, 1090522376, 33561105, 67122210, 134244420, 268488840, 536977680, 1073955360, 427073, 854146, 1708292, 3416584, 6833168, 13666336, 27332672, 54665344, 109330688, 218661376, 437322752, 874645504, 1749291008, 1351098369, 554713091, 1109426182, 71368717, 142737434, 285474868, 570949736]
def members {n : ℕ} (mask : ℕ) : Finset (Fin n) := Finset.univ.filter fun i => mask.testBit i.val

def gaps : List Nat := [23, 44, 45, 51, 113, 157, 173, 243, 268, 323, 325, 334, 380, 528, 541, 618, 650, 683, 719, 746, 828, 847, 855, 902]
theorem tabLength : boxes.length = 19 ∧ gaps.length = 24 ∧ gaps.Nodup := by decide +kernel
set_option maxRecDepth 10000 in
theorem audit : ∀ i j : Fin 31,
    ((rows.getD i.val 0).testBit j.val = false ↔
      ((i.val*31+j.val) ∈ gaps ∨ ∃ b ∈ boxes, b.1.testBit i.val = true ∧ b.2.testBit j.val = true)) ∧
    (i.val*31+j.val ∈ gaps → ∀ b ∈ boxes, ¬ (b.1.testBit i.val = true ∧ b.2.testBit j.val = true)) := by
  decide +kernel
end PEqualNP.Outside.L_meta_10009.Near19

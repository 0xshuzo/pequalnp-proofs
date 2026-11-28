import PEqualNP.Defs
namespace Lmeta10008LocalWitness
abbrev V := Fin 31
abbrev S := Fin 3
def mat (p j : V) := (([1141899472, 136315297, 272630594, 545261188, 1090522376, 33561105, 67122210, 134244420, 268488840, 536977680, 1073955360, 427073, 854146, 1708292, 3416584, 6833168, 13666336, 27332672, 54665344, 109330688, 218661376, 437322752, 874645504, 1749291008, 1351098369, 554713091, 1109426182, 71368717, 142737434, 285474868, 570949736] : List Nat).getD p.val 0).testBit j.val
def left (s : S) (p : V) := (([1361921, 537633, 197201] : List Nat).getD s.val 0).testBit p.val
def right (s : S) (j : V) := (([813766950, 962634760, 437142021] : List Nat).getD s.val 0).testBit j.val
def sole (s : S) : V := ![1,3,0] s
def shared : V := 28
theorem legal : ∀ s p j, left s p=true → right s j=true → mat p j=false := by decide +kernel
theorem completeRow : ∀ j, mat 0 j=false → ∃ s, left s 0=true ∧ right s j=true := by decide +kernel
theorem pattern : (∀ s, left s 0=true ∧ right s shared=true ∧ mat 0 (sole s)=false) ∧
  (∀ a b, right a (sole b)=decide (a=b)) ∧ mat 0 shared=false := by decide +kernel

def val (w : S → ℝ) (j : V) : ℝ := ∑ s : S, if right s j then w s else 0
theorem unbalanced (w : S → ℝ) : ∃ j, mat 0 j=false ∧ (val w j<5 ∨ 11<val w j) := by
  classical
  by_contra! all
  have priv (s : S) : val w (sole s)=w s := by
    simp [val,pattern.2.1]
  have low (s : S) : 5≤w s := (priv s) ▸ (all _ (pattern.1 s).2.2).1
  have total : val w shared=∑ s : S,w s := by simp [val,fun s => (pattern.1 s).2.1]
  have hi := (all _ pattern.2.2).2
  rw [total,Fin.sum_univ_succ,Fin.sum_univ_succ,Fin.sum_univ_one] at hi
  have h0:=low 0
  have h1:=low 1
  have h2:=low 2
  change w 0+(w 1+w 2)≤11 at hi
  linarith
end Lmeta10008LocalWitness

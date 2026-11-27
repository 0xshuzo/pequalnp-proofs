import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_9829.Recoding

abbrev X := Fin 13 → Bool
abbrev Y := Fin 11 → Bool
def row0 (x : X) := x 2 || x 3 || x 5 || x 11
def row1 (x : X) := x 3 || x 4 || x 6 || x 12
def row2 (x : X) := x 0 || x 4 || x 5 || x 7
def row3 (x : X) := x 1 || x 5 || x 6 || x 8
def row4 (x : X) := x 2 || x 6 || x 7 || x 9
def row5 (x : X) := x 3 || x 7 || x 8 || x 10
def row6 (x : X) := x 4 || x 8 || x 9 || x 11
def row7 (x : X) := x 5 || x 9 || x 10 || x 12
def row8 (x : X) := x 0 || x 6 || x 10 || x 11
def row9 (x : X) := x 1 || x 7 || x 11 || x 12
def row10 (x : X) := x 0 || x 2 || x 8 || x 12
def obs (x : X) : Y := ![row0 x, row1 x, row2 x, row3 x, row4 x, row5 x, row6 x, row7 x, row8 x, row9 x, row10 x]
def mask (z : Y) : Bool := z 1 || z 2 || z 3
def code (x : X) : Y := Function.update (obs x) 0 (row0 x && mask (obs x))
def decode (z : Y) : Y := Function.update z 0 (z 0 || (!mask z && (z 9 || z 10)))

theorem cleared (x : X) (hm : mask (obs x)=false) : row0 x=(row9 x || row10 x) := by
  have off (j : Fin 13) (hj : (j=0 ∨ j=1 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=12)) : x j=false := by
    cases hx : x j
    · rfl
    · rcases hj with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp [mask,obs,row1,row2,row3,hx] at hm
  simp [row0,row9,row10,off 0 (by decide), off 1 (by decide), off 3 (by decide), off 4 (by decide), off 5 (by decide), off 6 (by decide), off 7 (by decide), off 8 (by decide), off 12 (by decide),Bool.or_comm]

theorem recovers (x : X) : decode (code x) = obs x := by
  funext j
  by_cases h : j=0
  · subst j
    have mh : mask (code x)=mask (obs x) := by simp [mask,code,Function.update]
    simp only [decode, Function.update_self, mh]
    have c0 : code x 0=(row0 x && mask (obs x)) := by simp [code]
    have c9 : code x 9=row9 x := by simp [code,obs,Function.update]
    have c10 : code x 10=row10 x := by simp [code,obs,Function.update]
    rw [c0,c9,c10]
    change (row0 x && mask (obs x) || !mask (obs x) && (row9 x || row10 x)) = row0 x
    cases hm : mask (obs x)
    · simp [cleared x hm]
    · simp
  · simp [decode,code,Function.update,h]

def one (i : Fin 13) : X := fun j => decide (j=i)
theorem changedOnTwoFlags : row0 (one 2)=true ∧ row0 (one 11)=true ∧
    code (one 2) 0=false ∧ code (one 11) 0=false := by decide +kernel

def outside0 : X := fun p => !(p == 2 || p == 3 || p == 5 || p == 11)

theorem noSeparatingChannel :
    ∀ j : Fin 11, ¬(code (one 2) j=true ∧ code outside0 j=false) := by decide +kernel

end PEqualNP.Outside.L_meta_9829.Recoding

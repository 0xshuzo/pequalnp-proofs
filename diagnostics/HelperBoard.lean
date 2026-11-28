import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9737.HelperBoard
abbrev V := Fin 25
abbrev E := Fin 48
def edge : Array Nat := #[65537,4194305,16777217,8194,131074,8388610,8196,16388,262148,16777220,16392,32776,524296,8208,32784,65552,1048592,16416,65568,131104,2097184,32832,131136,262208,4194368,65664,262272,524416,8388736,131328,524544,1048832,16777472,262656,1049088,2097664,9216,525312,2098176,4195328,18432,1050624,4196352,8390656,36864,2101248,8392704,16781312]
def columnA : Array Nat := #[8191,15337,22483,36775,73550,138909,269627,531063,1053935,2099679,4199358,8390525,16781050]
def columnB : Array Nat := #[33546240,12509185,25018370,16482308,32972808,32391184,31236128,28926016,24305792,15065344,30138880,26723328,19900416,6254592]
def dyad (e : E) (v : V) : Bool := (edge[e.val]?.getD 0).testBit v.val
def positive (x : Nat) : Bool := edge.any (fun e => x &&& e == e)

set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem trueEdges : ∀ e : E, positive (edge[e.val]?.getD 0) = true := by decide +kernel
theorem falseA : ∀ j : Fin 13, positive (columnA[j.val]?.getD 0) = false := by decide +kernel
theorem falseB : ∀ j : Fin 14, positive (columnB[j.val]?.getD 0) = false := by decide +kernel
def pairRow (a b : V) : Nat :=
  (edge.toList.idxOf ((2^a.val) ||| (2^b.val))) % 48
theorem andRow : ∀ (e : E) (a b : V), a≠b → dyad e a=true → dyad e b=true → e.val=pairRow a b := by
  decide +kernel
def pickA : Array Nat := #[4,0,12,0,4,4,10,4,12,0,10,10,12,0,1,1,0,1,5,5,11,5,0,1,11,11,12,1,1,2,1,2,6,6,12,6,1,2,12,0,0,2,2,3,2,3,7,7,0,7,2,3,4,1,1,3,1,4,3,4,8,8,1,8,3,4,5,2,2,4,2,5,4,5,9,9,2,9,10,5,6,3,3,5,3,6,5,6,10,10,3,4,11,6,7,4,4,6,4,7,6,7,11,11,12,5,12,7,8,5,5,7,5,8,7,8,12,0,0,6,0,8,9,6,6,8,6,9,8,9,10,1,1,7,1,9,10,7,7,9,1,10,9,10,11,2,2,8,2,10,11,8,8,10,2,11,12,11,12,3,3,9,3,11,12,9,9,11,3]
def atA (j : Fin 13) (v : Fin 13) : Bool :=
  (columnA[j.val]?.getD 0).testBit (v.val+0)
theorem orColumnA : ∀ (j : Fin 13) (a b : Fin 13), a≠b → atA j a=false → atA j b=false →
    j.val=pickA[a.val*13+b.val]?.getD 0 := by decide +kernel
def pickB : Array Nat := #[2,3,5,5,2,3,11,5,11,11,2,3,3,3,4,6,6,3,4,12,6,12,12,3,5,4,4,5,7,7,4,5,13,7,13,13,5,6,5,1,6,8,8,5,6,1,8,1,2,6,7,6,2,7,9,9,6,7,2,9,3,3,7,8,7,3,8,10,10,7,8,3,11,4,4,8,9,8,4,9,11,11,8,9,5,12,5,5,9,10,9,5,10,12,12,9,11,6,13,6,6,10,11,10,6,11,13,13,11,12,7,1,7,7,11,12,11,1,12,1,2,12,13,8,2,8,8,12,13,12,2,13,3,3,13,1,9,3,9,9,13,1,13,1]
def atB (j : Fin 14) (v : Fin 12) : Bool :=
  (columnB[j.val]?.getD 0).testBit (v.val+13)
theorem orColumnB : ∀ (j : Fin 14) (a b : Fin 12), a≠b → atB j a=false → atB j b=false →
    j.val=pickB[a.val*12+b.val]?.getD 0 := by decide +kernel
end PEqualNP.Outside.L_meta_9737.HelperBoard

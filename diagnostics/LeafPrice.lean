import PEqualNP.Defs

namespace PEqualNP.Outside.Pcx9792LeafPrice
abbrev F := Fin 16
def bit (x : F) (i : Fin 4) : Bool := x.val.testBit i.val
def pop (x : F) : Nat := ((List.finRange 4).filter (bit x)).length
def single (i : Fin 4) : F := ⟨(2^i.val)%16,Nat.mod_lt _ (by decide)⟩
def xor4 (x y : F) : F := ⟨(x.val ^^^ y.val)%16,Nat.mod_lt _ (by decide)⟩
def space (a b c : F) : List F := [0,a,b,c,xor4 a b,xor4 a c,xor4 b c,xor4 (xor4 a b) c]
def paid (a b c : F) : Nat := ([a,b,c].filter fun x => x != 0).length
def unitMask (a b c : F) : F := ⟨((List.finRange 4).foldl (fun n i =>
  if (space a b c).contains (single i) then n+2^i.val else n) 0)%16,Nat.mod_lt _ (by decide)⟩
def touch (a b c : F) : F := ⟨(a.val ||| b.val ||| c.val)%16,Nat.mod_lt _ (by decide)⟩
def punct (a b c : F) : F := ⟨((List.finRange 4).foldl (fun n i =>
  if (space a b c).contains (xor4 15 (single i)) then n+2^i.val else n) 0)%16,Nat.mod_lt _ (by decide)⟩
def inside (x y : F) : Bool := (x.val &&& y.val) == x.val

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- A three-generator GF(2) bank pays for each independent singleton pattern,
and for one more generator if it reaches outside their coordinates. -/
theorem rowTable : ∀ a b c : F,
    pop (unitMask a b c) + (if inside (touch a b c) (unitMask a b c) then 0 else 1) ≤ paid a b c := by
  decide +kernel

/-- The full four-row pattern and its punctures demand independent generators. -/
theorem lineTable : ∀ a b c : F, (space a b c).contains 15 = true →
    min 4 (1+pop (punct a b c)) ≤ paid a b c := by decide +kernel

theorem smaller : ∀ un tm real : F, inside un real = true → inside un tm = true →
    pop un + (if inside tm un then 0 else 1) ≤
      pop real + (if inside tm real then 0 else 1) := by decide +kernel

theorem lineSub : ∀ x y : F, inside x y = true →
    min 4 (1+pop x) ≤ min 4 (1+pop y) := by decide +kernel

theorem pointPrice (a b c un : F) (forced : inside un (unitMask a b c)=true)
    (live : inside un (touch a b c)=true) :
    pop un + (if inside (touch a b c) un then 0 else 1) ≤ paid a b c :=
  (smaller un (touch a b c) (unitMask a b c) forced live).trans (rowTable a b c)

theorem linePrice (a b c modif : F) (full : (space a b c).contains 15=true)
    (zeros : inside modif (punct a b c)=true) : min 4 (1+pop modif) ≤ paid a b c :=
  (lineSub modif (punct a b c) zeros).trans (lineTable a b c full)

end PEqualNP.Outside.Pcx9792LeafPrice

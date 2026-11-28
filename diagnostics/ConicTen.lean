import PEqualNP.Defs

namespace Research10009.ConicTen
abbrev V := Fin 31
def rows : List Nat := [1141899472, 136315297, 272630594, 545261188, 1090522376, 33561105, 67122210, 134244420, 268488840, 536977680, 1073955360, 427073, 854146, 1708292, 3416584, 6833168, 13666336, 27332672, 54665344, 109330688, 218661376, 437322752, 874645504, 1749291008, 1351098369, 554713091, 1109426182, 71368717, 142737434, 285474868, 570949736]
def boxes : List (Nat × Nat) := [(1478533120, 1090824832), (268701696, 1949357921), (539033600, 1679979467), (805306586, 39419904), (772031236, 143133696), (22356098, 328730), (116067375, 532488), (1406026791, 33796), (105024, 1526726668), (3150096, 549593204)]
def absPoints : List Nat := [12, 16, 18, 21, 28, 29]
def absLines : List Nat := [19, 15, 13, 10, 3, 2]
def boundary (i j : V) := absPoints.contains i.val || absLines.contains j.val
def covered (i j : V) := boxes.any fun b => b.1.testBit i.val && b.2.testBit j.val
def zero (i j : V) := !((rows.getD i.val 0).testBit j.val)
def allFlags := (List.finRange 31).flatMap (fun i => (List.finRange 31).map (fun j => (i,j)))
set_option maxRecDepth 12000 in
theorem census : boxes.length=10 ∧
    (allFlags.filter (fun p => covered p.1 p.2)).length=389 ∧
    (allFlags.filter (fun p => zero p.1 p.2 && boundary p.1 p.2)).length=270 := by decide +kernel
set_option maxRecDepth 12000 in
theorem coversBoundary : ∀i j : V,(covered i j=true → zero i j=true) ∧
    (zero i j=true → boundary i j=true → covered i j=true) := by decide +kernel
end Research10009.ConicTen

import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_10009.AffineLift
open Finset
abbrev V := Fin 31
abbrev A := Fin 25
abbrev L := Fin 30
abbrev ProjectiveBox := Finset V × Finset V
abbrev AffineBox := Finset A × Finset L
def matrixP : List Nat := [1141899472,136315297,272630594,545261188,1090522376,33561105,67122210,134244420,268488840,536977680,1073955360,427073,854146,1708292,3416584,6833168,13666336,27332672,54665344,109330688,218661376,437322752,874645504,1749291008,1351098369,554713091,1109426182,71368717,142737434,285474868,570949736]
def matrixA : List Nat := [34636833,35719234,37884036,42213640,50872848,69345793,71581730,76022852,83921032,68227344,138938625,142643714,151068708,135413832,136578192,276906113,285345026,269748740,271061032,272670800,553914433,538452098,539017476,541132296,545392688]
def pg (p j : V) := (matrixP.getD p.val 0).testBit j.val
def ag (p : A) (j : L) := (matrixA.getD p.val 0).testBit j.val
def pointIndex : Array Nat := #[0,1,5,30,29,6,28,10,3,18,9,25,2,14,7,26,23,20,4,22,8,27,19,17,21,16,13,11,24,12,15]
def lineIndex : Array Nat := #[1,17,27,23,5,16,0,25,21,26,30,22,18,19,8,3,12,4,2,7,10,6,9,29,24,14,15,11,13,28,20]
def finitePt (p : V) : Bool := pointIndex[p.val]! < 25
def finiteLn (p : V) : Bool := lineIndex[p.val]! < 30
def point (p : V) : A := ⟨pointIndex[p.val]! % 25, Nat.mod_lt _ (by decide)⟩
def line (p : V) : L := ⟨lineIndex[p.val]! % 30, Nat.mod_lt _ (by decide)⟩
def ext (b : AffineBox) : ProjectiveBox :=
  (univ.filter (fun p => finitePt p = true ∧ point p ∈ b.1),
   univ.filter (fun j => finiteLn j = true → line j ∈ b.2))
def bits (m : Nat) : Finset V := univ.filter fun v => m.testBit v.val = true
def fixedMasks : List (Nat × Nat) := [(34880, 2073103244), (2099216, 619213494), (2129928, 1158068587), (88, 444579921)]
def border : List ProjectiveBox := fixedMasks.map fun b => (bits b.1, bits b.2)
theorem borderLength : border.length = 4 := by decide
theorem affineFaces : ∀ p j : V, finitePt p = true → finiteLn j = true →
    pg p j = ag (point p) (line j) := by decide +kernel
theorem boundary : ∀ p j : V, finitePt p = true → finiteLn j = false →
    pg p j = false := by decide +kernel
theorem someZero : ∀ p : A, ∃ q : L, ag p q = false := by decide +kernel
theorem fixedSound : ∀ b ∈ fixedMasks, ∀ p j : V, b.1.testBit p.val = true →
    b.2.testBit j.val = true → pg p j = false := by decide +kernel
theorem fixedComplete : ∀ p j : V, finitePt p = false → pg p j = false →
    ∃ b ∈ fixedMasks, b.1.testBit p.val = true ∧ b.2.testBit j.val = true := by decide +kernel

theorem transfer (source : (∃ L : List (Finset (Fin 25) × Finset (Fin 30)), L.length ≤ 15 ∧ (∀ r ∈ L, ∀ i ∈ r.1, ∀ j ∈ r.2, (([34636833, 35719234, 37884036, 42213640, 50872848, 69345793, 71581730, 76022852, 83921032, 68227344, 138938625, 142643714, 151068708, 135413832, 136578192, 276906113, 285345026, 269748740, 271061032, 272670800, 553914433, 538452098, 539017476, 541132296, 545392688] : List ℕ).getD i.val 0).testBit j.val = false) ∧ ∀ (i : Fin 25) (j : Fin 30), (([34636833, 35719234, 37884036, 42213640, 50872848, 69345793, 71581730, 76022852, 83921032, 68227344, 138938625, 142643714, 151068708, 135413832, 136578192, 276906113, 285345026, 269748740, 271061032, 272670800, 553914433, 538452098, 539017476, 541132296, 545392688] : List ℕ).getD i.val 0).testBit j.val = false → ∃ r ∈ L, i ∈ r.1 ∧ j ∈ r.2)) : (∃ L : List (Finset (Fin 31) × Finset (Fin 31)), L.length ≤ 19 ∧ (∀ r ∈ L, ∀ i ∈ r.1, ∀ j ∈ r.2, (([1141899472, 136315297, 272630594, 545261188, 1090522376, 33561105, 67122210, 134244420, 268488840, 536977680, 1073955360, 427073, 854146, 1708292, 3416584, 6833168, 13666336, 27332672, 54665344, 109330688, 218661376, 437322752, 874645504, 1749291008, 1351098369, 554713091, 1109426182, 71368717, 142737434, 285474868, 570949736] : List ℕ).getD i.val 0).testBit j.val = false) ∧ ∀ (i : Fin 31) (j : Fin 31), (([1141899472, 136315297, 272630594, 545261188, 1090522376, 33561105, 67122210, 134244420, 268488840, 536977680, 1073955360, 427073, 854146, 1708292, 3416584, 6833168, 13666336, 27332672, 54665344, 109330688, 218661376, 437322752, 874645504, 1749291008, 1351098369, 554713091, 1109426182, 71368717, 142737434, 285474868, 570949736] : List ℕ).getD i.val 0).testBit j.val = false → ∃ r ∈ L, i ∈ r.1 ∧ j ∈ r.2) := by
  rcases source with ⟨C,cap,legal,hits⟩
  refine ⟨C.map ext ++ border, ?_, ?_, ?_⟩
  · simp only [List.length_append,List.length_map,borderLength]
    omega
  · intro z hz p hp l hl
    rcases List.mem_append.mp hz with own | extra
    · obtain ⟨b,bc,rfl⟩ := List.mem_map.mp own
      have pr : finitePt p = true ∧ point p ∈ b.1 := (mem_filter.mp hp).2
      have cl : finiteLn l = true → line l ∈ b.2 := (mem_filter.mp hl).2
      change pg p l = false
      cases h : finiteLn l with
      | false => exact boundary p l pr.1 h
      | true =>
        rw [affineFaces p l pr.1 h]
        exact legal b bc (point p) pr.2 (line l) (cl h)
    · obtain ⟨b,mem,rfl⟩ := List.mem_map.mp extra
      exact fixedSound b mem p l ((mem_filter.mp hp).2) ((mem_filter.mp hl).2)
  · intro p l blank
    change pg p l = false at blank
    cases f : finitePt p with
    | false =>
      obtain ⟨b,mem,r,c⟩ := fixedComplete p l f blank
      refine ⟨_,List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨b,mem,rfl⟩)),?_,?_⟩
      · exact mem_filter.mpr ⟨mem_univ _,r⟩
      · exact mem_filter.mpr ⟨mem_univ _,c⟩
    | true =>
      have lift (b : AffineBox) (bc : b ∈ C) (r : point p ∈ b.1)
          (s : finiteLn l = true → line l ∈ b.2) :
          ∃ b ∈ C.map ext ++ border, p ∈ b.1 ∧ l ∈ b.2 := by
        refine ⟨ext b,List.mem_append.mpr (Or.inl (List.mem_map.mpr ⟨b,bc,rfl⟩)),?_,?_⟩
        · exact mem_filter.mpr ⟨mem_univ _,f,r⟩
        · exact mem_filter.mpr ⟨mem_univ _,s⟩
      cases q : finiteLn l with
      | false =>
        obtain ⟨z,zero⟩ := someZero (point p)
        obtain ⟨b,bc,r,_⟩ := hits (point p) z zero
        exact lift b bc r (by simp [q])
      | true =>
        have zero := (affineFaces p l f q).symm.trans blank
        obtain ⟨b,bc,r,c⟩ := hits (point p) (line l) zero
        exact lift b bc r (fun _ => c)
end PEqualNP.Outside.L_meta_10009.AffineLift

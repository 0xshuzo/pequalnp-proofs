import PEqualNP.Defs

namespace Upper58PCX150
open PEqualNP.ProofComplexity
abbrev V := Fin 4 × Fin 3
abbrev F := PHP 4 3
set_option maxRecDepth 10000

def c0 : Clause V := {((0,0),true),((0,1),true),((0,2),true)}
def r0 : List (Clause V) := c0 :: []
theorem d0 : IsDerivation F r0 :=
  IsDerivation.ax IsDerivation.nil (Or.inl ⟨0,by decide +kernel⟩)
def c1 : Clause V := {((1,0),true),((1,1),true),((1,2),true)}
def r1 : List (Clause V) := c1 :: r0
theorem d1 : IsDerivation F r1 :=
  IsDerivation.ax d0 (Or.inl ⟨1,by decide +kernel⟩)
def c2 : Clause V := {((2,0),true),((2,1),true),((2,2),true)}
def r2 : List (Clause V) := c2 :: r1
theorem d2 : IsDerivation F r2 :=
  IsDerivation.ax d1 (Or.inl ⟨2,by decide +kernel⟩)
def c3 : Clause V := {((3,0),true),((3,1),true),((3,2),true)}
def r3 : List (Clause V) := c3 :: r2
theorem d3 : IsDerivation F r3 :=
  IsDerivation.ax d2 (Or.inl ⟨3,by decide +kernel⟩)
def c4 : Clause V := {((0,0),false),((1,0),false)}
def r4 : List (Clause V) := c4 :: r3
theorem d4 : IsDerivation F r4 :=
  IsDerivation.ax d3 (Or.inr ⟨0,1,0,by decide +kernel,by decide +kernel⟩)
def c5 : Clause V := {((0,0),false),((2,0),false)}
def r5 : List (Clause V) := c5 :: r4
theorem d5 : IsDerivation F r5 :=
  IsDerivation.ax d4 (Or.inr ⟨0,2,0,by decide +kernel,by decide +kernel⟩)
def c6 : Clause V := {((1,0),false),((2,0),false)}
def r6 : List (Clause V) := c6 :: r5
theorem d6 : IsDerivation F r6 :=
  IsDerivation.ax d5 (Or.inr ⟨1,2,0,by decide +kernel,by decide +kernel⟩)
def c7 : Clause V := {((0,0),false),((3,0),false)}
def r7 : List (Clause V) := c7 :: r6
theorem d7 : IsDerivation F r7 :=
  IsDerivation.ax d6 (Or.inr ⟨0,3,0,by decide +kernel,by decide +kernel⟩)
def c8 : Clause V := {((1,0),false),((3,0),false)}
def r8 : List (Clause V) := c8 :: r7
theorem d8 : IsDerivation F r8 :=
  IsDerivation.ax d7 (Or.inr ⟨1,3,0,by decide +kernel,by decide +kernel⟩)
def c9 : Clause V := {((2,0),false),((3,0),false)}
def r9 : List (Clause V) := c9 :: r8
theorem d9 : IsDerivation F r9 :=
  IsDerivation.ax d8 (Or.inr ⟨2,3,0,by decide +kernel,by decide +kernel⟩)
def c10 : Clause V := {((0,1),false),((1,1),false)}
def r10 : List (Clause V) := c10 :: r9
theorem d10 : IsDerivation F r10 :=
  IsDerivation.ax d9 (Or.inr ⟨0,1,1,by decide +kernel,by decide +kernel⟩)
def c11 : Clause V := {((0,1),false),((2,1),false)}
def r11 : List (Clause V) := c11 :: r10
theorem d11 : IsDerivation F r11 :=
  IsDerivation.ax d10 (Or.inr ⟨0,2,1,by decide +kernel,by decide +kernel⟩)
def c12 : Clause V := {((1,1),false),((2,1),false)}
def r12 : List (Clause V) := c12 :: r11
theorem d12 : IsDerivation F r12 :=
  IsDerivation.ax d11 (Or.inr ⟨1,2,1,by decide +kernel,by decide +kernel⟩)
def c13 : Clause V := {((0,1),false),((3,1),false)}
def r13 : List (Clause V) := c13 :: r12
theorem d13 : IsDerivation F r13 :=
  IsDerivation.ax d12 (Or.inr ⟨0,3,1,by decide +kernel,by decide +kernel⟩)
def c14 : Clause V := {((1,1),false),((3,1),false)}
def r14 : List (Clause V) := c14 :: r13
theorem d14 : IsDerivation F r14 :=
  IsDerivation.ax d13 (Or.inr ⟨1,3,1,by decide +kernel,by decide +kernel⟩)
def c15 : Clause V := {((2,1),false),((3,1),false)}
def r15 : List (Clause V) := c15 :: r14
theorem d15 : IsDerivation F r15 :=
  IsDerivation.ax d14 (Or.inr ⟨2,3,1,by decide +kernel,by decide +kernel⟩)
def c16 : Clause V := {((0,2),false),((1,2),false)}
def r16 : List (Clause V) := c16 :: r15
theorem d16 : IsDerivation F r16 :=
  IsDerivation.ax d15 (Or.inr ⟨0,1,2,by decide +kernel,by decide +kernel⟩)
def c17 : Clause V := {((0,2),false),((2,2),false)}
def r17 : List (Clause V) := c17 :: r16
theorem d17 : IsDerivation F r17 :=
  IsDerivation.ax d16 (Or.inr ⟨0,2,2,by decide +kernel,by decide +kernel⟩)
def c18 : Clause V := {((1,2),false),((2,2),false)}
def r18 : List (Clause V) := c18 :: r17
theorem d18 : IsDerivation F r18 :=
  IsDerivation.ax d17 (Or.inr ⟨1,2,2,by decide +kernel,by decide +kernel⟩)
def c19 : Clause V := {((0,2),false),((3,2),false)}
def r19 : List (Clause V) := c19 :: r18
theorem d19 : IsDerivation F r19 :=
  IsDerivation.ax d18 (Or.inr ⟨0,3,2,by decide +kernel,by decide +kernel⟩)
def c20 : Clause V := {((1,2),false),((3,2),false)}
def r20 : List (Clause V) := c20 :: r19
theorem d20 : IsDerivation F r20 :=
  IsDerivation.ax d19 (Or.inr ⟨1,3,2,by decide +kernel,by decide +kernel⟩)
def c21 : Clause V := {((2,2),false),((3,2),false)}
def r21 : List (Clause V) := c21 :: r20
theorem d21 : IsDerivation F r21 :=
  IsDerivation.ax d20 (Or.inr ⟨2,3,2,by decide +kernel,by decide +kernel⟩)
def c22 : Clause V := {((1,0),true),((1,2),true),((2,1),false)}
def r22 : List (Clause V) := c22 :: r21
theorem d22 : IsDerivation F r22 := by
  apply IsDerivation.res (C := c1) (D := c12) d21
  · decide +kernel
  · decide +kernel
  · exact ⟨(1,1),by decide +kernel,by decide +kernel,by decide +kernel⟩
def c23 : Clause V := {((1,0),true),((1,2),true),((2,0),true),((2,2),true)}
def r23 : List (Clause V) := c23 :: r22
theorem d23 : IsDerivation F r23 := by
  apply IsDerivation.res (C := c2) (D := c22) d22
  · decide +kernel
  · decide +kernel
  · exact ⟨(2,1),by decide +kernel,by decide +kernel,by decide +kernel⟩
def c24 : Clause V := {((0,0),false),((1,2),true),((2,0),true),((2,2),true)}
def r24 : List (Clause V) := c24 :: r23
theorem d24 : IsDerivation F r24 := by
  apply IsDerivation.res (C := c23) (D := c4) d23
  · decide +kernel
  · decide +kernel
  · exact ⟨(1,0),by decide +kernel,by decide +kernel,by decide +kernel⟩
def c25 : Clause V := {((0,0),false),((1,2),true),((2,2),true)}
def r25 : List (Clause V) := c25 :: r24
theorem d25 : IsDerivation F r25 := by
  apply IsDerivation.res (C := c24) (D := c5) d24
  · decide +kernel
  · decide +kernel
  · exact ⟨(2,0),by decide +kernel,by decide +kernel,by decide +kernel⟩
def c26 : Clause V := {((1,1),true),((1,2),true),((2,0),false)}
def r26 : List (Clause V) := c26 :: r25
theorem d26 : IsDerivation F r26 := by
  apply IsDerivation.res (C := c1) (D := c6) d25
  · decide +kernel
  · decide +kernel
  · exact ⟨(1,0),by decide +kernel,by decide +kernel,by decide +kernel⟩
def c27 : Clause V := {((1,1),true),((1,2),true),((2,1),true),((2,2),true)}
def r27 : List (Clause V) := c27 :: r26
theorem d27 : IsDerivation F r27 := by
  apply IsDerivation.res (C := c2) (D := c26) d26
  · decide +kernel
  · decide +kernel
  · exact ⟨(2,0),by decide +kernel,by decide +kernel,by decide +kernel⟩
def c28 : Clause V := {((0,1),false),((1,1),true),((1,2),true),((2,2),true)}
def r28 : List (Clause V) := c28 :: r27
theorem d28 : IsDerivation F r28 := by
  apply IsDerivation.res (C := c27) (D := c11) d27
  · decide +kernel
  · decide +kernel
  · exact ⟨(2,1),by decide +kernel,by decide +kernel,by decide +kernel⟩
def c29 : Clause V := {((0,1),false),((1,2),true),((2,2),true)}
def r29 : List (Clause V) := c29 :: r28
theorem d29 : IsDerivation F r29 := by
  apply IsDerivation.res (C := c28) (D := c10) d28
  · decide +kernel
  · decide +kernel
  · exact ⟨(1,1),by decide +kernel,by decide +kernel,by decide +kernel⟩
def c30 : Clause V := {((0,0),true),((0,2),true),((1,2),true),((2,2),true)}
def r30 : List (Clause V) := c30 :: r29
theorem d30 : IsDerivation F r30 := by
  apply IsDerivation.res (C := c0) (D := c29) d29
  · decide +kernel
  · decide +kernel
  · exact ⟨(0,1),by decide +kernel,by decide +kernel,by decide +kernel⟩
def c31 : Clause V := {((0,2),true),((1,2),true),((2,2),true)}
def r31 : List (Clause V) := c31 :: r30
theorem d31 : IsDerivation F r31 := by
  apply IsDerivation.res (C := c30) (D := c25) d30
  · decide +kernel
  · decide +kernel
  · exact ⟨(0,0),by decide +kernel,by decide +kernel,by decide +kernel⟩
def c32 : Clause V := {((0,2),true),((2,2),true),((3,2),false)}
def r32 : List (Clause V) := c32 :: r31
theorem d32 : IsDerivation F r32 := by
  apply IsDerivation.res (C := c31) (D := c20) d31
  · decide +kernel
  · decide +kernel
  · exact ⟨(1,2),by decide +kernel,by decide +kernel,by decide +kernel⟩
def c33 : Clause V := {((2,2),true),((3,2),false)}
def r33 : List (Clause V) := c33 :: r32
theorem d33 : IsDerivation F r33 := by
  apply IsDerivation.res (C := c32) (D := c19) d32
  · decide +kernel
  · decide +kernel
  · exact ⟨(0,2),by decide +kernel,by decide +kernel,by decide +kernel⟩
def c34 : Clause V := {((3,2),false)}
def r34 : List (Clause V) := c34 :: r33
theorem d34 : IsDerivation F r34 := by
  apply IsDerivation.res (C := c33) (D := c21) d33
  · decide +kernel
  · decide +kernel
  · exact ⟨(2,2),by decide +kernel,by decide +kernel,by decide +kernel⟩
def c35 : Clause V := {((1,0),true),((1,1),true),((2,2),false)}
def r35 : List (Clause V) := c35 :: r34
theorem d35 : IsDerivation F r35 := by
  apply IsDerivation.res (C := c1) (D := c18) d34
  · decide +kernel
  · decide +kernel
  · exact ⟨(1,2),by decide +kernel,by decide +kernel,by decide +kernel⟩
def c36 : Clause V := {((1,0),true),((1,1),true),((2,0),true),((2,1),true)}
def r36 : List (Clause V) := c36 :: r35
theorem d36 : IsDerivation F r36 := by
  apply IsDerivation.res (C := c2) (D := c35) d35
  · decide +kernel
  · decide +kernel
  · exact ⟨(2,2),by decide +kernel,by decide +kernel,by decide +kernel⟩
def c37 : Clause V := {((0,0),false),((1,1),true),((2,0),true),((2,1),true)}
def r37 : List (Clause V) := c37 :: r36
theorem d37 : IsDerivation F r37 := by
  apply IsDerivation.res (C := c36) (D := c4) d36
  · decide +kernel
  · decide +kernel
  · exact ⟨(1,0),by decide +kernel,by decide +kernel,by decide +kernel⟩
def c38 : Clause V := {((0,0),false),((1,1),true),((2,1),true)}
def r38 : List (Clause V) := c38 :: r37
theorem d38 : IsDerivation F r38 := by
  apply IsDerivation.res (C := c37) (D := c5) d37
  · decide +kernel
  · decide +kernel
  · exact ⟨(2,0),by decide +kernel,by decide +kernel,by decide +kernel⟩
def c39 : Clause V := {((0,1),true),((0,2),true),((1,1),true),((2,1),true)}
def r39 : List (Clause V) := c39 :: r38
theorem d39 : IsDerivation F r39 := by
  apply IsDerivation.res (C := c0) (D := c38) d38
  · decide +kernel
  · decide +kernel
  · exact ⟨(0,0),by decide +kernel,by decide +kernel,by decide +kernel⟩
def c40 : Clause V := {((0,2),false),((1,1),true),((2,1),true),((2,2),true)}
def r40 : List (Clause V) := c40 :: r39
theorem d40 : IsDerivation F r40 := by
  apply IsDerivation.res (C := c27) (D := c16) d39
  · decide +kernel
  · decide +kernel
  · exact ⟨(1,2),by decide +kernel,by decide +kernel,by decide +kernel⟩
def c41 : Clause V := {((0,2),false),((1,1),true),((2,1),true)}
def r41 : List (Clause V) := c41 :: r40
theorem d41 : IsDerivation F r41 := by
  apply IsDerivation.res (C := c40) (D := c17) d40
  · decide +kernel
  · decide +kernel
  · exact ⟨(2,2),by decide +kernel,by decide +kernel,by decide +kernel⟩
def c42 : Clause V := {((0,1),true),((1,1),true),((2,1),true)}
def r42 : List (Clause V) := c42 :: r41
theorem d42 : IsDerivation F r42 := by
  apply IsDerivation.res (C := c39) (D := c41) d41
  · decide +kernel
  · decide +kernel
  · exact ⟨(0,2),by decide +kernel,by decide +kernel,by decide +kernel⟩
def c43 : Clause V := {((0,1),true),((1,1),true),((3,1),false)}
def r43 : List (Clause V) := c43 :: r42
theorem d43 : IsDerivation F r43 := by
  apply IsDerivation.res (C := c42) (D := c15) d42
  · decide +kernel
  · decide +kernel
  · exact ⟨(2,1),by decide +kernel,by decide +kernel,by decide +kernel⟩
def c44 : Clause V := {((1,1),true),((3,1),false)}
def r44 : List (Clause V) := c44 :: r43
theorem d44 : IsDerivation F r44 := by
  apply IsDerivation.res (C := c43) (D := c13) d43
  · decide +kernel
  · decide +kernel
  · exact ⟨(0,1),by decide +kernel,by decide +kernel,by decide +kernel⟩
def c45 : Clause V := {((3,1),false)}
def r45 : List (Clause V) := c45 :: r44
theorem d45 : IsDerivation F r45 := by
  apply IsDerivation.res (C := c44) (D := c14) d44
  · decide +kernel
  · decide +kernel
  · exact ⟨(1,1),by decide +kernel,by decide +kernel,by decide +kernel⟩
def c46 : Clause V := {((3,0),true),((3,2),true)}
def r46 : List (Clause V) := c46 :: r45
theorem d46 : IsDerivation F r46 := by
  apply IsDerivation.res (C := c3) (D := c45) d45
  · decide +kernel
  · decide +kernel
  · exact ⟨(3,1),by decide +kernel,by decide +kernel,by decide +kernel⟩
def c47 : Clause V := {((0,1),false),((1,0),true),((2,0),true),((2,1),true)}
def r47 : List (Clause V) := c47 :: r46
theorem d47 : IsDerivation F r47 := by
  apply IsDerivation.res (C := c36) (D := c10) d46
  · decide +kernel
  · decide +kernel
  · exact ⟨(1,1),by decide +kernel,by decide +kernel,by decide +kernel⟩
def c48 : Clause V := {((0,1),false),((1,0),true),((2,0),true)}
def r48 : List (Clause V) := c48 :: r47
theorem d48 : IsDerivation F r48 := by
  apply IsDerivation.res (C := c47) (D := c11) d47
  · decide +kernel
  · decide +kernel
  · exact ⟨(2,1),by decide +kernel,by decide +kernel,by decide +kernel⟩
def c49 : Clause V := {((0,0),true),((0,2),true),((1,0),true),((2,0),true)}
def r49 : List (Clause V) := c49 :: r48
theorem d49 : IsDerivation F r49 := by
  apply IsDerivation.res (C := c0) (D := c48) d48
  · decide +kernel
  · decide +kernel
  · exact ⟨(0,1),by decide +kernel,by decide +kernel,by decide +kernel⟩
def c50 : Clause V := {((0,2),false),((1,0),true),((1,2),true),((2,0),true)}
def r50 : List (Clause V) := c50 :: r49
theorem d50 : IsDerivation F r50 := by
  apply IsDerivation.res (C := c23) (D := c17) d49
  · decide +kernel
  · decide +kernel
  · exact ⟨(2,2),by decide +kernel,by decide +kernel,by decide +kernel⟩
def c51 : Clause V := {((0,2),false),((1,0),true),((2,0),true)}
def r51 : List (Clause V) := c51 :: r50
theorem d51 : IsDerivation F r51 := by
  apply IsDerivation.res (C := c50) (D := c16) d50
  · decide +kernel
  · decide +kernel
  · exact ⟨(1,2),by decide +kernel,by decide +kernel,by decide +kernel⟩
def c52 : Clause V := {((0,0),true),((1,0),true),((2,0),true)}
def r52 : List (Clause V) := c52 :: r51
theorem d52 : IsDerivation F r52 := by
  apply IsDerivation.res (C := c49) (D := c51) d51
  · decide +kernel
  · decide +kernel
  · exact ⟨(0,2),by decide +kernel,by decide +kernel,by decide +kernel⟩
def c53 : Clause V := {((0,0),true),((2,0),true),((3,0),false)}
def r53 : List (Clause V) := c53 :: r52
theorem d53 : IsDerivation F r53 := by
  apply IsDerivation.res (C := c52) (D := c8) d52
  · decide +kernel
  · decide +kernel
  · exact ⟨(1,0),by decide +kernel,by decide +kernel,by decide +kernel⟩
def c54 : Clause V := {((0,0),true),((3,0),false)}
def r54 : List (Clause V) := c54 :: r53
theorem d54 : IsDerivation F r54 := by
  apply IsDerivation.res (C := c53) (D := c9) d53
  · decide +kernel
  · decide +kernel
  · exact ⟨(2,0),by decide +kernel,by decide +kernel,by decide +kernel⟩
def c55 : Clause V := {((3,0),false)}
def r55 : List (Clause V) := c55 :: r54
theorem d55 : IsDerivation F r55 := by
  apply IsDerivation.res (C := c54) (D := c7) d54
  · decide +kernel
  · decide +kernel
  · exact ⟨(0,0),by decide +kernel,by decide +kernel,by decide +kernel⟩
def c56 : Clause V := {((3,2),true)}
def r56 : List (Clause V) := c56 :: r55
theorem d56 : IsDerivation F r56 := by
  apply IsDerivation.res (C := c46) (D := c55) d55
  · decide +kernel
  · decide +kernel
  · exact ⟨(3,0),by decide +kernel,by decide +kernel,by decide +kernel⟩
def c57 : Clause V := ∅
def r57 : List (Clause V) := c57 :: r56
theorem d57 : IsDerivation F r57 := by
  apply IsDerivation.res (C := c56) (D := c34) d56
  · decide +kernel
  · decide +kernel
  · exact ⟨(3,2),by decide +kernel,by decide +kernel,by decide +kernel⟩
theorem witness : ∃ π : List (Clause V), IsRefutation (PHP 4 3) π ∧ π.length ≤ 58 :=
  ⟨r57,⟨d57,List.Mem.head _⟩,by decide +kernel⟩
end Upper58PCX150

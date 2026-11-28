import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_9838.CutPrice
abbrev Word := Fin 14 → Bool
def target (x : Word) := x 12 || (x 0 && x 7) || (x 1 && x 7) || (x 2 && x 8) ||
  (x 3 && x 7) || (x 4 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 5 && x 8) ||
  (x 6 && x 7) || (x 6 && x 9) || (x 8 && x 10) || (x 9 && x 11)
structure Observation where
  output : Bool
  taps : Word

def donor (x : Fin 40 → Bool) (replacement : Option Bool) : Observation :=
  let w40 := (x 8 || x 4)
  let w41 := (x 5 || w40)
  let w42 := (x 18 || w41)
  let w43 := (x 24 && w42)
  let w44 := (x 13 || x 14)
  let w45 := (x 17 || x 8)
  let w46 := (w45 || w44)
  let w47 := (x 33 && w46)
  let w48 := (x 11 || x 15)
  let w49 := (x 6 || x 12)
  let w50 := (w48 || w49)
  let w51 := (x 4 || w50)
  let w52 := (x 31 && w51)
  let w53 := (x 2 || x 8)
  let w54 := (x 0 || x 11)
  let w55 := (x 7 || w54)
  let w56 := (w53 || w55)
  let w57 := (x 27 && w56)
  let w58 := (x 3 || x 12)
  let w59 := (x 8 || w58)
  let w60 := (w59 || x 9)
  let w61 := (x 1 || w60)
  let w62 := (x 28 && w61)
  let w63 := (x 18 || x 7)
  let w64 := (w63 || x 14)
  let w65 := (w64 || x 15)
  let w66 := (x 9 || w65)
  let w67 := (x 34 && w66)
  let w68 := (x 7 || x 10)
  let w69 := (x 6 || x 1)
  let w70 := (w68 || w69)
  let w71 := (x 26 && w70)
  let w72 := (x 17 || x 16)
  let w73 := (x 9 || x 11)
  let w74 := (w72 || w73)
  let w75 := (x 36 && w74)
  let w76 := (x 7 || x 19)
  let w77 := (w76 || x 4)
  let w78 := (x 3 || w77)
  let w79 := (x 17 || w78)
  let w80 := (x 23 && w79)
  let w81 := (x 10 || x 16)
  let w82 := (x 15 || w81)
  let w83 := (x 8 || x 19)
  let w84 := (w83 || w82)
  let w85 := (x 35 && w84)
  let w86 := (x 13 || x 0)
  let w87 := (w86 || x 15)
  let w88 := (x 3 || w87)
  let w89 := (x 20 && w88)
  let w90 := (x 10 || x 9)
  let w91 := (x 13 || x 2)
  let w92 := (w91 || w90)
  let w93 := (x 4 || w92)
  let w94 := (x 29 && w93)
  let w95 := (x 6 || x 2)
  let w96 := (x 16 || w95)
  let w97 := (x 18 || x 3)
  let w98 := (w97 || w96)
  let w99 := (x 22 && w98)
  let w100 := (x 19 || x 6)
  let w101 := (x 5 || x 0)
  let w102 := (w100 || w101)
  let w103 := (w102 || x 9)
  let w104 := (x 25 && w103)
  let w105 := (x 0 || x 18)
  let w106 := (x 10 || x 17)
  let w107 := (x 12 || w106)
  let w108 := (w107 || w105)
  let w109 := (x 37 && w108)
  let w110 := (x 10 || x 11)
  let w111 := (x 14 || w110)
  let w112 := (x 3 || x 5)
  let w113 := (w111 || w112)
  let w114 := (x 30 && w113)
  let w115 := (x 13 || x 7)
  let w116 := (x 5 || w115)
  let w117 := (x 16 || x 12)
  let w118 := (w117 || w116)
  let w119 := (x 32 && w118)
  let w120 := (x 12 || x 19)
  let w121 := (x 2 || w120)
  let w122 := (x 14 || w121)
  let w123 := (x 39 && w122)
  let w124 := (x 1 || x 13)
  let w125 := (x 19 || x 18)
  let w126 := (x 11 || w125)
  let w127 := (w124 || w126)
  let w128 := (x 38 && w127)
  let w129 := (x 17 || x 2)
  let w130 := (x 15 || w129)
  let w131 := (x 1 || x 5)
  let w132 := (w130 || w131)
  let w133 := (x 21 && w132)
  let w134 := (w62 || w128)
  let w135 := (w104 || w133)
  let w136 := (w85 || w80)
  let w137 := (w136 || w47)
  let w138 := (w57 || w109)
  let w139 := (w138 || w75)
  let w140 := (w89 || w114)
  let w141 := replacement.getD (w137 || w99)
  let w142 := (w119 || w94)
  let w143 := (w139 || w142)
  let w144 := (w141 || w143)
  let w145 := (w140 || w67)
  let w146 := (w43 || w52)
  let w147 := (w145 || w123)
  let w148 := (w144 || w134)
  let w149 := (w146 || w148)
  let w150 := (w135 || w149)
  let w151 := (w71 || w147)
  let w152 := (w151 || w150)
  ⟨w152, ![x 3, x 4, x 6, x 7, x 8, x 17, x 19, x 23, x 33, x 35, w44, w82, w99, w103]⟩
def graph (x : Fin 40 → Bool) := (x 0 && x 20) || (x 0 && x 25) || (x 0 && x 27) || (x 0 && x 37) || (x 1 && x 21) || (x 1 && x 26) || (x 1 && x 28) || (x 1 && x 38) || (x 2 && x 21) || (x 2 && x 22) || (x 2 && x 27) || (x 2 && x 29) || (x 2 && x 39) || (x 3 && x 20) || (x 3 && x 22) || (x 3 && x 23) || (x 3 && x 28) || (x 3 && x 30) || (x 4 && x 23) || (x 4 && x 24) || (x 4 && x 29) || (x 4 && x 31) || (x 5 && x 21) || (x 5 && x 24) || (x 5 && x 25) || (x 5 && x 30) || (x 5 && x 32) || (x 6 && x 22) || (x 6 && x 25) || (x 6 && x 26) || (x 6 && x 31) || (x 6 && x 33) || (x 7 && x 23) || (x 7 && x 26) || (x 7 && x 27) || (x 7 && x 32) || (x 7 && x 34) || (x 8 && x 24) || (x 8 && x 27) || (x 8 && x 28) || (x 8 && x 33) || (x 8 && x 35) || (x 9 && x 25) || (x 9 && x 28) || (x 9 && x 29) || (x 9 && x 34) || (x 9 && x 36) || (x 10 && x 26) || (x 10 && x 29) || (x 10 && x 30) || (x 10 && x 35) || (x 10 && x 37) || (x 11 && x 27) || (x 11 && x 30) || (x 11 && x 31) || (x 11 && x 36) || (x 11 && x 38) || (x 12 && x 28) || (x 12 && x 31) || (x 12 && x 32) || (x 12 && x 37) || (x 12 && x 39) || (x 13 && x 20) || (x 13 && x 29) || (x 13 && x 32) || (x 13 && x 33) || (x 13 && x 38) || (x 14 && x 30) || (x 14 && x 33) || (x 14 && x 34) || (x 14 && x 39) || (x 15 && x 20) || (x 15 && x 21) || (x 15 && x 31) || (x 15 && x 34) || (x 15 && x 35) || (x 16 && x 22) || (x 16 && x 32) || (x 16 && x 35) || (x 16 && x 36) || (x 17 && x 21) || (x 17 && x 23) || (x 17 && x 33) || (x 17 && x 36) || (x 17 && x 37) || (x 18 && x 22) || (x 18 && x 24) || (x 18 && x 34) || (x 18 && x 37) || (x 18 && x 38) || (x 19 && x 23) || (x 19 && x 25) || (x 19 && x 35) || (x 19 && x 38) || (x 19 && x 39)
def embed (x : Word) : Fin 40→Bool := ![false, false, false, x 0, x 1, false, x 2, x 3, x 4, true, false, false, false, x 10, false, x 11, false, x 5, true, x 6, false, false, x 12, x 7, false, false, false, false, false, false, false, false, false, x 8, false, x 9, false, false, false, false]

set_option maxRecDepth 32768 in
set_option maxHeartbeats 1000000 in
theorem tapBind (x : Word) : (donor (embed x) none).taps=Function.update x 13 true := by
  funext i
  fin_cases i <;> simp [donor,embed,Function.update]

set_option maxRecDepth 32768 in
set_option maxHeartbeats 1000000 in
theorem passThrough (x : Word) (b : Bool) : (donor (embed x) (some b)).output=b := by
  simp [donor,embed]

set_option maxRecDepth 32768 in
theorem induced (x : Word) : graph (embed x)=target x := by
  simp [graph,embed,target] <;> ac_rfl

theorem forceSlice (f : Word → Bool)
    (correct : ∀ x : Fin 40→Bool, (donor x (some (f (donor x none).taps))).output=graph x) :
    ∀ x, x 13=true → f x=target x := by
  intro x on
  have h := correct (embed x)
  rw [tapBind,passThrough,induced] at h
  have same : Function.update x 13 true=x := by rw [←on];exact Function.update_eq_self _ _
  rwa [same] at h
end PEqualNP.Outside.L_meta_9838.CutPrice

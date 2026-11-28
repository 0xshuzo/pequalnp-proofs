import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_10007_ForcedJoins
open Finset
abbrev P := Fin 31
abbrev Sides := Fin 17 → Nat

structure Plane where
  line : P → P → Finset P
  left : ∀a b, a∈line a b
  right : ∀a b, b∈line a b
  six : ∀a b, a≠b → (line a b).card=6
  unique : ∀a b x y, x≠y → x∈line a b → y∈line a b → line x y=line a b

def Separates (B : Sides) (g : Plane) : Prop :=
  ∀a b : P, a≠b → ∀p∉g.line a b, ∃i : Fin 17, (B i).testBit p.val=true ∧
    ∀q∈g.line a b, (B i).testBit q.val=false

theorem forced {B : Sides} {g : Plane} (good : Separates B g)
    {a b p : P} (ab : a≠b) (w : List P)
    (dom : ∀i : Fin 17, (B i).testBit p.val=true →
      ∃q∈w, (B i).testBit q.val=true)
    (inside : ∀q∈w, q∈g.line a b) : p∈g.line a b := by
  classical
  by_contra outside
  obtain ⟨i,hit,avoid⟩:=good a b ab p outside
  obtain ⟨q,mem,on⟩:=dom i hit
  have off:=avoid q (inside q mem)
  simp [off] at on

def bank0 (i : Fin 17) : Nat := ([1619034128, 281608487, 541068162, 205914684, 286791024, 134861416, 269559504, 304532228, 719340640, 2032474113, 76832834, 1077018888, 50364559, 688808961, 101328896, 86064262, 72618629] : List Nat).getD i.val 0

theorem impossible0 (g : Plane) (good : Separates bank0 g) : False := by
  have h0 : (2 : P)∈g.line 2 7 := g.left _ _
  have h1 : (7 : P)∈g.line 2 7 := g.right _ _
  have h2 : (1 : P)∈g.line 1 9 := g.left _ _
  have h3 : (9 : P)∈g.line 1 9 := g.right _ _
  have h4 : (2 : P)∈g.line 1 9 := by
    apply forced good (by decide) [1, 9]
    · decide
    · intro q hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | hq
      · exact h2
      subst q
      exact h3
  have h5 : (7 : P)∈g.line 1 9 := by
    apply forced good (by decide) [1, 9]
    · decide
    · intro q hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | hq
      · exact h2
      subst q
      exact h3
  have h6 : (1 : P)∈g.line 2 7 := by rw [(g.unique 1 9 2 7 (by decide) h4 h5)]; exact h2
  have h7 : (9 : P)∈g.line 2 7 := by rw [(g.unique 1 9 2 7 (by decide) h4 h5)]; exact h3
  have h8 : (1 : P)∈g.line 1 18 := g.left _ _
  have h9 : (18 : P)∈g.line 1 18 := g.right _ _
  have h10 : (2 : P)∈g.line 1 18 := by
    apply forced good (by decide) [1, 18]
    · decide
    · intro q hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | hq
      · exact h8
      subst q
      exact h9
  have h11 : (18 : P)∈g.line 1 2 := by rw [(g.unique 1 18 1 2 (by decide) h8 h10)]; exact h9
  have h12 : (18 : P)∈g.line 2 7 := by rw [← (g.unique 2 7 1 2 (by decide) h6 h0)]; exact h11
  have h13 : (0 : P)∈g.line 1 18 := by
    apply forced good (by decide) [1, 18]
    · decide
    · intro q hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | hq
      · exact h8
      subst q
      exact h9
  have h14 : (0 : P)∈g.line 1 2 := by rw [(g.unique 1 18 1 2 (by decide) h8 h10)]; exact h13
  have h15 : (0 : P)∈g.line 2 7 := by rw [← (g.unique 2 7 1 2 (by decide) h6 h0)]; exact h14
  have h16 : (1 : P)∈g.line 1 20 := g.left _ _
  have h17 : (20 : P)∈g.line 1 20 := g.right _ _
  have h18 : (7 : P)∈g.line 1 20 := by
    apply forced good (by decide) [1, 20]
    · decide
    · intro q hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | hq
      · exact h16
      subst q
      exact h17
  have h19 : (20 : P)∈g.line 1 7 := by rw [(g.unique 1 20 1 7 (by decide) h16 h18)]; exact h17
  have h20 : (20 : P)∈g.line 2 7 := by rw [← (g.unique 2 7 1 7 (by decide) h6 h1)]; exact h19
  have inc : ({2, 7, 1, 9, 18, 0, 20} : Finset P) ⊆ g.line 2 7 := by
    intro q mem
    simp only [mem_insert, mem_singleton] at mem
    rcases mem with rfl | mem
    · exact h0
    rcases mem with rfl | mem
    · exact h1
    rcases mem with rfl | mem
    · exact h6
    rcases mem with rfl | mem
    · exact h7
    rcases mem with rfl | mem
    · exact h12
    rcases mem with rfl | mem
    · exact h15
    subst q
    exact h20
  have large:=card_le_card inc
  rw [g.six 2 7 (by decide)] at large
  have seven : ({2, 7, 1, 9, 18, 0, 20} : Finset P).card = 7 := by decide
  omega

def bank1 (i : Fin 17) : Nat := ([76784259, 17376260, 1121452546, 136069152, 544211012, 1493303360, 304349313, 1140852772, 8946112, 2118400, 276908112, 1078339859, 34050056, 671124482, 406858424, 620757016, 8393769] : List Nat).getD i.val 0

theorem impossible1 (g : Plane) (good : Separates bank1 g) : False := by
  have h0 : (3 : P)∈g.line 3 12 := g.left _ _
  have h1 : (12 : P)∈g.line 3 12 := g.right _ _
  have h2 : (3 : P)∈g.line 3 8 := g.left _ _
  have h3 : (8 : P)∈g.line 3 8 := g.right _ _
  have h4 : (12 : P)∈g.line 3 8 := by
    apply forced good (by decide) [3, 8]
    · decide
    · intro q hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | hq
      · exact h2
      subst q
      exact h3
  have h5 : (8 : P)∈g.line 3 12 := by rw [(g.unique 3 8 3 12 (by decide) h2 h4)]; exact h3
  have h6 : (3 : P)∈g.line 3 9 := g.left _ _
  have h7 : (9 : P)∈g.line 3 9 := g.right _ _
  have h8 : (12 : P)∈g.line 3 9 := by
    apply forced good (by decide) [3, 9]
    · decide
    · intro q hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | hq
      · exact h6
      subst q
      exact h7
  have h9 : (9 : P)∈g.line 3 12 := by rw [(g.unique 3 9 3 12 (by decide) h6 h8)]; exact h7
  have h10 : (3 : P)∈g.line 3 14 := g.left _ _
  have h11 : (14 : P)∈g.line 3 14 := g.right _ _
  have h12 : (12 : P)∈g.line 3 14 := by
    apply forced good (by decide) [3, 14]
    · decide
    · intro q hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | hq
      · exact h10
      subst q
      exact h11
  have h13 : (14 : P)∈g.line 3 12 := by rw [(g.unique 3 14 3 12 (by decide) h10 h12)]; exact h11
  have h14 : (3 : P)∈g.line 3 21 := g.left _ _
  have h15 : (21 : P)∈g.line 3 21 := g.right _ _
  have h16 : (12 : P)∈g.line 3 21 := by
    apply forced good (by decide) [3, 21]
    · decide
    · intro q hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | hq
      · exact h14
      subst q
      exact h15
  have h17 : (21 : P)∈g.line 3 12 := by rw [(g.unique 3 21 3 12 (by decide) h14 h16)]; exact h15
  have h18 : (4 : P)∈g.line 4 12 := g.left _ _
  have h19 : (12 : P)∈g.line 4 12 := g.right _ _
  have h20 : (3 : P)∈g.line 4 12 := by
    apply forced good (by decide) [4, 12]
    · decide
    · intro q hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | hq
      · exact h18
      subst q
      exact h19
  have h21 : (4 : P)∈g.line 3 12 := by rw [(g.unique 4 12 3 12 (by decide) h20 h19)]; exact h18
  have inc : ({3, 12, 8, 9, 14, 21, 4} : Finset P) ⊆ g.line 3 12 := by
    intro q mem
    simp only [mem_insert, mem_singleton] at mem
    rcases mem with rfl | mem
    · exact h0
    rcases mem with rfl | mem
    · exact h1
    rcases mem with rfl | mem
    · exact h5
    rcases mem with rfl | mem
    · exact h9
    rcases mem with rfl | mem
    · exact h13
    rcases mem with rfl | mem
    · exact h17
    subst q
    exact h21
  have large:=card_le_card inc
  rw [g.six 3 12 (by decide)] at large
  have seven : ({3, 12, 8, 9, 14, 21, 4} : Finset P).card = 7 := by decide
  omega

end PEqualNP.Outside.L_meta_10007_ForcedJoins

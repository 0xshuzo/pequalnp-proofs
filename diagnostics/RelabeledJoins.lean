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

def boardRows : List Nat := [1141899472, 136315297, 272630594, 545261188, 1090522376, 33561105, 67122210, 134244420, 268488840, 536977680, 1073955360, 427073, 854146, 1708292, 3416584, 6833168, 13666336, 27332672, 54665344, 109330688, 218661376, 437322752, 874645504, 1749291008, 1351098369, 554713091, 1109426182, 71368717, 142737434, 285474868, 570949736]

def joins : List (List Nat) := [[4, 7, 6, 7, 30, 4, 26, 6, 7, 4, 30, 6, 7, 20, 20, 4, 20, 6, 7, 26, 26, 20, 26, 30, 30, 20, 30, 26, 4, 4, 6], [7, 0, 8, 7, 8, 0, 5, 27, 7, 8, 5, 0, 7, 8, 21, 21, 5, 21, 7, 8, 27, 27, 21, 27, 0, 0, 21, 0, 27, 5, 5], [6, 8, 1, 9, 8, 9, 1, 6, 28, 8, 9, 6, 1, 8, 9, 22, 22, 6, 22, 8, 9, 28, 28, 22, 28, 1, 1, 22, 1, 28, 6], [7, 7, 9, 2, 10, 9, 10, 2, 7, 29, 9, 10, 7, 2, 9, 10, 23, 23, 7, 23, 9, 10, 29, 29, 23, 29, 2, 2, 23, 2, 29], [30, 8, 8, 10, 3, 11, 10, 11, 3, 8, 30, 10, 11, 8, 3, 10, 11, 24, 24, 8, 24, 10, 11, 30, 30, 24, 30, 3, 3, 24, 3], [4, 0, 9, 9, 11, 0, 12, 11, 12, 4, 9, 0, 11, 12, 9, 4, 11, 12, 25, 25, 9, 25, 11, 12, 0, 0, 25, 0, 4, 4, 25], [26, 5, 1, 10, 10, 12, 1, 13, 12, 13, 5, 10, 1, 12, 13, 10, 5, 12, 13, 26, 26, 10, 26, 12, 13, 1, 1, 26, 1, 5, 5], [6, 27, 6, 2, 11, 11, 13, 2, 14, 13, 14, 6, 11, 2, 13, 14, 11, 6, 13, 14, 27, 27, 11, 27, 13, 14, 2, 2, 27, 2, 6], [7, 7, 28, 7, 3, 12, 12, 14, 3, 15, 14, 15, 7, 12, 3, 14, 15, 12, 7, 14, 15, 28, 28, 12, 28, 14, 15, 3, 3, 28, 3], [4, 8, 8, 29, 8, 4, 13, 13, 15, 4, 16, 15, 16, 8, 13, 4, 15, 16, 13, 8, 15, 16, 29, 29, 13, 29, 15, 16, 4, 4, 29], [30, 5, 9, 9, 30, 9, 5, 14, 14, 16, 5, 17, 16, 17, 9, 14, 5, 16, 17, 14, 9, 16, 17, 30, 30, 14, 30, 16, 17, 5, 5], [6, 0, 6, 10, 10, 0, 10, 6, 15, 15, 17, 0, 18, 17, 18, 10, 15, 6, 17, 18, 15, 10, 17, 18, 0, 0, 15, 0, 17, 18, 6], [7, 7, 1, 7, 11, 11, 1, 11, 7, 16, 16, 18, 1, 19, 18, 19, 11, 16, 7, 18, 19, 16, 11, 18, 19, 1, 1, 16, 1, 18, 19], [20, 8, 8, 2, 8, 12, 12, 2, 12, 8, 17, 17, 19, 2, 20, 19, 20, 12, 17, 8, 19, 20, 17, 12, 19, 20, 2, 2, 17, 2, 19], [20, 21, 9, 9, 3, 9, 13, 13, 3, 13, 9, 18, 18, 20, 3, 21, 20, 21, 13, 18, 9, 20, 21, 18, 13, 20, 21, 3, 3, 18, 3], [4, 21, 22, 10, 10, 4, 10, 14, 14, 4, 14, 10, 19, 19, 21, 4, 22, 21, 22, 14, 19, 10, 21, 22, 19, 14, 21, 22, 4, 4, 19], [20, 5, 22, 23, 11, 11, 5, 11, 15, 15, 5, 15, 11, 20, 20, 22, 5, 23, 22, 23, 15, 20, 11, 22, 23, 20, 15, 22, 23, 5, 5], [6, 21, 6, 23, 24, 12, 12, 6, 12, 16, 16, 6, 16, 12, 21, 21, 23, 6, 24, 23, 24, 16, 21, 12, 23, 24, 21, 16, 23, 24, 6], [7, 7, 22, 7, 24, 25, 13, 13, 7, 13, 17, 17, 7, 17, 13, 22, 22, 24, 7, 25, 24, 25, 17, 22, 13, 24, 25, 22, 17, 24, 25], [26, 8, 8, 23, 8, 25, 26, 14, 14, 8, 14, 18, 18, 8, 18, 14, 23, 23, 25, 8, 26, 25, 26, 18, 23, 14, 25, 26, 23, 18, 25], [26, 27, 9, 9, 24, 9, 26, 27, 15, 15, 9, 15, 19, 19, 9, 19, 15, 24, 24, 26, 9, 27, 26, 27, 19, 24, 15, 26, 27, 24, 19], [20, 27, 28, 10, 10, 25, 10, 27, 28, 16, 16, 10, 16, 20, 20, 10, 20, 16, 25, 25, 27, 10, 28, 27, 28, 20, 25, 16, 27, 28, 25], [26, 21, 28, 29, 11, 11, 26, 11, 28, 29, 17, 17, 11, 17, 21, 21, 11, 21, 17, 26, 26, 28, 11, 29, 28, 29, 21, 26, 17, 28, 29], [30, 27, 22, 29, 30, 12, 12, 27, 12, 29, 30, 18, 18, 12, 18, 22, 22, 12, 22, 18, 27, 27, 29, 12, 30, 29, 30, 22, 27, 18, 29], [30, 0, 28, 23, 30, 0, 13, 13, 28, 13, 30, 0, 19, 19, 13, 19, 23, 23, 13, 23, 19, 28, 28, 30, 0, 0, 30, 0, 23, 28, 19], [20, 0, 1, 29, 24, 0, 1, 14, 14, 29, 14, 0, 1, 20, 20, 14, 20, 24, 24, 14, 24, 20, 29, 29, 0, 0, 1, 0, 1, 24, 29], [30, 21, 1, 2, 30, 25, 1, 2, 15, 15, 30, 15, 1, 2, 21, 21, 15, 21, 25, 25, 15, 25, 21, 30, 30, 1, 1, 2, 1, 2, 25], [26, 0, 22, 2, 3, 0, 26, 2, 3, 16, 16, 0, 16, 2, 3, 22, 22, 16, 22, 26, 26, 16, 26, 22, 0, 0, 2, 0, 3, 2, 3], [4, 27, 1, 23, 3, 4, 1, 27, 3, 4, 17, 17, 1, 17, 3, 4, 23, 23, 17, 23, 27, 27, 17, 27, 23, 1, 1, 3, 1, 4, 3], [4, 5, 28, 2, 24, 4, 5, 2, 28, 4, 5, 18, 18, 2, 18, 4, 5, 24, 24, 18, 24, 28, 28, 18, 28, 24, 2, 2, 4, 2, 5], [6, 5, 6, 29, 3, 25, 5, 6, 3, 29, 5, 6, 19, 19, 3, 19, 5, 6, 25, 25, 19, 25, 29, 29, 19, 29, 25, 3, 3, 5, 3]]

def entry (p l : P) : Bool := (boardRows.getD p.val 0).testBit l.val
def join (p q : P) : P :=
  ⟨((joins.getD p.val []).getD q.val 0)%31, Nat.mod_lt _ (by decide)⟩
def column (l : P) : Finset P := univ.filter (fun p=>entry p l)

set_option maxRecDepth 8000 in
theorem incidence : ∀a b : P, entry a (join a b)=true ∧ entry b (join a b)=true := by decide +kernel
set_option maxRecDepth 8000 in
theorem colSix : ∀l : P, (column l).card=6 := by decide +kernel
set_option maxRecDepth 8000 in
theorem joinUnique : ∀l x y : P, x≠y → entry x l=true → entry y l=true → join x y=l := by decide +kernel

def rel (e : P ≃ P) (a b : P) : Finset P := (column (join (e a) (e b))).map e.symm.toEmbedding

theorem rel_mem (e : P ≃ P) (a b p : P) : p∈rel e a b ↔ entry (e p) (join (e a) (e b))=true := by
  constructor
  · intro h
    obtain ⟨q,hq,eq⟩:=mem_map.mp h
    have hit : e p=q := by rw [←eq]; simp
    rw [hit]
    exact (mem_filter.mp hq).2
  · intro h
    exact mem_map.mpr ⟨e p,mem_filter.mpr ⟨mem_univ _,h⟩,by simp⟩

def relPlane (e : P ≃ P) : Plane where
  line := rel e
  left := fun a b=>(rel_mem e a b a).2 (incidence (e a) (e b)).1
  right := fun a b=>(rel_mem e a b b).2 (incidence (e a) (e b)).2
  six := by intro a b _; simpa [rel] using colSix (join (e a) (e b))
  unique := by
    intro a b x y ne hx hy
    have h:=joinUnique (join (e a) (e b)) (e x) (e y) (fun eq=>ne (e.injective eq))
      ((rel_mem e a b x).1 hx) ((rel_mem e a b y).1 hy)
    unfold rel
    rw [h]

theorem physical {B : Sides} (e : P ≃ P) (n : Nat)
    (select : Fin n → Finset (Fin 17)) (right : Fin n → Finset P)
    (blank : ∀t p l, (∃i∈select t, (B i).testBit (p : P).val=true) →
        l∈right t → entry (e p) l=false)
    (covered : ∀p l, entry (e p) l=false →
        ∃t, (∃i∈select t, (B i).testBit p.val=true) ∧ l∈right t) :
    Separates B (relPlane e) := by
  intro a b _ p hp
  have misses : entry (e p) (join (e a) (e b))=false := by
    cases h : entry (e p) (join (e a) (e b))
    · rfl
    · exact False.elim (hp ((rel_mem e a b p).2 h))
  obtain ⟨t,⟨i,mem,hit⟩,cell⟩:=covered p _ misses
  refine ⟨i,hit,?_⟩
  intro q hq
  cases h : (B i).testBit q.val
  · rfl
  · have off:=blank t q _ ⟨i,mem,h⟩ cell
    have on:=(rel_mem e a b q).1 hq
    simp [off] at on

theorem noPhysical {B : Sides} (which : B=bank0 ∨ B=bank1) (e : P ≃ P) (n : Nat)
    (select : Fin n → Finset (Fin 17)) (right : Fin n → Finset P)
    (blank : ∀t p l, (∃i∈select t, (B i).testBit (p : P).val=true) →
        l∈right t → entry (e p) l=false)
    (covered : ∀p l, entry (e p) l=false →
        ∃t, (∃i∈select t, (B i).testBit p.val=true) ∧ l∈right t) : False := by
  have h:=physical e n select right blank covered
  rcases which with rfl|rfl
  · exact impossible0 _ h
  · exact impossible1 _ h

end PEqualNP.Outside.L_meta_10007_ForcedJoins

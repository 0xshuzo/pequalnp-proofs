import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18855.SharedPort

-- Coordinates 0 to 9 are the lexicographic edges of K5.
-- False and true select the four-vertex subgraphs omitting vertex 0 and vertex 1.
def edgeSet (t : Bool) : Finset (Fin 10) :=
  if t then {1,2,3,7,8,9} else {4,5,6,7,8,9}

def terms (t : Bool) : List Nat := if t then [514, 260, 136] else [528, 288, 192]
def factor (t : Bool) (a : Fin 1024) : Bool := (terms t).any fun m => (a.val &&& m) == m

def view (S : Finset (Fin 10)) (a : Fin 1024) (k : Fin 10) : Bool :=
  decide (k ∈ S) && a.val.testBit k.val

private def base0 : Fin 10 → Fin 10 → Nat :=
  ![![0,0,0,0,0,0,0,0,0,0],
    ![0,0,0,0,0,0,0,0,0,0],
    ![0,0,0,0,0,0,0,0,0,0],
    ![0,0,0,0,0,0,0,0,0,0],
    ![0,512,768,640,0,0,0,520,516,514],
    ![0,768,256,384,0,0,0,264,260,258],
    ![0,640,384,128,0,0,0,136,132,130],
    ![0,576,320,192,0,0,0,0,68,66],
    ![0,544,288,160,0,0,0,40,0,34],
    ![0,528,272,144,0,0,0,24,20,0]]

private def base1 : Fin 10 → Fin 10 → Nat :=
  ![![0,0,0,0,0,0,0,0,0,0],
    ![0,0,0,0,512,768,640,576,544,528],
    ![0,0,0,0,768,256,384,320,288,272],
    ![0,0,0,0,640,384,128,192,160,144],
    ![0,0,0,0,0,0,0,0,0,0],
    ![0,0,0,0,0,0,0,0,0,0],
    ![0,0,0,0,0,0,0,0,0,0],
    ![0,0,0,0,520,264,136,0,40,24],
    ![0,0,0,0,516,260,132,68,0,20],
    ![0,0,0,0,514,258,130,66,34,0]]


private def aRow (t : Bool) (i j : Fin 10) : Fin 1024 :=
  ⟨(if t then base1 i j else base0 i j) % 1024, Nat.mod_lt _ (by decide)⟩
private def changed (a : Fin 1024) (i : Fin 10) : Fin 1024 :=
  ⟨(a.val ^^^ (2 ^ i.val)) % 1024, Nat.mod_lt _ (by decide)⟩

private theorem flips : ∀ (t : Bool) (i j : Fin 10), i ∈ edgeSet t → j ∈ edgeSet (!t) → i ≠ j →
    let a := aRow t i j
    let b := changed a i
    let c := changed a j
    factor t a ≠ factor t b ∧ factor (!t) a = factor (!t) b ∧ factor (!t) a ≠ factor (!t) c ∧
    (∀ k : Fin 10, k ≠ i → a.val.testBit k.val = b.val.testBit k.val) ∧
    (∀ k : Fin 10, k ≠ j → a.val.testBit k.val = c.val.testBit k.val) := by decide +kernel

private theorem sameView {S : Finset (Fin 10)} {a b : Fin 1024} {i : Fin 10} (hi : i ∉ S)
    (h : ∀ k : Fin 10, k ≠ i → a.val.testBit k.val = b.val.testBit k.val) :
    view S a = view S b := by
  funext k
  by_cases e : k = i
  · subst k
    simp [view, hi]
  · simp only [view, h k e]

private theorem opposite {a b c : Bool} (ab : a ≠ b) (ac : a ≠ c) : b = c := by
  cases a <;> cases b <;> cases c <;> simp_all

private theorem missBoth (S T : Finset (Fin 10)) (hs : S.card ≤ 4) (ht : T.card ≤ 4) :
    ∃ i ∈ edgeSet false ∪ edgeSet true, i ∉ S ∧ i ∉ T := by
  classical
  by_contra h
  have sub : edgeSet false ∪ edgeSet true ⊆ S ∪ T := by
    intro i hi
    by_cases hS : i ∈ S
    · exact Finset.mem_union.mpr (Or.inl hS)
    · by_cases hT : i ∈ T
      · exact Finset.mem_union.mpr (Or.inr hT)
      · exact False.elim (h ⟨i,hi,hS,hT⟩)
  have bound := Finset.card_le_card sub
  have count := Finset.card_union_le S T
  have nine : (edgeSet false ∪ edgeSet true).card = 9 := by decide
  omega

private theorem missSecond (t : Bool) (T : Finset (Fin 10)) (i : Fin 10) (ht : T.card ≤ 4) :
    ∃ j ∈ edgeSet t, j ∉ T ∧ i ≠ j := by
  classical
  by_contra h
  have sub : edgeSet t ⊆ T ∪ {i} := by
    intro j hj
    by_cases hT : j ∈ T
    · exact Finset.mem_union.mpr (Or.inl hT)
    · by_cases e : i = j
      · subst j
        simp
      · exact False.elim (h ⟨j,hj,hT,e⟩)
  have bound := Finset.card_le_card sub
  have count : (T ∪ {i}).card ≤ T.card + 1 := by simpa using Finset.card_union_le T {i}
  have six : (edgeSet t).card = 6 := by cases t <;> decide
  omega

private theorem clash (t : Bool) (S T : Finset (Fin 10)) (i : Fin 10)
    (hi : i ∈ edgeSet t) (hs : i ∉ S) (ht : i ∉ T) (hsize : T.card ≤ 4)
    (wire : Fin 1024 → Bool)
    (da db : (Fin 10 → Bool) → Bool → Bool)
    (ha : ∀ a, da (view S a) (wire a) = factor t a)
    (hb : ∀ a, db (view T a) (wire a) = factor (!t) a) : False := by
  obtain ⟨j,hj,hT,hij⟩ := missSecond (!t) T i hsize
  let a := aRow t i j
  let b := changed a i
  let c := changed a j
  obtain ⟨fa,fb,fc,abi,acj⟩ := flips t i j hi hj hij
  have sab : view S a = view S b := sameView hs abi
  have tab : view T a = view T b := sameView ht abi
  have tac : view T a = view T c := sameView hT acj
  have w1 : wire a ≠ wire b := by
    intro e
    apply fa
    change factor t a = factor t b
    rw [← ha a, ← ha b, sab, e]
  have w2 : wire a ≠ wire c := by
    intro e
    apply fc
    change factor (!t) a = factor (!t) c
    rw [← hb a, ← hb c, tac, e]
  have bc : factor (!t) b = factor (!t) c := by
    rw [← hb b, ← hb c, ← tab, tac, opposite w1 w2]
  exact fc (Eq.trans fb bc)

-- The shared wire may be any function of the entire ten-bit input. The two
-- arbitrary decoders may each inspect any four of those ten raw inputs.
theorem twoCoefficientsCannotShareOneBit (S T : Finset (Fin 10)) (hs : S.card ≤ 4)
    (ht : T.card ≤ 4) (wire : Fin 1024 → Bool)
    (da db : (Fin 10 → Bool) → Bool → Bool) :
    ¬ ((∀ a, da (view S a) (wire a) = factor false a) ∧
       (∀ a, db (view T a) (wire a) = factor true a)) := by
  rintro ⟨ha,hb⟩
  obtain ⟨i,hi,hS,hT⟩ := missBoth S T hs ht
  rcases Finset.mem_union.mp hi with i0|i1
  · exact clash false S T i i0 hS hT ht wire da db ha hb
  · exact clash true T S i i1 hT hS hs wire db da hb ha

end PEqualNP.Outside.L_meta_18855.SharedPort

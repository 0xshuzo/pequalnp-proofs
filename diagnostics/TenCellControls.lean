import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

namespace PEqualNP.Outside.L_meta_21789.Controls

abbrev Cell := Fin 4 × Fin 6

def flags : Finset Cell := {(0,2), (0,4), (0,5), (1,2), (1,3), (2,1), (3,0)}

def flagged : Fin 7 → Cell := ![(0,2), (0,4), (0,5), (1,2), (1,3), (2,1), (3,0)]

def wanted (q : Cell) : Bool := (271156 : Nat).testBit (6*q.1.val+q.2.val)

def outcome (C : Circuit) (q : Cell) : Bool := C.eval (oneEach q.1 q.2)

def w0 : Circuit := ⟨[⟨.or, [8, 9]⟩, ⟨.and, [0, 10]⟩, ⟨.or, [6, 7]⟩, ⟨.and, [1, 12]⟩, ⟨.and, [2, 5]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [11, 13]⟩, ⟨.or, [16, 14]⟩, ⟨.or, [17, 15]⟩], 18⟩

theorem good0 : Monotone2 w0 ∧ w0.size ≤ 9 :=
  ⟨by simp [Monotone2, w0], by decide⟩

def w1 : Circuit := ⟨[⟨.or, [6, 9]⟩, ⟨.and, [0, 10]⟩, ⟨.or, [6, 7]⟩, ⟨.and, [1, 12]⟩, ⟨.and, [2, 5]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [11, 13]⟩, ⟨.or, [16, 14]⟩, ⟨.or, [17, 15]⟩], 18⟩

theorem good1 : Monotone2 w1 ∧ w1.size ≤ 9 :=
  ⟨by simp [Monotone2, w1], by decide⟩

def w2 : Circuit := ⟨[⟨.or, [6, 8]⟩, ⟨.and, [0, 10]⟩, ⟨.or, [6, 7]⟩, ⟨.and, [1, 12]⟩, ⟨.and, [2, 5]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [11, 13]⟩, ⟨.or, [16, 14]⟩, ⟨.or, [17, 15]⟩], 18⟩

theorem good2 : Monotone2 w2 ∧ w2.size ≤ 9 :=
  ⟨by simp [Monotone2, w2], by decide⟩

def w3 : Circuit := ⟨[⟨.or, [6, 8]⟩, ⟨.or, [10, 9]⟩, ⟨.and, [0, 11]⟩, ⟨.and, [1, 7]⟩, ⟨.and, [2, 5]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [12, 13]⟩, ⟨.or, [16, 14]⟩, ⟨.or, [17, 15]⟩], 18⟩

theorem good3 : Monotone2 w3 ∧ w3.size ≤ 9 :=
  ⟨by simp [Monotone2, w3], by decide⟩

def w4 : Circuit := ⟨[⟨.or, [6, 8]⟩, ⟨.or, [10, 9]⟩, ⟨.and, [0, 11]⟩, ⟨.and, [1, 6]⟩, ⟨.and, [2, 5]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [12, 13]⟩, ⟨.or, [16, 14]⟩, ⟨.or, [17, 15]⟩], 18⟩

theorem good4 : Monotone2 w4 ∧ w4.size ≤ 9 :=
  ⟨by simp [Monotone2, w4], by decide⟩

def w5 : Circuit := ⟨[⟨.or, [6, 8]⟩, ⟨.or, [10, 9]⟩, ⟨.and, [0, 11]⟩, ⟨.or, [6, 7]⟩, ⟨.and, [1, 13]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [12, 14]⟩, ⟨.or, [16, 15]⟩], 17⟩

theorem good5 : Monotone2 w5 ∧ w5.size ≤ 9 :=
  ⟨by simp [Monotone2, w5], by decide⟩

def w6 : Circuit := ⟨[⟨.or, [6, 8]⟩, ⟨.or, [10, 9]⟩, ⟨.and, [0, 11]⟩, ⟨.or, [6, 7]⟩, ⟨.and, [1, 13]⟩, ⟨.and, [2, 5]⟩, ⟨.or, [12, 14]⟩, ⟨.or, [16, 15]⟩], 17⟩

theorem good6 : Monotone2 w6 ∧ w6.size ≤ 9 :=
  ⟨by simp [Monotone2, w6], by decide⟩

def w7 : Circuit := ⟨[⟨.or, [6, 7]⟩, ⟨.and, [1, 10]⟩, ⟨.and, [2, 5]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [0, 11]⟩, ⟨.or, [14, 12]⟩, ⟨.or, [15, 13]⟩], 16⟩

theorem good7 : Monotone2 w7 ∧ w7.size ≤ 9 :=
  ⟨by simp [Monotone2, w7], by decide⟩

def w8 : Circuit := ⟨[⟨.or, [6, 8]⟩, ⟨.or, [10, 9]⟩, ⟨.and, [0, 11]⟩, ⟨.and, [2, 5]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [12, 1]⟩, ⟨.or, [15, 13]⟩, ⟨.or, [16, 14]⟩], 17⟩

theorem good8 : Monotone2 w8 ∧ w8.size ≤ 9 :=
  ⟨by simp [Monotone2, w8], by decide⟩

def w9 : Circuit := ⟨[⟨.or, [6, 8]⟩, ⟨.or, [10, 9]⟩, ⟨.and, [0, 11]⟩, ⟨.or, [6, 7]⟩, ⟨.and, [1, 13]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [12, 14]⟩, ⟨.or, [16, 2]⟩, ⟨.or, [17, 15]⟩], 18⟩

theorem good9 : Monotone2 w9 ∧ w9.size ≤ 9 :=
  ⟨by simp [Monotone2, w9], by decide⟩

def w10 : Circuit := ⟨[⟨.or, [6, 8]⟩, ⟨.or, [10, 9]⟩, ⟨.and, [0, 11]⟩, ⟨.or, [6, 7]⟩, ⟨.and, [1, 13]⟩, ⟨.and, [2, 5]⟩, ⟨.or, [12, 14]⟩, ⟨.or, [16, 15]⟩, ⟨.or, [17, 3]⟩], 18⟩

theorem good10 : Monotone2 w10 ∧ w10.size ≤ 9 :=
  ⟨by simp [Monotone2, w10], by decide⟩

def dropFlag : Fin 7 → Circuit := ![w0, w1, w2, w3, w4, w5, w6]

def fillRow : Fin 4 → Circuit := ![w7, w8, w9, w10]

theorem flagFit (i : Fin 7) : Monotone2 (dropFlag i) ∧ (dropFlag i).size ≤ 9 := by
  fin_cases i <;> first | exact good0 | exact good1 | exact good2 | exact good3 | exact good4 | exact good5 | exact good6

theorem rowFit (i : Fin 4) : Monotone2 (fillRow i) ∧ (fillRow i).size ≤ 9 := by
  fin_cases i <;> first | exact good7 | exact good8 | exact good9 | exact good10

theorem flagCount : flags.card = 7 := by decide +kernel
theorem enumerated : ∀ q ∈ flags, ∃ i : Fin 7, flagged i = q := by decide +kernel
theorem whenDrop : ∀ (i : Fin 7) (q : Cell), q ≠ flagged i → outcome (dropFlag i) q = wanted q := by decide +kernel
theorem whenFill : ∀ (i : Fin 4) (q : Cell), (q ∈ flags ∨ q.1 ≠ i) → outcome (fillRow i) q = wanted q := by decide +kernel

theorem smallSample (S : Finset Cell) (hs : S.card ≤ 10) :
    ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 9 ∧ ∀ q ∈ S, outcome C q = wanted q := by
  classical
  by_cases included : flags ⊆ S
  · have d : (S \ flags).card ≤ 3 := by
      rw [Finset.card_sdiff_of_subset included,flagCount]
      omega
    let rows := (S \ flags).image Prod.fst
    have few : rows.card ≤ 3 := (Finset.card_image_le).trans d
    have missing : ∃ i : Fin 4, i ∉ rows := by
      by_contra! allRows
      have h : (Finset.univ : Finset (Fin 4)) ⊆ rows := fun i _ => allRows i
      have hc := Finset.card_le_card h
      have total : (Finset.univ : Finset (Fin 4)).card = 4 := by decide
      omega
    obtain ⟨i,none⟩ := missing
    refine ⟨fillRow i,(rowFit i).1,(rowFit i).2,?_⟩
    intro q hq
    apply whenFill
    by_cases ht : q ∈ flags
    · exact Or.inl ht
    · right
      intro e
      apply none
      exact Finset.mem_image.mpr ⟨q, Finset.mem_sdiff.mpr ⟨hq,ht⟩, e⟩
  · obtain ⟨q,hq,nq⟩ := Finset.not_subset.mp included
    obtain ⟨i,hi⟩ := enumerated q hq
    refine ⟨dropFlag i,(flagFit i).1,(flagFit i).2,?_⟩
    intro r hr
    apply whenDrop
    intro e
    exact nq ((e.trans hi) ▸ hr)

end PEqualNP.Outside.L_meta_21789.Controls

open PEqualNP.Outside.L_meta_21789.Controls in
theorem PEqualNP.Outside.L_meta_21789 (S : Finset Cell) (hs : S.card ≤ 10) :
    ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 9 ∧ ∀ q ∈ S, outcome C q = wanted q :=
  smallSample S hs

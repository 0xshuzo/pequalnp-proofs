import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

namespace PEqualNP.Outside.L_meta_20532.NineProbe
def point (r : Fin 15) : Fin 3 × Fin 5 := (![(0,0), (0,1), (0,2), (0,3), (0,4), (1,0), (1,1), (1,2), (1,3), (1,4), (2,0), (2,1), (2,2), (2,3), (2,4)] : Fin 15 → Fin 3 × Fin 5) r
def control : Fin 10 → Circuit := ![
⟨[⟨.or, [1, 5]⟩, ⟨.or, [0, 6]⟩, ⟨.or, [7, 8]⟩, ⟨.and, [10, 9]⟩, ⟨.and, [5, 2]⟩, ⟨.or, [11, 12]⟩, ⟨.or, [3, 13]⟩, ⟨.or, [4, 14]⟩], 15⟩,
⟨[⟨.or, [6, 4]⟩, ⟨.and, [1, 8]⟩, ⟨.or, [7, 2]⟩, ⟨.or, [4, 5]⟩, ⟨.or, [9, 3]⟩, ⟨.or, [0, 11]⟩, ⟨.and, [13, 10]⟩, ⟨.or, [12, 14]⟩], 15⟩,
⟨[⟨.or, [6, 2]⟩, ⟨.or, [0, 4]⟩, ⟨.and, [9, 2]⟩, ⟨.or, [1, 10]⟩, ⟨.or, [9, 8]⟩, ⟨.or, [11, 5]⟩, ⟨.and, [13, 12]⟩, ⟨.or, [3, 14]⟩], 15⟩,
⟨[⟨.or, [1, 5]⟩, ⟨.or, [0, 6]⟩, ⟨.or, [7, 8]⟩, ⟨.and, [10, 9]⟩, ⟨.or, [11, 3]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [13, 2]⟩, ⟨.or, [12, 14]⟩], 15⟩,
⟨[⟨.or, [0, 4]⟩, ⟨.or, [3, 5]⟩, ⟨.or, [7, 2]⟩, ⟨.or, [4, 6]⟩, ⟨.and, [8, 10]⟩, ⟨.or, [12, 9]⟩, ⟨.and, [1, 11]⟩, ⟨.or, [14, 13]⟩], 15⟩,
⟨[⟨.or, [0, 2]⟩, ⟨.or, [1, 7]⟩, ⟨.and, [5, 8]⟩, ⟨.or, [9, 2]⟩, ⟨.or, [0, 4]⟩, ⟨.and, [12, 11]⟩, ⟨.or, [13, 10]⟩, ⟨.or, [3, 14]⟩], 15⟩,
⟨[⟨.or, [0, 6]⟩, ⟨.and, [0, 7]⟩, ⟨.or, [4, 8]⟩, ⟨.or, [9, 1]⟩, ⟨.or, [10, 2]⟩, ⟨.or, [11, 5]⟩, ⟨.and, [13, 12]⟩, ⟨.or, [3, 14]⟩], 15⟩,
⟨[⟨.or, [0, 4]⟩, ⟨.and, [8, 2]⟩, ⟨.or, [5, 9]⟩, ⟨.or, [1, 10]⟩, ⟨.or, [7, 11]⟩, ⟨.or, [8, 6]⟩, ⟨.and, [12, 13]⟩, ⟨.or, [3, 14]⟩], 15⟩,
⟨[⟨.or, [0, 6]⟩, ⟨.and, [8, 7]⟩, ⟨.or, [9, 1]⟩, ⟨.or, [8, 4]⟩, ⟨.or, [10, 5]⟩, ⟨.or, [3, 2]⟩, ⟨.and, [11, 12]⟩, ⟨.or, [14, 13]⟩], 15⟩,
⟨[⟨.or, [0, 4]⟩, ⟨.or, [1, 5]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [8, 6]⟩, ⟨.or, [9, 7]⟩, ⟨.and, [10, 2]⟩, ⟨.and, [11, 12]⟩, ⟨.or, [14, 13]⟩], 15⟩]
def errors : Fin 10 → Nat := ![2,4,16,64,128,256,2048,4096,24576,1057]
def value (C : Circuit) (r : Fin 15) := C.eval (oneEach (point r).1 (point r).2)
def target (r : Fin 15) := (7541 : Nat).testBit r.val
theorem legal : ∀ i : Fin 10, (control i).gates.all (fun g => (g.op == .or || g.op == .and) && decide (g.inputs.length ≤ 2)) = true := by decide +kernel
theorem fit (i : Fin 10) : Monotone2 (control i) := by
  intro g hg
  have h := List.all_eq_true.mp (legal i) g hg
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  rcases h with ⟨ho,hs⟩
  refine ⟨?_,hs⟩
  rcases ho with ho | ho <;> simp [ho]
theorem prices : ∀ i : Fin 10, (control i).size ≤ 8 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem disagreement : ∀ (i : Fin 10) (r : Fin 15),
    (errors i).testBit r.val = decide (value (control i) r ≠ target r) := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem separate : ∀ (i j : Fin 10) (r : Fin 15),
    (errors i).testBit r.val = true → (errors j).testBit r.val = true → i = j := by decide +kernel

theorem everyNine (S : Finset (Fin 15)) (hs : S.card ≤ 9) :
    ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 8 ∧ ∀ r ∈ S, value C r = target r := by
  classical
  by_contra none
  have failure (i : Fin 10) : ∃ r, r ∈ S ∧ value (control i) r ≠ target r := by
    by_contra! good
    exact none ⟨control i, fit i, prices i, good⟩
  choose r hr he using failure
  have bad (i : Fin 10) : (errors i).testBit (r i).val = true := by
    rw [disagreement]
    exact decide_eq_true (he i)
  have inj : Function.Injective r := by
    intro i j eq
    apply separate i j (r i) (bad i)
    rw [eq]
    exact bad j
  have contained : Finset.univ.image r ⊆ S := by
    intro x hx
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx
    exact hr i
  have count := Finset.card_le_card contained
  rw [Finset.card_image_of_injective _ inj, Finset.card_univ, Fintype.card_fin] at count
  omega

end PEqualNP.Outside.L_meta_20532.NineProbe

open PEqualNP.Outside.L_meta_20532.NineProbe in
theorem PEqualNP.Outside.L_meta_20532 (S : Finset (Fin 15)) (hs : S.card ≤ 9) :
  ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 8 ∧ ∀ r ∈ S, value C r = target r := everyNine S hs

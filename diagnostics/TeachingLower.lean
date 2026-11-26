import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_22817.Pack
def acceptedOp (g : Gate) : Bool :=
  match g.op with
  | .and | .or | .not => true
  | _ => false

theorem acceptedOpSound (g : Gate) (ok : acceptedOp g = true) :
    g.op = .and ∨ g.op = .or ∨ g.op = .not := by
  cases h : g.op <;> simp [acceptedOp, h] at ok ⊢

def point : Fin 21 → Fin 6 × Fin 6 := ![(0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, 2), (2, 3), (2, 4), (2, 5), (3, 3), (3, 4), (3, 5), (4, 4), (4, 5), (5, 5)]
def value (C : Circuit) (r : Fin 21) := C.eval (List.ofFn fun k : Fin 6 => decide (k = (point r).1 ∨ k = (point r).2))
def target (r : Fin 21) := (101311 : Nat).testBit (6*(point r).1.val+(point r).2.val)

theorem packing {k b : Nat} (control : Fin (k+1) → Circuit) (err : Fin (k+1) → Nat)
    (fit : ∀ i, FanInTwo (control i)) (cost : ∀ i, (control i).size ≤ b)
    (fail : ∀ i, ∃ r, value (control i) r ≠ target r)
    (readback : ∀ i (r : Fin 21), (err i).testBit r.val = decide (value (control i) r ≠ target r))
    (disj : ∀ i j (r : Fin 21), (err i).testBit r.val = true → (err j).testBit r.val = true → i = j)
    (S : Finset (Fin 21)) (hs : S.card ≤ k) : ∃ C : Circuit, FanInTwo C ∧ C.size ≤ b ∧
      (∃ r, value C r ≠ target r) ∧ ∀ r ∈ S, value C r = target r := by
  classical
  by_contra none
  have failure (i : Fin (k+1)) : ∃ r, r ∈ S ∧ value (control i) r ≠ target r := by
    by_contra! good
    exact none ⟨control i,fit i,cost i,fail i,good⟩
  choose r hr he using failure
  have bad (i : Fin (k+1)) : (err i).testBit (r i).val = true := by
    rw [readback]
    exact decide_eq_true (he i)
  have inj : Function.Injective r := by
    intro i j eq
    apply disj i j (r i) (bad i)
    rw [eq]
    exact bad j
  have contained : Finset.univ.image r ⊆ S := by
    intro x hx
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx
    exact hr i
  have count := Finset.card_le_card contained
  rw [Finset.card_image_of_injective _ inj, Finset.card_univ, Fintype.card_fin] at count
  omega
def controls5 : Fin 6 → Circuit := ![
⟨[⟨.or, [0, 1]⟩, ⟨.or, [3, 4]⟩, ⟨.and, [2, 7]⟩, ⟨.or, [6, 8]⟩], 9⟩,
⟨[⟨.or, [1, 4]⟩, ⟨.not, [4]⟩, ⟨.or, [2, 7]⟩, ⟨.and, [6, 8]⟩, ⟨.or, [0, 9]⟩], 10⟩,
⟨[⟨.and, [2, 3]⟩, ⟨.or, [0, 6]⟩, ⟨.not, [4]⟩, ⟨.and, [1, 8]⟩, ⟨.or, [9, 7]⟩], 10⟩,
⟨[⟨.or, [3, 4]⟩, ⟨.and, [6, 2]⟩, ⟨.or, [6, 2]⟩, ⟨.not, [8]⟩, ⟨.or, [9, 7]⟩], 10⟩,
⟨[⟨.or, [0, 3]⟩, ⟨.or, [1, 4]⟩, ⟨.and, [7, 2]⟩, ⟨.or, [6, 8]⟩], 9⟩,
⟨[⟨.or, [0, 2]⟩, ⟨.not, [4]⟩, ⟨.and, [1, 7]⟩, ⟨.or, [8, 6]⟩], 9⟩]
def errors5 : Fin 6 → Nat := ![512, 4096, 8192, 1048988, 230464, 18432]
theorem fits5 (i : Fin 6) : FanInTwo (controls5 i) := by
  have legal : ∀ j : Fin 6, (controls5 j).gates.all (fun g => acceptedOp g && decide (g.inputs.length ≤ 2)) = true := by decide +kernel
  intro g hg
  have passed := List.all_eq_true.mp (legal i) g hg
  simp only [Bool.and_eq_true, decide_eq_true_eq] at passed
  exact ⟨by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using acceptedOpSound g passed.1,
    passed.2⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem need5 (S : Finset (Fin 21)) (hs : S.card ≤ 5) : ∃ C : Circuit, FanInTwo C ∧ C.size ≤ 5 ∧
    (∃ r, value C r ≠ target r) ∧ ∀ r ∈ S, value C r = target r := by
  exact packing (k := 5) (controls5) (errors5) fits5 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) S hs
def controls6 : Fin 9 → Circuit := ![
⟨[⟨.or, [0, 1]⟩, ⟨.or, [3, 4]⟩, ⟨.and, [2, 7]⟩, ⟨.or, [6, 8]⟩], 9⟩,
⟨[⟨.or, [1, 4]⟩, ⟨.not, [4]⟩, ⟨.or, [2, 7]⟩, ⟨.and, [6, 8]⟩, ⟨.or, [0, 9]⟩], 10⟩,
⟨[⟨.and, [2, 3]⟩, ⟨.or, [0, 6]⟩, ⟨.not, [4]⟩, ⟨.and, [1, 8]⟩, ⟨.or, [9, 7]⟩], 10⟩,
⟨[⟨.or, [1, 0]⟩, ⟨.or, [3, 4]⟩, ⟨.and, [2, 7]⟩, ⟨.not, [4]⟩, ⟨.and, [9, 6]⟩, ⟨.or, [10, 8]⟩], 11⟩,
⟨[⟨.or, [4, 3]⟩, ⟨.and, [2, 6]⟩, ⟨.or, [0, 7]⟩, ⟨.not, [6]⟩, ⟨.and, [9, 1]⟩, ⟨.or, [10, 8]⟩], 11⟩,
⟨[⟨.not, [4]⟩, ⟨.and, [1, 6]⟩, ⟨.or, [0, 7]⟩, ⟨.not, [5]⟩, ⟨.and, [2, 9]⟩, ⟨.or, [8, 10]⟩], 11⟩,
⟨[⟨.or, [4, 3]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [2, 6]⟩, ⟨.or, [0, 8]⟩, ⟨.and, [7, 1]⟩, ⟨.or, [10, 9]⟩], 11⟩,
⟨[⟨.not, [4]⟩, ⟨.and, [1, 6]⟩, ⟨.or, [4, 3]⟩, ⟨.or, [2, 0]⟩, ⟨.and, [8, 9]⟩, ⟨.or, [7, 10]⟩], 11⟩,
⟨[⟨.or, [1, 4]⟩, ⟨.not, [4]⟩, ⟨.or, [2, 7]⟩, ⟨.or, [6, 3]⟩, ⟨.and, [8, 9]⟩, ⟨.or, [0, 10]⟩], 11⟩]
def errors6 : Fin 9 → Nat := ![512, 4096, 8192, 16, 256, 2048, 1088, 37, 163840]
theorem fits6 (i : Fin 9) : FanInTwo (controls6 i) := by
  have legal : ∀ j : Fin 9, (controls6 j).gates.all (fun g => acceptedOp g && decide (g.inputs.length ≤ 2)) = true := by decide +kernel
  intro g hg
  have passed := List.all_eq_true.mp (legal i) g hg
  simp only [Bool.and_eq_true, decide_eq_true_eq] at passed
  exact ⟨by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using acceptedOpSound g passed.1,
    passed.2⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem need6 (S : Finset (Fin 21)) (hs : S.card ≤ 8) : ∃ C : Circuit, FanInTwo C ∧ C.size ≤ 6 ∧
    (∃ r, value C r ≠ target r) ∧ ∀ r ∈ S, value C r = target r := by
  exact packing (k := 8) (controls6) (errors6) fits6 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) S hs
end PEqualNP.Outside.L_meta_22817.Pack

open PEqualNP.Outside.L_meta_22817.Pack in
theorem PEqualNP.Outside.L_meta_22817 (S : Finset (Fin 21)) :
  (S.card ≤ 5 → ∃ C : Circuit, FanInTwo C ∧ C.size ≤ 5 ∧ (∃ r, value C r ≠ target r) ∧ ∀ r ∈ S, value C r = target r) ∧
  (S.card ≤ 8 → ∃ C : Circuit, FanInTwo C ∧ C.size ≤ 6 ∧ (∃ r, value C r ≠ target r) ∧ ∀ r ∈ S, value C r = target r) := ⟨need5 S,need6 S⟩

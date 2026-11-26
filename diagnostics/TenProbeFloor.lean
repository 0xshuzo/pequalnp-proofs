import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_23615.TenRows

def points : Fin 21 → Fin 6 × Fin 6 := ![(0,0), (0,1), (0,2), (0,3), (0,4), (0,5), (1,1), (1,2), (1,3), (1,4), (1,5), (2,2), (2,3), (2,4), (2,5), (3,3), (3,4), (3,5), (4,4), (4,5), (5,5)]
def control : Fin 11 → Circuit := ![
  ⟨[⟨.and, [2, 3]⟩, ⟨.or, [5, 3]⟩, ⟨.or, [5, 4]⟩, ⟨.not, [7]⟩, ⟨.and, [0, 8]⟩, ⟨.or, [10, 6]⟩, ⟨.and, [1, 9]⟩, ⟨.or, [12, 11]⟩], 13⟩,
  ⟨[⟨.or, [0, 5]⟩, ⟨.or, [6, 3]⟩, ⟨.or, [1, 3]⟩, ⟨.not, [7]⟩, ⟨.and, [0, 5]⟩, ⟨.or, [9, 2]⟩, ⟨.and, [11, 8]⟩, ⟨.or, [10, 12]⟩], 13⟩,
  ⟨[⟨.or, [5, 3]⟩, ⟨.or, [1, 3]⟩, ⟨.and, [0, 4]⟩, ⟨.or, [0, 6]⟩, ⟨.not, [9]⟩, ⟨.or, [10, 2]⟩, ⟨.and, [11, 7]⟩, ⟨.or, [8, 12]⟩], 13⟩,
  ⟨[⟨.or, [1, 3]⟩, ⟨.or, [5, 4]⟩, ⟨.and, [0, 7]⟩, ⟨.and, [1, 4]⟩, ⟨.and, [2, 6]⟩, ⟨.or, [9, 10]⟩, ⟨.or, [8, 11]⟩], 12⟩,
  ⟨[⟨.and, [2, 3]⟩, ⟨.or, [5, 4]⟩, ⟨.and, [0, 7]⟩, ⟨.or, [0, 5]⟩, ⟨.not, [9]⟩, ⟨.or, [8, 6]⟩, ⟨.and, [1, 10]⟩, ⟨.or, [12, 11]⟩], 13⟩,
  ⟨[⟨.or, [0, 3]⟩, ⟨.or, [1, 3]⟩, ⟨.not, [6]⟩, ⟨.or, [8, 2]⟩, ⟨.and, [9, 7]⟩, ⟨.or, [5, 4]⟩, ⟨.and, [0, 11]⟩, ⟨.or, [12, 10]⟩], 13⟩,
  ⟨[⟨.or, [0, 5]⟩, ⟨.or, [5, 4]⟩, ⟨.and, [0, 7]⟩, ⟨.or, [6, 3]⟩, ⟨.not, [9]⟩, ⟨.and, [1, 10]⟩, ⟨.or, [8, 11]⟩], 12⟩,
  ⟨[⟨.or, [4, 5]⟩, ⟨.or, [4, 3]⟩, ⟨.and, [1, 7]⟩, ⟨.or, [0, 8]⟩, ⟨.or, [9, 6]⟩, ⟨.and, [9, 6]⟩, ⟨.not, [10]⟩, ⟨.or, [11, 12]⟩], 13⟩,
  ⟨[⟨.or, [0, 2]⟩, ⟨.or, [5, 3]⟩, ⟨.or, [4, 7]⟩, ⟨.or, [0, 7]⟩, ⟨.not, [9]⟩, ⟨.and, [8, 6]⟩, ⟨.and, [1, 10]⟩, ⟨.or, [12, 11]⟩], 13⟩,
  ⟨[⟨.or, [5, 2]⟩, ⟨.or, [0, 3]⟩, ⟨.or, [6, 4]⟩, ⟨.or, [5, 7]⟩, ⟨.and, [7, 8]⟩, ⟨.not, [9]⟩, ⟨.and, [1, 11]⟩, ⟨.or, [12, 10]⟩], 13⟩,
  ⟨[⟨.or, [5, 3]⟩, ⟨.or, [0, 6]⟩, ⟨.or, [1, 3]⟩, ⟨.and, [7, 8]⟩, ⟨.and, [8, 2]⟩, ⟨.or, [9, 2]⟩, ⟨.not, [11]⟩, ⟨.or, [12, 10]⟩], 13⟩]
def errors : Fin 11 → Nat := ![2, 16, 32, 64, 256, 1024, 4096, 34816, 24584, 196612, 1835009]

def value (C : Circuit) (r : Fin 21) : Bool :=
  let p := points r
  C.eval (List.ofFn fun k : Fin 6 => decide (k = p.1 ∨ k = p.2))

def target (r : Fin 21) : Bool :=
  let p := points r
  (34224 : Nat).testBit (6 * min p.1.val p.2.val + max p.1.val p.2.val)

def acceptedOp (g : Gate) : Bool :=
  match g.op with
  | .and | .or | .not => true
  | _ => false

theorem acceptedOpSound (g : Gate) (ok : acceptedOp g = true) :
    g.op = .and ∨ g.op = .or ∨ g.op = .not := by
  cases h : g.op <;> simp [acceptedOp, h] at ok ⊢


theorem legal : ∀ i : Fin 11,
    (control i).gates.all (fun g => acceptedOp g && decide (g.inputs.length ≤ 2)) = true := by
  decide +kernel

theorem fit (i : Fin 11) : FanInTwo (control i) := by
  intro g hg
  have p := List.all_eq_true.mp (legal i) g hg
  simp only [Bool.and_eq_true, decide_eq_true_eq] at p
  exact ⟨by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using acceptedOpSound g p.1,p.2⟩

theorem prices : ∀ i : Fin 11, (control i).size ≤ 8 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem disagreement : ∀ (i : Fin 11) (r : Fin 21),
    (errors i).testBit r.val = decide (value (control i) r ≠ target r) := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem separate : ∀ (i j : Fin 11) (r : Fin 21),
    (errors i).testBit r.val = true → (errors j).testBit r.val = true → i = j := by decide +kernel

theorem everyTen (S : Finset (Fin 21)) (hs : S.card ≤ 10) :
    ∃ C : Circuit, FanInTwo C ∧ C.size ≤ 8 ∧ ∀ r ∈ S, value C r = target r := by
  classical
  by_contra none
  have failure (i : Fin 11) : ∃ r, r ∈ S ∧ value (control i) r ≠ target r := by
    by_contra! good
    exact none ⟨control i, fit i, prices i, good⟩
  choose r hr he using failure
  have bad (i : Fin 11) : (errors i).testBit (r i).val = true := by
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

end PEqualNP.Outside.L_meta_23615.TenRows

open PEqualNP.Outside.L_meta_23615.TenRows in
theorem PEqualNP.Outside.L_meta_23615 (S : Finset (Fin 21)) (hs : S.card ≤ 10) :
    ∃ C : Circuit, FanInTwo C ∧ C.size ≤ 8 ∧ ∀ r ∈ S, value C r = target r :=
  everyTen S hs

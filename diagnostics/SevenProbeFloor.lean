import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_24236.ProbeFloor

def pairTable : Fin 21 → Fin 6 × Fin 6 := ![(0,0), (0,1), (0,2), (0,3), (0,4), (0,5), (1,1), (1,2), (1,3), (1,4), (1,5), (2,2), (2,3), (2,4), (2,5), (3,3), (3,4), (3,5), (4,4), (4,5), (5,5)]

def critical : Finset (Fin 21) := {4, 9, 14, 17, 18, 19, 20}

def criticalRow : Fin 7 → Fin 21 := ![4, 9, 14, 17, 18, 19, 20]

def control : Fin 8 → Circuit := ![
  ⟨[⟨.and, [1, 4]⟩, ⟨.or, [6, 5]⟩, ⟨.or, [2, 3]⟩, ⟨.or, [8, 4]⟩, ⟨.and, [9, 7]⟩, ⟨.not, [10]⟩], 11⟩,
  ⟨[⟨.and, [0, 4]⟩, ⟨.or, [6, 5]⟩, ⟨.or, [2, 3]⟩, ⟨.or, [8, 4]⟩, ⟨.and, [9, 7]⟩, ⟨.not, [10]⟩], 11⟩,
  ⟨[⟨.or, [0, 1]⟩, ⟨.and, [6, 4]⟩, ⟨.or, [7, 5]⟩, ⟨.or, [3, 4]⟩, ⟨.and, [9, 8]⟩, ⟨.not, [10]⟩], 11⟩,
  ⟨[⟨.or, [0, 1]⟩, ⟨.and, [6, 4]⟩, ⟨.or, [7, 5]⟩, ⟨.or, [2, 4]⟩, ⟨.and, [9, 8]⟩, ⟨.not, [10]⟩], 11⟩,
  ⟨[⟨.or, [2, 3]⟩, ⟨.not, [6]⟩, ⟨.or, [6, 4]⟩, ⟨.or, [7, 5]⟩, ⟨.and, [8, 9]⟩, ⟨.not, [10]⟩], 11⟩,
  ⟨[⟨.or, [0, 1]⟩, ⟨.and, [6, 4]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [8, 5]⟩, ⟨.or, [7, 9]⟩, ⟨.not, [10]⟩], 11⟩,
  ⟨[⟨.or, [0, 1]⟩, ⟨.not, [6]⟩, ⟨.or, [6, 5]⟩, ⟨.or, [4, 7]⟩, ⟨.and, [8, 9]⟩, ⟨.not, [10]⟩], 11⟩,
  ⟨[⟨.or, [0, 1]⟩, ⟨.or, [6, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.and, [4, 5]⟩, ⟨.or, [8, 9]⟩, ⟨.not, [10]⟩], 11⟩]

def rowValue (C : Circuit) (r : Fin 21) : Bool :=
  let p := pairTable r
  C.eval (List.ofFn fun k : Fin 6 => decide (k = p.1 ∨ k = p.2))

def target (r : Fin 21) : Bool :=
  let p := pairTable r
  (34634582959 : Nat).testBit (6 * min p.1.val p.2.val + max p.1.val p.2.val)

def acceptedOp (g : Gate) : Bool :=
  match g.op with
  | .and | .or | .not => true
  | _ => false

theorem acceptedOpSound (g : Gate) (h : acceptedOp g = true) :
    g.op = .and ∨ g.op = .or ∨ g.op = .not := by
  cases e : g.op <;> simp [acceptedOp,e] at h ⊢

theorem legal : ∀ i : Fin 8,
    (control i).gates.all (fun g => acceptedOp g && decide (g.inputs.length ≤ 2)) = true := by
  decide +kernel

theorem fit (i : Fin 8) : FanInTwo (control i) := by
  intro g hg
  have p := List.all_eq_true.mp (legal i) g hg
  simp only [Bool.and_eq_true, decide_eq_true_eq] at p
  exact ⟨by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using acceptedOpSound g p.1,p.2⟩

theorem costs : ∀ i : Fin 8, (control i).size ≤ 6 := by decide +kernel

theorem criticalCover : ∀ r ∈ critical, ∃ i : Fin 7, criticalRow i = r := by decide +kernel
theorem criticalCount : critical.card = 7 := by decide +kernel
theorem central : ∀ r ∈ critical, rowValue (control 7) r = target r := by decide +kernel

theorem omitted : ∀ (i : Fin 7) (r : Fin 21), criticalRow i ≠ r →
    rowValue (control i.castSucc) r = target r := by decide +kernel

theorem everySeven (S : Finset (Fin 21)) (hs : S.card ≤ 7) :
    ∃ C : Circuit, FanInTwo C ∧ C.size ≤ 6 ∧ ∀ r ∈ S, rowValue C r = target r := by
  classical
  by_cases h : critical ⊆ S
  · have heq := Finset.eq_of_subset_of_card_le h (show S.card ≤ critical.card by simpa only [criticalCount] using hs)
    exact ⟨control 7, fit 7, costs 7, heq ▸ central⟩
  · obtain ⟨q,hq,hnot⟩ := Finset.not_subset.mp h
    obtain ⟨i,hi⟩ := criticalCover q hq
    refine ⟨control i.castSucc, fit _, costs _, ?_⟩
    intro r hr
    apply omitted i r
    intro e
    have eq : q = r := hi.symm.trans e
    exact hnot (eq.symm ▸ hr)

end PEqualNP.Outside.L_meta_24236.ProbeFloor

open PEqualNP.Outside.L_meta_24236.ProbeFloor in
theorem PEqualNP.Outside.L_meta_24236 (S : Finset (Fin 21)) (hs : S.card ≤ 7) :
    ∃ C : Circuit, FanInTwo C ∧ C.size ≤ 6 ∧ ∀ r ∈ S, rowValue C r = target r :=
  everySeven S hs

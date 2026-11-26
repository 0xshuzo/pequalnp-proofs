import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23616.SampleBank
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def sample : Fin 21 → Fin 6 × Fin 6 := ![(0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, 2), (2, 3), (2, 4), (2, 5), (3, 3), (3, 4), (3, 5), (4, 4), (4, 5), (5, 5)]
def needed : Finset (Fin 21) := [0, 2, 3, 5, 6, 7, 8, 10, 12, 18].toFinset
def bank : Fin 13 → Circuit := ![⟨[⟨.or, [1,3]⟩, ⟨.or, [3,5]⟩, ⟨.or, [4,5]⟩, ⟨.and, [0,8]⟩, ⟨.not, [7]⟩, ⟨.or, [2,10]⟩, ⟨.and, [6,11]⟩, ⟨.or, [9,12]⟩], 13⟩,
⟨[⟨.not, [0]⟩, ⟨.not, [1]⟩, ⟨.and, [2,3]⟩, ⟨.or, [5,7]⟩, ⟨.and, [9,6]⟩, ⟨.or, [3,10]⟩, ⟨.not, [11]⟩, ⟨.or, [12,8]⟩], 13⟩,
⟨[⟨.or, [0,2]⟩, ⟨.not, [2]⟩, ⟨.or, [3,5]⟩, ⟨.or, [3,7]⟩, ⟨.and, [6,9]⟩, ⟨.not, [8]⟩, ⟨.and, [1,11]⟩, ⟨.or, [12,10]⟩], 13⟩,
⟨[⟨.or, [0,1]⟩, ⟨.or, [1,3]⟩, ⟨.or, [2,3]⟩, ⟨.and, [2,7]⟩, ⟨.or, [8,5]⟩, ⟨.not, [10]⟩, ⟨.and, [6,11]⟩, ⟨.or, [12,9]⟩], 13⟩,
⟨[⟨.or, [1,3]⟩, ⟨.or, [2,3]⟩, ⟨.and, [2,6]⟩, ⟨.and, [6,4]⟩, ⟨.or, [0,9]⟩, ⟨.not, [7]⟩, ⟨.and, [10,11]⟩, ⟨.or, [12,8]⟩], 13⟩,
⟨[⟨.or, [0,1]⟩, ⟨.and, [1,5]⟩, ⟨.or, [7,2]⟩, ⟨.and, [8,3]⟩, ⟨.or, [8,3]⟩, ⟨.not, [10]⟩, ⟨.and, [6,11]⟩, ⟨.or, [12,9]⟩], 13⟩,
⟨[⟨.and, [2,3]⟩, ⟨.or, [1,6]⟩, ⟨.or, [2,3]⟩, ⟨.not, [8]⟩, ⟨.and, [0,9]⟩, ⟨.not, [5]⟩, ⟨.and, [7,11]⟩, ⟨.or, [10,12]⟩], 13⟩,
⟨[⟨.not, [0]⟩, ⟨.not, [1]⟩, ⟨.and, [2,3]⟩, ⟨.or, [2,6]⟩, ⟨.and, [7,9]⟩, ⟨.or, [3,10]⟩, ⟨.not, [11]⟩, ⟨.or, [12,8]⟩], 13⟩,
⟨[⟨.not, [0]⟩, ⟨.not, [1]⟩, ⟨.or, [2,6]⟩, ⟨.or, [5,7]⟩, ⟨.and, [9,8]⟩, ⟨.or, [3,10]⟩, ⟨.not, [11]⟩], 12⟩,
⟨[⟨.not, [0]⟩, ⟨.or, [1,3]⟩, ⟨.or, [2,3]⟩, ⟨.and, [2,7]⟩, ⟨.and, [5,6]⟩, ⟨.or, [8,10]⟩, ⟨.not, [11]⟩, ⟨.or, [12,9]⟩], 13⟩,
⟨[⟨.and, [5,1]⟩, ⟨.or, [6,3]⟩, ⟨.or, [1,7]⟩, ⟨.or, [2,4]⟩, ⟨.or, [7,9]⟩, ⟨.and, [8,9]⟩, ⟨.not, [10]⟩, ⟨.or, [12,11]⟩], 13⟩,
⟨[⟨.not, [0]⟩, ⟨.or, [5,4]⟩, ⟨.or, [2,3]⟩, ⟨.and, [2,6]⟩, ⟨.and, [7,6]⟩, ⟨.or, [8,10]⟩, ⟨.not, [11]⟩, ⟨.or, [12,9]⟩], 13⟩,
⟨[⟨.and, [5,1]⟩, ⟨.or, [6,2]⟩, ⟨.or, [1,3]⟩, ⟨.and, [2,8]⟩, ⟨.or, [7,3]⟩, ⟨.or, [10,4]⟩, ⟨.not, [11]⟩, ⟨.or, [12,9]⟩], 13⟩]
def missing : Fin 21 → Fin 13 := ![0, 0, 1, 2, 0, 3, 4, 5, 6, 0, 7, 0, 8, 0, 0, 0, 0, 0, 9, 0, 0]
def extra : Fin 21 → Fin 13 := ![10, 10, 10, 10, 11, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 11, 10, 10, 10, 11]
def acceptedOp (g : Gate) : Bool :=
  match g.op with
  | .and | .or | .not => true
  | _ => false

theorem acceptedOpSound (g : Gate) (ok : acceptedOp g = true) :
    g.op = .and ∨ g.op = .or ∨ g.op = .not := by
  cases h : g.op <;> simp [acceptedOp, h] at ok ⊢


def Check (C : Circuit) (k : Fin 21) : Prop :=
  let p := sample k
  C.eval (List.ofFn fun a : Fin 6 => decide (a=p.1 ∨ a=p.2)) =
    (34227 : ℕ).testBit (6 * min p.1.val p.2.val + max p.1.val p.2.val)

instance (C : Circuit) (k : Fin 21) : Decidable (Check C k) := by unfold Check; infer_instance

set_option maxRecDepth 10000 in
theorem fan (c) : FanInTwo (bank c) := by
  have pass : ∀ k, (bank k).gates.all (fun g => acceptedOp g && decide (g.inputs.length ≤ 2)) = true := by decide +kernel
  intro g hg
  have h := List.all_eq_true.mp (pass c) g hg
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨by simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using acceptedOpSound g h.1,h.2⟩

theorem price : ∀ c, (bank c).size ≤ 8 := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
theorem whenMissing : ∀ i k : Fin 21, i ∈ needed → k ≠ i → Check (bank (missing i)) k := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
theorem withExtra : ∀ i k : Fin 21, k ∈ needed ∨ k=i → Check (bank (extra i)) k := by decide +kernel

theorem everyEleven (S : Finset (Fin 21)) (small : S.card ≤ 11) :
    ∃ C : Circuit, FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i ∈ S, Check C i := by
  classical
  by_cases absent : ∃ k, k∈needed ∧ k∉S
  · obtain ⟨k,hk,hno⟩ := absent
    exact ⟨bank (missing k),fan _,price _,fun i hi => whenMissing k i hk (by rintro rfl; exact hno hi)⟩
  have contained : needed ⊆ S := by
    intro x hx
    by_contra no
    exact absent ⟨x,hx,no⟩
  have ten : needed.card=10 := by decide +kernel
  have bound : (S \ needed).card ≤ 1 := by rw [Finset.card_sdiff_of_subset contained,ten]; omega
  by_cases rem : (S \ needed).Nonempty
  · obtain ⟨x,hx⟩ := rem
    refine ⟨bank (extra x),fan _,price _,?_⟩
    intro i hi
    apply withExtra
    by_cases h : i∈needed
    · exact Or.inl h
    · exact Or.inr (Finset.card_le_one.mp bound i (Finset.mem_sdiff.mpr ⟨hi,h⟩) x hx)
  · refine ⟨bank (extra 0),fan _,price _,?_⟩
    intro i hi
    apply withExtra
    left
    by_contra no
    exact rem ⟨i,Finset.mem_sdiff.mpr ⟨hi,no⟩⟩

end PEqualNP.Outside.L_meta_23616.SampleBank

open PEqualNP.Outside.L_meta_23616.SampleBank in
theorem PEqualNP.Outside.L_meta_23616 (S : Finset (Fin 21)) (small : S.card ≤ 11) :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i ∈ S, Check C i := everyEleven S small

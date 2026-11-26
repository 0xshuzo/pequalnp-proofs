import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24645.SmallSamples
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def sample : Fin 21 → Fin 6 × Fin 6 := ![(0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, 2), (2, 3), (2, 4), (2, 5), (3, 3), (3, 4), (3, 5), (4, 4), (4, 5), (5, 5)]
def bank : Fin 11 → Circuit := ![⟨[⟨.or, [1,2]⟩, ⟨.and, [2,3]⟩, ⟨.or, [7,4]⟩, ⟨.not, [6]⟩, ⟨.and, [6,8]⟩, ⟨.and, [5,9]⟩, ⟨.or, [10,11]⟩, ⟨.not, [12]⟩], 13⟩,
⟨[⟨.or, [1,2]⟩, ⟨.or, [0,6]⟩, ⟨.or, [6,5]⟩, ⟨.not, [7]⟩, ⟨.or, [3,4]⟩, ⟨.or, [10,9]⟩, ⟨.and, [8,11]⟩, ⟨.not, [12]⟩], 13⟩,
⟨[⟨.or, [0,1]⟩, ⟨.or, [6,2]⟩, ⟨.or, [2,5]⟩, ⟨.not, [7]⟩, ⟨.or, [3,4]⟩, ⟨.or, [10,9]⟩, ⟨.and, [8,11]⟩, ⟨.not, [12]⟩], 13⟩,
⟨[⟨.not, [0]⟩, ⟨.or, [1,2]⟩, ⟨.not, [7]⟩, ⟨.and, [7,4]⟩, ⟨.and, [5,8]⟩, ⟨.or, [9,10]⟩, ⟨.and, [11,6]⟩, ⟨.not, [12]⟩], 13⟩,
⟨[⟨.not, [1]⟩, ⟨.or, [2,5]⟩, ⟨.and, [3,7]⟩, ⟨.or, [8,4]⟩, ⟨.not, [7]⟩, ⟨.and, [10,6]⟩, ⟨.not, [9]⟩, ⟨.or, [12,11]⟩], 13⟩,
⟨[⟨.or, [1,2]⟩, ⟨.or, [2,4]⟩, ⟨.and, [6,7]⟩, ⟨.or, [8,5]⟩, ⟨.and, [6,5]⟩, ⟨.or, [0,10]⟩, ⟨.not, [9]⟩, ⟨.or, [11,12]⟩], 13⟩,
⟨[⟨.or, [0,4]⟩, ⟨.or, [1,2]⟩, ⟨.and, [2,3]⟩, ⟨.or, [8,4]⟩, ⟨.or, [7,6]⟩, ⟨.and, [7,9]⟩, ⟨.not, [11]⟩, ⟨.and, [10,12]⟩], 13⟩,
⟨[⟨.or, [1,2]⟩, ⟨.and, [2,3]⟩, ⟨.or, [7,4]⟩, ⟨.not, [6]⟩, ⟨.and, [5,9]⟩, ⟨.or, [8,10]⟩, ⟨.not, [11]⟩, ⟨.or, [0,12]⟩], 13⟩,
⟨[⟨.or, [0,2]⟩, ⟨.and, [1,4]⟩, ⟨.or, [7,2]⟩, ⟨.not, [6]⟩, ⟨.or, [8,5]⟩, ⟨.or, [3,9]⟩, ⟨.and, [10,11]⟩, ⟨.not, [12]⟩], 13⟩,
⟨[⟨.or, [1,2]⟩, ⟨.and, [2,3]⟩, ⟨.or, [7,4]⟩, ⟨.and, [6,8]⟩, ⟨.or, [9,5]⟩, ⟨.not, [10]⟩, ⟨.or, [0,11]⟩], 12⟩,
⟨[⟨.or, [0,1]⟩, ⟨.and, [1,4]⟩, ⟨.not, [7]⟩, ⟨.and, [2,3]⟩, ⟨.or, [9,5]⟩, ⟨.not, [10]⟩, ⟨.or, [6,11]⟩, ⟨.and, [12,8]⟩], 13⟩]
def errors : Fin 11 → Finset (Fin 21) := ![{5}, {8}, {9}, {12}, {20}, {7, 11}, {15, 19}, {16, 18}, {10, 13}, {10, 14}, {13, 14}]

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
    (274877375 : ℕ).testBit (6 * min p.1.val p.2.val + max p.1.val p.2.val)

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
theorem works : ∀ c k, k ∉ errors c → Check (bank c) k := by decide +kernel

theorem smallSamples (S : Finset (Fin 21)) (hS : S.card ≤ 9) :
    ∃ C : Circuit, FanInTwo C ∧ C.size ≤ 8 ∧ ∀ k ∈ S, Check C k := by
  classical
  by_contra hn
  have meet (c : Fin 11) : ∃ k ∈ S, k ∈ errors c := by
    by_contra! avoid
    exact hn ⟨bank c, fan c, price c, fun k hk => works c k (avoid k hk)⟩
  have h0 : (5 : Fin 21) ∈ S := by
    obtain ⟨k, h, e⟩ := meet 0
    have eq : errors 0 = {5} := by decide +kernel
    rw [eq, Finset.mem_singleton] at e
    simpa only [e] using h
  have h1 : (8 : Fin 21) ∈ S := by
    obtain ⟨k, h, e⟩ := meet 1
    have eq : errors 1 = {8} := by decide +kernel
    rw [eq, Finset.mem_singleton] at e
    simpa only [e] using h
  have h2 : (9 : Fin 21) ∈ S := by
    obtain ⟨k, h, e⟩ := meet 2
    have eq : errors 2 = {9} := by decide +kernel
    rw [eq, Finset.mem_singleton] at e
    simpa only [e] using h
  have h3 : (12 : Fin 21) ∈ S := by
    obtain ⟨k, h, e⟩ := meet 3
    have eq : errors 3 = {12} := by decide +kernel
    rw [eq, Finset.mem_singleton] at e
    simpa only [e] using h
  have h4 : (20 : Fin 21) ∈ S := by
    obtain ⟨k, h, e⟩ := meet 4
    have eq : errors 4 = {20} := by decide +kernel
    rw [eq, Finset.mem_singleton] at e
    simpa only [e] using h
  have h5 : (7 : Fin 21) ∈ S ∨ (11 : Fin 21) ∈ S := by
    obtain ⟨k, h, e⟩ := meet 5
    have eq : errors 5 = {7, 11} := by decide +kernel
    simp only [eq, Finset.mem_insert, Finset.mem_singleton] at e
    rcases e with rfl | rfl
    · exact Or.inl h
    · exact Or.inr h
  have h6 : (15 : Fin 21) ∈ S ∨ (19 : Fin 21) ∈ S := by
    obtain ⟨k, h, e⟩ := meet 6
    have eq : errors 6 = {15, 19} := by decide +kernel
    simp only [eq, Finset.mem_insert, Finset.mem_singleton] at e
    rcases e with rfl | rfl
    · exact Or.inl h
    · exact Or.inr h
  have h7 : (16 : Fin 21) ∈ S ∨ (18 : Fin 21) ∈ S := by
    obtain ⟨k, h, e⟩ := meet 7
    have eq : errors 7 = {16, 18} := by decide +kernel
    simp only [eq, Finset.mem_insert, Finset.mem_singleton] at e
    rcases e with rfl | rfl
    · exact Or.inl h
    · exact Or.inr h
  have h8 : (10 : Fin 21) ∈ S ∨ (13 : Fin 21) ∈ S := by
    obtain ⟨k, h, e⟩ := meet 8
    have eq : errors 8 = {10, 13} := by decide +kernel
    simp only [eq, Finset.mem_insert, Finset.mem_singleton] at e
    rcases e with rfl | rfl
    · exact Or.inl h
    · exact Or.inr h
  have h9 : (10 : Fin 21) ∈ S ∨ (14 : Fin 21) ∈ S := by
    obtain ⟨k, h, e⟩ := meet 9
    have eq : errors 9 = {10, 14} := by decide +kernel
    simp only [eq, Finset.mem_insert, Finset.mem_singleton] at e
    rcases e with rfl | rfl
    · exact Or.inl h
    · exact Or.inr h
  have h10 : (13 : Fin 21) ∈ S ∨ (14 : Fin 21) ∈ S := by
    obtain ⟨k, h, e⟩ := meet 10
    have eq : errors 10 = {13, 14} := by decide +kernel
    simp only [eq, Finset.mem_insert, Finset.mem_singleton] at e
    rcases e with rfl | rfl
    · exact Or.inl h
    · exact Or.inr h
  have triangle : ((10 : Fin 21) ∈ S ∧ (13 : Fin 21) ∈ S) ∨
      ((10 : Fin 21) ∈ S ∧ (14 : Fin 21) ∈ S) ∨ ((13 : Fin 21) ∈ S ∧ (14 : Fin 21) ∈ S) := by
    rcases h8 with a | a <;> rcases h9 with b | b <;> rcases h10 with c | c <;> tauto
  have large (x y z a b : Fin 21) (hx : x ∈ S) (hy : y ∈ S) (hz : z ∈ S)
      (ha : a ∈ S) (hb : b ∈ S)
      (distinct : 10 ≤ ({5, 8, 9, 12, 20, x, y, z, a, b} : Finset (Fin 21)).card) : False := by
    have sub : ({5, 8, 9, 12, 20, x, y, z, a, b} : Finset (Fin 21)) ⊆ S := by
      intro v hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
    have hcard := le_trans distinct (Finset.card_le_card sub)
    omega
  rcases h5 with hx | hx <;> rcases h6 with hy | hy <;> rcases h7 with hz | hz <;>
    rcases triangle with ⟨ha,hb⟩ | ⟨ha,hb⟩ | ⟨ha,hb⟩ <;>
    exact large _ _ _ _ _ hx hy hz ha hb (by decide +kernel)

end PEqualNP.Outside.L_meta_24645.SmallSamples

open PEqualNP.Outside.L_meta_24645.SmallSamples in
theorem PEqualNP.Outside.L_meta_24645 (S : Finset (Fin 21)) (hS : S.card ≤ 9) :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ k ∈ S, Check C k := smallSamples S hS

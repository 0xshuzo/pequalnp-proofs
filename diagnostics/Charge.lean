import Mathlib
namespace Charge9836
abbrev V := Fin 40
abbrev Edge := V × V
def allEdges : Finset Edge := ([(0, 24), (0, 26), (0, 36), (0, 39), (1, 25), (1, 27), (1, 37), (2, 21), (2, 26), (2, 28), (2, 38), (3, 21), (3, 22), (3, 27), (3, 29), (3, 39), (4, 22), (4, 23), (4, 28), (4, 30), (5, 23), (5, 24), (5, 29), (5, 31), (6, 21), (6, 24), (6, 25), (6, 30), (6, 32), (7, 22), (7, 25), (7, 26), (7, 31), (7, 33), (8, 23), (8, 26), (8, 27), (8, 32), (8, 34), (9, 24), (9, 27), (9, 28), (9, 33), (9, 35), (10, 25), (10, 28), (10, 29), (10, 34), (10, 36), (11, 26), (11, 29), (11, 30), (11, 35), (11, 37), (12, 27), (12, 30), (12, 31), (12, 36), (12, 38), (13, 28), (13, 31), (13, 32), (13, 37), (13, 39), (14, 29), (14, 32), (14, 33), (14, 38), (15, 30), (15, 33), (15, 34), (15, 39), (16, 21), (16, 31), (16, 34), (16, 35), (17, 22), (17, 32), (17, 35), (17, 36), (18, 21), (18, 23), (18, 33), (18, 36), (18, 37), (19, 22), (19, 24), (19, 34), (19, 37), (19, 38), (20, 23), (20, 25), (20, 35), (20, 38), (20, 39)] : List Edge).toFinset
def star (v : V) := allEdges.filter (fun e => e.1=v ∨ e.2=v)
def touched (S : Finset V) := S.biUnion star
def remain (S : Finset V) := allEdges \ touched S

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem data : allEdges.card=95 ∧ ∀ v, (star v).card≤5 := by decide +kernel

theorem forest_deletions (S : Finset V)
    (forest : S.card < 40 → (remain S).card+1 ≤ 40-S.card) : 14 ≤ S.card := by
  by_contra! ht
  have sub : touched S ⊆ allEdges := by
    intro e he
    obtain ⟨v,_,hv⟩ := Finset.mem_biUnion.mp he
    exact (Finset.mem_filter.mp hv).1
  have eq : (remain S).card + (touched S).card = allEdges.card :=
    Finset.card_sdiff_add_card_eq_card sub
  have bound : (touched S).card ≤ 5*S.card := by
    calc
      _ ≤ ∑ v ∈ S, (star v).card := Finset.card_biUnion_le
      _ ≤ ∑ _v ∈ S, 5 := Finset.sum_le_sum (fun v _ => data.2 v)
      _ = 5*S.card := by simp [Nat.mul_comm]
  have hf := forest (by omega)
  have he := data.1
  omega

def choice : Finset V := {23,24,25,26,28,30,31,32,33,34,35,36,37,38}
def depth (v : V) : Nat := if v=3 then 0 else if 21≤v.val then 1 else 2
def arc (u v : V) := ((u,v)∈ (remain choice) ∨ (v,u)∈ (remain choice))
instance (u v : V) : Decidable (arc u v) := by unfold arc; infer_instance
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem attaining : choice.card=14 ∧ (remain choice).card=25 ∧
    (∀ e ∈ remain choice, depth e.1 ≠ depth e.2) ∧
    (∀ v : V, v∉choice → v≠3 → ∃! w : V, arc v w ∧ depth w < depth v) := by decide +kernel
end Charge9836

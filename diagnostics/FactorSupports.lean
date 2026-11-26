import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7263.Research

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev Vertex := Fin 10
abbrev Assignment := Vertex → Bool

def pet (x : Assignment) : Bool :=
  (List.finRange 5).any fun i =>
    x (Fin.castAdd 5 i) && x (Fin.castAdd 5 (i+1)) ||
    x (Fin.castAdd 5 i) && x (Fin.natAdd 5 i) ||
    x (Fin.natAdd 5 i) && x (Fin.natAdd 5 (i+2))

def edge (i j : Vertex) : Bool :=
  (([50,69,138,276,521,385,770,548,104,208] : List Nat).getD i.val 0).testBit j.val

def one (i : Vertex) : Assignment := fun j => decide (j=i)
def two (i j : Vertex) : Assignment := fun k => decide (k=i ∨ k=j)

set_option maxRecDepth 10000 in
theorem graph_geometry :
    (∀ i j, pet (two i j) = edge i j) ∧
    (∀ i, pet (one i) = false) ∧
    (∀ i j, (List.ofFn (two i j)).count true ≤ 2) ∧
    (∀ i j, edge i j = false → ∃ t, edge i t = true ∧ edge j t = true) ∧
    (∀ a b c d : Vertex, a ≠ b → c ≠ d → edge a c = true → edge a d = true →
      edge b c = true → edge b d = true → False) := by decide +kernel

def promise (P : Assignment → Bool) : Prop :=
  ∀ x, pet x = false ∨ (List.ofFn x).count true ≤ 2 → P x = pet x

/-- Positive sensitivity from the singleton at a neighbor to the corresponding
    edge. Both rows are fixed by the promise. -/
def senses (A : Assignment → Bool) (i : Vertex) : Prop :=
  ∃ t : Vertex, edge i t = true ∧ A (one t) = false ∧ A (two i t) = true

lemma exceptions (R : Vertex → Prop) :
    (∃ i : Vertex, ∀ j, j ≠ i → R j) ∨
    ∃ i j : Vertex, i ≠ j ∧ ¬R i ∧ ¬R j := by
  classical
  by_cases all : ∀ i, R i
  · exact Or.inl ⟨0,fun j _ => all j⟩
  push_neg at all
  obtain ⟨i, hi⟩ := all
  by_cases rest : ∀ j, j ≠ i → R j
  · exact Or.inl ⟨i,rest⟩
  push_neg at rest
  obtain ⟨j,hj,missing⟩ := rest
  exact Or.inr ⟨i,j,Ne.symm hj,hi,missing⟩

/-- The exceptional vertex sets for the two factors span a complete
    bipartite subgraph of Petersen. Consequently one factor is positively
    sensitive on at least nine of the ten variables. -/
theorem factor_sensitivity (A B : Assignment → Bool) (agree : promise (fun x => A x && B x)) :
    (∀ i j, ¬senses A i → ¬senses B j → edge i j = true) ∧
    ((∃ i : Vertex, ∀ j, j ≠ i → senses A j) ∨ (∃ i : Vertex, ∀ j, j ≠ i → senses B j)) := by
  obtain ⟨pairVal, singleVal, pairSize, common, noSquare⟩ := graph_geometry
  have pairOn (i t : Vertex) (it : edge i t = true) :
      A (two i t) = true ∧ B (two i t) = true := by
    apply Bool.and_eq_true.mp
    exact (agree _ (Or.inr (pairSize i t))).trans ((pairVal i t).trans it)
  have cross (i j : Vertex) (hi : ¬senses A i) (hj : ¬senses B j) : edge i j = true := by
    cases h : edge i j with
    | true => rfl
    | false =>
      obtain ⟨t,it,jt⟩ := common i j h
      have atOne : A (one t) = true := by
        cases z : A (one t) with
        | true => rfl
        | false => exact (hi ⟨t,it,z,(pairOn i t it).1⟩).elim
      have btOne : B (one t) = true := by
        cases z : B (one t) with
        | true => rfl
        | false => exact (hj ⟨t,jt,z,(pairOn j t jt).2⟩).elim
      have impossible := (agree (one t) (Or.inl (singleVal t))).trans (singleVal t)
      change (A (one t) && B (one t)) = false at impossible
      simp [atOne,btOne] at impossible
  refine ⟨cross,?_⟩
  rcases exceptions (senses A) with hit | ⟨a,b,ab,ha,hb⟩
  · exact Or.inl hit
  rcases exceptions (senses B) with hit | ⟨c,d,cd,hc,hd⟩
  · exact Or.inr hit
  exact (noSquare a b c d ab cd (cross a c ha hc) (cross a d ha hd)
    (cross b c hb hc) (cross b d hb hd)).elim

end PEqualNP.Outside.L_meta_7263.Research

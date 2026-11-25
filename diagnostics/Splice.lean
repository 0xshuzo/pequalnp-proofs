import PEqualNP.Defs
namespace PCX150
open PEqualNP.ProofComplexity
abbrev V := Fin 4 × Fin 3
abbrev Cl := Clause V
inductive ResTree (F : Set Cl) : Cl → Nat → Prop where
  | ax {C : Cl} : C ∈ F → ResTree F C 0
  | res {C D R : Cl} {i j : Nat} : ResTree F C i → ResTree F D j →
      IsResolvent C D R → ResTree F R (i+j+1)
end PCX150

namespace PCX150
open PEqualNP.ProofComplexity

/-- A leaf records a physical source, so two copies of an equal clause can use different labels. -/
inductive LabeledTree (clause : Nat → Cl) : Cl → Type where
  | leaf (id : Nat) : LabeledTree clause (clause id)
  | resolve {C D R : Cl} (left : LabeledTree clause C) (right : LabeledTree clause D)
      (rule : IsResolvent C D R) : LabeledTree clause R

namespace LabeledTree

def cost {f R} : LabeledTree f R → Nat
  | .leaf _ => 0
  | .resolve l r _ => l.cost + r.cost + 1

def leaves {f R} : LabeledTree f R → List Nat
  | .leaf i => [i]
  | .resolve l r _ => l.leaves ++ r.leaves

theorem leafCount {f R} (t : LabeledTree f R) : t.leaves.length = t.cost+1 := by
  induction t with
  | leaf _ => rfl
  | resolve _ _ _ ih jh =>
    simp only [leaves,List.length_append,cost]
    omega

theorem toResTree {f R} (t : LabeledTree f R) {F : Set Cl}
    (available : ∀ i ∈ t.leaves, f i ∈ F) : ResTree F R t.cost := by
  induction t with
  | leaf i => exact .ax (available i (by simp [leaves]))
  | resolve l r rule ih jh =>
    exact .res (ih (fun x hx => available x (by simp [leaves,hx])))
      (jh (fun x hx => available x (by simp [leaves,hx]))) rule

/-- Substitute exactly the designated physical line. Other equal clauses are kept as leaves. -/
def splice {f R} (t : LabeledTree f R) (i : Nat) (proof : LabeledTree f (f i)) :
    LabeledTree f R :=
  match t with
  | .leaf k => if h : i = k then h ▸ proof else .leaf k
  | .resolve l r rule => .resolve (l.splice i proof) (r.splice i proof) rule

theorem spliceCost {f R} (t : LabeledTree f R) (i : Nat) (proof : LabeledTree f (f i)) :
    (t.splice i proof).cost = t.cost + t.leaves.count i * proof.cost := by
  induction t with
  | leaf k =>
    by_cases eq : i = k
    · subst k
      simp [splice,cost,leaves]
    · simp [splice,cost,leaves,eq,Ne.symm eq]
  | resolve l r rule ih jh =>
    simp only [splice,cost,leaves,List.count_append,ih,jh,Nat.add_mul]
    omega

theorem spliceLeaves {f R} (t : LabeledTree f R) (i : Nat) (proof : LabeledTree f (f i)) :
    ∀ k ∈ (t.splice i proof).leaves,
      (k ≠ i ∧ k ∈ t.leaves) ∨ k ∈ proof.leaves := by
  induction t with
  | leaf j =>
    by_cases h : i = j
    · subst j
      simp [splice]
    · simp [splice,leaves,h,Ne.symm h]
  | resolve l r _ ih jh =>
    simp only [splice,leaves,List.mem_append]
    intro k hk
    rcases hk with left | right
    · rcases ih k left with ⟨ne,mem⟩ | mem
      · exact Or.inl ⟨ne,Or.inl mem⟩
      · exact Or.inr mem
    · rcases jh k right with ⟨ne,mem⟩ | mem
      · exact Or.inl ⟨ne,Or.inr mem⟩
      · exact Or.inr mem

end LabeledTree
end PCX150

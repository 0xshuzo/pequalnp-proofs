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
      intro k hk
      exact Or.inr (by simpa [splice] using hk)
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

namespace PCX150
open PEqualNP.ProofComplexity

def portList (pair : Option (Nat × Nat)) : List Nat :=
  match pair with
  | none => []
  | some (j,k) => [j,k]

inductive Fragment (f : Nat → Cl) (parent : Nat → Option (Nat × Nat))
    (boundary : Nat → Bool) : Nat → Bool → Type where
  | leaf (i : Nat) (force : Bool) (reason : parent i = none ∨ force = false ∧ boundary i = true) :
      Fragment f parent boundary i force
  | node (i j k : Nat) (force : Bool) (openAt : force = true ∨ boundary i = false)
      (edge : parent i = some (j,k)) (step : IsResolvent (f j) (f k) (f i))
      (left : Fragment f parent boundary j false) (right : Fragment f parent boundary k false) :
      Fragment f parent boundary i force

namespace Fragment

def expanded {f p b i t} : Fragment f p b i t → List Nat
  | .leaf _ _ _ => []
  | .node u _ _ _ _ _ _ l r => u :: l.expanded ++ r.expanded

def tree {f p b i t} : Fragment f p b i t → LabeledTree f (f i)
  | .leaf u _ _ => .leaf u
  | .node _ _ _ _ _ _ rule l r => .resolve l.tree r.tree rule

theorem costCount {f p b i t} (g : Fragment f p b i t) : g.tree.cost = g.expanded.length := by
  induction g with
  | leaf => rfl
  | node _ _ _ _ _ _ _ _ _ ih jh =>
    simp only [tree,LabeledTree.cost,expanded,List.length_append,List.length_cons,ih,jh]
    omega

/-- Every occurrence other than the root came through exactly one parent slot.
    A physical line may appear more than once in either list. -/
theorem occurrenceBalance {f p b i t} (g : Fragment f p b i t) (v : Nat) :
    g.expanded.count v + g.tree.leaves.count v =
      [i].count v + (g.expanded.flatMap (fun u => portList (p u))).count v := by
  induction g with
  | leaf => simp [expanded,tree,LabeledTree.leaves]
  | node i j k force op edge rule l r ih jh =>
    simp only [tree,LabeledTree.leaves,expanded,List.count_append,List.flatMap_append,
      List.flatMap_cons,edge,portList,List.count_cons,List.count_nil,Nat.zero_add,
      List.cons_append] at ih jh ⊢
    omega

end Fragment

theorem canExpand {f : Nat → Cl} {p : Nat → Option (Nat × Nat)} {bound : Nat}
    (rules : ∀ i j k, p i = some (j,k) → i < j ∧ i < k ∧ j < bound ∧ k < bound ∧
      IsResolvent (f j) (f k) (f i)) (b : Nat → Bool) (i : Nat) (force : Bool) :
    Nonempty (Fragment f p b i force) := by
  have aux (m : Nat) : ∀ i, bound-i = m → ∀ t, Nonempty (Fragment f p b i t) := by
    induction m using Nat.strong_induction_on with
    | ind m ih =>
      intro u eq t
      by_cases cut : t = false ∧ b u = true
      · exact ⟨.leaf u t (Or.inr cut)⟩
      · cases hp : p u with
        | none => exact ⟨.leaf u t (Or.inl hp)⟩
        | some pair =>
          obtain ⟨j,k⟩ := pair
          obtain ⟨hj,hk,bj,bk,step⟩ := rules u j k hp
          obtain ⟨l⟩ := ih (bound-j) (by omega) j rfl false
          obtain ⟨r⟩ := ih (bound-k) (by omega) k rfl false
          have op : t = true ∨ b u = false := by cases t <;> cases hb : b u <;> simp_all
          exact ⟨.node u j k t op hp step l r⟩
  exact aux _ i rfl force

end PCX150

namespace PCX150.Fragment

theorem leafReason {f p b i t} (g : Fragment f p b i t) :
    ∀ v ∈ g.tree.leaves, p v = none ∨ b v = true := by
  induction g with
  | leaf u force reason =>
    intro v hv
    have hv' : v = u := by simpa [tree,LabeledTree.leaves] using hv
    subst v
    exact reason.imp_right And.right
  | node _ _ _ _ _ _ _ l r ih jh =>
    intro v hv
    rcases List.mem_append.mp hv with a | a
    · exact ih v a
    · exact jh v a

theorem boundaryExpansion {f p b i t} (g : Fragment f p b i t) (v : Nat) (cut : b v = true) :
    g.expanded.count v = if t = true ∧ i = v ∧ p i ≠ none then 1 else 0 := by
  induction g with
  | leaf u force reason =>
    rcases reason with raw | ⟨nf,_⟩
    · simp [expanded,raw]
    · simp [expanded,nf]
  | node u j k force op edge rule l r ih jh =>
    by_cases eq : u = v
    · subst u
      have forced : force = true := op.resolve_right (by simp [cut])
      simp [expanded,ih,jh,forced,edge]
    · simp [expanded,ih,jh,eq,Ne.symm eq]

theorem openedDerived {f p b i t} (g : Fragment f p b i t) :
    ∀ v ∈ g.expanded, p v ≠ none := by
  induction g with
  | leaf => simp [expanded]
  | node u j k force op edge rule l r ih jh =>
    intro v hv
    simp only [expanded,List.cons_append,List.mem_cons,List.mem_append] at hv
    rcases hv with rfl | hl | hr
    · simp [edge]
    · exact ih v hl
    · exact jh v hr

end PCX150.Fragment

namespace PCX150
open PEqualNP.ProofComplexity

abbrev Rooted (f : Nat → Cl) (p : Nat → Option (Nat × Nat)) (b : Nat → Bool) :=
  (i : Nat) × Fragment f p b i true

namespace Rooted
variable {f : Nat → Cl} {p : Nat → Option (Nat × Nat)} {b : Nat → Bool}

def nodes (fs : List (Rooted f p b)) := fs.flatMap (fun z => z.2.expanded)
def tips (fs : List (Rooted f p b)) := fs.flatMap (fun z => z.2.tree.leaves)
def starts (fs : List (Rooted f p b)) := fs.map (fun z => z.1)

theorem balance (fs : List (Rooted f p b)) (v : Nat) :
    (nodes fs).count v + (tips fs).count v =
      (starts fs).count v + ((nodes fs).flatMap (fun k => portList (p k))).count v := by
  induction fs with
  | nil => rfl
  | cons g gs ih =>
    obtain ⟨i,g⟩ := g
    have h := g.occurrenceBalance v
    simp only [nodes,tips,starts,List.flatMap_cons,List.map_cons,List.count_append,
      List.flatMap_append,List.count_cons,List.count_nil,Nat.zero_add] at ih h ⊢
    omega

theorem cutRoots (fs : List (Rooted f p b)) (v : Nat) (cut : b v = true)
    (proper : ∀ g ∈ fs, p g.1 ≠ none) : (nodes fs).count v = (starts fs).count v := by
  induction fs with
  | nil => rfl
  | cons g gs ih =>
    obtain ⟨i,g⟩ := g
    have h := g.boundaryExpansion v cut
    have d := proper ⟨i,g⟩ (by simp)
    have t := ih (fun z hz => proper z (by simp [hz]))
    by_cases eq : i = v
    · subst i
      simp [nodes,starts,d,List.count_append] at h t ⊢
      omega
    · simp [nodes,starts,d,eq,Ne.symm eq,List.count_append] at h t ⊢
      omega

theorem noncutNotTip (fs : List (Rooted f p b)) {v : Nat} (derived : p v ≠ none)
    (uncut : b v = false) : (tips fs).count v = 0 := by
  apply List.count_eq_zero.mpr
  intro hv
  obtain ⟨g,_,hg⟩ := List.mem_flatMap.mp hv
  rcases g.2.leafReason v hg with empty | cut <;> simp_all

theorem physicalDerived (fs : List (Rooted f p b)) {v : Nat} (hv : v ∈ nodes fs) : p v ≠ none := by
  obtain ⟨g,_,hg⟩ := List.mem_flatMap.mp hv
  exact g.2.openedDerived v hg

end Rooted
end PCX150


namespace PCX150

/-- A unique incoming slot is preserved when a list of line indices is replaced by
    its expanded occurrences, provided the unique reader has been expanded once. -/
theorem countParentsSingle (lines : List Nat) (ports : Nat → List Nat) (v u : Nat)
    (sole : ∀ x ∈ lines, (ports x).count v = if x = u then 1 else 0) :
    (lines.flatMap ports).count v = lines.count u := by
  induction lines with
  | nil => rfl
  | cons x xs ih =>
    have h := sole x (by simp)
    have tail := ih (fun y hy => sole y (by simp [hy]))
    by_cases eq : x = u
    · subst x
      simp_all [List.flatMap_cons,List.count_append,Nat.add_comm]
    · simp [List.flatMap_cons,List.count_append,h,tail,eq,Ne.symm eq]

theorem countParentsZero (lines : List Nat) (ports : Nat → List Nat) (v : Nat)
    (none : ∀ x ∈ lines, v ∉ ports x) : (lines.flatMap ports).count v = 0 := by
  induction lines with
  | nil => rfl
  | cons x xs ih =>
    have h := none x (by simp)
    have tail := ih (fun y hy => none y (by simp [hy]))
    simp [List.flatMap_cons,List.count_append,tail,List.count_eq_zero.mpr h]

/-- Conservation over the forest of fragments. The roots list has one copy of
    each cut line and the conclusion. A non-cut derived line ends no fragment. -/
theorem oneExpansionPerLine (nodes tips roots : List Nat) (ports : Nat → List Nat)
    (derived : Nat → Prop) (balance : ∀ v, nodes.count v + tips.count v =
      roots.count v + (nodes.flatMap ports).count v)
    (casesFor : ∀ v, derived v →
      nodes.count v = 1 ∨
      (tips.count v = 0 ∧ roots.count v = 0 ∧ ∃ u, u < v ∧ derived u ∧
        ∀ x ∈ nodes, (ports x).count v = if x = u then 1 else 0)) :
    ∀ v, derived v → nodes.count v = 1 := by
  intro v
  induction v using Nat.strong_induction_on with
  | ind v ih =>
    intro hv
    rcases casesFor v hv with done | ⟨tip,seed,u,lt,hu,sole⟩
    · exact done
    · have incoming := countParentsSingle nodes ports v u sole
      have earlier := ih u lt hu
      have h := balance v
      omega

end PCX150

namespace PCX150

private theorem occursAtMost {xs ys : List Nat} (h : ∀ x, xs.count x ≤ ys.count x) :
    xs.length ≤ ys.length := by
  induction xs generalizing ys with
  | nil => simp
  | cons a xs ih =>
    have positive := h a
    have mem : a ∈ ys := by
      by_contra bad
      have zero := List.count_eq_zero.mpr bad
      simp [zero] at positive
    have tail : ∀ x, xs.count x ≤ (ys.erase a).count x := by
      intro x
      have old := h x
      by_cases eq : x = a
      · subst x
        simp at old
        rw [List.count_erase_self]
        omega
      · simpa [List.count_erase_of_ne,eq,Ne.symm eq] using old
    have len := ih tail
    rw [List.length_erase_of_mem mem] at len
    have pos := List.length_pos_of_mem mem
    simp only [List.length_cons]
    omega

namespace Rooted
variable {f : Nat → Cl} {p : Nat → Option (Nat×Nat)} {b : Nat → Bool}

/-- If every uncut live internal node has exactly one incoming slot, expansion
    partitions the physical rules without charging any physical line twice. -/
theorem partitionCost (fs : List (Rooted f p b)) (physical : List Nat)
    (unique : physical.Nodup) (present : ∀ v, p v ≠ none → v ∈ physical)
    (rootsDerived : ∀ z ∈ fs, p z.1 ≠ none)
    (cut : ∀ v, p v ≠ none → b v = true → (starts fs).count v = 1)
    (single : ∀ v, p v ≠ none → b v = false → (starts fs).count v = 0 ∧
      ∃ u, u < v ∧ p u ≠ none ∧
        ∀ x ∈ nodes fs, (portList (p x)).count v = if x = u then 1 else 0) :
    (nodes fs).length = physical.length ↔ ∀ v ∈ physical, p v ≠ none := by
  have once : ∀ v, p v ≠ none → (nodes fs).count v = 1 := by
    apply oneExpansionPerLine (nodes fs) (tips fs) (starts fs) (fun x => portList (p x))
      (fun v => p v ≠ none) (balance fs)
    intro v hv
    cases hb : b v with
    | true => exact Or.inl ((cutRoots fs v hb rootsDerived).trans (cut v hv hb))
    | false =>
      obtain ⟨zero,u,lt,d,only⟩ := single v hv hb
      exact Or.inr ⟨noncutNotTip fs hv hb,zero,u,lt,d,only⟩
  have charge : ∀ v, (nodes fs).count v ≤ physical.count v := by
    intro v
    by_cases mem : v ∈ nodes fs
    · have hd := physicalDerived fs mem
      rw [once v hd]
      exact List.count_pos_iff.mpr (present v hd)
    · simp [List.count_eq_zero.mpr mem]
  constructor
  · intro eq v hv
    by_contra bad
    have absent : v ∉ nodes fs := fun h => physicalDerived fs h bad
    have charge' : ∀ x, (nodes fs).count x ≤ (physical.erase v).count x := by
      intro x
      by_cases same : x = v
      · subst x
        simp [List.count_eq_zero.mpr absent]
      · simpa [List.count_erase_of_ne,same,Ne.symm same] using charge x
    have h := occursAtMost charge'
    rw [List.length_erase_of_mem hv] at h
    have pos := List.length_pos_of_mem hv
    omega
  · intro proper
    apply Nat.le_antisymm (occursAtMost charge)
    apply occursAtMost
    intro v
    by_cases mem : v ∈ physical
    · rw [once v (proper v mem)]
      exact List.nodup_iff_count_le_one.mp unique v
    · simp [List.count_eq_zero.mpr mem]

end Rooted
end PCX150

namespace PCX150.Rooted

variable {f : Nat → Cl} {p : Nat → Option (Nat × Nat)} {b : Nat → Bool}

/-- Expand one fragment per selected root, preserving their physical labels and order. -/
noncomputable def chooseForest {bound : Nat}
    (rules : ∀ i j k, p i = some (j,k) → i < j ∧ i < k ∧ j < bound ∧ k < bound ∧
      PEqualNP.ProofComplexity.IsResolvent (f j) (f k) (f i))
    (b : Nat → Bool) (xs : List Nat) : List (Rooted f p b) :=
  xs.map (fun i => ⟨i,Classical.choice (canExpand rules b i true)⟩)

theorem chooseStarts {bound : Nat}
    (rules : ∀ i j k, p i = some (j,k) → i < j ∧ i < k ∧ j < bound ∧ k < bound ∧
      PEqualNP.ProofComplexity.IsResolvent (f j) (f k) (f i))
    (b : Nat → Bool) (xs : List Nat) : starts (chooseForest rules b xs) = xs := by
  simp [starts,chooseForest,List.map_map,Function.comp_def]

/-- A non-root with unit indegree is expanded once, no matter how the fragments
    were selected by the kernel's existential unrolling lemma. -/
theorem ownership (fs : List (Rooted f p b)) (physical : List Nat)
    (unique : physical.Nodup) (proper : ∀ v, v ∈ physical ↔ p v ≠ none)
    (allRoots : ∀ z ∈ fs, p z.1 ≠ none)
    (cuts : ∀ v, p v ≠ none → b v = true → (starts fs).count v = 1)
    (single : ∀ v, p v ≠ none → b v = false → (starts fs).count v = 0 ∧
      ∃ u, u<v ∧ p u ≠ none ∧ ∀ x, (portList (p x)).count v = if x = u then 1 else 0) :
    ∀ v, (nodes fs).count v = physical.count v := by
  have once : ∀ v, p v ≠ none → (nodes fs).count v = 1 := by
    apply oneExpansionPerLine (nodes fs) (tips fs) (starts fs) (fun x => portList (p x))
      (fun v => p v ≠ none) (balance fs)
    intro v hd
    cases hb : b v with
    | true => exact Or.inl ((cutRoots fs v hb allRoots).trans (cuts v hd hb))
    | false =>
      obtain ⟨zero,u,lt,hu,only⟩ := single v hd hb
      exact Or.inr ⟨noncutNotTip fs hd hb,zero,u,lt,hu,fun x _ => only x⟩
  intro v
  by_cases hd : p v ≠ none
  · have low := List.count_pos_iff.mpr ((proper v).2 hd)
    have high := List.nodup_iff_count_le_one.mp unique v
    have one := once v hd
    omega
  · have no : v ∉ nodes fs := fun h => hd (physicalDerived fs h)
    have other : v ∉ physical := fun h => hd ((proper v).1 h)
    simp [List.count_eq_zero.mpr no,List.count_eq_zero.mpr other]

end PCX150.Rooted

namespace PCX150.Rooted

variable {f : Nat → Cl} {p : Nat → Option (Nat × Nat)} {b : Nat → Bool}

/-- Identical multiplicities let us count each parent slot directly in the physical list. -/
theorem countPhysical (fs : List (Rooted f p b)) (physical : List Nat)
    (same : ∀ v, (nodes fs).count v = physical.count v) (v : Nat) :
    ((nodes fs).flatMap (fun k => portList (p k))).count v =
      (physical.flatMap (fun k => portList (p k))).count v := by
  have perm : (nodes fs).Perm physical := List.perm_iff_count.mpr same
  have out : ((nodes fs).flatMap (fun k => portList (p k))).Perm
      (physical.flatMap (fun k => portList (p k))) := perm.flatMap (fun _ _ => .refl _)
  exact (List.perm_iff_count.mp out) v

/-- For every marked derived line there is exactly one forced opening.
    The remaining occurrences on the frontier are exactly all physical reads. -/
theorem cutReads (fs : List (Rooted f p b)) (physical : List Nat)
    (same : ∀ v, (nodes fs).count v = physical.count v)
    (rootsDerived : ∀ z ∈ fs, p z.1 ≠ none) {v : Nat} (cut : b v = true) :
    (tips fs).count v = (physical.flatMap (fun k => portList (p k))).count v := by
  have bal := balance fs v
  have atRoot := cutRoots fs v cut rootsDerived
  have charge := countPhysical fs physical same v
  omega

end PCX150.Rooted

namespace PCX150.Rooted
open PEqualNP.ProofComplexity
variable {f : Nat → Cl} {p : Nat → Option (Nat × Nat)} {N : Nat}

/-- Build the partition at every selected shared rule and at the empty conclusion. -/
theorem markedFamily
    (rules : ∀ i j k, p i = some (j,k) → i < j ∧ i < k ∧ j < N ∧ k < N ∧
      IsResolvent (f j) (f k) (f i))
    (physical roots : List Nat) (unique : physical.Nodup) (distinct : roots.Nodup)
    (proper : ∀ v, v ∈ physical ↔ p v ≠ none)
    (relevant : ∀ v ∈ roots, p v ≠ none)
    (read : ∀ v, p v ≠ none → v ∉ roots → ∃ u, u < v ∧ p u ≠ none ∧
      ∀ x, (portList (p x)).count v = if x=u then 1 else 0) :
    ∃ fs : List (Rooted f p (fun k => decide (k ∈ roots))),
      starts fs = roots ∧ (nodes fs).length = physical.length ∧
      (∀ v, (nodes fs).count v = physical.count v) ∧
      ∀ v ∈ roots, (tips fs).count v =
        (physical.flatMap (fun k => portList (p k))).count v := by
  let b := fun k : Nat => decide (k ∈ roots)
  let fs := chooseForest rules b roots
  have start : starts fs = roots := chooseStarts rules b roots
  have allRoots : ∀ z ∈ fs, p z.1 ≠ none := by
    intro z hz
    apply relevant
    rw [←start]
    exact List.mem_map.mpr ⟨z,hz,rfl⟩
  have one (v) (mem : v ∈ roots) : (starts fs).count v = 1 := by
    rw [start]
    have pos := List.count_pos_iff.mpr mem
    have low := List.nodup_iff_count_le_one.mp distinct v
    omega
  have same := ownership fs physical unique proper allRoots
    (fun v _ hv => one v (by simpa [b] using hv)) (by
      intro v hv cut
      have absent : v ∉ roots := by simpa [b] using cut
      exact ⟨by rw [start]; exact List.count_eq_zero.mpr absent,read v hv absent⟩)
  have perm : (nodes fs).Perm physical := List.perm_iff_count.mpr same
  refine ⟨fs,start,perm.length_eq,same,?_⟩
  intro v hv
  exact cutReads fs physical same allRoots (by simp [b,hv])

end PCX150.Rooted

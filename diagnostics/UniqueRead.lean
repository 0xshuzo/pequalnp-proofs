import PEqualNP.Defs
namespace PCX150
open PEqualNP.ProofComplexity
abbrev Cl := Clause (Fin 4 × Fin 3)
structure Links {n : Nat} (atLine : Fin n → Cl) where
  parent : Fin n → Option (Fin n × Fin n)
  ax : ∀ i, parent i = none → atLine i ∈ PHP 4 3
  rule : ∀ i j k, parent i = some (j,k) →
    i.val < j.val ∧ i.val < k.val ∧ IsResolvent (atLine j) (atLine k) (atLine i)


end PCX150


namespace PCX150
variable {n : Nat} {C : Fin n → Cl}
def LeftRaw (g : Links C) (i : Fin n) : Prop :=
  ∃ j k, g.parent i = some (j,k) ∧ g.parent j = none

def RightRaw (g : Links C) (i : Fin n) : Prop := ∃ j k, g.parent i = some (j,k) ∧ g.parent k = none

noncomputable def rawSlots (g : Links C) : Nat := by
  classical
  exact ∑ i : Fin n, ((if LeftRaw g i then 1 else 0) + (if RightRaw g i then 1 else 0))


end PCX150

namespace PCX150.Links
open PEqualNP.ProofComplexity
variable {n : Nat} {C : Fin n → Cl}

/-- One physical rule contributes separately for each of its two argument positions. -/
def contribution (g : Links C) (i v : Fin n) : Nat :=
  match g.parent i with
  | none => 0
  | some (j,k) => (if v=j then 1 else 0)+(if v=k then 1 else 0)

def incoming (g : Links C) (v : Fin n) : Nat := ∑ i : Fin n, g.contribution i v

noncomputable def derived (g : Links C) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun i => g.parent i ≠ none)

noncomputable def raws (g : Links C) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun i => g.parent i = none)

def inputs (g : Links C) (i : Fin n) : List (Fin n) :=
  match g.parent i with
  | some (j,k) => [j,k]
  | none => []

inductive Used (g : Links C) (root : Fin n) : Fin n → Prop where
  | rootLine : Used g root root
  | input {i j} : Used g root i → j ∈ g.inputs i → Used g root j

theorem later (g : Links C) {i j} (mem : j ∈ g.inputs i) : i.val < j.val := by
  cases h : g.parent i with
  | none => simp [inputs,h] at mem
  | some pair =>
    obtain ⟨u,v⟩ := pair
    have edge := g.rule _ _ _ h
    simp only [inputs,h,List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl | rfl
    · exact edge.1
    · exact edge.2.1

theorem chargePositive (g : Links C) {i v : Fin n} :
    0 < g.contribution i v ↔ v ∈ g.inputs i := by
  cases h : g.parent i with
  | none => simp [contribution,inputs,h]
  | some pair =>
    obtain ⟨j,k⟩ := pair
    by_cases a : v=j <;> by_cases b : v=k <;> simp [contribution,inputs,h,a,b]

theorem incomingPositive (g : Links C) (v : Fin n) :
    0 < g.incoming v ↔ ∃ i, v ∈ g.inputs i := by
  classical
  constructor
  · intro h
    by_contra! none
    have zero : ∀ i, g.contribution i v = 0 := fun i =>
      Nat.eq_zero_of_not_pos (by rw [g.chargePositive]; exact none i)
    simp [incoming,zero] at h
  · rintro ⟨i,hi⟩
    have pos := g.chargePositive.mpr hi
    have le : g.contribution i v ≤ g.incoming v :=
      Finset.single_le_sum (f := fun u => g.contribution u v) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    omega

end PCX150.Links

namespace PCX150
def portList (pair : Option (Nat × Nat)) : List Nat :=
  match pair with
  | none => []
  | some (j,k) => [j,k]


end PCX150

namespace PCX150.Links
open PEqualNP.ProofComplexity
variable {n : Nat} {C : Fin n → Cl}

def natParent (g : Links C) (k : Nat) : Option (Nat × Nat) :=
  if h : k < n then (g.parent ⟨k,h⟩).map (fun p => (p.1.val,p.2.val)) else none

def natClause (C : Fin n → Cl) (outside : Cl) (k : Nat) : Cl :=
  if h : k < n then C ⟨k,h⟩ else outside

theorem natEdge (g : Links C) (outside : Cl) {i j k : Nat}
    (edge : g.natParent i = some (j,k)) :
    i < j ∧ i < k ∧ j < n ∧ k < n ∧
      IsResolvent (natClause C outside j) (natClause C outside k) (natClause C outside i) := by
  unfold natParent at edge
  split at edge
  next hi =>
    cases e : g.parent ⟨i,hi⟩ with
    | none => simp [e] at edge
    | some pair =>
      obtain ⟨u,v⟩ := pair
      obtain ⟨rfl,rfl⟩ : u.val=j ∧ v.val=k := by simpa [e] using edge
      obtain ⟨a,b,r⟩ := g.rule _ _ _ e
      exact ⟨a,b,u.isLt,v.isLt,by simpa [natClause,u.isLt,v.isLt,hi] using r⟩
  next => contradiction

theorem natAx (g : Links C) (outside : Cl) (ok : outside ∈ PHP 4 3)
    {i} (leaf : g.natParent i = none) : natClause C outside i ∈ PHP 4 3 := by
  by_cases hi : i < n
  · have hp : g.parent ⟨i,hi⟩ = none := by simpa [natParent,hi] using leaf
    simpa [natClause,hi] using g.ax ⟨i,hi⟩ hp
  · simpa [natClause,hi] using ok

theorem natDerived (g : Links C) (i : Fin n) :
    g.natParent i.val ≠ none ↔ g.parent i ≠ none := by simp [natParent,i.isLt]

theorem natRoots (g : Links C) (v : Nat) :
    g.natParent v ≠ none ↔ ∃ i : Fin n, i.val = v ∧ g.parent i ≠ none := by
  constructor
  · intro h
    by_cases hv : v < n
    · exact ⟨⟨v,hv⟩,rfl,(g.natDerived ⟨v,hv⟩).1 h⟩
    · simp [natParent,hv] at h
  · rintro ⟨i,rfl,h⟩
    exact (g.natDerived i).2 h

end PCX150.Links

namespace PCX150.Links
open PEqualNP.ProofComplexity
variable {n : Nat} {C : Fin n → Cl}

theorem soleReader (g : Links C) (v : Fin n) (single : g.incoming v = 1) :
    ∃ u : Fin n, u.val < v.val ∧ g.parent u ≠ none ∧
      ∀ x, g.contribution x v = if x = u then 1 else 0 := by
  classical
  have pos : 0 < g.incoming v := by omega
  obtain ⟨u,slot⟩ := (g.incomingPositive v).mp pos
  have hu := g.chargePositive.mpr slot
  have le := Finset.single_le_sum (f := fun x => g.contribution x v)
    (fun x _ => Nat.zero_le _) (Finset.mem_univ u)
  change g.contribution u v ≤ g.incoming v at le
  have one : g.contribution u v = 1 := by omega
  have nonzero : g.parent u ≠ none := by
    intro bad
    simp [contribution,bad] at one
  refine ⟨u,g.later slot,nonzero,?_⟩
  intro x
  by_cases eq : x = u
  · simpa [eq] using one
  · rw [if_neg eq]
    have e := Finset.sum_erase_add (Finset.univ : Finset (Fin n)) (fun j => g.contribution j v) (Finset.mem_univ u)
    change _ + _ = g.incoming v at e
    have xmem : x ∈ (Finset.univ : Finset (Fin n)).erase u := by simp [eq]
    have b := Finset.single_le_sum (f := fun j => g.contribution j v) (fun j _ => Nat.zero_le _) xmem
    omega

theorem portCount (g : Links C) (x v : Fin n) :
    (portList (g.natParent x.val)).count v.val = g.contribution x v := by
  cases h : g.parent x with
  | none => simp [natParent,x.isLt,h,contribution,portList]
  | some pair =>
    obtain ⟨j,k⟩ := pair
    by_cases a : v = j <;> by_cases b : v = k <;>
      simp_all [natParent,x.isLt,h,contribution,portList,List.count_cons,Fin.ext_iff,eq_comm,Nat.add_comm]

theorem soleNatReader (g : Links C) (v : Fin n) (single : g.incoming v = 1) :
    ∃ u : Nat, u < v.val ∧ g.natParent u ≠ none ∧
      ∀ x, (portList (g.natParent x)).count v.val = if x = u then 1 else 0 := by
  obtain ⟨u,lt,hd,only⟩ := g.soleReader v single
  refine ⟨u.val,lt,(g.natDerived u).2 hd,?_⟩
  intro x
  by_cases hx : x < n
  · have cnt := g.portCount ⟨x,hx⟩ v
    rw [only] at cnt
    simpa [Fin.ext_iff] using cnt
  · have ne : x ≠ u.val := by intro eq; subst x; exact hx u.isLt
    simp [natParent,hx,ne,portList]

end PCX150.Links

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
open PEqualNP.ProofComplexity LabeledTree

def Permit {f R} (raw : Nat → Prop) (other : List Nat) (t : LabeledTree f R) : Prop :=
  ∀ i ∈ t.leaves, raw i ∨ i ∈ other

private theorem permitSplice {f R raw other i} {t : LabeledTree f R} {p : LabeledTree f (f i)}
    (old : ∀ k ∈ t.leaves, k ≠ i → raw k ∨ k ∈ other)
    (inside : Permit raw other p) : Permit raw other (t.splice i p) := by
  intro k hk
  rcases t.spliceLeaves i p k hk with ⟨ne,mem⟩ | mem
  · exact old k mem ne
  · exact inside k mem

private theorem permitMono {f R raw xs ys} {t : LabeledTree f R}
    (h : Permit raw xs t) (sub : ∀ x ∈ xs, x ∈ ys) : Permit raw ys t := by
  intro k hk
  exact (h k hk).imp_right (sub k)

/-- Apply the numerical tree bound to any three cut fragments with two named shared roots. -/
private theorem threeCost {f raw a b} {x : LabeledTree f (f a)} {y : LabeledTree f (f b)}
    {z : LabeledTree f ∅} (source : ∀ i, raw i → f i ∈ PHP 4 3)
    (weights : ∀ {A B i j k}, ResTree (PHP 4 3) A i → ResTree (insert A (PHP 4 3)) B j →
      ResTree (insert B (insert A (PHP 4 3))) ∅ k → 38 ≤ i+j+k)
    (hx : Permit raw [] x) (hy : Permit raw [a] y) (hz : Permit raw [b,a] z) :
    38 ≤ x.cost+y.cost+z.cost := by
  apply weights (A := f a) (B := f b)
  · apply x.toResTree
    intro k hk
    rcases hx k hk with h | h
    · exact source k h
    · simp at h
  · apply y.toResTree
    intro k hk
    rcases hy k hk with h | h
    · exact Or.inr (source k h)
    · have eq : k = a := by simpa using h
      simp [eq]
  · apply z.toResTree
    intro k hk
    rcases hz k hk with h | h
    · exact Or.inr (Or.inr (source k h))
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at h
      rcases h with rfl | rfl <;> simp

/-- Expand each of the three candidate shared nodes in turn; each duplicated
    fragment increases the physical step count by exactly its own cost. -/
theorem afterThreeCopies {f raw a b c} (A : LabeledTree f (f a)) (B : LabeledTree f (f b))
    (C : LabeledTree f (f c)) (E : LabeledTree f ∅) (source : ∀ i, raw i → f i ∈ PHP 4 3)
    (weight : ∀ {P Q i j k}, ResTree (PHP 4 3) P i → ResTree (insert P (PHP 4 3)) Q j →
      ResTree (insert Q (insert P (PHP 4 3))) ∅ k → 38 ≤ i+j+k)
    (hA : Permit raw [] A) (hB : Permit raw [a] B) (hC : Permit raw [b,a] C)
    (hE : Permit raw [c,b,a] E)
    (twoA : B.leaves.count a + C.leaves.count a + E.leaves.count a = 2)
    (twoB : C.leaves.count b + E.leaves.count b = 2) (twoC : E.leaves.count c = 2) :
    let total := A.cost+B.cost+C.cost+E.cost
    38 ≤ total+A.cost ∧ 38 ≤ total+B.cost ∧ 38 ≤ total+C.cost := by
  dsimp only
  have removeA {R} (t : LabeledTree f R) (rest : List Nat)
      (ht : Permit raw (rest ++ [a]) t) : Permit raw rest (t.splice a A) := by
    apply permitSplice _ (permitMono hA (by simp))
    intro k hk ne
    simpa [ne] using ht k hk
  have removeB {R} (t : LabeledTree f R) (rest : List Nat)
      (memA : a ∈ rest) (ht : ∀ k ∈ t.leaves, raw k ∨ k = b ∨ k ∈ rest) :
      Permit raw rest (t.splice b B) := by
    apply permitSplice _ (permitMono hB (by simpa using memA))
    intro k hk ne
    simpa [ne] using ht k hk
  have sa := threeCost source weight (removeA B [] hB) (removeA C [b] hC)
    (removeA E [c,b] hE)
  have sb := threeCost source weight hA (removeB C [a] (by simp) (by simpa [Permit] using hC))
    (removeB E [c,a] (by simp) (by simpa [Permit,or_comm,or_assoc,or_left_comm] using hE))
  have sc := threeCost source weight hA hB (permitSplice
    (t := E) (i := c) (p := C) (fun k hk ne => by simpa [ne] using hE k hk) hC)
  simp only [spliceCost] at sa sb sc
  have ca := congrArg (fun n : Nat => n * A.cost) twoA
  have cb := congrArg (fun n : Nat => n * B.cost) twoB
  simp only [Nat.add_mul,Nat.two_mul] at ca cb
  rw [twoC,Nat.two_mul] at sc
  omega
end PCX150

namespace PCX150
open PEqualNP.ProofComplexity

theorem satOfTree {F : Set Cl} {C : Cl} {n : Nat} (tree : ResTree F C n)
    (a : V → Bool) (model : ∀ D ∈ F, ClauseSat a D) : ClauseSat a C := by
  induction tree with
  | ax h => exact model _ h
  | res _ _ step left right =>
    obtain ⟨v,_,_,rfl⟩ := step
    cases h : a v with
    | false =>
      obtain ⟨l,mem,val⟩ := left
      have ne : l ≠ (v,true) := by rintro rfl; simp [h] at val
      exact ⟨l,Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨ne,mem⟩),val⟩
    | true =>
      obtain ⟨l,mem,val⟩ := right
      have ne : l ≠ (v,false) := by rintro rfl; simp [h] at val
      exact ⟨l,Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨ne,mem⟩),val⟩

private theorem uniqueSign {x y z : Bool} (hx : x ≠ z) (hy : y ≠ z) : x = y := by
  cases x <;> cases y <;> cases z <;> simp_all

/-- Two nonempty clauses can refute by themselves only if one resolution step suffices. -/
theorem refuteTwo {A B : Cl} {n : Nat} (tree : ResTree ({A,B} : Set Cl) ∅ n)
    (na : A.Nonempty) (nb : B.Nonempty) : IsResolvent A B ∅ ∨ IsResolvent B A ∅ := by
  classical
  have noBoth (a : V → Bool) (sa : ClauseSat a A) (sb : ClauseSat a B) : False := by
    have sat := satOfTree tree a (by
      intro D hd
      rcases Set.mem_insert_iff.mp hd with eq | mem
      · simpa [eq] using sa
      · have eq : D = B := Set.mem_singleton_iff.mp mem
        simpa [eq] using sb)
    simpa [ClauseSat] using sat
  have opposite (l) (hl : l ∈ A) (m) (hm : m ∈ B) : l.1 = m.1 ∧ l.2 ≠ m.2 := by
    by_cases eq : l.1 = m.1
    · refine ⟨eq,?_⟩
      intro same
      exact noBoth (fun _ => l.2) ⟨l,hl,rfl⟩ ⟨m,hm,same⟩
    · let a : V → Bool := fun v => if v = l.1 then l.2 else m.2
      exact (noBoth a ⟨l,hl,by simp [a]⟩ ⟨m,hm,by simp [a,Ne.symm eq]⟩).elim
  obtain ⟨u,hu⟩ := na
  obtain ⟨v,hv⟩ := nb
  have h := opposite u hu v hv
  have oneA : A = {u} := by
    ext l
    constructor
    · intro hl
      have p := opposite l hl v hv
      exact Finset.mem_singleton.mpr (Prod.ext (p.1.trans h.1.symm) (uniqueSign p.2 h.2))
    · intro hl
      exact (Finset.mem_singleton.mp hl).symm ▸ hu
  have oneB : B = {v} := by
    ext m
    constructor
    · intro hm
      have p := opposite u hu m hm
      exact Finset.mem_singleton.mpr (Prod.ext (p.1.symm.trans h.1) (uniqueSign (Ne.symm p.2) (Ne.symm h.2)))
    · intro hm
      exact (Finset.mem_singleton.mp hm).symm ▸ hv
  obtain ⟨u,us⟩ := u
  obtain ⟨v,vs⟩ := v
  change u = v ∧ us ≠ vs at h
  obtain ⟨rfl,neq⟩ := h
  rw [oneA,oneB]
  cases us <;> cases vs <;> simp_all [IsResolvent]

end PCX150

namespace PCX150
open PEqualNP.ProofComplexity LabeledTree

private theorem otherLength (xs : List Nat) (c : Nat) :
    (xs.filter (fun k => decide (k ≠ c))).length + xs.count c = xs.length := by
  induction xs with
  | nil => rfl
  | cons k ks ih =>
    by_cases eq : k = c
    · subst k
      simp [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] at ih ⊢
      omega
    · simp [eq,Ne.symm eq] at ih ⊢
      omega

private theorem oneModel (u : Cl) (hn : u.Nonempty) :
    ∃ a : V → Bool, ClauseSat a u := by
  obtain ⟨l,hl⟩ := hn
  exact ⟨fun _ => l.2,l,hl,rfl⟩

private theorem otherLabel {f c} {e : LabeledTree f ∅}
    (three : e.leaves.length ≤ 3) (twice : e.leaves.count c = 2) (nc : (f c).Nonempty) :
    ∃ k ∈ e.leaves, k ≠ c ∧ ∀ u ∈ e.leaves, u = c ∨ u = k := by
  let other := e.leaves.filter (fun k => decide (k ≠ c))
  have hlength : other.length ≤ 1 := by
    have eq := otherLength e.leaves c
    change (e.leaves.filter _).length ≤ 1
    omega
  cases h : other with
  | nil =>
    obtain ⟨a,sa⟩ := oneModel (f c) nc
    have only : ∀ x ∈ e.leaves, f x ∈ ({f c} : Set Cl) := by
      intro x hx
      by_contra bad
      have ne : x ≠ c := by rintro rfl; simp at bad
      have mem : x ∈ other := List.mem_filter.mpr ⟨hx,by simpa using ne⟩
      simp [h] at mem
    have contra := satOfTree (e.toResTree only) a (by simpa using sa)
    simpa [ClauseSat] using contra
  | cons k ks =>
    have rest : ks = [] := by
      have hh : other.length = ks.length + 1 := by rw [h]; rfl
      have small : ks.length = 0 := by omega
      exact List.length_eq_zero_iff.mp small
    subst ks
    have km : k ∈ other := by simp [h]
    obtain ⟨km',ne⟩ := List.mem_filter.mp km
    refine ⟨k,km',by simpa using ne,?_⟩
    intro u hu
    by_cases eq : u = c
    · exact Or.inl eq
    · have mem : u ∈ other := List.mem_filter.mpr ⟨hu,by simpa using eq⟩
      exact Or.inr (by simpa [h] using mem)

theorem shortEnd {f raw a b c} (A : LabeledTree f (f a)) (B : LabeledTree f (f b))
    (C : LabeledTree f (f c)) (E : LabeledTree f ∅) (source : ∀ i, raw i → f i ∈ PHP 4 3)
    (weights : ∀ {P Q i j k}, ResTree (PHP 4 3) P i → ResTree (insert P (PHP 4 3)) Q j →
      ResTree (insert Q (insert P (PHP 4 3))) ∅ k → 38 ≤ i+j+k)
    (hA : Permit raw [] A) (hB : Permit raw [a] B) (hC : Permit raw [b,a] C)
    (hE : Permit raw [c,b,a] E) (nc : (f c).Nonempty) (proper : ∀ k ∈ E.leaves, (f k).Nonempty)
    (two : E.leaves.count c = 2) (small : E.cost ≤ 2) :
    38 ≤ A.cost+B.cost+C.cost+1 := by
  have three := E.leafCount
  obtain ⟨k,hk,ne,only⟩ := otherLabel (by omega) two nc
  have setTree : ResTree ({f c,f k} : Set Cl) ∅ E.cost := E.toResTree (by
    intro u hu
    rcases only u hu with rfl | rfl <;> simp)
  have allow : raw k ∨ k ∈ [b,a] := by simpa [ne] using hE k hk
  have allowedJoin (rule : IsResolvent (f c) (f k) ∅) :
      Permit raw [b,a] (LabeledTree.resolve C (.leaf k) rule) := by
    intro u hu
    simp only [LabeledTree.leaves,List.mem_append,List.mem_singleton] at hu
    rcases hu with hu | rfl
    · exact hC u hu
    · exact allow
  rcases refuteTwo setTree nc (proper k hk) with rule | rule
  · have h := threeCost source weights hA hB (allowedJoin rule)
    simp only [LabeledTree.cost,Nat.add_zero] at h
    omega
  · have allowed : Permit raw [b,a] (LabeledTree.resolve (.leaf k) C rule) := by
      intro u hu
      simp only [LabeledTree.leaves,List.mem_append,List.mem_singleton] at hu
      rcases hu with rfl | hu
      · exact allow
      · exact hC u hu
    have h := threeCost source weights hA hB allowed
    simp only [LabeledTree.cost,Nat.zero_add] at h
    omega

end PCX150

namespace PCX150
open PEqualNP.ProofComplexity

abbrev TreeLower := ∀ {P Q : Cl} {i j k : Nat},
  ResTree (PHP 4 3) P i → ResTree (insert P (PHP 4 3)) Q j →
  ResTree (insert Q (insert P (PHP 4 3))) ∅ k → 38 ≤ i+j+k

theorem forbidFour {f raw a b c}
    (A : LabeledTree f (f a)) (B : LabeledTree f (f b)) (C : LabeledTree f (f c))
    (E : LabeledTree f ∅) (source : ∀ i, raw i → f i ∈ PHP 4 3) (weight : TreeLower)
    (hA : Permit raw [] A) (hB : Permit raw [a] B) (hC : Permit raw [b,a] C)
    (hE : Permit raw [c,b,a] E)
    (twoA : B.leaves.count a+C.leaves.count a+E.leaves.count a=2)
    (twoB : C.leaves.count b+E.leaves.count b=2) (twoC : E.leaves.count c=2)
    (nonempty : (f c).Nonempty) (proper : ∀ k ∈ E.leaves, (f k).Nonempty)
    (tiny : A.cost+B.cost+C.cost+E.cost ≤ 29) : False := by
  obtain ⟨ha,hb,hc⟩ := afterThreeCopies A B C E source weight hA hB hC hE twoA twoB twoC
  have last : E.cost ≤ 2 := by omega
  have no := shortEnd A B C E source weight hA hB hC hE nonempty proper twoC last
  omega

theorem forbidThree {f raw a b}
    (A : LabeledTree f (f a)) (B : LabeledTree f (f b)) (E : LabeledTree f ∅)
    (source : ∀ i, raw i → f i ∈ PHP 4 3) (weight : TreeLower)
    (hA : Permit raw [] A) (hB : Permit raw [a] B) (hE : Permit raw [b,a] E)
    (tiny : A.cost+B.cost+E.cost ≤ 29) : False := by
  have no := threeCost source weight hA hB hE
  omega

theorem forbidTwo {f raw a} (A : LabeledTree f (f a)) (E : LabeledTree f ∅)
    (source : ∀ i, raw i → f i ∈ PHP 4 3) (weight : TreeLower)
    (hA : Permit raw [] A) (hE : Permit raw [a] E)
    (tiny : A.cost+E.cost ≤ 29) : False := by
  let B : LabeledTree f (f a) := .leaf a
  have pB : Permit raw [a] B := by simp [B,Permit,LabeledTree.leaves]
  apply forbidThree A B E source weight hA pB
  · simpa [Permit] using hE
  · simpa [B,LabeledTree.cost] using tiny

theorem forbidOne {f raw} (E : LabeledTree f ∅) (i : Nat) (pure : raw i)
    (source : ∀ v, raw v → f v ∈ PHP 4 3) (weight : TreeLower)
    (hE : Permit raw [] E) (tiny : E.cost ≤ 29) : False := by
  let A : LabeledTree f (f i) := .leaf i
  have pA : Permit raw [] A := by simp [A,Permit,LabeledTree.leaves,pure]
  apply forbidTwo A E source weight pA
  · intro v hv
    exact Or.inl (by simpa using hE v hv)
  · simpa [A,LabeledTree.cost] using tiny

end PCX150

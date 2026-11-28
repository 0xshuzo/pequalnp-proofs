import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9471.ConditionalPrice
open PEqualNP.ProofComplexity PEqualNP.Search
variable {V : Type} [DecidableEq V]

def negs (c : Clause V) : Set (Literal V) := negLit '' (↑c : Set (Literal V))
def db (F : Set (Clause V)) (xs : List (Clause V)) : Set (Clause V) := F ∪ {d | d ∈ xs}
def bad (G : Set (Clause V)) (A : Set (Literal V)) : Prop :=
  ∃ d ∈ G, ∀ l ∈ d, UPForces G A (negLit l)
def conditional (G : Set (Clause V)) (a c : Clause V) : Prop :=
  bad G (negs a ∪ negs c)
inductive Run (F : Set (Clause V)) (a : Clause V) : List (Clause V) → Prop
  | nil : Run F a []
  | step {xs c} : Run F a xs → conditional (db F xs) a c → Run F a (c :: xs)

def guard (a c : Clause V) := c ∪ a

theorem guarded_hyps (a c : Clause V) : negs (guard a c) = negs a ∪ negs c := by
  ext z
  constructor
  · rintro ⟨l,hl,rfl⟩
    rcases Finset.mem_union.mp hl with hc | ha
    · exact Or.inr ⟨l,hc,rfl⟩
    · exact Or.inl ⟨l,ha,rfl⟩
  · rintro (⟨l,hl,rfl⟩ | ⟨l,hl,rfl⟩)
    · exact ⟨l,Finset.mem_union_right _ hl,rfl⟩
    · exact ⟨l,Finset.mem_union_left _ hl,rfl⟩

theorem ordinary_under {F : Set (Clause V)} {a : Clause V} {xs : List (Clause V)}
    (h : IsRUPRun F xs) : Run F a xs := by
  induction h with
  | nil => exact .nil
  | @learn xs c _ step ih =>
    apply Run.step ih
    obtain ⟨d,hd,why⟩ := step
    refine ⟨d,hd,?_⟩
    intro l hl
    have extA {k : Literal V} (hk : UPForces (db F xs) (negs c) k) :
        UPForces (db F xs) (negs a ∪ negs c) k := by
      induction hk with
      | hyp hz => exact .hyp (Or.inr hz)
      | unit hz hmem _ next => exact .unit hz hmem next
    exact extA (why l hl)

theorem guard_run {F : Set (Clause V)} {a : Clause V} {xs : List (Clause V)}
    (h : Run F a xs) : IsRUPRun F (xs.map (guard a)) := by
  induction h with
  | nil => exact .nil
  | @step xs c previous price ih =>
    apply IsRUPRun.learn ih
    change bad (db F (xs.map (guard a))) (negs (guard a c))
    rw [guarded_hyps]
    let G := db F (xs.map (guard a))
    let B := negs a ∪ negs c
    have paid {z : Literal V} (hz : z ∈ a) : UPForces G B (negLit z) :=
      .hyp (Or.inl ⟨z,hz,rfl⟩)
    have old {d : Clause V} (hd : d ∈ xs) : guard a d ∈ G :=
      Or.inr (List.mem_map.mpr ⟨d,hd,rfl⟩)
    have move {z : Literal V} (hz : UPForces (db F xs) B z) : UPForces G B z := by
      induction hz with
      | hyp e => exact .hyp e
      | @unit d l hd hl _ next =>
        rcases hd with base | learned
        · exact .unit (Or.inl base) hl next
        · apply UPForces.unit (old learned) (Finset.mem_union_left _ hl)
          intro k hk ne
          rcases Finset.mem_union.mp hk with orig | covered
          · exact next k orig ne
          · exact paid covered
    obtain ⟨d,hd,dead⟩ := price
    rcases hd with base | learned
    · exact ⟨d,Or.inl base,fun l hl => move (dead l hl)⟩
    · refine ⟨guard a d,old learned,?_⟩
      intro l hl
      rcases Finset.mem_union.mp hl with orig | covered
      · exact move (dead l orig)
      · exact paid covered

theorem exact_price (F : Set (Clause V)) (a : Clause V) (n : Nat) :
    (∃ xs : List (Clause V), xs.length ≤ n ∧ IsRUPRun F (a :: xs)) ↔
    (∃ xs : List (Clause V), xs.length ≤ n ∧ Run F a ((∅ : Clause V) :: xs)) := by
  constructor
  · rintro ⟨xs,le,h⟩
    cases h with
    | learn prev curr =>
      refine ⟨xs,le,Run.step (ordinary_under prev) ?_⟩
      simpa [conditional,bad,negs,db,IsRUP] using curr
  · rintro ⟨xs,le,h⟩
    refine ⟨xs.map (guard a),by simpa using le,?_⟩
    simpa [guard] using guard_run h

end PEqualNP.Outside.L_meta_9471.ConditionalPrice

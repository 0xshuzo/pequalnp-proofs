import PEqualNP.Defs
open PEqualNP.ProofComplexity PEqualNP.Search
namespace PEqualNP.Outside.L_meta_9471.SharedResidues
variable {V : Type} [DecidableEq V] [Fintype V] {I : Type}
theorem carry {G H : Set (Clause V)} {A B : Set (Literal V)}
    (sub : G ⊆ H) (initial : ∀ l ∈ A, UPForces H B l)
    {l} (force : UPForces G A l) : UPForces H B l := by
  induction force with
  | hyp h => exact initial _ h
  | unit hd hl _ ih => exact .unit (sub hd) hl ih

theorem weaken {G : Set (Clause V)} {c d : Clause V} (sub : c⊆d) (ok : IsRUP G c) : IsRUP G d := by
  obtain ⟨q,hq,all⟩ := ok
  refine ⟨q,hq,fun k hk => carry (fun _ h => h) ?_ (all k hk)⟩
  rintro _ ⟨z,hz,rfl⟩
  exact .hyp ⟨z,sub hz,rfl⟩


abbrev Val (V : Type) := V → Option Bool
def Good (s : I → Val V) (a : I → Option (Clause V)) (l : Literal V) : Prop :=
  ∀ i d, a i = some d → s i l.1 ≠ some l.2 ∧ (s i l.1 = none → l ∈ d)

noncomputable def cap (s : I → Val V) (a : I → Option (Clause V)) : Clause V := by
  classical
  exact Finset.univ.filter (Good s a)

theorem split {s : Val V} {c d : Clause V} (h : restrictClause s c = some d) :
    (¬ ∃ l ∈ c, s l.1 = some l.2) ∧ c.filter (fun l => s l.1 = none) = d := by
  unfold restrictClause at h
  split at h
  · contradiction
  · exact ⟨by assumption,Option.some.inj h⟩

theorem capSub {s : I → Val V} {a : I → Option (Clause V)} {c : Clause V}
    (hc : ∀ i, restrictClause (s i) c = a i) : c ⊆ cap s a := by
  classical
  intro l hl
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _,?_⟩
  intro i d hd
  obtain ⟨absent,eq⟩ := split ((hc i).trans hd)
  exact ⟨fun yes => absent ⟨l,hl,yes⟩,fun free => eq ▸ Finset.mem_filter.mpr ⟨hl,free⟩⟩

theorem capSound {s : I → Val V} {a : I → Option (Clause V)} {c : Clause V}
    (hc : ∀ i, restrictClause (s i) c = a i) : ∀ i, restrictClause (s i) (cap s a) = a i := by
  classical
  intro i
  have child := hc i
  have sub := capSub hc
  cases he : a i with
  | none =>
    rw [he] at child
    unfold restrictClause at child ⊢
    split at child
    · obtain ⟨l,hl,eq⟩ := ‹∃ l ∈ c, s i l.1 = some l.2›
      simp only [if_pos (show ∃ z ∈ cap s a, s i z.1 = some z.2 from ⟨l,sub hl,eq⟩)]
    · contradiction
  | some d =>
    obtain ⟨_,same⟩ := split (child.trans he)
    have ok (l : Literal V) (hl : l ∈ cap s a) := (Finset.mem_filter.mp hl).2 i d he
    have clear : ¬ ∃ l ∈ cap s a, s i l.1 = some l.2 := by
      rintro ⟨l,hl,yes⟩
      exact (ok l hl).1 yes
    simp only [restrictClause,if_neg clear,Option.some.injEq]
    ext l
    constructor
    · intro h
      obtain ⟨hl,free⟩ := Finset.mem_filter.mp h
      exact (ok l hl).2 free
    · intro h
      rw [← same] at h
      obtain ⟨hl,free⟩ := Finset.mem_filter.mp h
      exact Finset.mem_filter.mpr ⟨sub hl,free⟩

theorem oneStep (G : Set (Clause V)) (s : I → Val V) (a : I → Option (Clause V)) :
    (∃ c, IsRUP G c ∧ ∀ i, restrictClause (s i) c = a i) ↔
    IsRUP G (cap s a) ∧ ∀ i, restrictClause (s i) (cap s a) = a i := by
  constructor
  · rintro ⟨c,ok,res⟩
    exact ⟨weaken (capSub res) ok,capSound res⟩
  · intro h
    exact ⟨_,h⟩

end PEqualNP.Outside.L_meta_9471.SharedResidues

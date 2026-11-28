import PEqualNP.Defs
namespace PEqualNP.Outside.L_pcx_178.StarOrder

abbrev Row := Fin 5
abbrev Hole := Fin 4
def precedes (u v : Row) : Prop := u=v ∨ (u.val<3 ∧ u.val<v.val)
def active (owner : Row → Row → Hole → Row) (p : Row) (h : Hole) : Prop :=
    ∃ q : Row, q≠p ∧ owner p q h = p

/-- The first three proper stops are sorted shared vertices. The two final
vertices are the incomparable root children. The two geometric hypotheses
say that an edge belongs to an endpoint and that every active endpoint is
downstream of all four owners of its incident edges in that column. -/
theorem peeling (owner : Row → Row → Hole → Row)
    (symm : ∀ i j h, owner i j h = owner j i h)
    (endpoint : ∀ i j h, i≠j → owner i j h=i ∨ owner i j h=j)
    (broadcast : ∀ i j h, i≠j → active owner i h → precedes (owner i j h) i) :
    (∀ i j h, i.val<3 → i.val<j.val → owner i j h=i) ∧
    ∀ h, (active owner 3 h ∧ ¬active owner 4 h) ∨ (active owner 4 h ∧ ¬active owner 3 h) := by
  have served (i j : Row) (h : Hole) (ne : i≠j) : active owner i h ∨ active owner j h := by
    rcases endpoint i j h ne with hi|hj
    · exact Or.inl ⟨j,Ne.symm ne,hi⟩
    · exact Or.inr ⟨i,ne,(symm j i h).trans hj⟩
  have exclusive (h : Hole) : ¬(active owner 3 h ∧ active owner 4 h) := by
    rintro ⟨a,b⟩
    have l := broadcast 3 4 h (by decide) a
    have r := broadcast 4 3 h (by decide) b
    rw [symm 4 3 h] at r
    rcases endpoint 3 4 h (by decide) with s|s
    · rw [s] at r
      exact (by unfold precedes; decide : ¬precedes 3 4) r
    · rw [s] at l
      exact (by unfold precedes; decide : ¬precedes 4 3) l
  constructor
  · intro i j h ii ij
    have activeI : active owner i h := by
      by_contra no
      have p := served i 3 h (by intro eq; rw [eq] at ii; omega)
      have q := served i 4 h (by intro eq; rw [eq] at ii; omega)
      exact exclusive h ⟨p.resolve_left no,q.resolve_left no⟩
    have ne : i≠j := fun eq => (Nat.ne_of_lt ij) (congrArg Fin.val eq)
    have l := broadcast i j h ne activeI
    rcases endpoint i j h ne with hi|hj
    · exact hi
    · rw [hj] at l
      rcases l with eq|⟨_,lt⟩
      · exact False.elim (ne eq.symm)
      · omega
  · intro h
    rcases served 3 4 h (by decide) with a|b
    · exact Or.inl ⟨a,fun b => exclusive h ⟨a,b⟩⟩
    · exact Or.inr ⟨b,fun a => exclusive h ⟨a,b⟩⟩
end PEqualNP.Outside.L_pcx_178.StarOrder

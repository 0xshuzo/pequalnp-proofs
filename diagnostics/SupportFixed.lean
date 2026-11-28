import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2374

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def target (x : Fin 10 → Bool) := (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)

abbrev X := Fin 10 → Bool

def vertex (v : Fin 10) : X := fun i => decide (i=v)
def edgeRow (u v : Fin 10) : X := fun i => decide (i=u ∨ i=v)
def adj (u v : Fin 10) := target (edgeRow u v)=true
def supported (S : Finset (Fin 10)) (f : X → Bool) :=
  ∀ x y, (∀ i∈S, x i=y i) → f x=f y

theorem singles : ∀ v, target (vertex v)=false := by decide +kernel
theorem neighbors : ∀ v, ∃ w, adj v w := by unfold adj; decide +kernel

def room (U : Finset (Fin 10)) : Finset (Fin 10) :=
  Finset.univ.filter (fun v => v∉U ∧ ∀ a∈U, target (edgeRow a v)=false)

theorem geom : ∀ U : Finset (Fin 10), 3≤U.card → (room U).card≤2 := by decide +kernel

theorem equal_vertex (S : Finset (Fin 10)) (f : X → Bool) (dep : supported S f)
    {u : Fin 10} (miss : u∉S) (v : Fin 10) : f (edgeRow u v)=f (vertex v) := by
  apply dep
  intro i hi
  have ne : i≠u := fun eq => miss (eq ▸ hi)
  simp [edgeRow,vertex,ne]

theorem supportCost (S T : Finset (Fin 10)) (f g : X → Bool)
    (fs : supported S f) (gs : supported T g)
    (correct : ∀ x, (f x || g x)=target x) :
    8≤S.card ∨ 8≤T.card := by
  classical
  have off (p : Fin 10) : f (vertex p)=false ∧ g (vertex p)=false := by
    have h := (correct (vertex p)).trans (singles p)
    cases h1 : f (vertex p) <;> cases h2 : g (vertex p) <;> simp_all
  have swapped (p r : Fin 10) : edgeRow p r=edgeRow r p := by
    funext x
    simp only [edgeRow,or_comm]
  have both (p : Fin 10) : p∈S ∨ p∈T := by
    by_contra! h
    obtain ⟨r,edge⟩ := neighbors p
    have f0 := (equal_vertex S f fs h.1 r).trans (off r).1
    have g0 := (equal_vertex T g gs h.2 r).trans (off r).2
    have on := (correct (edgeRow p r)).trans edge
    simp [f0,g0] at on
  have no {p r : Fin 10} (a : p∉S) (b : r∉T) : target (edgeRow p r)=false := by
    have f0 := (equal_vertex S f fs a r).trans (off r).1
    have g0 : g (edgeRow p r)=false := by
      rw [swapped]
      exact (equal_vertex T g gs b p).trans (off p).2
    simpa only [f0,g0,Bool.false_or] using (correct (edgeRow p r)).symm
  by_cases big : 8≤S.card
  · exact Or.inl big
  apply Or.inr
  let U := Finset.univ \ S
  let V := Finset.univ \ T
  have sub : V ⊆ room U := by
    intro v hv
    have vt := (Finset.mem_sdiff.mp hv).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_,?_⟩
    · intro vu
      exact (Finset.mem_sdiff.mp vu).2 ((both v).resolve_right vt)
    · intro a ha
      exact no (Finset.mem_sdiff.mp ha).2 vt
  have us : U.card=10-S.card := by
    rw [show U=Finset.univ\S from rfl,Finset.card_sdiff]
    simp
  have vs : V.card=10-T.card := by
    rw [show V=Finset.univ\T from rfl,Finset.card_sdiff]
    simp
  have geo := geom U (by omega)
  have cnt := Finset.card_le_card sub
  omega

end PEqualNP.Outside.L_meta_2374

import PEqualNP.Defs

namespace PlaneRows5176

def inc (p l : Fin 13) : Prop := p-l ∈ ([0,1,3,9] : List (Fin 13))
instance (p l : Fin 13) : Decidable (inc p l) := inferInstanceAs (Decidable (p-l ∈ ([0,1,3,9] : List (Fin 13))))

def off (a b c d : Fin 13) : Finset (Fin 13) :=
  Finset.univ.filter fun l => ¬inc a l ∧ ¬inc b l ∧ ¬inc c l ∧ ¬inc d l

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem four : ∀ a b c d : Fin 13, a<b → b<c → c<d → (off a b c d).card≤3 := by
  intro a
  fin_cases a <;> decide

theorem small_side (P L : Finset (Fin 13)) (none : ∀ p∈P, ∀ l∈L, ¬inc p l) :
    P.card≤3 ∨ L.card≤3 := by
  by_cases hp : P.card≤3
  · exact Or.inl hp
  right
  obtain ⟨Q,hsub,hc⟩ := Finset.exists_subset_card_eq (s:=P) (show 4≤P.card by omega)
  let f := Q.orderEmbOfFin hc
  have hb (i : Fin 4) : f i∈P := hsub (Finset.orderEmbOfFin_mem Q hc i)
  have hL : L ⊆ off (f 0) (f 1) (f 2) (f 3) := by
    intro l hl
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩
    exact ⟨none _ (hb 0) _ hl, none _ (hb 1) _ hl, none _ (hb 2) _ hl, none _ (hb 3) _ hl⟩
  exact (Finset.card_le_card hL).trans (four _ _ _ _ (f.strictMono (by decide : (0:Fin 4)<1))
      (f.strictMono (by decide : (1:Fin 4)<2)) (f.strictMono (by decide : (2:Fin 4)<3)))

theorem samples_complete (F : Finset (Fin 13) → Finset (Fin 13) → Bool)
    (mono : ∀ P L P' L', P ⊆ P' → L ⊆ L' → F P L=true → F P' L'=true)
    (pos : ∀ p l, inc p l → F {p} {l}=true)
    (neg : ∀ T : Finset (Fin 13), T.card≤3 →
      F T (Finset.univ.filter (fun l => ∀ p∈T, ¬inc p l))=false ∧
      F (Finset.univ.filter (fun p => ∀ l∈T, ¬inc p l)) T=false) :
    ∀ P L, F P L=true ↔ ∃ p∈P, ∃ l∈L, inc p l := by
  intro P L
  constructor
  · intro eqv
    by_contra h
    have indep : ∀ p∈P, ∀ l∈L, ¬inc p l := fun p hp l hl e => h ⟨p,hp,l,hl,e⟩
    rcases small_side P L indep with hp|hl
    · have bound : L ⊆ Finset.univ.filter (fun l => ∀ p∈P, ¬inc p l) := by
        intro l hL; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,fun p hP => indep p hP l hL⟩
      exact Bool.noConfusion ((neg P hp).1.symm.trans (mono _ _ _ _ (Finset.Subset.refl _) bound eqv))
    · have bound : P ⊆ Finset.univ.filter (fun p => ∀ l∈L, ¬inc p l) := by
        intro p hP; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,indep p hP⟩
      exact Bool.noConfusion ((neg L hl).2.symm.trans (mono _ _ _ _ bound (Finset.Subset.refl _) eqv))
  · rintro ⟨p,hp,l,hl,e⟩
    exact mono _ _ _ _ (Finset.singleton_subset_iff.mpr hp) (Finset.singleton_subset_iff.mpr hl) (pos p l e)
end PlaneRows5176

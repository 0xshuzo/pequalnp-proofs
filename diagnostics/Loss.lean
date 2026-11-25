import Mathlib

namespace LastOr6796

variable {E : Type} [DecidableEq E]

def Covers (edges : Finset E) (available : Finset (Finset E)) (terms : List (Finset E)) :=
  (∀ t ∈ terms, t∈available) ∧ ∀ e∈edges, ∃ t∈terms,e∈t

theorem repair {edges exceptional : Finset E} {available : Finset (Finset E)}
    {terms : List (Finset E)} (thin : Finset E → Finset E)
    (singles : ∀ e∈exceptional, {e}∈available)
    (legal : ∀ t∈terms,thin t∈available)
    (lost : ∀ t∈terms,∀ e∈t,e∉thin t → e∈exceptional)
    (cover : ∀ e∈edges, ∃ t∈terms,e∈t) :
    ∃ old, Covers edges available old ∧ old.length=terms.length+exceptional.card := by
  let old := terms.map thin ++ exceptional.toList.map (fun e => ({e} : Finset E))
  refine ⟨old,⟨?_,?_⟩,?_⟩
  · intro t ht
    rcases List.mem_append.mp ht with h | h
    · obtain ⟨q,hq,rfl⟩ := List.mem_map.mp h
      exact legal q hq
    · obtain ⟨e,he,rfl⟩ := List.mem_map.mp h
      exact singles e (Finset.mem_toList.mp he)
  · intro e he
    obtain ⟨q,hq,eq⟩ := cover e he
    by_cases present : e∈thin q
    · exact ⟨thin q,List.mem_append.mpr (Or.inl (List.mem_map.mpr ⟨q,hq,rfl⟩)),present⟩
    · have lostE := lost q hq e eq present
      exact ⟨{e},List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨e,Finset.mem_toList.mpr lostE,rfl⟩)),by simp⟩
  · simp [old]

/-- The bank right before an OR contains both possible intersections with any
positive guard whose negative evaluations avoid both arguments of that OR. -/
theorem lastOr {edges left right guards : Finset E} {available : Finset (Finset E)}
    (singles : ∀ e∈edges, {e}∈available) {terms : List (Finset E)}
    (split : ∀ t∈terms, t∈available ∨
      t∩left∈available ∧ t∩right∈available ∧ t⊆left∪right ∧ t⊆guards)
    (cover : ∀ e∈edges, ∃ t∈terms,e∈t) :
    ∃ old, Covers edges available old ∧ old.length ≤ terms.length+
      min (((edges∩guards)∩right)\left).card (((edges∩guards)∩left)\right).card := by
  classical
  have side (a b : Finset E)
      (pieces : ∀ t∈terms, t∈available ∨ t∩a∈available ∧ t⊆a∪b ∧ t⊆guards) :
      ∃ old, Covers edges available old ∧ old.length ≤ terms.length+(((edges∩guards)∩b)\a).card := by
    let thin := fun t : Finset E => if t∈available then t else t∩a
    have lex (t) (ht : t∈terms) : thin t∈available := by
      rcases pieces t ht with h | ⟨h,_,_⟩
      · simp [thin,h]
      · by_cases q : t∈available <;> simp [thin,q,h]
    let old := terms.map thin ++ ((((edges∩guards)∩b)\a).toList.map (fun e => ({e} : Finset E)))
    refine ⟨old,⟨?_,?_⟩,?_⟩
    · intro t ht
      rcases List.mem_append.mp ht with h | h
      · obtain ⟨q,hq,rfl⟩ := List.mem_map.mp h
        exact lex _ hq
      · obtain ⟨e,he,rfl⟩ := List.mem_map.mp h
        exact singles e (Finset.mem_inter.mp (Finset.mem_inter.mp (Finset.mem_sdiff.mp (Finset.mem_toList.mp he)).1).1).1
    · intro e he
      obtain ⟨t,ht,et⟩ := cover e he
      by_cases ok : e∈thin t
      · exact ⟨thin t,List.mem_append.mpr (Or.inl (List.mem_map.mpr ⟨t,ht,rfl⟩)),ok⟩
      · have out : t∉available := fun known => ok (by simpa [thin,known] using et)
        obtain ⟨_,sub,gd⟩ := (pieces t ht).resolve_left out
        have ea : e∉a := fun h => ok (by simpa [thin,out] using Finset.mem_inter.mpr ⟨et,h⟩)
        have eb := (Finset.mem_union.mp (sub et)).resolve_left ea
        have em : e∈((edges∩guards)∩b)\a := Finset.mem_sdiff.mpr ⟨Finset.mem_inter.mpr ⟨Finset.mem_inter.mpr ⟨he,gd et⟩,eb⟩,ea⟩
        exact ⟨{e},List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨e,Finset.mem_toList.mpr em,rfl⟩)),by simp⟩
    · simp [old]
  by_cases bound : (((edges∩guards)∩right)\left).card ≤ (((edges∩guards)∩left)\right).card
  · rw [min_eq_left bound]
    exact side left right (fun t ht => (split t ht).imp_right (fun h => ⟨h.1,h.2.2.1,h.2.2.2⟩))
  · rw [min_eq_right (Nat.le_of_not_ge bound)]
    apply side right left
    intro t ht
    apply (split t ht).imp_right
    rintro ⟨_,r,sub,gd⟩
    exact ⟨r,by simpa only [Finset.union_comm] using sub,gd⟩

end LastOr6796

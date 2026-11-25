import Mathlib

namespace Factor2585
variable {P L : Type*} [DecidableEq P] [DecidableEq L]
def hit (G : P → L → Prop) (A : Finset P) (B : Finset L) : Prop :=
  ∃ p∈A, ∃ l∈B,G p l

/-- The other factor may be any monotone predicate. Its accepted independent
    assignment rules out cross-nonedges between untouched matching endpoints. -/
theorem obstruction {r m : Nat} (G : P→L→Prop) (U : Fin r→Finset P) (V : Fin r→Finset L)
    (K : Finset P→Finset L→Prop)
    (correct : ∀ A B,hit G A B ↔
      (∃ t, (A∩U t).Nonempty ∧ (B∩V t).Nonempty) ∧ K A B)
    (mono : ∀ A B A' B', A⊆A' → B⊆B' → K A B → K A' B')
    (linear : ∀ p p' l l',p≠p' → l≠l' → ¬(G p l ∧ G p l' ∧ G p' l ∧ G p' l'))
    (X : Finset P) (Y : Finset L) (independent : ¬hit G X Y) (accepted : K X Y)
    (p : Fin m→P) (l : Fin m→L) (pi : Function.Injective p) (li : Function.Injective l)
    (matching : ∀ i,G (p i) (l i))
    (clearP : ∀ i,∀ b∈Y,¬G (p i) b) (clearL : ∀ j,∀ a∈X,¬G a (l j)) : m ≤ r := by
  classical
  have root (i : Fin m) : ∃ t,p i∈U t ∧ l i∈V t := by
    have yes : hit G {p i} {l i} := ⟨p i,by simp,l i,by simp,matching i⟩
    obtain ⟨t,⟨a,ha⟩,⟨b,hb⟩⟩ := ((correct _ _).1 yes).1
    obtain ⟨pa,ua⟩ := Finset.mem_inter.mp ha
    obtain ⟨lb,vb⟩ := Finset.mem_inter.mp hb
    have ea : a=p i := Finset.mem_singleton.mp pa
    have eb : b=l i := Finset.mem_singleton.mp lb
    exact ⟨t,ea ▸ ua,eb ▸ vb⟩
  choose f hf using root
  have cross (i j : Fin m) (t : Fin r) (hu : p i∈U t) (hv : l j∈V t) : G (p i) (l j) := by
    have k := mono X Y (insert (p i) X) (insert (l j) Y)
      (Finset.subset_insert ..) (Finset.subset_insert ..) accepted
    have pos := (correct (insert (p i) X) (insert (l j) Y)).2
      ⟨⟨t,⟨p i,Finset.mem_inter.mpr ⟨Finset.mem_insert_self ..,hu⟩⟩,
          ⟨l j,Finset.mem_inter.mpr ⟨Finset.mem_insert_self ..,hv⟩⟩⟩,k⟩
    obtain ⟨a,ha,b,hb,edge⟩ := pos
    rcases Finset.mem_insert.mp ha with rfl|ha <;> rcases Finset.mem_insert.mp hb with rfl|hb
    · exact edge
    · exact False.elim (clearP i b hb edge)
    · exact False.elim (clearL j a ha edge)
    · exact False.elim (independent ⟨a,ha,b,hb,edge⟩)
  have finj : Function.Injective f := by
    intro i j e
    by_contra ne
    have pij := cross i j (f i) (hf i).1 (by rw [e];exact (hf j).2)
    have pji := cross j i (f i) (by rw [e];exact (hf j).1) (hf i).2
    exact linear _ _ _ _ (fun h => ne (pi h)) (fun h => ne (li h)) ⟨matching i,pij,pji,matching j⟩
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective f finj

end Factor2585

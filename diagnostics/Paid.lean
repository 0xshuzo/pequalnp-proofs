import PEqualNP.Defs

namespace Paid17719

inductive Reach {α : Type} (op : Bool → α → α → α) (goal : α) : Nat → Set α → Prop
  | out {k S} (h : goal ∈ S) : Reach op goal k S
  | gate {k S a b} (d : Bool) (ha : a ∈ S) (hb : b ∈ S)
      (h : Reach op goal k (insert (op d a b) S)) : Reach op goal (k+1) S

theorem Reach.mono {α : Type} {op : Bool → α → α → α} {goal : α} {k : Nat} {S : Set α}
    (p : Reach op goal k S) : ∀ {S' : Set α}, S ⊆ S' → Reach op goal k S' := by
  induction p with
  | out h => exact fun h' => .out (h' h)
  | gate d ha hb _ ih =>
    intro T h
    exact .gate d (h ha) (h hb) (ih (Set.insert_subset_insert h))

section
variable {α β : Type} {op : Bool → α → α → α} {ob : Bool → β → β → β}
variable (phi : α → β) (zero : β)
def image (S : Set α) : Set β := insert zero (phi '' S)

theorem map_mem {S : Set α} {w : α} (h : w ∈ S) : phi w ∈ image phi zero S :=
  Set.mem_insert_of_mem _ ⟨w,h,rfl⟩

theorem map_insert (S : Set α) (v : α) : image phi zero (insert v S) =
    insert (phi v) (image phi zero S) := by
  ext y
  simp only [image, Set.image_insert_eq, Set.mem_insert_iff]
  tauto

theorem simulate {goal : α} {k S} (h : Reach op goal k S)
    (hom : ∀ d a b, phi (op d a b) = ob d (phi a) (phi b)) :
    Reach ob (phi goal) k (image phi zero S) := by
  induction h with
  | out h => exact .out (map_mem _ _ h)
  | gate d ha hb _ ih =>
    apply Reach.gate d (map_mem phi zero ha) (map_mem phi zero hb)
    rw [map_insert,hom] at ih
    exact ih

theorem paid_projection {goal : α} {k S} (h : Reach op goal k S)
    (hom : ∀ d a b, phi (op d a b) = ob d (phi a) (phi b))
    (different : α → Prop)
    (unchanged : ∀ d a b, ¬different a → ¬different b → ¬different (op d a b))
    (erasable : ∀ d a b, phi a = zero ∨ phi b = zero →
      phi (op d a b) = zero ∨ phi (op d a b) = phi a ∨ phi (op d a b) = phi b)
    (target_changes : different goal) (survives : phi goal ≠ zero)
    (initial : ∀ w ∈ S, different w → phi w = zero) :
    ∃ l < k, Reach ob (phi goal) l (image phi zero S) := by
  classical
  induction h with
  | out h => exact False.elim (survives (initial _ h target_changes))
  | @gate k S a b d ha hb cont ih =>
    by_cases hits : different a ∨ different b
    · have hz : phi a = zero ∨ phi b = zero := hits.imp (initial a ha) (initial b hb)
      have ready : phi (op d a b) ∈ image phi zero S := by
        rcases erasable d a b hz with e | e | e
        · rw [e]; exact Set.mem_insert _ _
        · rw [e]; exact map_mem phi zero ha
        · rw [e]; exact map_mem phi zero hb
      have p := simulate phi zero cont hom
      rw [map_insert] at p
      exact ⟨k, by omega, p.mono (Set.insert_subset ready (Set.Subset.rfl))⟩
    · have next : ∀ w ∈ insert (op d a b) S, different w → phi w = zero := by
        intro w hw diff
        rcases Set.mem_insert_iff.mp hw with rfl | hw
        · exact False.elim ((unchanged d a b (fun hn => hits (Or.inl hn))
              (fun hn => hits (Or.inr hn))) diff)
        · exact initial _ hw diff
      obtain ⟨l,hl,p⟩ := ih next
      rw [map_insert,hom] at p
      exact ⟨l+1, by omega, .gate d (map_mem phi zero ha) (map_mem phi zero hb) p⟩

end
end Paid17719

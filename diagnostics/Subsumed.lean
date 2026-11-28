import PEqualNP.Defs

open PEqualNP.ProofComplexity PEqualNP.Search
namespace PEqualNP.Outside.L_meta_9471.Subsumed
variable {V : Type}

abbrev C (V : Type) := Clause V
def Extends (H G : Set (C V)) : Prop := ∀ c ∈ G, ∃ d ∈ H, d ⊆ c
def Conflict (H : Set (C V)) (A : Set (Literal V)) : Prop :=
  ∃ d ∈ H, ∀ l ∈ d, UPForces H A (negLit l)

theorem forces_of_cover {H G : Set (C V)} {A : Set (Literal V)} {u : Literal V}
    (cov : Extends H G) (clean : ¬ Conflict H A) (p : UPForces G A u) :
    UPForces H A u := by
  induction p with
  | hyp ha => exact .hyp ha
  | @unit c v hc hv others ih =>
    obtain ⟨d,hd,sub⟩ := cov c hc
    by_cases keep : v∈d
    · exact .unit hd keep (fun l hl ne => ih l (sub hl) ne)
    · exact (clean ⟨d,hd,fun l hl => ih l (sub hl) (fun eq => keep (eq ▸ hl))⟩).elim

theorem rup_of_cover {H G : Set (C V)} {c : C V}
    (cov : Extends H G) (r : IsRUP G c) : IsRUP H c := by
  classical
  by_contra bad
  obtain ⟨d,hd,v⟩ := r
  obtain ⟨e,he,sub⟩ := cov d hd
  exact bad ⟨e,he,fun l hl => forces_of_cover cov bad (v l (sub hl))⟩

def bank (F : Set (C V)) (xs : List (C V)) : Set (C V) := F ∪ {c | c∈xs}
def skip (F : Set (C V)) (xs : List (C V)) (c : C V) : Prop :=
  c ≠ ∅ ∧ ∃ d ∈ bank F xs, d ⊆ c

noncomputable def thin (F : Set (C V)) : List (C V) → List (C V) := by
  classical
  exact fun xs => xs.rec [] fun c tail previous => if skip F tail c then previous else c::previous

@[simp] theorem thin_nil (F : Set (C V)) : thin F []=[] := rfl
open Classical in
theorem thin_cons (F : Set (C V)) (c : C V) (xs : List (C V)) :
    thin F (c::xs) = if _ : skip F xs c then thin F xs else c::thin F xs := by
  classical
  by_cases h : skip F xs c <;> simp [thin,h]

theorem extThin (F : Set (C V)) (xs : List (C V)) : Extends (bank F (thin F xs)) (bank F xs) := by
  classical
  induction xs with
  | nil => exact fun c hc => ⟨c,hc,(fun _ h => h)⟩
  | cons c xs ih =>
    rw [thin_cons]
    by_cases z : skip F xs c
    · rw [dif_pos z]
      intro p hp
      rcases hp with hp|hp
      · exact ih p (Or.inl hp)
      · rcases List.mem_cons.mp hp with rfl|inOld
        · obtain ⟨_,d,hd,dc⟩ := z
          obtain ⟨e,he,ed⟩ := ih d hd
          exact ⟨e,he,fun l hl => dc (ed hl)⟩
        · exact ih p (Or.inr inOld)
    · rw [dif_neg z]
      intro p hp
      have lift {d : C V} : d∈bank F (thin F xs) → d∈bank F (c::thin F xs) := by
        rintro (hf|hl)
        · exact Or.inl hf
        · exact Or.inr (List.mem_cons_of_mem _ hl)
      rcases hp with hf|hl
      · exact ⟨p,Or.inl hf,(fun _ h => h)⟩
      · rcases List.mem_cons.mp hl with rfl|old
        · exact ⟨_,Or.inr List.mem_cons_self,(fun _ h => h)⟩
        · obtain ⟨d,hd,sub⟩ := ih p (Or.inr old)
          exact ⟨d,lift hd,sub⟩

theorem runThin (F : Set (C V)) {xs : List (C V)} (r : IsRUPRun F xs) :
    IsRUPRun F (thin F xs) := by
  classical
  induction r with
  | nil => exact .nil
  | @learn xs c prev step ih =>
    rw [thin_cons]
    split
    · exact ih
    · exact .learn ih (rup_of_cover (extThin F xs) step)

theorem emptyThin (F : Set (C V)) (xs : List (C V)) (e : (∅ : C V)∈xs) :
    (∅ : C V)∈thin F xs := by
  classical
  induction xs with
  | nil => simp at e
  | cons c xs ih =>
    rw [thin_cons]
    rcases List.mem_cons.mp e with eq|earlier
    · subst c
      simp [skip]
    · split
      · exact ih earlier
      · exact List.mem_cons_of_mem _ (ih earlier)

end PEqualNP.Outside.L_meta_9471.Subsumed

import PEqualNP.Defs

namespace PHP169Projection

variable {α β : Type}

-- Pigeon rows and hole columns of the positive literals in an intermediate.
abbrev Board (α β : Type) := α → β → Prop

def rowsOf (C : Board α β) : Set α := {i | ∃ j, C i j}

def sharedCols (C : Board α β) (P : Set α) : Set β := {j | ∀ i ∈ P, C i j}

-- Positive literals after joining the donor and the current hole child.
-- T is the donor's untreated future holes; B is the child rows at this hole.
def joined (P : Set α) (S : Set β) (i : α) (h : β) (T : Set β) (B : Set α) :
    Board α β :=
  fun k j => k ∈ P ∧ (j ∈ S ∨ (k = i ∧ j ∈ T) ∨ (k ∈ B ∧ j = h))

theorem joined_rows (P : Set α) (S : Set β) (i : α) (h : β) (T : Set β)
    (B : Set α) (hs : S.Nonempty) : rowsOf (joined P S i h T B) = P := by
  ext k
  constructor
  · rintro ⟨j,hj⟩
    exact hj.1
  · intro hk
    obtain ⟨j,hj⟩ := hs
    exact ⟨j,hk,Or.inl hj⟩

theorem joined_cols (P : Set α) (S : Set β) (i : α) (h : β) (T : Set β)
    (B : Set α) (hi : i ∈ P) (hb : i ∉ B) (hh : h ∉ T)
    (ho : ∃ k ∈ P, k ≠ i) : sharedCols (joined P S i h T B) P = S := by
  ext j
  constructor
  · intro all
    by_contra ns
    have a := (all i hi).2
    obtain ⟨k,hk,ne⟩ := ho
    have b := (all k hk).2
    rcases a with a | ⟨_,a⟩ | ⟨a,_⟩
    · exact ns a
    · rcases b with b | ⟨b,_⟩ | ⟨_,b⟩
      · exact ns b
      · exact ne b
      · exact hh (b ▸ a)
    · exact hb a
  · intro hj k hk
    exact ⟨hk,Or.inl hj⟩

-- A partially discharged raw child. The negative literal is on donor i,
-- and all remaining positive literals are on other pigeons.
def guarded (P : Set α) (S : Set β) (i : α) (h : β) (B : Set α) :
    Board α β := fun k j => k ∈ P ∧ k ≠ i ∧ (j ∈ S ∨ (k ∈ B ∧ j = h))

theorem guarded_rows (P : Set α) (S : Set β) (i : α) (h : β) (B : Set α)
    (hs : S.Nonempty) : rowsOf (guarded P S i h B) = {k | k ∈ P ∧ k ≠ i} := by
  ext k
  constructor
  · rintro ⟨j,hj⟩
    exact ⟨hj.1,hj.2.1⟩
  · rintro ⟨hk,ne⟩
    obtain ⟨j,hj⟩ := hs
    exact ⟨j,hk,ne,Or.inl hj⟩

theorem guarded_cols (P : Set α) (S : Set β) (i : α) (h : β) (B : Set α)
    (ho : ∃ k ∈ P, k ≠ i ∧ k ∉ B) :
    sharedCols (guarded P S i h B) {k | k ∈ P ∧ k ≠ i} = S := by
  ext j
  constructor
  · intro all
    obtain ⟨k,hk,ne,nb⟩ := ho
    rcases (all k ⟨hk,ne⟩).2.2 with mem | ⟨mem,_⟩
    · exact mem
    · exact False.elim (nb mem)
  · intro hj k hk
    exact ⟨hk.1,hk.2,Or.inl hj⟩

-- A transferred non-first implication has all rows of its packet, even
-- the row of its own negative literal. It cannot equal a raw child with
-- the same negative literal.
theorem transfer_ne_guarded (P Q : Set α) (S V : Set β) (i neg : α) (h k : β)
    (T : Set β) (B : Set α) (hs : S.Nonempty) (hp : neg ∈ P) :
    joined P S i h T ∅ ≠ guarded Q V neg k B := by
  intro eq
  obtain ⟨j,hj⟩ := hs
  have x : joined P S i h T ∅ neg j := ⟨hp,Or.inl hj⟩
  rw [eq] at x
  exact x.2.1 rfl

end PHP169Projection

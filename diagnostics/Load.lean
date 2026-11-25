import Mathlib

namespace Load2585
variable {X Y : Type*} [DecidableEq X] [DecidableEq Y]

inductive Pool (X : Type*) [DecidableEq X] : Nat → Finset (Finset X) → Prop where
  | raw {S} (h : ∀ A∈S, A.card≤1) : Pool X 0 S
  | join {k S} (pr : Pool X k S) {A B : Finset X} (ha : A∈S) (hb : B∈S) :
      Pool X (k+1) (insert (A∪B) S)

def edges (R : Finset (Y × Finset X)) : Finset (Y × X) :=
  R.biUnion fun z => z.2.image (fun x => (z.1,x))

theorem edge_mem (R : Finset (Y × Finset X)) (y : Y) (x : X) :
    (y,x) ∈ edges R ↔ ∃ A, (y,A)∈R ∧ x∈A := by
  constructor
  · intro h
    obtain ⟨⟨t,A⟩,ha,r⟩ := Finset.mem_biUnion.mp h
    obtain ⟨s,hs,eq⟩ := Finset.mem_image.mp r
    cases eq
    exact ⟨A,ha,hs⟩
  · rintro ⟨A,ha,hx⟩
    exact Finset.mem_biUnion.mpr ⟨(y,A),ha,Finset.mem_image.mpr ⟨x,hx,rfl⟩⟩

theorem at_most_one_union {A B : Finset X} (small : (A∪B).card≤1) :
    A∪B=A ∨ A∪B=B := by
  by_cases non : A.Nonempty
  · left
    exact (Finset.eq_of_subset_of_card_le (Finset.subset_union_left : A⊆A∪B)
      (small.trans (Finset.card_pos.mpr non))).symm
  · right
    have h := Finset.not_nonempty_iff_eq_empty.mp non
    simp [h]

theorem price (N : Y → Finset X)
    (linear : ∀ i j, i≠j → (N i∩N j).card≤1)
    {k : Nat} {S : Finset (Finset X)} (program : Pool X k S) (R : Finset (Y × Finset X))
    (ready : ∀ z∈R,z.2∈S) (safe : ∀ z∈R,z.2⊆N z.1) :
    (edges R).card ≤ R.card+k := by
  classical
  induction program generalizing R with
  | raw h =>
    calc
      _ ≤ ∑ z∈R, (z.2.image (fun x => (z.1,x))).card := Finset.card_biUnion_le
      _ ≤ ∑ _z∈R, 1 := Finset.sum_le_sum (fun z hz => Finset.card_image_le.trans (h _ (ready z hz)))
      _ = _ := by simp
  | @join k S pr A B ha hb ih =>
    by_cases seen : A∪B∈S
    · have bound := ih R (fun z hz => (Finset.mem_insert.mp (ready z hz)).elim (fun e => by rw [e]; exact seen) id) safe
      omega
    by_cases used : ∃ y, (y,A∪B)∈R
    · obtain ⟨v,hv⟩ := used
      have large : 1 < (A∪B).card := by
        by_contra! small
        rcases at_most_one_union small with eq|eq
        · exact seen (by rw [eq]; exact ha)
        · exact seen (by rw [eq]; exact hb)
      have unique (y : Y) (hy : (y,A∪B)∈R) : y=v := by
        by_contra ne
        have sub : A∪B⊆N y∩N v := Finset.subset_inter (safe _ hy) (safe _ hv)
        have z := (Finset.card_le_card sub).trans (linear y v ne)
        omega
      let T := R.erase (v,A∪B)
      let Q := insert (v,A) (insert (v,B) T)
      have qr : ∀ z∈Q, z.2∈S := by
        rintro ⟨y,Z⟩ hz
        rcases Finset.mem_insert.mp hz with eq|hz
        · cases eq; exact ha
        rcases Finset.mem_insert.mp hz with eq|hz
        · cases eq; exact hb
        obtain ⟨ne,hr⟩ := Finset.mem_erase.mp hz
        rcases Finset.mem_insert.mp (ready _ hr) with eq|old
        · change Z=A∪B at eq
          subst Z
          exact False.elim (ne (by rw [unique y hr]))
        · exact old
      have qs : ∀ z∈Q,z.2⊆N z.1 := by
        intro z hz
        rcases Finset.mem_insert.mp hz with rfl|hz
        · exact Finset.subset_union_left.trans (safe _ hv)
        rcases Finset.mem_insert.mp hz with rfl|hz
        · exact Finset.subset_union_right.trans (safe _ hv)
        exact safe _ (Finset.mem_erase.mp hz).2
      have sub : edges R⊆edges Q := by
        rintro ⟨y,x⟩ hx
        obtain ⟨Z,hZ,xZ⟩ := (edge_mem R y x).mp hx
        apply (edge_mem Q y x).mpr
        by_cases he : (y,Z)=(v,A∪B)
        · cases he
          rcases Finset.mem_union.mp xZ with xA|xB
          · exact ⟨A,Finset.mem_insert_self ..,xA⟩
          · exact ⟨B,Finset.mem_insert_of_mem (Finset.mem_insert_self ..),xB⟩
        · exact ⟨Z,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨he,hZ⟩)),xZ⟩
      have hq := (Finset.card_le_card sub).trans (ih Q qr qs)
      have h1 := Finset.card_insert_le (v,A) (insert (v,B) T)
      have h2 := Finset.card_insert_le (v,B) T
      have h3 : T.card+1=R.card := Finset.card_erase_add_one hv
      change (edges R).card ≤ (insert (v,A) (insert (v,B) T)).card+k at hq
      omega
    · have rb : ∀ z∈R,z.2∈S := by
        rintro ⟨y,Z⟩ h
        rcases Finset.mem_insert.mp (ready _ h) with eq|old
        · change Z=A∪B at eq
          exact False.elim (used ⟨y,eq ▸ h⟩)
        · exact old
      have base := ih R rb safe
      omega

end Load2585

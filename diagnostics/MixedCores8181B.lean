import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8181.Pairs

private theorem side_bound {A B : Type*} [DecidableEq A] [DecidableEq B]
    (F : Finset (A × B)) (P : Finset A) (Q : Finset B)
    (cv : ∀ p ∈ F, p.1 ∈ P ∨ p.2 ∈ Q)
    (partner : ∀ i j, (i,j) ∈ F → ∃ i', i' ≠ i ∧ (i',j) ∈ F)
    (free : ∀ i k j l, i ≠ k → j ≠ l → ¬ ((i,j) ∈ F ∧ (i,l) ∈ F ∧ (k,j) ∈ F ∧ (k,l) ∈ F)) :
    (F.filter (fun e => e.2 ∉ Q)).card ≤ P.card*(P.card-1) := by
  classical
  let alt (e : A × B) := if h : e ∈ F then (partner _ _ h).choose else e.1
  have legal (e : A × B) (h : e ∈ F) : alt e ≠ e.1 ∧ (alt e,e.2) ∈ F := by
    simpa only [alt,dif_pos h] using (partner e.1 e.2 h).choose_spec
  have bound : (F.filter (fun e => e.2 ∉ Q)).card ≤ P.offDiag.card := by
    apply Finset.card_le_card_of_injOn (fun e => (e.1,alt e))
    · intro e he
      obtain ⟨h,nq⟩ := Finset.mem_filter.mp he
      obtain ⟨nd,ok⟩ := legal e h
      exact Finset.mem_offDiag.mpr ⟨(cv e h).resolve_right nq,(cv _ ok).resolve_right nq,nd.symm⟩
    · intro e he f hf h
      have er := Finset.mem_filter.mp he
      have fr := Finset.mem_filter.mp hf
      obtain ⟨nd,ok⟩ := legal e er.1
      have fok := (legal f fr.1).2
      have fst : e.1 = f.1 := congrArg Prod.fst h
      have snd : alt e = alt f := congrArg Prod.snd h
      apply Prod.ext fst
      by_contra no
      apply free e.1 (alt e) e.2 f.2 nd.symm no
      exact ⟨er.1,by rw [fst]; exact fr.1,ok,by rw [snd]; exact fok⟩
  calc _ ≤ P.offDiag.card := bound
       _ = _ := by rw [Finset.offDiag_card,Nat.mul_sub, Nat.mul_one]

theorem mixed_cover_bound {A B : Type*} [DecidableEq A] [DecidableEq B]
    (E : Finset (A × B)) (P : Finset A) (Q : Finset B)
    (cv : ∀ e ∈ E, e.1 ∈ P ∨ e.2 ∈ Q)
    (partners : ∀ i j, (i,j) ∈ E →
      (∃ l, l ≠ j ∧ (i,l) ∈ E) ∧ (∃ k, k ≠ i ∧ (k,j) ∈ E))
    (free : ∀ i k j l, i ≠ k → j ≠ l → ¬ ((i,j) ∈ E ∧ (i,l) ∈ E ∧ (k,j) ∈ E ∧ (k,l) ∈ E)) :
    E.card ≤ P.card * (P.card - 1) + Q.card * (Q.card - 1) + P.card * Q.card := by
  classical
  let X := E.filter fun e => e.2 ∉ Q
  let Y := E.filter fun e => e.1 ∉ P
  let Z := E.image Prod.swap
  have zm (i : B) (j : A) : (i,j) ∈ Z ↔ (j,i) ∈ E := by
    constructor
    · rintro h
      obtain ⟨⟨a,b⟩,he,eq⟩ := Finset.mem_image.mp h
      cases eq
      exact he
    · intro h
      exact Finset.mem_image.mpr ⟨(j,i),h,rfl⟩
  have top : X.card ≤ P.card*(P.card-1) := side_bound E P Q cv (fun i j h => (partners i j h).2) free
  have back := side_bound Z Q P (by
    rintro ⟨i,j⟩ h
    exact (cv (j,i) ((zm i j).mp h)).symm)
    (by
      intro i j h
      obtain ⟨l,ne,m⟩ := (partners j i ((zm i j).mp h)).1
      exact ⟨l,ne,(zm l j).mpr m⟩)
    (by
      rintro i k j l ik jl ⟨h1,h2,h3,h4⟩
      exact free j l i k jl ik ⟨(zm _ _).mp h1,(zm _ _).mp h3,(zm _ _).mp h2,(zm _ _).mp h4⟩)
  have symmCard : Y.card ≤ (Z.filter (fun e => e.2 ∉ P)).card := by
    apply Finset.card_le_card_of_injOn Prod.swap
    · rintro ⟨i,j⟩ he
      obtain ⟨h,p⟩ := Finset.mem_filter.mp he
      exact Finset.mem_filter.mpr ⟨(zm _ _).mpr h,p⟩
    · intro a _ b _ eq
      simpa only [Prod.swap_swap] using congrArg Prod.swap eq
  have incl : E ⊆ (X ∪ Y) ∪ (P ×ˢ Q) := by
    intro e he
    by_cases h : e.1 ∈ P
    · by_cases k : e.2 ∈ Q
      · exact Finset.mem_union_right _ (Finset.mem_product.mpr ⟨h,k⟩)
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨he,k⟩))
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨he,h⟩))
  have t := Finset.card_le_card incl
  have u := Finset.card_union_le (X ∪ Y) (P ×ˢ Q)
  have v := Finset.card_union_le X Y
  rw [Finset.card_product] at u
  omega

theorem mixed_four {p q e : Nat} (hp : 0 < p) (hq : 0 < q) (h : p + q ≤ 4)
    (cost : e ≤ p * (p-1) + q * (q-1) + p*q) : e ≤ 9 := by
  have h1 : p ≤ 3 := by omega
  have h2 : q ≤ 3 := by omega
  interval_cases p <;> interval_cases q <;> omega

end PEqualNP.Outside.L_meta_8181.Pairs

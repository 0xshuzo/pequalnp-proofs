import Mathlib
import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_8869.Geometry
open Finset
theorem mul_self_sub_self (n : ℕ) : n * n - n = n * (n - 1) := by
  by_cases hn : n = 0
  · subst hn
    rfl
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    have h1 : (k + 1) * (k + 1) = (k + 1) * k + (k + 1) := by ring
    have h2 : k + 1 - 1 = k := by omega
    rw [h1, h2, Nat.add_sub_cancel]

theorem offDiag_card_eq {α : Type*} [DecidableEq α] (s : Finset α) :
    s.offDiag.card = s.card * (s.card - 1) := by
  rw [Finset.offDiag_card]
  exact mul_self_sub_self s.card

theorem sq_eq_add_mul_pred (n : ℕ) : n ^ 2 = n + n * (n - 1) := by
  by_cases hn : n = 0
  · subst hn
    rfl
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    have hk : k + 1 - 1 = k := by omega
    rw [hk]
    ring

theorem card_filter_product_eq_sum {A B : Type} [DecidableEq A] [DecidableEq B]
    (E : Finset (A × B)) (X : Finset A) (Y : Finset B) :
    ((X ×ˢ Y).filter (fun p => p ∈ E)).card =
      ∑ a ∈ X, (Y.filter (fun b => (a, b) ∈ E)).card := by
  have hS : (X ×ˢ Y).filter (fun p => p ∈ E) =
      X.biUnion (fun a => (Y.filter (fun b => (a, b) ∈ E)).image (fun b => (a, b))) := by
    ext ⟨a, b⟩
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_biUnion, Finset.mem_image]
    constructor
    · rintro ⟨⟨ha, hb⟩, hab⟩
      exact ⟨a, ha, b, ⟨hb, hab⟩, rfl⟩
    · rintro ⟨a', ha', b', ⟨hb', hab'⟩, h⟩
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
      exact ⟨⟨ha', hb'⟩, hab'⟩
  have hdisj : (X : Set A).PairwiseDisjoint
      (fun a => (Y.filter (fun b => (a, b) ∈ E)).image (fun b => (a, b))) := by
    intro a₁ _ a₂ _ hne
    dsimp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro p hp₁ hp₂
    simp only [Finset.mem_image, Finset.mem_filter] at hp₁ hp₂
    obtain ⟨b₁, _, h₁⟩ := hp₁
    obtain ⟨b₂, _, h₂⟩ := hp₂
    exact hne (Prod.mk.inj (h₁.trans h₂.symm)).1
  rw [hS, Finset.card_biUnion hdisj]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.card_image_of_injective]
  exact fun b₁ b₂ h => (Prod.mk.inj h).2

theorem sum_pairs_le_offDiag {A B : Type} [DecidableEq A] [DecidableEq B]
    (E : Finset (A × B))
    (hE : ∀ a a' : A, ∀ b b' : B, a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    (X : Finset A) (Y : Finset B) :
    ∑ a ∈ X, (Y.filter (fun b => (a, b) ∈ E)).card *
        ((Y.filter (fun b => (a, b) ∈ E)).card - 1) ≤
      Y.card * (Y.card - 1) := by
  have hdisj : (X : Set A).PairwiseDisjoint
      (fun a => (Y.filter (fun b => (a, b) ∈ E)).offDiag) := by
    intro a₁ _ a₂ _ hne
    dsimp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro q hq₁ hq₂
    simp only [Finset.mem_offDiag, Finset.mem_filter] at hq₁ hq₂
    have hqne : q.1 ≠ q.2 := by tauto
    have h11 : (a₁, q.1) ∈ E := by tauto
    have h12 : (a₁, q.2) ∈ E := by tauto
    have h21 : (a₂, q.1) ∈ E := by tauto
    have h22 : (a₂, q.2) ∈ E := by tauto
    exact hE a₁ a₂ q.1 q.2 hne hqne ⟨h11, h12, h21, h22⟩
  have hsub : X.biUnion (fun a => (Y.filter (fun b => (a, b) ∈ E)).offDiag) ⊆ Y.offDiag := by
    rw [Finset.biUnion_subset]
    intro a _ q hq
    simp only [Finset.mem_offDiag, Finset.mem_filter] at hq ⊢
    tauto
  calc
    ∑ a ∈ X, (Y.filter (fun b => (a, b) ∈ E)).card *
        ((Y.filter (fun b => (a, b) ∈ E)).card - 1) =
      ∑ a ∈ X, ((Y.filter (fun b => (a, b) ∈ E)).offDiag).card := by
        refine Finset.sum_congr rfl fun a _ => ?_
        exact (offDiag_card_eq (Y.filter (fun b => (a, b) ∈ E))).symm
    _ = (X.biUnion (fun a => (Y.filter (fun b => (a, b) ∈ E)).offDiag)).card :=
        (Finset.card_biUnion hdisj).symm
    _ ≤ Y.offDiag.card := Finset.card_le_card hsub
    _ = Y.card * (Y.card - 1) := offDiag_card_eq Y

theorem tangent (k : Nat) : 30*k≤k*(k-1)+240 := by
  by_cases h : k≤15
  · interval_cases k <;> decide
  · obtain ⟨x,rfl⟩ : ∃ x,k=x+16 := ⟨k-16,by omega⟩
    have e : x+16-1=x+15 := by omega
    rw [e]
    nlinarith [Nat.zero_le (x*x)]

theorem sparse_side {A B : Type} [DecidableEq A] [DecidableEq B]
    (E : Finset (A × B)) (X : Finset A) (Y : Finset B) (sub : E ⊆ X ×ˢ Y)
    (four : ∀ a a' : A, ∀ b b' : B, a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    (yp : 0<Y.card) (ys : Y.card≤240) : E.card+8≤8*(X.card+Y.card) := by
  classical
  let d (a : A) := (Y.filter (fun b => (a,b)∈E)).card
  have el : (X ×ˢ Y).filter (fun e => e ∈ E)=E := by ext e; simp only [mem_filter]; exact ⟨And.right,fun h => ⟨sub h,h⟩⟩
  have summ : E.card=∑ a ∈ X,d a := el ▸ card_filter_product_eq_sum E X Y
  have pairs := sum_pairs_le_offDiag E four X Y
  change ∑ a ∈ X,d a*(d a-1) ≤ Y.card*(Y.card-1) at pairs
  have budget := Finset.sum_le_sum (s:=X) (fun a _ => tangent (d a))
  rw [←Finset.mul_sum,←summ,Finset.sum_add_distrib] at budget
  simp only [Finset.sum_const,Nat.nsmul_eq_mul] at budget
  have last := Nat.mul_le_mul_right (Y.card-1) ys
  have diff : 240*(Y.card-1)+240=240*Y.card := by
    have := Nat.sub_add_cancel (show 1≤Y.card from yp)
    nlinarith
  omega

def SquareFree {A B : Type} (E : Finset (A × B)) : Prop :=
  ∀ a a' : A, ∀ b b' : B, a ≠ a' → b ≠ b' → ¬ ((a,b)∈E ∧ (a,b')∈E ∧ (a',b)∈E ∧ (a',b')∈E)

theorem sparse_either {A B : Type} [DecidableEq A] [DecidableEq B] (E : Finset (A × B))
    (four : SquareFree E) (non : E.Nonempty)
    (small : (E.image Prod.fst).card≤240 ∨ (E.image Prod.snd).card≤240) :
    E.card+8≤8*((E.image Prod.fst).card+(E.image Prod.snd).card) := by
  classical
  let X := E.image Prod.fst
  let Y := E.image Prod.snd
  have sub : E ⊆ X ×ˢ Y := fun e he => mem_product.mpr ⟨mem_image_of_mem _ he,mem_image_of_mem _ he⟩
  obtain ⟨e,he⟩ := non
  rcases small with left|right
  · let D := E.image Prod.swap
    have dm (a : A) (b : B) : (b,a)∈D ↔ (a,b)∈E := by
      simp only [D,mem_image,Prod.exists,Prod.swap_prod_mk,Prod.mk.injEq]
      aesop
    have ds : D ⊆ Y ×ˢ X := by
      rintro ⟨b,a⟩ h
      obtain ⟨u,v⟩ := mem_product.mp (sub ((dm a b).mp h))
      exact mem_product.mpr ⟨v,u⟩
    have df : SquareFree D := by
      rintro b b' a a' ne ne' ⟨one,two,three,last⟩
      exact four a a' b b' ne' ne ⟨(dm _ _).mp one,(dm _ _).mp three,(dm _ _).mp two,(dm _ _).mp last⟩
    have upper := sparse_side D Y X ds df (card_pos.mpr ⟨e.1,(mem_product.mp (sub he)).1⟩) left
    have eq : D.card=E.card := card_image_of_injective _ (fun x y h => by simpa using congrArg Prod.swap h)
    change E.card+8≤8*(X.card+Y.card)
    omega
  · exact sparse_side E X Y sub four (card_pos.mpr ⟨e.2,(mem_product.mp (sub he)).2⟩) right
end PEqualNP.Outside.L_meta_8869.Geometry

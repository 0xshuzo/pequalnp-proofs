import PEqualNP.Defs
import Mathlib

namespace PEqualNP.Outside.L_lib_912_aux

open Finset
open scoped Classical

def singleHost {α β : Type*} (P : Finset (α × β)) (same : α → β → Prop) (p : α × β) : Prop :=
  same p.1 p.2 ∧ ∀ a, (a,p.2) ∈ P → a = p.1

theorem incidence_mass {α β : Type*} (P : Finset (α × β)) (L : Finset β)
    (same : α → β → Prop)
    (valid : ∀ a b, (a,b) ∈ P → same a b → b ∈ L) :
    let exceptional := L.filter (fun b => ¬ ∃ a, (a,b) ∈ P ∧ singleHost P same (a,b))
    let bad := P.filter (fun p => ¬ singleHost P same p)
    let withoutHost := L.filter (fun b => ¬ ∃ a, (a,b) ∈ P)
    Nat.dist L.card P.card + exceptional.card ≤ 3*bad.card + 2*withoutHost.card := by
  classical
  intro exceptional bad withoutHost
  let G := P.filter (singleHost P same)
  let normal := L.filter (fun b => ∃ a, (a,b) ∈ P ∧ singleHost P same (a,b))
  have hn : normal = G.image Prod.snd := by
    ext b
    constructor
    · intro hb
      obtain ⟨a,hab,hg⟩ := (mem_filter.mp hb).2
      exact mem_image.mpr ⟨(a,b),mem_filter.mpr ⟨hab,hg⟩,rfl⟩
    · intro hb
      obtain ⟨⟨a,y⟩,hp,rfl⟩ := mem_image.mp hb
      obtain ⟨hab,hg⟩ := mem_filter.mp hp
      exact mem_filter.mpr ⟨valid a y hab hg.1, a, hab, hg⟩
  have hni : Set.InjOn Prod.snd (↑G : Set (α × β)) := by
    rintro ⟨a,x⟩ hx ⟨a',y⟩ hy he
    dsimp only at he
    subst y
    have hax := (mem_filter.mp hx).2.2 a' (mem_filter.mp hy).1
    exact Prod.ext hax.symm rfl
  have hncard : normal.card = G.card := by rw [hn, card_image_of_injOn hni]
  have hl : normal.card + exceptional.card = L.card :=
    card_filter_add_card_filter_not (s := L) _
  have hp : G.card + bad.card = P.card := card_filter_add_card_filter_not (s := P) _
  have hs : exceptional ⊆ bad.image Prod.snd ∪ withoutHost := by
    intro b hb
    obtain ⟨hbL,ex⟩ := mem_filter.mp hb
    by_cases h : ∃ a, (a,b) ∈ P
    · obtain ⟨a,ha⟩ := h
      exact mem_union_left _ (mem_image.mpr ⟨(a,b),mem_filter.mpr ⟨ha,fun g => ex ⟨a,ha,g⟩⟩,rfl⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨hbL,h⟩)
  have hbad : exceptional.card ≤ bad.card + withoutHost.card :=
    (card_le_card hs).trans ((card_union_le _ _).trans (Nat.add_le_add_right card_image_le _))
  unfold Nat.dist
  omega

theorem twice_tail (s : ℕ → ℕ) (N : ℕ) (h : ∀ i < N, 2*s (i+1) ≤ s i) :
    (∑ i ∈ range (N+1), s i) + s N ≤ 2 * s 0 := by
  induction N with
  | zero => simp; omega
  | succ N ih =>
    have h1 := ih (fun i hi => h i (by omega))
    have h2 := h N (by omega)
    rw [sum_range_succ]
    omega

theorem weighted_tail (g : ℕ → ℕ) {z q N : ℕ} (hz : 2*z ≤ q)
    (hg : ∀ i ≤ N, q*g (i+1) ≤ g i) :
    q * (∑ i ∈ range (N+1), z^(i+1)*g (i+1)) ≤ 2*z*g 0 := by
  let s := fun i => z^(i+1)*g (i+1)
  have hs (i : ℕ) (hi : i < N) : 2*s (i+1) ≤ s i := by
    have hh := (Nat.mul_le_mul_right (g (i+1+1)) hz).trans (hg (i+1) (by omega))
    calc
      2*s (i+1) = z^(i+1) * ((2*z)*g (i+1+1)) := by dsimp [s]; rw [pow_succ z (i+1)]; ring
      _ ≤ z^(i+1) * g (i+1) := Nat.mul_le_mul_left _ hh
      _ = s i := rfl
  have ht := twice_tail s N hs
  have hsum : (∑ i ∈ range (N+1), s i) ≤ 2*s 0 := by omega
  calc
    _ ≤ q*(2*s 0) := Nat.mul_le_mul_left _ hsum
    _ = 2*z*(q*g 1) := by simp [s]; ring
    _ ≤ _ := Nat.mul_le_mul_left _ (hg 0 (by omega))

end PEqualNP.Outside.L_lib_912_aux

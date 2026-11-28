import PEqualNP.Defs

namespace Tap9755

def raw : List Nat := [2863311530,3435973836,4042322160,4278255360,4294901760]
def bank : List Nat := raw ++ [4210752250,4294945450,4291624908,4293984240,4294967040]
def bounds : Fin 6 → Nat × Nat :=
  ![(842152506,16844037),(858991146,5397),(855654156,3342387),
    (858799920,196623),(858996480,63),(3435970752,858996543)]
def fits (p : Fin 6) (v : Nat) : Prop :=
  ((bounds p).1 &&& v) = (bounds p).1 ∧ ((bounds p).2 &&& v) = 0
instance (p : Fin 6) (v : Nat) : Decidable (fits p v) := by unfold fits; infer_instance

def tap (v : Nat) : Prop := ∃ p, fits p v
instance (v : Nat) : Decidable (tap v) := by unfold tap; infer_instance

theorem rawFail : ∀ w∈raw, ¬ tap w := by decide +kernel
theorem lastFail : ∀ w∈bank, ¬ fits 5 w := by decide +kernel
theorem separate : ∀ i j : Fin 6, i≠j →
    ((bounds i).1 &&& (bounds j).2)≠0 ∨ ((bounds j).1 &&& (bounds i).2)≠0 := by decide +kernel

theorem bit_sep {on off w : Nat} (a : (on &&& w) = on) (b : (off &&& w) = 0) :
    (on &&& off)=0 := by
  calc
    on &&& off = (on &&& w) &&& off := congrArg (fun n => n &&& off) a.symm
    _ = on &&& (off &&& w) := by rw [Nat.and_assoc,Nat.and_comm w off]
    _ = 0 := by rw [b,Nat.and_zero]

theorem fits_inj {f : Fin 6 → Nat} (h : ∀ i,fits i (f i)) : Function.Injective f := by
  intro i j eq
  by_contra ne
  have ai:=h i
  have aj:=h j
  rw [eq] at ai
  rcases separate i j ne with a|b
  · exact a (bit_sep ai.1 aj.2)
  · exact b (bit_sep aj.1 ai.2)

theorem negClosed : ∀ a∈bank,tap (4294967295 ^^^ a) → (4294967295 ^^^ a) ∈ bank := by decide +kernel
theorem andClosed : ∀ a∈bank,∀ b∈bank,tap (a &&& b) → (a &&& b) ∈ bank := by decide +kernel
theorem orClosed : ∀ a∈bank,∀ b∈bank,tap (a ||| b) → (a ||| b) ∈ bank := by decide +kernel

inductive Step (w : List Nat) : Nat → Prop where
  | neg {a} : a∈raw++w → Step w (4294967295 ^^^ a)
  | conj {a b} : a∈raw++w → b∈raw++w → Step w (a &&& b)
  | disj {a b} : a∈raw++w → b∈raw++w → Step w (a ||| b)
inductive Program : List Nat → Prop where
  | nil : Program []
  | push {w v} : Program w → Step w v → Program (v::w)

theorem closed {w} (prog : Program w) (only : ∀v∈w,tap v) : ∀v∈w,v∈bank := by
  induction prog with
  | nil => simp
  | @push w v old step ih =>
    have prev := ih (fun a ha => only a (List.mem_cons_of_mem _ ha))
    have inbank (a : Nat) (ha : a∈raw++w) : a∈bank := by
      rcases List.mem_append.mp ha with l|r
      · exact List.mem_append_left _ l
      · exact prev a r
    have tv := only v (by simp)
    have hv : v∈bank := by
      cases step with
      | neg a => exact negClosed _ (inbank _ a) tv
      | conj a b => exact andClosed _ (inbank _ a) _ (inbank _ b) tv
      | disj a b => exact orClosed _ (inbank _ a) _ (inbank _ b) tv
    intro x hx
    rcases List.mem_cons.mp hx with rfl|mem
    · exact hv
    · exact prev x mem

theorem price {w} (prog : Program w) (f : Fin 6 → Nat)
    (observed : ∀i, f i ∈ raw++w) (spec : ∀i,fits i (f i)) : 7≤w.length := by
  classical
  by_contra! short
  have inside (i : Fin 6) : f i ∈ w := by
    rcases List.mem_append.mp (observed i) with l|r
    · exact (rawFail _ l ⟨i,spec i⟩).elim
    · exact r
  let image := Finset.univ.image f
  have six : image.card=6 := by simp [image,Finset.card_image_of_injective _ (fits_inj spec)]
  have sub : image ⊆ w.toFinset := by
    intro a ha
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp ha
    exact List.mem_toFinset.mpr (inside i)
  have card := List.toFinset_card_le w
  have eq : image=w.toFinset := Finset.eq_of_subset_of_card_le sub (by omega)
  have only (a : Nat) (ha : a∈w) : tap a := by
    have hi : a∈image := eq.symm ▸ List.mem_toFinset.mpr ha
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hi
    exact ⟨i,spec i⟩
  exact lastFail _ (closed prog only _ (inside 5)) (spec 5)

end Tap9755

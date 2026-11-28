import PEqualNP.Defs
namespace PEqualNP.Outside.L_pcx_178.AffineFree
abbrev Small := Fin 4 × Fin 3
inductive Symbol where
  | off
  | on
  | pos (u : Small)
  | neg (u : Small)
  | extra (id : Nat) (sign : Bool)
  deriving DecidableEq
def Compatible : Symbol → Symbol → Prop
  | .off, _ => True
  | _, .off => True
  | .pos u, .pos v => u.1≠v.1 ∧ u.2=v.2
  | .pos u, .neg v => u=v
  | .neg u, .pos v => u=v
  | .extra i s, .extra j t => i=j ∧ s≠t
  | _, _ => False

theorem fullThree : ∀ (c : Fin 4) (f : Fin 3→Fin 4), (∀i j, f i=f j → i=j) →
    (∀ i, f i≠c) → ∀ h, h≠c → ∃i,f i=h := by decide +kernel
theorem otherRow : ∀r : Fin 4, ∃ i : Fin 4, i≠r := by decide +kernel

theorem blockExtra (g : Fin 5→Fin 4→Symbol) (sel : Fin 4→Fin 5)
    (anchor : ∀ i j, ∃ h, g (sel i) h=.pos (i,j))
    (pairs : ∀ i k h, i≠k → Compatible (g i h) (g k h))
    (mustFill : ∀ k c, (∀h,h≠c → g k h=.off) → g k c=.on) :
    ∀ k c t b, g k c ≠ .extra t b := by
  intro k c t b exotic
  have blocked (i : Fin 4) (j : Fin 3) : g (sel i) c ≠ .pos (i,j) := by
    intro hit
    by_cases e : k=sel i
    · rw [e,hit] at exotic
      cases exotic
    · have ok := pairs k (sel i) c e
      rw [exotic,hit] at ok
      exact ok
  have fills (i : Fin 4) (h : Fin 4) (ne : h≠c) : ∃ j, g (sel i) h=.pos (i,j) := by
    choose f hf using anchor i
    have inj (a b : Fin 3) (eq : f a=f b) : a=b := by
      have aa:=hf a
      rw [eq,hf b] at aa
      simpa using aa.symm
    have away (a : Fin 3) (eq : f a=c) : False := blocked i a (eq ▸ hf a)
    obtain ⟨a,m⟩:=fullThree c f inj away h ne
    exact ⟨a,m ▸ hf a⟩
  have spare : ∃s : Fin 5, ∀i, sel i ≠ s := by
    by_contra! none
    have sur : Function.Surjective sel := none
    have sz:=Fintype.card_le_of_surjective sel sur
    simp at sz
  obtain ⟨s,sp⟩:=spare
  have zero (h : Fin 4) (hc : h≠c) : g s h=.off := by
    have adj (i : Fin 4) : ∃j, Compatible (g s h) (.pos (i,j)) := by
      obtain ⟨j,m⟩:=fills i h hc
      exact ⟨j,m ▸ pairs s (sel i) h (Ne.symm (sp i))⟩
    cases e : g s h with
    | off => rfl
    | on =>
      obtain ⟨j,z⟩:=adj 0
      rw [e] at z
      exact False.elim z
    | pos u =>
      obtain ⟨j,z⟩:=adj u.1
      rw [e] at z
      exact False.elim (z.1 rfl)
    | neg u =>
      obtain ⟨i,ne⟩:=otherRow u.1
      obtain ⟨j,z⟩:=adj i
      rw [e] at z
      exact False.elim (ne (congrArg Prod.fst (show u=(i,j) from z)).symm)
    | extra id sign =>
      obtain ⟨j,z⟩:=adj 0
      rw [e] at z
      exact False.elim z
  have one:=mustFill s c zero
  by_cases sk : s=k
  · rw [sk,exotic] at one
    cases one
  · have bad:=pairs s k c sk
    rw [one,exotic] at bad
    exact bad
end PEqualNP.Outside.L_pcx_178.AffineFree

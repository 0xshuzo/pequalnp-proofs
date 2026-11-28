import PEqualNP.Defs

namespace PEqualNP.Outside.Pcx177Switch

abbrev H := Fin 4
abbrev R := Fin 5
abbrev B := R → Fin 16
abbrev Label := R → H

def atom (h : H) : Fin 16 := ⟨(2^h.val) % 16, Nat.mod_lt _ (by decide)⟩
def mix (a b c : H) : H := ⟨(a.val ^^^ b.val ^^^ c.val) % 4,Nat.mod_lt _ (by decide)⟩
def add3 (a b c : Fin 16) : Fin 16 := ⟨(a.val ^^^ b.val ^^^ c.val) % 16,Nat.mod_lt _ (by decide)⟩
def has (r : Fin 16) (h : H) : Bool := r.val.testBit h.val
def board (v : Label) : B := fun i => atom (v i)
def join (s t u : B) : B := fun i => add3 (s i) (t i) (u i)

theorem atom_ne : ∀ a : H, atom a ≠ 0 := by decide +kernel
theorem uniqueHole : ∀ a b : H, has (atom a) b = true → a = b := by decide +kernel
theorem three_ne : ∀ a b c : H, add3 (atom a) (atom b) (atom c) ≠ 0 := by decide +kernel
theorem missing : ∀ a b c : H, a≠b → a≠c → b≠c →
    has (add3 (atom a) (atom b) (atom c)) (mix a b c) = false := by decide +kernel

structure Chart where
  region : Set B
  closed : ∀ s ∈ region, ∀ t ∈ region, ∀ u ∈ region, join s t u ∈ region
  addr : B → R → H
  affine : ∀ s ∈ region, ∀ t ∈ region, ∀ u ∈ region, ∀ i,
    addr (join s t u) i = mix (addr s i) (addr t i) (addr u i)
  valid : ∀ s ∈ region, (∀ i, s i ≠ 0) → ∀ i, has (s i) (addr s i) = true

theorem atAtom (L : Chart) {v : Label} (m : board v ∈ L.region) (i : R) :
    L.addr (board v) i = v i := by
  exact (uniqueHole (v i) _ (L.valid _ m (fun k => atom_ne (v k)) i)).symm

theorem noThree (L : Chart) {v w z : Label}
    (mv : board v ∈ L.region) (mw : board w ∈ L.region) (mz : board z ∈ L.region) (i : R)
    (x : v i ≠ w i) (y : v i ≠ z i) (j : w i ≠ z i) : False := by
  have mem := L.closed _ mv _ mw _ mz
  have haveAddr := L.affine _ mv _ mw _ mz i
  rw [atAtom L mv, atAtom L mw, atAtom L mz] at haveAddr
  have take := L.valid _ mem (fun k => three_ne (v k) (w k) (z k)) i
  rw [haveAddr] at take
  change has (add3 (atom (v i)) (atom (w i)) (atom (z i))) (mix (v i) (w i) (z i)) = true at take
  rw [missing _ _ _ x y j] at take
  contradiction

theorem pairCover (S : Set H) (no : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, a ≠ b → a ≠ c → b ≠ c → False) :
    ∃ a b : H, ∀ h ∈ S, h=a ∨ h=b := by
  classical
  by_cases empty : ∃ a, a ∈ S
  · obtain ⟨a,ha⟩ := empty
    by_cases second : ∃ b ∈ S, a ≠ b
    · obtain ⟨b,hb,ab⟩ := second
      refine ⟨a,b,?_⟩
      intro c hc
      by_contra miss
      exact no a ha b hb c hc ab (fun e => miss (Or.inl e.symm)) (fun e => miss (Or.inr e.symm))
    · refine ⟨a,a,?_⟩
      intro c hc
      left
      by_contra e
      exact second ⟨c,hc,Ne.symm e⟩
  · exact ⟨0,0,fun h hh => False.elim (empty ⟨h,hh⟩)⟩

theorem twoLabels (L : Chart) (i : R) : ∃ a b : H, ∀ v : Label,
    board v ∈ L.region → v i = a ∨ v i = b := by
  let S : Set H := {h | ∃ v : Label, board v ∈ L.region ∧ v i=h}
  have nop : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, a ≠ b → a ≠ c → b ≠ c → False := by
    rintro a ⟨v,hv,rfl⟩ b ⟨w,hw,rfl⟩ c ⟨z,hz,rfl⟩
    exact noThree L hv hw hz i
  obtain ⟨a,b,p⟩ := pairCover S nop
  exact ⟨a,b,fun v m => p _ ⟨v,m,rfl⟩⟩

theorem leafCount {k : ℕ} (charts : Fin k → Chart)
    (cover : ∀ v : Label, ∃ c, board v ∈ (charts c).region) : 32 ≤ k := by
  classical
  choose leaf hleaf using cover
  choose first second allowed using fun c i => twoLabels (charts c) i
  let code (v : Label) : Fin k × (R → Bool) :=
    (leaf v, fun i => decide (v i=first (leaf v) i))
  have inject : Function.Injective code := by
    intro v w same
    have eqc : leaf v = leaf w := congrArg Prod.fst same
    have eqb : (fun i => decide (v i=first (leaf v) i)) =
        (fun i => decide (w i=first (leaf w) i)) := congrArg Prod.snd same
    funext i
    have t := congrFun eqb i
    rw [←eqc] at t
    have av := allowed (leaf v) i v (hleaf v)
    have aw := allowed (leaf w) i w (hleaf w)
    rw [←eqc] at aw
    rcases av with h|h <;> rcases aw with j|j
    · exact h.trans j.symm
    · have yes : decide (w i = first (leaf v) i) = true := by simpa [h] using t.symm
      exact h.trans (of_decide_eq_true yes).symm
    · have yes : decide (v i = first (leaf v) i) = true := by simpa [j] using t
      exact (of_decide_eq_true yes).trans j.symm
    · exact h.trans j.symm
  have t := Fintype.card_le_of_injective code inject
  change Fintype.card (Fin 5 → Fin 4) ≤ Fintype.card (Fin k × (Fin 5 → Bool)) at t
  simp at t
  omega

end PEqualNP.Outside.Pcx177Switch

import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9809.Modules
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def gateValue (g : Gate) (b : List Bool) : Bool :=
  g.op.eval (g.inputs.map fun i => b.getD i false)

def evaluate (gs : List Gate) (o : Nat) (b : List Bool) : Bool :=
  (gs.foldl (fun w g => w ++ [gateValue g w]) b).getD o false

def informative {X T : Type} (outside : X → T) (f : X → Bool) (t : T) : Prop :=
  ∃ p n : X, outside p = t ∧ outside n = t ∧ f p = true ∧ f n = false

theorem bool_affine (g : Bool → Bool) (u v : Bool)
    (hu : g u = true) (hv : g v = false) :
    ∀ x, g x = Bool.xor x (g false) := by
  cases a : g false <;> cases b : g true <;> cases u <;> cases v <;>
    intro x <;> cases x <;> simp_all

theorem physicalModule {X S T : Type} (inside : X → S) (outside : X → T)
    (bit : S → Bool) (bank : T → Bool → List Bool) (gs : List Gate)
    (o : Nat) (f : X → Bool)
    (ok : ∀ x, evaluate gs o (bank (outside x) (bit (inside x))) = f x) :
    ∃ sign : T → Bool, ∀ x, informative outside f (outside x) →
      f x = Bool.xor (bit (inside x)) (sign (outside x)) := by
  refine ⟨fun t => evaluate gs o (bank t false), ?_⟩
  intro x h
  obtain ⟨p,n,ep,en,hp,hn⟩ := h
  let g := fun b => evaluate gs o (bank (outside x) b)
  have ap : g (bit (inside p)) = true := by
    dsimp [g]
    rw [← ep, ok p, hp]
  have an : g (bit (inside n)) = false := by
    dsimp [g]
    rw [← en, ok n, hn]
  exact (ok x).symm.trans (bool_affine g _ _ ap an _)

theorem threeConflicts {S T : Type} (h : S → Bool) (g : T → Bool → Bool)
    (a b c : S) (r s t : T)
    (ab : g r (h a) ≠ g r (h b)) (bc : g s (h b) ≠ g s (h c))
    (ca : g t (h c) ≠ g t (h a)) : False := by
  cases ha : h a <;> cases hb : h b <;> cases hc : h c <;> simp_all

end PEqualNP.Outside.L_meta_9809.Modules

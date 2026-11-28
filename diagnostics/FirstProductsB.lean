import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9792.Products

inductive Site (X : Type) where
  | raw (value : X → Prop)
  | meet (a b : Nat)
  | join (a b : Nat)

def Site.atVal {X : Type} (v : Nat → X → Prop) : Site X → X → Prop
  | .raw p,x => p x
  | .meet a b,x => v a x ∧ v b x
  | .join a b,x => v a x ∨ v b x

def Site.earlier {X : Type} (i : Nat) : Site X → Prop
  | .raw _ => True
  | .meet a b => (a < i) ∧ (b < i)
  | .join a b => (a < i) ∧ (b < i)

variable {X : Type}
def sufficient (F : X → Prop) (v : Nat → X → Prop) (i : Nat) :=
  ∀x, v i x → F x

def emitted (F : X → Prop) (v w : Nat → X → Prop) (k : Nat → Site X) (x : X) :=
  ∃i a b, k i=.meet a b ∧ sufficient F v i ∧
    ¬sufficient F v a ∧ ¬sufficient F v b ∧ w a x ∧ w b x

/-- Simultaneously clamp all sufficient wires to false. For an arbitrary physical
order, the target is exactly the disjunction of the first sufficient products. -/
theorem firstProducts (F : X → Prop) (v w : Nat → X → Prop) (k : Nat → Site X)
    (str : ∀i,(k i).earlier i)
    (raw : ∀i p, k i=.raw p → ¬sufficient F v i)
    (valEq : ∀i x, v i x ↔ (k i).atVal v x)
    (clip : ∀i x, w i x ↔ ¬sufficient F v i ∧ (k i).atVal w x)
    (root : Nat) (correct : ∀x, F x ↔ v root x) (x : X) :
    F x ↔ emitted F v w k x := by
  classical
  have sub (i : Nat) : w i x → v i x := by
    induction i using Nat.strong_induction_on with
    | ind i ih =>
      intro hi
      have hh := ((clip i x).mp hi).2
      apply (valEq i x).mpr
      have ss := str i
      cases eq : k i with
      | raw p => simpa [eq,Site.atVal] using hh
      | meet a b =>
        simp only [eq,Site.atVal,Site.earlier] at hh ss ⊢
        exact ⟨ih a ss.1 hh.1,ih b ss.2 hh.2⟩
      | join a b =>
        simp only [eq,Site.atVal,Site.earlier] at hh ss ⊢
        exact hh.imp (ih a ss.1) (ih b ss.2)
  have hit (i : Nat) : v i x → w i x ∨ emitted F v w k x := by
    induction i using Nat.strong_induction_on with
    | ind i ih =>
      intro hv
      have hh := (valEq i x).mp hv
      have ss := str i
      cases eq : k i with
      | raw p =>
        exact Or.inl ((clip i x).mpr ⟨raw i p eq,by simpa [eq,Site.atVal] using hh⟩)
      | meet a b =>
        simp only [eq,Site.atVal,Site.earlier] at hh ss
        rcases ih a ss.1 hh.1 with wa|done
        · rcases ih b ss.2 hh.2 with wb|done
          · by_cases safe : sufficient F v i
            · exact Or.inr ⟨i,a,b,eq,safe,((clip a x).mp wa).1,((clip b x).mp wb).1,wa,wb⟩
            · exact Or.inl ((clip i x).mpr ⟨safe,by simpa [eq,Site.atVal] using And.intro wa wb⟩)
          · exact Or.inr done
        · exact Or.inr done
      | join a b =>
        simp only [eq,Site.atVal,Site.earlier] at hh ss
        have joined : w a x ∨ w b x ∨ emitted F v w k x := by
          rcases hh with h|h
          · exact (ih a ss.1 h).imp id Or.inr
          · exact Or.inr (ih b ss.2 h)
        rcases joined with wa|wb|done
        · have ns : ¬sufficient F v i := fun hs => ((clip a x).mp wa).1 (fun z hz =>
            hs z ((valEq i z).mpr (by simpa [eq,Site.atVal] using (Or.inl hz : v a z ∨ v b z))))
          exact Or.inl ((clip i x).mpr ⟨ns,by simpa [eq,Site.atVal] using (Or.inl wa : w a x ∨ w b x)⟩)
        · have ns : ¬sufficient F v i := fun hs => ((clip b x).mp wb).1 (fun z hz =>
            hs z ((valEq i z).mpr (by simpa [eq,Site.atVal] using (Or.inr hz : v a z ∨ v b z))))
          exact Or.inl ((clip i x).mpr ⟨ns,by simpa [eq,Site.atVal] using (Or.inr wb : w a x ∨ w b x)⟩)
        · exact Or.inr done
  constructor
  · intro hf
    rcases hit root ((correct x).mp hf) with wr|done
    · exact (((clip root x).mp wr).1 (fun y => (correct y).mpr)).elim
    · exact done
  · rintro ⟨i,a,b,eq,safe,_,_,wa,wb⟩
    exact safe x ((valEq i x).mpr (by simpa [eq,Site.atVal] using And.intro (sub a wa) (sub b wb)))

end PEqualNP.Outside.L_meta_9792.Products

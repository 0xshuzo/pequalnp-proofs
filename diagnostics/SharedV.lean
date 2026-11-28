import PEqualNP.Defs

namespace Research9755.SharedV
abbrev M := BitVec 4
abbrev Ext := BitVec 6
def graph (x : Fin 10 → Bool) := (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 1 && x 6) || (x 2 && x 3) || (x 2 && x 7) || (x 3 && x 4) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 5 && x 8) || (x 6 && x 8) || (x 6 && x 9) || (x 7 && x 9)
def pins (c : Ext) (t : M) : Fin 10 → Bool :=
  ![t.getLsbD 0,t.getLsbD 1,t.getLsbD 2,c.getLsbD 0,c.getLsbD 1,
    c.getLsbD 4,t.getLsbD 3,c.getLsbD 3,c.getLsbD 5,c.getLsbD 2]
def val (c : Ext) (t : M) := graph (pins c t)
def split (m a b : M) := (m &&& a) ||| ((~~~m) &&& b)
def separates (m : M) : Bool :=
  (m.getLsbD 1 != m.getLsbD 2) && (m.getLsbD 1 != m.getLsbD 3)
def witness (c : Ext) (m a b d : M) (s t : M) : Bool :=
  let x : M → Bool × Bool := fun i => (val c (split m i s),val c (split m i t))
  (x a != x b) && (x b != x d) && (x d != x a)
def Blocks (m : M) := ∀ c : Ext,∃ h : M→Bool,∃ k : Bool→M→Bool,
  ∀ a b : M,val c (split m a b)=k (h a) b
theorem forbid (m a b d s t : M) (c : Ext) (hit : witness c m a b d s t=true) : ¬Blocks m := by
  intro blk
  obtain ⟨h,k,eq⟩ := blk c
  simp only [witness,eq] at hit
  cases e : h a <;> cases f : h b <;> cases g : h d <;> simp [e,f,g] at hit
theorem onlyV (m : M) (sep : separates m=true) (blk : Blocks m) : m=2 := by
  have pick : ∀ x : M, separates x=true → x=2 ∨ x=3 ∨ x=12 ∨ x=13 := by decide +kernel
  rcases pick m sep with eq|eq|eq|eq
  · exact eq
  · subst m
    exact (forbid 3 12 15 14 0 4 2 (by decide +kernel) blk).elim
  · subst m
    exact (forbid 12 3 15 11 0 2 1 (by decide +kernel) blk).elim
  · subst m
    exact (forbid 13 2 15 14 0 2 2 (by decide +kernel) blk).elim
end Research9755.SharedV

import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9809.Suffix

inductive Tree (I : Type)
  | leaf (i : I)
  | meet (a b : Tree I)
  | join (a b : Tree I)

def Tree.uses {I : Type} (t : Tree I) (i : I) : Prop :=
  match t with
  | .leaf j => i = j
  | .meet a b | .join a b => a.uses i ∨ b.uses i

def Tree.unique {I : Type} (t : Tree I) : Prop :=
  match t with
  | .leaf _ => True
  | .meet a b | .join a b =>
    a.unique ∧ b.unique ∧ ∀ i, a.uses i → b.uses i → False

def Tree.eval {I : Type} (t : Tree I) (v : I → Bool) : Bool :=
  match t with
  | .leaf i => v i
  | .meet a b => a.eval v && b.eval v
  | .join a b => a.eval v || b.eval v

def Tree.pick {I : Type} (t : Tree I) (p n : I → Bool) : I :=
  match t with
  | .leaf i => i
  | .meet a b => if a.eval n = false then a.pick p n else b.pick p n
  | .join a b => if a.eval p = true then a.pick p n else b.pick p n

theorem Tree.pick_uses {I : Type} (t : Tree I) (p n : I → Bool) :
    t.uses (t.pick p n) := by
  induction t with
  | leaf i => rfl
  | meet a b ha hb =>
    simp only [Tree.uses, Tree.pick]
    split
    · exact Or.inl ha
    · exact Or.inr hb
  | join a b ha hb =>
    simp only [Tree.uses, Tree.pick]
    split
    · exact Or.inl ha
    · exact Or.inr hb

theorem Tree.pick_sep {I : Type} (t : Tree I) (p n : I → Bool)
    (hp : t.eval p = true) (hn : t.eval n = false) :
    p (t.pick p n) = true ∧ n (t.pick p n) = false := by
  induction t with
  | leaf i => exact ⟨hp,hn⟩
  | meet a b ha hb =>
    cases ap : a.eval p <;> cases bp : b.eval p <;>
      cases an : a.eval n <;> cases bn : b.eval n <;>
      simp_all [Tree.eval, Tree.pick]
  | join a b ha hb =>
    cases ap : a.eval p <;> cases bp : b.eval p <;>
      cases an : a.eval n <;> cases bn : b.eval n <;>
      simp_all [Tree.eval, Tree.pick]

theorem Tree.rectangle {I : Type} (t : Tree I) (h : t.unique) (i : I)
    (p q n m : I → Bool) (hp : t.pick p n = i) (hq : t.pick q m = i) :
    t.pick p m = i := by
  induction t with
  | leaf j => exact hp
  | meet a b ha hb =>
    obtain ⟨ua,ub,dis⟩ := h
    by_cases h1 : a.eval n = false <;> by_cases h2 : a.eval m = false
    · simp only [Tree.pick, if_pos h1, if_pos h2] at hp hq ⊢
      exact ha ua hp hq
    · simp only [Tree.pick, if_pos h1, if_neg h2] at hp hq ⊢
      exact (dis i (hp ▸ a.pick_uses p n) (hq ▸ b.pick_uses q m)).elim
    · simp only [Tree.pick, if_neg h1, if_pos h2] at hp hq ⊢
      exact (dis i (hq ▸ a.pick_uses q m) (hp ▸ b.pick_uses p n)).elim
    · simp only [Tree.pick, if_neg h1, if_neg h2] at hp hq ⊢
      exact hb ub hp hq
  | join a b ha hb =>
    obtain ⟨ua,ub,dis⟩ := h
    by_cases h1 : a.eval p = true <;> by_cases h2 : a.eval q = true
    · simp only [Tree.pick, if_pos h1, if_pos h2] at hp hq ⊢
      exact ha ua hp hq
    · simp only [Tree.pick, if_pos h1, if_neg h2] at hp hq ⊢
      exact (dis i (hp ▸ a.pick_uses p n) (hq ▸ b.pick_uses q m)).elim
    · simp only [Tree.pick, if_neg h1, if_pos h2] at hp hq ⊢
      exact (dis i (hq ▸ a.pick_uses q m) (hp ▸ b.pick_uses p n)).elim
    · simp only [Tree.pick, if_neg h1, if_neg h2] at hp hq ⊢
      exact hb ub hp hq

def forced {I : Type} (p n : I → Bool) (i : I) : Prop :=
  ∀ j, p j = true → n j = false → j = i

theorem Tree.private_pick {I : Type} (t : Tree I) {p n : I → Bool} {i : I}
    (hp : t.eval p = true) (hn : t.eval n = false) (h : forced p n i) :
    t.pick p n = i := by
  obtain ⟨a,b⟩ := t.pick_sep p n hp hn
  exact h _ a b

theorem Tree.private_overlap {I : Type} (t : Tree I) (h : t.unique) {i j : I}
    {a b c x y z : I → Bool}
    (ha : t.eval a = true) (hb : t.eval b = true) (hc : t.eval c = true)
    (hx : t.eval x = false) (hy : t.eval y = false) (hz : t.eval z = false)
    (ax : forced a x i) (byi : forced b y i)
    (az : forced a z j) (cy : forced c y j) :
    i = j := by
  have first := t.rectangle h i a b x y (t.private_pick ha hx ax) (t.private_pick hb hy byi)
  have second := t.rectangle h j a c z y (t.private_pick ha hz az) (t.private_pick hc hy cy)
  exact first.symm.trans second

end PEqualNP.Outside.L_meta_9809.Suffix

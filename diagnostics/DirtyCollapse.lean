import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9829.DirtyCollapse
variable {P L : Type}
def fire (G : P → L → Prop) (x : Set P) (y : Set L) := ∃ p ∈ x, ∃ l ∈ y, G p l
def sqFree (G : P → L → Prop) := ∀ p q l r, G p l → G p r → G q l → G q r → p=q ∨ l=r
def missing (G B : P → L → Prop) (p : P) (l : L) := G p l ∧ ¬ B p l
def mono (H : Set P → Set L → Prop) :=
  ∀ x y x' y', x ⊆ x' → y ⊆ y' → H x y → H x' y'
def veto (G B : P → L → Prop) (H W : Set P → Set L → Prop) :=
  ∀ x y, fire G x y ↔ fire B x y ∨ (¬ H x y ∧ W x y)

theorem onBad {G B : P → L → Prop} {H W : Set P → Set L → Prop}
    (fact : veto G B H W) {p l} (off : ¬G p l) (fires : W {p} {l}) : H {p} {l} := by
  classical
  by_contra neg
  obtain ⟨a,ha,b,hb,inc⟩ := (fact _ _).mpr (Or.inr ⟨neg,fires⟩)
  obtain rfl := Set.mem_singleton_iff.mp ha
  obtain rfl := Set.mem_singleton_iff.mp hb
  exact off inc

theorem wall {G B : P → L → Prop} {H W : Set P → Set L → Prop}
    (m : mono H) (fact : veto G B H W) (sub : ∀ p l, B p l → G p l)
    {u v} (bad : ¬G u v) (wu : W {u} {v}) :
    (∀ l, G u l → B u l) ∧ (∀ p, G p v → B p v) := by
  classical
  have force := onBad fact bad wu
  constructor
  · intro l yes
    have ht : H {u} {v,l} := m _ _ _ _ (by rfl) (by simp) force
    have on : fire G {u} {v,l} := ⟨u,by simp,l,by simp,yes⟩
    rcases (fact _ _).mp on with ⟨p,hp,r,hr,keep⟩|⟨no,_⟩
    · obtain rfl := Set.mem_singleton_iff.mp hp
      rcases (show r=v ∨ r=l by simpa using hr) with rfl|rfl
      · exact False.elim (bad (sub _ _ keep))
      · exact keep
    · exact False.elim (no ht)
  · intro p yes
    have ht : H {u,p} {v} := m _ _ _ _ (by simp) (by rfl) force
    have on : fire G {u,p} {v} := ⟨p,by simp,v,by simp,yes⟩
    rcases (fact _ _).mp on with ⟨a,ha,r,hr,keep⟩|⟨no,_⟩
    · obtain rfl := Set.mem_singleton_iff.mp hr
      rcases (show a=u ∨ a=p by simpa using ha) with rfl|rfl
      · exact False.elim (bad (sub _ _ keep))
      · exact keep
    · exact False.elim (no ht)

theorem dirtyOne {G B : P → L → Prop} {H W : Set P → Set L → Prop}
    (sq : sqFree G) (m : mono H) (fact : veto G B H W) (sub : ∀ p l, B p l → G p l)
    {A : Set P} {S : Set L} (rect : ∀ p ∈ A, ∀ l ∈ S, W {p} {l})
    {u v} (hu : u ∈ A) (hv : v ∈ S) (bad : ¬ G u v)
    {p q l r} (pa : p ∈ A) (qa : q ∈ A) (ls : l ∈ S) (rs : r ∈ S)
    (e : missing G B p l) (f : missing G B q r) : p=q ∧ l=r := by
  classical
  have row {a b} (aa : a ∈ A) (ab : missing G B a b) (j : L) (jj : j ∈ S) : G a j := by
    by_contra gap
    exact ab.2 ((wall m fact sub gap (rect a aa j jj)).1 b ab.1)
  have col {a b} (bb : b ∈ S) (ab : missing G B a b) (i : P) (ii : i ∈ A) : G i b := by
    by_contra gap
    exact ab.2 ((wall m fact sub gap (rect i ii b bb)).2 a ab.1)
  have lv : l ≠ v := by
    intro eq
    apply bad
    simpa only [←eq] using col ls e u hu
  have pu : p ≠ u := by
    intro eq
    apply bad
    simpa only [←eq] using row pa e v hv
  constructor
  · exact (sq p q l v e.1 (row pa e v hv) (row qa f l ls) (row qa f v hv)).resolve_right lv
  · exact (sq p u l r e.1 (row pa e r rs) (col ls e u hu) (col rs f u hu)).resolve_left pu

end PEqualNP.Outside.L_meta_9829.DirtyCollapse

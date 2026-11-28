import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9829.Veto
variable {P L : Type}
def fire (G : P → L → Prop) (x : Set P) (y : Set L) :=
  ∃ p ∈ x, ∃ l ∈ y, G p l
def c4free (G : P → L → Prop) :=
  ∀ p q l r, G p l → G p r → G q l → G q r → p=q ∨ l=r
def missed (G B : P → L → Prop) (p : P) (l : L) := G p l ∧ ¬ B p l

theorem vetoPencil {G B : P → L → Prop} {H W : Set P → Set L → Prop}
    (factor : ∀ x y, fire G x y ↔ fire B x y ∨ (¬ H x y ∧ W x y))
    {u : P} (tag : ∀ x y, u ∈ x → H x y) {p l} (e : missed G B p l) :
    B u l := by
  classical
  have hit : fire G {p,u} {l} := ⟨p,by simp,l,by simp,e.1⟩
  rcases (factor _ _).mp hit with ⟨z,hz,k,hk,keep⟩|⟨off,_⟩
  · obtain rfl := Set.mem_singleton_iff.mp hk
    rcases (show z=p ∨ z=u by simpa using hz) with rfl|rfl
    · exact False.elim (e.2 keep)
    · exact keep
  · exact False.elim (off (tag _ _ (by simp)))

theorem uniqueLine {G B : P → L → Prop} {u : P}
    (sub : ∀ p l, B p l → G p l) (sq : c4free G)
    (pencil : ∀ p l, missed G B p l → B u l)
    {p q l r} (e : missed G B p l) (f : missed G B q r) (cross : G p r) :
    l=r := by
  have ne : p ≠ u := by
    intro eq
    exact e.2 (by simpa only [eq] using pencil p l e)
  exact (sq p u l r e.1 cross (sub _ _ (pencil p l e))
    (sub _ _ (pencil q r f))).resolve_left ne

theorem cleanPair {G B : P → L → Prop} (sub : ∀ p l, B p l → G p l)
    (sq : c4free G) {p q l r}
    (ep : missed G B p l) (eq : missed G B q l) (ap : B p r) (aq : B q r) :
    p=q := by
  rcases sq p q l r ep.1 (sub _ _ ap) eq.1 (sub _ _ aq) with same|same
  · exact same
  · exact False.elim (ep.2 (by simpa only [same] using ap))

theorem emptyExterior {G B : P → L → Prop} {u : P}
    (sub : ∀ p l, B p l → G p l) (sq : c4free G)
    (pencil : ∀ p l, missed G B p l → B u l)
    {x : Set P} {y : Set L} (xs : ∀ p ∈ x, ∃ l, missed G B p l)
    (ys : ∀ r ∈ y, ∃ q, missed G B q r) : ¬ fire B x y := by
  rintro ⟨p,hp,r,hr,live⟩
  obtain ⟨l,ep⟩ := xs p hp
  obtain ⟨q,eq⟩ := ys r hr
  have same := uniqueLine sub sq pencil ep eq (sub _ _ live)
  exact ep.2 (by simpa only [same] using live)

end PEqualNP.Outside.L_meta_9829.Veto

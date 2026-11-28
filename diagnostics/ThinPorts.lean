import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_9792.Guard
variable {P L : Type}
def edgeOn (G : P → L → Prop) (x : Set P) (y : Set L) :=
  ∃p∈x,∃l∈y,G p l
def positive {T : Type} (f : Set T → Prop) := ∀x y,x⊆y → f x → f y
def bright {T : Type} (f : Set T → Prop) (t : T) := f {t}
def hits {T : Type} (S x : Set T) := ∃t∈S,t∈x
def safe (G : P → L → Prop) (U : Set P) (V : Set L)
    (a : Set P → Prop) (b : Set L → Prop) :=
  ∀x y,a x → b y → (hits U x ∨ hits V y) → edgeOn G x y

theorem dirtyPartners {G : P → L → Prop} {U : Set P} {V : Set L}
    {a : Set P → Prop} {b : Set L → Prop} (ma : positive a) (mb : positive b)
    (ok : safe G U V a b) {p : P} {l : L}
    (ap : bright a p) (bl : bright b l) (no : ¬G p l) :
    (∀u∈U,G u l) ∧ (∀v∈V,G p v) := by
  classical
  constructor
  · intro u hu
    obtain ⟨w,wm,k,km,e⟩ := ok {p,u} {l}
      (ma _ _ (by intro z hz; simpa using (Or.inl (Set.mem_singleton_iff.mp hz) : z=p ∨ z=u)) ap)
      bl (Or.inl ⟨u,hu,by simp⟩)
    obtain rfl := Set.mem_singleton_iff.mp km
    rcases (show w=p ∨ w=u by simpa using wm) with rfl|rfl
    · exact False.elim (no e)
    · exact e
  · intro v hv
    obtain ⟨w,wm,k,km,e⟩ := ok {p} {l,v} ap
      (mb _ _ (by intro z hz; simpa using (Or.inl (Set.mem_singleton_iff.mp hz) : z=l ∨ z=v)) bl)
      (Or.inr ⟨v,hv,by simp⟩)
    obtain rfl := Set.mem_singleton_iff.mp wm
    rcases (show k=l ∨ k=v by simpa using km) with rfl|rfl
    · exact False.elim (no e)
    · exact e

def SquareFree (G : P → L → Prop) := ∀p q l r,G p l → G p r → G q l → G q r → p=q ∨ l=r
def two {T : Type} (S : Set T) := ∃x∈S,∃y∈S,x≠y
theorem sharedGap {G : P → L → Prop} (sq : SquareFree G)
    {U : Set P} {V : Set L} {p q : P} {l r : L}
    (h1 : (∀u∈U,G u l) ∧ (∀v∈V,G p v))
    (h2 : (∀u∈U,G u r) ∧ (∀v∈V,G q v)) :
    (two U → l=r) ∧ (two V → p=q) := by
  constructor
  · rintro ⟨x,hx,y,hy,diff⟩
    exact (sq x y l r (h1.1 _ hx) (h2.1 _ hx) (h1.1 _ hy) (h2.1 _ hy)).resolve_left diff
  · rintro ⟨x,hx,y,hy,diff⟩
    exact (sq p q x y (h1.2 _ hx) (h1.2 _ hy) (h2.2 _ hx) (h2.2 _ hy)).resolve_right diff

theorem rectangleSafe {G : P → L → Prop} (U : Set P) (V : Set L) (A : Set P) (B : Set L) :
    safe G U V (hits A) (hits B) ↔
      ∀p∈A,∀l∈B, ¬G p l → (∀u∈U,G u l) ∧ (∀v∈V,G p v) := by
  classical
  constructor
  · intro ok p hp l hl no
    have mh {T : Type} (S : Set T) : positive (hits S) := by
      rintro x y sub ⟨t,m,h⟩
      exact ⟨t,m,sub h⟩
    exact dirtyPartners (mh A) (mh B) ok ⟨p,hp,by simp⟩ ⟨l,hl,by simp⟩ no
  · rintro guard x y ⟨p,hp,px⟩ ⟨l,hl,ly⟩ trigger
    by_cases inc : G p l
    · exact ⟨p,px,l,ly,inc⟩
    obtain ⟨us,vs⟩ := guard p hp l hl inc
    rcases trigger with ⟨u,hu,ux⟩|⟨v,hv,vy⟩
    · exact ⟨u,ux,l,ly,us u hu⟩
    · exact ⟨p,px,v,vy,vs v hv⟩

theorem thinSupport {G : P → L → Prop} (sq : SquareFree G)
    {p : P} {B : Set L} {U : Set P} {V : Set L}
    (ok : safe G U V (hits {p}) (hits B))
    {u : P} (tag : u ∈ U) {bad : L} (inB : bad ∈ B) (gap : ¬G p bad)
    {l r : L} (lin : l ∈ B) (rin : r ∈ B) (li : G p l) (ri : G p r) (ne : l ≠ r) :
    (p ≠ u) ∧ (∀ s ∈ B, G p s ∨ G u s) ∧ ¬ (∃ q, ∀ s ∈ B, G q s) := by
  have sufficient := (rectangleSafe U V {p} B).mp ok
  have pointIn : p ∈ ({p} : Set P) := by simp
  have badEdge := (sufficient p pointIn bad inB gap).1 u tag
  refine ⟨?_,?_,?_⟩
  · intro e
    exact gap (e.symm ▸ badEdge)
  · intro s hs
    by_cases h : G p s
    · exact Or.inl h
    · exact Or.inr ((sufficient p pointIn s hs h).1 u tag)
  · rintro ⟨q,h⟩
    have eq := (sq p q l r li ri (h l lin) (h r rin)).resolve_right ne
    exact gap (eq.symm ▸ h bad inB)

end PEqualNP.Outside.L_meta_9792.Guard

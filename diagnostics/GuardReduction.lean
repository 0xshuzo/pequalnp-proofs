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

def onPair (U : Set P) (V : Set L) (A : Set P) (B : Set L) (p : P) (l : L) :=
  p ∈ A ∧ l ∈ B ∧ (p ∈ U ∨ l ∈ V)

theorem starReplacement {G : P → L → Prop} {U : Set P} {V : Set L}
    {A : Set P} {B : Set L} {center : P}
    (ok : safe G U V (hits A) (hits B))
    (present : center ∈ A)
    (atCenter : ∀ p l, onPair U V A B p l → p = center) :
    ∃ S : Set L, (S = B ∨ S = V) ∧ (∀ l ∈ S, G center l) ∧
      (∀ p l, onPair U V A B p l → p = center ∧ l ∈ S) := by
  classical
  by_cases clean : ∀ l ∈ B, G center l
  · exact ⟨B,Or.inl rfl,clean,fun p l h => ⟨atCenter p l h,h.2.1⟩⟩
  · obtain ⟨bad,inB,missing⟩ : ∃ l ∈ B, ¬G center l := by
      by_contra h
      apply clean
      intro l hl
      by_contra missing
      exact h ⟨l,hl,missing⟩
    have h := (rectangleSafe U V A B).mp ok center present bad inB missing
    have untagged : center ∉ U := fun tag => missing (h.1 center tag)
    refine ⟨V,Or.inr rfl,h.2,?_⟩
    intro p l pair
    have eq := atCenter p l pair
    obtain rfl := eq
    exact ⟨rfl,pair.2.2.resolve_left untagged⟩

theorem pairMerge {U : Set P} {V : Set L} {A C : Set P} {B D : Set L}
    {p : P} {l : L} :
    (onPair U V A B p l ∨ onPair U V C D p l) →
      onPair U V (A ∪ C) (B ∪ D) p l := by
  rintro (⟨x,y,t⟩|⟨x,y,t⟩)
  · exact ⟨Or.inl x,Or.inl y,t⟩
  · exact ⟨Or.inr x,Or.inr y,t⟩

end PEqualNP.Outside.L_meta_9792.Guard

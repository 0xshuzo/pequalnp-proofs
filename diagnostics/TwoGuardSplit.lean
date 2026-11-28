import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_9792.TwoGuard

theorem distribute (privateA privateB common tagA tagB : Prop) :
    (((privateA ∨ common) ∧ tagA) ∨ ((privateB ∨ common) ∧ tagB)) ↔
    ((privateA ∧ tagA) ∨ (privateB ∧ tagB) ∨ (common ∧ (tagA ∨ tagB))) := by
  constructor
  · rintro (⟨ha,ht⟩|⟨hb,ht⟩)
    · rcases ha with h|h
      · exact Or.inl ⟨h,ht⟩
      · exact Or.inr (Or.inr ⟨h,Or.inl ht⟩)
    · rcases hb with h|h
      · exact Or.inr (Or.inl ⟨h,ht⟩)
      · exact Or.inr (Or.inr ⟨h,Or.inr ht⟩)
  · rintro (⟨h,ht⟩|⟨h,ht⟩|⟨h,ha|hb⟩)
    · exact Or.inl ⟨Or.inl h,ht⟩
    · exact Or.inr ⟨Or.inl h,ht⟩
    · exact Or.inl ⟨Or.inr h,ha⟩
    · exact Or.inr ⟨Or.inr h,hb⟩

variable {P L : Type}
def squareFree (G : P → L → Prop) := ∀ p q l r, G p l → G p r → G q l → G q r → p=q ∨ l=r
def atLeastTwo {T : Type} (S : Set T) := ∃ a ∈ S, ∃ b ∈ S, a ≠ b
def accepted (A : Set P) (B : Set L) (U : Set P) (V : Set L) (p : P) (l : L) :=
  p ∈ A ∧ l ∈ B ∧ (p ∈ U ∨ l ∈ V)

theorem uniquePoint {G : P → L → Prop} (sq : squareFree G) {B : Set L}
    (hb : atLeastTwo B) {p q : P} (fp : ∀l∈B, G p l) (fq : ∀l∈B, G q l) : p=q := by
  obtain ⟨l,m,r,n,ne⟩ := hb
  exact (sq p q l r (fp l m) (fp r n) (fq l m) (fq r n)).resolve_right ne
theorem uniqueLine {G : P → L → Prop} (sq : squareFree G) {A : Set P}
    (ha : atLeastTwo A) {l r : L} (fl : ∀p∈A, G p l) (fr : ∀p∈A, G p r) : l=r := by
  obtain ⟨p,m,q,n,ne⟩ := ha
  exact (sq p q l r (fl p m) (fr p m) (fl q n) (fr q n)).resolve_left ne

theorem intrinsic {G : P → L → Prop} (sq : squareFree G)
    {A : Set P} {B : Set L} (ha : atLeastTwo A) (hb : atLeastTwo B)
    {U : Set P} {V : Set L} (ok : ∀p l, accepted A B U V p l → G p l)
    (hasPoint : ∃p∈A,p∈U) (hasLine : ∃l∈B,l∈V) (p : P) (l : L) :
    accepted A B U V p l ↔ p∈A ∧ l∈B ∧ ((∀ r ∈ B, G p r) ∨ (∀ q ∈ A, G q l)) := by
  obtain ⟨pa,paA,paU⟩ := hasPoint
  obtain ⟨la,laB,laV⟩ := hasLine
  constructor
  · rintro ⟨pA,lB,pU|lV⟩
    · exact ⟨pA,lB,Or.inl (fun r hr => ok p r ⟨pA,hr,Or.inl pU⟩)⟩
    · exact ⟨pA,lB,Or.inr (fun q hq => ok q l ⟨hq,lB,Or.inr lV⟩)⟩
  · rintro ⟨pA,lB,pr|ql⟩
    · have eq := uniquePoint sq hb pr (fun r hr => ok pa r ⟨paA,hr,Or.inl paU⟩)
      exact ⟨pA,lB,Or.inl (eq.symm ▸ paU)⟩
    · have eq := uniqueLine sq ha ql (fun q hq => ok q la ⟨hq,laB,Or.inr laV⟩)
      exact ⟨pA,lB,Or.inr (eq.symm ▸ laV)⟩

end PEqualNP.Outside.L_meta_9792.TwoGuard

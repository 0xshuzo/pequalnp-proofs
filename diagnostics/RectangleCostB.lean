import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17257

abbrev Vec (N : ℕ) := Fin N → Bool
abbrev Board (N : ℕ) := Vec N × Vec N
abbrev Bank (α : Type*) := ℕ → Set α

def Steps {α : Type*} (W : Bank α) (n s : ℕ) := ∀ j<s,
  ∃ a<n+j, ∃ b<n+j, W (n+j)=W a∪W b ∨ W (n+j)=W a ∨ W (n+j)=∅ ∨ W (n+j)=W a∩W b

def UnionAt {α : Type*} (W : Bank α) (n j : ℕ) := ∃ a<n+j, ∃ b<n+j, W (n+j)=W a∪W b


namespace Rectangle

variable {α ι κ : Type*}

def Covers (X : ι → α) (Y : κ → α) (W : Set α) (A : Set ι) (B : Set κ) : Prop :=
  (∀ u∈A,X u∈W) ∧ ∀ v∈B,Y v∉W

def Moves (A : ℕ → Set ι) (B : ℕ → Set κ) (n s : ℕ) : Prop :=
  ∀ j<s, ∃ a<n+j, ∃ b<n+j,
    (A (n+j) ⊆ A a∪A b ∧ B (n+j) ⊆ B a∩B b) ∨
    (A (n+j) ⊆ A a∩A b ∧ B (n+j) ⊆ B a∪B b) ∨
    (A (n+j) ⊆ A a ∧ B (n+j) ⊆ B a) ∨ A (n+j)=∅

theorem lower_of_moves (X : ι → α) (Y : κ → α) (R : ℕ → Set α)
    (A : ℕ → Set ι) (B : ℕ → Set κ) (n s : ℕ)
    (raw : ∀ w<n,Covers X Y (R w) (A w) (B w)) (hs : Moves A B n s) :
    ∃ W : Bank α, (∀ w<n,W w=R w) ∧ Steps W n s ∧
      ∀ w<n+s,Covers X Y (W w) (A w) (B w) := by
  classical
  induction s with
  | zero =>
    exact ⟨R,fun _ _ => rfl,fun _ h => (Nat.not_lt_zero _ h).elim,by simpa using raw⟩
  | succ s ih =>
    obtain ⟨D,dr,steps,cov⟩ := ih (fun j hj => hs j (Nat.lt_succ_of_lt hj))
    obtain ⟨a,ha,b,hb,jump⟩ := hs s (Nat.lt_succ_self s)
    obtain ⟨ap,an⟩ := cov a ha
    obtain ⟨bp,bn⟩ := cov b hb
    have make : ∃ V : Set α,
        (V=D a∪D b ∨ V=D a ∨ V=∅ ∨ V=D a∩D b) ∧ Covers X Y V (A (n+s)) (B (n+s)) := by
      rcases jump with ⟨l,r⟩|⟨l,r⟩|⟨l,r⟩|e
      · refine ⟨D a∪D b,Or.inl rfl,?_,?_⟩
        · exact fun u hu => (l hu).imp (ap u) (bp u)
        · exact fun v hv h => h.elim (an v (r hv).1) (bn v (r hv).2)
      · refine ⟨D a∩D b,Or.inr (Or.inr (Or.inr rfl)),?_,?_⟩
        · exact fun u hu => ⟨ap u (l hu).1,bp u (l hu).2⟩
        · exact fun v hv h => (r hv).elim (fun z => an v z h.1) (fun z => bn v z h.2)
      · exact ⟨D a,Or.inr (Or.inl rfl),fun u hu => ap u (l hu),fun v hv => an v (r hv)⟩
      · exact ⟨∅,Or.inr (Or.inr (Or.inl rfl)),fun u hu => (e ▸ hu : u∈(∅ : Set ι)).elim,
          fun _ _ h => h⟩
    obtain ⟨V,step,cv⟩ := make
    let W : Bank α := fun w => if w=n+s then V else D w
    have old (w : ℕ) (h : w<n+s) : W w=D w := if_neg (Nat.ne_of_lt h)
    have last : W (n+s)=V := if_pos rfl
    refine ⟨W,fun w hw => (old w (by omega)).trans (dr w hw),?_,?_⟩
    · intro j hj
      by_cases eq : j=s
      · subst j
        exact ⟨a,ha,b,hb,by simpa only [last,old a ha,old b hb] using step⟩
      · obtain ⟨u,hu,v,hv,h⟩ := steps j (by omega)
        refine ⟨u,hu,v,hv,?_⟩
        rw [old (n+j) (by omega),old u (by omega),old v (by omega)]
        exact h
    · intro w hw
      by_cases eq : w=n+s
      · subst w; rwa [last]
      · have lt : w<n+s := by omega
        rw [old w lt]
        exact cov w lt

theorem moves_of_bank (X : ι → α) (Y : κ → α) (W : Bank α) (n s : ℕ) (hs : Steps W n s) :
    Moves (fun w => {u | X u∈W w}) (fun w => {v | Y v∉W w}) n s := by
  intro j hj
  obtain ⟨a,ha,b,hb,h⟩ := hs j hj
  refine ⟨a,ha,b,hb,?_⟩
  dsimp only
  rcases h with e|e|e|e <;> rw [e]
  · exact Or.inl ⟨fun _ h => h,fun _ h => ⟨fun z => h (Or.inl z),fun z => h (Or.inr z)⟩⟩
  · exact Or.inr (Or.inr (Or.inl ⟨fun _ h => h,fun _ h => h⟩))
  · exact Or.inr (Or.inr (Or.inr (by ext; rfl)))
  · refine Or.inr (Or.inl ⟨fun _ h => h,?_⟩)
    intro v h
    by_cases z : Y v∈W a
    · exact Or.inr (fun hb => h ⟨z,hb⟩)
    · exact Or.inl z

theorem exact_size (X : ι → α) (Y : κ → α) (R : Bank α) (n s o : ℕ) (ho : o<n+s) :
    (∃ W : Bank α, (∀ w<n,W w=R w) ∧ Steps W n s ∧ (∀ u,X u∈W o) ∧ (∀ v,Y v∉W o)) ↔
    ∃ (A : ℕ → Set ι) (B : ℕ → Set κ),
      (∀ w<n,Covers X Y (R w) (A w) (B w)) ∧ Moves A B n s ∧
      (∀ u,u∈A o) ∧ (∀ v,v∈B o) := by
  constructor
  · rintro ⟨W,raw,h,p,f⟩
    refine ⟨fun w => {u | X u∈W w},fun w => {v | Y v∉W w},?_,moves_of_bank X Y W n s h,p,f⟩
    intro w hw
    rw [←raw w hw]
    exact ⟨fun _ h => h,fun _ h => h⟩
  · rintro ⟨A,B,raw,h,p,f⟩
    obtain ⟨W,r,t,ct⟩ := lower_of_moves X Y R A B n s raw h
    exact ⟨W,r,t,fun u => (ct o ho).1 u (p u),fun v => (ct o ho).2 v (f v)⟩

end Rectangle

end PEqualNP.Outside.L_meta_17257

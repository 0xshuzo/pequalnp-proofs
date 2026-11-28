import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17257

abbrev Vec (N : ℕ) := Fin N → Bool
abbrev Board (N : ℕ) := Vec N × Vec N
abbrev Bank (α : Type*) := ℕ → Set α

def Steps {α : Type*} (W : Bank α) (n s : ℕ) := ∀ j<s,
  ∃ a<n+j, ∃ b<n+j, W (n+j)=W a∪W b ∨ W (n+j)=W a ∨ W (n+j)=∅ ∨ W (n+j)=W a∩W b

def UnionAt {α : Type*} (W : Bank α) (n j : ℕ) := ∃ a<n+j, ∃ b<n+j, W (n+j)=W a∪W b


namespace Normal
variable {α : Type*}

def Improves (P F A B : Set α) : Prop :=
  (∀ x∈P, x∈A → x∈B) ∧ (∀ x∈F, x∈B → x∈A)

def Split (S A B : Set α) : Prop :=
  (∃ x∈S, x∈A ∧ x∉B) ∧ ∃ x∈S, x∈B ∧ x∉A

def Sharp (P F A B V : Set α) : Prop :=
  V=A ∨ V=B ∨ V=∅ ∨ (V=A∪B ∧ Split P A B) ∨ (V=A∩B ∧ Split F A B)

def Clean (P F : Set α) (W : Bank α) (n s : ℕ) :=
  ∀ j<s, ∃ a<n+j, ∃ b<n+j, Sharp P F (W a) (W b) (W (n+j))

private theorem reflImp (P F A : Set α) : Improves P F A A :=
  ⟨fun _ _ h => h,fun _ _ h => h⟩

private theorem oneUnion {P F A B A' B' : Set α}
    (ha : Improves P F A A') (hb : Improves P F B B') :
    ∃ V, Sharp P F A' B' V ∧ Improves P F (A∪B) V := by
  classical
  by_cases ab : ∀ x∈P, x∈A' → x∈B'
  · refine ⟨B',Or.inr (Or.inl rfl),?_,?_⟩
    · intro x hp hx
      exact hx.elim (fun t => ab x hp (ha.1 x hp t)) (hb.1 x hp)
    · exact fun x hf h => Or.inr (hb.2 x hf h)
  by_cases ba : ∀ x∈P, x∈B' → x∈A'
  · refine ⟨A',Or.inl rfl,?_,?_⟩
    · intro x hp hx
      exact hx.elim (ha.1 x hp) (fun t => ba x hp (hb.1 x hp t))
    · exact fun x hf h => Or.inl (ha.2 x hf h)
  push_neg at ab ba
  refine ⟨A'∪B',Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl,ab,ba⟩))),?_,?_⟩
  · intro x hp hx
    exact hx.imp (ha.1 x hp) (hb.1 x hp)
  · intro x hf hx
    exact hx.imp (ha.2 x hf) (hb.2 x hf)

private theorem oneInter {P F A B A' B' : Set α}
    (ha : Improves P F A A') (hb : Improves P F B B') :
    ∃ V, Sharp P F A' B' V ∧ Improves P F (A∩B) V := by
  classical
  by_cases ab : ∀ x∈F, x∈A' → x∈B'
  · exact ⟨A',Or.inl rfl,fun x hp h => ha.1 x hp h.1,
      fun x hf h => ⟨ha.2 x hf h,hb.2 x hf (ab x hf h)⟩⟩
  by_cases ba : ∀ x∈F, x∈B' → x∈A'
  · exact ⟨B',Or.inr (Or.inl rfl),fun x hp h => hb.1 x hp h.2,
      fun x hf h => ⟨ha.2 x hf (ba x hf h),hb.2 x hf h⟩⟩
  push_neg at ab ba
  exact ⟨A'∩B',Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl,ab,ba⟩))),
    fun x hp h => ⟨ha.1 x hp h.1,hb.1 x hp h.2⟩,
    fun x hf h => ⟨ha.2 x hf h.1,hb.2 x hf h.2⟩⟩

theorem normalize (W : Bank α) (n s : ℕ) (P F : Set α) (steps : Steps W n s) :
    ∃ D : Bank α, (∀ i<n,D i=W i) ∧ Clean P F D n s ∧
      ∀ w<n+s, Improves P F (W w) (D w) := by
  classical
  induction s with
  | zero =>
    exact ⟨W,fun _ _ => rfl,fun _ h => (Nat.not_lt_zero _ h).elim,
      fun w _ => reflImp P F (W w)⟩
  | succ s ih =>
    obtain ⟨D,raw,clean,imp⟩ := ih (fun j hj => steps j (Nat.lt_succ_of_lt hj))
    obtain ⟨a,ha,b,hb,eq⟩ := steps s (Nat.lt_succ_self s)
    have hv : ∃ V, Sharp P F (D a) (D b) V ∧ Improves P F (W (n+s)) V := by
      rcases eq with e|e|e|e <;> rw [e]
      · exact oneUnion (imp a ha) (imp b hb)
      · exact ⟨D a,Or.inl rfl,imp a ha⟩
      · exact ⟨∅,Or.inr (Or.inr (Or.inl rfl)),reflImp P F ∅⟩
      · exact oneInter (imp a ha) (imp b hb)
    obtain ⟨V,hV,iv⟩ := hv
    let E : Bank α := fun w => if w=n+s then V else D w
    have old (w : ℕ) (hw : w<n+s) : E w=D w := if_neg (Nat.ne_of_lt hw)
    have last : E (n+s)=V := if_pos rfl
    refine ⟨E,fun w hw => (old w (by omega)).trans (raw w hw),?_,?_⟩
    · intro j hj
      by_cases eq : j=s
      · subst j
        exact ⟨a,ha,b,hb,by simpa only [old a ha,old b hb,last] using hV⟩
      · have lt : j<s := by omega
        obtain ⟨u,hu,v,hv,h⟩ := clean j lt
        refine ⟨u,hu,v,hv,?_⟩
        rw [old u (by omega),old v (by omega),old (n+j) (by omega)]
        exact h
    · intro w hw
      by_cases e : w=n+s
      · subst w; rwa [last]
      · have lt : w<n+s := by omega
        rw [old w lt]
        exact imp w lt

theorem forget {P F : Set α} {D : Bank α} {n s : ℕ} (clean : Clean P F D n s) :
    Steps D n s := by
  intro j hj
  obtain ⟨a,ha,b,hb,h⟩ := clean j hj
  rcases h with e|e|e|⟨e,_⟩|⟨e,_⟩
  · exact ⟨a,ha,b,hb,Or.inr (Or.inl e)⟩
  · exact ⟨b,hb,a,ha,Or.inr (Or.inl e)⟩
  · exact ⟨a,ha,b,hb,Or.inr (Or.inr (Or.inl e))⟩
  · exact ⟨a,ha,b,hb,Or.inl e⟩
  · exact ⟨a,ha,b,hb,Or.inr (Or.inr (Or.inr e))⟩

end Normal

end PEqualNP.Outside.L_meta_17257

import PEqualNP.Defs
namespace Flat8811
def evalX (F : ℕ → Set (Finset ℕ)) (w : ℕ) (Z : Finset ℕ) : Prop := Z ∈ F w

lemma evalX_input {m : ℕ} {F : ℕ → Set (Finset ℕ)}
    (hin : ∀ v < m, F v = {Z | v ∈ Z}) {v : ℕ} (hv : v < m) (Z : Finset ℕ) :
    evalX F v Z ↔ v ∈ Z := by
  simp [evalX, hin v hv]

def GateSpec (F : ℕ → Set (Finset ℕ)) (m s : ℕ) : Prop :=
  ∀ g < s, ∃ a < m + g, ∃ b < m + g,
    F (m + g) = F a ∪ F b ∨ F (m + g) = F a ∨
    F (m + g) = ∅ ∨ F (m + g) = F a ∩ F b

lemma evalX_mono {m s : ℕ} {F : ℕ → Set (Finset ℕ)}
    (hin : ∀ v < m, F v = {Z | v ∈ Z}) (hgate : GateSpec F m s)
    {Z₁ Z₂ : Finset ℕ} (hsub : Z₁ ⊆ Z₂) :
    ∀ w < m + s, evalX F w Z₁ → evalX F w Z₂ := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw
    by_cases h : w < m
    · simpa only [evalX_input hin h] using @hsub w
    have hwg : w = m + (w - m) := by omega
    obtain ⟨a, ha, b, hb, hs⟩ := hgate (w - m) (by omega)
    have ha' := ih a (by omega) (by omega)
    have hb' := ih b (by omega) (by omega)
    rw [hwg]
    unfold evalX at ha' hb' ⊢
    rcases hs with h₁ | h₁ | h₁ | h₁ <;> rw [h₁]
    · exact fun h => h.elim (Or.inl ∘ ha') (Or.inr ∘ hb')
    · exact ha'
    · simp
    · exact fun h => ⟨ha' h.1, hb' h.2⟩

def negatives {N : ℕ} (I : Fin N → Fin N → Prop) (q : ℕ) (F : ℕ → Set (Finset ℕ)) (o : ℕ) :=
  ∀ (T : Finset (Fin N)) (Z : Finset ℕ),
      T.card ≤ q → (∀ u ∈ Z, u < N + N) →
      (∀ p : Fin N, p.val ∈ Z → ∀ l ∈ T, ¬ I p l) →
      (∀ l : Fin N, N + l.val ∈ Z → l ∈ T) → ¬ evalX F o Z

end Flat8811
namespace Flat8811
def inputsOf {N : ℕ} (X Y : Finset (Fin N)) : Finset ℕ :=
  (X.image Fin.val) ∪ (Y.image fun l => N+l.val)
theorem input_point {N : ℕ} (X Y : Finset (Fin N)) (p : Fin N) :
    p.val∈inputsOf X Y ↔ p∈X := by
  simp only [inputsOf,Finset.mem_union,Finset.mem_image]
  constructor
  · rintro (⟨r,hr,e⟩|⟨l,_,e⟩)
    · exact Fin.ext e ▸ hr
    · have := p.isLt; omega
  · exact fun hp => Or.inl ⟨p,hp,rfl⟩
theorem input_line {N : ℕ} (X Y : Finset (Fin N)) (l : Fin N) :
    N+l.val∈inputsOf X Y ↔ l∈Y := by
  simp only [inputsOf,Finset.mem_union,Finset.mem_image]
  constructor
  · rintro (⟨p,_,e⟩|⟨r,hr,e⟩)
    · have := p.isLt; omega
    · exact Fin.ext (Nat.add_left_cancel e) ▸ hr
  · exact fun hl => Or.inr ⟨l,hl,rfl⟩
theorem blocked {q N : ℕ} (I : Fin N → Fin N → Prop)
    (F : ℕ → Set (Finset ℕ)) (o : ℕ) (neg : negatives I q F o)
    (X Y : Finset (Fin N)) (hy : Y.card≤q) (noEdges : ∀ p ∈ X, ∀ l ∈ Y, ¬I p l) :
    inputsOf X Y ∉ F o := by
  apply neg Y _ hy
  · intro k hk
    simp only [inputsOf,Finset.mem_union,Finset.mem_image] at hk
    rcases hk with ⟨p,_,rfl⟩|⟨l,_,rfl⟩ <;> omega
  · exact fun p hp l hl => noEdges p ((input_point X Y p).mp hp) l hl
  · exact fun l hl => (input_line X Y l).mp hl

theorem defectsConflict {q N s o a b : ℕ} (I : Fin N → Fin N → Prop)
    (F : ℕ → Set (Finset ℕ)) (hq : 2≤q) (hin : ∀ i<N+N, F i={Z | i∈Z})
    (gates : GateSpec F (N+N) s) (ha : a<N+N+s) (hb : b<N+N+s)
    (carry : F a ∩ F b ⊆ F o) (neg : negatives I q F o)
    {p l r m : Fin N} (e : ¬I p l) (f : ¬I r m)
    (yesA : {p.val,N+l.val} ∈ F a) (yesB : {r.val,N+m.val} ∈ F b) :
    I p m ∨ I r l := by
  by_contra! h
  let X : Finset (Fin N) := {p,r}
  let Y : Finset (Fin N) := {l,m}
  have independent : ∀ i∈X, ∀ j∈Y, ¬ I i j := by
    intro i hi j hj
    simp only [X,Y,Finset.mem_insert,Finset.mem_singleton] at hi hj
    rcases hi with rfl|rfl <;> rcases hj with rfl|rfl <;> tauto
  apply blocked I F o neg X Y (Finset.card_le_two.trans hq) independent
  apply carry
  have lift (i j : Fin N) (hi : i∈X) (hj : j∈Y) :
      ({i.val,N+j.val} : Finset ℕ) ⊆ inputsOf X Y :=
    Finset.insert_subset ((input_point X Y i).mpr hi)
      (Finset.singleton_subset_iff.mpr ((input_line X Y j).mpr hj))
  exact ⟨evalX_mono hin gates (lift p l (by simp [X]) (by simp [Y])) a ha yesA,
    evalX_mono hin gates (lift r m (by simp [X]) (by simp [Y])) b hb yesB⟩

theorem fiveDefects {q N s o a b : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (F : ℕ → Set (Finset ℕ)) (hq : 2≤q) (hin : ∀ i<N+N, F i={Z | i∈Z})
    (gates : GateSpec F (N+N) s) (ha : a<N+N+s) (hb : b<N+N+s)
    (carry : F a ∩ F b ⊆ F o) (neg : negatives I q F o)
    (E : Finset (Fin N × Fin N)) (size : 5 ≤ E.card)
    (bad : ∀ z∈E, ¬I z.1 z.2 ∧ ({z.1.val,N+z.2.val} : Finset ℕ) ∈ F a)
    (arc : ∀ l, (E.filter (fun z => I z.1 l)).card≤2)
    (dual : ∀ p, (E.filter (fun z => I p z.2)).card≤2) :
    ∀ r m : Fin N, ({r.val,N+m.val} : Finset ℕ) ∈ F b → I r m := by
  classical
  intro r m on
  by_contra miss
  have sub : E ⊆ (E.filter (fun z => I z.1 m)) ∪ (E.filter (fun z => I r z.2)) := by
    intro z hz
    obtain ⟨hno,hy⟩ := bad z hz
    rcases defectsConflict I F hq hin gates ha hb carry neg hno miss hy on with h|h
    exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hz,h⟩)
    exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hz,h⟩)
  have card := (Finset.card_le_card sub).trans (Finset.card_union_le _ _)
  have := arc m; have := dual r
  omega

end Flat8811

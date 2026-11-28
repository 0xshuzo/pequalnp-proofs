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
namespace Flat8811

def Covered {N : ℕ} (E : Finset (Fin N × Fin N)) (a b : ℕ) : Prop :=
  ∃ P L : Finset (Fin N), P.card≤a ∧ L.card≤b ∧ ∀ e∈E,e.1∈P ∨ e.2∈L

theorem matchingCover {N : ℕ} (I : Fin N → Fin N → Prop)
    (unique : ∀ p r : Fin N, p≠r → ∃! l : Fin N, I p l ∧ I r l)
    (A B : Finset (Fin N × Fin N))
    (conflict : ∀ x∈A, ∀ y∈B, I x.1 y.2 ∨ I y.1 x.2) :
    Covered A 2 2 ∨ Covered B 3 3 := by
  classical
  by_cases non : A.Nonempty
  case neg =>
    left
    exact ⟨∅,∅,by simp,by simp,fun e h => (non ⟨e,h⟩).elim⟩
  obtain ⟨a,ha⟩ := non
  by_cases more : ∃ b∈A,b.1≠a.1 ∧ b.2≠a.2
  case neg =>
    left
    refine ⟨{a.1},{a.2},by simp,by simp,?_⟩
    intro e he
    simp only [Finset.mem_singleton]
    by_contra! n
    exact more ⟨e,he,n⟩
  obtain ⟨b,hb,pba,lba⟩ := more
  by_cases third : ∃ c∈A,c.1≠a.1 ∧ c.1≠b.1 ∧ c.2≠a.2 ∧ c.2≠b.2
  case neg =>
    left
    refine ⟨{a.1,b.1},{a.2,b.2},Finset.card_le_two,Finset.card_le_two,?_⟩
    intro e he
    simp only [Finset.mem_insert,Finset.mem_singleton]
    by_contra! n
    exact third ⟨e,he,n.1.1,n.1.2,n.2.1,n.2.2⟩
  obtain ⟨c,hc,pca,pcb,lca,lcb⟩ := third
  have meet (l m : Fin N) (ne : l≠m) :
      ∃ p : Fin N, ∀ r, I r l → I r m → r=p := by
    by_cases h : ∃ p, I p l ∧ I p m
    · obtain ⟨p,pl,pm⟩ := h
      refine ⟨p,fun r rl rm => ?_⟩
      by_contra rp
      exact ne ((unique r p rp).unique ⟨rl,pl⟩ ⟨rm,pm⟩)
    · exact ⟨a.1,fun r rl rm => (h ⟨r,rl,rm⟩).elim⟩
  obtain ⟨pab,mpab⟩ := meet a.2 b.2 lba.symm
  obtain ⟨pac,mpac⟩ := meet a.2 c.2 lca.symm
  obtain ⟨pbc,mpbc⟩ := meet b.2 c.2 lcb.symm
  obtain ⟨lab,_,mlab⟩ := unique a.1 b.1 pba.symm
  obtain ⟨lac,_,mlac⟩ := unique a.1 c.1 pca.symm
  obtain ⟨lbc,_,mlbc⟩ := unique b.1 c.1 pcb.symm
  have tri (u v w : Fin N) : ({u,v,w}:Finset (Fin N)).card≤3 := by
    have h := Finset.card_insert_le (a:=u) (s:=({v,w}:Finset (Fin N)))
    have t : ({v,w}:Finset (Fin N)).card≤2 := Finset.card_le_two
    omega
  right
  refine ⟨{pab,pac,pbc},{lab,lac,lbc},tri ..,tri ..,?_⟩
  intro y hy
  simp only [Finset.mem_insert,Finset.mem_singleton]
  have ab (x : I a.1 y.2) (z : I b.1 y.2) := mlab y.2 ⟨x,z⟩
  have ac (x : I a.1 y.2) (z : I c.1 y.2) := mlac y.2 ⟨x,z⟩
  have bc (x : I b.1 y.2) (z : I c.1 y.2) := mlbc y.2 ⟨x,z⟩
  have ab' := mpab y.1
  have ac' := mpac y.1
  have bc' := mpbc y.1
  rcases conflict a ha y hy with a₁|a₂ <;> rcases conflict b hb y hy with b₁|b₂ <;>
    rcases conflict c hc y hy with c₁|c₂
  · exact Or.inr (Or.inl (ab a₁ b₁))
  · exact Or.inr (Or.inl (ab a₁ b₁))
  · exact Or.inr (Or.inr (Or.inl (ac a₁ c₁)))
  · exact Or.inl (Or.inr (Or.inr (bc' b₂ c₂)))
  · exact Or.inr (Or.inr (Or.inr (bc b₁ c₁)))
  · exact Or.inl (Or.inr (Or.inl (ac' a₂ c₂)))
  · exact Or.inl (Or.inl (ab' a₂ b₂))
  · exact Or.inl (Or.inl (ab' a₂ b₂))

theorem oneChild {q N s o a b : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (unique : ∀ p r : Fin N, p≠r → ∃! l : Fin N, I p l ∧ I r l)
    (F : ℕ → Set (Finset ℕ)) (hq : 2≤q) (hin : ∀ i<N+N, F i={Z | i∈Z})
    (gates : GateSpec F (N+N) s) (ha : a<N+N+s) (hb : b<N+N+s)
    (carry : F a∩F b ⊆ F o) (neg : negatives I q F o) :
    ∃ w∈({a,b}:Finset ℕ), ∃ P L : Finset (Fin N), P.card≤3 ∧ L.card≤3 ∧
      ∀ p l, p∉P → l∉L → ({p.val,N+l.val}:Finset ℕ)∈F w → I p l := by
  classical
  let E (w : ℕ) := Finset.univ.filter (fun e : Fin N × Fin N =>
    ¬I e.1 e.2 ∧ ({e.1.val,N+e.2.val}:Finset ℕ)∈F w)
  have bad (w : ℕ) (e : Fin N × Fin N) : e∈E w ↔
      ¬I e.1 e.2 ∧ ({e.1.val,N+e.2.val}:Finset ℕ)∈F w := by simp [E]
  have h := matchingCover I unique (E a) (E b) (by
    intro x hx y hy
    exact defectsConflict I F hq hin gates ha hb carry neg ((bad a x).mp hx).1 ((bad b y).mp hy).1
      ((bad a x).mp hx).2 ((bad b y).mp hy).2)
  have finish (w : ℕ) (mem : w∈({a,b}:Finset ℕ)) {u v : ℕ} (uc : u≤3) (vc : v≤3)
       (co : Covered (E w) u v) :
       ∃ w∈({a,b}:Finset ℕ), ∃ P L : Finset (Fin N), P.card≤3 ∧ L.card≤3 ∧
        ∀ p l, p∉P → l∉L → ({p.val,N+l.val}:Finset ℕ)∈F w → I p l := by
    obtain ⟨P,L,ps,ls,ev⟩ := co
    refine ⟨w,mem,P,L,ps.trans uc,ls.trans vc,?_⟩
    intro p l np nl on
    by_contra no
    exact (ev (p,l) ((bad w (p,l)).mpr ⟨no,on⟩)).elim np nl
  exact h.elim (finish a (by simp) (by decide) (by decide)) (finish b (by simp) le_rfl le_rfl)

end Flat8811

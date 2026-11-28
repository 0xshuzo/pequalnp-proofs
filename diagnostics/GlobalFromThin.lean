import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9134

abbrev Vec (N : ℕ) := Fin N → Bool
abbrev Board (N : ℕ) := Vec N × Vec N
abbrev Bank (α : Type*) := ℕ → Set α

def Steps {α : Type*} (W : Bank α) (n s : ℕ) := ∀ j<s,
  ∃ a<n+j, ∃ b<n+j, W (n+j)=W a∪W b ∨ W (n+j)=W a ∨ W (n+j)=∅ ∨ W (n+j)=W a∩W b

def UnionAt {α : Type*} (W : Bank α) (n j : ℕ) := ∃ a<n+j, ∃ b<n+j, W (n+j)=W a∪W b

theorem upward {α : Type*} {W : Bank α} {n s : ℕ} (hs : Steps W n s)
    {x y : α} (h : ∀ i<n, x∈W i → y∈W i) : ∀ w<n+s, x∈W w → y∈W w := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw hx
    by_cases hi : w<n
    · exact h w hi hx
    let j := w-n
    have eq : n+j=w := by dsimp [j]; omega
    obtain ⟨a,ha,b,hb,e|e|e|e⟩ := hs j (by dsimp [j]; omega) <;>
      rw [eq] at ha hb e <;> rw [e] at hx ⊢
    · exact hx.elim (fun t => Or.inl (ih a ha (ha.trans hw) t)) (fun t => Or.inr (ih b hb (hb.trans hw) t))
    · exact ih a ha (ha.trans hw) hx
    · exact hx
    · exact ⟨ih a ha (ha.trans hw) hx.1,ih b hb (hb.trans hw) hx.2⟩

theorem leafCertificate {α : Type*} (n s : ℕ) (M : Finset ℕ)
    (A : ℕ → Prop) (H : α → ℕ → Prop)
    (rule : ∀ j<s, A (n+j) → ∃ B : Finset ℕ, B.card≤1+(if j∈M then 1 else 0) ∧
      (∀ i∈B,i<n+j) ∧ (∀ i∈B,A i) ∧ ∀ y : α, (∀ i∈B,H y i) → H y (n+j))
    (k : ℕ) (hk : k≤s) (S : Finset ℕ) (lo : ∀ w∈S,w<n+k) (off : ∀ w∈S,A w) :
    ∃ R : Finset ℕ, R ⊆ Finset.range n ∧ R.card ≤ S.card+(M∩Finset.range k).card ∧
      (∀ r∈R,A r) ∧ ∀ y : α, (∀ r∈R,H y r) → ∀ w∈S,H y w := by
  classical
  induction k generalizing S with
  | zero =>
    exact ⟨S,fun i hi => Finset.mem_range.mpr (by simpa using lo i hi),by simp,off,fun _ h => h⟩
  | succ k ih =>
    let v := n+k
    have below (i : ℕ) (hi : i∈S) (ne : i≠v) : i<n+k := by
      have := lo i hi
      dsimp [v] at ne
      omega
    have older : M∩Finset.range k ⊆ M∩Finset.range (k+1) :=
      fun i hi => Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hi).1,Finset.mem_range.mpr (Nat.lt_succ_of_lt (Finset.mem_range.mp (Finset.mem_inter.mp hi).2))⟩
    by_cases active : v∈S
    · have old := off v active
      have clause := rule k (by omega) old
      obtain ⟨B,bs,bl,bo,bc⟩ := clause
      let Q := S.erase v ∪ B
      have ql : ∀ i∈Q,i<n+k := by
        intro i hi
        rcases Finset.mem_union.mp hi with a|b
        · exact below i (Finset.mem_erase.mp a).2 (Finset.mem_erase.mp a).1
        · exact bl i b
      have qo : ∀ i∈Q,A i := by
        intro i hi
        rcases Finset.mem_union.mp hi with a|b
        · exact off i (Finset.mem_erase.mp a).2
        · exact bo i b
      obtain ⟨R,rr,cr,ro,rc⟩ := ih (by omega) Q ql qo
      refine ⟨R,rr,?_,ro,?_⟩
      · have merge := Finset.card_union_le (S.erase v) B
        have er := Finset.card_erase_add_one active
        dsimp [Q] at cr
        by_cases inM : k∈M
        · have strict : M∩Finset.range k ⊂ M∩Finset.range (k+1) := by
            refine Finset.ssubset_iff_subset_ne.mpr ⟨older,?_⟩
            intro eq
            have mem : k∈M∩Finset.range (k+1) := by simp [inM]
            rw [←eq] at mem
            simpa using mem
          have := Finset.card_lt_card strict
          simp [inM] at bs
          omega
        · have := Finset.card_le_card older
          simp [inM] at bs
          omega
      · intro y yr w hw
        have h := rc y yr
        by_cases eq : w=v
        · exact eq ▸ bc y (fun b hb => h b (Finset.mem_union_right _ hb))
        · exact h w (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨eq,hw⟩))
    · obtain ⟨R,rr,cr,ro,rc⟩ := ih (by omega) S (fun w hw => below w hw (fun eq => active (eq ▸ hw))) off
      exact ⟨R,rr,cr.trans (Nat.add_le_add_left (Finset.card_le_card older) _),ro,rc⟩

def MarkSteps {N : ℕ} (W : Bank (Board N)) (s : ℕ) (M : Finset ℕ) := ∀ j<s,
  ∃ a<N+N+j, ∃ b<N+N+j,
    W (N+N+j) ∈ [W a∪W b,W a,∅] ∨ W (N+N+j)=W a∩W b ∧
      (j∈M ∨ ∃ T U : Set (Vec N), W a=T ×ˢ Set.univ ∧ W b=Set.univ ×ˢ U)

theorem thinWitness {N s o : ℕ} (W : Bank (Board N)) (M : Finset ℕ)
    (hs : MarkSteps W s M) (ho : o<N+N+s)
    (raw : ∀ i : Fin N, W i.val={z | z.1 i=true} ∧ W (N+i.val)={z | z.2 i=true})
    (P Y : Vec N) (accept : (P,Y)∈W o) :
    ∃ L : Finset (Fin N), L.card≤M.card+1 ∧ (∀ l∈L,Y l=true) ∧
      (P,fun l => decide (l∈L))∈W o := by
  classical
  let A := fun w => (P,Y)∈W w
  let H := fun (y : Vec N) w => (P,y)∈W w
  have rule (j : ℕ) (hj : j<s) (on : A (N+N+j)) : ∃ B : Finset ℕ,
      B.card≤1+(if j∈M then 1 else 0) ∧ (∀ i∈B,i<N+N+j) ∧
      (∀ i∈B,A i) ∧ ∀ y : Vec N, (∀ i∈B,H y i) → H y (N+N+j) := by
    obtain ⟨a,ha,b,hb,eq|⟨eq,mark⟩⟩ := hs j hj
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at eq
      change (P,Y)∈W (N+N+j) at on
      rcases eq with eq|eq|eq <;> rw [eq] at on
      · rcases on with h|h
        · refine ⟨{a},by simp,by simpa using ha,by simpa [A] using h,?_⟩
          intro y hy
          change (P,y)∈W (N+N+j)
          rw [eq]
          exact Or.inl (hy a (by simp))
        · refine ⟨{b},by simp,by simpa using hb,by simpa [A] using h,?_⟩
          intro y hy
          change (P,y)∈W (N+N+j)
          rw [eq]
          exact Or.inr (hy b (by simp))
      · refine ⟨{a},by simp,by simpa using ha,by simpa [A] using on,?_⟩
        intro y hy
        change (P,y)∈W (N+N+j)
        rw [eq]
        exact hy a (by simp)
      · exact on.elim
    · change (P,Y)∈W (N+N+j) at on
      rw [eq] at on
      rcases mark with hm|⟨T,U,left,right⟩
      · refine ⟨{a,b},by simpa [hm] using (Finset.card_le_two : ({a,b}:Finset ℕ).card≤2),
          by simpa using And.intro ha hb,by simpa [A] using And.intro on.1 on.2,?_⟩
        intro y hy
        change (P,y)∈W (N+N+j)
        rw [eq]
        exact ⟨hy a (by simp),hy b (by simp)⟩
      · have pa : P∈T := by have t := on.1; rw [left] at t; exact t.1
        refine ⟨{b},by simp,by simpa using hb,by simpa [A] using on.2,?_⟩
        intro y hy
        change (P,y)∈W (N+N+j)
        rw [eq,left]
        exact ⟨⟨pa,Set.mem_univ _⟩,hy b (by simp)⟩
  obtain ⟨R,rr,cr,ro,rc⟩ := leafCertificate (N+N) s M A H rule s le_rfl {o}
    (by simpa using ho) (by simpa [A] using accept)
  let L := Finset.univ.filter (fun l : Fin N => N+l.val∈R)
  have inc (l : Fin N) (hl : l∈L) : N+l.val∈R := (Finset.mem_filter.mp hl).2
  have cs : L.card≤R.card := Finset.card_le_card_of_injOn (fun l : Fin N => N+l.val)
    inc (fun a _ b _ e => Fin.ext (Nat.add_left_cancel e))
  have rawL (l : Fin N) (h : l∈L) : Y l=true := by
    have yes := ro _ (inc l h)
    change (P,Y)∈W (N+l.val) at yes
    rw [(raw l).2] at yes
    exact yes
  have cm := Finset.card_le_card (Finset.inter_subset_left : M∩Finset.range s ⊆ M)
  simp only [Finset.card_singleton] at cr
  refine ⟨L,by omega,rawL,?_⟩
  apply rc (fun l => decide (l∈L)) _ o (by simp)
  intro r hr
  by_cases hl : r<N
  · let p : Fin N := ⟨r,hl⟩
    have yes := ro r hr
    change (P,Y)∈W p.val at yes
    change (P,_)∈W p.val
    rw [(raw p).1] at yes ⊢
    exact yes
  · have lt := Finset.mem_range.mp (rr hr)
    let l : Fin N := ⟨r-N,by omega⟩
    have e : N+l.val=r := by dsimp [l]; omega
    change (P,_)∈W r
    rw [←e,(raw l).2]
    change decide (l∈L)=true
    exact decide_eq_true (Finset.mem_filter.mpr ⟨Finset.mem_univ _,e.symm ▸ hr⟩)
theorem globallyExact {q N s o : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (W : Bank (Board N)) (M : Finset ℕ) (hs : MarkSteps W s M) (ho : o<N+N+s)
    (raw : ∀ i : Fin N, W i.val={z | z.1 i=true} ∧ W (N+i.val)={z | z.2 i=true})
    (pos : ∀ p l, I p l →
      (fun r : Fin N => decide (r=p),fun k : Fin N => decide (k=l))∈W o)
    (neg : ∀ Y : Vec N, Fintype.card {l // Y l=true}≤q →
      (fun p => decide (¬∃ l, I p l ∧ Y l=true),Y)∉W o)
    (few : M.card<q) (P Y : Vec N) :
    (P,Y)∈W o ↔ ∃ p l, I p l ∧ P p=true ∧ Y l=true := by
  classical
  have plain : Steps W (N+N) s := by
    intro j hj
    obtain ⟨a,ha,b,hb,h|h⟩ := hs j hj
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at h
      exact ⟨a,ha,b,hb,h.imp_right (Or.imp_right Or.inl)⟩
    · exact ⟨a,ha,b,hb,Or.inr (Or.inr (Or.inr h.1))⟩
  have mono {A B C D : Vec N} (h₁ : ∀ p, A p=true → C p=true) (h₂ : ∀ l, B l=true → D l=true) :
      (A,B)∈W o → (C,D)∈W o := by
    apply upward plain _ o ho
    intro r hr
    by_cases left : r<N
    · let i : Fin N := ⟨r,left⟩
      change (A,B)∈W i.val → (C,D)∈W i.val
      rw [(raw i).1]
      exact h₁ i
    · let i : Fin N := ⟨r-N,by omega⟩
      have e : N+i.val=r := by dsimp [i]; omega
      rw [←e,(raw i).2]
      exact h₂ i
  constructor
  · intro yes
    obtain ⟨L,card,sub,hit⟩ := thinWitness W M hs ho raw P Y yes
    let Z := fun l => decide (l∈L)
    have width : Fintype.card {l // Z l=true}=L.card := by
      rw [Fintype.card_subtype]
      congr 1
      ext l
      simp [Z]
    by_contra bad
    apply neg Z (width.le.trans (card.trans (by omega)))
    apply mono _ (fun _ h => h) hit
    intro p hp
    apply decide_eq_true
    rintro ⟨l,pl,on⟩
    exact bad ⟨p,l,pl,hp,sub l (of_decide_eq_true on)⟩
  · rintro ⟨p,l,pl,hp,hl⟩
    exact mono (fun a ha => (of_decide_eq_true ha).symm ▸ hp)
      (fun b hb => (of_decide_eq_true hb).symm ▸ hl) (pos p l pl)

end PEqualNP.Outside.L_meta_9134

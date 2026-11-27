import PEqualNP.Defs

namespace Flat8811
def adj (N : ℕ) (inc : Fin N → Fin N → Prop) (u v : ℕ) : Prop :=
  ∃ p l : Fin N, inc p l ∧
    ((u = p.val ∧ v = N + l.val) ∨ (v = p.val ∧ u = N + l.val))

theorem adjSymm {N : ℕ} {inc : Fin N → Fin N → Prop} {u v : ℕ}
    (h : adj N inc u v) : adj N inc v u := by
  obtain ⟨p,l,hp,hv⟩ := h
  exact ⟨p,l,hp,hv.symm⟩

theorem commonUnique {N : ℕ} {inc : Fin N → Fin N → Prop}
    (unique : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, inc p l ∧ inc p' l)
    {u u' v v' : ℕ} (ne : v ≠ v')
    (huv : adj N inc u v) (huv' : adj N inc u v')
    (hu'v : adj N inc u' v) (hu'v' : adj N inc u' v') : u = u' := by
  obtain ⟨p,l,edge,h⟩ := huv
  obtain ⟨p',l',edge',h'⟩ := huv'
  obtain ⟨r,t,edgeR,k⟩ := hu'v
  obtain ⟨r',t',edgeR',k'⟩ := hu'v'
  have hp := p.isLt
  have hp' := p'.isLt
  have hr := r.isLt
  have hr' := r'.isLt
  rcases h with ⟨hu,hv⟩ | ⟨hv,hu⟩
  · have b1 : u < N := by omega
    have b2 : N ≤ v := by omega
    have b3 : N ≤ v' := by rcases h' with ⟨_,h⟩ | ⟨_,h⟩ <;> omega
    have left' : u = p'.val ∧ v' = N + l'.val := by
      rcases h' with h | ⟨_,h⟩
      · exact h
      · omega
    have right : u' = r.val ∧ v = N + t.val := by
      rcases k with k | ⟨k,_⟩
      · exact k
      · omega
    have right' : u' = r'.val ∧ v' = N + t'.val := by
      rcases k' with k' | ⟨k',_⟩
      · exact k'
      · omega
    have p_eq : p' = p := Fin.ext (left'.1.symm.trans hu)
    have r_eq : r' = r := Fin.ext (right'.1.symm.trans right.1)
    have l_eq : t = l := Fin.ext (by omega)
    have l'_eq : t' = l' := Fin.ext (by omega)
    subst p' r' t t'
    by_contra u_ne
    have p_ne : p ≠ r := fun he => u_ne (by rw [hu,right.1,he])
    obtain ⟨c,_,only⟩ := unique p r p_ne
    have same : l = l' := (only l ⟨edge,edgeR⟩).trans (only l' ⟨edge',edgeR'⟩).symm
    exact ne (by rw [hv,left'.2,same])
  · have b1 : N ≤ u := by omega
    have b2 : v < N := by omega
    have left' : v' = p'.val ∧ u = N + l'.val := by
      rcases h' with ⟨h,_⟩ | h
      · omega
      · exact h
    have right : v = r.val ∧ u' = N + t.val := by
      rcases k with ⟨_,k⟩ | k
      · omega
      · exact k
    have right' : v' = r'.val ∧ u' = N + t'.val := by
      rcases k' with ⟨_,k'⟩ | k'
      · have hv' := left'.1
        omega
      · exact k'
    have p_eq : r = p := Fin.ext (right.1.symm.trans hv)
    have p'_eq : r' = p' := Fin.ext (right'.1.symm.trans left'.1)
    have l_eq : l' = l := Fin.ext (by omega)
    have t_eq : t' = t := Fin.ext (by omega)
    subst r r' l' t'
    have p_ne : p ≠ p' := fun he => ne (by rw [hv,left'.1,he])
    obtain ⟨c,_,only⟩ := unique p p' p_ne
    have same : l = t := (only l ⟨edge,edge'⟩).trans (only t ⟨edgeR,edgeR'⟩).symm
    rw [hu,right.2,same]

theorem singletonOf {U : Finset ℕ} {v : ℕ} (hv : v ∈ U) (small : U.card ≤ 1) :
    U = {v} := by
  symm
  exact Finset.eq_of_subset_of_card_le (Finset.singleton_subset_iff.mpr hv) (by simpa using small)

theorem firstBranch (N s : ℕ) (U : ℕ → Finset ℕ) (a b op : Fin s → ℕ)
    (prior : ∀ j, a j < N+N+j.val ∧ b j < N+N+j.val)
    (tags : ∀ j, op j ≤ 3)
    (raw : ∀ i < N+N, (U i).card ≤ 1)
    (updates : ∀ j, (op j=0 → U (N+N+j.val)=U (a j) ∪ U (b j)) ∧
      (op j=1 → U (N+N+j.val)=U (a j)) ∧ (2≤op j → U (N+N+j.val)=∅)) :
    ∀ r < N+N+s, ∀ v ∈ U r, 2 ≤ (U r).card →
    ∃ (j : Fin s) (dir : Bool), op j=0 ∧ U (N+N+j.val) ⊆ U r ∧
      2 ≤ (U (N+N+j.val)).card ∧ U (if dir then b j else a j) = {v} := by
  intro r
  induction r using Nat.strong_induction_on with
  | ind r smaller =>
    intro bound v hv large
    by_cases isRaw : r < N+N
    · have := raw r isRaw
      omega
    let j : Fin s := ⟨r-(N+N), by omega⟩
    have hj : N+N+j.val = r := by dsimp [j]; omega
    have a_prior : a j < r := by simpa only [hj] using (prior j).1
    have b_prior : b j < r := by simpa only [hj] using (prior j).2
    by_cases disj : op j=0
    · have parts := (updates j).1 disj
      rw [hj] at parts
      have helper (dir : Bool) (t : ℕ) (ht : t = (if dir then b j else a j))
          (before : t < r) (inside : U t ⊆ U r) (hm : v ∈ U t) :
          ∃ (k : Fin s) (d : Bool), op k=0 ∧ U (N+N+k.val) ⊆ U r ∧
            2 ≤ (U (N+N+k.val)).card ∧ U (if d then b k else a k) = {v} := by
        by_cases deep : 2 ≤ (U t).card
        · obtain ⟨k,d,h1,h2,h3,h4⟩ := smaller t before (by omega) v hm deep
          exact ⟨k,d,h1,h2.trans inside,h3,h4⟩
        · refine ⟨j,dir,disj,by rw [hj],by rwa [hj],?_⟩
          rw [← ht]
          exact singletonOf hm (by omega)
      rw [parts] at hv
      rcases Finset.mem_union.mp hv with ha | hb
      · exact helper false (a j) rfl a_prior (by rw [parts]; exact Finset.subset_union_left) ha
      · exact helper true (b j) rfl b_prior (by rw [parts]; exact Finset.subset_union_right) hb
    · by_cases isCopy : op j=1
      · have eq := (updates j).2.1 isCopy
        rw [hj] at eq
        rw [eq] at hv large ⊢
        exact smaller (a j) a_prior (by omega) v hv large
      · have eq := (updates j).2.2 (by have := tags j; omega)
        rw [hj] at eq
        rw [eq] at hv
        exact (Finset.notMem_empty _ hv).elim

set_option maxHeartbeats 3000000 in
theorem charge (N s : ℕ) (inc : Fin N → Fin N → Prop) [DecidableRel inc]
    (unique : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, inc p l ∧ inc p' l)
    (U : ℕ → Finset ℕ) (a b op : Fin s → ℕ)
    (prior : ∀ j, a j < N+N+j.val ∧ b j < N+N+j.val)
    (tags : ∀ j, op j ≤ 3)
    (raw : ∀ i < N+N, (U i).card ≤ 1)
    (updates : ∀ j, (op j=0 → U (N+N+j.val)=U (a j) ∪ U (b j)) ∧
      (op j=1 → U (N+N+j.val)=U (a j)) ∧ (2≤op j → U (N+N+j.val)=∅))
    (E : Finset (Fin N × Fin N))
    (trace : ∀ p l, (p,l) ∈ E → ∃ j : Fin s, op j=3 ∧
      ((p.val ∈ U (a j) ∧ N+l.val ∈ U (b j)) ∨
       (N+l.val ∈ U (a j) ∧ p.val ∈ U (b j))) ∧
      ∀ u ∈ U (a j), ∀ v ∈ U (b j), adj N inc u v) :
    E.card ≤ 2*s := by
  classical
  let pick (z : Fin s × Bool) := if z.2 then b z.1 else a z.1
  let flip (z : Fin s × Bool) := (z.1,!z.2)
  let certificate (z : Fin s × Bool) (u v : ℕ) :=
    (op z.1=0 ∧ U (pick z)={v} ∧ 2 ≤ (U (N+N+z.1.val)).card ∧
      ∀ w ∈ U (N+N+z.1.val), adj N inc u w) ∨
    (op z.1=3 ∧ U (pick z)={v} ∧ U (pick (flip z))={u})
  let endpoints (e : Fin N × Fin N) (u v : ℕ) :=
    (u = e.1.val ∧ v = N+e.2.val) ∨ (v = e.1.val ∧ u = N+e.2.val)
  have place (j : Fin s) (dir : Bool) (u v : ℕ) (hj : op j=3)
      (hv : v ∈ U (pick (j,dir))) (small : U (pick (flip (j,dir))) = {u})
      (neighbors : ∀ w ∈ U (pick (j,dir)), adj N inc u w) :
      ∃ z, certificate z u v := by
    by_cases multi : 2 ≤ (U (pick (j,dir))).card
    · have hk : pick (j,dir) < N+N+s := by
        have h := prior j
        have hj' := j.isLt
        cases dir <;> simp [pick] <;> omega
      obtain ⟨k,d,hk0,hsub,hlarge,hv⟩ :=
        firstBranch N s U a b op prior tags raw updates (pick (j,dir)) hk v hv multi
      exact ⟨(k,d), Or.inl ⟨hk0,hv,hlarge,fun w hw => neighbors w (hsub hw)⟩⟩
    · exact ⟨(j,dir), Or.inr ⟨hj,singletonOf hv (by omega),small⟩⟩
  have orient (j : Fin s) (u v : ℕ) (hj : op j=3) (hu : u ∈ U (a j)) (hv : v ∈ U (b j))
      (rectangle : ∀ t ∈ U (a j), ∀ w ∈ U (b j), adj N inc t w) :
      (∃ z, certificate z u v) ∨ (∃ z, certificate z v u) := by
    by_cases small : (U (a j)).card ≤ 1
    · exact Or.inl (place j true u v hj hv (singletonOf hu small) (rectangle u hu))
    · have hsmall : (U (b j)).card ≤ 1 := by
        by_contra not_small
        obtain ⟨u₁,hu₁,u₂,hu₂,ne_u⟩ := Finset.one_lt_card.mp (show 1 < (U (a j)).card by omega)
        obtain ⟨v₁,hv₁,v₂,hv₂,ne_v⟩ := Finset.one_lt_card.mp (show 1 < (U (b j)).card by omega)
        exact ne_u (commonUnique unique ne_v
          (rectangle u₁ hu₁ v₁ hv₁) (rectangle u₁ hu₁ v₂ hv₂)
          (rectangle u₂ hu₂ v₁ hv₁) (rectangle u₂ hu₂ v₂ hv₂))
      exact Or.inr (place j false v u hj hu (singletonOf hv hsmall)
        (fun w hw => adjSymm (rectangle w hw v hv)))
  have cover (e : E) : ∃ z, ∃ u v, endpoints e.val u v ∧ certificate z u v := by
    obtain ⟨j,hj,hab,cross⟩ := trace e.val.1 e.val.2 e.property
    rcases hab with ⟨ha,hb⟩ | ⟨ha,hb⟩
    · rcases orient j _ _ hj ha hb cross with ⟨z,cert⟩ | ⟨z,cert⟩
      · exact ⟨z,_,_,Or.inl ⟨rfl,rfl⟩,cert⟩
      · exact ⟨z,_,_,Or.inr ⟨rfl,rfl⟩,cert⟩
    · rcases orient j _ _ hj ha hb cross with ⟨z,cert⟩ | ⟨z,cert⟩
      · exact ⟨z,_,_,Or.inr ⟨rfl,rfl⟩,cert⟩
      · exact ⟨z,_,_,Or.inl ⟨rfl,rfl⟩,cert⟩
  have uniqueEnd (z : Fin s × Bool) (u v u' v' : ℕ)
      (h : certificate z u v) (h' : certificate z u' v') : u = u' ∧ v = v' := by
    rcases h with ⟨h₀,leaf,large,neigh⟩ | ⟨h₃,leaf,cent⟩
    · rcases h' with ⟨_,leaf',_,neigh'⟩ | ⟨h₃,_,_⟩
      · obtain ⟨w,hw,t,ht,ne⟩ := Finset.one_lt_card.mp
          (show 1 < (U (N+N+z.1.val)).card by omega)
        refine ⟨commonUnique unique ne (neigh w hw) (neigh t ht) (neigh' w hw) (neigh' t ht),?_⟩
        simpa using leaf.symm.trans leaf'
      · omega
    · rcases h' with ⟨h₀,_,_,_⟩ | ⟨_,leaf',cent'⟩
      · omega
      · constructor
        · simpa using cent.symm.trans cent'
        · simpa using leaf.symm.trans leaf'
  have ordered (e : Fin N × Fin N) (u v : ℕ) (h : endpoints e u v) :
      min u v = e.1.val ∧ max u v = N+e.2.val := by
    have bound := e.1.isLt
    rcases h with ⟨hu,hv⟩ | ⟨hv,hu⟩
    · rw [hu,hv,min_eq_left (by omega),max_eq_right (by omega)]
      exact ⟨rfl,rfl⟩
    · rw [hu,hv,min_eq_right (by omega),max_eq_left (by omega)]
      exact ⟨rfl,rfl⟩
  choose code hc using cover
  have injective : Function.Injective code := by
    intro x y he
    obtain ⟨u,v,hx,hcert⟩ := hc x
    obtain ⟨u',v',hy,hcert'⟩ := hc y
    rw [← he] at hcert'
    obtain ⟨sameU,sameV⟩ := uniqueEnd (code x) u v u' v' hcert hcert'
    subst u' v'
    obtain ⟨hx1,hx2⟩ := ordered x.val u v hx
    obtain ⟨hy1,hy2⟩ := ordered y.val u v hy
    apply Subtype.ext
    apply Prod.ext
    · exact Fin.ext (hx1.symm.trans hy1)
    · exact Fin.ext (Nat.add_left_cancel (hx2.symm.trans hy2))
  simpa only [Fintype.card_coe, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool,
    Nat.mul_comm] using Fintype.card_le_of_injective code injective

open scoped BigOperators in
theorem incidence_card (q N : ℕ) (inc : Fin N → Fin N → Prop) [DecidableRel inc]
    (h : ∀ l, Fintype.card {p : Fin N // inc p l} = q+1) :
    (Finset.univ.filter (fun e : Fin N × Fin N => inc e.1 e.2)).card = N*(q+1) := by
  rw [Finset.card_filter, Fintype.sum_prod_type_right]
  calc
    (∑ l : Fin N, ∑ p : Fin N, if inc p l then 1 else 0) = ∑ _l : Fin N, (q+1) := by
      refine Finset.sum_congr rfl (fun l _ => ?_)
      simpa only [Fintype.card_subtype,Finset.card_filter] using h l
    _ = _ := by simp

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

lemma not_evalX_empty {m s : ℕ} {F : ℕ → Set (Finset ℕ)}
    (hin : ∀ v < m, F v = {Z | v ∈ Z}) (hgate : GateSpec F m s)
    {w : ℕ} (hw : w < m + s) : ¬ evalX F w ∅ := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases h : w < m
    · simp [evalX_input hin h]
    have hwg : w = m + (w - m) := by omega
    obtain ⟨a, ha, b, hb, hs⟩ := hgate (w - m) (by omega)
    have ha' := ih a (by omega) (by omega)
    have hb' := ih b (by omega) (by omega)
    rw [hwg]
    unfold evalX at ha' hb' ⊢
    rcases hs with h₁ | h₁ | h₁ | h₁ <;> rw [h₁]
    · exact fun h => h.elim ha' hb'
    · exact ha'
    · simp
    · exact fun h => ha' h.1

def assignment (N : ℕ) (Z : Finset ℕ) : (Fin N → Bool) × (Fin N → Bool) :=
  (fun p => decide (p.val ∈ Z), fun l => decide (N + l.val ∈ Z))

def support {N : ℕ} (A B : Fin N → Bool) : Finset ℕ :=
  ((Finset.univ.filter fun p => A p = true).image Fin.val) ∪
    ((Finset.univ.filter fun l => B l = true).image fun l => N + l.val)

lemma mem_support_point {N : ℕ} (A B : Fin N → Bool) (p : Fin N) :
    p.val ∈ support A B ↔ A p = true := by
  simp only [support, Finset.mem_union, Finset.mem_image, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · rintro (⟨a, ha, he⟩ | ⟨b, _, he⟩)
    · simpa [Fin.ext he] using ha
    · omega
  · exact fun h => Or.inl ⟨p, h, rfl⟩

lemma mem_support_line {N : ℕ} (A B : Fin N → Bool) (l : Fin N) :
    N + l.val ∈ support A B ↔ B l = true := by
  simp only [support, Finset.mem_union, Finset.mem_image, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · rintro (⟨a, _, he⟩ | ⟨b, hb, he⟩)
    · omega
    · have h : b = l := Fin.ext (by omega)
      simpa [h] using hb
  · exact fun h => Or.inr ⟨l, h, rfl⟩

lemma assignment_support {N : ℕ} (A B : Fin N → Bool) :
    assignment N (support A B) = (A, B) := by
  apply Prod.ext
  · funext p
    change decide (p.val ∈ support A B) = A p
    cases h : A p <;> simp [mem_support_point, h]
  · funext l
    change decide (N + l.val ∈ support A B) = B l
    cases h : B l <;> simp [mem_support_line, h]

lemma assignment_pair {N : ℕ} (p l : Fin N) :
    assignment N {p.val, N + l.val} =
      ((fun i : Fin N => decide (i = p)), (fun i : Fin N => decide (i = l))) := by
  apply Prod.ext
  · funext i
    have h : i.val ≠ N + l.val := by omega
    simp [assignment, h, Fin.ext_iff]
  · funext i
    have h : N + i.val ≠ p.val := by omega
    simp [assignment, h, Fin.ext_iff]

def permittedWire {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (Y : Fin N → Bool) : (Fin N → Bool) × (Fin N → Bool) :=
  (fun p => decide (¬ ∃ l : Fin N, I p l ∧ Y l = true), Y)

def negatives {N : ℕ} (I : Fin N → Fin N → Prop) (q : ℕ) (F : ℕ → Set (Finset ℕ)) (o : ℕ) :=
  ∀ (T : Finset (Fin N)) (Z : Finset ℕ),
      T.card ≤ q → (∀ u ∈ Z, u < N + N) →
      (∀ p : Fin N, p.val ∈ Z → ∀ l ∈ T, ¬ I p l) →
      (∀ l : Fin N, N + l.val ∈ Z → l ∈ T) → ¬ evalX F o Z

lemma soundPairs {q N : ℕ} (I : Fin N → Fin N → Prop) (F : ℕ → Set (Finset ℕ)) (o : ℕ)
    (hq : 2≤q) (hX_neg : negatives I q F o) : ∀ u < N+N, ∀ v < N+N,
    {u,v} ∈ F o → adj N I u v := by
  classical
  have hX_neg_two_pts : ∀ p1 p2 : Fin N, ¬ evalX F o {p1.val, p2.val} := by
    intro p1 p2
    refine hX_neg ∅ {p1.val, p2.val} (by simp) ?_ ?_ ?_
    · intro u hu
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl <;> omega
    · intro _ _ _ hl; simp at hl
    · intro l hl
      simp only [Finset.mem_insert, Finset.mem_singleton] at hl
      rcases hl with h | h <;> omega
  have hX_neg_noninc : ∀ p l : Fin N, ¬ I p l → ¬ evalX F o {p.val, N + l.val} := by
    intro p l hnI
    refine hX_neg {l} {p.val, N + l.val} (by simp; omega) ?_ ?_ ?_
    · intro u hu
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl <;> omega
    · intro p' hp' l' hl'
      rw [Finset.mem_singleton] at hl'
      subst hl'
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp'
      rcases hp' with h | h
      · have : p' = p := Fin.ext h
        rwa [this]
      · omega
    · intro l' hl'
      simp only [Finset.mem_insert, Finset.mem_singleton] at hl'
      rcases hl' with h | h
      · omega
      · have : l' = l := Fin.ext (by omega)
        simp [this]
  have hX_neg_two_lns : ∀ l1 l2 : Fin N, ¬ evalX F o {N + l1.val, N + l2.val} := by
    intro l1 l2
    refine hX_neg {l1, l2} {N + l1.val, N + l2.val} (Finset.card_le_two.trans hq) ?_ ?_ ?_
    · intro u hu
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl <;> omega
    · intro p hp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with h | h <;> omega
    · intro l hl
      simp only [Finset.mem_insert, Finset.mem_singleton] at hl ⊢
      rcases hl with h | h
      · left; exact Fin.ext (by omega)
      · right; exact Fin.ext (by omega)
  have side (u : ℕ) (hu : u < N+N) : (∃ p : Fin N, u=p.val) ∨ (∃ l : Fin N, u=N+l.val) := by
    by_cases h : u<N
    · exact Or.inl ⟨⟨u,h⟩,rfl⟩
    · exact Or.inr ⟨⟨u-N,by omega⟩,by dsimp; omega⟩
  intro u hu v hv h
  rcases side u hu with ⟨p,rfl⟩|⟨l,rfl⟩ <;> rcases side v hv with ⟨p',rfl⟩|⟨l',rfl⟩
  · exact (hX_neg_two_pts p p' h).elim
  · exact ⟨p,l',Classical.byContradiction (fun hn => hX_neg_noninc p l' hn h),Or.inl ⟨rfl,rfl⟩⟩
  · have h' : {p'.val,N+l.val} ∈ F o := by rwa [Finset.pair_comm]
    exact ⟨p',l,Classical.byContradiction (fun hn => hX_neg_noninc p' l hn h'),Or.inr ⟨rfl,rfl⟩⟩
  · exact (hX_neg_two_lns l l' h).elim

def separate (N : ℕ) (F : ℕ → Set (Finset ℕ)) (a b : ℕ) :=
  (∀ u < N+N, ({u} : Finset ℕ) ∈ F a → ({u} : Finset ℕ) ∉ F b) ∧
  (∀ p l : Fin N, {p.val,N+l.val} ∈ F a ∩ F b →
    ({p.val} : Finset ℕ) ∈ F a ∧ ({N+l.val} : Finset ℕ) ∈ F b)
def markSteps (N s : ℕ) (M : Finset ℕ) (F : ℕ → Set (Finset ℕ)) :=
  ∀ j < s, ∃ a < N+N+j, ∃ b < N+N+j,
    F (N+N+j)=F a ∪ F b ∨ F (N+N+j)=F a ∨ F (N+N+j)=∅ ∨
    F (N+N+j)=F a ∩ F b ∧ (j∈M ∨ separate N F a b)
def cold (N s : ℕ) (M : Finset ℕ) (F : ℕ → Set (Finset ℕ)) (u : ℕ) :=
  ∀ j : Fin s, j.val∈M → ({u} : Finset ℕ) ∉ F (N+N+j.val)
def protectedFlag {N : ℕ} (s o : ℕ) (M : Finset ℕ) (F : ℕ → Set (Finset ℕ)) (p l : Fin N) :=
  cold N s M F p.val ∧ cold N s M F (N+l.val) ∧
  ∀ j : Fin s, j.val∈M → F (N+N+j.val) ⊆ F o → {p.val,N+l.val} ∉ F (N+N+j.val)

theorem protected_charge (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hq : 2≤q) (unique : ∀ p r : Fin N, p≠r → ∃! l : Fin N, I p l ∧ I r l)
    (s o : ℕ) (M : Finset ℕ) (F : ℕ → Set (Finset ℕ))
    (ho : o<N+N+s) (hin : ∀ i < N+N, F i = {Z | i∈Z})
    (hs : markSteps N s M F)
    (pos : ∀ p l : Fin N, I p l → {p.val,N+l.val}∈F o)
    (neg : negatives I q F o)
    (E : Finset (Fin N × Fin N))
    (he : ∀ p l : Fin N, (p,l)∈E → I p l ∧ protectedFlag s o M F p l) : E.card ≤ 2*s := by
  classical
  have hgate : GateSpec F (N+N) s := by
    intro j hj
    obtain ⟨a,ha,b,hb,k|k|k|k⟩ := hs j hj
    exact ⟨a,ha,b,hb,Or.inl k⟩
    exact ⟨a,ha,b,hb,Or.inr (Or.inl k)⟩
    exact ⟨a,ha,b,hb,Or.inr (Or.inr (Or.inl k))⟩
    exact ⟨a,ha,b,hb,Or.inr (Or.inr (Or.inr k.1))⟩
  have choices (j : Fin s) : ∃ a < N+N+j.val, ∃ b < N+N+j.val, ∃ op : ℕ,
      (op=0 ∧ F (N+N+j.val)=F a ∪ F b) ∨
      (op=1 ∧ F (N+N+j.val)=F a) ∨ (op=2 ∧ F (N+N+j.val)=∅) ∨
      (op=3 ∧ F (N+N+j.val)=F a ∩ F b ∧ (j.val∈M ∨ separate N F a b)) := by
    obtain ⟨a,ha,b,hb,k|k|k|k⟩ := hs j j.isLt
    exact ⟨a,ha,b,hb,0,Or.inl ⟨rfl,k⟩⟩
    exact ⟨a,ha,b,hb,1,Or.inr (Or.inl ⟨rfl,k⟩)⟩
    exact ⟨a,ha,b,hb,2,Or.inr (Or.inr (Or.inl ⟨rfl,k⟩))⟩
    exact ⟨a,ha,b,hb,3,Or.inr (Or.inr (Or.inr ⟨rfl,k⟩))⟩
  choose a ha b hb op hop using choices
  let U (i : ℕ) := (Finset.range (N+N)).filter (fun u => cold N s M F u ∧ ({u} : Finset ℕ) ∈ F i)
  have mem {i u : ℕ} : u∈U i ↔ u<N+N ∧ cold N s M F u ∧ ({u} : Finset ℕ)∈F i := by simp [U]
  have sound := soundPairs I F o hq neg
  refine charge N s I unique U a b op (fun j => ⟨ha j,hb j⟩) ?_ ?_ ?_ E ?_
  · intro j
    rcases hop j with ⟨k,_⟩|⟨k,_⟩|⟨k,_⟩|⟨k,_⟩ <;> omega
  · intro i hi
    calc
      (U i).card ≤ ({i} : Finset ℕ).card := by
        apply Finset.card_le_card
        intro u hu
        have hm := (mem.mp hu).2.2
        rw [hin i hi] at hm
        have eq : i=u := Finset.mem_singleton.mp hm
        simp [eq]
      _ = 1 := Finset.card_singleton _
  · intro j
    rcases hop j with ⟨k,e⟩|⟨k,e⟩|⟨k,e⟩|⟨k,e,mark⟩
    · refine ⟨fun _ => ?_,fun h => by omega,fun h => by omega⟩
      ext u
      simp only [Finset.mem_union,mem,e,Set.mem_union]
      tauto
    · exact ⟨fun h => by omega,fun _ => by simp [U,e],fun h => by omega⟩
    · refine ⟨fun h => by omega,fun h => by omega,fun _ => ?_⟩
      ext u; simp [mem,e]
    · refine ⟨fun h => by omega,fun h => by omega,fun _ => ?_⟩
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro u hu
      obtain ⟨bound,coldU,hx⟩ := mem.mp hu
      rcases mark with marked | sep
      · exact coldU j marked hx
      · rw [e] at hx
        exact sep.1 u bound hx.1 hx.2
  · intro p l hpl
    have props := he p l hpl
    obtain ⟨pi,li,good⟩ := props.2
    have hu : p.val<N+N := by have := p.isLt; omega
    have hv : N+l.val<N+N := by have := l.isLt; omega
    have tr (w : ℕ) (hw : w<N+N+s) (reach : F w ⊆ F o) (hwOn : {p.val,N+l.val}∈F w) :
        ∃ j : Fin s, op j=3 ∧ p.val∈U (a j) ∧ N+l.val∈U (b j) ∧
          F (N+N+j.val)=F (a j) ∩ F (b j) ∧ F (N+N+j.val) ⊆ F o := by
      induction w using Nat.strong_induction_on with
      | ind w ih =>
        by_cases wr : w<N+N
        · have single : ({w,w} : Finset ℕ) ∈ F w := by rw [hin w wr]; simp
          obtain ⟨p',l',_,⟨e1,e2⟩|⟨e1,e2⟩⟩ := sound w wr w wr (reach single)
          all_goals have := p'.isLt; omega
        let j : Fin s := ⟨w-(N+N),by omega⟩
        have eq : N+N+j.val=w := by dsimp [j]; omega
        have ar := ha j; have br := hb j
        rw [eq] at ar br
        rcases hop j with ⟨k,e⟩|⟨k,e⟩|⟨k,e⟩|⟨k,e,m⟩
        · rw [eq] at e
          rw [e] at hwOn reach
          rcases hwOn with on|on
          exact ih (a j) ar (ar.trans hw) (fun _ hx => reach (Or.inl hx)) on
          exact ih (b j) br (br.trans hw) (fun _ hx => reach (Or.inr hx)) on
        · rw [eq] at e
          rw [e] at hwOn reach
          exact ih (a j) ar (ar.trans hw) reach hwOn
        · rw [eq] at e
          rw [e] at hwOn
          exact hwOn.elim
        · have rex : F (N+N+j.val) ⊆ F o := by rw [eq]; exact reach
          have hit : {p.val,N+l.val} ∈ F (N+N+j.val) := by rwa [eq]
          rcases m with marked|sep
          · exact (good j marked rex hit).elim
          · have parts := sep.2 p l (e ▸ hit)
            exact ⟨j,k,mem.mpr ⟨hu,pi,parts.1⟩,mem.mpr ⟨hv,li,parts.2⟩,e,rex⟩
    obtain ⟨j,hj,pa,lb,e,rex⟩ := tr o ho (fun _ h => h) (pos p l props.1)
    refine ⟨j,hj,Or.inl ⟨pa,lb⟩,?_⟩
    intro u uok v vok
    obtain ⟨ur,-,ua⟩ := mem.mp uok
    obtain ⟨vr,-,vb⟩ := mem.mp vok
    apply sound u ur v vr
    apply rex
    rw [e]
    have cap : N+N+j.val < N+N+s := by have := j.isLt; omega
    refine ⟨evalX_mono hin hgate ?_ (a j) ((ha j).trans cap) ua,
      evalX_mono hin hgate ?_ (b j) ((hb j).trans cap) vb⟩
    · simp
    · simp
theorem assignment_pt_snd (N : ℕ) (p : Fin N) :
    (assignment N {p.val}).2 = (assignment N ∅).2 := by
  funext l
  have ne : N+l.val ≠ p.val := by omega
  simp [assignment,ne]
theorem assignment_ln_fst (N : ℕ) (l : Fin N) :
    (assignment N {N+l.val}).1 = (assignment N ∅).1 := by
  funext p
  have ne : p.val ≠ N+l.val := by omega
  simp [assignment,ne]
theorem assignment_pair_fst (N : ℕ) (p l : Fin N) :
    (assignment N {p.val,N+l.val}).1 = (assignment N {p.val}).1 := by
  funext r
  have ne : r.val ≠ N+l.val := by omega
  simp [assignment,ne]
theorem assignment_pair_snd (N : ℕ) (p l : Fin N) :
    (assignment N {p.val,N+l.val}).2 = (assignment N {N+l.val}).2 := by
  funext r
  have ne : N+r.val ≠ p.val := by omega
  simp [assignment,ne]

theorem sided {N s : ℕ} (W : ℕ → Set ((Fin N → Bool) × (Fin N → Bool)))
    (F : ℕ → Set (Finset ℕ)) (hF : ∀ i, F i=assignment N ⁻¹' W i)
    (hin : ∀ i < N+N, F i = {Z | i∈Z}) (hg : GateSpec F (N+N) s)
    {a b : ℕ} (ha : a<N+N+s) (hb : b<N+N+s)
    (A B : Set (Fin N → Bool)) (eA : W a=A ×ˢ Set.univ) (eB : W b=Set.univ ×ˢ B) :
    separate N F a b := by
  have pa (Z : Finset ℕ) : Z ∈ F a ↔ (assignment N Z).1 ∈ A := by simp [hF a,eA]
  have lb (Z : Finset ℕ) : Z ∈ F b ↔ (assignment N Z).2 ∈ B := by simp [hF b,eB]
  constructor
  · intro u hu ap bl
    by_cases hp : u<N
    · let p : Fin N := ⟨u,hp⟩
      have z := (lb {u}).mp bl
      change (assignment N {p.val}).2 ∈ B at z
      rw [assignment_pt_snd] at z
      exact not_evalX_empty hin hg hb ((lb ∅).mpr z)
    · let l : Fin N := ⟨u-N,by omega⟩
      have e : N+l.val=u := by dsimp [l]; omega
      have z := (pa {u}).mp ap
      rw [←e,assignment_ln_fst] at z
      exact not_evalX_empty hin hg ha ((pa ∅).mpr z)
  · intro p l on
    have xp := (pa _).mp on.1
    have yl := (lb _).mp on.2
    rw [assignment_pair_fst] at xp
    rw [assignment_pair_snd] at yl
    exact ⟨(pa _).mpr xp,(lb _).mpr yl⟩

lemma bridge (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hq : 2 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hdeg : ∀ l : Fin N, Fintype.card {p : Fin N // I p l} = q + 1)
    (huniq : ∀ p₁ p₂ : Fin N, p₁ ≠ p₂ → ∃! l : Fin N, I p₁ l ∧ I p₂ l)
    (s o : ℕ) (special : Finset ℕ) (W : ℕ → Set ((Fin N → Bool) × (Fin N → Bool)))
    (ho : o < N + N + s)
    (hwires : ∀ i : Fin N, W i.val = {z | z.1 i = true} ∧
      W (N + i.val) = {z | z.2 i = true})
    (hsteps : ∀ g < s, ∃ a < N + N + g, ∃ b < N + N + g,
      W (N + N + g) ∈ [W a ∪ W b, W a, ∅] ∨
      W (N + N + g) = W a ∩ W b ∧
        (g ∈ special ∨ ∃ A B : Set (Fin N → Bool),
          W a = A ×ˢ Set.univ ∧ W b = Set.univ ×ˢ B))
    (hpos : ∀ p l : Fin N, I p l →
      ((fun i : Fin N => decide (i = p)), (fun i : Fin N => decide (i = l))) ∈ W o)
    (hneg : ∀ Y : Fin N → Bool, Fintype.card {l : Fin N // Y l = true} ≤ q →
      permittedWire I Y ∉ W o) :
    ∀ E : Finset (Fin N × Fin N),
      (∀ p l : Fin N, (p,l)∈E → I p l ∧
        protectedFlag s o special (fun w => assignment N ⁻¹' W w) p l) →
      E.card ≤ 2*s := by
  let F : ℕ → Set (Finset ℕ) := fun w => assignment N ⁻¹' (W w)
  have hin : ∀ v < N + N, F v = {Z | v ∈ Z} := by
    intro v hv
    by_cases h : v < N
    · let i : Fin N := ⟨v, h⟩
      change F i.val = _
      simp [F, (hwires i).1, assignment, i]
    · let i : Fin N := ⟨v - N, by omega⟩
      have he : N + i.val = v := by dsimp [i]; omega
      rw [← he, show F (N + i.val) = assignment N ⁻¹' W (N + i.val) from rfl, (hwires i).2]
      simp [assignment]
  have hgate : GateSpec F (N + N) s := by
    intro g hg
    obtain ⟨a, ha, b, hb, h⟩ := hsteps g hg
    refine ⟨a, ha, b, hb, ?_⟩
    rcases h with h | ⟨h, _⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with h | h | h
      · left; simp [F, h, Set.preimage_union]
      · right; left; simp [F, h]
      · right; right; left; simp [F, h]
    · right; right; right; simp [F, h, Set.preimage_inter]
  have hmarked : markSteps N s special F := by
    intro j hj
    obtain ⟨a,ha,b,hb,k|⟨e,m⟩⟩ := hsteps j hj
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at k
      rcases k with e|e|e
      exact ⟨a,ha,b,hb,Or.inl (by simp [F,e,Set.preimage_union])⟩
      exact ⟨a,ha,b,hb,Or.inr (Or.inl (by simp [F,e]))⟩
      exact ⟨a,ha,b,hb,Or.inr (Or.inr (Or.inl (by simp [F,e])))⟩
    · refine ⟨a,ha,b,hb,Or.inr (Or.inr (Or.inr ⟨by simp [F,e,Set.preimage_inter],?_⟩))⟩
      rcases m with mark|⟨A,B,hA,hB⟩
      exact Or.inl mark
      exact Or.inr (sided W F (fun _ => rfl) hin hgate (by omega) (by omega) A B hA hB)
  intro E hE
  refine protected_charge q N I hq huniq s o special F ho hin hmarked ?_ ?_ E hE
  · intro p l h
    change assignment N {p.val, N + l.val} ∈ W o
    rw [assignment_pair]
    exact hpos p l h
  · intro T Z hT hZ hp hl h
    let Y : Fin N → Bool := fun l => decide (l ∈ T)
    have hY (l : Fin N) : Y l = true ↔ l ∈ T := by simp [Y]
    have hycard : Fintype.card {l : Fin N // Y l = true} ≤ q := by
      rw [Fintype.card_subtype]
      have he : Finset.univ.filter (fun l => Y l = true) = T := by
        ext l
        simp [hY]
      rwa [he]
    let A := (permittedWire I Y).1
    have hA (p : Fin N) : A p = true ↔ ¬ ∃ l : Fin N, I p l ∧ Y l = true := by
      simp [A, permittedWire]
    have hsub : Z ⊆ support A Y := by
      intro v hv
      have hvb := hZ v hv
      by_cases hvp : v < N
      · let p : Fin N := ⟨v, hvp⟩
        change p.val ∈ support A Y
        rw [mem_support_point, hA]
        rintro ⟨l, hpl, hly⟩
        exact hp p hv l ((hY l).mp hly) hpl
      · let l : Fin N := ⟨v - N, by omega⟩
        have he : N + l.val = v := by dsimp [l]; omega
        rw [← he, mem_support_line, hY]
        exact hl l (he ▸ hv)
    have hm := evalX_mono hin hgate hsub o ho h
    change assignment N (support A Y) ∈ W o at hm
    rw [assignment_support] at hm
    exact hneg Y hycard hm


theorem noMarks : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3],   (199 : ℕ) ≤ x1 →     x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →       (∀ (x7 : Fin x2), Fintype.card { x8 : Fin x2 // x3 x8 x7 } = x1 + (1 : ℕ)) →         (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x3 x8 x11 ∧ x3 x9 x11) →           ∀ (x9 x10 : ℕ) (x11 : Finset ℕ) (x12 : ℕ → Set ((Fin x2 → Bool) × (Fin x2 → Bool))),             have x13 : ℕ := x2 + x2;             have x14 : Fin x2 → Fin x2 → Bool := fun (x14 x15 : Fin x2) => Decidable.decide (x15 = x14);             x10 < x13 + x9 →               (∀ (x16 : Fin x2), x12 ↑x16 = {x17 : (Fin x2 → Bool) × (Fin x2 → Bool) | x17.1 x16 = Bool.true} ∧ x12 (x2 + ↑x16) = {x17 : (Fin x2 → Bool) × (Fin x2 → Bool) | x17.2 x16 = Bool.true}) →                 (∀ x17 < x9,                     ∃ x19 < x13 + x17,                       ∃ x20 < x13 + x17,                         have x21 : Set ((Fin x2 → Bool) × (Fin x2 → Bool)) := x12 (x13 + x17);                         x21 = x12 x19 ∪ x12 x20 ∨ x21 = x12 x19 ∨ x21 = ∅ ∨ x21 = x12 x19 ∩ x12 x20 ∧ (x17 ∈ x11 ∨ ∃ (x22 : Set (Fin x2 → Bool)) (x23 : Set (Fin x2 → Bool)), x12 x19 = x22 ×ˢ Set.univ ∧ x12 x20 = Set.univ ×ˢ x23)) →                   (∀ (x18 x19 : Fin x2), x3 x18 x19 → (x14 x18, x14 x19) ∈ x12 x10) → (∀ (x19 : Fin x2 → Bool), Fintype.card { x20 : Fin x2 // x19 x20 = Bool.true } ≤ x1 → (fun (x21 : Fin x2) => Decidable.decide ¬∃ (x22 : Fin x2), x3 x21 x22 ∧ x19 x22 = Bool.true, x19) ∉ x12 x10) → x11 = ∅ → x2 * (x1 + (1 : ℕ)) ≤ 2 * x9 := by
  intro q N I inst hq hN deg uniq s o M W
  dsimp only
  intro ho raw steps pos neg emptyM
  subst M
  let E := Finset.univ.filter (fun e : Fin N × Fin N => I e.1 e.2)
  have hE : E.card=N*(q+1) := incidence_card q N I deg
  rw [←hE]
  apply bridge q N I (by omega) hN deg uniq s o ∅ W ho raw ?_ pos neg E
  · intro j hj
    obtain ⟨a,ha,b,hb,e|e|e|e⟩ := steps j hj
    exact ⟨a,ha,b,hb,Or.inl (by simp [e])⟩
    exact ⟨a,ha,b,hb,Or.inl (by simp [e])⟩
    exact ⟨a,ha,b,hb,Or.inl (by simp [e])⟩
    exact ⟨a,ha,b,hb,Or.inr e⟩
  · intro p l h
    exact ⟨(Finset.mem_filter.mp h).2,by simp [protectedFlag,cold]⟩
end Flat8811

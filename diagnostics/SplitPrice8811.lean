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

end Flat8811
namespace Reset8811
inductive Source {n s : ℕ} (a b op : Fin s → ℕ) : ℕ → ℕ → Prop where
  | input (u : ℕ) (hu : u<n) : Source a b op u u
  | first (j : Fin s) (u : ℕ) (h : op j=0 ∨ op j=1) (earlier : Source a b op (a j) u) :
    Source a b op (n+j.val) u
  | second (j : Fin s) (u : ℕ) (h : op j=0) (earlier : Source a b op (b j) u) :
    Source a b op (n+j.val) u
theorem raw_src {n s : ℕ} {a b op : Fin s → ℕ} {w u : ℕ} (hw : w<n) :
    Source (n:=n) a b op w u ↔ w=u := by
  constructor
  · intro h
    cases h with
    | input => rfl
    | first => omega
    | second => omega
  · rintro rfl; exact Source.input _ hw
theorem step_src {n s : ℕ} {a b op : Fin s → ℕ} (j : Fin s) (u : ℕ) :
    Source (n:=n) a b op (n+j.val) u ↔
      ((op j=0 ∨ op j=1) ∧ Source (n:=n) a b op (a j) u) ∨
      (op j=0 ∧ Source (n:=n) a b op (b j) u) := by
  constructor
  · intro h
    generalize eq : n+j.val = w at h
    cases h with
    | input v hv => omega
    | first k v ho hprev =>
      have id : j=k := Fin.ext (by omega)
      subst k
      exact Or.inl ⟨ho,hprev⟩
    | second k v ho hprev =>
      have id : j=k := Fin.ext (by omega)
      subst k
      exact Or.inr ⟨ho,hprev⟩
  · rintro (⟨k,p⟩|⟨k,p⟩)
    exact .first j u k p
    exact .second j u k p

theorem maskBank {n s : ℕ} (a b op : Fin s → ℕ) (prior : ∀ j, a j<n+j.val ∧ b j<n+j.val)
    (tags : ∀ j, op j≤3) (U : ℕ → Finset ℕ) (inRaw : ∀ i<n, U i={i}) (M : Finset ℕ)
    (steps : ∀ j, (op j=0 → U (n+j.val)=U (a j)∪U (b j)) ∧
      (op j=1 → U (n+j.val)=U (a j)) ∧ (op j=2 → U (n+j.val)=∅) ∧
      (op j=3 → j.val∉M → U (n+j.val)=∅)) :
    ∃ H : ℕ → Finset ℕ, (∀ i<n, H i={i}) ∧ (∀ j,
      (op j=0 → H (n+j.val)=H (a j) ∪ H (b j)) ∧ (op j=1 → H (n+j.val)=H (a j)) ∧
      (2≤op j → H (n+j.val)=∅)) ∧
      (∀ w<n+s, H w⊆U w) ∧ (∀ w<n+s, ∀ u∈U w, u∉H w →
        ∃ j : Fin s, j.val∈M ∧ op j=3 ∧ u∈U (n+j.val) ∧ U (n+j.val)⊆U w) := by
  classical
  let H (w : ℕ) := (Finset.range n).filter (fun u => Source (n:=n) a b op w u)
  have mem (w u : ℕ) : u∈H w ↔ u<n ∧ Source (n:=n) a b op w u := by simp [H]
  have raw (i : ℕ) (hi : i<n) : H i={i} := by
    ext u; rw [mem,raw_src hi,Finset.mem_singleton]; omega
  have updates (j : Fin s) : (op j=0 → H (n+j.val)=H (a j) ∪ H (b j)) ∧
      (op j=1 → H (n+j.val)=H (a j)) ∧ (2≤op j → H (n+j.val)=∅) := by
    refine ⟨?_,?_,?_⟩
    · intro k; ext u; simp only [Finset.mem_union,mem,step_src,k]; tauto
    · intro k; ext u; simp [mem,step_src,k]
    · intro k; have no : op j≠0 := by omega
      have no' : op j≠1 := by omega
      ext u; simp [mem,step_src,no,no']
  have both (w : ℕ) (hw : w<n+s) : H w⊆U w ∧ (∀ u∈U w, u∉H w →
        ∃ j : Fin s, j.val∈M ∧ op j=3 ∧ u∈U (n+j.val) ∧ U (n+j.val)⊆U w) := by
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      by_cases wr : w<n
      · rw [raw w wr,inRaw w wr]
        exact ⟨fun _ h => h,fun u hu no => (no hu).elim⟩
      let j : Fin s := ⟨w-n,by omega⟩
      have eq : n+j.val=w := by dsimp [j]; omega
      have left := (prior j).1; have right := (prior j).2
      rw [eq] at left right
      have A := ih (a j) left (left.trans hw)
      have B := ih (b j) right (right.trans hw)
      rw [←eq]
      by_cases k : op j=0
      · rw [(updates j).1 k,(steps j).1 k]
        refine ⟨Finset.union_subset_union A.1 B.1,?_⟩
        intro u hu nm
        rcases Finset.mem_union.mp hu with hu|hu
        · obtain ⟨t,mt,ot,ht,st⟩ := A.2 u hu (fun h => nm (Finset.mem_union_left _ h))
          exact ⟨t,mt,ot,ht,st.trans Finset.subset_union_left⟩
        · obtain ⟨t,mt,ot,ht,st⟩ := B.2 u hu (fun h => nm (Finset.mem_union_right _ h))
          exact ⟨t,mt,ot,ht,st.trans Finset.subset_union_right⟩
      by_cases k1 : op j=1
      · rw [(updates j).2.1 k1,(steps j).2.1 k1]
        exact A
      rw [(updates j).2.2 (by omega)]
      constructor
      · exact Finset.empty_subset _
      intro u hu _
      have k3 : op j=3 := by
        have bound := tags j
        by_contra h
        rw [(steps j).2.2.1 (by omega)] at hu
        exact Finset.notMem_empty _ hu
      by_cases marked : j.val∈M
      · exact ⟨j,marked,k3,hu,Finset.Subset.rfl⟩
      · rw [(steps j).2.2.2 k3 marked] at hu
        exact (Finset.notMem_empty _ hu).elim
  exact ⟨H,raw,updates,fun w hw => (both w hw).1,fun w hw => (both w hw).2⟩
end Reset8811
namespace Flat8811
def edgeEnd {N : ℕ} (e : Fin N × Fin N) (u v : ℕ) :=
  (e.1.val=u ∧ N+e.2.val=v) ∨ (e.1.val=v ∧ N+e.2.val=u)
def anchored {N : ℕ} (I : Fin N → Fin N → Prop) (S : Finset ℕ) (e : Fin N × Fin N) :=
  ∃ u v, edgeEnd e u v ∧ u∈S ∧ ∀ w∈S, adj N I v w

theorem starQuota {q N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hcols : ∀ l, Fintype.card {p : Fin N // I p l}=q+1)
    (hrows : ∀ p, Fintype.card {l : Fin N // I p l}=q+1)
    (F : Finset (Fin N × Fin N)) (hit : ∀ e∈F, I e.1 e.2) (z : ℕ)
    (center : ∀ e∈F, e.1.val=z ∨ N+e.2.val=z) : F.card≤q+1 := by
  classical
  by_cases hp : z<N
  · let p : Fin N := ⟨z,hp⟩
    let S := Finset.univ.filter (fun l => I p l)
    have inc : F ⊆ S.image (fun l => (p,l)) := by
      intro e he
      have chosen := center e he
      have eq : e.1=p := Fin.ext (by rcases chosen with h|h <;> dsimp [p] <;> omega)
      exact Finset.mem_image.mpr ⟨e.2,Finset.mem_filter.mpr ⟨Finset.mem_univ _,eq ▸ hit e he⟩,
        by rw [←eq]⟩
    have sz : S.card=q+1 := by simpa [S,Fintype.card_subtype] using hrows p
    exact (Finset.card_le_card inc).trans (Finset.card_image_le.trans sz.le)
  · by_cases hn : z<N+N
    · let l : Fin N := ⟨z-N,by omega⟩
      let S := Finset.univ.filter (fun p => I p l)
      have inc : F ⊆ S.image (fun p => (p,l)) := by
        intro e he
        have chosen := center e he
        have bound := e.1.isLt
        have eq : e.2=l := Fin.ext (by rcases chosen with h|h <;> dsimp [l] <;> omega)
        exact Finset.mem_image.mpr ⟨e.1,Finset.mem_filter.mpr ⟨Finset.mem_univ _,eq ▸ hit e he⟩,
          by rw [←eq]⟩
      have sz : S.card=q+1 := by simpa [S,Fintype.card_subtype] using hcols l
      exact (Finset.card_le_card inc).trans (Finset.card_image_le.trans sz.le)
    · have empty : F=∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro e he
        have bound := e.1.isLt; have bound' := e.2.isLt
        rcases center e he with h|h <;> omega
      simp [empty]

theorem anchoredQuota {q N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (unique : ∀ p r : Fin N, p≠r → ∃! l : Fin N, I p l ∧ I r l)
    (hcols : ∀ l, Fintype.card {p : Fin N // I p l}=q+1)
    (hrows : ∀ p, Fintype.card {l : Fin N // I p l}=q+1)
    (S : Finset ℕ) (F : Finset (Fin N × Fin N)) (hit : ∀ e∈F, I e.1 e.2)
    (charged : ∀ e∈F, anchored I S e) : F.card ≤ q+1 := by
  classical
  by_cases ne : F.Nonempty
  · obtain ⟨e₀,he₀⟩ := ne
    obtain ⟨u₀,v₀,_,hu₀,nh₀⟩ := charged e₀ he₀
    by_cases width : 1 < S.card
    · obtain ⟨x,hx,y,hy,ne⟩ := Finset.one_lt_card.mp width
      apply starQuota I hcols hrows F hit v₀
      intro e he
      obtain ⟨u,v,ends,_,nh⟩ := charged e he
      have same : v=v₀ := commonUnique unique ne (nh x hx) (nh y hy) (nh₀ x hx) (nh₀ y hy)
      rcases ends with ⟨_,h⟩|⟨h,_⟩
      exact Or.inr (h.trans same)
      exact Or.inl (h.trans same)
    · have eq := singletonOf hu₀ (by omega)
      apply starQuota I hcols hrows F hit u₀
      intro e he
      obtain ⟨u,v,ends,hu,_⟩ := charged e he
      rw [eq,Finset.mem_singleton] at hu
      rcases ends with ⟨h,_⟩|⟨_,h⟩
      exact Or.inl (h.trans hu)
      exact Or.inr (h.trans hu)
  · simp [Finset.not_nonempty_iff_eq_empty.mp ne]
end Flat8811
namespace Flat8811
open Reset8811
theorem splitPrice {N q s : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hcols : ∀ l, Fintype.card {p : Fin N // I p l}=q+1)
    (hrows : ∀ p, Fintype.card {l : Fin N // I p l}=q+1)
    (unique : ∀ p r : Fin N, p≠r → ∃! l : Fin N, I p l ∧ I r l)
    (M : Finset ℕ) (a b op : Fin s → ℕ) (prior : ∀ j, a j<N+N+j.val ∧ b j<N+N+j.val)
    (tags : ∀ j, op j ≤ 3) (U : ℕ → Finset ℕ) (inRaw : ∀ i<N+N, U i={i})
    (steps : ∀ j, (op j=0 → U (N+N+j.val)=U (a j)∪U (b j)) ∧
      (op j=1 → U (N+N+j.val)=U (a j)) ∧ (op j=2 → U (N+N+j.val)=∅) ∧
      (op j=3 → j.val∉M → U (N+N+j.val)=∅))
    (E : Finset (Fin N × Fin N)) (edges : ∀ e∈E, I e.1 e.2)
    (term : ∀ e∈E, ∃ j : Fin s, op j=3 ∧
      ((e.1.val∈U (a j) ∧ N+e.2.val∈U (b j)) ∨ (N+e.2.val∈U (a j) ∧ e.1.val∈U (b j))) ∧
      ∀ u∈U (a j), ∀ v∈U (b j), adj N I u v) :
    E.card ≤ 2*s + (Finset.univ.filter (fun j : Fin s => j.val∈M)).card*(q+1) := by
  classical
  obtain ⟨H,hr,hs,sub,masks⟩ := maskBank a b op prior tags U inRaw M steps
  let J := Finset.univ.filter (fun j : Fin s => j.val∈M)
  let C (j : Fin s) := E.filter (fun e => anchored I (U (N+N+j.val)) e)
  let bad := J.biUnion C
  let rem := E \ bad
  have remBound : rem.card ≤ 2*s := by
    refine charge N s I unique H a b op prior tags (fun i hi => by rw [hr i hi]; simp) hs rem ?_
    intro p l hpl
    obtain ⟨epl,none⟩ := Finset.mem_sdiff.mp hpl
    obtain ⟨j,hj,pair,cross⟩ := term (p,l) epl
    have cap : N+N+j.val < N+N+s := by have := j.isLt; omega
    have ac := (prior j).1.trans cap; have bc := (prior j).2.trans cap
    have safe (u v r : ℕ) (hr₀ : r<N+N+s) (hu : u∈U r) (ends : edgeEnd (p,l) u v)
        (all : ∀ w∈U r, adj N I v w) : u∈H r := by
      by_contra no
      obtain ⟨t,mt,_,uu,ss⟩ := masks r hr₀ u hu no
      apply none
      exact Finset.mem_biUnion.mpr ⟨t,Finset.mem_filter.mpr ⟨Finset.mem_univ _,mt⟩,
        Finset.mem_filter.mpr ⟨epl,u,v,ends,uu,fun w hw => all w (ss hw)⟩⟩
    refine ⟨j,hj,?_,fun u hu v hv => cross u (sub _ ac hu) v (sub _ bc hv)⟩
    rcases pair with ⟨pa,lb⟩|⟨la,pb⟩
    · exact Or.inl ⟨safe _ _ _ ac pa (Or.inl ⟨rfl,rfl⟩) (fun w hw => adjSymm (cross w hw _ lb)),
        safe _ _ _ bc lb (Or.inr ⟨rfl,rfl⟩) (cross _ pa)⟩
    · exact Or.inr ⟨safe _ _ _ ac la (Or.inr ⟨rfl,rfl⟩) (fun w hw => adjSymm (cross w hw _ pb)),
        safe _ _ _ bc pb (Or.inl ⟨rfl,rfl⟩) (cross _ la)⟩
  have cost (j : Fin s) : (C j).card ≤ q+1 :=
    anchoredQuota I unique hcols hrows _ _ (fun e he => edges e (Finset.mem_filter.mp he).1)
      (fun _ he => (Finset.mem_filter.mp he).2)
  have total : bad.card ≤ J.card*(q+1) := calc
    _ ≤ ∑ j∈J, (C j).card := Finset.card_biUnion_le
    _ ≤ ∑ _j∈J, (q+1) := Finset.sum_le_sum (fun j _ => cost j)
    _ = _ := by simp
  have cover : E ⊆ rem ∪ bad := by
    intro e he
    by_cases h : e∈bad
    exact Finset.mem_union_right _ h
    exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨he,h⟩)
  exact ((Finset.card_le_card cover).trans (Finset.card_union_le _ _)).trans
    (Nat.add_le_add remBound total)
end Flat8811

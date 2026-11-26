import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3568

open PEqualNP.MetaComplexity.CoverPromise

variable {n : Nat} (G : SimpleGraph (Fin n))

theorem deleted_adj (z a b : Fin n) :
    (G.deleteEdges (G.incidenceSet z)).Adj a b ↔ G.Adj a b ∧ a ≠ z ∧ b ≠ z := by
  rw [SimpleGraph.deleteEdges_adj]
  constructor
  · rintro ⟨edge,noInc⟩
    refine ⟨edge,?_,?_⟩
    · rintro rfl
      exact noInc ⟨(SimpleGraph.mem_edgeSet G).2 edge,Sym2.mem_mk_left _ _⟩
    · rintro rfl
      exact noInc ⟨(SimpleGraph.mem_edgeSet G).2 edge,Sym2.mem_mk_right _ _⟩
  · rintro ⟨edge,az,bz⟩
    refine ⟨edge,?_⟩
    rintro ⟨_,h⟩
    rcases Sym2.mem_iff.1 h with ha | hb
    · exact az ha.symm
    · exact bz hb.symm

theorem drop_iff_minimal_cover_through (z : Fin n) :
    (∃ S : Finset (Fin n), IsVertexCover (G.deleteEdges (G.incidenceSet z)) S ∧
       ∀ T, IsVertexCover G T → S.card < T.card) ↔
    ∃ T : Finset (Fin n), IsVertexCover G T ∧ z ∈ T ∧
       ∀ U, IsVertexCover G U → T.card ≤ U.card := by
  classical
  constructor
  · rintro ⟨S,hS,small⟩
    have c : IsVertexCover G (insert z S) := by
      intro a b edge
      by_cases az : a=z
      · exact Or.inl (by simp [az])
      by_cases bz : b=z
      · exact Or.inr (by simp [bz])
      exact (hS a b ((deleted_adj G z a b).2 ⟨edge,az,bz⟩)).imp
        (Finset.mem_insert_of_mem) (Finset.mem_insert_of_mem)
    refine ⟨insert z S,c,Finset.mem_insert_self _ _,?_⟩
    intro U hU
    exact (Finset.card_insert_le z S).trans (small U hU)
  · rintro ⟨T,c,zt,least⟩
    refine ⟨T.erase z,?_,?_⟩
    · intro a b e
      obtain ⟨edge,az,bz⟩ := (deleted_adj G z a b).1 e
      exact (c a b edge).imp (fun ha => Finset.mem_erase.mpr ⟨az,ha⟩)
        (fun hb => Finset.mem_erase.mpr ⟨bz,hb⟩)
    · intro U hU
      have := Finset.card_erase_add_one zt
      have := least U hU
      omega

def EdgeOn (X : Finset (Fin n)) := ∃ a ∈ X, ∃ b ∈ X, G.Adj a b

theorem twin_merge (a b : Fin n) (hne : a ≠ b)
    (tw : ∀ y, G.Adj a y ↔ G.Adj b y) (X : Finset (Fin n)) :
    EdgeOn G X ↔ EdgeOn (G.deleteEdges (G.incidenceSet a))
      (if a ∈ X then insert b (X.erase a) else X) := by
  classical
  by_cases ha : a ∈ X
  · rw [if_pos ha]
    constructor
    · rintro ⟨u,hu,v,hv,edge⟩
      by_cases ua : u=a
      · subst u
        have va : v ≠ a := fun e => G.loopless.irrefl a (e ▸ edge)
        exact ⟨b,Finset.mem_insert_self _ _,v,Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨va,hv⟩),
          (deleted_adj G a _ _).2 ⟨(tw v).1 edge,Ne.symm hne,va⟩⟩
      by_cases va : v=a
      · subst v
        exact ⟨u,Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨ua,hu⟩),b,Finset.mem_insert_self _ _,
          (deleted_adj G a _ _).2 ⟨((tw u).1 edge.symm).symm,ua,Ne.symm hne⟩⟩
      exact ⟨u,Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨ua,hu⟩),
        v,Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨va,hv⟩),(deleted_adj G a _ _).2 ⟨edge,ua,va⟩⟩
    · rintro ⟨u,hu,v,hv,e⟩
      have edge := ((deleted_adj G a _ _).1 e).1
      rcases Finset.mem_insert.mp hu with eu | hu'
      · subst u
        rcases Finset.mem_insert.mp hv with ev | hv'
        · subst v
          exact False.elim (G.loopless.irrefl _ edge)
        · exact ⟨a,ha,v,(Finset.mem_erase.mp hv').2,(tw v).2 edge⟩
      · rcases Finset.mem_insert.mp hv with ev | hv'
        · subst v
          exact ⟨u,(Finset.mem_erase.mp hu').2,a,ha,((tw u).2 edge.symm).symm⟩
        · exact ⟨u,(Finset.mem_erase.mp hu').2,v,(Finset.mem_erase.mp hv').2,edge⟩
  · rw [if_neg ha]
    constructor
    · rintro ⟨u,hu,v,hv,e⟩
      exact ⟨u,hu,v,hv,(deleted_adj G a _ _).2
        ⟨e,fun eq => ha (eq ▸ hu),fun eq => ha (eq ▸ hv)⟩⟩
    · rintro ⟨u,hu,v,hv,e⟩
      exact ⟨u,hu,v,hv,((deleted_adj G a _ _).1 e).1⟩

end PEqualNP.Outside.L_meta_3568
namespace PEqualNP.Outside.L_meta_3568.LocalCover

open PEqualNP.MetaComplexity.CoverPromise

variable {n : Nat}
abbrev V := Fin n

def Minimum (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) : Prop :=
  IsVertexCover G A ∧ ∀ B, IsVertexCover G B → A.card ≤ B.card

def mix (L A B : Finset (Fin n)) := ((A ∪ B) ∩ L) ∪ ((A ∩ B) \ L)

theorem mem_mix (L A B : Finset (Fin n)) (v : Fin n) :
    v ∈ mix L A B ↔ ((v ∈ A ∨ v ∈ B) ∧ v ∈ L) ∨ ((v ∈ A ∧ v ∈ B) ∧ v ∉ L) := by
  simp [mix]

theorem mix_cover (G : SimpleGraph (Fin n)) (L A B : Finset (Fin n))
    (bip : ∀ a b, G.Adj a b → (a ∈ L ↔ b ∉ L)) (ha : IsVertexCover G A)
    (hb : IsVertexCover G B) : IsVertexCover G (mix L A B) := by
  intro a b e
  have h := bip a b e
  have c := ha a b e
  have d := hb a b e
  rw [mem_mix,mem_mix]
  tauto

theorem mix_card (L A B : Finset (Fin n)) :
    (mix L A B).card + (mix Lᶜ A B).card = A.card + B.card := by
  classical
  have expand (S : Finset (Fin n)) :
      S.card = ∑ v : Fin n, (if v ∈ S then 1 else 0 : Nat) := by simp
  conv_lhs => rw [expand (mix L A B),expand (mix Lᶜ A B),← Finset.sum_add_distrib]
  conv_rhs => rw [expand A,expand B,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro v _
  by_cases h : v ∈ L <;> by_cases a : v ∈ A <;> by_cases b : v ∈ B <;>
    simp [mem_mix,h,a,b]

theorem min_mix (G : SimpleGraph (Fin n)) (L A B : Finset (Fin n))
    (bip : ∀ a b, G.Adj a b → (a ∈ L ↔ b ∉ L)) (ha : Minimum G A)
    (hb : Minimum G B) : Minimum G (mix L A B) := by
  have bip' : ∀ a b, G.Adj a b → (a ∈ Lᶜ ↔ b ∉ Lᶜ) := by
    intro a b e
    have h := bip a b e
    simp only [Finset.mem_compl,not_not]
    tauto
  have c := mix_cover G L A B bip ha.1 hb.1
  have d := mix_cover G Lᶜ A B bip' ha.1 hb.1
  have ca := ha.2 _ c
  have cb := hb.2 _ d
  have eq := mix_card L A B
  refine ⟨c, fun S hS => ?_⟩
  have := ha.2 S hS
  omega

theorem exists_min (G : SimpleGraph (Fin n)) : ∃ A, Minimum G A := by
  classical
  let cvs := Finset.univ.filter fun U : Finset (Fin n) => IsVertexCover G U
  have hu : (Finset.univ : Finset (Fin n)) ∈ cvs := Finset.mem_filter.mpr
    ⟨Finset.mem_univ _,fun a _ _ => Or.inl (Finset.mem_univ a)⟩
  obtain ⟨A,ha,least⟩ := Finset.exists_min_image cvs Finset.card ⟨_,hu⟩
  exact ⟨A,(Finset.mem_filter.mp ha).2,fun S hS =>
    least _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hS⟩)⟩

theorem extreme (G : SimpleGraph (Fin n)) (L : Finset (Fin n))
    (bip : ∀ a b, G.Adj a b → (a ∈ L ↔ b ∉ L)) :
    ∃ A, Minimum G A ∧ ∀ B, Minimum G B → ∀ v ∈ L, v ∈ B → v ∈ A := by
  classical
  let mins := Finset.univ.filter fun S : Finset (Fin n) => Minimum G S
  obtain ⟨S,hs⟩ := exists_min G
  have sm : S ∈ mins := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hs⟩
  obtain ⟨A,ha,maximal⟩ := Finset.exists_max_image mins (fun B => (B ∩ L).card) ⟨_,sm⟩
  have ma : Minimum G A := (Finset.mem_filter.mp ha).2
  refine ⟨A,ma,?_⟩
  intro B mb v vl vb
  by_contra va
  have natbound := maximal (mix L A B) (Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, min_mix G L A B bip ma mb⟩)
  have sub : insert v (A ∩ L) ⊆ mix L A B ∩ L := by
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl | h
    · exact Finset.mem_inter.mpr ⟨(mem_mix ..).mpr (Or.inl ⟨Or.inr vb,vl⟩),vl⟩
    · obtain ⟨wa,wl⟩ := Finset.mem_inter.mp h
      exact Finset.mem_inter.mpr ⟨(mem_mix ..).mpr (Or.inl ⟨Or.inl wa,wl⟩),wl⟩
  have ub := Finset.card_le_card sub
  have nv : v ∉ A ∩ L := fun h => va (Finset.mem_inter.mp h).1
  rw [Finset.card_insert_of_notMem nv] at ub
  omega

theorem drop_iff_excluded_neighbor (G : SimpleGraph (Fin n)) (z : Fin n)
    (c : Fin n → Bool) (bip : ∀ a b, G.Adj a b → c a ≠ c b) :
    (∃ S : Finset (Fin n), IsVertexCover (G.deleteEdges (G.incidenceSet z)) S ∧
       ∀ T, IsVertexCover G T → S.card < T.card) ↔
    ∃ v, G.Adj z v ∧ ∀ S, Minimum (G.deleteEdges (G.incidenceSet z)) S → v ∉ S := by
  classical
  let H := G.deleteEdges (G.incidenceSet z)
  let L := Finset.univ.filter fun a => c a ≠ c z
  have part : ∀ a b, H.Adj a b → (a ∈ L ↔ b ∉ L) := by
    intro a b e
    have ne := bip a b ((deleted_adj G z a b).mp e).1
    simp only [L,Finset.mem_filter,Finset.mem_univ,true_and,not_not]
    cases ea : c a <;> cases eb : c b <;> cases ez : c z <;> simp_all
  constructor
  · rintro ⟨S,hs,drop⟩
    obtain ⟨A,ma,ex⟩ := extreme H L part
    by_contra! no
    have extends : IsVertexCover G A := by
      intro a b e
      by_cases az : a = z
      · subst a
        obtain ⟨B,mb,bB⟩ := no b e
        exact Or.inr (ex B mb b (Finset.mem_filter.mpr ⟨Finset.mem_univ _, (bip _ _ e).symm⟩) bB)
      by_cases bz : b = z
      · subst b
        obtain ⟨B,mb,aB⟩ := no a e.symm
        exact Or.inl (ex B mb a (Finset.mem_filter.mpr ⟨Finset.mem_univ _, bip _ _ e⟩) aB)
      exact ma.1 a b ((deleted_adj G z a b).mpr ⟨e,az,bz⟩)
    exact (Nat.not_lt_of_ge (ma.2 S hs)) (drop A extends)
  · rintro ⟨v,adj,absent⟩
    obtain ⟨A,ma⟩ := exists_min H
    refine ⟨A,ma.1,?_⟩
    intro B hb
    have hbH : IsVertexCover H B := fun a b e => hb a b ((deleted_adj G z a b).mp e).1
    have ab := ma.2 B hbH
    by_contra! bad
    have mb : Minimum H B := ⟨hbH,fun D hD => bad.trans (ma.2 D hD)⟩
    have zb := (hb z v adj).resolve_right (absent B mb)
    have her : IsVertexCover H (B.erase z) := by
      intro a b e
      obtain ⟨ed,az,bz⟩ := (deleted_adj G z a b).mp e
      exact (hb a b ed).imp (fun h => Finset.mem_erase.mpr ⟨az,h⟩)
        (fun h => Finset.mem_erase.mpr ⟨bz,h⟩)
    have m := mb.2 _ her
    have s := Finset.card_erase_add_one zb
    omega

end PEqualNP.Outside.L_meta_3568.LocalCover

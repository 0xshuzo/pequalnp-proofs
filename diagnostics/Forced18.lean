import PEqualNP.Defs
namespace A17379
abbrev Col := Finset (Fin 285)
def canJoin (bank : List Col) (w : Col) : Prop :=
  ∃ a∈bank,∃ b∈bank, ¬a⊆b ∧ ¬b⊆a ∧ w=a∪b

noncomputable def paid {N : ℕ} (P : Fin N → Prop) : ℕ := by
  classical
  exact (Finset.univ.filter P).card

theorem counted {N b : ℕ} (P : Fin N → Prop) :
    (∀ (m : ℕ) (f : Fin m → ℕ), Function.Injective f →
        (∀ j,∃ h : f j<N, ¬P ⟨f j,h⟩) → b+m≤N) ↔ b≤paid P := by
  classical
  let A := Finset.univ.filter (fun i : Fin N => ¬P i)
  have sum : paid P + A.card=N := by
    simpa [paid,A] using Finset.card_filter_add_card_filter_not (s:=Finset.univ) P
  constructor
  · intro hyp
    let eq : A ≃ Fin A.card := Fintype.equivFinOfCardEq (by simp)
    let f (j : Fin A.card) : ℕ := (eq.symm j).1.val
    have inj : Function.Injective f := by
      intro i j ij
      apply eq.symm.injective
      apply Subtype.ext
      exact Fin.ext ij
    have test (j : Fin A.card) : ∃ h : f j<N, ¬P ⟨f j,h⟩ := by
      refine ⟨(eq.symm j).1.isLt,?_⟩
      exact (Finset.mem_filter.mp (eq.symm j).property).2
    have lower := hyp A.card f inj test
    omega
  · intro bound m f inj hit
    let g (j : Fin m) : A := ⟨⟨f j,(hit j).choose⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,(hit j).choose_spec⟩⟩
    have gi : Function.Injective g := by
      intro i j ij
      exact inj (congrArg (fun a : A => a.1.val) ij)
    have sm : m≤A.card := by simpa using Fintype.card_le_of_injective g gi
    omega

def admissible (raw L : List Col) := ∀ i : Fin L.length,
  let B := raw++L.take i.val
  ∃ a∈B,∃ b∈B,¬a⊆b ∧ ¬b⊆a ∧ L.get i ∉ B ∧ (L.get i=a∩b ∨ L.get i=a∪b)
def cap (raw L : List Col) (target : Col) :=
  ∃ a∈raw++L,∃ b∈raw++L,¬a⊆b ∧ ¬b⊆a ∧ a∩b=target

def reps : List ℕ := [(8193 : ℕ), (8194 : ℕ), (8200 : ℕ), (8704 : ℕ), (21233693 : ℕ), (3211303 : ℕ), (7340103 : ℕ), (23068749 : ℕ), (5275731 : ℕ), (22020181 : ℕ), (19923045 : ℕ), (18890857 : ℕ), (6357127 : ℕ), (6553741 : ℕ), (6324419 : ℕ), (6308041 : ℕ), (4751635 : ℕ), (21496089 : ℕ), (17318185 : ℕ), (20988233 : ℕ), (21004625 : ℕ), (17891877 : ℕ)]
def raw : List Col := List.map (fun (x2 : ℕ) => (List.filter (fun (x3 : Fin (285 : ℕ)) => (reps.getD ((↑x3 + (1 : ℕ)) / (13 : ℕ)) (0 : ℕ)).testBit (x2 / (13 : ℕ) * (13 : ℕ) + (x2 + (13 : ℕ) - (↑x3 + (1 : ℕ)) % (13 : ℕ)) % (13 : ℕ))) (List.finRange (285 : ℕ))).toFinset) (List.range (26 : ℕ))
def target : Col := (List.filter (fun (x9 : Fin 285) => decide (↑x9 < (51 : ℕ))) (List.finRange 285)).toFinset
def pay (L : List Col) (i : Fin L.length) := canJoin (raw++L.take i.val) (L.getD i.val ∅)
theorem semantic_iff : (have x1 : List ℕ := [(8193 : ℕ), (8194 : ℕ), (8200 : ℕ), (8704 : ℕ), (21233693 : ℕ), (3211303 : ℕ), (7340103 : ℕ), (23068749 : ℕ), (5275731 : ℕ), (22020181 : ℕ), (19923045 : ℕ), (18890857 : ℕ), (6357127 : ℕ), (6553741 : ℕ), (6324419 : ℕ), (6308041 : ℕ), (4751635 : ℕ), (21496089 : ℕ), (17318185 : ℕ), (20988233 : ℕ), (21004625 : ℕ), (17891877 : ℕ)]; have x2 : List (Finset (Fin (285 : ℕ))) := List.map (fun (x2 : ℕ) => (List.filter (fun (x3 : Fin (285 : ℕ)) => (x1.getD ((↑x3 + (1 : ℕ)) / (13 : ℕ)) (0 : ℕ)).testBit (x2 / (13 : ℕ) * (13 : ℕ) + (x2 + (13 : ℕ) - (↑x3 + (1 : ℕ)) % (13 : ℕ)) % (13 : ℕ))) (List.finRange (285 : ℕ))).toFinset) (List.range (26 : ℕ)); ∀ (x3 : List (Finset (Fin (285 : ℕ)))) (x4 : ℕ) (x5 : Fin x4 → ℕ),   (∀ (x6 : Fin x3.length),       have x7 : List (Finset (Fin (285 : ℕ))) := x2 ++ List.take (↑x6) x3;       ∃ x8 ∈ x7, ∃ x9 ∈ x7, ¬x8 ⊆ x9 ∧ ¬x9 ⊆ x8 ∧ x3.get x6 ∉ x7 ∧ (x3.get x6 = x8 ∩ x9 ∨ x3.get x6 = x8 ∪ x9)) →     (∃ x7 ∈ x2 ++ x3, ∃ x8 ∈ x2 ++ x3, ¬x7 ⊆ x8 ∧ ¬x8 ⊆ x7 ∧ x7 ∩ x8 = (List.filter (fun (x9 : Fin (285 : ℕ)) => Decidable.decide (↑x9 < (51 : ℕ))) (List.finRange (285 : ℕ))).toFinset) → Function.Injective x5 → (∀ (x9 : Fin x4), x5 x9 < x3.length ∧ ¬∃ x10 ∈ x2 ++ List.take (x5 x9) x3, ∃ x11 ∈ x2 ++ List.take (x5 x9) x3, ¬x10 ⊆ x11 ∧ ¬x11 ⊆ x10 ∧ x3.getD (x5 x9) ∅ = x10 ∪ x11) → (50 : ℕ) + x4 ≤ x3.length) ↔ ∀ L, admissible raw L → cap raw L target → 50≤paid (pay L) := by
  constructor
  · intro h L ha hc
    apply (counted (pay L)).mp
    intro m f inj hf
    apply h L m f ha hc inj
    intro j
    obtain ⟨bound,no⟩ := hf j
    exact ⟨bound,no⟩
  · intro h L m f valid capH inj tests
    apply (counted (pay L)).mpr (h L valid capH) m f inj
    intro j
    exact ⟨(tests j).1,(tests j).2⟩

end A17379

namespace A17379
noncomputable instance canJoinDec (B : List Col) (w : Col) : Decidable (canJoin B w) := Classical.propDecidable _

def bank (base L : List Col) (i : ℕ) := base++L.take i
noncomputable def falseJoins (base L : List Col) (q : Fin 285) (i : ℕ) := by
  classical
  exact ((Finset.range i).filter fun j => canJoin (bank base L j) (L.getD j ∅) ∧ q∉L.getD j ∅).card

theorem false_succ (base L : List Col) (q : Fin 285) (i : ℕ) :
    falseJoins base L q (i+1) = falseJoins base L q i+
      (if canJoin (bank base L i) (L.getD i ∅) ∧ q∉L.getD i ∅ then 1 else 0) := by
  classical
  by_cases ch : canJoin (bank base L i) (L.getD i ∅) ∧ q∉L.getD i ∅ <;>
    simp [falseJoins,Finset.range_add_one,Finset.filter_insert,ch]

def Covers (R S : Finset Col) := ∀ w∈S,∀ p∈w,∃ r∈R,p∈r

theorem expand_cover (base L : List Col) (allow : admissible base L) (q : Fin 285) (i : ℕ)
    (bound : i≤L.length) (S : Finset Col) (valid : ∀ w∈S,w∈bank base L i ∧ q∉w) :
    ∃ R : Finset Col, (∀ r∈R,r∈base ∧ q∉r) ∧ Covers R S ∧ R.card≤S.card+falseJoins base L q i := by
  classical
  induction i generalizing S with
  | zero =>
    exact ⟨S,by simpa [bank] using valid,fun w hw p hp => ⟨w,hw,hp⟩,by simp [falseJoins]⟩
  | succ i ih =>
    have hi : i<L.length := by omega
    let w := L[i]
    have snoc : bank base L (i+1)=bank base L i++[w] := by
      simp [bank,w,List.take_succ_eq_append_getElem hi,List.append_assoc]
    have old (z : Col) (hz : z∈S) (ne : z≠w) : z∈bank base L i ∧ q∉z := by
      obtain ⟨h,hq⟩ := valid z hz
      rw [snoc] at h
      exact ⟨(List.mem_append.mp h).resolve_right (by simpa using ne),hq⟩
    have d : L.getD i ∅=w := List.getD_eq_getElem _ _ hi
    by_cases hw : w∈S
    · have hq := (valid w hw).2
      obtain ⟨a,ha,b,hb,ab,ba,new,role⟩ := allow ⟨i,hi⟩
      change w=a∩b ∨ w=a∪b at role
      let S0 := S.erase w
      have prev (z : Col) (hz : z∈S0) := old z (Finset.mem_erase.mp hz).2 (Finset.mem_erase.mp hz).1
      have sz : S0.card+1=S.card := by simp [S0,Finset.card_erase_add_one hw]
      have transfer (K : Finset Col) (hk : ∀ z∈K,z∈bank base L i ∧ q∉z)
          (enough : ∀ p∈w, ∃ z∈K,p∈z) (budget : K.card≤
            1+(if canJoin (bank base L i) (L.getD i ∅) ∧ q∉L.getD i ∅ then 1 else 0)) :
          ∃ R : Finset Col, (∀ r∈R,r∈base ∧ q∉r) ∧ Covers R S ∧
            R.card≤S.card+falseJoins base L q (i+1) := by
        have good : ∀ z∈S0∪K,z∈bank base L i ∧ q∉z := fun z hz =>
          (Finset.mem_union.mp hz).elim (prev z) (hk z)
        obtain ⟨R,rawR,cov,size⟩ := ih hi.le _ good
        refine ⟨R,rawR,?_,?_⟩
        · intro z hz p hp
          by_cases eq : z=w
          · obtain ⟨v,hv,pv⟩ := enough p (eq ▸ hp)
            exact cov v (Finset.mem_union_right _ hv) p pv
          · exact cov z (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨eq,hz⟩)) p hp
        · have u := Finset.card_union_le S0 K
          rw [false_succ]
          omega
      rcases role with meet|join
      · have small (v : Col) (hv : v∈bank base L i) (all : w⊆v) (falseV : q∉v) :
          ∃ R : Finset Col, (∀ r∈R,r∈base ∧ q∉r) ∧ Covers R S ∧ R.card≤S.card+falseJoins base L q (i+1) := by
          apply transfer {v}
          · intro z hz
            rw [Finset.mem_singleton.mp hz]
            exact ⟨hv,falseV⟩
          · exact fun p hp => ⟨v,Finset.mem_singleton_self _,all hp⟩
          · simp
        have wa : w⊆a := by rw [meet]; exact Finset.inter_subset_left
        have wb : w⊆b := by rw [meet]; exact Finset.inter_subset_right
        by_cases qa : q∈a
        · apply small b hb wb
          exact fun qb => hq (by rw [meet]; exact Finset.mem_inter.mpr ⟨qa,qb⟩)
        · exact small a ha wa qa
      · have yes : canJoin (bank base L i) (L.getD i ∅) ∧ q∉L.getD i ∅ := by
          rw [d]
          exact ⟨⟨a,ha,b,hb,ab,ba,join⟩,hq⟩
        apply transfer {a,b}
        · intro z hz
          rcases (show z=a ∨ z=b by simpa using hz) with rfl|rfl
          · exact ⟨ha,fun h => hq (by rw [join]; exact Finset.mem_union_left _ h)⟩
          · exact ⟨hb,fun h => hq (by rw [join]; exact Finset.mem_union_right _ h)⟩
        · intro p hp
          rcases Finset.mem_union.mp (join ▸ hp) with h|h
          · exact ⟨a,by simp,h⟩
          · exact ⟨b,by simp,h⟩
        · simpa [yes] using Finset.card_insert_le a ({b} : Finset Col)
    · have v : ∀ z∈S,z∈bank base L i ∧ q∉z := fun z hz => old z hz (fun e=>hw (e ▸ hz))
      obtain ⟨R,hR,cov,size⟩ := ih hi.le S v
      exact ⟨R,hR,cov,by rw [false_succ];omega⟩

end A17379
namespace A17379

def witnesses : Finset (Fin 285) := {43,47,17,49,30,8,21,10,34,25,26,14,15,42,44,45,46,35,37}
theorem witnesses_card : witnesses.card=19 := by decide +kernel
theorem witnesses_flags : witnesses⊆target := by decide +kernel
theorem excluded : (51 : Fin 285)∉target := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
theorem one_per_raw : ∀ z∈raw, (51 : Fin 285)∉z → (z∩witnesses).card≤1 := by decide +kernel

theorem separation_cost (L : List Col) (h : admissible raw L) (c : cap raw L target) :
    18≤falseJoins raw L (51 : Fin 285) L.length := by
  classical
  obtain ⟨a,ha,b,hb,_,_,meet⟩ := c
  have solve (z : Col) (hz : z∈raw++L) (goal : target⊆z) (neg : (51 : Fin 285)∉z) :
      18≤falseJoins raw L (51 : Fin 285) L.length := by
    obtain ⟨R,hR,cov,sz⟩ := expand_cover raw L h 51 L.length le_rfl {z} (by
      intro w hw
      rw [Finset.mem_singleton.mp hw]
      exact ⟨by simpa [bank] using hz,neg⟩)
    have inc : witnesses ⊆ R.biUnion (fun v => v∩witnesses) := by
      intro p hp
      obtain ⟨r,hr,hit⟩ := cov z (Finset.mem_singleton_self _) p (goal (witnesses_flags hp))
      exact Finset.mem_biUnion.mpr ⟨r,hr,Finset.mem_inter.mpr ⟨hit,hp⟩⟩
    have total : witnesses.card≤R.card := calc
      _ ≤ _ := Finset.card_le_card inc
      _ ≤ _ := Finset.card_biUnion_le
      _ ≤ ∑ _∈R, (1:ℕ) := Finset.sum_le_sum (fun r hr => one_per_raw r (hR r hr).1 (hR r hr).2)
      _ = _ := by simp
    rw [witnesses_card] at total
    simp only [Finset.card_singleton] at sz
    omega
  have ta : target⊆a := by rw [←meet];exact Finset.inter_subset_left
  have tb : target⊆b := by rw [←meet];exact Finset.inter_subset_right
  by_cases qa : (51 : Fin 285)∈a
  · apply solve b hb tb
    exact fun qb => excluded (meet ▸ Finset.mem_inter.mpr ⟨qa,qb⟩)
  · exact solve a ha ta qa

theorem marked_add (L : List Col) (q : Fin 285) (m : ℕ) (f : Fin m→ℕ) (inj : Function.Injective f)
    (notJoin : ∀ j, f j<L.length ∧ ¬canJoin (bank raw L (f j)) (L.getD (f j) ∅)) :
    m+falseJoins raw L q L.length ≤ L.length := by
  classical
  let A := Finset.univ.image f
  let B := (Finset.range L.length).filter (fun j => canJoin (bank raw L j) (L.getD j ∅) ∧ q∉L.getD j ∅)
  have dis : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro n ha hb
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp ha
    exact (notJoin j).2 (Finset.mem_filter.mp hb).2.1
  have sub : A∪B ⊆ Finset.range L.length := by
    intro n hn
    rcases Finset.mem_union.mp hn with h|h
    · obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp h
      exact Finset.mem_range.mpr (notJoin j).1
    · exact (Finset.mem_filter.mp h).1
  have card := Finset.card_le_card sub
  rw [Finset.card_union_of_disjoint dis,Finset.card_range] at card
  simpa [A,B,falseJoins,Finset.card_image_of_injective _ inj] using card


theorem partial_goal : have x1 : List ℕ := [(8193 : ℕ), (8194 : ℕ), (8200 : ℕ), (8704 : ℕ), (21233693 : ℕ), (3211303 : ℕ), (7340103 : ℕ), (23068749 : ℕ), (5275731 : ℕ), (22020181 : ℕ), (19923045 : ℕ), (18890857 : ℕ), (6357127 : ℕ), (6553741 : ℕ), (6324419 : ℕ), (6308041 : ℕ), (4751635 : ℕ), (21496089 : ℕ), (17318185 : ℕ), (20988233 : ℕ), (21004625 : ℕ), (17891877 : ℕ)]; have x2 : List (Finset (Fin (285 : ℕ))) := List.map (fun (x2 : ℕ) => (List.filter (fun (x3 : Fin (285 : ℕ)) => (x1.getD ((↑x3 + (1 : ℕ)) / (13 : ℕ)) (0 : ℕ)).testBit (x2 / (13 : ℕ) * (13 : ℕ) + (x2 + (13 : ℕ) - (↑x3 + (1 : ℕ)) % (13 : ℕ)) % (13 : ℕ))) (List.finRange (285 : ℕ))).toFinset) (List.range (26 : ℕ)); ∀ (x3 : List (Finset (Fin (285 : ℕ)))) (x4 : ℕ) (x5 : Fin x4 → ℕ),   (∀ (x6 : Fin x3.length),       have x7 : List (Finset (Fin (285 : ℕ))) := x2 ++ List.take (↑x6) x3;       ∃ x8 ∈ x7, ∃ x9 ∈ x7, ¬x8 ⊆ x9 ∧ ¬x9 ⊆ x8 ∧ x3.get x6 ∉ x7 ∧ (x3.get x6 = x8 ∩ x9 ∨ x3.get x6 = x8 ∪ x9)) →     (∃ x7 ∈ x2 ++ x3, ∃ x8 ∈ x2 ++ x3, ¬x7 ⊆ x8 ∧ ¬x8 ⊆ x7 ∧ x7 ∩ x8 = (List.filter (fun (x9 : Fin (285 : ℕ)) => Decidable.decide (↑x9 < (51 : ℕ))) (List.finRange (285 : ℕ))).toFinset) → Function.Injective x5 → (∀ (x9 : Fin x4), x5 x9 < x3.length ∧ ¬∃ x10 ∈ x2 ++ List.take (x5 x9) x3, ∃ x11 ∈ x2 ++ List.take (x5 x9) x3, ¬x10 ⊆ x11 ∧ ¬x11 ⊆ x10 ∧ x3.getD (x5 x9) ∅ = x10 ∪ x11) → (18 : ℕ) + x4 ≤ x3.length := by
  intro L m f valid meet inj h
  have left := separation_cost L valid meet
  have right := marked_add L 51 m f inj h
  omega

end A17379

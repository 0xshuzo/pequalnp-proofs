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
  · intro h
    dsimp only
    intro L m f valid capH inj tests
    apply (counted (pay L)).mpr (h L valid capH) m f inj
    intro j
    exact ⟨(tests j).1,(tests j).2⟩

end A17379

namespace A17379
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem no_raw_target : ∀ z∈raw, ¬target⊆z := by decide +kernel

theorem cut_first : have x1 : List ℕ := [(8193 : ℕ), (8194 : ℕ), (8200 : ℕ), (8704 : ℕ), (21233693 : ℕ), (3211303 : ℕ), (7340103 : ℕ), (23068749 : ℕ), (5275731 : ℕ), (22020181 : ℕ), (19923045 : ℕ), (18890857 : ℕ), (6357127 : ℕ), (6553741 : ℕ), (6324419 : ℕ), (6308041 : ℕ), (4751635 : ℕ), (21496089 : ℕ), (17318185 : ℕ), (20988233 : ℕ), (21004625 : ℕ), (17891877 : ℕ)]; have x2 : List (Finset (Fin (285 : ℕ))) := List.map (fun (x2 : ℕ) => (List.filter (fun (x3 : Fin (285 : ℕ)) => (x1.getD ((↑x3 + (1 : ℕ)) / (13 : ℕ)) (0 : ℕ)).testBit (x2 / (13 : ℕ) * (13 : ℕ) + (x2 + (13 : ℕ) - (↑x3 + (1 : ℕ)) % (13 : ℕ)) % (13 : ℕ))) (List.finRange (285 : ℕ))).toFinset) (List.range (26 : ℕ)); ∀ (x3 : List (Finset (Fin (285 : ℕ)))) (x4 : ℕ) (x5 : Fin x4 → ℕ),   (∀ (x6 : Fin x3.length),       have x7 : List (Finset (Fin (285 : ℕ))) := x2 ++ List.take (↑x6) x3;       ∃ x8 ∈ x7, ∃ x9 ∈ x7, ¬x8 ⊆ x9 ∧ ¬x9 ⊆ x8 ∧ x3.get x6 ∉ x7 ∧ (x3.get x6 = x8 ∩ x9 ∨ x3.get x6 = x8 ∪ x9)) →     (∃ x7 ∈ x2, ∃ x8 ∈ x2 ++ x3, ¬x7 ⊆ x8 ∧ ¬x8 ⊆ x7 ∧ x7 ∩ x8 = (List.filter (fun (x9 : Fin (285 : ℕ)) => Decidable.decide (↑x9 < (51 : ℕ))) (List.finRange (285 : ℕ))).toFinset) → Function.Injective x5 → (∀ (x9 : Fin x4), x5 x9 < x3.length ∧ ¬∃ x10 ∈ x2 ++ List.take (x5 x9) x3, ∃ x11 ∈ x2 ++ List.take (x5 x9) x3, ¬x10 ⊆ x11 ∧ ¬x11 ⊆ x10 ∧ x3.getD (x5 x9) ∅ = x10 ∪ x11) → (50 : ℕ) + x4 ≤ x3.length := by
  dsimp only
  intro L m f valid pair inj choose
  obtain ⟨a,ha,b,_,_,_,eq⟩ := pair
  exact (no_raw_target a ha (by rw [←eq];exact Finset.inter_subset_left)).elim

theorem both_gates (L : List Col) (h : cap raw L target) :
    ∃ a∈L,∃ b∈L,¬a⊆b ∧ ¬b⊆a ∧ a∩b=target := by
  obtain ⟨a,ha,b,hb,ab,ba,eq⟩ := h
  refine ⟨a,(List.mem_append.mp ha).resolve_left ?_,b,(List.mem_append.mp hb).resolve_left ?_,ab,ba,eq⟩
  · intro hraw
    exact no_raw_target a hraw (by rw [←eq];exact Finset.inter_subset_left)
  · intro hraw
    exact no_raw_target b hraw (by rw [←eq];exact Finset.inter_subset_right)
end A17379

namespace A17379
noncomputable instance canJoinDec (B : List Col) (w : Col) : Decidable (canJoin B w) := Classical.propDecidable _

def bank (base L : List Col) (i : ℕ) := base++L.take i
def wide (q : Fin 285) (F : Col) (B : List Col) (w : Col) :=
  q∉w ∧ ¬∃ z∈B,q∉z ∧ w∩F⊆z
noncomputable instance (q : Fin 285) (F : Col) (B : List Col) (w : Col) : Decidable (wide q F B w) :=
  Classical.propDecidable _
noncomputable def counts (base L : List Col) (q : Fin 285) (F : Col) (i : ℕ) := by
  classical
  exact ((Finset.range i).filter fun j => wide q F (bank base L j) (L.getD j ∅)).card

theorem counts_succ (base L : List Col) (q : Fin 285) (F : Col) (i : ℕ) :
    counts base L q F (i+1)=counts base L q F i+
      (if wide q F (bank base L i) (L.getD i ∅) then 1 else 0) := by
  classical
  by_cases ch : wide q F (bank base L i) (L.getD i ∅) <;>
    simp [counts,Finset.range_add_one,Finset.filter_insert,ch]

theorem wide_join {q : Fin 285} {F : Col} {base L : List Col} (allow : admissible base L)
    {i : ℕ} (hi : i<L.length) (h : wide q F (bank base L i) (L.getD i ∅)) :
    canJoin (bank base L i) (L.getD i ∅) := by
  rw [List.getD_eq_getElem _ _ hi] at h ⊢
  obtain ⟨a,ha,b,hb,ab,ba,_,op⟩ := allow ⟨i,hi⟩
  change L[i]=a∩b ∨ L[i]=a∪b at op
  rcases op with meet|join
  · obtain ⟨neg,no⟩ := h
    rw [meet] at no neg
    by_cases qa : q∈a
    · exact (no ⟨b,hb,fun qb=>neg (Finset.mem_inter.mpr ⟨qa,qb⟩),
        fun _ hx => (Finset.mem_inter.mp (Finset.mem_inter.mp hx).1).2⟩).elim
    · exact (no ⟨a,ha,qa,fun _ hx => (Finset.mem_inter.mp (Finset.mem_inter.mp hx).1).1⟩).elim
  · exact ⟨a,ha,b,hb,ab,ba,join⟩

def Focus (F : Col) (R S : Finset Col) := ∀ w∈S,∀ p∈w,p∈F → ∃ r∈R,p∈r

theorem cost_focus (base L : List Col) (allow : admissible base L) (q : Fin 285) (F : Col) (i : ℕ)
    (bound : i≤L.length) (S : Finset Col) (valid : ∀ w∈S,w∈bank base L i ∧ q∉w) :
    ∃ R : Finset Col, (∀ r∈R,r∈base ∧ q∉r) ∧ Focus F R S ∧ R.card≤S.card+counts base L q F i := by
  classical
  induction i generalizing S with
  | zero =>
    exact ⟨S,by simpa [bank] using valid,fun w hw p hp _ => ⟨w,hw,hp⟩,by simp [counts]⟩
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
          (enough : ∀ p∈w,p∈F → ∃ z∈K,p∈z) (budget : K.card≤
            1+(if wide q F (bank base L i) (L.getD i ∅) then 1 else 0)) :
          ∃ R : Finset Col, (∀ r∈R,r∈base ∧ q∉r) ∧ Focus F R S ∧
            R.card≤S.card+counts base L q F (i+1) := by
        have good : ∀ z∈S0∪K,z∈bank base L i ∧ q∉z := fun z hz =>
          (Finset.mem_union.mp hz).elim (prev z) (hk z)
        obtain ⟨R,rawR,cov,size⟩ := ih hi.le _ good
        refine ⟨R,rawR,?_,?_⟩
        · intro z hz p hp pf
          by_cases eq : z=w
          · obtain ⟨v,hv,pv⟩ := enough p (eq ▸ hp) pf
            exact cov v (Finset.mem_union_right _ hv) p pv pf
          · exact cov z (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨eq,hz⟩)) p hp pf
        · have u := Finset.card_union_le S0 K
          rw [counts_succ]
          omega
      by_cases yes : wide q F (bank base L i) (L.getD i ∅)
      · obtain ⟨a,ha,b,hb,_,_,join⟩ := wide_join allow hi yes
        rw [d] at join
        apply transfer {a,b}
        · intro z hz
          rcases (show z=a ∨ z=b by simpa using hz) with rfl|rfl
          · exact ⟨ha,fun h => hq (by rw [join]; exact Finset.mem_union_left _ h)⟩
          · exact ⟨hb,fun h => hq (by rw [join]; exact Finset.mem_union_right _ h)⟩
        · intro p hp pf
          rcases Finset.mem_union.mp (join ▸ hp) with h|h
          · exact ⟨a,by simp,h⟩
          · exact ⟨b,by simp,h⟩
        · simpa [yes] using Finset.card_insert_le a ({b} : Finset Col)
      · have dom : ∃ z∈bank base L i,q∉z ∧ w∩F⊆z := by
          by_contra none
          exact yes (by rw [d];exact ⟨hq,none⟩)
        obtain ⟨z,hz,qz,inc⟩ := dom
        apply transfer {z}
        · intro v hv
          rw [Finset.mem_singleton.mp hv]
          exact ⟨hz,qz⟩
        · exact fun p hp pf => ⟨_,Finset.mem_singleton_self _,inc (Finset.mem_inter.mpr ⟨hp,pf⟩)⟩
        · simp [yes]
    · have v : ∀ z∈S,z∈bank base L i ∧ q∉z := fun z hz => old z hz (fun e=>hw (e ▸ hz))
      obtain ⟨R,hR,cov,size⟩ := ih hi.le S v
      exact ⟨R,hR,cov,by rw [counts_succ];omega⟩

end A17379

namespace A17379
def panel : List (Fin 285 × Col) := [(51,{43,47,17,49,30,8,21,10,34,25,26,14,15,42,44,45,46,35,37}),(111,{42,1,14,3,27,48,29,9,40,38,0,41,43,31,19,20,34,36,50}),(69,{24,12,37,25,46,50,38,33,11,39,27,28,29,17,18,32,47,48,49}),(179,{44,45,15,28,18,19,31,32,41,12,0,40,42,43,33,47,35,36,24}),(54,{24,0,37,46,50,20,39,33,11,25,27,28,29,17,18,45,47,48,49})]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
theorem panel_valid : ∀ y∈panel,y.1∉target ∧ y.2⊆target ∧ y.2.card=19 ∧ ∀ r∈raw,y.1∉r → (r∩y.2).card≤1 := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
theorem panel_rows : ∀ r∈raw,∃ y∈panel,y.1∈r := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
theorem panel_points : ∀ p : Fin 285,∃ y∈panel,p∉y.2 := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem pair_overlap : ∀ a∈raw,∀ b∈raw,a≠b → ((a∩b)∩target).card≤1 := by decide +kernel
theorem private_samples (q : Fin 285) (F : Col) (excluded : q∉target) (witnesses_flags : F⊆target)
    (witnesses_card : F.card=19) (one_per_raw : ∀ r∈raw,q∉r → (r∩F).card≤1) (L : List Col) (h : admissible raw L) (c : cap raw L target) :
    18≤counts raw L q F L.length := by
  classical
  obtain ⟨a,ha,b,hb,_,_,meet⟩ := c
  have solve (z : Col) (hz : z∈raw++L) (goal : target⊆z) (neg : q∉z) :
      18≤counts raw L q F L.length := by
    obtain ⟨R,hR,cov,sz⟩ := cost_focus raw L h q F L.length le_rfl {z} (by
      intro w hw
      rw [Finset.mem_singleton.mp hw]
      exact ⟨by simpa [bank] using hz,neg⟩)
    have inc : F ⊆ R.biUnion (fun v => v∩F) := by
      intro p hp
      obtain ⟨r,hr,hit⟩ := cov z (Finset.mem_singleton_self _) p (goal (witnesses_flags hp)) hp
      exact Finset.mem_biUnion.mpr ⟨r,hr,Finset.mem_inter.mpr ⟨hit,hp⟩⟩
    have total : F.card≤R.card := calc
      _ ≤ _ := Finset.card_le_card inc
      _ ≤ _ := Finset.card_biUnion_le
      _ ≤ ∑ _∈R, (1:ℕ) := Finset.sum_le_sum (fun r hr => one_per_raw r (hR r hr).1 (hR r hr).2)
      _ = _ := by simp
    rw [witnesses_card] at total
    simp only [Finset.card_singleton] at sz
    omega
  have ta : target⊆a := by rw [←meet];exact Finset.inter_subset_left
  have tb : target⊆b := by rw [←meet];exact Finset.inter_subset_right
  by_cases qa : q∈a
  · apply solve b hb tb
    exact fun qb => excluded (meet ▸ Finset.mem_inter.mpr ⟨qa,qb⟩)
  · exact solve a ha ta qa


theorem before_first (L : List Col) (legal : admissible raw L) (i : ℕ) (hi : i≤L.length)
    (early : ∀ j<i, ¬canJoin (bank raw L j) (L.getD j ∅)) :
    ∀ w∈bank raw L i,w∈raw ∨ (w∩target).card≤1 := by
  induction i with
  | zero => intro w h;left;simpa [bank] using h
  | succ i ih =>
    have il : i<L.length := by omega
    have prev := ih il.le (fun j hj => early j (by omega))
    intro w h
    simp only [bank,List.take_succ_eq_append_getElem il,←List.append_assoc] at h
    rcases List.mem_append.mp h with old|last
    · exact prev w old
    · have eq : w=L[i] := List.mem_singleton.mp last
      obtain ⟨a,ha,b,hb,ab,ba,new,op⟩ := legal ⟨i,il⟩
      rcases op with meet|join
      · right
        rw [eq,(show L[i]=a∩b from meet)]
        rcases prev a ha with ar|small
        · rcases prev b hb with br|small
          · exact pair_overlap a ar b br (fun e=> ab (by rw [e]))
          · exact (Finset.card_le_card (show (a∩b)∩target⊆b∩target by
              intro x h; exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp (Finset.mem_inter.mp h).1).2,(Finset.mem_inter.mp h).2⟩)).trans small
        · exact (Finset.card_le_card (show (a∩b)∩target⊆a∩target by
            intro x h; exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp (Finset.mem_inter.mp h).1).1,(Finset.mem_inter.mp h).2⟩)).trans small
      · exact (early i (by omega) (by rw [List.getD_eq_getElem _ _ il]; exact ⟨a,ha,b,hb,ab,ba,join⟩)).elim

theorem first_waste (L : List Col) (h : admissible raw L) (s : ℕ) (hs : s<L.length)
    (early : ∀ j<s,¬canJoin (bank raw L j) (L.getD j ∅))
    (pay : canJoin (bank raw L s) (L.getD s ∅)) :
    ∃ y∈panel,¬wide y.1 y.2 (bank raw L s) (L.getD s ∅) := by
  classical
  obtain ⟨a,ha,b,hb,ab,ba,union⟩ := pay
  rcases before_first L h s hs.le early a ha with ar|small
  · obtain ⟨y,hy,hit⟩ := panel_rows a ar
    exact ⟨y,hy,fun yes=>yes.1 (by rw [union];exact Finset.mem_union_left _ hit)⟩
  · have lone : ∃ p : Fin 285,∀ x∈a∩target,x=p := by
      by_cases ne : (a∩target).Nonempty
      · obtain ⟨p,hp⟩ := ne
        exact ⟨p,fun x hx => Finset.card_le_one.mp small x hx p hp⟩
      · exact ⟨0,fun x hx => (ne ⟨x,hx⟩).elim⟩
    obtain ⟨p,only⟩ := lone
    obtain ⟨y,hy,miss⟩ := panel_points p
    have flags := (panel_valid y hy).2.1
    refine ⟨y,hy,?_⟩
    intro yes
    apply yes.2
    refine ⟨b,hb,fun hq => yes.1 (by rw [union]; exact Finset.mem_union_right _ hq),?_⟩
    intro x hx
    obtain ⟨hw,xf⟩ := Finset.mem_inter.mp hx
    rw [union] at hw
    rcases Finset.mem_union.mp hw with ax|bx
    · exact (miss ((only x (Finset.mem_inter.mpr ⟨ax,flags xf⟩)) ▸ xf)).elim
    · exact bx

theorem sharp_floor (L : List Col) (h : admissible raw L) (c : cap raw L target)
    (m : ℕ) (f : Fin m→ℕ) (inj : Function.Injective f)
    (off : ∀ j, f j<L.length ∧ ¬canJoin (bank raw L (f j)) (L.getD (f j) ∅)) :
    19+m≤L.length := by
  classical
  let J := (Finset.range L.length).filter fun j => canJoin (bank raw L j) (L.getD j ∅)
  have non : J.Nonempty := by
    by_contra none
    obtain ⟨y,hy⟩ : ∃ y, y∈panel := ⟨_,List.mem_cons_self⟩
    obtain ⟨out,inside,size,mon⟩ := panel_valid y hy
    have req := private_samples y.1 y.2 out inside size mon L h c
    have empty : ((Finset.range L.length).filter (fun j => wide y.1 y.2 (bank raw L j) (L.getD j ∅)))=∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro j hj
      obtain ⟨lt,wide⟩ := Finset.mem_filter.mp hj
      exact none ⟨j,Finset.mem_filter.mpr ⟨lt,wide_join h (Finset.mem_range.mp lt) wide⟩⟩
    simp [counts,empty] at req
  let s := J.min' non
  have sm := Finset.mem_filter.mp (J.min'_mem non)
  have sl : s<L.length := Finset.mem_range.mp sm.1
  have early (j : ℕ) (lt : j<s) (p : canJoin (bank raw L j) (L.getD j ∅)) : False := by
    have mem : j∈J := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),p⟩
    exact (Nat.not_le_of_gt lt) (Finset.min'_le _ _ mem)
  obtain ⟨y,hy,waste⟩ := first_waste L h s sl early sm.2
  obtain ⟨out,inside,size,mon⟩ := panel_valid y hy
  have req := private_samples y.1 y.2 out inside size mon L h c
  let A := Finset.univ.image f
  let B := (Finset.range L.length).filter fun j => wide y.1 y.2 (bank raw L j) (L.getD j ∅)
  have dis : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro j aj bj
    obtain ⟨v,_,rfl⟩ := Finset.mem_image.mp aj
    exact (off v).2 (wide_join h (off v).1 (Finset.mem_filter.mp bj).2)
  have ns : s∉A∪B := by
    intro mem
    rcases Finset.mem_union.mp mem with as'|bs
    · obtain ⟨v,_,eq⟩ := Finset.mem_image.mp as'
      exact (off v).2 (eq ▸ sm.2)
    · exact waste (Finset.mem_filter.mp bs).2
  have sub : insert s (A∪B) ⊆ Finset.range L.length := by
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl|memb
    · exact Finset.mem_range.mpr sl
    rcases Finset.mem_union.mp memb with av|bv
    · obtain ⟨v,_,rfl⟩ := Finset.mem_image.mp av
      exact Finset.mem_range.mpr (off v).1
    · exact (Finset.mem_filter.mp bv).1
  have cnt := Finset.card_le_card sub
  rw [Finset.card_insert_of_notMem ns,Finset.card_union_of_disjoint dis,Finset.card_range] at cnt
  have ac : A.card=m := by simp [A,Finset.card_image_of_injective _ inj]
  change 18≤B.card at req
  omega
end A17379

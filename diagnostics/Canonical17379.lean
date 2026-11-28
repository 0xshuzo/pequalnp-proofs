import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_17379.Canonical

abbrev Col (n : Nat) := Finset (Fin n)

def joins {n} (B : List (Col n)) (w : Col n) : Prop :=
  ∃ a ∈ B, ∃ b ∈ B, ¬ a ⊆ b ∧ ¬ b ⊆ a ∧ w = a ∪ b

def admissible {n} (base L : List (Col n)) := ∀ i : Fin L.length,
  let B := base ++ L.take i.val
  ∃ a ∈ B, ∃ b ∈ B, ¬ a ⊆ b ∧ ¬ b ⊆ a ∧ L.get i ∉ B ∧ (L.get i = a ∩ b ∨ L.get i = a ∪ b)

def cap {n} (base L : List (Col n)) (T : Col n) :=
  ∃ a ∈ base ++ L, ∃ b ∈ base ++ L, ¬ a ⊆ b ∧ ¬ b ⊆ a ∧ a ∩ b = T

def close {n} (B : List (Col n)) (F : Col n) (w : Col n) : Col n :=
  Finset.univ.filter fun x => B.all (fun z => decide (F ∩ w ⊆ z → x ∈ z))

theorem close_spec {n} {B : List (Col n)} {F w : Col n} {x : Fin n} :
    x ∈ close B F w ↔ ∀ z ∈ B, F ∩ w ⊆ z → x ∈ z := by
  simp [close, List.all_eq_true]

theorem preserve {n} (B : List (Col n)) (F w : Col n) : F ∩ w ⊆ close B F w :=
  fun _ h => close_spec.mpr (fun _ _ sub => sub h)

theorem close_antitone {n} {A B : List (Col n)} (inc : ∀ z ∈ A, z ∈ B)
    {F w : Col n} : close B F w ⊆ close A F w :=
  fun _ h => close_spec.mpr (fun z hz => (close_spec.mp h) z (inc z hz))

theorem narrower {n} {B : List (Col n)} {F u v : Col n} (uv : u ⊆ v) :
    close B F u ⊆ close B F v := by
  intro x h
  apply close_spec.mpr
  intro z hz sub
  apply (close_spec.mp h) z hz
  exact (Finset.inter_subset_inter_left F uv).trans sub

noncomputable def paid {n} (base L : List (Col n)) (i : Nat) : Nat :=
  ((List.range i).filter (fun j => @decide (joins (base ++ L.take j) (L.getD j ∅))
      (Classical.propDecidable _))).length

inductive Builds {n} (F : Col n) (raw : List (Col n)) : List (Col n) → Prop where
  | nil : Builds F raw []
  | step {K} (h : Builds F raw K) (a b : Col n) :
      Builds F raw (K ++ [close (raw ++ K) F a ∪ close (raw ++ K) F b])

theorem normalize {n} (raw L : List (Col n)) (F : Col n) (valid : admissible raw L)
    (i : Nat) (bound : i ≤ L.length) :
    ∃ K, Builds F raw K ∧ K.length = paid raw L i ∧
      ∀ w ∈ raw ++ L.take i, close (raw ++ K) F w ⊆ w := by
  classical
  induction i with
  | zero =>
    refine ⟨[],.nil,rfl,?_⟩
    intro w hw x hx
    have mem : w ∈ raw ++ [] := by simpa using hw
    exact (close_spec.mp hx) w mem Finset.inter_subset_right
  | succ i ih =>
    have hi : i < L.length := by omega
    obtain ⟨K,build,len,old⟩ := ih hi.le
    have listEq : raw ++ L.take (i+1) = (raw ++ L.take i) ++ [L[i]] := by
      rw [List.take_succ_eq_append_getElem hi, List.append_assoc]
    have get : L.getD i ∅ = L[i] := List.getD_eq_getElem _ _ hi
    have cost : paid raw L (i+1) = paid raw L i +
        (if joins (raw ++ L.take i) L[i] then 1 else 0) := by
      unfold paid
      rw [List.range_succ, List.filter_append, List.length_append]
      by_cases h : joins (raw ++ L.take i) L[i] <;> simp [get,h]
    rcases valid ⟨i,hi⟩ with ⟨a,ha,b,hb,ab,ba,_,op⟩
    change L[i] = a ∩ b ∨ L[i] = a ∪ b at op
    by_cases join : joins (raw ++ L.take i) L[i]
    · rcases join with ⟨u,hu,v,hv,uv,vu,eq⟩
      let z := close (raw ++ K) F u ∪ close (raw ++ K) F v
      have inew : ∀ t ∈ raw ++ K, t ∈ raw ++ (K ++ [z]) := by
        intro t ht
        rw [←List.append_assoc]
        exact List.mem_append_left _ ht
      have hz : z ∈ raw ++ (K ++ [z]) := by simp
      refine ⟨K ++ [z],build.step u v,?_,?_⟩
      · have h : joins (raw ++ L.take i) L[i] := ⟨u,hu,v,hv,uv,vu,eq⟩
        simp [cost,h,len]
      · intro w hw
        rw [listEq,List.mem_append] at hw
        rcases hw with prior|last
        · exact (close_antitone inew).trans (old _ prior)
        · have same : w = L[i] := List.mem_singleton.mp last
          rw [same,eq]
          have sub : F ∩ (u ∪ v) ⊆ z := by
            intro x h
            obtain ⟨hf,huv⟩ := Finset.mem_inter.mp h
            rcases Finset.mem_union.mp huv with h|h
            · exact Finset.mem_union_left _ (preserve _ _ _ (Finset.mem_inter.mpr ⟨hf,h⟩))
            · exact Finset.mem_union_right _ (preserve _ _ _ (Finset.mem_inter.mpr ⟨hf,h⟩))
          intro x hx
          exact (Finset.union_subset_union (old _ hu) (old _ hv)) ((close_spec.mp hx) z hz sub)
    · refine ⟨K,build,by simp [cost,join,len],?_⟩
      intro w hw
      rw [listEq,List.mem_append] at hw
      rcases hw with prior|last
      · exact old _ prior
      · have same : w = L[i] := List.mem_singleton.mp last
        rw [same]
        cases op with
        | inl eq =>
          rw [eq]
          intro x hx
          exact Finset.mem_inter.mpr
            ⟨old _ ha (narrower Finset.inter_subset_left hx),
             old _ hb (narrower Finset.inter_subset_right hx)⟩
        | inr eq => exact (join ⟨a,ha,b,hb,ab,ba,eq⟩).elim

theorem two_private {n} (raw L : List (Col n)) (T : Col n) (valid : admissible raw L)
    (out : cap raw L T) :
    ∃ (p q : Fin n) (K : List (Col n)) (a b : Col n),
      p ∉ T ∧ q ∉ T ∧ p ≠ q ∧ Builds (insert p (insert q T)) raw K ∧
      K.length = paid raw L L.length ∧
      let F := insert p (insert q T)
      let A := close (raw ++ K) F a
      let B := close (raw ++ K) F b
      p ∈ A ∧ p ∉ B ∧ q ∈ B ∧ q ∉ A ∧ A ∩ B = T := by
  classical
  obtain ⟨a,ha,b,hb,ab,ba,eq⟩ := out
  obtain ⟨p,pa,pb⟩ := Finset.not_subset.mp ab
  obtain ⟨q,qb,qa⟩ := Finset.not_subset.mp ba
  let F := insert p (insert q T)
  obtain ⟨K,hK,sz,closed⟩ := normalize raw L F valid L.length le_rfl
  have sa : close (raw ++ K) F a ⊆ a := closed _ (by simpa using ha)
  have sb : close (raw ++ K) F b ⊆ b := closed _ (by simpa using hb)
  refine ⟨p,q,K,a,b,?_,?_,?_,hK,sz,?_,?_,?_,?_,?_⟩
  · rw [←eq]
    exact fun h => pb (Finset.mem_inter.mp h).2
  · rw [←eq]
    exact fun h => qa (Finset.mem_inter.mp h).1
  · exact fun h => qa (h ▸ pa)
  · exact preserve _ F a (Finset.mem_inter.mpr ⟨by simp [F],pa⟩)
  · exact fun h => pb (sb h)
  · exact preserve _ F b (Finset.mem_inter.mpr ⟨by simp [F],qb⟩)
  · exact fun h => qa (sa h)
  · apply Finset.Subset.antisymm
    · rw [←eq]
      exact Finset.inter_subset_inter sa sb
    · intro x h
      have f : x ∈ F := by simp [F,h]
      obtain ⟨xa,xb⟩ := Finset.mem_inter.mp (by simpa only [eq] using h : x ∈ a ∩ b)
      exact Finset.mem_inter.mpr
        ⟨preserve _ F a (Finset.mem_inter.mpr ⟨f,xa⟩),
         preserve _ F b (Finset.mem_inter.mpr ⟨f,xb⟩)⟩
end PEqualNP.Outside.L_meta_17379.Canonical

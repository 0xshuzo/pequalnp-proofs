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
def lit (i : ℕ) (j : Fin 285) : Bool :=
  (reps.getD ((j.val+1)/13) 0).testBit ((i/13)*13+(i+13-(j.val+1)%13)%13)
def atRaw (i : ℕ) : Col := ((List.finRange 285).filter (lit i)).toFinset
theorem member_atRaw (i : ℕ) (j : Fin 285) : j∈atRaw i ↔ lit i j=true := by simp [atRaw]
theorem index_raw {w : Col} (h : w∈raw) : ∃ i : Fin 26, w=atRaw i.val := by
  change w∈(List.range 26).map atRaw at h
  obtain ⟨i,hi,eq⟩ := List.mem_map.mp h
  exact ⟨⟨i,List.mem_range.mp hi⟩,eq.symm⟩

theorem small_private : ∀ i : Fin 26, (lit i.val 0 && lit i.val 1)=false := by decide +kernel
theorem no_raw_target : ∀ z∈raw, ¬target⊆z := by
  intro z hz sub
  obtain ⟨i,rfl⟩ := index_raw hz
  have u := (member_atRaw i.val 0).mp (sub (by simp [target] : (0 : Fin 285)∈target))
  have v := (member_atRaw i.val 1).mp (sub (by simp [target] : (1 : Fin 285)∈target))
  have bad := small_private i
  simp [u,v] at bad

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

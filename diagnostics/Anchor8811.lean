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

end Flat8811
namespace Flat8811
open scoped BigOperators
theorem inputs_mono {N : ℕ} {X Y X' Y' : Finset (Fin N)} (points : X⊆X') (lines : Y⊆Y') :
    inputsOf X Y ⊆ inputsOf X' Y' := Finset.union_subset_union (Finset.image_mono points) (Finset.image_mono lines)

theorem deleteAnchor {q N s o a b : ℕ} (I : Fin N → Fin N → Prop)
    (F : ℕ → Set (Finset ℕ)) (hin : ∀ i<N+N, F i={Z | i∈Z})
    (gates : GateSpec F (N+N) s) (ha : a<N+N+s) (hb : b<N+N+s)
    (carry : F a ∩ F b ⊆ F o) (neg : negatives I q F o)
    (P L : Finset (Fin N)) (ind₀ : ∀ p∈P, ∀ l∈L, ¬ I p l)
    (on : inputsOf P L ∈ F b) :
    ∀ X Y : Finset (Fin N), Y.card + L.card ≤ q →
      (∀ p∈X, ∀ l∈L, ¬ I p l) → (∀ p∈P, ∀ l∈Y, ¬ I p l) →
      (∀ p∈X, ∀ l∈Y, ¬ I p l) → inputsOf X Y ∉ F a := by
  intro X Y width crossA crossB ind₁ yes
  have independent : ∀ p∈X ∪ P, ∀ l∈Y ∪ L, ¬I p l := by
    intro p hp l hl
    rcases Finset.mem_union.mp hp with h|h <;> rcases Finset.mem_union.mp hl with k|k
    exact ind₁ p h l k
    exact crossA p h l k
    exact crossB p h l k
    exact ind₀ p h l k
  apply blocked I F o neg (X∪P) (Y∪L) ((Finset.card_union_le _ _).trans width) independent
  apply carry
  exact ⟨evalX_mono hin gates (inputs_mono Finset.subset_union_left Finset.subset_union_left) a ha yes,
    evalX_mono hin gates (inputs_mono Finset.subset_union_right Finset.subset_union_right) b hb on⟩

theorem survivingFlags {q N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hcols : ∀ l, Fintype.card {p : Fin N // I p l} = q+1)
    (hrows : ∀ p, Fintype.card {l : Fin N // I p l} = q+1)
    (P L : Finset (Fin N)) :
    let edges := Finset.univ.filter (fun e : Fin N × Fin N => I e.1 e.2)
    let remain := edges.filter (fun e => (∀p∈P, ¬I p e.2) ∧ (∀l∈L, ¬I e.1 l))
    N*(q+1) ≤ remain.card + (P.card+L.card)*(q+1)^2 := by
  classical
  let edges := Finset.univ.filter (fun e : Fin N × Fin N => I e.1 e.2)
  let lines (p : Fin N) := Finset.univ.filter (fun l => I p l)
  let points (l : Fin N) := Finset.univ.filter (fun p => I p l)
  let starL (l : Fin N) := (points l).image (fun p => (p,l))
  let starP (p : Fin N) := (lines p).image (fun l => (p,l))
  let blockP := P.biUnion (fun p => (lines p).biUnion starL)
  let blockL := L.biUnion (fun l => (points l).biUnion starP)
  let remain := edges.filter (fun e => (∀p∈P, ¬I p e.2) ∧ (∀l∈L, ¬I e.1 l))
  change N*(q+1) ≤ remain.card + (P.card+L.card)*(q+1)^2
  have linesize (p : Fin N) : (lines p).card=q+1 := by simpa [lines,Fintype.card_subtype] using hrows p
  have pointsize (l : Fin N) : (points l).card=q+1 := by simpa [points,Fintype.card_subtype] using hcols l
  have colB (l : Fin N) : (starL l).card ≤ q+1 := Finset.card_image_le.trans (pointsize l).le
  have rowB (p : Fin N) : (starP p).card ≤ q+1 := Finset.card_image_le.trans (linesize p).le
  have pBudget : blockP.card ≤ P.card*(q+1)^2 := by
    calc
      _ ≤ ∑ p∈P, ((lines p).biUnion starL).card := Finset.card_biUnion_le
      _ ≤ ∑ _p∈P, (q+1)^2 := by
        apply Finset.sum_le_sum
        intro p _
        calc
          _ ≤ ∑ l∈lines p, (starL l).card := Finset.card_biUnion_le
          _ ≤ ∑ _l∈lines p, (q+1) := Finset.sum_le_sum (fun l _ => colB l)
          _ = (q+1)^2 := by simp [linesize,pow_two]
      _ = _ := by simp
  have lBudget : blockL.card ≤ L.card*(q+1)^2 := by
    calc
      _ ≤ ∑ l∈L, ((points l).biUnion starP).card := Finset.card_biUnion_le
      _ ≤ ∑ _l∈L, (q+1)^2 := by
        apply Finset.sum_le_sum
        intro l _
        calc
          _ ≤ ∑ p∈points l, (starP p).card := Finset.card_biUnion_le
          _ ≤ ∑ _p∈points l, (q+1) := Finset.sum_le_sum (fun p _ => rowB p)
          _ = (q+1)^2 := by simp [pointsize,pow_two]
      _ = _ := by simp
  have cover : edges ⊆ remain ∪ (blockP ∪ blockL) := by
    intro e he
    have inc : I e.1 e.2 := (Finset.mem_filter.mp he).2
    by_cases keep : (∀p∈P, ¬I p e.2) ∧ (∀l∈L, ¬I e.1 l)
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨he,keep⟩)
    apply Finset.mem_union_right
    by_cases first : ∃p∈P, I p e.2
    · obtain ⟨p,hp,hit⟩ := first
      apply Finset.mem_union_left
      apply Finset.mem_biUnion.mpr
      refine ⟨p,hp,Finset.mem_biUnion.mpr ⟨e.2,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hit⟩,?_⟩⟩
      exact Finset.mem_image.mpr ⟨e.1,Finset.mem_filter.mpr ⟨Finset.mem_univ _,inc⟩,rfl⟩
    · have second : ∃l∈L, I e.1 l := by
        by_contra! hn
        exact keep ⟨fun p hp h => first ⟨p,hp,h⟩,hn⟩
      obtain ⟨l,hl,hit⟩ := second
      apply Finset.mem_union_right
      apply Finset.mem_biUnion.mpr
      refine ⟨l,hl,Finset.mem_biUnion.mpr ⟨e.1,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hit⟩,?_⟩⟩
      exact Finset.mem_image.mpr ⟨e.2,Finset.mem_filter.mpr ⟨Finset.mem_univ _,inc⟩,rfl⟩
  have tot : edges.card=N*(q+1) := incidence_card q N I hcols
  have sz := (Finset.card_le_card cover).trans (Finset.card_union_le _ _)
  have add := (Finset.card_union_le blockP blockL).trans (Nat.add_le_add pBudget lBudget)
  rw [Nat.add_mul]
  omega
end Flat8811

import Mathlib

namespace Components4970

variable {α : Type} [DecidableEq α]

def Uniform (c : α → α) (s : Finset α) := ∀ x ∈ s, ∀ y ∈ s, c x = c y

def merge (a b x : α) : α := if x = a then b else x

theorem merge_cost (U : Finset α) (c : α → α) (a b : α) :
    (U.image c).card ≤ (U.image (fun x => merge a b (c x))).card + 1 := by
  have sub : U.image c ⊆ insert a (U.image (fun x => merge a b (c x))) := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    by_cases h : c x = a
    · simp [h]
    · apply Finset.mem_insert_of_mem
      exact Finset.mem_image.mpr ⟨x, hx, by simp [merge,h]⟩
  exact (Finset.card_le_card sub).trans (Finset.card_insert_le _ _)

theorem merge_union {c : α → α} {A B : Finset α} (ha : Uniform c A) (hb : Uniform c B)
    (U : Finset α) : ∃ d : α → α, (U.image c).card ≤ (U.image (d ∘ c)).card + 1 ∧
      Uniform (d ∘ c) (A ∪ B) := by
  rcases A.eq_empty_or_nonempty with rfl|⟨a,aa⟩
  · refine ⟨id,by simp,?_⟩; simpa [Uniform] using hb
  rcases B.eq_empty_or_nonempty with rfl|⟨b,bb⟩
  · refine ⟨id,by simp,?_⟩; simpa [Uniform] using ha
  let d := merge (c b) (c a)
  refine ⟨d,merge_cost U c (c b) (c a),?_⟩
  have same (z) (hz : z ∈ A ∪ B) : d (c z) = c a := by
    rcases Finset.mem_union.mp hz with h|h
    · rw [ha z h a aa]; simp [d,merge]
    · rw [hb z h b bb]; simp [d,merge]
  exact fun x hx y hy => (same x hx).trans (same y hy).symm

/-- Eligible means that the wire is false on the fixed negative test.
    At an AND choose a false child; at an OR both children are false. -/
def Rules (S : ℕ → Finset α) (good paid : ℕ → Prop) (m : ℕ) :=
  ∀ i < m, good i →
    (S i).card ≤ 1 ∨
    (∃ a < i, good a ∧ S i ⊆ S a) ∨
    (paid i ∧ ∃ a < i, ∃ b < i, good a ∧ good b ∧ S i ⊆ S a ∪ S b)

theorem labels (U : Finset α) (S : ℕ → Finset α) (good paid : ℕ → Prop)
    [DecidablePred paid] (m : ℕ) (rules : Rules S good paid m) :
    ∃ c : α → α, U.card ≤ (U.image c).card + ((Finset.range m).filter paid).card ∧
      ∀ w < m, good w → Uniform c (S w) := by
  induction m with
  | zero => exact ⟨id,by simp,by simp⟩
  | succ m ih =>
    obtain ⟨c,rank,inv⟩ := ih (fun i hi => rules i (by omega))
    have cost : ((Finset.range m).filter paid).card ≤ ((Finset.range (m+1)).filter paid).card :=
      Finset.card_le_card (Finset.filter_subset_filter _ (Finset.range_mono (by omega)))
    have keep (atM : good m → Uniform c (S m)) : ∀ w < m+1, good w → Uniform c (S w) := by
      intro w hw hg
      rcases Nat.lt_or_ge w m with h|h
      · exact inv w h hg
      · obtain rfl : w=m := by omega
        exact atM hg
    by_cases yes : good m
    · rcases rules m (by omega) yes with tiny|⟨a,lt,ga,sub⟩|⟨pm,a,la,b,lb,ga,gb,sub⟩
      · apply Exists.intro c; refine ⟨by omega,keep (fun _ x hx y hy => ?_)⟩
        exact congrArg c ((Finset.card_le_one.mp tiny) x hx y hy)
      · exact ⟨c,by omega,keep (fun _ x hx y hy => inv a lt ga x (sub hx) y (sub hy))⟩
      · obtain ⟨d,loss,uniform⟩ := merge_union (inv a la ga) (inv b lb gb) U
        have add : ((Finset.range (m+1)).filter paid).card = ((Finset.range m).filter paid).card+1 := by
          rw [Finset.range_add_one, Finset.filter_insert, if_pos pm, Finset.card_insert_of_notMem]
          simp
        refine ⟨d ∘ c,by omega,?_⟩
        intro w hw hg
        rcases Nat.lt_or_ge w m with h|h
        · exact fun x hx y hy => congrArg d (inv w h hg x hx y hy)
        · obtain rfl : w=m := by omega
          exact fun x hx y hy => uniform x (sub hx) y (sub hy)
    · exact ⟨c,by omega,keep (fun h => (yes h).elim)⟩

/-- A family of witnessed stars can overlap. Take one vertex in R per
    connected component of the hypergraph of witnessed leaf sets. -/
theorem components (U R : Finset α) (S : ℕ → Finset α) (good paid : ℕ → Prop)
    [DecidablePred paid] (m : ℕ) (rules : Rules S good paid m)
    (paths : ∀ x ∈ U, ∃ y ∈ R, Relation.ReflTransGen
      (fun u v => ∃ w < m, good w ∧ u ∈ S w ∧ v ∈ S w) x y) :
    U.card ≤ R.card + ((Finset.range m).filter paid).card := by
  obtain ⟨c,cost,flat⟩ := labels U S good paid m rules
  have sub : U.image c ⊆ R.image c := by
    intro z hz
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨y,hy,path⟩ := paths x hx
    have eq : c x = c y := by
      clear hy
      induction path with
      | refl => rfl
      | tail _ h ih =>
        obtain ⟨w,hw,hg,ha,hb⟩ := h
        exact ih.trans (flat w hw hg _ ha _ hb)
    exact Finset.mem_image.mpr ⟨y,hy,eq.symm⟩
  have bound := (Finset.card_le_card sub).trans Finset.card_image_le
  omega

end Components4970

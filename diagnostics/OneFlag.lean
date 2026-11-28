import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_9737.OneFlag
def core : List (Nat × Nat) := [(0,16),(0,24),(1,13),(1,17),(1,23),(2,13),(2,14),(2,18),(2,24),(3,14),(3,15),(3,19),(4,13),(4,15),(4,16),(4,20),(5,14),(5,16),(5,17),(5,21),(6,15),(6,17),(6,18),(6,22),(7,16),(7,18),(7,19),(7,23),(8,17),(8,19),(8,20),(8,24),(9,18),(9,20),(9,21),(10,13),(10,19),(10,21),(10,22),(11,14),(11,20),(11,22),(11,23),(12,15),(12,21),(12,23),(12,24)]
def hit (x : Nat → Bool) : Prop := ∃ e ∈ core, x e.1 = true ∧ x e.2 = true
def tr (a b i : Nat) : Nat := if i=a then b else if i=b then a else i
theorem twice (a b i : Nat) : tr a b (tr a b i) = i := by
  by_cases hab : a=b
  · subst b
    by_cases h : i=a <;> simp [tr,h]
  · by_cases hi : i=a
    · subst i; simp [tr,hab,Ne.symm hab]
    · by_cases hj : i=b
      · subst i; simp [tr,hab,Ne.symm hab]
      · simp [tr,hi,hj]
def branch (a b : Nat) (x : Nat → Bool) : Prop := hit x ∨ hit (x ∘ tr a b)
theorem symmetric (a b : Nat) (x : Nat → Bool) :
    branch a b (x ∘ tr a b) ↔ branch a b x := by
  have h : (x ∘ tr a b) ∘ tr a b = x := by funext i; simp [Function.comp_def,twice]
  unfold branch
  rw [h,or_comm]
def among (u a b c d : Nat) := u=a ∨ u=b ∨ u=c ∨ u=d
instance (u a b c d : Nat) : Decidable (among u a b c d) := by unfold among; infer_instance

set_option maxHeartbeats 0 in
theorem cross : ∀ e ∈ core, ∀ f ∈ core, ∃ g ∈ core,
    among g.1 (tr 0 2 e.1) (tr 0 2 e.2) (tr 2 16 f.1) (tr 2 16 f.2) ∧
    among g.2 (tr 0 2 e.1) (tr 0 2 e.2) (tr 2 16 f.1) (tr 2 16 f.2) := by decide +kernel

theorem accept {x : Nat → Bool} {u a b c d : Nat} (h : among u a b c d)
    (ha : x a=true) (hb : x b=true) (hc : x c=true) (hd : x d=true) : x u=true := by
  rcases h with h|h|h|h
  · simpa [h] using ha
  · simpa [h] using hb
  · simpa [h] using hc
  · simpa [h] using hd

theorem exactCore (x : Nat → Bool) : branch 0 2 x ∧ branch 2 16 x ↔ hit x := by
  constructor
  · rintro ⟨a,b⟩
    rcases a with p|⟨e,he,eu,ev⟩
    · exact p
    rcases b with p|⟨f,hf,fu,fv⟩
    · exact p
    obtain ⟨g,hg,gu,gv⟩ := cross e he f hf
    exact ⟨g,hg,accept gu eu ev fu fv,accept gv eu ev fu fv⟩
  · intro h
    exact ⟨Or.inl h,Or.inl h⟩

end PEqualNP.Outside.L_meta_9737.OneFlag

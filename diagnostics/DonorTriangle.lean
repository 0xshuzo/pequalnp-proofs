import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9743.DonorTriangle
def fires {α : Type} (E : α → α → Prop) (x : α → Bool) :=
  ∃ i j, E i j ∧ x i = true ∧ x j = true
def one {β : Type} [DecidableEq β] (a v : β) := decide (v = a)
def dyad {β : Type} [DecidableEq β] (a b v : β) := decide (v = a ∨ v = b)
def increasing {β : Type} (p : (β → Bool) → Bool) :=
  ∀ x y, (∀ i, x i = true → y i = true) → p x = true → p y = true

theorem transport {α β : Type} [DecidableEq β] {E : α → α → Prop} {G : β → β → Prop}
    (sb : ∀ u v, G u v → G v u) (loop : ∀ u, ¬ G u u)
    (p : α → (β → Bool) → Bool) (mono : ∀ u, increasing (p u))
    (correct : ∀ x, fires E (fun u => p u x) → fires G x)
    {u v : α} (edge : E u v) {a b : β}
    (ha : p u (one a) = true) (hb : p v (one b) = true) : G a b := by
  have l : p u (dyad a b) = true := mono u _ _ (fun i hi =>
    decide_eq_true (Or.inl (of_decide_eq_true hi))) ha
  have r : p v (dyad a b) = true := mono v _ _ (fun i hi =>
    decide_eq_true (Or.inr (of_decide_eq_true hi))) hb
  obtain ⟨c,d,adj,hc,hd⟩ := correct (dyad a b) ⟨u,v,edge,l,r⟩
  have c' : c = a ∨ c = b := of_decide_eq_true hc
  have d' : d = a ∨ d = b := of_decide_eq_true hd
  rcases c' with rfl|rfl <;> rcases d' with rfl|rfl
  · exact (loop _ adj).elim
  · exact adj
  · exact sb _ _ adj
  · exact (loop _ adj).elim

theorem triangle {α β : Type} [DecidableEq β] {E : α → α → Prop} {G : β → β → Prop}
    (sb : ∀ u v, G u v → G v u) (loop : ∀ u, ¬ G u u)
    (shore : β → Bool) (bip : ∀ a b, G a b → shore a ≠ shore b)
    (p : α → (β → Bool) → Bool) (mono : ∀ u, increasing (p u))
    (correct : ∀ x, fires E (fun u => p u x) → fires G x)
    {u v w : α} (uv : E u v) (vw : E v w) (wu : E w u) :
    (∀ a, p u (one a) = false) ∨ (∀ a, p v (one a) = false) ∨ (∀ a, p w (one a) = false) := by
  by_contra! bad
  obtain ⟨⟨a,ha⟩,⟨b,hb⟩,⟨c,hc⟩⟩ := bad
  have ta : p u (one a) = true := by cases h : p u (one a) <;> simp_all
  have tb : p v (one b) = true := by cases h : p v (one b) <;> simp_all
  have tc : p w (one c) = true := by cases h : p w (one c) <;> simp_all
  have i := bip _ _ (transport sb loop p mono correct uv ta tb)
  have j := bip _ _ (transport sb loop p mono correct vw tb tc)
  have k := bip _ _ (transport sb loop p mono correct wu tc ta)
  cases a' : shore a <;> cases b' : shore b <;> cases c' : shore c <;> simp_all

end PEqualNP.Outside.L_meta_9743.DonorTriangle

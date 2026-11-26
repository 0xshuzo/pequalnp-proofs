import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9804_Guard
universe u v w z
variable {L : Type u} {R : Type v} {J : Type w} {K : Type z}

-- Each leaf operand is either raw or belongs to a lambda cone with an ordinary
-- opposite center. The latter makes all its incident cells ordinary.
def centered (A : J → L → Prop) (T : L → R → Prop) : Prop :=
  ∀ j a c, A j a → A j c → a ≠ c → ∃ b, ∀ x, A j x → T x b

def thin (G : L → R → Prop) : Prop :=
  ∀ a c b d, b ≠ d → G a b → G a d → G c b → G c d → a = c


private theorem distinct_cell (G T : L → R → Prop) (A : J → L → Prop) (B : K → R → Prop)
    (j : J) (k : K) (tl : thin G) (tr : thin (fun b a => G a b))
    (cl : centered A T) (cr : centered B (fun b a => T a b))
    (ordinary : ∀ a b,T a b → G a b)
    (safe : ∀ a b,(∀ q,A q a) → (∀ p,B p b) → G a b)
    {a c : L} {b d : R} (notT : ¬T a b)
    (aa : ∀ q,A q a) (bb : ∀ p,B p b) (cc : ∀ q,A q c) (dd : ∀ p,B p d) :
    a=c ∧ b=d := by
  constructor
  · by_contra ne
    obtain ⟨z,side⟩ := cl j a c (aa j) (cc j) ne
    have za := side a (aa j)
    have zc := side c (cc j)
    have eq := tr z b a c ne (ordinary _ _ za) (ordinary _ _ zc)
      (safe a b aa bb) (safe c b cc bb)
    exact notT (eq ▸ za)
  · by_contra ne
    obtain ⟨z,side⟩ := cr k b d (bb k) (dd k) ne
    have zb := side b (bb k)
    have zd := side d (dd k)
    have eq := tl z a b d ne (ordinary _ _ zb) (ordinary _ _ zd)
      (safe a b aa bb) (safe a d aa dd)
    exact notT (eq ▸ zb)

-- With no mixing OR, an accepting top is a conjunction of pure one-shore
-- disjunctions. Any charged top meeting an exceptional cell must have operands
-- from both shores because otherwise it accepts an independent singleton.
theorem unmixed_price {Top : Type*} (J0 K0 : Top → Type*) (G T : L → R → Prop)
    (A : ∀ t, J0 t → L → Prop) (B : ∀ t, K0 t → R → Prop)
    (E : Finset (L × R)) (tops : Finset Top) (vertices paid : Nat)
    (tl : thin G) (tr : thin (fun b a => G a b))
    (ordinary : ∀ a b,T a b → G a b) (outside : ∀ e∈E,¬T e.1 e.2)
    (cla : ∀ t∈tops,centered (A t) T)
    (clb : ∀ t∈tops,centered (B t) (fun b a => T a b))
    (clean : ∀ t∈tops,∀ a b,(∀ q,A t q a) → (∀ p,B t p b) → G a b)
    (findTop : ∀ e∈E,∃ t∈tops, Nonempty (J0 t) ∧ Nonempty (K0 t) ∧
      (∀ q,A t q e.1) ∧ (∀ p,B t p e.2))
    (charge : 2*tops.card≤paid) (matching : 80≤4*vertices+E.card)
    (base : 95+vertices+paid≤113+E.card+1) : False := by
  classical
  have lookup (e : ↑E) : ∃ t : ↑tops, Nonempty (J0 t.val) ∧
      Nonempty (K0 t.val) ∧ (∀ q,A t.val q e.val.1) ∧ (∀ p,B t.val p e.val.2) := by
    obtain ⟨t,ht,p⟩ := findTop e.val e.property
    exact ⟨⟨t,ht⟩,p⟩
  choose f hf using lookup
  have fi : Function.Injective f := by
    intro u v eq
    obtain ⟨⟨j⟩,⟨k⟩,aa,bb⟩ := hf u
    have h := hf v
    rw [←eq] at h
    obtain ⟨_,_,cc,dd⟩ := h
    have repr := distinct_cell G T (A (f u).val) (B (f u).val) j k tl tr
      (cla _ (f u).property) (clb _ (f u).property) ordinary
      (clean _ (f u).property) (outside u.val u.property) aa bb cc dd
    exact Subtype.ext (Prod.ext repr.1 repr.2)
  have card := Fintype.card_le_of_injective f fi
  simp only [Fintype.card_coe] at card
  omega

end PEqualNP.Outside.L_meta_9804_Guard

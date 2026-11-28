import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9829.Deleted
abbrev V := Fin 24
def edges : List (V × V) := [(0,15), (0,21), (0,23), (1,16), (1,22), (2,13), (2,17), (2,23), (3,13), (3,14), (3,18), (4,14), (4,15), (4,19), (5,13), (5,15), (5,16), (5,20), (6,14), (6,16), (6,17), (6,21), (7,15), (7,17), (7,18), (7,22), (8,16), (8,18), (8,19), (8,23), (9,17), (9,19), (9,20), (10,18), (10,20), (10,21), (11,13), (11,19), (11,21), (11,22), (12,14), (12,20), (12,22), (12,23)]
def star : Finset V := {1,2,4,10}
def adjacent (p l : V) : Prop := (p,l) ∈ edges
instance (p l : V) : Decidable (adjacent p l) := by unfold adjacent; infer_instance
def hit (x : V → Bool) : Prop := ∃ p l, adjacent p l ∧ x p=true ∧ x l=true
def enlarged (h : (V → Bool) → Bool) (x : V → Bool) : Prop :=
  hit x ∨ (h x=true ∧ ∃ p∈star, x p=true)
def raisePin (x : V → Bool) (p j : V) : Bool := if j=p then true else x j

theorem star_price {h : (V → Bool) → Bool}
    (safe : ∀ x, enlarged h x → hit x)
    (incr : ∀ x p, p∈star → h x=true → h (raisePin x p)=true)
    {x : V → Bool} (newOn : h x=true) (indep : ¬hit x) :
    ∃ selected : {p // p∈star} → V, Function.Injective selected ∧
      ∀ p, adjacent p.1 (selected p) ∧ x (selected p)=true := by
  have col (p l : V) (e : adjacent p l) : 13≤l.val := by
    exact (by decide : ∀ (i j : V), adjacent i j → 13≤j.val) p l e
  have point (p : V) (hp : p∈star) : p.val<13 :=
    (by decide : ∀ i : V, i∈star → i.val<13) p hp
  have unique (p q l : V) (hp : p∈star) (hq : q∈star)
      (a : adjacent p l) (b : adjacent q l) : p=q :=
    (by decide +kernel : ∀ i j k : V, i∈star → j∈star → adjacent i k → adjacent j k → i=j) p q l hp hq a b
  have cover (p : {i // i∈star}) : ∃ l : V, adjacent p.1 l ∧ x l=true := by
    have H := safe (raisePin x p.1) (Or.inr ⟨incr x p.1 p.2 newOn,p.1,p.2,by simp [raisePin]⟩)
    obtain ⟨a,l,e,ha,hl⟩ := H
    have nlp : l≠p.1 := by
      have psmall := point p.1 p.2
      have lbig := col a l e
      intro eq
      rw [eq] at lbig
      omega
    have xl : x l=true := by simpa [raisePin,nlp] using hl
    by_cases eq : a=p.1
    · exact ⟨l,eq ▸ e,xl⟩
    · have xa : x a=true := by simpa [raisePin,eq] using ha
      exact (indep ⟨a,l,e,xa,xl⟩).elim
  choose f hf using cover
  refine ⟨f,?_,hf⟩
  intro p q eq
  exact Subtype.ext (unique p.1 q.1 (f q) p.2 q.2 (eq ▸ (hf p).1) (hf q).1)

theorem needs_four {h : (V → Bool) → Bool}
    (safe : ∀ x, enlarged h x → hit x)
    (incr : ∀ x p, p∈star → h x=true → h (raisePin x p)=true)
    {x : V → Bool} (hx : h x=true) (noEdge : ¬hit x) :
    4 ≤ ((Finset.univ : Finset V).filter (fun j => 13 ≤ j.val ∧ x j=true)).card := by
  obtain ⟨f,inj,all⟩ := star_price safe incr hx noEdge
  have cardS : Fintype.card {p // p∈star}=4 := by decide
  let B := (Finset.univ : Finset V).filter (fun j => 13 ≤ j.val ∧ x j=true)
  have goes (p : {i // i∈star}) : f p∈B := by
    have ij := (by decide : ∀ a b : V, adjacent a b → 13≤b.val) p.1 (f p) (all p).1
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,ij,(all p).2⟩
  have t := Fintype.card_le_of_injective (fun p : {i // i∈star} => (⟨f p,goes p⟩ : ↥B))
    (fun p q eq => inj (congrArg Subtype.val eq))
  change 4 ≤ B.card
  simpa only [cardS,Fintype.card_coe] using t
end PEqualNP.Outside.L_meta_9829.Deleted

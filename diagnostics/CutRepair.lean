import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9737.CutRepair

variable {V I : Type} [DecidableEq V]
def Dyad (u v : V) (x : V) : Prop := x=u ∨ x=v
def EdgeHit (e : V → V → Prop) (x : V → Prop) : Prop :=
  ∃u v, e u v ∧ x u ∧ x v

def Increasing (f : (V → Prop) → Prop) : Prop :=
  ∀x y, (∀v, x v → y v) → f x → f y

theorem frontier (e : V → V → Prop) (residual : (V → Prop) → Prop)
    (mon : Increasing residual) (sub : ∀x, residual x → EdgeHit e x) (x : V → Prop) :
    EdgeHit e x ↔ residual x ∨ EdgeHit (fun u v => e u v ∧ ¬residual (Dyad u v)) x := by
  classical
  constructor
  · rintro ⟨u,v,uv,hu,hv⟩
    by_cases h : residual (Dyad u v)
    · apply Or.inl (mon _ x _ h)
      intro w hw
      rcases hw with rfl|rfl
      · exact hu
      · exact hv
    · exact Or.inr ⟨u,v,⟨uv,h⟩,hu,hv⟩
  · rintro (h|⟨u,v,⟨uv,_⟩,hu,hv⟩)
    · exact sub x h
    · exact ⟨u,v,uv,hu,hv⟩

theorem replaceCuts (e : V → V → Prop) (wire : I → (V → Prop) → Prop)
    (context : (V → Prop) → (I → Prop) → Prop)
    (monX : ∀x y, (∀v, x v → y v) → ∀z, context x z → context y z)
    (monZ : ∀x z t, (∀i, z i → t i) → context x z → context x t)
    (computes : ∀x, context x (fun i => wire i x) ↔ EdgeHit e x)
    (x : V → Prop) :
    EdgeHit e x ↔ context x (fun _ => False) ∨
      EdgeHit (fun u v => e u v ∧ ¬context (Dyad u v) (fun _ => False)) x := by
  apply frontier
  · exact fun a b incl => monX a b incl _
  · exact fun a h => (computes a).1 (monZ a _ _ (fun _ h0 => h0.elim) h)

theorem oneFlag (e : V → V → Prop) (wire : (V → Prop) → Prop)
    (context : (V → Prop) → Prop → Prop) (a b : V) (ab : e a b)
    (monX : ∀x y, (∀v, x v → y v) → ∀z, context x z → context y z)
    (monZ : ∀x (z t : Prop), (z → t) → context x z → context x t)
    (computes : ∀x, context x (wire x) ↔ EdgeHit e x)
    (unique : ∀u v, e u v → wire (Dyad u v) → u=a ∧ v=b) (x : V → Prop) :
    EdgeHit e x ↔ context x False ∨ (x a ∧ x b) := by
  classical
  constructor
  · rintro ⟨u,v,uv,hu,hv⟩
    by_cases on : wire (Dyad u v)
    · obtain ⟨rfl,rfl⟩ := unique u v uv on
      exact Or.inr ⟨hu,hv⟩
    · left
      have has : EdgeHit e (Dyad u v) := ⟨u,v,uv,Or.inl rfl,Or.inr rfl⟩
      have atEdge := (computes _).2 has
      have stop := monZ _ _ False on atEdge
      apply monX _ x _ False stop
      intro w hw
      rcases hw with rfl|rfl
      · exact hu
      · exact hv
  · rintro (h|⟨ha,hb⟩)
    · exact (computes x).1 (monZ x False _ False.elim h)
    · exact ⟨a,b,ab,ha,hb⟩

end PEqualNP.Outside.L_meta_9737.CutRepair

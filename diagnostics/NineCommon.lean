import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_8089.Grid
abbrev V := Fin 26
abbrev P := Fin 13
abbrev X := V → Bool
abbrev pt (p : P) : V := Fin.castAdd 13 p
abbrev ln (l : P) : V := Fin.natAdd 13 l
def I (p l : P) : Prop := (p-l)^4=p-l
instance (p l : P) : Decidable (I p l) := inferInstanceAs (Decidable ((p-l)^4=p-l))
def F (x : X) : Prop := ∃ p l : P, I p l ∧ x (pt p)=true ∧ x (ln l)=true
def adj (u v : V) : Prop := ((u.val<13 ∧ 13≤v.val ∧ I (Fin.ofNat 13 u.val) (Fin.ofNat 13 v.val)) ∨
  (v.val<13 ∧ 13≤u.val ∧ I (Fin.ofNat 13 v.val) (Fin.ofNat 13 u.val)))
instance (u v : V) : Decidable (adj u v) := by unfold adj; infer_instance
def independent (x : X) := ∀u v, x u=true → x v=true → ¬adj u v
def active (x : X) : Finset V := Finset.univ.filter (fun i => x i=true)
def colors (d : P) : List (Fin 9) := 
  if d=0 then [0,0,0,0,1,2,3,4,5,0,6,7,8,0,6,0,8,0,3,4,5,1,2,0,7,0] else
  if d=1 then [0,0,0,0,1,2,3,4,5,0,6,7,8,0,0,0,8,1,0,3,4,7,2,6,0,5] else
  if d=3 then [0,0,0,0,1,2,3,4,5,0,6,7,8,0,6,0,0,1,2,4,0,5,8,3,7,0] else
  [0,0,0,0,1,2,3,4,5,0,6,7,8,0,1,2,8,4,3,0,5,0,0,6,7,0]
def color (p l : P) (v : V) : Fin 9 :=
  let t : P := (Fin.ofNat 13 v.val)-l
  (colors (p-l)).getD (if v.val<13 then t.val else 13+t.val) 0
theorem unbits (u v : V) (h : adj u v) :
    ∃ p l, I p l ∧ ((u=pt p ∧ v=ln l) ∨ (u=ln l ∧ v=pt p)) := by
  have raw (u v : V) : u.val<13 → 13≤v.val →
    u=pt (Fin.ofNat 13 u.val) ∧ v=ln (Fin.ofNat 13 v.val) :=
    (by decide +kernel : ∀ u v : V, u.val<13 → 13≤v.val →
      u=pt (Fin.ofNat 13 u.val) ∧ v=ln (Fin.ofNat 13 v.val)) u v
  rcases h with ⟨hu,hv,edge⟩|⟨hv,hu,edge⟩
  · exact ⟨_,_,edge,Or.inl (raw u v hu hv)⟩
  · exact ⟨_,_,edge,Or.inr ⟨(raw v u hv hu).2,(raw v u hv hu).1⟩⟩
theorem disjoint (x : X) (no : ¬F x) : independent x := by
  intro u v hu hv adj
  obtain ⟨p,l,pl,⟨a,b⟩|⟨a,b⟩⟩ := unbits _ _ adj
  · exact no ⟨p,l,pl,a ▸ hu,b ▸ hv⟩
  · exact no ⟨p,l,pl,b ▸ hv,a ▸ hu⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem color_law : ∀ p l : P, I p l → ∀ u v : V,
    ¬adj u (pt p) → ¬adj u (ln l) → ¬adj v (pt p) → ¬adj v (ln l) →
    color p l u=color p l v → u=v ∨ adj u v := by decide +kernel

theorem common {x y : X} (no : ¬F x) (ny : ¬F y) (cross : F (fun i => x i || y i)) :
    (active x∩active y).card ≤ 9 := by
  obtain ⟨p,l,pl,pbit,lbit⟩ := cross
  simp only [Bool.or_eq_true] at pbit lbit
  have one (i : V) (h : i∈active x∩active y) : x i=true ∧ y i=true :=
    ⟨(Finset.mem_filter.mp (Finset.mem_inter.mp h).1).2,
     (Finset.mem_filter.mp (Finset.mem_inter.mp h).2).2⟩
  have avoid (i : V) (h : i∈active x∩active y) : ¬adj i (pt p) ∧ ¬adj i (ln l) :=
    ⟨pbit.elim (fun t => disjoint x no i _ (one i h).1 t) (fun t => disjoint y ny i _ (one i h).2 t),
     lbit.elim (fun t => disjoint x no i _ (one i h).1 t) (fun t => disjoint y ny i _ (one i h).2 t)⟩
  have sz : (active x∩active y).card ≤ (Finset.univ : Finset (Fin 9)).card := by
    apply Finset.card_le_card_of_injOn (color p l) (fun _ _ => Finset.mem_univ _)
    intro u hu v hv eq
    exact (color_law p l pl u v (avoid u hu).1 (avoid u hu).2 (avoid v hv).1 (avoid v hv).2 eq).resolve_right
      (disjoint x no u v (one u hu).1 (one v hv).1)
  simpa using sz

theorem distinctMax {x y : X} (hx : Maximal (fun z => ¬F z) x)
    (hy : Maximal (fun z => ¬F z) y) (ne : x≠y) : (active x∩active y).card≤9 := by
  apply common hx.prop hy.prop
  by_contra no
  let z : X := fun i => x i || y i
  have xz : x≤z := fun i => Bool.le_iff_imp.mpr (fun h => by simp [z,h])
  have yz : y≤z := fun i => Bool.le_iff_imp.mpr (fun h => by simp [z,h])
  have zx : z≤x := hx.2 no xz
  have zy : z≤y := hy.2 no yz
  exact ne (le_antisymm (xz.trans zy) (yz.trans zx))

noncomputable def missed (f : X → Bool) : Finset V := by
  classical
  exact Finset.univ.filter (fun i => ∀ x : X, f (Function.update x i true)=f x)
theorem contain {f g : X → Bool} (correct : ∀ x, (f x && g x)=true ↔ F x)
    (gmono : ∀ x y : X, x≤y → g x=true → g y=true)
    {x : X} (hx : Maximal (fun z => ¬F z) x) (on : g x=true) : missed f ⊆ active x := by
  classical
  intro i hi
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _,?_⟩
  by_contra bad
  let z := Function.update x i true
  have above : x≤z := by
    intro a
    by_cases eq : a=i
    · subst a; simp [z]
    · simp [z,eq]
  have bit : z i=true := by simp [z]
  have nz : F z := by
    by_contra off
    have zx := hx.2 off above i
    exact bad (Bool.le_iff_imp.mp zx bit)
  have fz : f z=true := (show f z=true ∧ g z=true by simpa only [Bool.and_eq_true] using (correct z).mpr nz).1
  have fx : f x=true := ((Finset.mem_filter.mp hi).2 x) ▸ fz
  exact hx.prop ((correct x).mp (by simp [fx,on]))

theorem oneError {f g : X → Bool} (correct : ∀ x, (f x && g x)=true ↔ F x)
    (gmono : ∀ x y : X, x≤y → g x=true → g y=true)
    (omitCount : 10≤(missed f).card) :
    ∀ x y : X, Maximal (fun z => ¬F z) x → Maximal (fun z => ¬F z) y →
      g x=true → g y=true → x=y := by
  intro x y hx hy gx gy
  by_contra ne
  have sub := Finset.card_le_card (Finset.subset_inter (contain correct gmono hx gx) (contain correct gmono hy gy))
  have lim := distinctMax hx hy ne
  omega

end PEqualNP.Outside.L_meta_8089.Grid

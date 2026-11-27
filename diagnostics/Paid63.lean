import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_8009.Paid
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def W (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

lemma W_snoc (gs : List Gate) (g : Gate) (x : List Bool) : W (gs ++ [g]) x = W gs x ++ [g.op.eval (g.inputs.map fun i => (W gs x).getD i false)] := by
  simp [W, List.foldl_append]

lemma W_len (gs : List Gate) (x : List Bool) : (W gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [W]
  | append_singleton gs g ih => rw [W_snoc]; simp [ih]; omega

def amp (C : Circuit) : Circuit := ⟨C.gates ++ [⟨.and,[C.output,C.output]⟩],26+C.size⟩
theorem getLast {α : Type} (w : List α) (b d : α) : (w++[b]).getD w.length d=b := by
  simp [List.getD_eq_getElem?_getD]
theorem amp_eval (C : Circuit) (x : Fin 26 → Bool) : circuitFun 26 (amp C) x = circuitFun 26 C x := by
  change (W (C.gates++[_]) (List.ofFn x)).getD (26+C.size) false = (W C.gates (List.ofFn x)).getD C.output false
  rw [W_snoc,show 26+C.size=(W C.gates (List.ofFn x)).length by simp [W_len,Circuit.size],getLast]
  simp [GateOp.eval]
theorem amp_size (C : Circuit) : (amp C).size=C.size+1 := by simp [amp,Circuit.size]
theorem amp_mono {C : Circuit} (hm : Monotone2 C) : Monotone2 (amp C) := by
  intro g hg
  rcases List.mem_append.mp hg with old|fresh
  · exact hm g old
  · have e : g=⟨.and,[C.output,C.output]⟩ := by simpa using fresh
    subst g
    exact ⟨by simp,Nat.le_refl 2⟩
abbrev Posted : Prop := let x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (13 : ℕ)) ∨ x1 = x2 + (3 : Fin (13 : ℕ)) ∨ x1 = x2 + (9 : Fin (13 : ℕ)); have x2 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) := fun (x2 : Finset (Fin (13 : ℕ))) => {x3 : Fin (13 : ℕ) | ∀ x4 ∈ x2, ¬x1 x4 x3}; have x3 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) := fun (x3 : Finset (Fin (13 : ℕ))) => {x4 : Fin (13 : ℕ) | ∀ x5 ∈ x3, ¬x1 x4 x5}; have x4 : Finset (Fin (13 : ℕ)) → Prop := fun (x4 : Finset (Fin (13 : ℕ))) => ∀ (x5 : Fin (13 : ℕ)), {x6 ∈ x4 | x1 x6 x5}.card ≤ (2 : ℕ); have x5 : Finset (Fin (13 : ℕ)) → Prop := fun (x5 : Finset (Fin (13 : ℕ))) => ∀ (x6 : Fin (13 : ℕ)), (Finset.filter (x1 x6) x5).card ≤ (2 : ℕ); have x6 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Fin (26 : ℕ) → Bool := fun (x6 x7 : Finset (Fin (13 : ℕ))) (x8 : Fin (26 : ℕ)) => Fin.addCases (fun (x9 : Fin (13 : ℕ)) => Decidable.decide (x9 ∈ x6)) (fun (x9 : Fin (13 : ℕ)) => Decidable.decide (x9 ∈ x7)) x8; ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x7 → x7.size ≤ (63 : ℕ) → (∀ (x10 x11 : Fin (13 : ℕ)), x1 x10 x11 → (PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x7 fun (x13 : Fin (26 : ℕ)) => Decidable.decide (x13 = Fin.castAdd (13 : ℕ) x10 ∨ x13 = Fin.natAdd (13 : ℕ) x11)) = Bool.true) → (PEqualNP.MetaComplexity.NestedCover.gateAt x7 (x7.output - (26 : ℕ))).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (26 : ℕ) ≤ x7.output ∧ x7.output < (26 : ℕ) + x7.size → (∃ (x12 : Finset (Fin (13 : ℕ))), x12.card = (4 : ℕ) ∧ x4 x12 ∧ PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x7 (x6 x12 (x2 x12)) = Bool.true) ∨ ∃ (x12 : Finset (Fin (13 : ℕ))), x12.card = (4 : ℕ) ∧ x5 x12 ∧ PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x7 (x6 (x3 x12) x12) = Bool.true
abbrev Pt := Fin 13
def Inc (p l : Pt) := p=l ∨ p=l+1 ∨ p=l+3 ∨ p=l+9
instance (p l : Pt) : Decidable (Inc p l) := by unfold Inc; infer_instance
def AP (P : Finset Pt) := ∀ l : Pt, (P.filter (fun p => Inc p l)).card≤2
def AL (L : Finset Pt) := ∀ p : Pt, (L.filter (Inc p)).card≤2
def freeL (P : Finset Pt) := Finset.univ.filter (fun l : Pt => ∀ p∈P, ¬Inc p l)
def freeP (L : Finset Pt) := Finset.univ.filter (fun p : Pt => ∀ l∈L, ¬Inc p l)
def vec (P L : Finset Pt) : Fin 26→Bool := Fin.addCases (fun p : Pt => decide (p∈P)) (fun l : Pt => decide (l∈L))
def right (C : Circuit) := ∀ p l, Inc p l → circuitFun 26 C
    (fun z : Fin 26 => decide (z=Fin.castAdd 13 p ∨ z=Fin.natAdd 13 l))=true
def rejects (C : Circuit) := (∀ X : Finset Pt, X.card=4 → AP X → circuitFun 26 C (vec X (freeL X))=false) ∧
    (∀ X : Finset Pt, X.card=4 → AL X → circuitFun 26 C (vec (freeP X) X)=false)
def root (C : Circuit) := (NestedCover.gateAt C (C.output-26)).op=.and ∧
    26≤C.output ∧ C.output<26+C.size

theorem root_iff : Posted ↔ ∀ C : Circuit, Monotone2 C → right C → rejects C → root C → 64≤C.size := by
  constructor
  · intro post C hm on off isRoot
    by_contra! small
    obtain ⟨P,sz,arc,h⟩|⟨L,sz,arc,h⟩ := post C hm (by omega) on isRoot
    · have z := off.1 P sz arc
      change circuitFun 26 C (vec P (freeL P))=true at h
      rw [z] at h
      contradiction
    · have z := off.2 L sz arc
      change circuitFun 26 C (vec (freeP L) L)=true at h
      rw [z] at h
      contradiction
  · intro floor C hm small on isRoot
    classical
    by_contra rejectAll
    have off : rejects C := by
      constructor
      · intro P sz arc
        cases h : circuitFun 26 C (vec P (freeL P))
        · rfl
        · exact False.elim (rejectAll (Or.inl ⟨P,sz,arc,h⟩))
      · intro L sz arc
        cases h : circuitFun 26 C (vec (freeP L) L)
        · rfl
        · exact False.elim (rejectAll (Or.inr ⟨L,sz,arc,h⟩))
    have z := floor C hm on off isRoot
    omega

theorem paidFloor (post : Posted) (C : Circuit) (hm : Monotone2 C) (on : right C) (off : rejects C) :
    63≤C.size := by
  have m : root (amp C) := by
    constructor
    · change ((C.gates++[⟨.and,[C.output,C.output]⟩]).getD (26+C.size-26) ⟨.or,[]⟩).op=.and
      rw [show 26+C.size-26=C.gates.length by change 26+C.gates.length-26=_; omega,getLast]
    · change 26≤26+C.size ∧ 26+C.size<26+(amp C).size
      rw [amp_size]
      omega
  have on' : right (amp C) := fun p l h => (amp_eval C _).trans (on p l h)
  have off' : rejects (amp C) := ⟨fun X sz arc => (amp_eval C _).trans (off.1 X sz arc),
    fun X sz arc => (amp_eval C _).trans (off.2 X sz arc)⟩
  have lower := root_iff.mp post _ (amp_mono hm) on' off' m
  rw [amp_size] at lower
  omega

end PEqualNP.Outside.L_meta_8009.Paid

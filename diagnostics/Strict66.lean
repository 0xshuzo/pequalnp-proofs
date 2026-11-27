import Mathlib
import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_18611.DNF

open PEqualNP.CircuitLowerBounds

def wstep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wstep_len (w : List Bool) (g : Gate) : (wstep w g).length = w.length + 1 := by
  simp [wstep]

lemma wstep_lt (w : List Bool) (g : Gate) (i : ℕ) (hi : i < w.length) :
    (wstep w g).getD i false = w.getD i false := by
  simp [wstep, List.getD, List.getElem?_append_left hi]

lemma wstep_last (w : List Bool) (g : Gate) (k : ℕ) (hk : k = w.length) :
    (wstep w g).getD k false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  subst hk
  simp [wstep, List.getD]

lemma tsnoc_lt (T : List (List (List ℕ))) (a : List (List ℕ)) (i : ℕ) (h : i < T.length) :
    (T ++ [a]).getD i [] = T.getD i [] := by
  simp [List.getD, List.getElem?_append_left h]

lemma tsnoc_eq (T : List (List (List ℕ))) (a : List (List ℕ)) (i : ℕ) (h : i = T.length) :
    (T ++ [a]).getD i [] = a := by
  subst h
  simp [List.getD]

lemma ofFn_getD {n : ℕ} (x : Fin n → Bool) (i : ℕ) (h : i < n) :
    (List.ofFn x).getD i false = x ⟨i, h⟩ := by
  rw [List.getD_eq_getElem _ _ (by simpa using h)]
  first
  | rw [List.getElem_ofFn]
  | simp

def evalD (v : ℕ → Bool) (D : List (List ℕ)) : Bool := D.any fun c => c.all v

def prodD (D1 D2 : List (List ℕ)) : List (List ℕ) :=
  D1.flatMap fun c1 => D2.map fun c2 => c1 ++ c2

lemma evalD_append (v : ℕ → Bool) (D1 D2 : List (List ℕ)) :
    evalD v (D1 ++ D2) = (evalD v D1 || evalD v D2) := by
  unfold evalD
  rw [List.any_append]

lemma evalD_prod (v : ℕ → Bool) (D1 D2 : List (List ℕ)) :
    evalD v (prodD D1 D2) = (evalD v D1 && evalD v D2) := by
  rw [Bool.eq_iff_iff]
  simp only [evalD, prodD, List.any_eq_true, List.mem_flatMap, List.mem_map, Bool.and_eq_true,
    List.all_eq_true]
  constructor
  · rintro ⟨c, ⟨c1, h1, c2, h2, rfl⟩, hc⟩
    exact ⟨⟨c1, h1, fun i hi => hc i (List.mem_append_left _ hi)⟩,
      ⟨c2, h2, fun i hi => hc i (List.mem_append_right _ hi)⟩⟩
  · rintro ⟨⟨c1, h1, a1⟩, ⟨c2, h2, a2⟩⟩
    refine ⟨c1 ++ c2, ⟨c1, h1, c2, h2, rfl⟩, fun i hi => ?_⟩
    rcases List.mem_append.mp hi with h | h
    · exact a1 i h
    · exact a2 i h

def gD (T : List (List (List ℕ))) (g : Gate) : List (List ℕ) :=
  match g.op with
  | GateOp.and => (g.inputs.map fun i => T.getD i []).foldr prodD [[]]
  | _ => (g.inputs.map fun i => T.getD i []).foldr (fun a b => a ++ b) []

def okb (g : Gate) : Bool :=
  match g.op with
  | GateOp.and => decide (g.inputs.length ≤ 2)
  | GateOp.or => decide (g.inputs.length ≤ 2)
  | _ => false

def tstep (T : List (List (List ℕ))) (g : Gate) : List (List (List ℕ)) := T ++ [gD T g]

lemma all_spec (v : ℕ → Bool) (w : List Bool) (T : List (List (List ℕ)))
    (h : ∀ i, w.getD i false = evalD v (T.getD i [])) (l : List ℕ) :
    (l.map fun i => w.getD i false).all id
      = evalD v ((l.map fun i => T.getD i []).foldr prodD [[]]) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    show (id (w.getD a false) && (l.map fun i => w.getD i false).all id)
      = evalD v (prodD (T.getD a []) ((l.map fun i => T.getD i []).foldr prodD [[]]))
    rw [evalD_prod, ← ih, h a]
    rfl

lemma any_spec (v : ℕ → Bool) (w : List Bool) (T : List (List (List ℕ)))
    (h : ∀ i, w.getD i false = evalD v (T.getD i [])) (l : List ℕ) :
    (l.map fun i => w.getD i false).any id
      = evalD v ((l.map fun i => T.getD i []).foldr (fun a b => a ++ b) []) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    show (id (w.getD a false) || (l.map fun i => w.getD i false).any id)
      = evalD v (T.getD a [] ++ ((l.map fun i => T.getD i []).foldr (fun a b => a ++ b) []))
    rw [evalD_append, ← ih, h a]
    rfl

lemma gD_spec (v : ℕ → Bool) (w : List Bool) (T : List (List (List ℕ)))
    (h : ∀ i, w.getD i false = evalD v (T.getD i [])) (g : Gate) (hg : okb g = true) :
    g.op.eval (g.inputs.map fun i => w.getD i false) = evalD v (gD T g) := by
  obtain ⟨op, ins⟩ := g
  cases op with
  | and => exact all_spec v w T h ins
  | or => exact any_spec v w T h ins
  | not => exact absurd hg Bool.false_ne_true
  | mod m => exact absurd hg Bool.false_ne_true
  | maj => exact absurd hg Bool.false_ne_true

lemma okb_spec (g : Gate) (hg : okb g = true) :
    g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  obtain ⟨op, ins⟩ := g
  cases op with
  | and => exact ⟨Or.inl rfl, of_decide_eq_true hg⟩
  | or => exact ⟨Or.inr rfl, of_decide_eq_true hg⟩
  | not => exact absurd hg Bool.false_ne_true
  | mod m => exact absurd hg Bool.false_ne_true
  | maj => exact absurd hg Bool.false_ne_true

def Good (v : ℕ → Bool) (w : List Bool) (T : List (List (List ℕ))) : Prop :=
  w.length = T.length ∧ ∀ i, w.getD i false = evalD v (T.getD i [])

lemma good_step (v : ℕ → Bool) (w : List Bool) (T : List (List (List ℕ))) (g : Gate)
    (hg : okb g = true) (h : Good v w T) : Good v (wstep w g) (tstep T g) := by
  obtain ⟨hl, hv⟩ := h
  refine ⟨?_, fun i => ?_⟩
  · show (wstep w g).length = (T ++ [gD T g]).length
    rw [wstep_len, List.length_append, List.length_singleton, hl]
  · show (wstep w g).getD i false = evalD v ((T ++ [gD T g]).getD i [])
    by_cases hlt : i < T.length
    · rw [tsnoc_lt T _ i hlt, wstep_lt _ _ _ (by rw [hl]; exact hlt)]
      exact hv i
    · by_cases heq : i = T.length
      · rw [tsnoc_eq T _ i heq, wstep_last _ _ _ (by rw [hl]; exact heq)]
        exact gD_spec v w T hv g hg
      · have h1 : (T ++ [gD T g]).getD i [] = [] :=
          List.getD_eq_default _ _ (by rw [List.length_append, List.length_singleton]; omega)
        have h2 : (wstep w g).getD i false = false :=
          List.getD_eq_default _ _ (by rw [wstep_len, hl]; omega)
        rw [h1, h2]
        rfl

lemma good_fold (v : ℕ → Bool) (gs : List Gate) (hg : ∀ g ∈ gs, okb g = true) :
    ∀ (w : List Bool) (T : List (List (List ℕ))), Good v w T →
      Good v (gs.foldl wstep w) (gs.foldl tstep T) := by
  induction gs with
  | nil =>
    intro w T h
    exact h
  | cons g gs ih =>
    intro w T h
    exact ih (fun g' hg' => hg g' (List.mem_cons.mpr (Or.inr hg'))) _ _
      (good_step v w T g (hg g (List.mem_cons.mpr (Or.inl rfl))) h)

def T0 : List (List (List ℕ)) := (List.range 26).map fun i => [[i]]

lemma T0_len : T0.length = 26 := by decide +kernel

lemma T0_get : ∀ i < 26, T0.getD i [] = [[i]] := by decide +kernel

lemma good_init (x : Fin 26 → Bool) :
    Good (fun i => x (Fin.ofNat 26 i)) (List.ofFn x) T0 := by
  refine ⟨by rw [List.length_ofFn, T0_len], fun i => ?_⟩
  by_cases h : i < 26
  · rw [ofFn_getD x i h, T0_get i h]
    show x ⟨i, h⟩ = ((x (Fin.ofNat 26 i) && true) || false)
    rw [Bool.and_true, Bool.or_false]
    exact congrArg x (Fin.ext (Nat.mod_eq_of_lt h).symm)
  · have h1 : (List.ofFn x).getD i false = false :=
      List.getD_eq_default _ _ (by rw [List.length_ofFn]; omega)
    have h2 : T0.getD i [] = [] := List.getD_eq_default _ _ (by rw [T0_len]; omega)
    rw [h1, h2]
    rfl

end PEqualNP.Outside.L_meta_18611.DNF

namespace PEqualNP.Outside.L_meta_18611.Near
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_18611.DNF (evalD tstep okb T0 good_fold good_init)
set_option maxRecDepth 12000
set_option maxHeartbeats 5000000
def C : Circuit := ⟨[⟨.or,[13,17]⟩,⟨.or,[26,23]⟩,⟨.or,[14,15]⟩,⟨.or,[28,19]⟩,⟨.or,[0,2]⟩,⟨.and,[0,27]⟩,⟨.or,[25,31]⟩,⟨.or,[2,32]⟩,⟨.or,[29,32]⟩,⟨.and,[30,33]⟩,⟨.and,[34,35]⟩,⟨.or,[13,14]⟩,⟨.or,[37,18]⟩,⟨.or,[38,24]⟩,⟨.and,[1,39]⟩,⟨.or,[13,15]⟩,⟨.or,[41,16]⟩,⟨.or,[42,20]⟩,⟨.and,[3,43]⟩,⟨.or,[14,16]⟩,⟨.or,[45,17]⟩,⟨.or,[46,21]⟩,⟨.and,[4,47]⟩,⟨.or,[15,17]⟩,⟨.or,[49,18]⟩,⟨.or,[50,22]⟩,⟨.and,[5,51]⟩,⟨.or,[16,18]⟩,⟨.or,[53,19]⟩,⟨.or,[54,23]⟩,⟨.and,[6,55]⟩,⟨.or,[17,19]⟩,⟨.or,[57,20]⟩,⟨.or,[58,24]⟩,⟨.and,[7,59]⟩,⟨.or,[18,20]⟩,⟨.or,[61,21]⟩,⟨.or,[62,25]⟩,⟨.and,[8,63]⟩,⟨.or,[13,19]⟩,⟨.or,[65,21]⟩,⟨.or,[66,22]⟩,⟨.and,[9,67]⟩,⟨.or,[14,20]⟩,⟨.or,[69,22]⟩,⟨.or,[70,23]⟩,⟨.and,[10,71]⟩,⟨.or,[15,21]⟩,⟨.or,[73,23]⟩,⟨.or,[74,24]⟩,⟨.and,[11,75]⟩,⟨.or,[16,22]⟩,⟨.or,[77,24]⟩,⟨.or,[78,25]⟩,⟨.and,[12,79]⟩,⟨.or,[36,40]⟩,⟨.or,[81,44]⟩,⟨.or,[82,48]⟩,⟨.or,[83,52]⟩,⟨.or,[84,56]⟩,⟨.or,[85,60]⟩,⟨.or,[86,64]⟩,⟨.or,[87,68]⟩,⟨.or,[88,72]⟩,⟨.or,[89,76]⟩,⟨.or,[90,80]⟩],91⟩
def offsets : Finset (Fin 13) := {0,1,3,9}
def terms := (C.gates.foldl tstep T0).getD C.output []
lemma reflect (x : Fin 26 → Bool) :
    C.eval (List.ofFn x) = evalD (fun i => x (Fin.ofNat 26 i)) terms := by
  have ok : ∀ g∈C.gates, okb g=true := by decide +kernel
  exact (good_fold _ C.gates ok _ _ (good_init x)).2 C.output

def flags : List (Fin 13 × Fin 13) := [(0,0),(0,4),(0,10),(0,12),(1,0),(1,1),(1,5),(1,11),(2,1),(2,2),(2,6),(2,12),(3,0),(3,2),(3,3),(3,7),(4,1),(4,3),(4,4),(4,8),(5,2),(5,4),(5,5),(5,9),(6,3),(6,5),(6,6),(6,10),(7,4),(7,6),(7,7),(7,11),(8,5),(8,7),(8,8),(8,12),(9,0),(9,6),(9,8),(9,9),(10,1),(10,7),(10,9),(10,10),(11,2),(11,8),(11,10),(11,11),(12,3),(12,9),(12,11),(12,12)]
lemma member : ∀ p l : Fin 13, (p,l) ∈ flags ↔ p-l ∈ offsets := by decide +kernel
lemma contains : ∀ term∈terms, ∃ e∈flags, e.1.val∈term ∧ (13+e.2.val)∈term := by decide +kernel
lemma complete : ∀ e∈flags, ∃ term∈terms, ∀ i∈term, i=e.1.val ∨ i=13+e.2.val := by decide +kernel

lemma correct (x : Fin 26 → Bool) : C.eval (List.ofFn x)=true ↔
    ∃ p l : Fin 13, p-l∈offsets ∧ x (Fin.castAdd 13 p)=true ∧ x (Fin.natAdd 13 l)=true := by
  have point : ∀ p : Fin 13, Fin.ofNat 26 p.val=Fin.castAdd 13 p := by decide
  have line : ∀ l : Fin 13, Fin.ofNat 26 (13+l.val)=Fin.natAdd 13 l := by decide
  rw [reflect,evalD,List.any_eq_true]
  constructor
  · rintro ⟨z,hz,good⟩
    obtain ⟨⟨p,l⟩,hf,hp,hl⟩ := contains z hz
    have on := List.all_eq_true.mp good
    exact ⟨p,l,(member p l).mp hf,by simpa only [point] using on p.val hp,
      by simpa only [line] using on (13+l.val) hl⟩
  · rintro ⟨p,l,hf,hp,hl⟩
    obtain ⟨z,hz,sub⟩ := complete (p,l) ((member p l).mpr hf)
    refine ⟨z,hz,List.all_eq_true.mpr ?_⟩
    intro i hi
    rcases sub i hi with rfl | rfl
    · simpa only [point] using hp
    · simpa only [line] using hl

local instance : DecidableEq GateOp := gateOpDecEq

def legal (j : Nat) (g : Gate) : Prop := (g.op=.and ∨ g.op=.or) ∧ ∃ a b : Nat, g.inputs=[a,b] ∧ a≠b ∧ a<26+j ∧ b<26+j

theorem gateTest : ∀ j : Fin 66, let g := C.gates.getD j.val ⟨.or,[]⟩; (g.op=.and ∨ g.op=.or) ∧ g.inputs=[g.inputs.getD 0 0,g.inputs.getD 1 0] ∧ g.inputs.getD 0 0≠g.inputs.getD 1 0 ∧ g.inputs.getD 0 0<26+j.val ∧ g.inputs.getD 1 0<26+j.val := by decide +kernel

theorem gateLegal (j : Nat) (g : Gate) (h : C.gates[j]?=some g) : legal j g := by
  obtain ⟨hj,e⟩ := List.getElem?_eq_some_iff.mp h
  have v := gateTest ⟨j,hj⟩
  have ge : C.gates.getD j ⟨.or,[]⟩=g := by rw [List.getD_eq_getElem _ _ hj,e]
  change (_ ∨ _) ∧ _ at v
  simp only [ge] at v
  exact ⟨v.1,_,_,v.2⟩

theorem boundary : ¬(¬∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit),     have x2 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))};     have x3 : PEqualNP.CircuitLowerBounds.GateOp := PEqualNP.CircuitLowerBounds.GateOp.and;     have x4 : ℕ → (Fin (26 : ℕ) → Bool) → Bool := PEqualNP.EdgeOwnership.gateVal (26 : ℕ) x1;     have x5 : ℕ → (Fin (26 : ℕ) → Bool) → Bool := PEqualNP.CleanedNonEdge.wireVal (26 : ℕ) x1;     have x6 : ℕ → Prop := fun (x6 : ℕ) => (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x6).op = x3;     have x7 : Fin (26 : ℕ) → Bool := PEqualNP.EdgeOwnership.pairInput (0 : Fin (26 : ℕ)) (0 : Fin (26 : ℕ));     have x8 : Fin (26 : ℕ) → Bool := PEqualNP.EdgeOwnership.pairInput (13 : Fin (26 : ℕ)) (13 : Fin (26 : ℕ));     have x9 : Fin (26 : ℕ) → Bool := PEqualNP.EdgeOwnership.pairInput (0 : Fin (26 : ℕ)) (13 : Fin (26 : ℕ));     x1.size ≤ (66 : ℕ) ∧ (∀ (x10 : ℕ) (x11 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x10]? = Option.some x11 → (x11.op = x3 ∨ x11.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x13 : ℕ) (x14 : ℕ), x11.inputs = [x13, x14] ∧ x13 ≠ x14 ∧ x13 < (26 : ℕ) + x10 ∧ x14 < (26 : ℕ) + x10) ∧ (∀ (x10 : Fin (26 : ℕ) → Bool), x1.eval (List.ofFn x10) = Bool.true ↔ ∃ (x11 : Fin (13 : ℕ)) (x12 : Fin (13 : ℕ)), x11 - x12 ∈ x2 ∧ x10 (Fin.castAdd (13 : ℕ) x11) = Bool.true ∧ x10 (Fin.natAdd (13 : ℕ) x12) = Bool.true) ∧ (∃ x10 < x1.gates.length, x6 x10 ∧ ∃ (x11 : Fin (26 : ℕ) → Bool), x4 x10 x11 = Bool.true ∧ x1.eval (List.ofFn x11) = Bool.false) ∧ ∃ (x10 : ℕ), x6 x10 ∧ PEqualNP.EdgeOwnership.InCone (26 : ℕ) x1 x10 (x1.output - (26 : ℕ)) ∧ x4 x10 x9 = Bool.true ∧ ∀ (x11 : Fin (2 : ℕ)), x5 (PEqualNP.TopForm.opnd x1 x10 x11) x7 = Bool.false ∧ x5 (PEqualNP.TopForm.opnd x1 x10 x11) x8 = Bool.false) := by
  intro no
  apply no
  refine ⟨C, by decide, gateLegal, correct, ?_, ?_⟩
  · exact ⟨9, by decide, by decide, (fun i : Fin 26 => decide (i=2)), by decide +kernel, by decide +kernel⟩
  · exact ⟨10, by decide, by decide +kernel, by decide +kernel, by decide +kernel⟩
end PEqualNP.Outside.L_meta_18611.Near

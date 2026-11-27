import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_11094.Clone
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

lemma getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

def wmap (n m : ℕ) (π : Fin n → Fin m) (w : ℕ) : ℕ :=
  if h : w < n then (π ⟨w, h⟩ : ℕ) else w - n + m

def relGate (n m : ℕ) (π : Fin n → Fin m) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (wmap n m π)⟩

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def Rel (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) : Prop :=
  n ≤ W.length ∧ W'.length + n = W.length + m ∧
    ∀ w : ℕ, W'.getD (wmap n m π w) false = W.getD w false

lemma rel_step (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) (g : Gate)
    (h : Rel n m π W W') : Rel n m π (step W g) (step W' (relGate n m π g)) := by
  obtain ⟨h1, h2, h3⟩ := h
  have hv : (relGate n m π g).op.eval
      ((relGate n m π g).inputs.map fun i => W'.getD i false)
      = g.op.eval (g.inputs.map fun i => W.getD i false) := by
    simp only [relGate, List.map_map]
    congr 1
    apply List.map_congr_left
    intro a _
    exact h3 a
  refine ⟨by simp [step]; omega, by simp [step]; omega, ?_⟩
  intro w
  simp only [step, hv]
  rcases Nat.lt_trichotomy w W.length with hw | hw | hw
  · have hlt : wmap n m π w < W'.length := by
      unfold wmap
      split
      · have := (π ⟨w, by assumption⟩).2; omega
      · omega
    rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ hw]
    exact h3 w
  · have he : wmap n m π w = W'.length := by
      unfold wmap
      split
      · omega
      · omega
    rw [he, hw, getD_snoc_eq, getD_snoc_eq]
  · have hge : W'.length + 1 ≤ wmap n m π w := by
      unfold wmap
      split
      · omega
      · omega
    rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

lemma rel_fold (n m : ℕ) (π : Fin n → Fin m) (gs : List Gate) :
    ∀ W W' : List Bool, Rel n m π W W' →
      Rel n m π (gs.foldl step W) ((gs.map (relGate n m π)).foldl step W') := by
  induction gs with
  | nil => intro W W' h; exact h
  | cons g gs ih =>
    intro W W' h
    exact ih _ _ (rel_step n m π W W' g h)

variable {n m : Nat}

def ref (ρ : Fin n → Fin m) (j u : Fin n) : Fin (m+1) :=
  if u=j then Fin.last m else (ρ u).castSucc

def folded (ρ : Fin n → Fin m) (j : Fin n) (b : Fin m) (x : Fin m → Bool) (u : Fin n) : Bool :=
  if u=j then x (ρ j) || x b else x (ρ u)

def headGate (ρ : Fin n → Fin m) (j : Fin n) (b : Fin m) : Gate :=
  ⟨.or, [(ρ j).val,b.val]⟩

def lift (ρ : Fin n → Fin m) (j : Fin n) (b : Fin m) (C : Circuit) : Circuit :=
  ⟨headGate ρ j b :: C.gates.map (relGate n (m+1) (ref ρ j)),
   wmap n (m+1) (ref ρ j) C.output⟩

theorem cost (ρ : Fin n → Fin m) (j : Fin n) (b : Fin m) (C : Circuit) :
    (lift ρ j b C).size = C.size + 1 := by simp [Circuit.size,lift]

theorem mono (ρ : Fin n → Fin m) (j : Fin n) (b : Fin m) {C : Circuit} (h : Monotone2 C) :
    Monotone2 (lift ρ j b C) := by
  intro g hg
  change g ∈ headGate ρ j b :: C.gates.map _ at hg
  rcases List.mem_cons.mp hg with rfl|hg
  · simp [headGate]
  · obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hg
    simpa [relGate] using h k hk

theorem evaluation (ρ : Fin n → Fin m) (j : Fin n) (b : Fin m) (C : Circuit) (x : Fin m → Bool) :
    (lift ρ j b C).eval (List.ofFn x) = C.eval (List.ofFn (folded ρ j b x)) := by
  let y := x (ρ j) || x b
  have startWire : step (List.ofFn x) (headGate ρ j b) = List.ofFn x ++ [y] := by
    simp [step,headGate,y,GateOp.eval,List.getD_eq_getElem?_getD]
  have base : Rel n (m+1) (ref ρ j) (List.ofFn (folded ρ j b x)) (List.ofFn x ++ [y]) := by
    refine ⟨by simp,by simp <;> omega,?_⟩
    intro w
    by_cases h : w<n
    · let u : Fin n := ⟨w,h⟩
      have raw : (List.ofFn (folded ρ j b x)).getD w false = folded ρ j b x u := by
        simp [u,List.getD_eq_getElem?_getD,h]
      rw [raw,show wmap n (m+1) (ref ρ j) w=((ref ρ j) u).val by simp [wmap,h,u]]
      by_cases hu : u=j
      · simp [ref,hu,folded,y,List.getD_eq_getElem?_getD]
      · rw [show ((ref ρ j) u).val=(ρ u).val by simp [ref,hu],
          List.getD_append _ _ _ _ (by simp)]
        simp [folded,hu,List.getD_eq_getElem?_getD]
    · have newIndex : (List.ofFn x ++ [y]).length ≤ wmap n (m+1) (ref ρ j) w := by
        simp [wmap,h]
      rw [List.getD_eq_default _ _ newIndex,List.getD_eq_default _ _ (by simp <;> omega)]
  have finish := (rel_fold n (m+1) (ref ρ j) C.gates _ _ base).2.2 C.output
  change ((C.gates.map _).foldl step (step (List.ofFn x) (headGate ρ j b))).getD _ false = _
  rw [startWire]
  exact finish


open PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.EdgeOwnership
open PEqualNP.CleanedNonEdge

def plain (π : Fin n → Fin m) (C : Circuit) : Circuit :=
  ⟨C.gates.map (relGate n m π),wmap n m π C.output⟩

theorem plain_eval (π : Fin n → Fin m) (C : Circuit) (x : Fin m → Bool) :
    (plain π C).eval (List.ofFn x) = C.eval (List.ofFn (fun i => x (π i))) := by
  have base : Rel n m π (List.ofFn (fun i => x (π i))) (List.ofFn x) := by
    refine ⟨by simp, by simp [Nat.add_comm], ?_⟩
    intro w
    by_cases h : w < n
    · simp [wmap,h,List.getD_eq_getElem?_getD]
    · have high : m ≤ wmap n m π w := by simp [wmap,h]
      rw [List.getD_eq_default _ _ (by simpa using high),List.getD_eq_default _ _ (by simp; omega)]
  exact (rel_fold n m π C.gates _ _ base).2.2 _

theorem gateAt_map (π : Fin n → Fin m) (C : Circuit) {i : Nat} (hi : i<C.gates.length) :
    gateAt (plain π C) i = relGate n m π (gateAt C i) := by
  simp [gateAt,plain,List.getD_eq_getElem?_getD,hi]

theorem mapped_earlier (π : Fin n → Fin m) {i w : Nat} (h : w<n+i) :
    wmap n m π w < m+i := by
  unfold wmap
  split
  next hw => have := (π ⟨w,hw⟩).isLt; omega
  next _ => omega

theorem plain_ao (π : Fin n → Fin m) {C : Circuit} (h : IsAO2 n C) : IsAO2 m (plain π C) := by
  refine ⟨?_,?_,?_⟩
  · intro g hg
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hg
    exact h.1 a ha
  · intro i hi w hw
    have hi' : i<C.gates.length := by simpa [plain] using hi
    rw [gateAt_map π C hi'] at hw
    obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hw
    exact mapped_earlier π (h.2.1 i hi' v hv)
  · intro g hg
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hg
    simpa [relGate] using h.2.2 a ha

theorem lift_ao (ρ : Fin n → Fin m) (j : Fin n) (b : Fin m) {C : Circuit} (h : IsAO2 n C) :
    IsAO2 m (lift ρ j b C) := by
  let p := ref ρ j
  have ho := plain_ao p h
  refine ⟨?_,?_,?_⟩
  · intro g hg
    rcases List.mem_cons.mp hg with rfl|hg
    · exact Or.inr rfl
    · exact ho.1 g hg
  · intro i hi w hw
    cases i with
    | zero =>
      change w ∈ [(ρ j).val,b.val] at hw
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
      rcases hw with rfl|rfl <;> simp
    | succ i =>
      have hi' : i < (plain p C).gates.length := by simpa [plain,lift] using hi
      change w ∈ (gateAt (plain p C) i).inputs at hw
      have hh := ho.2.1 i hi' w hw
      omega
  · intro g hg
    rcases List.mem_cons.mp hg with rfl|hg
    · rfl
    · exact ho.2.2 g hg

def project (j : Fin n) : Fin (n+1) → Fin n := Fin.cases j id

def dup (G : SimpleGraph (Fin n)) (j : Fin n) : SimpleGraph (Fin (n+1)) :=
  G.comap (project j)

instance (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (j : Fin n) :
    DecidableRel (dup G j).Adj := fun a b => inferInstanceAs (Decidable (G.Adj (project j a) (project j b)))

theorem folded_iff (j u : Fin n) (x : Fin (n+1) → Bool) :
    folded Fin.succ j 0 x u = true ↔ ∃ a, project j a = u ∧ x a = true := by
  constructor
  · intro ht
    by_cases h : u=j
    · subst u
      simp only [folded,if_pos rfl,Bool.or_eq_true] at ht
      rcases ht with h|h
      · exact ⟨j.succ,rfl,h⟩
      · exact ⟨0,rfl,h⟩
    · exact ⟨u.succ,rfl,by simpa [folded,h] using ht⟩
  · rintro ⟨a,ha,hx⟩
    refine Fin.cases ?_ (fun v => ?_) a ha hx
    · intro hu hv
      change j = u at hu
      subst u
      simp [folded,hv]
    · intro hu hv
      change v = u at hu
      subst u
      by_cases h : v = j <;> simp_all [folded]

theorem graph_fold (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (j : Fin n)
    (x : Fin (n+1) → Bool) : graphFun (dup G j) ∅ x = graphFun G ∅ (folded Fin.succ j 0 x) := by
  simp only [graphFun,Finset.notMem_empty,false_and,exists_false,decide_false,Bool.false_or]
  congr 1
  apply propext
  constructor
  · rintro ⟨a,b,hab,ha,hb⟩
    exact ⟨project j a,project j b,hab,(folded_iff _ _ _).mpr ⟨a,rfl,ha⟩,
      (folded_iff _ _ _).mpr ⟨b,rfl,hb⟩⟩
  · rintro ⟨u,v,huv,hu,hv⟩
    obtain ⟨a,rfl,ha⟩ := (folded_iff _ _ _).mp hu
    obtain ⟨b,rfl,hb⟩ := (folded_iff _ _ _).mp hv
    exact ⟨a,b,huv,ha,hb⟩

theorem folded_pin (j : Fin n) (x : Fin (n+1) → Bool) :
    folded Fin.succ j 0 (Function.update x 0 false) = fun i => x i.succ := by
  funext i
  by_cases h : i=j <;> simp [folded,h]

theorem folded_pull (j : Fin n) (x : Fin n → Bool) :
    folded Fin.succ j 0 (fun v => x (project j v)) = x := by
  funext i
  by_cases h : i=j <;> simp [folded,h,project]

theorem lifted_dirty (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (j : Fin n)
    (C : Circuit) (hd : (junk G C).Nonempty) :
    (junk (dup G j) (lift Fin.succ j 0 C)).Nonempty := by
  obtain ⟨i,hi⟩ := hd
  obtain ⟨hi,hg,hx⟩ := Finset.mem_filter.mp hi
  obtain ⟨_,x,hon,hoff⟩ := hx
  have hil : i<C.gates.length := Finset.mem_range.mp hi
  have newlen : i+1 < (lift Fin.succ j 0 C).gates.length := by simp [lift]; omega
  let y := fun v => x (project j v)
  have hf : folded Fin.succ j 0 y = x := folded_pull j x
  refine ⟨i+1,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr newlen,?_,newlen,y,?_,?_⟩⟩
  · change (gateAt (plain (ref Fin.succ j) C) i).op = .and
    rw [gateAt_map _ _ (Finset.mem_range.mp hi)]
    exact hg
  · have ev := evaluation Fin.succ j 0 (⟨C.gates,n+i⟩ : Circuit) y
    rw [hf] at ev
    have ix : wmap n ((n+1)+1) (ref Fin.succ j) (n+i) = (n+1)+(i+1) := by
      simp [wmap] <;> omega
    change ((lift Fin.succ j 0 C).wires (List.ofFn y)).getD ((n+1)+(i+1)) false = true
    rw [←ix]
    exact ev.trans hon
  · rw [graph_fold,hf]
    exact hoff

end PEqualNP.Outside.L_meta_11094.Clone

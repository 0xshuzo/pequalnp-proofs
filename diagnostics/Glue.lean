import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.Frame4594
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.SyntacticMultilinear PEqualNP.CrossAnd

def shift (n d i : ℕ) : ℕ := if i<n then i else d+i

def move (n d : ℕ) (g : Gate) : Gate := ⟨g.op,g.inputs.map (shift n d)⟩

def push {α : Type} (z : α) (ev : GateOp → List α → α) (xs : List α) (g : Gate) : List α :=
  xs ++ [ev g.op (g.inputs.map fun i => xs.getD i z)]

lemma frameRead {α : Type} (z : α) (raw mid post : List α) (i : ℕ) :
    ((raw++mid)++post).getD (shift raw.length mid.length i) z = (raw++post).getD i z := by
  by_cases h : i < raw.length
  · simp only [shift,h,if_true,List.append_assoc]
    rw [List.getD_append _ _ _ _ h,List.getD_append _ _ _ _ h]
  · simp only [shift,h,if_false]
    rw [List.getD_append_right _ _ _ _ (by simp; omega),List.getD_append_right _ _ _ _ (by omega)]
    simp only [List.length_append]
    congr 1 <;> omega

lemma frameRun {α : Type} (z : α) (ev : GateOp → List α → α) (raw mid : List α)
    (gs : List Gate) (post : List α) :
    ∃ more : List α,
      (gs.map (move raw.length mid.length)).foldl (push z ev) ((raw++mid)++post) =
        (raw++mid)++more ∧
      gs.foldl (push z ev) (raw++post) = raw++more := by
  induction gs generalizing post with
  | nil => exact ⟨post,rfl,rfl⟩
  | cons g gs ih =>
    simp only [List.map_cons,List.foldl_cons]
    let v := ev g.op (g.inputs.map fun i => (raw++post).getD i z)
    have he : ev (move raw.length mid.length g).op
        ((move raw.length mid.length g).inputs.map fun i => ((raw++mid)++post).getD i z) = v := by
      simp only [move,List.map_map,Function.comp_def,frameRead,v]
    have big : push z ev ((raw++mid)++post) (move raw.length mid.length g) =
          (raw++mid)++(post++[v]) := by rw [push,he,List.append_assoc]
    have small : push z ev (raw++post) g = raw++(post++[v]) := List.append_assoc .. 
    rw [big,small]
    exact ih (post++[v])

lemma runTail {α : Type} (z : α) (ev : GateOp → List α → α) (xs : List α) (gs : List Gate) :
    ∃ mid : List α, gs.foldl (push z ev) xs = xs++mid ∧ mid.length=gs.length := by
  induction gs generalizing xs with
  | nil => exact ⟨[],by simp,rfl⟩
  | cons g gs ih =>
    obtain ⟨tail,he,hl⟩ := ih (push z ev xs g)
    refine ⟨ev g.op (g.inputs.map fun i => xs.getD i z)::tail,?_,?_⟩
    · simpa [List.foldl_cons,push,List.append_assoc] using he
    · simp [hl]

def unionValues {n : ℕ} (_ : GateOp) (r : List (Finset (Fin n))) : Finset (Fin n) :=
  r.foldr (· ∪ ·) ∅

lemma support_form {n : ℕ} : @supportStep n = push (∅ : Finset (Fin n)) unionValues := by
  funext xs g
  unfold supportStep push unionValues
  have ef (ws : List ℕ) :
      ws.foldr (fun w acc => xs.getD w ∅ ∪ acc) ∅ =
        (ws.map fun i => xs.getD i ∅).foldr (· ∪ ·) ∅ := by
    induction ws with
    | nil => rfl
    | cons a ws ih => simp only [List.foldr_cons,List.map_cons,ih]
  rw [ef]

def stages (n : ℕ) (D E : Circuit) := D.gates ++ E.gates.map (move n D.size)

def merger (n : ℕ) (D E : Circuit) : Gate :=
  let b := shift n D.size E.output
  ⟨.or,[if D.output<n+D.size then D.output else b,b]⟩

def joined (n : ℕ) (D E : Circuit) : Circuit :=
  ⟨stages n D E ++ [merger n D E],n+D.size+E.size⟩

lemma stageRead {α : Type} (z : α) (ev : GateOp → List α → α) (xs : List α)
    (n : ℕ) (hlen : xs.length=n) (D E : Circuit) :
    let st := (stages n D E).foldl (push z ev) xs
    (∀ i < n+D.size, st.getD i z = (D.gates.foldl (push z ev) xs).getD i z) ∧
    (∀ i, st.getD (shift n D.size i) z = (E.gates.foldl (push z ev) xs).getD i z) ∧
    st.length=n+D.size+E.size := by
  dsimp only
  obtain ⟨mid,hD,lD⟩ := runTail z ev xs D.gates
  change mid.length = D.size at lD
  obtain ⟨more,pref,post⟩ := frameRun z ev xs mid E.gates []
  simp only [List.append_nil,hlen,lD] at pref post
  have st : (stages n D E).foldl (push z ev) xs = (xs++mid)++more := by
    rw [stages,List.foldl_append,hD,pref]
  refine ⟨?_,?_,?_⟩
  · intro i bound
    rw [st,hD,List.getD_append _ _ _ _ (by simp [hlen,lD,bound])]
  · intro i
    rw [st,post,← hlen,← lD]
    exact frameRead z xs mid more i
  · obtain ⟨extra,hX,lX⟩ := runTail z ev xs (stages n D E)
    rw [hX,List.length_append,hlen,lX]
    simp [stages,Circuit.size,Nat.add_assoc]

lemma joinSize (n : ℕ) (D E : Circuit) : (joined n D E).size = D.size+E.size+1 := by
  simp [joined,stages,Circuit.size]

lemma joinMono {n : ℕ} {D E : Circuit} (hD : Monotone2 D) (hE : Monotone2 E) :
    Monotone2 (joined n D E) := by
  intro g hg
  simp only [joined,stages,List.mem_append,List.mem_map,List.mem_singleton] at hg
  rcases hg with (hd|⟨f,hf,rfl⟩)|rfl
  · exact hD _ hd
  · obtain ⟨ops,sz⟩ := hE _ hf
    exact ⟨ops,by simpa [move] using sz⟩
  · exact ⟨Or.inr rfl,by simp [merger]⟩

lemma joinEval {n : ℕ} (D E : Circuit) (xs : List Bool) (hlen : xs.length=n) :
    (joined n D E).eval xs = (D.eval xs || E.eval xs) := by
  obtain ⟨old,ren,len⟩ := stageRead false GateOp.eval xs n hlen D E
  let w := (stages n D E).foldl (push false GateOp.eval) xs
  change w.length=n+D.size+E.size at len
  change ((stages n D E ++ [merger n D E]).foldl (push false GateOp.eval) xs).getD
    (n+D.size+E.size) false = _
  rw [List.foldl_append]
  change (w ++ [(merger n D E).op.eval ((merger n D E).inputs.map fun i => w.getD i false)]).getD
    (n+D.size+E.size) false = _
  rw [List.getD_append_right _ _ _ _ (by omega),← len,Nat.sub_self]
  change (w.getD (if D.output<n+D.size then D.output else shift n D.size E.output) false ||
    (w.getD (shift n D.size E.output) false || false)) = _
  have hr : w.getD (shift n D.size E.output) false = E.eval xs := ren _
  rw [Bool.or_false,hr]
  by_cases valid : D.output < n+D.size
  · rw [if_pos valid,old D.output valid]
    rfl
  · rw [if_neg valid,hr,Bool.or_self]
    have hlenD : (D.wires xs).length=n+D.size := by
      obtain ⟨m,p,h⟩ := runTail false GateOp.eval xs D.gates
      change (D.gates.foldl (push false GateOp.eval) xs).length=n+D.size
      rw [p,List.length_append,hlen,h]
      rfl
    have zero : D.eval xs=false := by
      unfold Circuit.eval
      exact List.getD_eq_default _ _ (by omega)
    rw [zero,Bool.false_or]

lemma stageOldGate (n : ℕ) (D E : Circuit) (j : ℕ) (hj : j<D.size) :
    gateAt (joined n D E) j = gateAt D j := by
  unfold gateAt
  change ((D.gates++E.gates.map (move n D.size))++[merger n D E]).getD j _ =
    D.gates.getD j _
  rw [List.append_assoc,List.getD_append _ _ _ _ hj]

lemma stageNewGate (n : ℕ) (D E : Circuit) (j : ℕ) (hj : j<E.size) :
    gateAt (joined n D E) (D.size+j) = move n D.size (gateAt E j) := by
  have hsz : D.size+j < (D.gates ++ E.gates.map (move n D.size)).length := by
    simp only [List.length_append,List.length_map]; change D.size+j<D.size+E.size; omega
  unfold gateAt
  change ((D.gates++E.gates.map (move n D.size))++[merger n D E]).getD (D.size+j) _ = _
  rw [List.getD_append _ _ _ _ hsz,List.getD_append_right _ _ _ _ (by change D.size ≤ D.size+j; omega)]
  change (E.gates.map (move n D.size)).getD (D.size+j-D.size) _ = _
  rw [Nat.add_sub_cancel_left,List.getD_eq_getElem _ _ (by simpa [Circuit.size] using hj),
    List.getElem_map,List.getD_eq_getElem _ _ hj]

lemma stageLastGate (n : ℕ) (D E : Circuit) :
    gateAt (joined n D E) (D.size+E.size) = merger n D E := by
  unfold gateAt
  change ((stages n D E)++[merger n D E]).getD (D.size+E.size) _ = _
  have h : (stages n D E).length=D.size+E.size := by simp [stages,Circuit.size]
  rw [List.getD_append_right _ _ _ _ (by omega),h,Nat.sub_self]
  rfl

lemma joinSupport (n : ℕ) (D E : Circuit) :
    (∀ j < D.size, ∀ a, operandSupport n (joined n D E) j a = operandSupport n D j a) ∧
    (∀ j < E.size, ∀ a, operandSupport n (joined n D E) (D.size+j) (shift n D.size a) =
        operandSupport n E j a) := by
  let xs := List.ofFn fun i : Fin n => ({i} : Finset (Fin n))
  have hx : xs.length=n := by simp [xs]
  obtain ⟨old,ren,len⟩ := stageRead ∅ unionValues xs n hx D E
  let w := (stages n D E).foldl (push ∅ unionValues) xs
  change w.length=n+D.size+E.size at len
  have read (i : ℕ) (hi : i < n+D.size+E.size) : support n (joined n D E) i = w.getD i ∅ := by
    unfold support supports
    rw [support_form]
    change ((stages n D E ++ [merger n D E]).foldl (push ∅ unionValues) xs).getD i ∅ = _
    rw [List.foldl_append]
    change (push ∅ unionValues w (merger n D E)).getD i ∅ = _
    rw [push,List.getD_append _ _ _ _ (by omega)]
  constructor
  · intro j hj a
    by_cases a0 : a<n+j
    · rw [operandSupport,operandSupport,if_pos a0,if_pos a0,read a (by omega)]
      unfold support supports
      rw [support_form]
      exact old a (by omega)
    · simp [operandSupport,a0]
  · intro j hj a
    have bound : shift n D.size a < n+(D.size+j) ↔ a<n+j := by dsimp [shift]; split <;> omega
    by_cases a0 : a<n+j
    · have sa := bound.mpr a0
      rw [operandSupport,operandSupport,if_pos a0,if_pos sa,read _ (by omega)]
      unfold support supports
      rw [support_form]
      exact ren a
    · have sa := mt bound.mp a0
      simp [operandSupport,sa,a0]

lemma joinCount (n : ℕ) (M : Finset (Fin n)) (D E : Circuit)
    (clean : crossCount n M E = 0) : crossCount n M (joined n D E) ≤ crossCount n M D := by
  classical
  obtain ⟨o,s⟩ := joinSupport n D E
  have ce (j : ℕ) (hj : j<E.size) : ¬ IsCrossAnd n M E j := by
    intro cross
    let T := (Finset.range E.gates.length).filter (IsCrossAnd n M E)
    have hjt : j∈T := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj,cross⟩
    have hpos := Finset.card_pos.mpr (show T.Nonempty from ⟨j,hjt⟩)
    change T.card = 0 at clean
    omega
  apply Finset.card_le_card
  intro j hj
  obtain ⟨jl,cross⟩ := Finset.mem_filter.mp hj
  have jl := Finset.mem_range.mp jl
  change j < (joined n D E).size at jl
  rw [joinSize] at jl
  by_cases old : j<D.size
  · refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr old,?_⟩
    simpa only [IsCrossAnd,stageOldGate n D E j old,o j old] using cross
  · by_cases endAt : j=D.size+E.size
    · subst j
      have op := cross.1
      rw [stageLastGate] at op
      contradiction
    · let k := j-D.size
      have eqj : j=D.size+k := by dsimp [k]; omega
      have hk : k<E.size := by omega
      exfalso
      apply ce k hk
      rw [eqj] at cross
      unfold IsCrossAnd at cross ⊢
      rw [stageNewGate n D E k hk] at cross
      have le : (gateAt E k).inputs.length=2 := by simpa [move] using cross.2.1
      obtain ⟨a,b,ins⟩ := List.length_eq_two.mp le
      simpa only [move,ins,List.map_cons,List.map_nil,List.length_cons,List.length_nil,
        List.getD_cons_zero,List.getD_cons_succ,s k hk] using cross

end PEqualNP.Outside.Frame4594

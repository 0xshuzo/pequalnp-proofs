import Mathlib
import PEqualNP.Defs

-- From the published L_meta_5355.
namespace PEqualNP.Outside.L_meta_18065.Census.Core.Stars

open PEqualNP.CircuitLowerBounds

-- A vertex cover circuit: for each cover vertex c (in increasing order) an OR chain of the
-- neighbours of c not already handled, ANDed with c; the AND gates are ORed together.

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

def V {n : ℕ} (fs : List ((Fin n → Bool) → Bool)) (x : Fin n → Bool) : List Bool :=
  List.ofFn x ++ fs.map (fun f => f x)

def Sem {n : ℕ} (gs : List Gate) (fs : List ((Fin n → Bool) → Bool)) : Prop :=
  ∀ x : Fin n → Bool, wf gs (List.ofFn x) = V fs x

def Val {n : ℕ} (fs : List ((Fin n → Bool) → Bool)) (i : ℕ) (F : (Fin n → Bool) → Bool) : Prop :=
  i < n + fs.length ∧ ∀ x, (V fs x).getD i false = F x

def Mono (gs : List Gate) : Prop :=
  ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2

def St {n : ℕ} (G : SimpleGraph (Fin n)) (P : Fin n → Prop) (gs : List Gate)
    (fs : List ((Fin n → Bool) → Bool)) : Prop :=
  Sem gs fs ∧ fs.length = gs.length ∧ Mono gs ∧
  (∀ j < gs.length, (gs.getD j ⟨GateOp.or, []⟩).op = GateOp.and →
    ∃ l, P l ∧ ∀ x, fs.getD j (fun _ => false) x = true → x l = true) ∧
  (∀ j < gs.length, (gs.getD j ⟨GateOp.or, []⟩).op = GateOp.and →
    ∃ c v : Fin n, G.Adj c v ∧
      fs.getD j (fun _ => false) (PEqualNP.EdgeOwnership.pairInput c v) = true ∧
      ∀ i < j, (gs.getD i ⟨GateOp.or, []⟩).op = GateOp.and →
        fs.getD i (fun _ => false) (PEqualNP.EdgeOwnership.pairInput c v) = false)

def N {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Finset (Fin n)) (c : Fin n) :
    Finset (Fin n) :=
  Finset.univ.filter (fun w => G.Adj c w ∧ ¬ (w ∈ C ∧ w < c))

def gad {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Finset (Fin n)) (c : Fin n)
    (x : Fin n → Bool) : Bool :=
  x c && decide (∃ w ∈ N G C c, x w = true)

end PEqualNP.Outside.L_meta_18065.Census.Core.Stars

-- From the published L_meta_1527.
namespace PEqualNP.Outside.L_meta_18065.Census.Core.Normalize

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def W {n : ℕ} (gs : List Gate) (x : Fin n → Bool) : List Bool :=
  gs.foldl step (List.ofFn x)

def Rep {n : ℕ} (new : List Gate) (f : (Fin n → Bool) → Bool) : Prop :=
  (∃ c : Bool, ∀ x : Fin n → Bool, f x = c) ∨
    (∃ j : ℕ, j < n + new.length ∧ ∀ x : Fin n → Bool, (W new x).getD j false = f x)

def Fan (g : Gate) : Prop :=
  (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2

def Ext (n : ℕ) (new new' : List Gate) : Prop :=
  new' = new ∨ ∃ h : Gate, new' = new ++ [h] ∧ Fan h ∧ ∀ i ∈ h.inputs, i < n + new.length

def RB (n : ℕ) (new : List Gate) : Prop :=
  ∀ j < new.length, ∀ i ∈ (new.getD j ⟨GateOp.or, []⟩).inputs, i < n + j

def Inv {n : ℕ} (ρ : (Fin n → Bool) → Fin n → Bool) (old : List Gate) : Prop :=
  ∃ new : List Gate, (∀ g ∈ new, Fan g) ∧ RB n new ∧ new.length ≤ old.length ∧
    ∀ t : ℕ, Rep new (fun x => (W old (ρ x)).getD t false)

end PEqualNP.Outside.L_meta_18065.Census.Core.Normalize

namespace PEqualNP.Outside.L_meta_18065.Census.Core.Budget

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm
open PEqualNP.MetaComplexity.CoverPromise

variable {n : Nat}

def Conclusion (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (z : Fin n) : Prop :=
  ∃ D : Circuit, IsAO2 n D ∧
    circuitFun n D = (fun y : Fin n → Bool => @decide (∃ a b : Fin n,
      (G.deleteEdges (G.incidenceSet z)).Adj a b ∧ y a=true ∧ y b=true)
      (Classical.propDecidable _)) ∧
    D.size + G.degree z ≤ C.size ∧ ((∃ p q : Fin n, (G.deleteEdges (G.incidenceSet z)).Adj p q) →
      (∃ S : Finset (Fin n), IsVertexCover (G.deleteEdges (G.incidenceSet z)) S ∧
        ∀ T : Finset (Fin n), IsVertexCover G T → S.card < T.card) →
      D.size + G.degree z + 1 ≤ C.size)

end PEqualNP.Outside.L_meta_18065.Census.Core.Budget

-- Finite core classification from the published L_meta_17265.
namespace PEqualNP.Outside.L_meta_18065.Census.Core.Ten

namespace ThetaAnd3241

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity PEqualNP.ReadK

def thetaAdj (i j : Fin 4) : Bool := (13726 : Nat).testBit (4*i.val+j.val)

def theta (x : Fin 8 → Bool) : Bool :=
  decide (∃ i j : Fin 4, thetaAdj i j = true ∧
    x (Fin.castAdd 4 i) = true ∧ x (Fin.natAdd 4 j) = true)

def nine : Fin 9 → Finset (Fin 8) :=
  ![{0,1,2,3}, {0,4}, {1,2,5}, {1,3,6}, {1,5,6}, {2,3,7}, {2,5,7}, {3,6,7}, {4,5,6,7}]

def andGate (g : Gate) : Bool :=
  match g.op with
  | .and => true
  | _ => false

theorem subtract_or_eq_and {n : Nat} (C : Circuit) (ao : IsAO2 n C) :
    C.size - C.gates.countP (fun g => PEqualNP.SharedBlockCost.isOrOp g.op) =
      C.gates.countP andGate := by
  have total (gs : List Gate) (ok : ∀ g ∈ gs, g.op = .and ∨ g.op = .or) :
      gs.countP andGate + gs.countP (fun g => PEqualNP.SharedBlockCost.isOrOp g.op) = gs.length := by
    induction gs with
    | nil => rfl
    | cons g gs ih =>
      have tail := ih (fun a ha => ok a (List.mem_cons_of_mem _ ha))
      rcases ok g List.mem_cons_self with h | h
      · have a : andGate g = true := by simp [andGate,h]
        have o : PEqualNP.SharedBlockCost.isOrOp g.op = false := by rw [h]; rfl
        simp [a,o]
        omega
      · have a : andGate g = false := by simp [andGate,h]
        have o : PEqualNP.SharedBlockCost.isOrOp g.op = true := by rw [h]; rfl
        simp [a,o]
        omega
  have count := total C.gates ao.1
  unfold Circuit.size
  omega

end ThetaAnd3241

namespace ThetaPin3241

abbrev Signal (α : Type) := α → Bool
abbrev Gate (α : Type) := Signal α × Signal α

def join {α : Type} (a b : Signal α) : Signal α := fun x => a x || b x
def meet {α : Type} (a b : Signal α) : Signal α := fun x => a x && b x

def Free {α : Type} (B : Set (Signal α)) (a : Signal α) : Prop :=
  ∀ S : Set (Signal α), B ⊆ S → (fun _ => false) ∈ S → (fun _ => true) ∈ S →
    (∀ u ∈ S, ∀ v ∈ S, meet u v ∈ S) → a ∈ S

theorem atom {α : Type} {B : Set (Signal α)} {a : Signal α} (ha : a ∈ B) : Free B a :=
  fun _ h _ _ _ => h ha

theorem free_zero {α : Type} {B : Set (Signal α)} : Free B (fun _ => false) :=
  fun _ _ h _ _ => h

theorem free_one {α : Type} {B : Set (Signal α)} : Free B (fun _ => true) :=
  fun _ _ _ h _ => h

theorem free_meet {α : Type} {B : Set (Signal α)} {u v : Signal α} (hu : Free B u)
    (hv : Free B v) : Free B (meet u v) :=
  fun S incl h0 h1 hc => hc _ (hu S incl h0 h1 hc) _ (hv S incl h0 h1 hc)

theorem widen {α : Type} {B D : Set (Signal α)} {a : Signal α}
    (incl : B ⊆ D) (h : Free B a) : Free D a :=
  fun S incl' => h S (incl.trans incl')

theorem transport {α β : Type} (p : β → α) {B : Set (Signal α)} {D : Set (Signal β)}
    (base : ∀ a ∈ B, Free D (a ∘ p)) {a : Signal α} (ha : Free B a) : Free D (a ∘ p) := by
  apply ha {a | Free D (a ∘ p)}
  · exact base
  · exact free_zero
  · exact free_one
  · intro u hu v hv
    exact free_meet hu hv

theorem factors {α : Type} {B : Set (Signal α)} {f : Signal α} (ok : Free B f) :
    f = (fun _ => false) ∨ ∃ xs : List (Signal α), (∀ a ∈ xs, a ∈ B) ∧
      f = (fun x => xs.all (fun a => a x)) := by
  let S : Set (Signal α) := {f | f = (fun _ => false) ∨
    ∃ xs : List (Signal α), (∀ a ∈ xs, a ∈ B) ∧ f = (fun x => xs.all (fun a => a x))}
  apply ok S
  · intro a ha
    exact Or.inr ⟨[a],by simpa using ha,funext (fun x => by simp)⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨[],by simp,rfl⟩
  · intro a ha b hb
    rcases ha with rfl | ⟨xs,hh,rfl⟩
    · exact Or.inl rfl
    rcases hb with rfl | ⟨ys,ii,rfl⟩
    · exact Or.inl (funext (fun x => by simp [meet]))
    · refine Or.inr ⟨xs++ys,?_,?_⟩
      · intro u hu
        exact (List.mem_append.mp hu).elim (hh u) (ii u)
      · exact funext (fun x => by simp [meet])

def Valid {α : Type} (B : Set (Signal α)) (gs : List (Gate α)) (f : Signal α) : Prop :=
  match gs with
  | [] => Free B f
  | g :: rest => Free B g.1 ∧ Free B g.2 ∧ Valid (insert (join g.1 g.2) B) rest f

def Pass {α : Type} (t e z : α) (f : Signal α) : Prop :=
  f t = true → f e = true → f z = true

theorem free_pass {α : Type} {B : Set (Signal α)} {t e z : α} {f : Signal α}
    (base : ∀ a ∈ B, Pass t e z a) (ok : Free B f) : Pass t e z f := by
  apply ok {a | Pass t e z a}
  · exact base
  · intro h; contradiction
  · intro _ _; rfl
  · intro u hu v hv ht he
    have ⟨tu,tv⟩ : u t = true ∧ v t = true := by simpa [meet] using ht
    have ⟨eu,ev⟩ : u e = true ∧ v e = true := by simpa [meet] using he
    simp [meet,hu tu eu,hv tv ev]

theorem critical_gate {α : Type} (gs : List (Gate α)) (B : Set (Signal α)) (f : Signal α)
    (t e z : α) (base : ∀ a ∈ B, Pass t e z a) (ok : Valid B gs f)
    (ft : f t = true) (fe : f e = true) (fz : f z = false) :
    ∃ g ∈ gs, (g.1 t = false ∨ g.2 t = false) ∧
      join g.1 g.2 t = true ∧ join g.1 g.2 e = true ∧ join g.1 g.2 z = false := by
  classical
  induction gs generalizing B with
  | nil =>
    have impossible := free_pass base ok ft fe
    simp [fz] at impossible
  | cons g gs ih =>
    obtain ⟨ha,hb,tail⟩ := ok
    by_cases passes : Pass t e z (join g.1 g.2)
    · have next : ∀ a ∈ insert (join g.1 g.2) B, Pass t e z a := by
        intro a h
        rcases Set.mem_insert_iff.mp h with rfl | h
        · exact passes
        · exact base _ h
      obtain ⟨m,hm,p⟩ := ih _ next tail
      exact ⟨m,List.mem_cons_of_mem _ hm,p⟩
    · have hp : join g.1 g.2 t = true ∧ join g.1 g.2 e = true ∧
          join g.1 g.2 z = false := by simpa [Pass] using passes
      refine ⟨g,List.mem_cons_self,?_,hp⟩
      by_contra no
      have both : g.1 t = true ∧ g.2 t = true := by simpa using no
      have either : g.1 e = true ∨ g.2 e = true := by simpa [join] using hp.2.1
      rcases either with h | h
      · have yes := free_pass base ha both.1 h
        have nz := hp.2.2
        simp [join,yes] at nz
      · have yes := free_pass base hb both.2 h
        have nz := hp.2.2
        simp [join,yes] at nz

def Killed {α β : Type} (p : β → α) (g : Gate α) : Prop :=
  (∀ x, g.1 (p x) = false) ∨ (∀ x, g.2 (p x) = false)

def deadAt {α : Type} (t : α) (g : Gate α) : Bool := !(g.1 t && g.2 t)

theorem count_one_unique {α : Type} (gs : List α) (p : α → Bool) (a b : α)
    (ha : a ∈ gs) (hb : b ∈ gs) (pa : p a = true) (pb : p b = true)
    (one : gs.countP p ≤ 1) : a = b := by
  rw [List.countP_eq_length_filter] at one
  have a' := List.mem_filter.mpr ⟨ha,pa⟩
  have b' := List.mem_filter.mpr ⟨hb,pb⟩
  cases h : gs.filter p with
  | nil => simp [h] at a'
  | cons c rest =>
    have numeric : rest.length+1 ≤ 1 := by simpa only [h,List.length_cons] using one
    have nil : rest = [] := List.length_eq_zero_iff.mp (by omega)
    simp [h,nil] at a' b'
    exact a'.trans b'.symm

theorem single_charge_passes {α : Type} {B : Set (Signal α)} {gs : List (Gate α)}
    {f : Signal α} (ok : Valid B gs f) (g : Gate α) (hg : g ∈ gs) (t e z : α)
    (base : ∀ a ∈ B, Pass t e z a) (ft : f t = true) (fe : f e = true)
    (fz : f z = false) (dg : deadAt t g = true) (one : gs.countP (deadAt t) ≤ 1) :
    join g.1 g.2 t = true ∧ join g.1 g.2 e = true ∧ join g.1 g.2 z = false := by
  obtain ⟨j,hj,charge,h⟩ := critical_gate gs B f t e z base ok ft fe fz
  have dj : deadAt t j = true := by simpa [deadAt] using charge
  exact (count_one_unique gs (deadAt t) j g hj hg dj dg one) ▸ h

theorem propagate_property {α : Type} (B S : Set (Signal α)) (gs : List (Gate α)) (f : Signal α)
    (incl : B ⊆ S) (ok : Valid B gs f)
    (stable : ∀ g ∈ gs, Free S g.1 → Free S g.2 → join g.1 g.2 ∈ S) :
    Free S f := by
  induction gs generalizing B with
  | nil => exact widen incl ok
  | cons g gs ih =>
    obtain ⟨ha,hb,tail⟩ := ok
    have mem := stable g List.mem_cons_self (widen incl ha) (widen incl hb)
    exact ih (insert (join g.1 g.2) B) (Set.insert_subset mem incl) tail
      (fun a h => stable a (List.mem_cons_of_mem _ h))

noncomputable def killedBit {α β : Type} (p : β → α) (g : Gate α) : Bool :=
  @decide (Killed p g) (Classical.propDecidable _)

theorem restrict_transfer {α β : Type} (p : β → α) (gs : List (Gate α))
    (B : Set (Signal α)) (D : Set (Signal β)) (f : Signal α)
    (base : ∀ a ∈ B, Free D (a ∘ p)) (ok : Valid B gs f) :
    ∃ out : List (Gate β), Valid D out (f ∘ p) ∧
      out.length + gs.countP (killedBit p) = gs.length := by
  classical
  induction gs generalizing B D with
  | nil => exact ⟨[], transport p base ok, rfl⟩
  | cons g gs ih =>
    obtain ⟨ha,hb,tail⟩ := ok
    have left := transport p base ha
    have right := transport p base hb
    by_cases dead : Killed p g
    · have combined : Free D (join g.1 g.2 ∘ p) := by
        rcases dead with l | r
        · have e : join g.1 g.2 ∘ p = g.2 ∘ p := funext (fun x => by simp [join,l])
          exact e ▸ right
        · have e : join g.1 g.2 ∘ p = g.1 ∘ p := funext (fun x => by simp [join,r])
          exact e ▸ left
      have next : ∀ a ∈ insert (join g.1 g.2) B, Free D (a ∘ p) := by
        intro a h
        rcases Set.mem_insert_iff.mp h with rfl | h
        · exact combined
        · exact base _ h
      obtain ⟨out,sem,cost⟩ := ih _ D next tail
      refine ⟨out,sem,?_⟩
      have k : killedBit p g = true := by simp [killedBit,dead]
      simp [k]
      omega
    · let new := join (g.1 ∘ p) (g.2 ∘ p)
      have next : ∀ a ∈ insert (join g.1 g.2) B, Free (insert new D) (a ∘ p) := by
        intro a h
        rcases Set.mem_insert_iff.mp h with rfl | h
        · exact atom (Set.mem_insert _ _)
        · exact widen (Set.subset_insert _ _) (base _ h)
      obtain ⟨out,sem,cost⟩ := ih _ (insert new D) next tail
      refine ⟨(g.1 ∘ p,g.2 ∘ p)::out,⟨left,right,sem⟩,?_⟩
      have k : killedBit p g = false := by simp [killedBit,dead]
      simp [k]
      omega

abbrev PhysicalGate := PEqualNP.CircuitLowerBounds.Gate
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm

def wire {α : Type} (w : List (Signal α)) (i : Nat) : Signal α := w.getD i (fun _ => false)

def step {α : Type} (w : List (Signal α)) (g : PhysicalGate) : List (Signal α) :=
  w ++ [fun x => g.op.eval (g.inputs.map fun i => wire w i x)]

def pairShape (g : PhysicalGate) : Prop :=
  (g.op = .and ∨ g.op = .or) ∧ ∃ a b : Nat, g.inputs = [a,b]

theorem free_wire {α : Type} {B : Set (Signal α)} {w : List (Signal α)}
    (hw : ∀ a ∈ w, Free B a) (i : Nat) : Free B (wire w i) := by
  induction w generalizing i with
  | nil => cases i <;> exact free_zero
  | cons a w ih =>
    cases i with
    | zero => exact hw _ List.mem_cons_self
    | succ i => exact ih (fun a ha => hw a (List.mem_cons_of_mem _ ha)) i

def isOr (g : PhysicalGate) : Bool := PEqualNP.SharedBlockCost.isOrOp g.op

theorem compress {α : Type} (gs : List PhysicalGate) (output : Nat) (w : List (Signal α))
    (B : Set (Signal α)) (hw : ∀ a ∈ w, Free B a) (shapes : ∀ g ∈ gs, pairShape g) :
    ∃ ops : List (Gate α), Valid B ops (wire (gs.foldl step w) output) ∧
      ops.length = gs.countP isOr := by
  induction gs generalizing w B with
  | nil => exact ⟨[],free_wire hw output,rfl⟩
  | cons g gs ih =>
    obtain ⟨hop,i,j,pins⟩ := shapes g List.mem_cons_self
    have tail (h : PhysicalGate) (hh : h ∈ gs) := shapes h (List.mem_cons_of_mem _ hh)
    rcases hop with kind | kind
    · have eq : step w g = w ++ [meet (wire w i) (wire w j)] := by
        simp [step,pins,kind,GateOp.eval]
        rfl
      have ext : ∀ a ∈ step w g, Free B a := by
        intro a ha
        rw [eq,List.mem_append,List.mem_singleton] at ha
        rcases ha with old | rfl
        · exact hw a old
        · exact free_meet (free_wire hw i) (free_wire hw j)
      obtain ⟨ops,sem,cost⟩ := ih (step w g) B ext tail
      refine ⟨ops,sem,?_⟩
      have no : isOr g = false := by simp [isOr,kind,PEqualNP.SharedBlockCost.isOrOp]
      simpa [no] using cost
    · let a := wire w i
      let b := wire w j
      let D := insert (join a b) B
      have eq : step w g = w ++ [join a b] := by
        simp [step,pins,kind,GateOp.eval,a,b]
        rfl
      have ext : ∀ v ∈ step w g, Free D v := by
        intro v hv
        rw [eq,List.mem_append,List.mem_singleton] at hv
        rcases hv with old | rfl
        · exact widen (Set.subset_insert _ _) (hw v old)
        · exact atom (Set.mem_insert _ _)
      obtain ⟨ops,sem,cost⟩ := ih (step w g) D ext tail
      refine ⟨(a,b)::ops,⟨free_wire hw i,free_wire hw j,sem⟩,?_⟩
      have yes : isOr g = true := by simp [isOr,kind,PEqualNP.SharedBlockCost.isOrOp]
      simp [cost,yes]

theorem wire_point {α : Type} (w : List (Signal α)) (x : α) (i : Nat) :
    (w.map (fun f => f x)).getD i false = wire w i x := by
  induction w generalizing i with
  | nil => cases i <;> rfl
  | cons f fs ih => cases i with
    | zero => rfl
    | succ i => exact ih i

theorem run_point {α : Type} (gs : List PhysicalGate) (w : List (Signal α)) (x : α) :
    (gs.foldl step w).map (fun f => f x) =
      gs.foldl (fun a g => a ++ [g.op.eval (g.inputs.map fun i => a.getD i false)])
        (w.map (fun f => f x)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons,List.foldl_cons,ih]
    simp only [step,List.map_append,List.map_cons,List.map_nil,wire_point]

def inputs (n : Nat) : Set (Signal (Fin n → Bool)) := Set.range (fun (i : Fin n) x => x i)

def topMiss {n : Nat} (v : Fin n) (i : Fin n) : Bool := decide (i ≠ v)

theorem pass_inputs {n : Nat} (t e z : Fin n → Bool)
    (h : ∀ i, t i = true → e i = true → z i = true) : ∀ a ∈ inputs n, Pass t e z a := by
  rintro a ⟨i,rfl⟩
  exact h i

theorem one_charge {n : Nat} {gs f} (ok : Valid (inputs n) gs f)
    (v : Fin n) (e z : Fin n → Bool)
    (h : ∀ i, topMiss v i = true → e i = true → z i = true)
    (ft : f (topMiss v) = true) (fe : f e = true) (fz : f z = false) :
    1 ≤ gs.countP (deadAt (topMiss v)) := by
  obtain ⟨j,hj,hk,_⟩ := critical_gate gs (inputs n) f (topMiss v) e z
    (pass_inputs _ _ _ h) ok ft fe fz
  exact List.countP_pos_iff.mpr ⟨j,hj,by simpa [deadAt] using hk⟩

def Admissible {α : Type} (B : Set (Signal α)) (f : Signal α) (t : α) (g : Gate α) : Prop :=
  ∀ e z, (∀ a ∈ B, Pass t e z a) → f t = true → f e = true → f z = false →
    join g.1 g.2 t = true ∧ join g.1 g.2 e = true ∧ join g.1 g.2 z = false

theorem double_from_classifier {n : Nat} (low : Set (Fin n)) (f : Signal (Fin n → Bool))
    (S : Set (Signal (Fin n → Bool))) (inc : inputs n ⊆ S) (nonfree : ¬ Free S f)
    (classify : ∀ g : Gate (Fin n → Bool), Free S g.1 → Free S g.2 →
      (∀ v ∈ low, deadAt (topMiss v) g = true → Admissible (inputs n) f (topMiss v) g) →
      join g.1 g.2 ∈ S)
    (gs : List (Gate (Fin n → Bool))) (ok : Valid (inputs n) gs f) :
    ∃ v ∈ low, 2 ≤ gs.countP (deadAt (topMiss v)) := by
  classical
  by_contra no
  apply nonfree
  apply propagate_property (inputs n) S gs f inc ok
  intro g hg ha hb
  apply classify g ha hb
  intro v hv dg e z raw ft fe fz
  have small : gs.countP (deadAt (topMiss v)) ≤ 1 := by
    by_contra h
    exact no ⟨v,hv,by omega⟩
  exact single_charge_passes ok g hg (topMiss v) e z raw ft fe fz dg small

def Increasing {n : Nat} (f : Signal (Fin n → Bool)) : Prop :=
  ∀ x y, (∀ i, x i = true → y i = true) → f x = true → f y = true

theorem free_increasing {n : Nat} {B : Set (Signal (Fin n → Bool))}
    (base : ∀ a ∈ B, Increasing a) {a} (ha : Free B a) : Increasing a := by
  apply ha {v | Increasing v}
  · exact base
  · intro _ _ _ h; contradiction
  · intro _ _ _ _; rfl
  · intro u hu v hv x y le hx
    obtain ⟨lu,lv⟩ : u x = true ∧ v x = true := by simpa [meet] using hx
    simp [meet,hu x y le lu,hv x y le lv]

theorem active_monotone {n : Nat} {B : Set (Signal (Fin n → Bool))}
    (base : ∀ a ∈ B, Increasing a) {gs f} (ok : Valid B gs f) :
    ∀ g ∈ gs, Increasing g.1 ∧ Increasing g.2 := by
  induction gs generalizing B with
  | nil => simp
  | cons h gs ih =>
    obtain ⟨left,right,tail⟩ := ok
    have l := free_increasing base left
    have r := free_increasing base right
    have next : ∀ a ∈ insert (join h.1 h.2) B, Increasing a := by
      intro a ha
      rcases Set.mem_insert_iff.mp ha with rfl | old
      · intro x y le hx
        have one : h.1 x = true ∨ h.2 x = true := by simpa [join] using hx
        rcases one with p | p
        · simp [join,l x y le p]
        · simp [join,r x y le p]
      · exact base _ old
    intro g hg
    rcases List.mem_cons.mp hg with rfl | later
    · exact ⟨l,r⟩
    · exact ih next tail _ later

def pin {n : Nat} (v : Fin (n+1)) (x : Fin n → Bool) : Fin (n+1) → Bool :=
  v.insertNth false x

theorem pin_raw {n : Nat} (v : Fin (n+1)) :
    ∀ a ∈ inputs (n+1), Free (inputs n) (a ∘ pin v) := by
  rintro a ⟨i,rfl⟩
  refine v.succAboveCases ?_ (fun j => ?_) i
  · have eq : (fun t : Fin (n+1) → Bool => t v) ∘ pin v = (fun _ => false) :=
      funext (fun x => by simp [pin])
    exact eq ▸ free_zero
  · have eq : (fun t : Fin (n+1) → Bool => t (v.succAbove j)) ∘ pin v = (fun x => x j) :=
      funext (fun x => by simp [pin])
    exact eq ▸ atom ⟨j,rfl⟩

theorem delete_charge {n : Nat} {gs f} (ok : Valid (inputs (n+1)) gs f) (v : Fin (n+1)) :
    ∃ out, Valid (inputs n) out (f ∘ pin v) ∧
      out.length + gs.countP (deadAt (topMiss v)) ≤ gs.length := by
  obtain ⟨out,sem,cost⟩ := restrict_transfer (pin v) gs _ _ f (pin_raw v) ok
  refine ⟨out,sem,?_⟩
  have base : ∀ a ∈ inputs (n+1), Increasing a := by
    rintro a ⟨i,rfl⟩ x y le hx
    exact le i hx
  have zero {a : Signal (Fin (n+1) → Bool)} (inc : Increasing a) (ha : a (topMiss v) = false) :
      ∀ x, a (pin v x) = false := by
    intro x
    cases h : a (pin v x) with
    | false => rfl
    | true =>
      have le : ∀ i, pin v x i = true → topMiss v i = true := by
        intro i
        by_cases hi : i = v
        · subst i; simp [pin]
        · simp [topMiss,hi]
      simp [inc _ _ le h] at ha
  have keep (g) (hg : g ∈ gs) (h : deadAt (topMiss v) g = true) : killedBit (pin v) g = true := by
    obtain ⟨l,r⟩ := active_monotone base ok _ hg
    have either : g.1 (topMiss v) = false ∨ g.2 (topMiss v) = false := by simpa [deadAt] using h
    have killed : Killed (pin v) g := either.imp (zero l) (zero r)
    simp [killedBit,killed]
  have count : gs.countP (deadAt (topMiss v)) ≤ gs.countP (killedBit (pin v)) :=
    List.countP_mono_left keep
  omega

theorem of_circuit {n : Nat} (C : Circuit) (ao : IsAO2 n C) :
    ∃ ops : List (Gate (Fin n → Bool)), Valid (inputs n) ops (circuitFun n C) ∧
      ops.length = C.gates.countP isOr := by
  let w : List (Signal (Fin n → Bool)) := (List.finRange n).map (fun i x => x i)
  have ok (a) (ha : a ∈ w) : Free (inputs n) a := by
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp ha
    exact atom ⟨i,rfl⟩
  have shapes (g : PhysicalGate) (hg : g ∈ C.gates) : pairShape g := by
    refine ⟨ao.1 _ hg,?_⟩
    have len := ao.2.2 _ hg
    match h : g.inputs with
    | [] => simp [h] at len
    | [_] => simp [h] at len
    | a::b::rest =>
      have nil : rest = [] := List.length_eq_zero_iff.mp (by simpa [h] using len)
      exact ⟨a,b,by rw [nil]⟩
  obtain ⟨ops,sem,cost⟩ := compress C.gates C.output w (inputs n) ok shapes
  refine ⟨ops,?_,cost⟩
  have eq : wire (C.gates.foldl step w) C.output = circuitFun n C := by
    funext x
    rw [← wire_point,run_point]
    have start : w.map (fun f => f x) = List.ofFn x := by simp [w,List.ofFn_eq_map]
    rw [start]
    rfl
  exact eq ▸ sem

def Lower {n : Nat} (f : Signal (Fin n → Bool)) (k : Nat) : Prop :=
  ∀ ops, Valid (inputs n) ops f → k ≤ ops.length

theorem lower_zero {n : Nat} (f : Signal (Fin n → Bool)) : Lower f 0 :=
  fun _ _ => Nat.zero_le _

theorem lower_one_step {n k : Nat} (f : Signal (Fin (n+1) → Bool))
    (v : Fin (n+1)) (e z : Fin (n+1) → Bool)
    (h : ∀ i, topMiss v i = true → e i = true → z i = true)
    (ft : f (topMiss v) = true) (fe : f e = true) (fz : f z = false)
    (rec : Lower (f ∘ pin v) k) : Lower f (k+1) := by
  intro gs ok
  have saved := one_charge ok v e z h ft fe fz
  obtain ⟨out,sem,budget⟩ := delete_charge ok v
  have sub := rec out sem
  omega

theorem lower_two_step {n k : Nat} (f : Signal (Fin (n+1) → Bool)) (low : Set (Fin (n+1)))
    (S : Set (Signal (Fin (n+1) → Bool))) (inc : inputs (n+1) ⊆ S)
    (nonfree : ¬ Free S f)
    (classify : ∀ g : Gate (Fin (n+1) → Bool), Free S g.1 → Free S g.2 →
      (∀ v ∈ low, deadAt (topMiss v) g = true → Admissible (inputs (n+1)) f (topMiss v) g) →
      join g.1 g.2 ∈ S) (rec : ∀ v ∈ low, Lower (f ∘ pin v) k) : Lower f (k+2) := by
  intro gs ok
  obtain ⟨v,mem,saved⟩ := double_from_classifier low f S inc nonfree classify gs ok
  obtain ⟨out,sem,budget⟩ := delete_charge ok v
  have sub := rec v mem out sem
  omega

theorem lower_circuit {n k : Nat} {f : Signal (Fin n → Bool)} (lb : Lower f k)
    (C : Circuit) (ao : IsAO2 n C) (correct : circuitFun n C = f) :
    k ≤ C.gates.countP isOr := by
  obtain ⟨ops,sem,cost⟩ := of_circuit C ao
  exact cost ▸ lb ops (correct ▸ sem)

theorem lower_transport {m n k : Nat} {f : Signal (Fin n → Bool)}
    (p : (Fin m → Bool) → (Fin n → Bool))
    (raw : ∀ a ∈ inputs n, Free (inputs m) (a ∘ p))
    (sub : Lower (f ∘ p) k) : Lower f k := by
  intro gs ok
  obtain ⟨out,sem,budget⟩ := restrict_transfer p gs (inputs n) (inputs m) f raw ok
  have bound := sub out sem
  omega

theorem lower_rename {m n k : Nat} {f : Signal (Fin n → Bool)} (r : Fin n → Fin m)
    (sub : Lower (fun x => f (x ∘ r)) k) : Lower f k := by
  apply lower_transport (fun x => x ∘ r) _ sub
  rintro a ⟨i,rfl⟩
  exact atom ⟨r i,rfl⟩

end ThetaPin3241

namespace ThetaCores3241
open ThetaPin3241

def row {n : Nat} (mask : Nat) (i : Fin n) : Bool := mask.testBit i.val
def path2 (x : Fin 2 → Bool) : Bool := (x 0 && x 1)
def path3 (x : Fin 3 → Bool) : Bool := (x 0 && x 1) || (x 1 && x 2)
def path4 (x : Fin 4 → Bool) : Bool := (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3)
def path5 (x : Fin 5 → Bool) : Bool := (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4)
def cycle6 (x : Fin 6 → Bool) : Bool := (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 0)
def pendant7 (x : Fin 7 → Bool) : Bool := (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 0) || (x 0 && x 6)

def low : Set (Fin 8) := {v | v ≠ 0 ∧ v ≠ 4}

theorem path2_lower : Lower path2 0 := lower_zero path2

theorem path3_from_core (rec : Lower path2 0) : Lower path3 1 := by
  have eq : path3 ∘ pin (2 : Fin 3) = path2 := by
    funext x
    exact (by decide +kernel : ∀ y, path3 (pin (2 : Fin 3) y) = path2 y) x
  apply lower_one_step path3 2 (row 6) (row 2)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact eq.symm ▸ rec

theorem path4_from_core (rec : Lower path3 1) : Lower path4 2 := by
  have eq : path4 ∘ pin (3 : Fin 4) = path3 := by
    funext x
    exact (by decide +kernel : ∀ y, path4 (pin (3 : Fin 4) y) = path3 y) x
  apply lower_one_step path4 3 (row 12) (row 4)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact eq.symm ▸ rec

theorem path5_from_core (rec : Lower path4 2) : Lower path5 3 := by
  have eq : path5 ∘ pin (4 : Fin 5) = path4 := by
    funext x
    exact (by decide +kernel : ∀ y, path5 (pin (4 : Fin 5) y) = path4 y) x
  apply lower_one_step path5 4 (row 24) (row 8)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact eq.symm ▸ rec

theorem path5_lower : Lower path5 3 := path5_from_core (path4_from_core (path3_from_core path2_lower))

theorem pendant7_from_core (rec : Lower cycle6 5) : Lower pendant7 6 := by
  have eq : pendant7 ∘ pin (6 : Fin 7) = cycle6 := by
    funext x
    exact (by decide +kernel : ∀ y, pendant7 (pin (6 : Fin 7) y) = cycle6 y) x
  apply lower_one_step pendant7 6 (row 65) (row 1)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact eq.symm ▸ rec

def cycleRename : Fin 6 → Fin 5 → Fin 5 := ![![0,1,2,3,4],![0,4,3,2,1],![1,0,4,3,2],![2,1,0,4,3],![1,2,3,4,0],![0,1,2,3,4]]

theorem cycle6_deleted (v : Fin 6) : Lower (cycle6 ∘ pin v) 3 := by
  have all : ∀ i x, (cycle6 ∘ pin i) (x ∘ cycleRename i) = path5 x := by decide +kernel
  apply lower_rename (cycleRename v)
  have eq : (fun x => (cycle6 ∘ pin v) (x ∘ cycleRename v)) = path5 := funext (all v)
  exact eq.symm ▸ path5_lower

def thetaRename : Fin 8 → Fin 7 → Fin 7 := ![![0,1,2,3,4,5,6],![0,2,4,3,5,1,6],![0,2,4,3,5,6,1],![0,2,4,3,6,5,1],![0,1,2,3,4,5,6],![3,1,5,6,0,4,2],![3,1,6,5,0,4,2],![3,6,1,5,0,4,2]]

theorem theta_deleted (rec : Lower cycle6 5) (v : Fin 8) (hv : v ∈ low) :
    Lower (ThetaAnd3241.theta ∘ pin v) 6 := by
  have all : ∀ i : Fin 8, i ≠ 0 ∧ i ≠ 4 → ∀ x,
      (ThetaAnd3241.theta ∘ pin i) (x ∘ thetaRename i) = pendant7 x := by
    decide +kernel
  apply lower_rename (thetaRename v)
  have eq : (fun x => (ThetaAnd3241.theta ∘ pin v) (x ∘ thetaRename v)) = pendant7 :=
    funext (all v hv)
  exact eq.symm ▸ pendant7_from_core rec

def Classifier {n : Nat} (f : Signal (Fin n → Bool)) (L : Set (Fin n))
    (S : Set (Signal (Fin n → Bool))) : Prop :=
  inputs n ⊆ S ∧ ¬ Free S f ∧
    ∀ g : Gate (Fin n → Bool), Free S g.1 → Free S g.2 →
      (∀ v ∈ L, deadAt (topMiss v) g = true → Admissible (inputs n) f (topMiss v) g) →
      join g.1 g.2 ∈ S

theorem cycle6_of_classifier {S} (h : Classifier cycle6 Set.univ S) : Lower cycle6 5 :=
  lower_two_step cycle6 Set.univ S h.1 h.2.1 h.2.2 (fun v _ => cycle6_deleted v)

theorem theta_of_classifiers {S T} (cycle : Classifier cycle6 Set.univ S)
    (th : Classifier ThetaAnd3241.theta low T) : Lower ThetaAnd3241.theta 8 :=
  lower_two_step ThetaAnd3241.theta low T th.1 th.2.1 th.2.2
    (theta_deleted (cycle6_of_classifier cycle))

end ThetaCores3241

namespace ThetaClass3241
open ThetaPin3241

abbrev X (n : Nat) := Fin n → Bool
abbrev Sig (n : Nat) := Signal (X n)
def raw {n} (v : Fin n) : Sig n := fun x => x v
def bits {n} (s : Finset (Fin n)) : X n := fun i => decide (i ∈ s)

def High {n} (H : Finset (Fin n)) (a : Sig n) : Prop :=
  Monotone a ∧ ∀ x y : X n, (∀ i ∈ H, x i = y i) → a x = a y
def pool {n} (H : Finset (Fin n)) : Set (Sig n) :=
  {a | High H a ∨ ∃ i ∉ H, a = raw i}

theorem base_subset {n} (H : Finset (Fin n)) : inputs n ⊆ pool H := by
  rintro _ ⟨i,rfl⟩
  by_cases hi : i ∈ H
  · exact Or.inl ⟨fun _ _ h => h i, fun _ _ h => h i hi⟩
  · exact Or.inr ⟨i,hi,rfl⟩

theorem high_const {n} (H : Finset (Fin n)) (b : Bool) : High H (fun _ => b) :=
  ⟨fun _ _ _ => le_rfl, fun _ _ _ => rfl⟩

theorem high_join {n} {H : Finset (Fin n)} {a b : Sig n} (ha : High H a) (hb : High H b) :
    High H (join a b) := by
  constructor
  · intro x y xy
    exact sup_le_sup (ha.1 xy) (hb.1 xy)
  · intro x y h
    simp only [join,ha.2 x y h,hb.2 x y h]

theorem high_all {n} (H : Finset (Fin n)) (xs : List (Sig n))
    (hx : ∀ a ∈ xs, High H a) : High H (fun x => xs.all (fun a => a x)) := by
  induction xs with
  | nil => exact high_const H true
  | cons a xs ih =>
    have ha := hx a List.mem_cons_self
    have ht := ih (fun u hu => hx u (List.mem_cons_of_mem _ hu))
    constructor
    · intro x y xy
      exact inf_le_inf (ha.1 xy) (ht.1 xy)
    · intro x y eq
      simp only [List.all_cons, ha.2 x y eq, ht.2 x y eq]

theorem high_or_dead {n} {H : Finset (Fin n)} {a : Sig n} (ok : Free (pool H) a) :
    High H a ∨ ∃ v ∉ H, a (topMiss v) = false := by
  classical
  by_contra! bad
  obtain ⟨notHigh,live⟩ := bad
  rcases factors ok with rfl | ⟨xs,hxs,rfl⟩
  · exact notHigh (high_const _ _)
  apply notHigh (high_all H xs ?_)
  intro f hf
  rcases hxs f hf with h | ⟨v,hv,rfl⟩
  · exact h
  · have alive : xs.all (fun g => g (topMiss v)) = true := by simpa using live v hv
    have one := List.all_eq_true.mp alive (raw v) hf
    simp [raw,topMiss] at one

theorem arm_invariant {n} {H : Finset (Fin n)} {a : Sig n} (ok : Free (pool H) a)
    {v : Fin n} (low : v ∉ H) (alive : a (topMiss v) = true)
    (x y : X n) (same : ∀ i, i ≠ v → x i = y i) : a x = a y := by
  rcases factors ok with rfl | ⟨xs,hxs,rfl⟩
  · rfl
  have equal (f : Sig n) (hf : f ∈ xs) : f x = f y := by
    rcases hxs f hf with h | ⟨i,_,rfl⟩
    · exact h.2 x y (fun j hj => same j (fun eq => low (eq ▸ hj)))
    · have val := List.all_eq_true.mp alive (raw i) hf
      exact same i (by simpa [raw,topMiss] using val)
  apply Bool.eq_iff_iff.mpr
  simp only [List.all_eq_true]
  exact ⟨fun all f hf => equal f hf ▸ all f hf, fun all f hf => (equal f hf).symm ▸ all f hf⟩

theorem forced_raw {n} {H : Finset (Fin n)} {a : Sig n} (ok : Free (pool H) a)
    {v u w : Fin n} (low : v ∉ H) (ulow : u ∉ H) (diff : u ≠ w)
    (dead : a (topMiss v) = false)
    (e1 : a (bits {v,u}) = true) (e2 : a (bits {v,w}) = true) : a = raw v := by
  classical
  rcases factors ok with rfl | ⟨xs,hxs,rfl⟩
  · contradiction
  have classify (z : Sig n) (hz : z ∈ xs) : z = (fun _ => true) ∨ z = raw v := by
    have first := List.all_eq_true.mp e1 z hz
    have second := List.all_eq_true.mp e2 z hz
    rcases hxs z hz with high | ⟨i,_,rfl⟩
    · left
      have atZero : z (fun _ => false) = true := by
        rw [← first]
        apply high.2
        intro i hi
        have iv : i ≠ v := fun eq => low (eq ▸ hi)
        have iu : i ≠ u := fun eq => ulow (eq ▸ hi)
        simp [bits,iv,iu]
      funext x
      have le := high.1 (show (fun _ : Fin n => false) ≤ x from fun _ => bot_le)
      exact Bool.eq_true_of_true_le (atZero ▸ le)
    · right
      have h1 : i = v ∨ i = u := by simpa [raw,bits] using first
      have h2 : i = v ∨ i = w := by simpa [raw,bits] using second
      have eq : i = v := by grind
      rw [eq]
  have contains : raw v ∈ xs := by
    by_contra hn
    have t : xs.all (fun a => a (topMiss v)) = true := List.all_eq_true.mpr (by
      intro z hz
      rcases classify z hz with rfl | rfl
      · rfl
      · contradiction)
    simp [t] at dead
  funext x
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro all
    exact List.all_eq_true.mp all _ contains
  · intro hv
    apply List.all_eq_true.mpr
    intro z hz
    rcases classify z hz with rfl | rfl
    · rfl
    · exact hv

end ThetaClass3241

namespace ThetaClass3241
open ThetaPin3241

structure Geometry {n : Nat} (H : Finset (Fin n)) (f : Sig n) : Prop where
  surviving : ∀ v ∉ H, f (topMiss v) = true
  singleton_false : ∀ u, f (bits {u}) = false
  neighbors : ∀ v ∉ H, ∃ u w, u ∉ H ∧ u ≠ w ∧
    f (bits {v,u}) = true ∧ f (bits {v,w}) = true
  poles : ∀ v ∉ H, ∃ u, f (bits {v,u}) = true ∧ f (bits (insert u H)) = false
  twins : ∀ v ∉ H, ∀ w ∉ H, v ≠ w → ∃ u, f (bits {v,u}) = true ∧ f (bits {u,w}) = false

def Checks {n} (H : Finset (Fin n)) (f a b : Sig n) : Prop := ∀ v ∉ H,
  deadAt (topMiss v) (a,b) = true → Admissible (inputs n) f (topMiss v) (a,b)

theorem checks_swap {n} {H : Finset (Fin n)} {f a b : Sig n} (c : Checks H f a b) :
    Checks H f b a := by
  intro v hv hd e z pass ft fe fz
  have h := c v hv (by simpa [deadAt,Bool.and_comm] using hd) e z pass ft fe fz
  simpa only [join,Bool.or_comm] using h

theorem probe {n} {H : Finset (Fin n)} {f a b : Sig n} (geo : Geometry H f)
    {v u : Fin n} (hv : v ∉ H) (c : Checks H f a b) (dead : a (topMiss v) = false)
    (z : Finset (Fin n)) (inside : u ∈ z) (fe : f (bits {v,u}) = true) (fz : f (bits z) = false) :
    join a b (topMiss v) = true ∧ join a b (bits {v,u}) = true ∧ join a b (bits z) = false := by
  apply c v hv (by simp [deadAt,dead]) _ _ _ (geo.surviving v hv) fe fz
  apply pass_inputs
  intro i ti ei
  have ne : i ≠ v := by simpa [topMiss] using ti
  have eq : i = u := by simpa [bits,ne] using ei
  simpa [bits,eq] using inside

theorem collapse {n} {H : Finset (Fin n)} {f a b : Sig n} (geo : Geometry H f)
    (ha : Free (pool H) a) (hb : Free (pool H) b) (c : Checks H f a b)
    {v : Fin n} (hv : v ∉ H) (dead : a (topMiss v) = false) : a = raw v := by
  obtain ⟨u,w,lu,ne,eu,ew⟩ := geo.neighbors v hv
  have activate (i : Fin n) (e : f (bits {v,i}) = true) : a (bits {v,i}) = true := by
    obtain ⟨st,se,sz⟩ := probe geo hv c dead {i} (by simp) e (geo.singleton_false i)
    have live : b (topMiss v) = true := by simpa [join,dead] using st
    have same := arm_invariant hb hv live (bits {v,i}) (bits {i}) (fun j hj => by simp [bits,hj])
    have bz : b (bits {i}) = false := (Bool.or_eq_false_iff.mp sz).2
    simpa [join,same,bz] using se
  exact forced_raw ha hv lu ne dead (activate u eu) (activate w ew)

theorem reject_side {n} {H : Finset (Fin n)} {f a b : Sig n} (geo : Geometry H f)
    (ha : Free (pool H) a) (hb : Free (pool H) b) (c : Checks H f a b)
    {v : Fin n} (hv : v ∉ H) (dead : a (topMiss v) = false) : False := by
  have av := collapse geo ha hb c hv dead
  rcases high_or_dead hb with high | ⟨w,hw,dw⟩
  · obtain ⟨u,eu,zu⟩ := geo.poles v hv
    obtain ⟨st,_,sz⟩ := probe geo hv c dead (insert u H) (by simp) eu zu
    have bt : b (topMiss v) = true := by simpa [join,dead] using st
    have bz : b (bits (insert u H)) = false := (Bool.or_eq_false_iff.mp sz).2
    have eq := high.2 (topMiss v) (bits (insert u H)) (fun i hi => by
      have ne : i ≠ v := fun e => hv (e ▸ hi)
      simp [topMiss,bits,ne,hi])
    simp [bt,bz] at eq
  · have bw := collapse geo hb ha (checks_swap c) hw dw
    have ne : v ≠ w := by
      rintro rfl
      obtain ⟨u,_,_,_,eu,_⟩ := geo.neighbors v hv
      have st := (probe geo hv c dead {u} (by simp) eu (geo.singleton_false u)).1
      simp [join,dead,dw] at st
    obtain ⟨u,eu,zu⟩ := geo.twins v hv w hw ne
    have sz := (probe geo hv c dead {u,w} (by simp) eu zu).2.2
    simp [join,bw,raw,bits] at sz

theorem classify {n} {H : Finset (Fin n)} {f : Sig n} (geo : Geometry H f)
    (g : Gate (X n)) (ha : Free (pool H) g.1) (hb : Free (pool H) g.2)
    (c : ∀ v ∈ {v | v ∉ H}, deadAt (topMiss v) g = true → Admissible (inputs n) f (topMiss v) g) :
    join g.1 g.2 ∈ pool H := by
  have ck : Checks H f g.1 g.2 := c
  rcases high_or_dead ha with aa | ⟨v,hv,dead⟩
  · rcases high_or_dead hb with bb | ⟨v,hv,dead⟩
    · exact Or.inl (high_join aa bb)
    · exact (reject_side geo hb ha (checks_swap ck) hv dead).elim
  · exact (reject_side geo ha hb ck hv dead).elim

end ThetaClass3241

namespace ThetaClass3241
open ThetaPin3241 ThetaCores3241

theorem nonfree {n} (f : Sig n) (H : Finset (Fin n)) (x y z : X n)
    (hhigh : ∀ i ∈ H, x i = z i) (draw : ∀ i, x i = true → y i = true → z i = true)
    (fx : f x = true) (fy : f y = true) (fz : f z = false) : ¬ Free (pool H) f := by
  intro ok
  have base : ∀ a ∈ pool H, Pass x y z a := by
    intro a ha
    rcases ha with h | ⟨i,_,rfl⟩
    · intro ax _
      exact (h.2 x z hhigh) ▸ ax
    · exact draw i
  have pos := free_pass base ok fx fy
  simp [fz] at pos

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
theorem cycle_geo : Geometry ∅ cycle6 := by constructor <;> decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
theorem theta_geo : Geometry {0,4} ThetaAnd3241.theta := by constructor <;> decide +kernel

theorem cycle_classifier : Classifier cycle6 Set.univ (pool ∅) := by
  refine ⟨base_subset _,?_,?_⟩
  · exact nonfree cycle6 ∅ (bits {0,1}) (bits {2,3}) (bits ∅)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro g a b h
    exact classify cycle_geo g a b (fun v _ => h v (Set.mem_univ v))

theorem theta_classifier : Classifier ThetaAnd3241.theta low (pool {0,4}) := by
  refine ⟨base_subset _,?_,?_⟩
  · exact nonfree ThetaAnd3241.theta {0,4} (bits {1,7}) (bits {2,6}) (bits ∅)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro g a b h
    apply classify theta_geo g a b
    intro v hv
    apply h v
    simpa [low,Set.mem_ofPred_eq,not_or] using hv

end ThetaClass3241

namespace ThetaPrune3241
open ThetaPin3241

def Private {α : Type} (P : Set α) (g : Gate α) : Prop :=
  (∃ e ∈ P, g.1 e = true ∧ g.2 e = false) ∧
  (∃ e ∈ P, g.2 e = true ∧ g.1 e = false)

def Refines {α : Type} (P : Set α) (new old : Signal α) : Prop :=
  (∀ e ∈ P, new e = old e) ∧ (∀ x, new x = true → old x = true)

theorem self_refines {α : Type} (P : Set α) (f : Signal α) : Refines P f f :=
  ⟨fun _ _ => rfl,fun _ h => h⟩

theorem ref_meet {α : Type} {P : Set α} {a b c d : Signal α}
    (h : Refines P a b) (i : Refines P c d) : Refines P (meet a c) (meet b d) := by
  constructor
  · intro e he
    simp [meet,h.1 e he,i.1 e he]
  · intro x hx
    obtain ⟨hx,hy⟩ : a x = true ∧ c x = true := by simpa [meet] using hx
    simp [meet,h.2 x hx,i.2 x hy]

theorem ref_join {α : Type} {P : Set α} {a b c d : Signal α}
    (h : Refines P a b) (i : Refines P c d) : Refines P (join a c) (join b d) := by
  constructor
  · intro e he
    simp [join,h.1 e he,i.1 e he]
  · intro x hx
    have one : a x = true ∨ c x = true := by simpa [join] using hx
    rcases one with p | p
    · simp [join,h.2 x p]
    · simp [join,i.2 x p]

theorem ref_comp {α : Type} {P : Set α} {a b c : Signal α}
    (h : Refines P a b) (i : Refines P b c) : Refines P a c :=
  ⟨fun e he => (h.1 e he).trans (i.1 e he),fun x p => i.2 x (h.2 x p)⟩

theorem refine_free {α : Type} (P : Set α) {B D : Set (Signal α)}
    (base : ∀ a ∈ B, ∃ b, Free D b ∧ Refines P b a) {a} (ok : Free B a) :
    ∃ b, Free D b ∧ Refines P b a := by
  apply ok {a | ∃ b, Free D b ∧ Refines P b a}
  · exact base
  · exact ⟨_,free_zero,self_refines _ _⟩
  · exact ⟨_,free_one,self_refines _ _⟩
  · intro a ha b hb
    obtain ⟨c,hc,rc⟩ := ha
    obtain ⟨d,hd,rd⟩ := hb
    exact ⟨meet c d,free_meet hc hd,ref_meet rc rd⟩

theorem choose_arm {α : Type} {P : Set α} {g : Gate α} (bad : ¬ Private P g) :
    ∃ u, (u = g.1 ∨ u = g.2) ∧ Refines P u (join g.1 g.2) := by
  classical
  by_cases left : ∃ e ∈ P, g.1 e = true ∧ g.2 e = false
  · have right : ¬∃ e ∈ P, g.2 e = true ∧ g.1 e = false := fun h => bad ⟨left,h⟩
    refine ⟨g.1,Or.inl rfl,?_,fun x h => by simp [join,h]⟩
    intro e he
    cases a : g.1 e <;> cases b : g.2 e <;> simp [join,a,b]
    exact right ⟨e,he,b,a⟩
  · refine ⟨g.2,Or.inr rfl,?_,fun x h => by simp [join,h]⟩
    intro e he
    cases a : g.1 e <;> cases b : g.2 e <;> simp [join,a,b]
    exact left ⟨e,he,a,b⟩

theorem prune {α : Type} (P : Set α) (B D : Set (Signal α)) (gs : List (Gate α)) (f : Signal α)
    (base : ∀ a ∈ B, ∃ b, Free D b ∧ Refines P b a) (ok : Valid B gs f) :
    ∃ out f', Valid D out f' ∧ Refines P f' f ∧ out.length ≤ gs.length ∧
      ∀ g ∈ out, Private P g := by
  classical
  induction gs generalizing B D with
  | nil =>
    obtain ⟨f',h,r⟩ := refine_free P base ok
    exact ⟨[],f',h,r,by simp,by simp⟩
  | cons g gs ih =>
    obtain ⟨ha,hb,tail⟩ := ok
    obtain ⟨a,fa,ra⟩ := refine_free P base ha
    obtain ⟨b,fb,rb⟩ := refine_free P base hb
    have combined := ref_join ra rb
    by_cases use : Private P (a,b)
    · let D' := insert (join a b) D
      have next : ∀ v ∈ insert (join g.1 g.2) B, ∃ w, Free D' w ∧ Refines P w v := by
        intro v hv
        rcases Set.mem_insert_iff.mp hv with rfl | old
        · exact ⟨join a b, atom (Set.mem_insert _ _), combined⟩
        · obtain ⟨w,hw,hv⟩ := base _ old
          exact ⟨w,widen (Set.subset_insert _ _) hw,hv⟩
      obtain ⟨out,f',sem,r,cost,all⟩ := ih _ D' next tail
      refine ⟨(a,b)::out,f',⟨fa,fb,sem⟩,r,by simpa using cost,?_⟩
      intro u hu
      exact (List.mem_cons.mp hu).elim (fun h => h ▸ use) (all u)
    · obtain ⟨u,side,ref⟩ := choose_arm use
      have fu : Free D u := side.elim (fun h => h ▸ fa) (fun h => h ▸ fb)
      have next : ∀ v ∈ insert (join g.1 g.2) B, ∃ w, Free D w ∧ Refines P w v := by
        intro v hv
        rcases Set.mem_insert_iff.mp hv with rfl | old
        · exact ⟨u,fu,ref_comp ref combined⟩
        · exact base _ old
      obtain ⟨out,f',sem,r,cost,all⟩ := ih _ D next tail
      exact ⟨out,f',sem,r,by simp; omega,all⟩

theorem increasing_output {n : Nat} {B : Set (Signal (Fin n → Bool))}
    (base : ∀ a ∈ B, Increasing a) {gs f} (ok : Valid B gs f) : Increasing f := by
  induction gs generalizing B with
  | nil => exact free_increasing base ok
  | cons g gs ih =>
    obtain ⟨l,r,tail⟩ := ok
    apply ih _ tail
    intro a ha
    rcases Set.mem_insert_iff.mp ha with rfl | old
    · intro x y le hx
      have either : g.1 x = true ∨ g.2 x = true := by simpa [join] using hx
      rcases either with h | h
      · simp [join,free_increasing base l x y le h]
      · simp [join,free_increasing base r x y le h]
    · exact base _ old

def Generates {n : Nat} (P : Set (Fin n → Bool)) (f : Signal (Fin n → Bool)) : Prop :=
  ∀ x, f x = true → ∃ e ∈ P, f e = true ∧ ∀ i, e i = true → x i = true

theorem private_program {n : Nat} (P : Set (Fin n → Bool)) (f : Signal (Fin n → Bool))
    (cover : Generates P f) (gs : List (Gate (Fin n → Bool))) (ok : Valid (inputs n) gs f) :
    ∃ out, Valid (inputs n) out f ∧ out.length ≤ gs.length ∧ ∀ g ∈ out, Private P g := by
  have ids : ∀ a ∈ inputs n, ∃ b, Free (inputs n) b ∧ Refines P b a :=
    fun a h => ⟨a,atom h,self_refines _ _⟩
  obtain ⟨out,v,sem,ref,cost,all⟩ := prune P _ _ gs f ids ok
  have mon := increasing_output (fun a (h : a ∈ inputs n) => by
    obtain ⟨i,rfl⟩ := h
    exact fun _ _ le => le i) sem
  have eq : v = f := by
    funext x
    apply Bool.eq_iff_iff.mpr
    refine ⟨ref.2 x,?_⟩
    intro h
    obtain ⟨e,pe,pos,le⟩ := cover x h
    exact mon e x le ((ref.1 e pe).trans pos)
  exact ⟨out,eq ▸ sem,cost,all⟩

theorem private_lower_two_step {n k : Nat} (f : Signal (Fin (n+1) → Bool))
    (low : Set (Fin (n+1))) (S : Set (Signal (Fin (n+1) → Bool))) (P : Set (Fin (n+1) → Bool))
    (inc : inputs (n+1) ⊆ S) (nonfree : ¬ Free S f) (cover : Generates P f)
    (classify : ∀ g : Gate (Fin (n+1) → Bool), Free S g.1 → Free S g.2 → Private P g →
      (∀ v ∈ low, deadAt (topMiss v) g = true → Admissible (inputs (n+1)) f (topMiss v) g) →
      join g.1 g.2 ∈ S) (rec : ∀ v ∈ low, Lower (f ∘ pin v) k) : Lower f (k+2) := by
  classical
  intro gs ok
  obtain ⟨out,sem,short,priv⟩ := private_program P f cover gs ok
  have hit : ∃ v ∈ low, 2 ≤ out.countP (deadAt (topMiss v)) := by
    by_contra no
    apply nonfree
    apply propagate_property (inputs _) S out f inc sem
    intro g hg a b
    apply classify g a b (priv g hg)
    intro v hv dg e z raw ft fe fz
    have small : out.countP (deadAt (topMiss v)) ≤ 1 := by
      by_contra h
      exact no ⟨v,hv,by omega⟩
    exact single_charge_passes sem g hg (topMiss v) e z raw ft fe fz dg small
  obtain ⟨v,hv,charge⟩ := hit
  obtain ⟨sub,sok,cost⟩ := delete_charge sem v
  have lb := rec v hv sub sok
  omega

end ThetaPrune3241

namespace Theta244Cores
open ThetaPin3241 ThetaCores3241 ThetaPrune3241
def path6 (x : Fin 6 → Bool) : Bool := (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5)
def path7 (x : Fin 7 → Bool) : Bool := (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6)
def cycle8 (x : Fin 8 → Bool) : Bool := (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6) || (x 6 && x 7) || (x 7 && x 0)
def twoEnds (x : Fin 8 → Bool) : Bool := (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 0) || (x 0 && x 6) || (x 2 && x 7)
def tailTwo (x : Fin 8 → Bool) : Bool := (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 0) || (x 0 && x 6) || (x 6 && x 7)
def theta (x : Fin 9 → Bool) : Bool := (x 0 && x 2) || (x 1 && x 2) || (x 0 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 1 && x 5) || (x 0 && x 6) || (x 6 && x 7) || (x 7 && x 8) || (x 1 && x 8)

theorem path6_lower (rec : Lower path5 3) : Lower path6 4 := by
  have eq : path6 ∘ pin (5 : Fin 6) = path5 := by
    funext x
    exact (by decide +kernel : ∀ y, path6 (pin (5 : Fin 6) y) = path5 y) x
  apply lower_one_step path6 5 (row 48) (row 16)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact eq.symm ▸ rec

theorem path7_lower (rec : Lower path6 4) : Lower path7 5 := by
  have eq : path7 ∘ pin (6 : Fin 7) = path6 := by
    funext x
    exact (by decide +kernel : ∀ y, path7 (pin (6 : Fin 7) y) = path6 y) x
  apply lower_one_step path7 6 (row 96) (row 32)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact eq.symm ▸ rec

theorem twoEnds_lower (rec : Lower pendant7 6) : Lower twoEnds 7 := by
  have eq : twoEnds ∘ pin (7 : Fin 8) = pendant7 := by
    funext x
    exact (by decide +kernel : ∀ y, twoEnds (pin (7 : Fin 8) y) = pendant7 y) x
  apply lower_one_step twoEnds 7 (row 132) (row 4)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact eq.symm ▸ rec

theorem tailTwo_lower (rec : Lower pendant7 6) : Lower tailTwo 7 := by
  have eq : tailTwo ∘ pin (7 : Fin 8) = pendant7 := by
    funext x
    exact (by decide +kernel : ∀ y, tailTwo (pin (7 : Fin 8) y) = pendant7 y) x
  apply lower_one_step tailTwo 7 (row 192) (row 64)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact eq.symm ▸ rec

def cycleRelabel : Fin 8 → Fin 7 → Fin 7 := ![![0,1,2,3,4,5,6],![0,6,5,4,3,2,1],![1,0,6,5,4,3,2],![2,1,0,6,5,4,3],![3,2,1,0,6,5,4],![2,3,4,5,6,0,1],![1,2,3,4,5,6,0],![0,1,2,3,4,5,6]]
def thetaRelabel : Fin 9 → Fin 8 → Fin 8 := ![![0,1,2,3,4,5,6,7],![0,1,2,3,4,5,6,7],![0,4,1,2,3,7,6,5],![2,0,1,7,6,3,4,5],![0,2,1,6,7,5,4,3],![0,2,1,6,7,5,4,3],![2,0,1,3,4,5,7,6],![0,2,1,5,4,3,6,7],![0,2,1,5,4,3,6,7]]
def lows : Set (Fin 9) := {v | 2 ≤ v.val}
def cofactor (v : Fin 9) :=
  if v = 2 then cycle8 else if v = 4 ∨ v = 7 then twoEnds else tailTwo

theorem cycle8_deleted (v : Fin 8) : Lower (cycle8 ∘ pin v) 5 := by
  have all : ∀ i x, (cycle8 ∘ pin i) (x ∘ cycleRelabel i) = path7 x := by decide +kernel
  apply lower_rename (cycleRelabel v)
  have eq : (fun x => (cycle8 ∘ pin v) (x ∘ cycleRelabel v)) = path7 := funext (all v)
  exact eq.symm ▸ path7_lower (path6_lower path5_lower)

theorem theta_deleted (h6 : Lower cycle6 5) (h8 : Lower cycle8 7) (v : Fin 9) (hv : v ∈ lows) :
    Lower (theta ∘ pin v) 7 := by
  have all : ∀ i : Fin 9, 2 ≤ i.val → ∀ x, (theta ∘ pin i) (x ∘ thetaRelabel i) = cofactor i x := by
    decide +kernel
  apply lower_rename (thetaRelabel v)
  have eq : (fun x => (theta ∘ pin v) (x ∘ thetaRelabel v)) = cofactor v := funext (all v hv)
  rw [eq]
  unfold cofactor
  split
  · exact h8
  · split
    · exact twoEnds_lower (pendant7_from_core h6)
    · exact tailTwo_lower (pendant7_from_core h6)

theorem cycle8_of_classifier {S} (h : Classifier cycle8 Set.univ S) : Lower cycle8 7 :=
  lower_two_step cycle8 Set.univ S h.1 h.2.1 h.2.2 (fun v _ => cycle8_deleted v)

def positive : Set (Fin 9 → Bool) := {x |
  ∃ i j : Fin 9, ((i.val,j.val) ∈ ([(0, 2), (1, 2), (0, 3), (3, 4), (4, 5), (1, 5), (0, 6), (6, 7), (7, 8), (1, 8)] : List (Nat × Nat))) ∧
    x = row (2^i.val+2^j.val)}

theorem generates : Generates positive theta := by
  intro x hx
  have all : ∀ y : Fin 9 → Bool, theta y = true →
      ∃ i j : Fin 9, (i.val,j.val) ∈ ([(0, 2), (1, 2), (0, 3), (3, 4), (4, 5), (1, 5), (0, 6), (6, 7), (7, 8), (1, 8)] : List (Nat × Nat)) ∧
        theta (row (2^i.val+2^j.val)) = true ∧ ∀ l : Fin 9, row (2^i.val+2^j.val) l = true → y l = true := by
    decide +kernel
  obtain ⟨i,j,edge,yes,le⟩ := all x hx
  exact ⟨_,⟨i,j,edge,rfl⟩,yes,le⟩

end Theta244Cores

namespace Theta244Finish
open ThetaPin3241 ThetaPrune3241 Theta244Cores ThetaClass3241

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
theorem cycle_geo : Geometry ∅ cycle8 := by constructor <;> decide +kernel

theorem cycle_classifier : ThetaCores3241.Classifier cycle8 Set.univ (pool ∅) := by
  refine ⟨base_subset _,?_,?_⟩
  · exact nonfree cycle8 ∅ (bits {0,1}) (bits {2,3}) (bits ∅)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro g a b h
    exact classify cycle_geo g a b (fun v _ => h v (Set.mem_univ v))

theorem deleted (v : Fin 9) (hv : v ∈ lows) : Lower (theta ∘ pin v) 7 :=
  theta_deleted (ThetaCores3241.cycle6_of_classifier ThetaClass3241.cycle_classifier)
    (cycle8_of_classifier cycle_classifier) v hv

theorem nine_of_classifier {P : Set (Fin 9 → Bool)} {S : Set (Signal (Fin 9 → Bool))}
    (base : inputs 9 ⊆ S) (nonfree : ¬ Free S theta) (cover : Generates P theta)
    (classify : ∀ g : Gate (Fin 9 → Bool), Free S g.1 → Free S g.2 → Private P g →
      (∀ v ∈ lows, deadAt (topMiss v) g = true → Admissible (inputs 9) theta (topMiss v) g) →
      join g.1 g.2 ∈ S) : Lower theta 9 :=
  private_lower_two_step theta lows S P base nonfree cover classify deleted

def eleven : Fin 11 → Finset (Fin 9) :=
  ![{1,3,6}, {1,4,6}, {1,3,7}, {0,1,4,7}, {2,4,7}, {0,5,7}, {2,3,5,7}, {0,4,8},
    {0,5,8}, {2,4,6,8}, {2,3,5,6,8}]

def upper : PEqualNP.CircuitLowerBounds.Circuit := ⟨
  [⟨.or,[2,3]⟩,⟨.or,[9,6]⟩,⟨.and,[0,10]⟩,
   ⟨.or,[2,5]⟩,⟨.or,[12,8]⟩,⟨.and,[1,13]⟩,
   ⟨.or,[3,5]⟩,⟨.and,[4,15]⟩,⟨.or,[6,8]⟩,⟨.and,[7,17]⟩,
   ⟨.or,[11,14]⟩,⟨.or,[16,18]⟩,⟨.or,[19,20]⟩],21⟩

end Theta244Finish

namespace Theta244
open ThetaPin3241
abbrev X := Fin 9 → Bool
abbrev W := BitVec 28
def readBit (w : W) (i : Fin 28) : Bool := w[i.val]
def rowMasks : List Nat := [5,6,9,24,48,34,65,192,384,258,74,82,138,147,148,161,172,273,289,340,364,507,503,495,479,447,383,255]
def row (i : Fin 28) (v : Fin 9) : Bool := (rowMasks.getD i.val 0).testBit v.val
def target (x : X) : Bool := (x 0 && x 2) || (x 1 && x 2) || (x 0 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 1 && x 5) || (x 0 && x 6) || (x 6 && x 7) || (x 7 && x 8) || (x 1 && x 8)
def code : W := 266339327
def rawMasks : List W := [266772549,266354210,265895939,263263244,258631704,250970160,234360000,199356800,134087424]
def base : List W := [0,134087424,199356800,234360000,250970160,258631704,263263244,265895939,266346496,266354210,266772549,266780263,268435455]
def arm : List W := [0,2097152,4194304,6291456,8388608,10485760,12582912,14680064,16777216,18874368,20971520,23068672,25165824,27262976,29360128,31457280,33554432,35651584,37748736,39845888,41943040,44040192,46137344,48234496,50331648,52428800,54525952,56623104,58720256,60817408,62914560,65011712,65011968,67108864,69206016,71303168,73400320,75497472,76546048,77594624,78643200,79691776,80740352,81788928,82837504,83886080,85983232,88080384,88604672,90177536,90701824,92274688,93323264,94371840,95420416,96468992,98041856,98566144,100139008,100663296,102760448,104857600,106954752,109051904,110100480,111149056,112197632,113246208,114294784,115343360,115605504,116654080,117440512,119537664,121634816,122159104,123731968,123863040,124387328,125829120,126877696,127926272,128974848,130023424,131596288,132120576,132121088,132513792,132514304,134087424,134217728,136314880,138412032,140509184,142606336,144703488,146800640,148897792,150994944,153092096,155189248,157286400,159383552,161480704,163577856,165675008,165675136,167772160,169869312,171966464,174063616,176160768,176226304,178257920,178323456,180355072,180420608,182452224,182484992,182550528,184549376,186646528,188743680,188760064,190849024,190865408,192937984,193003520,195035136,195039232,195104768,197132288,197214208,199237632,199241728,199270400,199274496,199356800,201326592,203423744,205520896,207618048,209715200,210763776,211812352,212860928,213909504,214958080,216006656,217055232,218103808,220200960,222298112,222822400,224395264,224397312,224921600,226492416,227540992,228589568,228590592,229639168,230686720,232259584,232783872,232783936,232786944,232787008,234360000,234881024,236978176,239075328,241172480,241172496,243269632,244383744,245366784,246480896,247463936,248578048,249561088,249561120,249856000,249856032,250970160,251658240,253755392,253755400,255852544,256393216,257957888,257959936,258088960,258091008,258631704,260046848,261160960,262144000,262144004,262149120,262149124,263263244,264241152,264241153,264241154,264241155,265895939,266346496,266354210,266772549,266780263,268435455]
def posArm : List W := [65011968,132121088,132514304,134087424,165675136,199356800,232783936,232787008,234360000,241172496,249561120,249856032,250970160,253755400,258631704,262144004,262149124,263263244,264241153,264241154,264241155,265895939,266354210,266772549,266780263,268435455]
structure Test where
  v : Fin 9
  t : Fin 28
  e : Fin 28
  z : Fin 28
  deriving DecidableEq
def tests : List Test := [⟨2,21,0,13⟩,⟨2,21,0,15⟩,⟨2,21,0,17⟩,⟨2,21,0,18⟩,⟨2,21,1,10⟩,⟨2,21,1,11⟩,⟨2,21,1,12⟩,⟨2,21,1,13⟩,⟨3,22,2,13⟩,⟨3,22,2,15⟩,⟨3,22,2,17⟩,⟨3,22,2,18⟩,⟨3,22,3,11⟩,⟨3,22,3,13⟩,⟨3,22,3,14⟩,⟨3,22,3,17⟩,⟨3,22,3,19⟩,⟨4,23,3,10⟩,⟨4,23,3,12⟩,⟨4,23,3,16⟩,⟨4,23,3,20⟩,⟨4,23,4,15⟩,⟨4,23,4,16⟩,⟨4,23,4,18⟩,⟨4,23,4,20⟩,⟨5,24,4,11⟩,⟨5,24,4,13⟩,⟨5,24,4,14⟩,⟨5,24,4,17⟩,⟨5,24,4,19⟩,⟨5,24,5,10⟩,⟨5,24,5,11⟩,⟨5,24,5,12⟩,⟨5,24,5,13⟩,⟨6,25,6,13⟩,⟨6,25,6,15⟩,⟨6,25,6,17⟩,⟨6,25,6,18⟩,⟨6,25,7,12⟩,⟨6,25,7,13⟩,⟨6,25,7,14⟩,⟨6,25,7,15⟩,⟨6,25,7,16⟩,⟨7,26,7,10⟩,⟨7,26,7,11⟩,⟨7,26,7,19⟩,⟨7,26,7,20⟩,⟨7,26,8,17⟩,⟨7,26,8,18⟩,⟨7,26,8,19⟩,⟨7,26,8,20⟩,⟨8,27,8,12⟩,⟨8,27,8,13⟩,⟨8,27,8,14⟩,⟨8,27,8,15⟩,⟨8,27,8,16⟩,⟨8,27,9,10⟩,⟨8,27,9,11⟩,⟨8,27,9,12⟩,⟨8,27,9,13⟩]
def edgeIdx (i : Fin 10) : Fin 28 := i.castLE (by decide)
def positives : Set X := Set.range (fun i : Fin 10 => row (edgeIdx i))
def low : Set (Fin 9) := {v | 2 ≤ v.val}
def represents (a : Signal X) (w : W) : Prop := ∀ i, a (row i) = readBit w i
def pool : Set (Signal X) := {a | ∃ w ∈ base, represents a w}

def privateMask (a b : W) : Prop :=
  (∃ i : Fin 10, readBit a (edgeIdx i) = true ∧ readBit b (edgeIdx i) = false) ∧
  (∃ i : Fin 10, readBit b (edgeIdx i) = true ∧ readBit a (edgeIdx i) = false)

def good (a b : W) (q : Test) : Prop :=
  (readBit a q.t && readBit b q.t) = false →
    readBit (a ||| b) q.t = true ∧ readBit (a ||| b) q.e = true ∧ readBit (a ||| b) q.z = false

instance (a b : W) : Decidable (privateMask a b) := by unfold privateMask; infer_instance
instance (a b : W) (q : Test) : Decidable (good a b q) := by unfold good; infer_instance

theorem and_table (a b : W) (ha : a ∈ posArm) (hb : b ∈ base)
    (i : Fin 10) (hit : readBit (b &&& a) (edgeIdx i) = true) : (b &&& a) ∈ posArm := by
  have table : posArm.all (fun u => base.all (fun v => posArm.contains (v &&& u) ||
      decide (∀ j : Fin 10, readBit (v &&& u) (edgeIdx j) = false))) = true := by decide +kernel
  have either := List.all_eq_true.mp (List.all_eq_true.mp table a ha) b hb
  rcases Bool.or_eq_true_iff.mp either with yes | no
  · simpa using yes
  · have v := of_decide_eq_true no i
    simp [hit] at v

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
theorem or_table (a : W) (ha : a ∈ posArm) (b : W) (hb : b ∈ posArm)
    (p : privateMask a b) (h : ∀ q ∈ tests, good a b q) : (a ||| b) ∈ base := by
  have table : posArm.all (fun u => posArm.all (fun v =>
      base.contains (u ||| v) || !decide (privateMask u v) ||
      !tests.all (fun q => decide (good u v q)))) = true := by decide +kernel
  have atPair := List.all_eq_true.mp (List.all_eq_true.mp table a ha) b hb
  have gates : tests.all (fun q => decide (good a b q)) = true :=
    List.all_eq_true.mpr (fun q hq => decide_eq_true (h q hq))
  simpa [p,gates] using atPair

theorem probes : ∀ q ∈ tests, 2 ≤ q.v.val ∧ (∀ i, row q.t i = topMiss q.v i) ∧
    target (row q.t) = true ∧ target (row q.e) = true ∧ target (row q.z) = false ∧
    ∀ i, row q.t i = true → row q.e i = true → row q.z i = true := by decide +kernel

theorem represent_and {a b : Signal X} {u v : W} (ha : represents a u) (hb : represents b v) :
    represents (meet a b) (u &&& v) := by
  intro i
  simp [meet,ha i,hb i,readBit]

theorem represent_or {a b : Signal X} {u v : W} (ha : represents a u) (hb : represents b v) :
    represents (join a b) (u ||| v) := by
  intro i
  simp [join,ha i,hb i,readBit]

theorem free_arm {a : Signal X} (h : Free pool a) (i : Fin 10) (onEdge : a (row (edgeIdx i)) = true) :
    ∃ w ∈ posArm, represents a w := by
  rcases factors h with rfl | ⟨xs,hs,rfl⟩
  · contradiction
  · clear h
    induction xs with
    | nil => exact ⟨268435455,by decide +kernel,(by decide +kernel : ∀ i : Fin 28, true = readBit 268435455 i)⟩
    | cons a xs ih =>
      obtain ⟨u,hu,ra⟩ := hs a (by simp)
      obtain ⟨_,tail⟩ := Bool.and_eq_true_iff.mp onEdge
      obtain ⟨v,hv,rs⟩ := ih (fun b hb => hs b (by simp [hb])) tail
      have allRep : represents (fun x => (a::xs).all (fun f => f x)) (u &&& v) := by
        intro k
        change ((a::xs).all (fun f => f (row k))) = _
        rw [List.all_cons]
        exact (represent_and ra rs) k
      exact ⟨_,and_table v u hv hu i ((allRep _).symm.trans onEdge),allRep⟩

theorem inputs_pool : inputs 9 ⊆ pool := by
  rintro _ ⟨i,rfl⟩
  have tab : ∀ j : Fin 9, rawMasks.getD j.val 0 ∈ base ∧
      ∀ k, row k j = readBit (rawMasks.getD j.val 0) k := by decide +kernel
  exact ⟨_,(tab i).1,(tab i).2⟩

theorem target_nonfree : ¬ Free pool target := by
  intro h
  obtain ⟨a,ha,rep⟩ := free_arm h 0 (by decide +kernel)
  have fixed : ∀ i : Fin 28, target (row i) = readBit code i := by decide +kernel
  have different : code ∉ posArm := by decide +kernel
  have eq : a = code := by
    apply BitVec.eq_of_getElem_eq
    intro k hk
    exact (rep ⟨k,hk⟩).symm.trans (fixed ⟨k,hk⟩)
  exact different (eq ▸ ha)

theorem classify (g : Gate X) (fa : Free pool g.1) (fb : Free pool g.2)
    (priv : ThetaPrune3241.Private positives g)
    (valid : ∀ v ∈ low, deadAt (topMiss v) g = true → Admissible (inputs 9) target (topMiss v) g) :
    join g.1 g.2 ∈ pool := by
  obtain ⟨⟨_,⟨i,rfl⟩,ia,ib⟩,⟨_,⟨j,rfl⟩,jb,ja⟩⟩ := priv
  obtain ⟨a,pa,ra⟩ := free_arm fa i ia
  obtain ⟨b,pb,rb⟩ := free_arm fb j jb
  rw [ra] at ia ja
  rw [rb] at ib jb
  have joined := represent_or ra rb
  refine ⟨_,or_table a pa b pb ⟨⟨i,ia,ib⟩,⟨j,jb,ja⟩⟩ ?_,joined⟩
  intro q hq dead
  obtain ⟨lo,point,ft,fe,fz,pass⟩ := probes q hq
  have eq := funext point
  have dg : deadAt (topMiss q.v) g = true := by
    simp [← eq,deadAt,ra q.t,rb q.t,dead]
  have adm := valid q.v lo dg
  rw [← eq] at adm
  obtain ⟨st,se,sz⟩ := adm (row q.e) (row q.z) (pass_inputs _ _ _ pass) ft fe fz
  exact ⟨(joined q.t).symm.trans st,(joined q.e).symm.trans se,(joined q.z).symm.trans sz⟩

theorem generates : ThetaPrune3241.Generates positives target := by
  have all : ∀ x : X, target x = true → ∃ i : Fin 10, target (row (edgeIdx i)) = true ∧
      ∀ j, row (edgeIdx i) j = true → x j = true := by decide +kernel
  intro x hx
  obtain ⟨i,yes,le⟩ := all x hx
  exact ⟨_,⟨i,rfl⟩,yes,le⟩

theorem nine : Lower Theta244Cores.theta 9 :=
  Theta244Finish.nine_of_classifier inputs_pool target_nonfree generates classify

end Theta244

namespace LeafAnd3241
open ThetaPin3241 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm

abbrev X (n : Nat) := Fin n → Bool
def dual {n : Nat} (f : Signal (X n)) : Signal (X n) := fun x => !(f fun i => !(x i))

theorem dual_wire {n : Nat} {B : Set (Signal (X n))} {w : List (Signal (X n))}
    (hw : ∀ a ∈ w, Free B (dual a)) (i : Nat) : Free B (dual (wire w i)) := by
  induction w generalizing i with
  | nil => cases i <;> exact free_one
  | cons a w ih => cases i with
    | zero => exact hw _ List.mem_cons_self
    | succ i => exact ih (fun a ha => hw a (List.mem_cons_of_mem _ ha)) i

theorem dual_compress {n : Nat} (gs : List PhysicalGate) (output : Nat) (w : List (Signal (X n)))
    (B : Set (Signal (X n))) (hw : ∀ a ∈ w, Free B (dual a)) (shapes : ∀ g ∈ gs, pairShape g) :
    ∃ ops : List (ThetaPin3241.Gate (X n)), Valid B ops (dual (wire (gs.foldl step w) output)) ∧
      ops.length = gs.countP ThetaAnd3241.andGate := by
  induction gs generalizing w B with
  | nil => exact ⟨[],dual_wire hw output,rfl⟩
  | cons g gs ih =>
    obtain ⟨hop,i,j,pins⟩ := shapes g List.mem_cons_self
    have tail (h : PhysicalGate) (hh : h ∈ gs) := shapes h (List.mem_cons_of_mem _ hh)
    let a := dual (wire w i)
    let b := dual (wire w j)
    rcases hop with kind | kind
    · let D := insert (join a b) B
      have eq : step w g = w ++ [meet (wire w i) (wire w j)] := by
        simp [step,pins,kind,GateOp.eval]
        rfl
      have dual_and : dual (meet (wire w i) (wire w j)) = join a b := by
        funext x
        simp [dual,meet,join,a,b,Bool.not_and]
      have ext : ∀ f ∈ step w g, Free D (dual f) := by
        intro f hf
        rw [eq,List.mem_append,List.mem_singleton] at hf
        rcases hf with old | rfl
        · exact widen (Set.subset_insert _ _) (hw f old)
        · rw [dual_and]
          exact atom (Set.mem_insert _ _)
      obtain ⟨ops,sem,cost⟩ := ih (step w g) D ext tail
      refine ⟨(a,b)::ops,⟨dual_wire hw i,dual_wire hw j,sem⟩,?_⟩
      have yes : ThetaAnd3241.andGate g = true := by simp [ThetaAnd3241.andGate,kind]
      simp [cost,yes]
    · have eq : step w g = w ++ [join (wire w i) (wire w j)] := by
        simp [step,pins,kind,GateOp.eval]
        rfl
      have dual_or : dual (join (wire w i) (wire w j)) = meet a b := by
        funext x
        simp [dual,meet,join,a,b,Bool.not_or]
      have ext : ∀ f ∈ step w g, Free B (dual f) := by
        intro f hf
        rw [eq,List.mem_append,List.mem_singleton] at hf
        rcases hf with old | rfl
        · exact hw f old
        · rw [dual_or]
          exact free_meet (dual_wire hw i) (dual_wire hw j)
      obtain ⟨ops,sem,cost⟩ := ih (step w g) B ext tail
      refine ⟨ops,sem,?_⟩
      have no : ThetaAnd3241.andGate g = false := by simp [ThetaAnd3241.andGate,kind]
      simpa [no] using cost

theorem and_lower_circuit {n k : Nat} (f : Signal (X n)) (lb : Lower (dual f) k)
    (C : Circuit) (ao : IsAO2 n C) (correct : circuitFun n C = f) :
    k ≤ C.gates.countP ThetaAnd3241.andGate := by
  let w : List (Signal (X n)) := (List.finRange n).map (fun i x => x i)
  have ok (a) (ha : a ∈ w) : Free (inputs n) (dual a) := by
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp ha
    apply atom
    exact ⟨i,funext (fun x => by simp [dual])⟩
  have shapes (g : PhysicalGate) (hg : g ∈ C.gates) : pairShape g := by
    refine ⟨ao.1 _ hg,?_⟩
    have len := ao.2.2 _ hg
    match h : g.inputs with
    | [] => simp [h] at len
    | [_] => simp [h] at len
    | a::b::rest =>
      have nil : rest = [] := List.length_eq_zero_iff.mp (by simpa [h] using len)
      exact ⟨a,b,by rw [nil]⟩
  obtain ⟨ops,sem,cost⟩ := dual_compress C.gates C.output w (inputs n) ok shapes
  have eq : wire (C.gates.foldl step w) C.output = circuitFun n C := by
    funext x
    rw [← wire_point,run_point]
    have start : w.map (fun f => f x) = List.ofFn x := by simp [w,List.ofFn_eq_map]
    rw [start]
    rfl
  rw [eq,correct] at sem
  exact cost ▸ lb ops sem

theorem save_at {m n k : Nat} (f : Signal (X n)) (v : Fin n) (e z : X n) (p : X m → X n)
    (inputs_ok : ∀ a ∈ inputs n, Free (inputs m) (a ∘ p))
    (bounded : ∀ x i, p x i = true → topMiss v i = true)
    (pass : ∀ i, topMiss v i = true → e i = true → z i = true)
    (top : f (topMiss v) = true) (edge : f e = true) (neg : f z = false)
    (sub : Lower (f ∘ p) k) : Lower f (k+1) := by
  intro gs ok
  obtain ⟨g,hg,dead,_⟩ := critical_gate gs (inputs n) f _ _ _ (pass_inputs _ _ _ pass) ok top edge neg
  obtain ⟨l,r⟩ := active_monotone (fun a (h : a ∈ inputs n) => by
    obtain ⟨i,rfl⟩ := h
    exact fun _ _ le => le i) ok g hg
  have zero {a : Signal (X n)} (inc : Increasing a) (off : a (topMiss v) = false) :
      ∀ x, a (p x) = false := by
    intro x
    cases h : a (p x) with
    | false => rfl
    | true => simp [inc _ _ (bounded x) h] at off
  have killed : Killed p g := dead.imp (zero l) (zero r)
  have charge : 0 < gs.countP (killedBit p) :=
    List.countP_pos_iff.mpr ⟨g,hg,by simp [killedBit,killed]⟩
  obtain ⟨out,sem,cost⟩ := restrict_transfer p gs _ _ f inputs_ok ok
  have lower := sub out sem
  omega

def cover {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (x : X n) : Bool :=
  decide (∀ a b, G.Adj a b → x a = true ∨ x b = true)

theorem cover_dual {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    dual (NestedCover.graphFun G ∅) = cover G := by
  funext x
  apply Bool.eq_iff_iff.mpr
  simp [dual,NestedCover.graphFun,cover]
  grind

def pinLeaf {n : Nat} (v w : Fin n) (x : X n) (i : Fin n) : Bool :=
  if i = v then false else if i = w then true else x i

theorem leaf_step {n k : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (v w : Fin n) (adj : G.Adj v w) (leaf : ∀ i, G.Adj v i → i = w)
    (sub : Lower (cover (G.deleteIncidenceSet w)) k) : Lower (cover G) (k+1) := by
  have ne := G.ne_of_adj adj
  have hi (i : Fin n) : cover G (topMiss i) = true := by
    simp only [cover,decide_eq_true_eq,topMiss]
    intro a b ab
    by_cases av : a = i
    · exact Or.inr (fun (bv : b = i) => G.ne_of_adj ab (av.trans bv.symm))
    · exact Or.inl (by simp [av])
  let z : X n := fun i => decide (i ≠ v ∧ i ≠ w)
  have neg : cover G z = false := by
    apply decide_eq_false_iff_not.mpr
    intro h
    simpa [z] using h v w adj
  have cof : cover G ∘ pinLeaf v w = cover (G.deleteIncidenceSet w) := by
    funext x
    apply Bool.eq_iff_iff.mpr
    simp only [Function.comp_apply,cover,decide_eq_true_eq,SimpleGraph.deleteIncidenceSet_adj]
    constructor
    · intro h a b ⟨ab,aw,bw⟩
      have av : a ≠ v := fun e => bw (leaf b (e ▸ ab))
      have bv : b ≠ v := fun e => aw (leaf a (e ▸ ab.symm))
      simpa [pinLeaf,av,bv,aw,bw] using h a b ab
    · intro h a b ab
      by_cases aw : a = w
      · simp [pinLeaf,aw,ne.symm]
      by_cases bw : b = w
      · simp [pinLeaf,bw,ne.symm]
      have av : a ≠ v := fun e => bw (leaf b (e ▸ ab))
      have bv : b ≠ v := fun e => aw (leaf a (e ▸ ab.symm))
      simpa [pinLeaf,av,bv,aw,bw] using h a b ⟨ab,aw,bw⟩
  apply save_at (cover G) v (topMiss w) z (pinLeaf v w) _ _ _ (hi v) (hi w) neg (cof.symm ▸ sub)
  · rintro _ ⟨i,rfl⟩
    by_cases iv : i = v
    · simpa [Function.comp_def,pinLeaf,iv] using (free_zero (B := inputs n))
    by_cases iw : i = w
    · simpa [Function.comp_def,pinLeaf,iv,iw,ne.symm] using (free_one (B := inputs n))
    · simpa [Function.comp_def,pinLeaf,iv,iw] using (atom (B := inputs n) ⟨i,rfl⟩)
  · intro x i pi
    by_contra h
    have iv : i = v := by simpa [topMiss] using h
    simp [pinLeaf,iv] at pi
  · intro i tv tw
    simpa [z,topMiss] using And.intro tv tw

end LeafAnd3241

namespace LeafCore3241
open ThetaPin3241 LeafAnd3241 PEqualNP.MetaComplexity PEqualNP.TopForm

def edgeFun {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (x : X n) : Bool :=
  decide (∃ a b, G.Adj a b ∧ x a = true ∧ x b = true)

theorem ordinary_eq {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    NestedCover.graphFun G ∅ = edgeFun G := by
  funext x
  simp [NestedCover.graphFun,edgeFun]

def Leafless {n : Nat} (G : SimpleGraph (Fin n)) : Prop :=
  ¬ ∃ v w, G.Adj v w ∧ ∀ a, G.Adj v a → a = w

def Counts {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : Prop :=
  Lower (edgeFun G) (G.edgeFinset.card - 1) ∧
    ∃ S : Finset (Fin n), G.IsVertexCover (S : Set (Fin n)) ∧ Lower (cover G) S.card

def pinZero {n : Nat} (v : Fin n) (x : X n) (i : Fin n) := if i = v then false else x i

theorem or_leaf {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (v w : Fin n)
    (vw : G.Adj v w) (leaf : ∀ a, G.Adj v a → a = w)
    (sub : Lower (edgeFun (G.deleteIncidenceSet v)) ((G.deleteIncidenceSet v).edgeFinset.card - 1)) :
    Lower (edgeFun G) (G.edgeFinset.card - 1) := by
  have dg : G.degree v = 1 := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mpr ⟨w,vw,leaf⟩
  have card := G.card_edgeFinset_deleteIncidenceSet v
  rw [dg] at card
  by_cases small : G.edgeFinset.card ≤ 1
  · have h : G.edgeFinset.card - 1 = 0 := by omega
    rw [h]
    exact lower_zero _
  have pos : (G.deleteIncidenceSet v).edgeFinset.Nonempty := Finset.card_pos.mp (by omega)
  have nonzero := (G.deleteIncidenceSet v).edgeFinset_nonempty.mp pos
  have pair : ∃ a b, (G.deleteIncidenceSet v).Adj a b := by
    by_contra! no
    exact nonzero (SimpleGraph.eq_bot_iff_forall_not_adj.mpr no)
  obtain ⟨a,b,ab⟩ := pair
  obtain ⟨edge,av,bv⟩ := SimpleGraph.deleteIncidenceSet_adj.mp ab
  have top : edgeFun G (topMiss v) = true := by
    exact decide_eq_true ⟨a,b,edge,by simp [topMiss,av],by simp [topMiss,bv]⟩
  let e : X n := fun i => decide (i = v ∨ i = w)
  let z : X n := fun i => decide (i = w)
  have fe : edgeFun G e = true := decide_eq_true ⟨v,w,vw,by simp [e],by simp [e]⟩
  have fz : edgeFun G z = false := by
    apply decide_eq_false_iff_not.mpr
    rintro ⟨c,d,hcd,hc,hd⟩
    exact hcd.ne ((by simpa [z] using hc : c = w).trans (by simpa [z] using hd : d = w).symm)
  have cof : edgeFun G ∘ pinZero v = edgeFun (G.deleteIncidenceSet v) := by
    funext x
    apply Bool.eq_iff_iff.mpr
    simp only [Function.comp_apply,edgeFun,decide_eq_true_eq,SimpleGraph.deleteIncidenceSet_adj]
    constructor
    · rintro ⟨i,j,ij,hi,hj⟩
      have iv : i ≠ v := fun eq => by simp [pinZero,eq] at hi
      have jv : j ≠ v := fun eq => by simp [pinZero,eq] at hj
      exact ⟨i,j,⟨ij,iv,jv⟩,by simpa [pinZero,iv] using hi,by simpa [pinZero,jv] using hj⟩
    · rintro ⟨i,j,⟨ij,iv,jv⟩,hi,hj⟩
      exact ⟨i,j,ij,by simpa [pinZero,iv] using hi,by simpa [pinZero,jv] using hj⟩
  have eq : G.edgeFinset.card - 1 = ((G.deleteIncidenceSet v).edgeFinset.card - 1) + 1 := by omega
  rw [eq]
  apply save_at (edgeFun G) v e z (pinZero v) _ _ _ top fe fz (cof.symm ▸ sub)
  · rintro _ ⟨i,rfl⟩
    by_cases iv : i = v
    · simpa [Function.comp_def,pinZero,iv] using (free_zero (B := inputs n))
    · simpa [Function.comp_def,pinZero,iv] using (atom (B := inputs n) ⟨i,rfl⟩)
  · intro x i h
    by_contra no
    have iv : i = v := by simpa [topMiss] using no
    simp [pinZero,iv] at h
  · intro i tv ei
    have iv : i ≠ v := by simpa [topMiss] using tv
    simpa [e,z,iv] using ei

theorem add_leaf {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (v w : Fin n)
    (adj : G.Adj v w) (leaf : ∀ a, G.Adj v a → a = w)
    (dropV : Counts (G.deleteIncidenceSet v)) (dropW : Counts (G.deleteIncidenceSet w)) :
    Counts G := by
  refine ⟨or_leaf G v w adj leaf dropV.1,?_⟩
  obtain ⟨S,cv,lo⟩ := dropW.2
  refine ⟨insert w S,?_,?_⟩
  · intro a b ab
    by_cases aw : a = w
    · exact Or.inl (by simp [aw])
    by_cases bw : b = w
    · exact Or.inr (by simp [bw])
    exact (cv (SimpleGraph.deleteIncidenceSet_adj.mpr ⟨ab,aw,bw⟩)).imp
      (fun h => Finset.mem_insert_of_mem h) (fun h => Finset.mem_insert_of_mem h)
  · have pay := leaf_step G v w adj leaf lo
    intro ops valid
    exact (Finset.card_insert_le _ _).trans (pay ops valid)

theorem peel_to_core {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (base : ∀ (H : SimpleGraph (Fin n)) [DecidableRel H.Adj], H ≤ G → Leafless H → Counts H) :
    Counts G := by
  classical
  have work (k : Nat) : ∀ (H : SimpleGraph (Fin n)) [DecidableRel H.Adj],
      H ≤ G → H.edgeFinset.card = k → Counts H := by
    induction k using Nat.strong_induction_on with
    | ind k rec =>
      intro H _ hg count
      by_cases last : Leafless H
      · exact base H hg last
      obtain ⟨v,w,adj,leaf⟩ := not_not.mp last
      apply add_leaf H v w adj leaf
      all_goals
        apply rec _ _ _ (le_trans (H.deleteIncidenceSet_le _) hg) rfl
        rw [H.card_edgeFinset_deleteIncidenceSet,← count]
      · have h := (H.degree_pos_iff_exists_adj v).mpr ⟨w,adj⟩
        have c := H.degree_le_card_edgeFinset v
        omega
      · have h := (H.degree_pos_iff_exists_adj w).mpr ⟨v,adj.symm⟩
        have c := H.degree_le_card_edgeFinset w
        omega
  exact work _ G le_rfl rfl

theorem forest_leaf {n : Nat} (G : SimpleGraph (Fin n)) (h : G.IsAcyclic)
    (a b : Fin n) (adj : G.Adj a b) : ¬ Leafless G := by
  let _ : Nonempty (Fin n) := ⟨a⟩
  obtain ⟨u,t,p,path,maximal⟩ := SimpleGraph.Walk.exists_isPath_forall_isPath_length_le_length G
  have pathAB : (SimpleGraph.Walk.cons adj .nil).IsPath :=
    SimpleGraph.Walk.IsPath.cons SimpleGraph.Walk.IsPath.nil (by simp [adj.ne])
  have pos : 0 < p.length := lt_of_lt_of_le (by decide : 0 < 1) (maximal a b _ pathAB)
  have nonempty : ¬p.Nil := by grind
  intro none
  apply none
  refine ⟨u,p.snd,p.adj_snd nonempty,?_⟩
  intro w uw
  apply h.eq_snd_of_adj_start path uw
  by_contra miss
  have bigger := maximal _ _ (p.cons uw.symm) (path.cons miss)
  simp at bigger

theorem forest_counts {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h : G.IsAcyclic) : Counts G := by
  apply peel_to_core G
  intro H _ hg last
  have all (v w) : ¬ H.Adj v w := fun adj => forest_leaf H (h.anti hg) v w adj last
  have empty : H = ⊥ := SimpleGraph.eq_bot_iff_forall_not_adj.mpr all
  refine ⟨?_,∅,?_,lower_zero _⟩
  · have zero : H.edgeFinset = ∅ := Finset.not_nonempty_iff_eq_empty.mp (fun he => H.edgeFinset_nonempty.mp he empty)
    have eq : H.edgeFinset.card - 1 = 0 := by simp [zero]
    rw [eq]
    exact lower_zero _
  · exact fun a b ab => (all a b ab).elim

theorem bound_of_counts {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (proof : Counts G)
    (C : PEqualNP.CircuitLowerBounds.Circuit) (ao : IsAO2 n C)
    (h : circuitFun n C = edgeFun G) : ∃ S : Finset (Fin n),
    G.IsVertexCover (S : Set (Fin n)) ∧ G.edgeFinset.card + S.card ≤ C.size + 1 := by
  obtain ⟨orr,S,cv,andd⟩ := proof
  have ol := lower_circuit orr C ao h
  rw [← ordinary_eq] at h
  have al := and_lower_circuit _ ((cover_dual G).symm ▸ andd) C ao h
  rw [← ThetaAnd3241.subtract_or_eq_and C ao] at al
  change G.edgeFinset.card - 1 ≤ C.gates.countP (fun g => PEqualNP.SharedBlockCost.isOrOp g.op) at ol
  have le := List.countP_le_length (p := fun g => PEqualNP.SharedBlockCost.isOrOp g.op) (l := C.gates)
  change _ ≤ C.size at le
  exact ⟨S,cv,by omega⟩

end LeafCore3241

namespace ForestBipartite3241
open LeafCore3241 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm

abbrev bip {n m : Nat} (E : Finset (Fin n × Fin m)) : SimpleGraph (Fin (n+m)) :=
  SimpleGraph.fromRel fun a b => ∃ e ∈ E, a = Fin.castAdd m e.1 ∧ b = Fin.natAdd n e.2

theorem sides {n m : Nat} (a : Fin n) (b : Fin m) : Fin.castAdd m a ≠ Fin.natAdd n b := by
  intro eq
  have h := congrArg Fin.val eq
  change a.val = n + b.val at h
  omega

def pair {n m : Nat} (e : Fin n × Fin m) : Sym2 (Fin (n+m)) :=
  s(Fin.castAdd m e.1,Fin.natAdd n e.2)

theorem injective_pair {n m : Nat} : Function.Injective (pair (n := n) (m := m)) := by
  intro e f eq
  rcases Sym2.eq_iff.mp eq with ⟨a,b⟩ | ⟨a,_⟩
  · exact Prod.ext (Fin.castAdd_injective n m a) (Fin.ext (by
      have h := congrArg Fin.val b
      change n + e.2.val = n + f.2.val at h
      omega))
  · exact (sides _ _ a).elim

theorem bip_adjacency {n m : Nat} {E : Finset (Fin n × Fin m)} {e : Fin n × Fin m} (he : e ∈ E) :
    (bip E).Adj (Fin.castAdd m e.1) (Fin.natAdd n e.2) :=
  ⟨sides _ _,Or.inl ⟨e,he,rfl,rfl⟩⟩

theorem bip_edges {n m : Nat} (E : Finset (Fin n × Fin m)) [DecidableRel (bip E).Adj] :
    (bip E).edgeFinset.card = E.card := by
  have eq : (bip E).edgeFinset = E.image pair := by
    ext t
    induction t using Sym2.inductionOn with
    | _ a b =>
      rw [SimpleGraph.mem_edgeFinset]
      constructor
      · rintro ⟨_,⟨e,he,rfl,rfl⟩ | ⟨e,he,rfl,rfl⟩⟩
        · exact Finset.mem_image.mpr ⟨e,he,rfl⟩
        · exact Finset.mem_image.mpr ⟨e,he,Sym2.eq_swap⟩
      · intro h
        obtain ⟨e,he,eq⟩ := Finset.mem_image.mp h
        rcases Sym2.eq_iff.mp eq with ⟨a,b⟩ | ⟨a,b⟩
        · exact a ▸ b ▸ bip_adjacency he
        · exact a ▸ b ▸ (bip_adjacency he).symm
  rw [eq,Finset.card_image_of_injective _ injective_pair]

theorem formula {n m : Nat} (E : Finset (Fin n × Fin m)) [DecidableRel (bip E).Adj]
    (x : Fin (n+m) → Bool) : edgeFun (bip E) x =
      decide (∃ e ∈ E, x (Fin.castAdd m e.1) = true ∧ x (Fin.natAdd n e.2) = true) := by
  apply Bool.eq_iff_iff.mpr
  simp only [edgeFun,decide_eq_true_eq]
  constructor
  · rintro ⟨a,b,⟨_,⟨e,he,rfl,rfl⟩ | ⟨e,he,rfl,rfl⟩⟩,ha,hb⟩
    · exact ⟨e,he,ha,hb⟩
    · exact ⟨e,he,hb,ha⟩
  · rintro ⟨e,he,l,r⟩
    exact ⟨_,_,bip_adjacency he,l,r⟩

end ForestBipartite3241

namespace CoreTransfer3241
open ThetaPin3241 LeafAnd3241 LeafCore3241

theorem padded {m n : Nat} (G : SimpleGraph (Fin m)) (H : SimpleGraph (Fin n))
    [DecidableRel G.Adj] [DecidableRel H.Adj] (f : Fin m → Fin n) (inj : Function.Injective f)
    (adj : ∀ i j, H.Adj i j ↔ ∃ u v, G.Adj u v ∧ f u = i ∧ f v = j)
    (src : Counts G) : Counts H := by
  classical
  let p : X m → X n := fun x => Function.extend f x (fun _ => false)
  have put (x : X m) (i : Fin m) : p x (f i) = x i := inj.extend_apply x _ i
  have raw : ∀ a ∈ inputs n, Free (inputs m) (a ∘ p) := by
    rintro _ ⟨i,rfl⟩
    by_cases mem : ∃ t, f t = i
    · obtain ⟨t,rfl⟩ := mem
      have eq : (fun (x : X n) => x (f t)) ∘ p = (fun (x : X m) => x t) := funext (fun x => put x t)
      exact eq ▸ atom ⟨t,rfl⟩
    · have eq : (fun (x : X n) => x i) ∘ p = (fun _ => false) :=
        funext (fun x => Function.extend_apply' x (fun _ => false) i mem)
      exact eq ▸ free_zero
  have spec (u v : Fin m) (uv : G.Adj u v) : H.Adj (f u) (f v) := (adj _ _).mpr ⟨u,v,uv,rfl,rfl⟩
  have edge : edgeFun H ∘ p = edgeFun G := by
    funext x
    apply Bool.eq_iff_iff.mpr
    simp only [Function.comp_apply,edgeFun,decide_eq_true_eq]
    constructor
    · rintro ⟨i,j,ij,yes,also⟩
      obtain ⟨u,v,uv,rfl,rfl⟩ := (adj _ _).mp ij
      exact ⟨u,v,uv,(put x u).symm.trans yes,(put x v).symm.trans also⟩
    · rintro ⟨u,v,uv,yes,also⟩
      exact ⟨_,_,spec u v uv,(put x u).trans yes,(put x v).trans also⟩
  have covers : cover H ∘ p = cover G := by
    funext x
    apply Bool.eq_iff_iff.mpr
    simp only [Function.comp_apply,cover,decide_eq_true_eq]
    constructor
    · intro ok u v uv
      simpa only [put] using ok _ _ (spec u v uv)
    · intro ok i j ij
      obtain ⟨u,v,uv,rfl,rfl⟩ := (adj _ _).mp ij
      simpa only [put] using ok _ _ uv
  have subset : H.edgeFinset ⊆ G.edgeFinset.image (Sym2.map f) := by
    intro e
    induction e using Sym2.inductionOn with
    | _ i j =>
      intro he
      obtain ⟨u,v,uv,rfl,rfl⟩ := (adj i j).mp (H.mem_edgeFinset.mp he)
      exact Finset.mem_image.mpr ⟨s(u,v),G.mem_edgeFinset.mpr uv,rfl⟩
  have count := (Finset.card_le_card subset).trans Finset.card_image_le
  obtain ⟨ors,S,cv,ands⟩ := src
  refine ⟨?_,S.image f,?_,?_⟩
  · have lo : Lower (edgeFun H) (G.edgeFinset.card - 1) := lower_transport p raw (edge.symm ▸ ors)
    exact fun gs ok => (Nat.sub_le_sub_right count 1).trans (lo gs ok)
  · intro i j ij
    obtain ⟨u,v,uv,rfl,rfl⟩ := (adj i j).mp ij
    exact (cv uv).imp (fun hu => Finset.mem_image_of_mem _ hu) (fun hv => Finset.mem_image_of_mem _ hv)
  · rw [Finset.card_image_of_injective _ inj]
    exact lower_transport p raw (covers.symm ▸ ands)

theorem pass_of_choices {n : Nat} (gs : List (ThetaPin3241.Gate (X n))) (B : Set (Signal (X n)))
    (f : Signal (X n)) (x y z : X n) (base : ∀ a ∈ B, Pass x y z a)
    (agree : ∀ g ∈ gs, g.1 x = g.1 y) (ok : Valid B gs f) : Pass x y z f := by
  induction gs generalizing B with
  | nil => exact free_pass base ok
  | cons g gs ih =>
    obtain ⟨fa,fb,tail⟩ := ok
    have pass_a := free_pass base fa
    have pass_b := free_pass base fb
    have pass_g : Pass x y z (join g.1 g.2) := by
      have eq := agree g List.mem_cons_self
      intro gx gy
      cases ax : g.1 x with
      | true =>
        have az := pass_a ax (eq.symm.trans ax)
        simp [join,az]
      | false =>
        have ay := eq.symm.trans ax
        have bz := pass_b (by simpa [join,ax] using gx) (by simpa [join,ay] using gy)
        simp [join,bz]
    refine ih (insert (join g.1 g.2) B) ?_ ?_ tail
    · intro a ha
      exact (Set.mem_insert_iff.mp ha).elim (fun eq => eq ▸ pass_g) (base a)
    · exact fun g hg => agree g (List.mem_cons_of_mem _ hg)

theorem separated_rows {n k r : Nat} (f : Signal (X n)) (rows : Fin r → X n)
    (yes : ∀ i, f (rows i) = true)
    (off : ∀ i j, i ≠ j → f (fun v => rows i v && rows j v) = false)
    (many : 2^(k-1) < r) : Lower f k := by
  intro gs ok
  let key (i : Fin r) (g : Fin gs.length) := (gs.get g).1 (rows i)
  have distinguish : Function.Injective key := by
    intro i j eq
    by_contra ne
    have agree (g) (hg : g ∈ gs) : g.1 (rows i) = g.1 (rows j) := by
      obtain ⟨t,rfl⟩ := List.mem_iff_get.mp hg
      exact congrFun eq t
    have pass := pass_of_choices gs (inputs n) f (rows i) (rows j) (fun v => rows i v && rows j v)
      (pass_inputs _ _ _ (fun v a b => by simp [a,b])) agree ok
    have both := pass (yes i) (yes j)
    simp [off i j ne] at both
  have count := Fintype.card_le_of_injective key distinguish
  simp only [Fintype.card_fin,Fintype.card_fun,Fintype.card_bool] at count
  by_contra bad
  have cap := Nat.pow_le_pow_right (by decide : 0 < 2) (show gs.length ≤ k-1 by omega)
  omega

end CoreTransfer3241
end PEqualNP.Outside.L_meta_18065.Census.Core.Ten
namespace PEqualNP.Outside.L_meta_18065.Census.Core.Ten.Split
open ThetaPin3241 ThetaClass3241 CoreTransfer3241

theorem form {n : Nat} {f : Signal (Fin n → Bool)} (hf : Free (inputs n) f) :
    f=(fun _ => false) ∨ f=(fun _ => true) ∨ (∃ i, f=(fun x => x i)) ∨
      ∃ i j : Fin n, i≠j ∧ ∀ x, f x=true → x i=true ∧ x j=true := by
  obtain hf | ⟨fs,mem,rfl⟩ := factors hf
  · exact Or.inl hf
  cases fs with
  | nil => exact Or.inr (Or.inl rfl)
  | cons h hs =>
    obtain ⟨i,hi⟩ := mem h List.mem_cons_self
    by_cases single : ∀ z∈h::hs, z=(fun x => x i)
    · refine Or.inr (Or.inr (Or.inl ⟨i,?_⟩))
      funext x
      apply Bool.eq_iff_iff.mpr
      rw [List.all_eq_true]
      constructor
      · intro a
        simpa only [single h List.mem_cons_self] using a h List.mem_cons_self
      · intro a z hz
        simpa only [single z hz] using a
    · push_neg at single
      obtain ⟨z,hz,diff⟩ := single
      obtain ⟨j,hj⟩ := mem z hz
      refine Or.inr (Or.inr (Or.inr ⟨i,j,?_,?_⟩))
      · rintro rfl
        exact diff hj.symm
      · intro x t
        have yes := List.all_eq_true.mp t
        exact ⟨by simpa only [←hi] using yes h List.mem_cons_self,
               by simpa only [←hj] using yes z hz⟩

theorem branch_bound {n r : Nat} (f : Signal (X n)) (rows : Fin r → X n)
    (yes : ∀ i, f (rows i)=true)
    (off : ∀ i j, i≠j → f (fun v => rows i v && rows j v)=false)
    (g : ThetaPin3241.Gate (X n)) (gs : List (ThetaPin3241.Gate (X n)))
    (ok : Valid (inputs n) (g::gs) f) (bit : Bool) :
    (Finset.univ.filter (fun i => g.1 (rows i)=bit)).card ≤ 2^gs.length := by
  let S := Finset.univ.filter (fun i => g.1 (rows i)=bit)
  let key (i : S) (j : Fin gs.length) := (gs.get j).1 (rows i.val)
  have inj : Function.Injective key := by
    intro i j eq
    apply Subtype.ext
    by_contra ne
    have agree (z) (hz : z∈g::gs) : z.1 (rows i.val)=z.1 (rows j.val) := by
      rcases List.mem_cons.mp hz with rfl|tail
      · exact (Finset.mem_filter.mp i.property).2.trans (Finset.mem_filter.mp j.property).2.symm
      · obtain ⟨k,rfl⟩ := List.mem_iff_get.mp tail
        exact congrFun eq k
    have pass := pass_of_choices (g::gs) (inputs n) f (rows i.val) (rows j.val)
      (fun v => rows i.val v && rows j.val v) (pass_inputs _ _ _ (fun v a b => by simp [a,b])) agree ok
    simpa [off i.val j.val ne] using pass (yes _) (yes _)
  have cost := Fintype.card_le_of_injective key inj
  change S.card ≤ 2 ^ gs.length
  simpa only [Fintype.card_coe, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] using cost

theorem split_lower {n r k : Nat} (f : Signal (X n)) (rows : Fin r → X n)
    (yes : ∀ i, f (rows i)=true)
    (off : ∀ i j, i≠j → f (fun v => rows i v && rows j v)=false)
    (pop : 2^k < r)
    (one : ∀ u, 2^k < (Finset.univ.filter (fun i => rows i u=true)).card)
    (two : ∀ u v, u≠v → 2^k < (Finset.univ.filter (fun i => rows i u=false ∨ rows i v=false)).card) :
    Lower f (k+2) := by
  intro gs ok
  have past : Lower f (k+1) := separated_rows f rows yes off (by simpa using pop)
  cases gs with
  | nil => exact False.elim (by have := past [] ok; simp at this)
  | cons g gs =>
    by_contra lt
    have small : gs.length≤k := by simp at lt; omega
    have price (b) := (branch_bound f rows yes off g gs ok b).trans
      (Nat.pow_le_pow_right (by decide : 0<2) small)
    obtain z|o|⟨u,raw⟩|⟨u,v,ne,imp⟩ := form ok.1
    · have := price false; simp [z] at this; omega
    · have := price true; simp [o] at this; omega
    · have := price true; rw [raw] at this; exact (Nat.not_lt_of_ge this) (one u)
    · have sub : Finset.univ.filter (fun i => rows i u=false ∨ rows i v=false) ⊆
          Finset.univ.filter (fun i => g.1 (rows i)=false) := by
        intro i hi
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _,Bool.eq_false_iff.mpr ?_⟩
        intro q
        obtain ⟨a,b⟩ := imp (rows i) q
        rcases (Finset.mem_filter.mp hi).2 with h | h <;> simp_all
      exact (Nat.not_lt_of_ge ((Finset.card_le_card sub).trans (price false))) (two u v ne)

end PEqualNP.Outside.L_meta_18065.Census.Core.Ten.Split

namespace PEqualNP.Outside.L_meta_18065.Census.Core.Ten.Split
open ThetaPin3241 ThetaClass3241 ThetaAnd3241 LeafAnd3241 LeafCore3241 CoreTransfer3241
def masks : Fin 29 → Nat := ![2730,2733,1707,1709,3498,1451,1453,2922,2925,3434,1387,1389,2778,1755,2906,3418,1371,2742,2741,1717,3510,1461,2774,2773,1749,2902,2901,3414,1365]
def cyc (x : Fin 12 → Bool) : Bool := (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6) || (x 6 && x 7) || (x 7 && x 8) || (x 8 && x 9) || (x 9 && x 10) || (x 10 && x 11) || (x 11 && x 0)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem sixDual : Lower (dual cyc) 6 := by
  apply split_lower (k:=4) (dual cyc) (fun i => ThetaCores3241.row (masks i))
  · decide +kernel
  · decide +kernel
  · decide
  · decide +kernel
  · decide +kernel
def pth2 (x : Fin 2 → Bool) : Bool := (x 0 && x 1)
theorem pth2Low : Lower pth2 0 := lower_zero _
def pth3 (x : Fin 3 → Bool) : Bool := (x 0 && x 1) || (x 1 && x 2)
theorem pth3Low : Lower pth3 1 := by
  have equal : pth3 ∘ pin (2 : Fin 3) = pth2 := by
    funext x
    change ((x 0 && x 1) || (x 1 && false)) = _
    simp [pth2]
  apply lower_one_step pth3 (2 : Fin 3) (ThetaCores3241.row 6) (ThetaCores3241.row 2)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact equal.symm ▸ pth2Low
def pth4 (x : Fin 4 → Bool) : Bool := (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3)
theorem pth4Low : Lower pth4 2 := by
  have equal : pth4 ∘ pin (3 : Fin 4) = pth3 := by
    funext x
    change ((x 0 && x 1) || (x 1 && x 2) || (x 2 && false)) = _
    simp [pth3]
  apply lower_one_step pth4 (3 : Fin 4) (ThetaCores3241.row 12) (ThetaCores3241.row 4)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact equal.symm ▸ pth3Low
def pth5 (x : Fin 5 → Bool) : Bool := (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4)
theorem pth5Low : Lower pth5 3 := by
  have equal : pth5 ∘ pin (4 : Fin 5) = pth4 := by
    funext x
    change ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && false)) = _
    simp [pth4]
  apply lower_one_step pth5 (4 : Fin 5) (ThetaCores3241.row 24) (ThetaCores3241.row 8)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact equal.symm ▸ pth4Low
def pth6 (x : Fin 6 → Bool) : Bool := (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5)
theorem pth6Low : Lower pth6 4 := by
  have equal : pth6 ∘ pin (5 : Fin 6) = pth5 := by
    funext x
    change ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && false)) = _
    simp [pth5]
  apply lower_one_step pth6 (5 : Fin 6) (ThetaCores3241.row 48) (ThetaCores3241.row 16)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact equal.symm ▸ pth5Low
def pth7 (x : Fin 7 → Bool) : Bool := (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6)
theorem pth7Low : Lower pth7 5 := by
  have equal : pth7 ∘ pin (6 : Fin 7) = pth6 := by
    funext x
    change ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && false)) = _
    simp [pth6]
  apply lower_one_step pth7 (6 : Fin 7) (ThetaCores3241.row 96) (ThetaCores3241.row 32)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact equal.symm ▸ pth6Low
def pth8 (x : Fin 8 → Bool) : Bool := (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6) || (x 6 && x 7)
theorem pth8Low : Lower pth8 6 := by
  have equal : pth8 ∘ pin (7 : Fin 8) = pth7 := by
    funext x
    change ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6) || (x 6 && false)) = _
    simp [pth7]
  apply lower_one_step pth8 (7 : Fin 8) (ThetaCores3241.row 192) (ThetaCores3241.row 64)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact equal.symm ▸ pth7Low
def pth9 (x : Fin 9 → Bool) : Bool := (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6) || (x 6 && x 7) || (x 7 && x 8)
theorem pth9Low : Lower pth9 7 := by
  have equal : pth9 ∘ pin (8 : Fin 9) = pth8 := by
    funext x
    change ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6) || (x 6 && x 7) || (x 7 && false)) = _
    simp [pth8]
  apply lower_one_step pth9 (8 : Fin 9) (ThetaCores3241.row 384) (ThetaCores3241.row 128)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact equal.symm ▸ pth8Low
def pth10 (x : Fin 10 → Bool) : Bool := (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6) || (x 6 && x 7) || (x 7 && x 8) || (x 8 && x 9)
theorem pth10Low : Lower pth10 8 := by
  have equal : pth10 ∘ pin (9 : Fin 10) = pth9 := by
    funext x
    change ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6) || (x 6 && x 7) || (x 7 && x 8) || (x 8 && false)) = _
    simp [pth9]
  apply lower_one_step pth10 (9 : Fin 10) (ThetaCores3241.row 768) (ThetaCores3241.row 256)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact equal.symm ▸ pth9Low
def pth11 (x : Fin 11 → Bool) : Bool := (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6) || (x 6 && x 7) || (x 7 && x 8) || (x 8 && x 9) || (x 9 && x 10)
theorem pth11Low : Lower pth11 9 := by
  have equal : pth11 ∘ pin (10 : Fin 11) = pth10 := by
    funext x
    change ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6) || (x 6 && x 7) || (x 7 && x 8) || (x 8 && x 9) || (x 9 && false)) = _
    simp [pth10]
  apply lower_one_step pth11 (10 : Fin 11) (ThetaCores3241.row 1536) (ThetaCores3241.row 512)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact equal.symm ▸ pth10Low
def ren : Fin 12 → Fin 11 → Fin 11 := ![![0,1,2,3,4,5,6,7,8,9,10],![10,0,1,2,3,4,5,6,7,8,9],![9,10,0,1,2,3,4,5,6,7,8],![8,9,10,0,1,2,3,4,5,6,7],![7,8,9,10,0,1,2,3,4,5,6],![6,7,8,9,10,0,1,2,3,4,5],![5,6,7,8,9,10,0,1,2,3,4],![4,5,6,7,8,9,10,0,1,2,3],![3,4,5,6,7,8,9,10,0,1,2],![2,3,4,5,6,7,8,9,10,0,1],![1,2,3,4,5,6,7,8,9,10,0],![0,1,2,3,4,5,6,7,8,9,10]]
private theorem cut0 (x : Fin 11 → Bool) : (cyc ∘ pin (0 : Fin 12)) (x ∘ ren 0) = pth11 x := by
  change ((false && x 0) || (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6) || (x 6 && x 7) || (x 7 && x 8) || (x 8 && x 9) || (x 9 && x 10) || (x 10 && false)) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6) || (x 6 && x 7) || (x 7 && x 8) || (x 8 && x 9) || (x 9 && x 10))
  simp only [Bool.false_and,Bool.and_false,Bool.false_or,Bool.or_false,Bool.or_assoc,Bool.or_left_comm,Bool.or_comm]
private theorem cut1 (x : Fin 11 → Bool) : (cyc ∘ pin (1 : Fin 12)) (x ∘ ren 1) = pth11 x := by
  change ((x 10 && false) || (false && x 0) || (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6) || (x 6 && x 7) || (x 7 && x 8) || (x 8 && x 9) || (x 9 && x 10)) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6) || (x 6 && x 7) || (x 7 && x 8) || (x 8 && x 9) || (x 9 && x 10))
  simp only [Bool.false_and,Bool.and_false,Bool.false_or,Bool.or_false,Bool.or_assoc,Bool.or_left_comm,Bool.or_comm]
private theorem cut2 (x : Fin 11 → Bool) : (cyc ∘ pin (2 : Fin 12)) (x ∘ ren 2) = pth11 x := by
  change ((x 9 && x 10) || (x 10 && false) || (false && x 0) || (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6) || (x 6 && x 7) || (x 7 && x 8) || (x 8 && x 9)) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6) || (x 6 && x 7) || (x 7 && x 8) || (x 8 && x 9) || (x 9 && x 10))
  simp only [Bool.false_and,Bool.and_false,Bool.false_or,Bool.or_false,Bool.or_assoc,Bool.or_left_comm,Bool.or_comm]
private theorem cut3 (x : Fin 11 → Bool) : (cyc ∘ pin (3 : Fin 12)) (x ∘ ren 3) = pth11 x := by
  change ((x 8 && x 9) || (x 9 && x 10) || (x 10 && false) || (false && x 0) || (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6) || (x 6 && x 7) || (x 7 && x 8)) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6) || (x 6 && x 7) || (x 7 && x 8) || (x 8 && x 9) || (x 9 && x 10))
  simp only [Bool.false_and,Bool.and_false,Bool.false_or,Bool.or_false,Bool.or_assoc,Bool.or_left_comm,Bool.or_comm]
private theorem cut4 (x : Fin 11 → Bool) : (cyc ∘ pin (4 : Fin 12)) (x ∘ ren 4) = pth11 x := by
  change ((x 7 && x 8) || (x 8 && x 9) || (x 9 && x 10) || (x 10 && false) || (false && x 0) || (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6) || (x 6 && x 7)) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6) || (x 6 && x 7) || (x 7 && x 8) || (x 8 && x 9) || (x 9 && x 10))
  simp only [Bool.false_and,Bool.and_false,Bool.false_or,Bool.or_false,Bool.or_assoc,Bool.or_left_comm,Bool.or_comm]
private theorem cut5 (x : Fin 11 → Bool) : (cyc ∘ pin (5 : Fin 12)) (x ∘ ren 5) = pth11 x := by
  change ((x 6 && x 7) || (x 7 && x 8) || (x 8 && x 9) || (x 9 && x 10) || (x 10 && false) || (false && x 0) || (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6)) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6) || (x 6 && x 7) || (x 7 && x 8) || (x 8 && x 9) || (x 9 && x 10))
  simp only [Bool.false_and,Bool.and_false,Bool.false_or,Bool.or_false,Bool.or_assoc,Bool.or_left_comm,Bool.or_comm]
private theorem cut6 (x : Fin 11 → Bool) : (cyc ∘ pin (6 : Fin 12)) (x ∘ ren 6) = pth11 x := by
  change ((x 5 && x 6) || (x 6 && x 7) || (x 7 && x 8) || (x 8 && x 9) || (x 9 && x 10) || (x 10 && false) || (false && x 0) || (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5)) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6) || (x 6 && x 7) || (x 7 && x 8) || (x 8 && x 9) || (x 9 && x 10))
  simp only [Bool.false_and,Bool.and_false,Bool.false_or,Bool.or_false,Bool.or_assoc,Bool.or_left_comm,Bool.or_comm]
private theorem cut7 (x : Fin 11 → Bool) : (cyc ∘ pin (7 : Fin 12)) (x ∘ ren 7) = pth11 x := by
  change ((x 4 && x 5) || (x 5 && x 6) || (x 6 && x 7) || (x 7 && x 8) || (x 8 && x 9) || (x 9 && x 10) || (x 10 && false) || (false && x 0) || (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4)) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6) || (x 6 && x 7) || (x 7 && x 8) || (x 8 && x 9) || (x 9 && x 10))
  simp only [Bool.false_and,Bool.and_false,Bool.false_or,Bool.or_false,Bool.or_assoc,Bool.or_left_comm,Bool.or_comm]
private theorem cut8 (x : Fin 11 → Bool) : (cyc ∘ pin (8 : Fin 12)) (x ∘ ren 8) = pth11 x := by
  change ((x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6) || (x 6 && x 7) || (x 7 && x 8) || (x 8 && x 9) || (x 9 && x 10) || (x 10 && false) || (false && x 0) || (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3)) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6) || (x 6 && x 7) || (x 7 && x 8) || (x 8 && x 9) || (x 9 && x 10))
  simp only [Bool.false_and,Bool.and_false,Bool.false_or,Bool.or_false,Bool.or_assoc,Bool.or_left_comm,Bool.or_comm]
private theorem cut9 (x : Fin 11 → Bool) : (cyc ∘ pin (9 : Fin 12)) (x ∘ ren 9) = pth11 x := by
  change ((x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6) || (x 6 && x 7) || (x 7 && x 8) || (x 8 && x 9) || (x 9 && x 10) || (x 10 && false) || (false && x 0) || (x 0 && x 1) || (x 1 && x 2)) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6) || (x 6 && x 7) || (x 7 && x 8) || (x 8 && x 9) || (x 9 && x 10))
  simp only [Bool.false_and,Bool.and_false,Bool.false_or,Bool.or_false,Bool.or_assoc,Bool.or_left_comm,Bool.or_comm]
private theorem cut10 (x : Fin 11 → Bool) : (cyc ∘ pin (10 : Fin 12)) (x ∘ ren 10) = pth11 x := by
  change ((x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6) || (x 6 && x 7) || (x 7 && x 8) || (x 8 && x 9) || (x 9 && x 10) || (x 10 && false) || (false && x 0) || (x 0 && x 1)) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6) || (x 6 && x 7) || (x 7 && x 8) || (x 8 && x 9) || (x 9 && x 10))
  simp only [Bool.false_and,Bool.and_false,Bool.false_or,Bool.or_false,Bool.or_assoc,Bool.or_left_comm,Bool.or_comm]
private theorem cut11 (x : Fin 11 → Bool) : (cyc ∘ pin (11 : Fin 12)) (x ∘ ren 11) = pth11 x := by
  change ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6) || (x 6 && x 7) || (x 7 && x 8) || (x 8 && x 9) || (x 9 && x 10) || (x 10 && false) || (false && x 0)) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6) || (x 6 && x 7) || (x 7 && x 8) || (x 8 && x 9) || (x 9 && x 10))
  simp only [Bool.false_and,Bool.and_false,Bool.false_or,Bool.or_false,Bool.or_assoc,Bool.or_left_comm,Bool.or_comm]
theorem deleted (v : Fin 12) : Lower (cyc ∘ pin v) 9 := by
  apply lower_rename (ren v)
  have eq : (fun x => (cyc ∘ pin v) (x ∘ ren v)) = pth11 := by
    funext x
    fin_cases v
    · exact cut0 x
    · exact cut1 x
    · exact cut2 x
    · exact cut3 x
    · exact cut4 x
    · exact cut5 x
    · exact cut6 x
    · exact cut7 x
    · exact cut8 x
    · exact cut9 x
    · exact cut10 x
    · exact cut11 x
  exact eq.symm ▸ pth11Low

set_option maxRecDepth 16000 in
set_option maxHeartbeats 2000000 in
theorem cycleGeometry : Geometry (∅ : Finset (Fin 12)) cyc := by
  constructor <;> decide +kernel

theorem elevenOr : Lower cyc 11 := by
  apply lower_two_step cyc Set.univ (pool ∅) (base_subset _)
  · exact nonfree cyc ∅ (bits {0,1}) (bits {2,3}) (bits ∅)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro g a b h
    exact classify cycleGeometry g a b (fun v _ => h v (Set.mem_univ v))
  · exact fun v _ => deleted v

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity in
theorem cycleTwelvePrice (C : Circuit) (ao : IsAO2 12 C) (ev : circuitFun 12 C=cyc) :
    11 ≤ C.gates.countP (fun g => PEqualNP.SharedBlockCost.isOrOp g.op) ∧
    6 ≤ C.gates.countP ThetaAnd3241.andGate ∧ 17 ≤ C.size := by
  have a := lower_circuit elevenOr C ao ev
  have b := and_lower_circuit _ sixDual C ao ev
  refine ⟨a,b,?_⟩
  rw [← ThetaAnd3241.subtract_or_eq_and C ao] at b
  change 11 ≤ C.gates.countP (fun g => PEqualNP.SharedBlockCost.isOrOp g.op) at a
  omega

end PEqualNP.Outside.L_meta_18065.Census.Core.Ten.Split

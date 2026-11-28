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

namespace SmallCores3241
open ThetaPin3241 LeafAnd3241 LeafCore3241 CoreTransfer3241
open ThetaCores3241 Theta244Cores ThetaClass3241

set_option maxRecDepth 30000 in
set_option maxHeartbeats 10000000 in
def path8 (x : LeafAnd3241.X 8) : Bool := (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6) || (x 6 && x 7)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 10000000 in
theorem path8_lower (rec : Lower path7 5) : Lower path8 6 := by
  have eq : path8 ∘ pin (7 : Fin 8) = path7 := by
    funext x
    exact (by decide +kernel : ∀ y, path8 (pin (7 : Fin 8) y) = path7 y) x
  apply lower_one_step path8 7 (row 192) (row 64)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact eq.symm ▸ rec

set_option maxRecDepth 30000 in
set_option maxHeartbeats 10000000 in
def path9 (x : LeafAnd3241.X 9) : Bool := (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6) || (x 6 && x 7) || (x 7 && x 8)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 10000000 in
theorem path9_lower (rec : Lower path8 6) : Lower path9 7 := by
  have eq : path9 ∘ pin (8 : Fin 9) = path8 := by
    funext x
    exact (by decide +kernel : ∀ y, path9 (pin (8 : Fin 9) y) = path8 y) x
  apply lower_one_step path9 8 (row 384) (row 128)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact eq.symm ▸ rec

set_option maxRecDepth 30000 in
set_option maxHeartbeats 10000000 in
def cycle10 (x : LeafAnd3241.X 10) : Bool := (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6) || (x 6 && x 7) || (x 7 && x 8) || (x 8 && x 9) || (x 9 && x 0)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 10000000 in
def cycleRename : Fin 10 → Fin 9 → Fin 9 := ![![0,1,2,3,4,5,6,7,8],![8,0,1,2,3,4,5,6,7],![7,8,0,1,2,3,4,5,6],![6,7,8,0,1,2,3,4,5],![5,6,7,8,0,1,2,3,4],![4,5,6,7,8,0,1,2,3],![3,4,5,6,7,8,0,1,2],![2,3,4,5,6,7,8,0,1],![1,2,3,4,5,6,7,8,0],![0,1,2,3,4,5,6,7,8]]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 10000000 in
theorem cycle10_deleted (v : Fin 10) : Lower (cycle10 ∘ pin v) 7 := by
  have all : ∀ i x, (cycle10 ∘ pin i) (x ∘ cycleRename i) = path9 x := by decide +kernel
  apply lower_rename (cycleRename v)
  have eq : (fun x => (cycle10 ∘ pin v) (x ∘ cycleRename v)) = path9 := funext (all v)
  exact eq.symm ▸ path9_lower (path8_lower (path7_lower (path6_lower path5_lower)))

set_option maxRecDepth 30000 in
set_option maxHeartbeats 10000000 in
theorem cycle10_geometry : Geometry ∅ cycle10 := by constructor <;> decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 10000000 in
theorem cycle10_lower : Lower cycle10 9 := by
  apply lower_two_step cycle10 Set.univ (pool ∅) (base_subset _)
  · exact nonfree cycle10 ∅ (bits {0,1}) (bits {2,3}) (bits ∅)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro g a b h
    exact classify cycle10_geometry g a b (fun v _ => h v (Set.mem_univ v))
  · exact fun v _ => cycle10_deleted v

set_option maxRecDepth 30000 in
set_option maxHeartbeats 10000000 in
abbrev graph (n : Nat) (edges : List (Nat × Nat)) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel (fun (i j : Fin n) => (i.val,j.val) ∈ edges)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 10000000 in
abbrev six := graph 6 [(0,1),(1,2),(2,3),(3,4),(4,5),(5,0)]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 10000000 in
def sixRows : Fin 5 → Nat := ![21,27,42,45,54]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 10000000 in
theorem sixCounts : Counts six := by
  have eq : edgeFun six = cycle6 := by
    funext x
    exact (by decide +kernel : ∀ y, edgeFun six y = cycle6 y) x
  have card : six.edgeFinset.card - 1 = 5 := by decide +kernel
  constructor
  · rw [eq,card]
    exact cycle6_of_classifier ThetaClass3241.cycle_classifier
  · let S : Finset (Fin 6) := {0,2,4}
    refine ⟨S,?_,?_⟩
    · exact (by decide +kernel : ∀ a b, six.Adj a b → a ∈ ({0,2,4} : Finset (Fin 6)) ∨ b ∈ ({0,2,4} : Finset (Fin 6)))
    have sc : S.card = 3 := by decide +kernel
    have dualEq : cover six = dual cycle6 := by rw [← cover_dual,ordinary_eq,eq]
    rw [sc,dualEq]
    apply separated_rows (dual cycle6) (fun i => row (sixRows i))
    · decide +kernel
    · decide +kernel
    · decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 10000000 in
abbrev eight := graph 8 [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,0)]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 10000000 in
def eightRows : Fin 9 → Nat := ![85,91,107,109,170,173,181,182,214]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 10000000 in
theorem eightCounts : Counts eight := by
  have eq : edgeFun eight = cycle8 := by
    funext x
    exact (by decide +kernel : ∀ y, edgeFun eight y = cycle8 y) x
  have card : eight.edgeFinset.card - 1 = 7 := by decide +kernel
  constructor
  · rw [eq,card]
    exact cycle8_of_classifier Theta244Finish.cycle_classifier
  · let S : Finset (Fin 8) := {0,2,4,6}
    refine ⟨S,?_,?_⟩
    · exact (by decide +kernel : ∀ a b, eight.Adj a b → a ∈ ({0,2,4,6} : Finset (Fin 8)) ∨ b ∈ ({0,2,4,6} : Finset (Fin 8)))
    have sc : S.card = 4 := by decide +kernel
    have dualEq : cover eight = dual cycle8 := by rw [← cover_dual,ordinary_eq,eq]
    rw [sc,dualEq]
    apply separated_rows (dual cycle8) (fun i => row (eightRows i))
    · decide +kernel
    · decide +kernel
    · decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 10000000 in
abbrev ten := graph 10 [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,0)]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 10000000 in
def tenRows : Fin 17 → Nat := ![341,347,363,365,427,429,437,682,685,693,694,725,726,730,854,858,874]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 10000000 in
theorem tenCounts : Counts ten := by
  have eq : edgeFun ten = cycle10 := by
    funext x
    exact (by decide +kernel : ∀ y, edgeFun ten y = cycle10 y) x
  have card : ten.edgeFinset.card - 1 = 9 := by decide +kernel
  constructor
  · rw [eq,card]
    exact cycle10_lower
  · let S : Finset (Fin 10) := {0,2,4,6,8}
    refine ⟨S,?_,?_⟩
    · exact (by decide +kernel : ∀ a b, ten.Adj a b → a ∈ ({0,2,4,6,8} : Finset (Fin 10)) ∨ b ∈ ({0,2,4,6,8} : Finset (Fin 10)))
    have sc : S.card = 5 := by decide +kernel
    have dualEq : cover ten = dual cycle10 := by rw [← cover_dual,ordinary_eq,eq]
    rw [sc,dualEq]
    apply separated_rows (dual cycle10) (fun i => row (tenRows i))
    · decide +kernel
    · decide +kernel
    · decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 10000000 in
abbrev threeThreeThree := graph 8 [(0,5),(0,6),(0,7),(1,4),(1,7),(2,4),(2,6),(3,4),(3,5)]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 10000000 in
def threeThreeThreeRows : Fin 9 → Nat := ![15,55,91,115,157,181,217,238,240]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 10000000 in
theorem threeThreeThreeCounts : Counts threeThreeThree := by
  have eq : edgeFun threeThreeThree = ThetaAnd3241.theta := by
    funext x
    exact (by decide +kernel : ∀ y, edgeFun threeThreeThree y = ThetaAnd3241.theta y) x
  have card : threeThreeThree.edgeFinset.card - 1 = 8 := by decide +kernel
  constructor
  · rw [eq,card]
    exact theta_of_classifiers ThetaClass3241.cycle_classifier theta_classifier
  · let S : Finset (Fin 8) := {0,1,2,3}
    refine ⟨S,?_,?_⟩
    · exact (by decide +kernel : ∀ a b, threeThreeThree.Adj a b → a ∈ ({0,1,2,3} : Finset (Fin 8)) ∨ b ∈ ({0,1,2,3} : Finset (Fin 8)))
    have sc : S.card = 4 := by decide +kernel
    have dualEq : cover threeThreeThree = dual ThetaAnd3241.theta := by rw [← cover_dual,ordinary_eq,eq]
    rw [sc,dualEq]
    apply separated_rows (dual ThetaAnd3241.theta) (fun i => row (threeThreeThreeRows i))
    · decide +kernel
    · decide +kernel
    · decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 10000000 in
abbrev twoFourFour := graph 9 [(0,2),(1,2),(0,3),(3,4),(4,5),(1,5),(0,6),(6,7),(7,8),(1,8)]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 10000000 in
def twoFourFourRows : Fin 9 → Nat := ![147,171,222,238,339,350,363,364,373]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 10000000 in
theorem twoFourFourCounts (extra : Lower Theta244Cores.theta 9) : Counts twoFourFour := by
  have eq : edgeFun twoFourFour = Theta244Cores.theta := by
    funext x
    exact (by decide +kernel : ∀ y, edgeFun twoFourFour y = Theta244Cores.theta y) x
  have card : twoFourFour.edgeFinset.card - 1 = 9 := by decide +kernel
  constructor
  · rw [eq,card]
    exact extra
  · let S : Finset (Fin 9) := {0,1,4,7}
    refine ⟨S,?_,?_⟩
    · exact (by decide +kernel : ∀ a b, twoFourFour.Adj a b → a ∈ ({0,1,4,7} : Finset (Fin 9)) ∨ b ∈ ({0,1,4,7} : Finset (Fin 9)))
    have sc : S.card = 4 := by decide +kernel
    have dualEq : cover twoFourFour = dual Theta244Cores.theta := by rw [← cover_dual,ordinary_eq,eq]
    rw [sc,dualEq]
    apply separated_rows (dual Theta244Cores.theta) (fun i => row (twoFourFourRows i))
    · decide +kernel
    · decide +kernel
    · decide +kernel

end SmallCores3241

namespace GraphPacking3241
open ThetaPin3241 LeafAnd3241 LeafCore3241 ForestBipartite3241

abbrev Matrix (n m : Nat) := Finset (Fin n × Fin m)
abbrev Left {n m : Nat} (a : Fin n) := Fin.castAdd m a
abbrev Right {n m : Nat} (b : Fin m) := Fin.natAdd n b

def FourFree {n m : Nat} (E : Matrix n m) : Prop :=
  ∀ p q l s, p ≠ q → l ≠ s → ¬((p,l) ∈ E ∧ (p,s) ∈ E ∧ (q,l) ∈ E ∧ (q,s) ∈ E)

def HasPartners {n m : Nat} (E : Matrix n m) : Prop :=
  ∀ a b, (a,b) ∈ E →
    (∃ c, c ≠ b ∧ (a,c) ∈ E) ∧ (∃ d, d ≠ a ∧ (d,b) ∈ E)

theorem adj_left {n m : Nat} (E : Matrix n m) (a : Fin n) (j : Fin (n+m)) :
    (bip E).Adj (Left a) j ↔ ∃ b, (a,b) ∈ E ∧ j = Right b := by
  constructor
  · rintro ⟨_,⟨e,he,eq,rfl⟩ | ⟨e,_,_,eq⟩⟩
    · have ea : a = e.1 := Fin.castAdd_injective n m eq
      exact ⟨e.2,ea ▸ he,rfl⟩
    · exact (sides _ _ eq).elim
  · rintro ⟨b,h,rfl⟩
    exact bip_adjacency h

theorem adj_right {n m : Nat} (E : Matrix n m) (b : Fin m) (i : Fin (n+m)) :
    (bip E).Adj (Right b) i ↔ ∃ a, (a,b) ∈ E ∧ i = Left a := by
  constructor
  · rintro ⟨_,⟨e,_,eq,_⟩ | ⟨e,he,rfl,eq⟩⟩
    · exact (sides _ _ eq.symm).elim
    · have eb : b = e.2 := Fin.natAdd_injective m n eq
      exact ⟨e.1,eb ▸ he,rfl⟩
  · rintro ⟨a,h,rfl⟩
    exact (bip_adjacency h).symm

theorem leafless_iff {n m : Nat} (E : Matrix n m) : Leafless (bip E) ↔ HasPartners E := by
  classical
  constructor
  · intro no a b ab
    constructor
    · by_contra! bad
      apply no
      refine ⟨Left a,Right b,bip_adjacency ab,?_⟩
      intro i hi
      obtain ⟨c,hc,rfl⟩ := (adj_left E a i).mp hi
      have cb : c = b := by_contra (fun ne => bad c ne hc)
      rw [cb]
    · by_contra! bad
      apply no
      refine ⟨Right b,Left a,(bip_adjacency ab).symm,?_⟩
      intro i hi
      obtain ⟨d,hd,rfl⟩ := (adj_right E b i).mp hi
      have da : d = a := by_contra (fun ne => bad d ne hd)
      rw [da]
  · rintro partners ⟨i,j,ij,leaf⟩
    rcases ij with ⟨_,⟨⟨a,b⟩,h,rfl,rfl⟩ | ⟨⟨a,b⟩,h,rfl,rfl⟩⟩
    · obtain ⟨c,ne,hc⟩ := (partners a b h).1
      exact ne (Fin.natAdd_injective m n (leaf _ (bip_adjacency hc)))
    · obtain ⟨d,ne,hd⟩ := (partners a b h).2
      exact ne (Fin.castAdd_injective n m (leaf _ (bip_adjacency hd).symm))

theorem side_count {α β : Type} [DecidableEq α] [DecidableEq β] (E : Finset (α × β))
    (two : ∀ a b, (a,b) ∈ E → ∃ c, c ≠ b ∧ (a,c) ∈ E) :
    (E.image Prod.fst).card * 2 ≤ E.card := by
  classical
  let P := E.image Prod.fst
  have picks (p : P) : ∃ b c, b ≠ c ∧ (p.val,b) ∈ E ∧ (p.val,c) ∈ E := by
    obtain ⟨⟨a,b⟩,ab,e⟩ := Finset.mem_image.mp p.property
    change a = p.val at e
    obtain ⟨c,ne,ac⟩ := two a b ab
    exact ⟨b,c,ne.symm,e ▸ ab,e ▸ ac⟩
  choose first second diff one two using picks
  let edge (p : P) (b : Bool) : E := if b then ⟨(p.val,first p),one p⟩ else ⟨(p.val,second p),two p⟩
  have inj : Function.Injective (fun x : P × Bool => edge x.1 x.2) := by
    rintro ⟨p,i⟩ ⟨q,j⟩ eq
    have row (r : P) (b : Bool) : (edge r b).val.1 = r.val := by cases b <;> rfl
    have pe : p = q := Subtype.ext ((row p i).symm.trans ((congrArg (fun t : E => t.val.1) eq).trans (row q j)))
    subst q
    cases i <;> cases j
    · rfl
    · exact ((diff p).symm (congrArg (fun t : E => t.val.2) eq)).elim
    · exact (diff p (congrArg (fun t : E => t.val.2) eq)).elim
    · rfl
  have bound := Fintype.card_le_of_injective _ inj
  simpa [P] using bound

theorem both_sides {n m : Nat} (E : Matrix n m) (partners : HasPartners E) (small : E.card ≤ 10) :
    (E.image Prod.fst).card ≤ 5 ∧ (E.image Prod.snd).card ≤ 5 := by
  have left := side_count E (fun a b ab => (partners a b ab).1)
  have flip {a : Fin n} {b : Fin m} : (b,a) ∈ E.image Prod.swap ↔ (a,b) ∈ E := by
    constructor
    · rintro h
      obtain ⟨⟨p,q⟩,pq,eq⟩ := Finset.mem_image.mp h
      cases eq
      exact pq
    · exact fun h => Finset.mem_image_of_mem Prod.swap h
  have right := side_count (E.image Prod.swap) (fun b a ba => by
    obtain ⟨d,ne,db⟩ := (partners a b (flip.mp ba)).2
    exact ⟨d,ne,flip.mpr db⟩)
  rw [Finset.image_image,Finset.card_image_of_injective _ Prod.swap_injective] at right
  change (E.image Prod.snd).card * 2 ≤ E.card at right
  omega

theorem from_index {n k : Nat} (G : SimpleGraph (Fin n)) (H : SimpleGraph (Fin k))
    [DecidableRel G.Adj] [DecidableRel H.Adj] (lab : Fin n → Option (Fin k))
    (unique : ∀ i j a, lab i = some a → lab j = some a → i = j)
    (forward : ∀ i j, G.Adj i j → ∃ a b, lab i = some a ∧ lab j = some b ∧ H.Adj a b)
    (back : ∀ a b, H.Adj a b → ∃ i j, lab i = some a ∧ lab j = some b ∧ G.Adj i j)
    (size : G.edgeFinset.card ≤ H.edgeFinset.card) (h : Counts H) : Counts G := by
  classical
  let p : X k → X n := fun x i => (lab i).elim false x
  have read (x : X k) (i a) (hi : lab i = some a) : p x i = x a := by simp [p,hi]
  have raw : ∀ t ∈ inputs n, Free (inputs k) (t ∘ p) := by
    rintro _ ⟨i,rfl⟩
    cases hi : lab i with
    | none => simpa [Function.comp_def,p,hi] using (free_zero (B := inputs k))
    | some a => simpa [Function.comp_def,p,hi] using (atom (B := inputs k) ⟨a,rfl⟩)
  have edge : edgeFun G ∘ p = edgeFun H := by
    funext x
    apply Bool.eq_iff_iff.mpr
    simp only [Function.comp_apply,edgeFun,decide_eq_true_eq]
    constructor
    · rintro ⟨i,j,ij,pi,pj⟩
      obtain ⟨a,b,li,lj,ab⟩ := forward i j ij
      exact ⟨a,b,ab,(read x i a li).symm.trans pi,(read x j b lj).symm.trans pj⟩
    · rintro ⟨a,b,ab,pa,pb⟩
      obtain ⟨i,j,li,lj,ij⟩ := back a b ab
      exact ⟨i,j,ij,(read x i a li).trans pa,(read x j b lj).trans pb⟩
  have cover_eq : cover G ∘ p = cover H := by
    funext x
    apply Bool.eq_iff_iff.mpr
    simp only [Function.comp_apply,cover,decide_eq_true_eq]
    constructor
    · intro ok a b ab
      obtain ⟨i,j,li,lj,ij⟩ := back a b ab
      simpa only [read x i a li,read x j b lj] using ok i j ij
    · intro ok i j ij
      obtain ⟨a,b,li,lj,ab⟩ := forward i j ij
      simpa only [read x i a li,read x j b lj] using ok a b ab
  obtain ⟨ors,S,cv,ands⟩ := h
  let T := Finset.univ.filter fun i => ∃ a ∈ S, lab i = some a
  have lift (i : T) : ∃ a : S, lab i.val = some a.val := by
    obtain ⟨a,ha,eq⟩ := (Finset.mem_filter.mp i.property).2
    exact ⟨⟨a,ha⟩,eq⟩
  choose assign spec using lift
  have inj : Function.Injective assign := fun i j eq =>
    Subtype.ext (unique _ _ _ (spec i) (eq ▸ spec j))
  have card : T.card ≤ S.card := by simpa using Fintype.card_le_of_injective _ inj
  refine ⟨?_,T,?_,?_⟩
  · have bound : Lower (edgeFun G) (H.edgeFinset.card-1) := lower_transport p raw (edge.symm ▸ ors)
    exact fun gs val => (Nat.sub_le_sub_right size 1).trans (bound gs val)
  · intro i j ij
    obtain ⟨a,b,li,lj,ab⟩ := forward i j ij
    exact (cv ab).imp (fun mem => Finset.mem_filter.mpr ⟨Finset.mem_univ _,a,mem,li⟩)
      (fun mem => Finset.mem_filter.mpr ⟨Finset.mem_univ _,b,mem,lj⟩)
  · have bound : Lower (cover G) S.card := lower_transport p raw (cover_eq.symm ▸ ands)
    exact fun gs val => card.trans (bound gs val)

end GraphPacking3241

namespace MatrixPacking3241
open GraphPacking3241 LeafCore3241 ForestBipartite3241

def optional {α β : Type} [DecidableEq α] (P : Finset α) (f : P → β) (i : α) : Option β :=
  if h : i ∈ P then some (f ⟨i,h⟩) else none

theorem optional_unique {α β : Type} [DecidableEq α] (P : Finset α) (f : P → β)
    (inj : Function.Injective f) (i j : α) (a : β) (hi : optional P f i = some a)
    (hj : optional P f j = some a) : i = j := by
  unfold optional at hi hj
  split at hi <;> rename_i pi
  · split at hj <;> rename_i pj
    · exact congrArg Subtype.val (inj ((Option.some.inj hi).trans (Option.some.inj hj).symm))
    · contradiction
  · contradiction

def combine {n m : Nat} (r : Fin n → Option (Fin 5)) (c : Fin m → Option (Fin 5)) :
    Fin (n+m) → Option (Fin 10) :=
  Fin.addCases (fun a => (r a).map (Fin.castAdd 5)) (fun b => (c b).map (Fin.natAdd 5))

theorem combined_unique {n m : Nat} (r : Fin n → Option (Fin 5)) (c : Fin m → Option (Fin 5))
    (ri : ∀ i j a, r i = some a → r j = some a → i = j)
    (ci : ∀ i j b, c i = some b → c j = some b → i = j) :
    ∀ i j t, combine r c i = some t → combine r c j = some t → i = j := by
  intro i
  refine Fin.addCases (fun a => ?_) (fun b => ?_) i <;>
    intro j <;> refine Fin.addCases (fun u => ?_) (fun v => ?_) j <;>
    intro t hi hj <;> simp only [combine,Fin.addCases_left,Fin.addCases_right,Option.map_eq_some_iff] at hi hj <;>
    obtain ⟨x,hx,rfl⟩ := hi <;> obtain ⟨y,hy,eq⟩ := hj
  · obtain rfl : y = x := Fin.castAdd_injective 5 5 eq
    exact congrArg _ (ri _ _ _ hx hy)
  · exact (sides x y eq.symm).elim
  · exact (sides y x eq).elim
  · obtain rfl : y = x := Fin.natAdd_injective 5 5 eq
    exact congrArg _ (ci _ _ _ hx hy)

abbrev Rows {n m} (E : Matrix n m) := E.image Prod.fst
abbrev Cols {n m} (E : Matrix n m) := E.image Prod.snd
def erow {n m} {E : Matrix n m} (e : E) : Rows E := ⟨e.val.1,Finset.mem_image_of_mem _ e.property⟩
def ecol {n m} {E : Matrix n m} (e : E) : Cols E := ⟨e.val.2,Finset.mem_image_of_mem _ e.property⟩

def pack {n m} (E : Matrix n m) (r : Rows E → Fin 5) (c : Cols E → Fin 5) : Matrix 5 5 :=
  E.attach.image (fun e => (r (erow e),c (ecol e)))

theorem decode {n m} {E : Matrix n m} {r : Rows E → Fin 5} {c : Cols E → Fin 5} {a b} :
    (a,b) ∈ pack E r c ↔ ∃ e : E, r (erow e) = a ∧ c (ecol e) = b := by
  simp [pack]

theorem rows_eq {n m} {E : Matrix n m} {r : Rows E → Fin 5} (inj : Function.Injective r) (e f : E) :
    r (erow e) = r (erow f) ↔ e.val.1 = f.val.1 := ⟨fun h => congrArg Subtype.val (inj h),
      fun h => congrArg r (Subtype.ext h)⟩

theorem cols_eq {n m} {E : Matrix n m} {c : Cols E → Fin 5} (inj : Function.Injective c) (e f : E) :
    c (ecol e) = c (ecol f) ↔ e.val.2 = f.val.2 := ⟨fun h => congrArg Subtype.val (inj h),
      fun h => congrArg c (Subtype.ext h)⟩

theorem pack_card {n m} {E : Matrix n m} {r : Rows E → Fin 5} {c : Cols E → Fin 5}
    (ri : Function.Injective r) (ci : Function.Injective c) : (pack E r c).card = E.card := by
  unfold pack
  rw [Finset.card_image_of_injective,Finset.card_attach]
  intro e f eq
  exact Subtype.ext (Prod.ext ((rows_eq ri _ _).mp (congrArg Prod.fst eq))
    ((cols_eq ci _ _).mp (congrArg Prod.snd eq)))

theorem pack_free {n m} {E : Matrix n m} {r : Rows E → Fin 5} {c : Cols E → Fin 5}
    (ri : Function.Injective r) (ci : Function.Injective c) (free : FourFree E) :
    FourFree (pack E r c) := by
  intro p q l s pq ls h
  obtain ⟨a,ap,al⟩ := decode.mp h.1
  obtain ⟨b,bp,bs⟩ := decode.mp h.2.1
  obtain ⟨d,dq,dl⟩ := decode.mp h.2.2.1
  obtain ⟨e,eq,es⟩ := decode.mp h.2.2.2
  have ab := (rows_eq ri a b).mp (ap.trans bp.symm)
  have de := (rows_eq ri d e).mp (dq.trans eq.symm)
  have ad := (cols_eq ci a d).mp (al.trans dl.symm)
  have be := (cols_eq ci b e).mp (bs.trans es.symm)
  have pr : a.val.1 ≠ d.val.1 := fun hh => pq (ap.symm.trans (((rows_eq ri a d).mpr hh).trans dq))
  have lc : a.val.2 ≠ b.val.2 := fun hh => ls (al.symm.trans (((cols_eq ci a b).mpr hh).trans bs))
  apply free _ _ _ _ pr lc
  exact ⟨a.property,ab ▸ b.property,ad ▸ d.property,de ▸ be ▸ e.property⟩

theorem pack_partners {n m} {E : Matrix n m} {r : Rows E → Fin 5} {c : Cols E → Fin 5}
    (ri : Function.Injective r) (ci : Function.Injective c) (has : HasPartners E) :
    HasPartners (pack E r c) := by
  intro a b ab
  obtain ⟨e,rfl,rfl⟩ := decode.mp ab
  obtain ⟨⟨v,ne,ev⟩,⟨u,diff,ue⟩⟩ := has _ _ e.property
  let f : E := ⟨(e.val.1,v),ev⟩
  let g : E := ⟨(u,e.val.2),ue⟩
  exact ⟨⟨c (ecol f),fun eq => ne ((cols_eq ci f e).mp eq),
      decode.mpr ⟨f,(rows_eq ri f e).mpr rfl,rfl⟩⟩,
    ⟨r (erow g),fun eq => diff ((rows_eq ri g e).mp eq),
      decode.mpr ⟨g,rfl,(cols_eq ci g e).mpr rfl⟩⟩⟩

theorem unpack_counts {n m} (E : Matrix n m) (r : Rows E → Fin 5) (c : Cols E → Fin 5)
    (ri : Function.Injective r) (ci : Function.Injective c)
    (src : Counts (bip (pack E r c))) : Counts (bip E) := by
  let lab := combine (optional (Rows E) r) (optional (Cols E) c)
  have l (e : E) : lab (Left e.val.1) = some (Fin.castAdd 5 (r (erow e))) := by
    simp only [lab,combine,Left,Fin.addCases_left,optional]
    split
    · rfl
    · rename_i missing
      exact (missing (erow e).property).elim
  have rr (e : E) : lab (Right e.val.2) = some (Fin.natAdd 5 (c (ecol e))) := by
    simp only [lab,combine,Right,Fin.addCases_right,optional]
    split
    · rfl
    · rename_i missing
      exact (missing (ecol e).property).elim
  apply from_index (bip E) (bip (pack E r c)) lab
    (combined_unique _ _ (optional_unique _ _ ri) (optional_unique _ _ ci)) _ _ _ src
  · rintro i j ⟨_,⟨p,h,rfl,rfl⟩ | ⟨p,h,rfl,rfl⟩⟩
    · let e : E := ⟨p,h⟩
      exact ⟨_,_,l e,rr e,bip_adjacency (decode.mpr ⟨e,rfl,rfl⟩)⟩
    · let e : E := ⟨p,h⟩
      exact ⟨_,_,rr e,l e,(bip_adjacency (decode.mpr ⟨e,rfl,rfl⟩)).symm⟩
  · rintro i j ⟨_,⟨⟨a,b⟩,h,rfl,rfl⟩ | ⟨⟨a,b⟩,h,rfl,rfl⟩⟩
    · obtain ⟨e,rfl,rfl⟩ := decode.mp h
      exact ⟨_,_,l e,rr e,bip_adjacency e.property⟩
    · obtain ⟨e,rfl,rfl⟩ := decode.mp h
      exact ⟨_,_,rr e,l e,(bip_adjacency e.property).symm⟩
  · rw [bip_edges,bip_edges,pack_card ri ci]

def Census : Prop := ∀ E : Matrix 5 5, E.card ≤ 10 → FourFree E → Leafless (bip E) → Counts (bip E)

theorem compressed {n m} (E : Matrix n m) (free : FourFree E) (size : E.card ≤ 10)
    (last : Leafless (bip E)) (census : Census) : Counts (bip E) := by
  let h := (leafless_iff E).mp last
  obtain ⟨pr,pc⟩ := both_sides E h size
  let r (p : Rows E) := Fin.castLE pr (((Rows E).orderIsoOfFin rfl).symm p)
  let c (p : Cols E) := Fin.castLE pc (((Cols E).orderIsoOfFin rfl).symm p)
  have ri : Function.Injective r := (Fin.castLE_injective pr).comp ((Rows E).orderIsoOfFin rfl).symm.injective
  have ci : Function.Injective c := (Fin.castLE_injective pc).comp ((Cols E).orderIsoOfFin rfl).symm.injective
  apply unpack_counts E r c ri ci
  apply census
  · simpa [pack_card ri ci] using size
  · exact pack_free ri ci free
  · exact (leafless_iff _).mpr (pack_partners ri ci h)

end MatrixPacking3241

namespace CoreCensus
open LeafCore3241 SmallCores3241 ForestBipartite3241

inductive Shape | six | eight | ten | theta333 | theta244 deriving DecidableEq, Repr

abbrev order : Shape → Nat
  | .six => 6 | .eight => 8 | .ten => 10 | .theta333 => 8 | .theta244 => 9

instance (s : Shape) : NeZero (order s) := by cases s <;> exact ⟨by decide⟩

def edges : Shape → List (Nat × Nat)
  | .six => [(0,1),(1,2),(2,3),(3,4),(4,5),(5,0)]
  | .eight => [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,0)]
  | .ten => [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,0)]
  | .theta333 => [(0,5),(0,6),(0,7),(1,4),(1,7),(2,4),(2,6),(3,4),(3,5)]
  | .theta244 => [(0,2),(1,2),(0,3),(3,4),(4,5),(1,5),(0,6),(6,7),(7,8),(1,8)]

abbrev source (s : Shape) := graph (order s) (edges s)

theorem counts_source (s) (h : ThetaPin3241.Lower Theta244Cores.theta 9) : Counts (source s) := by
  cases s
  · exact sixCounts
  · exact eightCounts
  · exact tenCounts
  · exact threeThreeThreeCounts
  · exact twoFourFourCounts h

def pairs (rows : List Nat) : Finset (Fin 5 × Fin 5) :=
  Finset.univ.filter fun (i,j) => (rows.getD i.val 0).testBit j.val

def matrix (rows : List Nat) := bip (pairs rows)

instance (rows : List Nat) : DecidableRel (matrix rows).Adj := by unfold matrix bip; infer_instance

structure Item where
  rows : List Nat
  shape : Shape
  forward : List Nat
  backward : List Nat
  deriving Repr

def emb (r : Item) (i : Fin (order r.shape)) : Fin 10 := Fin.ofNat 10 (r.forward.getD i.val 0)
def inv (r : Item) (i : Fin 10) : Fin (order r.shape) := Fin.ofNat (order r.shape) (r.backward.getD i.val 0)

def Certified (r : Item) : Prop :=
  (∀ u, inv r (emb r u) = u) ∧ ∀ i j, (matrix r.rows).Adj i j ↔
     emb r (inv r i) = i ∧ emb r (inv r j) = j ∧ (source r.shape).Adj (inv r i) (inv r j)

instance (r : Item) : Decidable (Certified r) := by unfold Certified; infer_instance

theorem count_item (r : Item) (hc : Certified r) (h : ThetaPin3241.Lower Theta244Cores.theta 9) :
    Counts (matrix r.rows) := by
  apply CoreTransfer3241.padded (source r.shape) (matrix r.rows) (emb r) (Function.LeftInverse.injective hc.1) _ (counts_source _ h)
  intro i j
  constructor
  · intro a
    obtain ⟨hi,hj,adj⟩ := (hc.2 i j).mp a
    exact ⟨_,_,adj,hi,hj⟩
  · rintro ⟨u,v,a,rfl,rfl⟩
    apply (hc.2 _ _).mpr
    rw [hc.1 u,hc.1 v]
    exact ⟨rfl,rfl,a⟩

end CoreCensus

namespace CoreCensus

def batch0 : List Item := [
  ⟨[3, 5, 6],.six,[1, 5, 0, 6, 2, 7],[2, 0, 4, 0, 0, 1, 3, 5, 0, 0]⟩,
  ⟨[3, 5, 6, 9, 10],.theta244,[5, 6, 0, 1, 7, 2, 3, 8, 4],[2, 3, 5, 6, 8, 0, 1, 4, 7, 0]⟩,
  ⟨[3, 5, 6, 9, 12],.theta244,[5, 7, 1, 0, 6, 2, 3, 8, 4],[3, 2, 5, 6, 8, 0, 4, 1, 7, 0]⟩,
  ⟨[3, 5, 6, 10, 12],.theta244,[6, 7, 2, 0, 5, 1, 3, 8, 4],[3, 5, 2, 6, 8, 4, 0, 1, 7, 0]⟩,
  ⟨[3, 5, 6, 17, 18],.theta244,[5, 6, 0, 1, 7, 2, 3, 9, 4],[2, 3, 5, 6, 8, 0, 1, 4, 0, 7]⟩,
  ⟨[3, 5, 6, 17, 20],.theta244,[5, 7, 1, 0, 6, 2, 3, 9, 4],[3, 2, 5, 6, 8, 0, 4, 1, 0, 7]⟩]

def batch1 : List Item := [
  ⟨[3, 5, 6, 18, 20],.theta244,[6, 7, 2, 0, 5, 1, 3, 9, 4],[3, 5, 2, 6, 8, 4, 0, 1, 0, 7]⟩,
  ⟨[3, 5, 9, 10, 12],.theta244,[5, 8, 2, 0, 6, 3, 1, 7, 4],[3, 6, 2, 5, 8, 0, 4, 7, 1, 0]⟩,
  ⟨[3, 5, 9, 14],.theta333,[3, 2, 1, 0, 5, 6, 7, 8],[3, 2, 1, 0, 0, 4, 5, 6, 7, 0]⟩,
  ⟨[3, 5, 10, 12],.eight,[1, 5, 0, 6, 2, 8, 3, 7],[2, 0, 4, 6, 0, 1, 3, 7, 5, 0]⟩,
  ⟨[3, 5, 10, 20, 24],.ten,[1, 5, 0, 6, 2, 8, 4, 9, 3, 7],[2, 0, 4, 8, 6, 1, 3, 9, 5, 7]⟩,
  ⟨[3, 5, 12, 18, 24],.ten,[1, 5, 0, 6, 3, 9, 4, 8, 2, 7],[2, 0, 8, 4, 6, 1, 3, 9, 7, 5]⟩]

def batch2 : List Item := [
  ⟨[3, 5, 17, 18, 20],.theta244,[5, 9, 2, 0, 6, 3, 1, 7, 4],[3, 6, 2, 5, 8, 0, 4, 7, 0, 1]⟩,
  ⟨[3, 5, 17, 22],.theta333,[3, 2, 1, 0, 5, 6, 7, 9],[3, 2, 1, 0, 0, 4, 5, 6, 0, 7]⟩,
  ⟨[3, 5, 18, 20],.eight,[1, 5, 0, 6, 2, 9, 3, 7],[2, 0, 4, 6, 0, 1, 3, 7, 0, 5]⟩,
  ⟨[3, 6, 9, 10, 12],.theta244,[6, 8, 3, 0, 5, 2, 1, 7, 4],[3, 6, 5, 2, 8, 4, 0, 7, 1, 0]⟩,
  ⟨[3, 6, 9, 12],.eight,[2, 5, 0, 6, 1, 7, 3, 8],[2, 4, 0, 6, 0, 1, 3, 5, 7, 0]⟩,
  ⟨[3, 6, 9, 20, 24],.ten,[2, 5, 0, 6, 1, 7, 3, 9, 4, 8],[2, 4, 0, 6, 8, 1, 3, 5, 9, 7]⟩]

def batch3 : List Item := [
  ⟨[3, 6, 10, 13],.theta333,[3, 2, 1, 0, 6, 5, 7, 8],[3, 2, 1, 0, 0, 5, 4, 6, 7, 0]⟩,
  ⟨[3, 6, 12, 17, 24],.ten,[3, 5, 0, 6, 1, 7, 2, 8, 4, 9],[2, 4, 6, 0, 8, 1, 3, 5, 7, 9]⟩,
  ⟨[3, 6, 17, 18, 20],.theta244,[6, 9, 3, 0, 5, 2, 1, 7, 4],[3, 6, 5, 2, 8, 4, 0, 7, 0, 1]⟩,
  ⟨[3, 6, 17, 20],.eight,[2, 5, 0, 6, 1, 7, 3, 9],[2, 4, 0, 6, 0, 1, 3, 5, 0, 7]⟩,
  ⟨[3, 6, 18, 21],.theta333,[3, 2, 1, 0, 6, 5, 7, 9],[3, 2, 1, 0, 0, 5, 4, 6, 0, 7]⟩,
  ⟨[3, 9, 10],.six,[1, 5, 0, 6, 2, 8],[2, 0, 4, 0, 0, 1, 3, 0, 5, 0]⟩]

def batch4 : List Item := [
  ⟨[3, 9, 10, 17, 18],.theta244,[5, 6, 0, 1, 8, 2, 3, 9, 4],[2, 3, 5, 6, 8, 0, 1, 0, 4, 7]⟩,
  ⟨[3, 9, 10, 17, 24],.theta244,[5, 8, 1, 0, 6, 2, 3, 9, 4],[3, 2, 5, 6, 8, 0, 4, 0, 1, 7]⟩,
  ⟨[3, 9, 10, 18, 24],.theta244,[6, 8, 2, 0, 5, 1, 3, 9, 4],[3, 5, 2, 6, 8, 4, 0, 0, 1, 7]⟩,
  ⟨[3, 9, 12, 18, 20],.ten,[1, 5, 0, 6, 3, 9, 4, 7, 2, 8],[2, 0, 8, 4, 6, 1, 3, 7, 9, 5]⟩,
  ⟨[3, 9, 17, 18, 24],.theta244,[5, 9, 2, 0, 6, 3, 1, 8, 4],[3, 6, 2, 5, 8, 0, 4, 0, 7, 1]⟩,
  ⟨[3, 9, 17, 26],.theta333,[3, 2, 1, 0, 5, 6, 8, 9],[3, 2, 1, 0, 0, 4, 5, 0, 6, 7]⟩]

def batch5 : List Item := [
  ⟨[3, 9, 18, 24],.eight,[1, 5, 0, 6, 2, 9, 3, 8],[2, 0, 4, 6, 0, 1, 3, 0, 7, 5]⟩,
  ⟨[3, 10, 12, 17, 20],.ten,[3, 5, 0, 6, 1, 8, 2, 7, 4, 9],[2, 4, 6, 0, 8, 1, 3, 7, 5, 9]⟩,
  ⟨[3, 10, 17, 18, 24],.theta244,[6, 9, 3, 0, 5, 2, 1, 8, 4],[3, 6, 5, 2, 8, 4, 0, 0, 7, 1]⟩,
  ⟨[3, 10, 17, 24],.eight,[2, 5, 0, 6, 1, 8, 3, 9],[2, 4, 0, 6, 0, 1, 3, 0, 5, 7]⟩,
  ⟨[3, 10, 18, 25],.theta333,[3, 2, 1, 0, 6, 5, 8, 9],[3, 2, 1, 0, 0, 5, 4, 0, 6, 7]⟩,
  ⟨[3, 12, 21, 26],.theta244,[2, 3, 9, 5, 0, 6, 7, 1, 8],[4, 7, 0, 1, 0, 3, 5, 6, 8, 2]⟩]

def batch6 : List Item := [
  ⟨[3, 12, 22, 25],.theta244,[3, 2, 9, 5, 0, 6, 8, 1, 7],[4, 7, 1, 0, 0, 3, 5, 8, 6, 2]⟩,
  ⟨[3, 13, 20, 26],.theta244,[1, 3, 8, 5, 0, 6, 7, 2, 9],[4, 0, 7, 1, 0, 3, 5, 6, 2, 8]⟩,
  ⟨[3, 13, 22, 24],.theta244,[1, 2, 7, 5, 0, 6, 8, 3, 9],[4, 0, 1, 7, 0, 3, 5, 2, 6, 8]⟩,
  ⟨[3, 14, 20, 25],.theta244,[3, 1, 8, 5, 0, 6, 9, 2, 7],[4, 1, 7, 0, 0, 3, 5, 8, 2, 6]⟩,
  ⟨[3, 14, 21, 24],.theta244,[2, 1, 7, 5, 0, 6, 9, 3, 8],[4, 1, 0, 7, 0, 3, 5, 2, 8, 6]⟩,
  ⟨[3, 17, 18],.six,[1, 5, 0, 6, 2, 9],[2, 0, 4, 0, 0, 1, 3, 0, 0, 5]⟩]

def batch7 : List Item := [
  ⟨[5, 6, 9, 10],.eight,[2, 5, 0, 7, 1, 6, 3, 8],[2, 4, 0, 6, 0, 1, 5, 3, 7, 0]⟩,
  ⟨[5, 6, 9, 10, 12],.theta244,[7, 8, 4, 0, 5, 2, 1, 6, 3],[3, 6, 5, 8, 2, 4, 7, 0, 1, 0]⟩,
  ⟨[5, 6, 9, 18, 24],.ten,[2, 5, 0, 7, 1, 6, 3, 9, 4, 8],[2, 4, 0, 6, 8, 1, 5, 3, 9, 7]⟩,
  ⟨[5, 6, 10, 17, 24],.ten,[3, 5, 0, 7, 1, 6, 2, 8, 4, 9],[2, 4, 6, 0, 8, 1, 5, 3, 7, 9]⟩,
  ⟨[5, 6, 11, 12],.theta333,[2, 3, 1, 0, 7, 5, 6, 8],[3, 2, 0, 1, 0, 5, 6, 4, 7, 0]⟩,
  ⟨[5, 6, 17, 18],.eight,[2, 5, 0, 7, 1, 6, 3, 9],[2, 4, 0, 6, 0, 1, 5, 3, 0, 7]⟩]

def batch8 : List Item := [
  ⟨[5, 6, 17, 18, 20],.theta244,[7, 9, 4, 0, 5, 2, 1, 6, 3],[3, 6, 5, 8, 2, 4, 7, 0, 0, 1]⟩,
  ⟨[5, 6, 19, 20],.theta333,[2, 3, 1, 0, 7, 5, 6, 9],[3, 2, 0, 1, 0, 5, 6, 4, 0, 7]⟩,
  ⟨[5, 9, 10, 18, 20],.ten,[1, 5, 0, 7, 4, 9, 3, 6, 2, 8],[2, 0, 8, 6, 4, 1, 7, 3, 9, 5]⟩,
  ⟨[5, 9, 12],.six,[1, 5, 0, 7, 2, 8],[2, 0, 4, 0, 0, 1, 0, 3, 5, 0]⟩,
  ⟨[5, 9, 12, 17, 20],.theta244,[5, 7, 0, 1, 8, 2, 3, 9, 4],[2, 3, 5, 6, 8, 0, 0, 1, 4, 7]⟩,
  ⟨[5, 9, 12, 17, 24],.theta244,[5, 8, 1, 0, 7, 2, 3, 9, 4],[3, 2, 5, 6, 8, 0, 0, 4, 1, 7]⟩]

def batch9 : List Item := [
  ⟨[5, 9, 12, 20, 24],.theta244,[7, 8, 2, 0, 5, 1, 3, 9, 4],[3, 5, 2, 6, 8, 4, 0, 0, 1, 7]⟩,
  ⟨[5, 9, 17, 20, 24],.theta244,[5, 9, 2, 0, 7, 3, 1, 8, 4],[3, 6, 2, 5, 8, 0, 0, 4, 7, 1]⟩,
  ⟨[5, 9, 17, 28],.theta333,[3, 2, 1, 0, 5, 7, 8, 9],[3, 2, 1, 0, 0, 4, 0, 5, 6, 7]⟩,
  ⟨[5, 9, 20, 24],.eight,[1, 5, 0, 7, 2, 9, 3, 8],[2, 0, 4, 6, 0, 1, 0, 3, 7, 5]⟩,
  ⟨[5, 10, 12, 17, 18],.ten,[3, 5, 0, 7, 2, 8, 1, 6, 4, 9],[2, 6, 4, 0, 8, 1, 7, 3, 5, 9]⟩,
  ⟨[5, 10, 19, 28],.theta244,[2, 3, 9, 5, 0, 7, 6, 1, 8],[4, 7, 0, 1, 0, 3, 6, 5, 8, 2]⟩]

def batch10 : List Item := [
  ⟨[5, 10, 22, 25],.theta244,[3, 2, 9, 5, 0, 7, 8, 1, 6],[4, 7, 1, 0, 0, 3, 8, 5, 6, 2]⟩,
  ⟨[5, 11, 18, 28],.theta244,[1, 3, 8, 5, 0, 7, 6, 2, 9],[4, 0, 7, 1, 0, 3, 6, 5, 2, 8]⟩,
  ⟨[5, 11, 22, 24],.theta244,[1, 2, 6, 5, 0, 7, 8, 3, 9],[4, 0, 1, 7, 0, 3, 2, 5, 6, 8]⟩,
  ⟨[5, 12, 17, 20, 24],.theta244,[7, 9, 3, 0, 5, 2, 1, 8, 4],[3, 6, 5, 2, 8, 4, 0, 0, 7, 1]⟩,
  ⟨[5, 12, 17, 24],.eight,[2, 5, 0, 7, 1, 8, 3, 9],[2, 4, 0, 6, 0, 1, 0, 3, 5, 7]⟩,
  ⟨[5, 12, 20, 25],.theta333,[3, 2, 1, 0, 7, 5, 8, 9],[3, 2, 1, 0, 0, 5, 0, 4, 6, 7]⟩]

def batch11 : List Item := [
  ⟨[5, 14, 18, 25],.theta244,[3, 1, 8, 5, 0, 7, 9, 2, 6],[4, 1, 7, 0, 0, 3, 8, 5, 2, 6]⟩,
  ⟨[5, 14, 19, 24],.theta244,[2, 1, 6, 5, 0, 7, 9, 3, 8],[4, 1, 0, 7, 0, 3, 2, 5, 8, 6]⟩,
  ⟨[5, 17, 20],.six,[1, 5, 0, 7, 2, 9],[2, 0, 4, 0, 0, 1, 0, 3, 0, 5]⟩,
  ⟨[6, 9, 10, 17, 20],.ten,[3, 5, 1, 8, 2, 6, 0, 7, 4, 9],[6, 2, 4, 0, 8, 1, 5, 7, 3, 9]⟩,
  ⟨[6, 9, 12, 17, 18],.ten,[3, 5, 1, 8, 2, 7, 0, 6, 4, 9],[6, 2, 4, 0, 8, 1, 7, 5, 3, 9]⟩,
  ⟨[6, 9, 19, 28],.theta244,[2, 3, 9, 5, 1, 8, 6, 0, 7],[7, 4, 0, 1, 0, 3, 6, 8, 5, 2]⟩]

def batch12 : List Item := [
  ⟨[6, 9, 21, 26],.theta244,[2, 3, 9, 5, 1, 8, 7, 0, 6],[7, 4, 0, 1, 0, 3, 8, 6, 5, 2]⟩,
  ⟨[6, 10, 12],.six,[1, 6, 0, 7, 2, 8],[2, 0, 4, 0, 0, 0, 1, 3, 5, 0]⟩,
  ⟨[6, 10, 12, 18, 20],.theta244,[6, 7, 0, 1, 8, 2, 3, 9, 4],[2, 3, 5, 6, 8, 0, 0, 1, 4, 7]⟩,
  ⟨[6, 10, 12, 18, 24],.theta244,[6, 8, 1, 0, 7, 2, 3, 9, 4],[3, 2, 5, 6, 8, 0, 0, 4, 1, 7]⟩,
  ⟨[6, 10, 12, 20, 24],.theta244,[7, 8, 2, 0, 6, 1, 3, 9, 4],[3, 5, 2, 6, 8, 0, 4, 0, 1, 7]⟩,
  ⟨[6, 10, 18, 20, 24],.theta244,[6, 9, 2, 0, 7, 3, 1, 8, 4],[3, 6, 2, 5, 8, 0, 0, 4, 7, 1]⟩]

def batch13 : List Item := [
  ⟨[6, 10, 18, 28],.theta333,[3, 2, 1, 0, 6, 7, 8, 9],[3, 2, 1, 0, 0, 0, 4, 5, 6, 7]⟩,
  ⟨[6, 10, 20, 24],.eight,[1, 6, 0, 7, 2, 9, 3, 8],[2, 0, 4, 6, 0, 0, 1, 3, 7, 5]⟩,
  ⟨[6, 11, 17, 28],.theta244,[1, 3, 8, 5, 2, 9, 6, 0, 7],[7, 0, 4, 1, 0, 3, 6, 8, 2, 5]⟩,
  ⟨[6, 11, 21, 24],.theta244,[1, 2, 5, 6, 0, 7, 8, 3, 9],[4, 0, 1, 7, 0, 2, 3, 5, 6, 8]⟩,
  ⟨[6, 12, 18, 20, 24],.theta244,[7, 9, 3, 0, 6, 2, 1, 8, 4],[3, 6, 5, 2, 8, 0, 4, 0, 7, 1]⟩,
  ⟨[6, 12, 18, 24],.eight,[2, 6, 0, 7, 1, 8, 3, 9],[2, 4, 0, 6, 0, 0, 1, 3, 5, 7]⟩]

def batch14 : List Item := [
  ⟨[6, 12, 20, 26],.theta333,[3, 2, 1, 0, 7, 6, 8, 9],[3, 2, 1, 0, 0, 0, 5, 4, 6, 7]⟩,
  ⟨[6, 13, 17, 26],.theta244,[1, 3, 8, 5, 2, 9, 7, 0, 6],[7, 0, 4, 1, 0, 3, 8, 6, 2, 5]⟩,
  ⟨[6, 13, 19, 24],.theta244,[2, 1, 5, 6, 0, 7, 9, 3, 8],[4, 1, 0, 7, 0, 2, 3, 5, 8, 6]⟩,
  ⟨[6, 18, 20],.six,[1, 6, 0, 7, 2, 9],[2, 0, 4, 0, 0, 0, 1, 3, 0, 5]⟩,
  ⟨[7, 9, 10, 12],.theta333,[0, 3, 2, 1, 8, 5, 6, 7],[0, 3, 2, 1, 0, 5, 6, 7, 4, 0]⟩,
  ⟨[7, 9, 18, 28],.theta244,[0, 3, 7, 5, 1, 8, 6, 2, 9],[0, 4, 7, 1, 0, 3, 6, 2, 5, 8]⟩]

def batch15 : List Item := [
  ⟨[7, 9, 20, 26],.theta244,[0, 3, 6, 5, 1, 8, 7, 2, 9],[0, 4, 7, 1, 0, 3, 2, 6, 5, 8]⟩,
  ⟨[7, 10, 17, 28],.theta244,[0, 3, 7, 5, 2, 9, 6, 1, 8],[0, 7, 4, 1, 0, 3, 6, 2, 8, 5]⟩,
  ⟨[7, 10, 20, 25],.theta244,[0, 3, 5, 6, 1, 8, 7, 2, 9],[0, 4, 7, 1, 0, 2, 3, 6, 5, 8]⟩,
  ⟨[7, 12, 17, 26],.theta244,[0, 3, 6, 5, 2, 9, 7, 1, 8],[0, 7, 4, 1, 0, 3, 2, 6, 8, 5]⟩,
  ⟨[7, 12, 18, 25],.theta244,[0, 3, 5, 6, 2, 9, 7, 1, 8],[0, 7, 4, 1, 0, 2, 3, 6, 8, 5]⟩,
  ⟨[7, 17, 18, 20],.theta333,[0, 3, 2, 1, 9, 5, 6, 7],[0, 3, 2, 1, 0, 5, 6, 7, 0, 4]⟩]

def batch16 : List Item := [
  ⟨[9, 10, 17, 18],.eight,[2, 5, 0, 8, 1, 6, 3, 9],[2, 4, 0, 6, 0, 1, 5, 0, 3, 7]⟩,
  ⟨[9, 10, 17, 18, 24],.theta244,[8, 9, 4, 0, 5, 2, 1, 6, 3],[3, 6, 5, 8, 2, 4, 7, 0, 0, 1]⟩,
  ⟨[9, 10, 19, 24],.theta333,[2, 3, 1, 0, 8, 5, 6, 9],[3, 2, 0, 1, 0, 5, 6, 0, 4, 7]⟩,
  ⟨[9, 12, 17, 20],.eight,[2, 5, 0, 8, 1, 7, 3, 9],[2, 4, 0, 6, 0, 1, 0, 5, 3, 7]⟩,
  ⟨[9, 12, 17, 20, 24],.theta244,[8, 9, 4, 0, 5, 2, 1, 7, 3],[3, 6, 5, 8, 2, 4, 0, 7, 0, 1]⟩,
  ⟨[9, 12, 21, 24],.theta333,[2, 3, 1, 0, 8, 5, 7, 9],[3, 2, 0, 1, 0, 5, 0, 6, 4, 7]⟩]

def batch17 : List Item := [
  ⟨[9, 14, 18, 21],.theta244,[3, 1, 7, 5, 0, 8, 9, 2, 6],[4, 1, 7, 0, 0, 3, 8, 2, 5, 6]⟩,
  ⟨[9, 14, 19, 20],.theta244,[2, 1, 6, 5, 0, 8, 9, 3, 7],[4, 1, 0, 7, 0, 3, 2, 8, 5, 6]⟩,
  ⟨[9, 17, 24],.six,[1, 5, 0, 8, 2, 9],[2, 0, 4, 0, 0, 1, 0, 0, 3, 5]⟩,
  ⟨[10, 12, 18, 20],.eight,[2, 6, 0, 8, 1, 7, 3, 9],[2, 4, 0, 6, 0, 0, 1, 5, 3, 7]⟩,
  ⟨[10, 12, 18, 20, 24],.theta244,[8, 9, 4, 0, 6, 2, 1, 7, 3],[3, 6, 5, 8, 2, 0, 4, 7, 0, 1]⟩,
  ⟨[10, 12, 22, 24],.theta333,[2, 3, 1, 0, 8, 6, 7, 9],[3, 2, 0, 1, 0, 0, 5, 6, 4, 7]⟩]

def batch18 : List Item := [
  ⟨[10, 13, 17, 22],.theta244,[1, 3, 7, 5, 2, 9, 8, 0, 6],[7, 0, 4, 1, 0, 3, 8, 2, 6, 5]⟩,
  ⟨[10, 13, 19, 20],.theta244,[2, 1, 5, 6, 0, 8, 9, 3, 7],[4, 1, 0, 7, 0, 2, 3, 8, 5, 6]⟩,
  ⟨[10, 18, 24],.six,[1, 6, 0, 8, 2, 9],[2, 0, 4, 0, 0, 0, 1, 0, 3, 5]⟩,
  ⟨[11, 12, 17, 22],.theta244,[0, 3, 6, 5, 2, 9, 8, 1, 7],[0, 7, 4, 1, 0, 3, 2, 8, 6, 5]⟩,
  ⟨[11, 12, 18, 21],.theta244,[0, 3, 5, 6, 2, 9, 8, 1, 7],[0, 7, 4, 1, 0, 2, 3, 8, 6, 5]⟩,
  ⟨[11, 17, 18, 24],.theta333,[0, 3, 2, 1, 9, 5, 6, 8],[0, 3, 2, 1, 0, 5, 6, 0, 7, 4]⟩]

def batch19 : List Item := [
  ⟨[12, 20, 24],.six,[1, 7, 0, 8, 2, 9],[2, 0, 4, 0, 0, 0, 0, 1, 3, 5]⟩,
  ⟨[13, 17, 20, 24],.theta333,[0, 3, 2, 1, 9, 5, 7, 8],[0, 3, 2, 1, 0, 5, 0, 6, 7, 4]⟩,
  ⟨[14, 18, 20, 24],.theta333,[0, 3, 2, 1, 9, 6, 7, 8],[0, 3, 2, 1, 0, 0, 5, 6, 7, 4]⟩]

def items := batch0 ++ batch1 ++ batch2 ++ batch3 ++ batch4 ++ batch5 ++ batch6 ++ batch7 ++ batch8 ++ batch9 ++ batch10 ++ batch11 ++ batch12 ++ batch13 ++ batch14 ++ batch15 ++ batch16 ++ batch17 ++ batch18 ++ batch19

end CoreCensus

namespace CoreCensus

set_option maxRecDepth 12000 in
set_option maxHeartbeats 5000000 in
theorem check0 : batch0.all (fun r => decide (Certified r)) = true := by decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 5000000 in
theorem check1 : batch1.all (fun r => decide (Certified r)) = true := by decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 5000000 in
theorem check2 : batch2.all (fun r => decide (Certified r)) = true := by decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 5000000 in
theorem check3 : batch3.all (fun r => decide (Certified r)) = true := by decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 5000000 in
theorem check4 : batch4.all (fun r => decide (Certified r)) = true := by decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 5000000 in
theorem check5 : batch5.all (fun r => decide (Certified r)) = true := by decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 5000000 in
theorem check6 : batch6.all (fun r => decide (Certified r)) = true := by decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 5000000 in
theorem check7 : batch7.all (fun r => decide (Certified r)) = true := by decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 5000000 in
theorem check8 : batch8.all (fun r => decide (Certified r)) = true := by decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 5000000 in
theorem check9 : batch9.all (fun r => decide (Certified r)) = true := by decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 5000000 in
theorem check10 : batch10.all (fun r => decide (Certified r)) = true := by decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 5000000 in
theorem check11 : batch11.all (fun r => decide (Certified r)) = true := by decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 5000000 in
theorem check12 : batch12.all (fun r => decide (Certified r)) = true := by decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 5000000 in
theorem check13 : batch13.all (fun r => decide (Certified r)) = true := by decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 5000000 in
theorem check14 : batch14.all (fun r => decide (Certified r)) = true := by decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 5000000 in
theorem check15 : batch15.all (fun r => decide (Certified r)) = true := by decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 5000000 in
theorem check16 : batch16.all (fun r => decide (Certified r)) = true := by decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 5000000 in
theorem check17 : batch17.all (fun r => decide (Certified r)) = true := by decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 5000000 in
theorem check18 : batch18.all (fun r => decide (Certified r)) = true := by decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 5000000 in
theorem check19 : batch19.all (fun r => decide (Certified r)) = true := by decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 5000000 in
theorem validated {r : Item} (hr : r ∈ items) : Certified r := by
  have h : items.all (fun e => decide (Certified e)) = true := by
    simp only [items,List.all_append,check0,check1,check2,check3,check4,check5,check6,check7,check8,check9,check10,check11,check12,check13,check14,check15,check16,check17,check18,check19,Bool.true_and]
  exact of_decide_eq_true (List.all_eq_true.mp h r hr)

end CoreCensus

namespace CoreCensus
open List

def wt (r : Nat) := (r % 2) + (r / 2 % 2) + (r / 4 % 2) + (r / 8 % 2) + (r / 16 % 2)

def eligible (lo budget : Nat) (pre : List Nat) (r : Nat) : Bool :=
  decide (lo < r ∧ 2 ≤ wt r ∧ wt r ≤ budget) && pre.all (fun p => decide (wt (p &&& r) ≤ 1))

def generate : Nat → Nat → Nat → List Nat → List (List Nat)
  | 0, _, _, pre => [pre]
  | k+1, lo, budget, pre => pre :: ((range 32).filter (eligible lo budget pre)).flatMap
      fun r => generate k r (budget - wt r) (pre ++ [r])

theorem current_mem (k lo budget) (pre : List Nat) : pre ∈ generate k lo budget pre := by
  cases k <;> simp [generate]

def Compatible (r s : Nat) := r < s ∧ wt (r &&& s) ≤ 1

theorem listed (ys : List Nat) (fuel lo budget : Nat) (pre : List Nat)
    (len : ys.length ≤ fuel) (bounds : ∀ r ∈ ys, lo < r ∧ r < 32 ∧ 2 ≤ wt r)
    (total : (ys.map wt).sum ≤ budget) (pair : ys.Pairwise Compatible)
    (past : ∀ r ∈ ys, ∀ p ∈ pre, wt (p &&& r) ≤ 1) :
    pre ++ ys ∈ generate fuel lo budget pre := by
  induction ys generalizing fuel lo budget pre with
  | nil => simpa using current_mem fuel lo budget pre
  | cons r rs ih =>
    cases fuel with
    | zero => simp at len
    | succ k =>
      obtain ⟨rtop,rr,rlower⟩ := bounds r (by simp)
      have cost : wt r + (rs.map wt).sum ≤ budget := by simpa using total
      obtain ⟨first,tail⟩ := List.pairwise_cons.mp pair
      have elig : eligible lo budget pre r = true := by
        unfold eligible
        apply Bool.and_eq_true_iff.mpr
        exact ⟨decide_eq_true ⟨rtop,rlower,by omega⟩,
          List.all_eq_true.mpr (fun p hp => decide_eq_true (past r (by simp) p hp))⟩
      apply List.mem_cons_of_mem
      apply List.mem_flatMap.mpr
      refine ⟨r,List.mem_filter.mpr ⟨List.mem_range.mpr rr,elig⟩,?_⟩
      have hmem := ih k r (budget - wt r) (pre ++ [r]) (by simpa using len)
          (fun s hs => ⟨(first s hs).1,(bounds s (by simp [hs])).2⟩) (by omega) tail (by
            intro s hs p hp
            rcases List.mem_append.mp hp with old | new
            · exact past s (by simp [hs]) p old
            · obtain rfl : p = r := by simpa using new
              exact (first s hs).2)
      simpa only [List.append_assoc,List.singleton_append] using hmem

def liveCols (xs : List Nat) : Bool :=
  (range 5).all fun i => decide (xs.countP (fun r => r.testBit i) ≠ 1)

def recognized (xs : List Nat) : Bool := items.any (fun c => c.rows == xs)

def acceptedRows (xs : List Nat) : Bool := xs.isEmpty || !liveCols xs || recognized xs

theorem exists_item {xs : List Nat} (h : recognized xs = true) : ∃ r ∈ items, r.rows = xs := by
  obtain ⟨r,hr,eq⟩ := List.any_eq_true.mp h
  exact ⟨r,hr,by simpa using eq⟩

end CoreCensus

namespace CoreCensus
open List

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem first3 : (generate 4 3 (10 - wt 3) [3]).all acceptedRows = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem first5 : (generate 4 5 (10 - wt 5) [5]).all acceptedRows = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem first6 : (generate 4 6 (10 - wt 6) [6]).all acceptedRows = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem first7 : (generate 4 7 (10 - wt 7) [7]).all acceptedRows = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem first9 : (generate 4 9 (10 - wt 9) [9]).all acceptedRows = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem first10 : (generate 4 10 (10 - wt 10) [10]).all acceptedRows = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem first11 : (generate 4 11 (10 - wt 11) [11]).all acceptedRows = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem first12 : (generate 4 12 (10 - wt 12) [12]).all acceptedRows = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem first13 : (generate 4 13 (10 - wt 13) [13]).all acceptedRows = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem first14 : (generate 4 14 (10 - wt 14) [14]).all acceptedRows = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem first15 : (generate 4 15 (10 - wt 15) [15]).all acceptedRows = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem first17 : (generate 4 17 (10 - wt 17) [17]).all acceptedRows = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem first18 : (generate 4 18 (10 - wt 18) [18]).all acceptedRows = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem first19 : (generate 4 19 (10 - wt 19) [19]).all acceptedRows = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem first20 : (generate 4 20 (10 - wt 20) [20]).all acceptedRows = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem first21 : (generate 4 21 (10 - wt 21) [21]).all acceptedRows = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem first22 : (generate 4 22 (10 - wt 22) [22]).all acceptedRows = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem first23 : (generate 4 23 (10 - wt 23) [23]).all acceptedRows = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem first24 : (generate 4 24 (10 - wt 24) [24]).all acceptedRows = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem first25 : (generate 4 25 (10 - wt 25) [25]).all acceptedRows = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem first26 : (generate 4 26 (10 - wt 26) [26]).all acceptedRows = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem first27 : (generate 4 27 (10 - wt 27) [27]).all acceptedRows = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem first28 : (generate 4 28 (10 - wt 28) [28]).all acceptedRows = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem first29 : (generate 4 29 (10 - wt 29) [29]).all acceptedRows = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem first30 : (generate 4 30 (10 - wt 30) [30]).all acceptedRows = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem first31 : (generate 4 31 (10 - wt 31) [31]).all acceptedRows = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem all_rows : (generate 5 0 10 []).all acceptedRows = true := by
  have opts : (range 32).filter (eligible 0 10 []) = [3, 5, 6, 7, 9, 10, 11, 12, 13, 14, 15, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31] := by decide +kernel
  change (acceptedRows [] && (((range 32).filter (eligible 0 10 [])).flatMap (fun r => generate 4 r (10 - wt r) ([] ++ [r]))).all acceptedRows) = true
  rw [List.all_flatMap,opts]
  have empty : acceptedRows [] = true := rfl
  simp only [empty,List.nil_append,List.all_cons,List.all_nil,Bool.true_and,first3,first5,first6,first7,first9,first10,first11,first12,first13,first14,first15,first17,first18,first19,first20,first21,first22,first23,first24,first25,first26,first27,first28,first29,first30,first31]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem recognized_of_rows (xs : List Nat) (hne : xs ≠ [])
    (len : xs.length ≤ 5) (bounds : ∀ r ∈ xs, 0 < r ∧ r < 32 ∧ 2 ≤ wt r)
    (w : (xs.map wt).sum ≤ 10) (s : xs.Pairwise Compatible) (hcol : liveCols xs = true) :
    ∃ c ∈ items, c.rows = xs := by
  have mem := listed xs 5 0 10 [] len bounds w s (by simp)
  have result := List.all_eq_true.mp all_rows xs (by simpa using mem)
  apply exists_item
  have notEmpty : xs.isEmpty = false := List.isEmpty_eq_false_iff.mpr hne
  simpa [acceptedRows,notEmpty,hcol] using result

end CoreCensus

namespace CoreCensus
open LeafCore3241

theorem sorted_counts (xs : List Nat) (hne : xs ≠ []) (len : xs.length ≤ 5)
    (bounds : ∀ r ∈ xs, 0 < r ∧ r < 32 ∧ 2 ≤ wt r) (w : (xs.map wt).sum ≤ 10)
    (s : xs.Pairwise Compatible) (hcol : liveCols xs = true) : Counts (matrix xs) := by
  obtain ⟨r,member,rfl⟩ := recognized_of_rows xs hne len bounds w s hcol
  exact count_item r (validated member) Theta244.nine

end CoreCensus

namespace NormalizeCores3241
open CoreCensus GraphPacking3241 MatrixPacking3241 LeafCore3241 ForestBipartite3241

def encode (x : Fin 5 → Bool) : Nat :=
  (x 0).toNat + (x 1).toNat * 2 + (x 2).toNat * 4 + (x 3).toNat * 8 + (x 4).toNat * 16

theorem encode_bound : ∀ x : Fin 5 → Bool, encode x < 32 := by decide +kernel
theorem encode_bit : ∀ (x : Fin 5 → Bool) (i : Fin 5), (encode x).testBit i.val = x i := by decide +kernel
theorem encode_weight : ∀ x : Fin 5 → Bool, wt (encode x) = (Finset.univ.filter (fun i => x i)).card := by
  decide +kernel
theorem weight_two : ∀ (r : Fin 32) (a b : Fin 5), a ≠ b → r.val.testBit a.val = true →
    r.val.testBit b.val = true → 2 ≤ wt r.val := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 5000000 in
theorem weight_shared : ∀ a b : Fin 32,
    (∀ i j : Fin 5, a.val.testBit i.val = true → b.val.testBit i.val = true →
      a.val.testBit j.val = true → b.val.testBit j.val = true → i = j) → wt (a.val &&& b.val) ≤ 1 := by
  decide +kernel

def mask (E : Matrix 5 5) (i : Fin 5) : Nat := encode fun j => decide ((i,j) ∈ E)

theorem bit_iff (E : Matrix 5 5) (i j : Fin 5) : (mask E i).testBit j.val = true ↔ (i,j) ∈ E := by
  simp [mask,encode_bit]

theorem wt_fiber (E : Matrix 5 5) (i : Fin 5) :
    wt (mask E i) = (E.filter (fun p => p.1 = i)).card := by
  let T := Finset.univ.filter (fun j : Fin 5 => (i,j) ∈ E)
  have eq : E.filter (fun p => p.1 = i) = T.image (Prod.mk i) := by
    ext p
    constructor
    · rintro h
      obtain ⟨he,pi⟩ := Finset.mem_filter.mp h
      exact Finset.mem_image.mpr ⟨p.2,Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simpa [← pi] using he⟩,
        Prod.ext pi.symm rfl⟩
    · intro h
      obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp h
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hj).2,rfl⟩
  have wt_eq := encode_weight (fun j : Fin 5 => decide ((i,j) ∈ E))
  rw [eq,Finset.card_image_of_injective _ (fun j k h => congrArg Prod.snd h)]
  simpa [mask,T] using wt_eq

theorem separated (E : Matrix 5 5) (free : FourFree E) (p q : Fin 5) (ne : p ≠ q) :
    wt (mask E p &&& mask E q) ≤ 1 := by
  apply weight_shared ⟨mask E p,encode_bound _⟩ ⟨mask E q,encode_bound _⟩
  intro i j pi qi pj qj
  by_contra ij
  exact free p q i j ne ij ⟨(bit_iff E p i).mp pi,(bit_iff E p j).mp pj,
    (bit_iff E q i).mp qi,(bit_iff E q j).mp qj⟩

theorem row_bounds (E : Matrix 5 5) (rich : HasPartners E) (p : Fin 5) (hp : p ∈ Rows E) :
    0 < mask E p ∧ mask E p < 32 ∧ 2 ≤ wt (mask E p) := by
  obtain ⟨⟨a,b⟩,ab,eq⟩ := Finset.mem_image.mp hp
  change a = p at eq
  subst a
  obtain ⟨c,cb,pc⟩ := (rich p b ab).1
  have positive : mask E p ≠ 0 := by
    intro bad
    have bit := (bit_iff E p b).mpr ab
    simp [bad] at bit
  exact ⟨Nat.pos_of_ne_zero positive,encode_bound _,
    weight_two ⟨mask E p,encode_bound _⟩ c b cb ((bit_iff E p c).mpr pc) ((bit_iff E p b).mpr ab)⟩

theorem mask_inj (E : Matrix 5 5) (free : FourFree E) (rich : HasPartners E) :
    Set.InjOn (mask E) (Rows E : Set (Fin 5)) := by
  intro a ha b _ eq
  by_contra ne
  have cap := separated E free a b ne
  rw [← eq,Nat.and_self] at cap
  have low := (row_bounds E rich a ha).2.2
  omega

theorem sum_list (xs : List Nat) (f : Nat → Nat) (distinct : xs.Nodup) :
    (xs.map f).sum = ∑ i ∈ xs.toFinset, f i := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    have h := List.nodup_cons.mp distinct
    simp [h.1,ih h.2]

def SortedProof := ∀ xs : List Nat, xs ≠ [] → xs.length ≤ 5 →
  (∀ r ∈ xs, 0 < r ∧ r < 32 ∧ 2 ≤ wt r) → (xs.map wt).sum ≤ 10 →
  xs.Pairwise Compatible → liveCols xs = true → Counts (matrix xs)

theorem census_of_sorted (done : SortedProof) : MatrixPacking3241.Census := by
  classical
  intro E size free last
  by_cases zero : E = ∅
  · have ac : (bip E).IsAcyclic := by
      have bot : bip E = ⊥ := by
        apply SimpleGraph.eq_bot_iff_forall_not_adj.mpr
        intro i j h
        rcases h with ⟨_,⟨e,he,_,_⟩ | ⟨e,he,_,_⟩⟩ <;> simp [zero] at he
      rw [bot]
      exact SimpleGraph.isAcyclic_bot
    exact forest_counts _ ac
  have rich := (leafless_iff E).mp last
  let A := (Rows E).image (mask E)
  let xs := A.sort
  have inj := mask_inj E free rich
  have cap : A.card ≤ 5 := (Finset.card_image_le).trans (Finset.card_le_univ (Rows E))
  have len : xs.length ≤ 5 := by simpa [xs] using cap
  have mem (r : Nat) : r ∈ xs ↔ ∃ p ∈ Rows E, mask E p = r := by simp [xs,A]
  have nonempty : xs ≠ [] := by
    obtain ⟨e,he⟩ := Finset.nonempty_iff_ne_empty.mpr zero
    have hm := (mem _).mpr ⟨e.1,Finset.mem_image_of_mem _ he,rfl⟩
    intro eq
    simp [eq] at hm
  have rn : ∀ r ∈ xs, 0 < r ∧ r < 32 ∧ 2 ≤ wt r := by
    intro r hr
    obtain ⟨p,hp,rfl⟩ := (mem r).mp hr
    exact row_bounds E rich p hp
  have total : (xs.map wt).sum = E.card := by
    rw [sum_list _ _ (A.sort_nodup _)]
    have eq : xs.toFinset = A := by ext r; simp [xs]
    rw [eq,Finset.sum_image]
    · rw [Finset.card_eq_sum_card_image Prod.fst E]
      exact Finset.sum_congr rfl (fun x _ => wt_fiber E x)
    · exact inj
  have sorted : xs.Pairwise (· < ·) := A.sortedLT_sort.pairwise
  have pair : xs.Pairwise Compatible := by
    apply sorted.imp_of_mem
    intro a b ha hb lt
    obtain ⟨p,_,rfl⟩ := (mem a).mp ha
    obtain ⟨q,_,rfl⟩ := (mem b).mp hb
    exact ⟨lt,separated E free p q (fun eq => (Nat.ne_of_lt lt) (congrArg (mask E) eq))⟩
  have cols : liveCols xs = true := by
    apply List.all_eq_true.mpr
    intro j hj
    apply decide_eq_true
    intro unique
    have pos : 0 < xs.countP (fun r => r.testBit j) := by omega
    obtain ⟨r,hr,bit⟩ := List.countP_pos_iff.mp pos
    obtain ⟨p,hp,rfl⟩ := (mem r).mp hr
    let c : Fin 5 := ⟨j,List.mem_range.mp hj⟩
    have pc : (p,c) ∈ E := (bit_iff E p c).mp bit
    obtain ⟨q,qp,qc⟩ := (rich p c pc).2
    have hq : q ∈ Rows E := Finset.mem_image_of_mem Prod.fst qc
    have hq' := (mem _).mpr ⟨q,hq,rfl⟩
    have diff := ThetaPin3241.count_one_unique xs (fun a => a.testBit j) _ _ hq' hr
      ((bit_iff E q c).mpr qc) bit (by omega)
    exact qp (inj hq hp diff)
  have ok := done xs nonempty len rn (total ▸ size) pair cols
  let val (p : Rows E) : A := ⟨mask E p.val,Finset.mem_image_of_mem _ p.property⟩
  have bij : Function.Bijective val := by
    refine ⟨fun p q eq => Subtype.ext (inj p.property q.property (congrArg Subtype.val eq)),?_⟩
    intro a
    obtain ⟨p,hp,eq⟩ := Finset.mem_image.mp a.property
    exact ⟨⟨p,hp⟩,Subtype.ext eq⟩
  let order := (Equiv.ofBijective val bij).trans ((A.orderIsoOfFin rfl).symm.toEquiv)
  let r (p : Rows E) : Fin 5 := (order p).castLE cap
  have ri : Function.Injective r := (Fin.castLE_injective cap).comp order.injective
  let c (p : Cols E) : Fin 5 := p.val
  have read (p : Rows E) : xs.getD (r p).val 0 = mask E p.val := by
    have hl : (r p).val < xs.length := by simp [xs,r]
    rw [List.getD_eq_getElem _ _ hl]
    have ev := congrArg Subtype.val ((A.orderIsoOfFin rfl).apply_symm_apply (val p))
    exact ev
  have pe : pack E r c = pairs xs := by
    ext ij
    obtain ⟨i,j⟩ := ij
    change (i,j) ∈ pack E r c ↔ (i,j) ∈ pairs xs
    rw [decode]
    simp only [pairs,Finset.mem_filter,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨e,rfl,rfl⟩
      rw [read]
      exact (bit_iff E _ _).mpr e.property
    · intro bit
      have hl : i.val < xs.length := by
        by_contra! bad
        rw [List.getD_eq_default _ _ bad] at bit
        simp at bit
      have ha : i.val < A.card := by simpa [xs] using hl
      let p := order.symm ⟨i.val,ha⟩
      have pos : r p = i := Fin.ext (by simp [r,p])
      rw [← pos,read] at bit
      have cell := (bit_iff E p.val j).mp bit
      let e : E := ⟨(p.val,j),cell⟩
      exact ⟨e,pos,rfl⟩
  apply unpack_counts E r c ri Subtype.val_injective
  rw [pe]
  exact ok

theorem census : MatrixPacking3241.Census := census_of_sorted CoreCensus.sorted_counts

end NormalizeCores3241

end PEqualNP.Outside.L_meta_18065.Census.Core.Ten

namespace PEqualNP.Outside.L_meta_18065.Census.Core.Ten

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm
open LeafCore3241 ForestBipartite3241 GraphPacking3241 MatrixPacking3241

end PEqualNP.Outside.L_meta_18065.Census.Core.Ten

namespace PEqualNP.Outside.L_meta_18065.Census.Core.Puncture

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.EdgeOwnership

private def stepW (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private lemma foldl_stepW_len (gs : List Gate) (inp : List Bool) :
    (gs.foldl stepW inp).length = inp.length + gs.length := by
  induction gs generalizing inp with
  | nil => simp
  | cons g rest ih =>
    simp [List.foldl, stepW, ih]
    omega

private lemma getD_append_left (l1 l2 : List Bool) (i : ℕ) (hi : i < l1.length) :
    (l1 ++ l2).getD i false = l1.getD i false := by
  simp [List.getD, List.getElem?_append_left hi]

private lemma getD_append_self (l1 : List Bool) (b : Bool) :
    (l1 ++ [b]).getD l1.length false = b := by
  simp [List.getD]

private lemma getD_of_ge (l : List Bool) (i : ℕ) (hi : l.length ≤ i) :
    l.getD i false = false := by
  simp [List.getD, List.getElem?_eq_none hi]

private lemma getD_ofFn {n : ℕ} (z : Fin n → Bool) (i : ℕ) (hi : i < n) :
    (List.ofFn z).getD i false = z ⟨i, hi⟩ := by
  simp [List.getD, hi]

private def wireVal (n : ℕ) (gs : List Gate) (z : Fin n → Bool) (i : ℕ) : Bool :=
  (gs.foldl stepW (List.ofFn z)).getD i false

private lemma wireVal_append_gate_lt (n : ℕ) (gs : List Gate) (g : Gate) (z : Fin n → Bool)
    (i : ℕ) (hi : i < n + gs.length) :
    wireVal n (gs ++ [g]) z i = wireVal n gs z i := by
  unfold wireVal
  rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hlen : (gs.foldl stepW (List.ofFn z)).length = n + gs.length := by
    rw [foldl_stepW_len, List.length_ofFn]
  exact getD_append_left _ _ i (by omega)

private lemma wireVal_append_gate_self (n : ℕ) (gs : List Gate) (g : Gate) (z : Fin n → Bool) :
    wireVal n (gs ++ [g]) z (n + gs.length) =
      g.op.eval (g.inputs.map (fun i => wireVal n gs z i)) := by
  unfold wireVal
  rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hlen : (gs.foldl stepW (List.ofFn z)).length = n + gs.length := by
    rw [foldl_stepW_len, List.length_ofFn]
  rw [← hlen]
  exact getD_append_self (gs.foldl stepW (List.ofFn z)) _

private def gateAtL (gs : List Gate) (j : ℕ) : Gate :=
  gs.getD j ⟨GateOp.or, []⟩

private lemma gateAtL_append_lt (gs : List Gate) (g : Gate) (j : ℕ) (hj : j < gs.length) :
    gateAtL (gs ++ [g]) j = gateAtL gs j := by
  simp [gateAtL, List.getD, List.getElem?_append_left hj]

private lemma gateAtL_append_self (gs : List Gate) (g : Gate) :
    gateAtL (gs ++ [g]) gs.length = g := by
  simp [gateAtL, List.getD]

private def Good (x1 x2 : ℕ) (S : Bool → Finset ℕ) (gs : List Gate) : Prop :=
  (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∧
  (∀ j < gs.length, ∀ i ∈ (gateAtL gs j).inputs, i < x1 + x2 + j) ∧
  (∀ b : Bool, ∀ w ∈ S b, w < x1 + x2 + gs.length) ∧
  (∀ b : Bool, ∀ w ∈ S b,
    (w < x1 + x2 ∧ decide (x1 ≤ w) = b) ∨
    ∃ j < gs.length, w = x1 + x2 + j ∧ (gateAtL gs j).op = GateOp.or ∧
      ∀ u ∈ (gateAtL gs j).inputs, u ∈ S b) ∧
  (∀ j < gs.length, (gateAtL gs j).op = GateOp.and →
    ∃ a c : ℕ, ∃ b : Bool, (gateAtL gs j).inputs = [a, c] ∧ a ∈ S b ∧ c ∈ S (!b))

private def S0 (x1 x2 : ℕ) (b : Bool) : Finset ℕ :=
  if b then Finset.Ico x1 (x1 + x2) else Finset.range x1

private lemma good_init (x1 x2 : ℕ) : Good x1 x2 (S0 x1 x2) [] := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro g hg; cases hg
  · intro j hj; simp at hj
  · intro b w hw
    cases b <;> simp [S0] at hw <;> omega
  · intro b w hw
    left
    cases b <;> simp [S0] at hw
    · exact ⟨by omega, by simp [show ¬(x1 ≤ w) by omega]⟩
    · exact ⟨hw.2, by simp [hw.1]⟩
  · intro j hj; simp at hj

private lemma mem_S0_false {x1 x2 : ℕ} (p : Fin x1) : p.1 ∈ S0 x1 x2 false := by
  simp [S0, p.2]

private lemma mem_S0_true {x1 x2 : ℕ} (l : Fin x2) : x1 + l.1 ∈ S0 x1 x2 true := by
  simp [S0]

private lemma good_append_or_side {x1 x2 : ℕ} {S : Bool → Finset ℕ} {gs : List Gate}
    (hG : Good x1 x2 S gs) (b : Bool) {u v : ℕ} (hu : u ∈ S b) (hv : v ∈ S b) :
    let w := x1 + x2 + gs.length
    let S' : Bool → Finset ℕ := fun b' => if b' = b then insert w (S b') else S b'
    Good x1 x2 S' (gs ++ [⟨GateOp.or, [u, v]⟩]) := by
  rcases hG with ⟨hAO, hRB, hLt, hSide, hAnd⟩
  have hu_lt : u < x1 + x2 + gs.length := hLt b u hu
  have hv_lt : v < x1 + x2 + gs.length := hLt b v hv
  dsimp only
  have hSub : ∀ b' : Bool, S b' ⊆ (if b' = b then insert (x1 + x2 + gs.length) (S b') else S b') := by
    intro b'
    by_cases hbb : b' = b
    · simp [hbb]
    · simp [hbb]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | rfl
    · exact hAO g hg
    · exact ⟨Or.inr rfl, rfl⟩
  · intro j hj i hi
    simp only [List.length_append, List.length_singleton] at hj
    by_cases hlt : j < gs.length
    · rw [gateAtL_append_lt _ _ _ hlt] at hi
      exact hRB j hlt i hi
    · have hjeq : j = gs.length := by omega
      subst hjeq
      rw [gateAtL_append_self] at hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl <;> omega
  · intro b' w hw
    simp only [List.length_append, List.length_singleton]
    by_cases hbb : b' = b
    · simp only [hbb, ite_true, Finset.mem_insert] at hw
      rcases hw with rfl | hw
      · omega
      · have := hLt b w hw; omega
    · simp only [hbb, ite_false] at hw
      have := hLt b' w hw; omega
  · intro b' w hw
    by_cases hbb : b' = b
    · subst hbb
      simp only [ite_true, Finset.mem_insert] at hw
      rcases hw with rfl | hw
      · right
        refine ⟨gs.length, by simp, rfl, ?_, ?_⟩
        · rw [gateAtL_append_self]
        · rw [gateAtL_append_self]
          intro t ht
          simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
          rcases ht with rfl | rfl
          · exact hSub b' hu
          · exact hSub b' hv
      · rcases hSide b' w hw with h1 | ⟨j, hj, hweq, hop, hin⟩
        · exact Or.inl h1
        · right
          refine ⟨j, by simp; omega, hweq, ?_, ?_⟩
          · rw [gateAtL_append_lt _ _ _ hj]; exact hop
          · rw [gateAtL_append_lt _ _ _ hj]
            intro t ht
            exact hSub b' (hin t ht)
    · simp only [hbb, ite_false] at hw
      rcases hSide b' w hw with h1 | ⟨j, hj, hweq, hop, hin⟩
      · exact Or.inl h1
      · right
        refine ⟨j, by simp; omega, hweq, ?_, ?_⟩
        · rw [gateAtL_append_lt _ _ _ hj]; exact hop
        · rw [gateAtL_append_lt _ _ _ hj]
          intro t ht
          simp only [hbb, ite_false]
          exact hin t ht
  · intro j hj hop
    simp only [List.length_append, List.length_singleton] at hj
    by_cases hlt : j < gs.length
    · rw [gateAtL_append_lt _ _ _ hlt] at hop ⊢
      rcases hAnd j hlt hop with ⟨a, c, b0, hin, ha, hc⟩
      exact ⟨a, c, b0, hin, hSub b0 ha, hSub (!b0) hc⟩
    · have hjeq : j = gs.length := by omega
      subst hjeq
      rw [gateAtL_append_self] at hop
      cases hop

private lemma good_append_or_top {x1 x2 : ℕ} {S : Bool → Finset ℕ} {gs : List Gate}
    (hG : Good x1 x2 S gs) {u v : ℕ} (hu : u < x1 + x2 + gs.length) (hv : v < x1 + x2 + gs.length) :
    Good x1 x2 S (gs ++ [⟨GateOp.or, [u, v]⟩]) := by
  rcases hG with ⟨hAO, hRB, hLt, hSide, hAnd⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | rfl
    · exact hAO g hg
    · exact ⟨Or.inr rfl, rfl⟩
  · intro j hj i hi
    simp only [List.length_append, List.length_singleton] at hj
    by_cases hlt : j < gs.length
    · rw [gateAtL_append_lt _ _ _ hlt] at hi
      exact hRB j hlt i hi
    · have hjeq : j = gs.length := by omega
      subst hjeq
      rw [gateAtL_append_self] at hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl <;> omega
  · intro b w hw
    simp only [List.length_append, List.length_singleton]
    have := hLt b w hw; omega
  · intro b w hw
    rcases hSide b w hw with h1 | ⟨j, hj, hweq, hop, hin⟩
    · exact Or.inl h1
    · right
      refine ⟨j, by simp; omega, hweq, ?_, ?_⟩
      · rw [gateAtL_append_lt _ _ _ hj]; exact hop
      · rw [gateAtL_append_lt _ _ _ hj]; exact hin
  · intro j hj hop
    simp only [List.length_append, List.length_singleton] at hj
    by_cases hlt : j < gs.length
    · rw [gateAtL_append_lt _ _ _ hlt] at hop ⊢
      exact hAnd j hlt hop
    · have hjeq : j = gs.length := by omega
      subst hjeq
      rw [gateAtL_append_self] at hop
      cases hop

private lemma good_append_and {x1 x2 : ℕ} {S : Bool → Finset ℕ} {gs : List Gate}
    (hG : Good x1 x2 S gs) (b : Bool) {a c : ℕ} (ha : a ∈ S b) (hc : c ∈ S (!b)) :
    Good x1 x2 S (gs ++ [⟨GateOp.and, [a, c]⟩]) := by
  rcases hG with ⟨hAO, hRB, hLt, hSide, hAnd⟩
  have ha_lt : a < x1 + x2 + gs.length := hLt b a ha
  have hc_lt : c < x1 + x2 + gs.length := hLt (!b) c hc
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | rfl
    · exact hAO g hg
    · exact ⟨Or.inl rfl, rfl⟩
  · intro j hj i hi
    simp only [List.length_append, List.length_singleton] at hj
    by_cases hlt : j < gs.length
    · rw [gateAtL_append_lt _ _ _ hlt] at hi
      exact hRB j hlt i hi
    · have hjeq : j = gs.length := by omega
      subst hjeq
      rw [gateAtL_append_self] at hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl <;> omega
  · intro b' w hw
    simp only [List.length_append, List.length_singleton]
    have := hLt b' w hw; omega
  · intro b' w hw
    rcases hSide b' w hw with h1 | ⟨j, hj, hweq, hop, hin⟩
    · exact Or.inl h1
    · right
      refine ⟨j, by simp; omega, hweq, ?_, ?_⟩
      · rw [gateAtL_append_lt _ _ _ hj]; exact hop
      · rw [gateAtL_append_lt _ _ _ hj]; exact hin
  · intro j hj hop
    simp only [List.length_append, List.length_singleton] at hj
    by_cases hlt : j < gs.length
    · rw [gateAtL_append_lt _ _ _ hlt] at hop ⊢
      exact hAnd j hlt hop
    · have hjeq : j = gs.length := by omega
      subst hjeq
      rw [gateAtL_append_self]
      exact ⟨a, c, b, rfl, ha, hc⟩

private lemma addOrInSide {x1 x2 : ℕ} (b : Bool) (ws : List ℕ) (hne : ws ≠ []) :
    ∀ (S : Bool → Finset ℕ) (gs : List Gate),
      Good x1 x2 S gs →
      (∀ u ∈ ws, u ∈ S b) →
      ∃ (S' : Bool → Finset ℕ) (gs' : List Gate) (w : ℕ),
        gs'.length = gs.length + (ws.length - 1) ∧
        Good x1 x2 S' gs' ∧
        (∀ b', S b' ⊆ S' b') ∧
        w ∈ S' b ∧
        (∀ z i, i < x1 + x2 + gs.length → wireVal (x1 + x2) gs' z i = wireVal (x1 + x2) gs z i) ∧
        (∀ z, wireVal (x1 + x2) gs' z w = ws.any (fun u => wireVal (x1 + x2) gs z u)) := by
  induction ws with
  | nil => exact absurd rfl hne
  | cons u rest ih =>
    intro S gs hG hws
    cases rest with
    | nil =>
      refine ⟨S, gs, u, by simp, hG, fun _ => Finset.Subset.rfl, hws u (by simp), ?_, ?_⟩
      · intro z i _; rfl
      · intro z; simp
    | cons v rest' =>
      have hne' : v :: rest' ≠ [] := List.cons_ne_nil v rest'
      have hws' : ∀ t ∈ v :: rest', t ∈ S b := fun t ht => hws t (List.mem_cons_of_mem u ht)
      rcases ih hne' S gs hG hws' with ⟨S1, gs1, w1, hlen1, hG1, hSub1, hw1, hPres1, hVal1⟩
      have hu1 : u ∈ S1 b := hSub1 b (hws u (by simp))
      let w := x1 + x2 + gs1.length
      let gs2 := gs1 ++ [⟨GateOp.or, [u, w1]⟩]
      let S2 : Bool → Finset ℕ := fun b' => if b' = b then insert w (S1 b') else S1 b'
      have hG2 : Good x1 x2 S2 gs2 := good_append_or_side hG1 b hu1 hw1
      have hSub2 : ∀ b', S b' ⊆ S2 b' := by
        intro b'
        refine Finset.Subset.trans (hSub1 b') ?_
        by_cases hbb : b' = b
        · simp [S2, hbb]
        · simp [S2, hbb]
      have hw2 : w ∈ S2 b := by simp [S2]
      have hu_lt : u < x1 + x2 + gs.length := hG.2.2.1 b u (hws u (by simp))
      refine ⟨S2, gs2, w, ?_, hG2, hSub2, hw2, ?_, ?_⟩
      · simp [gs2, hlen1]; omega
      · intro z i hi
        have hi1 : i < x1 + x2 + gs1.length := by omega
        rw [wireVal_append_gate_lt _ _ _ _ _ hi1]
        exact hPres1 z i hi
      · intro z
        rw [wireVal_append_gate_self]
        simp only [List.map, GateOp.eval, List.any_cons]
        rw [hPres1 z u hu_lt, hVal1 z]
        simp

private lemma addOrTop {x1 x2 : ℕ} (ws : List ℕ) (hne : ws ≠ []) :
    ∀ (S : Bool → Finset ℕ) (gs : List Gate),
      Good x1 x2 S gs →
      (∀ u ∈ ws, u < x1 + x2 + gs.length) →
      ∃ (gs' : List Gate) (w : ℕ),
        gs'.length = gs.length + (ws.length - 1) ∧
        Good x1 x2 S gs' ∧
        w < x1 + x2 + gs'.length ∧
        (∀ z i, i < x1 + x2 + gs.length → wireVal (x1 + x2) gs' z i = wireVal (x1 + x2) gs z i) ∧
        (∀ z, wireVal (x1 + x2) gs' z w = ws.any (fun u => wireVal (x1 + x2) gs z u)) := by
  induction ws with
  | nil => exact absurd rfl hne
  | cons u rest ih =>
    intro S gs hG hws
    cases rest with
    | nil =>
      refine ⟨gs, u, by simp, hG, hws u (by simp), ?_, ?_⟩
      · intro z i _; rfl
      · intro z; simp
    | cons v rest' =>
      have hne' : v :: rest' ≠ [] := List.cons_ne_nil v rest'
      have hws' : ∀ t ∈ v :: rest', t < x1 + x2 + gs.length :=
        fun t ht => hws t (List.mem_cons_of_mem u ht)
      rcases ih hne' S gs hG hws' with ⟨gs1, w1, hlen1, hG1, hw1, hPres1, hVal1⟩
      have hu_lt : u < x1 + x2 + gs.length := hws u (by simp)
      have hu1 : u < x1 + x2 + gs1.length := by omega
      let w := x1 + x2 + gs1.length
      let gs2 := gs1 ++ [⟨GateOp.or, [u, w1]⟩]
      have hG2 : Good x1 x2 S gs2 := good_append_or_top hG1 hu1 hw1
      refine ⟨gs2, w, ?_, hG2, ?_, ?_, ?_⟩
      · simp [gs2, hlen1]; omega
      · simp [gs2, w]
      · intro z i hi
        have hi1 : i < x1 + x2 + gs1.length := by omega
        rw [wireVal_append_gate_lt _ _ _ _ _ hi1]
        exact hPres1 z i hi
      · intro z
        rw [wireVal_append_gate_self]
        simp only [List.map, GateOp.eval, List.any_cons]
        rw [hPres1 z u hu_lt, hVal1 z]
        simp

private abbrev Star (x1 x2 : ℕ) := (Fin x1 × List (Fin x2)) ⊕ (Fin x2 × List (Fin x1))

private def starSize {x1 x2 : ℕ} : Star x1 x2 → ℕ
  | Sum.inl (_, ls) => ls.length
  | Sum.inr (_, ps) => ps.length

private def starEval {x1 x2 : ℕ} (z : Fin (x1 + x2) → Bool) : Star x1 x2 → Bool
  | Sum.inl (p, ls) => z (Fin.castAdd x2 p) && ls.any (fun l => z (Fin.natAdd x1 l))
  | Sum.inr (l, ps) => ps.any (fun p => z (Fin.castAdd x2 p)) && z (Fin.natAdd x1 l)

private lemma wireVal_input_left {x1 x2 : ℕ} (gs : List Gate) (z : Fin (x1 + x2) → Bool)
    (p : Fin x1) :
    wireVal (x1 + x2) gs z p.1 = z (Fin.castAdd x2 p) := by
  induction gs using List.reverseRecOn with
  | nil =>
    unfold wireVal
    simp only [List.foldl_nil]
    have hlt : p.1 < x1 + x2 := by omega
    rw [getD_ofFn z p.1 hlt]
    rfl
  | append_singleton gs g ih =>
    rw [wireVal_append_gate_lt _ _ _ _ _ (by omega)]
    exact ih

private lemma wireVal_input_right {x1 x2 : ℕ} (gs : List Gate) (z : Fin (x1 + x2) → Bool)
    (l : Fin x2) :
    wireVal (x1 + x2) gs z (x1 + l.1) = z (Fin.natAdd x1 l) := by
  induction gs using List.reverseRecOn with
  | nil =>
    unfold wireVal
    simp only [List.foldl_nil]
    have hlt : x1 + l.1 < x1 + x2 := by omega
    rw [getD_ofFn z (x1 + l.1) hlt]
    rfl
  | append_singleton gs g ih =>
    rw [wireVal_append_gate_lt _ _ _ _ _ (by omega)]
    exact ih

private lemma addStar {x1 x2 : ℕ} (st : Star x1 x2) (hpos : 0 < starSize st)
    (S : Bool → Finset ℕ) (gs : List Gate)
    (hG : Good x1 x2 S gs) (hBase : ∀ b, S0 x1 x2 b ⊆ S b) :
    ∃ (S' : Bool → Finset ℕ) (gs' : List Gate) (w : ℕ),
      gs'.length = gs.length + starSize st ∧
      Good x1 x2 S' gs' ∧
      (∀ b, S b ⊆ S' b) ∧
      w < x1 + x2 + gs'.length ∧
      (∀ z i, i < x1 + x2 + gs.length → wireVal (x1 + x2) gs' z i = wireVal (x1 + x2) gs z i) ∧
      (∀ z, wireVal (x1 + x2) gs' z w = starEval z st) := by
  cases st with
  | inl pl =>
    rcases pl with ⟨p, ls⟩
    have hne_ls : ls ≠ [] := by
      intro h; simp [starSize, h] at hpos
    let ws : List ℕ := ls.map (fun l => x1 + l.1)
    have hne_ws : ws ≠ [] := by
      simp [ws, hne_ls]
    have hws_mem : ∀ u ∈ ws, u ∈ S true := by
      intro u hu
      simp only [ws, List.mem_map] at hu
      rcases hu with ⟨l, _, rfl⟩
      exact hBase true (mem_S0_true l)
    rcases addOrInSide true ws hne_ws S gs hG hws_mem with
      ⟨S1, gs1, wL, hlen1, hG1, hSub1, hwL, hPres1, hVal1⟩
    have hp1 : p.1 ∈ S1 false := hSub1 false (hBase false (mem_S0_false p))
    let w := x1 + x2 + gs1.length
    let gs2 := gs1 ++ [⟨GateOp.and, [p.1, wL]⟩]
    have hG2 : Good x1 x2 S1 gs2 := good_append_and hG1 false hp1 hwL
    refine ⟨S1, gs2, w, ?_, hG2, hSub1, ?_, ?_, ?_⟩
    · simp only [gs2, List.length_append, List.length_singleton, hlen1, ws, List.length_map,
        starSize]
      have : 0 < ls.length := by simpa [starSize] using hpos
      omega
    · simp [gs2, w]
    · intro z i hi
      have hi1 : i < x1 + x2 + gs1.length := by omega
      rw [wireVal_append_gate_lt _ _ _ _ _ hi1]
      exact hPres1 z i hi
    · intro z
      rw [wireVal_append_gate_self]
      simp only [List.map, GateOp.eval, starEval]
      rw [wireVal_input_left, hVal1 z]
      simp only [ws, List.any_map]
      have hfn : (fun l : Fin x2 => wireVal (x1 + x2) gs z (x1 + l.1)) =
          (fun l : Fin x2 => z (Fin.natAdd x1 l)) := by
        funext l
        exact wireVal_input_right gs z l
      simp [Function.comp_def, hfn]
  | inr lp =>
    rcases lp with ⟨l, ps⟩
    have hne_ps : ps ≠ [] := by
      intro h; simp [starSize, h] at hpos
    let ws : List ℕ := ps.map (fun p => p.1)
    have hne_ws : ws ≠ [] := by
      simp [ws, hne_ps]
    have hws_mem : ∀ u ∈ ws, u ∈ S false := by
      intro u hu
      simp only [ws, List.mem_map] at hu
      rcases hu with ⟨p, _, rfl⟩
      exact hBase false (mem_S0_false p)
    rcases addOrInSide false ws hne_ws S gs hG hws_mem with
      ⟨S1, gs1, wP, hlen1, hG1, hSub1, hwP, hPres1, hVal1⟩
    have hl1 : x1 + l.1 ∈ S1 true := hSub1 true (hBase true (mem_S0_true l))
    let w := x1 + x2 + gs1.length
    let gs2 := gs1 ++ [⟨GateOp.and, [wP, x1 + l.1]⟩]
    have hG2 : Good x1 x2 S1 gs2 := good_append_and hG1 false hwP hl1
    refine ⟨S1, gs2, w, ?_, hG2, hSub1, ?_, ?_, ?_⟩
    · simp only [gs2, List.length_append, List.length_singleton, hlen1, ws, List.length_map,
        starSize]
      have : 0 < ps.length := by simpa [starSize] using hpos
      omega
    · simp [gs2, w]
    · intro z i hi
      have hi1 : i < x1 + x2 + gs1.length := by omega
      rw [wireVal_append_gate_lt _ _ _ _ _ hi1]
      exact hPres1 z i hi
    · intro z
      rw [wireVal_append_gate_self]
      simp only [List.map, GateOp.eval, starEval]
      rw [wireVal_input_right, hVal1 z]
      simp only [ws, List.any_map]
      have hfn : (fun p : Fin x1 => wireVal (x1 + x2) gs z p.1) =
          (fun p : Fin x1 => z (Fin.castAdd x2 p)) := by
        funext p
        exact wireVal_input_left gs z p
      simp [Function.comp_def, hfn]

private lemma addStars {x1 x2 : ℕ} (stars : List (Star x1 x2))
    (hpos : ∀ st ∈ stars, 0 < starSize st) :
    ∀ (S : Bool → Finset ℕ) (gs : List Gate),
      Good x1 x2 S gs →
      (∀ b, S0 x1 x2 b ⊆ S b) →
      ∃ (S' : Bool → Finset ℕ) (gs' : List Gate) (ws : List ℕ),
        gs'.length = gs.length + (stars.map starSize).sum ∧
        ws.length = stars.length ∧
        Good x1 x2 S' gs' ∧
        (∀ w ∈ ws, w < x1 + x2 + gs'.length) ∧
        (∀ z i, i < x1 + x2 + gs.length → wireVal (x1 + x2) gs' z i = wireVal (x1 + x2) gs z i) ∧
        (∀ z, ws.any (fun w => wireVal (x1 + x2) gs' z w) = stars.any (fun st => starEval z st)) := by
  induction stars with
  | nil =>
    intro S gs hG _
    refine ⟨S, gs, [], by simp, rfl, hG, by simp, ?_, ?_⟩
    · intro z i _; rfl
    · intro z; simp
  | cons st rest ih =>
    intro S gs hG hBase
    rcases addStar st (hpos st (by simp)) S gs hG hBase with
      ⟨S1, gs1, w1, hlen1, hG1, hSub1, hw1, hPres1, hVal1⟩
    have hBase1 : ∀ b, S0 x1 x2 b ⊆ S1 b := fun b => Finset.Subset.trans (hBase b) (hSub1 b)
    have hpos_rest : ∀ s ∈ rest, 0 < starSize s := fun s hs => hpos s (List.mem_cons_of_mem st hs)
    rcases ih hpos_rest S1 gs1 hG1 hBase1 with
      ⟨S2, gs2, ws2, hlen2, hwslen2, hG2, hws2_lt, hPres2, hVal2⟩
    refine ⟨S2, gs2, w1 :: ws2, ?_, ?_, hG2, ?_, ?_, ?_⟩
    · simp [hlen2, hlen1, Nat.add_assoc]
    · simp [hwslen2]
    · intro w hw
      simp only [List.mem_cons] at hw
      rcases hw with rfl | hw
      · omega
      · exact hws2_lt w hw
    · intro z i hi
      have hi1 : i < x1 + x2 + gs1.length := by omega
      rw [hPres2 z i hi1]
      exact hPres1 z i hi
    · intro z
      simp only [List.any_cons]
      rw [hPres2 z w1 hw1, hVal1 z, hVal2 z]

private lemma circuit_from_good {x1 x2 : ℕ} (S : Bool → Finset ℕ) (gs : List Gate) (out : ℕ)
    (hG : Good x1 x2 S gs) :
    let C : Circuit := ⟨gs, out⟩
    IsAO2 (x1 + x2) C ∧
    (∀ b : Bool, ∀ w ∈ S b,
      (w < x1 + x2 ∧ decide (x1 ≤ w) = b) ∨
      ∃ j < C.size, w = x1 + x2 + j ∧ (gateAt C j).op = GateOp.or ∧
        ∀ u ∈ (gateAt C j).inputs, u ∈ S b) ∧
    (∀ j < C.size, (gateAt C j).op = GateOp.and →
      ∃ a c : ℕ, ∃ b : Bool, (gateAt C j).inputs = [a, c] ∧ a ∈ S b ∧ c ∈ S (!b)) := by
  rcases hG with ⟨hAO, hRB, _, hSide, hAnd⟩
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · intro g hg; exact (hAO g hg).1
  · intro j hj i hi; exact hRB j hj i hi
  · intro g hg; exact (hAO g hg).2
  · intro b w hw; exact hSide b w hw
  · intro j hj hop; exact hAnd j hj hop

end PEqualNP.Outside.L_meta_18065.Census.Core.Puncture

open PEqualNP.Outside.L_meta_18065.Census.Core.Puncture in
theorem PEqualNP.Outside.L_meta_18065.Census.Core.Puncture.stars :
    ∀ (x1 x2 : ℕ) (x3 : Finset (Fin x1 × Fin x2)) (x4 : Finset (Fin x1)) (x5 : Finset (Fin x2)),
      (∀ x6 ∈ x3, x6.1 ∈ x4 ∨ x6.2 ∈ x5) →
        ∃ (x7 : PEqualNP.CircuitLowerBounds.Circuit) (x8 : Bool → Finset ℕ),
          PEqualNP.TopForm.IsAO2 (x1 + x2) x7 ∧
            x7.size ≤ x3.card + x4.card + x5.card - (1 : ℕ) ∧
              (∀ (x9 : Fin (x1 + x2) → Bool),
                PEqualNP.MetaComplexity.circuitFun (x1 + x2) x7 x9 =
                  Decidable.decide
                    (∃ (x10 : Fin x1) (x11 : Fin x2),
                      (x10, x11) ∈ x3 ∧
                        x9 (Fin.castAdd x2 x10) = Bool.true ∧
                          x9 (Fin.natAdd x1 x11) = Bool.true)) ∧
                have x9 : ℕ → PEqualNP.CircuitLowerBounds.Gate :=
                  PEqualNP.MetaComplexity.NestedCover.gateAt x7;
                (∀ (x10 : Bool), ∀ x11 ∈ x8 x10,
                  x11 < x1 + x2 ∧ Decidable.decide (x1 ≤ x11) = x10 ∨
                    ∃ x13 < x7.size,
                      x11 = x1 + x2 + x13 ∧
                        (x9 x13).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧
                          ∀ x14 ∈ (x9 x13).inputs, x14 ∈ x8 x10) ∧
                  ∀ x10 < x7.size,
                    (x9 x10).op = PEqualNP.CircuitLowerBounds.GateOp.and →
                      ∃ (x13 : ℕ) (x14 : ℕ) (x15 : Bool),
                        (x9 x10).inputs = [x13, x14] ∧ x13 ∈ x8 x15 ∧ x14 ∈ x8 !x15 := by
  intro x1 x2 E A B hcov
  by_cases hE : E = ∅
  · subst hE
    refine ⟨⟨[], x1 + x2⟩, fun _ => ∅, ?_, ?_, ?_, ?_, ?_⟩
    · refine ⟨?_, ?_, ?_⟩
      · intro g hg; cases hg
      · intro j hj; simp at hj
      · intro g hg; cases hg
    · simp [PEqualNP.CircuitLowerBounds.Circuit.size]
    · intro z
      simp only [PEqualNP.MetaComplexity.circuitFun, PEqualNP.CircuitLowerBounds.Circuit.eval,
        PEqualNP.CircuitLowerBounds.Circuit.wires, List.foldl_nil, Finset.notMem_empty,
        false_and, exists_false, decide_false]
      exact getD_of_ge (List.ofFn z) (x1 + x2) (by simp)
    · intro b w hw; simp at hw
    · intro j hj; simp [PEqualNP.CircuitLowerBounds.Circuit.size] at hj
  · have hE_ne : E.Nonempty := Finset.nonempty_iff_ne_empty.mpr hE
    let NA : Fin x1 → Finset (Fin x2) := fun p => Finset.univ.filter (fun l => (p, l) ∈ E)
    let NB : Fin x2 → Finset (Fin x1) := fun l => Finset.univ.filter (fun p => (p, l) ∈ E ∧ p ∉ A)
    let A' : Finset (Fin x1) := A.filter (fun p => (NA p).Nonempty)
    let B' : Finset (Fin x2) := B.filter (fun l => (NB l).Nonempty)
    let starsA : List (Star x1 x2) := A'.toList.map (fun p => Sum.inl (p, (NA p).toList))
    let starsB : List (Star x1 x2) := B'.toList.map (fun l => Sum.inr (l, (NB l).toList))
    let stars : List (Star x1 x2) := starsA ++ starsB
    have hpos : ∀ st ∈ stars, 0 < starSize st := by
      intro st hst
      simp only [stars, starsA, starsB, List.mem_append, List.mem_map, Finset.mem_toList] at hst
      rcases hst with ⟨p, hp, rfl⟩ | ⟨l, hl, rfl⟩
      · simp only [starSize, Finset.length_toList]
        exact Finset.card_pos.mpr (Finset.mem_filter.mp hp).2
      · simp only [starSize, Finset.length_toList]
        exact Finset.card_pos.mpr (Finset.mem_filter.mp hl).2
    have hsumA : (starsA.map starSize).sum = ∑ p ∈ A', (NA p).card := by
      have h1 : (starsA.map starSize) = A'.toList.map (fun p => (NA p).card) := by
        simp [starsA, starSize, Function.comp_def]
      rw [h1, ← Multiset.sum_coe, ← Multiset.map_coe, Finset.coe_toList]
      rfl
    have hsumB : (starsB.map starSize).sum = ∑ l ∈ B', (NB l).card := by
      have h1 : (starsB.map starSize) = B'.toList.map (fun l => (NB l).card) := by
        simp [starsB, starSize, Function.comp_def]
      rw [h1, ← Multiset.sum_coe, ← Multiset.map_coe, Finset.coe_toList]
      rfl
    have hcardE : (∑ p ∈ A', (NA p).card) + (∑ l ∈ B', (NB l).card) = E.card := by
      let EA : Finset (Fin x1 × Fin x2) := A'.biUnion (fun p => (NA p).image (fun l => (p, l)))
      let EB : Finset (Fin x1 × Fin x2) := B'.biUnion (fun l => (NB l).image (fun p => (p, l)))
      have hEA_card : EA.card = ∑ p ∈ A', (NA p).card := by
        rw [Finset.card_biUnion]
        · refine Finset.sum_congr rfl ?_
          intro p _
          exact Finset.card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).2)
        · intro p1 _ p2 _ hne
          dsimp only [Function.onFun]
          rw [Finset.disjoint_left]
          intro e he1 he2
          simp only [Finset.mem_image] at he1 he2
          rcases he1 with ⟨l1, _, rfl⟩
          rcases he2 with ⟨l2, _, heq⟩
          exact hne (Prod.mk.inj heq).1.symm
      have hEB_card : EB.card = ∑ l ∈ B', (NB l).card := by
        rw [Finset.card_biUnion]
        · refine Finset.sum_congr rfl ?_
          intro l _
          exact Finset.card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).1)
        · intro l1 _ l2 _ hne
          dsimp only [Function.onFun]
          rw [Finset.disjoint_left]
          intro e he1 he2
          simp only [Finset.mem_image] at he1 he2
          rcases he1 with ⟨p1, _, rfl⟩
          rcases he2 with ⟨p2, _, heq⟩
          exact hne (Prod.mk.inj heq).2.symm
      have hdisj : Disjoint EA EB := by
        rw [Finset.disjoint_left]
        intro e he1 he2
        simp only [EA, EB, Finset.mem_biUnion, Finset.mem_image] at he1 he2
        rcases he1 with ⟨p1, hp1, l1, _, rfl⟩
        rcases he2 with ⟨l2, _, p2, hp2, heq⟩
        have hp_eq : p2 = p1 := (Prod.mk.inj heq).1
        subst hp_eq
        have hp1A : p2 ∈ A := (Finset.mem_filter.mp hp1).1
        have hp2nA : p2 ∉ A := (Finset.mem_filter.mp hp2).2.2
        exact hp2nA hp1A
      have hunion : EA ∪ EB = E := by
        ext ⟨p, l⟩
        simp only [EA, EB, Finset.mem_union, Finset.mem_biUnion, Finset.mem_image]
        constructor
        · rintro (⟨p1, _, l1, hl1, heq⟩ | ⟨l1, _, p1, hp1, heq⟩)
          · rcases Prod.mk.inj heq with ⟨rfl, rfl⟩
            exact (Finset.mem_filter.mp hl1).2
          · rcases Prod.mk.inj heq with ⟨rfl, rfl⟩
            exact (Finset.mem_filter.mp hp1).2.1
        · intro hpl
          by_cases hpA : p ∈ A
          · left
            refine ⟨p, Finset.mem_filter.mpr ⟨hpA, ⟨l, Finset.mem_filter.mpr ⟨Finset.mem_univ l, hpl⟩⟩⟩,
              l, Finset.mem_filter.mpr ⟨Finset.mem_univ l, hpl⟩, rfl⟩
          · right
            have hlB : l ∈ B := (hcov (p, l) hpl).resolve_left hpA
            refine ⟨l, Finset.mem_filter.mpr ⟨hlB, ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_univ p, hpl, hpA⟩⟩⟩,
              p, Finset.mem_filter.mpr ⟨Finset.mem_univ p, hpl, hpA⟩, rfl⟩
      rw [← hEA_card, ← hEB_card, ← Finset.card_union_of_disjoint hdisj, hunion]
    have hsum_stars : (stars.map starSize).sum = E.card := by
      simp only [stars, List.map_append, List.sum_append, hsumA, hsumB, hcardE]
    have hstars_len : stars.length = A'.card + B'.card := by
      simp [stars, starsA, starsB]
    have hstars_ne : stars ≠ [] := by
      intro hnil
      have h0 : E.card = 0 := by
        rw [← hsum_stars, hnil]; rfl
      exact (Finset.card_pos.mpr hE_ne).ne' h0
    rcases addStars stars hpos (S0 x1 x2) [] (good_init x1 x2) (fun _ => Finset.Subset.rfl) with
      ⟨S1, gs1, ws1, hlen1, hwslen1, hG1, hws1_lt, _, hVal1⟩
    have hws1_ne : ws1 ≠ [] := by
      intro hnil
      apply hstars_ne
      apply List.eq_nil_of_length_eq_zero
      rw [← hwslen1, hnil]
      rfl
    rcases addOrTop ws1 hws1_ne S1 gs1 hG1 hws1_lt with
      ⟨gs2, wOut, hlen2, hG2, _, hPres2, hVal2⟩
    let C : PEqualNP.CircuitLowerBounds.Circuit := ⟨gs2, wOut⟩
    have hC := circuit_from_good S1 gs2 wOut hG2
    refine ⟨C, S1, hC.1, ?_, ?_, hC.2.1, hC.2.2⟩
    · have hA' : A'.card ≤ A.card := Finset.card_filter_le _ _
      have hB' : B'.card ≤ B.card := Finset.card_filter_le _ _
      have hk_pos : 1 ≤ ws1.length := by
        cases ws1 with
        | nil => exact absurd rfl hws1_ne
        | cons _ _ => simp
      simp only [C, PEqualNP.CircuitLowerBounds.Circuit.size, hlen2, hlen1, List.length_nil,
        Nat.zero_add, hsum_stars, hwslen1, hstars_len]
      omega
    · intro z
      have hcf : PEqualNP.MetaComplexity.circuitFun (x1 + x2) C z = wireVal (x1 + x2) gs2 z wOut := rfl
      rw [hcf, hVal2 z, hVal1 z]
      apply Bool.eq_iff_iff.mpr
      simp only [List.any_eq_true, decide_eq_true_eq]
      constructor
      · rintro ⟨st, hst, hst_eval⟩
        simp only [stars, starsA, starsB, List.mem_append, List.mem_map, Finset.mem_toList] at hst
        rcases hst with ⟨p, _, rfl⟩ | ⟨l, _, rfl⟩
        · simp only [starEval, Bool.and_eq_true, List.any_eq_true, Finset.mem_toList] at hst_eval
          rcases hst_eval with ⟨hzp, l, hl, hzl⟩
          exact ⟨p, l, (Finset.mem_filter.mp hl).2, hzp, hzl⟩
        · simp only [starEval, Bool.and_eq_true, List.any_eq_true, Finset.mem_toList] at hst_eval
          rcases hst_eval with ⟨⟨p, hp, hzp⟩, hzl⟩
          exact ⟨p, l, (Finset.mem_filter.mp hp).2.1, hzp, hzl⟩
      · rintro ⟨p, l, hpl, hzp, hzl⟩
        by_cases hpA : p ∈ A
        · refine ⟨Sum.inl (p, (NA p).toList), ?_, ?_⟩
          · simp only [stars, starsA, List.mem_append, List.mem_map, Finset.mem_toList]
            left
            exact ⟨p, Finset.mem_filter.mpr ⟨hpA, ⟨l, Finset.mem_filter.mpr ⟨Finset.mem_univ l, hpl⟩⟩⟩, rfl⟩
          · simp only [starEval, Bool.and_eq_true, List.any_eq_true, Finset.mem_toList]
            exact ⟨hzp, l, Finset.mem_filter.mpr ⟨Finset.mem_univ l, hpl⟩, hzl⟩
        · have hlB : l ∈ B := (hcov (p, l) hpl).resolve_left hpA
          refine ⟨Sum.inr (l, (NB l).toList), ?_, ?_⟩
          · simp only [stars, starsB, List.mem_append, List.mem_map, Finset.mem_toList]
            right
            exact ⟨l, Finset.mem_filter.mpr ⟨hlB, ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_univ p, hpl, hpA⟩⟩⟩, rfl⟩
          · simp only [starEval, Bool.and_eq_true, List.any_eq_true, Finset.mem_toList]
            exact ⟨⟨p, Finset.mem_filter.mpr ⟨Finset.mem_univ p, hpl, hpA⟩, hzp⟩, hzl⟩

/- The star construction above follows L-meta-2874. The matching and cover
   construction below follows the Hall argument of R-meta-2685-41. -/

namespace PEqualNP.Outside.L_meta_18065.Census.Core

open PEqualNP.TopForm

open Ten.LeafCore3241 Ten.ForestBipartite3241 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm

def SmallCoreCovers {k : Nat} (G : SimpleGraph (Fin k)) : Prop :=
  ∀ H : SimpleGraph (Fin k), H ≤ G → Leafless H → ∃ T : Finset (Fin k),
    T.card ≤ 3 ∧ ∀ u v, H.Adj u v → u ∈ T ∨ v ∈ T

private theorem unmatched (n m : ℕ) (E M : Finset (Fin n × Fin m)) (G : SimpleGraph (Fin (n+m)))
    (adj : ∀ u v, G.Adj u v ↔ ∃ e ∈ E,
      (u = Fin.castAdd m e.1 ∧ v = Fin.natAdd n e.2) ∨
      (v = Fin.castAdd m e.1 ∧ u = Fin.natAdd n e.2))
    (cyc : ¬G.IsAcyclic)
    (ml : ∀ a ∈ M, ∀ b ∈ M, a.1 = b.1 → a = b)
    (mr : ∀ a ∈ M, ∀ b ∈ M, a.2 = b.2 → a = b) : ∃ e ∈ E, e ∉ M := by
  classical
  by_contra! allM
  have sep (a : Fin n) (b : Fin m) : Fin.castAdd m a ≠ Fin.natAdd n b := by
    intro eq
    have h := congrArg Fin.val eq
    change a.val = n + b.val at h
    omega
  have unique (v u w : Fin (n+m)) (hu : G.Adj v u) (hw : G.Adj v w) : u = w := by
    obtain ⟨e, he, ⟨ve,ue⟩ | ⟨ue,ve⟩⟩ := (adj _ _).mp hu <;>
      obtain ⟨f, hf, ⟨vf,wf⟩ | ⟨wf,vf⟩⟩ := (adj _ _).mp hw
    · have ef := ml e (allM e he) f (allM f hf) (Fin.castAdd_inj.mp (ve.symm.trans vf))
      simp [ue,wf,ef]
    · exact (sep _ _ (ve.symm.trans vf)).elim
    · exact (sep _ _ (vf.symm.trans ve)).elim
    · have eq := congrArg Fin.val (ve.symm.trans vf)
      have ef := mr e (allM e he) f (allM f hf) (by simpa [Fin.ext_iff] using eq)
      simp [ue,wf,ef]
  obtain ⟨v,w,hw⟩ := SimpleGraph.not_isAcyclic_iff_exists_isCycle.mp cyc
  have h3 := hw.three_le_length
  have eq := unique (w.getVert 1) (w.getVert 0) (w.getVert 2)
    (w.adj_getVert_succ (i:=0) (by omega)).symm (w.adj_getVert_succ (i:=1) (by omega))
  have bad := hw.getVert_injOn' (x₁:=0) (x₂:=2) (by change 0 ≤ w.length-1; omega)
    (by change 2 ≤ w.length-1; omega) eq
  contradiction


private theorem girth (n m : ℕ) (E : Finset (Fin n × Fin m)) (G : SimpleGraph (Fin (n+m)))
    (adj : ∀ u v, G.Adj u v ↔ ∃ e ∈ E,
      (u = Fin.castAdd m e.1 ∧ v = Fin.natAdd n e.2) ∨
      (v = Fin.castAdd m e.1 ∧ u = Fin.natAdd n e.2))
    (cyc : ¬G.IsAcyclic)
    (rect : ∀ a b i j, a ≠ b → i ≠ j → ¬ ((a,i) ∈ E ∧ (a,j) ∈ E ∧ (b,i) ∈ E ∧ (b,j) ∈ E)) :
    6 ≤ E.card := by
  classical
  have sep (a : Fin n) (b : Fin m) : Fin.castAdd m a ≠ Fin.natAdd n b := by
    intro eq
    have h := congrArg Fin.val eq
    change a.val = n + b.val at h
    omega
  have left (a b : Fin n) : ¬G.Adj (Fin.castAdd m a) (Fin.castAdd m b) := by
    rintro h
    obtain ⟨e, _, ⟨_, bad⟩ | ⟨_, bad⟩⟩ := (adj _ _).1 h <;> exact sep _ _ bad
  have right (a b : Fin m) : ¬G.Adj (Fin.natAdd n a) (Fin.natAdd n b) := by
    intro h
    obtain ⟨e, _, ⟨bad,_⟩ | ⟨bad,_⟩⟩ := (adj _ _).1 h <;> exact sep _ _ bad.symm
  have lr (a : Fin n) (b : Fin m) (h : G.Adj (Fin.castAdd m a) (Fin.natAdd n b)) : (a,b) ∈ E := by
    obtain ⟨⟨c,d⟩, he, ⟨ac,bd⟩ | ⟨bad,_⟩⟩ := (adj _ _).1 h
    · have : a = c := Fin.castAdd_inj.mp ac
      have : b = d := by simpa [Fin.ext_iff] using congrArg Fin.val bd
      subst c; subst d; exact he
    · exact (sep _ _ bad.symm).elim
  have square (v w x y : Fin (n+m)) (hv : v ≠ x) (hw : w ≠ y)
      (h1 : G.Adj v w) (h2 : G.Adj w x) (h3 : G.Adj x y) (h4 : G.Adj y v) : False := by
    cases v using Fin.addCases <;> cases w using Fin.addCases <;> cases x using Fin.addCases <;>
      cases y using Fin.addCases <;> first
      | exact (left _ _) h1 | exact (right _ _) h1 | exact (left _ _) h2 | exact (right _ _) h2
      | exact (left _ _) h3 | exact (right _ _) h3
      | exact rect _ _ _ _ (fun h => hv (congrArg _ h)) (fun h => hw (congrArg _ h))
          ⟨lr _ _ h1,lr _ _ h4.symm,lr _ _ h2.symm,lr _ _ h3⟩
      | exact rect _ _ _ _ (fun h => hw (congrArg _ h)) (fun h => hv (congrArg _ h))
          ⟨lr _ _ h1.symm,lr _ _ h2,lr _ _ h4,lr _ _ h3.symm⟩
  obtain ⟨v,w,hw⟩ := SimpleGraph.not_isAcyclic_iff_exists_isCycle.mp cyc
  let col : G.Coloring Bool := SimpleGraph.Coloring.mk (fun u => decide (u.val < n)) (by
    intro i j hij
    obtain ⟨⟨a,b⟩, _, ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩⟩ := (adj _ _).1 hij <;> simp)
  have ev := (col.even_length_iff_congr w).2 Iff.rfl
  have three := hw.three_le_length
  have six : 6 ≤ w.length := by
    by_contra! h
    obtain ⟨k,hk⟩ := ev
    have four : w.length = 4 := by omega
    have neq (a b : ℕ) (ha : a < 4) (hb : b < 4) (ne : a ≠ b) : w.getVert a ≠ w.getVert b :=
      fun eq => ne (hw.getVert_injOn' (by change a ≤ w.length-1; omega) (by change b ≤ w.length-1; omega) eq)
    apply square (w.getVert 0) (w.getVert 1) (w.getVert 2) (w.getVert 3)
      (neq _ _ (by decide) (by decide) (by decide)) (neq _ _ (by decide) (by decide) (by decide))
      (w.adj_getVert_succ (by omega)) (w.adj_getVert_succ (by omega)) (w.adj_getVert_succ (by omega))
    simpa [←four, SimpleGraph.Walk.getVert_length] using (w.adj_getVert_succ (i:=3) (by omega))
  let edge := fun e : Fin n × Fin m => s(Fin.castAdd m e.1, Fin.natAdd n e.2)
  have sub : G.edgeSet ⊆ ↑(E.image edge) := by
    intro z hz
    induction z using Sym2.inductionOn with
    | _ i j =>
      obtain ⟨e, he, ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩⟩ := (adj i j).1 hz
      · exact Finset.mem_image_of_mem edge he
      · rw [Sym2.eq_swap]; exact Finset.mem_image_of_mem edge he
  exact six.trans (hw.isTrail.length_le_ncard_edgeSet.trans
    ((Set.ncard_le_ncard sub).trans (by simpa only [Set.ncard_coe_finset] using Finset.card_image_le (s:=E) (f:=edge))))


theorem counts_irrel {k : Nat} {H : SimpleGraph (Fin k)}
    {I J : DecidableRel H.Adj} : @Counts k H I → @Counts k H J := by
  cases Subsingleton.elim I J
  exact id

theorem price_with_counts (n m : Nat) (E : Finset (Fin n × Fin m)) (C : Circuit)
    (counts : Counts (bip E)) (ao : IsAO2 (n+m) C)
    (h : ∀ x, circuitFun (n+m) C x =
      decide (∃ e ∈ E, x (Fin.castAdd m e.1) = true ∧ x (Fin.natAdd n e.2) = true)) :
    ∃ (P : Finset (Fin n)) (Q : Finset (Fin m)), (∀ e ∈ E, e.1 ∈ P ∨ e.2 ∈ Q) ∧
      E.card + P.card + Q.card ≤ C.size + 1 := by
  classical
  obtain ⟨S,cv,budget⟩ := bound_of_counts (bip E) counts C ao
    (funext (fun x => (h x).trans (formula E x).symm))
  let P := Finset.univ.filter fun i : Fin n => Fin.castAdd m i ∈ S
  let Q := Finset.univ.filter fun i : Fin m => Fin.natAdd n i ∈ S
  let L := P.image (Fin.castAdd m)
  let R := Q.image (Fin.natAdd n)
  have dis : Disjoint L R := by
    apply Finset.disjoint_left.mpr
    rintro i hl hr
    obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hl
    obtain ⟨b,_,eq⟩ := Finset.mem_image.mp hr
    exact sides a b eq.symm
  have inc : L ∪ R ⊆ S := by
    intro i hi
    rcases Finset.mem_union.mp hi with l | r
    · obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp l
      exact (Finset.mem_filter.mp ha).2
    · obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp r
      exact (Finset.mem_filter.mp hb).2
  have card := Finset.card_le_card inc
  rw [Finset.card_union_of_disjoint dis] at card
  change (P.image (Fin.castAdd m)).card + (Q.image (Fin.natAdd n)).card ≤ S.card at card
  rw [Finset.card_image_of_injective _ (Fin.castAdd_injective n m),
    Finset.card_image_of_injective _ (Fin.natAdd_injective m n)] at card
  rw [bip_edges] at budget
  refine ⟨P,Q,?_,by omega⟩
  intro e he
  exact (cv (bip_adjacency he)).imp (fun l => Finset.mem_filter.mpr ⟨Finset.mem_univ _,l⟩)
    (fun r => Finset.mem_filter.mpr ⟨Finset.mem_univ _,r⟩)

end PEqualNP.Outside.L_meta_18065.Census.Core

namespace PEqualNP.Outside.L_meta_18065.Census.Core.Pairs

private theorem side_bound {A B : Type*} [DecidableEq A] [DecidableEq B]
    (F : Finset (A × B)) (P : Finset A) (Q : Finset B)
    (cv : ∀ p ∈ F, p.1 ∈ P ∨ p.2 ∈ Q)
    (partner : ∀ i j, (i,j) ∈ F → ∃ i', i' ≠ i ∧ (i',j) ∈ F)
    (free : ∀ i k j l, i ≠ k → j ≠ l → ¬ ((i,j) ∈ F ∧ (i,l) ∈ F ∧ (k,j) ∈ F ∧ (k,l) ∈ F)) :
    (F.filter (fun e => e.2 ∉ Q)).card ≤ P.card*(P.card-1) := by
  classical
  let alt (e : A × B) := if h : e ∈ F then (partner _ _ h).choose else e.1
  have legal (e : A × B) (h : e ∈ F) : alt e ≠ e.1 ∧ (alt e,e.2) ∈ F := by
    simpa only [alt,dif_pos h] using (partner e.1 e.2 h).choose_spec
  have bound : (F.filter (fun e => e.2 ∉ Q)).card ≤ P.offDiag.card := by
    apply Finset.card_le_card_of_injOn (fun e => (e.1,alt e))
    · intro e he
      obtain ⟨h,nq⟩ := Finset.mem_filter.mp he
      obtain ⟨nd,ok⟩ := legal e h
      exact Finset.mem_offDiag.mpr ⟨(cv e h).resolve_right nq,(cv _ ok).resolve_right nq,nd.symm⟩
    · intro e he f hf h
      have er := Finset.mem_filter.mp he
      have fr := Finset.mem_filter.mp hf
      obtain ⟨nd,ok⟩ := legal e er.1
      have fok := (legal f fr.1).2
      have fst : e.1 = f.1 := congrArg (Prod.fst : A × A → A) h
      have snd : alt e = alt f := congrArg (Prod.snd : A × A → A) h
      apply Prod.ext fst
      by_contra no
      apply free e.1 (alt e) e.2 f.2 nd.symm no
      exact ⟨er.1,by rw [fst]; exact fr.1,ok,by rw [snd]; exact fok⟩
  calc _ ≤ P.offDiag.card := bound
       _ = _ := by rw [Finset.offDiag_card,Nat.mul_sub, Nat.mul_one]

theorem mixed_cover_bound {A B : Type*} [DecidableEq A] [DecidableEq B]
    (E : Finset (A × B)) (P : Finset A) (Q : Finset B)
    (cv : ∀ e ∈ E, e.1 ∈ P ∨ e.2 ∈ Q)
    (partners : ∀ i j, (i,j) ∈ E →
      (∃ l, l ≠ j ∧ (i,l) ∈ E) ∧ (∃ k, k ≠ i ∧ (k,j) ∈ E))
    (free : ∀ i k j l, i ≠ k → j ≠ l → ¬ ((i,j) ∈ E ∧ (i,l) ∈ E ∧ (k,j) ∈ E ∧ (k,l) ∈ E)) :
    E.card ≤ P.card * (P.card - 1) + Q.card * (Q.card - 1) + P.card * Q.card := by
  classical
  let X := E.filter fun e => e.2 ∉ Q
  let Y := E.filter fun e => e.1 ∉ P
  let Z := E.image Prod.swap
  have zm (i : B) (j : A) : (i,j) ∈ Z ↔ (j,i) ∈ E := by
    constructor
    · rintro h
      obtain ⟨⟨a,b⟩,he,eq⟩ := Finset.mem_image.mp h
      cases eq
      exact he
    · intro h
      exact Finset.mem_image.mpr ⟨(j,i),h,rfl⟩
  have top : X.card ≤ P.card*(P.card-1) := side_bound E P Q cv (fun i j h => (partners i j h).2) free
  have back := side_bound Z Q P (by
    rintro ⟨i,j⟩ h
    exact (cv (j,i) ((zm i j).mp h)).symm)
    (by
      intro i j h
      obtain ⟨l,ne,m⟩ := (partners j i ((zm i j).mp h)).1
      exact ⟨l,ne,(zm l j).mpr m⟩)
    (by
      rintro i k j l ik jl ⟨h1,h2,h3,h4⟩
      exact free j l i k jl ik ⟨(zm _ _).mp h1,(zm _ _).mp h3,(zm _ _).mp h2,(zm _ _).mp h4⟩)
  have symmCard : Y.card ≤ (Z.filter (fun e => e.2 ∉ P)).card := by
    apply Finset.card_le_card_of_injOn Prod.swap
    · rintro ⟨i,j⟩ he
      obtain ⟨h,p⟩ := Finset.mem_filter.mp he
      exact Finset.mem_filter.mpr ⟨(zm _ _).mpr h,p⟩
    · intro a _ b _ eq
      simpa only [Prod.swap_swap] using congrArg Prod.swap eq
  have incl : E ⊆ (X ∪ Y) ∪ (P ×ˢ Q) := by
    intro e he
    by_cases h : e.1 ∈ P
    · by_cases k : e.2 ∈ Q
      · exact Finset.mem_union_right _ (Finset.mem_product.mpr ⟨h,k⟩)
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨he,k⟩))
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨he,h⟩))
  have t := Finset.card_le_card incl
  have u := Finset.card_union_le (X ∪ Y) (P ×ˢ Q)
  have v := Finset.card_union_le X Y
  rw [Finset.card_product] at u
  omega

theorem mixed_four {p q e : Nat} (hp : 0 < p) (hq : 0 < q) (h : p + q ≤ 4)
    (cost : e ≤ p * (p-1) + q * (q-1) + p*q) : e ≤ 9 := by
  have h1 : p ≤ 3 := by omega
  have h2 : q ≤ 3 := by omega
  interval_cases p <;> interval_cases q <;> omega

end PEqualNP.Outside.L_meta_18065.Census.Core.Pairs

namespace PEqualNP.Outside.L_meta_18065.Census.Core.Closure
open Finset
variable {P L : Type*} [DecidableEq P] [DecidableEq L]
def Linear (A : L → Finset P) := ∀ ⦃l k⦄, l ≠ k → ∀ ⦃p q⦄, p ≠ q →
  p ∈ A l → q ∈ A l → p ∈ A k → q ∈ A k → False

theorem pair_budget (A : L → Finset P) (lin : Linear A) (S : Finset L) :
    (∑ l ∈ S, (A l).card.choose 2) ≤ (S.biUnion A).card.choose 2 := by
  classical
  let B := fun l => (A l).powersetCard 2
  have dis : (S : Set L).PairwiseDisjoint B := by
    intro l hl k hk diff
    apply Finset.disjoint_left.mpr
    intro K hK hK'
    obtain ⟨h₁,hc⟩ := Finset.mem_powersetCard.mp hK
    obtain ⟨h₂,_⟩ := Finset.mem_powersetCard.mp hK'
    obtain ⟨p,q,pq,rfl⟩ := Finset.card_eq_two.mp hc
    exact lin diff pq (h₁ (by simp)) (h₁ (by simp)) (h₂ (by simp)) (h₂ (by simp))
  have sub : S.biUnion B ⊆ (S.biUnion A).powersetCard 2 := by
    intro K hK
    obtain ⟨l,hl,h⟩ := Finset.mem_biUnion.mp hK
    obtain ⟨h₁,h₂⟩ := Finset.mem_powersetCard.mp h
    exact Finset.mem_powersetCard.mpr ⟨fun p hp => Finset.mem_biUnion.mpr ⟨l,hl,h₁ hp⟩,h₂⟩
  have h := Finset.card_le_card sub
  rw [Finset.card_biUnion dis,Finset.card_powersetCard] at h
  simpa only [B,Finset.card_powersetCard] using h

open Finset

theorem five_columns {n m : Nat} (E : Finset (Fin n × Fin m))
    (free : ∀ i k j l, i ≠ k → j ≠ l → ¬((i,j)∈E ∧ (i,l)∈E ∧ (k,j)∈E ∧ (k,l)∈E))
    (rows : (E.image Prod.fst).card ≤ 4) (cols : (E.image Prod.snd).card ≤ 5)
    (noLeaf : ∀ i j, (i,j) ∈ E → ∃ k, k ≠ i ∧ (k,j) ∈ E) : E.card ≤ 10 := by
  classical
  let S := E.image Prod.snd
  let N (l : Fin m) := Finset.univ.filter fun p => (p,l) ∈ E
  have nm (p : Fin n) (l : Fin m) : p ∈ N l ↔ (p,l) ∈ E := by simp [N]
  have lin : Linear N := by
    rintro j l jl i k ik a b c d
    exact free i k j l ik jl ⟨(nm i j).mp a,(nm i l).mp c,(nm k j).mp b,(nm k l).mp d⟩
  have sub : S.biUnion N ⊆ E.image Prod.fst := by
    intro u hu
    obtain ⟨l,_,h⟩ := Finset.mem_biUnion.mp hu
    exact Finset.mem_image.mpr ⟨(u,l),(nm u l).mp h,rfl⟩
  have four := (card_le_card sub).trans rows
  have pair := (pair_budget N lin S).trans (Nat.choose_le_choose 2 four)
  change ∑ l ∈ S, (N l).card.choose 2 ≤ 6 at pair
  have sz (l : Fin m) (hl : l ∈ S) : 2 ≤ (N l).card ∧ (N l).card ≤ 4 := by
    obtain ⟨⟨i,j⟩,h,rfl⟩ := Finset.mem_image.mp hl
    obtain ⟨k,ne,hk⟩ := noLeaf i j h
    constructor
    · by_contra! small
      change (N j).card < 2 at small
      exact ne (Finset.card_le_one.mp (show (N j).card ≤ 1 by omega) k ((nm _ _).mpr hk) i ((nm _ _).mpr h))
    · exact (Finset.card_le_card (show N j ⊆ S.biUnion N from fun x hx => Finset.mem_biUnion.mpr ⟨j,Finset.mem_image.mpr ⟨(i,j),h,rfl⟩,hx⟩)).trans four
  have inc : E.card ≤ (S.sigma N).card := by
    apply Finset.card_le_card_of_injOn (fun e => Sigma.mk e.2 e.1)
    · intro e he
      exact Finset.mem_sigma.mpr ⟨Finset.mem_image_of_mem _ he,(nm _ _).mpr he⟩
    · intro a _ b _ eq
      exact Prod.ext (congrArg (fun j : Σ _ : Fin m, Fin n => j.2) eq) (congrArg Sigma.fst eq)
  rw [Finset.card_sigma] at inc
  have cmp (l : Fin m) (hl : l ∈ S) : 2*(N l).card ≤ 3+(N l).card.choose 2 := by
    obtain ⟨lo,hi⟩ := sz l hl
    generalize (N l).card = t at lo hi ⊢
    interval_cases t <;> decide
  have twice : 2*∑ l ∈ S, (N l).card ≤ 3*S.card+∑ l ∈ S,(N l).card.choose 2 := by
    calc
      _ = ∑ l ∈ S, 2*(N l).card := Finset.mul_sum ..
      _ ≤ ∑ l ∈ S, (3+(N l).card.choose 2) := Finset.sum_le_sum cmp
      _ = _ := by rw [Finset.sum_add_distrib]; simp [Nat.mul_comm]
  change S.card ≤ 5 at cols
  omega

end PEqualNP.Outside.L_meta_18065.Census.Core.Closure

namespace PEqualNP.Outside.L_meta_18065.Census.Core
open Ten Ten.LeafCore3241 Ten.ForestBipartite3241 Ten.GraphPacking3241 Ten.MatrixPacking3241
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm

def SmallMatrix {n m : Nat} (E : Finset (Fin n × Fin m)) : Prop :=
   ∀ F ⊆ E, HasPartners F → F.card ≤ 10

def HasMixedCover {n m : Nat} (E : Finset (Fin n × Fin m)) : Prop :=
  ∃ (P : Finset (Fin n)) (Q : Finset (Fin m)), 0 < P.card ∧ 0 < Q.card ∧
    P.card+Q.card ≤ 4 ∧ ∀ e ∈ E, e.1 ∈ P ∨ e.2 ∈ Q

theorem from_mixed {n m : Nat} (E : Finset (Fin n × Fin m)) (free : FourFree E)
    (mixed : HasMixedCover E) : SmallMatrix E := by
  obtain ⟨P,Q,hp,hq,size,cov⟩ := mixed
  intro F sub both
  have ff : FourFree F := fun i k j l ik jl ⟨a,b,c,d⟩ => free i k j l ik jl ⟨sub a,sub b,sub c,sub d⟩
  have cost := Pairs.mixed_cover_bound F P Q (fun e he => cov e (sub he)) both ff
  exact (Pairs.mixed_four hp hq size cost).trans (by decide)

def thickCols {n m : Nat} (E : Finset (Fin n × Fin m)) : Finset (Fin m) :=
  Finset.univ.filter fun l => ∃ p q : Fin n, p ≠ q ∧ (p,l) ∈ E ∧ (q,l) ∈ E

theorem from_four_five {n m : Nat} (E : Finset (Fin n × Fin m)) (free : FourFree E)
    (rows : (E.image Prod.fst).card ≤ 4) (heavy : (thickCols E).card ≤ 5) : SmallMatrix E := by
  intro F sub both
  have ff : FourFree F := fun i k j l ik jl ⟨a,b,c,d⟩ => free i k j l ik jl ⟨sub a,sub b,sub c,sub d⟩
  have sc : F.image Prod.snd ⊆ thickCols E := by
    rintro l h
    obtain ⟨⟨p,j⟩,he,rfl⟩ := Finset.mem_image.mp h
    obtain ⟨k,ne,hk⟩ := (both p j he).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,k,p,ne,sub hk,sub he⟩
  apply Closure.five_columns F ff ((Finset.card_le_card (Finset.image_subset_image sub)).trans rows)
    ((Finset.card_le_card sc).trans heavy)
  exact fun i j h => (both i j h).2

theorem from_core_census {n m} (E : Finset (Fin n × Fin m)) (free : FourFree E) (small : SmallMatrix E)
    (census : Census) : Counts (bip E) := by
  classical
  apply peel_to_core (bip E)
  intro H _ sub last
  let F := E.filter (fun p => H.Adj (Left p.1) (Right p.2))
  have eq : H = bip F := by
    ext i j
    constructor
    · intro ij
      rcases sub ij with ⟨ne,⟨e,he,rfl,rfl⟩ | ⟨e,he,rfl,rfl⟩⟩
      · exact bip_adjacency (Finset.mem_filter.mpr ⟨he,ij⟩ : e ∈ F)
      · exact (bip_adjacency (Finset.mem_filter.mpr ⟨he,ij.symm⟩ : e ∈ F)).symm
    · rintro ⟨_,⟨e,he,rfl,rfl⟩ | ⟨e,he,rfl,rfl⟩⟩
      · exact (Finset.mem_filter.mp he).2
      · exact ((Finset.mem_filter.mp he).2).symm
  have subset : F ⊆ E := Finset.filter_subset _ _
  have freeF : FourFree F := fun p q l s pq ls ⟨a,b,c,d⟩ =>
    free p q l s pq ls ⟨subset a,subset b,subset c,subset d⟩
  have carry {K L : SimpleGraph (Fin (n+m))} [d : DecidableRel K.Adj] [e : DecidableRel L.Adj]
      (same : K = L) (ok : Counts L) : Counts K := by
    subst L
    have sameInst : d = e := Subsingleton.elim _ _
    cases sameInst
    exact ok
  exact carry eq (compressed F freeF (small F subset ((leafless_iff F).mp (eq ▸ last))) (eq ▸ last) census)

end PEqualNP.Outside.L_meta_18065.Census.Core

namespace PEqualNP.Outside.L_meta_18065.Stars

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm

-- The star circuit of a vertex cover of a bipartite edge set: every cover vertex with at
-- least one assigned edge gets an OR chain of its assigned neighbours ANDed with the vertex,
-- and the stars are ORed together. All gates have exactly two operands.

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

lemma wf_length (gs : List Gate) (w : List Bool) : (wf gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [wf]
  | cons g gs ih =>
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]
    simp
    omega

lemma wf_append (gs hs : List Gate) (w : List Bool) : wf (gs ++ hs) w = wf hs (wf gs w) := by
  simp [wf, List.foldl_append]

lemma wf_getD_lt (hs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (wf hs w).getD i false = w.getD i false := by
  induction hs generalizing w with
  | nil => rfl
  | cons g hs ih =>
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (by simp; omega)
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this, List.getD_append _ _ _ _ hi]

def val (n : ℕ) (gs : List Gate) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (wf gs (List.ofFn x)).getD w false

def inp {n : ℕ} (x : Fin n → Bool) (i : ℕ) : Bool := (List.ofFn x).getD i false

lemma val_old (n : ℕ) (gs hs : List Gate) (x : Fin n → Bool) (w : ℕ) (hw : w < n + gs.length) :
    val n (gs ++ hs) x w = val n gs x w := by
  unfold val
  rw [wf_append]
  exact wf_getD_lt _ _ _ (by rw [wf_length]; simpa using hw)

lemma val_new (n : ℕ) (gs : List Gate) (op : GateOp) (a b : ℕ) (x : Fin n → Bool) :
    val n (gs ++ [⟨op, [a, b]⟩]) x (n + gs.length) = op.eval [val n gs x a, val n gs x b] := by
  unfold val
  rw [wf_append]
  have hl : (wf gs (List.ofFn x)).length = n + gs.length := by rw [wf_length]; simp
  have e : wf [⟨op, [a, b]⟩] (wf gs (List.ofFn x)) = wf gs (List.ofFn x) ++
      [op.eval [(wf gs (List.ofFn x)).getD a false, (wf gs (List.ofFn x)).getD b false]] := rfl
  rw [e, ← hl, List.getD_append_right _ _ _ _ le_rfl]
  simp

lemma val_lt (n : ℕ) (gs : List Gate) (x : Fin n → Bool) (i : ℕ) (hi : i < n) :
    val n gs x i = inp x i := by
  unfold val inp
  exact wf_getD_lt _ _ _ (by simpa using hi)

lemma inp_of_lt {n : ℕ} (x : Fin n → Bool) (i : ℕ) (hi : i < n) : inp x i = x ⟨i, hi⟩ := by
  unfold inp
  simp [List.getD_eq_getElem?_getD, hi]

def OK (n : ℕ) (gs : List Gate) : Prop :=
  (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∧
  ∀ j < gs.length, ∀ i ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, i < n + j

lemma ok_snoc {n : ℕ} {gs : List Gate} (h : OK n gs) (op : GateOp)
    (hop : op = GateOp.and ∨ op = GateOp.or) (a b : ℕ) (ha : a < n + gs.length)
    (hb : b < n + gs.length) : OK n (gs ++ [⟨op, [a, b]⟩]) := by
  refine ⟨?_, ?_⟩
  · intro g hg
    rcases List.mem_append.1 hg with hg | hg
    · exact h.1 g hg
    · simp only [List.mem_singleton] at hg
      subst hg
      exact ⟨hop, rfl⟩
  · intro j hj i hi
    rw [List.length_append, List.length_singleton] at hj
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | hj
    · rw [List.getD_append _ _ _ _ hj] at hi
      exact h.2 j hj i hi
    · subst hj
      rw [List.getD_append_right _ _ _ _ le_rfl] at hi
      simp only [Nat.sub_self, List.getD_cons_zero, List.mem_cons, List.not_mem_nil,
        or_false] at hi
      rcases hi with rfl | rfl <;> assumption

lemma any_congr' {f g : ℕ → Bool} (ws : List ℕ) (h : ∀ w ∈ ws, f w = g w) :
    ws.any f = ws.any g := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    simp only [List.any_cons]
    rw [h w List.mem_cons_self, ih (fun w' hw' => h w' (List.mem_cons_of_mem _ hw'))]


def Safe (n : ℕ) (P : (Fin n → Bool) → Prop) (gs : List Gate) : Prop :=
  ∀ j < gs.length, (gs.getD j ⟨GateOp.or, []⟩).op = GateOp.and →
    ∀ x, val n gs x (n+j) = true → P x

def Aug (n : ℕ) (P : (Fin n → Bool) → Prop) (gs : List Gate) := OK n gs ∧ Safe n P gs

lemma augSnoc {n : ℕ} {P : (Fin n → Bool) → Prop} {gs : List Gate} (h : Aug n P gs)
    (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (a b : ℕ)
    (ha : a < n + gs.length) (hb : b < n + gs.length)
    (guard : op = GateOp.and → ∀ x, op.eval [val n gs x a, val n gs x b] = true → P x) :
    Aug n P (gs ++ [⟨op, [a,b]⟩]) := by
  refine ⟨ok_snoc h.1 op hop a b ha hb, ?_⟩
  intro j hj hand x hx
  simp only [List.length_append, List.length_singleton] at hj
  by_cases old : j < gs.length
  · rw [List.getD_append _ _ _ _ old] at hand
    rw [val_old n gs _ x (n+j) (by omega)] at hx
    exact h.2 j old hand x hx
  · have eq : j = gs.length := by omega
    subst j
    rw [List.getD_append_right _ _ _ _ le_rfl] at hand
    simp only [Nat.sub_self, List.getD_cons_zero] at hand
    rw [val_new] at hx
    exact guard hand x hx

lemma orAcc (n : ℕ) (P : (Fin n → Bool) → Prop) : ∀ (ws : List ℕ) (gs : List Gate) (o : ℕ), Aug n P gs → o < n + gs.length →
    (∀ w ∈ ws, w < n + gs.length) →
    ∃ (ext : List Gate) (o' : ℕ), Aug n P (gs ++ ext) ∧ ext.length = ws.length ∧
      o' < n + (gs ++ ext).length ∧
      ∀ x, val n (gs ++ ext) x o' = (val n gs x o || ws.any (fun w => val n gs x w)) := by
  intro ws
  induction ws with
  | nil =>
    intro gs o h ho _
    exact ⟨[], o, by simpa using h, rfl, by simpa using ho, fun x => by simp⟩
  | cons w ws ih =>
    intro gs o h ho hws
    have hw := hws w List.mem_cons_self
    have h1 := augSnoc h GateOp.or (Or.inr rfl) o w ho hw (by intro hk; cases hk)
    obtain ⟨ext, o', hok, hlen, ho', hv⟩ := ih (gs ++ [⟨GateOp.or, [o, w]⟩]) (n + gs.length) h1
      (by simp) (fun w' hw' => by
        have := hws w' (List.mem_cons_of_mem _ hw')
        simp only [List.length_append, List.length_singleton]
        omega)
    have e : gs ++ (⟨GateOp.or, [o, w]⟩ : Gate) :: ext = (gs ++ [⟨GateOp.or, [o, w]⟩]) ++ ext := by
      simp
    refine ⟨⟨GateOp.or, [o, w]⟩ :: ext, o', by rw [e]; exact hok, by simp [hlen],
      by rw [e]; exact ho', fun x => ?_⟩
    rw [e, hv x, val_new]
    rw [any_congr' ws (fun w' hw' => val_old n gs _ x w' (hws w' (List.mem_cons_of_mem _ hw')))]
    simp [GateOp.eval, Bool.or_assoc]

lemma star (n : ℕ) (P : (Fin n → Bool) → Prop) (gs : List Gate) (c w0 : ℕ) (ws : List ℕ) (h : Aug n P gs)
    (hc : c < n + gs.length) (hw0 : w0 < n + gs.length) (hws : ∀ w ∈ ws, w < n + gs.length) (paid : ∀ x, (val n gs x c && (val n gs x w0 || ws.any (fun w => val n gs x w))) = true → P x) :
    ∃ (ext : List Gate) (o' : ℕ), Aug n P (gs ++ ext) ∧ ext.length = ws.length + 1 ∧
      o' < n + (gs ++ ext).length ∧
      ∀ x, val n (gs ++ ext) x o' =
        (val n gs x c && (val n gs x w0 || ws.any (fun w => val n gs x w))) := by
  obtain ⟨ext, o1, hok, hlen, ho1, hv⟩ := orAcc n P ws gs w0 h hw0 hws
  have hc' : c < n + (gs ++ ext).length := by
    simp only [List.length_append]
    omega
  refine ⟨ext ++ [⟨GateOp.and, [c, o1]⟩], n + (gs ++ ext).length, ?_, by simp [hlen], ?_,
    fun x => ?_⟩
  · rw [← List.append_assoc]
    apply augSnoc hok GateOp.and (Or.inl rfl) c o1 hc' ho1
    intro _ x hit
    apply paid x
    simpa [GateOp.eval, val_old n gs ext x c hc, hv x] using hit
  · simp only [List.length_append, List.length_singleton]
    omega
  · rw [← List.append_assoc, val_new, hv x, val_old n gs ext x c hc]
    simp [GateOp.eval]

def starVal {n : ℕ} (x : Fin n → Bool) (s : ℕ × List ℕ) : Bool :=
  inp x s.1 && s.2.any (inp x)

lemma star_val (n : ℕ) (gs : List Gate) (x : Fin n → Bool) (s : ℕ × List ℕ) (w0 : ℕ)
    (ws : List ℕ) (hsw : s.2 = w0 :: ws) (h1 : s.1 < n) (h3 : ∀ w ∈ s.2, w < n) :
    (val n gs x s.1 && (val n gs x w0 || ws.any (fun w => val n gs x w))) = starVal x s := by
  unfold starVal
  rw [hsw] at h3 ⊢
  rw [val_lt n gs x s.1 h1, val_lt n gs x w0 (h3 w0 List.mem_cons_self),
    any_congr' ws (fun w hw => val_lt n gs x w (h3 w (List.mem_cons_of_mem _ hw)))]
  simp

lemma starsAcc (n : ℕ) (P : (Fin n → Bool) → Prop) : ∀ (sts : List (ℕ × List ℕ)) (gs : List Gate) (o : ℕ), Aug n P gs →
    o < n + gs.length → (∀ s ∈ sts, s.1 < n ∧ s.2 ≠ [] ∧ ∀ w ∈ s.2, w < n) →
    (∀ s ∈ sts, ∀ x, starVal x s = true → P x) →
    ∃ (ext : List Gate) (o' : ℕ), Aug n P (gs ++ ext) ∧
      ext.length = (sts.map (fun s => s.2.length)).sum + sts.length ∧
      o' < n + (gs ++ ext).length ∧
      ∀ x, val n (gs ++ ext) x o' = (val n gs x o || sts.any (starVal x)) := by
  intro sts
  induction sts with
  | nil =>
    intro gs o h ho _ _
    exact ⟨[], o, by simpa using h, rfl, by simpa using ho, fun x => by simp⟩
  | cons s sts ih =>
    intro gs o h ho hs paid
    obtain ⟨hs1, hs2, hs3⟩ := hs s List.mem_cons_self
    obtain ⟨w0, ws, hsw⟩ := List.exists_cons_of_ne_nil hs2
    have hw0 : w0 < n := hs3 w0 (by rw [hsw]; exact List.mem_cons_self)
    have hws : ∀ w ∈ ws, w < n := fun w hw => hs3 w (by rw [hsw]; exact List.mem_cons_of_mem _ hw)
    obtain ⟨e1, o1, hok1, hl1, ho1, hv1⟩ := star n P gs s.1 w0 ws h (by omega) (by omega)
      (fun w hw => by have := hws w hw; omega)
      (fun x hx => paid s List.mem_cons_self x (by rwa [← star_val n gs x s w0 ws hsw hs1 hs3]))
    have ho' : o < n + (gs ++ e1).length := by
      simp only [List.length_append]
      omega
    have h2 := augSnoc hok1 GateOp.or (Or.inr rfl) o o1 ho' ho1 (by intro hk; cases hk)
    obtain ⟨e2, o2, hok2, hl2, ho2, hv2⟩ := ih (gs ++ e1 ++ [⟨GateOp.or, [o, o1]⟩])
      (n + (gs ++ e1).length) h2 (by simp) (fun s' hs' => hs s' (List.mem_cons_of_mem _ hs'))
      (fun s' hs' => paid s' (List.mem_cons_of_mem _ hs'))
    have e : gs ++ (e1 ++ [(⟨GateOp.or, [o, o1]⟩ : Gate)] ++ e2) =
        (gs ++ e1 ++ [⟨GateOp.or, [o, o1]⟩]) ++ e2 := by simp
    refine ⟨e1 ++ [⟨GateOp.or, [o, o1]⟩] ++ e2, o2, by rw [e]; exact hok2, ?_,
      by rw [e]; exact ho2, fun x => ?_⟩
    · simp only [List.length_append, List.length_singleton, hl1, hl2, List.map_cons,
        List.sum_cons, List.length_cons, List.length_nil, hsw]
      omega
    · rw [e, hv2 x, val_new, hv1 x, val_old n gs e1 x o ho,
        star_val n gs x s w0 ws hsw hs1 hs3]
      simp [GateOp.eval, Bool.or_assoc]

lemma build (n : ℕ) (P : (Fin n → Bool) → Prop) (sts : List (ℕ × List ℕ)) (hne : sts ≠ [])
    (hs : ∀ s ∈ sts, s.1 < n ∧ s.2 ≠ [] ∧ ∀ w ∈ s.2, w < n)
    (paid : ∀ s ∈ sts, ∀ x, starVal x s = true → P x) :
    ∃ (gs : List Gate) (o : ℕ), Aug n P gs ∧
      gs.length + 1 = (sts.map (fun s => s.2.length)).sum + sts.length ∧
      ∀ x, val n gs x o = sts.any (starVal x) := by
  obtain ⟨s, rest, rfl⟩ := List.exists_cons_of_ne_nil hne
  obtain ⟨hs1, hs2, hs3⟩ := hs s List.mem_cons_self
  obtain ⟨w0, ws, hsw⟩ := List.exists_cons_of_ne_nil hs2
  have hw0 : w0 < n := hs3 w0 (by rw [hsw]; exact List.mem_cons_self)
  have hws : ∀ w ∈ ws, w < n := fun w hw => hs3 w (by rw [hsw]; exact List.mem_cons_of_mem _ hw)
  have h0 : Aug n P [] := ⟨⟨by simp, by simp⟩, by intro j hj; simp at hj⟩
  obtain ⟨e1, o1, hok1, hl1, ho1, hv1⟩ := star n P [] s.1 w0 ws h0 (by simpa using hs1)
    (by simpa using hw0) (fun w hw => by simpa using hws w hw)
    (fun x hx => paid s List.mem_cons_self x (by rwa [← star_val n [] x s w0 ws hsw hs1 hs3]))
  obtain ⟨e2, o2, hok2, hl2, ho2, hv2⟩ := starsAcc n P rest ([] ++ e1) o1 hok1 ho1
    (fun s' hs' => hs s' (List.mem_cons_of_mem _ hs'))
    (fun s' hs' => paid s' (List.mem_cons_of_mem _ hs'))
  refine ⟨[] ++ e1 ++ e2, o2, hok2, ?_, fun x => ?_⟩
  · simp only [List.length_append, List.length_nil, hl1, hl2, List.map_cons, List.sum_cons,
      List.length_cons, hsw]
    omega
  · rw [hv2 x, hv1 x, star_val n [] x s w0 ws hsw hs1 hs3]
    simp

noncomputable def stP (p l : ℕ) (F : Finset (Fin p × Fin l)) (P : Finset (Fin p)) : List (ℕ × List ℕ) :=
  P.toList.map (fun a => (a.val,
    (((F.filter (fun e => e.1 ∈ P)).filter (fun e => e.1 = a)).toList.map
      (fun e => p + e.2.val))))

noncomputable def stL (p l : ℕ) (F : Finset (Fin p × Fin l)) (P : Finset (Fin p)) (L : Finset (Fin l)) :
    List (ℕ × List ℕ) :=
  L.toList.map (fun b => (p + b.val,
    (((F.filter (fun e => e.1 ∉ P)).filter (fun e => e.2 = b)).toList.map
      (fun e => e.1.val))))

noncomputable def sts (p l : ℕ) (F : Finset (Fin p × Fin l)) (P : Finset (Fin p)) (L : Finset (Fin l)) :
    List (ℕ × List ℕ) :=
  (stP p l F P ++ stL p l F P L).filter (fun s => !s.2.isEmpty)

lemma not_isEmpty_of_mem {ws : List ℕ} {w : ℕ} (h : w ∈ ws) : (!ws.isEmpty) = true := by
  cases ws with
  | nil => simp at h
  | cons a t => rfl

lemma sts_wires (p l : ℕ) (F : Finset (Fin p × Fin l)) (P : Finset (Fin p))
    (L : Finset (Fin l)) :
    ∀ s ∈ sts p l F P L, s.1 < p + l ∧ s.2 ≠ [] ∧ ∀ w ∈ s.2, w < p + l := by
  intro s hs
  simp only [sts, List.mem_filter, List.mem_append, stP, stL, List.mem_map,
    Finset.mem_toList] at hs
  obtain ⟨hmem, hne⟩ := hs
  have hne' : s.2 ≠ [] := by
    intro h
    simp [h] at hne
  rcases hmem with ⟨a, _, rfl⟩ | ⟨b, _, rfl⟩
  · refine ⟨?_, hne', ?_⟩
    · show a.val < p + l
      have := a.isLt
      omega
    · intro w hw
      simp only [List.mem_map] at hw
      obtain ⟨e, _, rfl⟩ := hw
      have := e.2.isLt
      omega
  · refine ⟨?_, hne', ?_⟩
    · show p + b.val < p + l
      have := b.isLt
      omega
    · intro w hw
      simp only [List.mem_map] at hw
      obtain ⟨e, _, rfl⟩ := hw
      have := e.1.isLt
      omega

lemma sts_len (p l : ℕ) (F : Finset (Fin p × Fin l)) (P : Finset (Fin p))
    (L : Finset (Fin l)) : (sts p l F P L).length ≤ P.card + L.card := by
  calc (sts p l F P L).length ≤ (stP p l F P ++ stL p l F P L).length :=
        List.length_filter_le _ _
    _ = P.card + L.card := by simp [stP, stL]

lemma filter_sum (ss : List (ℕ × List ℕ)) :
    ((ss.filter (fun s => !s.2.isEmpty)).map (fun s => s.2.length)).sum =
      (ss.map (fun s => s.2.length)).sum := by
  induction ss with
  | nil => rfl
  | cons s ss ih =>
    cases hs : s.2 with
    | nil => simp [hs, ih]
    | cons a t => simp [hs, ih]

lemma sts_sum (p l : ℕ) (F : Finset (Fin p × Fin l)) (P : Finset (Fin p))
    (L : Finset (Fin l)) (hcov : ∀ e ∈ F, e.1 ∈ P ∨ e.2 ∈ L) :
    ((sts p l F P L).map (fun s => s.2.length)).sum = F.card := by
  unfold sts
  rw [filter_sum]
  have h1 := Finset.card_eq_sum_card_fiberwise (f := Prod.fst)
    (s := F.filter (fun e => e.1 ∈ P)) (t := P) (fun e he => (Finset.mem_filter.mp he).2)
  have h2 := Finset.card_eq_sum_card_fiberwise (f := Prod.snd)
    (s := F.filter (fun e => e.1 ∉ P)) (t := L) (fun e he => by
      have he' := Finset.mem_filter.mp he
      exact (hcov e he'.1).resolve_left he'.2)
  have h3 := Finset.card_filter_add_card_filter_not (s := F) (fun e => e.1 ∈ P)
  simp only [List.map_append, List.sum_append, stP, stL, List.map_map, Function.comp_def,
    List.length_map, Finset.length_toList, Finset.sum_map_toList]
  omega

lemma sts_mem (p l : ℕ) (F : Finset (Fin p × Fin l)) (P : Finset (Fin p))
    (L : Finset (Fin l)) (hcov : ∀ e ∈ F, e.1 ∈ P ∨ e.2 ∈ L) (a : Fin p) (b : Fin l)
    (hab : (a, b) ∈ F) :
    ∃ s ∈ sts p l F P L, (s.1 = a.val ∧ p + b.val ∈ s.2) ∨ (s.1 = p + b.val ∧ a.val ∈ s.2) := by
  by_cases ha : a ∈ P
  · have hm : p + b.val ∈ (((F.filter (fun e => e.1 ∈ P)).filter (fun e => e.1 = a)).toList.map
        (fun e => p + e.2.val)) :=
      List.mem_map.2 ⟨(a, b), Finset.mem_toList.2 (Finset.mem_filter.2
        ⟨Finset.mem_filter.2 ⟨hab, ha⟩, rfl⟩), rfl⟩
    refine ⟨(a.val, _), ?_, Or.inl ⟨rfl, hm⟩⟩
    refine List.mem_filter.2 ⟨List.mem_append.2 (Or.inl ?_), not_isEmpty_of_mem hm⟩
    exact List.mem_map.2 ⟨a, Finset.mem_toList.2 ha, rfl⟩
  · have hb : b ∈ L := (hcov (a, b) hab).resolve_left ha
    have hm : a.val ∈ (((F.filter (fun e => e.1 ∉ P)).filter (fun e => e.2 = b)).toList.map
        (fun e => e.1.val)) :=
      List.mem_map.2 ⟨(a, b), Finset.mem_toList.2 (Finset.mem_filter.2
        ⟨Finset.mem_filter.2 ⟨hab, ha⟩, rfl⟩), rfl⟩
    refine ⟨(p + b.val, _), ?_, Or.inr ⟨rfl, hm⟩⟩
    refine List.mem_filter.2 ⟨List.mem_append.2 (Or.inr ?_), not_isEmpty_of_mem hm⟩
    exact List.mem_map.2 ⟨b, Finset.mem_toList.2 hb, rfl⟩

lemma inp_cast {p l : ℕ} (x : Fin (p + l) → Bool) (a : Fin p) :
    inp x a.val = x (Fin.castAdd l a) := by
  have h : a.val < p + l := by
    have := a.isLt
    omega
  rw [inp_of_lt x a.val h]
  rfl

lemma inp_nat {p l : ℕ} (x : Fin (p + l) → Bool) (b : Fin l) :
    inp x (p + b.val) = x (Fin.natAdd p b) := by
  have h : p + b.val < p + l := by
    have := b.isLt
    omega
  rw [inp_of_lt x (p + b.val) h]
  rfl

lemma sts_sem (p l : ℕ) (F : Finset (Fin p × Fin l)) (P : Finset (Fin p))
    (L : Finset (Fin l)) (hcov : ∀ e ∈ F, e.1 ∈ P ∨ e.2 ∈ L) (x : Fin (p + l) → Bool) :
    (sts p l F P L).any (starVal x) = true ↔
      ∃ a b, (a, b) ∈ F ∧ x (Fin.castAdd l a) = true ∧ x (Fin.natAdd p b) = true := by
  constructor
  · intro h
    obtain ⟨s, hs, hv⟩ := List.any_eq_true.1 h
    simp only [starVal, Bool.and_eq_true, List.any_eq_true] at hv
    obtain ⟨hv1, w, hw, hv2⟩ := hv
    simp only [sts, List.mem_filter, List.mem_append, stP, stL, List.mem_map,
      Finset.mem_toList] at hs
    rcases hs.1 with ⟨a, _, rfl⟩ | ⟨b, _, rfl⟩
    · simp only [List.mem_map, Finset.mem_toList, Finset.mem_filter] at hw
      obtain ⟨e, ⟨⟨heF, _⟩, hea⟩, rfl⟩ := hw
      refine ⟨e.1, e.2, heF, ?_, ?_⟩
      · rw [← inp_cast x e.1, hea]
        exact hv1
      · rw [← inp_nat x e.2]
        exact hv2
    · simp only [List.mem_map, Finset.mem_toList, Finset.mem_filter] at hw
      obtain ⟨e, ⟨⟨heF, _⟩, heb⟩, rfl⟩ := hw
      refine ⟨e.1, e.2, heF, ?_, ?_⟩
      · rw [← inp_cast x e.1]
        exact hv2
      · rw [← inp_nat x e.2, heb]
        exact hv1
  · rintro ⟨a, b, hab, hxa, hxb⟩
    obtain ⟨s, hs, hcase⟩ := sts_mem p l F P L hcov a b hab
    refine List.any_eq_true.2 ⟨s, hs, ?_⟩
    simp only [starVal, Bool.and_eq_true, List.any_eq_true]
    rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨by rw [h1, inp_cast]; exact hxa, p + b.val, h2, by rw [inp_nat]; exact hxb⟩
    · exact ⟨by rw [h1, inp_nat]; exact hxb, a.val, h2, by rw [inp_cast]; exact hxa⟩

lemma stars : ∀ (p l : ℕ) (F : Finset (Fin p × Fin l)) (P : Finset (Fin p)) (L : Finset (Fin l)),
      F.Nonempty → (∀ e ∈ F, e.1 ∈ P ∨ e.2 ∈ L) →
      ∃ D : Circuit, IsAO2 (p+l) D ∧ D.size+1 ≤ F.card+P.card+L.card ∧
        (∀ j < D.gates.length, (gateAt D j).op = GateOp.and → ∀ x, gateVal (p+l) D j x = true →
          ∃ a b, (a,b)∈F ∧ x (Fin.castAdd l a)=true ∧ x (Fin.natAdd p b)=true) ∧
        ∀ x : Fin (p+l) → Bool, circuitFun (p+l) D x=decide (∃ a b, (a,b)∈F ∧
          x (Fin.castAdd l a)=true ∧ x (Fin.natAdd p b)=true) := by
  intro p l F P L hF hcov
  have hne : sts p l F P L ≠ [] := by
    obtain ⟨⟨a, b⟩, hab⟩ := hF
    obtain ⟨s, hs, _⟩ := sts_mem p l F P L hcov a b hab
    exact List.ne_nil_of_mem hs
  obtain ⟨gs, o, hok, hlen, hval⟩  := build (p + l)
    (fun x => ∃ a b, (a,b)∈F ∧ x (Fin.castAdd l a)=true ∧ x (Fin.natAdd p b)=true)
    (sts p l F P L) hne (sts_wires p l F P L)
    (fun st hst x hval => (sts_sem p l F P L hcov x).mp (List.any_eq_true.mpr ⟨st,hst,hval⟩))
  refine ⟨⟨gs, o⟩, ⟨fun g hg => (hok.1.1 g hg).1, fun j hj i hi => hok.1.2 j hj i hi,
    fun g hg => (hok.1.1 g hg).2⟩, ?_, ?_, fun x => ?_⟩
  · have h1 := sts_sum p l F P L hcov
    have h2 := sts_len p l F P L
    show gs.length + 1 ≤ F.card + P.card + L.card
    omega
  · intro j hj ha x hx
    apply hok.2 j hj _ x hx
    simpa only [gateAt, List.getD_eq_getElem _ _ hj] using ha
  · show val (p + l) gs x o = _
    rw [hval x]
    rw [Bool.eq_iff_iff, sts_sem p l F P L hcov x]
    simp


end PEqualNP.Outside.L_meta_18065.Stars
namespace PEqualNP.Outside.L_meta_18065

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm PEqualNP.EdgeOwnership

theorem localStars {n m : ℕ} (E : Finset (Fin n × Fin m)) (C : Circuit)
    (hn : E.Nonempty)
    (spec : ∀ x : Fin (n+m) → Bool, circuitFun (n+m) C x =
      decide (∃ i j, (i,j)∈E ∧ x (Fin.castAdd m i)=true ∧ x (Fin.natAdd n j)=true))
    (P : Finset (Fin n)) (Q : Finset (Fin m))
    (cover : ∀ e ∈ E, e.1∈P ∨ e.2∈Q) (cost : E.card+P.card+Q.card ≤ C.size+1) :
    ∃ D : Circuit, D.size ≤ C.size ∧ IsAO2 (n+m) D ∧
      (∀ x, circuitFun (n+m) D x = circuitFun (n+m) C x) ∧
      ∀ j < D.gates.length, (NestedCover.gateAt D j).op = GateOp.and → ∀ x,
        gateVal (n+m) D j x=true →
          ∃ i j, (i,j)∈E ∧ x (Fin.castAdd m i)=true ∧ x (Fin.natAdd n j)=true := by
  obtain ⟨D, ao, sz, safe, ev⟩ := Stars.stars n m E P Q hn cover
  exact ⟨D,by omega,ao,fun x => (ev x).trans (spec x).symm,safe⟩

end PEqualNP.Outside.L_meta_18065
namespace PEqualNP.Outside.L_meta_18065

/-- Each matching edge in a subboard of minimum positive degree two injects
into a different off-matching edge of that subboard on the same row. -/
theorem offMatching {n : ℕ} (E F : Finset (Fin n × Fin n)) (p : Fin n → Fin n)
    (sub : F ⊆ E) (mat : ∀ i, (i,p i)∈E)
    (partners : ∀ i j, (i,j)∈F → ∃ k, k≠j ∧ (i,k)∈F) :
    F.card + 2*n ≤ 2*E.card := by
  classical
  let M : Finset (Fin n × Fin n) := Finset.univ.image (fun i => (i,p i))
  have mem (e : Fin n × Fin n) : e∈M ↔ e.2=p e.1 := by
    rcases e with ⟨a,b⟩
    constructor
    · intro h
      obtain ⟨i,_,h⟩ := Finset.mem_image.mp h
      cases h
      rfl
    · intro h
      exact Finset.mem_image.mpr ⟨a,Finset.mem_univ _,Prod.ext rfl h.symm⟩
  have mcard : M.card=n := by
    dsimp [M]
    rw [Finset.card_image_of_injective _ (by intro a b h; exact congrArg Prod.fst h)]
    simp
  have subM : M ⊆ E := by
    intro e h
    rcases e with ⟨a,b⟩
    have eq : b=p a := (mem _).mp h
    simpa [eq] using mat a
  let A := F ∩ M
  let B := F \ M
  have free : ∀ e : A, ∃ d : B, d.val.1=e.val.1 := by
    intro e
    obtain ⟨ef,em⟩ := Finset.mem_inter.mp e.property
    obtain ⟨k,hk,hek⟩ := partners e.val.1 e.val.2 ef
    have kdifferent : k ≠ p e.val.1 := by simpa only [← (mem e.val).mp em] using hk
    refine ⟨⟨(e.val.1,k),Finset.mem_sdiff.mpr ⟨hek,fun h => kdifferent ((mem _).mp h)⟩⟩,rfl⟩
  choose f hf using free
  have inj : Function.Injective f := by
    intro a b h
    have same : a.val.1=b.val.1 := (hf a).symm.trans ((congrArg (fun d : B => d.val.1) h).trans (hf b))
    apply Subtype.ext
    apply Prod.ext same
    rw [(mem a.val).mp (Finset.mem_inter.mp a.property).2,
      (mem b.val).mp (Finset.mem_inter.mp b.property).2,same]
  have ab : A.card ≤ B.card := by simpa using Fintype.card_le_of_injective _ inj
  have bsub : B ⊆ E \ M := by
    intro e he
    exact Finset.mem_sdiff.mpr ⟨sub (Finset.mem_sdiff.mp he).1,(Finset.mem_sdiff.mp he).2⟩
  have bsize := Finset.card_le_card bsub
  have part : B.card + A.card = F.card := Finset.card_sdiff_add_card_inter F M
  have rest : (E \ M).card + M.card = E.card := Finset.card_sdiff_add_card_eq_card subM
  omega

end PEqualNP.Outside.L_meta_18065

namespace PEqualNP.Outside.L_meta_18065
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm PEqualNP.EdgeOwnership
open Census.Core Census.Core.Ten Census.Core.Ten.GraphPacking3241 Census.Core.Ten.LeafCore3241
theorem fiveExtras {n : ℕ} (E : Finset (Fin n × Fin n)) (p : Equiv.Perm (Fin n)) (C : Circuit)
    (hn : 0<n) (sq : FourFree E) (mat : ∀ i, (i,p i)∈E) (ao : IsAO2 (n+n) C)
    (ev : ∀ x : Fin (n+n) → Bool, circuitFun (n+n) C x =
      decide (∃ i j, (i,j)∈E ∧ x (Fin.castAdd n i)=true ∧ x (Fin.natAdd n j)=true))
    (few : E.card ≤ n+5) :
    ∃ D : Circuit, D.size ≤ C.size ∧ IsAO2 (n+n) D ∧
      (∀ x, circuitFun (n+n) D x = circuitFun (n+n) C x) ∧
      ∀ j < D.gates.length, (NestedCover.gateAt D j).op = GateOp.and → ∀ x,
        gateVal (n+n) D j x=true →
          ∃ i j, (i,j)∈E ∧ x (Fin.castAdd n i)=true ∧ x (Fin.natAdd n j)=true := by
  classical
  have sm : SmallMatrix E := by
    intro F sub hp
    have bound := offMatching E F p sub mat (fun i j he => (hp i j he).1)
    omega
  have cnt := from_core_census E sq sm NormalizeCores3241.census
  obtain ⟨P,Q,cov,sz⟩ := price_with_counts n n E C (Census.Core.counts_irrel cnt) ao (by
    intro x
    rw [ev]
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    constructor
    · rintro ⟨a,b,h,ha,hb⟩; exact ⟨(a,b),h,ha,hb⟩
    · rintro ⟨⟨a,b⟩,h,ha,hb⟩; exact ⟨a,b,h,ha,hb⟩)
  exact localStars E C ⟨_,mat ⟨0,hn⟩⟩ ev P Q cov sz
end PEqualNP.Outside.L_meta_18065

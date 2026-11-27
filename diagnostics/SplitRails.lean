import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9809.Split
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def good (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2
def readGate (g : Gate) (w : List Bool) := g.op.eval (g.inputs.map fun i => w.getD i false)
def stage (w : List Bool) (g : Gate) := w ++ [readGate g w]
def run (gs : List Gate) (w : List Bool) := gs.foldl stage w
def below (a b : List Bool) : Prop :=
  a.length = b.length ∧ ∀ i, a.getD i false = true → b.getD i false = true
theorem extend {a b : List Bool} {v w : Bool} (h : below a b) (hv : v=true → w=true) :
    below (a++[v]) (b++[w]) := by
  refine ⟨by simp [h.1], ?_⟩
  intro i
  by_cases lt : i<a.length
  · have lt' : i<b.length := h.1 ▸ lt
    simpa [List.getD_eq_getElem?_getD,List.getElem?_append_left lt,
      List.getElem?_append_left lt'] using h.2 i
  · by_cases eq : i=a.length
    · subst i
      have last (l : List Bool) (x : Bool) : (l++[x]).getD l.length false=x := by
        simp [List.getD_eq_getElem?_getD]
      rw [last,h.1,last]
      exact hv
    · have lo : (a++[v]).length ≤ i := by simp; omega
      simp [List.getD_eq_getElem?_getD,List.getElem?_eq_none lo]
theorem gate_mono {a b : List Bool} {g : Gate} (h : below a b) (hg : good g) :
    readGate g a=true → readGate g b=true := by
  have op : g.op=GateOp.and ∨ g.op=GateOp.or := by simpa using hg.1
  rcases op with ha | ho
  · simp only [readGate,ha,GateOp.eval,List.all_map,List.all_eq_true,Function.comp_apply,id_eq]
    intro ht i hi
    exact h.2 i (ht i hi)
  · simp only [readGate,ho,GateOp.eval,List.any_map,List.any_eq_true,Function.comp_apply,id_eq]
    rintro ⟨i,hi,hh⟩
    exact ⟨i,hi,h.2 i hh⟩
theorem run_mono {a b : List Bool} (gs : List Gate) (ok : ∀ g ∈ gs, good g)
    (h : below a b) : below (run gs a) (run gs b) := by
  induction gs generalizing a b with
  | nil => exact h
  | cons g gs ih =>
    exact ih (fun t ht => ok _ (by simp [ht])) (extend h (gate_mono h (ok _ (by simp))))


def finish (post : List Gate) (out : Nat) (w : List Bool) (bit : Bool) :=
  (run post (w ++ [bit])).getD out false

theorem finish_order (post : List Gate) (goodPost : ∀ g ∈ post, good g)
    (out : Nat) (w : List Bool) :
    finish post out w false = true → finish post out w true = true := by
  have same : below w w := ⟨rfl, fun _ h => h⟩
  have ord : below (w ++ [false]) (w ++ [true]) := extend same (by simp)
  exact (run_mono post goodPost ord).2 out

abbrev Inp := Fin 14 → Bool
theorem retained (pre : List Gate) (w : List Bool) : ∃ t, run pre w=w++t := by
  induction pre generalizing w with
  | nil => exact ⟨[],by simp [run]⟩
  | cons g gs ih =>
    obtain ⟨t,ht⟩ := ih (stage w g)
    exact ⟨[readGate g w]++t,by simpa [run,stage,List.append_assoc] using ht⟩

theorem rawRead (pre : List Gate) (x : Inp) (i : Fin 14) :
    (run pre (List.ofFn x)).getD i.val false=x i := by
  obtain ⟨t,ht⟩ := retained pre (List.ofFn x)
  rw [ht]
  have lt : i.val < (List.ofFn x).length := by simpa using i.isLt
  rw [List.getD_eq_getElem?_getD,List.getElem?_append_left lt]
  fin_cases i <;> rfl

def physical (pre : List Gate) (tap : Gate) (post : List Gate) (out : Nat) : Circuit :=
  ⟨pre++tap::post,out⟩

def setRow (x : Inp) (i : Fin 14) (p : Bool) : Inp := fun j => if j=i then p else x j

theorem rowSame (x : Inp) (i : Fin 14) : setRow x i (x i)=x := by
  funext j
  by_cases h : j=i <;> simp [setRow,h]

def constGate : Bool → Gate
  | true => ⟨.and,[]⟩
  | false => ⟨.or,[]⟩

theorem constEval (pre post : List Gate) (i : Nat) (x : Inp) (c : Bool) :
    (physical pre (constGate c) post i).eval (List.ofFn x)=
      finish post i (run pre (List.ofFn x)) c := by
  change ((pre++constGate c::post).foldl stage (List.ofFn x)).getD i false=_
  cases c <;> simp [finish,run,List.foldl_append,stage,readGate,constGate,GateOp.eval]

theorem rawEval (pre post : List Gate) (i : Nat) (x : Inp) (v : Fin 14) :
    (physical pre ⟨.not,[v.val]⟩ post i).eval (List.ofFn x)=
      finish post i (run pre (List.ofFn x)) (!(x v)) := by
  have rr := rawRead pre x v
  change (pre.foldl stage (List.ofFn x)).getD v.val false=x v at rr
  change ((pre++(⟨.not,[v.val]⟩ : Gate)::post).foldl stage (List.ofFn x)).getD i false=_
  simp [List.foldl_append,finish,run,stage,readGate,GateOp.eval,rr]

theorem guardedConst (pre post : List Gate) (out : Nat) (c : Bool)
    (a : ∀ g∈pre,good g) (b : ∀ g∈post,good g) :
    Monotone2 (physical pre (constGate c) post out) := by
  intro g hg
  change g∈pre++constGate c::post at hg
  rcases List.mem_append.mp hg with hp|hp
  · exact a g hp
  · rcases List.mem_cons.mp hp with rfl|hp
    · cases c <;> simp [constGate,good]
    · exact b g hp

def split (pre post : List Gate) (out : Nat) (v : Fin 14) (x : Inp) (p n : Bool) : Bool :=
  finish post out (run pre (List.ofFn (setRow x v p))) n

def andRow (u : Bool → Bool → Bool) : Prop :=
  u false false=false ∧ u false true=false ∧ u true false=false ∧ u true true=true
def orRow (u : Bool → Bool → Bool) : Prop :=
  u false false=false ∧ u false true=true ∧ u true false=true ∧ u true true=true

theorem fourLaw (a b c d : Bool) (lo : a=true → b=true) (diag : b=true → c=true)
    (hi : c=true → d=true) :
    ((¬(a=false ∧ b=false ∧ c=false ∧ d=true)) → d=c) ∧
    ((¬(a=false ∧ b=true ∧ c=true ∧ d=true)) → a=b) := by
  cases a <;> cases b <;> cases c <;> cases d <;> simp_all

theorem witnesses (pre post : List Gate) (out : Nat) (v : Fin 14)
    (a : ∀ g∈pre,good g) (b : ∀ g∈post,good g) (f : Inp → Bool)
    (up : ∀ x, f (setRow x v false)=true → f (setRow x v true)=true)
    (old : ∀ x, (physical pre ⟨.not,[v.val]⟩ post out).eval (List.ofFn x)=f x)
    (floor : ∀ C : Circuit, Monotone2 C →
      C.size≤(physical pre ⟨.not,[v.val]⟩ post out).size → ¬∀ x : Inp,C.eval (List.ofFn x)=f x) :
    (∃ x,andRow (split pre post out v x)) ∧ (∃ x,orRow (split pre post out v x)) := by
  classical
  let S := split pre post out v
  have actual (x : Inp) (p : Bool) : S x p (!p)=f (setRow x v p) := by
    have ho := old (setRow x v p)
    rw [rawEval] at ho
    simpa [S,split,setRow] using ho
  have law (x : Inp) :=
    fourLaw (S x false false) (S x false true) (S x true false) (S x true true)
      (finish_order post b out _)
      (by intro h; have low := actual x false; have high := actual x true
          simp only [Bool.not_false,Bool.not_true] at low high
          exact high.trans (up x (low.symm.trans h)))
      (finish_order post b out _)
  have cannot (c : Bool) : ¬∀ x : Inp, S x (x v) c=f x := by
    intro agree
    apply floor (physical pre (constGate c) post out) (guardedConst pre post out c a b)
      (by simp [physical,Circuit.size])
    intro x
    have h := agree x
    rw [constEval]
    simpa [S,split,rowSame] using h
  constructor
  · by_contra! no
    apply cannot true
    intro x
    cases e : x v with
    | false =>
      have h := actual x false
      have row : setRow x v false=x := e ▸ rowSame x v
      rw [row] at h
      exact h
    | true =>
      have eq := (law x).1 (no x)
      have h := actual x true
      have row : setRow x v true=x := e ▸ rowSame x v
      rw [row] at h
      exact eq.trans h
  · by_contra! no
    apply cannot false
    intro x
    cases e : x v with
    | false =>
      have eq := (law x).2 (no x)
      have h := actual x false
      have row : setRow x v false=x := e ▸ rowSame x v
      rw [row] at h
      exact eq.trans h
    | true =>
      have h := actual x true
      have row : setRow x v true=x := e ▸ rowSame x v
      rw [row] at h
      exact h

theorem separator {Y : Type} (gs : List Gate) (ok : ∀ g∈gs,good g) (out : Nat)
    (bank : Y → Bool → Bool → List Bool) (y z : Y)
    (ha : andRow (fun p n => (run gs (bank y p n)).getD out false))
    (ho : orRow (fun p n => (run gs (bank z p n)).getD out false)) :
    (¬below (bank y true true) (bank z false false)) ∧
    (∀ t p,(run gs (bank t p (!p))).getD out false=false →
      ¬below (bank y true true) (bank t p (!p))) ∧
    (∀ t p,(run gs (bank t p (!p))).getD out false=true →
      ¬below (bank t p (!p)) (bank z false false)) := by
  have sep (u v : List Bool) (yes : (run gs u).getD out false=true)
      (no : (run gs v).getD out false=false) : ¬below u v := by
    intro ord
    have bad := (run_mono gs ok ord).2 out yes
    exact Bool.noConfusion (no.symm.trans bad)
  exact ⟨sep _ _ ha.2.2.2 ho.1,fun _ _ h => sep _ _ ha.2.2.2 h,fun _ _ h => sep _ _ h ho.1⟩

end PEqualNP.Outside.L_meta_9809.Split

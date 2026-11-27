import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9809.Rectangles
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


def value (gs : List Gate) (o : Nat) (b : List Bool) := (run gs b).getD o false

theorem value_mono (gs : List Gate) (ok : ∀ g∈gs,good g) (o : Nat)
    {a b : List Bool} (h : below a b) : value gs o a=true → value gs o b=true :=
  (run_mono gs ok h).2 o

theorem below_trans {a b c : List Bool} (h : below a b) (k : below b c) : below a c :=
  ⟨h.1.trans k.1,fun i hh => k.2 i (h.2 i hh)⟩

def table {α : Type} (r : α → Bool) (lo hi : α → List Bool) (x : α) :=
  if r x then hi x else lo x

def positive {α : Type} (E : Set α) (base lo : α → List Bool) : Set α :=
  {e | e∈E ∧ ∀ p∈E, ¬below (base p) (lo e)}

def negative {α : Type} (N : Set α) (base hi : α → List Bool) : Set α :=
  {i | i∈N ∧ ∀ q∈N, ¬below (hi i) (base q)}

theorem rectangleReplacement {α : Type} [Preorder α]
    (gs : List Gate) (ok : ∀ g∈gs,good g) (o : Nat) (f : α → Bool)
    (base lo hi : α → List Bool) (E N : Set α) (menu : Set (α → Bool))
    (exactBase : ∀ x, value gs o (base x)=f x)
    (ord : ∀ x,below (lo x) (base x) ∧ below (base x) (hi x))
    (lm : ∀ x y : α,x≤y → below (lo x) (lo y))
    (hm : ∀ x y : α,x≤y → below (hi x) (hi y))
    (em : ∀ e∈E,f e=true) (nm : ∀ i∈N,f i=false)
    (ec : ∀ x,f x=true → ∃ e∈E,e≤x)
    (nc : ∀ x,f x=false → ∃ i∈N,x≤i)
    (inc : ∀ r∈menu,∀ x y : α,x≤y → r x=true → r y=true)
    (cover : ∀ (P Q : Set α), P ⊆ positive E base lo → Q ⊆ negative N base hi →
      (∀ e∈P,∀ i∈Q,¬below (hi i) (lo e)) →
      ∃ r∈menu,(∀ e∈P,r e=true) ∧ (∀ i∈Q,r i=false)) :
    ∃ r∈menu,∀ x,value gs o (table r lo hi x)=f x := by
  classical
  let P : Set α := {e | e∈E ∧ value gs o (lo e)=false}
  let Q : Set α := {i | i∈N ∧ value gs o (hi i)=true}
  have hp : P ⊆ positive E base lo := by
    intro e he
    obtain ⟨he,wrong⟩ := he
    refine ⟨he,?_⟩
    intro p pE le
    have hx := value_mono gs ok o le ((exactBase p).trans (em p pE))
    simp [wrong] at hx
  have hq : Q ⊆ negative N base hi := by
    intro i h
    obtain ⟨h,wrong⟩ := h
    refine ⟨h,?_⟩
    intro q qN le
    have hx := value_mono gs ok o le wrong
    rw [exactBase q,nm q qN] at hx
    contradiction
  have joint : ∀ e∈P,∀ i∈Q,¬below (hi i) (lo e) := by
    intro e he i hi' le
    have hx := value_mono gs ok o le hi'.2
    rw [he.2] at hx
    contradiction
  obtain ⟨r,hr,rp,rq⟩ := cover P Q hp hq joint
  have monotoneTable {x y : α} (h : x≤y) : below (table r lo hi x) (table r lo hi y) := by
    cases a : r x <;> cases b : r y
    · simpa [table,a,b] using lm x y h
    · simpa [table,a,b] using below_trans (lm x y h) (below_trans (ord y).1 (ord y).2)
    · have bad := inc r hr x y h a
      simp [b] at bad
    · simpa [table,a,b] using hm x y h
  have eGood (e : α) (he : e∈E) : value gs o (table r lo hi e)=true := by
    cases a : r e
    · cases b : value gs o (lo e)
      · have bad := rp e ⟨he,b⟩
        simp [a] at bad
      · simpa [table,a] using b
    · simpa [table,a] using value_mono gs ok o (ord e).2 ((exactBase e).trans (em e he))
  have iGood (i : α) (hi' : i∈N) : value gs o (table r lo hi i)=false := by
    cases a : r i
    · cases b : value gs o (lo i)
      · simpa [table,a] using b
      · have bad := value_mono gs ok o (ord i).1 b
        rw [exactBase i,nm i hi'] at bad
        contradiction
    · cases b : value gs o (hi i)
      · simpa [table,a] using b
      · have bad := rq i ⟨hi',b⟩
        simp [a] at bad
  refine ⟨r,hr,?_⟩
  intro x
  cases h : f x
  · obtain ⟨i,im,le⟩ := nc x h
    cases b : value gs o (table r lo hi x)
    · rfl
    · have bad := value_mono gs ok o (monotoneTable le) b
      rw [iGood i im] at bad
      contradiction
  · obtain ⟨e,ep,le⟩ := ec x h
    exact value_mono gs ok o (monotoneTable le) (eGood e ep)
end PEqualNP.Outside.L_meta_9809.Rectangles

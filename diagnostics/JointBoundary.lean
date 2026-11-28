import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9809.JointBoundary
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

-- The original positive and negative rails may each have several physical suffix readers.
-- Here bank a b x contains the whole live input list after choosing both rail values.
def lowerUsable {A : Type} (E : Set A) (old : A → List Bool)
    (bank : Bool → Bool → A → List Bool) (e : A) (a b : Bool) : Prop :=
  ∃ p∈E, below (old p) (bank a b e)
def upperUsable {A : Type} (N : Set A) (old : A → List Bool)
    (bank : Bool → Bool → A → List Bool) (i : A) (a b : Bool) : Prop :=
  ∃ q∈N, below (bank a b i) (old q)

theorem jointReplacement {A : Type} [Preorder A]
    (gs : List Gate) (hg : ∀ g∈gs,good g) (o : Nat) (target : A → Bool)
    (old : A → List Bool) (bank : Bool → Bool → A → List Bool)
    (u v : A → Bool) (E N : Set A)
    (correct : ∀ x, value gs o (old x)=target x)
    (ep : ∀ e∈E,target e=true) (ip : ∀ q∈N,target q=false)
    (edges : ∀ x,target x=true → ∃ e∈E,e≤x)
    (maximal : ∀ x,target x=false → ∃ q∈N,x≤q)
    (monotone : ∀ x y : A,x≤y → below (bank (u x) (v x) x) (bank (u y) (v y) y))
    (pe : ∀ e∈E, lowerUsable E old bank e (u e) (v e))
    (ni : ∀ i∈N, upperUsable N old bank i (u i) (v i)) :
    ∀ x, value gs o (bank (u x) (v x) x) = target x := by
  intro x
  cases h : target x with
  | false =>
    obtain ⟨i,hi,le⟩ := maximal x h
    obtain ⟨q,hq,atQ⟩ := ni i hi
    cases b : value gs o (bank (u x) (v x) x) with
    | false => rfl
    | true =>
      have bad := value_mono gs hg o (below_trans (monotone x i le) atQ) b
      rw [correct q,ip q hq] at bad
      contradiction
  | true =>
    obtain ⟨e,he,le⟩ := edges x h
    obtain ⟨p,hp,atP⟩ := pe e he
    exact value_mono gs hg o (below_trans atP (monotone e x le)) ((correct p).trans (ep p hp))

def improves {A : Type} (E N : Set A) (a b : A → Bool) :=
  (∀e∈E,a e=true → b e=true) ∧ (∀i∈N,b i=true → a i=true)
theorem comp_and {A : Type} {E N : Set A} {a b u v : A → Bool}
    (ha : improves E N a u) (hb : improves E N b v) :
    improves E N (fun x => a x && b x) (fun x => u x && v x) := by
  constructor
  · intro x hx h
    simp only [Bool.and_eq_true] at h ⊢
    exact ⟨ha.1 _ hx h.1,hb.1 _ hx h.2⟩
  · intro x hx h
    simp only [Bool.and_eq_true] at h ⊢
    exact ⟨ha.2 _ hx h.1,hb.2 _ hx h.2⟩
theorem comp_or {A : Type} {E N : Set A} {a b u v : A → Bool}
    (ha : improves E N a u) (hb : improves E N b v) :
    improves E N (fun x => a x || b x) (fun x => u x || v x) := by
  constructor
  · intro x hx h
    cases e : a x <;> cases f : b x <;> simp_all [ha.1 x hx,hb.1 x hx]
  · intro x hx h
    cases e : u x <;> cases f : v x <;> simp_all [ha.2 x hx,hb.2 x hx]
end PEqualNP.Outside.L_meta_9809.JointBoundary

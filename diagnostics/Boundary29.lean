import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_9755.Boundary
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
/-- The rows of the second frontier are covered from below on positives and from above
on negatives by rows of the first frontier. All wires use a common order. -/
def covers {A B : Type} (a : A → List Bool) (b : B → List Bool)
    (f : A → Bool) (g : B → Bool) : Prop :=
  (∀ x, g x=true → ∃ y, f y=true ∧ below (a y) (b x)) ∧
  (∀ x, g x=false → ∃ y, f y=false ∧ below (b x) (a y))
theorem monotone_suffix_transfer {A B : Type} (a : A → List Bool) (b : B → List Bool)
    (f : A → Bool) (g : B → Bool) (h : covers a b f g)
    (gs : List Gate) (ok : ∀ t ∈ gs, good t) (out : Nat)
    (hs : ∀ y, (run gs (a y)).getD out false = f y) :
    ∀ x, (run gs (b x)).getD out false = g x := by
  intro x
  cases e : g x with
  | true =>
    obtain ⟨y,hy,hxy⟩ := h.1 x e
    exact (run_mono gs ok hxy).2 out ((hs y).trans hy)
  | false =>
    obtain ⟨y,hy,hxy⟩ := h.2 x e
    cases hv : (run gs (b x)).getD out false with
    | false => rfl
    | true =>
      have hpos := (run_mono gs ok hxy).2 out hv
      rw [hs,hy] at hpos
      contradiction

abbrev Raw := Fin 1024
def edges : List Raw := [6, 12, 17, 24, 33, 66, 132, 160, 264, 288, 320, 528, 576, 640]
def independent : List Raw := [50, 69, 104, 116, 139, 201, 208, 276, 387, 402, 523, 548, 554, 771, 773]

def subset (x y : Raw) : Bool := (x.val &&& y.val)==x.val
def graph (x : Raw) := edges.any fun p => subset p x
theorem transBelow {a b c : List Bool} (h : below a b) (g : below b c) : below a c :=
  ⟨h.1.trans g.1, fun i hi => g.2 i (h.2 i hi)⟩

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem borderCovers : ∀ r : Raw, (graph r || independent.any (fun i => subset r i)) = true := by
  decide +kernel

theorem positiveBorder : ∀ r∈edges, graph r=true := by
  intro r hr
  exact List.any_eq_true.mpr ⟨r,hr,by simp [subset]⟩

theorem negativeBorder : independent.all (fun r => !(graph r))=true := by decide +kernel

theorem sufficient (a b : Raw → List Bool)
    (mono : ∀ x y,subset x y=true → below (b x) (b y))
    (pos : ∀ p∈edges,below (a p) (b p))
    (neg : ∀ q∈independent,below (b q) (a q)) :
    covers a b graph graph := by
  constructor
  · intro x hx
    obtain ⟨p,hp,hpx⟩ := List.any_eq_true.mp hx
    exact ⟨p,positiveBorder p hp,transBelow (pos p hp) (mono p x hpx)⟩
  · intro x hx
    have h := borderCovers x
    rw [hx] at h
    simp only [Bool.false_or] at h
    obtain ⟨q,hq,hxq⟩ := List.any_eq_true.mp h
    have pr := List.all_eq_true.mp negativeBorder q hq
    exact ⟨q,by simpa using pr,transBelow (mono x q hxq) (neg q hq)⟩

theorem physical_suffix_29 (a b : Raw → List Bool)
    (mono : ∀ x y,subset x y=true → below (b x) (b y))
    (pos : ∀ p∈edges,below (a p) (b p))
    (neg : ∀ q∈independent,below (b q) (a q))
    (gs : List Gate) (hg : ∀ g∈gs,good g) (output : Nat)
    (ok : ∀ x, (run gs (a x)).getD output false=graph x) :
    ∀ x, (run gs (b x)).getD output false=graph x :=
  monotone_suffix_transfer a b graph graph (sufficient a b mono pos neg) gs hg output ok

end PEqualNP.Outside.L_meta_9755.Boundary

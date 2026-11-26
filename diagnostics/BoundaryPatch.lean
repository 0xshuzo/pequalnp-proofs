import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9815.BoundaryPatch
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

theorem retap {α : Type} (post : List Gate) (mono : ∀ g ∈ post, good g)
    (out : Nat) (bank : α → List Bool) (h f r : α → Bool)
    (old : ∀ x, finish post out (bank x) (!(h x)) = f x)
    (keepOn : ∀ x, f x=true → h x=false → r x=true)
    (keepOff : ∀ x, f x=false → h x=true → r x=false) :
    ∀ x, finish post out (bank x) (r x) = f x := by
  intro x
  let lo := finish post out (bank x) false
  let hi := finish post out (bank x) true
  have law : ∀ H F R A B : Bool, (A=true → B=true) →
      (if H then A else B)=F → (F=true → H=false → R=true) →
      (F=false → H=true → R=false) → (if R then B else A)=F := by
    intro H F R A B
    cases H <;> cases F <;> cases R <;> cases A <;> cases B <;> decide
  have comp : (if h x then lo else hi)=f x := by
    cases hh : h x <;> simpa [hh,lo,hi] using old x
  have result := law (h x) (f x) (r x) lo hi (finish_order post mono out (bank x))
    comp (keepOn x) (keepOff x)
  cases hr : r x <;> simpa [hr,lo,hi] using result


abbrev Inp := Fin 14 → Bool
def pairOn (e : Fin 14 × Fin 14) : Inp := fun v => decide (v=e.1 ∨ v=e.2)
def onEdge (e : Fin 14 × Fin 14) (x : Inp) := x e.1 && x e.2
def graph (E : List (Fin 14 × Fin 14)) (x : Inp) := E.any (fun e => onEdge e x)
def increasing (h : Inp → Bool) := ∀ x y, (∀ i, x i=true → y i=true) → h x=true → h y=true


def incl (x y : Inp) : Prop := ∀ i, x i=true → y i=true
def add (x : Inp) (i : Fin 14) : Inp := fun j => if j=i then true else x j
def maximalOff (E : List (Fin 14 × Fin 14)) (x : Inp) : Prop :=
  graph E x=false ∧ ∀ i, x i=false → graph E (add x i)=true

theorem incAdd (x : Inp) (i : Fin 14) : incl x (add x i) := by
  intro j hj
  by_cases eq : j=i <;> simp [add,eq,hj]
theorem addInc {x y : Inp} (i : Fin 14) (le : incl x y) : incl (add x i) (add y i) := by
  intro j hj
  by_cases eq : j=i
  · simp [add,eq]
  · have z : y j=true := le j (by simpa [add,eq] using hj)
    simpa [add,eq] using z
theorem graphInc (E : List (Fin 14 × Fin 14)) : increasing (graph E) := by
  intro x y le on
  obtain ⟨e,he,ev⟩ := List.any_eq_true.mp on
  obtain ⟨a,b⟩ := Bool.and_eq_true_iff.mp ev
  exact List.any_eq_true.mpr ⟨e,he,Bool.and_eq_true_iff.mpr ⟨le _ a,le _ b⟩⟩

theorem saturate (E : List (Fin 14 × Fin 14)) (x : Inp) (off : graph E x=false)
    (L : List (Fin 14)) :
    ∃ y, incl x y ∧ graph E y=false ∧ ∀ i∈L, y i=false → graph E (add y i)=true := by
  induction L with
  | nil => exact ⟨x,fun _ h => h,off,by simp⟩
  | cons a L ih =>
    obtain ⟨y,hxy,hy,hL⟩ := ih
    cases ha : graph E (add y a) with
    | true =>
      refine ⟨y,hxy,hy,?_⟩
      intro i hi iz
      rcases List.mem_cons.mp hi with rfl|h
      · exact ha
      · exact hL _ h iz
    | false =>
      refine ⟨add y a,fun i hi => incAdd y a i (hxy i hi),ha,?_⟩
      intro i hi iz
      have ia : i≠a := by rintro rfl; simp [add] at iz
      have old : y i=false := by simpa [add,ia] using iz
      have mem : i∈L := (List.mem_cons.mp hi).resolve_left ia
      exact graphInc E _ _ (addInc i (incAdd y a)) (hL i mem old)

theorem maximalExtension (E : List (Fin 14 × Fin 14)) (x : Inp) (off : graph E x=false) :
    ∃ y, incl x y ∧ maximalOff E y := by
  obtain ⟨y,h,hy,all⟩ := saturate E x off (List.finRange 14)
  exact ⟨y,h,hy,fun i hi => all i (by simp) hi⟩

theorem boundaryRepair (E : List (Fin 14 × Fin 14))
    (post : List Gate) (goodPost : ∀ g∈post, good g) (out : Nat) (bank : Inp → List Bool)
    (h r : Inp → Bool) (hi : increasing h) (ri : increasing r)
    (pos : ∀ e∈E, h (pairOn e)=false → r (pairOn e)=true)
    (neg : ∀ m, maximalOff E m → h m=true → r m=false)
    (old : ∀ x, finish post out (bank x) (!(h x))=graph E x) :
    ∀ x, finish post out (bank x) (r x)=graph E x := by
  apply retap post goodPost out bank h (graph E) r old
  · intro x fx hx
    obtain ⟨e,he,both⟩ := List.any_eq_true.mp fx
    obtain ⟨ha,hb⟩ := Bool.and_eq_true_iff.mp both
    have le : incl (pairOn e) x := by
      intro i h
      rcases (show i=e.1 ∨ i=e.2 by simpa [pairOn] using h) with rfl|rfl
      · exact ha
      · exact hb
    have hn : h (pairOn e)=false := by
      cases z : h (pairOn e) with
      | false => rfl
      | true => have bad := hi _ _ le z; rw [hx] at bad; cases bad
    exact ri _ _ le (pos e he hn)
  · intro x fx hx
    obtain ⟨m,le,hm⟩ := maximalExtension E x fx
    have avoid := neg m hm (hi _ _ le hx)
    cases eq : r x with
    | false => rfl
    | true => have bad := ri _ _ le eq; rw [avoid] at bad; cases bad

end PEqualNP.Outside.L_meta_9815.BoundaryPatch

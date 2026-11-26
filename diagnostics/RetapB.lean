import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9809.FaceClamp
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
      (F=false → H=true → R=false) → (if R then B else A)=F := by decide +kernel
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

theorem edgeRepair (E : List (Fin 14 × Fin 14)) (e : Fin 14 × Fin 14) (he : e∈E)
    (post : List Gate) (mono : ∀ g∈post, good g) (out : Nat) (bank : Inp → List Bool)
    (h : Inp → Bool) (inc : increasing h)
    (cover : ∀ b ∈ E, b≠e → h (pairOn b)=true)
    (old : ∀ x, finish post out (bank x) (!(h x))=graph E x) :
    ∀ x, finish post out (bank x) (onEdge e x)=graph E x := by
  apply retap post mono out bank h (graph E) (onEdge e) old
  · intro x fx hx
    obtain ⟨u,hu,atU⟩ := List.any_eq_true.mp fx
    by_cases same : u=e
    · simpa [same] using atU
    · have up : ∀ i, pairOn u i=true → x i=true := by
        intro i hi
        have p := Bool.and_eq_true_iff.mp atU
        have a : i=u.1 ∨ i=u.2 := by simpa [pairOn] using hi
        rcases a with rfl|rfl
        · exact p.1
        · exact p.2
      have ht := inc (pairOn u) x up (cover u hu same)
      rw [hx] at ht
      cases ht
  · intro x fx _
    cases bit : onEdge e x with
    | false => rfl
    | true =>
      have contra : graph E x=true := List.any_eq_true.mpr ⟨e,he,bit⟩
      rw [fx] at contra
      cases contra

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
def positiveTap (e : Fin 14 × Fin 14) : Gate := ⟨.and,[e.1.val,e.2.val]⟩

theorem physicalRepair (E : List (Fin 14 × Fin 14)) (e : Fin 14 × Fin 14) (he : e∈E)
    (pre post : List Gate) (goodPre : ∀ g ∈ pre, good g) (goodPost : ∀ g ∈ post, good g)
    (wire out : Nat) (h : Inp → Bool) (inc : increasing h)
    (signal : ∀ x, (run pre (List.ofFn x)).getD wire false=h x)
    (cover : ∀ b∈E, b≠e → h (pairOn b)=true)
    (old : ∀ x, (physical pre ⟨.not,[wire]⟩ post out).eval (List.ofFn x) = graph E x) :
    Monotone2 (physical pre (positiveTap e) post out) ∧
    (physical pre (positiveTap e) post out).size=(physical pre ⟨.not,[wire]⟩ post out).size ∧
    ∀ x, (physical pre (positiveTap e) post out).eval (List.ofFn x)=graph E x := by
  refine ⟨?_,by simp [physical,Circuit.size],?_⟩
  · intro g hg
    change g∈pre++positiveTap e::post at hg
    rcases List.mem_append.mp hg with hp|hp
    · exact goodPre g hp
    · rcases List.mem_cons.mp hp with rfl|hp
      · simp [good,positiveTap]
      · exact goodPost g hp
  · let bank (x : Inp) := run pre (List.ofFn x)
    have old' (x : Inp) : finish post out (bank x) (!(h x)) = graph E x := by
      have z := old x
      change ((pre++(⟨.not,[wire]⟩ : Gate)::post).foldl stage (List.ofFn x)).getD out false=_ at z
      have hh := signal x
      change (pre.foldl stage (List.ofFn x)).getD wire false=h x at hh
      simpa [List.foldl_append,stage,readGate,GateOp.eval,finish,run,bank,hh] using z
    have now := edgeRepair E e he post goodPost out bank h inc cover old'
    intro x
    change ((pre++positiveTap e::post).foldl stage (List.ofFn x)).getD out false=_
    have ra := rawRead pre x e.1
    have rb := rawRead pre x e.2
    change (pre.foldl stage (List.ofFn x)).getD e.1.val false=x e.1 at ra
    change (pre.foldl stage (List.ofFn x)).getD e.2.val false=x e.2 at rb
    simpa [List.foldl_append,run,bank,stage,readGate,GateOp.eval,finish,onEdge,positiveTap,ra,rb] using now x
end PEqualNP.Outside.L_meta_9809.FaceClamp

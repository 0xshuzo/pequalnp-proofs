import Mathlib
import PEqualNP.Defs

namespace Graft4706
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

theorem getLastWire (xs : List Bool) (v : Bool) :
    (xs ++ [v]).getD xs.length false = v := by
  rw [List.getD_append_right _ _ _ _ (by omega)]
  simp

def wmap (n m : ℕ) (π : Fin n → Fin m) (w : ℕ) : ℕ :=
  if h : w < n then (π ⟨w, h⟩ : ℕ) else w - n + m

/-- A gate with its wires renamed. -/
def relGate (n m : ℕ) (π : Fin n → Fin m) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (wmap n m π)⟩

/-- A circuit with its wires renamed. -/
def relabel (n m : ℕ) (π : Fin n → Fin m) (C : Circuit) : Circuit :=
  ⟨C.gates.map (relGate n m π), wmap n m π C.output⟩

/-- One gate evaluated on a wire list. -/
def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

/-- The invariant: the wire lists match along the renaming. -/
def Rel (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) : Prop :=
  n ≤ W.length ∧ W'.length + n = W.length + m ∧
    ∀ w : ℕ, W'.getD (wmap n m π w) false = W.getD w false

theorem rel_step (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) (g : Gate)
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
    rw [he, hw, getLastWire, getLastWire]
  · have hge : W'.length + 1 ≤ wmap n m π w := by
      unfold wmap
      split
      · omega
      · omega
    rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

theorem rel_fold (n m : ℕ) (π : Fin n → Fin m) (gs : List Gate) :
    ∀ W W' : List Bool, Rel n m π W W' →
      Rel n m π (gs.foldl step W) ((gs.map (relGate n m π)).foldl step W') := by
  induction gs with
  | nil => intro W W' h; exact h
  | cons g gs ih =>
    intro W W' h
    exact ih _ _ (rel_step n m π W W' g h)

theorem rel_init (n m : ℕ) (π : Fin n → Fin m) (x : Fin m → Bool) :
    Rel n m π (List.ofFn (x ∘ π)) (List.ofFn x) := by
  refine ⟨by simp, by simp; omega, ?_⟩
  intro w
  unfold wmap
  split
  · rename_i hw
    rw [List.getD_eq_getElem _ _ (by simp), List.getD_eq_getElem _ _ (by simpa using hw)]
    simp
  · rename_i hw
    rw [List.getD_eq_default _ _ (by simp), List.getD_eq_default _ _ (by simp; omega)]

def run (gs : List Gate) (w : List Bool) := (Circuit.mk gs 0).wires w

theorem lengthRun (gs : List Gate) (w : List Bool) : (run gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [run,Circuit.wires]
  | cons g rest ih =>
    change (run rest (w ++ [_])).length = _
    rw [ih]
    simp
    omega

theorem keep (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (run gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g rest ih =>
    change (run rest (w ++ [_])).getD i false = _
    rw [ih _ (by simp; omega),List.getD_append _ _ _ _ hi]

theorem join (m : ℕ) (P C : Circuit) (pmono : Monotone2 P) (cmono : Monotone2 C)
    (hp : P.output < m + P.size) :
    let D : Circuit := ⟨P.gates ++ C.gates ++ [⟨.or,[P.output,C.output]⟩],m+P.size+C.size⟩
    Monotone2 D ∧ D.size = P.size + C.size + 1 ∧
      ∀ w : List Bool, w.length = m → D.eval w = (P.eval w || C.eval (P.wires w)) := by
  let g : Gate := ⟨.or,[P.output,C.output]⟩
  let D : Circuit := ⟨P.gates ++ C.gates ++ [g],m + P.size + C.size⟩
  have mono : Monotone2 D := by
    intro a ha
    change a ∈ P.gates ++ C.gates ++ [g] at ha
    simp only [List.mem_append,List.mem_singleton] at ha
    rcases ha with (h | h) | h
    · exact pmono a h
    · exact cmono a h
    · subst a
      simp [g]
  refine ⟨mono,by simp [D,Circuit.size,Nat.add_assoc],?_⟩
  intro w hw
  let u := P.wires w
  let v := C.wires u
  have hu : u.length = m + P.size := by simpa only [u,run,Circuit.size,Circuit.wires,hw] using lengthRun P.gates w
  have hv : v.length = m + P.size + C.size := (lengthRun C.gates u).trans (by rw [hu]; rfl)
  have hkeep : v.getD P.output false = u.getD P.output false := keep C.gates u _ (by rw [hu]; exact hp)
  change (((P.gates ++ C.gates ++ [g]).foldl _ w).getD (m + P.size + C.size) false) = _
  simp only [List.foldl_append,List.foldl_cons,List.foldl_nil]
  change (v ++ [g.op.eval (g.inputs.map (fun i => v.getD i false))]).getD (m + P.size + C.size) false = _
  rw [← hv,List.getD_append_right _ _ _ _ (by omega)]
  change ([g.op.eval (g.inputs.map (fun i => v.getD i false))]).getD (v.length - v.length) false = (u.getD P.output false || v.getD C.output false)
  rw [Nat.sub_self]
  change GateOp.or.eval [v.getD P.output false,v.getD C.output false] = _
  rw [hkeep]
  simp [GateOp.eval]


def back (n : ℕ) (gs : List Gate) :=
  ∀ j (hj : j < gs.length), ∀ i ∈ gs[j].inputs, i < n+j

theorem back_iff (n : ℕ) (C : Circuit) : ReadsBack n C ↔ back n C.gates := by
  have eq (j : ℕ) (hj : j<C.gates.length) : gateAt C j = C.gates[j] := List.getD_eq_getElem _ _ hj
  constructor <;> intro h j hj i hi
  · exact h j hj i (by rwa [eq j hj])
  · exact h j hj i (by rwa [← eq j hj])

theorem back_append {n : ℕ} {p q : List Gate} (a : back n p) (b : back (n+p.length) q) :
    back n (p++q) := by
  intro i hi
  by_cases hl : i < p.length
  · simpa only [List.getElem_append_left hl] using a i hl
  · have hr : i-p.length < q.length := by simp only [List.length_append] at hi; omega
    have add : n+p.length+(i-p.length) = n+i := by omega
    simpa only [List.getElem_append_right (by omega : p.length ≤ i),add] using b (i-p.length) hr

theorem renamed_back (n m : ℕ) (π : Fin n → Fin m) (C : Circuit) (h : ReadsBack n C) :
    ReadsBack m (relabel n m π C) := by
  apply (back_iff _ _).mpr
  intro j hj w hw
  have jc : j<C.gates.length := by simpa [relabel] using hj
  have jm : j < (C.gates.map (relGate n m π)).length := by simpa only [List.length_map] using jc
  have lookup : (C.gates.map (relGate n m π))[j]'jm = relGate n m π (C.gates[j]'jc) := by
    rw [List.getElem_map]
  have renamed : w ∈ (C.gates[j]'jc).inputs.map (wmap n m π) := by
    change w ∈ (relGate n m π (C.gates[j]'jc)).inputs
    rw [← lookup]
    exact hw
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp renamed
  have bound := (back_iff _ _).mp h j jc i hi
  dsimp [wmap]
  split
  · have hraw := (π ⟨i,by assumption⟩).isLt; omega
  · omega

theorem main : ∀ (n m : ℕ) (P C : Circuit) (π : Fin m → Fin (n+P.size)), Monotone2 P → ReadsBack n P →
      P.output < n+P.size → Monotone2 C → ReadsBack m C → C.output < m+C.size →
      ∃ D : Circuit, Monotone2 D ∧ ReadsBack n D ∧ D.size = P.size+C.size+1 ∧
        ∀ x : Fin n → Bool, circuitFun n D x =
          (circuitFun n P x || circuitFun m C (fun i => (P.wires (List.ofFn x)).getD (π i).val false)) := by
  intro n m P C π pmono pback hp cmono cback hc
  let M := n+P.size
  let A := relabel m M π C
  have aMono : Monotone2 A := by
    intro g hg
    obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hg
    simpa only [relGate,List.length_map] using cmono z hz
  have aBack : ReadsBack M A := renamed_back m M π C cback
  have asize : A.size = C.size := by simp [A,relabel,Circuit.size]
  have aout : A.output < M + A.size := by
    change wmap m M π C.output < _
    rw [asize]
    unfold wmap
    split
    · have raw := (π ⟨C.output,by assumption⟩).isLt; omega
    · omega
  let g : Gate := ⟨.or,[P.output,A.output]⟩
  let D : Circuit := ⟨P.gates ++ A.gates ++ [g],n+P.size+A.size⟩
  obtain ⟨dm,sz,sem⟩ := join n P A pmono aMono hp
  have b1 := back_append ((back_iff _ _).mp pback) ((back_iff _ _).mp aBack)
  have db : ReadsBack n D := by
    apply (back_iff n D).mpr
    apply back_append b1
    intro j hj
    have z : j=0 := by simpa [g] using hj
    subst j
    intro i hi
    rcases (by simpa [g] using hi : i=P.output ∨ i=A.output) with rfl|rfl
    · simp only [List.length_append]; change P.output < n+(P.size+A.size)+0; omega
    · simp only [List.length_append]; change A.output < n+(P.size+A.size)+0
      dsimp [M] at aout; omega
  refine ⟨D,dm,db,sz.trans (by rw [asize]),?_⟩
  intro x
  have E := sem (List.ofFn x) (by simp)
  change D.eval (List.ofFn x) = _
  rw [E]
  let w := P.wires (List.ofFn x)
  have wl : w.length = M := (lengthRun P.gates (List.ofFn x)).trans (by simp [M,Circuit.size])
  let y (i : Fin M) := w.getD i.val false
  have unpack : List.ofFn y = w := by
    apply List.ext_getElem
    · simpa [wl]
    · intro j hj h'w
      simp only [List.getElem_ofFn,y,List.getD_eq_getElem _ _ h'w]
  have rel := rel_fold m M π C.gates _ _ (rel_init m M π y)
  have sim := rel.2.2 C.output
  change (relabel m M π C).eval (List.ofFn y) = C.eval (List.ofFn (y ∘ π)) at sim
  rw [unpack] at sim
  change (P.eval (List.ofFn x) || A.eval w) = _
  rw [show A.eval w = circuitFun m C (y ∘ π) from sim]
  rfl

end Graft4706

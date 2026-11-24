import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace Cross2223

private def scan (step : List α → Gate → α) (gs : List Gate) (w : List α) : List α :=
  gs.foldl (fun w g => w ++ [step w g]) w

private theorem scan_cons (step : List α → Gate → α) (g : Gate) (gs : List Gate) (w : List α) :
    scan step (g :: gs) w = scan step gs (w ++ [step w g]) := rfl

private theorem scan_append (step : List α → Gate → α) (gs hs : List Gate) (w : List α) :
    scan step (gs ++ hs) w = scan step hs (scan step gs w) := by
  simp [scan, List.foldl_append]

private theorem scan_length (step : List α → Gate → α) (gs : List Gate) (w : List α) :
    (scan step gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih => rw [scan_cons, ih]; simp; omega

private theorem scan_prefix (step : List α → Gate → α) (gs : List Gate) (w : List α)
    (d : α) (i : ℕ) (hi : i < w.length) :
    (scan step gs w).getD i d = w.getD i d := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [scan_cons, ih _ (by simp; omega)]
    exact List.getD_append _ _ _ _ hi

private theorem read_gate (step : List α → Gate → α) (gs : List Gate) (w : List α)
    (d : α) (j : ℕ) (hj : j < gs.length) (a b : ℕ)
    (ha : a < w.length + j) (hb : b < w.length + j) (op : α → α → α)
    (hstep : ∀ p, step p gs[j] = op (p.getD a d) (p.getD b d)) :
    (scan step gs w).getD (w.length + j) d =
      op ((scan step gs w).getD a d) ((scan step gs w).getD b d) := by
  let pre := scan step (gs.take j) w
  have hp : pre.length = w.length + j := by
    simp [pre, scan_length, Nat.min_eq_left hj.le]
  have hs : scan step gs w = scan step (gs[j] :: gs.drop (j+1)) pre := by
    have hsplit := List.take_append_drop j gs
    conv_lhs => rw [← hsplit, scan_append, List.drop_eq_getElem_cons hj]
  have hpre (i : ℕ) (hi : i < w.length + j) : (scan step gs w).getD i d = pre.getD i d := by
    rw [hs]
    exact scan_prefix _ _ _ _ _ (by omega)
  rw [hpre a ha, hpre b hb, hs, scan_cons, scan_prefix _ _ _ _ _ (by simp [hp]),
    List.getD_append_right _ _ _ _ (by omega)]
  simpa [hp] using hstep pre

private def inputDegrees (p : Fin 14) : List ℕ :=
  (List.range 14).map fun i => if i ∈ ({p.val} : Finset ℕ) then 1 else 0

private theorem inputDegree (C : Circuit) (p : Fin 14) (i : ℕ) (hi : i < 14) :
    (C.lineDegrees 14 {p.val}).getD i 0 = if i = p.val then 1 else 0 := by
  change (scan (fun w g => g.lineDegree w) C.gates (inputDegrees p)).getD i 0 = _
  rw [scan_prefix _ _ _ _ _ (by simpa [inputDegrees] using hi),
    List.getD_eq_getElem _ _ (by simpa [inputDegrees] using hi)]
  simp [inputDegrees]

private theorem degreeAt (C : Circuit) (p : Fin 14) (j : ℕ) (hj : j < C.gates.length)
    (a b : ℕ) (ha : a < 14 + j) (hb : b < 14 + j) (op : ℕ → ℕ → ℕ)
    (h : ∀ w, C.gates[j].lineDegree w = op (w.getD a 0) (w.getD b 0)) :
    (C.lineDegrees 14 {p.val}).getD (14+j) 0 =
      op ((C.lineDegrees 14 {p.val}).getD a 0) ((C.lineDegrees 14 {p.val}).getD b 0) := by
  change (scan (fun w g => g.lineDegree w) C.gates (inputDegrees p)).getD (14+j) 0 =
    op ((scan (fun w g => g.lineDegree w) C.gates (inputDegrees p)).getD a 0)
      ((scan (fun w g => g.lineDegree w) C.gates (inputDegrees p)).getD b 0)
  have hlen : (inputDegrees p).length = 14 := by simp [inputDegrees]
  simpa only [hlen] using
    read_gate (fun w g => g.lineDegree w) C.gates (inputDegrees p) 0 j hj a b
      (by simpa [hlen] using ha) (by simpa [hlen] using hb) op h

theorem crossing : ∀ (C : Circuit) (i : Fin 14) (T : ℕ → Prop), (∀ (j : ℕ) (g : Gate), C.gates[j]?=some g →
      (g.op=.and ∨ g.op=.or) ∧ ∃ a b : ℕ, g.inputs=[a,b] ∧ a≠b ∧ a<14+j ∧ b<14+j) →
    T C.output → (∀ j (g : Gate), C.gates[j]?=some g → T (14+j) → ∀ a∈g.inputs, T a) → 2≤C.lineDeg 14 {i.val} →
    ∃ j (g : Gate), C.gates[j]?=some g ∧ T (14+j) ∧ g.op=.and ∧
      (∀ a∈g.inputs, (C.lineDegrees 14 {i.val}).getD a 0=1) ∧
      ∀ a<14+j, T a → (C.lineDegrees 14 {i.val}).getD a 0≤1 := by
  classical
  intro C i T shape out closed high
  let d (w : ℕ) := (C.lineDegrees 14 {i.val}).getD w 0
  have someHigh : ∃ w, T w ∧ 2≤d w := ⟨C.output,out,high⟩
  let w := Nat.find someHigh
  have atW : T w ∧ 2≤d w := Nat.find_spec someHigh
  have below : ∀ a<w, T a → d a≤1 := by
    intro a ha inT
    have no := Nat.find_min someHigh ha
    by_contra! large
    exact no ⟨inT,by omega⟩
  have raw : 14≤w := by
    by_contra! low
    have de := inputDegree C i w low
    have h := atW.2
    change 2≤(C.lineDegrees 14 {i.val}).getD w 0 at h
    rw [de] at h
    split at h <;> omega
  have hlen : (C.lineDegrees 14 {i.val}).length=14+C.gates.length := by
    change (scan (fun ds g => g.lineDegree ds) C.gates (inputDegrees i)).length=_
    simp [scan_length,inputDegrees]
  have inBounds : w<14+C.gates.length := by
    by_contra! outside
    have zero : d w=0 := List.getD_eq_default _ _ (by omega)
    have h := atW.2
    omega
  let j := w-14
  have hj : j<C.gates.length := by dsimp [j]; omega
  have pos : 14+j=w := by dsimp [j]; omega
  have live : T (14+j) := pos.symm ▸ atW.1
  have get := List.getElem?_eq_getElem (l := C.gates) hj
  obtain ⟨op,a,b,inp,_,ha,hb⟩ := shape j C.gates[j] get
  have ain : a∈C.gates[j].inputs := by simp [inp]
  have bin : b∈C.gates[j].inputs := by simp [inp]
  have al := below a (by omega) (closed j _ get live a ain)
  have bl := below b (by omega) (closed j _ get live b bin)
  have up : 2≤d (14+j) := pos.symm ▸ atW.2
  rcases op with andOp|orOp
  · have de : d (14+j) = d a+d b := degreeAt C i j hj a b ha hb (·+·)
        (by intro ds; simp [Gate.lineDegree,andOp,inp])
    refine ⟨j,C.gates[j],get,live,andOp,?_,?_⟩
    · intro z hz
      simp only [inp,List.mem_cons,List.not_mem_nil,or_false] at hz
      rcases hz with rfl|rfl <;> change d _=1 <;> omega
    · intro z hz ht
      exact below z (by omega) ht
  · have de : d (14+j) = max (d a) (d b) := degreeAt C i j hj a b ha hb max
        (by intro ds; simp [Gate.lineDegree,orOp,inp])
    have low := max_le al bl
    omega

end Cross2223

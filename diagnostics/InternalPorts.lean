import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_7290

namespace PlaneOrdered
open PEqualNP.CircuitLowerBounds

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem eval_eq (gs : List Gate) (o : ℕ) (x : List Bool) :
    Circuit.eval ⟨gs, o⟩ x = (wf gs x).getD o false := rfl

theorem wf_snoc (gs : List Gate) (g : Gate) (w : List Bool) :
    wf (gs ++ [g]) w = wf gs w ++ [g.op.eval (g.inputs.map fun i => (wf gs w).getD i false)] := by
  simp [wf, List.foldl_append]

theorem wf_len (gs : List Gate) : ∀ w : List Bool, (wf gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [wf]
  | cons g gs ih =>
    intro w
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]; simp; omega

theorem wf_keep (gs : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (wf gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) i (by simp; omega)
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]


end PlaneOrdered

namespace Ports
open PEqualNP.CircuitLowerBounds

abbrev I := Fin 13
def deltas : Finset I := {0,1,3,9}
def board (p q l m : I) := (List.ofFn fun i : I => decide (i=p ∨ i=q)) ++
  List.ofFn fun i : I => decide (i=l ∨ i=m)
def inc (p q l m : I) := decide (p-l∈deltas ∨ p-m∈deltas ∨ q-l∈deltas ∨ q-m∈deltas)
def val (C : Circuit) (r : ℕ) (p q l m : I) :=
  (C.wires (board p q l m)).getD r false
def tests (C : Circuit) (a b : ℕ) := ∀ p q l m : I,
  (val C a p q l m || val C b p q l m) = inc p q l m
theorem mask_of_pin : ∀ v : Fin 26, ∃ p l : I, inc p p l l = false ∧
    (board p p l l).getD v.val false = true := by decide +kernel
theorem length_wire (C : Circuit) (p q l m : I) :
    (C.wires (board p q l m)).length = 26+C.size := by
  change (PlaneOrdered.wf C.gates _).length = _
  rw [PlaneOrdered.wf_len]; simp [board,Circuit.size]
theorem interior (C : Circuit) (a b : ℕ) (ht : tests C a b)
    (ha : ∃ p l : I,val C a p p l l=true ∧ val C b p p l l=false)
    (hb : ∃ p l : I,val C b p p l l=true ∧ val C a p p l l=false) :
    (26≤a ∧ a<26+C.size) ∧ (26≤b ∧ b<26+C.size) ∧ a≠b := by
  have notraw (k : ℕ) (h : k=a ∨ k=b) : 26≤k := by
    by_contra! hv
    obtain ⟨p,l,hneg,hbit⟩ := mask_of_pin ⟨k,hv⟩
    have yes : val C k p p l l = true := by
      change (PlaneOrdered.wf C.gates _).getD k false=true
      rw [PlaneOrdered.wf_keep C.gates _ k (by simpa [board] using hv)]
      exact hbit
    have no := ht p p l l
    rw [hneg] at no
    rcases h with rfl|rfl <;> simp [yes] at no
  have notbad (k : ℕ) (p l : I) (h : val C k p p l l=true) : k<26+C.size := by
    by_contra! hbound
    unfold val at h
    rw [List.getD_eq_default _ _ (by rw [length_wire]; exact hbound)] at h
    contradiction
  obtain ⟨p,l,on,off⟩ := ha
  obtain ⟨q,m,on',_⟩ := hb
  exact ⟨⟨notraw a (Or.inl rfl),notbad a p l on⟩,
    ⟨notraw b (Or.inr rfl),notbad b q m on'⟩,fun e => by rw [e,off] at on; contradiction⟩

end Ports
end PEqualNP.Outside.L_meta_7290

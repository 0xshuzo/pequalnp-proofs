import PEqualNP.Outside.L_meta_5150

namespace PEqualNP.Outside.L_meta_2374

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def target (x : Fin 10 → Bool) := (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)

abbrev X := Fin 10 → Bool

def vertex (v : Fin 10) : X := fun i => decide (i=v)
def edgeRow (u v : Fin 10) : X := fun i => decide (i=u ∨ i=v)
def adj (u v : Fin 10) := target (edgeRow u v)=true
def supported (S : Finset (Fin 10)) (f : X → Bool) :=
  ∀ x y, (∀ i∈S, x i=y i) → f x=f y


def topExcept (S : Finset (Fin 10)) (v : Fin 10) : X := fun i => decide (i∈S ∧ i≠v)

theorem hasPivot : ∀ S : Finset (Fin 10), S.card≤3 → ∃ v, target (topExcept S v)=false := by
  decide +kernel

theorem edgeMono (x y : X) (h : ∀ i, x i=true → y i=true) (yes : target x=true) : target y=true := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  have h4 := h 4
  have h5 := h 5
  have h6 := h 6
  have h7 := h 7
  have h8 := h 8
  have h9 := h 9
  simp only [target, Bool.or_eq_true, Bool.and_eq_true] at yes ⊢
  tauto

theorem zeroFaceOfPencil {A B : X → Bool} (S : Finset (Fin 10)) (v : Fin 10)
    (dep : supported S A) (clean : target (topExcept S v)=false)
    (correct : ∀ x, (A x || B x)=target x) (x : X) (hx : x v=false) : B x=target x := by
  let y : X := fun i => if i∈S then x i else false
  have same : A x=A y := dep x y (by intro i hi; simp [y,hi])
  have sound : A y=false := by
    cases flag : A y with
    | false => rfl
    | true =>
      have a : target y=true := by simpa [flag] using (correct y).symm
      have bad := edgeMono y (topExcept S v) (by
        intro i hi
        by_cases ins : i∈S
        · have ne : i≠v := by rintro rfl; simp [y,ins,hx] at hi
          simp [topExcept,ins,ne]
        · simp [y,ins] at hi) a
      rw [clean] at bad
      contradiction
  simpa [same,sound] using correct x

theorem otherArmPrice {A : X → Bool} (S : Finset (Fin 10)) (dep : supported S A)
    (v : Fin 10) (clean : target (topExcept S v)=false)
    (C : Circuit) (fan : FanInTwo C) (correct : ∀ x,(A x || C.eval (List.ofFn x))=target x) :
    16≤C.size := by
  by_contra! h
  obtain ⟨x,hv,bad⟩ := PEqualNP.Outside.L_meta_5150 v C false fan (by simp; omega)
  apply bad
  exact zeroFaceOfPencil S v dep clean correct x hv

private def step (w : List Bool) (g : Gate) :=
  w ++ [g.op.eval (g.inputs.map (fun i => w.getD i false))]

private theorem foldlen (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length=w.length+gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, step,List.length_append,List.length_cons,List.length_nil]
    omega

private theorem foldget (gs : List Gate) (w : List Bool) (b : Nat) (hb : b<w.length) :
    (gs.foldl step w).getD b false = w.getD b false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih (step w g) (by simp [step]; omega)]
    simp only [step, List.getD_eq_getElem?_getD,List.getElem?_append_left hb]

theorem smallTap (C : Circuit) (b : Nat) (early : b<25) (x : X) :
    (C.wires (List.ofFn x)).getD b false =
      (⟨C.gates.take 15,b⟩ : Circuit).eval (List.ofFn x) := by
  change (C.gates.foldl step _).getD b false=((C.gates.take 15).foldl step _).getD b false
  by_cases short : C.gates.length≤15
  · rw [List.take_of_length_le short]
  · calc
      _ = (((C.gates.take 15 ++ C.gates.drop 15).foldl step (List.ofFn x))).getD b false := by
        rw [List.take_append_drop]
      _ = _ := by
        rw [List.foldl_append,foldget]
        rw [foldlen,List.length_ofFn,List.length_take]
        change b < 10+min 15 C.gates.length
        omega

theorem latePartner (C : Circuit) (b : Nat) (fan : FanInTwo C) (A : X → Bool)
    (S : Finset (Fin 10)) (dep : supported S A) (small : S.card≤3)
    (correct : ∀ x,(A x || (C.wires (List.ofFn x)).getD b false)=target x) : 25≤b := by
  by_contra! early
  obtain ⟨v,clean⟩ := hasPivot S small
  let D : Circuit := ⟨C.gates.take 15,b⟩
  have legal : FanInTwo D := by
    intro g hg
    exact fan g (List.mem_of_mem_take hg)
  have ok : ∀ x,(A x || D.eval (List.ofFn x))=target x := by
    intro x
    rw [← smallTap C b early x]
    exact correct x
  have lb := otherArmPrice S dep v clean D legal ok
  have ub : D.size≤15 := by
    change (C.gates.take 15).length≤15
    simp
  omega

end PEqualNP.Outside.L_meta_2374

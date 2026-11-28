import PEqualNP.Outside.L_meta_5148
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


def readers (C : Circuit) (v : Fin 10) (J : Finset Nat) : Prop :=
  ∀ j∈J, ∃ g : Gate, C.gates[j]?=some g ∧ (v : Nat)∈g.inputs ∧
    (g.op=GateOp.not → g.inputs.head?=some (v : Nat))

theorem pencilReaders {A : X → Bool} (C : Circuit) (fan : FanInTwo C) (cap : C.size≤18)
    (S : Finset (Fin 10)) (v : Fin 10) (dep : supported S A)
    (clean : target (topExcept S v)=false) (correct : ∀ x,(A x || C.eval (List.ofFn x))=target x)
    (J : Finset Nat) (reads : readers C v J) : J.card≤2 := by
  have on : ∀ w : Fin 10, target (fun i => decide (i≠w))=true := by decide +kernel
  have co := zeroFaceOfPencil S v dep clean correct
  rcases PEqualNP.Outside.L_meta_5148 10 C v J fan reads with ⟨c,hc⟩ | ⟨D,fanD,ds,agree⟩
  · cases c with
    | false =>
      have h := co (fun i => decide (i≠v)) (by simp)
      rw [hc _ (by simp),on v] at h
      exact (Bool.false_ne_true h).elim
    | true =>
      have h := co (fun _ => false) rfl
      rw [hc _ rfl] at h
      exact (Bool.false_ne_true h.symm).elim
  · by_contra! large
    have ub : D.size+(if false=true then 1 else 0)≤15 := by simp; omega
    obtain ⟨x,hv,bad⟩ := PEqualNP.Outside.L_meta_5150 v D false fanD ub
    apply bad
    simpa only [Bool.false_eq_true,ite_false,agree x hv] using co x hv

theorem smallReaders {A : X → Bool} (C : Circuit) (fan : FanInTwo C) (cap : C.size≤18)
    (S : Finset (Fin 10)) (dep : supported S A) (small : S.card≤3)
    (correct : ∀ x,(A x || C.eval (List.ofFn x))=target x) :
    ∃ v : Fin 10, (∀ x : X, x v=false → C.eval (List.ofFn x)=target x) ∧
      ∀ J, readers C v J → J.card≤2 := by
  obtain ⟨v,clean⟩ := hasPivot S small
  exact ⟨v,zeroFaceOfPencil S v dep clean correct,
    pencilReaders C fan cap S v dep clean correct⟩

end PEqualNP.Outside.L_meta_2374

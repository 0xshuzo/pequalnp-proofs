import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.ReadK

theorem PEqualNP.Outside.R_meta_4801_215
    (badFlag : let adj (p l : Fin 13) := p=l ∨ p=l+1 ∨ p=l+3 ∨ p=l+9
      let computes (C : Circuit) := ∀ z : Fin 26 → Bool, C.eval (List.ofFn z) = true ↔
        ∃ p l : Fin 13, adj p l ∧ z (Fin.castAdd 13 p) = true ∧ z (Fin.natAdd 13 l) = true
      ∀ C, IsAO2 26 C → computes C → C.size < 64 →
        ∃ p l : Fin 13, adj p l ∧ readsAtMost C 26 [p.val,13+l.val] 1 = false)
    (flags : let adj (p l : Fin 13) := p=l ∨ p=l+1 ∨ p=l+3 ∨ p=l+9
    ∀ p l, adj p l → ∃ (f g : Equiv.Perm (Fin 13)),
      f 0 = p ∧ g 0 = l ∧ ∀ a b, adj (f a) (g b) ↔ adj a b)
    (rename : ∀ (n : ℕ) (C : Circuit) (e : Equiv.Perm (Fin n)),
      IsAO2 n C → ∃ D : Circuit, IsAO2 n D ∧ D.size = C.size ∧
        (∀ z : Fin n → Bool, D.eval (List.ofFn z) = C.eval (List.ofFn (fun i => z (e i)))) ∧
        ∀ a b : Fin n, readsAtMost D n [(e a).val,(e b).val] 1 = readsAtMost C n [a.val,b.val] 1)
    (pinned : let adj (p l : Fin 13) := p=l ∨ p=l+1 ∨ p=l+3 ∨ p=l+9
      let computes (C : Circuit) := ∀ z : Fin 26 → Bool, C.eval (List.ofFn z) = true ↔
        ∃ p l : Fin 13, adj p l ∧ z (Fin.castAdd 13 p) = true ∧ z (Fin.natAdd 13 l) = true
      ∀ C, IsAO2 26 C → computes C → readsAtMost C 26 [0,13] 1 = false → 64 ≤ C.size) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 → x1.size < (64 : ℕ) → (∀ (x4 : Fin (26 : ℕ) → Bool), x1.eval (List.ofFn x4) = Bool.true ↔ ∃ (x5 : Fin (13 : ℕ)) (x6 : Fin (13 : ℕ)), (x5 = x6 ∨ x5 = x6 + (1 : Fin (13 : ℕ)) ∨ x5 = x6 + (3 : Fin (13 : ℕ)) ∨ x5 = x6 + (9 : Fin (13 : ℕ))) ∧ x4 (Fin.castAdd (13 : ℕ) x5) = Bool.true ∧ x4 (Fin.natAdd (13 : ℕ) x6) = Bool.true) → ∃ (x5 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (26 : ℕ) x5 ∧ x5.size ≤ x1.size ∧ (∀ (x6 : Fin (26 : ℕ) → Bool), x5.eval (List.ofFn x6) = x1.eval (List.ofFn x6)) ∧ ¬∃ (x6 : ℕ) (x7 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x5 x6).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x5 x7).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.EdgeOwnership.InCone (26 : ℕ) x5 x6 x7 := by
  intro C ao small computes
  obtain ⟨p,l,incident,miss⟩ := badFlag C ao computes small
  obtain ⟨f,g,fp,gl,preserve⟩ := flags p l incident
  let act (h k : Equiv.Perm (Fin 13)) : Fin 26 → Fin 26 :=
    fun w => Fin.addCases (motive := fun _ => Fin 26) (fun u : Fin 13 => Fin.castAdd 13 (h u)) (fun v : Fin 13 => Fin.natAdd 13 (k v)) w
  have inv (h k : Equiv.Perm (Fin 13)) (w : Fin 26) :
      act h.symm k.symm (act h k w) = w := by
    refine Fin.addCases (motive := fun x => act h.symm k.symm (act h k x) = x) (fun u : Fin 13 => ?_) (fun v : Fin 13 => ?_) w <;>
      simp only [act, Fin.addCases_left, Fin.addCases_right, Equiv.symm_apply_apply]
  let e : Equiv.Perm (Fin 26) :=
    ⟨act f.symm g.symm, act f g, (fun w => by simpa only [Equiv.symm_symm] using inv f.symm g.symm w), (fun w => inv f g w)⟩
  have ep (u : Fin 13) : e (Fin.castAdd 13 u) = Fin.castAdd 13 (f.symm u) := by
    change act f.symm g.symm (Fin.castAdd 13 u) = _
    simp only [act,Fin.addCases_left]
  have el (v : Fin 13) : e (Fin.natAdd 13 v) = Fin.natAdd 13 (g.symm v) := by
    change act f.symm g.symm (Fin.natAdd 13 v) = _
    simp only [act,Fin.addCases_right]
  obtain ⟨D,dao,size,eval,read⟩ := rename 26 C e ao
  have target (z : Fin 26 → Bool) : D.eval (List.ofFn z) = true ↔
      ∃ u v : Fin 13, (u=v ∨ u=v+1 ∨ u=v+3 ∨ u=v+9) ∧
        z (Fin.castAdd 13 u) = true ∧ z (Fin.natAdd 13 v) = true := by
    rw [eval, computes]
    constructor
    · rintro ⟨u,v,h,hu,hv⟩
      refine ⟨f.symm u,g.symm v,(preserve _ _).mp (by simpa using h),?_,?_⟩
      · simpa only [ep] using hu
      · simpa only [el] using hv
    · rintro ⟨u,v,h,hu,hv⟩
      refine ⟨f u,g v,(preserve u v).mpr h,?_,?_⟩
      · simpa only [ep,Equiv.symm_apply_apply] using hu
      · simpa only [el,Equiv.symm_apply_apply] using hv
  have left : f.symm p = 0 := by rw [← fp, Equiv.symm_apply_apply]
  have right : g.symm l = 0 := by rw [← gl, Equiv.symm_apply_apply]
  have hit := read (Fin.castAdd 13 p) (Fin.natAdd 13 l)
  have failed : readsAtMost D 26 [0,13] 1 = false := by
    have v := hit.trans miss
    rw [ep,el,left,right] at v
    exact v
  exact False.elim ((Nat.not_le_of_lt small) (size ▸ pinned D dao target failed))

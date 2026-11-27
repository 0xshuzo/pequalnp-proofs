import Mathlib
import PEqualNP.Defs
namespace PEqualNP.Outside.L_lib_592_aux
def combine {G : Type*} [Group G] : List G → G
  | [] => 1
  | a::rest => combine rest * a

section Linear
variable {K G : Type} [Field K] [Group G] {m : ℕ}

def Fact (f : G → K) (m : ℕ) := ∃ A B : G → Fin m → K,
  ∀ p r, f (r*p) = ∑ i, A p i * B r i

theorem makeScan (f : G → K) (h : Fact f m) :
    ∃ (s : Fin m → K) (T : G → (Fin m → K) →ₗ[K] (Fin m → K))
      (o : (Fin m → K) →ₗ[K] K), ∀ L : List G, o (L.foldl (fun v g => T g v) s) = f (combine L) := by
  classical
  obtain ⟨A,B,fac⟩ := h
  let E : (Fin m → K) →ₗ[K] (G → K) :=
    { toFun := fun v r => ∑ i, v i * B r i
      map_add' := by intro x y; funext r; simp [add_mul,Finset.sum_add_distrib]
      map_smul' := by intro a x; funext r; simp [Finset.mul_sum,mul_assoc] }
  have value (p r : G) : E (A p) r = f (r*p) := (fac p r).symm
  obtain ⟨g,hg⟩ := E.rangeRestrict.exists_rightInverse_of_surjective E.range_rangeRestrict
  obtain ⟨π,hπ⟩ := E.range.subtype.exists_leftInverse_of_injective (Submodule.ker_subtype _)
  let J := g.comp π
  have back (v : Fin m → K) : E (J (E v)) = E v := by
    let z := E.rangeRestrict v
    have p : π (E v) = z := LinearMap.congr_fun hπ z
    have q : E.rangeRestrict (g z) = z := LinearMap.congr_fun hg z
    change E (g (π (E v))) = E v
    rw [p]; exact congrArg Subtype.val q
  let shift (u : G) : (G→K) →ₗ[K] (G→K) :=
    { toFun := fun x r => x (r*u)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have sh (u p : G) : shift u (E (A p)) = E (A (u*p)) := by
    funext r
    change E (A p) (r*u) = _
    rw [value,value,mul_assoc]
  let T (u : G) := J.comp ((shift u).comp E)
  let o := (LinearMap.proj (R:=K) (φ:=fun _ : G => K) (1:G)).comp E
  have go (L : List G) (p : G) (v : Fin m → K) (hv : E v=E (A p)) :
      E (L.foldl (fun x u => T u x) v) = E (A (combine L*p)) := by
    induction L generalizing v p with
    | nil => simpa [combine] using hv
    | cons u L ih =>
      change E (L.foldl _ (T u v)) = _
      have eq : E (T u v)=E (A (u*p)) := by
        change E (J (shift u (E v)))=_
        rw [hv,sh,back]
      simpa [combine,mul_assoc] using ih (u*p) (T u v) eq
  refine ⟨A 1,T,o,?_⟩
  intro L
  change E (L.foldl _ (A 1)) 1 = _
  have eq := congrFun (go L 1 (A 1) rfl) 1
  simpa [value] using eq

def linWord (l : List ((Fin m → K) →ₗ[K] (Fin m → K))) : (Fin m → K) →ₗ[K] (Fin m → K) :=
  l.foldr (fun a b => b.comp a) .id

theorem linWord_eval (l : List ((Fin m → K) →ₗ[K] (Fin m → K))) (v : Fin m→K) :
    linWord l v = l.foldl (fun x t => t x) v := by
  induction l generalizing v with
  | nil => rfl
  | cons t l ih => exact ih (t v)

theorem dotLinear (l : (Fin m → K) →ₗ[K] K) (v : Fin m → K) :
    l v = ∑ i, v i * l (Pi.single i 1) := by
  have hv : ∑ i : Fin m, v i • Pi.single i (1:K) = v := by
    funext j
    simp [Finset.sum_apply,Pi.single_apply,smul_eq_mul,mul_ite]
  calc
    l v = l (∑ i, v i • Pi.single i (1:K)) := congrArg l hv.symm
    _ = _ := by simp [smul_eq_mul]

end Linear

end PEqualNP.Outside.L_lib_592_aux

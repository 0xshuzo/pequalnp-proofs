import PEqualNP.Defs
import PEqualNP.Outside.L_lib_377
namespace PEqualNP.Outside.L_lib_592_aux
abbrev State (b : ℕ) := Fin (b+1) → Bool
abbrev Control (b : ℕ) := (Fin b → Bool) → Bool

def row {b : ℕ} (c : Control b) : Equiv.Perm (State b) where
  toFun s := Fin.snoc (α := fun _ : Fin (b+1) => Bool) (fun j => s j.succ)
    (xor (s 0) (c (fun j => s j.succ)))
  invFun t := Fin.cons (xor (t (Fin.last b)) (c (fun j => t j.castSucc))) (fun j => t j.castSucc)
  left_inv s := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · simp
  right_inv t := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp
    · simp

def combine {G : Type*} [Group G] : List G → G
  | [] => 1
  | a::rest => combine rest * a

theorem combine_append {G : Type*} [Group G] (l r : List G) :
    combine (l++r)=combine r*combine l := by
  induction l with
  | nil => simp [combine]
  | cons a l ih => simp [combine,ih,mul_assoc]

theorem combine_eval {X I : Type*} (L : List I) (f : I → Equiv.Perm X) (x : X) :
    (combine (L.map f)) x = L.foldl (fun y i => f i y) x := by
  induction L generalizing x with
  | nil => rfl
  | cons i L ih => exact ih (f i x)

def word {b n : ℕ} (c : Fin n → Control b) : Equiv.Perm (State b) := combine (List.ofFn (fun i => row (c i)))

def fixCount {X : Type*} [Fintype X] [DecidableEq X] (p : Equiv.Perm X) :=
  (Finset.univ.filter (fun x => p x=x)).card

def graphMat {X : Type*} [Fintype X] [DecidableEq X] (p : Equiv.Perm X) : Matrix X X ℕ :=
  fun x y => if p x=y then 1 else 0

theorem graphMat_prod {X : Type*} [Fintype X] [DecidableEq X] (L : List (Equiv.Perm X)) :
    (L.map graphMat).prod = graphMat (combine L) := by
  induction L with
  | nil =>
    ext i j
    simp [graphMat,combine,Matrix.one_apply]
  | cons p L ih =>
    rw [List.map_cons,List.prod_cons,ih]
    ext i j
    simp [Matrix.mul_apply,graphMat,combine,ite_mul,Finset.sum_ite_eq]

theorem trace_graph {X : Type*} [Fintype X] [DecidableEq X] (p : Equiv.Perm X) :
    Matrix.trace (graphMat p) = fixCount p := by
  simp [graphMat,Matrix.trace,Matrix.diag,fixCount,Finset.card_filter]

open PEqualNP.Outside.L_lib_377 in
theorem nx_eq {b : ℕ} (s : State b) (v : Bool) :
    nx s v = Fin.snoc (α := fun _ : Fin (b+1) => Bool) (fun j => s j.succ) v := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [nx]
  · have h : j.val+1<b+1 := by omega
    simp [nx,h]

def countWords (b a : ℕ) (C : Fin (a+1) → Control b) : ℕ :=
  ((Finset.univ : Finset (Fin (a+1) → Bool)).filter (fun x =>
    ∀ i : Fin (a+1), x (Fin.ofNat (a+1) (i.val+(b+1))) =
      xor (x i) (C i (fun j => x (Fin.ofNat (a+1) (i.val+1+j.val)))))).card

open PEqualNP.Outside.L_lib_377 in
theorem count_fix (b a : ℕ) (C : Fin (a+1) → Control b) :
    countWords b a C = fixCount (word C) := by
  let test := fun (i : Fin (a+1)) (s : State b) (t : Bool) =>
    decide (t = xor (s 0) (C i (fun j => s j.succ)))
  have eq := PEqualNP.Outside.L_lib_377 a (b+1) test
  change Matrix.trace (List.ofFn (Mat test)).prod = _ at eq
  have cell (i : Fin (a+1)) : Mat test i = graphMat (row (C i)) := by
    ext s t
    let v := xor (s 0) (C i (fun j => s j.succ))
    have nxv : nx s v = row (C i) s := nx_eq s v
    change (Finset.univ.filter (fun x : Bool => decide (x=v)=true ∧ nx s x=t)).card = _
    by_cases h : row (C i) s = t
    · have he : Finset.univ.filter (fun x : Bool => decide (x=v)=true ∧ nx s x=t) = {v} := by
        ext x
        simp only [Finset.mem_filter,Finset.mem_univ,true_and,decide_eq_true_eq,Finset.mem_singleton]
        exact ⟨And.left,fun hv => ⟨hv,hv ▸ nxv.trans h⟩⟩
      rw [he]; simp [graphMat,h]
    · have he : Finset.univ.filter (fun x : Bool => decide (x=v)=true ∧ nx s x=t) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro x hx
        obtain ⟨_,hx,he⟩ := Finset.mem_filter.mp hx
        have hv : x=v := of_decide_eq_true hx
        subst x
        exact h (nxv.symm.trans he)
      rw [he]; simp [graphMat,h]
  have hm : List.ofFn (Mat test) = (List.ofFn fun i => row (C i)).map graphMat := by
    rw [List.map_ofFn]
    exact congrArg List.ofFn (funext cell)
  rw [hm,graphMat_prod,trace_graph] at eq
  rw [←eq]
  unfold countWords
  apply congrArg Finset.card
  ext x
  simp only [Finset.mem_filter,Finset.mem_univ,true_and,test,decide_eq_true_eq]
  apply forall_congr'
  intro i
  simp [Nat.add_comm,Nat.add_left_comm,Nat.add_assoc]


end PEqualNP.Outside.L_lib_592_aux

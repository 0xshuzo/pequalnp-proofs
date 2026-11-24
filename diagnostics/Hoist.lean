import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
namespace Narrow4785

abbrev Col := Finset (Fin 58)
abbrev Pool := Finset Col

def Op (I : Pool) (z : Col) : Prop :=
  ∃ a ∈ I, ∃ b ∈ I, z = a ∪ b ∨ z = a ∩ b

lemma opGrow {I J : Pool} {z : Col} (sub : I ⊆ J) (h : Op I z) : Op J z := by
  obtain ⟨a,ha,b,hb,h⟩ := h
  exact ⟨a,sub ha,b,sub hb,h⟩

def Scan (f : Pool → Col → Prop) (I : Pool) : List Col → Prop
  | [] => True
  | x::xs => f I x ∧ Scan f (insert x I) xs

lemma scanSplits (f : Pool → Col → Prop) (S : List Col) (I : Pool) :
    Scan f I S ↔ ∀ (a b : List Col) (z : Col), S = a ++ z :: b → f (I ∪ a.toFinset) z := by
  induction S generalizing I with
  | nil =>
    constructor
    · intro _ a b z eq
      cases a <;> simp at eq
    · intro _
      trivial
  | cons x xs ih =>
    constructor
    · rintro ⟨first,tail⟩ a b z eq
      cases a with
      | nil =>
        simp only [List.nil_append,List.cons.injEq] at eq
        simpa [← eq.1] using first
      | cons h a =>
        simp only [List.cons_append,List.cons.injEq] at eq
        obtain ⟨rfl,he⟩ := eq
        have given := (ih (insert x I)).1 tail a b z he
        simpa only [List.toFinset_cons,Finset.union_insert,Finset.insert_union] using given
    · intro splits
      constructor
      · simpa using splits [] xs x rfl
      · apply (ih (insert x I)).2
        intro a b z eq
        have given := splits (x::a) b z (by simp [eq])
        simpa only [List.toFinset_cons,Finset.union_insert,Finset.insert_union] using given

def Low (P z : Col) := z ⊆ P ∧ z.card ≤ 1
def Allowed (P : Col) (I : Pool) (z : Col) := Low P z ∨ (2 ≤ (z ∩ P).card ∧ Op I z)
def High (P : Col) (I : Pool) (z : Col) := 2 ≤ (z ∩ P).card ∧ Op I z
def atoms (A : Col) : Pool := A.image (fun q => {q})
theorem gather (P : Col) (S : List Col) (I : Pool) (zero : ∅ ∈ I) (prog : Scan (Allowed P) I S)
    (out : P ∈ I ∪ S.toFinset) :
    ∃ (A : Col) (T : List Col), A ⊆ P ∧ A.card + T.length ≤ S.length ∧
      Scan (High P) (I ∪ atoms A) T ∧ P ∈ I ∪ atoms A ∪ T.toFinset := by
  induction S generalizing I with
  | nil =>
    exact ⟨∅,[],by simp,by simp,True.intro,by simpa [atoms] using out⟩
  | cons z zs ih =>
    obtain ⟨head,tail⟩ := prog
    have pass : P ∈ insert z I ∪ zs.toFinset := by
      simpa only [List.toFinset_cons,Finset.insert_union,Finset.union_insert] using out
    obtain ⟨A,T,sub,cost,rest,output⟩ := ih (insert z I) (Finset.mem_insert_of_mem zero) tail pass
    rcases head with ⟨zp,small⟩ | ⟨big,op⟩
    · by_cases empty : z=∅
      · subst z
        rw [Finset.insert_eq_of_mem zero] at rest output
        exact ⟨A,T,sub,by simp; omega,rest,output⟩
      · have one : z.card = 1 := by
          have pos := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr empty)
          omega
        obtain ⟨q,rfl⟩ := Finset.card_eq_one.mp one
        have qP : q ∈ P := zp (by simp)
        have bank : I ∪ atoms (insert q A) = insert {q} I ∪ atoms A := by
          simp [atoms,Finset.image_insert,Finset.union_insert,Finset.insert_union]
        refine ⟨insert q A,T,Finset.insert_subset qP sub,?_,?_,?_⟩
        · have hsize := Finset.card_insert_le q A
          simp
          omega
        · rw [bank]
          exact rest
        · rw [bank]
          exact output
    · refine ⟨A,z::T,sub,by simpa [Nat.add_assoc] using cost,?_,?_⟩
      · refine ⟨⟨big,opGrow (Finset.subset_union_left) op⟩,?_⟩
        simpa only [Finset.insert_union] using rest
      · simpa only [List.toFinset_cons,Finset.union_insert,Finset.insert_union] using output

theorem hoistChild : let P : Finset (Fin 58) := Finset.univ.filter (fun i : Fin 58 => i.val < 21)
      let op := fun (M : Finset (Finset (Fin 58))) (z : Finset (Fin 58)) =>
        ∃ a ∈ M, ∃ b ∈ M, z = a ∪ b ∨ z = a ∩ b
      let low := fun z : Finset (Fin 58) => z ⊆ P ∧ z.card ≤ 1
      ∀ (I : Finset (Finset (Fin 58))) (S : List (Finset (Fin 58))), ∅ ∈ I →
        (∀ (u v : List (Finset (Fin 58))) (z : Finset (Fin 58)), S = u ++ z :: v →
          low z ∨ (2 ≤ (z ∩ P).card ∧ op (I ∪ u.toFinset) z)) → P ∈ I ∪ S.toFinset →
        ∃ (A : Finset (Fin 58)) (T : List (Finset (Fin 58))), A ⊆ P ∧
          A.card + T.length ≤ S.length ∧ (∀ (u v : List (Finset (Fin 58))) (z : Finset (Fin 58)), T = u ++ z :: v →
          2 ≤ (z ∩ P).card ∧ op (I ∪ A.image (fun q => {q}) ∪ u.toFinset) z) ∧ P ∈ I ∪ A.image (fun q => {q}) ∪ T.toFinset := by
  let P : Col := Finset.univ.filter (fun i : Fin 58 => i.val < 21)
  change ∀ (I : Pool) (S : List Col), ∅ ∈ I →
    (∀ (u v : List Col) (z : Col), S=u ++ z::v → Allowed P (I ∪ u.toFinset) z) →
    P ∈ I ∪ S.toFinset → ∃ (A : Col) (T : List Col), A ⊆ P ∧ A.card + T.length ≤ S.length ∧
    (∀ (u v : List Col) (z : Col), T=u ++ z::v → High P (I ∪ atoms A ∪ u.toFinset) z) ∧
    P ∈ I ∪ atoms A ∪ T.toFinset
  intro I S zero steps out
  obtain ⟨A,T,sub,cost,prog,hit⟩ := gather P S I zero ((scanSplits _ _ _).2 steps) out
  exact ⟨A,T,sub,cost,(scanSplits _ _ _).1 prog,hit⟩

end Narrow4785

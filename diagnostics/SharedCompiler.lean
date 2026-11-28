import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_121_shared
open PEqualNP.ProofComplexity
variable {V : Type} [DecidableEq V]
abbrev LC (V : Type) := LinClause V

inductive Recipe (B : Set (LC V)) : LC V → Nat → Type where
  | leaf {C} : C∈B → Recipe B C 0
  | join {C D R a b} : Recipe B C a → Recipe B D b → IsLinResolvent C D R →
      Recipe B R (a+b+1)
  | weaken {C D a} : Recipe B C a → (∀x,LinClauseSat x C → LinClauseSat x D) →
      Recipe B D (a+1)

theorem materialize {B F : Set (LC V)} {C : LC V} {n} (tree : Recipe B C n)
    {base : List (LC V)} (der : IsLinDerivation F base) (ready : ∀D∈B,D∈base) :
    ∃ ext : List (LC V), ext.length=n ∧ IsLinDerivation F (ext++base) ∧ C∈ext++base := by
  induction tree generalizing base with
  | leaf present => exact ⟨[],rfl,der,ready _ present⟩
  | @weaken C D a child imp ih =>
    obtain ⟨xs,size,ok,haveC⟩ := ih der ready
    exact ⟨D::xs,by simp [size],IsLinDerivation.weak ok haveC imp,List.mem_cons_self⟩
  | @join C D R a b lhs rhs rule left right =>
    obtain ⟨xs,sizeX,okX,haveC⟩ := left der ready
    have extended : ∀E∈B,E∈xs++base := fun E h => List.mem_append_right _ (ready E h)
    obtain ⟨ys,sizeY,okY,haveD⟩ := right okX extended
    have haveC' : C ∈ ys++(xs++base) := List.mem_append_right _ haveC
    have legal := IsLinDerivation.res okY haveC' haveD rule
    exact ⟨R::(ys++xs),by simp [sizeX,sizeY,Nat.add_comm],
      by simpa only [List.cons_append,List.append_assoc] using legal,List.mem_cons_self⟩

theorem shared {F B : Set (LC V)} {base : List (LC V)} (der : IsLinDerivation F base)
    (ready : ∀D∈B,D∈base) {H C : LC V} {a b}
    (build : Recipe B H a) (finish : Recipe (insert H B) C b) :
    ∃ π : List (LC V), IsLinDerivation F π ∧ C∈π ∧ π.length=base.length+a+b := by
  obtain ⟨xs,sx,ok,found⟩ := materialize build der ready
  have live : ∀D∈insert H B, D∈xs++base := by
    intro D hd
    rcases Set.mem_insert_iff.mp hd with rfl|before
    · exact found
    · exact List.mem_append_right _ (ready D before)
  obtain ⟨ys,sy,fin,last⟩ := materialize finish ok live
  refine ⟨ys++(xs++base),fin,last,?_⟩
  simp only [List.length_append,sx,sy]
  omega

theorem php55 {B : Set (LC (Fin 4 × Fin 3))} {base : List (LC (Fin 4 × Fin 3))}
    (der : IsLinDerivation (linOfClause '' PHP 4 3) base) (ready : ∀D∈B,D∈base)
    {H : LC (Fin 4 × Fin 3)} {a b} (build : Recipe B H a)
    (finish : Recipe (insert H B) ∅ b) (small : base.length+a+b≤55) :
    ∃ π : List (LC (Fin 4 × Fin 3)), IsLinRefutation (PHP 4 3) π ∧ π.length≤55 := by
  obtain ⟨π,d,h,count⟩ := shared der ready build finish
  exact ⟨π,⟨d,h⟩,by omega⟩
end PEqualNP.Outside.L_pcx_121_shared

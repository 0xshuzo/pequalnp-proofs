import PEqualNP.Defs
open PEqualNP.ProofComplexity
namespace PEqualNP.Outside.L_pcx_178.CherryFork
abbrev P := Fin 5
abbrev H := Fin 4
abbrev V := P × H
inductive Atom where
  | row (i : P)
  | coll (i j : P) (h : H)
  | into (i j : P) (h : H)
  deriving DecidableEq

def words : Atom → List (V × Bool)
  | .row i => (List.finRange 4).map fun h => ((i,h),true)
  | .coll i j h => [((i,h),false),((j,h),false)]
  | .into i j h => ((j,h),false)::((List.finRange 4).filter (· != h)).map (fun k => ((i,k),true))
def physical (c : Atom) : LinClause V := linOfClause (words c).toFinset
def belongs (a : V→Bool) (c : Atom) := (words c).any fun q => a q.1 == q.2
def price (c : Atom) : Option (Finset P × H) := match c with
  | .row _ => none
  | .coll i j h | .into i j h => some ({i,j},h)
def proper : Atom → Bool
  | .row _ => true
  | .coll i j _ | .into i j _ => i!=j

theorem sound {c : Atom} {a : V→Bool} (h : belongs a c=true) : LinClauseSat a (physical c) := by
  obtain ⟨q,hq,w⟩:=List.any_eq_true.mp h
  have eq : a q.1=q.2:=beq_iff_eq.mp w
  refine ⟨({q.1},q.2),Finset.mem_image.mpr ⟨q,List.mem_toFinset.mpr hq,rfl⟩,?_⟩
  cases b : q.2 <;> simp [LinEqSat,eq,b]

def witness (v : V) : Bool :=
  decide (v=(0,0) ∨ v=(0,1) ∨ v=(1,0) ∨ v=(2,1) ∨ v=(3,2) ∨ v=(4,3))

def form (c : Atom) : Prop := proper c=true → belongs witness c=true ∨
    (price c=price (.into 0 1 0) ∧ c≠.into 0 1 0) ∨
    (price c=price (.into 0 2 1) ∧ c≠.into 0 2 1)

instance (c : Atom) : Decidable (form c) := by unfold form; infer_instance

theorem cuts : ∀ c : Atom,form c := by
  have r : ∀ i : P, form (.row i) := by decide +kernel
  have k : ∀ (i j : P) (h : H), form (.coll i j h) := by decide +kernel
  have t : ∀ (i j : P) (h : H), form (.into i j h) := by decide +kernel
  intro c
  cases c with
  | row i => exact r i
  | coll i j h => exact k i j h
  | into i j h => exact t i j h

theorem badFork (S : Set Atom) (valid : ∀ c∈S,proper c=true)
    (one : ∀ c∈S, ∀ d∈S, price c≠none → price c=price d → c=d)
    (first : .into 0 1 0 ∈ S) (second : .into 0 2 1 ∈ S) :
    ∀ c∈S,LinClauseSat witness (physical c) := by
  intro c cin
  rcases cuts c (valid c cin) with yes | ⟨p,ne⟩ | ⟨p,ne⟩
  · exact sound yes
  · exact False.elim (ne (one c cin _ first (by rw [p]; decide) p))
  · exact False.elim (ne (one c cin _ second (by rw [p]; decide) p))

theorem axis {A B : Type} (S : A→B→Prop)
    (noCross : ∀ i h j k,S i h → S j k → i=j ∨ h=k)
    (i : A) (h : B) (ih : S i h) :
    (∀ j k,S j k → j=i) ∨ (∀ j k,S j k → k=h) := by
  classical
  by_cases hrow : ∀ j k,S j k → j=i
  · exact Or.inl hrow
  · push_neg at hrow
    obtain ⟨j,k,q,ji⟩:=hrow
    have kh := (noCross j k i h q ih).resolve_left ji
    subst k
    right
    intro u v uv
    by_contra vh
    have ui:=(noCross u v i h uv ih).resolve_right vh
    have uj:=(noCross u v j h uv q).resolve_right vh
    exact ji (uj.symm.trans ui)
end PEqualNP.Outside.L_pcx_178.CherryFork

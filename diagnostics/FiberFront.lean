import PEqualNP.Defs
namespace Research9755.FiberFront
abbrev X := Fin 8 → Bool
abbrev Ctrl := Bool × Bool
abbrev Input := X × Ctrl
abbrev W := Input → Bool
def u : W := fun x => x.2.1
def v : W := fun x => x.2.2
def ctxt (f : W) := ∀ z : X,∀ t : Ctrl, f (z,t)=f (z,(false,false))
def base (f : W) := f=u ∨ f=v ∨ ctxt f
def pins (a : Input) : Fin 10→Bool := ![a.2.1,a.2.2,a.1 0,a.1 1,a.1 2,a.1 3,a.1 4,a.1 5,a.1 6,a.1 7]
def graph (x : Fin 10 → Bool) := (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 1 && x 6) || (x 2 && x 3) || (x 2 && x 7) || (x 3 && x 4) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 5 && x 8) || (x 6 && x 8) || (x 6 && x 9) || (x 7 && x 9)
def wanted (a : Input) := graph (pins a)
def witness (i : Fin 5) (k : Fin 8) := (#[0,4,1,5,3] : Array Nat)[i.val]!.testBit k.val
theorem differs : ∀ i j : Fin 5,i≠j → ∃t : Ctrl,wanted (witness i,t)≠wanted (witness j,t) := by decide +kernel
def Agrees (S : Finset W) (a b : Input) := ∀ f∈S,f a=f b
def Determines (S T : Finset W) := ∀ a b,Agrees S a b → Agrees T a b

theorem supportFive (S : Finset W) (ok : ∀ f∈S, base f)
    (calc : ∀ a b, Agrees S a b → wanted a=wanted b) : 5≤S.card := by
  classical
  have uv : u≠v := by
    intro eq
    have no := congrFun eq (witness 0,(true,false))
    change true=false at no
    contradiction
  have needU : u∈S := by
    by_contra miss
    have agree : Agrees S (witness 1,(false,false)) (witness 1,(true,false)) := by
      intro f hf
      rcases ok f hf with rfl|rfl|c
      · contradiction
      · rfl
      · exact (c _ _).trans (c _ _).symm
    have no:=calc _ _ agree
    have diff : wanted (witness 1,(false,false))≠wanted (witness 1,(true,false)) := by decide
    exact diff no
  have needV : v∈S := by
    by_contra miss
    have agree : Agrees S (witness 2,(false,false)) (witness 2,(false,true)) := by
      intro f hf
      rcases ok f hf with rfl|rfl|c
      · rfl
      · contradiction
      · exact (c _ _).trans (c _ _).symm
    have no:=calc _ _ agree
    have diff : wanted (witness 2,(false,false))≠wanted (witness 2,(false,true)) := by decide
    exact diff no
  let R := (S.erase u).erase v
  have vr : v∈S.erase u := Finset.mem_erase.mpr ⟨uv.symm,needV⟩
  have card : R.card+2=S.card := by
    have a := Finset.card_erase_of_mem needU
    have b := Finset.card_erase_of_mem vr
    have p := Finset.card_pos.mpr ⟨u,needU⟩
    have q := Finset.card_pos.mpr ⟨v,vr⟩
    change ((S.erase u).erase v).card+2=S.card
    omega
  let code (i : Fin 5) (f : R) := f.val (witness i,(false,false))
  have inj : Function.Injective code := by
    intro i j e
    by_contra ij
    obtain ⟨t,conflict⟩:=differs i j ij
    apply conflict
    apply calc
    intro f hf
    by_cases fu : f=u
    · rw [fu]
    by_cases fv : f=v
    · rw [fv]
    have ins : f∈R := Finset.mem_erase.mpr ⟨fv,Finset.mem_erase.mpr ⟨fu,hf⟩⟩
    have h := congrFun e (⟨f,ins⟩ : R)
    have ct : ctxt f := ((ok f hf).resolve_left fu).resolve_left fv
    exact (ct _ _).trans (h.trans (ct _ _).symm)
  have h := Fintype.card_le_of_injective code inj
  simp at h
  by_contra! bad
  have rr : R.card≤2 := by omega
  have options : R.card=0 ∨ R.card=1 ∨ R.card=2 := by omega
  rcases options with hr|hr|hr <;> simp [hr] at h

end Research9755.FiberFront

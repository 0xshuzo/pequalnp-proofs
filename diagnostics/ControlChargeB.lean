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
    (determines : ∀ a b, Agrees S a b → wanted a=wanted b) : 5≤S.card := by
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
    have no:=determines _ _ agree
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
    have no:=determines _ _ agree
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
    apply determines
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
namespace Research9755.FiberFront
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def z : W := fun _ => false
def starting : List W := List.ofFn (fun i : Fin 10 => fun x => pins x i)
def result (w : List W) (g : Gate) : W :=
  fun x => g.op.eval (g.inputs.map (fun i => (w.getD i z) x))
def next (w : List W) (g : Gate) := w++[result w g]
def run (w : List W) (gs : List Gate) := gs.foldl next w
noncomputable def cost (w : List W) (gs : List Gate) : Nat := by
  classical
  exact match gs with
  | [] => 0
  | g::tail => (if ctxt (result w g) then 0 else 1) + cost (next w g) tail

def prior (w : List W) (f : W) := base f ∨ f∈w

theorem compress (T : Finset W) (w : List W) (gs : List Gate)
    (small : ∀ g∈gs, g.inputs.length≤2) (ok : ∀ f∈T, prior (run w gs) f) :
    ∃ S : Finset W, (∀ f∈S, prior w f) ∧ S.card≤T.card+cost w gs ∧ Determines S T := by
  classical
  induction gs generalizing w T with
  | nil => exact ⟨T,ok,by simp [cost],fun _ _ h => h⟩
  | cons g gs ih =>
    obtain ⟨U,avail,count,determ⟩:=ih T (next w g) (fun a h => small a (by simp [h])) ok
    let f := result w g
    have unpack (c : W) (m : c∈U) : prior w c ∨ c=f := by
      rcases avail c m with basec|seen
      · exact Or.inl (Or.inl basec)
      · rcases List.mem_append.mp seen with sw|sg
        · exact Or.inl (Or.inr sw)
        · exact Or.inr (by simpa [f] using sg)
    by_cases cc : ctxt f
    · refine ⟨U,?_,?_,determ⟩
      · intro c m
        rcases unpack c m with h|rfl
        · exact h
        · exact Or.inl (Or.inr (Or.inr cc))
      · simpa [cost,f,cc] using count
    by_cases inside : f∈U
    · let ps := (g.inputs.map fun i => w.getD i z).toFinset
      let S := U.erase f ∪ ps
      have b : ps.card≤2 := (List.toFinset_card_le _).trans (by simpa using small g (by simp))
      have a : ∀ s∈S, prior w s := by
        intro s h
        rcases Finset.mem_union.mp h with er|pa
        · obtain ⟨ne,mem⟩:=Finset.mem_erase.mp er
          exact (unpack s mem).resolve_right ne
        · obtain ⟨i,_,rfl⟩:=List.mem_map.mp (List.mem_toFinset.mp pa)
          by_cases lt : i<w.length
          · exact Or.inr (by simpa [List.getD_eq_getElem?_getD,lt] using List.getElem_mem lt)
          · left; right; right
            simp [List.getD_eq_getElem?_getD,List.getElem?_eq_none (Nat.le_of_not_gt lt),z,ctxt]
      refine ⟨S,a,?_,?_⟩
      · have sz:=Finset.card_union_le (U.erase f) ps
        have er:=Finset.card_erase_of_mem inside
        have pos:=Finset.card_pos.mpr ⟨f,inside⟩
        change (U.erase f ∪ ps).card ≤ T.card+cost w (g::gs)
        simp only [cost,show ¬ctxt (result w g) from cc,if_false]
        omega
      · intro x y ag
        apply determ x y
        intro s h
        by_cases eq : s=f
        · subst s
          apply congrArg g.op.eval
          apply List.map_congr_left
          intro i hi
          exact ag (w.getD i z) (Finset.mem_union_right _ (List.mem_toFinset.mpr (List.mem_map.mpr ⟨i,hi,rfl⟩)))
        · exact ag s (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨eq,h⟩))
    · refine ⟨U,?_,?_,determ⟩
      · intro c h
        exact (unpack c h).resolve_right (fun eq => inside (eq ▸ h))
      · simp only [cost,show ¬ctxt (result w g) from cc,if_false]
        omega

def read (w : List W) (x : Input) := w.map (fun f => f x)
theorem read_at (w : List W) (x : Input) (i : Nat) :
    (read w x).getD i false = (w.getD i z) x := by
  induction w generalizing i with
  | nil => simp [read,List.getD_eq_getElem?_getD,z]
  | cons a w ih => cases i with
    | zero => rfl
    | succ i => exact ih i
theorem read_next (w : List W) (x : Input) (g : Gate) :
    read (next w g) x=read w x++[g.op.eval (g.inputs.map fun i => (read w x).getD i false)] := by
  simp only [read,next,List.map_append,List.map_cons,List.map_nil]
  apply congrArg (fun a : List Bool => (w.map (fun f => f x))++a)
  apply congrArg (fun b : Bool => [b])
  apply congrArg g.op.eval
  exact List.map_congr_left (fun i _ => (read_at w x i).symm)
theorem read_run (w : List W) (x : Input) (gs : List Gate) :
    read (run w gs) x = gs.foldl (fun a g=>a++[g.op.eval (g.inputs.map fun i=>a.getD i false)]) (read w x) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change read (run (next w g) gs) x=_
    rw [ih,read_next]; rfl
theorem base_start : ∀ f∈starting,base f := by
  intro f h
  obtain ⟨i,rfl⟩:=List.mem_ofFn.mp h
  fin_cases i
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  all_goals exact Or.inr (Or.inr (fun _ _ => rfl))

theorem physicalCost (C : Circuit) (leg : FanInTwo C)
    (exactly : ∀ x : Fin 10→Bool, C.eval (List.ofFn x)=graph x) :
    4 ≤ cost starting C.gates := by
  classical
  let w:=run starting C.gates
  have eq : w.getD C.output z=wanted := by
    funext x
    rw [←read_at]
    change (read (run starting C.gates) x).getD C.output false=_
    rw [read_run]
    have h : read starting x=List.ofFn (pins x) := by simp [read,starting,List.map_ofFn]
    rw [h]
    exact exactly (pins x)
  have member : prior w wanted := by
    rw [←eq]
    by_cases lt : C.output<w.length
    · exact Or.inr (by simpa [List.getD_eq_getElem?_getD,lt] using List.getElem_mem lt)
    · left; right; right
      simp [List.getD_eq_getElem?_getD,List.getElem?_eq_none (Nat.le_of_not_gt lt),z,ctxt]
  obtain ⟨S,sb,sz,det⟩:=compress {wanted} starting C.gates
    (fun g hg => (leg g hg).2) (by simpa using member)
  have floor:=supportFive S (fun f hf => (sb f hf).elim id (base_start f))
    (fun a b h => det a b h wanted (by simp))
  simp at sz
  omega
end Research9755.FiberFront

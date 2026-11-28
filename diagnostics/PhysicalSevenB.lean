import PEqualNP.Defs
namespace Research9755.CycleFront
abbrev X := Fin 6 → Bool
abbrev Ctrl := Fin 4 → Bool
abbrev Input := X × Ctrl
abbrev W := Input → Bool
def raw (i : Fin 4) : W := fun x => x.2 i
def ctxt (f : W) := ∀ z : X,∀ t : Ctrl, f (z,t)=f (z,fun _ => false)
def base (f : W) := (∃i,f=raw i) ∨ ctxt f
def kind : Fin 10 → Sum (Fin 4) (Fin 6) :=
  ![.inl 0,.inl 1,.inl 2,.inr 0,.inr 1,.inr 4,.inl 3,.inr 3,.inr 5,.inr 2]
def pins (a : Input) (i : Fin 10) : Bool :=
  match kind i with
  | .inl j => a.2 j
  | .inr j => a.1 j
def graph (x : Fin 10 → Bool) := (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 1 && x 6) || (x 2 && x 3) || (x 2 && x 7) || (x 3 && x 4) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 5 && x 8) || (x 6 && x 8) || (x 6 && x 9) || (x 7 && x 9)
def wanted (a : Input) := graph (pins a)
def witness (i : Fin 9) (k : Fin 6) := (#[0,2,1,10,4,20,5,21,3] : Array Nat)[i.val]!.testBit k.val
theorem differs : ∀i j : Fin 9,i≠j → ∃ t : Ctrl,wanted (witness i,t)≠wanted (witness j,t) := by decide +kernel
theorem depends (i : Fin 4) : ∃ k : Fin 9,∃ t : Ctrl,
    wanted (witness k,t)≠wanted (witness k,Function.update t i (!t i)) := by
  exact (by decide +kernel : ∀ j : Fin 4,∃ k : Fin 9,∃ t : Ctrl,
    wanted (witness k,t)≠wanted (witness k,Function.update t j (!t j))) i
def Agrees (S : Finset W) (a b : Input) := ∀ f∈S,f a=f b
def Determines (S T : Finset W) := ∀ a b,Agrees S a b → Agrees T a b
theorem supportEight (S : Finset W) (ok : ∀ f∈S,base f)
    (determines : ∀ a b,Agrees S a b → wanted a=wanted b) : 8≤S.card := by
  classical
  have need (i : Fin 4) : raw i∈S := by
    by_contra miss
    obtain ⟨k,t,ne⟩ := depends i
    apply ne
    apply determines
    intro f hf
    rcases ok f hf with ⟨j,rfl⟩|ct
    · have hj : j≠i := by rintro rfl; exact miss hf
      simp [raw,Function.update_of_ne hj]
    · exact (ct _ _).trans (ct _ _).symm
  let U : Finset W := Finset.univ.image raw
  have injRaw : Function.Injective raw := by
    intro a b eq
    have h := congrFun eq ((fun _ => false), (fun j => decide (j=a)))
    have q : b=a := by simpa [raw] using h.symm
    exact q.symm
  have four : U.card=4 := by simp [U,Finset.card_image_of_injective _ injRaw]
  have sub : U⊆S := by
    intro f hf
    obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp hf
    exact need i
  let R := S \ U
  have allC (f : R) : ctxt f.val := by
    have h := Finset.mem_sdiff.mp f.property
    rcases ok _ h.1 with ⟨j,eq⟩|ct
    · exact (h.2 (Finset.mem_image.mpr ⟨j,Finset.mem_univ _,eq.symm⟩)).elim
    · exact ct
  let code (i : Fin 9) (f : R) := f.val (witness i,fun _ => false)
  have inj : Function.Injective code := by
    intro i j eq
    by_contra neq
    obtain ⟨t,n⟩ := differs i j neq
    apply n
    apply determines
    intro f hf
    by_cases u : f∈U
    · obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp u
      rfl
    · let w : R := ⟨f,Finset.mem_sdiff.mpr ⟨hf,u⟩⟩
      exact ((allC w) _ _).trans ((congrFun eq w).trans ((allC w) _ _).symm)
  have h := Fintype.card_le_of_injective code inj
  simp at h
  have cu : R.card=S.card-U.card := Finset.card_sdiff_of_subset sub
  by_contra! small
  have bound : R.card≤3 := by omega
  have cases' : R.card=0 ∨ R.card=1 ∨ R.card=2 ∨ R.card=3 := by omega
  rcases cases' with p|p|p|p <;> simp [p] at h

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
        · exact Or.inl (Or.inr cc)
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
          · left; right
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
  cases e : kind i with
  | inl j =>
    left
    refine ⟨j,?_⟩
    funext x
    simp [pins,e,raw]
  | inr j =>
    right
    intro w t
    simp [pins,e]

theorem physicalCost (C : Circuit) (leg : FanInTwo C)
    (exactly : ∀ x : Fin 10→Bool, C.eval (List.ofFn x)=graph x) :
    7 ≤ cost starting C.gates := by
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
    · left; right
      simp [List.getD_eq_getElem?_getD,List.getElem?_eq_none (Nat.le_of_not_gt lt),z,ctxt]
  obtain ⟨S,sb,sz,det⟩:=compress {wanted} starting C.gates
    (fun g hg => (leg g hg).2) (by simpa using member)
  have floor:=supportEight S (fun f hf => (sb f hf).elim id (base_start f))
    (fun a b h => det a b h wanted (by simp))
  simp at sz
  omega
end Research9755.CycleFront

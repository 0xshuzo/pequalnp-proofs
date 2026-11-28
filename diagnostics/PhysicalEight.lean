import PEqualNP.Defs

namespace Split9755

def graph (x : Fin 10 → Bool) := (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 1 && x 6) || (x 2 && x 3) || (x 2 && x 7) || (x 3 && x 4) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 5 && x 8) || (x 6 && x 8) || (x 6 && x 9) || (x 7 && x 9)
def pins (l r : Nat) : Fin 10 → Bool := ![l.testBit 0,r.testBit 0,l.testBit 1,l.testBit 2,r.testBit 1,r.testBit 2,l.testBit 3,l.testBit 4,r.testBit 3,r.testBit 4]
def board (l r : Nat) := graph (pins l r)
def yes : Fin 7 → Nat × Nat := ![(6,0),(24,8),(17,17),(4,2),(3,1),(1,5),(0,12)]
theorem yesDiag : ∀ i, board (yes i).1 (yes i).2 = true := by decide +kernel
theorem yesCross : ∀ i j, i≠j → board (yes i).1 (yes j).2 ≠ true ∨ board (yes j).1 (yes i).2 ≠ true := by decide +kernel
def no : Fin 13 → Nat × Nat := ![(9,0),(20,1),(24,2),(12,4),(8,6),(17,9),(16,3),(5,17),(4,5),(3,24),(2,20),(1,25),(0,7)]
theorem noDiag : ∀ i, board (no i).1 (no i).2 = false := by decide +kernel
theorem noCross : ∀ i j, i≠j → board (no i).1 (no j).2 ≠ false ∨ board (no j).1 (no i).2 ≠ false := by decide +kernel

theorem price {k b : Nat} {t : Bool} {p : Fin k → Nat × Nat}
    (diag : ∀ i,board (p i).1 (p i).2=t)
    (cross : ∀ i j,i≠j → board (p i).1 (p j).2≠t ∨ board (p j).1 (p i).2≠t)
    (L R : Fin b → Nat → Prop)
    (safe : ∀ c l r,L c l → R c r → board l r=t)
    (cover : ∀ l r,board l r=t → ∃ c,L c l ∧ R c r) : k≤b := by
  classical
  have each (i : Fin k) := cover (p i).1 (p i).2 (diag i)
  let tag (i : Fin k) := (each i).choose
  have hit (i : Fin k) : L (tag i) (p i).1 ∧ R (tag i) (p i).2 := (each i).choose_spec
  have inj : Function.Injective tag := by
    intro i j eq
    by_contra ne
    have a := hit i
    have d := hit j
    rw [←eq] at d
    rcases cross i j ne with h|h
    · exact h (safe _ _ _ a.1 d.2)
    · exact h (safe _ _ _ d.1 a.2)
  simpa using Fintype.card_le_of_injective tag inj

theorem both {k m : Nat} (L R : Fin k → Nat → Prop) (P Q : Fin m → Nat → Prop)
    (one : ∀ l r,board l r=true ↔ ∃ i,L i l ∧ R i r)
    (zero : ∀ l r,board l r=false ↔ ∃ j,P j l ∧ Q j r) : 7≤k ∧ 13≤m := by
  exact ⟨price yesDiag yesCross L R (fun i l r a b => (one l r).2 ⟨i,a,b⟩)
      (fun l r => (one l r).1),
    price noDiag noCross P Q (fun i l r a b => (zero l r).2 ⟨i,a,b⟩)
      (fun l r => (zero l r).1)⟩

end Split9755

namespace Cut9755
abbrev Input := Fin 32 × Fin 32
abbrev W := Input → Bool
def leftOnly (f : W) := ∀ x : Input,f x=f (x.1,0)
def rightOnly (f : W) := ∀ x : Input,f x=f (0,x.2)
def base (f : W) := leftOnly f ∨ rightOnly f
def pins (x : Input) := Split9755.pins x.1.val x.2.val
def graph := Split9755.graph
def wanted (x : Input) := graph (pins x)
def row : Fin 14 → Fin 32 := ![0,1,2,3,4,5,16,17,8,12,24,20,9,6]
theorem rowDiff : ∀ i j, i≠j → ∃ t : Fin 32,wanted (row i,t)≠wanted (row j,t) := by decide +kernel
def col : Fin 17 → Fin 32 := ![0,2,1,8,9,10,3,4,6,16,17,20,5,24,25,7,12]
theorem colDiff : ∀ i j, i≠j → ∃ t : Fin 32,wanted (t,col i)≠wanted (t,col j) := by decide +kernel
def Agrees (S : Finset W) (a b : Input) := ∀ f∈S,f a=f b
def Determines (S T : Finset W) := ∀ a b,Agrees S a b → Agrees T a b

theorem supportNine (S : Finset W) (ok : ∀f∈S,base f)
    (determines : ∀a b,Agrees S a b → wanted a=wanted b) : 9 ≤ S.card := by
  classical
  let P := S.filter leftOnly
  let Q := S \ P
  have sub : P ⊆ S := Finset.filter_subset _ _
  have lefts (f : P) : leftOnly f.val := (Finset.mem_filter.mp f.property).2
  have rights (f : Q) : rightOnly f.val := by
    obtain ⟨hm,hn⟩ := Finset.mem_sdiff.mp f.property
    rcases ok _ hm with lp|rp
    · exact (hn (Finset.mem_filter.mpr ⟨hm,lp⟩)).elim
    · exact rp
  let lc (i : Fin 14) (f : P) := f.val (row i,0)
  let rc (i : Fin 17) (f : Q) := f.val (0,col i)
  have li : Function.Injective lc := by
    intro i j eq
    by_contra ne
    obtain ⟨t,h⟩ := rowDiff i j ne
    apply h
    apply determines
    intro f hf
    by_cases hp : f∈P
    · let w : P := ⟨f,hp⟩
      exact (lefts w _).trans ((congrFun eq w).trans (lefts w _).symm)
    · let w : Q := ⟨f,Finset.mem_sdiff.mpr ⟨hf,hp⟩⟩
      exact (rights w _).trans (rights w _).symm
  have ri : Function.Injective rc := by
    intro i j eq
    by_contra ne
    obtain ⟨t,h⟩ := colDiff i j ne
    apply h
    apply determines
    intro f hf
    by_cases hp : f∈P
    · let w : P := ⟨f,hp⟩
      exact (lefts w _).trans (lefts w _).symm
    · let w : Q := ⟨f,Finset.mem_sdiff.mpr ⟨hf,hp⟩⟩
      exact (rights w _).trans ((congrFun eq w).trans (rights w _).symm)
  have lp := Fintype.card_le_of_injective lc li
  have rp := Fintype.card_le_of_injective rc ri
  simp at lp rp
  have pl : 4≤P.card := by
    by_contra! h
    have casesP : P.card=0 ∨ P.card=1 ∨ P.card=2 ∨ P.card=3 := by omega
    rcases casesP with q|q|q|q <;> simp [q] at lp
  have ql : 5≤Q.card := by
    by_contra! h
    have casesQ : Q.card=0 ∨ Q.card=1 ∨ Q.card=2 ∨ Q.card=3 ∨ Q.card=4 := by omega
    rcases casesQ with q|q|q|q|q <;> simp [q] at rp
  have qsub : Q.card=S.card-P.card := Finset.card_sdiff_of_subset sub
  have ps := Finset.card_le_card sub
  omega

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
  | g::tail => (if base (result w g) then 0 else 1) + cost (next w g) tail

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
    by_cases cc : base f
    · refine ⟨U,?_,?_,determ⟩
      · intro c m
        rcases unpack c m with h|rfl
        · exact h
        · exact Or.inl cc
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
            simp [List.getD_eq_getElem?_getD,List.getElem?_eq_none (Nat.le_of_not_gt lt),z,rightOnly]
      refine ⟨S,a,?_,?_⟩
      · have sz:=Finset.card_union_le (U.erase f) ps
        have er:=Finset.card_erase_of_mem inside
        have pos:=Finset.card_pos.mpr ⟨f,inside⟩
        change (U.erase f ∪ ps).card ≤ T.card+cost w (g::gs)
        simp only [cost,show ¬base (result w g) from cc,if_false]
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
      · simp only [cost,show ¬base (result w g) from cc,if_false]
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
  intro f hf
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hf
  fin_cases i <;> first | exact Or.inl (fun _ => rfl) | exact Or.inr (fun _ => rfl)
theorem physicalCost (C : Circuit) (leg : FanInTwo C)
    (exactly : ∀ x : Fin 10→Bool, C.eval (List.ofFn x)=graph x) :
    8 ≤ cost starting C.gates := by
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
      simp [List.getD_eq_getElem?_getD,List.getElem?_eq_none (Nat.le_of_not_gt lt),z,rightOnly]
  obtain ⟨S,sb,sz,det⟩:=compress {wanted} starting C.gates
    (fun g hg => (leg g hg).2) (by simpa using member)
  have floor:=supportNine S (fun f hf => (sb f hf).elim id (base_start f))
    (fun a b h => det a b h wanted (by simp))
  simp at sz
  omega
end Cut9755

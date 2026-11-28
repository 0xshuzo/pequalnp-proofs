import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9809.JointBoundary
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def good (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2
def readGate (g : Gate) (w : List Bool) := g.op.eval (g.inputs.map fun i => w.getD i false)
def stage (w : List Bool) (g : Gate) := w ++ [readGate g w]
def run (gs : List Gate) (w : List Bool) := gs.foldl stage w
def below (a b : List Bool) : Prop :=
  a.length = b.length ∧ ∀ i, a.getD i false = true → b.getD i false = true
theorem extend {a b : List Bool} {v w : Bool} (h : below a b) (hv : v=true → w=true) :
    below (a++[v]) (b++[w]) := by
  refine ⟨by simp [h.1], ?_⟩
  intro i
  by_cases lt : i<a.length
  · have lt' : i<b.length := h.1 ▸ lt
    simpa [List.getD_eq_getElem?_getD,List.getElem?_append_left lt,
      List.getElem?_append_left lt'] using h.2 i
  · by_cases eq : i=a.length
    · subst i
      have last (l : List Bool) (x : Bool) : (l++[x]).getD l.length false=x := by
        simp [List.getD_eq_getElem?_getD]
      rw [last,h.1,last]
      exact hv
    · have lo : (a++[v]).length ≤ i := by simp; omega
      simp [List.getD_eq_getElem?_getD,List.getElem?_eq_none lo]
theorem gate_mono {a b : List Bool} {g : Gate} (h : below a b) (hg : good g) :
    readGate g a=true → readGate g b=true := by
  have op : g.op=GateOp.and ∨ g.op=GateOp.or := by simpa using hg.1
  rcases op with ha | ho
  · simp only [readGate,ha,GateOp.eval,List.all_map,List.all_eq_true,Function.comp_apply,id_eq]
    intro ht i hi
    exact h.2 i (ht i hi)
  · simp only [readGate,ho,GateOp.eval,List.any_map,List.any_eq_true,Function.comp_apply,id_eq]
    rintro ⟨i,hi,hh⟩
    exact ⟨i,hi,h.2 i hh⟩
theorem run_mono {a b : List Bool} (gs : List Gate) (ok : ∀ g ∈ gs, good g)
    (h : below a b) : below (run gs a) (run gs b) := by
  induction gs generalizing a b with
  | nil => exact h
  | cons g gs ih =>
    exact ih (fun t ht => ok _ (by simp [ht])) (extend h (gate_mono h (ok _ (by simp))))


def value (gs : List Gate) (o : Nat) (b : List Bool) := (run gs b).getD o false

theorem value_mono (gs : List Gate) (ok : ∀ g∈gs,good g) (o : Nat)
    {a b : List Bool} (h : below a b) : value gs o a=true → value gs o b=true :=
  (run_mono gs ok h).2 o

theorem below_trans {a b c : List Bool} (h : below a b) (k : below b c) : below a c :=
  ⟨h.1.trans k.1,fun i hh => k.2 i (h.2 i hh)⟩

-- The original positive and negative rails may each have several physical suffix readers.
-- Here bank a b x contains the whole live input list after choosing both rail values.
def lowerUsable {A : Type} (E : Set A) (old : A → List Bool)
    (bank : Bool → Bool → A → List Bool) (e : A) (a b : Bool) : Prop :=
  ∃ p∈E, below (old p) (bank a b e)
def upperUsable {A : Type} (N : Set A) (old : A → List Bool)
    (bank : Bool → Bool → A → List Bool) (i : A) (a b : Bool) : Prop :=
  ∃ q∈N, below (bank a b i) (old q)

theorem jointReplacement {A : Type} [Preorder A]
    (gs : List Gate) (hg : ∀ g∈gs,good g) (o : Nat) (target : A → Bool)
    (old : A → List Bool) (bank : Bool → Bool → A → List Bool)
    (u v : A → Bool) (E N : Set A)
    (correct : ∀ x, value gs o (old x)=target x)
    (ep : ∀ e∈E,target e=true) (ip : ∀ q∈N,target q=false)
    (edges : ∀ x,target x=true → ∃ e∈E,e≤x)
    (maximal : ∀ x,target x=false → ∃ q∈N,x≤q)
    (monotone : ∀ x y : A,x≤y → below (bank (u x) (v x) x) (bank (u y) (v y) y))
    (pe : ∀ e∈E, lowerUsable E old bank e (u e) (v e))
    (ni : ∀ i∈N, upperUsable N old bank i (u i) (v i)) :
    ∀ x, value gs o (bank (u x) (v x) x) = target x := by
  intro x
  cases h : target x with
  | false =>
    obtain ⟨i,hi,le⟩ := maximal x h
    obtain ⟨q,hq,atQ⟩ := ni i hi
    cases b : value gs o (bank (u x) (v x) x) with
    | false => rfl
    | true =>
      have bad := value_mono gs hg o (below_trans (monotone x i le) atQ) b
      rw [correct q,ip q hq] at bad
      contradiction
  | true =>
    obtain ⟨e,he,le⟩ := edges x h
    obtain ⟨p,hp,atP⟩ := pe e he
    exact value_mono gs hg o (below_trans atP (monotone e x le)) ((correct p).trans (ep p hp))

def improves {A : Type} (E N : Set A) (a b : A → Bool) :=
  (∀e∈E,a e=true → b e=true) ∧ (∀i∈N,b i=true → a i=true)
theorem comp_and {A : Type} {E N : Set A} {a b u v : A → Bool}
    (ha : improves E N a u) (hb : improves E N b v) :
    improves E N (fun x => a x && b x) (fun x => u x && v x) := by
  constructor
  · intro x hx h
    simp only [Bool.and_eq_true] at h ⊢
    exact ⟨ha.1 _ hx h.1,hb.1 _ hx h.2⟩
  · intro x hx h
    simp only [Bool.and_eq_true] at h ⊢
    exact ⟨ha.2 _ hx h.1,hb.2 _ hx h.2⟩
theorem comp_or {A : Type} {E N : Set A} {a b u v : A → Bool}
    (ha : improves E N a u) (hb : improves E N b v) :
    improves E N (fun x => a x || b x) (fun x => u x || v x) := by
  constructor
  · intro x hx h
    cases e : a x <;> cases f : b x <;> simp_all [ha.1 x hx,hb.1 x hx]
  · intro x hx h
    cases e : u x <;> cases f : v x <;> simp_all [ha.2 x hx,hb.2 x hx]
-- A virtual bank may alias both rails to arbitrary earlier physical wires.
-- Subsequent gates are copied exactly once even if a rail has many readers.
def ix (l k : Nat) (p : Nat → Nat) (i : Nat) := if i<l then p i else k + (i-l)

def renameGate (f : Nat → Nat) (g : Gate) : Gate := {g with inputs := g.inputs.map f}

theorem lookup {a b : List Bool} (p : Nat → Nat)
    (small : ∀ i<a.length,p i<b.length)
    (same : ∀ i<a.length,a.getD i false=b.getD (p i) false) (tail : List Bool) (i : Nat) :
    (a++tail).getD i false = (b++tail).getD (ix a.length b.length p i) false := by
  by_cases h : i<a.length
  · simpa [ix,h,List.getD_eq_getElem?_getD,List.getElem?_append_left h,
      List.getElem?_append_left (small i h)] using same i h
  · have h1 : a.length≤i := by omega
    have h2 : b.length≤b.length+(i-a.length) := by omega
    simp [ix,h,List.getD_eq_getElem?_getD,List.getElem?_append_right h1,
      List.getElem?_append_right h2]

theorem agreeGate (f : Nat → Nat) (a b : List Bool)
    (h : ∀ i,a.getD i false=b.getD (f i) false) (g : Gate) :
    readGate g a=readGate (renameGate f g) b := by
  dsimp [readGate,renameGate]
  rw [List.map_map]
  apply congrArg g.op.eval
  apply List.map_congr_left
  intro i hi
  exact h i

theorem copiedTail (p : Nat → Nat) (a b : List Bool)
    (small : ∀ i<a.length,p i<b.length)
    (same : ∀ i<a.length,a.getD i false=b.getD (p i) false)
    (gs : List Gate) (t : List Bool) :
    ∃ z : List Bool, run gs (a++t)=a++z ∧
        run (gs.map (renameGate (ix a.length b.length p))) (b++t)=b++z := by
  induction gs generalizing t with
  | nil => exact ⟨t,rfl,rfl⟩
  | cons g gs ih =>
    let v := readGate g (a++t)
    have h : v=readGate (renameGate (ix a.length b.length p) g) (b++t) :=
      agreeGate _ _ _ (lookup p small same t) g
    obtain ⟨z,left,right⟩ := ih (t++[v])
    refine ⟨z,?_,?_⟩
    · change run gs ((a++t)++[v])=_
      simpa only [List.append_assoc] using left
    · change run (gs.map _) ((b++t)++[readGate _ (b++t)])=_
      rw [← h,List.append_assoc]
      exact right

theorem copiedValue (p : Nat → Nat) (a b : List Bool)
    (small : ∀ i<a.length,p i<b.length)
    (same : ∀ i<a.length,a.getD i false=b.getD (p i) false)
    (gs : List Gate) (o : Nat) :
    value gs o a = value (gs.map (renameGate (ix a.length b.length p)))
       (ix a.length b.length p o) b := by
  obtain ⟨z,left,right⟩ := copiedTail p a b small same gs []
  simp only [List.append_nil] at left right
  unfold value
  rw [left,right]
  exact lookup p small same z o

theorem run_length (gs : List Gate) (b : List Bool) : (run gs b).length=b.length+gs.length := by
  induction gs generalizing b with
  | nil => simp [run]
  | cons g gs ih =>
    change (run gs (stage b g)).length=_
    rw [ih]
    simp [stage,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

theorem paidSuffix {n l : Nat} (pre gs : List Gate) (p : Nat → Nat)
    (bank : (Fin n → Bool) → List Bool) (o : Nat) (target : (Fin n → Bool) → Bool)
    (oldLen : ∀ x,(bank x).length=l)
    (small : ∀ i<l,p i<n+pre.length)
    (same : ∀ x i,i<l → (bank x).getD i false=(run pre (List.ofFn x)).getD (p i) false)
    (correct : ∀ x,value gs o (bank x)=target x)
    (gp : ∀ g∈pre,good g) (gg : ∀ g∈gs,good g) :
    ∃ C : Circuit,C.size=pre.length+gs.length ∧ (∀ g∈C.gates,good g) ∧
       ∀ x : Fin n → Bool,C.eval (List.ofFn x)=target x := by
  let f := ix l (n+pre.length) p
  let C : Circuit := ⟨pre ++ gs.map (renameGate f), f o⟩
  refine ⟨C,by simp [C,Circuit.size],?_,?_⟩
  · intro g hg
    change g∈pre++gs.map (renameGate f) at hg
    rcases List.mem_append.mp hg with hp|hs
    · exact gp g hp
    · obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hs
      simpa [renameGate,good] using gg v hv
  · intro x
    let b := run pre (List.ofFn x)
    have el : b.length=n+pre.length := by simp [b,run_length]
    have hh := copiedValue p (bank x) b
      (by simpa only [oldLen x,el] using small)
      (by simpa only [oldLen x] using same x) gs o
    rw [oldLen x,el] at hh
    change (run (pre++gs.map (renameGate f)) (List.ofFn x)).getD (f o) false = target x
    rw [← correct x,hh]
    simp only [run,List.foldl_append,value,b,f]

end PEqualNP.Outside.L_meta_9809.JointBoundary

import PEqualNP.Defs
namespace PlaneOrdered
open PEqualNP.CircuitLowerBounds

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem eval_eq (gs : List Gate) (o : ℕ) (x : List Bool) :
    Circuit.eval ⟨gs, o⟩ x = (wf gs x).getD o false := rfl

theorem wf_snoc (gs : List Gate) (g : Gate) (w : List Bool) :
    wf (gs ++ [g]) w = wf gs w ++ [g.op.eval (g.inputs.map fun i => (wf gs w).getD i false)] := by
  simp [wf, List.foldl_append]

theorem wf_len (gs : List Gate) : ∀ w : List Bool, (wf gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [wf]
  | cons g gs ih =>
    intro w
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]; simp; omega

theorem wf_keep (gs : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (wf gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) i (by simp; omega)
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem wf_prefix (pre post : List Gate) (w : List Bool) (i : ℕ)
    (hi : i < w.length + pre.length) :
    (wf (pre ++ post) w).getD i false = (wf pre w).getD i false := by
  have : wf (pre ++ post) w = wf post (wf pre w) := by simp [wf, List.foldl_append]
  rw [this]
  exact wf_keep post _ i (by rw [wf_len]; exact hi)

theorem getD_snoc_lt (L : List Bool) (a : Bool) (w : ℕ) (h : w < L.length) :
    (L ++ [a]).getD w false = L.getD w false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_snoc_eq (L : List Bool) (a : Bool) : (L ++ [a]).getD L.length false = a := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_snoc_gt (L : List Bool) (a : Bool) (w : ℕ) (h : L.length < w) :
    (L ++ [a]).getD w false = false := by
  rw [List.getD_eq_default]; simp; omega

theorem eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (ins : List ℕ)
    (U V : List Bool) (h : ∀ i, U.getD i false = true → V.getD i false = true) :
    op.eval (ins.map fun i => U.getD i false) = true →
    op.eval (ins.map fun i => V.getD i false) = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id]
    exact fun hall i hi => h i (hall i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
    exact fun ⟨i, hi, hv⟩ => ⟨i, hi, h i hv⟩

theorem ofFn_mono (n : ℕ) (x y : Fin n → Bool) (hxy : ∀ v : Fin n, x v = true → y v = true)
    (w : ℕ) : (List.ofFn x).getD w false = true → (List.ofFn y).getD w false = true := by
  by_cases hw : w < n
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hw, dite_true, Option.getD_some]
    exact hxy ⟨w, hw⟩
  · rw [List.getD_eq_default _ _ (by simp; omega)]
    simp


theorem mono2 (gs : List Gate)
    (hleg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    ∀ U V : List Bool, U.length = V.length →
      (∀ i, U.getD i false = true → V.getD i false = true) →
      ∀ i, (wf gs U).getD i false = true → (wf gs V).getD i false = true := by
  induction gs with
  | nil => intro U V _ h i; exact h i
  | cons g gs ih =>
    intro U V hlen h i
    have hg := (hleg g (by simp)).1
    have := ih (fun g' hg' => hleg g' (by simp [hg']))
      (U ++ [g.op.eval (g.inputs.map fun i => U.getD i false)])
      (V ++ [g.op.eval (g.inputs.map fun i => V.getD i false)]) (by simp [hlen]) (by
        intro t
        rcases Nat.lt_trichotomy t U.length with ht | ht | ht
        · rw [getD_snoc_lt _ _ _ ht, getD_snoc_lt _ _ _ (by omega)]; exact h t
        · subst ht
          rw [getD_snoc_eq]
          have e2 := getD_snoc_eq V (g.op.eval (g.inputs.map fun i => V.getD i false))
          rw [← hlen] at e2
          rw [e2]
          exact eval_mono g.op hg g.inputs U V h
        · rw [getD_snoc_gt _ _ _ ht]; intro hf; exact absurd hf (by simp)) i
    simpa [wf] using this

theorem cmono (C : Circuit) (hC : PEqualNP.MetaComplexity.Monotone2 C) (n : ℕ)
    (x y : Fin n → Bool) (hxy : x ≤ y) :
    C.eval (List.ofFn x) = true → C.eval (List.ofFn y) = true := by
  intro h
  have h' : (wf C.gates (List.ofFn x)).getD C.output false = true := h
  exact mono2 C.gates (fun g hg => ⟨by
      rcases (hC g hg).1 with h | h
      · exact Or.inl h
      · exact Or.inr h, (hC g hg).2⟩) (List.ofFn x) (List.ofFn y) (by simp)
    (fun i => ofFn_mono n x y (fun v hv => by
      have := hxy v
      rw [Bool.le_iff_imp] at this
      exact this hv) i) C.output h'

theorem ordered (n : ℕ) (D : Circuit) (h : PEqualNP.TopForm.IsAO2 n D) (w : ℕ) :
    Monotone (fun x : Fin n → Bool => (D.wires (List.ofFn x)).getD w false) := by
  let C : Circuit := ⟨D.gates,w⟩
  have hm : PEqualNP.MetaComplexity.Monotone2 C := by
    intro g hg
    exact ⟨h.1 g hg,by have eq := h.2.2 g hg; omega⟩
  intro x y hxy
  apply Bool.le_iff_imp.mpr
  exact cmono C hm n x y hxy

end PlaneOrdered

namespace Promise17245
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
abbrev V := Fin 13
abbrev W := Fin 26
def Inc (p l : V) := (p.val+l.val)%13 ∈ ([0,1,3,9] : List Nat)
instance (p l : V) : Decidable (Inc p l) := by unfold Inc; infer_instance
def vec (X Y : Finset V) (i : W) : Bool :=
  if i.val<13 then decide (Fin.ofNat 13 i.val∈X) else decide (Fin.ofNat 13 i.val∈Y)
def pts (x : W → Bool) := Finset.univ.filter fun p : V => x (Fin.castAdd 13 p)=true
def lns (x : W → Bool) := Finset.univ.filter fun l : V => x (Fin.natAdd 13 l)=true
theorem rebuild (x : W → Bool) : vec (pts x) (lns x)=x := by
  funext i
  unfold vec
  split <;> rename_i hi
  · have eq : Fin.castAdd 13 (Fin.ofNat 13 i.val) = i := Fin.ext (by change i.val%13=i.val; omega)
    simp [pts]
    exact congrArg x eq
  · have eq : Fin.natAdd 13 (Fin.ofNat 13 i.val) = i := Fin.ext (by change 13+i.val%13=i.val; have := i.isLt; omega)
    simp only [lns,Finset.mem_filter,Finset.mem_univ,true_and,eq]
    cases x i <;> rfl
end Promise17245

namespace TerminalStars6530
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity Promise17245
abbrev X := W → Bool
abbrev Flag := V × V
def pt (z : Flag) : W := Fin.castAdd 13 z.1
def ln (z : Flag) : W := Fin.natAdd 13 z.2
def flags : Finset Flag := Finset.univ.filter fun e => Inc e.1 e.2
def hasEdge (x : X) : Prop :=
  ∃p l : V, Inc p l ∧ x (Fin.castAdd 13 p)=true ∧ x (Fin.natAdd 13 l)=true
def singletonInput (a : W) : X := fun v => decide (v=a)
def pair (a b : W) : X := fun v => decide (v=a ∨ v=b)
def adj (a b : W) : Bool :=
  decide ((a.val<13 ∧ 13≤b.val ∨ b.val<13 ∧ 13≤a.val) ∧
    (a.val+b.val)%13 ∈ ([0,1,3,9] : List Nat))
def closed (a v : W) : Bool := decide (v=a) || adj a v
def away (a : W) : Finset Flag := flags.filter fun z =>
  closed a (pt z)=false ∧ closed a (ln z)=false
def outside (a : W) : Finset Flag := flags.filter fun z => pt z ≠ a ∧ ln z ≠ a
theorem away_count : ∀a, (away a).card=36 := by decide +kernel
theorem outside_count : ∀a, (outside a).card=48 := by decide +kernel
theorem c4 : ∀a b c d : W, a≠b → c≠d → adj a c=true → adj a d=true →
    adj b c=true → adj b d=false := by decide +kernel
theorem symm : ∀a b, adj a b=adj b a := by decide +kernel
theorem pairEdge : ∀a b, hasEdge (pair a b) ↔ adj a b=true := by
  unfold hasEdge
  decide +kernel
def wire (C : Circuit) (k : Nat) (x : X) := (C.wires (List.ofFn x)).getD k false
def exactPair (C : Circuit) (a b : Nat) : Prop :=
  ∀P L : Finset V, GateOp.and.eval ([a,b].map (fun w => wire C w (vec P L)))=true ↔
    ∃p∈P,∃l∈L,Inc p l
def S (C : Circuit) (k : Nat) := Finset.univ.filter fun a : W =>
  wire C k (singletonInput a)=true
theorem decode {C a b} (h : exactPair C a b) (x : X) :
    wire C a x=true ∧ wire C b x=true ↔ hasEdge x := by
  have step := h (pts x) (lns x)
  rw [rebuild] at step
  change (wire C a x && (wire C b x && true))=true ↔ _ at step
  simp only [Bool.and_true,Bool.and_eq_true] at step
  rw [step]
  constructor
  · rintro ⟨p,hp,l,hl,ed⟩
    exact ⟨p,l,ed,(Finset.mem_filter.mp hp).2,(Finset.mem_filter.mp hl).2⟩
  · rintro ⟨p,l,ed,hp,hl⟩
    exact ⟨p,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hp⟩,l,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hl⟩,ed⟩
theorem liftWire (C : Circuit) (h : Monotone2 C) (k : Nat) (v a b : W)
    (hv : v=a ∨ v=b) (yes : wire C k (singletonInput v)=true) : wire C k (pair a b)=true := by
  let D : Circuit := ⟨C.gates,k⟩
  have hd : Monotone2 D := h
  apply PlaneOrdered.cmono D hd 26 (singletonInput v) (pair a b) _ yes
  intro i
  apply Bool.le_iff_imp.mpr
  intro hi
  have eq : i=v := of_decide_eq_true hi
  apply decide_eq_true
  simpa only [eq] using hv
theorem cross {C a b} (h : Monotone2 C) (e : exactPair C a b) :
    ∀u∈S C a,∀v∈S C b, adj u v=true := by
  intro u hu v hv
  apply (pairEdge u v).mp
  apply (decode e _).mp
  exact ⟨liftWire C h a u u v (Or.inl rfl) (Finset.mem_filter.mp hu).2,
    liftWire C h b v u v (Or.inr rfl) (Finset.mem_filter.mp hv).2⟩
theorem shape {A B : Finset W} (h : ∀u∈A,∀v∈B,adj u v=true) (ha : A.Nonempty) (hb : B.Nonempty) :
    ∃k, (A={k} ∨ B={k}) ∧ ∀v∈A∪B, closed k v=true := by
  obtain ⟨u,hu⟩ := ha
  obtain ⟨v,hv⟩ := hb
  by_cases one : ∀w∈A,w=u
  · have ea : A={u} := Finset.eq_singleton_iff_unique_mem.mpr ⟨hu,one⟩
    refine ⟨u,Or.inl ea,?_⟩
    intro w hw
    rcases Finset.mem_union.mp hw with hw|hw
    · simp [closed,one w hw]
    · simp [closed,h u hu w hw]
  · push_neg at one
    obtain ⟨z,hz,hzu⟩ := one
    have only (w : W) (hw : w∈B) : w=v := by
      by_contra hne
      have bad := c4 z u w v hzu hne (h z hz w hw) (h z hz v hv) (h u hu w hw)
      rw [h u hu v hv] at bad
      contradiction
    have eb : B={v} := Finset.eq_singleton_iff_unique_mem.mpr ⟨hv,only⟩
    refine ⟨v,Or.inr eb,?_⟩
    intro w hw
    rcases Finset.mem_union.mp hw with hw|hw
    · have same : adj v w=true := (symm v w).trans (h w hw v hv)
      simp [closed,same]
    · simp [closed,only w hw]
def doubleFlags (C : Circuit) (a b : Nat) : Finset Flag :=
  flags.filter fun z => pt z ∉ S C a ∪ S C b ∧ ln z ∉ S C a ∪ S C b
def splitFlags (C : Circuit) (a b : Nat) : Finset Flag :=
  flags.filter fun z => (pt z ∈ S C a ∧ ln z ∈ S C b) ∨ (ln z ∈ S C a ∧ pt z ∈ S C b)
theorem bounds {C a b} (h : Monotone2 C) (e : exactPair C a b)
    (ha : (S C a).Nonempty) (hb : (S C b).Nonempty) :
    36≤(doubleFlags C a b).card ∧ 48≤(flags \ splitFlags C a b).card := by
  obtain ⟨k,one,sub⟩ := shape (cross h e) ha hb
  constructor
  · rw [←away_count k]
    apply Finset.card_le_card
    intro z hz
    obtain ⟨flag,pp,ll⟩ := Finset.mem_filter.mp hz
    exact Finset.mem_filter.mpr ⟨flag,fun y => by rw [sub _ y] at pp; contradiction,
      fun y => by rw [sub _ y] at ll; contradiction⟩
  · rw [←outside_count k]
    apply Finset.card_le_card
    intro z hz
    obtain ⟨flag,pp,ll⟩ := Finset.mem_filter.mp hz
    refine Finset.mem_sdiff.mpr ⟨flag,?_⟩
    intro hh
    have hh' := (Finset.mem_filter.mp hh).2
    rcases one with eo|eo <;> rw [eo] at hh' <;>
      simp only [Finset.mem_singleton] at hh' <;> tauto
end TerminalStars6530
namespace TerminalStars6530
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity Promise17245

def boost (x : X) (a : W) : X := fun i => x i || decide (i=a)
def Agree (f : X → Bool) (x : X) : Prop := f x=true ↔ hasEdge x
theorem monotoneWire (C : Circuit) (hm : Monotone2 C) (w : Nat) : Monotone (wire C w) := by
  intro x y sub
  let D : Circuit := ⟨C.gates,w⟩
  have hd : Monotone2 D := hm
  exact Bool.le_iff_imp.mpr (PlaneOrdered.cmono D hd 26 x y sub)
theorem leBoost (x : X) (a : W) : x ≤ boost x a := by
  intro i
  apply Bool.le_iff_imp.mpr
  intro hi
  simp [boost,hi]
theorem singletonBoost (x : X) (a : W) : singletonInput a ≤ boost x a := by
  intro i
  apply Bool.le_iff_imp.mpr
  intro hi
  have e : i=a := of_decide_eq_true hi
  simp [e,boost]
theorem flagAdj : ∀p l : V, Inc p l → adj (Fin.castAdd 13 p) (Fin.natAdd 13 l)=true := by decide +kernel
theorem boostEdge (a : W) (x : X) (off : ∀v,x v=true → adj a v=false) :
    hasEdge (boost x a) → hasEdge x := by
  rintro ⟨p,l,ed,hp,hl⟩
  have ad := flagAdj p l ed
  change (x _ || decide (_=a))=true at hp hl
  simp only [Bool.or_eq_true,decide_eq_true_eq] at hp hl
  rcases hp with hp|hp <;> rcases hl with hl|hl
  · exact ⟨p,l,ed,hp,hl⟩
  · rw [hl] at ad
    have bad := off _ hp
    rw [symm,ad] at bad
    contradiction
  · rw [hp] at ad
    rw [off _ hl] at ad
    contradiction
  · have noSame : Fin.castAdd 13 p ≠ Fin.natAdd 13 l := by
      intro eq
      have eq' := congrArg Fin.val eq
      change p.val=13+l.val at eq'
      omega
    exact (noSame (hp.trans hl.symm)).elim
theorem guardRestriction {C : Circuit} {a b : Nat} (hm : Monotone2 C) (ex : exactPair C a b)
    (u : W) (hu : u∈S C a) (x : X) (off : ∀v,x v=true → adj u v=false) :
    Agree (wire C b) x := by
  constructor
  · intro yes
    have ha := Bool.le_iff_imp.mp (monotoneWire C hm a (singletonBoost x u)) (Finset.mem_filter.mp hu).2
    have hb := Bool.le_iff_imp.mp (monotoneWire C hm b (leBoost x u)) yes
    exact boostEdge u x off ((decode ex _).mp ⟨ha,hb⟩)
  · intro yes
    exact ((decode ex _).mpr yes).2
theorem flipPair {C : Circuit} {a b : Nat} (ex : exactPair C a b) : exactPair C b a := by
  intro P L
  have e := ex P L
  change (_ && (_ && true))=true ↔ _ at e ⊢
  simpa only [Bool.and_true,Bool.and_eq_true,and_comm] using e
def coreVertices (u v : W) : Finset W := Finset.univ.filter fun w => adj u w=false ∧ adj v w=false
def coreFlags (u v : W) : Finset Flag := flags.filter fun f => pt f∈coreVertices u v ∧ ln f∈coreVertices u v
theorem coreCounts : ∀u v, adj u v=true → (coreVertices u v).card=18 ∧ (coreFlags u v).card=27 := by decide +kernel
theorem sameCore {C : Circuit} {a b : Nat} (hm : Monotone2 C) (ex : exactPair C a b) {u v : W}
    (hu : u∈S C a) (hv : v∈S C b) :
    (coreVertices u v).card=18 ∧ (coreFlags u v).card=27 ∧
    ∀x : X,(∀w,x w=true → w∈coreVertices u v) → Agree (wire C a) x ∧ Agree (wire C b) x := by
  have ad := cross hm ex _ hu _ hv
  obtain ⟨m,n⟩ := coreCounts u v ad
  refine ⟨m,n,?_⟩
  intro x mask
  exact ⟨guardRestriction hm (flipPair ex) v hv x (fun w h => (Finset.mem_filter.mp (mask w h)).2.2),
    guardRestriction hm ex u hu x (fun w h => (Finset.mem_filter.mp (mask w h)).2.1)⟩
theorem distinguish : ∀a v : W, a≠v → ∃k : W,adj a k=false ∧ adj v k=true := by decide +kernel
theorem essential25 {C : Circuit} {a b : Nat} (hm : Monotone2 C) (ex : exactPair C a b) {u : W}
    (hu : u∈S C a) (v : W) (different : u≠v) :
    ∃x y : X, x u=true ∧ y u=true ∧ (∀i,i≠v → x i=y i) ∧ wire C b x=false ∧ wire C b y=true := by
  obtain ⟨k,uk,vk⟩ := distinguish _ _ different
  let x := pair u k
  let y := boost x v
  have hit : wire C a x=true := liftWire C hm a u u k (Or.inl rfl) (Finset.mem_filter.mp hu).2
  have no : wire C b x=false := by
    cases h : wire C b x with
    | false => rfl
    | true => exact False.elim (Bool.noConfusion (uk.symm.trans ((pairEdge u k).mp ((decode ex x).mp ⟨hit,h⟩))))
  have pos : hasEdge y := by
    obtain ⟨p,l,edge,hp,hl⟩ := (pairEdge v k).mpr vk
    have sub (j : W) (h : pair v k j=true) : y j=true := by
      have h' : j=v ∨ j=k := of_decide_eq_true h
      rcases h' with rfl|rfl <;> simp [y,boost,x,pair]
    exact ⟨p,l,edge,sub _ hp,sub _ hl⟩
  refine ⟨x,y,by simp [x,pair],by simp [x,y,boost,pair],?_,no,((decode ex y).mpr pos).2⟩
  intro i hi
  simp [y,boost,hi]
end TerminalStars6530
namespace TerminalStars6530
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity Promise17245

def Ignores (C : Circuit) (w : Nat) (v : W) : Prop :=
  ∀x y : X,(∀i,i≠v → x i=y i) → wire C w x=wire C w y
theorem omittedNeighbors {C a b} (ex : exactPair C a b) {v : W} (omit : Ignores C a v) :
    ∀w : W,adj v w=true → w∈S C a := by
  intro w hw
  have yes := ((decode ex _).mpr ((pairEdge v w).mpr hw)).1
  have eq := omit (pair v w) (singletonInput w) (by intro i hi; simp [pair,singletonInput,hi])
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,eq.symm.trans yes⟩
theorem noComplete : ∀u v : W,∃i j : W,adj u i=true ∧ adj v j=true ∧ adj i j=false := by decide +kernel
theorem neighborsIdentify : ∀u v : W, u≠v → ∃i : W,adj u i=true ∧ adj i v=false := by decide +kernel
theorem fullOperand {C a b} (hm : Monotone2 C) (ex : exactPair C a b) :
    (∀u,¬Ignores C a u) ∨ (∀u,¬Ignores C b u) := by
  classical
  by_cases allA : ∀u,¬Ignores C a u
  · exact Or.inl allA
  · push_neg at allA
    obtain ⟨u,omit⟩ := allA
    right
    intro v bad
    obtain ⟨i,j,ui,vj,ij⟩ := noComplete u v
    have ad := cross hm ex i (omittedNeighbors ex omit i ui) j (omittedNeighbors (flipPair ex) bad j vj)
    rw [ij] at ad
    contradiction
theorem omittedStar {C a b} (hm : Monotone2 C) (ex : exactPair C a b) {u : W}
    (omit : Ignores C a u) (on : (S C b).Nonempty) :
    S C b={u} ∧ S C a=Finset.univ.filter (fun i => adj u i=true) := by
  have only (v : W) (hv : v∈S C b) : v=u := by
    by_contra hne
    obtain ⟨i,ui,iv⟩ := neighborsIdentify u v (Ne.symm hne)
    have yes := cross hm ex i (omittedNeighbors ex omit i ui) v hv
    rw [iv] at yes
    contradiction
  obtain ⟨v,hv⟩ := on
  have hu : u∈S C b := only v hv ▸ hv
  refine ⟨Finset.eq_singleton_iff_unique_mem.mpr ⟨hu,only⟩,?_⟩
  ext i
  simp only [Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · intro hi
    exact (symm u i).trans (cross hm ex i hi u hu)
  · exact omittedNeighbors ex omit i
end TerminalStars6530

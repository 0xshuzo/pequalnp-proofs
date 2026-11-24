import Mathlib
import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_3590
open PEqualNP.CircuitLowerBounds
abbrev Sig := BitVec 512
def zero : Sig := 0
def one : Sig := BitVec.allOnes 512
def neg (a : Sig) : Sig := ~~~a
def bin (d : Bool) (a b : Sig) : Sig := if d then a ||| b else a &&& b
def proper (a : Sig) : Prop := a ≠ zero ∧ a ≠ one
private theorem bin_comm (d : Bool) (a b : Sig) : bin d a b = bin d b a := by
  cases d <;> simp [bin,BitVec.and_comm,BitVec.or_comm]

def Live (target : Sig) (k t : Nat) (S : Finset Sig) : Prop :=
  ∀ M : Nat → Nat → Finset Sig → Prop,
  (∀ (hp : proper target), M 0 0 {target}) →
  (∀ {k t : Nat} {U : Finset Sig} {a : Sig} (ha : proper a) (hf : neg a ∉ insert a U) (tail : M k t (insert (neg a) U)), M (k+1) (t+1) (insert a U)) →
  (∀ {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool} (ha : proper a) (hb : proper b) (hab : a ≠ b) (hf : bin d a b ∉ insert a (insert b U)) (tail : M k t (insert (bin d a b) U)), M (k+1) t (insert a (insert b U))) → M k t S
theorem Live.stop {target : Sig} : ∀ (hp : proper target), Live target 0 0 {target} := by
  intro hp
  intro M stopStep unaryStep binaryStep
  exact stopStep hp
theorem Live.unary {target : Sig} : ∀ {k t : Nat} {U : Finset Sig} {a : Sig} (ha : proper a) (hf : neg a ∉ insert a U) (tail : Live target k t (insert (neg a) U)), Live target (k+1) (t+1) (insert a U) := by
  intro k t  U  a  ha hf tail
  intro M stopStep unaryStep binaryStep
  exact unaryStep ha hf (tail M stopStep unaryStep binaryStep)
theorem Live.binary {target : Sig} : ∀ {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool} (ha : proper a) (hb : proper b) (hab : a ≠ b) (hf : bin d a b ∉ insert a (insert b U)) (tail : Live target k t (insert (bin d a b) U)), Live target (k+1) t (insert a (insert b U)) := by
  intro k t  U  a b  d  ha hb hab hf tail
  intro M stopStep unaryStep binaryStep
  exact binaryStep ha hb hab hf (tail M stopStep unaryStep binaryStep)
theorem Live.weakInduct {target : Sig} {M : Nat → Nat → Finset Sig → Prop} {k t : Nat} {S : Finset Sig} (h : Live target k t S)
    (stop : ∀ (hp : proper target), M 0 0 {target})
    (unary : ∀ {k t : Nat} {U : Finset Sig} {a : Sig} (ha : proper a) (hf : neg a ∉ insert a U) (tail : Live target k t (insert (neg a) U)) (ih : M k t (insert (neg a) U)), M (k+1) (t+1) (insert a U))
    (binary : ∀ {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool} (ha : proper a) (hb : proper b) (hab : a ≠ b) (hf : bin d a b ∉ insert a (insert b U)) (tail : Live target k t (insert (bin d a b) U)) (ih : M k t (insert (bin d a b) U)), M (k+1) t (insert a (insert b U)))
    : M k t S := by
  apply And.right (a := Live target k t S)
  apply h (fun k t S => Live target k t S ∧ M k t S)
  · intro hp
    exact ⟨Live.stop hp, stop hp ⟩
  · intro k t  U  a  ha hf tail
    exact ⟨Live.unary ha hf tail.1, unary ha hf tail.1 tail.2⟩
  · intro k t  U  a b  d  ha hb hab hf tail
    exact ⟨Live.binary ha hb hab hf tail.1, binary ha hb hab hf tail.1 tail.2⟩
theorem Live.induct {target : Sig} {M : ∀ (k t : Nat) (S : Finset Sig), Live target k t S → Prop} {k t : Nat} {S : Finset Sig} (h : Live target k t S)
    (stop : ∀ (hp : proper target), M 0 0 {target} (Live.stop hp))
    (unary : ∀ {k t : Nat} {U : Finset Sig} {a : Sig} (ha : proper a) (hf : neg a ∉ insert a U) (tail : Live target k t (insert (neg a) U)) (ih : M k t (insert (neg a) U) tail), M (k+1) (t+1) (insert a U) (Live.unary ha hf tail))
    (binary : ∀ {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool} (ha : proper a) (hb : proper b) (hab : a ≠ b) (hf : bin d a b ∉ insert a (insert b U)) (tail : Live target k t (insert (bin d a b) U)) (ih : M k t (insert (bin d a b) U) tail), M (k+1) t (insert a (insert b U)) (Live.binary ha hb hab hf tail))
    : M k t S h := by
  apply Live.weakInduct (M := fun k t S => ∀ z, M k t S z) h _ _ _ h
  · intro hp z
    exact stop hp
  · intro k t  U  a  ha hf tail ih z
    exact unary ha hf tail (ih tail)
  · intro k t  U  a b  d  ha hb hab hf tail ih z
    exact binary ha hb hab hf tail (ih tail)


private lemma live_proper {k t S} (h : Live target k t S) : ∀ a ∈ S, proper a := by
  induction h using Live.induct with
  | stop hp => simpa using hp
  | unary ha hf _ ih => simpa using And.intro ha (fun a h => ih a (Finset.mem_insert_of_mem h))
  | binary ha hb hab hf _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha,hb,fun a h => ih a (Finset.mem_insert_of_mem h)⟩

private lemma live_size {k t S} (h : Live target k t S) : t ≤ k ∧ S.card+t ≤ k+1 := by
  induction h using Live.induct with
  | stop hp => simp
  | @unary k t U a ha hf _ ih =>
    have hu : neg a ∉ U := fun hm => hf (Finset.mem_insert_of_mem hm)
    rw [Finset.card_insert_of_notMem hu] at ih
    have hc := Finset.card_insert_le a U
    exact ⟨by omega,by omega⟩
  | @binary k t U a b d ha hb hab hf _ ih =>
    have hu : bin d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1 := Finset.card_insert_le (a := a) (s := insert b U)
    have h2 := Finset.card_insert_le (a := b) (s := U)
    exact ⟨by omega,by omega⟩


def gv (w : List Sig) (g : Gate) : Sig :=
  let xs := g.inputs.map (fun i => w.getD i zero)
  match g.op with
  | .and => xs.foldr (bin false) one
  | .or => xs.foldr (bin true) zero
  | .not => neg (xs.headD zero)
  | _ => zero

def execute (gs : List Gate) (w : List Sig) : List Sig :=
  gs.foldl (fun l g => l ++ [gv l g]) w

def represented (w : List Sig) (v : Sig) : Prop := v ∈ w ∨ ¬proper v

private lemma get_rep (w : List Sig) (i : Nat) : represented w (w.getD i zero) := by
  simp only [List.getD_eq_getElem?_getD]
  cases h : w[i]? with
  | none => exact Or.inr (fun h => h.1 rfl)
  | some a => exact Or.inl (List.mem_of_getElem? h)

private lemma bin_laws (a : Sig) :
    bin false a one = a ∧ bin true a zero = a ∧
    bin false a zero = zero ∧ bin true a one = one ∧
    bin false a a = a ∧ bin true a a = a := by
  simp only [bin,one,zero,Bool.false_eq_true,ite_false,ite_true,BitVec.and_allOnes,BitVec.or_zero,BitVec.and_zero,BitVec.or_allOnes,BitVec.and_self,BitVec.or_self,and_self] <;> simp

private lemma neg_laws : neg zero = one ∧ neg one = zero := by simp [neg,zero,one]

private lemma operand_cases {w : List Sig} {a : Sig} (h : represented w a) :
    a = zero ∨ a = one ∨ a ∈ w ∧ proper a := by
  by_cases hz : a = zero
  · exact Or.inl hz
  by_cases ho : a = one
  · exact Or.inr (Or.inl ho)
  exact Or.inr (Or.inr ⟨h.resolve_right (fun x => x ⟨hz,ho⟩),hz,ho⟩)

def witness (w : List Sig) (z : Sig) : Prop :=
  (∃ a ∈ w, proper a ∧ z = neg a) ∨
  (∃ d a b, a ∈ w ∧ b ∈ w ∧ proper a ∧ proper b ∧ a ≠ b ∧ z = bin d a b)

private lemma bin_rep {w a b} (d : Bool) (ha : represented w a) (hb : represented w b) :
    represented w (bin d a b) ∨ witness w (bin d a b) := by
  have rz : represented w zero := Or.inr (fun h => h.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2 rfl)
  obtain ⟨a1,a0,az,ao,aa,aa'⟩ := bin_laws a
  obtain ⟨b1,b0,bz,bo,bb,bb'⟩ := bin_laws b
  rcases operand_cases ha with rfl | rfl | ⟨ham,hap⟩
  · rw [bin_comm]; cases d <;> simp_all
  · rw [bin_comm]; cases d <;> simp_all
  rcases operand_cases hb with rfl | rfl | ⟨hbm,hbp⟩
  · cases d <;> simp_all
  · cases d <;> simp_all
  by_cases he : a=b
  · subst b; cases d <;> simp_all
  exact Or.inr (Or.inr ⟨d,a,b,ham,hbm,hap,hbp,he,rfl⟩)

private lemma gate_rep (w : List Sig) (g : Gate)
    (h : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2) :
    represented w (gv w g) ∨ witness w (gv w g) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at h
  obtain ⟨ho,hl⟩ := h
  have rz : represented w zero := Or.inr (fun h => h.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2 rfl)
  have nx (a : Sig) (ha : represented w a) : represented w (neg a) ∨ witness w (neg a) := by
    rcases operand_cases ha with rfl | rfl | ⟨hm,hp⟩
    · exact Or.inl (neg_laws.1 ▸ ro)
    · exact Or.inl (neg_laws.2 ▸ rz)
    · exact Or.inr (Or.inl ⟨a,hm,hp,rfl⟩)
  cases l with
  | nil =>
    rcases ho with rfl | rfl | rfl
    · exact Or.inl ro
    · exact Or.inl rz
    · exact nx _ rz
  | cons i l =>
    cases l with
    | nil =>
      rcases ho with rfl | rfl | rfl
      · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).1] using Or.inl (b := witness w (w.getD i zero)) (get_rep w i)
      · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).2.1] using Or.inl (b := witness w (w.getD i zero)) (get_rep w i)
      · exact nx _ (get_rep w i)
    | cons j l =>
      cases l with
      | cons a l => simp at hl
      | nil =>
        rcases ho with rfl | rfl | rfl
        · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).1] using bin_rep false (get_rep w i) (get_rep w j)
        · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).2.1] using bin_rep true (get_rep w i) (get_rep w j)
        · exact nx _ (get_rep w i)



private lemma pull_gate {w : List Sig} {z : Sig} {k t S} (h : Live target k t S)
    (hz : represented w z ∨ witness w z) (sub : ∀ a ∈ S, a ∈ w++[z]) :
    ∃ k' t' S', k' ≤ k+1 ∧ Live target k' t' S' ∧ ∀ a ∈ S', a ∈ w := by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ w
    · refine ⟨k,t,S,by omega,h,?_⟩
      intro a ha
      have hu : a ∈ w ∨ a = z := by simpa using sub a ha
      rcases hu with hu | rfl
      · exact hu
      · exact hw
    · have hp := live_proper h z hm
      rcases hz with hr | (⟨a,ha,hp',eq⟩ | ⟨d,a,b,ha,hb,pa,pb,hab,eq⟩)
      · exact False.elim ((hr.resolve_left hw) hp)
      · subst z
        let U := S.erase (neg a)
        have ht : Live target k t (insert (neg a) U) := by simpa [U,Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U, v ∈ w := by
          intro v hv
          obtain ⟨hne,hm⟩ := Finset.mem_erase.mp hv
          simpa [hne] using sub v hm
        have hf : neg a ∉ insert a U := by
          intro hh
          rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          · exact hw (hu _ u)
        exact ⟨_,_,_,Nat.le_refl _,Live.unary hp' hf ht,by simpa using And.intro ha hu⟩
      · subst z
        let U := S.erase (bin d a b)
        have ht : Live target k t (insert (bin d a b) U) := by simpa [U,Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U, v ∈ w := by
          intro v hv
          obtain ⟨hne,hm⟩ := Finset.mem_erase.mp hv
          simpa [hne] using sub v hm
        have hf : bin d a b ∉ insert a (insert b U) := by
          intro hh
          rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          rcases Finset.mem_insert.mp u with eq | u
          · exact hw (eq.symm ▸ hb)
          · exact hw (hu _ u)
        exact ⟨_,_,_,Nat.le_refl _,Live.binary pa pb hab hf ht,by simpa using And.intro ha (And.intro hb hu)⟩
  · refine ⟨k,t,S,by omega,h,?_⟩
    intro a ha
    have hn : a ≠ z := fun hh => hm (hh ▸ ha)
    simpa [hn] using sub a ha

private lemma extract (gs : List Gate) (w : List Sig)
    (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (hp : proper target) (hout : target ∈ execute gs w) :
    ∃ k t S, k ≤ gs.length ∧ Live target k t S ∧ ∀ a ∈ S, a ∈ w := by
  induction gs generalizing w with
  | nil => exact ⟨0,0,{target},by simp,Live.stop hp,by simpa [execute] using hout⟩
  | cons g gs ih =>
    obtain ⟨k,t,S,hk,ht,hs⟩ := ih (w++[gv w g]) (fun a ha => legal a (by simp [ha])) hout
    obtain ⟨l,u,T,hl,hu,hT⟩ := pull_gate ht (gate_rep w g (legal g (by simp))) hs
    exact ⟨l,u,T,by simp; omega,hu,hT⟩

def bit (i : Fin 512) (a : Sig) : Bool := a.getLsbD i.val
private lemma bit_zero (i) : bit i zero = false := by simp [bit,zero]
private lemma bit_one (i) : bit i one = true := by unfold bit one; rw [BitVec.getLsbD_allOnes]; simp
private lemma bit_neg (i) (a : Sig) : bit i (neg a) = !(bit i a) := by simp [bit,neg,i.isLt]
private lemma bit_bin (i d) (a b : Sig) : bit i (bin d a b) =
    (if d then bit i a || bit i b else bit i a && bit i b) := by cases d <;> simp [bit,bin]

private lemma b_read (i) (w : List Sig) (j : Nat) :
    (w.map (bit i)).getD j false = bit i (w.getD j zero) := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases w[j]? with
  | none => exact (bit_zero _).symm
  | some a => rfl

private lemma run_bit (i) (g : Gate) (w : List Sig)
    (hg : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    bit i (gv w g) = g.op.eval (g.inputs.map fun j => (w.map (bit i)).getD j false) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hg
  simp only [b_read]
  rcases hg with rfl | rfl | rfl
  · induction l with
    | nil => exact bit_one _
    | cons a l ih =>
      change bit i (bin false _ _) = (_ && _)
      rw [bit_bin]; exact congrArg (fun x => bit i (w.getD a zero) && x) ih
  · induction l with
    | nil => exact bit_zero _
    | cons a l ih =>
      change bit i (bin true _ _) = (_ || _)
      rw [bit_bin]; exact congrArg (fun x => bit i (w.getD a zero) || x) ih
  · cases l with
    | nil =>
      change bit i (neg zero) = !false
      rw [bit_neg,bit_zero]
    | cons a l => exact bit_neg _ _

private lemma execute_bits (gs : List Gate) (i) (w : List Sig)
    (hg : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    (execute gs w).map (bit i) =
    gs.foldl (fun (l : List Bool) g => l++[g.op.eval (g.inputs.map fun j => l.getD j false)]) (w.map (bit i)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (execute gs (w++[gv w g])).map _ = _
    rw [ih _ (fun a ha => hg a (by simp [ha]))]
    simp only [List.foldl_cons,List.map_append,List.map_singleton,run_bit i g w (hg g (by simp))]




abbrev Wire (R : Type) := R → Bool

def inv {R} (a : Wire R) : Wire R := fun r => !(a r)

def combine {R} (isOr : Bool) (a b : Wire R) : Wire R :=
  if isOr then fun r => a r || b r else fun r => a r && b r

def Constant {R} (a : Wire R) : Prop := ∃ b : Bool, a = fun _ => b

noncomputable def cost {R} (a : Wire R) : Nat := by
  classical exact if Constant a then 1 else 0

noncomputable def mass {R} (xs : List (Wire R)) : Nat := (xs.map cost).sum

def Available {R} (pool : List (Wire R)) (v : Wire R) : Prop := v ∈ pool ∨ Constant v

def supply {R} (pool xs : List (Wire R)) := ∀ a ∈ xs, Available pool a

def Reach {R : Type} (roots : List (Wire R)) (p : Nat) (bank : List (Wire R)) : Prop :=
  ∀ M : Nat → List (Wire R) → Prop,
  (M 0 roots) →
  (∀ {p : Nat} {bank : List (Wire R)} {a : Wire R} (tail : M p bank) (ha : Available bank a), M (p+1) (inv a :: bank)) →
  (∀ {p : Nat} {bank : List (Wire R)} {a b : Wire R} (op : Bool) (tail : M p bank) (ha : Available bank a) (hb : Available bank b), M (p+1) (combine op a b :: bank)) → M p bank
theorem Reach.start {R : Type} {roots : List (Wire R)} : Reach roots 0 roots := by
  intro M startStep oneStep twoStep
  exact startStep
theorem Reach.one {R : Type} {roots : List (Wire R)} : ∀ {p : Nat} {bank : List (Wire R)} {a : Wire R} (tail : Reach roots p bank) (ha : Available bank a), Reach roots (p+1) (inv a :: bank) := by
  intro p  bank  a  tail ha
  intro M startStep oneStep twoStep
  exact oneStep (tail M startStep oneStep twoStep) ha
theorem Reach.two {R : Type} {roots : List (Wire R)} : ∀ {p : Nat} {bank : List (Wire R)} {a b : Wire R} (op : Bool) (tail : Reach roots p bank) (ha : Available bank a) (hb : Available bank b), Reach roots (p+1) (combine op a b :: bank) := by
  intro p  bank  a b  op tail ha hb
  intro M startStep oneStep twoStep
  exact twoStep op (tail M startStep oneStep twoStep) ha hb
theorem Reach.weakInduct {R : Type} {roots : List (Wire R)} {M : Nat → List (Wire R) → Prop} {p : Nat} {bank : List (Wire R)} (h : Reach roots p bank)
    (start : M 0 roots)
    (one : ∀ {p : Nat} {bank : List (Wire R)} {a : Wire R} (tail : Reach roots p bank) (ha : Available bank a) (ih : M p bank), M (p+1) (inv a :: bank))
    (two : ∀ {p : Nat} {bank : List (Wire R)} {a b : Wire R} (op : Bool) (tail : Reach roots p bank) (ha : Available bank a) (hb : Available bank b) (ih : M p bank), M (p+1) (combine op a b :: bank))
    : M p bank := by
  apply And.right (a := Reach roots p bank)
  apply h (fun p bank => Reach roots p bank ∧ M p bank)
  · exact ⟨Reach.start , start  ⟩
  · intro p  bank  a  tail ha
    exact ⟨Reach.one tail.1 ha, one tail.1 ha tail.2⟩
  · intro p  bank  a b  op tail ha hb
    exact ⟨Reach.two op tail.1 ha hb, two op tail.1 ha hb tail.2⟩
theorem Reach.induct {R : Type} {roots : List (Wire R)} {M : ∀ (p : Nat) (bank : List (Wire R)), Reach roots p bank → Prop} {p : Nat} {bank : List (Wire R)} (h : Reach roots p bank)
    (start : M 0 roots (Reach.start ))
    (one : ∀ {p : Nat} {bank : List (Wire R)} {a : Wire R} (tail : Reach roots p bank) (ha : Available bank a) (ih : M p bank tail), M (p+1) (inv a :: bank) (Reach.one tail ha))
    (two : ∀ {p : Nat} {bank : List (Wire R)} {a b : Wire R} (op : Bool) (tail : Reach roots p bank) (ha : Available bank a) (hb : Available bank b) (ih : M p bank tail), M (p+1) (combine op a b :: bank) (Reach.two op tail ha hb))
    : M p bank h := by
  apply Reach.weakInduct (M := fun p bank => ∀ z, M p bank z) h _ _ _ h
  · intro z
    exact start
  · intro p  bank  a  tail ha ih z
    exact one tail ha (ih tail)
  · intro p  bank  a b  op tail ha hb ih z
    exact two op tail ha hb (ih tail)


def kept {α : Type} (save : Bool) (x : α) (xs : List α) := if save then x::xs else xs

def Run {R : Type} (goal : Wire R) (s : Nat) (ws : List (Wire R)) : Prop :=
  ∀ M : Nat → List (Wire R) → Prop,
  (M 0 [goal]) →
  (∀ {s : Nat} {xs zs : List (Wire R)} (eq : xs.Perm zs) (tail : M s xs), M s zs) →
  (∀ {s : Nat} {a : Wire R} {rest : List (Wire R)} (save : Bool) (tail : M s (inv a :: kept save a rest)), M (s+1) (a :: rest)) →
  (∀ {s : Nat} {a b : Wire R} {rest : List (Wire R)} (op : Bool) (ka : Bool) (kb : Bool) (tail : M s (combine op a b :: kept ka a (kept kb b rest))), M (s+1) (a :: b :: rest)) → M s ws
theorem Run.stop {R : Type} {goal : Wire R} : Run goal 0 [goal] := by
  intro M stopStep permStep oneStep twoStep
  exact stopStep
theorem Run.perm {R : Type} {goal : Wire R} : ∀ {s : Nat} {xs zs : List (Wire R)} (eq : xs.Perm zs) (tail : Run goal s xs), Run goal s zs := by
  intro s  xs zs  eq tail
  intro M stopStep permStep oneStep twoStep
  exact permStep eq (tail M stopStep permStep oneStep twoStep)
theorem Run.one {R : Type} {goal : Wire R} : ∀ {s : Nat} {a : Wire R} {rest : List (Wire R)} (save : Bool) (tail : Run goal s (inv a :: kept save a rest)), Run goal (s+1) (a :: rest) := by
  intro s  a  rest  save tail
  intro M stopStep permStep oneStep twoStep
  exact oneStep save (tail M stopStep permStep oneStep twoStep)
theorem Run.two {R : Type} {goal : Wire R} : ∀ {s : Nat} {a b : Wire R} {rest : List (Wire R)} (op : Bool) (ka : Bool) (kb : Bool) (tail : Run goal s (combine op a b :: kept ka a (kept kb b rest))), Run goal (s+1) (a :: b :: rest) := by
  intro s  a b  rest  op ka kb tail
  intro M stopStep permStep oneStep twoStep
  exact twoStep op ka kb (tail M stopStep permStep oneStep twoStep)
theorem Run.weakInduct {R : Type} {goal : Wire R} {M : Nat → List (Wire R) → Prop} {s : Nat} {ws : List (Wire R)} (h : Run goal s ws)
    (stop : M 0 [goal])
    (perm : ∀ {s : Nat} {xs zs : List (Wire R)} (eq : xs.Perm zs) (tail : Run goal s xs) (ih : M s xs), M s zs)
    (one : ∀ {s : Nat} {a : Wire R} {rest : List (Wire R)} (save : Bool) (tail : Run goal s (inv a :: kept save a rest)) (ih : M s (inv a :: kept save a rest)), M (s+1) (a :: rest))
    (two : ∀ {s : Nat} {a b : Wire R} {rest : List (Wire R)} (op : Bool) (ka : Bool) (kb : Bool) (tail : Run goal s (combine op a b :: kept ka a (kept kb b rest))) (ih : M s (combine op a b :: kept ka a (kept kb b rest))), M (s+1) (a :: b :: rest))
    : M s ws := by
  apply And.right (a := Run goal s ws)
  apply h (fun s ws => Run goal s ws ∧ M s ws)
  · exact ⟨Run.stop , stop  ⟩
  · intro s  xs zs  eq tail
    exact ⟨Run.perm eq tail.1, perm eq tail.1 tail.2⟩
  · intro s  a  rest  save tail
    exact ⟨Run.one save tail.1, one save tail.1 tail.2⟩
  · intro s  a b  rest  op ka kb tail
    exact ⟨Run.two op ka kb tail.1, two op ka kb tail.1 tail.2⟩
theorem Run.induct {R : Type} {goal : Wire R} {M : ∀ (s : Nat) (ws : List (Wire R)), Run goal s ws → Prop} {s : Nat} {ws : List (Wire R)} (h : Run goal s ws)
    (stop : M 0 [goal] (Run.stop ))
    (perm : ∀ {s : Nat} {xs zs : List (Wire R)} (eq : xs.Perm zs) (tail : Run goal s xs) (ih : M s xs tail), M s zs (Run.perm eq tail))
    (one : ∀ {s : Nat} {a : Wire R} {rest : List (Wire R)} (save : Bool) (tail : Run goal s (inv a :: kept save a rest)) (ih : M s (inv a :: kept save a rest) tail), M (s+1) (a :: rest) (Run.one save tail))
    (two : ∀ {s : Nat} {a b : Wire R} {rest : List (Wire R)} (op : Bool) (ka : Bool) (kb : Bool) (tail : Run goal s (combine op a b :: kept ka a (kept kb b rest))) (ih : M s (combine op a b :: kept ka a (kept kb b rest)) tail), M (s+1) (a :: b :: rest) (Run.two op ka kb tail))
    : M s ws h := by
  apply Run.weakInduct (M := fun s ws => ∀ z, M s ws z) h _ _ _ _ h
  · intro z
    exact stop
  · intro s  xs zs  eq tail ih z
    exact perm eq tail (ih tail)
  · intro s  a  rest  save tail ih z
    exact one save tail (ih tail)
  · intro s  a b  rest  op ka kb tail ih z
    exact two op ka kb tail (ih tail)


theorem mass_cons {R} (a : Wire R) (xs) : mass (a::xs)=cost a + mass xs := by
  simp [mass]

theorem mass_kept {R} (a : Wire R) (xs) (k : Bool) : mass xs ≤ mass (kept k a xs) := by
  cases k <;> simp [kept,mass_cons]

theorem inv_constant {R} {a : Wire R} (h : Constant a) : Constant (inv a) := by
  obtain ⟨v,rfl⟩ := h
  exact ⟨!v,rfl⟩

theorem both_constant {R} {a b : Wire R} (op) (h : Constant a) (g : Constant b) :
    Constant (combine op a b) := by
  obtain ⟨v,rfl⟩ := h
  obtain ⟨w,rfl⟩ := g
  cases op <;> exact ⟨_,rfl⟩

theorem from_constant {R} (op) {a b : Wire R} {bank}
    (h : Constant a ∨ Constant b) (ha : Available bank a) (hb : Available bank b) :
    Available bank (combine op a b) := by
  rcases h with ⟨v,rfl⟩ | ⟨v,rfl⟩
  · cases op <;> cases v
    · exact Or.inr ⟨false, by funext x; simp [combine]⟩
    · simpa [combine] using hb
    · simpa [combine] using hb
    · exact Or.inr ⟨true, by funext x; simp [combine]⟩
  · cases op <;> cases v
    · exact Or.inr ⟨false, by funext x; simp [combine]⟩
    · simpa [combine] using ha
    · simpa [combine] using ha
    · exact Or.inr ⟨true, by funext x; simp [combine]⟩

theorem available_cons {R} {bank v} (w : Wire R) (h : Available bank v) :
    Available (w::bank) v := by
  exact h.elim (fun h => Or.inl (List.mem_cons_of_mem _ h)) Or.inr

theorem extend_one {R} (roots : List (Wire R)) {p bank a} (hp : Reach roots p bank)
    (ha : Available bank a) :
    ∃ q next, Reach roots q next ∧ Available next (inv a) ∧
        (∀ v, Available bank v → Available next v) ∧ q+cost a ≤ p+1+cost (inv a) := by
  classical
  by_cases c : Constant a
  · exact ⟨p,bank,hp,Or.inr (inv_constant c),fun _ h => h,by simp [cost,c,inv_constant c]⟩
  · exact ⟨p+1,_,Reach.one hp ha,Or.inl (by simp),fun _ h => available_cons _ h,by simp [cost,c]⟩

theorem extend_two {R} (roots : List (Wire R)) {p bank a b} (op) (hp : Reach roots p bank)
    (ha : Available bank a) (hb : Available bank b) :
    ∃ q next, Reach roots q next ∧ Available next (combine op a b) ∧
        (∀ v, Available bank v → Available next v) ∧
        q+cost a+cost b ≤ p+1+cost (combine op a b) := by
  classical
  by_cases c : Constant a ∨ Constant b
  · refine ⟨p,bank,hp,from_constant op c ha hb,fun _ h => h,?_⟩
    by_cases ca : Constant a <;> by_cases cb : Constant b
    · simp [cost,ca,cb,both_constant op ca cb]
    · simp [cost,ca,cb]
    · simp [cost,ca,cb]
    · exact False.elim (c.elim ca cb)
  · have ca : ¬Constant a := fun h => c (Or.inl h)
    have cb : ¬Constant b := fun h => c (Or.inr h)
    exact ⟨p+1,_,Reach.two op hp ha hb,Or.inl (by simp),fun _ h => available_cons _ h,
      by simp [cost,ca,cb]⟩

theorem mem_kept {α : Type} {k : Bool} {x a : α} {xs} (h : x ∈ kept k a xs) :
    x=a ∨ x∈xs := by cases k <;> simp_all [kept]

theorem contraction {R} {goal : Wire R} (nc : ¬Constant goal) {s ws}
    (h : Run goal s ws) (roots : List (Wire R)) {p bank}
    (hp : Reach roots p bank) (hs : supply bank ws) :
    ∃ q next, Reach roots q next ∧ Available next goal ∧ q+mass ws ≤ p+s := by
  classical
  induction h using Run.induct generalizing p bank with
  | stop =>
    exact ⟨p,bank,hp,hs _ (by simp),by simp [mass,cost,nc]⟩
  | perm eq _ ih =>
    have hsub : supply bank _ := fun v hv => hs v (eq.mem_iff.mp hv)
    obtain ⟨q,W,hW,hv,hl⟩ := ih hp hsub
    exact ⟨q,W,hW,hv,by simpa only [mass,←(eq.map cost).sum_eq] using hl⟩
  | @one s a rest save _ ih =>
    obtain ⟨r,T,hT,hz,inc,le⟩ := extend_one roots hp (hs a (by simp))
    have ht : supply T (inv a :: kept save a rest) := by
      intro v h
      rcases List.mem_cons.mp h with rfl | hh
      · exact hz
      · exact inc v (hs v (List.mem_cons.mpr (mem_kept hh)))
    obtain ⟨q,W,hW,hv,hl⟩ := ih hT ht
    have hlen := mass_kept a rest save
    rw [mass_cons] at hl ⊢
    exact ⟨q,W,hW,hv,by omega⟩
  | @two s a b rest op ka kb _ ih =>
    obtain ⟨r,T,hT,hz,inc,le⟩ := extend_two roots op hp (hs a (by simp)) (hs b (by simp))
    have ht : supply T (combine op a b :: kept ka a (kept kb b rest)) := by
      intro v h
      rcases List.mem_cons.mp h with rfl | hh
      · exact hz
      · apply inc v
        apply hs
        rcases mem_kept hh with rfl | hh
        · simp
        · exact List.mem_cons_of_mem _ (List.mem_cons.mpr (mem_kept hh))
    obtain ⟨q,W,hW,hv,hl⟩ := ih hT ht
    have hlen := mass_kept a (kept kb b rest) ka
    have hlen' := mass_kept b rest kb
    rw [mass_cons] at hl
    refine ⟨q,W,hW,hv,?_⟩
    rw [mass_cons,mass_cons]
    omega

def restrictRows {R S : Type} (rows : S → R) (a : Wire R) : Wire S :=
  fun r => a (rows r)

theorem restrict_kept {R S : Type} (rows : S → R) (k : Bool) (a : Wire R) (ws) :
    (kept k a ws).map (restrictRows rows) =
    kept k (restrictRows rows a) (ws.map (restrictRows rows)) := by
  cases k <;> simp [kept]

theorem restrict_run {R S : Type} (rows : S → R) {goal s ws} (h : Run goal s ws) :
    Run (restrictRows rows goal) s (ws.map (restrictRows rows)) := by
  induction h using Run.induct with
  | stop => exact Run.stop
  | perm p _ ih => exact Run.perm (p.map _) ih
  | one save _ ih =>
    simp only [List.map_cons,restrict_kept] at ih ⊢
    exact Run.one save ih
  | two op ka kb _ ih =>
    simp only [List.map_cons,restrict_kept] at ih ⊢
    cases op
    · exact Run.two false ka kb ih
    · exact Run.two true ka kb ih

theorem projected_bound {R S : Type} (rows : S → R) {goal s ws} (h : Run goal s ws)
    (nc : ¬Constant (restrictRows rows goal)) {roots : List (Wire S)} {p bank L}
    (hp : Reach roots p bank) (hs : supply bank (ws.map (restrictRows rows)))
    (hl : ∀ q bs, Reach roots q bs → Available bs (restrictRows rows goal) → L ≤ q) :
    L + mass (ws.map (restrictRows rows)) ≤ p+s := by
  obtain ⟨q,bs,hq,ht,hle⟩ := contraction nc (restrict_run rows h) roots hp hs
  have hqle := hl q bs hq ht
  omega


abbrev Row := Fin 512
def observe (a : Sig) : Wire Row := fun r => bit r a
def table (f : Wire Row) : Sig :=
  (BitVec.ofBoolListLE (List.ofFn f)).cast (List.length_ofFn)

theorem bit_table (f : Wire Row) (r : Row) : bit r (table f) = f r := by
  simp only [bit,table,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]; simp [r.isLt]

theorem table_observe (v : Sig) : table (observe v) = v := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  exact bit_table (observe v) ⟨j,hj⟩

theorem observe_table (f : Wire Row) : observe (table f) = f := by
  funext r
  exact bit_table f r

theorem obs_neg (a : Sig) : observe (neg a) = inv (observe a) := by
  funext r
  exact bit_neg _ _

theorem obs_bin (d : Bool) (a b : Sig) :
    observe (bin d a b) = combine d (observe a) (observe b) := by
  funext r
  cases d <;> exact bit_bin _ _ _ _

theorem map_kept {α β : Type} (f : α → β) (d : Bool) (a : α) (l : List α) :
    (kept d a l).map f = kept d (f a) (l.map f) := by cases d <;> rfl

theorem kept_nd {α : Type} (k : Bool) (a : α) (l : List α)
    (hn : l.Nodup) (ha : a ∉ l) : (kept k a l).Nodup := by cases k <;> simp [kept,hn,ha]

theorem kept_fin (k : Bool) (a : Sig) (l : List Sig) :
    (kept k a l).toFinset = if k then insert a l.toFinset else l.toFinset := by
  cases k <;> simp [kept]

theorem list_run {T : Sig} {k u S} (h : Live T k u S) (v : List Sig)
    (hv : v.Nodup) (eqv : v.toFinset = S) : Run (observe T) k (v.map observe) := by
  classical
  induction h using Live.induct generalizing v with
  | stop hp =>
    have eq : [T].Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp) hv
      simpa [eqv]
    exact Run.perm (eq.map _) Run.stop
  | @unary k u U a ha fresh _ ih =>
    let rest := (U.erase a).toList
    let save := decide (a ∈ U)
    let tail := kept save a rest
    have er : rest.toFinset = U.erase a := by simp [rest]
    have hm : a ∉ rest := by simp [rest]
    have hr : rest.Nodup := Finset.nodup_toList _
    have ht : tail.toFinset = U := by
      rw [show tail=kept save a rest by rfl,kept_fin,er]
      by_cases hh : a ∈ U <;> simp [save,hh]
    have nd := kept_nd save a rest hr hm
    have hf : neg a ∉ tail := by
      intro hz
      exact fresh (Finset.mem_insert_of_mem (ht ▸ List.mem_toFinset.mpr hz))
    have progress := ih (neg a::tail) (List.nodup_cons.mpr ⟨hf,nd⟩) (by simp [ht])
    rw [List.map_cons,map_kept,obs_neg] at progress
    have perm : (a::rest).Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (List.nodup_cons.mpr ⟨hm,hr⟩) hv
      simp [er,eqv]
    exact Run.perm (perm.map _) (Run.one save progress)
  | @binary k u U a b d ha hb hab fresh _ ih =>
    let rest := ((U.erase a).erase b).toList
    let ka := decide (a ∈ U)
    let kb := decide (b ∈ U)
    let mid := kept kb b rest
    let tail := kept ka a mid
    have er : rest.toFinset = (U.erase a).erase b := by simp [rest]
    have ar : a ∉ rest := by simp [rest]
    have br : b ∉ rest := by simp [rest]
    have hr : rest.Nodup := Finset.nodup_toList _
    have bm := kept_nd kb b rest hr br
    have am : a ∉ mid := by cases h : kb <;> simp [mid,kept,h,hab,ar]
    have nd := kept_nd ka a mid bm am
    have ht : tail.toFinset = U := by
      change (kept ka a (kept kb b rest)).toFinset = U
      rw [kept_fin,kept_fin,er]
      ext j
      by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> by_cases aj : j=a <;>
        by_cases bj : j=b <;> simp_all [ka,kb]
    have hf : bin d a b ∉ tail := by
      intro hz
      exact fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ht ▸ List.mem_toFinset.mpr hz)))
    have progress := ih (bin d a b::tail) (List.nodup_cons.mpr ⟨hf,nd⟩) (by simp [ht])
    change Run _ _ ((bin d a b::kept ka a (kept kb b rest)).map observe) at progress
    rw [List.map_cons,map_kept,map_kept,obs_bin] at progress
    have perm : (a::b::rest).Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp [hab,ar,br,hr]) hv
      ext j
      by_cases ja : j=a <;> by_cases jb : j=b <;> simp_all [er]
    exact Run.perm (perm.map _) (Run.two d ka kb progress)


theorem table_inv (f : Wire Row) : table (inv f) = neg (table f) := by
  rw [←table_observe (neg (table f)),obs_neg,observe_table]

theorem table_bin (d : Bool) (f g : Wire Row) :
    table (combine d f g) = bin d (table f) (table g) := by
  rw [←table_observe (bin d (table f) (table g)),obs_bin,observe_table,observe_table]

theorem available_rep {bank : List (Wire Row)} {a} (h : Available bank a) :
    represented (bank.map table) (table a) := by
  rcases h with hm | ⟨b,rfl⟩
  · exact Or.inl (List.mem_map_of_mem hm)
  · apply Or.inr
    cases b
    · have z : table (fun _ => false) = zero := by
        apply BitVec.eq_of_getLsbD_eq
        intro j hj
        exact (bit_table _ ⟨j,hj⟩).trans (bit_zero ⟨j,hj⟩).symm
      exact fun hp => hp.1 z
    · have z : table (fun _ => true) = one := by
        apply BitVec.eq_of_getLsbD_eq
        intro j hj
        exact (bit_table _ ⟨j,hj⟩).trans (bit_one ⟨j,hj⟩).symm
      exact fun hp => hp.2 z

theorem inv_rep {w a} (ha : represented w a) :
    represented w (neg a) ∨ witness w (neg a) := by
  rcases operand_cases ha with rfl | rfl | ⟨hm,hp⟩
  · exact Or.inl (Or.inr fun h => h.2 neg_laws.1)
  · exact Or.inl (Or.inr fun h => h.1 neg_laws.2)
  · exact Or.inr (Or.inl ⟨a,hm,hp,rfl⟩)

theorem pull_cons {w : List Sig} {z : Sig} {T k t S} (h : Live T k t S)
    (hz : represented w z ∨ witness w z) (hs : ∀ a ∈ S, a ∈ z::w) :
    ∃ k' t' S', k' ≤ k+1 ∧ Live T k' t' S' ∧ ∀ a ∈ S', a ∈ w := by
  apply pull_gate h hz
  intro a hm
  simpa [or_comm] using hs a hm

theorem reach_live_sub {roots : List (Wire Row)} {p bank}
    (h : Reach roots p bank) {T k t S} (run : Live T k t S)
    (sub : ∀ a ∈ S, a ∈ bank.map table) :
    ∃ l v U, l ≤ p+k ∧ Live T l v U ∧ ∀ a ∈ U, a ∈ roots.map table := by
  induction h using Reach.induct generalizing k t S with
  | start => exact ⟨k,t,S,by omega,run,sub⟩
  | @one p bank a h ha ih =>
    rw [List.map_cons,table_inv] at sub
    obtain ⟨k',t',S',hk,run',sub'⟩ := pull_cons run (inv_rep (available_rep ha)) sub
    obtain ⟨l,v,U,hl,hr,hs⟩ := ih run' sub'
    exact ⟨l,v,U,by omega,hr,hs⟩
  | @two p bank a b d h ha hb ih =>
    rw [List.map_cons,table_bin] at sub
    obtain ⟨k',t',S',hk,run',sub'⟩ := pull_cons run (bin_rep d (available_rep ha) (available_rep hb)) sub
    obtain ⟨l,v,U,hl,hr,hs⟩ := ih run' sub'
    exact ⟨l,v,U,by omega,hr,hs⟩

theorem reach_live {roots : List Sig} {p bank T} (hp : proper T)
    (h : Reach (roots.map observe) p bank) (hit : Available bank (observe T)) :
    ∃ k t S, k ≤ p ∧ Live T k t S ∧ ∀ a ∈ S, a ∈ roots := by
  have hm := available_rep hit
  rw [table_observe] at hm
  have mem := hm.resolve_right (fun hn => hn hp)
  obtain ⟨l,v,U,hl,hr,hs⟩ := reach_live_sub h (Live.stop hp) (by simpa using mem)
  refine ⟨l,v,U,by omega,hr,?_⟩
  simpa [List.map_map,Function.comp_def,table_observe] using hs

theorem live_row_difference {T k t S} (h : Live T k t S) {r s : Row}
    (diff : bit r T ≠ bit s T) : ∃ a ∈ S, bit r a ≠ bit s a := by
  induction h using Live.induct with
  | stop hp => exact ⟨_,by simp,diff⟩
  | @unary k t U a hp hf _ ih =>
    obtain ⟨v,hv,hd⟩ := ih
    rcases Finset.mem_insert.mp hv with rfl | hu
    · refine ⟨a,by simp,?_⟩
      exact fun he => hd (by rw [bit_neg,bit_neg,he])
    · exact ⟨v,Finset.mem_insert_of_mem hu,hd⟩
  | @binary k t U a b d ha hb hab hf _ ih =>
    obtain ⟨v,hv,hd⟩ := ih
    rcases Finset.mem_insert.mp hv with rfl | hu
    · by_cases aeq : bit r a = bit s a
      · refine ⟨b,by simp,?_⟩
        intro beq
        exact hd (by rw [bit_bin,bit_bin,aeq,beq])
      · exact ⟨a,by simp,aeq⟩
    · exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu),hd⟩

theorem raw_required {T k t S} (h : Live T k t S) (roots : List Sig) (a : Sig)
    (sub : ∀ v ∈ S, v ∈ roots) (r s : Row) (diff : bit r T ≠ bit s T)
    (isolated : ∀ v ∈ roots, v ≠ a → bit r v = bit s v) : a ∈ S := by
  obtain ⟨v,hv,hd⟩ := live_row_difference h diff
  by_cases veq : v=a
  · simpa [veq] using hv
  · exact False.elim (hd (isolated v (sub v hv) veq))

def inputs : List Sig := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000]
def graph : Sig := 0xfffffffffffffffffffffffffffafff8ffffffffffffffffffffffffffeaffc8fffffffffffefcfcfffffffffffaf8f8ffeefeeeffeefcccffeafaeaffeaf8c8
def seed : Sig := 0x88888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888

def sample (r : Row) (j : Fin 9) := bit r (inputs.getD j.val zero)
def edge (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
  (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) ||
  (x 6 && x 8) || (x 8 && x 5)
theorem edge_table : ∀ r : Row, bit r graph = edge (sample r) := by decide +kernel
theorem seed_table : ∀ r : Row, bit r seed = (sample r 0 && sample r 1) := by decide +kernel
theorem graph_proper : proper graph := by unfold proper; decide +kernel
theorem seed_nonzero : seed ≠ zero := by decide +kernel
theorem input_list : List.ofFn (fun j : Fin 9 => inputs.getD j.val zero) = inputs := rfl
theorem sampled (r : Row) : List.ofFn (sample r) = inputs.map (bit r) := by
  rw [←input_list]
  rw [List.map_ofFn]
  rfl

theorem table_eval (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (i : Nat) (r : Row) : bit r ((execute C.gates inputs).getD i zero) =
      (C.wires (List.ofFn (sample r))).getD i false := by
  rw [←b_read,execute_bits _ _ _ (fun g hg => (h g hg).1),sampled]
  rfl

theorem exec_extends (gs : List Gate) (ws : List Sig) : ∃ l, execute gs ws = ws ++ l := by
  induction gs generalizing ws with
  | nil => exact ⟨[],by simp [execute]⟩
  | cons g gs ih =>
    obtain ⟨l,hl⟩ := ih (ws++[gv ws g])
    exact ⟨gv ws g::l,by simpa [execute,List.append_assoc] using hl⟩

def neighbor (i : Fin 9) : Nat := [4,2,1,2,3,0,1,2,3].getD i.val 0
def absentRow (i : Fin 9) : Row := Fin.ofNat 512 (1 <<< neighbor i)
def presentRow (i : Fin 9) : Row := Fin.ofNat 512 ((1 <<< i.val) ||| (1 <<< neighbor i))

theorem seed_witness : ∀ i : Fin 9,
    (bit (absentRow i) graph != bit (presentRow i) graph) &&
    ((inputs++[seed]).all fun w => w == inputs.getD i.val zero ||
      bit (absentRow i) w == bit (presentRow i) w) = true := by decide +kernel

theorem all_roots {k t S} (h : Live graph k t S) (sub : ∀ v ∈ S, v ∈ inputs++[seed]) :
    S=inputs.toFinset ∨ S=(inputs++[seed]).toFinset := by
  have all (i : Fin 9) : inputs.getD i.val zero ∈ S := by
    have cut := seed_witness i
    simp only [Bool.and_eq_true,Bool.not_eq_true',bne_iff_ne,List.all_eq_true,
      Bool.or_eq_true,beq_iff_eq,decide_eq_true_eq] at cut
    apply raw_required h _ _ sub (absentRow i) (presentRow i) cut.1
    exact fun v hv hne => (cut.2 v hv).resolve_left hne
  have needed : inputs.toFinset ⊆ S := by
    intro v hv
    have hm := List.mem_toFinset.mp hv
    rw [←input_list,List.mem_ofFn] at hm
    obtain ⟨i,rfl⟩ := hm
    exact all i
  by_cases hseed : seed ∈ S
  · right
    ext w
    constructor
    · exact fun hw => List.mem_toFinset.mpr (sub w hw)
    · intro hw
      have hx := List.mem_toFinset.mp hw
      simp only [List.mem_append,List.mem_singleton] at hx
      exact hx.elim (fun h => needed (List.mem_toFinset.mpr h)) (fun e => e ▸ hseed)
  · left
    exact Finset.Subset.antisymm (fun w hw => by
      have hx := sub w hw
      simp only [List.mem_append,List.mem_singleton] at hx
      rcases hx with hin | rfl
      · exact List.mem_toFinset.mpr hin
      · exact False.elim (hseed hw)) needed

theorem initial_live (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (first : ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 && y 1))
    (computes : PEqualNP.MetaComplexity.circuitFun 9 C = edge) (small : C.size ≤ 15) :
    ∃ k t, k ≤ 14 ∧ (Live graph k t inputs.toFinset ∨ Live graph k t (inputs++[seed]).toFinset) := by
  have headEq : (execute C.gates inputs).getD 9 zero = seed := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    exact (table_eval C legal 9 r).trans ((first (sample r)).trans (seed_table r).symm)
  have goalEq : (execute C.gates inputs).getD C.output zero = graph := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    exact (table_eval C legal C.output r).trans ((congrFun computes (sample r)).trans (edge_table r).symm)
  have out := get_rep (execute C.gates inputs) C.output
  rw [goalEq] at out
  have targetIn := out.resolve_right (fun hn => hn graph_proper)
  cases hgs : C.gates with
  | nil =>
    rw [hgs] at headEq
    exact False.elim (seed_nonzero headEq.symm)
  | cons g gs =>
    have eq0 : gv inputs g = seed := by
      rw [hgs] at headEq
      change (execute gs (inputs++[gv inputs g])).getD 9 zero = seed at headEq
      obtain ⟨l,hl⟩ := exec_extends gs (inputs++[gv inputs g])
      rw [hl] at headEq
      exact headEq
    rw [hgs] at targetIn
    change graph ∈ execute gs (inputs++[gv inputs g]) at targetIn
    rw [eq0] at targetIn
    have tailLegal : ∀ gate ∈ gs, gate.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ gate.inputs.length≤2 := by
      intro gate hg
      apply legal
      rw [hgs]
      exact List.mem_cons_of_mem _ hg
    obtain ⟨k,t,S,hk,run,hs⟩ := extract gs _ tailLegal graph_proper targetIn
    have len : gs.length+1 ≤ 15 := by simpa [Circuit.size,hgs] using small
    refine ⟨k,t,by omega,?_⟩
    rcases all_roots run hs with h | h
    · exact Or.inl (h ▸ run)
    · exact Or.inr (h ▸ run)


def rename (f : Row → Row) (a : Sig) := table fun r => bit (f r) a
theorem bit_rename (f : Row → Row) (a : Sig) (r : Row) :
    bit r (rename f a) = bit (f r) a := bit_table _ _
theorem observe_rename (f : Row → Row) (a : Sig) :
    observe (rename f a) = restrictRows f (observe a) := by funext r; exact bit_rename f a r
theorem rename_neg (f : Row → Row) (a : Sig) : rename f (neg a) = neg (rename f a) := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  change bit ⟨j,hj⟩ (rename f (neg a)) = bit ⟨j,hj⟩ (neg (rename f a))
  rw [bit_rename,bit_neg,bit_neg,bit_rename]
theorem rename_bin (f : Row → Row) (d : Bool) (a b : Sig) :
    rename f (bin d a b) = bin d (rename f a) (rename f b) := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  change bit ⟨j,hj⟩ (rename f (bin d a b)) = bit ⟨j,hj⟩ (bin d (rename f a) (rename f b))
  rw [bit_rename,bit_bin,bit_bin,bit_rename,bit_rename]
theorem rename_inj (f : Row → Row) (onto : Function.Surjective f) :
    Function.Injective (rename f) := by
  intro a b h
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  obtain ⟨r,hr⟩ := onto ⟨j,hj⟩
  have he := congrArg (bit r) h
  change bit ⟨j,hj⟩ a = bit ⟨j,hj⟩ b
  rw [bit_rename,bit_rename,hr] at he
  exact he
theorem rename_constants (f : Row → Row) : rename f zero = zero ∧ rename f one = one := by
  constructor <;> apply BitVec.eq_of_getLsbD_eq <;> intro j hj
  · exact (bit_rename f zero ⟨j,hj⟩).trans ((bit_zero _).trans (bit_zero ⟨j,hj⟩).symm)
  · exact (bit_rename f one ⟨j,hj⟩).trans ((bit_one _).trans (bit_one ⟨j,hj⟩).symm)
theorem live_rename {T k t S} (h : Live T k t S) (f : Row → Row) (onto : Function.Surjective f) :
    Live (rename f T) k t (S.image (rename f)) := by
  have inj := rename_inj f onto
  obtain ⟨fz,fo⟩ := rename_constants f
  have pp (v) (p : proper v) : proper (rename f v) :=
    ⟨fun e => p.1 (inj (e.trans fz.symm)),fun e => p.2 (inj (e.trans fo.symm))⟩
  induction h using Live.induct with
  | stop hp => simpa using Live.stop (pp _ hp)
  | @unary k t U a hp hf _ ih =>
    have fresh : rename f (neg a) ∉ (insert a U).image (rename f) := by
      intro hm
      obtain ⟨v,hv,eq⟩ := Finset.mem_image.mp hm
      exact hf (inj eq ▸ hv)
    simp only [Finset.image_insert,rename_neg] at fresh ih ⊢
    exact Live.unary (pp _ hp) fresh ih
  | @binary k t U a b d ha hb hab hf _ ih =>
    have fresh : rename f (bin d a b) ∉ (insert a (insert b U)).image (rename f) := by
      intro hm
      obtain ⟨v,hv,eq⟩ := Finset.mem_image.mp hm
      exact hf (inj eq ▸ hv)
    simp only [Finset.image_insert,rename_bin] at fresh ih ⊢
    exact Live.binary (pp _ ha) (pp _ hb) (fun hh => hab (inj hh)) fresh ih

theorem mono_row_difference {T k t S} (h : Live T k t S) (none : t=0) {r s : Row}
    (pos : bit r T = true) (negRow : bit s T = false) :
    ∃ a ∈ S, bit r a = true ∧ bit s a = false := by
  induction h using Live.induct with
  | stop hp => exact ⟨_,by simp,pos,negRow⟩
  | unary _ _ _ _ => omega
  | @binary k t U a b d ha hb hab hf _ ih =>
    obtain ⟨v,hv,hp,hn⟩ := ih none
    rcases Finset.mem_insert.mp hv with rfl | hu
    · rw [bit_bin] at hp hn
      cases d <;> cases p : bit r a <;> cases q : bit s a <;>
        cases u : bit r b <;> cases z : bit s b <;> simp_all
    · exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu),hp,hn⟩

def Lower (roots : List Sig) (T : Sig) (L : Nat) : Prop :=
  ∀ p bank, Reach (roots.map observe) p bank → Available bank (observe T) → L ≤ p

def Impossible (T : Sig) (cap : Nat) (S : Finset Sig) : Prop :=
  ∀ k t, k ≤ cap → ¬Live T k t S

def Essential (T : Sig) (roots : List Sig) (a : Sig) : Prop :=
  ∃ r s : Row, bit r T ≠ bit s T ∧ ∀ v ∈ roots, v ≠ a → bit r v = bit s v

theorem lower_impossible {roots T L} (hp : proper T)
    (essential : ∀ a ∈ roots, Essential T roots a)
    (noRun : Impossible T L roots.toFinset) : Lower roots T (L+1) := by
  intro p bank h ha
  obtain ⟨k,t,S,hk,run,hs⟩ := reach_live hp h ha
  have he : roots.toFinset = S := by
    ext a
    rw [List.mem_toFinset]
    refine ⟨fun hm => ?_,hs a⟩
    obtain ⟨r,s,hd,iso⟩ := essential _ hm
    exact raw_required run roots a hs r s hd iso
  by_contra! small
  exact noRun k t (by omega) (he.symm ▸ run)

theorem observe_proper {v : Sig} (hv : proper v) : ¬Constant (observe v) := by
  rintro ⟨b,h⟩
  have hr : represented ([] : List Sig) v := by
    have avail : Available ([] : List (Wire Row)) (observe v) := Or.inr ⟨b,h⟩
    simpa only [List.map_nil,table_observe] using available_rep avail
  exact (hr.resolve_left (by simp)) hv

theorem mass_append {R} (a b : List (Wire R)) : mass (a++b) = mass a + mass b := by
  simp [mass]
theorem mass_constants {R} (xs : List (Wire R)) (hc : ∀ x ∈ xs, Constant x) :
    mass xs = xs.length := by
  induction xs with
  | nil => simp [mass]
  | cons a xs ih =>
    have ha := hc a (by simp)
    simp only [mass_cons,List.length_cons,cost,if_pos ha,ih (fun x hx => hc x (by simp [hx]))]
    omega

theorem lower_slice {roots other : List Sig} {T G : Sig} (pT : proper T) (pG : proper G)
    (r : Row → Row) (eq : rename r T = G)
    (covered : ∀ a ∈ roots, Available (other.map observe) (observe (rename r a)))
    (singles : Finset Sig) (necessary : ∀ a ∈ singles, Essential T roots a)
    (constant : ∀ a ∈ singles, Constant (observe (rename r a)))
    (L : Nat) (prior : Lower other G L) : Lower roots T (L + singles.card) := by
  classical
  intro p bank hh ha
  obtain ⟨k,t,S,hk,run,sub⟩ := reach_live pT hh ha
  have subS : singles ⊆ S := by
    intro a hs
    obtain ⟨i,j,hd,hiso⟩ := necessary a hs
    exact raw_required run roots a sub i j hd hiso
  let front := singles.toList ++ (S \ singles).toList
  have nd : front.Nodup := by
    simp only [front,List.nodup_append]
    refine ⟨Finset.nodup_toList _,Finset.nodup_toList _,?_⟩
    intro a ha b hb he
    subst b
    exact (Finset.mem_sdiff.mp (Finset.mem_toList.mp hb)).2 (Finset.mem_toList.mp ha)
  have fe : front.toFinset=S := by ext a; simp [front,Finset.union_sdiff_of_subset subS]
  have run' := list_run run front nd fe
  have gc : restrictRows r (observe T) = observe G := (observe_rename _ _).symm.trans (congrArg observe eq)
  have supp : supply (other.map observe) ((front.map observe).map (restrictRows r)) := by
    intro v hv
    obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
    obtain ⟨a,hmem,rfl⟩ := List.mem_map.mp hm
    rw [←observe_rename]
    exact covered a (sub _ (fe ▸ List.mem_toFinset.mpr hmem))
  have bound := projected_bound r run' (gc ▸ observe_proper pG) Reach.start supp
    (L:=L) (gc ▸ prior)
  have massLo : singles.card ≤ mass ((front.map observe).map (restrictRows r)) := by
    simp only [front,List.map_append,mass_append]
    let xs := (singles.toList.map observe).map (restrictRows r)
    have only : ∀ v ∈ xs, Constant v := by
      intro v hv
      obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
      obtain ⟨a,hmem,rfl⟩ := List.mem_map.mp hm
      rw [←observe_rename]
      exact constant _ (Finset.mem_toList.mp hmem)
    have sz := mass_constants xs only
    simp only [xs,List.length_map,Finset.length_toList] at sz
    change singles.card ≤ mass xs + _
    rw [sz]
    omega
  omega



def childOne (ws : List Sig) (a : Sig) (keep : Bool) : List Sig :=
  neg a :: kept keep a (ws.erase a)
def childTwo (ws : List Sig) (a b : Sig) (d ka kb : Bool) : List Sig :=
  bin d a b :: kept ka a (kept kb b ((ws.erase a).erase b))

theorem erase_fin {l : List Sig} (h : l.Nodup) (a : Sig) : (l.erase a).toFinset = l.toFinset.erase a := by
  ext x
  simp [h.mem_erase_iff]

theorem enum_step {T : Sig} {cap : Nat} {ws : List Sig} (hn : ws.Nodup) (out : T ∉ ws)
    (oneStep : ∀ a ∈ ws, ∀ keep, neg a ∉ ws → proper (neg a) →
      (childOne ws a keep).length ≤ cap →
      Impossible T (cap-1) (childOne ws a keep).toFinset)
    (twoStep : ∀ a ∈ ws, ∀ b ∈ ws, ∀ d ka kb, a ≠ b → bin d a b ∉ ws →
      proper (bin d a b) → (childTwo ws a b d ka kb).length ≤ cap →
      Impossible T (cap-1) (childTwo ws a b d ka kb).toFinset) :
    Impossible T cap ws.toFinset := by
  classical
  intro k t hk h
  generalize he : ws.toFinset = S at h
  induction h using Live.induct with
  | stop hp =>
    have mem : T ∈ ws.toFinset := he.symm ▸ Finset.mem_singleton_self _
    exact out (List.mem_toFinset.mp mem)
  | @unary k t U a ha hf tail _ =>
    have am : a ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
    have fresh : neg a ∉ ws := fun h => hf (he ▸ List.mem_toFinset.mpr h)
    have hz := live_proper tail _ (Finset.mem_insert_self _ _)
    let keep := decide (a ∈ U)
    have er := erase_fin hn a
    have rest : (kept keep a (ws.erase a)).toFinset = U := by
      rw [kept_fin,er,he]
      by_cases hm : a ∈ U <;> simp [keep,hm]
    have nd : (childOne ws a keep).Nodup := by
      have na : a ∉ ws.erase a := hn.not_mem_erase
      have nk := kept_nd keep a (ws.erase a) (hn.erase _) na
      refine List.nodup_cons.mpr ⟨?_,nk⟩
      intro h
      exact hf (Finset.mem_insert_of_mem (rest ▸ List.mem_toFinset.mpr h))
    have eq : (childOne ws a keep).toFinset = insert (neg a) U := by simp [childOne,rest]
    have sc := (live_size tail).2
    have len : (childOne ws a keep).length ≤ cap := by
      rw [←List.toFinset_card_of_nodup nd,eq]
      omega
    exact oneStep a am keep fresh hz len k t (by omega) (eq.symm ▸ tail)
  | @binary k t U a b d ha hb hab hf tail _ =>
    have am : a ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
    have bm : b ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    have fresh : bin d a b ∉ ws := fun h => hf (he ▸ List.mem_toFinset.mpr h)
    have hz := live_proper tail _ (Finset.mem_insert_self _ _)
    let ka := decide (a ∈ U)
    let kb := decide (b ∈ U)
    let rest := (ws.erase a).erase b
    have er : rest.toFinset = (ws.toFinset.erase a).erase b := by
      rw [show rest=(ws.erase a).erase b by rfl,erase_fin (hn.erase _) b,
        erase_fin hn a]
    have ke : (kept ka a (kept kb b rest)).toFinset = U := by
      rw [kept_fin,kept_fin,er,he]
      ext j
      by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> by_cases ja : j=a <;>
        by_cases jb : j=b <;> simp_all [ka,kb]
    have rn : rest.Nodup := (hn.erase _).erase _
    have ar : a ∉ rest := fun h => (hn.not_mem_erase) (List.mem_of_mem_erase h)
    have br : b ∉ rest := (hn.erase a).not_mem_erase
    have nk := kept_nd kb b rest rn br
    have ax : a ∉ kept kb b rest := by cases kb <;> simp [kept,ar,hab]
    have nd : (childTwo ws a b d ka kb).Nodup := by
      refine List.nodup_cons.mpr ⟨?_,kept_nd ka a _ nk ax⟩
      intro h
      exact hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ke ▸ List.mem_toFinset.mpr h)))
    have eq : (childTwo ws a b d ka kb).toFinset = insert (bin d a b) U := by
      change (bin d a b::kept ka a (kept kb b rest)).toFinset = _
      simp [ke]
    have sc := (live_size tail).2
    have len : (childTwo ws a b d ka kb).length ≤ cap := by
      rw [←List.toFinset_card_of_nodup nd,eq]
      omega
    exact twoStep a am b bm d ka kb hab fresh hz len k t (by omega) (eq.symm ▸ tail)

def Sep (T : Sig) (width : Nat) (pos negRow : Fin width → Row)
    (asig : Sig → BitVec width × BitVec width) : Prop :=
  (∀ i, bit (pos i) T = true ∧ bit (negRow i) T = false) ∧
  ∀ w i, (asig w).1.getLsbD i.val = bit (pos i) w ∧
    (asig w).2.getLsbD i.val = bit (negRow i) w

def column {n} (oriented : Bool) (s : BitVec n × BitVec n) : BitVec n :=
  if oriented then s.1 &&& ~~~s.2 else s.1 ^^^ s.2

def covered {n} (oriented : Bool) (sig : Sig → BitVec n × BitVec n) : List Sig → BitVec n
  | [] => 0
  | a::ws => column oriented (sig a) ||| covered oriented sig ws

theorem covered_bit {n : Nat} {oriented : Bool} {sig : Sig → BitVec n × BitVec n} {ws : List Sig} {i : Fin n} :
    (covered oriented sig ws).getLsbD i.val = true ↔
    ∃ a ∈ ws, (column oriented (sig a)).getLsbD i.val = true := by
  induction ws with
  | nil => simp [covered]
  | cons a ws ih =>
    simp only [covered,BitVec.getLsbD_or,Bool.or_eq_true,ih,List.mem_cons,exists_eq_or_imp]

theorem cover_sound {T k t S} (h : Live T k t S) {ws : List Sig} (he : ws.toFinset=S)
    {width : Nat} {r s : Fin width → Row} {sig} (correct : Sep T width r s sig)
    (oriented : Bool) (zeroNot : oriented=true → t=0) :
    covered oriented sig ws = BitVec.allOnes width := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  let i : Fin width := ⟨j,hj⟩
  have yes := (correct.1 i).1
  have no := (correct.1 i).2
  rw [BitVec.getLsbD_allOnes]; simp only [hj,decide_true]
  apply (covered_bit (i:=i)).mpr
  cases oriented with
  | false =>
    obtain ⟨a,ha,hd⟩ := live_row_difference h (show bit (r i) T ≠ bit (s i) T by simp [yes,no])
    refine ⟨a,List.mem_toFinset.mp (he.symm ▸ ha),?_⟩
    simp only [column,Bool.false_eq_true,ite_false,BitVec.getLsbD_xor,(correct.2 a i).1,(correct.2 a i).2]
    cases hx : bit (r i) a <;> cases hy : bit (s i) a <;> simp_all
  | true =>
    obtain ⟨a,ha,hp,hn⟩ := mono_row_difference h (zeroNot rfl) yes no
    refine ⟨a,List.mem_toFinset.mp (he.symm ▸ ha),?_⟩
    simp only [column,ite_true,BitVec.getLsbD_and,BitVec.getLsbD_not,i.isLt,decide_true,
      Bool.true_and,(correct.2 a i).1,(correct.2 a i).2,hp,hn,Bool.not_false,Bool.and_self]

theorem cover_required {T cap ws k t} (h : Live T k t (List.toFinset ws))
    (hk : k ≤ cap) (hn : ws.Nodup) {n : Nat} {r s : Fin n → Row} {sig}
    (correct : Sep T n r s sig) :
    covered (decide (ws.length=cap+1)) sig ws = BitVec.allOnes n := by
  apply cover_sound h rfl correct
  intro hh
  have eq := of_decide_eq_true hh
  have bound := (live_size h).2
  rw [List.toFinset_card_of_nodup hn] at bound
  omega



def Slice (raw : List Sig) (T d : Sig) (L : Nat) : Prop :=
  ∃ (f : Row → Row) (roots : List Sig), (∀ r, bit (f r) d = true) ∧
    (∀ a ∈ raw, Available (roots.map observe) (restrictRows f (observe a))) ∧
    ¬Constant (restrictRows f (observe T)) ∧
    ∀ p bank, Reach (roots.map observe) p bank → Available bank (restrictRows f (observe T)) → L ≤ p

def masked (d a : Sig) := a &&& d
def availableB (d : Sig) (pool : List Sig) (a : Sig) :=
  let m := masked d a
  m == zero || m == d || (pool.map (masked d)).any (fun v => v==m)

theorem masked_eq {f : Row → Row} {d a b : Sig} (dom : ∀ r, bit (f r) d = true)
    (eq : masked d a = masked d b) :
    restrictRows f (observe a) = restrictRows f (observe b) := by
  funext r
  have h := congrArg (bit (f r)) eq
  change bit (f r) a = bit (f r) b
  simpa only [bit,masked,BitVec.getLsbD_and,show d.getLsbD (f r).val = true from dom r,
    Bool.and_true] using h

theorem masked_zero {f : Row → Row} {d a : Sig} (dom : ∀ r, bit (f r) d = true)
    (eq : masked d a = zero) : restrictRows f (observe a) = fun _ => false := by
  funext r
  have he := congrArg (bit (f r)) eq
  change bit (f r) a = false
  rw [bit_zero] at he
  simpa only [bit,masked,BitVec.getLsbD_and,show d.getLsbD (f r).val = true from dom r,
    Bool.and_true] using he

theorem masked_one {f : Row → Row} {d a : Sig} (dom : ∀ r, bit (f r) d = true)
    (eq : masked d a = d) : restrictRows f (observe a) = fun _ => true := by
  funext r
  have he := congrArg (bit (f r)) eq
  change bit (f r) a = true
  rw [dom r] at he
  simpa only [bit,masked,BitVec.getLsbD_and,show d.getLsbD (f r).val = true from dom r,
    Bool.and_true] using he

def poolSupply (f : Row → Row) (bank : List (Wire Row)) (pool : List Sig) :=
  ∀ a ∈ pool, Available bank (restrictRows f (observe a))

theorem availableB_sound {f : Row → Row} {d a : Sig} {bank pool}
    (dom : ∀ r, bit (f r) d = true) (supplyB : poolSupply f bank pool)
    (check : availableB d pool a = true) : Available bank (restrictRows f (observe a)) := by
  simp only [availableB,List.any_map,Function.comp_def,Bool.or_eq_true,beq_iff_eq,List.any_eq_true] at check
  rcases check with (hz | ho) | ⟨v,hv,he⟩
  · exact Or.inr ⟨false,masked_zero dom hz⟩
  · exact Or.inr ⟨true,masked_one dom ho⟩
  · exact masked_eq dom he ▸ supplyB v hv

abbrev Choice := Nat × Sig × Sig
def choiceVal (c : Choice) :=
  if c.1=2 then neg c.2.1 else bin (c.1==1) c.2.1 c.2.2
def choiceOK (d : Sig) (pool : List Sig) (c : Choice) :=
  availableB d pool c.2.1 && (c.1==2 || availableB d pool c.2.2)

theorem pay_choice {f : Row → Row} {d : Sig} {roots bank pool q}
    (dom : ∀ r, bit (f r) d = true) (hp : Reach roots q bank) (hs : poolSupply f bank pool)
    (c : Choice) (valid : choiceOK d pool c = true) :
    ∃ next, Reach roots (q+1) next ∧ poolSupply f next (choiceVal c :: pool) := by
  have ok : availableB d pool c.2.1 = true ∧ (c.1==2 || availableB d pool c.2.2) = true := by simpa only [choiceOK,Bool.and_eq_true] using valid
  have ha := availableB_sound dom hs ok.1
  let z := restrictRows f (observe (choiceVal c))
  have hz : Reach roots (q+1) (z::bank) := by
    by_cases unary : c.1=2
    · change Reach _ _ (restrictRows f (observe (choiceVal c)) :: _)
      rw [choiceVal,if_pos unary,obs_neg]
      exact Reach.one hp ha
    · have hb : availableB d pool c.2.2 = true := by simpa [unary] using ok.2
      have hz' := Reach.two (c.1==1) hp ha (availableB_sound dom hs hb)
      change Reach _ _ (restrictRows f (observe (choiceVal c)) :: _)
      rw [choiceVal,if_neg unary,obs_bin]
      have comm (b : Bool) (v w : Wire Row) : restrictRows f (combine b v w) = combine b (restrictRows f v) (restrictRows f w) := by cases b <;> rfl
      rw [comm]
      exact hz'
  refine ⟨_,hz,?_⟩
  intro a hm
  rcases List.mem_cons.mp hm with rfl | hm
  · exact Or.inl (by simp [z])
  · exact available_cons _ (hs _ hm)

def makePool (d : Sig) (pool : List Sig) : List Choice → Option (List Sig)
  | [] => some pool
  | c::cs => if choiceOK d pool c then makePool d (choiceVal c::pool) cs else none

theorem makePool_sound {d : Sig} {f : Row → Row} (dom : ∀ r, bit (f r) d = true)
    {roots bank q pool} (hp : Reach roots q bank) (hs : poolSupply f bank pool)
    (cs : List Choice) {result} (ok : makePool d pool cs = some result) :
    ∃ next, Reach roots (q+cs.length) next ∧ poolSupply f next result := by
  induction cs generalizing bank q pool with
  | nil => cases ok; exact ⟨_,hp,hs⟩
  | cons c cs ih =>
    simp only [makePool] at ok
    split at ok
    next h =>
      obtain ⟨next,hr,sh⟩ := pay_choice dom hp hs c h
      obtain ⟨out,hr',sh'⟩ := ih hr sh ok
      exact ⟨out,by simpa [Nat.add_assoc,Nat.add_comm 1] using hr',sh'⟩
    next => contradiction

def isMaskedConstant (d a : Sig) := masked d a == zero || masked d a == d
theorem count_constants {d : Sig} {f : Row → Row} (dom : ∀ r, bit (f r) d = true)
    (ws : List Sig) : ws.countP (isMaskedConstant d) ≤ mass ((ws.map observe).map (restrictRows f)) := by
  classical
  induction ws with
  | nil => simp [mass]
  | cons a ws ih =>
    simp only [List.countP_cons,List.map_cons,mass_cons]
    cases h : isMaskedConstant d a
    · simpa using (Nat.le_add_left _ _ |> ih.trans)
    · have hc : Constant (restrictRows f (observe a)) := by
        have hh : masked d a = zero ∨ masked d a = d := by simpa only [isMaskedConstant,Bool.or_eq_true,beq_iff_eq] using h
        rcases hh with hz | ho
        · exact ⟨false,masked_zero dom hz⟩
        · exact ⟨true,masked_one dom ho⟩
      simpa [cost,hc,Nat.add_comm] using Nat.succ_le_succ ih

def poolCut (d : Sig) (L k p : Nat) (pool ws : List Sig) :=
  decide (k+p < L+ws.countP (isMaskedConstant d)) && ws.all (availableB d pool)

theorem poolCut_sound {raw T d L} (slice : Slice raw T d L) (cs : List Choice)
    {pool ws cap} (built : makePool d raw cs = some pool)
    (nd : ws.Nodup) (cut : poolCut d L cap cs.length pool ws = true) :
    Impossible T cap ws.toFinset := by
  intro k t hk h
  obtain ⟨f,roots,dom,base,nc,lo⟩ := slice
  obtain ⟨bank,hr,hs⟩ := makePool_sound dom (Reach.start (roots:=roots.map observe)) base cs built
  simp only [poolCut,Bool.and_eq_true,decide_eq_true_eq] at cut
  obtain ⟨ineq,all⟩ := cut
  have coveredS : supply bank ((ws.map observe).map (restrictRows f)) := by
    intro v hv
    obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hm
    exact availableB_sound dom hs (List.all_eq_true.mp all a ha)
  have b := projected_bound f (list_run h ws nd rfl) nc hr coveredS lo
  have massLo := count_constants dom ws
  have hu := ineq
  simp only [Nat.zero_add] at b
  omega



abbrev Move := Sig × Sig × Row
def shifted (d r : Row) : Row :=
  if h : r.val < 512-d.val then ⟨d.val+r.val,by omega⟩ else ⟨r.val-(512-d.val),by omega⟩
def backwards (d : Row) : Row := Fin.ofNat 512 (512-d.val)
def rowMove (m : Move) (r : Row) : Row :=
  if bit r m.1 then shifted m.2.2 r else if bit r m.2.1 then shifted (backwards m.2.2) r else r
def mux (m a b : Sig) := (m &&& a) ||| (~~~m &&& b)
def wordMove (m : Move) (a : Sig) :=
  mux m.1 (a.rotateRight m.2.2.val) (mux m.2.1 (a.rotateRight (backwards m.2.2).val) a)

theorem bit_shift (d r : Row) (a : Sig) : bit r (a.rotateRight d.val) = bit (shifted d r) a := by
  unfold bit
  rw [BitVec.getLsbD_rotateRight_of_lt d.isLt]
  by_cases h : r.val < 512-d.val <;> simp [shifted,h,r.isLt]

theorem bool_mux (p x y : Bool) : (p && x || !p && y) = (if p then x else y) := by cases p <;> simp

theorem bit_mux (r : Row) (m a b : Sig) :
    bit r (mux m a b) = if bit r m then bit r a else bit r b := by
  simp only [bit,mux,BitVec.getLsbD_and,BitVec.getLsbD_or,BitVec.getLsbD_not,r.isLt,
    decide_true,Bool.true_and]
  exact bool_mux _ _ _

theorem bit_move (r : Row) (m : Move) (a : Sig) : bit r (wordMove m a) = bit (rowMove m r) a := by
  simp only [wordMove,bit_mux,bit_shift,rowMove]
  cases bit r m.1 <;> cases bit r m.2.1 <;> rfl

def movedRow (ms : List Move) (r : Row) := ms.foldl (fun j m => rowMove m j) r
def movedWord (ms : List Move) (a : Sig) := ms.foldr wordMove a
theorem bit_moved (ms : List Move) (a : Sig) (r : Row) :
    bit r (movedWord ms a) = bit (movedRow ms r) a := by
  induction ms generalizing r with
  | nil => rfl
  | cons m ms ih => exact (bit_move r m _).trans (ih _)
theorem moved_eq_rename (ms : List Move) (a : Sig) : movedWord ms a = rename (movedRow ms) a := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  exact (bit_moved ms a ⟨j,hj⟩).trans (bit_rename _ _ ⟨j,hj⟩).symm

def freeWord (roots : List Sig) (w : Sig) := w==zero || w==one || roots.contains w
theorem freeWord_ok {roots w} (ok : freeWord roots w = true) :
    Available (roots.map observe) (observe w) := by
  simp only [freeWord,Bool.or_eq_true,beq_iff_eq,List.contains_eq_mem,decide_eq_true_eq] at ok
  rcases ok with (rfl | rfl) | hm
  · exact Or.inr ⟨false,funext bit_zero⟩
  · exact Or.inr ⟨true,funext bit_one⟩
  · exact Or.inl (List.mem_map_of_mem hm)

def checkMap (ms : List Move) (raw : List Sig) (T : Sig) (base : List Sig) (G : Sig) :=
  movedWord ms T == G && raw.all (fun a => freeWord base (movedWord ms a))

theorem map_correct {ms raw T base G} (ok : checkMap ms raw T base G = true) :
    rename (movedRow ms) T = G ∧
    ∀ a ∈ raw, Available (base.map observe) (observe (rename (movedRow ms) a)) := by
  simp only [checkMap,Bool.and_eq_true,beq_iff_eq,List.all_eq_true,moved_eq_rename] at ok
  exact ⟨ok.1,fun a ha => freeWord_ok (ok.2 a ha)⟩

theorem lower_map {ms raw T base G L} (ok : checkMap ms raw T base G = true)
    (pT : proper T) (pG : proper G) (hL : Lower base G L) : Lower raw T L := by
  obtain ⟨eq,supp⟩ := map_correct ok
  simpa using lower_slice pT pG (movedRow ms) eq supp ∅ (by simp) (by simp) L hL

theorem slice_correct {ms raw T base G L d} (ok : checkMap ms raw T base G = true)
    (all : movedWord ms d = one) (properG : proper G) (hL : Lower base G L) :
    Slice raw T d L := by
  obtain ⟨eq,supp⟩ := map_correct ok
  have obs : restrictRows (movedRow ms) (observe T) = observe G :=
    (observe_rename _ _).symm.trans (congrArg observe eq)
  refine ⟨movedRow ms,base,?_,?_,?_,?_⟩
  · intro r
    rw [←bit_moved,all,bit_one]
  · intro a ha
    rw [←observe_rename]
    exact supp a ha
  · rw [obs]
    exact observe_proper properG
  · rw [obs]
    exact hL

def witnessB (T : Sig) (roots : List Sig) (a : Sig) (rs : Row × Row) :=
  (bit rs.1 T != bit rs.2 T) &&
  roots.all (fun w => w == a || bit rs.1 w == bit rs.2 w)
theorem witnessB_sound {T roots a rs} (ok : witnessB T roots a rs = true) : Essential T roots a := by
  simp only [witnessB,Bool.and_eq_true,bne_iff_ne,List.all_eq_true,Bool.or_eq_true,beq_iff_eq] at ok
  exact ⟨rs.1,rs.2,ok.1,fun w hw hne => (ok.2 w hw).resolve_left hne⟩

def checkEssential (T : Sig) (raw : List Sig) (xs : List (Sig × Row × Row)) :=
  xs.all (fun a => witnessB T raw a.1 a.2)
theorem essential_ok {T raw xs} (ok : checkEssential T raw xs = true) :
    ∀ a ∈ (xs.map Prod.fst).toFinset, Essential T raw a := by
  intro a ha
  obtain ⟨⟨a,r,s⟩,hm,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
  exact witnessB_sound (List.all_eq_true.mp ok _ hm)

theorem lower_count {raw T} (properT : proper T) (xs : List (Sig × Row × Row))
    (ok : checkEssential T raw xs = true) :
    Lower raw T ((xs.map Prod.fst).toFinset.card-1) := by
  intro p bank hr hit
  obtain ⟨k,t,S,hk,run,sub⟩ := reach_live properT hr hit
  have le : (xs.map Prod.fst).toFinset.card ≤ S.card := by
    apply Finset.card_le_card
    intro a ha
    obtain ⟨r,s,hd,iso⟩ := essential_ok ok a ha
    exact raw_required run raw a sub r s hd iso
  have bound := (live_size run).2
  omega

def checkLift (ms : List Move) (T : Sig) (raw : List Sig) (base : List Sig) (G : Sig)
    (xs : List (Sig × Row × Row)) :=
  checkMap ms raw T base G && checkEssential T raw xs &&
    xs.all (fun a => movedWord ms a.1 == zero || movedWord ms a.1 == one)

theorem lift_ok {ms T raw base G xs L} (ok : checkLift ms T raw base G xs = true)
    (properT : proper T) (properG : proper G) (low : Lower base G L) :
    Lower raw T (L+(xs.map Prod.fst).toFinset.card) := by
  simp only [checkLift,Bool.and_eq_true] at ok
  obtain ⟨eq,supp⟩ := map_correct ok.1.1
  apply lower_slice properT properG _ eq supp _ (essential_ok ok.1.2) _ L low
  intro a ha
  obtain ⟨⟨v,r,s⟩,hm,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
  have hh := List.all_eq_true.mp ok.2 _ hm
  simp only [Bool.or_eq_true,beq_iff_eq,moved_eq_rename] at hh
  rcases hh with h | h
  · rw [h]
    exact ⟨false,funext bit_zero⟩
  · rw [h]
    exact ⟨true,funext bit_one⟩



def selected (m : Nat) : List (Nat × Sig) :=
  (List.range 9).filterMap fun i => if m.testBit i then some (i,inputs.getD i zero) else none
def vars (m : Nat) := (selected m).map Prod.snd
def vertex (m j : Nat) := if m.testBit j then inputs.getD j zero else zero
def graphGoal (m : Nat) : Sig :=
  let x := vertex m
  (x 0 &&& x 1) ||| (x 1 &&& x 2) ||| (x 2 &&& x 3) ||| (x 3 &&& x 4) |||
    (x 4 &&& x 0) ||| (x 0 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 7) |||
    (x 3 &&& x 8) ||| (x 5 &&& x 7) ||| (x 6 &&& x 8) ||| (x 8 &&& x 5)
def cube0 : Nat → Nat
  | 0 => 0xff
  | 1 => 0x55
  | 2 => 0x33
  | 3 => 0x11
  | 4 => 0xf
  | 5 => 0x5
  | 6 => 0x3
  | _ => 0x1
def cube3 : Nat → Nat
  | 0 => 0x101010101010101
  | 1 => 0x1000100010001
  | 2 => 0x10100000101
  | 3 => 0x100000001
  | 4 => 0x1010101
  | 5 => 0x10001
  | 6 => 0x101
  | _ => 0x1
def cube6 : Nat → Nat
  | 0 => 0x10000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001
  | 1 => 0x1000000000000000000000000000000010000000000000000000000000000000100000000000000000000000000000001
  | 2 => 0x100000000000000010000000000000000000000000000000000000000000000010000000000000001
  | 3 => 0x10000000000000000000000000000000000000000000000000000000000000001
  | 4 => 0x1000000000000000100000000000000010000000000000001
  | 5 => 0x100000000000000000000000000000001
  | 6 => 0x10000000000000001
  | _ => 0x1
def subcube (z o : Nat) : Sig :=
  let fixed := z ||| o
  if z &&& o != 0 then zero else
    BitVec.ofNat 512 ((cube0 (fixed &&& 7)*cube3 ((fixed >>> 3) &&& 7)*cube6 ((fixed >>> 6) &&& 7)) <<< o)
def fixRows (z o : Nat) : List Move :=
  (List.range 9).filterMap fun j =>
    let x := inputs.getD j zero
    let step := Fin.ofNat 512 (1 <<< j)
    if z.testBit j then some (zero,x,step)
    else if o.testBit j then some (~~~x,zero,step) else none
def swapRows (v : Nat) : Move :=
  let i := v &&& 15
  let j := v >>> 4
  let a := inputs.getD i zero
  let b := inputs.getD j zero
  let d := (1 <<< j)-(1 <<< i)
  (a &&& ~~~b,b &&& ~~~a,Fin.ofNat 512 d)

def supportPairs (mask : Nat) : List (Sig × Row × Row) :=
  (selected mask).map fun (i,a) => (a,0,Fin.ofNat 512 (1 <<< i))

def graphPairs (m hints : Nat) : List (Sig × Row × Row) :=
  (selected m).map fun (i,a) =>
    let r := 1 <<< ((hints >>> (4*i)) &&& 15)
    (a,Fin.ofNat 512 r,Fin.ofNat 512 (r ||| (1 <<< i)))

def properB (T : Sig) := T != zero && T != one
theorem proper_of (T : Sig) (h : properB T = true) : proper T := by
  simpa only [properB,proper,Bool.and_eq_true,bne_iff_ne] using h
def assertSize (m hints L : Nat) :=
  let xs := graphPairs m hints
  properB (graphGoal m) && checkEssential (graphGoal m) (vars m) xs &&
    decide (L ≤ (xs.map Prod.fst).toFinset.card-1)
theorem size_of {m hints L} (h : assertSize m hints L = true) :
    Lower (vars m) (graphGoal m) L := by
  simp only [assertSize,Bool.and_eq_true,decide_eq_true_eq] at h
  intro p bank hr ha
  exact h.2.trans (lower_count (proper_of _ h.1.1) _ h.1.2 p bank hr ha)

abbrev ColumnInfo := Nat × Nat × Nat × Nat × Nat
def colFree (m z o : Nat) := m ^^^ (m &&& (z ||| o))
def chartGoal (m : Nat) : Sig :=
  if m=1023 then graphGoal m &&& ~~~seed else graphGoal m
def colCheck (m : Nat) (c : ColumnInfo) (prior : Nat → Nat) : Bool :=
  let (z,o,q,s,L) := c
  let ms := fixRows z o
  let free := colFree m z o
  let G := movedWord ms (chartGoal m)
  let xs := supportPairs s
  let count := (xs.map Prod.fst).toFinset.card
  properB G && checkMap ms (vars m) (chartGoal m) (vars free) G &&
    (movedWord ms (subcube z o)==one) &&
    (if q=0 then checkEssential G (vars free) xs && decide (L ≤ count-1)
     else properB (graphGoal q) &&
       checkLift (fixRows (colFree free q 0) 0) G (vars free) (vars q) (graphGoal q) xs &&
       decide (L ≤ prior q+count))

theorem col_sound {m : Nat} (c : ColumnInfo) (prior : Nat → Nat)
    (valid : ∀ q, Lower (vars q) (graphGoal q) (prior q))
    (ok : colCheck m c prior = true) : Slice (vars m) (chartGoal m) (subcube c.1 c.2.1) c.2.2.2.2 := by
  obtain ⟨z,o,q,s,L⟩ := c
  let ms := fixRows z o
  let free := colFree m z o
  let G := movedWord ms (chartGoal m)
  let xs := supportPairs s
  change (((properB G && checkMap ms (vars m) (chartGoal m) (vars free) G) &&
    (movedWord ms (subcube z o)==one)) && _) = true at ok
  simp only [Bool.and_eq_true,beq_iff_eq] at ok
  apply slice_correct ok.1.1.2 ok.1.2 (proper_of _ ok.1.1.1)
  intro p bank hr ha
  have hh := ok.2
  by_cases hq : q=0
  · simp only [colCheck,hq,if_true,Bool.and_eq_true,decide_eq_true_eq] at hh
    exact hh.2.trans (lower_count (proper_of _ ok.1.1.1) xs hh.1 p bank hr ha)
  · simp only [colCheck,hq,if_false,Bool.and_eq_true,decide_eq_true_eq] at hh
    exact hh.2.trans (lift_ok hh.1.2 (proper_of _ ok.1.1.1) (proper_of _ hh.1.1) (valid q) p bank hr ha)

def relabelOK (old rep : Nat) (swaps : List Nat) :=
  properB (graphGoal old) && properB (graphGoal rep) &&
    checkMap (swaps.map swapRows) (vars old) (graphGoal old) (vars rep) (graphGoal rep)
theorem relabel_of {old rep L swaps} (ok : relabelOK old rep swaps = true)
    (h : Lower (vars rep) (graphGoal rep) L) : Lower (vars old) (graphGoal old) L := by
  simp only [relabelOK,Bool.and_eq_true] at ok
  exact lower_map ok.2 (proper_of _ ok.1.1) (proper_of _ ok.1.2) h

def boundsBefore (entries : List (Nat × Nat)) (q : Nat) :=
  ((entries.find? (fun a => a.1 == q)).map Prod.snd).getD 0
theorem before_sound (entries : List (Nat × Nat))
    (sound : ∀ e ∈ entries, Lower (vars e.1) (graphGoal e.1) e.2) (q : Nat) :
    Lower (vars q) (graphGoal q) (boundsBefore entries q) := by
  unfold boundsBefore
  cases h : entries.find? (fun a => a.1 == q) with
  | none => exact fun _ _ _ _ => Nat.zero_le _
  | some e =>
    have he := List.mem_of_find?_eq_some h
    have hit : (fun a : Nat × Nat => a.1 == q) e = true := List.find?_some (p:=fun a : Nat × Nat => a.1 == q) (a:=e) h
    have eq : e.1=q := beq_iff_eq.mp hit
    simpa only [Option.map_some,Option.getD_some,eq] using sound e he


abbrev BoundPool := (Sig) × (Nat) × (Nat) × (List Sig)
def BoundPool.domain (v : BoundPool) : Sig := v.1
def BoundPool.bound (v : BoundPool) : Nat := v.2.1
def BoundPool.paid (v : BoundPool) : Nat := v.2.2.1
def BoundPool.wires (v : BoundPool) : List Sig := v.2.2.2

def ValidPool (raw : List Sig) (T : Sig) (c : BoundPool) :=
  ∃ (f : Row → Row) (roots : List Sig) (bank : List (Wire Row)),
    (∀ r, bit (f r) c.domain = true) ∧ ¬Constant (restrictRows f (observe T)) ∧
    (∀ q ws, Reach (roots.map observe) q ws → Available ws (restrictRows f (observe T)) → c.bound ≤ q) ∧
    Reach (roots.map observe) c.paid bank ∧ poolSupply f bank c.wires ∧ True

theorem build_valid {raw T d lb} (h : Slice raw T d lb) (cs : List Choice) {ws}
    (build : makePool d raw cs = some ws) : ValidPool raw T ⟨d,lb,cs.length,ws⟩ := by
  obtain ⟨f,roots,dom,sup,nc,prior⟩ := h
  obtain ⟨bank,hr,hs⟩ := makePool_sound dom (Reach.start (roots:=roots.map observe)) sup cs build
  exact ⟨f,roots,bank,dom,nc,prior,by simpa [BoundPool.paid] using hr,hs,trivial⟩

theorem valid_exclude {raw T c} (valid : ValidPool raw T c) (k : Nat) (rest : List Sig)
    (choice : Choice) (paid : Bool)
    (known : ∀ a ∈ rest, availableB c.domain c.wires a = true)
    (buy : if paid then choiceOK c.domain c.wires choice = true
       else availableB c.domain c.wires (choiceVal choice) = true)
    (bound : k+c.paid+paid.toNat <
      c.bound+(choiceVal choice :: rest).countP (isMaskedConstant c.domain))
    (nd : (choiceVal choice :: rest).Nodup) :
    Impossible T k (choiceVal choice :: rest).toFinset := by
  intro t num ht run
  obtain ⟨f,roots,bank,dom,nc,lo,hp,hs,_⟩ := valid
  let ws := choiceVal choice::rest
  have done (n : Nat) (out : List (Wire Row)) (reach : Reach (roots.map observe) n out)
      (zs : poolSupply f out (choiceVal choice::rest)) (le : n = c.paid+paid.toNat) : False := by
    have covered : supply out ((ws.map observe).map (restrictRows f)) := by
      intro v hv
      obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
      obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hm
      exact zs _ ha
    have b := projected_bound f (list_run run ws nd rfl) nc reach covered lo
    have cm := count_constants dom ws
    change k+c.paid+paid.toNat < c.bound+ws.countP (isMaskedConstant c.domain) at bound
    omega
  cases paid with
  | false =>
    apply done _ _ hp _ rfl
    intro a h
    rcases List.mem_cons.mp h with rfl | hm
    · exact availableB_sound dom hs buy
    · exact availableB_sound dom hs (known _ hm)
  | true =>
    obtain ⟨out,hr,hc⟩ := pay_choice dom hp hs choice buy
    apply done _ _ hr _ rfl
    intro a h
    rcases List.mem_cons.mp h with rfl | hm
    · exact hc _ (by simp)
    · have avail := availableB_sound dom hs (known _ hm)
      rcases avail with mem | con
      · have ha : availableB c.domain c.wires a = true := known _ hm
        have point : ∀ u ∈ c.wires, Available out (restrictRows f (observe u)) :=
          fun u hu => hc u (List.mem_cons_of_mem _ hu)
        exact availableB_sound dom point ha
      · exact Or.inr con

def scalarPoolCut (c : BoundPool) (k : Nat) (rest : List Sig) (op : Choice) :=
  let z := choiceVal op
  let extra := !(availableB c.domain c.wires z)
  ((k+c.paid+extra.toNat < c.bound+(z::rest).countP (isMaskedConstant c.domain)) &&
    rest.all (availableB c.domain c.wires)) && (!extra || choiceOK c.domain c.wires op)

theorem scalarPoolCut_sound {raw T c} (valid : ValidPool raw T c) {k rest op}
    (nd : (choiceVal op::rest).Nodup) (cut : scalarPoolCut c k rest op = true) :
    Impossible T k (choiceVal op::rest).toFinset := by
  let extra := !(availableB c.domain c.wires (choiceVal op))
  apply valid_exclude valid k rest op extra _ _ _ nd
  · simp only [scalarPoolCut,Bool.and_eq_true,List.all_eq_true] at cut
    exact cut.1.2
  · simp only [scalarPoolCut,Bool.and_eq_true,Bool.or_eq_true] at cut
    cases he : availableB c.domain c.wires (choiceVal op) <;> simp_all [extra]
  · simp only [scalarPoolCut,Bool.and_eq_true,decide_eq_true_eq] at cut
    exact cut.1.1

def materialize (raw : List Sig) (cs : List Choice) (d : Sig) (lb : Nat) : Option BoundPool :=
  (makePool d raw cs).map (fun pool => ⟨d,lb,cs.length,pool⟩)
theorem materialize_sound {raw T d L cs c} (slice : Slice raw T d L)
    (h : materialize raw cs d L = some c) : ValidPool raw T c := by
  unfold materialize at h
  cases he : makePool d raw cs with
  | none => simp [he] at h
  | some pool =>
    simp only [he,Option.map_some,Option.some.injEq] at h
    subst c
    exact build_valid slice cs he


abbrev Bits := BitVec 768
abbrev Signals := Bits × Bits
abbrev Decor := Sig × Signals

def ofRows {n : Nat} (r : Fin n → Row) (v : Sig) : BitVec n :=
  (BitVec.ofBoolListLE (List.ofFn (fun i => bit (r i) v))).cast List.length_ofFn
theorem ofRows_bit {n : Nat} (r : Fin n → Row) (v : Sig) (i : Fin n) :
    (ofRows r v).getLsbD i.val = bit (r i) v := by
  simp only [ofRows,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [i.isLt]
def pairSig (r s : Fin 768 → Row) (a : Sig) : Signals := (ofRows r a,ofRows s a)
def properPairs (T : Sig) (r s : Fin 768 → Row) :=
  ∀ i, bit (r i) T = true ∧ bit (s i) T = false
theorem pair_sep {T r s} (h : properPairs T r s) : Sep T 768 r s (pairSig r s) := by
  exact ⟨h,fun a i => ⟨ofRows_bit _ _ _,ofRows_bit _ _ _⟩⟩
def faithful (r s : Fin 768 → Row) (x : Decor) := x.2 = pairSig r s x.1
def dneg (x : Decor) : Decor := (neg x.1,~~~x.2.1,~~~x.2.2)
def dbin (d : Bool) (x y : Decor) : Decor :=
  if d then (bin d x.1 y.1,x.2.1 ||| y.2.1,x.2.2 ||| y.2.2)
  else (bin d x.1 y.1,x.2.1 &&& y.2.1,x.2.2 &&& y.2.2)

theorem ofRows_neg (r : Fin 768 → Row) (a : Sig) : ofRows r (neg a) = ~~~ofRows r a := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have h := ofRows_bit r (neg a) ⟨j,hj⟩
  rw [bit_neg,←ofRows_bit r a ⟨j,hj⟩] at h
  simpa only [BitVec.getLsbD_not,hj,decide_true,Bool.true_and] using h
theorem ofRows_bin {n : Nat} (r : Fin n → Row) (d : Bool) (a b : Sig) :
    ofRows r (bin d a b) = if d then ofRows r a ||| ofRows r b else ofRows r a &&& ofRows r b := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have h := ofRows_bit r (bin d a b) ⟨j,hj⟩
  rw [bit_bin,←ofRows_bit r a ⟨j,hj⟩,←ofRows_bit r b ⟨j,hj⟩] at h
  cases d <;> simpa only [Bool.false_eq_true,ite_false,ite_true,BitVec.getLsbD_and,BitVec.getLsbD_or] using h
theorem faithful_neg {r s x} (h : faithful r s x) : faithful r s (dneg x) := by
  change x.2 = _ at h
  simp only [faithful,dneg,pairSig,ofRows_neg, h]
theorem faithful_bin {r s x y} (d) (hx : faithful r s x) (hy : faithful r s y) :
    faithful r s (dbin d x y) := by
  change x.2 = _ at hx
  change y.2 = _ at hy
  cases d <;> simp only [faithful,dbin,Bool.false_eq_true,ite_false,ite_true,pairSig,ofRows_bin,hx,hy]

def codeDecor (op : Nat) (x y : Decor) := if op=2 then dneg x else dbin (op==1) x y
def defaultDecor : Decor := (zero,0,0)
theorem faithful_default (r s) : faithful r s defaultDecor := by
  apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro j hj
  · change (0 : Bits).getLsbD j = (ofRows r zero).getLsbD j
    rw [show (ofRows r zero).getLsbD j = bit (r ⟨j,hj⟩) zero from ofRows_bit _ _ ⟨j,hj⟩,bit_zero]
    simp
  · change (0 : Bits).getLsbD j = (ofRows s zero).getLsbD j
    rw [show (ofRows s zero).getLsbD j = bit (s ⟨j,hj⟩) zero from ofRows_bit _ _ ⟨j,hj⟩,bit_zero]
    simp
theorem faithful_get {r s ws} (all : ∀ v ∈ ws, faithful r s v) (i : Nat) :
    faithful r s (List.getD ws i defaultDecor) := by
  simp only [List.getD_eq_getElem?_getD]
  cases e : ws[i]? with
  | none => exact faithful_default _ _
  | some v => exact all _ (List.mem_of_getElem? e)
def decodeBank (n : Nat) (bits : Nat) (ws : List Decor) : List Decor :=
  match n with
  | 0 => ws
  | k+1 =>
    let a := ws.getD (bits &&& 15) defaultDecor
    let b := ws.getD ((bits >>> 4) &&& 15) defaultDecor
    decodeBank k (bits >>> 10) (ws++[codeDecor ((bits >>> 8) &&& 3) a b])
theorem decode_faithful (n bits) (ws) (r s) (base : ∀ v ∈ ws, faithful r s v) :
    ∀ v ∈ decodeBank n bits ws, faithful r s v := by
  induction n generalizing ws bits with
  | zero => exact base
  | succ n ih =>
    apply ih
    intro v hv
    rcases List.mem_append.mp hv with hw | hz
    · exact base _ hw
    · obtain rfl := List.mem_singleton.mp hz
      unfold codeDecor
      split
      · exact faithful_neg (faithful_get base _)
      · exact faithful_bin _ (faithful_get base _) (faithful_get base _)

def asRow (cols : Nat → Bits) (i : Fin 768) : Row :=
  (BitVec.ofBoolListLE (List.ofFn (fun j : Fin 9 => (cols j.val).getLsbD i.val))).toFin.cast
    (by simp [List.length_ofFn])
theorem coordinate0 : ∀ r : Row, bit r (inputs.getD 0 zero) = r.val.testBit 0 := by decide +kernel
theorem coordinate1 : ∀ r : Row, bit r (inputs.getD 1 zero) = r.val.testBit 1 := by decide +kernel
theorem coordinate2 : ∀ r : Row, bit r (inputs.getD 2 zero) = r.val.testBit 2 := by decide +kernel
theorem coordinate3 : ∀ r : Row, bit r (inputs.getD 3 zero) = r.val.testBit 3 := by decide +kernel
theorem coordinate4 : ∀ r : Row, bit r (inputs.getD 4 zero) = r.val.testBit 4 := by decide +kernel
theorem coordinate5 : ∀ r : Row, bit r (inputs.getD 5 zero) = r.val.testBit 5 := by decide +kernel
theorem coordinate6 : ∀ r : Row, bit r (inputs.getD 6 zero) = r.val.testBit 6 := by decide +kernel
theorem coordinate7 : ∀ r : Row, bit r (inputs.getD 7 zero) = r.val.testBit 7 := by decide +kernel
theorem coordinate8 : ∀ r : Row, bit r (inputs.getD 8 zero) = r.val.testBit 8 := by decide +kernel
theorem input_coords : ∀ (j : Fin 9) (r : Row),
    bit r (inputs.getD j.val zero) = r.val.testBit j.val := by
  intro j r
  fin_cases j
  · exact coordinate0 r
  · exact coordinate1 r
  · exact coordinate2 r
  · exact coordinate3 r
  · exact coordinate4 r
  · exact coordinate5 r
  · exact coordinate6 r
  · exact coordinate7 r
  · exact coordinate8 r
theorem asRow_bit (cols : Nat → Bits) (i : Fin 768) (j : Fin 9) :
    bit (asRow cols i) (inputs.getD j.val zero) = (cols j.val).getLsbD i.val := by
  rw [input_coords]
  change (BitVec.ofBoolListLE (List.ofFn (fun h : Fin 9 => (cols h.val).getLsbD i.val))).getLsbD j.val = _
  simp only [BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [j.isLt]
def rawDecor (m : Nat) (p q : Nat → Bits) : List Decor :=
  (selected m).map (fun (j,a) => (a,p j,q j))
theorem selected_entry {m j a} (h : (j,a) ∈ selected m) :
    j<9 ∧ a=inputs.getD j zero := by
  obtain ⟨v,hv,hh⟩ := List.mem_filterMap.mp h
  simp only [List.mem_range] at hv
  split at hh
  next =>
    cases hh
    exact ⟨hv,rfl⟩
  next => contradiction
theorem raw_faithful (m) (p q : Nat → Bits) :
    ∀ a ∈ rawDecor m p q, faithful (asRow p) (asRow q) a := by
  intro a ha
  obtain ⟨⟨j,v⟩,hv,rfl⟩ := List.mem_map.mp ha
  obtain ⟨hj,rfl⟩ := selected_entry hv
  apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi
  · exact (asRow_bit p ⟨i,hi⟩ ⟨j,hj⟩).symm.trans (ofRows_bit _ _ ⟨i,hi⟩).symm
  · exact (asRow_bit q ⟨i,hi⟩ ⟨j,hj⟩).symm.trans (ofRows_bit _ _ ⟨i,hi⟩).symm

def liftGoal (m : Nat) (v : Nat → Bits) : Bits :=
  let x := fun j => if m.testBit j then v j else 0
  (x 0 &&& x 1) ||| (x 1 &&& x 2) ||| (x 2 &&& x 3) ||| (x 3 &&& x 4) |||
    (x 4 &&& x 0) ||| (x 0 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 7) |||
    (x 3 &&& x 8) ||| (x 5 &&& x 7) ||| (x 6 &&& x 8) ||| (x 8 &&& x 5)
theorem bit_vertex (m : Nat) (v : Nat → Bits) (i : Fin 768) (j : Fin 9) :
    bit (asRow v i) (vertex m j.val) =
    ((if m.testBit j.val then v j.val else 0) : Bits).getLsbD i.val := by
  by_cases hh : m.testBit j.val = true
  · simpa [vertex,hh] using asRow_bit v i j
  · simp [vertex,hh,bit_zero]
theorem bit_liftGoal (m : Nat) (v : Nat → Bits) (i : Fin 768) :
    bit (asRow v i) (graphGoal m) = (liftGoal m v).getLsbD i.val := by
  have pos (j : Nat) (hj : j<9) : (vertex m j).getLsbD (asRow v i).val = ((if m.testBit j then v j else 0) : Bits).getLsbD i.val := bit_vertex m v i ⟨j,hj⟩
  simp only [bit,graphGoal,liftGoal,BitVec.getLsbD_and,BitVec.getLsbD_or]
  simp only [pos 0 (by decide),pos 1 (by decide),pos 2 (by decide),pos 3 (by decide),pos 4 (by decide),pos 5 (by decide),pos 6 (by decide),pos 7 (by decide),pos 8 (by decide)]
abbrev Cov := Bits × Bits × Bits

def addCov (z : Bits) (c : Cov) : Cov :=
  (z ||| c.1, (z &&& ~~~c.1) ||| (c.2.1 &&& ~~~z),
   (z &&& c.2.1) ||| (c.2.2 &&& ~~~z))

def coverage (d : Bool) (v : List Decor) : Cov :=
  v.foldr (fun a c => addCov (column d a.2) c) (0,0,0)

def takeOne (c : Cov) (a : Bits) : Bits := c.1 &&& ~~~(c.2.1 &&& a)
def takeTwo (c : Cov) (a b : Bits) : Bits :=
  c.1 &&& ~~~((c.2.1 &&& (a ||| b)) ||| (c.2.2 &&& (a &&& b)))

private theorem cov_one (c : Cov) (a : Bits) : takeOne (addCov a c) a=c.1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [takeOne,addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases c.1.getLsbD i <;> cases c.2.1.getLsbD i <;> rfl

private theorem cov_two (c : Cov) (a b : Bits) : takeTwo (addCov a (addCov b c)) a b=c.1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [takeTwo,addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.1.getLsbD i <;>
    cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> rfl

private theorem add_swap (c : Cov) (a b : Bits) : addCov a (addCov b c)=addCov b (addCov a c) := by
  apply Prod.ext
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [addCov,BitVec.getLsbD_or]
    cases a.getLsbD i <;> cases b.getLsbD i <;> rfl
  · apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi <;>
      simp only [addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and] <;>
      cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.1.getLsbD i <;>
      cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> rfl

private theorem cov_perm (d : Bool) {l r : List Decor} (h : l.Perm r) : coverage d l=coverage d r := by
  induction h with
  | nil => rfl
  | cons a _ ih => exact congrArg (addCov (column d a.2)) ih
  | swap a b t => exact add_swap _ _ _
  | trans _ _ h1 h2 => exact h1.trans h2



theorem cov_word (d : Bool) (v : List Decor) {r s} (good : ∀ a ∈ v, faithful r s a) :
    (coverage d v).1 = covered d (pairSig r s) (v.map Prod.fst) := by
  induction v with
  | nil => rfl
  | cons a v ih =>
    change (column d a.2 ||| (coverage d v).1) = column d (pairSig r s a.1) ||| _
    rw [show a.2=pairSig r s a.1 from good _ (by simp),ih (fun a ha => good a (by simp [ha]))]

def delOne (ws : List Decor) (a : Decor) (keep : Bool) :=
  if keep then ws else ws.erase a
def delTwo (ws : List Decor) (a b : Decor) (ka kb : Bool) :=
  delOne (delOne ws a ka) b kb

theorem delOne_perm {ws : List Decor} (a : Decor) (ha : a ∈ ws) :
    ws.Perm (a::ws.erase a) := List.perm_cons_erase ha

theorem cover_one {ws : List Decor} (d : Bool) (a : Decor) (ha : a ∈ ws) (keep : Bool) :
    (coverage d (delOne ws a keep)).1 =
      (if keep then (coverage d ws).1 else takeOne (coverage d ws) (column d a.2)) := by
  cases keep
  · change (coverage d (ws.erase a)).1 = takeOne (coverage d ws) _
    rw [cov_perm d (delOne_perm a ha)]
    exact (cov_one _ _).symm
  · rfl
theorem delTwo_perm {ws : List Decor} (a b : Decor) (ha : a ∈ ws) (hb : b ∈ ws) (hne : a≠b) :
    ws.Perm (a::b::(ws.erase a).erase b) := by
  have hm : b ∈ ws.erase a := (List.mem_erase_of_ne (Ne.symm hne)).mpr hb
  exact (delOne_perm a ha).trans (List.Perm.cons _ (delOne_perm b hm))

theorem cover_two {ws : List Decor} (d : Bool) (a b : Decor) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : a ≠ b) (ka kb : Bool) :
    (coverage d (delTwo ws a b ka kb)).1 =
      (if ka then (if kb then (coverage d ws).1 else takeOne (coverage d ws) (column d b.2))
       else if kb then takeOne (coverage d ws) (column d a.2)
       else takeTwo (coverage d ws) (column d a.2) (column d b.2)) := by
  cases ka <;> cases kb
  · change (coverage d ((ws.erase a).erase b)).1 = takeTwo (coverage d ws) _ _
    rw [cov_perm d (delTwo_perm a b ha hb ne)]
    exact (cov_two _ _ _).symm
  · exact cover_one d a ha false
  · exact cover_one d b hb false
  · rfl

def sameWords (a b : List Sig) := (a.all (fun x => b.contains x)) && (b.all (fun x => a.contains x))
theorem sameWords_sound {xs ys} (h : sameWords xs ys = true) : xs.toFinset=ys.toFinset := by
  simp only [sameWords,Bool.and_eq_true,List.all_eq_true,List.contains_eq_mem,decide_eq_true_eq] at h
  ext a
  simp only [List.mem_toFinset]
  exact ⟨h.1 a,h.2 a⟩


def keyWord (v : Sig) :=
  let n := v.toNat % 2305843009213693951
  (n*(n+971)) % 2305843009213693951
def keySet (xs : List Sig) := xs.foldl (fun v x => v+keyWord x) 0

def closeChild (pools : List BoundPool) (links : Nat → List (List Sig)) (k : Nat)
    (rest : List Sig) (op : Choice) :=
  let ws := choiceVal op::rest
  (links (keySet ws)).any (sameWords ws) || pools.any (fun p => scalarPoolCut p k rest op)

theorem closeChild_sound {raw T pools links k rest op}
    (pValid : ∀ p ∈ pools, ValidPool raw T p)
    (lValid : ∀ tag xs, xs ∈ links tag → Impossible T k (List.toFinset xs))
    (nd : (choiceVal op :: rest).Nodup)
    (h : closeChild pools links k rest op = true) :
    Impossible T k (choiceVal op :: rest).toFinset := by
  simp only [closeChild,Bool.or_eq_true,List.any_eq_true] at h
  rcases h with ⟨xs,hx,ok⟩ | ⟨p,hp,ok⟩
  · rw [sameWords_sound ok]
    exact lValid _ _ hx
  · exact scalarPoolCut_sound (pValid _ hp) nd ok

abbrev CovPair := Cov × Cov
def preCov (ws : List Decor) : CovPair := (coverage false ws,coverage true ws)
def getCov (c : CovPair) (d : Bool) := if d then c.2 else c.1
theorem get_preCov (ws) (d : Bool) : getCov (preCov ws) d = coverage d ws := by cases d <;> rfl
def restCov (v : Cov) (a b : Bits) (un ka kb : Bool) :=
  if un then (if ka then v.1 else takeOne v a) else
    if ka then (if kb then v.1 else takeOne v b)
    else if kb then takeOne v a else takeTwo v a b
def opKeep (un ka kb : Bool) (a b : Decor) (ws : List Decor) :=
  if un then delOne ws a ka else delTwo ws a b ka kb

theorem rest_coverage {ws : List Decor} {a b : Decor} (ha : a ∈ ws) (hb : b ∈ ws)
    (un ka kb d : Bool) (ne : un=false → a≠b) :
    (coverage d (opKeep un ka kb a b ws)).1 =
      restCov (getCov (preCov ws) d) (column d a.2) (column d b.2) un ka kb := by
  rw [get_preCov]
  cases un
  · exact cover_two d a b ha hb (ne rfl) ka kb
  · exact cover_one d a ha ka

theorem delOne_sub (ws : List Decor) (a : Decor) (k : Bool) : (delOne ws a k).Sublist ws := by
  cases k
  · exact List.erase_sublist
  · exact List.Sublist.refl _
theorem keep_sub (ws : List Decor) (a b : Decor) (un ka kb : Bool) :
    (opKeep un ka kb a b ws).Sublist ws := by
  cases un
  · exact (delOne_sub _ _ _).trans (delOne_sub _ _ _)
  · exact delOne_sub _ _ _
theorem len_keep (ws : List Decor) (a b : Decor) (un ka kb : Bool) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : un=false → a≠b) :
    (opKeep un ka kb a b ws).length =
      ws.length - (if ka then 0 else 1) - (if un || kb then 0 else 1) := by
  cases un
  · have hm : b ∈ ws.erase a := (List.mem_erase_of_ne (Ne.symm (ne rfl))).mpr hb
    cases ka <;> cases kb <;> simp [opKeep,delTwo,delOne,List.length_erase_of_mem ha,List.length_erase_of_mem hb,List.length_erase_of_mem hm]
  · cases ka <;> cases kb <;> simp [opKeep,delOne,List.length_erase_of_mem ha]

def movedDecor (op : Nat) (a b : Decor) := codeDecor op a b
def movedChoice (op : Nat) (a b : Decor) : Choice := (op,a.1,b.1)
theorem moved_full (op) (a b : Decor) :
    (movedDecor op a b).1 = choiceVal (movedChoice op a b) := by
  by_cases h : op=2
  · simp [movedDecor,codeDecor,h,dneg,choiceVal,movedChoice]
  · cases hh : op==1 <;> simp [movedDecor,codeDecor,h,hh,dbin,choiceVal,movedChoice]
theorem moved_faithful {r s a b} (ha : faithful r s a) (hb : faithful r s b) (op : Nat) :
    faithful r s (movedDecor op a b) := by
  unfold movedDecor codeDecor
  split
  · exact faithful_neg ha
  · exact faithful_bin _ ha hb

abbrev NodeContext := Nat × Nat × List Decor × CovPair × List BoundPool × (Nat → List (List Sig))
def evalMove (c : NodeContext) (op : Nat) (a b z : Decor) (ka kb : Bool) :=
  let (cap,n,ws,cov,pools,links) := c
  let un := op==2
  let len := 1+(n - (if ka then 0 else 1) - (if un || kb then 0 else 1))
  if len>cap then true else
    let d := len==cap
    let rs := restCov (getCov cov d) (column d a.2) (column d b.2) un ka kb
    if (rs ||| column d z.2) != BitVec.allOnes 768 then true else
    if !properB z.1 || ws.any (fun v => v.1==z.1) then true else
      let rest := (opKeep un ka kb a b ws).map Prod.fst
      closeChild pools links (cap-1) rest (movedChoice op a b)

def moveFront (ws : List Decor) (op : Nat) (a b : Decor) (ka kb : Bool) :=
  (movedDecor op a b).1 :: (opKeep (op==2) ka kb a b ws).map Prod.fst
theorem evalMove_sound {raw T r s ws pools links cap a b op ka kb}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : (op==2)=false → a≠b) (hcap : 0<cap)
    (pv : ∀ p ∈ pools, ValidPool raw T p)
    (lv : ∀ tag xs, xs ∈ links tag → Impossible T (cap-1) (List.toFinset xs))
    (pro : proper (movedDecor op a b).1) (fresh : (movedDecor op a b).1 ∉ ws.map Prod.fst)
    (test : evalMove (cap,ws.length,ws,preCov ws,pools,links) op a b (movedDecor op a b) ka kb = true) :
    Impossible T (cap-1) (moveFront ws op a b ka kb).toFinset := by
  let z := movedDecor op a b
  let rest := opKeep (op==2) ka kb a b ws
  let child := z.1 :: rest.map Prod.fst
  have sub : rest.Sublist ws := keep_sub _ _ _ _ _ _
  have ndc : child.Nodup := List.nodup_cons.mpr ⟨fun hm => fresh ((sub.map _).subset hm),
    nd.sublist (sub.map _)⟩
  have fr : ws.any (fun v => v.1==z.1) = false := by
    apply Bool.eq_false_iff.mpr
    intro hh
    obtain ⟨x,hx,he⟩ := List.any_eq_true.mp hh
    exact fresh (beq_iff_eq.mp he ▸ List.mem_map_of_mem hx)
  have pp : properB z.1 = true := by simpa [properB,proper] using pro
  have leq : 1+(ws.length-(if ka then 0 else 1)-(if (op==2) || kb then 0 else 1)) = child.length := by
    change _ = (z.1::rest.map Prod.fst).length
    rw [List.length_cons,List.length_map,len_keep _ _ _ _ _ _ ha hb ne,Nat.add_comm 1]
  intro k t hk h
  have hsz := (live_size h).2
  change child.toFinset.card + t ≤ k+1 at hsz
  rw [List.toFinset_card_of_nodup ndc] at hsz
  have len : child.length ≤ cap := by omega
  unfold evalMove at test
  change (if 1+(ws.length-_ - _) > cap then true else _) = true at test
  rw [leq,if_neg (by omega)] at test
  have sep := cover_required h hk ndc (pair_sep pairs)
  have ce : cap-1+1=cap := by omega
  rw [ce] at sep
  let d := child.length==cap
  have g : (coverage d rest).1 = covered d (pairSig r s) (rest.map Prod.fst) :=
    cov_word _ _ (fun v hv => faith _ (sub.subset hv))
  have rz := rest_coverage ha hb (op==2) ka kb d ne
  have hf := moved_faithful (faith _ ha) (faith _ hb) op
  have deq : decide (child.length=cap) = (child.length==cap) := by by_cases he : child.length=cap <;> simp [he]
  change covered (decide (child.length = cap)) (pairSig r s) child = BitVec.allOnes 768 at sep
  rw [deq] at sep
  change column d (pairSig r s z.1) ||| covered d (pairSig r s) (rest.map Prod.fst) = _ at sep
  change z.2 = pairSig r s z.1 at hf
  rw [←hf,←g,rz,BitVec.or_comm] at sep
  have be : ((restCov (getCov (preCov ws) d) (column d a.2) (column d b.2) (op==2) ka kb ||| column d z.2) != BitVec.allOnes 768) = false := by simp [sep]
  change (if (_ != _) then true else if !properB z.1 || ws.any (fun v => v.1==z.1) then true else _) = true at test
  rw [be,pp,fr] at test
  have val := moved_full op a b
  change z.1 = _ at val
  change Live T k t child.toFinset at h
  have nd' := ndc
  change (z.1::rest.map Prod.fst).Nodup at nd'
  change Live T k t (z.1::rest.map Prod.fst).toFinset at h
  rw [val] at nd' h
  exact closeChild_sound pv lv nd' test k t hk h


def testPair (ctx : NodeContext) (a b : Decor) (d : Bool) :=
  let op := if d then 1 else 0
  let z := movedDecor op a b
  let attempt := evalMove ctx op a b z
  attempt false false && attempt true false && attempt false true && attempt true true
def testRow (ctx : NodeContext) (a : Decor) (bs : List Decor) :=
  let z := movedDecor 2 a a
  evalMove ctx 2 a a z false false && evalMove ctx 2 a a z true true &&
    bs.all (fun b => testPair ctx a b false && testPair ctx a b true)
def testAll (ctx : NodeContext) : List Decor → Bool
  | [] => true
  | a::bs => testRow ctx a bs && testAll ctx bs

theorem all_unary {ctx ws} (h : testAll ctx ws=true) {a : Decor} (ha : a∈ws) (keep : Bool) :
    evalMove ctx 2 a a (movedDecor 2 a a) keep keep=true := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    simp only [testAll,Bool.and_eq_true,testRow] at h
    rcases List.mem_cons.mp ha with rfl | hm
    · cases keep
      · exact h.1.1.1
      · exact h.1.1.2
    · exact ih h.2 hm

theorem all_binary {ctx ws} (h : testAll ctx ws=true) {a b : Decor} (ha : a∈ws) (hb : b∈ws)
    (ne : a≠b) (d : Bool) : testPair ctx a b d=true ∨ testPair ctx b a d=true := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    simp only [testAll,Bool.and_eq_true,testRow,List.all_eq_true] at h
    rcases List.mem_cons.mp ha with rfl | haTail
    · have bm := (List.mem_cons.mp hb).resolve_left (Ne.symm ne)
      left
      cases d <;> first | exact (h.1.2 b bm).1 | exact (h.1.2 b bm).2
    · rcases List.mem_cons.mp hb with rfl | hbTail
      · right
        cases d <;> first | exact (h.1.2 a haTail).1 | exact (h.1.2 a haTail).2
      · exact ih h.2 haTail hbTail

theorem testPair_at {ctx a b d} (h : testPair ctx a b d = true) (ka kb : Bool) :
    evalMove ctx (if d then 1 else 0) a b (movedDecor (if d then 1 else 0) a b) ka kb = true := by
  simp only [testPair,Bool.and_eq_true] at h
  cases ka <;> cases kb <;> first | exact h.1.1.1 | exact h.1.2 | exact h.1.1.2 | exact h.2

theorem keep_mem {v : List Sig} {w : Sig} (a : Sig) (k : Bool) :
    w ∈ kept k a v ↔ (w=a ∧ k=true) ∨ w∈v := by cases k <;> simp [kept]
theorem mem_delone {v : List Decor} (nd : v.Nodup) (a w : Decor) (k : Bool) :
    w ∈ delOne v a k ↔ w∈v ∧ (w≠a ∨ k=true) := by
  cases k <;> simp [delOne,nd.mem_erase_iff,and_comm]

theorem unique_value {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a∈ws) (hb : b∈ws) (eq : a.1=b.1) : a=b := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    obtain ⟨hn,ht⟩ := List.nodup_cons.mp nd
    rcases List.mem_cons.mp ha with rfl | haTail <;> rcases List.mem_cons.mp hb with rfl | hbTail
    · rfl
    · exact False.elim (hn (eq ▸ List.mem_map_of_mem hbTail))
    · exact False.elim (hn (eq.symm ▸ List.mem_map_of_mem haTail))
    · exact ih ht haTail hbTail

theorem kept_value {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a ∈ ws) (hb : b ∈ ws) (un ka kb : Bool) (v : Sig) :
    v ∈ (opKeep un ka kb a b ws).map Prod.fst ↔
    v ∈ ws.map Prod.fst ∧ (v≠a.1 ∨ ka=true) ∧ (un=true ∨ v≠b.1 ∨ kb=true) := by
  have wn := nd.of_map
  have dn := wn.sublist (delOne_sub ws a ka)
  cases un <;> simp only [opKeep,Bool.false_eq_true,ite_false,ite_true,delTwo,List.mem_map,
    mem_delone wn,mem_delone dn,or_false,false_or,true_or,and_true] <;> constructor
  all_goals
    first
    | rintro ⟨w,hw,rfl⟩
      first
      | exact ⟨⟨_,hw.1.1,rfl⟩,hw.1.2.imp (fun ne eq => ne (unique_value nd hw.1.1 ha eq)) id,
          hw.2.imp (fun ne eq => ne (unique_value nd hw.1.1 hb eq)) id⟩
      | exact ⟨⟨_,hw.1,rfl⟩,hw.2.imp (fun ne eq => ne (unique_value nd hw.1 ha eq)) id⟩
    | rintro ⟨⟨w,hm,rfl⟩,h1,h2⟩
      exact ⟨w,⟨⟨hm,h1.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,
        h2.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,rfl⟩
    | rintro ⟨⟨w,hm,rfl⟩,h1⟩
      exact ⟨w,⟨hm,h1.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,rfl⟩

theorem unary_front {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a : Decor} (ha : a∈ws)
    (keep : Bool) :
    (moveFront ws 2 a a keep keep).toFinset = (childOne (ws.map Prod.fst) a.1 keep).toFinset := by
  ext v
  simp only [moveFront,childOne,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    kept_value nd ha ha,keep_mem,nd.mem_erase_iff,movedDecor,codeDecor,dneg,ite_true,
    Nat.reduceBEq,true_or,and_true]
  have av := List.mem_map_of_mem (f:=Prod.fst) ha
  by_cases e : v=a.1 <;> cases keep <;> simp_all

theorem binary_front {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a∈ws) (hb : b∈ws) (ne : a.1≠b.1) (d ka kb : Bool) :
    (moveFront ws (if d then 1 else 0) a b ka kb).toFinset =
      (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
  ext v
  have av := List.mem_map_of_mem (f:=Prod.fst) ha
  have bv := List.mem_map_of_mem (f:=Prod.fst) hb
  cases d <;> simp only [moveFront,childTwo,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    kept_value nd ha hb,keep_mem,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,movedDecor,codeDecor,dbin,
    Bool.false_eq_true,Nat.reduceBEq,ite_true,ite_false,false_or]
  all_goals by_cases va : v=a.1 <;> by_cases vb : v=b.1 <;> cases ka <;> cases kb <;> simp_all

theorem childTwo_swap (v : List Sig) (nd : v.Nodup) (a b : Sig) (d ka kb : Bool) :
    (childTwo v a b d ka kb).toFinset = (childTwo v b a d kb ka).toFinset := by
  ext x
  simp only [childTwo,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    keep_mem,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,bin_comm d b a]
  tauto

theorem node_sound {raw T r s ws pools links cap}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (out : T ∉ ws.map Prod.fst)
    (pv : ∀ p ∈ pools, ValidPool raw T p)
    (lv : ∀ tag xs, xs ∈ links tag → Impossible T (cap-1) (List.toFinset xs))
    (checks : testAll (cap,ws.length,ws,preCov ws,pools,links) ws = true) :
    Impossible T cap (ws.map Prod.fst).toFinset := by
  by_cases hc : cap=0
  · intro k t hk h
    have ke : k=0 := by omega
    subst k
    generalize he : (ws.map Prod.fst).toFinset = S at h
    have eqS : S = {_} := h (fun k _ S => k = 0 → S = {_}) (fun _ _ => rfl) (fun _ _ _ hn => by contradiction) (fun _ _ _ _ _ hn => by contradiction) rfl
    exact out (List.mem_toFinset.mp ((he.trans eqS).symm ▸ Finset.mem_singleton_self _))
  have hc' : 0<cap := by omega
  apply enum_step nd out
  · intro v hv keep fresh pro len
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hv
    have hf := unary_front nd ha keep
    rw [←hf]
    exact evalMove_sound pairs faith nd ha ha (by simp) hc' pv lv pro fresh (all_unary checks ha keep)
  · intro a ha b hb d ka kb ne fresh pro len
    obtain ⟨a,haW,rfl⟩ := List.mem_map.mp ha
    obtain ⟨b,hbW,rfl⟩ := List.mem_map.mp hb
    have ab : a≠b := fun e => ne (congrArg Prod.fst e)
    have one (a b : Decor) (aa : a∈ws) (bb : b∈ws) (ne' : a.1≠b.1) (ka kb : Bool)
        (pr : proper (bin d a.1 b.1)) (fr : bin d a.1 b.1 ∉ ws.map Prod.fst)
        (test : testPair (cap,ws.length,ws,preCov ws,pools,links) a b d = true) :
        Impossible T (cap-1) (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
      rw [←binary_front nd aa bb ne']
      have eq : (movedDecor (if d then 1 else 0) a b).1 = bin d a.1 b.1 := by cases d <;> rfl
      exact evalMove_sound pairs faith nd aa bb (fun _ e => ne' (congrArg Prod.fst e)) hc' pv lv
        (eq ▸ pr) (eq ▸ fr) (testPair_at test ka kb)
    rcases all_binary checks haW hbW ab d with hh | hh
    · exact one a b haW hbW ne ka kb pro fresh hh
    · rw [childTwo_swap _ nd]
      exact one b a hbW haW (Ne.symm ne) kb ka (bin_comm d a.1 b.1 ▸ pro)
        (bin_comm d a.1 b.1 ▸ fresh) hh


theorem agree_inputs (r s : Row) (h : ∀ a ∈ inputs, bit r a = bit s a) : r=s := by
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j<9
  · let i : Fin 9 := ⟨j,hj⟩
    have hm : inputs.getD i.val zero ∈ inputs := by
      rw [← input_list]
      exact List.mem_ofFn.mpr ⟨i,rfl⟩
    exact (input_coords i r).symm.trans ((h _ hm).trans (input_coords i s))
  · have le : 512 ≤ 2^j := by
      change 2^9 ≤ 2^j
      exact Nat.pow_le_pow_right (by decide) (by omega)
    exact (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le r.isLt le)).trans
      (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le s.isLt le)).symm

def composedOK (p q : List Move) := inputs.all (fun a => movedWord p (movedWord q a) == a)
theorem composed_id {p q} (h : composedOK p q = true) (r : Row) :
    movedRow q (movedRow p r) = r := by
  apply agree_inputs
  intro a ha
  rw [←bit_moved,←bit_moved]
  have eq := beq_iff_eq.mp (List.all_eq_true.mp h a ha)
  rw [eq]

def autoOK (T : Sig) (p : List Move) :=
  (movedWord p T == T) && composedOK p p.reverse && composedOK p.reverse p
theorem rotate_excluded {T n} {ws : List Sig} (hi : Impossible T n ws.toFinset)
    (p : List Move) (ok : autoOK T p = true) : Impossible T n (ws.map (movedWord p.reverse)).toFinset := by
  simp only [autoOK,Bool.and_eq_true,beq_iff_eq] at ok
  have onto : Function.Surjective (movedRow p) := fun r => ⟨movedRow p.reverse r,composed_id ok.2 r⟩
  intro k t hk h
  have run := live_rename h (movedRow p) onto
  have goal : rename (movedRow p) T = T := (moved_eq_rename p T).symm.trans ok.1.1
  have inv (x : Sig) : rename (movedRow p) (movedWord p.reverse x) = x := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    change bit ⟨j,hj⟩ _ = bit ⟨j,hj⟩ _
    rw [bit_rename,bit_moved,composed_id ok.1.2]
  have back : (ws.map (movedWord p.reverse)).toFinset.image (rename (movedRow p)) = ws.toFinset := by
    ext a
    simp only [Finset.mem_image,List.mem_toFinset,List.mem_map]
    constructor
    · rintro ⟨v,⟨w,hw,rfl⟩,rfl⟩
      simpa only [inv] using hw
    · intro ha
      exact ⟨_,⟨a,ha,rfl⟩,inv a⟩
  rw [goal,back] at run
  exact hi k t hk run

abbrev Packing := Nat × Nat × Nat × Nat × Nat × Nat × Nat × (Nat → Nat)
def emptyPacking : Packing := (0,0,0,0,0,0,0,fun _ => 0)
def packedAt (word : Nat → Nat) (pos len : Nat) :=
  let i := pos/8192
  let shift := pos % 8192
  let lo := word i >>> shift
  if shift+len ≤ 8192 then lo &&& ((1 <<< len)-1)
  else (lo ||| (word (i+1) <<< (8192-shift))) &&& ((1 <<< len)-1)


def lookupWord (nb slots sw vw iw pw : Nat) (data : Nat → Nat) (h : Nat) : Option (Nat × Nat) :=
  let a := h % nb
  let sh := packedAt data (a*sw) sw
  let row := (h/nb+sh)%slots
  let word := packedAt data (nb*sw+row*vw) vw
  if (word >>> (iw+pw)) == h/(nb*slots)%16 then
    some (word &&& ((1 <<< iw)-1),(word >>> iw) &&& ((1 <<< pw)-1))
  else none


abbrev IndexTree (α : Type) := List α
def IndexTree.leaf {α} (xs : List α) : IndexTree α := xs
def IndexTree.fork {α} (_ : Nat) (a b : IndexTree α) : IndexTree α := a ++ b
def IndexTree.read {α} (xs : IndexTree α) (i : Nat) := xs[i]?
def IndexTree.values {α} (xs : IndexTree α) := xs
theorem IndexTree.read_mem {α} (tree : IndexTree α) {i x} (e : tree.read i=some x) :
    x ∈ tree.values := List.mem_of_getElem? e
abbrev Forest := (Nat) × (Nat) × (Nat → Bits × Bits) × (IndexTree ColumnInfo) × (Array (List Nat)) × (Nat → Packing) × (Nat → Nat → Option (Nat × Nat))
def Forest.mask (v : Forest) : Nat := v.1
def Forest.cap (v : Forest) : Nat := v.2.1
def Forest.samples (v : Forest) : Nat → Bits × Bits := v.2.2.1
def Forest.cols (v : Forest) : IndexTree ColumnInfo := v.2.2.2.1
def Forest.autos (v : Forest) : Array (List Nat) := v.2.2.2.2.1
def Forest.levels (v : Forest) : Nat → Packing := v.2.2.2.2.2.1
def Forest.index (v : Forest) : Nat → Nat → Option (Nat × Nat) := v.2.2.2.2.2.2

def wiresOf (g : Forest) :=
  let ws := rawDecor g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)
  let nonedge := dneg (dbin false (ws.getD 0 defaultDecor) (ws.getD 1 defaultDecor))
  if g.mask=1023 then ws.map (fun w => dbin false w nonedge) else ws
theorem wires_faithful (g : Forest) : ∀ a ∈ wiresOf g,
    faithful (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2) a := by
  have base := raw_faithful g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)
  intro a ha
  unfold wiresOf at ha
  split at ha
  · obtain ⟨w,hw,rfl⟩ := List.mem_map.mp ha
    exact faithful_bin false (base w hw) (faithful_neg (faithful_bin false
      (faithful_get base 0) (faithful_get base 1)))
  · exact base _ ha

def targetOf (g : Forest) := chartGoal g.mask
def chartSamples (m : Nat) (v : Nat → Bits) :=
  if m=1023 then liftGoal m v &&& ~~~(v 0 &&& v 1) else liftGoal m v
theorem chart_bit (m : Nat) (v : Nat → Bits) (i : Fin 768) :
    bit (asRow v i) (chartGoal m) = (chartSamples m v).getLsbD i.val := by
  by_cases e : m=1023
  · have u := asRow_bit v i (0 : Fin 9)
    have w := asRow_bit v i (1 : Fin 9)
    have h := bit_liftGoal m v i
    change (inputs.getD 0 zero).getLsbD (asRow v i).val = (v 0).getLsbD i.val at u
    change (inputs.getD 1 zero).getLsbD (asRow v i).val = (v 1).getLsbD i.val at w
    have seedEq : seed = inputs.getD 0 zero &&& inputs.getD 1 zero := by decide +kernel
    simp only [chartGoal,chartSamples,e,ite_true,bit,seedEq,BitVec.getLsbD_and,
      BitVec.getLsbD_not,(asRow v i).isLt,i.isLt,decide_true,Bool.true_and,u,w] at h ⊢
    rw [h]
  · simpa only [chartGoal,chartSamples,e,ite_false] using bit_liftGoal m v i
theorem chart_pairs {m : Nat} {p q : Nat → Bits}
    (hp : chartSamples m p = BitVec.allOnes 768) (hq : chartSamples m q = 0) :
    properPairs (chartGoal m) (asRow p) (asRow q) := by
  intro i
  simp only [chart_bit,hp,hq,BitVec.getLsbD_allOnes,i.isLt,decide_true,BitVec.getLsbD_zero]
  simp
def selectLive {α : Type} (bits : Nat) : List α → List α
  | [] => []
  | w::ws => if bits &&& 1 == 1 then w::selectLive (bits >>> 1) ws else selectLive (bits >>> 1) ws
theorem selectLive_sub {α : Type} (bits : Nat) (ws : List α) : (selectLive bits ws).Sublist ws := by
  induction ws generalizing bits with
  | nil => exact List.Sublist.slnil
  | cons a ws ih =>
    unfold selectLive
    split
    · exact List.Sublist.cons₂ _ (ih _)
    · exact List.Sublist.cons _ (ih _)

def storedBits (g : Forest) (depth : Nat) := if g.cap = 15 then 6+10*(depth-2) else 10*depth
def readNode (g : Forest) (k i : Nat) : Nat × List Decor × List Decor :=
  let raw := wiresOf g
  let (_,depth,_,_,_,_,_,data) := g.levels k
  let len := storedBits g depth
  let width := len+raw.length+depth
  let recp := packedAt data (i*width) width
  let stored := recp &&& ((1 <<< len)-1)
  let ops := if g.cap = 15 then 0x140 ||| ((0x100 ||| ((0x989787968676958575659484746454938373635343928272625242329181716151413121908070605040302010 >>> (8*(stored &&& 63))) &&& 255)) <<< 10) ||| ((stored >>> 6) <<< 20) else stored
  let bank := decodeBank depth ops raw
  (ops,bank,selectLive (recp >>> len) bank)

def getFieldV (x pos width : Nat) := (x >>> pos) &&& ((1 <<< width)-1)
def chosenSteps (bank : List Decor) (ops paid : Nat) : Nat → List Choice
  | 0 => []
  | n+1 =>
    let more := chosenSteps bank (ops >>> 10) (paid >>> 1) n
    if paid &&& 1 == 0 then more else
      (getFieldV ops 8 2,(bank.getD (ops &&& 15) defaultDecor).1,
        (bank.getD (getFieldV ops 4 4) defaultDecor).1) :: more

def buildRule (g : Forest) (ops d : Nat) (bank : List Decor) (idx paid : Nat) : Option BoundPool :=
  (g.cols.read idx).bind fun ci =>
    materialize (vars g.mask) (chosenSteps bank ops paid d) (subcube ci.1 ci.2.1) ci.2.2.2.2

theorem buildRule_sound (g : Forest)
    (cols : ∀ ci ∈ g.cols.values, Slice (vars g.mask) (targetOf g) (subcube ci.1 ci.2.1) ci.2.2.2.2)
    {i ops depth bank paid c} (h : buildRule g ops depth bank i paid = some c) :
    ValidPool (vars g.mask) (targetOf g) c := by
  unfold buildRule at h
  cases e : g.cols.read i with
  | none => simp [e] at h
  | some ci =>
    simp only [e,Option.bind_some] at h
    apply materialize_sound _ h
    exact cols ci (g.cols.read_mem e)

def getPairs (data : Nat → Nat) (w v : Nat) : Nat → Nat → List (Nat × Nat)
  | 0,_ => []
  | n+1,pos =>
    let x := packedAt data pos (w+v)
    (x &&& ((1 <<< w)-1),x >>> w) :: getPairs data w v n (pos+w+v)

def stateSet (g : Forest) (k i : Nat) := (readNode g k i).2.2.map Prod.fst
def linkedSet (g : Forest) (k : Nat) (pair : Nat × Nat) : Option (List Sig) :=
  if pair.1 ≥ (g.levels k).1 then none else
    (g.autos[pair.2]?).map fun perm => (stateSet g k pair.1).map (movedWord (perm.map swapRows).reverse)

theorem linkedSet_sound (g : Forest) (k : Nat)
    (names : ∀ x ∈ g.autos.toList, autoOK (targetOf g) (x.map swapRows) = true)
    (earlier : ∀ i < (g.levels k).1, Impossible (targetOf g) k (stateSet g k i).toFinset)
    {pair out} (h : linkedSet g k pair = some out) :
    Impossible (targetOf g) k out.toFinset := by
  unfold linkedSet at h
  split at h
  · contradiction
  next valid =>
    cases e : g.autos[pair.2]? with
    | none => simp [e] at h
    | some perm =>
      simp only [e,Option.map_some,Option.some.injEq] at h
      subst out
      exact rotate_excluded (earlier _ (by omega)) _ (names _ (by simpa using Array.mem_of_getElem? e))

def poolWords (i : Nat) : Nat := (if i < 3 then (if i < 1 then 0xb0105a6b08e61cd30d4d8640ba9a59503074d7334b182548d2634d319098a94c402437d3080bb1a5d90304808234b9225c8d2e4816234b1204c29b02817134b8a058500a281214010a09560467021153445599aaa050233ab08d5a2242034e3352c09a4229d114d06a719d3484d282397272c332615e043aa774519c258d9423d655089bf62051903621192c15d609b9036562c4b1214a115104a77249b584e2c4cc49325299324caed103932852a8e4cba264dd874344299994caa4a66d1444e4e2ed117655bb19f461de0a5da66a133484c8d423897624c0a9615c30288388241386050b03742882b132148d3032586b22bc15c512e3d43782c39e09e0ae389716ea0455864a2da83582a88e60a9aa2dd81aaa8e260592a3d551baa0295c7530ee17872bb025d7baeae16504abc1955cae6c97371199a8cdc304688200b9384a1caa4e052ef331c8880444e578829c384c75270f116a0bb5f4c6aa717937ef2aa05035270e5388298c958aaa8161327098b74e0e26a7181a09af74c7aa6f0540be0c12a2192812d16b08b1261ac2edaa669692f6456482a4921ea93f7616f243d0853490b29564a42a5408491f6487522d6553a719b940a9a43098264c13858b52a5d1216e941c49e0a4b052338a076486eb036171e8a048502ea815551248820421020e8131b28320487120a81310ea0064a20a4285821cc1405c872e50140c4b12258a9ccc6a22813b9a6069ae2c96146b0a2544d2a28e00428ba361cc2ea617546b2985951b04608230b918548c0a48222308aa04869c008288413ba040904448185473bf5957ad10de88a12acb8ce5843d211d53b8e954d4455502d119de88b14233a55ed19f688bb4ccca66413bb29569cef8a88bc80e895714676255a0a074a22cccd6611b2a03888a9c45d266a6a05e844c21061416f3318454c4aa62333144589df54cd7e66b12af488b5423d288353b98888d42269764519c195670ec88854508d858b3a6d6485832aa28cec8a506224511689dfa10c1181200b62a220cef057120b09054482a5de77ed3bba955c466ca88713bb850712820655bc2938a21e4eef288971138889d444ca557919bc5030510e688093b84a204c45de77132a898cc4caa8c238299772151ccc8633ef44219dfbcabdc1246a03c50490a48d28469941503aa316485bc42b8502ca81de669d114e6060102885145330e4c5930e8d3134c3235d91a308d154241235c91ac48d5247110e455128039214490a3a20c0434c2144a9c1558e4ab0611a708a08459281421125114199914228a88473ba39991c448e1146a0c3501c988123a1a044a4cea69b16a74bec42cb304e70043731b68bb36c0e0ca73d8fbac9729cad191acdcf3e105e224f65447d557b8ff6d71f90eabbd65e93fa0fb9247ba1473f410e444254fb46bb59419a96be9 else (if i < 2 then 0x5d4c5215298a812121502aa42a029845408b332614e994087324985364930814cb0469906087532b11a6616240942c48197588d2ceb1204a222804c4446a224c2992b111a24622354ca023a8840473229853889011d4cb026a88604d320c08e9dd30804b30281866050304c0a04093081113026a224c20532b8a06617134bc2e282885c4d2e4b8a088971354caa269905447326a89a4c1400ca92a26a22544d324989a5c93134a92626930501c532909a641211ccc2428288484d32e909a45d2140932428195484d2a69840416111cc2c226930503a205088e60a1134a94226a88956432ca0558cd40bb4ca81d193502eb26a04884503a733422a6668464272a07488a88354ca8122889dd05108153a650281114cc6a889994d11330e64940ba42a812222954d324a05599a551d334aa6a5540a051119d59de33533346756558cdc510a04899940912ac443a55502446711298cd40914442356778454c22815399a11ab19c2356228454c22a048625409094a81d169502451080d39de551cc8a8156888ceed1119a9a2233913bc67d2558cfa4ef11299de22e92ac45d23388ba467115546540e8c4a80e159501c5113b9aa226600cb90a85962150b2642996488543444aa6941502acef2a9a99a5501444666a668cc04ab199a6585242a0a812115888d4ab111a8ce2235444220255844046708808cd40712aa6269634c69a64989a4e540708ca812130502ecef3320a2222353bc448277888d4cd112099a22349828156994c4d466989a4613134caa626913484d32010a06602140cb8428196085032a10a04c14091444226a77844d4ab089a88a11414ca074c9341e0323111a6622234cac446892a20d1252a9a9de661d2ac223982502eb2e429c6588538c990a7192214e32c291a65a11c44b302a496605912cc0d0a2255bb4ca070211503a511115d95622bacb5107288846ecab08dd6494071114237541503a4ef2a82a2255713bcaae2888cdc4ef19b865885054c8a4e288149c51111389de2271444440191214d32e11f62491742c890a8d972151b2c42a36488546cb0a48e8888904cd110e2415140c9aa202889de0511331a9de6634cb0a4828888a04ef11402591844cba62693050012a6909aa202180ca84301590869b3010d365821a6c9843019154cd511088e9de111d334223a8884604ef08c065c8534cb10a6993214d324429a1661135444234e668469ab0a99aa2211413bc22826684504ab08a054d5235114226a884c4d26298539dd31348a26202224c4d2a7089a0d600ca8032803120149cac6698634c3a25cdcaecc98764b9c054a00a4893280b8df60ecb06c98740baa020992e4c95240c3c0619130a698544baa25951306695244297414a0102a451e810a958c310a3963be40d35cafb075573e8c1552094c44a6884483c09de020 else 0x940bf19aec6a225d8d422a05da656335442c6699758cd4eeb19a9556335112c668985024324a0369998235113046a11608d510b91a999723519ae46a115c8d330b11aa216234cbac48277588d2c4a0559556234b12817d63588d466b11a6096235112c46a994c8d270a048a2132353ba646932501b4cc991a9553235112646a114c8d304c09aa657134cc2e281185022d10a05da21408ac3a80e1875c4d32ca0455d971413328116555c4d466b89a65951408b281558154502e2a8a05cd407098a811622502aa50a0389dd40e93ba426a66502aa2aa04895540e8aa281d123501c444909a4c1408ac9a80d930501b304a88e60d7100c32812152604d2a498406095134c2a426a3388aec6708dd64d40aac9a800998999032f33206566640b1a80199299903233320a6567404b4aa8163502a92d112058d409119a81d29958eab24a00224d8234cb3043a666087326c11a1a5824019281d233608d322c10e6458234c1281559060a9c22c10e5c940e839281d16250148f2b120a656252b1ac5559060a0304b10ea652840cb2646a994990532992961d82409330481914c94b22991a4c940aa99281d266844d322a05d66052bacc0a4699314aeb22a006a65816c4b30366778ccd12cc09a259814209281d1826047302a0559dd81352ab026a33604d32aa07495540babb2e37e11502aaf2a0385c540e8cbac37d96544732ca00654540bac82a282668ccd320a8d36495134aa280e092544d02ca05f54540e9332817d81544d444a0745c5511d44280a571545bae2a89a8cd40528ba80a495a20d532c39aa218700bc2ea6a885d40532b29a59d6535444aa01879540532c180a2183013bb06025560c0532b9806617334bc2e66a885cc04aab98061e3300bac6602886080304a08e61d82352ab040183608d466c1006548234cc2e46a885c804aab9005cd723519ae40288501c2ceb11a9dd4070b1a800a99548d250a91aa215200cbaa46897549092ea94125d5234cb2a46a335480330991a4a132354426401974c8d26e991a9553200a0a80198388804aaa0388894070b92e26a88544d4eea89a8cd5134c1c220299461053298d5a21400d4ca62a699459032c98a94c540bb4ca2a81974c402c698a964931aab1a6355816090272a0064c93152cc28019324c6aaa8a00688931531128175814c6aa30988066131009c280e2884c40282a0456613134c3a6269864c4d2ec989a5d5313498a81d131502aa62a029661211ccb2426998502eb2aa045655400ccaa8176555022caa90805652100aa281767748402a8a045a652140c9a42a597503a326a0455e521403ca42816948500d290a0565214119a8116334854b24a045889408b2aa426993484d322a0458cd2134c0a812121503a510a0556554090aa28121714854ae2909a8cd40aaa9280e198484d282a0)) else (if i < 4 then 0xd8814c1406cd4ae29818409714c0c2e298280d9a95853030a8a60a03614530501b2829828019414c140baa0a60a074505305022a82982817d414c14090caa6298185d5314c0c2ca98a6061924c5303098a60a0454c530502ea4298280d9144c140aaaa260a05d44d30502ab309828121544c14090a9a60a04864930503a324982815598845303108a60a0459de55501b466cb28116558cd406d3bc44a036889965022cab11280da33889406d08b26a03628d97503a134b1a8116aa64940bf3bb24a03669c85409034c42a8019a62150240d190aa00668485409034042a8018a995502412ab24a0360e992503a074c92817633649406d2ac66811888992501b422c9280da33649408b19c22811864211608c153442026277645406d33322a04569c85405034c42a0281a22150140d090a80a06808540504aac8a80da33645406cd30a480a088991501b422c8a811611645406cd3532c0d369a996050152812a28277505406d2aa82a0368cd41501b324a0a80da22505406d08a82a03626931502a93498a8115924c1406d11260a03650530501b23098a614d314c1406c89a60a048aa9305022d3308a6061984c1408aaa260a04554d305022b249828116114c1406cd190a81406888540a034242a0502aa64940e854caaa0062a563500334e48b0439824c9408ad090a80c014991501b3434ca0501a624951be4c302a89a69892a20d34e42a80e085505406cd190aa0384c541503a34442a80e19850540ab444ef2a9aa22778ccd5112ac666a779563335334ab199a69e99548d0a4a0a80d998505400cd0931111aa2255888d4ef2ac4402888ce22353bc67110095633888d4ef2ac2202778ce11012ac67089a299984c54944cba62a5a824931aad312498d550531503a28298a80d8a6661214053b2a90f468e9960a034e4c44469a32562234d3532c09aaa997206032f11103019388851808c26298404c530503a34a98a61011348530815533010c0a2197086004298280daaa65421814432a10c0aa9930860510c9843028888a11353bc45089a95622844d34048ac4819858cd32ab19a6496334492c669635014b2cc1206598234bb304698250012c6c11a609406cc8b0481825014b0cb91a2054090c3ac46995589032ab11a64d6234b9ac46962500730e991a4c940babb26469954c8d264a002589323499280a597605030ec09a60540bacab028183604d2e6c09a6498140b93026932604d302a0292617134c328115835022b06b89a58d408ac12e26952503a2a4b89a4c97134b8a8039615014ac2a048585401cbb28019925450264a89a545401c4c26268954c4d2eaa0065954090c12626852503a130909a61d2134c32815585502eaeaa0745d52134c1a817583502ab06909a5cd40e8b9a426953502eb04909a54940baa92426932484d242a00e65 else (if i < 5 then 0x55404c306c8a80d973645406cc1322a03620991501b264c8a80daaa64540e955322a0552a222404c14b1120261a7a658134d1d32c09a6a581501b554cc280daaa661400d5532ea03666277501b5113ba80d8a6605408a53302a00e41c96605015333302689625581355532aa036aa995502435282b026277655406c4b20ac0a065581501b2b32aa80d8a99558130cc4aaa036a2255501b32f2aa80d896955813450caac098aa993501b4eec9a80d89640d81a6c9b02a0362a573604d352b9a80d9795cd406ccc466a036a2233501b32f19a80da778cd406c4b466c09a65633501b14cc0a815590249813155324a03666981500312c813028192605406cd4b04a03660981501b142c130269a95c9406c54aa4c09a6a5815022a50a930269a9149406cd20a4a0364a132604d25311280d9a960540aa54c44c09866222501b51111280d997889406c4b444c09a65622501b32711280d991605406cd4532b89a68e995c4d14ccc2e280a9a21713454d10b89861d71501b312c3a8019a95c540e8caae2a036661035c4c326b8a80d9925c5406c54b04b89a61d825c4d2ceb12e268a95497134c8ae2a0365e573501c352b0a8115a6a655134d1d32a89a6a551502eb26a8a80d992545406c54b04a89a2a622544c14b112a26191545406cc0aa2a0366a5515022af0b8aa26965545408ad22a2a0455c551501b30ea0a80d99850540babaa82a03660d41501b2e6a0a80d99250540bec1282a03620941501b2e4a0a80daaa505408a94a82a074661415022d10a0a811596505408b33282a04554941501b466a0a8115a6149411c99282a03666141502432ca0a8155a550540bac9282a05560541501b2e2a0a80d951505406cd4532989a69e994c4d34e4c26268a9a21313454d109898286884c4c14498a8154a24c5408acc262a04569d31501b144cba6268a24dd4070cba62a0362a5874c4d2f2c3a6269a94c540bad032a989869531501b32a98a80d8a99553130aa262a0366a531502ab5298a8121924c5406cb1ac4989a2a5524c7a35298a8115284c9313499262a0362a6224c4c1431126261914c5406c53302989a60531501b28298a8121414c54052a0a62a05d505315022a8298a817da8a652134d3d32909a69a99484d3474ca4268a9a21213454d10909869d21501b32e90a80d8a961d213453b2a909a29d25501c14ecaa4281a5485406d5532aa07465521501b152c2a42695a485408a54caa909855121501b34690a80daaa64d40bac9a42a0362a573484d152a9a42695464940e8c9242a03659d62484d352a9281d1a948540e8c8a42a0366a521502ab5290a8115785c52134b8a42a03650521501b22898a815531485406cd4aec981864930502eb0498280d8824c1406cd4ae498185c930501b352b126061298893030cc444981868530501b3029828 else 0x1b1aa992501b22690a60a0366d2aa64d406c8a26298280d9b82a655418c36654caa83186c8a99550630dc1531120c61b52a622418c36654c4483186d2aa64d40badc15308a0661b52a61140cc36454c2281986d8a584503305d321112c660ba41a2258cc57654d1081186d4a9a210230d99534420461b12a688408c57654caa81186e0a99550230d99532aa0461b12a655408c36e50caa8118aeca98450230dc15308a0461b52a611408c36654c2281186d8a58450230d914b08a0460ba64211608c174c8510b9182e99084572305d3212aac461785d982588d2f0b9b04991a6d4a9a210130d99534420261b22a688404c36c5151080986e0a99550130d99532aa0261b22a655404c37054c4480986d4a98890130d99531120261b72a222404c174c84aac0982e99088981305d321442e260ba64222544c174c851098986dca99553134db9532aa6260ba642554c4c152b1ac4989a2e99088931305d3214424260ba64255484c2ceb12e2909a2e9088893030d99431126060b1a21314c0c16498a60a045451314c140ba8a2629828155144c530503a22898a60a0452c6224c53030aa2a69828121b3296114c0c174a9c2298186d2aa64d408aaa2a698281149b54d30503a554b1a8115a858d408ad0ac6a04568d82501b34a99280d9a7605406cd2b02a03668d815022b46c0a80d9a2605408ad1302a03668d71501b346a8a8115a3545406cd12a2a04568951501b34498a8115a24c5406d55264a0366a532501b306c8a8116aa605408ac9b02a04564d615022d5498a8115a84c5408ac0a62a045aa9965022d10cb2811611659408b55326a045845935022b52b1a811633645408b55260a0366053050229452aa0c62aa65940ab5532ca04829622501b102c9a80daaa64d40aa5442281986a29958cd34f4cac669a58cd406cd1466a03668a9958cd554cbac668a3955406c54caab1982a62258cd352b1a81559658d40aacb2c6a0482a62258cc14ac9280daaa64940ba544aa81185cd92501b142c9280d881649406d55324a05514592501b15108a0461a6a658234d1d32c11a2a563608d324c1280d9a72458234d3922c120aa9825022b5240a8121a42054090d4ae4a0746a299588d34f4cac469a3a65623555330b11aa6508588c554cbac469a961d623454b0eb11a5e176588d1532aac460a95cd6234d3ac6b11a61d82588d2ecc12c46963609623555330991a2a6884c8c1454426461974c9406c45264a045aa9964c8d1532aa6461a94c9408abc2e6991a5cd32501b32499280d9876093234cb304991a60932501b2e6c126469a94c940aacc264a04529688404c145442026288645408ac3b22a036aa9915003554c8a811568645408b55322a0482a2)))
def poolRecord (i : Nat) : Nat × Nat :=
  if i < 93 then (0,0 + (i-0)*7) else
  if i < 586 then (1,651 + (i-93)*17) else
  if i < 1240 then (2,9032 + (i-586)*27) else
  if i < 1741 then (3,26690 + (i-1240)*37) else
  (4,45227 + (i-1741)*47)

def paidPath : Nat → Nat → List Sig → List Choice
  | 0,_,_ => []
  | n+1,ops,bank =>
    let read := fun i => if i = 14 then zero else if i = 15 then one else bank.getD i zero
    let c : Choice := (getFieldV ops 8 2,read (ops &&& 15),read (getFieldV ops 4 4))
    c :: paidPath n (ops >>> 10) (bank ++ [choiceVal c])

def sharedPool (g : Forest) (i : Nat) : Option BoundPool :=
  let n := (poolRecord i).1
  let pos := (poolRecord i).2
  (g.cols.read (packedAt poolWords pos 7)).bind fun ci =>
    let raw := vars g.mask
    materialize raw (paidPath n (packedAt poolWords (pos+7) (10*n)) raw) (subcube ci.1 ci.2.1) ci.2.2.2.2

theorem sharedValid {g : Forest} (cols : ∀ ci ∈ g.cols.values,
    Slice (vars g.mask) (targetOf g) (subcube ci.1 ci.2.1) ci.2.2.2.2)
    {i p} (hp : sharedPool g i = some p) : ValidPool (vars g.mask) (targetOf g) p := by
  unfold sharedPool at hp
  obtain ⟨ci,read,mat⟩ := Option.bind_eq_some_iff.mp hp
  exact materialize_sound (cols ci (g.cols.read_mem read)) mat

def nodePools (g : Forest) (ops depth : Nat) (bank : List Decor) (data : Nat → Nat)
    (cw nr st : Nat) : List BoundPool :=
  if g.cap = 15 then
    (getPairs data cw 0 nr st).filterMap (fun v => sharedPool g v.1)
  else (getPairs data cw depth nr st).filterMap (fun (a,b) => buildRule g ops depth bank a b)

theorem nodePoolsValid {g : Forest} (cols : ∀ ci ∈ g.cols.values,
    Slice (vars g.mask) (targetOf g) (subcube ci.1 ci.2.1) ci.2.2.2.2)
    {ops depth bank data cw nr st} {p} (hp : p ∈ nodePools g ops depth bank data cw nr st) :
    ValidPool (vars g.mask) (targetOf g) p := by
  unfold nodePools at hp
  split at hp
  · obtain ⟨_,_,h⟩ := List.mem_filterMap.mp hp
    exact sharedValid cols h
  · obtain ⟨⟨_,_⟩,_,h⟩ := List.mem_filterMap.mp hp
    exact buildRule_sound g cols h

def nodeVerified (g : Forest) (k i : Nat) :=
  let raw := wiresOf g
  let (num,depth,cw,iw,pw,offw,lw,data) := g.levels k
  let (ops,bank,ws) := readNode g k i
  let values := ws.map Prod.fst
  let start := num*(storedBits g depth+raw.length+depth)
  let pos := start+num*offw+packedAt data (start+i*offw) offw
  let nr := packedAt data pos 5
  let nl := packedAt data (pos+5) lw
  let st := pos+5+lw
  let rules := nodePools g ops depth bank data cw nr st
  let ls := fun tag => ((g.index k tag).bind (linkedSet g (k-1))).toList
  decide values.Nodup && !(values.contains (targetOf g)) &&
    (if k=0 then true else testAll (k,ws.length,ws,preCov ws,rules,ls) ws)

theorem nodeVerified_sound (g : Forest) (k i : Nat)
    (samples : properPairs (targetOf g) (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2))
    (cols : ∀ ci ∈ g.cols.values, Slice (vars g.mask) (targetOf g) (subcube ci.1 ci.2.1) ci.2.2.2.2)
    (names : ∀ x ∈ g.autos.toList, autoOK (targetOf g) (x.map swapRows) = true)
    (prior : k>0 → ∀ j < (g.levels (k-1)).1, Impossible (targetOf g) (k-1) (stateSet g (k-1) j).toFinset)
    (checked : nodeVerified g k i = true) : Impossible (targetOf g) k (stateSet g k i).toFinset := by
  simp only [nodeVerified,Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true',List.contains_eq_mem] at checked
  have hN := checked.1.1
  have hT : targetOf g ∉ stateSet g k i := by simpa [stateSet] using checked.1.2
  by_cases h0 : k=0
  · subst k
    intro t u lo h
    have ht : t=0 := by omega
    subst t
    generalize he : (stateSet g 0 i).toFinset = S at h
    have eqS : S = {_} := h (fun k _ S => k = 0 → S = {_}) (fun _ _ => rfl) (fun _ _ _ hn => by contradiction) (fun _ _ _ _ _ hn => by contradiction) rfl
    exact hT (List.mem_toFinset.mp ((he.trans eqS).symm ▸ Finset.mem_singleton_self _))
  apply node_sound (raw:=vars g.mask) samples _ hN hT _ _ (by simpa only [h0,if_false] using checked.2)
  · intro v hv
    apply decode_faithful _ _ _ _ _ (wires_faithful g) v
    exact (selectLive_sub _ _).subset hv
  · intro p hp
    exact nodePoolsValid cols hp
  · intro tag xs hx
    have e : ((g.index k tag).bind (linkedSet g (k-1)))=some xs := by simpa using hx
    obtain ⟨pair,_,h⟩ := Option.bind_eq_some_iff.mp e
    exact linkedSet_sound g _ names (prior (by omega)) h


def block (g : Forest) (k start : Nat) : Nat → Bool
  | 0 => true
  | n+1 => nodeVerified g k (start+n) && block g k start n
theorem block_at {g k start n} (h : block g k start n=true) (j : Nat) (lo : start≤j) (hi : j<start+n) :
    nodeVerified g k j=true := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [block,Bool.and_eq_true] at h
    by_cases eq : j=start+n
    · simpa [eq] using h.1
    · exact ih h.2 (by omega)
theorem block_merge {g k start a b} (h : block g k start a=true)
    (h' : block g k (start+a) b=true) : block g k start (a+b)=true := by
  induction b with
  | zero => simpa using h
  | succ b ih =>
    simp only [block,Bool.and_eq_true] at h'
    simp only [Nat.add_succ,block,Bool.and_eq_true]
    exact ⟨by simpa [Nat.add_assoc] using h'.1,ih h'.2⟩

def checkedTables (g : Forest) (top : Nat) :=
  ∀ k ≤ top, block g k 0 (g.levels k).1 = true
def graphValid (g : Forest) (prior : Nat → Nat) :=
  (chartSamples g.mask (fun j => (g.samples j).1) == BitVec.allOnes 768) &&
  (chartSamples g.mask (fun j => (g.samples j).2) == 0) &&
  g.cols.values.all (fun c => colCheck g.mask c prior) &&
  g.autos.toList.all (fun p => autoOK (targetOf g) (p.map swapRows))

theorem forest_all (g : Forest) (top : Nat) (prior : Nat → Nat)
    (lower : ∀ q, Lower (vars q) (graphGoal q) (prior q))
    (geometry : graphValid g prior = true) (rows : checkedTables g top) :
    ∀ k ≤ top, ∀ i < (g.levels k).1, Impossible (targetOf g) k (stateSet g k i).toFinset := by
  simp only [graphValid,Bool.and_eq_true,List.all_eq_true,beq_iff_eq] at geometry
  intro k
  induction k with
  | zero =>
    intro hk i hi
    apply nodeVerified_sound g 0 i (chart_pairs geometry.1.1.1 geometry.1.1.2)
      (fun x hx => col_sound _ prior lower (geometry.1.2 x hx)) geometry.2 (by omega)
    exact block_at (rows 0 hk) i (by omega) (by omega)
  | succ k ih =>
    intro hk i hi
    apply nodeVerified_sound g _ i (chart_pairs geometry.1.1.1 geometry.1.1.2)
      (fun x hx => col_sound _ prior lower (geometry.1.2 x hx)) geometry.2
      (fun _ => by simpa using ih (by omega))
    exact block_at (rows _ hk) i (by omega) (by omega)

def indexedRoot (g : Forest) (k i : Nat) (ws : List Sig) :=
  decide (i < (g.levels k).1) && sameWords (stateSet g k i) ws
theorem root_index {g top prior k i ws} (low : ∀ q, Lower (vars q) (graphGoal q) (prior q))
    (geom : graphValid g prior = true) (blocks : checkedTables g top) (le : k ≤ top)
    (idx : indexedRoot g k i ws = true) : Impossible (targetOf g) k ws.toFinset := by
  simp only [indexedRoot,Bool.and_eq_true,decide_eq_true_eq] at idx
  rw [←sameWords_sound idx.2]
  exact forest_all g top prior low geom blocks _ le i idx.1

theorem lower_forest {g prior i hints} (low : ∀ q, Lower (vars q) (graphGoal q) (prior q))
    (geom : graphValid g prior = true) (blocks : checkedTables g g.cap)
    (idx : indexedRoot g g.cap i (vars g.mask) = true) (hp : properB (targetOf g) = true)
    (ess : checkEssential (targetOf g) (vars g.mask) (graphPairs g.mask hints) = true)
    (all : (graphPairs g.mask hints).map Prod.fst = vars g.mask) :
    Lower (vars g.mask) (targetOf g) (g.cap+1) := by
  apply lower_impossible (proper_of _ hp) _ (root_index low geom blocks (Nat.le_refl _) idx)
  intro a ha
  apply essential_ok ess a
  rw [all]
  exact List.mem_toFinset.mpr ha

theorem lower_discard {g prior ci hints} (low : ∀ q, Lower (vars q) (graphGoal q) (prior q))
    (ok : colCheck g.mask ci prior = true)
    (hp : properB (targetOf g) = true)
    (ess : checkEssential (targetOf g) (vars g.mask) (graphPairs g.mask hints) = true)
    (all : (graphPairs g.mask hints).map Prod.fst = vars g.mask)
    (nd : (vars g.mask).Nodup)
    (cut : poolCut (subcube ci.1 ci.2.1) ci.2.2.2.2 g.cap 0 (vars g.mask) (vars g.mask)=true) :
    Lower (vars g.mask) (targetOf g) (g.cap+1) := by
  apply lower_impossible (proper_of _ hp) _ (poolCut_sound (col_sound ci prior low ok) [] rfl nd cut)
  intro a ha
  apply essential_ok ess a
  rw [all]
  exact List.mem_toFinset.mpr ha

def Known (entries : List (Nat × Nat)) := ∀ e ∈ entries, Lower (vars e.1) (graphGoal e.1) e.2
def extendKnown (old : List (Nat × Nat)) (L : Nat) (relabels : List (Nat × List Nat)) :=
  relabels.map (fun v => (v.1,L)) ++ old
theorem extendKnown_ok {old L m relabels} (previous : Known old)
    (main : Lower (vars m) (graphGoal m) L)
    (ok : relabels.all (fun v => relabelOK v.1 m v.2) = true) :
    Known (extendKnown old L relabels) := by
  intro e he
  rcases List.mem_append.mp he with hx | h
  · obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hx
    exact relabel_of (List.all_eq_true.mp ok _ hv) main
  · exact previous e h
theorem baseKnown : Known [] := by simp [Known]
def lanePlace (v : Nat) (upper : Nat) := 2^769*upper+v
def combineLanes {α : Type} (f : α → Bits) : List α → Nat
  | [] => 0
  | x::xs => lanePlace (f x).toNat (combineLanes f xs)
def units : Nat → Nat
  | 0 => 0
  | n+1 => lanePlace 1 (units n)
theorem laneSmall (x : Bits) : x.toNat < 2^769 :=
  lt_trans x.isLt (by decide +kernel)
theorem place_and (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u &&& lanePlace b.toNat v = lanePlace (a &&& b).toNat (u &&& v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_and,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<769 <;> simp only [h,ite_true,ite_false,BitVec.toNat_and,Nat.testBit_and]
theorem place_or (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u ||| lanePlace b.toNat v = lanePlace (a ||| b).toNat (u ||| v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_or,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<769 <;> simp only [h,ite_true,ite_false,BitVec.toNat_or,Nat.testBit_or]
theorem place_xor (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u ^^^ lanePlace b.toNat v = lanePlace (a ^^^ b).toNat (u ^^^ v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_xor,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<769 <;> simp only [h,ite_true,ite_false,BitVec.toNat_xor,Nat.testBit_xor]
theorem lanes_and {α} (f g : α → Bits) (xs) :
    combineLanes f xs &&& combineLanes g xs = combineLanes (fun x => f x &&& g x) xs := by
  induction xs with
  | nil => simp [combineLanes]
  | cons a xs ih => simp only [combineLanes,place_and,ih]
theorem lanes_or {α} (f g : α → Bits) (xs) :
    combineLanes f xs ||| combineLanes g xs = combineLanes (fun x => f x ||| g x) xs := by
  induction xs with
  | nil => simp [combineLanes]
  | cons a xs ih => simp only [combineLanes,place_or,ih]
theorem lanes_xor {α} (f g : α → Bits) (xs) :
    combineLanes f xs ^^^ combineLanes g xs = combineLanes (fun x => f x ^^^ g x) xs := by
  induction xs with
  | nil => simp [combineLanes]
  | cons a xs ih => simp only [combineLanes,place_xor,ih]
theorem broadcast {α} (a : Bits) (xs : List α) :
    units xs.length * a.toNat = combineLanes (fun _ => a) xs := by
  induction xs with
  | nil => simp [units,combineLanes]
  | cons v xs ih => simp only [List.length_cons,units,combineLanes,lanePlace,Nat.add_mul,Nat.mul_assoc,ih,Nat.one_mul]

def fullMarks (r packed : Nat) := ((packed+r) >>> 768) &&& r
theorem unit_bit (n i : Nat) (hi : i<n) : (units n).testBit (769*i) = true := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
    rw [units,lanePlace,Nat.testBit_two_pow_mul_add _ (by decide +kernel : 1 < 2^769)]
    cases i with
    | zero => simp
    | succ i =>
      have di : 769*(i+1)-769=769*i := by omega
      have ge : ¬769*(i+1)<769 := by omega
      simp only [ge,ite_false,di]
      exact ih _ (by omega)
set_option maxRecDepth 8192 in
theorem guardBit (a : Bits) : (a.toNat+1).testBit 768 = (a==BitVec.allOnes 768) := by
  by_cases h : a=BitVec.allOnes 768
  · subst a
    decide +kernel
  · have lim := a.isLt
    have ne : a.toNat ≠ 2^768-1 := by
      intro eq
      apply h
      apply BitVec.eq_of_toNat_eq
      simpa only [BitVec.toNat_allOnes] using eq
    have lt : a.toNat+1<2^768 := by omega
    rw [Nat.testBit_eq_false_of_lt lt]
    exact (beq_eq_false_iff_ne.mpr h).symm

set_option maxRecDepth 8192 in
theorem mark_at {α} (f : α → Bits) (xs : List α) (i : Nat) (hi : i<xs.length) :
    (fullMarks (units xs.length) (combineLanes f xs)).testBit (769*i) =
      (f xs[i]==BitVec.allOnes 768) := by
  simp only [fullMarks,Nat.testBit_and,Nat.testBit_shiftRight,unit_bit _ _ hi,Bool.and_true]
  induction xs generalizing i with
  | nil => simp at hi
  | cons a xs ih =>
    simp only [combineLanes,List.length_cons,units,lanePlace]
    have sum (u v x : Nat) : 2^769*u+x+(2^769*v+1)=2^769*(u+v)+(x+1) := by omega
    rw [sum,Nat.testBit_two_pow_mul_add _ (show (f a).toNat+1<2^769 from by have := (f a).isLt; omega)]
    have hi' : i < xs.length+1 := hi
    cases i with
    | zero => simpa using guardBit (f a)
    | succ i =>
      have ge : ¬769*(i+1)+768<769 := by omega
      have di : 769*(i+1)+768-769=769*i+768 := by omega
      simp only [ge,ite_false,di,List.getElem_cons_succ]
      apply ih i (by omega)


abbrev PackedSig := Nat × Nat
abbrev PackedCov := Nat × Nat × Nat

def packedSig {α} (s : α → Signals) (xs : List α) : PackedSig :=
  (combineLanes (fun x => (s x).1) xs,combineLanes (fun x => (s x).2) xs)
def packedCov {α} (c : α → Cov) (xs : List α) : PackedCov :=
  (combineLanes (fun x => (c x).1) xs,combineLanes (fun x => (c x).2.1) xs,
   combineLanes (fun x => (c x).2.2) xs)
def packedColumn (d : Bool) (a : PackedSig) :=
  if d then a.1 ^^^ (a.1 &&& a.2) else a.1 ^^^ a.2

theorem xor_meet (a b : Bits) : a ^^^ (a &&& b) = a &&& ~~~b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_xor,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases b.getLsbD i <;> rfl

theorem packed_column {α} (s : α → Signals) (xs : List α) (d : Bool) :
    packedColumn d (packedSig s xs) = combineLanes (fun x => column d (s x)) xs := by
  cases d <;> simp only [packedColumn,packedSig,column,Bool.false_eq_true,ite_false,ite_true,lanes_and,lanes_xor,xor_meet]

def packedOp (full : Nat) (op : Nat) (a b : PackedSig) : PackedSig :=
  if op=2 then (full ^^^ a.1,full ^^^ a.2) else if op=1 then (a.1 ||| b.1,a.2 ||| b.2)
  else (a.1 &&& b.1,a.2 &&& b.2)
theorem top_xor (a : Bits) : BitVec.allOnes 768 ^^^ a = ~~~a := BitVec.allOnes_xor
theorem packed_op {α} (a b : α → Decor) (xs : List α) (op : Nat) :
    packedOp (units xs.length*(BitVec.allOnes 768).toNat) op
      (packedSig (fun x => (a x).2) xs) (packedSig (fun x => (b x).2) xs) =
    packedSig (fun x => (movedDecor op (a x) (b x)).2) xs := by
  by_cases un : op=2
  · simp only [packedOp,un,ite_true,packedSig,broadcast,lanes_xor,top_xor,movedDecor,codeDecor,dneg]
  · by_cases one : op=1 <;> simp [packedOp,un,one,packedSig,lanes_or,lanes_and,movedDecor,codeDecor,dbin]

def takePacked (c : PackedCov) (a b : Nat) (un ka kb : Bool) :=
  let without1 := fun w => c.1 ^^^ (c.1 &&& (c.2.1 &&& w))
  let without2 := c.1 ^^^ (c.1 &&& ((c.2.1 &&& (a ||| b)) ||| (c.2.2 &&& (a &&& b))))
  if un then (if ka then c.1 else without1 a)
  else if ka then (if kb then c.1 else without1 b)
  else if kb then without1 a else without2

theorem takePacked_ok {α} (c : α → Cov) (a b : α → Bits) (xs : List α) (un ka kb : Bool) :
    takePacked (packedCov c xs) (combineLanes a xs) (combineLanes b xs) un ka kb =
    combineLanes (fun x => restCov (c x) (a x) (b x) un ka kb) xs := by
  cases un <;> cases ka <;> cases kb <;>
    simp only [takePacked,packedCov,lanes_and,lanes_or,lanes_xor,xor_meet,restCov,takeOne,takeTwo,
      Bool.false_eq_true,ite_false,ite_true]

def contextWire (c : NodeContext) (i : Nat) := c.2.2.1.getD i defaultDecor
def checkAt (c : NodeContext) (i j op : Nat) (ka kb : Bool) :=
  let a := contextWire c i
  let b := contextWire c j
  evalMove c op a b (movedDecor op a b) ka kb
def combField (c : NodeContext) (d un ka kb : Bool) (op i j : Nat) :=
  let a := contextWire c i
  let b := contextWire c j
  restCov (getCov c.2.2.2.1 d) (column d a.2) (column d b.2) un ka kb |||
    column d (movedDecor op a b).2

def onMarks {α : Type} (f : α → Bool) (mask : Nat) : List α → Bool
  | [] => true
  | x::xs => if mask=0 then true else
    ((mask &&& 1 == 0) || f x) && onMarks f (mask >>> 769) xs
theorem marked_ok {α} (f : α → Bool) (mask : Nat) (xs : List α) (i : Nat) (hi : i<xs.length)
    (bitOn : mask.testBit (769*i)=true) (ok : onMarks f mask xs=true) : f xs[i]=true := by
  induction xs generalizing mask i with
  | nil => simp at hi
  | cons x xs ih =>
    have ne : mask≠0 := by intro e; simp [e] at bitOn
    simp only [onMarks,ne,ite_false,Bool.and_eq_true,Bool.or_eq_true,beq_iff_eq] at ok
    cases i with
    | zero =>
      have nonzero : mask &&& 1 ≠ 0 := by
        intro he
        have at0 := congrArg (fun n : Nat => n.testBit 0) he
        simp only [Nat.testBit_and] at at0
        change mask.testBit 0=true at bitOn
        simp [bitOn] at at0
      exact ok.1.resolve_left nonzero
    | succ i =>
      apply ih (mask:=mask >>> 769) (i:=i) (by simpa using hi) _ ok.2
      simpa only [Nat.testBit_shiftRight,Nat.mul_succ,Nat.add_comm] using bitOn

abbrev Batch := Nat × Nat × Nat × List PackedSig × PackedCov × PackedCov
def makeBatch (k n : Nat) (xs : List NodeContext) : Batch :=
  (k,n,units xs.length,(List.range n).map (fun i => packedSig (fun c => (contextWire c i).2) xs),
    packedCov (fun c => c.2.2.2.1.1) xs,packedCov (fun c => c.2.2.2.1.2) xs)
def laneWire (b : Batch) (i : Nat) := b.2.2.2.1.getD i (0,0)
theorem laneWire_at (k n) (xs) {i : Nat} (h : i<n) :
    laneWire (makeBatch k n xs) i = packedSig (fun c => (contextWire c i).2) xs := by
  simp [laneWire,makeBatch,List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_range,h]

def availableMasked (p : BoundPool) (m : Sig) :=
  m==zero || m==p.domain || (p.wires.map (masked p.domain)).any (fun v => v==m)
theorem available_mask (p : BoundPool) (x : Sig) :
    availableB p.domain p.wires x = availableMasked p (masked p.domain x) := rfl

def constantLoss (p : Decor → Bool) (a : Decor) (keep : Bool) :=
  if keep then 0 else (p a).toNat
theorem lossBound (p : Decor → Bool) (ws : List Decor) (a : Decor) (keep : Bool) :
    ws.countP p ≤ (delOne ws a keep).countP p + constantLoss p a keep := by
  cases keep
  · simp only [delOne,Bool.false_eq_true,ite_false,constantLoss,List.countP_erase]
    split
    next h => simp [h.2]; omega
    next => omega
  · simp [delOne,constantLoss]

theorem keptCount (p : Decor → Bool) (ws : List Decor) (a b : Decor) (un ka kb : Bool) :
    ws.countP p - constantLoss p a ka - constantLoss p b (un || kb) ≤
    (opKeep un ka kb a b ws).countP p := by
  have h1 := lossBound p ws a ka
  have h2 := lossBound p (delOne ws a ka) b kb
  cases un <;> simp only [opKeep,delTwo,Bool.false_eq_true,ite_false,ite_true,
    Bool.false_or,Bool.true_or] <;> first | omega | simp [constantLoss]; omega

abbrev QuickPool := BoundPool × Nat × Bool
def summarizePool (ws : List Decor) (p : BoundPool) : QuickPool :=
  (p,ws.countP (fun w => isMaskedConstant p.domain w.1),
     ws.all (fun w => availableB p.domain p.wires w.1))
def fastCost (s : QuickPool) (k : Nat) (a b : Decor) (op : Nat) (ka kb : Bool) :=
  if !s.2.2 then false else
  let p := s.1
  let un := op==2
  let const := fun w : Decor => isMaskedConstant p.domain w.1
  let z := choiceVal (movedChoice op a b)
  let zm := masked p.domain z
  let zc := isMaskedConstant p.domain z
  let cm := s.2.1 - constantLoss const a ka - constantLoss const b (un || kb) + zc.toNat
  let free := zc || zm==masked p.domain a.1 || zm==masked p.domain b.1
  decide (k+p.paid+(!free).toNat < p.bound+cm)

theorem fastCost_good {p k ws a b op ka kb} (ha : a∈ws) (hb : b∈ws)
    (h : fastCost (summarizePool ws p) k a b op ka kb=true) :
    scalarPoolCut p k ((opKeep (op==2) ka kb a b ws).map Prod.fst) (movedChoice op a b)=true := by
  let z := choiceVal (movedChoice op a b)
  let const := fun w : Decor => isMaskedConstant p.domain w.1
  let free := isMaskedConstant p.domain z || masked p.domain z==masked p.domain a.1 ||
      masked p.domain z==masked p.domain b.1
  let rest := opKeep (op==2) ka kb a b ws
  have ck := keptCount const ws a b (op==2) ka kb
  change ws.countP const - constantLoss const a ka - constantLoss const b ((op==2) || kb) ≤ rest.countP const at ck
  by_cases all : ws.all (fun w => availableB p.domain p.wires w.1)=true
  · have hav := List.all_eq_true.mp all
    have ready : free=true → availableB p.domain p.wires z=true := by
      intro f
      simp only [free,Bool.or_eq_true,beq_iff_eq] at f
      rcases f with (zc|za)|zb
      · simp only [availableB,isMaskedConstant,Bool.or_eq_true] at zc ⊢
        exact Or.inl zc
      · rw [available_mask,za,←available_mask]
        exact hav _ ha
      · rw [available_mask,zb,←available_mask]
        exact hav _ hb
    have extra : (!availableB p.domain p.wires z).toNat ≤ (!free).toNat := by
      cases hf : free <;> cases he : availableB p.domain p.wires z <;> simp_all
    have hs : (rest.map Prod.fst).all (availableB p.domain p.wires)=true := by
      apply List.all_eq_true.mpr
      intro _ hm
      obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hm
      exact hav w ((keep_sub ws a b (op==2) ka kb).subset hw)
    have opOK : choiceOK p.domain p.wires (movedChoice op a b)=true := by
      simp [choiceOK,movedChoice,hav _ ha,hav _ hb]
    simp only [fastCost,summarizePool,all,Bool.not_true,Bool.false_eq_true,ite_false,decide_eq_true_eq] at h
    change k+p.paid+(!free).toNat < p.bound+(ws.countP const - constantLoss const a ka -
        constantLoss const b ((op==2)||kb)+(isMaskedConstant p.domain z).toNat) at h
    dsimp only [rest] at hs
    simp only [scalarPoolCut,hs,opOK,Bool.or_true,Bool.and_true,decide_eq_true_eq,List.countP_cons,
      List.countP_map,Function.comp_def]
    change k+p.paid+(!availableB p.domain p.wires z).toNat <
      p.bound+(rest.countP const + if isMaskedConstant p.domain z then 1 else 0)
    cases hc : isMaskedConstant p.domain z <;> simp [hc] at h ⊢ <;> omega
  · simp [fastCost,summarizePool,all] at h

def quickAt (c : NodeContext) (i j op : Nat) (ka kb : Bool) :=
  let a := contextWire c i
  let b := contextWire c j
  (c.2.2.2.2.1.map (summarizePool c.2.2.1)).any (fun s => fastCost s (c.1-1) a b op ka kb)

theorem quickAt_good {c i j op ka kb} (hi : i<c.2.2.1.length) (hj : j<c.2.2.1.length)
    (h : quickAt c i j op ka kb=true) : checkAt c i j op ka kb=true := by
  have mem (t) (ht : t<c.2.2.1.length) : contextWire c t ∈ c.2.2.1 := by
    simp [contextWire,List.getD_eq_getElem?_getD,ht]
  obtain ⟨_,hm,ok⟩ := List.any_eq_true.mp h
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hm
  have closed := fastCost_good (mem _ hi) (mem _ hj) ok
  have cut : c.2.2.2.2.1.any (fun p => scalarPoolCut p (c.1-1)
      ((opKeep (op==2) ka kb (contextWire c i) (contextWire c j) c.2.2.1).map Prod.fst)
      (movedChoice op (contextWire c i) (contextWire c j)))=true :=
    List.any_eq_true.mpr ⟨p,hp,closed⟩
  simp only [checkAt,evalMove,closeChild,cut,Bool.or_true]
  repeat' split
  all_goals rfl

def fallbackAt (c : NodeContext) (i j op : Nat) (ka kb : Bool) :=
  (if i<c.2.2.1.length ∧ j<c.2.2.1.length then quickAt c i j op ka kb else false) ||
    checkAt c i j op ka kb
theorem fallback_sound {c i j op ka kb} (h : fallbackAt c i j op ka kb=true) :
    checkAt c i j op ka kb=true := by
  simp only [fallbackAt,Bool.or_eq_true] at h
  rcases h with h | h
  · split at h
    next yes => exact quickAt_good yes.1 yes.2 h
    next => contradiction
  · exact h
def batchMove (b : Batch) (xs : List NodeContext) (i j op : Nat) (ka kb : Bool) :=
  let (k,n,r,_,u,v) := b
  let un := op==2
  let len := 1+(n-(if ka then 0 else 1)-(if un || kb then 0 else 1))
  if len>k then true else
    let d := len==k
    let a := laneWire b i
    let b' := laneWire b j
    let z := packedOp (r*(BitVec.allOnes 768).toNat) op a b'
    let cov := if d then v else u
    let mask := fullMarks r (takePacked cov (packedColumn d a) (packedColumn d b') un ka kb ||| packedColumn d z)
    onMarks (fun c => fallbackAt c i j op ka kb) mask xs

theorem batchMove_at (k n) (xs : List NodeContext) {i j op : Nat} {ka kb}
    (hi : i<n) (hj : j<n) {q : Nat} (hq : q<xs.length)
    (budget : xs[q].1=k) (arity : xs[q].2.1=n)
    (pass : batchMove (makeBatch k n xs) xs i j op ka kb=true) :
    checkAt xs[q] i j op ka kb=true := by
  let len := 1+(n-(if ka then 0 else 1)-(if (op==2) || kb then 0 else 1))
  let d := len==k
  have eval : checkAt xs[q] i j op ka kb =
      if len>k then true else if combField xs[q] d (op==2) ka kb op i j != BitVec.allOnes 768 then true
      else if !properB (movedDecor op (contextWire xs[q] i) (contextWire xs[q] j)).1 ||
        xs[q].2.2.1.any (fun v => v.1==(movedDecor op (contextWire xs[q] i) (contextWire xs[q] j)).1)
      then true else closeChild xs[q].2.2.2.2.1 xs[q].2.2.2.2.2 (k-1)
        ((opKeep (op==2) ka kb (contextWire xs[q] i) (contextWire xs[q] j) xs[q].2.2.1).map Prod.fst)
        (movedChoice op (contextWire xs[q] i) (contextWire xs[q] j)) := by
    simp only [checkAt,evalMove,budget,arity,len,d,combField] <;> rfl
  by_cases small : len>k
  · simp [eval,small]
  · let r := units xs.length
    let a := laneWire (makeBatch k n xs) i
    let b := laneWire (makeBatch k n xs) j
    let cov := if d then packedCov (fun c : NodeContext => c.2.2.2.1.2) xs
            else packedCov (fun c : NodeContext => c.2.2.2.1.1) xs
    change (if len>k then true else onMarks _ (fullMarks r
       (takePacked cov (packedColumn d a) (packedColumn d b) (op==2) ka kb |||
        packedColumn d (packedOp (r*(BitVec.allOnes 768).toNat) op a b))) xs) = true at pass
    rw [if_neg small] at pass
    have chosen : cov = packedCov (fun c => getCov c.2.2.2.1 d) xs := by
      dsimp only [cov]
      cases d <;> rfl
    have ca : a = _ := laneWire_at k n xs hi
    have cb : b = _ := laneWire_at k n xs hj
    dsimp only [r] at pass
    rw [ca,cb,packed_op,packed_column,packed_column,packed_column,chosen,takePacked_ok,lanes_or] at pass
    by_cases hit : combField xs[q] d (op==2) ka kb op i j = BitVec.allOnes 768
    · apply fallback_sound
      apply marked_ok _ _ _ q hq _ pass
      rw [mark_at _ _ _ hq]
      exact beq_iff_eq.mpr hit
    · rw [eval,if_neg small,if_pos (bne_iff_ne.mpr hit)]


def batchPair (b : Batch) (xs : List NodeContext) (i j op : Nat) :=
  let f := batchMove b xs i j op
  f false false && f true false && f false true && f true true
def batchRow (b : Batch) (xs : List NodeContext) (i : Nat) (js : List Nat) :=
  batchMove b xs i i 2 false false && batchMove b xs i i 2 true true &&
    js.all (fun j => batchPair b xs i j 0 && batchPair b xs i j 1)
def batchRows (b : Batch) (xs : List NodeContext) : List Nat → Bool
  | [] => true
  | i::js => batchRow b xs i js && batchRows b xs js

theorem batchRows_at (k n) (xs : List NodeContext) {q : Nat} (hq : q<xs.length)
    (budget : xs[q].1=k) (arity : xs[q].2.1=n) (js : List Nat)
    (bounds : ∀ j ∈ js, j<n) (allRows : batchRows (makeBatch k n xs) xs js=true) :
    testAll xs[q] (js.map (contextWire xs[q])) = true := by
  induction js with
  | nil => rfl
  | cons i js ih =>
    simp only [batchRows,Bool.and_eq_true,batchRow,List.all_eq_true] at allRows
    simp only [List.map_cons,testAll,testRow,Bool.and_eq_true,List.all_eq_true,List.mem_map]
    have hi := bounds i List.mem_cons_self
    have check := @batchMove_at k n xs
    refine ⟨⟨⟨check hi hi hq budget arity allRows.1.1.1,check hi hi hq budget arity allRows.1.1.2⟩,?_⟩,
      ih (fun j hj => bounds j (List.mem_cons_of_mem _ hj)) allRows.2⟩
    rintro _ ⟨j,hj,rfl⟩
    have hj' := bounds j (List.mem_cons_of_mem _ hj)
    have both := allRows.1.2 j hj
    have opCheck (d : Bool) (pass : batchPair (makeBatch k n xs) xs i j (if d then 1 else 0)=true) :
        testPair xs[q] (contextWire xs[q] i) (contextWire xs[q] j) d=true := by
      simp only [batchPair,Bool.and_eq_true] at pass
      simp only [testPair,Bool.and_eq_true]
      exact ⟨⟨⟨check hi hj' hq budget arity pass.1.1.1,check hi hj' hq budget arity pass.1.1.2⟩,
        check hi hj' hq budget arity pass.1.2⟩,check hi hj' hq budget arity pass.2⟩
    exact ⟨opCheck false both.1,opCheck true both.2⟩

def runBatch (k n : Nat) (xs : List NodeContext) :=
    batchRows (makeBatch k n xs) xs (List.range n)
theorem runBatch_at {k n} {xs : List NodeContext} {q} (hq : q<xs.length)
    (hb : xs[q].1=k) (ha : xs[q].2.1=n) (hn : xs[q].2.2.1.length=n)
    (pass : runBatch k n xs=true) : testAll xs[q] xs[q].2.2.1=true := by
  have all := batchRows_at k n xs hq hb ha (List.range n) (fun _ => List.mem_range.mp) pass
  have eq : (List.range n).map (contextWire xs[q]) = xs[q].2.2.1 := by
    apply List.ext_getElem
    · simp [hn]
    · intro i h1 h2
      simp [contextWire,List.getD_eq_getElem?_getD,h2]
  rwa [eq] at all

def contextOf (g : Forest) (k i : Nat) : NodeContext :=
  let raw := wiresOf g
  let (num,depth,cw,iw,pw,offw,lw,data) := g.levels k
  let (ops,bank,ws) := readNode g k i
  let start := num*(storedBits g depth+raw.length+depth)
  let pos := start+num*offw+packedAt data (start+i*offw) offw
  let nr := packedAt data pos 5
  let nl := packedAt data (pos+5) lw
  let st := pos+5+lw
  let rules := nodePools g ops depth bank data cw nr st
  let ls := fun tag => ((g.index k tag).bind (linkedSet g (k-1))).toList
  (k,ws.length,ws,preCov ws,rules,ls)


def prelim (T : Sig) (c : NodeContext) :=
  let ws := c.2.2.1.map Prod.fst
  decide ws.Nodup && !(ws.contains T)
theorem from_context (g : Forest) (k i : Nat) :
    nodeVerified g k i = (prelim (targetOf g) (contextOf g k i) &&
      (if k=0 then true else testAll (contextOf g k i) (contextOf g k i).2.2.1)) := rfl

theorem makeBlock {g k start n} (h : ∀ (i : Nat), start ≤ i → i < start + n → nodeVerified g k i = true) :
    block g k start n=true := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [block,Bool.and_eq_true]
    exact ⟨h _ (by omega) (by omega),ih (fun i le lt => h i le (by omega))⟩

def contexts (g : Forest) (k start n : Nat) :=
  ((List.range n).map (start+·)).map (contextOf g k)
def header (g : Forest) (k start n ar : Nat) :=
  (contexts g k start n).all (fun c => c.2.1==ar && prelim (targetOf g) c)
def rowCut (g : Forest) (k start n ar lo len : Nat) :=
  let xs := contexts g k start n
  let b := makeBatch k ar xs
  (List.range len).all (fun d =>
    let i := lo+d
    batchRow b xs i (List.range' (i+1) (ar-(i+1))))
theorem rowCut_at {g k start n ar lo len} (h : rowCut g k start n ar lo len=true)
    (i : Nat) (l : lo ≤ i) (r : i < lo+len) :
    batchRow (makeBatch k ar (contexts g k start n)) (contexts g k start n)
      i (List.range' (i+1) (ar-(i+1)))=true := by
  have ha := List.all_eq_true.mp h (i-lo) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le l] using ha

theorem rowCut_merge {g k start n ar lo a b}
    (h : rowCut g k start n ar lo a=true) (t : rowCut g k start n ar (lo+a) b=true) :
    rowCut g k start n ar lo (a+b)=true := by
  apply List.all_eq_true.mpr
  intro j hj
  have jlt := List.mem_range.mp hj
  by_cases first : j<a
  · exact rowCut_at h (lo+j) (by omega) (by omega)
  · exact rowCut_at t (lo+j) (by omega) (by omega)

theorem cutsRun {g k start n ar} (h : rowCut g k start n ar 0 ar=true) :
    runBatch k ar (contexts g k start n)=true := by
  let xs := contexts g k start n
  have go (lo num : Nat) (eq : lo+num=ar) :
      batchRows (makeBatch k ar xs) xs (List.range' lo num)=true := by
    induction num generalizing lo with
    | zero => rfl
    | succ num ih =>
      simp only [List.range'_succ,batchRows,Bool.and_eq_true]
      refine ⟨?_,ih (lo+1) (by omega)⟩
      have ok := rowCut_at h lo (by omega) (by omega)
      simpa only [show ar-(lo+1)=num by omega] using ok
  unfold runBatch
  rw [List.range_eq_range']
  exact go 0 ar (by omega)

theorem cutsBlock {g k start n ar} (hd : header g k start n ar=true)
    (h : rowCut g k start n ar 0 ar=true) : block g k start n=true := by
  apply makeBlock
  intro i lo hi
  let xs := contexts g k start n
  have hm : contextOf g k i ∈ xs := by
    apply List.mem_map.mpr
    exact ⟨i,List.mem_map.mpr ⟨i-start,List.mem_range.mpr (by omega),by omega⟩,rfl⟩
  obtain ⟨q,hq,e⟩ := List.getElem_of_mem hm
  have one := List.all_eq_true.mp hd _ hm
  simp only [Bool.and_eq_true,beq_iff_eq] at one
  have hb : xs[q].1=k := by rw [e]; rfl
  have ha : xs[q].2.1=ar := e ▸ one.1
  have hn : xs[q].2.2.1.length=ar := by rw [e]; exact one.1
  rw [from_context,Bool.and_eq_true]
  refine ⟨one.2,?_⟩
  split
  · rfl
  · exact e ▸ runBatch_at hq hb ha hn (cutsRun h)

def boxes (g : Forest) (k start n ar lo num : Nat) : Nat → Prop
  | 0 => rowCut g k start n ar lo num=true
  | d+1 => boxes g k start n ar lo (num/2) d ∧ boxes g k start n ar (lo+num/2) (num-num/2) d
theorem boxesCut {g k start n ar lo num d} (h : boxes g k start n ar lo num d) :
    rowCut g k start n ar lo num=true := by
  induction d generalizing lo num with
  | zero => exact h
  | succ d ih =>
    have v := rowCut_merge (ih h.1) (ih h.2)
    simpa only [Nat.add_sub_of_le (Nat.div_le_self num 2)] using v

def cells (g : Forest) (k start n ar rows : Nat) : Nat → Prop
  | 0 => header g k start n ar=true ∧ boxes g k start n ar 0 ar rows
  | d+1 => cells g k start (n/2) ar rows d ∧ cells g k (start+n/2) (n-n/2) ar rows d
theorem cellsBlock {g k start n ar rows d} (h : cells g k start n ar rows d) :
    block g k start n=true := by
  induction d generalizing start n with
  | zero => exact cutsBlock h.1 (boxesCut h.2)
  | succ d ih =>
    have v := block_merge (ih h.1) (ih h.2)
    simpa only [Nat.add_sub_of_le (Nat.div_le_self n 2)] using v

def listPieces {α} (f : α → Bool) (xs : List α) : Nat → Prop
  | 0 => xs.all f=true
  | d+1 => listPieces f (xs.take (xs.length/2)) d ∧ listPieces f (xs.drop (xs.length/2)) d
theorem listPieces_all {α f xs d} (h : @listPieces α f xs d) : xs.all f=true := by
  induction d generalizing xs with
  | zero => exact h
  | succ d ih =>
    have ap : ((xs.take (xs.length/2)) ++ (xs.drop (xs.length/2))).all f=true := by
      simp only [List.all_append,ih h.1,ih h.2,Bool.and_self]
    simpa only [List.take_append_drop] using ap
def g15d3 (i : Nat) : Nat := 0xf
def g15l3 : Packing := (1,0,0,0,1,0,0,g15d3)
def g15samples : Array (Bits × Bits) := #[(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffbaf3ea78de4d799d,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff450cc90c3c245919),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdf7ff8fe9f9b7ed5,0x20812421801324c4),(0xefbdbf97f9f6bf6a,0x102a401415600a0a),(0xf3a9d7437375f5ba,0xfc028ab620235b0),(0,0),(0,0),(0,0),(0,0),(0,0)]
def g15columns : IndexTree ColumnInfo := (IndexTree.leaf [])
def g15autos : Array (List Nat) := #[[],[33,48]]
def g15levels : Nat → Packing
  | 3 => g15l3
  | _ => emptyPacking
def g15index : Nat → Nat → Option (Nat × Nat)
  | 3 => fun _ => none
  | _ => fun _ => none
def g15 : Forest := ⟨15,3,fun j => g15samples[j]?.getD (0,0),g15columns,g15autos,g15levels,g15index⟩
def key31l6 (i : Nat) : Nat := 0x820007028af371d000003180048302e380000000003819155875690d58000003d
def g31d5 (i : Nat) : Nat := 0x84001e90fd02fd01fa00
def g31l5 : Packing := (3,1,3,0,4,4,0,g31d5)
def g31d6 (i : Nat) : Nat := 0x11a20bf
def g31l6 : Packing := (1,0,3,2,4,0,0,g31d6)
def g31samples : Array (Bits × Bits) := #[(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdafffab2d55fb9f999d9ceeefacb357b78f9ce2bb554a3bac97b2a9d65,0x250142092220460600407048c382809c2160e048740030a88143281c44),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffef5dfed46f26fea572a7ba9effd7341aff97ad1ab5bd2d547d6793334b,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff90aa211010d10141c4300836206168204010183680184d04682483210b),(0x73ef3f3c8ff8df3fe567b556c9567ffcd665219778a6bd6e36bfd946ac,0xc10d0c3000214920a0d648109801012344d60802686b04210115006a4),(0x7c7fd57b7ffa3476e74d6f3fc4bddbd44dc213c5eb8bdea95bf6ee7492,0x38022048645c06490200044a25241818912934541000824c322ae5002),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8fe76ff6451fda6ff84b6daf38f5bb6f6a5ee88a4d6be3f71c64aa3f,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8076989008882001270e063010011622500c04308a174300141c40a239),(0,0),(0,0),(0,0),(0,0)]
def g31columns : IndexTree ColumnInfo := (IndexTree.fork 2 (IndexTree.leaf [(1,0,30,0,4),(2,0,29,0,4)]) (IndexTree.leaf [(4,0,27,0,4),(8,0,23,0,4),(16,0,15,0,4)]))
def g31autos : Array (List Nat) := #[[],[50,65],[66,16],[67,50,33,16],[67,32],[67,66,49,32],[33,48],[67,50,65,48],[67,66,65,64],[49,64]]
def g31levels : Nat → Packing
  | 5 => g31l5
  | 6 => g31l6
  | _ => emptyPacking
def g31index : Nat → Nat → Option (Nat × Nat)
  | 5 => fun _ => none
  | 6 => lookupWord 5 25 2 10 2 4 (key31l6)
  | _ => fun _ => none
def g31 : Forest := ⟨31,6,fun j => g31samples[j]?.getD (0,0),g31columns,g31autos,g31levels,g31index⟩
def g47samples : Array (Bits × Bits) := #[(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffddffff5cfaafae7dd35b9ce7bbffd6b6b7b7cfbb8d3b7ad85ddf257b56b575,0x2200a042011011800c00803812181c2009c1061c0107200c09440143143444),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeebefed537937fcb8ab173daa7df7f7691aff9776b2b7dcb92a3f3678b2b59,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff9149112428688034a38448020d64a21d120601022ea84882b022a624830919),(0x77db9fef67fc77f3ffe6e3dd55f86b6fffcab66472f7c57fb768dabfad4eae,0x820641080010508440806b120004c020121a4ec1002247c020840112806a4),(0x78ebe4ae9ffd0d576de696b3cff805db7d426c00d8ded437ed436ff6f66c92,0x71419416322f057a950700411b6b328381c4110e8d4580325370f22d66812),(0,0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0bf9ebdb2287acd4afec26dbb6d98eabb3768bb508ca4b7f1fdd1c709a3f,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff80f74f1424444852a26637058ca3a012d22680c12e48c8e17411561c608a3b),(0,0),(0,0),(0,0)]
def g47columns : IndexTree ColumnInfo := (IndexTree.leaf [(8,0,39,0,4)])
def g47autos : Array (List Nat) := #[[],[83,32]]
def g47levels : Nat → Packing
  | _ => emptyPacking
def g47index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g47 : Forest := ⟨47,4,fun j => g47samples[j]?.getD (0,0),g47columns,g47autos,g47levels,g47index⟩
def g55samples : Array (Bits × Bits) := #[(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffbfffffdf7defdfafbfd3fcebcfdeffcebffefe76de77fed7f1773f95eb2ebeb,0x400028000010005000000400701010180030103060043200102204010904888),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdb7fbfbb9ad3afd94caf0b9db5bbdf7f7d39bfcdadcf77ec9eccd2fb9cf16b5,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff2484444214284026a4e002420468a8a43140a00408d944460a4082569431231),(0xeda5e7e7b2fc29de4ffc371dba2bf0775ff12db9b18bb528fedad96afcd3c5e,0x12589919410293410206d0396285445a082c5d2bf0022b20f0895d2048c2c4e),(0,0),(0xf1cd79264efe956afa7a64bb677ab40beba463600362eda36f3357b7d763926,0xe3a8651b1a36a0acc57538a080f6ea703078a0c13c28dc34c91f3868663126),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe05fe74eda341d5872cbf684d5e2ed19e7e3bba5e964550dd792aec724f479,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff01fb53db1204342a549861b60b6727a22d48ac0b14da4445855161ae724b471),(0,0),(0,0),(0,0)]
def g55columns : IndexTree ColumnInfo := (IndexTree.leaf [(16,0,39,0,4)])
def g55autos : Array (List Nat) := #[[],[84]]
def g55levels : Nat → Packing
  | _ => emptyPacking
def g55index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g55 : Forest := ⟨55,4,fun j => g55samples[j]?.getD (0,0),g55columns,g55autos,g55levels,g55index⟩
def g63samples : Array (Bits × Bits) := #[(0xdabffdfdbdf61bfbfc7dcbe34f7f1b17917df75df7edd9eff77b6dbd3dcebed3cfbfaddba50fcabded46bc9b579eb7bd3d92776566ad4ad3debe36d74deb7f9faf189ad76da7dc1a6b4eaf21eb254de4ae1f7451bb34d9456fd18e934db17349,0x4400202400040800310000100084000ac0000102800a1100490002240004b2800a001b4000190000008108000574009200040400000594000190004218c0010840002890800550053044a00410008802d0060013000c004400188120c206208),(0xb6678efeffcbf5a9cad5bfd527a7a5bd74d1314b7915f5b2ffdec2fc5d978f8ab3b44b2b5add5b771711b15ce99bf2b3f5bce975ef94cd59a34e76ab937848a94ef6be6c9579db5905539ea703c87a7d4ae11fe2ae423fade4a3c3299b0724e7,0x499461811a200a55004cf88854029340027a680613c002ec00233c1096d01045025d0203d400243150030b7e4900b00499e023395882049d0206ec00041398010bbb1000b7310ad00cc0858112c8207810e917400e423d0034024309910504e5),(0xbfdd27bedf8fade4776ebf9d185bc5bd76aeffb29711f77d628e86e5fffdff6d1a52bff6da987348e3e147dcecdbcc68d1accc4e7d7d77b9734cfbbcefbc022d72eff5a31a72e32584dd5a72accb1256ede309af577ea6b3ab2be572a2769632,0x20983204990108b1910222a2810c12a8041040402e00006394000908008912a582448429aad10a21a0240190b504314209040621245140c82010e8812042049440841100c0c52080310832a5111106e902488a012c82618908a42202729212),(0x77ddb87389d95f9f7bbe7e8eb89e6e76fbf75ca7fd5bb3758b555b578affe964ae7e7fa493e06d03bebc4fb5cff51e46b2dd5bdbb1eab66f60f7d916b9c6944fd85b6f0fc30a2ae7d2afc9dc369ef80bb1b0b2dd52e9331e786f7a5d38e8c8b4,0x1482478012444200420888514440810c402202189081ecc814422aa4c048408050190921c0450c000a080254044021081134422900082c11250884167012813a48094aca870a3283708e41084282480000c012150640581c30655a55288040a4),(0xdca768aafb78ce8d2db2ec3fbdddfa4ec963339dbac7a8e05eccbf0bb99ddf5febcef6dc7762a4a79d9ad8f70324ba6e724754bded1eed86f695f276b70acbd73dc66e39a88d0cfed920a0ee10b5a4dd5893bba709bff6dc1ece388c561e1ed5,0x210938550593284a984457082a220ca002159526023c0223a02100100d271046aa46f2022bb0201ea5730921b3008e848a002106a7520082d20653c8040064810364a00030c5086c0c2084761035a077101508a009ba22e00b822088521e1c51),(0x77dad76bd4ced656e7ec247a694c9eb5b66dc4de71aac18acebb177a9bac7a62d6f3e3996dd9d62d6ecf7b18557229a30b5ebb1ef46b568a8f3400a7c2d3365caade63d0f2234a24623735bcfaee29c0664eddfc63b2a86915f817ca03dc41fa,0x88252894b2b3256598a758928465236453b27d28c68c4c28a24dcc0d24d500d4a845700845b04bd175706d345a20a0a24d641d897dd822a1d52444cad2629c8e732b305273362844202335b73c8d8150424e93e44a78286995ec17c803dc01f2),(0,0),(0,0),(0,0)]
def g63columns : IndexTree ColumnInfo := (IndexTree.leaf [(32,0,31,0,7)])
def g63autos : Array (List Nat) := #[[],[50,65]]
def g63levels : Nat → Packing
  | _ => emptyPacking
def g63index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g63 : Forest := ⟨63,7,fun j => g63samples[j]?.getD (0,0),g63columns,g63autos,g63levels,g63index⟩
def g111d6 (i : Nat) : Nat := 0x120ff
def g111l6 : Packing := (1,0,2,0,1,0,0,g111d6)
def g111samples : Array (Bits × Bits) := #[(0xeafcc7b96fc59ffd26c5e2bb3d7bd378fb35ff5dcb26f92afa5f57eff59a73b7aaa379b2fc8d7a99e2ef9efcf4defd4efabc9c89733cebade5579ad5abbcd64d8557ad3d63bd1c6a75510ce3b9bf05e462ee0edf6dfb2914efc74c7d31727465,0x4d00310a2003881269402d0c00406ccc142a8012908082d00025ac006a88036948003229000032d4001bf20024ec2018680000aaf2500325400423a6f02003840040a8016ea8106822700071012c01d500600ad401ea0010f407087831504444),(0xf771ad34ff2bcf4fbd7f5f5de52efaeb7ebbabfffefbf2eab7c7cf56f8ecea565ddfabcf87cb61db9d6ef4aecff7cebd76fe679cfb9935e6adabc77cdcdb677ed3da5e4f56b4cbe39cfd7aed1f519a6b999796b48a51f4f7b8ad91a66cc6d9cb,0x1204940050200482000010001c10308054448009004424020800871400ac0690000402004e0508404004081210450414000904018220d090010808000a44280600460810104d92040818880c1010088d8400200a10a1400808810604821909),(0xf5be76df5e79b8b5d13f5f6e3ecd176fbeee538a7cfb9f7f6b7fad9b13bb7fed97560ecd71f29f3f1e3ef959a338e3a9e32bd5e7cfc7b51df73d7e9e165479b3baa9a0d59e62e11eead3ad5c624777de8699f96d3766d64d1f3fa2ca8f3d2e52,0x8e4d19200884440101e4a802e100a0c04000830eb000289800c49240c1c411082c325a6812b0485430294040c52402008322a4b0e00c0021216842103a050a9080848145264020288841a770220547500211500d95204c05521120880b352452),(0xde2ebbc73c1cf83c4cedbed77297d7f5b666582db23d5c5d7bf4a54b37a75f4992f88d683d388ea5bafb57791a5deb9b257390777cf70e9d329773c24416edd93fe3d2909bc3b81d7e62dd94d70a759eb42b6b51587d63da2e7eea6ce78912bc,0x10b22099c5638280b403142808691e02bd9d04d1097a9640ce2041351e20e64283892100494815238b12089820999d9858901b4e1903515e001721098578a5416f515492d981d895722018845902b08a5c4a2a2248dd03d08c66ca64e48812ac),(0,0),(0x4a99db5e74fdf3bbfb83b4b12e735e58f515867b75942dba656f9eeac55739b971685432ece5b39368c30fbbb9f895ca9efa5eceda2fea7be4766f052ba5def635ccf928215f7640050f6846acafb2ca6efbba0bffbfdb9043d87d111c3c3ebd,0x12d68401de50564414b80023f49c0203c0413d800068400bbb08034f0177ac0427f40400f6de0023bcc009fc1201950403ff4900082ea08a2fc908010c8a4053de0011e801464d050407f806ac13f8026d9b800bfa055d40038875010c2c3ab9),(0x107b7e8791b6519a9ebd6f37d374faa298392ebad8b5e4afe6bd267679568b3365bebaabdf6ef4e9035a918e8ca50ef74769b2b74aea726a09a6c5e9463715fb76745a9b1b6212a1b9add6dec52a9ba55b57e399ab660ca6d0f217384af881fe,0xadc48a6a24248ac9294916cc74a18dce4988890976a839d0a90054480a8f001149b409fd5690d8d50882129489ae3083c83b5253565cd02541ca4550f495b985581508b28aaa022919a1e755a00eaaa54243a315f06a0c87d4f216384a7880f6),(0,0),(0,0)]
def g111columns : IndexTree ColumnInfo := (IndexTree.leaf [(4,8,99,0,4),(1,32,78,0,4),(64,0,47,0,5)])
def g111autos : Array (List Nat) := #[[],[83,32]]
def g111levels : Nat → Packing
  | 6 => g111l6
  | _ => emptyPacking
def g111index : Nat → Nat → Option (Nat × Nat)
  | 6 => fun _ => none
  | _ => fun _ => none
def g111 : Forest := ⟨111,6,fun j => g111samples[j]?.getD (0,0),g111columns,g111autos,g111levels,g111index⟩
def g119samples : Array (Bits × Bits) := #[(0xfab75f3dfbfa3756f92d9ff7baf5ff7dbfebb9b33bef7dcdf77fbffe7bbbf75546cedccfd6f7eb762bef3ffdd2ede7abbef7e4e4b775eb9be6ab6f4d5fde77f2b955ece57b3feb97c6d99b5cdd2fdd2ea315de5f3efbf8d44ddcaa7566eda9cd,0x20100000802449000a820000c1900042800052080010000098c000620802429000050a2000012e00000be20013404000082000047420011240000c8b8000110080002480036500158018000c4009400c9000c0062803a0400e00885042a10888),(0xaf7efcd6de9febfb57d6f5ddedde36f3db7fffeed79fdbfafcf255738c743cbbbff3e3b86b8f9fb9f5bdf54fbff79bd74f5afb3f7fba34f5bf5f9afae879ab5feefe93fa9ee6566f7bbee6bf67d426d75cfb2bace9344fabf72bd58e999b76b3,0x9300010000091004000400382060802420900110020801010208161810541520000000800198110400c004084880812115000049028020c0800220200009220a01801050108206a8408406120184808104430800802442850101410609083421),(0xd3aee9d1a16b8afb579b1b1a2ede96c634714fced4ed35afb8d86696aabedb2eada373270f48f3a9b93de8a90d87d8f6684756adef8eb40bf672fc78b9342c9c7aaa652b2aec9422dd38b32b2a5255bdcc3d35b2da5f372953f3c4ba3a70d996,0x2c07b23e74020fd2aa41748155856818d263d681015680dac92709c7448b08586eaf3a512642c64b613a9091954b38c222671d26711d023332d48951dd0691952839212f8b6888039910b9ac2a42653c283c65315b1b95185ae084b83270c996),(0,0),(0x759a506bc07865de6f37bc2fabe39a5e2705b6a3eec6bd3cca572e3ed72f0325f632aa43d8e0e833eaeab6f86ad5fa72dbaf9c83b9e70faa212acf122e177ae733d8fa39a0b0bb12b7915f7134c3b9a9ed98d75362b1d9c725676c3caf04637c,0x16e5f59c6d01a255c44806523c0cddb5529a2196d082e7c24415d298c0f10d071e6090549dc090f8ed501938009f3fb2169588d90b0b506d102e01343cb84ad135f45369a498be0a36011e712702bb816af81651c4b05c0701a6642cad046374),(0x6339c3e76f77dc41ec6c9766b8b0f93592cd6e58a17db2abb9eea5cd269eeae2dc2c1c9ec755bae6a2821f6b678c3538a75edaf56c57e97ff4e8b90d55c4e75ce36b37ac511be4c610c6f229b9ab77956345b3a117ef6f3608dd37697870ba61,0x84ef690f5888a6bc0049f9381c0ba0115db000874a075d2102333605e754184fe100105f739880fb92c019ec481f2d2102dbf2480954a0ad3f922114724920d57f80032e5018c6a22083e62199863ec06b43378157e41d3d00d937293850b261),(0xd5cc96ab2735f4eedbcfece9fd4d847149d75b8aa71ff3959066dc7566c66ecb75975abde9bb8d684d89311f3151135dd1ce4d97acd9737d0b4d97b62b1596cf57b51ab1b6b408593b67d5bb928b32dabad66fc43367241aeaae177095e247ea,0x481560b0cd924918c5323d4303992d88d1232e6a49f254a2454320824e8122936522ef3572424e688310332525616c12e023da92a435d213539c9243b254cc21b63548a8e4258841b361f1c95a017252ba1c47902bc1245a7a8e167094e243ca),(0,0),(0,0)]
def g119columns : IndexTree ColumnInfo := (IndexTree.leaf [(4,0,115,0,5)])
def g119autos : Array (List Nat) := #[[],[84],[98],[84,98],[101,66,16],[101,100,66,16],[101,84,82,16],[100,82,16]]
def g119levels : Nat → Packing
  | _ => emptyPacking
def g119index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g119 : Forest := ⟨119,5,fun j => g119samples[j]?.getD (0,0),g119columns,g119autos,g119levels,g119index⟩
def key189l7 (i : Nat) : Nat := 0xa81337040d4b600002948880000590cc33d41450272020001b1
def g189d6 (i : Nat) : Nat := 0x82000f487f40bfa03fa00
def g189l6 : Packing := (3,1,3,0,4,4,0,g189d6)
def g189d7 (i : Nat) : Nat := 0x1f5859bf
def g189l7 : Packing := (1,0,3,2,4,0,0,g189d7)
def g189samples : Array (Bits × Bits) := #[(0x76b7b935ad7f6fd4d735f26d2df10ff4361bcad97bdde979efcd6e58b7554d7ea7eff73e73de92e56562d7533a4ef3de34b1f6acf1d6e216666babd43dbaabce3ad8d545ed4e53771cb4e6d84ab365f9722155b0decf672135d0ab0e8aab3265,0x8404642124899480a2a81184400c4494a40542200633c0114901482008a100b4c40690c02a500485280025a8300be5004d078022244028e4a0122910034dd0088624c002500565400b4701a401901a06a801c60d40e430038408b0c08aa0264),(0,0),(0xb725f7b34edfbeffaf8e64c99fca263eeb8ebd6e6efba6759d07fff35f0d57cf0f1af1c8e8596f2d9f9a363b65aade972ff9af593499366f72b4e55d5e6f961954d5fce693a74e66d370dbbd59357a0ab5d8c2e2b4913d9ddc0ac963246654eb,0x2019084c910042485050a84580141012107000421c10cd02a29a004c0424911090cb1414ac1a4012048a60a1130c00921224ba8854044c203120d1318881010110848d88109408245548f0845c253042044cc0e02091152804424943044214c9),(0x6b3b37beb0d3b3db67cafb77eb9e1dd789aebdb18d1db77732f653e35977f97f4dd313687fb67a399a5d29e7c5c2df2ae361e9d1a8a6a7bdf9b41bf76bf3c59c972736ba642a6ec8e10ddd388a5d8a2fef454b2f6c5cd8cb4dafd1a5458caf32,0x84c42401462a8882042c15880121e0040f09501440a3008044047580824b00c92204cb801220a2e8d004050a8c13a8082552010080e322ce0002224042220e86c96110212062d680201609100358082de8010e0a0c4e080169249024018caa32),(0xeed4ecfef66eeb7efebdd9aee7077cf1671b7b7a97dfdfd372d0ed94ede3ade9c50737565e265d36d07689d4ac4faafe5abbfdc5676e89f79f8f9a623b38502f3db98ff0fa982b81b88d0790fae9d8d74f74351d5187af7a955e769667c1914c,0x112b0124099000041080680538580102a03620812918016ca82b084951200b0011391441e40a1406003a00a460640102802906c05910d52121d05c00b8012058249003c452192901d049060038a0e052051c011422a1a0780618649266411108),(0xd9cafe65094bbf5f7264b7bbce3ffbefdc6762cbb35969c8ac2ddbae62ff5a5f3ee2cea13be5ccd265ed5a725a1921f7f9e712e69e98fb2d45e97fd5f2e0abe4f3f7676b375491bf662220c7ec1235aaa52f7b260bfdf8f023b73c589c1c3f19,0x2215018860a440b0408528403b942810a5b0009c1c080302094a000184016510830b02e2ac10b810014a60046c8c012e120b028809b84c0105208c4e88802201101131880274018a550300819c02301e012cc3000b90a8a80382305084143519),(0,0),(0xe9cbc8feffb7f8e7b8d17ff4f26deb6af5fadcfef4fa8da189aed6c66eadfbba567e7aa58acda76b57bfee9d03799233ac5e277f4fab9af55d736c18d65d30adcab7ab9d1b9dcbcc02d24b67373e9182d29baedd99bcc115aa3d04dc337a48be,0x1420360100482d00252a00a2440945244a022b202187302c44004bb2035a00002400090800450025fa000d1a80010240a950404582409154ca522280124a1c0c672a40054909a2500214036203d800a092812c0514244211e81d048c33284826),(0,0)]
def g189columns : IndexTree ColumnInfo := (IndexTree.fork 4 (IndexTree.leaf [(1,0,188,0,5),(12,0,177,0,4),(16,0,173,0,5),(17,0,172,0,4)]) (IndexTree.leaf [(24,0,165,0,4),(33,0,156,0,4),(132,0,57,0,4),(160,0,29,0,4)]))
def g189autos : Array (List Nat) := #[[],[84,115],[117,67,32],[116,83,32],[82,48],[84,115,82,48],[117,116,115,114,64],[83,114,64],[116,50,80],[117,84,67,50,80],[84,115,66,112],[66,112]]
def g189levels : Nat → Packing
  | 6 => g189l6
  | 7 => g189l7
  | _ => emptyPacking
def g189index : Nat → Nat → Option (Nat × Nat)
  | 6 => fun _ => none
  | 7 => lookupWord 5 18 5 10 2 4 (key189l7)
  | _ => fun _ => none
def g189 : Forest := ⟨189,7,fun j => g189samples[j]?.getD (0,0),g189columns,g189autos,g189levels,g189index⟩
def g127samples : Array (Bits × Bits) := #[(0x27ec63be833e95d9cd8b1b0f8c7b949b955ab7ff06f2f46fb53d19a8b89e2cf938ea5b637a679113a99b1a558cf5d3757100e2a2d92956b1df648864a3a84cf9f5aafcc4980f547cd2d2abacb351593072ded0ca36876c216b176a15583d3069,0x215000b22a840210400a1040082a19401000220004808d00802008c02014082088420800402688520818425544410445400040805130408104600820a3600c001020e0440008143510802b10a111102142440000168440214816081150281060),(0xd1272c7d4d43f0bd72e56dab39ddfe7c6a407c139e413a8c95b2f6c7134bd9d2e6151acc0f6f6e61aecc859cb80ab9d38d1f9c08bbd08127631b9fb156aefb042a9049abe4f27cdb8815184a3fa2b5dede495570df2830da3c38c46cf1426d13,0x806000d540888802080408280406213088804000000320c048631024209804006241648090164a10080940a08001912a8109004a2408004431a0101080453200880088a80c0004a880100481a02008819080040c10830122428406420422c11),(0x3757a63bdee4ba3fd3e2275cd925bbac4327c3605b6a92ba668b6b375f5956a61c0ee4c8b6382a0c726a8d674c1d24e187c7697b46618e9a3259ec9e635cb1935494676727a9c6a3df6b34450ca72f271676b8367562d5a985429aaa9a64d626,0xe190134200c030558e6885084d0788a40161e860830e0412a109c61098d030850809a9902628890c322a09e446182064058721691005078a1841cc5c6248a09654242521162044855722240404692506023498262462c48981029a8a9a244222),(0x7c12f7ae7cb67a121957d4766ab145360dad0baa714fd5dd4ad95b9245e39e4cff88a61691dd24ee5570ea624367b54a6aea5375c626bc6f4082772e38770d5a1955fa1dcb198b20afa8d659c70c9ab5dbb42b955b55e374e0f839c3068a9694,0x100b203118264280010702e3020864421484020c18c0438c4090018044060d7096401604915660c20151c00201478d0220604290c2020821402022221025140809114a0c4919231288809339110498f1918002911b15216460582041008a9494),(0x5f0ed2cab79191489f9794fa9f865222c0c45f4f23977137ba6ec87e2fb718cbcb3281372d8190b9e5b2713c276012285f3b185c628f375c96ee95cada25845527c7ad5b31bc018c667be7de6cdf9480211b73e5e0fc0e1e03a683a80feb2399,0x4e04900c0410144f3ce0e018c1840020605099a3823d30032c4ce03413c1e08c412481b32c810028f486342022205010179b1c44008d375c030cd5d908008055e282051134c40088667900c444ea04000013f960e0680e1a03a083a80f412309),(0x64ed11ab034e6565aa5f6f0a73fb2abb553e90eaf5f2056f4f2ad1a6a7112f3107edc462d825611a42150349a39be3bcbdfa3bf68749fd950e410251758bd0aaed7e1f93ab81b400f6cd22629068e5bc2da9dbde283bbf115009f3b1a197a662,0x46299909050b25a18c71e62a5095c63ecb8f04a3c26b60b927cda532c109201915ade64b3091412042050108b390e3bab9cb9877060097580a090251508bf2aae7571e1ba185a2088a6c00621068c596ada8d9f5a83bbf101009f3a0a197a602),(0xed72aa63cb994444b8dcf183254b4e7cee24db3ad729ab4a1ba98c700af5e5480459e832e1cc5750368c89edf172492ed4565f186db3259850f427f3943aea1f7b1d745054d56ed5059c9e36e00b68fdae413f628aa9c64ad98b04d0b38dd9ac,0x4400b2628be723745844a119668f0ccc9303b92a933d014173710ec9a0c0658c41596832a4cc13563c0629c5d4a2402c44020f584d31651810e10cda143b2c95631f726414156f15141896b3a1182c75a6e53b222aa1c648d9830490938dd1ac),(0,0),(0,0)]
def g127columns : IndexTree ColumnInfo := (IndexTree.leaf [(32,0,95,0,8)])
def g127autos : Array (List Nat) := #[[],[101,66,16]]
def g127levels : Nat → Packing
  | _ => emptyPacking
def g127index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g127 : Forest := ⟨127,8,fun j => g127samples[j]?.getD (0,0),g127columns,g127autos,g127levels,g127index⟩
def key191l10 (i : Nat) : Nat := 0xa2d43b28d7001ab368009df79a6668d8a485480048c00a24000002900046192841e000000005078511fa7b8000001d8000000000050332001c2200008044
def key191l9 (i : Nat) : Nat := 0xb5d65558d2140ea31b806b286019a820212fb2e35aa613228a5a077246e6fc20ca1a41bb2d080a9c3e39f318874648000323b01b537426ceae26842215792e4b19e71cc72290229e7cad73d5f333056000d205f83e366a30000000d49821b1f1088000bb771a5c8c0000000000eb0000e0cb6ac6bec3c000c1b800347e18451880000012040006004d1cd8e0000001866e151a0000282800081e2a5e9518b100010bc00000030815564ae0000000000000ba722a1a34000000e6c5a954a6f09e6780014941d61a7112de27d595e7f09e40be3dc9678ab0bf3d70002c438a3dd4912345fe50900b4e481ecbbcceb07786be83e621d46430465b9b583a98309000098f882ae3a444b1d707c001bdad01b2c800179a0001f6d90464c82da1658b094500004b589e042e51604dd58429e06b90ff614389938aaeb6d12bb049522a72f25c09129e0463116174d50c3960b150c0a182d435d81d03dcbc0b346f3525916e494182a5649d22c9002ab560902d0004c5bd2828ce425700001e0842090d9c2ec56f6a2934aac61902201440c3800d7464005040d9808000b00120008008026140608781000c78f2e086830a0c98000580830000a023a002141e004000c001040a00380
def key191l8 (i : Nat) : Nat := 0x18cd14b25011e7225b26001876a3412158c6fc726c2320d6e3243bdd05603f1613ebb0007f7c604089b00125f5892200bf9421800b5e245039f1cf3cb8436d7f2000047800310000002025492575bf0012c00000042000001b8021c00800c01d000c080081
def key191l7 (i : Nat) : Nat := 0x2c
def g191d6 (i : Nat) : Nat := 0x47d6448788a00
def g191l6 : Packing := (1,4,6,0,2,0,0,g191d6)
def g191d7 (i : Nat) : Nat := 0x1021aae2c480c58812165850610304200048200685020d100000000000200100000fce5cec0b2a49f918c877974664f4a45403b36312c2722140f0a0500fd51548d13edd3641903fd51544d03fe92540d02df57305d02ff10305d02df4179dd02bf5819dd02df5819dd029fd819dd02df5155cd019fe885c901fe92440901ff114409019fc8788a009bd849dd039f5819dd02ed6668ce11f56558ce119f47840a11f3a5591200eda668ce00f5a558ce00bb9841ca00fca3388a00fb24484600fd23384600fe22284600
def g191l7 : Packing := (28,3,6,0,2,8,0,g191d7)
def g191d8 (i : Nat) : Nat := 0x850910304081c2440c0e2128f09183458e0d563c424bf1e12406128b1c7846402045834a31022c1244b4112285081c2449f022410c0418818084041a2060210127868c180849614f082043003c28008103c00a001050011a0c10d03085c404064a2030a0610180108a409488504804aab1e40a0610805408d7f063c2499716b62841c098f1800a084818401971629005810a08556544b736241080077f04053c18a8a2824181120efe78c80844603045000e102828008e8b070510443840106263000efe5858a100024042202241d09811e292070e043021810a5c588002801000c0052e2c5001418110006003021810c08516144821810a085042001810afc7897e3c49e14f0a7850604482184f83a8258107f37d67c179c77f77274572070b6f66e16cc6bf6aa69568066b64e63962c61f61a60d5f85e35ce5b95ac59758256d55053b50e4f94d44bf4a247d45843b4264113e43d73ca3b53a039338635934432f3122d52c02b328e27925c24f22a21d1f81db1be1b11a419718217516815b14e13912c11710a0fd0f00e30d60c10b40a709a08d08007305e04903c02f02200d000ffa4c91ffd0548ffe93227ff41513ffa4c81ffd1640ffe83207ff49503ffa2a81ffd0540ffea2a05ff4d502ffae6817fd2340bfe89a05ff40d02ffa2e817fe7740bfe9b203ff51501ffa6a80ffd24407fe91a03ff5cd01ffa0680ffd72407fe81203ff4da00ffa47007fd13803fe89401ff88a00bfceea2dfe774d6febb247f74d923bfcee91dfd7644efebaa27fd45513bfcee89fdd2344efebb207f74d903bfaea81fdd3540eff3ba07f744d03fba4d19fdd168cfee83467f749633fba2b19fdd058cefeb9a05fe40d02fbc66817f41740aff3ba057f5cc02fbc66015fd7100afeba203fd45101f7c8880dfd73407ef19a037f5c901ff20480dfe77407faa2c23fd4d611fea4708ff503847fa81423fd00a11ff209007be44803fc81c01f78ce00ff205007f901803fb08c01fe4da00ff28b007f935803fc92401fe45200ff247007f913803fc89401fe1ca00ff445006de668cfaf2ac67f58ce11f7489007da33803f511401fc84600
def g191l8 : Packing := (100,2,6,5,2,12,0,g191d8)
def g191d9 (i : Nat) : Nat := 0x180327c7c11a70600f8f1304b1c05f0c3c541303017c38f1204e0ef8f13040180df9e0e080325463418a006077cbcf0238c0ef961b3c041381be3e0900df9e30006fcf825f86eb1755933dd9099319085000ff517fd35ff48ffd13ff40ffd02ff00bfd01ff803de33fd847fa00
def g191l9 : Packing := (12,1,6,7,2,9,0,g191d9)
def g191d10 (i : Nat) : Nat := 0x1f3c11ff
def g191l10 : Packing := (1,0,6,4,2,0,0,g191d10)
def g191samples : Array (Bits × Bits) := #[(0x6acfda3c2cb83a92b793db4cbe83faea9cb2634793e21db352fb83fe8df2bc07a86d83614e9e1d6652f73c866931a299021d0d35cea03b8bca899a3ae9b0852968ae39aed598c502d3cc66c95e3918558ba9636cd1546c95b4522b12e41c6251,0x8027018c1220821109402382a0c04040242201142810004800310a01021028020024504420900008134444101889108100844480011218a0808a088000429588a002494484002118004005c4110108908c2000154441190520210a0142200),(0x7913ceb593e8bd03514889e55f4c93639759259376fb3230720c9a865196f27cc74c193b9b758265cc3f7b6a39d891145642471fe1a3e402ed12036d66f3fc532a7d00122732be1cd6f8a0d631223ddb153772d463789a2c383ce02e7842d163,0x88036081c60419a2c82401d04754b2b302101402821d5c654204040641a4c69d42c491108805a675482c4b1a3210132646402113b58224122512010966d1b044833550122312b410427aa086012a6ec1101538c042289a0c282ca02a5842d161),(0x557693cafd0fd9424efb95e75ddf8ed5bd78c8ecb52fa208a8d45cb3574ccaab77d93b1e650b4399e9518160864e914bee471a4d6078d8cd3710b8c5462d299957d5836e24a95a7b253cdb2e6196070b78eaa32a2b4a267149c447650cd138a6,0x10c082401088400012d0c4008000004018ca8080142020182010002082500860100b028600824082a011044180428040210612040030c884904098c2002801191040822880a108c8040449084010010648220108084220210140474504110882),(0x9c642d62a2f2f7ba22bc048df67d49f5212576be5994f8cdc5e270babb8959b792802cb3e87f90d4054ae918d4ab1ce241d9cf541d5d16b72277276810cef58c9e0f2a3137066d66292bcd81a96583d025d9fd03afbb585aa2b81e898b063d44,0x8024093988519a8e002822a41919198600217873085849c0c483198871885081c08060615e498874054ab3104029780240914c50140c132321226228088464808a9608100702c12708ba84812c642a102598ac01a5195852a098180889063544),(0xd23eefb5d75806b89dcda38864b64661c9f5e2babc176a70b2d3a56f26f32e727e31fe7789e6e58a36284c9dbcb30e74d59821a10b67441120e71511dbf31ab50b42210b3baf1a3e4c47734dcff8958cfd1109f7ce27c18a062741ac46d7cd91,0x7413208444084451d48501104604c068b3980408840422121160844600658c78341c18180024668a9220480b8c940760b50821038273441010c51501633a18440140258228a50a1044455344031a81ae1001013e42228188062541a446c1c891),(0x44ee3263ec00331534507b30f50239085a477dc26fc97fafdd3677e1adedabf5a6627a917685fed951e16b05c441608531a6eebab7bf0ffa2c9d6923c000425ae070ded9cbf43ff0702d561449016826463c1cddf881bbc98109fdb0912bda0a,0x5c9601812402000310c10a308504200a188ca4d220b13a418220c4ac1700cc49329049900289169c4a408a09044020043184b638a739649c2011540242004250a0701ac901871eb02048c310010048264632184cec01aac801096da0110b580a),(0,0),(0x3ab08ab4b6d74c50e56bc9651caf5894b179e03465572acbdca5615696769c27053d6dc580568c9318a62a712d4d06df8fcf0933a8a96615b24c8891d85dee28deccf746ecda09546a23c7138dbf2215a9d969340b49504d34d905859a5a4fc,0x8020482e4971b288ed202044508b9ca5050108094844412451461041282e3192c9648008d0242841110660a6538444294c484083188002614b0e00011891a8820d8e45006648e00548a230c32acf32918089829300b41504d204901848a4a474),(0,0)]
def g191columns : IndexTree ColumnInfo := (IndexTree.fork 19 (IndexTree.fork 9 (IndexTree.fork 4 (IndexTree.leaf [(1,0,190,0,7),(2,0,189,0,8),(3,0,188,0,5),(4,0,187,0,7)]) (IndexTree.fork 2 (IndexTree.leaf [(6,0,185,0,5),(8,0,183,0,8)]) (IndexTree.leaf [(0,8,163,20,6),(10,0,181,0,5),(12,0,179,0,5)]))) (IndexTree.fork 5 (IndexTree.fork 2 (IndexTree.leaf [(4,8,163,16,5),(14,0,177,0,4)]) (IndexTree.leaf [(16,0,175,0,8),(0,16,166,9,6),(1,16,166,8,5)])) (IndexTree.fork 2 (IndexTree.leaf [(19,0,172,0,4),(24,0,167,0,7)]) (IndexTree.leaf [(16,8,163,4,5),(8,16,166,1,5),(25,0,166,0,4)])))) (IndexTree.fork 9 (IndexTree.fork 4 (IndexTree.leaf [(9,16,166,0,4),(20,8,163,0,4),(32,0,159,0,8),(1,32,30,128,5)]) (IndexTree.fork 2 (IndexTree.leaf [(35,0,156,0,4),(40,0,151,0,5)]) (IndexTree.leaf [(48,0,143,0,5),(56,0,135,0,4),(128,0,63,0,8)]))) (IndexTree.fork 5 (IndexTree.fork 2 (IndexTree.leaf [(130,0,61,0,5),(4,128,27,32,5)]) (IndexTree.leaf [(136,0,55,0,5),(160,0,31,0,7),(128,32,30,1,5)])) (IndexTree.fork 2 (IndexTree.leaf [(32,128,27,4,5),(161,0,30,0,4)]) (IndexTree.leaf [(129,32,30,0,4),(164,0,27,0,4),(36,128,27,0,4)])))))
def g191autos : Array (List Nat) := #[[],[84,115],[117,67,32],[116,83,32]]
def g191levels : Nat → Packing
  | 6 => g191l6
  | 7 => g191l7
  | 8 => g191l8
  | 9 => g191l9
  | 10 => g191l10
  | _ => emptyPacking
def g191index : Nat → Nat → Option (Nat × Nat)
  | 6 => fun _ => none
  | 7 => lookupWord 1 3 0 6 0 2 (key191l7)
  | 8 => lookupWord 17 64 6 11 5 2 (key191l8)
  | 9 => lookupWord 68 242 7 13 7 2 (key191l9)
  | 10 => lookupWord 9 46 4 10 4 2 (key191l10)
  | _ => fun _ => none
def g191 : Forest := ⟨191,10,fun j => g191samples[j]?.getD (0,0),g191columns,g191autos,g191levels,g191index⟩
def g251samples : Array (Bits × Bits) := #[(0x7c5b1073c997e37379da30f398119ee6fb6b9ec3f472bcb960b6e16b764eab308775a6f93b85666e9d3190b2b24d642ca5712b6de7ab3f7906c1699135342a691b3ae0a5aa4ef7bb316cf861cfcc30541d6a6cc4992b1a999615c8e8d911c1e1,0x2118206040004a02130d09680103a002090a061080141a8c00302460220208340600a251588102029c90b010225400202065234404234e080480294178042009180840240246b20a0024c060c50410001a48a084882a181106058840c1114140),(0xcce5a5f376b735aeaefe578ced15d32ecca61663a9af3bd1860bc21b19116b79223f9d41251db7915d2d676e62aaa4f819f9d341f91890478f7c179edecb18b88452ff03ce59b2503e9c1117dab8cd95ebc956b7a216470f30e3a2b3ec2d18bb,0x4842cb022293909020208080c0985104462050200a232050248f580a09002349282c0500277025a04229050a00aa2098018840837118b0c40a78400806c358a084123a0140090810bc8810142aa8e601010152222014470a10a222b02c2818b9),(0,0),(0x615f43b7c5899d56d0ed540d07e5651da134ed341e9bc1f74f237fc0ae8a342e74d0d54381c29b89aafb968c73300f2ad24e70d94c925aaf7c71d97b8e42ee34b1eb0d1c78f57307cdbb8ab0333b96f243ce283ea4988c525a6cf93575cb22d6,0x600508638c1a9f0381c44ce96aa5f40532886e32158a42c5402a7e6c4a89343c9410964685c08b09acb0120c353c06229a6c00c94c92de87444159522882ae0499430c1549527146cd2ac810537252985246622c84980c521a4cf835558922d2),(0x743743261165c64a5893c74b56706899b56f313d76fa70640bd59bea9f4cd6cd40c9796a92725dcea2baccf628444b5fc70e36349d152cf473b98c6d967cf8571ea4949a30a5a9a67c52f2db3fa12e66e966315b35ec80fa603e034c2e56ad7c,0x8e228200012500a04432a202145800c8c044118122412020998581138524c38140cb492802205484420a48e00002411d45001410a1402070b13084088559515204a0a28a24a10ca03050168720812c4621201151314480a8603203082a468c2c),(0xf3d9bb1a8ffcdc97c518eaf4c8cf14e122f0fafd99d5fdca7ef0f64eebb658a39d280ab679b66835384c18039df39cc970c09cab32e75b6d986af50aa1e14f67f56dcf6f41924d79e9e39f3990e7fa0a34138f4a5e417d209f607f101fc4fe09,0x9201861738918010c41062040c8818244620088911c0e1638783100880a45083c120082600262524204640020401ded90000982b30080131d06c4002816148a041658f0100904561e8880e0910f0e60220020e2216414120916065101cc4aa09),(0x8c34b489b6743f0cbbb4f14fa7d16d9fa49b993f9ba2b3789eb911d5e1cd7a6f64e2a177140a8013c504eb6dd8b5e7f7e94f5a351463882a81261e97691b96dcefd6ddbc37c1e3432aa0876640524995f6a595fd43d7d81429dbe94302afe942,0x269c30c1984c0e0408d2577d35632830a8c6a4165540daa693102041644d9ca647426045188a80110514e824d9155760ee46136c04410a2a918614976910825e2b85c52c35a0b36b4200852245520814f6b484dd43c398142959c9430287e142),(0x1bb2ab4aa0e85ba9e596de5ec3ce129b01134cce9757f2d674620576a8bd96bf3a893c9457f0a28da9ccac591d7731877093a6c205d64d4c2bcaa6363cd0b55e770f7a466dfb2a9c82572d4ce3aa90cf64d9c30549ce2fe50b809671629a567c,0xd9639e04222012901869c59f133e18908110146a61f169c201c69140019863c2e851098d7d900098988b54119762026501322c440c64c4e0e9086343c860556368a70222d632a1a145321c6e30c00cc44fdf181498e2ec50a809261621a5474),(0,0)]
def g251columns : IndexTree ColumnInfo := (IndexTree.leaf [(8,0,243,0,7)])
def g251autos : Array (List Nat) := #[[],[84,115],[99,65],[118,84,115,65],[118,81],[118,84,99,81]]
def g251levels : Nat → Packing
  | _ => emptyPacking
def g251index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g251 : Forest := ⟨251,7,fun j => g251samples[j]?.getD (0,0),g251columns,g251autos,g251levels,g251index⟩
def g255samples : Array (Bits × Bits) := #[(0x9b665c544a8481c32c829a3849d25a0c2e734bceaece0410b1910c9246b692285657c973ca335d593cb00f0546b90059eb43e97a932728851785431870f031165ac8b80393ba6e576270cc58c906b870841734e15dc89803598ab05c2460a6b1,0x104454110880808228020a2041d8002c08600a02808c02009111060244ac12008614a1024802115108904700443200508241c8821224200116051018407029164080a01212302c0942400010c90428108414142154888803090a9048202086a0),(0xf315668af28fdb1ca228365b7ccc05a0011317731e21482f697635c521d4e57b4580944cacd08190116899ef79421d834fcee4e488905930903982805fb1c61927af17aaf49049a676974192f0d0160363a1bd03830701b0dc1f8281c2dc6123,0x83112a82400c43108201140b24040542001210600e014836084820c40800442b4181104024900000902098cc210099010006246088901220003082011981800902040620cc814002101041843090160043212902810201b054050081825c2101),(0x380526282fa13ac851f4c9c505254980d6e8ec3804b3594a769d93b950ebc251b0d8e2a15610b8154799066089743516386914b45de9a6e1e91c2d64aa4bec2945782990b2d68e61aa4d3cd1b24a6ab680984b4c1298da14a63264e421a50a46,0x184000082381184051a442400021c800c760240c008201086414493150c8805030586481420228050588002082640402084818905528808149002d00020c144045280184104604602a043c40824a60b20098024012185a048212646400810a02),(0x96903da21572f2b1f1c959078994a771bc47364121282ac5966e24786e0f6b8886ae49c27124b27b7242ff2e0094e0b4b1b582696d3c94568c371a6b03b30075a8d6353ad9672c0089eb12ba6325f80dd24d451b8459a7c113618d0b812f118c,0x86100cb01034a2a12848198388d4226018030240202c8a411a0a044824066a838a240842212092185a40cf0a0080e094a530c6680a1400448645526011312024a0c7343889210800016b021a61259805924545098441a1c11120810b812e1184),(0xca830c6ee5a1c1ac77b2c4bb013b84b271c7189edce77b42164b82b2ec44ccc2202552493f52e619512b4f09e2177ba801c291327039cbf4fba1fd7ca29d36ceca40c4508827295a1b45be11b7c00687be220f65622167c80c13fe90c415919,0x1282044674a181cc515204830038803270c71014e5265b22464b9241a4004482002443590d10ca0850630203a411b2a000c201185038c3861ba0d078200d6480c204804048212d4a89449e11258006869a220d60222163c80c12ea00c414819),(0xadcb89db333a54791fc5b16de6a74b1fbdaa5224c4caa060c8434905e130b3e50875189fa3aee40ebf67487ce98db2673644923b555505294552488c144494c2312ef3656d2d51ee39b1b44e04f3d3ec4d148000ab72771f011403179f478e82,0xa991884a13221d3803c5e045a0014312e78660240442614040424905201081f109410899826ca6043646807ca808b20b342020284941850001124c8410049440302c118d6904416438b533460072d3ec490080008b50771c0014031517470802),(0xccf1d170b069949f14600d7679a83ea985e068495997ad010287ff4ea745b576050c4fa9e8e0fabd2497448bd27a5aa8acea4ac0268e4d44dc2df9de452a225ad1457b3d721818b9bf9e05034d50ecb938aed67098a522a72856072e55b8d214,0xce85130b040942f1560095449a91aad8dc0e80b5196a18140955b282345b194266c47298868eeb9221d4601c27a00e8acf04a8036004c04cc8c58ecc43a23d68161791d311c0cb9abcc24434d40e8b9388ed67018a522072852072e55a0d214),(0x442aa5b9d884c622461c21eaaaf556fac8da8923687abbfb99c9c28096422e0eb83cb34c1d8918aec8c55d99f53bc2670104934ee2f27258616b2c55a56fa8970e02486406e9b92b5242282d15890d903f02672424a3e96d3ce1d022fa0aa8e8,0x460a679588446000a40a01aa08c414e80818810338389a92898982c08602320ec02091061180118a88016c815113416481048146a2821250206d8051a4632a958802cc600689381b004a400915810c003602652424a380613ce19002e808a0e8),(0,0)]
def g255columns : IndexTree ColumnInfo := (IndexTree.leaf [(64,0,191,0,11)])
def g255autos : Array (List Nat) := #[[],[84,115],[117,67,32],[116,83,32]]
def g255levels : Nat → Packing
  | _ => emptyPacking
def g255index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g255 : Forest := ⟨255,11,fun j => g255samples[j]?.getD (0,0),g255columns,g255autos,g255levels,g255index⟩
def key383l12 (i : Nat) : Nat := 0xf8400002630000023000000000000000000b83d5688000000000341000030000000000814000015d0000000210344000018d003b10000000000e080000000e70005c3803500091000000000008
def key383l11 (i : Nat) : Nat := 0x404c001fd7a0dd080d1200990f207c017043e0ac430a491c9aec7438f32422a414035a0e000e6f384202824e3e5491f317a0090ee161490000d0e481ce32000c4b9104c1860ad6100030920000000003c06000000722ae38f1200000035c780290bd08d23d219503209024ec0512fd44dc0985ef07266b48508d728f004824e9809324688ad260642ee33843c9e425582082c2260138002f8f81ac0c0002216a57414583e222000012800202204f00400024f34c01300e78608380c041012080080846040
def key383l10 (i : Nat) : Nat := 0x8a7028008f8208641c25de616202731427f0aa3ea6a9bc18603a40bac46606be46000184a7c7d25a0000000b98af69a264a6b01ac3b3a21709000001146294f5b28f5117b2b2368000000119a0000000503689a2858e10b056a96282c8039064ce4000005a1824c4b68b4a1ca0160003a96c1c5108908a005faaaa16a13000042ba8544116a040004b6aa18802880c23178071841517e2559911705a04117c6495c00000000085d314e242a96a0880000a01fc56687256502c84968668866a1180000003d68390f815a1fa922000012b8020000c2a6caf0234475dcf201fa032887c28e092c47a60725df80221bc02a000007a61e192100d1c1f61f683d817642e40874ab202e012c0cd05141d60b104cb094626909c0000000c0e573a858d7326a6285e00010ac0007468e22e50bc16f60921b5c8f41249001273800322800110cb04e0005728622182280ff076809bc29a93800081a596455d1053c0607cc3a5870000108081400524002801c04219100c0821c60cc13c0c2030a201001e00285000001f020030024000800c08280
def key383l9 (i : Nat) : Nat := 0x6977b1303806491384c288005f480044300b4273a470aef249bb09d0238c000000000000000603688ce51876813ab9e6c881d7b37687df408050502a181c84000606800000000000000424bbbaa9612800409100800346576b8a520800702905aa985610b9a10486080010008502020c0020a18085
def g383d8 (i : Nat) : Nat := 0x7c610014028800000000000000302080140040000000a09b827d78736e69645f5a55504b4637322d1e19140f0a0500cef45d94a2103afbaa93760801f7445d0744d03aaf69017618038fb68a9960d01ad76949760c01af34a89760c01af64289760c01adb6943760801aeb69037608018fb6683760801af94683760801afa42837608018ef690988ce009fcaa9190de009fa68a9944e009deaa99504e009deaa99520e009ee690988ce00be6690178ce00be6690918ce00be6690988ce00bf84a83784600bbc6989384600f749de3384600
def g383l8 : Packing := (25,4,6,0,3,8,0,g383d8)
def g383d9 (i : Nat) : Nat := 0x2dd0028c0601f18c02041010022160ac183c0004580028bb3c71c058816e807460680741c30700441602883bd0180c08009e92a09189248391a905315048c4c0a178c440a1c344e20480c5e3ec8c4124f1f67a1c70097c7d918050801b86cae3f18d8123489e81e3f187030392c68303e84a0683078305e30e0607e38f83c60f060a511f174250341f8c5e031010ee21078c3c161c0cee22050c28801004142c00504800c7c3000f402160a08ae97100120112003c70a082689408970b120030209083000c003000838e14007c610001c70838e1020020212004000023e3ec8cb8e14489e2f1a14a23e23d15c47a2b88f457115cca2f195c5e3ecf438e4f9debbcbf80ec1d2799709dd3b93626add2d9db38e63c8786afd5e3b876b2cad6ca75446864ec9992b24646c8990d60abf57bcf1dd3b7e6bccf98f3075e0b6565abd55ea85452734dc95d24a3b45a858ff9f13c6754e39b9356698cc18a2f85dcb916d2be568a61472724d08e918226438650b3138214370570800a4005ff65c1840f7fa2f442077fd9720d01dfe9bd1080dffa6537006ffd329bc017fd9704e009fe44a2e81ddf6541840f7ea300c2077bd94a2103ddeca51081cff6468840ffb20e89a07fd41844d03def4422681cff6241700f5fa2ec3007afc1761803d7e8cb0c01cff65d8100f7ea2ec08073fe99604039fe44a6e80cff65d834067fd32c1a03bdd8320d019fec4a0680cff64e884067fb121b8033fd9760c01dee9bb0600ef70dd830067fd32c1803bdd9760c01dee4bb0600ef7a65830077da6ec1003bec37608019fe44a6f005ef65037802fda521bc017f5190de00bfc8486f004ff22513802efb2a09c017f90904e00bfccba07007f644d03803fb20719c013fc988ce00bfcc9a03007fc406118027f93108c017f8894de00bfd4ca6f005fe46437802ff32e89c01ff11744e00bfc44a27005fea6513802ff32e09c017f99720e00fec89907005fe64483803fb26f19c01fd9138ce00bfc4c467007f645e33803fb02f19c01fd8918ce00fec4c467005fe64c81803fb46640c01ff11384600fed19c23005fe26211803fe26f08c01ff03784600ff849c23007fc8ce11803fe13108c013bd94a210397f4cb0c01cf7a6583006f73281bc017e9290de00bf88c86f005de65413802ef32a41c01fd23384600
def g383l9 : Packing := (91,3,6,5,3,11,0,g383d9)
def g383d10 (i : Nat) : Nat := 0xb1c029771ece80316e3a8b78f40771ca00d1002da03a69a8d16d01d28d4d3292968b98ba7f8c288f4271a30301042b0c2ce3d9d0c753d16f1a58de8639cbb8c715c8d44b554a1a9a3e0a89a12200921586544f91de7c3c6840c59058fc73e70a427a578082339c40459aa8af185209a7d34148d4cb55354aae60605689f215010071ece816c5e382c02c0800b78f67401b1c150a01655c62e06083462ae3d9d02d06c70541505820071ece801e380c14030a8b4a07c8d48497c63f8e66a4b4202e31fc73a14025b571ece863a00201e95c8d50005c7b3a084978e980d957652718d2b8da90a038f655cc3ed026a4b80d9d0683120b8d0ca07c4503e24b0080e3d9d0c73a100400171ece863a2041f8deb9e05d31c9dc29ad59e194d8397a571169d5a94d53c132d2591c5050edce08cf4b60acc9f89047f075c62859452044c3f83242b025c208114003ff45d03ffd1840fff06103ffe8840fff44d03ffd1700fff05c03ffd37407ff60d01ffc83407ff40d01ffe88407ff4dc01ffc37007ff4de00ffc37803ff44e00ffc13803ff8ce00ffe11802ffa2103fdd1340eff60403bfd83406ffa2101bfd83007fe40e00ff901803fe4de00ff837803fe44e00ff813803fe20e00ffa33803fe20600ffa11802bf61803bdd83006fb60801fda33803fc84600
def g383l10 : Packing := (41,2,6,7,3,12,0,g383d10)
def g383d11 (i : Nat) : Nat := 0x540b1d9a02e3804632e686a85e3b342382008507c4a8582c71cf98063b342397069da95ca003fe81ffc03ffa03ff007ff007fa00
def g383l11 : Packing := (6,1,6,6,3,8,0,g383d11)
def g383d12 (i : Nat) : Nat := 0x11b280e4ff
def g383l12 : Packing := (1,0,6,3,3,0,0,g383d12)
def g383samples : Array (Bits × Bits) := #[(0x22c0d3a3723e453b61b292904161c19166ba4156452239cb2ce776d1285888036922ca069735ba1c39466bb49cb80c880d6801ee650cd2ea8938a452f08d3169a1612a59384753bad95626662c63076161205bac29b905015369815a61884cb1,0x22a042a308281022412222104041018102a0455c0820218028210490004898014122a802062510400900403480940c80084001804506910881200012c0203148e041211030641239500420000c630440212052a0291101014268811220880c80),(0x3e4782180591e1e8ca415c93fb0e30440ddb7b080a80044a5e58703417b0ed0da2975b6df4e0151155ba1024096257dc7280e61c3739c9924483ab0a0d0a407f268250f5cf15b48886f76ba0ccf46838068d8de07060e07838bc1a040b61c283,0x9028018810161088ac0504223081040850928000290004c425070241b00400822080144b0c0241004a20000482053184202c40808184882448102000d0800b3040a404084018c8080110220c214483800898940502040781814120409604201),(0xc3b0d0243e2c92704a6d0bb89a642e3e324709614c855ba1b03c2574c53f0c84bca3b709607618aaaaca1686a79e094292d1a5b2e1a729d1ef4c761d2455891cd68664af136132ce19aaa19e6c55a2caed1460758145348a6cc923aa16a49516,0xc22070243c088a32102908b09820ae3610c20125cc051d809026055084360c62d8a3320940364922a8484682858e00c384d420b061233141a94434152055010c599024a50348105611a2a11e2441a2c2e41460350145348264c921aa12049512),(0x4138264952b1d12493a4452d72585b389605825093cff11edb60090262cf75191c382db2876b8a708e04945dba40fc5c0117030382d504a579e551698e39d387601c521a9a75d96750089c8958b895e01b82b803f01d0be08606741604bc230c,0x1080c0b03b031008084040c42504188060180103100c00a0a40008040890111041009902b010250040410442a404c140103030210c08ca050a00048c0a8c022200c1018d83149210000148108b815200b021800b00809600202141404b82204),(0x7a0c641d50044e150338db871c0d9c6d8b49b017941b1c71c485efc79a14e6ae159b09d8c200cd085276a758cd18f3623c4db7d00870524c281de7f5fe3e2adc1756b294808a0882ea6a1f2df107bc01d0df010f4d40469e2105ef94c107b239,0xd004201450464809021899a3188eb82288483003841b1c31c500f247991664ae92090048c000c90e723223084509b040f48cd45008304046281cf3843e140e8407928284000804822b6a8b24f004a801d0dd010f4440469e21056a80c1079039),(0xcc62da0a5fa8f5e2c996caf343c42faac6de9a345ff56a94813a6425060416282f4d23c281526277465dd835f65817a533b901ad51024edaaa84a94a69219208d911c25be8aad34a7f39eda22807bafd8e8540012ec5ecf42900c6dcd341c02,0x8452d0021128d5c8c9144a91d1c007ab845a00141d69e1982122246c02041428290423d28902225305595421e41c17a5023985a908040a15a0c4800269208200d9018058b1aa90485c38f99a2803baf58c8040010ec1ece00900c4d4d341002),(0xdaef1c77688221978d1e0c4ad4cf460c43747468370c9781a044ccfb808507cfc7550e6f05834be93d3c1e4e94918217a4e0da637baa95002472c84f89f63e421033ad28de7ab208228bfb0281a229d272553696158289b300da2c9976c32464,0x92e959624882001701040c005417432c02544069252c9701a0048cc280a00e56d4150e31071309c931151f4c9213080304e00a4233c09500a002c04d90b29c403071012c5a3a310c128ab91220a221c27244349605808983008a2c9966812464),(0,0),(0x941a1aee99450a81362f36506691ad42486aa7b56b55a36c2710c35afdccd2f0604110c2892f54d343a9228b60c516b3ea6e18394813263b179331842a516d8adc29c7c000c846f164b52014130d4016a078833106127956c94690a3b81ad1d8,0x4120210904c02803268a2402080b401402a07040a01006405204110294490a020401002d0205402c22800a1400c2280a20c04a14813021a0411310009012188c000460020c0069060300020050540108030832102126010c94480229002c198)]
def g383columns : IndexTree ColumnInfo := (IndexTree.fork 29 (IndexTree.fork 14 (IndexTree.fork 7 (IndexTree.fork 3 (IndexTree.leaf [(1,0,382,0,9),(0,1,332,50,7),(2,0,381,0,9)]) (IndexTree.leaf [(0,2,312,69,7),(3,0,380,0,6),(2,1,332,48,6),(1,2,312,68,6)])) (IndexTree.fork 3 (IndexTree.leaf [(4,0,379,0,11),(5,0,378,0,7),(7,0,376,0,5)]) (IndexTree.leaf [(5,2,312,64,5),(8,0,375,0,9),(0,8,99,276,7),(12,0,371,0,8)]))) (IndexTree.fork 7 (IndexTree.fork 3 (IndexTree.leaf [(13,0,354,0,4),(14,0,369,0,5),(16,0,367,0,11)]) (IndexTree.leaf [(17,0,366,0,8),(18,0,365,0,7),(19,0,364,0,5),(18,1,332,32,5)])) (IndexTree.fork 4 (IndexTree.leaf [(24,0,359,0,8),(25,0,358,0,5),(28,0,355,0,7),(20,8,99,256,5)]) (IndexTree.leaf [(32,0,351,0,11),(33,0,350,0,8),(32,1,332,18,6),(35,0,348,0,5)])))) (IndexTree.fork 15 (IndexTree.fork 7 (IndexTree.fork 3 (IndexTree.leaf [(34,1,332,16,5),(44,0,339,0,5),(49,0,334,0,7)]) (IndexTree.leaf [(48,1,332,2,5),(33,16,326,8,5),(56,0,327,0,5),(64,0,319,0,11)])) (IndexTree.fork 4 (IndexTree.leaf [(65,0,318,0,7),(66,0,317,0,8),(67,0,316,0,5),(65,2,312,4,5)]) (IndexTree.leaf [(70,0,313,0,7),(34,64,29,256,5),(256,0,127,0,9),(0,256,23,104,7)]))) (IndexTree.fork 7 (IndexTree.fork 3 (IndexTree.leaf [(264,0,119,0,6),(256,8,99,20,6),(8,256,23,96,6)]) (IndexTree.leaf [(268,0,115,0,5),(260,8,99,16,5),(280,0,103,0,5),(272,8,99,4,5)])) (IndexTree.fork 4 (IndexTree.leaf [(288,0,95,0,8),(289,0,94,0,5),(40,256,23,64,5),(304,0,79,0,5)]) (IndexTree.leaf [(320,0,63,0,8),(322,0,61,0,5),(258,64,61,0,5),(352,0,31,0,7)])))))
def g383autos : Array (List Nat) := #[[],[84,131,98],[101,66,16],[100,131,82,16],[82,129,48],[101,100,131,98,129,48],[100,49,128],[101,84,131,66,49,128]]
def g383levels : Nat → Packing
  | 8 => g383l8
  | 9 => g383l9
  | 10 => g383l10
  | 11 => g383l11
  | 12 => g383l12
  | _ => emptyPacking
def g383index : Nat → Nat → Option (Nat × Nat)
  | 8 => fun _ => none
  | 9 => lookupWord 17 68 7 12 5 3 (key383l9)
  | 10 => lookupWord 57 200 7 14 7 3 (key383l10)
  | 11 => lookupWord 30 108 6 13 6 3 (key383l11)
  | 12 => lookupWord 6 61 1 10 3 3 (key383l12)
  | _ => fun _ => none
def g383 : Forest := ⟨383,12,fun j => g383samples[j]?.getD (0,0),g383columns,g383autos,g383levels,g383index⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low3 : Lower (vars 3) (graphGoal 3) 1 := size_of (hints:=1) (by decide +kernel)
def maps3 : List (Nat × List Nat) := []
def known3 := extendKnown [] 1 maps3
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid3 : Known known3 := extendKnown_ok baseKnown low3 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low7 : Lower (vars 7) (graphGoal 7) 2 := size_of (hints:=257) (by decide +kernel)
def maps7 : List (Nat × List Nat) := []
def known7 := extendKnown known3 2 maps7
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid7 : Known known7 := extendKnown_ok valid3 low7 (by decide +kernel)
set_option maxHeartbeats 0 in
theorem geom15 : graphValid g15 (boundsBefore known7) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s15_3_0 : block g15 3 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl15_3 : block g15 3 0 1 = true := s15_3_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem tables15 : checkedTables g15 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g15 0 0 0 = true)
  · exact (rfl : block g15 1 0 0 = true)
  · exact (rfl : block g15 2 0 0 = true)
  · exact bl15_3
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low15 : Lower (vars 15) (graphGoal 15) 4 :=
  lower_forest (g:=g15) (i:=0) (hints:=8449) (before_sound known7 valid7) geom15 tables15 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps15 : List (Nat × List Nat) := [(15,[]),(23,[32,67]),(27,[16,66]),(29,[65,50]),(30,[64,65,66,67]),(39,[32,67,84]),(57,[32,65,82,83]),(78,[64,33,67,84,101]),(99,[16,33,66,83,100,101]),(135,[67,84,101,118]),(156,[64,81,83,101,118]),(163,[16,66,83,100,101,118]),(165,[65,50,83,100,101,118]),(166,[64,65,66,83,100,118]),(172,[64,81,82,67,100,101,118]),(177,[16,65,82,99,118]),(198,[64,83,100,117]),(281,[65,82,83,101,118,135]),(305,[16,65,82,99,118,135]),(312,[64,81,98,83,118,135]),(326,[64,66,83,100,117,135]),(330,[64,65,82,100,117,135]),(332,[64,81,66,83,100,117,118,135]),(344,[64,81,98,83,117,118,135]),(353,[65,82,99,116,117,135]),(354,[64,65,82,99,116,101,118,135]),(396,[64,81,82,83,100,117,134,135]),(424,[64,81,98,67,116,101,134]),(480,[64,81,98,115,132,101,134])]
def known15 := extendKnown known7 4 maps15
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid15 : Known known15 := extendKnown_ok valid7 low15 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low45 : Lower (vars 45) (graphGoal 45) 3 := size_of (hints:=8965) (by decide +kernel)
def maps45 : List (Nat × List Nat) := []
def known45 := extendKnown known15 3 maps45
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid45 : Known known45 := extendKnown_ok valid15 low45 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low51 : Lower (vars 51) (graphGoal 51) 3 := size_of (hints:=1) (by decide +kernel)
def maps51 : List (Nat × List Nat) := []
def known51 := extendKnown known45 3 maps51
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid51 : Known known51 := extendKnown_ok valid45 low51 (by decide +kernel)
set_option maxHeartbeats 0 in
theorem geom31 : graphValid g31 (boundsBefore known51) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=1) ?_⟩,listPieces_all (d:=2) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s31_5_0 : block g31 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s31_5_1 : block g31 5 1 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl31_5 : block g31 5 0 3 = true := (@block_merge g31 5 0 1 2 s31_5_0 s31_5_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s31_6_0 : block g31 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl31_6 : block g31 6 0 1 = true := s31_6_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem tables31 : checkedTables g31 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g31 0 0 0 = true)
  · exact (rfl : block g31 1 0 0 = true)
  · exact (rfl : block g31 2 0 0 = true)
  · exact (rfl : block g31 3 0 0 = true)
  · exact (rfl : block g31 4 0 0 = true)
  · exact bl31_5
  · exact bl31_6
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low31 : Lower (vars 31) (graphGoal 31) 7 :=
  lower_forest (g:=g31) (i:=0) (hints:=8449) (before_sound known51 valid51) geom31 tables31 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps31 : List (Nat × List Nat) := [(31,[]),(167,[83,100,101,118]),(313,[81,98,99,84,118,135]),(334,[80,81,82,83,100,117,135]),(355,[82,99,116,117,118,135]),(428,[80,97,82,99,116,101,134])]
def known31 := extendKnown known51 7 maps31
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid31 : Known known31 := extendKnown_ok valid51 low31 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low47 : Lower (vars 47) (graphGoal 47) 5 :=
  lower_discard (g:=g47) (ci:=(8,0,39,0,4)) (hints:=8449) (before_sound known31 valid31) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps47 : List (Nat × List Nat) := [(47,[]),(61,[65,50]),(94,[64,65,66,67,101]),(151,[67,84,101,118]),(173,[48,65,50,83,100,118]),(181,[65,50,99,84,118]),(185,[16,65,98,83,101,118]),(188,[64,97,98,67,84,118]),(227,[16,66,99,116,117,118]),(230,[64,65,66,99,116,101]),(301,[48,65,82,100,118,135]),(331,[80,81,66,100,117,118,135]),(339,[66,99,84,117,118,135]),(345,[80,65,98,67,84,117,118,135]),(346,[64,49,98,67,84,117,135]),(358,[64,65,82,99,116,101,118,135]),(369,[65,98,115,84,118,135]),(422,[64,81,66,99,116,117,134]),(440,[64,97,114,67,84,117,134]),(454,[64,66,99,116,133,118,135]),(460,[64,97,66,99,116,133,135]),(482,[64,49,98,115,132,133,135]),(484,[64,97,82,115,132,101,118,135])]
def known47 := extendKnown known31 5 maps47
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid47 : Known known47 := extendKnown_ok valid31 low47 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low55 : Lower (vars 55) (graphGoal 55) 5 :=
  lower_discard (g:=g55) (ci:=(16,0,39,0,4)) (hints:=257) (before_sound known47 valid47) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps55 : List (Nat × List Nat) := [(55,[]),(79,[64,65,66,67,101]),(103,[16,66,100,101]),(115,[50,99]),(143,[32,67,101,118]),(174,[48,65,50,83,100,118]),(179,[65,50,99,84,118]),(206,[48,50,67,100,117]),(286,[48,33,101,118,135]),(316,[48,97,66,84,118,135]),(327,[64,65,82,100,117,135]),(348,[48,97,66,84,117,118,135]),(364,[48,97,99,116,118,135]),(376,[48,97,114,99,116,118,135]),(398,[48,65,50,67,100,117,134]),(433,[16,49,98,115,100,117,134,135])]
def known55 := extendKnown known47 5 maps55
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid55 : Known known55 := extendKnown_ok valid47 low55 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low63 : Lower (vars 63) (graphGoal 63) 8 :=
  lower_discard (g:=g63) (ci:=(32,0,31,0,7)) (hints:=8449) (before_sound known55 valid55) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps63 : List (Nat × List Nat) := [(63,[]),(95,[16,66,101]),(159,[32,67,101,118]),(175,[32,83,100,118]),(183,[99,84,118]),(231,[16,66,99,116,117,118]),(317,[32,97,82,83,100,118,135]),(350,[96,33,99,84,117,135]),(359,[16,82,99,116,118,135]),(366,[96,49,116,118,135]),(371,[98,115,84,135]),(377,[48,97,114,99,116,117,118,135]),(429,[80,97,116,134,135]),(430,[96,81,98,83,116,134]),(441,[16,97,114,116,101,134,135]),(444,[96,113,114,99,84,101,134]),(462,[96,98,67,116,133,135]),(492,[96,113,115,132,133,134])]
def known63 := extendKnown known55 8 maps63
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid63 : Known known63 := extendKnown_ok valid55 low63 (by decide +kernel)
set_option maxHeartbeats 0 in
theorem geom111 : graphValid g111 (boundsBefore known63) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s111_6_0 : block g111 6 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl111_6 : block g111 6 0 1 = true := s111_6_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem tables111 : checkedTables g111 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g111 0 0 0 = true)
  · exact (rfl : block g111 1 0 0 = true)
  · exact (rfl : block g111 2 0 0 = true)
  · exact (rfl : block g111 3 0 0 = true)
  · exact (rfl : block g111 4 0 0 = true)
  · exact (rfl : block g111 5 0 0 = true)
  · exact bl111_6
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low111 : Lower (vars 111) (graphGoal 111) 7 :=
  lower_forest (g:=g111) (i:=0) (hints:=16785665) (before_sound known63 valid63) geom111 tables111 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps111 : List (Nat × List Nat) := [(187,[16,97,66,83,100,101,118]),(190,[64,97,98,67,84,118]),(215,[67,84,117]),(222,[64,65,66,67,117,118]),(238,[64,65,66,99,116,101]),(243,[16,66,115,100,101]),(318,[64,81,66,83,100,118,135]),(349,[80,65,98,67,84,117,118,135]),(365,[48,65,82,116,135]),(378,[64,49,114,67,84,101,118,135]),(413,[48,65,50,67,117,134]),(437,[65,50,115,84,134]),(455,[96,98,67,116,133,135]),(476,[64,113,66,115,100,133,118,135]),(490,[64,49,114,99,132,133,118,135]),(497,[65,114,131,84,134,135]),(504,[64,113,130,67,84,133,135])]
def known111 := extendKnown known63 7 maps111
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid111 : Known known111 := extendKnown_ok valid63 low111 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low119 : Lower (vars 119) (graphGoal 119) 6 :=
  lower_discard (g:=g119) (ci:=(4,0,115,0,5)) (hints:=16777473) (before_sound known111 valid111) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps119 : List (Nat × List Nat) := [(119,[]),(207,[64,65,66,67,117,118]),(380,[48,113,66,84,101,135]),(414,[48,65,50,67,117,134])]
def known119 := extendKnown known111 6 maps119
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid119 : Known known119 := extendKnown_ok valid111 low119 (by decide +kernel)
set_option maxHeartbeats 0 in
theorem geom189 : graphValid g189 (boundsBefore known119) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=1) ?_⟩,listPieces_all (d:=2) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s189_6_0 : block g189 6 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s189_6_1 : block g189 6 1 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl189_6 : block g189 6 0 3 = true := (@block_merge g189 6 0 1 2 s189_6_0 s189_6_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s189_7_0 : block g189 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl189_7 : block g189 7 0 1 = true := s189_7_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem tables189 : checkedTables g189 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g189 0 0 0 = true)
  · exact (rfl : block g189 1 0 0 = true)
  · exact (rfl : block g189 2 0 0 = true)
  · exact (rfl : block g189 3 0 0 = true)
  · exact (rfl : block g189 4 0 0 = true)
  · exact (rfl : block g189 5 0 0 = true)
  · exact bl189_6
  · exact bl189_7
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low189 : Lower (vars 189) (graphGoal 189) 8 :=
  lower_forest (g:=g189) (i:=0) (hints:=536879876) (before_sound known119 valid119) geom189 tables189 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps189 : List (Nat × List Nat) := [(189,[]),(347,[65,66,115,84,101,118,135]),(486,[16,66,99,132,133,134,135])]
def known189 := extendKnown known119 8 maps189
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid189 : Known known189 := extendKnown_ok valid119 low189 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low250 : Lower (vars 250) (graphGoal 250) 5 := size_of (hints:=1366507616) (by decide +kernel)
def maps250 : List (Nat × List Nat) := []
def known250 := extendKnown known189 5 maps250
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid250 : Known known250 := extendKnown_ok valid189 low250 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low127 : Lower (vars 127) (graphGoal 127) 9 :=
  lower_discard (g:=g127) (ci:=(32,0,95,0,8)) (hints:=16785665) (before_sound known250 valid250) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps127 : List (Nat × List Nat) := [(127,[]),(223,[64,65,66,67,117,118]),(247,[115,84]),(375,[98,115,84,135]),(381,[48,113,82,135]),(382,[112,49,66,115,84,101,135]),(415,[48,65,50,67,117,134]),(446,[112,81,114,83,100,134,135]),(478,[112,65,114,67,100,133,135]),(493,[80,113,50,132,135]),(499,[65,114,131,84,134,135]),(505,[64,113,130,131,132,133,135]),(508,[112,129,66,115,84])]
def known127 := extendKnown known250 9 maps127
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid127 : Known known127 := extendKnown_ok valid250 low127 (by decide +kernel)
set_option maxHeartbeats 0 in
theorem geom191 : graphValid g191 (boundsBefore known127) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=4) ?_⟩,listPieces_all (d:=1) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_6_0 : block g191 6 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl191_6 : block g191 6 0 1 = true := s191_6_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_7_0 : block g191 7 0 13=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_7_1 : block g191 7 13 15=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl191_7 : block g191 7 0 28 = true := (@block_merge g191 7 0 13 15 s191_7_0 s191_7_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_8_0 : block g191 8 0 7=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_8_1 : block g191 8 7 61=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_8_2 : block g191 8 68 32=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl191_8 : block g191 8 0 100 = true := (@block_merge g191 8 0 68 32 (@block_merge g191 8 0 7 61 s191_8_0 s191_8_1) s191_8_2)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_9_0 : block g191 9 0 3=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_9_1 : block g191 9 3 9=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl191_9 : block g191 9 0 12 = true := (@block_merge g191 9 0 3 9 s191_9_0 s191_9_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_10_0 : block g191 10 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl191_10 : block g191 10 0 1 = true := s191_10_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem tables191 : checkedTables g191 10 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g191 0 0 0 = true)
  · exact (rfl : block g191 1 0 0 = true)
  · exact (rfl : block g191 2 0 0 = true)
  · exact (rfl : block g191 3 0 0 = true)
  · exact (rfl : block g191 4 0 0 = true)
  · exact (rfl : block g191 5 0 0 = true)
  · exact bl191_6
  · exact bl191_7
  · exact bl191_8
  · exact bl191_9
  · exact bl191_10
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low191 : Lower (vars 191) (graphGoal 191) 11 :=
  lower_forest (g:=g191) (i:=0) (hints:=536879361) (before_sound known127 valid127) geom191 tables191 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps191 : List (Nat × List Nat) := [(191,[]),(319,[65,50,135]),(351,[64,65,66,67,101,135]),(367,[80,81,66,100,117,118,135]),(379,[81,98,118,135]),(431,[48,65,50,83,100,134,135]),(445,[48,97,82,134]),(487,[16,66,99,132,133,134,135]),(494,[96,65,98,67,132,117,134])]
def known191 := extendKnown known127 11 maps191
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid191 : Known known191 := extendKnown_ok valid127 low191 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low251 : Lower (vars 251) (graphGoal 251) 8 :=
  lower_discard (g:=g251) (ci:=(8,0,243,0,7)) (hints:=1358970881) (before_sound known191 valid191) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps251 : List (Nat × List Nat) := [(251,[]),(254,[32,67,117]),(471,[16,66,67,100,133,134,135]),(501,[16,33,50,131,100,133,118]),(506,[32,49,130,100])]
def known251 := extendKnown known191 8 maps251
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid251 : Known known251 := extendKnown_ok valid191 low251 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low255 : Lower (vars 255) (graphGoal 255) 12 :=
  lower_discard (g:=g255) (ci:=(64,0,191,0,11)) (hints:=553656577) (before_sound known251 valid251) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps255 : List (Nat × List Nat) := [(255,[]),(479,[64,65,66,67,133,134,135]),(503,[16,66,131,100,101,135]),(507,[81,130,118]),(509,[48,129,82]),(510,[128,65,130,67,100,117])]
def known255 := extendKnown known251 12 maps255
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid255 : Known known255 := extendKnown_ok valid251 low255 (by decide +kernel)
set_option maxHeartbeats 0 in
theorem geom383 : graphValid g383 (boundsBefore known255) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=4) ?_⟩,listPieces_all (d:=2) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_8_0 : block g383 8 0 23=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_8_1 : block g383 8 23 2=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl383_8 : block g383 8 0 25 = true := (@block_merge g383 8 0 23 2 s383_8_0 s383_8_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_9_0 : block g383 9 0 9=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_9_1 : block g383 9 9 75=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_9_2 : block g383 9 84 7=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl383_9 : block g383 9 0 91 = true := (@block_merge g383 9 0 84 7 (@block_merge g383 9 0 9 75 s383_9_0 s383_9_1) s383_9_2)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_10_0 : block g383 10 0 5=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_10_1 : block g383 10 5 16=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_10_2 : block g383 10 21 20=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl383_10 : block g383 10 0 41 = true := (@block_merge g383 10 0 21 20 (@block_merge g383 10 0 5 16 s383_10_0 s383_10_1) s383_10_2)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_11_0 : block g383 11 0 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_11_1 : block g383 11 1 5=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl383_11 : block g383 11 0 6 = true := (@block_merge g383 11 0 1 5 s383_11_0 s383_11_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_12_0 : block g383 12 0 1=true := by
  apply cellsBlock (ar:=8) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl383_12 : block g383 12 0 1 = true := s383_12_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem tables383 : checkedTables g383 12 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g383 0 0 0 = true)
  · exact (rfl : block g383 1 0 0 = true)
  · exact (rfl : block g383 2 0 0 = true)
  · exact (rfl : block g383 3 0 0 = true)
  · exact (rfl : block g383 4 0 0 = true)
  · exact (rfl : block g383 5 0 0 = true)
  · exact (rfl : block g383 6 0 0 = true)
  · exact (rfl : block g383 7 0 0 = true)
  · exact bl383_8
  · exact bl383_9
  · exact bl383_10
  · exact bl383_11
  · exact bl383_12
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low383 : Lower (vars 383) (graphGoal 383) 13 :=
  lower_forest (g:=g383) (i:=0) (hints:=12901687553) (before_sound known255 valid255) geom383 tables383 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps383 : List (Nat × List Nat) := [(383,[]),(447,[65,50,131,84,118,135]),(495,[80,81,82,83,116,133,118])]
def known383 := extendKnown known255 13 maps383
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid383 : Known known383 := extendKnown_ok valid255 low383 (by decide +kernel)
def hashdeadl14 (i : Nat) : Nat := 0x4592c8500000000002800049a6c68a83340e9800000aa00684000000054a001bcc7001e180000682000000000000001d46a1840000003a00000001c
def hashdeadl13 (i : Nat) : Nat := 0x301a0007b2f00e0aa2992094818000e2e0000000269e056438000000000d33e40e4a200074d00000000000003b10001e0240a9bd45d962582900000000000001430001e1400000fc03b84a000614e69108a1108000810000d04c9d0000000408800000160f24180010b9d040003080001e0c000000000001997f401183740ee12000000000080d312c00102c00000000012070000000001d35000308c000a4c0001b30000000cb3800183000070f0000001abcc008002c8cc133000000000000000000000020b000000064ec0a00000f8000cc5000105d8204160001a38001c1c467309c000000a7700000016de30f80000008380b08e000d3001
def hashdeadl12 (i : Nat) : Nat := (if i<1 then 0x7b02c3200425d610a000042a0327300000000106b33757005e04600006037d811679d009461963480703e1077f067f2582384275d80a540a20109b59b4006305d00000000ab6dfb0bf59ec084c806986b30597776440b146b100c50a956520000878e0000747c463e108bc029e7600000395ef090d06800000000f0550000d0b1e4af00000000f324d141840ca4380000000051505017000067300000e779907b0000e77730641201ea62a089a48ff0924111e9a7a041b2a180aee462f29d9b47b01eb0427030e02a5973605b9086f08d5081d04bb014363000006038c0b6d110106cc731308e0023a07fb1305601ba1839b4c088a10b88011043e427e75a600831464016903d3ba52b1ec095000ec050b011b0730478f11a0000755e331ef63db004a00a000069a91680e225f60f90092a9d0000764650a40000c591f95ac03baa33c5a1283d11871a6d2772c01c1057280f201f5012328b908232a5505e000fe02b507cf0809817c267c05c9528506d997696872194b206264030ad402d007d586d7228701d30605840f67838625a51443ce034d47ed45f704cb08730a1794e1252000070330000b56f0000b0b4000000000000a842e047609d406ae26b67b08a4de12aa0a34019000000000000b664342c50b50000c0af924dc9aa401870366002b26d00000000841e0000000060986614000000000000783ae10d980ee051d0ab4022a615808f0000a0832619a148d81500007000e007d616b032d01b483f163f00104028276b2015141030631049a027580cd0a7a05ab977802fb09ff07a97899053b0a80816e83be0790a1b809b8b460a4f0000178b0000847be03cf139a1170000b07850b3605408416262696b908af0aa7b1f5b446070d024601a42492101d496f4b4e035922127ab0000e18600008284831c00440000f031500310656013b071b045b25b4113766b5b4c6b0800008291b4888a50000000000000e38b0000225eb04d807230618425c0b097ae226f809e00000000f00d93480485e88728040000b11c3039204e9432711f445c905f004a300b97ada05680211292f09a7b1a696f3106704f19748066703f00000204d074ba20a118f025458794596091a06f000065946020913b783e342dd08c819b5b452076c21dc075e0991a4a183c3b19d7a750a68058c8379643a487b408d0523762d062b422e0b2d47fc0ac224a46231a5dca3b6069a4390000768a5433e07e0000da410b00003102090604000a010a1f88080000080d030b0c310304001300040113030203141f0c0001000232030b0801010a010007110002020208010605020401010119010b0304070203070506000210070d110100150b0a0504051d050002020b05000c0402003d0e1500260200020108040b03090500060204000d0602010100180501000001030f04 else 0xe0a0512830933085c048e216509713746026a02ec09cb040548400000268f701103ac254729fc29e8096145a39ab47552144806e00019612b7b4491ea44bc1)
def hashdeadl11 (i : Nat) : Nat := 0x5b144463e05aea749a36008e0000f05f008fc82400000000057a08357304bb42c02b0000807cd1701823000007095811411b96631031e07218223334c77b980e8010305dd000180820521064ca3ef0420000409b626cd483a833f03ac022e048a008f80a513f0000db73410f3393ca38834018881012b081c465a02c6142704300002631809700000000715300007115b00dd054b2886014000054161b183099000000000129f0870000a24110110427972915960000477d5b457113518aa01a00007134a023d08a1053002d678ef06b604a6076520f5468b025698fe62d5060c1370000e07eb793c95be02a510198285417000000000000000000005b72220ea00f9098e036e09602120000503908396112556c56084a3a211d0342f0784635707b4293308d0624205556235211962a72516903a0190235010e7765e07d5784f16feb3c248834149073d088b0134091f720f0803275f0052809446ed494b01b1b0305939136b20cf495111aba390000db890950e9807026e609a0205015880ba66b8778d4967988f077f007110cd289d0160000e278401d0000000000000000f032027400000000a08c6209804c4030102eb368a33f3b1d798e0000538a70215061a44e228300000000000000000000d01710838075e4517067406f00000000609a00003253a089a4002093b00a8125000090790000c0599583180c00000000c0411830f1160047224900000000906992725046700b000050511a67544b00000407c35bb06d0000504d3821ca470002762e0000cb1760948827b10a603b4009e06552019464444f9688a0286169097ab82524185057db2feb3d000e6303670ac01e70822426b090d664c05cf764008be03c365d6a2549347068706a71244461f086277c5780380d698dd120b27c20626037d807f403502fe1110000ea6e5071301cb0388044704f411c809595011003b20deb1a98372208b0561092820a91190049704bb03ec070670890335001a03f64504063613c50294b430832441aba46e146c8120193598c103df8314066401fd460e0745084044c100c7760b24b824f4006205b0000563070507a7c9058000000006a440000506e3040e97d006cd027646a6207807fb0450138e56fa018704e8482e0356085662f762c5b3be05eb81f1004f836000000000000000046203a6ac89692730000b034807a613d00008145702433536a79b0407805012a04e80082c50a0c0e782286421a0e4c00400004833a1491a02243880c0851202004211c6408c1835c192e081800c39681005000c04e408002001860c34c8040000000400008087400400100892c38005148410524200800478080001438126000000020022
def hashdeadl10 (i : Nat) : Nat := 0x1c05302000382d2ecf474c3a08f618409ea54931a0a2272b385214e934380040192451090d15cc0564307983441ce005970002c06068f08a82680cc070001a2c5d4a1440400018207150002808001022205d856c41e1700072d518800084a2900000a334a12801820030b1a27
def hashdeadl9 (i : Nat) : Nat := 0x202e0
def deadd8 (i : Nat) : Nat := 0xa24b7baf6624ad253281df927589c4d52540d02
def deadl8 : Packing := (2,6,7,0,4,3,0,deadd8)
def deadd9 (i : Nat) : Nat := 0x17a6100d01602e1f830400f202c200003405840f980801c0010720e8006a183c001d000f8007c00200001509fc5a0b0071b79b2bc5ba99429c459e8d258238d84a14078280a00a7becc495a4a6503c6fdb66689a4d50287fcbc661a544d029ef9c6aed1840d02bed9c626d3540d02ff49184d52540d02ff489c4d52540d02d7f11826d1540d02ffc1184951340d029f6cbc4a1354950195fdc7aed2564d01ff49384d52540901ff61384951540901ef4935496aa40d02df49b54951340d02f7493549503a6502bf62cc4951540901ef6125456aa40901f7612545502a6501fb61284612545600fbc1284612344e009dd9c7aed258ce009ee9c6aed1888a009df1c7aed2584600ff42558ce2284600
def deadl9 : Packing := (25,5,7,1,4,9,0,deadd9)
def deadd10 (i : Nat) : Nat := (if i<1 then 0x2693540b3fecd1349aa055ff26d1a4d502cffb30d2a26815ffabb4610340bfec8c26a81a05ff626d3540d02ffd23092a06817ff1184550340abff5da6b4ca059ff4d5a1a65029ff9569426a80cffdb8aa9354067fed95549aa03fdb4a13549501affb7092b2680e7fda849593407bf69424ac9a035ffaed2564d01cffab15532680e7fd25aa993406bfedc26ac92035ffaed3564901cffab0d1b2480e7fd38aa9924073fe9ad54c92037fe6e13540901fef2b09aa0480ffd9384d502406ffd5da6a81203ffa4e12540901ffe2708aa0480f7f95864d02406bff5da714ca03df74e135a6501affd769ad3280d7febb49699407bbe9aa4b4ca035ff6e123a6501efda5091d3280d7fdb548e99406bff5da474ca039ef495a4a65038ffb63553308167f9b0aa998408bff5dd54cc2053bf6daaa461028ffb6a4d2268157fabb6610340bbf4cc24a81a055fe26d1540d02cff33155206816fd935aa90340b7f492d5481a057f66d51340d02ff924a89a06816fdaaa44d0340b3fcd42074ca05df64d503a6502efd24a81d328157fabb40e9940bbec89a074ca059fd461a1a65029bfb6f5524a80c7febb6a1934063fedc554c9a031ff6d6aa64d01cf7b695532680c7fdb2aa9934073fcd8554c9a031ffaeda8649018ffb6ad1b2480c7febb68d92406ff55da4a81203fda4d52540901fee34a8aa0480f7e92564d02406bfd5db2681203bfa496aa40901dfe22b5520480e7f993aa902407bf492a054ca03dfc45502a65019ff36755251004ff9b1aa928802ff55da5092c01efa4a11849600dfd2515524b007f692849515803fb88c24a8ac017deaed2545600def55492a2b004ffabb6a123802ff55da5091c01efa4a11848e00dfd25155247004ffabb6a1138027fc55a5089c01afe6a12844e00bfe5768c227007bf128461138027fd5db4a89c01bde6952544e00dfe23155227004ff9b8aa9138027fcdad5489c013fe6caaa44e00ff925091a27007fd11848d13802fed5da4689c01bf6aa92344e00bfb57692c67005fdabb45633803fac92a2b19c013feaeda844a009ff370d2a25004ffabb695128027fcdc346894013fe6d5a344a009ff576d1a25006ff1a844d12802ff95da2689401bf66963344a00dfe22755225006fda33aa912802ff55da71114017faaed1888a00bfd3709ac45007fc9384d622802ff55da6b114017fa6e11388a00ffc23089c45007bea8844e22802ff4daa27114017faaed1388a00bfe5769c423007fd1384d611802ff95da6b08c017fcaed2584600fee26a92c23005ff1b848e11803ff09424708c017fc6d52384600bfe57691c23007fd1588ce11803fe89446708c01ff44963384600ffc27111423007fe13588a11803fa49aa4a81a05fd849515409019bf36f5524b007bd2888ce11803df14444508c01ff08ce2284600 else 0x4000888405e986c113905805080340b02e1f06087905c2003f080d05c2010004400c0288128f50060048004020800804100127c503a3f6c170230c990618643002074409038882341900e30020304004060800870140c00228180045c08224a09086c45817020801a183810008ad48702001100108e2b0c1c0800456383810230b0200117dff6de0be2c10281f00a20021f8a108140c707c503e3f8bed83901520010dd505020c988c1183426000e000e00086905c20a40d058002020340034003c1834002fd2040bdb798060306e1b00c84f01a5f8a10bc3024202bf0c090605c00880505210010fc506e1cc0693effc5f6de600097e28190cc11092183f1414080603412860a40cc6004380038003800340034003c003c0020e00107000f000801c0020e00100f78ee2192287800ec3041c003c00361820e001f8a1e001e001e00100000b0411ef1dc4377ae886cc5917b60fc50f000d8e083e2840000016a420f6c1b1c100000b521002c30416383f1420003e284000100c4aca220cd523db61a02c91b20b40600a0dbf169c61a02c9f6de60578fe2fb6f303f8bedbcc0fe2fb6f303d0acfaceacb9c93c83c68c63c53c38c1dc02bd1bb6b9bb96b70b4ab24b09aeeac8aada92a77a5ca41a31a169fb9eb9e69e19d19b69a698b97096094593591a8ff8c38a889887284c81b80b7f07bf7af79f78f7747597497397297197096f96de6b867c64b62560a5ef5df5ae5725415315164fb4d54c54b54a549548547546545545044043b42b41b4164114013fc3ec3e73cc3a639639138137136135c34c33c32c31c30c3073022fd2f82e82cd2b229728727726725725224223d23823322e2292192142041f41ef1ea1e51e01d01cb1c61b61b11a119118c18718217216d16810009807204c026000affd7692d3281defdb6)
def deadl10 : Packing := (156,4,7,5,4,12,0,deadd10)
def deadd11 (i : Nat) : Nat := (if i<1 then 0x86120d08111f407ad1db072b1c206d11ab867718d8613174859115b85231388497118042910183c50e603570c082b709d822b07a8195055010902a80410003ffd1849503fff6692540fffd2546503fff4613540bffd9a4d502fff2693540bffd1a4d502fff4619340bffd3546502fff4d69940bffd9a4e101fff6a135407ffd284d501fff4a935407ffd9a4d501fffaa935407ffd3849501fff4e925407ffd9a49501fff56123407ffd9a48d01fff56193407ffd2864d01fff49593407ffd5864901fff4e192407ffd3564901bff6a11940f7fd9846503dff6551940effeaa46503dff4a51940f7fd25a6503bffaa99840b7fd1a66102dffaa99840b7fd9a46102bffaa91840bbfd9846102dff6619340affda564d02dff6559340affeaa64d02bff6951340bfdd9344d02ffe6a10340bff99840d02ffe4610340bff9a540d02ffe6550340bff91540d02ffe4690340affda846502dff6611940affda346502dff64d1940bff90346502dff6629940b7fd93a6502ffe40e9940b7fd18a6502dff4d69940b7fd13a6502dff66935406ffeaa4d501dff66925406ffeaa49501fdf4d525406ffda864d01dff66193406ffeaa64d01dff561934077fda864d01dff4a1934077fda564d01dff495934077fd2a64d01dffaa993406ffda864901dff66192406ffda564901dff65592406ffda364901dff64d924077fd3864901dff6a1924077fd3564901dff68d92407ff95840901ffe4e102407ff9a840901ffe66102407ff93540901ffe69502407ff99540901ffe68d02407ff99340901dff4e2994077fd35a6501dff496994077fd23a6501ffe4e928803ff91a4a200ffeaa928803ff9a849600ffe46125803ff93a49600ffe46925803ff92845600ffe4e915803ff92a45600ffe6a123803ff91848e00ffe69523803ff91548e00ffe46923803ff9a844e00ffe4a113803ff9a544e00ffe49513803ff92a44e00ffeaa913803ff95844a00ffe4e112803ff9a844a00ffe4d512803ff9a544a00ffe68d128027feaa661029ff2693540a7fc9a44d02dfe6610340bfd93540d02ffa4950340affaaa40d02ff644d0340a7fda8a6502dfe40e9940a7fda3a65029ff6869940a7fda864d019ffaa9934067fda8649019ff68d924067feaa64901ffa49502407ff11540901dfe64d02406ffaaa40901dfe40a99406ffaaa4a200ffa4a125802ffaaa49600bfeaa915803f792545600bfe6a123803fe92848e00bfeaa923802ff9a844e00ffc46113802ff9a544e00bfeaa913803fd92344e00ff649633803fd9158ce00bfe6a112802ff9a544a00bfe68d12803ff11344a00ff68cd12802ffaaa44a00ffa4e222803fe91888a00ffa4d622803fe91388a00ffc4e211803ff13584600ffc49611803ff123846009ef6929940fbea8888a00ff48ce11803fe22284600 else (if i<2 then 0x6718d1b071686b63b38c6ac837ab208143ea5f4a804c20460a84911c7405186a093027a82ae19d57d066c694fa70dcc0ac4ea478ce31a1ecaeaf303c8c241ac2f19b38c69c83fbee47302190238ea2305424c6856399d2085637d12388c0c16cbeff1d208076416c80b40c0049e29d5208144b23f46802b201800c183275231bc58d5919c2ba9ed854030806003067bf9c352078df64634afd056e600c20020b418eaf319c182b832c8683382f1c2de703e3ac80ac412003efc19433aad06707f7f38754282036168bdf159a0ce09fa590158824f17a919786904bef86bc33ab209458f7dd8e39c8904deff5232b9120958e0b701b7e8611b1e288d8776dd9609e2b1c2f1582105b80098e0b90124824976d090cd009250909820be81c002d484d8f144c3068ea08444c12222609117812260911961224208de83785dd4e900b63480dfc5edb981b80c307224fbfd4f301f09477d2a0d202e2010188cddb353cc69017202256222f7fb60add5a80164f6c116903054660bb98d200c6e0e18f8afa73037818602100ed9a0d20beff8bdb752d00186f7fc5ea78e6e01e33bfe2f534770c056718d202388c2401066f7fc5ea68ee1b388131a6862ef8df646718d182bf7fa963ac8ce31a3fbfe2f6dd4f31c70187010d8f7c2b7561a05a04ce121581816fbfdb3530d74005590a1982b682c8ce0be2f6dcc0184f14410307c705b875e98d59067d2d5c686717058176d8d1b06f7c92f17b6e602d3634e457030b7007d2a0b20be2be9500fdf0b7b6c68d029b1803bfe2d415c1bc57d2a01fbfc3600ead415c1bdf363c5c6a8eae0d8d3915c0fdfe0b00ed9a9a81c83fbfc3600ead40dc1ba9e3b0e77f1ab22b839c4d4e356457053ab00682c8ae0bdb341640fdfea700682c8ae0dd49c58d1bc4ea782c02c87d1a03753c751d873bf64634dc23dfe0a86c03b6755a03fbfd4e0164340dc1a82ea786c03c57d1a03fbfc36015c3aad01bdfe3a8ec3ab86a71a7211eff5380570d03906f7fc5edba9e1b82040ec751d87590fa7538d71ddc2586a198ec1bdff16b8ea71ae195efb915c7ab8d74068ed23878d423198bda2f18b3a2a189fa24788e221f881a1e387521a785ea14384820fd83ba0cb82a2071816203f8099ff97ee1f8b7d29f137b21e9179b9e377829ddd76c1d8d7581d3373c9cb17239c6170f9bfd6f41ba36e01b536c99af96b31a9f69c9a4568619f5665990f63618ab610981f5f517935dc17435c0969959b163558495c7566954f54b14f552f949151914374f393a14ce130b4b2929349c124347e11cb46c9185456112143a90a941c9063415103b4088ff53f70fc33ea8f9b3e30f7d3d68f4b3cc8f233c50f053bd8edd3b38eb53a70e8339d0e5b3930e3d37a0da73570d2f3368c7b3160c0d2f30b952d50b132af8a3727d89ab2580901226 else 0x6c244e0445e2e80648bc5050262048e47300a0565ed8f60346f5d8ae98260a0c0068580a0c27015b807c906026158e08c030604c2b2a82103cee10cc378bc503c5a1a381a3a2d03cb121b082409e29104f14d80b00b29b02601632490481068e0401093981802127303093987200a0aca00c1820060c1003060ba9e62b81ec8b40d15c753cc0a26ae1d5e606624740ac47cc0483c9bdf72398ae02b28b1eff6cec705e2c44719c65bd0520ccbd4b702a0c67030651f4282f8a37f6c0f90083dbc507c95c01a2901847d2a015c7efbab500764fd1d5a800524460a84613d40171bdf12bb67568e07cc1703e060df4d22a00b883dd40220c2777c2ed22a06e0defe90110884fd1d5a800526915008831e748a802e219d5c0560f91f4ea40c1509ef89ad00884fd0566800c25702b3400611df1500c10c813b1c0f00a44001e0b8625494a83ec3b7532876c0fa40c07c018307cf7fb66a40f0d782d231a682c8a82a1e8185ce3c519b1a206a008183e7be5a8cd9c5ab50287af14281809827bfc7))
def deadl11 : Packing := (183,3,7,8,4,14,0,deadd11)
def deadd12 (i : Nat) : Nat := 0x226c48bbfb654c3991828d28cddfe2ea731865c0891b87a0bb538ea405a3487b1d9bfa906e3a90b8064694310477f6ca947523051a4f7f6c2ed4a3a91828d23bfa90b0351c15a42e0191a577f8ab8d4e631c0c3f7e91b6d4c6b1c0c3811c4dfe2ea51d869c41234a020c7bed54772271048d2408d8efaa71cc89c4123490277f528e4932271048d27e9c5d4a830c011d1fe8c8d4907400c377f8bb6d4e1b04223bd3538ea46e23461177f6da950523047efedb538ea4608191a477f8ba94761a711a3f7f538e644e0191a3f7f5398d032019383963e9c516e8018413c39e9a98d63991b83b6205dfdb2a635a0646093df6ac6b41c816ae0f00efedb52a0493230488077f8ba95061970704f7f531ac732112b842091d02eff176da98d61b04a4140bbec8db6a6358ec1250d06eff1571a98d6830c994a8fd8b08517fb7ae74f70b6c76686125bc5665224e74a34684243d739334f30b2c728322d1e919c15810b0ac056000ffe92a07ffd1940fffb30817ff46102ffe9aa05ffd9340bffa26817ff46502fff4ca05ffd38407ffa6a80fff49501ffe91a03ffd93407ffb2480dffa6503bfecc205ff90340affd32815ff64d01bfec9203ff902406ffd3280ffe4a200ffc92c01ff915803ff247007fe44e00ffc89401fda33803fd445007fc84600
def deadl12 : Packing := (32,2,7,8,4,12,0,deadd12)
def deadd13 (i : Nat) : Nat := 0x22dfc5b6a90e86821a4efdb54c724410d1f7f16a63a18e01069005bf8b6d52351d0d049cf924d00ffd03ffd02ffd01ffa00
def deadl13 : Packing := (4,1,7,5,4,8,0,deadd13)
def deadd14 (i : Nat) : Nat := 0x17e2b6526070604013ff
def deadl14 : Packing := (1,0,7,2,4,0,0,deadd14)
def deadsamples : Array (Bits × Bits) := #[(0xf854605d026923a5a16008862c9d18d42fd85e54d221898f1e440284a107a02910c3e03c06c40d2642ca74f54627022c11e389d9b43b30c961ca72386ce81500aa210d1ba1a121108a6c99348979d054ac200727ac054c0970110780155ad581,0x6844620d0040231585204884208800c4270824141201090814040082a10700282003e02402c4084602ca04a440240a1091218919100a2084314a220840a00480aa210819a02120100a4409048968c05484200702a805440920100380144a9480),(0x80b20c31f72bfc4e1481d27000d43c9c5bd438a9c5e0286040f054f111d001ce10920229bde170b8d339029e2bcac4cd494fb74d1052452141a61c5b9ca1e642f40c600258428f0e5c00df481e03202a204cd465e10fe01206e82c7b03150603,0x80100c30e6089040109182600012282018c41889c5e0204002b0604000c009861080028b1c2120a0d12000120908c00d005a724402504200402010501c01c208540860025840090e1400964816012008204cd0254102a00206a0247b01150201),(0x12ce100c308544478a85796a2341d206e4242e31335abb35943abb40be28c8e05c4c115123137950052a02a9ba0d31c096458c656cc338623e92230683d8962194d5145c2aa62229438824d8e06246d0cd124850733918c390189888a426380a,0x10ca0000108540870900790a0240900460282200221a991490081a0028289000cc41010021184410080a0a28a20020c0200184206c0128621092200a03d8103080d5145c02a2022143880090804206d04d100840322918c190088800a4221002),(0x8628ebbd17000228c83c0291b729e17b3643984a392a815889878936d04e41b82b8e28807cc302855ead3105d9868885c748c2b0724ae81086518e259124cd4278a18b4aa01db88524c3a3435a0814469349110c18f0c24c2a8052bd88818268,0xc2206a1d05000020401c0090e509051303449848110100480001811490070429238c000818c508010485900541c68805c240409012420000024186258024450270208b02a00da0842041a3414a08100690490104085040042a8052bc00818028),(0xbc8ccda8781e4d8151cd3cf93a4a0a01509a42078c1bc4a783ea4aec6c7bbbd02ef85be130b1750bcd872a062d01842a34826040203d5b99ac8899721d47b82106b4f88001d04ee6f42e103eb14e0a090b95e84905a08ef7a2230402e2b14bc5,0x148981a0109a5c8210c1a4690a42220050930202c418c4a7837a48680e50b9d00c601bc02020f518c9002a002c1124282402304220255b598c9019921c51b8010494708001d04e62d42a103a30060a090b94e84905a08af280230402e2304b45),(0xd3b19712becef4647857054f8773c68492608a46265cd6cd0106c449284294958830b40e8328a4102841c46a63b66493288c7290c714876750b08cb0eb0a532e014ce7e24f9c08720240400006971f885be46b00080a21145aa7f52cf42a8012,0x92218c003e8654007015040a0c73c50280c0084821449285810a8400004080918c301008002824100801c000230200c0688c40804110046300b00cb28307502a0004c5624f9c086200004000021315805bc46800000a00145205f42ce0200002),(0x3145d24845746a93b60987114c89950ee90ab5809889781e716b0d141d9e036fea797f20c896480c8b565809c5575a81eabcad03980701be24b7e8d7401960b32336416db2f0c4c050f169960250e8b311988b92828b0074bd455ad232c2112c,0x2307720c00346283a400011d4c09950fa108a4001a095004514a0014181e2261ab3d3060c0d6480a2ac41009e4571880ea848181d90321bc24d38a860208103323340169a2b084c040f169960050c8b211800b9082890074b8455a803282012c),(0x49615339cc24bb41a658244591d020101222d0f578b5376254a121290a30cd5c4e2ad1d6dabfa9e032f022500c91031b32331a7a9ace0ca4e96243014a4009cd0d2a3210b66014de852533c420acc80ff443ad9cc5d0f4808cd621151170ac54,0x4900539a4030aa408668006591882010120251355ca1242200a1212102144d6e020a42d6d2878b6832b420400cb9813312321a4a924e408ce04943054c0001c10d2a2200b040149c8425334420acc80fa003859cc5d0e4000cd201111150ac54),(0x2108654280dbc21c532263cad6a2ab60a053058994f658a43b3dd89384745a04932387065124c385d01899e2cc083e3c1e3327061d61ca921a4965c8583262f4485320b5c04953298d1f02098424a39520b6148b236021a80528c3236c545ab4,0xc0001428049001c03a04a4012802a200013019184320c200a34088304a0580410028702010083a440180cc2080827381411260a0400ca0098085048489022c408432094004053098d0e0008842422012032140b21202188052801030c545a90)]
def deadcolumns : IndexTree ColumnInfo := (IndexTree.fork 63 (IndexTree.fork 31 (IndexTree.fork 15 (IndexTree.fork 7 (IndexTree.fork 3 (IndexTree.leaf [(1,0,510,0,12),(0,1,460,50,8),(2,0,509,0,12)]) (IndexTree.leaf [(0,2,440,69,8),(3,0,508,0,9),(2,1,460,48,7),(4,0,507,0,12)])) (IndexTree.fork 4 (IndexTree.leaf [(0,4,369,138,8),(5,0,506,0,8),(6,0,505,0,9),(4,2,440,65,7)]) (IndexTree.leaf [(2,4,369,136,7),(7,0,504,0,7),(5,2,440,64,6),(8,0,503,0,12)]))) (IndexTree.fork 8 (IndexTree.fork 4 (IndexTree.leaf [(0,8,227,276,8),(9,0,486,0,8),(10,0,501,0,8),(12,0,499,0,9)]) (IndexTree.leaf [(8,4,369,130,7),(4,8,227,272,7),(14,0,497,0,7),(10,4,369,128,6)])) (IndexTree.fork 4 (IndexTree.leaf [(15,0,480,0,4),(16,0,495,0,13),(0,16,486,9,10),(17,0,494,0,11)]) (IndexTree.leaf [(16,1,460,34,7),(19,0,492,0,8),(16,4,353,138,7),(21,0,490,0,7)])))) (IndexTree.fork 16 (IndexTree.fork 8 (IndexTree.fork 4 (IndexTree.leaf [(21,2,424,64,5),(24,0,487,0,11),(8,16,486,1,9),(25,0,486,0,8)]) (IndexTree.leaf [(9,16,486,0,8),(27,0,484,0,5),(11,16,484,0,5),(24,4,353,130,6)])) (IndexTree.fork 4 (IndexTree.leaf [(29,0,482,0,5),(26,4,353,128,5),(32,0,479,0,12),(0,32,94,385,8)]) (IndexTree.leaf [(32,1,460,18,7),(1,32,94,384,7),(35,0,476,0,7),(34,1,460,16,6)]))) (IndexTree.fork 8 (IndexTree.fork 4 (IndexTree.leaf [(36,0,347,0,8),(39,0,344,0,4),(40,0,471,0,8),(49,0,462,0,8)]) (IndexTree.leaf [(48,1,460,2,6),(50,1,460,0,5),(56,0,455,0,7),(64,0,447,0,13)])) (IndexTree.fork 4 (IndexTree.leaf [(0,64,189,258,10),(66,0,445,0,11),(2,64,189,256,9),(67,0,444,0,8)]) (IndexTree.leaf [(66,1,396,48,6),(70,0,441,0,8),(69,2,440,0,5),(74,0,437,0,7)]))))) (IndexTree.fork 31 (IndexTree.fork 15 (IndexTree.fork 7 (IndexTree.fork 3 (IndexTree.leaf [(74,4,305,128,5),(80,0,431,0,11),(83,0,428,0,7)]) (IndexTree.leaf [(96,0,415,0,9),(96,1,396,18,6),(98,1,396,16,5),(128,0,383,0,13)])) (IndexTree.fork 4 (IndexTree.leaf [(128,1,332,50,7),(3,128,344,36,6),(132,0,379,0,11),(4,128,347,32,9)]) (IndexTree.leaf [(133,0,378,0,7),(134,0,377,0,8),(132,2,312,65,6),(133,2,312,64,5)]))) (IndexTree.fork 8 (IndexTree.fork 4 (IndexTree.leaf [(136,0,375,0,9),(128,8,99,276,7),(140,0,371,0,8),(132,8,99,272,6)]) (IndexTree.leaf [(138,4,369,0,5),(144,0,367,0,11),(152,4,353,2,5),(160,0,351,0,11)])) (IndexTree.fork 4 (IndexTree.leaf [(160,1,332,18,6),(162,1,332,16,5),(164,0,347,0,8),(36,128,347,0,8)]) (IndexTree.leaf [(172,0,339,0,5),(176,1,332,2,5),(180,0,331,0,5),(192,0,319,0,11)])))) (IndexTree.fork 16 (IndexTree.fork 8 (IndexTree.fork 4 (IndexTree.leaf [(198,0,313,0,7),(256,0,255,0,12),(258,0,189,0,8),(260,0,251,0,8)]) (IndexTree.leaf [(264,0,247,0,9),(256,8,227,20,7),(8,256,151,96,7),(268,0,243,0,7)])) (IndexTree.fork 4 (IndexTree.leaf [(260,8,227,16,6),(273,0,238,0,7),(280,0,231,0,8),(276,8,227,0,5)]) (IndexTree.leaf [(288,0,223,0,9),(256,32,94,129,7),(32,256,151,72,7),(257,32,94,128,6)]))) (IndexTree.fork 8 (IndexTree.fork 4 (IndexTree.leaf [(296,0,215,0,7),(40,256,151,64,6),(304,0,207,0,6),(288,16,198,9,6)]) (IndexTree.leaf [(273,32,78,128,5),(56,256,135,64,5),(320,0,191,0,11),(256,64,189,2,9)])) (IndexTree.fork 4 (IndexTree.leaf [(322,0,189,0,8),(258,64,189,0,8),(324,0,187,0,7),(324,8,163,16,5)]) (IndexTree.leaf [(321,32,30,128,5),(388,8,99,16,5),(168,256,23,64,5),(224,256,23,8,5)]))))))
def deadautos : Array (List Nat) := #[[],[118,130,81],[100,131,82,16],[118,133,100,131,50,33,16],[116,83,32],[118,116,83,130,49,32],[118,133,33,48],[82,129,48],[118,133,116,83,82,81,80],[116,50,129,80],[100,49,128],[118,100,83,130,81,128]]
def deadlevels : Nat → Packing
  | 8 => deadl8
  | 9 => deadl9
  | 10 => deadl10
  | 11 => deadl11
  | 12 => deadl12
  | 13 => deadl13
  | 14 => deadl14
  | _ => emptyPacking
def deadindex : Nat → Nat → Option (Nat × Nat)
  | 8 => fun _ => none
  | 9 => lookupWord 1 3 0 9 1 4 (hashdeadl9)
  | 10 => lookupWord 17 61 5 13 5 4 (hashdeadl10)
  | 11 => lookupWord 124 434 7 16 8 4 (hashdeadl11)
  | 12 => lookupWord 137 475 8 16 8 4 (hashdeadl12)
  | 13 => lookupWord 26 148 3 13 5 4 (hashdeadl13)
  | 14 => lookupWord 7 47 1 10 2 4 (hashdeadl14)
  | _ => fun _ => none
def dead : Forest := ⟨511,14,fun j => deadsamples[j]?.getD (0,0),deadcolumns,deadautos,deadlevels,deadindex⟩
set_option maxHeartbeats 0 in
theorem geomdead : graphValid dead (boundsBefore known383) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=5) ?_⟩,listPieces_all (d:=3) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead8_0 : block dead 8 0 2=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alldead8 : block dead 8 0 2=true := sdead8_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead9_0 : block dead 9 0 12=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead9_12 : block dead 9 12 13=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alldead9 : block dead 9 0 25=true := (@block_merge dead 9 0 12 13 sdead9_0 sdead9_12)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead10_0 : block dead 10 0 6=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead10_6 : block dead 10 6 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead10_42 : block dead 10 42 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead10_78 : block dead 10 78 35=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead10_113 : block dead 10 113 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead10_149 : block dead 10 149 7=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alldead10 : block dead 10 0 156=true := (@block_merge dead 10 0 149 7 (@block_merge dead 10 0 113 36 (@block_merge dead 10 0 78 35 (@block_merge dead 10 0 42 36 (@block_merge dead 10 0 6 36 sdead10_0 sdead10_6) sdead10_42) sdead10_78) sdead10_113) sdead10_149)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead11_0 : block dead 11 0 4=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead11_4 : block dead 11 4 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead11_40 : block dead 11 40 15=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead11_55 : block dead 11 55 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead11_91 : block dead 11 91 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead11_127 : block dead 11 127 29=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead11_156 : block dead 11 156 27=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alldead11 : block dead 11 0 183=true := (@block_merge dead 11 0 156 27 (@block_merge dead 11 0 127 29 (@block_merge dead 11 0 91 36 (@block_merge dead 11 0 55 36 (@block_merge dead 11 0 40 15 (@block_merge dead 11 0 4 36 sdead11_0 sdead11_4) sdead11_40) sdead11_55) sdead11_91) sdead11_127) sdead11_156)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead12_0 : block dead 12 0 3=true := by
  apply cellsBlock (ar:=9) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead12_3 : block dead 12 3 14=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead12_17 : block dead 12 17 15=true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alldead12 : block dead 12 0 32=true := (@block_merge dead 12 0 17 15 (@block_merge dead 12 0 3 14 sdead12_0 sdead12_3) sdead12_17)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead13_0 : block dead 13 0 1=true := by
  apply cellsBlock (ar:=9) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead13_1 : block dead 13 1 3=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alldead13 : block dead 13 0 4=true := (@block_merge dead 13 0 1 3 sdead13_0 sdead13_1)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead14_0 : block dead 14 0 1=true := by
  apply cellsBlock (ar:=9) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alldead14 : block dead 14 0 1=true := sdead14_0
theorem tablesdead : checkedTables dead 14 := by
  intro k hk
  interval_cases k
  · exact (rfl : block dead 0 0 0 = true)
  · exact (rfl : block dead 1 0 0 = true)
  · exact (rfl : block dead 2 0 0 = true)
  · exact (rfl : block dead 3 0 0 = true)
  · exact (rfl : block dead 4 0 0 = true)
  · exact (rfl : block dead 5 0 0 = true)
  · exact (rfl : block dead 6 0 0 = true)
  · exact (rfl : block dead 7 0 0 = true)
  · exact alldead8
  · exact alldead9
  · exact alldead10
  · exact alldead11
  · exact alldead12
  · exact alldead13
  · exact alldead14
theorem dead_start {prior : Nat → Nat}
    (low : ∀ q, Lower (vars q) (graphGoal q) (prior q))
    (geometry : graphValid dead prior=true) (checks : checkedTables dead 14) :
    Impossible graph 14 inputs.toFinset := by
  have noRun := root_index (g:=dead) low geometry checks (k:=14) (by decide)
    (i:=0) (ws:=inputs) (by decide +kernel)
  have tgt : targetOf dead=graph := by decide +kernel
  exact tgt ▸ noRun

def sid8 (i : Nat) : Nat := 0x183
def rootLink8 (i : Nat) : Nat := 0x120004840000
def sid9 (i : Nat) : Nat := 0x309a80408134141010a14d05044009a122448912247240e70390000081002040b6366d882220c19c0c500420000000000c1834c0429b361489e10204901218482040800502042850a154033a5450b1e3c003163d10b285018306e400038500830604000202c803020d10102040930000c2f2850408060c410
def rootLink9 (i : Nat) : Nat := 0xc1e100d80000000102d05a8341800001d9cd82bc02c8000180581c9905ac0000c0f9806bc12b98a40001693c000341388220c1540003421b418b81b8da9dc113016a41ab98af40218032400341a6c1080000069e028259c704bc413740e6018f840bc67f0099c299c0b7017bc02f41c6a99b026a4689419f8412004ac23b40118a8100a640f60087006d026541b581634101c0c501c11e7c405544c04170c0ac00000000014b4425420400008a8749cfc14101b3c03400000001006701d78257c49fc043007400000000124e815e1a8919cac2dcc27f44bb0006c0dcc01b40c3801d416480f2c12c0002c08c000302944654802b811bc21d42080001c1989e880000189d016e80a3040301ae818540aac6b981c8000240b9801681ce01900000000241bc000000000000000042d40002007d00cac6808061424880fe80cc81530590c0b00e4f02b441d00003013e800fc126014d8429c29041f9c1dfd9d4c1ef403cc4c8da6ec2754174c288c406441ac28d82c0409f822e45a040e2024e020c85a70131425c40d302b280bec99a81eb0217c19485c882780000000242a501fc81f300d401f5003881068120410f42cdc02481d88285c42200ec4116409400000000c224005f0245a95241e5417cc04e8089c41ec594023e80534228007398a8400b80ea02db4508c078027342aac082026f82ac41468212c240023584c7040d0047c2c6015ac202425046a0c25a865a8091c26142315e83011d80cc1461c00a101506d5812c201700004010a0802841035c320128e03c78104018d1070c00066c201e8c04803404410022860861d01c51c0249001a43041
def sid10 (i : Nat) : Nat := (if i < 1 then 0x800200080020000002000d1428b4694c87010258080000018300201c00654a8800000000000000060c58b222c3840e1d48000000000000000001c00000000000000515308c3840820093009438702040070010383081c501100408702081010a14702020410e0a04702041488d06681021c3810700690021c000000010000040810e040810200040034018d000a142850c183030a1428540185040a08207004830004014280400102040830300900020c000100470e040a1430302040060c0c0800e04c9b066949134183060c4451a0c183060c183070068d2c06f409a1eb063708c99032a18b161410b160e1cd06541830a0204380061c3a414d4624170c50c60041d14a14284070438708383063818e060e1c30622446110c1830734646a61a1c58b222d20000000000000000000000000000000028a984610208163c78b024c000532809702000c4023002118141810204b972e4138100049832e9c98102040842e0c21714044010204b8122018003a448914844e9d48448c460080000000ac21a0810204558951a108ab0080058a6081070e3419b001818000000030000000060000000000000600000000c0000001000081c21b240818c0c3018306001020408104170c0001401c800200e06280010204081021a0802630503870408100021c0871a3468d043410202000011a041020c08a020e0070e0c387061c7001c0c5000000010062818e9d0054500167478f0010180163c7ad16b42045a4800300040030260000302d781065c08126042080800000001050b082c50a020c0031e28387260031e3c7830e061020d24200050818883082cf030e1c9851a00388206d51310003060c182100020400000000000200000000000002000800000000000008000000000200000000000001088a0e1c38a0c14daa262041024201aa224499e1020f051014306101c387060c2930c2068d08b830a2618400000c18d08203030c22608140c4031020421421d08c0e183060c1860c1898a150c50308001c3871aa5f8d1a1831006183060c0c0c963203352a180810040e9024946810800000040810604501000008102040800004081020408283067c809207c49f742448912240050a00285123800000002800000e091204083022450112240891224489202448912244890aa8489120000900248050640805071408102141a83804000001428912244890a2c7901600001000c481200000912400812e040810240215140000b447510f1e3c78b000018b443c79016105832850a031650a0b061018b002c080280c18144881832000000004059020400834489101020409006044091214405002448912244890a0000900004892015283060428808040091204188100c188200018b0800583060418f100c1b410d018310401832c58b162c58b162858903 else 0x1a34087001cc00244890c18206040810200001c504080834b0c1c01f0000006164800a2c0002e08183060c0008e02482202a1c50000009812c00b0002011872e0472c0270001023118202040800008393080c32174ac606221023f000060c2614200000003d1c2850a14204003c4430a08102040c44204100040d3c54f23102)
def rootLink10 (i : Nat) : Nat := (if i < 5 then (if i < 2 then (if i < 1 then 0x40201104502032d00010c21000c19190551a7030b2501070207040a0d4603240e053640221103132a0207000d00000618505a0402020705103e0b0d0000220f532d07020e221a63490b530022190700030207080405482601000102070128020c124800141f2b070a0932020703001b120007162400132509130613070000000a02062b00020006270f080e1f5407200c000227001c71001e000f27080d000224c45c20000000241908075712262b04101a00133f1e2302011301052202080a1a3700091749160640000007000c010102170006010e32092a0200000b170c0516023619060c050308081b030b0101020220010201072202005403240c0712400b31280500411225020b1002000003000007361e1200220e0800160154021b200307001c100606010701320001ab1c001b1c0001010000030e002e001d00000d020502002900052302022a00140425300003140f2002052003020705000300404105001a100e1500000008001e00000814362a190c141100100006280103101900031b030c01001200000a0021080e04102409010a07010800000000001607000207030503000c083207060100000b030015251c00080d1c000014020c00060b07220a06080d103136180404002a052f39250400321f0000032c0f1112160b04040a011609080805090100121b0d000304200e0117000d0c01050105030500020008090007000e3a0002060d0202010a0011000c00051a1f2418080514060307010210000009010a0f1a0613000006030000030125060001000303030447000115030121040305000513000b0e3c000f00021a00351b08010200040002050e38000a0301020a1408040001001d0009000a03050000000005011100020200420f01100202001f550000020009101b0330030c030b000100012409060b00040204000207110000020000001d0a03000600020107000224040c090832040f02021602040000000d16010004030d200b0014160012030006110e07020c0004000a0b000017000b02000405001701000c0003040101000101000002080200000112310001000601010607001809000109240508050501090101040d040d050309020802000e081505050502050b0107171100095a010809000201010b0200000203140e000a00020d0f00051417000a13050d003d090201171b070300250804041f09000b00070005004e0b0204021700020003140101030c00000e0b25060b04010a0d1a0000020001020004120c01190a000c0002000f0c000103040d000100130003000000000600160002000c02080000010108160a07060a02000002011d080100000000010502000100031801060a060001050a01000200080104010102030611020b06021d0f0a010307000001000200110213010001010a0000050206090b else 0x8e40093d012d207fb900ec408614037be02361080890041103de6010080727507fe56234b065e108a511814016d9c0530b03044044c354bf0000000000102060a5fd0739a80885000000005e901f2000003022d00000504aa00000702cf207fd8068ab089b508cc7121b414075034e00000a08a1c0230a052980856c171241008000008088b8142a00000303625066c4007300000e079b704d370625b02a0d02bb7056a00000300b8c04b0004f60053200000000004678ea676ec03cb111d2c0004807b370574f0761903d5100dd00082e0113304d0401097009d0000030038a33e9208b460123a089791538b156500000c0768000000000081038d617a504e96068640345103bb511d1c0146e18c4312d1608ec0000010328308557151e0148000000e08f240241606e100000a00de9650eb048290010405dda01c651652b249a905b0c0499f06ed700f4a030021668913f6407fc1027c2041a60440671651071590244704ec0107d510f670673d0477302cbcb4b69083e0000000000108000000060560000003179000000f03f310333b020920045b07a10000030653c05d870826f051826553500a100000000001048ab02e440403e0890f085ea102b905688056920205610a1300ee91444a16e600000f07dd301f600000000001123540036a034b50599414d151185c95d0310be00000406f4b05a5200af1087b70006a085d506794046e103c6d060f40136113e0e104b5012a4056210280013d8516ee01656905e4b02dce06d8d0107e028600000a71820179c803fcf01678026f204ef2a6050849e101d0700ea6026560289000005006edb436e067f51460c0059406ac1030200000000000000030794902d1f10f95081f00000701400000040097903aca663aa013700000d00ad00000000007069c0000000000107ff7043e7a5b3804c69124500000905be60733e02117017300506214933653b0947ed0128c03a9906a3c023bf03159086cd021b10195f771f61718e0350761819062a104ab4057940657d05d6d038a90852b06e0d1260ea8d4000005b4b8900cfe04b381637d029a706bd60104901d8a07842017f00000e07e4235534163a0122460501b054ce12dbf06b39062c500d3d17ee000000000001101a04802440c5068b000004137d0000040484f17910000010746000002021d500fd00000110dfa075f000007080ba04c1500fe104af6945330159b08ebe00c1807176176e000003014bf02a74053d702ed3000700000c0431113d16069d203c410872a0281606ba10177e13d74035f6041fb01cd807649108bd02b2d00478054d004c2a01fb407b6e063e6036fd01701b04035f4234110802003f1a000b0a2e0f0912130101020104040102040b09046d060d0a3c550400011c7308370000067f0003160000090d07160011263502) else (if i < 3 then 0xa144f603e0e0644e0766003ae2125f00000765512038fa0483703db0000000000901f12142ba02c520379308d60000000000b0461400cd000001076fc01c590121116df873a300000c03e4600d6e03654101a0000000000606fd513e2514b500000701da6068c1078a610de211690000000000203ec00000e052a70706e045430037000000000000000f25b57146eb15392249b206e8904a291476c000371049802d5103cee078c00000d0188e0537f00abe06f5545e57042e205cd710662739f305dc00214600a04084d107b40075b81024d08d0806f7a05b7d8658d0103903fb507a870412805b3d6187e087e401ff305ece026e40240808e3c01f8c02430000000032f139200000e050ec0561b0762a0860103ba610c5b01c1e0803c0787b030f607bd102a3c043a80755b164f71711707ec010ba51035b01f41027b404c3a022ac03766079250675f02f280162201a3e0827b164b51550217413100eb183a304586061891545403f5908b1e16d44020d904009013f9010d43576f0122103f1902e2701d52076e8147ba0051100cc202017064e7024dd0467c001ca034a102b9e08965085f2a45ca01143063c4040bd00e2c023531440103c5800d2206dc207a02048d061841070121015a0508d015a90713718c220608b040f60891801c0b1635a1529f02f7810a43059a60709902db6044b7650d1027f0655770504017199026821438403ca90495201c3f0102101cf00269db6e8d16cf403230776e304524102eb03e9b07b0207535086ec0303d14230074a90685413a970434316bd307e0207ae707aaa653d302ce006e3a104e8064ac0181f031e7840ca079e60736c06802101dd0816516d1c0605306fec7395a02e8c96b28063170176f0293708e0b0498d0366c10897123d8041080134b066f4153db021a206cbd58911269731653a46b58075d6005cc00f00048c4001e4039e86163d033410752617b1403ab507bb60488f618300000d02999240d0000000229d087411564801f37038621851a0166e01ec3031a00000a0538c02ee204b22057a2010a006fa700bcd05cfb032e60564224a2e07e5f0413a0025d106720654f031f306bc60632507753073716552d06bf0147491234402a450343f02ab502de405a1f010f80363e00952b421246e9512e43073ff08e171523b0250d01168049ba11c6b02c220892e044e50880600f10000040822e076d3671c50309b146966180716cc8023810397e671d802fae00464063930551007a7d02b1c035ab0543d03d21064f901bdb033b2145b0000090862802e5b840e318dd90589e019b60591b000c9031390879d012f00000d0889f10e19b646b038ed16e1e0858d0068e07ce91526a166600000401d20037340398a10dd104f010617704bea037de172d8104c3180bdb53c40811104bae0441705 else (if i < 4 then 0x805d0224b13f70053fc062010541f1632f04d5503f6e01fd400c5d071bf0401e1249d0030e122160881a04cfb0723c174a9087f016d00024f5031170112145bff01330061f70012704595073b50799513915180d90052d03c13089430512d060cc051f0058ba05e0a04ade4467a067b202198049ddb54c81713108bd50705e15b2003fa705acf05dfa10002023f40153e11be4062910823100290026cc07dfd083f5010b00661b3490f653cf408f00550a02fe70613b054ae026400031d05286b438e1186311b440492b02b70108af16d670777416e8c01acf00a7f07283150af082ae05848054820468a0445b04694020ac06c480732c02ea00182a025100000300d1500f6a041df1640e103f00643f16d2203e5f027a1547d201a2000000000000000003ad808120000031033b08370000080645000000000000000406140000000000000000000000000202df0083d11898600202008d000000000000000a07bed039f8026690274102b8100c8903a2c1534c001b004b45005de077c20666e11dbd052100000f0124c025ea0278b05bfb01729067c00000000000000000000306f2518c680485b1527a049aa03ee110988029e41511802d70000030231006d3e06c32061cc0722000000000000000f027eb083840066f02f61055600000505f4c050aa056d500c01036bc065cc0796f01efb014f61060e022180699f01bf001b9d01c4000000000000000e00b72083300000308ea79454b008010117b077fe0773a11cef16dbd1037b856600000504b92058870687008b7914b100000f04b51064c603480166e4029f000000000000000e0144402c9406bef0450e88cd4039c50716000000000000000e1837000000000000000e009ee025c00000207c3204bc404e721895a07c900000d01f7000000000000000e040ea04494612a306b2306984086400427a778e6040540570e01eb00000d0197b028e1067a914027006f404df3031911497d051aa013de006ba67368723400000a0024f06b4d1567c033e8104a000b6e0016216eb40576404ffc1715f05f6000002157b863a39068fd717a00000a055e402b4903a3810bd000003052fc0276204f1500eff086b0000000000305e2d0062107d8b08c0405a9f082534414401b29142c115b620503101608119b135f7901bcb143a616af00502707914043880168302bf2653e0a452801893089a106d4901d16084cc102740668107f7b04b1e00aeb02a8d1447211612081a8150f803b8b033af009a806e4a068e16185208aea0014a18b5c6727795ff40592103eb9000a501522050071011213d0c012900000004f9e06d9d154e806595013ae07ba586974047af05ad000000000060426a06eb706942141400000416e90000000142c163d0037000000000000000031639f00a450563c105100000f143b else 0x4377bd616fb21788f05f8e0312705e6c12198078bc08a3271874118150245000009063f000000000000000e188200000804bd106da7059d206227011100000b05ef00000000005057f00000a00ff00000f0544e11fe00000a14b0305a8f0154d07002067601625a04c7f0760603694083cc06b0a03b5708bf001df010ca11531e01fc9021ed053c535fc00000808e9f08d3217ff818abc016f016f29032256501418c500000000000a43ff06a1401ab5014500000d06b5805f7e0028c10f5b040d0044d30414f01c8903493078f20456000001044af00e02051100000145ee706770253ba06a5000005a6690000070424205457152f80180e1095f07f63003b18545001a1b11d800000d00c9a011ad140500000906d12028af7183516de50804808a7b08e6d089fd02f0a16e540813d039d00000e1490615716057e00000a085000000e0481a00a360840e55720000000000e0558f06efa036c50227f1022000009068360295a0021405c9b01ad2050f4070cb03841049700000f054b602ff00000d015e70193e0013803fe00000706ce000000000070000b0453906df90712b07dae054e406336062e700050088c9038b1856400000405ee00000204c980851b014ee00e8e07f1001b881420402c490420115c900000f1698e00b5d02f4a1215e1813e0649b1649f0183e084ff08bed027d117b870437b007f90115a0071d07e3e05eb808698464720630605722026ab0759f052d10091105d7f1801602ada166900000a139690652a63a4506b140547c05bad058c104da506d7a1864e004d40308f075e00000e0859117933008e610fc0000020634a07b7c00486044f40581d0819218c020390d106cd043300000004480004f807bc7162488401716ed7072ee06a2206248058dc07c6907d4c01e1e01552081b0000050385b01cc00513a089dc0418c02cd305f09b5ee9032610318002bc505ff300ca707d040486ca4a1c18baf00d9703e15009280027201a8d01dc1069b00000c02720147a007c000000706c2e0514c12eae0642b04467042b00000002e1346e8b16c8203550077200118803b794567a10fb6045d00000204dc8015d3a74c8005ff025b00000a05fe204ea707de00000006657164d33450655b38700600000901ce61466e149f60778e0253603a53655b40731211776017a60797c051ce0845903308029d00000404f47189c00000307897080d707d1b10a39000eb4646802103105881439000000065f00000f0490a05fd9018b0000000000e148ba080fd0151502c80000070708000000000010156bb467fb4d190174c0058000006052700000f6559000000000000000d0417000004016c7106300000e04160000000000d06f800000e034fb03c0c177b60557d25a20000000000d17a100000000000000000000e139c90087603d1d1))) else (if i < 7 then (if i < 6 then 0x16f5807e1a04ed000007a694b071d0087a9038cd18bff10f8804b63053660807b03bd00000301d49023c4774e9088af454ce021501553c03f0301918079370359c0381301d6c017e607f3e055dc11a98274d41020808317b536b08e52082d7138e60368c0690416f0015a2202c1d1009f000921425a655a00000908eff06b8c016ec06c6010a200000b04f8e0627e00330000030523502e3a100dd10c4b184fb73933182e7076a00000214297124df03cdf01c7b171ae05a7a0628d17ef403f8d10dc0045be03d89019d204bba02aef067230580500fc0000020406906ca00000404b7903d9904559161ea049300539b08b3d0165104d7507e940688b778550310f079f80317a18c96152ac00dc185b4b0391836d8e009631248a00a20032441421208667077ef00d0b6641400e1d04445183fe0090a001d8062bd0598e0809f070ea046000022701e65656fc04fcc0237404434069ec07810177e803ff206dec07ac4032a40135208686029210393a07c11a4d2e147eb048b00000601aee03441030600000901a6000002063ac018aa7237c004c136ce305c38a3eeb042f5639c7018e6037a7055b9016ba13f5203604004380596e01b6a0184c10199101cd02576067ee0783e072cf05a4a0070504e322233d070700853811b3904d60176a0146d0086dd0776d03ed80769ca4a3405170017510553906c9513e50025d306d6a047fb10e0285470164ea043240610e072be010ec05787063dd08da7079d40336103be118048087cd08468000f10001a04d8d03415027140867c18088074d5077950428604cb80873000001038300000108f3403072058500000d6161501ca00000c04f38071100000000007105600000000008077b2029bd06a02146720522600ed000001144a000006188c2612c9023d901bbd0171304c4000000000000000d17f4f06f1d08478159f7048e801270000050389810a600000701dde7694b0119704f2ab437f05c28015b701bea02625007df006c00802e6639103c7b102ce0077e02e700000300c7a0057201a730429201b4105ce20877505e1313dff08af81007c01de4035bd6169a12e11048f501fa716f7405a380196916fea030d896d760178603e6000008029c202b30112a31880e08dc0a0ac514ac200b4b03af3024700000000be614b4206c130586d10e2414967030e0000000000e0710945763068d605550000000000505d3603b6d03a696178c05c700000818a000000604890017cf008b706ddb0893602790000020131605d5b0353d0739006625073c0000000000306cf1184190185501afe16387015f00000400f7605fcd0770c03f9a042d800745739880692903bc6071a5152e913de9039b50471816c4c05c4f03051083a3059e2101410696406eac04086014c3025550190085651043dd7593a03211188 else 0xeaf060020294f0615505d1d04fb003c30000000000801b19179710053004a560757616184018ca024eb650c105d2505c001546918a2c18caa16d5606e5d0275d1551c01fe344a7807cda039680818a031d10849c0743401b5b10bfa016d102eb1023a103daa05e89019cb0516500350035e1024b100cbb0638c03dc0006a46749a05d07117a407d7f04f5d102301424418edf04ca804946070f9069780510a00f3f6237a1032303dfa00fba1535144a970149c0671b057780337903d7d01630082fe1459202acf08cf5078d00000914af60756eb647113d51249db05ae9110f0072dd2749f07cf0047040602f079a51487218d100000d03a1903a031398b04ddd0821902968103d214451089e00000c16f40000000000000000104031269d0651102563103e1b415105ea215251622e902d8c053e000003164a00000514ae00534104a48066e905830152101054901a51051b000007008c00000a08150000090392246d790801b055900000805f2507a910684b95f750476f02083143df14ba40042510c731620103c26037480750a00cea06bb000000000000000d05095047500000000009008130223e184e3249f2067d218bb506ffc05158101ea0228a017be177dc02e050669e6380000006056f00000616e000000d171b400a600000b16f1a0782411c7c07a3b034c505cb81039e146a404f740125504e0a040c90616d0340f14ce20525110f4607d5203e2608e2103f42024ce050570810c009440026c00e330260d6162c036e501c9a7184d03e8106aaa1783607d68163b202f9a009be05e5916fd103b2100082078ec047d0012000290c07af301eda0277907dc0039490571802c65000bc07c8f064bc086f000005016a708294015c904eee018fe06e230018c01d96008500000000004082c407f0201b3610066102de1634116677019f81717c454dc0388f072070089c070ab0063206f6546ce4065d008aac073560150e102a516e3a071ed07b2e08e4a030b9003e1101f003d04003d002d00026d505dea12e3900b9501f94087500000604d1608ade05909657f00000404c000000103b4f071840834804e8002aa0000060291000bd000000000000000404c87030c0000011522e0765e065b1045e2037e0033c1147800000a049ff13e1c1026005e3607b5e1802a06c58143fc03828073d604eba06c7e088820130800d4a18506104fe1692603e712671b123731573906ee402ef7274cd06c800000f05f9300ebc04cd2003cd00bb00000a082b8153050842f04ae418c36223411057b04a84022080650f07a271244a18de6088f96186d02d4f13dda06067138a8a4ae7059f014547031c9a5edc12410077d00000a05af00689e151f5081e718b0407cb501dbd05fba6640604e4b061ab0088f041ca042c00000a07ab7043cb650bc0447000004) else (if i < 8 then 0xa0832e08cb304a04021f808d990141f088eb085af004ef06d22059b655fd30200a03cfb0050205a06001a6153640297801b04076c3043fc1481313d6f182fc045f902e968498114a070148814a6d0785516ef30487602260147c10774c0435a080c800833100a3020b608576012c00335713f9d013247380302da708c1a00f800636701577019af18c11147dc04e6007e2902f580887b46d8d60062053a406e9b0161a63aa70409c07448060d0638d9a4f6c058a14421507f97028c70496a01e760520001e400464d05b680542305b2f0425207f2c06b7d255a00000403d30000050767c04de8026bc1404f0549005a27032b31524e0637e0316a06212b4d37005a1014ab0656b08d21124080751908d770664c04d4c06a7a07a4604150046231205e039a3772ce638a607caa084b701a4202737005b20011f052bf047900721e06a6f037850575c06d031012a8531107d31057c404a1e022e60371105e9a00c6f03fd81899b0836500f2eb42e21021c056c5141dd058f4031b90667a0064307ad9071f3022280072402af40023105aa808b6403aad045af11cb544bc70106c010c9037761671818b24021390387717c4e3468716cdd07c74184cb0198b655c5063b2066bf1716c061d5153bd766ef03b131465e0351d0682b03c926593a035db0288500aad075c3025fe8535506b6b033f105c110194500a5d002a8064d502d980533201874009c7046500000a034d301bab03a4b6165b05b10000000000504fd00000101e380270b039500000c00780028f00019e003f700e4905b8d165ac650ab01d3714ad202d680681000006b55300000e638e905ca0072f905da30017e032780139a1491203b9400db607884154f30419507db0060154558c0641e0067001a9800e77070d9053bd040460060706048047c906c0b02164148de16b6b750da036a966382038d7066a3163e6087de101b1060761426b02617035610806301f0d049c1042a50079d0814e04e1d024a4074c806f08066d802fc9a43220204302989046b1057bb06ab002a9f03b30000031831c443700747b13dc1174b91806a0703000003043b5046300000502fd800d5685460000000000408ee0037ce033211055000001055f200e600000e02a53011f41786e04e2602a13084411766e06b9e081d90233010ff403d6d0034504b860002000000012e00000c06a9305ab6342280099103efd11b100000702ca3007c7138fd072ad0474416da94553f07bfb13e4105edf1217902ba7125cb02d2b16e4b24a17618990878c05e77047e204bf40347d028d00000000000000000000e05bb812dac0597705db00000a16d370246302b0c1528304217b3e1927504069ae1510f019270158f010141498402a6416e2a00c3602dd21650b01eaa00babb5c0e071410457e00d7e0655702549001fd17 else (if i < 9 then 0x5c53046f606487019eb00b0601aab04ccc8643b050b2032cd00d8212385772dd1812b036d203c85014d6012bf44b630039c071c31028716cb745eb51883f02583663ba02e62108055573f17fab05f5c0841308c270075504a38069f10619b10cba04789026781018808b5b0207f12e6c06afa01b70082e545ef724a0aa891e02c3501477028b2020f603b020285e07a5501e8d01e0c0609916510000040865f18ac000007180c5007ec06fc825b4507715b4248173000000c02f35655570595e01c2000005032570407c08dfb146b208300000030098418b940738e36d7905460000000000c07269a8d5106d540252823df9025ad06e6a05b4e638b81013507d9f037290138405b96002df0740a4497c07cc104e50046ab058240354e1626916422087600745371861022591401c021cd119ec020cb03f721761f12de200445006111803501a0004d2c4475e612b405c84760ee01f5d00697010500000f13dbe16dcc03521121c8060331648c02f8330a8e174e4178f00000f2546c044290169f103100000301cb20338508f08075a00000000009104d113e3a0795e022c00000010db2b54d00000000004b413e266a5070200000d148c4009f300a9211b00000070375d045100000900e5e0524b088d71048303a700000307a6000008084a31422201867750c516ea902825b4350062d9030a204667011d30594c117860473807b9f05353060ee04a9808e85849ac157f50566101e2600b3a0704900b11153c400dad16f3e0331100151050d4021802499f771e2145d4108d8086af02c7a674fe180790402904ce908483004a0000026182000000000000000b085b305a6713ade08208061e6676c0000000000f03ccf164c804220000070239c076b2156e00000000005055cf06464080e106e7906269041e2a4d6c06405054f8040a5769380540f007b608bcc0439a035761721f1742f047bf04a68122291180e145c202d3105d990203a6398b08a8a16b07080ae00bfc05ccf06f3104234051ee14b9000007a6f6611dec002b401e9b24a300000206f960612214506059c105bd3011eb00c2000001032db86420079800000217fef02ecf035c00000c00a852564408f1407eb11468405192007af1532f074990660d06477002e3051d00000108b8205739056770552307ed40164207300073ab63a8c081c40623a074e804db606ae50367f00766149b614940000070232707e75123f104a7106cd106ad900fa502b6905fa307243145230284700b2011df513da8849c000007026350531b01085144910055406700b6e730593404fa000008049e917317712c307faa0259803dd8008f10339514349070be08cea02496674eb06914062f6008a302bd006fbd052ed1036b77ad902f11074ba061b301e50052c20693707c2903615057d00329505c6e013e else 0x21484702fb005f18b4bc905bcf084e5148efa896307d2a000de0611d013bba4bf8011c8105c914a5b0380a0587c074f010cd702a27060a4045c807e82083b210256004b80358b056bc0287507190240fd0364e004950828418a6d0843503eac037f907f87002c604d9208c7608db502b530472f04c5616fc815373067430399f018db148f208a47041b812718079090526b08053020ea16c91075801764105f3e006d90202806cca03f2d0411b00ac68551d17948022f2011b500c470084767165440440895c013c105b5a050c814a9a05d4b0086104300000071616506a89072510110a00e9b13e6e02cc00000602c0008547032051886206a4e0199b002ff08d8c0554e18a9707348120100870113d380565407f5203bff085cd3453b07c50000001815e15a5e63a5104ac807639003a00507f077af1540214a10043610040c0212c046d444a860663b08244081776509213f3e6177f1435603a81032f900f92022b716270000000000303464005600748d1555708c8e055a60635900dfa06dbd1427c13f4b0143d08637046cb0283902343078007394e087121725401eea0248f13a310301d02be444fbc005477189e0729f0491a173e600f5a083500000e06780000000000a060b046c2307e626129000007023e3125ba069500000003d40000000000008e70183e5107b801d796735b0314201791033d00754c04fe10839d03e35017de0126c141fa02423021750065e274f50342e06ec30))))
def sid11 (i : Nat) : Nat := (if i < 1 then 0x400002000811c0400002047011c380009ae0000004c400000050a08101831400000000c18306000402a5451500104000000180102068a14045870e1c3874e1c3800e1c9000060387501c3870e1c21208000870004087500000100000073e003870e1c08000002070e10207021c00a0810000260020204387020400002040830204081020008285001470e0c1428e1c143050c08002080810008681000400280003800e1c18000000400102700020004002b8080000408102029c10708142850814000000000000142850018002081c1000a001040644c9122641151a083190c1e81b36643196e3c30c083018c18306061a18c9a346508102047013205b810c0460c043060c0c543191a4c0810228c8102cc69d1034783621c0810e908820a8c020308ed0a040408102f82070a145850a142840a1428c0a1428548142850a043870a142850a30605181428514142850a20685141428520142a30e1c2870a901020a3870e1c3070c8a44c99186460a162c58b162cb91229cb97003c90f24000182e28b955a2968a143020c24100012e000812e3e70000040002e98c001830f802a04083025c08b029c0a70204b8102048971804000001050b081058114040031e282040000793001088204002800402a81022918b24141850054500006ca8d2b5c136162d59d16001590808902043c78f1e34102160000204081023608302040c002042c6820408102043c782040810204486820408114042c102240810004302020408102000010206081020008102082c1000408000000008002040800c5000004081020234102060810204080000000102040811f040808202080b0ac3408104040820210682040840400000000828584040850a0208002040800204081040e0010002001020438700003870e011c0473a341020434102082c002040008006205000000f0d661068e10d858b762d48700b9280248078f1e3c68516945841034503101835206183060e20000002018416206881a3c7860e2878f1e98592262898d26341881050a0316d4414160000a080c1830010580160c0031e289840c0c187000c38670000250000012400128628609b83a4c6931a0c183821028000000003048c050c50188060c1a6103418a077440d06100001e2800300000800004314000000000000480a18a0404006051830f820054f81020c98102349810204181020498000000040810083060c2070e0018a001c1800210002040821d1a0c1863265319300c18d061420b000c500140c001080010204000041600102040010204001011200080122449008100000824489202420012004890814000081448500102850024000001028000240890a24489202408902248001204085060c1830a1400002142040800000001020912244840810009060c083120c79612249010a24081 else 0x1e36140840848204243060c0800000000020408f090c08480000000912001060418302011810b0030850846604081020408102040810204081020408102042010204081020408102040810004081460408102040810294083180060c223020c187cf9f3e3041892a67845ebd080020000e1c3060e003800810204011020408000000a0c280003cac40d10b8596162cb08100000810ac41e0036315161c78f1e4c4081a285081a1040d7c2068a0020000b6186bc1a04b08021000a000)
def rootLink11 (i : Nat) : Nat := (if i < 9 then (if i < 4 then (if i < 2 then (if i < 1 then 0x4020002030000b000100007070104602018182a05088000003118900602030046607000200e1400000060b100a83406088201c1e0201476030b00002000882c0e13040044e020982c08030493846300381c0203218200a0810800100c0300000050180c50000006c00050282000010103c0000008008802130080006000001a1d010000803000080404028202600000000803000081c000000886000b8740607000500207019800807000001c171300004070b02c1805220000621008440402060080e061981c0a040c0641e0200800001900018000500800000002064120100000000000004020904800001a03808060000000240505074280300820201900000060d0581c2c1e0001006020280022000180c02000982c300400008000a16048082e010b81006108000a040201426020f07418020001822000181c3e030001c0c0b00048001c00838240b0181000000a01c0220000080a0c0000000010484404030100c00070080400000000004010481c1a090900820000005802260083c121800020d000020240402020080017020a800011e018160008824620c0003c001401818000201808120000084000402078400600808000f0980c0003000240c0c02028000607800000a010580613010800a040201c160d028141c1103808022604888060205004000d000480000000000400030100228008280004000501205030140c0e000044216008041000078201001010140c0501050020a020040601010200200008000e000001078150004802080680826000300c12031180000030d80c06030001016041285408060080402030000002010002058010105c1c000d8080001028200000048040c011300c02080003c04090d0101e00110040e0003808060500804001d000481e000506c00000280002110000c0201020042a1100808000100000080c0200010000700c1e0807010062e000200000020103205000100e030080028010200c0201020302201000140203000580e090000c08000500c06020107c0a1a0e8000a03080100400000104e00038000000000000035048200000000000000008045200088040809058000600000000002000000a0c0083c04020400426030180800050280c04010385442030481400010083c0004048080a060c0340201050040200058080006070000002000000616000040a08000a0020004848000701000000a010241407020b80c0400000000102800000101038042403010080e0100416030a80c100723000140300840000006004160d0085c0a0a000000405018000e08010080600000340004018240002000280406038940200058080a0e00000182701028000f0100006120083c0a01018280001040001e06070180002020041000060300c04030040a040001000000b0380000010001608058040405 else 0x30001402020b9542c000a8080a0001129240a000041a1a0022802030e8205a0d298240013078205c060178414092000c7a1c090cc00050202032030796800010d028041622800001d00054b6010000000290b8000000250b80c11028104000000a4280804bac02100685c02350680002003b9440202160140c000b80c1607005218a081580c1e140e0101a00000180237010082c2201020180c038140600078000600000001a020280800020002406230680800010308800080a81078020006c500341804240b1b0045c0004044040a1da5408000d02c12080082c1c25100141c332581c0024018080627088243e160a0108803008c8060d0a060041015008dc14000120c280b8204005018100019028081e250602824010f8801c04108250e060680c0e0b03038020f22004000f022380c021c0081059098241e071580436042e808200617814001e05800100801014302f09800000802a281206040040035008000c00000b40600258144223080e442490013008170600008020202c0a30058081234060040007050c83a04008f420210001c5a012400004011b0088a02090314c01058000a00118981e121001400000c00006040000c140400034001104000063d000001c1b0085c02022a81c3a0001180000b0001000000b8000a280a02c044a0002c1a01010200c0000014400300000040f01050000a0500004210000002201400832020200800001a04c1600000542207010c410111404c40020a02002320000400000102c3a030200c0005078080e001580804160702c04010002c4c0200024061f2080c12040281416010400c06080081c681b2104c0008038480c0800004320005858042b0c00002100000806042680c02020d0485005010482c011003c0203020742418010280006008080a06420004a00000300a7700888063d0488c0e1e0d02036000380008000400c0400150340602008085c0e01034020c13004021e0a8589a0b030000c020b8000e0c0000c2602008082e132c900163c0202800174001804000a03c74030092058010a80c00090a800000e480782c0d000540a03000001c02000041a03010705a12078002e0c000001000000f00603000302e0b000000002058001201000180a091b00062050080c040003028020004070002e0200008080280c780701004100b03890000000810068f070481000020081e01088001c2b0780000002100826000000024165d824c40306800040b020440215258081403198000c00010500400018240000001b41c021281816000380c02030203038060b00c0e04000301c06090700015000500604050081e0b088340401048303c10038402203028100a191b0000a05008102c91000040a08018180000000907012008102c05010181414010d41c290b830000a0001418050003000040280) else (if i < 3 then 0x3601dbc897c80024c5286782d7106b470ad280e63d02d1f0a6b48e43903cb08e266824d985aa303677028ea018c281c360282584e14ae15e8a4218242a036098d11a05d1b840ae8042d01ba70532a04f23031310f188868a0854450440e8baa38df8c8720b000b1061ff04763011240503444ba680c90dcc3482d2e0b055835d782638860128377902ae680c6c8a080837e583e0f013fb001bc89bc700b8f8541f3642786a32bc828047970109a01c65818bf0814aa175603dda047890523b867de048e10020f829643535c80bf3053332b7ae819a6042528cc418e7f401b2f0710e8e1d0000018d77a0d9550efd385d600f260012ac8175d883d78e878000038626785b1c8d65183c1902f38000050532031400000040e5e8000078ec928e4ad88e600000589ce781dc30ee5481ff4000998190c8cd6f0d4ce8d8e6873da08b0785733995c282f0d0579a061f50730404c88016a08af810a85204a530ba3285bed84ee5842be829bd83d2006790000070c2100000291e4304b65040480b975964682252c452df020ba805280517b85b498092a0dea40558a0a7ea01f470110e02a16871738696900e95307818dec10d33f86b688071c0576b88973842390845b02f300000314bb001d6000007011dd0abd1041600000685c33849e78ec30000040290e0142881d0686b6086ba8000048b60b035500000303a6000000000010da8e03761007078e0c9871eb09f3a035a2037cb8aca00577605be7812cb0e450001010631e8744a04c9203416809368645401da906d3b82e7c09c3e007fe873118187b063578287c867a6555f90294303613015f68f2348442184bda00cf28dbaa00fb78e460053c40eba4856b3034a80000386a6b001e28961b807e08000aa17ea04d3205c228181a8b0a9800f582da80000686ef10ca35868d6872e78d5e800003855518139c095c68d606827a805886832d000001026d5037510329f04ff580858000038948e8a9100000000000000028275800003850de026448bcd80643a06ece84aa611d70000000000604c5709ea1844d30b668000000d77502c690208786da58e68ab4ef521732869c803f438b0278a8648c15800000803e686d8000002827d90bcf101b8088df50cbc502040000018ee0f8c3b104bb104f428a98001a5b02be6830bb870e402cb303ef810420e04a105e0603e583c810000000640c800513a520b81618001e8062c0100830050c14016170180c00240600002011b808040b000042218121641e271e03008510800022040000804760102c200c023c032020717c24050188008a10400158130100000c303150040211024061843a1400283882404190009814050080c00020281c6a01068100204048004603071280c1f1587000820109da6510c0207626028247a200083c40090004c06121a04c001 else 0xed2a2258c86c6f02c0785b3a8cf8f011a0850838438b85e48033254202000002046528a05c8519000000071fe01f8300d40000008274c02791028e000005044a80000000001836e78f2180000080ea486c7c04b920345800000000018a22b850f1851700000183288a422b8c9e4850bb04a8a838c8803a61cf51004108f05582448828ff067980000701488819ee02a8283e2f0bd2384cc300f7d864ab0256b8292a05ae6c2032ad4b2a88ce893c403c8b001568d708103f884a3688dd72e4478d4aa82283893fd012c483ce780cd886cf8807d00203d0dfa48dd4d068140de6f8212c81687a13c9844ea08ae601c9c8664f05a2a04d9005de98ecee866bc068ec0dd73225918ebb080021836d38628f0ce8c8322e046a78589289ebc01232814c60ec008252280fbd02ce0866b3820d78642580e0a840230620c02881005f00c6fbba07b8388d818248262b0688e0a6410a6d0869ef044368e88f855b504067030620096283dbb81149063ce024aa0389784f69072285499d03f1b00801a421e05168001f483f36845a0889ba0dc03821eb034a55ca39d4dde088e203ffd05ffd0bfcb027b3864d6814d20422386615869b185d9d5c9e1858cf0243d02c3005d3803945aeab1b2c428119e84f4f007e88047602d6186db881e680cd2f0e54d062dc870580000382b9d06de1838420462704ac2415bd80916047e203c7506978000060f3b40e531896a203c630921f00a470348405efb8acda8db9909e700618c01b79860b25cd6686dd201aa286eb71d49b0d6370ca4b8124a047c088e4e06fab86f26d418300eba821a101eb000fa5885b000000000000000000003862a00000000c3fb486189563859e9806220ec13d3aa78a5980000382c51051988468783ee60583396475050e1074afc512307404851a7803b50011a038f404d6e095a8000058dc46d30cc014b30cbd4c17450289d8220e0e21d0111d850130a2200000500d778e6b58725180cc902ab38059c828b80000383cf08c748000000000301610818750d40e0d2dc863e8000078249504c780000000000000000000292c1186ad80000286360000078075106df8000033ac38048610141e05f340312f9561b043780000000006005e20f074109e0019728134306340000000000708b400000200e200000606528000052566800006822e80000685ab800001022df08c540ada354cde02f480000000004864bf0c5bddda0102e93849f801cb80000000000057be826d800003073698a3a6064e281c5000005074d7052bf067e7b2fea82b000000286d50003748e2c30deccd27688ecce0076a019c0010ba0670c85423006153b1be06a0d00b608d27d85a9e0640000000000050277e868278112a02a180000086ffd873aa01f5e845700433a0d2848097181ca95a59602bd054061823b8353)) else (if i < 6 then (if i < 5 then 0x1b684397801368cadb0303c016d50b4790f1388a859056813021b364130053300b2f8c89f0173908e32009a88527e844f80285700d2c0601a01954837ec04f918327c0419c32fc4802c7a59f60951b0046f042fe8a10d81f1b84b228137808f6883c550444b8347f0472b013a40345683350026f500f730359a84c74070c48384c0f2a58e23a03f2a0dd0300aaf42d450660a85cc481cc001dd75560382f28027270c9b18d14a05cd706d998abe903a68065668489d8ecb502ba003a3ca602504e5989ed90752d88daa8a7340e14905a5e82dfa8394906fb382180000008197a8bfad82fab08f240912b80d0406cc00000280d100000482db480f9000000d08c80000000001014800000683bf703f670cff402551820e206fcd8ec6d80582860eb81e2f00b418ec2886eeba548c02cf2802558715902aa805289048b284e3c8033792ad60205b049c58f0e204913816058a2420586b05a18814ab82f0103020016d80000000000000000000404e26045b08721a029f580df8000000000501a99824bb049a3072f3c1d71816640646685a078750f81d6e42da58432b0b78608be1802300000604a5c05d68000058e39d0c3190a4ce822513c81205dff01e26029980000701065024c903e64863de847f3064080b539833c80000483eef871f10473702b168a1b0000068b9120a989058ad814df804c000007857ff00a5e0e11905f3a84bc8000068747000000000058006004d482724cba9ed8e680000058755886cd6a560000000000060a49516448000023b2410093800000000008dd1901456d0c7522408000018ee3a225800000684634074fe050600000186a100000507033826c18a888000070e3c5032cf225a6853bb822f80000000000000018d23800000000000000382e080000000003061df8d00800000058880000380da501cce8a32382a4101898000058dca6055968213682bf18a7530c9ac8dbfa043bd05b088658b8a7620647d08b630479b874210d4fa83abd0215c0c87380744825f532ded83a188005605fe4821d1d286c02470001a189915827e19546781477c2d110653f8c82d0841c0399b03d06061aa00e588357606e7e05a698108f0483c81fee10c3608e058084a05da68184d3a00000001039508677682da0000000000400a3f013840804684f8c8e2b084e940596920e9098a9a819068276a02d20041702b97602f1f812980000000000000018f15e8816203d5800000000028adce818100000781c5e01ac00000000002018a28742a86f2b81b6d90c50000000000608aab83c680000202870000000000000000048fd2c0e8000000000780c9d015860d15703ea98d19000007065758255f054eb0b0fd82e008af43822900000001fe30ea7e82bb000007834bc01ea2034300000501b200000000000000038340d805050aff9 else 0xd31ce207056014a40082a0c25f86a4084d7506fe00591a8617b87562030e402ca00000000000000078b6670899f8433289e18000078702f8dc19cdc68000070120a8390700ddc9ac9f05538000068673c0109786f70000068a21e08433857080000588a93056c703ba800000000072a8680000183ba00000485093818800f14a8058906f12bcef00000187531031720f311071200000383a0e02f560293e040b02599405c6d8491b8a48a836df0da9188db2029ee86440000040d26886ec00000682f6800000000008386b8507082df0000000000503e06025b50ccd6026e885d7e214f109de0069a785e1dad4bf811118d7258577b8a1d30406901f9d8d7c58b0e585e47009b785c65066410e0650e5f932fe3b1eda8c0470ee5984df2857f70677c82dc0843b083c250d10fa0b5709d9582e3f819d6863d5070de83b108161d01043062440a69503d1d82c1e031ff034d88509a824040557284ae381c168be4984953889860471b8d2e00d34780c434dc4f85ad401a0d0346a04cbe0db948cb8702b3405fb8826cb088f30e314889ef05ab78595e0e0bd06e2c83bba1a69106d6e8198e018e98e8348623d803d90350b88059812189135b05add08d768d4a681d32043858815b838b2062fe050f8000004528985845873be0922c80b908da0530f5a551728cb9d054038157908a4aa3f380000083c080280689fbd9999c83e4900186c12498260edd9ed001b2038598450986a580000256c82819900073f06af58ea990a7b985db604e410d0c28df6f80dce81f608536200a0803dd3017e0053ae065d58f41003c30007158a89310c4e8134b8dfc40e8a00f2c48d199047020069f225658dc9400770025ec82fbc86bf40000409ee583723a417281ed2036238286a846170288e0434b06c9c8182b8892182ac5807de040308743d05c9d82731864198737204c3e830b68b92b00921059700000684b1000004897de8ec5e82198000078a4a80000000007031e80000000003cdc4081bf58c0e302fef8e633817c8000068549003ad483256027a280d6882a7a4d38f3e2213c84704eef80b6e021908603006a25032b2856cf4de6f841c483f100804b034d00000186d5a8351405d280000280559097d7867b300c148e91d0336d0226e07193888c682d8201a7c8441d8599680fe14dc0884e98859de028f000001046e10c88e013580000000002035ec8539000002027d00000688aa0000078565186218000028a688000058aae585790000000000681d57066af05008000000de018321f0b1010c0d68da5401be8000040320c819f2065f485e588b01d019c906b2f83f888515203e9d0131f81c0f01d200000006ea00099f807950c6c900ec8022148a62d83dcf8e15d0040785d200000681e8302aa00000000002885a80b90b82b82011c383e59839a485) else (if i < 7 then 0x859385b1583b7283eb28805401c28000071a7f80000202d1285693863fc08a2301d9f018b40de100aeba85f63259fd08eb00000602432008678e12e064300000000004049b000000000010d100000000000000000000038af0700c63039b38671800000000069a7cd8011000002096b7862768aa20036938038481a8a8cd118240906a84841fe04b3282e6f822750066e8261485dcf833048281203e2705429812a385fc0003990910b0e19b08f7800f0ccd77f012858606a04b718e36d0eb9583c2e052680000381ee00000204017011040277308d5e8415784e020e9cd8078e0cf79815600000582b790966ab536c843408818f219678ec3f84dcb8b11804f5514b9d0313800003039e6805da0d92d849c8817b288299b1f3f8203680bcd85f8d81a32857af02112073933633800000000000000000003867af0638f0a0928c9ff86f4e8535586c1e04401041d386ceb094f580bc4808fd842b280af08678980d360056b830df0d8f6028db83e7c85bd088a028a906b66c20257a8f327804f90b37b95c4d0e47d8c0ee302388cbad0a7d78292584f3102a758c5740caaa83aec05a908e03c03405d4ab102d320480282a0e0c82408a1704f1b24b6a83d62827470279e03fdc8b2530df4d311238939d8dfb48086885c1306d0882baa002a906992073a12d5bd9e2a4a1d1000001859f086dc20d03d06250000018b9d7066a60ebbb00bb281af084f140c5a98031981af90632b05e7685fd80b36183ff702d6982a6d0278791459069e20acc18dc4f85250005cf00a4e050a883e6d0014882e7080d92000eb842c708a9c06b3086f37835e792cd11d4fb81a638200c8ded8217fa8b94e0515b8216a8526081ead0428903ca580cb80a24e022aa05e6080ee78b67e86d780000683b6b2601c03c46055290f358000000000000000000000000008e20851320d61a051670707b012be839888c2738042000006832258123b0f3dc56608031220cd6501ae0000050cc8d03337058730932382562855f0073800209dc4b9f8630001036866e28604080f9e83248074a4029e1032a80748a88ea5859b28b35056158043ab8aa7204116832c28561745a498d1c80000006dca0421c868a800006029000b9e0000078391e81db50493685b2105ca70e191002cf8dfcf8374350dd88943b071060327106b57038800000000002036a8000000000503aa800001840e584428000010347000004833d252004811b8000018944a05af800002b661b05d5e0581a00c730694285dc709d620740988dfd094df81cf8053f6001c183a2e8470f049080000200f8b0d74e249e2845cd00e288533c0a8780000000006824e704bf2883443480c835bf885b804ed98d017025cb848aa85180000008e6498c37d842d101da608f0b2ec800b749029938ad9c065fa05820838d404f7 else (if i < 8 then 0x38000068179f051ca0a86e028d68d32f8ced186e5f862f1033e00c65800000537a8000000000383393043118b1cd0f07e8598c0590a817f980109da56d00b80847520621102a020aefe096c08bb04834223876d8343908a698d5b3868be80300000000000586c8c85f758209000000000028317b80365b2da80bcc78284c066db816951dc6282b2904104002b90067f8334f0474d869bd83d2b0a468835cdd0e6b0df96822f08538500d230ec508635c83fcc027bf09ff80000000001038e0000000000000006be483044bb048510459b0e1858411e0443c1d6ea805c780ed708d7d8564f8ec7e8b2fc841414646501e980d31b0535d8e1dc8160f8ac9a8cc7408229836f6867270d27403ca88e53a829b68237b0572886735853e68a77503018060b9526f280f260661d8522e83cbf8cd7e847208461c32dc480596829c10608481f9102eda259ea0493a0c33f845de07357801da32e7001c45be765822e7854510751800001042e981328000070dfd7074588e8a98da1000000d55f188e9b8a6ac09df00d115011ac817ba869628d027060a68dd8582055843a5858f384a1085a468512d8382a836bb0e42f0354006e250a3990165b067698338d9644786ff20550d01414867d701b310dc2b30222dd1a3839928b933846ea864a18e52a0615f0541112db70b7b6888ea810a30e1068095f8d658034b206ee00605088e42845f3858558687eb9b1b36271828588d90c80ab588bdf8e050000038158e8104b8326d0035b0a8f982c298655992d12862c303db3d8eae01cf70cefa0678131d2e86f0083ae302ee000004064998b3cc8392c0bc280000481673046fc0316104f3d0602c0605c02d0f889300b00c019b6018d4057b2092a18530994b970e76fd4be88189400eea81e348c2800000000003832a386cbb015c2822be01f27815ae0898f9dc5683b9683aa4026b8000028536e066680000401338000038c31483f390332f84b68000078108203ac004fe0000078ba280000006e6800002810148a0a103a56b487c05a8439f3f81d180000000000839f30391000000000052d408000000000000003824a105cc98610586603023cd84c2380a148b670000050b9f80df780000686fa405c718371800000027c902e8f0c37203d0b85bfd8f162874180000188de98dd1783568000060183000007842a9040a386b80000000004a061b1092800127b845908a70a01f6a91778801ed807b88208f8128882a4c80eb08436000000806f285d8983dfb31a660008d827f3009050c17d8c5c500e6002e3287455117350ae86874d8000058de40000060152b03d7a850c00000402b880000483ec80000685b7100f800000307210000038caf80000588cc8000060747d8cd868a7fb89bcf832608f39a00e0392d4a8a6e002afb9d4e10680f012978674c048f68 else 0x5fa0818e682375816cc825fa81e90812d0808a28d380022ca8271905a79540e804125071e00563d8a48185a4f0622dabaa702a38050b680f68000050507e88ca980bd40b7670caf000006d9d10000078cd21830f80ec228892d0690d8ad80000010f0d53afc382f250475981fc106e358e99680e980000484668823b51decd034fb062068e8df8d29903857010500401808e7e5236580cfb0ad78859e30592bb4ec80393c82bc200f5a070b58494a850548718b041e2814792bf8d06e83848680199a8bfb404fa406e3ca1648846f18e0c406f878739c0365680c0d8090f089580ac950177e068f680df401c0389ff300556805470214602fdd0e06b042a183936046d703a3106f9301181815a486ccf05483825e4bc85a0727701652033f30bbed0077a8a49a84c18000025d9f8000010663800005826ab068390702581e10000010cf80b638804482858b886bb78585e92da984b43054d308cd7059ba0614a2086600a6800003067f8de79a86f41831c881b57852fd10c5a8d2a8000048103a8ab84915ba070f90d7180000000000000070224c024e9850c98cb780e59e0964e89be480de800006888d800002862c90612502f1500035006e08abf209d468060800005216fb0156800002058db873c8000000000000000000068180a05a508575083e1500b72065c1040df85f2985cdb85c3b8adb2817dc0183f85fd483fa20adfe00db78422c0bf9308a09842f7823df827fd83a028371000006a601000004804eb889400000683a788991800001d4cef03bed8e0da830a882e2d0612905f1205cfa807c08417e8736703df101938028ca86fc5874400bc6e067580000688ac800000000008e2a50609c83f538ee648e3bc0aba003a42071c455d1d0ae1980a00000000a0108d2d641bb00000403fbf0153b859c1062bd873880000000000000000000406a5509b8000003025380000003628000050675788cb180280844da0269f0bfea830d584c2e8241389eb00cb5d010f00578800001a41ed8925a0040c0095004ccb9acc30e0ad0c9ce821ab01a700000600bee015dd8811c06998000000000102a29043d88227f03d15003200000503afa024180000205bc78a7db8859f807cc1a7ed032fc0cf3584cec8d0b000006a155000004801ce831e20c9a681fd0000068e6a8000000000310c75017f20ccaa806a000000000078017f849ac81e88000078826a8ab9401eb8019b80000001350000068429131c088e93f0db8586b9681d4183601828080735802b1a88d680000282cfbb8750000040a9da808eb820a00000581e530050d80bba850448537c0202f8e8d302ed2006d386371061e0000000000403f0d853b583e1b0bc000000506e0d04c660c2b0000040de08096370611383b4881f528a25f81cd0072a000000000000000706ea8044b283c)))) else (if i < 13 then (if i < 11 then (if i < 10 then 0xad7988990116d0546a00675808ad80146009890102e154e800000023600000182cc800000000000bca0000000000605d42813f501a83815748aeb3060f302b3e06a7884c08000000000000004851448b52800003823f5068638e160000000000000003088b00000000001804d485702056990e1a2be6c8000000000305c2f84b3a0004386161054a0000070691a0a79f870be8b9c701c8886234da40802d570e30304f07068c680c5f2e700000078b91f004b000006225778e77f09abb80e440ebd68052701c2605c5005b4582ded81bce050e90e146888af0655200ce10155b0d8fa817570b0428d92283a888e828017a50e0fd808870ad010e9aa88fae8d472098ea828b602b4a8c868000010ebcc02b4002cc685a1088a5000004062e8000060414b823e204ca4823480000589fc78497800000000000000006f680000000001834648da1800002d38ca868b10341a8305800001837c68a32b0a6748310884ba40174d0c8c800005894e983fb0896c80000306bfb831c0817d43472e0505f8684aba1028be0c8d82e031a503edab1ef4860f9803f8005bd015161de6a0a5e8000020b09306688000018cb6887220000008875e802fc86d70090b9872320480800003044cb85e698556a06bed0656e073450d1b48cf9486840000010206188d6705233031d883211035c406bc8814660096a844e08235584b040020681493010e000002873e1b210683ef7006658130585c8d051480bc3e84d7d05cac0d38e8309189b42003938967b0eb9d04213040939202704de90d8ea853d48305206171875380000000003846dc83a90000040b28000005811ce83b5a85e3b06ba1800e28593806e1f0689184a2c224b00051e05ddb84d298d01a0087006b780513f8469780de188125034e88501c8838c1dc4c008cc8636d0e170000010567982025092b78b3c305fa800af9029d186886830ec8eb5f0876c8af3500cb4842870938206db78582c0344000002830000000506c870e5a40a4a28756b060c90029582e580000012da504fc8864158da5e0d3012c184841b400f5508b8000566835df0398782c70000048276404e80000000720000000000000000281bd80000000000000000000040c40000000cce7834ca0e5d60458108c76033fc04af784e7f0c035367628d20c86c3605d068b576808b0000000000000000000000000000000000000000380a678d7f80000002f9d01f78000058d167060c08271589aa084a1b4176e05f9b8ad4105f1d817c2070f3803130d8258d18ab9d2d8bcb8000033c83800005029869aae000004862e70c28a0ce9a01a43863b283e30000000000000002ce2a000007810000eb480000000000000000000689b9b81fa000002026070441205eb00000000006034f700cc402bd800005801a8000000000088eaa92d5000001 else 0x3802e500dd38e8e90e3890511000005061ec1a4b505eaa0c8b20b35a0023982c100000506ac6882c709e38823ff83d4b8024503590820d884169a17ce025d50eeb50ed3d0e6968f2b30e1be017913945683fc4892bc8d06604ffb0320000000871d7848d38d902856f78970d871600000482b5800000065e9541b80000301505029180272d064f80000286f6703d900000381d0e88a7000c2581a4a81b168c7b35d2e8846be84d9f0e4200000000003803e90b1e800002015b88da78831d389e15958f801ba8063348e600000000000000004024880000704368860ac85bf484f0e86488000028df76880258ba044a800046cd839dc215c18568e8390f831578543884ddf8437083b6000005414278947208892c646b8ec9d8079d8f3820ca6680f4184263353521d38b02eee8a2f1837ba822d58e883858fe815e1894fd020b28c5958323b0592004a85007f28296d0d4068473c830100e469cdc5f80d858f292856090d9d516414005b78c36486d630ab9c86a8a026e3859490427b1a7f50950c0a2398659104c040070e8d2960cbff85f7a04cdd02bcbb2da384b0f843c7074ca0b5a004fda036b10ec438b9df0da3b016ab871ad06c718c129053100c838d254908c4c855228121406c520212085f238616d04dbe0275582704087a782c380e8188dc110de82872478d1280750083976049018e205821c6053a68701f01a120e13483186002b48f2aa83f5d84ab5066fb019420487d80b17067100b9ef0057d824811a9038730b81aef8508c8185b89901883e6822a3056580e4cad524704a028464282eba01e5b063090267e81c921ca7a86b2085ba312cbd86f0b04589841be8ad6b09f9685d9080f06a41920a60a8e1f60f0dd8462f05d52823c084d239e0a809b92c1547008f603d760453c8f354053ec06b08000070553006be1048e80000283dad8884b0ca88000000a4b8000068300dbac340686c02c4aa4c180000102ef0000010018c8ab78000002a76c8ec1a9e174065438df8042d7901727069dc85e5541736d6ab480e800000681d2e03c10000020ca6a066eb83240000003c88000003008bf08e5800b33a1437c642503961838368e774059d30246d8cc150558782de50231c0037880d620c20654159837280120183d3f85ced044708650f05ed0004f40e2560682dc2d8400b018bf810ba828bc48000050383e0894c32c528ebdf8d0bc015978c184a25780000080fe80bb4784bfa8c407800790f3c80000000006023d00000788c0084600840998429e820f805c97048930273986074831580704f8306986e488405e056318019d00a8c03f9b0a09c0131483bd38a5e00000583f220e23701eec0d8d50e24a00074c14e180ffd047ce3adc288e53a10cd0172b81ca38d03208cbd8649785221068cd058480b96b8993206c40964270c) else (if i < 12 then 0x8da04130000000000000006ce3a80000486bb904817019f88551e051ee8a6508e041833a30ef108670783790025ba0ca5c858a70566b037ae0d1f888c7f0354b8431d016c60b31f0178e842708d360824578564204876841dd86e04865a78d1868368082d9002d4d83bb202c0b04d0a009e581dde0b4f207466dd21e865cf857e8023a6883dc8091e8ec8f01e729202f01a218653606c268381ac0c398ee8c0dabc054d98ba0e8dbdb074ec85cb7030c403b400000608ddb85f83d8ea306efba404c83ed082619852f50304f83cfe8e5608088d0448b86dab036a380dbf85d130e10c82100001750bc0e8ee850ec6306f8f84fd685470860880000000004817410a3ce8aa98000070d0c80000000005098fb01f0800000000059e302cd504053d80000000000000038eff702af7b481401a2a10c10016280714a8266c8089682988000018e5800d05000005824444decf03da4817750054889f8a2419a8e37488bbf8239704bd2dd9df80bfa854ae8380e006b683cee8bf4d01e0e8224000004807b486a4a8545d08c5c00b7a806c008ba385b648b2b202dd30195d071dd0713380a71843ef0170884afc8df608964583de38652001cb68632708e6d0a716811548cf60861a582a66057a101f4d840780353a80d0e05781828478164d006fa833c184b7c80e390581104d020aab7870a98bf8f86c2d8d46801d878247f80cad0e8ce05c0c0a50f04dfd80acb02b7105d4a0aad6c50010d1a305f01dcc1f85bdd028c20498e88ed50408e82dbe83be204778813de0a63e8e8b885d73073c38379e03d508278a030a1b2c4b85c458672904bef059c900eaf0318900c280314e1a3450c5d3866c18ae17026599dc698e0750bdb28985b03f81847bc0d93805bc804d8000aa40554783ab501271b28d0000060218d001628ba8901640000038ab070180001c1e8006f8e4428603d86f55363db0959a0447880f2b03e95539738ca82825358693810c8000b4c869238a724056dc0064c810ee8f01c8d5c70728f83a2585af30ecfc85bad0f2cd86e640ab17032de0e83a0842e81020849bf845eb8889a8663704c6a093920896f88c1683a5f0a29385c1c14bbb01688a4ba089fdfc1f04860e5454610027b026b50711c0049f04972009ff06d4d8cc9000007006de0254606c088e540070ee869f3865b30057209e53040cb81d4a0485cd5ea28d9e605388817af8045a003570232903f0485fb20268181f3205024008540d2c000005044c4817ee045e601fc800dad825a80520088f15a5a0d92d8286138000068249c0ecc5863a485a630dfdbb022a8d8030e5ab84ed18302b8a1db809ed0392406b1681ff80000000003839d106f1982dcac1ff80000000006804e40f38c072da06c03021b800000000060268c06fd704ecc03258000018464d01b58000000000 else 0xc6009f000002013e60eab682cd80d4338225c08b7c86e8e85106ae16f801d78bbf50571c83d998613181e0580987007af05ebd86673852e102d060d2a204c37825978669f0a8de0d84082890040570f14500388811668e1218d72802a310af6083dea09f480000006abe04a700000484c100000181fde847f8000030a9500000383f938ec0a870a28d2b9038f800006013ac808d0000038382000005857df061d0000000000000000000030e15611760000053afbb039ea0aaac847e8085a00000502930000009a1eb05ec0000040af9800004837078e6f281f3d89e46020ce9d4f702ffc0016881b650c41000004068fd8cfe50364b080be833e98642b0107101d100000503e8b82b658886d09e6489652872c2840808a927047ae006970b5840c853c561808b90841e90063605cf30503b03dc38619f80efc81508dd9d1097a00009501b90036300accc0030e800280d54d920310599c0ca7d8727e8062c259138ba9884d8c05a3f825000000000007853988eb688ccedd94320465bbafee002668dfbcc5197871be8524da68648a9a0000028c8598333f8192b834c03144d8236ab078d382268b08a81171852b30125a8a36b03b8880b0800000805a480436887320676306e400965885c800000085ae90b6c18155605b86855da0da45039ad8068301e7b5ccca89a63526a8009c292d30000060a6128f1be32fb606a6385e7f8215103a1000004807620d4da0cc5a8308c82336c54e80000409504063e5012f880c4e852aa81fbd01bf8839c1b294d062ab86b1f041ab0706207469829a883733009a30154a810d9004afb4803043f201b3a8cebc8f3ae8afe80000785c580166800001873f00000100f4d8732f06d30033d88b45b12d77002188233bc641000000000040d9db0a76c835f18dd8d84a900000402ad105e1000005d524e06d43882848094988cc3046700000000002893e287178000048c8c4032e800000000010d7a40c1368c3d702218000008a73c8330a85edf8201a8a9f504cfa8f25eb2d1400e1002b2685ea603ea10311600e5586d95013370734c0aea4073ff0cb65043c984958802f0000000000000000873d000007806880ee9fd5b8000000000000000400b1800006b871b8502f0842601e420432581e67089aa01bd084193040ff8aef48668181f128586786744d71e88d0038b7ae01b1f816e0000068e5c502f478db5f005380689a8ca7402f95082180000003770000078430208c09862b3808e504d10000028a4c000006039fe8457e8633c0aa430715783b07b01c005b578163f8b4d8000028c9ed837f000001018d8000000000331ff00000305e9a06ad185215846c084bad1d51801df2052c80f342809cb800d92f1e8adf5104849808180000382200000048297800004855f9037fb8662e034958665dcd82ac20298)) else (if i < 15 then (if i < 14 then 0x3755d81c7f8daa000001005aa0c5b601bb20d4b9064f20659a0891f80f65894110029e851220d8108311e06aad86d8e8376f073eb045b9065858acad81be604ab98074c8283e05f5b32fd0833b60622204d530d4e68c0c481f7386ede00645069d589cd600a9006d28000048251b002700000084b4812d210d203061930840e0aa4c8213a83d8c8ccd8009bb0639c9a814804b8856738e0f785292ae60f05a37810ae06094044a48435a8d1d800002814fe01ab3067c08d093856f80000000003022c303e4284b98000000000104e1f82e1f8940782cbb038e80000201a6c8559a832b98045507510849d681a3e02b54049f704cb30b58912d600d96982f7e8dfa801fb384c9d8d7168ea2000003d97f4010fb04ec683d6d9d33e0693000000000000028c80ef48439d098363144706296825d89d77800002856e20bccc833400000701b8d0a4e4259df01b4b86bd10ae070aa808d5e23652b826a000c04863c703bfdcd50889f02824d380e33012e5060d00000542d28000048e27286fdf044f0000020c70306dee045048638606f7e8f174b9ff480210831bd840d3047870e458838608e3ac0022d0c0a70c34a8a9ec065a8883a28aadd10c3f8607d852180000000000000010474258e9c0469904558000000000682eb1870c9072bd84a090e31a80992c2d3604350000c644ba80000000462837d8000068604e0492e28ddb88d4e81bc483a858358e0229b0097880ad800001820f2066530194b86cb00000000b2182a97152d80130b021cb80b9c800cc8600d85e808555b2b0b800005d173f851ab063a853f540843e0e56fdda0b807318f1e48524009e9800006801968c1b1833be06afb01b0b0b97983b1d02b0881e188a623042408329504ad9be9438113a0159f8d04e0ceb383a4f9641881716814028003d818cd8118d80a538ecd083d8604de600e6a8b8400d9a00f16fa679f9dc0d8295c0aaa603b7f88c658044903c9c4dc5704846aba2f02a5d020ec0c09482ddd0082104bc000d7a41e8f8ce3c82ace5d9f7091031ce5b85a0a0467a024b00562b02d4586b8ed6b4c8557f84ce485f6d04e718610b088cf811b504da0856060397b854ce80837057c800b3884075838bf8934b8bfa304ad303197811f800002047d882c5e854f5d724005f0c01d3f0547a8191d070058460d0575d01a1a037840598400a8181cdf0654c0365da4235803d7d66530117a824660041c00489832e48453789bdf858b3870178065904dab01852800a3072b0000048456800006858080000509f5f82ab8022b18b14a05957041f704b1981541038c301679821f785a8e20f9b883f70e9de02007813770d2cc01e4e8d95c0b3be056d4051b90176d0395a01de98b0670044586c620709483c7b054c100600838d8000000000584fb0000020ca5383bdb83bc7827 else 0x15f8a8f18d9655560b06b058c344849ec8e084851e51e43606df1057c7dcd5f8ad9302e4a0089e01ce483758054fd0e28a8b04a0a70685b9002d5e0a9b65d9138c3cb0d1c1841298163200f1603d4702c9305e8986ed600ad30d56b858068a8ea835650336684efa12d7b83acd8be2e81ecc86c5e8f1ce0b07a0ec4d86d1f80c568549a04ef503faa06acf8e08980128000bf2420e1d07f08f930a5f28b77b9174086e170100a071b607555851c180ec40146e020ad8b0b582f8185e048db39cdb3b88b6b0228c0662380c8001aad05cbf04fbb04d3f080dc01bb98087c8573f589f90a0610719f0da6481dce82aec054e2d3f8b80e7a027ec00bdd8741306900823158bac386e7004d418f1ef806c803f4b83b3e0e6760a33e82bbf81adb808100000603c930245a9d1b201ec3055aa000590171809f6880d9b8cab50af7705ac1055d58a9960107f8ba24d0acd8ba1200fc386f9cd417703af784b8e86cad874b90a8c982fd509a1c021dc08bb52bf5780d3e8e2dd0667a015f98518c8992d054300aba905b8a01f290e6a081c6d088538413d04184009d102d9b04f98d2d9185c4b013914d4fd0258280347004d804bb9072588ac088b2738363da21b884a438c2790047c8e5e7016b60d54184510819a90e5bd0a946053cf0455085bb0b532a24c310e3a5075268e04f074c603c820d508837b404469058d789e4f8644d85fed0ab440b3850420b1a23e0683681707835300000412d9e0e5b1023ec025a000000560e007008000000a510000028d1af036780979b0369b9d829893d9015e980d4a0083800e184178686a92003c8000058aa608562708b3f8378885e37852e907296058ee82c860520cd19c708bc4043e680010000000dfed4d4f08646d861c2813ee458f8000040ce84812648bb4d0402d811f283f7d0729a008c304e62888a3814330aa1b01889854bd811350482c85eeb82fcd00aee81760055e682b6a42d9a02e2209ef00267000004848c405dbf0a8d608e2b8b05e861bb826940bde0061840626a0a0bc84047dd601823058abbb0afc38d91c0e30c806ba83e7486f5908aef01dfa865d80000000007024f8accea8e4720a9ff0264b049458726905d0d8342986ab78611906cf5067cb8c76a048840ac6d8e9c78d31187493826ff8d49605660812468b12f0282e8a7ae03c5f068188222815001066f654d50000000000000007071170511f029738df50013d00000283b840b0d8dd9c8000008531cd5f5000003026568162184be0000030a94b00ff20b55d0928800004c5bc906a3800003828600000300ae38061c807a6830748e9a58aa89872ed843d68952011e8f8a1fa83fed1dffe82b900d4250b99f045d6802a301421055ba0366a831b403cd198b710e9bd86283867bc81d8a8ddf1050a48a9e20b955828a08c3f38645e) else (if i < 16 then 0x18aa2b2d600874b007321850d089c288eef20ebf90d5bb0933d8122c06005036cf0348b859620d6898be848a0c48456480b54034e083fe388d3f0034a018f8029a2821f883ad834e7e8d2ffa973d8adab80a278a97b016f08716f0335e844610b1410554b0651e8540a31d3b85fcb815350efc2353390366305dd2841595886782a51821e0853fe88ac60ac0606ca4014be83386832f20df9b05ff60048686983080e40731d0304385a7304a6f030990a7418e208055000737c0352a00d58d8e5480d8d0a11780abe84dd30724884202030f106bdf831690c04b87087838a98bace845208af97803ba811d00355f0e1888dd0d8648189fd50dbf20196d86e9385b69002ed0126e04ebe02e64847750cfcf868df04666857e403142015b783f740adc10c2c300496056a301c4d84e4a0c80b8357d05aac8364010c7b8207800a3001d950344b862488de930887004cd005e2885002845c1848be0234783d3101acf00b5c0aed081d7585d31a575f8ce7a24d54047b5857d48e117848338a7298a4d505761058e183cc20368d02d8d8c989054890529b0627b81194835af046ae8396f0a71b45d4a81eda9d5168b64f03e5685347845468b4c0054b389e5e864da0403d0138f0db7b84aaa85df682f66055a78d5dc000d00e62e8217a015d780ca2067f4098298bdbd02388052d001f038749a812570192786d0086a9b021770426c066c80445082fa40e25d82c7a8713b85f44059aa805150451b01b0085ef40ac34813c28b94400783ad5fa0308631a708c3aa0226400e8b815cd2b0ccb020e8cb4286bc10449f85acb0e6438ec84812ef86b778984a3c72f815250319d052870aa578262308cdd8b4b48bcd68b9f4859010204e0373e84c5e841a008412863918da6a04c46867e80e0eeb077f3adb48ba90045ae85f50049950496508b7181d59053028e21400946802da8e3e48b3b205c7f0817a0944601019833aa307588544e00d5495d4f861c902e560e095818ac8bb3203fd642daf0339b065b984ea30270f0bc378186101f890aaf8036fd550ed0d48b010cc08d0d066d00b4888223e03505848db2b8ca030cb86a748a846844978ddfc05a23036c10f1b4828a804f740ac7402ecd1176d021b28013a8132405373016bc048a685f94071a082cd6b2aab094e00ec742a36486c3b12d9003ebf10c6507547060db0ab3484e30055e80525b85b9b035b30a7e2838a281a918e16b00eda86a188425b0144032fb8b076b8331e82fe403078095be8075a8685e842e08c9d402e9801b40872ce806ad92c3e8c240821620481d863140634f020c382f8986b9d04d650709d8387f2eb4a06e9e04a380583c810c18aa9304a238cbbe0235f8f3c70c6d780c18c177c02913011588d0804e0ae0072706915840ee0d5f38a6a78e98700e4c0c2a705e97852dbac else (if i < 17 then 0x6959014c8813cfb9ef7811e382e100000658e963823d8e577b071b83ccc86fe9037a78178300a780e05a0e826adea5049220e17e0ac17812248eb8d8637982d780000501c7186a2e85b01847a70eb44018f1549e4056eb00fd703c038e7b881c8700cd302ec3800f88e13d84ae902e808692c83e3808ecf82c65065788008283b9d0a74bb62f78410a0eec08a7c101b7005bba806550597c8214db66d4866628e8e38191604b5707264070d702ff20e018aba9e0444406505842df08b5a86d1306875012f6064720a2660e225002d28708a04b86825c68748605ee30bf35d6448869c58f2d404fe80698b840f402fc184a9c8625800002013bd82c4082663848cd8351984d1d831f3865e48f2f0000008d228000058bfbc003f6806e80000600dc1049de02e44835f98602606aa5047d6310820d1be062980df5a046b7856ab0418b0b39c82015873310888d0084003e8106802091df91f04074f6855c0009da097bb88d1e24a3e0a91e02ce880f3e8184583cde01868033700000402630000010d97200a28029c9068e60387481e380c9900000383c4bbe963014f000000000aa812d8000020e6ff84f2812d43832340a7f0000050361b0eca68a972864ec04c86b145b8695380c8a0e67e8733b8f27541761811408dd98000038534a0a99b0c2fb80ac2030300000000003042498bda48acf303ec3de010000000000681d7f0694c0ac380000082f5e8452800000000000000602ea80000222598b324280d1c86ebb01ce800003031078dbd78d22000000000030707403810808080000289f5086b5906d26851df03749052a00743585f4c814ee84db48d145801fe80be08496c019d8314528c29e84e2e0a84a8251083b268723e0561804f838a90e95bc8000020e1c9b483f04cae1a806840c7420430cf260349c8669685b5e051f6d56128cbec0c1510aaf6855c88551702325023ad01ad4856bf842cf0252aa40d30015c041cf0d1f00000604c4ec177501ef80000081a008cfef0ce928504800005054602df8a829f805e0e88efd5266b045ff0136d01b9f85724889cd84e8f09230000078239d85b33863f70206d0712b0072f072828283608b0e81ef584cf58754f12d2e051d482c8b8d41f86ae10c3b885ce384a7b84eaf819628012084fc48499f00cef02be802ea1804a306c9604f5883b0f8b743851ff86cda0389e880fb0223783315060600032e02eff8140b82a8b04b2e8295286c4e84a6203a73038028d1e246477835810001885ecb864c38207280e77072f8043fb0430d0ebae839bf8b0a00211c0703e858c00468911ffb00fcb805ef0036e82fb003b3306f3b0e81011773810b00947d08bec096f78281f8bc7000fad8ca900259f0258d0e32b0d55d8b1d989590d59b40b69d040090ca451d4ef5659683a9d8c0588a4ec8510e8238 else 0x653a2c05b78b4851b1cf887182063bab2db4069fd0b4ab0e901413b00a03903bcc842378802800003217f408f85d3a9a04fa8059170706800005880eb8e2f4a0c9d80fda0370a003380ecda074e28697286ce78a12a91540813b181a5000003064b0000060bfde8063c040be01abb45d410614602cac8b9ce04a4b005ff0d3320dc8080c7b896ae89f60000070f2570144c8e2a800005859418e7350f3068294d83b2a040038210e0bc50037d00000584ac9061518149d8e228805d707045072d504eb205daf3485b8151b86aee86b3b86ddc0e50f8e89e871cf0254e8b9ad05de51d91001fa800000d0b8d02a988b0ba84d5a82220c1d070574d003ae0026e02bf801c3d9cdb1832800e26c0dc3a05e2586516057478250d8c06703f6800007016fa0043f8952b864c9862d60506c025768714280f1c88b8f8d02c8a8ba80a1c0e0070454e80ba800004059a585c0402a202c9e5013628193384711804cbb9d38073b10593082adc82c9f0a365859ff029d98352305564de86106e578173602f730b125069ac8cff902308019e7b66be85d860963f82c2381de63afd6039cb84e0a8106d31cd50c3528b5ed836ec0463a052760105b04f63014e186b49083beb66cb8c19105716011ec04e6958a62aad438e28380a988a93181699019868f2fbc13590685403378000048022404981824c6058998ea37831aa80f320956a06c15048200b56484458000070eca98aa370e0d00d320816eb86a078587b04e538cb0e814580000000007010d0000038d645852c186fbe824f500c350025800000000010476f82d3b85b2c884570bcb4003c70143e02425812b0000070488c03b5212d390afb284b5d00ba41dc46872ac84dc70)))))
def sid12 (i : Nat) : Nat := 0x0
def rootLink12 (i : Nat) : Nat := (if i < 1 then 0x53800000000000073a8ec17fa2c4e0b500000c69f612d519478cd0000000006144e01e3007b4109b0174010dd66ac388200a086db81bf6148907d285e34222c944910a4066702fc54d3d0085866ec26c20b9c080b831886eec31b6074a82f5433e61bb305d7080b86b4a02a502bf82388485c19030c4d0e1fc0aa6243f04be0171809a40cac02f9049840764110b0e29829a474f6140e040e070b8031c023700750389c2c7604500c32837045e0203af083e0bc90230e146ca48783b542c142e870cd48afb427b212520aef848ec2ce205e204458ee0403f60d090a5782abc16fe147f0c2502b4887e2361a102c0e740001c3065006404dec0ee000000007836e01a9a19c8021208e845dba13800bb3828a40f82191200e886ba838c8017c01480003cad2000010dd08a40448b6200222e880d0de2a204eb651c007b8211400240d86818a11e0e0e74617c016e837a610f0048403e40000c204d06cf024c00002005a068803fd01e72124a09800000c1d00114601400000000000000000401b80000a143311d80000000000003188d9295820800009064781cc0001e076202c100872696074b90d3bb45e2a6b42b9b0c100001a14a80b821a5e8214420b6364e0a48000000b5a129504aa03f28694a092b09af0653028502096073580b30219a0cd525170cbd00cec32e21478000100eb2af3a04ce82c8000000000000000030232c00b407b8014e0162413f000071a34c631e2cc514b3061c0000a03c101200002c2a5f4f3c0c6a86de4008602f51b0000cf00a141aa70b5801e40001e1735081886f00000c03161c6a8d7d02cd60d3702780002c0e5a1a1c0a8e001b91ed2086e06b8000382b0216241234086541bde346008f40226c32b0007519eb8a8d853da14ca020d45aa81b101700011182d9c76f004ba0bae0196c64e4132208710bea56ef61b990784071e052f6a90a001d0c284642a06f20d47023c0000810b100da0a95418000000000103ab006a6156006ab38240000a026000028028c2fe0000000030125c1cb017a009c803d210c1a2b1d16a309d980c6e1b260d6a0e6000002046102880000c013e31aa1adb06764489017c2080181b10492e15a3065a82080001028ce05de86bf4362c06bc06b581c48254e368a1dd82380488510b40800719405060062212180832e0884050154a75a0eb1400006e3702deb2060c1851a000b90e34f8706100900c55800002029b7ce4e1f00049800c141000a2cf89109810098003842c30a071206209002868060084a00411504527c0170444901080008500000090808d3b0448aa1142c0050204003080c08004341001400005025c00c000840400181060408000000c804040001c101008010002000430383000048e386800b0008500044c18100200034c0980026683800201580041ce800200081 else 0x3c4b4000020af00a3642abc06960835028f8240e18b0000402348156f64650b7f0dc306a4e0a5905f20d600001a150000000003c160205620670000281b4000d7131e38bd44abe185212fe042bc1e38047700ac80e2066e8168b0718043582660000c052605b8000000000000201f98acc6025f00d586ce0268606a102540349c4af61b5a036c8d0a44efc15f90c65b454473e82fe20b600dac037f41a640a9c067a4557c1c0b170195ab4135e04c00da005c680a5a21821db6030e023b42f320aba8c97450e62cf20aa411d2c4dd0000a0a2189f5d935823ff013d069101fc4001a569f8326c529409da14e8057106d400b3c1118022b038360aee0098000182c80000000040905828ae2cef195f0191e0e9409b0000583d78310224b7442b8d66c2fa705d11c1d8070c769c17b917ef8a710e5fa4a1900ca82b08278612fc0b6d81500001a11b0000682d5c307ec091251b038742b20000b148b045c0000a196000000000413c03a600006820180b3236e00000000186b94279c08d605974056a2fba17c903be410f813b40a6a0174c153614ff0d1805cac93cc09cf03eb83bac2756116007ed8a62838700afb04618caa822661125655b04a080cd61153062b83db508dc1a05007c86fa6146c27060307848984c442593075f829f405b618e404f8869782efc295c15e000fd04602198d16c481860258414170adc80808263e38f0149c01024585c315a11738211430221a931b9d847e05062037b11e1080c000040bcf17110b4c000120680000087100001e0c20000706b2812d6eabb0b0a86e1c14102ef0000580200000c14bf0cbd833fc02c0000b095c03b201f64350000020330000100c700c9f02630300a1741008983c9015160304060983904568a22f903850acd855a6169e0c508111024e62d2801968c5a824380a1e0d5cdd1380726179301f681238106c012808e50805825d618fb0d12825141f0428a203a70cd644f5807bf12048375c5b440360045c838000000000903d201fd4324e102405a104f8c55fa091006228)
def sid13 (i : Nat) : Nat := 0x0
def rootLink13 (i : Nat) : Nat := 0x285a830235a17508c00000080a886c063e22a03000201e0000000003c2fc03000681c00000000078a4059e04b0120af023a21e0e006b828639800a8c381d60c000783604f43261a104f44cc0900050f4001a0ae17c89681600000960cf811a10000186403b42af0280edc0163780420213904520021301910
def rootData8 (i : Nat) : Nat := 0xbee07a02b451524c42bf6079c2b451524c42
def rootData9 (i : Nat) : Nat := (if i < 1 then 0xd412afb2bae42a64a0957e95d621532504a9fcaee10a9928256fe174dc2215412aff23a042a64a0957ba5d80a952504abed2eb854a928255fe87402a549412b5d6994b2ac4a095fb858261d32504a937eeb598d432e4c9bf75acc6a195265d7bad66350aa131ef9d6b31b8484283ff6e996d432e4d17f75ebb659a5264bfbaf6634ac9931df9d7b31b54842a3deea576d33264d1ef752bb69593266f6ba966326b893f4e56764d625c49fe70b12e2bb24217db158d975893127ed8ac6caac49893fe8563551624c499fcce9d98c128214fae75acc461410a7b73af662a4a0853dd9d7b31524c42ab7ceb576c9302147be758cba22110a9f71b4da364a8856f38da6d1525442cbf865a30c92a215fe2349b7551310bfb22e2c3a2898857f91d72e1144c42bfc8ea9708a26215fe4b7587451310aff23b0bb2289885fd91785d9144c42bfc8ec16a8a26215fe4748b5451310bfb22f0baa289885fe9168595144c42bfc8ebaca8a26217fa459d65451310bfd21ac8c2a89885fb9181619544c42bde4ec056a926215f7275c2b549310b7f238a8a16498855fc8db4a1524c42dde8c6230b126217ef060918589310bf783048c2a49885fb9181551824c42fdc8c3a28c126216fe470554209310b7f238a8a1049885bf91c8451724c42dfc8e4228b126217fe04a114589310b7f238e8a2c49885fe9167451624c42ff48b2a28b1262177d256d27549310b7f25988a2a49885ff802b451524c42ffc094228a926216fe471d14549310bfb218e8a2a49885ff1157451524c42ffc093a28a926216fe471914549310bbf8370932269085f7c198499134842ff60b12ec89a4217fb05896544d210bbf2370aa2269085ff8126551134842ef8d5daa8a9a42177c66e15454d210bbe336eaa2a69085ff1117551534842ef8cdb2a8a9a4217fc24995454d210ac97ba9554ef333b45bdd4aa9b7205da35eea554db042ed1cf752aa6d421768f73a95536010bb63b5d4aaa88845db2daea5553bc22ed9ad752aa99a1176ce6ba9554ab08bb67a5d4aaa22845d837eedd98d494c7e7e4705c06cc852e5f63a0652c4a095ae94ca58d62504abdc2ec05499282553e6369b46cd510afb23ae5c2289885db92bba21144c42bfc06936e8a26217764aee77451310bf325113ba289885de92bb999144c42fd49444cc8a26217f249de66451310b7723908a1649885bd91c7450b24c42df48e32285926216fc4715142c9310b7d238c8a0a49885df82bb452224c42fdc1442291126217f609dd14889310bfd04cc8a44498857ec1d6309134842cf8ce2386da842167c672d5454c210b9e3374aa2a61085db19b8551530842ee8cdbaa8a9842177866d95454c210a6fa1b8cc2a70885bf12cc551538442fd89442a8a9c2217f449dd5454e110bfc24ccaa2a70885ff015454e228442 else 0x26c05e105d00420060004008200420003b342000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000097de00001a808a000000001a956ad528000000002a54a952a5428000000008b7eea996cc2c6a7e3a5d98261d620a0ffdba65b2ed323f1cd78659736091f8e6b9b04c3a6487e635cd8261d322f0dfd76e3554cb9f64fdd6aa9795ccfc37f5db8d5532a7d17f75ebb6a552368f7ba95dd54c99f56bdd4aeca664cfc37f5db8d553267d1bf75aaa6e5733e8dfbad55372b91f45fdd7aeda9548fa2feebd76d4aa4549bf75acc6a1933a3df3ad66370b88547bdd4aeda864ceaadeea576c3b267556f752bb5d9933a8f7ba95db50c99b47bdd4aeda764cd9bdaea598c9b02668fd618ca6498133e6ca50c9aa4c099fb6125605825442fa3ab3acac9ae267f1c595715d9510b3f2b84e0b664297b795d170c85648b9fd8e8d98b12821556f75ebb661522eab7baf5db2ca9173db5d7b3152504a8edeeb9972ac445c9bf75acc6a1972a4dfbad66350ca952ebdd6b31a8550aa3f6e9576cc34e549fb74acc69d962a0ffdba65b50cb9563edd8289a9548ab2f6eb944d4aa457cf14a1974c9812be78a50caa64c095fb852855132604abecaeb9509928255f693497a61)
def rootData10 (i : Nat) : Nat := (if i < 10 then (if i < 5 then (if i < 2 then (if i < 1 then 0x9a88551310bf669dd544c42fe9a66551310bfe4451b24c42bbd9c82c9310af7671cb24c42bed9c62c9310afd6714b24c42ff91142c9310b5f6aed924c42f7d118649310bcf6a21924c42f5da77649310bdb6999924c42d7d9b5649310a7f632d824c42fbd181609310bfe4451824c42bfd1c1209310bfe4450824c42ff91145c9310bfe4451624c42df595b549310bfe4451524c429fd9cb149310aff4704524c42bed9c6149310bfe4450524c42f7c929889310bfe4452224c42dfcabb889310bff0306224c42efcaaa889310bff0462224c42f7c998889310bef2a22224c42fdca77889310bfb299a224c42dfc9b5889310bfe2452224c42ff8954889310bfe4451134842bfd2cc44d210b7f4aed134842ffc0c244d210bff0889134842efd2aa44d210bdf44a5134842dfd1b844d210bdf4661134842fbd28844d210bf749dd134842ffc12644d210bfb4999134842ff915444d210bfc65515348428ffacc6e8210a6feb31b80842cbfaaa6e0210b4fe725b80842d3f98b660210b1fe6e9980842cbf9baa20210b37eaa9b70842d5f9986dc210b67ea21b70842cefaaa6d8210b5be661b60842dafa886d8210a7deb31b50842cf7aaa6d4210b5de661b50842db7a886d4210b7ce711b50842df59c36d4210b7ce56d540842cfb9ba550210b6ee6e1540842ddb9b7550210b7ae6d95408429fdacc6cc210b3f6aa9b30842d7d9986cc210b6f6a21b30842df99546cc210a7f672d530842df595b54c210b3f66e9530842dbd9b854c210b7766dd530842ded9b654c210bfc6551530842fbb288452110bf6c9dd148442efd2aa44e110bdf4661138442fbd28844e110bf749dd138442ff915444e110a7f632d538442bfd1c154e110bfc6551538442ff911454e110bdf444d928442ffa11488a110bff044e228442f3f189a22110bafcaaa888442edf2aa9de110bd7c662778442f9f2889de110bbbcaaa668442f6f19899a110bebca22668442fcf27799a110afbc718b58442bfd1c32d6110abfc728858442bdf1c7216110afbc718858442bfd1c3216110aff8708858442ef72aa956110bf9c99a558442ff3255552110afec32d548442fbb288552110bf6c9dd548442feb266552110aff4b31538442ff525554e110aff432d538442efd2aa54e110bfd4561538442f7d19854e110bef4a21538442fdd27754e110bfb4999538442ff915454e110bcfca21928442f5f27764a110bdbc999928442f7725564a110bdf454d928442ff515354a110afbc718528442bfd1c314a110bdf84a6228442efe2aa88a110bdf8662228442fbe28888a110bf789de228442fee26688a110bfd8956228442ffa15488a110bff054e228442a6bdc4aaa66769ed712aa845ddf92bb451310bee4a21144c42fd9277451310bfa4999144c42ff8114889310bfc4551538442 else 0x5558d412aeed720a2504abdb5c7289412afad718a2504abf35c5289412afec700a2504abf95c3209412abed32962504afe9563589412afad71852504abf95c3149412afe5b3132504aff842a4c9412bbe5aa932504aff85284c9412bee5a2132504afd96774c9412afe571932504afe96664c9412bfc595532504aff8523889412bbe9aaa22504afba688889412bf699de22504afea666889412bfc995622504aff8563889412b8fd6a688844ae5f5a99de112b9dd6a655844ae7e5a988a112a3bf71abb6a09c6fdb92d9a8261ff32da9a209a3fccb6a688261ff32eaa65c987fccb6a197261ff32da961c9e1fda9a2277263bf32da89989e2fda9a22662793f6a67799898dfdc7aeda52717f6e4b769498dfccb9dda52717f6a5b72149c6fda96d885271f76a5b32149c7eda96c885271fd6a5b12149c7f9a96c085261ff32da99549a77ccb6a655278df6a6889549e57da99de552799f6a666954997bdc4aed93278fb6a6888889e6eda999a22279db6a6558889fce5675897126fb9718b24c49bfe1c02c93127df148d924c49fec56358931278fd6a6888449e5f5a99de11279dd6a6558449e7e5a988a1127b3eaaa779982f4fa77999920a7f670ebb608297f8cb662220bdba4a6668882bde9c72e2220adfa32d988882f3e989a22220bafaaaa888882edeaaa9de220bd7a662778882eeeaaa99a220bdba662668882faea8899a220bf3a9de668882bfc9c32d6220aff270cb188829ef9c6aed810a7be32e6660429dfacc6dc810b37eaa9b72042cfdaaa6cc810b7769ddb32042d5f9b7648810b5f66cd922042dde9b7888810b7f26ce222042afb8ca6d1510b7e66d1b3544297f8cb649510a7f6b31b31442cfdaaa6cc510b5f66cd921442dfc9b3888510be6ea22775042faba88999410bf2e9de665042beb9c6149410afe670c525042fbaa88889410bf6a9de225042feaa66889410a7f6716bb4c42cfdabbaa9310af7671cb84c42bfd2cc461310bef422d184c42dfd2bb461310bbf4aa9184c42fed0c6461310b5f6aed984c42f7d181661310bef4606884c42f3d989a21310b6f6aee884c42fbd0c1a21310baf6aaa884c42bfc8c26dd310b776aee774c42eddaaa9dd310bf74462774c42f5d9989dd310be76a22774c42fbd181619310b7b6aee664c42eedaaa999310bfb4462664c42f6d998999310beb6a22664c42fcda77999310a7f6b31b54c42cfdaaa6d5310b7b6999b54c42df9abb451310bfe4461144c42fb9a88451310bfe445d144c42fd9a77451310bfe4455144c42ff92bb451310bfe46e1144c42ff90b8451310bfe4a21144c42ff91b7451310bfe461d144c42ff91b6451310bfe4619144c42ff9176451310bfe46d5144c42ff90b5451310bfe45d5144c42ff9165451310b7e656d544c42df9abb551310bfe4461544c42fb) else (if i < 3 then 0x999922edeb70885648bb5bdc7215922edaf71885648bb79dc3215922eded70485648bb7b9c0215922f9cf32a55648bf33e88955922fd4f9de55648bf63e66955922e7ed706bb588b9dbdc7aed522e76f32e77548b9ebecc6d8522f3afaa9b6148bd6bd986d8522f6afa21b6148bde9db68cc522e5ef32d98888bf3ad29a22222fdab4a666888bf72d29956222ef6b71cb8888bbfa5c12e2222edeb32d98888bf3ad89a22222faebaaa88888bedaeaa9de222fd6b66277888bf9ae889de222fd6b9dd96888bf6ad9899a222feaba2266888bfcae7799a222faeba21a5888bedae77696222fbab999a5888bbdadc7216222efab71885888bbf8dc3216222efe970485888bbfa9c0216222fbcb32a55888bef2eaa956222fdcb66255888bfb2e88956222ff4b9de55888bf72d96956222ff8b99a55888bfb8e888ce222ff639de33888bfe8e668ce222ffc395633888b9ebdc6aed812fced62688844bf5b5989de112fe6da2277844bebb688696112fb6d9dda5844bbdb5c7216112efad71885844bbf95c3216112efe970885844bbfb1c0216112fbcd56a55844bf73598956112fecda2255844bfd3677956112fee5a2233844bfd96778ce112ffc595633844bf3b68864a112fd6d9dd92844bf7365564a112efad71852844bf7a52988a112fde966222844bfba68888a112ff699de22844befa5a588a112ffc995622844bff863388a112e3bf71abb6a0ac6fdb92d9a82b17f6a5b72a0a87fdc52e9982a1ff32da9a20aa3fccb6a6882b1fb6a4b269ca8fedc2aeda72a1ff720ba65ca87fdc52e9972a1ff32eaa65ca87fccb6a1972b0ff2ea8865ca87fccb6a5872a97f329989dcae1fda9a22772a3bf32da8998ae2fda9a22662b93f6a677998ac5fda96dc852b1bf6a5b6214ac7dda96cc852b1fb6a5b2214ac7f5a96c4852b1fe6a5b0214a8dfdc72ea552a1ff32da9954aad7dc72ea552a9df32da9954aa77cca662552b8df6a688954aa77cca65e552b95f6a677954ae67da999a552b0ff6a5b8288ac5fda96dca22b1bf6a5b6288ac77da96d4a22b1fe6a5b0288a87fdc82e9922a1ff714ba648ac3fcbaa21922b17f2ea77648ac77cba955922a37f71cba608a8ff9c02e9622b3b72e963588ac6fda96d8522aef37202a4c8a87fccb6a6222a9fb32da9888ae3eda9a22222a3fb32da7888ae5eda99de222b9bb6a666888ae76da9956222a9fd32992604afbc5284c9812af6d71ca8504aebb6aaa21412afe9309a7504aedb6aa9dd412be6da2277504aeeb6aa999412beada2266504afcb677999412abed72885504abdb5c7215412afad71885504abf95c3215412afe970885504abfb1c0215412bbcdaaa55504afb3688955412bf4d9de55504afe3666955412afe5b3163504aef96aa58d412bfa55a163504afb968858d412bf659dd63504aff16 else (if i < 4 then 0x62243d9b99a558890e7ccba8ce2243cf3a22338890f5ce778ce2243db399a338890f74e558ce2243c7da22778450b5f5c72161142dbd718858450b7d5c32161142df9708858450b7f1c02161143cdda22558450f576779561143cf5a22338450f5d6778ce1143dd5956338450b6f5c614a1143cf9a22228450f5e67788a1143dd9956228450f7c63388a11429bf71aaa6a4fa6fdc6aa9983eabf71aaaa20f87fdcaaed973e1ff32eaa65cfa6fdc6aa9973eb3f71aaa9dcfe1fda9a22773e9bfb31a9298fa6fdca65ca63f93f6a677298fc6fdc92ea663f1bf2ada9998fc6fcba65e663f33f2ea77998fe4fda99de663f1bf6e4a6294fcebca66d0a53e9bf71aaa654fc6fdab299953e9bf32a66654f87fccb6a6553eb9f71aaa954fa77ccb6a6553f8df6a688954fe57da99de553f99f6a4a6954fae7cca99a553f99f6a666954f97bdc4aed933e9bf71aaa64cfc6fdab299933e9bf32a6664cf8ff9c02e9633ebb771aaa8ccfe6dda929a333ebb732a668ccfc6fdb9298a23e5fd706bb648fa6fdc6aa9923f1bf6aca6648fa6fcca999923e3bf329b6148fc6fda96d8523e1ff32da9888faeedc6aaa223e9fb32da9888fe3eda9a22223f97b6a677888fe6eda929a223ebbb32a66888fe6eda999a223f9db6a655888fa6fdc6aa9913ebbd71aaa844fe3f5a9a22113f97d6a677844fe775a9956113e5fd32d92844fe7e5a988a113e3bf71abb6a0e87fccb6a6883a8ff32da9a20e8efccb6a2663b8bf6a688998e97bdc4aed933a3fe700ba4c8ee3f5a9a22113a5ef712bb64cde5eda99de22379db6a655888d97f9c0aeda9329bf32997998ce4fda99de66325ef712bb64ccc6fda96d8a2333af6d9a4288c87fdc82e992321ff70cba648cc5fcba9dd92331bf2ea66648cc7dcba8cd92321ff32da9888ca7eccb6a622329fb32998888ce3eda9a22223397b6a677888ce6eda999a2233aed2a1a4604ca7f4ca6498133ed94a152604cfc756759571338fd6a688844ce5f5a99de11339dd6a655844ce7e5a988a1132eaf718b2a20bf1bd89a22772fa6faaa889dcbf4bd989de662fe2fa2277998becbe77999a52f36faa9b7214bcebeaa6d8852e7e7b31b3214bcf9eaa6cc852f7e5705b3214bdf99c06cc852e7ebb31b2214bcfaeaa6c8852f5eb725b2214b9fb6cc6c4852f3edaa9b1214bcfbaaa6c0852f9cf2e998954bf33d89a22552facf2ea88954beb3eaaa22552fb4faaa77954bf53d989de552fe4fa2277954bf53e7765a552fd8f66266954bfa3e8899a552ff0f9de66954bf99e889de332fea7a22668ccbfc9e7799a332ef6771c858ccbbe9dc6216332efe3708858ccbbf95c1216332efe6700858ccbef1cca956332fec7a22558ccbfd1e77956332ff8799a558ccb97bccba21922f4ef32e88648bf1be889dd922fcafa2266648bf4be77 else 0x35fcd7a22558cd7f55e77956335fd9799a558cd7e3eccaa22225fcbba22668897b5edc7216225edbb718858897b7cdc3216225edf9704858897b7e9c0216225f9db32a558897f36e88956225fd9b99a558897f3ce888ce225fdb399a338897f74e558ce225e57fb31b72057c5feaa6dc815f55f6de552057d5ddb78cc815f57b6de22205787fdc82ea115e1ff714ba845787fdc32ea115f0ff2ea888457c5fcba9de115f1df2ea558457c7dcba8ce115e9fdb30ba8457a7f5c82ea115e9fd714ba8457a7f5c32ea115e9fd722aa8457a7f5c5aaa115e9fd32a888457e3f4caa22115f8fd2ea888457e3f6aaa22115f97d2ea778457e5f6aa9de115fc7da22778457e6f6aa99a115fcbda22668457f4f67799a115edbd718b58457b7e5c22d6115ed7d71c858457b6f5c6216115edf570c858457b7e5c2216115edfc700858457a7f4ca956115f9dd32a558457e774ba956115f9ddaaa558457f37688956115fd5d9de558457f67666956115f9f52ea338457f3d6888ce115fd759de338457f6d6668ce115fdd5956338457e7e4ba88a115fcf9a22228457f6e66688a115fdd9956228457f7c63388a115e5f770ebb6a56e4fda99de665a5f732da98cd6e3eda9a22225b9bb6a6668896c5fda96dca15a1ff32da98456a7f4cb6a6115b8fd6a6888456a7f4ca65e115b97d6a6778456e6f5a999a115b9dd6a6558456e7e5a988a115a1ff32da9a215a3fccb6a688578bf6a688999587fccb6a611569fd32da98455e3f5a9a2211579bd6a666845587fccb6a655529df32da99554e57da99de55525bf32d9858d4f8ed785d982539db6a655889487fccbaa997461ff32d976991f9cd785cd82468ff714baa210a3fdc32ea88428ff708baa210b2fdc62ca884387f32a889dd0e1feaaa227743c3fa22779990c5feaa6dc85431bfaa9b6215097decc6cc85431f7729b32150c7deaa6cc85425fbb31b22150c7edca6c885431fbaa9b2215097f6cc6c485431fdaa9b12150c7faaa6c085429df720ba9550a77dc32ea55429df708ba9550e37ccaa2255438df2ea889550e37eaaa22554395faaa779550f17e889de5543c9fa22669550f47e7799a55438f732a888cd0f1de889de3343cb7a22668cd0f4de7799a3342d7771c858cd0b6ddc62163342df3708858cd0b7d5c12163342df6700858cd0e75cca9563343cd7a22558cd0f55e779563343d9799a558cd096fecc6d852431bfaa9b61490d2fe886d852435b76da331490a7edc82ea22429fb714ba8890a7edc32ea2242d7b71cb88890e3eccaa2222438fb2ea888890e3eeaaa22224397baaa778890f1ee889de2243cbba22668890f4ee7799a2242d7b71c858890b6edc62162242df370c858890b7e5c12162242dfa700858890e76cca95622439db2ea558890e76eaa9562243cdba22558890f56e7795))) else (if i < 7 then (if i < 6 then 0xa7fe72d850842df795b614210b7de721b50842dfb9b8550210b7f6615b30842ff595854e110bfd654d5284428ffccb695822a9df720ba9569a77dc32ea55a69df708ba9569e37cbaa2255a795faaa779569f17e889de55a7c77a22778ce9e75cca95633a7cd7a22558ce9f55e7795633a69fb720ba88a9a7edc52ea22a69fb70cba88a9e3ecbaa2222a797baaa7788a9f1ee889de22a79db32a5588a9e76cba95622a79dbaaa5588a9f36e8895622a7d5b9de5588a9e7ccba8ce22a7cf3a223388a9f5ce778ce22a7dd39563388a9f5767795611a7d759de338469f756558ce11a7d799de228469f7665588a11a7df18ce228469a7bdc4aa9767793faaa77999da7bdc4aa8817657fb31b7205dc5feaa6dc81769ef712aa145da7bdc4aa821771bfaa9b6085d977ecc6d421771df729b5085dc77eaa6d421771feaa9b0085da7bdc4aaa11769fd720ba845da7f5c52ea11769fd708ba845de3f4baa2211778fdaaa88845de5f4ba9de117797daaa77845df1f6889de11779bdaaa66845df2f68899a1177d3d9de66845db6f5c62d61176d7d71c85845db6f5c62161176df570c85845db7e5c22161176dfc70085845de774ba95611779ddaaa55845df676669561176dbd71852845de7e4ba88a11779f9aaa22845df6e66688a1177dd995622845d87fdc82e9976a1ff714ba65da87fdc22e9976b0ff2ea8865daa77cca65e556bd1f9dd96955a87fccb6a6226a9fb32da9889aa7ecca65e226b97b6a677889ab6eccb65a226bd3b9dd96889ae76da9956226bd9b65a55889a87fdc52ea885e1ff70cbaa21787fdc12ea885e8ffb30baa217a3fdc52ea885e8ff70cbaa217a3fdc12ea885e8ff716aaa217a3fdc1aaa885e97f722aa9dd7a5fdc5aaa775e97f706aa9dd7a5fccaa22775f87f32a889dd7e1feaaa22775e9bf722aa9997a6fdc5aaa665e9bf706aa9997e2feaaa22665f93faaa779997f0fe889de665f17faa9b72157c6feaa6d8855e5f7b31b32157c7ddca6cc855f1f7aa9b32157d7d9c06cc855e5fbb31b22157c7eeaa6c8855e5fdb31b12157c7f5ca6c4855f1fdaa9b12157d7b5c46c4855f1feaa9b0215787fdc82ea555e1ff70cba955787fdc12ea555f0ff2ea889557c6fcba99a555e9dfb30ba9557a77dc82ea555e9df70cba9557a77dc12ea555e9df722aa9557a77dc1aaa555e9df32a889557e37ccaa22555f8df2ea889557e37eaaa22555f95faaa779557f17e889de555f99f2ea669557e67eaa99a555fc9fa22669557f47e7799a555ed5f71cb1955787fdc82e9635e1ff714ba58d7c3fcbaa21635f17f2ea7758d7c77cba955635e9f732a888cd7e3dccaa22335fc77a22778cd7f2de8899a335fd379de668cd7b5ddc7216335edb7718858cd7b7cdc2216335edf5704858cd7b7d9c0216335e9f732a558cd7e75cca9563 else 0xeeb31825042fbb981609410beee61d825042bfb9c1209410afee714825042fdb9715c9410afee721725042bfbacc589410afee721625042ffa928589410afee71d625042feb967589410bfae595625042bfbacc549410bfce545525042ffa928549410afee71d525042fdb8c7549410bfce55d525042ffa927549410afee719525042bfb9c8149410aff671cb84c42bfd9c52e1310bff4315184c42f7d981661310aff6b31874c42ffd18161d310bf765c5874c42f7d98961d310aff6721764c42fdd9785d9310bff4461764c42f7d9985d9310b7f65d9b54c42bfd9c82d5310bff4460b54c42bfd9c22d5310bf765e1754c42ffd1185d5310bfb65a1654c42ffd118595310aff671d654c42fed967595310bfe6a21144c42ff9987451310bfe656d544c42ff99b8551310bfe6461544c42ff9a88551310bfe66dd544c42ff9987551310bfe66d9544c42ff9986551310bfe65d9544c42ff99546c9310aff6718b24c42bfd9c52c9310bdf661d924c42f7d986649310bdf65d9924c42fbd987609310bfe6451824c42ff9954609310aff6714824c42ff9954209310aff6721724c42ffd1185c9310bdf6661724c42dfd9b55c9310bfe6551724c42bfdacc589310aff6721624c42ffc928589310bff4461624c42f7d998589310aff671d624c42fed967589310bfb6595624c42dfd9b5589310bfe6551624c42bfdacc549310bff20ad524c42ffc928549310bff4461524c42f7d998549310aff671d524c42fdd8c7549310bfd655d524c42ffc927549310aff6719524c42ff9954549310bfe6451524c42ff9954889310a7fe722bb48429ff9c7aed210a7fe71abb48429ff9c5aed210a7feb31b84842def8c66e1210b5feaed9848429ffacc6dd210a7fe72d874842d7f9986dd210bf7c5c5874842f7f19845d210bf7c5c57648429ffacc6d9210a7fe72d864842d7f9986d9210a7fe72d764842dfe9b8499210bdfa661264842fee9625d9210bff845d264842fee962595210a7feb31b54842d7f9986d5210a7fe72d754842ddf8c76d5210b7fc45db548429ff9cb595210a7fe72d8548429ff8cb615210b7eeaed144842dfb9b8451210bfec45d144842dfb9b7451210b7ee6d5144842dfb95b551210b7eeaed544842dfb9b8551210b7ee6dd544842ffb117551210b7ee6d9544842ffa926551210bdf6661134842ff995444d210bff461d134842ffd12644d210bff4619134842ffd17644d210bff4315134842ffd0b544d210bff4495134842ffd17544d210bff4595134842dfdabb54d210bfd6549534842f7d92954d210bfd6561534842dfd9b854d210bdf6661534842dfd9b754d210bff445d534842dfd9b654d210bff2499534842ff995454d210bfe6451534842cff9ba614210b6fe62d850842dbf9c56e0210b77e6dd850842def9b6614210) else (if i < 8 then 0x551635889c7fdba65581273ef6e95460499ff9cb461210bd7d465785c49e5fda95e17127d7d6a5785c49b7f6cc6617127d7d61d985c49f5f5985d971279fd661a55c49e7f5966957126dfdb31955c49b7f5c96157127ded661545c49ff355454d7126dfdb31935c49b7f5c960d7127d7d5e1935c49f5f57664d7126dfd725535c49e7f5a564d7127f795e1625c49f7e5985897127fb9595625c49f7e5955897127fe9551625c49fee5635897127df964d625c49c7fdba64d51267fe72d154842e7bd8a66141279efaa9985049fdb57161d4127ded661175049e7bd9869d41279ef661a55049d7f5986dd31279fd6a1974c49efd4ca4d93127fb558d864c49efd5a84d93127df5661364c49f7d5974d93127fb558d624c49d7f5b765931279fd6a1954c49f7d5366553127bed6a1544c49ff95365513127ff148d824c49f7d5984c93126ff570d624c49ffc5235893127df5659324c49f7d5954c93127fe5551324c49efe5a85893127df9661624c49fee56758931277f96dd624c49f7e5975893127fb9595624c49f7e5955893127fe9551624c499ffacc6c4820a7fe72c825442bff1c1209510a7fe722bb58829ff9c7aed620a7fe716bb58829ff9c1aed620a7feb31b85882fbe98261d620b5feaed9858829ffacc6dd620a7fe72d875882d7f9986dd620bf3e5d9875882fee92859d620bdbe6616758829ff9c7aed810a7fe71abb6042def9c6aed810a7fe716bb60429ff9c2aed810b7beaecb66042def9b72d9810b7be2d9b56042def8b66c9810b7be2d8b26042fbe928589810bebe2d9826042d7fabb649810bdbe2d9926042bbf9c8589810a7fe32d526042fbe928549810b77e5ed722042ddf9c26dc810b77e6dd522042df795b548810b7f66cd722042dfd9b3548810a7fe72d7220429ff9cb548810b7fa4ad5220429ffacc6e1710b7be319b85c42dbf98b609710be7e61d825c42f5f987661710af7e71d865c42ddf9b85d9710bd7e661765c42fcf967595710bf3e59d625c42bdf9c7609710bd7e661725c42bdf9c7589710b5fe6e1925c42f5f978649710bd7e5d9925c429ffacc6e1610a7feb31b758429ff9cb61d610b77e5ed875842d7f9986dd610bfba499825842f6f998589610b7be6dd625842d7f9b8649610b5fe6dd9258429ff9cb5d9510b7be5ad625442fdf1715c9510bf7c5c5765442ff7117559510bf9e595625442dfb9b46c9510bfdc461525442fd78c7549510b7de6dd525442ff7117549510afde715625442ff39b4549510bdfc461925442fbf181609510a7feb31b214429ff9cb608510b7fa4ad821442d7f9b8648510afeeb31185042ffb11845d410afeeb31875042bfb9c161d410bf6e5c5875042bfb9c85d9410bf6e5e1765042ffb118455410bf6e5e1755042feb968595410afee71d655042feb967595410af else (if i < 9 then 0xa884c499ff8cba21210a9ffb319869c9c7febb661a7269ffb31a865c9c7fccb6a197279bf319a865c9c7fcba62587269ff329876549afbcca61d54263ff70cba61c99ff8cb61d210b1ffaeda961c9a7fecc661a6271ff6e9976189c7fda96e1762797f6a5785d898ffdc3aeda5271ffaed966949e5fcb7659a5271ff6e5a82949c7fda96cca5273ef6a1b42949c7febbaa995269ff722aa6549a7fdc6aa995269ff70eaa6549a7fecc6a195271ff32da86549c7febb6a195279bf319a86549c7febb69d95271ffaeda665498ffdc32e985271ff6e6aa6149a7fdca21593271ffaa9b92149cdfeaa6dc852757f6a5b72149adfdc7215a326d7f71c856489b5fdc72159126f6f71c855049bdf5c721531273bfaa9b62149d6fda96d88526bbf7188568c9b6fdc62159326dbf718856489b6fdc62159126faf718855049bef5c621531273efaa9b42149cfddca6cc85273f7aa9b32149d7ddc96cc85275f76a5b32149b7ddc321592277f5705b32149b7ddc32159126fe770c855049dfd9c06cc85273fbaa9b22149afedc2215a326dfb708856449bfadc22154126ff9708854c49b7f5c121593273feaa9b02149d7f9a96c08526bfe7008568c9b7f9c02159326dfe700856489b7f9c02159126fee700855049bff1c021531271ff6e9965d498ffdc82e965263ff70cba5949c7fda96e165279bf6a5685949e6fda959d65263ff70cba9549a7fcca95593267fe32d858442afbdc8aa95426bef71aaa5509afbdc3aa95426befb31a85509eebcc66a154279efaa9985509e7bd9869d5426befb31a65509afbdca61954279ef661a655098ffdc8aeda3271ffaed9868c9c7febb65da3271ffaed9668c9c7febb655a3273efaed5468c9c7febbaa993269ff71aaa64c9a7fdc5aa993269ffb31a664c9c7febb69993269ff7297664c9a7fecc69593271ff32da564c9c7febb69593269ff7298564c9a7fdca5d5932797f31da564c9a7fdca59593271ff6e99760c9c7fdba65583273ef6e95460c9c7fdba66173271ff6e9965cc98ffdc82e9732737f2e9785cc9c7fcba65573273ef2e9545cc9c7fdba65d63271ff6e99558c9cfbdba55163263ff720ba58c9c7fcba66163271ff2e99558c9cfbcba55163271ff6e99654c98ffdc82e953271ffaa9b954c9c7fdb96a153271ff6e5a754c9c7fdb96995327bcfaa95454c9ff1d385515327bcf6a15454c9ff1d375515327bcf69d5454c9ef3da655153279ef569546489e7beaa55192279ef6a1546489e7bda65519227dbb4a5655889f7ad2955162279bf6a5655889b7eecc66162279fb6a1975889f6eda95956226dfbb31955889f6ed566556226dfb725855889e7eda86556227dbb59d955889fead565516227beb6a1545889f7ad985516227fab59d545889ff2d5454d6227dbb65d635889f6ed9558d6227fab else 0x458cac7fda96d4a22b9fb289a9548abbedc80a9522b6f76e163288abdedc70a9522b7776dd63288adf5db558ca22affa7002a548adfd9636c0a22b1ff2ea88648ac7fcba61d922a5ff32d9854c9c7fcba215922a3ff32da6608ac7fcba955922b9f76a163648aafecca4a1522a7fd32d824c49e3fd8a65d822bafb609a8588aebed826a1522b8ff62995608aebbd8a551822baf762963608ac7fdba654822b3ef6e954208ad7dd956cc822b7e7551b3208ad7f5956c4822b7ed551b1208ae5fd7a661722b97f5e9965c8a8ffdc82e9622b3bf2e965588ae6fd6a65d622bbaf5a954588ae6fda959d622b9bf6a565588af6dd9758d622bdb765563588afe9d5458d622a3ff720ba548ac7febb6a5522b9fb6a528548ae5fda92dd522b1ff6a5b6548ac7fdba660522b1ff6e996148ad6fd986d8522b5f7661b3148ad7dd966cc522b5fd661b1148ad7f5966c4522b7f558db1148afbcd8261d322bff1705284c8af7cd82661322bbf34a1a74c8ae7dd9869d322bdf34a1974c8ad7dd976d9322b9f769d964c8af7cd28655322b5f76d9954c8aff8d28551322b7e76d9544c8ae5fd7a61d912bdf34a132644af6f5972d9812b9fd65da5604af6f4b6655812bfad2d954604af7d59758d812bdf565563604aff955458d812bcfd65d82604afbe528589812bef94a152604af3f595609812beed55182604afbd563609812bdf558d92604affc5284c9812bdf562532604af7d5974c9812bdf565532604aff95544c9812b97f6a5785c4afdb57161d412bb6f5e987504aff8d284c9412afed71ca8504abfb5c52a1412afed708a8504abfb6cc61d412bf6d5e987504abfb5c85d9412bf6d5e176504abfb5c8295412afed718a5504abfb5c2295412afed70885504afdb5785d5412afedb3165504afeb568595412afed71d65504afeb567595412bfe561d63504aff94c558d412bfe529563504aff957558d412bfe595563504abfb5c8289412afed714a2504abfb6cc609412beed61d82504aff9563609412afed71482504abfb5c85c9412bfe558d72504abfb5c8589412bfe94a162504abfb5c7589412bfad59d62504afeb565589412afedb3152504affa42a549412bfe94a152504abfb5c7549412bf6d31d52504abfb5c6549412bfe558d52504abfb5c8149412bfe5b3132504aff94ca4c9412bfe572132504aff94c84c9412bfe54a132504aff94a84c9412bfe5a2132504aff95c74c9412bfe561d32504aff95c64c9412bfe55d932504aff95c54c9412bfe531532504aff95254c9412bfe529532504aff94854c9412bfe55d532504aff95654c9412bfe595532504a97fdc8aeda9265ff716bb6a498ffdc3aeda8271ff6a5b32a0997fdc5aed98271ffaeeaa6609a7fdc7aa998269ff70eaa6609a7fccaa219526bef32a8855098ffdc32ea8826bfd32)))) else (if i < 15 then (if i < 12 then (if i < 11 then 0x88bdf9dc16cc852e7efb31b2214bbfadc2216222e7ef72c854c8bbfadc2215322f7ebb31b2214bdfadc36c8852f7eb705b2214bbfb5c1215322efee700854c8bbfb9c0216222e7ef722bb5ccb9fbdc5aed732e7ef70abb5ccb9fbecc6e1732e7ef71ebb58cb9fbdc5aed632e7ef70abb58cbb7becc61d922edef72176648bf5bd785d9922fdaf59d65648b9fbdc7aed822e7ef716bb608b9fbdc3aed822f5efaed89608bf3bd8961d822fe6f5e176608bf9bd785cd822f3efaeda5608bbbbdc85cd822fee74e163608b9fbecc6e1722f5ef62d985c8bddbdb85cd722feeb60987588bfbad8260d622fdaf4a565588befad28695622fbaf59da5588b9fbdc8aed522e7ef71ebb548bddbdc7aed522e7ef70ebb548bff2cc54a1522feeb60987548bfbad8260d522f5efaed98548bf7ad82661522e7efb31b7548bd7bd986dd522f76faecb7548bddbdb82dd522f76f2e0b7548bfdad282dd522fd6f660b7548bddbcb76d9522f76f2ddb3548bd7bebb659522f5ef6dd96548bf5bcb7659522f6ef62d83148bdebdb660c522e7efb31b3148b9fbdcb60c522f7e74ed83148b9fbdc8aed322e7ef71ebb4c8b9fbdc5aed322e7efb31b84c8bfbad8261d322e7efb31b74c8bfd9d7361d322ffe34a1374c8bf3bd8961d812fcef62582604bfbad28549812feeb4a132604bf9bd87609712ff6d61d185c4bd7bd8b661712fd6f61d985c4bf7b581661712fb6f5e1a55c4bbdbdc7609712fd6f5e1925c4bf7b581661512f76f5ed87544bfdb57161d512fdcf66152544bff2d25609512ebfb70aaa548aadfdc72a1a22af7771ca84c8abdf5c72e131263ff708baa20acfeca82c9a72af7b3097a61cad7ed982c9a72adfb309a7658ab7ecc269d952afeb309a7550abfccc269d632a3ff722bb69cac7febb661a72b3fb2e0b269cae7ed982c9a72b1ff2ea8865cac7fd852e9972a9ffb31a865cac7fccb6a1972b9bf319a865ca8ffdc22e9872b97f5e98961cac7febb65da62a9ffb31a7658ae7ecc269d962b1ff6a5b85d8ae5fda95e1762b1ffaed96694ac7fda96c8a52a9ffb31a8654ac7fccb6a1952b9bf319a8654acdfeaa6dc852ad7f71c85648abdddc7215322ad7f71c85644abdbdc7215412b3bfaa9b6214ab6fdc6215922afb7718854c8ab6fdc6215912afaf71885504acfdeaa6cc852a7f772c854c8aafddc3215a326df770c85648ab7ddc3215912afe770c85504abfd5c321531273fb729b2214acfeeaa6c8852b7f370db2214adfe5c16c8852adfb70885644abfadc2215412b3feaa9b0214ab7f9c0215922aff6700854c8ab7f9c0215912afee70085504ac7fdba65d652a3ff720ba594a8ffdc22e9652b9bf6a567594a8ffdc22ea552abefb31a8550aeebcc66a1542abefb31a6550aafbdca619542b9f76a19758cae7dda8655632bbe76a15 else 0xfe6fca664da23f1ff6a5b5288fc7fda96cca23f3bf299b5288fe6fca6654a23f3bf299b3288fa7fdc6aa9923e9ff716aa648fa7fdc3aa9923edfd714b1648ff2fd97299823fabf298a5608fb3fecc655823fcbf29995608fc7feaa6e5723f5bf6e4a65c8fc7fcba655623e7ef32d87548b8ffdc32e9623e7fd32d62604c9ff8cb589810bcfb4a197588ff3ed28655623e3ff70cba548fc7fcba64d523f1ffaeda9548fd6fdb9299523fedb31528548ffaed28299523f1ff6e993148fd6fdb664c523f5fd64db1148fc7fcba655323f3ef550ba4c8ffbcd284dd323fcfb4a1974c8ffaed28299323fcfb4a1954c8fc7fcba656223e7ef32e88548bc7fcba64e223e7fe32e226042f3ed28549913fcfb4a132644fafedc2aa9823a3ff70ebb6a0e8ffdc32ea883ad7fb318961cef1fd8961d823bc7f62587604eb5fecc661763b1ff69abb654ec7febb6a1953b57faed87654ed5febb5d9953a3ff720ba594e8ffdc32e9653a9ffb31a864cec7fccb6a1933b1ffaeda864cee6fcc66a1933b57f32d8764ced5febb61d933b57faed7664cee5fda85d9933bd3f59d6564ce8ffdc82e9633b57faed87648ed5febb5d9923b37f2e987608e8ffdc32e9823bafb609a8588eebed826a1323b57f6e587608ed5fdb95d9823ba7f2e987608ef9ed8261d623be7b609874c8e8ffdc82e9623b3fb2e928588ecdfcba61d623a3ff70cba588ecefcba58d623bd3f59d93588e8ffdc82e9523b3fb2e928548e8ffdc32e9523a3ff720ba4c8ecfecba4a1323b37f2e9874c8ef1fd87609913b57f6e587604e97fdc8aed97371ffaeda864cda7fecc69d93371ffaeda764cdc7fdb96a1733797f5e5a85ccdc7febb6a5523797f6a4b7548da7fdca5d993323ff720ba58cc8ffdc22e963331ff6a5b8288cc7fda96cca2333ef6e1a4288ccfbda46cca2329ff32998888ca7fcca66162331ff618ba648cc7fcba5d992329ff329984c8cc7fcba5cd92331ff2e963648cef6d252e982333df494ba608c8ffdc32e982329ff329b9608cc7febb6a582331ff6e993208cd7f5936c482323ff720ba588c8ffdc32e962333bf2e963588ce7eda94a162339bf6a567588c8ffdc82e93233dbd65cb6604cb7f6cc64d8133dbd2d993604cfbe5285898133cfd65582604cfbe5284c98133cfd64d82604cf775935498133d7d465785c4ce5fda95e17133d7d6a5785c4cf5f5876617133d7d661765c4cfe75655897133f6d5e1a45c4cd7f5b864d7133d7d5e1935c4cf5f57664d7133ddd595935c4cf775656497133fd94a1525c4cf775985497132fdd719525c4cf775965497133ddd64d525c4c9fbdc5aed872f3ef696bb61cb9fbdc3aed872e7ef70abb61cbd7bebb625872ef6f71c854c8bbdbdc7216222efaf718854c8bbebdc6216222efe770c854c8bdf9dc26cc852efe770c858) else (if i < 13 then 0x5dd876617347d775e1965cd1f9ed785d98247afb61da66091e7ed976998247cfb61d966091fdcd7b5cd8247f735e1736091f7cd965cd82471ff6a5b82851cff9a86c0a1475fe661b02851cff9a56c0a1477ee551b02851dfe9826c0a1463ffb31ba2051c7fdba65c814737faa9b72051d7dd976cc81475fb65db22051dfcd736c881463ffb31ba14518ffdcb6a051471ff6e9981451cfedba60851473f76a1b31451d7dd986cc51477f36cd8214518ffdc82ea11471ff2e9988451c7fd952ea11473ef550ba845197fdc5aed87431ff696bb61d097fdc3aed87425ff70abb61d0a7fdc52e987431ff2e9b561d0e3fd852e9874397f5d4ba61d0c7febbaa98742d7f71c854c90b5fdc72162242dbf718854c90b6fdc62162242df770c854c90d7ddc26cc8542df770c858890d7ddc16cc85425ffb31b22150b7edc221622431ffaa9b2215097fdcb2153242dfb708854c90d7eecc6c885435fb70db22150d7edc16c88542dfd704854c90b7f9c02153242dfe70085889097fdc8aed73425ff716bb5cd097fdc2aed73425ffb31b85cd0c7fcca6e173425ff71ebb58d097fdc5aed63425ff70abb58d097fdc7aed82425ff716bb609097fdc3aed82431ffaeeaa6090e3feaa61d8243c7f5e1766090f1fd785cd8242cff721736090f3dd3858d8243cfb609875890f3ed8260d62434ff62d831490d6fdb660c52425ffb31b3149097fdcb60c52435f74ed83149097fdc8aed32425ff71ebb4c9097fdc5aed32425ffb31b84c90f3ed8261d3243d775cd874c90f7cd284dd3242dbf71aaa65cfb6fdc6aa9953ef6f71ebb548bb6fdc6aa9933efbe71abb6042aefdc6aa9873f3bf315b6aa8f9dfdc7aed522677f71ebb548daefdc6aaa553ebbf71aaa60cfaefdc6aa9733e77f71ebb548aaefdc6aa9823ebbf71aaa5c8faefdc6aa9523ebbf71aaa4c8fa7fecc2e9973e9ff718ba65cfa7fccbaa9973f1ffaeeaa65cfa7fdc6aa9973f9bf71aaa65cfa7fdc5aa9973e9ff70eaa65cfa7fdc2aa9973f9bf6a4a6548fe6fda9299323edbfb3197298fe6fcca65ca63f9bfaa997298fe6fd97299a53e9ff724a5688fb3fdc9295823f1ff6a5b2294fcefca66cca53f3bf299b2294fafbdc4295a23eeef710a5608fc7febbaa9953e9ff71aaa654fe6fdc6aa9953e9ff70eaa654fa7fdc2aa9953f9bfaa8a6654fd6febb299953f9bf69ca6654f8ffdc32ea553e3ff708ba954fa7fcca955923e7fe32d528442e6fd97299a33f9bf2999568cfc7febbaa9933e9ff71eaa64cfa7fdc6aa9933f9bf71aaa64cfa7fdc2aa9933f9bfaa8a664cfd6febb299933f9bf69ca664cfc7fcba655733e7ef32d63548bc7feaa6e5733f5bf6e4a65ccfe5feaa5e5733fd3f5e4a65ccfc7fcba65d633f1ff2e99558cf9fbccb5cd522e3ff708ba58cfe6fd97299a23f9bf29995688 else (if i < 14 then 0xe02cc08d019c04c009800097fecc6cc52a75bf719b314a997fecc6c851771ffaa9b2145dc7fda86c851775df721b5085d9fedc2aed73531ff661b7aa9a8ffdcaaed635b1ff661b2aa9ac7fd852e9976a9ff722aa65daa7fdc5aa9976a9ff70aaa65daa7fdc1aa9976a3ff708ba955a9efccb95563525ff32e5558d09fbccb955632e3ff720ba889ac7fd982ea226a5ff32e885cd09fbccba21732e5ff32d6388909fbccb58e222e7f732d63888ac7fd876d6aa5e9ff706aaa217a7fdc5aa9765e9ff706aa5d97a7fdc92d5a852bef710b56a14d7ddc26cc855f5f7705b3215797fccb66211469ff32a5558d7c7fd872e9635f1ff614ba58d78ffccb61da62b1ff2ea5558d797fecc6e0a15edfb708b56614a7fdca2d598275ef551b22057c7fcbaa22115e5ff32d98955497fccb66255265ff32d98955197fccb662552a7f770ebb6091a7fdc7aa9965a9ff716aa6596a7fdc3aa9965a3ffb30ba58d6c7fdc92e9635b1ff2e99758d69feccb5cd82525ff32d7360909fbccb5cd822e7bf32d63609497fccb58d82427ef32d63608ba7fdc5aa9925b1ffaa9b92856c7fdb969ca15adfb724b56094c7fdb9694a15acff724b5608fcdfeaa6dca15b57f661b72856cdfdb7694a15adbf718b56090bebdc62d5822f37f6dda32856beedc62d5824777b309b72856bdf5c72c58226ebf718b5608fbdedc72c582473efaa9b42856cfbda76d0a15afeb710b56094cfbda56d0a15aeef710b5608f8ffecc6e8515b1ffaa9b91456cfbeaa6d0515b6fb62d821451c7fcba662115b1ff2e997845697fccb95582427ef32e55608b8ffdc32ea115a3ff70ebb6a1497fdc5aed98531ffaeeaa6614a7fdc7aa998529ff70eaa6614a7fecc6a197531ff654ba61d4cfbd542e987523ff70cba61d49ff8cb61d620adbfb31985d94c7fdb96a0a552dfb724a56094cfbda86d0a552feb710a560948ffdc32ea55527fe32d8784428ffdc82e973527bf32d8758d497fccb61d63427ef32d8758cbbeeccb58d8253ebb61d636094f6ed9758d82531ff655b8aa91cfbd546e2aa471ff655b6aa91cfbd546daaa471ff655b1aa91cfbd546c6aa471ff6a5b12a11a7fdc7aa998469ff706aa6611c7fd952ea88473ef550baa21197fccba2132427ef32e884c8bc7fcba62587469ff329876591c7fd952e987473ef550ba61d197fccb61d32427ef32d874c8b8ffdc2aeda6469ff32d976991c7febb65da6469ff722aa6591a7fdc7aa996469ff716aa6591a7fdc1aa996469ffb31a865918ffecc6e8854737faa9b72151b5fdc721592473bfaa9b62151b6fdc621592473f7aa9b32151b7ddc321592473fbaa9b22151bfcdc2215322b3fdaa9b12151d7f5c96c485477ed711b12151b7f5c121592473feaa9b02151b7f9c021592471ff2e996955197fccb95532427ef32e554c8bf else 0x327a59e299449dea76a9d69f908ca010474ce74a9cbe71f9c3e6ff9bbe6d49b1269e529a68e4f7410499ce658041263d04101049888fa004125fc975a5b0962a56f95525399479944943a4f3041010404124cd929e46b90bc1040410104041241f903c104778dde38ffe3ef8f7e3c48ed238e8dce3588d2218b76ce3388ca2318768c1040410104833a3088be22e88b622c88ae22a88a6227d898a24788b2211041220187c61e18718e8d778e1b6869a18b85c215584be11483ba0de768e0ce768e0a8820a072815e04780b20117fd9fd07e81f7079a519a7f01fb07e801040411f907e01f507dc1f607d41f407cc1f207c15eea7b3deb47a641040411e697a25e7979a5e697965e4978e5e29780ddf3778dde3774ddc376cddb376cddb376cc2a5768dda3764dd8375cdd63754dd23744dd4374cdd3374cdd2304a5d13740dcdd7309ca77205c667159c307029be46ef96786ddc3a16d183a104113dd041010469e5a796c15a796c81b056ba928d6b69aca0e841040e841040411aaf69e5a9469e5a5e68e1a122a04a6667dd9d1668197a657c1046511934041138c0410104041190363498b7041188604101040410104041186b611581f5fb97c85e88104041010404117875db17305c556fa5b7d6b95a4d67859e164758b160657815c5567d512563d512554d5125449522544951254481040410104041010453dc104041010404114dc53054a6525946550a53ed04113dd04101044edd39c4e313664d0131a4bd12ce4aa128d49f4104041010449b4104041010448f0104041121647c01040410104041010447811c546a915a466918a45e8104041116a041115a3e40f80452913a445110443a462b42f90be1398fa043390be423506740d902640584e63fecfeb3f6cfcb3ec0fa03e40f8004a4f700914f553d141043d14f453c50eee3b4c82d3ae01043a74e8d399c104395c82d38c41043884104384482d37ac1040410ddb376cddb18acdaa18acbb618acd843578b3434b4cfc3300c8f31a4c433074bf72f44bb62e6cb800e84b5a0e843a10e84b342c64b192c64b192b74ac22a70a812998a4b28c09ff27909c926e497d258894724848e50ff447f11908b42264868041084d20f482d201c10404101041fdc62b0e847bb1ca472904107291ca47a01de87541ca47291ce47291c386d214046b718ac4e613984e61a7062b139868119c44e6195863b18ac4e618405ea11905c41678578154852c144450113984cb129446411fc464119046411904330a14275041041804101040e843fd0fb43b108283a104a41040e4410404103810a141040dc43610d443410cc42e00c582fb0b802c504102b50a942950a142750994104041025509142350868104041010408281fa07a81da07281a4065017905a41590410159052413904a4119042410403a40c))) else (if i < 17 then (if i < 16 then 0x40410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104da0f673d963648041010404101040410104041362dd87760d041010404101040410104041010404101040410104041010404101040410104d7c8104d7043a1d4a7590d57f52905a7544d4a750ed3a34d8d3234b80410104041010404101040410104d2a2ae1ab4748daac6ef204101040410169041010404101046f91bbed19f457d033447d0b341cd030104cff116a04133eccf473b6ce43380cdc3360cd42f63c616f73bd8f185bd4c1040412f73bd8f1850410104041330fcc3f340697b30fcbd32e4cafb2ae4b3b293c9e323c4a37216c7c31e0c7831d0c7031a5c656f73c616f5304101040410104041010404101040413175c513113c3e30ddc30af5304101040410104ab86ad1c29f0978846ee2041010404101040410104ab86ad1ab07097c1f01040410104041010404103a1c12c3a10e843a1c096fffbf643a10e843a10e86fc9bee6f9ebe0ef73bd8ef5304101040410104041010404101040412f43bca2ae1ab46ac1bc36ef2bb8810404101040410104041010404101040410104041010404101040412ec7badeea745e915aba05678b9c439126e43810dc6e610566e46b8d810459e2e2604101044a36e16833ade5b6a5e69b5e2d3cb42ecfbb3aecdbb32c1040410104b2c2c958ed1a79b1ea348b152c39b0a6c0eb03abfeaf8ebd3041010404101040410104041010404101040412ae1ab46ab1aee2b9d04101040410104adcab82adcab72ad5eb47acdeb270410104041010404101040412ae1ab46ac1ac32af1041010404101040410104041010404101040410104ab86ad1ab06ab176cc10404101040410104aa8410404101040412a70a92a77aa8929f3a73677aa6f6997a5c63284f769610410104778e946a4828faa37c1044a3677aa33e8bf833a3280411da3a23a868a134104996277a8ca0104a09e8019f6e7c04e else 0x41010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101) else (if i < 18 then 0x125b0d224b41a441b021a42964296021ac295c3b40217c295820142f8802852a852a05298529040286a0be34a210d01a441a0219c336c336821983364294020d9e1945b3c32092705f124e49e18c69392686218040c2249892c300f6724a0be304101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040410104041010404101040 else (if i < 19 then 0x4116a151215101a0a150e150c14ba2d049705a092d0b4127f16820382d05410340c340820803188598459041a27910344f6250a9e842c41a00818344f820682c04c8c4e045784160880123070062808c1b8680284150008ae4f02a00a0c54004b8a7f8180c039fc1030115a115811561154150415021500106c115214ba2a0497054092d8a8127f15020382a053f433f0229c33ec33e8229833e422941a80918a4089508a308a2083408940cf808970cf70cf608a1083308a0089f089e089d088d00002473d412080a02f10020580546000110b72067a0130483000224048c1800403e30200b0078c1902604a0601887c302604a0900a100001d026303a0bc5b8c010b710770867982f14f205e20600bc40b800880680a044305a0b0078c0109c127e11200860ac4d8140104111b80010c11024102a0262dbe100c1f00b0092088134060049278802100a0069f4099009a7c10811109ec62042ea7a18810ba0484c900c0884f231102044c8e7809814f012e202802c0b07e11059e025853c04a8a78094100a02600860280101318130042014034498132012026201c248010c0581311030269e0424448013180a080b0062200508f288801c1e04710098678060108d01229de0884080110b6f041482505004c80980001c04e230a09812813100090a174208c0a8091cee03220121116084100c11021040300007c0f0c0001d0303114048008c0e01200230360205b742068206444089db840141c80c8c09888008310e19da0004180000a76076d853b8443053b0675876d04080099d4310a101d3a4403a740842040080c4ea02089d006009181001606004100384418441ce712730a720a710a70010201014de14dc11021000008539829b67280900840040282f8c0901010630242db218c418c3b60018001862080202e188601021842008410611ce4087c00201004903f801026302c04c010f6a80b000008818c00804000410200d3600400050280300008020010fe000604f6a87e1813dae1f4600c020001ed6018008604c00880980c100102a20040183e0c00804000300400049ac01813016000a0082f880487c000300418c4008310801061107b00020000540580220090002016000400021e805803daa024a1e401883c01310150060006050096d40261dca00c0980b00040041804180008040004da61804180203420083b060187508120e400402009287202220e8040048c050000e4301338c41cc2008390803a6ad9c03c3914074e2106f0e2201d384538033813488074df100e080e9bc24d0004010d33801004301a004010d3300c00430e0030010d3280c00430df37441bc2028040837cdc10014c8008602c0080018010002da41b80580020020142012020498c201c0306eda4008a008298829842980297c297821b43b44297434892e069 else 0x541e8001f150f1418c2e261e242a85c443c40233f87881e8ce0020688080218ce034407a09006002202c05e202800841bc010b878200343e1c1e1a1e181e1614b61904320130181aa708cd08000302e1411981e121150103608840000f88190450263e101e0e1e0c1e0a1a34107545c5400120440102a321040060008e8c0404801103f4f8206426465d17010501a0f0040c0102e0863a2c1e081e061e043185c042a983c0020c00b04204440200ec1600f25150c62a2a18854544e092d0c5127f081c07620020800c002201c06000860001600218000580207bfc3bf83bf4650b7e06412a50aa40aa30efb0efa0d224b41904070348951041781912a108220d140020607be42a8020800f8b7c077b877b04648310f00608a7c0cef5112220a0940c068000405204c208c80f05a260677a08926f30ef20ef10ef00a9e002253a0044a7000880003003035360045448231c008b7787770c616ed0a7f18a20383144310008a8887760aa16eb0eea0ee90a7f186203830849742970296c29682a6820114c8ad044415a2940f8c2003c044304c0400482220100260fc63042040048221a9852c08862942a5c060860010018303e04c1f8d4b02216e80a950a940020bc5f900983f044302608840f80480c183da2004c60d41480918be044201203040b00f8949877385490548845e81312900a8f08bc0a8e081351a2518111a224048f73045d801100d0102174030400409885c80c0023a1e084098c1980901030680b0080c1e024103b0c4207618440ec058b728404060150e01203060e81c80918181182e00a809280111204c020882d0d08b708b60d0c0d0b0d0a1682a141a12048408c0900815081502a10151610381a0e1a0c151)))))
def rootData11 (i : Nat) : Nat := (if i < 19 then (if i < 9 then (if i < 4 then (if i < 2 then (if i < 1 then 0xebfcd810abc7fcba9557cef9752aaf9dfaaa555f9bf444aabf57e779557ecfccd2aaf1ff2e9635f9ef44466bf5de778cd7edbccd19afdd7956335f9f744444bf6ee668897eedcab112fdf38ce225eafedb902bc7fcba8457cfe97508af9fdaaa115f9fb44422bf5f6778457edeccd08afddd956115fbeb19c22bf7e6228457cdfb53332d9fb6a6225b3fad4c22b63fda9a215cdfb53332b9fd6a611572fed4ceea677da99554cfdb5311298ff2ea88431ff55510865feaa9dd0e3fd113ba1cbfa226643a7f3bccc855fdb72150adfb6c42a15f76cc8542bf6d910a857f5b12150aff36042a19df2ea55433bf554aa8737e889550eafcef2aa1d9f99a55439ef44466875de778cd0edbccd19a1dd79563342b7edb0a4867ecba8890cfdd551121cfba222243af73bc44876ee668890eedcab1121df38ce22439fb44422875f6778450eeecab08a1df58ce1143bf31142284efdb6aa8fc7fb53441f97f6a6773f37ed494c7cefcba998fcdfb53331f9df6a6553f3f6d4c447e7f5a9844fc7fb53441d9bf6a6663b3fad4c22765fda99dcdcfdb53111b9bf6a666323fe5d324667eda9888ccfeb530899cef626882f5df555105edbeaa9dcbeb7b313b97e6fa22772fadf3bb2c5f6bd98998bf57d113317f2f9de662f75f3334a5ddbdb7214bbd7b6c42977e76cc852efd6d910a5dfb5b1214bbf73604297bcf2ea552f79f554aa5f73d98954bf67d112a97f4f9de552fb9ecb4aa5fe3e66954bf73d111997f679de332ff4f334665ff1e558ccbe77d10c917d6f9dd922fb5f333245f73e55648bbd7b6c2917deb4a6222f7d7554445f7ad98888bf75d111117f6b9de222fbd6cb4445feae66888bdf5b4b1117fcb956222ffc719c445f7b598844bf76d110897f6d9de112f7dad2c225ff3655844bff2c670897ded64a112ffd3114225c7fcba660ac7fb5344151ff2e9972b2fed4cee566fda9998acefb532a951ff2e9922b3f6d4c4456fb6aa504af76d10a095f6d9dd412bf5b3328257f3655504aff2ac6a095fe54c9412bfd311282567f5a9844ac7fb53441397f6a6772737ed4ccc4e77da99549cfdb5311139fd6a6112777d554cc17cfa779982ebf4eec905dbe999920bbf494c4416feaaa8882efd3311105efaa22220bef53bc4417eea668882bbf36e40857f66cc810afecd98a217bba885042fb74eea085fae999410bfd51128215fdabb4c42dfb5549885ff4461310bbeccc26217bda884c42fbb4ee9885fb6999310afecdaa6217f99144c42ff32a89885df6649310bfe51126217fd11348429ff37410856fe6e0210aefcdb84215ef9b60842bef36a10857f66cc210bfd88a42217fd1138442dfe5550885dfc662110bdf94442217df2778442fde4cd0885fdc956110bfd8aa42217fd1538442efe3250885ff888a110a3deda554eff91144c42 else 0x2dff55440857fe6dc810befd3b90215ff9b52042bff3644085dfe648810bff51110215ffabb5c42bff374b885bfeaa9710affcdc2e217df9785c42eff330b885efea21710befcbb2e217efa665c42fbf2e4b885dfe649710bff5112e215ff9ba5842dff554b0857fe6e1610bff88c2c2177f9985842f7f510b0857fe6dd610befd3bac217ef9625842eff324b085ffa889610affd5daa215ff9ba5442dff554a8857fe6d9510bfbcab2a217efa665442ff7368a885ff66cd510bfbca92a2177f9925442ffd444a8857fe6e8510b7fd550a215ff9b21442eff3242885ffa888510bfdc8c28217fba885042ff722ea085fee61d410bfdcc328217fb9765042ff722aa085fee5d5410bfdcb2a8217fb9825042ff7104a085fee5c9410bfdcb128217fb9525042ff70a4a085fee889410bfed5da6217fd9b84c42ffb1709885ff6461310bfecd426217fda884c42ffb36e9885ff645d310bfecd3a6217fd9874c42ffb36c9885ff6699310bfecc326217fd9764c42ffb36a9885ff62d5310bfec8aa6217fd9a54c42ffb2ea9885ff6595310bfecd926217fd8b24c42ffb3449885ff6609310bfec4126217fd9724c42ffb2c49885ff6549310bfec2926217fda224c42bff5769085ffa889210affcdd24216ffaaa4842eff25290857fe6e1210bbfccc24217bfa884842bff36e9085ffc45d210befd3ba4215ff9b64842ffd24c9085fbe999210affcdaa4217fb9144842ff72a89085ff644d210bfeca9a4215ff9ba0842dff55410857fe6e0210bbfccc04217bfa880842bff36a1085fee550210bfeca984217ff11a8442dff5550885ffc462110bbfccc42217bfa888442ffe22f0885f7e9de110bff88ac2217fb9548442ffb2a70885ffc44a110bbfcc942217fea228442ffe1710885ffc6a2110bff94442217ff1a78442ffe30f0885ffc69a110bff8c342217ff1768442ffe16b0885ffc696110bff8c2c2217ff0858442ffe2eb0885ffc596110bff92ac2217ff0b28442ffe3450885ffc60a110bff84142217ff1728442ffe2c50885ffc54a110bff82942217ff2228442cbfd553bd3c7fa2277a73be5d4ab4e77eaa9569e6fd112ad3d5f9de55a79ef444674f5de778ce9eebcab19d39fb2ea22a73f7554454f3ee8888a9ebdcef1153ddb95622a7be719c454f5f6778469eeecab08d3df58ce11a7bf3114234e6feaa999de9fcef333b57f6dc8176b7edb042ed77db5085daff36010bb9fd2ea11773fb55422ef3f688845debecef08bbdbd99a1177bbb2ac22ef7e622845d8ff974cbb597f6a6776ba7f3bb2cd767d96955acfdb531135dbb65a226a3fedc554bc7fdb5aa978ffb63552f1ff2ea885f1fe5d510be3feaaa217cbfd553bafc7fa22775f37f554ccbf2fe889997e9fcef332f57f6dc855eb7edb10abd7ddb32157afdb6442af5fd6c4855) else (if i < 3 then 0x27beecb4664fede668cc9dfbb4b1993df76563327faf2ac664ff9d548cc9affd76c9139ffaa992273fed43244f3fe886489cffb4cc913dbf99992273fed2b244f77e556489ef7aa8c9139ff68d9227bef19b244d7fdb96089cffb52c113dfb4a562273fed4ac44dfeebb5889dfdd54b113dfb6a562277f6d42c44f7ed985889f7dd10b113fbb59d6227bf6cbac44fdee775889fddacab113dfb6556227fb72aac44ffad545889fddac6b113ff38cd6226bfedcaa44e7fda95489efda529913bfbaaa2227bf6d4c444efeda88889efdb311113efba2222277f6d34444f7ed968889fddccd1113bfb6962227bf6cac444ff6e558889ff5aa91113bfb68e2227fe719c444e7feaa6449cffb50c893cffa2191273fed3b224f5fe776449cffb4ac893ddf95591273fed1b224f7de336449efdc44c8933ff6e98126bfedcb024e7fda96049efea32b8939ff6a57126ffb5dae24eff6aa5c49efeb52b893f7d5e17127bfacc2e24fbf6885c49fbeaecb893dfd6597127f7b332e24eff5a55c49efeb2ab893fdd9557127fdaaa2e24f7f5935c49ffac66b893ff958971267fedd2a24d7fdb95449cffb52a893befaa941277ded42824f7bd985049f77d10a093fed45d41277ded3a824fdbe775049bf7b6aa093bef6954127f9f2aa824efbda35049ff3c66a093def6494127fd7112824d7fdb94c49efea329893fed4513126ffb5da624eff6aa4c49efeb729893dfd6a531277fad42624f7f5984c49f7ed1098937fd6dd3127bfacba624fdf6774c49ffaa6c9893dfd6593127f7b332624f7f5954c49feecaa9893fed5513127ff2592624ffd5324c49efeb249893ff95893127ff3112624eff6aa8449efeb530893bfd6a21127bfacc4224fbf6888449dfeb4f0893dfd65e1127efb3bc224eff5a58449efeb2b0893fdd9561127fdaaa4224eff5a38449efeb270893ff58ce1127bfac94224ffe6228449bff576d3057fe6e9760b7fd552ec17ef9a79982bff576d105bfe69da20befd3bb4417efa666882eff2ecc9057feaed820affcdd30416ffaaa6082eff372c105dfe4a5820bf7d3330415ff9ba2082dff55441057fe6c4820affcdd2e416ffaaa5c82eff330b905fbe999720affd5dac415ff9ba5882dff554b105dfe4a5620affcdc2c417fe9285882eff330b1057fe6dd620bf7cb3ac417dfa775882ffd2551105bfeaaa220bff494444177f9988882ffd24d1105fbe99a220bff45c44417fe9a88882ffd5111105ffa69e220bff4c3c4417fe9a68882ffd30d1105ffa5da220bff45ac4417fe8b18882bff576d085efea21a10befd3bb4216ff9a66842fdf4ccd085bfe689a10bff51134215ffabb6042f7f510c0857fe6e9810b7fd55302177f9896042fbf4eec085fbe2d9810bdfcc330217efa666042f7f304c085dfe649810bff51130215ff9ba204 else 0x4aff6a2ea095bef69d412bedf3ba8257fb515504adf7b4aa095fcf955412bfce9928257fae22504aff6d54a095fed6a1412bfda5428257fb688504aff6b4ea095fed61d412bfdad328257fb586504aff6aeca095fed695412bfda52a8257fb485504aff6aeaa095fed595412bfdb2aa8257fb5a2504aff6944a095fed609412bfda4128257fb572504aff6ac4a095fed549412bfda2928257fb622504aefeb530895bfd6a2112bbfacc42257bf688844adfeb4f0895dfd65e112befb3bc2256ff5a5844aefeb2b0895fdd956112bfdaaa422577f592844affaa650895ff988a112a7fedc5544cffdb7aa899ffb6d55133ff6d6aa267fed9d544d7febb6a49cffd54d4939ff6a5a8267ff5db504e7fdb96a09ddf96cd413aff6a0a826bfedc9504e7fda92a09affd76cc135ff6e998273fec53304e7feaa66099ff9754413aff62a88279fec4d104e7fda9a209d7f9754413affaaa88279fed4d104e7fda969c99ffd76d3939ff661a7275ff4434e4e7feaa65c9cffb50cb93cffa2197267fedd30e4cffcba61c9cffb52c393b7faaa7727afed4cee4edfda89dc9ebfb313b93e7fa2277273fed4b4c4cffebb6989cffb30d313affa21a6273fecbb4c4edfe776989cffd54cb139ff69d9627aff3bb2c4cffdba6189cffb52c3133ff6e976273fed4aec4eefeaa9989edfb533313bbf6a26627b7ecc4cc4fafe889989ddfb4f3313dbf65e6627e7f3bccc4e7fda969499ffd76d2939ff6e5a5273fecc34a4ebfe886949dbf96ed293b7f9dda5273fecb34a4eefe666949defb4a52935ff6e4a5273fed494a4dfbdb42949affd76ca935ff6e995273fead32a4e7feaa6549cffb50ca93cffa2195273fed3b2a4f5fe776549cffb4cca93dbf99995267fedd30a4cffcba6149cffb52c2933ff6e88526bfedc90a4e7fda92149bbfb6e42937bf6d88526fdeda10a4dfddb32149bfdb6442937fd6c48526ffcd810a4cffdba5d499ffb74b2933ff2e965273fed4aca4cffcba9549defab52a93ddf56655273fed4caa4ef7cba9549defd552a93ddf6a655277bed44aa4f77d989549f6fd112a93bdf69e5527ebf3bcaa4ef7da69549eefb2d2a93f9f99a5526fdf5daa84ff3e555509df7ab4aa13befaa954277ded42a84f7bd985509f77d10aa13bef69d5427edf3baa84efbda65509fd7cccaa139ff6a5a3267ff5db464e7fdb968c9cffb30d193affa21a3273fecbb464edfe7768c9cffb2cd193bbf999a3273fecab464ef7e5568c9df7aa8d1935ffaed9326bfedd3264e7feaa64c9cffb4cc993dbf99993273fed2b264f77e5564c99ffb74c1933ff6e973267fe5d2e64cffdba58c99ff974b1933ff6e953267fe5d2a64d7fdb954c9fe7aa8a993bf7aaa3327beed4c664efdda88cc9efbb311993ef7a2233277eed3c664f7dd978cc9fbbcef1993bf769a33)) else (if i < 6 then (if i < 5 then 0x72a7ff5db4e567fd9869cad7fd10d395bfb2c9a72b3ff5532e567fda865cae7fd10cb953ff6e9872a7fe5d30e56dfd7a61cacffb52c395b7faaa772bafed4cee56dfda89dcaebfb313b95e7fa22772b3fed4b4c54ffebb698acffb30d315affa21a62b3fecbb4c56dfe77698acffd54cb159ff69d962baff3bb2c567fda9618a9ffb74bb159ff6a5762b77f554cc576fda9998addfb513315dbf662662bd7f444cc56efda7998aedfb2f3315f3f9de662b3fed4b4a54ffebb694acffb72d2959ff659a52b77f3334a56f7da5294acffb5252959ffaa9952b3fed432a573fe88654acffb4eca95d7f9dd952bb7f3332a54ffdba214acffb52429577f6dc852af7edb10a55fddb3214abfdb6442957fd6c4852affcd810a54ffdba594a9ff974b2959ff6a5652a7fe5d4aa5777d59954acffb532a95bdf2ea552b7bf554aa5777da9954adefb512a95ddf662552bdbf444aa56f7da7954aeefb2f2a95f5f9de552b7bed34aa5777d96954afcfccd2a95fcf955542b7df552a856fbda8550af77d10aa15bef69d542bedf3baa856fbda6550afd7cccaa157f7aed632b7ef552c6577dda958cadfbb50b195df7661632bdef442c6577dd9758cafbbceeb195df7655632bfaf2aac657f9d5458cacffb52d115bfb688a22b3fed494455bfdb8288abbfb6e51157bf6d8a22afbeda94455ff9b0288acffd54c9159ff6a1922b9ff44324567fda7648aebfceec9159ff699922bb7f33324567fda5648aeefcaac915df758d922a7fe5d30456bfd8a608acffb52c1153ff6e8822b3fed490455fddb3208abfeb624115b7f5e9722a7fe5d2c456efd6a588acffb52b115fb758d622a7fe5d2a4567fda9548a9ffb7429159ff6a4522af7edb0a455fddb3148abfeb6229157f7aed322bfe61526456fdeaa4c8aefbb729915df74a5322bbeed4a6457fcd284c8aefbb309915ef7a21322b7eed3a64577dd974c8afbbcee99157f76d9322bbeecb26457ede664c8aefbb2a9915fd7955322bfceaa26457fd4b14c8a9ff9751115dfb4a6222b3fed4c4457fcd23888adfd9751115bfbaaa222bbf6d4c4456feda8888aefdb311115efba22222b7f6d3c44577ed97888afbdcef1115bfb69a222bbf6cb44457eee66888adfdb4b1115dfb656222bfb72ac4457fad54888aff9ac71115ff92c6222b3ff55322567fda8644ae7fd10c8959ff69d912baff3bb22567fda5644aeefcaac895df74c9912bbf711322577f519604acffb52c0957fdaed812bdfb4430257bf48a604adfed54c095dfd6e5812bbfac4b02577f5a9604aefeb2ec095f7d9dd812bf7a5b30257ef666604adfeb4ac095dfd655812bfbb2ab0257fb554604affaac6c095efd609812bbfac930257fd532604affcc44c0959ff6a5712bbfa8caa2567fda9544adf7d54a095fed461412b7ded428257bbe8850 else 0x54bfe79652a977efaed832fddf443065fdbe7760cbfd7cccc197fcf955832efdf5dae65dfbdb85ccbfb7af0b997eefa21732ff5f332e65ff3e555ccbbf7d76b1977ef6e1632ff5eb42c65ff9d3858cbf77d10b1977ef6dd632fedf3bac65ff3e5558cbff3d111997fe761e332ffcec34665ff9d768ccbff390b1997fe75d6332ffceb2c665ff9e558ccbef7d10c917def61d922fbdec33245f7bd76648bef790ac917def595922fbdf2ab245dfbebb608bf77d10c117befaa9822fbdedcb045f7bd89608bef7a52c117eef61d822fedf3bb045febe66608bdf7b4ac117fcf955822fddec1b045ff9e33608bdf7d5441177ef6d4822f7ded29045ff3e55208bbf7b664117fe78cc822efded89045efbeaa5c8bbf7b70b917def661722fddf442e45f7bd965c8bfd7cccb917fcf955722fedeb9ae45ff9e335c8bbf7d76b117def4a5622efdedc2c45ffad28588bef7b30b117eefa21622efdedbac45febd67588bfb7ceeb117faf595622f7ded2ac45ff3e55588bfd7ac6b117fe78cd622efdf5daa45ff3e55548bdf7d54a917def4a5522ffd6942a45f7bd98548bf77d10a9177ef6dd522fede5baa45fdbe77548bbf7b6ca917def659522ff5f332a45ff9e33548bdf7d5429177ef6e0522fbdecc0a45fbbe88148bbf7b6c2917def658522ff5f330a45dfbdb3148bff3c6629177ef6c4522efdf5da645dfbdb84c8bff5a509917eefa21322efdedba645ff9d374c8bfb7cee99177ef6d9322ff5f332645ff3e554c8bdf7d551117feb4a2222fbdecc4445fbbe88888bff5a4d1117def65a222ff5f334445ffad25888bdf7b4b1117fcf956222ffd691c445ff9e33888bff59711117feba22222ffd6c3c445ffad86888bff5aed1117feb2d6222ffd642c445ffad75888bff5acb1117feb956222ffd6c1c445ffad73888bff5ac711177efaed812fddf443025f7bd89604bfb7ceec097bef695812ff9f2ab025ff9e33604bf77b04c097def649812ffd7113025dfbebb5c4bbf7b70b897f6f5e1712ffda8c2e25f7bd985c4bf77d10b897bef695712ff9f2aae25ff9e335c4bfb7ae4b897def649712ffd7112e25dfbebb544bfe7caaa897fed461512fbdecc2a25fbbe88544bbf7b6ea897fed45d512fedf3baa25ff9e33544bfe7aa4a897def649512ffd7112a25ffb688844bff6b0f0897fed216112ffdabac225ffb655844bff6b070897fed5ce112ffdac14225ffb482844bff6ae50897fed54a112ffda294225ffb532844bff6c4508973ff6e2aa2a7fedbd5454ffdb6aa8a9ffb6b55153ff6caaa2b3ff55352567fda96a0a9ffd76d4159ff6e5a82b77e5b35056bfda82a0acffb52541577f6dca82b3fec5330567feaa660a9ff9754415aff62a882b9fec4d10567fda9a20ad7f9754415affaaa882b9fed4d1057bf4b1a20acffb52d3957fb2c9a) else (if i < 7 then 0x113bbfac9c2277fd633844eefeb25089dff988a113abff5db2e6d7febb64cdcffb50c99b9ff69d9337aff3bb266d7fdb95ccdebfaf2b99bbf76a23337def444666efdda78ccdefbb2f199bf779de33373fed4aa46d7fdb9148dcffb52291b7ef6d052373fed4c446efeda8888df7dd11111bbfb69e2237bf6cbc446fdee77888dfedcab111bdfb64e2237fe719c446cffdb6aa8c9ffb6755193ff6caaa32bff5db52667feaa6a4ccffb52d3193ffaeda6333ff5532c667fda7658c9ffb74bb199ff6a5763377f554cc676fda9998cddfb4f3319dbf65e6633e7f3bccc65fbebb690cdf7d54d219bef699a433f5f33348667fda968ccdf7b48d1995ffaed9332bfedd326667feaa64cccffb4cc999dbf99993327fe5d2c666fdeaa8cccefbb531999bf769a3333beecb46667ede668cccff3b4919999ff6a5a2337ded234466feda2288caffb7251199ff6a4a232f7edb14465fbdb4288cdf7b4851195ffaed9232bfedd324667feaa648cebfceec9199ff6999233b7f33324677bda4648cefbc66c9193ff2e98232bfedcb04667fda9608c9ffb7441195ff6e482333fed490465ff5b1208c9ff974b1199ff6a562327fe5d26464ffcba888cefda5311199ff6a622337f65d44466feeaa888cefdb531119dfb6622233df74444466feda7888cfbdcef1119bfb69a2233bf6cb44467eee66888cfed96b1119feb6922233bf6c9c4467fce33888ccffd54c899cffa219133aff3bb22677de33644cefdc44c8995ff6e58133bfa8cb02667fda9604cbfed76c099efda218133dfa4530266ff6aa604cefeb72c099dfd6258133bfad4b02677f597604cfbeceec099fbd2d98133f7b3330267f74b5604cefeb2ac099fed6918133bfac9b0267fd633604cf7eb04c099dfd6498133fbaa930267fe622604cefea32b8999ff6a57132ffb5dae266ff6aa5c4cefeb52b8997fd6e17133efabc2e2677f5985c4cf7ed10b899f7d5d97133bfacb2e267ef6665c4cfeeacab899fed6917133bfac9ae267fd6335c4cefeb24b899fdd5497133ff3112e266ff6aa844cefeb530899dfd6621133dfb4442266ff5a7844cefeb2f0899f7d9de1133bfacac2267f7655844cff6b490899dfd64e1133feb19c22677f592844cfeeaa50899ff988a11337df555105fbbcb5a20bf7796544177efaed872fddf4430e5efbeaa61cbef7b12c397f6fa22772fedf3bb0c5dfbdb85d8bfb7af0bb17def661762fddf442ec5febd87998bdf7aecd297befaa8852efded990a5dfbdb2214bbf7b624297befaa9752fedebc2ea5f7bd985d4bf77d10ba97def659752ff5f332ea5dfbebb594bef7b30b297eefa21652efdedbaca5febd67594bfb7ceeb297befaaa552fbdecc4aa5fbbe88954bfe7aad2a97def65a552ff5f334aa5ff3cb8954bfe7d112a97fcf61e552ff9ec34aa5ff3d769 else (if i < 8 then 0x8ccfefbb2f199ff779de333ff6e534667fede668ccfefbb2b199ffd7956333f3fed4b447eefca6688fdfdb44511f5ff6e4a23f3fed49447eefca6288faffd76c91f5ff6e9923f3ff553247f3fe88648febfceec91fdbf299923fb7f333247f77e55648fefbc66c91fdfd2c5923ebfedcb047f3fd89608fcffb52c11f6ffaed823fdf6153047ebfeaa608fe7fb72c11fcff4a5823f9fed4b047f3fd97608ff3fceec11febf299823fd7f333047f3fd95608ff6fcaac11fef78cd823fdfa58b047d7fdb95c8f9ff974b11f9ff6a5623fdf6942c47cffcba548fcffb52a91fefb4a1523e7fedd0a47d7fdb9148fcffb52291f6ff6e0523ef7edb0a47dfbdb4148fbfeb62291f3ff2e9323fdf6942647cffcba888fefda53111f9ff6a6223fdf6944447efecba888fdfdd55111fdfb6a6223fdf65c4447f7ed98888ff7dd11111fdfb65e223fef73bc447feeca6888ffddccd111fdfb656223ffb72ac447f7ed93888fff9c67111f9ffaa9913f9ff443227f5fe77644feefcaac89fdf78cd913f9fec13227f7ee22644fdfed55089fdfd6a6113fbfacc4227fbf688844fefeb2f089ff7d9de113fbfacac227ff7655844fefeb27089fff58ce113fbfac94227fbf582844fffcc45089f3ff6e2aa3a7fedb55474ffdb5aa8e9ffb67551d3ff6caaa3a7ff5db5076efcb66a0ed7fb50541d5ff6e4a83abff5db30767fd8a660ecffd54cc1d3ff2ea883b5fec5510773fd89a20ecffb53441daff2ea883b5ff5551075dfebb61cef3fd10c39de7f229873b6ff5530e775fd8961cefbe962c39d9ffaa9963b3fed4b0c76dfeaa5d8ebbfb70bb1db7f6a1763bafecc2ec779fe885d8eddfd55331dbbf6a2663bb7ecc4cc77afe88998ef9fb0f331d5ffaed953b3ff5532a767fda8654ee7fd10ca9dd7f61d953bafebb32a776fe66654e9ff974b29df3f59d653b7bf554aa76f7da8954eeefb312a9dedfa22553bebec3caa7777d96954efafaed2a9df9f99a553abff5db26767feaa64cecffb50c99dcffa21933bafec3b26775fd7664ceedfcccc99dddf955933a7fe5d2c676fdeaa8ccedfbb51199ddf7662333bdef4446677ddd878cceefbb2d199df775da333bf6f33466777dd958ccefebcab199d5ffaed923b3ff55324767fda8648ee7fd10c91dd7f61d923bafebb324776fe66648eeefcaac91ddf78cd923a7fe5d30476bfd8a608eaffb72c11de7f61d823a7fe5d2c477cfd67588e9ff974a91d5ff6e5523a7fe5d26476feeaa888edfdb51111ddfb662223bdf74444477ded87888eefdb2d111df7b5da223bf7733444777ed95888efedcab111ddfb64e223bfe719c44767feaa644ecffb50c89dcffa21913bafec3b227777e55644eefbc66c89ddfb889913abfedcb02767fda9604edfeb51089ddfd662113bdfb4442277df587844eefeb2b089dfdd956 else 0xa1147fbb2ac228ffd5738451efeb2508a3ff960a1147ff3114228e7feaaa210e7f96b4421cff2ca8842bff5db0e873fe8861d0cff974c3a19ffaa98743aff444ee875fe776190affb70bb21d7f5e176439ff442ec876fd879990cffd5442a15ff6cc8542bfed910a857fdb12150cffd552aa1cffa225543b7f334aa8777cb89550eefd112aa1ddf61e5543bbec34aa8777d769550eef9652aa15ffaed83439ff44306875fe7760d0edfcccc1a1ddf9558342bff5dae6857fdb85cd0ebfaf0b9a1cffa217343b7f332e68777e555cd0affd76b1a15ff6e16343bee9c2c6873fe8858d0affb6eb1a1d7f9dd6343bbf2aac6877de888cd0efbb0f19a1df761a3343beebb466877dc858cd0efbcab19a15ffaed82439ff44304867fdba6090cffd54c121cff61d8243aff3bb04876fe666090eefcaac121cff60d8243bef19b04867feaa2090affb6a4121ddf9548242bfed9904877de332090affb6241215ffaed6242bfedc2c4877ed285890e7fd10b121dbf59d6243aff3bac48777e555890edfac6b121df78cd62433ff550a4857fdb81490e7fd1029215ff6d85243b7f330a4857fdb31490efbc6629215ff6c45242bff5da64857fdb84c90efda509921cffa213243bee9ba64875fe774c90affb6c9921dbf9993243bbf2aa64867feaa8890efda511121cffa222243bf693444876fe668890eefcab1121dfb48e2243bef19c44877ecb88890efdd111121dfb61e2243bf6c3444877ed768890efd96b1121dfb2162243bf72ac44877ed838890efdae71121dfb58e2243bfb44422877f5878450efe90b08a1dfd9561143bfac1c22877f5738450efeb0508a1dfd20a1143bfa29422877f5328450efec4508a17bf6daaa3e7fedbd547cffdb6aa8fddfb6d551f3ff6d6aa3e7fed9d547cffdb2aa8faffd76d49f9ffaa9a93fb7e5b3527d7febb660fcffd54cc1faffaaa883f9fed4d107e7fda969cfaffd76cb9f5ff6e9973f3fe5d32e7e7feaa65cfe7fd10cb9f5ff6e5873f9fec4b0e7e7fda961cfdbfd553b9fd7f6a6773fafecc4ee7f9fe889dcfcffb52d31fbbfaa8a63fb7ed494c7eefda7298fedfb2e531ff3f9dca63f3fed4aec7defcba998fddfd55331fdbf6a6663fb7ecbccc7fcfe77998fcffb52d29fbbf299a53f7bed294a7d7fdb9294fcffb52529fbbf298a53efdeda14a7d7febb654faffb74ca9f9ffaa9953f9ff4432a7f5fe77654fedf94cca9fdbf999953e7fe5d4aa7f77d59954fcffb532a9fbdf2ea553f7bf554aa7f77da9954feefb312a9fedfa22553fbbecbcaa7fd7e77954ffcf94d2a9ff9f99a553ffba58caa7e7fda968cfddf94cd19f5ffaed933ebfedd3267e7feaa64cfebfceec99fdbf299933fb7f333267f3fd8960cf9ff974b99f5ff6e5733fafebcae67cffcba58cfdfbd55199fdf76a6333fbeecc4667fbde88)))) else (if i < 14 then (if i < 11 then (if i < 10 then 0xaa2149ffd76d3a9affa21a7533ff5532ea67fda865d4e7fd10cba93ff6e987527fe5d30ea6dfeaa9dd4dbfb513ba9d7f6627753cff444eea6efeaa5d94f9faf0bb29dbf6617653d7f442eca6f7da52954affb7252a97ef6d0a5527fe5d4aaa67fda99554def9752aa9bdfaaa55537bed44aaa777d989554f6fd112aa9bdf69e5553ebf3bcaaa7e7d7695549ff974b9a97bfaed635377f552c6a76fd9858d4f5fd10b1a97bf6dd6353b7ecbac6a7cfe7758d4fcfcaab1a9fbb2c963537ef55466a6fdda88cd4efbb3119a9ef7a2233537eed3c66a77dd978cd4fbbcef19a9fb75da3353faf2ac66a57febb6494cffd54c9299ff6a192539ff44324a777e556494edfac6c929df78cd9252bfedcb04a77ed296094bfdd76c129bfbaa98253bf6dcb04a7bed876094efdb2ec129f7b9dd8253f76bb304a7f6e556094fddac6c129ff38cd82537f6d4444a77ed988894f7dd111129fdb9562253f76b1c44a7fce338894dfed5508a9bfd6a21153bfacc422a7bf6888454dfeb4f08a9dfd65e1153efb3bc22a7ef5768454feecab08a9fbd58e1153feb19c22a77f5928454ffcb0508a9ff988a11527fedc5548cffdb7aa919ffb6d55233ff6d6aa467fed8d548e7feaa6a51cffb52d4233ffaeda8473fedcb508ebfda82a11cffb5254239ffaa998467fe5d5108f3fd89a211d7f9754423affaaa88479fed4d108fbecb2a211cffb52d3a39ffaa997479ff4432e8cffcba61d1dbfd553ba3d7f6a67747afecc4ee8f9fe889dd1cffb52d3233ffaeda6473fecc34c8ebfe886991cffb2ed323b7f9dda6473ff5532c8e7fda86591e7fd10cb23d7f9dd964777f554cc8f6fda99991ddfb513323dbf6626647d7f444cc8f6fd979991f9fcef33239ff6a5a5477bed294a8e7fda929519ffb7442a377f6dc8546f7edb10a8dfddb32151bfdb6442a37fd6c48546ffcd810a8cffcba9551def9752aa3bdfaaa5547bbed4caa8f77d989551f6fd112aa3f5f9de55477bed34aa8f77d969551fcfccd2aa37f7aed73477ef552e68f7dda95cd1fbbaf0b9a3df76617347def442e68f7dd965cd1fdbcccb9a3fd795573473ff553248e7fda86491e7fd10c9239ff6999247b7f333248f77e556491efda52c1237fbaed8247df7443048fbec8a6091dfdd54c123dfb6e58247bf6c4b048f7eda96091f7db0ec123dfb65d8247ef73bb048efeda66091efdb2cc123fbb9998247fb72ab048ffcd736091efdb531123bfb6a22247bf6cc4448fbee888891dfdb4d1123dfb65a2247f77334448ff6e558891cffb52d0a3bfd684a1473fed49428dff9b028519ffb7440a377f6dc8146feed99028dfedb220519ffb7428a37f76cc51467fe5d4228eff4ba8451dfed5508a3dfd6a611477fad44228f7f5988451f7ed1108a3dfd65e1147efb3bc228eff5a68451efeb2d08a3fbd99 else 0xd61177bfa42c22ef7f655845defe96508bbdfd20a1177bfa29422ef7f622845d9ffb7155353ff6deaa6b77ec3554d4ffdb5aa9a9ffb6555353ff6c6aa6b5ff55510d4ffebb69dacffd54cbb5cffa21976b6ff554eed79fe889ddadefb4a52b53ff2ea556bb7ecb4aad6f7cba955adefd552ab5edfa22556bbbecbcaad7d7e77955adfdb4451353ff6e8526b3fed48a4d5efdb6149aedfb2c29353ff2ea226b3fed4c44d76fd96889adfd9751135bfbaaa226bdf744444d6feda7889aefdb2f1135f7b9de226bfb72ac44d6ff6aa845af7ed1108b5bfd69e116bbfacbc22d7df677845afeecab08b5ff988a116abfedb950bd7fdb52a17affb62542f9ffaaa885f9fe5d510bf3fcb5a217e7f963442fd7f2a2775faff444eebe7feaa5d97e7fd10bb2f5ff6e0a55f9ff4414abd7fdb62957edfccc52af5ff6c4a55f3ff5510abd7fdb32157affb6442af5ff6c4855f3ff554aabf3fe889557edfccd2aafddf2ea555fbbe5c4aabf77ca89557eefd112aafddf5da555fbbe58caabd7febb5cd7e7fd10b9afdbf999735fbbf2aae6bd7febb58d7e7fd10b1af5ff6dd635faff3bac6bf77e5558d7efbd1119afdf75da335fbee42c66bf7de558cd7efdd11112fdfb216225fbf72ac44bf7ed638897affb7050afcffa20a15ebfedb942bf5fe772857affb6a50afddf954a15f3ff55102bd7fdb72057ebfcee40af5ff6d4815fbbf2a902bd7fdb32057efbc6640af5ff6c8815fbf711102be7feaa1457affb7028afcffa20515ebfed98a2bf7de331457affb6428afdfb888515f3ff55422bf3fe888457ebfcef08afddf956115fbef19c22bf7ee228457efe97508afdfd2e2115fbfa54422bf7f6888457efeaed08afdfd2d6115fbfa52c22bf7f4858457efecab08afdfd5ce115fbfab1c22bcffdb6aa969ffb67552d3ff6c6aa5abff5db52b67feaa6a56efb966d4ad9ff6a5a65b3ff5532cb67fda95d96ddfd55332ddbf6a6665bb7ecbcccb7cfe779996cffb52d1ad3ff2e9635b7ef55466b77dda98cd6efbb2d19adfb799a335abff5db24b67feaa6496edfcccc92ddf78cd925b7f755444b77eda98896efdb31112defba22225bbf6cb444b7eee668896ff9c67112d9ff6a5a15b7fad0942b57fdb92856cffb5250ad77f6dca15afdeda142b4ffdba1456affb7228ad9ff6a4515afdeda0a2b5fedb214569ff97508ad9ff6a6115b7fa5d422b6ff6aa8456efeb5308adefd2e2115bbfacc422b7bf6888456efeb2f08adf7d9de115bf7b33422b7f76558456ffac6708addfd64a115bff311422b67fda9a215f5fd11332bef7a223357f6f33466aff5e558cd5affb7240ab9ff6a48156fdeda102ae7fda98455f7ed1108abfbd99a1157feb19c22acffdb8aa949ffb6f55293ff6d6aa527fed9d54a4ffdb1aa949ffd76d4295ffaed98533ff55330a6bfea) else (if i < 12 then 0x885c49ffeb0ab893ffd5957127ffac1ae24fff5635c49ffeaa6b893dff5655127bfecc2a24ffbd545449effb26a893fefa214127fdec3a824ffbc855049ff7aeaa093fef9554127fdec1a824ffbd735049ff7aa6a093fef6094127fdea92824ffbd325049effb309893dff65d3127bfecaa624ffbd544c49ffe9709893ffd2a13127ffb442624fff5874c49ffeb0c9893ffd5d93127ffa5aa624fff4a54c49ffe90a9893ffd5d53127ffab2a624fff6554c49ffeb049893ffd5893127ffaa92624fff9766882fff36cc105ffe5d9820bffcd8b0417ff9a85c82fff34cb905ffe619720bffd5dac417ff9ba5882fff254b105ffe6e1620bffc942c417ff9a85882fff36eb105ffe69d620bffcc3ac417ff9b55882fff16ab105ffe6c5620bffcc344417ff9876842fff30cd085ffe5d9a10bffcb934217ff9626842fff576c085ffe6e9810bffcc530217ff91a6042fff36ec085ffe61d810bffcd3b0217ff9b66042fff34cc085ffe5d9810bffcdab0217ff8b56042fff34ac085ffe6c9810bffc5930217ff9826042fff344c085ffe5c9810bffcb130217ffa226042fff2e44085ffe548810bffcdc2e217ff9185c42fff510b885ffe6d9710bffcc32e217ff9655c42fff364b885ffe609710bffcb12e217ff9525c42fff30eb085ffe5d5610bffcc12c217ff9725842fff2a4b085ffe889610bffcbb2a217ff9b25442fff2a4a885ffe209510bffcb92a217ff9625442fff444a885ffe608510bffc410a217ffa221442fff5769085ffe6e9210bffc9524217ff91a4842fff3709085ffe2e1210bffc9424217ff9184842fff3509085ffea21210bffcdba4217ff9174842fff34e9085ffe61d210bffcdb24217ff9264842fff34c9085ffe619210bffcbb24217ff9b54842fff16a9085ffe495210bffc8aa4217ff9a54842fff2ea9085ffe595210bffcc284217ffa888442fff30f0885ffe616110bffcc142217ff8828442fff2e50885ffe54a110bffd1142215ffdb52856bffd76c119bff2e982337ff55304677fdb9608ceffa52c119fef6918233ff69426467fbd865c8bff7b06b897fef609512fbfec4b0e56ffda7618adffb4ac115bffaa98527fee9c2a64f7fd856489ffeb0cb893fef6154127ffac2a624fff9526042fff304a885ffe615210b3ff554ab4f3fe889569eef9652ad3df795633a73ff550a54d7fdb814a9e7fd1029535ff6cc52a7bef198a54d7fdb114a9cffd551153cffa2222a7bbf2ac454f7de3388a9efd96b1153dfb95622a7bfb2ac234f7f4528469efec4508d3efba22229ffe719c453fbf6888467feecab08cfff58ce119fff3114233e7feaa5d9dcffd5440bb5ff6dc8177aff3b902ed7fdb2205dcffd5428bb5ff6c851773ff55042ed7fdb5085dcffd5508bbd7f9de1177bfa5c422ef7f688845defeaed08bbdfd2 else (if i < 13 then 0x6999527bfebb32a4f7fda96149dffd544293dff6a48526ffed990a4dffdb22149dffd54ba93dff6a57526ffedc2ea4fdfd785d49dffb50ba93dff66175277fed32ea4f7fd965d49bffd76b293bffaa96527bfeacaca4f7fda95949bffb70b293fbf5a165277fed42ca4f7fd985949bffb6eb293fbf59d65277fed3aca4effeaa9549effb532a93bff6a25527bfecc4aa4effda69549effb2d2a93fef5695427fdf552a84ffbda85509ff7950aa13fefa215427fded3aa84ffbd875509ff7aacaa13fef6995427fdec32a84ffbd765509dff950d193dff661a327bfecbb464f7fd9668c9dff94ad193dff655a327fdeaa3464effcb868c9dffd10d193bff61da3277fec33464effd7668c9dff96ad193bff215a3277febab464effd6568c9dffcaad193dffaa99327bfed33264f7fd7664c9effb4ac993dff2959327bfec2b264f7fc8564c9effaeac993dff5959327bff2ab264dffebb60c9dffb74c193bff62983277ff553064f7fdb960c9effb12c193dff6a583277fed3b064f7fd9760c9dffb4cc193bff6958327bfecab064ffbd5460c9bffd76b993bffaa97326ffedc2e64fdfd785cc9dffb50b993dff66173277fed32e64f7fd965cc9dffb4ab993dff6557327fdeaa2e64dffebb58c9dff974b193bffaa96326ffedc2c64fefd6858c9ffba70b193bff6a16327bfecc2c64dffdb758c9dffb4eb193dff65d63277fed2ac64f7fd9558c9ff7aa8b1937ffaed53277ff552a64f7fdb954c9effab2a993dff6a55326ffedc2a64effda854c9effb30a9937ff6dd5327fee9baa64effda754c9bffb6ca993bff6995327bfecb2a64ffbd5454c9effd10c913dff6199227bfe42b244f7fd656489effcaac913dff60d9227bfea9b244dffebb6089dffb14c113bffaa98227bfec4b044effda66089dffb4ac113dff6558227fdeaa3044fbfd836089dffb46c113ffd2c58226ffedc2c44ffed285889dffb50b113dff6616227f7eb2ac44effda55889effb2ab113fef5516227f7eb1ac44effda35889ffdb50b113ffb61d6227ff6d2ac44ffed855889ffdaeab113ffb9556227ff6d1ac44ffed835889ffdae6b113ffb54d6226fff5daa44effeaa5489effab2a9137ff6e15227ff6942a44effda85489effb30a9137ff6d95227ff6932a44effda65489effb2ca913fef5515227fbea9aa44effda35489bffd769913bffaa93226ffedc2644ffed284c89dffb509913dff6613226ffedb2644ffed264c89effb2c99137ff6d532277fed2a644f7fd954c89ff7aa89913dffa219127bfec3b224f7fd856449eff90ac893dff5d59127bff2ab224f7fd836449effae6c893dff54d9127bfec13224f7fd526449effa64c893dff6258127bfecbb024f7fd956049ff7aa8c093dff64d8127efebc2e24f7fd985c49effb2ab893fef5517127bfec9ae24fff6 else 0xda9954adffb512a95dff662552b7fed34aa577fd96954aff7ab4aa15fef6a1542bfdf442a857fbda7550aff7b0eaa15fef559542bfded32a857fbd86550aff7aecaa15ff7aa9632bfeed42c657fdda758caffbb0eb195ff72d5632bfeed2ac657fdca558caffbaeab195ff7955632bfee592c656ffca8688aeffb30d115dff65da22bbfecb34456ffca5688aeffb2ad115fef551a22bfeeb1b4455ffdb8288abffb6c51157ff6d4a22bfeeb1944577fe88648aeffb0ec915dff5d9922bbfe42b24577fd65648aeffcaac9157ffaed822b7fedd30456ffcba608adffb14c115bffaa9822bbfec4b0457bfd87608adffb4ec115dff65d822b7fed3304577fd95608aff7aa8c115ff758d822bffad8b0455ffdb5208aeffb2a4115fef550822b7ff552e455ffdb85c8aeffb30b915bff699722bbfecb2e456ffda55c8aeffb2ab915fef551722bfeeb1ae455ffebb588adffd54b1157ff6e1622bff6942c456ffda8588aeffb30b1157ff6dd622bf7eb3ac456ffda7588aeffb2eb115fbf595622b7fed2ac4577fd95588aff7aa8b1157ffaed522bff6152a456ffeaa548aeffab2a915dff6a5522bff6942a456ffda8548aeffb30a9157ff6dd522befe5baa455ffdb6548adffb4ca915dff659522bfdeaa2a457fdd63548abffb702915dff660522affedb0a4577fd96148affbac62915ff7aed322bfee5d26457fddb84c8affb9709915ff74a1322bfee5426457fde884c8affbb6e9915ff761d322bfeedb26457fdd264c8affbaec9915ff76d5322bfee5aa6457fdd254c8affb94a9915ff7215322bfeebaa6457fdd654c8affbcaa9915dff662222bbfecb444577fd95888aff7aa91115ff758e222bbff44322577fd87644aeff90ac895dff955912bbfec1322577fd52644aeffb12c095dff65d812bbfecab0257fbd54604affeb0ec095ffd5d9812bffa5ab0257ff4a5604affeaeac095ffd595812bffb2ab0257ff582604affeae4c095ffd589812bffaa930257dfd785c4aeffb30b895dff655712bfdeaa2e2577fd59544aeffb30a895dff65d512bfdeaa2a257fbe88504aff7b0ea095fef215412bfdebaa8257fbe55504aff7b04a095fef549412bbfe5c3524f7fcb56a49dff96ad4137ff6d4a826ffed99504f7fcba6609effb14cc13dffaa99827bfe5ab304effeaaa209effb534413dff661a7277ff4434e4f7fda865c9effd10cb937ffaed87277fe5d30e4effd8a61c9dffd54c393dff6258727bfed4b0e4f7fd986989dffb0ed313bffaa98627bfed4b0c4effda76189effb2ec3137ff6e17627efebc2ec4effda85d89effb30bb13dff661a527bfecb34a4effd876949dffb0cd293bff5d9a526ffedc14a4effda82949effb3052937ff6cca527bfead32a4f7feaa6549effb50ca93dff2a19527bff4432a4f7fda76549effb0eca93dff))) else (if i < 16 then (if i < 15 then 0xf64e2233bff44322677fd87644ceffb06c899dff5cd9133bfec1322677fd32644ceffb12c099dff65d8133bfecab02677fd93604cffeb0ec099ffd5d98133ffac1b0267ff573604cffeac6c099ffd6098133ffab130267ff532604cfbfaf0b899ffda217133ffac1ae267ff5635c4cffeb04b899ffd5897133ffa992e267fbebb61cbff7b6cc397fef6d5872ffded9b0e5ffbdb261cbff7b62c397fefa21752ffdec32ea5ffbd87594bff7b0d2a97fef6dd832ffdec3b065ffbdb660cbff7aecc197fef6d5832ffdeb2b065ffbe5560cbff7b64c197fef6c5832ffdf5dae65ffbdb85ccbff7970b997fefa21732ffdedb2e65ffbd865ccbff7b6ab997fef595732ffded92e65ffbdb15ccbff7b0eb197fef2d5632ffdebaac65ffbe5558cbff7964b197fefaed822ffdedbb045ffbd87608bff7b6cc117fef5d9822ffdedab045ffbcb5608bff7acac117fef955822ffded9b045ffbd83608bff7ae6c117fef58d822ffded8b045ffbe885c8bff7acab917fef58d722ffde942c45ffbd87588bff7aeab117fef955622ffdec1ac45ffbd73588bff7d76a917fef6e1522ffde5c2a45ffbd28548bff7d10a917fef6dd522ffdec3aa45ffbdb6548bff7aaca917fef499522ffdec32a45ffbd76548bff7b66a917fef60d522ffdeb9aa45ffbd63548bff7b62a917fef618522ffdec18a45ffbd63148bff7d769917fef6e1322ffde5c2645ffbd284c8bff7d109917fef6dd322ffdec3a645ffbdb64c8bff7a4c9917fef5d9322ffdedaa645ffbcb54c8bff7a4a9917fef215322ffdebaa645ffbd654c8bff7caa9917fef6c5322ffdf444445ffbd86888bff790b1117fef596222ffdf2ac445ffbd83888bff7ac71117fef61d812ffdebab025ffbe55604bff7b06c097fef5cd812ffdec13025ffbd52604bff7a64c097fefa21712ffdec12e25ffbd525c4bff7a64b897fefa21512ffdec3aa25ffbd83544bff7ae6a897fef549512ffde992a25effcb56a0abffb6e54157ff6d4a82affed9150577fd8a660adffd554415bff2a1a72bbfecc34e56ffcb869cadffd10d395dff6a1972bbff4432e55ffebb61cadff974c395bff629872befebd30e56ffeaa61caeffb30d315dff65da62b7fec3b4c56ffcb5698aeffb4ecb15bffaa9862b7ff552ec577fda95d8abffb70bb15f7f5e1762b7fed42ec577fd985d8aeffb30d295dff65da52bbfecb34a56ffd76694abffb705295bff6a0a52affedb14a56ffda6294abffb645295dff569952bbfed432a577fe88654aeffb4eca95dff61d952bbfed332a577fd76654adffd5442957ff6c8852b7ff552ea577fda95d4afbfaf0ba95dff661752b7fed32ea577fd965d4abffd76b295bffaa9652bbfeacaca577fda9594adffb50b295dff661652affedbaca57efd67594adffb4eb295dff65d652b7ff554aa577f else 0xfebb608fdffd54c11fdff4a5823fdfec3b047f7fd97608feffb2ac11feff60d823fdff5db047fbfcba608ff7fb6ec11feff6d9823fdfebb3047fbfdb5608ff7f96ac11feff295823fdff2ab047fbfdb3608ff7fae6c11feff58d823f7ff552e47f7fd985c8ffdf94cb91fdff4a5623fdfe942c47f7fd97588feffb2ab11fbffaa9523fbfed4aa47fbfd28548feffb30a91ffbf299523fbfec9aa47dffdb8148fbffb66291fdff64c523efff5da647effdba4c8fdffd54991fdff6e5323fbfe94a647f7fda94c8fbffb70991fffb4a1323fdfe942647f7fd984c8fbffb6e991fff74dd323fbfecba647fefca64c8feffb2a991fdff662223fbfecac447f7fd93888feffb0ec89fdff955913fbfec1b227f7fd73644feffb04c89fdff549913fbfe993227dffdb32a0eeffb14cc1dbffaaa883bbfecc34c76ffeaa618eeffd10ca9dbffaa9653b7fe54346777fd9868ceeffb2cd19ddff6a1933bbff44326777fda664ceeffacac99d7ffaed833b7fedd30676ffd8a60cedffd54c19ddff6e5833bbfec4b0677dfd8760cefbfaecc19ddff655833afff5dac676ffcba58cedffd54b19d7ff6e1633bfee9c2c676ffda858ceeffb30b19df7f61d633bbfecaac6777fd98688eeffb26d11ddffa21923bbfec3324777fd65648eeffb06c91ddff58d923afff5db0476ffdba608edff974c11dbff629823b7ff55304777fd89608efbfb6ec11df7f61d823befebb304777fd95608ef7fb06c11d7ff6e1623bff6942c476ffda8588eeffb30b11df7f61d623bf7eb2ac4777fd95588efdfac6b11ddff64d623bff6942a4777fd98548ebffb6ca91ddff659523bbfec9aa475ffebb4c8edffb74991dbffaa9323affedc26477fed284c8edffb50991ddff661323befec3a6475ffdb64c8eeffb2c991df7f5d9323bbfecaa64777fe88644eeffb06c89ddff609913bbfea9322777fd32644eeffb12c09df7f61d813bbfecab02777fd93604ebffd76c19bdff6e58337bfecbb066dffebb5ccdbffb70b99bf7f5e173377fed42e66effda85c8dbffd76a91b7ff6dd5237efe5baa46f7fd93548dbffb66291bdff64e2237bfec3b5266ffeaa5d8ceffb52bb19fef61da433fdebb348677fd9668cceffaecc9997ffaed63337fe5d2c666ffeaa58cceffb52b1997ff6dd63337fed3ac6677fd9758ccff7b48b199dff659a233bfec9b4465ffdb8288cbffb665119dff5d99233bfeb9b24677fd63648cdffb74c119dff6a58233bfec9b0465ffdb3208ceffb2641197ffaed62337ff552c4677fd29588cffda50b119dff6616233f7eb3ac466ffda7588cfdfac6b119dff64d6232fff5da6466ffdba4c8cdffd549919dff6e53233bfe94a64677fda94c8cbffb709919dff6613233fee9ba6466ffda74c8cbffb6c9919dff6593233fded2264677fd98888ceffb2d1119df) else (if i < 17 then 0xff69da5477fed334a8f7fd966951bffb7052a3bff6a0a547bfecc14a8dffdb62951dffb4c52a3dff658a546ffed894a8dffdba2151dffd5442a37ff6c88546ffed890a8effeaa9551effb532aa3dff66255477fed34aa8f7fd969551ffbb50b9a3ff7a217347feed32e68ffdda55cd1effd10c923dff2159247bff2ab248dffebb6091dffd54c123dff62582477fed33048f7fd966091ffdd76c123ffbaa98247ff6dbb048ffed876091ffdb4ec123ffb6d98247ff6d33048ffed766091ffdb6ac123ffb2d58247ff6d2b048ffeca56091ffdcaac123ffb6c58247ff658b048dffebb5891dffd54b123ffb4a162477fed42c48f7fd985891bffd76d0a3bffaa9a1477fed43428effca86851effb30d0a3bff69da147bfecbb428effda66851effb2cd0a3bff695a1477fe52b428ffdd736851ffdb04d0a37ff6e0a1477fed41428f7fd982851bffb6a50a3bff694a147bfeca9428ffbd542851ffdb0450a37ff6e881477ff551028dffdb72051effb2e40a37ff6d48147feeb99028dffdb22051bffb7428a3bffaa85146ffedc0a28effda81451effb3028a37ff6c85147ff6c10a28effeaa8451dffb5108a3dff6621147bfecbc228ffdd738451ffdb0508a3dffaed8743bfedb30e877fdb561d0effb66c3a1dff6c98743bfed8b0e877fd869550effb6ec1a1dff61d8343bfedb306877fd7660d0effb6ac1a1dff9558343bfed9306877fdb160d0effd76b9a1dff6e17343bfe5c2e6877fe885cd0effb6cb9a1dff6d57343bfed92e6877fdb15cd0effb0eb1a1dff2d56343bff2aac6877fcb258d0effd76c121dff6dd8243bfec3b04877fdb66090effaecc121dff6d58243bfe5ab04877fe556090effb66c121dff60d8243bfeb9b04877fd636090effb62c121dff4a16243bfec3ac4877fe555890effb06b121dff5cd6243bfec30a4877fd831490effac62921dffaed3243bfedc264877fcb84c90effa509921dffa213243bfedba64877fd874c90effb6c9921dff4993243bfebb264877fdb54c90eff96a9921dff2153243bff2aa64877fdb14c90effd111121dff61a2243bfe42c44877fe558890effb071121dff58e2243bfe5d32e7f7feaa65cfbffd76c39fbffaa9873fbfecbb4c7f7fd97694fbffb66529f7ff6c8a53fbfead32a7f7feaa654feffb4eca9fdff61d953fbfed332a7f7fd76654fdffd552a9ffbf29a553fbfecbb467effca568cfeffb2ad19fdffaa9933fbfed3b267f7fda664cfeffaecc99fbffaa9833fbfecbb067f7fd9560cfbffd76b99fbffaa9733effedc2e67fdfd785ccffdf94cb99fdff655733fbfecbac67f7fd9558cfeffb2ed11fbff295a23fbfecab447f7fd93688fbffb6a511fdff654a23effed99447f7fd93288feffb0ec91fdff5d9923fbfe52b247f7fe55648feffb06c91fdff5cd923fbfeb1b247df else (if i < 18 then 0x580125e08fe0471822f4112e08710425820940ffe07ce03d401ddc0e8c0746039001be80da806b903498195c0c7805ea02cc015c80a98053c0275012b808e4042001fd00ea006d80330017a00ae004f8024b01180082803c801b300c100544026c0105006f802e401100057001880003bff2ac454f7fe88845deff90508bbdff88a1176ffedbd54d5ffdb5aa9abffb655535bff6deaa6b7fedad54d6ffdb2aa9aeffd54cbb5dff6a1976bbfecbb4ad6ffeaa295abffb7052b5bff6a0a56bbfecc14ad7efd86295affbb0652b57ff6c8a56affed894ad5ffcba955adffd552ab5dff662556bbfecbb44d6ffca5689adffd5451357ff6e0a26b7fed4144d77fd98289afdfb0c51357ff6d4a26b7fed2944d7fdd83289abffb625135bffaa8526affedc0a4d77fd98149abffb6229357ff2ea226b7ff55444d77fd97685adff94ad0b5dffa21735fbfedc2c6bf7fdb758d7effb6ab1afdff955635fbff44142bf7fe888457bffb6d552d7ff6ceaa5affed8d54b6ffdb6aa96dffb67552dbff6c6aa5b7fe58d54b5ffebb6996dffd54d32dbff69da65bbff5532cb77fda76596bffb74bb2dbffaa9765afff5db46b6ffeaa68d6dffb4cd1addff659a35afff5dac6b5ffdba58d6bff974b1adbff2e9635bf7eb52c6b6ffeaa58d6bffb6eb1addff65d635afff5db42b6ffeaa6856dffb4ed0addff65da15bf7e5b342b6ffda66856dffb4ad0adbff68da15b7ff55142b77fd982856bffb6e50adbff69ca15bbfecb942b6ffda52856bffb6650adbff68ca15affedd0a2b6ffeaa1456bffb6628ad7ff6c8515affe5d422b6ffeaa8456effb3108addff65e115affed9902aeffcb56a14eff974cc29dff2d59853bfed432ea6ffcba61d4dffd54c3a97ff6e0a5537fed414aa77fd982954bffb6652a9bffaaa55537fed44aaa77fd989554effb2ed1a9bff295a352fff5dae6a6ffeaa5cd4effb30b9a9fbf61d6353f7e5aac6a7efca558d4fdfcaab1a9dff9559252fff5db04a6ffeaa6094fdfac6c129ffbaed8253ff6dbb04a7fedb56094ffd96ac129ffb2958253ff72ab04a7fedb36094ffdae6c129ffb6c58253bfecad548ffbd54aa91dff9715523bff2d6aa477fea95548effcb1aa91bffd76d423bffaa9a8477ff5db508effdb66a11dffb62d423bff2c5a846ffeda9508f7fd952a11ff7aa854237ff6c4a847bfec53308f7feaa6611dffd554423bff6a1a747bfecc34e8f7fda865d1effd10cba37ffaed8746ffedd30e8effcba61d1dffd54c3a3dff6258746fff5db4c8effeaa6991dffb50d323dff661a6477fed3b4c8f7fd976991dffb0ed323bff2d5a647bff5532c8f7fda86591effb4ecb23dff61d9646ffedd2ec8effeaa5d91effb52bb23f7f5e176477fed42ec8f7fd985d91bffd76d2a3bffaa9a5477fed434a8f7fd986951fbf96ed2a3b else 0x4b3118187d0c3b261b330d198570c26c60ef306f9837cc1466067301597f90bf925f982fa897cd8bdf45ec92f571799cbc985e1b2f0b17794bb685d6d2ea9174dcba385cf62e6817300b9345c742e32170ccb81a5bfd1c6496f5cb7625b962dbd96dacb6485af32d7196b20b5185a662d25968c0b3fe59ce2cce96608b28c58ff2c6c962ccb13058512c1016040afbe57c42bbe95d04ae6256ea2b5715a20acae561b2afa95768ab6855992ab9954dcaa3854f62a6d952d4a91e54742a2c950f8a846540829f694f48a716535a299a14c38952852dd295614968a47e520e28f9946dca322514a2897814f0a1e650a1283d94154a074501427f193ec89f184f50279513be49d7a4ead272d938a89bf24dde26e1814f09b3a4d6c26a8934809a204cc92651931c898ae4c26260592f9497684b9925a912c5895e04aca255792a5094b04a3224f59266492d049422493923ac915e4889242c120708fec47ba23ca11db88e904722237e11b008cf24648230b9176c8b3e454d228e0fe2089d644ba21b990ebc88e6444d220e10f54875e437321a690c9c85d642ba213f10908843841f620dd105f8826e4111206a9023880a43fea1fdc8fe207e6c3f1b1f750fb687d263e411f080f7d47b5c3d931ebc0f4c47a2c053c1e620f24c78ae3c1b1ddf0ee6076fa3b4c1d828eb5075303a5c1d158e3247420053c1ce48e68c7192397d1b7b0e48071b238c91c3b8e1446dec382b1c028dfa86f9e053c029e014f06dec379e1bc18dd486e6e053c1b888dbd86da036aa1b420d9a40a7836431b0e8d7dc6b8c358a1ab78d4f86a0434bb1a450d138680e33ec19dd8cdfc665a32d019448c98c647a321718f88c72c631e3148187b0c29060a4302c18030bed05ec42f26176a0ba085c762e0a16ec8b6a05aee2d4616748b25c58482be815d60adc056942aed155e0aa00547229dc14bf8a48851b6287e141089f3c4f262757138289af84cd8262512fa096e04b0e254012770929c48c0242411e908e5846ca2329116b889e8449221ec10d808578424420e6104f881b8407a200c0fe807e503eb01f320f8607b983d281e790f2f078303b741d680e8b0733c38fa1c620e1e06fa8375c1b880da606c6c36001acf0d390695c346219df0cd1865f4326c19050c6f86310313c18830c2e8602c2fb417a90bab85cc42dea16c40b49859b42c78160b0aed056a42af015470a75052e4291014620a1e0505827e013bf09c704da02684131c035c84b802548125d0910847942352118e08b404508222210f608628427c20f2105308168401c1fc20fbb035c83e541e860f1d077b83b441d400e8507248388c1be40dcc06d3008c01b000d5a0118034d01a1c023006740325813e60c5a061482fe012c00bbc05c582d94167e0b19035c82bcc156e0a7b052a8289013e609c204c882))))) else (if i < 29 then (if i < 24 then (if i < 21 then (if i < 20 then 0xd7bba5c645ed62f5697a68bcf85e69178597942bc4f5df3aef0576c8bb3e5d8c2eb4558a2ba8a5d21ae7c5733eb9585c832e2fd7106b8475c002df696f3cb7785ba929de16e58b7063f17adb556d74b6aa3ef1ad9b96cbcb6385afe2d6d56b1eb5485a912d3980a78b4cb5a582d229689cb40759f0ace6864c6b369191eacd39660e5e165965ac9d164e8b29a593a2c90d640eb1c058d2ac5a5629cb11258762c2956114b04357f32bea95eb0af11576aaba915d48ae735710ab7c15b68ad6d56932b3255904ac5155ffaaf0d5724ab6755bbaad9d566cab05556a2a9dd544aaa0a54ecaa6755304a94654852a3bd513aa88254232a0d9500aa72c53e4a9eb94f10a63353bc29d494e58a71c537b29b414d806b8b5347a99fd4cb2a633357f298354bcea5cc52cda957d4a72a4e75260a91e948a8a42e5204184d94782a39151d8a8e854722a3555181a8b494516a270511fa889143d0a1a150c3285554248a0f35066a82714102a045500fa7fb93f909f814f9d27c513d849e654f1fa780d3b789d964ead274fd3a1c9cc74e50a713d37fa9bb64dbd26cf9361a9ad14d5b269bd347c9a024cdda65fd327098f14c602629530fe98384c03a5f2d2f7697954bb7973012e7c97182e3225bc92d985bfd1c64a5a992d165b6b4b27a584d2bae95a64aafa548d29ce94a04a1c24ff1276a5e1649b1a4cc9259492834923a46f922ee91514895a43bd219290a339ea2419d20568fb847c923d2d1e088ede474ba39151bd08dc239ea236711aec8d664695233b9194e8c81461d23051179a8b9145b5a2cbd15ba8a96452d228d0e7a88a0e44f4173011384899c2e322252911f088d2443aa21110ffa87d743cda1da8bc2c872e437ea1b310d0a86494301216110a0c84e04247211a107ea83cf41bea0d0505de82b341362089503d281e940cba056d022880d84048a0154fff07fbc3fba9fd10fe267e3f3f6b9fac4fd1673d43f329f8fcfc5e7e093ed69f78cfb7a7dad3ece9f608fa8c7ce93e461f16cf8807bf93def1ee5c0a787b453d799eb08f4ca7a3f3cfc1e748f32c79703c899e3b4f14c785f3c171deeceebc77383b5d1da50ec8475fb3ad49d588ea3674c93a469d118e81473e439ea1ceb8e710736d39a39cc84e60c72e0395d1ca7ce4dc724839169c848e3ac71a538af1c4e0e20e053c38601c268e0bc700c37f31be50de9a6edb378e1bc30de186edb37551b9b8dca66e2d36f89b758db606d7436ac9b4f8da1a6cf236559b164d8506c0d1c649af9cd7826bb135c59ad94b6d66b3435871abf8d5c66abd35511a9c4d46a6a0f34e99a6e0d2e2694b34821a378d1706866340499edccf22675533a299d14ce1266d83348999d8cca0661f330219778cb2e657c32ab19410c9d264ce323e190d4c7f263d331cb98d6cc680630f317498b38c52462 else 0xe86f1436f21b2d0d7086aac34ea1a290cf9866f432e2193af9b386414311a18150be485ce8718a16ee1a577a3f42cc216150a622e6042bbe15930aae85440620e14c50a478505c276a12fb092b8482c2326113072e039b6c21ca109873068402c1f520f05075183851ae2e0dde6b8b8364c1ae4d5fd06933551419320c21052082e4c16360aa30520826cc127608c3040f81f48e326078703a82e3240e0a06a3032b029e40bbe0551026c8123407fe0371019280b0c04ec719272e0808ac03ea01bf009880289785a002affd97fd43fdddfe60feff7f673fa75fd04fe517f1b3f841fbeafdae7ea8bf3fdf95afc7c7e1abefe5f764fb767d9d3ec25f5c6fa9c7d3b3e9407192d518538e3e8a94d806b8b7d02299fdf3e8f9d97cd9be661f2cef9417c933e401f1b4f89e7c3c3e0c5efc0f8167bf83df81ef48f77e7ba6bdbededc0f6af7b4a17859ecc6f6327ae53d6bdeae6f52c7a7dbd381e974f47e7a373d1b9e864f3f679dd3cdf9e6c6f327797b3cb6de554f27979243c8b5e3f8f1e178e33c6add678f1032e603c615e2be5c6478a216ff5e2885bb17894bc40de1d05b6b7866bc2c9e12ef03a780fbc03ddf90efa275ea3bd6dde54eef97633bbb79dd5aee8777203b761db64eda276b8bb501da4aecf4766cbb2cdd904ec6776103afbdd7a8ebb975b93ad31d678eb00756d3a921d568ea99753f3a98dd490ea0c74f8ba72dd34ae97f7496ba399d13ee8797429ba0b5d00ee7cb73cd39d7967c2e72219318c8f5cdf8e6e17363399a9cd40e685733539911cc26e5d772cdb95d5ca46e4f27255b910dc83ae40271e338dfdc686e3077170b8aedc4e8e24e710eb87ddc3b8e1a070acb84cdc1d8e0c6705038241c07ce00d6ff937f05bf4cdf8b6fad37cfdbe1cdee86f4b37969bc3cddf86ede37659bae0dd3f6e87373a1b958dc866e0f3700db7d0dbac6dad36c79b5f0daa66d2fb6911b3e4d9c16ccdb65d5b29ed9086c5b36241b0a8d8026be8b5e29aec8d73e6b7bb5ac1acfed6596b0935785ab76d57f6aacb54cdaa30d4f26a5b35241a8d4d42369feb4f89a736d3756581b4d3ca9b6d329662434c39a58453ed696eb301da584d29c693b34941a454d20468f4b470da33ad16c68a334481a1c8d0a8684134171a02acfd967ceb3db19ea2444d679b33c6d9deacecf675a33a0d9cd0ce3766fdb37559b48cd6866a13347199c0ccaf6644b318d9890cc226603b2fb1978ccba065bd32c7996becb39658f32c0d95d0caac6532b287993c4c9b164c5b24e5918cc8a0642c97859903ac7e163c7b1cc98dc0c6ba634a319618c64c60c53bc317c58b6ac56e6293b12a588f0c43161f530eb98726c336617230a7584c2c23b53bc3085583de8d6660d9b05858208c0de6046301998012bfac5fb82fcd17ddabea65f4029de17cb4be342e602f8) else (if i < 22 then 0xecbc365bbb2cad611ecadf65492e605948cb8c964dc2f0b592aec89d6407b1e058d8ec62362bfb136d889ac40161daac23d86d0fc5eb6aab0c7585a16cbd614db099583aec149605db01bd7feebfab5fafafb9d7c86bdf75ea9af41d7976bc2d5e0651d89785abc0d5dcaaec757576ba435ce5ae655723ab8a55c37ae0e56f292f775ba4adbf29c72b6b15b32533f9abfab5ec5e16ad62d6a52b46f59daaccf565b6b24d58eaac51d61f6b0af5847ac10d5fecb98157d52e3255ebeaf1357792dfed5d4c6d0957382db5d5bc6ad9756a5ab13d5806abcd5594aab755522a9ed54c54640d527ea8b15406a9bed4d32a5f552d4a95754a22a4c5523ca90b547c2a3955178a8a9544b2a20d50e0a83c540429f674f8da7b3d3d069e0b4eb3a73bd391a9be94dc3a6c9535b29a8d4d20a67d53352995d4c25a5ffd2f0e970f4b40a58d52bd2959d4a92a5365286a939149a2a4a8524aa91f348bda43052065190347f3460a51f368f383217a3a551bb68d8f468ba332d184e8bdb45b1a2aa5140a89774495a22cd10ce87d943c6a1d050d3a86514302a16e50ada8521426aa1225087a83f1412fa0e9506b2830d4155694e504be821340d8a0595023280cccbeca00d501028034cb1e9fffcff64d5c73fa89fb64fc967de93eb89f38cf9027bf33db29ec0cf4ea79fd3ce39e5ecf20678753bfe9de14ed96767f3af89d63cea0274b53a3f9d074e7ce739b39919cb5ce49271a4ebd49c4b4e1ee70ab383a9c0a4e0126f7b37762f0b4dcbe6dd136ac9b3dcd8d26c0735909ab54d4e669b934b69a3d4d126680533dc99db4ce6e66d5334f998f4cc0e65d132d899644ca06648b31f398e14c56a625330cc98534c1aa60472fe797db4bd0e5e3b2f029768cbaae5cf52e54971ccb87a5bdb2dc796c04b4e4bc2d2cfd965b4b1ea58672bf795d84ae2a56b32b079570caac254ff2a4e94f8ca702530929742f0b4a5d252712907946b4a26a50ff284e9419c9f2e4f61279593c2c9d264def26b093454993a4be32573929649396495324629218c8f7e4747235c917fc8b0e4525224b91184882a43c921c990dcc862242db213c9090c841a41ed20c59055481e640a720228ffe47f5a3f611f8a8fb247cfa3e311efd8f7e973023dae5c648f58c7a863cf618838f2ac78e8b6d71dfe8edbc75ee3a7f1d0e8e58c71a8bc2d1c238de346dfe365b1ae68d6046a6a34d31a438d0ec678a340519f28cf146614bc2d19338c76463723157187a8c1f4608e2ffb17d744ce173022f7917808b9cc5b722d6d166f8b19c58362ba315a08abd455522a5d15138a7c4534a296f149c8a35c50be2779139689a7c4c4e25db12c78945c4996247e732139b6c489223fd11e3394f9cc84e45b11b288c0c449221fd10b78843441822075101487e6c3e461e950f0e876943ab21cb50e1 else (if i < 23 then 0x2f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b6a6e35325a96cd49dea3ff5187a892d4366a11b5041a7efd3d9e9db34e61a70ad37269acf4d05a65cd31b698434ba9a5c4d2bee955f4a634caed26a6923748b9a40ad1ece8e7746ada330d1855091345c9a2bed14c6899f4483a226d105e87c2db91a1d5d0dd685fb4285a106d06ae823b40799fdfcfcc67d1b3dff9ed9cf59e7a373cce5c0dcf1b678433bd59dc4cecf675e33a379cc9ba59e71df37dd9bb2cdc666d1735e79ad8cd5966a5cbc2d9a3accff6676333659997ccbe2daa8bc2d9935cc7ce62cb30d797f8cbd8e5dab2e89971ecb81e5b772d84a6c0357f65a732d036e3fcb2de59032c4b960acae1e55c72a5594c2ca596523328cd944bca1864f7b27719371c9ab64c6b25ff92cec938e482723b191a7c89fe446721e6eb3cc866e42cb212f9071c825e403f1fd38fc3c7cee3d2f1e4b8ed3c756e3a1f1cd98e46c710637eb1ba98daec6c46355f1a0b8ceac65ce327b18c58c47c60062f1317278b4cc59362bab15898a93c498e2933140b89dfc4d1e25f712998931c47ae233f11538883c42ee21087193881cc400e1f9b0f81879ac3bfe1d3b0e518702c36e61a2b0bed85afc2b9e150b0a3984d5c241e10f3082d83fbc1ea9719307498326c18060bc3059582afc13f6090b044f8201c0ede06d7031f8159c0b4e0564d54581122f0b600f701ad8079c01edffdaff757f7ebfa15fc1afd697e6dbf23df886fc0d7df6bee817302fb6a5c64abbc96ff431077d8f2db5df578b9817d43394f9c8b6f9e37caabe2c5f09cb9817c170c41def42f7137b4dbd835eafef4af79efbcc3a428ef281791abc645e206f0b7781fbbe6a370aef4f7781bbb31bc32ee6b76eebb699785aed2f7666bb155d7baeb907e8bbad15d5f2eac3753b3ed6dd482e99d74b3ba4c5d19ee8997410b9df5ce8ee711737839f25cd4ae658736db9835cb80e60d72c53916dca52e4b17227b9065c79ae3137163b888dc382e1a170d0b84a5c162e04f700cb7eddbf02df1f6f74b7a75bca2de1a6afeb7791aa8add996ea6b7405b996dc7f6e19b6ff5b78edb916dadb6c9014f2daef6d5cb68adb366d93b6c61b60d5afd2d7456b0eb5741785ad5596a44b4f95a732d34d6980ac23da5c2d26968edb463da1aad0895847b40f2359acfc56785b39f59c62cda366abb3275981 else 0xbc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e16))) else (if i < 26 then (if i < 25 then 0xf0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858 else 0xb21b2b0031106c0d751a18480f46b0af13841543556006020d4194a342f9290861127157eaf8605d568621d27104184605d568601d21186180747c0b8601d260c69dd5e915e2ad5763a4c1855d2b920120020000210002b80083a4a34c318e928d20c430081845494688601d230be058352b72ab604e20841f2920099caad4001c0b02d9ca0040600004e7a4618d278e9186249a3008108e0540480c568004001c0a00104e00c02143f80200203013940b0000180240081804e7a46181258c21073e30026912b30007564020002ad0085562004002ad0085560004002ad008555e004002ad008555c004002ad00850180015680420040be20d4108020e90d200be3a3e1a86805f251b0c6ab12a928d862556950894c020a8d89c55494894783585f1d1d0c89287470350d00be4a36181282a922a8e2e11861fd2771604e42f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162f0b17858bc2c5e162) else (if i < 27 then 0xc00a80895404554f604005760054044a9c0d07db02002bb002a022034604bb00c005303f08953581009002bb002a02254c068265810015d8015009aa580901e0318103b38946043b457805283d1280c58189c2d4a0c63a54a845128b50e36574af715eb498118308d6602c00740af5fe706352405d4802c0ecd51d7f2870c645c8bf47d2f50c45a8ebf04b86125471da3b2a32fb1386a8a2806aa771eabe95e9c74276a8a3d57cab935455f035453af759461f2bd8532f50c050620b0228015d8064021c188010320101d946a0e71f001080f4738394a017cb510318a44c4bd020aac386212abcd30aee5562dd79206a2605e201095104e0e7128a80650f75548a875087b2f00be50c0281778671eabb9281c7a0f3058bb0309454017154bb430141e8d4a821a86505f303d1663a431901e8391d018480f46a0e70be41e42c97586212a55d83c45a89c12851502a9758601405a803a45e8c1e86317a307a1885e0e9f8951b2b68780ef5d475ba2f454f85e094f04ba7aba000add00a753a12e9e2e8002b74029d4e04b1dcba000add00a753612e9dae8002b74029c25d3a5d01296e80530c70974e5740015ba014eba036081e89c0d83a7018c4a2951dab50749c6cae915eb497414308e80d83a6eb9d732e50c65a6eb9062862206119c2a6eb8c7609c202605c12e9b013110b0002a160066103d0c019874d4318a05243a55e84b3ae210cb855dac028611d019874d44e0315c0b287598672df5bc18094cc6a0bd1d341782a6639c360c2f8ce15331ce19863981ad32a6202452cea38b31b4b7431901e8310581888b754c0be0581280f804385d1d401060996e8d75b8184a0f45a8af138407a2a01606020ca00817c6034598631d241b0184020e820d40be0107390730951781888398500660c041b035d6d861203104c02c008c4a600ec1a201e8e51c81808350652db0be4166a2c318c7086317a31c22f0310c700b20c43a5e1c44aada20df0582543111458040c231c6b645e8c7182c1783010b6169a8b00a518eb5d69a8b00a5024b58042d3516014c0216aad3516014ab4c09003516014a31c4cad3516014ab4c36087086c13831c02d44e0e97071128b508b4d69086f8b512827083796886c1d2d5a018c74b5430621acf58a18474b56709c1d2c08218c6b301b8621d2c16a270637c01888598b347100538aa59818063843006618e015418074ac388a057a4598aec41986f8aa140180a3785506618dd1a2b2c3012958dc59431b6b24300e952c817a3a540dc5e0e952c70d8358cb142f8e950490cc306202c0c81502c028241e94d2802c09c05141e8c106218883606bac10c2406202c0c816076507a0b06a86024f058a17c73c1278631cf049a18873c16209c180b58622009804280d58400c098272cf04961806350652c10be407a2cc6d06320 else (if i < 28 then 0x310e0164700c801018020f5d868b2b0c04004010040eba91b10180040015c004280a016062b00022d750cc1806006b787c0084ae8010008120c65234010008c8cd74ae20304014025720fc30095cc3e8c87004002323045c008c8b11501832294940580111e501644eb7803ae41e8c44801d6f0f24ae0004020782111ae15c40e0772d6701802c88008280d21f5c00180cade180e1a80b00200049ca02c01000201400201004903fa6cad4030048003004002024609c0080400040002000a009018938c00402000180104e0000200828009ca0106002b4804187faca030048002d6501802c04108707f0160300496b700104e010001404d6d00230135b0060d95004002024001535d2200402c0016b580104e000020083009016000602e914e5012000a0703c803012ca691180c81400200002140a8770335a804d6902800194240600b002000800c00804000403002593801004001931eb400a132557e0480412b40405019ac35803901130100300258d842002c90e0298d81f0e44ad0c8c40600481e004001911990aad156821a200406000868000010cc8002080c015012afc0004263e702559c02072200121a04ab307228140255940200928070121cc2151d02a07935200680201039c009c402d5680400040155900600b000020d3818d8bd0c64016011572ad01050e158c0580c00450dc02c00800205f21820140702fd64024020d46c5e90b1d1b17842860142f86b02402eb180c004800e1b80931eac4020c034202ab0d600be060848083d1b0cc42060703255f18631a0ab0607188884006b101c63a17c321083b1c126b6361a42f900286b10050d2190617c06880e31a0c8311ec642f8c3405f0ce30f21ac41dd8c55e18680d217c61a0680671b140c44185e108230b5b43a44a958b06c13141384143610820ed62eb504a146cd5d5d22bd6931632e65ca25c3191720fa62a3143116ae0edab6bec7609c32eb0cc26282803006621041aa40d5e8a02ae1ab4b88430ac576bacf5644a0d5ab0be018aca204812e3e6abaf6202180c3985e09518e60d825063984b8ce18e60cc28060f4308651abe1ae25538b13282c0020c409024008620013557801624090021c2702e55c00589024008705c13559008624090021c738040c8307a17c320eab0631489547faac1de70c4bcd2a2ab12ac44161c6a3104a6c3c0216ab09c4a439c4a2aa15e7aac181548a01ce940161eaa818aa832013816330e0621884a90730fe0c425483987e89c128461c3f0300a020e60ec1805010225530580241100b03e0ed00b80482c01e02c0083b382e0260df8c80c09802c00818076a0620257601f07651d211477aec546507a3a41cb0d0c6512ac30310ea90951b2c2d7d2da16ec2903a184b080c2460ec1877a725d851aea857c8954e2c14c11182034aa2c0800ae else 0x8a08132ac0178201a4f9b300b28004cd639b406c1b67014d981013f0266b1cd94670c068600663016d90730050d0d8c049c0593e0644f41581009a04d002d46d8d2780a0288133ac001a04c60f49d84d03204cb62836302084d026064a0e49d58b11240720b018b5e032bb4d629b1080980411232720e4020e2258a2722270224048daf039032d8416089358a27026c0d78448c17b5f06e0e5af0136247b14d74401071080693802ad7005b5701272620800584302e04cc02c9b85000204ca2801980918e6002109ad8132849002080020722d8915a2092b300681320371c402476245608100010081c8049406849170049ad009358914e2014d68100720125b12298404c198111833080b2623b82184d026626c034098c058490256203901335870936262d641b813280b262d640b81328740200e59200928106b20289a82c0e46b0e18c44b99088901240924d0988182661c8d61c31083a03905e0600214990390081c8961c30880c1311124c0160723587138211202d5987220097b5825c02481c81d809030401217409818640010d61c300834833103b124225a17c020c0685f092317a16ae39c348c068e7092317816ac17c34b55200d0be1a461a424b02f869180d0be190617c32081d80d1066084309e02d4a0000106b0c1a00900820cf081c6a826a60ec0583c0105570108040da91221351248202e066c287d23500020100011a7868008020961013889580b02000008949581911e02c00011358425418460f0090081d8323620121098d81e55a048d6080e0120104b0210204a6b2079258125020300018d83c002d38d6009386801a020a498205c0c800ac01e0089808018084005a6940c31b698302e0058d87820180020000134b281957ed28649892880e57f1863084180423da4860180a0380043000028782462a4c490918c30348101c1875f8618c68abd181c68e210039440719b883f123107d1ca20c0d184181a289a205f01a02c0a008357d68618c699031342244304e010040c0682708402095f5a08601a240200258d801004001a01d9fb1b133e0d00100412be2941012ac8c6c3e0102d7c242cf469b4082bf03ccf002199d804132d0120340cb3a2868024ce404d600301f0f5f19c337180202402075ec8d898d8120023af6ae05e06220010160480610058040003014064058180105af6198300c0e00066c00495e80e32d024020b5e020418d80903c0080033538000020499a100801723400495e1998890004100955acc8605ebc8190024af0cc455dc34012010423c1004040008000d0010cc6c00004181663647c06108f0bd100100400002108f0bc101900001060580c91f018423c198402d9801c0d004804199781c0d00480416bb0422363000010060c0200c1061008221c0040611d010565c030048d9681900003404b2c)))) else (if i < 34 then (if i < 31 then (if i < 30 then 0x636ae3a07a0c068e82b6301656ac7d8c2a004c141c0580d11239c2e815012706e03c140c241591700600980b6fe055167c318bd6c44b45686d00156ae024d67c310bc180427202c5c1402d9f0c24909c901e8492a41c87114ac0201240048d58248e20e4400a0f41959e2a41c8c4c49e8200260a0a125bf00b6ae5480798448e70260145037d01e06021802058b0520944488c03855dbe04a01606002aece86315a303003c058132ac014449ece862158300a0b84494c00c4e00581805801156743082c180d1182e005815272024e02c24d9c1c4080a02c2281802655483820380d016d5db1809280b092d5db19520e4600a06005d8f132004c01493b576c6548a038059536aed8ca9072392700ad5db19522805030049abb632a4600a049abb6301252a854c65b576c6548d66c0200b012054a0f4069382980603405d02a8016388068c401850980601302c22a030c02c248e202a46ac2706337b20201241304e0012d9a1383186248578c6192d1381b060344e0af1ad40b572a231863984e0c619431382bc62bc36643665bd09bcb78084d5c0a94448e700400c0436001ec9900a44488c0060e1bc0076b682a0018110722599646200a53c01812644224d665bb8844b7629801803804303d262dd0050200260a0e02c068890ba055ba8093b7401000c17900588d6e80280a8220581c91660318bd183d29cdcc050722666b301885e0c1e80a0022684716cc06124830164c44480a27003c1607245981381b0603444b6727003c39182103db2e08096073314d04004c1412cb0180842807381305e10c0102c501403001ca60260480b00222cb06105830162e00c0136e40c42100605e0b18faecb09c14e30160a44d0056484e4049c1e80d27cdc444809301f02a02c1db70b2a388e0f49c0056de23404980584902adb84d8e2300b01a4cdb6939012054e04005d9400e388a02c9880101e0b0391803a6a29603c3914490fa1683124125a02c670c0680b1f430c6b404d5c628b4180d18a3e861887d087314a16832865287d0c308fa13560162d1b6100680b16831382d04035b588070180400ec1414068090660608d6d828010820240c1ac932315a300802449019231f01a081828090326b24da0538c19949b262243915b380a6d41c8100090307b24d94530c058725d852005147032701651ac6850008064c5141000403241cc105c1340201920e60302209690248310320104414730bd15911c422060b80c004062388a3985e081880411030920c41701900851cc1b040c402080c3200082208398670805931b200b002819300b28963ec604c008064e4243900a032409219844b430066180d0c012462b42398300a819430c01246d58300a86d2401a180540c540406833112c0c02a0618061880686606604c80100080b28404cb639918bd183d06e38 else 0x1202484e82581804e4ccb6d85e080c01301c2204714b580b1cc2684716db0e610186fa2240684b05809cf6d83609c908901ab08139405840580a01200881800404d0060bca1d0970ada86015030041708180330c0100a0c0357a1706180540c01060014357612d42800506022b90b820c02a06008300a818027223446399c80a01db40c0201a0280a0132389008004b48132db30c62f460f406803580080b20133db30c42f06ad00693e6cc5a0099ad989c0d8301a238098ed98600cc3278b04058430a004cc048202836c4202c1f38f02404ca0582407c02459dc2010393671e04809901f8160204d01787c35b10c42b64cf1c200925b10c222c659800015012502c0181f9300581f0d6c44e080300b56a1f085940988800840300e59d00921090f802460e84409a0124b6218040f49d83700204ca03402813180b0a0004099005013004371ca2c025880f804cce34020010f8e30049a7838b17a301b6b2d7803016468099c06837006b30b202023402513c01b8bc1dacb101088e013280d568e289f11c01269e0b10360c070490164fc09967800a100e05604c0112d63890096203e013300b9e2008605006a4fb5f6c278863380d4d96b2d780323404ce051c45afb5a04c401806dacb1047c09940180b70f3c43f1401b86b5c1f48036d658823804cb620010801d880173c44c881300370b6208b900a5ac00800c8a940a2c4b5804ec409c300ab5962039013280a00603405813004602802c0c58802623cc02c0187a02640f200c402c3c01318140316b2d68130ee600602c4801325acb101083001328420b840be01060082f80a1b831ce1a57710010e702c370417c348c0105f0d2300417c0b0c3a00e102900a02ed58e22848016226d50e22805016236d48e2280d0163880a901e96300a002d40e2300d0400ec09828280d14039cb0018280b27963420804050612402c0682911217450015012928ce040105204450084e4a7cef6c6024c0f424b6302a534390e2396203838810102403d06250c0c01501208839249e84d01408009828335b6c60b00201f284811a280098221cebb40a81808600816300584902ad8ed38e2312d0c62f46034318ef18da05c388318202da60c6584624877961183d2ac134b0018283d01a2247100928292ac234098310300780a827058ab4a18c5e8c100a0014108738e23381038010208271186b4818c568c149560160104480931380161240a824b46388e0f41b813048088062c01008124188790c96862178301a1881b8d6d041715f04001014141e80d11a38804941e81f0325302408830e60c62f460b0af026700388a61873062178300853c05866140388c0f4160e22ac504a50c310bc183d11a01434009283d05c060aea8db1e1f8e0f40688d11238804981e82c2b81f47114490611e8325a1847a0c068612b) else (if i < 32 then 0x1141e80d01200880340a02f180b0240a6de82400804ce0500580d0522242e89702ae8c04a8bd00904430084e4a7800708024c0901000b0280bca2240add0708008ae24092ed0085e03e02238185da17c243a204402801200580a112055c25cf004770818c5e8c240120c631b41400086305e5b9c18cb08c010632c23b9a18c56f6dc1754d80bca02ae3dcc00172c04980580d0bacd8448093019090236e5017062055ca0220584697724318bd7424063722e3800112024c081d01390620bc0118bc9392f00c43e16e3063103d0525cc9700000822404a09c00b0ba054245c500472e64e8b1800b88224c0f409822100090a008310f21b840c42f060080b862183a73c08002003280b01a2240ab9f11a024e0f40b39e0445dd7688823e823c18c5e8c9c02073c0001881623e723c1885e0c0214f0be25d7580a19c00900f40214f73a0b1759732c882d42f04a82c0c4507a0b8ae80405e507a0ec0008d112024c0b0bb2c106370c3e98010611e837081847a0c010160c237063a07a2f920021d005876f55a17505e40160344485d738054049ee100305e307a010711660dc5b82184920c1001e02800480f40289701e5b07d002380b00a048128896f85b0ba07c4dc00c658460f4029736c203c1611a1128b80188790ee006102c301603409383708024c01582383000e10409802d50706001c2081303a00b539c1b84024204e5b00c805706001c20813805016e11c1812012607454ea6383024e10409c9c0350900000a809300b0142240a00c284c04c4541600c280b014e0c2e8150046004270028c6b09c09a0bc0096df89c18c3004270630dc209c0d830045c84e0dc195118cbdc8008a8896904b506c1282d44e158006df2c400a3016adc0796c0045070225c48042d81f0d6f9278d31b9b2e2d800211a1126b7c934910c448060085b08f947316a10e612e2730010000c730222e0220b7940b398014b700588830e617a29060600939a01402c02180b024016010802c0208058497336f40682f35bc58202c0a02f280a0ba008049005002012301403401009203d07617c04818280b0760818287c0126b7618c40f41d889012064b6ec31081e81623e0600496dd8160c230160ec10305238024d6ec4e0982816024e601381831631121740a83b01605001200c03925ce5c04940582e28e04c4782405e7016d6002812708024c02c1602004804ca5b9c2012012425c00044809212e0160544d80d1c4008e4b80008d012407a0b8b680405e50285a80c813b74220c1741ddb90165b0011805820b705100081309a1dd002c0513e000e0c04980280b0020bc853cb5005110001c1809383a0ba4e1c1809280b000e0c04900500b15b60b9672a0b000101d80b0120648b05ca82c00040e84b80c0881340e804db743942d622006b9301409cf6d85e880c92e1 else (if i < 33 then 0x7a45e3d41de92fc5e877a4363d31bd20ba00c05820124188e17401bd100a2484018c42cc016f404408035e817af3c77a0bf1871de80d8f38605844061183500ab304407e280b06a2203f1073170016220b7941609200a2203e94c30f60c63516f344398a509458b4016300af304398c288670b4138307e38810063203700603166080283d030012f107e28371c41f460601a5d6bc402c4c808381807c454061006834bce3884e00835e60301745002002400c023504de60c6f2c77980588a33ca01823c0c94c214627d41c4408f318428c03047819281907200de4acc2de60c40dc77983094619840160180600311e6bcc271e40c0180b78e23c979805bc61de5016251600d663c5040530602c0180f0f4024d7944e094184951600d660120f46bca02c4b8c9f0330123bc81030174ab008026009e21cc1088bb21e49791e188c11561c41e49790c10af23c21003782b303c92f23c010df69c22009900201303230300b0070010164b4441c730183024b444141ed070081e04414733bf148306e038711411105598ef8440c733bd12a300a0f80208820380081e00990733aa128307cef00587811051ccb144b8eee83803017401814040389dda402ad315ddbc623017883bacc022500a0180c088170a2ddd1cc0088bc24f83b96eebb9bc030280e00c088026009dc1c0c3b776c00d69bb535dd06e20700600105301aed0441cc05df1701dc9774c05de1ddd76777074000680b180b0ba00d6600504060402ba83888016240041e800ad0c63bb604c1a85d018515c02cbfdd81be240041e800e615c184802c05088026b4c481a800a6016300a030048eed00a01800c44060305d040ec80180411e611002dd888f25da17aec0617401baf0400103c9801bae59809c97685e037196b0020343c0882dda2fc5ac7768363ad180d0c02516180248c5550727d7643016958bd15a31ccea4be0c020aa27d76030013352b2fc2a861256608be80d04175c30009352b0d829c6338530601a8b1a23d46398be09d628b15018083985508028661503516345d58c298d106e31cc344be0c1f93e01235160fc44f83e0041dd517825460043e0040124baaea84a0eeaac512e301c0602492d026507f7583e0040125baaea4500c1b80900231cc0801b8422f6024cb31458370025eca0dc01a8b00804ca0b08d0040024ba82ac5750810aea10112cc75004c60dc0c8131dd406e201a0d004808200d00a207ca2c06813203407a0108e0012dd317ae9c60341b801012400a0dc068010265ba62f1d30ee98ce74a301c12401940026507a0d00600925d30cccac6a2c682c81a8b06e201c17c1a0c02837100d0682516341d20c298d006e351617c248c2984910050921ac617c19881680a10d0066207a014715d2004507a58c02892ba2008c0f40688d2d833801181e804274054 else 0x7806101e8410400b8210220480110fd01002c0840bc18804381c0c42f060e82083d33a030a036fe91f29841cc3145a0c0e0c530a307a13afe0b80ee500c0f402809018400a5fc13090016310009c0582c01802480b0020200c01980198500ad101c0c02a860b02070300c3183d0ba120345fb01860164f81ddfa002500c0348e00500204cc0344a39c00204ca671f980c00800ca02c068090184008fc8058940d8004c0f40218d314004a035f880b02a024a0f4162e805cb6efc87d38080c23d06f80740f4180d1d02660034028c05b30012020801006009199a00c129f80132b2e01b7b88e00f012608402c06075002532c004098c0589414e1081780130420740181e82c0186bf0184328c0200b3360048020058b419982943386fbc308806ba5101800c02c1bbee02667db7b801004006054cfac0600b012004ab6c0584b00204ca0d02e80900240160d006009200b026fb1f5803010607602c06009219332c00409900583b01203097dc31081e83b01203097dc30881a00c0123bee02c458c2e83b0177d800981a19a03002c1480c238005002ccc80600204c1708f380b01a565f486802a024e0d00581500240160b0018200f404cc58cacbe902a024a4b87100b0083100618128260581e009940505d0160f000940680b01200480341d86018e4be2080160600266bea2a0300c0406015037c0180540ccc0600cc3be8101acac4034300c318c30c0201a1b01a01325f374e2f46ba05e0af9ba519c3be6cac330c0599609800409940280d0263278b6c058430a204cd7c8b1881a0090183be415ba0f8cb1970265090054080c0281f0a004c80d09c1967ce1040088c3df227027d403df480925f27d02112014ca80f20057ce03c04901a03a7ce0481c88c00c0041126f901210291180e40a809282900a230ca00601261182e00a80925f27cc25d0034098c1e93b0a80040996f684c8be53277c40994c90290722240494008392417c04494148057ca04c0096f6be4100127204c0208929390720100092f693913e30277bc0212f73e200204c8014c88130024bdaf84401444809002411202457b49d082f86913e01ce1a4603473834180501a219c17c40341a05f180501c201a18c418def8831aa315ec0ba25401814040389ef22f63dd15ec0990bb37840608810065164885b8c160200042484417b318f6b45ec4410c75eb1101f48a2c160969804bae1f4942c0680b1805006a2d6981213260060200c2d35aa02c00a8b00a900a024060ef5044418d7b8b4c8630441170024bd4f6c4632ec18d22e4bd46304f682e80c198b22a2200610730a410380580084918a11066b4b4dec88820e612a20161b042d40693ebb2270041a970bd7b0300a116a4f87109c0105a5c5f85a8d458fd1ee3516f5c4398c488730b5109c00a27ac080710120c657aa0485))) else (if i < 36 then (if i < 35 then 0x347502c02040164f81708f0445c421728ffc1b818020501a1040481822dc0200b011100e13a0961044617108bc10e60300249693108e6102e6fa6a04481c01a0e4250184e210d82c42338588020f70f8411181f0a02c0a82f110010d58e2383d3544981608802660304b4440c0580dc3c5b0441405e1d30004c4402209a1dd058c97018112230440b801205414e1c58292fe02c023fe01260160149c61b0f8024c0040582e120088a0a42e97f270ff8049802bfe1100248124059a92718683e00939630525fdff009280b0140543413e078625c0604409a0120419d619400b01a6a09f009280d0c18607a909f0aac2e13430013316325c2c2c180540c5e86015030442a8458c20883061515441418504034300a0c264577568439b090850040686015184482a2ac0806860187840818061d57184827c2f40990068bd5ba3c1eff45e0f07bfc0d83c1efec670c0692d0263c1ece0330c5e85f0d23090010439c1fbf6185f0d201061b0217c32004185f07e010658c07081e8040d183800941e80d11a1a05e001303d01a2240a801283d09024b06801283d01a02400907100b01a0a42e89511202500c40260c7ea22404981e82c7ea46871001300d0620f41499f03246800a01ebf55da01016010303127c06576812058004efd4058371c582c0099fa8e917a301a3a4778c170e20c60809828319611bf71de5847824b188008704840a9a0c10004240317ea0b10154013f212a0b05e001383d05cfdb0387e34e633c101cfd4bd88920e67ea5ec4490160546fe0c44414cf0bd13f70c23d06fd4740f4199e1cc200a0f48d120002500a2540c82c112004c63c09b7c016040208051128c0c18c558cc79a0240fe82088933f80a8480020892e060c20b0602c1b8e234c030a4e00208911047ee2bc630dfa9510d8301a544578c74ad4119e0d8233e270810ccf3f910e815e20840f4d280120950840bc160012829627814099a405e0b00f031084ac0818c778c069a40620041202c302c7f0c4c188042e040c20b078104e0af180b1c4010d18012bf71f42d06fd4628ce199e024233e314808ccf315103107a06404901e83101200480f41d82960a63c0c0890128c0618c778cd118f5d86801608933f80a8a344493018610583c06270578f0180b1f430160381de021c4004c0a41c92e112024a0a40b82c07a06400989d01907380444949700b008684009700089110306e22405dff274388009c1e9a00582240c940585d0760f00095fb86015037ea180330c0686005831d2af446783308cf86006e333ce4043a016080686006e32a22a0431461881e80d1c42f00994730050165ec0996ff06317a327c0056002301a5ecd7f8058ce1bf632a02c2185102667ea39c020ccf00e100d1ce0dc639c3488068e70c8301a39c160c73866102607a47cce80c284207a4 else 0xd6eac00407caa2704a0c05845026b756007a1dc7caa02c4b8c1e83335604c80f40686611004ca0b80c1a705e0040588825a81cc0601882f25a220cb000208818e61381b0602c02078110401a08329090016310099c0585d81212c09c085800811444508631826098310440132d11008184701c05888026115600903d1113a02c60f4dc00a00204ca174058200421280202f0c080161740982200212c479c0b8880161341708f36540c62f4604c1782158009cb950310bc183d01a0043c08811c6ca8184db8f2a09c0d8301a02f29e520c0198099d6e86005c3a6a2f4568c7306005c3a6a5f8db0e9a86c14e336a180050c6706014c3ca2180720d6e8661c831cc180720c730600cc3ca0180540e032dd1841808b74300661ae80c005c63983006615441a80345e8d6e8e701a35ba0342f8d740e701a35ba17c068c1985f11b50be19c63981f8a5012401a02f27889110504c1040286811a2f4c0fe750a5012407a0343413e02a507a0340016cc9c4f8c0f40693e012401a0e41104802004cc036029b415a220111b2682e27c07c803b2664b0201201118068ad07e4f80f94318bd100d166b7460f56e1ac02004ca0a41ce4a0262303e1b0b9ac36404009941e81c0821f0461452031026dcc08043082009018c1fb7319b2062dccbd82c03e601a3a81b81f203dc4a4f816080044617a188790c110b210220c592459104ae48101300807c60fe010a50122f4a040048221c02c8e53f233f501262739141703f021010021c1e9b3058220111404e4410bd0c201060e41108068e8082312a10166c8d880403e04cd00b1440101efa404981e8057fc1f0ca93e308a020b74108080446c50fa802643018507eff89f07c200507b90b2087c32a63599000f813263d1480140808901e12821841004a0c60fdfd0f1e86212b8fc8a5f1f02ec500fc0781f0088c7a184208c0580d7fc4f80a940689c1298f082d71293e09a270111b1d89c18c317a270630c110b510221398e84a104a639100d2a22531c116955d10e6c6e21ee1c6c107a5e96e012012088d00b1433c708024a1081ee350020bcd69b038023580241113190a40840a41784a08610401271906212b8d098cc0f02e4da0fc1102f0088c64184208c3e0ea0245e808140580d02b8c434088303dc601043e08c280dc5e1f04610730391120540c00b090cf0d788850bd1ec2d06088c2881100bc5c25c818c4be2d180d18a25f161031403c5631cd8a841847b080680b1698a482705a55b1adc05402c1600904468040a600e280124b4c0ec0693e0f8024a00cd76275b8084099a0002f00802471141d83dc4c004d680936253580483e022283b0040a44483901260c6bb01f8f11862aa425480fc14b0503d890020093e230c2104788c4e54a1284c4602ea3897200b51a0243e1176e220241f0138490440410) else (if i < 37 then 0x310633a03ce218cb08c301d02c23ce0107a0e826868030504012c0c0040d0314d9bc818e919380160282e8150139b81e20301cf1e43cc4188e78ce70208287140c940580d1120540c413cda22100f42402239c1e044189306317a307a0800114e0f0320c498310bc18048240617594f0480e430201e84b0027344789a31c40c62f46710310bc18603983d0623c308f41e620c273061a0e60e8180bcd672c2102f03260400781e001200b0300240680081b030e5200293e001036061ca30050ba00206c0c39460740140493e819034091ca400527c0620640d024728e4f802809001036061ca383a2a64f80940d818728e02c0505d0121a00a9b3609c38030c0700630f3109c3803818270630ce209c3803cd20c459a4628b359c975c13400019303c0160e89d66a112602e07c160215da09cd9a5b10e9181206e085758272e692723a079a49c151180d0c00281e0182bb229cda84782200a060f9a0319c818200f005c131c700a064f9a0308821e6813871864240c01011e0480c9b3284058180204ac0c94478480150300f948481038a06480400cd1382399ca12c9a14e11e0c4b99431080c16382199844149904b09a23c4d1732861166513821121a00f83103344f321c478601503cc41800b8e060601503388180050e07e6381c0dc17944739607800480283408e07840162249c01500a0600908e40e20620280a81811204847204481503004847140a818024238802c0c04800103447181d01801b03447140580a02a1a04703c308e0be1a46180338691868088f0be1a479882f86718680ce39c70302f86919c40be19c702c21a1aa8e7188f0c8205c02c31e5a17a080d984319611e600c6368797b2f8953782200980b020004120045e5e0c62f465ec12082a80bca59772e1c32f675ba2f0608c73062182301b96c10092016220bd9c11c0a2f62208b7474004180dca4264058c7010601604d6e84b5d03b84c9c05814536090098181dcba0258015ba01580f41a0c7026408802f2989ccb41b0041e9c0bd3843a705f8e08f2c89c1ac35ba1b06b0d6e9510d831cc2706b0c7309c15e3124270e00c06820096088710631dc7cb018c5e8f2c0621783cb0184df8f2c09c0d83cae174098540400c44902f0c4907a0342e8200260881789210090486216000b11007c1788046570c66f8795c308871e5713833460340b061110338a0f4068200941743f16f38e637a2200596f28e60c62f4de101e80d040248b207d11071cc1885e02c20e61381b0dd906706337435ba314670c7314a37431cc3147d0d6e8c5016319c2705a0f2b0181d22801208800404c008220960119958318bd194625606047822280d07b9484792d283937204c120105806cac1885e0f2b06105c3cac270360c0980b09608847972b00b19c301a0b0018200f46ac099c0581c08a04 else (if i < 38 then 0x863180b08a064028182e8d12e02c60f42816c0304066180402c1d85f012008b510698a41d4424425475107e894198612e17c60ec198b4605f1a830bebb0418c6a09760e7058301a1a42f8c0285f142a5d81a42f90028d00d230d03e0eb8d7605f02c307a060028000d1a2c441c0903d01a0404485d02a0600497100038b45345000401600000809303b090089a80192c156a00880c1214822032307b0a00c1d625a07cc754020ad03e10c138a0383d02e0641607d0446d0a0b87a0c1142713731d00b8604a1302203040160b8448150300240900184b09344af4280b168304413aa528670c30bef103d03c0ec0c901482e5f4d400c157602e16888460487a14300a81848044158612024aed19d50c00b860b8305e110498420880c98053940160040c1471031d0fa180c0001124b5002c1700111e4b4a0341480b03108096980582e84023c96940c00b01408801142480b8404b447940c13805308096940582e1120540012d012704107c2f80a030004c4b42f8691e850be1a4608a0f0896841105f09236e639c40a82f84118411c418c101031ae5103d06f0740ae840f2504e0381880bd04750011a0e80b02a0df418792827d0410473802230f083d01a0bf4088d1c4605e12005889d00388c0341780b1c4054a0f4b18050019fc7118068e205e0b044009300b01a2240a82f7cc0633f088483d0620540c01304c0058a078483502b9f4178e803007016088480b01a2373e0891c4627218c5e8c130200300b8210e81c4707a0600402e00469cc4e43182e180d0162273d888280b05c0541241ccf4388e234310f219d20c40b062556d0b3c93911222083241604c366bb4441873362103d05c6a83c0e2282e8361e071100582e05e3880a944910506827000973c09c18c311a270630ce909c15e3128b5044e44e0c618e66f6201607c0a83b8359dc711c7306110e601620167383c08820e60c6225d9d9a50891105030dcc9a02e0083203c1c7306210e6138202c111a5285a0ce914a1f432723145a0c9c8c51f431ccdb058981003b032401b064170e20305052bb00281922ec15a2124270538c1d8173a60643c41801606102484b8a618200f005ca384c82e064e0897602e032411a1c45058a302203251240c40ce7553e505c061b9831208d1782032a7f3a088208d0d82030d3339888208d19c211a180540ce906005c31400b8439830084905f0d2311a17c348ce905f05831482f444e47386919391ce0b062545e087335510940d221cc17c425c6708968e610a00cc207a0a4340010080f0c0f4b18041120f0a0f4340051100f0a0f43400402a0f0a0f43413e00a00c1e180683c0303016048e6e630481080c1c1e0291121740a81801212c008120090573934e881104430480808483c05e50001200ac12016220110fa0c090160280a8090d10301e1f else 0x4b44780c02a46a0004048c0602e11e311e03004947200c03023e21029283b030030478092c3d00c0040191f4bb111e30ba4f8f18c09441012325a00c00c3d20481000082a010285d27c7888d44005e602a51c8e00900052aa054048db180b02a3012060101e120892720e40690018203c2320e1c8068e1fea987c33090f44791c000587810880984e6a60d8020c2f44a1c21ea81387006010bfea704c240058c4010807a12e042eb2fe080c248508a40c6401653c24845072bac481c4909d12e02c83980580a2fe004a0b01e820d4c18033185e8a015a31241b0538f528601503128198540c020940d232fe39cee05f200414032863a5490862c3b10a451e212f0e8428146082103d0fb65c67942100b01809001141883700809000975243912a188802c248243b003417982100e041a8c6708300470281400c03a09202e1c80440420480300586f0046016781cb02f062010009c0580ed460bc3200235563be2547a882f8641b0e0c83506c38738641c3861c1a42f90028640d230d017c650c3405f0c830d01902f8c340641943016034448150310df50888403d2c6c5402436d40224e02f4f8180770d4008153c340162249c0150120634f1710090cf4eb00580d86422004961606307230160374e431112220c779b98a60020c41c86139390c628581884a8d6d095100b01a06004e9b8610bc0aa0e3696d2e2704a174d09c18c38582704a0d6a0941139138201a0993842d3ba220c0141300b05e004a09802a7085a774441805026017a5c4817f302f0165f00a8092e20361742dd32a0c02a34c02c008090c01005697d2c180501b4a8601503858180500d5e8a011390c02a064e4300a1605f3b8317a29044e47381618bc12a20d2250419850081e8025d80ec40089303d11202576107076080e1a01fa8d0401f00498058e9d1c290b083b03018c10243185761610c6300428c318c312ec106318220620f411009619a4c3e9d76063378307a02581107076080da5031881eb0222a0ec06174a061103401602400901d80b031a384c805a2e021002c0c009068111763021f626520357616c030406802c0480c200bd1c62463020d260ec4e0084d4a1a67087528921c11e9213835862717608318d612ec1382bc6008ed89c183d0620bc448192e9137c18c7a44438611e9119a27061a00b0260410ac308183aec02418c60f41d8200047683e8893aec02e1886bb0e309c186337425d83147d0d760b4016330c2d04e0c3183b1c835d80ec300c028a807635d80ec0b860203d1121a00200c0761f0fa4031881e83b1120649a4031080080b2380ec06174809c103ba2e02c008180046062048160890025d1e4e84a8622020002060058450186d1e2504e0c0581908a7640c174789701635d876019818203b04002f4701800460161140c302008080da341f))))))
def rootData12 (i : Nat) : Nat := (if i < 4 then (if i < 2 then (if i < 1 then 0x4c89fff6049fff5c49fff5449fff4c49dff9569dff14a9dff88a9ff78ce7ffb88a7ffd8467dff5d9ddff205ddff145ddff085ddff845dbffaa9aeffa21abff69dadff65daf7f9ddafdf955affb889affd845adff2a17dffa217dff5d97dff2957dff2157dff9557dff5cd7dff58d7dff2857dff2057dff1457dff8457bffaa96dff6a56dff6596fbf9996ff78cd6dff6496ffb8896ffd8456effa215fbf9995ff78cd5ffd8455bffaa94bff6a14dff6614effa214bff69d4dff65d4f7f9dd4fbf5d94fdf9554fbf58d4ff78cd4dff6494ffb6094ffb8894ffd8454bffaa91dff6a51bff6a11dff6611effa211dff65d1f7f9dd1bff6991dff6591fbf9991fdf9551ff75cd1dff6491ffb6091ffb8891ffd8451dffa210dff61d0dff6190dff5d90dff2150dff9550dff60d0dff5cd0dff58d0dff6090dff2090dff5890dff1490dff4c90dff8890bffaa8fdff6a4fdff660feffa20fdff65cff7f9dcffbf298ffbf998fdff654ffdf954fdff64cfff78ccfdff648feff608fffb888fdff644fffd844fbffaa8ebff6a0edff660eeffa20ef7f61cedff658ef7f5d8efbf998edff654efdf954edff64ceff78ccedff648effb888edff644effd844edff65cdf7f9dcddff64cdff78ccdffb888dbffaa8cdff6a4cbff698cdff658cfbf998cfef690cdff64ccff78cccdff648cffb888cdff644cffd604cffd5c4cffd844cfefa20bfef61cbfef618bfef5d8bfef214bfef5d4bfef594bfef954bfef60cbfef5ccbfef58cbfef608bfef208bfef5c8bfef588bfef548bfef148bfef4c8bfef888bfef604bfef5c4bfef544bbffaa8adff6a4abff6a0adff660aeffa20abff69cadff65caf7f9dcabff698adff658afbf998abff694adff654afdf954afef550aff758cadff648aff74c8affb888adff644affd604afef504affd844abffaa89dff6a49bff6a09dff6609effa209bff69c9dff65c9f7f9dc9bff6989dff6589fbf9989bff6949dff6549fdf9549fef5509bff68c9dff64c9ff78cc9dff6489ffb5889ffb8889dff6449ffd5c49fef5049ffd4c49ffd8449ffe6982ffe5d82ffe6882ffe6082ffe2082ffe5c82ffe5882ffe8882ffe6842ffe6042ffe2042ffe5c42ffe5842ffe5442ffe1442ffe4842ffe0842ffe84429ffaaa9cffa229d7f9de9ddf9569df78ce9dfb88a9dfd84699ff6a679ffaa9ddbf999ddfd845d9ff6a5adbf659a9ffaa97cffa217d7f9dd7dbf9997ddf9557df78cd7dfb8897dfd84579ff6a569ff6a559ff6a549ffaa90cffa210d7f9dd0dbf9990ddf9550df78cd0dfb8890dfd84509ff6a4f9ff6a4e9ff6a4d9ff6a4cbefaa8bdef660beefa20bf6f9dcbdef658bfaf998bbef694bfcf954bfe78ccbdef648bfeb888bfed844b9ff6a4afed504a9ff6a49bfeaa82fbe9982dfe6482ffa8882fee5042ff64c42ffc8442 else 0x536a530252b0524851d5518e513150ea506c50254fd34f814eed4e594e1d4dcb4d6e4cda4c5c4be94b8c4af84a904a2849cb496348da484647a7472946d7464345d04589454d44b944464391431e428a422d41af4152411640823fee3f4f3edc3e5e3deb3da43d523c9d3c4b3bac3b443aa53a5339eb399939263900388d385c382b3797370e36a6365f362e35d1352734ca340a33a2333a32d23280324431d1315e312230d0308930422fda2f722f0a2ead2e502de82d962d442ce72c7f2c382be62b7e2b212aae2a5129c8295528d7284e27f1277e270b26b9265125f425b8254524d22480242323f2237f233822db2289222c21cf2193210a208c20191f901f331ec01e4d1e061da91d621d311cb31c1f1bc21b4f1ae71a5319f61962192618d4186c181a17bd176b172f16c7166a15f7158f153d14f6148e141b13b3134013041291124a11cc1185112810e11084105310010f830efa0e9d0e1f0dee0dc80d970d190ca60c750c440bfd0b950b220aba0a3c09f5098d093008de08ad0871084b07cd0765073406cc06850628060205b0057f054e050704e104a50453040c03d003940358031c02eb02ba027e024d021101e001990173012100f000a9007800470000fffaa9afff6a1afff69dafff695afff295afff955afff689afff289afff149afff889afff685afffaa96fff6996fff5d96fff68d6fff58d6fff6856fff2856fff1456fff8456fffa215fff6195fff2055fff8455fffaa94fff6a14fff69d4fff61d4fff6954fff2954fff9554fff68d4fff5cd4fff6094fff6854fffaa91fff6a11fff2a11fffa211fff69d1fff61d1fff6991fff5d91fff6951fff2951fff2151fff9551fff6091fff5891fff6851fff2851fff2051fff1451fff8451fffaa8ffff69cffff61cffff698ffff5d8ffff694ffff294ffff954ffff68cffff60cffff5ccffff58cffff688ffff288ffff608ffff5c8ffff588ffff548ffff148ffff4c8ffff888ffffaa8efff6a0efff2a0efffa20efff698efff618efff694efff594efff68cefff60cefff58cefff688efff608efff588efff548efff4c8efff604efff60cdfff5ccdfff5c8dfff548dfff148dfff888dfffaa8cfff698cfff5d8cfff68ccfff58ccfff688cfff288cfff608cfff208cfff588cfff4c8cfff888cfff604cfff5c4cfffaa8afff6a0afff2a0afffa20afff69cafff61cafff698afff618afff5d8afff694afff294afff214afff5d4afff594afff954afff688afff288afff608afff208afff5c8afff588afff548afff148afff888afff604afff5c4afff544afffaa89fff6a09fff2a09fffa209fff69c9fff61c9fff6989fff6189fff5d89fff6949fff2949fff6149fff2149fff5d49fff5949fff9549fff68c9fff60c9fff5cc9fff58c9fff54c9fff6089fff5889fff5489fff) else (if i < 3 then 0x570010c1098d8053ca1c9568043ee801802cfb00055a010cc6c02aad028108350010088d620e40580420500247b7580631a60e4e3040eb1602ebac160952441889c8bc58e61ac0c4fa97216a1347e89462c2703630091f43d66140bb1512e09d03987212302e0c41b8d1140bac300665eaf0be0e40210138310723d5c0f71a84220d80981941630e62649030c441e601160f4f983906e1906805fd5a1a8022826eac04e0e481609c827072406209868e2661809cc0f4598123e40e5760635f434d23040e81716554981122274188a4a86c0f33e2bb0921f05f218402241e8d60623c4b90b5a940144e2f71fab0247bcc2d475ea09cc390268171540eea286027434520f4350393dc3417705f00880980b4c202c5d8bb4139c20e1f06209c80f826aeb04e0e4b97005804183d0722cc280123db97c69add0c62f5605c60ae809ab00910623d82f12b7605061008407a0c4b90d609a3f57409c0d893d66e80beab58a09cc0f47203102e345600600cc8a6817c020c201ea09b8756e80404e70240101383125fc07202c02100911d06eba002027306b01601060f8f4a8b00809ca0f41c9e851618c5e8d33ad3598188298bc244607c79c1c80b0085248a2c718f300850b047569bec04e507a2716986c1fa530c79962827203e59801013901e86059819868942b86b0d4010804826db800809ca1fed6cf004e402479426ac000809cd487550271924886c6d5f8610083cce0b693aad04e408f498840c355a344c792b880404e4ad41080207f20471a15782f8040d46b219b1b1b149b0ecb06eafdaaf7daeffae76add7ad6facdbac5dabdfab77aae3aa5aa9fda9aba92da8a4a85da80ba7a3a746a6c8a681a5d7a564a51da489a42ca377a2e3a2b2a24aa1d7a190a0fca0c0a02c9fb99f469ebd9e8c9e2f9db19d339c9f9c2c9be59b939b369ab89a7c9a09998b995a991e98b6987a97e6977e97169661960f959c956094ed94649428937e9316928291f991a7913f90f89059901d8faa8f588ecf8e678dbd8d348ced8c598c288bcb8b378acf8a7289f489c38950891488ac8870883f87d7877a87128694865885cf857d84ff8481840e83b1836a832e82c6827f81f6818e80ef809d80357fd87f707f347ecc7e597de67d687d0b7cc47c257bd37b557acc7a1779c5794778ea7882782577e97781774576c7768b75f775c67574754374c5749f741673c4735172d37260720e718570db705d6fd46f4b6f256ea76e1e6dc16d856d1d6caa6c166bae6b1a6ade6aa26a7c69f369a1694468e7685e67d5677867056692662a65b7653964f264ab6417638e634762df625661cd6139610860b6606f5fdb5f685edf5e775e3b5dde5d555d035ca65c5f5c2e5bf25bb65b385ad05a3c59ea596c58ee5886583457c1575956f15652560b55a3556754f45476542453bc else 0x4d660800a65ed0aa81aa14426a2c0214c728b5a68147135a008701631c4cad3516014c02d661173148496998c5a8b016031d6211110b4c02254580b7580800209c5a61b002a5458055985e908004024e3013a54580441eb4d660538a209d083945805758d684400b00880720140680b51623d6612d30890160800987a59880d459c05ad340000ca0a01598751602d699fe06a22071004428b0a602c022cc0eeb4ca020d480b04024009acc00a6516014021b559911c139d458050160103306002634566240280b3d47f16613e0060110a2c0280b7580dcfd05300200c02294580b21cb308e8010060110058059633244e8026b40283380486a56ec0256e01220a02882c0204a05e09d402c1c92e7180149ceb37087f004b8958162c68280282d416bb4015ca70801013b0730d32c23a81cafa21693d00c47500525c026281643f4225362809373414008050314180109982751221e44ea26c50214934e58cc9035274e11ce8093f201120141f2eb004e740583900887d03d17c8f3008501658c0213a7060243710e02aad14058093fa00a82db080270601013a87320a00b1257b9725887890015b007f004e0c02027403973a2200210970125d85d58101902c0240c027512e1ccd622380958461cc4b8248d17cd13c8424b42dd00a0516000b094010e1d01c963d64e10049fc56a8412a2c0281459802c0180442930d2bb83500428492c66480593a752bb9ba8040123899330058180720c40bac01c404cf2804050b0731380280b272c91b2363012d6d40e40280a0900c405b6306e79576872008c1cc34cb0839024efd7d32340311d4015ab80b6e20249d0e2644a092821b980b0141c8711e50080c54488791df89a4ea26181316327002db788d1c4011002d8b0721c40e40219f40658960108034b18310164e5b68098945000ab1f5bfa062d5c0500507202c1b9523cad843900468e689231802831754bddb42224357062014059520e4d81f61e5500b2c64e402b5888e7dc04b674842024014058390621cc1b8723cac48fb804680b30c0485a2c55ea7ddb2a0a800501402c1caec1240ec1f0092747940c34a1b201103880214248a8186f980713a88c75ba0c4058925d07943904a0089062c84048891c44e9af1c24a8b0162496987200601101d0975876b0024fbab33a930c8fdc970042b1b00a9ad5682700081c008424b1b40cae15687d0088155fa0dab1b55aae00200c04e0000084250054d674413aad636810c2000480b0000f101b1b55a048e80ac0ab84028015698210053fec6e2187855a010ff258d8050840101e526000344842ad500565ac6cfe80c0fe000008274842886014f52add52c6c3e0043f8a016000008120085084c6cd28053f7115568043f400544798dabf0187e402193585865a0058d8270ea4755c10e018b0160700a1f8)) else (if i < 6 then (if i < 5 then 0xe33183a0fd8924e018baa2e519500c7348681124e9d718092ec3960141e02c51a05c0c13a04eb0e858e89c0c408ec4c345f30a87524209d4643874092a4dfb8040d518ce0142280b5807b72f8120400345e8631a6b75a0e4c82dd01604974031008b010a8803d85eda0f60507e5ba010a0f56eae80fa38a0500438c709602c4cae8002b7402a16e8b501701826845040270022e80d800402b56e97a00a8816004bd700107738c04eb02eb750f84d008ba1603668a209d41016e80580d0284400b00880620e4a300543c02c0684b5bab00c208f25ad43a02c090200261e901ac05ba904cb7418ae80161e0440e2008915c12c0582012004d6000542dd00a134e28e602eb02238274add00a870058e40ac04c020601a21996030c96b7274049dfa93072e8c020880124f9a0370e8393586c80900b006b741b88800804cf501f71b200a0481baed0901049f0ea3d407d634cb0a1b5f40387533f3a1a364048058498be0e43e0316e67a8460046922432254791df274ef626c5f7faa14b91d9e0ea012010c3d0328ea5f2010a8600900532a0ddb080b072fe8f53fe0f8011a58cd91f5128319d50055ef125fe282120761c6c80280b06ec481c9b0d6c0483e1ea3f8012002cc31f412e2d162af58587f1fda8f801207665d8100b6c80e5761ea0f801004b41c92e1ccce9b212d013189058c970491a248c500c375313df333858050161f1601ea27c1280220348642c6bb802141616377a6489700b66c010048896aa38a30b4188393244b9fa80b00918004c5f2f62259ab41c80502e0b0243f5016468fd8315da010f480171381d234e2f1615f40e40945d666a0724e09d163062fd4733348b82262dac0280b234bac1645a0023881c80450317eb1649c88900861d0fa07a0655f3160021c18805240fe80bb6107202c8d1fb06e4e04480442e00603f4632f70631249c457380b084694090050580e4fd831624dc8021fa002e18a02cc30b45eb0b0fd36c8ac9076bb0028170580e41891a016010049fb274005c344540c3062f989d3313add00a02d6011a002d982500448e75261a4322ee6aa010e4e42c84c42c12418b7323e53002289113917830161308f02606ec3b5a9f9018011402cc31f919c41cc4b81606620342c6e709700b2701a5d500402a02400b30683133400c1c8375d0fc00200f00247409b0131630171549d0098a8054022405aeb2380041c80433e80cabe4021001bec5a64380780123a04d00d00903162402c210390181d61c84d23a010870017986024bd405ac56ba439d2a01a03b5d80c4c9c4a0186689d0392380140580423a02400c49c12e1a2f986183175313d95a56e8310164716011d00212802241c96332514c0abe97fc025f3a4acded8a4004049387c47526190c92ee008500a02d661e80400345e8631a6a2d40e54580b008b else 0x3ef24981a00681901683db1b56922024188891247dc9d4907809016d8dab08d85e0601c8e23ee011601c0680b6c60c402c8f012054711f74d4c0920e5ab1479147440c0091d40109d48e60390083886d8e46c8a4560600a80900a0109d48c580b6c6d58e5009031030210042747de45b0b1b56914ff80913a00802500c41b93a1c4024ad8c0a8319141d49d1380080252125b18126ac02dc193a3ee01004aa4480b7e41b0268b508a7d44e00462c25002b515229016028480262febac02a64492300a8700584b0c0124020a01a219975b40598640ac564414188d127521dc8141cc860083016108bb30e8720c58907d00881503313622806e00405812048010e89c0a049016080fc43900882008980600b3ecc4812004405f61c35002834084c480a0370d400402300b00b2c6098c913a3e80118a8f3111215834cb0bbf5f40e4858ea90882c66489703101a4e50288811320d40580904c44a0c5b98041904e413a84a92289a3c89d3bd2144e641247304c129125d50055ee7d4b948150e625c894500d17ccea6279082472016a4c34aee0721a8021a3f82001202d7603b303b3d001405c2a08a4e8208205f418c69aec680b0585d80baec062c080207d27481982b01000901802d8103b322460822805899604005760054aec5ee4242283b0082d41009c60403002b17601200a0761501730ec144481927409d805816a2300a1321513a058bb216c7e03009da00405a8d0764444114058015d8064021c2280b04006181004303b0bebb06a0050147b88493a0120040c804682e0166480913a009055f32fa6a0a07202c08031256bb40caec058088c2018600400a02c2588f09abacc203948658960107547d280b30c2d0092f558a81211a02680502402c068390761657613a3080618344540c32c6ea49d47c39630d2191498395dc0123da09c16344234d7d47a3124272be63c9005986400bd63c149c00e06ebba3b94171635f24e005c13008220918e269cb04c4e00580d69b1002e8ea8ec904c1200281706202c1608d3febb43c0ea008d1a686ddf8396c43aa3a9c941928e404a3a00d06a4e8440e2696b05805c0587805c868713733fe01018ac4a92289a3c8efbbd2744e639a4134726944e84413977c71cc2507ec4918cea89c0313eb1c551c0973bc04c02e169fe1111bd225c05986024b15ae9fe3e91b920b81d84c1240140b80b01a0f97613a3fe7c00cb81ca9f6982207546d30a01a2f98540c375248c9d46c4a930c80e5fb80428172c6bd405938009ae8840688d6a024c4b5c82f3960f00c82c04806013ac059380090323520476472c672c028175b80b2062ed04e90e834c0936277e42e349c0bb7338a029fb068cde09c18a49144d1e4ef48513a8d072c60d49c00d8cf0b4ff088828902472c0284907205e33aeb13409d4fa2258048ce3c) else (if i < 7 then 0xc0732a230031008fd444809483101afd6588e20026474034748d302a586542fa8ba4e809001666fd5c0c4020891c4024a0247503934e78918c40960fd402289c00d0580c44480101271c453dfaca845b2741c83111a0249c004600d059b049d0317ea7e844809480d47202d164940724e11c46a01204a579fa1c52b9e3886400b7ea7761688d0732b4449fa008c2740c4160891c4024c064c229f07251e54031008048008092752b1a0e4188041c4441a4e11583195602655089403c032034da9ca0aafd6060010127e89d4a9696306e6565401227117c02009480b45929c024a61d47e4b7a04499d01683c46ca71240109c9f92c8b09e0b253141218011a224a64a502a0100c139280a09315002809018525c234ceca505915002066012901c0d00281500250720100600920092720c4440cf9484e1f8804480d65db035fbf121c05404a00488d0170b41c815002438022406bed271af818ebd94328df880902ab7d603406009002525c610188399420114f81502402400c3d604940604a253e902a024e02418ca124c0e4098e202a2200080459b5062012060150161a00480121d28963449c4a1186fa5f313a06201404a8b183e8bf2840913800802500c41b93800802400980b00d016008049405b89d660e4023833f8e1004a405015017281c2002301407434dc10152c2d617d00d70893c09300580d4d8e11ceb833f514004a40a16e0160910a8397043a8448090091411bb88700b73ae11c19f9008024e0247500b05e78a2021370801120249c80b11022502b9d00880160355a015b82e1087383012901402dc1c9f004507454d8200b012e0dc2012102927002c06a1293d25804a36706e154051c238329e0e404c9d02a84402280a384012bdcbac4900a5c9c1804102b017af35d80a708e0cfb809400a6b00340580201260284b8058243080e40c8ea70708002009409271c02d01a356b0e1009009393a01682d00a3483a00c04a006b0ca56050058137086a804819706388441fe008c0284b805a0d70822499c8d0331400a8042d802519b28804900b26c05910706024ee11c10a80e84b9f300a6b001084009583e2c6e0dff00b3f801004a1c23f5705140059383f401004a5c20157064e08700b00802504b82480d1c4024a125b2039914c90023576c602521240ab63934388a820068d36ac05645362024389b1b23593a0620dc71009280d42a8c81cb569140c4448120122489d49968390083880490048ea0728c64c36300872720c4020e2200d0920549d031b3f229b6b636ae0256124a90e2180d4600c41cc8a45e0564b8092e238a1e3006953024025abb632a472700c406a1245d2580493a6af2554024a7b630632291683927005471004580d6c631826c493ee014493572a4a6b1660053636ae7dc049c0680b4592501cb56926024090e2 else (if i < 8 then 0x9c341128141313990622121087543485e09908cd611082e25b00c00149205805c2f04c920eeac4a08d2e30d17b8010987d402c2f0085c8eeb4210189a70b4131fe9aa22108961216c0122492380b04c91a16cd4585d44a914b880900201405a292210b4eeb11297c11af9a698a80122489183b00842216c8076ca9a60240c42d3f209802088482e3080a665c155f4f980c12d27404800350683905d100094d205f080968181d534564e41c9d6044900678041d44ea6829f59840531ab64c2025a06102426498401691265ccf85e4e80c039110810754ce69840120a5b24cd07204a6642025a06210b00a16305c4b8008180004b501241488301a0621012d3963996190248013080489d01801a4b564e910a01270054340242821220ec7a5f4c27480521c1d995100c58c0a82483a0de64941380e2748060e9384000dd77141482e04c4b81780469c23471207502e88130da682f03009a39476110b2720b01334b1c4220c248ffa1583730d2145c0620e44485d1d44e89ccc879ff2720c661cc703009a394c6110a04c4b81782e354388c250441719863180084c3ea24802c720086a9a7fe1681804d1c8ff4c511081241a00ba4101683c0941b8a20c51f0891107f89d4c4801830906ca3cc33a20be270390084e87546d682600838844102100a8192f09700b11c1a01e24058428d48100c4be81b030003b2501501402c3440c07860781081d0d39780565f13e6c44ea06469024d27402c0bbaf0d0507858c2102442b2f02a88911d1711b93a984d01610a168188cf0320688e00105144e4059c940c9004413a40b3066028058428180549d031d900604740d0012fd802805c0d078407454c9f00b819034091ca440c2e21342106811c1b00297281a72972f0a3c4e03012c470ea0168109d3b158428182225e1aa97c0623380b0084e8ff4bd680b085031ac0090310344700081ca25c0280586811c0f0c0280a8010160600908e39382e2028058183f1034472206293978124008180d40342106811cb2c60fc0693e0125053b1c4401297717c1c8047fc02548565923f0120a40913a01b17c754ba58390084f804909c839972010441414ec611004a5c0397fc01004a4b183f7fc6549f149f09418c0257b9970527d4090057fc010cab414ec5d882201cbfe0087f004a41480b4588e2351fc1d52dc0924341a801a02d078882e72c80fa3e8be0244493e3f92da002e590396c87f0020883829d87b084401296a0e5ff004012a076035b213e012530851c14bfe0240249d00d1d518944e81ba011105591a20225002401b64968c072049ff004110501a8344488c1102e00922b8be8f4048152d84fa1fbc248291105fd1e005452ff804a40680b36a2204d1ca476ff83400927c7f259b4068a09642a0090c309248c1db641d402580c5aa82c01a22404801382 else 0x5ecc1cc060130f390a22103a8216cb9a70b4132139ae221210a6))))
def rootData13 (i : Nat) : Nat := 0xb03a89c2052743989ca0640260b0648970ea27216c7302d488a0b06483a00d4083a89d184405a2724e10013a402604c160c90743fc3a82d93a1cc7fd4160b19921cd19c9d02d36a80b016c1c9920e84ea2f9fc1d4398f52c188582c61d0fd138274678731fb50581d44e4fc80428582c61d09710e2703988ea02e042c1633244ea280e605a1fd0160b19920e87dc9d0e63ca80b010b216c0e82d07c1689c85807209c022c2c81d0b40f8213728880b405858505905a0741f47e0164e82c200e82d0b2169b305804e011014c0585800840851162185805a543198d71218be0b890c593a993650c47c430ff9c5b4f5e4b8942a284308610c21833449c6506d078003ffd3ffe7ffeffff77ffb5ffd8ffebfff5bffabffd4ffe97ff47ffa1ffcfffe77ff37ff99ffcbffe57ff27ff8bffc2ffe0fff02ffd37fddbfebdff43f797ff82
def sixIds : Nat → Nat → Nat
  | 8 => sid8
  | 9 => sid9
  | 10 => sid10
  | 11 => sid11
  | 12 => sid12
  | 13 => sid13
  | _ => fun _ => 0
def directStart : Nat → Nat
  | 8 => 0
  | 9 => 46
  | 10 => 976
  | 11 => 2373
  | 12 => 456
  | 13 => 30
  | _ => 0
def sixRowsData (i : Nat) : Nat := 0x22b14caa8440a229168ac0e0501825120c6a340a9a1d06c4230088090682c4c24111a0d16940f0302c0f07064a2402a034181928900a8142a0c0c0401028160aa2d1489192c86cc5609162130888844001028541a180802303c1c1b29908a68361a80c2411229548b1c8e03260701c124820900a850aaa11028c0e270a0d048148ac532c92082468741b188c0220a1502c4220008194c875088102a034181948a012456295520810888b4532cd22834194c8e54080101150a6550200c0446215120800800a8512aa1102804c245330880c181c070482002022d04cb248209050a8163118044c0e1706060200a094483309808222d14c320820820984922a11028c0f0606c260209149a45c4621012251099088002114aa4588450098261248a241089a0d86a030100468349a383c16048b4532c820824343a058c460112094483108800268351a4160a04b03c1819088002825120c4a2402844a213311804468741b189c0a270385c1c5a2912190e86c2c1409061301c422000802a144aa24108920984a0301004142a05984c0410d06a3480c140968361a84d24915149a458442001343a0d8c4601106532395160a454542995c0c03030385c181a0902112884d84c0410241a0b0341205c0f0706c260208130914c8200208a5522c522804a034181908800220d04c3208008229949a2c1203011488c5448211044a2132110004090682c0c040108b4526c26020922b14cae0601830385c1c1a0902194c8e54180905a0d86a13090444562995c0c03004522315020040452a9162914024150a2551208440506816110800450381484420014562955228108a09849228100200542895408010065321d42a040a22d14cb24820900a8512a810020
def rootLevels : Nat → Packing
  | 8 => (2,7,11,0,0,0,0,rootData8)
  | 9 => (184,6,11,0,0,7,0,rootData9)
  | 10 => (2292,5,11,0,0,14,0,rootData10)
  | 11 => (3758,4,11,0,0,17,0,rootData11)
  | 12 => (456,3,11,0,0,16,0,rootData12)
  | 13 => (30,2,11,0,0,11,0,rootData13)
  | _ => emptyPacking
def rootIndex : Nat → Nat → Option (Nat × Nat)
  | 9 => lookupWord 2 5 0 9 1 4 rootLink8
  | 10 => lookupWord 83 269 6 16 8 4 rootLink9
  | 11 => lookupWord 1087 3467 8 20 12 4 rootLink10
  | 12 => lookupWord 1979 6323 9 20 12 4 rootLink11
  | 13 => lookupWord 229 739 7 17 9 4 rootLink12
  | 14 => lookupWord 23 67 4 13 5 4 rootLink13
  | _ => fun _ => none
def seedForest : Forest :=
  (511,15,fun j => deadsamples[j]?.getD (0,0),deadcolumns,deadautos,rootLevels,rootIndex)

theorem seedGeometry : graphValid seedForest (boundsBefore known383) = true := geomdead

def cheapAt (c : NodeContext) (i j op : Nat) :=
  let z := (movedDecor op (contextWire c i) (contextWire c j)).1
  !properB z || c.2.2.1.any (fun v => v.1 == z)

theorem cheapSound (c : NodeContext) (i j op : Nat) (ka kb : Bool) (h : cheapAt c i j op = true) :
    checkAt c i j op ka kb = true := by
  rcases c with ⟨cap,n,ws,cov,pools,links⟩
  simp only [cheapAt,contextWire] at h
  simp only [checkAt,contextWire,evalMove,h,ite_true] <;> repeat' first | rfl | split

abbrev Cached := NodeContext × List QuickPool
def hot (c : NodeContext) : Cached := (c,c.2.2.2.2.1.map (summarizePool c.2.2.1))
def cachedAt (q : Cached) (i j op : Nat) (ka kb : Bool) :=
  let c := q.1
  cheapAt c i j op ||
   ((if i<c.2.2.1.length ∧ j<c.2.2.1.length then
     q.2.any (fun s => fastCost s (c.1-1) (contextWire c i) (contextWire c j) op ka kb) else false) ||
    checkAt c i j op ka kb)
theorem hotAt (c : NodeContext) (i j op : Nat) (ka kb : Bool) :
    cachedAt (hot c) i j op ka kb = fallbackAt c i j op ka kb := by
  change (cheapAt c i j op || fallbackAt c i j op ka kb) = _
  cases h : cheapAt c i j op
  · rfl
  · have yes := cheapSound c i j op ka kb h
    simp [fallbackAt,yes]

theorem mappedMarks {α β : Type} (f : β → Bool) (g : α → β) (m : Nat) (xs : List α) :
    onMarks f m (xs.map g) = onMarks (fun x => f (g x)) m xs := by
  induction xs generalizing m with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons,onMarks,ih]

def hotMove (b : Batch) (xs : List Cached) (i j op : Nat) (ka kb : Bool) :=
  let (k,n,r,_,u,v) := b
  let un := op==2
  let len := 1+(n-(if ka then 0 else 1)-(if un || kb then 0 else 1))
  if len>k then true else
    let d := len==k
    let a := laneWire b i
    let b' := laneWire b j
    let z := packedOp (r*(BitVec.allOnes 768).toNat) op a b'
    let cov := if d then v else u
    let mask := fullMarks r (takePacked cov (packedColumn d a) (packedColumn d b') un ka kb ||| packedColumn d z)
    onMarks (fun c => cachedAt c i j op ka kb) mask xs

theorem hotMove_eq (b : Batch) (xs : List NodeContext) (i j op : Nat) (ka kb : Bool) :
    hotMove b (xs.map hot) i j op ka kb = batchMove b xs i j op ka kb := by
  rcases b with ⟨k,n,r,ws,u,v⟩
  simp only [hotMove,batchMove,mappedMarks,hotAt]

def hotPair (b : Batch) (xs : List Cached) (i j op : Nat) :=
  let f := hotMove b xs i j op
  f false false && f true false && f false true && f true true
def hotRow (b : Batch) (xs : List Cached) (i : Nat) (js : List Nat) :=
  hotMove b xs i i 2 false false && hotMove b xs i i 2 true true &&
    js.all (fun j => hotPair b xs i j 0 && hotPair b xs i j 1)
theorem hotRow_eq (b : Batch) (xs : List NodeContext) (i : Nat) (js : List Nat) :
    hotRow b (xs.map hot) i js = batchRow b xs i js := by
  simp only [hotRow,batchRow,hotPair,batchPair,hotMove_eq]

def hotCut (g : Forest) (k start n ar : Nat) :=
  let xs := contexts g k start n
  let cs := xs.map hot
  let b := makeBatch k ar xs
  (List.range ar).all (fun i => hotRow b cs i (List.range' (i+1) (ar-(i+1))))
theorem hotCut_eq (g : Forest) (k start n ar : Nat) :
    hotCut g k start n ar = rowCut g k start n ar 0 ar := by
  simp only [hotCut,rowCut,Nat.zero_add,hotRow_eq]

def hotCells (g : Forest) (k start n ar : Nat) : Nat → Prop
  | 0 => header g k start n ar = true ∧ hotCut g k start n ar = true
  | d+1 => hotCells g k start (n/2) ar d ∧ hotCells g k (start+n/2) (n-n/2) ar d
theorem hotBlock {g k start n ar d} (h : hotCells g k start n ar d) :
    block g k start n = true := by
  induction d generalizing start n with
  | zero => exact cutsBlock h.1 (by rw [← hotCut_eq]; exact h.2)
  | succ d ih =>
    have e := block_merge (ih h.1) (ih h.2)
    simpa only [Nat.add_sub_of_le (Nat.div_le_self n 2)] using e

abbrev Six := BitVec 6
def sixGood (v : Six) : Bool := (0xf1000000e1f1f1f1 : Nat).testBit v.toNat
def traceA (v : Six) := (v.getLsbD 1 != v.getLsbD 2) || (v.getLsbD 5 != v.getLsbD 3)
def traceB (v : Six) := (v.getLsbD 0 != v.getLsbD 2) || (v.getLsbD 5 != v.getLsbD 4)
def apart6 (a b : Six) := !(traceA a && traceA b || traceB a && traceB b)
def merge6 (d : Bool) (a b : Six) := if d then a ||| b else a &&& b

set_option maxHeartbeats 0 in
theorem sixClosed : ∀ (d : Bool) (a b : Six), sixGood a = true → sixGood b = true →
    apart6 a b = true → sixGood (merge6 d a b) = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem traceParent (d : Bool) (a b : Six) :
    (traceA (merge6 d a b) = true → traceA a = true ∨ traceA b = true) ∧
    (traceB (merge6 d a b) = true → traceB a = true ∨ traceB b = true) :=
  (by decide +kernel : ∀ (d : Bool) (a b : Six),
    (traceA (merge6 d a b) = true → traceA a = true ∨ traceA b = true) ∧
    (traceB (merge6 d a b) = true → traceB a = true ∨ traceB b = true)) d a b

theorem apartNext (d : Bool) (a b c : Six) (ha : apart6 a c = true) (hb : apart6 b c = true) :
    apart6 (merge6 d a b) c = true := by
  exact (by decide : ∀ (a b c e u v p q : Bool),
    (u = true → a = true ∨ b = true) → (v = true → c = true ∨ e = true) →
    (!(a && p || c && q)) = true → (!(b && p || e && q)) = true →
    (!(u && p || v && q)) = true) _ _ _ _ _ _ _ _ (traceParent d a b).1 (traceParent d a b).2 ha hb

theorem swapApart (a b : Six) : apart6 a b = apart6 b a := by simp [apart6,Bool.and_comm]

def shape6 (r : Fin 6 → Row) (S : Finset Sig) : Prop :=
  (∀ a ∈ S, sixGood (ofRows r a) = true) ∧
  ∀ a ∈ S, ∀ b ∈ S, a ≠ b → apart6 (ofRows r a) (ofRows r b) = true

theorem fullTree {T k t S} (r : Fin 6 → Row) (h : Live T k t S) :
    S.card = k+1 → shape6 r S → sixGood (ofRows r T) = true := by
  induction h using Live.induct with
  | stop hp => exact fun _ ok => ok.1 T (Finset.mem_singleton_self T)
  | @unary k t U a ha hf tail ih =>
    intro sz _
    have n := (live_size tail).2
    have fresh : neg a ∉ U := fun hm => hf (Finset.mem_insert_of_mem hm)
    rw [Finset.card_insert_of_notMem fresh] at n
    have cs := Finset.card_insert_le a U
    omega
  | @binary k t U a b d ha hb hab hf tail ih =>
    intro sz ok
    let z := bin d a b
    have fresh : z ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    have n := (live_size tail).2
    change (insert z U).card + t ≤ k+1 at n
    rw [Finset.card_insert_of_notMem fresh] at n
    have ca := Finset.card_insert_le a (insert b U)
    have cb := Finset.card_insert_le b U
    have na : a ∉ insert b U := by
      intro hm
      rw [Finset.insert_eq_of_mem hm] at sz
      omega
    have nb : b ∉ U := by
      intro hm
      rw [Finset.insert_eq_of_mem hm] at sz
      have cu := Finset.card_insert_le a U
      omega
    have nu : a ∉ U := fun hm => na (Finset.mem_insert_of_mem hm)
    have am : a ∈ insert a (insert b U) := Finset.mem_insert_self _ _
    have bm : b ∈ insert a (insert b U) := Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
    have up {v : Sig} (hv : v ∈ U) : v ∈ insert a (insert b U) :=
      Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hv)
    have op : ofRows r z = merge6 d (ofRows r a) (ofRows r b) := ofRows_bin r d a b
    have away {q : Sig} (hq : q ∈ U) : apart6 (ofRows r z) (ofRows r q) = true := by
      rw [op]
      apply apartNext
      · exact ok.2 _ am _ (up hq) (fun e => nu (e.symm ▸ hq))
      · exact ok.2 _ bm _ (up hq) (fun e => nb (e.symm ▸ hq))
    apply ih
    · change (insert z U).card = k+1
      rw [Finset.card_insert_of_notMem fresh]
      omega
    constructor
    · intro q hq
      rcases Finset.mem_insert.mp hq with rfl | hu
      · rw [op]
        exact sixClosed d _ _ (ok.1 _ am) (ok.1 _ bm) (ok.2 _ am _ bm hab)
      · exact ok.1 _ (up hu)
    · intro q hq v hv ne
      rcases Finset.mem_insert.mp hq with eq | hqu
      · subst q
        rcases Finset.mem_insert.mp hv with eq | hvu
        · exact (ne eq.symm).elim
        · exact away hvu
      · rcases Finset.mem_insert.mp hv with eq | hvu
        · subst v
          rw [swapApart]
          exact away hqu
        · exact ok.2 _ (up hqu) _ (up hvu) ne

def sixOK : List Six → Bool
  | [] => true
  | a :: xs => sixGood a && xs.all (apart6 a) && sixOK xs

theorem initSix {r : Fin 6 → Row} (ws : List Sig) (h : sixOK (ws.map (ofRows r)) = true) :
    shape6 r ws.toFinset := by
  induction ws with
  | nil => simp [shape6]
  | cons a xs ih =>
    simp only [List.map_cons,sixOK,Bool.and_eq_true] at h
    have old := ih h.2
    have noOverlap (v : Sig) (hv : v ∈ xs) : apart6 (ofRows r a) (ofRows r v) = true :=
      List.all_eq_true.mp h.1.2 _ (List.mem_map.mpr ⟨v,hv,rfl⟩)
    constructor
    · intro v hv
      rcases List.mem_cons.mp (List.mem_toFinset.mp hv) with rfl | hx
      · exact h.1.1
      · exact old.1 _ (List.mem_toFinset.mpr hx)
    · intro u hu v hv ne
      rcases List.mem_cons.mp (List.mem_toFinset.mp hu) with rfl | ux <;>
        rcases List.mem_cons.mp (List.mem_toFinset.mp hv) with rfl | vx
      · exact (ne rfl).elim
      · exact noOverlap _ vx
      · rw [swapApart]; exact noOverlap _ ux
      · exact old.2 _ (List.mem_toFinset.mpr ux) _ (List.mem_toFinset.mpr vx) ne

def directRows (q : Nat) (i : Fin 6) : Row :=
  Fin.ofNat 512 (packedAt sixRowsData (54*q+9*i.val) 9)
def directCheck (k i : Nat) :=
  let ws := stateSet seedForest k i
  let r := directRows (packedAt (sixIds k) (7*(i-directStart k)) 7)
  decide ws.Nodup && (ws.length == k+1) && !sixGood (ofRows r (targetOf seedForest)) &&
    sixOK (ws.map (ofRows r))
theorem directSound {k i : Nat} (pass : directCheck k i = true) :
    Impossible (targetOf seedForest) k (stateSet seedForest k i).toFinset := by
  simp only [directCheck,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq,Bool.not_eq_true'] at pass
  intro n t hn run
  have eq := List.toFinset_card_of_nodup pass.1.1.1
  have len := pass.1.1.2
  have sz := (live_size run).2
  have ex : (stateSet seedForest k i).toFinset.card = n+1 := by omega
  have yes := fullTree _ run ex (initSix _ pass.2)
  exact Bool.noConfusion (yes.symm.trans pass.1.2)

def directBlock (k start : Nat) : Nat → Bool
  | 0 => true
  | n+1 => directCheck k (start+n) && directBlock k start n
theorem directAt {k start n : Nat} (ok : directBlock k start n = true) (i : Nat)
    (lo : start ≤ i) (hi : i < start+n) : directCheck k i = true := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [directBlock,Bool.and_eq_true] at ok
    by_cases eq : i=start+n
    · exact eq.symm ▸ ok.1
    · exact ih ok.2 (by omega)

def Zone (k s n : Nat) := ∀ i, s ≤ i → i < s+n →
  nodeVerified seedForest k i = true ∨ directCheck k i = true
theorem zoneBlock {k s n} (pass : block seedForest k s n = true) : Zone k s n :=
  fun i lo hi => Or.inl (block_at pass i lo hi)
theorem zoneDirect {k s n} (pass : directBlock k s n = true) : Zone k s n :=
  fun i lo hi => Or.inr (directAt pass i lo hi)
theorem zoneJoin {k s a b} (h : Zone k s a) (j : Zone k (s+a) b) : Zone k s (a+b) := by
  intro i lo hi
  by_cases before : i<s+a
  · exact h i lo before
  · exact j i (by omega) (by omega)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem fit8x0 : Zone 8 0 2 := by
  apply zoneDirect
  decide +kernel
theorem allFit8 : Zone 8 0 2 := fit8x0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem fit9x0 : Zone 9 0 46 := by
  apply zoneBlock
  apply hotBlock (ar:=9) (d:=0)
  simp only [hotCells,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem fit9x46 : Zone 9 46 138 := by
  apply zoneDirect
  decide +kernel
theorem allFit9 : Zone 9 0 184 := (@zoneJoin 9 0 46 138 fit9x0 fit9x46)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem fit10x0 : Zone 10 0 8 := by
  apply zoneBlock
  apply hotBlock (ar:=9) (d:=0)
  simp only [hotCells,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem fit10x8 : Zone 10 8 256 := by
  apply zoneBlock
  apply hotBlock (ar:=10) (d:=3)
  simp only [hotCells,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem fit10x264 : Zone 10 264 256 := by
  apply zoneBlock
  apply hotBlock (ar:=10) (d:=3)
  simp only [hotCells,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem fit10x520 : Zone 10 520 256 := by
  apply zoneBlock
  apply hotBlock (ar:=10) (d:=3)
  simp only [hotCells,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem fit10x776 : Zone 10 776 199 := by
  apply zoneBlock
  apply hotBlock (ar:=10) (d:=3)
  simp only [hotCells,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem fit10x975 : Zone 10 975 1 := by
  apply zoneBlock
  apply hotBlock (ar:=11) (d:=0)
  simp only [hotCells,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem fit10x976 : Zone 10 976 256 := by
  apply zoneDirect
  decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem fit10x1232 : Zone 10 1232 256 := by
  apply zoneDirect
  decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem fit10x1488 : Zone 10 1488 256 := by
  apply zoneDirect
  decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem fit10x1744 : Zone 10 1744 256 := by
  apply zoneDirect
  decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem fit10x2000 : Zone 10 2000 256 := by
  apply zoneDirect
  decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem fit10x2256 : Zone 10 2256 36 := by
  apply zoneDirect
  decide +kernel
theorem allFit10 : Zone 10 0 2292 := (@zoneJoin 10 0 976 1316 (@zoneJoin 10 0 520 456 (@zoneJoin 10 0 8 512 fit10x0 (@zoneJoin 10 8 256 256 fit10x8 fit10x264)) (@zoneJoin 10 520 256 200 fit10x520 (@zoneJoin 10 776 199 1 fit10x776 fit10x975))) (@zoneJoin 10 976 768 548 (@zoneJoin 10 976 256 512 fit10x976 (@zoneJoin 10 1232 256 256 fit10x1232 fit10x1488)) (@zoneJoin 10 1744 256 292 fit10x1744 (@zoneJoin 10 2000 256 36 fit10x2000 fit10x2256))))
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem fit11x0 : Zone 11 0 2 := by
  apply zoneBlock
  apply hotBlock (ar:=9) (d:=0)
  simp only [hotCells,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem fit11x2 : Zone 11 2 256 := by
  apply zoneBlock
  apply hotBlock (ar:=10) (d:=3)
  simp only [hotCells,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem fit11x258 : Zone 11 258 6 := by
  apply zoneBlock
  apply hotBlock (ar:=10) (d:=0)
  simp only [hotCells,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem fit11x264 : Zone 11 264 256 := by
  apply zoneBlock
  apply hotBlock (ar:=11) (d:=3)
  simp only [hotCells,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem fit11x520 : Zone 11 520 256 := by
  apply zoneBlock
  apply hotBlock (ar:=11) (d:=3)
  simp only [hotCells,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem fit11x776 : Zone 11 776 256 := by
  apply zoneBlock
  apply hotBlock (ar:=11) (d:=3)
  simp only [hotCells,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem fit11x1032 : Zone 11 1032 256 := by
  apply zoneBlock
  apply hotBlock (ar:=11) (d:=3)
  simp only [hotCells,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem fit11x1288 : Zone 11 1288 256 := by
  apply zoneBlock
  apply hotBlock (ar:=11) (d:=3)
  simp only [hotCells,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem fit11x1544 : Zone 11 1544 256 := by
  apply zoneBlock
  apply hotBlock (ar:=11) (d:=3)
  simp only [hotCells,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem fit11x1800 : Zone 11 1800 256 := by
  apply zoneBlock
  apply hotBlock (ar:=11) (d:=3)
  simp only [hotCells,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem fit11x2056 : Zone 11 2056 256 := by
  apply zoneBlock
  apply hotBlock (ar:=11) (d:=3)
  simp only [hotCells,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem fit11x2312 : Zone 11 2312 38 := by
  apply zoneBlock
  apply hotBlock (ar:=11) (d:=0)
  simp only [hotCells,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem fit11x2350 : Zone 11 2350 23 := by
  apply zoneBlock
  apply hotBlock (ar:=12) (d:=0)
  simp only [hotCells,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem fit11x2373 : Zone 11 2373 256 := by
  apply zoneDirect
  decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem fit11x2629 : Zone 11 2629 256 := by
  apply zoneDirect
  decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem fit11x2885 : Zone 11 2885 256 := by
  apply zoneDirect
  decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem fit11x3141 : Zone 11 3141 256 := by
  apply zoneDirect
  decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem fit11x3397 : Zone 11 3397 256 := by
  apply zoneDirect
  decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem fit11x3653 : Zone 11 3653 105 := by
  apply zoneDirect
  decide +kernel
theorem allFit11 : Zone 11 0 3758 := (@zoneJoin 11 0 1800 1958 (@zoneJoin 11 0 520 1280 (@zoneJoin 11 0 258 262 (@zoneJoin 11 0 2 256 fit11x0 fit11x2) (@zoneJoin 11 258 6 256 fit11x258 fit11x264)) (@zoneJoin 11 520 512 768 (@zoneJoin 11 520 256 256 fit11x520 fit11x776) (@zoneJoin 11 1032 256 512 fit11x1032 (@zoneJoin 11 1288 256 256 fit11x1288 fit11x1544)))) (@zoneJoin 11 1800 829 1129 (@zoneJoin 11 1800 512 317 (@zoneJoin 11 1800 256 256 fit11x1800 fit11x2056) (@zoneJoin 11 2312 38 279 fit11x2312 (@zoneJoin 11 2350 23 256 fit11x2350 fit11x2373))) (@zoneJoin 11 2629 512 617 (@zoneJoin 11 2629 256 256 fit11x2629 fit11x2885) (@zoneJoin 11 3141 256 361 fit11x3141 (@zoneJoin 11 3397 256 105 fit11x3397 fit11x3653)))))
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem fit12x0 : Zone 12 0 58 := by
  apply zoneBlock
  apply hotBlock (ar:=10) (d:=1)
  simp only [hotCells,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem fit12x58 : Zone 12 58 230 := by
  apply zoneBlock
  apply hotBlock (ar:=11) (d:=3)
  simp only [hotCells,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem fit12x288 : Zone 12 288 168 := by
  apply zoneBlock
  apply hotBlock (ar:=12) (d:=2)
  simp only [hotCells,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allFit12 : Zone 12 0 456 := (@zoneJoin 12 0 58 398 fit12x0 (@zoneJoin 12 58 230 168 fit12x58 fit12x288))
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem fit13x0 : Zone 13 0 6 := by
  apply zoneBlock
  apply hotBlock (ar:=10) (d:=0)
  simp only [hotCells,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem fit13x6 : Zone 13 6 24 := by
  apply zoneBlock
  apply hotBlock (ar:=11) (d:=0)
  simp only [hotCells,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allFit13 : Zone 13 0 30 := (@zoneJoin 13 0 6 24 fit13x0 fit13x6)
theorem rootZones (k : Nat) (hk : k ≤ 13) : Zone k 0 (rootLevels k).1 := by
  interval_cases k
  · intro i lo hi; change i < 0 at hi; omega
  · intro i lo hi; change i < 0 at hi; omega
  · intro i lo hi; change i < 0 at hi; omega
  · intro i lo hi; change i < 0 at hi; omega
  · intro i lo hi; change i < 0 at hi; omega
  · intro i lo hi; change i < 0 at hi; omega
  · intro i lo hi; change i < 0 at hi; omega
  · intro i lo hi; change i < 0 at hi; omega
  · exact allFit8
  · exact allFit9
  · exact allFit10
  · exact allFit11
  · exact allFit12
  · exact allFit13
theorem reachableSound (k : Nat) (hk : k ≤ 13) :
    ∀ i < (seedForest.levels k).1, Impossible (targetOf seedForest) k (stateSet seedForest k i).toFinset := by
  have geo := seedGeometry
  simp only [graphValid,Bool.and_eq_true,List.all_eq_true,beq_iff_eq] at geo
  have step (n : Nat) (hn : n ≤ 13) (prior : n>0 → ∀ j < (seedForest.levels (n-1)).1,
      Impossible (targetOf seedForest) (n-1) (stateSet seedForest (n-1) j).toFinset) :
      ∀ i < (seedForest.levels n).1, Impossible (targetOf seedForest) n (stateSet seedForest n i).toFinset := by
    intro i hi
    rcases rootZones n hn i (Nat.zero_le _) hi with h | dh
    · exact nodeVerified_sound seedForest n i (chart_pairs geo.1.1.1 geo.1.1.2)
        (fun ci hc => col_sound ci _ (before_sound _ valid383) (geo.1.2 ci hc)) geo.2 prior h
    · exact directSound dh
  induction k with
  | zero => exact step 0 hk (by omega)
  | succ k ih => exact step (k+1) hk (fun _ => by simpa using ih (by omega))

def pivots (i : Nat) : Nat := 0x4010040100810040108024080200804080200840100501004020401004200802048020102008021004010040100810040108020080200804080200840100401004020501004200802008020102024021004010040100810040108020080200804080200840120401004020401004200802008020102008021044410040100810040108100090000804080200840400401400020401004203002008030102008021004010040100c00040108090080200804090200840140401004020401404200902008020102008031004014040100810040108222080200804080200840100401004020401004200822208020102008021004080048000810040108020280200a040802008401028010040290010042008020080201022000210040880401008100481080200a0200804080200a401004090040204010042040024000201020080210041110401008100401080200802008040802008401004111040204010042008020480241020080210040101401009100401080200904008040848008401004010040204011002008024040201020080250040100401008100401080800802800040802008401020012000204010042008020888201020080210040100401008100401080200802487fc0802008401004010240224010042008020080a01020880210040100482008100424080200802008040802008c0100401004020401004203002008030102008021004050040140810040108020081200904080200840100401243fe0401004200802008020102008021004010040104840040108020080200814081200840100401007fe04010502008020080201020080210040100401008140401080200802008060002008401028010040290010042008020280201220080210040100409008900401080200802008242002008401004010040204010042008020080201020200210040100401008480409080200802008040a0200ffc100401004020404804202402008020102408021004010040100811000108020090400804084800840100401014020411004200802008020502048021004010040100810100108020080200804080200840100401004020401010200802008020102024021404010040100810040108028080200804080280840102201004020401204200802008020102008801004010048200810042408020080200ffc08020a0401004010040212010242008020080201020080810040100401008100401080200802008040802008481004010040204010042009020080201020080310040140401008100401480200901008040802009401004010040204010046008020080201020080210040100401008140401ff8200802008040809008501004010040204010042408020080201020080210

def rawAt (i : Nat) : Sig := inputs.getD i zero
def joined (i j : Nat) : Sig := bin true (rawAt i) (rawAt j)
def firstOr := joined 0 4
def firstBank := inputs ++ [firstOr]
def secondOr (i j : Fin 10) := bin true (firstBank.getD i.val zero) (firstBank.getD j.val zero)
def fullBank (i j : Fin 10) := firstBank ++ [secondOr i j]

abbrev Admissible (i j : Fin 10) := i < j ∧ ¬(i = 0 ∧ j = 4) ∧ ¬((i = 0 ∨ i = 4) ∧ j = 9)
def lowRow (i j : Fin 10) (a : Fin 9) : Nat :=
  (pivots 0 >>> (9 * (9 * (10 * i.val + j.val) + a.val))) &&& 511
def must (i j : Fin 10) (a : Fin 9) := lowRow i j a != 511
def row0 (i j : Fin 10) (a : Fin 9) : Row := Fin.ofNat 512 (lowRow i j a)
def row1 (i j : Fin 10) (a : Fin 9) : Row := Fin.ofNat 512 (lowRow i j a ||| (1 <<< a.val))
set_option maxHeartbeats 0 in
theorem requiredChecks : ∀ (i j : Fin 10) (a : Fin 9), must i j a = true →
    bit (row0 i j a) graph ≠ bit (row1 i j a) graph ∧
    (fullBank i j).all (fun v => v == rawAt a.val || bit (row0 i j a) v == bit (row1 i j a) v) = true := by decide +kernel

def requiredWords (i j : Fin 10) := ((List.finRange 9).filter (must i j)).map fun a => rawAt a.val
def spareWords (i j : Fin 10) :=
  (((List.finRange 9).filter fun a => !(must i j a)).map fun a => rawAt a.val) ++ [firstOr,secondOr i j]

set_option maxHeartbeats 0 in
theorem bankSet : ∀ (i j : Fin 10), (fullBank i j).toFinset =
    ((requiredWords i j) ++ (spareWords i j)).toFinset := by decide +kernel

def rootsWithin (fixed : List Sig) : List Sig → List (List Sig)
  | [] => [fixed]
  | a :: tail => rootsWithin fixed tail ++ rootsWithin (a :: fixed) tail

theorem chooseRoot (fixed spare : List Sig) (S : Finset Sig)
    (lo : fixed.toFinset ⊆ S) (hi : S ⊆ (fixed ++ spare).toFinset) :
    ∃ ws ∈ rootsWithin fixed spare, ws.toFinset = S := by
  induction spare generalizing fixed with
  | nil => exact ⟨fixed,by simp [rootsWithin],Finset.Subset.antisymm lo (by simpa using hi)⟩
  | cons v vs ih =>
    by_cases hv : v ∈ S
    · have small : (v :: fixed).toFinset ⊆ S := by
        intro a ha
        rcases List.mem_cons.mp (List.mem_toFinset.mp ha) with rfl | h
        · exact hv
        · exact lo (List.mem_toFinset.mpr h)
      have big : S ⊆ ((v :: fixed) ++ vs).toFinset := by
        intro a ha
        have mem := hi ha
        simp only [List.mem_toFinset,List.mem_append,List.mem_cons] at mem ⊢
        tauto
      obtain ⟨ws,hw,he⟩ := ih (v :: fixed) small big
      exact ⟨ws,List.mem_append_right _ hw,he⟩
    · have big : S ⊆ (fixed ++ vs).toFinset := by
        intro a ha
        have mem := hi ha
        have ne : a ≠ v := fun eq => hv (eq ▸ ha)
        simp only [List.mem_toFinset,List.mem_append,List.mem_cons] at mem ⊢
        tauto
      obtain ⟨ws,hw,he⟩ := ih fixed lo big
      exact ⟨ws,List.mem_append_left _ hw,he⟩

def suppliedBy (z : Sig) (w : List Sig) := w.all fun v => (inputs ++ [z]).contains v
def rootVerdict (i j : Fin 10) (w : List Sig) :=
  (suppliedBy firstOr w || suppliedBy (joined i.val j.val) w) ||
  (((rootIndex 14 (keySet w)).bind (linkedSet seedForest 13)).toList.any (sameWords w))

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem rootChecks : ∀ (i j : Fin 10), Admissible i j →
    (rootsWithin (requiredWords i j) (spareWords i j)).all (rootVerdict i j) = true := by decide +kernel

theorem fromOne (i j : Nat) (w : List Sig) (h : suppliedBy (joined i j) w = true) :
    Impossible graph 13 w.toFinset := by
  intro k t hk run
  have supplied (v : Sig) (hv : v ∈ w.toFinset) : v ∈ inputs ++ [joined i j] :=
    List.contains_iff_mem.mp (List.all_eq_true.mp h v (List.mem_toFinset.mp hv))
  have formed : represented inputs (joined i j) ∨ witness inputs (joined i j) :=
    bin_rep true (get_rep inputs i) (get_rep inputs j)
  obtain ⟨l,u,V,bound,tail,hsub⟩ := pull_gate run formed supplied
  rcases all_roots tail (fun v hv => List.mem_append_left _ (hsub v hv)) with eq | eq
  · exact dead_start (before_sound _ valid383) geomdead tablesdead l u (by omega) (eq ▸ tail)
  · have present : seed ∈ V := eq ▸ List.mem_toFinset.mpr (List.mem_append_right _ (List.mem_singleton_self _))
    exact (by decide +kernel : seed ∉ inputs) (hsub _ present)

theorem verifiedRoot (i j : Fin 10) (adm : Admissible i j) {k t S}
    (run : Live graph k t S) (hk : k ≤ 13) (sub : ∀ v ∈ S, v ∈ fullBank i j) : False := by
  have small : (requiredWords i j).toFinset ⊆ S := by
    intro v hv
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hv)
    have hc := requiredChecks i j q (List.mem_filter.mp hq).2
    apply raw_required run (fullBank i j) (rawAt q.val) sub (row0 i j q) (row1 i j q) hc.1
    intro z hz ne
    have ok := List.all_eq_true.mp hc.2 z hz
    simp only [Bool.or_eq_true,beq_iff_eq] at ok
    exact ok.resolve_left ne
  have big : S ⊆ (requiredWords i j ++ spareWords i j).toFinset := by
    rw [←bankSet]
    exact fun v hv => List.mem_toFinset.mpr (sub v hv)
  obtain ⟨w,hw,eq⟩ := chooseRoot _ _ S small big
  have test := List.all_eq_true.mp (rootChecks i j adm) w hw
  simp only [rootVerdict,Bool.or_eq_true,List.any_eq_true] at test
  rw [←eq] at run
  rcases test with (a|a)|⟨ws,source,same⟩
  · exact fromOne 0 4 w a k t hk run
  · exact fromOne i.val j.val w a k t hk run
  · have someq : (rootIndex 14 (keySet w)).bind (linkedSet seedForest 13) = some ws := by simpa using source
    obtain ⟨_,_,got⟩ := Option.bind_eq_some_iff.mp someq
    have geo := seedGeometry
    simp only [graphValid,Bool.and_eq_true,List.all_eq_true,beq_iff_eq] at geo
    have ss := linkedSet_sound seedForest 13 geo.2
      (reachableSound 13 (by decide)) got
    have tg : targetOf seedForest = graph := by decide +kernel
    rw [tg] at ss
    exact ss k t hk ((sameWords_sound same) ▸ run)

theorem bankBits (i j : Fin 10) (r : Row) :
    (fullBank i j).map (bit r) =
      let w := List.ofFn (sample r) ++ [sample r 0 || sample r 4]
      w ++ [w.getD i.val false || w.getD j.val false] := by
  have first : firstBank.map (bit r) = List.ofFn (sample r) ++ [sample r 0 || sample r 4] := by
    simp only [firstBank,firstOr,joined,rawAt,List.map_append,List.map_singleton,bit_bin,sampled]
    rfl
  simp only [fullBank,List.map_append,List.map_singleton,secondOr,bit_bin,ite_true,←b_read,first]

theorem finish (C : Circuit) (i j : Fin 10) (fan : PEqualNP.MetaComplexity.FanInTwo C)
    (adm : Admissible i j)
    (correct : ∀ x : Fin 9 → Bool, let w := List.ofFn x ++ [x 0 || x 4]
      C.eval (w ++ [w.getD i.val false || w.getD j.val false]) = edge x) : 14 ≤ C.size := by
  by_contra! small
  have eqGoal : (execute C.gates (fullBank i j)).getD C.output zero = graph := by
    apply BitVec.eq_of_getLsbD_eq
    intro l hl
    let r : Row := ⟨l,hl⟩
    change bit r ((execute C.gates (fullBank i j)).getD C.output zero) = bit r graph
    rw [←b_read,execute_bits _ _ _ (fun g hg => (fan g hg).1),edge_table]
    change C.eval ((fullBank i j).map (bit r)) = _
    rw [bankBits]
    exact correct (sample r)
  have out := get_rep (execute C.gates (fullBank i j)) C.output
  rw [eqGoal] at out
  obtain ⟨k,t,S,hk,run,sub⟩ := extract C.gates (fullBank i j) fan graph_proper
    (out.resolve_right fun h => h graph_proper)
  exact verifiedRoot i j adm run (by change C.gates.length < 14 at small; omega) sub

end PEqualNP.Outside.L_meta_3590

theorem PEqualNP.Outside.L_meta_3590 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : Fin (10 : ℕ)),   PEqualNP.MetaComplexity.FanInTwo x1 →     x2 < x3 →       ¬(x2 = (0 : Fin (10 : ℕ)) ∧ x3 = (4 : Fin (10 : ℕ))) →         ¬((x2 = (0 : Fin (10 : ℕ)) ∨ x2 = (4 : Fin (10 : ℕ))) ∧ x3 = (9 : Fin (10 : ℕ))) →           (∀ (x8 : Fin (9 : ℕ) → Bool),               have x9 : List Bool := List.ofFn x8 ++ [x8 (0 : Fin (9 : ℕ)) || x8 (4 : Fin (9 : ℕ))];               x1.eval (x9 ++ [x9.getD (↑x2) Bool.false || x9.getD (↑x3) Bool.false]) = (fun (x10 : Fin (9 : ℕ) → Bool) => [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x11 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x10 x11.1 && x10 x11.2) x8) →             (14 : ℕ) ≤ x1.size := by
  intro C i j fan lt diff nontriv h
  apply PEqualNP.Outside.L_meta_3590.finish C i j fan ⟨lt,diff,nontriv⟩
  intro x
  simpa only [PEqualNP.Outside.L_meta_3590.edge,List.any_cons,List.any_nil,Bool.or_false,Bool.or_assoc] using h x

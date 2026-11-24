import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5002
-- The positive input lower bound adapts the certificate of L_meta_3640.
-- The boundary argument adapts the monotonicity proof of L_meta_2549.
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
abbrev Sig := BitVec 512
def zero : Sig := 0
def one : Sig := BitVec.allOnes 512
def neg (a : Sig) : Sig := ~~~a
def bin (d : Bool) (a b : Sig) : Sig := if d then a ||| b else a &&& b
def proper (a : Sig) : Prop := a ≠ zero ∧ a ≠ one
private theorem bin_comm (d : Bool) (a b : Sig) : bin d a b = bin d b a := by
  cases d <;> simp [bin,BitVec.and_comm,BitVec.or_comm]

def Live (target : Sig) : Nat → Nat → Finset Sig → Prop
  | 0,t,S => t=0 ∧ S={target} ∧ proper target
  | k+1,t,S =>
    (∃ (u : Nat) (U : Finset Sig) (a : Sig), t=u+1 ∧ S=insert a U ∧ proper a ∧
      neg a ∉ insert a U ∧ Live target k u (insert (neg a) U)) ∨
    (∃ (U : Finset Sig) (a b : Sig) (d : Bool), S=insert a (insert b U) ∧ proper a ∧ proper b ∧ a ≠ b ∧
      bin d a b ∉ insert a (insert b U) ∧ Live target k t (insert (bin d a b) U))
theorem Live.stop {target : Sig} (hp : proper target) : Live target 0 0 {target} := ⟨rfl,rfl,hp⟩
theorem Live.unary {target : Sig} {k t : Nat} {U : Finset Sig} {a : Sig} (ha : proper a)
    (hfresh : neg a ∉ insert a U) (tail : Live target k t (insert (neg a) U)) :
    Live target (k+1) (t+1) (insert a U) :=
  Or.inl ⟨t,U,a,rfl,rfl,ha,hfresh,tail⟩
theorem Live.binary {target : Sig} {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool}
    (ha : proper a) (hb : proper b) (hab : a ≠ b)
    (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live target k t (insert (bin d a b) U)) :
    Live target (k+1) t (insert a (insert b U)) :=
  Or.inr ⟨U,a,b,d,rfl,ha,hb,hab,hfresh,tail⟩
theorem Live.ind {target : Sig} {motive : ∀ (k t : Nat) (S : Finset Sig), Live target k t S → Prop}
    (stop : ∀ (hp : proper target), motive 0 0 {target} (Live.stop hp))
    (unary : ∀ {k t : Nat} {U : Finset Sig} {a : Sig} (ha : proper a)
      (hfresh : neg a ∉ insert a U) (tail : Live target k t (insert (neg a) U)),
      motive k t (insert (neg a) U) tail → motive (k+1) (t+1) (insert a U) (Live.unary ha hfresh tail))
    (binary : ∀ {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool}
      (ha : proper a) (hb : proper b) (hab : a ≠ b)
      (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live target k t (insert (bin d a b) U)),
      motive k t (insert (bin d a b) U) tail →
      motive (k+1) t (insert a (insert b U)) (Live.binary ha hb hab hfresh tail))
    {k t : Nat} {S : Finset Sig} (h : Live target k t S) : motive k t S h := by
  induction k generalizing t S with
  | zero =>
    obtain ⟨rfl,rfl,hp⟩ := h
    exact stop hp
  | succ k ih =>
    rcases h with ⟨u,U,a,rfl,rfl,ha,hf,tail⟩ | ⟨U,a,b,d,rfl,ha,hb,hab,hf,tail⟩
    · exact unary ha hf tail (ih tail)
    · exact binary ha hb hab hf tail (ih tail)

private lemma live_proper {k t S} (h : Live target k t S) : ∀ a ∈ S, proper a := by
  induction h using Live.ind with
  | stop hp => simpa using hp
  | unary ha hf _ ih => simpa using And.intro ha (fun a h => ih a (Finset.mem_insert_of_mem h))
  | binary ha hb hab hf _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha,hb,fun a h => ih a (Finset.mem_insert_of_mem h)⟩

private lemma live_size {k t S} (h : Live target k t S) : t ≤ k ∧ S.card+t ≤ k+1 := by
  induction h using Live.ind with
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

def Reach {R} (roots : List (Wire R)) : Nat → List (Wire R) → Prop
  | 0,b => b=roots
  | p+1,c => (∃ bank a, Reach roots p bank ∧ Available bank a ∧ c=inv a :: bank) ∨
    (∃ (op : Bool) (bank : List (Wire R)) (a b : Wire R), Reach roots p bank ∧ Available bank a ∧
      Available bank b ∧ c=combine op a b :: bank)
theorem Reach.start {R} {roots : List (Wire R)} : Reach roots 0 roots := rfl
theorem Reach.one {R} {roots : List (Wire R)} {p bank a} (h : Reach roots p bank)
    (ha : Available bank a) : Reach roots (p+1) (inv a :: bank) := Or.inl ⟨bank,a,h,ha,rfl⟩
theorem Reach.two {R} {roots : List (Wire R)} {p bank a b} (op : Bool) (h : Reach roots p bank)
    (ha : Available bank a) (hb : Available bank b) : Reach roots (p+1) (combine op a b :: bank) :=
  Or.inr ⟨op,bank,a,b,h,ha,hb,rfl⟩
theorem Reach.ind {R} {roots : List (Wire R)} {motive : ∀ p bank, Reach roots p bank → Prop}
    (start : motive 0 roots Reach.start)
    (one : ∀ {p bank a} (h : Reach roots p bank) (ha : Available bank a), motive p bank h →
      motive (p+1) (inv a :: bank) (Reach.one h ha))
    (two : ∀ {p bank a b} (op : Bool) (h : Reach roots p bank) (ha : Available bank a)
      (hb : Available bank b), motive p bank h →
      motive (p+1) (combine op a b :: bank) (Reach.two op h ha hb))
    {p bank} (h : Reach roots p bank) : motive p bank h := by
  induction p generalizing bank with
  | zero =>
    obtain rfl := h
    exact start
  | succ p ih =>
    rcases h with ⟨bank,a,h,ha,rfl⟩ | ⟨op,bank,a,b,h,ha,hb,rfl⟩
    · exact one h ha (ih h)
    · exact two op h ha hb (ih h)

def kept {α : Type} (save : Bool) (x : α) (xs : List α) := if save then x::xs else xs

def Run {R} (goal : Wire R) : Nat → List (Wire R) → Prop
  | 0,zs => List.Perm [goal] zs
  | s+1,zs => (∃ (save : Bool) (a : Wire R) (rest : List (Wire R)), (a::rest).Perm zs ∧
      Run goal s (inv a :: kept save a rest)) ∨
    (∃ (op ka kb : Bool) (a b : Wire R) (rest : List (Wire R)), (a::b::rest).Perm zs ∧
      Run goal s (combine op a b :: kept ka a (kept kb b rest)))
theorem Run.stop {R} {goal : Wire R} : Run goal 0 [goal] := List.Perm.refl _
theorem Run.perm {R} {goal : Wire R} {s : Nat} {xs zs : List (Wire R)} (p : xs.Perm zs)
    (h : Run goal s xs) : Run goal s zs := by
  cases s with
  | zero => exact List.Perm.trans h p
  | succ s =>
    rcases h with ⟨save,a,rest,q,h⟩ | ⟨op,ka,kb,a,b,rest,q,h⟩
    · exact Or.inl ⟨save,a,rest,q.trans p,h⟩
    · exact Or.inr ⟨op,ka,kb,a,b,rest,q.trans p,h⟩
theorem Run.one {R} {goal : Wire R} {s : Nat} {a : Wire R} {rest : List (Wire R)} (save : Bool)
    (h : Run goal s (inv a :: kept save a rest)) : Run goal (s+1) (a::rest) :=
  Or.inl ⟨save,a,rest,List.Perm.refl _,h⟩
theorem Run.two {R} {goal : Wire R} {s : Nat} {a b : Wire R} {rest : List (Wire R)} (op ka kb : Bool)
    (h : Run goal s (combine op a b :: kept ka a (kept kb b rest))) : Run goal (s+1) (a::b::rest) :=
  Or.inr ⟨op,ka,kb,a,b,rest,List.Perm.refl _,h⟩
theorem Run.ind {R} {goal : Wire R} {motive : ∀ s ws, Run goal s ws → Prop}
    (stop : motive 0 [goal] Run.stop)
    (perm : ∀ {s xs zs} (p : List.Perm xs zs) (h : Run goal s xs), motive s xs h → motive s zs (Run.perm p h))
    (one : ∀ {s a rest} (save : Bool) (h : Run goal s (inv a :: kept save a rest)),
      motive s _ h → motive (s+1) (a::rest) (Run.one save h))
    (two : ∀ {s a b rest} (op ka kb : Bool) (h : Run goal s (combine op a b :: kept ka a (kept kb b rest))),
      motive s _ h → motive (s+1) (a::b::rest) (Run.two op ka kb h))
    {s ws} (h : Run goal s ws) : motive s ws h := by
  induction s generalizing ws with
  | zero => exact perm h Run.stop stop
  | succ s ih =>
    rcases h with ⟨save,a,rest,p,h⟩ | ⟨op,ka,kb,a,b,rest,p,h⟩
    · exact perm p (Run.one save h) (one save h (ih h))
    · exact perm p (Run.two op ka kb h) (two op ka kb h (ih h))

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
  induction h using Run.ind generalizing p bank with
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
  induction h using Run.ind with
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
  induction h using Live.ind generalizing v with
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
  induction h using Reach.ind generalizing k t S with
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
  induction h using Live.ind with
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
def seed : Sig := neg (inputs.getD 0 zero)

def sample (r : Row) (j : Fin 9) := bit r (inputs.getD j.val zero)
def edge (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
  (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) ||
  (x 6 && x 8) || (x 8 && x 5)
theorem edge_table : ∀ r : Row, bit r graph = edge (sample r) := by decide +kernel
theorem seed_table : ∀ r : Row, bit r seed = !(sample r 0) := by decide +kernel
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

theorem initial_live (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (first : ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = !(y 0))
    (computes : PEqualNP.MetaComplexity.circuitFun 9 C = edge) (small : C.size ≤ 15) :
    ∃ k t S, k ≤ 14 ∧ Live graph k t S ∧ ∀ a ∈ S, a ∈ inputs++[seed] := by
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
    exact ⟨k,t,S,by omega,run,hs⟩


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
  induction h using Live.ind with
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
  induction h using Live.ind with
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
  induction h using Live.ind with
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
def varsX (m : Nat) : List Sig := if m.testBit 9 then vars m ++ [seed] else vars m
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
def chartGoal (m : Nat) : Sig := graphGoal m
def rawMask (m : Nat) (c : ColumnInfo) : Nat := m ^^^ (m &&& (c.1 &&& 512))
def colCheck (m : Nat) (c : ColumnInfo) (prior : Nat → Nat) : Bool :=
  let (z,o,q,s,L) := c
  let ms := fixRows z o
  let raw := rawMask m c
  let free := colFree raw z o
  let G := movedWord ms (chartGoal m)
  let xs := supportPairs s
  let count := (xs.map Prod.fst).toFinset.card
  properB G && checkMap ms (varsX raw) (chartGoal m) (varsX free) G &&
    (movedWord ms (subcube z o)==one) &&
    (if q=0 then checkEssential G (varsX free) xs && decide (L ≤ count-1)
     else properB (graphGoal q) &&
       checkLift (fixRows (colFree free q 0) 0) G (varsX free) (varsX q) (graphGoal q) xs &&
       decide (L ≤ prior q+count))

theorem col_sound {m : Nat} (c : ColumnInfo) (prior : Nat → Nat)
    (valid : ∀ q, Lower (varsX q) (graphGoal q) (prior q))
    (ok : colCheck m c prior = true) : Slice (varsX (rawMask m c)) (chartGoal m) (subcube c.1 c.2.1) c.2.2.2.2 := by
  revert ok
  obtain ⟨z,o,q,s,L⟩ := c
  intro ok
  let ms := fixRows z o
  let raw := rawMask m (z,o,q,s,L)
  let free := colFree raw z o
  let G := movedWord ms (chartGoal m)
  let xs := supportPairs s
  change (((properB G && checkMap ms (varsX raw) (chartGoal m) (varsX free) G) &&
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
    checkMap (swaps.map swapRows) (varsX old) (graphGoal old) (varsX rep) (graphGoal rep)
theorem relabel_of {old rep L swaps} (ok : relabelOK old rep swaps = true)
    (h : Lower (varsX rep) (graphGoal rep) L) : Lower (varsX old) (graphGoal old) L := by
  simp only [relabelOK,Bool.and_eq_true] at ok
  exact lower_map ok.2 (proper_of _ ok.1.1) (proper_of _ ok.1.2) h

def boundsBefore (entries : List (Nat × Nat)) (q : Nat) :=
  ((entries.find? (fun a => a.1 == q)).map Prod.snd).getD 0
theorem before_sound (entries : List (Nat × Nat))
    (sound : ∀ e ∈ entries, Lower (varsX e.1) (graphGoal e.1) e.2) (q : Nat) :
    Lower (varsX q) (graphGoal q) (boundsBefore entries q) := by
  unfold boundsBefore
  cases h : entries.find? (fun a => a.1 == q) with
  | none => exact fun _ _ _ _ => Nat.zero_le _
  | some e =>
    have he := List.mem_of_find?_eq_some h
    have hit : (fun a : Nat × Nat => a.1 == q) e = true := List.find?_some (p:=fun a : Nat × Nat => a.1 == q) (a:=e) h
    have eq : e.1=q := beq_iff_eq.mp hit
    simpa only [Option.map_some,Option.getD_some,eq] using sound e he


abbrev BoundPool := Sig × Nat × Nat × List Sig
def BoundPool.domain (c : BoundPool) : Sig := c.1
def BoundPool.bound (c : BoundPool) : Nat := c.2.1
def BoundPool.paid (c : BoundPool) : Nat := c.2.2.1
def BoundPool.wires (c : BoundPool) : List Sig := c.2.2.2

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
theorem ofRows_bin (r : Fin 768 → Row) (d : Bool) (a b : Sig) :
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
    obtain ⟨_,hS,_⟩ := h
    exact out (List.mem_toFinset.mp (by rw [he,hS]; exact Finset.mem_singleton_self _))
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


abbrev Forest := Nat × Nat × (Nat → Bits × Bits) × List ColumnInfo × List (List Nat) ×
  (Nat → Packing) × (Nat → Nat → Option (Nat × Nat))
def Forest.mask (g : Forest) : Nat := g.1
def Forest.cap (g : Forest) : Nat := g.2.1
def Forest.samples (g : Forest) : Nat → Bits × Bits := g.2.2.1
def Forest.cols (g : Forest) : List ColumnInfo := g.2.2.2.1
def Forest.autos (g : Forest) : List (List Nat) := g.2.2.2.2.1
def Forest.levels (g : Forest) : Nat → Packing := g.2.2.2.2.2.1
def Forest.index (g : Forest) : Nat → Nat → Option (Nat × Nat) := g.2.2.2.2.2.2

def wiresOf (g : Forest) :=
  let ws := rawDecor g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)
  ws
theorem wires_faithful (g : Forest) : ∀ a ∈ wiresOf g,
    faithful (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2) a := by
  exact raw_faithful g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)

def targetOf (g : Forest) := chartGoal g.mask
def chartSamples (m : Nat) (v : Nat → Bits) :=
  liftGoal m v
theorem chart_bit (m : Nat) (v : Nat → Bits) (i : Fin 768) :
    bit (asRow v i) (chartGoal m) = (chartSamples m v).getLsbD i.val := by
  exact bit_liftGoal m v i
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

def storedDepth (_g : Forest) (depth : Nat) := depth
def readNode (g : Forest) (k i : Nat) : Nat × List Decor × List Decor :=
  let raw := wiresOf g
  let (_,depth,_,_,_,_,_,data) := g.levels k
  let len := 10*storedDepth g depth
  let width := len+raw.length+depth
  let recp := packedAt data (i*width) width
  let stored := recp &&& ((1 <<< len)-1)
  let ops := stored
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
  (g.cols[idx]?).bind fun ci =>
    materialize (varsX (rawMask g.mask ci)) (chosenSteps bank ops paid d) (subcube ci.1 ci.2.1) ci.2.2.2.2

theorem buildRule_sound (g : Forest)
    (cols : ∀ ci ∈ g.cols, Slice (varsX (rawMask g.mask ci)) (targetOf g) (subcube ci.1 ci.2.1) ci.2.2.2.2)
    {i ops depth bank paid c} (h : buildRule g ops depth bank i paid = some c) :
    ValidPool (vars g.mask) (targetOf g) c := by
  unfold buildRule at h
  cases e : g.cols[i]? with
  | none => simp [e] at h
  | some ci =>
    simp only [e,Option.bind_some] at h
    apply materialize_sound _ h
    exact cols ci (List.mem_of_getElem? e)

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
    (names : ∀ x ∈ g.autos, autoOK (targetOf g) (x.map swapRows) = true)
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
      exact rotate_excluded (earlier _ (by omega)) _ (names _ (List.mem_of_getElem? e))

def nodeVerified (g : Forest) (k i : Nat) :=
  let raw := wiresOf g
  let (num,depth,cw,iw,pw,offw,lw,data) := g.levels k
  let (ops,bank,ws) := readNode g k i
  let values := ws.map Prod.fst
  let start := num*(10*storedDepth g depth+raw.length+depth)
  let pos := start+num*offw+packedAt data (start+i*offw) offw
  let nr := packedAt data pos 5
  let nl := packedAt data (pos+5) lw
  let st := pos+5+lw
  let rules := (getPairs data cw depth nr st).filterMap (fun (a,b) => buildRule g ops depth bank a b)
  let ls := fun tag => ((g.index k tag).bind (linkedSet g (k-1))).toList
  decide values.Nodup && !(values.contains (targetOf g)) &&
    (if k=0 then true else testAll (k,ws.length,ws,preCov ws,rules,ls) ws)

theorem nodeVerified_sound (g : Forest) (k i : Nat)
    (samples : properPairs (targetOf g) (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2))
    (cols : ∀ ci ∈ g.cols, Slice (varsX (rawMask g.mask ci)) (targetOf g) (subcube ci.1 ci.2.1) ci.2.2.2.2)
    (names : ∀ x ∈ g.autos, autoOK (targetOf g) (x.map swapRows) = true)
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
    obtain ⟨_,hS,_⟩ := h
    exact hT (List.mem_toFinset.mp (by rw [he,hS]; exact Finset.mem_singleton_self _))
  apply node_sound (raw:=vars g.mask) samples _ hN hT _ _ (by simpa only [h0,if_false] using checked.2)
  · intro v hv
    apply decode_faithful _ _ _ _ _ (wires_faithful g) v
    exact (selectLive_sub _ _).subset hv
  · intro p hp
    obtain ⟨⟨a,b⟩,_,h⟩ := List.mem_filterMap.mp hp
    exact buildRule_sound g cols h
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
  g.cols.all (fun c => colCheck g.mask c prior) &&
  g.autos.all (fun p => autoOK (targetOf g) (p.map swapRows))

theorem forest_all (g : Forest) (top : Nat) (prior : Nat → Nat)
    (lower : ∀ q, Lower (varsX q) (graphGoal q) (prior q))
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
theorem root_index {g top prior k i ws} (low : ∀ q, Lower (varsX q) (graphGoal q) (prior q))
    (geom : graphValid g prior = true) (blocks : checkedTables g top) (le : k ≤ top)
    (idx : indexedRoot g k i ws = true) : Impossible (targetOf g) k ws.toFinset := by
  simp only [indexedRoot,Bool.and_eq_true,decide_eq_true_eq] at idx
  rw [←sameWords_sound idx.2]
  exact forest_all g top prior low geom blocks _ le i idx.1

theorem lower_forest {g prior i hints} (low : ∀ q, Lower (varsX q) (graphGoal q) (prior q))
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

theorem lower_discard {g prior ci hints} (low : ∀ q, Lower (varsX q) (graphGoal q) (prior q))
    (ok : colCheck g.mask ci prior = true)
    (hp : properB (targetOf g) = true)
    (ess : checkEssential (targetOf g) (vars g.mask) (graphPairs g.mask hints) = true)
    (all : (graphPairs g.mask hints).map Prod.fst = vars g.mask)
    (nd : (vars g.mask).Nodup)
    (cut : poolCut (subcube ci.1 ci.2.1) ci.2.2.2.2 g.cap 0 (varsX (rawMask g.mask ci)) (vars g.mask)=true) :
    Lower (vars g.mask) (targetOf g) (g.cap+1) := by
  apply lower_impossible (proper_of _ hp) _ (poolCut_sound (col_sound ci prior low ok) [] rfl nd cut)
  intro a ha
  apply essential_ok ess a
  rw [all]
  exact List.mem_toFinset.mpr ha

def Known (entries : List (Nat × Nat)) := ∀ e ∈ entries, Lower (varsX e.1) (graphGoal e.1) e.2
def extendKnown (old : List (Nat × Nat)) (L : Nat) (relabels : List (Nat × List Nat)) :=
  relabels.map (fun v => (v.1,L)) ++ old
theorem extendKnown_ok {old L m relabels} (previous : Known old)
    (main : Lower (varsX m) (graphGoal m) L)
    (ok : relabels.all (fun v => relabelOK v.1 m v.2) = true) :
    Known (extendKnown old L relabels) := by
  intro e he
  rcases List.mem_append.mp he with hx | h
  · obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hx
    exact relabel_of (List.all_eq_true.mp ok _ hv) main
  · exact previous e h
theorem baseKnown : Known [] := by simp [Known]
def contextOf (g : Forest) (k i : Nat) : NodeContext :=
  let raw := wiresOf g
  let (num,depth,cw,iw,pw,offw,lw,data) := g.levels k
  let (ops,bank,ws) := readNode g k i
  let start := num*(10*storedDepth g depth+raw.length+depth)
  let pos := start+num*offw+packedAt data (start+i*offw) offw
  let nr := packedAt data pos 5
  let nl := packedAt data (pos+5) lw
  let st := pos+5+lw
  let rules := (getPairs data cw depth nr st).filterMap (fun (a,b) => buildRule g ops depth bank a b)
  let ls := fun tag => ((g.index k tag).bind (linkedSet g (k-1))).toList
  (k,ws.length,ws,preCov ws,rules,ls)


def prelim (T : Sig) (c : NodeContext) :=
  let ws := c.2.2.1.map Prod.fst
  decide ws.Nodup && !(ws.contains T)
def enabledLinks {α} (flag : Bool) (xs : List α) := if flag then xs else []
theorem enabledLinks_mem {α} {flag : Bool} {x : α} {xs : List α} (h : x ∈ enabledLinks flag xs) : x ∈ xs := by
  cases flag <;> simp_all [enabledLinks]

def wideDecode (n : Nat) (bits : Nat) (ws : List Decor) : List Decor :=
  match n with
  | 0 => ws
  | k+1 =>
    let a := ws.getD (bits &&& 31) defaultDecor
    let b := ws.getD ((bits >>> 5) &&& 31) defaultDecor
    wideDecode k (bits >>> 11) (ws++[codeDecor ((bits >>> 10) &&& 1) a b])
theorem wide_faithful (n bits) (ws) (r s) (base : ∀ v ∈ ws, faithful r s v) :
    ∀ v ∈ wideDecode n bits ws, faithful r s v := by
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

def wideRead (g : Forest) (k i : Nat) : Nat × List Decor × List Decor :=
  let raw := wiresOf g
  let (_,depth,_,_,_,_,_,data) := g.levels k
  let len := (8+11*(depth-2))
  let width := len+raw.length+depth
  let recp := packedAt data (i*width) width
  let stored := recp &&& ((1 <<< len)-1)
  let second := 1024 + 32*((stored >>> 4) &&& 15) + (stored &&& 15)
  let ops := 1120 ||| (second <<< 11) ||| ((stored >>> 8) <<< 22)
  let bank := wideDecode depth ops raw
  (ops,bank,selectLive (recp >>> len) bank)

def wideSteps (bank : List Decor) (ops paid : Nat) : Nat → List Choice
  | 0 => []
  | n+1 =>
    let more := wideSteps bank (ops >>> 11) (paid >>> 1) n
    if paid &&& 1 == 0 then more else
      (getFieldV ops 10 1,(bank.getD (ops &&& 31) defaultDecor).1,
        (bank.getD (getFieldV ops 5 5) defaultDecor).1) :: more

def wideRule (g : Forest) (ops d : Nat) (bank : List Decor) (idx paid : Nat) : Option BoundPool :=
  (g.cols[idx]?).bind fun ci =>
    materialize (varsX (rawMask g.mask ci)) (wideSteps bank ops paid d) (subcube ci.1 ci.2.1) ci.2.2.2.2

theorem wideRule_sound (g : Forest)
    (cols : ∀ ci ∈ g.cols, Slice (varsX (rawMask g.mask ci)) (targetOf g) (subcube ci.1 ci.2.1) ci.2.2.2.2)
    {i ops depth bank paid c} (h : wideRule g ops depth bank i paid = some c) :
    ValidPool (vars g.mask) (targetOf g) c := by
  unfold wideRule at h
  cases e : g.cols[i]? with
  | none => simp [e] at h
  | some ci =>
    simp only [e,Option.bind_some] at h
    apply materialize_sound _ h
    exact cols ci (List.mem_of_getElem? e)

def wideState (g : Forest) (k i : Nat) := (wideRead g k i).2.2.map Prod.fst
def wideLinks (g : Forest) (k : Nat) (pair : Nat × Nat) : Option (List Sig) :=
  if pair.1 ≥ (g.levels k).1 then none else
    (g.autos[pair.2]?).map fun perm => (wideState g k pair.1).map (movedWord (perm.map swapRows).reverse)

def wideContext (g : Forest) (k i : Nat) : NodeContext :=
  let raw := wiresOf g
  let (num,depth,cw,iw,pw,offw,lw,data) := g.levels k
  let (ops,bank,ws) := wideRead g k i
  let start := num*((8+11*(depth-2))+raw.length+depth)
  let pos := start+num*offw+packedAt data (start+i*offw) offw
  let nr := packedAt data pos 7
  let nl := packedAt data (pos+7) lw
  let st := pos+7+lw
  let rules := (getPairs data cw depth nr st).filterMap (fun (a,b) => wideRule g ops depth bank a b)
  let ls := fun tag => enabledLinks (nl != 0) (((g.index k tag).bind (wideLinks g (k-1))).toList)
  (k,ws.length,ws,preCov ws,rules,ls)


def evalMono (c : NodeContext) (op : Nat) (a b z : Decor) (ka kb : Bool) :=
  let (cap,n,ws,cov,pools,links) := c
  let un := op==2
  let len := 1+(n - (if ka then 0 else 1) - (if un || kb then 0 else 1))
  if len>cap then true else
    let d := true
    let rs := restCov (getCov cov d) (column d a.2) (column d b.2) un ka kb
    if (rs ||| column d z.2) != BitVec.allOnes 768 then true else
    if !properB z.1 || ws.any (fun v => v.1==z.1) then true else
      let rest := (opKeep un ka kb a b ws).map Prod.fst
      closeChild pools links (cap-1) rest (movedChoice op a b)

def testMonoPair (ctx : NodeContext) (a b : Decor) (d : Bool) :=
  let op := if d then 1 else 0
  let z := movedDecor op a b
  let attempt := evalMono ctx op a b z
  attempt false false && attempt true false && attempt false true && attempt true true
theorem testMonoPair_at {ctx a b d} (h : testMonoPair ctx a b d = true) (ka kb : Bool) :
    evalMono ctx (if d then 1 else 0) a b (movedDecor (if d then 1 else 0) a b) ka kb = true := by
  simp only [testMonoPair,Bool.and_eq_true] at h
  cases ka <;> cases kb <;> first | exact h.1.1.1 | exact h.1.2 | exact h.1.1.2 | exact h.2

def ImpossibleM (T : Sig) (cap : Nat) (S : Finset Sig) : Prop :=
  ∀ k t, k ≤ cap → t=0 → ¬Live T k t S

theorem enum_stepM {T : Sig} {cap : Nat} {ws : List Sig} (hn : ws.Nodup) (out : T ∉ ws)
    (twoStep : ∀ a ∈ ws, ∀ b ∈ ws, ∀ d ka kb, a ≠ b → bin d a b ∉ ws →
      proper (bin d a b) → (childTwo ws a b d ka kb).length ≤ cap →
      ImpossibleM T (cap-1) (childTwo ws a b d ka kb).toFinset) :
    ImpossibleM T cap ws.toFinset := by
  classical
  intro k t hk ht h
  generalize he : ws.toFinset = S at h
  induction h using Live.ind with
  | stop hp =>
    have mem : T ∈ ws.toFinset := he.symm ▸ Finset.mem_singleton_self _
    exact out (List.mem_toFinset.mp mem)
  | @unary k t U a ha hf tail _ => omega
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
    exact twoStep a am b bm d ka kb hab fresh hz len k t (by omega) ht (eq.symm ▸ tail)

theorem closeChild_soundM {raw T pools links k rest op}
    (pValid : ∀ p ∈ pools, ValidPool raw T p)
    (lValid : ∀ tag xs, xs ∈ links tag → ImpossibleM T k (List.toFinset xs))
    (nd : (choiceVal op :: rest).Nodup)
    (h : closeChild pools links k rest op = true) :
    ImpossibleM T k (choiceVal op :: rest).toFinset := by
  simp only [closeChild,Bool.or_eq_true,List.any_eq_true] at h
  rcases h with ⟨xs,hx,ok⟩ | ⟨p,hp,ok⟩
  · rw [sameWords_sound ok]
    exact lValid _ _ hx
  · intro n t le _
    exact scalarPoolCut_sound (pValid _ hp) nd ok n t le

theorem evalMove_soundM {raw T r s ws pools links cap a b op ka kb}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : (op==2)=false → a≠b) (hcap : 0<cap)
    (pv : ∀ p ∈ pools, ValidPool raw T p)
    (lv : ∀ tag xs, xs ∈ links tag → ImpossibleM T (cap-1) (List.toFinset xs))
    (pro : proper (movedDecor op a b).1) (fresh : (movedDecor op a b).1 ∉ ws.map Prod.fst)
    (test : evalMono (cap,ws.length,ws,preCov ws,pools,links) op a b (movedDecor op a b) ka kb = true) :
    ImpossibleM T (cap-1) (moveFront ws op a b ka kb).toFinset := by
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
  intro k t hk ht h
  have hsz := (live_size h).2
  change child.toFinset.card + t ≤ k+1 at hsz
  rw [List.toFinset_card_of_nodup ndc] at hsz
  have len : child.length ≤ cap := by omega
  unfold evalMono at test
  change (if 1+(ws.length-_ - _) > cap then true else _) = true at test
  rw [leq,if_neg (by omega)] at test
  let d := true
  have sep := cover_sound h rfl (pair_sep pairs) true (fun _ => ht)
  have g : (coverage d rest).1 = covered d (pairSig r s) (rest.map Prod.fst) :=
    cov_word _ _ (fun v hv => faith _ (sub.subset hv))
  have rz := rest_coverage ha hb (op==2) ka kb d ne
  have hf := moved_faithful (faith _ ha) (faith _ hb) op
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
  exact closeChild_soundM pv lv nd' test k t hk ht h

def testRowM (ctx : NodeContext) (a : Decor) (bs : List Decor) :=
  bs.all (fun b => testMonoPair ctx a b false && testMonoPair ctx a b true)

def testAllM (ctx : NodeContext) : List Decor → Bool
  | [] => true
  | a::bs => testRowM ctx a bs && testAllM ctx bs

theorem all_binaryM {ctx ws} (h : testAllM ctx ws=true) {a b : Decor} (ha : a∈ws) (hb : b∈ws)
    (ne : a≠b) (d : Bool) : testMonoPair ctx a b d=true ∨ testMonoPair ctx b a d=true := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    simp only [testAllM,Bool.and_eq_true,testRowM,List.all_eq_true] at h
    rcases List.mem_cons.mp ha with rfl | haTail
    · have bm := (List.mem_cons.mp hb).resolve_left (Ne.symm ne)
      left
      cases d <;> first | exact (h.1 b bm).1 | exact (h.1 b bm).2
    · rcases List.mem_cons.mp hb with rfl | hbTail
      · right
        cases d <;> first | exact (h.1 a haTail).1 | exact (h.1 a haTail).2
      · exact ih h.2 haTail hbTail

theorem node_soundM {raw T r s ws pools links cap}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (out : T ∉ ws.map Prod.fst)
    (pv : ∀ p ∈ pools, ValidPool raw T p)
    (lv : ∀ tag xs, xs ∈ links tag → ImpossibleM T (cap-1) (List.toFinset xs))
    (checks : testAllM (cap,ws.length,ws,preCov ws,pools,links) ws = true) :
    ImpossibleM T cap (ws.map Prod.fst).toFinset := by
  by_cases hc : cap=0
  · intro k t hk ht h
    have ke : k=0 := by omega
    subst k
    generalize he : (ws.map Prod.fst).toFinset = S at h
    obtain ⟨_,hS,_⟩ := h
    exact out (List.mem_toFinset.mp (by rw [he,hS]; exact Finset.mem_singleton_self _))
  have hc' : 0<cap := by omega
  apply enum_stepM nd out
  · intro a ha b hb d ka kb ne fresh pro len
    obtain ⟨a,haW,rfl⟩ := List.mem_map.mp ha
    obtain ⟨b,hbW,rfl⟩ := List.mem_map.mp hb
    have ab : a≠b := fun e => ne (congrArg Prod.fst e)
    have one (a b : Decor) (aa : a∈ws) (bb : b∈ws) (ne' : a.1≠b.1) (ka kb : Bool)
        (pr : proper (bin d a.1 b.1)) (fr : bin d a.1 b.1 ∉ ws.map Prod.fst)
        (test : testMonoPair (cap,ws.length,ws,preCov ws,pools,links) a b d = true) :
        ImpossibleM T (cap-1) (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
      rw [←binary_front nd aa bb ne']
      have eq : (movedDecor (if d then 1 else 0) a b).1 = bin d a.1 b.1 := by cases d <;> rfl
      exact evalMove_soundM pairs faith nd aa bb (fun _ e => ne' (congrArg Prod.fst e)) hc' pv lv
        (eq ▸ pr) (eq ▸ fr) (testMonoPair_at test ka kb)
    rcases all_binaryM checks haW hbW ab d with hh | hh
    · exact one a b haW hbW ne ka kb pro fresh hh
    · rw [childTwo_swap _ nd]
      exact one b a hbW haW (Ne.symm ne) kb ka (bin_comm d a.1 b.1 ▸ pro)
        (bin_comm d a.1 b.1 ▸ fresh) hh

theorem rotate_excludedM {T n} {ws : List Sig} (hi : ImpossibleM T n ws.toFinset)
    (p : List Move) (ok : autoOK T p = true) : ImpossibleM T n (ws.map (movedWord p.reverse)).toFinset := by
  simp only [autoOK,Bool.and_eq_true,beq_iff_eq] at ok
  have onto : Function.Surjective (movedRow p) := fun r => ⟨movedRow p.reverse r,composed_id ok.2 r⟩
  intro k t hk ht h
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
  exact hi k t hk ht run

theorem linkedSet_soundM (g : Forest) (k : Nat)
    (names : ∀ x ∈ g.autos, autoOK (targetOf g) (x.map swapRows) = true)
    (earlier : ∀ i < (g.levels k).1, ImpossibleM (targetOf g) k (wideState g k i).toFinset)
    {pair out} (h : wideLinks g k pair = some out) :
    ImpossibleM (targetOf g) k out.toFinset := by
  unfold wideLinks at h
  split at h
  · contradiction
  next valid =>
    cases e : g.autos[pair.2]? with
    | none => simp [e] at h
    | some perm =>
      simp only [e,Option.map_some,Option.some.injEq] at h
      subst out
      exact rotate_excludedM (earlier _ (by omega)) _ (names _ (List.mem_of_getElem? e))

def nodeVerifiedM (g : Forest) (k i : Nat) :=
  let ctx := wideContext g k i
  prelim (targetOf g) ctx && (if k=0 then true else testAllM ctx ctx.2.2.1)

theorem nodeVerified_soundM (g : Forest) (k i : Nat)
    (samples : properPairs (targetOf g) (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2))
    (cols : ∀ ci ∈ g.cols, Slice (varsX (rawMask g.mask ci)) (targetOf g) (subcube ci.1 ci.2.1) ci.2.2.2.2)
    (names : ∀ x ∈ g.autos, autoOK (targetOf g) (x.map swapRows) = true)
    (prior : k>0 → ∀ j < (g.levels (k-1)).1, ImpossibleM (targetOf g) (k-1) (wideState g (k-1) j).toFinset)
    (checked : nodeVerifiedM g k i = true) : ImpossibleM (targetOf g) k (wideState g k i).toFinset := by
  simp only [nodeVerifiedM,prelim,wideContext,Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true',List.contains_eq_mem] at checked
  have hN := checked.1.1
  have hT : targetOf g ∉ wideState g k i := by simpa [wideState] using checked.1.2
  by_cases h0 : k=0
  · subst k
    intro t u lo hu h
    have ht : t=0 := by omega
    subst t
    generalize he : (wideState g 0 i).toFinset = S at h
    obtain ⟨_,hS,_⟩ := h
    exact hT (List.mem_toFinset.mp (by rw [he,hS]; exact Finset.mem_singleton_self _))
  apply node_soundM (raw:=vars g.mask) samples _ hN hT _ _ (by simpa only [h0,if_false] using checked.2)
  · intro v hv
    apply wide_faithful _ _ _ _ _ (wires_faithful g) v
    exact (selectLive_sub _ _).subset hv
  · intro p hp
    obtain ⟨⟨a,b⟩,_,h⟩ := List.mem_filterMap.mp hp
    exact wideRule_sound g cols h
  · intro tag xs hx
    have e : ((g.index k tag).bind (wideLinks g (k-1)))=some xs := by simpa using enabledLinks_mem hx
    obtain ⟨pair,_,h⟩ := Option.bind_eq_some_iff.mp e
    exact linkedSet_soundM g _ names (prior (by omega)) h

def blockM (g : Forest) (k start : Nat) : Nat → Bool
  | 0 => true
  | n+1 => nodeVerifiedM g k (start+n) && blockM g k start n

theorem block_atM {g k start n} (h : blockM g k start n=true) (j : Nat) (lo : start≤j) (hi : j<start+n) :
    nodeVerifiedM g k j=true := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [blockM,Bool.and_eq_true] at h
    by_cases eq : j=start+n
    · simpa [eq] using h.1
    · exact ih h.2 (by omega)

theorem block_mergeM {g k start a b} (h : blockM g k start a=true)
    (h' : blockM g k (start+a) b=true) : blockM g k start (a+b)=true := by
  induction b with
  | zero => simpa using h
  | succ b ih =>
    simp only [blockM,Bool.and_eq_true] at h'
    simp only [Nat.add_succ,blockM,Bool.and_eq_true]
    exact ⟨by simpa [Nat.add_assoc] using h'.1,ih h'.2⟩

def checkedTablesM (g : Forest) (top : Nat) :=
  ∀ k ≤ top, blockM g k 0 (g.levels k).1 = true

theorem forest_allM (g : Forest) (top : Nat) (prior : Nat → Nat)
    (lower : ∀ q, Lower (varsX q) (graphGoal q) (prior q))
    (geometry : graphValid g prior = true) (rows : checkedTablesM g top) :
    ∀ k ≤ top, ∀ i < (g.levels k).1, ImpossibleM (targetOf g) k (wideState g k i).toFinset := by
  simp only [graphValid,Bool.and_eq_true,List.all_eq_true,beq_iff_eq] at geometry
  intro k
  induction k with
  | zero =>
    intro hk i hi
    apply nodeVerified_soundM g 0 i (chart_pairs geometry.1.1.1 geometry.1.1.2)
      (fun x hx => col_sound _ prior lower (geometry.1.2 x hx)) geometry.2 (by omega)
    exact block_atM (rows 0 hk) i (by omega) (by omega)
  | succ k ih =>
    intro hk i hi
    apply nodeVerified_soundM g _ i (chart_pairs geometry.1.1.1 geometry.1.1.2)
      (fun x hx => col_sound _ prior lower (geometry.1.2 x hx)) geometry.2
      (fun _ => by simpa using ih (by omega))
    exact block_atM (rows _ hk) i (by omega) (by omega)

def oneReason (pools : List BoundPool) (links : Nat → List (List Sig))
    (k : Nat) (rest : List Sig) (op : Choice) (reason : Nat) :=
  if reason = 0 then
    let ws := choiceVal op :: rest
    (links (keySet ws)).any (sameWords ws)
  else (pools[reason-1]?).any fun p => scalarPoolCut p k rest op

theorem oneReason_ok {pools links k rest op reason} (h : oneReason pools links k rest op reason = true) :
    closeChild pools links k rest op = true := by
  simp only [closeChild,Bool.or_eq_true]
  by_cases zero : reason=0
  · exact Or.inl (by simpa only [oneReason,zero,ite_true] using h)
  · apply Or.inr
    cases hp : pools[reason-1]? with
    | none => simp [oneReason,zero,hp] at h
    | some p =>
      exact List.any_eq_true.mpr ⟨p,List.mem_of_getElem? hp,by simpa [oneReason,zero,hp] using h⟩

def unarySymbol : Nat → Nat → Nat × Nat
  | 0,w => (0,w)
  | n+1,w =>
    if (w &&& 1) = 0 then (0,w >>> 1) else
      let p := unarySymbol n (w >>> 1)
      (p.1+1,p.2)

def reasonAt (n : Nat) (link : Bool) (data : Nat) : Nat × Nat :=
  let p := unarySymbol (n+link.toNat-1) data
  let j := if !link then p.1+1 else if n=0 then 0 else
    if p.1=0 then 1 else if n=1 then 0 else if p.1=1 then 2 else if p.1=2 then 0 else p.1
  (j,p.2)

abbrev Reader := Nat → Nat × Nat
def moveData (c : NodeContext) (op : Nat) (a b z : Decor) (ka kb : Bool) : Option (List Sig × Choice) :=
  let (cap,n,ws,cov,_,_) := c
  let un := op==2
  let len := 1+(n - (if ka then 0 else 1) - (if un || kb then 0 else 1))
  if len>cap then none else
    let rs := restCov (getCov cov true) (column true a.2) (column true b.2) un ka kb
    if (rs ||| column true z.2) != BitVec.allOnes 768 then none else
    if !properB z.1 || ws.any (fun v => v.1==z.1) then none else
      some ((opKeep un ka kb a b ws).map Prod.fst,movedChoice op a b)

theorem moveData_eq (ctx : NodeContext) (op : Nat) (a b z : Decor) (ka kb : Bool) :
    evalMono ctx op a b z ka kb =
      ((moveData ctx op a b z ka kb).map (fun value =>
        closeChild ctx.2.2.2.2.1 ctx.2.2.2.2.2 (ctx.1-1) value.1 value.2)).getD true := by
  obtain ⟨cap,n,ws,cov,pools,links⟩ := ctx
  unfold evalMono moveData
  dsimp only
  split_ifs <;> rfl

def stepReading (ctx : NodeContext) (reader : Reader) (op : Nat) (a b z : Decor)
    (ka kb : Bool) (data : Nat) : Option Nat :=
  match moveData ctx op a b z ka kb with
  | none => some data
  | some (rest,choice) =>
    let p := reader data
    if oneReason ctx.2.2.2.2.1 ctx.2.2.2.2.2 (ctx.1-1) rest choice p.1 then some p.2 else none

theorem stepReading_ok {ctx reader op a b z ka kb data next}
    (h : stepReading ctx reader op a b z ka kb data = some next) :
    evalMono ctx op a b z ka kb = true := by
  rw [moveData_eq]
  cases he : moveData ctx op a b z ka kb with
  | none => rfl
  | some pair =>
    obtain ⟨rest,choice⟩ := pair
    simp only [stepReading,he] at h
    split at h
    next test => exact oneReason_ok test
    next => contradiction

def itemsRead {α} (op : α → Nat → Option Nat) : List α → Nat → Option Nat
  | [],d => some d
  | a::xs,d => (op a d).bind (itemsRead op xs)

theorem itemsRead_ok {α} {op : α → Nat → Option Nat} {f : α → Bool}
    (sound : ∀ a d t, op a d = some t → f a = true) (xs : List α) {d t} (h : itemsRead op xs d = some t) :
    xs.all f = true := by
  induction xs generalizing d with
  | nil => rfl
  | cons a xs ih =>
    obtain ⟨u,hu,hs⟩ := Option.bind_eq_some_iff.mp h
    simpa only [List.all_cons,Bool.and_eq_true] using And.intro (sound a d u hu) (ih hs)

def pairRead (ctx : NodeContext) (reader : Reader) (a b : Decor) (d : Bool) (data : Nat) :=
  let op := if d then 1 else 0
  let z := movedDecor op a b
  itemsRead (fun f : Bool × Bool => stepReading ctx reader op a b z f.1 f.2)
    [(false,false),(true,false),(false,true),(true,true)] data

theorem pairRead_ok {ctx reader a b d x y} (h : pairRead ctx reader a b d x = some y) :
    testMonoPair ctx a b d = true := by
  have hit := itemsRead_ok (op:=fun f : Bool × Bool => stepReading ctx reader (if d then 1 else 0) a b
    (movedDecor (if d then 1 else 0) a b) f.1 f.2) (f:=fun f : Bool × Bool =>
    evalMono ctx (if d then 1 else 0) a b (movedDecor (if d then 1 else 0) a b) f.1 f.2)
    (fun _ _ _ eq => stepReading_ok eq)
    [(false,false),(true,false),(false,true),(true,true)] h
  simpa only [testMonoPair,List.all_cons,List.all_nil,Bool.and_true,Bool.and_assoc] using hit

def rowRead (ctx : NodeContext) (reader : Reader) (a : Decor) (bs : List Decor) :=
  itemsRead (fun b d => (pairRead ctx reader a b false d).bind (pairRead ctx reader a b true)) bs

theorem rowRead_ok {ctx reader a bs x y} (h : rowRead ctx reader a bs x = some y) :
    testRowM ctx a bs = true := by
  refine itemsRead_ok ?_ bs h
  intro b d u eq
  obtain ⟨v,hv,hu⟩ := Option.bind_eq_some_iff.mp eq
  simpa only [Bool.and_eq_true] using And.intro (pairRead_ok hv) (pairRead_ok hu)

def allRead (ctx : NodeContext) (reader : Reader) : List Decor → Nat → Option Nat
  | [],d => some d
  | a::bs,d => (rowRead ctx reader a bs d).bind (allRead ctx reader bs)

theorem allRead_ok {ctx reader ws x y} (h : allRead ctx reader ws x = some y) :
    testAllM ctx ws = true := by
  induction ws generalizing x with
  | nil => rfl
  | cons a bs ih =>
    obtain ⟨v,hv,hu⟩ := Option.bind_eq_some_iff.mp h
    simpa only [testAllM,Bool.and_eq_true] using And.intro (rowRead_ok hv) (ih hu)

def auditNode (g : Forest) (configuration : Nat → Nat → Nat × Bool × Nat) (k i : Nat) :=
  let ctx := wideContext g k i
  let (n,flag,w) := configuration k i
  prelim (targetOf g) ctx && (if k=0 then true else (allRead ctx (reasonAt n flag) ctx.2.2.1 w).isSome)

theorem auditNode_ok (g : Forest) (conf) (k i) (h : auditNode g conf k i = true) : nodeVerifiedM g k i = true := by
  rcases hc : conf k i with ⟨n,flag,w⟩
  simp only [auditNode,hc,Bool.and_eq_true] at h
  simp only [nodeVerifiedM,Bool.and_eq_true]
  refine ⟨h.1,?_⟩
  split
  next => rfl
  next ne =>
    have ok := h.2
    simp only [ne,ite_false] at ok
    cases hh : allRead (wideContext g k i) (reasonAt n flag) (wideContext g k i).2.2.1 w with
    | none => simp [hh] at ok
    | some y => exact allRead_ok hh

def auditBlock (g : Forest) (conf : Nat → Nat → Nat × Bool × Nat) (k start : Nat) : Nat → Bool
  | 0 => true
  | d+1 => auditNode g conf k (start+d) && auditBlock g conf k start d

theorem auditBlock_ok {g conf k start n} (h : auditBlock g conf k start n = true) : blockM g k start n = true := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [auditBlock,Bool.and_eq_true] at h
    simp only [blockM,Bool.and_eq_true]
    exact ⟨auditNode_ok _ _ _ _ h.1,ih h.2⟩
def deadautos : List (List Nat) := [[],[118,130,81],[100,131,82,16],[118,133,100,131,50,33,16],[116,83,32],[118,116,83,130,49,32],[118,133,33,48],[82,129,48],[118,133,116,83,82,81,80],[116,50,129,80],[100,49,128],[118,100,83,130,81,128]]
def nd5 (i : Nat) : Nat := 0x60650c1c62cf158734b59e30d0081
def level5 : Packing := (1,10,0,0,0,0,1,nd5)
def nd6 (i : Nat) : Nat := 0x20202021e50c1c78ac39a5acf1868040e8ca062cf158734b59e30d0081
def level6 : Packing := (2,9,0,0,0,4,1,nd6)
def nd7 (i : Nat) : Nat := 0x1ae03010003201ca01ae80da070022c035c0bff7deac0622bad65c22925189250081e32a18bb0e696b3c61a01035e503c561cd2d678c3402073149734a49462491868040ccb40f7568a8728a80c4051
def level7 : Packing := (5,8,8,0,0,7,1,nd7)
def nd8 (i : Nat) : Nat := 0x701ae11b20809960395036c14035e0501ae11b008020202000011382480a401d7040c0388039406bc06d839e1a0200000190116021800b01b40458086022606d018402180898180160180b75e01020001ae031711dc020401016e10c004000005b80400005809a01af04b40116035e080178180f3fb9e7991df779dd771db769d2522c5d1343d0b3b8d12d0a8a5290a14711b45915451116418f62703e0b801835f62ed394928c4920706bec5da22925189240e4575ac2925189250081b8aeb84524a3124a01031de8732d11498c34020679d0e6d87acf1868040f33a18bb0f59e30d0081d6d4316696b3c61a0103bca961cd2d678c340206f992e398b2491868040cf525cd28c49230d0081f8a429251892461a010371c872a931248c34020739d0c5da73051868040cf3a5c735958a30d0081ce74b8e6b2b1461a010327e4736c4543ac4501460fd8e6d8ba87408a028e1f31acac950e8114051a3f239950eb1502280a3a75969ab2142a02501474f92b25a3285404a028fb64564a0528a8094051f70c9cd316b24e1280a3ee3139a62d629c2501474eb2d35a42d54062028e97a5a8b465aa80c4051d3e4b4968cb5501880a3a77169ad116aa03101474fc2d1da22d54062028c9f65cd2d449280c405192f439b5a2a1d01880a3e5a15a2a1ca2a0310146fb82e41829451864020dfb05c730528a30c8041
def level8 : Packing := (35,7,8,0,0,10,1,nd8)
def nd9 (i : Nat) : Nat := (if i < 2 then (if i < 1 then 0x101469fb5a82d51862028ebd2b1528a30c4051a2ff688a4d6720a8346fed1149acc415068fbda229358c82a0d1fdb44526b090541a3fd688a4d6020a832fccd6543a0528906f78da82c528a30a0df71b4e58a5146141fe8c61e51ca290083ff0a51d0294520107fe14a39c528a4020ff64a0f38630c8041bec969cc4461900837f80d15878c320106ff25a89cd1864020ff64a0f39a30c80419fc96b082c61900837792d49058c320106fb25a720b1864020dfa4b4c41630c8041bfc168882c6190083fd9283ce58c320106ff25a798b1864020ffa4a0d31630c8041ff4939a62c61900837b92d41828c320106fb25a73051864020dfa4b4c60a30c8041bfc9694c1461900837f12d29828c320107f72507a051864020dfe4b5138a30c8041bfc96a261461900837f92d3cc28c320107fd24e69851864020ffa498b30a30c8041ffc140a61461900837f92d3ca28c320107fb21a79451864020dfe4b4d28a30c8041ff893965146190083ff80c14a28c320107ff05029451864020ffe09c528a30c8041bf496985146190083ef4a72d4394510107fe84e59451862020d1ef3555a0b252521a3de6aab3964a4a4347bcd55662c949487e9cce6a4930a7090ff299cc492614e121c5fd5aac4160942438fbab55842c1284871bf18b30f5168010e9ee31461292d0021b3dc6aa93124a004367b8d552524940086fae1a5acf3868010fbc6a9129251c8021f78d51e524a390043ef1aa34a494720087fe14a494730a4010ffc494928e70c8021fe7139a614e1900432fd8d6548947100867f91ac94740a2010fbd235528e5144021ff6130e30cc08804337a8d4d842cb100867f85a3b024962010ddeab504949244021bbd1684929248804337e2d098994910086fd95a631728e2010dbf2b5462251c4021bee569cc44a3880437ecad318894710086ff15a431128e2010dff0b4262251c4021bfa5694b44a3880433fc8d654894710086fe95a529128e2010dfd2b4a4a251c4021b7e46aac3ca3880437bc8d458694710087fe150524928e2010fbe2a8b41241c4021faf141e90ce188043fda2839249c310087fb44e62493862010ffd0a0b28e70c4021ffa129251ce188043fdc283c839c310087fb84e69073862010dff0b4b20e70c4021ffc141241ce1880437ee2d31658c310087fb85079c31862010dfb0b4c62e30c4021bfe1694c5c61880437fc2d29498c310086ff85a830b1862010dff0b5059630c4021bf61698b2c61880437f82d21658c310086ff85a828b1862010dff0b5049630c4021afe16ac82c61880436fc2d51058c310086ef85a920b1862010dfb0b4c41630c4021bfc169082c61880437fc2d44c58c310086ff85a798b1862010ffb0a0d31630c4021ff6139a62c6188043ff4282cc58c310087ff04e62491862010ffe0a0a49230c4021 else 0x18a114051c7dd622b2142280a38ebac3564284501471fb568b06508a028e2f6ad160ca114051c7cd592c1942280a38feac4562284501471dd586ac4508a028e3f2b07588a114051c7dd62ab2502280a32fd8d6543a04501471fb58ba87408a028f3e6ac950e8114051e7e550eb1502280a38fbac5564204501471fd58aac4408a028e6fcad16048114051cfd9592c0902280a39fe2b15812045014717f58aad1388a028e3eeb155927114051c5fd62ab44c2280a3cafab4546984501471f758aac9308a028f3aea8d5926114051e77551ab14c2280a38bfac55688c4501471f758aac9188a028f2f6ad150e3114051e7cd592a1c62280a3cfcaa1d628c450146bde5ab30d404a028f3ec3155928094051e7d951eb2501280a3deb0c3564a02501479f6546ac9404a028f6eca0d5928094051e7d9592a1d01280a3cbd2b4543a02501479f2564a87404a028f3f831558a8094051edf16a2b1501280a3cfe2a3d62a0250147bdc186ac5404a028f3f8a8d58a8094051edf141ab1501280a3df62d2d62a02501479fc543ac5404a028f3f0a8758a8094051a7f96aca1501280a36ef2d3142a02501479f6564285404a028dbf4b4650a8094051edd959281501280a3dbe2b1502a0250147be6564945404a028f7d8ac528a8094051fdb140a51501280a3d9f2d3d689c250147b3e568a0f384a028f67cad139a7094051fe3939a62ce1280a39fb2c45649c2501479f6548ac9384a028f76ca0f5927094051eed939ab24e1280a3df3262d649c2501473fc588ac5384a028f3f8a9158a7094051eef169eb14e1280a3dde283d629c250147bbc4e6ac5384a028f7d898b58a7094051e5f95a2a14e1280a3cfb2b25429c250147b3e5689c5384a028f76cac938a7094051eef158a714e1280a38f9ac55648c2501471f958aac5184a028d9ee353512a148051bbd86a6a2501900a3fb62814a2a0320147f8e4e698b3864028c5ee353610b544051c77d622c316a880a38f7ac45852d5101471f7588b085aa2028e3aeb0d610b544051c79d616c216a880a38fdac45832d5101471f3584b065aa2028e3fab11608b544051c77561ac116a880a38fcac1d822d5101469f75a42d55222028c3eeb585a89244051a7ed6a0b5543880a34f9ad216aa87101461fb1acad150e2028d3eeb485aaa144051e7ac5aa51ca2880a34fe8d5d4394510146be75a42d528a2028dfd8b426225144051bfb1684b44a2880a37f62d092894510146bed1aba8728a2028f3d235750e5144051f7a4626a1ca2880a3ef089254394510146bf65a42d54062028f3ecb485aa80c4051e7e968cb5501880a3cfe2d116aa03101479f616a2494062028f2f4ad150e80c4051e7e85aa41d01880a3cbf0b5502a0310147fac1a79454062028ffc824928a80c4051f7a150e51501880a3ff4241ca2a03) else (if i < 3 then 0xdc8f6a3cecf133ba8ed33aa0e7c3994e4e38dce20381cdee375cdaf369cd8e3618d5b34c0d083380cc932c8c7531b4c653138c1e2fbcbe72f28bc22e94b882d80b2b2c50ae92ad8a8e2994a4e2894a0e27dc9e0272499c265097d255093924c4917243c8dd23548cd229487d212883320708051fb87d71f007a91e4878a1e087691d847591d4473a1c8c6f11ba46d21aec6a41a34676197c648190062918485f7176c5c416f05a5163858615bc5671540539148851a14484fb13904ca12cc49c121447d11d446d119445d115444d10d840e10183fe0fd83ee0f183af0e9c39f0e203710d683520cec3330c702d60afc2b70a8027309ac263096c253092c24308ec23308ac223086c213082c1f407b01e407701c506f41b506b4196063818605bc1580540148050013804840f703bc0e703400b9028808b01d006c019004d00d801f005c000c35f62ea49462490386bec594928c49206cd7da72925189240d9afb44524a312481cb5f62e939462490336bed614624948a0637f1abb0a5268040cef4b4760492d0081b9dd688a4924a01033abad614624940207c5714928c4928040d8ee35549892500819cfd69cc5c61a010379dad398b8c340207f3a5a73171868040def4b4e62e30d0081bce969cc5c61a01037bd2d118b8c340206f7a5a72931868040def4b4452630d0081bde86b2b3c61a0103dbd0c5d678c340207f3a587acf1868040ded434b59e30d0081bde86b2b2461a010373d0d4d448c340207f7218b2491868040fce429249230d0081fd4851892461a0103f392931248c340207f5a1469c91868040def435760a30d0081ade96acc1461a0103bbd0c59828c340206f3a5a73051868040def4b4a60a30d0081bda9694c1461a01037b92d21828c340206f7a1acac51868040cef435958a30d0081bde9694b1461a0103f390925228c340206f7a5a52451868040d6f4b5628a30d0081b9e96a451461a01037b92d20a28c3402066f39a9b085a230b8db5e34b59ea1d0071fce941e80c61a00e3ecdaa1cc39c1301c66f39a9b0858a51b0fb36a8738e704c0619f5b6b0b3124a02a36bd2d4180a87405465fe1aab0058a80a8e9ed3144929150151b9f3688a4d02a02a3f364a4d0294540547f4c966a0528a80a8fcd9a4940a5150151fd92492814a2a02a3f476734c5a4938547f86ce698a49270a8ff159cd31641ce1519bce6a6c21688c2a3771ed2928249185469f75aa9cd590a028e3eeb155926194051e7cd592a1cc3280a35f6ad2988ac450146bfc5a1311588a028f3bab0d51ab114051a7f56aa73562280a3cfcac1d43ac4501479f9588a87588a028f3d2b0b50eb114051a7f56aa71d62280a3cfcaa1ce3ac4501469fd5aa987588a028f3f2a8730eb114051e4fd5a0c3d42280a3cdb8c3d64a84501471df568b0c508a028e2bead16 else (if i < 4 then 0xa050240279a0802005e020000bc074022c04341040116045808703009e03013c120278080402e00808000e301b80202235c0101c70400038c04101c70200038c0407180a6b01ee00ae11036cdf40610086002d07a0116021a0b40308043414021a06e0080802013e7030149c0c023809009e38180802e0080ae03019c0c02ae03b802052e06b8020438180570180ab80ee00814e06019c0c023818060e12011c049709008e029704dc01028b848047014b826e0081201d7034e09780204035c04200a201ae04804f5c2405008b010c04b82405009eb8480970480c028a05a022c0432a05035c12021005100d702007026ef80304de502bc0182802035e0404300bc7282250280d78380458086027004580d78274100368200601f63847e00c14a822e00812b802b8440803d00ad708dc01821ee00ae1182541002b8440404580ba08015708c0af80a0670180d380de0081402f00604010001006b814000200d702ba03ee0302750474070201ae03d0040424a40426e01ae0501000180044600c0038e084c0180071c14002038e0400201c702080e381804aee0202100c084c071c10086012640401ae040eb0186038e0a012bb80c0a6e032062040140066a0501ae0402180404300808601fc00022004301160200022c03350400d702720c10301400c40c02c5809a01af04000080c201160480c301340416101ae047e0806c80805701022c02600404c008098010130020260040402015c070200000028140701880800de030232040078080701880805101c0620380c407018809e0801003c1002780c047018c084069c0e0310100c06202780c040004600801e03013c0c027808040000f01809e0301d780e04f04009e0301c0620200000000000000e80c05740770040800000001e813280c09d010080006a0201d40603d004040021880802404010460009ae008035c0c0198080085a010810c406b8100000000000000000000000000300401000000046c0200000050100400005028080d7010000000001ae022026806b810000009201011c020248040718080e30100003c1002780c04f01008004300184760d1832609b81ce036802dfdf7ed1f6c7ca9ee27b2dec37aedeb37979e4778fde147831e0477f1dbd76d5d9675f5d3373a5cb172a5ca171cdc487045bfa6eddb896dc1b506ce5af26b6dac46ab5a8169a9a4268ad9f167a59e166dd9a065e19616565942646191063a18e063618c162a98a2622d86361318245ff17e55f757c65e6d76e5d5d7405ca57125c296f35bad6d45af568d5a1566e594564958c961b578159955b954354a9513542d4e352e94925229473517144550753f54f793c74e7d3884dc535a4cc53084b812b74a3d275493523648251e146e51a245e9163452911043e50cc431109941b106441290333fd0fcc3e80f893 else 0x22c000345e1001da061330623858a4501d305018e035c4364140168522812680ca014849140d6020c040412000e406b816406b9a058202c4510ac07280ec820c0860b01cb01b6080e09885dd81701b60ff000080000037cdc061008bc08d80c61002880806809000d78280808032310080b701c704001003ae05086102001f201ca035c08c4198089c04480a401d704838000eb01d904000080015c0718134061005182c88180c301af040218059100184030c06b8182604601ae049e06814000e581010c0228c04246940a03b00c0430080d70101d8022604601ae05e80c06d80fa8180850280b5d037205f802060000402380788100d70181377c010201340200f01004404f00d702008061809a020000d80203e010040360080ab826e00814e020140281)))
def level9 : Packing := (328,6,9,0,0,14,1,nd9)
def nd10 (i : Nat) : Nat := (if i < 12 then (if i < 6 then (if i < 3 then (if i < 1 then 0x7f551651c4021ff6a82ca388043ff954394710087ff2a0728e2010ffe538e51c4021ffca61ca388043ff918b94710087ff2b1528e2010ffe462a51c4021ffc8b54a388043ff918994710087ff229328e2010ffe562251c4021ffc8c44a388043ff916894710087ff2a9128e2010ffe452251c4021ffc8944a388043ff958794710087ff2a8f28e2010ffe541e51c4021ffcac34a388043ff954694710087ff2a0d28e2010ffe539a51c4021ffcaa2ca388043df954594710087ff2a0b28e2010ffa541651c4021ffcac24a388043ff954494710087fe224928e2010ffe541251c4021ffca724a388043ff94c494710087fd294928e2010ffe560651c4021ffca83c8388043ff950690710087ff29cd20e2010dfe561641c4021efcaa2c8388043ff950590710087ff29cb20e2010ffe531641c4021ff8a8248388043efd128a4310087dea2494862010fbf462290c4021f7ea83d2188043cfd545a4310087dfaa0b4862010fbd461290c4021f7ea8252188043efd503a4310087dfa9474862010fbf549e80c4021efeaa2d0188043ff5124a0310087ff29474062010ffe520e80c4021bfeac44e188043fbd5079c310087df8a433862010fff140670c4021ffe0b44e188043ffc1289c310087f78acf3862010fef141e70c4021ffe2834e188043fbc4e69c310087bf8a8b3862010fff141670c4021ffe262ce188043ff41249c310087ff8a093862010fff131270c4021ffe2524e188043ffc5039c310087ff89473862010ffe128e70c4021ffc241ce1880435fd58a94310086ffab112862010fbf148650c4021ffe280ca188043efc52190310086ffab111862010dff561630c4021ffca81c6188043ff94a38c310087ff8a031862010fff128630c4021f7e2c4c61880437fc5878c310087df8a4f1862010fff059630c4021ffe282c6188043ffc4e58c310087ff898b1862010ffe140e30c4021ffc271c6188043ff84c38c310087ff09471862010ffe44a230c4021ffca83c61880437f95858c310087bf2a8b1862010ffe541630c4021bfcac246188043ff11248c310087ff2a091862010ffe140630c4021ffc270c6188043ff84a18c310087ff09031862010ffe062e30c4021ffc2b546188043ff816a8c310087ff0ad31862010ffe05a630c4021ffc2a4c6188043ff81498c310087ff0b0d1862010ffe159a30c4021ffc2a346188043ff85268c310087ff09cd1862010ffe161630c4021ffc0c2c6188043ff85658c310087ff02cb1862010ffe151630c4021ffc0a2c6188043ff85258c310087ff024b1862010ffe141630c4021ffc082c6188043ff84e58c310087ff098b1862010ffe159230c4021ffc2a246188043ff85248c310087fe02491862010ffe131230c4021ffc25246188043ffa461a0108087ff88c31021010ffe11862042021 else (if i < 2 then 0xf6b064164010dff560882c8021bff2c0905900435ff58a9cb20086bfeb153164010f7dd5225248021efbaa3ca490043df754694920087beea8b2924010efed5a251c8021efdaa44a390043dfb54794720087bf6a8d28e4010ffcd29251c8021ff1a524a390043bfd56898520087bfaa9130a4010ff7539a6148021feea62cc290043ff54a498520087ff294730a4010ffad28e5148021affac550190043bfe5689c320087f7ca0f3864010fef939a70c8021eff2a2ce190043ff64a49c320087ff49473864010fff130a70c8021affac54a190043df754890320087beea8f2064010f7dd51640c8021ff9a51c8190043ff64e190320087fd394728a2010dff960492c4021b7fac4905880437bf58720b10086fbeb0c4162010dfdd61082c4021bfdac1905880437fe58120b10087deea504922010dbfc6265244021efd8c54a388043bfb56894710087bf6a9128e2010f7ed51a51c4021efdaa2ca388043bfb56494710087fe624928e2010ffad29251c4021ffcac14a388043ff94a3a0510087fba98b30a2010ffe528e6144021ffca51ca288043fe94a394510087ff294720a2010ffc520e4144021e7ecc4d4588043fbcd079c310087f799cd3862010eff359a30c4021f7e69346188043efcd258c310087ff88c34022010fef538e7044021fde270ce088043ffc4619c110087fba9873022010fff11866044021ffe230ca0880437fd58829310086ffab0a5262010dff561cb444021bfeac2968880437fd5832d110086ffab0a5222010dff561c9444021bfeac2928880437fd58125110086bfa31549e2010fbf44a293c4021f7ea93d06880437fd5889cd10087f7aa0f39a2010dff5620b2c4021beeac3165880437f55842cb10086ffab065962010dfe560cb2c4021efe8a4d4588043dfd148a8b100873fa3175162010f7f4626a2c4021efe8c454588043dfd168a8b10087bfa2515162010f6f461ea2c4021efea83d4588043dfd506a8b10086ffab105162010dfe560ca2c4021afeac5125880437fd58824b10086ff8b024962010fdf541e82c4021efeaa2d05880433fd58b20b10086bfab144162010dbf562482c4021bdeac3905880437dd58620b10086feab084162010dff560c82c4021bfcac1905880437fc58120b10086ffab113962010fef541e72c4021bfeac44c5880437fd58798b10087fbaa0d3162010ff7539a62c4021ff6a82cc588043ef552824910087deaa4e4922010ffd541c9244021ffaa8312488043ff54e624910087beaa8a4922010fbd44949244021ffaa8292488043efd527a0910087bfaa8b4122010f7f55166244021b7e8c4ca488043efd527a0710087bfaa8b40e2010dff562271c4021fdea83ce3880437fd58898710087fbaa0d30e2010ffe540e61c4021bfeac44a3880437fd58794710086ffab0d28e2010f else 0xfd46a4b29086dfbb044a29090e3df5a89252121b5fec3905a42436dfd8620b48486defb084169090dbef60c82d2121b7eec1105a42436ff58020b484871efad45929090f2ff52683ce121f5f683d219c2436fe989a9138487ded3094a27090dff3608944e121f5f6a4d079c243ebed28a0f38487d7da5139a7090f3fb4a2a2ce121e7f6935459c243dfe180a8b38487ded3094967090dbfb62682ce121b7f4c4d449c243ebed07a4938487d7d9cd4927090f3fb516924e121f7b6941249c243ef692824938487f6da0e4927090fbdb498924e121fdb6731249c243df6d4524938487deda4a4927090dbfb626824e121b7f4c4d049c243e7ed28a0938486dfdb132927090fbbb496524e121fce6734c29c243efcd2598538487fb998b30a7090fbf3492614e121ffa4924c29c2439ff180ad5284865ffb105a65090c7ff62ea44a121c7fcb4d48942438ffd6aa49284873efad44925090e7fd5a8b04a121bbfac4160942437f75842c128486ffab045825090d7fd61cb550021aff8c5567a00439ff16aacf40086fde30b59e8010d7fc62a93d0021aff8c5526a00435ff58a2cb40086f7eb0e5968010df7d618b2d0021bfbac2165a00437fb5832cb40086ffab045968010dff9604b2d00219ff8c5d45a00439ff18ba8b400863fe3175168010f6fc61ea2d0021b7fac4945a004377f58828b40086ff6b065168010d7fc62a92d0021d7f8c5d25a0043cff18aa4b400879fea8f4968010f3fd51a92d0021f7b8c2525a00435ff58a24b40086efeb104968010dff960492d0021affac54e5a00436ff189a8940087dee2924928010f7dd51c9250021efbaa3124a0043ef752624940087beea8a4928010fbdd4949250021ebfaa3d04a0043d7f546a0940087afea8b4128010f9fd4968250021f77a92ca4a0043dfb54694740087fe624928e8010ffad29251d0021cff8b5562a0043ef7124a4540087dfaa4b30a8010ffd44926150021fbea824c2a0043d7f16aa0340087afea8f4068010f5fd51680d0021fbb892501a0043d7f543a0340087ef69474068010fdf940670d0021fdf2b3ce1a0043fbe5079c340087f7c9cd3868010f7f951670d0021f7f292ce1a0043ff61249c340087efca093868010ffe928e70d0021ffe2614e1a00433ff18b94340086bfeb152868010fdf940650d0021f5f6944e19c043ebed269c338087f799853867010fef9386804e021e6fea4cc398043ddf4c3a8130087f7c9c33826010c3ff62ea4ca021c7feb4d48940432ffd8ba51280871ffad351a5010ebf75a6614a021d7fab4d0094043ddf186a91200873fead151e4010d7fd62a83c8021cffab4546900435ff58aa0d20086bfeb1539a4010e7fd5a2a2c8021edf8c3d45900435ff58aa0b20086bfeb144164010dbfd62482c8021bdfac3905900437df58620b20086f)) else (if i < 4 then 0xcc4d68a8a438ff969ad1514869ffb125a2a290d7fd600b454521c5feb4967a8a438bf9692cf5148737fad059ea290d3fe626b354521c7fcb4d66a8a439bf967acd514861ff31749aa290f2fe59e9354521a7fcc4d64a8a438ff969ac7514871ff2d3582a290e7fd5a4b054521affac4160a8a439ff5682c1514873feace582a290f6fc59cb054521cffab3160a8a439ff5632c1514871ffa935a0a290e3ff5a6a414521cfdea456328a431ffd882d5494871ffad45269290e3fe5aa9452521a7fcc5527a4a434ff98aa4d494871ef3095aa9290e3ff5a8b552521a7fec416aa4a434ffd862d5494869ff3155a29290e3fe5aab452521a7fec5168a4a436fdd822d1494861ff3175229290cbff62ca452521b7fac0148a4a434ff98aacf494869ff31559a9290d9fe622b352521c7beb5164a4a43af796a2c9494871ef2d45929290ebdf5a0b252521e7bea4164a4a43af7d672c9494879efa8e5929290ebdf598b252521e7bea3164a4a438ff96aac5494871ff2d55869290c3ff626b512521c7fea4d6824a431ffd8ba90494871ffad54a09290e3ff5aa9312521cff6a456124a43afed28ac2494875fda4d5849290cfeb60eb092521c7fcc4d6aa0a439df986ad5414873fe3015aa8290c3ff624b55052187fec5d49a0a438ff98ba93414879ef3095268290c3ff62ca4d0521d7bcc256920a430ffd8ba92414861ffb165248290eb7f526b310521c6fea4d6620a438df949acc414865ef3135908290ebdf526b210521c7bea4d6420a438fed49ac2414871fd2935848290ebfd526b010521c7faa4d6020a438ff149ac0414871ffad549a7290c3ff624b54c52187fec516998a438ffd49ad1314871ffa9359e6290f37f526834c521e6fea4ce698a432ffd852d3510871ff2d351aa210cbfe62e9354421c7fcb4d45a88432ff98ba4b510869ffb1539a9210f2fe61ea2d2421a7fec5505a48434ffd8a20b49086dbfb0c4169210dbfb60482d2421b7fac0105a48434ffd8a9cb490869ffb153169210dbdf614a492421a7bec5526248434f798aa4c490879efa8f4989210d7df62a7312421b7bec4ce624843cf7d499cc490879ef2935149210f3de626a292421edbcc3d4524843cf7d27a8a490879efa4d5149210d3df62a9292421a7bcc552524843cf7d48a4a490879efa8f4949210f3df51a9292421a7bec5125248436f7d8824a49086defb0c4949210f3df5189292421b7b6c0925248435f7d8aa0a490879efa934149210cfdf62c8292421afbec5105248436f7d8920a49086fafb0c4149210dfdb6048292421bfbac0105248435f7d8a9ca49086defb133949210d7df62a6292421b7bec4cc5248430ffd8a2d3290865ffb105a65210cbfb604b4ca421c7feb4d48948438ffd69a8f290871ffad351a5210e3fe5a6a34a421e77ea3d2594843ce else (if i < 5 then 0x6248146141bfd6c29028c2837fa58020518506ff5b1138a30a0dfeb6226146141bfd6c3cc28c283fdace698518507fb598b30a30a0ffe340a6146141bfd6c3ca28c283fba98794518506ff5b0d28a30a0fbeb49a5146141ff5672ca28c283ff896294518507ff1a0528a30a0ffe338a5146141b7d6c48a28c2837dad8614518506ff4b0028a30a0d7ed60cb550041affac116aa00834ff585293401079fe29341e8020f3fc52672d0041efda73543a0083dfb4e5a8740107bf698b50e8020f3fc5268150041e7f8a4ce2a0083cff14994540107bf6a8728a8020ffad28e5150041efdaa1d01a0083d7b543a0340107ff4a031868020fde940630d0041ffd273461a0083ffa4e58c340107ff498b1868020ffe938a30d0041ffd261461a0083ffa4a28c340106feeb1139a4020fedd41e7348041b7bac4905900837b758720b20106faeb0c4164020dfcd60c82c8041bfbac1105900837f558220b20106fecb024164020fedd41e72c8041bfbac3cc590083fd750698b20107fae9cd3164020ffcd41e51c8041ff9ac34a390083ff350694720107fe69cd28e4020ffcd60a51c8041ff9ac0ca390083f77507a0520107fe694740a4020dfdd6227148041ff9a51ce2900837f758898520106feeb0f30a4020ff5d39a6148041feba62cc290083ff34a398520107feaa0530a4020dfdd61e5148041fdb8c3ca2900837f758694520107fce9cb28a4020ffcd28e5148041ff1a51ca290083ff550294520107fea9c528a4020df5d6185148041bf9ac18a290083ff34a3a0320107eeea054064020dfdd62270c8041fdba83ce190083fb74e29c320107feca033864020ff9d28a50c8041ffb280ca190083ff35078c320106fe6b0b1864020ffcd40a30c8041ff9a5146190083ff25018c320107fe49c31864020ffc928630c8041ff92c446190083ff21888c320107fe4b0f1864020ffc941e30c8041ff92c346190083ff25068c320107fe49cd1864020ffc961630c8041ff90c2c6190083ff21058c320107fe49cb1864020ffc931630c8041ff92c146190083ff21828c320107fe4a051864020ffc840a30c8041ff927146190083ff24c28c320107fe49451864020ffc828a30c8041affac416a880835fb5832d5101073f6ad150e2020f7ed39aa1c4041efda72d4388083dfb4c5a8710107fda9cb28a2020f7e550e5144041ff4a51ca288083afe18ba4310107dfca0f4862020fbf941a90c4041dfd2b446188083ffa5078c310107ff4a0d1862020ffe939a30c4041ffd272c6188083ffa4c58c310107ff09451862020d3ff620b2d4921c7beb3164a92438f7d652c9524871ffa93594a490c7ff620b5526218ffec296aa4c432ffd882d3514871ff2d3522a290e3fe5a6a354521ddf8b3960a8a438ffd692d3514869ffb105a6a290d3ff610b4d4521a7f else 0x73862028e7fc5aa30c4051afdac5461880a39fb16a8c310147fd29451862028ff3b41a62c2051fe76734c5840a37eed8520508147f9d98b30a1028ff393166042051fef261cc0840a34ffd822d54a1069ffb105aa93a0d3ff608a4d0741c7fea4d689cc83cbfd49a0f399069ffb105aa92a0d3ff608b55254187fec594920a834ffd822924150717fa9359c82a0e2fe526b390541c6fea4d6620a838df949acc415071f7a9358c82a0e3ee526b190541c7eea4d6220a838fd949ac4415071fda9358482a0e3fa526b090541c7faa4d6020a838ff149ac0415069ffb0452672a0f2ff52683ce541e5fca4d079ca838ffd49acf315079bfa9341a62a0f37f526734c541afdec44e6a8683dbbd079cd50d069f7b12416a1a0d6ef61c82d4341aedec3105a86835f9d8220b50d06bf5b02416a1a0d7ed60082d4341edde83ce5a86835fbd8798b50d07bb7a0d316a1a0f76f39a62d4341afdec116a9468377b988acd28d069ffb105aa9120c3ff62ca4d0241a3fec4149a04834ffd85293409069fbb045268120c7ee62ea1d024187fec5949204838ff949aca409077d7acb28c8120e3fc526b010241cfdaa1d60204834ffd88293389069ffb0a5267120f37f52662cc241cfdeb3d4398483ddbce6a8730907bb798b50e6120c3ff62ca4ca241a7fec4149944834efd85293289073f7acf50e5120f6ee59ea1ca241cfdeb354394483debce5a8728907bd731528e5120feae59e51ca241efcea1d0294483fe9ca3a0528907bf3a8738a5120ffa728e714a24187fec5949144838ff949ad0289071bfa935985120e37e526b30a241cedeb3543144839fb543ac028906dfdb0a5a290a0dbf260ab3d2141b7f6c44e6a4283ebed079cd48506dfdb1059690a0dbfb608b2d214197f6c5905a42836bed8720b48506dbdb0c41690a0dbeb60c82d2141b7e6c1105a42836fe58020b48507d7da0f39690a0dbfb61e62d2141f6f6834c5a4283edece698b48506dfdb0a58a90a0f9fb41e8152141b7f6c2902a42836fe58020548506dfdb1138a90a0dbfb6226152141f6f662cc2a4283efcd0298548506dbdb0c28a90a0dbeb60c5152141b7f2c00a2a4283cbfd49a0f38507b77a0f50e70a0fafb41e90ce141fdd683ce18c2837bad872d118506ff5b0a5a230a0dfe9600b446141bfc4c15678c2837fad889cd18507f75a0f39a30a0dfeb620b2c6141bfd6c31658c2837fad822cb185067f5b1641630a0dbeb62482c6141bdd6c39058c2837dad8620b18506ff1b0441630a0dfe960082c6141fdd683ce58c283efad269cb18506ff5b0f31630a0ff6b41a62c6141fed6734c58c28377ad882c518506f75b0e58a30a0df6b618b146141bfd6c29628c2837ead852c518506ff4b0058a30a0fbeb39a9146141f7d672d228c283efacc5a4518507ef5a0f40a30a0dbeb))) else (if i < 9 then (if i < 7 then 0xaa02501476fcad1404a028f7f951e8094051fef0c3501280a3dfe546a0250147efca0d404a028efd95928094051eff2a1d01280a3dfa543a02501477fcac5404a028eff158a8094051eff0a1501280a3f7e502a0250147fdc945404a028dff96227094051dff2b44e1280a3b7e5689c250147bfca91384a028fef941e7094051fdf2734e1280a3fee4c59c2501477ecac9384a028eff958a7094051dfe2b14e1280a3dfe5429c250147f7c9c5384a028edfd5a23094051dfbab2461280a3bfd5628c250146bf6b15184a028efed5a23094051dbdab4461280a3bf35648c2501477f2ac5184a028f37f52661cc051eedea1cc3980a35ff58a9cd20146dee3135124028f7cd512a1c8051efda73543900a3df7544a8520146bfeb1440a4028dff96048148051eefaa34c2900a3fde186a0320147efca0d4064028ffd951280c8051efd2a1d01900a3f7e502a0320147fdc9454064028dff962270c8051fdf283ce1900a3fbe4e69c320147fdc98b3864028fef938a70c80518ffec416a880a31dfd862d5101463f7b065aa2028d7fd620b544051aefac316a880a35fb5832d5101467feb105aa2028cfdd610b544051cffac416a880a31ff5882d5101473beb0c5aa2028e7bd614b544051cfbac216a880a39fb5832d5101473fab045aa2028c7fc62ab444051affac5168880a37ef5852d110146ffcb025a22028cffc62ea444051cff8b5548880a35ff58a25110146fdeb0a4a22028dff960494440518ff8c5d47880a39ff16aa0f101463fe31751a2028e7fc5aa8344051cff8b54e6880a3fcf50698b10147f9e9cd3162028e7dc5a892440519ff8c5d43880a39ff16aa87101473f62d550e2028c7fc62ea1c4051cfd8c5d43880a39fb568a8710147bf69cd50e2028f7cc492a1c4051cff8b5503880a39ff16a9c7101473fe2d530e2028e7fc5aa51c4051cfd8b54a3880a39fb16a90710147bf6a8f20e2028f7ed51a41c4051ff5a62c83880a39ff16aa85101477fa31750a2028f7f5522a144051efeaa1d42880a3df9543a85101473fe2d540a2028e7fc5aa6144051eefaa34c2880a3fcf4c5985101473fe2d528a2028f7ed50e5144051ff5a51ca2880a3dfd54394510147fda94728a2028ffa528e5144051df78b54a2880a3deb54394510147fda31328a2028ffb46225144051ff68b44a2880a3fed54894510147fda25128a2028feb461e5144051ff6a834a2880a3fed4e694510147fca24928a2028ffb53925144051ff6a624a2880a3fed54394510147fd2a8728a2028f7b550e5144051ef4aa1ca2880a3fe9483945101473fe2d54062028ffb528a80c4051dff0b5501880a39fe16aa0310147fec2494062028f7e950e80c4051ffd241d01880a3ffc542a0310147efca054062028ffb928a80c4051ff6251501880a3fee4c59c310147ff49 else (if i < 8 then 0x543a02a3dfa180a8740547fb52cd20e80a8fdeb41a41d0151b7f4c4d62a02a36fed892c5405477bd2cc58a80a8dfbb614b150151bff2c0162a02a36fe989a8540546dfdb1250a80a8ddfb620a150151bef6c3142a02a37f6d8428540546ff5b0650a80a8dff9600a150151aff4c5522a02a3ef6924a45405467fdb1648a80a8ddfb6209150151bf76c2922a02a36fe989a0540547cfd29340a80a8fd7a59a8150151f3f692502a02a3f76924a0540547ddd29328a80a8ff3a59a5150151f776924a2a02a3fe692494540547bd5a8728a80a8ffab20e5150151fb76814a2a02a3f6cd0294540547fd99c528a80a8f2ff52683ce151edde83d439c2a3ebed07a4338546dfd31352270a8dfbb614944e151f5f6945079c2a3ebed289cd38547f1d9cd31670a8dbfa626a24e151d7f6b45249c2a3ebed07a4938547d7d9cd49270a8fbbb316924e151dfb6b41249c2a3fb6d0724938547f6d9cc49270a8ff9b314924e151dfd6b44839c2a3fbad0790738547f759cd20e70a8ffab31641ce151f77662d229c2a36fe989a0538547d7da5138a70a8fafb49a714e151fd7662ce29c2a3ebed249c538547f6d24938a70a8feeb20e714e151fe7662cc29c2a38fb989ad5185473f63015aa30a8deef61cb446151bf9ec21688c2a37ebd8525118547b77a8f41e30a8fbce4a09246151cfd6b55018c2a3fbad079c318546bfeb15398a028e7dd526b214051cfbaa3564280a3bf74e6ac8501477eeac950ca028efcd592a194051cfbab2543280a39f3564a8650146bfeb1530ca028efdd5926194051efdaa1cc3280a39ff549ac4501473fea8f588a028e7fd51ab114051cffaa1d62280a39fb543ac4501473faa93588a028eff5622b114051dfe8c4562280a3bfd587ac4501473faa8f588a028eff561ab114051cfeaa3562280a3bfd4e6ac4501477fab0b588a028efb5616b114051dfeac1d62280a3bfd543ac4501477f2a87588a028e7f550eb114051cfcaa1d62280a3bfd4e3ac4501477fa987588a028eff5606b114051dbfab4542280a3bf7564a84501473fead1508a028e5fd5a2a114051edf8c3d42280a39f7564a84501463feb16508a028d7fd620a114051cffab4142280a397f56828450146bbeb0c508a028e7dd590a114051afdac1942280a39fd562284501467feb17408a028d7fd62a8114051dfbab2502280a3dfb543a04501477faac5408a028cffd62c8114051affac5102280a3bf7564204501477faac4408a028dff96048114051affac54e2280a3b7f5689c4501477eeac9388a028eff558a7114051affac54c2280a3b7f56898450147bbea8d308a028efdd5926114051dfeab14c2280a35ff58a8c4501476fead1188a028efdd5923114051efdaa1c62280a3bfd5628c4501476fead1404a028efdd5928094051dfeab1501280a3dfe18 else 0x704c061d6feb4cc2940c35ff58aa0f20187b7ea8f41e4030f7ed51e51c8061eefaa3cc2900c3fdb4a398520187fd694728a4030f77d50e6044061efbaa3924880c3dfb54790710187fb694730a2030ffa528e5144061ffca41ca2880c347f988acd525471efacc592a4a8e3de592b154951c7fea4d62292a32ffd83ac452546bfeb04582a328c7ff620b5526518ffec116aa4ca30ffd822d5499465ffb045a6a228e3fe5a6a354451a7fec54e6a48a36f7d82292491469efb154989228d3de62a9312451afbec54e6248a3cf7d499cc491469ffb04526a1a8d7ef608a4d4351c7dcb4d66a86a357b988acd50d47be79cc492a1a8e3ee5a6b154351aedec3162a86a35f3d842c550d46bf6b0058aa1a8d7ed608b054351afdec54e6906a32ffd882d3509469ffb10526a128d3ff610a4d4251c7fcb4d48a84a38ff969a8d509469ff313512a128f3de5249254251c7feb4d48284a38dfd49acc509473bfa91598a128cbde626b214251c7bea4d64284a39f7d48ac8509473f7a9158ca128e76f59aa194251cf9eb2543284a39ff548ac0509473f6a87580a128c7ff620b552251c7bcb5124a44a34ffd882d5489461ffb105aa9128d3ff628b452251b77ec2968a44a36fed812d1489465ff3175229128e3df5a8b252251c7bcb5164a44a30ff98ba87489461ffb135a89128e3ff5aa9412251c7feb5526244a3aefd28aca489475dfa4d5949128e3df5a89212251d7beb4124244a3ae7d65248489473d7acb50c9128ebfb4a2b092251d7f693561244a3af6924ac2489473f5a875849128c3ff624b5502518ffac016aa04a32ff98ba93409465ffb165268128e3ff5a8a4d0251b7eec1149a04a30ffd8b293409469fbb045268128d7fc62ab050251cff8c056a204a30ffd8ba92409461ffb165248128e3ff5aa9210251cfbeb5124204a38fbd69a86409473f7ad520c8128ebfb492b090251dfb492561204a39fad43ac2409477f59075848128c7fc62ab010251c7faa4d60204a39fb543ac0409469ffb105267128c3ff624b54c2518fdec196a984a34ffd88293309479bfa8d4926128f75f518924c251cfdeb3d43984a3ddbce6a8730947bb7a8d20e6128f37f51a914c251c7feb51498c4a34ff98aa51189469ff31549a3128dbbf6149452151c7beb5124a42a3cbfd47a0f485471efad459290a8cbfe62e8152151a7fec1149a02a36fed8429340546dfdb0452680a8dbfa626b3d0151d6f6b4966a02a3bded672cd40547dbda4e59a80a8f9fb49e8350151b7f4c4d65a02a36fe989ac940546dfd31351280a8fb7a59a9250151f3f683524a02a3ef696924940547ded29249280a8fbdb49c9250151feb4b3124a02a3ef6d2624940547eeda0c49280a8ef7a59ab1d0151e7f4a4d43a02a3dfa949a87405479f531350e80a8f7ea5a6a1d0151ef9492)) else (if i < 10 then 0x926138daff61c9452171f5be83924a42e36bfd872d1485c7d6fa0e59290b8eaff5a683d0171bddec39688c2e37f3d842d1185c6f77b0e4a230b8fbce4a09246171affac116aa00e37af185acf401c7d7ea0f4968038fafd39a92d0071fdba83924a00e3fb74e6249401c7b7eacf50e8038feed39a51d0071fdda73483a00e3f3f507a03401c7afea874068038fdf940630d0071efdaa4461a00e3fbb5078c3401c7ff4a031868038fde940630d0071e5fe945439c0e3cbfd26a87381c7b77a8730e7038f6fd50e804e071e6fea4cc3980e3ddbd43987301c7bbe9875026038f6fd50e704c071fcfa61ce0980e3f9f4e698b201c7f769cd28e4038fe7d39a6148071fdda83c61900e31ffd882d5101c737f2d541e2038e6fc5aa7044071affac416a880e3dbf16aa0f101c79eea924922038fedd41c9244071fdba73124880e3fbb507907101c7f769cd20e2038fafd41e90c4071fdda83c61880e38f7d6a2c94a1879ef3094a2a3b0f3df520b252761c7beb5164a4ac3cf7d472c9495869ffb1458a92b0db7f618b152561c7fea4d6224ac3cbfd47a0f491869efb154a09230f3df4a2a392461a7bec5527248c3cf7d48a4e49186befb1541c9230f6df51e8392461e7bea3d25248c34f7d8a24a49186defb104949230dbdf6089292461c7feb4d489c8c3cbfd48a4f391879f7a5151e51b0f7cf51c924a361afdec5162946c37dbd862c528d86fe7b0858a51b0f6ef51e83c8361e7bea4124a44c3cf7d47249489871efad45929130e3ff526b292261c7feb5525244c3adfd66a4a489871efad44909130ebdf5a09212261d6beb3124244c3af7d65248489873f7ad528c9130ef6f59a5192261df5eb2ca3244c3ef392494648987daf3094a26130fb5e61292cc261e6fea3d24984c3ed7d2824930987bafa8e4926130fb5f49c924c261f6be92924984c3ed792524930987db7a5128e6130ff4e49251cc261eedea3c83984c32ffd882d3289871ff2d35225130f3df524924a261ff1c924a3944c38ffd69a90289865ef3135905130e3df526b20a261cfbea4564144c39fbd6a906289877b7acd20c5130e7fd522b00a261f7b4c2527a02c36fe989acb40587deda4e49280b0fbdb4949250161f5f693ce4a02c3ef6924a4540586efdb1048a80b0dbfa6265150161b7f6c48a2a02c377ed8814540586fedb0828a80b0dfeb60c5150161bff2c00a2a02c3cff547a4b40187beea8e4928030f7ed51e51d0061efdaa3c83a00c3edf52598540187fae24930a8030ff6d28e6150061feda41cc2a00c3f76124a0340187efc9c94068030fde920e80d0061fbf0b1501a00c3f7e122a034018797fa9338e7030f6ef50e71ce061e6fe93d43980c3cdfd25a8730187bb7a8738e6030f76f50e51cc061e6fea1d22980c3fcbca394530187bbea873826030fe7d38e else (if i < 11 then 0xf48a071ff2d549e9140f37e524a352281a7fcc5526a45038ff96aa4b48a071ef2d44929140fb5e5189252281f7b492161a45030ffd89ad448a073bf30d5a89140cdfd602b412281cefeb514624503b5fd6828c48a071ffa935949140e3ff5aa9292281d3feb4525245038f7d6a24848a074efad04909140ebdf594921228187fec5949945039f796a24928a079efa924925140ebde612b48a28187fec5d49145030ffd8b29228a065ef3135905140e3df526b20a2819fbec5924145039f7d6a24828a075efad24905140ef5f598920a281c7faa4d6014503bdf146ac028a077ee2495805140e37f5a4a354081c6fcc3569a81038dfd692cd50207abf28d50a8040fd7a51a30d0081bbfac3949a010377f58529340206efeb045268040ddbc616b3d0081b9fac3965a01037775842cb40206efeb045968040ddf5608b2d0081bbf2c0965a0103e7f149a4b40206afeb144968040ddfd60892d0081bbf2c0925a010367f189a8940207cee2924928040fd5c5189250081f3ba93124a0103e7752524940207ebe28d3928040ddfd614b150081fbb892162a010377f5812c540207cee24948a8040fd7c5189150081bbfac2922a0103e7f52524540206efeb0248a8040cdfd62c5150081b3fac48a2a010377758414540206efcb0228a8040ddfc62e30d0081fbd8c5c61a0103f731248c340207ef43171868040fde95a630d0081fbd0b4c61a0103f7a5498c340207ef42931868040fde959e30d0081fbd293c61a0103f7a5648c340207ef4a891868040fde949230d0081fb9092461a0103f7a4e48c340207ef49891868040fde960a30d0081fbd0c1461a0103f7a5628c340207ef42c51868040fde948a30d0081fbd091461a0103f7a0a28c340207efc8c34021040fde91868042081c7fea4d68292e34ffd842d3521c71bf2d259aa438d3ff608b552871c7beb5164a50e31ffd882d5499c7d6f3094a27338c7ff620b552571a7fec416aa4ae34ffd862d5495c69ffb045aa92b8e3df5a8b252571f5be73164a4ae30ffd892d5315c63f7b065aa62b8fa7f39a62d2471e7acc1549248e3cf7989a90491c7baf30d5209238d3df62a9412471a7bec5128248e36b7d87250491c6defb0a4a09238fade6268392471e7bea4526248e3eb7d07a4c491c7b6fa913989238fadf4a27312471f5be73525248e3f97ce698a491c6bf7b0c5aa51b8d7ef608b54a371bedec3168946e37f3d842d128dc6ff3b045a251b8dfeb604b44a371bf5ec2928946e377b988acd28dc7d77a5139a51b8f3cf524924a371fd9e73124946e3f9bce698b20dc63ffb105aa9138e6fe5aa83d2271e7bea4124a44e3eb7d07249489c7d6f9cc4929138d3ff620b552271e5fcb5507a44e38f7d6a2c9489c7d6fa0e5929138c3ff624b54c2718ffac016a984e3e9fce6a49309c7f2f9cc4 else 0x779e3ba51dbf0edd876dc3b2f1d8b8ec0475f23af11d640ea4474f23a631d268e8d4741e3a071cf00e6e8736439aa1cc20e578726a38fd1c6a0e330718838ac1c4b0e20070f038601c250e0d06ffa37d71bd80de5c6f1e37791ba98dcb46e2e37011b758db086d3836761b280d8a86c0835ec1aea0d6b86b2a355e1a9c0d44469b234b31a468d19868a0342719fb8cefc6730337119a58ccd4661c32f819688caec652a327f19240c8c863f231e318de8c65c62e2314b18920c3f461ae30b018420c1b060a8302d180b8bfb85fcc2fde17dc0bd945e782f15177e0bb8c5d922eb117548ba045cb62e4517168b81c5bdc2dd616df0b65c5ade2d5916990b4a85a282ced16628b27c58f22c5316168b01c57c02bca15d18ae2c56ea2b4c159b0ac3c55d22ab2154e0aa1854ba2a33150e8a7d052fc295514828a3785170289214358a114503e27e713d509cc04de426da135809a244ce226591319898ac4c2a25fc12e2896f44b4e259112bd895cc4ab625431295893dc49322483122a090f8485023aa11c188db446ae2331116d08ad0453c2296113408898443c21d710d60861842a4211e106d0825840a4200e0ff387e843eb61f530f9d87ccc3e561f130f7507b483d1a1e570f17078603c201dc40eb9075643aa21d390e918730039701ca20e3e07150387c1c180e0106fb0378c1ba00dc506d90369c1b380d8006ba835a41aac0d5206a3834d01a600d2c06898343c1a060cff0679833bc19d60cdf066d8335c19a60cc8065a8324a190f0c53862443112182c0c0b05fc02fd017b40bd605e902f3817940ba905bf82dec16ee0b7305ad82d40166a0b31059682c88163c0b06857dc2bde15d90ae1856302aca153f0a948540c29d414b50a4f8522428c6143009f484f4c2740135d099a04c38257c12b6095704a0c24f61255090f847fc2378119608c004568224e1101087584310213810740826040d81fe20fc307cc03dc41e960f25076e03a881cc40e0406ee836d01b0e0d44068f033c419680c8c061502f9017580b49057182ab414e20a1104ec02610125008f0044e0219c101207b703b681c940d92066202f78169c0a9604dc022480f5406ec030e016100908041c00ee005c001fc00d2003f000063df5a8b252176f7ba94124880edff3124947101dbdee249486203b7fcc49230c4076a7ecc1567a93038f7d672c9526071efacc592a4c0f35e598b254981c7bcb2562a93034ffd852c5526071ffa9359ca4c0e3ff526b1149818ffec116aa4f038ffd6a29349e065ffb045a6a240e3fe5a6a3d4481e6bcc3549249036f7d8729249206defb045249240f3de526a392481a7bcc5527249033d7d8b28c492079afa925189240f35e524a312481f6be93946249034f798aa4c492079bfa9251a7240c7ff614b552281c7feb5149a45034ff98aa4)))) else (if i < 18 then (if i < 15 then (if i < 13 then 0x8922438120e6904c481b240351fce8fc147cda3e151ebe8f314781a3b551d4e8e774723a38851c168de546dfa36611ac08d384676a32ed18fc8c4d45fc22e2916c08b4a456ea2ab9150e8a4c45132284113d489c444baa24f111de88d94461a227510e8885e441aa202d0fe687cd43e2a1cfd0de286c3432ba18a50c2685fd42dda16950afe856942a9a145109a8849442292104907a283ab41caa0dbd069283334186a0bdd056e82a1413d2090d043a81de40d8a061102dc814840912042901a680bd403c200dd005e80173ff89ff6cff6a7f7e3fa39fc40fdb27ea23f2d9f90cfc5a7e253f069f7d4fb787d823ea59f50cfa187cb33e4e9f21cf8e27c593e149f04cf79e7bc73dd71ee98f71c7b763daf1ed58f67c7b263d801eb9cf5747aa13d449e960f44279de3cca9e5b8f21678e53c5f9e264f0e6784a3c091dfb0ef68776b3ba19dc70edd076bd3b329d93cec72761f3b049d784eb5075903abb9d4c8e9da74a83a309d0e4e7e873ad39ca1cdf0e6c6734a39a11ccb0e648731c39831cbf8e5ca72cb39591caa8e5007257391f1c850e3fc71e538e69c6d0e314717138a59c408e1ae70bd383c1c188e078701537f71bf14df3c6f7737a79bca0ddfe6ecf37531b9f4dc0c6db136bc1b464d9226c2e35e99ae28d69a6af535541a900d372697b349b9a404d0ca682133db19de0ce406691330d19810cb9e65a132c5995cccaba65443289192fcc8f86466322018fb4c7ae63af31cc98dfcc6d26333318618b88c54c627f311a18830c3cc61bf30cc985c8c2986125307698318c1406068301897fd0bf345f5d2f9b17c80bdf05eae2f4397970bc8c5e302f0417788bb505d922ebe17554ba5c5d072e67972a0b9005c6a2e2197070b7ea5bc92dd196df0b6aa5b2c2d8b16bbcb5925a802d2c9690cb43459f12cdd16634b30a59012c7496308b15458842c2d960d4b01e57f92bdc15e44aece57402b8c95bc4ad9656932b2f158e0abfa55c52abf154f0aa4c55002a6715258a8aa540c29fb14ed4a6b8530a297a14acca4d8522329069471ca2fc515728879432ca148507d282b1407c9fee4fd027d493e009eb24f33278693b549d5e4e892731138ec9c2a4dee26e3936549a5a4d072670932ec992a4c7f26239307c97ec4bbe25c512c9495f84ad625581297c946c4a0e24f39266492de4949247f9231c911e4857240f11f508f5a478723af91c9c8db646b42334119048c3645f522e6116d88b40457922a29143489aa449d2231910a887e043c321ce10dc886b84346218f90be085a442ac21431093c8450421220f590710835c41a620c8105e88284412a2082103f081cc40c02055101c0809440241fff0fd887e763f251f8e8fc547ddc3ec81f460f98c7c783e131eea8f6ac7b003d481e990f47079ec3cb81e510f1e0789e3c261e070efd4 else (if i < 14 then 0x314f17278a63c499e200f0d67856bc21de0e2f04b7821bc075e00aeffd77ebbbf05df72ef93778ebbc55dda8eea8773e3b955dc5eee1976ef3b6d1dacced3e76813b371d968ec8075fabaf39d750eb8275adbac59d5a0eaba753cba929d432e9e774d13a5f1d2ace92f7483ba381d174e878741f3a015cf88e7897399b9bc9cd6ee68f7330398c5cc14e5f472e5b94f1ca2ae4cd725339201c8b2e43371fb38e61c6bee31e717bb8b41c552e2837119b87ddc35ce19870b938531c1fee0e97051381d1c078e0166ff7b7f5dbf4adf766f9d37c85bdc0de976f38b7929bc40ddfa6ef237739bb70dd926ea237461ba04dcdc6e483717db86edc216e05b6fd5b79edba96dc1b6d75b66cdb106d7536ad9b520da636d1cb6841b3f4d9e16cddb6619b2bed9386c9036429b1c4d8b46c4f36259b0e0d8486c193601dafe2d7d96bd935e31aeccd7356b96b5bc9ad7ad6966b3f35961ac1cd5e66ae6b5679ab10d5506a94b53a9a984d4966a2d350c5a830d3f169e534ec5a6f0d35f699034c61a5ded2c56954b4a85a50ed234690d347c1a1d0d0bf684434189a076d0256807b3fa59f86cf00676333ac19d34ce926745339d19cbcce566727338a19c24cdfa66f1336f19b06cd6b66a1334719a28cd0c667a332f598f2cc4b661232fe997a0cbaa65c0b2d31964ccb0c6550329719436ca0564e7324958ff0c7cb63cfb1e158ebac7356385b1b358c7cc5d662cbb15a98a5cc4d9624c311198832c3df61c030d5d8682c30a612ab04a1821cc0f4605e3025980dec0475fc4afd797d62be685f1e2f7ed7ab0bd175e40af10d7766bb785d8aaeb457540ba625d1cae87d73e2b9c45ccb2e5ad727cb8fd5c612e21170a8b8275bf12de856ec6b74a5b8fadc156db8b6a25b3aad9256c14b5ab5ac02d4f96a00b4e55a40ad10d680cb3c559b1accd1660cb2c15941ac9a96432b1ed58e92c68d62e6b131588bac3056106b06858202c05d5fdeafa257b42bc895db8ae965737ab9255c46adb556b8ab5a55a7ead1956792b331594aac8c56282b03d57ecabdd55dbaae855712ab7155acaacb95592aa965537aa8d15402a9d854b3aa57d525ca8f15452aa0354fa8a741537629b594d5ea684532f298d54c1ea5e852de295b14a68a4f2526ca930d4956a4855217a901947e0a3a851ba28cbd45eea2e1514b289bd4490a232510e2872d4302a16850a8284e1421ea0e95061a82b540d8a041500d27fd13f9c9fa44fc727d453e509f004f5ca79f93c889e2c4f01a77ad3b8a9d9c4eb0a75253a469cce4e542724938f49c404e0226b89355c9a644d1da67b533ca99b74cb6a6549323698df4c5ba60ad300a97eb4beaa5e852ea6971b4b7aa5b7d2d9296a24b20258a92be495ca4ad0a55ed2aca953c4a82252292880941249d2a4ddd261492d84935a48f5238691914 else 0x5481ae04018d2470f00825007881b2080282901440e7027240c7825e0178440e3047799260281540409f0434840291003a80d702238112800a05039c0e3030528047406b8111c2203010d3c0209401c608213367c621880a2085418089883c0609001ae0609b903c2007881b3060e61460603bc24f0181b2080e26f16461e1050100f1035e101b1e70a00218bc12a023c0607582f0324090304f8071c191c880c0434f00825007602143ccef800f1013de1050100e3857ef17bb5b5b9f602c4062028886213e01af0c5862c31d9ec30f093c2002781c7088433677a03110c404f04121108660db77a03110c404f03c61004491310c40d703640c00cdef24939c04640e310d010a035c151540434038c08e383800773c9e4ee793cbfbeee793c9fad773c9e4d7d504a0120041008e78040f104b61e229110c40ec0288a818862071810030021480806c81230a40000600e30297d1cbe365ee92f5e97ab4bc0a5d612e86972e4b8c25c0f2ddf96dbcb63e5aaf2d1b9679cb2fe592d2c679628cafc255c92a91951d4a84652f529539495ca45651dd28c794504a1da509f27ec93d749e1e4e87271a9370c9a9a4cd726429305497024ab524fb9261c91f248ad240791e748e2a468322da914b4896e444521e990d84861a42bd21359076482ba40dd2045900e480523fcf1fba8fa747ba23d391e818f0fc778a3b771d788eb0474a639df1c988e244701e374b1b9d8dcac6dbe36b31ae58d5f46a9234fd1a688d1ac6806339319948cacc64c231ab17ec8bc645c962d7116488af44561e2a61149e8a3344c66258b12518901c456621c710968802c3e8a1e7d0f16876b43a7a1cef0e2d8703436ca1af50d64869ec345a19df0cb78645431d218570bf985f042eb2172d0b70858a42b1a15170a638526c289a13df09d984e1c26761309096e84a44248a11f908d68457c229e1101085a8409c1fb60f87079c83c341d7e0e730723837e41b9a0d7706958322417e60be305e982e1c16b60b0f057182a5414d20a3704f5826fc132608eb044f8214c100e07bb03a281c540dca06930323817e40b5a057d02948129c087203c901ba80c1c052e01fb00d6804d401c6008f002f800bbfffdffaeffb17fbe3fd99fea0ff1b7f793fb25fd60fe977f373f959fc56fe057eefbf689faf8fd557e97bf41df9e2fcbf7e4cbf155f85efc097df9bef35f6f6fb557d97bec25f5e6fadd7d63beac5f516fa727d263e899f400f9d57cd73e61df2c2f9277c76be2d9f120f87a7c2a3e131f06cf8207c053dfd1ef9cf7b87bc93ddf1eeaaf72f7b84bdb8ded7af6977b37bd965ec64f5f57ada3d635eaeef5517a9dbd495ea1ef4f97a693d2b1e90af45e7a243d085e816f3e479debce59e700f35a79a93cd29e642f2f8796fbcb19e4eef26f79283c8e9e428f1ee78eb3c6c1e)) else (if i < 16 then 0x41007202b540b043c00c04d4154040220140104027303c2043e0219031881ba12040a17007188620401910a508620680204065c0703e8090867c01024219f00408842e036814e00fc00053803f00011c028f802603818bb086600401e20c203c6180ae501a0867c129028104053930866e0301e20d101204bb808c07824028980e04980f029c110281ec10c814000a802ce08813825010c9c0607000278081c602e038080210cc0a70140b80240801d9c20071c10b8c07a6708600821881c70802a0080138400e30203e80640401390c83e3c050013c0300088083040818813007d0100880300200ce03c008043211e0098008810403ec1108da00402801006000138400e302580200100b6038c0e0020dd82189c20071c1b708d8e0382405040100800ac0b6038e0800ac0b6038e0800f30150e10038e0c0173030ce10038e0c00f3030ce10038e0c00f310c4e10038e0e1c1002a01001cc80a870801c706041d802a1c20071c1c0270440c0402704409c236380e09380a040006816360581c606000180f0071813412801460812001802c8400900404080e30301909c325011e1004b60d88610200a00902802008e910f1da10100e311e84318400401005015021a023030c03e02015005030cc07023808040540140540868090150e0902401005030cc0702382004e08012c2362090e1003380805c012065011e030200015805015140a0200006f7cc07026a0a02780a0601301e06000208da06000000236019404780c08b800480880201fa0602800afb77b601b4062218980f80242a80802000e4018f041140a90100e38410c40510c50190200081710c40e382008000802e131010416038e0c471bc102014100403661000000086f00410c609c07010024009a035c080200086010004021c010c04218808010540370100ac04f4012e02035701011c04809f701015c0402809e7010132816040c2170181cf04708808432028432e0381600403ec0e3023a8319c0600c846d0610c808a1b0064236823051582a11b020406708d8e03824236380c08003329d702c10403fa0e0001788f4701c100211b1c0604056d846c082410e2081409888800438400d903404f3808080e701404f382008006086206b8147017c000402780a013ca05022013c09a022013c0a9022013c09a02039c04a700043201f025006c0007c04b0132015043182460381860500a860381402a180e0436108005578400ee03829a000c30408085888c800a904640872c0840015620609f011904402780a204b013ca058240080806b811a009004a8140d703804f2814090821881ae040000a802380e302228144310200e3153004317840a0c035c100296522009f00d7820155003c40d70201849083c218bc0201981ce0814cf63b3001ec073940a06bc222a0002a81c604255b0 else (if i < 17 then 0x18402025a07581ac05a286a098a21285c091410047010400039812a50301d707400de074814014944e049f01868181c1004d021604c0060047019c02a1434028819c061e06004d018e015303002680d37030d030301c05104850a806004943450a814142807d013450d1c1202a01b210b0401300f407581a006805a02380900c00610c40e783407300ca04807a00981201d002604800c008e02900406401015b0080a204900091401e804d600da00813406d600da00813407908718030134065ba00813401a819a401b40102680cb740101440350341019205f012881400f022d20301e20b60301c80c066406081012980c40f02a2037004090919c0102a20370040b406fc406e0081cd80c10202c838066406207812d80cc0102480c06012030102c405c486720304080d480e0648f72030280041006c80d60302c80c0560415c80c10203720330040ac80c4030272033004092e9fddf3edbde6ee01a1217c01091827c08da19046ca078178020301012a0e02600a109c01a0259020301680e903600dc02781200d006f028813007d0135b80acd01f80307a6410027c168c82008e82d0056c82004f03d02407409014081b01c0ba6c081d026a0383d01c04ed01c0c38258089a04c12c044d02609d0260481a9028187a04810fa04808904b409030c0a020039604080ac04041da03c08812030000b282340782681c022400520681c10320480c812028891030089a0381402d01c0c3028044d01c08000200c3407028030d01c09a061ac13046e80ed01822a06d030d6098280805a038110c404431018040308110c406c070158187304d40a072813501012d01c12002750140c0009e02809ed0181204720600402780809e03501809f409280e09d01ca03024246d01c09d01ca03029409a80c09d01ea03026a03816a03814246d01c08886303a0113407280c0d013ea06024e0081620591034e0081620680a3e00813603a40604a40400340804a018816203681060801e0920134070540402d01a006805a02401d00b4055404a0081081202408ed02c09407019a00909404a0380a403e80205a0080e8080501ea0303d02804e1407a0081e00604700a04b0802048233a0081208ce80204811da00812d004119028503011c050015a00812d00403f024f9004084826401816401814d01811e0420d80ac064680a0a02020140a08023851998d80a021881a9067501ea0282850101d604f401812036c0980db02d40502012047109404a80f5018100f002e803031407a0081101e205a80e05d00605680201f814811c04201011c029a030238080007801402b600805010301ae0480a8003012061e00c048187803012061e00c0480a9803012c018054024818050862043012d02c080ac0390159a028201580480a002081220d880e047026320690100c431010 else 0x73011e03c40d478400d2053b084307b3ec763c24f08023290981c10a8433d9809e08241210cc7f9809e078c12809406a023204210e3f61ec7d8d8608c81cef07140a90981a70c1481bd9e9098233048700cbc047921378380e7034c144865b303f010182120dd86cce01b484c0ee8375227f36f7b776cdbc12f0181ce06940630ae1087c78ec0465e0e039d213034e1603101004c00620718101500b01c60500b00d00b40c02c034109810711016036609202d102806ca062071819a02ba01027c0d20380c40580c5016020985c06ca42701882320901880c202d018814062025018c0c062020982c06206cc12009c05f0241e0902ec09847825e0302f80d1c1002e81137030c05f584804a04a017403002842700680a2810074813304281004805602380a780de0102406f80ea04700e6f009814070c0903e80ab80ee0202680df08a005a03c8088114180e06c09c0970040ac033984800075605c0fa04b810e53c0407d0130070c0203e80ae0301503e805a02c2120200b80e9037c0d01be02d013203e809802b80c06e03013026003f02804400880875c07026007b03026004098018f018130051e03026009181202f81340705c0402d019780805802a017c03002583c062410073014280e60f0285014c1a04080078258053c06f00812038005f024f0100bc0470068a0982b8040501c002d012224140a04b2012001504500e003400d00b404204809ee03280e08f701140504d022444800a40c10d01825804007e79f0138602f80bc90f340cd0281c10c80530280e0019409487a05038121e0268890014c120700052055c07700815c0202c804009003c0f4039304909005200b4074812037c05a02406f80b4046047044205440cf00816406fbc0202a018041c03904660a03e80e9025a042202d01d20638061e0080f6065902c003804b038c0c5184002003c0ab0303240503240290240540f903bc09a038005401440d900801200781e8068c240961204540df037004046408012c0781e806372402984260903800d50418988320984a61004b40c43801192001c005007a0184908d80101340ac03118485309022a06f8188700212406c00805007a01ac092098240e061f00d01d202d011640b000700960718192118003809a07581a013005d02404280ba04a608012c0b4008cc06c0081a003421c0129805401025b00880205250040fa025b00880204806800981206f805404e0068009942206806800981380d602604501a018409602606f81201a002604803401bc09143421c0120005048212047888e0010602f80ba53e025b08947a50a012018142804943450a01450a14220407d00e207d0131a0581b01f404c014409a03e809c03a4a1480fc0c1800a03049008f111c000602f806053e025b08a0380120024a3d28540928e8a1402088110))) else (if i < 21 then (if i < 19 then 0x2d81158074038009103803a98180a804016804580c0a581a8040262b0805002401f81b206d0035d80c0930330c088003b906209301d0080206c80d4022c06047a01160382036405a06cd06305a4c1006cc1206cc0ac024c060501f39e418021005c00a2c1c00081c606983116e071b00801880be0822004e08681337704101434c2008c30140698210140202320408c80f4020210c9818f40207381e002031c058008174020206c80994000138480d7035a07001027f031035907001027f031031641c00409603800d642c00409fc0c40c310e00281881d8071c11800816002031c11800814701e00205d0080c701e00205800809641800f40206981e00202b001034809c01d1c0d80081c701600204b20c007a01034c0d41d0081a6041140c40ab028814064816804028205a004090816040207606208cc1023c0205840a1340c4119030004113821408cc140270140a08f01c60407880a06c81a8040103b0310466080207206208cc10040ec0c4119820401d8188233040021f03104660802c20509a06208c81a70440a02e03009c11029c07020130ec0c411982008c3b0310466081007606208cc1400040ec0c41198200984701c6509a06208c8240620301880c062029c070214002401ce0408f0081610509a06208c81c01034a0601380e05381a05380a0602036605380e05405ee03026701c0f9c0e3b80e0881c7029c070202140c4119020401d8188233040b08284d03104640c4301181c6018823206881b80c408f037020b8088071806208b424818a00805206280201300b400804c02d0020136016801209a40c5004206c0e40c50040259031b80c0c2034f81b280b200970182081b2818811405806d02b00000cc0d70227018810804982480450740204901ce0701880c062029018c0c06202880b4062044c0d9780e031037001812042408803b014400103820c201d813580081c106100ec09ac0040e0830103b009f80081c106208c811604080ec09ac0040e083011cc009f80081c106407a81700181204240901ea060011e010000780c040080f102604e40901e2060072814084823940b800c1101e2053381806d82a81404810902e00302f001814f00102c60880f102a037701812199be0218c0740c60d79c11800c1180f102100ec086c0040e083038c05013ee0202850281ae048e020238096502e00304408601e0096002708814140a06b814382008e025809e502c1160013406b8114086023008450281ec0401e5cc54c000c601b784006d035c14022b3c88141805881af06026b003c40d70202e628c100dbc2003681ae082103f673e78095023c06a3c2490981a50c4802f3861e08780c06d046610480cd9b6ed00da42609541960090480507a04640d025b7809202470470965b365e0150188215060212c41e0304900d70301e2 else (if i < 20 then 0xa14120178122000c00bc0e382800406181c604d0278063820633927b19b7083613c84dc071c240200c030039609a181cc03b01c7047c302b00ec00c01c70638cf8f618fd850c06980ec13700c000b01c70c6063b00bc0e38219f1ec3847ec0c06980ec137003000b01c70c67056084c09e022c0e304015404810c02a8107021805582408600bc09aa025c0505005fa03812d01c0c30253034c086827443015c05508d806004d0057a82103103708d015c26e01820ca0630281880ba0340a11b680c0431e00050c04c8060071c1aec07f8020843101760c1240450100d783100c00bc119820e04c04300a008cc19c0758186071c10216020e0131801009a04660e00ae01881198180310200c404031011c61056604f0062071c18e0411813200b01a706c060814060815a02816a809701c120278082054808f0101480802688240403c40d70317603a063046a0540c409901820602a406a814096b80d031829838046f00a170180a907a0141c07822014008b0230520085004d024d04be021aa0550120c20142022c1190240d9813818450441204340a0283c040470309c078200074c06c820904823f03021611b010203c163e04100d9038e0d03f44190203b806701e04341410410116024108a4030c0fb023cec533a935573b3affea92aafd409bf9e7c09d9ce0126045810b03b80fd03d81200366210dbc050036609a70218057b80903104c01d4043013edc04f010d50428090900d381ae04d41016473018409001af06b038e04e027d410a0201f6204d011604341a81160430125f6ddedb7ed818604f206c11b013404343211b680c04608140806202016204d0233042c1c388018d40a06bc18e10a010c06cc1210bf80205e0080f80202421701b40810022187f01bc0122140e30401b4059205ba0100a40d411800540a2038819a04809c009814c0402a04600920264816e8040290319cc104f0a000ad6125840038045414b6f66e01600e002b83410010048009c79c10461413094c20c05022b080a00200900178738208c282612984180a04561044400401200210ef38218504c25308301408ac2022008024005e19cc102140015cc25308301408a828a08013821a0450ef38208c0984a6106028115840920d80600a00ad0303bce0811854c25308101408ac22004005d029820051304012204810a0098140094c1005002330181600802e0087010110000e82320440600808c8110180202320440600808c81040600808c81040200808c81470460080580200c704600804e008701811038c0e1021c11ea80b0310350460029022c8460809403d01b206400000c0798111320100e0024c0c80000481f604f1cd00140213002c119844e5e0c0800b560e0004118034c150007408f020478046fe204280fd3094c1c405022a0a400804046409001c0 else 0x76cb7e90280f18269f60853c23600c19816021558026e035c0809bdbb7a666fcddb37c028009f7095c1ca0518170cbc3cf7de5cef2e777794ffafe839ce794b5faaec0b242047c10a03d80045028126039c0e3887d9c13e00c16980c6036c139c0502402b00c004a07d9c0c04580ac7034112fb80e0459c0d064c079bf3e73000f6039c09a0140004035e19e7243000bde097805e11038c15cb6031b80e045c1edc086782608bb03d8063022e0f866dd18b01f72050209069af80e7022c06383e199a316015a40a03c60f6e0853c2305a802b04f2028019439e66e01400fb68140d984380c602b41380e025550026e035c09779bedda86666fe1bf00a0027bc1320200ec07538170ea7be5769d77e9ddd54ffafebb0e73979e1ef3cf085920047c10a03d80049028126039c0e388902da0640a981d0056682004f03404fb80c095c06047012816e704813fbffcdab32ecfddbe04d00ae028009e022281401f81d311e4056f006088feb7b6eed66bf6f8134028009f704dc0607828150ee0815805700580e38337f0040578217d7502822a02bc1be1c7ec21e3fb000d309b8057005ae0ea8140e3873c3107300c0071c10f87193f61e160c1370427502b80207e01c70c3c06399c0c071c10ce3ec21e3f6001a6137002c707540a071c31bc09e022c06383f8d7780ae02b180fe009c230af96d80c7603b80307ffa03080868279b018c056b01e0cc06b80c605be00c0eb770301af05b70218e06827cce06023a0bc80ade00c167c0f6b83a09aed81ed707380306bb03d8056383a0dadc056380fc0183dfa039c063827d9c0de00c132dbe039dc01018e0d35f01ce04580c706d6e02b1c07e00c1d018e07580c6e00c139c0d027018c05682d4015c26e013c0f48137011d05a8137009f05d630278e12023a0c51dde61809e079d410072c23b3827c01826f630278e12023a0decc0f33827c0183c81d702d436db6edf6d8185504281506f6604f1c13e00c1838463011f035e09bad813c043541106d8db6db6f6fa061281550441fbb2817c018273c09e035e09ed8d941050281af06f6604f1411e00c19027a07866646d813c02780f5066fe009c2305501ea05fd9c23e00c11fbf802708c101edd97e13c80f504407dc0f0db35f3201f613c80f506b6e05b1c07e00c1efc01812013ec07021009e605811009f603812ec06180308004035e0dc80c2018c04f0326490140009a039e084ca4900002680e7820c924028009a039e0948080068152022008050015a0081081bce72337e08201e320581c7083528280807881ae0600cdc06a054140056802050a0602380a281b401029504811c0480eb812dc04fa82140a830590075822c06b819035e0481af031411a008100f402e80302e80302e8030288030026408920611c80112f80206981c608400000404640)) else (if i < 23 then (if i < 22 then 0x181d60640002f04640820000b02320400b00a008cc100731014004f04660d201340102406300a8092c1203a8132c1e60501450180e9026606501808a17c0e381e8c0a8347026a07a70100d901a6a0081e2063211c09703c0ed031d780206981e20608891001800b01e206b8185907024c0f03b40d2604d012a07481a81e203181100b010119020816020232045e02018c08119015006004c811f8f8f0388184017d2154852c0b00c00e386406980be044804b000803e01ca0680d30168091120a0502222401a60480c6204813086825a0302fc0cf39200c017d21903c412d841501101a608c813204002400f03b40d01be02d012037c05a022f00822a05440af008104c4200c811209406b81962a03822a04a81840060025520503f40c11901a20678040a8819e01020407180056440c06bc18232025902c003804b038c0c80001c0e3023807e011c05303406300a808d808b08812204c0aa0208901b20440000903ec086f027808b20c60ef80302c810009003c0ed03cb2010b0901be06981a01a002605002900c008800bc0c3025004b0040a2060101500411901a2067004082810c2c06300580600321012005902046406005400e02648321004801f00e303200000808c81480d601d01240c0290300d00802d008b01814903580205040d6008136022c0604801c00b00a208001c028205d80409200122803b40a282740102403412086811c023805504901140a502018c0480c702e4126018110001808039c0a341002d011700581e029c0181a82005320903940887038cc0a82c824060103972090290269c0402c820071011c078c10134030195032a0801680a9825c0402409a70100880002201ce05000040580ca035e08704006501af053209039409b00605c824c06026e80ad018cc0101f410bc0103c40881af03a500f1035e0b208011c09a300406303204d01ae04756018c0d703c60d80d7026808b409a013e099d0268086018e0f204d00fb05009a818104011c04409a035c0881af025807ec82009e036e0240bc3620903c40d783807018604d410ee0200c704381af0300e061c08244f930c0f6047c0d7837700605402180d9025ae79b7f77eff6f5b3edffb6bfedb030c09a0918236f00fc01411883603a80d78a381ede00c1680288815801039205a01009341003d016c060205d00d504380205048ce00812fee7ae7b8bf6defbd87358611f027c0103f40df09182368723041360330280d2080168200602012080168200602024822c010201e805b00605b0060608dac01022c03a640604e81ae00c0ac07970060a085fc010280805c0181d020810bf80206c900008803d81ae078000fa06b811e0100c2026780410c60930814431828a09d0100b4a03f00904082c03280d7825a08d0100b7c01810e79930a40a3805e1278380e30542 else 0x201481745118154120280e9019409a704d40ad028194040350100c508b404044a1181d02006d020a0302807dd0200a01f740802807dd0200a140602781002d020068029408a80808c0040904340c08c81ba023404043e802508c12085405f0201dc0501a603281203bb40a04d0100a086405f0201dc050341207a01203bb40a04c906142004801f00e303130380015003b81c6070101040bb0081240a02889010281240a032205503408032014218c0c102e80804a038080ac0223801841e81205881c7070812d02815204b40404e80ed02813a03b40405d60112c07a81a0d680a05680a04fa03940b05340dd01812e80e807027a03680809281604be80d2098206c03180162073812ea068011c01035aa068011033031da06b03609a603b40c0020196c03480800681af76d03640a8027803087c010128087d681b205d0360db902f803043e802508c12d0140ba00c0a502c0a006004c81210cf802040020f0040e302015c07406012000240c071811f407681608fa03b40504da05816d0140ae4062816092816040b40c05e812088444a0481f400a810c16825a0603380d038121e024d0600b40480bc5028144c0c43c011412020401410080812521942804c004141250301c806949250a01201814280450480a5219428041108801840201e206b81c50a141805142850601202480260520080a81003a0200e81002e810502812021a062827401025249485009490d2140240d04821205260820e009141802d014902dc020424480247406b8126a80e04aa4740620001205031c0a485120c02b010064816c040200901c0720c01c8140520601920cc81409206015606c8140b2050159028120051811902815902d80805240d60081400a001804806000a01500de91b0101e2028049016808244801d0601ae043210038009c101034018812a0560080c902d8020520300e40403d0100e404029609029009c808c01029106014805320203bc0b20201460081480407780a02540f102460201e2048c0602900a409018030d01c0a02016a04d40b047d01ea05827502c0ba81604101c78607881de07641800cc0ec810894050895c0702a4046004094012068011c0102a004700409b00e059011004029004b00409026b004024c004b03e097002780305540aa00816802031413a0081404503680204d40b0200e80c00201680e03008117502817c08c791c980a011b206207881d50a00483004800a00ed031001201280204b80c12c02470300b605083870301005e02c95848099020c0d6034809802212406200140df03ec0d00630168088703c640a50280d00d0013025034c05a0230002824101023e31c08f030802f80b7701020841001c60d0a1400c00a2850a110256063018088134031810ac00b80c044035c0c2003004f011011903c010058a05c137) else (if i < 24 then 0x6068c60308382ca4503a60b402d148b0423c0efc0f88584c05d016ca152808a4603a61a2826a0781500ba018012c1a030a03983c0a240c06e011032a06d02a40ca81b40a240c06e010183888080175215034c1180469d03280a449160d00fa052011190800100f407681aa4310238084009602501c7044b015d43102380d2c043286204c81d006a20e009a038120201680f9a2827a02b8040510404280618390044071211039410300800e5816902f40407a823491b740404a8191480c00401380d903403000a4092cb80c2d01016a91b0232034c07d02900c8c84000807a03b40d658042c2042481a606043d88c003a020396285035c102464600807a03b40cd241801e206b8196023803003c40cb00fa923014806380c3a0c00f1032000600a408805702180a206b814804260801408503c0ed03184008740a04040c02c7019c0104240ca047486205490c740a0280c581e2072c17acc072816082e3c202114f009c01010f038e10b9e400693c02700403cc0e3841c1022f00403c40e58308117022e790049e01380201e6071c2024038c0f3038e09014808c012c800004015c0e303408b811407007981c704062038230079c1000f83272c0e549180ef833016085082b03940ec820e0802581de071c10e4080f26052241207281c7090100818710481009e023e0803a79c48ce05d40a05201c70a4086015c09ce08819209b01c0804f01008e05201cb04011604f01e3040809607981c704007203940f1826f180e502fc0107a301ca05820591000121480804701c6067aedb7db7adfdbff6e7ed9bfc0c2022e04680c5e03091843103c40d78923920182780de0104800e5042548b800c8909181621881c608f1724181e037809e0103c40d70577992b5981b328154040924434843650c90600e5e06043c0e38323940182048cf008240071821814e00139e0e302c0f3830847b3ce71f0c45407808434783c0e5039e151404843403c408e5c67073babe7eddc7af3d7bb8a96b5aee354ad7aa70b0b7f9fcc09402402181816082281407881af1084132e28825421881fd0621227419781d840ba02c21881d60a6120702f040250075c1bf663c2e4fb161360c06028bc1c603940a09001af0c36f24092500070116f03021e071c202e45807838120035e0c50f878fe00e18052048cf01bc0250601c70c1479c7601e0e039cc07035e1062c316e2c43078380f1035e0ca404501c091130008039038c08b6838e09017c0d3c0203481093064046c09381d2069a0e016c0818e15a086809a0602b810b017d61208480f20201410a80be04821e017c093c0402f011602db41c5070180da06032c09a11012c8160007009607181904003b8232044a1181200001f40f40203a40503a4a1502050e0302820a0628080e40408404c0281884a03880c40000140a07 else 0x604d04b40c07201ac0c02623681981806002191c06000eae1003b41031470181e0200e00a70411e0802d008401840b40204b80811102a00d4072015014c707813024402d81500b60180132b042c0cb06819c4033808a06b81b4c1aa008101001442080811de03380e08e5948c06bc15c0402204e0620017405b29180fa0407bedfdfb29bb73ffb7f959bedec34c26c0ad0284a4550c00a80257e03021006d8918421c0000d0f0801db)))))
def level10 : Packing := (1669,5,9,0,0,17,1,nd10)
def nd11 (i : Nat) : Nat := (if i < 23 then (if i < 11 then (if i < 5 then (if i < 2 then (if i < 1 then 0x120087ffd51e4010effaa3c8021fff52790043ffea0f20087ffd51a4010effaa348021fff52690043ffea0d20087ffd39a4010fffaa2c8021dff54590043ffea4b20087ffd4164010fff882c8021fff4e590043ffe98b20087fdd2924010ffda51c8021fff52290043ffea0520087ffd30a4010ffea6148021fff4a290043ffea4320087ffd4064010fffa70c8021ffe4e190043ffe94320087fdd2064010e7fea4c4021bffd6888043bffa9110087bff4a22010dffeb344021dffd4688043dffa4d10086fff5962010effea2c4021effd2588043bffa8710087fef28e2010ffee8144021ffdcc288043ffb94510087ffd4022010fffa6044021fff4a088043bfead5100877fd5262010dffab444021dff54888043ffea5110087ffc4a22010effaa344021fff52688043ffea0d100877fd5162010fffa92c4021fff12588043ffea0b10087ffc4162010fffa62c4021bff56488043ffea4910087fdc4922010fffa8244021fff4c488043ffe949100877fd50e2010fffa81c4021fff4a388043ff694710087fed20e2010ffea8144021ffd4c288043ffa94510087ff520a2010fffa90c4021eff52188043ffea0310087ffd2862010ffda30c4021efdd6988043dfba9310087ff75222010f7ee9444021ffdd4788043dfba4f10087ff741e2010dfeeb344021ffdd4688043dfba4d10087ff741a2010ffee7344021ffdd4588043bfba8b10087bf74962010ffee82c4021ffdd4388043ffba0710087ff738e2010ffee61c4021ffdca388043ff394710087bf74862010ffee80c4021ffcce188043ffb8c310087ff31862010ffce30c4021ffd50088043ffa9c110087ff53022010ffea5044021ffd16a88043ffa2d310087ff55262010ffe8a4c4021ffd56888043ffa2d110087ff55222010ffe8a444021ffd52888043ffa25110087ff559e2010ffeaa3c4021ffd52788043dfaa4f10087ff541e2010ffeab344021ffd54688043ffaa4d10087ff541a2010ffea7344021ffd56588043ffa2cb10087ff55162010efeaa2c4021ffd14588043ffaa4b10087ff44962010ffea82c4021ffd10588043ffa9cb10087ff53162010ffeab244021ffd54488043ffaa4910087fd44922010ffea8244021ffd4e488043ffa98910087ff52922010ffeab1c4021ffd54388043ffaa0710087ff538e2010ffea61c4021ffd4a388043ff294710087fe520e2010ffeab0c4021ffd52188043dfaa4310087ff54062010ffea70c4021ffc4e188043ffa94310087ff52062010ffea30c4021ffc46188043ff28c310087fe11862010e7fea4c2021bffd6884043bffa9108087bff4a21010dffeb3c2021dffd47840437ffacb080877ff5161010f7fe92c2021dffd4384043ff794708087ffb3861010fff650c2021ffec6184043ff58c308087ffd4021010ffea2042021 else 0xfff690ca121efed2194243ffda0328487ffb3865090fff8b04a121affd69902439ffa93204877ff5224090f7fe9448121dffd4790243dffa4f204877ff5164090f7fe92c8121efed2190243ffd9c320486bff5a6a010effea454021effd28a8043bffa8f500877ff51aa010f7fe9354021dffd45a8043dffa4b50086fff58ea010effea1d4021ffdcc2a8043ffd9c3500873ff5a6a010c7feb4d4021cffd28a80439ffa4f500877ff41ea010e7fe9354021dffd06a8043bff9cd500873ff496a010cffeb1d4021cffd22a8043bffa05500877ff30aa010effe5154021cffd21a8043bffa0350086fff5aa8010cffeb5500219ff96aa0043dffa93400873ff5268010effea450021effd28a0043bffa8f40087bff49e8010effea350021dffd45a0043dffa4b400877ff50e8010f7fe9150021ffdcc2a0043dffa4340087dff4068010fff670d0021fff540a0043bfea8140087ffd5aa8010effab550021fff16aa0043bfe2d540087ffc5a68010fffaa4d0021dff549a0043ffe29340087ffd5228010effaa450021fff567a0043ffea8f400877fd51e8010fffa93d0021fff507a0043ffeacd40087ffd51a8010effaa350021fff526a0043ffe9cd40087ffd5968010fff8b2d0021fff545a0043bfea8b40087ffc5168010fffa92d0021eff525a0043ffe24b40087ffd3968010fffa62d0021fff564a0043ffea8940087ffd4928010ffb89250021fff504a0043efea0940087ffd3928010fffa6250021fff4a4a0043ffeac740087ffd50e8010effaa1d0021fff4a3a0043ff694740087ffd58a8010fffa9150021fff502a0043ffe98540087ff530a8010fffa5150021fff482a0043ffeac340087ffd4868010fffa80d0021f7f501a0043ffe9c340087ff93868010fffa50d0021fff481a00437ffad5380867ff5aa7010e7fea4ce021bffd689c043bffa9138087bff4a27010effea34e021effd269c043bffa8b38087bff4967010fdfe72ce021dffd439c043ff794738087ff730a7010fdfe70ce021fbece19c043ffea0138086fff5aa6010cffeb54c021cffd49980437ffad1300877ff5226010f7fe944c021bffd6798043bffa8f30087bff49e6010effea2cc021effd2598043fbf98b300877ff50e6010fefe61cc021ffbca398043dffa4530087ffb3866010fffaa04c021dff54098043ffea0130087ffd3826010dffeb54a0219ffd6a940435ffad328087bff5265010e7fea4ca021bffd6894043bffa9128087bff4a25010dffeb3ca021dffd47940437ffacd280877ff51a5010f7fe934a021dffd4594043dffa4b28086fff58e5010effea1ca021ffbca394043dffa4528087ff730a5010f7fe90ca021ffece194043fdf94328087ffd4025010fffa704a021fff54990043bfea9320086ffd5a24010fffaa448021dff54890043ffea5) else (if i < 3 then 0x9a0a439ffa93414873fe5268290dffeb5105219ffd6a20a437ffad241486bff5a48290f7fea490521cffd4920a439ff29241486f7f5988290dfbeb210521bffd6120a437fdac241486fff5808290dffab010521bffd6a9ca433ffad539486fff5a67290f7fea4ce521cffd499ca43bffa9139487bff4a27290effea34e521effd269ca437ffad5314867ff5aa6290cffcb54c521bffd6998a435ff2d331487bff5266290e7fea4cc521bffd6898a43bffa9131487bff4a26290dffeb3cc521dffd4798a43fbfa0d31487f7f39a6290effea2cc521effd2598a435ff2d3510873ff526a210effea354421effd26a8843bffa8b51087bff496a210f7fea4d2421cffd49a4843bffa8d49087bff49a9210effea2d2421effd25a48435ffad549087bff51a9210e7fea352421effce6a4843dffa8b490873ff5169210f7fe82d2421eff905a4843dff9cb49087bff3169210f7bea492421df7d49248439efa9249087bde5249210ffbea312421df7d4624843fefa4c49087bdf4989210ffbe7312421ff7d4524843befa8a49087fdf4949210f7be9292421ef792524843fefa0a49087fde4149210ffbe7292421ff7cc5248439ffa93310877ff5226210f7fe944c421dffd4798843dffa4f310877ff5166210f7fe92cc421affd69948435ff2d329087bff5265210e7fea4ca421dffd4894843dffa51290877ff51e5210effea34a421effd2694843bffa8b29087bff4965210f77e92ca421dffd48a4243dffa5148487bfe4a29090effea3d2121effd27a4243bffa8b48487bff4969090f7fc92d2121effd24a4243def24948487bff48a9090e7feb552121cff96aa4243dff2d1484873ff5229090e7fea3d2121effd07a4243dff2cb484873ff5169090f7fe82d2121eff905a4243dff9cb48487bde5929090f7fe8252121effce4a4243dff94948486fff5a68090d7feb4d0121dffd49a0243bffa9140487bff4a28090effea3d0121effd27a0243bffa8b40487bff4928090ffbc9250121bffd699c2439ffa9338486fff5a27090effea44e121effd289c243f7fa0f384877ff5167090f7fe92ce121effd249c243fef24938487ffb4867090f7f690ce121ffed019c243ffda9338487bfb5267090fff6a44e121ffed289c243dfda5138487ffa4a27090fdf683ce121ffed269c243dfda4d38487ffb41a7090fdf6734e121ffed459c243bfda8b38487ffb4967090f7f692ce121ffed059c243ffd98b38487ffb5127090fff6924e121efed249c243fed24938487ffb4127090fff6624e121ffeca49c243ff9985384867ff5aa5090dffeb4ca121affd69942435ff2d3284873ff5265090dffeb44a121dffd4894243dffa5128486fff59e5090effea3ca121dffd4594243dffa4b28487bff4925090ffbc924a121bffd6294243dffa4528487fbf28a5090 else (if i < 4 then 0x7feb40630a0ffd670c6141ffaca18c283ff5ad118507fea5a230a0ffd6b3c6141ffad078c283ff5acd18507beb49a30a0ffd68346141fface68c283ff5acb18507fea59630a0ffd482c6141fface58c283ff598b18507feb58a30a0ffd4b146141efad228c283ff5a0518507fea40a30a0ffd67146141ffacc28c283ff594518507fea28a30a0eff8b550041cff149a0083ffea0f40107ffd39a8020f7fa92d0041fff4e5a0083ffe98b401077ed50e8020ffda51d0041fff502a0083ffe9c540107ffd30a8020fffa5150041fff501a0083efea0340107fed1868020ffd230d0041ff750790083feea0d20107fdd39a4020ffb882c8041ff74e590083fee98b20107fcd28e4020ffba8148041ff710290083fee9c520107fdd30a4020ffba5148041ff70a290083feea0320107fdd3864020ffba50c8041ff346190083fe48c3201077fc5aa2020dffab444041eff52788083ffea0f10107ffd41a2020fffa7344041fff4e588083ffe98b101077ed50e2020ffda51c4041ffd4a288083dfea4310107bf94862020fffa80c4041ffb46188083ff48c310107bfe596a490f7bcb254921df7964a92439ffacd524873ff596a490e7fcb2d4921cffd64a92439ef2c9524873ff524a490dffeb2949218ffd6529243bffa93518873ff526a310dffeb5526219ffd6aa4c433ff2d549887bff5269310e7fea4d2621dffd47a4c43dffa4f49887fde5929310e7fea3d26219ffd6a9cc437ffad3398877ff5267310e7fea4ce621aff969a8a43bffa93514873ff526a290effca4d4521dffd48a8a43f7f2cf514877ff51ea290effea354521effd26a8a43ffe2c1514877ff5a6a290e7feb4d4521dff969a8a439ff2d3514877ff5a2a290effcb454521dffd67a8a43b7f2cf514877ff49ea290effeb354521dffd26a8a439ffa4d514877ff39aa290effeb254521dffd63a8a43bffac1514877fc582a290dffeb494521affd6928a439ffa9251486fff5a0a290effea414521bfbd6328a437ffad5494867ff5aa9290cffcb552521effd49a4a439ffa9349487bfe5269290effea452521effd28a4a43bffa8f49487bff49e9290effea352521effd26a4a43bffa8b49487fde5929290f7feb552521cffd6aa4a435ffad5494863ff5aa9290f7fcb552521cff96aa4a43dffad149487bfe5a29290f7fea452521cffd48a4a43dff29149487bff59e9290f7fea3d2521cffd47a4a43dffacd49487bff51a9290e7fea352521effce6a4a43dffa8b494873ff5169290f7feb252521ef7964a4a43dffac549487bff5869290dffeb5125219ffd6a24a43dffa92494873ff5249290dffeb412521dffd4824a43dffa5049486fff5989290effea312521effd2624a437ffac449486fff5849290dff6b092521bffd6aa0a433ffad5414867fe5aa8290f7fea4d0521dffd4 else 0x1c2051ffaca3840a3ffda8508147bfb48a1028fff68142051ffe902840a3ffd9c508147ffb30a1028fff63142051ffe500840a3ffc98108147ff91021028c7feb4149418ffd65292831ffac4525073fe5aa9420e7fcb552741affd69a0e839ffa9341d073fe52683a0f7fe9450741cffd49a0c83dffa4f419073ff5267320dffeb44e641effd289cc83f7fa0f399073fe5aa92a0f7fe83d2541effd06a4a83dff9cd49506bff5a482a0e7fea490541cff94920a8377face41506f7f59882a0dfdeb190541bffd6220a837fbac441506ffb58482a0dffab010541affd699ca839ffa93395073fe52672a0f7fe944e541fbfd079ca83dffa4d395073ff52662a0f7fe944c541bffd6798a83dffa4f31507f7f41a62a0fefe734c541effd2598a83bf7a0f50d077ef41aa1a0efde7354341dfb905a8683bf79cb50d077ef316a1a0efdcb54a341ffbd6894683df7a5128d07fef59e51a0f7de93ca341ffbd0794683ff7acd28d07fef41a51a0ffde734a341ffbcc594683ff7ac528d07fef58651a0e7fcb552241effd07a4483dffa0d48907bff39a9120f7fe72d2241effcc5a44835ffad3409073ff5268120e7fca4d0241effd28a0483dffa4f40907dff41e8120f7fe92d0241dfbd43a0483ff794740906bff5a48120e7fea490241cff949204837ffaca40907bff4948120efdea190241ffbca3204837ffac240906ffd5808120d7feb4ce241cffd499c4839ff29338906fff5a27120f7fe944e241effd269c483dffa4b389077ef50e7120ffde51ce241cffd49984837ffad130907bff4a26120dffeb3cc241effd2798483fbf9cd30907bff4966120fefe62cc241dfbd4398483ff794730907ff740a6120d7feb4ca241cff949944837ffacf28907efe59e5120dffeb34a241effd2694483dffa4b28907fbf3965120efdea1ca241ffbca394483fd794728907ff740a5120ffee714a241affd69144839ffa92289073fe5245120dffeb40a241bffd66144837bfacc28906fef58c5120efdea18a241bff56014483dffa0f48507bff39690a0f7fe8152141efed68a4283dfd2d148507bfb59e90a0f7f683d2141efed66a4283dfda0d48507bfb39a90a0f7f6b2d2141efe965a4283dfd20b48507bfb39690a0f7f662d2141efed62a4283dfd2c548507bfb40a90a0f7f48152141efece2a4283dfd98548507bfa28a90a0d7feb4d0141cffd49a0283dffa5140507bff49e80a0efdea1d0141ffbca3a0283effa0540507bfb48680a0d7feb4ce141cffd499c2837ffad138507eff41e70a0efdea1ce141ffbca39c283f7f9c538507bfb48670a0fff680ce141affd69942839ffa9328506fff59e50a0efdea1ca141fefca294283dfda4328507ffb40650a0fff670ca141ffbd078c2837f7acb18507fef39630a0f7de9146141ffbd028c283ff79451850))) else (if i < 8 then (if i < 6 then 0x3ffda0d38547efb39a70a8ff7662ce151ffed449c2a3dfda4938547fda49270a8fff6624e151ffed439c2a3ff5a8738547ffb40e70a8fff661ce151ffac839c2a3ffda8538547bfb48a70a8fff6814e151fbece29c2a3ffd98538547ffb18a70a8e7fea4c6151bffd688c2a3dffa5118546fff59e30a8effea3c6151effd278c2a3dffa4b18547fef40e30a8ffde71c6151ffbca38c2a3dffa4518547fef18a30a8fff680c6151ffece18c2a3bf7ad5185467ef5aa30a8efdea4c6151ffb9688c2a3ff7251185477ef51e30a8ffde83c6151bfbd658c2a3fe724918547fef39230a8f7de9146151ffbca28c2a3fd794518547feb40630a8ffd670c6151affd69a80a3bffa87501477ef50ea028effea154051ffed01a80a39ffad3501463ff5a6a028e7fe9354051dffce6a80a33ffac7501477ff30ea028e7fe9154051dffd02a80a3bff205501477ff38aa028effe6154051dffc62a80a39ffa43501477ff186a028efde30d4051dff549280a3bfea8c50147ffd398a028dfbab214051fff543280a3ff6a86501477fd50ca028efdaa194051fff4c3280a37feac450146ff5588a028fffaa114051dff542280a3bfe28450147ffd408a028fff88114051fff4e2280a3ffe98450147ffd188a028fffa8094051ffe501280a3ffc9c250147ffd184a028ffda30940519ffd6a980a39ffa933014777f51a6028fe7e62cc051dffd43980a3bf7a8730147f7f30e6028ff7e514c051dff549900a3bfea8d20147ffd39a4028ffbaa248051ffb543900a3bf6a8720147ffd50a4028fffa8148051fff102900a3ffe9c520147ffd30a4028fffa80c8051ffe501900a3ffc9c320147fed1864028cffcb544051affd69880a39ffa93101477ff50e2028efdea1c4051fefca2880a3fdb945101477fd5022028effab544051dff16a880a37fe2d5101467fc5aa2028effaa4c4051bff568880a3ffe2d110147ffd5222028fff89444051dff547880a3ffea0f101477fd51a2028fffa8344051fff4e6880a3fdeacb10147fbd3162028ffb89244051fff4e4880a3ffe98910147ffd50e2028ffdaa1c4051dff543880a3bf6a8710147ffd40e2028fffa71c4051fff4c3880a3ffe94710147fed28e2028ffda41c4051fff542880a3ffaa8510147ffd40a2028fffa6144051fff4a2880a3ffa94510147fbd28a2028ff6a5144051fff462880a3dfea4310147ffd4062028fff280c4051ffe4e1880a3ffe8c310147fed1862028e7fea4c2051dffd43840a3bf7a8708147ffb4061028fff630c2051ffac61840a3dfdad308147bfb5261028dff6b442051ffed48840a3dfda5108146ffb59e1028f7f693c2051ffed07840a3dfda4d08147ffb41a1028fff67342051efed25840a3fdd98b08147ffb50e1028ffd6a1c2051ffed03840a3ffd9c708147ffb30e1028fff65 else (if i < 7 then 0x929128efdea1d2251cffd6aa44a35ffad5489473fe5aa9128c7fcb552251eff968a44a3dffa91489473ff51e9128e7fea352251effce6a44a3def2c948947bff3929128f7fe6252251effd43a44a39ffa8748947bff38e9128f7fe61d2251effd42a44a37ffad4489467ff5a89128e7fea492251bffd68244a3dffa5048946fff5989128effea312251effd26244a37ffaca48946fbf5949128f7bc9212251dfbd43244a37ffac248946ffb5849128dffeb5502519ff96aa04a3dffa93409473ff5268128f7fca4d0251cff949a04a3dffa4940947fde4928128fffab050251bffd6a204a33ffad440946bff5a48128e7fea490251cff949204a3dffa4840947fde4908128dffeb190251dfbd43204a3ff790640946fff5848128dff6b090251bff560204a37ffad5389473ff5267128e7fca4ce251effd289c4a3bffa8d38947bff49a7128f7fe924e251ff79249c4a3bf7a8738947eff38e7128ffde41ce251bffd6a984a33ff2d5309473ff5266128e7fca4cc251bffd68984a3dffa5130946fff59e6128effea3cc251fdfd46984a3bbfa8d30947f7f39a6128f7fe924c251ff7924984a3bf7a8730947f7f30e6128ffde41cc251effd22984a37ffad518947bff5263128e7fea4c6251eff9498c4a3dffa5118946fff59e3128effea3c6251bffd668c4a3bffa8d18947bff49a3128ffdea1c6251dfbd438c4a3ff79c718947bff48a3128f7fc9452151ef7924a42a3bf7a87485473ff5aa90a8e7fcb552151eff968a42a39ffa8f48547bff41e90a8f7bcb252151effce4a42a39ffa8748547bff40e90a8f7fe71d2151effd02a42a3dff8c548546bff5a680a8effea4d0151cff949a02a3dffa51405477ff51e80a8f7fe93d0151effd24a02a3fef249405477ff50e80a8ffde41d0151ffed21a02a3dfda4340547ffa5aa80a8fff6b4d0151efed69a02a3ffd2d340547ffb52680a8f7f6a4d0151ffe949a02a3dfd29340547ffb4a280a8f7f69450151ffed67a02a3ffda8f40547ffb49e80a8f7f693d0151ffed07a02a3ffdacd40547f7a59a80a8fff6a350151ffed26a02a3efda0d40547ffb39a80a8fff6b2d0151ffed25a02a3ffdac940547ffb51280a8fff69250151efed24a02a3fed24940547ffb39280a8fff66250151ffed63a02a3ffda8740547feb50e80a8eff6a1d0151dfad43a02a3ffda0740547ffb38e80a8ffd641d0151ffed62a02a3ffd2c540547ffb50a80a8fff4a150151ffed22a02a3ffd24540547ffb40a80a8fbf68150151ffece2a02a3ffd94540547fbb28a80a8fff6b050151cffd499c2a37ffad138547eff41e70a8effea1ce151dfbd439c2a3ff790738547eff38a70a8f7f690ce151ffed019c2a3dfda9338546ffb5a270a8fff6a44e151efed289c2a3ffd25138547efb41e70a8fff6a34e151efed269c2a else 0x1fff4e4a00c3bfea8740187ffd38e8030fffa51d0061ffb4a3a00c3ff690740187ffc58a8030fff89150061fff4e2a00c3fbe98540187ffd18a8030fbf280d00619ffd6a9c0c39ffa93381877ff5227030effea1ce061fbfce39c0c3fbf98538187ffb4067030f6fe944c061edfd27980c3fbfa0f30187b7f4966030eefea1cc061fdfd03980c3fbf9c730187f7f28e6030fede51cc061edfd22980c3fbf9c530187f7f28a6030fefe314c061fdf500980c3fbe9c130186bff5a65030e7fea4ca061dffd47940c3bffa8728187f7f30a5030effaa4c8061dff548900c3bfea8f20187ffd41e4030fffa72c8061ffb4a3900c3ffe9c520187f7d30a4030fffa5148061ffe501900c35ffad3101873ff5262030effea3c4061bdfd66880c3bffa8710187f7f30a2030effaa044061fdf4c0880c3bfead5101877fd5262030effaa3c4061eff527880c3ffea0f10187f7d59a2030fffa72c4061ff7124880c3ffe9c9101877fd50e2030fffa81c4061fff4e3880c3ffe94710187fed28e2030ffda41c4061fdf4c2880c3ffa94510187bde592a4a8efbcb254951cffd66a92a39ffac9525473de592a4a8e7feb154951cff962a92a39ffa9252546fff588a4a8d7feb214951affd62292a31ffac4525473ff526a328effea3d4651dff160a8ca33ffad5499467fe5aa9328e7fea4d26518ff96aa4ca39ffa8f49946fff5aa7328cffeb54e651dffd499cca39ffa93399473fe5267328d7fcb4d4451cffd49a88a3bffa8d511473ff5269228d7feb552451cffd46a48a3dff9cd49147bdf5249228efbea492451cf7d49248a3def292491477df5189228f7be9312451ff7ce6248a39ffa93311477ff51e6228f7fe93cc451eff969a86a39ff29350d477ff51aa1a8f7fe9354351fff160a86a3ff72d350d47bee5a6a1a8efdca4d4351dfbd46a86a3bf7a8950d47fce492a1a8ffd8b054351cffd69a86a39ff2d350d473ff49aa1a8effe7354351dff160a86a3bf72d350d473ee5a6a1a8efdeb354351dfbd26a86a3bf79cd50d477ef592a1a8efde9254351df3924a86a3bf798950d477ef58aa1a8efdcb154351dfbd60a86a3bf62c150d46fff5aa61a8cffeb54c351effd49986a39ffa9330d46fff59e61a8effea3cc351effd27986a3ff7a8730d477ef50e61a8ffde71cc351bfbd6a906a3bf7a9320d47fef51a41a8efdea348351ffbce6906a35ff2d3509477ff526a128e7fea4d4251dff949a84a39ff293509477ff522a128fdfcb3d4251dffd47a84a3bffa8d50947bff49aa128effea254251effd24a84a3fef249509477ff50ea128efdea1d4251ffbc83a84a3ffe2c150946bff5a4a128e7fea494251bffd68284a3bffa9050946f7f598a128dfbeb214251bffd63284a37f7ac6509477ef50ca128dffab0142519ff96aa44a39ffa9348947bde4)) else (if i < 9 then 0xc5495867ff5a892b0e7fea492561bffd6824ac37ffac4495873ff52672b0e7fea4d2461dffd48a48c3bffa8f491873ff5229230e7fea3d2461effd07a48c3dff9cb491877df5249230e7bea492461df7d48248c3defa50491877df51c9230f7be9392461ff7d07248c3defa4a49187bde4949230ffbe7292461affd699c8c39ffa93391877ff5227230f7fe944e461ebfd279c8c3dffa4b391873ff4a2a1b0e7fe93d4361cffd25a86c3bffa8f40d87bff49e81b0f7fe92d0361dfbd43a06c33ffad538d873ff52671b0dffeb44e361effd289c6c3f7fa0f38d87bff49671b0efdea1ce361cffd49946c3dffa5128d86fff59e51b0effea3ca361effd27946c3dffa4b28d877ef50e51b0ffde81ca361ffbce3946c3bf7ad528d87fee5a651b0efdea4ca361ffbd68946c3df7a5128d87fef59e51b0efdea3ca361efbd27946c3ff7a0f28d87fef59251b0ff9c924a361ffbce4946c3ff7ac528d87fee58a51b0efdea4c8361dfbd47906c3ff7a0f20d87fef39641b0e7fea4d2261dffd48a44c3bffa8f48987bde4929130e7feb552261cffd47a44c3dffa0f48987bff3969130f7bcb252261effce4a44c39ffa8748987bff40e9130f7fe71d2261effca3a44c33ffad4489873ff5249130dffeb412261dffd48244c3dffa5048986f7f5989130dffeb292261effd25244c3def24848987fef28c9130e7fea4ce261effd259c4c3dffa4938987fde4927130fefe944c261edfd28984c3bbfa8f30987f7f49e6130f6fe93cc261fdfd07984c3fbfa4b30987b7f4966130fefc92cc261fdfce5984c3fbfa4930987b7f4926130febc924c261fdfce4984c3bbfa8730987f7f40e6130fefe71cc261fdfca3984c3fb794730987f6f20e6130fefe914c261edfd22984c35ffad328986bfe5a65130effea4ca261dffd48944c3dffa4928987fde4925130ff7e51ca261febca3944c33ffad428986bff5a45130e7fea48a261bffd68144c3bffa9028986f7f5985130dfbeb20a261bffd63144c37f7ac628987fef20c5130dffab00a261cffd498c4c3dffa51189877ff51e3130f7fe93c6261bffd658c4c3dffa4b18987fef38e3130ffde51c6261fdfcc28c4c3ffdad340587bfb5a680b0fff6b3d0161ffed27a02c3dfda4f40587ffb59680b0fff692d0161ffe925a02c3ffd9cb40587ffb59280b0fff69250161ff6924a02c3ffd9c940587ffb58e80b0fff671d0161ffac83a02c3ffdac540587ffb48a80b0fff49150161ffeca2a02c3ffd14540587ffb58280b0e7fe9454061cffd27a80c3bffa0f501873ff496a030effe81d4061dffce3a80c3bff947501877ef28ea030e7fe9154061dffce2a80c3bff8c5501877ff51e8030effea1d0061fdfcc2a00c3efda03401877fd5028030effab550061dff549a00c3bfea8f40187bfd4968030ffb8925006 else (if i < 10 then 0x8f7fe6252271cffd43a44e3dffa07489c7bff30e9138f7fe51d22719ff96a984e3f3f9cd309c7bff4966138fefe62cc271effd24984e3fef249309c7bff4a23138f7fe9346271fbfce68c4e3dffa4b189c77ef50e3138ffde51c6271dffd48a42e3dff251485c7eff41e90b8f7bc9252171eff968a42e39ffa91485c7aff41e90b8f7bcb252171cffd43a42e3dffa07485c7bff28e90b8f7fe3152171affd69a02e3bffa93405c7bff4a280b8fdfe83d0171ff7924a02e3bffa87405c73ff52630b8dffeb446171effd288c2e3dffa4b185c7fef40e30b8ffde51c6171ffbc628c2e3ffda03185c77ef52630b8ffdcb446171ffb9288c2e3fe7249185c7bef48a30b8ffd680c6171cff969a80e3bff2d1501c73ff4a2a038e7fe9354071cffd25a80e33ffac7501c77ff40ea038effe61d4071dffca3a80e3bf7947501c73ff48aa038effe6154071dffc62a80e39ffa43501c77ff406a038effe30d4071dfbc61a80e33ffad5401c67fe5aa8038d7feb4d0071cffd49a00e3bffa91401c7eff41e8038fdfe7350071dffd43a00e3bfea81401c77fd5aa8038eff8b550071dff549a00e3ffea91401c77fd5228038fdfab3d0071fbf507a00e3ffea8d401c7efd39a8038f7fa92d0071ff7124a00e3ffe989401c7ffd50e8038effaa1d0071fff503a00e3ffe987401c7ffd28e8038ffda51d0071ffb483a00e3ffea85401c7ffd30a8038fffa3150071fff501a00e3efea03401c7ffd1868038ffda30d0071bbfd689c0e3d7fa51381c7aff49a7038f5fe92ce071dbfd439c0e3f7fa07381c7eff30e7038fdfe51ce071fbbca39c0e3d7fa45381c7eff30a7038fdfe314e071ebfd219c0e3f7fa03381c7eff1867038fdde30ce071fbf5009c0e39ffa93301c6eff59e6038fdfe83cc071dffd43980e3fbf987301c77fd5026038fdfa704c071fbfd07940e3f7f9cd281c77ff50e5038fdfa704a071dff549900e3ffea91201c7efd41e4038fffaa348071fbf4e6900e3ffe98b201c7fed28e4038fffaa148071fff4c2900e3ff68c3201c67fe5aa2038fdfe83c4071fbfce6880e3bffa87101c77fd5022038fdfa7044071dff56a880e3bfe2d5101c77fd5262038fff8b444071fff128880e3f7eacf101c7efd41e2038fdfa7344071fff4c5880e3fee249101c7ffd3122038effaa1c4071fff503880e3ffe987101c7ffd28e2038ffda51c4071ffb483880e3dfea43101c7fed1862038e7fea4c2071dffd48840e3f7fa0f081c77ff50e1038efbcb2549619ffd6aa50c39ffa934a1873ff5aa9430f7bcb252861eff962a50c3bffa5151d873ff4a2a3b0cffeb552761cffd49a4ec3bffa9149d873ff52293b0f7bcb2527619ffd6aa0ec35ffad341d876ff51e83b0e7fea4d2561dffd47a4ac39ffad5495873ff51e92b0f7fe83d2561ef7964a4ac3dff2 else 0x69a81039ff2d3502073ff4a2a040eefcb354081dffce6a81033ffac7502077fe58aa040e7fe90d4081cffd49a0103dffa43402079ff5a68040f3fea4d0081f7fd47a0103effa8d40207d7e51a8040fbfe7350081f7fd45a0103effa8740207dfe58a8040fbfea150081f7f942a0103cffa4340207dff1868040fbf630d0081f7bc61a0103efe2d340207dfd5268040fbf8a4d0081f7f567a0103efea4f40207dfd5968040fbf8b2d0081f7f525a0103efe24b40207dfd5928040fbfaa250081f7f524a0103eee24940207dfd3928040fbfa6250081f7f562a0103efe2c540207dfd48a8040fbf89150081f7f0a2a0103efeac340207dfd4868040fbfa30d0081f7b461a0103ef48c3402073ff5261040effea1c2081fff50084103efea01082077de592a4b8efecb154971cffd49292e37ffad0525c63ff5a0a4b8c7feb294971aff969a90e3bff293521c77fe5a6a438e7fcb4d4871ddf966a90e35ffad2521c6fff58ca438dffab0148719ffd6aa50e33ff2d54a1c73ff5269438e7feb552871cff96aa50e3dffa914a1c7bde5929438cffeb512871cffd49250e377face4a1c6fff5949438dffeb112871bffd61250e3f7f29341dc7bff4a2a338cffcb552671cffd49a4ce3bffa91499c7eff41e9338edfea44e671fbfd289cce3d7fa51399c67fe5aa92b8e7fea4d2571eff928a4ae3f7f9cd495c73ff5aa92b8e7fcb552571eff968a4ae3d7f9cd495c7bde59292b8cffcb54c571f9fce698ae39ffa93491c77ff5229238fdfe83d2471fbfce6a48e3dffa91491c7aff41e9238f7fea352471ebfce6a48e3dff98b491c7bdf5249238efbea492471cf7d49248e3fefa90491c77df5209238f7be9412471ef7928248e3f6fa0e491c7fdf5189238f7be9312471fb7ce6248e3defa4a491c7fdf3149238e7fea4cc471dffd48988e3dffa51311c7eff41e6238f7fe92cc471effd28a86e3dffa4d50dc73fe5a6a1b8e7fe9454371cffd26a86e39ffa4b50dc77f658aa1b8e7fea4d0371effd28a06e3f7f9cd40dc7bff49681b8e7fea4cc371effd28986e3dffa4b30dc7fef50e61b8efdea1cc371ffbd03986e33ff2d528dc7bff4a251b8dffeb34a371effd26946e3f7f9cd28dc77ef50e51b8ffde81ca371ffbcc3946e3bf7ad528dc77ee5aa51b8efdea4ca371ffbd68946e3ff72d128dc7bef4a251b8ffdc944a371ffbd66946e3f779cd28dc7fef59251b8ff9c924a371ffbcc4946e3ff7ac528dc7fef58651b8efdea4c8371ffbd48906e3ff7a8d20dc7eef39a41b8ffdea2c8371ffbcc5906e3dffa51509c7bff492a138ffbc9254271ffbc83a84e33ff2d5489c73ff5269138effea452271eff928a44e3f7fa0f489c7eff39a9138f7bc9252271cffd6aa44e39ff2d5489c7bfe5a29138f5fe83d2271ebfce6a44e3dff98b489c7bde592913)))) else (if i < 17 then (if i < 14 then (if i < 12 then 0x74cc1cfd873581c98071ca1c2286fea1bae06e241b4a86cb21b0d06b4a1a8a069121a1c067fa19d8066da1997065c01931063bc18c90621c18668601617c505dd416f785b16168485952160e0577615ad8559c14fe052d814630509213e004e28136784c5c1276047d811ac8462811450437410a084154100403eac0efd83b400e8a838f40dc5835e80d42834140cc1031ca0c4902ea60b5802c820af902b080a84029820a03826e6098302422086a81f14079901d260690818cc05e3014fe050101316047980f68033000aac0279009260222007f001d5806c4018a8056801340045e00fc0037e00b98026a00720015400006fbcb254976cffd49a48edbefa92491db3df524923b67fea4d2176effd28a42eddffa4b485dbfde59290bb77fe9252176ff7924a42eddef249485dbbff48a90bb67feb552176ef7964a42ed9ffa45501db3ff486a03b6ffaa4c8076fff522900edffea43201dbbff4a2203b77fe92c4076dffd43880eddffa43101db7fd502203b7ffa8044076dff56a880edbfea93101dbffd4a2203b7ffa92c4076fff524880edfee249101db7fd50e203b7ffa51c4076ffb4a3880edff6907101dbffd486203b77fa90c4076fff461880edff68c3101dbbff4a2103b77fe92c2076dffd43840edff7947081dbbff48a103b7ffa8042076fff440840ed5ffad2289933ff52451325efeb30a264edfd26144c97ffac228992ffd580513277fa92d0064ffb461a00c9dfea4f10193fed28e203277fa90c4064ffb461880c9fef2c95260777e59aa4c0efbcb254981cffd67a93039ffac9526073de592a4c0e7feb154981cff962a93039ffa9252606fff59ca4c0dffeb1149818ffd62293037ffad549e067fe5aa93c0f7fea4d2781cffd49a4f03dff29349e07fde59293c0d7fcb4d4481cffd49a8903bffa8f51207bff5269240e7fea4d2481effd27a4903dffa4d49207fdf5249240f7bea492481df7d49249039efa9249207bde5249240ffbea392481ff7d2724903defa4e49207fdf5189240febca312481ff7d2624903defa4c49207bff5267240e7fea4ce481fdf9469c9039ffa9331206fff5aa9140cffcb552281effd49a45039ffa9348a07bfe5269140f7fe93d2281fdf946a4503dffa4d48a07bff4969140ffbcb252281effd24a4503fef24948a07bde4929140fff4b0d2281bffd6a245033ffad448a073ff5249140dffeb412281b7fd6824503fbf28c48a06fff5949140f7fe9292281ef7924245037ffac248a077ff5265140e7fca4ca281ff7924945037ffad228a06bff5a45140e7fea48a281cff949145037efac828a07fde4905140dffeb00a281bff56014503bffa8f50207f7e59aa040effea354081fdf946a8103bbf28d502077ff516a040dffeb1d4081dffd43a8103bffa85502077fe50aa040e7feb4d40818ffd else (if i < 13 then 0x732e1ca38722a9c7ea71431c442705a9c0d66fc11be466f761bc846ee51bb186e991b9c46e431b71e6d729b4e46cdd1b2d26c591b09c6bf21af0c6b901ad8a6b3a9ac246acd1aa906a1d9a75c69af9a66a69711a57269491a45668fa1a37068b71a246686a1a15c67f319f4a67b719cac670599b7a66c119a86667f9997a659a195b065501939a64ca9915c643d19058637718d6c62d998a2e6271988fe621f987f661bd98654616f185266123983e460d4982205ffc97f845f9f17de05f4d97ca65f0497b705eaf97a225e409786a5deb9770e5d9f975e65d53974925cff173845caa1720a5c59170ae5c0616ede5b7096cfa5b1a16b285a99969a05a411683e59e69671e59a0965c6592c1641658ce162a0587716138581015fa657bf95e62575315c8856f095b4856a8159d6564e958c25609157b455b1155fc5563954ba54fe153a8548395192540b94fbc539214d8e531514bb65283949ba520f1477051a2146305179944d050e69435e50ba14282504793e444f6b13c844ed393a624e6c139004e21937c64dc29364c4d6e935444d28133e84cd5132e04c8c131904c3292fd84bde92e864b5692cb04afe92b584aa8129ee4a571282649e8126d4498d925e84955924c4491d123d048e09231448b09224e487f92128477d91cf646f791b28467a9193446279177645a091588453b9147844f4912da448f11184441190f1843aa90d9e433c10c8242f890b2c42ac10a2a4259908ca4209907ae41be1066241719057641299043440da1033a408a901a6404f1007840120ffd83fb18fe3c3f838fc723eff0fb843ec38fae03e720f9223e2a8f8163dd58f7043d460f4e43d080f2ee3c9b0f21a3c660f11c3c3b0f07e3b9f8ee003b290ec343ae78eb163aaa0ea603a638e91039ea8e70a39928e5ba39530e46238f90e36e38b60e248386b8dffe37ea8dea0378f8ddbe37530dc2836c38d9f0364b0d88635fb0d72035978d598353f0d47834ef0d32234980d0f0340a8cfb833a50cda2333f0cc5832ee0cad6328f8c9a232410c86c31fb8c77a31bc0c68231798c546312e8c41630e20c300309b0c12e2fb10be562f538bcac2f018bb6a2eb18ba522e6b8b9142e1c8b7b02dd08b68c2d7d8b5882d398b4922cf58b3402cb38b1ba2c3c0b0a42bf98af042ba68ad1c2b230ac622adf0ab0c2aad0aa8a2a6a0a9382a398a88c2a088a6ac297e0a5a229428a4b829180a38e288b8a1ba28518a0da281589ffe27db09efa27aa09e58277809d18271289b9c26bd09a5c266d8993c2627897da25c48967a25808956825308944024e0892d4249709200245f890c223e788e6a237288d38232308c1622e188a10225e888d82217087a221c908666217c885082114883c220c60826e207e8812c1fd687ea61f5c87c561e9e079141e23877ca1dd4876d41d708 else 0x3630ad890360d4d81cb6016d7da35ea6d77f35cd2d71bb5be6d6cb35a4cd63235800d5e13572ad5a335566d495b51d8d44cb50b8d40db4f30d39134daad331b4bfed2dcb4aecd275b489ad175b4544d12034414d081b4124d02833feacfc8b3ea8cf7eb3d56cf41b3c60cee5b3ae2ce71b392ace0fb372ccd89335b4cd38b346cccfeb330ccc87331cccc45b30accc20b304ecc0932f88cbbb32dfccb58b2ceacb1e32bfacae432aceca74b289ac9a1b23f0c8723206ac7cd31e00c73ab1a4cc66db18d0c61631750c5b031628c572314b8c508b13aac4c6311f8c43430f3cc38f30d3cc30430b64c29930956c20ab0702c17e30440c0e93036ac0b1b01a6c042b007abff7aff7cbfc6afea0bf6fafd30bf18afb1ebe8faf936be18af7eebdcbaf6babd76af55ebd3faf488bd05af3a4bcc22f2aabc53af08ebbfb2ef6abbb02ee18bb442ebb6ba662e8faba20ae800b9e22e628b967ae49eb8edae24ab85dae0dab7f0adf1eb798add5ab7142db48b668ad90eb61dad7dab5d22d674b57f2d4ccb50d2d372b4afad220b467ad102b427ad004b3e32cf0ab37eacbeeb2d7acac6b28bac982b239ac882b1c12c642b126ac434b0f42c2d0b0742c03cafd7abea4af692bcd4aef52bafeae95ab9daae4dab846adce2b640ad54ab48cacebab2f4ac8bab16aac082af44ab9e2ad92ab242aba4aab4aa9dcaa20aa776a9902a51ea9292a40aa8bfaa262a879aa0d8a7e829ebaa78529db4a73529c64a6fb29ad8a694a9948a61c297cea5b429652a553a94c6a50aa93aca4afa922ca44f2908ea40228ec0a373a8cdaa2f8a8acca272a88eea208a864aa15fa84a4a0e7a82e4a06ca80d29fe4a7ea49f5a27ace9e7aa78f69e0ba772a9d5fa74869ce3271709c3ca70729be526f129b9926bee9ace26aac9a8b269829a34a684c99c9a661298de2622098552607097d7a5e9c9771a5bc896a325968961ea57489582254f494f92530c94842500893a9a4db29339a4c2892ea24b2292a0a49fc925e2478091aa245a2911d242329063a409a8f9ba3e068f63a3ce48f13a3b928ea1239f68dca236148d62a33e08cd42325e8c74230fe8bf9a2f748b9722de68b4aa2c988ac6a29848a3a2287289c6225fc89592241a88f9222c688932218a8831a2054880121f6887a6a1e42874d21c6286f7a1b408623a181085e22170a8547a145684ed213108494210f4841720e6a835ea0ccc831220ac28292a096a8219a07f681c5a06c88192a05808142a044080f2a032680a3a01fc8063200c07fed1fcac7f271fb6c7ec51fa967e899f77e7dc19f68e7d901f4627cf91f3967c531f0847c051ef007ba49ecd07b051eb7e7ac21e9367a3a1e7ce79cf9e6b879871e57079369e43878ee1e31278759e11477731dbdc76d41da9276019d69875899d32674a29cf9e73ba9cdda)) else (if i < 15 then 0x93f2b4fbd13ec7cfaaf3e7f4f9513e24cf7cd3dc14f60f3d694f4e33d1ccf3633cb5cf2213c6dcf1473c2dcefa53baf4edf33b434ec6b3ae14eae73a96ce7d539c64e62f3937ce41138b34e16d37bc4ddff3748cdc7336e64da5f3659cd72f35694d52b34e44d2fb34644d05b33b2ccdbd33464cc4d32eaccaa13287cc94732274c5f531294c3673083cc18130204bfe52fdc4bf472f7d4bd532f414bcdb2f21cbbdb2eb8cba1f2e434b8372ddb4b6cf2d7ecb4d72d0d4b3572c884af0d2b954ad892b1dcabb32ac4ca89b29f2ca6fb2978ca54f28adca21928254a00327b7c9e23276149ceb271cc9b5926a6c99a9263b498a125eb4972f2582c95732513c93d124a3c9191243cc900f23bec8e8b2375c8d69233148c0f22b8c8a5322784884921d1486512165483db20a2c81f1202cc7fb11fa7c7d491f19c7ae71e7cc79491e1ec779b1d59474e71d1cc733d1c6dc70ef1bea46f111ba746e4f1b47c6c851afb46b7d1aca4693d1a144678d19bac66211962464e719194630d185a4604b17eac5e991783c5cd7170fc5ab116934580715d9456ad15834559314abc50e31400c4f0d13a2c4ddb134fc4c5912ed44b151240447b511cec45ef1129443ff10d14429f108744175101d43fd90fdfc3ee10f5743bdb0e7f438d70e0bc37130d9d436010d2d433a70cc7432670c58430a90c11c2f990bce42ecb0b79c2d930b4542c590aef42afd0a91c29cb0a55c283909e6c272d09a2c25890927c23d908c7c228f0860420d307fbc1f7707a541de10752c1ca70703c1b19069ec18c3060941739059ec15d70541413cd04d3c12990465410c50403c0f3103bfc0e4b035f40d2502ff40b8f02a4c09c50247408ab01cec069f0183403af00c140293001c3ffb0ffc53fe64ff71bfd40ff35bfae0fe3fbf882fe02bf748fd9cbf55cfd0bbf180fc443f080fbdbbee86fb7ebed30fb1c3ebf8fadd3eacefa183e7c4f9c63e4d2f9043e2f6f882be136f8253dfb6f7d93debcf773bdcb6f6f83da4cf656bd84ef5ee3d606f55d3d442f4e23d21af4123cfc4f3b9bcdd8f35abccf8f3043cb86f2c73ca8af26dbc8aef1f9bc684f1773c572f12a3c3eaf0d63c292f07dbc164f03cbc060eff2bbf50efae3bdf8ef3f3bc8ceee03b8e0ee0a3b762edaebb5e4ed47bb452ecd53b2e4ec8e3b1a2ec243aeeceb853ad48eb3c3ac52eaed3ab40eaaa3a79ce9983a5ace92eba444e8cfba282e882ba174e838ba04ce7ddb9efee79639d52e729b9c18e63e398c4e602b9690e4f73937ce44338e00e36a38c06e2a1b89ece261388f6e21838802e1e83868ee17a3858ce137b83b6e0a8381c2e02337fdadfc837e9edf80b7d40df2237c04debbb7a3addd3b76d8dd8337566dd393745adcee37284dc7f370eedbbf36d8adb2736c0cdacf36ab4da6a368d4da03366aad96c else (if i < 16 then 0x16597d9654e58c796276581f95f46578595ce6570f956ee54af950de538394cc652e3946b6510b9401e4f77938be4d3d931c64b2f92aee495d9231e482d91e4646179138e443590dc642e39095641bf9049e40bd900963f178fa8e3e118f5de3d298f0363b778e8c638918de9e36758d706352b8d2ce33998cb6e32418c67630bb8bef62ec98b84e2d818b3b62c618af162b498aa8629c38a48e28a789f4e271f896be2529892e623bd889ee21398817e1fc987d261eab876b61c8586fbe1b7b869fe19e18659e189f85d1615f58525e136984b2e123d8473610cd83fe60f0b838360d3f833de0bd782c0e09d3826a608df81f5e068f8180e05bb8118603f980d9e02ed807ae010b80386006b80005ff617f96dfde57f3b5fbbf7eafdf9b97e34df76f7dc15f6cf7d96df5717d0a5f3af7ccfdf26b7c6c5f15f7c2bdefd77baf5ede97b5d5eca57b07deb717aa35ea157a685e8e179e6de6d379a2de5757952de4c3791a5e39178d9de3097892de0b1780cddfbb77cadddbf771a5dbc776a5dd9957647dd8a375f65d70b7592dd5cb7536dd46974de5d30774a55d2137457dd0b173f35cf0b7387dcd69733fdcc6972f05caef7275dc9357206dc78b71c55c53771175c36570bbdc0e96feedbe316f2edbb696e9cdb9fd6e44db7636db1db5976d47db3e76cb35b2316c64db0616beddaf496bb6dad0d6adedaaff6aa25a9df69fdda60b6938da3316872da12f67fbd9ea3678359d05670159b8366bc599fd66595983f65ccd9625656c5951f6521d93cb64a7d9189643c5905b63fad8f4f639fd8d81633958c4d62ec58b0f62b058a016251588a361eb5873761a4d86256148584b360e7d82776080581b1602c580255fe657ef75f9657d895f4dd7ce95ef457b5b5eb95797f5e37577b95dc6d76855d55574bf5ce3d72f75c97d71c95c23d6f995bbad6e5b5b7156cc75b0956ba95aa5d6a3b5a425687359ff5678759cdd65ef59275642d58ae561fd586bd5ff357e0d5ef757b355da7571e55c0b56c255a915687559a95613557cd55d9556715544d53cd54c2552155456550b5540054dd15320d4b0f5280d493d522b5472f5188d45875119543e950bb541f55057d40c9500cd3f794fb8d3e514f7153d794f4253c414ef353b7d4e8ad39af4e56d38cf4e16537e34de65364d4d7d535614d34534514ce5d33434caa5321b4c61d30f34bfed2efd4b99d2d6b4b3652c654afad2b3f4a90529ab4a4dd28bb4a0b527b549acd260149585249348ded22814861d21174804d1fa547c251e19475ed1d27472c51c4146d851af1461c5176d4597d15c74550514c34515513df44b9511ed4457d106f43e1d0f1743a7d0e054344d0c2142e550af942a3d094d421b5072d418cd05bf4152d04fb410f5035b40a3d023d407bd01294036d00313feecff6d3f8a4fd2 else 0x5c09100a580fd307f38048620e384014673a600339307999c98102a03ed4180d9845e15db85eeebaeeeed5576febaaaebaaef5af77dbb5a0000186186186004a086205809004398170cbbb80abddebbbd6eebbbaedc001daaed56ff476abbeab6bf4530c30c030c08203f806205807b038d4190edb6db6db6db6db6ddbb76eddad6b5ad6db6db6dbb599f99b33300c7c07e02f00c23932001848202501f01807a0234bdc701a301014403808e056976500503280c011c08d2ed00402d00680a208d2e380d014403808e04697401680803002d0234b8e03405100e023811af3a2c06100504d008811c0ad2ed00402d00680a2088cc8168140550371802026809e0658881416203303562704d40100aa08e047226a06a0200ce0c044881090c980cc1cf045cd80e40400c41820f1393e4e2400243f1982c781320501e81b41c70de0577808fdff977d03df0277b55de9ef7a0dde667794dddf3f773bdd947751fdd08f7325dc9a771fddc5bf70d7dc1176fc7dbcaf6e59db6676cb3dafa76b2ddab076a57da4ff6891da07f6773d9a376613d94576483d8dff62edd896f61e7d85ff60edd82076007d7c475df9d72a75b9dd6c6f5a67d667758add5f7f571bd5947558dd53f7542bd4cef5267d46af4f19d39574d39d2fc74b8bd2b4748a7d1f7746d1d186f44d9d129f4413d0b1f41bdd044f4081cfe373ef7cf9673dcdcf2773bcbce3af381dcddff370dcd2df3425cc81f3195cc1472fb7cbab72e1fcb43f2c91cada72aadca5f72947ca15727b3c9b9f25c9c94472473c8f7f2119c829f2005c77571cd3c709f1a59c6757191bc61cf16b7c58471541c4d9f129dc47ff0ec7c365f0c77c28770979c22cf061fc158f04edc11df0405c0ad701edc055f00bfbfff6ff67bfae6fbc9bec4efa0bbe356f81bbdc76f68bbd59ef473bcfd6f325bc98ef1c7bc4ceefebbbddeeeabbb8c6ed9fbb3d6ec7dbaeb6eb2bba5c6e869b9cfee64db959ee3f5b8b66e1d5b80f6de9fb76d6dc95b6c76da8fb5fb6d743b58ced49fb4ac6d15fb3f36cee3b3796ccc3b2b4ec7fdb16c6c4e1b112ec3cfb0ca6c25bb0626c065aff2ebe1faf25ebb81aec5ebac9ae896b861adb36b659ad4deb409acb26b1a9ac2beafafabcfeadf5ab0feab29aa7fea957aa1fea805a9ef6a76fa989ea501a9226a3f5a8a96a257a84aea007a7b969e2ba76ee9cd1a70569b5ba684698c3a5cae95b7a530e9453a502e93e1a4dce9217a472e90b7a40c68f53a3a168b9fa2c4e88a1a1d2e8501a0c7e82d3a054680199faf67e179f39e7c4b9eece7b459eac67a419e73e78eb9ddee75e59d21e73219c7e6718b9c48670679bc5e6e7d9b77e6d4f9b0ee6ba59a97e69c19a37e683d99e3e66359956664c598f3e63139884e6187982ce5f9d97c9e5e8b976b65d379706e5bb396d065aa9967))) else (if i < 20 then (if i < 18 then 0x121f805c7c01e64590c5c10c0770103a82050ce3903379fff4df04c25a11506810c40a205813e43842200e181f7982c40a8e0113e038e14af9ccde66033366c0ace12802301c8690a1f1e2fcfe910020e63704b01d40b00470183c41b30e08a480c4c47a0d98205827cd2401c1807fe6054704b80dc0227c071c30fc2ef8bdde00aeb40000577fad0a2eeedcffa1fd0ad0a2bb421c031e05801a0080d107d83b006d127cfbf77bfaaddb76dbcff6cdb66b7ff6c25103180340100aa431078b80c1b3122e078f7c4400281c49b824074a05087038e141102032388e82050410f100e01fbe60b102a3825c0223d071c339fcb9ecd9b7cfdb36d2bff584800ad031218c0180a2a0c7094403c6363718da4b2c0a2431506043a10385f3f0bc9c02086e09603b80d41810406cc3147de19c7ec0c1b01d983c40ab00470810101c70c1e3f8cfcc3825f00322c862e097041011c060ea0814396ee63faccd593fd6a92d5067e7cb81b7fcc296aab67b0667ecf81ec10201b40182080f106c80c421c0e389019101d80f302c09f01c70610f110700fdf30588151c12e0113e038e183ec339f8065031de60f102b10c5c20404071c33fe5eff77dafedadb9fb66db66db605502880da06300680210c44f80d98918f60c2c3b060d818fcc18605670938401c70a7818d89cc60cc0ad031218841210f03306cd398c319815a062431078c20b970f1f22008093704b01c01410e071c281c73efc049e780c8b08ab8241c6434075040a1821220074c162434071c1911f88a73ceca73cecdea73ce6edd4e7b39b77dddc8124b10667d9ce2da00810408103c581612d867e5e0593eddc0632d8d8155c1100470089f08630c2043a5e29604c20401921883fa104090b14e19643107641078192202962c0d300b10c41c7062f1f1101c014dc12a0570084381c70a08812064702c040a097ffddf5e6edad606cd6cd81580ab00420208f41e2c0b8707c77186f3001ec5916824087380c1f61028507180d88a337b8ed418c0b08741affffbbebcdfb77f6b604cccc1ad9b01580aa036704c01080823d078b02e24db37cde1b66d9b73b77f76ed2d2d68d86ce4d86fc3666336067640036018c010808104078838e1ca97e778572e9fd72e9dbae5d3edf6eb0ec3330bc3d648581bfd9f003f8863004d0638042040d0071c402244008fcc16c055071c18413cc92401c18fc7cc162054704b8044f80e3863b91eb39d7e92d525eaaf9cddbfffaf530fe67fcf3e067f9e604b258c608203f81f603100c838d41805545f03662975cf7dd6f606f6fbfb6b6336703121884100aa0d950643087c61a5ce079c0cc4e1e600c83ec20827c07f4292f17e97e77d33acc2f3d9d39d76eeca4d56a7b5f026c333ec0c7f363043803221970189f0208102871ec0ce2103606dd98158208a0c071c2 else (if i < 19 then 0x9f80303121884121127f4e9801081405602ac211ac1cea0c01c8192581580ab04252402000aa0e302398c4080240c128506838c103bbf3e49e01808e062a09d04101c21c0d9860f3b80befc03d80965042808063407075040a189d6bc0a920604c086a1059e0c390308680ac0813c8a4060200c27c06cc1915815013023a034d709040180ac21a040f3cbf7f07c70189090739504c01940603107548182050e4d5c0a920604c0868113f93612d90301580ab08bb4e00c05610d418b76db2fc18700610d015a11726e00c056078c18fc8924230e181e01a80d98365605421888680c070a6491030492046903040825b0669cf84641a001610d10c41595c1dc016218886811d67b260d000b08688630844822403081580b01190329605402c01580df939dbd10d48180ac05400e42bb5fbe5edb86ed7fedeb6c9866667f01a00868021010062120071c83a200910a4109093241a010282039f8071f121e3403218b82180ea0c04c03ee180f13f2044c8e1b80600650102604740fb85063e1fe7fcfc7f0f0739c4a0cd00e062431d04b82540ae0307882601f7120f108f2701393e2bf069806431d0400c742407807dc3112a581501b221a0310224826db08008b02c035c0ca1608602a83a80d8ed411608602a81822c922019926024921d40a08b13e035c1023be08f0a018604b02200806d07dc28de11c280c09604501181a0fb0574d2d40405202388620813b9201e0fb00162c0190281f01c70a69780a340404710c4101fcbcf9c038164920400d3026008c0d068838e1bd3b6a009c0102890c610a1cf39405f07e66002c442fc0981e81b41c70c3cb10c541804f036820729e70087d9802c581203d036838e14f34c1202881b60cf3e8214051036c1ac9eef930278069c074042188260197cc3dce78083892410009c1208250281c70a1f29e1df870300280069812c0d90283fa1bcbb65004e0090c41350825c05104710c40dd2fc051802502880908e8da700470181e20c734c42ee02036c1b93f40518021012815085e9c183e492400824010809404071c280ef3042c024248604c01181e0e3073829674813c862051036821079c31d80ac848c42806b82540a082420271aa05a0200ce0c4e73366cc0be799998fce6666040a8051027815a814434862a4001ce404924067d01009e039071c204ee1e22000f8f03f660b1e00b01e40a27c071c3079efc7109feff9c9e2000f8fec07367c09704b01c009c0113e380c0f80e389082224005839982c40720e3830838f1100e0f9982c5c12c0713e038e144a488049480194702a840a0897124922001e81f4c41cc0b80210c41c70a3c880e053704b80421c0e384e2c0334a9a09a81486827c830f3e2e14f10039023802283180e10406cc28467fb99bcfffd9bf86fcc25a0d1068030e06243170908180ab else 0xc61081102ae3f4215603028d03e10d64bdc0a340402a813c0660a3dee77ee6f9be1d544765b25813f824a0606fd02846d0cbf3dcd80a580f40311e808a149390600e811c0638be732400f3080209e00809404807c071831e39c92500705902c0404b085038e10ba7f67004112058028c213d9ad60207583a40ca08d375102004490340a2085a6eff8214219e0082240b005106376a01809f281a029046b9a103427c2068144109ecd580a81a0e90820234dd408011240d028822ba640c40da09a83d3802c01041b40c69edb10b80c00db06d102020202680cb4d7073c0e407802b044ef2d10cd80816206d8427c14520c60380e4104e204060201c0720e38347f5d308a01b40a3065ca5f08502c40db064d3814503403e047020c4f7e29cf3807c8703813c0110921f00480e3867bf6eadfdbdf5f7fdfd6f7dc7eff39efffadfafbcec02bd01900484a05a30804801cc07ca054516886887002a031897c9c087839c1609400c0f809a0ec852d7bb40c7802058028c212fceba03f0041c00658469dea03e81a21c014610ba7f6e0082280b0051847680e010f03880cba7f6e0082240b00518425fbd01f8020e0014c23af3ad03408921c00a611af3a2c06140704d008811e0a4ec0107000a40c96fe02a7004c020e002882b4be20380b003f40a042b04d018c0a007ee4eb0158160066029846ba0381b608b5ee621a600814406c04f0564f623605891e8c20089181440aa08e037cfddbdfd603100f982280ec07e0080a61d477bbec46c03103788f48f50aa08e300810464e4080501d8041080e3040baf333086361815c80e43106a421cc0770102380dd743f6f6ddedc98acfb6fec11c05702b284415a034a05c39ec8352c020963008202380575c376d68631f82382360ad03c421c41a809630781e9e0d403c410238045c35b5b86bb7805607004a80db087106a0258c1a07ad42540182d7ea11a00c16440a70182380c574376dbdedc9bbfcfb6fc11e08e02b280c248034a05439f6741a8431b008258c020baf06a500608cd6cdbe119a0083520f5a84280305a782b40db0404f4666643333190048620d48374be75b76f6ef5899b6ff6c11c40407e84901cd40a8664e096a0580cc0ccb84668020d4830e0ee02b01b40c0f7b762e81606d82d3d40a078822c7d02940c4310198234e08e50301b60c682380f104079440f103da4205035011d0604bc66460cf6321881b41a906e4c9201840101280f073838c13d2726700a606205804c4225dacd48181ae0650180213d8d01200801a02d8274c8ac506039c0aa098041dc80740560368192d8f07380e403405b04fa73d300a603440711e826215af2e2580c140740402a8260149ec680900400d016c110b5c0102a01540d3bf2061202501200908f74a6940b00404c10c6101dda07381580da068e4ef6c)) else (if i < 21 then 0xa82621062f2720018483025806c0b02a83d0156e6890c404c0a40470213b2f028a068c04407047028c5f9f38a7003c50e02812203e00a1f00940e3861c60924cc0f192491c4780220904089f022a0a4ec0102c00a80c625f393c0107380803b0140f80960e38549fd73540702f8194061084ec0108a80a40c97ee680fc0108a80a611779640d102580208a028829d7908b845444a064bee411608a84120dbdf2e481a204b0041020518525f6480ec0b02200a410fe9d3014816006602b843c6d01c48c06d83f725805440960081540a20a5ba409e81a02880cc10dfd610cd01f8020b1841e80e05582084e4c80020a03a80c0940e30474e812e02603c184e6280014140950181281c608d02604119b9d140279fcda81940a0830408456149e79b02c22a051831c186e0102c0184e4c8020140750182101c608e80f03cba03b01dc05061e7721f0a0079036a02018d01c2100ef8536f36e812c07037c1b407813aefbde5fdff66dcdb4dbf6e08c225507502680e115065039620b75c020c301f419e3680e12805bc1bd1820c05241283680f024b9c3dcf6cb6cb7f00aca10012846c48d0a59f3b4062e01061984a11d36a11a03891a0dfcb04080a6812c078463fadb6dba04982480804484d7407701c11bdaf77df2dafdfcff76f36d3bffb6c0ad046112a80e80e11506103341df137a03c0bcddf58062609a03b8041870addd64b7bb537f36f36de031094011823e0e5857d66d41140720241eb508501e09e76b126091884b06f78c100029605c1da03c09c80d018640b0315fe7bddbef9737e6ecd6c5bfed9fdb360980406817406030a0383281cac0b8979e602b906c23306f4ff8b76ef9ade81636636080023380421e0e0218c374c02ca0fa03c1ba7b218805941a4258478c6d80e002c431837108a830d81606830c80e04f1ce1226006022502450a119842fb22038208187068bffbdcb7b536db736db6db203901017603108f83961975bce812a05014b01e10bcedf830d40ae01028807215d34c12c070618158105c2400565060195ce51b36cd9bcc241409506091a11f2cd40ae0302b41ba6b80423241b83f716029503380808d0879aa06700830c0b0089fcb02bd01cc24209842fadfbddbc1b5bfbadadff99b304590c4812209058c0c41caa0c881fa03a83a083ab6f6db36fed8c186046a04d01d41d0be7fe80ea0682ea0db8040664318324c0a203d047019f12799300390c00057813c0103e01281c60c3c77c8b9200e0b280809b01803c2140e3853bf727dffda10c9054c11c0102c40c41630e93b2de057d80e81e06507d02ba7796811022881e0b18466e9580c05340f07d023a79cbf821481a13e103c1630a93b3f2236b01d03c1340fa0574ec5bc0a208a11b103c1600be2ed1013803031082427729601481e004506ce96f04d101046 else (if i < 22 then 0xa7380416304eba0b7eb6fb36ef6fec9bff058815002ec0860081680f920e8876d6219603c80e0c7bd26b7dfbe136ee313366c08cc1290370041be23686e5847ae01058c181f8f223ec3b9fc17fe0b102a006981120360081181f110bdfe621900bb04a407c0185125e7f5c3cdbb98f4cd9be04837d81a27c11b42a99ae602037cc201020479fba9bfbd1b89b77cc9b37fb0827024407c01b0182b01be236884d058983e093f4eedf5cf3e86def626dfc16202a023103e41c0e811b43bbfaf36c89a236901980f8030aeffd7cd921446c017901980f8030cac183c205044162078025d70fe375bfb037bc89ac0a07c01980f10a07bf4d866b36f0c19b9d816a46cc0a93e01e215de07881e93901805d81b06d6ff23d01e20824b78b10dbcdb777db7fb6c1620a8242f0040f827c8677b7fd5bdbe3fffe7dfef7fbefefaf6ddffbd7f6777fcefdab67ec407c0106fc830c1010424284901ae03150745975b20c411c078028820c4fbf2703843c81a09204e01e420078075c30f1d981ce048fc871e29240420401b88680df8518e7272043e480100204d071839e11b97b8b701a11d10c411d08dc9b91f404078a0c411d084be48181be05a83765e1701a507041086208e05f7241a838411404083023814bd8bb031d0102088310470293d8c1120600d01681097e40c0df01541b49c3e09a41804b411d084ec7c0ac01a30190c411c0ae5a018d40c05506b8224304581541ae06d3bc13405a30428180a80a2270000390300d81cf06f5cf8d8068c11206503023a156d1ce8ff84128080df507083811c0dbe6904023a08f1cc80192480013003109c11010a051c67932048bf8a00218a026c0200f071839c1972f48701d10083a411d0872b790c403b20108a81681572f0701d10080c411d087353c12401d00d01e00b40af93a0b710083641f408e8472b00764020e002d0208784f87071fc3d00c863a09018e8400660e7867a21f07f00cc11d0664c8191c20100489a21a0758234bb2a03819486208e04500680b404d2ea03b80c86205a04697501dc0443102d022801a0758134bb1740708210c411c08a00d0168085c0a208e21a01aa218d028084e8288130055032c204055023bc9000c40aac09600a0f81e80a6be7fd7ea7f9fffe78cfd9ff839df7dce055492abcf395fd7af3f9cbdd240393832817601500a00a802004b08650282500f48b18be4e001e0e24209600c09007a0f4851e7ce480060890034015604b0041a20f4064f9cc863007e0080a419a0a7e27c99e4038260014604c80d80280e025038c1c9fd6065304b80204a01482996fe0089f00f80290418bf39381c3c1f21813007600893407a0ec86379248061c20702780204813e038c1462f2727201841812c1160581541c60bd32601490c404c0980456c01d00e413006ebcb9886206f02 else 0x6010206681b61c9c05407481440d7b7dd8ffcd6e686fcdfcbef7034c33827410e08074816d47a128036c46edfea1153e411373e09870190c011d085eedab73ffdb7f7f37edcdfe7effba7e7de7bede29be60c670478094060fd06c835c194030a05451380a80e002881bdf6eb3b7f37b4dfb4de7ee7bffa6fa6f6c7602db82417405a09003814f940a88063c67c898c43806310060a15043011c2012d85db7fe06012d826cd3b6dbf6061c0c1c1009a8466bb40c1c201048366b9b40c08600f1833c70341a0c125201300681e88621240574d34883602e0eb07482237cc83422a43105602765210988341f00ac0447b380b03b01100ac047a74e9883602e0ac07d4223da02d20d04402b01078f962c5bf0e18dc00b4034013a0591381a10c7edcedff7d2efe6f97970f40f1f3fcc7ec83998284056414015421081407a23d10c624b4434438015018e79a03406924a001c004c09643108482ba69a6db01c02841d3065ffdd308a827c8704318479666d80e00620a08329b7db740104f80c60d3bee701604f822087108b97a0b721c038c1f408f84ec92ec0240107300b411efba9bb76ef4133161006c0212c07010c61493e80b5601018048011a5edd206b00816843405105f25bb015301c8680308425f02d5804060a0e04127db00b8040a223d0424fa02d580406010404697b7481ac0205a10d014414bd8c81ac0209a027820ee40680510198183389120122c401390304b41d70624fb6c020d70288868109240070d140212807a419248120c80100d01a40ed0347f644802380a80fb083139e71f879c0f900940540150811340620ed863e327981303902507502680204211e83b4197fc4ed80a885140100c8336151f443801a80a81340833f3c8ee4e481f3c0180c680282650892141af0cf9edd642710d401a80202a85395db7ed9b40101a826805508657cd00408410401502119c92409200180d025a0e7833be5cc43444801890c610bd583f80f002a0332f6600c43807180a810ef56c8311030238c1a0510518be4e1e13878720241240d08401081d70a5cb621882380900a40427b72f815c08b60250120c411c0c66f520600d18480b408e9efa382320c541c27c047429cfea6a0e08a09f00b508df2fdee2dc118412a03b0120c411d0c4bf7903580822802a84697b9b418580825a08e844bb34c0208e02888f410f8e72580e5179200b01a00409a0fe073c2baf9e8c86301a90708e811d0be9cd3b580d0630231088238149f190700f40b407eecb36205101f00603508ebcd196831b0183ec04408e056751803402a90703fc109f320e01e80a80db24b82c641d23d047020b40b40b103c018423bcb0f1c5001913641c078073c20efde5b023006a40605a13e4296816816260f0308ef187828e089b20e207842a1173fa78034c07b019844205))))) else (if i < 35 then (if i < 29 then (if i < 26 then (if i < 24 then 0x45848090a0e306b80c4c246108b25df80a8601070014611f7f6f775febf39faebe7f9effdbfbfef7dfbcfffbafee7edbef5b7d80ac82640121381682500ec07001f0c246108b276d6fcc05760821c00aa10639258180e3162cf61805403809403d21067a0671d847c8b030322c031b0904541bf08bfafdbedeed7d7eff9e73ddf6dfbfdf735bdbcfb6feeb6fef407c01078912c2321060701848c2112f06ccf7bfdcfd3fdcfd0f59d9363dd98a1406261230810c615a4e178269034608031823814e77bfef7dbfefed7d7e39fafafce7efeedbfff7bedf7f36f5feeb6ff7c0106f826b062485090035c0f46123084517afb9920c4c11c01031814615f79cedf6fded5fd7e7f3afafcf3bfef7db7fbfdfde6fffedbadf9fdb02b106f80212809103b01c004230918422898f02b206886208e047394fbff71f6f396defc99defef15b702700bc0110903ac06c03411b441cf5fc0544188868c02051852db0811e8054063e2586580f3f9cefc005802a00aa00641c085084c3bebbf75e701910af00417a285418c32ebe05d82288f507e2bb10a50438020e805d82a7f69a06902808923d4213b1f02b2068c0643104702b9ca1c7efdf7b9ef96dffe5edfdf38537fe00815840703607e81180682468818be3df1e00e1ff474400e008a1410a0f402c03c618f3eebfc0544188868c12601028c31f61cffb9de009ea5ef83a97ba0901583e890a431037433eb9cc8420ad01510361078e58ec16c62ff3f3e60086202c015805010a04b078c3bbdf65b2188868429c01044c2b8fde7aee02e0f512320c415b0afcd1d210b004112246056829efdae6c86221ae00822442f0ae2f99214429c0107c02b41577e6c07421230470061177f3db01d08d8422603e00c2bd39ab1fe0f1b0120c4842211047833a779622104490340d508774b3ffdfcdf7e6f66ff87416e6ff305822a0e00151054829e03f0100768144318a189df0039e2981609b0403228164010850329ccf02b00c4c1a08e846400d03ae097268f8158c020fa047423200d016a0a960121a011c649200364b0088042500f10427b0080d0052063b90780150c1a06e8c80d2c0209a07d0232de01a02200526010464019240213822021406a03a015013ddebeb76f6efd1bedf8efff40057036073009419a07c036c3a6f3701304401f20c9dc060df01501b8bf7ededdb7dfd76f7fbba7bdffaffadf3e02b015405d40603408204902580df018c53d97213c06a026088842dd6cdb701306f82220cb7602610604441bd8990841120ad8312902480025a0eb024a520080096838c09d9fd4ecfd5ffbbb3fa9ddbbb3f5377fdf7fb939ce7139f39f04f3cf3c04924003341760ad509284017205a090502825b14199122cc0c210329f025b044b04c28e811c063adf7bda7fda6e1bf36bccef806ee1250428e80 else (if i < 25 then 0x60fa04c42137f2c072701b0101310879bf380dec07602380c1310ad6dedbbb4435f9fdb7c0ac05002781100440f06054392df015025a21a028823cc3765d2e9fbbf3fffdf7dfe7845e304b41c041330410040a848513e015624f63a0039f2400b1812c0f11e83d215cfd96d909cc13c0102ac216e5b701038014306f25e660773efeff09bf2c25a0e006a105805860802a89f220d4e051307823a0c0777924386043c0620f07884661073d9924800c12491900d08204f80e08427380443405a03188138108f1ceb0088f40f412484d006ac03044bb560107004820dbccd7f80a8608b00b8040a30a4f7601070087a0dd33bdf80a8e01045183c0a30a4f760107000a60dd33fa7008224c1a0548424fa02ed804060104042cf0151c020e00288235c0b4e03700c180a700863bda05d07283c249087be29818438007d204f01ec2040f0758319fdffadf7df8ff9fc79f9d7e3fcdf7c70e0871e579ebc52a5d1eae573ae2aa01500a004c0240ce00784302120f60924540333df99f00613398608a044887940ca050704336ee01014c133ad838089007d8327380822805a035dbcdf7bff7effbedbbfdefff8edafedf9ffd6bdfb9f01680ac43d019501500425010808a02ac1da0e08c6e581f680201a833758229c0202983500f40b4049fcfffe76fa3be876def672ff4fd80f4054015070411a80288407408da24ddac112e01014c1a807405a027bbc9bb7bfddfcf7ff576df7dbaffcfcffac05a02b014887a032a0ca0080942540e003e45fd3baf620a500418007c11b42939c0601a02d018c407c3938f78e48140740144200e824d0a4ee0107300a40dcbd9b7fdadf6fdbdaefc9f7b7bed73722401d01fe0ed60504801c10e79bbf02da815c06e01014c29cdf02d2819c020298424702b10c411c06f99ddbd97afef65e9c19d3f3e5f1dd9f988500ac04f14280c4c2043187610d009e047d8a003c3bbf20056a09500d0102080f48667b36d909cc1211583645dba0202841d306f65d837e808e01030c227f39ace02044885c1e308ef340c2214a0200c211ecbb60dfa0238040c309d72621880c013106b2613c134030218823811e7b9cd957d903734cc667a02104013cc2043485276c9f02b2068c2243104702afb63fdeffedddfff7bff6effffbdfde7db5ff7ffb1fdbf57ebec7fb7f04681b00b042a214e00815c0a008b02c92144220d7018c71f612e974ba5dfcfffef7be5f8005fe09683504260d0016700410a28502ac4b9a42710d30040540873d7f01f48622275008186157b63ff9ff9bedff3779bfdbdffffd7eefdd5df5f21880b902a814409a0040fa0bb02e83a81ae0858c3edcff8383be27a97a1c3a5e80b805a03103e20c50f90c4981581be08e037befffbbafebf3ff3f5fd7e7cfddf6deffbfb9bfdebdfe7f7b7dd6ff7d837c407c01 else 0x36c208098d21c98cce6e01606d082418202679c72c319fa6104506402c1c70800007e70eea0eb40016f0e776f7a29c3ad51a070c300c3011810401883d80db0a0006c03e03ed01ad6c06df6b601b7dadf80fc0403183058e3c04258142800da219018838e1038920e5160889806e0620e38330490250285220300c41c607d11b00b04a206306f2e3612000b40c60dd19ec21a016508c0c613a332c02c109818c1f498b00b03d206306003b41d1ef14fad0e8deded00000ebaaed028baeab8b424012806c839c0630a900488609453b2806c80c41c7063c1113a4c28ce6130c02c0e381883661078112474877c709244606c901806206d06bc2ab1f17af175c6eaa35d551bfd51f00000005c3ddddd7ed0010906ce80423210d07a00c61fb3645d0083b010d031044802480252850eee1cc086018838e0d47801776817741beaa0d6aee83fdbed1e000028075d576801c7e03d0083641ce03186590e0054e0803540150025a10a021924920101c0212d0718192080e1b805c241098301f20870dc06e017080492118e8801fbe79003801600ac04e10407a43124801b80419a0f40372cfb967fffbdcb3effaf5cb3f6bfd51ce73879e79e07f3c900924003341940bb01501e809610c60583c425b14fec78f8decaee9027093841c0243413e42a7b36643130401560ddbf8000ee0aaa0aaaa82a800000000aaa0aaa000903f00c40f9084de05a2189836c0408389cc0bcc206c0801288e881a1020534e05111d180411c08492f00e1840b0108042500e3841cf66481980c64924b19b01080847a0e9842d043460d075818f18012430e7c9206b01580441a0f10950313dd8044f802983126fe8152c02e0102889f014b3c05470083a40a2083cff4418f7c3b9fc07e407a02c014a05803d40182303e2213e5cbffe970f96def2675d2fdb81222500f70040f827c11b4392efc05430089f00a3084f6a0113e00a60c71e5861d98bfcfc03e21880b005201100f012c2190e39f6607981248614900d105081043406fc2927d0169c02431082020c4fdfc8ee043c3e1609604d01d80360320803ae1e507d40b7e66e9f3ff8158c10c07a02580dc0408e87247c0ac0df04741a99a3f815a808106308023815d7cd3c03aa023808c2209885272c060df07581e40560474137f4c06f701b8041310848b8b00e3c380ec0f06703ae136b60203ea09980de61be4c0733018a05d80ec0406fc299bb5f7b301d808e037010262158f3588a022a0c68325decc0470184181310875f6fef6df6edffb77eef7db5ff3ef7ec97f5fedfffdb3fd808bc05c01082037cc2012a07d12141aea0e8b49d970082681f50666b76602380c131064bb4e0107484120d3fcec276defe8e3efbf5ff7e719e9e02c00a480e036c01082041822e8468967577b3c0106f88d821c07b0532ebd3011c)) else (if i < 27 then 0x80804f095418e2e49247f8008c81880581c60d78446b841280804f43d021e24821916242200014062086076021ea73fb049021a02c0d2843f84d80b038c1ed060f10f1272103893f000669a06203170801b41cf0a071130224f80126818a8041fc0e78403888804f800e49a06280a071839e1050438a3c10e011d9c1010a036846610b80fb3c61c101616095384902c0d208cc28b83809e4384301259c1080a085046610e018d9b02c9942da84e06212a83141039c210092ce1003684660c00aa4aee2802bfc56e004042aee795dc6e780800036806210102301b614e03199c0c942da05a06212483023199f14c6d1a6f403031085418a7f08071043802876d0084280da11984019cc80c4235c200e3069418c5c183d9f60e08c0b0b3849c20816070046617b88cb660acb68c3604f818a1ea0dde179fd6e1b609bada30db8241a40f681881b6145040e27843823b382021406d08cc21707831f62c361c10c5859c1c20540b039c2330aafc1eaa175cffabfaa2b57d7f8d6ed1e3c005f0ebbbaef80000012a06c805c00a0d3d0083fc248031890a019b18438d9d8ed03140b04660c2e0c7918704161670720581ce1198438193181464cb284e0621018301f18c1b33b8a1869802e816818839e11d4f27fcdbefb76ed3c33f6c58df9b8241b2e03d00839c1a5031870b83078b0704161670720581ce119840895e3801092c18803f844a031071c2003bdbc006776ddb8089001fcaaa281dededf1b92800000013c0611507180c50790dd30a01609540c60fa436016036c0c60c638522025224a0748120310718274c3601650840c60dd5e58da0f002c0e3818c200f80178f7171ddb853fdad6800005b8eef7776851b5fd7ea8d08e03fb41800409404801c603188090092772004e4838c063047991fc23281b818c1f4c2c02c128818c1ba4e7ac240016036c0c613d338dac02ce03071c0c6107456d03b0310424193c03a74009604bee4c0fed0081b60620e3854802920024a483379c181fca0c018838e11ff1f801402fbbe0fabdde1fcf5bd77706d6edc7e00000aed02b5ad01150236804255612071846406310908f1bb6e6c8dfe6fb4cdb819c07001078834a0630c0e2a66306c5d2e06206d091c1a4713e6f9b9be6a4b70881b606306387063c7b160c1b0b0b03d084c1e20e08410398d893184e002107082419c04c6366b98c0981b60160f18300003dc03b80dda035a01ed755b806f6ed6d6d037eaab420811e08383c40630a5211e3fb6edc28cd9b99b701c0041e2031818c29f80227cf03ce1d884dc2411e06a01e01a70c045d633019b2dec1ed00181883f2100b83fade6dd6b96b0499c12e0307040c40db0a909f379b776f32666da66e002e12701834a0630a38701ef8f160c10b08f01e04260f10704281f05b81fab9b75acd303800f10310 else (if i < 28 then 0xa0c503b01604903b417c57765b109c0f021a092844ed3281d80b02481da09d1ad980c21a03c833da6902681d07002481166fcc0c06d8204336d0254406d09041174d80901607741f45b660209040f20cf19d0da041a4488004c81207741883b01463d8fef87dfbfc7bfecf871470007047b402d40a5826c060ff036a0290620d98979636d88740620938379636db08d70620d98345f766da0f00620fe833a7ff2c1fc0e940b824e11e4d920303f812602d046bff07f81e2090f96fdb7bdb9a0d9d72dfcc1b3609402580c1ce0d2418c39e9cbf838e02d60311b20c615f3219ed97e7bb82d9fc31ff981b208621b101f425a0112120c621cff660806cc135ff824c0f10478e8a28a21c00458801300e82481a70838f28018977c0b016006009847021b0a317e6739e3d9c11f0200a783f81c606200b20f2c20038069c3b8eb3bd53e11ec0080c42320e3852cb2c65783c41280ee069821431945141c3200b162330020e3069c1ae5c44402a4303002c831071c18e1e1f160e08b0b0720104260e708cc2870888394b02469806d0620e38327ddcbd00c0041b602a842f5687a03d00a80cbf6b2061c0041a40530408e608c1780d031d00842541a0ed0507fcf30f804084a902ce12d0084641a50c117c0f04e0639c12e08818a83c1db0a78bb366c106652d42700181884aa102263709a03820254a0d06b8208accc7006f4b818a0580da1248403b367c490480db031086c1846e202e06062e02941e0ed04076f200605c21a0107a034a10b0e4f3ec58720c7ec188465c2100140b03d01c10c78bb360a8cd0284e003031084c21c7b30db0919a0036c0c41e90611cc8784c6382340211950783b0141fe5230f00b0c4232816d0084341a50a38fb3661c20d89400502d03108cc2213a4c79006102d001086834e10076f99e2a560086e80600303107b428fe0f671d997c7e4ac003a818a05a00210dc05839e1d0e4ff9161c83030119800a05821a0d3851c64f21848bf8a00020c4807a01006838c1ce0c7c4930389e66000027608b01410009a0e706770403a831042019bb5003a0fa9068168102be7151c3c0033003140b58400da0d7853a5ec1c7a01906813e11705c0741240d7830e211820c3e39001062031b0801b41ce0a38cc90245fc50f00020c480da01024038c1ce0c78e72580949002c06028082039e1172f41c0744020e90474239fe20580ec105c965c51e00420580da0fe06bc214c20920f02781ae0e03a20506bc1871c3c58091f8a00106320100783f81cf0bc50f60fe02781b60c71992408bf14001063a0102403f81ce0a71992408900001301384101ce08b2e0b80e841006208e041c592498f0034102c80b036838c1ae0bc81a20506c835e0c38c310807c500083120400cc1c60e705ea11d838c06608e836a11c2086030198238113a6e else 0xca07002500cf6881650882f81280878e8a2880706088b1623401300e82481c10838f0960625c3033ec58054008009840c2410a311c7678f67047c08633f6147b03009300b20f2c2003808ac3143194500e0c0a162c46b0020e30704194319450070c0a162c46b0020e3070418e0e3194514007850b2c23580100b038c1c108f3cbbcbf982320e006cc194319451401c18162d11b0020e307041974c319451403898c0a04680e01c60e083038c694514038f06094162f00201b049038210f8cf4810690e910009902480c01d41883b018712c32c0f1d9fc005580b00c82142070a5fa7fe6a6f3d41d03899f5f1dcf42c05e80541fe83c03d41e90630efaec845412483140e823781ea07dcb9320a03a503a105843e258b05b1b9c7b300013403602c10a0f18534d5d062115056825011e58db621d01882520cd75680b108415a0940459fe608036c12cff30181b60b4b183680f00d40603b36368079a2027c0130141288401d9a025101b42410423d9b1f2b340d606d818842a0c430f3b1f60818fd8ec009ee1280221e84261198611766c1337863027c0120621038475f0ddb9b585bb406301884a206206d84128e7840cc010da21e041038e112d8478058833037e244862526810200620e3834b610701620cc0cee22483125e8086c408018838e13a4da0581c70168349ac0d086d82753509405902d07d1a059423016832c68080f105181a5ee740870180b106708903d00a0ce098be21fc4387a445f80038c062219d00a8041a60ec8776d47b03120a834c254077052b65dc0c42480d304a023f5160d308602520dffdd160d304940c603b087752f703106982b41290878d1a03a0d2244002640803ba0c41d80a3f3f85207d9c033cf7011c026808029e0282501208718bfecf8fbeff1fb1fc3c4ee3c10601e0e2dc05c814b0458081fe80a41880c41b3124de6a06681d018a0c410e720c307d024c0cf2db07f84a00f10673906183801260618f8f3dc63f87649fb0109e02900812809002182330e5d67d838d02c0e0833c74514510e0808b000980741c60d3843c6400a4e04013c05801823810d05188e73cf7e608f81070a781803f005907960e030045619ea3736fe11e109e00412411c852f65903b01604a8248101e393f0f8386408e084d0080f6b09034e19726ef08f405902c0e38459387835103a2010188238141c3244039ea581234f00201b418838e10f19d203a0d2244002642700ea0c41d80a3cf9401ece48c3801c01ec0504a021b0a3e3f625f7f1621e3b8f000f0716e8140070055014831b0703661dd7576d84a01260318334f990704550620930434d3c2020e907c024c10aed01690702d0126081e0c64339d1201010d80a094423a6e02d20e40b418f9f94007b372441c03a009a023014120086c33ae9736c24009306941a3b47e))) else (if i < 32 then (if i < 30 then 0x75d56db3ec0b240b0480232101078e84080e0ee01884a01ce0e38b769b41350180a906e6f9d280c05430703ee113e4a0301501d5069f4dd0180a880783f306064719c0363634054078a8401c708906066618376766cd81b2016071c1bb4bc116404043183a11bc0ca38e06c1a20203c42080e3844b77fc60c3603901813408b852fb3e20e704d022e0d3e6d080c05608241bcc0328e064e00d8d83402b03c54200e38417b2f80ff9b9242430043101940a0d930303ee182f265f5336d59d9ffed5fbb72555ad07f26ccc0db6673fc6059b3b20c104075038c06c40610303ec1e20d9893d6034c0a8058045821c08809193403203038c1cf07b95e60f1043413d5b673fdff6fbf6db6dbfffedb6db6c18609e04d021a06c236504d01d4114068a1c3d051832d2dd019406236082427354360382181170661a29244065823078835e09c99021840101280f80c03b4110b4e0080b00c606149248007809a031835c0d27b0d218813c13406d044100e0330202500106204d00cc1ce0611b8810a00604c0100f40e7041b880a01813404607839c107c0889f8707b0015a208e03700510a0e38674d4e8080f104710c41007889f0e0b00ad80230040f80e385101933e1077800ad11b701b82407a0718300e784f841b00ad604c01106cc0d0718316486207a0308180bc70843b01812c0e036838e1176982406d030c1bac01760881b60c06f114861d0604b01807010b07182801e38362967606702781d40a078c21540a218810e584028a0210101e20d704ca008404a050181e804206d8101c008d60904000f81401c606e9a9d01020808e2188200f2227c3980056c011802885071c2fa736009c0103090c61097dc0102a81860dd340f30380f5063db243103081b60f280210128140604700f003056b01c0080e38404203c714260460ef813c0e036838e101f080711c7e0781360568013803c12607038e197bfa8016bd5400005d755145bef5bed1a3a000000000000611501b00c421006d865afeffaf5005aafc007005dddd745c2df7b5a2df39dc000000c0000015004f80c1c000e01883380db10b7befebed005bdf6da0000baeea8e8b7a85e14000000000005409a0d301882d80db0cbf8be201c3d3f50c5000fe0188897402a0108a838e1d8afc40387a50f8a0086d20ce8054020fa071c31f1a4683c0d507488004c81040601e20c41c60c3c40b32cdb801f3700a802780a04284a214f7b9dff8f783bff9bfed87ca2f97e99fdfbfbfd1f1c1d819c02eb04580c1ff07840500540da831436c592fa11440580ee831043c70ec1d9a009401304281b42410873906503e8128067c4b0c2cdcf003802780bc05021421b0af2c6db10e80c41290669f321108aa0c412808e7f980a07904c7e208387a23140043da0150083801d90ab6f20260e0049407410be4 else (if i < 31 then 0xa05446ede063036c12fbb7bffb6dbedfd627edacd6efb77b6dfeddadc6f6dfb7018780fc0408603b10c41e20d920544b664cfdb6ccb7bdbfcb7b77f672ddbb619e7f647ce3e921adb67ed6b5b2f986cf6706de0313700c081427903690c41c711b9b80c11d05feb79b6ddcd191869f8fecdf04d01580a004f704b80c1e140a881863687ec1e0f863bfb02c3034c4dc016502f005c1c0e3876fb65b6c0c6c07e00c1fbf9ee0606bc135b76d83d9c1dc018366db6f6073f0040c707bef031f0060b77309b811d046af6cd9b3183b6e36db04f030941140a840df99ccc11ff89e40f50479604f605c10c9791111830104dc0d7821c5f393300f21300413c01012c1f007c0e3061e39cbe4a0382c901007602025839c1c70a2033117919c0044a12903683c4100079f1c52387fe006104e04891b81d40a078c33a5de73442802c01041b610ac25400a240002039c1c6064f9980c042806d831d7cc147602a06826a1027313081160150901e01c608382c6422c6c005502c1e306d1f6e036a11036c188310cf39cfb0cdbc40b08203c48140e3850e8a494310140a078835e0cee3f2e7adcf2a7ff443fe652f55e38773876161fe7f0f614bed57caecf825412408c840400808e08b50282080ee8a45f04701ea815066bdfe5b80dc02a80211920dc2bb17eb80d906c1ae0608468f6c2020fc03d41b46df501b07701b60db8f5b01b50402380db08f50fdb6db377db9b609ea05a82422ca08a05430873d817e07a082410f07452491f1008c01b205c0281e20d7851e3b1ff13fb11f81c1f2c171061e3924120854428205e0088180620d3071c40cfe763a3bc3c3e3f2434006360390041e244e307038e1c63bc9c9207090020240f00e7071c23dd137805e05406bc187a49204c02490000809a06bc19d52ecc0c0d704d41a780e038a6d1842128c036e09502820908109cc230210501942403e0718204e6146040501942403e07182016289fb11e0703ec42e00c078815140a03103b038e1836f1c7181b0566fc27913710101c7083b62f8b7dec5bdbcc33e78ddc3490b35ad6cb2ddc5afd6b2506cf9e06dfc055b0709e44dc031069838e1c27308c204140750901e01c60818fc73e79e07f6116e6f818640708203c413c08b071c3e37f04301560bcbdc040868237addb60d3061d01c1350818742908d16c5018432104832dcfb604a280c09a11b42060b1e1c3e3fcccc02b0150432016a0303c61b6efe80c120822fb6b501821c236831070007e02c680ca05071c2043986c3f366c022e80ca02078c200c7c7f18787071fb058b1bc018302e80e10407883641c70eba3fdbc204431080834c8330a5d6e80c0ee069c1f9f603d01a08345249019600f106bc11f627838e042483301602fa03284580e119852cef1fae69d72777527ffad067f3fcbc61bff3fe7c29 else 0xc017609480f8030a792747fbdc5e6dbbee610db6e04f004c220eb06f88da1877d75db7c3b0b1b6f7adb5bfefdb7ffdb08203c5099c01082839cc230e2d15c20804f03d4180e586586f6d8603480d824104845105bd0d3b43459db0012b07681e820909a520300bb0340da2b018168082061cd83ea004014560360204981ae0af60823012407c0104d2406e0260681a06f37fe6302781ea085d715efe104602037c11c60e8501efa13a18eeab0c09901b03446c104857ac3fdac07901f004208236857e725cdf371db6bd3119b6c60ee04f0041e40d711b433fba36c80c2080ed11b423860e90191e00c0925c30005208400842823209e937180b0c0503100f8238149ed407803818c0b4085d33bd98180b503100f81c81792d4a03d01011c030042ed018e80e04102d02096c01016018c0c93f804a0200b00c60892df009404031a84010487c02102c0c6065da2063a0381601ae08e7e32480e20502c00c41ae0bfa9df4ef46407a02700441807d818c332540605a02081861c0925e0000b2141100540204282320a37df24950738fd551e1ef3c20ff3f0b0776bae5dce2d6ab95ef3fb3a0c3043284000840b90604981dd1070c81001404501a834232085eb6fb82680fb804019101e15cadbf880e04f21880c21027cb2800074501100810406bc23f3b2de063c02501009ea10852c925000743008404078835c101e2e4588a2802074102c0660f106bc238541e81621881ac84824200002838c1ce07d13640b804082014011ce32fc1e3f806f181ec0d750350101cf0a0f18eeff3c7e3e005001fd9940c7009a03701282680808e073c4070f860820115011406104073c212480597000c0720084ac1ce08565028862041492401809a031835c0c97cd501c0b44310820209704d02380c606492033060583381da066bdffafd4ff9eff3f9551cef7b9c275d72ee33f7f9fc21c487c38aaf95cebe201500a048021a00e028812d816126076c50f9f9e4090c13900250051812c0660083741fc0ef2bb108c01f8020be0148283c992187008080f80220d218846415c7009402c036818c4ef9c81c3c241209600a13407c0ec8533edd030f80207f21880a41597401c04a80a40c9b7f00416803e014823d1847500701483b411aed101005801ca05020c5cb9021840426b02c0c60ed0442700b1816063030a493800c028818c1ae067364703c67c1365029c02e12707038e14cfc11cb873fda8140f1826b6ddb0853847803067ce3bef99fa6cca7b7f96f4fece5bb70679fd97cdb67ed6b5b26ccb6deddb341b3d9c6cde0313700c081427903690c41c7119605c0a5d9112181800c2137035e0cb79b6e6f10c4666fc3736d8df014009ee12707302c8630c3eef1b2f770bffbba15ebfa15ebd5018003b8d976eeefd7b40aed7548e84982140e7002047c1ec0f1)) else (if i < 33 then 0x4047439f27838c0da04f83f71a8c12a0870082381e20a109e481c21b000904580980204d07382a739e87f04d018c08a61204742f9cd4a08701380411c0f10509e411843b80120960082141cf08f2098126ef82680b4e0103e9824142714801b00482180204d073823b209a602417c3e73b8031ef36369503130100f206303742b4b8041ca07d031f3b9000a0f31818d80d20860783ce154cf769f04f0119c04a1004742a9dcf6b0100f21040474216e09a70081f60cf3f3b9ee5b6315fc0fbec07d031826808a01e606a0da1df2b2904284024c0e5045338278092212047021f3e5dedfebfe26df97e6ddfcdffdacdbb67b3db6c19406e022f007021209078825423e6128a539cf6b0100dc0f10474216e09a70081f60cfcbbfaff6f0ae6db77dffdb5b6f6ffb6d832813406e0230827803c0e050847cc25147afbac48c017e00842843d0a9a3f8279808612047421be70630268c12e0103e82a99cf04f380809008e84530eb602038c11d0658269c0207d0339ff7ef7bfddf3736fff7dbfb36a81f80c6062605c82503d208023302821b143fbdeed674dbf36df65d9ff69bed8733605c827c060ed904039422cc0a88e97612a40f303e0fa4720800b83ae0d4f767c13cc04701009811d0aff26e7adc82180e609602016a143e77311e2a000698904780d80811f06bc29dc7c1e03c52109006d5046c0808258161208519d996e9ceeee92dd5afa7af55d41cdfbfcfc81cece7f2c0c5b67c918c12a0738490215a08094047c1af10b260201f41ca06b1e10870181f581e08ef50db6ecdb67cc60e5904830a410c0a857be64efc13d209504301dc0408e86ecb637209102835e0fef3476cc13208602380c11d0a636ed6b7e09a102835c0c708cb704d38040fb06cdf2c12ac07061c1a6f3ac204b01c1860e5847efeb39bfdff7db6eb5b67b7ff6db36db5ffb6db061826906c2361048817807c0102303cc1af16fe4da07a411c0107b4279721b6208701a0d822d08fdfd73cdadfeebfedeb6cfbff6d9b6db6db6db061891846c208102f00608c836096035e2bd33745410e0202303c411c0a3c77c8bb0145c9000809b01803c1fc0e7857af9a867218c8430080790788238187b4edaff804301f0040f206385e4b2b580c86208e0110205c933e50000890620102080d7848404f03d0129c677e0100f206306bc20423bc4c0b85000604c8400f40e7846adf9dde3e811b008e0203cc84020808e0709cc29861401603067103c1ce087bd2efdf71f70edb7fa6437edb80209e02308201e40d711b439e7f9d5f603cb012c06e0204704121807f865862b1edb0062603480d81a1048527ee12b603c80c43d08ff24eb73fbe3f26dbdee610db60318119411c02e0084981be236881e581b980805a3088203f1e50a11dd3edb003cb01a406c010230412197bfd843 else (if i < 34 then 0xf6eeb00a78020df02808a010a0ee06b80c4c2460e8b19ff3f78e800eeff1fd87d23d0018d06202c2049018c1240f30703c624639281073c05805804809303b61067b92739203c09000bec240df069c2276b683404d014e0d9fcb376c0c09a418015210f65930311201a602c040f19c8ec02c160804093039c2330865bbf038c82cc01043c234b84837cc0c055047023e7dfbddeae1eafddeb6efeeff6ecf7fdad80c2054e00819840c10608b1848c1d1218f8c7238381efd824740542037004c2460e071c31716079218823a0c7c73de0a60e01a7f00a402a12803c484021a101071e3b11efc41f13b8900081440980540ed60e06f432f769b05a01e413447884f69ae10a70041e20b441882a7f69b03ca050134478842f66d0680b404d41b7b936826ac1c83005ac207c19c78e6891e40204064200f609442f8b9a606e00a0c416b08cf98020f7822f71606e30190c411d0831d1fe397e28f801e591100042a206102f0040f2120071c38f3fca007e63bbf9220f807443101680a402880109004362078ec7f7f8f8f380897e3eff981c0015a056c1280407d00500dc83106ec4a3bffafbbcdf8377009c0109010c442e09a876bcd0b03702681da24604477febd9fbe09b10f601380210d10b826a1de7c98411062214076822e303718181af063e91f9eb7b6ee6da2037c0910340db8020f8123433bfbf2df784341ba236c02180f802217872f66d90680a704d41b3dd6db921802a106009a8407830fe670452380a0804077039c2410be1674c0d205e00a0c41500aebf015006d825de59ba06e20682680a5085a3810411d044ec0103180a80c6204e070823c7902c1040f0124843a031b0120ba6e8134478016419fb2e4c1dc01031c0c40580a5a7cf0040320d310c821f4dcb20a700606206301602a5eec0f1a0270040580d305e9ba09a23c00b20dc980b1808063831f1c3c0c4c0104081a80880490840e42320dc532cc0603123c01c8109d8020d301581975bbd80e43401800aa1018e7912010a0002e960901804101db0813c27106000804b015806420119052490f0e180a0850083341db084920483200200d01a40ed032be224009c0fa02a043e27259c903ce00142140142502141af0a4efb74e01006309580aa108c7792408800022400d02080e7842f521e80f402a0338c0924c1c002502a01010a08c8225fcc058826a0080a804e0a7b2405482403d284010cbeec804500418605384699ea00826806c02c0418e4e47842e4800040203d038c1cf085d2d886208e024029010fbe3f9cee0013d2fcbd9bd8f9c497a02e40220201a607941881ba1c97d8c820c2406302d027dc9bccba842c0410482320c411c0c5eed8818d4200f1022816814bdbb941a03c408a02a846e7be89741810c013406d04742ff727dde3e7e7ac059005218c8304128 else 0x101f506cc07dce1dbf1ef3012406360360201b80c60df867f99ba7bed981a808c04b01b8080b50c48efc20804106f823a11cb32ffa808c0470184180b41040674fcd3dffe0f10375011808e02308816a1c9d60306f81680d7329eb7602038c1f408e8427b01837c054064dcfbb028208430047422f74fa7302d30100e4431840f7bf07720107c26218d011809603073845a1995c1c604f03d302810bb02781058150631fcfb1d001dffcfc7a46800d303180b081240620798381e3105140c77078c83e014b00640a128076c2bc7dfceb3018c862609e00830c1350c59dfb35bc8141e20d304ac23c719fec7e8ef00f9fd8474341800c6054e04f00442e07c307038e200c63d8b8fc4f8b1c5c6e07803c406260e218838e1509ae0d3e0080b00c609f9f39c623c78246860016101c1e2406307038e1841e7d8b83082c015160e902818c2330a18f0c471c1f6093405420303c4c1c0e3851e3b1fc5f10032c220c1c0854428206018034c1c70c310270384791cb0084100f0124840631fb0ee1417f1e786e07c302ec1380404984101e20e3870cf83c4838202012c07601078846614079023862507841024906038642c920080640d0718498118b8f8801a40601e2219069838e10c3c7bce3bbb8007c7f5eb8635eba29f1af5d1540c00000001e0101881e40dc0d3031c333b5834c89007d83374063701016a0c7cfd1e28e21dd258007900ad02681a219082430e7fb1df107857f3f363003700b005621940b009681e0f1885cbfdbc06ea0082f8134236850637ec771417c79e370112181605208203c41c70c9f32a0f06990c417408b581a609a05601a80c605a0218c0e4e5f81e010fa010804a00a8460861198669b901e413440f0390234dc81b813440d03402139c0606302d01d6023886204f99ddbd97aff7b3f3833bf2fe9f2f8eec885040c050027893806260e218c41450783880d805aa01a0384a01da0ac7f5b7f6c830c86203004d423d9adc1bf407700815210fbac3acc040ed01802a042e0a996f40704a885006008f66b706fd01dc0205484d658486203004781bcffce653ec0dcca735c6402d10b881810c60e21a4300c4c7cf1f38e7f673c580603f0402ed01c25047807680c01af0e0e3e4fd80582f0028583880e804073846619a5c2406060602a823813dee73654ccc1b9b24622060279838869084ff25984486208e8318e8bc7a20387cb088061c0108200c42400e38533be03f018d8020538419fe17cf83c2bf8079cefc04721880a425007e029a03c24111b6fec04031c11f693fecfcef77f7fef7f3710ff11f66cfcdd841ba02e402011806c02bb08837c0628318a3becda0d086881304d4231f77db3830d06043004d4232ed7827980e0c3045c217160df218823a0defb7fddd7f5f9fcfd7d7eff7ebbedbdffbeeff67cf7bfe7ff)))) else (if i < 41 then (if i < 38 then (if i < 36 then 0x3612300d046d0c77aec2221150080a61078e50891bfe7e007c43101600a402801140084b021a103c7f8840626e2003106080500f6831b08837c184766fccf98611e538ccde3610e0c20a905086340b205038e1871924805af40038a03d02880212b073828bac9e0f1018813c0db087102606281d80486820f09002324809000409082039c0c79f62c41ce62c60068013a0584a41e30a59edc0d017c09a830c488010007aa0538242080ed04031622004142243008c81ad7f0b77e1ead7f0ad0f5dde855d575afc2ffaaf543ebbbe9d77d000002d5424a0e02d04ac208120a05440319e3ce3839f898cc37841060204101e340b071c2a18ec9ec9e88932fb460e009509580c28160f18518c3e639c417e3ccc37022816e0970304100da0e3866bd9b6708826a0610678e0684181a4a402600d03c10c42480ae9ad083602e0ac0188227a07d0268158074070167fb9dd2a1e1f337b4c3d609602034c0f206e218c3725a8dc0540404710c411406302d01502c0648862c0a0259240c800011603c839c0d2df3c033187404101e2c04031838e142792000c8a0230101e20d7041c4fc92f0f00390ca0203098140e306bc282c8889000e860550101e20d7041d2c889800301018406306b8201248c0130042141190302cb201240044b207b21884640cf8819e4c380061002920360081e40401190626de6f00421407b016020134c1c849001e0081ec862119041805e49c9201802458ee3c0602060510c42320aee6fff74d7f7fae9afdd55f5d55c79fbcf3c9c67f73fce583e6e49f0778f3ef248002204a00ec03b031b02824010b06bc484619c000a7015ec0408cc186304470080e010100410232083c77669f8d9a01b6431016401021610a850841b6c00145010a60504640c6612404000a21a04640c07efc2a85d7fe8555685df5ddf42aaff55f685ded777a77a018030128802023c11c104090302a1c0e2209a284e0080ee218849010230773c0141c04e036020466103e1e2c3b0c1cd0b000bdc1c05007384661446c2003845814119031fd692ba4abb81fbfca7d553b8e1dce13b03f3c2c3a7ded7af2fb9e085001024006307b302824c0ee882f71606e304901011d083f10f84ccf0380060afe0850028209c04700608602208c8427c80c602ab011034107107cf14784003b8f6803820c83001a119853f65c984780206381880b0149eccd80a81a0e90340235cc80dc09a20681a010b96c04b01018e0c3c78f8082001c713280402090641042330ac69cfe011406039a0681a014b924b0c00f42814404061038c1ae0a118e4100280ec0220d08c824013c0da04bae1adf0dad98318140068128036c23e5b2846803016831cfb303cc349200c9280c082840621a037e1493e80b4e01218841010639245f00f1f9c280f603600901819c0eb86e35704d30 else (if i < 37 then 0x40f83059f4c071184080230040f822507182872be80f18e18604b00407520c071c29ba218c0138020a40401e47e1c643005080230042520ec8500bdf5f02d97f896310c444a06d8368c01044a08403e4dc01180740a83f74b085200940a202427cbd3a1819a0014200840481c838e1407913f0e60c013500460082141d90add303a009c0102882793b5004e0090c4209099401080940a030be3f0a71c00790384cc070027004252225071c30a38801cd83c6380d81f20c071c20f13d8b8707c7e2cc60c072008094c2007c076431e324090e0990005100203608e83f815da038043c0e20371c06c01601b40daa0381b608237102042826c02078071820b8f6b70d766b14240e008081b610786b6f86f66b6038023206d83d6a0ca00c16941940182e00cc350b336602e58041e307a506500608066cd6ed8045d02c0db06f96a0c701d0060c0157042408e3cec507df079f9218301c1e203c01284301d90c78ce492018480002880903003d81c60a75e41ae0d310c81880cc0bc98e0022509481b41e208b8bf9d310a01b00a806d841d1018126a0c03084c840108280c03907181851c80300ca0328301c70611b88020141340601f038c10237080810282680e0780718213dcb416c9835680c27c11b418f067107c928c054203380c86c0ec856941940610c81943903c030117406506038e13a6219506501a0c03c18604be4e746302e80e0d907883b215a721880594184190422c12410081a0303a823206d283280c054034d50180a827c032dd403d0181d4054047803381b2366fb66075015046c031078c2b80331b034b7b303a98160d9076420b9f2ac303080ca0513e03661004679267226c608da0620f107542164901000448082039c0c3079392010f01f809c0243408c828b208e183805c24101832400e0e0106284340d4d7dc67ffe719f7f0aa93aeb9cbb8cfdfc09c481e7155e795d7883342400780258145816116086c400f900e1ae03700b838249088a20c0f431c06001480b42500ed053d8ffc7bf01f0a3b004101e2e01709383a8080e3874bd9b3fc13443101818180c70a3c74cbe4e1c522668fe1e003c90280dc41b071c28f8b3039c3bdf998678c92a03120310c40dc06306fc33b5f5fbfd777d7b75dfebdaaf400000076abaa05faf6abaa0a0000001e80d804a06e086037c0630e38c924863c01407b0110342580d70557cf3703c81ba808c0430881681882e5fcbd90c0a078891a0c384bc870c02160202404102330839f62f14400cb8620f07160208200801d20e3853c604990c3809602b00883420811905200450003f1451fc5147731451df6e00000f1451ddddee0080027e0103183a408c079871e7fa22f0fc3bafe63ec001e4058816a03005280304608244171606e218823a0de794eefbc7dcf2dbff930f3bee2bb7004230 else 0xc218c293cecfc0c243150088d816b0affbdf6d36236418a050429603e00c33ef764868813406580c1490acf6eb10c3419603078c23a6bc1d4606e0081510620ae93dff366dfcff7df9b36cd9b6fffffb07883a80a843611b20c48624082038143419163cfd1e8e021df468e880018700404a47811283c61878f9ec741df83e7f1d23000b0c1003c0129108c1c0ec871c79405c43c60f9283007001408e840617e2bcec10a60338020c4078c2bdd966c1a621404ac187e0f3fa3d1c10efa351c40203040bc0101291e044a0f187f1319ec5c4051c5c60006260e21883c610acf9e0080e847402c047ce71881ff89180831016105880c60e078c31bd960083b082d060f0c4383e712602a1018c1060e076429e3002643821100a200406c08d09502b49f600829007402c0459afc01069886403208d27d80227c01d00b010b4fdcc07c0105280e40580ad27d8020a401d00b011a3d80c30180b08f008f900b0c0cc0481c822824c0b0044d02d029141a061398430a01a0260820341ce0839424e0ef508819ce01052412e70b91adb5edf6ddbfdb05201f580212207ac83219d64e8081de039834d052021209ba07a88958080f1045f3608480b803063a211805501b40c82900da04077c29bc06ff2cddb2660f5923780c12a084036c33b7202607c10b1e0aa602091810808b1e10f70181f581e0801e7f59c8480db046f93a11412368081de04a052d05201b608dfd6095112b01e40508b7cdb6e0390170060ddacd6f83c412a225831676418c0712301b410f130201c1899483180303901d042414719c9301e08c86008094075039071829bb521883360da029041c67206478264300404a03a81c83f815f2802610a00960da08ed007202c83681bb4403901641b40cae110c05810120720e3831c672f2601848180602501e40e41c60a4dbf8020b401f00a411da00e405906d033af211708a88940cf5dec822e044112c18f3680e225036c1a781c00ac8ec8460a408dc0ea0503c6102132400210a0380e41c60633200108024a0f81c606138a60080c280ea0e024038c10973877db2db2d9ec282140c02508d891a14782639c1f334c0fa409078c8481d90a011e460e3938c626d0603c41080ec84e98059419407837c484e3980007b0111418a10025046614e480e10f03e81a3b5e0f320381f41e309e01309b38d99b2607d018c8481e308805bd82dbcb04203b208ac106225824f3a03829044b07d3112a83280f063ba436db37e1808b506502448d09d3112a83080f061727cbf53cf7578e2e712b56b503936181d9e3fb18f9b756deecd66079902448c10f50603c41df0e3899c900798640e0080940fe07c071828f1df2480382c940809b01803c1ec0e38566eab0180a681e0fa0478f3303600b00db07d966404e0080c20dc6c06051a0781bc5d80c149)) else (if i < 39 then 0x1c84641062044e60783e08e040dc0100f8078086119061e20713bef0e0012ec1160303d00e42330a5a7dc0105300e405808cf590180a4016103c113580c04201f40d9eb1406029005840f04111c0f0006cb01d00c044119843c40ce4c18004802960303d00e42320af32c90210780f101602169f700414c03901602169f3c0100f038043c08d26f360083c40dc02c04a00b10da04109c0840004ca020104233064f9ae509603280802c04202a4beec1e4c0f07880b010230e100002bc028282681004108c82a72683005886d0309822080140403d04640c9e810839016019dc79185f36cda006202c20428481e30ae8a0c01610400c9739edc32db0f96ca0c50480781cc236853b8f8cf06fcb4ac006202c701902086c0f186753506107843d07400b10da043c5d19322666d861202ca0203c50db08d390c502ca0c20f0271a02ca04380d07208c76bf078d02080e0548409848200b0081e823206f786b7d86d6c33073030c0db07ad41940182d2832803047c40099e1c2622832c10a0111b01b42540c4f760106980a60c9eec0227c10cc1831f8f61603fc7c7386003c6418c0bb04824ec200ec8700248e1894020f1095418e7d1e223a1b401010e81201ea0088642180dcf32c14903c10c833c117d608641780a481e02031f7ec503b9e2461a12d06302c1e210c076431e6a40b405022010c043f1f02724f038042d41800ca04503c1d4119867cca204829207802c0469ba80609f081e02c047cca40805240f0058085ebee7425cd4ab4d09274a0c106089486827c852813ec1e023b9410a01a0384502030be9d7598428122061812a1392c42940704a80c01164fd01d0da054112822f49729d819949d3910288944f84348473dad90c4429a0c05242166fa03a1b40a906031cc488b189c5800f0a03c0e64f80d784cfe60203c60871e50e3d83e01a7f00a500204200a21182030cb6e843c0b405220f0117350260a403e41b5702d414927c832e40a06d824bce3cfa6f9b7767fa200a443690600f01f0246863f73c3dd176def96b8e1a206e00831c1be2361234327cc0d205700c180f3f0a3bbfd0fb19fc054028b02480d20560090d81d110e7fcb0271064419c0110cc2ae40ae01827486f9fafedb77bffbacb3fd81500a223620cb02580209303e483227ac214902b0120ced20cb0438022190403680af81a75b76ffd6300a403a60590d825206d8603a0fe6d36cf675860de424c0b06cc9f00db0ba520520cb03c0cf00318a0031dc840c217082b02c2400ae8b9028894109063e581e60e02a018fa60270040a906fc3a9bdf6db6d9bfb6c13405421b08d9810c049064380fdfb320d9036c12c1272057008180f381d8bf0600a920502630042190a3c7cf61747f071f923002d016003004a40f08603b21cfd3d9ae7539d1e0b9d74c200a00c4885a else (if i < 40 then 0x81620600c83ec23308f1a0984330198338680c10e05401bc9760fb02a00fa0d004149b2693e2c46c104824033df81a73b581e01fd0438e08ca50478183ec03227c06bc2022933c500406a0c07d835e0de481218438080940320041bc0ed056bce8061005a0200800b40ae481440b0330327b32058028156814083025920109060410232064978070c240d0108042500e3843e2604cf0e1009419608500889c0da101060248e18054020f1080c1833e47b077273d98468308f00f104203b214adc8f1a0c02a0894109edc02115112c195cff179f34fedbde7677ff4fc7ce10c021c82240c017207846c06c24689079243860708580c0f00f108cc20e2064de18402b04580c0f406d08c8293dd8041f40298378bafa77d66ff77edbdfdffddb37bd7eec059408a00816542409507d012406d12e3f1e7d8053900d200ae84b418c0b07883a219ce57bee7de1cb6ffe4c3bdf797b700423024601b00d046d0c3e37203c1bfe7e148e106202c00a102242403c07403c420fdce5ef4736f7c638bab08278020c706f891846d0c78819c9861012832c0607a0368464149eec020e010f418f849e1c3012827404a0105884661527ff3fb5f8bc3b6f7d9c3cf4ec086a09701d0041da0e602308da21f3e9067829207821e04063cfb161f9c598c005ba12d06302c8f00ec8662f91e3418054833e3d1d1c043b4747441e020c01810c444a0f18528101e1dc7dbf0a0c503280680811d084c378aec214d0604741e308ebd9886221410603aa1071e50b80f9f8f66800b100204200a21182130c22005b14081840da1280327b0080d0052064f60101a00a40ddeffffbefab7b71bf6fe2b7b70024804e810a0801a02d4168084036c4aebef7b77fd7d8dfb477b77d6140950404300680c301b01b61cb3dc03019e0a4832cf80602f0149060226440086808208119035bf85af0a016ef86ba055175af0aa35400000001412a0850702ec25006d861f76ff7bcadcdf86fe7ff536e6f8058285492a08f0182540600b504201b62467c23cc0e7139e66102831c1c0f104203b2145dbef7b73fe5f61bf35de6dcd601bd092821486030061a8d80db0e33f87cc70247e4f330c0a0ca05b825c0ce0307883b21d8feb06690c34180a48418f8731307e3c4cc3000baa0ca05b825c1c0ec86431e99f9cb850bca6598fc003d5072e10a0583c6158fe82edc21a0c052420f3e7b014e7006900600968160f1074429e33a11a0d0049009a0240f443108082bfacc0b8018d03e0d37501640a0290220083c19cf94e0d2b00900483c43107442a6ecc058170431088021f190279c3001a76418c0880f80f044a101063e207279c20023b483181004101e046614f881e7270800473906300c08203c08cc2bb408a8894234068fa016203014811a047c9a204829107802c0411880007044a8040 else 0x56c0480681f012c1c60c4be6680e05f018019410ed182680fc010288216a80e06d1230192f7fdeef96215503302c80e044014c30427240010c140750301281c60813c503802185025410a06025038c141438f0087e2c003e889540a0800824284e480201b0a03a8181080e304a80ee02021f97c7750001e0c0614075032808c240e5861c3c0c05900e812a05049041211ebee70f6db6d6db5b6da814134409094184a1680e022f715b36db319d025422246831c3e199a407999609e03e90254200fe8500e1f7e198c88f23184c132030605d01c2080fe8669c862016506909411507101c09fc4fc638e6f0201f0c022101d40da03126301c2330fa02b809880e06eb4025101cc240ca044e6880e07d08241b80f0d98ccc8d99b0c13c07d01884121101c6cdb30333363609960583fa0e80e02e860b1a03891a0da40e101c0fa067cb77407701082740708f00a2ee019c662e66f40610450603fa10f2c80e807d01c1f806371d48033669e80d41810407f420f0319f015c860e00c1020510c84868141040609dc401e317c31a06600c8140f80e3850e57c008ce78461813a0601e81b41c70a104c6509cc1e0046c12103d03f8107dcf1ad0957ac9f89d71b2540c004605813c86223686ca008404a05018606d8123260810f01e80dd2ee703cc0a28060802088d81c7080fc79f100bac4180011b026008c0110c83b02080e2eb10c40da0b18368c01043207803096e200c9221812033073838c10b85ec0a2431a02013c0da0b0a406033024eb00122a0006010c0e30312e78000c10360380101620e3841e39c9280382c7e4040358080960e7071c294339008703011410c81b41c6083ea81b20c02881fdce8deb10a281804120c836c28f9ad80c240a06d83138840260040381b41c706210801361e1c1e81a40a06d071c23a3540a21e03d419e310828080f5066b2ef940d20300fc1e843c0a7e40f21c7007c827819101f00406dc1211b038e182731810142c02a1203c038c1170150040bea1b6f6cccdbb6db504b82340ca05a05c2d004040fddeff370401b60b27d0041e305c018d98ca1666c302e58042090740101d7f82c68030408a59e28200ca0c082035e0c71ec47e1ff17c407a7c880383410a0814208060103034c1fd0eecaca0506c08660cbad40603688660cf5dd640d701788660c33f109c7c9c4007986402057813c0150900700f80e3070be581c8fc3800f427009f024009c0103e08641c70c3321004000f50940e3031e160e1fe043e28804f805410328140c0104860e3c8bc900e0c172048380f0120071c23a9a826032219834fe612105888660cba3c00802740650288641c7083b4ac0d8c1b336a0500c88da0c3df986cc349601950608da0d70b740611b03c60c0230c0ccddc5c9e72610403c03fa0fa300b2836033064727084a003c))) else (if i < 44 then (if i < 42 then 0x4d80f60103e886415da816c0304b50158060819f1ec18f663b844872003bd84820807807f428102470c4a0108204920d88378fc407480010413e01dc1a60fe852f306991200fa2190443eb7ede7a11b7706d30046a05212d0041e4236860f13a0e8d811501113280223608602bfd1c5ec84340105908d81e30a0cfcfb06773947802240ee44860584302080ff865ac0d305882b00c73f02264e818078217c046219103007a81a0fb08c83b4dd81182c489002c0469b9408c4f840d034022c9bd40103c82c40580831d11e12f8a07e1dcb2514018042620610281dc240104861cf5c5e3b6ff99d5c96b70042300df12308da15775e8582a014e0ff11b421f7796c20903d80cf00446d0bc9adb641305401f20dbc9b6c1620a893e41acba80e10181fe02c0434f280e10180580ff047041ca0203c019a78c07080c02c07f8208610430e8100678219e0401f00f011905474c0401f00b00c93e05ab0080c00ca09ea67015301c0fb20f8458816c03040f1cf91600945000ab04e80e406104076c2ba3f22400a9413a03843f1243c19039f00600aa01d40540140f81341da0ee5ffdcca5ecdb6efdf6ddf6db7b102d00418610404bc83010b0e471de4b0129000224680c2080e78418e044be740c1e014a08503404281410a08c832efb0446409d0180aa01e0a7b2405422303d28401359423d03c00b00cf8e4b0f0728b9200340640203d03f81cf0a5e5bb10c540c08e02402901533e920301748300ee09ec74d8816c05c01022c23b3df5341810c34060b1906023819ee5fbcefa643150301a004802304743013392181e01100d602406a1042320ad3bd408c809a031088168149eda03901808c0b408976680e40602a03b823b202c111d01003008327cd01009e40b08202116e81182180f007e3aea6407011823804d08309e081c0282140d404506846414badbc163a03019101e10f6cd01016204f8301e4598bc2a000920c058835e0d721694a00000144f80d783078777f3d801fbe14019940c7411a03504d01011c0e7875400155002cc1e804b100a80a4200067899000e0c4c800ab0040fe03d07a029f89f26403826780014604c81980280e025038c1cfc4f3e400e0c99000ac825812c0180e00f41e80e064923860e1003c603c1e2119046bb4404016009a81408f1e302500b00db069ec68808c0b10f00dc11f4870e1603bc001b88d8240041071c29f133999c03c2400015600c84909c01c07183395a11d401c1da0290474c01c10ca1e00c62f3902610e00c0981348400f40ed055b9a2431013029011c09ac890c400e08e03298e40091090490101ce0e3041c4cc531f80790f9c00410206e00806609c04a071838c744f878821745e2018020513e01dc412115082030f9fa13d201ef73b87d9860046019206b02cc24104863e24c9e00831dcc000 else (if i < 43 then 0xda024ee0209380540cbdff2d6bedd9b7b67b66dd40b402094041024e0df86502180540970bb7f63dadbac6d409704043006c06d857b11b21082c81e306188620043801141ce120588390100322441c08281b4060f108c822d7e03ab5f85756fff0d777a157faadd6b7df0aeabaa1fd3debdd7bfa00030a08d018169424a06078a8d824140a893740ee430701285410bbdb53fffe77edbdfe6fb6ff9bbd36f3767dfb7c9fdb825410a0204c81dc1d60a851b00c28151433f0f83399921e4e6616003b817e816a7c08203fa183f69227b0098fefbc1ffc6ff6fc7f6ceff8efb83fd80fa06095816a071a03a0502109091477bcb7fcdfd9b7df9b59db3b59bedb1b03bb825c11a0c50284a146d40a885521a8540867f0f98324e70fc79984e6003bd02dc12e0608228301fd0e05dfb36f0e6b366b0cc6d486e12508a8d80db0a33f0e6099ccc87c79984c0077a05b819c24a1007f4337a71b058c0c08600f1843e33483d06a477400026808403012c8620ec06e2b2c42740d09382ac111be641a11521882b0134940b017a0681b2e901620982ac220084b907008c0b40693483802a07703022494001c212c07ac0407d84641071f25039e87e007f0f8f7206600808e03e01e06683ba1c71023f39efe1f007f82879c81b406202600c07c03c02308cc41f880a27361e007c239805640cc018100878086119070718043e6274078063f2e02780b80201e03e08782320e7c498130e00e0f3005640a078820809c1dc0c4ec0108a80b00dc309280890806ddf5882320482c405880f051c40f14fcf0803e0ee3d9010806820c83001a119866b99208c16240d03402349ae60082c408606804537507580807340d041e3c400e08f80e362818041211a0684661595c80c4c04484034020c51078e883e593c700380227c03e08201040fe0635a74c0103c80b020808577de9a0626092027004162068066937cb004162079016027aec2111085011405c01050847c01e130387e013140d404501700443c01f08c839e3afd80c443cc04e00c0782080cb9a01298040390340204f00c0070299408503028d0081190513c0c749660008203204120c23c0e1410c3e0281a808a0201c046615f2041087a8100410429e6edbf841281040703e887a14a3be1b318f36cd9803100c4058408082429e6d01020821e837976820940802081a213c748ccdb0e1b284541940811b423b8019005807a03579232c46b34659db4300059a0e03d0412134816506d0100d9708200d8058069e64104a04680c082081185e081c0504281ac0220d08c82ae02a00815004040f7dfef6dc1006d8203d00be8d83d2802a1183500f40b404a03d00a812c8f642a04c01011f1d883fc5e203a79100010a081820807706983fa187192724031e0b0160190701e02400e30525dd8041a6065832f9b83 else 0x66fff7fd830c10d04612340c48622092020111c1d141f878a00e1807cbf981f448ca05701b8041480e38729f9e73e7fecd80cecd9fd845010c0571234011c1cc0721a440c58338b2060b01926e0e079838e0c3e22e40043c93603b819c0410f071c287c39401e0713f303e8825c02e0e506038e19d8a9baab76c1cf9930dffecfd7f5aad03411607d02b813dc0c104506302e216a03bafaeeebbb8002dddd6eeeee2d757aebff47eabb55d7f46a986180618603f81ec0e312300c42080d75064436db6db6db76eddbb5ad6feb5b6db6db76b33799b3336db6db6ed6d808c031f01f80bc030a4c8e190c20080203d40601da084f6a40b005010502810b91b01c8080398304122800824d80e41c704181924838400f0a0f07884641092724078600078d0184801c708760ff8a0f10be802435073805c2423607f433ced444621503b98261000076feee0aaa82aaa82a80000000055505550004018806207c84eff0003f0555055554154000000002aa82aa801e406207c8319e00091c9249152404641320488d824e0a981dc42a0e903383a442b0400c9649248a4236093c12f739f6f7e7073edbffa7cc397e53ef6e0081181e00ef01b283046d0e38f9de1e6900dff3f0e90803f8058023304806481a27c082046ac016088c0ee060f0c6881cf8e4440fa40707f18244f810406278b91f81c305f20082040da0310684801c70c7c68838bc40d3ce200082420827c03b84541fc0c7c664090c381e1005540d60102404101dc0c4383f21c303c2a0850328342080ee8540f17107c9d880077112841022a0fe8527380804605a03067e7c19d994793b30b0077017302c1da10407f433e7cee7ef5f1fbd04aace43fd7f3bd013c42401530900c08622368711450700f3e3600a940ca01a0384942320c7de78e8e84ab10b4c7420500a984886223685717cdb018085424a0b184275efbade0ff07d90c41862198572c806043104701a077902812808605a021f1d8822f103a7bf100047a20208201dc1d20fe861e30392430e0f84281ac0520f10683c42320c4bbb0083a40cb06f9b982640aa05b00c21fb9cbcf4e6def99c5cac202e0084601be24611b432e404e01824ff289ba6def6fee1db04318020df908891a14f8ec41e2881d27880020813e01dc1c00fe853e3819243860f0921050300e241e0f108c832dfa3838180e07d10f483c17a621150158060c0f243861f0940da0350082902330ac418a07262000ee0e007f41959bf82c489012703e8878157ef8e8df3a36f7b13a1a84409d40150603a046d0c0cfcec16766478fb30b003be83981644b90803fa1863ff8fa20085e7ec5fc700049823d016702780203d07f03c620be3ee7ae179d6dff9875cb45b80221108c037c48c236861c40c098a3c3281ac0243401c0480149760101a01940e502d80408)) else (if i < 45 then 0x602b09380c508c831886dbbf4db6da0c0861603d01421277e03e98041a60a4847dedd5fa7fcffebf6dfeffdbfbf7f7fffdbdff77dfee79cf5bfbfdedf77efb209e80f40440f06518201e60e306b834c08c60e8c18f2c507188718b033ec02900320342100ed8518f49ce47e703c0240046018d8410920d385706fcceeff2fa6dfdfffe6f7de1debe97e6f3f63bfcdc23027b404086121182006260e218c4b66bb66d6418035c1e3065d78d920c4c0c0d702a829015d79ffbddaefedfcff9b7eff6fbfff5dbf5f627b7dfbd906c80da03d010278240608043038c1a660e8b6bced10c680e0653088168156c408ca0c047018ee012405406d0324d4180450470183111e7000f9f83cec4e1407e00d8381ec04507a4334bdb8ba03d8081e243104702f32b218829011c60d0424beb01380886340a04697b72a03d8080ca43104702979aa03d80812a051042470c91c4060684201db067ebfd5ff37bd3e35faabe39def4e1caaf95c67e9fc30fe3e4211775ceb9d71c02800305a80d848c00da0504201db124906004924004908983d00c717981c020cf32303a41903e01983d0148c49e7003efc3ce01c07e0089f381c049071c325bf3c01f8020be0148844149ce2c8063c240e0081bc41a12007182a3e447401c01482541071be481e4870c01013202605c01c1760ed06245900609de0581900c80d087838c17274848c0a40240184e60050620401181c033079821cc2014602808c0e60683cc11d356a02029011c431041e58862a0c02781b410503cf1c08af919c1984852701c08bc0ea0503c614ed04280a206d03699c7cc813c08c431a0503c4145ae0520238862064eb0431010412080047a7697501014808e218c232ac48c0d70288191730216005401181e0e3073820271aa05a0200ce0c4e7336de6c0bf3e6661b37f399981603e814409e04602bd0288690e54900072071248119f40402780e41c7084bc48939000fa110726c0b80208488620e38508bd00707c937033809c0210f071c2f264ad66c0c666965a8144924348317970fcfe48300143e424e012c07703281600810f071c387c280380f05f981f448ce0670082901c70c2e1f114010f093603b81940a10f071c297178f87efec5880c0b06c6324dc21009104c0108080f3071c387e7f0673e52078307182ff303e8918413e03700b8381480e388063c8803861645b8408080f1072c20b971f0f000844f013603b838014099078c280b1e73f0f8602809c78fec09fe03701034dc1c431079c3842008902c8680f182017bf0bec2ef75c2bd6b5a15ed5aea800305b7b5beddad02aff756ad1b3740b00421802642080f1605c3880b2c29c89eb21883fa084083d7c9c9640c983bd02e01621883b2145c5f0f1fc9250000bc8fc1c49c025c0d004603a81421e0e38772f23f9bfd9b7cfdb36 else (if i < 46 then 0x1f201200835c03e03090038c151e18b21c30c7013805c200ed8401e1925c1c04e0104f8436115c67e9c66fbe8537fd5fcfe5579e5719fa06789e048eaee73aeb8e03808881e001a07d605039421b1048f0c0386b809c02e0e07a422440fb1e0fd0c7018007403501484a01db0c9becaf7a7fb0ee0df643821c1ce0270089248690c96ff301b80e08e5fb6bb7e0012310c4c0d08aaffbbd55555dbef56ea0000002bbaaef81555554140000002a0d300801c408c0318635fe9e7304181814860d047428e7a40933018ccc922760310189241f5084efd019448ce023078168147c4c8785f843806b04580d40560112301e81dc0f4118812cb80fae0107d02901071e7cc06660e126661a6916415b009004862118851c64863c48d8800b01580481a10807382ae4d73c0ae611074823a112dc06521a5804c1a0838de48612181904d80441a104077028f5a07d00d00ca60f0416b3a07d07801440da08d701f4860e020520203c7c3831114003f5c04f01b80dc040e5076c3099c58802203c06a11090038c102dde1f56b7bc2b56eff0faeefa15755bad7f0bff55aa0bbbf5dd77e8000c02d5410a0602d03d5422104090502a240660366459b0d688e43008c411cd6f04c90c1c0408e842580fa0fa05201af6ff765fdc5f779b7df6dfcffe7eff6de6b7b9b7e27a0807d0286816a11076a9181b140a8925b8265c04a49047020c1efb7f7ec51bb71ffdbfc5637dbd834c1360ad050a9168600a804af80c10806d892580fa0e9052018c603cc09f31c799837322dc10e0ea0581b42310abbe6b07903c05440d841cf40da3a0d0049007807801a43108082bd9acdd83e86340f833c68e833a0d49d0001342100348620eb0537a7052183411d0639f49e649980c60491006021510309241a70a4bfb2032b809c0224606b828c4e5f8ef9c021e216035015804194078071c352118815333bdffc07d902d805c0260e052431376f81956011228292117993afc07d30138042300a4856f99bf2effe03ea824c0d205b00b8041490e593f80fa033700834c1480bd3329c020dc01983281093e03ec8141a60a4042f7daecfb9bfedf9df6deff66fbffe7a7ebf3fb77fedbdfd8b3d044816c07a0206b83fc1ea0ca923034d815165f01f40660a48325d97815cc04431047423e657f3bdcff6f7ffcdfb20c5677ee7ccfb2fe708a08500ae2360278844c1c031218c4a283c7d83c4077282141b40709403b61565cb2c0180480862099047cfb9ca7f6f7ff9b03194fcd9fb73211410b821840da0202b983886910d2cee80f43106bc1b3fb2db6c862608d01038210b2cfee80ee0108a02a2100627fb1e270efb98fe78b0003f002fe82280fa0223c03b607c0d788f72746606018283011d084f3aecfc0c243150688d816b0a7db9d2f7f36f7e9eff98e0e7cb4bd0e016a056c else 0xc9640240141e120071819c64b900c9090788042400e304226200880340612007181ad7f80f4295bbf86bbbd0abaaeb5f857aaffaab77c7febbbd775da000052328d9412a085032815422104090502a28f1c0c921c301241803390783c42320a1deb908a846c02e0112302a3f7b710f4846c02e0105f085c1969c02029d08818ee06d80a40da06a0d2014810f5aff9bb4bb06ed67acdf6b00e4236060164a1742206d86127ec02e0101489f0100f24870c7c140da0350082b42330a863efd9187b370013425a11d08302d81410d863c499200e1980484580207f027038c14639c9201e1320600813803210a071828464041c0a06b0081201c608d0052a1103c019a721880a542206d0469ba90882fc0f00290446f484502223606c022cf9036043202f035b96502207813e00a410211b8004200a09a0300701c608b2f59e423c0102504380520a11de002018282680ca05403838c142370040500a09a0381e01c6083dfeb014a84680ee0110cc299508b80446c06d005942240b030e874dac637d860cd6dbd0800a74220788422c040191101f043823206d3843807c23603243946f3e0fcbd0888da08e9d6d6dac18636d6c0b3a1103c419176e0101489f20ca398d99ef836002a00c4052406086c2a35c21d40602a09f013c84d9b66db986c66302a00c40a227c8446f484502224606b0223d843d21105f035811da006042f06d03d087a4224040347d086502227c06b0232112b01c07206cad00a421a06d0338d144f22180224401400683b01a60831ca03e259e01005301600600984701f00c4f4e1c6514506080a23e089440201440683b81a60c7c3887851818014b07200506301608a0339da00e301883ac0c3088214a2010181c00ec0318245c925003d08120310760220123dd30921cc5a05c248031076421c1244964c020310d80620ec04107484c2398960f401883ba0c608914ae040f420300c41d8088024e829863cc1dc03107641bb490d0c1a0a4047021c9203c3090041ae02094038e103933))))))
def level11 : Packing := (2241,4,9,0,0,18,1,nd11)
def nd12 (i : Nat) : Nat := (if i < 7 then (if i < 3 then (if i < 1 then 0x28043800017ff525da7fea4bb7ffd2476dffa48edfde491dbffe90bb6ffd2176bffa80edffd201dbffe203b7ff44076fff840ed3ff525937fe93b26dfd2664dffa44c9ffe289937fe90b27ff50064ffe880c9fff52606ffea4c0cffd4981fff293033fe52607ffe93c0fffd4481fffa4903fde49207ffe7240fffcc481fffa4503ffe48a07ffe5140fff8a281fffa81037ff50207ffe8040f7fd0081efea0103fff08207ffea4b8dffd49719ffa92e3ffe525c67fca4b8fffd4871bffa90e3ffe521c7ffe9438effd2871fff250e3eff41dc7ffea338fffd2671dffa4ce3eff399c7ffea2b8fffd2571dffa4ae3fff315c7ffea238fffd2471dffa48e3fde491c7ffe6238fffd4371bffa86e3fff40dc7ffe61b8fffca371ff7946e3fef20dc7ffea138fffd2271dffa44e3fff309c7ffe3138fffd2171dffa42e3fff405c7ffe30b8ffbc6171fffa80e37ff501c7ffe8038fff50071f7f9c0e3fff301c7ffe5038fff48071fff880e3ffd101c7ffe1038dffd49619ffa92c37ff52187ffe9430effd2861bffa8ec3fff49d877fe93b0fffd0761fffa4ac3bff49587ffc92b0fffce561fffa48c3bff49187fbc9230fffce461bffa86c3fff40d87ffe71b0fffca361ff7946c3fef20d87ffe9130effd2261fff244c3fff38987efe6130fffca261fff144c3fff18987ff680b0dffd4061fffa00c3ffd40187ffe7030fdfcc061fff940c3ffd20187ffe2030fff44061fffa92a3bff52546ffea4a8cffd4951fff292a3bfe525467fca4a8fffd4651bffa8ca3fff499477fe9328fffce651fffa88a3fff491477fe9228ff792451fff988a3fff50d47fdea1a8dffd4351bf7a86a3fff30d47fde41a8fffd4251fff284a3fff489477fe9128fff92251fffa04a3ffe40947ffe7128fffcc251fff8c4a3fff485477fe90a8fffd0151ffda02a3fff38547ff670a8fffc6151ff78c2a3fff50146ffea028fff14051fff980a3ffd20147ffe2028fff44051fff840a3ffb081467fea4a0cff94941dffa5083bff49d07ffe83a0effd2641fffa0c83fff399077fe92a0fff90541fff9ca83fff31506fdea1a0ffbca341dffa4483fff40907ffc8120fffce241fff98483fff28907ffc5120effd2141dfda4283fff40507ffe70a0fffca141ff78c283feb18507ffa8020ff748041ffe88083fff524877fea490dffd49219ffa9243ffe524867fca490fffd4621bffa8c43fff498877fe9310fffce621fffa8a437ff51487ffca290fffd2521dffa4a43ffe49487ffe8290fff90521fff9ca43fff31487ffea210fffd2421dffa4843fde49087ffe6210fffca421fffa4243bff48487ffe8090fffce121ffd9c243fff28487ffe4090fffd4021bffa8043fff40087ffa8010fffce021fff98043fff28087ffa4010fffc4021ffe88043ff710087fea2010fffc2021 else (if i < 2 then 0x9605d07506453fb6f7fde1cefdfdbbfddbffdbffeffff03b7dbeddbff6f6ffed57aaa7fdbfdb439b7dfb9b6fdabdedb4b70268258270218201600c00a42bc0e41e81f102883a38d83b8ffbdafacdfdbfd9bda066f6fd801cdf6c6cd0333666c660a2c09a09c080300bb60207c06d897fb6f7dedb77f76ff6fbf7edffb7ff6fff6ffb7fffddad6b7b7081bfb7ecdf6fb6b5b6d96ccc0db02682582580c0a501c0c41541050401b502a34f92bbb67cd6dfedf96cf6f6f2d96b5a5b3fb7edb7b4e4b924d0e7b9ce7638cccf3660199b2631db28268210c40c41e102c1b435220479dc3fb0ccdfb9cefb337eccdf4955ccdfe619ccc981d9863d9ccc82028e0960800210720502ac399f97d7fcdde6f9bbfb612a47377f6edd1f377fedb69b98f3f66c33067b1ffcd8c6a6a49a9a993276ddba9ddbbfcff6d942a68200183668480281540c48e883840a2cbfafe673773b737bfe76e6f7fb7e6edcdefb7dbe3633fd9fbff0a255241dbb7b7b7b6506767ecf81b6c6a6a6a6a6495321e38138200082080728620aa8141c714dbdb7db6db6dbb76ddbb5ad6b5b6db6db76b3fccd999999999b19adad6d56b36d80c401801380e83302e18be0ee17f6ab35bf66ffbc066b78039ac9436663130d1029c09404c1020505506d88c98d648f322af8f6ec6e5630e7148f87f1c33a6130f05f781f9c09b5fe42fda77d41be32debf2f3697865bb63dd262e589721cb8a45bd1edb876caab540da542d0bb666db29558c42c1a75f34ae6c56ba2b18f5756ab09d54cea5b551b5a88a5417e9e0f4c53a59f529428f794685a20450cba846d402f9f0acf4da788739de9b95cd9f26b9d337998accc0b25dbd2c339506ca00a4c27242c9124c85be40fd1df68e5646daa349b17fd8add44efe23cf1100875cc36b616d50907841841d420b3b0464812c405c5fed2fe5c7dd8beb1df1b0f6587aaf3cd3de268f03a7729bb679d85eeb97750d3a321cfdee5a57249b8c15c2dadfca6f49b76b1b776db076cee35fedac3ad50869c4346c9a0a6cf1866c2331899618ca10647031f0d8be8c4fd616cb031d7e30be455e672ee99755ab8365b9fad5ed6688b28a58e22bdb15ab4ac4b554caa2394c06a4b25161a839d3dee9dd94e72269f932c097574ab1a4d3121bc8f0946fca2e8112fa874542eba0f0d04027ff23f879f3c0f6527a3c3c349dc84ea0a73f439089c4ace0626e27362e1abecd35268ba33e6197b8ca1464263187188f0c1905ee32ec317280b7525a8c2c8e96154adb655f02a7695068a690520f289313e149d564d1425d3125e48ec645b8229c912508766416f1fef0f84879e63b151c318dbd86aa432c018eb8c0785cb62c8c153a8a4bc506825f1120d88c5c43cc204a0ee906f84351e18ab0b3d055f02934126d084f039fc18f40b3804b301ef80cf6046a013 else 0x88243e042031b09308459b73ff9bffdf9fb76fbfbecdfedff92d9bfdbe73ffff9fd6d7fd9a6f3d6f66f9b6cefedb7bb431019210c09c01a1283141007c20e1040786108d7fedbbfb7fb7fbfefb6edefdedfff6ffdbfdbfb7fffffef02db76ffb7d7eb6bffb7dbf6dbfb79b0b19b5d6db7606cc1340780244a84208c47b0628620f81e20da4191c31b994ffbffec7dbec7b7b1fedffb03f859f9b99d859f988a870304b0420082b307b06827818a18c5a73fd99dcb7d8b7b16fb16f643f3b166599b3b33034601a12a10031434431873f6fdfff7f7f37fbff6cfff3fead969ffbded9eded37fbfed9ffdb6b79c924bb9755d749964d98467b36798770f9ef9f3cf871f006941341008c06c8680340268140da8160f01a11a4e6d9bf7ea6dfed9a9b3b676ea6cf6cf6f6ea6cfed9b6ddbc8f9df39f3ec4676736608cf66cf31f6c227ac921ac504d0401820583683c205096c42728f8ff33b96fd8b7b297c5bd9041cc59298b0b1985650480bd08018836a18c3a4ef18d994fedf63b7ff8edf66f3641f831661d98eccd8586cc0d98250068481e89f00c50c621edaebfdedd5fff6fb6ddbedc06ffdbdb7f7fdfbf5edff7fb7d6dbb71b7f7cdeb6ded8258204b41690c58044a038c8f40c48322cdb37bf36fff35fff3febf35fda73e73b91b7fcd7f6dae337dffcff3ecc31aff6f6b9bdfff8d7b55735ff9e93434c6a67dbfff861cffdb602bf02e82502500435c0d80c68400381b41608309f03ae3db6f77bfb6fdffbf7f6ddffffb7b7edfedff6fe0137fb7fdbffdffafadaffeddbedb76ec59b36b5b6db6035811802863420c200e008d0624120b00da4191a3e3e6fd2769666fe1604ccdf9feff9b7bd99b08ccac19998ce6d9db418a18e0481b10760085883e13e448abdfcfb67de66dffc53ac0d9f633cd9b7bfb7a59e66ddbbfdba66ef666e99b776e29d11924f336fd666f7eddd5b604e00a0f60503e11b03c10713e44b6ddeff7db7f7fdbeedefffffb7ffb7ffdbfff6ff6efef816edfcffafd6d7fefb6f6fdb6f6f366b6cdb5ffdd6db76c06b0268258250130050c483837e0c42bc1604101b48323d39462f33b97fb16fb1545bec820c761791665858de6a09a100d903106d43186360fb0ccdecdfbb337b337495599a31b3368c3440a704b04102815618db2fbe6bff37fdffcd7f37bfdbccfccfd98cfe67fb3c1cf9ceeee701afb7fdbd9b3b8d5bffeb339a6ad7afcf39b54d260e4d341d8124128638204200720162088140aa1e918fb6ffdedb6fefdfb7dbdddbff6fedfedf6ffb5bffd6ff6fb7fd840dfb766f6f6d6b6db665cccc199811811304184102501c2ec1540c41b502a2db6db7fdfbf6dbedbdfdbdadab5acd8fff3ccdb6dfedb6ded66ddbeefeddb6ed66eddb77dbb59b776edad6ab66b5accd9b0ccdb6023204d04024203818b0)) else (if i < 5 then (if i < 4 then 0x206005bfc3f8b873375e1e37b750fc6b5a000001801800e3eeeefbbed00a366ffd7aa1b3ed0fe0d3a09a080d9a0c0780e3031892dfff6f6d9bfeccdecdffb76d7fbf7ebb7fbedeb6fe6f9bdf6eb6feed82582380c4b415980423848038d0c49f22cdbf9bb3ffd7e6bff69fcf99ff671b7e6edb6b19bef99edfffc31af6abffe6bcbaacba526843533ffb3fff0c3fcb017215e152033809c07c05c0008c82081b8164f81f61d71e6bffcd66bfcd7f533e67bfe633fccd9f87ffcdf7ccdffdb9c0aa9658d7f557fcce5377b5faf3f396effd34819cd380b104f00f00090108507082106d0621889407a46b6defff77b76ffaf6b5b6f6dbb5bfcdfdfd9999beddadf7cddddadd9bb5aad66bf599987e66015014013001e00c0b085a0ea0cc0a8a3eda040eda92ba5a104b4b4e8684f904c00019e045052282a800000000450555003107c8237a4da599bc08b337ff336eeccd9133666cda18e0402360083e13e432fdbf3fbefadffedafccffb67f65e742cffb6dffdac97cedbb77fed64dd67dac9b7fbfdbb67f606667bce81e73de1676d64dddbbb67104e0460090860583e01281890603692313e463b7ffd6ddaf7b7f6fb7f6b7da1bff6edbfdbf7ef76dff6ff7dedb5a06f9bbdb6ec3a58238050c58498044a00c438c9f08322c07bc003d6bf0003ff6d7e34077fdbfae34377dafe346ffff70f1435afa0180331b5c346eeeff76d302d0210078000c68403540f41b49f011a2c63f37a4da599be161666f6feff36eeccd84611b3666cdc18a18908e0481b60083e13e442dbeed6ccdfedbfffdb7bffdbdf37fb7ff67b7ddfb7f6d7feddbffedbfe69b5b6efdbfb6ffb781380ec07c058020acc258148141bec2086211c0f91cdb6dbdedb7fdb7fff6ddbfbfb7feefdbb6bfedafdad6dfeffdbfdfeed6f3fb667ffb33336fbdbeddadbefb36efdbbbb5bb376d7ed6d56b36bffad9bded9998c6db3604e00f0001b10930810783e605818d07506605469b07fd8666e92e92ef7bbfcffe7ffff7efcfb3e7bf820be60dff8c4b43803501850c43430041618212149f0156316cedadbffdbffb7b6ddbdbfb76b7ecffdfedf7cb6ffb7fbcdb76fedbb7ededa6dac0c58258238050c683a8318044a09f03b038231b6db7bdb6ffdb6fff7fff5edab5bff3db199b7effb7efd66ddbfdfedfddff6ed66ddb7dfdbed66fbeedaf6ab66b5ad9ecd8666c6ddfdb76b37777ff76d6019a09e00046038401031610c0b07cc0aa0ea0c8d36e7667766f64bd337b2f47067c74cccd99361d99a02142818b08218c2b6dcdb6fdedb6bedbb7ecddffad9bfff5bb7edeff7dff6dfdfdbdbedb6cd6cd6db6f6fb6db6c1180da80580700509e0c50c4a161f09f22cdb9e6dcff6fdbeffb5ebfc63f3e597af9ceffecffbdb7f7f367fef3366fa6cdcffdb367eeb6fda18861c18a04e0 else 0x6504204503500a0700ed07842071818c7019ebffefc3fe1f5f5fbbc3b75d6bf87f6ab43fcf00000182d7c3ed56a816ef6ebbbbff41a0000300fa0e3a09a0107a04607803ca0c4360318b2b9eff994633b1df379fff36ff3b3683f84631bf3f66f9bcd99b231b02320ab0440083c301836942818c18c5120aa455f38a00abf38ade004041c5771dc2af9c56f1ff39dc0007300400001c681081dc0606208c0db0e5e977cee312e6e58a6e5997821c631b962964b238d805c0582101b60c614bd2ef9de316e58b994dcb3410e331b96652c96463601703161106d83185033d6fefc3eb770edd7ebc3ed6876eeed0ff3c0000005bfbfe1ffb6ddadc0b5edfff55ffd0681800003f838e81901a80438011a8480f01e83b00c63078e31c6328ec53ec500f0706181b142c58b184698480581e838c38214f7a5328c6d3b14da76290423235f6669b1b230da81805a8481ea0c615387d7d772c3fe9ade9a1f8da6b012e598de9ad1309830d982480805d8380c60c41b61c3c01b835a06dbb40001b6ed6c0d6ab46860018004e03a0c0318403003787f3370e66ed08d6871b777687c0006f0fc6dbb5b70da1ad5ff4d00c006300e3a09a06a010e007aa0c03188033ebfff7f0ffeb5e1ed5fddf0eddab7eff87fedfb5b87f9f00000007af55d7805afb55d7e86ca00000069d04d0420450082307181e03c50607f818c615e7dcca319ecdf9fd9b7cfff9bf3fb141fe0a3187b9b1be6ccdb9a31b811a0068418401b44803640c60c624788c46329c772299fb0f04066018fb1f6308ca080860160780840d3863de94ca31b4ec534ecd7ec82118c299a7d99f646354101ec02d4240f10630c9c3dfebb961bf4d6fa681b7d35a7025cb2c4f5a0989818de0176096100d903183106d872b9ef994636ff9fd9b7efcfff9bcfec76683fc23330ef9b379b3364637cc86cc13003424c061b20da4840630631478e31c63629c51b1451e0e0c3201162c611802c0f01c61a708483b7dfc8edde46e000edf7e47fedc0080115450edde46eee372530c030218000030071a04a0406920705a018836c40f7db1b8dda35ad8db768f000000d8db76b6000006001a01e03e02031854e3f5aee584d6f4d0037d3404b96637a6b53334c0cc6c054c10c1c0630620db0c78e33c63b220dc8bb2203aa2cc645a3334d80300c41b60c43fa10f1c678c7645917220e0752c58322d19b4c380c03106d8310e38424011de457722b70003b7915fdb800803b916b7771b910c300c0c00c0063007186907b018836c29e06c0dc1bb4335ad836dda78001b066dbb5b0060031a80780f8080c610300181c5e1e375c39fe776ea1f99b5ad000000300302fff0f8ddbdbb40a1b5ff5fd50d9a22a1fc08d41941140d41e1081c60631403c0001b80d6806dbb40018036ddad806b55a366800f01d06018c) else (if i < 6 then 0x7fb07ecffb370c3c00a6058c12c0cc020622084181c7126d9bef9b7ff35ffe7fd7cd7f69cf39dce35f6abb8cdeffcff3d98fffc6bfdbf6b9afc67fccfecfff86c31a68e9898d7af54b52f58d0e30b4a09409401036031a0ec0b01006d20c1040ed8e6dbf77ef76fbfbef6dffbfdb7edf6edff6f009bb7fe7f5feb6bffb7f7b6ff6dfffdbfededb32f9833333adafff6edb6cc0d0098020c741d06286241208c1ec2080da4191adffefdfb6dfdb6dbb6efb6b5b5f6b76dbb7f77ddbb5adafb55b599b33fd9999bdb6deddaddb5ecdb6db7fdb76b76d66f6ccdb6cccd8c6c41380d80208c41010b816c25421815143c78ff1c67ff663f878d23a05ff3ff0fbec6c6cc76c63b1199980fc003cc18a1880f604c0260090803e106082458a9ff9f9bffbd98dbfe24eb3cc6fbf6fac13a159e6376eff6e9ba79b37f4df53fb779b1bdfb7acdeb376f30cdcc731bb9b83ca0ae04e00e0583e70111b03d10808245873aafebfbefdbdddbff6fdfff6ff6fdbfeaabe7b7a1c1f33bb3261bfdbf6fb65eda35edbbb637812c13806c1c00a2501ce0c6068418817166d9ff3bf77e6bf99affd679af5ede4ebaebae9aad7aba63f9f4d99cffe0cff59bffce6c134d2e98c19befac92c63183d838e82401e8180c401602a8408303c435e3062312cfe5e3cb8e3807c9b058fd8de1f0604e03205082078831871c39b67dfbf37dfcdeff3535699fccff66356abff8e4e75dc846f7eded66d771beff9bdffb6d66b9bccfb7ff870d98d2139340b10adc06206c1221200706343140a07a0ec8c33f56cd99d4fb7f9dbea7f679dbdbc867cfec56278aa48536d9fb76eddb295b36676dbeded93721b3ecf06cdc064dc0604f20da8628141c710311e233f2c7971cb146130089b30b1f60dc0803031c0604610406d0e3863cfffbfe2a679bb67cfcefece76e19f19819c65af395552c56b3d552ca9bb67f9fb6dd9b2a8367f60b2cc81401540c2088634240620f48161e314318c7c63f3fd9ff3de3cee38c3804fe6c1b1f3606f063f248c28d812c1280e06280c2081e28141c71266d8feffdfccff9b6cff32fd9effeb4eecff3b769867e7631ff3c6ccc1f6db3dbed6ed9f66db3cb55adb66cd0cd9fb38366c06c80e06342480c2098160f01e2c1c1c7163c47c467f963f971ca208049b058fd8c59c8333040031c09c0620540410406d0e3882fd7e67377376e6f7f37ffdcdefb7c7fc67f660cecf8c2895480edbb7b7b3651db9bdfedb7d9b26f29a4c449a2081e380d8240080828620c68141e9143e1edc2d687b6dda000007b6ddad835aad068000004821701836818c298f8dc00c6db807900178aa2831b6e364a1e000006000002a015c060620db0a067c3adefc3dbafff770eeedd6bfe1ffb5ad0fe7c00000305fffefc3fdbb7b76816bed7ffd7ff541a0000008a87f00bd else 0x6b3eaa9655b3fe6fedb6ecd95467ed9fec16629e7bbe6e70f26e7a8268184110c28300c10281e902c3c628b82f87eb5dd3fed4ded13e4d00a7eb75937b583600c350487580bd07018a18836c3afedbbafb7bfedfff6fb7edfedffb7b7f6fb5fbd8006667e1bfdbed6cbdb4fedddb7fdb636c13c06862c1c1e21842400f28081ce817166def359cd6b9cd7f5ddc9afd7fff5ffeabaead319f4dfff3ff9ff38334cffcff3b04d34a03337dac92c631847c4584283f43d83ac39f80f80b0290104983c435e38db37bcddff9bbffcddfe6effbb99ff99ffffe637dffdbbffeec4f255211a9a993524cff33fee70d8326fbf6ddbbf97f46ac6fb7bdb76ecdf52b66f865508604c041096071075064062188050942058774736def6db6eddbb5ad6b76eeed7f99b33336db6ddadbb35b5aafacd66d9998cd9805b80001284283302a19edbfdffeff0f9f6f7fff776ffededfdbf6f6fe07db7edfcabaaad6edb5bfededffb687db0fdb776dad837031b04e0330302504282080609401a20590646ab7e7f954cfd5b3fcfead9e7b7ab673b76eb0cf3627159215b7fcfedb7b76cb2c366ce0c4f9f77e6e739f11b9f503024218818a05508036a05871c49ed766d6dbfdb7fffb6fdffdbf5f6ff6ffdbefaddedfdb3fedcdbffefb7eccb67b77ffb6fedb6dede04e03a02301f01600b09605307085871a1886f86bc70c719ff663fa473d9e38fc3c603e6c7fb09d06860c00c60a981240b8021e20f8c1c1c712318c79fd8cee394410f81bfd867ec0dc1e002c6096066010311040f10e38836cdecdbffb67fdfff5fdfecfb4ffeef767fdbb4cf67f9d8cdfdfcffcfb330d9f6fdadd9f9b3ed56b66cd33db3fd9c1b319ff9ffe4e60fc9807b0101180c684841103f02c1e01b83c583838e34db9de67767fd92fa66fb1b331c18f3765f53679af1f87762a0940727c08603160e431876da6cdbb6b6f6d6ffb7f6ff7ffbedbfb7ffffdf66ffb73d6dfbf6ddffdadedb6b7db6db37db6db376deffdb6d82301b203c02013d08b08e0083e418a1888c871c69b79e7fb73eefdbff7f6bf5f0f3e97ebe6cffbefffcfef6ddffd9dfb7bfecf38d9dffa73fd9b7f7ffad9a18c0260086f86104d41886504283c06bb09307469b739ff7ffe9fff5fdbefdb37f6fff3966ffdbef3df7fffcfddb7fbfd97f6edece5e6cbecdaff9b7effedb343101e40ec09804a0209ac011288310f22100780f660e8f7fdb7bb7fbbfdf7efbffbdffffbfb6fffededfeddbffeffdf6626ffb6edff9b7ebfadafff6fdffdedfdb6dedf6c0b61d6d7ffedb6c1b982601280f00439c0d885c11a0c50c41f04804101b483241f6deeffb76f7efdbedab7ff6fb7fb7fedfffff7f6edf6ff6edfd8419ad9bdbdb376f6dbbf6d5b3606cc12c0607d8250208081940b01e20688171831e31e7f633b8e51043e06))) else (if i < 11 then (if i < 9 then (if i < 8 then 0x63b77b5b8ed7f1d6b5a35d315a36ad76cc76f5be66ed681e6000031409e032120f1084a0c8718f8f1c639fb3fef1c0a2807f1fb347fb1dec181f0c302581b00412808980c1f03c43b2241f0002ddfc16bda196bf6a800003376b6830b77bff6b46e018000630030212c09c08004c0e43110406d8818e3118e7d9fe7b107e201c7d9f8f63fb0600c09c060f104a60e06d4100ec880018631df0c77b780063bb76e0000c11545a0c63fedf6f337140c000431a12e030f140b06d86188c78c4fb3fcfd8f183b8e013ece63db81831fc9188a6048023018252070788368764418afdfefcc5be62fae62ddb9805fcc5fdbedc5affc56d68d5e637b71b7bfed3177bbb99edded7b80c000031c0b4070f1406a120ea60e0eca0c8a19fb3fe771ca221e067f60fb1fec6e0c00fc0a6058c12c0cc022081e21c7126bf9acfffafcd7ff53f9f33fffffcff2aac66fbe67bfe7fc2377b5acbbc67e66cff0b0c69a3870d7ffaab96b9d71a19603d809c07c0425621a08c81c81b81613424c1db1c6f7fe6ecd7f35fef4cfccffffcc6bfdaafff1ffcdfbf337fdb9c38e434c67f3379e180d7daaf95c6b2dd52aceb286505680b104f00d08107106d0609421888207746b6dfefff77f6edfebed6b7776b7fcdf7d9999bdbb5bbcdb7f6dbb5bb37b5aafd66b599987e6601501302500ee0000dc0ba10a0cc0a8a1b3179e2e710700cbe2c33160de0f8fc00608082081e28621c70c61870e3b908aa00461fc7ef77507df0c6f7751ef30c7feeea67ef6f031c00000000037c0c50c501302c1e41b818e20c7f8dcfe35a7c6baa0001e000636ddad03f1aeaa834000000540500200140101e41b80c6207f1c63b3166207f985ec6c6cc7ed8d83e18086202f80c8098020dc2561e3107f6fe7ff7df5bffe6bfacff9bf7fed3ce919ffd9f85f39bb77ffb5ba659f6b7e9b3fdbacff9b7fed6fd666edfe79d6781cf79e3377cd3983773708270041bb03883b02c0968400c48301b49183c6346318f9ec7945ce0e1f819fec1fd8d8341f0016303300818b09301082071c400ffd8007fffb5e0007c7a01dfebfae342b6bf8de35fa1f6d7fc6f1b5adf803000b5c2e2d55d73082031d03200818e05821508036871823459b7f9fe7fefd3feb7fffefb66fffdbfe72cf2e77e76fffe7dedbdffd96df76cdfff6fdb7f2f67f6bff36f7ffb6db06e431a09a06804c0109a08521120c03683106d21010a6119018c67a6298a623074b16098b46c1c38300c50290c438e1073f18e5897880045f2c4b160de0e00346011040314340f1863edf3fffff7f9bfeffdb3f9fff777ff676e7fe7e67f6633b38ca755494faaa4a6ffbf6cfff6dbb365533f6cffec1263ce73878939e06301ea06104046434034a1203a01b40a07a40b0f18e539b66fbeab6ffcdfdaaff673776ea33f33f66519d9c655 else 0xa0750960581e308076506450c78c7b31738804859f91662c18010100c18410d03c61532ff5f6f5e7edced66f4bb274bdff7ff36fefed65b59bb64ecfafcdf7edc18a1890660088207884283e308506451e38c72c4b10011744b160c000b036a1a078c21fcfe0ed4c76fbf31a00eddfe635b800078af47a3bffbf31adf3371e818000000010d102004d03b80d02c3c42101b62406c018ed418edf7da00018eddb5b80f15e8f6831dfedadf3377a00c000030018430e0340b0f108406d8677ca31e994ed674ec51dac82098ed6629a16180b207b07836a18c2953f5f9bde6f799fccff7fc57aa3fffbff37ffbffb7b29cf39dddc271b989b9c67f33fdff0b30395f5a9551517df6decb5beee76ca0d886381041025181c41c0180721088164182031a583de1ff7f75f8335b8335be004c666b76d2e5e699816012c0660410943e506042443f33efbbbbdde7ede7b7f66fee77b39edff67ffbaa554b26b7fb37b6cf9ecefb36d7810c10c0c0940580720f842281741914fe6776ffb7ddcfedeffdbfd9bfdbf66f39ecdf6a9552c35a2adfb37b6d39ec7fdd9b57018148094058c1c8110f80728174191462dfdfbf31be62df6f316f6f00315b5e8dbbfc5db76e36b662dbede66d6e030017316eb9956eb700c50210128498430283c68322080314c7bea63ddb802d31ffb7db800c0298ffdbedccd980600006000c218d09076701a05836c30c78c7e7d8fe76381443c0ffc99d818002ca12a0c60906d60e0f10ec8833fe3efadfefe62d7f31a1f05bdfcc6f68b76fbeffc6ed1b98dfb46f7ee62ff532f5bafc3e600031eef4cf7773ae01880a509042e0581e078e05086506450c72d3b33408c599a92ad268058f93520381821a13e420c7f3ed27ed2ccde10b337bfdff36eecfcdb09858f99b683143120c0b50a4085c0107c27c89157bf9f53bc96defe19b3ecf2cdbffb7b3c9b76eff6ecdde59bd9b7efdb8d9f6c3330a7584944f64dbb3776eed9604600812e0583e11283690613e44b32bf7f6fbd9b73b7fecdffdb7fdfffff9f72766fb7afff36ff7fb7b36db3f76d93b1fd66dbf7f646d063812c12c078021e21d486c8620f80db4191a31f18e31d98fd238c01fd9fe1ef36ff8d1d06180054831431c09206c0107c60e0f1897f33defbf6ef73fb73b7fb37fb7fd9b9e76fd9ffea95536b3eeda79d9fbd9b5fc0860304a02c0f10ea03907c40ba0c8a036efeefea07b775b7df80206eed6dffc6f8d56d6bfc68d6eed1bc6def6b775b6fccdf336d6f6a8d9a66ad5b702300411b03b80c2109181b484a247bc0c5bbf98b5f68018b5fb5400000f1bb46d062ddf7fed1a37000006000c509604e0460710621885d836c40c478f8f8bc7cfd8fe0771dc027fd9c7ec7f60f30c7fa46224407004c0e60e0252120f106d0ec8931ddfbdf9878ebbe63bef400ee) else (if i < 10 then 0x8c718f638c33f63b002854fb13ecfec0318f46214980cc0407c0628248142090e663ffbfbf99ff6cfc987b16cfdfff55ec7767fe6edae7b4c7fcfc6d8663fdb3f6bcd6ddfec6fb67cfb5ecd6ecdf06c7ff9d86cd811a8310268200c702d01c21283a80c4118483fa34bfaff3f3f9fbefff37f77ffcdf7ff37bbcdef6f1ffbb19fb7ffe144aa41f76fb7dbdb28ddddff377eddbb9370cf678c366c534d31268878858811e04b0450300201101b21881c91b205071c70c47118f2cf8c345400a152cc963d87031830c0907c20c06d10485188e23e7e58f0e32c7b440116458fb04cc0c031036c1221007a0fe863f38a99f9bb67fbfe0fb1db39dbbec19fc61f6539552ac54f54ab2a6ed9e7b7bd9bb2a831c65966c8634134100634060f00da81620912318e3cff8f3ec7f8c33ec7b0050a7f62e3dc80e631f918854019c0940700461207c20e40a10489331fafcfdbf3f9b767fccc4b1eecf3dbd63bb3fcedd2dcc7f3e36198fbb3edf4dedbbeca4aa956aca198f7ff61ffb2b61040fba09a08031019078a0c23620e0fe8b1f11f88c7967f06514b8e00967163d8e30181240b40607a2080da1fd0e6f7fe6f7ff33e67ffff8aaa377fcddb7729ffe6fbe66fdbc271e137319fe66f0980aaa55454edee577767eeca19a02d42441241040dc0781441e2322124182031a01e0078df01fe3468dc6ee878df1b6b7000068d57eb4001e00e03042c0b06d046877bffb7ff7fffff7f7f55f7b7effb6fdffaa893dbfdfff6dbfff56fd3dfc6ccfff4c33dbefab7d36fbecf6ff7fdb6ffd5bf4db37ddc4e1c3b9cf6298631b009381041180202981c41c492063c061084284184240db1e31f18fee73d8fc0a21f037f91ec6c1c0016506701836b071090788764419ff8fbe78edfbe63d083b77fcc7adc76b5fdffc5ad1a62b46d576df31eb7e66ed687cf00031d77e67774bbfc031014408c04401e0307c2120f1084a0c8b5f6fbfff7efd67ff6dfff7ffaf9feb3de77859ffb6bed4f2fcedbb77fb74e6acfdbfa79b5fdb99ff6cfb064ccf79de079cf7859db74e6bb776ce043a12c0920920820640fc0b03103620c06d23627c8e18f18fe7ec7fbe70288781bfe4763b06000b284a83182580c1b58383c43b224ff3fc7bd6ffeff987c5f0f05aff98d516edef7ff8dd6e34c6febe36bfbad7fe6354cad687980018fdd733f5dcefda018d0920302600ae0585230181e60521b506463ffccafffbfdbefef9ffbfff73bcf7cfd9fb939bfd9bedbfbfffcdbfeffb7f7fe6db7ff66edfb2778ff59edb8310254152156060cdc010f143160308521207c06da0c8f18e31fcfd8ff2c41e4381bfe78fb1b06000b284a8318258183c41b58403b224cff1ef5bf7f98b77f31b87818dddc5adef7fe35a3698df6e377d5b7f31bf6e66ed6f87980018b7eb99753ebfe018e02012 else 0xdffcdefff9ddff76e67ff33fef9c6ff7ff9bdfdbeeeec4fc95484526348cdffbff33fbe761fe0c6f7fdbebfffe6ff475b1bdfb6f76ecdea5b37d0660490410910302191b01b005090218d01a05877473ffbfff6fbbeddbdfef7fdffdbff7f7f6fb7bf5fadbffdbffffdedbb7ffdbfefc202d9ad6b6ddbff6dbbfdbfb6608c42b410c0405904703c8080634060948242080f08171efefdbffff7873bfdfdbbfeedffededfff0ec0ecdfb7ff6ff2af555adecd6fdbfb76d7df7dcdf67fedff6dac88f0258268210100c20781508d88302101f102c84639f7fbfff7f6abd7bdf7bf776ffdbedffd557edbfb7dbf6abda1c0ff33bb260dfdbededb37f6fd66bfeddb181be04b04a0210f13e42189001b01a108205c63d997ebf33fb6f6ff9b492cdf7b3e7dbeb122c29b77bf9cedba6eb37bd9fe7b7acdeb376c31f1336399cdcc70dcdca09a06031408a0c23607a2101048953caa67fd5b3fdffa1f656ce76efb2d6cfcfdbf7cfb727158495b3cf6f7b376f59618e6c3627f39b9fc7391b88620634128154214060f00da8161fd149e5d3cb92ff425701e25b7df24c72e44b3604e0080f03e13e11b430c633fcf63067b1fb2883e06fe4e77027000c40b38098058488384103fa20dfdfcdfbf36ffbb3ffe4f58ffbefdd9f6fac6efeecfff6e96e66f7fe7f9ec333b3dbd37b7794aa9556533f63efffec3fff6519fe7ff31f387904103ee8268230110041180c407810e8301e08d88383fa3c633fbe93f7a599be316310d99bcdfeff9b7767e6d858261bf99b68314310b10a8046036c0107c27c893f60ee1efbd7f59beffe0d9bed6cdfede007e630319ad9cdfdb30268200c08643280d88381f01e22478f8f3ff3fb1833b8ee5107e06ff91f63fd918006205941cc12c0241d4064182081fd147773bf7e6dff37ffe75fbb4f3e79ef3bc6bfe6bffdaaef19beffcff3ece18d7fb7f75e6bf8cfccffecec30c50d3131afafad4a97d6341341140c80209a06381601c0da4194062081db1aaaf7fffffbdbfdfbfdffb6fbfbebfedfebd7d8071bdbfff6ffd7eefeedbbffb7edfdb6fff6fffb7db1df36cdbddbb7b6d80aa82281981b00607882411a0c50c40f44101b680c8323c39d57af7f7fdbdddbffdbfefffe7efbdaaaf5bfdbffb7f7c383e7ceecf930dfb7effded97b635feddb1ffe04b04d0407d83e820c0f01f50183e01a106205c69e79dfbbf35f337ff5957b4e75d7777774d35ff56abdd31f3fa6cf39833fd667b39826a4d31833eb2c918c504d04503500802818d0190608206bc50f8e3e39e9fc4f47401a1b3f4651d040c0940701561207c40a219104083f6fcdfdfcdbff35ffcfd7fbbfccf33d9c67f99fb383e79f3ef7d2035fdaeb365f1bbfe6bf6eeece4d35edeef7bffd936b734983e4d213581241240c08200e06c8140da46c8621e91831)) else (if i < 13 then (if i < 12 then 0x79bb7fbfdbffbbfeffdcdcdfffb67ec31f5fedad7ffb4b58dfdf6fe7b76cfed33ffed9fb618666ddff7b9dddb35b7635f6d2d65ab66904103600823309021906e0581b018d01d0660511b470c71fe3bf3e3f87e91f403cf0eedff1e91f4046001f40548158244843f81dc9f0412246319fece0cec765107819fc8fb1fb04c003102ca0e6066016121040fe8837fbfcdef6cfe73dd9fffaf6cfeaec6fbfdf67ffb5ced337fdff3ff9fdb0ccd9fdae6b6fbff1bf7b67ed766b7d9bf33d8fff9f619b19ffc989f0ffcfc017a0ca08031c0b40101e084a0e10407ca036120fe8e3fdb9ffe6775f4f6794be966fb3c7061d99bf66ccdb1fc74619842a80f40c499406062c24863123ffeff7f9f6ff9f6fe7edbf7fcdcddfffeefefdc7ff99b3ed9896d6bff6b58f37b7b76cf6987ff6cfb66198edbbfb7776cd6ddb1a5b5acb56cd046209608a06c01028205043612036c0ba0cc0a2368e4f2e9e5c97fa2b80f12dbef92607172259b0270040781f090c8da186319fe7b1e0dcee5107e067f23ec7d8713000c40b18049f18488304103fa2007bc003c0003fffffb5ffc7d7c077fd7fae286b6bfc7d1bf7e87bffdafe3ed1bfb5bf03c060196b85a2eabae08213e504204200818d07605d0181e83687f023468abbe7f77cfeececdfff7fe29e9cffb9b77dbace736f6f7fb7a6ee737e9b77ede61b3ec67330a7a164a33b39b7a6ef6f7b64c25812c1180208781606c0da46c4184f91638fc71fa47c523e8243de91a475047f010101e704b0040648644121c6319fe76308cec7ed20f819fc8f63d826001881670130091b30910807f441bfdfe6fbe6dffbb7ffc97beb1ffbf7dd9fb7eb2954a99bdffcff9ec32cecffb7f4dfabf8ddf767ffb759bab3733ec7e50cd8cf3798f21e728268190041180c405702e8301f01e88d88403fa35fff7ffb7efedffdfdffdeff7bff7effdfffbfefffdffffdbffede07b02c6eeef67faffadafffedfedff76dffedfffedffb6fafa77dbedfd7eb7efedb04d0360082191290c80b81b418a18882078906042908036908c89e39e3a46291a9181d2491a89000150774312360fe051cf8c72c41962c022f44b1603000d18040c50d041214fff7efcfffbfdfe7fffbfed9ffcf9efb1ff776ceddf633f33ff61f653aa54a7aa54a6f7b67b7bd9bb2a99d8e324d8fe739fc7093886806802741341008c04681403d4060f00da8162091ca736dffdfeff55b3fe6ffda8f9efb2ad9cdddbbeca33f99fd87d9553d52acab679bdedef66ecaa33b1c659b14fce6e7e389b80ee8614120614208154060f00da816209165c17c7fd6bba6ff6a7ac4f89bfb5e02975937ed60c60c3815a09a08a06017a0303143106d89739efb9cf7cfcff6ffb87e7fb7c0712aaac8ffc38fef9fc79ec883b02432813d84810d0c40d902c8da28fedfcdfbf37 else 0x63edffecdcd9d85f99870069823304701f0120082bb07301027818a18c6a73feccee58b7d8b6f7b32dfd90fcec5beccb366ceccc0d282180683a8080c50d10c6202db6fdbfdfe1b50dbefedbefb436b5ff6d56b436fff6dfb6b7da1dd55d57686dbfb6fdb6b7dadba1b7bd6f7b5b7bbb6b780f33003141140406141c861c060da816108815149cbf8c7d99dcb2f2c5b7bffccb7ec83e0e62dfb3166cd8766384620f23640f21103160f431882f07e1d6bbd3a9bb417c4dda9e052eb26ed6064c1cc602e06248c8620db0ab676d6dfffb76fffb7dbf6fbbfdb7bffb7b6fff6b6ffb7f7f2dbff6fcdb3edff6ddfededbf6d35b6063412c11405c02862418c0219ac1d41848c1c61a71c6dcef99dcd992f4ff36fdfffcd9bd87061d97ab3e6cfb1fc766445091901e8082189080c58390c625b6efb6dbcdb6fd6df6fdb7fdff77ff7fffbeffdb7fbfdffffb6edecffd7ff6dfdfd9adb6ddbdb6dbedfb6db6d9adb6dbc11a0f60d603a02c018462464362368314318c369ff369dfbdbff7f66cffee1ff3bfffb36ff7ffdffbb7defb9fffb3fbdb7efff367fbfbec91b3f5beff7ecd9ebffbdb123218d0160084f42310709041886bb0407184282ab0747bb6bd77ed7afadfedffb7dff6fefedbf6bb7ffdbf6f8037b7b37fb6ddbadb767cdff3608e0324660e6020ad1084310e704640a8b36cdfbf35ff9befe6bfdbe66effe7fe77fcc67ff9bffecf83ce79eef480d7ed6b365e36fe6bfdbfedf664d35deefbb9f64dadcd260f269c08208202046a12c0e20e00710440a06d4310f48d0e755ebdfbedeeefad7bdbfb7dbf6aaaaf57ffedf6fda1c05ffdbb59bfb7fdbff69fedeadb6fccee193066608407c06a0620560e10810404903421240a8c2fd7e67fe6eff3edf377f37b7b3fddede3633fefbff8512a9076eddbb651b6cddfdbedec9b867be7b186db31a9a9a99254d4c878804e0402360700208201ca18a05071c5b6f6df6dbb76ed6b7fd6b6db6db76b37e66cccccccd8cdb6db6ed6d99ad6ad6d66db341180c402401380e83302e1ca0ee1f7edfdef4dfd9bf6f8019bf7ff00737b337fb7d8666331e0450302285d85a018902a02036c48cfd3fc4e8e801efa1ed1e2fe8e820066107304b0087f13e10c882441bfbffcdd9ebde99f99f7f3c6bff9affb57fff8fff9bf7e66ffdb9c38e434c66ff7f99ff7f3c3fff01ebed57cae3596ea95675942b48d80588248238040d881848083683280d0c44103ba3c7f81edc0001ef68d1be371f40fe000dc771adc68d15fa1a01200dc0181601b41981406d1036620dce2e0121f48b9c5c070007727c434104843000031f02282914154000000002282aa850801883e41a4ed27ffdf6fd07dff3efde0239fdb7bfce7fe6047bf3c73fb3011e03b01600e05023309075a1a01b11b459fb7edbefb6ffdffcf7bfe) else (if i < 14 then 0xcdddd531b7efdbcc37efb76ea91682ab5684283102c2101e102a8461de65ffcf61bfb37f23237fd9bff6fdbeffffcdbfdbffcdb59adcbbf779b6062058423420c11c0248c862c020524184f94231a67f8f7bb7fef303cc10edfde637f0ced6bfeffe341a637c1befaeddfe6370cddadcfc74fc3ab5d74c68354b6a818d0920080cd08106605842886836d08c5953d7e6f7ff9befff95ea57aa99ffccfec9639f9ceeee482f7edf556cee37bff37dfdbfd55fe737ccff99fffffcb206cc6e48739b848d81241241040c07246c06c0168620f68144221c71c4554c5a63fe0600a637edf8622aa0b54e3b83b755698df6f866fabba98dede61bd6bb76fa12a10a0ea0c40b40aa11877e67fffbbbbdde7efef3dbecdff9cf67cf6fb37f6a955dff66b9deed6ff66f6d961a0d556908e04a03b0281b01494283e107205508c598eefeefe63edfe637f80c01f7e637edf867daff8d6d06ba6341b569c75d0e76ad57de636f6f30ded6d76818d0920350808750610703c508c4960f787fbeebb35be9760cd6fd803cd666b76060c605381008c4180f94220db0e01c00e3f0514515438fc6d540000145555380c1080c411a100f3eeffefe1e1555f5576efe1edd543cf800001876eff0f6eaaee0edfbe1edfaab7037000018a1240604ca0c03ca0d436211031890f00006e02a82aa80ddb55000000aaaaa000f0181882342013ef6fdfc2f6ee16eabeaaf7fefe16fdba84f8000000b77756e07b7be16f6eade0cdc000001a60994240781d80f141a063103c718e31f629c5162c50f070c10314463f01e901a02c0f01dc1a70c483b7ef91dbdf237803bff7c8dfb7801008aa4a3b77f2376e3714000200000180d2406a12085e030ed03106d88200803bc8a04fc0ef91699bc00200000c1dff228de37c1dc8a66e3723371150250f4e030ec031084870801edf08f7099ba8557fe11bedd400000018046eeeadb81ef099bdbab78336e1a74241d8c1d41a0630c9beb7fedff6ffadfeff6dfb5f6fffb7b7cdfdfcf6ddbf36dffb7eddbadbf76f3ef6db04307701b0130089007987186b923218c59bbfcd7f35ffdfa66f799f7f98d7ff9adabfff8fff9bde66ffdb9c38e434c67f337e7e180d7dff55f2b8d65baa559d650ad016208e03e01e00a1220e128a0c20d4311040ee8e6feeffb77ffd6fbefd6b6dfdbf6ed6ffcdf7d9999bdbb5bde6dbfb7eddadb37bfd6ab59ad66661fe66014013003e00036a1200dc0be03a0cc0a8b4d266b255a59ac7061666b3496585330312494318323c522a98add4000000315bab60455550500000015e030460318436bb66dfffeddbfff7ffd7ddffdb7bffdbfb6ff66ff7fdbf7e9b7fedff7adb7dbdbedbb7f6ded966d818d04b01d01301700a18b08506300b0709012307d071c78c6e657e3edff61ef6dfedffccffdfffd81fc1 else 0xddffcddfcaa955533ff33f648fff37bccdf6e4877557676377fcddfbbaabffe73b99fe67ffffc903b31b9219f3709188d80588248208188141180db02880446484438e382280003ba8a28a7d800005451545146dec5c0be00001c0a0460360677e77d329dac74ce8ed66e1e58ed6676b365980b108b00a1a508a18c31ff3fe3fbfbedef303983c3edfeff31bc311414fc7b83f757dbb98dc3375777dffefe637986ff57eedc8a0aa55683004c1e810d02d04c2101e102a846288360a98dbde406200a98dfffede1953e3dc1f6ea98dbbb7))))
def level12 : Packing := (263,3,9,0,0,17,1,nd12)
def nd13 (i : Nat) : Nat := 0x3679ff98dbffbfc3cc1e0c6dfdfedfc33ffc6d6bfed0698dc1b77698dbf7b7e19bf6b731b7dedf30df6b6edf31b41ab56d6862890230090a8821c860f905c1488c6061f098131b8b154263fdba81f0000060131fedd5b0098dedd5bc19bc0c000c22406a1981a1a18c336db7f7edb7dfdb77fb6effb76d6bffdbfafffbed6b6dfffb6ffffb7dbb5bf3ff6ccffeccccdbdfb7b76b6f7b36dfedb7fdb7dbb5b66f6d7f5ab5b59b6d6b67edb666631b3410844048140280c1c8708c18a2505e06864151edff6dbf7f6db7ffb6fffeabf5adbbb6efdbad6df7db7dff6faaddbf9ffb667ff64ccdbfdfdbfd5bb6fbfd9b7bdb7bf6f5addbd9bdb77edd776dd9b76ddb3fb65998c6cd04a1300a020f416188f88821c8620705468d93ff31b7dff31b77edc20636dfedf6e3ff8dad7f6b4698dedc6def698db7edf6e66dade1300018dad3356ada06206413044030722505e0636a1916db6dbedb6fff6dfffdb776ddfeddb56d7f6b5b77ff6eeedadf3f6ccffb33336dbdf6f6ed6ddecdb7fedb7fb6ddadbb37b6bfb6b6aacdad6cdf7ed999b18d9b4128481083403070180506305a20864151a1863f981cc6e131ad0fcc6dbb40f0003003007cc6dbb5b00d8d6ab436681800c30425084180143d0c0c61db6dbdfb6dbffb6fffdb776ddeddb56d7b5adb7fdb6ffdb6ed6fcfed99feccccdbefdbeddadbefb36ef6eeedadd9bb6bdadaad66db56cfdb33318db668250982108805010c60b1f10e4320a8cec7d87ac181b63d3b9262000ffeedffd93ffc0fff71ffec3ffd47ffa0fff21
def level13 : Packing := (8,2,8,0,0,12,1,nd13)
def p3853i6 (i : Nat) : Nat := 0x9
def p3853i7 (i : Nat) : Nat := 0x201d
def p3853i8 (i : Nat) : Nat := 0x181f100247a439901
def p3853i9 (i : Nat) : Nat := 0x500440a000284f412889610896c100000000000000c067414628009a000290142868872034003d06ec13000381cc03801e405d002710cc0ca00181dc07c89e1063c069083885b021886001501ae043c04e084809326600bd40310c301e8159045812803c016bb008004001082217404337247002
def p3853i10 (i : Nat) : Nat := (if i < 1 then 0x2c38702fb0104c05a00006602c82040000e0ae8427454f38089ac560121939b941eaa0e907027000a5177d652a02f502f000000000b629dd88100e02057e6147802d984a60d3fb28481f742010c137791614a9825a95420000459ca008a211000909833782480000b07f48b36d81aa21b703a9b0ebc1b4a0b0000053164425820d6000068067804d20300000404fc98092106000040a2fd0a3e13b00003841380e6012e307bf80719e78428a42a21012bc1e180222048984c80199223a00000000281ce62e3d04d881bb413e02056099f8be940c7e0e120500046b4a3600008a898000046060d0e961a4a14b5807202f242488060420eab0d603e402cdc8f8e0c74053384640256431290040c1e80000c112161e00000c25ec0100000280255854210e97a17051dc4c4203d728650a02c04ba0db30543120aa1796c26000043046d94420059b3880003419c84831044bb81885c1acea615a6011800000526d65d8000341da8072009b9826a061a0000eb26688ee811c0000a292502fb42110037117db838d8431610f5343c42f4000100031049800000001a0aa00000000318240000601b403080000e261602a591f8411e000060005b0d40001e13ce242b00abc1e20000807e08a1b44f4452c80214009c4183c05cf056102e30162809ca23dcd4fd40cbe076007ef0a9782362e3520196948c000000000000503cf407c2513901a1005a417aae6050a3630cd9834a0c5b00d799b74153c0bb6086b8077002900e59082e921250980000309c9023005a100352064c0452c13a0000000063c75049480fb000060405028202ae0000281214a85c03ad0a10818280f782b5062c084d2980cc0b4f121681c7c1a9f64de036604a7847800d70101002dc80b4c03300002005f045d00581072614dac24f6c5500658000300800000000030086012480b5a089900300000023957348000198afe2d8a04cc83a2984122b80000181640000004c6033f81a88086c27cea91409f5421685253041f0253d0e1851ce60a08c1a458f2b292045d0b6ac15fc03f7084e021d81a0a0297076581e28270e0ab100398af0422a42de000078323c058405d201750b3b5c41e10cc29f031b41e264126707c3847f0046c2b0108e98bfe2ce0ec15c61da84eb400dc0c320600000301b9c203e02a93062510d80f2d08bab023c1734028178f3b08a41b1a135702b004289924804003046818002000040220000005c20008044000828b84000c204020c1800c1020e000868e00004800010782003a1801028009000da80000078f0c689010249f110e08a8120a0526044838032083002e48686002820310143900c08401281400f0002e03100c18024307160015e030c55188002c89220042161c700012ac091000dd5811e08190120008a160c61500140002300d08040c61120180aa else 0x200f3606300e0412f884a805fd593fc8ffee1740622032a856d4084853d8848dc18d6c17804c781b400016529a02838ae80000a00db0480950e0cde0000802880001186f013620092007885ce0000807ceb064000000008023901fb44710c2955896806d850eec2ca05b421c7c0fea06900002850180972527e00a880124079601390569833f00d0168c7042f0289ad1640faa090694d14a64c0e6301220b9141bd006f862a014f78223a00e5427c8b3f4164a0a570a20849700030074204ae82ea5e80e09600696214284f6825f00520300941e84304b60df0376c22cc0530044581dec0720000409f00002c238e1181031230e54245a08ddb270d92b0250828c6018800825857903690273080000000000a035930910562607900002029d589a62e10050f016d981700642098c0389c5734641606a88202805780eaa61b280ed00cd4481151e2836745aea11ea027c83d9802220527296b8a900001ec860000289e18a340000f16fc802b42040000816c80002c1d622bf01728000141de000000308850dc566008a2151e11e9c558c09ec00f939a0494500821024e04a81c38c086c051a8380c28aa1304b28d19b9420662d3909ee8346c1dd807a1026d03fe01bf)
def p3853i11 (i : Nat) : Nat := (if i < 4 then (if i < 2 then (if i < 1 then 0x3ced00880000201a53054b00bdda16ad002728614003a0603d71ae9b560c62bdb8044f427a48c6f000a0c002503002a01150004100a21002302355a140004002903220502000b000017091000060000010100000107470003010b45000a21000000170c0400000036171f400b011a0b1b0d190500000004080604010102070428090e060005a404cc12110500000700040601200621080800000d0f2c02280002130802020202420201000b004c0000040502062100205f0c17000104090029030004000204224b01001604003604000a09021d010a0100000100000000051f300605080700003a020d0f008700000415001a0f1d020403170e0701000701024005010206031c100001310d000807000301021f0703000002200002011b001000080118000001020a312d01070c021e010b00020b00062c05010820030b010f05090309020428000512291b110e1f000203100f031b0000000000081d000100020c270b03190108201903090209160514050123002111172900181f0f000e1a052b1e010a061516030908000101010802370300460f32121c000003100011001e0602000100050f12131113d30d0401030d00041101040400000001000d1d0a0d0000072f030008132507025805021d032301000508011300030013020d0500070c0207020e000409000003311d000313110209010002010738001c432c00060504091308151916080002032d1a03000f00031022040901200003002a24000003040000090100110814020004100e3a06230d00080513000711560200030607000e02190010000f1f001c43083111071a171001603a027201030415000500001f0b0501000703051f0200021203117120006517220f0002017208000002430c000112021505011d02010026007c030e97190d040100160000010b0400053c0507050e05200017005b000e0227162805080a0707021101520028120c0112000609850208080008081203170603030d0a0001040a0a010200670a1d030e020010000a2503180930000000010001053e270f0b020b0c0a6f0a070f000103080921060c001f040f0304000502040404070403111e02183508000100020d1c010b02060101061800031103001a050608000501002308000504032220002e060500072048040707002400043300000e0500050c2600082110200321050000010a120205080501000d020600050000000f0d26060f20010b180005060803060e091143bf030d2e050f22040c170923000a0300000111000e0710010b02003f0851351f0710160f0312020214110908150600250200010017001a2e183f000103210c0003081109000302020e1608070607030212001d01010000560c000e07230507141d0e001a050e00000428040003030401060001003445010001054d000000000a else 0xf0413067a7cb3490676d6b040246fc1b6a82bba63e74c08fdd814be16402df2137640ea12d494624001528c0edf81107021bac0bf82bec82895081f3527c813d283cb00c70e064384c7e1630c7c5c227796aab60299b63c380fc944e3d30eed182fa02f1819fd02dac045f40f16184e782a9d0af4006a301b7c809e2026b4c9dbd84258367c0338016f442086864e8068dc087340196015c00000013aa4030b80da9654a00000000000000b02b6000000000586466189c016b8e1c0b00d7b61beec23002b5b86371083960f1182e2d835160bb5c19a882f58000077abaa10be9a6559abe00001e0dadc65233e1cb61cc2d5b806203835da0ac301a085996d30b587241c16375d3333930d03670e46bc1bc680bb105d9c02d34695e138222974210f6c1f440bf2803564175045c83051ee00606c0f39855382cc717c8e033000003302ac16b000c1781700b1a250bc34c3bf1ea830677b087e00000400eab10c0000000000406380000008ce000000000216644094380655989f285e4a012ae03805ecef04d0a058240e3600ec58059b16e9e12b302ba03206b005aa10361872d0215607ee3529118828b07120906c0c75d8e6e851b1029920e49c191abb01807328124d460c60cd5a634a763dc80e0c4485b62e200001d3295060ad0940865e2c0b1583df311604415c00358311b408c08d1a2deaa2a2be0189ea0b7c2d6d60290d2227a74fa81e86308100c5bce34bd83bc93e02795ec0097c23e9b9a6a0bfa82bdf42cf286435031de12a442d250d518a978e183445bb60586778c2605b0ddf2a05417005582d3c00006807e010d800002409a7b2a472b38c30d8624628440217ee00ca0000068466c04c8000030670b0248f07f5ed303d82280000000decd6b058eef85583616380ab00000305e52608914b1400f9e038e000010c7f785518000070cf242f7fc1e6b834de022e76e65593868471f70c628b7800000312900000d58a242c7080cd00001c272ac0670563760acde130e9c616387d062380185d8169a354e80b8c2d5c8803a580a7207dfe09efeb1500232116ea8f76f0b23fbe32b2cf0ac0cc40c028cb500000d0557c0bc701f2818234148440f0e860671750ac6b00000601e280019ac40c000048431601fac585a80d14064ab60d36116fc4c5302db0726ba10dd01bfb80f210047c06ed4cb5c8be3717c5814e698ce6b037660bce651449c4680b8801f3818a9c30c60213f05f1e184e41848b2cf707c56046f41bd031a310449816a8401e48d0c9040a2354b8d4d6843b80b87ec9e602cef83982069c4e284011b901e982ccee04c202d0331b8361b28e3470046db06fd0354a0f204074c85a5302afac7aac251b3e2f10657c04ab0130c8373e004f6081e4332892955000fe0a2081d270368343fbeca9d801b0b2c0f183c0000180a87) else (if i < 3 then 0x3a066858b833da4b63ffc15f18168c8000820b92097780ece8049b44d9008f9820c5b027d0600a2de183109307fd04a74c1d441749307e00000b6a2c44388b46ce0b85ecceac00f2863eb424c141654197a01537017d6c51f807f5827d117466364c40dd5807500b92019d0c040f03a5102c720e0e6d6dd829c805e9230e841260291f6090e2045b426c302974238600002c2638049547350d56e40000785ad70387839458b250000080016e078d8317684b5304df4075f8286681dab7b5a000031f0639660000008059ead360b07bf19c60000342b87319680885accf1445db8598f552dc08cf1847e9ac9862332c0c041f1800de5023b80ae1288f8b963a049fe4e14c0a5a3b6e11318ee76a824a284dfb08b9a179a04fb88366204ecc0c188042b210f50859e0390000079612961356062f5d56eb200111e92066d1ab82326b57a75a11e8c165602b730994e17bd18cf8865e000006000401726d86b617ffae17c000020420668d4a245a427f6855aa060e60bd42dc91912e00000000035cd0d31c20000001021029888139000000000058cd00000e73f58030280148000050cc46c1c382f000000f031a2c2480000205a7cac62000012dce80000b021c00000000000000f08a3213c400000000000000000035ab6085f59013f81267c010d002b705d5a32319eabca32e60a05e0e4c5853000000000000000c42608b8a00000000000000180df0000000002ad6c831bd0000160416987fa00f4514d72e1bc6a5c7354bc64560000085e20b08d00001e0551823f59a9db0626a0b791f3133136c007e00003c1eb3007a418f4218ae5dc99822022c1de4e0c516e630a180137419c3807710965b037320e3e81f6605dca030fe017a829fe0184509c704f98185bb8b94809eb01038c14b4955b20c17c1720817ce015800001e134818d37051500001a089d804000000a0abf2323dc28b8051641732609a4593398242e01a2e0e7c813290d14707d24231a830dc8257c06d48163302af10568e3a60c083602bd8b237e0c07c165800c4d819800799003ac806ec32a10000000003408ac051250ace4c16781931ba95000002e3ea4247c8d1b609d10151e80c470c033013aec21400f6c007ba0674a2a748051b025610a44600288b3fd0186d0341e098081311306ac00bb807211cd739610602c340f9d82727828d301df204e1d8e56049e80132e04b2c0823bd94b04556c7d782711bd837ac456c01398c2183dde07c32020a8b31b03953093fe1624c14630b5a70cd78163e9c519863c317c140dcb6cf5582ce2041f830fbd8c75834f0012840cbbc09330c3f46997a1447c0ab1309550a6800003ea512846d90c47c027000003042860294c068702a6102f310a3a000000000200b3a078f4c87c0000508a5b0d0600d2746198049bc0d016e270c0f2403ee else 0xc9ca5a0bc7ab0c20e135c984400000a0cf6602f542156883390b380000000000000010a558a5440000382c8b1845ae9a711c94010ce076e00000830ca857e3acc9a2acd48c82bdc00000000000c3005ba8e8353c82a81cdc828c32602762c00fc4b5c8dbf1035961767012a000000000160d955d91401e710667e2fa10070a0039f2703af2121f23abd39a7c03e0b5780c2b8476844db81900981eb0347da94a60bdb400ddb933c31ef6583c000013211e442320e7780b50393bf0860a31fb810da399ca074364a53c062000673607000001d8148000030ca4ec2eb018f803220000000000c10b30a7c8295160b899811205e9068d2813eb84e8b82a01b66462fd2c0bef83aa000000000000003190bb6a6e0000000000000000001216d40000000000000000000000033ca447c36cc4fc4a460000090b58208ffc0b4bb25d0000180b08000070086b128b358b6dc5690c8100000ec4b558e4301dd56113e118c018658b9ce72c141503017bcd48c000012eaa6c2e258b9fb0323ce264df30183fd0000036274c231003ded0857a2c62116d5857f30038405f34b358000000000959c580449ba71109cba6a83863b303422604c42550013f001ff70b67a08c3d5118000080be1b016d818e00c4660b46a19b4c15ffb277827c2e0ea2010d399309a709c0ee346625958af0c23a176d057b385ff918832f915599608170f60cf8c30f98ea7865fd625100dd584a2531a100000b69ae4641803bdf02ca00bb540368a2ddb07a6e0b98c10600000000003588e4251600acb68d6e6e7cc558b04e956a3360c540000203db35c252137045c7fb99a309e06323b46884029de0904000014653e04cd00000230e4000000000f028c6123a02a8800007064e15221c1e9000001635bc0dd2008a704170666ac2dde599dcb0b8000010164000000000070a38a08ad8182000005173a608189d3298040d80b2a15d6820d48664761512048a44ae604bd1159eac70fc1f2401604032fc1295dcb0b0054972af0d59c2a59d01cd207c12f73f02eaa847867ceec29b6429c28c7b2051c81248810078026d7c1722b0c024590389a6ada8c314d8dbe88c5d60dc207abc1ee3d4ba419a340556804c5d4a6e76df6032258c6c147b0b4eac0dc781e4a322cf087d602229ee1ab1f7d0c0ec0fac432a4838aa047463108ad97c81d1cb31c427e75da6c14b9d6924613fcc047185463162d814538220a028f00896c1275996cb029bc6129d51cddf1a758c630a59017fb11c7f9d355184600002829180000f60f5610d8984b8b0a900aa8c0af18228783367011fe0a2d022600000e0949503e40a5da1965e01542187f815839b8f000012056782b4a300ef08444193d422368426b02fca097f044b803391034a0000200e10863f9037cc0c96c208d03edf78e4a0d5082fc28576e025)) else (if i < 6 then (if i < 5 then 0xcf800b9e030423362406cc0dfbb258a66922029d7050a122686253359720b16840cf5c111c84c580000702e2a0cb10124a06710000040a285a64883bb000004c2d1580480000c07b000001427dd163ec0526c038a181280000c01abc0c5840e30000060556c08ba4b05902a60000140b5f9970ab0b300000000035ab7881b850566c302e81eab21ea50a1fe19f700ba1892267cf7086ab1821cc8a1702756e1e40142902a700000c02cbeb20b01280000083032edc600000b0ba52094b824348bc5dac6c602af060e1b2020000000eb4000000000b027e411e6c01bfb039b068940d07c091903d1503e9c0ec7deb0104f226048ae2a0000030452e61bd019580302281ebb1923cec53c02d93c7fb067b204bdc0f308364a0add8cba76a5ceb0d56043d40b2601a98000087b134d5340000000007002120d5f6a3dd8491b07b4e6a7e818770444e7c6a00001802543e33f7c6c019650692085a270892e01fc980900000102c8e0a7c000000000d0b32e18ea86a780000a0b8f20bad42dc7bdd52066e419550663a85edf175a80adb80922d4bb611e26f21f8307b83b6804458053e427bd399b9182900517c0e048509501212172bc042082e120778c0bee8165813e4e0c89e0cedc658984dbe0875a0bc4dd580818fe190e2869000000a2db00000f04c8000048370009133598fc302d050e462ab68a2c00000baa6a60f8e298945cf70c5fe04f200000802ff393200000419d6c11a280fb20c65e06ff40a100172f14dc00d7f5a36e3d932015a00001d8fb730a3605b3601f2014aa805c3088b601b80000304cc306f240b180076bb0463039cc0287c23a0846ae620ee32ac40f2d54a9c0b07007a042d43018ce020f801c4811e7800f6077c4c39cc240c85e36034600003c1d5b014076144811efc948d048af08916140e04142858237c44801b0c5ae385265006a0f7b3acd64d4a1564bca16e55edf181f7f18ee000010131c85af318f8447bfdd91d81ca31018c05d9c05d0000090bafe585702b6800008880a6348800004862f00001601a000004856f000000000280b4031de21275c65e40000251c3e9727e16f2c4c8b020a060e80000082eee8055980b88147e8012785fc0000000000d8ac1411930cbbce1b800006ba23403252c97dd8cd800002058eec6bb18b04024322c3c00003426b5811ec75e9c01c2c18d18d1db7509a34b200813825e063d7602c54b09a0056d015de0e731a7380000b033f0641781388000010828e16a558451992f40562000004026c0bac30a6f0c063005130c02c0bd400003c268810f950aa4219bd41b748390b0ca72189ac687cbdab82a746e0a29c89a09fa61ad5c0a4402fbf312e8409a000000150f8c714078d8005fc0a700000a17cacca4a02581841fa023fc09e341e100533402426384b0318800006026c006 else 0x12d00000a34449e56d03f44623da0c5205f500000b62d4405ff4434109c17047680e0501ad5830a66a76000000000000004b57c000035646581010000140860c162780a850ba30c0ad020deb05df60d1007fac1d058bb4e18038198302e858394407f0622afc1f8e3169f04b1607c380732845336473c0ad31938a83bac0c99811d721c2781cb96623c1732858cc04cf07505a0e1b00d480000110e600002c02bb3087c008e00002413fd22614062e417e9006854039233e0605bbc285dc487a026e0000041aac8d9af63b5a248783016b53641aa16167e0196e13847b1de4119005d173849e084800003d889802414ac8e0049c181600000a1350000006aaff3e6600b9b81316c21ab21ca862b5a080a2b0e3002ec60b0e162ea4b0a06631190060b16586b1b0e2c06208c26118abe8caa202414c6e6431b282392091a60d8dc0497040080b2944e27c133f831860611a0a10033f5b016c623400001405480000274d1629f744df7b01eb71a600000000028060b17e7611a7c2d3280d8861a2c018800000d547e6184000000000130171a58e0000258a90b1b0ca969e0f2841f3394afa2c4200002181d2848471a6094b1ac01f31136208944e47c00000000091248a0b4ac48730063c7ab94022b4297a854d9606ce115b1886f02b50000000000ab10d80db50b11c091b422a3055bf62710306644f1b0565907ed409d6dc4d485f361a1b04f968002b01b6e08ee8cb97030ed8650661e40000142974039bf055e2078386f580000000014030c09638a19e070f8c14d9eb15c85595331cec6c982e080000100324146480351ba1791a39c0ff1410a48c49964b3c1606585380000e0636000000000502870000100c80403ea1124c6268a17c800033910ac72c56ed678d35cb26416021ee7e0031aa81009424a414efc658102ddc7960a3003813448053606bd214a1c82d48c38363fd4c1cd45fc385b6009348e28b129a93310333d4e149c18400000061664a0fc000000b29a0000000000000058072a1ad00000041f2e0c0a980ae00e58c2c3a8505a6396e0eb102aac81f8e0bd9430188230a8573f61a8603a3181700000108aeb5919988bb3115f0c246cc3c81a28000000001ece69002d182ad306b1c125f40eb005b4f1582000030016431dccb5b06c35c82880000030555832ce0190985ba60160acb0e820310ccb729176149141189bcb8a09018101c400ff8630100260000118ece824e6acc06330ac2efa025c918a2500fe188b1b014b78edf522c000050194b0368015216b3d80000000000000000007862936262612f28159430830038ee2b345ec428041403f36043c0000404cb50c184c0c4000060434263f540946513598c1a31b800000318f3982e500000000020198e84a751a5ae41600275b31e8805ad8155a0041d01dcf7b3f01a072d) else (if i < 7 then 0x420c2e6b433e5045840a8ac318b58761b2e2b0361c2d39c5d5884da5044ba0d72c039a0b7bf041c40b3d0081d83800084ac012280af10356e01d80cf7044e40bde1000000000000004053d000018012d913a80b8c00001405680d4d80000c1a4360c2c00004293b203d9e00ea420b00000e0be8000025d55408fc108b5632f9da98800006015f416ec0000300e33251400000431a70091469915625000005064d30546000010205300fa715d596b2400000b32f4158560259116c48c5200001027009e3b985631124c000000000402ba00000000000000184b400000000030567103f5b2cfceca30000000000d0028403189654c81b77044c0000c0000305a1e18e4207ef8298230d8f7cebc0757825c60c3ba01960000058ae0000070be3ce0ac21c400000806320000102fdb0143904da22774ddf11b54cc0b9781155401eab3eb300a52c822014d0b91200001a2256000418b7fe089b0270fd88fd0999a0965440f5987d402550b3d3e1310831468361b1158e14060418ca33162c1800a4b05798389396032e1577007508684d04e90319e6d6ecb06b309e6601e298ec5021f60182811644312c058472c378211c00004054f7b72ee0f04c14a7bb2e57c464c523c028018ef906c4e0caba461030f1c005082d33026f50627e61610e3e7013508272a194c015105716905d6262c720cf84458b5616c05fdafa0f1c7900229c762f4e29c809ea0c7f40c8a60ed38205e2be37139367560c30f004f800842619e0c1895312bb0ad5c4f8a01c43b167209a70f61205bf68b96205b94eaf70206184b350cb0821eac0fed3135005a900f0f8008c061c90920686b1011b28998b17cee09af02d9285ce202e68064d44afc5d2fa084f82f1b4304030f00151b2c34885ef7857140a87a01a60a5c41b30d1217001e605c400000f035da09340000000000000062e0183160000000000d69218656900201025d0f734daba800000000000002687c80000eb5be00001180442a12000002335a81817db94c0b36805ac4c9e03872460ed20beb4049d8553a07e6c0ff800003017a903a7e195f0139f08948755c4153b5809e841d5003560afb01d968b98602ee0c6ed004d78d8f07613222f300a4305cfd0348e18ec98d8bc8c3080b18298cc1eb98508414dee59ca4141f841e618096335f587b784b1b0773f00f5403b484c6005c68c453c1d13824b202bf082804202903bf9055cae13fc2ec4835900001a58241ee2a014d70c124108c000048106a2b1661273eb17f05bfc0314c117d184ed80650016e0c392c0789813c402cc2c076845025b2dd63f000000da66e3e2d10459e0231adc500000f09a80152742cad0ab4e6ad741460000000000863d820190000070152b08bbe029541bb000008006800000d196784abb0233d528d04ee00000d0548c0e681d5e50 else (if i < 8 then 0xec070000038666000012141b9e591905b00001ac0ca823758667376f000001c457a0413b2c2880c3682b000000b1852c8b7c180543091706d368e68000010c2450ae4c2259c21e00000862c56e2f0000000000313d52c3e781c59033c00c497586c194cf8223217faceef8833730043e038a0150b404bd80ff60408000034219b9a9906266a2ef4815140535a0009000374257e32e0401a460d6cc168502ee0000000002c0a200000108040002400000000000001a125b41cf00000000000000381b6004a8d03f46046ac0baad55b31a3000cc1c31c90281e05e1a0c3cc05b08c30201a8e3087d9daba16bd0cfee0848019c530ca762c30104ad8f2b15bbd670300b3741f5730ed977026136601c8c84fc0000100e98017e9042ef6260415b080522017b2075c74f8e584cb04c920b2e6ca04c065605f93066b80dec00c19b1390007160928c1ffb03fbf024b404c8d1c6386726034e2228f4324702172297840c79d81a94024d62a3a58fe988ec166af6551e16144201e990806471c0d014334d846ce1246a8e83c177b0c6be0709617a0d8963b00d462056c4ca8dc5f837d4053de11c382a84038c201f16eed4822701921c0930c32a6813878649f0c40c188b5c35584fd902238113ec1819847c50954c1946824415b98d095ba333602df4b0d3503626c3cf411e805b700852404228018ab1c9418f236ccc90a660c84f18e60c0b4c1b061618f131d4158adac9a8280961f682efa1e0320513b7ce26179cc0f7c85f690870a1854983e8042d28082421a7029e0b0962074fa02d601c2fa0299080381906c043d8228d022516b7b41a808485b176b812dc817e78244b70cf6332b5971c82d840665807f242f10038730c2dd0150c629b0557c0990e18cf82bc23c8300918209dd8098c1a90009ed6309605cbd052bb69156c461859e0000076bb2a11bf02d828a90671010033e9ecb3819ea7bbee14690c8a20419101cfef68081fc9db9a00000827100caa09ba0914258f769d808ab0f4c6120c035910f4a840432ce0e564540e4a091c20025013b9415440c552270e2c3800000630b9c0bbd616030027a059154a7cc2e2dc26ad928f8035feec1f04208b1412007620063425f904e0b0a1b2ca8a813635b350096c6191ce5646b4cc8078140a63011c4053ee0aee809650017fb02806ae7210e6807280532e04a0a1629ca59f05b17001dcc03d6cf813485909d8b58e88336616176198d6c80782cd702e78113ee12bb8404d00f0c03dca07da411a981c420a5a094bc98e6205c0d12788f17a002108196e0972e164c809f73100db741e133981e7db2bfca95f665e904e300b915115d601dc0642c8c4d806494054581335001570747e488dd903d8c54a60e5404ad609a400dce019200df9857aa0579503bfa6a73d810e02f2571364c3f498da38472b else 0x10668f76ae213851c3a5b1f9d138522e368282403afb08d1c196e0141581a6fb721c11cc00001c95471998c0f65432e413803101560e5fc1a5bbab23033200000d87400211b0686200cc00000000070cc3e047244c6e31af461f002e4b082cb037c45387c31d71e49681d2306688f29c00000000096673400580000182c3c18c20000341c123cb6804f9e8642a94b582b942cfb01968181da01bc006a40000201bbb860ec0410cd0aac28048046c15d6e159200f8c04c1c62b25528000dee0c1540975627154b06c819d30603e3043015ecbda2f043aa0ecc0000201415018400000000000000c097721300d87bc3e3110752612f80000000008137f85919c204d024000000806b606e100000400b164f8d1ec83824567922807d5865c780a0000018052580ef68601406900000018af3004500001cec295976204e647958000000000180f33171c00000013730d69507a9c141f90d5f086132c9016cd3c20a80000d7435eb29881d8102a5e09dac05b4007e0b08200001a20ca41948a3330000000003040180000a2b736f2bbd198180bfe1a4a000029ab8b0592160d9a0425980f98b95e61eae110cd910fb002318b7c13095dab00000300a2e139c00000b56817a70000000000702ff6039fa051dc2e9d309b00001a03dc00000000080005ec27800006863d00001e2e4f84feb025a00001619cf6ade400660000000001010180000a02bbac654000058133000000000081058b30e205800000318f68000074acf608b546303852020c9661571c08c6164c3076ac92189ca4e010a6446a00002c069f0529e09dfa523c8085d80f6108bc60130023fe06420044380314c10c80000d0864a080518368000000699a303780dad808bf06237582d8b0e200a68324be37130235e3825202f3f6b708253482e8c0398e3560048bd84f900000e096cdeaaa346e90a4a6091d030d78286f128c40604ea538046542abf8d5d004fd80000000018c69d80110000000001))))
def p3853i12 (i : Nat) : Nat := (if i < 6 then (if i < 3 then (if i < 1 then 0x7200005050a06031d1d001522000309070a0a0104510400100412052b000011052f00000702000207090b000002000007150501152e261a040704c2000800000a004513000c0300011c03191710034e030410170000100035070b1101223a010d06102f060105000b00090d0f002d13265a0811250001000f09010200010a140101000d002103040a0718053507032f171001112a1000000f04041c05002110000f0012000f032e03062c770501000103020400100009014a00070000050a252a004227042913210c040d043c0f022a00274301030603080009030534030200060f000502262a030004060c151701070712004c0230041d060502000b030300240200000071001213161400030100010000020117260000000101010202000200072410001400090112005b190521050c030013040201051f0f0d1400470f0f0402001603020000071401271c051401030000323a0c00060a072f0b430330010000220804280204000703020000060000000100022604094000010200030010001b011c1d0102051308108d011000000100080c0605001501070600010500050800000202020c170301090e00040f02060001180b0203110e000004353700042a005f26000100000102140120033608000d01000306020c010b0131870a010400020b01052b021005060724090504190900040e01080000080e0800210200020002080900060501011001063a0c00092800290303013d03020e070206000e0f033a0601000000205004070f0b01ea07000a03320b0e010702030003330a2b055605000413080e11000d0003002a0d010025010c07010807040000010e00020b0b031009070f010200020001060b18350602000c033e030300000603602303140b000c003d0003061e0a0102020001173e0f000005361905001105000407050100004300030004101409020131071dd60500001203090c06010105031d00160a030b0101010b130205170009013b10000002070201070b090405750009000003030203030032070009600033033a0e0b26284236003304050002210306270602050609000e21000246041a160003000c010b05000b00022203010e11050d5400002e010f0300030b237c00080005041711010018001e00470b1301000000091a0d0113000031090b2d0010132202050000000400020038042e01240500091d0000000a0c150500050a0116fc020001200400020302040f02350d000a0101051918000006000a031000000f0a091b0a0100410007010a060b001c0105020003000b1b00071a01041c0029260014001d000109050004001f1e04162f3c0100000201070d150201015e0501110b000c000000021a2f000f00000b03010d043a0a13000305020b00040007000108291123000107000504020608010c1b052b020218 else (if i < 2 then 0x7930468103867a3166038d907fec05e460393364fb061c41046d0057990729724ba60387506ef00000c07f200000c01b1204201069000000707ae90359901f2914c26070e203edb60d9b017600000100a656151a2318932660031160044068ab802fab06c7703b4d2873003d5e152900000c77c3314c4f033ee02e07664c0000000000000000360b401b0910e600000000001061a00000d0790c03da0000030030a083b402e7000000000000000606e4b077300000d75b6102eb4141e00000a0067315340000000472c05f2c3009000003043f0000036215600dcb6065000000048c0000050120f0760f63696127da1304f0249e03e447086216470142b9080b76208506fe000006260ab07400138cb61843a108f03acd109900000906b4c14bd0077c860bba07fa916964b2fa503bb2003bd052f705cec01a2f0019d6643965d6c3261905b1d16a1276d9204f0061eb960d3201fa00000b122770179e6143b0004c1543308483621d1617550515f14178000e6003f00000b05ec408b6e2860000000000001496000004078f20080d7364d088ef06c6ca837d14ac00000d07aa660b04622bc64e8000009a61d9071e601319147d365c5a00a386667202dcd0617d0021e067fb02d18053c201ad0081e006138663f7003600000613f8b05132075d908448077800000c040f3665000000f70ee9669b0000000000b2820a6176b68a3d749b30898d41ad702ca360fce780b9031f80204d05cc514ce100d3a05f32b27d00000300e3000002078b90524802af960b5107f1218b8c0502d03c3d03a250433f27faf13e7b04df16217b07d0303f8b73748066d50208f1501f08bd0023970367381527a7518085c3084fe6290705e8ea83a961b13149d6613050068611b660321602ab8028300000d61b73054070057c00c0d00899087600000c636d7041d42843e01f900000705b2913e2014ef600099024b674c400000b1429f01ab0000040282e055f01405214996a4b770049a01b2418941b020108262604000504092001130201042300190001360e17020001051303111500000a00044107460c0d000301270107001001070f00031a07310c0e0001012f01040000010a310005010115040500070003070101130b150201021a1c1b0107190a0600070905050d0c000302220101141d00051d0b00250700021c6b010101010a13130102070505000e6d04250f0e1a170002041600021b0f1404000f0d00010009000a0a1a012f072a4200000a03093538030001021d00011a00100575174b35002305320101090500030c0005200d010b001d0b04000200030010030a1217040e50020300230029031403050e0a06010e007200020f0405000400030003003c4a01a82e230c110904001b0512002610070008152400020600001407000109001f00020e12162a else 0x10707c68a6a6092056168629f808a91026d7781e800b6b0272d0038e24bb2a816d780e318bcc1473165bd000008108210335e16b7f143c9768c121b6f074c301ccc07ca00000000007117d00000c0683a03058656a0000000000d4341c0650a14b006380801cf3019a66161400eef2054b6355e07a0264fd606511a49411435301b300000c640c5008200153462bc5050120836064ec4739e8b281710b5b6149d1183c02d07082bf032740108b0733308111719d0000032612a05e9a082ad6067a0758708663071d00000706bae03db014203620dd03d8c7809504838073ca0819e419a1006e1765bf01e87012d114f52037d61389f14b4d14980000060748f05a2006d8d04e3010b3570395b2e2902aec05c271444a1025d262ea01de3078306358260c9361e9a10ad6650ce06f2ca4c5b04d330349414d8307fc9052be10eb504c5406a31158500000b0130c02e1506b97444b206255028f704fc411e20000000000806c9260e37064900000812b700000906bc521e91088800000a04ad0000070232206e610495000008056800000262c6708a7f083ef00eac664b92819d0072b62a4c61a6602d22029b1011f10193512db303ae906a2407eaca314108bc602c27043ad0375f07be0071b8a81c113e4b60c197678903ce5622ca73ddc005eb648a9619d06177901631732640175060aa273624a83c1030f872f3214e4f05dd8057e000000a61ea014b01387e12eae4634f0047305eef074fd0094f711aa080e61215d080ac047d602a8771e8e6291411d860882c6342406acb0720b005a5026b781b636202806079a4b6d06d60004e0b09880417813c621561c61ea20430591b6504268748670810524a46057cd0138005ac015007009d60013b060cb06b771419108420605b504f9c615550518200ffb76f3b223eb075580247802a7b003c7002c060610042be03e3410dba013f9119750764b066fd13c9e02b1606fbfa1b6b61f230593b02f9b0538300b29761530629c08a1801ef401e2c312620171816c086346a0121b78b710028f039a664393260b005fd16352d1539103199045831386d0850676cbea4b87043800000513b89032a163b4e171da788a3086f30065306e07140a800cae0381a061257380a721a4031e104b4104f404638272b9c060eb004c9134830705e0238311eb426cbe610f5056eb04def75c9a068aa61807788c2154e954c1d05c00000000007d0020707e9526bde07b1105ef40376006abc62a97052af049823344c05702073600000308b201548670b6a6095a145f52845c009f307e59083a210faa102daa825313dbc029130769100aca00df41104c076b8009c301d68664861178f68a22780ae08260000000000c02cb000007051a5021651281000005633a10202202ac476ed618b6e05ad00000906784777a20507767)) else (if i < 4 then 0x82d10714b0397864fa4626a5a4c27043ba062d46089f03f7814d400000570c10080f2022a3065d102cca71873014cc146f4609f3059000000c0667b761bd06312031c00000a020ef2808e05b4d1581a6227605a9514372a2d30044d91540e026c0000000000a6249f16f9a075a9086ef73b400000e0797d00c100000d284a00000f61fee10a21034c101dac463500000c04c2f03d9e06d0402cd607dfe01f0c63dc20730000000009e805c77a4a9601e572837c6010274c5571bd1031400000364ee90310000004a80e074b6e120300000f14950077b660da000007056c000001141f0000000000403cba0749076b42a610000002069ab03bf107a5077fda2800177d610646e6895eb3d8b0835513f2311dda0408712019083710766e02597032e40111602ec400f5a013300000e0801c60bf712252010c00000f02548109210834803524689b00000d14e200000704f30000000000302111048a164f7f0236b35d55069521518203dcc140650774b000aa269910147a01e000000d1438707cb77468901d0866a140422574b82031a902efe0188b283c3083060544b067ec0266f065b00615e056250480b08ac305270000071462a30a7e0219b6058c139a903080000041596000006617418612a057280697d054a00000000008287cf01eab08654010dc01d7500f2877530000000000e0098007bf41414903ca000007037e000000000000000b121c00000f2841000000034e205e700000215a1c01cef0633601bc4065a7059b80777e02bb701ac013882a80b502870a495402c4164e370329504cbc00ae2050ff00c9707016011bf62548b48ae06990000027729502fe1007310660207dda0184e03435077080601161488133df017cb6056906dc104ebf15361148a3607ee608d57312a6134a014d30698f07562726c600e200000411dbb6079d13afd13ba2a70f413d9707d1b0322113efc18ac961d35026e402850085723639f206e304af30594708ba3a4aa771b6006ec7069fa02076605a508a09004d00000c003a0000000000d00bc860503007c215fdb333e7061181526b0008d0413000c5a263720159700a0900f1260f63060f5028480804361b300000715511a31300000a01d24a496000005123b908aaa085a902e2d052e3041f000003065c761c3c0439103d400431e03efe032500000b21bbf088b2046200000807f476197f7226c0567606c0d616c6088c30585e605c00000a002f000000000000000506b000000d008fd07f93061897479c73631427de14f86044e2a857000000000000000073a1312173085470809814f06018ab054bb18a9505a1506bdd14d37079c301cb466aa00000d04469a805d1768d06ccc0887102df0031501545000005240890665000003035d702c300000805197363a10373806a456625561e500000da134 else (if i < 5 then 0x880411b0279113b34036b20443301fb801fe202e4a0738a286c00000304d4a14cb0433f30727a6663a06e1e033b44340508b7977fc0138ff286100000d018d00000765bfb02c0624b860215b1426418b22760b2079fb0414914a1727da00000000000648d60554414009151c9666a678abd065600000601a82034b0000000000c283b00000d04b7614680000000000302eea615e006e2f05cf803615118100000105b8506f0861e3430b3f72c8504c6b00f4f105e10616802c7360a0f66420084b57676f14d27003d871e6b04dc171c44286e805879020ad082120820d0220ea1b50008c6016016073503998007f00577963b2e14ea202aa6064c2a492c2882e078010400b053d801988067600000866c0264f180596f033c50214a03a8d04b2010d2c0799a0710707dc00000506dbe730da13f0014c530626104bf427b3e0829a74a01774c002f7c07d631472305a336512102d80433df000fb06b8c03e2b13e9b7496f0664e079af00b1c134241463d071fd01b9113c320489f14a5f032481408e05df272ba06258f0658000004602a108be0000071218965c65029ea06ebc1121861e8d05c1d05647a10750002a025c5703d904231775f7031b2137e41451107a91a4a5f0845e00b99148590024806f3c07310036ea76f8b60482035fe0581178a3d64c73088485699532d4a06d9d0862208966010ec02fbd065ee021c707c4b00a50636ac2876b0145e02b40054c46059fa72a328231136ca005010487014ed812b622449014e1a78584063930364803e9905f1d080ce0040361ef1005da042f775cb41554560d120648d04d25053b301fd861a0c663e6626f200bb80096d071a80222b14de1a832d02e506623262c5a087d106f9e00de071ae907bc606e5ba856173283766f5760ad050b2948ac012e512da62842202d920512405aa512b37766b874a6e1027d22b01012bd13c0c038ab04a140772b62a820787c0859506447635757721d630a004a7a152530713e1577605af16349a06d5802c505845400c38023012878e141df062acb27e5059c765ebc0719f182b4707c8783c924bf4620480252b0090f02b5978962038bc620e50302d07f3f0055c0750907444058df2619e0087b081802019601bfa0808115b42a8243055d314ee70879006cf0024e1622676641b05a8301df503d0162472780c00448361f1f069d203303016b60500b11e0c039186060107041032c7053e202ff801e95739b203f5603334a80130225c04a91017e66438b018c8283a41428404249039c701705a49fa6044965e297852c0081f24b710256f070ab14762012a0a5e8705170031340016105fe5073577369104a5670ba76363b001f264f9e051c3600e006917607d407951085b0000020288577de816eb40823d02e3a067a0027e000000000061566100af276b930 else 0x749d77134004812049f204ca7a4a7a05bd8600de082520368f058a807898118850679b061c8064a5080d610d4f033a900d8b6100b143681483a159d80475601f3f4636a78979017aa0552b6253d089c01196c140de0415c012fe023e9261db1898d61f5e03009149af065f502063663dd02e63035c0000000000a1665b04ab90530e04db1076d0000000000876ba778483285b303b60000020194902b64085df020d207e20b3dbe62981148ce6768464e9177b71286d47812204603000572311a03c4f607c30520900b5804d6a0851c040ba0275401b6507e7203465047100000160ee601d90142ac024a0000000000b02451015001154b60134705c7028c6063ef0792720a5805c8807e300000606f80650fa1479462761023a7163592407e011000000b06dec1845b01e47079e401d56081fc00a11070de02cf907edf6292000eb56529263404a49c403894033fb0281006035069e207a670429806e9962626065947381c060a803a5e15aaf6077260edc1187907d931253f01fc0000060200c016c00000000000000000340c764b00000d048f9067200000e05d800000c02260000091407613c1e04eef14bf0000030132f0242904360144300000260450000000000e08243034700000000000000021582c1251f615d6014671219a608a00000d30db0000000000000009036cfb3ff0000070312d08af907ad312cd503a9302f3a548a107c3002a1161bc513dd204b500000466e7201b5164e7e08003154f00000a02441b1b6503704021e9848b0000000000d01f717191160715020507498a048bc0409713bdd07f820418414f64640a30097401bed029210642203ddb60efd07b42036aa0886415178770bb77b2900a7607c94629c330e8706cb2031df1616a61ae40425703a7e00fdb049ad087ce037400000a76a8273f000000e0452718b73067196209d634500000b1418b0600207ab00000c16d71015e502b9d635456042d61c900000a016721421f433a905dc003e56024cb0263000009b2b3d04da002f20014f205501057a50706604d7a16381028ed04b052869e749ef618dd77c79061016218c126100000c037f566405702810831b00a8d02c60003426711f6094004596333b00000124b6714c9c0745906d78072be0560608538664de77a6764e5200e6f03c82061b2b34140142703561007486029f0022307d40000000000f01d1730cf000000011320627003a3a152b803f290104c1584c039050546f0380fb44b501aa504a400000c0779412fe000006006df0643d072661475578a2b0407774abc06c5a609e7021af41b6000002088ab1305b020c614a656173900d5314aba066e000003004a2616bd01a3d62719056600680b14b210307d0077405f6b746330161e14ad30227f17c3a737580178573a0a1422460eb6016fea8268032))) else (if i < 9 then (if i < 7 then 0xb66286567582f21c9d72ff9058080233f004b314f7910cf000a22009b20186f04cf204e0c1432562a06077a268b2b21b5a055c273f2d249f616ad306619123fb072290382d611c0019b802b0a03f38209e008706073d604e931547402b3004dde6131711e3e761892740d01ff261018073780543a6645706b1b77b4860a90062e00000b6043f0632000000601f00000b02943148dd06c1200da107c0a7377808075631d21409c155c417ce107fda03b72a8219071600798700fe701bd205841068db0069f045c10868f03310261ed01c296785405ae1074d3050600203a0574b4489f0684906fff766e6024fe105c53845d6014270d770231701d810693fa7ff303173001a660c2000007035000000a06bff06a68a8127062806268606d20130731221868af00000000006057f00000f016e5619ca1182b0293c0394081b8f00e4b0666000009019ca78a000000c0261261ba0058c00000362efe315400000f24a9d45c40000050582b05ca00000408a51616a70134f076f00000a021320248c7746803719042af6351e0510824c4963b1000006a2d2d0828f73a3000004b072a01412049000000000002083d000000000000000a12c08013a901a50118f0149f803556610ec04c1200d6102db1077fc14dfb025700657f1080a2881a044c4008b46088304fb20366764f6500faa6366571b44327d00066908037052c9005f606be0000030765404c8803510140240454f0595468b8f077167759104857017d00000e02b7876e4a033250895304e8f061fa037a10746601929602400000b14d100000b40db80575773c1d61882079bc1120c02e88076a46137610afb0492d0337b070f7035e678a54152710041468b0d75e5906ad1040a0000000000d41e5661dfc059da0791305f9000009611d113b4061b5d04020000000000f0696406ed906a5a0037161148089a0000000000d07efc04f2a0006501265048d0000083414e26bbe045e1136b00000d045600000d027b306f440427604e582314615f626193c0385607b2414ca713c8705d46010fc62a32068ba7188e0734005bc46468c0341260fed138be28039038e302ad305bfea822e01002006a861f357887711ded07d8000cf527fb2137dd00a9460cb20085700ec60304a07bd3030e9060b442b3b14b1f7476601c65052df07fb83201c23cdb6634a626960172e027a3049640164c144e2035b004556624640434b025dc00f3e2859a039e60488400c4901c85655310078061367634f761e7b24aa2088980867f61e06622570482601ba7010a507af014b5304048063d4615b40139406da800b7ba8309628d700995739cd07d550775a02f51739f802c8904d1700e0c05e17179cd627f278a66a70ed6638c02da566496087ef0812600b0330faf046ab621bc655d500c6765fbd05fb5b636b62748 else (if i < 8 then 0x9159a00000e620fd07d7235c4708746054d018b1901c04058970558d028b00000d047ae088033341902d400000c0739313bf7624a904640025ad08a26004800000d73a7f022b805b000000d11c400000f033d4159ef14dd0000066082e606b564ed9614df02eda3281c615a605da55498914e8d0476a62e6d035a76228960c0c14c10000021340e04b3ba61c222f9a26c77610d20189b07cc50388511daf027770871f044b621d700000b78ad704ba004ffa067c406a0c622e7632c70181c04773069200000707b3907a4000005a80c2122400000c0441206a8b71e4a01e6e0863a3844067c30000050033015ca461ecc062c814161422100000762297a1e9300c8602a45006f00000f04652348af076c102410000020479920d6f062200000d0318d051b00000406d4807ce00243da81bda61a7042c25226c11f2e07769063b103c1701a9311f47a4bc9a4af000ed701e1c02551422aa04a62072a2000cf067d6059750149707183484560647a086436281506753029f001ca7059ea6163206f16000b0a80d6281ff010101555300ba966540056541487d777ce08b1f285f00269405e6301f5972bc00056d132dc1580813e6e7485213e15620a0734e20362005b6e122a760ec1784dd0619b7061305c3b0484105d780685c03ee372d7a074b6a809f13f331034ca8208046b303b0f24c0c76cab01c4805b5661b0d0894c18a34738220470000000000000000000001a80a003c2e0742ba4ac676a7505599078a7600b2a14c4086ae054e4025ff03d1924a5d0353d0637507b6e74a20000000000313ce000004809e1036d503e676231d0855d072c1062f94339c0548e0432c03f1a00438648b908a3d11fe614c8e0210802bd6779a4627d5061d1041cc6353b07c5b272e00000804f800000e00e876135000007014eb032be74c7b00add1564606ae500ab30289a0893f03cf803fbf00f71027f3005b00000207de703aa2026f3036300000201aeb622d8a317f05d00000020688501dcb6172772ce10467b708c7761190478f603e51214200ddd066aa70ff00000f01f1005e5a00bd2046e000008063af107a406fcf61b246409006b69602b205eb0000040630b075ff0297e081d86086e01d3f0166f07ebf76c1c0623c05496610b461ab80377c040c306ea3075c560e2e04fe87367005c4e0012f0114b070851772c6344060bc8015be077ed634d2118500000c081b760cde0813d13f19013c00000f0843d1698975dea13fe201a4b749cc658a5710f6074ea6007d07530000006028e156b00000403367145200000403d6700ef7a498c1117a00cc868b6a029cc082e2027dc02a9b65cd6848950148f609d277d7560277015cb02d36745801520b28357607fa05a6c0079014fd812084a7fb515598281a603bc00268f0209705f090053461 else 0x2a6807db90469702bc00000b138300000ea83bf6189d61d5704c0f363300228a6272074ad00000061d286635000008028ae019de0846d60d830817b15a336156605d540316506fa905c6e611eb60e410768260bea0606f10d7ab085c04d9c621aa017f761502147cba4bf2145e600d72560b00031000006152c061cef7899614975611b207c7a08a630029d01ece047ed1266614f4000000000032862406df9052900000a611900000215a400000e01bb0000000000201c30044a6732ea0125e156cb0152d02d500280a06f52747d800db102a27118b261bdf24a7904e63076e407e65036060457d03b5d0250705cbf663b707150069400000703f9006868039d41412528303021f27385716a8161c87780fa118000000c62fb00000e0169505216b33f00000000000000040674e05ab105ea000000000000000e622f80299e0224006f700000000003016d011190000000000206ee300f8207a3ba836f0365b76aa20796c6049e0218e01a15621cd0309203c9a14cd321509067b406d156113e61d7960e5c05cd0129600000a61fdc7692905d100000761b90000000000d1271104167724706116f05766058e40788604be60869905236622a00000000005034fe0609a03cc0a48a5084a4056b905d39064e81471060aba25cb5582b8081a96023a07e4c249c3028d07819e13214b3da96039d13da2009530551b0071301a0c62d6328571155ed06b3a159800000f0116000007245850379d019e905ff204d80000081532f0011aa80fe04b1b021d560d700000201735068eb0187f084d605bb961a23607600000f73a681809764e6c03dee04b8904b6761ccd585fa00f9000005808bc0018b086ce018f4056f906af3788d701955a60a0022900000871c7e13b7e18afe00bff0342c008a9287fa0561d61e6a038c30190908b5f089770061611e5c14b306068f6347804973157150634a08b3c0545902dd47216c61cfd045f017c70000000621f06c3fb33c862ad8050c4085f801eb00000b61de5056a215f30000040157613a16145d505edf002a116f240751773c316205610aec62a1003ab0000000000000002079460062c060820449e15a741697a0123e04ec602b800000e611096003960a800000e08602689e54009800e59208b4249700000802120000000000e525b901994122670542f2872f0535c10f8e06023050e203c5e6078760fde0398c068c675805060d0006c000000614c00000961f79018300000515b2500ce70636c07b9225e100000a07c20000090372d071190588e0140d00aa20555c0670568bca14404a1b73041b4158ee08906087a00000018a200000000001609600000a0872827fc00000000007a838103a1f51b6a333a00000000007064d108929144d502bfa07bbc00b3e06407015830444968a130668e64db000004603d)) else (if i < 11 then (if i < 10 then 0x78011cf0841b0717105f500000000007748a000002073be64ef0000080339c052820128a6075000000065211439a005400000743426676900000e785b405be971b1600d95275f604c9d0271900fc9a84a2008300000d0063c14dae046c10592b0504003f60041e524bd978b6c60b8c0556e03d3f0786b03a6114a0700d20000020806b023f7049e512dd901770011a40583d745010334000000000010534906b5a01a60a8046611ae48432806ee06241014a00000c2856000005073a406e7207cf7775da61dd8005980532804ed503afc57d8464f4e13d800681c026a801b720838000005007d86425203b9a07ec70162000002521a00000000004602000000e06a9806d3b08859012c00000e03eb0000000000b158ba2863c61bb304379612f80344e0151202d6374be60743605630089ed066c3056db666f36144670d600440d0017c138ad7666f0046d07d3203ade04f640873205fae04cd508a8f0655560f0f04d0504fa00000000000000090154400d100000e1461a1401e023c007ac201856008856773000000000000000a27d8907c6411c2007320010b000000000010348f633900000008a4a053176093d002780747b771f6057dea1bc4601e18150361944020f414bea612cd84a552317000000000000000f076227774a0654000001a489000006a83110106a145400000113f5f6022b01ee704010000000000b01dbf0045043383022f60463a05c92025e0047f803a0c0858971e93006b3147a9774f118a4005a0e0673704efb0461132c4604124285da582080816104cc810c6302c1a03572103016012a664e865ff5078dc1344b0802b61af20474a01d45055b61373207b0e03df5a82bd631bf761e00428314561085e607b700052f0137e327e8152d9066bf70bf701b4908321629dc721be089f562014141a6664ab7065c044f403cda1460d1306578b8e0689b00034011da01f8c013e00000602bed045b6038fc14fc7169b00000922c2b075e00000304a0000004109860899b1239e010750001f0687a1482464dd000001007e6618700000d06bb300e75736a9008e772cfc008dd18a6d11fd5084c02824f040ec617fe089df76a1802646026760445e61f663636460d6603be00000960f7206040154b91544a0537d0035201969040500759000004003ee121e11147a65ab76030d0384d075401820a07128009a8434400000000000000002801000007032fc0827713ecd6081871c0207e1b036f0022d0000000000b772a251df0000020805212cb1664f203bae634a002377785aa0514f088f3023d50677f629bb085280306d0338b6653c0015925e52023b1055ef13d0660ea50861f07f0108b44157da1434e45d5905035062b30201e275a46181b01361652b924c5105e2417b7403ecc433e36072802f85648970253202406604040 else 0xa4b1165839a721c04aa000001018ed043cf1464413eb904ae00000a07f5000000725b603b13078201535d017be0395b06e3d05f8a6216212ca40168306aaf084700000a169ac708200000007f6000000000050234401f650217402233070086348f04c32010500000d600200000d13be000002634ba13e07059900000103ea10383007094626d0000000000207414068f20442a71a0f6102ea60e861c05155080092801c5f14a43123a30191a04b9106e847684678bc0121f00000b613212838d030b16219b07674002b81546f6644e0620b07a8b64f87078e8610c9617e2048e127525086b5163a4022ef054fa0435120bf201edd61bff0509703e0b088da14fe7a1b93042e00000f77b000000d714cc0345e0303413e8b002500000760ca00000d00c7e1484505f7360c3f56bbf60f500453706694069c3059f50508205e3408b000026501f4f05d66061e40135266a800000c0752d643b2146d605393625a06467411df100510118dd6021000001084920119103e8205b9c07c81055a80505d06cac12fd00000302e96034d4a823060b60079d1049db756652827e053a0073e2288600000c16b56074a8014447614902625013b0000030493000000000000000203c000000b05696001d8082f0603f708ab000002082ca064fd13c7361d60000000000000004078ce030c0000000000076c2c063fca493b155b00000d02d780258d70aa331b66003200000b004f161a40000000000618445145c00000d0155963f700000074ef907935149e000d491728e670116244b021b107f7a14c7408331045de602f00000007e8363ddf01c7503e17141cf60ff904bc5019700000624898024d00000714d7805c500000e462380058205e0e14dc0000020127124af405d97730e00000161380000000000968b780557106a7504f1207a1714fbe13208606900000c64667151ed039b1783b8122900000d07cd607210000000000f287b00000262e40000000000d0533804e7561b4e611516038804ace0129c62d5a0703606f64072d00586104917609900298205a40b344b146b3a315211dc101a7000006673450369600be904d5461a1121b7427ff765145077d97859c609ca61a54001eb00f0324ac51560c715bd041a3037c5433bd058b0088300000b058f2039fb66460000020891113ed00000201c1c661fa073f0030100598517d2300cd10103b274e101cd302dea778e5146ee0182004f52805417847d608ce06c2c0295e005cf14e6e01e376192a6210a072ec283ee04e190450ea4b0002ba27365661b8614ec713c5b60ba0000090358c61e1804c7b072f1155ad03fc4001b1606a705fc965109015a101dde42fa7026570023504105614b000009057191565000002736e5083c00000213f40000000000000000000000000501227144bd08c000000601e) else (if i < 12 then 0x78e001026006a314700000c112a9153e0000020578b04515138ea06fd401651310cc02b200000114e9404c45b2010000040014b083fc0875c06824049930392d05b7374a3000001709f020ede034ad7030b03b20000000320203fd202cea047ba2871c147b2043db72de2059ae07a2000003768e2736ff07b527612a070c1052217318570edb051e3015d3a802511264778571427a00d08078100000c03bd00000e123ce0246b0614001172053f6614ee282600000e0814b00e18087f4022cf06c8c0093a61a3d14c380525f0143c4171e019ff1303464e48249d164eae03962047cd04bd9051d706cd9018b073a4c61c7ca85950118763a1da318d0822402a5161f0b14f1868976283dd007a674cd306621147e4049cb21bcd155f02821614a34778b91450d027380406211d9b0124e03230168531223c0180c025be14e7407a745809d669a905a5a0494914d677851b08bf26157702f0567b770553f05f4b60acc0724b08b9e049b66057008402007be03c60000000000707ff2648100000772f000000013bc0057b8100a000b8c086d003b8576c0d12ebb848aeb03400000002a000000f13ff004ce26257c05b3b06b2307ee32814d62a2202964614aa051f503781448a0064100000a04a3c0102000007148630815b0354b14c08007530276e0761360525788ef157ca64f5706a1c6221602f1d6064e08ad1a85b900f6000007333fa016a805db202fcd0536f626c00000005ba771bad712f00763f02fdd009107150e2880421529030db04a80000000000603c700000371bcc23d5b084e1160be748d000008008420725d05d2702a38144a566970000086074a18ae00000102600000010663000003608b10541908398248a00000a0221a152e00000f064500000763500000052836b769f00000c03f4c1860a01aff2315f42e266673e2746000009011296511000007075b207da2143dc06ce200e9a04fd211ec5029a602f6d04f7605264081ce127fe1384020fef282a603b3c60e930516d0235961aaa609b8064b2046690109e60b1c03f082815607e0c286820856e14230045ab15e7b601d113e5800608040dc032680605714bcf634c007ba804bb206c4d631aa01c9a0251800a460076400cbd07239102e8626e000002141bb069b00000b0573a08bb3657060877b61868789ee0728d6207a07b85015f005de167c700000c28226013d00421da753e03d78044700278e000d37853b02f4380199037b90785a60a78761301639404ea000007614521213960d530403c0115964cb0159fd043e407c1e089ba06dd600c29b092d60bd000001768ab02c9206383118a30286f78a14200eb0039962c8662aa600702676300000803fe00000b004280473000004032d00000808ae000007029d907d28030ac041900000000000000000000a063c000005 else 0x2070bd015600000000007760674303f617dd042d9772e065ead0702913cf8149400000a77521668eb02eab03e7d0591f0547b261cd423ee11869011e70653108815027cb60ccf00fba07574087bd711bf775a4001c1a4c04002e503d200000d13bb8619576338705a7e644d8121bc027460270b625ca0486661f8303fa8050d027538118c304e2704a250511b04e4f002d411be173a2262e30050ac0635d020b1071c50064c03a4a03ff0663c80784816aaa13c4914ae6612ad0086314e0b0290f282b261d4376174615f900b4c715d116379b3d9d261a513fd915cff61911325156066f08b88046f97197401b8a0174d08))))
def p3853i13 (i : Nat) : Nat := (if i < 1 then 0x25dbd0ef4f0138808a81b1cf01d05f1929b41b7802b1600502df40df16224630502a989e354e69244e0113583f54e7e044b80a6c07c22ceca44fb0a381d94e47007be82ea49c440da107b1b973008c80c14052982a6405a84e9e041f02c5c4b1c079307c9833a8021c00fa054200ec9837ce896137f938d407bc07c501bc93b4984f863a702a2090f41c30066a0640803680547436a41d48044815620b5817da01f500ef6ee20073483aec4eca26830486b0f181a1cc8d513c1032bc198203a90659821149d8245c2003d83abc4be82a347234328d814300942030002e1c07840def34600114d8412071b1461810ec189406cf10d7091a41cb806dd00370345011760e2610a6b401d88c4069503ac818f01e4acfc60697817789cd2c1ee133e0319a96c624ec006630365829e02ea03a382fcc02804e1e12e8035b4063e0491077bbad89825ce1190215813398026021306e1818969c1a0f5d08298945a8b6363aa601a3b800001e00ef005d027741732091d01aab09640d4202f0000781588059e07296058025901b28c0fc051000009dfb245b660610299c0a20000e773d81da496ce0987737f83fe009e6d01a059402bfc0a5409a0000582f580c8a0610000000000001e25c0000609aa41a92002003380001d81400003044650440000609200000000140bc0000000050400c0e714e2d00ac304c0001804e00258000000008103602c73a82403d4c61000053bec0000610600001b261041c6ee3d1305894000000000b61300001408ea0b600006095c00000000867fb896b45d32c21463a081c1010e0000d67f781a3c530cc15c77bfb01b006d0277004db03ebc0a00000900b8020b815c825ef06aa834f803f4ef300007894edd8be005307c28094184700813071c088a41e84c05e17ee90d9c11ec08ef04f780489c2a200196072b96fc48520ad5724802328049d4e300000000080bf4104f035902738177a095206bc1044c083a0f35009903f480f1807ea07f603749821c265c03d1802bc1c0608d510dd816a58110c3b307d880e1d8748e36e050004058169c23af00c580c295d260b3918033bf08133a622313088137010d24dfa275d8099c008a03f000b100d340660000313329383c1e080eea02e6824e0001401c80252896c09ae201b000030bf18073e059202afb047c4480080c77aa827e00dc2032e0720b3f4010b8cce0000680640000207f00001814c0000aece0c110b012301100400030a0fb90e0302020003072d001000130b2a0b050b0006041001584800001300050a1e3f0b68160d1a013d0600080039050000002f0848080e25010e580200660007060105030f3b01081a0a0c090507000528040d020813010300000064290400022f19310b0101000a090002101d00000a00200962050e05000e550001110000189819034c02 else 0xd02ddb01e018a60bc00005840a41f800000000081ed580840c07024000009844408ac60d6893cc03a345c0000000000000000091325002581bfc023e180db025803400009601383a081ce0000e05260964000080f1971f00334c4686ee6a02ba828f005140c22061e30fa812e00000000633ef800780c92032a83b5018e60208780700229d46000060587939c0000000000007010144ea00cfa0562029e89d4000000748000)
def p3853i14 (i : Nat) : Nat := 0x8991800b214e0000000000000000000060547ac5c3000000004b7317c0000000000415fb4c9820000001000002c05e4004cef40024d00000000008
def actualLevels : Nat → Packing
  | 5 => level5
  | 6 => level6
  | 7 => level7
  | 8 => level8
  | 9 => level9
  | 10 => level10
  | 11 => level11
  | 12 => level12
  | 13 => level13
  | _ => emptyPacking
def actualIndex : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 2 0 4 0 0 p3853i6
  | 7 => lookupWord 1 4 0 5 1 0 p3853i7
  | 8 => lookupWord 2 8 1 9 3 2 p3853i8
  | 9 => lookupWord 17 59 6 14 6 4 p3853i9
  | 10 => lookupWord 182 619 7 17 9 4 p3853i10
  | 11 => lookupWord 984 3338 8 19 11 4 p3853i11
  | 12 => lookupWord 1322 4483 8 20 12 4 p3853i12
  | 13 => lookupWord 144 492 8 17 9 4 p3853i13
  | 14 => lookupWord 7 47 2 10 3 3 p3853i14
  | _ => fun _ => none
def basesamples : Array (Bits × Bits) := #[(0xfff000000000000000000ffffff000000000fff000000000000000000ffffff000000000fff000000000000000000ffffff000000000fff000000000000000000ffffff000000000fff000000000000000000ffffff000000000fff,0x544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544),(0xffffff000000000000000fff000000000000ffffff000000000000000fff000000000000ffffff000000000000000fff000000000000ffffff000000000000000fff000000000000ffffff000000000000000fff000000000000ffffff,0x823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823),(0xffffff000000000000000fff000000000000ffffff000000000000000fff000000000000ffffff000000000000000fff000000000000ffffff000000000000000fff000000000000ffffff000000000000000fff000000000000ffffff000,0x314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314),(0xffffff000000000000000fff000000000000ffffff000000000000000fff000000000000ffffff000000000000000fff000000000000ffffff000000000000000fff000000000000ffffff000000000000000fff000000000000ffffff000000,0x69069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069),(0xfff000000000000000000000000000000ffffff000000000000000000000000000000ffffff000000000000000000000000000000ffffff000000000000000000000000000000ffffff000000000000000000000000000000ffffff000000000,0xa92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92),(0xfff000fff000000000fff000000000000000fff000fff000000000fff000000000000000fff000fff000000000fff000000000000000fff000fff000000000fff000000000000000fff000fff000000000fff000000000000000,0x1b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b),(0xfff000000000fff000000000000000000000fff000000000fff000000000000000000000fff000000000fff000000000000000000000fff000000000fff000000000000000000000fff000000000fff000000000000000000,0xdc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc),(0xfff000fff000000000000000000000000000fff000fff000000000000000000000000000fff000fff000000000000000000000000000fff000fff000000000000000000000000000fff000fff000000000000000000000,0xce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0),(0xffffff000fff000000000000000000000000ffffff000fff000000000000000000000000ffffff000fff000000000000000000000000ffffff000fff000000000000000000000000ffffff000fff000000000000000000000000,0xf00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00)]
def basecolumns : List ColumnInfo := [(0,0,511,0,15),(16,0,495,0,13),(64,0,447,0,13),(128,0,383,0,13),(1,0,510,0,12),(2,0,509,0,12),(4,0,507,0,12),(8,0,503,0,12),(32,0,479,0,12),(256,0,255,0,12),(17,0,494,0,11),(24,0,487,0,11),(66,0,445,0,11),(80,0,431,0,11),(132,0,379,0,11),(144,0,367,0,11),(160,0,351,0,11),(192,0,319,0,11),(320,0,191,0,11),(0,16,486,9,10),(0,64,189,258,10),(0,128,347,36,10),(1,16,486,8,9),(2,64,189,256,9),(3,0,508,0,9),(4,128,347,32,9),(6,0,505,0,9),(8,16,486,1,9),(12,0,499,0,9),(18,0,493,0,9),(32,128,347,4,9),(33,0,478,0,9),(65,0,446,0,9),(96,0,415,0,9),(129,0,382,0,9),(130,0,381,0,9),(136,0,375,0,9),(256,64,189,2,9),(264,0,247,0,9),(288,0,223,0,9),(384,0,127,0,9),(0,1,460,50,8),(0,2,440,69,8),(0,4,369,138,8),(0,8,227,276,8),(0,32,94,385,8),(0,256,151,104,8),(5,0,506,0,8),(9,0,486,0,8),(9,16,486,0,8),(10,0,501,0,8),(19,0,492,0,8),(25,0,486,0,8),(36,0,347,0,8),(36,128,347,0,8),(40,0,471,0,8),(49,0,462,0,8),(67,0,444,0,8),(70,0,441,0,8),(81,0,430,0,8),(82,0,429,0,8),(134,0,377,0,8),(140,0,371,0,8),(145,0,366,0,8),(152,0,359,0,8),(161,0,350,0,8),(164,0,347,0,8),(194,0,317,0,8),(257,0,254,0,8),(258,0,189,0,8),(258,64,189,0,8),(260,0,251,0,8),(280,0,231,0,8),(322,0,189,0,8),(328,0,183,0,8),(336,0,175,0,8),(352,0,159,0,8),(416,0,95,0,8),(448,0,63,0,8),(1,2,440,68,7),(1,32,94,384,7),(2,1,460,48,7),(2,4,369,136,7),(4,2,440,65,7),(4,8,227,272,7),(7,0,504,0,7),(8,4,369,130,7),(8,256,151,96,7),(14,0,497,0,7),(16,1,460,34,7),(16,2,424,69,7),(16,4,353,138,7),(16,8,227,260,7),(16,32,78,385,7),(16,64,173,258,7),(16,256,135,104,7),(21,0,490,0,7),(32,1,460,18,7),(32,256,151,72,7),(35,0,476,0,7),(56,0,455,0,7),(64,1,396,50,7),(64,2,440,5,7),(64,4,305,138,7),(64,8,163,276,7),(64,16,422,9,7),(64,32,30,385,7),(64,256,151,40,7),(74,0,437,0,7),(83,0,428,0,7),(98,0,413,0,7),(128,1,332,50,7),(128,2,312,69,7),(128,4,369,10,7),(128,8,99,276,7),(128,16,358,9,7),(128,32,94,257,7),(128,256,23,104,7),(133,0,378,0,7),(146,0,365,0,7),(156,0,355,0,7),(162,0,349,0,7),(177,0,334,0,7),(193,0,318,0,7),(198,0,313,0,7),(256,8,227,20,7),(256,32,94,129,7),(268,0,243,0,7),(273,0,238,0,7),(289,0,222,0,7),(296,0,215,0,7),(321,0,190,0,7),(344,0,167,0,7),(480,0,31,0,7),(5,2,440,64,6),(5,16,482,8,6),(6,16,480,9,6),(6,64,185,256,6),(6,128,345,32,6),(10,4,369,128,6),(10,16,484,1,6),(12,64,177,258,6),(17,2,424,68,6),(17,32,78,384,6),(17,64,172,258,6),(17,128,330,36,6),(18,1,460,32,6),(18,4,353,136,6),(18,64,173,256,6),(20,2,424,65,6),(20,8,227,256,6),(20,128,331,32,6),(24,4,353,130,6),(24,256,135,96,6),(34,1,460,16,6),(34,128,345,4,6),(40,16,454,1,6),(40,128,339,4,6),(40,256,151,64,6),(48,1,460,2,6),(48,128,331,4,6),(48,256,135,72,6),(65,2,440,4,6),(65,32,30,384,6),(66,1,396,48,6),(66,4,305,136,6),(66,128,281,36,6),(68,2,440,1,6),(68,8,163,272,6),(72,4,305,130,6),(72,256,151,32,6),(80,1,396,34,6),(80,2,424,5,6),(96,1,396,18,6),(96,256,151,8,6),(129,2,312,68,6),(129,32,94,256,6),(130,1,332,48,6),(130,64,61,256,6),(131,0,380,0,6),(132,2,312,65,6),(132,8,99,272,6),(136,4,369,2,6),(136,256,23,96,6),(144,1,332,34,6),(144,4,353,10,6),(144,32,78,257,6),(160,1,332,18,6),(160,64,29,258,6),(160,256,23,72,6),(192,2,312,5,6),(192,4,305,10,6),(192,32,30,257,6),(192,256,23,40,6),(257,32,94,128,6),(260,8,227,16,6),(260,64,185,2,6),(272,8,227,4,6),(272,32,78,129,6),(272,64,173,2,6),(288,16,198,9,6),(304,0,207,0,6),(320,8,163,20,6),(320,32,30,129,6),(320,128,27,36,6),(384,8,99,20,6),(384,32,94,1,6),(384,64,61,2,6),(7,16,480,8,5),(7,128,344,32,5),(11,16,484,0,5),(13,16,482,0,5),(14,16,480,1,5),(14,64,177,256,5),(19,64,172,256,5),(21,2,424,64,5),(21,128,330,32,5),(26,4,353,128,5),(26,64,165,256,5),(27,0,484,0,5),(29,0,482,0,5),(35,64,156,256,5),(35,128,344,4,5),(38,128,345,0,5),(41,16,454,0,5),(44,128,339,0,5),(49,128,330,4,5),(50,1,460,0,5),(52,128,331,0,5),(56,256,135,64,5),(57,0,454,0,5),(69,2,440,0,5),(70,128,281,32,5),(73,16,422,0,5),(74,4,305,128,5),(81,2,424,4,5),(82,1,396,32,5),(84,2,424,1,5),(84,8,163,256,5),(88,256,135,32,5),(89,0,422,0,5),(98,1,396,16,5),(98,128,281,4,5),(104,256,151,0,5),(112,1,396,2,5),(112,256,135,8,5),(133,2,312,64,5),(133,16,354,8,5),(134,64,57,256,5),(135,0,376,0,5),(137,16,358,0,5),(138,4,369,0,5),(140,16,354,1,5),(145,32,78,256,5),(146,1,332,32,5),(146,4,353,8,5),(147,0,364,0,5),(148,8,99,256,5),(152,4,353,2,5),(161,16,326,8,5),(162,1,332,16,5),(162,64,29,256,5),(166,0,345,0,5),(168,16,326,1,5),(168,256,23,64,5),(176,1,332,2,5),(193,2,312,4,5),(193,32,30,256,5),(194,4,305,8,5),(196,2,312,1,5),(200,4,305,2,5),(200,256,23,32,5),(210,0,301,0,5),(224,256,23,8,5),(225,0,286,0,5),(259,64,188,0,5),(262,64,185,0,5),(265,16,230,0,5),(273,32,78,128,5),(273,64,172,2,5),(274,64,173,0,5),(276,8,227,0,5),(280,64,165,2,5),(281,0,230,0,5),(289,16,198,8,5),(289,64,156,2,5),(296,16,198,1,5),(321,32,30,128,5),(324,8,163,16,5),(324,128,27,32,5),(326,0,185,0,5),(328,16,166,1,5),(336,8,163,4,5),(352,128,27,4,5),(385,32,94,0,5),(386,64,61,0,5),(388,8,99,16,5),(388,64,57,2,5),(400,8,99,4,5),(400,32,78,1,5),(448,32,30,1,5),(15,0,480,0,4),(39,0,344,0,4)]
def mf : Forest := ⟨511,13,fun j => basesamples[j]?.getD (0,0),basecolumns,deadautos,actualLevels,actualIndex⟩
def tokenConfig (k i : Nat) : Nat × Bool × Nat :=
  let (num,d,cw,_,_,offw,lw,data) := mf.levels k
  let start := num*(8+11*(d-2)+9+d)
  let pos := start+num*offw+packedAt data (start+i*offw) offw
  let nr := packedAt data pos 7
  let linked := packedAt data (pos+7) lw
  let st := pos+7+lw+nr*(cw+d)
  (nr,linked!=0,packedAt data st 552)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem sample : auditBlock mf tokenConfig 5 0 1 && auditBlock mf tokenConfig 6 0 2 && auditBlock mf tokenConfig 7 0 5 && auditBlock mf tokenConfig 8 0 35 && auditBlock mf tokenConfig 9 0 32 && auditBlock mf tokenConfig 10 0 48 && auditBlock mf tokenConfig 11 0 48 && auditBlock mf tokenConfig 12 0 32 && auditBlock mf tokenConfig 13 0 8 = true := by decide +kernel
end PEqualNP.Outside.L_meta_5002

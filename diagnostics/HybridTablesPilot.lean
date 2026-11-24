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
def sampleLe (raw : List Sig) (r s : Row) :=
  raw.all (fun v => !bit r v || bit s v)

def rawMonotone (raw : List Sig) (v : Sig) : Prop :=
  ∀ r s : Row, sampleLe raw r s = true → bit r v = true → bit s v = true


def sampleRelation (raw : List Sig) (p n : List Row) (a b : Sig) : Prop :=
  rawMonotone raw b ∧ (∀ r ∈ p, bit r a = true → bit r b = true) ∧
    ∀ r ∈ n, bit r b = true → bit r a = true


def extremalGeometry (raw : List Sig) (p n : List Row) (goal sub : Sig) :=
  p.all (fun r => bit r goal) && n.all (fun r => !bit r goal) &&
  (List.finRange 512).all (fun r =>
    if bit r sub then p.any (fun u => sampleLe raw u r) else n.any (fun u => sampleLe raw r u))


abbrev SimpleGate := Bool × Nat × Nat

def simpleValue (raw : List Sig) (g : SimpleGate) :=
  bin g.1 (raw.getD g.2.1 zero) (raw.getD g.2.2 zero)

def auxBank (raw : List Sig) (cs : List SimpleGate) := cs.map (simpleValue raw) ++ raw

def choicesFor (raw : List Sig) (cs : List SimpleGate) := zero :: one :: auxBank raw cs


def readChoice (sources : List Sig) (indices : Nat) (live : List Sig) (a : Sig) :=
  sources.getD ((indices >>> (4*live.idxOf a)) &&& 15) zero


def betterB (pm nm a b : Sig) := (pm &&& a &&& ~~~b == zero) && (nm &&& b &&& ~~~a == zero)

def cutTest (pm nm : Sig) (raw : List Sig) (cs : List SimpleGate)
    (idx k L : Nat) (ws : List Sig) :=
  let rep := readChoice (choicesFor raw cs) idx ws
  ws.all (fun a => betterB pm nm a (rep a)) &&
    decide (k+cs.length<L+(ws.map rep).countP (isMaskedConstant one))


def nd5 (i : Nat) : Nat := 0x60650c1c62cf158734b59e30d0081
def level5 : Packing := (1,10,0,0,0,0,1,nd5)
def nd6 (i : Nat) : Nat := 0x20202021e50c1c78ac39a5acf1868040e8ca062cf158734b59e30d0081
def level6 : Packing := (2,9,0,0,0,4,1,nd6)
def nd7 (i : Nat) : Nat := 0x4040004007700a602ef3ac0e32a18bb0e696b3c61a01035e503c561cd2d678c3402073148526e69462491868040ccb40f7568a8728a80c4051
def level7 : Packing := (4,8,8,0,0,6,1,nd7)
def nd8 (i : Nat) : Nat := 0x4053045e020080808000044e092022005b41000000000000000000a6018b88ee010200160208053412d003b80a6820000ca633095caa532893c9a3cdd6e36db4d96c35dacd3874360fc2008006c57146b445249250081c8ae2936b0a3124a0103bcc8492d398b8c3402063bd0e65a22931868040cf3a1cdb0f59e30d0081e67431761eb3c61a0103ada862cd2d678c3402077952c39a5acf1868040ec5a14635351230d00819ea4b9a51892461a0103f148524a31248c34020739d0c5da73051868040cf3a5c735958a30d0081ce74b8e6b2b1461a010327e4736c4543ac4501460fd8e6d8ba87408a028e1f31acac950e8114051a3f239950eb1502280a3ed91592814a2a0250147dc32734c5ac9384a028fb8c4e698b58a709405192f439b5a2a1d01880a3e5a15a2a1ca2a03101477b82405a82c528a30a0efb0480b4e58a5146141
def level8 : Packing := (25,7,8,0,0,9,1,nd8)
def nd9 (i : Nat) : Nat := (if i < 1 then 0x50147b7c562a05404a028f7ccac928a8094051efb158a51501280a3fb62814a2a0250147b3e5a7ad1384a028f2fca855a27094051ecf938ab44e1280a3d9f2b45079c250147b3e5689cd384a028ff1c9cd3167094051cfd9622b24e1280a3cfb2a45649c250147bb6507ac9384a028f76c9cd5927094051ef99316b24e1280a3cfb2a15649c250147bb64e2ac9384a028f7789c558a7094051cff1622b14e1280a3cfe2a45629c250147bbc5a7ac5384a028f778a0f58a7094051eef139ab14e1280a3df6262d629c2501471f358aac9184a028e3f2b1558a30940518bdc6a6c216a880a34fbad216aa91101469fb5a82d550e2028d3e6b485aaa1c405187ec6b2b4543880a34fbad216aa85101479eb16a94728a2028d3fa35750e5144051af9d690b54a2880a35f68d5d43945101479e91aba8728a2028fbd231350e5144051f784492a1ca2880a35fb2d216aa03101479f65a42d54062028f3f4b465aa80c4051e7e920cb5501880a3cfe2d116aa03101479f616a2494062028f2f4ad150e80c4051e5f85aa81501880a3fd60d3ca2a0310147fe41249454062028fbd0a8728a80c4051ffa120e51501880a3af4ac54a28c310147fa34802cf28e5120ffc290128e814a241fec920283ce18c283bf8240182acf18507fb2480a0f39a30a0e7e490162c82c6141dbc9202c49058c283bd924058720b185077d2480b0c41630a0efe090160882c6141fec920283ce58c283fe92404e698b18507772480b1058a30a0ef6490161cb146141df49202c31628c283bf92405852c5185077e2480b0a58a30a0fee490141e8146141ff49202734c28c283fe92404c598518507ff0480a0530a30a0ff6490061e5146141dfc9202c34a28c2837bc6d416294518506fb8da72c528a30a0ffe090058a5146141ffc1202814a28c283ff4272ca28c310107e9cd249cd30a7090ff2924939a614e121fe71202734c29c2438bfab55882c1284871f756ab085825090e9ee24862a9350021beb8696b3ce1a00432fd8d6548947100867f91ac94740a2010fbd235528e5144021bf65698c5ca3880436fcad518894710086fb95a731128e2010dfb2b4c62251c4021bfc5690c44a3880437fc2d098894710086f791a8b0d28e2010ffc2a0a49251c4021faf141e90ce188043fda0925079c310087fb8483a0f3862010ff6824939a70c4021fee120e734e188043ff4282ca39c310086ff85a49473862010ffd094928e70c4021fee141e70c61880437ec2d318b8c310086ff85a53171862010dff0b4a52630c4021afe16ac82c61880436fc2d51058c310086ef85a920b1862010dfb0b4c41630c4021bfc169082c61880437fc2d44c58c310086ff85a798b1862010ffb0a0d31630c4021ff6139a62c6188043ff4282cc58c310087ff04e62491862010ffe0a0a49230c4021 else (if i < 2 then 0xc7263130d984cc165f52ee9714b385732b5958ca9a52427993ac9884ae24391c488c43e21410047f23f11f48f847b23a91d08dec6aa32418e0c185fc2f61770b985bc2d61670b1857c2b61570a9853c2961470a184fc27613709984bc25612008e044021810808204001f80f807a03c01d80d906a832818c0c205f02e816c0b205702a814c0a204f026812c092043820c0fe07403481940c2056029011c07803101680a404a01a007802c000d35e51ac394924903a6bca3582292492070d7949b165189240e5afa4562ca312481c35f62ea49462490396bec5d2728c4920637f1abb0a5268040e8be28c626a250081b9dd688a4924a01033abad614624940207c5714928c4928040fe74b4e62e30d0081bde969cc5c61a010379d2d398b8c340206f7a5a23171868040def4b4e52630d0081bde9688a4c61a01037bd0d65678c340207b7a18bacf1868040fe74b0f59e30d0081bda8696b3c61a010373d0d4d448c340207f7218b2491868040fce429249230d0081fd4851892461a0103f392931248c340207f5a1469c91868040d6f4b5660a30d0081dde862cc1461a010379d2d39828c340206f7a5a53051868040ded4b4a60a30d0081bdc9690c1461a01037bd0d65628c34020677a1acac51868040fce424948a30d0081b6bc696b3d43a00e3f9d283d018c3401c7d9b5439873826038fb36a8738e704c061dbd862640544a02a33eb6d616624940546d7a5a830150e80a8fcd929340a5150151fd3259a814a2a02a3f3669250294540547f64924a0528a80a8fed890140a5150151fa3b492734c59c2a3fc5641ce698b38547f8e4809cd31670a8ff0d9cd314924e151a7dd6a2a3564280a34fbad54e6ac8501471f758aac930ca028f3e6ac950e6194051a7f56a2a3562280a3ceeac3546ac4501469fd5aa9cd588a028f3f2b0750eb114051e7e5622a1d62280a3cf4ac2d43ac4501469fd5aa9c7588a028f3f2a8738eb114051a7f56aa61d62280a3cfcaa1cc3ac4501471f758aac9408a028cbf635950e8114051c7ed62ea1d02280a3cf9ab2543a04501479f9543ac5408a028e2feb155a26114051e57d51ab44c2280a38fbac5564984501479d7546ac9308a028f3baa8d58a6114051c5fd62ab4462280a38fbac55648c45014797b568a87188a028f3e6ac950e3114051e7e550eb1462280a35ef2d5986a02501479f618aac9404a028f3eca8f5928094051ef5861ab2501280a3cfb2a3564a0250147b76506ac9404a028f3ec2855928094051e7d9592a1d01280a3cbd2b4543a02501479f2564a87404a028d3fc35558a8094051e7f062ab1501280a3dbe2d4562a02501479fc547ac5404a028f7b830d58a8094051e7f151ab1501280a3dbe283562a0250147bec5a5ac5404a028f3f8a8758a8094051e7e150eb1501280a3dbb2b2502a02 else 0x8b000176f1002e00e015054202580e4037c100640a63416080b11442b02c40b7820000006f9b813203be087818c2009a0201a03740a682008080323100812a057c104016d0200001f202c40a603660cc044e022408802da0800010005202bc09a04c809b05910302680a68201d405910026409a02980c130430298093c1a0500058c0805b03ea0c0428280b5d06e417e01030000201e00bc02029805e04011020c0a60200809a0208080a6010000780404000000027020100000000bc07403b80eb041007703600800f0301003c08040003403b80eb05a026407582807581000000000000009c1806706011c18060e2403c0125c4807802008b8900f0040000014e12f0081014c021008602980801012d71202807701d40801012d712020000680ee03aaa0a06b84808402180a60220534080ea02f1ca11282814d0700ee03a813803b814d04e840080005a100300fb1c47e01829508b8040800069015ae23700c10f700ae2304000000a840080003a1002ae2302be0502800100a6028000805301000000ea024c8100a6020758134057c1004dc0c831020130066a0a053017e000220075036008000d8019a84014c040000000000b16041014d0400813203b81204d01040416102980dc82000360040000000000000000000000000000000000000000000270301805703810000000000000000007a09940c080023101000000000000000000000000000004d404000050501029804000007a010001e8040af0102bc04000000f03013c080400230018ce465231918489f44621df0e785f41e20e1068830403dff2ff17e43f01f70fb07b9bd55e9af0675f3ad9d5ce8272cb891c1cdce6d13629ad6d6369eb49d9e0ce867032e1944c8c632317186cc2060c30417f4bf25f52f897b4bc45de2ed1758b965b6ad09674b2458e2c195fcaf6566aa91518a8453e29d14d8a6452e295147ca2850927ad3889bc4caa63530a97d4aba50522c90e4742309174894446221109a8374061fccfba7a13bd9d44e767333959c54e1a6e035d1ac8d386733249904))
def level9 : Packing := (224,6,8,0,0,13,1,nd9)
def nd10 (i : Nat) : Nat := (if i < 7 then (if i < 3 then (if i < 1 then 0xbf549e81c4021efeaa2d03880437fd58898710087fbaa0d30e2010ffe540e61c4021bfeac44a3880437fd58794710086ffab0d28e2010f7f551651c4021ff6a82ca388043ff954394710087ff2a0728e2010ffe538e51c4021ffca61ca388043ff918b94710087ff2b1528e2010ffe462a51c4021ffc8b54a388043ff918994710087ff229328e2010ffe562251c4021ffc8c44a388043ff916894710087ff2a9128e2010ffe452251c4021ffc8944a388043ff958794710087ff2a8f28e2010ffe541e51c4021ffcac34a388043ff954694710087ff2a0d28e2010ffe539a51c4021ffcaa2ca388043df954594710087ff2a0b28e2010ffa541651c4021ffcac24a3880437f958494710087ff2a8928e2010ffc449251c4021ffca824a388043ff94e494710087ff298928e2010ffa529251c4021ffcac0ca388043efd128a4310087dea2494862010fbf462290c4021f7ea83d2188043cfd545a4310087dfaa0b4862010fbd461290c4021f7ea8252188043efd503a4310087dfa9474862010fbf120690c4021f7ea93d0188043dfd545a0310087fea2494062010ffe528e80c4021ffca41d01880437fd5889c310087f7aa0f3862010fbf148670c4021ffe280ce188043ffc1689c310087ff82513862010fef159e70c4021fde283ce188043ffc5069c310087f789cd3862010f7f151670c4021ffe282ce188043ffc4c59c310087fe82493862010fff141270c4021ffe2624e188043ffc4a49c310087ff8a073862010fff128e70c4021ffc251ce188043ff84839c310086bfab152862010dff562250c4021f7e290ca188043ffc50194310086ffab111862010dff561630c4021ffca81c6188043ff94a38c310087ff8a031862010fff128630c4021f7e2c4c61880437fc5878c310087df8a4f1862010fff059630c4021ffe282c6188043ffc4e58c310087ff898b1862010ffe140e30c4021ffc271c6188043ff84c38c310087ff09471862010ffe44a230c4021ffca83c61880437f95858c310087bf2a8b1862010ffe541630c4021bfcac246188043ff11248c310087ff2a091862010ffe140630c4021ffc270c6188043ff84a18c310087ff09031862010ffe062e30c4021ffc2b546188043ff816a8c310087ff0ad31862010ffe05a630c4021ffc2a4c6188043ff81498c310087ff0b0d1862010ffe159a30c4021ffc2a346188043ff85268c310087ff09cd1862010ffe161630c4021ffc0c2c6188043ff85658c310087ff02cb1862010ffe151630c4021ffc0a2c6188043ff85258c310087ff024b1862010ffe141630c4021ffc082c6188043ff84e58c310087ff098b1862010ffe159230c4021ffc2a246188043ff85248c310087fe02491862010ffe131230c4021ffc25246188043ffa461a0108087ff88c31021010ffe11862042021 else (if i < 2 then 0xf69075168010d7fc62a92d0021d7f8c5d25a0043cff18aa4b400879fea8f4968010f3fd51a92d0021f7b8c2525a0043ef714924940087beea8e4928010f7dd5189250021f7ba93124a0043df754524940087deea4a4928010ffcd20e8250021ebfaa3d04a0043d7f546a0940087afea8b4128010f9fd4968250021fb9a41d04a0043eef52594940087bf6a8d28e8010efed59251d0021ff98924a3a0043feb4a4947400873fe2d558a8010fbdc4929150021f7ea92cc2a0043bfd56498540087fea24930a8010fdf54126150021ffca41cc2a0043d7f16aa0340087afea8f4068010f5fd51680d0021fbb892501a0043d7f543a0340087ef69474068010fded20e80d0021fbf280ce1a0043fbe5679c340087f7ca0f3868010fef939a70d0021eff2a2ce1a0043efe5259c3400877fcac93868010ffd849270d0021fbf2824e1a0043ffa4a39c340087ff49073868010fff130a70d00219ff8c5ca1a00435ff58a94340087efca032868010fafb4a270ce021f5f6934e19c043fbccc29c338087f7c9813867010fef9386804e02197fec5d2894043aff569a0128087fd394728a2010dbfd62482c4021bdfac3905880437df58620b10086feeb084162010dfed60c82c4021bff2c090588043ef752824910086dfe3132922010f7ec62a51c4021dfdab44a388043dfb54894710087bf6a8d28e2010f7ed51651c4021dfdab24a388043ff312494710087fd694928e2010ffe560a51c4021ffca414a388043ff94a3a0510087fba98b30a2010ffe528e6144021ffca51ca288043fe94a394510087f79a0f3862010fef339a70c4021dfe6b346188043efcd268c310087df9a4b1862010fff130230c4021ffe230d0088043fbd4e39c110087f789c33822010fff11867044021ffe230ca0880437fd58829310086ffab0a5262010f7f5514a4c4021afe8c552788043efd128a4f10087dfaa0d49e2010fef539683c4021fdea71d0788043ff9483a0f10086ffab1139a2010fef541e7344021ffca41ce6880439fd18ba8b10087bfa3135162010f7f4622a2c4021efe8b454588043dfd128a8b10087b7a30f5162010f7f541ea2c4021efea8354588043dfd4c4a8b10087bf29075162010dff561e82c4021fbea83d0588043dfd545a0b10087ff29074162010cff562c82c4021afeac5105880436fd58920b10086f7ab0e4162010df7561882c4021bfaac2105880437fd58320b10086ff2b064162010dff160482c4021bfeac44c5880437fd58798b10087fbaa0d3162010ff7539a62c4021ff6a82cc588043ff948398b10087deaa504922010fbd549c9244021ffaa8392488043ff550624910087fea9cc4922010f7d55149244021f7a89292488043ff550524910087dfaa4f4122010f7f55168244021ff8a41d04880436fd18994910086ffab0f40e2010f else 0xb5439cd401079fe2933968020f7ed50e72d0041efdaa1cc5a0083cff149a05401079fe29338a8020f3fc5265150041efdaa1ca2a0083feb4a394540107bf6a874068020f5ed50e80d0041ffd280c61a0083f7a5018c340107ff49cd1868020ffe939630d0041ffd262c61a0083ffa4e28c340107ff49851868020ffe928a30d0041cfdaa1d6888083dfb5439cd10107bf6a873162020ffb53965144041efcaa1ca288083fe94a3945101075fc3174862020fbf941e90c4041f7f28352188083bfa5688c310107ff4a0f1862020ffe941a30c4041ffd27346188083ffa4e58c310107ff498b1862020ffe128a30c4041c7fea4d6529243af7924aca524863ffb105aa9310c7ff614b552621c7fe9296aa4c438f79242d5498871ffad45269290f3de492a452521c7fcb5528a4a434ff98aa4f494861ffb175229290c3fe62ea452521c7feb2548a4a43cf7964a91494861ffb165268290c3ff62ab490521d7bcc256920a43aff480ad2414861ffb165248290eb7f526b310521c6fea4d6620a438df949acc414875bfa495988290ef6f20eb310521defa4056620a432f7989ac8414875efa935908290e3df526b210521c7f6a4d6120a438fe949ac2414875fda495848290efeb20eb090521dff24056120a43aff549ac0414871fea935808290e3fc526b010521d7fa9256020a43bfb483ac0414875ef2495a66290f37f526734c521afbec550524843cf7d49a0a490867efb164149210d7df6288292421b7bec4905248437d7d8620a49086fedb024149210dfdd6008292421c7beb5124a42436bfd8720b48486dbfb0c4169090dbdf61082d2121b7dec1905a42436fdd8220b48486dfeb004169090e3df5a8b25212187fec5569a0243cbfd49a0f38487d7da0f4867090fbda492944e121e7f6a2d289c2436fed84a5138487ded3094a27090f9fb412944e121f5f6a4d079c243ebed28a0f38487d7da4941e7090feda49283ce121fdd641d079c243fbe480a0f38487ded24949a7090f3fb516934e121f5f6944e69c243ebed249cd38487f6d24939a7090feeb20e734e121fdf2404e69c243ef6924a4b38486dfdb094967090fbda61292ce121f776525259c2436fed89a0b38487f399cd30a7090fbf3496614e121fee662cc29c243efcd2498538487fe924930a7090fff1202614e1218ffec5d48942438ff969a91284871ffad54a25090e7df5a8924a121cffab51609424377f5882c128486feeb085825090dff5608b04a121d7f6b4ce1a00435ff18aacf400873fe2d559e8010dfbc616b3d0021aff8c5527a00435ff18aa4d40086bfeb145968010defd61cb2d0021befac3165a00437f75842cb40086ff6b065968010dff5608b2d0021bff2c0965a00439ff18ba8b400863fe3175168010d7fd61ea2d0021edf8c3d45a00439ff564a8b40087b)) else (if i < 5 then (if i < 4 then 0xea4d6320a838fb949ac6415077e690158c82a0efdd202b110541c7eea4d6220a838fd949ac4415073f3a8758882a0efd5202b110541c7f6a4d6120a838fe949ac2415073f5a8758482a0efd9202b090541c7faa4d6020a838ff149ac0415073f6a8758082a0f2ff52683ce541e5fca4d079ca83dbbd43a0f39507f6e90141e72a0f37f526734c541eedea1ce698a83fd74809cd31507fe690141e51a0ddee622b34a341ff9a4056694683ff34809cd28d07fe690158a51a0ffcd202b0ca341fbba40507a0483ff348094740907bb7a8739a6120ff5d202734c241e6fea4cc598483ddbd4398b30907fae9013166120ffcd20251cc241ffaa4050298483cbfd492cf28907b77a8659e5120fafb484b3ca241fdba40167944838ffd49acd289073f7a8759a5120efdd202b34a241ff9a404a394483deb98a94728907f572cf28e5120ffa738a51ca241ff1a404a394483df9d43a0528907fd394740a5120ffd5202814a241b7e4c1567a42836fed889cd48507d7da0f39a90a0cbfb62c82d2141b5f6c3905a42836ded8620b48506df5b0641690a0dbf360882d2141b7f2c0105a42836fed889cb48507d7da0f39690a0fbbb28a72d2141b7f6c44c5a42836fed8798b48507dbda0d31690a0fb7b39a62d2141b7f6c2962a4283efcca22c548507cfda0f40a90a0dbfb6227152141b7f6c2ce2a4283efcca29c548506dfdb1130a90a0fb7b3166152141f7e6814c2a4283ff348094740507eee90140a80a0efdd202b44e141e5fea4d079c283dbbd43a0f38507f6e90141e70a0fedd202714e141f5f683d219c283ff6480a0338507fce90128a50a0ffd920280ca141ff9a405078c283bf3480acb18507fe690140a30a0ffcd2025146141ff92405018c283fbad079c318507fe490138630a0ffc920250c6141ff92405688c2837f8982acf18507fe490159e30a0ffc920283c6141ff92405668c2837fad889cd18507f75a0f39a30a0fbeb48a7346141ff92404e68c283ff2480acb185067f5b1641630a0dbeb62482c6141bdd6c39058c2837dad8620b18506ff1b0441630a0dfe960082c6141ff92401058c283fbad079cb18507df5a4d39630a0fbeb48a72c6141ff92404e58c2837fad8798b18507fb5a0d31630a0ff6b39a62c6141f7d6914c58c283ff248098b18506ef5b1058a30a0deeb61cb146141bed6c31628c2837fad852c518506fd5b0a58a30a0dfe9600b146141ff92401628c283f7ad07a0518507fe490140a30a0dfeb6227146141ff92404e28c2837fad8898518506ff5b0f30a30a0ff6b39a6146141fed662cc28c283ff8d0298518507fe490130a30a0dfeb61e5146141fdd4c3ca28c2837fad8694518507df5a4d28a30a0ffab3965146141ffc4b14a28c283ff8d0294518507ff19c528a30a0ffc92025146141e7f8a4d07a0083df else 0x58a6114051affac5462280a3b7f5688c4501477eeac9188a028f7ed50e3114051dfeab1462280a3b7f568a02501477eeac9404a028eff558a8094051eff0c5501280a3b7e568a0250147bfca8f404a028ff7861a8094051eff2a3501280a3f7e506a02501477ecac9404a028f7f950e8094051efd2a1d01280a3bfe562a02501477f8ac5404a028f7f850a8094051fbf281501280a3fee4a2a0250146ffcb11384a028eff95a27094051dbf2b44e1280a3dfe5489c250147f7ca0f384a028fef939a7094051ff7262ce1280a3bf65649c2501477fcac5384a028eff158a7094051eff2a14e1280a3fbe4e29c2501476fead1184a028efdd5923094051dfeab1461280a35fb58a8c2501477f6ad1184a028eded5a23094051df9ab2461280a3bf95628c2501479bfa9330e6028f76f50e61cc051affac416a880a35df5862d510146bf6b065aa2028cffd620b5440519fbac216a880a39ff5882d5101463feb105aa2028e77d618b544051cffa8316a880a39ef5852d5101473eeb085aa2028e7ed60cb544051cfda4196a880a39fd5822d5101463fe3155a22028cffc62ea444051cff8b5548880a39ff16aa0f101473fe2d539a2028ff3d41a62c4051fe7a734c5880a3feb48398b101473ee2d44922028cffc62ea1c4051cff8b5543880a39fb16aa87101463fe31750e2028e7ec62ea1c4051cfdab4543880a3dfb4e6a8710147be624950e2028e7fc5aa81c4051cff8b54e3880a39ff16a987101473fe2d528e2028e7ec5aa51c4051cff8b5542880a3bfd18ba8510147bfaa9150a2028f7f550ea144051efcaa1d42880a39ff16aa05101473fe2d530a2028f77d51a6144051fe7a62cc2880a39ff16a94510147bf6a8728a2028ffad28e5144051efeaa1ca2880a3fed4a394510147fd294728a2028efbc5aa5144051ef5aa1ca2880a3fed18994510147fda31128a2028ffb45a25144051ff6aa44a2880a3fed12894510147f5a30f28a2028ffb541a5144051ff6a734a2880a3fe512494510147fda9c928a2028ffb53125144051ff6aa1ca2880a3fe954394510147bdaa8728a2028f7a550e5144051ff4a41ca2880a39ff16aa0310147fda9454062028eff85aa80c4051cff0b5501880a3ff6124a0310147bf4a874062028ffe920e80c4051ffe2a1501880a3f7e502a0310147fdc9454062028ffb128a80c4051ff7262ce1880a3ffa4839c3101473fe2d51862028d7ed62a30c4051cfd8b5461880a3fe94a28c310147f9da0d3161028ff3b39a62c2051fe7662cc2840a3fce4c598108147fbc9873021028f2ff52683ce641eddea1d079cc83fb7480a0f399071f7a875a482a0ebdd202b490541c5fea4d6720a838bf949ace41507377a8759c82a0eedd202b390541c6fea4d6620a838df949acc415073b7a8759882a0ef5d202b310541c7d) else (if i < 6 then 0x154a23128d3fe62a9346251c7beb5124a42a3cbfd47a0f485471efad459290a8cbfe62e8152151b7f4c4d67a02a3e7ed06a4f405475bdad259a80a8ef7b59cb350151f6f693966a02a3eded242cd40547fb590659a80a8ef7a588b350151fef240166a02a36fe989acb40546dfd31359280a8dbfa626a250151ffb240544a02a3ef696924940547ded29249280a8fbdb49c9250151feb4b3124a02a3ef6d2624940547eeda0c49280a8ef7a59ab1d0151e7f4a4d43a02a3dfa949a87405479f531350e80a8f7ea5a6a1d0151ef9492543a02a3dfa180a8740547bf490150e80a8dbfa626b150151b7f4c4d42a02a35fe98aa4540547ded24948a80a8dbfa6268150151f3f4a4d02a02a3f5e966a0540547cfda4940a80a8fdda4928150151fbf240502a02a3eee94994540547f9d2cd28a80a8fbbb4925150151ff34924a2a02a3dead4394540547fd590728a80a8fdbb40a5150151fb66814a2a02a3fecce294540547fdc90128a80a8f2ff52683ce151edde83d439c2a3ebed07a43385475fda495a270a8efeb20eb44e151dff2405689c2a36fe989a9138547d7d9c54a270a8fafb4a283ce151f5f6925079c2a3fbac83a0f38547f7c90141e70a8fafb38a934e151f5f6944e69c2a3ebed249cd38547f7590739a70a8fef9202734e151fc76734c59c2a3eeed2498b38547fd590731670a8fbbb48a62ce151fd76714c59c2a3fee48098b38546dfd31351270a8efdb5a0924e151fdb6839249c2a3fb6ce624938547fcd98a49270a8fedb388924e151b7f4c4d029c2a3fcecc5985385471f73135aa30a8e7ec602b546151eddea3d078c2a3ef3928249185473f5ad540630a8feeb41e70c6151affac4546280a35ff58a9cc501473eea93590a028e7dd51ab214051dfba73564280a39f7542ac8501473ee285590a028efdc40ab214051dfba71564280a3bf7564a86501477e6ac950ca028e7dd592a194051cf9ab2543280a35ff58a986501477eeac930ca028f7ed50e61940518ff8c5562280a39ff549ac4501473fea91588a028e7fc522b114051cffaa3d62280a39ff546ac4501473fea87588a028e7ed50eb114051cfe8a1562280a3bfd102ac4501477fa9c5588a028e7f5526b114051dfeac4562280a3bfd188ac4501473faa91588a028e7f4522b114051dfeac3d62280a39fd547ac4501477fab0d588a028e7f551ab114051dfea83562280a3bfd4e6ac4501477fab0b588a028efb5616b114051dfeac1d62280a3bfd543ac4501477f2a87588a028e7f550eb114051cfcaa1d62280a3bfd4e3ac4501477fa987588a028eff5606b114051dbfab4542280a3bf7564a84501467feb17408a028d7fd62a8114051dfbab2502280a3dfb543a04501477faac5408a028d7fd62a6114051dbfab44c2280a3ddf546984501477eeac9308a028eff5 else 0xaa50491c79efa8d4a09238f3df50a9412471f5bcc4d07248e3eb7d26a0e491c6f6fb113989238f6df5227312471f5be944e6248e3eb7d259cc491c7d6fa453989238fe5f39a6292471bedec3168946e37f3d842d128dc6ff3b045a251b8dfeb604b44a371e7dea3528946e3ebbce2a5128dc6ef731159a51b8faef4a2734a371fdda404e6946e3cf3d4924928dc7f679cc49251b8f3de492a452271cdfcb5507a44e3eb7924a0f489c61ffb125aa6138c7fd600b54c271f4fe924e6984e3f9f4809cd309c7f2f9cc4926138fadf41c9252171b5fec1507a42e3eb7d072c9485c757fad341e80b8fbce4a09246171c7fea1569a00e37af185acf401c7d7ea4b41e8038feed20e83d0071f5fa92ce6a00e3fbb4839cd401c7f6ea0e4928038f7dd5189250071fdba73124a00e3dbf567a87401c7bf6a8d28e8038feed39a51d0071f9fa83d01a00e3d7f543a03401c7efca031868038f7ed52230d0071fdda83c61a00e3ffa5018c3401c7ef4a031868038f2ff4a2a1ce071e5fe935439c0e3dbbd43987381c7b7ea874027038f37f52661cc071eedea1cc3980e3ddf4c3a81301c7b7ea873826038fe7d30e704c071cdfcb5507880e39bf16a9c1101c7b7e2d541e2038feed20e83c4071fdda41ce6880e3cf7549249101c7f6ea0e4922038fedd3989244071f5fa83d21880e3fbb5078c3101c79efa9059293b0ebfb59680d2761d7f6b2501a4ec3ef6964a0349d875fdac540693b0d3df62a9392461e7bea4527248c3cf7d42a4e49187deda0349c9230f2ff52293ce461f5f680d279c8c3df3d4724928d87de724449251b0fbda49280d2261cfbeb51249c4c3ed7d2824930987bafa8e4926130fb5f49c924c261f6be92924984c3ed792524930987faea004926130fb6f4a251cc261fe9c924a3984c3fdb50094730987fb690128e6130f3df524924a261ff1c924a3944c3feb4809472898797fa9338e7030f6ef50e71ce061e6fea1d27980c3ddbd439c730187bb7a8728e6030ff2f28e514c061eefaa1ce0980c3f9f4e39c1301875bfad330a5030f77d50e6044061efbaa3924880c3fdb4a398510187fd294728a2030ffe520e5144061c7fcb4d46a88a3af716990151147beea85202a228d7df62a7312451e7bea4ce6248a34ffd8229350d471ffac4526a1a8d7ef608a4d4351ef9a40544a86a38fbd622d350d471f72d359aa1a8d5ee622b354351efda404e6a86a3df3ce624950d46bb7b0c58aa1a8d7cf610b154351afdac0162a86a35fb5822c150d465ffb105a6a128e3ff520b4d4251edf8a0167a84a38ff969a8d509479ef292492a128c7ee62ea1d225197fcc5d48a44a30ff98ba87489471ff2935aa8128c3ff624b5502518ffac016aa04a35ff18aac1409473efad44926128f75f518924c251cfdeb3d43984a3ddbce6a87309469ff3))) else (if i < 10 then (if i < 8 then 0x110e220c43bc87390df21ae430885d107820c640007fc0ff01fd03e3c7bd0f721ed43ce07980f281de83bb07720ecf1d8e3a687428e7d1cd039807258e171be437386e30da21b14355c6a10d3a1a64340465e8cb5190831f062a8c311852308460c8c11181230045e68bc5177a2ed45d00b7c16b02d0c58f0af815a42ab054b8a8f150e29fc52d0a52145c27a04f009a21290250048c88ee115c2228441084710421f0c3bf87490e821b7c36b869d0c82182830105aa0ae8148c28d84c108e410ac21183cb07860eec1d9835b06a60b1812b024e03d407880ed01d2017202c403d0065007a00039efa8a49290bb6bdf5889252176e7bea1124a42ed8f7d6a2c9485db9efa8a59290bb7b5f314b252176f7ba94124880edff3124947101dbdee249486203b73fd51690c4076ff9892461880ed4ffd85245526069ffb05524a4c0e3ff526b394981c7fea4d62293038ffce5ac4526071ffad452693c0e37e518b4d448197fec1169a89038ffd422d3512071ff2d351ea240d3df61aa492481e6bcc3549249034f7d82a9249206defb0e5249240dbdf608a492481e7bca4d47249034f798aa4e492079efa8549c9240cf5f62ca312481e6bea494624903cd794928c49207dafa4e5189240f37f524a34e4818ffec296aa45038ffd252d548a071ef2485aa9140d3fe62a93d2281c7fcb5527a4503cdf94928d48a07daf24851a9140fbda490b0d228187fec5949945038ffd6729328a079fb9c45265140e7de5a8924a281e7bea4924945038dfd6928d502071bfad259aa040f57e51aa150081faf4a3461a010377f58729340206efeb0a5268040ddfd608a4d0081bb78c2d67a010373f5872cb40206eeeb085968040ddfd608b2d0081bbeac1165a010377e5812cb40207cfe2934968040f9fc48a92d0081b3f8c4d44a0103e7714924940207eae28c4928040f9dd4989250081f3ba92924a0103f7716224940207eee2844928040fdd93049250081faf8a34e4a0103f7e4c19c940207cee24948a8040ddfc62e30d0081fbd8c5c61a0103f731248c340207ef43171868040fde95a630d0081fbd0b4c61a0103f7a5498c340207ef42931868040fde959e30d0081fbd293c61a0103f7a5648c340207ef4a891868040fde949230d0081fb9092461a0103f7a4e48c340207ef49891868040fde960a30d0081fbd0c1461a0103f7a5628c340207ef42c51868040fde948a30d0081fbd091461a0103f7a0a28c340207efc8c34021040fde91868042081a7fec4149a92e38df9692cd521c71efad45929438f3df518b252871e7bea1164a50e3eb7ce22c94a1c7d6f3094a27338fa7f492734c571fcde41ce698ae3f9f4809cd315c69efb0b5249238d3df60aa492471e7acc1549248e3cf7989a90491c6befb0d5209238f75e61aa412471e7be93548248e34f7d8 else (if i < 9 then 0xfc2df733ede7d92f9edf2a3e307c50f84deeabdac7b48f671ebc3d507a76f405e6d3cb478def0dddffbbe877c0ef61dda3bac76e6edadda3baf575a2eaf1d52ba6d7466e465c88b90971c4e261c483864703ae055bf0b7a86f04dbf1b6c36d06d90da59b4736586ca0d8edb0b35b86b46d66dac9b58b6b06d5edab9b56b6ac6d56daa9b54b6a86d4eda99b52b6a46d46da89b50b6a06d3eda79b4eb69c6d36da69b4cb6986d2eda59b4ab6946d26da49b48b6906d139a23343e686cd0b9a13341e682cd039a0333fe67eccfb99f333de67accf059dcb3b16752ce059bcb3716694cd0999d33326636cc4d96a32cc6550c9b1917b1f26366c5d989c31306218c39d86fb0d7619ec2ad851b07e60b4c14982530426074c0197f12fda5fa4beb57d2af9d5f2abe357b4af615eb2bd457a4af415e72bcc5794af125e14bc0977d2ebb5d66baad751ae9b5d08b9f173a2e6c5c6eb8096e6ad985ac6b47d68bad0059f0b3c16742ce059b0b30565cacb158f4b109606ac0557a0aded5b9ab5c56a8ad315a22b3c5668ac755832aef55ceab7d5642ab15552aa8553b2a5e54aca9395232a3e546ca8b95132a1e542ca83950329e053b0a7414d3a952527aa4a1487a8fa51a8a27944b288e510ca1f943b28264fcc9f453e4a77a4eca9d753a427404e569bdd377a6e74dbe9ae5358a6a94d429a65348a66c4cc8997132a264c4c8898f1303a5ff4b7296c52d4a5a14b3296452c4a5814af295c52b4a5234a36944d285a50349f692d5256a4a5493a9255246a485487e90dd20123cd472e8d451a4a31446188b5d150226a446688ad111a21b43e687ad0f1a1db43a6872d0e1a1bb436686ad0d1a19b4326862d0b3a15f42ae853d0a3a13f426e84bd093a11f41128205036206440b881510262044407880d101620043fb67e98fcf1f963f1c7d4cf9f1f163e1c7b9cf681eb83d2879b0f239e3f3c6e78bcf139e1f3c2e783cf039dff3bee77bcef39ddf3bae773cee39dbf3b6e76bced39d9f3b2e763cec39d7f3aee75bceac1d433a7674cce959d233a36744ce859d0339f6735ce599cab392c7238e3c9c52385c7028e011bfa37e46fa8df11bcb37866e7cdc39b7f36b66cd8d971b26363c6be8d791aea358a6a84d4c9a7534a268b4d0419f333d6678cce719a7333e65e8cb9193e32526450c8618e5317a62a0c4098102fd85f90bee17d42f605ea0bb9976b2dec5bb8b6496b22d365a4cb3f16762cdc5998b2f16562c9c58dcb1796272c3e585cb0796072bfe57dcaf795e72bbe575cad715a62b3c55b0ab2152329c45284a30143b27f04ed49d693a5273a4dd89af9357262a4c3498292fd25ea4bb497292cd258a4af495a92ad254a4a7494a928d250a49c09341260247848d0908120823e647ac8eb11bf236e46bc8cd117622dc459889b112e224c447888b else 0x3f78bddadadcfb029c0c409a2310b5829a18b0c5863b3d861e24f1002582be100108660db77a06223102582f210000000e383800773c9e4ee793cbfbeee793c9fad773c9e4d7d5072037419407878082f01d30e011150311882bc080300214810150048c290000300af02fb05f5ebeb97d6afac5f537e9c7d20fa17f40fe7dfcf3f9d7f317e4ffc97f8c5f16be10fc19f7e7efafddcfbb1f715ed77da47b40f671e8d7cf2f9ddf36de6bbcd3799ef32de63bcb4f961f2b3e547c86f905f1fbe367c477886f0fde1dbc27f847f039dfc7bc4f727edbddb13b33762bec47d86faf1f58fea83d4e7a98f529ea43d467a88f509ea03d3e7a78f499e773cd7797d7292e44dc7278b67164e1afc33f7c56f39dd95bb0b70f6dacdb49b467688ed09d9c7b2976386c68d8c1b1636286c48d881b0e36186c28d841b0635f36bd1d793ae975ceeb45d67bacd7596eb25d63bac23579eaebd5c7ab2f553ea83d4bfa8eb5196a2ad40ba7f74fae9b1d31ba6174bee975d24fa37f46be8cfd18fa2cb4556895d11ba21743ee82cd049a07340a680ccfd19f833de6784cef99d9739f671acdeb9b4735d6692cca7987f2f565c2cb1d9567287e4eac963922b241647ac8e591ab231642fc8118f871dd63a3c7378e4f1c5e383c6f78dcf1b5e363c6b78d4f1a5e343c6778ccf195e323c6378bdf177e2e7c5bf8b5f159e2abc5478a6f143627ec4ed89bb1256242c475885b10761e7c3bf875f0e7e1abc27584cb0956122c235844b0856102c1f5835704a608cc109810701ce024bfef7f22fcc5f56be657caaf915f1abe257c2af815efabde57baaf715ea9bd437a66f48de6dbccb7976f2ade31bc537886f0cde02bbf577caee6ddc5bb7b76d6ed6dd98bae575aae98dd0dba0b73c2e63dcbfb96f72bee45dc67b87170c2dfbdbc4b7796e62dc1db7bb6e76daedb1db27b63f6be2d785ae8b59b6b16d565a5cb4a968b2c975926b23d645ac7958cdb18b62f6c4cd884b0f961d2c365864b0b960d6c16d825b03b6056bacd751ae935d06b9cd731ae535c52b7fd6f7addf5b9eb6fd6abacd558fab1b562eabf7575eae7d5c7aac1547aa7054d8a9a15322a6054aba8ed4f4e95752a6a4f9498e92dd253a497490e91dd233a3f145be8b3d15fa2af453e889d10ba20743ee879d0a1a0c740528064fe19f553d3e7944f139dbd38c2685ccf299b332926404c5b9847306e5ed4bab96e12da259d4b3295e12aca5554a9294d32942514c9f2938f26764b0c90691fd22fe45bc8af909d204e3ec479a8e771cce383c6c58d1519ca312461c8c0517562d3c5678a9d13ee279c4eb898b127a23c442e87ef0ece1b7c32b86470bfe17bc2be851b099a0fcc1f183d307860ecc1d1839307060dcc1b182c10562098c0fc81e903b206440c08171024603e4037800aff0dfc6bf787e6)) else (if i < 12 then (if i < 11 then 0xa0800d601b4020820300c846f8060410196e8041040340334806d0082080cb740204d01a0180000016903033c10000000000000000000000000021437008100000000000000000025d3fbbe7db7bcddc0684e9e010a185ac26b0c01e01010000000000000000d321004b82d190803c4168051c84012c0c000003a6c0e1a09a81c1e81c04ed03826a08016041d04c13a098120a3814135a09021f412041825a0904d0100000000000000000000000000000000000000000000000000000020308111880800000000000000000204b6818120784180100012c0402a06027d04940e09d03940c090a1e81c080000000001a81c0802143d03811118c080204ba83012700824408000001b03a40c080001014700804813c00c0400826b00c04826b00c04813f00c04b00c04f0248300800001440720516814100102600f80800e080c8348100c462020ca0100c8146a0b043c01810505502011013019404e60784087c075418c41ba240c9854233e01020000009c03f0002003809be01303818004078c3015ca068233e12905032814010134c0e04981e05384408002bc04000000000001381408000000000000000000000003709a9c0e08000000ac1280af8200003cc09e710057c1802e609a38802be0c00f304d1c4015f06007988c4e200af83870802781001cc813ce200af83020ec0279c4015f06000000709a9c0e0938140800000d048d82c15e06000000000000c46102000000000000000000702010000409e70902004134607020038400801c0805c02408000014405027a828080001bdf303820a0800000000000209ac0c0000004d40400b80048110080c50302600afb77b603581888c4c0f8048500000007200c78329415204057c208c4040000205c4620af820000002401040a602008003a808002011b81d408462020042a0100b8100ac096804b8101ab8101e009025dc0808010259c08099416040c21703059411c44040003002031015e0475063381806426b0600286c0321358200384d4e070484d4e0604000000000000056d84d4195040000000b2014096708028e05f000202580a0259414088096082022025822c0880960820205900800000230382680802027981c086c2100141e200b90300162232004583680872c084002844182d60da04005812ca0b0480102029808d004804a8282980e0259414080000015007805781114144620401c62a6008c5e2050c053020052ca44016b0534100aa802f014c040014cf63b30030416450505342000956c0022c14c04018d2470f0107202f0150080282902682c80801de64980a0aa040b588ce100a44016a0a602238112800a0a0b2057818011c2203011a780839015e08213367c623102683420c044c41e060dd05301800398518181de24f030540200000011c880c0469e020e405b82 else 0x14008205941005204402010022000c01782be0a001026815e04d041816a0818ce49ec66dc21b0b4058015f0800000000000000000067056089820c0ee0af04006a812e0505a014aa10831030000426ba060200005d81fe010423101760c12408a0405341880600bc1b5041c0980ea04c06d419c075826815f040d101070098c0101040da83805201881198300c408000620238c20acc106031057c1b540970382409603e0200902009a2090202f014c062ec0e831820000a40d505025ae0683182987008de0265c0c09f07a026381e08809807702305200850082071412f80eb5055024184028407706d0120a88100004098f02020000074c0a8065410040d109a810203c163e06502a015f068314432040b9019c0f021a0a083281b00482114809a062011e76299d49aab9d9d7ff549557ea04dfcf3e04ece700e206c03441720c50608374151100001805a81d409f6e04181d6a10a04848069c14c0828202c8e604c837414d06007025d42140807d882080ee07583503b81d4092fb6ef6dbf6c13408341a84d410407586426ba0602000000b1041036a0800708500ea0a88200f0080908b817c0810022187f0378048e80af0402f808000000000000000000000000000000000000000000000000000000000000000000000000e0dba8160c40c000000000000000000000000000000150020000009b004123040000d05450c6080000010544080043260c7a020b203008e05801023280004e240a6035a07002084c1881ac8380104260c40c590700207e05701ac8580104260c40c310e0050620b703008e11801025801067810000004703c0081004e80833c0a381e0040800000001c03938360040e38160040800014c080f004000000010416802040000000000000000841604000000001044e0d006d41000000002702810000000081d83106d410040e418836a08020760c41b5040803b0620da820010f83106d41005840a2683106d018027088100000000004e070200000130ec18836a080230ec18836a08100760c41b505000103b0620da8200984702bca2683106d020027038100000000004e07029c1a0538140800040a8814e07020001e7057dc0e0882be040000000000000000000000415083102000027031039812609201141d0103d02c80e06203031014818c0c0c405102d03102260a8781c0c40c0000000001202d10280a841882bc0cd015d0104202840e0620200130b815091381883681206202010310100818808260b03105441000000501580600400000000010a0730f020000000000006815c04f0268180230902589035c15a060000000000000000000023090a6240d70568180000000002c092098482b98d6060000000000009f026906070804102001c04f28d01340ce04d60c0104063809f83004101a6e09a418181c09) else (if i < 13 then 0x2b06c8281000000005905b020100000002f0040000024025804080001041601008017004f00c10000002077a82817c08c791c9813026a83105e02d614000000000000000082080b40462a818101780a60300000800c02581041b406018040120002f06d01040002c0da0200580980da8200e6204c025836a0d02d00a808000000000000000000006f04181dc86306000000d011606040000011427402040000015806040000b80583c0400000001508014c8482c408009f025e420c150682c7212040190801c407805e4100000053097020120827020110000820b2028000202c09c053410e0801380a68200721260602c8400800000003c362120bc0534180381340828200001c14d0200e09a810489f26183041b80a68300500ea0a8025ae79b7f77eff6f5b3edffb6bfedb04d0208286135f01f80508643505a829a28000002482d0100934200d20400014421c0205b03010000000000581a2c030400000000bfb9eb9ee2fdb7bef61cd6188f827c020c5056850c26b0e0000000000009080168400c040000068194117f0081b240004103502980f000360298080000105809c053412d08d02010000073cc98520a380bc49e1c0af054276cb7e90502f209a7d8341e23601830000000030580855600b002980809bdbb7a666fcddb37c04c025dc4ae1ca0a305c32f0f3df7973bcb9ddde53febfa0e739e52d7eabb02c9081b80d006080114140e205902be20034c0b405f8273814080000000000012fb81c0ee706832603cdf9f39800c105902080980040534300000000396c0b4e0703bc18000000070cdba3160624828195069af816407702d41f0ccd18b01464140bc8300db8341e2305a80510b401300ca1cf3370130188d05054421c0b40518270380955400b0029809779bedda86666fe1bf0130096f09902019416ae0b8753df2bb4ebbf4eeeaa7fd7f5d8739cbcf0f79e7842c9003701a00c100248281c40b2057c44825206411703a0145a1004b03409770302570303c011bc10607702d41803e5b605ab03b8060fff409903ac13cd81680a36078300dfa059016a080196df02c9c0205a834d7c0b203b816a0c02816a0758169c0304e70681381680a305a80520b0012c0f4816003c416a058009705d630419c480f10628eef30c0960bea8402c61001bd8c10671203c418000350db6dbb7db6099a84282a0decc106709f00c183846301b80a6826eb608303ad4220db1b6db6dedf4132a0aa84418039e083053413db1b284141414d06f6608328478060c820e07866646d820c0960698300a81a605fd9c47c03047efe01388c101edd97e168034c1103120786d9af990188168034c180001012ec0e042025982c088097607025d80c30099002029a0dc813205a02581932480a00082059410994920000820594106492 else 0x1a2202b0601313581983008040000050224e1e04c0df02a810032b085832c340c00e202e010814c0600d30d500810001001484190040077819c0e08e5950c14d0570201000007bedfdfb29bb73ffb7f959bedec34c26c11c0852a128c011407df8181cc0bf123084380002ebc401710601a02a150a08000000000224181540400000045203002012815006000080c005204965c0b0d02049a4d4100000029231d05014062c1780b182f5981ca0b04171e10108a7809c02035415f085cf200349e0270080be057c20e0811780405e02c60c207781173c8024f01380405f02be101201c60be057c1000001880e0d905f41000f83272c16294305d41980b042841582c416f04000000000100000000000b2200024290201e015e067aedb7db7adfdbff6e7ed9bfc132077821c0c5e0614311882f014d1247240304f037808374162084a9170019122460b11882bc11e2e48303c0de04f0105e029815de64ad6606cca0aa040a288ce10d9432418039783035415f06472803040a1bc041ba0af04000847b3ce71f0c454078108cde1e0b105942801cb8ce0e7757cfdbb8f5e7af77152d6b5dc6a95af54e1616ff3f981c80dd118182c194a0a05e029a2108265c5107308c418d0621227419782dc82e81611882d81401fb31e1727d8b09b0603026bc38c0e50506e829a186de48124a000e03bbc181aa0af8400143e1e3f803860220286f03780943015f0c0000520450381222600100e015e045e439612057030000000000000000000000200003602fc08168020082d0a2a04000a1c060508283140816008000000000050201a810080001288c0c06cd0401406cd0401406cd04014281812c08000168200ba0400006002048434181b406e811a0404000000c906142008806b057818981c00114066057818000402414040120a0200000023801841e8241220af8300000000740ed050200740ed0202eb0106c0f50683005a05027d0394160a683740c09740e80e04f40da0404941604be81a426081b00c60091059012ea0d00470081ad50680220c80c7683583609a60768300100cb603481001a06bddb41b20a804f00c21f008118087d683641741b06dc82f8060800000000008000906057811f40ed05823e81da0504b903141609282c0800000000000000000))))
def level10 : Packing := (1158,5,8,0,0,15,1,nd10)
def nd11 (i : Nat) : Nat := (if i < 14 then (if i < 7 then (if i < 3 then (if i < 1 then 0x538087eff3867010fdf670ce021fff5009c043ffe98138086fff5aa5010cffeb54a021affd6994043dffa93280873ff5265010dffeb44a021dffd4894043dffa5128086fff59e5010effea3ca021bffd6694043bffa8d28087bff49a5010effea2ca021effd25940437ffac7280877ff50e5010ffde51ca021effd2294043ffb98528087bff4865010fff670ca021fefca194043ffea0128087ffd3825010e7fea4c4021bffd6888043bffa9110087bff4a22010dffeb344021dffd4688043dffa4d10086fff5962010effea2c4021effd2588043bffa8710087fef28e2010ffee8144021ffdcc288043ffb94510087ffd4022010fffa6044021fff4a088043bfead5100877fd5262010dffab444021dff54888043ffea5110087ffc4a22010effaa344021fff52688043ffea0d100877fd5162010fffa92c4021fff12588043ffea0b10087ffc4162010fffa62c4021bff56488043ffea4910087fdc4922010fffa8244021fff4c488043ffe949100877fd50e2010fffa81c4021fff4a388043ff694710087fed20e2010ffea8144021ffd4c288043ffa94510087ff520a2010fffa90c4021eff52188043ffea0310087ffd2862010ffda30c4021efdd6988043dfba9310087ff75222010f7ee9444021ffdd4788043dfba4f10087ff741e2010dfeeb344021ffdd4688043dfba4d10087ff741a2010ffee7344021ffdd4588043bfba8b10087bf74962010ffee82c4021ffdd4388043ffba0710087ff738e2010ffee61c4021ffdca388043ff394710087bf74862010ffee80c4021ffcce188043ffb8c310087ff31862010ffce30c4021ffd50088043ffa9c110087ff53022010ffea5044021ffd16a88043ffa2d310087ff55262010ffe8a4c4021ffd56888043ffa2d110087ff55222010ffe8a444021ffd52888043ffa25110087ff559e2010ffeaa3c4021ffd52788043dfaa4f10087ff541e2010ffeab344021ffd54688043ffaa4d10087ff541a2010ffea7344021ffd56588043ffa2cb10087ff55162010efeaa2c4021ffd14588043ffaa4b10087ff44962010ffea82c4021ffd10588043ffa9cb10087ff53162010ffeab244021ffd54488043ffaa4910087fd44922010ffea8244021ffd4e488043ffa98910087ff52922010ffeab1c4021ffd54388043ffaa0710087ff538e2010ffea61c4021ffd4a388043ff294710087fe520e2010ffeab0c4021ffd52188043dfaa4310087ff54062010ffea70c4021ffc4e188043ffa94310087ff52062010ffea30c4021ffc46188043ff28c310087fe11862010e7fea4c2021bffd6884043bffa9108087bff4a21010dffeb3c2021dffd47840437ffacb080877ff5161010f7fe92c2021dffd4384043ff794708087ffb3861010fff650c2021ffec6184043ff58c308087ffd4021010ffea2042021 else (if i < 2 then 0xe7fea1d2121effce3a42435ffac548487bfb2069090e7fea052121bffd69a02435ffad3404877ff5268090effea450121effd28a0243bffa8f40487bff49e8090effea2d0121effd24a0243fef249404877ff50e8090ffde41d0121dffd40a0243ffe90140486fff5a67090e7fea4ce121bffd689c243bffa9138487bff4a27090fdfe83ce121dffd459c243dffa4b38487bff4927090ffbc924e121dffd439c243ff790738487ffb4867090f7f690ce121ffed019c243ffd90338487ffd2027090fff6a4ce121efed499c243ffda9138487ffb4a27090f7f6944e121ffe9289c243f7da0f38487ffb49a7090f7f6934e121ffed069c243f7d9cd38487ffb5167090eff6a2ce121ffed259c243dfda4b38487ffb4167090fff662ce121ffed449c243ffda4938487bfb4927090ffb4924e121ffed049c243ffd98938487ffb2927090fff6a1ce121ffac839c243ff998538487ffb5027090fff6604e121ffe4809c2433ffad528486fff5a65090d7feb4ca121aff969942439ffa9328486fff5a25090effea44a121effd28942437ffacf284877ff51e5090effea2ca121effd2594243dffa4928487fde4925090effea1ca121ffbc83942437ffac528487bff48a5090ff7e514a121ffed2194243dfda4328487ffb4065090fff670ca121fff16094243ffe90128486fff5aa8010cffeb5500219ff96aa0043dffa93400873ff5268010effea450021effd28a0043bffa8f40087bff49e8010dffeb350021dffd46a0043bffa8b40087bff4968010effea1d0021effd22a0043ffb98540087bff4868010fbfe80d0021ffece1a0043ffea81400877fd5028010fffa6050021fff56aa0043bfead540087ffc5aa8010eff8b550021fff169a0043ffea93400877fd5268010fff8a4d0021fff548a0043bfea9140087ffd59e8010fffaa3d0021dff547a0043ffea4f40087ffd41e8010fffab350021fff546a0043bfea8d40087ffd49a8010fffa7350021fff565a0043ffe2cb40087ffd5168010effaa2d0021fff145a0043ffea4b40087bfd4968010fff892d0021fff4e5a0043ffe98b40087ffd5928010dffab250021fff544a0043ffea4940087fdc4928010fffa8250021f7f504a0043ffe9c940087ffd3128010fffa5250021fff563a0043ffea87400877fd50e8010fffa71d0021fff4a3a0043ff694740087fed20e8010fffab150021fff522a0043ffea0540087ffd30a8010ffea6150021fff4a2a0043ffe90540087ffd5868010fffa90d0021fff501a0043efea0340087ffd3868010fff270d0021fff4a1a0043ffe90340086fff5aa7010cffeb54e021cffd499c0437ffad1380877ff5227010f7fe944e021bffd669c043bffa8d38087bff49a7010effea2ce021effd259c043f7f9cb380877ff50e7010fdfe71ce021ffbca39c043ffb98 else 0x9a8a439ff2d3514877ff5a2a290effcb454521dff928a8a43bffacf514867ff59ea290edfcb3d4521dffd27a8a43bffacd514877ff49aa290e7fe9354521dffd06a8a43bff9cd514877ff592a290effe9254521cffd24a8a43bff9c9514877ff312a290effeb1d4521dffce3a8a43bf7907514877ff20aa290effe40d4521dffd60a8a43bfe2c1514877ff302a290effa4054521bffd6aa4a433ffad5494867fe5aa9290f7fea4d2521cffd49a4a43dff293494877ff5229290f7fe9452521eff928a4a437ffacf494877ff51e9290f7fe93d2521dffd46a4a43dffa4d494877ff5169290ffbcb252521effd24a4a43ff790749487ffd2029290f7feb552521cffd6aa4a435ffad5494863ff5aa9290f7fcb552521cff96aa4a43dffad149487bfe5a29290f7fea452521cffd48a4a43dff29149487bff59e9290f7fea3d2521cffd47a4a43dffacd49487bff51a9290e7fea352521effd06a4a43dff9cd49487bff5169290e7fea2d2521effd64a4a43def2c949487bff5129290f7fe7252521effcc4a4a43dffa87494873ff50e9290f7fe71d2521effd62a4a43dff90549487bff5869290f7fe40d2521effd40a4a439ffa8149487bff3029290dffeb5505219ffd6aa0a433ff2d541487bff5268290effea4d0521cffd49a0a439ff29341487bff4928290fffa4050521bffd6a20a433ffad441486fff5a48290d7feb490521effd4920a439ffa92414873fe5248290defeb310521bf7d6420a43dffa4841486fff5848290dff6b090521bffd6020a437feac041487ffd2008290dffeb54c5219ffd6a98a433ff2d531486fff5a66290d7fcb4cc521effd4998a439ffa9331486fff5a26290effea44c521effd2898a437ffacf314877ff51e6290fefe834c521fdfce698a43bffa8b31487bff4966290f7fe924c521dffd4398a43ff790731487f7f3026290fffa404c521ef7d4924843befa92490873df5249210f7bca492421ff7d4624843befa8c49087fdf4989210f7be9312421ff7ce624843fefa8a490877df5149210ffbe9292421ef7d2524843def24a49087fdf4149210ffbc8292421ff7ce524843fef98a49086bff5a65210d7fcb4ca421effd49948439ffa93290877ff5225210f7fe944a421dffd4794843bffa8d29087bff49a5210effea2ca421effd2594843ddfa4b29087fdd2025210cffeb552121dffd48a4243dffa5148487bfe4a29090effea3d2121effd27a4243bffa8b48487bff4969090f7fc92d2121effd24a4243def24948487fef20e9090dffeb152121effd22a4243ffe901484873ff5aa9090c7feb552121cff96aa4243dff2d1484873ff5229090e7fea3d2121effd07a4243dff2cb484873ff5169090f7fe82d2121eff905a4243dff9cb48486bff5929090f7bcb252121effd04a4243dff9c948487bff2929090)) else (if i < 5 then (if i < 4 then 0x7fdd2028120d7feb4ce241cffd499c4839ff29338906fff5a27120f7fe944e241effd269c483dffa4b389077ef50e7120ffde51ce241ff74809c4839ffa9330906fff5a26120f7fe944c241bffd6798483dffa4f30907f7f39a6120f7fe92cc241fdfcc598483bf7a8730907fef28e6120ffee814c241ff7480984835ffad3289073fe5265120dffeb3ca241fbf967944837ffacd28907bff49a5120f7fe92ca241fefce594483bf7a8728907fef28e5120ff5e51ca241ffdd0294483ffb9c528907fdd2025120f7fe83d2141effce5a42835ffac548507bff40a90a0f7f6b452141efe968a4283dfdacf48507bfb41e90a0f7f6b352141efed06a4283dfd9cd48507bfb59690a0f7f4b2d2141efe905a4283dfd9cb48507bfb31690a0f7f6b152141efe962a4283dfda0548507bfa40a90a0f7f67152141efecc2a4283dfd14548506bff5a680a0e7fea4d0141effd28a0283dffa4f405077ef50e80a0ffde51d0141f7fd02a0283dfda4340507fdd20280a0d7feb4ce141cffd499c2837ffad138507eff41e70a0efdea1ce141ffbca39c2837ffac538507eff38a70a0f7f690ce141ffed019c283fee90138506bff5a650a0e7fea4ca141bffd6794283bf7a8728507fbf28a50a0f7f690ca141ffed0194283ffd9c328507fdd20250a0ffde83c6141bfbd658c283ff79cb18507bef48a30a0ffde8146141ffbca28c283ff5a0318507feb38630a0ffd650c6141ff34808c283ff5ad118507fea5a230a0ffd6b3c6141ffad078c283ff5acd18507beb49a30a0ffd68346141fface68c283ff5acb18507fea59630a0ffd482c6141fface58c283ff598b18507feb58a30a0ffd4b146141efad228c283ff5a0518507fea40a30a0ffd67146141ffacc28c283ff594518507fea28a30a0ff924046141dff16aa00839fe29340107ffd41e8020fffa7350041eff525a0083ffe9cb40107ffd3168020efdaa1d0041ffb4a3a0083ffea0540107ffd38a8020fffa6150041fff4a2a0083ffea0340107dfd4068020ffda30d0041ffa461a0083bfe2d510106ffd5a22020f7fa93c4041fff50788083ffea0d10107ffd39a2020fffa72c4041fff4c588083bf6a8710107fed28e2020ffea5144041eff52188083dfca4310107ffd4062020ffda30c4041ffa461880839ffa9252486fff594a490effea2949218ffd65292437ffad5498867ff5aa9310cffcb552621effd49a4c439ffa93498877ff51e9310f7fe93d2621eff925a4c43fef2c949887bff4929310ffde41d2621fff480a4c439ffa8f49887bff5169310f7fe72d2621effd44a4c43dff9c9498873ff50e9310f7fe71d2621effc82a4c43dffa81498873ff5029310cffeb54e621bffd699cc43bffa93398873ff5267310f7fe924e621dffd409cc43ffe901398877ff5a6a290e7feb4d4521dff96 else 0x314051bf7564280a3ffea8650147fed50ca028effaa194051dfb543280a3ffe98650146ffd588a028dfeab114051fff542280a3bfea84501477fc508a028fffa8114051fff102280a3ffe9c450147ffd308a028fffa3114051fff501280a3ffca0250147ff9384a028fffa3094051ffb461280a33ffad5301473ff5266028eefea34c051fcfcc5980a3bffa87301477ef50e6028fefe61cc051fefca2980a33ff2d510146bff5a62028e7fea4c4051dffd43880a3bf7a8710147fbf28a2028ff6e5144051dff540880a3bfead5101477fc5aa2028dff8b5440519ff16a880a3bfea9310146ffd5a22028fff8b444051fff548880a3ffe251101477fd51e2028fffa83c4051dff546880a3ffea0d10147ffd39a2028ff7ab2c4051fef4c5880a3fee24910147ffd3922028fffa6244051fff543880a3ff6a87101477fd50e2028efdaa1c4051fff503880a3ffe9c710147ffd30e2028fffa51c4051ffb4a3880a3ff690710147ffd50a2028ffeaa144051fff502880a3ffe98510147ffd28a2028ffea5144051fef4a2880a3fda94510147ffd18a2028f7fa90c4051fff501880a3ffca0310147ff93862028fffa30c4051ffb461880a39ffa93081477ff50e1028efdea1c2051ffed01840a3ffd8c308147feb1861028f7f6b4c2051efed49840a37fdad108147ffb5221028f7f69442051bfed67840a3dfda4f08147ffb41e1028f7f69342051ffed06840a3ffd9cd08147bfb4961028ff7662c2051ffed43840a3ff5a8708147ffb40e1028fff671c2051ffecc3840a3ffd94708147feb28e1028fff6a142051efed22840a3ffda0508147ffa40a1028fff67142051ffecc2840a3ffd8c508147ff94021028fff26042051ffe440840a39ff2d54a1073fe5aa93a0f7fe8352741affd69a0e839ffa9341d073fe52683a0f7fe9450741effd25a0e83bf7a8741d07bff48a83a0ffba4050741cffd499cc837ffad139907bff4a27320fdfe83ce641effd259cc83bf7a8739907bff48a7320ffba404e641affd6920a839ffa92415073fe52482a0ddfeb390541bdfd6620a837f7ac6415077ef50c82a0dffeb110541bfdd6220a837fdac241506ffd58082a0ffba4010541affd699ca839ffa93395073fe52672a0f7fe944e541fbfd079ca83dffa4d395077ef50e72a0f7fe914e541ff74809ca839ffa9331507bff4a262a0dffeb3cc541effd2798a83fbfa0d31507f7f39a62a0f7fe92cc541dfbd4398a83dffa4531507fdd20262a0efdcb54a341ffbd6894683df7a5128d07fef59e51a0f7de93ca341ffbd0794683ff7acd28d07fef41a51a0ffde734a341ffbcc594683ff7ac528d07fee40a51a0ffdeb0ca341ff3480946835ffad3409073ff5268120e7fca4d0241effd28a0483dffa4f40907dff41e8120f7fe92d0241dfbd43a0483ff79474090) else (if i < 6 then 0x3ffe90140946fff5aa6128cffcb54c251cffd49984a39ff29330946fff5a26128f7fe944c251bffd67984a3bffa8f30947f7f51a6128eefea34c251fdfce6984a3dffa4930947fde4926128efdea1cc251fdfcc3984a3ff790730947bff48a6128effea04c251fff480984a37ffad518947bff5263128e7fea4c6251eff9498c4a37ffad118947bff4a23128dffeb3c6251dffd478c4a37ffacd189477ff51a3128f7fe9346251ffbd438c4a3bf7a8718947fef38e3128f7fe9146251dffd408c4a33ffad548547bfe4a290a8f7bc9252151dfbd43a42a39ffad5485463ff5aa90a8e7fcb552151eff968a42a39ffa8f48547bff41e90a8d7feb2d2151ef7964a42a3dff9c9485473ff50e90a8f7fe81d2151effce3a42a3dffa0548547bff18a90a8e7fea052151affd69a02a3bffa93405473fe52680a8f7fe9450151dffd47a02a3dffa4f40547bff49280a8ffbc9250151dffd43a02a3ff790740547ffb48680a8f7f690d0151fff480a02a3ffd2d540547ffb5a680a8f7f6b4d0151ffe969a02a3ffda9340547bfb52680a8fff4a4d0151efe949a02a3ffda5140547bfb4a280a8fff6b3d0151ffed47a02a3ffda4f40547bfb49e80a8fff683d0151ffed66a02a3fbd2cd40547ffb51a80a8fff69350151f7ed06a02a3ffd9cd40547ffb59680a8fff692d0151ffed64a02a3ffda8940547ffb49280a8f7f69250151ff6924a02a3ffd9c940547ffb31280a8fff6b1d0151ffed43a02a3ff5a87405477fb50e80a8efd6a1d0151ffed03a02a3ffd9c740547feb20e80a8fff6b150151ffe962a02a3ffda8540547ffa50a80a8fff69150151ffe922a02a3ffda0540547dfb40a80a8fff67150151ffeca2a02a3fdd94540547ffb58280a8fff6a050151ffe480a02a39ffa9338546fff5a270a8fdfe83ce151dffd439c2a3bf7a8738547fef20e70a8fdfe714e151efed219c2a3ffda0338547bfb52670a8dff6b44e151ffed489c2a3dfda5138547ffa4a270a8fdf683ce151ffed469c2a3dfda4d38547ffb41a70a8fdf6734e151feecc59c2a3ffda8938547bfb49270a8ffb4924e151ffecc49c2a3ffda8738547feb50e70a8fff681ce151ffecc39c2a3ff590738547ffb50a70a8f7f6914e151ffed029c2a3f7d9c538547ffb30a70a8fff6314e151ffe4809c2a39ffa9318546fff5a230a8f7fe9446151bffd678c2a3bffa8f18547bff49e30a8f7fe92c6151ffbd038c2a3ff79c718547fef28e30a8f7fe9146151ffbc628c2a3ffda0318547ffb38630a8effea046151dfbd6a8c2a33f7ad5185477ef52630a8ffdcb446151ffb9288c2a3bf7a8f18547fef41e30a8dfdeb2c6151ff39248c2a3ff79c918547bef48a30a8ffde5146151febca28c2a3ff5a0318547feb38630a8efdea046151ffb4808c2a3bfea92501477fd518a028fffa7 else 0xa7030fff680ce061edfd28980c3dbfa4f30187f7f41e6030f6fe92cc061ddfd43980c3fbfa0730187f7f38e6030fefe51cc061fdbca3980c3dbfa4530187f7f38a6030fefe514c061fdfc62980c3fbea0130187f7d3826030d7feb4ca061cffd49940c3bffa8f281877ff50e5030fefe614a0619ffd6a880c35ffad3101873ff5262030effea3c4061bdfd66880c3bffa8710187f7f30a2030effaa044061fdf4c0880c3bfead5101877fd5262030effaa3c4061eff527880c3ffea0f10187f7d59a2030fffa72c4061ff7124880c3ffe9c9101877fd50e2030fffa81c4061fff4e3880c3ffe94710187fed28e2030ffda41c4061fdf4c2880c3ffa945101873ff526a328effea3d4651ffbc83a8ca33ffad5499467fe5aa9328e7fea4d2651eff922a4ca31ff2d5499473ff51e9328f7fe7152651cffd40a4ca37ffad5399467ff5aa7328effea4ce651cffd499cca39ff29339947bff4927328ffde41ce651dffd409cca3ffe90139946bff5a6a228d7fcb4d4451cffd49a88a3bffa8d51147fdd202a228f7bea492451df7d49248a39efa9249147bde5249228efbea312451ef7d26248a3fef9cc49147bde4889228ffbc8112451ff7ce2248a39ffa93311477ff51e6228f7fe93cc451eff969a86a39ff29350d477ff51aa1a8f7fe9354351fff160a86a3bffa8150d47fee5a6a1a8f7dcb4d4351dfb949a86a3bf7a8d50d46fef592a1a8efdea254351ff3924a86a3bf728550d47fec582a1a8efdea054351ffb480a86a39ffad350d473fe5a6a1a8e7fe9354351dffce6a86a3bfe2c150d477ee5a6a1a8e7dcb4d4351dfbd66a86a3bf7a4d50d477ef39aa1a8efdeb254351dfbd24a86a3be724950d477ef312a1a8efdeb154351dfb962a86a3bf724550d477ee40aa1a8efde7154351dfbd60a86a3bf62c150d477ed202a1a8dffeb54c3519ffd6a986a3dffa9330d473ff52661a8dffeb3cc351dffd47986a3dffa4f30d47f7f41a61a8ffdea1cc351dfbd43986a3ff79c730d477ff50261a8d7fcb4d4251dffd49a84a39ffa93509477fe526a128e7fca4d4251dffd48a84a3bff29150946fff59ea128fdfcb3d4251dffd47a84a3bffa8d50947bff49aa128effea254251effd24a84a3fef249509477ff50ea128efdea1d4251ffbc83a84a3ffe2c1509477ff502a128fffa40542519ff96aa44a39ffa9348947bfe4a29128f7bc9252251dfbd43a44a39ffad548946bff5aa9128e7fcb5522518ff96aa44a3dff2d148947bff5229128e7fea3d2251cffd46a44a3dffa0d48947bff39a9128f7bcb252251effce4a44a3dff98948947bff50e9128e7fea1d2251effce3a44a3dff98748947bff50a9128e7fea052251bffd6aa04a33ff2d540947bff5268128e7fea4d0251eff949a04a39ff29340947bff4928128ffbc9250251fff560a04a))) else (if i < 10 then (if i < 8 then 0x1dffd43980e3fbf987301c77fd5026038fdfa704c071fbfd07940e3f7f9cd281c77ff50e5038fdfa704a0719ff96a880e3f7fa0f101c7eff39a2038effea1c4071dff540880e3f7e9c1101c77fd5aa2038eff8b544071dff549880e3ffe2d1101c7ffc4a22038fdfab3c4071fbf507880e3f7e9cd101c7ffd3162038ffb89244071fff4c4880e3bfea87101c7ffd40e2038fffa61c4071fff4a3880e3ff6947101c7fed20e2038f7fa90c4071ffb461880e39ffa93081c77ff5221038fdfe83c2071dffd43840e33ffad549d873ff52693b0effea452761ffed01a4ec35ffad149d873ff52293b0f7bcb252761cffd43a4ec3dffa0749d87bfb40693b0e7fea052761cffd49a4ac3bffa8f49587bfe48a92b0fff680d2561cffd499cac3dffa4939587fef20e72b0effea14e561effd229cac3ffe901395877df5249230e7bea492461df7d48248c3defa50491877df51c9230f7be9392461ff7d07248c3defa4a49187bde4949230ffbe7292461ef7922248c3feda0249187fdd4009230d7feb4ce461cffd499c8c3bffa9139187bff4a27230f5fe93ce461effd259c8c3bffa8539187bff48a7230fff680ce461fff5009c8c33ffad538d873ff52671b0dffeb44e361effd289c6c3f7fa0f38d87bff49671b0efdea1ce361dffd429c6c3dffa4538d87ffb40671b0effea04e361fff5009c6c39ffa9328d86fff5a251b0f7fe944a361bffd67946c3bffa8f28d87bff49e51b0f7fe92ca361dfbd43946c3ff7a0728d87fef38e51b0f7fe914a361dffd40946c3ffea0128d877ef5aa51b0ffdcb4ca361dfbd49946c3ff7ad128d87bef4a251b0ffdeb3ca361dfbd47946c3df7a4f28d87fef41e51b0ffdeb24a361ff3924946c3ff79c928d87fef58a51b0ffdcb14a361ffb922946c3bf7a8128d87fed40251b0ffda404a361cffd49a44c3bffa91489877ff51e9130f7bc9252261ffed01a44c39ffa93389877ff5167130f7fe92ce261effd249c4c3fef24938987ffd4027130fffa404e261fdfd28984c3dbfa513098777f51e6130fefe93cc261edfd27984c3fbfa0f30987f7f4966130f6fe92cc261fdf925984c3fbf9cb30987f7f4926130f6fe924c261fd7924984c3fbf9c93098777f50e6130fefe81cc261fdfce3984c3fbf94730987f6f28e6130fede41cc261fdfd22984c3dbfa4530987f7f4026130fefa804c261fdf480984c35ffad328986bfe5a65130effea4ca261dffd48944c3dffa4928987fde4925130ff7e51ca261febca3944c3ff790728987ffb4065130fffa404a261cffd498c4c37ffad118987bff4a23130dffeb3c6261dffd478c4c3dffa4f18986fff5963130f7fe92c6261ffbce38c4c3ff794718987f7f30a3130effea046261fff5008c4c33ffad5381873ff5267030effea44e061dffd439c0c3f7f9c738187f7f3 else (if i < 9 then 0x92491c7fdf5209238efbea412471ef7d28248e3def250491c7edf41c9238ffbea312471ef7d26248e3f6f9cc491c7bdf4949238ffbe6292471ff7d42248e39ffa93311c77ff5226238f7fe944c471fbfd07988e3dffa4b311c7bff48a6238f7fe9454371effd26a86e39ff2d350dc73ff4a2a1b8e7fe9354371cffd25a86e3bfb2c550dc73ff48aa1b8e7fea4d0371effd28a06e3bffa8d40dc7eff39a81b8f7fe92d0371effd22a06e39ffa9330dc6fff5a261b8f7fe944c371effd25986e3ff7a8730dc77ef50e61b8ffde81cc371effd22986e33ff2d528dc7bff4a251b8dffeb34a371effd26946e3f7f9cd28dc77ef50e51b8ffde81ca371ffbcc3946e3dffa4528dc77ef5aa51b8efdcb54a371dfbd49946e3ff7ad128dc7fee5a251b8f7de944a371ffb928946e3ff7acd28dc7eef39a51b8ffdeb24a371ff3924946e3ff798928dc7fef58a51b8ffdeb0ca371ffb480946e33ff2d5489c73ff5269138effea452271eff928a44e3f7fa0f489c7eff39a9138f7bc92522719ff96a984e3f3f9cd309c7bff4966138fefe62cc271effd24984e3fef249309c7ffd2026138f7fe9446271effd268c4e3f7f9cd189c7bff4963138efdea1c6271ffbca38c4e3bffa91485c7bfe4a290b8fdfe83d2171ef7924a42e3dff2d1485c73ff52290b8f5fe83d2171ef7964a42e39ffa87485c7bff40e90b8f7fe51d2171effc62a42e35ffad3405c77ff52680b8f7fe9450171fbfd07a02e3fef249405c77ff50e80b8e7fea4c6171bffd688c2e3dffa51185c7bff49630b8ffde81c6171ffbca38c2e3ff78c5185c7ffb40630b8efdea4c6171ffb9688c2e3ff7251185c7fce49230b8f7de9146171ffad018c2e3ff6901185c73fe5a6a038effcb454071cffd28a80e39ffa4d501c73ff496a038cffeb1d4071dffd03a80e3bff987501c77ff28ea038efde51d4071cffd22a80e3bff985501c77ff18aa038e7fe90d4071dffd01a80e3bff8c3501c77ef186a038cffeb5500719ff96aa00e35ffad3401c73ff5268038effea450071fbfd07a00e3bffa8d401c7eff39a8038effea1d0071dff540a00e3bfead5401c77fc5aa8038effaa4d0071fff548a00e3bfea91401c7efd59e8038fdfa83d0071fff546a00e3bfea8d401c7efd39a8038f7fa92d0071ff7124a00e3ffe989401c7ffd50e8038effaa1d0071fff503a00e3ffe987401c7ffd28e8038ffda51d0071ffb483a00e3ffea85401c7ffd30a8038fffa3150071fff501a00e3efea03401c7ffd1868038ffda30d0071bbfd689c0e3d7fa51381c7aff49a7038f5fe92ce071dbfd439c0e3f7fa07381c7eff30e7038fdfe51ce071fbbca39c0e3d7fa45381c7eff30a7038fdfe314e071ebfd219c0e3f7fa03381c7eff1867038fdde30ce071fbf5009c0e39ffa93301c6eff59e6038fdfe83cc07 else 0xcffcb552781effd49a4f039ffa9349e07bfe52693c0ffbcb252781effd24a4f03ffe90149e06bff5a6a240d7fcb4d4481cffd49a8903bffa8f512077ff51aa240fff660d4481ff7d4924903defa92492077df5249240e7bea492481ef794924903fefa8e49207fdf49c9240f7be9392481ff7d4624903faf28c49207fdf4989240f7be9312481ff794224903def24449207fde2889240f7fea4ce481cffd499c903fbf28d392073ff5266240dffeb5522819ff96aa4503dffa9348a073ff5269140f7fca4d2281effd27a4503fbf28d48a07bff49a9140f7fe92d2281eff925a4503fef2c948a07bff4929140ffbc9252281ef7924a4503ff790748a07ffa5869140fffa4052281dffd49945039ff29328a07fde4925140effea3d4081fdf966a8103bffa8d50207f7e51aa040eefca354081f7fd06a8103bffa8b50206fff58ea040effea1d4081dffd42a8103bff28550207ffb306a040e7feb4d40818ffd69a81039ff2d3502073ff4a2a040eefcb354081dffce6a81033ffac7502077fe58aa040e7fe90d4081cffd49a0103dffa43402079ff5a68040f3fea4d0081f7fd47a0103effa8d40207d7e51a8040fbfe7350081f7fd45a0103effa8740207dfe58a8040fbfea150081f7f942a0103cffa4340207dfb3068040fbfe30d0081f7ec61a0103ef78c340207dfc5a68040fbfaa4d0081f7f149a0103efeacf40207dfd49e8040fbfab2d0081f7f165a0103efea4b40207dfc4968040fbfab250081f7f544a0103efea4940207ddc4928040fbfa7250081f7f4c4a0103efeac540207dfc58a8040fbfa9150081f7f122a0103efe14540207dfd5868040fbfa90d0081f7e4c1a0103efe8c340207ded1868040fbd230d0081cffd4984103bffa8708207ffd4021040fbfa8042081cff949a92e39ff251525c77de592a4b8e7fe9254971dfbc83a92e3bfb2c5525c77fd202a4b8d7fcb4d4871dff949a90e3dffa49521c7fef20ea438fffa4054871dff969a90e39ff2d3521c67ff59aa438eefcb354871dffd24a90e33ffad54a1c67fe5aa9438e7fea4d2871dffd46a50e39ffad54a1c73fe5aa9438f7fea452871cffd46a50e3def2c94a1c7bff50a9438fdfca4d0771fbfd24a0ee3d7fa4941dc7efd20283b8f7fe9454671effd24a8ce3ff7907519c7ffd202a338cffcb552671cffd49a4ce3bffa91499c7eff41e9338ddfeb44e671dbfd489cce3f7fa51399c7aff4a27338fdfe924e671ebfd249cce3f77907399c7aff48a7338fdfa404e671ffbc83a8ae33ff2d5495c73ff52692b8f7fc9452571fbfce6a4ae39ffad5495c73fe5aa92b8f7fcb452571ebfd07a4ae39ffa8d495c7bff41a92b8f5fe7352571ef7964a4ae33ff2d5315c7e7f39a62b8f7fe924c571ffbc8398ae3dffa45315c7ffd20262b8f7bea492471df7d49248e39efa)) else (if i < 12 then (if i < 11 then 0x131c098d04c60261492f5897124b2b255c12a2c95064a7b2539929ac94c64a5b25299287c942e49c124dc926c49352494c24a2123d891dc489824289201c8ffe47f723f791f9c8fbe47d723e791e408f10478023b491d848dba469b234991a2c8ca6461a2309118288c0445b322bd115c88a2c450e22109106487784328219010c6085b442d2216510b08857441c320c39037c81ae40cf20471016880a4404a2021100187eb23f511f828faa87ccc3e321ee08f6147afa3d361e790f2a477b23bb11d988ec0875f43af21d750eb8874b43a521d018e7ec73e639eb1cf18e61472fa39751cb68e450721838b01bff0de806f3037901bc40de006ef037701bb40dd806e2c370e1b830dbf86dec36ee1b730db786d1036801b260d9106c7835e31ace0d59869c634831a3d8d0a0684033d819e80cf206780336319ad8cc4c661632c219398c9ac642031bd18da8c6246302317918768c164601a300517fe8bf145f7a2f0917610bae85cfe2e2616f50b7885bb42d6816890b42859722cb1163d0b060566e2b2f154d8a8485258292414720a2145098281013c589c544e1a2705134709a184bd825a012cc096404b10258012bc095c04ad024e3124b09238488a243d121a88fac46e422f31155888ac43da2131105a080683e501f200f51879143b7a1db50eac0734039901cc00e5c0710038701b930dc586bc0336e18c00c19060a82f4c179e0b9485a602d2016880a9b054b8295214a109dd84ca4264212aa095104a6825241159085e042d02158104107e503f081e1e0f07074e836c418f80c74063602f4c14d609b6048d81f6c0ec4075a0363016340880033a019900b6005a00288011f808dc045e0227010f8085c03c601ad00b2804a801b600a400006fbea492476cf7d49248ed9ffa93485dbbff4a290bb77fe92d2176ff7964a42eddffa49485dbfde49290bb77bc9252176ffbc83a42eddffa45485dbffd20290bb67feb552176ef7964a42ed9ffa85485db3ff48aa03b67fe90d4076effd28880eddffa4b101db7ff50e203b77fe90c4076dff540880edffea01101db7fd5aa203b6ffaa4c4076fff528880edffea4b101dbffd492203b7fb89244076dff543880edffe947101dbfed28e203b7fda41c4076fff521880eddfea43101dbffd186203b7fda30c4076effd28840eddffa4b081db7ff50e103b7fde51c2076effd22840edffea01081dbffd102103b76fc5152664affd62a42c9dfea4b40193fed186803277fa93c4064ffb4a3880c9dfea4310193fed18620327fbcb254981effd24a9303ffe9015260777e59aa4c0efbcb254981cffd24a93039ff245526077fd202a4c0e7feb3d4981cffd64a93039ef2c9526073ff58aa4c0e7fcb154981cff8a2a93039ffa9252606fff59ca4c0dffeb1149818ffd62293039ff14452606fff5aa93c else 0x9dea4ebf2750d3a2a9d0d4e6ba728538ae9c4f4e112706938249c0a4e0126edd36fc9b404d9c26cc135dc9ae64d6f26b59359c9ac64d5f26ad9355c9aa64d4f26a59351c9a864d152688933ae99994cc8a658532b299204c712636931a498ca4c61261e5306098284c1026061302097b44b7425add2d5e96a74b2ba58712c2895c64aa9a552d29a894614a2ca514527ee93ef49f3a4d2125bc927b4939a47dd230a917d4883a418520b28fc447de23e091e728f314773a3ab11c548e2246c6236111a6a8d07467fa332919848c89460222f1117788bb445d622e9117388b604571a2a8914b08a50450a2268512b889544480a2305104487ad439ba1cbd0d6e86af43192171d0ac8855c42aa213a908d6846341e7a0d89058e82bf411320879035e81a740a320320fff27ff13ff49ff84ffb27f9d3fb01fd60fe347ec73f5f9f998fc467de63eca9f504fa027c733df69eaa0f5407a3d3cf09e690f33879503ca41e424f20278983c0c9de1cecda761f3ad41d260e920744e3a231cdd4e6da7365396e9cb54e59a72c539361c990e4b8725439261c910e478723439161c890e438721439061c810e3f871f438f61c790e3b871d438e61c710e37871b438d61c690e338719438c61c610e2f8717438b61c590e2b8715438a61c510e278713438961c490e238711438861c410e1f870f438761c390e1b870d438661c310e17870b438561c290e0fe704337f19bf6cdfa66fcb37b59bd8cdeb66f1337671bb18dd7c6eb637571ba98dd3c6e9637471ba18dcfc6e7637371b498da3c6d1636871b418d9fc6cf636771b398d9bc6cd636289b124d8826c3936189b0a4d8426c1936089b024d8026bf935f89afa4d7c26bd935e89af24d7826bb935d89aea4d5f06af035741ab80d5b06a8e34919a46cd226688633a799a34cd0a662a326299194c60662fb317998bacc5c66276313718998c4bc6256312718918c47c6236311718740c39061c030dc186c0c35061a030cc18640c310618030bc185c0c2d0616030ac18540c290614030859840cc1f660c9303498184c0b26051302498104c07260312ff017f60bfa05fc82fe017ee0bf605fa82fd017d60bdfe5ef72f7797a9cbcbe5e062eff177d8bb165d832ebd974c0ba505d202e8c17440ba105c712e3497028b8045b682d8616ab4b54a5a9d2d1e967bcb3ce599d2cca96634b30a597d2cba96470b12c588e2c1295f74afaa57872b8895c24ad7256b12b5495a84ad32564f2b23957a8abc455a82aac15540aa9055402a9c154c0aa5054f32a3f95080a83054102a0415000a7f053d2298694c14a4b2522328b8945a4a1a250c92860942649fc24f80278913c289e044efa277913ba89dc44eda276913b289c3c4e162707138189bfc4df626f7137989bbc4dd626c1135209a804d38266f13358999c4c80263c) else (if i < 13 then 0x58a22bb515548aa6455122a7915348a964549229c114d88a6845322298114b88a40c51b62795137d89ac44d12267913148960c492a23d911e488b0443e621e3109088444420220f1101187c2c3ce21d9b0e37865b4317617f70b77858c42c4213b7097784b7c23a211c108d88468423220f09077c83ba41db20ec9075c8381c1bee0d6506aa8338c17a60b1f0587827d413ca09d504e2826d4134a099504c2823bc11be07d903b781d7c0e9e06b303028139409aa0469022c8112408720429020c81024063e030f017f80bbc05be02cf01308094404820231011080844040201f100d38020c00e60062fffc7ffa3fec9fe36ff137f85bfc0dfdf6fef37f4dbf93dfc8efe3f7f1bbf8bdfc4efe1f7f0bbf83dfc0efdd07ee43f521fa80fce97e35bf051f818fc047dfe3efd1f7d8fbe47dee3ef51f798fb907dc43ee01f64afb1d7d713eaadf444f9d77ce7be71df37ef9b77c9d3e329f184f8ba7c593e2a9f050f7d57be6bdd7dee4cf6b97b323d875eb9ef5877abfbd5ddeadef5677a8e3d451e974f4b27a273cee5e762f35b796f3cb59e4e6f21d78d93c669e324f18a78c13c5e9e28cf0cd7835bc06ddfcaef3477753bb89db7aedb576bfbb5ddda38ecd2763fbb0d1d7e8ebec75f23abedd580ea877515ba715d27ee8ad73af39ca5cdcae6dd7337b999dcc0ee5ff72e3396f9cadee443721db8fa5c5a0e274713638991c4b8e1ec70c3b84e9c19ee0c7705fb8131bf8edfbf6f7e37a25bc10de006e97b73a9b8aedc4f6dcf36af1b4fada756cf9366f9b310d9196c6c36299b13cd8396c18b5f49af94d77a6ba435d01ae70d6de6b4cb58edac66d5ee6af335685aab4d5206a8c352f5a88ad4106a0434e1da47ed2376917b489da43ed1c168afb4391a15ed0a7683033f719e24ceaa675133a699c38cdc866c232ff197c6cb8965693260192a4c8236352b19ed8ce6c66b6310b18658c22c5c962ce315b589d0c4976235b1059881cc40661ff30da58628c2ba613e308c98454c222610d3075582e0c12f6056b0295813abff25fbcaf8b57c4abd765eb72f5097a74bd325e70af36579a2bc905e1baef2d7620bab15d3b2e92d73fcb9705bf9adedd6ed0b72e5b782d9c56cd2b6205ad92d54d6a20b4d05a24acec564b0b21358da2c6016106b01657ebabdf95eecaf3c57742ba695ce8ae2456e1ab6ed5a66ace9563c2afd556eeab42556eaab55553eaa2d54dcaa64d5278a90a547b2a3755192a87e541a29f054ef0a77053b429cb14df4a69d5311a96354b0aa57d52baa938549b2a4d15264a93054972a4b15254a92854932a4515211a906d4826a40b5201a8ddd46dea3675175289b543b6a1d350c02840d40fe9fed4ff2a7f753faa9fcd4fc1a7d9d3ebe9f574fa7a7d1d3e7e9f374f97a7b953dba9eae4f5327a793d2c9e8e4f43279f93c42 else 0x763bbadddae6ed297603bafddd7ceebd775e3baeddd74eeb977540ba9c5d40ee9f774f3ba75dd38ee9b774d3ba65dd30ee9777407b9ffdcfdee7df73e7b9be5cc66e35f716db81f5be66df236ea8b7425b9f2dbcb6dddb6c75b61ad9e96caab6315b0bad84d6c1eb5f4daeced7576afab51bda63ed1c768dbb426da116d07b680bb401d9feeceb36751b38459c02cd796637b2f8597a2cbc16595b29559376c91763e5b1bed8cdec65f6327b18fd8a92c5396237b0d8d86a6c2bf60f4b0765818ac0635ffbafd9d7eaebf475f22af74d7b86bd755eb2af55577cebabd5d56ae7cd73c6b95b5ca5ae2f5715ab89d5c46ade256e36b6915b40ad8dd6a4ab51559eeac92d62d2b04357ccabc2d5df6adeb569bab2955812ab335520aa55d5156a8215408a9e354df2a6e95324a95d54acaa5555243a91dd462aa305517aa8b9543e6a0bf4fc5a7ae53c569db14e8da709d382e9b894d8da68a53326991f4c2fa5c4d2e0695b14a47a4fe526e69363497ca4815227290554822a3dfd1e768e2746ada30d5184a8c1545a8a2d05140a8981449ea1fc50f1e87054348a165d0b0e85774283a128d0816830d414ea06b501167f953f4c9f6ecf8c67bff3de59ed74f4f67a6b3cfb9e634f18278113be19dc64ec9275393a369cffce67272b939089c4d4e186705537cf9b994dcaa6ddd36b59b384d7066a3935149a864d23e690f347f9a0f4ceea66bb33209955cc9d6640331cb98cacc55e61ff30f79844cc0ae5f752f6497994bbae5dc72edb9769cbab65d4b2e9d97064b62e5b072ce0966c4b34259912cc0965c4b2c259512ca0964c4b24259112c80963c4b1c258d12c6095da4aeb257492b9c95aacad36568b2b3d959acacb6564b2b1d95544aa8255312a9095444aa0254f12a7095344a98254b12a5095244a90254712a3095144a88254312a1095044a80253f129ab94d1ca66e53272946949f4a4da525d292694774a39a51bd28d694514a26a5019280493fe49e024e7d26fc937a49bb24dc926dc936a49b324d8926bc935a49a324d09267c933a499b24c69262c9312498724c29260c92ebc94964a3b24f89278493a249c124d89268490fa4815240291fd48f0e471922e5916ec8b56459b22c5915ec8ad6455b22a5914ec8a56451b223f90f54837641ab20cd9062c82f6416b20ad9052c8276412b208d9042c81f6407720339015c808e403720139005c800e3f8f1f938fc5c7e0e3e191f048f7e47bd23dd91eb38f35477da3bdd1dac8eb1474c23a511cbc8e5a472b239491c9c8e3b471ba38cd1c5e8e2b46fb237c91bdc8dea46e0636f31b718db4c6bce35d71a8e8d434680e338319b98cd8c65f2327118b48c564612e2fb917d48be645f122f7917b48bd645e922f3916df8b4845a222d0116788b38459a22cc116588b28459222c8116388b184)))) else (if i < 21 then (if i < 17 then (if i < 15 then 0x3244052c581a602c46215f062f1f1101c014dc25415c043502be14017ffddf5e6edad606cd6cd82882840210209e05e305c380038c06c4519bdc76a18c161a906bfffeefaf37eddfdad81333306b66c0a20a006ae13008408278178c17126d9be6f0db36cdb9dbbfbb769696b46c36726c37e1b3319b033b200350318042040ca0bc0af87000008279924803831f8f9848827b84b808b5857c31dc8f59cebf496a92f557ce6edfffd7a987f33fe79f033fcf302592c6306506306201880c857a8602824b854452eb9efbadec0dedf7f6d6c66ce0c48c43281402a14321843e30d2e703ce066270f300c8620650b58634292f17e97e77d33acc2f3d9d39d76eeca4d56a7b5f026c333ec0c7f36306a00c88cb818b5865064c38f60671081b036ecc1443294302be10000519ce9800ce4c1e667260413c3114302a21178576e17bbaebbbbb555dbfaeaabaeabbd6bddf6ed68000061861861801c84620a61ba1a8c170cbbb80abddebbbd6eebbbaedc001daaed56ff476abbeab6bf4530c30c030c0ca0c60310530c10af50c876db6db6db6db6db6eddbb76ed6b5ad6b6db6db6ddaccfccd99980c7c0fc0bc061001a5ee381a30204d01c0780500697680405401a04d046971c0d02680e03c02000000000038c020410258196220a12206406ac4e1050080a00f008e44d41a8100ca0c044881090c98190594117360720401883041e2727c9c4800487e33091e0990503c05f0af86dbc9ede2f6e27b6bedb2bed88f6c37b5f7da9f6d4db6a5db526da8f6d22f6907b47bda00ecee76763b375d995ecb1b64d7b263d92dec80b639fb1c7d89fec3af616bb061d82cec07f5f4baf60d7716ba775d2bae5ed716eb8975be5adb8d6d86b6a35b41ad2cd664eb1ab5813abaad5b36ad7b5653aac4d528ea927539ba96dd4b2ea57752aba94dd4a2ea4f7513fa86ed40ae9c1b4dfda69ed34b699034b4da58ed2a4695034a71a530d247e903f477da3b6d1d768db345b5a275d087682a740bda028cf8367bfb3bf19dc2cedd676cb3b559da2ceace7367392b9c8dce42e6fdb373b9b0bcd81e6a4334879a3bcd19e68af33a999ccccc3665fb32ed9940cc9c663572fe1978fcbc3e5d3f2e8f9711cb37e599f2c1195c1cadce55772aab954dcaa2e54f72a6b952dca4c65103278d93bec99964af72503921dc8e0645db22dd90cfc84c640df1ffb8ff5c7d263e731e718f30c779638731b398d0cc64c630a316ed8aeec5736288712b58952c4a562257111b8743c378619b70b5585a2c280613e309e18476c1f5e0f8f05e78190c037e002eff897f89bf9c5fab2fc4f7dc4bea7df38af8fb7c1dbe0adf036f80b7be3bde0dee72f7297b8cbd58deaa6f4317a10bcc35e5faf2ed796ebcb35e57af17f78b7bc57de29ef13f7897bc47de21ef0ff7877bc37ddf8aef537 else (if i < 16 then 0x10a0406340e16a1930c4eb5e09f20c10023508000045609e10027206001e797efe0f8e0312120e72a1300ca0606216b20c1930e4d5c13e4182004681001769c0302888d418b76db2fc26a01846814611726e0181442f20c0000070a64910304920469060c90e98334e7c36827c0584688c41401d67b2613e02c234463080052c13c14c1440df939dbd11a90605104f01c8576bf7cbdb70ddaffdbd6d930ccccfe04f83ac0210201886e857c87440001cfc038f890f1a01918b84303a860400624301e27e408991c3700c0194082004e43121418f87f9ff3f1fc3c1ce712833403831231d097095057030bc0800c489002254b04f0a811a0310224826db0800ee0a614c0650b0750500b50363b507707505003045924403324c049243a8283b8b5853020477c11e14030c12c110080be1890a000013b9201e0fb002458064141ac2be14001fcbcf9c038164920401a60980460d0a00af86f4eda804e0104d23184000000000000000f94f0efc381802600d304b06c82863437976ca0138048c420a1001d2fc09b009414409080000e4fd026c021025054217a7060f92490032a0108128102be1407798216012124304c0230785785902967482591882682f821079c31d80ac848c4280d709505065420271aa0b4080650627399b36605f3ccccc7e733330209e09a0960a34144670c5480039c8092480cfa0404b0380af8409dc3c44001f1e07ecc24780581e4145ac2be183cf7e3884ff7fce4f10007c7f6039b3e09709607004e0116b70306b0af89000838f1100e0f99848b84b038b5857c2894910092900328e0a0193044b892491000f40fa621cc1700846215f0a01c5806695341350523316b830f3e2e14f1003902380450c6070ca0a885000000084401c303ef309104f70116b0af85000f8f17e7f488010731b84b03a82c0238185e054438002c13e69200e0c03ff304f70970370116b0af861f85df17bbc015d680000aeff5a145dddb9ff43fa15a1457686a018f0580340205006205b81ac49f3efddefeab76ddb6f3fdb36d9adffdb0e48318068040502310bc7030a8891703c7be2200140e24dc240e54143502be140021e201c03f7cc24413dc25c044f02be18001e31b1b8c6d259609a462a181a9081c2f9f85e4e0104370960770350c0ca0a88600002ddcc7f599ab27fad525aa0cfcf97036ff9852d556cf60ccfd9f03d83240d60183282f02a00c43502be240021e220e01fbe612209ee12e022d615f0c00ff97bfddf6bfb6b6e7ed9b6d9b6d82802681ac18c034021188b5854448c7b06161d8306c0c7e61340a2e24e2015f0a00781983669cc618cc1460c48c42f21000000088fc4539e76539e766f539e7376ea73d9cdbbeeee4092588333ece716d008194192178c161d30cfcbc0b27dbb80c65b1b05070880470116b2318600000f else 0xf049fa776fae79f436f7b136fe12205408641f21c16626b0eefebcdb249135903303e018577febe6c9d04d405e40cc0f8061800000000000000000024b78b10dbcdb777db7fb6c2442289d38041ac5ae18000000000000000001b93723e8102f10c41e21097c9060ad0548300002f62ec16a8103290c41e0140001a4e1f0824300e907884000000004860ee0a014c06d3bc208150c2141813c1444e0000720c06a16506f5cf8d80d18448328303c42ada39d1ff0caa040ad50e10e07806df348403c410000000000000013b0086b81481802ef2c834412c020ec09a0a000000def97241a20960107004d85003fa74c0a414c0c80ae1003dc9602a20960105004d052dd209683409a064086feb08cd03f00848c20000000000000013cf360b0d704d830000740f02001e7721f0a0079036a0406340e19c1750a6de6dd04b03830c1800016eb8084d01ec19e3681c3902560c000000b3e76818b8084d189423a6d44681c50e0c018feb6db6e824c248101061000ded7bbef96d7efe7fbb79b69dffdb60a308624aa0740e1ae13213c1751200f377d6031309a0770109a856eeb25bdda9bf9b79b6f0310e40430dc0b185000079dac52050c8960c0000000057f9ef76fbe5cdf9bb35b16ffb67f6cd840037e82e8181850384e058b05c4bcf302910d86d41bd3fe2ddbbe6b7a058d98d837821b8086a857118c300003c636c0dc0588c60dc435c26982c0c000000bec881c1c426a0d17ff7b96f6a6db6e6db6db640e40812c0621b81630c00bade7412a0a052c0f085e76fc269415c0413407215d34c2581c268144105c3741454300cae728d9b66cde61bb412a1828708f966a0ae060a30601ee2c0a5419c0810e10f35419c0426814c113f960a540e624213085f5bf7bb7836b7f75b5bff33660ee462412212123062162a19103f40ea1d041d5b7b6d9b7f6c613408741340ea1d0be7fe81d41a0800000000efdc9f7ff68464854c2380414e0c42461c01d3bcb41103b107848c2000000003a762de09a0ec26a41e1200a000000ce96f08220413531082205003592f704da0405004b032051ef73bf737cdf0eaa23b2d92c12f8494182b68284d6197e7b9b029607a0313c02285000000000000000069dea07d0688dc136100000000000000096fe04fe013010ae04d05002b08205a04c0300002d7b988d30082681a82582b27b1350912693100448c1341401e00df3f76f7f581880f984503b03f00814c3a8ef77d89a81883089e134c2807a4e4ce029831053080840027b1a0480401a05504000000fa73d3014c0d10389e040428013d8d0240200d02a8200277e416081281201211ee94d282c02040118c2002393bdb27e018312310ca8449fd3a60084140a20a108004960a20a10400001ddf9f24f00c047062a13a1040e1a81510c1e77017df807b012ca)) else (if i < 19 then (if i < 18 then 0xd00d580c112ed58085706ec1b799aff027984580b80826c28000003a677bf027b8083b187826c28000127d02b58081806502167813dc042b81341000000000000000000000000176f37deffdfbfefb6eff7bffe3b6bfb7e7ff5af7ee7c0b40ac47a06540a8043903383582302e02ba30000000000000000000006203e1c9c7bc7240a074028e60721c50a0000000000000000000000000000000000000000007db9ff07077c4f52f43874bd02e02d03106b43146b860000000025df813cc042b813611f7f6f775febf39faebe7f9effdbfbfef7dfbcfffbafee7edbef5b7d81590990091382a07205b8570359891884580000cf40ce3b08f91606064580c6c4835c2b6117f5fb7dbddafafdff3ce7bbedbf7fbee6b7b79f6dfdd6dfde81f0085e12386d06605718918844bc1b33deff73f4ff73f43d6764d8f7662e80626246204630a00d270bc209068c201681e014e77bfef7dbfefed7d7e39fafafce7efeedbfff7bedf7f36f5feeb6ff7c0215a1058624e81ba14c0d2624621145ebee64862611c020b409b0afbce76fb7ef6afebf3f9d7d7e79dff7bedbfdfefef37fff6dd6fcfed82890df0087206f85b85701f98918845000000001e7dd7f813d0c4468c24c041361800000000000000000177f3db039135111303e0185000000000000000000000000000000000000270278570268180006dbff0601d304d9a76db7ec135060e1010508000000000000005ffdd30d708423723184000000000000000024fa054b010300dd04697b748358082a08d026828000093ed80b8082689e02127d02a5808180650234bdba41ac0415046813414000019c489009162009c8307485b418000093edb010a604d11a040000000000189cf38fc3ce07c804a05402a204920621710c00bfe276c0a88a280406427a140067e791dc9c903e7803031a014265112740a6867cf6eb22711a806a0102a85395db7ed9b40206810405508000046724902480060661d21650677cb988d122018918c200197b300c46e15e05408000000000077ab643110607830d04d0518be4e1e1387872024248343380fc2da14009edcbe0a4085604a048620f00c66f520c0346240a8080073fa9a8706b0b582a4237cbf7b8b7086212a076048620f10c00d2f7368616041d20f10800000000976698083c02689e02003af9e8c8c606a4384e41e214009f190e03c05403f7659b105103e0181a840000000000001682a048833818423bcb0f1c5001924c87033859420efde5b04301a90305416b85000000000039c0424609d7416fd6df66ddedfd937fe12209e02ec10c020a80d721d10003de935befdf09b771899b36086c2520dc0215a26b0dcb09e380848c181f8f223ec3b9fc17fe12209e034c11206c02086185100024bcfeb879b7731e99b37c1215ac1a2d626b0a00009a12261 else 0x82d0021a78161650e0038c9e430917f14000431203d0100d0af0b2060077040750c41cc0cdda803a18721a0a8080074bd857e80c86825c22e0b81d07a0a6830e211820c3e390010c40c6c4017c2c8140071992048bf8a1e000431206d010440af0b206005cbd0703a2021680f108e7f882c0ec10014c32a43c12c0c0170703a20a14d061c70f160247e280043190100f0c60b285e287b0c604b05f830000000000e40d1050a80a6830e30c4201f140021890401905785902f508ec2bc0c81e20da8470ca30303207804004e9ba0404b0e6831c5c9248ff0011906202c15e14d088d70caa0404b46904003d4e7f60f40eb02c143087f09b02c15e183060f10f1272103893f000669a0c40c5c4017c2ca140e2260449f0024d062a0218c1650807111009f001c93418a0505785942000a087147821c023b38406802f86d42000b83809e4384301259c2102834036a10e018d9b02c9942da89c18873418a081ce108049671005f0da830000023199f14c6d1a6f4060c43420c53f84038821c0143b68086802f86d42000c5c183d9f60e08c0b0b38938820b05706d42f71196cc1596d186c12e0c51a60dde179fd6e1b609bada30db84850860c1882fc2801707831f62c361c10c5859c384150582c836a140028066c610e36763b418a0b06d41801c0c98c0a3265944e0c43220c07c6306ccee2861a60174168310b284753c9ff36fbeddbb4f0cfdb1637e6e12150e07a021641430630e00000001d30a02c1cd06307d21b01605f8318300e986c0594420c60dd5e58da1d80b057c18c2000480493b90027242bc0c608f323f86d20dc18c1f4c2c0583920c60dd273d61ba02c0bf06309e99c6d602ce0615f063083a2b683b0620e7064f00e9d0025812fb9306368082fc18857c2a40149001252419bce0c18ca1806215f08ff8fc00a017ddf07d5eef0fe7adebbb836b76e3f00000576815ad680d7043d010e6b120af0da03188000e24839458222603706215f06609204a050a440c06215e07d11b0160e483183007467b0d30165118318400e931602c17f0630600900488609453b280a80310af831e0889d2614673098602c15f062151083c08923a43be384922305410301882f85342ab1f17af175c6eaa35d551bfd51f00000005c3ddddd7ed0019e151a021b41a617e0630fd9b22e8085b83ac188224012401294287770e60750310af8351e005dda05dd06faa835abba0ff6fb4780000a01d755da00aff03d010a80b203186004f66cc8c4c201420c01dbf8000ee0aaa0aaaa82a800000000aaa0aaa00120da0620d708000039ecc9033018c92496336042042781690800000024dfd04fb0170104d16b05000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) else (if i < 20 then 0xa84503450e1e828c19696e81940c4d432a139aa1b0383a83bc19868a491019608c2f029a08010b4e0102c05a030a4924003c08205a0a60349ec348c412c20817c110407032020250010620820320b20308dc408500304c0203485902000f81113f0e0f60047084703700a3a057c33a6a74081780f04620803c44f8705808e80460106b0af85101933e10778011c26bc0dc240d215e0c039e13e106c047304c0221ab06857831648c41a41600c05e38421d80c12c1c0be15f0800eb00bb0882fc180de2290c3a0c12c0c06e1a215e0a0078e0d8a59d819c13c1d414179085505118810e584028a042040bc0a604ca0108128280c1a40420bf0206e023582410007c1302bc0dd353a040ca0782310401e444f8730011d008c028e815f0be9cd804e010582318400001ed923105805f83ca0108128280c08e01e00611cc0e00815f08084078e284c08c1df04f0702f857c203e100e238fc0f026c11c009c03c24c1c15f0c0000007c691a0f03541d22002641040c07686215e0c00000000000000000069f32221ae8620f808e7f98141dc1000000001e3a28a201c18222c588d00980e83d057420000143194500e0c0a162c46b0042bc2ba0ca18ca280386050b1623580215e15d063838c65145001e142cb08d60080b05785742003cf2ef2fe60da0ae0a883286328a28038302c5a2360085785741974c319451403898c0a04681b8578574181c634a28a01c78304a0b178020360f415d0800000000faec86b83d218a0e8237834c0800000000000001aead02c44211c0f80800b3fcc0c17e08000000000001f891218949a041006215f0696c3340b10c80cee22483125e808d48200c42be13a4da0b057c0b41a4d60ba8bf0401d1a0b288c0b4196340817810e0697b9d043818162194200240f4050ca08000000009bcd41920e818a18821ce426830c1ec0cf2db0c70e40678300002eb3ec2bd0582ba0c000000000000000000000000011da3f50c50760581e82e014013b4ca0ec0b03d05c02746b66061a60770600b37e60c0bf04005d36048160b983e8b6cc083760ee0c00000001e58db6c269862151068beecdb43b0310c683000000003d397f0af816b03135431857cc867b65f9eee0b67f0c7fe60a8075235207d12d0113f4318873fd98405441000013eee5e80c008548154217ab46906902a03002fdac826a0042841381023982305e03418e80867a8685c0280045f03c13818e70970883150f0b8853c5d9b360833296a270030621cd0800000766cf8920902fc18869c18000161c9e7d8b0e418fd8310da7108014160bf0ae863c5d9b054668144e0060c433e10e3d986d848cd002fc1885fc18003fca461e0161886d20b680869850c28e3ecd98708362500282d0621b5080003b7ccf152b0069e80c00c18860c28fe0f671d997c7e4ac0073062 else 0x44d905c040ca04c04738cbf078fe01bc60c10a6506a040b285078c777f9e3f1f002800fecca0c701340dc094268101e02ca20387c3041008a81140c3282ca100000e6c8e078cf826ca0a70171270e0af8533f0472e1cff6a0a0bc826b6ddb0d0711e01833e71df7ccfd36653dbfcb7a7f672ddb833cfecbe6db3f6b5ad93665b6f6ed9a0d9ece366f0316003020a16805f2310af88cb05c0a5d9112181801322c014d065bcdb73788623337e1b9b6c6f813012dc49c3982c8c6187dde365eee17ff7742bd7f42bd7aa03000771b2eddddfaf6815daea91d0e20d00b20040dc0c10bca0a88ddbc16817e097ddbdffdb6df6feb13f6d66b77dbbdb6ff6ed6e37b6fdb818781f8103a83291885e05410544b664cfdb6ccb7bdbfcb7b77f672ddbb619e7f647ce3e921adb67ed6b5b2f986cf6706de062c00604142d00be46215f11b9b8183c41000037db2db60b4c0fc03060000cdb6dec165c020b507bef05ae0182ddcc2c00f1046af6cd9b3183b6e36db083099508a0a840df99ccc11ff8b4034c11e5825b05c10c97911118301058029a080000000079f1c52387fe006195c12287c1d4141790ce9779cd11402c02085f842b09500289000102c82bc0c9f3303011405f831d7cc21ec0a83420a10000001ee89bc05e09e14d061e9248130092400040820a6833aa5d98305304141a780e038a6d1842128c06bc25414195080000058a27ec4781c0fb10b80302f013d4140c41942be1836f1c7181b0566fc2d02c040815f083b62f8b7dec5bdbcc33e78ddc3490b35ad6cb2ddc5afd6b2506cf9e06dfc0a161c2d02c006214415f0e0018fc73e79e07f6116e6f826881c3282f020c1dc2be1c03cbdc081d6080000b73ed81c940c10426b0800005f6d6a060d4135831070007e048d03282857c2043986c3f366c03bd0328105e4200c7c7f18787071fb058b1bc03060ba070ca0bc0a80af875d1fede1924621901444330a5d6e8182e428a0fcfb03d0341068a492032c02f029a08fb13c1c7021241980b02fa065116070da852cef1fae69d72777527ffad067f3fcbc61bff3fe7c2975d56db3ec0b240b06e86d06405e68810385c818872059057c5bb4da13503027c1b9be74a0604f30e0c4844f9281813c2d60d3e9ba0604f40783f306064719c036363409e178a2015f0800ed2f07720407530e846f0328e381b0688102f03282be112ddff184d30390304103bc297d9f10b2082077834f9b42060510ca837980651c0c9c01b1b0680a2178a2015f082f65f01ff3724848600ea40ca0a15060c1890c17932fa99b6acecfff6afddb92aad683f9366606db339fe302cd9d9060ca0b50af0352061060c40bc0a8893d605102782983b821c088091934032060af0b283dcaf30bc075827ab6ce7fbfedf7edb6db7fffdb6db6d84d04184103ac1a89aa84d03))) else (if i < 25 then (if i < 23 then (if i < 22 then 0x821b8128803c42a9dcf6b0203406503c4216e104e020d90679f9dcf72db18afe07df606c05a08204201e60d435877caca4214403882c41000f9f2ef6ff5ff136fcbf36efe6ffed66ddb3d9edb61380c0085c038212121780fa1b862514005b84138083641801ebeeb143017e010d011e854d1fc20d810c481e210df384d841184b8083602a99cf08370204407884530eb6040af0788300001fdef76b3a6df9b6fb2ecffb4df6c399b05c84f8185c48405886c3054474bb0e641e60f83e91c8400b85b41a9eecf841b0238101303c42bfc9b9eb7210c0e612c080a90a1f3b988f1500034c484781b0206e053429dc7c1e03c52109006d5087820212c161bb0a33b32dd39dddd25bab5f4f5eaba839bf7f9f9039d9cfe5818b6cf923183982c838034342039037029a2164c080d816206b1e19ce060d8c1e0800f7cc9df841c84a84303b8103c43007de68ed984c8430238183c428032dc209c041b20c01379d6104b0384d058c23f7f59cdfeffbedb75adb3dbffb6d9b6daffdb6d84d04121a89a884882f01f0082185f053458079721b6210e0686a1b108fdfd73cdadfeebfedeb6cfbff6d9b6db6db6db09a143135108105e018434350e80a68af4cdd15087020430bc078050000007af9a867231910c040680bc078061ed3b6bfe02181f0083402d42f2595ac0c8c41e0088102e499f2800044862020650534200000423bc4c0b850006099100690b2846adf9dde3e821e0238103448806503c03801ef4bbf7dc7dc3b6dfe990dfb6e010830431080bd0a6135873cff3abec0d0c09606e040f01950c03fc32c3158f6d805960690360d0ca85007f9275b9fdf1f936def73086db02d021a8470170087105689ac40f2c181810150c44101f8f28508ee9f6d8034303481b0082186543001e49d1fef7179b6efb98436db827804c442d82b44d61877d75db7c3b0b1b6f7adb5bfefdb7ffdb0ca0bc448e010cb0b231187168ae1940960d30600a20b7a1a76868b3b60039c2e01a432a134a40c05d8340da2b0305403e030e6c1f5002010d606c081c414c0af60ca604903e0104d240dc098340c005d715efe194c0815a0f061d0a00f587fb581e40f8043284d61401fdd1b640c3282e04d611c30e903267030000f49b8c0b0c0a0c407c1e0149ed40f00e0b40a8085d33bd98302a41880f8320280176816a81c0f8150100093f8094080580b40892df01281016944010487c0420b05a030073f19240e20a0a606214c0bfa9df4ef4640f409c022180d90630cc950305403e03000c38124bc000164284402a0206806d028df7c92541ce3f554787bcf083fcfc2c1ddaeb97738b5aae57bcfece84d03aa88002105c8607105cc4000000003f3b2de0b5809408096a210a5924a000e860210205e0530203c5c8b11450040e820b0320bc0a68470a87a0b11881807 else 0xa60400000002cb201240044b20d44621b4067c40cf261c00308029206c020d00401b40c4dbcde010d006a02c040269839092003c020d44621b408300bc93924030048b1dc78181030511886d02bb9bffdd35fdfeba6bf7557d75571e7ef3cf2719fdcff3960f9b927c1de3cfbc92001043901940e816982837434429a24230ce00053811ec081b50618c111c02038081006506d020f1dd9a7e366806d918816402068868428420db6000a280d060a0da030001fbf0aa175ffa1555a177d777d0aabfd57da177b5dde9de80600c07240203c83c06506eb054381c44134509c0205c918870020007c3c58761839a16002f70e04c0b20da85000000001fd692ba4abb81fbfca7d553b8e1dce13b03f3c2c3a7ded7af2fb9e0d00040dd05a0c160a0e20b98800000000003f65c988f0082d418816028035cc81802088341741000b96c096040b5061e3c7c041000e389940404121907c1b50ac69cfe0228181c50682e82800e7d981e61a490064940c08508188cc2b6140000000000000091df86501f05683c42003a7e69efff0bc060a04604702311054872758185682a0180001373eec141944600f108bdd3e9cc1518101908c6103defc1dc8041f0988c6811812c0c2c83621800bb04b03e60a830000000000000cf83c483820202581d8085e06d4280000000001ba05a7020548300000000000000502d02a010c607272fc0f0087d010809402a230801b50c00004e70305a054030027f92cc448c41e20c63a2f1e880e1f2c2201870086501886e857c2800000000031f77db384d2181180414232ed7841b0384d03bc20000000000000000002e30603060a6830077f7e5bef0d30ab135c04303e01117870067badb72460114860105080f061fcce08a4702620205c85906ec2f859d306905e0143108a05000000000000000000e9ba08226702c8300003e9b96429c030620b40580a01d37420899c0b20dc981630202d418f8e1e06260082041a8110124420e03681b8a659818189338320200000000031cf22402140005d2c240c03282e2102784e20c001012c0ac064403681400000000f89c967240f3800510a014460740a685277dba70100b41ce0550800463bc920440001220198650594217a91a41a40a80ce3024930700094150101a01b40897f302c426a0102a027053d920548480d2a200865f7640450084d0274234cf50084101a816020000000012fb190831205a05404002f76c41694402f01081501401b9efa25d0c08c020817c1e217fb93eef1f3f3d605900a4632182128080f10e01ee35184a8438083c05e0284279207086c002422c098041242c8140139cf43f84102d02118903c42f9cd4a10e04e020f01780a13c82308770024258041d02ca11e4260400000001a5c042c41b00c7cee400283cc60b4c0d210c1e17d0aa67bb4f841) else (if i < 24 then 0xd614d0808a4cf140101a8606205341bc90243087010250190042b02e015af3a030805a0402005405724144160c80c9ecc82c02828505020000001d602111040000e3f1e7d8053900d2015d12d0c60b0bc0b3863e207273c08023b28650401f01d86d42802e0eb89adb5edf6ddbfdb08806ca010df0c050c860000000000000000000000000000000019fc3e638123f279986050ca0b7097067030bc0b78700000063fa12ce21a1811108000000000000003c19cf94e0d2b0120121e2310b3850000000000000000000000000000000000000000000069379b0085e0300160200000024beec2f583c2f00b010000000013934300b117c0c000001d14300b08400c00ee3e33c1bf2d2b003102c7032082350bc8600001e2e8c9913336c30902ca040bc45f8469c8c5059430878138d02ca08703438040000000000000000004d08805f82000000006ae09308896b8300000000004f983482b80c180f3f0a3bbfd0fb19fc09e09ac1240d20ac0246a1671000b90570182000000000003a0fe6d36cf675860de44982c2a25ac17e174a41486583c0c00007cb07987027818fa604e0104f837e1d4defb6db6cdfdb610409e46a26ac10c092190e0000000000000000000000cf6eb11868658185e423a6bc2d4c1b80413d0c415d27bfe6cdbf9fefbf366d9b36dfffff617816a09e46a26a86246241040e099a1916000000000000000000000000f901618330241c0200000000000000765990270081841b8d81826d07818000072be80f18e1860960103990c0af8500000000e4dc02301d0541fba5845201282881213e5e9d0c0cd001320108120e02be1401ba60e804e0104d04f276a0138048c432a132804204a0a030014710039b078c70360f90c0af84000000006a81c17e0800000000406605e4c7001250e505f0bc040000000a3900601940ca1815f060000003c19c41f24a302790338191a85bc280143903c0301de8194302be100003c18604be4e746305d0385405e05bc2b4e46202ca184320800009aa0604f16b032dd407a060b504f047803381b2366fb660b504f1350310bc8500173e5586061032828b585442008cf24ce44d8c1358310bc0b58400000000000000001e7fa22f0fc3bafe63ec003401620b50300a500c218654426bf9b068814082267840000000000000000000000000017593c2f00c412c17e104118679ce7d866de20b0ca0bc20a0af850000000000006bd9b67110828308300000000004f418610411a0740e02cff73ba543c3e66f6987ac258102881a01808c61b92d46e054080f046208a05a05402a0b01009223160a0259240c80001b00d01640696f9e0198c3a03282f18101682be142792000c8a046040bc0a604001c4fc92f0f00390ca0409960a0af0a6850591112001d0c1540817814c08003a5911300060409905a else 0xc83300a07023057839f89e7c801c1932002b212c12c0303807817e0e064923860e10067c0f0bc0da046bb440805804d41408f1e304602c05f834f634408c1623c06c08fa43870b01de001b09a86e81f057c280395a1398070b80290474c0382328ce063179c813087006098269100690b8055b9a246204c1100f009ac891880383c0194c7200488484902059057820e266298fc03c87ce0021020dc0203309408c15e0e003e7e84f4807bdcee1f661802301920d60b3120ca863e24c9e00831dcc000ad8120341e8238578312f99a0705703005b043b461340fc0209a08005aa0705f1430325effbddf2c45541982c81c1040a61821392000860a075060460af0409e281c010c28254214181182bc140027240100d8503a8303985782540ee04043f2f8eea0003c1818503a83281189058c30e1e0602c807412a0a0f419508f5f7387b6db6b6dadb6d414208824390c4a1400005ee2b66db6633a09511143830000e1f7e198c88f23184c2040c182e81c32831a19a723101650d22504543881c09fc4fc638e6f0201f0c041207506d031486070da87d02901310381bad011881cc482701139a20706c0ca83701e1b319991b33618418360188654200003a1848d038a1c1b483840e0d8067cb7740ee04213a0708f00a2ee019c662e66f40c32943031a10f2c81d01f40e0fc031b8ea4019b34f40d43032831a107818cf80ae43070061020a2321bd4141940c13b8803c62f8634198064141ac2be14395f002339e118609d0603c05f0af8508263284e60f0026a1bc0d218c083ee78d684abd64fc4eb8d92a0c008c1609646226b0d940210250501860bf02464c204781a40dd2ee703cc0a28061007c26a15f08002eb11882f848c1b4601046419c0c25b880324886090320b20af042e17b04d231a0404b05f0585206064049d600245400180750af0312e78000c1036070040910af841e39c9280382c7e40406b020470b20af8528672010e06035846417c2bc107d506c8602681fdce8deb11450602090c85f851f35b03090505f83138840260040705f0af831084009b0f0e0f41a41417c2be11d1aa0a23c0d30678c4414081a60cd65df28348180fc3488f029f903c871c01f209e06440f8040d78484d42be1801d95941429c4660cbad40c0be233067aeeb20a602f119830cfc4271f271001e6190082bc13c02a240380d615e0e17cb0391f87001e84e013e09004e0106b1190af8600000e3c8bc900e0c172048703386e857c200001747801004e8194144642be10769581b183666d4140644d60c3df986cc3496032a1826b06b85ba061350bc83008c303337717279c986503386341f4602ca1b033064727084a003c81620c0321881b508f1a1308cc0cc19c340c1a811406f25d86202781ec1a00829364d27c589a86541000e382329411e061880322)) else (if i < 27 then (if i < 26 then 0x4082041982d82294d40c282a2867e1f06733243c9ccc2c00cc0af416ad619418d0c0077bcb7fcdfd9b7df9b59db3b59bedb1b066709708d0c5050e4535a0a885540515020002efd9b787359b3586636a80e24a22a6a0bf0a00de9c6c2460c08c02f21000f8cd20f41a91dd000134084060472310b706e2b2c44e83438c230111be643435c8c4234134941605e8340c00009721c0460a8069348700a83301800e3e4a073d0fc00fe1f1ee41980408e07c0782782e61c71023f39efe1f007f82879c83681881300c0f80f01186d441f880a27361e007c23980ac83300c1008f02006d03838c021f313a03c031f970278170080f03588f06d03801f12604c380383cc02b20a0cf07c04e1720c0000e1892811398180000e2078a7e78401f0771ec81080d07d21801a1b50c00d73242309120d05d040053750eb02038a0d041e3c400e08f80e36283010488d0686d42b2b903130227305d04000035a74c020d005819408577de9a0c4c2481380424417419a4df2c021220d005809ebb088888502281700828423e00f0981c3f0098a0d408a05c0223c03e1b40e78ebf606223cc09c0303c1940cb9a02330101c02e8200000004781c282187c0506a045020370da850029e6edbf86550410383608f429477c36631e6d9b300b20620584101950a00f2ed06550401f02ec278e9199b61c3651150ca081358400579232c46b34659db43000b34381a432a13482ca1b40806cb86501a81601a79906550468181f0200000e324e48063c1602c0643819c3742bc149776021440b70600ed416c0608000063a23c25f140fc3b964a2803008988308283306e865430e7ae2f1db7fcceae4b5b8043642b450c4d61400fbbcb6195079033c0226b0a00de4db61221152d70600b2ea07081831c0b01000000043082187408033c119e0806b0670da05474c0807a0580649f054b0103005b04005882d80c103c73e45802514002ac2740e40c3282e21400fc490f0640e7c01805501d40a80507c1242e01dcbffb994bd9b6ddfbedbbedb6f620b4021341940ff2180e90e471de4b0129000244d030ca0b28418e044be740c1e014a10a0d0214141a01b40cbbec123209d0302a80f053d920542460d2a2008007c7258783945c9001a064040d218c1650a5e5bb118a8303c02204402a67d240c0ba43019813d8e9b105b02e0104284767bea6860461a061232180f00cf72fde77d323150605d02402307886026724303c02203581206a1f06d02b4ef5046409a062220a80a4f6d0390302305404007640b048e8100601064f9a0404b20b0ca0400f1d75320702307802684184f040e0142141a8114343681400000791662f0a8002486048853418003c3bbf9ec00fdf0a00cca0c742340d4268101e02ca1c000000f132001c1899002ac020dc07817e0a7e27c9900e099e000a304 else 0xf03699c7cc825821918d0505e028b5c1100f04620600f4ed2ea04088078231840022e6042c00a80460f0af0b2040004e354168100ca0c4e7336de6c0bf3e6661b37f399981606c04d04b043052a0a233872a48003903892408cfa0404b0380af8425e2449c8007d08839360b8041122310af8508bd00707c937067027010d50af85e4c95acd818ccd2cb5051452338317970fcfe48300143e424e02581dc194160103542be1c3e1401c0782fcc1b050dc19c042202be1800b8bc7c3f7f62c4060583631926e2101221300840817c15f0e1f9fc19cf9481e0c1c60bfcc1b050c427c0dc05c382202be200000058f39f87c301404e3c7f6097e06e04144e1c46217d0e0002f7e17d85deeb857ad6b42bdab5d500060b6f6b7dbb5a055feead5a366e82c0211804086505e305c3880b2c29c89eb2310c6821020f5f27259032617482e02c46216f0a2e2f878fe49280005e47e0e24e025c1a01181d4143542be1c003f0f1401c300f97f306c1435057037010880af8700000f88b90010f24d81dc19c083542be143e1ca00f0389f9836084b80b87286057c3003b1537556ed839f3261bffd9fafeb55a0683b836029025b83065286305c42d40775f5ddd7770005bbbadddddc5aeaf5d7fe8fd576abafe8d530c300c30c0c60c10af1430310ca0a650c886db6db6db6eddbb76b5adfd6b6db6db6ed666f336666db6db6ddadb021818f81f81780c293238643080201034c0c05c0213da905805020a0a042e46c0e4080710608245001049b0380af82639f8e881e90be014090eb01b121350c686122881c03fe36015483480b0387086d0306064920e1006750f0bc0da041c40c0c8a0f348338091981b86e8284613c20702422419c0443436814927240786000cfa061ba15f08138cc08050e032240ce15e08000000d81300813604c020470b41158200005ee73edefce0e7db7ff4f9872fca7dedc0208617617406aa1826b0e004f1723f03860be40108106d0310d0dd0af86003e33204861c0f0805541ac041103282e418000000000019f9f0676651e4ecc2c03301730585c06506343000000000000000000000f181c9218707c2141ac0a43c4342f0368189776021680b706f9b984c82a82d80c2001fb9cbcf4e6def99c5cac205c021b215a28626b0cb902701824ff289ba6def6fee1db069300856c888a1c2800000000000001f1c0c921c3078491050603790f0bc0da0600e9888a81580c180000000000000000017c7dcf5c2f3adbff30eb968b70088886c8568a189ac300000000062188010e00450e7120910b00400c89107020a0da061781b408b5f80ead7e15d5bffc35dde855feab75adf7c2baaea87f4f7af75efe8000c28468182a28928305e29a86ed05449ba0cc460e04a2a085deda9ffff3bf6deff37db7fcdde9b79bb3efdbe4fedc25421) else (if i < 28 then 0x8de7c1f97a2226b040045db808148b5c194731b33df06c009e06205240c1a70a8d70d4a0604f16b04f21366d9b6e61b198c13c0c41345ae111bd22282228614a0800ed006045e17c0f423d2224080600c849581c0e00d95a0290d305f0300000040247ba6124398b4170e00310b7843824892c98040c46a06216e0820e909847312c2fc0c42e60c608914ae0417e40c06216e088024e829863cc2e40c42de0dda48ccc342201e01000b20b60f061a0672480f0c24010d7020e40af840e4cc7c8048021ae03e061ba15e0a009103d9f03d01dd21121ac0e1c81710a138c501018e0321c21a15e080000000000009becaf7a7fb0ee0df643843873813808a2919c325bfcc0dc0e08e5fb6bb7e0028646260d08aaffbbd55555dbef56ea0000002bbaaef81555554140000005428804018c10c0c61800d7fa79cc20c18220c341e214009dfa05b14370230f054051f1321e17e10e01ac22c0d40ac0450c1a42e41e836604b2e06c7010c3088040000001c79f301998384999869a4590ad8090091886cc28e32431e246c40058158090686705902ae4d73c148c442d01e2100001ae06c23070208804078f87062228007eb813c0dc0dc082c42e2184ce2c401101e06a221ba15e0816ef0fab5bde15ab77f87d777d0abaadd6bf85ffaad505ddfaeebbf40006024d42141815030144432837682a240660366459b0d688e4601b304735bc2048c1c081e2109606c0c3088035edfeecbfb8beef36fbedbf9ffcfdfedbcd6f736fc4f42030c21682d4442e150c29e82a240060f7dbfbf628ddb8ffedfe2b1bedec1a609b08e085542a3008a07df0307305f892581b02d02200c0000000177cd61e41e05441b0839e81b4741a009201e03c01a4621900af66b3761f46341f06000039f49e649980c6049100c045441851428a1497f640b6e04e0228614c0a31397e3be7008788581a8158084e033857c3002999deffe06c905b0170130e0888626edf04e5808a104442000000164fe06c0327010a2088050024f81b2414288220100000be06c0320888300279d767e0b0462a1a26a1270a7db9d2f7f36f7e9eff98e0e7cb4bd0e02d415b0302b0e3031443431886dbbf4db6da18118581e8142002d8821a8603c0180126a180840f0060c4479c003e7e0f3b138503f00d8706082105fc30034bdb8ba07b020bc23107805e6564621100f061a0800d2f6e540f6040b64620f00a0000000000004624f3801f7e1e700e07e0116be0e0450af864b7e7807e01097029111052738b2018f09038041844343742bc140071be481e4870c0102640982e01c2582e01891640182778160c80c81a1aa15e0b93a42861100880613980141881008c1c06417c08730805180a0460e60d0be0474d5a8102201e08c41000503cf1c08af919c198485270382170750505e429da0d004d05 else 0x1e3819243860248601948785e06d02877ae445446c05c0450c151fbdb88f488d80b8084b88b832d380814e8881802850814810f5aff9bb4bb06ed67acdf6b00e446c180b25d344417e18000000010c7dfb230f66e002689688e88305b05069c300000c7392403c2640c020940321a015e0ad3752221300ce0520800b3e414e23205e06b72ca088338b5814820423700084014268180702bc1165eb3c88f0082306a0148280000f7fac0a544681dc0446614ca88b8089a81800743a6d631bec3066b6de88014e88833c21160200c8881e86a06d01b4e1a807a26a064872)))))
def level11 : Packing := (1977,4,8,0,0,17,1,nd11)
def nd12 (i : Nat) : Nat := (if i < 5 then (if i < 2 then (if i < 1 then 0xb8041800017ff525da7fea4bb7ffd2476dffa48edfde491dbffe90bb6ffd2176bffa80edffd201dbffe203b7ff44076fff840ed3ff525937fe93b26dfd2664dffa44c9ffe289937fe90b27ff50064ffe880c9fff52606ffea4c0cffd4981fff293033fe52607ffe93c0fffd4481fffa4903fde49207ffe7240fffcc481fffa4503ffe48a07ffe5140fff8a281fffa81037ff50207ffe8040f7fd0081efea0103fff08207ffea4b8dffd49719ffa92e3ffe525c67fca4b8fffd4871bffa90e3ffe521c7ffe9438effd2871fff250e3eff41dc7ffea338fffd2671dffa4ce3eff399c7ffea2b8fffd2571dffa4ae3fff315c7ffea238fffd2471dffa48e3fde491c7ffe6238fffd4371bffa86e3fff40dc7ffe61b8fffca371ff7946e3fef20dc7ffea138fffd2271dffa44e3fff309c7ffe3138fffd2171dffa42e3fff405c7ffe30b8ffbc6171fffa80e37ff501c7ffe8038fff50071f7f9c0e3fff301c7ffe5038fff48071fff880e3ffd101c7ffe1038dffd49619ffa92c37ff52187ffe9430effd2861bffa8ec3fff49d877fe93b0fffd0761fffa4ac3bff49587ffc92b0fffce561fffa48c3bff49187fbc9230fffce461bffa86c3fff40d87ffe71b0fffca361ff7946c3fef20d87ffe9130effd2261fff244c3fff38987efe6130fffca261fff144c3fff18987ff680b0dffd4061fffa00c3ffd40187ffe7030fdfcc061fff940c3ffd20187ffe2030fff44061fffa92a3bff52546ffea4a8cffd4951fff292a3bfe525467fca4a8fffd4651bffa8ca3fff499477fe9328fffce651fffa88a3fff491477fe9228ff792451fff988a3fff50d47fdea1a8dffd4351bf7a86a3fff30d47fde41a8fffd4251fff284a3fff489477fe9128fff92251fffa04a3ffe40947ffe7128fffcc251fff8c4a3fff485477fe90a8fffd0151ffda02a3fff38547ff670a8fffc6151ff78c2a3fff50146ffea028fff14051fff980a3ffd20147ffe2028fff44051fff840a3ffb081467fea4a0cff94941dffa5083bff49d07ffe83a0effd2641fffa0c83fff399077fe92a0fff90541fff9ca83fff31506fdea1a0ffbca341dffa4483fff40907ffc8120fffce241fff98483fff28907ffc5120effd2141dfda4283fff40507ffe70a0fffca141ff78c283feb18507ffa8020ff748041ffe88083fff524877fea490dffd49219ffa9243ffe524867fca490fffd4621bffa8c43fff498877fe9310fffce621fffa8a437ff51487ffca290fffd2521dffa4a43ffe49487ffe8290fff90521fff9ca43fff31487ffea210fffd2421dffa4843fde49087ffe6210fffca421fffa4243bff48487ffe8090fffce121ffd9c243fff28487ffe4090fffd4021bffa8043fff40087ffa8010fffce021fff98043fff28087ffa4010fffc4021ffe88043ff710087fea2010fffc2021 else 0xffb5bffd6ff6fb7fd840dfb766f6f6d6b6db665cccc199821841c20c4104a0712c1401885f41516db6dbfefdfb6df6defeded6d5ad66c7ff9e66db6ff6db6f6b36edf77f6edb76b376edbbeddacdbbb76d6b55b35ad666cd8666db021a09a101110383162582e8750c8a7f6deffbc39dfbfb77fbb7ffb7ffdfffe076fb7dbb7fededffdaaf554ffb7fb68736fbf736dfb57bdb696e09a12c27043080a60c01488f0701a435a0a21d1c00ff6defbdb6efeedfedf7efdbff6ffedffedff6ffffbb5ad6f6e1037f6fd9bedf6d6b6db2d99835c1342584b0305281c1885007c8402fa0a8d0011e770fec3337ee73beccdfb337d2557337f98673326076618f673320813709610008439050508733f2faff9bbcdf377f6c2548e6efeddba3e6effdb6d3731e7ecd8660cf63ff9b18d4d4935353264edbb753bb77f9fedb288ba10018545120141401893921c3262cbfafe673773b737bfe76e6f7fb7e6edcdefb7dbe3633fd9fbff0a255241dbb7b7b7b6506767ecf81b6c6a6a6a6a6495322f304e100083281c2310a082857c536f6df6db6db6eddb76ed6b5ad6db6db6ddacff336666666666c66b6b5b55acdb606201802703a1982e18be0ee17f6ab35bf66ffbc066b78039ac9436663131400a704a04c204142805f88871a438b21c490e1c863fc2bee122906cc83624147a06bf0264812e402fe000cfffe7ffb3fa55faa8fc0b7d3c3e15ded1cf5e97a8cbcc9de360f1a877c4bb981dae4eb9075c43a5e9d2e4e7de72c7b8eadc32ae02b6f78b7865b79edab26d5536a89b2aad6af6b53b5705a676d333686233fc19e00cd06657bb287d9268c6dc621d30e418710c38060b5b011d7e06bc665d27ae1496cdeb4915a44ad2056730b3905927ac4596006adc055c62a6794fa0a6f1525b28ec542f69f264f2a275e93ae49c424d20a658532b299514ca4a6505327299314c20258f52c6a95444a9e254d1279e93c749dfa49cd233e919748c7a402d1cfa8ce2466d22fed17e68beb4564a23c50e40871842d1216690b24858a42c1211a506368227410fa0428fe8a7f3d3f9a9fcb4fe4a7f1d3f8a9fc34fc387e143e929edb0f28a788f3c439e1fcecee756f39e41c72cde9c6e0336109b064d46e6a2f34a119ba4cdc264e5326e99354c4ee60ae2fd397570b68c59182bda956b0a7ea51f228f514788a0464f3c279a137d497c84adb2481123e891e446f6229b10f7c87ae43cf217310b7883fe412020079001c7d363e931e9f8f4dc788c3b301ce58e70c70a2376b1b370d67c69a2339d195c0c48462322f8b17c18bdec5ee62f6b17770b92c5c862e3b165a8abd053ba29d5139809ca04b20230b1181885543f3a1f950ec6076103af81d740dd306e7834ea18e40b3d8525c269c117307a883d241e820f3906ba82d8012d2096103ce01e500cb00452012) else (if i < 3 then 0x550000000008a0aaa00c435c100003b7ffd6ddaf7b7f6fb7f6b7da1bff6edbfdbf7ef76dff6ff7dedb5a06f9bbdb6ec5a308e028c5893011c80c45796b2191603de001eb5f8001ffb6bf1a03bfedfd71a1bbed7f1a37fffb878a1ad7d00c0198dae1a37777fbb6982d04201e000c6880a407817cb58438b18fcde9369666f858599bdbfbfcdbbb33611846cd99b370c518911c120d70086b2d71000db6dbdedb7fdb7fff6ddbfbfb7feefdbb6bfedafdad6dfeffdbfdfeed6f3fb667ffb33336fbdbeddadbefb36efdbbbb5bb376d7ed6d56b36bffad9bded9998c6db3609c03c001a91262043c35e0b06343a8660a8d005b3b6b6fff6ffededb76f6feddadfb3ff7fb7df2dbfedfef36ddbfb6edfb7b69b6b062c258470146343a863011c85ac5b8ae8c6db6def6dbff6dbffdfffd7b6ad6ffcf6c666dfbfedfbf59b76ff7fb7f77fdbb59b76df7f6fb59befbb6bdaad9ad6b67b36199b1b77f6ddacddddffddb580cd09e0010c1ba01062c430586bc1543a86468036dcdb6fdedb6bedbb7ecddffad9bfff5bb7edeff7dff6dfdfdbdbedb6cd6cd6db6f6fb6db6c21835a02c0700a278628c4ba46b2d7166dcf36e7fb7edf7fdaf5fe31f9f2cbd7ce77ff67fdedbfbf9b3ff799b37d366e7fed9b3f75b7ed1889a862827008ca8d61cc2d3126211600ffdb77f6ff6ff7fdf6ddbdfbdbffedffb7fb7f6ffffffde05b6edff6fafd6d7ff6fb7edb7f6f3616336badb6ec1ab09a0780492a210864f218a310d62f02f90c8e0000002736cdfbf536ff6cd4d9db3b75367b67b7b75367f6cdb6ede47cef9cf9f6233b39b30467b36798fb6113d6490d6284d0806082c2f8674143a620012778c6cca7f6fb1dbffc76fb379b20fc18b30ecc7666c2c3660d584a01a241a4b583146310f6d75fef6eafffb7db6edf6e037fededbfbfefdfaf6ffbfdbeb6ddb8dbfbe6f5b6f6c25840e90a88c5808e415e4f01890c8b36cdefcdbffcd7ffcffafcd7f69cf9cee46dff35fdb6b8cdf7ff3fcfb30c6bfdbdae6f7ffe35ed55cd7fe7a4d0d31a99f6fffe1873ff6d811f82e84a094022981a831a200382f8532185ac5b47b6deef7f6dfbff7efedbbffff6f6fdbfdbfedfc026ff6ffb7ffbff5f5b5ffdbb7db6edd8b366d6b6db6c0d608c028c6883100c410e189090a617c86468f8f9bf49da599bf85813337e7fbfe6def666c2332b06666339b676d0c518e0906a43b008910d65ae2455efe7db3ef336ffe29d606cfb19e6cdbdfdbd2cf336eddfedd3377b3374cdbbb714e88c92799b7eb337bf6eeadb04e0143d828359350ce438b5c4b6ddeff7db7f7fdbeedefffffb7ffb7ffdbfff6ff6efef816edfcffafd6d7fefb6f6fdb6f6f366b6cdb5ffdd6db76c0d609a12c250260146243856c3111e14c6505f2191e000000fb6ffdedb6fefdfb7dbdddbff6fedfedf6 else (if i < 4 then 0xd8f9b037831f9246146c12c250383140c3285e20a15f1266d8feffdfccff9b6cff32fd9effeb4eecff3b769867e7631ff3c6ccc1f6db3dbed6ed9f66db3cb55adb66cd0cd9fb38366c0d503831a248186560b0ce2f1870af8b1e23e233fcb1fcb8e5104024d82c7ec62ce4199820031c1381882a0419417c57c417ebf339bb9bb737bf9bffee6f7dbe3fe33fb306767c6144aa4076ddbdbd9b28edcdeff6dbecd93794d26224d1942f3036120080f91885a4142fe2800000cf875bdf87b75ffeee1dddbad7fc3ff6b5a1fcf80000060bfffdf87fb76f6ed02d7dafffaffea834000001ae3180bd0ca108228350141c0768787315e0c6380cf5fff7e1ff0fafafdde1dbaeb5fc3fb55a1fe7800000c16be1f6ab540b77b75dddffa0d0000180c315f4268086908619c1dd0c46a0c62cae7bfe6518cec77cde7ffcdbfcecda0fe118c6fcfd9be6f3666c8c6c10d0ab0880219d8185f2e80c618c5000017a5df3bc62dcb17329b966821c66372cca592c8c6c05c18b110bf0c6140078e31c6328ec53ec500f0706181b142c58b18469890160d22bc57429ef4a6518da7629b4ec52084646beccd3636461b50602d44834c31854e1f5f5dcb0ffa6b7a687e369ac04b96637a6b44c260c366124080bb0e0630c42fc38001801bc3f99b873376846b438dbbbb43e0003787e36ddadb86d0d6affa6806003180afa1341a808ae0d343018c40015e7dcca319ecdf9fd9b7cfff9bf3fb141fe0a3187b9b1be6ccdb9a31b821c01a20c402f8dd1500c618c4801ef4a6518da7629a766bf64108c614cd3eccfb231aa103040b5120cf0c619387bfd772c37e9adf4d036fa6b4e04b96589eb41313031bc05d84b101500c61885f872b9ef994636ff9fd9b7efcfff9bcfec76683fc23330ef9b379b3364637cc8d584c01a24c0c5405f27e0c618c500120edf7f23b7791b8003b7df91ffb700200455143b7791bbb8dc94c300c08600000c02bd04a08142838490310bf103df6c6e3768d6b636dda3c000003636ddad800001800d01e07c0818c2a71fad772c26b7a6801be9a025cb31bd35a999a606636054c218703186217e18f1c678c76441b9176440754598c8b46669b0060310bf0c463421e38cf18ec8b22e441c0ea58b0645a3369870180c42fc3115f0848023bc8aee456e00076f22bfb7001007722d6eee37221860181801800c6015e284608310bf0a781b03706ed0cd6b60db769e0006c19b6ed6c01800c6a03c0f81031840c0060717878dd70e7f9ddba87e66d6b4000000c00c0bffc3e376f6ed0286d7fd7f543668d718c10e86508a0d43c398af063140018016ff0fe2e1ccdd7878dedd43f1ad680000060060038fbbbbeefb4028d9bff5ea86cfb4630a2a134205450c0ce2bc18c4800000001f6d02076d495d2d0825a5a74665ae09800033c08a0a450 else 0xd6dd9adad57d66b36cccc66cc05b80004a2143305433db7fbffdfe1f3edefffeeedffdbdbfb7ededfc0fb6fdbf957555addb6b7fdbdbff6d0fb61fb6eedb5b0c016984e0660c1183a03e01839019a0b2191a007b5d9b5b6ff6dfffedbf7ff6fd7dbfdbff6fbeb77b7f6cffb736fffbedfb32d9eddffedbfb6db7b782703a04607c0b00b12c14c38688af4622b45347000c631e7f633b8e51043e06ff619fb03707801630960cc04188ca1782be20db37b36ffed9ff7ffd7f7fb3ed3ffbbdd9ff6ed33d9fe76337f7f3ff3eccc367dbf6b767e6cfb55ad9b34cf6cff6706cc67fe7ff93983f2603d81021831a2432907e0b0ce1805e30e15f1a00db4d9b76d6dedadff6fedfefff7db7f6fffffbecdff6e7adbf7edbbffb5bdb6d6fb6db66fb6db66edbdffb6db0860d503c0404f44588e010d70c5188da15f1a0000ffb6f76ff77fbefdf7ff7bffff7f6dfffdbdbfdbb7ffdffbecc4dff6ddbff36fd7f5b5ffedfbffbdbfb6dbdbed816c3adafffdb6d86061301281e011640d48b8438628c4358dd19417c86483edbddff6edefdfb7db56ffedf6ff6ffdbffffefeddbedfeddbfb08335b37b7b66ededb77edab66c1ab096060f709410408270298bc06682e3063c63cfec6771ca2087c0cff60fd9ff66e187802702c612c198083119443057c49b66fbe6dffcd7ff9ff5f35fda73ce7738d7daaee337bff3fcf663fff1aff6fdae6bf19ff33fb3ffe1b0c69a3a62635ebd52d4bd63457892a128250083506343b058100be430650b88e6dbf77ef76fbfbef6dffbfdb7edf6edff6f009bb7fe7f5feb6bffb7f7b6ff6dfffdbfededb32f9833333adafff6edb6cc1a026010b543a18a3121210c608ca0be43235bffdfbf6dbfb6db76ddf6d6b6bed6edb76feefbb76b5b5f6ab6b33667fb33337b6dbdbb5bb6bd9b6db6ffb6ed6edacded99b6d999b18d884e06c0210c84074c16c4a8860a8a1e3c7f8e33ffb31fc3c691d02ff9ff87df6363663b631d88cccc07e003443146207b04c04c024403590c195162a7fe7e6ffef6636ff893acf31befdbeb04e856798ddbbfdba6e9e6cdfd37d4fedde6c6f7edeb37acddbcc33731cc6ee6e1a10ae09c0382c35f0226a1a4880ca8b0e755fd7f7dfb7bbb7fedfbffedfedfb7fd557cf6f4383e677664c37fb7edf6cbdb46bdb776c6f04b09c06c38028e41641681990c417166d9ff3bf77e6bf99affd679af5ede4ebaebae9aad7aba63f9f4d99cffe0cff59bffce6c134d2e98c19befac92c6318608afa1201e8303100b02a8810c17829a300000cfd5b366753edfe76fa9fd9e76f6f219f3fb1589e2a9214db67eddbb76ca56cd99db6fb7b64dc86cfb3c1b37032c00c0b405f46282857c40c4788cfcb1e5c72c5184c0226cc2c7d8370200c18e060863282f8af860018c63e31f9fecff9ef1e771c61c027f36))) else (if i < 7 then (if i < 6 then 0x1ac1c20ba191462dfdfbf31be62df6f316f6f00315b5e8dbbfc5db76e36b662dbede66d6e030017316eb9956eb7018a084094498860a179432200063c63f3ec7f3b1c0a21e07fe4cec0c002ca254318485f61c2f05bc400000c7f3ed27ed2ccde10b337bfdff36eecfcdb09858f99b68628c4860931101d30086b2d7122af7f3ea7792dbdfc3367d9e59b7ff6f67936eddfedd9bbcb37b36fdfb71b3ed866614eb09289ec9b766eedddb2c1180412e0b0d64942f90c2d712ccafdfdbef66dcedffb37ff6dff7ffffe7dc9d9bedebffcdbfdfedecdb6cfddb64ec7f59b6fdfd93586382584b03c022f05aa354621ac2fd0c8d007f33defbf6ef73fb73b7fb37fb7fd9b9e76fd9ffea95536b3eeda79d9fbd9b5fc10c0c2302c1782d41c06b417432280000000063e3c718e7ecffbc7028a01fc7ecd1fec77b0607c30c12c1b00846044c0c358bc16f120f80016efe0b5ed0cb5fb54000019bb5b4185bbdffb5a3700c000318018112c138200260e4623282fc40c7188c73ecff3d883f100e3ecfc7b1fd8300609c0c2f02330e0be8405bc4000c463c627d9fe7ec78c1dc7009f6731edc0c18fe48c45304804606119070bc0be2de20c57eff7e62df317d7316edcc02fe62fedf6e2d7fe2b6b46af31bdb8dbdff698bbdddccf6ef6bdc06000031c1681c5e206a242d5870b7a1914000000000000003f8e31d98b3103fcc2f6363663f6c6c1f0c046205f03204c02180738bc880018c63e7b1e51738387e067fb07f6360d07c00b183301062c49810ca15f1003ff6001fffed78001f1e8077fafeb8d0adafe378d7e87db5ff1bc6d6b7e00c002d70b8b5575cc3282d5064020c70583fa2017c578438b36ff3fcffdfa7fd6ffffdf6cdfffb7fce59e5cefcedfffcfbdb7bffb2dbeed9bffedfb6fe5ecfed7fe6defff6db618118d09a0d013008820e84448603586217c880d062320318cf4c5314c460e962c13168d8387060314148c457c2000029cdb37df55b7fe6fed57fb39bbb7519f99fb328cece32ab59f554b2ad9ff37f6db766caa33f6cff60b314f3ddf373879373d426830ca4614301820a0d282c5e451705f0fd6bba7fda9bda27c9a014fd6eb26f6b06c0186a122d80bd0e0628c42fc3afedbbafb7bfedfff6fb7edfedffb7b7f6fb5fbd8006667e1bfdbed6cbdb4fedddb7fdb636c2781a3161c2f04c8dd0d08105920b8b36f79ace6b5ce6bfaeee4d7ebfffafff55d75698cfa6fff9ffcff9c19a67fe7f9d8269a50199bed6496318c3706c0d018a3045b0b2e07c0b052041c42f053471b66f79bbff377ff9bbfcddff7733ff33ffffcc6fbffb77ffdd89e4aa423535326a499fe67fdce1b064df7edbb77f2fe8d58df6f7b6edd9bea56cdf13944304c082258388750c8188c4050e44162e639b6f7b6db76eddad6b5bb7776bfccd9999b6db6e else 0xc31434c4c6bebeb52a5f58d09a114190084906382c0705f21940c650b88d557bfffffdedfefdfeffdb7dfdf5ff6ff5ebec038dedfffb7febf77f76ddffdbf6fedb7ffb7ffdbed8ef9b66deeddbdb6c0aa8450660d8060f1090870c51883c19417e8190c8f0e755ebdfdff6f776fff6ffbfff9fbef6aabd6ff6ffedfdf0e0f9f3bb3e4c37edfbff7b65ed8d7fb76c7ff82584d081881b01f41e07b40c3583321882e34f3cefddf9af99bffacabda73aebbbbbba69affab55ee98f9fd3679cc19feb33d9cc1352698c19f59648c6284d08a0d40402831a06430650a68a1f1c7c73d3f89e8e8034367e8ca3a081825038156241ad05119194107edf9bfbf9b7fe6bff9faff77f99e67b38cff33f6707cf3e7defa406bfb5d66cbe377fcd7edddd9c9a6bdbddef7ffb26d6e69307c9a4416092124181f00706a8282f9354622fe306318e31ec71867ec760050a9f627d9fd80631e8c42930330207a0c50920a1950e663ffbfbf99ff6cfc987b16cfdfff55ec7767fe6edae7b4c7fcfc6d8663fdb3f6bcd6ddfec6fb67cfb5ecd6ecdf06c7ff9d86cd821d0c41342018e0b40e1ce87503194c48634697f5fe7e7f3f7dffe6feefff9beffe6f779bdede3ff7633f6fffc2895483eedf6fb7b651bbbbfe6efdbb7726e19ecf186cd8a69a624d117824411e096114180202206a8c41c1354142be3862388c7967c61a2a0050a9664b1ec3818c186090d64302f8ca85188e23e7e58f0e32c7b440116458fb04cc0c0620d7091100d231a1800631c79ff1e7d8ff1867d8f600a14fec5c7b901cc63f2310a806704a07008c483590e41432a24cc7ebf3f6fcfe6dd9ff3312c7bb3cf6f58eecff3b74b731fcf8d8663eecfb7d37b6efb292aa55ab28663dffd87fecad8650c4a13420188190cf4309a90e18d163e23f118f2cfe0ca2971c012ce2c7b1c60304905a060f06505f18d0e00000000000031e31fcfd8ff7ce0510f037fc8ec760c002ca2543184b030bec385e0b7893fcff1ef5bffbfe61f17c3c16bfe63545bb7bdffe375b8d31bfaf8dafeeb5ff98d532b5a1e600063f75ccfd773bf680c689206090057058886060ef05235a19180031c63f9fb1fe5883c87037fcf1f6360c002ca2543184b0617817d880b78900004cbfd7dbd79fb73b59bd2ec9d2f7fdffcdbfbfb596d66ed93b3ebf37dfb70c51890cc023285e0740d6c428645000000d8031da831dbefb400031dbb6b701e2bd1ed063bfdb5be66ef40180000600308c381a0b1781cc2fc33be518f4ca76b3a7628ed64104c76b314d0b0c0b20f61e17d18c280003f33efbbbbdde7ede7b7f66fee77b39edff67ffbaa554b26b7fb37b6cf9ecefb36d78218430608c0b01c06b22282e86453f99ddbfedf773fb7bff6ff66ff6fd9bce7b37daa554b0d68ab7ecdedb4e7b1ff766d5c0c1101181630e411) else (if i < 8 then 0xff1f5f01dff5feb8a1adaff1f46fdfa1efff6bf8fb46fed6fc0f018065ae168baaeb8328b5d0841080418d0ec1740c1e05f18c10e3455df3fbbe7f76766fffbff14f4e7fdcdbbedd6739b7b7bfdbd37739bf4dbbf6f30d9f63399853d0b2519d9cdbd377b7bdb26258258460108182c1a85f26a430b5c58e3f1c7e91f148fa090f7a4691d411fc04081a30960103246465438c633fcec6119d8fda41f033f91ec7b04c00620b38130126ac48880c68837fbfcdf7cdbff76fff92f7d63ff7efbb3f6fd652a95337bff9ff3d8659d9ff6fe9bf57f1bbeecfff6eb37566e67d8fca19b19e6f31e43ce509a0c8042183102b82e8606b0d24d4880c68d7ffdffedfbfb7ff7f7ff7bfdeffdfbff7ffeffbfff7ffff6fffb781ec0b1bbbbd9febfeb6bfffb7fb7fddb7ffb7fffb7fedbebe9df6fb7f5fadfbfb6c26836010804948c81706b0c5188ca1784303a1100be44644f1cf1d23148d48c0e9248d44800150cc8c49a8c6050000539b6ffeff7faad9ff37fed47cf7d956ce6eeddf6519fccfec3ecaa9ea95655b3cdef6f7b3765519d8e32cd8a7e7373f1c4dc0cc8c284830a2082a818670be82c65459705f1ff5aee9bfda9eb13e26fed780a5d64dfb5831830e0ad09a114180bd030628c42fc4b9cf7dce7be7e7fb7fdc3f3fdbe0389555647fe1c7f7cfe3cf6443b0489c096c482023106a82c9ac51fdbf9bf7e6fbff9bdfff3bbfeedccffe67fdf38dfefff37bfb7dddd89f92a908a4c6919bff7fe67f7cec3fc18deffb7d7fffcdfe8eb637bf6deedd9bd4b66fa198248411220c1009a83501437518d034162e639ffdfffb7ddf6edeff7bfeffedffbfbfb7dbdfafd6dffedffffef6ddbffedff7e1016cd6b5b6edffb6ddfedfdb30864568430205908e0f20406340c2321219419d05c7bfbf6ffffde1ceff7f6effbb7ffb7b7ffc3b03b37edffdbfcabd556b7b35bf6feddb5f7df737d9ffb7fdb6b24782584d084080c20f04f26a4303986b41644639f7fbfff7f6abd7bdf7bf776ffdbedffd557edbfb7dbf6abda1c0ff33bb260dfdbededb37f6fd66bfeddb1836c12c250211e2d71006e83506644105c63d997ebf33fb6f6ff9b492cdf7b3e7dbeb122c29b77bf9cedba6eb37bd9fe7b7acdeb376c31f1336399cdcc70dcdca1341818a08a184d434910195120000318cff3d8c19ec7eca20f81bf939dc09c00620b381301624438650c6880018cfefa4fde9666f8c58c43666f37fbfe6ddd9f9b6160986fe66da18a3112222821835c021acb5c49fb0770f7debfacdf7ff06cdf6b66ff6f003f31818cd6ce6fed9826840302322701a90e0d619e2478f8f3ff3fb1833b8ee5107e06ff91f63fd91800c41650e612c048750321832863451ddcefdf9b7fcdfff9d7eed3cf9e7bcef1aff9afff6abbc66fbff3fcfb38635fedfdd79afe33f33ffb3b0 else (if i < 9 then 0x3c9aa0f2220c587a31882f07e1d6bbd3a9bb417c4dda9e052eb26ed6064c1cc605c1894346217e156cedadbfff6edfff6fb7edf77fb6f7ff6f6dffed6dff6fefe5b7fedf9b67dbfedbbfdbdb7eda6b6c18d0961140b80a31218c044f30ea1850c578a28e006dbbedb6f36dbf5b7dbf6dff7fddffdfffefbff6dfeff7fffedbb7b3ff5ffdb7f7f66b6db76f6db6fb7edb6db66b6db6f08d0f61ac0e8160188650d1a9358628c63001db5ebbf6bd7d6ff6ffdbeffb7f7f6dfb5dbffedfb7c01bdbd9bfdb6edd6dbb3e6ff9b08e0650d8730211c339188b208682a2cdb37efcd7fe6fbf9aff6f99bbff9ff9dff319ffe6fffb3e0f39e7bbd2035fb5acd978dbf9aff6ffb7d9934d77bbeee7d936b734983c9a70410820410e8960e21c01c6520a0be8c45fc6873aaf5efdf6f777d6bdedfdbedfb55557abfff6fb7ed0e02ffeddacdfdbfedffb4ff6f56db7e6770c983330840f81a8310561c33865045066449054617ebf33ff377f9f6f9bbf9bdbd9feef6f1b19ff7dffc2895483b76eddb28db66efedf6f64dc33df3d8c36d98d4d4d4c92a6a645e009c1010f070041940e118a0a15f16dbdb7db6eddbb5adff5adb6db6ddacdf99b33333336336db6dbb5b666b5ab5b59b6cd0860c404804e0743305c3941dc3efdbfbde9bfb37edf00337effe00e6f666ff6fb0ccc663c11418210961240c482a040bf1233f4ff13a3a007be87b478bfa3a08027487309602318b5919195106fefff3767af7a67e67dfcf1affe6bfed5fffe3ffe6fdf99bff6e70e390d319bfdfe67fdfcf0fffc07afb55f2b8d65baa559d6511c4d40b109211c041a9061ba436865034623285cc78ff03db80003ded1a37c6e3e81fc001b8ee35b8d1a2bf43404806e0182c06d0cc140d620000127693ffefb7e83eff9f7ef011cfedbdfe73ff3023df9e39fd9811e07605807050436242d91983526b167edfb6fbedbff7ff3deff9e6edfeff6ffeeffbff73737ffed9fb0c7d7fb6b5ffed2d637f7dbf9eddb3fb4cfffb67ed86199b77fdee7776cd6dd8d7db4b596ad9a42083601086c482010dc160d418d03a198289ac7000c633fd9c19d8eca20f033f91f63f609800c41650e60cc05890ca18d106ff7f9bded9fce7bb3fff5ed9fd5d8df7fbecfff6b9da66ffbfe7ff3fb6199b3fb5cd6df7fe37ef6cfdaecd6fb37e67b1fff3ec33633ff9313e1ff9f805e8650806382d0081e0e74386506ba06c486347000fffbfdfe7dbfe7dbf9fb6fdff37377fffbbfbf71ffe66cfb6625b5affdad63cdededdb3da61ffdb3ed98663b6efeddddb35b76c696d6b2d5b342190961141b0082820a10189035c17433051358e4f2e9e5c97fa2b80f12dbef92607172259b04e0103c1aca01358618c67f9ec78373b9441f819fc8fb1f61c4c00620b18096b624430650c68801ef000f0000fffffed7 else 0x20d82a636f79018802a637fffb78654f8f707dbaa636eedc3377754c6dfbf6f30dfbeddbaa45a0aad5a21431058730ce82a88c3bccbff9ec37f66fe4646ffb37fedfb7dffff9b7fb7ff9b6b35b977eef36c1882c223441847012868c5808292185ae88c699fe3deedffbcc0f3043b7f798dfc33b5affbff8d0698df06fbebb77f98dc3376b73f1d3f0ead75d31a0d52daa0c6892010334408660b0e834c2fd118b2a7afcdefff37dfff2bd4af5533ff99fd92c73f39dddc905efdbeaad9dc6f7fe6fbfb7faabfce6f99ff33fffff9640d98dc90e7370a1e092124208303826a0d405a310d4828888af8e007e67fffbbbbdde7efef3dbecdff9cf67cf6fb37f6a955dff66b9deed6ff66f6d961a0d556911c1281d828350525d03590e4154462cc777f77f31f6ff31bfc0600fbf31bf6fc33ed7fc6b6835d31a0dab4e3ae873b56abef31b7b7986f6b6bb418d1240d4406a50c21c19e88c4960f787fbeebb35be9760cd6fd803cd666b76060c60a7040432181ae8885f870003cfbbffbf8785557d55dbbf87b7550f3e0000061dbbfc3dbaabb83b7ef87b7eaadc0dc000062892060914301dd0d46a44418c4878000370154155406edaa80000055555000f0306210e1000009076fdf23b7be46f0077fef91bf6f002011549476efe46edc6e2800040000030285035120e9c0c5c0310bf10401007791409f81df22d33780040000183bfe451bc6f83b914cdc6e466e35c128bfe062dc18873870801edf08f7099ba8557fe11bedd400000018046eeeadb81ef099bdbab78336e28a890b761d43418c326fadffb7fdbfeb7fbfdb7ed7dbffededf37f7f3db76fcdb7fedfb76eb6fddbcfbdb6c2187703604c046e8be15e298a1a318b377f9afe6bffbf4cdef33eff31afff35b57fff1fff37bccdffb73871c8698cfe66fcfc301afbfeabe571acb754ab3aca2380b108e07c078051221c3928610d4623285cc737f77fdbbffeb7df7eb5b6fedfb76b7fe6fbeccccdeddadef36dfdbf6ed6d9bdfeb55acd6b3330ff3301402600f80035a2403705f03a1982a2d3499ac956966b1c18599acd259614cc1894546306478a455315ba800000062b756c08aaaa0a0000005781843063086d76cdbfffdbb7ffefffafbbffb6f7ffb7f6dfecdfeffb7efd36ffdbfef5b6fb7b7db76fedbdb2cdb06342581d02605c0518b10a18c05870dd28630c57c78c6e657e3edff61ef6dfedffccffdfffd81fc163edffecdcd9d85f998ae14410d84703e048042930e60412c18a318d000b6dbf6ff7f86d436fbfb6fbed0dad7fdb55ad0dbffdb7edadf687755755da1b6fedbf6dadf6b6e86def5bded6deeedade03ccc00c508a040c287230e0617d05873415149cbf8c7d99dcb2f2c5b7bffccb7ec83e0e62dfb3166cd876638864))))
def level12 : Packing := (263,3,8,0,0,17,1,nd12)
def nd13 (i : Nat) : Nat := 0x1b3cffcc6dffdfe1e60f0636feff6fe19ffe36b5ff6834c6e0dbbb4c6dfbdbf0cdfb5b98dbef6f986fb5b76f98da0d5ab6b4629208c04e89047230d70b852463030f84c098dc58aa131fedd40f8000030098ff6ead804c6f6eade0cde0600061240d4660d1a31866db6fefdb6fbfb6eff6ddff6edad7ffb7f5fff7dad6dbfff6dffff6fb76b7e7fed99ffd9999b7bf6f6ed6def66dbfdb6ffb6fb76b6cdedafeb56b6b36dad6cfdb6cccc636684222048280a061c8e218c5250bc1a32151edff6dbf7f6db7ffb6fffeabf5adbbb6efdbad6df7db7dff6faaddbf9ffb667ff64ccdbfdfdbfd5bb6fbfd9b7bdb7bf6f5addbd9bdb77edd776dd9b76ddb3fb65998c6cd0944c05021e858c4d69047231070a8d1b27fe636fbfe636efdb840c6dbfdbedc7ff1b5afed68d31bdb8dbded31b6fdbedccdb5bc2600031b5a66ad5b418832130880c39250bc197d1916db6dbedb6fff6dfffdb776ddfeddb56d7f6b5b77ff6eeedadf3f6ccffb33336dbdf6f6ed6ddecdb7fedb7fb6ddadbb37b6bfb6b6aacdad6cdf7ed999b18d9b4251208434061c0c050c616904642a3430c7f30398dc2635a1f98db7681e000600600f98db76b601b1ad5686cd030018608944218028f460c61db6dbdfb6dbffb6fffdb776ddeddb56d7b5adb7fdb6ffdb6ed6fcfed99feccccdbefdbeddadbefb36ef6eeedadd9bb6bdadaad66db56cfdb33318db6684a26108880a04630b35a39190a8ce7ad40a897f061d3a6256000ffeedffd93ffc0fff71ffec3ffd47ffa0fff21
def level13 : Packing := (8,2,7,0,0,12,1,nd13)
def p3853i6 (i : Nat) : Nat := 0x9
def p3853i7 (i : Nat) : Nat := 0x201d
def p3853i8 (i : Nat) : Nat := 0x230091006b0040f2
def p3853i9 (i : Nat) : Nat := 0x923009000718000656d0750eb0b324417000a05111110400d02000b13203501b0a00630fd04186955616000151d12b0800091590ce0de14008a01170d
def p3853i10 (i : Nat) : Nat := 0x542ea03800003100606cc0bea0419069303f6b2d0000509b0050e0406011107900000096a60e00002619a1935abf308c80afe02740df606fe09fc0d3fb2fa16430355192c0b602d170c9b01d305b6198d05ae00d0000219992c00000c07a603d30b900000000402d0000a025805f40cfe01b824db0d700000000808fe00300007084006400000000b2c4b0a31653000070a60000c05c7036e621e03e90a94092d60397bf11b500009061b09c301e50c61013a0d53090c03c406ac0146037d04eb06d10b40000c61c0000a0c732c85103205720c3260200000000b051216250dc0086018c5adcd2cd40ca6476f167507f5080b0d1c0c43046901900656028f0a7c0db700f0000f006008bc6b40191414af0b300000000301792dce60d617762c540ba60cb2052c721e03230b502c2e010c0831005008a3172942d9007e16d924ef0b09ab6a2dad020b09951a0a249b62700004097742fb19048770000004d07b6160b92b06009605db7bc302b708d000082cf80ce20ad509dc0de30a2a0c29252901fb0626154918632b2609a6015b24f92c6101660d40000504c4453f0a4302f6022900150399000a0b8900890a0504fc2c3b19750043712667630c02187d146401c418511266073a08850da600ecad7317ac125907ba0cd3071a0ab2248b2b630bba0a5707c1608c053f05e5029a08e70d90030d0983548807ef07750dd907d606b000080a15058b03b70b1316fc0d8c0ccb066702c80d24085b012e69cd0d070c1208741a8109350aaf02ea0ac003331a940310000f00ce0597026e09ec03a52d60000b149d09402c90034e61d20821171606ea07810422354f021c6b0160f4044660c8056e048600ac0bc661a204930896023c0d690a8f1b3000000000000616030c8009110748095e24b0000e1758072c16c0000f0ae0000c07551020000504b000000008054b0b7307045c5c606d2470000c02a661b000050437047a01805b58002f068e06050246153c06320bf00bd3110c0c50000400b9878025157dc0000c055cb2e0000a04a701a104552501076000000008148908160b222c1e60585b3c067c14c05021c00000006620e03000503090803150c0e020101590006000000490807120920000b02010004083c1000050105000106030d1a0b0c28022d02080040000060010d00010601020003000002030009090c0501035f0000121a000011000301010500070401002f00000c030000085a80
def p3853i11 (i : Nat) : Nat := (if i < 3 then (if i < 1 then 0xe9b3876e9b804d85007bd24ea288a81840e02ba4084f6ce8841d8b009fa08a6c0fecc586d0444b351b849b4057d5823251734609e041f72031aa6314608260178a82d4a00ec00002c0ba18248907aec0495418d80000b635de51af0102f83f2224e5407ec0000782b2d03d2a0bbe21a8c8084a60d595113d81d8819c0000000000c53f5806700001003d800005000e3059200000000000000115daa813000002306700001a6a31c1acd83046003760e3200608000020090a0b9fc5b5911fc508caa0e16c14ff0244d07d0ae1a5405d28354307ca402acc0bbd8a7c614c548885c148583c070170e106800007838fa07918036ac085803ebca6ce20950000020b3400000a11555943900afa03f320e400000203477059ce0d81816c7043cc060a8c0e4000078351301540000044462010200001200f00000149080060540041c56810315100db229e1814a413740074960ec8020014044001f1000c0a0e1d85802151f820661101858140503808280100004000a0000400040000400890102c160600020040000080000000008080301814040e04008200005004020c0d00c0402018005816018600400010501406048000800018540013010342601028d414000302c58000e84400100b8b82a060901c0c110004002010000000200180c0c100180404000101400000582c26040381c0c050083c000807134520702870003d03004282c01010020000014201901078081d058240013090040a070c0803403088040001048000a070200422010004c040204808080301844040000008021d0082008040003c0e5c0001806000400800080c8000018050142800040780000020180e0806064122c108540000050281810108e43e34038000e0303020080c0189408010300c0400000180a00020dc5403028682c44110a40c0b048201407010080e0409840160500018123f178180004048040e050400c190901834260a0183808050080c00000f8000401000100000000014203190543e04128040c01008883603098000a01000000c000d02c020002800220005130761a120001e5005000161c0287000020a89c1a08021ec1003028000e0c07010040001810221901830b00d00830184a0b80c000002814280000844060f0000892110291822070003c060101044040a0000012010086802010682c100c008082405028100025008180c000000046010680000250200804240001c10110101414020d80c300f0881c06030301c00130801402190280408001700c00102a8200001000002a05020000400000000424010080e000b04414040000034000100004000283046040380400020304000000b864003209000000204808200300034041304000000913000023200000004c0000818000000002000109438160184c0021290205e06018080a030000c2a2b else (if i < 2 then 0xf2accb381ef2bc0057343a1184c5aa2820ef03e51512485af200454049ee0b12004288ac536113807980a1950307e61f5c2a33c00590431d047940b6f9dfa388f6f04d9004358081e03ef80424ec32cc237230da707386efa6414e601a24033f010bf8129f003a20817010010221c0314802b78cbba44b9080b0b07e36e26b9cfb383f48003eef0de8003500c7703280ef95c54f09429200bbc108400000000040349ec049807ae8a3fe80aca083f4199381c147807e0f4ac1a4a84168923262a0e05c08021a403bda1165058a13c73304938015dc0b1903ccd17d02093802171006ca0368204b500c568077e62fc20be2493a10ad3461b08ef2c00d088abfb041400502c050580bd005f600002419180000503edc052601b9381c2d01de40e64d858103bf8015da4d4180eeb819a902d9a03cd81910046b404802116fdc31f81161611b8eb4e40ffbbc32b04a460572d07fc3178428ca8066e8108d01d38165d4c6f9815ac030e4106380961c08bf03cd4451b8079541989828bb077c00000c091e8af7d05568100b8119f33b77604800000000000218306cae04c5804dd808df70f0e04261801d006ad02fe4889602052a1a7306c7206ab860563891e916e00001c9b9a82e01062e60314000040428c079c62c6d8435281db907d4e11a881bb7b8da2165e20957001ae83b8e08b1408679870519ac06079801c1020c2829d500c8e10b11e06980723089e20dc60535b0a6de0251e0e7b404e30457f027e80ecf58d8e81fe106afac05099d2a009e81164ac384000050075477f4011e840d5902d07012b0ca7a80e858348d03f94075ec0c39b0d3a066c00003580e9802d26074a0fb2ad46bb3b0c03b380889c566103168076da0d98806640350216bf2006805724044bc03b80c0448937a8be700000204dd90e2c8268000014080a19c01140cf716e0084385a8a0270420b2600135dfe30ae71159a20935c81e88041101140000018b35813c6285d026fb4dd44d35d10229a0f8f9c52a80fe00001002891c4ca031cf054900e4580e5a80b78807b410226ce308916d122540f700000102da026d7cc163ac6b8817040219c50b100b140296000df20d6dc230502089022620a80000000000d03de000000000019a6707f1ce8758592909b1515fc60554d0d34831f7a7c35671fc1def8437ca6e22e692e9a2183354601ca0f06ca184005230512969e78111e827e1069be0f84000008ad7e62d4c0d6958e500000713b8208fc804353018a05aacc3724001a8262305d3804aa19bf00074a013ac26f3c175c832900001e2a2ac1ef8000000001e0e74000011ba100001211ce80674b1d212855c1204dc1420154008914c4dd413e80000515d26c1ca40607000a407c1604d7c1512011ec00f08514a806c00000700488ed1cc068180c63053cac1dd4140781c else 0x3fd418000000902594039e1e1411056b74436e56ac9e300000a06a48cebd00d4d038200000e0aa441583018bf00b0c0d8a405a00000220b580564407a0000000000869f04069800006045e0000000001b381a1520000000000583a190060500e400007b01660514aea7b800100000f67244c455811460051000018096ac07bdb0d60000020a4658c3381808036380486d8650b03100001ce97d41a5481507151680b09ec49c31a6801d42059a4233982aa00000000034097102c100000e0376802d000003277eec46000006819600001e0311c1c6d821b2050d6059e40dfb81e7184ea82b62c1797007fb13c2a2d33c1dc80a75406f260e571e39000007172d0113a113fb027c9783b411c800001014800000e111fd816d000d577c6e0eb9c179d013ee027aa055c423263848205475016880d6e03e490372c0f9c000068373a1007400e681b50845416071f6a33c1c922b5ee06cf2edb70226e011000840c09e709baa80d4877944036cc14968456d05f34e808000008032306ef04f806cd310073a078f6c04109a4e8164a607b0f082c0c8c81ba0000000000985680000606fa366b0202df8482a62d1c2df8000069204908cd005cac2206315f378dd406220446e3b76f91700000081f4c82de603c3a0b65c937783bc976c84c0a80000281f12602e0000201c48000082792806ba813521205e0625608e8406ae81be931aee08f529afc8b27104e560eacdc15900e830700cc1fcc21f380fbc14fae11a0a5400844a5006ce06080000282300000000003d866380424072ef50c9a9af38012207536012e19d95039fc04b28051c99d9901f7100a96c366806548a9da04eb54dd30477d00d2d05b9a10af45bfa025e10534c2a196a23481dfa02a7cc0cc00005b0d0d1050023dfc0b0b024bc14f204f02c1bfd80839084b80abf58879843a7113502e61c0b000000e069fe68a0819e0d3c6000000000141b80000007131a0a6c019680000056a3c2c75c138bc109e054c0000140924d1b58014e8ccf301c9d8327908bd00695c22330238028bb5517b0a2f08442f014640ba98d1001a2ba282b768b7453463b5f7161e80751012bb015af06f462e6691d7f01a0d004600b231818750e2b088a011c5c11b4011bf1655568a7aa2eb00316072c00003d096139ed31685604ec80d1888dd36051e1174c5904bb6a802bfe2c7945713b34f30495a0b4901a70017e00777021035db3cb8e29a77f60dbf5809c01c8208f7c0244c21f80000f05970004681d81891e26180a06ca2ce2d02eee08b4c01f3401171431e03b416231823edbaa8702dfa080f0105f8333701c400c2c8a1b98025a016760b8f462be03a6706c2c1214401f90267f12ea00241c02fc04104159fa053b989270186a712a20958c1628bbe4e07b3609d1161f8010e003c1a11ff810648bb0e01)) else (if i < 4 then 0x8e5b0181205d9010c1c00ad0b33f03b02071b00b5531209621bc0d10401000000631da405e040e55803460824003b898d169438814c780e6800004026e5040f6101558158b0c7f031aa85525d926819773210000e000f2182bbc034dc24fbc065b8260e78d3686b0c12eb035c761baae30cd1148b023120b760bd8c9a8d08a4202b0e0c94800a43c7ff11fec2788007c60469d10e4e0158005da802af0152c0df0d804880176807d600a249b3c018f546962c0358a324837e10294e10e4dc59d8324205af60c20814985a8144459e0185010b903f9a0677008deddb4401bb16229a0f9b986880ac15a0b00000000be98a6c00001c43880000000001475de0d1bc9b0180eb2028c40fdfd84d48334504d242e0301bda80a4116c600003de2ec5a7fb0270a03c000000bc0b50698e11dd015680000da87000371846c800007009a000000000782cf30595007d6d80f48099312814067a00fa5813af788c003b7c11a30229175006c08ac0890b1405007b20ad8c163a30aa0057d02b84008213090b67ecc0d00ca22dbc3f400934010fc06b98b8ee030be11fac21b001303043aa014040c84817cc0869e0db8415e1831d502d600d7741ac30341f01b30001ed8a25ba607078800a1201ec03c11407fae2b2a005f0030cd03f120a9701ba28328e60e84039809ef0006b3029fe0a878241a82452b36fe0a60000070414f03db607f61dfe8802ee075960850c027e0080c009d80f5bd5b0a91fe70234e071281950842d41589405c5c57300000d28b2409ea01c3401182127ea013081468036b4438f751b2de1c502e6608f3c0f56c2154b874c60d1a075b423600000e05cbe05e400003b082107a3e05580000181b6e718060e9c040638449400778c38c000060974b086a0ef35c0c2703c900019601a5c0004005e000000000049a280000d062600003401780000e03dd6026344233039b7001e00001dddf5b89f907288034680f18808120870e66de09aaa03186081820acec15ce01cd2043cac00b81ff4021c226e5a041bc0ce80000000014023f40708b3f834386ee1d681b24d373e768181035c4d3033b5c01c9e037c057c4543f8286962a1d8046180fd404bfe0716c112e3026000014cee4000000000e0039e02f2c57988406a075f05096053d1011fe020000002023b7808ba03e7e1212056f000000000142c5800007b1638047740db44072880fab01f80000101c5091b3000004689480e180152000004c59f006400000000000000169a800000908a060970000000000d08c5e096e19c180000b06f000000ea269404000001211d305d0b00b600000000029884eb0eb5433842e7480e04542700000000028080e3148800b66e83541f85038ec0602a0c9841ff80000d585c80b8840b4c02e100000000030459802610000120164000000000d162580 else (if i < 5 then 0x8478d0867ac03c00000118e0000160c78181bd0ae5c0502004d31a04883d3a032a00000dc4f230aea0484a038281e5e041ba044f806de804a4017300001cc0a400003840900000e0f1400000000000000000028168d04410000000003417b800000000000000c19c082c600000000010099483690101200000c0a0d8a7be04de2014c404480000f05fe0000000004d4288784f40f6a583c311b500001cc708c0e908008f0142a00a6c1c478016507b600002822600000e080701044401f3820df04ee60fe95821c8062a039860416c091494771021e0063300a1b02760450f650a3c16ff391ac646be0cf50116e81073037a623d58010ab90c00001802fe81324894b1765eb226041bafa279a070660cadc178702f4f083fa51b6802e102249006e4084f45f2582a78028bc0d5541a13841580746c04a7c236c812f602dbc2bca8085082b7e080980ff2c56c80000e61f100fd7409580000404c680fcc018500000c012622fadd8a3c0343a7661c0258811080000305c820065c1da083ba3008100309c0d99009720750000011cae68018071f6a0a3c00000000000000ec174c03ef0108702eaa0a31417f330a9e154f6c0979876db0de9083bb46cf80d800000d08e0eed4c806b7830600000c49c2400289451e02f4e0e888009c301ca044d80b58809c800009a7bc805ba5874f845c00000d6a1ec5cad0079e605c00002c544c3232306bde08d5058173958b004f401e8c09370868504cda05a201901b1ec9052fe052e00470b0049778200cea5014fbc6ca151e00003d8cf80000e0193d4d844181f82e8a231e00a568071abbf2405baa0a1fd8d5d8452000004033cc142f53750000000000408888aeb003aa10d334025601b50000140eb40000630e2860100000000005827331695e0ab800006042200000e02a300166033f447514081b1482d83dd5024fac36e1c2f8b00a7082f80ea9c1db9814cd02850c64d18b6e89bbe0057208aa882c284635083d80da141e3684260000000beb4188083099080fe50cd007480000200c7b6708003328144870d7f00926caf882ede03d1e228f45987316c3037904d0dc4eda39191022aec64a419c9043b9003b20a228120800003070320471415c389af926de605ec00004215f5068ae020a015e98423b08a3401bb8066f9353ea894a0cdd41fb1030f8603e000020123d83a5f788f60480000070311516c2000000000280ac000006100740c7280b1560320c1b000000000000001c0157008e80000d014ca0ac7d8e64b10510306a0cf8c425981af6287582be50938918e0f161800a0f056898a81c14c980e1d8a3c803196a86e4c6b54123782f5400d0ac21c00006426e7323c0000251d07014de6157eed30c1afe5a8a500fd02b7501158015e000c0c0547c156602fdc14846094329a6f80a5506ac42ddad else 0xa1093d8358000010569211d40000203a0f62dda509ea938d8220000000000000007b91b90326a0ed7d876203cfe15ec5638300dc502437045d60fb480f5901993438c6085942403028eb0832c0cba6d3e80000104dad014c00001826ba04ff20804449ec840e261e5889f0c169db22246225ac443586ba81a70416d2021ec0bb70b15f764fa242000000024c961a5e0e600000199fdc039200002d9371da86f81c52e22ec099f036c707a84026a85840086130587001c401e8700c30000060c348004a089c50111a0110000070321503c4000010141001fa284e340944800f4820040716c02e780f81032f20408403c8c21edd3519042ad26d81867d83307035800000c019e80472082600000000075a2200000b01600000000002718b822d844d4c0c2e085a440a6440494d35c20697403b2c4cef8119f34faa0b300000082cd60708608b1006f08353014fe82d1d80c4e81eae08526107145f2db8e3504f7a2b03c05ab846f501e3c073c81961045f934f0602c81dabe382510864c0663c16018833908f860afd013280000b0473a0f0fc0e3c142f9043fa103d40b280000548b074d1781f10023ed2856002b581e50b0e82032482d88000050231e03a2a0aa380aed813620785406a0c023481eca00038c6a90013782fc000000000000002537296243001979c38c)))
def p3853i12 (i : Nat) : Nat := (if i < 5 then (if i < 2 then (if i < 1 then 0x404030da744000000183215018201a080a8400608270101a2b0102c029a04804061602028004b0189002100a878420106801ec170000c10090680c020e00000061300818280428044105f038000e05219f40400068001408008000601028001119018581a030003c060f0188804081a010020a038001a0c018102005000583e0422034003f438500c000d00c100001000bc0104864240204800000f030b00e020384c04010180000030a80000770100004180008800010080c420201800000000044000802000061c01804000a021600000010001e00018786e08208000019020140004038304042108040a080309808450b80074070b80008050481448bb100103000040880c010400810000b03c0200020200a020382c020500b9036000186402001e1600006008140415020000003038180c2500084184500804001d0685802050001006074900000030000800000506838010a81014011a0a0040f008a0041100abc00040300c180f0880c0005000100a06018244601008040e5100004020004888280100024220307a4c08080881400071e00010070080c0819000e01c1913800021101000020402078000015804220e011c97200008042c0a020951606090700200000140c0103810560d048000009018cc3a010102450020384808280401c7016000007c1b2505438000300c1203000003001000b4001e0007c1a000881810150387010080700c029700800000703804320b0602c58cd000192c091811400010500c000001c50020304024060c0004808250f010185b0c80c180e0080008053a8180014008003800030100200028001a000902c002e0480c00060483c7e9f000005259008042e000886008090100866000400800280201c0004000240c1f018240801068101a07049100200070043e040500404170d84050000002406000000c28031e000240b4d91400060301c14090f014041e2882418020181424000d00c08010411c30040600c000001084020e00008160b0000c0004059342a09000001202068081605060180000000082e080000c28033680818290801c3e4c228001a081a8ac020802810d406128240000000041400000040e020080c0401098041c002b880021d000000602000680a120f82c040a0200c14230180c4e05140700c0000000000301044021a01068380404bdc32020304852050109c040a0480c5800020003a00068084818100080000002ec04331c004143c013d000070300418050084806000402c6802020201200008d80c6f0183c021a000140426000103a23001584a2700004000c0101410060000c04040c8007c0002144140f11098060601814020d068107e0a1f0000202018080402060002e050505c12070202406190180004000a038020a100182808138d41808008000a000581c0c01008000004 else 0x2542f97d829200c24006065ce5df8488700e0ae86166742ec80747808c660ff7c28ff09e4418d761167c6d3884884b5c421c82c1ef9009000f39026795a2f68cbfc0842214f8c246c8680d0297ad5928232903b4f0894cfd585f873b104c06f6609b98078634cbf6006a0d10d96f10383f65e6a1727916fb82a8405c8e0d3d437e1057d0063ca0ad58315b821f40d0de10488413f3014f0917605b8190b4017d804ce215c5012b686de2201d61c14809de8c3830b06a00129889b0535467f1c00e78120e8219a1b84b6e56c89028898703d020ecec059105af2162b749c5d9b91072a304e180e908165b058c40119e0eea4321480d2008a00dea7865f402b0d2d4bce47081d970784808a7c149585b80012316538c00864281cb1c886114ccdcc40acd82e107e96e1b8c037d19652509e2cde3c426df87581787e00e94c2bc38234a63370046d8007104a2300d6619e5409ef821c76ada212e4c3da001b1801df010ef44d1382a67029a81021879f28585705ce6eb500baf182bbe0bef4031e4ae8a06fdf6d54c03c68508f0772a028401be480e335a2ae0497a002ec36788362a082e610921ee540b6e117e02196fc637a0215b0a62d5715c2ca2001570d9ce0ce603cd286fe70f33a14bd81b2ab79b60c074193a85ac88604975634093643835322a22574e267d9bd2f8773d03341503b8d6ce8681e054ac017d0784091e76257800d8782be40505614f9d45cd1918c8037b1413af0531b34ebf1e908920134480df0171f705e18313c410975723f0b6cc0a0d010810306869cde11581e0b4040780c1440279c03ac311c62e42a0d910513b05a510067405fb408348654261af607e8809ac07a4a0a28ab5264121a0484b0747a85c047cf687772072e2125ac23848358a3aa2001bc420615bc0b082984f3b0663c849720bd9c0f709b341254100244a12f180d010031c0b9ca1a2e85efb86f77620585c03dea4f176d16b4d00f1ec3cfc043d5019b009508cfc2bf8246a8222eff8144505de22ebfefc208094d070b8175002a9403ad8dd4aeae1540ce243a49328490d696d1e841cb086e77093b618f802b7f03513198c8120b0365fb1aa9048da0819804d705bdfaf052071140aa780f910827215a4da343062cc0d3600f6dc38fc8646709d58027000574043870a7aa11ffdc2e3872ef065ee2c50081c180001c1301810181c0d9401e4e0509c280000a8c0200010208e020002800ec0480c0802000040210030381e06000000c00030385c3f01904000a030000c11030d8000000040000200004b601020000d5a000180a020000408460a834000e050000000010f01009438080410022f402000080c00040700c1c0900c003e02040281a2e0080000160100c581e020000614020281e060000400071002434070482c020a058000e010003402000300) else (if i < 3 then 0x76382f46b0d90070fc157cc36079714c607a20684c3be800002094d806304320b35a2771d0250cc4173407b5000000311b054fe073320ce4c7526c61f9853770a141500a5abaf965e7028a411f80000330c79078be0c12c3b00000050e9a4efd21bcafb2299642780b02c29c98a33d02d90c5d1801f9406ec60b041e6042566822ce17a48f94b0607803c3514f520973c30b65429905d522a28820180000606ba009d0000050984c61b44700dc20ce82d29ae406102dc00e68a2ed0cbc0052359e100000769c6000018284e3120119260000098e780000b0dedcfb3bc05d33214f08d84f4e0000070b8100001200d4c125506ab000018009a0135e03e6709c00000182ad304da90efc0000381ca80000000016c0821aa84a22490c8e0c7eb4258584f2b1717a13b4821890226403bd412efc4fa70cc1f0171cb00d4045e01fe40742000024273bca2f4163e0000203700000060c0c001b3020680000d091300f44000000c29ea2e000001c583d8796c6f6360a300bba284d066386750fdc2872837d0000162505e95d606e840b78a059d42acab56b8813d007c40000201fbb07cb20c9c000068393e6a7b202de1e38800006083e0000080fe001c8417d102208000000000115c5a1406416ac86c5e00f1418f4434ec81782039640e380000305d86182d206048343a0746272926307700f8106bf805172d1918060384ff20ba4000031e08c856b00001a0d1dc5d8301610000002c5ec348d8185017f660826599960094335bee0717ac42e174a135b155c3a5927403a9406f94db240000194340000080fd0000028434506f2d5cc39dc308baf30ef28505a818a88bd5b134d41c8fc5fd0000097dc70117982af0be28300daa04bbd8b770721a18b8c099400c8105ca60d08ef81d023380000000000000280f658528164b200002c26a801da009b8000015afe800fa30ea6a1ca780e79016b306d201cc0c4ded00a700c399566541f4f80c9c0920812d000001355ec09bee1882c14ae83b9fb0e4c038745ab500e030de16c9d302a3e3169c0f56ea72201e1485c31060e6d22505f643f64b086c0f87900b82010127838c15d70283c964500000c1a9a5fce000009668ee044d0137b829ef173c6000d6b0f7836800001816d7c0a9b84d700001018c39a37011750000000002095a918c490ccba0fc4000070560000010033bc2e98b24770e594063a00858000000001ce329c1ba6bfb1b09b02c71882b900000e191362f982ea720c57f08dec19b54079b000571beb61b4781b3986bd60ecd2c10e19a51000210c5e6031719c6db23fa7391a11c75ecf0bafc119c1a36f28bac70b9da028ec146802e6dbbd9018c581aa9c4401033f805660000002b76018f0000101c3f9ee8f8511a0b8d0f05c0000702fa200fdc1474dcbbc441e6adfb20a3d02c958187203 else (if i < 4 then 0x535652005b4cba6c21b90fa82035c00fde82d9e84690000048b7a81c803e76a0212000018162e031820b1f41102d845c84b54066f0074f03a8105cc704ba802a0c6210870d8087de074602f17807436052a0ef9065c78278e1bdd2fe40c2f5f30b770270050e7c167b0c9ee01990c034461d7876cf02c6c122841b7800004046140b6d003e4829d2048bc002000003be58000010cbc6aa08d2f5216307c1b90586ff0534c05716165b01adf0385f08478e9aec1cc804f5001d6e0e32c121500a60036f218ba422ad38619051a000008114104e85066682c749de29840fc13402c549019938112e0906360d0402752ecf10e336106d8c567941000001e082c0000381449616649cf581fcd0e25116e720fd90179b04b3322d7c1294c392e8355c0429a1d2b5a01d31d5d0e90804c800000000090a7463418000028d4d00001ec7bb4235ed711e02606d69541118000030585e1d7a0316800006600ccc36f80ab1bf4360d89e0194c07900000a012e000000bbd183da30eb5ce61c6b84e81ebc0002000015b0688581000000000000004057f00000000025814707870000141957c0fcd026300001c08965c1c9831620ed400003014be8bad203e76023c0000287ad0000000000c13e0b1969b504000000000438e7f622400001831bc32d7a7169ac5d80000239c97636342f5b879fb057b4178b0287801eb4307c1ae4281d2d01ad481bb4040a218ea1ab3585abc0b4175c70983ec84449180ce1ebac4e6d00fef2e5541d7102cadbbdfc66028e592c1a2d03a2475640000343d8731b60768000002411e68141d0615a073743ced86f2a61cfc015c0072e806980123a18a94f9f0bc2f00555c12e245e34061be61b00168ac0871824f70cc2e1a7842fe1bb0b96495468aa426ef83c6f057c60987c15080892100848019d8638b86784026e4ebe981ff607595097bcf92ec3c4c850dd047da03d48148004935632e808cb4d6ec04d6602c040554e00ca0548aae1781703402b5200990d9803e8f854f686dc60984a1bb18622581b4507d1e31a3e8b653970c0a5d418e00b89d83b807806c166c982870ba6d00e0804f9da3da8448006ac40b450275f81a700001e064c1201e002b57f4ec5d4882e7b80ca5025a20bb92b8440512d03c701ce482e268221d18b220c2f8333f850fd034b4338542ff000006622f2e0a2027e80000000014fa99c930fb4c5000000f0c5430638305e619901575cb7d50ca0d08d5c1b2ac3300b012d60ca62ccec0908000053a90e0fbfd2014119b0000000002c1b91356c4097d645c49801296e92ac1680e2fc01940000205d08068c00001842f0000001a66ed17185cb00001a273f1171086a2b0ea46c465587d20b7be08ef0155d6b9e70bcb00132c1cd002bf685441b807e1a0d833f3856640563b50f203140000090e4d20 else 0x5415b1342807590515201461094e00cd3c15923efbf60d7430ee41e9c00e3b06bfe0276421fe0617a01b1a386587c71087af06f54032c0000786d83004800003cd173962c234e7ec3fac20ee32adf75fe059464014900d580ec3ade7000007849850d42400f501cf20611419cfd50dadacdd973dc0353765c1c9b1a116d000012c3e140730000000000000000000700926059a000002ba65027fb170461e8b02653dada00000e3ea640f78000030eda09530000000000965c580b07c140b33ac9027ea309f827d107864090ca0d004240f85ff6015800003c27b78025b7e9c00000408550b513138b00707429c00000605c0e1dae54b80000000001209facbb1e39433073a00000083700044c03c141a14000058d50c0cc840a714a14406ea0000000003d8b8002d9a68f8227a00000584ba50c650cba9049a00000d185400000c08b000000000000000400faa2298625101e5d007398c17a0f640c973823dc3092e6309b50348533901890008aec1cb45ca804e6f11473100cc261fd74ee16b8000000000750d392e304c02d805578c37b08bbe084e4171ab96e00001819afea18206d9c45b240571d97f5060e30c2041dbdc020405d0408c3b68c2849188055b282aed4a580439825b601dd033489ef7c0251f7cdc6096ac1f658336f08e6000039a5e2b1330003d63371c061f0007e58230065bd8b0208c740086e101581976c1700000000000d8b88021e1024c410d400003b66d8014240902c398f07320000161bc4868810b7f90a9d41a3b0208c80fc000000000045aec8357d0a05ed57e9a43d8f2be0b4860c8a8377000000000162c69992a80000000000079d416a382ec00001811b800005a2d8a03160000301420572b40e7d005798352305e610399a19c583bd0000067d7e8026d05d5412bd46a994304c41a85815b30d6585de1c1f1303290000022df80000487b35ac150086c9864d841040bd4a1a5b295c00000a050e000004013904457025643236804b280bb301b4004a94643882c9f0e2582ec800002b1d8a4a942f4c5c0ea800002a20400002802a18516e093420042516e085dac0f2b40496c30f0850840eec0000109ffb2528903100000000000014cc0d4600000000000000000016158400000000000000000000000000003063b2f06f07445bd7676aab28a9400003821700000012c6431e38645778486ea4cc1388000050d2a0000000000000000000c18fe46097516f0000101367c02f5b0a7d0be200003dcc268577628600000000007026db02e961e50d0f3a940200000616e1836921d4e80eff8c27800007844ee0ccc0000201e040bd96020a01ca19aaa5826200000cf01800000845f87e17e18d8813d00558e68cec0f3b40506869ff0b31824cccd6ae047251bba407d543c5a347000000009ef41406800c202e5624e80))) else (if i < 7 then (if i < 6 then 0x7bbfa03dc81baa92b6507008127cc2c9a85b7160e8ee4d058d758420f0aed4fdf400005d715e0cac00002c00ee071ce13c40000040284006a80ef6c03d29ed9db0aa9084ae0b8800c35bd92e064880a39813ac04af50c73c1c9c00000000000000f4aed98460000010e774c26f006400b6f50540804e51f2e2800f000000c29a186b78d62cb6de00003042f005f64076ea11d9516ed8150f01043434842d35831b40a8c000020274881e1919c60000000007805af5e7e00001c106c01a622192806b1409225a331095a4f965c1f1c823f80dcc208c48681217591037be2d1701d81039af001420c3f02fd48331a759b2c221c2c3bb442d068c65cc0827a20bfd207974018900904b19a10356800689ed15822e70111e3aaa02010858e000c92d534000063b590000125de618e3a035e07e89e06bc4b936d4398087461248484f403a8e0e1d65b480325d85305083c00001c37c0000000000211d22ba498623c0daae193705d70869a104a4c059a40430000050e23e0dc00000006f400001afa90c1a448320f0e808858ec52630ba0d0f02403b411320000017a2420d2f075b33f93f09de55ccf82f1a8134da57a20f372a0c783d9b0798cc9d40b8d5317773a976ecd09bc89053270bbe0182f403cdbb4ae0754c0fee436d783c946691d022ec12fd066f76236e1d0d811ee085cb02ece036ec266331b4102ff006ff039ab875dd0032e16208127300fd60097cfbe9d857507b140699804c40000006ae16ae5a03a7c5b8b020201a45833b8c19580000f063ee1334c9df1003421cd000000415b485260077b006d681de38b4af72cfe315903b4e0118a0e75614f24104302049092a6149000003023960f52c167541fd2819f60515013035e1f184fb5045b6ccc4d9720b544a170ead577dd8458707f19cba16aa06529052200e4980cc0d61d805366626b014325e24c0500e11dde0ebec3ab39727679834e2cdc157e820060990804f243c970515a0f4280f1100e4da1cfd0f5801a3105af5b9200a81f20fb8045648247209ee00001c601c1773a6aade189b81f200000e0dea000028687101b380dde00003071338cb01018debc8192a743c428014ba233d406fc01d420bdd4086203c5706a9a03c8e030400004854da0d6360748000000000c62a8600351936e808390d736072bddfe78c5540206211f4000060767a08a800002c3dbf3a03301c8607b7d8d2f862587b03a05380000232c23283160bae5d5b98286a066aed01b8518b81f430b51d50a241768032d60b5c60e4902cb88191407d6000005fcfa87a6d18a0015cd006f5026070ab986846c0805b473103cd6ef381b32e091670f1c000028324086c2b7e31e02c6832928111105f081bfe8b7f784669033840d731824000007070da0c8403001008133a518fd3218b3000000000115ce01d9e2 else 0x661dd7804983f9bd0dd36270700ce9141da0218c5d4d0328e020fa0b1720c5f4380882f6d0c9e002d2411af03bf6006c61e00002500279a08f38ecd6863850084762e6a0ed4c254306757002c808bc038408c8bd0149e0bf0000040f9c10535204ea997280000c17d5c0f78000000000b06dba10ac0000682dd000016d46400000074ca125f4065198e88000060ebe0000000002865f00001409a70113a88b8b0948e22bd82076222e90af4e01c503c8f02fb00000617d6834150107a6a0f00868000000000000008127b4aa4a14370000000003c3261229ba021f6c090c22b8000000000e085800005038a26ae3816c482a02ba6d718d8e01edc612b02fe417a621b5dc339a84e58193be2ec5035f7997020686c16e903a2a86eb3b5bfe0c4312a8501a4a037922f618c5c280d7d0f050508a811235898b0bc381ebf0221d3e70d04ed403ab9d84e0182b0b3e416011d7ea02a380525e20c202e47874e668fa206b55865482e9f0659a02cfc0c18bda030059c1e4f41fc4048590a85212df18c3e88c2860f001463c0aef80b61b4c8c0413daa1b8c9c40d7801e978234287624ae4c63e48c08478e1ad35b92fda9aa154057060e6d43af1ec497867670f46c0a4d0058405bbc023c868240172e8b6530d5e017ccdab3cd41e9145340470c2e898051560efb45c61a90780dddac512e5fc00000859e01f4dc049dc17ee055120c3495c33034c6bb16000006c660dee5800005099e00000000023e95d07ba014ec1d3eb03f370aa4e119000000044d000000f0e2d8d59867d91e414eaf440568811af2b8b42e5c00000000000001206da585f70bc2c16c80000283d3f819b21928619b980268000060ada00000000013013c0dc4000000000331679090fee9d80000006b3a04a041866c2766347fa069400002435684970000010cf78000000000f0a5a40bd4000009a3060f40e0bdc8b9e3014002c7ecca0d191f788f45015e00002002c283ac0000000000c859c8b96f00c7e18561c415868920f0b007dc000000000c050a00003ca1d606ed000000000180cc0807210b0dcf9144154d854a07d0d2d6ac000000000603d5c15258029b85e45650c82a2dc352a805b3097e00000c525105e5000006c24ccd717b4b490d6a6c74e45890b0990000102d4c0000402f2803f02c46b40e3800006005488b5f98a4a068800e7f00c721833009aa40a41a50d7c0d110048e0ef000e6f8bc17042876255419f38416886dd20845c113c8845d017117bd561ad80a0f6355b00b7200000000020328716a4c176f8153f029630bf64c25080290000020372e0bc783079041a263a4c0804406998bd70618ca853303aa80000260e72055e46ddb071e62ed20c3ffc573f892d7613fefa5a025008555122ec0000000003867f7607d2321743aa6db71a0e04804340000282d0) else (if i < 8 then 0x2038858c2400000a02fc0000283ad500cc61edb85dc8045cd039d4026304fc2863102807750960220b01ffc009f616b21f28cb095d6ae1e08d802311846d5057b61cdf9e70680dc10b4f229e509b5f8c4580be140de24366f3da4a6ad2408a6423d7bed0e0af20000380b1580be000000000000005b469802a2a32c9c66003db5f1887a5cac9d9fb854c30f3601a3c013ee041560937002f60076305f4a0c02a0932420528366f7cbca304402194837f00001e070340400143122e47a5cfd82b1e254820f06c004d835021534f1394635274081430b290e79616f8400da3402b534ba462580fb78460d0e710c1d8000000000d03dd42b16823c4837790a21218cd82a5b0302c0360ae5d34097e82ce6199820180d8f0782efb0a4e000018d1080000e0c2402694d84e200ff40a828596741f5709a3d16fb0c8cd02fcb0d51f0b46a004683249bf7e83467c144f18b2704d442b924c726018062f08c09e16033f43867852a90bc0610cc58b938b9f005298061106dfe045ba04af005cd880ce00d110d58e10a54192a0744907a96123cd8c94037e2645d00e11c248d976610a52a0a0bc12aa068d56ab961a2984e1c81d960db760080d8dae8b7a80ac582df281c0eaa0366150c12c9808fe8359802ef75c95c18610704200776e5494c8b58c1c10730c15908a128bb7380e136e8649aad406e520471a0bd0df271047537cf2617e0c1a4981d7000004ee22400bf0277d02f3c1c6c8379ecc03209970008d82550048c81752e4ae74213a8c0e000012088880d400000909c580b5b430ea8d520000182d54000000000e075600002c5c18000000000c06cadf6c8000080c12a00536d6ed80d600001209a000000042de0c86e131b404680000b0d8fa159d831488494962aa00000c251b02d8361c683040000000000867ba0000001ea984c960e07015404262e000600e56ecf7c418d6034ea0da181776402390314a11f0236d7c27c706b830250815518270bbb3a716f016dc2c12f2d70d76aaeefd5dc34a30774c0c0ae1820430118308616ee214866b80286bb00000a415300f48d74a6028668a09c28f2853fb0548e2e9258bfc8523a60b5405f2849a83477d0791418ec8ba87d704408128004b004499724e02f7413cd813320658e14c960d4e82cd408b440cf7a1e3d40ee5834d70ec8c0edb42a7dd40cf196e40e5341667026c669f8e1a729dfed0fb0fb6dd002571976407b800e342fe946a111023a31947cd5fb012ca032311363619a3c41a38650e0602ee9ab06d43b057c058640adc81937a3c016a6a80a6d85d1883d7e7b072c088c2718000010626000010494000000000180ab34bc1a861300000419b201b9c00184635e0000000000000000000a0e3c00002004100000a0aaceb80ad739a06a542ff1980fe1767302daa1a49821e1002200a6 else (if i < 9 then 0x4d103f240070e0ec4cbaa0b935a06838c20a0250d018d605a6209100254e00e8000014179f5838f0cb30000000002c1fabb56a6170a60796466b1065a00001410b3463480000713f482e8a016550061502218cb98992ebd2721713e00003015e184e400000219e805f90009f8139382d36021c804d2200b3217cb0144c0b13e07b0e6e6fd968c81999284021c4d589a1b0e850156e0311438ad856a0000160cf40000784fee70cb811f201f80844b10d87254e36d13d8644088058d46d406ce347657c4fc307ad97da058d3629de101b810708b9b102b483098c5f9a054350e1421708016f7273f70f2190151c5d3c039c606d709534189d2007d3043a82e53dfc4000002022a0e230c3ab805841ae06ad564028bcb143202f5e2264839ec8311b7dbe605d41ab400000f0cae406e0000028d93c0ceecd194000078d4f10e30a2d699fc2d04de00001223bc00000000000000000011f0e00000a17e80000083b1eb83da075c61a9f42dfe306810e9e01c5041c4a06623014402524dfcd10622f0355c111f034be032a62df3c231380afb8ec3a71b580ae7c360b074236808a11081ee00b21eb0a162c895c0ca807166781e4d16aab7fc8b5bc2d9e0c0bdc18cd0cbcb178754472c2d87bfb090232e0923007b5826400bfa8f099828e08da360cd3e0f2844f2986d640575216c81ada80000c00ef026fd01d30b2e8a0ad9e1238000038237d08a5550be8ba633dae518934077d0369b02f9b75410e7130184d05c72195ee1705405c98249b04e44f743014c80000b71fb01b2601570d650a00f4a05aaa0b9504d350f3c000009d9f7067052df000000000008291907daa03500303c002860bd341c8b40960b0c8707f98c4b7c0e1cd403506dd4c15ac03b79736e032f21d07c1b02b976603c400003c02643cb1912e000a7fab7cd8298803fbc1e354b9c0000040d610197706d5d3c1530bb80000002da0030d30989c017602022beaaf02940278d83c4104ae708a281835d9738000070b5a205a243b80000010b21c07c8c33a488e4b033c4ca3e5a38a3064f0115202f1987e8833ee63a880bfe6a189bf1192e9c60b5c4039b977b00001c1aa2580f4300e0745e0000282770000090414a084501ffd85d7f60c1c002642f68000040f5000002461e5055b805be62e224b83f82a25057f83afb08b5118d780b2360e20009b606e173013e10735b315051ba3e7fac86ad84e90382f129081cbc819dc036360ecbec2fc467ed0220f0375826cdc2a2fb081601f6c076f2a1d3062400000c056100e83039170b0400000c1298942f90ca6000000000183a7d180af5948000000000c07a5a0341001e486df4607e00003c101a839fc6313e16280000484f900000609ab007130426c0466c63d08103c877c6163c00002856f00000a0bac4553f981c0833a90da8000 else 0xc2b2f85ef6005f45936007c1802ea6432a0831031af305c306a8e2f51424e7c404501534054841f05848020ee261e3103b418068e64b6612ae02608061f40854e08a9030c6176f16c6420e368163d0d3a80aa78045c000018ce83a2ec4fe464156d89ab0446a0fd378a1f1818a8079f019a80bb1088e600000ccb61c19e28504e174b8e40b8200e842e07c58e0b1b403fa03e10000121becc31a683d0d60618189c00001011420cc600000022d305891082ce0f9e80b7d0568a0aada0ad3824cbb129a06e2000025876285c5d0c8000002c04748614800dc000000000503bb30740e5e10c8b8000000000080dd8416e4040080a33275498364285d5168d761ea800001387c10cb800000000000000a0a5940d088310800002a840000008ba4f85a1d010ae0c0cc5a833bf0d636402709c3b7603c17088cc16a506425b1fc8016a205260024800008007c2028c422c284c7d089800b6a4412f822bd2e4000602420c731a4e7060407754a1ff572471f6380b1045aa78bc0d099ce1aebc32cb059c50d2001adc00006b0e9706d400000c0b2800004636e0000003637893020e2f214ac002e03ecdb0d2600000000000000168d80000000001b144f0476a0474000000000000010070b43a88000077acce13f29f6e1072d000004e218000060be4d06d9645bd0641f8273b7be94317782ea2830e2b5376141902180b1b0a0075aece48099f37b0b183543375d8b2835a896169a2d38da8f80000000016053dc38eb031212dfb4096000b480000f0c95a12d80000582c8902c9a011949))))
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
  | 8 => lookupWord 1 8 0 8 2 2 p3853i8
  | 9 => lookupWord 10 37 4 12 5 3 p3853i9
  | 10 => lookupWord 113 387 8 16 8 4 p3853i10
  | 11 => lookupWord 610 2073 9 19 11 4 p3853i11
  | 12 => lookupWord 1066 3616 9 19 11 4 p3853i12
  | 13 => lookupWord 144 492 8 17 9 4 p3853i13
  | 14 => lookupWord 7 47 2 10 3 3 p3853i14
  | _ => fun _ => none
def basesamples : Array (Bits × Bits) := #[(0xfff000000000000000000ffffff000000000fff000000000000000000ffffff000000000fff000000000000000000ffffff000000000fff000000000000000000ffffff000000000fff000000000000000000ffffff000000000fff,0x544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544),(0xffffff000000000000000fff000000000000ffffff000000000000000fff000000000000ffffff000000000000000fff000000000000ffffff000000000000000fff000000000000ffffff000000000000000fff000000000000ffffff,0x823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823),(0xffffff000000000000000fff000000000000ffffff000000000000000fff000000000000ffffff000000000000000fff000000000000ffffff000000000000000fff000000000000ffffff000000000000000fff000000000000ffffff000,0x314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314),(0xffffff000000000000000fff000000000000ffffff000000000000000fff000000000000ffffff000000000000000fff000000000000ffffff000000000000000fff000000000000ffffff000000000000000fff000000000000ffffff000000,0x69069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069),(0xfff000000000000000000000000000000ffffff000000000000000000000000000000ffffff000000000000000000000000000000ffffff000000000000000000000000000000ffffff000000000000000000000000000000ffffff000000000,0xa92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92),(0xfff000fff000000000fff000000000000000fff000fff000000000fff000000000000000fff000fff000000000fff000000000000000fff000fff000000000fff000000000000000fff000fff000000000fff000000000000000,0x1b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b),(0xfff000000000fff000000000000000000000fff000000000fff000000000000000000000fff000000000fff000000000000000000000fff000000000fff000000000000000000000fff000000000fff000000000000000000,0xdc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc),(0xfff000fff000000000000000000000000000fff000fff000000000000000000000000000fff000fff000000000000000000000000000fff000fff000000000000000000000000000fff000fff000000000000000000000,0xce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0),(0xffffff000fff000000000000000000000000ffffff000fff000000000000000000000000ffffff000fff000000000000000000000000ffffff000fff000000000000000000000000ffffff000fff000000000000000000000000,0xf00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00)]
def basecolumns : List ColumnInfo := [(0,0,511,0,15),(16,0,495,0,13),(64,0,447,0,13),(128,0,383,0,13),(1,0,510,0,12),(2,0,509,0,12),(4,0,507,0,12),(8,0,503,0,12),(32,0,479,0,12),(256,0,255,0,12),(17,0,494,0,11),(24,0,487,0,11),(66,0,445,0,11),(80,0,431,0,11),(132,0,379,0,11),(144,0,367,0,11),(160,0,351,0,11),(192,0,319,0,11),(320,0,191,0,11),(0,16,486,9,10),(0,64,189,258,10),(0,128,347,36,10),(1,16,486,8,9),(2,64,189,256,9),(3,0,508,0,9),(4,128,347,32,9),(6,0,505,0,9),(8,16,486,1,9),(12,0,499,0,9),(18,0,493,0,9),(32,128,347,4,9),(33,0,478,0,9),(65,0,446,0,9),(96,0,415,0,9),(129,0,382,0,9),(130,0,381,0,9),(136,0,375,0,9),(256,64,189,2,9),(264,0,247,0,9),(288,0,223,0,9),(384,0,127,0,9),(0,1,460,50,8),(0,2,440,69,8),(0,4,369,138,8),(0,8,227,276,8),(0,32,94,385,8),(0,256,151,104,8),(5,0,506,0,8),(9,0,486,0,8),(9,16,486,0,8),(19,0,492,0,8),(25,0,486,0,8),(36,0,347,0,8),(36,128,347,0,8),(40,0,471,0,8),(49,0,462,0,8),(67,0,444,0,8),(70,0,441,0,8),(81,0,430,0,8),(82,0,429,0,8),(134,0,377,0,8),(140,0,371,0,8),(161,0,350,0,8),(164,0,347,0,8),(194,0,317,0,8),(257,0,254,0,8),(258,0,189,0,8),(258,64,189,0,8),(280,0,231,0,8),(322,0,189,0,8),(328,0,183,0,8),(336,0,175,0,8),(352,0,159,0,8),(416,0,95,0,8),(448,0,63,0,8),(1,2,440,68,7),(1,32,94,384,7),(2,1,460,48,7),(4,2,440,65,7),(4,8,227,272,7),(7,0,504,0,7),(8,4,369,130,7),(8,256,151,96,7),(14,0,497,0,7),(16,2,424,69,7),(16,4,353,138,7),(16,32,78,385,7),(16,256,135,104,7),(32,1,460,18,7),(32,256,151,72,7),(35,0,476,0,7),(64,1,396,50,7),(64,4,305,138,7),(64,8,163,276,7),(74,0,437,0,7),(83,0,428,0,7),(98,0,413,0,7),(128,1,332,50,7),(128,2,312,69,7),(128,4,369,10,7),(128,8,99,276,7),(133,0,378,0,7),(146,0,365,0,7),(156,0,355,0,7),(162,0,349,0,7),(177,0,334,0,7),(193,0,318,0,7),(198,0,313,0,7),(256,8,227,20,7),(256,32,94,129,7),(268,0,243,0,7),(273,0,238,0,7),(289,0,222,0,7),(296,0,215,0,7),(321,0,190,0,7),(344,0,167,0,7),(480,0,31,0,7),(5,2,440,64,6),(6,128,345,32,6),(10,4,369,128,6),(17,2,424,68,6),(17,32,78,384,6),(18,1,460,32,6),(18,4,353,136,6),(18,64,173,256,6),(20,2,424,65,6),(20,8,227,256,6),(20,128,331,32,6),(24,4,353,130,6),(24,256,135,96,6),(34,1,460,16,6),(40,256,151,64,6),(48,1,460,2,6),(48,256,135,72,6),(65,2,440,4,6),(65,32,30,384,6),(66,1,396,48,6),(66,128,281,36,6),(68,8,163,272,6),(72,4,305,130,6),(80,1,396,34,6),(80,2,424,5,6),(96,1,396,18,6),(129,2,312,68,6),(129,32,94,256,6),(130,1,332,48,6),(132,2,312,65,6),(132,8,99,272,6),(136,4,369,2,6),(136,256,23,96,6),(160,1,332,18,6),(192,2,312,5,6),(192,4,305,10,6),(257,32,94,128,6),(260,8,227,16,6),(272,32,78,129,6),(320,8,163,20,6),(320,128,27,36,6),(384,8,99,20,6),(7,16,480,8,5),(7,128,344,32,5),(11,16,484,0,5),(13,16,482,0,5),(14,16,480,1,5),(14,64,177,256,5),(19,64,172,256,5),(21,2,424,64,5),(21,128,330,32,5),(26,4,353,128,5),(27,0,484,0,5),(29,0,482,0,5),(35,64,156,256,5),(35,128,344,4,5),(38,128,345,0,5),(41,16,454,0,5),(50,1,460,0,5),(52,128,331,0,5),(56,256,135,64,5),(69,2,440,0,5),(70,128,281,32,5),(73,16,422,0,5),(74,4,305,128,5),(81,2,424,4,5),(82,1,396,32,5),(84,2,424,1,5),(84,8,163,256,5),(88,256,135,32,5),(89,0,422,0,5),(98,1,396,16,5),(98,128,281,4,5),(104,256,151,0,5),(112,1,396,2,5),(112,256,135,8,5),(133,2,312,64,5),(134,64,57,256,5),(137,16,358,0,5),(138,4,369,0,5),(145,32,78,256,5),(146,1,332,32,5),(146,4,353,8,5),(148,8,99,256,5),(152,4,353,2,5),(162,1,332,16,5),(162,64,29,256,5),(166,0,345,0,5),(168,16,326,1,5),(168,256,23,64,5),(176,1,332,2,5),(193,2,312,4,5),(193,32,30,256,5),(194,4,305,8,5),(196,2,312,1,5),(200,4,305,2,5),(200,256,23,32,5),(262,64,185,0,5),(265,16,230,0,5),(273,32,78,128,5),(274,64,173,0,5),(276,8,227,0,5),(296,16,198,1,5),(321,32,30,128,5),(324,8,163,16,5),(324,128,27,32,5),(326,0,185,0,5),(336,8,163,4,5),(352,128,27,4,5),(385,32,94,0,5),(386,64,61,0,5),(388,8,99,16,5),(388,64,57,2,5),(400,8,99,4,5),(400,32,78,1,5),(448,32,30,1,5),(15,0,480,0,4)]
def mf : Forest := ⟨511,13,fun j => basesamples[j]?.getD (0,0),basecolumns,deadautos,actualLevels,actualIndex⟩
def tokenConfig (k i : Nat) : Nat × Bool × Nat :=
  let (num,d,cw,_,_,offw,lw,data) := mf.levels k
  let start := num*(8+11*(d-2)+9+d)
  let pos := start+num*offw+packedAt data (start+i*offw) offw
  let nr := packedAt data pos 7
  let linked := packedAt data (pos+7) lw
  let st := pos+7+lw+nr*(cw+d)
  (nr,linked != 0,packedAt data st 552)
structure MinorData where
  q : Nat
  level : Nat
  pos : List Row
  neg : List Row
  pm : Sig
  nm : Sig
  deriving Inhabited

def minorInputs : Array MinorData := #[⟨495,13,[3, 6, 12, 33, 66, 132, 264, 160, 320, 288],[42, 69, 100, 104, 138, 201, 261, 385, 386],0x100000001000001000000000000000000000000010000001000000000000000040000000200001048,0x6000000000000000000000000000000200000000000000200000000000000040000000110000000200000040000000000⟩,
⟨447,13,[3, 6, 12, 24, 17, 33, 132, 264, 160, 288],[42, 50, 52, 137, 138, 261, 276, 385, 402],0x1000001000000000000000000000000010000001000000000000000000000000201021048,0x40002000000000000000000000000001000200000000000000000000000000000060000000000000000000014040000000000⟩,
⟨383,13,[3, 6, 12, 24, 17, 33, 66, 264, 320, 288],[42, 50, 69, 73, 104, 116, 261, 274, 276],0x100000001000001000000000000000000000000000000000000000000000000040000000201021048,0x1400200000000000000000000000000000000000100100000002200004040000000000⟩,
⟨510,12,[6, 12, 24, 66, 132, 264, 160, 320, 288],[42, 50, 104, 116, 138, 200, 208, 276, 402],0x100000001000001000000000000000000000000010000001000000000000000040000000001001040,0x40000000000000000000000000000001000000000000000010100000000000000040000100100000000000004040000000000⟩,
⟨509,12,[12, 24, 17, 33, 132, 264, 160, 320, 288],[69, 104, 116, 201, 208, 261, 276, 385, 400],0x100000001000001000000000000000000000000010000001000000000000000000000000201021000,0x10002000000000000000000000000001000200000000000010200000000000000000000100100000000200000000000000000⟩,
⟨507,12,[3, 24, 17, 33, 66, 264, 160, 320, 288],[42, 50, 104, 112, 138, 201, 208, 385, 402],0x100000001000001000000000000000000000000010000000000000000000000040000000201020008,0x40002000000000000000000000000000000000000000000010200000000000000040000010100000000000004040000000000⟩,
⟨503,12,[3, 6, 17, 33, 66, 132, 160, 320, 288],[50, 69, 116, 193, 208, 261, 276, 385, 402],0x100000001000000000000000000000000000000010000001000000000000000040000000200020048,0x40002000000000000000000000000001000200000000000010002000000000000000000100000000000200004000000000000⟩,
⟨479,12,[3, 6, 12, 24, 17, 66, 132, 264, 320],[69, 84, 138, 201, 208, 261, 276, 385, 402],0x100000000000001000000000000000000000000000000001000000000000000040000000001021048,0x40002000000000000000000000000001000200000000000010200000000000000040000000000001000200000000000000000⟩,
⟨255,12,[3, 6, 12, 24, 17, 33, 66, 132, 160],[42, 50, 69, 104, 116, 138, 146, 201, 208],0x10000001000000000000000040000000201021048,0x10200000000000004040000100100000000200004040000000000⟩,
⟨494,11,[6, 12, 66, 132, 264, 160, 320, 288],[42, 100, 104, 138, 200, 260, 386],0x100000001000001000000000000000000000000010000001000000000000000040000000000001040,0x4000000000000000000000000000000100000000000000100000000000000040000000110000000000000040000000000⟩,
⟨487,11,[3, 6, 33, 66, 132, 160, 320, 288],[34, 69, 100, 193, 261, 385, 386],0x100000001000000000000000000000000000000010000001000000000000000040000000200000048,0x6000000000000000000000000000000200000000000000002000000000000000000000010000000200000000400000000⟩,
⟨445,11,[12, 24, 17, 33, 132, 264, 160, 288],[40, 52, 137, 261, 276, 385, 400],0x1000001000000000000000000000000010000001000000000000000000000000201021000,0x10002000000000000000000000000001000200000000000000000000000000000020000000000000000000010010000000000⟩,
⟨431,11,[3, 6, 12, 33, 132, 264, 160, 288],[36, 42, 137, 138, 261, 385, 386],0x1000001000000000000000000000000010000001000000000000000000000000200001048,0x6000000000000000000000000000000200000000000000000000000000000060000000000000000000000041000000000⟩,
⟨379,11,[3, 24, 17, 33, 66, 264, 320, 288],[42, 50, 73, 104, 112, 257, 274],0x100000001000001000000000000000000000000000000000000000000000000040000000201020008,0x400020000000000000000000000000000000000010100000002000004040000000000⟩,
⟨351,11,[3, 6, 12, 24, 17, 66, 264, 320],[10, 69, 73, 84, 261, 274, 276],0x100000000000001000000000000000000000000000000000000000000000000040000000001021048,0x1400200000000000000000000000000000000000000000001002200000000000000400⟩,
⟨508,9,[12, 24, 132, 264, 160, 320, 288],[104, 116, 200, 208, 276, 400],0x100000001000001000000000000000000000000010000001000000000000000000000000001001000,0x10000000000000000000000000000001000000000000000010100000000000000000000100100000000000000000000000000⟩,
⟨505,9,[24, 17, 33, 264, 160, 320, 288],[104, 112, 201, 208, 385, 400],0x100000001000001000000000000000000000000010000000000000000000000000000000201020000,0x10002000000000000000000000000000000000000000000010200000000000000000000010100000000000000000000000000⟩,
⟨499,9,[3, 17, 33, 66, 160, 320, 288],[50, 112, 193, 208, 385, 402],0x100000001000000000000000000000000000000010000000000000000000000040000000200020008,0x40002000000000000000000000000000000000000000000010002000000000000000000010000000000000004000000000000⟩,
⟨493,9,[12, 33, 132, 264, 160, 320, 288],[69, 100, 104, 201, 261, 385],0x100000001000001000000000000000000000000010000001000000000000000000000000200001000,0x2000000000000000000000000000000200000000000000200000000000000000000000110000000200000000000000000⟩,
⟨478,9,[6, 12, 24, 66, 132, 264, 320],[84, 138, 200, 208, 276, 402],0x100000000000001000000000000000000000000000000001000000000000000040000000001001040,0x40000000000000000000000000000001000000000000000010100000000000000040000000000001000000000000000000000⟩,
⟨446,9,[6, 12, 24, 132, 264, 160, 288],[42, 50, 52, 138, 276, 402],0x1000001000000000000000000000000010000001000000000000000000000000001001040,0x40000000000000000000000000000001000000000000000000000000000000000040000000000000000000014040000000000⟩,
⟨415,9,[3, 6, 12, 24, 17, 132, 264],[137, 138, 261, 276, 385, 402],0x1000000000000000000000000000000001000000000000000000000000001021048,0x40002000000000000000000000000001000200000000000000000000000000000060000000000000000000000000000000000⟩,
⟨382,9,[6, 12, 24, 66, 264, 320, 288],[42, 50, 104, 116, 274, 276],0x100000001000001000000000000000000000000000000000000000000000000040000000001001040,0x1400000000000000000000000000000000000000100100000000000004040000000000⟩,
⟨381,9,[12, 24, 17, 33, 264, 320, 288],[69, 73, 104, 116, 261, 276],0x100000001000001000000000000000000000000000000000000000000000000000000000201021000,0x1000200000000000000000000000000000000000100100000002200000000000000000⟩,
⟨375,9,[3, 6, 17, 33, 66, 320, 288],[50, 69, 116, 261, 274, 276],0x100000001000000000000000000000000000000000000000000000000000000040000000200020048,0x1400200000000000000000000000000000000000100000000000200004000000000000⟩,
⟨247,9,[3, 6, 17, 33, 66, 132, 160],[50, 69, 116, 146, 193, 208],0x10000001000000000000000040000000200020048,0x10002000000000004000000100000000000200004000000000000⟩,
⟨127,9,[3, 6, 12, 24, 17, 33, 66],[42, 50, 69, 73, 104, 116],0x40000000201021048,0x100100000002200004040000000000⟩,
⟨506,8,[24, 66, 264, 160, 320, 288],[42, 50, 104, 112, 138, 200, 208, 402],0x100000001000001000000000000000000000000010000000000000000000000040000000001000000,0x40000000000000000000000000000000000000000000000010100000000000000040000010100000000000004040000000000⟩,
⟨486,8,[6, 66, 132, 160, 320, 288],[34, 100, 192, 260, 386],0x100000001000000000000000000000000000000010000001000000000000000040000000000000040,0x4000000000000000000000000000000100000000000000001000000000000000000000010000000000000000400000000⟩,
⟨501,8,[17, 33, 132, 160, 320, 288],[69, 116, 193, 208, 261, 276, 385, 400],0x100000001000000000000000000000000000000010000001000000000000000000000000200020000,0x10002000000000000000000000000001000200000000000010002000000000000000000100000000000200000000000000000⟩,
⟨492,8,[12, 132, 264, 160, 320, 288],[100, 104, 200, 260, 384],0x100000001000001000000000000000000000000010000001000000000000000000000000000001000,0x1000000000000000000000000000000100000000000000100000000000000000000000110000000000000000000000000⟩,
⟨462,8,[6, 12, 66, 132, 264, 320],[68, 138, 200, 260, 386],0x100000000000001000000000000000000000000000000001000000000000000040000000000001040,0x4000000000000000000000000000000100000000000000100000000000000040000000000000000100000000000000000⟩,
⟨444,8,[12, 24, 132, 264, 160, 288],[40, 52, 136, 276, 400],0x1000001000000000000000000000000010000001000000000000000000000000001001000,0x10000000000000000000000000000001000000000000000000000000000000000010000000000000000000010010000000000⟩,
⟨441,8,[24, 17, 33, 264, 160, 288],[40, 48, 137, 385, 400],0x1000001000000000000000000000000010000000000000000000000000000000201020000,0x10002000000000000000000000000000000000000000000000000000000000000020000000000000000000001010000000000⟩,
⟨430,8,[6, 12, 132, 264, 160, 288],[36, 42, 138, 260, 386],0x1000001000000000000000000000000010000001000000000000000000000000000001040,0x4000000000000000000000000000000100000000000000000000000000000040000000000000000000000041000000000⟩,
⟨429,8,[12, 33, 132, 264, 160, 288],[36, 40, 137, 261, 385],0x1000001000000000000000000000000010000001000000000000000000000000200001000,0x2000000000000000000000000000000200000000000000000000000000000020000000000000000000000011000000000⟩,
⟨377,8,[24, 17, 33, 264, 320, 288],[73, 104, 112, 257, 272],0x100000001000001000000000000000000000000000000000000000000000000000000000201020000,0x100020000000000000000000000000000000000010100000002000000000000000000⟩,
⟨371,8,[3, 17, 33, 66, 320, 288],[50, 65, 112, 257, 274],0x100000001000000000000000000000000000000000000000000000000000000040000000200020008,0x400020000000000000000000000000000000000010000000000020004000000000000⟩,
⟨359,8,[3, 6, 33, 66, 320, 288],[34, 69, 100, 258, 261],0x100000001000000000000000000000000000000000000000000000000000000040000000200000048,0x240000000000000000000000000000000000000010000000200000000400000000⟩,
⟨350,8,[6, 12, 24, 66, 264, 320],[10, 72, 84, 274, 276],0x100000000000001000000000000000000000000000000000000000000000000040000000001001040,0x1400000000000000000000000000000000000000000000001001000000000000000400⟩,
⟨317,8,[12, 24, 17, 33, 264, 288],[9, 40, 52, 261, 276],0x1000001000000000000000000000000000000000000000000000000000000000201021000,0x1000200000000000000000000000000000000000000000000000000010010000000200⟩,
⟨254,8,[6, 12, 24, 66, 132, 160],[42, 50, 104, 116, 138, 146, 200, 208],0x10000001000000000000000040000000001001040,0x10100000000000004040000100100000000000004040000000000⟩,
⟨189,8,[12, 24, 17, 33, 132, 160],[5, 40, 52, 137, 144],0x10000001000000000000000000000000201021000,0x1020000000000000000000010010000000020⟩,
⟨231,8,[3, 6, 33, 66, 132, 160],[34, 69, 100, 130, 193],0x10000001000000000000000040000000200000048,0x2000000000000000400000010000000200000000400000000⟩,
⟨183,8,[3, 6, 17, 33, 132, 160],[5, 50, 52, 129, 146],0x10000001000000000000000000000000200020048,0x4000200000000000000000014000000000020⟩,
⟨175,8,[3, 6, 12, 33, 132, 160],[5, 36, 42, 137, 138],0x10000001000000000000000000000000200001048,0x60000000000000000000000041000000020⟩,
⟨63,8,[3, 6, 12, 24, 17, 33],[5, 9, 42, 50, 52],0x201021048,0x14040000000220⟩]
def minorLeaf5 (i : Nat) : Nat := 0x0
def minorLeaf6 (i : Nat) : Nat := 0x0
def minorLeaf7 (i : Nat) : Nat := 0xa050ec9418c0030
def minorLeaf8 (i : Nat) : Nat := 0x410eca87458d01d950c88c1ce08195342eb9c103282685d05298764a0aaa0050ec9418e00e1d9508720e1d950087210e1d94087200e1d95087065908e1da8a90c3211cbb51520208781ad0017a000000014b0011c00000000f0310981b00000000000000e406
def minorLeaf9 (i : Nat) : Nat := (if i < 1 then 0xeca09a17400e081d95342e88294c3b27053015298764e0a60065530ecbc2c450995c54bb279c30a3526570ec9c74c10b2b29ba10108aa4c3b219020a1c3b29810e0a1c3b29810e09a4c3b2a1023081c3aa190e081c3b2a190e081c3b2a190e081c3b2a190e0aa43832190ac01c3b2a010e0ca43b2a19020c31baa1810e0aa4c3b219020a31c3a9810e0831c3aa190e0c23b282190508243b2a19050a92043b21950a92043b21950a429bb29908139b5d4c32f8110846d7530ecbe04420992043b2a150992043b2a1509429bb2a1880c92c03b2a68551923570654d0a82c4b300ea9a1545896601d5342a8b11acb82a68541423597065d0a8284b300ecba154508d65c19742a195d4c32a1ac10842b300ea876554856601d50ecaaa041c3b299081841c3b2a108091b5d4c3af81108a46d7530ede0442101b54c3b2f01114286c4f975187c60c41066238704a2cc32864b974deb159c7143625ca97fdc6ce388211cc3b5152143625ca97fdd6ce38a1184c3ad95a134209875b2b43284610eb65686108c25d6cad0aa1184c3d95a143625ca97fdd2ce38a1b12e5cbf5d9671c6508e1d828a90c211cbb05152174239860a2a42c84730ec145485908e61c28a90a1b12dd4bfef5671c50d8972e5faeab38e286c4b972fb3559c7143625cba9f5aace3883211c3b05166124635cba9c5648e38a1b12e5d4fac5671c64d50b2ea2cd1a18c34c65730e9c68c103a10ac32860631824139760d4b2308e0ca8642a2a90e0c8642a08530eca81c14dc8ea61d95282381c215d4bae2a10c248b300ec7895421084e1d828338a1b13e54c7ee123101c905601970318a1b13e54c75e123104d49aea61f848846642138070a0ce248b300ed41545894eea61e8488513452ba987a3421851c98f2e63650918ae0482b0e0d418c0aef569eaf7544000000000151800000029d94b5000000000000000051f8000000000000288e0000005050000000000000000000000000000013e100000000000009d180000000000004d94000000993cbdc000000963ca5e4ce00091bc81e3ae000000000234e0008bb800228f11700000000010e785bc21e0af0277fbbf1c0000000000000000f970003d9de6eef90000000000ebb0000001d1600072db8ac00000000000000000000000000000df46de80000000000003618000000000353da30ce100032a98e6000000000000000061cb0080000000002f2c00000000000000000000000001736b6b596abbd5620000000000000000536000146a9f04d5a5e1266900466a2690ce8343f79ea8eee7443889b68d4e66230e9760b2655c0000000000517269123489e4181f08ec470234a0000c4c0002d50000a780000000000000000000000099c4441eb0d300002d0131000000000000000003f8000000000030010403d000000000c000 else 0x410eca861898c0821d950c28b1a03b2a19011894cc32a01b45304876543215400765432237038206504d0ba07040)
def minorLeaf10 (i : Nat) : Nat := (if i < 3 then (if i < 1 then 0x46de4695464c460a45cc458a4548450a000044cc448e44500000441243d44396435b0000432042e242a400000000000000000000000042660000422b41e241a4415b4119000040de40a00000000000000000000000004062000040243fdb3f9d3f623f270000000000003ee93ea7000000003e6c3e23000000003dda3d9c3d533d183ccf3c943c593c103bc73b7e3b4300003b083ad1000000000000000000000000000000003a9a3a5f3a2439e239ab0000000000003969000000003927000038de0000000038a338683826000037f237c23787374c370a000036da36aa366f3634360435d40000359900003557352034e234a03465342a33f333b1337a334a0000330f32d4329932573220000031de319c3168312630eb30b000003075000000000000000030450000300300000000000000002fd32fa32f6100002f262eeb2ea92e6e2e332dea2da82d5f2d2b2ce22c992c652c2a00002be82bad2b642b1b2ae72aa52a712a3d29fb000029c700002985294a290128cd288b2850281527e100000000000027a6275d271400000000000026e000000000000000000000000026ac267c263a260625cb2597255c252124e624a42469242e23fa23b8237d2342230e22d32291224821ff21cb21902152211720ce2093000000002058201d1fe21fa01f6c1f381ef61ebb1e72000000001e2900001de700000000000000001db31d781d361cfb1cc000001c7e000000001c4a000000001c0f1bd41b9900001b5e1b23000000001ae1000000000000000000001a981a56000000001a0d000019d20000000000001997000000000000000000000000195c192118e6000018ab00001870000018350000000000001801000017b8177d173b170016be167c0000163a160a15d6158d1544150914d914a5145c142813f813af0000137b133900001309000000000000000000000000000012c01285123c0000000011fa000011c311881154112010f010ab00001070103c0ffe0fb90f7e0f430f080ebf0e7600000e2d0df200000db700000d7500000d3a000000000cf80cb60000000000000c7400000c320bf70bb50b730b310aef000000000aad0a6400000a2900000000000009e709b0097500000000093a08ff0000000008b60000086d00000000000000000000000000000836000000000000000007f4000000000000000007ab0762000000000720000006f00000000006b9067e0643060805cd059200000554052404f000000000000000000000000000000000000004b904820440000003fe0000000003c70000000003850000000000000000034e000000000000000000000317000002d9000000000000029b000000000000025d000000000000021f000001e101aa016c0000012e0000000000f0000000b2007b003d000000060000000000000000 else (if i < 2 then 0x876500000000872a86e886ad00000000867286290000000085f5000085ba857185360000850284c0848c844a0000840f0000000083c60000000000000000000000000000000000000000000000000000000000000000000083848346830482c2828000000000000000000000823e81fc81c181868144811480d280908055801a7fdf7fab7f627f2e7ef37eb87e7d00007e427df97dbe7d7500007d2c7cea7caf00007c6d7c2b7be200007b997b5000007b0700007acc7a837a48000000007a0679cb79947960792578ea78a878740000000078447814000077d2000000000000000000000000779e776a773676fb76bd76897652761e75ee75b000007575753a74f8000074b6747474440000741473d97390000073607325000072e372af7266722b0000000071e90000000071a000000000716c713870fd00000000000000000000000070bf00000000707d704970076fbe00006f7500006f2c6ee300006e9a000000006e51000000006e0f6dc66d84000000006d426d07000000006ccc6c916c486bff6bb600006b7b6b396af06aa700006a656a1c69e1699f69566914000000000000000068d96897000000000000684e68050000000067d1679d000000000000676d673666fb66c70000000000000000669300000000665c662165ed65b2657e654a00000000651364d864a4646d00006432640263cb6397000000000000636300000000000000000000000000000000000000000000000000000000632f00000000000062fb000062c7000000006293000000000000000000000000000000000000625f0000622b61e90000000000000000000061a700000000000000000000616c000000000000000000000000613160e80000000000000000000000000000000060a60000606b0000000000000000603760005fd05f8e5f505f205ef05eb95e8200005e47000000005e055dbc00005d7a5d4300000000000000000000000000000000000000005d0100000000000000005ccd0000000000005c8b5c4200000000000000000000000000000000000000005c005bbe00005b7500005b2c000000000000000000000000000000005aee5aac000000000000000000005a6a000000000000000000005a2859e6000059a8000059660000000000000000592b58e958a058705839580257d257a2576b573456fd56c6568f5658562855ea55af55785548551854e154aa547a544a541353dc53a5536e532c52e352a15258522451e2519951570000511550d35091504f50064fc44f824f394f054ec34e7a4e384def4db44d7900004d3e4d034cc800004c864c3d00004bfb4bbd4b7b00004b3200004af700000000000000000000000000004ab5000000004a7a4a3f49fd000049bb000000004980493e490348c8000000004886483d000047fb47b947704727 else 0x7654090ca268a5730ecbfa84304909cc3b02505913526ba9874fd2210494eea61d828488513526ba9874eb2210c521c195085504d21c1950854108f2e8261a8d8a190084797530e186848c501239087604a0b2e26900ca842b026900eca842e284797530e186848c551348706542151134870652151243cb0a986a362861089a403b2a10b89a935d4c3a7c91082690e0ca842a2487817530d46c50c31342a987654a08c284c79730e1b2848c513526ba9874d92210c08601d812833c0109c03b025067102237654301f60314760542231034760542233024cba986a2828609c10c03b0025067173476050422313526ba984f72210c932ea421a8a0a1832427210ec094164e486421d81282c8c91c843b0250591243cba9086a3628608a131e5cc386aa12314490f2c2a61a8d8a1842685530eca941185c8e421d81282c89a9354c3825a91140e427210ec941644d49aa61c12d488a03452ba9875c542184d49aa61c12d488a03526ba9874c5221049056601d8f12a81a935d4c3a629108104697530eb4684389a295d4c3ae2a10c304697530eb4684389a935d4c3a629108284c79753018a848c512415980763c4aa26a4d7530e98a4420a12d4c3b1c84412415980763c4aa0c42700ec09419c090561c180ed31811a65d4c0351a1231c08d32ea601a8d0918e2483300ecb41544d49aea61d3c488406243c0ba98a3628618211ae5d4c071a3431c6894eea61da848851234807654170421380760a0cf0842700ec01419c090561c1817031b2109c03b00506794213908760a0b2e8427210ec141644d49aea61f8488413487065421513148706542154213908760a0b26843210ec141640d49aea61da8488413452ba9876a342181084e421da82c8291a5d4c3ad1a10e284b530ec7211049056601da82a8a91a54c3851a11626a4d530e14244509a935d4c3d0910806a4d7530f4244201a935d4c3d091082482b300ed41540d49aea61e8488403526ba987a122104d14aea61e8d08615234ba987a3421c49056601da82a89a935d4c3d091080482b0e0c1418c0971396d8969d966d9632000000000000000095f7000095bc958100000000954600009516000094e2000094b200009482000000000000944b94100000000093e0000093a5936a9336930692c400009289924e921a000091df91a400000000917491449110000000000000000000000000000000000000000090d5908c0000000000009055901e8fd58fa18f7100008f2f8ef88ebd8e82000000000000000000000000000000008e4400008e060000000000008dc8000000008d8a00008d4c8d0e0000000000008cd78ca78c6c8c2a8bef8bb48b798b308ae78ab78a87000000008a4c00008a11000089d68994894b891088d500000000889a885f00000000000000000000881d87e2000087a7)) else (if i < 5 then (if i < 4 then 0xc08a5010cc3b2a01f15323ba9876540f44610661d8150c8051d95000c80744aa61d9500fca2810cc3b2a01f15318706543201519876054320113209876054a2b42657530eca8f68c10954c3b2a1bd4223ba876504d846144caea61d951ed18212349865300c6a0304612ec0a945680aa61d950e8a08995d4c3b2a3ca30225530eca86f1044e01c195083c492a61d950de228992cc38320485414230987605a2b4265530e0ca8ce445094c3b02a1b34a132ba9876547922104c9aea61d51e48840138765430213132ba807654ebb204496601d50c0d2a89054c3b2a1fc411259807543034aa2130eca8640264b750eca09b2842884c3b2a19008cc3b02a19008995cc03b2a7ee302048300ec0a7a19c48e421d950392b8995d04c3b271a304048300ec0a7a19e09041d8014f4338a19654843afee3470444ca8021d934d1961432c0a9875fdc68e1039893b2821138a193e54c307ee1231050c972a601ff71a38e02e70eca864262a5300eca81a15468cac261d938d18207215806540c0c62864f9530c1d7848c414325ca9807ebc68e380b9c3b2a19098995d04c3b271a30402e70eca86426a2e70ec08642626575300ec9c68c089b1bb02821120b195d04c3a71a3040842b0e0ca1818c50c972ea603571a38e290e0ca86402a477530eca09e5042894c03b2a1872551259807543034aa2090e0ca8642a483210ec0a7c16490f02ea61dbc581186487817530ede2c08c318487065432158148706543215949876543204132ba980765f16205c61201950c85448e61d94012ca908c243832990a952d4c3b2a1914421498760540e0a682530ec0a81c14c48eea61c197c608712aa9876543c488024930eca81c14d01c5d8150c88c48d2ea60197c188712a5a9875433488204930eca81c14c41d1d8150c88c409261d950382989d935d4c2a7b9108286561530edf3c58c214320ba9876f9e2c618bba3028219118c9243b02a0705313b26a9854f72210589261c15038298a19605d4bb6bf1630c5c8ea61d9528a3812d4c3b2a1f94401249876540e0a628490e0c0a1a1904c92ea61c17551870371476054223737146050422313b26ba9874d322100a9661d950fc220a195854c3b79f1630850c82ea61dbcf8b1862764d530ea9e24420942403b2a18b8a19004c3b2d15b1324ba98706e3461c1084e01d817433c210983b002e86713b26ba9875e122106121c1950c8554a0641d950342aa140ac83b28685502815907654d0aa25530e0ca87450449261d815038299a295cc3b02fea10c649975210ed45050c10342ba98705c54218508f02ea5db5d8a1862e47530eca9451c5c84e421d9282cc120ac83b28685542159807650a0aaa483300eca1415409056601d9682a81909cc3b02505943213908760a0b228690e0ca842a0649975300d47850c7123080 else 0x648c21c152cad0954c3b2a1bd420298605403c6a624930ca6018d40608c25c152cad0954c3b2a1bc470476500320201324ba986579661c548c261c152cad0954c3b2a1bc460376500420201348760520141523098704b2b425530eca86f11409d94010c0804921d814c050508c261c16cad0954c3b2a1bc440298760543669424b530ec86f1104cac261d953f7582243ca908765fdd046089935cc3aa07ee9082864b9520edfba59c718798765432021326ba87540ebb21050c972e41dbaecb38e270497530cbfacc389c125d4c32ecb30e270497530cbd6cc389c125d4c32e2b30e270497530cb86cc38a192dd483b7ef5671c60c92ea6197d59871326ba87540eba61050c972e41dbaeab38e2e930eca86404264d750ea81b34c20a192e5c83b6cd5671c60c92ea61975598714325cba906f5aace388154c3b2a1ea431245970643052a820c470ec00945984aa421d950f521092cc383218615418324ba9865c5661c10cb2e81d971e2b1822ec657530a986c440c1925d4b2e2b30e264d7530e81e70c20a192e5d4837ac5671c49aa61d950e822891dd4c3b2858a10824d530eca87411449021d8014e4360993dd43b2a6ca10a64b530e00c96a445891c3b002a05060123ba987650b14211048e1d8014283009354c3b2a1d04518324ba9865f3661c50c96ea41dbd79b38e2656130eca9fb8c109935cc3aa07ee1082864b9520edfb8d9c714325ca9076e5c6ce38a192e5d483f9e3671c50c972e81db161b38e2864b97520fe70d9c713524ba9865fd661c4c92ea61970d98713524ba9865f5661c4d492ea61971598713524ba986f3661c4d492ea61b8d98713524ba986c3661c4d492ea61bcd98713524ba986e3661c4d492ea61bf598713524ba986d3661c558aa61d90e82289284c3b021ec5313524ba986eb661c4d492ea61b0d98713524ba98679661c494261d810f5a9909a65d4c02d9a343184d492ea61ba59871342cba9805b34686309b395d43aa6ca10a24a130ec0878d4c4d492ea61b6598712534ba986b2461c4d492ea61bd59871342cba0975c366c6409a925d4c372b30e2ac5530ec874114558aa61d90e82289a925d4c36ab30e26a575300c966c4089284c3b021d95319342cba805b3468630b9a165d04ae1b363204d492ea61b15987243cba90876fde04608952d4c3b21f544243cba90876e9e04608952d4c3b21f44412a5a987643d888487975210edebc08c1243cba90876e5e0460921e5d4843b62f023044a96a61d90f0a20952d4c3b21f84412a5987643f08824b530ec87e5104916a61d90faa20922d4c3b21ec4418432ba9765b342184916a61d8f0a20993dd4c3b2d0910a2c4e77530eb4244289aa165d4c059a343184a61d81500eca9810c3832a185a6332ba9876504f342144e1d9410c084c0e1d950c084c4a61d815) else (if i < 6 then 0x41c5201950c854061d950c08070086601d50c0d2a995d4c3a8262a10acc0e0ca8604565530eca8078914061c1950c8054661d8150c804caea61d817c5086125a98754303488204610c0a8789b04caea61d4131508532ba98765407946108eea61d95028a884109876543201109876543201a2a98765043c28c487961530ebe74d8c210387065421610429807653b0ac20657530ec9e74c1083a9bb2a1010982165d4c3ae92363084108c21d8170b681954c3832870b11408659752ec06bc60c41085876543213107436543201f01429807653b0ac24697530ede70c391b5d4c3b28781108030b0eca864260657530e0c9e70c382195d4c3b079f1831050cac2a61d7d79d3842864b75300febce1c70432cba8760c3e30620a196584c3aeaf3a70850c9f2ea1830f8c1882c6a57530e9e6c440a192e5d403e2f3871c4cae601d953f7181132b0a98764f3a60c48d601c190343408924803b29e95611249007653d2ac286581530ebfb8e9c214327ca9860fdc30620a192e54c03fee3871c6092401d94f4ab0d19584c3b271d3042864f9530c1d7860c414325ca9807ebc70e38c995d043b271d3042864f9750c1b3860c412079086543d8b0326a5730ec9c6c440a192e5d403ece3871c0caa61c19434588a10235860540c0c00657530e0c9c70c38a19654c032fea34319008f2ea5d95de1b38220930eca864082070eca8604382a90e0c8642a4cb530ea8621101896a61d50f0220a9243b02190a081c3b2a1810e12d4c3b2a1884412380760054a0ce2690e0ca8642a48b530eca86f11040e1d950c087040e1d950c0870916a61d94c4220212d4c3b29e04413248760542141238076004a0ce084b530eca781104d21c1950854916a61d94de22099243b02a10a0929c3b2a180808243832a190a8824c3b2a19020b01c3aa1810e08243b28219050902043b2a1950902043b2a1950d9c154c3b2a0a10a460d7530ecbe04420902cc03b2a685512059807654d0aa284c794130fc6c08c8132ba807654d7a204916a61d950fca2401c3b2a1900812d4c3b2a1f944603875432010132ba9876504142160caea5d94105085403876532010303876542010125a987643108884b530eca62111096a61d950f0221c954843b2820a11828527970ec1b2848c513526ba9754d9821081661d950c4251b154843b2820a11822690e0ca842a6a55210eca0828460a118654c3b72b143241894eea61d6c508803526ba9764c38210108d72ea01b161a18e285279750e186848c513526ba974c38210ecaea61d9410508513526ba9875f182104d49aea61d786084362ba987650414214d8aea61d410508513482ba7654d942144a6821d950ff2109935cc3aa07eeb082864b9520edfbad9c71487605320141320987054b2b425530eca86f50c19d4010c80805d21814c8050 else 0x40821d8150e43608154c3b2a1f5411249876430022a02130eca8640220410ec0a8721b048e61d9500242890cc003b2a19a561298760543064942530eca8006c544121d950c8054521c1950c80544261d950c8044261d950c80482a61d950fca0899484382a1985940076543202310298076543d8ac410eca008614574621d9410c084c221d950c084ccaea61d9501d51849219860540368a6043330ca806d14c00621d950c84c4aa61d950c1d220924c3832983254108706543216108706543216018476543201591298760540e0a6046975300ede7c60c71029876540e0a620530eca81c14c00d0aea61dbcf8b18200ee6ca86403e20464eca0858268a57530edf2c448094c3b2a0705308207650043d0ba0a60500ec8141ac548d2a61dbcf88712b36a9875f142104a8da61c178508a02b36a9875f14210148d2a61dbcf88702b36a9875f1421082a61d950ec210b43802a190b138cc0032a1e956123ba980654f0621c5c4a401950f4ab38c148032a1e9561982a876543e2842864f930ca1d7670c414325c98076ebb38e3884c3b2a1900884c3b2a190088154c3b2a1d84112098765403eaa6264130e0a8661684caea601953c18873402ca98765fcef8e089044bb2a01f5531284976430022a024112eca807b14c48225d9500f62989185d4c32a6bb11222c5200ea87a558618a401d50f4ab09c125cc3b2f5e30e04330eca807d54d0cae61d8153f508602189765403eaa632a550eca87c50850c972601dbaeae38e24f0ca806043c225200eca87a559008f2ea5d95df1b38225530ec0a87e11c408c21d950c6c4ec9ae61d53f7084182308765431b13b26b98754ebc21048cc261c150c2d0a1965d4c0362f143190cae61d8153f5086432b987605e142190d0ae61d817f508613526b98754fdc2104d49ae61d53af084123ba986540e46a104caea601d93ce981124a9087653f284084210ec0a7a1b04caea601d93ce981109876543201132ba986540e46a104caea61950391a8442010876053d0d824f530eca87610d0a041d8014f436082903b2a1916182165d4bb2e335a704205a1d950c84c40aa61d950ec20981084302a1e26c1273986004320a4204f30ca807854c810f2e61d9756941826042610c0a989b090c432a5d975f2b192a86241952edaf958c918324ba8765d5a61c40aa61d950f1208c1925d4bb2e2d30e2657300eca9cf8408a1905d4bb2fbf1632450c832a5d97df0b19228641952ecbaf858c914320ca9876f1c2c64893cc302a01e15314230ca9876e1628648919cc3b002105213526ba9874c3a2100a1d9410c02d2f8014c3b2a1d84a15148706432151239876004320a4241530eca87d5048eea61d941316185108765043200a14876503200a31876540201c1324ba98765eb861c521c1950c805)))
def minorLeaf11 (i : Nat) : Nat := (if i < 6 then (if i < 3 then (if i < 1 then 0x47f047b84772473746ff46c7468800004642460e45d6459e4566452044e544a6446e443643f043b84372433742ff42c742934258421241cc41910000414b410540cd409900000000405340180000000000003fd200000000000000003f8c3f463f0b3ec900003e873e413e063dc03d883d493d0a3ccb3c8500003c4d3c0e3bcf3b893b433b0b3ac53a8a3a4f3a1f39eb39a5396a393238fe38c6388738530000381f37dd0000000037a5376d373236f036b1367d3645000035ff35b935813549351134dd349b346000000000341a33db0000000000003395334f0000330932c30000327d3242321231d73191000031560000311000000000000030d130960000000030570000301c2fdd2fa22f672f2c000000002ee6000000002ea0000000002e5a00002e142dce2d882d4200002d0700002ccf000000002c972c5f2c192be12ba22b5c0000000000002b1d2ad72a8a2a482a090000000029c30000000000002984000029452911000000000000000028d228852843280f27d727982760271a26d80000268b264c260a25d625902555251a24df24a70000000024682422000023ea23a40000235e231822e022a80000000000000000000000002262221c21e1219f2159211e20e6000020a000002061201b1fe300001f9d00001f650000000000001f181ed61e9e1e511e0f1dd01d9c00001d4f1d0d00001cd5000000001c881c46000000001c001bb31b71000000001b2400001aec00001a9f000000001a601a1a000019d419991961191400000000000018d5189d000000001850180e17cf00000000179400000000000000000000000017550000000000000000000000000000171d16d7169c166100001629000015ea15ab1573153b000014f514b6147e00001446000000000000140e13c8138d1359131312d81292125a0000121411ce11961150111810e010a8000010620000102a0ff2000000000000000000000fb700000f7f00000f470f010ec900000e9100000e4b000000000e13000000000ddb00000d990d570000000000000d110ccf00000c89000000000c4a0000000000000c0f0bc2000000000b8a00000b480000000000000b0d0000000000000ad20000000000000000000000000a900a5800000a0b0000000009d7098a0956091008d808a0086c00000000081f000007e007a800000000000000000000000000000000000000000774000000000000072b0000000006e206ae066500000623000005da000000000000000005910000054f00000000051404e0000004970000045c000000000421000003df03ab036200000000032702f30000000002aa0000026f000000000000023801ef00000000000000000000000001bb000000000000000001800000014800000000010200bc0084004c00060000000000000000000000000000 else (if i < 2 then 0x82eb82b00000000000000000826a82240000000081e2000000000000819c000000000000815d000000000000811b00000000000000000000000080d9000080a5000080630000000080217fe60000000000007fa000007f680000000000007f300000000000007eea000000007ea87e697e2a7de800000000000000007db400000000000000007d727d370000000000000000000000000000000000000000000000007d037cc800007c897c4300000000000000000000000000007c087bcd7b8b000000000000000000007b507b1c7ae100000000000000007a9f7a5d0000000000007a1b000079ce00007988794d0000790b78c5000000000000000000000000000000000000000000000000000000000000788a000000000000000000000000000000000000000000000000000000000000784f000000000000000000000000780d000000000000000000000000000077ce00000000000000000000000000000000000000000000000000007781773b00000000000000000000770076c576860000764b760975ca758b7550751174cf749b745c00000000741d73e273a373610000732672e400000000000072a900000000000000007267723371f871b6000000007177713c70f670b4708070416ffb00006fb500006f766f3b6efc6eba6e786e2b000000000000000000006de50000000000006d9f00006d686d346cf96cb70000000000006c786c3d00006bfb6bc76b8c6b4a6b046ac56a866a406a0569bf697d6949690a000068cb00000000688c0000685100000000680f67db6799675a00000000671b66dc6696665b000000000000661565d300000000659f00000000655d00000000652264e7000064ac646a000000000000642f0000000063ed0000000063ab0000637000000000633500000000000062f3000062b800000000627d0000623700000000000061f561c1618661406105000000000000000060c3000000000000608f0000000000000000000060580000601d0000000000005fed5fb2000000005f700000000000005f2700005ef700005eb50000000000005e735e405e0c5dce000000005d93000000005d630000000000000000000000000000000000005d2f0000000000005ce900005ca300005c7300000000000000000000000000005c3800005c0000005bba5b7f00005b395afe5abf00005a795a4159fb59b5596f593458fc58bd5885584d581257d3579b5755571a56df56995653561855d9559a5554550e54d3549b5467542f53e953b1536b533052fc52c4527e5246521251cc5194515c511650db50a3506b50254fed4fb94f814f494f034ecf4e974e634e1d4de24da74d614d260000000000004ce04c9a4c5b00004c1c4be4000000004b9e4b584b124acc4a914a564a2649ee49ba4974493c48fd000048b74871482b else 0xcd6d000000000000000000000000000000000000000000000000000000000000000000000000cd3200000000000000000000ccf0ccb50000cc68cc2200000000000000000000000000000000000000000000cbe7000000000000000000000000cbaccb71cb320000cafecac300000000ca840000ca49ca0ec9cfc989c94ac90fc8d0c88ac84bc805c7bfc784c754c719c6e5c6b10000c679c645c6030000c5c1c58dc559c525c4f1c4b2c46c0000c434c3f5c3bdc377c331c2f6c2bbc275c22fc1e9c1b1c16fc130c0f8c0b2c06cc026bfebbfacbf66bf20beda0000be9bbe59be130000bdd4bd8ebd48bd060000bcc4bc7ebc3c0000bbfa0000bbb4bb6e000000000000bb2fbaf0baaeba6cba31b9f6b9b7b978b9440000b909b8c3b87db83e0000b7f8b7b2b76cb72ab6ef00000000b6a90000b66eb628b5e2b5a3b56f00000000b52db4e7000000000000b4a5b466b432b3ecb3aab368b334b300b2bab274b235000000000000b1efb1a9b163b128b0e2b09cb056b017afd8af99af5aaf1b0000aedcae96ae50ae15addaad94ad4e00000000ad08acc60000ac80ac4cac0aabc4000000000000ab90000000000000ab4e0000ab1aaadfaa99aa530000aa18a9e4a9a9a96a0000a924a8eca8aa0000a868a826a7eb0000a7a50000a75f00000000a71da6d7000000000000a69c00000000a661a629a5f1a5b6a57ba540a4faa4c300000000a488a442a407a3c1a386a34ba30ca2c6a280a23aa1ffa1c4a18900000000a14ea113a0e3a0a1a06da03900009ff79fb19f799f459eff0000000000000000000000009ec000000000000000009e85000000009e4300009e089dcd9d9200000000000000000000000000000000000000009d50000000009d0e00009cd39c919c4f9c1400009bdd9b979b5c9b169adb00009a9500009a4f0000000000009a09000099c399889950991c98e4989e9858000098120000000097da979b000000000000975c0000971696d7969c9661961b95e7000095ac9571953d950694c0000094859451941993e193ad9375933d00000000930592cd0000929200000000924c921191cb9190914a00000000910490be907c904190068fc78f8f8f508f1100008ecf00008e900000000000008e4a8e128dcc8d868d408cfa8cbf8c798c3300008bed8bae00008b6800000000000000008b308aea8aaf8a69000000008a2e89fe89c3897d0000000089420000000000000000000000000000890788d3888d88520000880c000087c600000000878000000000873a000000000000000086ed86ab86658623000000000000000000000000000085d6000085900000855500000000000000000000850884c6000000000000000000000000000000000000000084840000844500008406000083c000000000837a000000000000832d)) else (if i < 4 then 0x9c8441342a987654a08c24697530e0b46843898a43832a10a8921e5854c351b14308084e01d8012833818a3b02821118921e05d4c351b1430c084e421d81282c8a12d4c3b1c8441243cb0a986a362861098a43832a10a8954c3832a1c84112487065432015123ba0987654b122084caea601d9528d8811248706543201512387650430213123b0a987654b1220c0f67bf64b0000000000000000f60500000000f5bff580f53af4ff0000f4c4f49000000000f4510000000000000000f40ff3cd00000000f3870000000000000000f34c00000000000000000000f31400000000f2dc00000000f2a1f26df232000000000000000000000000f1f3000000000000f1bf00000000f18bf157f127f0f3f0bff08b0000000000000000f0500000f00e0000000000000000efc8ef82ef47000000000000ef01eebb00000000000000000000000000000000ee7500000000ee41ee09edc7ed81000000000000ed4ded07000000000000eccf00000000ec97ec5fec190000ebd30000eb9feb590000eb13000000000000ead40000ea9500000000ea4f00000000ea100000e9cae984e950e920e8e5e8b1000000000000e86b000000000000000000000000e81e0000000000000000e7d10000e78b0000e75000000000000000000000000000000000e70700000000e6cce68a0000e6410000000000000000e5f80000e5b6e56d00000000e53600000000000000000000000000000000000000000000000000000000e4f4e4aee46f000000000000e43be4000000e3ba0000e37f0000e340e30ce2d1e292e2570000e211e1cbe17ee13ce0fae0b4e075e03ddffedfbc000000000000df81000000000000df3bdf00debede8ade48de10ddce0000dd880000dd4ddd19dce1dcaddc79dc41dc0ddbd9db970000db58db12dad3da8d000000000000000000000000da4b00000000da170000d9e30000d99d0000000000000000d965d92d00000000d8f20000000000000000d8be0000d87fd8390000d801d7c20000d77c0000d744000000000000d705d6c30000000000000000000000000000d684d642d6000000d5b300000000d57400000000d52e0000000000000000d4f3d4b800000000d4720000d433d3ff00000000d3c70000d3880000d3420000d303d2c4d285000000000000d23f00000000d1f9000000000000000000000000d1ba000000000000000000000000000000000000d18200000000d14300000000d104d0c50000d0910000d056d01bcfd500000000000000000000000000000000cfa10000000000000000000000000000cf5f0000000000000000cf190000000000000000cee500000000000000000000ce9fce5d0000ce2900000000000000000000000000000000cdeecda100000000000000000000000000000000000000000000000000000000 else (if i < 5 then 0x46132ba0987654d3620854e1d9410c084c4cae8261d9534d182132b0a987654d3620c4c9aea61d5030488411487065432015153876504302131324ba987065c3461c4cae8261d9528d88212a90876543b0844775300eca960440891dd4c03b2a51f10225530e0ca87e1046121c1950c80544cae8261d953c5882142a98765403a08a26561530eca9e2c418c243832a1900a8995854c3b2a78b10670290e0ca8402a2685961530ed47c58c2132ba098765f1620820521c1950c8544d0b2c2a61da8f8b18426574130ecbe2c410512d4c3b2a1c84409498765432041342cba90876a3e2c608995d4c03b2f8b10230290e0ca8642a2685961530ed47c58c2132ba098765f162084d4aea61d943c50851342c0ba9876a3e2c618995854c3b2f8b1062685817530ed47c58c3181487065432150342cba90876a3e2c608512d4c3b2a1c8441352ba987605f1421848d2ea61c1968f887123a9876054a28e30290e0ca8642a2685961530ed47c58c2021380760054d0ce0e28ec0a0864462685817530ed47c58c3132b0a98765f1620c084e421d815382c8d12d4c3b21c844121390876054e0b230290e0ca8642a26574130eca946c410954843b2a1d84212a98706543e0822e90e0ca86402a20530eca800721444ca8261d950ec21a38c3832a1900a8ba43832a1900a89a95cc3b02a70a10c2654130eca87610c084a1d9410c864dc521c195080541c521c1950c8544caea601d9528d88112a98706543b082270eca086042624775300eca9470408954c3832a1e041132b0a987654a3620c5921c1950c80544caea601d9528d881132ba0987654d162098521c1950c80544cac2a61d95345883113876504302131648706543201511387650430213132b0a987654d1620c44e1d9410c084cd8521c195080544aa61c1950e82089a43832a1900a98a43832a1900a891d854c3b2a58a1068630e0ca86402a2690e0ca86402a24761530eca962841998a43832a100a818a43832a190a891dd04c3b2d8a10424775300ecb62840811a5d4c3832d1a10e24761530ecb628418929dd4c3b2850910a084b530eca87211048ea61d81528a38921e5854c3b51b143080c51d81410c88c48ec2a61d96c50831425a98764390882427210ec09416448eea601d528d081131487065420151243cb0a9865a36286118a43832a100a8921e05d4c32d1b1430d0c61c19508054494eea61d81284885731487065420151314870654201513487065420151243c0ba9865a3628618109c843b021d0594314870654201503148706542151243cba9086a3628608121e5d484351b143044c521c1950854090f2ea421a8d8a18204697530e0b468438921e5854c351b14308490f02ea61a8d8a18624a77530ec1424428212d4c3b29c84413148706542150243cba9086a3628608212d4c3b2 else 0xcc4e1d9410c084c48ea61c019528d88b01387650430213123a98700654a3622c4a61d80150ec25889c3b2821810988a43832a1900a8a43832a1900a8154c3832a1d841132ba9807654f946044caea601d953e588112a98706543f88226574130eca9f68c109925d4c3832fca30e2290e0ca86402a290e0ca86402a26575300eca8f28c08954c3832a1bc41132ba09876547b46084c92ea61c195e5187132b0a987654a3620c4a8261d950ec21995d4c03b2a29b1024775300eca9450408995d4c03b2a6ca30225530e0ca87b1044cac2a61d9528d88316487065432015102980076543a2ac285530eca087411860aa421d950ec2109a95d43b2826ca10a2c90e0ca86402a2240130eca87456c60aa421d950e8a10995854c3b2a75b106264d7530ea81b2442030a43b2a1900a89925d4c3832eca30e205530eca87450440aa61d950ec20884c3b2a1900a00bb02a1901189935d4c32a01a910824b530ea86069110051d8150c808c40e1d950c084d8051d8150c808c4856601d50c0d2a8823b02a19011881c3b2a18109901dd4c3b2a514102a024e0ca08644ea028ec0a864046255210eca8745088eea601d9528a081172a98706543a2822d30ec0a864022a8ec0a086404626574130eca9b2c410995854c3b2a6cb1062a70eca086042622900eca86402e2a70eca08604262a70ec0860426264975300cb8e8c38954c3832a1d841023ba9870654a3221c48ea61d8150e4238195d4c3b2a05091082657530eca814244209935d4c3aa050910826575300eca946c40891a5d4c3832d1910e2530ec0a8614128661d8150c8050aa61d8150e423811dd4c3832a51910e25530ec0a87211c0caea61d95028488412098765400390a2255210eca87450808601d80150e433894c3b02a18504a02190876054390b225530e0ca874504486601d950282a894c3b002a1c84b132ba9807654f362044cae8261d953cd882132ba0987654f346084cac2a61d953cd8831326ba987540f122104cae8261d953cd8821324ba987065f3461c4aa61c1950f8a0899403b282190c892403b2a1900b8b9c3b282181098995d04c3b2a71a3040624e0ca08644e2854130eca87610c4c9aea61d50384884121598076540d0aa26497530e0cbc68c38a1965d4843af1a363044caea601d938d181121598076540d0aa06497530e0c9c68c38ca154c3b2a1d045121598076540d0aa24900eca8602e242b300eca81a15450cb2c2a61d78d1b18426574130ec9c68c10189383282113b9893832802113810ac38302a06063531270650042271532b0a98764a3620c4c9aea61d43848841432cb0a9875e346c61010acc03b2a068551324ba98706e3461c521c1950c80544caea601d9528d88112a98706543a28205530eca86121104aa61c1950f0a088a43832a1900a8a154c3b2821d0))) else (if i < 9 then (if i < 7 then 0x1048e61d81502825011dd4c3b2858a1080477530eca1628420954843b2a1f942125a9876430f088264975300cbe6cc38954843b2a1f142125a9876430e08826574130eca986c4109925d4c032f1b30e2730ec0a86402255210eca87a5084caea61d8152cd086125a9876430c088264975300cb86cc38a043b28181098a11d4c3aa59470423a987653b28e2810eca064262ac5530ec8741140d4aea60192cd8811342c0ba975c366c618a043b28190981a95d4c03259b10206a575300c966c408a11d4c3ad947094987654320423ba980765f0220448261d815038298ca4c3b2990219a4c3b2a19020939dd4c3b2850910a28657530ec0b6684309a4c3b29902094c3b02a18114a14487065432015132ba9807654a362044aa61c1950ec20891dd04c3b2a51b104255210eca87610848aa421d950ec210195d4c3b2a06a91080828ec0a86404624774130eca946c4109935d4c3aa06a910824697530e0cb474438954843b2a1d8421418706543201512087065400390c46270eca0860426e270eca08604262530ec0a8618928086421d8150f42c989c3b28218109891dd04c3b2a51b104255210eca8761084aa61c1950ec208995d4c03b2a51b10226575300eca9d6c408954c3832a1f541192a90876543a2843255210eca8761084c92ea61c197ad187132a09876054c342384a421d9410f0a720a43832a1900aa0c3832a1900a88a43832a1900a8195d4843b2a51b11002500eca0864322657530eca09868428954c3832a1d841714806543201541480765432017132a09087654a3623d0521c1950c8055061c1950c80544caea61d94130d0857148706543201511487065432015132ba9876504c342144aa61d9500f0a2a8a403b2a1900ba8a43832a1900a899504843b2a51b11e82900eca86402e2290e0ca6402a22500eca0864322290e0ca86402a2654130ec0a98684700a43832a190a80a43832a1900a889403b28218c8995d4c03b2a51b10225530e0ca87610496a61d950c08a209954c3832a05a91142530ec0a861692808eea61c19528e087132ba9807654a3620448ea61d8150f023892d4c3b2a18624411387650430213132ba9876540c522104c9aea61d503148841234ba987065a3821c4caa61c19502d488a12987605430b49425530e0ca874504661d8150c804c4e1d9410c084cc61d9410c084c4caa61c19502d488a81387650430213121980765430c4aa0657530eca818a442091d4c38032a51b1162477530e0ca9470438954c3b02a1e04711387650430213132ba9876540c522104aa61d950c3122089c3b28218109b09bb028218112090cc03b2a186255132ba9876540c5221004e1d950c084cc4e1d9410c084dc4e1d9410c084d84e1d9410c084c4caa61c19502d488a12987605430b494043210ec0a87816444e1d9410c084 else (if i < 8 then 0x9876543a08a14e5530eca8741140c92ea61c193ce1871352ba908764f3622050cb2ea421d7ce1b18226497530e0de70c38954c3832a1f1411326ba987540e182104d4ae421d9538d888132ba980764e386040c92ea61c1938e1871972a9876543a08a26574130ec9c74c109935d4c3a870c10820d00eca8643026a57210ec9c6c4409925d4c38371c30e25530e0ca8765044caea61d81528d0861458765043021314587650430213132ba9807654b362044caea601952cd8810423a9876543c28e0847530eca87851c4caea61c1528d0861458765030213132ba980654b36204508ea61d9530a388243832a190a902d4c3b2a188440025a9876543c08824a775210ecb604440954c3832a1d84112a98706543d0822641730eca9c2c4492d4c3b2a180844158765043021312a98706543a08224775300ecb62840891dd4c03b2d8a10224775300ecb628408121e5d4843b61b1430408d2ea61c1970d087132a9876504a08c24617530ecb628448941dd4c3b2850910a284b530ec8781104aa61c1950e420891dd4c03b261910226e5530eca874114090f2ea421d70d8918224a775210ec962444014c3b02a18724a02987605430d4942410eca08601857c4aa421d950ff2111dd4c03b2a7e11022253000eca87855848261d81500faa9892d4c3b2187e44120987605403eaa6264975300cbfacc38c4c03b2a19010b154c3b2a01d045120987605403d8a624b530ec861d51048261d81500f62989925d4c032f5b30e255210eca86f5088eea601d951e0881125a98764307888264975300caf2cc389cc3b02a19008954843b2a1f54223ba9807654e8220448261d81500f5a9892d4c3b2187444213ba9876054b342184c92ea60197a59871798076543202102980076543c2ac2657530ec0a96684309b95d43b2826ca10a24130ec0a8078d4c496a61d90c36220904c3b02a01e3531324ba98065d9661c0caea6019531d8811432cb0a9765d786c6109b95d4c3a8262a10a06a575300ca98ec408b91d4c3aa5947139876054320112a90876543f4844775300eca9e84408904c3b02a01f153125a9876430f288264975300cbeacc389cc3b02a19008954843b2a1f24223ba9807654e422044caea421d9530d888112980076543c2ac24130ec0a807a54c84eea421d9530d888125a9876430e288e26575210ca986c4409925d4c032f2b30e29300eca864042c5530eca807411458aa61d9500e8228904c3b02a01e153125a9876430d288264975300cbaacc38843b2821810991dd4c03b2a621102285530e0ca87610448261d81500eca98904c3b02a01d9531832ba976054b34218496a61d90c30a20b195d4843aa61b110264975300cb8acc389cc3b02a1900811dd4c383259910e24930ec00a7212c49aa61d950e8228924c3b0029c84b023ba987650b142 else 0x876054c342184aa61d9410e8230995d4c03b2a75b10225530e0ca87d5040aa61d950c3aa20c954843b2a1e9421326ba987540eb82104caea601d953ad8811324ba987065eb861c4aa61c1950f0a0814c3b02a18584a12a98706543c282205530eca87850440aa61d950ec20884c3b2a19008195d4c32a01ac1082040eca08645820b0eca8604266057530eca86b0c080195d4c3b2a61b1022048eca08640402f30ec0a864022657530ec0a9ae843091cc3b002a1d94b125a9876430c0880657530ea098a842891cc3b02a1d94b1223a987654c28e2530ec00a87652c4caea61d41315085132a0908654b3623c08ea61d950f0a38195d4c3a8262a10a26575210ca966c44091cc3b02a1d94b123a987654c28e26417530eca9a6c4489054c3b2a1d849132ba9807654d786044aa61c1950f5a08995d4c3b02a6aa10c2705750eca09aa8428995d4c03b2a6bb1022654130ec0a986847094843b2821e14e01487065432015018706543201511487065432015032ba9087654a362204caea601d9530d881132ba9876054c342184521c1950c805449ea61d9500f0a28892cc03b2186055132a09876054c34238448e421d81530ac92d4c3b2a18084412987600543a0960477530e0ca98684380ac3b2a18109894c3b02a18514a12a98706543c282a30eca08604265530eca860211008eea61c19530d08712a98765043a08ca2ec0a086044822b0eca0860426e2d00eca86043002b0eca860426e2b0eca0860426c2b0eca086042682d00eca86043082aec0a08604482530ec00a87412c4caea601d953d618112a98706543f4820657530eca81e70420154c3b2a187944132ba0987654f5a6084c92ea61c197d6187132b0a987654d3620ccae8261d9508d88212a98706543d48205530eca861a5105caa61d9500e8228a1c38032a190b0b954c3b2a01d045182a98765043a08c2641730eca9cac448a954843b2a1e9421326ba987540d3821045a01d950c08604caea601d953558811324ba987065d5861c4cac2a61d9534d883132ba9807654b586044aa61c1950ed208195d4c3b2a051c10826575300eca986c408995d4c03b2a61b1022a5530eca08741184c82ea61d952d588911680765430218132ba9807654b562044aa61c1950ec20811dd4c3832a61910e2530ec00a87212c661d8150c804caa61d950c2822011dd4c3832a61910e25530e0ca8785044a61d80150e42589c38032a190b0995d4c03b2a79b10205530eca861e1104caea61d8153cd086132ba0987654f3a6084c9aea61d503c60841324ba987065f3861c50cb2ea421d7ce1b18226575300ec9e70c081935d4c3b2878c1080657530eca1e30420a1965d4843af9c3630454c82ea61d934d8891a729876543a08a2865961530ebe74d8c2132ba098764f3a6084c9aea61d43c60840a72a)) else (if i < 10 then 0x917687650430213172a09876543b0862ed0eca0860426a62417530ec9f2c44a18905d4c3b2fcb11225530eca08741184aa61c1950f9a098905d4c3b2a7bb11246217530eca9eec44d989054c3b2a7bb1122a2010eca8643626417530ca9eec448b1504c3b2a1d8431478076543021853120ba98764f762244caea601d9539d88143120ba98765f762244aa61c1950f1a08a154843b2a1d8422310ba987654d762244caea61d81534d086132ba9876054c542184840261d950f5ad89905d4c32a6bb112e62417530ca9aec44890438302a01da64132ba9807654c762050c482ea61d975d8891320ba98654d762244caea6019531d8811352ba098654d762088c42ea619535d889132ba987054c5421acc482ea619535d8891326ba987540c5a2101c8ea61d950f4a38391d4c3b2a1e947132ba980654c762050c482ea61975d8891723a987654d28e25530eca0874118496a61d950c28a209154c3b2821d046016876543021312a98706543e48262575210eca9a6c44109dd4843b2a69b1102495210eca87c9090c482ea61d97d58891324ba987065e5a61c8c482e61d953958892310b987654e5622460aa5d9410e823598905cc3b2a72b112242010eca87c96c0c9aea1d95034e8841932ba876054d34218550aa61d950ec210a1cc3b2a190109905cc3b2a72b112e6241730eca9cac4489935d43aa069d108230520eca807416045e01950c08610c482e61d9539588943120b98765e562244c92ea1c197569871687650430213018765430201c132ba9807654c562044caea601d95315881124a90876543d484264d7530ea8187442298905d4c3b26ab11226497530e0cb8b4c38954c3832a1da41132ba9807654d362048c42ea61d952d5889132ba9807654d3620454aa61d9410e8231084003b2a01d069112009876543b0b62420130eca87696d440a001d900e83488c1483b2a01d058132ba9807654b562050c482ea61d96d588912a98706543b08225530e0ca87c1044caea601d953858811320ba987654f162254c482ea61d93c58892310b987654e16226cc482e61d9538588911687504302131320b987654e16225cc482e61d95385889116875043021343120b98765e162245a1d9410c084c4aa61c1950f0208995d4c3b02a60a10c26417530eca9a2c448954c3832a1d841168765043021312a98706543a082265530eca087411848c2ea61d952c50896013875430201c123ba980765b1420448eea601d96c5081123ba980765b142044caa61d9412823590985d4c3b2d8a11228657530ec0ba684309185d4c3b2d8a112e42617530ecb628448a12d4c3b21e84412980706543c29a2270eca86040382aa6ec0a84004225530e0ca87610496a61d950c1422094c3b002a1e04b023ba9870654c3a21caa61d950c1422094c3b002a1e04b132ba9 else (if i < 11 then 0x8383832a181158954c3832a1d841132b0a987654f3620d0aa61c1950ec20891054c3b2a1d849118700654321602a98765430f4882253000eca87a558482a61d950ec24891dd4c3832a71f10e064d730eca81fb8420a196054c3b2fee363084cac261d953f71821324b987065fdc61c84c2ea61d953cd889122a90876543e2842cc6ec0a840042224730eca009a5488ee8261d952c0882192a8765403a08a34656130eca9c6c410c95043b2a1f1421326b987540ebc2105c21d950c08604c92e61c197af1871224706053202823b0a987654b0220c08eea61c19538e08712987600543b096e30eca086042702f0eca086042602610eca8643622010eca8643622f0eca0860426c2ce0a086044802f0eca8604266574130eca8d6c410c154843b2a1f1421326ba987540d9c210482421d9500f62c09925d4c3832ece30e6057530eca8ef8c0883c3b2a18109883c3b2a18109891a5d4c032a71310e2cf0eca08604262cf0eca0860426a5530eca807c9145201d950c086044a6001d950f4ab0995d4c3b02a7aa10c2a6010eca86436241210eca807c9604caea601d9538d88114676050430224120908765403d4b06575300eca8d2c408904843b2a01e258132ba987054c542180cac2a619535d8831432cb0a9765d7c6c610391d4c3b2a1f1471326ba987540c5c2105c8ea61d9538a39954c3b2821d046023ba9870654e3421c040a01d9500e83480bc3b2a1810989b3b0282181120a954843b2a1f1421324ba987065d5c61c842001d9500e8348081403b2a01d069112080706543d2dc0477530e0ca9c6443811dd4c3832a71910e241210eca807416051e1d9410c084c540a421d900e82c0211d4c3b2a1f1470423a9876543e28e28f0eca0604262847530eca9c51cca8261d950e421811d854c3b2a5891062500eca8604304775300eca9604408995d4c3b02a78a10c12930eca86408286417530ecbe6c448995d4c3b02f8a10c246010eca8636344b530ec87c1104d0b2c2a61db8f8b1842410eca86043065530eca087411848ee8261d96c5082332a9876504a08c0487975210edc6c50c10234ba987065e3421c5096a61d90f8220954c3832a1d84112987600543d0962454130eca87610c4e1c01950c8584a8261d950ec2181084c3b02a1f05a12987600543d0962530ec00a87612c4480261d950ec2d811dd4c3832a69c10e82240130eca7616c4aa61c1950fa2089254843b2a1f5421326ba987540e9a21060a8261d950ec21909dd4c3b02a69a10c26497530e0cbd34c388154c3b2a1d841109876543201102a9876543b0824020eca0864582040eca086458e0240eca08645820d0eca8604264077530eca9a50409815d4c3b2a1ad30260240eca0845840240eca0865827300eca864043130ec0a86402325530e0ca8761048c42ea61d953e588 else 0x40aa61d950ec20884c3b2a1900891dd4c3b2a075a108246d7530ea81d68420904003b2a01d0691234ba987065eb221c4a61d80150e4258954c3b2a01d0451187650430213120000876543a0de2477530eca142442891dd4c03b2d8a102254774130ecb628410a12d4c3b21f5441267605043022412780765430218027a9876543b0842f30ec0a864022410e0c0a81a19044a6001d950f8ab08c38032a190b08c38032a190b08c38032a190b30c3802a190b08c38032a190b20c38032a190b00c38032a190b0154c3b2a183a4432ba9807654f3620448ec2a61d953cd8831234ba987065f3c21c4aa421d950fca10995d4c03b2a79b10226a417530ec986c4488195d4c3b2a79b1022110eca86042600e6eca864003e6057530eca86bcc080195d4c3b2a79b1022d0e00ca8642c26575300eca9e6c40c0c43b2821810988c43b2821810988c43b282181098195d4c3b2a051f1082657530eca8147c4200c43b2a1810989935d4c3aa051f10824697530e0cbe68438894c003b2a1d856125a98765430f0882765530eca09e28428894c003b2a1d856032ba9876504f14214494c2ea61d92c48891187006543216187006543216320a98765439092230e00ca8642c0657530eca09e284289a15d4843b2f9f163040d0aea421d97cf8b1820765530eca09e284289a154c3b29d84913420ba9876f3e2c618512cc3b2a1f8441234a987065f3e21c4d0ac2a61dbcf8b184068575210ede7c58c10234a987065f3e21c0d0aea421dbcf8b1822685530ecb61248ee8261d9538d882032ba9876504fd42144928261d950fca1))))
def minorLeaf12 (i : Nat) : Nat := (if i < 1 then 0xca9e6c40812d4c3b2a1870442a98706543108206575300eca9c6c40811d4c3b02a1f147132ba0987654e362084aa421d950f8a1092d4c3b2187044132ba0987654e362084201d950c086048ea61d81538a38954c3832a1d84119876054320112a98706543b0824241530eca876124842a61d950ec248954c3b2821d046a120a9876543b09222010eca8643604b530eca861a11050aa421d950ec2109cc03b2a190109054c3b2a1d8496120a9876543b09224b530ec861a11041d81410c089008ea61d8150f4a38195d4c03b2a69b1028241530eca761244aa61c1950ec20989054c3b2a1d8493120a987654b092247530ec0a9a51c4caea601d9530d88112a98706543c28225530e0ca876104661d8150c804096a61d950c30220154c3b2a186044098765432004120a9876543b09226574130eca9a6c410954843b2a1e942125a9876430c0880e5530eca807411408ea61d8150f0a38195d4c03b2a61b1022855300eca8761204caea601d9530d88112a98706543b082247530ec0a9851c6601d950c808aa61c1950c4208843b282181098b154c3b2a01d04510876504302131498765320041087650430213042a98706543b082085530e0ca87610448ea61c152ca38995d4c03b2a51b10225530e0ca8745044aa61c1950ec208cc3b02a19008995854c3b2a51b106254130eca87610c4521c1950c80540caea601d9528d881025a987654309088285530eca08741184521c1950c80544cae8261d9528d88212a90876543a284028ec0a08640462290e0ca86402a26574130eca946c410954843b2a1d84201487065432015123a9876054a28e05342941461a1680000000000004fc80000000004f080000009c74d3c0000000000000000000000000000000098480000000000004b2800128400000000000000000000000000000491641c00000047200000008c480000000000000000000000000000000114388400000000000000000000000000433610e00082980000000000000000000000000000000000000000000010180000000000fdd7d6bdc9e66ef875e8000000e7e0003929c160006e636600000006aeb478000000000338c000caf638000000000061500017debb45baace80000000002bfc00000055ca9f9486a134ea26652d2000497000000000000023a115a000000000000000000000010e400041980000007f40001eb8ede000000000000000000000000000000001ca4ddc0000001acc0000000000000d0664c00000000006182ec8000b4a0000000000aea0002a08000a0400000000009860000000000000000000000000048c00011188163d01d0000000035a18f80000000001738000542000000098800000011180003d61a50b50000264000000000000000000000001f40b403c8000000000020800000c0000000000000000 else 0x4aa61c1950ec208cc3b02a19008c954843b2a1d8421898076543202123a9876054ea8e3300eca8640420ec0a0860448105530e0ca8761044cae8261d953cd882023a98760543f28e06575300e)
def minorLeaf13 (i : Nat) : Nat := 0x0
def projectionTable : Nat → Nat × Nat × (Nat → Nat)
  | 5 => (1,0,minorLeaf5)
  | 6 => (2,0,minorLeaf6)
  | 7 => (4,3,minorLeaf7)
  | 8 => (25,10,minorLeaf8)
  | 9 => (224,13,minorLeaf9)
  | 10 => (1158,16,minorLeaf10)
  | 11 => (1977,16,minorLeaf11)
  | 12 => (263,13,minorLeaf12)
  | 13 => (8,0,minorLeaf13)
  | _ => (0,0,fun _ => 0)
def projectionSpec (k i : Nat) : Nat × List SimpleGate × Nat :=
  let (cnt,ow,data) := projectionTable k
  let off := cnt*ow + packedAt data (i*ow) ow
  let tag := packedAt data off 6
  let m := packedAt data (off+6) 2
  let gates := (List.range m).map fun j =>
    let b := packedAt data (off+8+7*j) 7
    (b.testBit 6,b &&& 7,(b >>> 3) &&& 7)
  (tag,gates,packedAt data (off+8+7*m) 56)

def checkProjection (k i : Nat) :=
  let (tag,cs,idx) := projectionSpec k i
  if tag=0 then auditNode mf tokenConfig k i else
    let ws := wideState mf k i
    let m := minorInputs[tag-1]?.getD default
    decide ws.Nodup && cutTest m.pm m.nm (vars m.q) cs idx k m.level ws

def checkRange (k start : Nat) : Nat → Bool
  | 0 => true
  | n+1 => checkProjection k (start+n) && checkRange k start n

def geometryOK (m : MinorData) (level : Nat → Nat) :=
  properB (graphGoal m.q) && !(m.q.testBit 9) && decide (m.level = level m.q) &&
  m.pos.all (fun r => bit r m.pm) && m.neg.all (fun r => bit r m.nm) &&
  extremalGeometry (vars m.q) m.pos m.neg graph (graphGoal m.q)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem testedProjectedStates : (checkRange 5 0 1 && checkRange 6 0 2 && checkRange 7 0 4 && checkRange 8 0 25 && checkRange 9 0 32 && checkRange 10 0 48 && checkRange 11 0 48 && checkRange 12 0 32 && checkRange 13 0 8) = true := by decide +kernel
end PEqualNP.Outside.L_meta_5002

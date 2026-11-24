import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3172

-- The general reachability calculus and predecessor-graph bounds are adapted from L_meta_3640.
-- Only transitions reachable after one of the three specified OR pairs are retained below.
open PEqualNP.CircuitLowerBounds
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


abbrev Bits := BitVec 132
abbrev Signals := Bits × Bits
abbrev Decor := Sig × Signals

def ofRows {n : Nat} (r : Fin n → Row) (v : Sig) : BitVec n :=
  (BitVec.ofBoolListLE (List.ofFn (fun i => bit (r i) v))).cast List.length_ofFn
theorem ofRows_bit {n : Nat} (r : Fin n → Row) (v : Sig) (i : Fin n) :
    (ofRows r v).getLsbD i.val = bit (r i) v := by
  simp only [ofRows,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [i.isLt]
def pairSig (r s : Fin 132 → Row) (a : Sig) : Signals := (ofRows r a,ofRows s a)
def properPairs (T : Sig) (r s : Fin 132 → Row) :=
  ∀ i, bit (r i) T = true ∧ bit (s i) T = false
theorem pair_sep {T r s} (h : properPairs T r s) : Sep T 132 r s (pairSig r s) := by
  exact ⟨h,fun a i => ⟨ofRows_bit _ _ _,ofRows_bit _ _ _⟩⟩
def faithful (r s : Fin 132 → Row) (x : Decor) := x.2 = pairSig r s x.1
def dneg (x : Decor) : Decor := (neg x.1,~~~x.2.1,~~~x.2.2)
def dbin (d : Bool) (x y : Decor) : Decor :=
  if d then (bin d x.1 y.1,x.2.1 ||| y.2.1,x.2.2 ||| y.2.2)
  else (bin d x.1 y.1,x.2.1 &&& y.2.1,x.2.2 &&& y.2.2)

theorem ofRows_neg (r : Fin 132 → Row) (a : Sig) : ofRows r (neg a) = ~~~ofRows r a := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have h := ofRows_bit r (neg a) ⟨j,hj⟩
  rw [bit_neg,←ofRows_bit r a ⟨j,hj⟩] at h
  simpa only [BitVec.getLsbD_not,hj,decide_true,Bool.true_and] using h
theorem ofRows_bin (r : Fin 132 → Row) (d : Bool) (a b : Sig) :
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

def asRow (cols : Nat → Bits) (i : Fin 132) : Row :=
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
theorem asRow_bit (cols : Nat → Bits) (i : Fin 132) (j : Fin 9) :
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
theorem bit_vertex (m : Nat) (v : Nat → Bits) (i : Fin 132) (j : Fin 9) :
    bit (asRow v i) (vertex m j.val) =
    ((if m.testBit j.val then v j.val else 0) : Bits).getLsbD i.val := by
  by_cases hh : m.testBit j.val = true
  · simpa [vertex,hh] using asRow_bit v i j
  · simp [vertex,hh,bit_zero]
theorem bit_liftGoal (m : Nat) (v : Nat → Bits) (i : Fin 132) :
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

abbrev NodeContext := Nat × Nat × List Decor × CovPair × List BoundPool × (Nat → List (List Sig)) × Nat
def evalMove (c : NodeContext) (op : Nat) (a b z : Decor) (ka kb : Bool) :=
  let (cap,n,ws,cov,pools,links,_) := c
  let un := op==2
  let len := 1+(n - (if ka then 0 else 1) - (if un || kb then 0 else 1))
  if len>cap then true else
    let d := len==cap
    let rs := restCov (getCov cov d) (column d a.2) (column d b.2) un ka kb
    if (rs ||| column d z.2) != BitVec.allOnes 132 then true else
    if !properB z.1 || ws.any (fun v => v.1==z.1) then true else
      let rest := (opKeep un ka kb a b ws).map Prod.fst
      closeChild pools links (cap-1) rest (movedChoice op a b)

def moveFront (ws : List Decor) (op : Nat) (a b : Decor) (ka kb : Bool) :=
  (movedDecor op a b).1 :: (opKeep (op==2) ka kb a b ws).map Prod.fst
theorem evalMove_sound {raw T r s ws pools links note cap a b op ka kb}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : (op==2)=false → a≠b) (hcap : 0<cap)
    (pv : ∀ p ∈ pools, ValidPool raw T p)
    (lv : ∀ tag xs, xs ∈ links tag → Impossible T (cap-1) (List.toFinset xs))
    (pro : proper (movedDecor op a b).1) (fresh : (movedDecor op a b).1 ∉ ws.map Prod.fst)
    (test : evalMove (cap,ws.length,ws,preCov ws,pools,links,note) op a b (movedDecor op a b) ka kb = true) :
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
  change covered (decide (child.length = cap)) (pairSig r s) child = BitVec.allOnes 132 at sep
  rw [deq] at sep
  change column d (pairSig r s z.1) ||| covered d (pairSig r s) (rest.map Prod.fst) = _ at sep
  change z.2 = pairSig r s z.1 at hf
  rw [←hf,←g,rz,BitVec.or_comm] at sep
  have be : ((restCov (getCov (preCov ws) d) (column d a.2) (column d b.2) (op==2) ka kb ||| column d z.2) != BitVec.allOnes 132) = false := by simp [sep]
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

theorem node_sound {raw T r s ws pools links note cap}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (out : T ∉ ws.map Prod.fst)
    (pv : ∀ p ∈ pools, ValidPool raw T p)
    (lv : ∀ tag xs, xs ∈ links tag → Impossible T (cap-1) (List.toFinset xs))
    (checks : testAll (cap,ws.length,ws,preCov ws,pools,links,note) ws = true) :
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
        (test : testPair (cap,ws.length,ws,preCov ws,pools,links,note) a b d = true) :
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
theorem chart_bit (m : Nat) (v : Nat → Bits) (i : Fin 132) :
    bit (asRow v i) (chartGoal m) = (chartSamples m v).getLsbD i.val := by
  exact bit_liftGoal m v i
theorem chart_pairs {m : Nat} {p q : Nat → Bits}
    (hp : chartSamples m p = BitVec.allOnes 132) (hq : chartSamples m q = 0) :
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

def notesOf (m k i : ℕ) : ℕ :=
  match m,k with
  | 15,3 => (#[0x0] : Array ℕ)[i]?.getD 0
  | 31,5 => (#[0x11,0x0,0x1] : Array ℕ)[i]?.getD 0
  | 31,6 => (#[0x118c631] : Array ℕ)[i]?.getD 0
  | 111,6 => (#[0x4652] : Array ℕ)[i]?.getD 0
  | 189,6 => (#[0x11,0x0,0x1] : Array ℕ)[i]?.getD 0
  | 189,7 => (#[0x25294a52] : Array ℕ)[i]?.getD 0
  | 191,6 => (#[0x0] : Array ℕ)[i]?.getD 0
  | 191,7 => (#[0x0,0x0,0x0,0x0,0x11,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x212,0x12,0x0,0x3,0x0,0x0,0x10,0x0,0x1,0x1,0x12,0x21,0x21,0x10] : Array ℕ)[i]?.getD 0
  | 191,8 => (#[0x11,0x21,0x12,0x12,0x12,0x252,0x252,0x1,0x11,0x11,0x11,0x1,0x11,0x21,0x1,0x1,0x1,0x12,0x11,0x21,0x12,0x21,0x12,0x11,0x12,0x1,0x21,0x11,0x11,0x11,0x4474,0x851,0x10842,0x1,0x94434,0x1,0x434,0x274,0x94a94,0x12,0x274,0x8428c461,0x4652,0x21,0x234,0x1288652,0x1,0x11,0x21,0x21,0x11,0x1,0x188691,0x292,0x34,0xa72,0x88634,0x94653,0x4e91,0x292,0x8e32,0x74,0x10ce91,0x292,0x693,0x73,0x292,0x292,0x12,0x243,0x72,0x243,0x243,0x11,0x0,0x12,0x1,0x43,0xe53,0x43,0x73,0x43,0x231,0x11,0x241,0x73,0x234,0x21,0x18673,0x308673,0x12,0x881,0x24a53,0x32,0x823,0x1253,0x43,0x73,0x43,0x233] : Array ℕ)[i]?.getD 0
  | 191,9 => (#[0x110ca51,0x4652,0xca51,0x6539ca51,0x32a4a34,0x2949ca92,0x3294631,0x3294e31,0x4329ca71,0x3294a91,0x43294e33,0x43394a33] : Array ℕ)[i]?.getD 0
  | 191,10 => (#[0x4a51] : Array ℕ)[i]?.getD 0
  | 383,8 => (#[0x0,0x0,0x0,0x0,0x0,0x0,0x11,0x0,0x0,0x1,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x272,0x0,0x11] : Array ℕ)[i]?.getD 0
  | 383,9 => (#[0x8c631,0x233,0x272,0x273,0x273,0x273,0x273,0x272,0x6319c671,0x0,0x0,0x0,0x21,0x0,0x11,0x0,0x11,0x0,0x11,0x0,0x0,0x0,0x11,0x11,0x11,0x0,0x11,0x11,0x11,0x11,0x1,0x11,0x21,0x63,0x1,0x11,0x11,0x292,0x0,0x63,0x294,0x11,0x11,0x13,0x11,0x254,0x254,0x291,0x4874,0xe83,0x4a83,0x8d034,0x4674,0x273,0x292,0x4674,0x4474,0x292,0x4674,0x4a54,0x4474,0x4a74,0x4474,0xa73,0x0,0x8c694,0x118c632,0x8c694,0x292,0x254,0x4474,0x294,0x5254,0x14a94,0x4e54,0x1,0x0,0x5234,0x293,0x2b2,0x4295,0x0,0x5234,0x8c694,0x253,0x242,0xc42,0x62,0x53,0x851,0x5233] : Array ℕ)[i]?.getD 0
  | 383,10 => (#[0x886218c631,0x44318c631,0x273,0x273,0x4a72,0x218c634,0x274,0x218c634,0x4654,0x8c693,0x1886318c631,0xc694,0xc6318c631,0x4310c671,0x218c671,0xce73,0x86618c6328ca31,0xc6319ce33,0x319ca72,0x4338c6338ce31,0x4218c6338c671,0xa5294,0x220cc54,0xad274,0x14c6290a35,0x81a5241,0x4630c634,0x4e95,0x10a94,0x90ab5,0x883214a74,0x1c6b4,0xc718d231,0x42188438c631,0x52b3,0xa5235,0x5290a93,0x1295635,0x348d635,0x148c6b1,0x849ce318ce71] : Array ℕ)[i]?.getD 0
  | 383,11 => (#[0x118c631,0x210c634,0x294,0x86318c631,0x4693,0x86318c631] : Array ℕ)[i]?.getD 0
  | 383,12 => (#[0x8c631] : Array ℕ)[i]?.getD 0
  | 511,8 => (#[0x0,0x0] : Array ℕ)[i]?.getD 0
  | 511,9 => (#[0x0,0x0,0x0,0x0,0x11,0x11,0x10,0x10,0x10,0x10,0x14,0x10,0x0,0x0,0x11,0x0,0x273,0x0,0x0,0x293,0x0,0x11,0x4e73,0x2,0x0] : Array ℕ)[i]?.getD 0
  | 511,10 => (#[0x4631,0x4631,0x4631,0x4633,0x1294a538c633,0x10ca538c633,0x0,0x0,0x11,0x0,0x0,0x0,0x11,0x11,0x0,0x11,0x0,0x0,0x11,0x0,0x0,0x0,0x0,0x11,0x11,0x0,0x11,0x0,0x0,0x0,0x0,0x0,0x11,0x0,0x11,0x11,0x11,0x11,0x63,0x42,0x63,0x11,0x0,0x0,0x0,0x0,0x11,0x11,0x11,0x11,0x11,0x0,0x11,0x11,0x11,0x0,0x11,0x851,0x63,0x0,0x11,0x0,0x11,0x0,0x0,0x11,0x11,0x0,0x11,0x0,0x11,0x11,0x10,0x10,0x10,0x10,0x10,0x12,0x42b4,0x275,0x235,0x10,0x88695,0x118c632,0x886b4,0x12,0x275,0x2d2,0x4e35,0x88a35,0x198674,0x4636,0x253,0x10,0x11,0x10,0x10,0x12,0x10,0x2b5,0x2b4,0x10,0x10,0x10,0x14c75,0x255,0x12,0x8c6b3,0x4e35,0x4455,0x12,0x2b3,0x118c633,0x262,0x263,0x11,0x262,0x11,0x44,0x262,0x11,0x262,0x11,0x0,0x0,0x11,0x63,0x42,0x11,0x282,0x282,0x44,0x44,0x44,0xc22,0xa4,0x43,0xc43,0x44a3,0x1623,0x0,0x43,0x43,0x28842,0x43,0x62,0x294,0x15,0x0,0x2b4,0x11,0x5294,0x88a73,0x2,0x13,0x62] : Array ℕ)[i]?.getD 0
  | 511,11 => (#[0x23294a52,0x218863194651,0x1086528ca32,0x46318c633,0x2318ca52,0x8c42194652,0x2318ca52,0x46318c652,0x2318ca52,0x46318c652,0x8c4218ca52,0x2318ca52,0x88a55,0x2318ca52,0x4652,0x28ca52,0x28ca52,0x46218ca52,0x2318ca52,0x46318c652,0x4a52,0x2238ca32,0x2318ca52,0x4652,0x718c652,0x111c654,0x4652,0x38ca52,0x4a52,0x2228c634,0x510c654,0x4a52,0x2230ca52,0x4694,0x8c634,0x149ca52,0x2739c6318ca72,0x29c6728d252,0x46318c634,0x4e318ca52,0x51a4a52,0x39d4548c6318ca52,0x8c6318ce52,0x2318c654,0x2318c654,0x1284652,0x5194694,0x4e948ca72,0x4672,0x39ce319ca54,0x10a918c654,0x94a54,0x8518c694,0x318c694,0x14a948ca92,0x13,0x14,0x63,0x14,0x63,0x63,0x231,0x11,0x91,0x11,0x11,0x12,0x11,0x63,0x14,0xe23,0x13,0x12,0x11,0x91,0x231,0x231,0x20844,0x291,0x231,0x12,0x11,0x1189255,0x91a4655,0x1124655,0x1189235,0x94a94,0x8d652,0x294,0x8ca56,0xa348ca52,0x8ca94,0x46d2,0x3a4a52,0x44a4a32,0x95634,0x82a465111252,0x8c6d4,0x82a0e239ca52,0x94a54,0x88ab4,0x95293,0x118d672,0x1218e96,0xab4,0xe731da55,0x8ca35,0x1463a4a52,0x4a36,0x1124a56,0x94635,0x658cc5194a92,0x63b4e94,0x8ca55,0x4ab4,0xa38ca52,0xe718ca54,0x5a36,0x822163424a52,0x946b2,0x15a12d4,0x428a858c62224652,0x4a0e8488e36,0x4295,0xb4694,0x8da95,0x95654,0x95654,0x8da56,0x94696,0x14a96,0xb4a55,0x4a56,0x94a54,0x8ca76,0xb1a4a52,0x5656,0x94a55,0x56d4,0x2248ca36,0x2631da55,0x94a54,0x8ca55,0x4a56,0x956d4,0x1d236,0x8d636,0x318ed6,0x4656,0x31cad5,0x1231a4634,0x1194654,0x263a46d6,0x94a35,0x26394635,0x8c656,0x75,0x75,0x75,0x68ca94,0xcd1,0xcd1,0x14,0xc63,0x52b4,0x38d294,0x20c71,0x8d074,0x14,0x4466,0xa5,0x75,0x15,0x148c694,0x5694,0x35256,0x1694,0x0,0xa94,0x11214a4,0x694694,0xa4695,0x8411222] : Array ℕ)[i]?.getD 0
  | 511,12 => (#[0x10c6328ca51,0x10c6518ca31,0x310c6318ca31,0x1c6328ca72,0x46318ca32,0x8c63194e51,0x465294a92,0x140c63194a51,0x65194652,0xe51a4a95,0x463194a92,0x463194a92,0x46318c652,0x8c63194692,0x4e318ca51,0x2518ca52,0x46318c634,0x2528d655,0x4a3194674,0x38c63394a72,0x3a463194a72,0x31c65194a72,0x738c6318ca72,0x46518ca35,0x46328c635,0x231ad63494a92,0x8c6b18ca32,0x31c6318ca32,0x2848c6b194a92,0x94ab18cab2,0xac6318c654,0x94a46318ca32] : Array ℕ)[i]?.getD 0
  | 511,13 => (#[0x18c63194631,0x8c6318ca72,0x46318ca32,0x148c6318c632] : Array ℕ)[i]?.getD 0
  | 511,14 => (#[0x118c6318c631] : Array ℕ)[i]?.getD 0
  | 527,3 => (#[0x0] : Array ℕ)[i]?.getD 0
  | 535,3 => (#[0x0] : Array ℕ)[i]?.getD 0
  | 543,5 => (#[0x0,0x0] : Array ℕ)[i]?.getD 0
  | 543,6 => (#[0x11,0x118c432] : Array ℕ)[i]?.getD 0
  | 699,5 => (#[0x0] : Array ℕ)[i]?.getD 0
  | 699,6 => (#[0x12,0x252] : Array ℕ)[i]?.getD 0
  | 701,6 => (#[0x0,0x0,0x0] : Array ℕ)[i]?.getD 0
  | 701,7 => (#[0x12,0x4a53] : Array ℕ)[i]?.getD 0
  | 703,6 => (#[0x0,0x0] : Array ℕ)[i]?.getD 0
  | 703,7 => (#[0x0,0x1,0x1,0x0,0x0,0x0,0x0,0x0,0x11,0x12,0x0,0x0,0x11,0x12,0x0,0x0,0x0,0x12,0x0,0x11,0x0,0x0,0x13,0x0,0x0,0x0,0x0,0x0,0x11,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x3,0x0,0x1,0x61,0x0,0x2,0x1,0x0,0x0,0x0,0x0] : Array ℕ)[i]?.getD 0
  | 703,8 => (#[0x11,0x252,0x12,0x12,0x12,0x138ce73,0x252,0x252,0x11,0x0,0x11,0x0,0x0,0x12,0x242,0x454,0x12,0x52,0x0,0x242,0x2,0x12,0x10e74,0x51,0x0,0x0,0xa54,0x242,0x0,0x12,0x12,0x31,0x642,0x234,0x0,0x11,0x31,0x694,0x0,0x12,0x242,0x2,0x2,0x0,0x242,0x0,0x222,0x0,0x242,0x0,0x12,0x12,0x12,0x12,0x1,0x0,0x0,0x12,0x32,0x0,0x0,0x51,0x12,0x12,0x42,0x2,0x12,0x11,0x11,0x634,0x2,0x0,0x0,0x12,0x0,0x0,0x11,0x0,0x12,0x0,0x12,0x0,0x42,0xa42,0x0,0x294,0x0,0x12,0x2,0x62a0854,0x12,0x294,0x294,0xa42,0x12,0x18874,0x0,0x52,0x12,0x242,0x0,0x12,0x842,0x11,0x12,0x642,0x242,0x2,0x0,0x4a74,0x2,0x52,0x12,0x12,0x0,0x32,0x242,0x0,0x12,0x294,0x12,0x2,0x0,0x1,0x0,0x31,0x0,0x0,0x0,0x12,0x31,0x12,0x51,0x294,0x0,0x11,0x221,0x242,0x221,0x0,0x11,0x0,0x0,0xa42,0x12,0x12,0x2,0x51,0x11,0x98874,0x0,0x84308c71,0x310a54,0x31,0x0,0x0,0x2,0x0,0x2,0x221,0x42,0x242,0x0,0x0,0x0,0x842,0x11,0x2219ce73,0x12,0x1,0x12,0x0,0x282,0x4842,0x0,0x44,0x4a44,0x44,0x284,0x4,0x44,0xa94,0x2,0x51,0x62,0x282,0x12,0x2,0x54,0x274,0x12,0x94,0x82,0x0,0x62,0x284,0x2,0x2,0x13,0x82,0x294,0x202,0x4851,0x232,0x264,0xa74,0x242,0x0,0x31,0x44,0x42,0x234,0x0,0x4c42,0x62,0x242,0x281,0x4454,0x8a52,0x11] : Array ℕ)[i]?.getD 0
  | 703,9 => (#[0x40028c652,0x4652,0x4652,0x4a51,0x108652,0x4c21a4a52,0x252,0x108a32,0x8452,0x10c452,0x1108852,0x232,0x108a52,0x8851,0x14a5252,0x9cc21a4a52,0x4652,0x188452,0x108652,0x188452,0xca62a4a32,0x108652,0x8452,0x4652,0x110a32,0x108a52,0x8852,0x4a51,0x188851,0x1108a62a5252,0x1110451,0x2830c87210a32,0x23214ab5,0x1294ab5,0x18c3215052,0x88652a5232,0x418a3290892,0xe519ca55,0xc3108a55,0x252946b5,0xa062190a55,0x8c42294855,0x469394a52,0x41c64290a82,0xa062118a52] : Array ℕ)[i]?.getD 0
  | 703,10 => (#[0x1004652,0x8ca52] : Array ℕ)[i]?.getD 0
  | 727,6 => (#[0x0] : Array ℕ)[i]?.getD 0
  | 861,6 => (#[0x0] : Array ℕ)[i]?.getD 0
  | 863,6 => (#[0x0] : Array ℕ)[i]?.getD 0
  | 863,7 => (#[0x12,0x12,0x0,0x12,0x12,0x11,0x12,0x0,0x11,0x12,0x0,0x11,0x0,0x0,0x0,0x12,0x0,0x12,0x0,0x0,0x12,0x12,0x0,0x0,0x0,0x0,0x11,0x0,0x12,0x12,0x0,0x11,0x0,0x12,0x0,0x11,0x12,0x0,0x0,0x12,0x12,0x11,0x0,0x12,0x0,0x0,0x0,0x0,0x0,0x1,0x2,0x0,0x0,0x0,0x2,0x0,0x0,0x1,0x0,0x0,0x2,0x0,0x1,0x0,0x0,0x0,0x0,0x11,0x0,0x0,0x0,0x1] : Array ℕ)[i]?.getD 0
  | 863,8 => (#[0x12,0x11,0x12,0x251,0x12,0x12,0x42,0x12,0x11,0x12,0x12,0x12,0x18672,0x222,0x12,0x12,0x51,0x12,0x0,0x12,0x12,0x0,0x12,0x12,0x12,0x0,0x2,0x12,0x12,0x0,0x32,0x12,0x12,0x11,0x0,0x1ca74,0x242,0x242,0x1,0x0,0x12,0x12,0x0,0x0,0x0,0x11,0x0,0x0,0x242,0x18e54,0x52,0x12,0x2,0x12,0x12,0x0,0x0,0x12,0x31,0x0,0x242,0x2,0x12,0x0,0x642,0x254,0x31,0x642,0x0,0x0,0x0,0x0,0x0,0x242,0x274,0x282,0x0,0xa42,0x0,0x0,0x12,0x14,0x12,0x12,0x0,0x0,0x0,0x0,0x12,0x0,0x0,0x242,0x12,0x51,0x642,0x642,0x294,0x0,0x0,0x0,0x0,0x31,0x12,0x242,0x12,0x12,0x0,0x0,0x0,0x0,0x221,0x874,0x0,0x0,0x0,0x0,0x32,0x0,0x0,0x0,0x0,0x642,0x0,0x274,0x0,0x2,0x1ca74,0x12,0x12,0x12,0x0,0x0,0x294,0x242,0x0,0xc842,0x0,0x0,0x12,0x18e54,0x0,0x0,0x0,0x294,0x11,0x0,0x0,0x1,0x251,0x2,0x12,0x0,0x51,0x0,0x0,0x242,0x12,0x5254,0x12,0x12,0x0,0x294,0x0,0x242,0x52,0x51,0xa42,0x0,0x0,0x0,0x1,0x2,0x1ce53,0x12,0x0,0x0,0x12,0x242,0x52,0x12,0x0,0x31,0x52,0x242,0x0,0x0,0x12,0x242,0x0,0x242,0x12,0x12,0x12,0x242,0x242,0x32,0x12,0x0,0x242,0x0,0x221,0x12,0x242,0x242,0x0,0x0,0x12,0x0,0x0,0x12,0x12,0x242,0x4a54,0x0,0x12,0x1,0x2,0x12,0x13,0x11,0x0,0x0,0x12,0x12,0x1,0x0,0x12,0x11,0x242,0x12,0x0,0x12,0x221,0x242,0x11,0x2,0x12,0x12,0x0,0x12,0xa94,0x294,0x12,0x0,0x2,0x0,0x12,0x31,0x12,0x294,0x0,0x2,0x0,0x12,0xe74,0x0,0x51,0x12,0x242,0x12,0x0,0x0,0x2,0x0,0x0,0x0,0x0,0x31,0x12,0x0,0x0,0x0,0x12,0x18e54,0x63,0x12,0x283,0x282,0x1c844,0x63,0x1,0x64,0x84,0xc44,0x3,0x63,0x63,0x2,0x5242,0x13,0x63,0x63,0x284,0x63,0x63,0xe24,0x221,0x3,0x243,0x4623,0x31,0x63,0x82,0x64,0x221,0x63,0x2,0x13,0x3,0x73,0x73] : Array ℕ)[i]?.getD 0
  | 863,9 => (#[0x20014652,0x28c652,0x4652,0x4652,0x4a51,0x4652,0x8652,0x4653,0x4653,0x8452,0xc452,0x8652,0x452,0x190852,0x452,0x4653,0x8452,0x310c852,0x867414e92,0x8452,0x452,0x8652,0x8452,0x851,0x252,0x8452,0x8851,0x8652,0xc452,0x52,0x1190442,0x8a32,0x8a32,0xc452,0x14a4a52,0x4653,0x8c653,0x190a73,0x44931c855,0x29121253,0x1198e55,0x818d253,0x126314ab5,0x50910d253,0x1121253,0x40d253,0x1590e95,0x2310c853,0x12840c653] : Array ℕ)[i]?.getD 0
  | 863,10 => (#[0x4652,0x4653] : Array ℕ)[i]?.getD 0
  | 967,6 => (#[0x0] : Array ℕ)[i]?.getD 0
  | 999,6 => (#[0x0] : Array ℕ)[i]?.getD 0
  | 999,7 => (#[0x11,0x0,0x12,0x0,0x11,0x0,0x11,0x0,0x12,0x12,0x0,0x11,0x11,0x12,0x0,0x2,0x12,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x2,0x0,0x0,0x0,0x2,0x0,0x2,0x0,0x2,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x11,0x0] : Array ℕ)[i]?.getD 0
  | 999,8 => (#[0x21,0x12,0x12,0x252,0x252,0x0,0x0,0x0,0x0,0x14841,0x10474,0x31,0x0,0x0,0x12,0x0,0x0,0x11,0x0,0x52,0x11,0x242,0x12,0xa42,0x221,0x0,0x11,0x12,0x242,0x12,0x0,0x14,0x12,0x242,0x874,0x294,0x11,0x0,0x12,0x94c71,0x4654,0x11,0x0,0x0,0x31,0x0,0x12,0x242,0x0,0x51,0x318c71,0x221,0x51,0x18e54,0x0,0x51,0x0,0x0,0x0,0x0,0x11,0x11,0x12,0x12,0x0,0xa34,0x242,0x2,0x0,0x218e33,0x12,0x11,0x12,0x0,0x12,0x12,0x12,0x0,0x4654,0x12,0x12,0x11,0x0,0x12,0x12,0x0,0x11,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x0,0x11,0x282,0x44,0x2,0x4,0x2,0x5242,0x51,0x282,0x244,0x44,0x54,0x44,0x2,0x244,0x282,0xc44,0x62,0x11,0x2,0x1] : Array ℕ)[i]?.getD 0
  | 999,9 => (#[0x18c652,0x4652,0x88852,0x8ca52,0x8851,0x8452,0x8652,0x4a52,0x8a32,0x8652,0x8452,0x32,0x12a4a32,0x232,0x1188442,0x90a55,0x2a2aca55,0x503490a52,0x52940ca52,0x23214852,0x1d2940ca52,0x490a4290a55] : Array ℕ)[i]?.getD 0
  | 999,10 => (#[0x4652,0x4a52] : Array ℕ)[i]?.getD 0
  | 1023,8 => (#[0x0] : Array ℕ)[i]?.getD 0
  | 1023,9 => (#[0x2b5,0x0,0x12,0x0,0x0,0x12,0x0,0x0,0x0,0x11,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x15,0x12,0x4] : Array ℕ)[i]?.getD 0
  | 1023,10 => (#[0x4210a31,0x4e52,0x528c651,0x4e52,0x16,0x1,0x11,0x0,0x2d6,0x0,0x12,0x12,0x96,0x0,0x21,0x0,0x2,0x0,0x16,0x0,0x12,0x0,0x12,0x2d6,0x2,0x12,0x0,0x1,0x2,0x12,0x0,0x0,0x12,0x0,0x52,0x0,0x2,0x12,0x12,0x0,0x0,0x2d6,0x11,0x0,0x11,0x96,0x2,0x2,0x96,0x896,0x0,0x13,0x2,0x12,0x1,0x243,0x12,0x2,0x0,0x432,0x52,0x0,0x896,0x0,0x2d6,0x12,0x0,0x2,0x276,0x896,0x0,0x2,0x0,0x0,0x94a76,0x2,0x9ca56,0x0,0x8ad6,0x0,0x12,0x12,0x0,0x0,0x0,0x12,0x42,0x2d6,0x16,0x12,0x42,0x96,0x2d6,0x1,0x14ad6,0x12,0x12,0x0,0x2d6,0x0,0x2,0x2,0x0,0x13,0x11,0x2,0x1,0x2,0x2,0x0,0x0,0x16,0x52,0x0,0x0,0x896,0x12,0x42,0x56,0x0,0x2,0x0,0x13,0x0,0x2,0x2,0x12,0x0,0x12,0x0,0x42,0x896,0x2d6,0x0,0x2,0x0,0x0,0x12,0x0,0x0,0x0,0x0,0x11,0x12,0x256,0x0,0x2,0x52,0x0,0x0,0x12,0x0,0x16,0x56,0x11,0x2,0x0,0x2,0x4,0x53,0x0,0x2,0x12,0x12,0x0,0x13,0x96,0x0,0x16,0x0,0x14a36,0x0,0x16,0x244,0x2,0x32,0x0,0x11,0x0,0x0,0x0,0x16,0x52,0x2,0x2,0x0,0x0,0x244,0x13,0x244,0x2d6,0x2,0x16,0x2,0x0,0x2,0x16,0x0,0x2,0x52,0x0,0x2,0x444,0x16,0x2,0x0,0x2,0x96,0x12,0x12,0x0,0x32,0x0,0x0,0x0,0x0,0x2d6,0x2,0x2,0x0,0x0,0x52,0x12,0x12,0x2d6,0x0,0x0,0x0,0x12,0x0,0x2d6,0xad6,0x0,0x1,0x2,0x0,0x2,0x12,0x4,0x1,0x12,0x0,0x11,0x0,0x0,0x2,0x0,0x1,0x0,0x12,0x2,0x12,0x12,0x96,0x0,0x13,0x0,0x2,0x2,0x0,0x12,0x0,0x4656,0x32,0x12,0x12,0x2d6,0x1,0x0,0x0,0x13,0x12,0x2d6,0x0,0x1,0x11,0x0,0x2d6,0x2,0x2,0x244,0x3,0x12,0x0,0x2,0x2,0x2,0x2,0x0,0x12,0x0,0x2,0x12,0x1096,0x2d6,0x452,0x0,0x0,0x0,0x0,0x0,0x42,0x12,0x12,0x0,0x0,0x3,0x4,0x2,0x2,0x0,0x0,0x244,0x2,0x0,0x2,0x0,0x2,0x0,0x0,0x12,0x2,0x2,0x2d6,0x4a76,0x16,0x0,0x32,0x2d6,0x0,0x0,0x32,0x16,0x0,0x0,0x12,0x0,0x32,0x0,0x2,0x12,0x2,0x0,0x0,0x56,0x12,0x12,0x0,0x12,0x12,0x0,0x4,0x4,0x0,0x0,0x4a56,0x12,0x0,0x0,0x243,0x0,0x44,0xc4,0x242,0x85,0x86,0x2d6,0x12,0xc5,0x2c6,0x242,0x42,0x2c5,0x85,0xac6,0x42,0x2c4,0x6,0xc3,0x6,0x4,0x85,0x4,0x0,0xc4,0x13,0x44,0x242,0x86,0x2c6,0x0,0x86,0x73,0xc6,0x86,0x96,0x6,0xd6,0x2,0x13,0xd6,0x242,0x2d2,0x42,0x1,0x242,0x86,0x86,0x96,0x13,0x0,0x242,0x266,0x86,0x96,0x44,0x86,0x2,0x2,0x242,0x4,0x86,0x96,0x242] : Array ℕ)[i]?.getD 0
  | 1023,11 => (#[0x1294a53,0x1294a53,0x94a34,0x1294892,0x26208874,0x5254,0x255,0x90a94,0x2521c892,0x94a54,0x394a54,0x29290894,0x6521dad4,0x25294ad4,0x4a52,0x31ca32,0x4a52b46d4,0x1494892,0x9ca52,0x4a94,0x121ca52,0xa0ec4b4ad3,0x8a55,0x94a52,0x4a55,0x3290e52,0x4a5224a52,0x4a52,0x9487295a56,0x5214a52,0x485224a52,0x4a94,0x3290e52,0x24294892,0x121ca52,0x5224a52,0x4a52,0x1294ad4,0x5290a54,0x4652,0x94a34,0x2738c652,0x20ce8290e52,0x4a4224a52,0x14a55,0x52521c892,0x1294894,0xc872b4a56,0x485494a52,0x5210e52,0x2d295a56,0x19868290e52,0x25218e54,0x252952d4,0x25214894,0x252952d4,0x4895,0x4a52,0x294ad3,0x25291094,0x4a4294a52,0x1214a53,0x1194ad4,0x255,0x2421ca52,0x94a54,0x94a54,0x24494894,0x90e5295a56,0x429ca52,0x27294892,0x8e54,0x25214892,0x94a34,0x24224a52,0x4a52,0x1294894,0x121ca52,0x25294a54,0x18e52,0x455,0x4a55,0x4a52,0x4a4224a52,0x4a52,0x324652,0x1294892,0x139ca51,0x324652,0x94a55,0xa55,0x4a54,0x4853,0x1390a51,0x4a94,0x94a34,0x4a52,0x25291094,0x25294a94,0x2721ca52,0x4875,0x4e4294892,0x21ca52,0x121ca52,0x25290894,0x485224ad4,0x14855,0x521ca52,0x394a54,0xb0e7694a56,0xa55,0x8ca54,0x2421ca52,0x94a54,0x4a94,0x1294892,0x4a55,0x24494a52,0x24224a52,0x25210e52,0x2421ca52,0x244,0xa44,0x74,0xc74,0x14,0x91,0x65,0x4852,0x1092,0x950b7,0x14,0x1092,0x65,0x10c9291ad2,0x5e97,0x4d290e57,0x252,0x242,0x12,0x94,0x92,0x244,0x1643,0x92,0x10b2,0x54,0x4,0x2b7,0x1052,0x3,0x12,0x244,0x242b1274,0x272,0x1452,0x4852,0x12,0xe43,0x252,0x244,0x0,0x94,0x5463,0x292,0x242,0x852,0x852,0x4ad7,0x12,0x4e42,0x92,0x52,0xa4a57,0x10b2,0x12,0x3,0xb2,0x254,0x1234a55,0x3,0x27394a53,0x43,0x65,0x52,0x14,0x244,0x12,0x12,0x94a57,0x1242,0xa3,0x92,0x3,0x1292,0x4453,0x12,0x254,0xb2,0x9ca57,0x15,0x63,0xb2,0x4af7,0x1299697,0x10b2,0x4a57,0x94,0x244,0x52,0x20a43,0x12,0x1052,0x254,0x242,0x4e42,0x12,0xe44,0x244,0x852,0x3,0x242,0x4852,0x10b2,0x242,0x2ca57,0x12,0x242,0x92,0x4ad7,0x54,0x14,0x3,0x284,0x4a24,0x12,0x94,0x12,0x252,0x4e52,0x4863,0x7494af7,0x94,0x92,0x52,0x4,0x254,0x65,0x52,0x1092,0x14,0x252,0x12,0x43,0x19072,0x45,0x1092,0x4842,0x14,0x74,0x254,0x54,0x1052,0x252,0x14,0x2ca57,0x5,0x12,0x74,0x4,0x2ca57,0x14b2,0x1092,0x12,0x15,0x54,0x3,0x2468ca53,0x10b2,0x12,0x54,0x4a57,0x12,0x92,0x63,0x14,0x14a57,0x14,0x245,0x5,0x14ab7,0x2,0x15,0x42,0x52,0x242,0xa44,0x242,0x1243,0x12,0x92,0x254,0x244,0x242,0x272,0x892,0x12,0x0,0x252,0x42,0x12,0x1a5219297,0x12,0x4852,0x65,0x594a57,0x1245,0x14,0x5,0x254,0x12,0x5,0x24af7,0xc195877,0x4a57,0x12150b7,0x43,0x656,0x12,0x65,0x5,0x3,0x242,0x65,0x4e52,0xc74,0xa42,0x242,0x8b2,0xb2,0x242,0x4,0x52,0x94,0x12,0x92,0x3,0x242,0x19072,0x242,0x8b2,0x43,0x92,0x242,0x1243,0x242,0x63,0x94a57,0xb2,0x292,0x624a57,0x4a57,0x1390a57,0x52,0x12,0x1452,0x52,0x52,0x0,0x12258b7,0x12,0x10b2,0x2568c8d3,0x244,0x63,0x12,0x14,0x3,0x43,0x74,0x242,0x1052,0x14,0x52,0x18e72,0x1092,0x52,0x54,0x4,0x254,0x12,0x4,0x43,0x252,0x245,0x1092,0x244,0x5463,0x15,0x5,0x12,0x48c6916d2,0x252,0x244,0x52,0x1052,0x92,0x1219a97,0x242,0x1242,0x1642,0x92,0x852,0x12,0x854,0x3b8e97,0x54,0x34,0xb2,0x242b1274,0x4ce5,0x1290ca7,0x35c83,0x908f7,0xaf4,0x2f2,0xcf7,0x30af4,0x94843,0xa8a65,0x74,0x8ce4,0xe87,0x1cf4,0x48a7,0x74,0x16f2,0x5c34,0x5665,0x17248f7,0xe3,0xcf7,0x90ce7,0xc87,0x4843,0x90a43,0x1dae3,0x1290ce7,0x274,0x248a7,0x724874,0xa0cf4,0x39474,0x2e4,0x52f2,0x74,0xb9657,0x10f7,0x4ce5,0x710874,0xae7,0xb4,0x5cf2,0x90ce7,0x4ce5,0x1e97,0x25ce4,0xae7,0x90cf4,0x20ee7,0x5,0x1dc94] : Array ℕ)[i]?.getD 0
  | 1023,12 => (#[0xa4a5294a92,0x25294a52,0x525294a52,0x4a5294a55,0xca5294a54,0xa5294a52,0x4a5294a55,0x4a52a4652,0x25294a52,0x25294a94,0x65294a52,0x1294a55,0x27294a52,0x14a9294a52,0x3294a55,0x4a52a4652,0x3294a55,0x90852a4a52,0x90852a4a52,0x25294a52,0x484294a54,0xa4a5294a92,0x4a5294a55,0x4a5294a55,0xa210a4594a52,0x121485290a52,0x1294a75,0x1214ab5,0x2108922ca52,0x590a4294a53,0x4ef294a53,0x90a4294a53,0x90e5294af3,0x2821085224a52,0x1214ab5,0x1590a4294a53,0x22c84224a52,0x25295e55,0x21088594a52,0x14bca5294a93,0x41104294a52,0x94a55,0x5214855,0x821084594a52,0x2941084294a52,0xa52a4a53,0x94a5794a93,0x1590a4294a53,0x24294a55,0xac85294a53,0x821147294a52,0xa4a528d253,0x525294a53,0x2108b224a52,0x1214a42a4a52,0x5214a55,0x214855,0x1490a4294a53,0xa210a4594a52,0x2108922ca52,0x2108922ca52,0x90a4294a52,0x5e52a4a53,0x1294a74,0x484294895,0x9485291275,0x524214ae4a4a53,0x1a4294a75,0x1a52a4a53,0x4a423965494a93,0x564211e45a4a53,0x54b514a4594a53,0x2d490a75,0x2f21165224a53,0x25295675,0x4842a52f294a93,0x4a5294a75,0xaca721cab8] : Array ℕ)[i]?.getD 0
  | 1023,13 => (#[0x4a5294a55,0x25294a52,0x565294a53,0x25294a53] : Array ℕ)[i]?.getD 0
  | _,_ => 0

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
    (if k=0 then true else testAll (k,ws.length,ws,preCov ws,rules,ls,notesOf g.mask k i) ws)

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
  (chartSamples g.mask (fun j => (g.samples j).1) == BitVec.allOnes 132) &&
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
def lanePlace (v : Nat) (upper : Nat) := 2^133*upper+v
def combineLanes {α : Type} (f : α → Bits) : List α → Nat
  | [] => 0
  | x::xs => lanePlace (f x).toNat (combineLanes f xs)
def units : Nat → Nat
  | 0 => 0
  | n+1 => lanePlace 1 (units n)
theorem laneSmall (x : Bits) : x.toNat < 2^133 :=
  lt_trans x.isLt (by decide +kernel)
theorem place_and (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u &&& lanePlace b.toNat v = lanePlace (a &&& b).toNat (u &&& v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_and,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<133 <;> simp only [h,ite_true,ite_false,BitVec.toNat_and,Nat.testBit_and]
theorem place_or (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u ||| lanePlace b.toNat v = lanePlace (a ||| b).toNat (u ||| v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_or,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<133 <;> simp only [h,ite_true,ite_false,BitVec.toNat_or,Nat.testBit_or]
theorem place_xor (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u ^^^ lanePlace b.toNat v = lanePlace (a ^^^ b).toNat (u ^^^ v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_xor,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<133 <;> simp only [h,ite_true,ite_false,BitVec.toNat_xor,Nat.testBit_xor]
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

def fullMarks (r packed : Nat) := ((packed+r) >>> 132) &&& r
theorem unit_bit (n i : Nat) (hi : i<n) : (units n).testBit (133*i) = true := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
    rw [units,lanePlace,Nat.testBit_two_pow_mul_add _ (by decide +kernel : 1 < 2^133)]
    cases i with
    | zero => simp
    | succ i =>
      have di : 133*(i+1)-133=133*i := by omega
      have ge : ¬133*(i+1)<133 := by omega
      simp only [ge,ite_false,di]
      exact ih _ (by omega)
set_option maxRecDepth 8192 in
theorem guardBit (a : Bits) : (a.toNat+1).testBit 132 = (a==BitVec.allOnes 132) := by
  by_cases h : a=BitVec.allOnes 132
  · subst a
    decide +kernel
  · have lim := a.isLt
    have ne : a.toNat ≠ 2^132-1 := by
      intro eq
      apply h
      apply BitVec.eq_of_toNat_eq
      simpa only [BitVec.toNat_allOnes] using eq
    have lt : a.toNat+1<2^132 := by omega
    rw [Nat.testBit_eq_false_of_lt lt]
    exact (beq_eq_false_iff_ne.mpr h).symm

set_option maxRecDepth 8192 in
theorem mark_at {α} (f : α → Bits) (xs : List α) (i : Nat) (hi : i<xs.length) :
    (fullMarks (units xs.length) (combineLanes f xs)).testBit (133*i) =
      (f xs[i]==BitVec.allOnes 132) := by
  simp only [fullMarks,Nat.testBit_and,Nat.testBit_shiftRight,unit_bit _ _ hi,Bool.and_true]
  induction xs generalizing i with
  | nil => simp at hi
  | cons a xs ih =>
    simp only [combineLanes,List.length_cons,units,lanePlace]
    have sum (u v x : Nat) : 2^133*u+x+(2^133*v+1)=2^133*(u+v)+(x+1) := by omega
    rw [sum,Nat.testBit_two_pow_mul_add _ (show (f a).toNat+1<2^133 from by have := (f a).isLt; omega)]
    have hi' : i < xs.length+1 := hi
    cases i with
    | zero => simpa using guardBit (f a)
    | succ i =>
      have ge : ¬133*(i+1)+132<133 := by omega
      have di : 133*(i+1)+132-133=133*i+132 := by omega
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
theorem top_xor (a : Bits) : BitVec.allOnes 132 ^^^ a = ~~~a := BitVec.allOnes_xor
theorem packed_op {α} (a b : α → Decor) (xs : List α) (op : Nat) :
    packedOp (units xs.length*(BitVec.allOnes 132).toNat) op
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
    ((mask &&& 1 == 0) || f x) && onMarks f (mask >>> 133) xs
theorem marked_ok {α} (f : α → Bool) (mask : Nat) (xs : List α) (i : Nat) (hi : i<xs.length)
    (bitOn : mask.testBit (133*i)=true) (ok : onMarks f mask xs=true) : f xs[i]=true := by
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
      apply ih (mask:=mask >>> 133) (i:=i) (by simpa using hi) _ ok.2
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

def readNotes : List BoundPool → Nat → List QuickPool
  | [], _ => []
  | p::ps, h => (p,h%16,h.testBit 4) :: readNotes ps (h >>> 5)
def checkNotes (ws : List Decor) : List BoundPool → Nat → Bool
  | [], _ => true
  | p::ps, h =>
    let info := (summarizePool ws p).2
    ((h%16 == info.1) && (h.testBit 4 == info.2)) && checkNotes ws ps (h >>> 5)
theorem notes_sound (ws : List Decor) (ps : List BoundPool) (h : Nat)
    (valid : checkNotes ws ps h = true) : readNotes ps h = ps.map (summarizePool ws) := by
  induction ps generalizing h with
  | nil => rfl
  | cons p ps ih =>
    simp only [checkNotes,Bool.and_eq_true,beq_iff_eq] at valid
    simp only [readNotes,List.map_cons,ih _ valid.2]
    have one : (p,h%16,h.testBit 4) = summarizePool ws p := by
      exact Prod.ext rfl (Prod.ext valid.1.1 valid.1.2)
    rw [one]
def notesValid (c : NodeContext) := checkNotes c.2.2.1 c.2.2.2.2.1 c.2.2.2.2.2.2

def quickAt (c : NodeContext) (i j op : Nat) (ka kb : Bool) :=
  let a := contextWire c i
  let b := contextWire c j
  (readNotes c.2.2.2.2.1 c.2.2.2.2.2.2).any (fun s => fastCost s (c.1-1) a b op ka kb)

theorem quickAt_good {c i j op ka kb} (hi : i<c.2.2.1.length) (hj : j<c.2.2.1.length)
    (valid : notesValid c = true) (h : quickAt c i j op ka kb=true) : checkAt c i j op ka kb=true := by
  have mem (t) (ht : t<c.2.2.1.length) : contextWire c t ∈ c.2.2.1 := by
    simp [contextWire,List.getD_eq_getElem?_getD,ht]
  unfold quickAt at h
  rw [notes_sound _ _ _ valid] at h
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
theorem fallback_sound {c i j op ka kb} (valid : notesValid c=true) (h : fallbackAt c i j op ka kb=true) :
    checkAt c i j op ka kb=true := by
  simp only [fallbackAt,Bool.or_eq_true] at h
  rcases h with h | h
  · split at h
    next yes => exact quickAt_good yes.1 yes.2 valid h
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
    let z := packedOp (r*(BitVec.allOnes 132).toNat) op a b'
    let cov := if d then v else u
    let mask := fullMarks r (takePacked cov (packedColumn d a) (packedColumn d b') un ka kb ||| packedColumn d z)
    onMarks (fun c => fallbackAt c i j op ka kb) mask xs

theorem batchMove_at (k n) (xs : List NodeContext) {i j op : Nat} {ka kb}
    (hi : i<n) (hj : j<n) {q : Nat} (hq : q<xs.length)
    (budget : xs[q].1=k) (arity : xs[q].2.1=n) (valid : notesValid xs[q]=true)
    (pass : batchMove (makeBatch k n xs) xs i j op ka kb=true) :
    checkAt xs[q] i j op ka kb=true := by
  let len := 1+(n-(if ka then 0 else 1)-(if (op==2) || kb then 0 else 1))
  let d := len==k
  have eval : checkAt xs[q] i j op ka kb =
      if len>k then true else if combField xs[q] d (op==2) ka kb op i j != BitVec.allOnes 132 then true
      else if !properB (movedDecor op (contextWire xs[q] i) (contextWire xs[q] j)).1 ||
        xs[q].2.2.1.any (fun v => v.1==(movedDecor op (contextWire xs[q] i) (contextWire xs[q] j)).1)
      then true else closeChild xs[q].2.2.2.2.1 xs[q].2.2.2.2.2.1 (k-1)
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
        packedColumn d (packedOp (r*(BitVec.allOnes 132).toNat) op a b))) xs) = true at pass
    rw [if_neg small] at pass
    have chosen : cov = packedCov (fun c => getCov c.2.2.2.1 d) xs := by
      dsimp only [cov]
      cases d <;> rfl
    have ca : a = _ := laneWire_at k n xs hi
    have cb : b = _ := laneWire_at k n xs hj
    dsimp only [r] at pass
    rw [ca,cb,packed_op,packed_column,packed_column,packed_column,chosen,takePacked_ok,lanes_or] at pass
    by_cases hit : combField xs[q] d (op==2) ka kb op i j = BitVec.allOnes 132
    · apply fallback_sound valid
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
    (budget : xs[q].1=k) (arity : xs[q].2.1=n) (valid : notesValid xs[q]=true) (js : List Nat)
    (bounds : ∀ j ∈ js, j<n) (allRows : batchRows (makeBatch k n xs) xs js=true) :
    testAll xs[q] (js.map (contextWire xs[q])) = true := by
  induction js with
  | nil => rfl
  | cons i js ih =>
    simp only [batchRows,Bool.and_eq_true,batchRow,List.all_eq_true] at allRows
    simp only [List.map_cons,testAll,testRow,Bool.and_eq_true,List.all_eq_true,List.mem_map]
    have hi := bounds i List.mem_cons_self
    have check := @batchMove_at k n xs
    refine ⟨⟨⟨check hi hi hq budget arity valid allRows.1.1.1,check hi hi hq budget arity valid allRows.1.1.2⟩,?_⟩,
      ih (fun j hj => bounds j (List.mem_cons_of_mem _ hj)) allRows.2⟩
    rintro _ ⟨j,hj,rfl⟩
    have hj' := bounds j (List.mem_cons_of_mem _ hj)
    have both := allRows.1.2 j hj
    have opCheck (d : Bool) (pass : batchPair (makeBatch k n xs) xs i j (if d then 1 else 0)=true) :
        testPair xs[q] (contextWire xs[q] i) (contextWire xs[q] j) d=true := by
      simp only [batchPair,Bool.and_eq_true] at pass
      simp only [testPair,Bool.and_eq_true]
      exact ⟨⟨⟨check hi hj' hq budget arity valid pass.1.1.1,check hi hj' hq budget arity valid pass.1.1.2⟩,
        check hi hj' hq budget arity valid pass.1.2⟩,check hi hj' hq budget arity valid pass.2⟩
    exact ⟨opCheck false both.1,opCheck true both.2⟩

def runBatch (k n : Nat) (xs : List NodeContext) :=
    batchRows (makeBatch k n xs) xs (List.range n)
theorem runBatch_at {k n} {xs : List NodeContext} {q} (hq : q<xs.length)
    (hb : xs[q].1=k) (ha : xs[q].2.1=n) (hn : xs[q].2.2.1.length=n) (valid : notesValid xs[q]=true)
    (pass : runBatch k n xs=true) : testAll xs[q] xs[q].2.2.1=true := by
  have all := batchRows_at k n xs hq hb ha valid (List.range n) (fun _ => List.mem_range.mp) pass
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
  let start := num*(10*storedDepth g depth+raw.length+depth)
  let pos := start+num*offw+packedAt data (start+i*offw) offw
  let nr := packedAt data pos 5
  let nl := packedAt data (pos+5) lw
  let st := pos+5+lw
  let rules := (getPairs data cw depth nr st).filterMap (fun (a,b) => buildRule g ops depth bank a b)
  let ls := fun tag => ((g.index k tag).bind (linkedSet g (k-1))).toList
  (k,ws.length,ws,preCov ws,rules,ls,notesOf g.mask k i)


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
  (contexts g k start n).all (fun c => c.2.1==ar && prelim (targetOf g) c && notesValid c)
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
  have ha : xs[q].2.1=ar := e ▸ one.1.1
  have hn : xs[q].2.2.1.length=ar := by rw [e]; exact one.1.1
  have hnots : notesValid xs[q]=true := by rw [e]; exact one.2
  rw [from_context,Bool.and_eq_true]
  refine ⟨one.1.2,?_⟩
  split
  · rfl
  · exact e ▸ runBatch_at hq hb ha hn hnots (cutsRun h)

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
def maps3 : List (Nat × List Nat) := []
def known3 := extendKnown [] 1 maps3
def maps7 : List (Nat × List Nat) := []
def known7 := extendKnown known3 2 maps7
def maps15 : List (Nat × List Nat) := [(15,[]),(23,[32,67]),(27,[16,66]),(29,[65,50]),(30,[64,65,66,67]),(39,[32,67,84]),(57,[32,65,82,83]),(78,[64,33,67,84,101]),(99,[16,33,66,83,100,101]),(135,[67,84,101,118]),(156,[64,81,83,101,118]),(163,[16,66,83,100,101,118]),(165,[65,50,83,100,101,118]),(166,[64,65,66,83,100,118]),(172,[64,81,82,67,100,101,118]),(177,[16,65,82,99,118]),(198,[64,83,100,117]),(281,[65,82,83,101,118,135]),(305,[16,65,82,99,118,135]),(312,[64,81,98,83,118,135]),(326,[64,66,83,100,117,135]),(330,[64,65,82,100,117,135]),(332,[64,81,66,83,100,117,118,135]),(344,[64,81,98,83,117,118,135]),(353,[65,82,99,116,117,135]),(354,[64,65,82,99,116,101,118,135]),(396,[64,81,82,83,100,117,134,135]),(424,[64,81,98,67,116,101,134]),(480,[64,81,98,115,132,101,134])]
def known15 := extendKnown known7 4 maps15
def maps45 : List (Nat × List Nat) := []
def known45 := extendKnown known15 3 maps45
def maps51 : List (Nat × List Nat) := []
def known51 := extendKnown known45 3 maps51
def maps31 : List (Nat × List Nat) := [(31,[]),(167,[83,100,101,118]),(313,[81,98,99,84,118,135]),(334,[80,81,82,83,100,117,135]),(355,[82,99,116,117,118,135]),(428,[80,97,82,99,116,101,134])]
def known31 := extendKnown known51 7 maps31
def maps47 : List (Nat × List Nat) := [(47,[]),(61,[65,50]),(94,[64,65,66,67,101]),(151,[67,84,101,118]),(173,[48,65,50,83,100,118]),(181,[65,50,99,84,118]),(185,[16,65,98,83,101,118]),(188,[64,97,98,67,84,118]),(227,[16,66,99,116,117,118]),(230,[64,65,66,99,116,101]),(301,[48,65,82,100,118,135]),(331,[80,81,66,100,117,118,135]),(339,[66,99,84,117,118,135]),(345,[80,65,98,67,84,117,118,135]),(346,[64,49,98,67,84,117,135]),(358,[64,65,82,99,116,101,118,135]),(369,[65,98,115,84,118,135]),(422,[64,81,66,99,116,117,134]),(440,[64,97,114,67,84,117,134]),(454,[64,66,99,116,133,118,135]),(460,[64,97,66,99,116,133,135]),(482,[64,49,98,115,132,133,135]),(484,[64,97,82,115,132,101,118,135])]
def known47 := extendKnown known31 5 maps47
def maps55 : List (Nat × List Nat) := [(55,[]),(79,[64,65,66,67,101]),(103,[16,66,100,101]),(115,[50,99]),(143,[32,67,101,118]),(174,[48,65,50,83,100,118]),(179,[65,50,99,84,118]),(206,[48,50,67,100,117]),(286,[48,33,101,118,135]),(316,[48,97,66,84,118,135]),(327,[64,65,82,100,117,135]),(348,[48,97,66,84,117,118,135]),(364,[48,97,99,116,118,135]),(376,[48,97,114,99,116,118,135]),(398,[48,65,50,67,100,117,134]),(433,[16,49,98,115,100,117,134,135])]
def known55 := extendKnown known47 5 maps55
def maps63 : List (Nat × List Nat) := [(63,[]),(95,[16,66,101]),(159,[32,67,101,118]),(175,[32,83,100,118]),(183,[99,84,118]),(231,[16,66,99,116,117,118]),(317,[32,97,82,83,100,118,135]),(350,[96,33,99,84,117,135]),(359,[16,82,99,116,118,135]),(366,[96,49,116,118,135]),(371,[98,115,84,135]),(377,[48,97,114,99,116,117,118,135]),(429,[80,97,116,134,135]),(430,[96,81,98,83,116,134]),(441,[16,97,114,116,101,134,135]),(444,[96,113,114,99,84,101,134]),(462,[96,98,67,116,133,135]),(492,[96,113,115,132,133,134])]
def known63 := extendKnown known55 8 maps63
def maps111 : List (Nat × List Nat) := [(187,[16,97,66,83,100,101,118]),(190,[64,97,98,67,84,118]),(215,[67,84,117]),(222,[64,65,66,67,117,118]),(238,[64,65,66,99,116,101]),(243,[16,66,115,100,101]),(318,[64,81,66,83,100,118,135]),(349,[80,65,98,67,84,117,118,135]),(365,[48,65,82,116,135]),(378,[64,49,114,67,84,101,118,135]),(413,[48,65,50,67,117,134]),(437,[65,50,115,84,134]),(455,[96,98,67,116,133,135]),(476,[64,113,66,115,100,133,118,135]),(490,[64,49,114,99,132,133,118,135]),(497,[65,114,131,84,134,135]),(504,[64,113,130,67,84,133,135])]
def known111 := extendKnown known63 7 maps111
def maps119 : List (Nat × List Nat) := [(119,[]),(207,[64,65,66,67,117,118]),(380,[48,113,66,84,101,135]),(414,[48,65,50,67,117,134])]
def known119 := extendKnown known111 6 maps119
def maps189 : List (Nat × List Nat) := [(189,[]),(347,[65,66,115,84,101,118,135]),(486,[16,66,99,132,133,134,135])]
def known189 := extendKnown known119 8 maps189
def maps250 : List (Nat × List Nat) := []
def known250 := extendKnown known189 5 maps250
def maps127 : List (Nat × List Nat) := [(127,[]),(223,[64,65,66,67,117,118]),(247,[115,84]),(375,[98,115,84,135]),(381,[48,113,82,135]),(382,[112,49,66,115,84,101,135]),(415,[48,65,50,67,117,134]),(446,[112,81,114,83,100,134,135]),(478,[112,65,114,67,100,133,135]),(493,[80,113,50,132,135]),(499,[65,114,131,84,134,135]),(505,[64,113,130,131,132,133,135]),(508,[112,129,66,115,84])]
def known127 := extendKnown known250 9 maps127
def maps191 : List (Nat × List Nat) := [(191,[]),(319,[65,50,135]),(351,[64,65,66,67,101,135]),(367,[80,81,66,100,117,118,135]),(379,[81,98,118,135]),(431,[48,65,50,83,100,134,135]),(445,[48,97,82,134]),(487,[16,66,99,132,133,134,135]),(494,[96,65,98,67,132,117,134])]
def known191 := extendKnown known127 11 maps191
def maps251 : List (Nat × List Nat) := [(251,[]),(254,[32,67,117]),(471,[16,66,67,100,133,134,135]),(501,[16,33,50,131,100,133,118]),(506,[32,49,130,100])]
def known251 := extendKnown known191 8 maps251
def maps255 : List (Nat × List Nat) := [(255,[]),(479,[64,65,66,67,133,134,135]),(503,[16,66,131,100,101,135]),(507,[81,130,118]),(509,[48,129,82]),(510,[128,65,130,67,100,117])]
def known255 := extendKnown known251 12 maps255
def maps383 : List (Nat × List Nat) := [(383,[]),(447,[65,50,131,84,118,135]),(495,[80,81,82,83,116,133,118])]
def known383 := extendKnown known255 13 maps383
def maps511 : List (Nat × List Nat) := [(511,[])]
def known511 := extendKnown known383 15 maps511
def mapsx15 : List (Nat × List Nat) := [(527,[]),(541,[50,65]),(647,[115,99,83,67]),(677,[114,33,97,82,50,65]),(793,[131,115,99,50,82,65]),(865,[130,33,113,99,82,65])]
def knownx15 := extendKnown known511 4 mapsx15
def mapsx23 : List (Nat × List Nat) := [(535,[]),(539,[50,65]),(551,[84]),(569,[65,33,82,49]),(611,[66,100,82,50]),(675,[114,33,97,82,50,65]),(689,[114,33,97,82,49]),(817,[130,114,33,97,82,49])]
def knownx23 := extendKnown knownx15 4 mapsx23
def mapsx31 : List (Nat × List Nat) := [(543,[]),(679,[115,67,100,83]),(825,[131,115,65,50,98,81]),(867,[131,50,66,116,99,82])]
def knownx31 := extendKnown knownx23 7 mapsx31
def mapsx47 : List (Nat × List Nat) := [(851,[131,50,114,82,99,66])]
def knownx47 := extendKnown knownx31 5 mapsx47
def mapsx187 : List (Nat × List Nat) := [(699,[]),(755,[99,65])]
def knownx187 := extendKnown knownx47 7 mapsx187
def mapsx189 : List (Nat × List Nat) := [(701,[]),(859,[130,50,98,82,115,33,65])]
def knownx189 := extendKnown knownx187 8 mapsx189
def mapsx215 : List (Nat × List Nat) := [(727,[]),(949,[134,81,114,49]),(1009,[118,33,129,82,49])]
def knownx215 := extendKnown knownx189 7 mapsx215
def mapsx349 : List (Nat × List Nat) := [(861,[]),(877,[84,131,98]),(925,[118,130])]
def knownx349 := extendKnown knownx215 7 mapsx349
def mapsx455 : List (Nat × List Nat) := [(967,[])]
def knownx455 := extendKnown knownx349 7 mapsx455
def mapsx191 : List (Nat × List Nat) := [(703,[]),(831,[135,50,65]),(891,[130,50,81,115,98,65])]
def knownx191 := extendKnown knownx455 11 mapsx191
def mapsx351 : List (Nat × List Nat) := [(863,[]),(879,[84,131,98]),(943,[98,118,81,130,50,65]),(957,[118,130,81])]
def knownx351 := extendKnown knownx191 11 mapsx351
def mapsx471 : List (Nat × List Nat) := [(1013,[134,81,114,49])]
def knownx471 := extendKnown knownx351 8 mapsx471
def mapsx487 : List (Nat × List Nat) := [(999,[])]
def knownx487 := extendKnown knownx471 11 mapsx487
def mapsx503 : List (Nat × List Nat) := [(1015,[])]
def knownx503 := extendKnown knownx487 12 mapsx503
def mdata8 (i : Nat) : Nat := 0x3d325526d181544a960a00
def mlevel8 : Packing := (1,7,7,0,0,0,0,mdata8)
def mdata9 (i : Nat) : Nat := 0xc0704030100b040000000001a06100017000801d0008006e01615fd6cdcb48c643c13ebc39b0ae2ba9201d9b120f8051ef750a96d5a160a00b9d6ea192c12a4c0c01b3e552325824c581803e6caa264b04a93030074ed6d181544a960a00fda0a9302a8b0519c01dbc182606bb4c532803f68306a92a6c14230073cc6d255844a960a00f5b0a9302a8d54c1401fb2151609526064480376c38ac1262a9303007af04c9814c6aa60a00f5e09930498d54c0c01eb615160aaa5498180376c2a264b04a9303007af06053160aaa4ca00e39b2ac22da152c1401eb6152605516818280376c305662a2a93030078d954981544a960a00
def mlevel9 : Packing := (21,6,7,0,0,8,0,mdata9)
def mindex9 (i : Nat) : Nat := 0x1
def mdata10 (i : Nat) : Nat := (if i < 2 then (if i < 1 then 0xefd131606aa4ca008ff9c0aeda54ca00c77e556c4a94ca00c77cb9955a258e00d778b9955a848200d7e8b9549a848200dfe2bb8455388a00cf79ba9553244200b7e4c960e1188a00c7f5b14c4a960a00c77cb9956aa4ca008ff8c96c6aa60a0087fdc86c4a94ca00dfe182aed52846009fd8c96d5218ce008ff9c82e5a14ca00a7f8c96e98048600cff1c1aeda160a00efc93160aaa4ca009feacc6c18388a00ffa18254a11912009fbacc6c58291200c3fd81aeca960a00a7f8c96e92058e00ffc1324c5a160a00cff1a8aed3148600dfd1b054d8384600dbda886d5218ce00cff211aeda360a0087fdc12e6aa60a00fbd181545828ce008ff9c12e5a360a008ff9c3aeda060a0087fcc9aeda360a0097becc6d0a960a00e3bd816d0a960a0087fdc52e5a160a0097ecc9aed8388a00ebf181544a960a0097f8c96e1a14820087fdca2e5834860097f4c9aed3284600ff495254d8348200bbbacc6058291200de7a552e53299a00fba9825498191200fbe18160932546008ff8c96ceaa60a00cf7a556cca94860087fcc9aeda54ca009fd9c12e5828ce00c7bd516d0a960a00c3fe886c4a94ca00fbc581609314ca00cf7a556e0a94ca00bf71c060a55846009ef8c9aed3299a00dfb1b4844a960a0087fdcb608a94c600b3f4c96093160600d3dcb9605828ce00eb7a88954a9486008ffacc6d4a94ca0087fdc16cca960a00eb7a55a20a94ca0087fdc82e5a348600df5a552e5218ce008ff8c9aeda360a008ffacc6e98548600ff615254d8284600ff62554c58188a008ff9c12e5a54ca00cfe9522e93160a009fdacc6d5218ce008ff9c52e6aa4ca00d7ccb954d8388a00b7e8c96e12048600eb7a88954a94c60087fdcb60ca94860087fdcb544a960a00b7e4c96095284600ff621154d8588a0087fdc82e5a54ca00cdf9c7aeda54ca00cf7a556c4a960a00cfb9c42e6aa4ca0087fecc2e5a2546009ef9c52e53299a00cff2112e5a360a00ebf1814c5a060a00ebf1814c4a960a009fe9cb4c58588a00ffa21161622912008ff8c9aeda14ca00dfd181aed314ca00ff61525451060a00ef7255844a94ca00cbf9b5a20a94ca008ff8c96c5a360a0097dcc9aed828ce0097f8c9aed824c200abf9c060aaa606008ff9c1aeda54ca0097ddc12e5828ce0087fecc2e5a54ca00ebf181545a060a00cff2116cca960a00fbd131605824c200b774c94ca558460097f8c96cda548200cff2116ceaa60a009ff2cc6c13284600dfd211aed828ce00a7becc6d0a960a00cbf981aeda060a0087fdc52e5a3486008ff9c32e5a160a00bbe8c96095260600cf7a552e6aa4860087fecc6d4a94ca00cff2112e5a54ca00cfb9b46c4a960a009feacc6c58588a00a7f8c9685a060a00cfb2116d0a960a00fbc182605314ca00c7b6116d0a960a00fb61825455260600 else 0xe3f8a9605a060a00ebf1824c6aa6060087fdc52e5a258e008ff9c16cca960a00fbe1824c55260600c77e556e0a94ca008ff9c52e93160a00efc93260aaa4c600d7b5b4844a960a00ff5151549818ce0096fdc52e53299a00ef7255aa93148600cff1b5844a94ca00ebb9816d0a960a00cbfa88aeda14ca008ff9c0aeda160a009ff2cc6c985846009fb9cb61521912008ff9c02e93160a00c77e556c4a960a00cbf981aeca960a00ef7255845a850a00afbacc6d0a960a00ef6a5560aaa4ca0087fcc9aeda34860087fcc96c5a360a00bbeacc60952606008ff9cb2a5854ca00dfd151aed818ce00cfe9c2aeda060a00cbfa886c4a94ca0087fcc96c6aa60a009fd9c3aeda460a008ffacc6c4a960a008ff9cb2a5835c600ebe982606aa4ca00bf72cc54d528460097edc12e58388a009fd9cb601218ce0087fdc32e5a160a009fbacc6d0a960a00cff211aeda060a009feacc6d53260a00ebe982aa95260600efd1306a13148600dbba88aed21912008ff8c96e985486008ff9ca2e5325460087fdcb544a94ca00dbf1b0a213284600ebf18160aaa4c6009ff1cb6095084600c7f8b96c1a54ca00cf7a552e93160a0097f4c96d53284600cfd9c32e6aa4ca008ff9cb60ca948600ebd9a88cd81482009fd8c9aed828ce0097f8c96d5a24c200be79c24c25599a00ebf18160aaa54600c7f6112e5a360a00a7f8c96d5a24c200cff1ba845824c200e3f581544a960a008ff9cb545a360a00cff1b14c4a960a008ff9cb608a954600cf7a556c6aa60a00fbb1815458291200cfba442e982546009ff1cb4c985846008ff9cb4c8a954600c7f8b9681a64ca00cfe9c2aeda54ca00cf78b9955a258e009ef8c96d53299a009ef9c6aed814ca00cff1b8844a94ca00ebe98268d5260600bfe1c060e1188a008ff9cb6a13244200e7d4a94c5814ca00b3f8c96a18148200c7bdb4684a960a00d67e552e53299a0097f9c12e5a848200ebf288844a94ca0087fdc26cca954600cbf9b8608a94c600e7f0a9845a060a008ff9c52e5a258e00cfb9b4684a960a009fe9cb5418388a00aff2cc6a131486008ff9cb608a94c6009fe9cb4418388a00df3a556c58291200ebda884c4a94ca00dfc9b054d8388a00cef9c6aeda160a0087fdc12e5a54ca00c7f9b02e5a160a00d3f4b9a2132846008ff9cb4c8a960600cfda332e5a160a00cbfa886cca9486008ff9cb604a94ca00bfe1c06095284600ebf1814c6aa60a00b3ecc960952606008ff9c8aeda54ca00a7f8c96e93058a00ebf288aa93148600cbfa882e5a14ca00dbda882e5218ce00ebf181546aa60a008ff9c52e5a160a00cfd9a0aed314ca00df5a55aed314ca00a3fcc960aaa60600b774c960a558460087fecc2e5a160a0087fdcb60ca95c60096fcc9aed3299a00dbd9812e5828ce00dbb9b4604a960a00) else (if i < 3 then 0xd7f4b9545814ca00e7eca9549a160a00c7fca9aed835c600c7fca96d5a160a00d7ecb9609a54ca009efdc6aed814ca00d7dcb94c5a54ca00c7fcb9609a354600a7fcc9695a84ca00a7fcc9aa9814ca00c7fd32aeca954600c7fdb54c8a960600a7fcc9695a14ca0097fcc96d5a14ca008ffdc3aeda160a0097fdc52e58348600fbe5816093254600a7fcc968d5260600c7fcb954da160a00a7fcc9546aa4ca0097fdc52e5a64ca00c7fdb8544a94ca00c7fcb9695a160a00ff318295611912009fd8cb4c5824c200dfb211aed8291200de7a55aed3299a00ebf181609a354600fb65825455260600dbf288aed3148600fbd15360983846009fd9cb615218ce009ef9cb4c95099a00efb2116d0a960a00c7edc22e6aa60a00a7edc22e6aa60a00cf7a556c4a94ca00c7f8b9609a5506009fd9c3aed824c200c3fdb8608a94c6009ff0c96c985846009fe8c96c58588a00abfacc60aaa606008ff9c52e5a14ca00c7f6116cca960a00fbc9518ce8888a008ffacc6c9a354600ef5a554c4a94ca00bbe9c84815260600dbe982aed814ca00efc9324c6aa60a0097f8c96e1a2442008ffacc6e98048600dfd131aed814ca00afe9c22e6aa60a0087fcc96e985486008ffacc6c5a360a00cfba446c6aa60a0097f8c96cda84420087fcc96ceaa60a0087fdcb4c8a96060097f5c52e53284600c3fcb9a21a348600efd131604a94ca00dfd1b0845828ce00dbb981aed8291200dbba886c95191200ef7255844a960a00cff211aeca960a00ebe981aa93260a00ef72556a131486008ff9cb541a348600df5a55aed218ce00dfe222aed8584600bf71c24c255846009ff0c9aed83846009ff1cb5413284600dfd2112e5828ce00df3a55aed2191200eb7a88955a150a008ff9cb544a960a008ff9c5aeda160a00c7f611aeca960a00abf9c84c6aa60a00ebf182546aa60600cf7a552e5a14ca00cbfa882e6aa48600cbfa882e5a54ca008ffacc6c1a54ca0087fcc96d5a34860087fdcb608a9546008ff9c82e5a54ca00cf79b8954a948600fbe18254983846008ff9c3aeda160a00df7255aed314860097dcc96c5828ce00c77cb9955a34860096fcc96d53299a0097f5c82e53284600ffc18588a118ce008ff9c82e6aa4ca00d7d4b9845828ce008ff9cb6818548600c7dcb94c6aa4ca00d7d4b954d838460087fcc96d6aa4c600abfacc604a960a00cfb9516d0a960a009efacc6d53299a00eb7a55604a960a0087fdc12e5a360a008ff8c96c9a354600fbc932609a84c600eb7a55a21a14ca00cbf9b5a20a948600e7b6116d0a960a00c7bdb46c4a960a00c7f5c12e6aa606008ff9c12e6aa4ca00efd131681814ca00d3bd816d0a960a00b7f0c96e120846008ff9c1aeda060a00dbd981aed828ce0097ecc96c58388a0097f4c96c98584600afdacc681314ca00 else (if i < 4 then 0xa0a3813808603e026016030c052066ebff58ba8bd34e8bf41b9ebcd8e5df27b903c64e23f10b863c14dfbef6b77bbacdc7edcb6abb38d93ec5b5f3ae8d65eabb523a74d2be94b46ba18cfde77b39b9b0cd5e66b2fb96ccade4fb25b910c79e32b15b890c39e15b07381cc05dfbafa37b4bcbddeaebb758b9ddcdae63720b7bdbcaddb6dcb65db1ad6b6a4b4fda3acfb660b2dd95ac8b634b11d87ac035fcaf5d79abc35d0ad9d6bab5358cab7d5aaab3530a89d40a9e34e0a6dd35a98b4c0a57d2aa93347ca3bd1ca8c3450a1fd0ba853424a09d00a7cb3e09edcf5a7a33cc9d1ce1a6bb34c99dccda64b320987cbfa5db2dc96bcb1a56b298943c9da4b3254921c8ca45b2108ffc7ba3d31e48e9c6da34b1948bbc53a293138899c48a22310c87dc3da1b30c885bc29a12b09083fc1ea0d306482fc13a093038813c05a00aff47f7bf79f9afc87cfbe09efaf6c7b3bd89ebaf40797bc79e02efc77bbb99daaeb8759bab9d52ea4743ba09ce2e60721b8c9c5ae1c705b789ba2dcc6d7b679b32d886bbb5c9ac2d5069fb489a0acf466bb34999acbc655b2398fac78639b1b98bac5861db0a981abfc5fbaf0977abac5d3ae296f2b745b1ad49682b3c58fac395faaf8573ab59572aa8551aa4951aa88535a9694aaa38513a859422a0c503a8093e29ec4f3a7593a29b44c5a5b92d29584a9a50926292048da42920a8f4477a34916a8a443da1d90e2854421a0f907282840ba018fea7e43e99f38f7a7ac3d39e28f0a7743b19cb8e3a7003719b18d6a6a434399a8cb26543279928c7262831197b8bd25b42d195b8ad25642a99538a4a50827b93c89c24c425f9258922474225911886a4242038fd87ca3d41e18ef872a3781b38d586723281918c485ea2f01758b685922b81598a5852228013d89d84ca25412188f845a21c0ff87b83d21d80e9870837a1ac0d3862830a1680ab851828212408f84381fa0ec06181d809a00097fcc96d5a160a00c7fcb960aaa54600c7fcb968d5260600d7bdb4544a960a0097fdc56c4a960a00e7dca954d8348600e7f4a9545814ca00a7fcc9546aa60a00c7fda56c4a960a00c7fdb5608a94c600a7fcc9545a360a00b3fcc9609536060097fcc96d5a64ca00d7dcb954d8348600ffc5324c5a160a00c7febb608a954600c7fdb560ca948600c7fdb54c4a960a0097fdc12e5a54ca00ebed81609a54ca00a7fcc9695a64ca00fbe5824c5526060097fdc82e5a54ca00c7fdb5604a94ca00d7ed526c4a960a00e7eca96093254600c7fcb96958348600d7ecb9549a160a00c7fcb94caaa54600c7fcb968d854860097fcc9aed8348600cfed522e93160a00a7fcc968d8548600f3f581544a960a00c7fdb84c8a954600c7fd516cca960a0097fdc52e5a160a00c7fcb9695a64ca00f3ecc96095260600a7fcc96958348600 else 0x700100100980b0807c08840301d0010014818640c202602c290520e100c01108060058403002c2700100100060202602c2018016100c80b0ac0040040041903303100b5838ac00400402c06e20180c81040580e4406e1013016100c80b080580b8405403020190161000580d0403002c2b00100128140708060202c0302041284060038501c1022081a700080dc202c0302903303110681980b0c04c030402c01829033031380080080cc0d0402c01c2e03080b01c8808c05840260182b00100100b00c0941603840e000281001c06111ff07016180021c110c082c0036001020687800200804820020103600150008005380c40b00080002c100fd00100006e02c200fe021000583c0803006e3034016150004c003a00100240c2080008201c36000182000c00221a110c0c140400d000b8186001400400000001400db00181b80b080440300587600140208380820600098005800340010580050a0360001c25000b00040dc08840900088a04006802c2700080c8400100081a01c8ac0036001005b00148070201a0c1a001030005800200180800301245a001d030a8005c0c20100082800200480040e001114088705c002a0010603840002000d02e016181a00b0816001000006e02c2d000e800400ac0040050004408206802c200000007700101c0036001012016128004020610220c0a406c060d80020002d00120284006e1300080c00206e1400081b80b0ac0c03840301d0000e100000011030801e80080d02000140820004d0311800780004840521050170228001a10002c100130110806420b000d828440020002019108906408201030b0104000088402c106800400002d001081841a0606e2d0309078400002c0020028004002c06820030120161886b0008160a103800540026001000c0408001000380b09034c004e00100301201618000056002034080021a1303088786400241e101808040c32061001980b0816001d000806f0101b81990400207206820120161086b000b400202c10340161086b000b8002000380c2e001000a006820011101051c05c0806e4500080c781c0600b100010d08000c048058603002c2600083400206802c2000180900b0c001ae00201400fd031824083600170302a108a06c002c00101808000c048058602402c26000c81040440884a0610180040580dc40068007400220410006b80081a001001c002c00120008340c340010220371680041c001001984021a1008000008002402c2b000b8004006e044202800443c20681828e04e02180580cb0260380c1811)))
def mlevel10 : Packing := (424,5,7,0,0,13,0,mdata10)
def mindex10 (i : Nat) : Nat := 0xc9b3753400d0002f22044ec2f30003c6001140028700000000000000060883f12c513c5100000001c88b61232800a9a0c200280d000
def mdata11 (i : Nat) : Nat := (if i < 3 then (if i < 1 then 0x681828027ff5db46c1401ffa6953260a00dff17355305007bf6884ca118037fca8344b1c019ff544a94ca00ffe304a8423006ff9a0aa9828037fc99554a8c01bfe545a060a00dff30555283007fd9b84c5328037fcc1346a8c01bfe616aa4ca00dff36ad0a65005ff9b868d218037fcd8b4a994013ffaeda54ca00cff973553050067fd822a551802ff6d8b07114017fe6c5824c200dff152c2a65004ffdb568d21802ffd5db4c99401bfe6d5a24c200ffd444c2a83007fb94169182803dfcc135098c017fe2e6aa60a00dff26254b05005ff9b84c171803fecd2a6299401ff88455388a009ff374c2a43007fd21160a33803f3c994ab334015fb2e58388a00dfe422d1b05006fd931aa9328027fc5cb46c1401bfc844a960a00bf736854b05006bfa882a5218023fe5cd54c14015f72e5828ce00fee2652ac23005feabb616228023ff5d952c14013feaeda14ca009ff364d1aa3004ffabb68182802ff4d8307114017fcaed83846009ff374c12610047fdb82a5328027fcd9d54c1401afe604a960a00bfb57698a65004ff9b82a5328035fcc0d54c1401afe60aaa60600df736854b05006f7a552a521802b7e5ca6533401ff4605314ca00f7e304c0a63006bfa8868532803df4c0a64c1401fda54d8588a00ff630b08c89005fe9b54c982802bfa5ca6508c017fc2e58384600f7d304a93030047fdb32a5828027fcdd30090c01afea21a150a00f7b302c1467007f5a5548633802bfc5cb50904017fa6c58588a009ff36a54a65004ff9b068d21802fecd830519c011ff2e5a160a00bfb576c1467004ff8b9685328037bd2ab44b1c019fd844a960a00dfe42254a650067bdb42a5828027fc5cb44b1c017be6d53299a009ff576d1b050047fcb968963803df8c130708c017fcaed8584600cfba6254a65004ffabb2a5828023fed8952994013fe2e93160a009ff576d2a650063fd812a5828037f908d54c14017be6c13299a008ff972d2a65006f7a5568542802ff8d830708c017beaed3299a00ff530b11489004ffabb68582803fe498a64c14019fe680a960a00fee4aa98a43006ff2116a1428023fe5cb46c1401bfc6a13148600bf7576c1489004ff8b968582802fecdaa4319c013fe6c1a54ca009ff36254a65007fb182846448037f908b40c14011ff6c4a960a00d7f302d0305005fb9b160a448027fc5cb4a994017be2e53299a00f77302c148900677e552a5328023fe5cd54c0c013fe6c4a960a00dfd30555265006fd9a04c532802ff8d826508c015ef6d0a960a00f7e302c12a3007f715354a118023fe5cb4690c011ff6d4a94ca009ff36355305005fd8b960a338027fcd9952c14017fc6c985846009ff174c12a3006bfa882a5328037ec98952994013fe2e6aa4ca009ff362d1b05006feaaa4c9828023deda152c14013ee6d0a960a00 else (if i < 2 then 0x1bfe6d9a54ca00ffe2a6c1423006ff9b168d828037fcd0302994017fe6e9824c200bff362d4265007bf982695818037fcd2b5099401bfe608a954600ffe422d1b05006ff98269541802ffcd9346a8c017fe6d53258200ffe2a299221007fd95360d20803ff908d54c1401ffa6c18388a00efec2254b050057fcb960d71803ff8a826508c017fe6c1a54ca00dff30654a430067fda12a582803ff4c134299401bfd846aa60a00dff30ad0a65007ff1b560a11802bfe5cb4c99401bfe686aa60a00ffd362c2c45005ffabb60532803df6c130299401aff606aa60a00ffb262d0265007ff1b04ca118037fcd0952c1401bfe442aa60a00bff576992c10057fcb960d21803ff488307114017fbaed8388a00dff342d0305007ff132616118033fe99152c0c017fe2e53254600dff366d0b05005ff9b160d208037fcd2554c1401ff66d5314ca00bfbd76c1467006fdd31aa932803fec98b0498401bfe68d5260600fef4aa992c1006ffabb68582803fe6a9b0711401efea21a348600dff370d2a65007bf98168d828037fcc1554a8c01ffa6095250600bfeb6a99423006ff9a06a132803fec8830519c01ff64c5854ca00dff2a2d1b05005ffabb60d208033fe98952c1401bdf955a258e00dff370d1261006ff8b9695328037fcdc342994017feaed3244200fef4aad1a43007bf982681818037fcc155498c01fdd60a5584600ffb262d4265007fe9b54c9828033fe5cb4a99401bfe544a960a00bff36ad4265007bfa88691218033fec195290c01ffc6053254600dff30355265006ff9b568582803ff8a8a20c1401bfb4caaa60a00dff374c1ae3005ff9b169182802ffcd930aa0c017fe6c4a960a00bff374c1a41007ef932595608037fcd0346c1401bfe6a15048600ffe364c2c23006ff9516a1428037fcd2b4c99401ffc845824c200dff30755243007bf581609518037fca8554994013ff6c6aa60a00cffb6254b05006ff9322a5818035ff4434690c01fde955a04ca00f7eb0498b03006ff9812a5328037fcd0b46c14017fe2e5a64ca00f7f304d1b03005ffabb609308037f6c155499401bfe6818348600fef3052aa83006ff9a1609308037fad426290c01fde955a448600dff36254b05007fe95268582803fecd830519c01efe60d1060a00bdfb6a994cd007fe58254a11803df6c12a4c0c01ff5845828ce00cffb0654ae3006ff9a16a1328037fc99152a8c01aff60aaa60600fdf36a994cd006ff983aa971803fea98b0299401ffa6093254600dff2a0d1a43005ff9b368910803ff908952c14019ff2e5a160a00dff34ad0b05006ff9a169182802ffcd834299401bfe6c1a348600bdfd76994cd006ff931aa982803ff908b40c1401efe609a460600dff368d0b05005ffabb69532803fbd2ab5099401bfe6c1a54ca00dff35099221006ff9b3 else 0x76c1ae3006ffda168d82803fee98b4a99401bff6c5a360a00ffda64d0b05006ffdba60d21802fff5db0299401dff608a954600f7fb02d1b05006ffda56a132802ffedab42c14017ffaed8348600dffb42d4265006ffeaa605328037fed2b0690c01ffd4c5a160a00dffaa2d1b05005ffebb69532803ff6c1264a8c01ff754d8348600dffb4ad0b05006ffd83aa9718037fec1554a8c01ffb549a160a00dffb04d1aa3005ffdb568532803dfec0d54c1401dff4c8a954600ffdb04d0a65006ffda3615218037fec1d5490c01bff695a14ca00f7fb06d0b05007fdd316a132802ffedab4c99401ffd545814ca00dffb4355305006ffd32aa9518037fed2b4c99401ffb609a54ca00dffb46a9303005ffebb685828037fea8d54c14017ff6c5a360a009ffb6755305007ff15260e11803dfcc0d54c1401ffa4c9a060a00aff97355305007fe9a14c982802ffcd8346c1401efe605a460a00dff304d02a3005ff9b3601218037fcd12a2984017fe6d5a14ca009ffd76d1a43006ff98068d218037fcd42a690c01efe605824c200bff370d12a3006ff8b9685828033fe99152a8c01bfe6c1a160a00ffe30099423007ef9b04ca668037bf2ad5499401bfe6e98254600bff576d2305005ff9b36a1108037fcdb34498401ff554d8384600ffb2a2c1467007ff211691828037fcd034299401ffa5418388a00ffd304d0265007fd98354d108037fca8d54c1401bfeaeda060a00dff340d3265005fdebb4c532802ffcdaa6488401ffa5498348200bfed7699423007bf58384582803ff2c1c2311401ffc4c5a160a00dff362d0305006ff61168d82803fecd826299401ff3609314ca00bff576c1ae3007bf9812a5828027fedd30a90c01fee5458291200ffd304a9221005ff9b868910802ffcd8b0a994017fe2e5a160a00bff362d0305006fed82695328039fec0952c14019ff544a960a00dff360d1b05006ff93268151802bfed8952c1401bdf955a348600fef2a0992a3005ffabb68582802ffcd8b46c1401bfe4c5a060a00ffcb0499423005ff8b960d71802ffcd835099401bfeaeda54ca00ffd304a9263007e7d32956668037fc88346c1401ff66c5828ce00dff2a355265007fe9824c910803ff498b0b11401ffa4818348600dff152c1ae3006ff93269560803dfcc0b40c14017fe6c1a64ca00dff576d1261006ff9b168930802ffad930b08c017fe6e1a24c600feea652ac23007f7a554c910803ff8c2c22a1401fee6c58291200aff972d2a65007bdd8160a338027fed8b46c14015ff2e5a160a009ffd76d0b050067fd822a531803ff908b0690401fde955a64ca00dff34ad0a65007ef932542668037fcc115298c017feaed8250600cffb0254a65005fddb160a338037fcd034a99401bfe6e9814ca009ff97498b05005ff8b969532803fdd22554c14)) else (if i < 5 then (if i < 4 then 0xe06182e040060301b1814504a04c000c1702602a00060981582128a04046819a8100d0560608c0a06080cb05018342a03407803016030cc170250704d808b41f014040304e0bc0f026020505e0bc0f026020505916b229643a4843903b1fb23e347a08edf1d2639747088d991a9a340464f8c69183a2f9c5c28b2315562924509899b1272235c445883f0fba1e443ad86e30d2e192c2ff85c90afa14c42728483089a0fac1c4832705b60a9412c81f7032a047406880430019ff5bfd07f28fdb9faf3f387e3afbddf68beb67cf4f97df1cbe1e7c06f7a1ecb3d867aecf599ea03d2579fef391e64bcae793cf239e39bc637890f0b5e03bbd67776eeaddc2bb6a769eecd1d923b147608eba5d673a8774c2e945d0aba1073eae769cda39a47312e535c93b8eb71a0e2d5c423869709ce0a1c06b7f26faedec5bcb37656e94dce9b8fb70f6de8db65b64b6ae6d26d9b5b29362c6c0cd781ae2b5aa6b34d629ab7b55f6a72d479a7134bc68ead111a1a34246812cfe59f4b3c3670ecdb19a3333665c8cb5195cb29e6532ca25931b248645ac8498fbb1dc6398c6998c5b1656294c4bd88a310461e8c30d859b0986110c15d823b02c6022c0057edafc05f60be297a1af335e30bc2177c2ed25d58b9ed735ae505c80b8c16ffadef5ba8b6b96c9ad785abab535693ad0159ccb2d564d2c8a58deb17d61cac1e5806afa15ec2bbd5744ae1d5a02b1a55e8ab65564aaae553ca9e152eaa4d547aa8894fe29e1538ca6d94c2a96a5288a479481a8f3519aa2c9446287c50aca0ed41027fa4fd49ee53cf27834ed09d0938e26e04d749a7d34226744c8698a1306a5fd4bae96c52d0a5864ad6951528a250449e89365264a4ae492691e1218a42147ca8f291d7a39f471e8da519c231d46048b7116622a64500896911fa22443fc878d0ef21c3435086090b9214c424c842d06220a941328225031a04840708074ffb9fdc3f6c7e6cfc01f653eaa7ce8f8f9ecd3d4e7928f179e093bf27720ed11d7c3ac27518e9b1d1039ea733ce5a1c6d384c6f7cdcc1b72366c6c40d6f9a9834ce6904cf219a832c264c0c6f189730b6607cbe697a72ec05c64b6916ac2cf65954b0c95f32b9a569cabb153a29fc5308a431460281c4fa09e1139c26d64c9097412ac250c48fc90711c7232c453c88410ab20c840cc8010fbb1f403d907940ed61d1e394c7168e071b8035e46990ceb190630f05fa8ba3168c2c2855c0a87146a27344c30955125e23a04560886107e200c3de07750e9e1bf435b06590c6617842cd05740a86144825a847908a610881f3039406b00cc8175829904a408580f2819e02da054809600e5015201e001e0000dffa63553050077fd512a5828037fea9b42c1401bff546aa4ca00f7fb04a9b03005ffebb69932802fff5da62c14017ff6c5a84ca00bffd else 0x2c02606320a80a838d8010010196002219800800c0c8181018200e1307612204740c150e810681903600301880b000c0c30717030060cc077000306a0e0304c003400204c07b001c0c06e20261000060404c066031813a002023800068f0200e1018c0620460604c0c2c08810982d03101402dc1702000c0e088e0cc0c0241b0706404d815000620a701a30011110150258006060381606026044402403a810f00200606381b044406083880c840f01c03030500604052800301d0501c2c094080e305a0f40cd8170200005140a819982d0322381e82502350324d8170130460e6601810890f01604a0f0998295828190183c0980980018230580606680604c046201813010182002a0103860900981806f81301300066805141281300030560540c09e05608c1cc4170210724a4c0400e80011c080dc0c1e82e04c0e00012819330403d81683e032803033403026022818a0e40f0250201cc00f8148f9121818c0e04e82502c006e0bc0e80302030030d81183e0204c0380c1a80305c083c09416038192302018060606182805c08808ac100200b1e04c04060600e8040e1b00c0581486100580c80f81181140c81860981c811682e04c0f09981140580c80941d829702307a043a0b8010010ec0ec0d811e83e026063601814860c8a005224303e02f02d032705e07813015000306c0a08f02500a045a0b811810258505c0f411828d81d0024b81e82d043502c088000c1182e0421b40c06502300f016c0c06100cd07c0b81012b00310520606282502c0e6e0608e82e02c080f980016460724d4128110e0306a0b811800192504c0ec0e0d1182c03033403026023305818220180b020370305c0e00e823000345a08c0c80605a0f80b009f02507c04098070183003a0981c1c81a2e0560941c7814861251d0060bc080c8370186c0980801d00022060dc0982d000320dc061b025070540a282818301483e03e06000c0802f03d034816a00c141a60406e681ac1603813c09808d41c8190cc0581682609380f60002e81837c0981c112302505606096141489605a0e4aa8100e60072078170110c2504c0080087607606c08e03407c0b81c00e82815c0980920640c40420ec17011b02602200060901683e041c07a0581201b058506c04c03020370305c08c0a838c81e0002341303d023505047813013002b0320141703812a08601f8130380ba06c00cc14060191d0560780008b04c0ec08f01f01403c09401829982f0304780b0203ea000591812803051b05a0580013504c0f824e03f0260701740d801b016052183c0141303b05240f00740206110882a02c0301d3000720690c1411e02c09400ac080c00c180cc09415801086605a08496839486e04c040e080027030702606282102c065c0ac1e820f816056018101b819300f6074000583704403) else (if i < 6 then 0x23a000640b0c0150006803894000c0a06102e00498940981903c00404201412036240006e05860cd8188810330183a088081781620210480700d1182b036000d40b17800342223e0600c1980ee00060c4498188010181202030203c0900e01806658048080c0e838502105a0e3031400403a801001813c008006c0c818b818000620640b140cb00102340540c6413000b0180e160260026080c411605018122801f010486048606063008003c060384048065001e00022260ac24440f00080c06838580019101809020182207800404c0c303181e0380628010813001019081320780078010008800191207a0026001030160a16010005810060b81816408c081a700301801d80c6c14340806024022058a0207800440b000806102a0636001005400406382802c0e088b81280034183103180b02037281860020194004c170250006846010004c010008075050343c040084066800881600101401cc006c0080081180c05540c940c818980040c30013050813032220580040642c01000807300100f0198006c14828882b0020030380a0060c0cb05c003c004984c0881098006060506a0c1305090f6000b06413000b818038240440b1702300068304403f0102401a058c0628003408048241a04160606444302064206300011180c605812800342e002222a0640d800e810411507e060a81403605c760018090084c0980880c14280005d021818c002a044084c100709818181018a002a0e1031800068f01803100fc001147801000881e00140480422241200102981089039210c0b00018203214058128003420190b008002032c0c4c0c381180034180506c260a1016032810f8183440981e82f00350009050182218160a1026061800c0880cc00301d8118003420180900030260a12181018c128003420190b07c04203840b000c00018160403222000604030380200200181f01d40c703e06080c00e035808840f000a8385815031018081303180c640f000b0012613000302030140940c406181880e018102803181280034062681ec02000c0c302c003a06c004c08204c0c8a83858220201c30320604c0020602808060a8182c04430314004c0c818a800407604a000d0980d01880580c6043c04809818e8010015000a0400580c7400090806e00060360a1031800000f004001300030202680a800d820409c07c000348409818b0041510180322e0f80c0b0c0980c6003e07c001301802c560a0d01c8c06500130080028181031c0e83816200c604260a0604c0028088200b181503180074002061800908a0d1018c008006c0b81d0702c4a00160a16060944060281e800b001261103c00223e82f83e05a07c00d4002c1c12603a01038b4080c080650015000b03081801d80c683381d02052420580c406580080ce000003a001c040840b0c8 else 0x1800330320608060208d800240444606c001b819220404805860481983401c40620640b0f800342223c078001c8162033068c1464440609010330683069009015000305e000d1088c0583402c304404e80016250003020300cd818c1980e103401d8000c100cb0002c06080d005d02a00060a0630222602c4e000604c1581b0006e058a08c160330544c0a40b01e0026042078007400128161c148000e40b120003702c304402c40880c507062058b033801261824004060604c0b5001d000322a040780b0c1a01603)))
def mlevel11 : Packing := (472,4,7,0,0,15,0,mdata11)
def mindex11 (i : Nat) : Nat := (if i < 1 then 0x2971018000016ceac15d2026082a3460cc263a0240000045820000c9438000386fd633e00002860f03310067a0afd9c340001c6f4d0ad5cba1028700db60a280525810a000040d3dd58bc0620000bb02e8c04000180e0913248509023c000080d1503740000619ba06f40db8024ec01b0000084280001c38f9055c936cc319f02e8106d8e97c20182590000284ec05d00394306478029a8bd000516a90000046b661142066800014161e33f00006057a866a00000000183c202026262f0c2b014c0000030a719cf81678165a10f2034d8603c09400edb18ce04610406604170ccf04bd4324835c30cef8e7284a620e1e04148170000020015053d00d8c70c20fd389b70c0e01d800aea13280000418180c7406d3448b402961023177c09ac000060e2a140480f40001e0f101367844f844e6364700bd095581340000000000000412d2936a05d3044800c6c164639040902c183631bd531200a80001205e806e20a4a86ae212ab1a9f063d4158c0f3804dc81d000000000c03bca070821a613c411720064045ee38e70b288d27800dc11aa04c00003830ea12bb0bda8350c29740ef71ae98395c2aaa0b1603e9822a454840c960c2285dae473007a80845004c0000000030c680c100515c0ad50ab90b53440d213f91b100001c11de0eb4156b06078711229dc11a502874323a087503aa08e9d109408f6079181a20664602000006047ec5ef418260c32048140bb3717706c7000d42f94369508cd04840001c0a3c09c00001405622ecb023901b64019a0b71134c0970000000000000000000000000010caf85100000621f50d180002c2666064403f00000433c40e691b328bf18079418a9092b0692004fe03aa02f9053800000000000000000c155021520a04862c0274c146501d80002447f02a1a02af09e00620e479c7320000185aca1533a0e000000001a111e020701458187d682e0beb80600001e06a101680003c0de615b40bd285d72eece1730000580dc000080348146b807c0000000041717801cc18c41792075500100000a0ce00005833000edc2da219a00dc084af209cf02b31ce4c149e05a907c8000280f9e04390b8c091b041e0000405a1035e412a01094005800038128a099505db0438586c4132610c48564000082f2c013485360038000060aa70cb785d600001217581948000204c8012445030008014020c2380a14006460800017400004608556060d100141400c085018147d00090418100020028406082000320013011458d1024e800400004020438800181801a0000340780012200b81121c02c02a8500567020e0a0868604001812e1848c361c001320000002085060003a9802041011000f841c24302000800a0a3c1220a0848a3a2c0e8000108200c851404015090038004060018232143944c20709021ce8d05d4180 else 0xf0510058501ef819a817d900b820c60000a0503811040b6c4efe0d078b6400d76050e00ee05be057e0000805328c360085012e40880436d0dd115895194b8627c260000010b69059b81ce6073c13041e2c0290407f00006855a42d5609e806fa031744572123a1a308057462ca00f61660d54884e52188a07e3845bc1ac2167b17a60248c09a2033503d98188982f605791694092742480000807aa8e36431d02ba000018355ca6d941bf108c00bf81f54045307c4d23402f1282ed0ac359598001e00e5155602f2803d606c00007039301ffc2776059d0430873e8177709b682e2032f945a20a090686c8e400cf0000080e2c02000005185998e4849b220900000092c458c2122d038c81e180cde2afa01238adec10266871023308e58605c1061083c85ffc46400004011a0097c2d98172205a80002007d681bc1cb08b0ec644a0b6d121d85a482e9416e103028b29c573c089f0c8082bdc7258f37205f8024f41a280e8e29150148c259a08360a78834e0195e0cb609ad808b0295809dc09f5054102a3e04fe02a1857242e1a3315014580d6c1008350101678a788545029b00827053301d2c058a05ce9c57c20b61939077181390338e39a109bd8cefc269200d50b1884760239401a7045a8c44822e6216b024b005a017a0337100978af8c34bc194704fd03d3c216c19f60a3d029640dca0c4928d9024240234365303cb021bc119a0d09054a8d8486bd012d604230cf740c31029b17ff840c817cc2ce506c8049bc441417ed67b40222c07ee201f6320bb8d0042e1963094300210715426140258000981f6e22450384025c034d42810000705a2012242c2809ce85ae81fc0000c0b000cb141844)
def mdata12 (i : Nat) : Nat := (if i < 1 then 0xe0580904c011802010220f01030644b054170340d0781102c01282e0f8182d0240407600801f05c0c1881202c00e0c0330020101a0682c090120ea02e004020340c0c4160781102520b8020081a04061a0480900060809a0e0c4008020902a0501a41905b02c0d078160403b004c0481400098188240a83c069c16048082740018320808a0501a060c40083c0a94330240b0340d0781504c01380200828320614188150580d03800154110281d58103481e0b03c08116008c1e07c0e034160480b0040160b60f81c0882e007443044130340e0541d02c01302c06818388382481409002700401020600c2e0782e05800185c1d07c0d0380b0040204415248400800290281d01a0e81408ac1102c030341e05448f8260e8160081c0a929c18c1700c0e0441c0c80918280a03e0702204141f05c0e004110281cd8280a03e060c409012008c140501f030610081202401f81e0a80604061b02c0f000640741604381f81e0a8060406180dc1418c0f00c1e04809005e078060f0220a6c0f05c0302030a07e0b804098140e819f00c0d0481c0c068d82e0f81c09012006c1703c00180120241cf8060702a0e82404861c0dc0f004170781202381f81e0b03e0482400062305c1d03c01028112538338160181a0b03c087c0f008170741102303182e0181c0e820188123157860bf6deb2e87702b47d872b5355ea89d2828974009e4cdfa6532ca935c80a34716c895c3320db0227e6bd91e1eece737b869b9ed6667eb2f191ec305e8adc9662ad2539a8f13a697e494a3790fe8203f49ec8ea66ea34f9950bfe5b42b9947899248821e8ff074e3661978b9054626210b873030212c07082580aa000fff68532803ffda360a00fff4c582803ffda84ca00fff60951803ffda54ca00fff60d71803ffd8348600fff4c951803ffda160a00fff69932803ffd814ca00fffaa982803ffaaa60a00bff68963803fdd314ca00ffe69182803ff9854ca00ffe4c910803ff93258200ff760a33803ff9a04ca00ffe69932803ff9a060a00ffe44182802ffda360a00ffb4c982803ff98250600fbf4ca66803ff9a360a00ffb60e22802ffda160a00bffaa982803ff93160a00ffe60532803ff9a54ca00ffe2a582803ff98254600bff68d21803ff93254600dff2a582803ff98344200ffd4ca11803ff9a14ca00ffe60930802ffda54ca00ffd84582803bfd8160a00ffd60e11803ff98348200ffe6a132802ffeaa4ca00ffe68582803ff9835c600ffc60e11803ff18584600bfe68d82802ff9a850a00fee60a448027fca960a00bfe2a5828027fca94ca00ff64c532802ff8a94ca00bfeaa982803bf98160a00bfeaa932802ff9a54ca00bfe68963802ff9a060a00ffa4c982803ef93299a00bfe68582802ff9a24c200ffa61622802ff9a14ca00ffc60a11803fd9828ce00 else 0x19c0b00c0d004140c0b9182a0f81c09016000c1f0380d0306019059078120203b005e0b81a04066000c1816c1d0704d044081881603c014160338120580018644812838148150703a0340a04c0168960701a060b20e0903281409802d07c0a0208813410198160303b00584383e060c40882e0070770340d0540b00030e85e0701a070382c0583302205802f05c0d038120203b0006118020081c090101c0c1f0381d04c001a282d816060ca0b026007c1505c0d034020480907440a82a000f4080620703a04940a0340c1880011411078152064068181f000230120883c0aa063054170340e0741102c01282a0680204061503c010041502030d82a0b83e06818310240480260780d03046020610081105483182e0683c0901600706305c0d070100c80b00403101a060881b02c008220503a90cc0d0341)
def mlevel12 : Packing := (78,3,7,0,0,13,0,mdata12)
def mindex12 (i : Nat) : Nat := (if i < 1 then 0x7128685dea01d4311106a704abc6b501aa4066584cc01e00000e08ef0c1b406c011120b99857bc35a00005039800000000409bf0b100000c26a000060ca9839d00000000b064d8bc202ea6020f16d80001c6b2828aa08398b620481a12dd04420dad4678838861c27869483918097a09a60c6b8333210d103358419c2f7609040dee8ae90729e032f07ef02f6436c405f10ad6898382928127c335f0ed5038462c9b0abb0e800253407d801358c79c1894301d1b090f5f41910016c0a76062e4319a07f9175980a54321c2bfe060004c901fe211e2195d83d2429ae00a40e93845f80d341d64040f0d820029e12c60e4e0f3241d5a052a1a888497838320faf02480003c6c63717603da41cd01c1608e20e7b59a90244004fb16400002856ca38631104899400000000e0c2203654003a08780da70a63441e0000007968aed06ca037c30ba285db81f60000313b5022c0299e0ae718f901b5017260e30000708c8c00843339046a05f680970185f166986b88044a07a0000483cc00000000804ee8202c2a440bae061605e6c12b819c515f48680016b2293e041e871b843d425a706840466030121c761ac08344020801ccf0d34807080c9a3b88036108b842c361d4c0692805d4162623120bf20658c362c07e6004c0be90124e408816b0021b474980632070b83c702d781581061d01ca438be382a02e801c0426d0239b1de281e6412da16a4180181434025e1bac0c1982cb80cf224bc07770b2f86e68a15e0876dd57459c416e11a41015d8631e05570164835b835ee1486186611e245b202fcc09f102bd0358412420a8384bc44f5a0a1709c500c3023181c440b2486fd81a6003fe05578c38433ca202f0cd5089fc29462b4b04c7823ec171015b302250518c7946058802399a76c738000090dbd8e3f4552a35260c8800000001a0c660eab064dc09ce37a20dc205e1042ea36fe167d846f02800000f0b790b7502e5a14f20a3881034261e11a0074800024536821610d4e054c4071225d7a7e58b6844dda0e510d240d18c6382034000000000000000000000482780000016de01c901734105a214a190d04ac871ae0f75077c0f1e8205e3a240ae48933c43a802d03020002123d00000203172297002d11020222020425010700260203010200031f0c00231d030428083306000112210014060100060f0602041c0f000b1d02171c1c00002a07010000220102010100001f090802040a03030000083614051b08061a100e3e00071b00080a0e020000090d0616030353a6010f020a16000101210b07010115040009160003001a04050e0202114406390907004e000000040400120905070e2204000f050b42040200020a09051b0000010304050308051202100f03010c01040700070001280f010d02080808060003230c001627140400 else 0x48453849bc264105110269039aa11231d3e8297441660e40028b858c4194a01b2021c03d4445a81051207704554756e3d32125400308387a3cf00c9481a2c50823401063e8c8d81460000c135d83a342760000903780000431e2084bb2a6808f4167603d000018420c10ac27ba0d9586ae421f601f60e86055180f88169d029a04fc4616b64800e5f81c5841040ad416e50ebd817f607621b940c51c0d4e10b00004044381560000f0e8805f385e461c0002a48d6f430c01677101e8bd40dd641097001685eb4620c01eb0214829e872d01be90156855b04e6821bd06c580c5c25c20b0e003600e84394c03b303bf048102d040f9e0cde83564556214b904e082a0026e00006093289fa80e80000e0c55004001ec6369105b58a75c1da22ac70b61816c40bdc04550c15036c0000809400002001f831b010c000070870004a03c1f0079040c43aee19fd1660189dc5e2000000004042b85794048500c80002c0caa252c01af8b1708e6000090cbf027c000182f8b17ec0c970696a0c5d0b0584f7c44d2e4ad009e0cf88571210140b3405554119800d30d14039a0872a285e05240e6b82ca00004015a8ddd064980f8601e30d358126e0bb90a1d82d000000000a05000000000100d700005800e052a4005f94eb8d1705fe0000f1b3086741c42c3b2f1caf861fc343e2740000282a480c4803e40d8203b280c2e0dc0000789d598420000000060dd8854d009130a0800018132000030b880104000041bc4005c874c0000c04db120c029a028943ad721c300bd86bc0000b10d505c2c0ad21bbb08e6048400000000f00c000000000000091900806902fee01d11deb0b51439c80ac901478607406642a22269f833b0284015f481c80000000100fe2235a8da8417c41b98065b04f0808c000000005004706c8e15d0000384c7c79c80df312b000000000a2e24044e83060226a3c490cc10379c4e02075e012483358246603780d40000000000000605bf0b4203106296000070e84000041399004000000001c060c19910565064ca194000030459431c0000506d00001c69482a1b0a2800000001212821aef86d5c645e3d5b0a880ce800b3c0dd609d00627836741a300000000000)
def mdata13 (i : Nat) : Nat := 0x20f038280809003032070203c1409003c0e0b008380808681c0a010503810187c37f4400ffec1401ffd32803ff305007fe4ca00
def mlevel13 : Packing := (4,2,7,0,0,8,0,mdata13)
def mindex13 (i : Nat) : Nat := 0x3822000000d400038085b07c0c70573036816ac06a40480005084000000058278040a0b301bf02db158208d822e887b09160cc41a10050000227c0000000a18c2065025704d201820480006028c15e0094000203bc149626001ff097602100c9c00d83df139812cc21a8992196000000020b3a0600000000482e70810232c1d500ff00101100000000903c40464591849c02620a60033085c028431c005a89d701de0af80f88215004402800060c4801bc012c8b0026009880a9003d015e083e27a840883e607260f001c681b00100008700114504104f0402000002c368a258a00818
def mdata14 (i : Nat) : Nat := 0x6050403020100385048403828201810000aaa80ffe00ffa00
def mlevel14 : Packing := (2,1,7,0,0,7,0,mdata14)
def mindex14 (i : Nat) : Nat := 0x1de145217540002
def mlevels : Nat → Packing
  | 8 => mlevel8
  | 9 => mlevel9
  | 10 => mlevel10
  | 11 => mlevel11
  | 12 => mlevel12
  | 13 => mlevel13
  | 14 => mlevel14
  | _ => emptyPacking
def mindex : Nat → Nat → Option (Nat × Nat)
  | 9 => lookupWord 1 2 0 4 0 0 mindex9
  | 10 => lookupWord 8 40 5 10 5 1 mindex10
  | 11 => lookupWord 202 690 7 17 9 4 mindex11
  | 12 => lookupWord 222 755 8 17 9 4 mindex12
  | 13 => lookupWord 30 109 6 15 7 4 mindex13
  | 14 => lookupWord 2 8 1 7 2 1 mindex14
  | _ => fun _ => none
def x511samples : Array (Bits × Bits) := #[(0x428cc12264149e267921b62882c098020,0x408cc12020109c227920b008828088020),(0x8aa85f1091ec269926430cb3e82715ec8,0x8b021a8090cc221906430c803433355c2),(0x44508786a292442dd8da28d3b986e000,0x48100304a310440d99023080a84ca831),(0x1012d4293b00a1ad02450c440713c17d5,0x100cc0da100a18d02058c0095120164c),(0xbe33328302ef1050c6da53c26841081d3,0xbe33328202ef005084da43d2686922993),(0xa3318ad04c72499c87d6210000260241e,0x22310e944c20419486560000012647c9a),(0x6c3da63de99255c4192c487a414e4ba2c,0x643d843d69125584190c4072414c4aa2c),(0x994d51c91087f83b3028dcf774c920744,0x994e51491186b82b2028dcf7744920344),(0x74c0200612cc8963e8b2538e0ca092122,0x10c2210212cc086260a0330c2a81a0101)]
def x511columns : List ColumnInfo := [(529,0,494,0,11),(192,0,831,0,11),(320,0,703,0,11),(160,0,863,0,11),(132,0,891,0,11),(66,0,957,0,11),(8,0,1015,0,12),(24,0,999,0,11),(512,0,511,0,15),(80,0,943,0,11),(144,0,879,0,11),(322,0,701,0,8),(156,0,867,0,7),(513,16,486,8,9),(198,0,825,0,7),(0,64,701,258,10),(856,0,167,0,7),(595,0,428,0,7),(344,0,679,0,7),(547,0,476,0,7),(0,128,859,36,10),(537,0,486,0,8),(709,2,312,0,4),(10,0,1013,0,8),(268,0,755,0,7),(14,0,1009,0,7),(258,64,701,0,8),(32,128,859,4,9),(519,0,504,0,7),(844,0,179,0,5),(801,0,222,0,7),(164,0,859,0,8),(4,128,859,32,9),(838,0,185,0,5),(961,32,30,0,4),(296,0,727,0,7),(120,256,647,0,4),(480,0,543,0,7),(689,0,334,0,7),(868,128,27,0,4),(521,16,486,0,8),(597,2,424,0,4),(36,128,859,0,8),(162,0,861,0,7),(172,0,851,0,5),(98,0,925,0,7),(527,16,480,0,4),(679,0,344,0,4),(146,0,877,0,7),(852,8,163,0,4),(520,4,369,130,7),(202,4,817,0,4),(846,0,177,0,4),(546,1,460,16,6),(324,0,699,0,7),(626,1,396,0,4),(902,64,57,0,4),(690,1,332,0,4),(232,256,535,0,4),(282,64,677,0,4),(803,64,156,0,4),(785,32,78,128,5),(270,64,689,0,4),(697,0,326,0,4),(154,4,865,0,4),(896,8,99,20,6),(56,0,967,0,7),(74,0,949,0,7),(148,8,611,256,5),(705,0,318,0,7),(785,0,238,0,7),(533,0,490,0,7),(102,128,793,0,4),(787,64,172,0,4)]
def x511autos : List (List Nat) := [[],[81,130,118],[16,82,131,100],[16,32,48,128,100,80,116],[32,83,116],[32,49,128,81,116,100],[48,33,133,118],[48,129,82],[80,16,33,50,116,131,100],[80,129,50,116],[128,49,100],[128,81,32,49,100,116]]
def mf : Forest := ⟨1023,13,fun j => x511samples[j]?.getD (0,0),x511columns,x511autos,mlevels,mindex⟩
set_option maxHeartbeats 0 in
theorem geomMono : graphValid mf (boundsBefore knownx503) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=4) ?_⟩,listPieces_all (d:=2) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem mfast11_2 : block mf 11 2 40 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
end PEqualNP.Outside.L_meta_3172

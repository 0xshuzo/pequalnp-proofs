import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5002
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
  let len := 11*storedDepth g depth
  let width := len+raw.length+depth
  let recp := packedAt data (i*width) width
  let stored := recp &&& ((1 <<< len)-1)
  let ops := stored
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
  let start := num*(11*storedDepth g depth+raw.length+depth)
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

def deadautos : List (List Nat) := [[],[118,130,81],[100,131,82,16],[118,133,100,131,50,33,16],[116,83,32],[118,116,83,130,49,32],[118,133,33,48],[82,129,48],[118,133,116,83,82,81,80],[116,50,129,80],[100,49,128],[118,100,83,130,81,128]]
def nd5 (i : Nat) : Nat := 0x1819430718b3c561cd2d678c340280c60
def level5 : Packing := (1,10,0,0,0,0,1,nd5)
def nd6 (i : Nat) : Nat := 0x20202021e50c1c78ac39a5acf186805018c1a32818b3c561cd2d678c340280c60
def level6 : Packing := (2,9,0,0,0,4,1,nd6)
def nd7 (i : Nat) : Nat := 0x20203010001110080a01dc0c0138010102ebb72aa0188aeb59708a494624940280c60e32a18bb0e696b3c61a014063057940f158734b59e30d00a031833149734a4946249186805018c132d03dd5a2a1ca2a0310250c60
def level7 : Packing := (5,8,9,0,0,7,1,nd7)
def nd8 (i : Nat) : Nat := 0x20210ed04022280ef04020302020210ec040101010000017a0233040222020300ef073c1a020000000138012c002c060138012c04260601ce012c042606002c0204f1780204000202025c23b802040004f020d204000004f00200000164020304013802030400bc0603a8651805d1605715855150531384711043108410e8330b029090230801b06815050130400f038090100300060d7d8bb4e524a3124a0318306bec5da2292518925018c1915d6b0a494624940280c60b8aeb84524a3124a0140630477a1ccb4452630d00a0318279d0e6d87acf186805018c1cce862ec3d678c340280c60d6d4316696b3c61a01406306f2a58734b59e30d00a03182f992e398b249186805018c13d49734a31248c340280c60f8a429251892461a01406305c721caa4c49230d00a0318339d0c5da7305186805018c19ce971cd65628c340280c609e74b8e6b2b1461a014063049f91cdb1150eb11409431820fd8e6d8ba87408a04a18c187cc6b2b2543a0450250c60a3f239950eb15022812863069d65a6ac850a809409431834f92b25a3285404a04a18c1ed91592814a2a0250250c60f70c9cd316b24e1281286307b8c4e698b58a709409431834eb2d35a42d5406204a18c1a5e96a2d196aa0310250c60d3e4b4968cb55018812863069dc5a6b445aa80c409431834fc2d1da22d5406204a18c127d9734b5124a0310250c6092f439b5a2a1d01881286307968568a8728a80c40943182fb82e4182945186404818c17ec171cc14a28c320240c60
def level8 : Packing := (35,7,9,0,0,10,1,nd8)
def nd9 (i : Nat) : Nat := (if i < 2 then (if i < 1 then 0x8c17f82d11058c320240c60fec941e72c61901206305fe4b4f31630c80903183fd250698b186404818c1fe92734c58c320240c60bdc96a0c1461901206305f64b4e60a30c80903182fd25a6305186404818c17f12d29828c320240c60bfc9694c1461901206307ee4a0f40a30c80903182ff25a89c5186404818c17f92d44c28c320240c60bfc969e61461901206307fa49cd30a30c80903183fd24c5985186404818c1ff82814c28c320240c60bfc969e51461901206307f6434f28a30c80903182ff25a6945186404818c1ff1272ca28c320240c60ffc060a51461901206307fe0a0528a30c80903183ff04e2945186404818c17e92d30a28c320240c60fec941e70c61901206307bd29cb50e51440903183fe84e5945186204818c147bcd55682c949620c60a3de6aab3964a4b1063051ef355598b2525883183e9cce6a4930a70c418c1fca67312498538620c60c5fd5aac41609431063063eead5610b04a18831831bf18b30f516804418c1a7b8c5184a4b40220c60b3dc6aa93124a011063059ee35549492500883182fae1a5acf386804418c1ef1aa44a494720220c60f78d51e524a3901106307bc6a8d29251c80883183fe14a494730a404418c1ff12524a39c320220c60fe7139a614e1901106304dea353610b2c408831827f85a3b02496204418c177aad412524910220c60bbd168492924881106304df8b4262652440883182fd95a631728e204418c16fcad518894710220c60bee569cc44a3881106305fb2b4c62251c40883182ff15a431128e204418c17fc2d098894710220c60bfa5694b44a3881106304ff235952251c40883182fe95a529128e204418c17f4ad292894710220c60b7e46aac3ca3881106305ef235161a51c40883183fe150524928e204418c1ef8aa2d0490710220c60fed141c924e1881106307f689cc49270c40883183fe8505947386204418c1ff42524a39c310220c60fee141e41ce1881106307f709cd20e70c40883182ff85a5907386204418c1ff82824839c310220c60faf141e90ce1881106305fb0b4c62e30c40883182ff85a5317186204418c17fc2d29498c310220c60bfe16a0c2c61881106305ff0b5059630c40883182fd85a62cb186204418c17f82d21658c310220c60bfe16a0a2c61881106305ff0b5049630c40883182bf85ab20b186204418c16fc2d51058c310220c60bbe16a482c61881106305fb0b4c41630c40883182ff05a420b186204418c17fc2d44c58c310220c60bfe169e62c61881106307fb0a0d31630c40883183fd84e698b186204418c1ff4282cc58c310220c60ffc139892461881106307fe0a0a49230c40883182fb8da7311186204418c1fec261c6198110220c6097ec6b2a44a3881106304ff235928e81440883183de91aa94728a204418c1fec262cc28c310220c60 else 0x943183bdc186ac5404a04a18c1cfe2a3562a0250250c60edf141ab15012812863077d8b4b58a809409431839f8543ac5404a04a18c1cfe2a1d62a0250250c60a7f96aca1501281286305bbcb4c50a809409431839f6564285404a04a18c16fd2d1942a0250250c60edd9592815012812863076f8ac540a80940943183be6564945404a04a18c1df62b14a2a0250250c60fdb140a5150128128630767cb4f5a270940943183b3e568a0f384a04a18c1d9f2b44e69c250250c60fe3939a62ce12812863067ecb11592709409431839f6548ac9384a04a18c1ddb283d649c250250c60eed939ab24e12812863077cc98b592709409431833fc588ac5384a04a18c1cfe2a45629c250250c60eef169eb14e1281286307778a0f58a70940943183bbc4e6ac5384a04a18c1df6262d629c250250c60e5f95a2a14e12812863073ecac950a70940943183b3e5689c5384a04a18c1ddb2b24e29c250250c60eef158a714e12812863063e6b15592309409431831f958aac5184a04a18c167b8d4d44a8520250c60bbd86a6a2501901286307ed8a0528a80c80943183f8e4e698b386404a18c18efac45862d510250c60c7bd622c296a8812863063eeb11610b54409431831d7586b085aa204a18c18f3ac2d842d510250c60c7ed622c196a8812863063e6b0960cb54409431831fd588b045aa204a18c18eeac35822d510250c60c7e560ec116a8812863045ee353610b54409431829f75a42d5522204a18c10fbad616a24910250c6087ec6b2b45438812863053f6b505aaa1c409431829f35a42d550e204a18c14fbad216aa8510250c60bfb1684c44a2881286305fd8b425a251440943182fec5a125128a204a18c1cf48d5d4394510250c60f7a4626a1ca2881286307bc224950e51440943182bed1aba8728a204a18c15f3ad216a94510250c60a7f46aea1ca28812863073d62d528e514409431839f65a42d5406204a18c1cfd2d196aa0310250c60e7f1688b5501881286305bbcb4c5aa80c409431839f616a249406204a18c1cbd2b4543a0310250c60e7e85aa41d018812863072fc2d540a80c40943183fac1a7945406204a18c1ff20924a2a0310250c60f7a150e51501881286307fd090728a80c409431829fb5a82d5186204a18c1af4ac54a28c310250c60a2ff688a4d6720b2063051bfb44526b31059031828fbda229358c82c818c147f6d1149ac241640c60a3fd688a4d6020b206304bf335950e814a2903182f78da82c528a30c818c17dc6d396294518640c60fe8c61e51ca2901206307fc294740a51480903183fe14a39c528a404818c17d92d39888c320240c60bfc068ac3c61901206305fe4b5139a30c80903183fb25079cd186404818c13f92d61058c320240c60bbc96a482c61901206305f64b4e41630c80903182fd25a620b18640481) else (if i < 3 then 0xa01406307ce429249230d00a03183f52146249186805018c1f392931248c340280c60fd6851a72461a01406305ef435760a30d00a03182b7a5ab305186805018c1bbd0c59828c340280c60bce969cc1461a01406305ed4b4a60a30d00a03182f7a5a5305186805018c17b92d21828c340280c609de86b2b1461a01406305ef435958a30d00a03182f7a5a52c5186805018c1f390925228c340280c60bde969491461a014063056f4b5628a30d00a03182e7a5a9145186805018c17b92d20a28c340280c60bee969cc5c61a01406305775b4e62e30d00a031826f39a9b085a230ce18c16d78d2d67a8740270c60fce941e80c61a01386307b36a8730e704c09c31826f39a9b0858a51cc18c1ecdaa1ce39c130260c609f5b6b0b3124a03286305af4b50602a1d019431825fe1aab0058a80ca18c1a7b4c5124a4540650c60b9f3688a4d02a03286307cd929340a51501943183f4c966a0528a80ca18c1f3669250294540650c60fd92492814a2a03286307d1d9cd316924e1943183f86ce698a49270ca18c1fc56734c590738650c609bce6a6c21688c3286305dc7b4a4a0924619431829f75aa9cd590a04a18c18fbac556498650250c60e7cd592a1cc32812863057dab4a622b1140943182bfc5a1311588a04a18c1ceeac3546ac450250c60a7f56aa735622812863073f2b1150eb11409431839e9585a87588a04a18c1cfcac1d43ac450250c60a7f56aa71d622812863073f2a8738eb11409431829fd5aa987588a04a18c1cfcaa1cc3ac450250c60e4fd5a0c3d4228128630736e30f592a114094318315f568b0c508a04a18c18efab458628450250c60c7dd622b21422812863063aeb0d590a114094318317b568b06508a04a18c18fdab458328450250c60c7cd592c19422812863063fab11588a11409431831dd586ac4508a04a18c18fcac1d6228450250c60c7dd62ab2502281286304bf635950e811409431831fb58ba87408a04a18c1cf9ab2543a0450250c60e7e550eb15022812863063eeb15590811409431831fd58aac4408a04a18c19bf2b458120450250c60cfd9592c09022812863067f8ac56048114094318317f58aad1388a04a18c18fbac55649c450250c60c5fd62ab44c22812863072bead151a611409431831f758aac9308a04a18c1cebaa356498450250c60e77551ab14c22812863062feb155a2311409431831f758aac9188a04a18c1cbdab45438c450250c60e7cd592a1c622812863073f2a8758a31140943182bde5ab30d404a04a18c1cfb0c5564a0250250c60e7d951eb25012812863077ac30d592809409431839f6546ac9404a04a18c1dbb283564a0250250c60e5e95a2a1d012812863073e4ac950e809409431839f6564a87404a04a18c1cfe0c5562a0250250c60edf16a2b15012812863073f8a8f58a80940 else (if i < 4 then 0x404c008098010100805c070200000180c406f01815102003c040380c40402980e03101c0620380c404f0400801e08013c060380c60407ec0e03101c0620200780c040004e80801e03013c0c027808040000f01809e0301bc0702782004f0180e03101140a0200000000000000e80c05d01dc010200000000e813280c09d010080006a0201d40603d00404059700402020600cc040043100843102020400000000000000000000000000c01004000011b008000001404010000020202000000000404040590101020000014c0202880405300810e01021c020000782004f01809e02010008600200901004002188080120601efbf747b93da3ebef523a45cfce6b72c3915c55e08f027803beadf16ef3769bacdd26dfb6edb5fda46c4f5dbac7d5feadf523a6bd22e8433f39d3cde669731d959ca164af2298eec73633f171892c3de11b07d836c085fe6fa77bcbda5e76eef76fba4dd06e73722b85dc0edd96c6b57da26cc764cb22587abf15e1ae556ceb39585abed59aa9f547a98542a9e74eba6a533296b49ea34d0d281d3e89e8ceea76538c9b34d026713219854bce59b2a794849e64a723c912c83a3d11c28ce45da2a113989143f21ad0b084541ce09b03680fbfa9f88fad7d2bdfdeb2f5179d3c8dddcec87513a2dce8e6c7233881bf4de36deb65db00d696a934eda48d0d67b3341990cb1654b20d8bac37608afe97c6bdb5e9aef172cb705b42d45692b3258dabd559eaa9541a9b148ca20504a7c93b69b54d6a6592fe9594a1247120a8fd473230117089244522090b88364081fe4fc47cb3da1e74f0c76f3ac1d40e907313949c84e3270236e1b50d7a6a634799e0cc264a31998acc285fd2f3173cb705a12cc9608af45632ad9510a5a51628714189de4d826092a892647c23291748aa44d22290f486a42d20b0fc07d03e01ec0f407543931c58e0c6d835519f0c245e42ea1698ab454a29d14a8a3450a27d13a89b44ca25d12a893448a22e113087840e1ff0fb87bc3b01d00e406c43521a10cc86442f41540a6051025a11607f83a01a20c906082a812607c03a01740aa03e01b007c02e000c35f62ea49462494063061afb16524a3124a03182cd7da7292518925018c166bed114928c49280c60cb5f62e93946249406304dafb5851892522a0318237f1abb0a526805018c13bd2d1d8124b40280c60b9dd688a4924a01406304eaeb5851892500a03183c5714928c492805018c163b8d552624940280c60bce969cc5c61a01406305ef4b4e62e30d00a03183f3a5a7317186805018c17bd2d118b8c340280c60bde969ca4c61a01406305ef4b4452630d00a03182f7a1acacf186805018c1dbd0c5d678c340280c60fce961eb3c61a01406305ed434b59e30d00a03182f7a1acac9186805018c173d0d4d448c340280c60fdc862c92461 else 0xe5784008d818a45022d0500040443b410062148a0403c805e924503011e02320801c8101020202681608088811a82022301de08432ec0b80ef06039c04e6046c063080000014c04000ae01018280808001b2043a080008cc0843081022204040a84180bd023304046408d410000005f021c04039c029c100e9020304039c074810103012c038118080810111813c0d020258061234a0502340602580408080811a01c08c04040803f0000fa0301d80fa8180850280ba06e40bf0040c0000051011f0202020209e3e008100b2010078080202d8080810000e90164040001b00407c0200806c01015c1370040a701008050340a04013cd0401002f01000138025a0804e014e02005e02381804f01809e09013c04020170040408700805c0101b802043a080870080010e8100021c02043805603dc015c2206039c04b0016830138025a08073809682012d0370040400027ce06029c0c0288080278e060200b80202b80c0670300ae03b80204b81ae00810e06015c0602b80ee00814e06019c0c0238180470900a2025c24028809704dc01025c24028809704dc010202330204040405d0101029c12f00408027ae1202013802580970480804f5c2404b8240405d40809c012ca8140c05d0101025c12020009e3e00c14a057803050004060404b00ca08940a04060c04e0096020138040609d0400da0801801c23f006095045c0102b802b8440804280ae11b803057005708c12a08015c2202027005d0400ae11817c0503380c06701bc010280780302000010080810004020205d01f701816a08e80e04040407a0080c04000690100d2043a08034810e8280021d0200043a0408740c27802020402a7701010213021d0403a408741009601c808040408054ee0302012c0202580404b008096029c0400053807f0000ea0502020401400770190310220d30300006207a03011f028001640406080000073809c0201d202c808080815a82020602017c040a700980101300202600)))
def level9 : Packing := (328,6,9,0,0,13,1,nd9)
def nd10 (i : Nat) : Nat := (if i < 12 then (if i < 6 then (if i < 3 then (if i < 1 then 0x1270c40883183ff8989386204418c1ffc4a49c310220c60ffe281ce1881106307fe128e70c40883183ff8947386204418c1ff84839c310220c60bfeac44e1881106307ef541e70c40883183df8a43386204418c1ffc5019c310220c60bfeac44a1881106307bf148650c40883183ff8a03286204418c1efc52190310220c60ffc0c5c61881106307fe05aa30c40883183ff02d3186204418c1ff85498c310220c60ffc0a4c61881106307fe161a30c40883183ff0acd186204418c1ff85468c310220c60ffc293461881106307fe139a30c40883183ff0b0b186204418c1ff81858c310220c60ffc2b2c61881106307fe059630c40883183ff0a8b186204418c1ff81458c310220c60ffc292c61881106307fe049630c40883183ff0a0b186204418c1ff81058c310220c60ffc272c61881106307fe131630c40883183ff0ac9186204418c1ff85448c310220c60ffc292461881106307fc049230c40883183ff0989186204418c1ff84a48c310220c60e7ecc4d45881106307fa741651c40883183f79a0f386204418c1fbcce69c310220c60ffc4c4461881106307fe341e30c408831837f1acd186204418c1ef8d268c310220c60ffc683461881106307fe341630c408831837f9acd186204418c1efcd268c310220c60f7e692c61881106307fe118680440883183ff88c3402204418c1fbd4e39c110220c60fde270ce0881106307fe118670440883183ff88c3382204418c1fdd4c398110220c60ffc230cc0881106307ff118660440883183ff08c3282204418c1ffc46194110220c60bff2c0925881106305bfd62482c40883182f7eb0e416204418c17df58620b10220c60bfbac2105881106305fed60c82c40883182ffcb02416204418c1ef752824910220c60b7f8c4ca48811063077ec62a51c408831837f6ad128e204418c1dfb54894710220c60efdaa34a38811063077ed51651c40883183fd6a0b28e204418c1bfb56494710220c60ff98924a3881106307fad29251c40883183ff2b0528e204418c1ff94a3a0510220c60feea62cc2881106307fe528e61440883182bfab1528a204418c1fe94a394510220c60ffca51ca2881106307fe528e41440883183fe290720a204418c1bfa5688c310220c60efd2a4461881106307fe849630c40883183ff4a0b186204418c1ffa4c58c310220c60dfd2b2461881106307fc849230c40883183ff4949186204418c1ff85828c310220c60ffc291461881106307fe140a30c40883183ff0985186204418c1ff84a28c310220c60ffc241461881106307fa728e514408831837f5ad1186204418c1bfad658c310220c60f7c691461881106307fe340a30c40883183ff1945186204418c1ffa461a0110220c60ffd230ca0881106307fe918680420883183ff08c3102104418c1ffc46188108220c60 else (if i < 2 then 0x204418c1dfd507a8b10220c60efea835458811063077f4526a2c40883183bfa291516204418c17fd58828b10220c60bfcac19458811063057f562892c40883182ffab10496204418c17fc58124b10220c60fbea83d058811063077f551682c408831827fab16416204418c15fd58a20b10220c60b7eac4905881106305ef561c82c40883182fbab0c416204418c17f558420b10220c60bfcac1905881106305ff560c82c40883182ff8b02416204418c17fd5889cb10220c60fdea83ce5881106305ff562262c40883182ffab0f316204418c1fdd50698b10220c60feea734c5881106307fb541662c40883183deaa50492204418c1ef552724910220c60ffaa83924881106307fd541892440883183fea9cc492204418c1df554524910220c60f7a892924881106307fd541492440883183dfaa4f412204418c1dfd545a0910220c60efeaa2cc4881106305bf462652440883183dfaa4f40e204418c1dfd545a0710220c60bfeac44e3881106307ef541e71c40883182ffab1130e204418c1fdd50698710220c60ffca81cc3881106307fe462e51c40883183ff2b1528e204418c1ff918a94710220c60ffc8b54a3881106307fe462651c40883183ff229328e204418c1ff958894710220c60ffc8c44a3881106307fe45a251c40883183ff2a9128e204418c1ff914894710220c60ffc8944a3881106307fe561e51c40883183ff2a8f28e204418c1ff950794710220c60ffcac34a3881106307fe551a51c40883183ff2a0d28e204418c1ff94e694710220c60efcaa2ca3881106307fe551651c40883183fd2a0b28e204418c1ff958494710220c60ffcaa24a3881106307fc449251c40883183ff2a0928e204418c1ff94e494710220c60ffca624a3881106307fa529251c40883183ff2b0328e204418c17fd58894710220c60bfeac3ca3881106305ff561a51c40883183bfaa8b28e204418c1ff954394710220c60ffca81ca3881106307fe538e51c40883183ff298728e204418c1ff950790710220c60ffca83483881106307fe539a41c40883182ff2b0b20e204418c1df954590710220c60ffca82c83881106307fe539641c40883183ff298b20e204418c1ff150490710220c60f7e8c4521881106307bf541e90c408831839faa8b486204418c1efd505a4310220c60f7a8c2521881106307bf541290c40883183dfaa07486204418c1efd4a3a4310220c60f7e894521881106307bd449290c40883183dfaa4f406204418c1dfd545a0310220c60ffa892501881106307fe528e80c40883183ff2907406204418c1ffc1689c310220c60ffe0944e1881106307ef159e70c40883183f78a0f386204418c1ffc5069c310220c60fde2734e18811063077f151670c40883183ff8a0b386204418c1ffc4c59c310220c60ffa0924e1881106307ff14 else 0xc60ebfaa3d04a011063075fd51a82500883183afea8b412804418c1e7f525a0940220c60f77a92ca4a011063077ed51a51d00883183fe624928e804418c1feb4a494740220c60cff8b5562a01106307bdc49291500883183dfaa4b30a804418c1ff512498540220c60fbea824c2a011063075fc5aa80d00883183afea8f406804418c1d7f545a0340220c60fbb892501a011063075fd50e80d00883183ef6947406804418c1fbe5679c340220c60fdf283ce1a01106307ef939a70d00883183bfca8b386804418c1efe5259c340220c60ffb0924e1a01106307df941270d00883183ff4947386804418c1ffc4c29c340220c60fbf280ce1a01106304ffc62e50d00883182bfeb15286804418c1f7e50194340220c60f5f6944e19c1106307afb49a70ce0883183f79985386704418c1fbe4e1a0138220c60e6fea4cc398110630777d30ea04c0883183f7c9c3382604418c10ffd8ba9328220c60c7feb4d48941106304bff62e944a08831831ffad351a504418c1afdd6998528220c60d7fab4d0094110630777c61aa44808831833fead151e404418c15ff58aa0f20220c60cffab45469011063057fd62a83480883182bfeb1539a404418c19ff568a8b20220c60edf8c3d459011063057fd62a82c80883182bfeb14416404418c16ff58920b20220c60bdfac3905901106305f7d61882c80883182ff6b06416404418c17fd58220b20220c60bff2c09059011063057fd62a72c80883182bfeb15316404418c1df754894920220c60efbaa3ca49011063077dd51a52480883183beea8b292404418c1bfb56894720220c60efdaa44a39011063077ed51e51c80883183bf6a8d28e404418c1fe34a494720220c60ff9a524a3901106306ff55a261480883183bfaa9130a404418c1fdd4e698520220c60feea62cc2901106307fd529261480883183ff294730a404418c1feb4a394520220c60affac5501901106306ff95a270c80883183f7ca0f386404418c1fbe4e69c320220c60eff2a2ce1901106307fd929270c80883183ff4947386404418c1ffc4c29c320220c60affac54a19011063077dd52240c80883183beea8f206404418c1df754590320220c60ff9a51c81901106307fd938640c80883182ffab10526204418c17fd58529310220c60bfeac3968881106305ff5614b4440883182ffab065a2204418c17fd58529110220c60bfeac3928881106305ff561494440883182ffab024a2204418c15fd18aa4f10220c60f7e894527881106307bf549e83440883182ffab1139a204418c1fbd5079cd10220c60bfeac4165881106305f75618b2c40883182feab08596204418c17f95832cb10220c60bfeac19658811063067f462ea2c40883183bfa313516204418c1dfd188a8b10220c60efe8b45458811063077f44a2a2c40883183b7a30f516)) else (if i < 4 then 0xdf522929248831839efa8f494924418c1cf7d46a4a49220c60a7bec5125249106305bdf62092924883182defb0c494924418c1cf7d4624a49220c60b7b6c09252491063057df62a829248831839efa93414924418c13f7d8b20a49220c60afbec5105249106305bdf62482924883182fafb0c414924418c17f6d8120a49220c60bfbac01052491063057df62a72924883182defb13394924418c15f7d8a98a49220c60b7bec4cc52491063043ff628b4ca48831825ffb105a6524418c12fed812d329220c60c7feb4d489491063063ff5a6a3ca48831831ffad351a524418c18ff969a8d29220c60e77ea3d259491063073bf51a92ca4883182d7fb0e41690c418c16dfd8620b48620c60b7bec2105a43106305bef60c82d21883182dfbb0441690c418c16ff58020b48620c60c7beb5164a43106305bf7608945218831831efad449290c418c16fe989a9138620c60f7b4c25289c3106305ff3608944e1883183d7da9341e70c418c1ebed28a0f38620c60f5f6944e69c31063073fb4a2a2ce18831839fda4d51670c418c1dfe180a8b38620c60f7b4c25259c3106305bfb62682ce1883182dfd31351270c418c1ebed07a4938620c60f5f6735249c31063073fb516924e1883183deda5049270c418c1ef692824938620c60fdb6839249c3106307bdb498924e1883183f6d9cc49270c418c1df6d4524938620c60f7b6929249c3106305bfb626824e1883182dfd31341270c418c1e7ed28a0938620c60b7f6c4ca49c3106307bbb496524e1883183f399cd30a70c418c1efcd2598538620c60fee662cc29c3106307bf3492614e1883183fe924930a70c418c1cbfd49a0f38620c60f5f683d219c31063067fc602b54a18831825ffb105a650c418c11ffd8ba9128620c60c7fcb4d489431063063ff5aa924a18831833efad449250c418c19ff56a2c128620c60bbfac4160943106305fdd610b04a1883182ffab0458250c418c15ff5872d540220c60aff8c5567a011063067fc5aab3d00883182fde30b59e804418c15ff18aa4f40220c60aff8c5526a011063057fd628b2d00883182f7eb0e596804418c17df5862cb40220c60bfbac2165a01106305fed60cb2d00883182ffab04596804418c17fe5812cb40220c608ff8c5d45a011063067fc62ea2d00883183b7e30f516804418c13ff18ba8b40220c60b7fac4945a01106305dfd620a2d00883182ff6b06516804418c1aff18ba4b40220c60e7f8c5525a011063073fd51e92d008831839fea8d496804418c1ef7184a4b40220c60aff8c5525a011063057fd62892d00883182efeb10496804418c17fe58124b40220c60affac54e5a01106305bfc626a2500883183dee292492804418c1df754724940220c60efbaa3124a01106307bdd49892500883183beea8a492804418c1ef752524940220 else (if i < 5 then 0x59ea2c418c14ff989acd51620c60c7fcb4d66a8b1063066fe59eb35458831821ff31749aa2c418c1cbf967a4d51620c60a7fcc4d64a8b1063063fe5a6b1d458831831ff2d3582a2c418c19ff5692c151620c60affac4160a8b1063067fd5a0b05458831833feace582a2c418c1dbf1672c151620c60cffab3160a8b1063067fd58cb05458831825ffb105a6a2c418c18ff969a9151620c60c7fcb4d46a8b106306efc59cb05458831831ffa935a0a2c418c18ffd69a9051620c60cfdea456328b1063063de612b55258831829ffb105aa92c418c14ffd862d549620c60c7feb516aa4b1063053fe62ab45258831831ff2d55a292c418c14ffd8a2d149620c60b7eec1168a4b1063043fe62ea45258831825ffb1652292c418c16ff58029149620c60a7fcc5567a4b1063053fe62ab3525883182cff31159a92c418c18f7d6a2c949620c60c7bcb5164a4b106306bde5a8b25258831835efad059292c418c1cf7d482c949620c60d7beb3964a4b1063073df51cb25258831835efacc59292c418c1cf7d462c949620c60c7fcb5562a4b1063063fe5aab0d258831823ffb105aa92c418c18ffd6a29349620c60c7fcb5528a4b1063053fe62a93d258831829ff31549a92c418c10ffd89ad449620c60c7fea4d6824b1063047ff62ea41258831831ffad54a092c418c18ffd6aa4c49620c60cff6a456124b106306bfb4a2b09258831835fda4d58492c418c13fad83ac249620c60c7fcc4d6aa0b10630677e61ab55058831833fe3015aa82c418c10ffd892d541620c6087fec5d49a0b1063063fe62ea4d058831839ef30952682c418c10ffd8b29341620c60d7bcc256920b1063043ff62ea49058831821ffb1652482c418c18dfd49acc41620c60d6fea4d6620b10630637e526b31058831825ef31359082c418c18f7d49ac841620c60d7bea4d6420b1063063fb526b09058831831fd29358482c418c18ff549ac041620c60d7faa4d6020b1063063fc526b01058831831ffad549a72c418c10ffd892d531620c6087fec516998b1063063ff526b44c58831831ffa9359e62c418c1cdfd49a0d31620c60e6fea4ce698b106304bff614b4d448831831ff2d351aa24418c12ff98ba4d51220c60c7fcb4d45a89106304bfe62e92d448831829ffb1539a924418c1cbf987a8b49220c60a7fec5505a491063053ff62882d24883182dbfb0c416924418c16fed8120b49220c60b7fac0105a491063053ff62a72d248831829ffb15316924418c16f7d8529249220c60a7bec55262491063053de62a931248831839efa8f498924418c15f7d8a9cc49220c60b7bec4ce62491063073df526731248831839ef313514924418c1db7987a8a49220c60e7be93d452491063073df49aa29248831839ef293514924418c14f7d8aa4a49220c60a7bcc55252491063073 else 0x240c60ebdaa1d01a012063077ed50e80d00903183ff49cd186804818c1ffa4e58c340240c60ffd262c61a01206307fe938a30d00903183ff4985186804818c1ffa4a28c340240c60fbd280c61a01206307fe940630d00903182feeb1139a404818c1fb75079cd20240c60b7bac4905901206305edd61c82c80903182faeb0c416404818c17f358320b20240c60bfaac1105901206305fdd60882c80903182fecb02416404818c1fb75079cb20240c60bfbac3cc5901206307f5d41a62c80903183fae9cd316404818c1ff350794720240c60ff9ac34a3901206307fcd41a51c80903183fe69cd28e404818c1ff358294720240c60ff9ac0ca3901206307ddd41e81480903183fe694740a404818c17f75889c520240c60ff9a51ce2901206305fdd62261480903182feeb0f30a404818c1fd74e698520240c60feba62cc2901206307fcd28e61480903183feaa0530a404818c17f758794520240c60fdb8c3ca2901206305fdd61a51480903183fce9cb28a404818c1fe34a394520240c60ff9a51ca2901206307fd540a51480903183fea9c528a404818c17d758614520240c60bf9ac18a2901206307fcd28e80c80903183eeea05406404818c17f75889c320240c60fdba83ce1901206307edd38a70c80903183feca03386404818c1fe74a294320240c60ffb280ca1901206307fc962230c80903183fe4311186404818c1ff25878c320240c60ff9283c61901206307fc961a30c80903183fe4a0d186404818c1ff24e68c320240c60ff92c2c61901206307fc861630c80903183fe420b186404818c1ff24e58c320240c60ff9262c61901206307fc960a30c80903183fe4305186404818c1ff25028c320240c60ff9081461901206307fc938a30c80903183fe4985186404818c1ff24a28c320240c60ff9051461901206307fcd41e30c80903182fe6b0b186404818c1ff35028c320240c60ff9a51461901206307fc940630c80903183fe49c3186404818c1ff24a18c320240c60affac416a8812063057ed60cb54409031833f6ad150e204818c1dfb4e6a8710240c60efda72d438812063077ed316a1c40903183fda9cb28a204818c1df954394510240c60ff4a51ca2881206306bf862e90c40903183dfca0f486204818c1efe506a4310240c60dfd2b4461881206307fe941e30c40903183ff4a0d186204818c1ffa4e68c310240c60ffd272c61881206307fe931630c40903183ff0945186204818c14ffd882cb52620c60c7beb3164a931063063df594b25498831831ffa93594a4c418c11ffd882d549a20c608ffec296aa4d1063053ff620b4d458831829ffb085a6a2c418c18ffd692d351620c60a7fcc4d68a8b1063063fe5a6b45458831829ffb125a2a2c418c15ff5802d151620c60c5feb4967a8b1063062fe5a4b3d4588318337fad0))) else (if i < 9 then (if i < 7 then 0x53ff620a4ce29031829ffb0a526714818c1cdfd4998b30a40c60cfdeb3d4398520630776f39aa1cc2903183bb798b50e614818c10ffd8b29328a40c60a7fec41499452063053bf614a4ca29031833f7acf50e514818c1dbb967a8728a40c60cfdeb35439452063077af396a1ca2903183bd731528e514818c1fab96794728a40c60efcea1d02945206307fa728e814a2903183bf3a8738a514818c1fe9ca39c528a40c6087fec59491452063063fe526b40a29031831bfa93598514818c18df949acc28a40c60cedeb35431452063067ed50eb00a2903182dfdb0a5a290c818c16fc982acf48640c60b7f6c44e6a43206307afb41e73521903182dfdb1059690c818c16fed822cb48640c6097f6c5905a43206305afb61c82d21903182dbdb0c41690c818c16fad8320b48640c60b7e6c1105a43206305bf960082d21903183d7da0f39690c818c16fed8798b48640c60f6f6834c5a43206307b7b39a62d21903182dfdb0a58a90c818c1e7ed07a0548640c60b7f6c2902a43206305bf960081521903182dfdb1138a90c818c16fed8898548640c60f6f662cc2a43206307bf340a61521903182dbdb0c28a90c818c16fad8314548640c60b7f2c00a2a432063072ff52683ce1903183b77a0f50e70c818c1ebed07a4338640c60bdd6c39688c3206305feb614b4461903182ff4b005a230c818c17f8982acf18640c60bfd6c44e68c3206307eeb41e73461903182ff5b1059630c818c17fad862cb18640c60bfd6c11658c3206304feb62c82c61903182df5b1241630c818c17bad8720b18640c60bed6c31058c3206305fe360882c61903182ff4b0041630c818c1fbad079cb18640c60f7d6934e58c3206305feb61e62c61903183fb5a0d31630c818c1fdace698b18640c60bbd6c41628c3206305eeb61cb1461903182fb5b0c58a30c818c17ead852c518640c60bfd6c29628c3206305fe9600b1461903183df59cd48a30c818c1eface5a4518640c60f7d662d228c3206307deb41e81461903182df5b1240a30c818c17fad8520518640c60bfd2c01028c3206305feb62271461903182ff5b1130a30c818c17fad8798518640c60fed6734c28c3206307f6b31661461903183ff1a0530a30c818c17fad8794518640c60fdd4c3ca28c3206305feb61a51461903183df5a4d28a30c818c1feace594518640c60ffc4b14a28c3206307fe340a51461903183ff19c528a30c818c16fad8914518640c60bed6c30a28c3206305fe960051461903183f75a0f38630c818c15fb5832d540240c60affac116aa012063053fd614a4d009031839fe29341e804818c1cff1499cb40240c60efda73543a012063077ed396a1d00903183bf698b50e804818c1cff149a0540240c60e7f8a4ce2a012063073fc52651500903183bf6a8728a804818c1feb4a394540 else (if i < 8 then 0x2d538e204a18c19ff16a98710250c60cfd8b54a38812863067fc5aa51c409431833f62d520e204a18c1dfb54790710250c60efdaa3483881286307fad31641c409431837fa31750a204a18c1dfd548a8510250c60efcaa1d428812863077f550ea14409431833fe2d550a204a18c19ff16aa0510250c60cff8b54c288128630777d51a61440943183f9e98b30a204a18c1fed18994510250c60ff68c44a2881286307fb45a251440943183fdaa9128a204a18c1fed12894510250c60fd68c3ca2881286307fb541a51440943183fda9cd28a204a18c1fe512494510250c60ff6a724a2881286307fb531251440943183bd2a8728a204a18c1fe954394510250c60ff6aa1ca2881286307fa520e514409431837de2d528a204a18c1df954394510250c60efeaa1ca2881286307fa528e51440943183fda94728a204a18c19ff16a94510250c60ff5a51ca28812863067f85aa80c40943183bfc2d5406204a18c1ff6124a0310250c60efd2a1d01881286307fe920e80c40943183ff8a85406204a18c1f7e502a0310250c60ff6251501881286307ff128a80c40943183fdc98b386204a18c1ffa4839c310250c60afdac54618812863067ec5aa30c40943183fd2945186204a18c19ff16a8c310250c608ffec416a88128630477f618b54409431823f7b065aa204a18c1de9d4394510250c60ef6ea1ca28812863067fa5aa80c40943183fd9945406204a18c1fced0698b08250c60fe76734c5841286305fbb61481420943183f9d98b30a104a18c1fce4c598108250c60fef261cc08412863053ff608b55289031829ffb105aa93c818c14ffd8229341e40c60c7fea4d689cd2063072ff52683ce69031829ffb105aa92c818c14ffd822d549640c6087fec594920b2063053ff608a490590318317fa9359c82c818c18bf949ace41640c60c6fea4d6620b20630637e526b31059031831f7a9358c82c818c18fb949ac641640c60c7eea4d6220b2063063f6526b11059031831fda9358482c818c18fe949ac241640c60c7faa4d6020b2063063fc526b01059031829ffb0452672c818c1cbfd49a0f39640c60e5fca4d079cb2063063ff526b3cc59031839bfa9341a62c818c1cdfd499cd31640c60afdec44e6a872063076ef41e735439031829f7b12416a1c818c15bbd8720b50e40c60aedec3105a872063057e760882d43903182bf5b02416a1c818c15fb58020b50e40c60edde83ce5a872063057ef61e62d43903183bb7a0d316a1c818c1ddbce698b50e40c60afdec116a947206305dee622b34a39031829ffb105aa914818c10ffd8b29340a40c60a3fec4149a052063053ff614a4d029031829fbb04526814818c11fb98ba8740a40c6087fec59492052063063fe526b29029031837d7acb28c814818c18ff149ac040a40c60cfdaa1d602052063 else 0x450250c60dfbab25022812863077ed50e811409431837faac5408a04a18c13ff58b20450250c60affac5102281286306fdd590811409431837faac4408a04a18c17fe58120450250c60affac54e2281286306dfd5a2711409431837eeac9388a04a18c1bfd5629c450250c60affac54c2281286306dfd5a261140943183bbea8d308a04a18c1bf756498450250c60dfeab14c22812863057fd62a311409431836fead1188a04a18c1bf75648c450250c60efdaa1c62281286306ff558a31140943183bfc315404a04a18c1b7e568a0250250c60eff2a3d01281286307f7861a80940943183bfca8d404a04a18c1f7e506a0250250c60dfb2b25012812863077e950e80940943183bfca87404a04a18c1bfc562a0250250c60dff2b15012812863077f850a80940943183efca05404a04a18c1fee4a2a0250250c60dbfab4501281286306fdd592809409431837faac5404a04a18c17fe5889c250250c60dbf2b44e1281286306ff95a270940943183bfca91384a04a18c1fbe5079c250250c60fdf2734e1281286307fb9316709409431837ecac9384a04a18c1bfc5629c250250c60dff2b14e12812863077f950a70940943183f7c9c5384a04a18c15fb58a8c250250c60dbdab4461281286306fed5a2309409431837e6ac9184a04a18c1bf95628c250250c60dbfab4461281286306fdd592309409431837faac5184a04a18c1cdfd4998730250c60eedea1cc39812863057fd62a73480943182dee313512404a18c1dfb4e6a8720250c60ef9aa25439012863077dd512a1480943182bfeb1440a404a18c17fe58120520250c60eefaa34c2901286307f7861a80c80943183efca0d406404a18c1ff6544a0320250c60efd2a1d01901286307df940a80c80943183fdc945406404a18c17fe5889c320250c60fdf283ce1901286307ef939a70c80943183fdc98b386404a18c1fbe4e29c320250c608ffac416a8812863067fd620b54409431833beb0c5aa204a18c19ef5852d510250c60cfbac216a8812863067ed60cb54409431833fab045aa204a18c13ff5882d510250c609fbac216a8812863057fd620b5440943182bbeb0c5aa204a18c15fb5832d510250c608ff8c55688812863057fd628b4440943182fdeb0a5a2204a18c17fe5812d110250c609ff8c5d488812863067fc5aaa4440943182bfeb144a2204a18c17ef58525110250c60bff2c09288812863047fc62ea3c409431833fe2d541e204a18c11ff18ba8d10250c60cff8b55068812863067fc5aa73440943183f9ea0d316204a18c1fcf4e698b10250c60cfb8b51248812863067ec62ea1c409431833f6ad150e204a18c1dfb4e6a8710250c60ef98925438812863047fc62ea1c409431833f62d550e204a18c13ff18ba8710250c60cff8b55438812863067fc5aa81c409431833fe)) else (if i < 10 then 0x86306f7a598b1501943182fddb0a58a80ca18c17fe5802c540650c60b7f4c4d42a03286305bfb624a1501943182efdb1050a80ca18c17ded8628540650c60bfb6c2142a03286305feb60ca1501943182ffcb0050a80ca18c15fe98aa4540650c60f7b492522a03286304ffb62c91501943182efdb1048a80ca18c17eed8524540650c60f3f4a4d02a03286307d7a59a81501943183cfda4940a80ca18c1f76924a0540650c60f774a4ca2a03286307f3a59a51501943183ddda4928a80ca18c1fe692494540650c60ef56a1ca2a03286307fab20e51501943183ed9a0528a80ca18c1fecce294540650c60a7fec1149a032863071fe52681501943183edba0528a80ca18c16fe989a9138650c60bf76c29289c3286307afb4a283ce1943183d7da5139a70ca18c1f8ece698b38650c60b7f4c4d449c3286306bfb5a2924e1943183d7da0f49270ca18c1ebece6a4938650c60f77662d249c3286306fdb5a0924e1943183f6da0e49270ca18c1fb6ce624938650c60ff36629249c3286306feb5a241ce1943183f75a0f20e70ca18c1fbace690738650c60ff5662c839c3286307bbb316914e1943182dfd31340a70ca18c1ebed289c538650c60f5f6934e29c3286307ebb316714e1943183d7da4938a70ca18c1fb69249c538650c60fdd641ce29c3286307f3b316614e194318397fa9341e70ca18c1dbbd07a8738650c60f5f683d219c32863063ee626b54619431833f63015aa30ca18c17bbd872d118650c60bf9ec21688c3286305faf61494461943183b77a8f41e30ca18c1ef392824918650c60cfd6b55018c3286307eeb41e70c61943182bfeb15398a04a18c19f7549ac850250c60cfbaa3564281286306fdd39ab21409431833e6ac950ca04a18c19f7564a8650250c60df9ab2543281286306fdd592a1940943182bfeb1530ca04a18c1bf756498650250c60efdaa1cc32812863067f5526b11409431837fab11588a04a18c1bfd188ac450250c60dfeac3d622812863067f551eb11409431837fab0d588a04a18c19fd546ac450250c60dfea73562281286306fb5616b11409431837fab0b588a04a18c1bfd583ac450250c60cfcaa1d622812863067f550eb11409431837f2a87588a04a18c1bfd543ac450250c60dfea71d62281286306ff530eb11409431837fab03588a04a18c19ff549ac450250c60cffaa3d622812863067fd51ab11409431833f6a87588a04a18c19ff543ac450250c60cbfab45422812863067fd5a2a1140943183b7e30f508a04a18c19f7564a8450250c60dbfab4542281286306fdd592a11409431823feb16508a04a18c15ff58828450250c60cbfab41422812863067fd5a0a1140943182bbeb0c508a04a18c19f756428450250c60afdac19422812863067f5588a11409431827feb17408a04a18c15ff58aa0 else (if i < 11 then 0xbb7b0c58aa1ca18c15f3d842c550e50c60afdac0162a872863057ed608b0543943182bf7b04526a1ca18c14ffd8229350e50c60afdec54e6907286304bff620b4d429431829ffb10526a14a18c14ffd8429350a50c60c7fcb4d48a852863063fe5a6a35429431829ff313512a14a18c1cf794924950a50c60c7feb4d4828528630637f526b31429431833bfa91598a14a18c12f7989ac850a50c60c7bea4d642852863067df522b21429431833f7a9158ca14a18c19dbd66a8650a50c60cf9eb25432852863067fd522b01429431833f6a87580a14a18c10ffd882d548a50c60a7fec416aa452863053ff628b4522943182ddfb0a5a2914a18c16fed812d148a50c6097fcc5d48a452863063df5a8b25229431831ef2d4592914a18c10ff98ba8748a50c608ffec416aa452863063de5a8925229431821ffb135a8914a18c18ffd6aa5048a50c60c7feb5526245286306bbf4a2b29229431835dfa4d594914a18c18f7d6a24848a50c60d7beb4124245286306b9f594921229431833d7acb50c914a18c1afed28ac248a50c60d7f693561245286306bda492b09229431833f5a87584914a18c10ffd892d540a50c608ffac016aa05286304bfe62ea4d029431821ffb16526814a18c14fdd8229340a50c6097fec5949a052863063ff5a8a4d02943182dfbb04526814a18c15ff18aac140a50c60cff8c056a2052863043ff62ea49029431821ffb16524814a18c18ffd6aa4840a50c60cfbeb51242052863063ef5a6a19029431833f7ad520c814a18c1afed24ac240a50c60dfb4925612052863067eb50eb09029431837f5907584814a18c11ff18aac040a50c60c7faa4d602052863067ed50eb01029431829ffb10526714a18c10ffd892d530a50c608fdec196a9852863053ff620a4cc29431839bfa8d492614a18c1dd7d4624930a50c60cfdeb3d4398528630776f39aa1cc2943183bb7a8d20e614a18c1cdfd46a4530a50c60c7feb51498c52863053fe62a944629431829ff31549a314a18c1cbfd47a0f48650c60c7beb5164a43286304bfe62e81521943182ddfb0a4a290ca18c18f7d6a24948650c60b7f6c2149a03286305bfb608a4d01943182dfd31359e80ca18c1aded692cd40650c60def6b3966a03286307b7b49cb3501943183cfda4f41a80ca18c16fe989acb40650c60b7f4c4d64a03286305bfa626a2501943183dbd2cd49280ca18c1e7ed06a4940650c60f7b4b4924a03286307bda52492501943183deda4e49280ca18c1fd696624940650c60f7b693124a03286307ddb418925019431837bd2cd58e80ca18c1cfa989a8740650c60efd4b4d43a032863077ca492a1d01943183bf430150e80ca18c1dfa949a8740650c60e7f4a4d43a03286307f6a59a41d01943183ef5a0d20e80ca18c16fe989ac540650c60b7f6c4962a032 else 0x7a0e49260c60e7bea3d252493063053df62892924983182defb10494924c18c16f7d8224a49260c60c7feb4d489c93063072ff52293ce49831839f7a5151e51cc18c1df3d4724928e60c60afdec5162947306305f6f618b14a3983182fe7b0858a51cc18c1dbbd47a0f20e60c60c7beb5164a453063073df520925229831839efa8e492914c18c18ffd49aca48a60c60c7feb5525245306306b7f59a929229831831efad4490914c18c1af7d6824848a60c60d6beb3124245306306bdf594921229831833f7ad528c914c18c1bdbd6694648a60c60df5eb2ca3245306307bce49251922983183daf3094a2614c18c1ed7984a4b30a60c60e6fea3d24985306307b5f4a0924c2983183bafa8e492614c18c1ed7d2724930a60c60f6be92924985306307b5e494924c2983183db7a5128e614c18c1fd392494730a60c60eedea3c83985306304bff620b4ca29831831ff2d3522514c18c1cf7d4924928a60c60ff1c924a39453063063ff5a6a40a29831825ef313590514c18c18f7d49ac828a60c60cfbea45641453063067ef5aa418a29831837b7acd20c514c18c19ff548ac028a60c60f7b4c2527a03306305bfa626b2d01983183deda4e49280cc18c1ef6d2524940660c60f5f693ce4a03306307bda49291501983182efdb1048a80cc18c16fe98994540660c60b7f6c48a2a03306305dfb62051501983182fedb0828a80cc18c17fad8314540660c60bff2c00a2a033063073fd51e92d00983183beea8e492804c18c1dfb54794740260c60efdaa3c83a01306307b7d49661500983183fae24930a804c18c1fdb4a398540260c60feda41cc2a01306307dd849280d00983183efc9c9406804c18c1f7a483a0340260c60fbf0b1501a01306307df848a80d0098318397fa9338e704c18c1dbbd439c738260c60e6fe93d4398130630737f496a1cc0983183bb7a8738e604c18c1ddbd4394730260c60e6fea1d22981306307f2f28e514c0983183bbea87382604c18c1f9f4e39c130260c60d6feb4cc29413063057fd62a83c80983183b7ea8f41e404c18c1dfb54794720260c60eefaa3cc2901306307f6d28e61480983183fd694728a404c18c1df754724910260c60efdaa3c83881306307f6d28e61440983183fd294728a204c18c1ff948394510260c60eefaa1cc08813063051fe622b35499431831efacc592a4ca18c18f7964ac552650c6097fec1d622932863063ff526b1149943182bfeb04582a34a18c10ffd822d549a50c608ffec416aa4d2863047ff608b55269431825ffb045a6a24a18c18ff969a8d51250c60a7fec54e6a49286305bdf608a49249431829efb15498924a18c14f798aa4c49250c60afbec54e62492863073df526731249431831f72d359aa1ca18c157b988acd50e50c60ef9e73124a872863063ee5a6b1543943182)))) else (if i < 18 then (if i < 15 then (if i < 13 then 0x933863053ff610b4d489c31831bf2d259aa44e18c14ffd822d54a270c60c7beb5164a513863047ff620b55269c3183d6f3094a2734e18c14ffd882d549670c60a7fec316aa4b3863053ff608b55259c31831efad459292ce18c1eb7ce62c949670c608ffec416aa4b3863043ff624b54c59c31823f7b065aa62ce18c1e9fce698b49270c60e7acc15492493863073de626a41249c3183baf30d520924e18c14f7d8aa5049270c60a7bec5128249386305adf61c941249c3182defb0a4a0924e18c1eb7989a0e49270c60e7bea4526249386307adf41e931249c3183b6fa91398924e18c1eb7d289cc49270c60f5be73525249386307e5f39a629249c3182bf7b0c5aa51ce18c15fbd822d528e70c60bedec3168947386305fcf610b44a39c3182ff3b045a251ce18c17fad812d128e70c60bf5ec2928947386305dee622b34a39c3183d77a5139a51ce18c1cf3d4924928e70c60fd9e73124947386307e6f39a62c839c31829ffb105aa914e18c1cbf96aa0f48a70c60c7beb5164a45386307adf41cb25229c31823ffb105aa914e18c19bf96aa0f48a70c60e7bea4124a45386307adf41c925229c3183d6f9cc492914e18c10ffd892d530a70c608ffac016a985386307a7f39a924c29c3183f2f9cc492614e18c16bfd872d148670c60f5be83964a43386305aff61c945219c3183d6fa0e49290ce18c1abfd69a0f40670c60bddec39688c3386305fcf610b44619c3182f77b0e4a230ce18c1ef392824918670c60affac116aa01386305ebc616b3d009c3183d7ea0f496804e18c1ebf4e6a4b40270c60fdba83924a01386307edd398925009c3183b7eacf50e804e18c1fbb4e694740270c60fdda73483a013863075fd50e80d009c3183e7ea0f406804e18c1dfb5488c340270c60fdda83c61a01386307de940630d009c3183ff4a03186804e18c1f7e5018c340270c60e5fe945439c13863072ff49aa1ce09c3183b77a8730e704e18c1dbf543a0138270c60e6fea4cc398138630776f50e61cc09c3183bbe987502604e18c1dbf5439c130270c60fcfa61ce0981386307e7d39a62c809c3183f769cd28e404e18c1f9f4e698520270c60fdda83c619013863057fd620b54409c3183b7e2d541e204e18c1cf754924910270c60fdba83924881386307edd398924409c3183f76a0f20e204e18c1fbb4e690710270c60f5fa83d21881386307eed41e30c409c31823ffb105aa204e18c19bf96aa0f10270c60cdf8b54e08813863063df5a8b25289831839ef3094a2a3cc18c1cf7d482c949e60c60c7beb5164a4b3063073df51cb25259831829ffb1458a92cc18c16dfd862c549660c60c7fea4d6224b3063072ff51e83d249831829efb154a0924c18c1cf7d28a8e49260c60a7bec55272493063073df52293924983182befb1541c924c18c1db7d4 else (if i < 14 then 0x1831efacc592a4d018c1cd79662c952680c60c7bcb2562a934063053ff614b1549a031831ffa9359ca4d018c18ffd49ac452680c608ffec116aa4f4063063ff5a8a4d27a031825ffb045a6a25018c18ff969a8f51280c60e6bcc3549249406305bdf61ca4924a03182defb04524925018c1cf7949a8e49280c60a7bcc5527249406304f5f62ca3124a031839afa92518925018c1cd794928c49280c60f6be939462494063053de62a93124a031839bfa9251a725018c11ffd852d548a80c60c7feb5149a454063053fe62a93d22a031831ff2d549e915018c1cdf94928d48a80c60a7fcc5526a454063063fe5aa92d22a031831ef2d4492915018c1ed794624948a80c60f7b492161a454063043ff626b5122a031833bf30d5a8915018c137f580ad048a80c60cefeb5146245406306d7f5a0a3122a031831ffa93594915018c18ffd6aa4a48a80c60d3feb45252454063063df5a892122a031834efad0490915018c1af7d6524848a80c6087fec59499454063067de5a8924a2a031839efa92492515018c1af7984ad228a80c6087fec5d491454063043ff62ca48a2a031825ef313590515018c18f7d49ac828a80c609fbec59241454063067df5a8920a2a031835efad2490515018c1bd7d6624828a80c60c7faa4d60145406306f7c51ab00a2a031837ee249580515018c18df986ad350280c60c6feb4966a8140630637f5a4a3540a03182efeb0e526805018c177f58529340280c60bbfac1149a01406305dbc616b3d00a03182e7eb0e596805018c17775842cb40280c60bbeac1165a01406305dfd608b2d00a03182efcb02596805018c1e7f149a4b40280c60abfac5125a01406305dfd60892d00a03182efcb02496805018c167f189a8940280c60f3b8a4924a01406307d5c51892500a03183ceea4c492805018c1e7752524940280c60faf8a34e4a01406305dfd614b1500a03183eee24858a805018c177f5812c540280c60f3b892522a01406307d7c51891500a03182efeb0a48a805018c1e7f52524540280c60bbfac0922a01406304dfd62c51500a03182cfeb1228a805018c177758414540280c60bbf2c08a2a01406307de862e30d00a03183ef42d3186805018c1f7a5498c340280c60fbd0a4c61a01406307de959e30d00a03183ef4a4f186805018c1f7a5648c340280c60fbd2a2461a01406307de949230d00a03183ee4249186805018c1f7a4e48c340280c60fbd262461a01406307de960a30d00a03183ef4305186805018c1f7a5628c340280c60fbd0b1461a01406307de948a30d00a03183ef4245186805018c1f7a0a28c340280c60f7b892522a01406307fe862e30d00a03183ef4a51186805018c1ff21248c340280c60ff9892461a01406306fea62e30d00a03183ef48c3402105018c1ffa461a0108280c60c7fea4d682 else 0x287dc47d7c7d347cd07ca47c5c7bdc7b947b4c7b047aa07a587a1079c87964791c78d4785477f0778c772876c4764475fc75b4756c750874a4745c73f873b07368732072d872ac7280721c71b8715470f0708c70286fe06f986f506f246ef86eb06e686e206dd86d906d2c6ce46cb86c706c286bfc6bec6bc06b946b306b046abc6aac6a806a386a0c69a86960691868d0681867d067a467946784673c66f466ac6664660065b86570652864c4647c643463d063a46378633062cc62a06258621061c8619c6170612860e06098603460245ff85fe85fbc5fac5f9c5f385f0c5ee05eb45e885e405df85de85da05d585d485d385cf05ca85c605bfc5bb45ba45b945b685b3c5b105b005ad45aa85a7c5a1859d05988595c594c592058d858905864583857f057a85760571856d05688565c563055e855bc5590552c54e4549c543853f053a85360533452ec52a4524051f851b05168513c50f450c850805054500c4fe04f7c4f504eec4ec04e784e304de84da04d584d104cc84c804c384c0c4be04b984b6c4b244b144b044aa04a584a1049c8499c497049444918490848c04878484c482047d847ac47804754470c46c4469846504640461445e845bc457445644538450c44a84498446c44404414440443d843ac4380433842b842704244418c4144411840ec40a440243fdc3fb03f843f583f483f003e9c3e8c3e283de03d983d503d083ca43c403bdc3b783b143acc3a683a583a2c3a1c3a0c39e03998396c390838c03878384c383c37d8377437483738370c36e036603650362435dc35943568352034f434c834803470344433fc33ec33dc3394338433583348331c330c32fc32d032c032b032a03274321031c8312c310030f0307030442ffc2fec2fa42f942f682f202ed82eac2e802e542df02dc42db42da42d942d302cb02ca02c902c802c382c282c182bec2bdc2b942b682b582b2c2b002ab82a8c2a2829e02998296c294028f828b0284c282027d82774272c26e42680267026602618260825c02578254c250424d824902464241c23f023a8236022e02298225021d02150210820a4205c1fdc1f781f141eb01e301db01d141cb01c301b941adc1a5c19dc195c18f8185c1814174016f816b01668162015d8159015481500149c1454140c13c4137c133412ec126c120811a4110810c0105c10300fe80fa00f200ed80e900e480e000db80d700d280ce00cb40c6c0c400c140bcc0ba00b580b2c0ae40a800a540a2809e00998096c0908086c082407dc0778073006cc0684063c05f405ac0564051c04d40454040c03c4034402c4027c0250020801dc0194014c010400bc0090004800018f7d6a2c948673460f7ba9412488139a307fcc49251c409cd183dee249486204e68c1ff31248c310273460a7ecc1567a934063063df59cb2549a03)) else (if i < 16 then 0x9d1471142913fd13d113a513791331132112d9127511bd117510bd10750ff50fad0f650f1d0e9d0e710e290de10d990d510d090cc10c790bf90b950b310b050ad90aad0a650a01099d0955092908c5087d081907d107a5075d071506e90685065905f505c9059d0571052904e1047d0451040903c10379033102e902bd02750249020101b90171014500fd009900510024ff34feecfec0fe78fe14fdccfd84fd3cfcf4fcacfc48fc38fbb8fb70fb0cfae0fa7cfa18f960f918f8d0f8a4f85cf7f8f7b0f784f73cf6bcf674f62cf600f580f538f4f0f4c4f498f450f3d0f3a4f340f2f8f2b0f268f23cf1f4f190f0f4f090f048efc8ef80ef00eeb8ee38edf0ed54ed0cec8cec28eba8eb60eb34eaeceaa4ea5cea14e9e8e9a0e958e910e8c8e880e838e7f0e7a8e77ce734e6ece6a4e640e5f8e594e54ce4e8e4a0e420e384e33ce310e274e22ce1e4e180e138e10ce0c4e07ce018dfb4df50df24def8deb0de68de3cddf4ddacdd80dd38dd28dc70dbf0dba8db28dae0dab4da88da24d9f8d9b0d984d958d8f4d890d82cd7c8d764d700d6b8d68cd644d5fcd5d0d588d55cd4f8d4ccd484d420d3d8d374d32cd2e4d2b8d270d228d1e0d1b4d150d108d0f8d0ccd084d058d010cfc8cf80cf38cef0cea8ce44ce18cdeccddccdb0cd84cd3cccf4ccaccc64cc54cbd4cba8cb7ccb50cb24cadccab0ca4cca3cca10ca00c9d4c9a8c97cc96cc940c914c8ccc8a0c858c82cc800c7b8c770c70cc6e0c67cc634c5b4c56cc524c4dcc494c44cc3e8c3a0c33cc2bcc274c22cc1e4c1b8c18cc160c134c0ecc088c024bfdcbfb0bf84bf20bebcbe58bdf4bd90bd48bce4bcb8bc8cbc60bc34bc24bbf8bbe8bbd8bbacbb9cbb70bb44bb18bb08bac0ba78ba4cba04b9d8b9acb980b954b90cb8e0b87cb834b7ecb7c0b75cb730b6e8b6a0b658b610b5c8b580b538b4f0b470b3b8b338b2d4b270b228b1c4b160b0c4b028afe0af98af50ae98ae50adb4ad6cad08ac6cabd0ab88ab40aaf8aab0aa14a9b0a968a93ca8f4a8aca880a854a828a7fca7b4a750a6eca6c0a678a5f8a5cca584a558a52ca500a4b8a470a428a3c4a37ca2fca2b4a26ca208a1c0a178a130a0cca068a0049f849f209ed89eac9e649e009db89d709d449d189cd09c889c249bf89bcc9b849b3c9af49aac9a649a1c99d49970992898e098989850980897c09794974c970496a09658962c95e4959c953894f09438942893fc93b49388934092f892b09268923c91f491c89180913890f0908c90448ffc8fb48f6c8f248edc8e788e308de88d848d208cbc8c588c2c8be48b9c8b388ad48a708a0c89e0896088fc8898886c880887a48740871486b08668860485a08558851084c88464841c83d4838c834482fc82b4826c820881c08178813080e880a0805880107fc87f487f007eb87e707e else (if i < 17 then 0xa9a861a7fda7b5a76da725a6f9a6b1a669a621a5f5a5ada565a539a4d5a471a461a451a409a3dda395a369a321a2f5a2c9a281a255a229a1c5a17da135a0eda0a5a041a0159fe99fa19f599f119ee59e9d9e559e0d9da99d459cfd9c999c359bb59b6d9b099ac19a799a4d9a2199f599c9999d9955990d98c59899986d982597f997b19769972196d99691964995e5959d9555950d94c594999451940993a5935d931592e992a1923d91f591ad91659139910d90e190b5906d90418ff98fb18f698f218ed98e918e498e018d9d8d558d0d8ce18c998c898c5d8c318c058bd98b918b658b1d8af18aa98a618a1989d18989894188f988cd8885883d87d987918765871d86f186c58699866d862585dd8595854d852184d984ad8465841d83d583a983618351834182f982b18285825981f581e581b9818d814580fd80d18089804180157fcd7f857f3d7ef57ead7e657e397df17de17d997d6d7d5d7d317d217cd97c3d7c2d7be57b817b397af17aa97a617a3579d1796d792578dd7879783177e977a176e976a1765975f575917565750174b97471742973c5737d733572ed72a5725d721571cd7185712170bd70596ff56f916f2d6ec96e656e1d6dd56d8d6d456d196cb56c6d6c256bdd6b956b4d6ae96a696a2169d9692168bd6875682d67e5679d673966d56671664565fd65b56551652564c16479641563cd6385633d62f562c96265623961d56171612960e16099605160255ff95fcd5f855f215ed95ead5e655e015db95d715d455d195ced5ca55c5d5c155bcd5b855b3d5af55aad5a655a1d59d559a9597d593558ed58a5585d5831580557bd57755749573956f156a9567d5635560955dd5595554d553d54f554ad5465541d53d553a9536152e15299526d522551f95195514d50e950a150594ff54fad4f814f394ef14ec54e994e354e254ddd4d954d694d594d2d4cc94c9d4b754b2d4ae54a814a394a0d49e149994951487d481947ed47c147b147a1477547494739472946e146b54689465d461545b14585453d44f544e544d544a9444543e14399435142ed42a5425d421541cd4185413d40f540ad40813fe53f9d3f393e493d913d493d1d3cd53c8d3c613bc53b613b193ab53a5139ed3989394138c1385d381537253651360935dd35b13585352134d9349134493391332d323d31f531ad30d9309130492fe52f9d2ec92e652e1d2d652d1d2c652c012b652b012ab92a552a0d29e129992951290928c12879281527b1274d270526bd265925f525912565251d24f124a9244523c5237d231922b52289222521dd2179211520b1206920211fbd1f591f111ec91e651e011dd51d8d1d611d191cd11c891c251bf91b951b691b051abd1a591a1119c91981193918f118a91861181917991789172516dd1695164d160515bd1591152d14c914 else 0xb010862020041500b80e0205902020570100809e8025c0407701014404027dc04057010084320210cb80e04095021c04701803211b4184320200c846d0560a846c09901846c701c1046c70181381609a025d0700002429c07040011b02690411b1c060409940809e70101140b0370182270470880809e701010226020279c10042188202040928226502820308061020204029822604f04bc02f08821c08502a80814388690808b8202045028226087018474080810434f0082d4087020862029827f06f0182b808081bc2008f820706603bc24f01820608f08280808f820308218bc12a023c0608c82a40c143821d0610d3c020b502340808f809ef0828080874280c101880a6218850e080c33c24f08009e087424062218809e09a424062218809e08fc208620808206060a8821c21a027e0808288680870102d40ae02680513c0208f82ef0e218823404218821c04e0382520405960080410cf8020410cf80204029886304029a8080410b807208f8180720530100a6a0201280805901042e03b813803f00013803f000100c1202050e0870200a7e00980e0610cc008041c1a03410cf82520502680a066021c0410cdc06041c188090205d021c05701180f040305c1211e823408029980e0410302020402c000c04074e00c04074e00c04074e00c0402c600c0580300b00490300886204b01340b0202e0080b8d014100b80202800820402e0088362038101599034808062188082680202e540b0500301650550100800870802060604b206310374240994280a009a01021c21881086207d026406203820604403e40c0818180b802c0100b89030100b89034108620818101580a881240c2188100c0099013c020b5023e0818202d408181050e081c10862f09241c081820862f0081060950200b98020100a602b01fc00040950080a60748100a60660100a60748100a71030100300200c021c05202020605e0b9e08de061e035e025dfa5df25deddde95de4dde05ddbddd75dd2ddcc9dc65dc1ddbd5db8ddb45db19da99d98dd929d8e1d899d7e1d799d751d725d6ddd695d64dd605d5bdd53dd4d9d491d42dd3e5d39dd339d2d5d28dd229d1a9d129d0a9d045cfe1cf99cf19ceb5ce51cdedcd6dcd09cca5cc41cbddcb79cb31cae9caa1ca3dc9d9c975c965c91dc8d5c855c7d5c771c6f1c6c5c67dc635c5d1c5a5c55dc515c4b1c469c421c3a1c391c381c339c30dc271c229c1fdc1b5c189c141c0f9c0b1c069bf5dbeddbe41bdc1bd5dbcddbc79bbddbb95baa5ba41b9a5b941b889b809b7a5b6edb66db609b5c1b579b4f9b495b44db3e9b3a1b359b2f5b2adb249b201b181b11db0f1b0a9b061affdafb5af89af41aeddae95ae69ae21adf5adadad2dacc9ac81ac39ac0dabc5ab61ab35ab09aac1aa95aa69aa21a9d9a991a949a901a8f1a8))) else (if i < 21 then (if i < 19 then 0x780a433901826406901c0a47b9018140026803901ac060590180882b90182640790198020590188060590198020500d0925e00848c143846d0c11b281e05e0080c040440a007812406041c1541c05601084e00d010406031022c0603c009e0401a00f20405602520402e3407e00c1e410027c164100514100b9904009e07a0480e81202046d80e04046e813501c1e80e03a0381d304022681304022681305a04c081fd02074e81205a04808905a0481d20404680b804641c0680f030020480c0000216224005206085c0c8120320480889102504680f04022680e0501a0381d204022680e040000018680e04018680e04074ac1305a03b4060a58181d2b04c140403407022188088620300018408862036038081d3304d40a06a04d40405a0382b80550140c0009e02027b4060405120600402780809e03a04940705a03940604123680e05a03940604a04d40605a03d40605501c0d40702123680e0550180886302022680e50181809f503013802067811034e00819e06029f80205603a40605202001a0402500819e03b81001e0b101021750100c40600d00c40401d00c405501280204204808145a0581280e03a00909404a0380900fa0081680202046280f50181e81402501e80208f018144020550802040a8e802040a8e80204051680205a0082a204503014404005680205a00807e05200812305200c0c80302d0181460420d8080dcd0141404000a021881fd06028141004a03d40504501023205a00c080ef0203bc0d4050200051109404a03d4060404180e80302501e80204041c0d40703a00c0e80201f81014404881014402d018144040004180980f0270440824a10c814000b0027044082d410c9c06070002780821c02e03808004330270140e00902708021d047086008218821d08708021c0402c0080a00278060011011e0990301580948100880300200b80f002010158011026809502046d0020140080209480c8080300708021c0400201ae08701c00862708021d0611b1c070402820080406b821d0406b821d0402c1c200874181d2708021d060749c20087418862708021d0602c1c20087419c1002c0100b0708021d070070440c0401c110211b1c070470140819f605821c06041821c040b500a7040ae00c02008099021c06a023c200bbc18861020080240a00802202021c242886308008020080b010d0101d201f0100b002074980e0470100e00902a023c06040002e0080b0a05010000180e05941403c050300603c0c000046d0300000011b00c808802025a06a023c060401b4062218980f80242a808020009a2815202021d0821880886280c81000862087410000b00202c04340402c1c1204802009c100270400846c4121c200670100c00040080820b021d0609900a0802020708000001802086304010004b0080087004 else (if i < 20 then 0x40b0405902020404b013a04502824a04018c036f0800ee08082941806782030608f82020501880806208701402c08701402c0300b40c02c0209e40a02c081c10206818821c07d00816e07e01c06203018a02c04081a42701882a20901880a02d01881406203018c0c0620301882070401380d004f0481bc04f04bc06071019c100328101d20342c240250200ca0180102140400100faf00981406f01bc0204604825205701dc04040850450031018088114180e06e04b802063018100c0b82520bc023c0409481580660102520570180825203101005c08b02140608500c40409481580570180dc0602056007e04022004404e0381580430181580205600bc06056013c0605601084e00d01281008b014c10a040100b805101181203401021770100c406f0100c00400782e60408580d004f0100cc04f01bc020400d14130570080821603101089050281002a0a502160600d00c40420480dc06501c15c04501410134224005206d0182e60403400cc90f340cd0282170c00014c0821603781243d02085a43c04224005304085805205701dc02057008080d0018012c1e02904022404501cc1e045014c1a04004801e09101cc124240100c408b01021403101021403101014411081440cf00810214f0080b00601c82a304094822c0410880c408b018061e00810c060070096087018004007818a060788081e201481025008e81021602c00a606004801e09101ac240a5821406004b01e09101b802033084c1208581fe093094c200bb81807001402440621c00b002026818c07309029608501b00201402440621c00cc12085b10e0608b00c404007009608701800e02682320602600ca0404900ca05304009604008cc06c0081803421c014c02a00816c02200812802094816c0220081006800981021401501006800994220601a00260580d60260480d00d40580982140401a00260401a00f20450d08700450482780403400ca54382ef0851e94280401814280450d14280450a1422040948159a0581825205601016409481022c50a407e060948094060b10100d0018150e0bbc202160ae01147a50a81147450a0110080bb823206031143504510942e04504014404054940c08cc180f208b0100525138101d28181c1005902015801801440602c14340298181d381801640602c60600590181d2818180e02982142a01801143450a81142809481143470480b006013010a08c81803403101000c21882270608900de0401e80260401d00260401801440520080c80203803680205901e00da0081640621c600c05901e802059006a06803680205901e802029806a0607881c405b0080a604914024405b0180e40603901826405301881e05101b80204123380205101b802040854406e0081ec0609901641c03901881e05b0198020490180c024060206 else 0x800800ca0530400cc10052810124009810025304010023301816008038021c040400e82a20580202a20580202a20580202a20580202a20480202a204704600805802009c1180201600870181021c0860102af5016062060a8005204025010a08181800c090811008085814e06004825404028042600582a308016ac1c00082a007e82803a0518102ae020454c2530710140a58290080a881001c0318100fc085814a0601d4c0c0540200d008b01812c0d40201002401f82060601aec0605381810441882d007402008206034022c06054022c0704081808207418c14c10081c1020702c024c0605000170028b07000208701fa0c087300801880d00801382860530802a0c0501fa0940202a2040a880f40203818f40208981e00202701600205d00808206020009c2408081e00205be06207800816f81881e002055021607800816f81881e002818823406704600205800809c11800811c0780081740202701e0020580080e003d0081fa0780080e00207e010074703600206701600205800f40207e81f40207e81206206281440a02902d00804102d0020581882a3040ab80942681882a20609f82a305007014082ae08701023e0208181fc0581882a30481882a30581882a30581882a30581882a304509a0620a8819c110280b80c01c1102701c0e0620a8c160620a8c160620a8c160620a8c140021c509a0620a88240620301880c06202701c080900898102ae02509a0620a881c001f90300701c09c0d0270140c0020702701c0a02f701811c07020875c0704087409c070281882a20581882a304509a0620a881840b0208700620a881903701881008808700620a742206280201206280201402d00201402d00201402d002412062802103606818a00804818dc0607381820680b200970182020681881006608081202c03b8140620301880c0630301880a02d018810206f01c06207d00814c08981c06204881600302048c080a60008217060596002085c18165800821706027e002085c181658008217060a8813804027e002085c1810b03800c0812302042c0c002ae020000f01808001070205a4081070300502812304502e00304041c09c0c03bc1540a02048c0e00303800c0e002067c101070204b180e818c1a037701811c11800c101070204b6002085c1821c02027dc0404502820204701014404502e0030404b0106058009c220450282020470401440500dbc2003b8202080b682ae07f3c2490981f90cf043c0603b82a30900da4260b6c1a40284282a2060b102bf05805406209fc1bc060b10202060ab823e07f3c2007e02bc24f0802a290982170a027826904027823f0407f02a2040a88226f07140a90981fb0c90982a3040aba426f07022607e828256098c14036909823906f04bc0608981f9018c282a2f07022690981fb0a0279)) else (if i < 23 then (if i < 22 then 0xf802708c280db603b80306073812d0403680b9603c182020368178030370302030404b1c0d0470301450402e780304092dc1d04092dc1ce00c1824a02e1c1d0602e1c07e00c18226036c11c0de00c10226e0080db060898138036c180b8701f80306036c080dae00c11c0d0203680b90405b1c2405141809e090d410088c21c13e00c1016c7090145060909c13e00c1823302073d410a054182b4080c1016c704f80306073a81550441816c04b541106502f8030405b020304504140a080c180be13c009e0613c01450413c009f0405b1411e00c1816c027810b0605b40f802708c1010b02708f80305e009c2304142010b040950508042c182550206b9c07e00c1f803020738008080c18164089c101ce036809e06059022704059022704027d80e04027981604027d80e05202001a0520220080400568020409a023f205821d0800a02023e08081dc06a05410015a0081140c05101140da0081541205101023302027d410a054182320a7020206080c082030250468020404280e80303a00c0e8030201802230500040821d0404080300874181fa04084f0034802c08743005e0874101fa04084f000c002c08743016c036c1083614204f008742141201781005e0874101d208701042605b01380870200b60204b00b60404b00b70404b005e04a025c0504017e80e05a0381d20407e812d0402f80b611b00d20802fd4108188180be13c00d306818c0a06203a0340846da0301015c018021d0604b00a00a8c181d20874102800300201640a8c1805e0a8c14808a02020307603fc01042188080be018814c0c0188100620205b006208741806202057002c07ec180d302034c0b405020278082052023c0405202023e08081c80802a025c0705603a06305502a06205203040c05203540a04081c081ce50441012d020283c0404073b80f040818269040ad40828011b010268081821d0609688320408e0082d00a7028008e025a09282b8081c402680a701380f0202802070404b540aa024181ce0870100a0e03c101640b44100a004e015c06818c100a170180b107000748165a03140b0808081650407382b8080c1821d02027d410a0201816404e012d06074816c81b046c059012d0c07381640411b680c040994081640a8c1006350282030604b02070401880806005701044be0081fa0870200080a88101640a7016814020590111e00848c0808081640410bf80205e0080f8020210b80ee05e037802449021c0803b80902dd008052060a8002a0403d81ec040270026053010082a005301102dd00805206015ac24b0800700a582c02c01c00570600802b8053094c20c0502970800802b8053094c20c0502970800802b8053094c20c0502970800802b804015cc2530830140a582804e0a1814c2530830140a5c2300c0140192073094c2040502970 else 0xe8100da204813412d0181c606034243208f82ef0807e82a204018015c04034242a90a5816018021d0c004801e08d818214031010214031013c020a581440af00812044825020206a038296054818152902825a060a880c40cf0081440cf0081018d1030203060a880801c025821c06003821c04045008e02b8182900818100120950100da015015808b088108130205b0138418c1f80302004801e08d81ac2408501fa0601a00260401480600401781d2048025802051030080b0020a880c40ce008100da00b00d20602400c2040a880802a007010090043821c0600202a20403a80740490300a40c0340200d008b0181240d60081040d600815808b0181003801601104000e011413a008134120a181008e01541040bb0081245008d8100da02036c0e412601813010089813410031013802c0f0138030350400e41208881021c6054164120300088e4120405938080590400814408fc101640207940d410031010088089814001e4080c101e4080c10164e02014c12e0201641208881580303904980c0406480da600811009e00823e04080c0823e080c164100205918020368181640808100da080823f06080816404059009f04059012c036c1816404441016502104014404059020204080c0b80903104823e080c1c001d2059413808036c102030300074c0824a0ad020306e00c081d2059048c11b7807e00a08c41b022e080c5024be00c1008a05f0100a9102812c0604e020205b018081ba03504380204123380204308f813e00825a085048c11b438269b0198140690400b41003010090400b41003010090458020404280d80303600c0846d6008100fd901816a06e00c08108e00c1042fe0081404038030209a042fe00818051102b00206902d00804d04010a04022010c080818110080817008073817008218c1040a218c11413a0201280fc024101e4080c13411a02017803032051c02f093c1c08702c81408fc1027ef08d803060ad027e0928008a0502d0089821d10028009f7095c1ca0518170c13c020204605809c13e00c100da03bc11c0502017bc12f00bc220870280dae0381390604b3c130409280da04e4182552050269060898138036c180b9205023f0609fbc23040280254d0282070802e05080280180da02e4102b409f824a00248140b402260874400a0027bc13202010208bb8170e13c020204e038081af020614080b8d04009e0602e00d2040951c0c0402e1c0d04092822605900a000202030ce03813870341816402f80a00278088a05007e08b4401b27048100b9e00c10164028009f704dc0608f28150e027dc060570181440402f802c08741f80202fc101fa13c00be00b5c1d502821d0f502829602fc180d20874104f0109d40ae008256087431c0c0874101fa13c002c707540a08743016c04e00db0602f80b8603) else (if i < 24 then 0x3502b40a0650100d40402508b40404508c0e81003a04140604044681004044681004044681004501809e0401a0400e404a04540404904340c0a881e808d01016802508c1043203401010402d04824404041340a0410a80d0040410081fa037810104d0281340402024010e087018182041021c070100224040a0490280840bb0081240a03102a81a0401900886302102e80804a038080b803a04819e087418812d02814812d0101680ed0281680ed01010089603d40d06d0140b40502d03740605a03940b05d01b40404502c0819e089817406904c1740740381540d002380207503400881981b40d606c1180ed03000806c03480800681b40d902a009e00c2780202501340d902e81b07902f80305a00942304d0140e80302502c080be03a0300a40c08701680ed02c1680ed0141340b02d0140c80c502c1140b02018015c0410cf80205e00821c04d0301c2040a3444a04094802a04d04b40c07b81821690f0134180310100cc502814c0c44181141202504026204521942804504940c08801949250a01006050a01141202521942804402023e08081942850601142850601009200981480202a0400e80803a0400e81050281012d02504e80204d04827804924a42804921a4280530410700450600c404902dc020491d020204a03815291d01a40a07781242890601580802902d808040120380e4180390280a40c02906640a0490300ac0d90281640a03902814804604640a05902d8080490358020400a00180401800280403ca46c0408f80809203101741808081007001382620601881520560080a40b60081480c0390100f4040390100ac1205e81640460081441805e81640408e81640402600817a0408e80815208f81180808f81180c05e81481202018680e050100a04d40b05a03d40b05502c0d40b0208f823a08d418002350211280844ae03814808c0081200903002380205002380205601c0c808802012009600810165802010009607c14009e00c1540aa0081680202504e8020500503680205502c080680e030004e540a04028046c818823e08bc280680c00201009001402360602402d40570182e60420e1c0c0470300c60401780800a085025406b09015c0478181f80560100da03101023f20528140601a00260407e80c40450482620403400c77010268410021c0c50a00600450a142205701808808081809e02202a20780200dc1370182320601782a20400b02a20402802a304028009e0a8c18164036812c0c603011009a008100da015012c12040012c1e60501280c08b014c0ca0301021d042981506059410ae020181faa00823e06e04b81e08d81f80207e823e0600b023e08081b812607823606059015208b01823e0368158080a88158080a8813c040368102a202002010e0888181fa0340101fa03101089050281089007 else 0x3412d03022006b0300c46d0330300c000d201d5c2008d8200d2f010070060023c100698100d4069815c040a38100e808801017e7078102bc0318100c6018012c10b032c1a06038808a08081cc1aa00811442098813c06701c1148c080c15c040203280c65230252080648172522a8600608153f01812203bc480e4f08023706522822d04031148b0403280c650a9404523022d0ca09a81e04032806004b0680940730781240c0830101e503b8101e503b81240c0830100ca90a81fa0a80201e405ea48b06044017a04001010a08d81c8620510100940874100bea1881440604b28620570180e841c01021690100c406504f40570080a6088022038908822209605a40bd0102460891b7404054818008027020606018005204035340406a246c0807e811005e818004042823606b08109207e81f404088c524080823004042823606418023e080818144018023e06044248c05e8181d3418023e0600300520402f812c04080817a04010e81409881b80ce00827806a04281e08d81c0023e088c1180e502c16013802028a087426013802024208742600808f822307804e008090821d0804e40824208741017a0a801000802f821c0604e4082420874102a0090c10222923023b0608882350408e821d0405ea412088821d090100074c4120402780c48ce05d40a05e821d0a04b00be0470440a41360381009e0205e82230405b023f04090821d04088823f0407381390234062f01848c218823e080c4a4246058862087023c06f013c0208f82020a502a808124886908f03028a08741848cf0082b8087023c1c605824306f010868f078222089c2886808f8102d40ae08606058268a05023e080c402da218825d0608d102e80b086208c82bc100b5023306029bc1c603940a0ae02030c04e3c0c0a2821d08f0702b8080c1817a1233c06f009418087433c1c089980e080c23c1c08f820306079448c04904a80904f01bc020ae022209203815c0a881c48d506012412a027c010601c821c05202441204d071c1203401bc0203981046c0b4822c06d0700c604d043404d030194080342c2410901e4040210f00d004f0100cc04031b41c50701b40c07a0134220210a80d00400700960870181040a88114230204402440408b00822c50a811410503140408802140c425021a0650282200406e94460550480822c037811c1)))))
def level10 : Packing := (1669,5,9,0,0,16,1,nd10)
def nd11 (i : Nat) : Nat := (if i < 19 then (if i < 9 then (if i < 4 then (if i < 2 then (if i < 1 then 0x26881106307fea83440883183ff539a204418c1ffaacb10220c60ffd165881106306feaa2c40883183ff5516204418c1ffa28b10220c60ffd525881106307fe892c40883183ff5416204418c1ffa20b10220c60ffd4e5881106307fea62c40883183ff5592204418c1ffaa8910220c60ffd524881106307fa892440883183ff5412204418c1ffa9c910220c60ffd4c4881106307fea52440883183ff550e204418c1ffaa0710220c60ffd4e3881106307fea61c40883183fe528e204418c1ffa94710220c60ff94838811063077ea90c40883183ff5486204418c1ffaa0310220c60ffc4e1881106307fea70c40883183ff5286204418c1ffa90310220c60ff84618811063077eea4c40883183ff7522204418c1dfba5110220c60ffdd478811063077ee93c40883183ff741e204418c17fbacd10220c60ffdd468811063077ee93440883183ff741a204418c1ffb9cd10220c60dfdd45881106307feea2c40883183bf7496204418c1ffba0b10220c60ffdd43881106307fee81c40883183ff738e204418c1ffb98710220c60ff9ca3881106307fee51c40883183bf7486204418c1ffba0310220c60ffcce1881106307fc630c40883183ff3186204418c1ffaa8110220c60ffd500881106307fea70440883183ff5302204418c1ffa94110220c60dff549881106305ffab44408831837fd522204418c1ffea5110220c60fff128881106306ffaa3440883183ffd49a204418c1ffea0d10220c60dff545881106307ffa92c40883183ffc496204418c1ffea0b10220c60fff105881106307ffa62c40883182ffd592204418c1ffea4910220c60ff7124881106307ffa82440883183ffd312204418c1ffe94910220c60dff543881106307ffa81c40883183fed28e204418c1ffe94710220c60ffb483881106307fea91440883183ff540a204418c1ffa98510220c60ffd4a2881106307fea41440883183bfd486204418c1ffea4310220c60fff501881106307ffa50c40883183fe9186204418c1ff68c310220c60ffe4618811063067fea4c40883182fff5a2204418c1bffa9110220c60effd28881106305ffeb34408831837ff51a204418c1dffa4d10220c60bffd65881106306ffea2c40883183bff496204418c1bffa8710220c60ffbca38811063077ee91440883183ff740a204418c1ffb98510220c60ffdca2881106307fd630c40883183ffb186204418c1bfea8110220c60fff500881106307ffa60440883183ffd282204418c19ffa9308220c60bffd68841106306ffea4420883183bff4a2104418c17ffacf08220c60dffd47841106305ffeb2c208831837ff516104418c1dffa4b08220c60dffd43841106307fde51c20883183ffb386104418c1ffd94308220c60ffac61841106307ff630c20883183ffd402104418c1ffa88108220c60 else 0x1106307ffa90d00883183dfd406804418c1ffea0340220c60ffe4e1a01106307ffa70d00883183ffd286804418c1ffe90340220c609ffd6aa01106305ffeb55008831827fe5aa804418c19ffa9340220c60effd49a01106306ffea4500883183bff4a2804418c1bffa8f40220c60effd27a01106306ffea35008831837ff516804418c1dffa4b40220c60dffd43a01106307fde51d00883183bff48a804418c1ffb98540220c60effd21a01106307bfe80d00883183ffb386804418c1bfea8140220c60fff540a01106304ffeb54e0883182fff5aa704418c19ffa9338220c60bffd689c1106306ffea44e0883183bff4a2704418c1bffa8d38220c60effd269c1106306ffea2ce0883183bff496704418c1f7f9cb38220c60dffd439c1106307fde51ce0883183ff730a704418c1f7d9c338220c60fbfce19c1106307ffa804e08831827ff5aa604418c17ffad530220c60cffd49981106305ffeb44c08831837ff522604418c1dffa5130220c60bffd67981106306ffea3cc0883183bff49e604418c1bffa8b30220c60effd25981106307efe62cc08831837ff50e604418c1fbf98730220c60ffbca39811063077fe914c0883183ffb386604418c1bfea8130220c60fff540981106307ffa804c0883183ffd382604418c13ffad528220c60bffd6a9411063057feb4ca08831833ff526504418c1dffa9328220c60bffd68941106306ffea44a0883183bff4a2504418c17ffacf28220c60dffd47941106305ffeb34a08831837ff51a504418c1dffa4d28220c60dffd459411063077fe92ca0883182fff58e504418c1bffa8728220c60ffbca39411063077fe914a0883183ff730a504418c1dffa4328220c60ffece1941106307f7e50ca0883183ffd402504418c1ffe9c128220c60dff549901106307ffaa4c80883182ffd5a2404418c1bfea9120220c60fff548901106307ffa944808831837fd51e404418c1ffea8f20220c60fff527901106307ffa83c808831837fd51a404418c1ffea8d20220c60fff526901106307ffa83480883183ffd39a404418c1bfea8b20220c60fff545901106307ffa92c80883183ffd416404418c1ffe20b20220c60fff4e5901106307ffa62c80883183fdd292404418c1ff694720220c60fff522901106307ffa81480883183ff530a404418c1ffe98520220c60fff4a2901106307ffa90c80883183ffd406404418c1ffc9c320220c60fff4e1901106307ffa50c80883183fdd206404418c1ffa2d510220c60ffd169881106307feaa4c40883183ff4526204418c1ffaad110220c60ffd168881106307feaa4440883183ff4522204418c1ffaa5110220c60ffd128881106307feab3c40883183ff551e204418c1dfaa4f10220c60ffd527881106307fea83c40883183ff559a204418c1ffaa8d10220c60ffd5) else (if i < 3 then 0x307ff4944e1883183efb41e70c418c1dfda4d38620c60ffed269c3106307ff6834e1883183efb39a70c418c1bfda8b38620c60ffed459c31063077f692ce1883183ffb49670c418c1ffda0b38620c60ffecc59c3106307ff6a24e1883183bfb49270c418c1ffda4938620c60ff69249c3106307ff6824e1883183ffb31270c418c1ffd94938620c60ffccc29c3106305ffeb4ce18831833ff52670c418c17ffad138620c60dffd489c31063077fe944e1883183eff41e70c418c1bffa8b38620c60effd259c31063077fe924e1883183fde49270c418c1dfda4338620c60ffed219c3106307ff680ce18831827ff5aa50c418c15ffad328620c60bffd699431063057fcb4ca18831833ff52650c418c17ffad128620c60dffd489431063077fe944a1883182fff59e50c418c1bffa8f28620c60dffd459431063077fe92ca1883183bff49250c418c1fef24928620c60bffd629431063077fe914a1883183fbf28a50c418c1dfda4328620c60ffed21943106307ff680ca1883183ffb38650c418c1ffe2c128620c60affd699031063067fea4c818831837ff52240c418c1dffa5120620c60dffd479031063077fe93c818831837ff51640c418c1dffa4b20620c60efed21903106307ff670c818831823ff5a6a04418c19ffa5150220c60cffd27a81106306ffe83d408831833ff49aa04418c1bffa0d50220c60dffce6a811063067fe92d408831827ff58ea04418c19ffa4550220c60dffd02a81106306ffe615408831837ff28aa04418c19ffa4350220c60dffd01a811063057feb4d408831833ff526a04418c1bffa9150220c60effd28a81106306ffea3d408831837ff51aa04418c1dffa4d50220c60dffd45a811063077fe92d40883182fff58ea04418c1bffa8750220c60ffdcc2a81106307ff670d408831837fd5aa804418c1ffead540220c60dff16aa01106307ff8b5500883183ffc5a6804418c1bfea9340220c60fff549a01106307ff8a4d008831837fd522804418c1ffea9140220c60fff567a01106306ffaa3d00883183ffd51e804418c1ffea4f40220c60fff507a01106307ffab35008831837fd51a804418c1ffea8d40220c60fff526a01106307ffa73500883183ffd596804418c1ffe2cb40220c60dff545a01106307ffaa2d00883183ffc516804418c1dfea4b40220c60fff525a01106307ff892d00883183ffd396804418c1ffe98b40220c60fff564a01106307ffaa2500883183ffd492804418c1fee24940220c60f7f504a01106307ffa82500883183ffd392804418c1ffe98940220c60fff4a4a01106307ffab1d008831837fd50e804418c1ffea8740220c60ffb4a3a01106307ffab1500883183ffd48a804418c1ffea0540220c60ffd4c2a01106307ffa61500883183ffd28a804418c1ffe90540220c60fff561a0 else 0xfeb55058831827fe5aa82c418c19ffa9341620c60dffd49a0b1063077fea4d058831833fe52682c418c13ffad441620c60bffd6a20b1063057feb4905883182fff5a482c418c19ffa9241620c60effd4920b1063067fca4905883182f7f59882c418c17efac841620c60bfed6120b106305ffeb0905883182ffd58082c418c17ffac041620c609ffd6a9cb106305ffeb54e5883182fff5a672c418c19ffa9339620c60effd499cb106306ffea44e5883183bff4a272c418c1bffa8d39620c60effd269cb106304ffeb54c5883182fff5aa62c418c13ff2d531620c60bffd6998b1063057fcb4cc58831833ff52662c418c1dffa9331620c60bffd6898b106306ffea44c5883183bff4a262c418c17ffacf31620c60dffd4798b106307efe834c5883183f7f39a62c418c1bffa8b31620c60effd2598b1063057fcb4d448831833ff526a24418c1bffa8d51220c60effd26a89106306ffea2d44883183bff496a24418c15ffad549220c60cffd46a491063077fea3524883183bff39a924418c19ffa8b49220c60effd45a491063077fe82d24883183bfe416924418c1dff9cb49220c60effcc5a491063067fea4d24883183bff526924418c1bffa8d49220c60effd26a49106306ffea2d24883183bff496924418c19efa9249220c60df7d492491063077bea4924883183bde524924418c1befa8c49220c60ff7d462491063077be93124883183fdf498924418c1fef9cc49220c60df7d45249106307fbea2924883183bdf494924418c1fefa4a49220c60ef7925249106307fbe82924883183fde414924418c1fef9ca49220c60ff7cc52491063067fea4cc48831837ff522624418c1dffa5131220c60dffd479891063077fe93cc48831837ff516624418c1dffa4b31220c60affd699491063057fcb4ca48831833ff526524418c1dffa9329220c60dffd489491063077fe944a48831837ff51e524418c1bffa8d29220c60effd26949106306ffea2ca4883183bbf496524418c1dffa4b29220c60cff96aa431063077fcb45218831833ff52290c418c19ffa8f48620c60effd07a431063077fcb2d218831833ff51690c418c1dffa0b48620c60eff905a431063077fe72d21883183bde59290c418c1dffa0948620c60effce4a431063077fe525218831833ff52690c418c1bffa9148620c60effd28a431063077fc945218831837ff51e90c418c1dffa4f48620c60dffd45a431063077fe92d21883183bfe49690c418c1dffa4948620c60ef7924a431063077fe91521883182bff5a680c418c17ffad340620c60dffd49a03106306ffea4501883183bff4a280c418c1bffa8f40620c60effd27a03106306ffea2d01883183bff49280c418c1fef24940620c60efed499c3106307ff6a4ce1883183ffb52270c418c1dfda5138620c60ffed289c3106)) else (if i < 6 then (if i < 5 then 0x480903183fdd39a404818c1fee20b20240c60ff74e5901206307fba62c80903183fcd28e404818c1feea0520240c60ff7102901206307fba71480903183fdd30a404818c1fee94520240c60ff70a2901206307fba80c80903183fdd386404818c1fee94320240c60ff2461901206307f9a30c809031837fc5aa204818c17fead110240c60eff527881206307ffa83c40903183ffd41a204818c1ffe9cd10240c60fff4e5881206307ffa62c409031837ed50e204818c1ff694710240c60ffd4a28812063077f290c40903183bfd486204818c1ffea0310240c60ffa461881206307fda30c409031833ff59aa4c418c19ffacb52620c60cff965a931063067feb25498831833de592a4c418c1bef2c952620c60eff965a931063077bcb25498831823ff594a4c418c19ffa9252620c60bffd652931063067fea4d468831837ff526a34418c19ffa8f49a20c609ffd6aa4d106305ffeb55268831827fe5aa934418c19ffa9349a20c60effd49a4d106306ffea3d26883183bff49e934418c1fef2c949a20c609ffd6a9cd106305ffeb4ce68831833ff526734418c1bffa9339a20c60cffd69a8b106306ffeb4d458831833fe5a6a2c418c1bff2d351620c60dffd68a8b106306ffcb45458831837ff59ea2c418c1b7f2cf51620c60dffd27a8b106306ffeb35458831833ff49aa2c418c1bffa4d51620c60dffce6a8b106306ffeb25458831837ff58ea2c418c1bffac151620c60dff160a8b1063057fcb4d458831833ff526a2c418c1bffa9351620c60dff949a8b106306ffea4545883183efe59ea2c418c1bffa8f51620c60dffd46a8b1063077fe93545883183ffc582a2c418c15ffad251620c60bffd6928b1063067fea4945883182fff5a0a2c418c1bffa9051620c60bfbd6328b1063047feb5525883182bff5aa92c418c19ffad549620c60effd6aa4b1063067fcb5525883183bfe5aa92c418c1dffad149620c60eff968a4b1063067fea4525883183bff52292c418c1dff29149620c60effd67a4b1063067fea3d25883183bff51e92c418c1dffacd49620c60cffd46a4b1063077fea3525883183bff39a92c418c19ffa8b49620c60effd45a4b1063077feb2525883183bde59292c418c1dffac549620c60effd61a4b106304ffeb5525883182fff5aa92c418c13ff2d549620c60cffd49a4b1063077fea4d25883183bfe52692c418c1bffa9149620c60effd28a4b106306ffea3d25883183bff49e92c418c1bffa8d49620c60effd26a4b106306ffea2d25883183fde59292c418c13ffad449620c60bffd6a24b1063067fea4925883183bff52492c418c17ffad049620c60dffd4824b1063077fe94125883182fff59892c418c1bffa8c49620c60effd2624b106305ffeb1125883182ffb58492c418c17ffac249620c609ffd6aa0b106306f else 0x3183bff494814818c1bf7a8640a40c60ffbca3205206305ffeb0902903182ffd580814818c15ffad338a40c60cffd499c52063067fca4ce2903182fff5a2714818c1dffa5138a40c60effd269c52063077fe92ce29031837ef50e714818c1ff794738a40c60cffd49985206305ffeb44c2903183bff4a2614818c17ffacf30a40c60effd27985206307efe734c2903183bff496614818c1fbf98b30a40c60dfbd43985206307fde51cc2903183ff740a614818c15ffad328a40c60cff949945206305ffeb3ca2903183efe59e514818c17ffacd28a40c60effd269452063077fe92ca2903183fbf396514818c1bf7a8728a40c60febca3945206307fde51ca2903183ff740a514818c1ffb9c528a40c60affd691452063067fea48a29031833fe524514818c17ffad028a40c60bdfd66145206305ffeb30a2903182fef58c514818c1bf7a8628a40c60bff5601452063077f6b4521903183bfa5a290c818c1dfdacf48640c60efed07a432063077f6b3521903183bfb41a90c818c1dfd9cd48640c60efed65a432063077f4b2d21903183bfa41690c818c1dfd9cb48640c60efecc5a432063077f6b1521903183bfa58a90c818c1dfda0548640c60efe902a432063077f671521903183bfb30a90c818c1dfd14548640c60effd07a432063077fe72d21903183bff40a90c818c15ffad340640c60cffd49a032063077fe94501903183bff49e80c818c1bf7a8740640c60ffbca3a03206307bfe81501903183bfb48680c818c15ffad338640c60cffd499c3206305ffeb44e1903183eff41e70c818c1bf7a8738640c60ffbca39c3206307dfe714e1903183bfb48670c818c1ffda0338640c60affd699432063067fea4ca1903182fff59e50c818c1bf7a8728640c60fefca29432063077f690ca1903183ffb40650c818c1ffd9c328640c60ffad688c3206307fd4b4461903183feb59e30c818c1ff5a0f18640c60ffad668c32063077d693461903183feb41a30c818c1ff59cd18640c60ffad658c3206307fd4b2c61903183fea41630c818c1ff59cb18640c60ffacc58c3206307fd6b1461903183fea58a30c818c1df5a4518640c60ffad028c3206307fd481461903183feb38a30c818c1ff598518640c60ffaca28c3206307fd451461903183fef41e30c818c17f7acb18640c60ffbce58c32063077de91461903183fef40a30c818c1ff794518640c60ffad018c3206307fd670c61903183feb28630c818c1bfe2d540240c60cff149a01206307ffa83d00903183ffd39a804818c1dfea4b40240c60fff4e5a01206307ffa62d009031837ed50e804818c1ff694740240c60fff502a01206307ffa71500903183ffd30a804818c1ffe94540240c60f7f501a01206307ffa80d00903183fe9186804818c1ff68c340240c60ff7507901206307fba83) else (if i < 7 then 0x3ffd40e204a18c1ffe9c710250c60fff4c3881286307fda51c40943183ffd28e204a18c1ff690710250c60ffd542881286307ffaa1440943183ffd40a204a18c1ffe98510250c60fed4a2881286307f7a51440943183ff528a204a18c1ffe94510250c60fff4628812863077fa90c40943183ff9406204a18c1ffc9c310250c60ffb461881286307ffa30c409431827fe5aa204a18c15ffad310250c60cffd49881286306fdea1c409431837ff50e204a18c1fdb94510250c60fefca2881286307ff680c409431837fd502204a18c1dfda9308250c60bfed68841286307ff6a4420943183bfb4a2104a18c17fdacf08250c60efed27841286307ff683c20943183bfb49a104a18c1ffda0d08250c60ffece68412863077f692c20943183fbb316104a18c1ff5a8708250c60ffed43841286307ff681c20943183ffb38e104a18c1ffd98708250c60ffaca3841286307ff651c20943183ffb50a104a18c1dfda4508250c60ffed02841286307ff481420943183ffb38a104a18c1ffd98508250c60ffec62841286307ff280420943183ff9302104a18c1ffc88108250c60cffd49841286306fdea1c209431837ff50e104a18c1dfda4308250c60ffed01841286307fd630c20943183ffb186104a18c11ffad052640c608ffd652932063047feb11499031833fe5aa944818c19ff2d549e40c60affd69a0f2063067fea4d079031833fe52683c818c1dffa5141e40c60cffd49a0d2063077fe93d069031833ff526734818c17ffad139a40c60effd289cd206307dfe83ce69031833fe5aa92c818c1dffa0f49640c60effd06a4b2063077fe73525903182bff5a482c818c19ffa9241640c60cff94920b206305dfeb3905903182f7f59882c818c17f7ac641640c60bfdd6220b206305ffeb1105903182ffb58482c818c17feac041640c60affd699cb2063067fea4ce59031833fe52672c818c1dffa5139640c60fbfd079cb2063077fe934e59031833ff52662c818c1dffa5131640c60bffd6798b2063077fe93cc5903183f7f41a62c818c1fbf9cd31640c60effd2598b206306fde83d439031837ef41aa1c818c1bf79cd50e40c60dfb905a87206306fde72d439031837ef316a1c818c1bf72d528e40c60ffbd689472063077de944a3903183fef59e51c818c1df7a4f28e40c60ffbd07947206307fdeb34a3903183fef41a51c818c1ff79cd28e40c60ffbcc5947206307fdeb14a3903183fef58651c818c19ff2d548a40c60effd07a452063077fe83522903183bff39a914818c1dff9cb48a40c60effcc5a452063057feb4d029031833ff526814818c19ff29340a40c60effd28a052063077fe93d02903183dff41e814818c1dffa4b40a40c60dfbd43a05206307fde51d02903182bff5a4814818c19ffa9240a40c60cff949205206305ffeb29029 else (if i < 8 then 0x31670ca18c1ffda8938650c60efed249c3286307fb4924e1943183ffb31270ca18c1ff5a8738650c60ffed439c3286307ff681ce1943183ffb30e70ca18c1ff590738650c60ffed429c32863077f6914e1943183ffb40a70ca18c1f7d9c538650c60ffecc29c3286307ff6314e19431833ff52670ca18c17ffad138650c60fbfd079c3286306fdea1ce19431837ff50e70ca18c1ff790738650c60fbfce29c32863077f690ce1943183ffb40670ca18c13f7ad518650c60dfbd498c3286307fdcb4461943183fee4a230ca18c1bf7a8f18650c60ffbd078c3286305fdeb2c61943183fce49230ca18c1ff79c918650c60efbd228c3286307f5e51461943183feb40630ca18c1ff59c318650c60cffd498c3286305ffeb4461943183bff4a230ca18c17ffacf18650c60dffd478c32863077fe93c61943183bff49630ca18c1bf7a8718650c60ffbd038c3286307fde71c61943183fef28e30ca18c1dffa4518650c60fefca28c3286307fde31461943183ffb40630ca18c1ffd9c318650c608ffd69a812863067fe935409431837ff39aa04a18c13ffac750250c60dffcc3a812863067fe915409431837ff40aa04a18c1bff20550250c60dffce2a81286306ffe615409431837ff18aa04a18c19ffa4350250c60dfbc61a81286306ffe30d40943182bff5a6a04a18c19ffa9350250c60dfbd43a81286306ffea1d409431837ff50aa04a18c1ffda0350250c60dff549281286306ffaa3140943183ffd398a04a18c17eeac850250c60dfb543281286306ffaa1940943183fed50ca04a18c1ffea8650250c60fff4c3281286305feab1140943182ffd588a04a18c1bfea8450250c60fff542281286306ff8a1140943183ffd408a04a18c1ffe20450250c60fff4e2281286307ffa61140943183ffd188a04a18c1ffca0250250c60fff501281286307ff270940943183fed184a04a18c1ffe8c250250c609ffd6a9812863067fea4cc094318377f51a604a18c1f9f98b30250c60dfbd43981286306ffea1cc0943183f7f30e604a18c1fdf94530250c60dff549901286306ffaa3480943183ffd39a404a18c1feea8920250c60dfb543901286307fdaa1c80943183ffd50a404a18c1ffea0520250c60fff102901286307ffa71480943183ffd30a404a18c1ffca0320250c60fff501901286307ff270c80943183fed186404a18c1bfead510250c609ff16a881286305ff8b54409431837fc5aa204a18c1bfea9310250c60bff568881286307ff8b4440943183ffd522204a18c1ffe25110250c60dff547881286307ffa83c409431837fd51a204a18c1ffea0d10250c60fff4e6881286307f7ab2c40943183fbd316204a18c1fee24910250c60fff4e4881286307ffa624409431837ed50e204a18c1bfea8710250c60ffb543881286307ffaa1c4094318 else 0x14a18c1ffeac140a50c609ffd6a205286305ffeb5102943182bff5a4814a18c19ffa9240a50c60cff9492052863077fe92102943183fde490814a18c17ffac640a50c60dfbd43205286307fde41902943182ffb584814a18c17ffac240a50c60bff560205286305ffeb54e29431833ff526714a18c19ff29338a50c60effd289c5286306ffea34e2943183bff49a714a18c1dffa4938a50c60ff79249c5286306fdea1ce2943183eff38e714a18c1ff790738a50c60bffd6a985286304ffcb54c29431833ff526614a18c19ff29330a50c60bffd689852863077fe944c2943182fff59e614a18c1bffa8f30a50c60ddfd46985286307efea34c2943183f7f39a614a18c1dffa4930a50c60ff7924985286306fdea1cc2943183f7f30e614a18c1ff790730a50c60effd22985286305ffeb54629431833ff526314a18c1dffa9318a50c60eff9498c52863077fe94462943182fff59e314a18c1bffa8f18a50c60bffd668c5286306ffea3462943183bff49a314a18c1bf7a8718a50c60ffbd438c5286307fde71c62943183bff48a314a18c19ff2d548650c60eff968a432863067fea3d21943183bff41e90ca18c1def2c948650c60effce4a432863067fea1d21943183bff40e90ca18c1dff9c748650c60effd02a432863077fe315219431833ff52690ca18c1dff25148650c60ef7924a43286306fdea1d21943183ffa5aa80ca18c1dfdad340650c60ffed69a03286307ff4b4d01943183bfb52680ca18c1ffda9340650c60efe949a03286307ff4a4d01943183bfb4a280ca18c1ffda5140650c60ffed67a03286307ff6a3d01943183bfb49e80ca18c1ffda4f40650c60ffed07a03286307ff6b3501943183f7a59a80ca18c1ffda8d40650c60ffed26a03286307bf683501943183ffb39a80ca18c1ffdacb40650c60ffed25a03286307ff6b2501943183ffb51280ca18c1dfda4940650c60ffed24a03286307fb492501943183ffb39280ca18c1ffd98940650c60ffed63a03286306fd6a1d01943183feb50e80ca18c1ffda8740650c60ffed03a03286307ff671d01943183feb20e80ca18c1ffdac540650c60ffe962a03286307ff6a1501943183ffa50a80ca18c1ffda4540650c60ffe922a03286307bf681501943183ffb38a80ca18c1fdd94540650c60ffed60a032863057feb4d019431837ff52680ca18c19ff29340650c60effd28a03286306ffea3d01943183bff49e80ca18c1dffa4940650c60ff7924a03286306fdea1d019431837ff50e80ca18c1ff790740650c60f7fd02a03286307f7e51501943183bfb48680ca18c1ffda4340650c60efed499c3286305ff6b44e1943183ffb52270ca18c1dfda5138650c60ffe9289c3286307df683ce1943183ffb51a70ca18c1dfda4d38650c60ffed069c3286307df6734e1943183fbb)))) else (if i < 14 then (if i < 11 then (if i < 10 then 0x8c19ffa9351a50c60dffd47a8d2863047fcb55269431833ff51e934a18c13ffad549a50c609ff96aa4d2863067fea4d269431827ff5aa734a18c17ffad539a50c60cffd499cd286306ffea4ce69431833fe526734a18c15ff2d351250c60cffd49a89286306ffea3544943182bff5aa924a18c19ffa8d49250c60effce6a492863067fea4d249431833df524924a18c1befa9249250c60ef7d492492863077bca49249431837df518924a18c1defa4c49250c60ff7ce62492863067fea4cc49431837ff51e624a18c1dffa4f31250c60cfb969a87286306fdcb4d439431837ef59aa1ca18c1bf7a4d50e50c60dfbce6a87286306fdeb25439431837ef492a1ca18c1be724950e50c60dfbcc4a87286306fdeb15439431837ee58aa1ca18c1bf62c150e50c60cff969a872863067fe935439431837ff39aa1ca18c1bfe2c150e50c60efb969a87286307fdcb4d439431837ef526a1ca18c1bf729350e50c60dfbd46a87286306fdea2543943183fce492a1ca18c1ff62c150e50c60eff969a872863067fea4d439431833fe526a1ca18c1bffa8d50e50c60effd26a87286307ff8b05439431827ff5aa61ca18c17ffad530e50c60cffd499872863077fea4cc3943182fff59e61ca18c1bffa8f30e50c60effd27987286306fdea1cc3943183fef50e61ca18c1ff79c730e50c60bfbd6a907286306fdea4c839431837ef51a41ca18c1ff7a8d20e50c60ffbce69072863057fcb4d429431833ff526a14a18c1bffa9350a50c60cff949a85286306ffca4d429431837ff522a14a18c1f7f2cf50a50c60dffd47a85286306ffea3542943183bff49aa14a18c1bffa8950a50c60effd24a85286307fbc925429431837ef50ea14a18c1bffa8750a50c60ffbc83a85286307ff8b0542943182bff5a4a14a18c19ffa9250a50c60bffd68285286306ffea4142943182f7f598a14a18c17efac850a50c60bfbd63285286305ffeb19429431837ef50ca14a18c17feac050a50c60affd6aa452863067feb55229431823fe5aa914a18c19ff2d548a50c60eff968a452863077fea45229431833ff51e914a18c19ffa8d48a50c60effce6a452863077bcb2522943183bff392914a18c1dff98948a50c60cffd43a452863077fea1d22943183bff38e914a18c1dff98748a50c60effd42a45286304ffcb55229431833ff526914a18c1def24948a50c60dfbd43a45286304ffeb5122943182fff5a8914a18c19ffa9248a50c60bffd682452863077fe94122943182fff598914a18c1bffa8c48a50c60effd26245286305f7eb2922943182fff594914a18c1def24848a50c60dfbd43245286305ff6b0922943182fff584914a18c1bffad540a50c609ff96aa052863067fea4d02943183bff526814a18c19ff29340a50c60eff949a052863077fe92502943183fde4928 else 0xefac828a60c60bfbd63145306305ffeb18a2983183fef20c514c18c17feac028a60c60cffd498c53063077fe944629831837ff51e314c18c1dffa4f18a60c60bffd658c53063077fe92c62983183fef38e314c18c1ff794718a60c60fdfcc28c53063077f6b4d01983183ffb5a680cc18c1ffdacf40660c60efed27a03306307ff693d01983183ffb59680cc18c1ffda4b40660c60ffe925a03306307ff672d01983183ffb59280cc18c1ffda4940660c60ff6924a03306307ff672501983183ffb58e80cc18c1ffd9c740660c60ffac83a03306307ff6b1501983183ffb48a80cc18c1ffd24540660c60ffeca2a03306307ff451501983183ffb58280cc18c19ffa5150260c60cffd27a81306306ffe83d409831833ff496a04c18c1bffa0750260c60dffce3a81306306fde51d409831837ff28ea04c18c19ffa4550260c60dffce2a81306306ffe315409831837fd5aa804c18c1bfea9340260c60dff547a013063077fa92d00983183fdc492804c18c1ffe9c940260c60dff543a01306307ffa71d00983183fed28e804c18c1ffe94740260c60ffb483a01306307ff8b1500983183ffc48a804c18c1ffe9c540260c60fdf4c2a01306307ffa31500983183df9406804c18c1bffa8f40260c60dffd43a01306307efe61500983183dfb406804c18c1bfea8140260c609ffd6a9c13063067fea4ce09831837ff522704c18c1bffa8738260c60fbfce39c1306307efe614e0983183ffb406704c18c1dbfa5130260c60edfd27981306307efe83cc0983183b7f496604c18c1bbfa8730260c60fdfd03981306307efe71cc0983183f6f28e604c18c1fbf94730260c60edfd22981306307efe714c0983183f7f28a604c18c1fbf8c530260c60fdf500981306307efa704c0983182bff5a6504c18c19ffa9328260c60dffd47941306306ffea1ca0983183f7f30a504c18c1bfea9320260c60dff548901306306ffaa3c80983183ffd41e404c18c1ffe9cb20260c60ffb4a3901306307ffa71480983183f7d30a404c18c1ffe94520260c60ffe501901306306ffab54409831837fd526204c18c1bfea8f10260c60eff527881306307ffa83c40983183f7d59a204c18c1ffe9cb10260c60ff7124881306307ffa724409831837fd50e204c18c1ffea0710260c60fff4e3881306307fda51c40983183ffd28e204c18c1ff690710260c60fdf4c2881306307fea51440983182bff5a6204c18c19ffa9310260c60dffd47881306305efeb34409831837ff50e204c18c1fbf98510260c60dff540881306307efa604409831833ff59aa4ca18c19ffac952650c60cf7964a932863067feb15499431833fe58aa4ca18c1bef2c952650c60ef7964a932863047feb1149943182bff590a4ca18c15ffac452650c60cffd49293286305ffeb11499431837fc582a34a1) else (if i < 12 then 0x149e60c609ffd6aa0f3063057feb4d079831836ff51e83cc18c19ffad549660c60cffd47a4b3063077fe83d25983183bde59292cc18c1dff2c549660c60cffd49a4b306306ffea3d259831827ff5a892cc18c19ffa9249660c60bffd6824b306305ffeb11259831833ff52672cc18c19ffa9149260c60cffd47a493063077fe83d24983183bff396924c18c19ffa9349260c60dffd48a49306306ffea3d249831833df524924c18c1befa9249260c60df7d482493063077be941249831837df51c924c18c1defa4e49260c60ff7d072493063077be92924983183bde494924c18c1fef9ca49260c60affd699c93063067fea4ce49831837ff522724c18c1dffa5139260c60ebfd279c93063077fe92ce49831833ff4a2a1cc18c19ffa4f50e60c60cffd25a87306306ffea3d03983183bff49e81cc18c1dffa4b40e60c60dfbd43a07306304ffeb54e39831833ff52671cc18c17ffad138e60c60effd289c7306307dfe83ce3983183bff49671cc18c1bf7a8738e60c60dfbd6a947306307fdcb4ca39831837ef52651cc18c1ff7ad128e60c60efbd28947306307fdeb3ca39831837ef51e51cc18c1df7a4f28e60c60ffbd07947306307fdeb24a3983183fce49251cc18c1ff79c928e60c60ffbd62947306307fdcb14a39831833ff52651cc18c1dffa5128e60c60bffd67947306306ffea3ca3983183bff49e51cc18c1dffa4b28e60c60dfbd43947306307fde81ca3983183fef38e51cc18c1bf7a9320e60c60dfbd47907306307fde83c83983183fef39641cc18c19ffad548a60c60cffd47a453063077fe83d22983183bff396914c18c1def2c948a60c60effce4a453063067fea1d22983183bff40e914c18c1dff9c748a60c60effca3a453063067fea4d229831837ff522914c18c1bffa8f48a60c60ef7924a45306304ffeb51229831833ff524914c18c17ffad048a60c60dffd482453063077fe94122983182f7f598914c18c17ffaca48a60c60effd252453063077bc92122983183fef28c914c18c19ffa9338a60c60effd259c53063077fe924e2983183fde492714c18c1dbfa5130a60c60fdfd28985306306efea3cc2983183b7f49e614c18c1fbfa4f30a60c60fdfd079853063076fe92cc2983183f7f496614c18c1fbf24b30a60c60fdfce59853063076fe924c2983183f7f492614c18c1faf24930a60c60fdfce4985306306efea1cc2983183f7f40e614c18c1fbf9c730a60c60fdbca3985306307efe51cc2983183f6f20e614c18c1dbfa4530a60c60fdfd229853063057feb4ca2983182bfe5a6514c18c1bffa9328a60c60dffd489453063077fe924a2983183fde492514c18c1fd794728a60c60ffbca3945306304ffeb50a2983182bff5a4514c18c19ffa9228a60c60bffd68145306306ffea40a2983182f7f598514c18c17 else (if i < 13 then 0x70c60ffb9288c3386307f9c924619c3183bef48a30ce18c1ff5a0318670c60cffd498c3386305ffeb44619c3183bff4a230ce18c1dffa4b18670c60ffbd038c3386307fde51c619c3183fef18a30ce18c1ffda0318670c60cff969a81386306ffcb45409c31833ff4a2a04e18c19ffa4d50270c60cffd25a81386304ffeb1d409c31837ff40ea04e18c1bff98750270c60dfbca3a81386306ffe51d409c31833ff48aa04e18c1bff98550270c60dffc62a813863067fe90d409c31837ff406a04e18c1bf78c350270c60dffc61a81386306ffab55009c31837fc5aa804e18c1bfea9340270c60dff548a01386307ffaa45009c3183efd59e804e18c1f7ea0f40270c60fff546a01386307dfa735009c3183bfd496804e18c1fee24940270c60fff4c4a01386306ffaa1d009c3183ffd50e804e18c1ffea0740270c60fff4c3a01386307fda51d009c3183ffd28e804e18c1ff690740270c60fff542a01386307ffa615009c3183ffd18a804e18c1efea0340270c60fff501a01386307fda30d009c3183ffd186804e18c13ffad540270c609ff96aa013863057feb4d009c31833ff526804e18c1bffa9140270c60fbfd07a01386307dfe735009c31837ff50e804e18c1bfea8140270c60bbfd689c13863075fe944e09c3183aff49a704e18c1d7fa4b38270c60dbfd439c1386307dfe81ce09c3183eff30e704e18c1f7794738270c60fbfca39c13863075fe914e09c3183eff30a704e18c1f7f8c538270c60ebfd219c1386307dfe80ce09c3183eef186704e18c1f7f8c338270c60fbf5009c13863067fea4cc09c3182eff59e604e18c1f7fa0f30270c60dffd43981386307efe61cc09c31837fd502604e18c1f7e9c130270c60fbfd07941386307dfe734a09c31837ff50e504e18c1f7e9c128270c60dff549901386307ffaa44809c3183efd41e404e18c1ffea8d20270c60fbf4e6901386307ffa62c809c3183fed28e404e18c1ffea8520270c60fff4c2901386307fda30c809c31837fd5aa204e18c1bfe2d510270c60dff549881386307ff8b44409c3183ffc4a2204e18c1f7eacf10270c60fbf507881386307dfa734409c3183ffd316204e18c1fee24910270c60fff4c4881386306ffaa1c409c3183ffd40e204e18c1ffe98710270c60ffb4a3881386307ffa51c409c3183fed20e204e18c1dfea4310270c60ffb461881386304ffcb54409c3183eff41e204e18c1f7f9cd10270c60dffd43881386306ffaa04409c3183efd382204e18c19ffa9308270c60dffd48841386307dfe83c209c31837ff50e104e18c1bef2c952660c60cffd6aa513063077bcb2528983183bfe58a944c18c13ffad54a260c60cffd49a513063067fe945479831837ff4a2a3cc18c19ffa9149e60c60ef7964a4f306304ffeb55279831833ff52693cc18c1bffa9 else 0xcffd49a4d386306ffea45269c3183eff41e934e18c1b7fa9139a70c60ebfd289cd386307dfe944e69c31833ff5aa92ce18c19ff2d549670c60eff968a4b3863075fe735259c3183bde59292ce18c13ff2d549670c60cffd49a4b3863077fc945259c3183eff39a92ce18c13ff2d531670c60f9fce698b3863077fea45249c3183aff41e924e18c1dffa8d49270c60ebfce6a493863077fe62d249c31833ff526924e18c1bffa9149270c60fbfd07a49386307dfe735249c31833df524924e18c1befa9249270c60ef7d49249386306fbea41249c3183fdf520924e18c1defa5049270c60ef7928249386307dbe839249c3183fdf518924e18c1defa4c49270c60fb7ce62493863077be929249c3183fdf314924e18c19ffa9331270c60dffd489893863077fe944c49c3183eff41e624e18c1dffa4b31270c60cff969a873863067fe945439c31833ff49aa1ce18c19ffa4b50e70c60dfd962a873863077fe945439c3183bff49aa1ce18c19ffa9340e70c60effd28a07386307dfe735039c3183bff49681ce18c19ffa9330e70c60effd289873863077fe92cc39c31837ef50e61ce18c1ff7a8730e70c60ffbd03987386306fdeb54a39c31837ee5aa51ce18c1bf7a9328e70c60ffbd68947386307fdcb44a39c3183bef4a251ce18c1ff725128e70c60ffbd66947386307dde734a39c3183fef59251ce18c1fe724928e70c60ffbcc4947386307fdeb14a39c3183fef58651ce18c13ff2d528e70c60effd28947386305ffeb34a39c3183bff49a51ce18c1f7f9cd28e70c60dfbd43947386307fde81ca39c3183fef30e51ce18c1bf7a9320e70c60ffbd48907386307fdea34839c3183eef39a41ce18c1ff7a8b20e70c60ffbcc59073863077fe945429c3183bff492a14e18c1fef24950a70c60ffbc83a853863067feb55229c31833fe5aa914e18c1dff2d148a70c60ebfd07a453863075fe735229c3183bff316914e18c1def2c948a70c60effcc4a453863067fea1d229c3183bff40e914e18c1dff98748a70c60effca3a45386304ffcb55229c31833ff526914e18c1bffa9148a70c60eff928a45386307dfe83d229c3183eff39a914e18c1def24948a70c609ff96a985386307cfe734c29c3183bff496614e18c1fbf98b30a70c60effd24985386307fbc924c29c3183bff4a2314e18c1dffa4d18a70c60fbfce68c53863077fe92c629c31837ef50e314e18c1ff794718a70c60eff968a433863067fea45219c3183aff41e90ce18c1def2c948670c60cffd43a433863077fe81d219c3183bff28e90ce18c1dff8c548670c60dffd48a433863077fc945219c3183eff41e90ce18c1def24948670c60affd69a03386306ffea4d019c3183bff4a280ce18c1f7fa0f40670c60ff7924a03386306ffea1d019c31837ef52630ce18c1ff72d1186))) else (if i < 16 then (if i < 15 then 0xd49249406307fbea4924a03183bde524925018c1fefa8e49280c60ef7d27249406307fbe93924a03183fdf518925018c1faf28c49280c60ef7d26249406307fbe93124a031833ff526725018c1dffa9339280c60fdf9469c94063067fea4cc4a03182fff5aa915018c13ff2d548a80c60cffd49a454063077fea4d22a03183bfe526915018c1dffa4f48a80c60fdf946a454063077fe93522a03183bff496915018c1fef2c948a80c60effd24a454063077bc92522a03183fde492915018c1ffd2c348a80c609ffd6a245406305ffeb5122a031833ff524915018c16ffad048a80c60bffd68245406307efca3122a03182fff594915018c1dffa4a48a80c60ef7924245406305ffeb0922a03183bff526515018c19ff29328a80c60ff79249454063057feb48a2a03182fff5a4515018c19ffa9228a80c60cff949145406305fbeb20a2a03183fde490515018c17feac028a80c60bffd601454063047feb4d40a031833fe5a6a05018c19ffa5150280c60ddf966a81406306ffe73540a031837fe58aa05018c19ffa4350280c60affd69a814063067fea4d40a031837ff51ea05018c1fbf2cd50280c60dffd46a81406306efca3540a03183f7e51aa05018c1bffa8b50280c60bffd63a81406306ffea1d40a031837ff50aa05018c1bff28550280c60f7f169a01406307bfaa4d00a03183dfc526805018c1efeacf40280c60f7f527a01406307bfab2d00a03183dfc596805018c1efea4b40280c60f7f125a01406307bfab2500a03183dfd512805018c1efea4940280c60f77124a01406307bfa72500a03183dfd312805018c1efeac540280c60f7f162a01406307bfa91500a03183dfc48a805018c1efe14540280c60f7f521a01406307bd230d00a031837fd526805018c1efea5140280c60fff527a01406307ffa92d00a03183ffd492805018c1fee24940280c60fff4e4a01406306ffaa1d00a03183ffc58a805018c1ffea4540280c60fff122a01406307ffa90d00a03183fe9186805018c1ff68c340280c60ffe461a014063067fea4d00a03183bff486805018c1ff58c340280c60ffec61a01406306ffaa0500a031833ff526105018c1bffa8708280c60f7f500841406307ffa80420a031837de592a4ce18c1bfb2c552670c608ffd682933863047feb29499c31833ff524a4ce18c17ffad052670c60cff969a91386306ffcb4d489c318377e59aa44e18c15ff2d352270c60dff949a913863057feb49489c3182fff58ca44e18c17feac052270c60cffd6aa513863067fcb55289c3183bff522944e18c1def2c94a270c609ffd6aa51386304ffcb55289c31833ff526944e18c13ffad44a270c60cffd49251386305dfeb39289c3182fff594944e18c17ffac44a270c60bffd61251386307dfca4d079c3183bff4a2a34e18c13ff2d549a70c6 else 0x285e60178085dbe175e85cb4171585bc416e005b2216b785a9a168f05990164c858d416240583215fb8577615c6056ee15aa8564c157b855aa1546054a01510853b014ad8520a1451050b2140804f5a13c584e1c135c04c7612f904ba012bd04a141267048f012110474a11a104626115e844ce10f50434210b284252107004114102d8400a0fd783ee60fa883e440f8003d3a0f2a03c4a0ee103a8a0e6a838960dfa8373e0d9e035e60d5b834f60d1f833ec0cdd032e20c9a831be0c518309a0c0882f900bcc82ed40b9082d960b3a82c720b0502b9c0acf82ae00a93829d60a51028cc0a150278e09b8826840976024de0920023ee08dd822ca0887821a6084b820d0081c81ffa07cd01ebc079101de6075b81d10072c81c5406fd81b6406bb01a740685819b806360184606008177005b101632054e0148c050b813d004dc813140493811d60457810e6041b80ff603df80f0603aa00e30036780d0c032500c3602ef80b2c02ad00a560277809660242008c40213007ee01ea8073201a800628016c0053801300044800ed8033e00b8002820089001ac005a0010a002b00001bef2c952673460cffd49a4939a3067bea49249cd1837df524924e68c19ffad548673460ef7964a4339a3067fea4d219cd183bff4a290ce68c1dffa4b48673460ff7964a4339a3077fe925219cd183bde49290ce68c1fef24948673460effd22a4339a3067fe915409cd1833ff486a04e68c1bfea9320273460fff52290139a307ffa90c809cd1837fd5aa204e68c1bfea9310273460fff52888139a307ffa92c409cd183ffd492204e68c1fee24910273460dff54388139a307fda51c409cd183fed20e204e68c1dfea4310273460fff52188139a307fda30c409cd183bff4a2204e68c1dffa4b10273460dffd4388139a307fde51c409cd183bff486204e68c1ff78c310273460dff54088139a307ffa804409cd183bff4a2104e68c1dffa4b08273460dffd4384139a307fde51c209cd183bff48a104e68c1ffea0108273460fff44084139a3057feb48a29891833ff524514c48c17bfacc28a62460edfd26145312305ffeb08a2989182ffd580514c48c1dfea4b40262460ffb461a013123077fa93c40989183fed28e204c48c1dfea4310262460ffb4618813123067feb3d49a031833ff592a4d018c19ef2c952680c60cffd62a934063067fcb1549a03183b7e59aa4d018c1def2c952680c60ff7964a934063047feb1149a031833ff524a4d018c17fface52680c60bffd62293406305ffeb5527a031827fe5aa93d018c19ffa9349e80c60effd49a4f4063077fca4d27a03183fde59293d018c15ff2d351280c60cffd49a89406306ffea3d44a031833ff526925018c1dffa9349280c60effd27a494063077fe93524a031833df524925018c1befa9249280c60ef7) else (if i < 17 then 0xfc51349440c50eb9431c50a29422c507a140ee501d93fe44fdb13f0e4f8b93d1a4f1b93bf64ee613aec4eb713a984e8e938f24e25138364df6136de4da69363c4d43934ca4d0e133a64cd2132ea4c89131924c46930a24c1112fcc4bd512ef64bac92e544b7092d644b3492c744aff12b844ac312a464a7a1293c4a3e1289a4a0f127c449d3126d44997125fe495b124f448de122e6487b120a4480491f9a47bb91dc0475891c3446ef11b4446b311a544656918c845ed1172245839157c45271142444e4912cc449b911c24459110d2441690f7a43ba10e3c436410ce4430790ba642c510a82427c1095e42331085441f09071641a79058a4137904664108903aa40d9903084090901fe40681008c400b8ffb63fd60fefa3fa70fe243f780fd823f490fcac3f0d0fb203eb70fa983e950f98e3e4c0f8503dfc8f7ae3da68f6223d508f4e43d148f40e3ce58f3383cb68f2483c740f1583c380f0683bfc0ef783bb30edd23b500ece23b210ec0c3aeb8eb503ab60ea603a738e9563a3e0e88039f50e72839a58e61e395c8e4e0391a0e3f038e48e31a38af0e24438730e15438308e04a37f48df5a37b88de5037760dd7a37470dca437048db8036c20da5c36790d95236368d82e35ed8d73e35b18d66835758d4f6352c8d45434ea0d2c8349a8d1d834518d06633fb8cf2833b90ce5233698cd6233340cc8c32fe8cbd032dc8cb2e32a08ca0a325e0c8e632150c7f631df8c6ec319d0c61631678c52631320c43630c20c25c30790c15230368c0622ffa8bf8c2fbe8be682f758bd5e2f400bc882efd8bb7e2ec80bac22e8c0b99e2e3c8b8ae2e070b7702dbe0b6662d7b8b55c2d390b46c2cf00b3622c8d0b1a22c3d8b0642be78af0c2ba50ade82b558acc42b130abee2add8aae42a9b0a9f42a588a8ea2a298a82e29ed8a77229be8a6b629960a614296d8a572293e8a49c29028a3e028e08a30a28ab0a282287c0a192284d0a054280a89fcc27db89f10279f89e54277709d7e274189c8e26e509b5026c989a942680899a426580990226290987a260709722259d89618256e895422539094862503893ca24c7892a624850919c2449090c6241a0900a23e488f1a238e88dc2234c08cec232a08c4a22e788b0c229e889e8226288912222d0883c21ea8874c21bb8865c2179085862143884b02107883a620cb882b6209c881c6205a080d6200407f7e1fc187e8e1f7f07d6a1f3607c601f0087b701ebe07a4c1e6e879281e1f0781e1de98772e1dad8763e1d648751a1d288742a1cec873541cbd872981c8e871c21c52870ec1c1d070161bee06f0c1ba506d801b3b86c901b0606ba01aca06ab01a94869da1a58868ea1a16067fa19da066f019a48661a19758654419330646e18ea0631618a78625a18788611c182f8604617f385fa417d185f0217a else (if i < 18 then 0xc6a22548870a21308834a204087eba1f5087b621e60877a21d708744a1cb4870f21bde86e021b3c86b121a66867521990864ca185285dca16c6859a2163e857ea151a85082134084bf21236847621194844da10d884252101c83f620f9483d420f0c839820dce8355a0caa831320bd482dda0afe82a1a0a288272a09388209207c681da206d68197a06008168a04f6811fa043a80ea20330809aa01f28051a00ce80021ffc47fe01ff087faa9fe327f619fd427f391fc6c7efd1fb2e7ea71fa3e7e441f87e7e0e9f7f67de61f7207db09f64a7d7b1f58e7d459f49e7d031f3ae7cad1f2087c641f1327c2e9f05c7bd21eed07ba31ee2e7b539ec887b041ebb27ad51eadc7a9f9ea3a7a709e94a7a279e82679e51e6e8798f1e5de79599e508792a9e41878e81e32878b91e28678971e23278751e1aa784c9e0a0780a1dfca77db1df0e77ac1de3877701dd1477271dc3e76f81db6876bc1da9276939d9a276309d81675d41d6a4757e1d566750e1d3c074d21d2ea74961d1fa74609d13e742b1d03473f59cf5e73b99ce54736a1cd4a733b1cc7473059cbb872d69cae2728d9c9a472379c866720f1c7c471cc9c6ba71971c5e471681c55c713f9c48671109c3e470ce1c2c070921c1d0705c9c114702d9c03e6ff81bf9c6fcf9bee06fa09be0a6f719bd006f1b9bbf66ee61bb206eaa1ba166e541b8566df79b7806dc89b6c46d7f9b5a06d4a1b4966cfa9b3586cb81b2346c6f1b12a6c2c9b0206be39aec86b9a9adf26b5e9ad026b229ac2c6ae01ab226aa41aa186a681a9426a329a8866a109a7e469e19a6f4697e9a59c694f9a4e0691a1a3f068eb1a2e668819a174684c1a0ec681d19fe267c719e8a678b19db4675599cc4671999bd466ca19a966687999a6664b998d06616197e065cd196bc6597995cc654e994c26512993b864bc99260647a1918a64449906663ee98f5c63b918e52637698d7c633a98c3e62f198b4e62c298a92628d189d66251188e66215187dc61d9186d2619d185e261611850c61251840260e29832c60b39823c6077981806042180aa600617fba5fca17eb05f8797d245f3197c4e5efc17b785eac97a3a5e77179645e3b178745dff1779e5dc3176945d87175a45d3e1749a5d0f173c45cd9972ee5c83971ca5c5b1710e5c259701e5be316f2e5b9396dd65b4a96ccc5b1b96bf65ae616b3a5aaa16a165a5a968f25a18167ce59cf166c45999965ee5964164fe59219642858f29636c58c396296588e161da5852160ea581c95fac57c695ea2577d95d98574e95cc2570595bb856a915a46567a159a4564b1589a560f157aa55cc95652557695562553a9543e54f81538254bc15278546c9513a541d1501653e794f2653a514e50536f94d60533a14bba52d714afe5281149a652451489c52091479251b31463a515d144 else 0xd82c34fb0cc6c31a30c0ac2e4b0b00c29bb09f6c259308ecc223b0830c1f4b0740c1b23066ac18330594c140b0470c0fe3039ac0c2302aac08cb01bac05db0132c03530076bfffaffa0bfb6afe7cbf87afdc0bf522fceabf162fbc6bed3afaf0bea4afa34be75af944be2caf83abdea2f74abdbb2f68ebd7f2f584bd3caf47abd00af3a4bcbe2f280bc752f142bc392f086bc10aefcabbd4aeef4bbac2ee6cbb83aedcabb5b2ed0ebb392ec6cbafd2eb96bac12eaa6ba8bae9d0ba4fae8c6ba1a2e80ab9eb2e71ab9a8ae62ab96cae53ab923ae3fcb8e7ae326b8abae250b87cae194b84dae0d8b7fe2df80b7bbade5cb77fadd38b729adbfab6cd2daa2b6912d9b2b641ad840b5d82d6e8b595ad5c4b5462d4bab4f6ad362b4adad20ab45e2d100b428ad010b3ecacf3ab396acdfcb3612ccf2b3182cbb4b2d5acac4b2932c9eeb23d2c862b2012c78cb1beac69cb18fac578b1402c488b0fdac316b0ae2c20cb0652c11cb02fac07ab0072bf8aafc4abe80af822bd90af59abd08af172bbe4aee82bb76aea5aba1eae632b914ae20ab80aade4ab700ada8ab610ad5fab506ad23ab44aacfb2b35aacabab236ac62ab12cac202b008abd72ae96ab8e2adc0ab58aaceaab0faabc6aad3aaaf0aa842a97eaa34aa85aa9deaa6e8a98f2a5c4a94caa4a0a90a2a3caa8c7aa2a6a8922a1eaa84faa05ea7f329f20a7aa29e4aa767a9d5aa738a9c6aa70329b60a6ba29a22a664298b0a61b297daa5d8a96eaa596295e0a55a294bca517a9398a4bb29274a47f2919ea4432902ca3ed28ea0a39728de4a35b28cf4a2f1a8b68a29ba89f6a25fa8920a22a28830a1ee28740a191a85cea148a84c4a0ffa8352a0b6a8248a07428172a03ea80689ffc27fac9fcd27e6e9f63a7c949ef3a7b569ea427a189e5b2790e9e12277ea9ddca76e09d93a760a9d64a754e9d35a74789d0d273d69cd1272cc9c8ea71a89c52a709e9c1026fc89bdaa6f0c9ba526e029b62a6d129b2d26c3c9aeaa6b329aaea6a429a6c269389a302682e99e72672499a4a6668997c2655e99332648898fda639898c1a628e98722616a983ca607a97d9a5eee97a425d7c973aa5c7296f825b6896c2a59f69666258b89616a57fc95daa568a957e2556695422549094ffa535294bd25262947aa518c944ba500093e224e749378a4d6a933ca4c2c92ed24b08929da49fe925b248da9205247b691cfa46c6918d245a2914aa446490ee2432690aba41ce9055a40aa900623f6c8fa9a3e488f7423d588f3ea3c688f02a3b928ecd23af08e97a39cc8e4ea388e8e05a37b88dc9a367a8d7a235708d3e234b48d0f233c48cbfa321e8c69a31148c27230248be4a2f1a8ba8a2e448b79a2d548b1d22bfc8ae122af28a9ea29e88a5c228f88a26a280889e42271889aea26428972a253889232242e88))))) else (if i < 29 then (if i < 24 then (if i < 21 then (if i < 20 then 0xbf2bef6cfbb6bee2efb60becf0fb113ebb2fad53ea74fa723e96afa2fbe87af9fa3e78af9be3e69af995be62cf94cbe4baf910be32ef8adbe20af83dbe016f7f4bdf0cf79ebddcef755bdcaaf70cbdbbaf6d73dae4f69b3d9a6f631bd800f5cebd6dcf59fbd5d2f55d3d516f5213d3d8f4d83d2e8f495bd1def459bd0d4f41dbcfe4f3db3cedaf3923cdeaf35cbccfaf3273cc24f2f1bcb68f2bc3ca44f2733c920f22a3c816f1d43c6a4f18b3c59af155bc52cf13a3c4bef1183c41cf0f63c394f0dabc30cf09ebc202f055bc0c4f00cbbf86efca3be62ef7abbd72ef3ebbc4eeeef3bb5eeeb33ba88ee913b9b2ee41bb874edff3b76aedc33b6aeed8dbb5beed583b4e8ed15bb3f8ece03b2baec7d3b17cec343b03eebf1baf68ebbc3ae78eb8d3ada2eb443ac7eeb01bab8eeab8baa36ea693a92cea33ba870ea04ba74ce9aeba628e96c3a538e9303a448e8faba372e8cbba2d0e88fba178e82cba03ae7f0b9f64e7b4b9e5ae76bb9d36e73639c46e6f3b9b56e6be39a66e6753995ce62c3986ce5fd39762e5ce396dae5923959ce5493945ee506b93bce4d1392cce49bb9210e479b9188e44ab90b2e40eb8fc2e3d938e9ee37cb8d46e326b8c22e2eab8b4ce2a838a28e25f388eae216387e0e1cd386d6e1ab38634e175b8510e12cb8454e0f73834ae0bb382a8e08c3819ee049b80c8e00db7fd8dfdeb7f02dfa937e46df6d37d08df2437c4cdeeeb7b90ded337b08deaab7a80de8f379dede60378d4de17377fedde837728ddb2b766cdd83b75b0dd54b74dadd1f3741edcf6b737cdcce372c0dc98b719cdc4fb70e0dc20b6fbcdbc436e7edb7b36d8edb45b6cb8db16b6bc8dad436ad8da8b36932da35367dad9cbb66b6d989365c6d946b643ad8e3b62fcd887361a4d83e3609ad80235faad7c635e6cd77d35d7cd73435bd6d6c435ab2d695359f6d6663593ad623b5830d5cdb56a4d577b5518d528353f4d4d8b52ead496351c6d45a350f0d417b4fe6d3ceb4ea8d385b4db8d35034cc8d31434ba4d2c4b4a9ad288b49c4d253348d4d210b47e4d1e1b4728d1a5b4638d169b44fad12734458d0f834368d0bc34278d079b416ed03db407ed001b3fc2cfd933ed2cf96b3dfccf67b3d5acf45b3cb8cf0333b94cec733a70ce7e3394cce353385ccdf933738cdb6b367ccd6db3524cd24b341acce8b332accacb323acc7733164cc4833074cbff32f9ecbd032e94cb9432da4cb3132c66caf532adacaa5b2a38ca7032914ca3ab2858c9feb2768c9c2b26acc979b2588c951324b2c9153238ec8bf3226ac86fb212cc82d31f86c7bd31e48c760b1cf0c717b1c00c6ceb1ac2c685b199ec650318aec607317a4c5cb316b4c588b15aac54cb14bac51db13fec4e831342c4a5b1252c47d311b0c44e310dac41f31038c3e330f48c3b430e58c38530 else 0x4340817790301700b70900602e086a0c1d300610d01721200c05c08fc1820c1fc1038302c10c44340720609905de0c2a20fa00b08688620a11c00b10c4434080fa00b08688630805c03005440c0b006002e0183e812d00420200c42b810e90744086a40c05c02c0072141f413282704a815c021440874290c5c10c0750602b02550c00650102b047412a8581890c7412e09502b80c23e0ac0954490c7410031d09020c2550c09c03004040c0b010310d0182580b61170304e02580b60615c01885440b609c08e483a1d40a09c14384041240c05c01f05461101280f08984381005303103002b21240c10103780c01280900400d018c1141811302d82b01007405c03b81844c07201a0318200a603440711e82b214060a03a02016c1580b40480200680c609c0102c016c0c0d4404a02401211812c0880201dc2550aa0580202b08630811302e01dc0f80303121884d2100a611390704061180f206041c1816c21c0400420501700b70811350600e40c0b805b82404a03e0301220480d18080a601c05102c0140de0300510240100c401a0298240680a601c0510240168080300310240680a601c0510200c200a0b201102881600806200d014c1240b40a02d81c01016404f03102833c066060b2802016c14408033089c1281a808033836039010031060cfe04c81407a0770874346e4d1b7546cc11b18c6bd11ac946a931a80469551a3dc689919fb467a919cc4669f198346595194dc64bf190b463b518c8c62c51899c61ef18644614d183bc605d17ffc5f8717c3c5e97178e45ddb1758c5ceb171cc5be116da45af116a4c5a35166f4595f16404588915f74573115a1456271572455511536454611500c538b14cb452b5148f4515d14394503913f044f4913b444e25135e44d35132f44c2b12ecc4aed1296c4a31126e4492712254481d11e2c471311a6c4623114a444b111014438d10d2442d11075c41791040440070fdd43f170fa143e0d0f6bc3d1d0f2fc3c2d0ee043aef0eb143a190e684390f0e12437b70dcfc36110d664353b0d10433c90ccdc32570c77c31810c42430910bec42f390ba9c2dc70b53c2c070ae3c2afd0a9ac29710a44c27e509d4c2659097ec2569092f4242b08ecc230708a3c221708614212708324201d07efc1f2d07ad41e3d076ac1d33072841c0f06ec41aeb068fc19ad0639c180705e3c16fd058dc15f3054b414e90515c1391049f411b70435c107903f340f3b03b0c0e31036e40d27032bc0c1d02efc0b4702b3c0a57027e4099b022ec07f501df406eb01a3405ad0153c04d70117c03e700e8c034500b34025500774017f0034c005b0005bffd2ffc33fe7aff873fd3cff37bfc32fee83fb0efeac3fa04fe563f8acfe003f73afda3bf5fcfd613f4f2fd253f450fd033f360fcad3f256fc77bf132fc283f05cf) else (if i < 22 then 0x42c2da077840510083f815460d035095006094234018205182880b8a030b100d28150e40a70182880c1fc431b0082a8c020a0fea00c105468020fe835085006081920778220090c41fd060a220204b42c4112a054302aa816033030a8d0041fd0740b03bc104700b807703502820e0a814a0621880cc10144a0603bc1820e041440838220503f81450643103b83fa0c0b613282107302e00843108742b825c0214408742281486828783802283180e134081c285dc1f60fa074c0c4862e12103016e24862e08603b80822e132860bb852c1f4431029818050f0e0cf02c380450e10e8502e384a008c0721a42b82580ea05802380c23e1038711e840e08288031e05801a0080fb095046806d12058704b80dc022870874305aa063006802016c86211f701840e25c1203a502851021d0a23a09941033c0b0e0970088f421d0c15c02e40c4863006029a831c2510053218a83028908e09603b80d418134081c3047c0b7004708101021d0c13201b401826811f08180c428810e89218b825c10404701845c2650e060143843a0c19e058704b80450e10e8608f8170862e10202043a180b605301b40c600d0042188a1c207120e902e3849c2010e8502e40c48621348402e40c486211f84704b01c01414408742852dc1210e21a045c2650c0cf21a043a0e008134099047d8161778602db822008e0114390c61826401921884ba1086211a8200b10c421d060600994101700b700420208f423ec0b874120511c0612a09942a8318161448301b00c600840409a047c21d0e05c02d80d9c1300420208f423ec0b8909710c6009a0c70084c81f410e8809a04b825403100c843941805b471040e2819e058704b80450e10e8681890c426805b081a8321828801910cb80c50e13409943806425413414384ba140b8134506043a1025ce01218843a10063e03f01780611812c08a0230342540b40405e8288862080cf600c81410e10e85029d0101444310400d3026008c0d07d843a1a009c0102990c61019e217e04c0f40ee10e86218a83009e07704067b02407a07708742b0480a60778309f814c0ef06004e0904d281410e850278069c0740421882b0180a001a604b03640a12e8680270048620b284029828886206053802502880909004701820e0c42ee0203bc184d2008404a02043a140a7004202502a1181300460784382260a04f218814c0ee0801ae0950282690813f09a016c86212508fd02a1c0b005302781728144348606b816c21d060cfe00b01e40a287087437025c12c07002700450ee03043843a2419e03908741833dc12c07143843a1640c16a506843812062a09d04101c28810386504280806340708b84ca180b1206056086a101d320610d01701200c287081c1816015823a030ae40180b821a04504c01940603108bc8182650e05890302b else (if i < 23 then 0x200250a9891a1680f0203170083a4c2508a11a03891a0c11a029a04b01e128126092020112100b9046112a80e80e14b07383d823b13407701c1501e0406216a02305682230a031304d01dc020e985504501c80906a10a03c1093048c4258304600a5817074078101a03a4816060ac0466817406030a0383c8222c0b890460119c0214508590c6180be41b0a8c1805941f40783218805941a4258401c00588630614b074b02c0c0894091490546101d24070220390101bc0310ad04461a812a05014b01e101d2a05700814c0390a60960383a40b80815ca04a83048d0815c02e28300d40ae0302e41b8042a241b83014a819c040468450338041d20600404e10c4812209067c0c4222a0c8802fd01cc2420984074811a81340750742d01d41d0540750341380406643183a04880f802887025043a180a681a301101c1440bc01104823450e14b05401d80a07c04b08742b0040c002a03a0381a00de03084600852c05207407e00852c0530881a204b004136053050a7852c44a0614e0a584d20d03440960082340a70a40760581100520840404682ca0c05206001980ae1280e24603bc180a8812c0102d814c1409e81a02980cc10433407e00833e1280ea0302504381280e05b8200af0278020870250438180a603d05101a026c0600f09f843a1443241530470040c1031067c38332c0740f03784a41604409b207833e12c06029a0784a41027e81a143903c19f0a236b01d03c16412905029826c46c40f06702901380303109a4200a410602283059101046c6108110284fec06053a07c2013f824a06085502846d0c053a02016c09e03305014b01e80623d011428827802025012021c21c0d20c01d02880ec0404b09f843a1380209a030014e12c0411908b01bc1204009a206814c1027e219e0082680c0053060180a1e81a0290440d0a1c81a05304b01503422c13404810026881a0530481881dc1650602c01041dc0c42e03003bc1c0808080b203089c0e407802b0410cd80819e0778440380e421d060ba906301c0720814a03b814e0c27e0cf03bc1f027802212443809021d0c05340d00f81440802bd01900484a0623080570224087a0545582500303e026846a1443443801501c0c7802060029c2501f80210b037c2407d034438029c27004136060029c2042c43c10d03e0082680c005384a03f0042160298440d026887002984018501c16402205182b0042160290302c7004c0210b02982901c05801fa050202c80da05003015818006602984a0381de08434c0102980d809e0a2360679214c200805302d82880c06201f304501d80fc01014c388d806207911e9216154076010488438101446010202f901c8620fe84051017c0b8a1106480d28170ec0770102880c1fd601055180410144153064820e10144020fe055183c0c1fc0838202e else 0x490358040c421a02982c81ac020b20278200d00a60330390305dc23307601080814c4340920920684e808411985418881814460d0298290c414404805e82017c08b60250120c41440d20600d18480c409046418a83850e0a285507052850e062848230825407602418828a1a40d6020a500aa110616020bb828a1089b20e20784fe100c40cf30781806980f60330884ca1419e05800bb021802062043c83a21c020cf8210cb01e40706046609481b80210a11b43033c0b001a604480d802046093c408f5c020cf8310c805d825203e00c2f024214c0d14388da14269c09101f006c060c608508da2180810a30804c81019e02a023103e41c11411b43833cc1f0444d11b480cc07c018524908d802f203301f00618c1e13282226b02824e070041c2833c1060406291b302a50e08385041c0c80c02ec0d83242820e0819e0c1249700410e2878630082880a623d04b01a00409a12e089c290c603520e11d028a16c0683181188441440b20e01e81880c40a203e00c06a1106360309500881440a01a015483825e0920e01e80a80c19f20e91e82881089b20e041844e100c40cf0418181180352030310a1e14407c010854830c10134249058820203150745e824813807908020c2330c831051020c0a60840420401e086810a85400813421c1138480d08e88620a284a02047d0620a28490304280c50701a50704d08620a20550708228081380510281b6808134418828814c1120600d01881240c10a0154182c90601770514201700346032188288140daa0602d84041013805b08081c81806c113830590188c10a0602c028068c11206503028a14269404085283841c0a206904028a08026006213826427e0a431404d80401e10e0898340744021160514210c403b2010a581881603a201018828a1014c01d00d020c0c40a20108184a41450801d900842c0c408431d0480c7420033089c304b80660a283079037802a0140150040096141a0505a824516209600c09007a1228500d0055812c0107d848818863007e0080a41ec0a014604c80d80280e02504381c1e4c12e0081280520bc01143821c05208c09803b00449a03d08d437027802048143843815812c11605816c21c0a02921880981580803a01c82b00c86207902d82b211812c03605816c2440a43101302f414408401226886823209609604b00507c12205a0381bc8620a20400d01880a80ee0321881881280ee0221881881003411902a0384d08620a20400d0188080a60a221a0190c6814040ba056016c0c26405b02a04a80c09410e04a04b80980f06a06502823c11a14b85a04c0b02c29605383a03a80c12210e04074b8040c0074078150100c680e13a08ec2d01d80ee0283a04b01c0f307046112a83a8134070a583c8223114078170083a407d074070b503660c11e0292094181714))) else (if i < 26 then (if i < 25 then 0x214203e0082702b849208704040626123084581702140a203015904c80242703105a823410b0439848c2116058300842c0a70802a01c05a82450802bb0410e005508031b09052c21509a03e00847c89615109c042cc246108914900c4c24610218c2f0042140b2c1892482b81010429848c21140b240d18200da0a20502e106f80216a0af0468216042309184229062608e0081b40a70bc09c02f00442411901b00d046d1005c40d10c4144080584188868c020538501600a802a80190702482790f61024280a80e032215e0083845248318606f026c90b06214a0870042280de0540d205013448584e00817040703609681180682468802e2068c0643105102f004524092091018023f0c0584188868c12601029c3682405612924910c40f10c43101600ac028092025847e1c8420c901510361086221a10a70041350b01709189190620c985210b0041342460648290c4435c0104d085e14924214e00849c1920a03a10918238030803a11b0844c07c018508fd809062421108828c1844209a20681d21029610b0151054829e03f0100768144318ab04d8201e140b20084fc180b8031306828a100341198202e18042520a28400d018a0884e09909f8180ae06c11201283d810e0778701d00a80a026099043c180ac05501750180d02681620b9842806314e0308500a80c84f01a80982661202610a04cc1c04c2700998321082681930760110085a823e0960121a0158040680290308f0160c1a06034b0082c82520803404c80a4c02080f606f0325424a1006d81882b940a0bbc505dc21c0417708c812a1c2ef04e1250428e806013207b01de1c158a3a05101b827410e0808b018d47a16a03bc4016022c05303508aa1e081dce08f01280c25a10308083c806140a8a056380c8600a284031b8241ba0620ae042d50f40a8802c042c0a6060b95043011c201778581805de081d303070402ca12060e1009a41c0c086011f83009803410a4310b102883602e11908b02483429643106302084c41a12706302405823409906302083602e0c6094c2405a41a0990630200b4034013a0591381f50c0b90159050055091205021490a4318901c004c09643109e02886887002a0301c02e422d0614b05b90e08630803801882e20e8020b7018c1c05816e09921c4210e021c129051c21006c0217308590c616c0240108900b4100680fc08d81912008e02a04442280a802a1022680c42370ca0ea04d00408423d08d8300a885140100c83da1487003501502c810063401413284492410186213886a00d40101542d00406a0b20154250040841340150200d02ee1138310d112006243184097020c0540700621c04380540960150085a824408062b0080c02b809206b00818843405305015301c868030840315804060a0e04b00b8040a623d0403158040601340 else 0x812d03104087780f40210308980c61812c03108741b805c2413c83701b805c201628401c00b005602709a048a19c020f60910183d81e40de0150214096141605847c2ef14e010bb84380c87002a7040185dc27e0400904500c410f08e1270838048682878521898200b706c0801288e881a1320503110c4c1b6020401e80b005281600f500608c12788b0108042d410e8402988e8c020a204b01080847a11684903580ac0220d08f85b41843460d08c81d80450e0298302c5805c02053143828161c0211602982702444a01ee00821c50e2368702c180450e0538421880b005201100f012c2830ea0114380a60f80ec0f07b8466100f2e0370082b210062817603b0102150ac04094c1301d808e0370102b21445014b07741b011c0613805642008bc05c0109a0428c2016d0949248202a0e8b70082c825306c0470182b20c058014901c06d80213409c053d08d12e0108b04d20f80210a11b051010c0ac0470184a41590807c701b01015908079603b011c060ac8502e014009e04401104798150e01a20a102086810a85b04b02680ec01b0190402330e06270090c4268081298102e182180f404b01b8081450e05c085028a0c0b940409c18401440a03aa023808c220ac85b0184282320605c0514105dc21641330410040b0492143816e240b017710d014c10058c0960788f42450a427304f0040b708e0208582e60c2ee10b07f105805860802d8a1e2002a01400980481ee00f0a084f024a1628a044102780f61020784641b40ba0e507858a100c4e03700c1826c13421e50328142170d00e01014c1042c8900888301680ac43d01950150042d413a0a5031423610b8c70105280c406088a00806a0c136e01014c180f4054015085c11a80289108a08da2407a0620204d38040530602d01580a443d019506500404a16d085821e2c0740620220a50041c808711b42a80e80289101d05a215c0601a03101b8042240290322401f825e11b60505702170e063502b80dc02029850312819c0202984f01883c23e15184029983c1450601a1040a1c2170960111e82142c508e0110d01880c03560182b00842c2b9060583045805c0205385b00842c43d06058700826cc1e05385b00842c05306e0104d18340b108065b0080c026808058700842c0a60821402e013c52403130810c61c0b84310510180ad412a01a0204d02450c43402781109cc1214b83a0202e422d0610aa0238040d508e0204d085c23f0806a10a50100610810aa0238040d50843101802b20f40420802798408690a0b201810c41440904681b00b042a214e00817c0a009c0309248422101018c7017c84ea11418828c142ee0fe10983e8059c010490a480b712431017205502881340082201bc06508b840412518088218889d40206a85213886980202a0401700b4062087418a21e18) else (if i < 27 then 0x80c42a210e85c0084381fb0611f05404701fa08016418843a0ec1c804109844c2a30a01b418843a0e063a0109e28342360a16d40b384b40215107e433825c11031507846e1542700181885b611c1016d50684041206281603b858a100ef0310a1c183b7014a0f08d82384340212207e420545c2100140b04882170ca13800c0c427908077818848a0dc11a010a8a83c2340a15140b68042860fc85800a05a0621518440b40042860fd840a1e806003031092c280ea062816800850f016113870a8c00502c14307ec2e80600210501542221410a02a03074c0041f805704418900f40200d087044c18027608b01410009a1130600ea0c41220601d094c8340c40803140b58400ee10185087680641a04f8480e829820306831018d8400ee11305418901b402048087044c1ac0602809a044e1203a20108b028a1040b01d8240b01dc25c1018409a483c09e0701d10284060d06320100784b82270a12e02781de0d063a0102404b82260a01301384d02260901d09a00c41440881640581dc21c10105102840c2030683120400cc21c1130508700cc1450613430180cc14408e0809f81dc2a30816d70920581f815185704202827e15184509c0c42db06e1003b85460c20803109881180ef0a816818858a0f40303109fc1e80427e0770a8c2384021c0fc83709384102c10b0a8c2813e0628858370483f024b03103bc2b82027e0770a8c2383840a8160898546142da10300b80141fba0109785880631303140b05460dc1c816089854611427031098c1805d02d031089c23824206e03d00844c1f903187707205822615184a02013c2db0703100b043820308134a02013d10a080050188258234080a604b40581f90901608704960e06203170801dc2270b03150084b82270903140504382270812e11280c421d08004f01852c21c03141e4300582db0318300b01de0630681d20480c421c0801650840c60d07801608740c6102aa12ed0600102d415c08700c62021c031820a8a06e063060160b540c60c2b801603bc0c61002ce0308740c61025da0103bc0c421d0a81d81882460c296046d0085b6c2410e0a880c62025ca0c018843a11c0ce03800847c1f90318681881dc2bf06e1103bc0c60c10a21308f842e1200213909a4181de01611f8309a055c27211f018c2b80e00211f018c0c614426e120ab83f81060fd86092c00606212b84704b80c21703103bc2c005c24e0307e40c6142ae083109847c2170a10b041c0c40ef0900b03b84d20c268a0c805843a13c07e02018c1827426803109281de140ee219018843a1003703108741901806210e0300b05aa0630615c00b40c60c286016508c0c61002c13c818c18058245031830ae05a8206113018c2840c06210e8300b043a0621038409e040f4021510a184880630e10320300c40ee10185d00846 else (if i < 28 then 0x4a0501832580e00408742702781c077087420324009c01e09303821d0c809407c060236080b203684040f80202c03681b0260080850898210c409e0b203b8202c80661130340380cc0800614b01b00c42740778600a8027c0610b00700c41ee0778800a81341fa03106b81de1825c031112e80540214b08743a1dc833a0150084a421d0c01320410180788310870300a802780a04905aa141ee02eb04580c25f08340500540ee83143bc588a202c08241882004c1240770ae4203c82520a803009e02f0140920a1c288740620a883908852d0620a80430140f20843da01500842c2350b013085829a03a080f208582a00d02ca1107102a01002601d053042e1005400800984cc2b90a0a700b20f2c200380a5c3600421c10b83c0084382170780100b043821709801087042e0c2a210b081c180e021c10b83c00806c14c10b84009902480c01d41884681805580b00c82482670a0e100a84bd078085842a0c61c2960a6418a0741010b0241408b207426b08013403602c12411f85418852c1920a80410e80c41510701621083241500860803bc1180c0ef0507701e01d00c09f004c0505aa100ee15c8203bc0c427f0604f709401110a2130a8c3013e009031099c200c42d503103bc221dc43c08e08742055c0588330320400c421d0613901620cc0c86c408018843a1102c10e80b4181c90ef04a1280b205a0d02ca1180b41d01023e0bc03a04380c05883384d00a0ce0821c03110ce8054020fd08d43c0c482a0fd0b682081606216207e82a0101fa1410544183f414d03180ec240c41fa0c905442004c81008241884681408e013404015f01416a0ae4380b9029608b0104bd014831018840e2606681d018a0c4101d21290538184bc2d408383074842c14e06213c0520102d415c04b05461c21c816085c1804c03a10e07ec2004f0160060aa850c1411401641e58380d214b860ab884f0020a60aac2a07602c0a9053020554426804092d8481fb0c15780b205821d080fe40e88040620a205c00806d06210e84009909c03a83108d02803803d80a0b5050e1502800e00aa02906360e081c385a814e03183907052d0620a704098845824e0a70480b48381a60a704402025b01416a8480b483902d0603a009a02301415c0a1c3057014e0fc83418a07602c0a608d82884e07814305342207602c0a608d82180c28603c83409a0742160a60430301de080ee15c826024058239066020ae40f20c02640904120c42340a02d40a5826c0612f03ba0290621038910e80c414f06235c18840e0d0780310974184b822c817053c2101825c0a70168204bc10704103b04a012c0611307e20c61c20609621b101f425a0112120c62021d016b0188d90630a608081c1029c1070401300e82981fb0980b003004c2aa1438508701b002c83cb0800e01fb0e157c00 else 0x8208ea00e02908d82101005801ca0502213581606d08d82014c0da10103016302c0da06c0720085b822608c0b07b846c0c16406d08081d0288620540703110c4268080b205101b40e814e01709383821d0b40a08fc104fdc23c0183f0189e006040a14201dc86210e880b404fc2260040ad049423f40a88028013dc24e0e60590c6181ce278080c1b02e040da07782f0189e006040a14201dc86210e88018780fc0409604090c423e1032054482c80b8050027b825c0611ea0544380c145040fd13c005940bc01707043a1c0dac07e00c1b8182030412570770060c227c01036c181b7803040b6073a82281508278051410a1010b04278080c1013d81704209e00809610e03e08703200ec0404b089843a1444a16b03b847c10269c09123703a81411f86002044c21c0621401600820ef0803010a01de0c179602a0682ca12c02a1204184381001540b08fc1c06d4220778320584d023e40a0874285b42c4151098801014414ea0504d02391540a08f84060c144085a0541c06e0154010a8906e1603641b08081a61026212b042c1c06c2380778305b502d41214e504502a1a036a0805101de1010a1348200d902e01411f080c2d01942403e08702016ec1c28413c00c41fa10e8714209e080810e8408f816140a031040843a1a80ea120418438101d240709a047c16c09c0874382580b704e0204b4103f41d3407059425018432134830b550181642368402e0160432016a03047e1a80c15c82a03051046d060cfa03281421d0809ca03280823f08030605d01c26811f081843a1c26443109883f48330b40608e03f60c2b8151098847f42040708e00c42d41130874580be80ca1160385461423e10182603d01a0904d40602c41d0180b060e0954250180b01178302c047d42010e84a03016100f0610300b043a0c80811f09a043a1013840404b183a101d2c0720302c81390a11305902720c26811708700d880c206095047c20712096203281420660609543017023ea100874210180b81348307e81600c009c042030438227060e905b02c812d03611b282680ea08a0345501940623609a42047c20304c0704b02720c42a214102f00440c03107e843a200dac07200847c89c60e08743a02410611308742001016410183017816020306036e0950282690860608082ca0c2020b282a03284807c10e04604d01181e11304064882380dc01449043a1a80811f05110c410193004600821c21d0a0c911b701b82408508703032581300441b303421c0c43104281a80d812c0e03b843a1182407703541805d82207783604b01807014008702f02781d40a08fc2501080811f0808250288620500420250280c10a020778100f814021c0603801a0204d014443104064c01180289208742c01380206a218c270040b606a8340f303810b0643103501de0e0084)))) else (if i < 34 then (if i < 31 then (if i < 30 then 0x164e010444183c81640780230827803c0e05c8568c251424600bf00427e21e8505b3010c240a28407702c8c12e010440282d9c0404805142301021c0a28304501b40d8c0b904a07a410046605050e28164e0104401b02e413e0308dc82022214e6054405b503cc0f83904005c233060b6602380804c0a2850b6844c2c413fd0405a82b410188904780d80815a080c2c82180e609602018a158080880888184e9c060886078204464120e7904302a1416d209504301dc040a2869048814203066099043011c060a285059081420206d840593804111060a960383a60c1d20b241b08d8412205e01f00408c121080c5a07a411c01092c203a448c236104081780304641b05cc20314a08701011823e0a205201021421c1138421882880900bd0401720110100fd04220c40f10f20830901b40c408a10b0104d208c8310510301b542011f02281881506811f02280aa1106043005901dc1450a431908201241810185016401486320c104a0101450e10e03b813e0e00b80405904061040b60282304061241160260081342260a609504380414411f05b0183dc81e11304e0082d808c208090040446d0e084602580dc040a209a4301b180d20360684d2142dcc07901887a100da046504700b80216808508da200f0c04031184410108c06901b00408c1348610f005d825203e00c2f02780261108c842846d0c13408fa13380213508998461c26804f042c1b01a406c1209a4205b823608509a42480c02ec0d0305d580d80816808082d80c0c40410309a3012407c0104901b80981a0604f042c104d180810a051183a1581320360688d82690ac07901f00426823685307702780212008088da1a40613408d88da10c1d20324181a026c0600f097044e14863210c02021023e0a206c02180f802084036c2c831008134080c2580c8620a201102013c10a0580404201b420308c09908021422708046c02380810921009a02881c1d2096508001081720c0b4047222808a03506854410164088c0200c880f0a40702790c40610940440204d02030806dc02501009ea1085c02101023e1010420580cc23e10184507a05886206005087044c0c24a10150350102270b031c02680dc04a09a0202882271140450184d02270920840084fc2a20802c30140c403e0a205a03c01c0da06204303018a06201f03e02d01e8080a20180201b680e04103102300405806d03504501100813f0a882e01280802c03682601280806d50802601081606d03036d01c0c01010430348142060580420388140c003108082901e809c0110602220630ca0303101040c02a0140ae050c01c053025b02c2d011b8a0250051812c06600841c25c0e211803f0041c402905101f00441a4310a882812805807703904b00509a03e08d4283a780208b21880a4140380a901481f0041a603e014 else 0x43106e8203f41640c6038042012802a118218546180da0620204202c881e07c0403c02c881a0720470181b40c40621510a08180600fd0874358042680830b142302ec1380405384d023e10e87402580ec0211f0a8c2885040c050027893806260e218c402888620402d500d01c2d411b0507490c40600b284085501dc0205884301046c0600c110b82d01c15221401802042a80ee0102c4200b442e20604b18388690c431018028c0c0cb4070b5120c236030080c38142c1c407402044c2a30c206027983886908030303016c14408a1141882b20f802134018857021d0a04721880a42d408a02ba03c2b91008a036b0040af08107017201008c036015d844214031418c530100db0483421a204c165080e941810c0165080b660383a413908029e0084280a02280490470202031309183a2c2144310514181b506202c2049018c1240f307047e240580480b4046e1005f61208503f6110680b202bc1d81816483002c4218188900fd0160220102d01130a8c2043882cc0104bc201a80b1c01038081827014e309183a2421460602d8288100b0406e009848c1c10e8604210c41450602900a85a81072100a184c41d02881300a8206c1c1088606982101644838410a700423e0d34188282110280b2241c220d01a60b28305958390600d48440204c64201250b542981b80283106a42300424d0407830190c41450821510308178020840ae043a1c07443101680a40288010ae050e20056815b04a01025201403c20c420f12107c0270042b843110b82ca1c0f00b208d89181016621ec0270042862170594384d106221408d82702440d036e00849c48d0c07830304060c28610711b6010c07c0110bc3a0d01800b28321803050600b28402820102381130ae42981a40bc014188304141820778203c103416405484020828a0a40b041041858a1180206d0150181b5809040b224180b20cc1dc01036c0c40580bc0100c83f443208414e00c0c40da02c0508fd01380202c07e8282c890602c83103501100921081c854418058c04036c1980c06248303e0230041fa02b0301a03f023606448013822005408a10a00a1281241018580401b42dc02a8422400d02681138444282140540740a80404fc2a20802c413500405402705015209010aa100480450041d205784a0082c806c02c0450458054020f608d82b01c86803001542582406013408dc22012c0560190805441416406d02298481450b209600824822708a08701380414411f05904c0c82180204d0898202c80c4e010441824140d8c0404201b40f10a0b26024101b580d208607848615c021110440182d808ce02508028a1580808409a028a1011006d059011403cc0d41b4382c9c020888390428402d01110405b01244240a20407901e008bc01c08482423e0a90ad184a2980807808f828a10) else (if i < 32 then 0xc07e0270090d02a20a44809a044c0c07a03601281e028210a018c3821081407820d843a1406240621881e00da10a8609a047dc02e12707501021d0e0b221880c0c0c06d85605047c48d07407b0110342e61010504201e2808c04308818818040013f0081b422c046042438210058816a03005280304609a4458080901340a8c2580826802008b043a16c0560110684d02a20bc010a800d848c03411b4301e08620a28321880b0052014008a0042e614308b08884540202984072805010c831b0884281882a414218d02c81410e86a03d02880216e08982847c06204f03bc210242681130301a004e81616b08fc2c0d01c40b283b0090d041e15c0406a284941c0620b704d02b940a8850890c02a20740a70484d023608c0409a047e81610e8505485b806140b08fc2d02dc12e0609a01dc21d0ce1105940c20c02600d04190c42c40a20d80b83180620812905903180c08816a04080ec0dac0a0ae050020313e0301030288621510506630102a306e0101004d02a208431016401028013f8509fb0282a20600a21a05440c2d5004051828826815c60543c0102384310b1023809c06c040a8c200bdc1c05008985461427e0040ae01b424ac0a0b404722010c4310a8818052406c0104200802a20dc0109f821805809c0104310c42a20814e042044c0c862c0a02708b0282a20613408fb0100da10e85a02301023e10104a02039d81410e080c2b02a80811f0808230101ce06d08082501c0580213f0a881d8258080fd04201e08630ce02a0202888620806d03101502c04428014104e0238030430110544200f0609202028a1100704190600342a30a06d015580881a08611e0081b606202c05b01503422c0720403c02c881a07204a0100824190410a8c2b012c0406d83c02280c07340d03902d0288080e70870404154076011068544100a00340b501de1009e07702508d00602d0603020a101886810a85a03d80d80240607b8466180c4e0121884d01006360360201e00da10a86059301025306606a023012c06e020314304d008210a051425011808e0309c01882680c11f03c5011808e02308818a1ec0610a03101b01021c12905142580c21402a0360504d08600a284218d011809603089853a180c4c0403e10c61021c04f042b0281009e0416054183f40da02c204901881e60e08fc400a58032050b5046e140da431304f0041d20b286902847c1fa0a9840368163813c0110b821cc1c10e8808f80c4c1c4310874280b080e11f203183821d0c0fde0080b00da080c1b0748140da1518502c101823e60e08742900c81a10e0b402283c26816283f0080c410807807e81b61823e21907e843a101fa4480444181b5c0406283042005681340d10c84d2180f002c015886502c025a07847e200f140107102c846d0a448605815026811f08743283c1fa else (if i < 33 then 0x30e00809490622508fc300b0c1003c0129108c1c11a8750600e0028156098c28853019c01075047e141fa214054c1a03040bc01012920c44a11f87018983886211f8441880b082c406307047e1b80203a11d00b01180211a20b41816080c608307046a1402880101b02802da0ac0105e80e805809c0107e886403208c0114380e805808603e0082f807202c0560082f407402c04c06180c0584830401618198090390405381800b404c10406844c100c40bd5068185a423aa110305e822180215e091c83219c020bd82d010474073060bd048c1048c44ac0408f823042405c01830a803100ee060bd03b81048e48de0305482440ef0d202607c10311808246048820515c060886078248480ef0414a123680823a04a0505e81de08152225603c80a11c07202e00c1847c15222583906301c48c07704906300607203a09e02b00404a03a81c8438148620f683b80a41180202501d40e425c0a02610a00960ee0803901641dc0c8090390874180e405907703601809407903908702f0041a603e0148200e405907703024a0f821c07407507012021c08a0850300942a624685044102423f21208d42e83023e09108d42005941940783022283142004a0a8c2901c28a0880304400c642411f84090901c11011f84048846a0811e22582a0382f444b06225506501e0c138a0ca04891a1044aa0c203c184848122460a2a83023e11d870a7852c44a0614f02208960e80e22503bc1811b81d40a08fc2501c07210e03e00809411608708702a026c0600f092843a16c06029a0784a4100ec02c03bc1901380203083b01814e81e0760305ed03e0e008c01043889421c0ac0960080ea41810e85218c0138020bd04028401180216b08d4290c444a07783802089412207004601d02a0c0a100420240e421d0a2148025028809080b2802300412411a85607401380205304802700486213484802101281406c0700270042d622508743380d81f20c08742301c802025308021c2350c01440080d82ac12e05085887821a0607601601dc0e80e07782504d80410610e04509042c2620778408585440ef06a0ca00c1283280304064b00847e0d4194018204e502c0ef06a0c701d0060c12302a09a0300f821c08a09a03820c21c0940614388da0c0b040670190d82350aa0ca0308640c139406506043a10432a0ca0341b02e80e10308f846a1486201650610641280c1170a881a83280c05803a03016050e0611702c08d806211f85403d01822e0580408bb02c20611a84203281450e1038411b40c423e11784603847c0780250a0846a18028809034849421c0a10107e88640c44a16b03b847c1042807602c01de1080c0a750601d01807210e03a03283021d06e0170904c60dc020ed0a18183d82b8083025814d81614e0a1c4380dc02e0e0b14201a405202d0b5046c17 else 0xca01a0205582790c214d06055823f0843110a083022f0802c400810802884609e43012402740850400d01a80d304881de26812a080a080d01d203603bc3c0301f00bd83806038017b0606a03b85a80ec0203401481d80406802903504a82141c0de0b501de1b4041340a88182e5492a08f0182a40600d404881de25418e0e08f82442350ba12504290c0600e951b01de1d41940b704b819c0611f08d4383d8861a0c05ec2019541940b704b8382350c12341cb84281611f8506f38434180bd84006009681611f08a42804d01208521884c4141b4031a07c1c0590280bd0a302580480241e21884521602c0da218851812418c0880f80f044a13106906302008203c0a8c2c83180604101e0546142962250a90180b10180bd0a902102417a83c0160208950080390a882081b80201f00f010c2a20d608b01821407215185e0082fc07202c0440602f405840f04c0602441100680c05e80b081e09603a0180882a308050504d02008215105d0600b10ee0740404285440e8108390160180c4058408509047e1541802c20801a83141201e08908da1406202c701902086c11f86506107843d0602c43b8100b280811f43bc210c502ca0c20f0200b2810e0341c82047e81040702c420052c0608501c85441481083c08f80b0138020bf01c80b01380201e08588781180211f03c00b01005887702a0201042a306a12c06501005809105090303c23e02c04b0082142a20611207481de0d4194018250650060940211f0b6c1810e81201ea0088642820c0bd81e08641f00821907002f607809a12d06302c23e14108d43205a0281460a0822830019408a07845c2a30c40905ec0f00580900c143903c0580840805ec0f005808a0cb04280446c0770b68358041fa02983b008a1c4330611f906302ec120a7b08046a1d41820c11290d050f0aa08500d01c2941318510a05781d204a8410a501c15203004a03a1dc0b022504102889450e4348421888534180bd84a03a1dc0b10740781cca1c20308c0408fc100a500204200a21182630c21e06982f50780881305e821e0c1a80bd943c1815086d20c01e049c48d0d20503bc1081b8020ef08508d848d0c058029b02480d20560090d822910606902b8060c09c41910670044330a05802988d8832c09600829c10f20c89902b80608429205602419065821c0110c820150074c0b21b05ac0ef0c07701909302c20728703bc2c814832c0f03103085c26ac0b0ae02c81444a0918360798380b0060b202c10d846cc0860248321d809c0102c41840c0ef04058902813180214185053c815c020602d016003004a40f0a0846a1c02803122168308630a06a218a80446c0d48511b20c5028214b01f00618868813406580c17b0a430d06580c23f0811f08b816086c23641890c481040702868322c23ec04b01814046c0a0))) else (if i < 36 then (if i < 35 then 0xe85202302c43c0370400ab00642484e00e04381847500708d80a41003821944181b02604d210042846c1486202605e82881241240408984381086200705101d025410a0602504381411022550282302690b407503024421c08030a03a819404612088c3501dc0405409502829826908a0505910242d461285a0380d0254222468305b0220812a100974282b8060c0ba0384d025d0c43100b283484a08044203a81b40624c60385461d41c4070202f809880e0604a20398481e4080b604400c42690840704404d20c15cc0b09741d01c0419f40712341a07080e08803d0184d141812e84a03b808413a0384d01a83026812e84203a01f40706208103700403304e02504381c40a287041082429613406011806481ac0b30904d21802b60240340f809610e06a0381a006006f04304d01f80205304a0381dc48c06215503302c80e044014c3501d40c04a08702182040a2190aed0282680da06600c81410e10e85604e81807a0770874288d82ba085097022818008c0b02790c446d0d00420250280c0ef0260802088d821d0860810f02140c046c09802300443211a09a0390c40ee0cf83802086410606c09019844c21c08053218d01009e0770500c025821c0720301981301c0080cf08742201ac0404b089843a1429421903b84381281b20c02981885140c02090641de1406120503bc1a01c0ee10e83d0348140ee10e84502887810b0621050102160d40d20300fc21443c0a203e0080db82423608743580542408308702380a80204a09704681940b40b85a0080b8200ef0540108fc10192c0213483a0080833e80304a0c09a04060c07a84a087018a1c0b020650281a42690d20e041857021d08a0980c88660c2ba0cf10cc1d01940a2190874228140322368300ca83046d0740611b047e0c26808309741805941b019831030064254151844130866033074060a203040c46c13482095016007d060830974104a8032287080c228302541018310a081426806910303f425d0ea0508108660e80c07710cc1840405e2198340af027802a1200e021c21c0fc09002700410e21908743202500c801084046c14061005a0200800c40b205102c0cc0e40b00502dd028124181340a881a80423e13183d06120c23e09108d42920f41805811282680840216a087422832c10a0111381dc2620c141021c82240c017207854c06c24689700852c44b0602ca0450040c2a1205484a40920368900ae84b418c0b08f84521ac0608308f854612c1160304281dc2a20b60109480a60f80215012300d80682368641880b002840890900f022811f08104f0041de10a12308da19413a02500833c2a30a043504b80e80211b089011846d100f805ec0f043c0802dd09683181648308d43120f41805883506580c10a0770a882d80421621e8310600c086222508fc2a83140 else 0x9284546c07785041502dc0ce1250804ba1819f030218047e10026808403012c86211a06109d0342d20c504906852c8620c604502c05e81a07016209831428c0803d60204a82a209206600808e03e01e07b04721e40da03101300603e01e01185462002b206600c08043c0430a883f013c05c0100f021c43c15107907008c0c40720e00a82080c02b205041c10404e11c06600852c0580661250112440d04640906780b101e0a808403410641800d0a8c3208c19e40d03902300419e043039022818041211a0685461541d60201cd0341006260224881c812810a0605e20102a20a08e03704d20d40d40450100e02a30a08e10f502008208134a04101c11021e8503600c405840809a42d01026821e8309a502008207284508a8328102368403700b010a0602cd07021426908816506d0100c2680360160184d2811a0302082700450e087104023825c0cc0104200b02680903130490138020cf03903300419e08401602084442140450170041540d404501700443c01f0a88380c443cc04e00c0782680c04a60100e40e408a08503580441a1510570150040a80202e0803bc1021404245401508c180f40c40403d00a8148f642a04c010150084d02c50613414382081fa12e8507e912011021904011a81484b40109008da1940444ca0088d82820a421a00834446c11f85041112181614109a04be181fa0cf06301808c43220600f503425415107811833c89002c048118a1c81a07204a00821019e02c0410a081826808207e84ba1ac0320e041857021c0b60107e81be0c1fac07b0082204320aa05b00c1280ac0304082b0904d010612e85109881840a0820ae04d21b802150085091846d0a0c106004bc46d0813481ec06780223685209830410f060cf060ca1e0e03840609780b01203840601604bc1041ca0204181c07080c02c09782086781008704185441580803e016019120054a09d01c2005500ea02a00a07c09a11b07102d0041d2134055c8301250e448d0184d022708a08503404281413f0a883088c813a03015403c14054223042a8401047a08301601818ac020300378200a980e088907c20816c0305609d01c80c26811b85d01900810a12e089c290c540c0a202402f41640602e90602081040b602e00811611060430d01833e4180a206218a8180e4024011828a19410a06a0228342a20a0cfd0180c880f09404067813e0e4180cf080c1801450e10183818e823406a09a0202882270e806b01203508215105811901340621103102e80e40602303102680e40602a0410200b044740400c02501009e40b09a02408c12c08303203808c1440268406904880802a02909801805580208b01e848814028c09903300501c04a087038056412c09600c07007a12207041e03c23e1510420200b004d40a0402500b00ef0603711b057008210) else (if i < 37 then 0x88c1a0960270110c681409407b0101bc8620a205a03d80815205304605c01042443108742b819c04e010a2843a1540a24921a41c02580ee06502c01028a10e870440919c0ce0105e843a1980ee06502851421d0ae108048826008404090843a1c110246104f80dc02e0e05e843a21c2040408f84461180ee0e00502b823f0a04ff01b8081fae0e21884861c86811f82d02c0108600ae09a047d8170e43109741047502e016218846a16012e06802301d40a1450874383a412d04612340c48622092020111c1d140881232815c06e0105e843a1c29409602f891a008e0e60390d221c1c121087418220412e01707283021d0c046018f80fc05e0185a03a83941a10e047032815c021450874282224240ae12302022006224690904441411003402982441340a030d0748482230a16d02f82440c80ea110908544101d2e06202023c10111212057091a1086215c02f8183c815c246030b6854427424601885a82232128802f814c09e03104428304930ec07044012024309606403203428a10e0512302f4090060e7044017c0a7608092c84a8151120960381220e80ea0e02504381100408580c046c1240b00501050281007210e82603901007306083507847c2a208083d01857021d0800803600c410f08084018821e0c486a0e700b84846c12e8611188541046098411b05a60822c21582e00811823c11d01b283046d0e023209902446c16905041085422c0612e016008cc120192068a1c2681002c11182080c110407097182450e13406504281941a13408e42820844a1340a584ba15c0402303101820805cc0b08d84d025d0c208103680c41a15c087430824268287041052c25c0c015503580409013408e03013c42401530900c08622368701528194034070b285441840a01530910c446d0a03010a859419f0812f09510c41d22198501810c41440608290281010c0c40423d10104d010411609743281ac0520f106847c2a20d60108b01be0cc13205502d80610405c010a8042848c236860a0b00421521112342c809c0304a06d01a80417a15185041042c25d060cf22405a411021e05508813a802a0c08a08da18105a0e605912e42012e861040a1c10410b09742c84140c038907847c2a20c10b603822043d20f05108a80ac030624c11e80b3813c0101e84b823f11c01108854021424611b4338082d201503502d0082d41340b4842a1808601502a04b82028203603bc290841a211f8350358048680380ae02d80406806f03502d804080ee02a08d018189424a0608fa8d82b940a89503680c23e15104507384819e11004704a8214040ae0410464182a36018502a28104430701285410104068a05aa1c26812e86097b01f40c16e03140e340740a048924628104e09704683140a16a51b502a21486a1502041502dc12e0609a283025d0ea437 else (if i < 38 then 0x1111b04081020421901781850008223603408820c50e0290409f90100a628704504d01803810e04908f00409414401482c84502224608002087a4220e208002006042f0770310f4844808062194088a1c2000822560380e40c05214303b81805001a11a07e820053016006009855424e0c225100805101a11c07e830052c1c801418c0582940c10e01884640c80c10b08d01848881203108d02205c2c403108d42101886c03108d02048806211c83091101806211a0408e00c423506e02700b84023708e0270082dc287080380a3820c01a088605044428710e02700b8382450806901d00d405216a08dc31035c0413a080821035c0213a089c210d0c1a0bd0510200541fa01003d81180630ce087073809c0224921a43180dc0705e0012310c4c0d0860830302f4c1a0a285b01880c49212984b04580d40560112302142380e06f1233808c1e062050a8408221c0212905e821056c02401218854216c0560120684e82260a05f308845814509209b00883426811c0503790d2c0260d0409480d00de60f0404404780a60770406a282140c062091a84426815ca0544f80d42215c087027013c06e0370104442370c088218380817a084300a84102b8860e020514268202520b9a05a844236a46081502a2411012905e8182b9c04a49051020324172a45a180304153e0304881de25c10e0ea0581dc2a10a08808b02f40c01e01e00690c42620b60f20780a881b0960fa18d03e0c02684200690c42320a0bd306828a0c06021510309241fb0b60350158041e40830874301bdc04e011230404142a102088902d805c0260e05ec303cac0224505ec20220c04e010a802f614110a093034816c02e0105ec38220066e0107e82f415c0210601983c813411205b01e80820212f09183ca48c0fd60545822240a0fd05e8202200660bd830a508500be2360278844c1c031218c4817cc0443105142282141b4070b5046e1429421704b081b40405f30710d22006015c21882b81280f431080c190c4c11a02085c2501dc0214a060c201a3411407d01120c23703e080c41818060a0c0514201b048cc0d21b034e1405a815b0180ac2d203142320c621060430b01e80a10827a03d01103c1e460809084382020fd023183a3011060107e82f61005200640684e82370a046018d8410920fd85c2302db404096121182006260e218c4a0c020211f8320d901b407a0205b0570c1009608703f4c1d1683130304040b60bd0500a000c1a8036123003681413a08dc4812429212203607483207c03309102f01f802287e07012421d0d007e0083880522110511d00700520a904404c80981700706f046c180f440d088844e12c04c0d09d046c1086340703798440c40a04650602880c09202a03b81d01f80360e09281142450ca0c02282880e80f60208f90c41440a43105e82 else 0x507857021c0720f100857021c08a4651b2825410a06502a84426815ca0545680c2b810e03503680d4020c90a8c2e84b423a10605b0282870d20c019c83c23e15105908a846c02e0112302887a423601700838842e0ce01014e8440c20a02903b81c846c0c02c94968440ef0c0fc014815805c0202914382484580208b02704381580204e00c84fc21c0aa06b00812021c08029508820c0c86202950881dc11413406502a01c21c0aa09a03820c21c08029508d01dc0221985508b80446c06016508902c0f420029d08820e1007c1440a881e84446d04061d08820e0c0b003101490182870ae010148a1e0c0b00310298a1e124220e304180a4124228))))))
def level11 : Packing := (2241,4,9,0,0,18,1,nd11)
def nd12 (i : Nat) : Nat := (if i < 3 then (if i < 1 then 0x3fde30ce18c1fff18670c60bffa81386307ffd409c3183ffa804e18c1fff40270c60f7f9c1386307ffcc09c3183ffe504e18c1ffd20270c60ffe881386307ffc409c3183ffe104e18c13ff52660c60bffa93306305ffd489831837fe944c18c1fff4a260c60bffa8f306306ffd27983183ffe93cc18c1fff41e60c60dffa4b306307ffd25983183ffc92cc18c1fff39660c60dffa49306307ffd24983183fbc924c18c1fff39260c60bffa87306307ffd03983183ffe71cc18c1fef28e60c60fff947306307fbc839831837fe914c18c1fff48a60c60fff245306307ffce2983183efe614c18c1fff28a60c60fff145306307ffc62983183ff680cc18c17ff50260c60ffea01306307ffd00983183ffe704c18c1f7f30260c60fff941306307ff480983183ffa204c18c1fff10260c609ffa93286305ffd499431837fea4ca18c1fff52650c609ff293286306ff949943183ffca4ca18c17ff51a50c60fffa8d286306ffd26943183ffe934a18c1fff39a50c60fffa89286306ffd24943183ffe924a18c1fde49250c60fff989286305fbd43943182ffea1ca18c1fef50e50c60fffa87286307ffcc3943183fde41ca18c1fff50a50c60fff285286306ffd22943183ffe914a18c1ffe48a50c60fffa05286307ff902943183ffe714a18c1fff30a50c60fff8c5286306ffd21943183ffe90ca18c1ffb40650c60fffa03286307fece1943183ffe70ca18c1fef18650c60fff8c3286305ffd40943183ffea04a18c1ffc50250c60fff981286307ff480943183ffa204a18c1fff10250c60ffd841286307ffc209431827fea4c818c13fe52640c60dffa51206306ffd27903183ffe83c818c1bff49a40c60fffa0d206307ffce69031837fe92c818c1ffe41640c60fff9cb206307ffcc5903182fdea1c818c1fef28e40c60dffa45206307ffd02903183ffc814818c1fff38a40c60fff985206307ffca2903183ffc514818c1bfb48640c60dffa43206307ffd01903183ffe70c818c1fff28640c60ff58c3206307fbc61903183ffa804818c1fdd20240c60ffe881206304ffd49883182ffea4c418c1bff52620c60fffa93106304ff949883183ffca4c418c17ff51a20c60fffa8d106306ffd26883183ffe934418c1fff39a20c60bffa8b106307ffd45883183ffca2c418c1bff49620c60fffa4b106307ff925883183ffe82c418c1ffe41620c60fff9cb106307ffcc5883183ffea24418c1bff49220c60fffa49106307f7924883183ffe624418c1fff29220c60dffa43106307ffd21883183ffe80c418c1ffb38620c60fff9c3106307ffca1883183ffe40c418c17ff50220c60fffa81106307ff500883183ffe804418c1fff38220c60fff981106307ffca0883183ffa404418c1ff510220c60ffb881106307ff440883183ffe204418c1fff08220c60 else (if i < 2 then 0x108340b0770fe88031006004e03a0cc0b8611fc09c1000413403943105b40a10e8a0c2a08006103a1200a05b03123a20e1328b053c12c1000420e40a05b870fb029c09404c1020505b07788fa91f263e0c7bc8f6d9eb83d1e798cf261e2f3c1877d4ef39dca3b787688ec71d743aba7524e931cfa39ae7324e5f1c8f38cc7130e161c1238026f54ddc1b9236c66ce8d8b9b0035c66af4d501a8634ae68f4d191a2433f06754cdc198c32e46554c94991531d86348c57989830de6154c10180f2fc65f48bd797922ecc5d18b8b96eb2d9c5aa0b4416742c8a58acb0715f12b9056a0abc95592a605428a7814c729605210a39945f2884507ca0113eb27a84eac9be1359267e4c4c97692d025424a0493212532466485890411f423c646e88d0118022cc4518899111221f043a886690b0210e41a8825102d20263ff07ef8fc21f503e387bd0f5a1e803c8077b8ecb1d5c3a5073d0e661c7a388c7000de61b6836986bd0d661a8c34bc68d8cef1986328063b8c5a185c30445f40bce176e2e385b28b3616082b785590a9514ea29305148a0613c026f44cb898012cc2548499090f11e4234845c08a7112c21a8423882710201ffc3f707c80f6e1e983c787810ece1d0439207100df81b9436286b70d4c1a3033c066a0cb8193831e861d0c1e17c82e905a90af4155c2a785470a42143427504c7095a121022c043208120f8c1e903af07180d8c19b831405d60b5015d02a30512096811b820e03e207500d2819102d6055c09b811401d0032c051008800e80150018801a00004ffd499cd182ffea4ce68c1bff49273460fffa4939a307f79249cd1837fe90ce68c1fff48673460bffa8139a307ff4809cd183ffa204e68c1fff10273460fff84139a304ffd499891837fe93cc48c1b7f49a62460dffa45312307ff8a29891837fe90cc48c1ffd40262460ffe881312304ffd49a031837fea4d018c1fff52680c609ff293406307ff949a03183ffe93d018c1fff51280c60fffa49406307f7924a03183ffe725018c1fff31280c60fffa45406307ff922a03183ffe515018c1ffe28a80c60bffa81406307ffd40a03183bfa805018c1ffd40280c60fffa01406307ffc20a031827fea4ce18c17ff52670c60fffa93386304ff9499c3183ffca4ce18c17ff52270c60fffa91386307ff9489c31837fe944e18c1fff4a270c60fff251386307bfd079c3183ffea34e18c1bff49a70c60fffa4d386307bfce69c3183ffea2ce18c1bff49670c60fffa4b386307ffcc59c3183ffea24e18c1bff49270c60fffa49386307f79249c3183ffe624e18c17ff50e70c60fffa87386307ffd039c3183ffe61ce18c1fef28e70c60fff947386307fbc839c3183ffea14e18c1bff48a70c60fffa45386307ffcc29c3183ffe314e18c1bff48670c60fffa43386307ffd019c318 else 0x514b12e017a0ca08408a06a0140e01da0f09110e0318e12910ea09a0108504608303ca0c4360318b0464156088010836030772920318318a10e40840ee0303104607787017016091077831850170316110778318512e10ea06406a0110b046a1203c08511a0318c61201608510e10b85a06016a120858318560920201760e03183107787004e03a0c0318410ea09a06a0110b085a0c031880fda09a08408a0104610e03c083a0c12f0318c046801a1061007715c10303183189a080960160830910fd86a08125016a120838318601760961010303183107787436609801a126031030772420318318a01608310e0fd84001a01e03e020318510e4094080fc40e0d30310778802a60860e0318310778603107783112e8403107783110e84a01e03e020318410e0fc1250310778514b12e046a0ca08a06a0f09110e0318a001e03a0c0318412e0fda09a08103a0c08310e03189015014013001e00c0b092a0ea0cc0a8a016209e01e0015c210a0e13420da0c43116a1228d0db0cc0c2019c04e03e02e0004641040dc0b28712a1198f609608e0317705c6010a215c10e4312878b0310878243428782209c08c01210c0b08702503120c0772462878c431c08046c0108728786c0b408401e00031a100ff03d0772870468b116608e0143161260116a03110e28720c8b831431211c09036c0108728788c09c01e0003621261020f087c0b031a0ea0cc0a8dc09c07603e02c0105c612c0a40a10a6104310a20878e17710b0fe06a4310fac0106060849228705b8c019a09e00046038401031610c0b087c0aa0ea0c8d031609608e01431a0ea0c60116a28711a10b8c40429203161043185046036a01601c014278314312928872878b4310e9831409c0113488709106d6126108b431019210c09c01a1283141008720e1340836108d036609a03c0122542104623d83143108711f07720c8e14b10b60960840105c60f60d04f0314318b034a09a0804603643401a01340a07740b0830fa8d034601a12a1003143443187a09a0803040b07708340a177880c6a09017a1003107743187036609401a12085287031431880ccc0ba09409401101036031a1000e07706020c2871198f60960817706243160116a10e23d03120c8b01ac08c01431a1061007a04683120906007720c8dc09c0141ec0a08723608320e28789831431c0903620ec010cf0872878901ac09a09609404c0143120e10a8310cc06013407720c8fa09a1010303107743186a0ec09209431c1021003900b13440a05b1228c0fb029c12c1040a05b86046409a08048407031612c0ba0ea0c8a046044c106104094070de05b03107740a8bc09a09609c086080600300290cc03908508740a20e8e0bac09a09c080300de60208707789036c09a0960960302940703105b04141007740a8da09a0843103)) else (if i < 4 then 0x36431087077a0c8d058831431c09206c0108760e11f89c0860304a02c11f11703908740ba0c8ac08c01046c0ee0309124607721289a12c09c08c0e20c4310de07788031409e0321211f091a0c87407004c0e60e02521211f07711a89c09606c0104a02260308711f11a89212c09c08004c0e43113407788c09c0611f04a60e07741011a88431a12e0311f40b07786031c0b40711f406a1211760e11aa0c8ac0900460304a40e11f07711a8801501302500ee0000dc0ba10a0cc0a8a0f20c9016209e01a1020e20da0c16a43113411c8d0f401ec04e03e0216e14304640e40dc0b0b216811b8e08a05702c60960660113411f10e890150140080050040840780318810a031431404c0b08407806d8803040413411f43110e86209c01078c0e20ec0b025a1003120c07724611f8d431017c06404c0107816e11f8813406da06401031c0b042a1007710e0468b02c60660103161260213410e88078431a09a06804c010b209221120c03683107721013f6119003140a43110e8406d01ea06134046434034a1203a01b40a08540b11f8e03460113403143411f86a09a06134430a0c03040a08540b11f8aa09119017a0e03143107787016e00004a10a0cc0a860f2a10c09808212c0e20ea0c80c43100a16a40b11c8e15a14e13f12d125119113e03e02c0a40416811f1018e609e0343160e11f0e715c08440411340b8b07806d609c0660604a09204100c16a03440b20c8da0604843103140aa1007740b10e89c09c07404603e02c01612c0a60e14010e43110a1018e06d058c09205c0111f08760e10e8901ec04046031a1213440fc0b08307811f60e10e8d02c60960660103113411f10e88a0940728709603160e43187046036407804027a11611c0108783143115110e8d431804c0110a0e70b28310f209208310161260e8d43101e40ec09804a020b2c0116a83112021008312560e8f078609804a03c0111303621704683143108715c13407720c9003660960303ec128104040f206011f03440b8c10e0d3a09409401036031a0ec0b01007720c13411b8e05702c60960660103113420c10e89209c06c01046208092c0b612a10c0a8a606804c0106da0e83143120904612513407720c8d084415c09c01c0b087e022360852101348b08483143101ec09804c0121008720c1348b12510ea09007a0603100580aa1020c11f1018cc09609c0360e00516a11306d03420c40b8b0cf0c9c06206c1221200706d43140a08511a8cc09c0640a13411f06d10e87e0327803028407743140a10e88031c0604613407710e8640a00aa06134431a1203108540b11f8a036407031a12406134c0b08311f60e10e8bc0960940703140613411f40a10e8913411fc06c1200404143106d40a1228a031c09c0620540413407710e88009042e030770318501500ae030310778 else (if i < 5 then 0x9a06401046031015c0ba0c08708523621012e8d03102ce0260123661221012e88609a06c0104322521901703683143113411f20c0922100772119101508243123612e05434034013a09a0804602340a01ea0308307740b1348e03460103143413485082430a09030a1040aa0308307740b1348b815a09a08a06017a0303143107789a0cc0920821220604323603600a15c431a0340b11c8e20ec090f204f61204343103640b2368a046215a0860202c82381e404031a0304a41213408340b8f223c09609a0840403081e05823620c09108740b2118ea09a06031408a0c23608521013489037c0960940421e28784315c03603421040b8c431031a0940aa10a0308307740b12e8ac09c0101e0872872368613412aa09a08c0440104603101e043a0c08323620e12e8f03102ce0260161220e13412e888314310cf0c1046036c0108728789c09a080302190f203620e08708389a09a08a0640104d031c0b00e07720ca0313411b8d03102ca0e60960120ea0320c13412e8a02aa08a06606c0181e20904683143103d134077a0320c8fa09a08a06a01005031a0320c1341018ac09609a0812a08804181e03ea0308703420c40b8d0b2c0920920604100703640a0772364311228cc0940701561208740a21913408046a0c409a08031c0b407091a0ea0313461212e8dc0660203e03141240a1348711f0cf023c09608a0600402203643103923640a10e8ec0908720c07713485031036c1221008512e86431a09a08031a0308307740b1348913412aa09a08031019083a0c23620e12e8b019c0940700461208720e40a13489c09205a0303d13407712e87001e00e03042c0b077046870f6016a12209208206e03c0a20f15113c20c1318d049c08208c01014c0e20e249031e0309121420c2120778f031014408c04401e0308721211f091a0c8b02ca0ce0307760e21211f11a88043a12c0920920820640fc0b03103620c0772362878e031a1240604c015c0b0bd60303cc0a436a0c8c02ca12a0c60960307760e11f11a898310254152156060f6c0111f431603092212087077a0c8f031c0402540ea12c0b03c61011aa0c8a02ca12a0c60960611f07761011a8940403061043411f8583143120cc0113411f092087610a0c8a43440801340ee0340b11f0910778901607743411f84430e0340b11f0910778601640f60f07743185076431c0820816ac0e20e00c03909140b20c1318d02c02580cc08212887a0c09188c0860860604a02c03908721140ba0c8a031408404a12610c0a11fa0c8880c0bd04a02c60e40888703940ba0c8a431a1211ae0340b07786031014a12092c0b03c11fc0a141a0c8a02ca12a0c60907760e11f11a884070304342878483143120c0d40bd092c0108728789c08c01025c0b08722507720c28789236831c09609603c0111f1174 else 0xc0be00001c0a04603606246236016209208206205046036c0a20115121110e8ea0c01308504340b41309108340aa118a016211601434a1143186a10a0c40b09108340aa1187031a12401019a1020cc0b092143077a118b03102c211a10608e0124643160102920c287a118d246c0920920820603923603600b43108640a21110e8ea12a10a0ea0c40b40aa1187031a12406a10144a0c20e083a1189211c0940760503602929208720e40aa118b029c0804620c087a1107787e0304203104684a1240604ca0c03ca0d43621103189001e03031046840fd04ca1203c11a083a0d0318812280d01608311c0fd860fc406a12092e0311b0310778814b025122e0311a031091870fda1211a60ea0d03186014013003e00036a1200dc0be03a0cc0a8b0b9017408e03e02e0040ec0b125c0a40d24613a11b8e60860ee0360260115c12110e1012464318b015e030460318403124943183031a09603a02602e01431610a0c60160e15c24612910e8f10b0fd046608e03e0240105f60e60204f0314318d034a08601a0ea0203143443188a08a02030a0e430e0307740b09140a8a84620f23640f21103160f4318801703124643107785031a09608a02e0143120c6010f660ea0c24610e0fd8e14a246407a0209624203160e43189c11a0f60d603a02c018462464362368314318c246431a02c010b684620e15c83110160810e09205b60e8fc08208202046a12c0e20e00713440a0774311228d608e0324660e6020c913a43111304640a8b046031009004e03a0cc0b87a08a0e00a00903113a24621211189608407c06a0620560e13a13404903421240a8cc08a060450de0d303120540407789009006e00c0b00da0cc0a036880c9236016209208e0103620615c20da0ca0343113411c8f0f520e60960112e28721913488a100310878308228743413484208206c0104661204320dc0b036031a03a0cc0a2368e023c07602c01c0a0466121194340362368b08801520560915d12e08228713489017a0ca08031c0b40101e091a0e134087a0361212e8e03102ca0e60660161213412e880f5215407a0624ca0303161243189046209608a06c01028205043612036c0ba0cc0a2368ec09c0101e08724323686134287a08408401031a0ec0ba0303d07712e0468d03102c60128761220c13412e88612c09608c01043c0b03607723620c2878b404084c12c0101921913487a)))
def level12 : Packing := (263,3,9,0,0,15,1,nd12)
def nd13 (i : Nat) : Nat := 0x3144811804924410e4308782e0a44631120350cc0d0d0c61a084220240a014060e438460c51282f034320a8f825098050107a0b0c4874410e4310382a343103209822018391282f031dd0c8b82509021068060e0300a0c60b4410c82a3509421060050f43031878250982108805010c60b21d0e4320a8cceaf6961ce560ce20000fff39a307ff989183ffd018c1ffe70c60fff306307ff943183ffc818c1ffe20c60
def level13 : Packing := (8,2,8,0,0,10,1,nd13)
def p3853i6 (i : Nat) : Nat := 0x9
def p3853i7 (i : Nat) : Nat := 0x201d
def p3853i8 (i : Nat) : Nat := 0x181f100247a439901
def p3853i9 (i : Nat) : Nat := 0x500440a000284f412889610896c100000000000000c067413628009a000290142868872034003d06ec14000381cc03801e405d002710cc0ca00181dc07c89e1063c069083885b021886001501ae043c04e084809326600bd40310c301e8159045812803c016bb008004001082217404337247002
def p3853i10 (i : Nat) : Nat := (if i < 1 then 0x405668bff40794098a0a24888000000000715b1951000016cea000000000000000000000282e18272e08e304f0000000008082000000000000000000000702159c43008b3091f801b428c00000004f80546ce5247e0000000000001a094906600000d0a60c4ef062e02bc01e320c1e23de83c1c1a86118d06758a02808bd003415880124d0a1cc01c62cd832181ae603e6170fb02d80f8e1247084a343b187682e06050f024201acc08ac3378019bde796b2be00a004308024a8bb624120141c0b54c37402f55892405e011a051e0328a0a3d0125f13deb05f413720d1a067d8282009c6134a2a1301e042754112fb279b069808e6243f08f3822701f94018e606005144484c130700f984da40e4e2d86048f04ab0a6ce21d501aa8b5e825da0db40584898d00b86e6ae7a00000042760000205af046fc5c7cc2e808f800000001e51c800740b3441fd0070306c2032c45c9a0ddf088c0210c270c4859090f08f318aa22605086b94be01aa2034360558371057f2c1100001b0a6406de074000040182c20800870000300214a180000614680272021f047af4257012a40a7ae0a20592149f41f38026f019e94ae808dce1c714710488c02330bda60140324827f200b5426b42f3c03d8037313d3b22b58780000a06fa88270a26c852301773080d801403b9445481f5982500de606930ae3c1e420ede0128000290e1a044e046d850e426e40a2261c98265c0be82b3b424f8ab045b340c0205b800021870a24a4020384c7001a603146169002a00bb201b209698b68c2168c56a08a20a93001eac05e337280f6c46502fb7035284bc0001027d9345a831358600000f093983368047e021e0418000140e68cbb2320c84a40000a07f0000714a584740065b038e30bf0056000000000000301eac077e601c83d29e498042000000002c04f652e74388000000010b0d000068013c24c0000a7a10014800002b1200000000000004543a05b18b40c02180b10000200cb41558c58b065583a64001a113260e381b9c09b20d3b031b01e60267c238000078aea89020c094189402010a50c0547b47b02948045364aa602280e8020e284fe790202986ca6d53c10313003184f8810ec151c5a39814fa002d71243151d83e00688616003e0c150ac1e9021e84f8585140ad1b287040e813a553f270b0a01000c135c02000f000401020500022601020604001301130d110100260f0301010200212509363208080e0d00010000200313011c2a00000e0f040b000a0003000e240e04050017081103220c3b021234001503022a0502082d0004181f02261804120307020002000d02060c00030701080005081712010a12060a0903020b03bc1b000a0300490804000d07030410140d010637070001011b0b0809152e27011104033b00003c2505170201041b10060011 else 0x594e049459542c04d1819e427bec13f08c89212809720ab7604002a400000000e61268407c58e2110f073cb074054b0f13f03dc00774177406b870648185c18ec0bae08e5898b584d0c18d0744823d461ba526215af0160c05440be307d8000001188028cb3880000017e2304616fa8343826ba1472a9230b79c103a0e04296781b0000142fa0075283db420c403f86073024a81f54e6ea003f02901cc32059d02b0805e060640ae963680a2b40b78f1f30993028d40ae964e700ceb16bc41756708095b830dc28040bd5147a038b50a3266df1581804c01690e6900a120b3c81c680e640777b06400ab40fd50615031a005bc0d93b28f00b385726095a173d025b6a26009fd28eb81a681c2c020d0245013e807040f7e037f024d81ca80bce62bf021b022c42ce303d682e74048810aa08ae881a8002a06d7081294f800728120013c20421c258c13c229ef0107800b0e02207fe0ad140ed611d90a0fc1e8402c764d200e594d11854807e2079800012ca5247fc29280003c1c883060082800000001c0640000000038476804c508b90a2c58756483805980002c0a3c2d3e1040000045ca00000000183bc0001047c00006840141d980030000700a4000100ebf15e280c2455c0000c00d104a000018a7bf11ce025c0001608800005836b80ea000)
def p3853i11 (i : Nat) : Nat := (if i < 4 then (if i < 2 then (if i < 1 then 0xc80000b804a6040001c3800020080018018000409068280005170140a050000c220a0b01c0800080b80209690481402050144c16000180c0400004021e002480222118040a01000126e0e1880016001300000430005000150b8680203008640e182a0341c06008840a0000030120b1202002000001c4a1b0400014010d09c0e070f028045600004181200018000400900040f02374081d000344800000980c0a340e4000f000081c05030540a02029085400028000a00028300001010b008010080404040880006080b02c4e340a0080201000004c0100000008212000021001808000101800000002000ea0f0980056050300402020b00c040a0080c440001028060e058000402008001005048400000000fc0802000640a03008040214020201a0d0400c021d0002c0a0b01024020000008120100284421f070d004000b8340008010681203001ee04010580c002e061c81819030000649000f4c40d040000c112a0180202028301a00060440407000000a060000020000107c10000282c02080001800110002002010201c020506000481b0600802022a804103302814280f640440204040082002008301200390000000060500a01070e006030206c00aa0180002050007c24230680c00030380038101181000250206c0c01130240014138a00004098041a050001c36001b00400021b02c00010a0082002118a802150080800020082c06050302d20040800c2c00000000a08020186c000101000060100812020180000180480c0000068100006050200001020c006080500006070282c02031e05800020380000002581804061080c08090500004fe0e800000a0089420001f000040c008e8000a1d80004000000086010082c1800000100a00400041240020390802090040005050141411010100a7c338040002050d01c0c3d0040a140300000010d80c0c2a048202001040140015011984407010002809008402801058280200168c83e1b1787004030b0304e050286004011203410000185400084881c020300000161507858041000010003313810080301138040f020b02805110041c000885422040208016180102c18df3a83c2e00040001200010000022008180c0541000000e03000b2050a0086a00030002c09000080c050600ce203140ac10020132006090481c023e010380003000100000008f4000b008c404171185c1200120441e070182d22000608c2c000022d8c01000341082020a800001084014000001638180b0000213030383600068d800080d80002bc0880006000400410040080400021404402020019806000180004000380434040100008010000c0004038140c00088900000000000e02000006a0e0c80000090b8041628118380803658a0001d0104800030c0480002140040e05088480403008100a2d020000e03 else 0x85ab19e81cd467b8c13da45f9280da1b749a1490c0a248555e073d617ed154b48d58604d540e75c0da08c14cb188f52b0c58b4849a93532a0d040120a82e38091e34f8d188d58420161b700cc882fab02ca005e6a113e812ca808d633e1a02be8322482a5b0128000014200d85391b665411b980f9201ae00835e040cc46300000203ff0ec25c0f580d14a02fcc011a411e18c93e473b60c17409080000a05b6019a400006862a07c244e448000000000501626f67400000000047bd92102f82398898ba053c810a4028e5007fdac420168fd8410000076175ed5ac9821783b9a2cce9122201c5283f6c0933cc2c7825af845f0019f21486c1880067e019b00000304c6000000000080b608234d01c6b527740e520261139a300cf64d23000006a1a61182020f9eadd10053a000014c26401cb00000b1a59011a9c28af357000b1e6edb918b14b15c00000c169540abb0283f0022e0f64412a800003071b0e469c640d4017d0317ef2b5184bd0c85a07826eab5c004b03c020b87325854d4dbb0c4c094785933d84e105ce5091c000004061a04ff00c9600003988c800f6a1813e1022860ca84660000020a520236d015c0020d2e3e1823780000601c2c2b35188e5028680cdb412c400004065dd0c6c00002013700000413d420290c2e2a8309a174a00000000000000a08a96c02b00b160558500be204ff5988fb280b64036174dc1f52845200000ac44c0000031b200000659f800002021bf0c2c015180074c85d90097902e9bdd5f00000806ec0000241c14b1c9e09bd81350d03d5d2c6000000000000001d67b200c8e0e91c324801afd2968e013f4477131f9b0a960134880947825c60b30ce58f19731b2c5d91d660a9904efb0c30868580000018167041040192e0ff100f400000000016079c00001b1b90000000000c2539a2dc31760613c40000000fd6606c000038104985e116728016cec20b800002005b00d1000002844e37c6a8005d58e1c3d93c17c80000280e16906930ae7ae2949950e8065b64bec0a06c68800000e0a8516b7dc168380474636d2029800007035c2077f8d33305fea81b31794b609f29996f066c30066631a64067282a07435de234bc18c60d1550cfa027e6863a4001230826e0a30828180024e6510002f242900000051566c014a624758345b0604ac7f9820a0be3727c6dc65e9ec040000000000a07680000030adb03ae22e0d6e986000a50ba0000028b0c800000000080f79dc455d55ba6231e164a831cf8007c0b3800000000000000e63d12583400004805c806258111a8013330cd0083806050002428000201436100103400000e00c06020a018080c0e8e80e01168014a07028740803058080011288040e3500808000400025f6022806c0e0400000340a000100a1f118680002000240e073b0c412101880) else (if i < 3 then 0x9ba192f90233ec47cc1d3f82fdf04ea02b17408f9008266010e087b85bceb04d60694827098493604e51757a003bd02d4e227c200b080cacc0db10be850184400c8c61e80000000002e8a0c090680251004e00000000058c07000000000001292b5321252922fcfc45200000b62e5a0628000000000000012161a85d7300d8b01f14159041f20849470474a07f2c9bd38441a063d400068105d0c6ea11ac266398183203354042b2c341c2bda4ac850745ec110814ba063e60a794f2bbc294f80444661de036681bd0b2e5a061982a8185e0bb167d1084a35a7c63b0318406449a06b1060d7050860bd78199a0b0473098d08f10132c02c66b19747b2da331d1c75bb2c2b0b3e814a80696a804ec6269e0a66c0036022c5037601446ca5ec029a563964c00d5896c014a334d7ea70f40f8800e4712790c7d88332a8537e01ebc8642c01be0013309dd20560ab32684a1d09b8602799f19c1b9940324c0f4d0612f356cf0234c047040b88356e709df620994274c8560c6030c6a6a05f1c831ae6baa2ef0501e9102ac311c4c02728142d066b7755d413df029b6051f3418ec30ce580af807495a93002ad01d50058502c65aec2a90d0402ed9b5ba0089a8136081996210342e4c005f3312cc014e416346476130cab74cd602c81c7d3827a266212141702e0c3e2ff60e2e195400b3904ba9ac8dac10c403098bc7365c3610cac132fb56dd7b81216ed8107e84d3906a5406c1c4e40b03411aa4a4e21430f3017071a9f230eac6033bdbdb27cba09419d45b8264c64e1ec0348b23a087900606c04cd4112a0c84c14c5411098207cb84650cada0e4a00217d80a463f1a16ac815d63002f09b1a0abd832a319088723ee0c1f0281700e7cacc102ebfcb25731ca870f9cc4ff42dc6aa2890ba52c878404ab83bbb0a29e13e94d486815d065c8c04ba5d6358472e7260c0d384cbcf1930760ac45870d8ee900cac098aac3ed15f18b18ed6910c592342f79b081500d1cf98a8b35601a2813fbb6cbe41b47052cf1b88a0204c31e3854f708fcc27dd46dfd30b096264033451818a854150869e470ec5588033fd0abb203ae82afebda3a59590172bc2ed2b0bc91a5540567c283d8c7dc01e0cf77cd844434cb4093140e15428d900ead0473680208010c0cac9098ea0db284ef08056164bcac69201a6e815a20917001dd01072036ab60be40010993f60c03a400a486b4814fab2a4709202272581022842d806bc00003861b2034ce095308cc106395a211c03c76189f008bf85cc30c170c7b4c1baeb019575656054cd903bb136a00a88138f05f3831d8c5c310153241cba30b2c131fc0c01188bd82344082b56b6f80c9f2125c03a960bf9d8f9f03df76029aea9b582ea05eac01e4901ae8a48abc79104e762e3f8110331e520aaf040a11d54900de00000a15 else 0xc3bb45bbe074b049d6025326022003b5c2f82326b1600940b0583107399ea047f4c847da9df045eb0487808c11cb040419f321682b13c670ab0ab4016a000035d346807df1c30201b3c01c6393b2a978a0a9105ad50a9d82713802a3c2cb9895ca07016d323c293a0426c030101193023090433e0ae50e323423da2a12a1994403941e3d3b15900001231ffdc586be7ba34990c004432f902be002378045b8408b8553817304f541d0060022d10669b6b70d8b0e8189107d040015c0f2e1615001f2e0ec5c2e3a016c0607b0031e58530035046532f01b39cfd2b0a2f61340000104cd98682b80de232aad938f09bec0609c152b40d3783ffd07c7e655081ec62261a0189616b01814c0485523216c385c123f8365b1199cc4df42849811320a1920873c2ff483e017c684994a58ce98122fb12820c2b89c338a90420df2143740b3684ac60b2b4a47f5e59b8479813228e3265c47702c9b0467808dbc01f2b1a31038aa3332002283dd6ca717c58444071094bcb112aa095302306305b00000e0df2c0d6800000000000001d8231b20600000e134745efcc408b06fecc6c3588633d5c000000000118ce7b1334a91a000000000502a240b204044a24aa6853000001c1175c2f99b01e00380816f22b3898322603ba21213c2fcf8097d0735a137400002018e00001e59a5c03d4033ba0256808c44629d03c900001615a2c04b7511f0000180518000008beae093f8c04ec0a8101758150600002c450180b4d2715e0852029c7a95100001a136a581fd3e0c7196520b58814b7b913665c642be0000040245501974055300158be8390387a16aadec4581be86ae248b810652f0cb6205f0c25104080101fec70ed809e34314c822bf01a12c3af42dff81822188b6093ec16a10b92c0d0608b784133483c431735a187e82667865ce003ac103242c8830c9b0578ef60882498b03900000c248a82daf8626a0af8414764199db1e71013e252e55890782b5209148c3ff9199b0222c328af00a358672b0b3a03e6c0912809e6014b865d5231f2418fb863a160c116e6f810d0000000000a0de380d20000060654cca9e6dbe60661b198820ddc0b0a00000e712f4c28344e00000096a9d456282a51004fc0000000001de581033c40aa160bca800f60279007cdc0ca640d3f05fda44d8c0d839a651342ab2cfae843ec22853b17b173828e5042b2b817320a3da0530033e60645f170d04f895e34c840900d036c70882db8b0a1515478013205ae284c340c608155983098b29a47555e03b340bc431bb404fe25860425283e77009fde124a448de03f75705160425023f9807bd06e3cc0a80000000007007200003424e0000047183a0d0c10a6b0c38e186f6c73000003802f503d9e0b3800004bd9400000000008692654bd706ce014c4407dd03dcdac240000100)) else (if i < 6 then (if i < 5 then 0x621a20232c567fbb2e50c4686cc0c05b3010b8796fe5900cdc8901cb71910e74c52a5da8648963a9e421142f90037420c21e1565c049800009018cc00644301c821300001426abc15d80000104bda10f7813b7035160c0dec1629c480842c13229c183dc5bbb82abb03d2600a819c90824e10b03419880280b8ce450a5b28b03029de00f456401216da830698268b7b5aee339116ca806257bc3212c10212e1a9e00a684f980c014cb073b170b02eec45ba2b11e44a6aa0e5542d868070a0354e01b4dae9d0356c742e4035d129838194108c5cc380c6076003c304912c199031df03919129ae05a1e84163be260a328c373c0870000020484c34598321dc069768de8c2e3d86fc032340c2e0c45100f7405e5e0ac581799425f602ae301fe00e7d011aa04e850407e08a1c630105bd4b66762f7bc2a050594202f9e0bb3427a485de8187fe17fda042994bb47904204ea0156985b12a914e19e3589c40172b0a2dc22338131ebb9eb029ba08c902651846ce7c1bac2271ab933e09e11244c4af00de484008608b8556c822bd811080a6be272b060bd82e8017324c2799e49a01410990b6335d820f78267c0006218ce027349b7b00af4013840100f00e07043e0c090c28d20c552050561517440e00000e0713c16b400005be47401b8000008631000007aabfc15d4c17080000703346c3b200ea9833820134618bfda3700000b2b7000f3142bf281b240767c31f80000408d7304ef6c55602c19b1ae00001618c8c0810000000001e14fc81ad582f150ab84cb686a3f70407f01be405145987ab0aeb076b06e4c893b103cef011d4270f8297f089fa01532c251c093d84fdc051cec33d404c7300c065c40000000002ba1a40b42c178c00003059e5033bd05545cd80000000000ec694c02b800000000020a4782ba0000000000000038196c01ea00000000000000538c2e0ae2e03c6c2600000000000e0cbfceac030fd70143c2bdbc292802bd0000160e4d8251301fd8632880d67020ea0260c62a4ef6ae989f00451c07ea2420a8623d314800000609624328301f0006b02182801dbd09c40614bc076042fa33d8400001802b5c0cf7b0950000000fe000002856cc61f84092842500b1dc7a91dc139dc0e4bdba3514db2ec51d2b3c1aa0c092b4125901267d624600fce29b840a1f83cb80159ec0f26d6d201d3c0a500000181e828657404d6051f903231816372cf0606a0818aeb8e3e0363a082141e1a81341614720b34c114b814e3173e92e7982a4d01fadacc66c6d0987f70aec4617e6d1b5012d883c2287162214d405cc3c68e0a1f6168382bc83e1ceac58904ca82e07813130cb1e0fa6002833dc3f0c7a6231f030118668a7c60cc2d19d91bbabc00000a0d8d829ed84ece0004c343d464305b35106a8ec30eab068023db7b746c660800830 else 0x2366a026830270f09920000141f5a059970041ac04942768baf5804db403f8000063d5d00000000020115034cd00001e18879e9d1961e00000e9225c2eaf3037f60b500cb198efb05a666081818d1059e33abf90a4c0d530588ac0142f06af808dc05f02013d872aeac03bcb3278c4e00001c0cf40000084f8a02ffa126ec8a9204b98041860db7d9de183da1065c40200c2246a1ca0000000ea00000701010000196b800000482eb761a200000c5c8c85b410617ef640827588b750000063111000e706646083860866819f0d55671bf800002c307580a3864fb6104ac0f080000000000000002f6282d54007700988000038346300bac8cc680935964600000c00b903264bcaab04766f9c45eab80b960000140c640000482690000183433c2c000000702ada3100000000000e6391406e7404df046320125c101a0240f8ace00c840000303378000091a4400001062598611860a70f556d8a4f1d3e000018065a9f18c04db3041a634340000000004066c000004025f84024704a0000000002005e00000000000000303b6f602d8177200fc800008025e00003840a80000c05cc219cf44a35d9ea507f3a309081581801500001cc4c39877000002088bf51d80000083ed000000000000004b1690000024e2c0000000001184600798182c98600000004057adc600806350223c2638000000000000010d46e822c8000000001c071000001301ba00e50178800002033a31969a0fce40c8f85e8f77cb013924b302b46b00000a6b021ed2d04d7a03f0a17a65dc400000a353a0000000002a1fd00001007930229d807c11972000000000205d1263b4c12aae04080000208e8c07ddc32900000d02a20000282bb5059d415e80000098b8804b800000e162c000015b2d000018c635046aa01ba1091a830f00000713e0c19220000000000000000000000006d64b01d60000160cc00000630a7b070ea0a28823d000002085f8c24258d4f027220569e0f7742df40d31b00016f75cc2cdc02c8a033e90209c190d3b78f096600000412ea884cd62d50173e821a80000205aec0b8ad9013016b101766d4d80000504e2d0277a0df58006b0c79c0cb42144f805fcd028000000000041df0000090b8d80fd2581728d11922154042a82cd3167200001a2329d967c03889057f8ec8b81b9e8b4ff0663c198cc27cf8ccb70155c0fbf81d6400850000120d6d81de38d1a3639b01062c00d0004000752c09f7ea5a001833096d4196c025a0000090c3800000000043962003eb800d842c44809dd0a89ce9c482187810f402f3812c91cd56b00920161a04d740adb042ab05f60000218d3ab935b618500b14dd4afb1bde604f60d20c1d09052b00001a0c80e4647d611861b5a0c0443097961aa16b14022410f563593a0191c00c2d92e8814f4313a8f68ac1e280000e) else (if i < 7 then 0x3d8002045a32c3b22e87c26b4b0206080700c9840ee1856b0000060c4cc84180000000000000108923025af091103086023bfb470e19634c5040485a38ac47130a0ec9c1c8702c200001c0b7701174009020718a14fa0dcd43151fac8ea2f9400004b01cc65452c30041a7c91ef510aa90212465435638206cc2f2be00a073c61a7b9a367c140ecdb84a8790a211348ac8e3163b061dec01442eb58491606dd0c3618b39c02f500000000001d638000050a87152d4000000000760c540cde8130c067000b4f80244000039621000008c90091be000007093c60f870630e8b78e17c5b6e75465fd039cb769a42f21026350640d07e400002c623401a012c376c37b56476bb03e0afb0008bc304405f8978fa0000318ef00000a17ecc106e1856582d2644d7401d4000010547d00cc00001800f800000000181320000060207474cb4109c40f693485b02c80000000000000000000619dc00005b19e3086e61869c077788ef4698400003433fb159c20bb00000000007058ea096e8c4ba511d1a16b56173e063498b01805927053801cc824169641e080a6c14601b86948ee02934052143275060ce06ab6c45800006a2df7055216b7b015b731007031e00b9d817b13e75e054e601e6404430431207ca8208b404c9043e1b6f7ce58798297ba8950a9aa298ec06ed818580b05a14189c21c0604801ace002e8469a82741075eb6e7d41755044760a9ca54e96cf4d2126a02314071d18550060100422e52d75811101c1961912178289c6a354b60769c03a30212405db409e7a061f01d068108e0b9bcd3899cd448607f051a569ae8663200b8ea52c60a8481a120c78f61d261521017a2838600000a17dfd82e7805a50ca2808840000583a60000002050433d2029c22cd6a27eac53cd8570b15ee4323aea508000010addc27700000754aa201f4816e58233b16138081c00e8ec29740c13a0115a05b7c1c1e014700001811d500d0d0123466760000000004323100001412ec0000005fc00001a6a700000204c4f870c810eac4aff82f761748a17b5433ca862b408082159fc00c1828780a24cf887027ded4a5d024be18e15f12a13e3f022b6137f5d586561c00000b69b1c0f1601a9707a200002016e68369444eea0a540000186715064881489c2efd01b79026d60fc35862c05a88051240a42c33740c0090b0920144000030c836025a21410000043139000000f4e245cb85a7cc615f20be800000000000001c17d800001d2c7a620f40120001ea0288806f6e18b6020b63e2420c2a033580000000002ac5e000000000516122085d821ac00e6000009169c6157a00afd3d890000000003410b900679006a4e52a8a46eb537702c0000000000203cdf047cec993c5d10000091ad4558e5c096201d08b1de4e24c02053011dd6582406fe4020e035fa173b else (if i < 8 then 0x3d8071601aa8c6be581d10916c63eee0f19413d88619c62370d59dd9c8f9136d08230e2b48a5818444518d102e8fd87d781df50c63e2278c062e0635862ae4ca4982bc0036200001a0fc542e418280700d642363003b5162390415665951f22984361636740ff8ccf5354a6902d3c0b02d99a80000506bb0354289c6301c881728216c9c5de48c5fb18eb0308ac451409179733a6161c000070c1c80449003500000532a810ce48112d440dcb5688121d6014dc0aab31fd3048c6ec080000293e6f0311808bc0000200d37051e24a47c0e7901bd5600ea11940000203b8068e30b2a40000000000000120b4502780822777962000000000502380163200003d8f65232e7616b00b90c15c3356f2093a0000000000b278907f66b8bdd8faed60870880803f31805b8852505262c086428b80000d17363470dc5be5b8ca32451616e9017f981d111508c3703c0823bb577005140feac21db01810039d6c1c104053055a00338ef17bd8b40032520756000030302a062c6170e025ae8186d0364e061fc076e4692c82def608322eb1aa50682d3374d3e278cc89a08d51d02d482dda01c2583c8dac4a206e09c9050ac3a08446e76819960091c7087eec4a40000704704001f2095c04df9064700000412199933d0218e0337e3708000048c7a1031980aa084b2d8023607602012b814d909c71049a4038d9eaa28954e094c00003d16da54a300000000000000285330000184214cb3f8847c80bf4a05841dacf8177c623a630a505759831d3616ece353008a0000080028ac07cc690e0676ab4ef8199d05e4a31ff963d783947c041ebe113001ce142d807348105fb31ce0e6042a8e8ca770c3a6072941eb283d5d60aef04d000da8bd6026992000029ee780000b09e560f518267800001058dc10f000001038e00000656f9040f80000a7ccdc0430007bc00d200001607ec000003092301b7a59468178680f3d05dda1129c5fad333ac602ec67a5c03499a9ff7812ae081405ef03bd20aa5886b00291c046b37b726c822430a600c0617ff60d2dc026f82c4f08b6c14cb81bf75ad9e02dfc3153404790684304ad0c76440f05166347264a01b8814c2be3871a3a03355017063096a0c7fe363c2dcb00000d6136689b45ed3f050a605474f7680000701a300000000028050189c6d604d2077a09f0f0210205caa05d05807f808bdb5812c0d6c05d509c59098200000831178b4c00001d588e58ad20c0d00adb0f71400000842850198800b00000385a2760e5558c482751d4b9e68d84f6e3810eeb21ffac5bac88000001010da04bfa029482c5131ea000aa2c08c81cdd03cae003683148000010200107026115a4194089c14617ba02bb46f5e309d000000000000007813ea068e0144281b0f028bf0182000010024c85c9b057376cd0c24bc092381ad00000 else 0x3010b654ba80c83a0f5c0037d8129e74f4b69301823f0b32060354eef240bb201abf008660eb40000214ab000010107f02700000050673610e0129f08327a0842000000000732a560446a121c032f4b0659081a00c5c0660d8483e183d9551f0b0b6031600000a0b2c81f700000e671000000000000000b62b0000035dab38195e010900b1f5d6a98566d0628000000000401840000120944000000000013f6e07d0000068c6a303de8016c0000603ba00000ac4a018544309300000610ac00006b4e710524e16be81093b13580330806968059b064dd2bda80bbf058c505632078e00900424048653d097bc65ad4066bb933f071e2034681a9e0500c1740674d7408f3332fe0599ae33d5c61d12957059eec305009940152e05b32196644c6c007847a72212addc51c0c32e195ca15dc416fb85e770b850c0f8c2b780c0fa6461418bac2d228628d2226612bc208cb8449b3736e1a03c600b30f9e0c9e2186e80b70831ba0068e1753c2aa58675279736301302ebb02b3d05d3c24924238c8060e08aacc1845ac0d000c408d064de5c490a84233002d0164dc1c5f8138705b52c133aa54d94ba91831ecbb786015399cf1780217bb02bfe048ca097e0041dc64800625813a28649418146be0150074613d71db7d817d2099d20492c23ea31b1602726192a4161f8130d075d0171382540098a96351029aed852782496600d60a1140432333966ae9e07da831bac38843593c8cb29808402b2461f12c27eea52202b17074a81171c31248ccd8190440de581fe9a1e9a3243264f3426cf8399b10560156ec1f638340505542172c0537e817b40062017c741f1183db271f3a01a8417e0099a9251ea028a0654a0891e0010e2fdcea584b15e80b2c0000082eeb03cfe0cd4e11db199e68569c040d20dad405bc8618763f5612ba41a480202b78ea621d311bdb850ed0610000010b3878489418b7acfb34137f04a4b06394364e82d738a1266aeac65ecc21c98674000010092cc095784ad00001205978221c338f00001c00fc6cd733091f27c8000038138e35730000120dc8d8d0800009056e00000dcfc784d5302f4c1826014efb105d0bc8015a8000000000b08b1ee0571817c30d7b11c6158ab5898b0197d6a9ae06438266f844ca4734958f2813f5836f9188781624017cc018681569014625ad600b9e82abe8c6eb4ac5c32264062280815c8973b0320000061981c04))))
def p3853i12 (i : Nat) : Nat := (if i < 6 then (if i < 3 then (if i < 1 then 0x1f0200060c001b0002011900015712031a0a010f0603020001520009080a01711a070b0000000a0b01040f02080101050e1100020308070663020008020800050b1314010c01030000000c030302010e0902030513130100120f000017170100231f0b00010a0a0000040201230800342d03080d0a62031700ba08180007000003010b011e000a0010000204130b00000f000a02024e00120109160b0401180009070c0504010809000006050909080f0f0201030a03171c4307022c000a07000208003c01180518070004010c090011010a100303050312000123000300010030040e0803171302050303250304000253040602035c00020e1403270822021151001d100b13010105000024040d070c01010e0034033302140000001c0f010500110716010f000f0a1459021a030002000006000107030c04030200000d001301010e1b080900000f11140400010803221e1002200100020700030a0205121200050405890c0c0a0400010b000001045d071202040406a10a523b0a0200013405000006000d1c050e051a031819060135030f0e2b07010033020116004e09000300000700010c05011001110c0d0000070e990e0a020307240600020c030d000b0129023900140829010139012704000b020e080427040302030510030f0200081800003204140b3b06000610090100160012510346030408032502000245051208020406201d0b02140000000a0205031e090107000902031e0201130e0503052b0c04000003051c100727170202011d1a0a0b0204040f0622030000041d7904010002000720010219090163131c060001020800031708120166163201000a07260f000f2200021305120005000a000c01033c0846450414000001010c101b33080b1a001f00040010000916011b0003003513014000040720080d00970205000c0000000106032605010500010001000600050e000100010004280413002f140a0603110e0c07000a040002030000000100030804070c00060b000a07101200060602170100370301000222073608020c0f1b0d000631027704130f00001d021604040100050a174c0d0104021400130000160400004b12020d150414040a0303010d0004140c0604001b000b031859240c1a0f0a100011200107011f0b0111003d0015060001060d080000230e0b08091509012d120a082d030f3106010105070a040143050000040116011f280a060612000304010b00130008010064020005007d0316060e140800090d2104050a003f02010100003d00013e33070004000237090401010d00070d490004240a0000110558020101190103060309561b090aa3000b5806040005000305180402020e0d02120117690001031210100805161405020201020b1f000144040b050a1a0a0100000300012d3e010000050e48 else (if i < 2 then 0x440a1038704eec16a18053ca04708046071898f0553ca1bda117da12b72038d861d5d66a1c06ae9075b204fab24b100239fa75126345878ac7002c412606617e66145c0017e0385e1188f7377d048a6009b868b4a02e2e03a790300d0161763fff1493c77de614c80a8316521a727528746c715603057340462260b1c009e8667c2130610609773a0000e4702fdc0391b07b7b01e9761bd96471404ba2156b2a1b960306505ec03845177c2513ec800aeb1532203125145c3765bd112d40714404ecf433dbb1b680339d0170e001900000704388704a70633f07529142b8054bf0163701d01657bb0818505dc33289803cb777b08283b001a3c06e5a68b03034f164cb907c0b042e503435011fc0023c073a913e2704988053a304b3f06aa405cc44171600d13037f16409d433b8036720514e0591504f5e61e06147cf65ea204e8a0164f02b1c04217789ff0561714aa101ea7072db0639f00a1973f8f06af010d76054780810b086f00127e03616000791635b46366617460314627dab60bb9001a405e1f06ff7036897198f065c70288971cc806f3500d4903ce07085174b8664e34085750562f00ba405c650008377fdf005c5049d84635a74a3f0221c062a4738521186860b9203233b017a65e2d06c83023e2283c205ea6066de6650743442157d1606a270bae06ce006f61054cc0113f031be61a0e060fe63429136ca70441057c3081c10804c1581b057a013e0207b9c0292d01d4f614b4027b902b2911fe860bc811e25747fe081da68a9428569281467728a7614107f0507f7c0784c0251001ac7121357615a13f4072d797375c0843204eb7073c114f7806ea4581a1039e977fc204f4864e9661c08a811c78a830539107f88781fe2861b0079378a100876127fa618b1415290000040846e08bac026b5046b671aa675bea0817005829561616036a159e700f21055c8037e161e5700b2200dd7049bb074b207da0071e9032b406bc000003077aa0805f02c1007dc414a60b07094001151104a1081d270000010009000100230102350115100702011607080101000109110900190b0205130716061813051d02001103000a130200060f002406060000010406250e1c1704110300010c040100001a273827030000020100020111080012042608011b0100010402030f0d014714190d2213000002201118030019180c0009001904160000280600000d0a10274103000307290003002d100201011501001f104e005705070100080a20060008110903000d13041607092510040502004106001500340427140411120000000c24021205380c09021a2a291106000a01030404010904075d050448060002230a00150000011903020848001001110a001526070212213c0e0f030027120f110c28011b041a070200000806170f140a0001000a else 0x603f3f04742039b7a313900f9b20495055a5650c764e63062410567572cf30137702352767f062a22613030219f06f2b1324f041c401bd961092632002070305fb62619302445146bf06c3b60fea1450003288287e4046630350114df47740f026000000176a6c07134029100000f636d76010000000000050232a761800000972540000030816000002610b105e596164406e2802f6e0203f1580e03cdf72ce0000006210c0031f45c4f433e402ce2024220446760b0a05e40012be07d4b617700000314dc702f23780c0000000000c154f2048fa000fa607fb074d40148d12cdb75cb0005dba49192841414554138c00000f18b4a06a8000005147f411de66259d056000000a05f89143e9045a1033dd66483155ff6653100561a82f50379107870000000000c7117406b1c01cf00000514b70a84d2087a000006047e62842d0085a75de0000000000202d20000040178c08828a4a2e617300000ab289a42b3814cbf04cc5629ef3341c04aa0663842757d60f7ca61d90759c0058207946a31510166005ef301e6d13bb9042cd781bf07e7702fb40753317793059a706c500000a0132a0691601b616227008aef052800000a0652204cad07a1813cd103fa21416a60a7002fe807e6d02f17030df0801604e1914b0562032078be6047d761eb078cb633a001f34629a402dbc285b9240750248100a07148f164f620253d14d6524a8603760048e3018dc13eae60d97b3e30000036287e448a206c2b634f000000000000000012b6000000000000000103041275ea07fa00000004ea00000a768e000005113e00000a0578104ce8057dba83cb02a8e07c656697d001300000901bfc60b6f14eb207d00000006348d0397b6065000006008f103a03036a6019d608282172600000d04642082c314a5c03adca810070408060d10373715f8f01def051500000376114151c8609790623e0868c77d7808a0d01fdc1427c13fdf06ca101ce813fa274ab702d41080fd74ae8015fd06ab90698806b0e034790295a310d002209050d0000000000300907148aa602e84498703d8f02f77005470390900253664120027f003a80704a07d2e130400000b07be00000b4845a04a60000000000aa61020433165b3b61ba103164052400000506a7802b48001200467103a960541f73fa5148216470807cf0286e4031e0000000000902d797692f06502040207852774c2405b2c71a4a00f58023f613ef664ec9051696425b60669748b361f0c067d00096d14e1a11809a75300000e620700000405a0a022aa180be041e8037710004660cd4313bc645cfa1bcf70c096144904cd4400936358968a7b036ed61872000390754927fc3076b603c3214a2a0646701509a5ed5148e3038cc0125906bdf136ba03f53034b661414008e9620dca4a1b061e000008059356357c)) else (if i < 4 then 0xb00402785800000f001c807fe000008033e00000aa83b903bc1026c000000000060879e624700000e13ca000002664500000f03210059f7328b213ce86625f015e00000206442614c00000b60bd91423572f90a813a0303c0612f10c6705bbe2740a732b7634a060eb6a60a00000561afe001dc01fa00000306cd00000a0364300509045700000b159900000715cfa71b6701c6e045dc619830559e073e00000f0074a0217232c4e0779a0647461485008800000000000000000000a02c4b08b90000014340a0820f14ef20535c13c40000062490a07230000081517264ed41548c154be0574101d9562f84022760412d00bcf05ad00000000008a5e9000001155e9606000000a463800000a14e2406bf6021fe02d0302bad61c700000c0709608b67069f274af9019700000c02c840045d45d500000a0076f05bc0202bd066b72408b11caa04e7b131ad11e12619e773ca2802b404e0712b32731450268901e8e0459b11340736a70267312180000000000ba816a02a0602ea308660012d2151ef0374400cfd76ed26049e054691598e13d7307cc50661200849041ac73677789e10859901474043f8025e5046811463a61ccb00c0a625200000101830000051405560aa5123b3073310887e041bd12cb614ccf0199104d3301c86612870838d10ad308ac00000000002075d00000e018c0000000000406678014a802d130566f02f9d00c8a02d5a78480671a003f2c433f460c3b13c1a32d4b788de049ef64670000070756e13b2703d5c30fac8070000009444b00000805690000066076c61b300000107ed000000000000000901c950611a052e40134d06e8b045e1132351576e61972778c47329a063c2030a513cc70896605e6c76c2660bf005fcd07f4e14329155c50200411a47004a574c4500700000000000a04df902520000000000f007ec61a21032f6045b0000020044f21b7b63e5a0850c0116907b24065600000804a50721600000504f9903d146037f280200000f0618f03b670083c046cd772b905650014f30552f07b436027008adc04daa023a4017c2080da03b5e036c762a5804e68287151135430cfc7755c05453038fa1388b14e04018a20673267b79a4ac66514c084c603c8005f0904bbb0229a002fb74a712024600f0e046d360c9601ddb0143c284d173c8b07efd1543c281140157c71246155162054f00189333f411a390305a661fb089cc144b0016200000c0658c133d0060e8085f528018b3d35026db14c77028fa073900000d24a930556460efa0842f066a40802600b560486aa4c3707c3f0426e082f673189034d9080922806f06cf3029b416dd06112b0858204e360527d00520603c708a8a110d000003005ea00f7b034576255f2318b144fe04ed266e73055886121804c9b02dcd078900000b02c300000f0399000 else (if i < 5 then 0x68e410b5404c28783b665ef10355e607d000d8505e940420d000671844802e7771e9014a16616b581b61081990872461cb0003ff6018e138f11531c05ae1028a003966002137226c03c01065392884760cbc62193670180428806d800000f053b8638060890b084b116ebe043d0000037853e60ffeb28bc00e9c0881000002622200000271bd58049d3634917cd1010fd06d6d05b95324ec0378307d66072fe07f34137351187774560000020533002e3303ecf0301e78a7b0665c7369e00ffa14f400000c0568e03263062bc00c40000000000f141f50676f248d00000e62d52042f401055560b2013e32449561c5c058cb078623260524c390520301713620a314fd17495601eb901014047c313e8307e4c04815664200000206a4b02e4c155bd0097b012f6078d806d1066a6603dfa01c1c76616019e9029e00000827fb9a82d3002b5780fe14698101f00000e042a607b500000c15a60758010425202f4f16a686339f00e132876d03d4d7363d02e8162080a7fa00000406b7a41b686080d003b705f600000000001053fd077e9614620808e07c20000000000605d9d079e703af0779680782f04d900000d022bb000c503f0d02e591406c6175000001047d006d23083e70720a0151163b8e044de030e802e6b1894e078e87859206512117840777b0009202ccd032df07657076ec01d7a05ee003f68032e101d8907ee562ed601f6d61eb001e770353314ddf782327676476b9171e62063ec77525011550269d04db865c5c61131087bb0696e0572e04b83a498ea8015143d000002248a502eb6016f7081ad11e5914fca11dcd223fa029d662bc506a1e761230781a14ab235c410880503b200000e712e91342e02233004c2028be601fd663c00000c615d008249065900000b0016320ed0000016029b72fcd0638300ad6734ee027100000000000006d000003341400000702ef2060200000b01c4705b5d06dc1064ae088470677b05b000840508bec00a3606be6178e3040b000000000076340501f0063199107c00445c08bbd03ed16261800cd00000000003a49f1a829bb2b3c8054304e9606cba6026508b100000c18aaf1555c157c0000000000202f0502c2000006b3d4000000000090564661f2f0233615e700000d06daf084d404d2e24a6b006b161b7505a9b200ee61d3b020dd0030b76df0034c6068b8113b862d6f78a9100898712f607b82026470348600a6400eda0662213bf405a7901120669aba85a51845a012cc0853803f7e03bb6030936124c0209908a2600a476649228830000000000607a700000d73a2f0387702cb00000606b66048701229f14761051d607ade018f00000c07a8b04d4600cbb63b9f14209617f507d50000020222f0114100fc0079890626c02b6277480000000000914d1e074632311a00ef161e1312ca else 0x903dab14142011e10447f08abc04294158ec059be630ab03e3b03d3567c2462172286a3039d60297000008011a0000070479105de00000c77b400000000005035cf00fad08b8200ec77188b040a701112037a504a100000000000000040851717c722495d748ec6189b01e40000000000302e06051fd0606407ab2031cc74719a827aa49370831b0436807003088f074a8f1768fa318960c06000a0042d364f4201cdb02e12011b100b6a048900000f286b6153e2074500000a14bc91223073622640c807470000000000a08a9f0117a04944064c90610110838084ec21c8206b49141700000406f5a139a116380089e20690d023ce629b000005a1b6e0394901aa606dfea7fbe01d110011303ee802ecd14bfe069a56131e002a9070c0148cc0250d0888e06b95084f0622a806210768c5a3165a83601539f042b921d5410af981174141c0000000000b06e1f0028000006669b900f16609d0023700000a021bc30a7b04fe9731b0768100160c261200000306b58026e0628b8635120796900c2a00d0b0329000005802400086a0833f3636e08b4303ae806fa91836404bc305a8260929a81ab0512f73a76780df12879080ed004b2006c8a4b5f147bd77b2c080a86654e643f001e27086b901dc50721024984a61bc07e8101b2d071170196c0563f0055d6101f07066005f00000e1435836390079c213fbd1446d627c704cbf05e3f62a3f051c2075c00000f0215900291766e306875034a1622fb07b0c028dd60e386254901454086df03b8000009075e000006029c8384410415007e27083a5040181496d15a5fa81b370aac118c9105c1066430322504dd303bd000000000000000e776e00000f1494a12170000000000c02bdf04ab00000000000000000000d1554c163a00000b02acb002e0781c8027af06d320192260948118206006f6056101c7905cf76048a03600037ba04aeb781d302a290506a6059a02b8b134810775301fe2152300000a6249a0000b07d8101b0c085d161e86159c8073df038b674a9d60d100000105107033770149208450000000000102be00000c0400d03c41861200000603fde1461506c7000009625a000000000040091d06f96628090255b666bd676300000a041f30210c04614603a002c0f282e56120a0371b03493b48ac025810093d00346616a106b30000037757927b3407859069960404c01c07089d0000000719c05d2803dc00000f423fa07bf003c61609836553a057f8629f004f3d0579000002118a5059650213d02f5d60eec01a1103be0000000000d0037b62ec002a5407aa606c65030ba015820327014099071b70557b02784622820893a16b7c1477205a36610f00000608b320788605cd448431615317496d02c5a05a6b02bfb1443806427163710480407afc07ec7054052825424ace07c4b0))) else (if i < 9 then (if i < 7 then 0x1383f0274c03110043000000e025c70636b037df719ef1484304e4460640066e214b900000507cd6780e9b44bc04c120357274b23015d9a1b5b07438026a4001ee0041a064f2006a70543ca61ce144e164cff1697b06c4003d203287c04f1f0503f6114962c6000000608d00000b785100000000000000027168803ff00000672c800000225e1a069d514ad76204e348ae08a620586964f812831303f8202b5512144739cea7fe000002138400000000f3d61efe03244625610272a664b700a7f071874194502760000000000912f370243000002050bc05d6271e4178b5f059e2051b00000a6100000003051a07820900aae0110900eaa00f44008af049c40585e03d640476ba815710b4303aad05f1800731066cb61f77a82001456d14ba20382b079aa12043606700847c00a96061de004e50645503fe00000257d890511805ff10762361c80000090319204bf305920000020234b21bc508354108a868a530792d1486f124e226993601b276ba90813ca857f020170411c66330000000000f622e204f0003864019b860d50033bf01baf035f6054fb6274141a8507b1a034460230c01be821bd6b25a00000e145731442605224b33c00000261bc864dba1451b14f50000000000961f3f2491a11d83145d26172d007200000d07bb951b6d0523a00b1808490000046167c618d215bab03e1e003d702bbb02120029650496000003127230320776aa614b2300de508a430735000000000000000710852050c7433820886a664d000000677a115a2a012e000003026100000201a4b06a09089bd6057102269055fb0780000009025d86667530dc000000000000000910d2302d8c780af1492a009c100f60000080299e0770e739b204c4a037500000000003664e3145ac6369008a5c05fdf01fc803fb00000560e40000023344f050f2016d411d9964e40038900000b061b00000961e73707d6041dc02a6312f48068921483c065a30855000004a718e13c69281376149584b11634cb360b30715202318607c000000000000000c023d000008049700000174ef000003064875699807a500000702289664fe062d300b7000001059970098a04c7175828056f00000a10aee05c8000bd0000060889461b6000001043a2634b2619a00000801c5c06198333eb0622d0249a141bd70d600000f06d0015ec7a11d00000c0530605c370334503cf6080bb01abe6347d067b000000000000000000004065440580000009658b0000000000000000000071082000b842117b048c703a6a72e9000000000021185305ed92860614e8105aa907d1704ef000006771400000073e54643ea40dc711dfb004780057401f4208b01287840046c05712007f2a4b9a120996129d05ab204226042710106e0589714c1864f9e076d0000000000000004a49600000105c40000 else (if i < 8 then 0x2f06102d07c100000e6635e617de12dd000007030220043c14e632870205f90060a06032f017b6a106b65c6814a9414da500fbd288200000211f40a4c2f0537603cc3088ee02de602c9a05eb601a7707ae9612ef1017f0456f17b7412c0507ff300db90734e04b701596c03f1b052dd048530441903e000080f060cc014600000178990050a825e5a15bc00000e06e6d61b5c087d0000020504000007b287205a56103eb0289b002d2621a3067cb03e5e0442e05b62152f000004031d0000056017d04166073f508412282f11550c04a7d624ab736fd24b917793b0313b041346108002936b33fa764ba06e7204ff5140dc0140b76f3b01d3203e7d05dbf03b0a61624100ad02b3873bb9063fb13f3b020cf0783860d7571d0c088b060d3a13a1261a1214916287b001ef513bae18ac80152d1208f6181b0518603887031800000604af1014d251df40014d00d6e74b7e02a7b62a190193f01bcd8499213d5e03a1204b40000070406a04ad76061d035100000d070ad058bf088d000006054a0000000000a024ef0290007dfc111940521b07364016af07fdf087ca0187713f8e60be8056a606d5e066fe05483613250048474d1b068d1153726025964fd901420000090604301a6d0169108bc7147a3a4a3c00627154e002066001b806c00059031303f15a0d6215b06d407112f00b0301c2106a2305197055e063441069440790d4342300650056b614eef0245a073b704a08076a701daa280050740aa4bb12317414c6aa1e9f60f5d03a4300d920032b027e908771055d013d0e06273a81cc1520e6251d146c60738e067f2068a0003c7a710305cb804c84261db626300189916690664300000f62c5f013d00000c03a51145f7b2eb4274e276ca571d3906ee000008716a7a81f40741105e23021e0033aa0099c1426f64e85014ba01085777010505001ca000001028100000701b75022cd0286608780000000000207e1e0597406ba112e8cb341b6265161f600000d06de1169a172e39034e5736e91572a0191c1698506f7e15fb4280541453200a5a070d901ff20362c029f413d1218a8d6199b063d90325010fad78ba5028e5101e204697285a6620bc522610826c0102c283d8761d00000a152de6499406a9e60ec01203d06c1c25cb40342324b5c0587a6022705812010921340b06fc0000000000a0854b06e300000d00e210341f001f50188604fba15449612fd046ef011d0000000000d015c213b31020ea018e00000d605c104f8107316020ac0069e037080332314d2000000000000000005b4a0265802a3f0439903e2600753703a4019fb084a806a641471c08633774f808bf407db675e5312e7f7785b0675f583600000e0365400af00000000004031ab143f1600d1032c777d600000005519088c000e69602140294464eb20839501280 else 0xd548e61525561ad000005143c708b76025600000103d0b141d000003122800000000001a859f063590499c6229b015b87065a6271e009d4033f318b5f4633904f77646fc62efe2872627e7d07f59138b4030f907a61036b905496143ae024ba03efb649840359013897141256769271ade011ce766a32753d64e5a788ad0811907fc30793707253071f5730d768af2035d3070f164f7a0020a02473605aa0082d04a820484b1547e00ee803a8c0175301e080702e06f8404e580130f21bbf61ecb08740000006019f060b0000000000c0899d626800000013f06137e715751058af07f6902d6101e5063550000000000e12dbe112b0000000000c6034104432760ac128b403ac505df6a81d3019500000e10e6c065fc10dc3622c0668e802aae03e900767f05b1000000000000000862a000135000005025b8036fe18af00000f05a4402c77062800000000000121900000211ecd047b000000024a961c420176400d7d0452f02a91606900000e053e0000000000000004008b00000b0577d1501a285f71452106070000040669407e91009230513b08141614a2074cc30b4300b9d6218916ada015530346905af7069500000f0340903eb0000000000c121b6607416077e260a906ac4000e7078f00000d0526704f6808348058d00448d01ada780b213b6e071734339205f430121014b180724d6143000000000076353004de5069b201ae5020590685c07b3d013c6615b808276788c115778033827061868bae72de30686a0870f1454f769f3022d91485e6897a138e0a81eb08970000000000207975052c263bbd01b907247c215f9008780806b628840035b6176b13cb80660761f1207a3e0657e1296105faa0815d04dc121e9f07ca8072200000000001761780123304a900864a00104781a807a431043f1434501243605ba6895000009069700000a60da460236003300000e0885803bf702daa067a80354f152b000001030790380715630000000000313f7c848a000006a4b361040506ed5029ae6033ba4b6f783c965f000273907f9d65d6d075570871f022577365605ac423d2a05a1761e9f585f31478305da703566007a9018b801b5000001629c0147e0121e60822066be660ea3622bd00a2f60ba761b2e022e074c3a009a862a7a02bcd65cd20873500e5f122b7b2e4e14e7e03f49010c577c740298d0751f027f800c7a021650179a010b108aa00000a1225f0603c00c330238b61de71616e6068a0477001cbf766f66030a636ac0681f013f407449600b5146a661165063b7119c16583b2843605d4776c1400e7e7449d0730776b61815f70584b0682b02145768aa0204f64f1b0279c612a502b910678a00a8406d7903b3b041020534205fee06fb906f4e03dd615a9e00b3b06705789732714a0712c68b55745f86073707bc802)) else (if i < 11 then (if i < 10 then 0x8a900000d60e200000013cfa02ff0548a7600e624b6e155a00000124b3a032a30768800fe50844806cc913c70631d870d7762ac56441f141e0000000000605d110728000002a48e00000c00c5a6095965acf06bb1006700000c16bec06ebe666fe0100d158c104d8ca84a00000711d0662ad9320866660705c000703561cfa16f29079580383a6035303ca701d590119f0708f086e70867f603dc03c9e13eeb613e660e5104182064e0074fa2845806dd5057eb0705e0500701a0561b4a02ca2063082496d15ca206668014ca283e4a48c6761380275b05e0642e49123c012247004250059e62668052920773516b22015a82857a0002e68b22a1b7304551689fd148d0074e60277908afe610eb71ba96007870eea619f8a112e663e60122521b6a06ef00671511f31061ca085a50583664ee76180a04a370608a282d8a828004530068fba4a0a013a904243069e4077f90643e12390078a46075860028013300000f081bb04d51065d8118d261bf668a8608c081408d6352c60c1830090024f80501d0774f039c7085b000000000000000306200000000000b24c2000004262e8705c9020b960fc00000014af800f8c03fc10081907f2d026600000261aa000007287fe60d64003800000a07160007b715b2406320000030538478b6320c0042eb00000e615aa052b0000000758801eeb079f0000040172d01db5045ce05ba00000000008037cf030c504b10000000000d78a500000502dd0775d00000d02625026f102cf3609ed141a5434107025c0103a631e9121d606fef18bab00d590761e23af760ca714007021c000008043b600eb4739f602b0408912140a70138814d88018690287313f5304d0306ec700df3067e50185d152ab07e3d260bc13d400000c14cfd15004064b405b38610ad60b500000f06b2011b6218a06071a0070776257a1564c03c5a84984082141540578abe4623c61fe764e71760b8012920763d14fec06632076cf02eed089450892a047f7016e5433a3057b40434b07c9101f5830e8976cb7a856c137d060cc001e3e61f8412dae0139401b8d062ed13c8c0240811eb802b7301810000017482360f6401774043e96269003db927ff214deda60e80435f005ab0236b04b53612d064fb861a4e621c4123a2718700000c7459c1387e6225361ddb0167003e6e01f7603ba00000c069ca06724a4bc576ab1010e40613000000000085845c065b0045f1038a6083fd726a0663d20776c07e02282c0000020202c087f00832c0432e14a30000000000c08837075ae00bb7020f061928663b6007c905bed1386c06495072a870ff1a4bd20437f0005e770f00000d052fc03e4d102f60241524bb90259111ce805f7a0060000003057500000c0616113ed00000e281940207008bdf027d000004039f308038071d061d0e041900000 else 0xdc01f2008a35771000211913c55130700000466ab874865083bf01d600000000008010700000e044c00000a60d8f017f00000da82ec10f8b6015e089840544b0772702edf721b1a490300ac00000606a5b61230000000000f04d73056e20600460fd00000507e5b6125503d9404178049100000300770000000000e608ed0024214c066003e003900000810d440120542875286900000207c700000000000147430001f0095f68b6b0812316abf2488215847652dc044fc730e0b2085149a00000505b89604ae06adf0495207370000067753007c5313f96009fc2877e06f1315460746bc663f52315e00c950051226c460684304074189b77149b04549058857364a0710178059069317195561bbc2489600ca400644089f30026e2885d72b93050861183c044447832c61c3a73a4903a2204b900336013e1c0748e03b9a0144b077b62836018ae80246b04651785ae14aca0198b05bd891b6807663051e70598214cdfb01ec6244b62ab0316151647d0631304b0818613017e6621b0076ff0194473a1217c25047a7049fc7746f075f00000a01744123e8052ac05f214222961172087ea748a360a8e07dda0502306e9f035e407a2d0408f20d6a65105088a00000a082aa604000000871e83721ac61b1f081e713c27054d00000104b2d333b901f1261c950488e06db463460000000000e028300000b1460e74aa11545c00da907a0100b474303a13e3814be604f2614d70000040865a0352261681028257380114ce80778963e4d01ed9046a901c38023b8284a00000903a300000901a8614221788741495fa85bd60aba6276c739e1044b7053dd0078202aed60a981407f07f1106a3206fd907c8b1344a070e814f832637d11dde1518c0331d0869600dc000000077d000009b6360000000000203d7000002000d4608500000707bd764fa0169bb040f00000c02c6a07d98016b361958059dd05c7361a9502f3202e9b664a0000070066304c60000040749004a20000090507f20fef0729200d320190f014167847f036de07012086ab0218b1418f086c21677e0153c05d35082bf0184907320604660688a040c001b42047122868a62e5aa314820a5d61e620680ca82330674c02af4059500310a7143907b6c261b00000508298019afb3e1413e9405c1b053210525406e0318b25788e21639461b940757104148003e9648a8008d102ab805e80000022833908070000000000d04728048df04d6502fa215306664620384d60936017d460ed7118b268ac356bb400be1142a00000c02fcb10a23636657896a005336349401a9f6363d0555907acb14a46618690760d77b733121961b0c0637070ed00000aa2d3e63504650f0027c000000000040393e02a1eb08a96640f06e4461ff0000000000206685549200000c01af201ec00000303b47089551) else (if i < 12 then 0x14f6c61f5b70b6d04310081fa622db00491689ce0493b61aef01b16063480270505a2c0280503ea065128085c0063ad05dd000008072b176be0026360168d65ff16200a02adb07d3060c20000020615305c5b0492811da76246104fc126bb81524a021d613e57148770614107ea504510007d2620fc0363202d330126a00e0d1222d05bff0104361c651585d030800000503350077cb08759060500000226cba13be208a7a08488609a70333d065ee004f814fba73a62058ef0405e07999004d9a4a8331b650617807eb50061a0317db05f01429b0463804bd60655875c91071c70862d0764208b5904900000000000501b3000000012a600fd000000000051582905f5815610000000000702df0000070458f6354d70c1c06255085e0000060372b181a506c9527d8606409708ee00cc40830302f8b633bb0550618b6b7382c526a302541621d104cfd14b8e76f81010a704c01363a010cfb0036c014eb1305a07fb501a2c038e000004261c00000c04c5f040d2777b704e2000000000087374805c900000b61636089a5148bc025a000000000026571d00cec05420000001468206f04070bf03c2b0409101f810366b0131304ac4043c9146d707cea6079c6099a6511b03ab0325aa0182d062ff048bb025f8761ab6734703e8c083d70473c615c9061f10837300d271288413c37020810823f00c6e072e176063160bf603f521b5c78b43046fd0531c00e380726001df00000d41e5b6216902573655d574cbb031fb1419606790000076623e05ce5056de22c290629e08b260570902249040ee149080285264efd3272907505044ac0742d122610173c03de10369a03c7e006ee016cf422bb05097775e76196211db9049a50094e080c2044e60449d04be203926072c2138ab05b710423714e41024c10478d601a216962028c014f1d0068624b0410eb062c8006412059420576473a32a7fff652f40381f00abf04b68079d1054eb06d9c04d1960841285d601e10008ce086030692a60244024d9948ab05f380683d7312905d550284a62816607e6039a5580b80071116f9e125ad055b0050e10536307bae0154fa4b1b0861000008006f4059cc61b8a107af0856372baa11615664cd05e7226c0001d2c079b06338961119a317805c29000b001bb57381613b1b033036785c603bc0800d04c3b0180a620ec6231b056cb676de2826211e33770b01261e6058760f1b017a814c9d02d9d17d2581b840450d005b5068cd76a1413fc622b0b13d390136d0156508a1b0554b64f5161df32865a61fd4604411181e6184306b8c058f913d6e14e9a00e8a01fbe01f9e28629616cf010d86191f072716122614f0004a46079150395b011810358d016570769c1559c602fa01cc707d7b2863802cd0035afb344605d76061a00475b72bcc074a961d4c601c764d else 0xa035bd748fe14bd36188000000000000000605ca8627ff70925634d0000000000b04fd6286c435d53170e30836463a1307de967c7207a9d143b0000081215a61e3a640ae01a50000021421d013b603f9803b7ba48a46226a60e93648b501598085200000e14ed160acc604b503c116768662504006300771e05d86062ce71b4507cb16110e664487577d28594021a3083ca031500000d03b1e04820000000000661ea3286da60780000030015960164051770398614ec70825d14286121f700bf30403c082db00c1e02a4e65ae30483877a69082e760318064d20022a05d0a033ca0601376d136052713f1b019ce))))
def p3853i13 (i : Nat) : Nat := (if i < 1 then 0x65dbd40abf0140808ec07d40acd05f1929b80214e47160073c030192609146301304f584154e63054d035f81132489f613b80ab40de22ceca44c83310183c083a053e82e881b2c26f007b9b96f008d24e340525025f81d884e9712bf02c3991bc07b41219833a801f202caa73a00ec9837ce89702a183e5407bc07f501c493b49851863a107b4804741bf0065a063880368053628c30421d0d8815400450073201f900f16ee3817dc83aec4eac214101d6b0f1819ea268513be01122c46c0d2f271520e949d8245bd06ef897c800e82a360514328d1c8d0093c017002ddc07840def346601b0d83f2072e2731810e80db206af10d7091a41cb8c0dd00370345011760e376236b40780804069503b4818d59fae0c0e133f817b01e12c1e105a5830da96c624fc005e031a5829e02ba03a18053c01c04df20650035b4063e04910773badb84bdce11d08358133c196602131281818941c12042b075101806c75cc04a601683d74172d45cf0065027400012090427000001584c202f000000003c0a460dc000078154805a8c10c050b8143c0e3245c66059029800004efce773b8262496d60757737f83fe009c6d00a059c02bc012d409bc135582f580c8a0619606000000000000000007896e41ab200376048000000ce000000006504502086073502e9824b4c4714e330445040580af0c12d00a800000001804f00258000000000000d01af3a82403d4c61000053bec00006105000000001041c6ee2d1305894619fe0000b612a0369408ea0b600006096000008c74364c3896745d32c21f034081c1010c0000d67f303ebc530cc15c77bfb01b006d0278004d00003c0a3e0d4900c00003815c825df12980209404d20f4f121101df85f8008c307c53bcfc00b008030714088dc11e4c055069b02395c93a436f04fdbb149c2a200496072b973c02600000000482b68049d4e2d079d040c80be40fc000010270c1f60c22761d410440001e06eb02ca886f412b807da07f6036c981fc266c03d18027e9c1c0bc206c1810440370c3b9604302d781408e363046804038475405bf00bd80c295d260b29180b3bf48132a09e3130f0083010ea012a275d8095c002a03f1026900d3406400009270abb83c1e480efd04a080ce0001401c80252897304b404d83132b0bf7c0b46053202b7b047c4480081c77ab00e600d640bfe0720b3f0010ba019305d800000000207c000040317199caece041194011419090400080606341303020200030f21001000200b3e04050f00020421011425000004000c03473f0b1d1f0d05010010020a004a06000001290842311c1c01104d0a00100029060103020b00010a090f0e091e1d00060c040d140c1301030007000719050002361546090601000a090002102100004f00091d4544090300185200011c00002ea620030903 else 0xd02e5b01c01a1a24e00005840a41fa0000311a081e5580200000000000009846408ac60d0d16cc03b2264e011000000000e04800005002981c20016e18030068000000002073b83a2d8154058e052a828c00012c03971f0033400006ee6000000003004e84f1203300001816340c22062633ef800400004064283b7187c601f0000700229d46000000007939d44ec0000000043c04406e0000877a202a289d540b80074b03c)
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
  | 10 => lookupWord 182 623 8 17 9 4 p3853i10
  | 11 => lookupWord 988 3350 9 19 11 4 p3853i11
  | 12 => lookupWord 1321 4482 8 20 12 4 p3853i12
  | 13 => lookupWord 144 492 8 17 9 4 p3853i13
  | 14 => lookupWord 7 47 2 10 3 3 p3853i14
  | _ => fun _ => none
def basesamples : Array (Bits × Bits) := #[(0xfff000000000000000000ffffff000000000fff000000000000000000ffffff000000000fff000000000000000000ffffff000000000fff000000000000000000ffffff000000000fff000000000000000000ffffff000000000fff,0x544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544),(0xffffff000000000000000fff000000000000ffffff000000000000000fff000000000000ffffff000000000000000fff000000000000ffffff000000000000000fff000000000000ffffff000000000000000fff000000000000ffffff,0x823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823),(0xffffff000000000000000fff000000000000ffffff000000000000000fff000000000000ffffff000000000000000fff000000000000ffffff000000000000000fff000000000000ffffff000000000000000fff000000000000ffffff000,0x314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314),(0xffffff000000000000000fff000000000000ffffff000000000000000fff000000000000ffffff000000000000000fff000000000000ffffff000000000000000fff000000000000ffffff000000000000000fff000000000000ffffff000000,0x69069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069),(0xfff000000000000000000000000000000ffffff000000000000000000000000000000ffffff000000000000000000000000000000ffffff000000000000000000000000000000ffffff000000000000000000000000000000ffffff000000000,0xa92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92),(0xfff000fff000000000fff000000000000000fff000fff000000000fff000000000000000fff000fff000000000fff000000000000000fff000fff000000000fff000000000000000fff000fff000000000fff000000000000000,0x1b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b),(0xfff000000000fff000000000000000000000fff000000000fff000000000000000000000fff000000000fff000000000000000000000fff000000000fff000000000000000000000fff000000000fff000000000000000000,0xdc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc),(0xfff000fff000000000000000000000000000fff000fff000000000000000000000000000fff000fff000000000000000000000000000fff000fff000000000000000000000000000fff000fff000000000000000000000,0xce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0),(0xffffff000fff000000000000000000000000ffffff000fff000000000000000000000000ffffff000fff000000000000000000000000ffffff000fff000000000000000000000000ffffff000fff000000000000000000000000,0xf00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00)]
def basecolumns : List ColumnInfo := [(0,0,511,0,15),(16,0,495,0,13),(64,0,447,0,13),(128,0,383,0,13),(1,0,510,0,12),(2,0,509,0,12),(4,0,507,0,12),(8,0,503,0,12),(32,0,479,0,12),(256,0,255,0,12),(17,0,494,0,11),(24,0,487,0,11),(66,0,445,0,11),(80,0,431,0,11),(132,0,379,0,11),(144,0,367,0,11),(160,0,351,0,11),(192,0,319,0,11),(320,0,191,0,11),(0,16,486,9,10),(0,64,189,258,10),(0,128,347,36,10),(1,16,486,8,9),(2,64,189,256,9),(3,0,508,0,9),(4,128,347,32,9),(6,0,505,0,9),(8,16,486,1,9),(12,0,499,0,9),(18,0,493,0,9),(32,128,347,4,9),(33,0,478,0,9),(65,0,446,0,9),(96,0,415,0,9),(129,0,382,0,9),(130,0,381,0,9),(136,0,375,0,9),(256,64,189,2,9),(264,0,247,0,9),(288,0,223,0,9),(384,0,127,0,9),(0,1,460,50,8),(0,2,440,69,8),(0,4,369,138,8),(0,8,227,276,8),(0,32,94,385,8),(0,256,151,104,8),(5,0,506,0,8),(9,0,486,0,8),(9,16,486,0,8),(10,0,501,0,8),(19,0,492,0,8),(25,0,486,0,8),(36,0,347,0,8),(36,128,347,0,8),(40,0,471,0,8),(49,0,462,0,8),(67,0,444,0,8),(70,0,441,0,8),(81,0,430,0,8),(82,0,429,0,8),(134,0,377,0,8),(140,0,371,0,8),(145,0,366,0,8),(152,0,359,0,8),(161,0,350,0,8),(164,0,347,0,8),(194,0,317,0,8),(257,0,254,0,8),(258,0,189,0,8),(258,64,189,0,8),(260,0,251,0,8),(280,0,231,0,8),(322,0,189,0,8),(328,0,183,0,8),(336,0,175,0,8),(352,0,159,0,8),(416,0,95,0,8),(448,0,63,0,8),(1,2,440,68,7),(1,32,94,384,7),(1,64,188,258,7),(1,128,346,36,7),(2,1,460,48,7),(2,4,369,136,7),(2,16,484,9,7),(2,128,345,36,7),(4,2,440,65,7),(4,8,227,272,7),(4,16,482,9,7),(4,64,185,258,7),(7,0,504,0,7),(8,4,369,130,7),(8,64,181,258,7),(8,128,339,36,7),(8,256,151,96,7),(14,0,497,0,7),(16,1,460,34,7),(16,2,424,69,7),(16,4,353,138,7),(16,8,227,260,7),(16,32,78,385,7),(16,64,173,258,7),(16,128,331,36,7),(16,256,135,104,7),(21,0,490,0,7),(32,1,460,18,7),(32,16,454,9,7),(32,256,151,72,7),(35,0,476,0,7),(56,0,455,0,7),(64,1,396,50,7),(64,2,440,5,7),(64,4,305,138,7),(64,8,163,276,7),(64,16,422,9,7),(64,32,30,385,7),(64,256,151,40,7),(74,0,437,0,7),(83,0,428,0,7),(98,0,413,0,7),(128,1,332,50,7),(128,2,312,69,7),(128,4,369,10,7),(128,8,99,276,7),(128,16,358,9,7),(128,32,94,257,7),(128,64,61,258,7),(128,256,23,104,7),(133,0,378,0,7),(146,0,365,0,7),(156,0,355,0,7),(162,0,349,0,7),(177,0,334,0,7),(193,0,318,0,7),(198,0,313,0,7),(256,8,227,20,7),(256,16,230,9,7),(256,32,94,129,7),(268,0,243,0,7),(273,0,238,0,7),(289,0,222,0,7),(296,0,215,0,7),(321,0,190,0,7),(324,0,187,0,7),(344,0,167,0,7),(480,0,31,0,7),(3,16,484,8,6),(3,64,188,256,6),(3,128,344,36,6),(5,2,440,64,6),(5,16,482,8,6),(5,128,346,32,6),(6,16,480,9,6),(6,64,185,256,6),(6,128,345,32,6),(10,4,369,128,6),(10,16,484,1,6),(10,64,181,256,6),(12,16,482,1,6),(12,64,177,258,6),(12,128,339,32,6),(17,2,424,68,6),(17,32,78,384,6),(17,64,172,258,6),(17,128,330,36,6),(18,1,460,32,6),(18,4,353,136,6),(18,64,173,256,6),(20,2,424,65,6),(20,8,227,256,6),(20,128,331,32,6),(24,4,353,130,6),(24,64,165,258,6),(24,256,135,96,6),(33,16,454,8,6),(33,64,156,258,6),(33,128,346,4,6),(34,1,460,16,6),(34,128,345,4,6),(40,16,454,1,6),(40,128,339,4,6),(40,256,151,64,6),(48,1,460,2,6),(48,128,331,4,6),(48,256,135,72,6),(65,2,440,4,6),(65,16,422,8,6),(65,32,30,384,6),(66,1,396,48,6),(66,4,305,136,6),(66,128,281,36,6),(68,2,440,1,6),(68,8,163,272,6),(72,4,305,130,6),(72,16,422,1,6),(72,256,151,32,6),(80,1,396,34,6),(80,2,424,5,6),(80,8,163,260,6),(80,256,135,40,6),(96,1,396,18,6),(96,256,151,8,6),(97,0,414,0,6),(129,2,312,68,6),(129,16,358,8,6),(129,32,94,256,6),(130,1,332,48,6),(130,4,369,8,6),(130,64,61,256,6),(131,0,380,0,6),(132,2,312,65,6),(132,8,99,272,6),(132,16,354,9,6),(132,64,57,258,6),(136,4,369,2,6),(136,16,358,1,6),(136,256,23,96,6),(144,1,332,34,6),(144,4,353,10,6),(144,8,99,260,6),(144,32,78,257,6),(160,1,332,18,6),(160,16,326,9,6),(160,64,29,258,6),(160,256,23,72,6),(192,2,312,5,6),(192,4,305,10,6),(192,32,30,257,6),(192,256,23,40,6),(257,16,230,8,6),(257,32,94,128,6),(257,64,188,2,6),(260,8,227,16,6),(260,64,185,2,6),(264,16,230,1,6),(264,64,181,2,6),(272,8,227,4,6),(272,32,78,129,6),(272,64,173,2,6),(288,16,198,9,6),(304,0,207,0,6),(320,8,163,20,6),(320,16,166,9,6),(320,32,30,129,6),(320,128,27,36,6),(384,8,99,20,6),(384,32,94,1,6),(384,64,61,2,6),(392,0,119,0,6),(7,16,480,8,5),(7,128,344,32,5),(11,16,484,0,5),(13,16,482,0,5),(14,16,480,1,5),(14,64,177,256,5),(19,64,172,256,5),(21,2,424,64,5),(21,128,330,32,5),(26,4,353,128,5),(26,64,165,256,5),(27,0,484,0,5),(29,0,482,0,5),(35,64,156,256,5),(35,128,344,4,5),(37,128,346,0,5),(38,128,345,0,5),(41,16,454,0,5),(44,128,339,0,5),(49,128,330,4,5),(50,1,460,0,5),(51,0,460,0,5),(52,128,331,0,5),(56,256,135,64,5),(57,0,454,0,5),(69,2,440,0,5),(70,128,281,32,5),(71,0,440,0,5),(73,16,422,0,5),(74,4,305,128,5),(78,0,433,0,5),(81,2,424,4,5),(82,1,396,32,5),(84,2,424,1,5),(84,8,163,256,5),(88,256,135,32,5),(89,0,422,0,5),(98,1,396,16,5),(98,128,281,4,5),(104,256,151,0,5),(112,1,396,2,5),(112,256,135,8,5),(113,0,398,0,5),(133,2,312,64,5),(133,16,354,8,5),(134,64,57,256,5),(135,0,376,0,5),(137,16,358,0,5),(138,4,369,0,5),(140,16,354,1,5),(142,0,369,0,5),(145,32,78,256,5),(146,1,332,32,5),(146,4,353,8,5),(147,0,364,0,5),(148,8,99,256,5),(152,4,353,2,5),(161,16,326,8,5),(162,1,332,16,5),(162,64,29,256,5),(163,0,348,0,5),(165,0,346,0,5),(166,0,345,0,5),(168,16,326,1,5),(168,256,23,64,5),(172,0,339,0,5),(176,1,332,2,5),(180,0,331,0,5),(184,0,327,0,5),(193,2,312,4,5),(193,32,30,256,5),(194,4,305,8,5),(195,0,316,0,5),(196,2,312,1,5),(200,4,305,2,5),(200,256,23,32,5),(210,0,301,0,5),(224,256,23,8,5),(225,0,286,0,5),(259,64,188,0,5),(262,64,185,0,5),(265,16,230,0,5),(266,64,181,0,5),(268,64,177,2,5),(273,32,78,128,5),(273,64,172,2,5),(274,64,173,0,5),(276,8,227,0,5),(280,64,165,2,5),(281,0,230,0,5),(284,0,227,0,5),(289,16,198,8,5),(289,64,156,2,5),(296,16,198,1,5),(305,0,206,0,5),(321,16,166,8,5),(321,32,30,128,5),(323,0,188,0,5),(324,8,163,16,5),(324,128,27,32,5),(326,0,185,0,5),(328,16,166,1,5),(330,0,181,0,5),(332,0,179,0,5),(336,8,163,4,5),(337,0,174,0,5),(338,0,173,0,5),(352,128,27,4,5),(360,0,151,0,5),(368,0,143,0,5),(385,32,94,0,5),(386,64,61,0,5),(388,8,99,16,5),(388,64,57,2,5),(396,0,115,0,5),(400,8,99,4,5),(400,32,78,1,5),(408,0,103,0,5),(416,64,29,2,5),(417,0,94,0,5),(432,0,79,0,5),(448,32,30,1,5),(450,0,61,0,5),(456,0,55,0,5),(464,0,47,0,5),(15,0,480,0,4),(39,0,344,0,4)]
def mf : Forest := ⟨511,13,fun j => basesamples[j]?.getD (0,0),basecolumns,deadautos,actualLevels,actualIndex⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem allSparseRows : blockM mf 5 0 1 && blockM mf 6 0 2 && blockM mf 7 0 5 && blockM mf 8 0 35 && blockM mf 9 0 32 && blockM mf 10 0 48 && blockM mf 11 0 48 && blockM mf 12 0 32 && blockM mf 13 0 8 = true := by decide +kernel
end PEqualNP.Outside.L_meta_5002

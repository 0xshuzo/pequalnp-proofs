import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.Theta1739
open PEqualNP.CircuitLowerBounds
abbrev Sig := BitVec 162
def zero : Sig := 0
def one : Sig := BitVec.allOnes 162
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

def bit (i : Fin 162) (a : Sig) : Bool := a.getLsbD i.val
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




def witnessM (w : List Sig) (z : Sig) : Prop :=
  ∃ d a b, a ∈ w ∧ b ∈ w ∧ proper a ∧ proper b ∧ a ≠ b ∧ z = bin d a b

private lemma bin_repM {w a b} (d : Bool) (ha : represented w a) (hb : represented w b) :
    represented w (bin d a b) ∨ witnessM w (bin d a b) := by
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
  exact Or.inr ⟨d,a,b,ham,hbm,hap,hbp,he,rfl⟩

private lemma gate_repM (w : List Sig) (g : Gate)
    (h : g.op ∈ ({GateOp.and,GateOp.or} : Set GateOp) ∧ g.inputs.length≤2) :
    represented w (gv w g) ∨ witnessM w (gv w g) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at h
  obtain ⟨ho,hl⟩ := h
  have rz : represented w zero := Or.inr (fun h => h.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2 rfl)
  cases l with
  | nil =>
    rcases ho with rfl | rfl
    · exact Or.inl ro
    · exact Or.inl rz
  | cons i l =>
    cases l with
    | nil =>
      rcases ho with rfl | rfl
      · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).1] using Or.inl (b := witnessM w (w.getD i zero)) (get_rep w i)
      · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).2.1] using Or.inl (b := witnessM w (w.getD i zero)) (get_rep w i)
    | cons j l =>
      cases l with
      | cons a l => simp at hl
      | nil =>
        rcases ho with rfl | rfl
        · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).1] using bin_repM false (get_rep w i) (get_rep w j)
        · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).2.1] using bin_repM true (get_rep w i) (get_rep w j)

-- Remove a last computed signal from a backward derivation. A gate whose value
-- is already available, or is unused by the suffix, needs no entry in the plan.


private lemma pull_gateM {w : List Sig} {z : Sig} {k S} (h : Live target k 0 S)
    (hz : represented w z ∨ witnessM w z) (sub : ∀ a ∈ S, a ∈ w++[z]) :
    ∃ k' S', k' ≤ k+1 ∧ Live target k' 0 S' ∧ ∀ a ∈ S', a ∈ w := by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ w
    · refine ⟨k,S,by omega,h,?_⟩
      intro a ha
      have hu : a ∈ w ∨ a = z := by simpa using sub a ha
      rcases hu with hu | rfl
      · exact hu
      · exact hw
    · have hp := live_proper h z hm
      rcases hz with hr | ⟨d,a,b,ha,hb,pa,pb,hab,eq⟩
      · exact False.elim ((hr.resolve_left hw) hp)
      · subst z
        let U := S.erase (bin d a b)
        have ht : Live target k 0 (insert (bin d a b) U) := by simpa [U,Finset.insert_erase hm] using h
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
        exact ⟨_,_,Nat.le_refl _,Live.binary pa pb hab hf ht,by simpa using And.intro ha (And.intro hb hu)⟩
  · refine ⟨k,S,by omega,h,?_⟩
    intro a ha
    have hn : a ≠ z := fun hh => hm (hh ▸ ha)
    simpa [hn] using sub a ha

private lemma extractM (gs : List Gate) (w : List Sig)
    (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or} : Set GateOp) ∧ g.inputs.length≤2)
    (hp : proper target) (hout : target ∈ execute gs w) :
    ∃ k S, k ≤ gs.length ∧ Live target k 0 S ∧ ∀ a ∈ S, a ∈ w := by
  induction gs generalizing w with
  | nil => exact ⟨0,{target},by simp,Live.stop hp,by simpa [execute] using hout⟩
  | cons g gs ih =>
    obtain ⟨k,S,hk,ht,hs⟩ := ih (w++[gv w g]) (fun a ha => legal a (by simp [ha])) hout
    obtain ⟨l,T,hl,hu,hT⟩ := pull_gateM ht (gate_repM w g (legal g (by simp))) hs
    exact ⟨l,T,by simp; omega,hu,hT⟩

def kept {α : Type} (save : Bool) (x : α) (xs : List α) := if save then x::xs else xs
theorem kept_nd {α : Type} (k : Bool) (a : α) (l : List α)
    (hn : l.Nodup) (ha : a ∉ l) : (kept k a l).Nodup := by cases k <;> simp [kept,hn,ha]

theorem kept_fin (k : Bool) (a : Sig) (l : List Sig) :
    (kept k a l).toFinset = if k then insert a l.toFinset else l.toFinset := by
  cases k <;> simp [kept]

def childTwo (ws : List Sig) (a b : Sig) (d ka kb : Bool) : List Sig :=
  bin d a b :: kept ka a (kept kb b ((ws.erase a).erase b))

theorem erase_fin {l : List Sig} (h : l.Nodup) (a : Sig) : (l.erase a).toFinset = l.toFinset.erase a := by
  ext x
  simp [h.mem_erase_iff]

abbrev Row := Fin 162
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

def inputs : List Sig := [34320977784678737805174580702623245691124711423, 331769451918561132116687613458691410197145976832, 1155472918750850839440877550330872608449162641408, 1933415081870235563024837130756858697813959114752, 2951604089482371451245013945138760219540695547904, 3889710815596923617919788226093240591367626818047, 4667652978716308341503742975565966771613052698112, 5491356445548598048827932912419719345674265559040]
def target : Sig := 2417851639229258349412351
def pairs : List (Nat × Nat) := [(0, 5), (0, 6), (0, 7), (1, 4), (1, 7), (2, 4), (2, 6), (3, 4), (3, 5)]
def sample (r : Row) (i : Fin 8) := bit r (inputs.getD i.val zero)
def graph (x : Fin 8 → Bool) := decide (∃ a b : Fin 8,(a.val,b.val)∈pairs ∧ x a=true ∧ x b=true)
theorem realises (r : Row) : graph (sample r)=bit r target := by
  have c : ∀ i : Row, graph (sample i)=bit i target := by decide +kernel
  exact c r

theorem tabled (C : Circuit) (h : PEqualNP.MetaComplexity.Monotone2 C)
    (i : Nat) (r : Row) : bit r ((execute C.gates inputs).getD i zero) =
      (C.wires (List.ofFn (sample r))).getD i false := by
  have raw : List.ofFn (fun j : Fin 8 => inputs.getD j.val zero) = inputs := rfl
  have inp : List.ofFn (sample r) = inputs.map (bit r) := by
    rw [←raw,List.map_ofFn]
    rfl
  rw [←b_read,execute_bits _ _ _ (fun g hg => by
    have op : g.op=.and ∨ g.op=.or := by simpa using (h g hg).1
    rcases op with e | e <;> simp [e]),inp]
  rfl

theorem allLive (C : Circuit) (h : PEqualNP.MetaComplexity.Monotone2 C)
    (correct : ∀ x : Fin 8 → Bool, C.eval (List.ofFn x)=graph x) :
    ∃ k, k≤C.size ∧ Live target k 0 inputs.toFinset := by
  have eq : (execute C.gates inputs).getD C.output zero=target := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    exact (tabled C h C.output r).trans ((correct (sample r)).trans (realises r))
  have rep := get_rep (execute C.gates inputs) C.output
  rw [eq] at rep
  have pro : proper target := by unfold proper; decide
  obtain ⟨k,S,hk,live,sub⟩ := extractM C.gates inputs h pro (rep.resolve_right (fun n => n pro))
  refine ⟨k,hk,?_⟩
  have separate : ∀ i : Fin 8, ∃ r s : Fin 162, bit r target=true ∧ bit s target=false ∧
    ∀ j : Fin 8,j≠i → (bit r (inputs.getD j.val zero)=false ∨ bit s (inputs.getD j.val zero)=true) := by
    decide +kernel
  have all : ∀ a∈inputs,∃ j : Fin 8,inputs.getD j.val zero=a := by
    intro a ha
    obtain ⟨i,hi,eq⟩ := List.mem_iff_getElem.mp ha
    exact ⟨⟨i,by simpa [inputs] using hi⟩,(List.getD_eq_getElem inputs zero hi).trans eq⟩
  have same : S=inputs.toFinset := by
    ext a
    constructor
    · intro ha
      exact List.mem_toFinset.mpr (sub _ ha)
    · intro ha
      obtain ⟨i,hv⟩ := all a (List.mem_toFinset.mp ha)
      obtain ⟨r,s,yes,no,others⟩ := separate i
      obtain ⟨w,hw,hp,hn⟩ := mono_row_difference live rfl yes no
      obtain ⟨j,he⟩ := all w (sub w hw)
      by_cases e : j=i
      · subst j
        exact (he.symm.trans hv) ▸ hw
      · have o := others j e
        rw [he] at o
        rcases o with q | q <;> simp_all
  exact same ▸ live

def column (w : Sig) := w &&& ~~~(w >>> 81)
def mass : List Sig → Sig
  | [] => 0
  | w::ws => column w ||| mass ws

theorem in_mass {w : Sig} {ws : List Sig} {i : Nat} (hw : w∈ws)
    (h : (column w).getLsbD i=true) : (mass ws).getLsbD i=true := by
  induction ws with
  | nil => simp at hw
  | cons a l ih =>
    rcases List.mem_cons.mp hw with rfl | hm
    · simp [mass,h]
    · simp [mass,ih hm]

theorem enough {k t ws} (z : Live target k t (List.toFinset ws)) (none : t=0) :
    (mass ws &&& target)=target := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_and]
  by_cases p : target.getLsbD i=true
  · have geom : ∀ r : Fin 162,bit r target=true →
        r.val+81<162 ∧ bit (Fin.ofNat 162 (r.val+81)) target=false := by decide +kernel
    obtain ⟨hv,hn⟩ := geom ⟨i,hi⟩ p
    obtain ⟨v,hm,hp,hh⟩ := mono_row_difference (r := ⟨i,hi⟩) (s := Fin.ofNat 162 (i+81)) z none p hn
    have hn' : v.getLsbD (i+81)=false := by
      change v.getLsbD ((i+81)%162)=false at hh
      rwa [Nat.mod_eq_of_lt hv] at hh
    have col : (column v).getLsbD i=true := by
      change v.getLsbD i=true at hp
      simp [column,BitVec.getLsbD_ushiftRight,BitVec.getLsbD_not,hi,hp,hn',Nat.add_comm 81 i]
    simp [p,in_mass (List.mem_toFinset.mp hm) col]
  · simp [Bool.eq_false_iff.mpr p]

def both (f : Bool → Bool) := f false && f true
theorem both_at {f : Bool → Bool} (ok : both f=true) (v : Bool) : f v=true := by
  cases v
  · exact (Bool.and_eq_true_iff.mp ok).1
  · exact (Bool.and_eq_true_iff.mp ok).2

instance (v : Sig) : Decidable (proper v) := inferInstanceAs (Decidable (v≠zero ∧ v≠one))

def rule (visit : List Sig → Bool) (cap : Nat) (ws : List Sig) (a b : Sig) (op ia ib : Bool) :=
  let z := bin op a b
  let c := childTwo ws a b op ia ib
  if z∉ws ∧ proper z ∧ c.length≤cap then
    if mass c &&& target = target then visit c else true
  else true

def checks (visit : List Sig → Bool) (cap : Nat) (ws : List Sig) :=
  decide (target∉ws) && ws.all fun a => ws.all fun b =>
    if a<b then both fun op => both fun ia => both fun ib => rule visit cap ws a b op ia ib else true

theorem child_swap {ws : List Sig} (nd : ws.Nodup) (a b : Sig) (op ia ib : Bool) :
    (childTwo ws a b op ia ib).toFinset=(childTwo ws b a op ib ia).toFinset ∧
    (childTwo ws a b op ia ib).length=(childTwo ws b a op ib ia).length := by
  have val : ((ws.erase a).erase b).toFinset=((ws.erase b).erase a).toFinset := by
    rw [erase_fin (nd.erase _) _,erase_fin (nd.erase _) _,erase_fin nd _,erase_fin nd _]
    ext i
    simp only [Finset.mem_erase]
    tauto
  have len : ((ws.erase a).erase b).length=((ws.erase b).erase a).length := by
    rw [←List.toFinset_card_of_nodup ((nd.erase _).erase _),val,
      List.toFinset_card_of_nodup ((nd.erase _).erase _)]
  cases ia <;> cases ib <;> simp [childTwo,kept,bin_comm op a b,val,len,Finset.insert_comm]

theorem node_sound (cap : Nat) (ws : List Sig) (nd : ws.Nodup) (visit : List Sig → Bool)
    (h : checks visit cap ws=true)
    (cert : ∀ xs,visit xs=true → ImpossibleM target (cap-1) xs.toFinset) :
    ImpossibleM target cap ws.toFinset := by
  have parts := Bool.and_eq_true_iff.mp h
  apply enum_stepM nd (of_decide_eq_true parts.1)
  have ordered (a b : Sig) (am : a∈ws) (bm : b∈ws) (ab : a<b) (op ia ib : Bool)
      (fresh : bin op a b∉ws) (proper' : proper (bin op a b))
      (len : (childTwo ws a b op ia ib).length≤cap) :
      ImpossibleM target (cap-1) (childTwo ws a b op ia ib).toFinset := by
    have entry := List.all_eq_true.mp (List.all_eq_true.mp parts.2 a am) b bm
    rw [if_pos ab] at entry
    have check := both_at (both_at (both_at entry op) ia) ib
    unfold rule at check
    try dsimp only at check
    rw [if_pos ⟨fresh,proper',len⟩] at check
    split at check
    · exact cert _ check
    · intro k t le none live
      rename_i no
      exact no (enough live none)
  intro a am b bm op ia ib ne fresh hp len
  by_cases ab : a<b
  · exact ordered a b am bm ab op ia ib fresh hp len
  · have ba : b<a := by
      change b.toNat < a.toNat
      change ¬a.toNat < b.toNat at ab
      have different : a.toNat ≠ b.toNat := fun e => ne (BitVec.eq_of_toNat_eq e)
      omega
    have swap := child_swap nd a b op ia ib
    rw [swap.1]
    apply ordered b a bm am ba op ib ia
    · rwa [bin_comm op b a]
    · rwa [bin_comm op b a]
    · rwa [←swap.2]

def tree : Nat → List Sig → Bool
  | 0,ws => decide (target∉ws)
  | k+1,ws => checks (fun xs => if xs.Nodup then tree k xs else false) (k+1) ws

theorem tree_sound (k : Nat) (ws : List Sig) (nd : ws.Nodup) (h : tree k ws=true) :
    ImpossibleM target k ws.toFinset := by
  induction k generalizing ws with
  | zero =>
    intro j t le none live
    have j0 : j=0 := by omega
    subst j
    obtain ⟨_,eq,_⟩ := live
    have member : target∈ws := List.mem_toFinset.mp (eq ▸ Finset.mem_singleton_self target)
    exact (of_decide_eq_true h) member
  | succ k ih =>
    apply node_sound (k+1) ws nd _ h
    intro xs ok
    change (if xs.Nodup then tree k xs else false)=true at ok
    split at ok
    · exact ih xs ‹xs.Nodup› ok
    · contradiction
def rot0 (w : Sig) := ((w &&& 5846006549323611672814739330865132078623730171903) <<< 0)
def rot1 (w : Sig) := ((w &&& 1555878391011084515338664635942351152833240236032) >>> 19) ||| ((w &&& 3512166662061786369183603259075748558233858473984) >>> 18) ||| ((w &&& 777939195505542257669332317971175576416620118016) >>> 17) ||| ((w &&& 168359845342811717386280964096) >>> 10) ||| ((w &&& 380047592060611744394031293952) >>> 9) ||| ((w &&& 84179922671405858693140482048) >>> 8) ||| ((w &&& 22641096651881931393806540383520292864) >>> 1) ||| ((w &&& 51108946118586418661019175718681837568) <<< 0) ||| ((w &&& 11320548325940965696903270191760146432) <<< 1) ||| ((w &&& 328827822935179135520080008) <<< 8) ||| ((w &&& 742280453243382313269592371) <<< 9) ||| ((w &&& 164413911467589567760040004) <<< 10) ||| ((w &&& 5935205043835008679728182357568173037846528) <<< 17) ||| ((w &&& 13397852562186379887327588115981096489844736) <<< 18) ||| ((w &&& 2967602521917504339864091178784086518923264) <<< 19)
def rot2 (w : Sig) := ((w &&& 4189556501530594362161069899459886850244608) >>> 20) ||| ((w &&& 17063714501025649954218524278008497483808768) >>> 18) ||| ((w &&& 1047389125382648590540267474864971712561152) >>> 16) ||| ((w &&& 60847228810955011271841779023872) >>> 11) ||| ((w &&& 247825692344618847992605579149312) >>> 9) ||| ((w &&& 15211807202738752817960444755968) >>> 7) ||| ((w &&& 1098267099537236128474583621481378587272066105440) >>> 2) ||| ((w &&& 4473150374156867981599606208325198204410185908615) <<< 0) ||| ((w &&& 274566774884309032118645905370344646818016526360) <<< 2) ||| ((w &&& 118842243771396506390315974656) <<< 7) ||| ((w &&& 484034555360583687485557771776) <<< 9) ||| ((w &&& 29710560942849126597578993664) <<< 11) ||| ((w &&& 15981889730570199440616874311294124032) <<< 16) ||| ((w &&& 65092905048468208138345810997041692672) <<< 18) ||| ((w &&& 3995472432642549860154218577823531008) <<< 20)
def rot3 (w : Sig) := ((w &&& 1464356132716314837965802010298683437960696692736) >>> 39) ||| ((w &&& 366089033179078709491450502574670859490174173184) >>> 38) ||| ((w &&& 91522258294769677372862625643667714872543543296) >>> 37) ||| ((w &&& 2963033112293168304946427505213742268998597214208) >>> 36) ||| ((w &&& 732178066358157418982901005149341718980348346368) >>> 35) ||| ((w &&& 183044516589539354745725251287335429745087086592) >>> 34) ||| ((w &&& 45761129147384838686431312821833857436271771648) >>> 33) ||| ((w &&& 81288094739635210370976126664704) >>> 12) ||| ((w &&& 20322023684908802592744031666176) >>> 11) ||| ((w &&& 5080505921227200648186007916544) >>> 10) ||| ((w &&& 164481379199730620985022006298112) >>> 9) ||| ((w &&& 40644047369817605185488063332352) >>> 8) ||| ((w &&& 10161011842454401296372015833088) >>> 7) ||| ((w &&& 2540252960613600324093003958272) >>> 6) ||| ((w &&& 5586096644560433552632357176457332917272704) <<< 15) ||| ((w &&& 1396524161140108388158089294114333229318176) <<< 16) ||| ((w &&& 349131040285027097039522323528583307329544) <<< 17) ||| ((w &&& 11303117429227752266654535224237884574793987) <<< 18) ||| ((w &&& 2793048322280216776316178588228666458636352) <<< 19) ||| ((w &&& 698262080570054194079044647057166614659088) <<< 20) ||| ((w &&& 174565520142513548519761161764291653664772) <<< 21)
def rot4 (w : Sig) := ((w &&& 366090429697912573305314159916307770066383929344) >>> 21) ||| ((w &&& 732180859395825146610628319832615540132767858688) >>> 20) ||| ((w &&& 1464361718791650293221256639665231080265535717376) >>> 19) ||| ((w &&& 2963044415367479890189886481822616013974794928128) >>> 18) ||| ((w &&& 45761303712239071663164269989538471258297991168) >>> 17) ||| ((w &&& 91522607424478143326328539979076942516595982336) >>> 16) ||| ((w &&& 183045214848956286652657079958153885033191964672) >>> 15) ||| ((w &&& 39691452509587505063953186848) <<< 6) ||| ((w &&& 79382905019175010127906373696) <<< 7) ||| ((w &&& 158765810038350020255812747392) <<< 8) ||| ((w &&& 321252693749473869111371106051) <<< 9) ||| ((w &&& 4961431563698438132994148356) <<< 10) ||| ((w &&& 9922863127396876265988296712) <<< 11) ||| ((w &&& 19845726254793752531976593424) <<< 12) ||| ((w &&& 5327296576856733146872291437098041344) <<< 33) ||| ((w &&& 10654593153713466293744582874196082688) <<< 34) ||| ((w &&& 21309186307426932587489165748392165376) <<< 35) ||| ((w &&& 43117806668934183907497608819012272128) <<< 36) ||| ((w &&& 665912072107091643359036429637255168) <<< 37) ||| ((w &&& 1331824144214183286718072859274510336) <<< 38) ||| ((w &&& 2663648288428366573436145718549020672) <<< 39)
def rot5 (w : Sig) := ((w &&& 1830445165895393547457252512873354297450870865920) >>> 39) ||| ((w &&& 3786733436946095401302191136006751702851489103872) >>> 36) ||| ((w &&& 228805645736924193432156564109169287181358858240) >>> 33) ||| ((w &&& 101412048018258352119736298373120) >>> 21) ||| ((w &&& 209796174337771965947704467259392) >>> 18) ||| ((w &&& 12676506002282294014967037296640) >>> 15) ||| ((w &&& 6982594169217855340674735493277128610365440) >>> 3) ||| ((w &&& 14445241687569438236020859051717059812693504) <<< 0) ||| ((w &&& 872824271152231917584341936659641076295680) <<< 3) ||| ((w &&& 386856262276681335905976480) <<< 15) ||| ((w &&& 800308892584884513655488843) <<< 18) ||| ((w &&& 48357032784585166988247060) <<< 21) ||| ((w &&& 26636482884283665734361457185490206720) <<< 33) ||| ((w &&& 55104223966861833487960264552482865152) <<< 36) ||| ((w &&& 3329560360535458216795182148186275840) <<< 39)
def rot6 (w : Sig) := ((w &&& 5708990770823839524233146238981221980353593344) >>> 53) ||| ((w &&& 1427247692705959881058286559745305495088398336) >>> 48) ||| ((w &&& 3211307308588409732381144759426937363948896256) >>> 47) ||| ((w &&& 44601490397061246283071454992040796721512448) >>> 45) ||| ((w &&& 2923003296439877319347432536014369536773460066304) >>> 44) ||| ((w &&& 802826827147102433095286189856734340987224064) >>> 43) ||| ((w &&& 178405961588244985132285819968163186886049792) >>> 42) ||| ((w &&& 730750824109969329836858134003592384193365016576) >>> 39) ||| ((w &&& 1644189354247430992132930801508082864435071287296) >>> 38) ||| ((w &&& 22300745198530623141535727496020398360756224) >>> 37) ||| ((w &&& 22835963253436541557401816687612262006042656768) >>> 36) ||| ((w &&& 83076749736557242056487975627259904) >>> 35) ||| ((w &&& 411047338561857748033232700377020716108767821824) >>> 34) ||| ((w &&& 91343853013746166229607266750449048024170627072) >>> 33) ||| ((w &&& 20769187434139310514121993906814976) >>> 30) ||| ((w &&& 46730671726813448656774486290333696) >>> 29) ||| ((w &&& 11417981626718270778700908343806131003021328384) >>> 28) ||| ((w &&& 649037107316853453566312309587968) >>> 27) ||| ((w &&& 11682667931703362164193621572583424) >>> 25) ||| ((w &&& 2596148429267413814265249238351872) >>> 24) ||| ((w &&& 324518553658426726783156154793984) >>> 19) ||| ((w &&& 11150372599265311570767863748010199180378112) >>> 8) ||| ((w &&& 2787593149816327892691965937002549795094528) >>> 3) ||| ((w &&& 6272084587086737758556923358255737038962688) >>> 2) ||| ((w &&& 87112285931760246646623935531329681096704) <<< 0) ||| ((w &&& 1568021146771684439639230839563934259740672) <<< 2) ||| ((w &&& 348449143727040986586495742125318724386816) <<< 3) ||| ((w &&& 43556142965880123323311967765664840548352) <<< 8) ||| ((w &&& 618970019642690137449562368) <<< 19) ||| ((w &&& 154742504910672534362390592) <<< 24) ||| ((w &&& 348170636049013202315378832) <<< 25) ||| ((w &&& 4835703278458516698824706) <<< 27) ||| ((w &&& 42535296182029957989979193895333003264) <<< 28) ||| ((w &&& 87042659012253300578844708) <<< 29) ||| ((w &&& 19342813113834066795298824) <<< 30) ||| ((w &&& 10633824045507489497494798473833250816) <<< 33) ||| ((w &&& 23926104102391851369363296566124814336) <<< 34) ||| ((w &&& 2417851639229258349412353) <<< 35) ||| ((w &&& 332307001422109046796712452307289088) <<< 36) ||| ((w &&& 162259276829213363391578077396992) <<< 37) ||| ((w &&& 5981526025597962842340824141531203584) <<< 38) ||| ((w &&& 1329228005688436187186849809229156352) <<< 39) ||| ((w &&& 40564819207303340847894519349248) <<< 42) ||| ((w &&& 91270843216432516907762668535808) <<< 43) ||| ((w &&& 166153500711054523398356226153644544) <<< 44) ||| ((w &&& 1267650600228229401496703729664) <<< 45) ||| ((w &&& 22817710804108129226940667133952) <<< 47) ||| ((w &&& 5070602400912917605986814918656) <<< 48) ||| ((w &&& 633825300114114700748351864832) <<< 53)
def rot7 (w : Sig) := ((w &&& 5708990770823839524233146238981221980353593344) >>> 62) ||| ((w &&& 2854495385411919762116573119490610990176796672) >>> 58) ||| ((w &&& 356811923176489970264571639936326373772099584) >>> 56) ||| ((w &&& 1427247692705959881058286559745305495088398336) >>> 55) ||| ((w &&& 44601490397061246283071454992040796721512448) >>> 54) ||| ((w &&& 178405961588244985132285819968163186886049792) >>> 53) ||| ((w &&& 713623846352979940529143279872652747544199168) >>> 52) ||| ((w &&& 89202980794122492566142909984081593443024896) >>> 50) ||| ((w &&& 22300745198530623141535727496020398360756224) >>> 46) ||| ((w &&& 21778154559689798218898040370808047534080) >>> 35) ||| ((w &&& 10889077279844899109449020185404023767040) >>> 31) ||| ((w &&& 1361134659980612388681127523175502970880) >>> 29) ||| ((w &&& 5444538639922449554724510092702011883520) >>> 28) ||| ((w &&& 170141832497576548585140940396937871360) >>> 27) ||| ((w &&& 2923014425714972431709247836562697425727971655680) >>> 26) ||| ((w &&& 2722269319961224777362255046351005941760) >>> 25) ||| ((w &&& 340283664995153097170281880793875742720) >>> 23) ||| ((w &&& 1461507212517202550859470821111066832070110085120) >>> 22) ||| ((w &&& 182688401564650318857433852638883354008763760640) >>> 20) ||| ((w &&& 730753606343672191678523684848103886233523978240) >>> 19) ||| ((w &&& 22836050195581289857179231579860419251095470080) >>> 18) ||| ((w &&& 91344200782325159428716926319441677004381880320) >>> 17) ||| ((w &&& 365376803129300637714867705277766708017527521280) >>> 16) ||| ((w &&& 45672100391162579714358463159720838502190940160) >>> 14) ||| ((w &&& 11418025097790644928589615789930209625547735040) >>> 10) ||| ((w &&& 316912650057057350374175932416) <<< 10) ||| ((w &&& 158456325028528675187087966208) <<< 14) ||| ((w &&& 19807040628566084398385995776) <<< 16) ||| ((w &&& 79228162514264337593543983104) <<< 17) ||| ((w &&& 2475880078570760549798249472) <<< 18) ||| ((w &&& 9903520314283042199192997888) <<< 19) ||| ((w &&& 39614081257132168796771991552) <<< 20) ||| ((w &&& 4951760157141521099596498944) <<< 22) ||| ((w &&& 1237940039285380274899124736) <<< 26) ||| ((w &&& 42535295865117307932921843521157070848) <<< 28) ||| ((w &&& 21267647932558653966460921760578535424) <<< 32) ||| ((w &&& 2658455991569831745807615220072316928) <<< 34) ||| ((w &&& 10633823966279326983230460880289267712) <<< 35) ||| ((w &&& 332306998946228968225951902509039616) <<< 36) ||| ((w &&& 1329390255680715105909889325563117824) <<< 37) ||| ((w &&& 5316911983139663491615230440144633856) <<< 38) ||| ((w &&& 664613997892457936451903805018079232) <<< 40) ||| ((w &&& 81129947899616503040857763479680) <<< 41) ||| ((w &&& 10141243487452062880107220434960) <<< 43) ||| ((w &&& 166194064447064292364496380136259648) <<< 44) ||| ((w &&& 1267655435931507860013402554370) <<< 45) ||| ((w &&& 5070621743726031440053610217480) <<< 46) ||| ((w &&& 20282486974904125760214440869920) <<< 47) ||| ((w &&& 2535310871863015720026805108740) <<< 49) ||| ((w &&& 633827717965753930006701277185) <<< 53)
def rot8 (w : Sig) := ((w &&& 5709012548895322464294807894965104812773867520) >>> 53) ||| ((w &&& 1427253137223830616073701973741276203193466880) >>> 49) ||| ((w &&& 2854506274447661232147403947482552406386933760) >>> 47) ||| ((w &&& 356813284305957654018425493435319050798366720) >>> 46) ||| ((w &&& 44601660538244706752303186679414881349795840) >>> 45) ||| ((w &&& 2923716901230417751715407725345256292042636525568) >>> 44) ||| ((w &&& 89203321076489413504606373358829762699591680) >>> 43) ||| ((w &&& 178406642152978827009212746717659525399183360) >>> 41) ||| ((w &&& 730750818665451459101842718589596413485259948032) >>> 40) ||| ((w &&& 1461501637330902918203685437179192826970519896064) >>> 38) ||| ((w &&& 182710005496631987128836831240738810811989884928) >>> 37) ||| ((w &&& 22835963083295358096932584955924887921414373376) >>> 36) ||| ((w &&& 365375409332725729550921359294798206742629974016) >>> 35) ||| ((w &&& 45671926166590716193865169911849775842828746752) >>> 34) ||| ((w &&& 91343852333181432387730339823699551685657493504) >>> 32) ||| ((w &&& 11417981541647679048466292477962443960707186688) >>> 28) ||| ((w &&& 83076749736557242056487975627259904) >>> 26) ||| ((w &&& 20769187434139310514121993906814976) >>> 22) ||| ((w &&& 41538374868278621028243987813629952) >>> 20) ||| ((w &&& 5192296858534827628530498476703744) >>> 19) ||| ((w &&& 649037107316853453566312309587968) >>> 18) ||| ((w &&& 10384593717069655257060996953407488) >>> 17) ||| ((w &&& 1298074214633706907132624619175936) >>> 16) ||| ((w &&& 2596148429267413814265249238351872) >>> 14) ||| ((w &&& 324518553658426726783156154793984) >>> 10) ||| ((w &&& 11150415134561176688075796669853720337448960) <<< 10) ||| ((w &&& 2787603783640294172018949167463430084362240) <<< 14) ||| ((w &&& 5575207567280588344037898334926860168724480) <<< 16) ||| ((w &&& 696900945910073543004737291865857521090560) <<< 17) ||| ((w &&& 87112618238759192875592161483232190136320) <<< 18) ||| ((w &&& 1393801891982406981808707589813430569140480) <<< 19) ||| ((w &&& 174225236477518385751184322966464380272640) <<< 20) ||| ((w &&& 348450472955036771502368645932928760545280) <<< 22) ||| ((w &&& 40564973949808251520428881739840) <<< 23) ||| ((w &&& 81129947899616503040857763479680) <<< 25) ||| ((w &&& 43556309129520839925248143621723315503120) <<< 26) ||| ((w &&& 1267655435931507860013402554370) <<< 27) ||| ((w &&& 20282486974904125760214440869920) <<< 28) ||| ((w &&& 2535310871863015720026805108740) <<< 29) ||| ((w &&& 5070621743726031440053610217480) <<< 31) ||| ((w &&& 633827717965753930006701277185) <<< 35) ||| ((w &&& 316912650057057350374175932416) <<< 46) ||| ((w &&& 79228162514264337593543983104) <<< 50) ||| ((w &&& 158456325028528675187087966208) <<< 52) ||| ((w &&& 19807040628566084398385995776) <<< 53) ||| ((w &&& 2475880078570760549798249472) <<< 54) ||| ((w &&& 39614081257132168796771991552) <<< 55) ||| ((w &&& 4951760157141521099596498944) <<< 56) ||| ((w &&& 9903520314283042199192997888) <<< 58) ||| ((w &&& 1237940039285380274899124736) <<< 62)
def rot9 (w : Sig) := ((w &&& 5708990770823839524233146238981221980353593344) >>> 71) ||| ((w &&& 2854495385411919762116573119490610990176796672) >>> 68) ||| ((w &&& 1784059615882449851322858199681631868860497920) >>> 64) ||| ((w &&& 44601490397061246283071454992040796721512448) >>> 63) ||| ((w &&& 892029807941224925661429099840815934430248960) >>> 62) ||| ((w &&& 89202980794122492566142909984081593443024896) >>> 58) ||| ((w &&& 22300745198530623141535727496020398360756224) >>> 55) ||| ((w &&& 21778071482940061661655983882832420274176) >>> 35) ||| ((w &&& 10889035741470030830827991941416210137088) >>> 32) ||| ((w &&& 6805647338418769269267494963385131335680) >>> 28) ||| ((w &&& 170141183460469231731687374084628283392) >>> 27) ||| ((w &&& 11153775506011270691959739551979867373305856) >>> 26) ||| ((w &&& 5575186341171030653662552902249087403819008) >>> 23) ||| ((w &&& 340282366920938463463374748169256566784) >>> 22) ||| ((w &&& 3484576533823624393154961407592721941528576) >>> 19) ||| ((w &&& 87112286580797353963477389097641990684672) >>> 18) ||| ((w &&& 1742245731615947079269547781952839813693440) >>> 17) ||| ((w &&& 174224573161594707926954778195283981369344) >>> 13) ||| ((w &&& 43556143290398676981738694548820995342336) >>> 10) ||| ((w &&& 2923003274661805836407370874358385653941039792128) >>> 8) ||| ((w &&& 1461501637330902918203685437179192826970519896064) >>> 5) ||| ((w &&& 913438523331814323877303398236995516856574935040) >>> 1) ||| ((w &&& 22835963083295358096932584955924887921414373376) <<< 0) ||| ((w &&& 456719261665907161938651699118497758428287467520) <<< 1) ||| ((w &&& 45671926166590716193865169911849775842828746752) <<< 5) ||| ((w &&& 11417981541647679048466292477962443960707186688) <<< 8) ||| ((w &&& 42535296182029957989979193895333003264) <<< 10) ||| ((w &&& 21267648091014978994989596947666501632) <<< 13) ||| ((w &&& 13292280056884361871868498092291563520) <<< 17) ||| ((w &&& 332307001422109046796712452307289088) <<< 18) ||| ((w &&& 6646302287719010149297640624223178752) <<< 19) ||| ((w &&& 81129638414606681695789038698496) <<< 22) ||| ((w &&& 664614002844218093593424904614578176) <<< 23) ||| ((w &&& 166204206735063652574416094302831104) <<< 26) ||| ((w &&& 1267650600228229401496703729664) <<< 27) ||| ((w &&& 25353012004564588029934074593280) <<< 28) ||| ((w &&& 2535301200456458802993407459328) <<< 32) ||| ((w &&& 633825300114114700748351864832) <<< 35) ||| ((w &&& 618970019642690137449562368) <<< 55) ||| ((w &&& 309485009821345068724781184) <<< 58) ||| ((w &&& 193428131138340667952988240) <<< 62) ||| ((w &&& 4835703278458516698824706) <<< 63) ||| ((w &&& 96714065569170333976494120) <<< 64) ||| ((w &&& 9671406556917033397649412) <<< 68) ||| ((w &&& 2417851639229258349412353) <<< 71)
def rot10 (w : Sig) := ((w &&& 5708990770823839524233146238981221980353593344) >>> 62) ||| ((w &&& 4281743078117879643174859679235916485265195008) >>> 58) ||| ((w &&& 713623846352979940529143279872652747544199168) >>> 55) ||| ((w &&& 44601490397061246283071454992040796721512448) >>> 54) ||| ((w &&& 356833701247972910326233295920209206192373760) >>> 53) ||| ((w &&& 267608942382367477698428729952244780329074688) >>> 50) ||| ((w &&& 16333553612205046246241987912124315205632) >>> 49) ||| ((w &&& 22303467457465990649243434494005752413290496) >>> 46) ||| ((w &&& 170141183460469231731687374084628283392) >>> 45) ||| ((w &&& 1361129467683753853853498992677026267136) >>> 44) ||| ((w &&& 1020847100762815390390124244507769700352) >>> 41) ||| ((w &&& 85070591730234615865843687042314141696) >>> 37) ||| ((w &&& 2923003274661805836407370874358385653941039792128) >>> 26) ||| ((w &&& 2192252455996354377305528155768789240455779844096) >>> 22) ||| ((w &&& 365375409332725729550921359294798206742629974016) >>> 19) ||| ((w &&& 22835963083295358096932584955924887921414373376) >>> 18) ||| ((w &&& 182687704666445941525197236889455591346942246912) >>> 17) ||| ((w &&& 137015778499772148581595509735549327528486240256) >>> 14) ||| ((w &&& 62307562302417931542365981720444928) >>> 13) ||| ((w &&& 11417981541658063642183362133219504957660594176) >>> 10) ||| ((w &&& 649037107316853453566312309587968) >>> 9) ||| ((w &&& 42540488161975842760550374019633774592) >>> 8) ||| ((w &&& 3894222643901120721397873857527808) >>> 5) ||| ((w &&& 31901471898837980949691382640867803136) >>> 4) ||| ((w &&& 5317236501693321918342013596299427840) >>> 1) ||| ((w &&& 332306998946228968225951902509039616) <<< 0) ||| ((w &&& 2658618250846660959171006798149713920) <<< 1) ||| ((w &&& 1993841993677373809355711415054237696) <<< 4) ||| ((w &&& 121694457621910022543683558047744) <<< 5) ||| ((w &&& 166173781882718135783399898514194432) <<< 8) ||| ((w &&& 1267650600228229401496703729664) <<< 9) ||| ((w &&& 11150372599275452775569689583222172810215424) <<< 10) ||| ((w &&& 7605903601369376408980222377984) <<< 13) ||| ((w &&& 8362779449448983678075897811007649385283584) <<< 14) ||| ((w &&& 1393796574908797771646097083202023249412096) <<< 17) ||| ((w &&& 87112285931760246646623935531329681096704) <<< 18) ||| ((w &&& 696898287454081973172991484250637448773632) <<< 19) ||| ((w &&& 522673715590561479879743613187978086580224) <<< 22) ||| ((w &&& 43556142965880123323311967765664840548352) <<< 26) ||| ((w &&& 618970019642690137449562368) <<< 37) ||| ((w &&& 464227514732017603087171776) <<< 41) ||| ((w &&& 77371252455336267181195296) <<< 44) ||| ((w &&& 4835703278458516698824706) <<< 45) ||| ((w &&& 316951335683285018507766530064) <<< 46) ||| ((w &&& 29014219670751100192948236) <<< 49) ||| ((w &&& 237684487542793012780631949312) <<< 50) ||| ((w &&& 39616499108771398055121403905) <<< 53) ||| ((w &&& 2475880078570760549798249472) <<< 54) ||| ((w &&& 19807040628566084398385995776) <<< 55) ||| ((w &&& 14855280471424563298789496832) <<< 58) ||| ((w &&& 1237940039285380274899124736) <<< 62)
def rot11 (w : Sig) := ((w &&& 5708990770823839524233146238981221980353593344) >>> 71) ||| ((w &&& 2854495385411919762116573119490610990176796672) >>> 68) ||| ((w &&& 1427247692705959881058286559745305495088398336) >>> 66) ||| ((w &&& 713623846352979940529143279872652747544199168) >>> 64) ||| ((w &&& 44601490397061246283071454992040796721512448) >>> 63) ||| ((w &&& 356811923176489970264571639936326373772099584) >>> 62) ||| ((w &&& 178405961588244985132285819968163186886049792) >>> 60) ||| ((w &&& 89202980794122492566142909984081593443024896) >>> 58) ||| ((w &&& 22300745198530623141535727496020398360756224) >>> 55) ||| ((w &&& 21778071482940061661655983882832420274176) >>> 44) ||| ((w &&& 10889035741470030830827991941416210137088) >>> 41) ||| ((w &&& 5444517870735015415413995970708105068544) >>> 39) ||| ((w &&& 2722258935367507707706997985354052534272) >>> 37) ||| ((w &&& 170141183460469231731687374084628283392) >>> 36) ||| ((w &&& 1361129467683753853853498992677026267136) >>> 35) ||| ((w &&& 680564733841876926926749496338513133568) >>> 33) ||| ((w &&& 340282366920938463463374748169256566784) >>> 31) ||| ((w &&& 85070591730234615865843687042314141696) >>> 28) ||| ((w &&& 83076749736557242056487975627259904) >>> 17) ||| ((w &&& 41538374868278621028243987813629952) >>> 14) ||| ((w &&& 20769187434139310514121993906814976) >>> 12) ||| ((w &&& 10384593717069655257060996953407488) >>> 10) ||| ((w &&& 649037107316853453566312309587968) >>> 9) ||| ((w &&& 2923014425076945589880917484982684038159853944832) >>> 8) ||| ((w &&& 2596148429267413814265249238351872) >>> 6) ||| ((w &&& 1461507212538470198792029475077527753830688620544) >>> 5) ||| ((w &&& 1298074214633706907132624619175936) >>> 4) ||| ((w &&& 730753606269235099396014737538763876915344310272) >>> 3) ||| ((w &&& 365376803134617874216561027196108721613826949120) >>> 1) ||| ((w &&& 22836050195913596856125460548086371153604509696) <<< 0) ||| ((w &&& 182688401567308937108280513598054360806913474560) <<< 1) ||| ((w &&& 91344200783654387424501842192345484614418038784) <<< 3) ||| ((w &&& 81129638414606681695789038698496) <<< 4) ||| ((w &&& 45672100391827193712250921096172742307209019392) <<< 5) ||| ((w &&& 40564819207303340847894519349248) <<< 6) ||| ((w &&& 11418025097956818710472333925713609524061929472) <<< 8) ||| ((w &&& 1267650600228229401496703729664) <<< 9) ||| ((w &&& 10141204801825835211973629837312) <<< 10) ||| ((w &&& 5070602400912917605986814918656) <<< 12) ||| ((w &&& 2535301200456458802993407459328) <<< 14) ||| ((w &&& 633825300114114700748351864832) <<< 17) ||| ((w &&& 316912650057057350374175932416) <<< 28) ||| ((w &&& 158456325028528675187087966208) <<< 31) ||| ((w &&& 79228162514264337593543983104) <<< 33) ||| ((w &&& 39614081257132168796771991552) <<< 35) ||| ((w &&& 2475880078570760549798249472) <<< 36) ||| ((w &&& 19807040628566084398385995776) <<< 37) ||| ((w &&& 9903520314283042199192997888) <<< 39) ||| ((w &&& 4951760157141521099596498944) <<< 41) ||| ((w &&& 1237940039285380274899124736) <<< 44) ||| ((w &&& 618970019642690137449562368) <<< 55) ||| ((w &&& 309485009821345068724781184) <<< 58) ||| ((w &&& 154742504910672534362390592) <<< 60) ||| ((w &&& 77371252455336267181195296) <<< 62) ||| ((w &&& 4835703278458516698824706) <<< 63) ||| ((w &&& 38685626227668133590597648) <<< 64) ||| ((w &&& 19342813113834066795298824) <<< 66) ||| ((w &&& 9671406556917033397649412) <<< 68) ||| ((w &&& 2417851639229258349412353) <<< 71)
def phi (g : Nat) (w : Sig) := match g with
  | 0 => rot0 w
  | 1 => rot1 w
  | 2 => rot2 w
  | 3 => rot3 w
  | 4 => rot4 w
  | 5 => rot5 w
  | 6 => rot6 w
  | 7 => rot7 w
  | 8 => rot8 w
  | 9 => rot9 w
  | 10 => rot10 w
  | 11 => rot11 w
  | _ => w
def undo (g : Nat) : Nat := [0,1,2,4,3,5,6,8,7,9,10,11].getD g 0

set_option maxRecDepth 32768
set_option maxHeartbeats 0
theorem laws0 (a b : Sig) : rot0 (rot0 a) = a ∧
    (rot0 (neg a)) = neg (rot0 a) ∧
    (rot0 (a &&& b)) = ((rot0 a) &&& (rot0 b)) ∧
    (rot0 (a ||| b)) = ((rot0 a) ||| (rot0 b)) ∧
    (rot0 zero) = zero ∧ (rot0 one) = one ∧ (rot0 target) = target := by
  simp only [rot0,neg,zero,one,target] <;> bv_decide

theorem laws1 (a b : Sig) : rot1 (rot1 a) = a ∧
    (rot1 (neg a)) = neg (rot1 a) ∧
    (rot1 (a &&& b)) = ((rot1 a) &&& (rot1 b)) ∧
    (rot1 (a ||| b)) = ((rot1 a) ||| (rot1 b)) ∧
    (rot1 zero) = zero ∧ (rot1 one) = one ∧ (rot1 target) = target := by
  simp only [rot1,neg,zero,one,target] <;> bv_decide

theorem laws2 (a b : Sig) : rot2 (rot2 a) = a ∧
    (rot2 (neg a)) = neg (rot2 a) ∧
    (rot2 (a &&& b)) = ((rot2 a) &&& (rot2 b)) ∧
    (rot2 (a ||| b)) = ((rot2 a) ||| (rot2 b)) ∧
    (rot2 zero) = zero ∧ (rot2 one) = one ∧ (rot2 target) = target := by
  simp only [rot2,neg,zero,one,target] <;> bv_decide

theorem laws3 (a b : Sig) : rot4 (rot3 a) = a ∧
    (rot3 (neg a)) = neg (rot3 a) ∧
    (rot3 (a &&& b)) = ((rot3 a) &&& (rot3 b)) ∧
    (rot3 (a ||| b)) = ((rot3 a) ||| (rot3 b)) ∧
    (rot3 zero) = zero ∧ (rot3 one) = one ∧ (rot3 target) = target := by
  simp only [rot3,rot4,neg,zero,one,target] <;> bv_decide

theorem laws4 (a b : Sig) : rot3 (rot4 a) = a ∧
    (rot4 (neg a)) = neg (rot4 a) ∧
    (rot4 (a &&& b)) = ((rot4 a) &&& (rot4 b)) ∧
    (rot4 (a ||| b)) = ((rot4 a) ||| (rot4 b)) ∧
    (rot4 zero) = zero ∧ (rot4 one) = one ∧ (rot4 target) = target := by
  simp only [rot4,rot3,neg,zero,one,target] <;> bv_decide

theorem laws5 (a b : Sig) : rot5 (rot5 a) = a ∧
    (rot5 (neg a)) = neg (rot5 a) ∧
    (rot5 (a &&& b)) = ((rot5 a) &&& (rot5 b)) ∧
    (rot5 (a ||| b)) = ((rot5 a) ||| (rot5 b)) ∧
    (rot5 zero) = zero ∧ (rot5 one) = one ∧ (rot5 target) = target := by
  simp only [rot5,neg,zero,one,target] <;> bv_decide

theorem laws6 (a b : Sig) : rot6 (rot6 a) = a ∧
    (rot6 (neg a)) = neg (rot6 a) ∧
    (rot6 (a &&& b)) = ((rot6 a) &&& (rot6 b)) ∧
    (rot6 (a ||| b)) = ((rot6 a) ||| (rot6 b)) ∧
    (rot6 zero) = zero ∧ (rot6 one) = one ∧ (rot6 target) = target := by
  simp only [rot6,neg,zero,one,target] <;> bv_decide

theorem laws7 (a b : Sig) : rot8 (rot7 a) = a ∧
    (rot7 (neg a)) = neg (rot7 a) ∧
    (rot7 (a &&& b)) = ((rot7 a) &&& (rot7 b)) ∧
    (rot7 (a ||| b)) = ((rot7 a) ||| (rot7 b)) ∧
    (rot7 zero) = zero ∧ (rot7 one) = one ∧ (rot7 target) = target := by
  simp only [rot7,rot8,neg,zero,one,target] <;> bv_decide

theorem laws8 (a b : Sig) : rot7 (rot8 a) = a ∧
    (rot8 (neg a)) = neg (rot8 a) ∧
    (rot8 (a &&& b)) = ((rot8 a) &&& (rot8 b)) ∧
    (rot8 (a ||| b)) = ((rot8 a) ||| (rot8 b)) ∧
    (rot8 zero) = zero ∧ (rot8 one) = one ∧ (rot8 target) = target := by
  simp only [rot8,rot7,neg,zero,one,target] <;> bv_decide

theorem laws9 (a b : Sig) : rot9 (rot9 a) = a ∧
    (rot9 (neg a)) = neg (rot9 a) ∧
    (rot9 (a &&& b)) = ((rot9 a) &&& (rot9 b)) ∧
    (rot9 (a ||| b)) = ((rot9 a) ||| (rot9 b)) ∧
    (rot9 zero) = zero ∧ (rot9 one) = one ∧ (rot9 target) = target := by
  simp only [rot9,neg,zero,one,target] <;> bv_decide

theorem laws10 (a b : Sig) : rot10 (rot10 a) = a ∧
    (rot10 (neg a)) = neg (rot10 a) ∧
    (rot10 (a &&& b)) = ((rot10 a) &&& (rot10 b)) ∧
    (rot10 (a ||| b)) = ((rot10 a) ||| (rot10 b)) ∧
    (rot10 zero) = zero ∧ (rot10 one) = one ∧ (rot10 target) = target := by
  simp only [rot10,neg,zero,one,target] <;> bv_decide

theorem laws11 (a b : Sig) : rot11 (rot11 a) = a ∧
    (rot11 (neg a)) = neg (rot11 a) ∧
    (rot11 (a &&& b)) = ((rot11 a) &&& (rot11 b)) ∧
    (rot11 (a ||| b)) = ((rot11 a) ||| (rot11 b)) ∧
    (rot11 zero) = zero ∧ (rot11 one) = one ∧ (rot11 target) = target := by
  simp only [rot11,neg,zero,one,target] <;> bv_decide

theorem laws (g : Fin 12) (a b : Sig) : phi (undo g.val) (phi g.val a) = a ∧
    (phi g.val (neg a)) = neg (phi g.val a) ∧
    (phi g.val (a &&& b)) = ((phi g.val a) &&& (phi g.val b)) ∧
    (phi g.val (a ||| b)) = ((phi g.val a) ||| (phi g.val b)) ∧
    (phi g.val zero) = zero ∧ (phi g.val one) = one ∧ (phi g.val target) = target := by
  fin_cases g
  · exact laws0 a b
  · exact laws1 a b
  · exact laws2 a b
  · exact laws3 a b
  · exact laws4 a b
  · exact laws5 a b
  · exact laws6 a b
  · exact laws7 a b
  · exact laws8 a b
  · exact laws9 a b
  · exact laws10 a b
  · exact laws11 a b

theorem transport (g : Fin 12) {T k t S} (h : Live T k t S) :
    Live (phi g.val T) k t (S.image (phi g.val)) := by
  have inj : Function.Injective (phi g.val) := by
    intro a b eq
    exact (laws g a a).1.symm.trans ((congrArg (phi (undo g.val)) eq).trans (laws g b b).1)
  have pn (a : Sig) : phi g.val (neg a) = neg (phi g.val a) := (laws g a a).2.1
  have pb (d : Bool) (a b : Sig) : phi g.val (bin d a b) = bin d (phi g.val a) (phi g.val b) := by
    cases d
    · exact (laws g a b).2.2.1
    · exact (laws g a b).2.2.2.1
  have fz : phi g.val zero = zero := (laws g zero zero).2.2.2.2.1
  have fo : phi g.val one = one := (laws g zero zero).2.2.2.2.2.1
  have pp (v) (hp : proper v) : proper (phi g.val v) :=
    ⟨fun e => hp.1 (inj (e.trans fz.symm)),fun e => hp.2 (inj (e.trans fo.symm))⟩
  induction h using Live.ind with
  | stop hp => simpa using Live.stop (pp _ hp)
  | @unary k t U a hp hf _ ih =>
    have fresh : phi g.val (neg a) ∉ (insert a U).image (phi g.val) := by
      intro hm
      obtain ⟨v,hv,eq⟩ := Finset.mem_image.mp hm
      exact hf (inj eq ▸ hv)
    simp only [Finset.image_insert,pn] at fresh ih ⊢
    exact Live.unary (pp _ hp) fresh ih
  | @binary k t U a b d ha hb hab hf _ ih =>
    have fresh : phi g.val (bin d a b) ∉ (insert a (insert b U)).image (phi g.val) := by
      intro hm
      obtain ⟨v,hv,eq⟩ := Finset.mem_image.mp hm
      exact hf (inj eq ▸ hv)
    simp only [Finset.image_insert,pb] at fresh ih ⊢
    exact Live.binary (pp _ ha) (pp _ hb) (fun hh => hab (inj hh)) fresh ih

theorem target_transport (g : Fin 12) {k t S} (h : Live target k t S) :
    Live target k t (S.image (phi g.val)) := by
  have hm := transport g h
  rw [(laws g target target).2.2.2.2.2.2] at hm
  exact hm
structure Link where
  perm : Nat
  index : Nat
  pool : List Nat
  deriving Inhabited
structure State where
  pool : List Nat
  links : List Link
  deriving Inhabited
def dict : Array Sig := #[511,261632,262143,133955584,133956095,134217216,134217727,68585259008,68585259519,68719214592,35115652612096,35115652612607,35115786567680,35115786568191,35115786829823,35184237871104,35184237871615,35184371826688,35184371827199,35184372088831,17979214137393152,17979282722652160,9205357638345293824,9205357638345555456,9205357638345555967,9205392753997905920,9205392753998167552,9205392754132123136,9205392822583426560,9223336852482686976,9223336852482949119,9223371968269254656,4713143110832790437888,4713143110832790438399,4713161090115513090048,2413129272746388704198656,2413129272746388704199167,2417842415857221494636544,2417842415857221494637055,2417842415857290079895552,2417842433836504217288704,11440325928226245935058193567541081896996831232,11440325928226245935058193567541081896996831743,11440325928226245935058193567541081896997093375,11440325928226245935058193567541081897130786816,11440325928226245935058193567541081897131048448,11440325928226245935058193567541081897131048959,11440325928226245935058193567541081965582090240,11440325928226245935058193567541117012649443328,11440325928226245935058193567541117081234702336,11440325928226245935058193567559061111134224384,11440325928226245935058193567559061179719483392,11440325928226245935058193576746439535342125056,11440325928226245935058198280684192729787269120,22880651856452491870116387135082163793993662464,22880651856452491870116387135082163793993662975,22880651856452491870116387135082163793993924607,22880651856452491870116387135082163794127880191,22880651856452491870116387135082163862578921472,22880651856452491870116387135082198909646274560,22880651856452491870116387135082198978365489152,22880651856452491870116387135100143076716314624,22880651856452491870116391848243253909506752512,22880651856452491870118804977498021015488299519,34320977784678737805174580702623245690990493696,34320977784678737805174580702623245690990494207,34320977784678737805174580702623245691124711423,34320977784678737805174580702623245759709970431,34320977784678737805174580702623280806777323519,34320977784678737805174580702623280875362582527,34320977784678737805174580702641224905262104575,34320977784678737805174580702641224973847363583,34320977784678737805174580711828603329470005247,34320977784678737805174580711828638445122617343,34320977784678737805174585415766356523915149311,34320977784678737805174585415784335806637801471,34320977784678737805176993831895992079828910079,34320977784678737805176998545039102912619347967,45761303712904983740232774270164327587987324928,45761303712904983740232774270164327587987325439,45761303712904983740232774270164327656572583936,45761303712904983740232774270164362703639937024,45761303712904983740232774270164362772225196032,45761303712904983740235187399437073976691523584,45761303712904983740235187399437073976691524095,57201629641131229675290967837705409484984156160,57201629641131229675290967837705409484984156671,57201629641131229675290967837705409484984417792,57201629641131229675290967837705409553569415168,57201629641131229675290967837705444600636768256,57201629641131229675290967837705444600770723840,57201629641131229675290967837705444669222027264,57201629641131229675290967837723388699121549312,57201629641131229675290967846910767123329449984,57201629641131229675290967846928746337466843136,57201629641131229675290972550848520317774594048,57201629641131229675293380966978155873688354816,80082281497583721545407354972787573278977818624,80082281497583721545407354972787573279112036351,80082281497583721545407354972787573347563077632,80082281497583721545407354972787573347697295359,80082281497583721545407354972787608394764648447,91522607425809967480465548540328655175974649856,102962933354036213415523742107869737072971481088,102962933354036213415523742107869737072971481599,102962933354036213415523746821012847905761918976,102962933354036213415526155237142483461675679744,102962933354036213415526159950285594294466117632,148724237066941197155756516378034064660958806016,148724237066941197155756516378034064729544065024,148724237066941197155756516378034099776611418112,148724237066941197155756516378034099845196677120,148724237066941197155756521091195154707886637056,171604888923393689025872903513116228455086686207,183045214851619934960931097080657310351949299712,183045214851619934960931097080657310351949561344,194485540779846180895989290648198392248946130944,217366192636298672766105677783280556043074011135,228806518564524918701163871350821637939936624640,228806518564524918701163871350821637939936625151,228806518564524918701163871350821637939936886272,228806518564524918701163871350821637940070580224,228806518564524918701163871350821638008521883648,228806518564524918701163871350821673055589236736,228806518564524918701163871350821673055723192831,228806518564524918701163871350821673124174495744,228806518564524918701163871360026995578281918464,228806518564524918701166284480094384328640823296,228806518564524918701166284480094384328640823807,240246844492751164636222064918362719836933455872,240246844492751164636222064918362719836933456383,240246844492751164636222064918362719905518714880,240246844492751164636222064918362754952586067968,240246844492751164636222064918362755021171326976,240246844492751164636224478047635466225637654528,251687170420977410571280258485903801733930287104,251687170420977410571280258485903801802515546623,263127496349203656506338452053444883631061336063,263127496349203656506338452053444883699646595071,263127496349203656506338452053444918746713948159,263127496349203656506340865182717630019765534719,274567822277429902441396645620985965527923949568,274567822277429902441396645620985965527923950079,274567822277429902441396645620985965527924211200,274567822277429902441396645620986000643576561664,274567822277429902441396645630191323166269243392,274567822277429902441396645630191323166269505024,286008148205656148376454839197732405063266074624,320329125990334886181629419891150293115911274496,320329125990334886181629419891150293115911536639,320329125990334886181629419891150293184496533504,320329125990334886181629419891150328231563886592,320329125990334886181629419891150328300149145600,331769451918561132116687613458691375012908105728,331769451918561132116687613458691375012908106239,331769451918561132116687613458691375012908367360,331769451918561132116687613458691375081493364736,331769451918561132116687613458691410128560717824,331769451918561132116687613458691410197145976832,331769451918561132116687613458691410197145977343,331769451918561132116687613458691410197146238464,331769451918561132116687613458691410197146238975,331769451918561132116687613458691410197279932416,331769451918561132116687613458691410197279932927,331769451918561132116687613458691410197280194559,331769451918561132116687613458709389411283369984,331769451918561132116687613467896767835491270656,331769451918561132116687613467896767835491532288,331769451918561132116687613467914747049628663808,331769451918561132116687618171834521029936414720,331769451918561132116687618171852500244073807872,331769451918561132116690026587964156585850175488,331769451918561132116690031301107267418640613376,354650103775013623986804000593773538807035985919,354650103775013623986804000593773573991139639296,354650103775013623986804000593773573991139639807,354650103775013623986804000593773573991273594880,354650103775013623986804000593773573991273857023,354650103775013623986804000593791553205277032448,354650103775013623986804000593791553205411250175,354650103775013623986804000602978931629619150847,366090429703239869921862194161314655819551211520,366090429703239869921862194161314655819685167104,377530755631466115856920387728855702600895430656,377530755631466115856920387728855737716548042752,377530755631466115856920387738061060239240724480,400411407487918607727036774863937866395023310847,423292059344371099597153161999020030188882755584,469053363057276083337385936269184357776870080512,469053363057276083337385936269202337059592732672,469053363057276083337385940982327468609660518400,469053363057276083337388349398457104165574279168,469053363057276083337388354111600214998364717056,606337274195991034558084259079677340540832055296,606337274195991034558086672208950086929536253952,652098577908896018298317033359047025767164674048,697859881621801002038549807620006030901044576256,697859881621801002038549807620024010115181969408,697859881621801002038549807629211388539389870080,720740533478253493908666194755088194695172456447,732180859406479739843724388322629276523449810944,732180859406479739843724388322629276523583766528,777942163119384723583957162592793568995784523776,777942163119384723583957162592793604111437135872,777942163119384723583957162601998926634129817600,789382489047610969519015356160334650892781355008,960987377971004658544888259673450879347733823488,960987377971004658544888259673450879347733823999,960987377971004658544890672802723625736438022144,960987377971004658544890672802723625736438022655,972427703899230904479946453240991961244730654720,995308355755683396350062840376074125038858534911,1052509985396814626025353808213779534523708473344,1052509985396814626025353808222984892162053767168,1063950311325040871960412001781320651604943175680,1063950311325040871960412001781320651604943176191,1063950311325040871960412001781338630819080568832,1063950311325040871960412001790526009243288469504,1063950311325040871960414414910593397993647374336,1086830963181493363830528388916402815399071055871,1098271289109719609765586582483943862111695798272,1098271289109719609765586582483943862111829753856,1098271289109719609765586582483943897227348410368,1098271289109719609765586582483943897227482365952,1098271289109719609765586582483961841325833191424,1098271289109719609765586582493149219750041092096,1098271289109719609765586582493167198964178485248,1155472918750850839440877550321649271596679954432,1155472918750850839440877550330854629235025248256,1155472918750850839440877550330872608449162641408,1155472918750850839440877550330872608449162641919,1155472918750850839440877550330872608449162903040,1155472918750850839440877550330872608449162903551,1155472918750850839440877550330872608449296596992,1155472918750850839440877550330872608449296597503,1155472918750850839440877550330872608449296859135,1155472918750850839440877550330872608517747900416,1155472918750850839440877550330872608517747900927,1155472918750850839440877550330872608517881856000,1155472918750850839440877550330872643564815253504,1155472918750850839440877550330872643564815254015,1155472918750850839440877550330872643564949209088,1155472918750850839440877550330872643633400512512,1155472918750850839440877550330872643633534468096,1155472918750850839440877555044015719281953079296,1155472918750850839440877555044015719281953079807,1155472918750850839440879963460145354837866840064,1155472918750850839440879963460145354837866840575,1155472918750850839440879968173288465670657277952,1155472918750850839440879968173288465670657278463,1155472918750850839440879968173288465739242536960,1178353570607303331310993937465954772243156303872,1178353570607303331310993937465954772243156304383,1178353570607303331310993937465954772243290521599,1178353570607303331310993937465954772311875780607,1178353570607303331310993937465954807358943133695,1246995526176660806921343098871201263625137291264,1327077807674244528466750453834765500051632422912,1338518133602470774401808647411529918801111941120,1338518133602470774401808647411529918801111941631,1338518133602470774401808647411529953916764553216,1361398785458923266271925034546612082595239821311,1372839111387149512206983228104929827639619747840,1372839111387149512206983228114135220393617653760,1430040741028280741882274195942635237124603904000,1430040741028280741882274195942635272308841775104,1430040741028280741882274195942635272308975730688,1430040741028280741882274195942653251522979168256,1430040741028280741882274195951840629947187068928,1430040741028280741882274195951858573977086590976,1430040741028280741882274195951858609161324462080,1430040741028280741882274195951858609161324462591,1430040741028280741882274195951858609161324723712,1430040741028280741882274195951858609161458417664,1430040741028280741882274200665001719994114899968,1430040741028280741882276609081131355550028660736,1452921392884733233752390583077717436102969655295,1452921392884733233752390583086940772955318124544,1452921392884733233752390583086940772955452342271,1555884326238769447167914325185587137991569047552,1555884326238769447167914325185587137991569048063,1613085955879900676843205293023292547476553203712,1738929541090389382128845422275449805981863641088,1738929541090389382128845422275449805981863902720,1830452148516199349609310970806573103519492997120,1830452148516199349609313388648988960740987633664,1933415081870235563024834712914442840592464478208,1933415081870235563024837130756858697813959114752,1933415081870235563024837130756858697813959115263,1933415081870235563024837130756858697813959376384,1933415081870235563024837130756858697813959376895,1933415081870235563024837130756858697814093070336,1933415081870235563024837130756858697814093331968,1933415081870235563024837130756858697814093332479,1933415081870235563024837130756858697882544373760,1933415081870235563024837130756858697882544374271,1933415081870235563024837130756858697882678329344,1933415081870235563024837130756858732929611726848,1933415081870235563024837130756858732929611727359,1933415081870235563024837130756858732929745682432,1933415081870235563024837130756858732998196985856,1933415081870235563024837130756858732998330941440,1933415081870235563024837130756876677028096507904,1933415081870235563024837130756876677096681766912,1933415081870235563024837130766064055452304408576,1933415081870235563024837130766064055452304670208,1933415081870235563024837130766064090567957020672,1933415081870235563024837130766082034666441801728,1956295733726688054894953517891940861607952777216,1956295733726688054894953517891940861607952777727,1956295733726688054894953517891940861608086994943,1956295733726688054894953517891940861676672253951,1956295733726688054894953517891940896723739607039,1979176385583140546765069905027023025401946439680,1979176385583140546765069905027023025470531698688,1979176385583140546765069905027023060517599051776,2002057037439593038635186292162105189196074319871,2059258667080724268310474842157394741459429621760,2116460296721855497985768227837516008165908414464,2162221600434760481726001002107680335753895739392,2162221600434760481726001002107680335753895739903,2162221600434760481726001002107680370869548351488,2162221600434760481726001002107680370938133610496,2162221600434760481726001002107680370938133611007,2162221600434760481726001002107680370938267566080,2162221600434760481726001002107698350152271003648,2162221600434760481726001002116885728576478904320,2185102252291212973596117389242762499548023619583,2185102252291212973596117389242762534732127272960,2185102252291212973596117389242762534732261490687,2562633007922679089453035359129202380042942808064,2562633007922679089453035359129202380043076763648,2711357244989620286608794293358875603662226325504,2711357244989620286608794293358875603662226326015,2711357244989620286608794293358875638777878937600,2894402459841240221569722972587893755124436172800,2894402459841240221569722972597117091976918859776,2894402459841240221569725390430309612345930809344,2894402459841240221569725390439532914014175625216,2894402459841240221569725390439532949198413496320,2917283111697692713439841777574615112992541376511,2928723437625918959374897553290516965631188795392,2928723437625918959374897553290516965631188795903,2928723437625918959374897553290516965631189057024,2928723437625918959374897553290516965631322750976,2928723437625918959374897553290516965699774054400,2928723437625918959374897553290517000746841407488,2928723437625918959374897553290517000746975363072,2928723437625918959374897553290534944845326188544,2928723437625918959374897553290534944913911447552,2928723437625918959374899966419789712019892994048,2928723437625918959374899966419789712019892994559,2940163763554145205309955746858058047528185626624,2940163763554145205309955746858058047596770886143,2940163763554145205309955746858058047596904841216,2951604089482371451245013940425599129425182457856,2951604089482371451245013940425599129493767716864,2951604089482371451245013945138760219540695547904,2951604089482371451245013945138760219540695548415,2951604089482371451245013945138760219540695809536,2951604089482371451245013945138760219540695810047,2951604089482371451245013945138760219540829503488,2951604089482371451245013945138760219540829765120,2951604089482371451245013945138760219540829765631,2951604089482371451245013945138760254656348160000,2951604089482371451245013945138760254656348160511,2951604089482371451245013945138760254656482115584,2951604089482371451245013945147965577179040841728,2951604089482371451245013945147965577179041103360,2951604089482371451245013945147965612294693453824,2951604089482371451245016358268032965929399746560,2951604089482371451245016358268032965929399747071,2951604089482371451245016358268033001045052358656,2951604089482371451245016358277238323567745040384,2963044415410597697180072133993140211322313506815,2963044415410597697180072133993140211390898765823,2963044415410597697180072133993140246437831901184,2963044415410597697180072133993140246437966118911,2963044415410597697180072138706301301437692379136,2963044415410597697180072138706301301437692379647,2963044415410597697180072138706301301437826596863,2963044415410597697180072138706301336553344991232,2963044415410597697180072138706301336553479208959,2974484741338823943115130327560681293219176120320,2985925067267050189050188521128222375116172951552,2985925067267050189050188521128240389445962956800,2997365393195276434985246719408924547128682872832,3008805719123502680920304912976465629025679704064,3008805719123502680920304912976465629025813921791,3008805719123502680920304912976465664141332316160,3100328326549312648400770461516794284201654353920,3111768652477538894335828650371174275983138095104,3111768652477538894335828650371174275983138095615,3111768652477538894335831063500447022371842293760,3111768652477538894335831063500447022371842294271,3123208978405765140270886843938715357880134926336,3134649304333991386205945042219417529892644847616,3157529956190443878076061424641338603571125420032,3157529956190443878076061424641338603571125420543,3168970282118670124011119618208879685468122251264,3168970282118670124011119618208879685468122512896,3168970282118670124011119618208897664682259644416,3168970282118670124011119618218085043106467545088,3180410608046896369946177816489581857480632172544,3180410608046896369946177816489581857480632173055,3180410608046896369946177816489581892596284784640,3191850933975122615881236005343961849262115913728,3191850933975122615881236005343961849262250131455,3191850933975122615881236010057122939377629003776,3191850933975122615881236010057122939377763221503,3203291259903348861816294198911502931159112744960,3203291259903348861816294198911502931159113006592,3203291259903348861816294198920708288797458038784,3203291259903348861816294198920708288797458300416,3214731585831575107751354805608316759444813774848,3260492889544480091491585166749208375828334772224,3260492889544480091491585166749208375828334772735,3260492889544480091491585166749208375828468727808,3260492889544480091491585166749226319858234294272,3260492889544480091491585166749226355042472165376,3260492889544480091491585166758413733466680066048,3271933215472706337426643365029910512656606822400,3283373541400932583361701553884290539622328434688,3283373541400932583361701553884290539622462652415,3283373541400932583361701558597451594553603653632,3283373541400932583361701558597451629669256265728,3283373541400932583361701558597451629669256266239,3283373541400932583361701558597451629669390221312,3283373541400932583361701558597451629669390483455,3283373541400932583361701558606656987307601559552,3283373541400932583361703971726724376057960464384,3489299408109005010192749038100029978584033525760,3489299408109005010192751451238508082611083018240,3649463971104172453283563752758766250373154865152,3660904297032398699218621941613146207038985994240,3660904297032398699218621941613146207038985994751,3660904297032398699218621941613146207039119949824,3660904297032398699218621941613146242154638606336,3660904297032398699218621941613146242154772561920,3660904297032398699218624354742418953427690192896,3660904297032398699218624354742418953427690193407,3763867230386434912634148096850288725616314286080,3889710815596923617919785812963967844978922618880,3889710815596923617919785812963967844978922619391,3889710815596923617919788226093240591367626818047,3889710815596923617919788226093240591367627079679,3889710815596923617919788226093240591367760773631,3889710815596923617919788226093240591367761035263,3889710815596923617919788226093240591436212077055,3889710815596923617919788226093240591436346032639,3889710815596923617919788226093240626483279430143,3889710815596923617919788226093240626483413385727,3889710815596923617919788226093240626551864689151,3889710815596923617919788226093240626551998644735,3889710815596923617919788226093258570581764211199,3889710815596923617919788226093258570650349470207,3889710815596923617919788226102445949005972111871,3889710815596923617919788226102445949005972373503,3889710815596923617919788226102445984121624723967,3889710815596923617919788230806383702200417255935,3889710815596923617919788230806401681483139908095,3901151141525149863854846419660781673264623649279,3901151141525149863854846419660781673333208908287,3901151141525149863854846419660781708380276261375,3912591467453376109789904613228322755161620480511,3912591467453376109789904617941483845277133570559,3912591467453376109789904617941483880392786182655,3924031793381602355724962806795863837058617311743,3924031793381602355724962806795863837058751528959,3924031793381602355724962806795863837127336787967,3924031793381602355724962806795863872174404141055,3924031793381602355724962811509024927174130401791,3924031793381602355724962811509024927174264619007,3981233423022733585400253774633569246543601467903,3992673748950959831335309555071837582051894099968,3992673748950959831335309555071837617236131971072,3992673748950959831335309555071837617236131971583,3992673748950959831335309555071837617236265926656,3992673748950959831335311968201110328440598299135,3992673748950959831335311968201110363556250911231,3992673748950959831335311968201110363624836170239,3992673748950959831335311968201110363624836431871,3992673748950959831335311968201110363624970125823,3992673748950959831335311968201128342838973563391,3992673748950959831335311968210315721263181464063,4015554400807412323205425942206919781030259851263,4015554400807412323205425946920080871077053464576,4015554400807412323205428355336192527418829832703,4015554400807412323205428355336192527418964049919,4015554400807412323205428360049353617465757663743,4015554400807412323205428360049353617465891880959,4026994726735638569140484135774460862858537205760,4026994726735638569140484135774460862858671161344,4107077008233222290685891490756471737874479316991,4107077008233222290685891495469614848775720796160,4107077008233222290685891495469614848775720796671,4107077008233222290685891495469614848775855013887,4107077008233222290685891495469614883891373408256,4267241571228389733776708613831319630821004935679,4267241571228389733776708613831319665936657547775,4290122223084842225646822592550272159127670095872,4358764178654199701257171749233152237940030570496,4358764178654199701257171749242375574792513257472,4358764178654199701257174162362424949144496898559,4358764178654199701257174162362424984328734769663,4358764178654199701257174162371648321181217456639,4381644830510652193127288141081395491780952064000,4381644830510652193127288141090600849419297357824,4381644830510652193127288141090600849419431575551,4381644830510652193127290549506730484975345336319,4381644830510652193127290554219873595808001556991,4393085156438878439062346329935775448446783193088,4393085156438878439062346329935775448446783193599,4393085156438878439062346329944980806085128486912,4393085156438878439062346329944980806085128748544,4450286786080009668737637297773480857931767349248,4450286786080009668737637297782686250685765255168,4667652978716308341503742975556761413974707142656,4667652978716308341503742975556761413974707404288,4667652978716308341503742975565966771613052698112,4667652978716308341503742975565966771613052698623,4667652978716308341503742975565966771613186653696,4667652978716308341503742975565966771613186654207,4667652978716308341503742975565966771681637957120,4667652978716308341503742975565966771681637957631,4667652978716308341503742975565966771681771912704,4667652978716308341503742975565966806728705310208,4667652978716308341503742975565966806728705310719,4667652978716308341503742975565966806728839265792,4667652978716308341503742975565966806728839266303,4667652978716308341503742975565966806797290569216,4667652978716308341503742975565966806797424524800,4667652978716308341503742975565984750827190091264,4667652978716308341503742975565984750895775350272,4667652978716308341503742975565984785942842703360,4667652978716308341503742980279109882445843136000,4667652978716308341503742980279109882514428395008,4667652978716308341503742980279109917561495748096,4667652978716308341503745388695239518001756896768,4667652978716308341503745388695239518001756897279,4667652978716308341503745388695239553117409508864,4667652978716308341503745393408382628834547334656,4667652978716308341503745393408382628834547335167,4679093304644534587438801169133507853510049529344,4679093304644534587438801169133507853510049529855,4679093304644534587438801169133507853578634788352,4679093304644534587438801169133507888625702141440,4690533630572760833373859362701048935407046360576,4690533630572760833373859362701048935407046361087,4690533630572760833373859367414210025522559450624,4690533630572760833373859367414210025522559451135,4690533630572760833373859367414210060638212062720,4701973956500987079308917556268590017304043191808,4701973956500987079308917556268590017304177147903,4701973956500987079308917556268590017372762406911,4701973956500987079308917556268590052419829759999,4701973956500987079308917560981751107419690237951,4713414282429213325243975749836131099201040023040,4713414282429213325243975749836131099201040023551,4713414282429213325243975749836131134316692635136,4724854608357439571179033943403672181098036854272,4724854608357439571179033943403672181166622113280,4724854608357439571179033943403672216213689466368,4724854608357439571179033943403672216282274725376,4724854608357439571179033943403672216282274725887,4724854608357439571179033943403672216282408680960,4724854608357439571179033943403690195496412118528,4747735260213892063049150330538754344892164472831,4747735260213892063049150330538754380076268387840,4747735260213892063049150330538754380076402343935,4747735260213892063049150335251915435007543606784,4747735260213892063049150335251915470123196218880,4747735260213892063049150335251915470123330174975,4885019171352607014269851071182457827239275790335,4885019171352607014269851071182475806521864224768,4885019171352607014269851071182475806521864225279,4885019171352607014269851071182475806521998442495,4885019171352607014269851071182475841637516836864,4885019171352607014269851071191681164160209518592,4930780475065511998010083845452640134109851549696,5045183734347774457360665781137238331435442765312,5045183734347774457360665781137238331435442765823,5090945038060679441100896137564986836986173324800,5090945038060679441100898555398197336569322405888,5090945038060679441100898555407402659023430090240,5113825689917131932971014942533297444461800849408,5113825689917131932971014942533297479577453461504,5113825689917131932971014942533297479577587679231,5445595141835693065087702551288033086997541421055,5457035467763919311022758331726301457690071924224,5457035467763919311022760744855574168894538252287,5457035467763919311022760744855574204078776123391,5468475793692145556957818943136276340907048173567,5479916119620371802892877131990656367872903741439,5491356445548598048827932912419719345674265559040,5491356445548598048827932912419719345674265559551,5491356445548598048827932912419719345674265820672,5491356445548598048827932912419719345674265821183,5491356445548598048827932912419719345742850818048,5491356445548598048827932912419719345742850818559,5491356445548598048827932912419737324888402952192,5491356445548598048827932912419737324888402952703,5491356445548598048827932912419737324888403213824,5491356445548598048827932912419737324956988211200,5491356445548598048827932912428924703312610852864,5491356445548598048827932912428924703312610853375,5491356445548598048827932912428924703312611114496,5491356445548598048827932912428924703381196111872,5491356445548598048827932912428942682526748246016,5491356445548598048827932917132862456507055996928,5491356445548598048827932917132862456507055997439,5491356445548598048827932917132862456575641255936,5491356445548598048827932917132880435721193390080,5491356445548598048827932917132880435789778649088,5491356445548598048827932917142067814145401290752,5491356445548598048827935325548992092062969757696,5491356445548598048827935325548992092062969758207,5491356445548598048827935325558197449701315051520,5491356445548598048827935330262135202895760195584,5491356445548598048827935330262135202895760196095,5502796771476824294762991105987260427571262390272,5502796771476824294762991105987260427571262390783,5502796771476824294762991105987260427639847649280,5514237097405050540698049299554801509468259221504,5514237097405050540698049299554801509468259222015,5514237097405050540698049304267962599583772311552,5514237097405050540698049304267962599583772312063,5514237097405050540698049304277167957222117605376,5525677423333276786633107493122342591365256052736,5525677423333276786633107493122342591365256314879,5525677423333276786633107493122342591433841573887,5525677423333276786633107493122360570579393708031,5525677423333276786633107493131547949003601608703,5525677423333276786633107497835503681480769404927,5537117749261503032568165686689883673262252883968,5548558075189729278503223880257424755159249715200,5548558075189729278503223880257424755227834974208,5548558075189729278503223880266648092011732402176,5548558075189729278503223880266648092011732402687,5548558075189729278503223880266648092080317661184,5571438727046181770373340267392506918953243639807,5571438727046181770373340267401730255805726326783,5571438727046181770373340272105668009068756467712,5571438727046181770373340272114873366707101761536,5594319378902634262243459072370004939968731676672,5594319378902634262243459072370004939968731677183,5594319378902634262243459072370004940037316935680,5594319378902634262243459072370022919182869069824,5594319378902634262243459072379210297607076970496,5617200030759086754113575459505087103762725601279,5617200030759086754113575459505105083045447991296,5640080682615539245983689428797753410335224365056,5640080682615539245983691846649392604409201688576,5674401660400217983788864009500376656026214858752,5720162964113122967529096783770540983614202183680,5720162964113122967529096783770540983614202184191,5720162964113122967529099196899813730002906382847,5720162964113122967529099196899813730071491641855,5720162964113122967529099196899831709217043775999,5720162964113122967529099196909019087641251676671,5731603290041349213464154977338082065511199014912,5731603290041349213464157390476578148752385901055,5743043615969575459399215588748056983912413135359,5754483941897801705334271364473164229305192939519,5765924267826027951269329558040705311202189508608,5765924267826027951269329558049910668840535064064,5765924267826027951269329558049910668840535064575,5765924267826027951269329558049910668909120323072,5765924267826027951269329558049928648054672457216,5788804919682480443139445949898153922750041816576,5811685571538932935009562332310869638790176833536,5811685571538932935009564745449347742817226588159,5823125897467159180944620525878410685571387097088,5823125897467159180944620525878410720687173664768,5823125897467159180944620525878410720755758923776,5823125897467159180944620525878410720755758924287,5823125897467159180944620525878428699969896316928,5823125897467159180944620525887616078325519220224,5823125897467159180944620525887616078393970523648,5823125897467159180944620525887616078394104217600,5823125897467159180944620525887616078394104479232,5823125897467159180944620525887634022423870045696,5823125897467159180944620525887634057539522657792,5823125897467159180944620525887634057539656613376,5823125897467159180944620525887634057608107916800,5823125897467159180944620525887634057608241610752,5823125897467159180944620525887634057608241872384,5823125897467159180944622939007683467144463122943,5823125897467159180944622939016888824782808678399,5823125897467159180944622939016906803996812115967,5823125897467159180944622939016906803996945809919,5823125897467159180944622943720826542792881734143,5823125897467159180944622943720826577908668301312,5823125897467159180944622943720826577908668301823,5823125897467159180944622943720826577977119604736,5823125897467159180944622943720826577977119605247,5823125897467159180944622943720826577977253560320,5823125897467159180944622943720826577977253560831,5823125897467159180944622943730031935615465160703,5823125897467159180944622943730031935615599115776,5823125897467159180944622943730049914829602292223,5823125897467159180944622943730049914829602553344,5823125897467159180944622943730049914829736247296,5846006549323611672814736913013492884549752586240,5846006549323611672814736913013492884549752848383,5846006549323611672814736913022698242188098142207,5846006549323611672814736913022716221402235535359,5846006549323611672814736917726653974596680417280,5846006549323611672814736917726653974596680679423,5846006549323611672814736917735859332234892017152,5846006549323611672814736917735859332235025711104,5846006549323611672814736917735859332235025972736,5846006549323611672814739326142765630938457047039,5846006549323611672814739326151970988508217081855,5846006549323611672814739330855908741771247484927,5846006549323611672814739330865132078623595954176]
def ini : List Nat := [66,158,229,287,357,444,519,594]
def layer0 : Array State := #[]
def layer1 : Array State := #[]
def layer2 : Array State := #[]
def layer3 : Array State := #[]
def layer4 : Array State := #[]
def row5_0 : State := ⟨[27,66,270,287,357,444],[]⟩
def row5_1 : State := ⟨[19,229,287,357,444,519],[]⟩
def row5_2 : State := ⟨[66,158,249,371,519,594],[]⟩
def row5_3 : State := ⟨[66,158,249,357,542,594],[]⟩
def row5_4 : State := ⟨[66,158,248,357,542,594],[]⟩
def row5_5 : State := ⟨[66,165,305,368,444,594],[]⟩
def row5_6 : State := ⟨[66,158,248,370,520,594],[]⟩
def row5_7 : State := ⟨[66,158,248,370,519,595],[]⟩
def row5_8 : State := ⟨[66,158,248,357,541,595],[]⟩
def row5_9 : State := ⟨[66,167,307,368,444,594],[]⟩
def row5_10 : State := ⟨[66,158,248,371,539,594],[]⟩
def row5_11 : State := ⟨[66,158,248,371,519,616],[]⟩
def row5_12 : State := ⟨[66,158,248,357,539,594],[]⟩
def row5_13 : State := ⟨[68,229,322,370,519,656],[]⟩
def row5_14 : State := ⟨[66,158,332,373,588,594],[]⟩
def layer5 : Array State := #[row5_0,row5_1,row5_2,row5_3,row5_4,row5_5,row5_6,row5_7,row5_8,row5_9,row5_10,row5_11,row5_12,row5_13,row5_14]
def row6_0 : State := ⟨[12,23,66,270,287,357,444],[⟨0,0,[27,66,270,287,357,444]⟩]⟩
def row6_1 : State := ⟨[27,66,158,229,287,357,444],[⟨0,0,[27,66,270,287,357,444]⟩]⟩
def row6_2 : State := ⟨[12,66,229,294,357,444,519],[]⟩
def row6_3 : State := ⟨[66,158,332,368,444,580,594],[]⟩
def row6_4 : State := ⟨[66,158,248,357,580,588,594],[]⟩
def row6_5 : State := ⟨[12,66,229,322,370,444,519],[]⟩
def row6_6 : State := ⟨[12,72,270,287,357,444,519],[]⟩
def row6_7 : State := ⟨[26,66,270,287,357,444,594],[]⟩
def row6_8 : State := ⟨[66,158,248,370,519,594,656],[]⟩
def row6_9 : State := ⟨[66,158,248,370,519,588,594],[]⟩
def row6_10 : State := ⟨[66,158,247,332,371,519,594],[]⟩
def row6_11 : State := ⟨[66,158,247,332,357,539,594],[]⟩
def row6_12 : State := ⟨[66,158,229,323,371,519,594],[]⟩
def row6_13 : State := ⟨[66,158,247,322,371,519,594],[]⟩
def row6_14 : State := ⟨[66,158,247,322,357,539,594],[]⟩
def row6_15 : State := ⟨[6,15,229,287,357,444,519],[⟨0,1,[19,229,287,357,444,519]⟩]⟩
def row6_16 : State := ⟨[66,158,229,322,371,539,594],[]⟩
def row6_17 : State := ⟨[66,158,229,322,371,519,616],[]⟩
def row6_18 : State := ⟨[18,66,229,287,357,444,519],[]⟩
def row6_19 : State := ⟨[12,66,229,303,357,444,519],[]⟩
def row6_20 : State := ⟨[17,66,229,287,357,444,519],[]⟩
def row6_21 : State := ⟨[17,66,229,287,357,444,523],[]⟩
def row6_22 : State := ⟨[12,67,229,287,357,444,523],[]⟩
def row6_23 : State := ⟨[12,66,229,294,357,448,519],[]⟩
def row6_24 : State := ⟨[12,66,229,294,357,444,523],[]⟩
def row6_25 : State := ⟨[66,158,229,288,371,519,594],[]⟩
def row6_26 : State := ⟨[17,66,229,287,366,444,519],[⟨5,2,[66,243,287,366,444,519]⟩,⟨4,2,[66,229,301,366,444,519]⟩]⟩
def row6_27 : State := ⟨[17,66,229,287,357,444,531],[⟨6,2,[69,229,287,357,444,531]⟩,⟨5,3,[66,243,287,357,444,531]⟩]⟩
def row6_28 : State := ⟨[17,66,229,287,361,444,519],[]⟩
def row6_29 : State := ⟨[17,66,229,287,357,444,521],[]⟩
def row6_30 : State := ⟨[12,67,229,294,357,444,519],[]⟩
def row6_31 : State := ⟨[66,158,229,287,364,444,521],[]⟩
def row6_32 : State := ⟨[17,66,229,287,364,444,519],[]⟩
def row6_33 : State := ⟨[17,66,229,287,357,444,530],[]⟩
def row6_34 : State := ⟨[12,66,229,301,357,444,519],[⟨4,2,[66,229,301,366,444,519]⟩,⟨7,4,[66,229,301,357,451,519]⟩]⟩
def row6_35 : State := ⟨[17,66,229,287,357,444,528],[⟨6,4,[66,243,287,357,444,528]⟩]⟩
def row6_36 : State := ⟨[12,66,229,294,366,444,519],[⟨3,5,[66,241,294,366,444,519]⟩,⟨4,2,[66,229,301,366,444,519]⟩]⟩
def row6_37 : State := ⟨[0,77,158,229,357,519,618],[⟨7,5,[77,158,229,357,520,618]⟩,⟨9,2,[77,158,229,357,519,619]⟩]⟩
def row6_38 : State := ⟨[0,66,158,248,370,519,594],[⟨0,6,[66,158,248,370,520,594]⟩,⟨0,7,[66,158,248,370,519,595]⟩]⟩
def row6_39 : State := ⟨[12,66,229,294,357,451,519],[⟨7,6,[68,229,294,357,451,519]⟩,⟨7,4,[66,229,301,357,451,519]⟩]⟩
def row6_40 : State := ⟨[0,66,158,248,357,541,594],[⟨0,4,[66,158,248,357,542,594]⟩,⟨0,8,[66,158,248,357,541,595]⟩]⟩
def row6_41 : State := ⟨[12,66,229,294,357,444,528],[⟨6,7,[68,229,294,357,444,528]⟩,⟨6,8,[66,241,294,357,444,528]⟩]⟩
def row6_42 : State := ⟨[12,68,229,294,357,444,519],[⟨7,6,[68,229,294,357,451,519]⟩,⟨6,7,[68,229,294,357,444,528]⟩]⟩
def row6_43 : State := ⟨[12,66,236,299,357,444,519],[⟨2,5,[66,236,299,366,444,519]⟩,⟨7,8,[66,236,299,357,451,519]⟩]⟩
def row6_44 : State := ⟨[12,66,236,294,357,444,519],[]⟩
def row6_45 : State := ⟨[66,158,229,287,366,444,528],[]⟩
def row6_46 : State := ⟨[28,66,229,287,357,444,594],[]⟩
def row6_47 : State := ⟨[14,158,229,287,357,444,519],[]⟩
def row6_48 : State := ⟨[66,158,229,289,368,444,594],[]⟩
def row6_49 : State := ⟨[66,158,229,287,366,444,521],[]⟩
def row6_50 : State := ⟨[66,158,248,370,444,519,594],[]⟩
def row6_51 : State := ⟨[66,158,229,297,357,451,519],[]⟩
def row6_52 : State := ⟨[66,158,229,287,364,444,528],[]⟩
def row6_53 : State := ⟨[68,162,229,287,366,444,519],[]⟩
def row6_54 : State := ⟨[66,158,248,370,459,519,594],[]⟩
def row6_55 : State := ⟨[68,158,229,299,366,444,519],[]⟩
def row6_56 : State := ⟨[66,158,248,370,444,541,594],[]⟩
def row6_57 : State := ⟨[66,158,248,370,444,519,618],[]⟩
def row6_58 : State := ⟨[68,158,229,287,366,444,528],[]⟩
def row6_59 : State := ⟨[66,168,307,367,444,519,594],[]⟩
def row6_60 : State := ⟨[66,158,231,305,368,444,594],[]⟩
def row6_61 : State := ⟨[66,158,231,305,357,457,594],[]⟩
def row6_62 : State := ⟨[66,158,229,288,371,519,616],[]⟩
def row6_63 : State := ⟨[66,158,241,299,366,444,519],[]⟩
def row6_64 : State := ⟨[66,158,241,299,357,444,528],[]⟩
def row6_65 : State := ⟨[66,158,247,333,371,519,594],[]⟩
def row6_66 : State := ⟨[66,158,247,333,357,539,594],[]⟩
def row6_67 : State := ⟨[12,69,229,287,357,444,530],[⟨9,9,[69,229,287,357,451,530]⟩,⟨6,2,[69,229,287,357,444,531]⟩]⟩
def row6_68 : State := ⟨[66,158,229,299,366,451,519],[]⟩
def row6_69 : State := ⟨[66,158,229,299,366,444,528],[]⟩
def row6_70 : State := ⟨[66,158,229,299,357,451,528],[]⟩
def row6_71 : State := ⟨[12,66,229,300,366,444,519],[⟨2,9,[66,241,300,366,444,519]⟩,⟨4,2,[66,229,301,366,444,519]⟩,⟨4,10,[66,229,300,366,451,519]⟩,⟨4,11,[66,229,300,366,444,528]⟩]⟩
def row6_72 : State := ⟨[12,69,229,300,357,444,519],[⟨7,10,[69,229,300,357,451,519]⟩,⟨6,11,[69,229,300,357,444,528]⟩]⟩
def row6_73 : State := ⟨[66,158,229,287,366,451,528],[]⟩
def row6_74 : State := ⟨[12,66,229,300,357,444,519],[⟨4,12,[66,229,300,357,451,519]⟩]⟩
def row6_75 : State := ⟨[66,158,248,371,444,519,594],[]⟩
def row6_76 : State := ⟨[66,158,229,299,366,444,519],[]⟩
def row6_77 : State := ⟨[66,158,229,299,357,451,519],[]⟩
def row6_78 : State := ⟨[75,158,229,287,444,519,613],[]⟩
def row6_79 : State := ⟨[66,158,229,303,460,519,594],[]⟩
def row6_80 : State := ⟨[6,158,229,287,364,444,519],[]⟩
def row6_81 : State := ⟨[66,158,229,290,371,519,594],[]⟩
def row6_82 : State := ⟨[66,158,229,287,364,444,522],[]⟩
def row6_83 : State := ⟨[66,158,229,322,370,520,594],[]⟩
def row6_84 : State := ⟨[66,158,229,322,370,519,595],[]⟩
def row6_85 : State := ⟨[66,158,332,357,432,588,594],[]⟩
def row6_86 : State := ⟨[66,158,250,370,444,519,594],[]⟩
def row6_87 : State := ⟨[68,158,229,287,367,444,665],[⟨1,13,[68,270,287,367,444,665]⟩]⟩
def row6_88 : State := ⟨[66,158,332,373,444,519,594],[⟨0,14,[66,158,332,373,588,594]⟩]⟩
def row6_89 : State := ⟨[66,158,332,367,444,538,594],[]⟩
def row6_90 : State := ⟨[10,66,229,322,370,519,656],[⟨0,13,[68,229,322,370,519,656]⟩,⟨2,14,[66,229,322,372,519,656]⟩]⟩
def row6_91 : State := ⟨[66,158,246,304,357,588,594],[]⟩
def row6_92 : State := ⟨[66,158,229,297,370,519,656],[]⟩
def row6_93 : State := ⟨[25,66,270,287,357,444,665],[⟨6,14,[73,270,287,357,444,665]⟩,⟨3,14,[66,270,287,369,444,665]⟩]⟩
def row6_94 : State := ⟨[66,158,229,287,369,444,665],[⟨3,14,[66,270,287,369,444,665]⟩]⟩
def row6_95 : State := ⟨[66,158,230,288,371,519,594],[]⟩
def row6_96 : State := ⟨[66,158,229,289,367,445,594],[]⟩
def row6_97 : State := ⟨[66,158,229,289,367,444,596],[]⟩
def row6_98 : State := ⟨[66,158,229,288,371,519,595],[]⟩
def row6_99 : State := ⟨[66,158,229,288,370,519,595],[]⟩
def row6_100 : State := ⟨[10,66,229,294,357,446,519],[]⟩
def row6_101 : State := ⟨[10,66,229,294,357,444,521],[]⟩
def row6_102 : State := ⟨[68,158,229,287,364,444,521],[]⟩
def row6_103 : State := ⟨[66,165,304,367,444,519,594],[]⟩
def row6_104 : State := ⟨[66,158,229,297,364,446,519],[]⟩
def row6_105 : State := ⟨[66,158,229,297,364,444,521],[]⟩
def row6_106 : State := ⟨[66,158,229,297,357,450,521],[]⟩
def row6_107 : State := ⟨[66,158,229,287,364,446,521],[]⟩
def row6_108 : State := ⟨[66,158,229,287,364,446,526],[]⟩
def row6_109 : State := ⟨[68,158,229,287,364,444,528],[]⟩
def row6_110 : State := ⟨[66,166,307,367,444,519,594],[]⟩
def row6_111 : State := ⟨[66,158,248,370,444,538,594],[]⟩
def row6_112 : State := ⟨[66,158,248,370,444,519,615],[]⟩
def layer6 : Array State := #[row6_0,row6_1,row6_2,row6_3,row6_4,row6_5,row6_6,row6_7,row6_8,row6_9,row6_10,row6_11,row6_12,row6_13,row6_14,row6_15,row6_16,row6_17,row6_18,row6_19,row6_20,row6_21,row6_22,row6_23,row6_24,row6_25,row6_26,row6_27,row6_28,row6_29,row6_30,row6_31,row6_32,row6_33,row6_34,row6_35,row6_36,row6_37,row6_38,row6_39,row6_40,row6_41,row6_42,row6_43,row6_44,row6_45,row6_46,row6_47,row6_48,row6_49,row6_50,row6_51,row6_52,row6_53,row6_54,row6_55,row6_56,row6_57,row6_58,row6_59,row6_60,row6_61,row6_62,row6_63,row6_64,row6_65,row6_66,row6_67,row6_68,row6_69,row6_70,row6_71,row6_72,row6_73,row6_74,row6_75,row6_76,row6_77,row6_78,row6_79,row6_80,row6_81,row6_82,row6_83,row6_84,row6_85,row6_86,row6_87,row6_88,row6_89,row6_90,row6_91,row6_92,row6_93,row6_94,row6_95,row6_96,row6_97,row6_98,row6_99,row6_100,row6_101,row6_102,row6_103,row6_104,row6_105,row6_106,row6_107,row6_108,row6_109,row6_110,row6_111,row6_112]
def row7_0 : State := ⟨[66,158,229,287,357,444,519,594],[]⟩
def row7_1 : State := ⟨[49,66,229,287,357,444,519,594],[]⟩
def row7_2 : State := ⟨[66,158,229,287,358,444,519,594],[]⟩
def row7_3 : State := ⟨[66,158,229,287,357,444,519,595],[]⟩
def row7_4 : State := ⟨[66,158,229,287,357,444,519,600],[]⟩
def row7_5 : State := ⟨[66,158,229,287,357,444,519,598],[]⟩
def row7_6 : State := ⟨[66,158,229,287,364,444,519,594],[]⟩
def row7_7 : State := ⟨[66,158,229,287,357,444,519,604],[]⟩
def row7_8 : State := ⟨[12,66,229,310,322,357,444,519],[⟨1,0,[12,36,66,229,322,357,519]⟩]⟩
def row7_9 : State := ⟨[66,125,229,287,357,444,519,594],[]⟩
def row7_10 : State := ⟨[12,23,66,158,229,287,357,444],[⟨0,1,[27,66,158,229,287,357,444]⟩,⟨0,0,[12,23,66,270,287,357,444]⟩]⟩
def row7_11 : State := ⟨[66,158,229,287,364,444,519,656],[]⟩
def row7_12 : State := ⟨[12,66,229,322,357,444,519,574],[⟨0,2,[12,66,229,294,357,444,519]⟩]⟩
def row7_13 : State := ⟨[66,158,229,287,357,444,521,625],[⟨10,2,[15,66,229,287,357,444,521]⟩]⟩
def row7_14 : State := ⟨[12,66,229,322,357,444,519,644],[⟨2,3,[66,229,322,366,444,519,644]⟩,⟨7,4,[66,229,322,357,451,519,644]⟩]⟩
def row7_15 : State := ⟨[66,158,253,332,370,444,519,594],[⟨2,5,[23,66,158,332,370,444,594]⟩]⟩
def row7_16 : State := ⟨[66,158,229,297,357,465,519,656],[]⟩
def row7_17 : State := ⟨[66,158,229,287,364,444,549,665],[⟨9,6,[29,66,158,287,364,444,665]⟩]⟩
def row7_18 : State := ⟨[10,23,66,270,287,357,444,594],[⟨0,7,[26,66,270,287,357,444,594]⟩,⟨2,6,[23,68,270,287,357,444,594]⟩,⟨4,5,[23,66,270,287,364,444,594]⟩]⟩
def row7_19 : State := ⟨[49,66,229,287,357,444,519,656],[]⟩
def row7_20 : State := ⟨[12,68,229,270,287,357,444,519],[⟨7,8,[68,229,270,287,357,451,519]⟩,⟨6,9,[68,229,270,287,357,444,528]⟩]⟩
def row7_21 : State := ⟨[12,66,229,299,322,357,444,519],[⟨4,10,[66,229,299,322,366,444,519]⟩,⟨4,11,[66,229,299,322,357,451,519]⟩]⟩
def row7_22 : State := ⟨[12,66,229,273,287,357,444,519],[⟨4,12,[66,229,273,287,366,444,519]⟩]⟩
def row7_23 : State := ⟨[12,66,229,270,299,357,444,519],[⟨4,13,[66,229,270,299,366,444,519]⟩,⟨4,14,[66,229,270,299,357,451,519]⟩]⟩
def row7_24 : State := ⟨[12,66,229,287,339,357,444,519],[⟨10,15,[12,34,66,229,287,444,519]⟩]⟩
def row7_25 : State := ⟨[12,66,229,270,287,366,444,519],[⟨5,10,[66,241,270,287,366,444,519]⟩,⟨4,12,[66,229,273,287,366,444,519]⟩,⟨4,13,[66,229,270,299,366,444,519]⟩,⟨4,16,[66,229,270,287,366,451,519]⟩,⟨4,17,[66,229,270,287,366,444,528]⟩]⟩
def row7_26 : State := ⟨[2,29,66,158,287,357,444,594],[⟨2,18,[30,66,158,287,357,444,594]⟩,⟨9,2,[29,66,158,287,357,445,594]⟩,⟨7,19,[29,66,158,287,357,444,597]⟩]⟩
def row7_27 : State := ⟨[12,66,229,270,287,357,451,519],[⟨7,8,[68,229,270,287,357,451,519]⟩,⟨4,14,[66,229,270,299,357,451,519]⟩,⟨4,16,[66,229,270,287,366,451,519]⟩]⟩
def row7_28 : State := ⟨[12,66,229,270,287,357,444,528],[⟨6,9,[68,229,270,287,357,444,528]⟩,⟨5,11,[66,241,270,287,357,444,528]⟩,⟨4,17,[66,229,270,287,366,444,528]⟩]⟩
def row7_29 : State := ⟨[12,66,158,229,287,357,444,519],[]⟩
def row7_30 : State := ⟨[66,158,229,322,371,444,519,594],[⟨4,3,[66,229,322,371,480,519,594]⟩]⟩
def row7_31 : State := ⟨[66,158,229,300,357,444,519,656],[⟨4,4,[66,229,300,357,480,519,656]⟩]⟩
def row7_32 : State := ⟨[66,91,229,287,357,444,519,665],[]⟩
def row7_33 : State := ⟨[66,158,229,292,357,444,519,625],[]⟩
def row7_34 : State := ⟨[66,158,229,290,357,465,519,594],[⟨3,20,[38,66,158,229,357,519,594]⟩]⟩
def row7_35 : State := ⟨[66,158,229,290,357,444,549,594],[]⟩
def row7_36 : State := ⟨[66,158,229,287,357,444,522,625],[⟨10,19,[15,66,229,287,357,444,522]⟩]⟩
def row7_37 : State := ⟨[6,158,229,287,357,444,519,625],[⟨0,15,[6,15,229,287,357,444,519]⟩]⟩
def row7_38 : State := ⟨[57,158,229,287,357,444,519,594],[]⟩
def row7_39 : State := ⟨[66,152,229,287,357,444,519,594],[]⟩
def row7_40 : State := ⟨[66,158,229,287,360,444,519,594],[]⟩
def row7_41 : State := ⟨[66,133,229,287,357,444,519,594],[]⟩
def row7_42 : State := ⟨[66,158,229,287,357,444,519,608],[]⟩
def row7_43 : State := ⟨[66,125,229,287,357,452,519,594],[]⟩
def row7_44 : State := ⟨[66,125,229,285,357,444,519,594],[]⟩
def row7_45 : State := ⟨[12,66,128,158,229,287,357,519],[]⟩
def row7_46 : State := ⟨[12,158,186,229,287,357,444,519],[]⟩
def row7_47 : State := ⟨[12,66,196,229,287,357,444,519],[]⟩
def row7_48 : State := ⟨[66,84,158,229,287,357,519,594],[]⟩
def row7_49 : State := ⟨[158,229,310,380,444,519,625,644],[]⟩
def row7_50 : State := ⟨[158,229,310,380,465,519,594,691],[]⟩
def row7_51 : State := ⟨[66,158,229,287,366,444,519,594],[]⟩
def row7_52 : State := ⟨[66,158,229,289,380,444,549,594],[]⟩
def row7_53 : State := ⟨[66,158,229,288,380,465,519,594],[]⟩
def row7_54 : State := ⟨[66,158,229,287,380,444,521,625],[]⟩
def row7_55 : State := ⟨[12,67,158,229,287,357,444,519],[]⟩
def row7_56 : State := ⟨[12,47,66,229,287,357,444,519],[⟨1,2,[12,66,236,287,357,444,519]⟩,⟨0,2,[12,66,229,294,357,444,519]⟩]⟩
def row7_57 : State := ⟨[66,158,229,289,444,494,549,594],[]⟩
def row7_58 : State := ⟨[12,66,177,229,287,357,444,523],[]⟩
def row7_59 : State := ⟨[66,158,229,310,357,444,535,609],[]⟩
def row7_60 : State := ⟨[66,158,229,310,357,459,519,609],[⟨3,21,[38,66,158,229,357,519,609]⟩]⟩
def row7_61 : State := ⟨[66,158,229,289,359,444,549,594],[⟨7,22,[29,66,158,289,359,444,594]⟩]⟩
def row7_62 : State := ⟨[0,37,66,158,230,357,519,594],[⟨6,21,[38,66,158,230,357,519,594]⟩,⟨6,22,[37,66,158,230,358,519,594]⟩,⟨8,23,[37,66,158,230,357,520,594]⟩,⟨6,24,[37,66,158,230,357,519,595]⟩]⟩
def row7_63 : State := ⟨[66,158,229,289,357,445,549,594],[⟨9,23,[29,66,158,289,357,445,594]⟩]⟩
def row7_64 : State := ⟨[66,158,229,289,357,444,549,596],[⟨7,24,[29,66,158,289,357,444,596]⟩]⟩
def row7_65 : State := ⟨[66,158,229,288,465,519,575,594],[⟨0,25,[66,158,229,288,371,519,594]⟩]⟩
def row7_66 : State := ⟨[17,66,229,287,357,444,519],[⟨10,26,[17,69,229,287,357,444,519]⟩,⟨11,27,[17,66,243,287,357,444,519]⟩,⟨10,27,[17,66,229,301,357,444,519]⟩,⟨0,26,[17,66,229,287,366,444,519]⟩,⟨1,27,[17,66,229,287,357,453,519]⟩,⟨0,27,[17,66,229,287,357,444,531]⟩]⟩
def row7_67 : State := ⟨[17,66,177,229,287,357,444,519],[]⟩
def row7_68 : State := ⟨[17,66,162,229,287,357,444,519],[⟨4,25,[66,162,229,287,366,444,519]⟩]⟩
def row7_69 : State := ⟨[66,158,229,288,465,519,574,594],[]⟩
def row7_70 : State := ⟨[17,66,158,229,287,357,444,519],[]⟩
def row7_71 : State := ⟨[66,158,229,288,358,465,519,594],[⟨3,28,[38,66,158,229,358,519,594]⟩]⟩
def row7_72 : State := ⟨[0,38,66,158,229,357,519,594],[⟨8,21,[38,66,159,229,357,519,594]⟩,⟨6,21,[38,66,158,230,357,519,594]⟩,⟨3,28,[38,66,158,229,358,519,594]⟩,⟨5,29,[38,66,158,229,357,520,594]⟩,⟨3,29,[38,66,158,229,357,519,595]⟩]⟩
def row7_73 : State := ⟨[66,158,229,288,357,465,519,595],[⟨3,29,[38,66,158,229,357,519,595]⟩]⟩
def row7_74 : State := ⟨[0,37,66,158,229,358,519,594],[⟨3,28,[38,66,158,229,358,519,594]⟩,⟨8,22,[37,66,159,229,358,519,594]⟩,⟨6,22,[37,66,158,230,358,519,594]⟩,⟨8,30,[37,66,158,229,358,520,594]⟩,⟨6,30,[37,66,158,229,358,519,595]⟩]⟩
def row7_75 : State := ⟨[66,158,229,287,358,465,519,595],[⟨6,30,[37,66,158,229,358,519,595]⟩]⟩
def row7_76 : State := ⟨[66,158,229,287,425,444,521,625],[⟨0,31,[66,158,229,287,364,444,521]⟩]⟩
def row7_77 : State := ⟨[0,66,158,229,287,370,519,594],[⟨5,31,[66,158,229,287,370,520,594]⟩,⟨3,31,[66,158,229,287,370,519,595]⟩]⟩
def row7_78 : State := ⟨[12,17,66,229,287,357,444,519],[⟨10,32,[17,68,229,287,357,444,519]⟩,⟨11,33,[17,66,241,287,357,444,519]⟩,⟨1,34,[12,66,243,287,357,444,519]⟩,⟨10,33,[17,66,229,299,357,444,519]⟩,⟨0,34,[12,66,229,301,357,444,519]⟩,⟨0,26,[17,66,229,287,366,444,519]⟩,⟨1,35,[17,66,229,287,357,451,519]⟩,⟨0,35,[17,66,229,287,357,444,528]⟩]⟩
def row7_79 : State := ⟨[0,37,77,158,229,357,519,594],[⟨6,26,[38,77,158,229,357,519,594]⟩,⟨8,36,[37,77,158,229,357,520,594]⟩,⟨2,37,[0,77,158,229,357,541,594]⟩,⟨6,36,[37,77,158,229,357,519,595]⟩,⟨0,37,[0,77,158,229,357,519,618]⟩]⟩
def row7_80 : State := ⟨[0,37,66,158,248,357,519,594],[⟨6,35,[38,66,158,248,357,519,594]⟩,⟨0,38,[0,66,158,248,370,519,594]⟩,⟨8,39,[37,66,158,248,357,520,594]⟩,⟨0,40,[0,66,158,248,357,541,594]⟩,⟨6,41,[37,66,158,248,357,519,595]⟩]⟩
def row7_81 : State := ⟨[0,37,66,158,229,370,519,594],[⟨3,32,[38,66,158,229,370,519,594]⟩,⟨2,38,[0,66,172,229,370,519,594]⟩,⟨0,38,[0,66,158,248,370,519,594]⟩,⟨8,42,[37,66,158,229,370,520,594]⟩,⟨6,42,[37,66,158,229,370,519,595]⟩]⟩
def row7_82 : State := ⟨[12,66,229,294,357,444,519],[⟨0,42,[12,68,229,294,357,444,519]⟩,⟨1,43,[12,66,241,294,357,444,519]⟩,⟨0,34,[12,66,229,301,357,444,519]⟩,⟨0,36,[12,66,229,294,366,444,519]⟩,⟨0,39,[12,66,229,294,357,451,519]⟩,⟨0,41,[12,66,229,294,357,444,528]⟩]⟩
def row7_83 : State := ⟨[12,66,229,236,287,357,444,519],[]⟩
def row7_84 : State := ⟨[0,37,66,158,229,357,519,595],[⟨3,29,[38,66,158,229,357,519,595]⟩,⟨6,23,[37,66,159,229,357,519,595]⟩,⟨6,24,[37,66,158,230,357,519,595]⟩,⟨6,30,[37,66,158,229,358,519,595]⟩,⟨6,44,[37,66,158,229,357,520,595]⟩]⟩
def row7_85 : State := ⟨[0,37,66,158,229,357,519,618],[⟨3,33,[38,66,158,229,357,519,618]⟩,⟨0,37,[0,77,158,229,357,519,618]⟩,⟨2,40,[0,66,172,229,357,519,618]⟩,⟨6,43,[37,66,158,229,357,520,618]⟩,⟨6,34,[37,66,158,229,357,519,619]⟩]⟩
def row7_86 : State := ⟨[12,66,177,229,294,357,444,519],[]⟩
def row7_87 : State := ⟨[12,66,229,294,357,444,519,594],[⟨10,31,[68,229,294,357,444,519,594]⟩]⟩
def row7_88 : State := ⟨[66,158,229,287,357,445,549,596],[⟨7,44,[29,66,158,287,357,445,596]⟩]⟩
def row7_89 : State := ⟨[12,66,158,229,287,357,444,523],[]⟩
def row7_90 : State := ⟨[12,66,158,229,294,357,444,519],[]⟩
def row7_91 : State := ⟨[66,158,229,289,357,444,549,594],[]⟩
def row7_92 : State := ⟨[66,158,229,288,357,465,519,594],[⟨3,20,[38,66,158,229,357,519,594]⟩]⟩
def row7_93 : State := ⟨[0,37,66,158,229,357,519,594],[⟨3,20,[38,66,158,229,357,519,594]⟩,⟨8,2,[37,66,158,229,357,520,594]⟩,⟨6,2,[37,66,158,229,357,519,595]⟩]⟩
def row7_94 : State := ⟨[66,91,229,287,357,444,519,594],[]⟩
def row7_95 : State := ⟨[49,69,229,287,357,444,519,594],[⟨11,45,[69,242,287,357,444,519,594]⟩,⟨10,45,[69,229,300,357,444,519,594]⟩]⟩
def row7_96 : State := ⟨[49,66,229,300,357,444,519,594],[⟨10,45,[69,229,300,357,444,519,594]⟩]⟩
def row7_97 : State := ⟨[66,158,229,287,357,444,519,606],[]⟩
def row7_98 : State := ⟨[12,66,158,229,287,357,444,535],[]⟩
def row7_99 : State := ⟨[12,66,158,229,287,357,444,532],[]⟩
def row7_100 : State := ⟨[12,70,158,229,287,357,444,519],[]⟩
def row7_101 : State := ⟨[12,66,165,229,287,357,444,519],[]⟩
def row7_102 : State := ⟨[16,66,229,287,357,444,519,594],[]⟩
def row7_103 : State := ⟨[12,66,158,229,302,357,444,519],[]⟩
def row7_104 : State := ⟨[12,66,88,229,287,357,444,519],[⟨1,2,[12,66,236,287,357,444,519]⟩]⟩
def row7_105 : State := ⟨[12,66,159,229,287,357,444,519],[]⟩
def row7_106 : State := ⟨[12,66,158,229,289,357,444,519],[]⟩
def row7_107 : State := ⟨[12,66,158,229,288,357,444,519],[]⟩
def row7_108 : State := ⟨[12,66,158,229,287,358,444,519],[]⟩
def row7_109 : State := ⟨[12,66,158,229,287,357,444,520],[]⟩
def row7_110 : State := ⟨[13,66,158,229,287,357,444,519],[]⟩
def row7_111 : State := ⟨[66,158,332,444,494,549,580,594],[]⟩
def row7_112 : State := ⟨[66,158,229,287,357,444,519,603],[]⟩
def row7_113 : State := ⟨[66,158,229,287,357,444,519,612],[]⟩
def row7_114 : State := ⟨[66,119,158,229,287,370,519,594],[]⟩
def row7_115 : State := ⟨[12,66,122,229,287,357,444,519],[]⟩
def row7_116 : State := ⟨[66,111,229,287,357,444,519,594],[]⟩
def row7_117 : State := ⟨[66,91,242,287,357,444,519,594],[]⟩
def row7_118 : State := ⟨[12,66,214,229,287,357,444,519],[]⟩
def row7_119 : State := ⟨[66,82,229,287,357,444,519,594],[]⟩
def row7_120 : State := ⟨[12,72,158,229,287,357,444,519],[⟨0,6,[12,72,270,287,357,444,519]⟩]⟩
def row7_121 : State := ⟨[12,66,166,229,287,357,444,519],[]⟩
def row7_122 : State := ⟨[12,66,158,229,304,357,444,519],[]⟩
def row7_123 : State := ⟨[12,66,158,229,287,367,444,519],[⟨1,5,[12,66,270,287,367,444,519]⟩]⟩
def row7_124 : State := ⟨[12,66,158,229,287,357,444,538],[]⟩
def row7_125 : State := ⟨[26,66,158,229,287,357,444,594],[⟨0,7,[26,66,270,287,357,444,594]⟩]⟩
def row7_126 : State := ⟨[12,29,66,158,287,357,444,519],[⟨2,46,[31,66,158,287,357,444,519]⟩]⟩
def row7_127 : State := ⟨[71,158,229,287,444,465,519,594],[]⟩
def row7_128 : State := ⟨[66,158,229,303,444,465,519,594],[⟨6,47,[40,66,158,229,444,519,594]⟩]⟩
def row7_129 : State := ⟨[2,12,158,229,287,357,444,519],[⟨0,47,[14,158,229,287,357,444,519]⟩]⟩
def row7_130 : State := ⟨[12,66,158,229,291,357,444,519],[⟨2,48,[66,158,229,291,366,444,519]⟩]⟩
def row7_131 : State := ⟨[12,66,162,229,287,357,444,519],[⟨4,25,[66,162,229,287,366,444,519]⟩]⟩
def row7_132 : State := ⟨[12,66,158,229,287,361,444,519],[]⟩
def row7_133 : State := ⟨[0,66,158,229,287,371,519,594],[⟨4,48,[66,159,229,287,371,519,594]⟩,⟨1,48,[66,158,230,287,371,519,594]⟩,⟨0,25,[66,158,229,288,371,519,594]⟩,⟨5,49,[66,158,229,287,371,520,594]⟩,⟨3,49,[66,158,229,287,371,519,595]⟩]⟩
def row7_134 : State := ⟨[12,66,158,229,287,357,444,521],[⟨0,49,[66,158,229,287,366,444,521]⟩]⟩
def row7_135 : State := ⟨[66,158,229,322,370,444,519,594],[]⟩
def row7_136 : State := ⟨[66,158,248,444,465,519,574,594],[⟨0,50,[66,158,248,370,444,519,594]⟩]⟩
def row7_137 : State := ⟨[12,68,158,229,287,357,444,519],[⟨7,50,[68,158,229,287,357,451,519]⟩,⟨6,50,[68,158,229,287,357,444,528]⟩]⟩
def row7_138 : State := ⟨[66,158,229,287,357,444,528,629],[]⟩
def row7_139 : State := ⟨[12,66,158,229,297,357,444,519],[⟨0,51,[66,158,229,297,357,451,519]⟩]⟩
def row7_140 : State := ⟨[12,66,158,229,287,364,444,519],[⟨1,52,[66,158,229,287,364,451,519]⟩,⟨0,52,[66,158,229,287,364,444,528]⟩]⟩
def row7_141 : State := ⟨[12,66,158,229,287,357,444,526],[]⟩
def row7_142 : State := ⟨[10,66,158,229,287,357,444,528],[⟨6,50,[68,158,229,287,357,444,528]⟩,⟨1,51,[66,158,239,287,357,444,528]⟩,⟨0,52,[66,158,229,287,364,444,528]⟩]⟩
def row7_143 : State := ⟨[60,66,229,287,357,444,519,674],[⟨0,20,[17,66,229,287,357,444,519]⟩]⟩
def row7_144 : State := ⟨[66,158,229,310,371,519,594,691],[⟨0,25,[66,158,229,288,371,519,594]⟩]⟩
def row7_145 : State := ⟨[66,158,229,287,366,444,519,674],[]⟩
def row7_146 : State := ⟨[12,68,162,229,287,357,444,519],[⟨0,53,[68,162,229,287,366,444,519]⟩,⟨7,54,[68,162,229,287,357,451,519]⟩,⟨6,54,[68,162,229,287,357,444,528]⟩]⟩
def row7_147 : State := ⟨[12,68,158,229,299,357,444,519],[⟨0,55,[68,158,229,299,366,444,519]⟩,⟨7,56,[68,158,229,299,357,451,519]⟩,⟨6,57,[68,158,229,299,357,444,528]⟩]⟩
def row7_148 : State := ⟨[12,68,158,229,287,366,444,519],[⟨0,53,[68,162,229,287,366,444,519]⟩,⟨1,55,[68,158,241,287,366,444,519]⟩,⟨0,55,[68,158,229,299,366,444,519]⟩,⟨1,58,[68,158,229,287,366,451,519]⟩,⟨0,58,[68,158,229,287,366,444,528]⟩]⟩
def row7_149 : State := ⟨[66,158,248,370,444,519,594],[⟨0,38,[0,66,158,248,370,519,594]⟩,⟨0,9,[66,158,248,370,519,588,594]⟩,⟨0,8,[66,158,248,370,519,594,656]⟩]⟩
def row7_150 : State := ⟨[66,158,168,287,367,444,519,594],[]⟩
def row7_151 : State := ⟨[12,68,158,229,287,357,444,528],[⟨6,54,[68,162,229,287,357,444,528]⟩,⟨6,56,[68,158,241,287,357,444,528]⟩,⟨6,57,[68,158,229,299,357,444,528]⟩,⟨0,58,[68,158,229,287,366,444,528]⟩,⟨8,59,[68,158,229,287,357,451,528]⟩]⟩
def row7_152 : State := ⟨[66,68,158,229,287,357,444,528],[]⟩
def row7_153 : State := ⟨[12,66,162,229,299,357,444,519],[⟨2,60,[66,162,229,299,366,444,519]⟩,⟨2,61,[66,162,229,299,357,451,519]⟩]⟩
def row7_154 : State := ⟨[66,158,229,288,371,519,594],[⟨0,12,[66,158,229,323,371,519,594]⟩,⟨2,12,[66,158,229,333,371,519,594]⟩,⟨3,26,[38,66,158,229,371,519,594]⟩]⟩
def row7_155 : State := ⟨[66,69,229,287,357,444,519,598],[⟨0,20,[17,66,229,287,357,444,519]⟩]⟩
def row7_156 : State := ⟨[12,66,162,229,287,366,444,519],[⟨0,53,[68,162,229,287,366,444,519]⟩,⟨3,60,[66,162,241,287,366,444,519]⟩,⟨2,60,[66,162,229,299,366,444,519]⟩,⟨5,62,[66,162,229,287,366,451,519]⟩,⟨4,62,[66,162,229,287,366,444,528]⟩]⟩
def row7_157 : State := ⟨[12,66,162,229,287,357,444,528],[⟨6,54,[68,162,229,287,357,444,528]⟩,⟨3,61,[66,162,241,287,357,444,528]⟩,⟨4,62,[66,162,229,287,366,444,528]⟩]⟩
def row7_158 : State := ⟨[66,158,162,229,287,366,444,519],[]⟩
def row7_159 : State := ⟨[12,66,158,241,299,357,444,519],[⟨0,63,[66,158,241,299,366,444,519]⟩,⟨1,64,[66,158,241,299,357,451,519]⟩,⟨0,64,[66,158,241,299,357,444,528]⟩]⟩
def row7_160 : State := ⟨[12,66,229,299,324,357,444,519],[⟨4,65,[66,229,299,324,366,444,519]⟩,⟨4,66,[66,229,299,324,357,451,519]⟩]⟩
def row7_161 : State := ⟨[66,158,229,299,366,444,519],[⟨4,13,[66,229,270,299,366,444,519]⟩,⟨4,65,[66,229,299,324,366,444,519]⟩,⟨10,67,[15,66,229,299,366,444,519]⟩]⟩
def row7_162 : State := ⟨[66,69,229,287,357,444,530,594],[⟨4,37,[3,69,229,287,357,444,530]⟩]⟩
def row7_163 : State := ⟨[12,66,158,229,299,366,444,519],[⟨0,55,[68,158,229,299,366,444,519]⟩,⟨2,60,[66,162,229,299,366,444,519]⟩,⟨0,63,[66,158,241,299,366,444,519]⟩,⟨0,68,[66,158,229,299,366,451,519]⟩,⟨0,69,[66,158,229,299,366,444,528]⟩]⟩
def row7_164 : State := ⟨[66,158,229,299,357,451,519],[⟨4,14,[66,229,270,299,357,451,519]⟩,⟨4,66,[66,229,299,324,357,451,519]⟩,⟨7,40,[7,66,229,299,357,451,519]⟩]⟩
def row7_165 : State := ⟨[66,158,168,287,357,444,519,608],[]⟩
def row7_166 : State := ⟨[12,66,158,229,299,357,451,519],[⟨7,56,[68,158,229,299,357,451,519]⟩,⟨2,61,[66,162,229,299,357,451,519]⟩,⟨1,64,[66,158,241,299,357,451,519]⟩,⟨0,68,[66,158,229,299,366,451,519]⟩,⟨0,70,[66,158,229,299,357,451,528]⟩]⟩
def row7_167 : State := ⟨[12,66,158,229,299,357,444,528],[⟨6,57,[68,158,229,299,357,444,528]⟩,⟨0,64,[66,158,241,299,357,444,528]⟩,⟨0,69,[66,158,229,299,366,444,528]⟩,⟨0,70,[66,158,229,299,357,451,528]⟩]⟩
def row7_168 : State := ⟨[66,158,167,229,287,368,444,594],[⟨3,10,[66,167,270,287,368,444,594]⟩,⟨1,12,[66,158,272,287,368,444,594]⟩]⟩
def row7_169 : State := ⟨[66,158,167,229,287,357,444,606],[⟨3,11,[66,167,270,287,357,444,606]⟩]⟩
def row7_170 : State := ⟨[12,15,66,229,287,366,444,519],[⟨0,26,[17,66,229,287,366,444,519]⟩,⟨11,67,[15,66,241,287,366,444,519]⟩,⟨1,71,[12,66,242,287,366,444,519]⟩,⟨10,67,[15,66,229,299,366,444,519]⟩,⟨0,71,[12,66,229,300,366,444,519]⟩,⟨11,72,[15,66,229,287,366,451,519]⟩,⟨10,72,[15,66,229,287,366,444,528]⟩]⟩
def row7_171 : State := ⟨[66,158,229,287,366,444,528],[⟨4,17,[66,229,270,287,366,444,528]⟩,⟨5,16,[66,229,287,322,366,444,528]⟩,⟨10,72,[15,66,229,287,366,444,528]⟩]⟩
def row7_172 : State := ⟨[66,158,229,287,366,444,451,519],[]⟩
def row7_173 : State := ⟨[12,66,158,229,287,366,444,528],[⟨0,58,[68,158,229,287,366,444,528]⟩,⟨4,62,[66,162,229,287,366,444,528]⟩,⟨1,68,[66,158,241,287,366,444,528]⟩,⟨0,69,[66,158,229,299,366,444,528]⟩,⟨0,73,[66,158,229,287,366,451,528]⟩]⟩
def row7_174 : State := ⟨[12,15,66,229,287,357,444,519],[⟨0,20,[17,66,229,287,357,444,519]⟩,⟨1,74,[12,66,242,287,357,444,519]⟩,⟨0,74,[12,66,229,300,357,444,519]⟩,⟨11,74,[15,66,229,287,357,451,519]⟩,⟨10,74,[15,66,229,287,357,444,528]⟩]⟩
def row7_175 : State := ⟨[66,69,229,300,357,444,519,594],[⟨0,74,[12,66,229,300,357,444,519]⟩]⟩
def row7_176 : State := ⟨[12,66,158,229,287,357,451,528],[⟨8,59,[68,158,229,287,357,451,528]⟩,⟨1,70,[66,158,241,287,357,451,528]⟩,⟨0,70,[66,158,229,299,357,451,528]⟩,⟨0,73,[66,158,229,287,366,451,528]⟩]⟩
def row7_177 : State := ⟨[66,158,229,287,364,444,519,598],[]⟩
def row7_178 : State := ⟨[66,158,229,287,364,444,530,594],[]⟩
def row7_179 : State := ⟨[68,158,229,287,366,444,519,594],[]⟩
def row7_180 : State := ⟨[66,158,229,300,364,444,519,594],[]⟩
def row7_181 : State := ⟨[66,158,229,287,357,444,530,598],[]⟩
def row7_182 : State := ⟨[66,158,229,288,371,444,519,594],[]⟩
def row7_183 : State := ⟨[66,158,229,288,357,444,519,616],[]⟩
def row7_184 : State := ⟨[66,158,229,299,357,444,519,625],[]⟩
def row7_185 : State := ⟨[66,158,229,299,357,444,519,656],[]⟩
def row7_186 : State := ⟨[66,158,229,287,357,444,541,618],[]⟩
def row7_187 : State := ⟨[66,158,229,299,366,444,519,594],[]⟩
def row7_188 : State := ⟨[66,158,229,299,357,451,519,594],[]⟩
def row7_189 : State := ⟨[66,158,229,299,357,444,528,594],[]⟩
def row7_190 : State := ⟨[12,69,158,229,287,357,444,519],[⟨7,75,[69,158,229,287,357,451,519]⟩,⟨6,75,[69,158,229,287,357,444,528]⟩]⟩
def row7_191 : State := ⟨[66,158,229,287,366,444,519,637],[⟨3,3,[66,270,287,366,444,519,637]⟩]⟩
def row7_192 : State := ⟨[66,158,229,287,366,444,519,656],[]⟩
def row7_193 : State := ⟨[66,158,229,287,366,444,528,594],[]⟩
def row7_194 : State := ⟨[66,158,229,287,357,444,528,637],[⟨6,4,[66,270,287,357,444,528,637]⟩]⟩
def row7_195 : State := ⟨[66,158,229,287,357,444,528,625],[⟨10,74,[15,66,229,287,357,444,528]⟩]⟩
def row7_196 : State := ⟨[66,158,229,287,357,444,539,616],[]⟩
def row7_197 : State := ⟨[12,66,229,265,287,357,444,519],[]⟩
def row7_198 : State := ⟨[66,158,248,370,444,465,519,594],[]⟩
def row7_199 : State := ⟨[66,158,229,288,310,371,519,594],[]⟩
def row7_200 : State := ⟨[66,158,177,229,299,366,444,519],[]⟩
def row7_201 : State := ⟨[66,158,177,229,299,357,451,519],[]⟩
def row7_202 : State := ⟨[66,158,177,229,287,366,444,528],[]⟩
def row7_203 : State := ⟨[12,66,158,229,299,357,444,519],[⟨0,76,[66,158,229,299,366,444,519]⟩,⟨0,77,[66,158,229,299,357,451,519]⟩]⟩
def row7_204 : State := ⟨[12,66,158,229,287,366,444,519],[⟨4,25,[66,162,229,287,366,444,519]⟩,⟨1,76,[66,158,241,287,366,444,519]⟩,⟨0,76,[66,158,229,299,366,444,519]⟩,⟨1,45,[66,158,229,287,366,451,519]⟩,⟨0,45,[66,158,229,287,366,444,528]⟩]⟩
def row7_205 : State := ⟨[12,66,158,229,287,357,444,528],[⟨6,50,[68,158,229,287,357,444,528]⟩,⟨1,77,[66,158,241,287,357,444,528]⟩,⟨0,45,[66,158,229,287,366,444,528]⟩]⟩
def row7_206 : State := ⟨[66,158,229,287,396,444,519,598],[]⟩
def row7_207 : State := ⟨[67,158,229,287,396,444,519,594],[]⟩
def row7_208 : State := ⟨[66,158,229,294,396,444,519,594],[]⟩
def row7_209 : State := ⟨[66,158,229,313,370,444,519,594],[]⟩
def row7_210 : State := ⟨[66,158,229,297,357,444,519,653],[]⟩
def row7_211 : State := ⟨[66,158,229,287,364,444,519,653],[]⟩
def row7_212 : State := ⟨[6,158,229,287,357,444,519,594],[]⟩
def row7_213 : State := ⟨[66,158,229,287,357,444,519,597],[]⟩
def row7_214 : State := ⟨[6,158,229,293,357,444,519,594],[⟨6,78,[158,229,293,363,444,519,594]⟩,⟨9,79,[158,229,293,357,447,519,594]⟩]⟩
def row7_215 : State := ⟨[6,158,229,287,363,444,519,594],[⟨10,78,[164,229,287,363,444,519,594]⟩,⟨7,78,[158,235,287,363,444,519,594]⟩,⟨6,78,[158,229,293,363,444,519,594]⟩]⟩
def row7_216 : State := ⟨[6,158,229,287,357,444,519,597],[⟨6,79,[164,229,287,357,444,519,597]⟩]⟩
def row7_217 : State := ⟨[6,10,158,229,287,357,444,519],[⟨0,47,[14,158,229,287,357,444,519]⟩,⟨0,80,[6,158,229,287,364,444,519]⟩]⟩
def row7_218 : State := ⟨[66,158,229,287,357,444,519,613],[]⟩
def row7_219 : State := ⟨[66,158,229,287,363,444,519,594],[]⟩
def row7_220 : State := ⟨[66,158,229,339,370,444,519,594],[⟨6,47,[40,66,158,229,444,519,594]⟩]⟩
def row7_221 : State := ⟨[66,158,229,287,364,444,519,671],[⟨0,80,[6,158,229,287,364,444,519]⟩]⟩
def row7_222 : State := ⟨[46,158,229,287,357,444,519,594],[]⟩
def row7_223 : State := ⟨[66,158,332,367,444,519,574,594],[]⟩
def row7_224 : State := ⟨[66,158,229,297,357,468,519,656],[]⟩
def row7_225 : State := ⟨[66,158,229,287,364,444,553,665],[⟨0,31,[66,158,229,287,364,444,521]⟩]⟩
def row7_226 : State := ⟨[10,66,158,229,287,357,444,521],[⟨0,31,[66,158,229,287,364,444,521]⟩]⟩
def row7_227 : State := ⟨[66,158,229,297,357,444,519,656],[]⟩
def row7_228 : State := ⟨[66,158,229,287,357,444,536,611],[]⟩
def row7_229 : State := ⟨[66,158,229,292,362,444,519,594],[]⟩
def row7_230 : State := ⟨[66,158,229,292,357,444,519,596],[]⟩
def row7_231 : State := ⟨[66,158,229,292,357,447,519,594],[]⟩
def row7_232 : State := ⟨[12,66,163,229,287,357,444,519],[⟨4,81,[66,163,229,287,366,444,519]⟩]⟩
def row7_233 : State := ⟨[66,158,229,287,357,444,533,603],[]⟩
def row7_234 : State := ⟨[66,158,229,290,360,444,519,594],[]⟩
def row7_235 : State := ⟨[66,158,229,290,357,445,519,594],[]⟩
def row7_236 : State := ⟨[66,158,229,290,357,444,520,594],[]⟩
def row7_237 : State := ⟨[66,158,229,290,357,444,519,597],[]⟩
def row7_238 : State := ⟨[66,158,229,287,360,444,520,594],[]⟩
def row7_239 : State := ⟨[66,158,229,287,360,444,519,597],[]⟩
def row7_240 : State := ⟨[66,158,229,287,357,444,521,596],[]⟩
def row7_241 : State := ⟨[66,158,229,287,357,444,520,597],[]⟩
def row7_242 : State := ⟨[2,66,158,229,287,367,444,594],[⟨4,31,[66,158,229,287,367,445,594]⟩,⟨2,82,[66,158,229,287,367,444,597]⟩]⟩
def row7_243 : State := ⟨[10,66,158,229,287,357,444,522],[⟨0,82,[66,158,229,287,364,444,522]⟩]⟩
def row7_244 : State := ⟨[2,162,229,287,357,444,519,594],[]⟩
def row7_245 : State := ⟨[12,66,229,270,287,357,444,519],[]⟩
def row7_246 : State := ⟨[0,66,158,229,322,370,519,594],[⟨0,83,[66,158,229,322,370,520,594]⟩,⟨0,84,[66,158,229,322,370,519,595]⟩]⟩
def row7_247 : State := ⟨[10,66,229,270,287,357,446,519],[⟨4,83,[66,229,270,287,364,446,519]⟩]⟩
def row7_248 : State := ⟨[10,66,229,270,287,357,444,521],[⟨4,84,[66,229,270,287,364,444,521]⟩]⟩
def row7_249 : State := ⟨[66,123,236,287,357,444,519,594],[]⟩
def row7_250 : State := ⟨[66,123,229,294,357,444,519,594],[]⟩
def row7_251 : State := ⟨[66,158,332,357,498,580,588,594],[⟨0,85,[66,158,332,357,432,588,594]⟩]⟩
def row7_252 : State := ⟨[66,158,229,287,357,432,588,594],[⟨0,85,[66,158,332,357,432,588,594]⟩]⟩
def row7_253 : State := ⟨[66,158,332,367,444,519,580,594],[]⟩
def row7_254 : State := ⟨[66,158,229,297,357,480,519,656],[]⟩
def row7_255 : State := ⟨[66,158,229,287,364,444,563,665],[]⟩
def row7_256 : State := ⟨[66,158,332,367,444,519,578,594],[⟨1,50,[66,158,307,367,444,519,594]⟩]⟩
def row7_257 : State := ⟨[13,68,158,229,287,357,444,519],[⟨7,50,[68,158,229,287,357,451,519]⟩,⟨6,86,[68,158,229,287,357,444,529]⟩]⟩
def row7_258 : State := ⟨[66,158,229,322,370,519,588,594],[]⟩
def row7_259 : State := ⟨[10,66,229,322,370,444,519,594],[⟨8,87,[68,229,322,370,444,519,594]⟩,⟨2,88,[66,229,322,372,444,519,594]⟩,⟨4,89,[66,229,322,370,450,519,594]⟩,⟨0,90,[10,66,229,322,370,519,656]⟩]⟩
def row7_260 : State := ⟨[66,158,229,322,370,519,594,656],[⟨0,90,[10,66,229,322,370,519,656]⟩]⟩
def row7_261 : State := ⟨[68,158,229,287,364,444,519,656],[]⟩
def row7_262 : State := ⟨[66,158,246,332,370,444,519,594],[]⟩
def row7_263 : State := ⟨[66,158,246,322,370,444,519,594],[]⟩
def row7_264 : State := ⟨[66,158,229,322,370,444,538,594],[]⟩
def row7_265 : State := ⟨[66,158,229,322,370,444,519,615],[]⟩
def row7_266 : State := ⟨[66,158,229,322,357,444,538,615],[]⟩
def row7_267 : State := ⟨[66,158,229,297,364,444,519,665],[]⟩
def row7_268 : State := ⟨[66,158,229,297,357,450,519,665],[]⟩
def row7_269 : State := ⟨[10,66,166,229,287,357,444,665],[⟨8,89,[68,166,229,287,357,444,665]⟩,⟨3,91,[66,166,239,287,357,444,665]⟩,⟨4,92,[66,166,229,287,364,444,665]⟩]⟩
def row7_270 : State := ⟨[66,158,229,297,364,444,519,656],[]⟩
def row7_271 : State := ⟨[66,158,229,297,357,450,519,656],[]⟩
def row7_272 : State := ⟨[66,158,229,297,357,444,526,656],[]⟩
def row7_273 : State := ⟨[10,22,66,270,287,357,444,665],[⟨0,93,[25,66,270,287,357,444,665]⟩,⟨7,90,[22,68,270,287,357,444,665]⟩,⟨10,90,[10,72,270,287,357,444,665]⟩,⟨4,90,[22,66,270,287,364,444,665]⟩,⟨1,90,[10,66,270,287,367,444,665]⟩]⟩
def row7_274 : State := ⟨[10,66,158,229,287,367,444,665],[⟨0,87,[68,158,229,287,367,444,665]⟩,⟨1,92,[66,158,239,287,367,444,665]⟩,⟨1,90,[10,66,270,287,367,444,665]⟩,⟨0,94,[66,158,229,287,369,444,665]⟩]⟩
def row7_275 : State := ⟨[66,158,229,287,364,444,551,665],[⟨9,6,[29,66,158,287,364,444,665]⟩]⟩
def row7_276 : State := ⟨[66,158,229,287,364,444,526,665],[]⟩
def row7_277 : State := ⟨[66,158,229,287,364,444,526,656],[]⟩
def row7_278 : State := ⟨[25,66,158,229,287,357,444,665],[⟨6,88,[73,158,229,287,357,444,665]⟩,⟨0,93,[25,66,270,287,357,444,665]⟩,⟨0,94,[66,158,229,287,369,444,665]⟩]⟩
def row7_279 : State := ⟨[66,158,229,289,357,444,547,594],[]⟩
def row7_280 : State := ⟨[66,158,229,288,357,464,519,594],[]⟩
def row7_281 : State := ⟨[66,158,229,287,357,444,521,623],[]⟩
def row7_282 : State := ⟨[66,158,229,287,358,444,519,595],[]⟩
def row7_283 : State := ⟨[66,158,229,287,357,444,520,595],[]⟩
def row7_284 : State := ⟨[47,68,229,287,357,444,519,594],[⟨11,31,[68,236,287,357,444,519,594]⟩,⟨10,31,[68,229,294,357,444,519,594]⟩]⟩
def row7_285 : State := ⟨[66,158,229,287,357,444,523,609],[]⟩
def row7_286 : State := ⟨[66,158,229,287,357,444,523,600],[]⟩
def row7_287 : State := ⟨[66,158,229,289,358,444,519,594],[]⟩
def row7_288 : State := ⟨[66,158,229,289,357,444,520,594],[]⟩
def row7_289 : State := ⟨[66,158,229,289,357,444,519,595],[]⟩
def row7_290 : State := ⟨[66,158,229,287,357,444,535,609],[]⟩
def row7_291 : State := ⟨[66,158,229,287,357,444,523,598],[]⟩
def row7_292 : State := ⟨[66,158,229,289,359,444,519,594],[]⟩
def row7_293 : State := ⟨[66,158,229,289,357,445,519,594],[]⟩
def row7_294 : State := ⟨[66,158,229,289,357,444,519,596],[]⟩
def row7_295 : State := ⟨[66,158,229,287,357,444,532,609],[]⟩
def row7_296 : State := ⟨[66,158,229,289,361,444,519,594],[]⟩
def row7_297 : State := ⟨[66,158,229,289,357,446,519,594],[]⟩
def row7_298 : State := ⟨[66,158,229,289,357,444,521,594],[]⟩
def row7_299 : State := ⟨[66,158,229,289,357,448,519,594],[]⟩
def row7_300 : State := ⟨[66,158,229,289,357,444,519,609],[]⟩
def row7_301 : State := ⟨[66,158,229,288,357,444,519,600],[]⟩
def row7_302 : State := ⟨[66,158,229,287,358,444,519,600],[]⟩
def row7_303 : State := ⟨[66,158,229,287,357,444,520,600],[]⟩
def row7_304 : State := ⟨[66,158,229,287,357,444,519,601],[]⟩
def row7_305 : State := ⟨[66,158,229,289,364,444,519,594],[]⟩
def row7_306 : State := ⟨[66,158,229,289,357,450,519,594],[]⟩
def row7_307 : State := ⟨[66,158,229,289,357,444,526,594],[]⟩
def row7_308 : State := ⟨[66,158,229,287,364,444,535,594],[]⟩
def row7_309 : State := ⟨[66,158,229,287,357,444,523,615],[]⟩
def row7_310 : State := ⟨[66,158,229,287,357,444,519,614],[]⟩
def row7_311 : State := ⟨[66,158,229,289,357,454,519,594],[]⟩
def row7_312 : State := ⟨[66,158,229,289,357,444,519,600],[]⟩
def row7_313 : State := ⟨[66,158,229,288,357,444,519,609],[]⟩
def row7_314 : State := ⟨[66,158,229,287,358,444,519,609],[]⟩
def row7_315 : State := ⟨[66,158,229,287,357,444,520,609],[]⟩
def row7_316 : State := ⟨[66,158,229,287,357,444,519,602],[]⟩
def row7_317 : State := ⟨[66,158,229,289,367,444,519,594],[]⟩
def row7_318 : State := ⟨[66,158,229,289,357,456,519,594],[]⟩
def row7_319 : State := ⟨[66,158,229,289,357,444,519,604],[]⟩
def row7_320 : State := ⟨[66,158,229,287,364,444,523,594],[]⟩
def row7_321 : State := ⟨[66,158,229,287,357,444,535,615],[]⟩
def row7_322 : State := ⟨[66,158,229,289,357,444,535,594],[]⟩
def row7_323 : State := ⟨[66,158,229,288,357,448,519,594],[]⟩
def row7_324 : State := ⟨[66,158,229,287,358,448,519,594],[]⟩
def row7_325 : State := ⟨[66,158,229,287,357,444,521,609],[]⟩
def row7_326 : State := ⟨[66,158,229,287,357,444,521,600],[]⟩
def row7_327 : State := ⟨[66,158,229,289,370,444,519,594],[]⟩
def row7_328 : State := ⟨[66,158,229,289,357,444,538,594],[]⟩
def row7_329 : State := ⟨[66,158,229,289,357,444,519,615],[]⟩
def row7_330 : State := ⟨[66,158,229,287,364,444,519,600],[]⟩
def row7_331 : State := ⟨[66,158,229,287,357,444,526,609],[]⟩
def row7_332 : State := ⟨[66,158,229,287,357,444,523,604],[]⟩
def row7_333 : State := ⟨[66,125,229,287,357,448,519,594],[]⟩
def row7_334 : State := ⟨[66,158,229,287,357,448,523,598],[]⟩
def row7_335 : State := ⟨[66,158,233,291,361,444,519,594],[]⟩
def row7_336 : State := ⟨[66,158,229,294,357,448,523,594],[]⟩
def row7_337 : State := ⟨[12,66,162,229,291,357,444,519],[⟨4,95,[66,162,229,291,366,444,519]⟩]⟩
def row7_338 : State := ⟨[66,158,230,288,358,444,519,594],[]⟩
def row7_339 : State := ⟨[66,158,229,294,357,448,519,598],[]⟩
def row7_340 : State := ⟨[66,158,229,294,357,444,523,598],[]⟩
def row7_341 : State := ⟨[10,66,158,229,291,361,444,519],[⟨2,48,[66,158,229,291,366,444,519]⟩]⟩
def row7_342 : State := ⟨[66,158,229,289,359,445,519,594],[]⟩
def row7_343 : State := ⟨[66,158,229,289,359,444,519,596],[]⟩
def row7_344 : State := ⟨[0,66,158,230,287,370,519,594],[⟨1,48,[66,158,230,287,371,519,594]⟩,⟨1,96,[66,158,230,287,370,520,594]⟩,⟨1,97,[66,158,230,287,370,519,595]⟩]⟩
def row7_345 : State := ⟨[10,66,158,229,291,357,446,519],[⟨2,96,[66,158,229,291,364,446,519]⟩]⟩
def row7_346 : State := ⟨[10,66,158,229,291,357,444,521],[⟨2,97,[66,158,229,291,364,444,521]⟩]⟩
def row7_347 : State := ⟨[66,158,229,289,357,445,519,596],[]⟩
def row7_348 : State := ⟨[66,158,229,288,358,444,519,594],[]⟩
def row7_349 : State := ⟨[66,158,229,288,357,444,519,595],[]⟩
def row7_350 : State := ⟨[66,158,229,287,357,444,532,598],[]⟩
def row7_351 : State := ⟨[66,158,229,288,359,444,519,594],[]⟩
def row7_352 : State := ⟨[66,158,229,288,357,445,519,594],[]⟩
def row7_353 : State := ⟨[66,158,229,288,357,444,519,596],[]⟩
def row7_354 : State := ⟨[66,158,229,288,357,444,519,598],[]⟩
def row7_355 : State := ⟨[66,158,229,287,358,444,519,598],[]⟩
def row7_356 : State := ⟨[66,158,229,287,357,444,520,598],[]⟩
def row7_357 : State := ⟨[66,158,229,287,357,444,519,599],[]⟩
def row7_358 : State := ⟨[66,158,229,288,364,444,519,594],[]⟩
def row7_359 : State := ⟨[66,158,229,288,357,450,519,594],[]⟩
def row7_360 : State := ⟨[66,158,229,288,357,444,519,604],[]⟩
def row7_361 : State := ⟨[66,158,229,287,364,444,532,594],[]⟩
def row7_362 : State := ⟨[66,158,229,287,357,444,532,615],[]⟩
def row7_363 : State := ⟨[66,158,229,287,357,444,519,607],[]⟩
def row7_364 : State := ⟨[66,158,229,288,357,459,519,594],[⟨3,20,[38,66,158,229,357,519,594]⟩]⟩
def row7_365 : State := ⟨[66,158,229,287,358,459,519,594],[]⟩
def row7_366 : State := ⟨[66,158,229,287,357,444,521,598],[⟨10,2,[15,66,229,287,357,444,521]⟩]⟩
def row7_367 : State := ⟨[49,66,229,287,357,444,519,598],[⟨6,25,[69,229,287,357,444,519,598]⟩]⟩
def row7_368 : State := ⟨[66,91,229,287,357,444,519,598],[]⟩
def row7_369 : State := ⟨[66,125,229,287,357,444,519,598],[]⟩
def row7_370 : State := ⟨[66,158,229,288,370,444,519,594],[]⟩
def row7_371 : State := ⟨[66,158,229,288,357,444,519,615],[]⟩
def row7_372 : State := ⟨[66,158,229,287,357,444,526,598],[]⟩
def row7_373 : State := ⟨[12,66,162,229,287,361,444,519],[⟨4,25,[66,162,229,287,366,444,519]⟩]⟩
def row7_374 : State := ⟨[66,158,229,288,358,444,519,595],[]⟩
def row7_375 : State := ⟨[0,66,158,229,288,371,519,594],[⟨2,95,[66,159,229,288,371,519,594]⟩,⟨0,95,[66,158,230,288,371,519,594]⟩,⟨2,98,[66,158,229,288,371,520,594]⟩,⟨0,98,[66,158,229,288,371,519,595]⟩]⟩
def row7_376 : State := ⟨[12,66,162,229,287,357,444,521],[⟨4,98,[66,162,229,287,366,444,521]⟩]⟩
def row7_377 : State := ⟨[66,158,229,288,357,444,520,595],[]⟩
def row7_378 : State := ⟨[10,66,162,229,287,361,444,519],[⟨4,25,[66,162,229,287,366,444,519]⟩]⟩
def row7_379 : State := ⟨[0,66,158,229,288,370,519,594],[⟨0,25,[66,158,229,288,371,519,594]⟩,⟨2,99,[66,158,229,288,370,520,594]⟩,⟨0,99,[66,158,229,288,370,519,595]⟩]⟩
def row7_380 : State := ⟨[10,66,162,229,287,357,444,521],[⟨4,99,[66,162,229,287,364,444,521]⟩]⟩
def row7_381 : State := ⟨[67,158,229,287,358,444,519,594],[]⟩
def row7_382 : State := ⟨[66,158,229,294,359,444,519,594],[]⟩
def row7_383 : State := ⟨[66,158,229,294,358,444,519,594],[]⟩
def row7_384 : State := ⟨[67,158,229,287,361,444,519,594],[]⟩
def row7_385 : State := ⟨[66,158,229,294,361,444,519,594],[]⟩
def row7_386 : State := ⟨[49,67,229,287,357,444,519,594],[]⟩
def row7_387 : State := ⟨[67,158,229,287,364,444,519,594],[]⟩
def row7_388 : State := ⟨[66,158,229,297,361,444,519,594],[]⟩
def row7_389 : State := ⟨[66,158,229,287,358,444,519,615],[]⟩
def row7_390 : State := ⟨[66,158,229,287,358,445,519,594],[]⟩
def row7_391 : State := ⟨[66,158,229,287,358,444,519,596],[]⟩
def row7_392 : State := ⟨[67,158,229,287,367,444,519,594],[]⟩
def row7_393 : State := ⟨[66,158,229,297,359,444,519,594],[]⟩
def row7_394 : State := ⟨[66,158,229,297,358,444,519,594],[]⟩
def row7_395 : State := ⟨[66,158,229,287,365,444,519,594],[]⟩
def row7_396 : State := ⟨[66,158,229,287,358,450,519,594],[]⟩
def row7_397 : State := ⟨[66,158,229,287,358,444,519,604],[]⟩
def row7_398 : State := ⟨[10,66,158,229,287,361,444,521],[⟨0,49,[66,158,229,287,366,444,521]⟩]⟩
def row7_399 : State := ⟨[66,158,229,287,358,444,520,595],[]⟩
def row7_400 : State := ⟨[66,158,229,294,357,445,519,594],[]⟩
def row7_401 : State := ⟨[66,158,229,294,357,444,519,596],[]⟩
def row7_402 : State := ⟨[66,158,229,294,357,444,519,595],[]⟩
def row7_403 : State := ⟨[9,10,66,229,287,357,444,519],[⟨0,20,[17,66,229,287,357,444,519]⟩]⟩
def row7_404 : State := ⟨[0,35,66,158,244,357,519,594],[⟨3,2,[36,66,158,244,357,519,594]⟩,⟨3,100,[35,66,158,244,357,520,594]⟩,⟨3,101,[35,66,158,244,357,519,595]⟩]⟩
def row7_405 : State := ⟨[66,158,229,294,357,446,519,594],[⟨0,100,[10,66,229,294,357,446,519]⟩]⟩
def row7_406 : State := ⟨[66,158,229,294,357,444,521,594],[⟨0,101,[10,66,229,294,357,444,521]⟩]⟩
def row7_407 : State := ⟨[48,66,229,294,357,444,519,594],[⟨10,31,[68,229,294,357,444,519,594]⟩]⟩
def row7_408 : State := ⟨[0,76,158,229,287,370,519,594],[⟨5,102,[76,158,229,287,370,520,594]⟩,⟨3,102,[76,158,229,287,370,519,595]⟩]⟩
def row7_409 : State := ⟨[10,66,229,294,364,444,519,594],[⟨10,102,[68,229,294,364,444,519,594]⟩,⟨3,103,[66,239,294,364,444,519,594]⟩,⟨4,50,[66,229,300,364,444,519,594]⟩]⟩
def row7_410 : State := ⟨[0,76,158,229,287,357,519,615],[⟨7,103,[76,158,229,287,357,520,615]⟩,⟨9,50,[76,158,229,287,357,519,616]⟩]⟩
def row7_411 : State := ⟨[0,66,158,246,287,370,519,594],[⟨3,104,[66,158,246,287,370,520,594]⟩,⟨3,105,[66,158,246,287,370,519,595]⟩]⟩
def row7_412 : State := ⟨[10,66,158,229,297,357,446,519],[⟨0,104,[66,158,229,297,364,446,519]⟩,⟨0,51,[66,158,229,297,357,451,519]⟩]⟩
def row7_413 : State := ⟨[0,66,158,246,287,357,538,594],[⟨3,51,[66,158,246,287,357,539,594]⟩,⟨3,106,[66,158,246,287,357,538,595]⟩]⟩
def row7_414 : State := ⟨[10,66,158,229,297,357,444,521],[⟨0,105,[66,158,229,297,364,444,521]⟩,⟨0,106,[66,158,229,297,357,450,521]⟩]⟩
def row7_415 : State := ⟨[66,158,229,287,364,444,521],[⟨4,84,[66,229,270,287,364,444,521]⟩,⟨5,83,[66,229,287,322,364,444,521]⟩,⟨10,42,[15,66,229,287,364,444,521]⟩]⟩
def row7_416 : State := ⟨[66,158,229,287,364,444,446,519],[]⟩
def row7_417 : State := ⟨[0,66,158,229,287,370,519,595],[⟨4,96,[66,159,229,287,370,519,595]⟩,⟨1,97,[66,158,230,287,370,519,595]⟩,⟨0,99,[66,158,229,288,370,519,595]⟩,⟨3,49,[66,158,229,287,371,519,595]⟩,⟨3,107,[66,158,229,287,370,520,595]⟩]⟩
def row7_418 : State := ⟨[66,68,229,294,357,444,519,594],[⟨0,2,[12,66,229,294,357,444,519]⟩]⟩
def row7_419 : State := ⟨[10,66,158,229,287,364,444,521],[⟨0,102,[68,158,229,287,364,444,521]⟩,⟨1,104,[66,158,239,287,364,444,521]⟩,⟨0,105,[66,158,229,297,364,444,521]⟩,⟨1,108,[66,158,229,287,364,450,521]⟩,⟨0,52,[66,158,229,287,364,444,528]⟩]⟩
def row7_420 : State := ⟨[0,66,158,229,287,370,519,615],[⟨3,108,[66,158,229,287,370,520,615]⟩,⟨3,52,[66,158,229,287,370,519,616]⟩]⟩
def row7_421 : State := ⟨[10,66,158,229,287,357,446,526],[⟨8,103,[68,158,229,287,357,446,526]⟩,⟨1,106,[66,158,239,287,357,446,526]⟩,⟨0,108,[66,158,229,287,364,446,526]⟩]⟩
def row7_422 : State := ⟨[10,66,158,229,287,357,446,521],[⟨0,107,[66,158,229,287,364,446,521]⟩]⟩
def row7_423 : State := ⟨[66,158,229,294,364,444,519,594],[]⟩
def row7_424 : State := ⟨[66,158,229,294,357,450,519,594],[]⟩
def row7_425 : State := ⟨[66,158,229,294,357,444,526,594],[]⟩
def row7_426 : State := ⟨[66,158,229,287,364,444,521,594],[]⟩
def row7_427 : State := ⟨[66,158,229,287,357,444,520,615],[]⟩
def row7_428 : State := ⟨[66,158,229,287,357,444,520,596],[]⟩
def row7_429 : State := ⟨[66,158,229,294,367,444,519,594],[]⟩
def row7_430 : State := ⟨[66,158,229,294,357,456,519,594],[]⟩
def row7_431 : State := ⟨[66,158,229,294,357,444,519,604],[]⟩
def row7_432 : State := ⟨[66,158,229,287,364,444,520,594],[]⟩
def row7_433 : State := ⟨[66,158,229,287,357,444,521,615],[]⟩
def row7_434 : State := ⟨[66,158,229,287,357,444,519,605],[]⟩
def row7_435 : State := ⟨[66,89,229,294,357,444,519,594],[]⟩
def row7_436 : State := ⟨[66,158,229,294,370,444,519,594],[]⟩
def row7_437 : State := ⟨[66,158,229,294,357,444,538,594],[]⟩
def row7_438 : State := ⟨[66,158,229,294,357,444,519,615],[]⟩
def row7_439 : State := ⟨[66,158,229,287,364,444,519,595],[]⟩
def row7_440 : State := ⟨[66,158,229,287,357,444,521,604],[]⟩
def row7_441 : State := ⟨[66,158,229,287,357,444,520,604],[]⟩
def row7_442 : State := ⟨[66,91,236,287,357,444,519,594],[]⟩
def row7_443 : State := ⟨[6,158,229,287,357,444,519,595],[]⟩
def row7_444 : State := ⟨[66,89,236,287,357,444,519,594],[]⟩
def row7_445 : State := ⟨[66,158,229,287,364,436,444,519],[⟨1,31,[66,158,229,287,364,446,519]⟩]⟩
def row7_446 : State := ⟨[66,158,229,287,364,444,526,594],[]⟩
def row7_447 : State := ⟨[66,158,229,287,357,444,538,615],[]⟩
def row7_448 : State := ⟨[66,158,229,318,370,444,519,594],[]⟩
def row7_449 : State := ⟨[66,158,229,297,357,444,519,634],[]⟩
def row7_450 : State := ⟨[66,158,229,287,364,444,519,634],[]⟩
def row7_451 : State := ⟨[66,158,229,287,357,444,526,634],[]⟩
def row7_452 : State := ⟨[66,158,229,319,370,444,519,594],[]⟩
def row7_453 : State := ⟨[66,158,229,297,357,444,519,654],[]⟩
def row7_454 : State := ⟨[66,158,229,287,364,444,519,654],[]⟩
def row7_455 : State := ⟨[49,66,229,287,364,444,519,594],[⟨5,50,[66,242,287,364,444,519,594]⟩,⟨4,50,[66,229,300,364,444,519,594]⟩]⟩
def row7_456 : State := ⟨[49,68,229,287,357,444,519,594],[⟨11,52,[68,242,287,357,444,519,594]⟩,⟨10,52,[68,229,300,357,444,519,594]⟩]⟩
def row7_457 : State := ⟨[66,91,229,287,364,444,519,594],[⟨5,50,[66,242,287,364,444,519,594]⟩]⟩
def row7_458 : State := ⟨[68,158,229,287,367,444,519,594],[⟨9,87,[68,270,287,367,444,519,594]⟩,⟨0,87,[68,158,229,287,367,444,665]⟩]⟩
def row7_459 : State := ⟨[66,158,229,297,370,444,519,594],[⟨0,92,[66,158,229,297,370,519,656]⟩]⟩
def row7_460 : State := ⟨[66,158,229,297,367,444,519,594],[]⟩
def row7_461 : State := ⟨[66,158,229,287,369,444,519,594],[⟨3,88,[66,270,287,369,444,519,594]⟩,⟨0,94,[66,158,229,287,369,444,665]⟩]⟩
def row7_462 : State := ⟨[66,158,229,287,364,444,538,594],[]⟩
def row7_463 : State := ⟨[66,158,229,287,364,444,519,604],[⟨3,89,[66,270,287,364,444,519,604]⟩]⟩
def row7_464 : State := ⟨[66,125,229,287,364,444,519,594],[]⟩
def row7_465 : State := ⟨[68,158,229,287,364,444,519,594],[]⟩
def row7_466 : State := ⟨[66,158,229,297,364,444,519,594],[]⟩
def row7_467 : State := ⟨[12,68,158,229,287,364,444,519],[⟨1,109,[68,158,229,287,364,451,519]⟩,⟨0,109,[68,158,229,287,364,444,528]⟩]⟩
def row7_468 : State := ⟨[68,158,229,287,364,444,526,594],[]⟩
def row7_469 : State := ⟨[12,68,158,229,287,357,444,526],[⟨9,110,[68,158,229,287,357,451,526]⟩,⟨6,50,[68,158,229,287,357,444,528]⟩]⟩
def row7_470 : State := ⟨[66,158,239,297,364,444,519,594],[]⟩
def row7_471 : State := ⟨[66,158,229,297,364,450,519,594],[]⟩
def row7_472 : State := ⟨[66,158,229,297,364,444,526,594],[]⟩
def row7_473 : State := ⟨[12,68,158,229,297,357,444,519],[⟨7,111,[68,158,229,297,357,451,519]⟩,⟨6,112,[68,158,229,297,357,444,528]⟩]⟩
def row7_474 : State := ⟨[10,66,229,300,364,444,519,594],[⟨10,109,[68,229,300,364,444,519,594]⟩,⟨2,110,[66,239,300,364,444,519,594]⟩,⟨4,111,[66,229,300,364,450,519,594]⟩,⟨4,112,[66,229,300,364,444,526,594]⟩]⟩
def row7_475 : State := ⟨[66,158,229,287,364,450,526,594],[]⟩
def row7_476 : State := ⟨[66,158,229,297,357,456,519,594],[]⟩
def row7_477 : State := ⟨[66,158,229,297,357,444,519,604],[]⟩
def row7_478 : State := ⟨[66,158,229,287,357,444,526,615],[]⟩
def row7_479 : State := ⟨[66,158,229,287,357,444,519,617],[]⟩
def row7_480 : State := ⟨[66,158,229,297,357,450,519,594],[]⟩
def row7_481 : State := ⟨[66,158,229,297,357,444,526,594],[]⟩
def row7_482 : State := ⟨[66,91,239,287,357,444,519,594],[]⟩
def row7_483 : State := ⟨[66,158,229,297,357,444,519,615],[]⟩
def row7_484 : State := ⟨[66,158,229,287,357,444,526,604],[⟨6,91,[66,270,287,357,444,526,604]⟩]⟩
def row7_485 : State := ⟨[66,125,229,287,357,450,519,594],[]⟩
def row7_486 : State := ⟨[66,158,229,297,357,450,526,594],[]⟩
def layer7 : Array State := #[row7_0,row7_1,row7_2,row7_3,row7_4,row7_5,row7_6,row7_7,row7_8,row7_9,row7_10,row7_11,row7_12,row7_13,row7_14,row7_15,row7_16,row7_17,row7_18,row7_19,row7_20,row7_21,row7_22,row7_23,row7_24,row7_25,row7_26,row7_27,row7_28,row7_29,row7_30,row7_31,row7_32,row7_33,row7_34,row7_35,row7_36,row7_37,row7_38,row7_39,row7_40,row7_41,row7_42,row7_43,row7_44,row7_45,row7_46,row7_47,row7_48,row7_49,row7_50,row7_51,row7_52,row7_53,row7_54,row7_55,row7_56,row7_57,row7_58,row7_59,row7_60,row7_61,row7_62,row7_63,row7_64,row7_65,row7_66,row7_67,row7_68,row7_69,row7_70,row7_71,row7_72,row7_73,row7_74,row7_75,row7_76,row7_77,row7_78,row7_79,row7_80,row7_81,row7_82,row7_83,row7_84,row7_85,row7_86,row7_87,row7_88,row7_89,row7_90,row7_91,row7_92,row7_93,row7_94,row7_95,row7_96,row7_97,row7_98,row7_99,row7_100,row7_101,row7_102,row7_103,row7_104,row7_105,row7_106,row7_107,row7_108,row7_109,row7_110,row7_111,row7_112,row7_113,row7_114,row7_115,row7_116,row7_117,row7_118,row7_119,row7_120,row7_121,row7_122,row7_123,row7_124,row7_125,row7_126,row7_127,row7_128,row7_129,row7_130,row7_131,row7_132,row7_133,row7_134,row7_135,row7_136,row7_137,row7_138,row7_139,row7_140,row7_141,row7_142,row7_143,row7_144,row7_145,row7_146,row7_147,row7_148,row7_149,row7_150,row7_151,row7_152,row7_153,row7_154,row7_155,row7_156,row7_157,row7_158,row7_159,row7_160,row7_161,row7_162,row7_163,row7_164,row7_165,row7_166,row7_167,row7_168,row7_169,row7_170,row7_171,row7_172,row7_173,row7_174,row7_175,row7_176,row7_177,row7_178,row7_179,row7_180,row7_181,row7_182,row7_183,row7_184,row7_185,row7_186,row7_187,row7_188,row7_189,row7_190,row7_191,row7_192,row7_193,row7_194,row7_195,row7_196,row7_197,row7_198,row7_199,row7_200,row7_201,row7_202,row7_203,row7_204,row7_205,row7_206,row7_207,row7_208,row7_209,row7_210,row7_211,row7_212,row7_213,row7_214,row7_215,row7_216,row7_217,row7_218,row7_219,row7_220,row7_221,row7_222,row7_223,row7_224,row7_225,row7_226,row7_227,row7_228,row7_229,row7_230,row7_231,row7_232,row7_233,row7_234,row7_235,row7_236,row7_237,row7_238,row7_239,row7_240,row7_241,row7_242,row7_243,row7_244,row7_245,row7_246,row7_247,row7_248,row7_249,row7_250,row7_251,row7_252,row7_253,row7_254,row7_255,row7_256,row7_257,row7_258,row7_259,row7_260,row7_261,row7_262,row7_263,row7_264,row7_265,row7_266,row7_267,row7_268,row7_269,row7_270,row7_271,row7_272,row7_273,row7_274,row7_275,row7_276,row7_277,row7_278,row7_279,row7_280,row7_281,row7_282,row7_283,row7_284,row7_285,row7_286,row7_287,row7_288,row7_289,row7_290,row7_291,row7_292,row7_293,row7_294,row7_295,row7_296,row7_297,row7_298,row7_299,row7_300,row7_301,row7_302,row7_303,row7_304,row7_305,row7_306,row7_307,row7_308,row7_309,row7_310,row7_311,row7_312,row7_313,row7_314,row7_315,row7_316,row7_317,row7_318,row7_319,row7_320,row7_321,row7_322,row7_323,row7_324,row7_325,row7_326,row7_327,row7_328,row7_329,row7_330,row7_331,row7_332,row7_333,row7_334,row7_335,row7_336,row7_337,row7_338,row7_339,row7_340,row7_341,row7_342,row7_343,row7_344,row7_345,row7_346,row7_347,row7_348,row7_349,row7_350,row7_351,row7_352,row7_353,row7_354,row7_355,row7_356,row7_357,row7_358,row7_359,row7_360,row7_361,row7_362,row7_363,row7_364,row7_365,row7_366,row7_367,row7_368,row7_369,row7_370,row7_371,row7_372,row7_373,row7_374,row7_375,row7_376,row7_377,row7_378,row7_379,row7_380,row7_381,row7_382,row7_383,row7_384,row7_385,row7_386,row7_387,row7_388,row7_389,row7_390,row7_391,row7_392,row7_393,row7_394,row7_395,row7_396,row7_397,row7_398,row7_399,row7_400,row7_401,row7_402,row7_403,row7_404,row7_405,row7_406,row7_407,row7_408,row7_409,row7_410,row7_411,row7_412,row7_413,row7_414,row7_415,row7_416,row7_417,row7_418,row7_419,row7_420,row7_421,row7_422,row7_423,row7_424,row7_425,row7_426,row7_427,row7_428,row7_429,row7_430,row7_431,row7_432,row7_433,row7_434,row7_435,row7_436,row7_437,row7_438,row7_439,row7_440,row7_441,row7_442,row7_443,row7_444,row7_445,row7_446,row7_447,row7_448,row7_449,row7_450,row7_451,row7_452,row7_453,row7_454,row7_455,row7_456,row7_457,row7_458,row7_459,row7_460,row7_461,row7_462,row7_463,row7_464,row7_465,row7_466,row7_467,row7_468,row7_469,row7_470,row7_471,row7_472,row7_473,row7_474,row7_475,row7_476,row7_477,row7_478,row7_479,row7_480,row7_481,row7_482,row7_483,row7_484,row7_485,row7_486]
def row8_0 : State := ⟨[12,41,66,158,229,287,357,444,519],[]⟩
def row8_1 : State := ⟨[66,158,229,287,378,444,465,519,594],[⟨0,0,[66,158,229,287,357,444,519,594]⟩]⟩
def row8_2 : State := ⟨[41,66,158,229,287,357,444,519,594],[]⟩
def row8_3 : State := ⟨[66,158,229,287,357,423,444,519,594],[⟨10,1,[66,158,229,287,347,357,444,519]⟩]⟩
def row8_4 : State := ⟨[64,66,158,229,287,357,444,519,594],[]⟩
def row8_5 : State := ⟨[66,158,229,287,357,380,444,519,594],[]⟩
def row8_6 : State := ⟨[47,66,158,229,287,357,444,519,594],[⟨6,2,[67,158,229,287,357,444,519,594]⟩,⟨7,3,[66,158,236,287,357,444,519,594]⟩,⟨6,3,[66,158,229,294,357,444,519,594]⟩]⟩
def row8_7 : State := ⟨[66,158,229,287,357,425,444,519,594],[]⟩
def row8_8 : State := ⟨[41,66,158,229,287,357,444,519,600],[]⟩
def row8_9 : State := ⟨[41,66,158,229,287,357,444,519,598],[]⟩
def row8_10 : State := ⟨[41,67,158,229,287,357,444,519,594],[]⟩
def row8_11 : State := ⟨[41,66,158,229,294,357,444,519,594],[]⟩
def row8_12 : State := ⟨[66,158,229,287,357,444,519,620,625],[⟨0,0,[66,158,229,287,357,444,519,594]⟩]⟩
def row8_13 : State := ⟨[66,158,229,287,357,444,519,620,656],[⟨0,0,[66,158,229,287,357,444,519,594]⟩]⟩
def row8_14 : State := ⟨[66,85,158,229,287,357,444,519,594],[]⟩
def row8_15 : State := ⟨[66,158,229,287,357,444,502,519,594],[]⟩
def row8_16 : State := ⟨[42,66,158,229,287,357,444,519,594],[⟨10,4,[66,159,229,287,357,444,519,594]⟩,⟨7,4,[66,158,230,287,357,444,519,594]⟩,⟨6,5,[66,158,229,288,357,444,519,594]⟩]⟩
def row8_17 : State := ⟨[66,129,158,229,287,357,444,519,594],[]⟩
def row8_18 : State := ⟨[66,158,229,287,357,444,480,519,594],[]⟩
def row8_19 : State := ⟨[48,66,158,229,287,357,444,519,594],[⟨10,6,[68,158,229,287,357,444,519,594]⟩,⟨9,7,[66,158,239,287,357,444,519,594]⟩,⟨8,7,[66,158,229,297,357,444,519,594]⟩]⟩
def row8_20 : State := ⟨[66,158,229,287,357,444,519,594,674],[]⟩
def row8_21 : State := ⟨[41,66,158,229,289,357,444,519,594],[]⟩
def row8_22 : State := ⟨[41,66,158,229,288,357,444,519,594],[]⟩
def row8_23 : State := ⟨[41,66,158,229,287,358,444,519,594],[]⟩
def row8_24 : State := ⟨[41,66,158,229,287,357,444,519,595],[]⟩
def row8_25 : State := ⟨[41,68,158,229,287,357,444,519,594],[]⟩
def row8_26 : State := ⟨[41,66,158,229,297,357,444,519,594],[]⟩
def row8_27 : State := ⟨[41,66,158,229,287,364,444,519,594],[]⟩
def row8_28 : State := ⟨[41,66,158,229,287,357,444,519,604],[]⟩
def row8_29 : State := ⟨[66,158,229,287,352,357,444,519,594],[]⟩
def row8_30 : State := ⟨[12,66,158,229,287,341,357,444,519],[⟨10,1,[66,158,229,287,347,357,444,519]⟩]⟩
def row8_31 : State := ⟨[66,158,229,287,357,384,444,519,594],[]⟩
def row8_32 : State := ⟨[66,158,229,287,357,444,549,625,665],[⟨7,8,[29,66,158,287,357,444,625,665]⟩,⟨10,8,[15,66,229,287,357,444,549,665]⟩]⟩
def row8_33 : State := ⟨[66,98,158,229,287,357,444,519,594],[]⟩
def row8_34 : State := ⟨[66,158,229,278,287,357,444,519,594],[⟨7,9,[66,146,158,229,287,357,444,594]⟩,⟨10,9,[66,158,223,229,287,357,444,519]⟩]⟩
def row8_35 : State := ⟨[12,66,158,229,253,287,357,444,519],[⟨1,8,[12,66,253,270,287,357,444,519]⟩,⟨0,10,[12,23,66,158,229,287,357,444]⟩]⟩
def row8_36 : State := ⟨[12,66,85,158,229,287,357,444,519],[]⟩
def row8_37 : State := ⟨[66,158,229,287,380,444,519,625,656],[]⟩
def row8_38 : State := ⟨[66,158,229,287,425,444,519,625,656],[⟨0,11,[66,158,229,287,364,444,519,656]⟩]⟩
def row8_39 : State := ⟨[66,158,229,287,357,444,549,629,665],[⟨7,12,[29,66,158,287,357,444,629,665]⟩,⟨2,13,[66,158,229,287,357,444,549,596]⟩]⟩
def row8_40 : State := ⟨[66,158,229,287,357,444,549,637,665],[⟨7,14,[29,66,158,287,357,444,637,665]⟩]⟩
def row8_41 : State := ⟨[10,66,158,229,287,357,444,549,665],[⟨6,15,[68,158,229,287,357,444,549,665]⟩,⟨1,16,[66,158,239,287,357,444,549,665]⟩,⟨0,17,[66,158,229,287,364,444,549,665]⟩,⟨11,18,[10,29,66,158,287,357,444,665]⟩]⟩
def row8_42 : State := ⟨[66,158,229,287,357,444,519,633,656],[⟨0,19,[49,66,229,287,357,444,519,656]⟩,⟨0,3,[66,158,229,287,357,444,519,595]⟩]⟩
def row8_43 : State := ⟨[12,66,229,270,287,357,444,519],[⟨0,20,[12,68,229,270,287,357,444,519]⟩,⟨1,21,[12,66,241,270,287,357,444,519]⟩,⟨1,8,[12,66,253,270,287,357,444,519]⟩,⟨0,22,[12,66,229,273,287,357,444,519]⟩,⟨0,23,[12,66,229,270,299,357,444,519]⟩,⟨0,24,[12,66,229,287,339,357,444,519]⟩,⟨0,25,[12,66,229,270,287,366,444,519]⟩,⟨1,12,[12,66,270,287,357,444,494,519]⟩,⟨8,26,[12,21,66,229,287,357,444,519]⟩,⟨0,27,[12,66,229,270,287,357,451,519]⟩,⟨0,28,[12,66,229,270,287,357,444,528]⟩,⟨2,18,[12,22,66,270,287,357,444,519]⟩]⟩
def row8_44 : State := ⟨[12,66,177,229,270,287,357,444,519],[⟨0,29,[12,66,158,229,287,357,444,519]⟩]⟩
def row8_45 : State := ⟨[12,66,229,270,287,357,444,519,594],[⟨10,11,[68,229,270,287,357,444,519,594]⟩,⟨4,30,[66,229,270,287,366,444,519,594]⟩,⟨10,31,[66,229,270,287,357,444,528,594]⟩,⟨1,14,[12,66,270,287,357,444,519,637]⟩]⟩
def row8_46 : State := ⟨[66,158,229,287,357,444,519,643,665],[⟨0,32,[66,91,229,287,357,444,519,665]⟩,⟨0,7,[66,158,229,287,357,444,519,604]⟩]⟩
def row8_47 : State := ⟨[2,66,158,229,287,357,444,549,594],[⟨4,33,[66,161,229,287,357,444,549,594]⟩,⟨1,34,[66,158,232,287,357,444,549,594]⟩,⟨0,35,[66,158,229,290,357,444,549,594]⟩,⟨4,13,[66,158,229,287,357,445,549,594]⟩,⟨0,26,[2,29,66,158,287,357,444,594]⟩,⟨2,36,[66,158,229,287,357,444,549,597]⟩]⟩
def row8_48 : State := ⟨[66,158,229,287,357,444,519,625,680],[⟨0,5,[66,158,229,287,357,444,519,598]⟩]⟩
def row8_49 : State := ⟨[66,158,229,287,357,444,519,625,661],[⟨0,4,[66,158,229,287,357,444,519,600]⟩]⟩
def row8_50 : State := ⟨[66,158,229,287,357,444,519,625,683],[⟨0,4,[66,158,229,287,357,444,519,600]⟩]⟩
def row8_51 : State := ⟨[66,158,229,287,357,444,519,625,671],[⟨10,24,[15,66,229,287,357,444,519,671]⟩,⟨0,37,[6,158,229,287,357,444,519,625]⟩,⟨0,0,[66,158,229,287,357,444,519,594]⟩]⟩
def row8_52 : State := ⟨[66,158,229,287,357,444,519,594],[]⟩
def row8_53 : State := ⟨[66,158,229,270,287,357,444,519,594],[]⟩
def row8_54 : State := ⟨[66,158,177,229,287,357,444,519,594],[⟨0,29,[12,66,158,229,287,357,444,519]⟩]⟩
def row8_55 : State := ⟨[12,66,158,229,270,287,357,444,519],[]⟩
def row8_56 : State := ⟨[66,158,196,229,287,357,444,519,594],[]⟩
def row8_57 : State := ⟨[66,158,229,287,357,387,444,519,594],[]⟩
def row8_58 : State := ⟨[66,78,158,229,287,357,444,519,594],[]⟩
def row8_59 : State := ⟨[66,158,229,287,357,415,444,519,594],[]⟩
def row8_60 : State := ⟨[66,158,229,287,357,444,475,519,594],[]⟩
def row8_61 : State := ⟨[66,108,158,229,287,357,444,519,594],[]⟩
def row8_62 : State := ⟨[66,158,229,287,340,357,444,519,594],[⟨6,38,[62,66,158,229,287,444,519,594]⟩,⟨6,39,[66,158,209,229,287,357,519,594]⟩,⟨7,39,[66,158,229,283,287,357,444,594]⟩,⟨10,39,[66,158,229,287,331,357,444,519]⟩]⟩
def row8_63 : State := ⟨[66,158,229,287,380,444,519,592,594],[⟨0,40,[66,158,229,287,360,444,519,594]⟩]⟩
def row8_64 : State := ⟨[56,66,158,229,287,357,444,519,594],[⟨0,40,[66,158,229,287,360,444,519,594]⟩]⟩
def row8_65 : State := ⟨[66,158,229,287,357,444,508,519,594],[⟨7,41,[66,158,229,287,357,413,444,594]⟩,⟨10,41,[66,158,229,287,357,444,492,519]⟩]⟩
def row8_66 : State := ⟨[66,150,158,229,287,357,444,519,594],[]⟩
def row8_67 : State := ⟨[66,158,229,287,357,444,509,519,594],[⟨7,41,[66,158,229,287,357,413,444,594]⟩,⟨10,41,[66,158,229,287,357,444,492,519]⟩]⟩
def row8_68 : State := ⟨[66,158,229,287,357,444,519,637,669],[⟨0,42,[66,158,229,287,357,444,519,608]⟩]⟩
def row8_69 : State := ⟨[66,125,229,287,357,444,519,594],[⟨0,43,[66,125,229,287,357,452,519,594]⟩]⟩
def row8_70 : State := ⟨[66,125,158,229,287,357,444,519,594],[⟨3,42,[66,158,229,287,357,452,519,594]⟩]⟩
def row8_71 : State := ⟨[66,125,229,287,357,444,519,594,662],[⟨0,44,[66,125,229,285,357,444,519,594]⟩]⟩
def row8_72 : State := ⟨[66,158,229,287,357,444,519,594,706],[]⟩
def row8_73 : State := ⟨[66,125,229,287,357,444,465,519,594],[⟨6,45,[37,66,125,229,357,444,519,594]⟩]⟩
def row8_74 : State := ⟨[12,66,158,229,278,287,357,444,519],[⟨1,45,[12,66,146,158,229,287,357,444]⟩]⟩
def row8_75 : State := ⟨[66,125,229,287,357,444,519,594,625],[⟨10,29,[15,66,229,287,357,444,519,594]⟩]⟩
def row8_76 : State := ⟨[66,158,229,287,396,444,519,594,625],[⟨10,46,[15,66,229,287,396,444,519,594]⟩,⟨0,0,[66,158,229,287,357,444,519,594]⟩]⟩
def row8_77 : State := ⟨[66,158,229,287,357,444,519,625,653],[⟨10,47,[15,66,229,287,357,444,519,653]⟩,⟨0,0,[66,158,229,287,357,444,519,594]⟩]⟩
def row8_78 : State := ⟨[66,158,199,229,287,357,444,519,594],[⟨4,48,[66,158,182,229,287,357,444,519]⟩]⟩
def row8_79 : State := ⟨[12,66,158,183,229,287,357,444,519],[⟨0,46,[12,158,186,229,287,357,444,519]⟩,⟨0,47,[12,66,196,229,287,357,444,519]⟩]⟩
def row8_80 : State := ⟨[12,66,158,229,287,332,357,444,519],[⟨0,24,[12,66,229,287,339,357,444,519]⟩]⟩
def row8_81 : State := ⟨[12,54,66,158,229,287,357,444,519],[]⟩
def row8_82 : State := ⟨[158,177,229,287,380,444,465,519,594],[⟨5,49,[177,229,287,380,465,480,519,594]⟩]⟩
def row8_83 : State := ⟨[158,177,229,287,380,444,519,594,625],[⟨4,50,[177,229,287,380,444,519,625,674]⟩]⟩
def row8_84 : State := ⟨[66,158,229,287,428,444,519,594,625],[⟨0,51,[66,158,229,287,366,444,519,594]⟩]⟩
def row8_85 : State := ⟨[0,66,158,229,287,380,465,519,594],[⟨4,52,[66,159,229,287,380,465,519,594]⟩,⟨1,52,[66,158,230,287,380,465,519,594]⟩,⟨0,53,[66,158,229,288,380,465,519,594]⟩,⟨5,54,[66,158,229,287,380,465,520,594]⟩,⟨3,54,[66,158,229,287,380,465,519,595]⟩]⟩
def row8_86 : State := ⟨[66,158,229,287,380,444,519,625,637],[⟨1,49,[158,253,287,380,444,519,625,637]⟩]⟩
def row8_87 : State := ⟨[66,158,229,287,380,444,519,625,674],[⟨4,50,[177,229,287,380,444,519,625,674]⟩]⟩
def row8_88 : State := ⟨[47,177,229,287,357,380,444,519,594],[⟨11,54,[177,236,287,357,380,444,519,594]⟩,⟨10,54,[177,229,294,357,380,444,519,594]⟩]⟩
def row8_89 : State := ⟨[12,158,177,229,287,357,380,444,519],[⟨0,55,[12,67,158,229,287,357,444,519]⟩]⟩
def row8_90 : State := ⟨[66,158,229,287,358,444,519,594],[]⟩
def row8_91 : State := ⟨[66,158,229,287,358,444,465,519,594],[⟨6,55,[37,66,158,229,358,444,519,594]⟩]⟩
def row8_92 : State := ⟨[66,158,229,287,358,380,444,519,594],[]⟩
def row8_93 : State := ⟨[47,66,177,229,287,357,444,519,594],[⟨11,13,[66,177,236,287,357,444,519,594]⟩,⟨10,13,[66,177,229,294,357,444,519,594]⟩,⟨0,56,[12,47,66,229,287,357,444,519]⟩]⟩
def row8_94 : State := ⟨[66,67,158,229,287,357,444,519,594],[]⟩
def row8_95 : State := ⟨[66,158,229,287,357,428,444,519,594],[⟨10,1,[66,158,229,287,347,357,444,519]⟩]⟩
def row8_96 : State := ⟨[12,66,158,229,287,357,380,444,519],[⟨0,56,[12,47,66,229,287,357,444,519]⟩]⟩
def row8_97 : State := ⟨[66,158,229,289,357,444,549,594],[⟨0,52,[66,158,229,289,380,444,549,594]⟩,⟨0,57,[66,158,229,289,444,494,549,594]⟩,⟨7,58,[29,66,158,289,357,444,549,594]⟩]⟩
def row8_98 : State := ⟨[66,158,159,229,287,357,465,519,594],[]⟩
def row8_99 : State := ⟨[0,66,158,230,287,357,465,519,594],[⟨9,59,[66,159,230,287,357,465,519,594]⟩,⟨9,60,[66,158,230,288,357,465,519,594]⟩,⟨1,61,[66,158,230,287,358,465,519,594]⟩,⟨0,62,[0,37,66,158,230,357,519,594]⟩,⟨1,63,[66,158,230,287,357,465,520,594]⟩,⟨1,64,[66,158,230,287,357,465,519,595]⟩]⟩
def row8_100 : State := ⟨[66,158,229,288,357,465,519,594],[⟨0,53,[66,158,229,288,380,465,519,594]⟩,⟨0,65,[66,158,229,288,465,519,575,594]⟩,⟨3,66,[38,66,158,229,357,519,594]⟩,⟨6,67,[38,66,158,229,357,465,519,594]⟩,⟨3,68,[38,66,158,229,288,357,519,594]⟩]⟩
def row8_101 : State := ⟨[66,158,162,229,287,357,444,519,625],[⟨4,69,[66,162,229,287,425,444,519,625]⟩,⟨0,70,[17,66,158,229,287,357,444,519]⟩]⟩
def row8_102 : State := ⟨[0,66,158,229,288,357,465,519,594],[⟨11,60,[66,159,229,288,357,465,519,594]⟩,⟨9,60,[66,158,230,288,357,465,519,594]⟩,⟨0,71,[66,158,229,288,358,465,519,594]⟩,⟨0,72,[0,38,66,158,229,357,519,594]⟩,⟨2,73,[66,158,229,288,357,465,520,594]⟩,⟨0,73,[66,158,229,288,357,465,519,595]⟩]⟩
def row8_103 : State := ⟨[0,66,158,229,287,358,465,519,594],[⟨4,61,[66,159,229,287,358,465,519,594]⟩,⟨1,61,[66,158,230,287,358,465,519,594]⟩,⟨0,71,[66,158,229,288,358,465,519,594]⟩,⟨0,74,[0,37,66,158,229,358,519,594]⟩,⟨2,75,[66,158,229,287,358,465,520,594]⟩,⟨0,75,[66,158,229,287,358,465,519,595]⟩]⟩
def row8_104 : State := ⟨[0,66,158,229,287,465,519,574,594],[⟨4,57,[66,159,229,287,465,519,574,594]⟩,⟨1,57,[66,158,230,287,465,519,574,594]⟩,⟨0,69,[66,158,229,288,465,519,574,594]⟩,⟨5,76,[66,158,229,287,465,520,574,594]⟩,⟨0,77,[0,66,158,229,287,370,519,594]⟩,⟨3,76,[66,158,229,287,465,519,574,595]⟩]⟩
def row8_105 : State := ⟨[0,37,66,158,229,357,519,594],[⟨3,66,[38,66,158,229,357,519,594]⟩,⟨6,78,[37,38,66,158,229,357,519,594]⟩,⟨0,72,[0,38,66,158,229,357,519,594]⟩,⟨0,79,[0,37,77,158,229,357,519,594]⟩,⟨2,62,[0,37,66,159,229,357,519,594]⟩,⟨2,80,[0,37,66,172,229,357,519,594]⟩,⟨0,62,[0,37,66,158,230,357,519,594]⟩,⟨0,80,[0,37,66,158,248,357,519,594]⟩,⟨0,74,[0,37,66,158,229,358,519,594]⟩,⟨0,81,[0,37,66,158,229,370,519,594]⟩,⟨8,82,[37,66,158,229,357,520,594]⟩,⟨6,83,[37,66,158,229,357,519,520,594]⟩,⟨2,84,[0,37,66,158,229,357,520,594]⟩,⟨2,85,[0,37,66,158,229,357,541,594]⟩,⟨6,82,[37,66,158,229,357,519,595]⟩,⟨8,83,[37,66,158,229,357,519,594,595]⟩,⟨0,84,[0,37,66,158,229,357,519,595]⟩,⟨0,85,[0,37,66,158,229,357,519,618]⟩]⟩
def row8_106 : State := ⟨[0,37,66,158,229,357,465,519,594],[⟨6,67,[38,66,158,229,357,465,519,594]⟩,⟨8,58,[37,66,159,229,357,465,519,594]⟩,⟨6,58,[37,66,158,230,357,465,519,594]⟩,⟨8,86,[37,66,158,229,357,465,520,594]⟩,⟨6,86,[37,66,158,229,357,465,519,595]⟩]⟩
def row8_107 : State := ⟨[0,37,66,158,229,287,357,519,594],[⟨3,70,[38,66,158,229,287,357,519,594]⟩,⟨0,77,[0,66,158,229,287,370,519,594]⟩,⟨8,87,[37,66,158,229,287,357,520,594]⟩,⟨6,87,[37,66,158,229,287,357,519,595]⟩]⟩
def row8_108 : State := ⟨[66,158,229,287,357,444,521,625],[⟨0,54,[66,158,229,287,380,444,521,625]⟩,⟨0,76,[66,158,229,287,425,444,521,625]⟩,⟨10,82,[15,66,229,287,357,444,521]⟩,⟨10,86,[15,66,229,287,357,444,521,625]⟩,⟨10,87,[15,66,158,229,287,357,444,521]⟩]⟩
def row8_109 : State := ⟨[66,158,165,253,287,357,444,519,594],[⟨2,83,[23,66,158,165,287,357,444,594]⟩]⟩
def row8_110 : State := ⟨[0,66,158,229,287,357,465,519,595],[⟨4,63,[66,159,229,287,357,465,519,595]⟩,⟨1,64,[66,158,230,287,357,465,519,595]⟩,⟨0,73,[66,158,229,288,357,465,519,595]⟩,⟨0,75,[66,158,229,287,358,465,519,595]⟩,⟨0,84,[0,37,66,158,229,357,519,595]⟩,⟨1,88,[66,158,229,287,357,465,520,595]⟩]⟩
def row8_111 : State := ⟨[66,158,177,229,287,357,444,523,594],[⟨0,89,[12,66,158,229,287,357,444,523]⟩]⟩
def row8_112 : State := ⟨[66,158,177,229,287,357,444,519,598],[⟨0,70,[17,66,158,229,287,357,444,519]⟩]⟩
def row8_113 : State := ⟨[0,37,66,158,229,357,444,519,594],[⟨6,70,[38,66,158,229,357,444,519,594]⟩,⟨8,89,[37,66,159,229,357,444,519,594]⟩,⟨6,89,[37,66,158,230,357,444,519,594]⟩,⟨6,55,[37,66,158,229,358,444,519,594]⟩,⟨8,90,[37,66,158,229,357,444,520,594]⟩,⟨6,90,[37,66,158,229,357,444,519,595]⟩]⟩
def row8_114 : State := ⟨[66,158,177,229,294,357,444,519,594],[⟨0,90,[12,66,158,229,294,357,444,519]⟩]⟩
def row8_115 : State := ⟨[66,158,174,229,287,357,444,519,594],[]⟩
def row8_116 : State := ⟨[12,66,158,229,287,357,425,444,519],[]⟩
def row8_117 : State := ⟨[66,158,175,229,287,357,444,519,594],[]⟩
def row8_118 : State := ⟨[66,158,176,229,287,357,444,519,594],[⟨0,29,[12,66,158,229,287,357,444,519]⟩]⟩
def row8_119 : State := ⟨[54,66,158,229,287,357,444,519,594],[]⟩
def row8_120 : State := ⟨[55,66,158,229,287,358,444,519,594],[]⟩
def row8_121 : State := ⟨[0,66,158,229,287,357,444,519,594],[⟨10,4,[66,159,229,287,357,444,519,594]⟩,⟨7,4,[66,158,230,287,357,444,519,594]⟩,⟨6,5,[66,158,229,288,357,444,519,594]⟩,⟨0,2,[66,158,229,287,358,444,519,594]⟩,⟨2,3,[66,158,229,287,357,444,520,594]⟩,⟨0,3,[66,158,229,287,357,444,519,595]⟩]⟩
def row8_122 : State := ⟨[66,158,178,229,287,357,444,519,594],[]⟩
def row8_123 : State := ⟨[0,66,158,229,287,357,465,519,594],[⟨4,91,[66,159,229,287,357,465,519,594]⟩,⟨1,91,[66,158,230,287,357,465,519,594]⟩,⟨0,92,[66,158,229,288,357,465,519,594]⟩,⟨0,93,[0,37,66,158,229,357,519,594]⟩,⟨5,13,[66,158,229,287,357,465,520,594]⟩,⟨3,13,[66,158,229,287,357,465,519,595]⟩]⟩
def row8_124 : State := ⟨[12,58,66,158,229,287,357,444,519],[⟨0,55,[12,67,158,229,287,357,444,519]⟩,⟨6,93,[7,12,66,229,287,357,444,519]⟩]⟩
def row8_125 : State := ⟨[66,88,158,229,287,357,444,519,594],[⟨7,3,[66,158,236,287,357,444,519,594]⟩]⟩
def row8_126 : State := ⟨[66,131,158,229,287,357,444,519,594],[]⟩
def row8_127 : State := ⟨[66,158,229,287,357,444,490,519,594],[⟨3,94,[66,107,158,229,357,444,519,594]⟩,⟨10,94,[66,158,229,287,357,438,444,519]⟩]⟩
def row8_128 : State := ⟨[49,66,229,287,357,444,519,594],[⟨0,95,[49,69,229,287,357,444,519,594]⟩,⟨1,96,[49,66,242,287,357,444,519,594]⟩,⟨0,96,[49,66,229,300,357,444,519,594]⟩,⟨0,19,[49,66,229,287,357,444,519,656]⟩,⟨1,19,[49,66,229,287,357,444,519,665]⟩]⟩
def row8_129 : State := ⟨[49,66,158,229,287,357,444,519,594],[⟨10,51,[69,158,229,287,357,444,519,594]⟩,⟨9,97,[66,158,242,287,357,444,519,594]⟩,⟨8,97,[66,158,229,300,357,444,519,594]⟩]⟩
def row8_130 : State := ⟨[49,66,229,287,357,444,519,594,633],[]⟩
def row8_131 : State := ⟨[66,158,229,287,357,444,519,594,708],[]⟩
def row8_132 : State := ⟨[12,66,158,229,287,357,428,444,519],[]⟩
def row8_133 : State := ⟨[49,66,229,287,357,444,519,594,625],[⟨10,29,[15,66,229,287,357,444,519,594]⟩]⟩
def row8_134 : State := ⟨[66,158,177,229,287,357,444,535,594],[⟨0,98,[12,66,158,229,287,357,444,535]⟩]⟩
def row8_135 : State := ⟨[66,158,177,229,287,357,444,519,600],[⟨0,29,[12,66,158,229,287,357,444,519]⟩]⟩
def row8_136 : State := ⟨[66,158,177,229,287,357,444,532,594],[⟨0,99,[12,66,158,229,287,357,444,532]⟩]⟩
def row8_137 : State := ⟨[66,158,229,287,358,444,519,549,594],[⟨7,100,[29,66,158,287,358,444,519,594]⟩,⟨0,0,[66,158,229,287,357,444,519,594]⟩]⟩
def row8_138 : State := ⟨[66,158,229,287,357,444,519,595,625],[⟨10,101,[15,66,229,287,357,444,519,595]⟩,⟨0,0,[66,158,229,287,357,444,519,594]⟩]⟩
def row8_139 : State := ⟨[66,158,179,229,287,357,444,519,594],[⟨0,29,[12,66,158,229,287,357,444,519]⟩]⟩
def row8_140 : State := ⟨[0,15,66,229,287,357,444,519,594],[⟨0,102,[16,66,229,287,357,444,519,594]⟩,⟨11,98,[15,66,230,287,357,444,519,594]⟩,⟨10,99,[15,66,229,288,357,444,519,594]⟩,⟨10,100,[15,66,229,287,358,444,519,594]⟩,⟨10,103,[15,66,229,287,357,444,520,594]⟩,⟨10,101,[15,66,229,287,357,444,519,595]⟩]⟩
def row8_141 : State := ⟨[66,158,177,229,302,357,444,519,594],[⟨0,103,[12,66,158,229,302,357,444,519]⟩]⟩
def row8_142 : State := ⟨[66,88,177,229,287,357,444,519,594],[⟨11,13,[66,177,236,287,357,444,519,594]⟩,⟨0,104,[12,66,88,229,287,357,444,519]⟩]⟩
def row8_143 : State := ⟨[66,99,158,229,287,357,444,519,594],[]⟩
def row8_144 : State := ⟨[12,66,158,229,287,357,444,494,519],[⟨1,12,[12,66,270,287,357,444,494,519]⟩,⟨0,104,[12,66,88,229,287,357,444,519]⟩]⟩
def row8_145 : State := ⟨[66,158,229,287,357,444,519,600,625],[⟨10,105,[15,66,229,287,357,444,519,600]⟩]⟩
def row8_146 : State := ⟨[66,158,177,229,289,357,444,519,594],[⟨0,106,[12,66,158,229,289,357,444,519]⟩]⟩
def row8_147 : State := ⟨[66,158,177,229,288,357,444,519,594],[⟨0,107,[12,66,158,229,288,357,444,519]⟩]⟩
def row8_148 : State := ⟨[66,158,177,229,287,358,444,519,594],[⟨0,108,[12,66,158,229,287,358,444,519]⟩]⟩
def row8_149 : State := ⟨[66,158,177,229,287,357,444,520,594],[⟨0,109,[12,66,158,229,287,357,444,520]⟩]⟩
def row8_150 : State := ⟨[66,158,177,229,287,357,444,519,595],[⟨0,110,[13,66,158,229,287,357,444,519]⟩]⟩
def row8_151 : State := ⟨[0,12,66,158,229,287,357,444,519],[⟨0,110,[13,66,158,229,287,357,444,519]⟩,⟨0,105,[12,66,159,229,287,357,444,519]⟩,⟨1,106,[12,66,158,230,287,357,444,519]⟩,⟨0,107,[12,66,158,229,288,357,444,519]⟩,⟨0,108,[12,66,158,229,287,358,444,519]⟩,⟨0,109,[12,66,158,229,287,357,444,520]⟩]⟩
def row8_152 : State := ⟨[66,137,158,229,287,357,444,519,594],[]⟩
def row8_153 : State := ⟨[66,158,229,287,357,444,488,519,594],[⟨10,94,[66,158,229,287,357,438,444,519]⟩]⟩
def row8_154 : State := ⟨[12,66,158,229,287,357,444,468,519],[]⟩
def row8_155 : State := ⟨[12,66,118,158,229,287,357,444,519],[]⟩
def row8_156 : State := ⟨[66,158,229,310,357,444,519,625,644],[⟨0,49,[158,229,310,380,444,519,625,644]⟩,⟨2,91,[66,158,229,291,357,444,519,625]⟩,⟨7,91,[66,158,229,310,357,444,519,609]⟩]⟩
def row8_157 : State := ⟨[66,158,229,310,357,444,519,644,656],[⟨7,111,[158,229,310,357,468,519,644,656]⟩]⟩
def row8_158 : State := ⟨[66,158,229,287,425,444,519,625,637],[⟨3,111,[66,270,287,425,444,519,625,637]⟩]⟩
def row8_159 : State := ⟨[12,66,177,229,287,357,444,480,519],[⟨0,105,[12,66,159,229,287,357,444,519]⟩]⟩
def row8_160 : State := ⟨[42,66,158,229,287,357,465,519,594],[⟨4,91,[66,159,229,287,357,465,519,594]⟩,⟨1,91,[66,158,230,287,357,465,519,594]⟩,⟨0,92,[66,158,229,288,357,465,519,594]⟩]⟩
def row8_161 : State := ⟨[66,158,229,287,357,444,519,625,685],[⟨0,112,[66,158,229,287,357,444,519,603]⟩]⟩
def row8_162 : State := ⟨[66,158,229,287,357,444,519,625,652],[⟨0,113,[66,158,229,287,357,444,519,612]⟩]⟩
def row8_163 : State := ⟨[66,158,229,287,357,444,519,600],[⟨6,91,[66,158,253,287,357,444,519,600]⟩]⟩
def row8_164 : State := ⟨[66,158,229,287,357,444,519,600,637],[]⟩
def row8_165 : State := ⟨[66,158,159,229,287,357,444,519,594],[]⟩
def row8_166 : State := ⟨[12,66,158,229,287,357,444,480,519],[]⟩
def row8_167 : State := ⟨[66,118,158,229,287,357,444,519,594],[]⟩
def row8_168 : State := ⟨[66,119,159,229,287,357,444,519,594],[]⟩
def row8_169 : State := ⟨[66,158,215,229,287,357,444,519,594],[]⟩
def row8_170 : State := ⟨[66,158,229,266,287,357,444,519,594],[⟨10,9,[66,158,223,229,287,357,444,519]⟩]⟩
def row8_171 : State := ⟨[66,138,158,229,287,357,444,519,594],[]⟩
def row8_172 : State := ⟨[10,66,122,229,287,357,444,519,594],[⟨6,114,[68,122,229,287,357,444,519,594]⟩,⟨0,9,[66,125,229,287,357,444,519,594]⟩]⟩
def row8_173 : State := ⟨[66,119,158,229,287,357,465,519,594],[⟨4,91,[66,159,229,287,357,465,519,594]⟩,⟨6,115,[37,66,119,158,229,357,519,594]⟩]⟩
def row8_174 : State := ⟨[66,158,216,229,287,357,444,519,594],[]⟩
def row8_175 : State := ⟨[66,158,229,267,287,357,444,519,594],[]⟩
def row8_176 : State := ⟨[12,66,119,158,229,287,357,444,519],[⟨0,105,[12,66,159,229,287,357,444,519]⟩]⟩
def row8_177 : State := ⟨[66,89,158,229,287,357,444,519,594],[⟨9,7,[66,158,239,287,357,444,519,594]⟩]⟩
def row8_178 : State := ⟨[65,66,158,229,287,357,444,519,594],[]⟩
def row8_179 : State := ⟨[66,158,229,287,357,444,510,519,594],[⟨3,116,[66,158,192,229,357,444,519,594]⟩]⟩
def row8_180 : State := ⟨[66,158,229,287,357,444,519,641,665],[⟨0,97,[66,158,229,287,357,444,519,606]⟩]⟩
def row8_181 : State := ⟨[66,91,229,287,357,444,519,594],[⟨0,117,[66,91,242,287,357,444,519,594]⟩,⟨0,32,[66,91,229,287,357,444,519,665]⟩]⟩
def row8_182 : State := ⟨[66,91,158,229,287,357,444,519,594],[⟨9,97,[66,158,242,287,357,444,519,594]⟩]⟩
def row8_183 : State := ⟨[66,91,229,287,357,444,519,594,643],[]⟩
def row8_184 : State := ⟨[66,158,229,287,357,444,519,594,705],[]⟩
def row8_185 : State := ⟨[12,66,158,229,287,357,444,488,519],[]⟩
def row8_186 : State := ⟨[66,91,229,287,357,444,519,594,625],[⟨10,29,[15,66,229,287,357,444,519,594]⟩]⟩
def row8_187 : State := ⟨[66,158,229,287,357,444,519,625,634],[⟨10,118,[15,66,229,287,357,444,519,634]⟩,⟨0,0,[66,158,229,287,357,444,519,594]⟩]⟩
def row8_188 : State := ⟨[66,158,219,229,287,357,444,519,594],[⟨10,119,[66,158,201,229,287,357,444,519]⟩]⟩
def row8_189 : State := ⟨[12,66,158,202,229,287,357,444,519],[⟨0,118,[12,66,214,229,287,357,444,519]⟩]⟩
def row8_190 : State := ⟨[66,130,158,229,287,357,444,519,594],[⟨10,4,[66,159,229,287,357,444,519,594]⟩]⟩
def row8_191 : State := ⟨[12,66,158,229,287,357,444,498,519],[]⟩
def row8_192 : State := ⟨[66,158,229,287,364,444,465,519,594],[⟨8,120,[37,66,158,229,364,444,519,594]⟩,⟨0,0,[66,158,229,287,357,444,519,594]⟩,⟨1,17,[66,158,229,287,364,465,519,656]⟩]⟩
def row8_193 : State := ⟨[66,158,229,287,357,444,519,604,625],[⟨11,121,[15,66,229,287,357,444,519,604]⟩,⟨0,0,[66,158,229,287,357,444,519,594]⟩]⟩
def row8_194 : State := ⟨[66,158,180,229,287,357,444,519,594],[⟨7,9,[66,146,158,229,287,357,444,594]⟩,⟨0,29,[12,66,158,229,287,357,444,519]⟩]⟩
def row8_195 : State := ⟨[66,158,177,229,304,357,444,519,594],[⟨0,122,[12,66,158,229,304,357,444,519]⟩]⟩
def row8_196 : State := ⟨[66,158,177,229,287,367,444,519,594],[⟨3,15,[66,177,270,287,367,444,519,594]⟩,⟨1,114,[66,143,158,229,287,367,444,594]⟩,⟨0,123,[12,66,158,229,287,367,444,519]⟩]⟩
def row8_197 : State := ⟨[66,158,177,229,287,357,444,538,594],[⟨0,124,[12,66,158,229,287,357,444,538]⟩]⟩
def row8_198 : State := ⟨[66,158,177,229,287,357,444,519,604],[⟨7,16,[66,177,270,287,357,444,519,604]⟩,⟨0,29,[12,66,158,229,287,357,444,519]⟩]⟩
def row8_199 : State := ⟨[10,23,66,158,229,287,357,444,594],[⟨0,125,[26,66,158,229,287,357,444,594]⟩,⟨2,120,[23,68,158,229,287,357,444,594]⟩,⟨2,121,[23,66,158,239,287,357,444,594]⟩,⟨0,18,[10,23,66,270,287,357,444,594]⟩,⟨2,122,[23,66,158,229,297,357,444,594]⟩,⟨2,123,[23,66,158,229,287,364,444,594]⟩,⟨4,124,[23,66,158,229,287,357,450,594]⟩]⟩
def row8_200 : State := ⟨[12,66,158,229,287,357,444,519,681],[]⟩
def row8_201 : State := ⟨[66,154,158,229,287,357,444,519,594],[⟨10,4,[66,159,229,287,357,444,519,594]⟩]⟩
def row8_202 : State := ⟨[66,136,158,229,287,357,444,519,594],[]⟩
def row8_203 : State := ⟨[12,66,158,229,287,357,444,465,519],[⟨0,115,[12,66,122,229,287,357,444,519]⟩,⟨1,126,[12,37,66,158,229,357,444,519]⟩]⟩
def row8_204 : State := ⟨[12,66,158,229,287,357,391,444,519],[]⟩
def row8_205 : State := ⟨[2,158,177,229,287,357,444,519,594],[⟨6,127,[158,177,229,287,360,444,519,594]⟩,⟨6,128,[158,177,229,287,357,444,519,597]⟩,⟨0,129,[2,12,158,229,287,357,444,519]⟩]⟩
def row8_206 : State := ⟨[66,149,158,229,287,357,444,519,594],[⟨10,113,[66,161,229,287,357,444,519,594]⟩]⟩
def row8_207 : State := ⟨[12,66,158,229,287,357,444,519,588],[⟨0,129,[2,12,158,229,287,357,444,519]⟩]⟩
def row8_208 : State := ⟨[66,158,177,229,291,357,444,519,594],[⟨0,130,[12,66,158,229,291,357,444,519]⟩]⟩
def row8_209 : State := ⟨[66,158,229,287,357,444,519,598,625],[⟨10,131,[15,66,229,287,357,444,519,598]⟩]⟩
def row8_210 : State := ⟨[66,158,177,229,287,361,444,519,594],[⟨0,132,[12,66,158,229,287,361,444,519]⟩]⟩
def row8_211 : State := ⟨[0,36,66,158,229,287,357,519,594],[⟨5,130,[36,66,159,229,287,357,519,594]⟩,⟨3,130,[36,66,158,230,287,357,519,594]⟩,⟨3,131,[36,66,158,229,288,357,519,594]⟩,⟨3,132,[36,66,158,229,287,358,519,594]⟩,⟨0,133,[0,66,158,229,287,371,519,594]⟩,⟨5,134,[36,66,158,229,287,357,520,594]⟩,⟨3,134,[36,66,158,229,287,357,519,595]⟩]⟩
def row8_212 : State := ⟨[66,158,177,229,287,357,444,521,594],[⟨0,134,[12,66,158,229,287,357,444,521]⟩]⟩
def row8_213 : State := ⟨[66,158,229,322,444,465,519,574,594],[⟨4,111,[66,229,322,465,480,519,574,594]⟩,⟨0,135,[66,158,229,322,370,444,519,594]⟩]⟩
def row8_214 : State := ⟨[66,158,229,287,425,444,519,625,674],[]⟩
def row8_215 : State := ⟨[12,158,177,229,287,357,444,519,629],[⟨7,136,[158,177,229,287,357,451,519,629]⟩,⟨6,136,[158,177,229,287,357,444,528,629]⟩,⟨0,137,[12,68,158,229,287,357,444,519]⟩]⟩
def row8_216 : State := ⟨[66,158,229,287,364,444,519,594],[⟨4,135,[66,229,270,287,364,444,519,594]⟩,⟨5,135,[66,229,287,322,364,444,519,594]⟩,⟨10,137,[15,66,229,287,364,444,519,594]⟩,⟨4,77,[3,66,158,229,287,364,444,519]⟩,⟨0,11,[66,158,229,287,364,444,519,656]⟩,⟨1,11,[66,158,229,287,364,444,519,665]⟩]⟩
def row8_217 : State := ⟨[66,158,229,287,364,444,519,594,625],[⟨10,137,[15,66,229,287,364,444,519,594]⟩]⟩
def row8_218 : State := ⟨[66,158,229,287,364,425,444,519,594],[]⟩
def row8_219 : State := ⟨[12,66,158,229,287,357,444,519,629],[⟨1,138,[66,158,229,287,357,451,519,629]⟩,⟨0,138,[66,158,229,287,357,444,528,629]⟩]⟩
def row8_220 : State := ⟨[66,68,158,229,287,357,444,519,594],[⟨0,29,[12,66,158,229,287,357,444,519]⟩]⟩
def row8_221 : State := ⟨[66,158,229,287,357,444,519,594,704],[]⟩
def row8_222 : State := ⟨[66,158,177,229,297,357,444,519,594],[⟨0,139,[12,66,158,229,297,357,444,519]⟩]⟩
def row8_223 : State := ⟨[66,158,177,229,287,364,444,519,594],[⟨0,140,[12,66,158,229,287,364,444,519]⟩]⟩
def row8_224 : State := ⟨[66,158,177,229,287,357,444,526,594],[⟨0,141,[12,66,158,229,287,357,444,526]⟩]⟩
def row8_225 : State := ⟨[10,12,66,158,229,287,357,444,519],[⟨0,137,[12,68,158,229,287,357,444,519]⟩,⟨1,139,[12,66,158,239,287,357,444,519]⟩,⟨0,139,[12,66,158,229,297,357,444,519]⟩,⟨0,140,[12,66,158,229,287,364,444,519]⟩,⟨1,141,[12,66,158,229,287,357,450,519]⟩,⟨1,142,[10,66,158,229,287,357,451,519]⟩,⟨0,141,[12,66,158,229,287,357,444,526]⟩,⟨0,142,[10,66,158,229,287,357,444,528]⟩]⟩
def row8_226 : State := ⟨[66,158,229,310,357,465,519,594,691],[⟨0,50,[158,229,310,380,465,519,594,691]⟩,⟨3,143,[63,66,158,229,357,519,594,691]⟩,⟨0,92,[66,158,229,288,357,465,519,594]⟩,⟨9,92,[66,158,229,310,357,459,519,594]⟩]⟩
def row8_227 : State := ⟨[12,66,177,229,287,357,444,519,674],[⟨4,144,[66,177,229,287,366,444,519,674]⟩,⟨0,131,[12,66,162,229,287,357,444,519]⟩]⟩
def row8_228 : State := ⟨[66,158,229,287,357,444,519,598],[⟨6,92,[66,177,229,287,357,444,519,598]⟩,⟨10,131,[15,66,229,287,357,444,519,598]⟩]⟩
def row8_229 : State := ⟨[66,158,229,287,357,444,519,598,674],[]⟩
def row8_230 : State := ⟨[12,66,158,229,287,357,444,519,674],[⟨0,145,[66,158,229,287,366,444,519,674]⟩]⟩
def row8_231 : State := ⟨[66,158,162,229,287,357,444,519,594],[⟨0,29,[12,66,158,229,287,357,444,519]⟩]⟩
def row8_232 : State := ⟨[12,68,158,229,287,357,444,519],[⟨0,146,[12,68,162,229,287,357,444,519]⟩,⟨1,147,[12,68,158,241,287,357,444,519]⟩,⟨0,20,[12,68,229,270,287,357,444,519]⟩,⟨0,147,[12,68,158,229,299,357,444,519]⟩,⟨1,20,[12,68,229,287,322,357,444,519]⟩,⟨0,148,[12,68,158,229,287,366,444,519]⟩,⟨6,81,[7,12,68,229,287,357,444,519]⟩,⟨7,149,[68,158,229,287,357,451,519]⟩,⟨8,150,[68,158,229,287,357,444,451,519]⟩,⟨1,151,[12,68,158,229,287,357,451,519]⟩,⟨6,149,[68,158,229,287,357,444,528]⟩,⟨9,150,[68,158,229,287,357,444,519,528]⟩,⟨0,151,[12,68,158,229,287,357,444,528]⟩]⟩
def row8_233 : State := ⟨[12,66,68,158,229,287,357,444,519],[⟨1,152,[66,68,158,229,287,357,451,519]⟩,⟨0,152,[66,68,158,229,287,357,444,528]⟩]⟩
def row8_234 : State := ⟨[12,66,162,229,287,357,444,519],[⟨0,146,[12,68,162,229,287,357,444,519]⟩,⟨1,153,[12,66,162,241,287,357,444,519]⟩,⟨0,22,[12,66,229,273,287,357,444,519]⟩,⟨0,153,[12,66,162,229,299,357,444,519]⟩,⟨1,22,[12,66,229,287,324,357,444,519]⟩,⟨4,154,[66,162,229,287,366,444,519]⟩,⟨10,155,[66,162,229,287,357,366,444,519]⟩,⟨0,156,[12,66,162,229,287,366,444,519]⟩,⟨6,93,[7,12,66,229,287,357,444,519]⟩,⟨1,157,[12,66,162,229,287,357,451,519]⟩,⟨0,157,[12,66,162,229,287,357,444,528]⟩]⟩
def row8_235 : State := ⟨[12,66,158,162,229,287,357,444,519],[⟨0,158,[66,158,162,229,287,366,444,519]⟩]⟩
def row8_236 : State := ⟨[12,66,158,177,229,287,357,444,519],[]⟩
def row8_237 : State := ⟨[12,66,158,229,299,357,444,519],[⟨0,147,[12,68,158,229,299,357,444,519]⟩,⟨0,153,[12,66,162,229,299,357,444,519]⟩,⟨0,159,[12,66,158,241,299,357,444,519]⟩,⟨0,23,[12,66,229,270,299,357,444,519]⟩,⟨0,160,[12,66,229,299,324,357,444,519]⟩,⟨0,161,[66,158,229,299,366,444,519]⟩,⟨10,162,[66,158,229,299,357,366,444,519]⟩,⟨0,163,[12,66,158,229,299,366,444,519]⟩,⟨6,85,[7,12,66,229,299,357,444,519]⟩,⟨0,164,[66,158,229,299,357,451,519]⟩,⟨8,165,[66,158,229,299,357,444,451,519]⟩,⟨0,166,[12,66,158,229,299,357,451,519]⟩,⟨0,167,[12,66,158,229,299,357,444,528]⟩]⟩
def row8_238 : State := ⟨[12,66,158,229,241,287,357,444,519],[⟨1,21,[12,66,241,270,287,357,444,519]⟩,⟨0,22,[12,66,229,273,287,357,444,519]⟩,⟨2,168,[66,158,229,241,287,366,444,519]⟩,⟨2,169,[66,158,229,241,287,357,444,528]⟩]⟩
def row8_239 : State := ⟨[12,66,158,229,287,366,444,519],[⟨4,133,[3,66,158,229,287,366,444,519]⟩,⟨0,148,[12,68,158,229,287,366,444,519]⟩,⟨4,154,[66,162,229,287,366,444,519]⟩,⟨0,158,[66,158,162,229,287,366,444,519]⟩,⟨0,156,[12,66,162,229,287,366,444,519]⟩,⟨1,161,[66,158,241,287,366,444,519]⟩,⟨2,168,[66,158,229,241,287,366,444,519]⟩,⟨1,163,[12,66,158,241,287,366,444,519]⟩,⟨0,25,[12,66,229,270,287,366,444,519]⟩,⟨0,161,[66,158,229,299,366,444,519]⟩,⟨3,168,[66,158,229,287,299,366,444,519]⟩,⟨0,163,[12,66,158,229,299,366,444,519]⟩,⟨1,25,[12,66,229,287,322,366,444,519]⟩,⟨0,170,[12,15,66,229,287,366,444,519]⟩,⟨1,171,[66,158,229,287,366,451,519]⟩,⟨0,172,[66,158,229,287,366,444,451,519]⟩,⟨1,173,[12,66,158,229,287,366,451,519]⟩,⟨0,171,[66,158,229,287,366,444,528]⟩,⟨1,172,[66,158,229,287,366,444,519,528]⟩,⟨0,173,[12,66,158,229,287,366,444,528]⟩]⟩
def row8_240 : State := ⟨[12,66,158,229,287,357,366,444,519],[⟨10,155,[66,162,229,287,357,366,444,519]⟩,⟨11,162,[66,158,241,287,357,366,444,519]⟩,⟨10,162,[66,158,229,299,357,366,444,519]⟩,⟨6,79,[7,12,66,229,287,366,444,519]⟩,⟨0,174,[12,15,66,229,287,357,444,519]⟩,⟨11,175,[66,158,229,287,357,366,451,519]⟩,⟨10,175,[66,158,229,287,357,366,444,528]⟩]⟩
def row8_241 : State := ⟨[12,66,158,229,287,357,444,528],[⟨6,149,[68,158,229,287,357,444,528]⟩,⟨0,152,[66,68,158,229,287,357,444,528]⟩,⟨0,151,[12,68,158,229,287,357,444,528]⟩,⟨0,142,[10,66,158,229,287,357,444,528]⟩,⟨0,157,[12,66,162,229,287,357,444,528]⟩,⟨1,164,[66,158,241,287,357,444,528]⟩,⟨2,169,[66,158,229,241,287,357,444,528]⟩,⟨1,166,[12,66,158,241,287,357,444,528]⟩,⟨0,28,[12,66,229,270,287,357,444,528]⟩,⟨0,167,[12,66,158,229,299,357,444,528]⟩,⟨1,27,[12,66,229,287,322,357,444,528]⟩,⟨0,171,[66,158,229,287,366,444,528]⟩,⟨10,175,[66,158,229,287,357,366,444,528]⟩,⟨0,173,[12,66,158,229,287,366,444,528]⟩,⟨6,80,[7,12,66,229,287,357,444,528]⟩,⟨0,176,[12,66,158,229,287,357,451,528]⟩]⟩
def row8_242 : State := ⟨[12,66,158,229,287,357,444,451,519],[⟨8,150,[68,158,229,287,357,444,451,519]⟩,⟨8,165,[66,158,229,299,357,444,451,519]⟩,⟨0,172,[66,158,229,287,366,444,451,519]⟩]⟩
def row8_243 : State := ⟨[12,68,158,229,287,357,444,519,594],[⟨10,177,[68,162,229,287,357,444,519,594]⟩,⟨11,178,[68,158,241,287,357,444,519,594]⟩,⟨10,178,[68,158,229,299,357,444,519,594]⟩,⟨0,179,[68,158,229,287,366,444,519,594]⟩,⟨11,180,[68,158,229,287,357,451,519,594]⟩,⟨10,180,[68,158,229,287,357,444,528,594]⟩]⟩
def row8_244 : State := ⟨[10,66,158,229,287,357,444,519,594],[⟨10,6,[68,158,229,287,357,444,519,594]⟩,⟨9,7,[66,158,239,287,357,444,519,594]⟩,⟨8,7,[66,158,229,297,357,444,519,594]⟩,⟨0,6,[66,158,229,287,364,444,519,594]⟩,⟨3,7,[66,158,229,287,357,450,519,594]⟩,⟨2,7,[66,158,229,287,357,444,526,594]⟩]⟩
def row8_245 : State := ⟨[12,66,162,229,287,357,444,519,594],[⟨10,177,[68,162,229,287,357,444,519,594]⟩,⟨11,181,[66,162,241,287,357,444,519,594]⟩,⟨10,181,[66,162,229,299,357,444,519,594]⟩,⟨4,182,[66,162,229,287,366,444,519,594]⟩,⟨5,183,[66,162,229,287,357,451,519,594]⟩,⟨4,183,[66,162,229,287,357,444,528,594]⟩]⟩
def row8_246 : State := ⟨[66,158,229,287,357,444,519,608],[⟨7,184,[66,158,253,287,357,444,519,608]⟩,⟨7,185,[66,158,270,287,357,444,519,608]⟩,⟨4,43,[66,158,226,287,357,444,519,608]⟩]⟩
def row8_247 : State := ⟨[66,158,167,229,287,357,444,519,594],[⟨7,9,[66,146,158,229,287,357,444,594]⟩]⟩
def row8_248 : State := ⟨[12,66,158,229,299,357,444,519,594],[⟨10,178,[68,158,229,299,357,444,519,594]⟩,⟨10,181,[66,162,229,299,357,444,519,594]⟩,⟨6,186,[66,158,241,299,357,444,519,594]⟩,⟨0,187,[66,158,229,299,366,444,519,594]⟩,⟨0,188,[66,158,229,299,357,451,519,594]⟩,⟨0,189,[66,158,229,299,357,444,528,594]⟩]⟩
def row8_249 : State := ⟨[66,158,229,287,366,444,519,594],[⟨4,30,[66,229,270,287,366,444,519,594]⟩,⟨5,30,[66,229,287,322,366,444,519,594]⟩,⟨10,190,[15,66,229,287,366,444,519,594]⟩,⟨4,133,[3,66,158,229,287,366,444,519]⟩,⟨0,145,[66,158,229,287,366,444,519,674]⟩,⟨0,191,[66,158,229,287,366,444,519,637]⟩,⟨1,191,[66,158,229,287,366,444,519,644]⟩,⟨10,95,[66,158,229,287,347,366,444,519]⟩,⟨0,192,[66,158,229,287,366,444,519,656]⟩,⟨1,192,[66,158,229,287,366,444,519,665]⟩]⟩
def row8_250 : State := ⟨[66,69,158,229,287,357,444,519,594],[⟨0,1,[49,66,229,287,357,444,519,594]⟩,⟨0,29,[12,66,158,229,287,357,444,519]⟩]⟩
def row8_251 : State := ⟨[12,66,158,229,287,366,444,519,594],[⟨0,179,[68,158,229,287,366,444,519,594]⟩,⟨4,182,[66,162,229,287,366,444,519,594]⟩,⟨1,187,[66,158,241,287,366,444,519,594]⟩,⟨0,187,[66,158,229,299,366,444,519,594]⟩,⟨1,193,[66,158,229,287,366,451,519,594]⟩,⟨0,193,[66,158,229,287,366,444,528,594]⟩]⟩
def row8_252 : State := ⟨[66,158,229,287,357,444,519,606],[⟨7,31,[66,158,270,287,357,444,519,606]⟩,⟨2,138,[66,158,229,287,357,444,553,606]⟩,⟨2,194,[66,158,229,287,357,444,563,606]⟩,⟨2,142,[22,66,158,229,287,357,444,606]⟩,⟨2,195,[66,158,229,287,357,444,549,606]⟩,⟨9,117,[66,158,229,287,357,444,514,606]⟩]⟩
def row8_253 : State := ⟨[66,158,168,229,287,357,444,519,594],[⟨2,94,[66,94,158,287,357,444,519,594]⟩]⟩
def row8_254 : State := ⟨[12,66,158,229,287,357,444,528,594],[⟨10,180,[68,158,229,287,357,444,528,594]⟩,⟨4,183,[66,162,229,287,357,444,528,594]⟩,⟨1,188,[66,158,241,287,357,444,528,594]⟩,⟨0,189,[66,158,229,299,357,444,528,594]⟩,⟨0,193,[66,158,229,287,366,444,528,594]⟩,⟨4,196,[66,158,229,287,357,451,528,594]⟩]⟩
def row8_255 : State := ⟨[12,66,158,220,229,287,357,444,519],[⟨10,9,[66,158,223,229,287,357,444,519]⟩,⟨0,197,[12,66,229,265,287,357,444,519]⟩]⟩
def row8_256 : State := ⟨[12,66,158,229,287,357,444,519,637],[⟨1,14,[12,66,270,287,357,444,519,637]⟩,⟨0,191,[66,158,229,287,366,444,519,637]⟩,⟨0,194,[66,158,229,287,357,444,528,637]⟩]⟩
def row8_257 : State := ⟨[12,66,158,229,287,357,444,519,625],[⟨4,92,[66,162,229,287,357,444,519,625]⟩,⟨1,184,[66,158,241,287,357,444,519,625]⟩,⟨0,184,[66,158,229,299,357,444,519,625]⟩,⟨1,195,[66,158,229,287,357,451,519,625]⟩,⟨0,195,[66,158,229,287,357,444,528,625]⟩,⟨0,174,[12,15,66,229,287,357,444,519]⟩]⟩
def row8_258 : State := ⟨[12,66,158,229,287,357,434,444,519],[⟨10,94,[66,158,229,287,357,438,444,519]⟩]⟩
def row8_259 : State := ⟨[12,66,158,229,287,357,444,519,656],[⟨6,135,[68,158,229,287,357,444,519,656]⟩,⟨0,185,[66,158,229,299,357,444,519,656]⟩,⟨0,192,[66,158,229,287,366,444,519,656]⟩]⟩
def row8_260 : State := ⟨[12,68,158,177,229,287,357,444,519],[⟨7,198,[68,158,177,229,287,357,451,519]⟩,⟨6,198,[68,158,177,229,287,357,444,528]⟩]⟩
def row8_261 : State := ⟨[12,66,162,177,229,287,357,444,519],[⟨4,199,[66,162,177,229,287,366,444,519]⟩]⟩
def row8_262 : State := ⟨[12,66,158,177,229,299,357,444,519],[⟨0,200,[66,158,177,229,299,366,444,519]⟩,⟨0,201,[66,158,177,229,299,357,451,519]⟩]⟩
def row8_263 : State := ⟨[12,66,158,177,229,287,366,444,519],[⟨4,199,[66,162,177,229,287,366,444,519]⟩,⟨1,200,[66,158,177,241,287,366,444,519]⟩,⟨0,200,[66,158,177,229,299,366,444,519]⟩,⟨1,202,[66,158,177,229,287,366,451,519]⟩,⟨0,202,[66,158,177,229,287,366,444,528]⟩]⟩
def row8_264 : State := ⟨[12,66,158,177,229,287,357,444,528],[⟨6,198,[68,158,177,229,287,357,444,528]⟩,⟨1,201,[66,158,177,241,287,357,444,528]⟩,⟨0,202,[66,158,177,229,287,366,444,528]⟩]⟩
def row8_265 : State := ⟨[66,158,177,229,299,357,444,519,594],[⟨0,203,[12,66,158,229,299,357,444,519]⟩]⟩
def row8_266 : State := ⟨[66,158,177,229,287,366,444,519,594],[⟨4,144,[66,177,229,287,366,444,519,674]⟩,⟨0,204,[12,66,158,229,287,366,444,519]⟩]⟩
def row8_267 : State := ⟨[66,158,177,229,287,357,444,528,594],[⟨6,136,[158,177,229,287,357,444,528,629]⟩,⟨0,205,[12,66,158,229,287,357,444,528]⟩]⟩
def row8_268 : State := ⟨[12,66,158,229,287,357,444,519,704],[]⟩
def row8_269 : State := ⟨[66,153,158,229,287,357,444,519,594],[]⟩
def row8_270 : State := ⟨[66,156,158,229,287,357,444,519,594],[]⟩
def row8_271 : State := ⟨[66,158,229,287,403,444,519,594,625],[⟨0,0,[66,158,229,287,357,444,519,594]⟩]⟩
def row8_272 : State := ⟨[66,158,229,287,357,444,519,625,654],[⟨10,197,[15,66,229,287,357,444,519,654]⟩,⟨0,0,[66,158,229,287,357,444,519,594]⟩]⟩
def row8_273 : State := ⟨[66,158,229,276,287,357,444,519,594],[⟨10,9,[66,158,223,229,287,357,444,519]⟩]⟩
def row8_274 : State := ⟨[66,90,158,229,287,357,444,519,594],[⟨10,5,[66,162,229,287,357,444,519,594]⟩,⟨9,42,[66,158,241,287,357,444,519,594]⟩,⟨0,29,[12,66,158,229,287,357,444,519]⟩]⟩
def row8_275 : State := ⟨[60,66,158,229,287,357,444,519,594],[⟨10,51,[69,158,229,287,357,444,519,594]⟩,⟨10,29,[15,66,229,287,357,444,519,594]⟩,⟨0,51,[66,158,229,287,366,444,519,594]⟩,⟨0,29,[12,66,158,229,287,357,444,519]⟩,⟨0,143,[60,66,229,287,357,444,519,674]⟩]⟩
def row8_276 : State := ⟨[66,158,229,287,387,444,519,549,594],[⟨0,0,[66,158,229,287,357,444,519,594]⟩]⟩
def row8_277 : State := ⟨[66,158,229,287,357,444,519,625,635],[⟨0,0,[66,158,229,287,357,444,519,594]⟩]⟩
def row8_278 : State := ⟨[66,158,229,287,357,444,485,519,594],[⟨10,94,[66,158,229,287,357,438,444,519]⟩]⟩
def row8_279 : State := ⟨[66,124,158,229,287,357,444,519,594],[⟨10,112,[66,163,229,287,357,444,519,594]⟩,⟨3,97,[66,158,229,287,357,451,519,594]⟩,⟨0,29,[12,66,158,229,287,357,444,519]⟩]⟩
def row8_280 : State := ⟨[66,158,229,287,357,374,444,519,594],[]⟩
def row8_281 : State := ⟨[66,158,229,287,380,396,444,519,594],[⟨0,0,[66,158,229,287,357,444,519,594]⟩]⟩
def row8_282 : State := ⟨[66,158,229,287,357,388,444,519,594],[]⟩
def row8_283 : State := ⟨[0,98,158,229,287,357,444,519,594],[⟨6,206,[98,158,229,288,357,444,519,594]⟩,⟨6,207,[98,158,229,287,358,444,519,594]⟩,⟨8,208,[98,158,229,287,357,444,520,594]⟩,⟨6,208,[98,158,229,287,357,444,519,595]⟩]⟩
def row8_284 : State := ⟨[66,79,158,229,287,357,444,519,594],[⟨10,4,[66,159,229,287,357,444,519,594]⟩,⟨7,4,[66,158,230,287,357,444,519,594]⟩]⟩
def row8_285 : State := ⟨[66,158,229,287,396,444,494,519,594],[⟨0,0,[66,158,229,287,357,444,519,594]⟩]⟩
def row8_286 : State := ⟨[66,158,229,287,357,444,486,519,594],[]⟩
def row8_287 : State := ⟨[66,158,229,287,357,444,519,629,653],[⟨0,0,[66,158,229,287,357,444,519,594]⟩]⟩
def row8_288 : State := ⟨[66,158,229,287,357,433,444,519,594],[]⟩
def row8_289 : State := ⟨[66,158,229,287,357,444,519,637,653],[⟨0,0,[66,158,229,287,357,444,519,594]⟩]⟩
def row8_290 : State := ⟨[66,158,229,287,357,444,504,519,594],[]⟩
def row8_291 : State := ⟨[10,66,158,229,287,357,444,519,653],[⟨6,209,[68,158,229,287,357,444,519,653]⟩,⟨1,210,[66,158,239,287,357,444,519,653]⟩,⟨0,210,[66,158,229,297,357,444,519,653]⟩,⟨0,211,[66,158,229,287,364,444,519,653]⟩]⟩
def row8_292 : State := ⟨[66,83,158,229,287,357,444,519,594],[⟨10,7,[66,171,229,287,357,444,519,594]⟩,⟨7,7,[66,158,246,287,357,444,519,594]⟩]⟩
def row8_293 : State := ⟨[66,97,158,229,287,357,444,519,594],[]⟩
def row8_294 : State := ⟨[66,116,158,229,287,357,444,519,594],[]⟩
def row8_295 : State := ⟨[66,85,158,229,287,357,448,519,594],[]⟩
def row8_296 : State := ⟨[66,85,158,229,287,357,444,519,600],[]⟩
def row8_297 : State := ⟨[66,85,158,229,287,357,444,519,598],[]⟩
def row8_298 : State := ⟨[66,158,229,287,358,391,444,519,594],[]⟩
def row8_299 : State := ⟨[66,85,158,236,287,357,444,519,594],[]⟩
def row8_300 : State := ⟨[66,85,158,229,294,357,444,519,594],[]⟩
def row8_301 : State := ⟨[66,85,158,229,287,357,444,519,609],[]⟩
def row8_302 : State := ⟨[66,85,158,229,287,357,459,519,594],[]⟩
def row8_303 : State := ⟨[66,158,229,287,358,444,511,519,594],[]⟩
def row8_304 : State := ⟨[66,95,158,229,287,357,444,519,594],[⟨11,3,[66,169,229,287,357,444,519,594]⟩,⟨9,3,[66,158,244,287,357,444,519,594]⟩]⟩
def row8_305 : State := ⟨[66,85,158,244,287,357,444,519,594],[]⟩
def row8_306 : State := ⟨[66,86,158,229,287,357,444,519,594],[⟨10,4,[66,159,229,287,357,444,519,594]⟩,⟨7,4,[66,158,230,287,357,444,519,594]⟩]⟩
def row8_307 : State := ⟨[66,85,158,230,287,357,444,519,594],[]⟩
def row8_308 : State := ⟨[66,85,158,229,288,357,444,519,594],[⟨6,206,[98,158,229,288,357,444,519,594]⟩]⟩
def row8_309 : State := ⟨[66,85,158,229,287,358,444,519,594],[⟨6,207,[98,158,229,287,358,444,519,594]⟩]⟩
def row8_310 : State := ⟨[66,85,158,229,287,357,444,519,595],[⟨6,208,[98,158,229,287,357,444,519,595]⟩]⟩
def row8_311 : State := ⟨[66,117,158,229,287,357,444,519,594],[]⟩
def row8_312 : State := ⟨[66,158,214,229,287,357,444,519,594],[]⟩
def row8_313 : State := ⟨[66,158,229,287,364,391,444,519,594],[⟨0,211,[66,158,229,287,364,444,519,653]⟩]⟩
def row8_314 : State := ⟨[66,96,158,229,287,357,444,519,594],[⟨10,7,[66,171,229,287,357,444,519,594]⟩,⟨7,7,[66,158,246,287,357,444,519,594]⟩]⟩
def row8_315 : State := ⟨[66,85,158,246,287,357,444,519,594],[]⟩
def row8_316 : State := ⟨[66,85,158,229,287,370,444,519,594],[⟨0,209,[66,158,229,313,370,444,519,594]⟩]⟩
def row8_317 : State := ⟨[66,85,158,229,287,357,444,519,615],[⟨6,210,[66,158,229,313,357,444,519,615]⟩]⟩
def row8_318 : State := ⟨[66,87,158,229,287,357,444,519,594],[⟨11,4,[66,160,229,287,357,444,519,594]⟩,⟨7,5,[66,158,231,287,357,444,519,594]⟩]⟩
def row8_319 : State := ⟨[66,85,158,233,287,357,444,519,594],[]⟩
def row8_320 : State := ⟨[66,85,158,229,289,357,444,519,594],[]⟩
def row8_321 : State := ⟨[66,85,158,231,287,357,444,519,594],[]⟩
def row8_322 : State := ⟨[66,85,158,229,287,359,444,519,594],[]⟩
def row8_323 : State := ⟨[66,85,158,229,287,357,445,519,594],[]⟩
def row8_324 : State := ⟨[66,85,158,229,287,357,444,519,596],[]⟩
def row8_325 : State := ⟨[66,158,229,287,357,444,519,635,665],[⟨0,0,[66,158,229,287,357,444,519,594]⟩]⟩
def row8_326 : State := ⟨[66,158,229,287,357,444,519,594,677],[]⟩
def row8_327 : State := ⟨[66,158,229,287,364,434,444,519,594],[]⟩
def row8_328 : State := ⟨[66,85,158,239,287,357,444,519,594],[]⟩
def row8_329 : State := ⟨[66,85,158,229,297,357,444,519,594],[]⟩
def row8_330 : State := ⟨[66,85,158,229,287,364,444,519,594],[]⟩
def row8_331 : State := ⟨[66,85,158,229,287,357,450,519,594],[]⟩
def row8_332 : State := ⟨[66,85,158,229,287,357,444,519,604],[]⟩
def row8_333 : State := ⟨[66,158,193,229,287,357,444,519,594],[]⟩
def row8_334 : State := ⟨[66,158,229,287,357,399,444,519,594],[]⟩
def row8_335 : State := ⟨[66,158,229,287,357,431,444,519,594],[]⟩
def row8_336 : State := ⟨[66,125,229,287,357,444,519,594,656],[]⟩
def row8_337 : State := ⟨[66,158,229,287,339,357,444,519,594],[⟨6,212,[34,66,158,229,287,444,519,594]⟩]⟩
def row8_338 : State := ⟨[66,113,158,229,287,357,444,519,594],[]⟩
def row8_339 : State := ⟨[66,158,229,287,357,390,444,519,594],[]⟩
def row8_340 : State := ⟨[66,158,229,287,357,444,503,519,594],[]⟩
def row8_341 : State := ⟨[66,158,229,287,357,444,519,629,671],[⟨0,213,[66,158,229,287,357,444,519,597]⟩]⟩
def row8_342 : State := ⟨[6,158,229,287,357,444,519,594],[⟨4,214,[6,164,229,287,357,444,519,594]⟩,⟨1,214,[6,158,235,287,357,444,519,594]⟩,⟨0,214,[6,158,229,293,357,444,519,594]⟩,⟨0,215,[6,158,229,287,363,444,519,594]⟩,⟨3,216,[6,158,229,287,357,447,519,594]⟩,⟨3,217,[6,35,158,229,287,357,519,594]⟩,⟨3,37,[6,158,229,287,357,465,519,594]⟩,⟨2,216,[6,158,229,287,357,444,522,594]⟩,⟨2,217,[6,22,158,229,287,357,444,594]⟩,⟨2,37,[6,158,229,287,357,444,549,594]⟩,⟨0,216,[6,158,229,287,357,444,519,597]⟩,⟨0,217,[6,10,158,229,287,357,444,519]⟩,⟨0,37,[6,158,229,287,357,444,519,625]⟩]⟩
def row8_343 : State := ⟨[6,66,158,229,287,357,444,519,594],[⟨10,218,[66,164,229,287,357,444,519,594]⟩,⟨7,218,[66,158,235,287,357,444,519,594]⟩,⟨6,218,[66,158,229,293,357,444,519,594]⟩,⟨0,219,[66,158,229,287,363,444,519,594]⟩,⟨3,213,[66,158,229,287,357,447,519,594]⟩,⟨2,213,[66,158,229,287,357,444,522,594]⟩,⟨0,213,[66,158,229,287,357,444,519,597]⟩]⟩
def row8_344 : State := ⟨[6,158,229,287,357,444,519,594,671],[]⟩
def row8_345 : State := ⟨[66,158,229,287,357,444,519,594,713],[]⟩
def row8_346 : State := ⟨[10,66,158,229,287,357,444,519,671],[⟨6,220,[68,158,229,287,357,444,519,671]⟩,⟨0,221,[66,158,229,287,364,444,519,671]⟩,⟨0,217,[6,10,158,229,287,357,444,519]⟩]⟩
def row8_347 : State := ⟨[66,151,158,229,287,357,444,519,594],[]⟩
def row8_348 : State := ⟨[66,158,229,287,357,444,519,594,688],[⟨0,222,[46,158,229,287,357,444,519,594]⟩]⟩
def row8_349 : State := ⟨[6,158,229,287,357,444,519,588,594],[]⟩
def row8_350 : State := ⟨[66,158,229,287,357,444,519,623,656],[⟨0,0,[66,158,229,287,357,444,519,594]⟩]⟩
def row8_351 : State := ⟨[66,158,229,277,287,357,444,519,594],[]⟩
def row8_352 : State := ⟨[51,66,158,229,287,357,444,519,594],[⟨6,40,[71,158,229,287,357,444,519,594]⟩,⟨10,3,[66,165,229,287,357,444,519,594]⟩,⟨7,3,[66,158,236,287,357,444,519,594]⟩,⟨6,213,[66,158,229,303,357,444,519,594]⟩]⟩
def row8_353 : State := ⟨[66,158,229,270,287,357,448,519,594],[]⟩
def row8_354 : State := ⟨[66,158,229,270,287,357,444,519,600],[]⟩
def row8_355 : State := ⟨[66,158,229,270,287,357,444,519,598],[]⟩
def row8_356 : State := ⟨[66,158,229,287,358,444,519,588,594],[]⟩
def row8_357 : State := ⟨[66,158,229,287,357,444,519,595,656],[]⟩
def row8_358 : State := ⟨[66,158,229,270,294,357,444,519,594],[]⟩
def row8_359 : State := ⟨[66,158,229,287,357,444,553,629,665],[]⟩
def row8_360 : State := ⟨[66,158,229,287,357,444,553,637,665],[⟨6,111,[158,253,287,357,444,553,637,665]⟩]⟩
def row8_361 : State := ⟨[10,66,158,229,287,357,444,553,665],[⟨8,223,[68,158,229,287,357,444,553,665]⟩,⟨1,224,[66,158,239,287,357,444,553,665]⟩,⟨0,225,[66,158,229,287,364,444,553,665]⟩,⟨0,226,[10,66,158,229,287,357,444,521]⟩]⟩
def row8_362 : State := ⟨[48,66,158,229,287,357,444,519,656],[⟨6,135,[68,158,229,287,357,444,519,656]⟩,⟨0,227,[66,158,229,297,357,444,519,656]⟩]⟩
def row8_363 : State := ⟨[66,158,229,287,357,444,519,595],[⟨3,226,[35,66,158,229,287,357,519,595]⟩,⟨3,13,[66,158,229,287,357,465,519,595]⟩]⟩
def row8_364 : State := ⟨[66,158,229,287,357,444,519,595,629],[]⟩
def row8_365 : State := ⟨[66,158,165,229,287,357,444,519,594],[]⟩
def row8_366 : State := ⟨[66,158,229,287,357,444,507,519,594],[]⟩
def row8_367 : State := ⟨[66,158,229,287,357,444,519,612],[⟨7,33,[66,158,253,287,357,444,519,612]⟩,⟨6,33,[66,158,229,310,357,444,519,612]⟩]⟩
def row8_368 : State := ⟨[66,158,161,229,287,357,444,519,594],[]⟩
def row8_369 : State := ⟨[2,66,161,229,287,357,444,519,594],[⟨9,228,[66,161,232,287,357,444,519,594]⟩,⟨8,228,[66,161,229,290,357,444,519,594]⟩,⟨4,229,[66,161,229,287,360,444,519,594]⟩,⟨5,230,[66,161,229,287,357,445,519,594]⟩,⟨4,230,[66,161,229,287,357,444,520,594]⟩,⟨4,231,[66,161,229,287,357,444,519,597]⟩]⟩
def row8_370 : State := ⟨[66,158,229,287,357,444,519,603],[⟨6,34,[66,177,229,287,357,444,519,603]⟩,⟨6,35,[66,158,253,287,357,444,519,603]⟩,⟨10,232,[15,66,229,287,357,444,519,603]⟩]⟩
def row8_371 : State := ⟨[66,158,163,229,287,357,444,519,594],[⟨0,29,[12,66,158,229,287,357,444,519]⟩]⟩
def row8_372 : State := ⟨[2,66,158,229,290,357,444,519,594],[⟨8,228,[66,161,229,290,357,444,519,594]⟩,⟨6,233,[66,158,232,290,357,444,519,594]⟩,⟨0,234,[66,158,229,290,360,444,519,594]⟩,⟨0,235,[66,158,229,290,357,445,519,594]⟩,⟨0,236,[66,158,229,290,357,444,520,594]⟩,⟨0,237,[66,158,229,290,357,444,519,597]⟩]⟩
def row8_373 : State := ⟨[66,158,229,287,360,444,519,594],[⟨6,127,[158,177,229,287,360,444,519,594]⟩]⟩
def row8_374 : State := ⟨[66,71,158,229,287,357,444,519,594],[]⟩
def row8_375 : State := ⟨[2,66,158,229,287,360,444,519,594],[⟨4,229,[66,161,229,287,360,444,519,594]⟩,⟨1,234,[66,158,232,287,360,444,519,594]⟩,⟨0,234,[66,158,229,290,360,444,519,594]⟩,⟨1,238,[66,158,229,287,360,445,519,594]⟩,⟨0,238,[66,158,229,287,360,444,520,594]⟩,⟨0,239,[66,158,229,287,360,444,519,597]⟩]⟩
def row8_376 : State := ⟨[2,66,158,229,287,357,444,520,594],[⟨4,230,[66,161,229,287,357,444,520,594]⟩,⟨1,235,[66,158,232,287,357,444,520,594]⟩,⟨0,236,[66,158,229,290,357,444,520,594]⟩,⟨0,238,[66,158,229,287,360,444,520,594]⟩,⟨4,240,[66,158,229,287,357,445,520,594]⟩,⟨0,241,[66,158,229,287,357,444,520,597]⟩]⟩
def row8_377 : State := ⟨[2,22,66,158,229,287,357,444,594],[⟨2,110,[24,66,158,229,287,357,444,594]⟩,⟨0,242,[2,66,158,229,287,367,444,594]⟩,⟨4,226,[22,66,158,229,287,357,445,594]⟩,⟨2,243,[22,66,158,229,287,357,444,597]⟩]⟩
def row8_378 : State := ⟨[66,158,229,287,357,444,519,597],[⟨6,128,[158,177,229,287,357,444,519,597]⟩,⟨3,243,[35,66,158,229,287,357,519,597]⟩,⟨3,36,[66,158,229,287,357,465,519,597]⟩,⟨2,243,[22,66,158,229,287,357,444,597]⟩,⟨2,36,[66,158,229,287,357,444,549,597]⟩,⟨0,216,[6,158,229,287,357,444,519,597]⟩]⟩
def row8_379 : State := ⟨[66,158,170,229,287,357,444,519,594],[⟨6,212,[34,66,158,229,287,444,519,594]⟩]⟩
def row8_380 : State := ⟨[2,66,158,229,287,357,444,519,597],[⟨4,231,[66,161,229,287,357,444,519,597]⟩,⟨1,237,[66,158,232,287,357,444,519,597]⟩,⟨0,237,[66,158,229,290,357,444,519,597]⟩,⟨0,239,[66,158,229,287,360,444,519,597]⟩,⟨1,241,[66,158,229,287,357,445,519,597]⟩,⟨0,241,[66,158,229,287,357,444,520,597]⟩]⟩
def row8_381 : State := ⟨[0,5,158,229,287,357,444,519,594],[⟨0,212,[6,158,229,287,357,444,519,594]⟩,⟨3,244,[5,158,229,288,357,444,519,594]⟩]⟩
def row8_382 : State := ⟨[66,158,229,270,287,357,455,519,594],[]⟩
def row8_383 : State := ⟨[66,158,229,270,287,357,444,519,603],[]⟩
def row8_384 : State := ⟨[66,158,229,287,360,444,519,588,594],[]⟩
def row8_385 : State := ⟨[66,158,229,270,303,357,444,519,594],[]⟩
def row8_386 : State := ⟨[66,109,158,229,287,357,444,519,594],[]⟩
def row8_387 : State := ⟨[66,132,158,229,287,357,444,519,594],[]⟩
def row8_388 : State := ⟨[66,158,229,270,287,357,444,519,609],[]⟩
def row8_389 : State := ⟨[66,158,229,270,287,357,459,519,594],[⟨6,244,[21,66,158,229,287,459,519,594]⟩]⟩
def row8_390 : State := ⟨[66,158,229,287,358,444,519,594,665],[]⟩
def row8_391 : State := ⟨[66,158,229,287,357,444,519,595,665],[⟨0,0,[66,158,229,287,357,444,519,594]⟩]⟩
def row8_392 : State := ⟨[66,158,229,274,287,357,444,519,594],[⟨6,212,[34,66,158,229,287,444,519,594]⟩]⟩
def row8_393 : State := ⟨[66,112,158,229,287,357,444,519,594],[⟨10,213,[66,170,229,287,357,444,519,594]⟩]⟩
def row8_394 : State := ⟨[66,158,229,287,357,444,519,600,656],[⟨0,0,[66,158,229,287,357,444,519,594]⟩]⟩
def row8_395 : State := ⟨[66,158,229,271,287,357,444,519,594],[]⟩
def row8_396 : State := ⟨[66,158,229,270,288,357,444,519,594],[]⟩
def row8_397 : State := ⟨[66,158,229,270,287,358,444,519,594],[]⟩
def row8_398 : State := ⟨[66,158,229,270,287,357,444,519,595],[]⟩
def row8_399 : State := ⟨[66,158,210,229,287,357,444,519,594],[]⟩
def row8_400 : State := ⟨[66,158,229,287,357,444,505,519,594],[]⟩
def row8_401 : State := ⟨[66,158,173,229,287,357,444,519,594],[]⟩
def row8_402 : State := ⟨[66,158,229,265,287,357,444,519,594],[]⟩
def row8_403 : State := ⟨[66,158,211,229,287,357,444,519,594],[]⟩
def row8_404 : State := ⟨[66,158,229,287,335,357,444,519,594],[]⟩
def row8_405 : State := ⟨[66,110,158,229,287,357,444,519,594],[]⟩
def row8_406 : State := ⟨[43,66,158,229,287,357,444,519,594],[⟨10,113,[66,161,229,287,357,444,519,594]⟩,⟨7,112,[66,158,232,287,357,444,519,594]⟩,⟨6,112,[66,158,229,290,357,444,519,594]⟩]⟩
def row8_407 : State := ⟨[66,158,229,287,357,444,519,594,689],[]⟩
def row8_408 : State := ⟨[66,158,229,287,364,444,519,588,594],[⟨0,221,[66,158,229,287,364,444,519,671]⟩]⟩
def row8_409 : State := ⟨[66,158,229,287,357,444,519,604,656],[⟨0,0,[66,158,229,287,357,444,519,594]⟩]⟩
def row8_410 : State := ⟨[66,158,229,275,287,357,444,519,594],[]⟩
def row8_411 : State := ⟨[66,158,229,270,287,370,444,519,594],[⟨0,220,[66,158,229,339,370,444,519,594]⟩]⟩
def row8_412 : State := ⟨[66,158,229,270,287,357,444,519,615],[]⟩
def row8_413 : State := ⟨[66,158,229,264,287,357,444,519,594],[]⟩
def row8_414 : State := ⟨[66,158,229,287,357,444,519,600,665],[⟨0,0,[66,158,229,287,357,444,519,594]⟩]⟩
def row8_415 : State := ⟨[66,158,229,270,289,357,444,519,594],[]⟩
def row8_416 : State := ⟨[66,158,229,287,357,444,519,598,656],[⟨10,245,[15,66,229,287,357,444,519,656]⟩,⟨0,0,[66,158,229,287,357,444,519,594]⟩]⟩
def row8_417 : State := ⟨[66,158,229,272,287,357,444,519,594],[⟨7,9,[66,146,158,229,287,357,444,594]⟩]⟩
def row8_418 : State := ⟨[66,158,229,270,287,359,444,519,594],[]⟩
def row8_419 : State := ⟨[0,35,66,158,229,322,357,519,594],[⟨3,245,[36,66,158,229,322,357,519,594]⟩,⟨0,246,[0,66,158,229,322,370,519,594]⟩,⟨3,247,[35,66,158,229,322,357,520,594]⟩,⟨3,248,[35,66,158,229,322,357,519,595]⟩]⟩
def row8_420 : State := ⟨[0,66,127,158,229,287,357,519,594],[⟨6,9,[66,128,158,229,287,357,519,594]⟩,⟨6,249,[66,127,158,229,287,357,520,594]⟩,⟨6,250,[66,127,158,229,287,357,519,595]⟩]⟩
def row8_421 : State := ⟨[66,158,229,270,287,357,445,519,594],[⟨2,247,[22,66,158,270,287,357,445,594]⟩,⟨7,249,[66,145,158,229,287,357,445,594]⟩]⟩
def row8_422 : State := ⟨[66,158,229,270,287,357,444,519,596],[⟨2,248,[22,66,158,270,287,357,444,596]⟩,⟨7,250,[66,145,158,229,287,357,444,596]⟩]⟩
def row8_423 : State := ⟨[48,66,229,270,287,357,444,519,594],[⟨10,11,[68,229,270,287,357,444,519,594]⟩]⟩
def row8_424 : State := ⟨[66,134,158,229,287,357,444,519,594],[⟨10,7,[66,171,229,287,357,444,519,594]⟩]⟩
def row8_425 : State := ⟨[66,158,229,322,357,444,519,644,656],[⟨2,251,[66,229,322,357,480,519,644,656]⟩,⟨0,227,[66,158,229,297,357,444,519,656]⟩,⟨6,227,[66,158,229,322,357,444,519,615]⟩]⟩
def row8_426 : State := ⟨[66,158,229,287,357,444,563,637,665],[⟨3,251,[66,270,287,357,444,563,637,665]⟩,⟨3,252,[66,158,229,287,357,444,516,665]⟩]⟩
def row8_427 : State := ⟨[10,66,158,229,287,357,444,563,665],[⟨8,253,[68,158,229,287,357,444,563,665]⟩,⟨1,254,[66,158,239,287,357,444,563,665]⟩,⟨0,255,[66,158,229,287,364,444,563,665]⟩]⟩
def row8_428 : State := ⟨[66,89,158,229,287,357,444,519,665],[⟨1,227,[66,158,239,287,357,444,519,665]⟩]⟩
def row8_429 : State := ⟨[66,89,270,287,357,444,519,594,637],[]⟩
def row8_430 : State := ⟨[66,158,229,287,357,444,519,604],[⟨7,227,[66,158,270,287,357,444,519,604]⟩]⟩
def row8_431 : State := ⟨[66,158,229,287,357,444,519,604,665],[]⟩
def row8_432 : State := ⟨[66,158,229,287,357,444,519,604,637],[]⟩
def row8_433 : State := ⟨[66,89,229,270,287,357,444,519,594],[]⟩
def row8_434 : State := ⟨[66,158,166,229,287,357,444,519,594],[]⟩
def row8_435 : State := ⟨[66,158,229,287,357,444,519,594,680],[]⟩
def row8_436 : State := ⟨[66,158,229,322,370,444,519,594],[⟨2,15,[66,177,229,322,370,444,519,594]⟩,⟨0,220,[66,158,229,339,370,444,519,594]⟩,⟨4,256,[66,229,322,370,430,444,519,594]⟩,⟨6,257,[39,66,158,229,370,444,519,594]⟩,⟨0,246,[0,66,158,229,322,370,519,594]⟩,⟨4,253,[66,229,322,370,444,480,519,594]⟩,⟨0,258,[66,158,229,322,370,519,588,594]⟩,⟨0,259,[10,66,229,322,370,444,519,594]⟩,⟨0,260,[66,158,229,322,370,519,594,656]⟩]⟩
def row8_437 : State := ⟨[66,68,158,229,287,357,444,519,656],[⟨9,223,[68,158,229,287,357,468,519,656]⟩,⟨0,110,[13,66,158,229,287,357,444,519]⟩]⟩
def row8_438 : State := ⟨[10,66,229,270,287,364,444,519,594],[⟨10,261,[68,229,270,287,364,444,519,594]⟩,⟨5,262,[66,239,270,287,364,444,519,594]⟩,⟨4,263,[66,229,270,297,364,444,519,594]⟩,⟨4,264,[66,229,270,287,364,450,519,594]⟩,⟨4,265,[66,229,270,287,364,444,526,594]⟩]⟩
def row8_439 : State := ⟨[10,66,158,229,297,357,444,519,665],[⟨7,264,[68,158,229,297,357,444,519,665]⟩,⟨7,266,[66,158,239,297,357,444,519,665]⟩,⟨0,267,[66,158,229,297,364,444,519,665]⟩,⟨0,268,[66,158,229,297,357,450,519,665]⟩]⟩
def row8_440 : State := ⟨[10,66,229,270,287,357,444,519,656],[⟨6,258,[68,229,270,287,357,444,519,656]⟩,⟨4,258,[66,229,270,287,364,444,519,656]⟩]⟩
def row8_441 : State := ⟨[66,158,229,297,357,444,519,656],[⟨0,224,[66,158,229,297,357,468,519,656]⟩,⟨0,254,[66,158,229,297,357,480,519,656]⟩,⟨3,269,[35,66,158,229,297,357,519,656]⟩,⟨0,16,[66,158,229,297,357,465,519,656]⟩]⟩
def row8_442 : State := ⟨[66,158,166,229,287,357,444,594,665],[⟨0,269,[10,66,166,229,287,357,444,665]⟩]⟩
def row8_443 : State := ⟨[10,66,158,229,297,357,444,519,656],[⟨6,265,[68,158,229,297,357,444,519,656]⟩,⟨6,266,[66,158,239,297,357,444,519,656]⟩,⟨0,270,[66,158,229,297,364,444,519,656]⟩,⟨0,271,[66,158,229,297,357,450,519,656]⟩,⟨0,272,[66,158,229,297,357,444,526,656]⟩]⟩
def row8_444 : State := ⟨[10,66,229,270,287,357,444,519,665],[⟨7,260,[68,229,270,287,357,444,519,665]⟩,⟨4,260,[66,229,270,287,364,444,519,665]⟩,⟨0,273,[10,22,66,270,287,357,444,665]⟩]⟩
def row8_445 : State := ⟨[66,158,229,287,364,444,519,656],[⟨4,258,[66,229,270,287,364,444,519,656]⟩,⟨5,260,[66,229,287,322,364,444,519,656]⟩,⟨10,20,[15,66,229,287,364,444,519,656]⟩,⟨1,225,[66,158,229,287,364,468,519,656]⟩,⟨1,255,[66,158,229,287,364,480,519,656]⟩,⟨3,274,[35,66,158,229,287,364,519,656]⟩,⟨1,275,[66,158,229,287,364,466,519,656]⟩,⟨2,242,[4,66,158,229,287,364,444,519]⟩,⟨0,221,[66,158,229,287,364,444,519,671]⟩]⟩
def row8_446 : State := ⟨[66,68,229,270,287,357,444,519,594],[⟨11,17,[68,253,270,287,357,444,519,594]⟩,⟨0,245,[12,66,229,270,287,357,444,519]⟩]⟩
def row8_447 : State := ⟨[10,66,158,229,287,364,444,519,656],[⟨0,261,[68,158,229,287,364,444,519,656]⟩,⟨1,267,[66,158,239,287,364,444,519,656]⟩,⟨0,270,[66,158,229,297,364,444,519,656]⟩,⟨1,276,[66,158,229,287,364,450,519,656]⟩,⟨0,277,[66,158,229,287,364,444,526,656]⟩]⟩
def row8_448 : State := ⟨[10,66,158,229,287,357,444,526,665],[⟨6,262,[68,158,229,287,357,444,526,665]⟩,⟨1,271,[66,158,239,287,357,444,526,665]⟩,⟨0,276,[66,158,229,287,364,444,526,665]⟩]⟩
def row8_449 : State := ⟨[10,22,66,158,229,287,357,444,665],[⟨0,278,[25,66,158,229,287,357,444,665]⟩,⟨7,259,[22,68,158,229,287,357,444,665]⟩,⟨10,259,[10,72,158,229,287,357,444,665]⟩,⟨0,269,[10,66,166,229,287,357,444,665]⟩,⟨2,269,[22,66,158,239,287,357,444,665]⟩,⟨0,273,[10,22,66,270,287,357,444,665]⟩,⟨2,274,[22,66,158,229,287,364,444,665]⟩,⟨0,274,[10,66,158,229,287,367,444,665]⟩]⟩
def row8_450 : State := ⟨[10,66,158,229,287,357,444,526,656],[⟨6,263,[68,158,229,287,357,444,526,656]⟩,⟨1,268,[66,158,239,287,357,444,526,656]⟩,⟨0,272,[66,158,229,297,357,444,526,656]⟩,⟨0,277,[66,158,229,287,364,444,526,656]⟩]⟩
def row8_451 : State := ⟨[66,158,229,287,364,444,519,594,656],[]⟩
def row8_452 : State := ⟨[66,158,229,270,297,357,444,519,594],[]⟩
def row8_453 : State := ⟨[66,158,229,270,287,364,444,519,594],[]⟩
def row8_454 : State := ⟨[66,158,229,270,287,357,450,519,594],[]⟩
def row8_455 : State := ⟨[66,158,229,270,287,357,444,519,604],[]⟩
def row8_456 : State := ⟨[66,139,158,229,287,357,444,519,594],[⟨0,29,[12,66,158,229,287,357,444,519]⟩]⟩
def row8_457 : State := ⟨[66,158,217,229,287,357,444,519,594],[]⟩
def row8_458 : State := ⟨[66,123,229,270,287,357,444,519,594],[]⟩
def row8_459 : State := ⟨[66,158,229,268,287,357,444,519,594],[]⟩
def row8_460 : State := ⟨[66,123,229,287,322,357,444,519,594],[⟨11,227,[66,229,287,322,357,450,519,594]⟩]⟩
def row8_461 : State := ⟨[66,140,158,229,287,357,444,519,594],[⟨6,9,[66,128,158,229,287,357,519,594]⟩]⟩
def row8_462 : State := ⟨[66,123,158,229,287,357,450,519,594],[]⟩
def row8_463 : State := ⟨[66,158,218,229,287,357,444,519,594],[]⟩
def row8_464 : State := ⟨[10,66,158,229,287,357,444,519,656],[⟨6,135,[68,158,229,287,357,444,519,656]⟩,⟨0,227,[66,158,229,297,357,444,519,656]⟩,⟨0,11,[66,158,229,287,364,444,519,656]⟩]⟩
def row8_465 : State := ⟨[66,157,158,229,287,357,444,519,594],[]⟩
def row8_466 : State := ⟨[66,158,229,287,357,444,519,594,686],[]⟩
def row8_467 : State := ⟨[66,158,229,287,357,444,519,634,665],[⟨0,0,[66,158,229,287,357,444,519,594]⟩]⟩
def row8_468 : State := ⟨[66,158,229,287,336,357,444,519,594],[]⟩
def row8_469 : State := ⟨[66,89,229,287,322,357,444,519,594],[]⟩
def row8_470 : State := ⟨[66,158,194,229,287,357,444,519,594],[]⟩
def row8_471 : State := ⟨[66,158,213,229,287,357,444,519,594],[]⟩
def row8_472 : State := ⟨[66,158,229,263,287,357,444,519,594],[]⟩
def row8_473 : State := ⟨[0,66,158,229,287,357,464,519,594],[⟨4,279,[66,159,229,287,357,464,519,594]⟩,⟨1,279,[66,158,230,287,357,464,519,594]⟩,⟨0,280,[66,158,229,288,357,464,519,594]⟩,⟨5,281,[66,158,229,287,357,464,520,594]⟩,⟨3,281,[66,158,229,287,357,464,519,595]⟩]⟩
def row8_474 : State := ⟨[55,66,158,229,287,357,444,519,594],[⟨0,2,[66,158,229,287,358,444,519,594]⟩]⟩
def row8_475 : State := ⟨[66,158,229,287,357,444,519,623,637],[⟨0,0,[66,158,229,287,357,444,519,594]⟩]⟩
def row8_476 : State := ⟨[66,158,229,287,357,444,487,519,594],[]⟩
def row8_477 : State := ⟨[66,158,229,287,357,444,519,623,674],[⟨0,0,[66,158,229,287,357,444,519,594]⟩]⟩
def row8_478 : State := ⟨[66,158,229,287,357,444,519,594,703],[]⟩
def row8_479 : State := ⟨[54,66,158,229,287,357,444,519,600],[⟨6,279,[66,158,251,287,357,444,519,600]⟩]⟩
def row8_480 : State := ⟨[54,66,158,229,287,357,444,519,598],[⟨6,280,[66,174,229,287,357,444,519,598]⟩]⟩
def row8_481 : State := ⟨[54,66,158,229,287,358,444,519,594],[]⟩
def row8_482 : State := ⟨[54,66,158,229,287,357,444,519,595],[⟨3,281,[66,158,229,287,357,464,519,595]⟩]⟩
def row8_483 : State := ⟨[66,135,158,229,287,357,444,519,594],[]⟩
def row8_484 : State := ⟨[59,66,158,229,287,357,444,519,594],[⟨10,6,[68,158,229,287,357,444,519,594]⟩,⟨0,6,[66,158,229,287,364,444,519,594]⟩]⟩
def row8_485 : State := ⟨[54,66,158,229,287,364,444,519,594],[]⟩
def row8_486 : State := ⟨[54,66,158,229,287,357,444,519,604],[]⟩
def row8_487 : State := ⟨[66,158,229,287,357,380,444,519,600],[⟨6,52,[158,253,287,357,380,444,519,600]⟩]⟩
def row8_488 : State := ⟨[66,158,229,287,357,380,444,519,598],[⟨6,53,[177,229,287,357,380,444,519,598]⟩]⟩
def row8_489 : State := ⟨[66,158,229,287,357,380,444,519,595],[⟨3,54,[66,158,229,287,380,465,519,595]⟩]⟩
def row8_490 : State := ⟨[47,67,158,229,287,357,444,519,594],[⟨7,282,[67,158,236,287,357,444,519,594]⟩,⟨6,282,[67,158,229,294,357,444,519,594]⟩]⟩
def row8_491 : State := ⟨[47,66,158,229,294,357,444,519,594],[⟨6,282,[67,158,229,294,357,444,519,594]⟩,⟨6,283,[66,158,236,294,357,444,519,594]⟩]⟩
def row8_492 : State := ⟨[66,158,229,287,357,416,444,519,594],[]⟩
def row8_493 : State := ⟨[66,158,229,287,357,417,444,519,594],[⟨10,1,[66,158,229,287,347,357,444,519]⟩]⟩
def row8_494 : State := ⟨[10,47,66,229,287,357,444,519,594],[⟨0,1,[49,66,229,287,357,444,519,594]⟩,⟨0,284,[47,68,229,287,357,444,519,594]⟩,⟨11,226,[10,66,236,287,357,444,519,594]⟩,⟨10,226,[10,66,229,294,357,444,519,594]⟩]⟩
def row8_495 : State := ⟨[49,66,229,287,357,380,444,519,594],[]⟩
def row8_496 : State := ⟨[66,158,229,287,380,403,444,519,594],[⟨0,0,[66,158,229,287,357,444,519,594]⟩]⟩
def row8_497 : State := ⟨[66,158,229,287,357,409,444,519,594],[]⟩
def row8_498 : State := ⟨[66,158,229,287,353,357,444,519,594],[]⟩
def row8_499 : State := ⟨[66,158,229,287,364,380,444,519,594],[⟨0,0,[66,158,229,287,357,444,519,594]⟩,⟨10,284,[66,158,229,287,344,364,444,519]⟩]⟩
def row8_500 : State := ⟨[66,158,229,287,357,380,444,519,604],[]⟩
def row8_501 : State := ⟨[66,158,229,287,357,382,444,519,594],[⟨0,1,[49,66,229,287,357,444,519,594]⟩,⟨10,1,[66,158,229,287,347,357,444,519]⟩]⟩
def row8_502 : State := ⟨[66,158,229,287,354,357,444,519,594],[]⟩
def row8_503 : State := ⟨[0,66,158,229,289,357,444,519,594],[⟨8,285,[66,159,229,289,357,444,519,594]⟩,⟨6,286,[66,158,230,289,357,444,519,594]⟩,⟨6,112,[66,158,229,290,357,444,519,594]⟩,⟨0,287,[66,158,229,289,358,444,519,594]⟩,⟨0,288,[66,158,229,289,357,444,520,594]⟩,⟨0,289,[66,158,229,289,357,444,519,595]⟩]⟩
def row8_504 : State := ⟨[66,158,229,287,357,425,444,519,600],[]⟩
def row8_505 : State := ⟨[0,66,158,230,287,357,444,519,594],[⟨9,290,[66,159,230,287,357,444,519,594]⟩,⟨6,291,[66,158,230,288,357,444,519,594]⟩,⟨1,292,[66,158,230,287,358,444,519,594]⟩,⟨1,293,[66,158,230,287,357,444,520,594]⟩,⟨1,294,[66,158,230,287,357,444,519,595]⟩]⟩
def row8_506 : State := ⟨[66,158,229,287,357,425,444,523,594],[]⟩
def row8_507 : State := ⟨[0,66,158,233,287,357,444,519,594],[⟨11,285,[66,159,233,287,357,444,519,594]⟩,⟨7,113,[66,158,234,287,357,444,519,594]⟩,⟨7,295,[66,158,233,288,357,444,519,594]⟩,⟨3,296,[66,158,233,287,358,444,519,594]⟩,⟨3,297,[66,158,233,287,357,444,520,594]⟩,⟨3,298,[66,158,233,287,357,444,519,595]⟩]⟩
def row8_508 : State := ⟨[66,158,229,287,357,425,444,535,594],[]⟩
def row8_509 : State := ⟨[0,66,158,229,287,357,444,519,600],[⟨4,299,[66,159,229,287,357,444,519,600]⟩,⟨1,300,[66,158,230,287,357,444,519,600]⟩,⟨0,301,[66,158,229,288,357,444,519,600]⟩,⟨0,302,[66,158,229,287,358,444,519,600]⟩,⟨0,303,[66,158,229,287,357,444,520,600]⟩,⟨0,304,[66,158,229,287,357,444,519,601]⟩]⟩
def row8_510 : State := ⟨[66,158,229,287,357,444,468,519,600],[]⟩
def row8_511 : State := ⟨[66,118,158,229,287,357,444,519,600],[]⟩
def row8_512 : State := ⟨[66,158,229,287,357,444,480,519,600],[]⟩
def row8_513 : State := ⟨[66,118,158,229,287,357,444,523,594],[]⟩
def row8_514 : State := ⟨[66,158,229,287,357,444,480,523,594],[]⟩
def row8_515 : State := ⟨[10,66,158,229,287,357,444,535,594],[⟨10,305,[68,158,229,287,357,444,535,594]⟩,⟨10,306,[66,158,239,287,357,444,535,594]⟩,⟨10,307,[66,158,229,297,357,444,535,594]⟩,⟨0,308,[66,158,229,287,364,444,535,594]⟩,⟨5,309,[66,158,229,287,357,450,535,594]⟩,⟨2,310,[66,158,229,287,357,444,537,594]⟩]⟩
def row8_516 : State := ⟨[66,158,229,287,357,444,519,600,691],[]⟩
def row8_517 : State := ⟨[0,66,158,229,287,357,444,519,609],[⟨4,311,[66,159,229,287,357,444,519,609]⟩,⟨1,312,[66,158,230,287,357,444,519,609]⟩,⟨0,313,[66,158,229,288,357,444,519,609]⟩,⟨0,314,[66,158,229,287,358,444,519,609]⟩,⟨0,315,[66,158,229,287,357,444,520,609]⟩,⟨1,316,[66,158,229,287,357,444,519,610]⟩]⟩
def row8_518 : State := ⟨[66,158,229,287,357,444,468,519,609],[⟨7,57,[158,229,310,357,444,468,519,609]⟩]⟩
def row8_519 : State := ⟨[66,118,158,229,287,357,444,519,609],[]⟩
def row8_520 : State := ⟨[66,158,229,287,357,444,480,519,609],[]⟩
def row8_521 : State := ⟨[10,66,158,229,287,357,444,523,594],[⟨8,317,[68,158,229,287,357,444,523,594]⟩,⟨8,318,[66,158,239,287,357,444,523,594]⟩,⟨8,319,[66,158,229,297,357,444,523,594]⟩,⟨0,320,[66,158,229,287,364,444,523,594]⟩,⟨5,321,[66,158,229,287,357,450,523,594]⟩,⟨2,42,[66,158,229,287,357,444,530,594]⟩]⟩
def row8_522 : State := ⟨[66,158,229,287,357,444,519,600,681],[]⟩
def row8_523 : State := ⟨[66,118,158,229,287,357,444,535,594],[]⟩
def row8_524 : State := ⟨[66,158,229,287,357,444,480,535,594],[]⟩
def row8_525 : State := ⟨[0,66,158,229,287,357,448,519,594],[⟨4,322,[66,159,229,287,357,448,519,594]⟩,⟨9,300,[66,158,230,287,357,448,519,594]⟩,⟨0,323,[66,158,229,288,357,448,519,594]⟩,⟨0,324,[66,158,229,287,358,448,519,594]⟩,⟨5,325,[66,158,229,287,357,448,520,594]⟩,⟨3,326,[66,158,229,287,357,448,519,595]⟩]⟩
def row8_526 : State := ⟨[66,158,229,287,357,444,519,600,631],[]⟩
def row8_527 : State := ⟨[10,66,158,229,287,357,444,519,600],[⟨6,327,[68,158,229,287,357,444,519,600]⟩,⟨6,328,[66,158,239,287,357,444,519,600]⟩,⟨6,329,[66,158,229,297,357,444,519,600]⟩,⟨0,330,[66,158,229,287,364,444,519,600]⟩,⟨1,331,[66,158,229,287,357,450,519,600]⟩,⟨2,332,[66,158,229,287,357,444,526,600]⟩]⟩
def row8_528 : State := ⟨[66,158,229,287,357,444,519,600,676],[]⟩
def row8_529 : State := ⟨[66,118,158,229,287,357,454,519,594],[]⟩
def row8_530 : State := ⟨[66,158,229,287,357,444,519,600,647],[]⟩
def row8_531 : State := ⟨[42,66,158,230,287,357,444,519,594],[⟨9,290,[66,159,230,287,357,444,519,594]⟩,⟨6,291,[66,158,230,288,357,444,519,594]⟩]⟩
def row8_532 : State := ⟨[66,158,229,287,357,444,519,600,658],[]⟩
def row8_533 : State := ⟨[66,158,229,287,357,444,519,600,668],[⟨4,333,[66,158,226,287,357,444,519,600]⟩]⟩
def row8_534 : State := ⟨[66,158,229,287,357,444,519,600,629],[⟨0,0,[66,158,229,287,357,444,519,594]⟩]⟩
def row8_535 : State := ⟨[66,158,229,287,357,426,444,519,594],[]⟩
def row8_536 : State := ⟨[66,118,158,229,287,357,448,519,594],[]⟩
def row8_537 : State := ⟨[66,119,158,229,287,357,444,519,594],[⟨10,4,[66,159,229,287,357,444,519,594]⟩]⟩
def row8_538 : State := ⟨[66,158,229,287,357,444,519,600,644],[⟨0,0,[66,158,229,287,357,444,519,594]⟩]⟩
def row8_539 : State := ⟨[66,158,229,287,357,444,481,519,594],[]⟩
def row8_540 : State := ⟨[66,158,229,287,357,444,519,600,674],[⟨0,0,[66,158,229,287,357,444,519,594]⟩]⟩
def row8_541 : State := ⟨[66,158,229,287,357,444,519,594,675],[]⟩
def row8_542 : State := ⟨[66,158,229,287,357,444,535,609],[⟨0,59,[66,158,229,310,357,444,535,609]⟩]⟩
def row8_543 : State := ⟨[66,158,159,230,287,357,444,519,594],[]⟩
def row8_544 : State := ⟨[0,66,159,230,287,357,444,519,594],[⟨6,334,[66,159,230,288,357,444,519,594]⟩,⟨3,335,[66,159,230,287,358,444,519,594]⟩,⟨8,336,[66,159,230,287,357,444,520,594]⟩,⟨6,336,[66,159,230,287,357,444,519,595]⟩]⟩
def row8_545 : State := ⟨[66,158,229,287,357,444,523,598],[⟨4,60,[66,177,229,287,357,444,523,598]⟩,⟨10,337,[15,66,229,287,357,444,523,598]⟩]⟩
def row8_546 : State := ⟨[66,158,162,229,291,357,444,519,594],[⟨0,130,[12,66,158,229,291,357,444,519]⟩]⟩
def row8_547 : State := ⟨[0,66,158,230,288,357,444,519,594],[⟨6,334,[66,159,230,288,357,444,519,594]⟩,⟨0,338,[66,158,230,288,358,444,519,594]⟩,⟨8,339,[66,158,230,288,357,444,520,594]⟩,⟨6,340,[66,158,230,288,357,444,519,595]⟩]⟩
def row8_548 : State := ⟨[66,158,229,289,359,444,519,594],[⟨2,341,[22,66,158,229,289,359,444,594]⟩,⟨0,61,[66,158,229,289,359,444,549,594]⟩]⟩
def row8_549 : State := ⟨[66,67,158,229,287,357,444,523,594],[⟨8,61,[67,177,229,287,357,444,523,594]⟩,⟨8,91,[66,177,229,287,357,444,523,594]⟩]⟩
def row8_550 : State := ⟨[0,66,158,230,287,358,444,519,594],[⟨3,335,[66,159,230,287,358,444,519,594]⟩,⟨0,338,[66,158,230,288,358,444,519,594]⟩,⟨1,342,[66,158,230,287,358,444,520,594]⟩,⟨1,343,[66,158,230,287,358,444,519,595]⟩]⟩
def row8_551 : State := ⟨[0,35,66,158,230,287,357,519,594],[⟨3,130,[36,66,158,230,287,357,519,594]⟩,⟨3,341,[35,66,158,230,287,358,519,594]⟩,⟨0,344,[0,66,158,230,287,370,519,594]⟩,⟨3,345,[35,66,158,230,287,357,520,594]⟩,⟨3,346,[35,66,158,230,287,357,519,595]⟩]⟩
def row8_552 : State := ⟨[66,158,229,289,357,445,519,594],[⟨2,345,[22,66,158,229,289,357,445,594]⟩,⟨0,63,[66,158,229,289,357,445,549,594]⟩]⟩
def row8_553 : State := ⟨[66,158,165,229,287,357,444,519,600],[]⟩
def row8_554 : State := ⟨[0,66,158,230,287,357,444,520,594],[⟨8,336,[66,159,230,287,357,444,520,594]⟩,⟨8,339,[66,158,230,288,357,444,520,594]⟩,⟨1,342,[66,158,230,287,358,444,520,594]⟩,⟨1,347,[66,158,230,287,357,444,520,595]⟩]⟩
def row8_555 : State := ⟨[66,158,229,289,357,444,519,596],[⟨2,346,[22,66,158,229,289,357,444,596]⟩,⟨0,64,[66,158,229,289,357,444,549,596]⟩]⟩
def row8_556 : State := ⟨[66,158,165,229,287,357,454,519,594],[]⟩
def row8_557 : State := ⟨[0,66,158,230,287,357,444,519,595],[⟨6,336,[66,159,230,287,357,444,519,595]⟩,⟨6,340,[66,158,230,288,357,444,519,595]⟩,⟨1,343,[66,158,230,287,358,444,519,595]⟩,⟨1,347,[66,158,230,287,357,444,520,595]⟩]⟩
def row8_558 : State := ⟨[66,158,159,229,288,357,444,519,594],[]⟩
def row8_559 : State := ⟨[66,158,159,229,287,358,444,519,594],[]⟩
def row8_560 : State := ⟨[66,158,159,229,287,357,444,520,594],[]⟩
def row8_561 : State := ⟨[66,158,159,229,287,357,444,519,595],[]⟩
def row8_562 : State := ⟨[0,66,158,229,288,357,444,519,594],[⟨8,291,[66,159,229,288,357,444,519,594]⟩,⟨6,291,[66,158,230,288,357,444,519,594]⟩,⟨0,348,[66,158,229,288,358,444,519,594]⟩,⟨2,349,[66,158,229,288,357,444,520,594]⟩,⟨0,349,[66,158,229,288,357,444,519,595]⟩]⟩
def row8_563 : State := ⟨[66,158,229,287,357,425,444,519,598],[]⟩
def row8_564 : State := ⟨[0,66,158,231,287,357,444,519,594],[⟨11,295,[66,159,231,287,357,444,519,594]⟩,⟨7,112,[66,158,232,287,357,444,519,594]⟩,⟨6,350,[66,158,231,288,357,444,519,594]⟩,⟨1,351,[66,158,231,287,358,444,519,594]⟩,⟨1,352,[66,158,231,287,357,444,520,594]⟩,⟨1,353,[66,158,231,287,357,444,519,595]⟩]⟩
def row8_565 : State := ⟨[66,158,229,287,357,425,444,532,594],[]⟩
def row8_566 : State := ⟨[0,66,158,229,287,357,444,519,598],[⟨6,323,[66,159,229,287,357,444,519,598]⟩,⟨7,301,[66,158,230,287,357,444,519,598]⟩,⟨0,354,[66,158,229,288,357,444,519,598]⟩,⟨0,355,[66,158,229,287,358,444,519,598]⟩,⟨0,356,[66,158,229,287,357,444,520,598]⟩,⟨0,357,[66,158,229,287,357,444,519,599]⟩]⟩
def row8_567 : State := ⟨[66,158,229,287,357,444,468,519,598],[]⟩
def row8_568 : State := ⟨[66,118,158,229,287,357,444,519,598],[]⟩
def row8_569 : State := ⟨[66,158,229,287,357,444,480,519,598],[]⟩
def row8_570 : State := ⟨[66,118,158,229,287,357,444,532,594],[]⟩
def row8_571 : State := ⟨[66,158,229,287,357,444,480,532,594],[]⟩
def row8_572 : State := ⟨[10,66,158,229,287,357,444,532,594],[⟨10,358,[68,158,229,287,357,444,532,594]⟩,⟨10,359,[66,158,239,287,357,444,532,594]⟩,⟨8,360,[66,158,229,297,357,444,532,594]⟩,⟨0,361,[66,158,229,287,364,444,532,594]⟩,⟨5,362,[66,158,229,287,357,450,532,594]⟩,⟨2,363,[66,158,229,287,357,444,534,594]⟩]⟩
def row8_573 : State := ⟨[66,158,229,287,357,444,519,598,681],[]⟩
def row8_574 : State := ⟨[0,66,158,229,287,357,459,519,594],[⟨11,313,[66,159,229,287,357,459,519,594]⟩,⟨9,313,[66,158,230,287,357,459,519,594]⟩,⟨0,364,[66,158,229,288,357,459,519,594]⟩,⟨0,365,[66,158,229,287,358,459,519,594]⟩,⟨0,93,[0,37,66,158,229,357,519,594]⟩,⟨5,366,[66,158,229,287,357,459,520,594]⟩,⟨3,366,[66,158,229,287,357,459,519,595]⟩]⟩
def row8_575 : State := ⟨[66,158,229,287,357,444,519,598,630],[⟨6,65,[177,229,287,357,444,519,598,630]⟩,⟨0,367,[49,66,229,287,357,444,519,598]⟩]⟩
def row8_576 : State := ⟨[66,118,158,229,287,357,459,519,594],[]⟩
def row8_577 : State := ⟨[66,158,229,287,357,444,519,598,639],[⟨0,368,[66,91,229,287,357,444,519,598]⟩]⟩
def row8_578 : State := ⟨[42,66,158,229,288,357,444,519,594],[⟨8,291,[66,159,229,288,357,444,519,594]⟩,⟨6,291,[66,158,230,288,357,444,519,594]⟩]⟩
def row8_579 : State := ⟨[66,158,229,287,357,444,519,598,657],[⟨10,22,[15,66,229,287,357,444,519,657]⟩,⟨0,369,[66,125,229,287,357,444,519,598]⟩]⟩
def row8_580 : State := ⟨[66,158,229,287,357,444,519,598,629],[⟨6,69,[177,229,287,357,444,519,598,629]⟩,⟨0,0,[66,158,229,287,357,444,519,594]⟩]⟩
def row8_581 : State := ⟨[66,158,229,287,357,427,444,519,594],[⟨10,1,[66,158,229,287,347,357,444,519]⟩]⟩
def row8_582 : State := ⟨[66,158,229,287,357,444,519,598,637],[⟨0,0,[66,158,229,287,357,444,519,594]⟩]⟩
def row8_583 : State := ⟨[66,158,229,287,357,444,482,519,594],[⟨10,94,[66,158,229,287,357,438,444,519]⟩]⟩
def row8_584 : State := ⟨[10,66,158,229,287,357,444,519,598],[⟨6,370,[68,158,229,287,357,444,519,598]⟩,⟨7,371,[66,158,239,287,357,444,519,598]⟩,⟨6,371,[66,158,229,297,357,444,519,598]⟩,⟨0,177,[66,158,229,287,364,444,519,598]⟩,⟨1,372,[66,158,229,287,357,450,519,598]⟩,⟨0,372,[66,158,229,287,357,444,526,598]⟩]⟩
def row8_585 : State := ⟨[12,66,158,229,287,357,444,519],[⟨0,137,[12,68,158,229,287,357,444,519]⟩,⟨0,131,[12,66,162,229,287,357,444,519]⟩,⟨1,203,[12,66,158,241,287,357,444,519]⟩,⟨0,245,[12,66,229,270,287,357,444,519]⟩,⟨0,203,[12,66,158,229,299,357,444,519]⟩,⟨1,245,[12,66,229,287,322,357,444,519]⟩,⟨0,204,[12,66,158,229,287,366,444,519]⟩,⟨6,93,[7,12,66,229,287,357,444,519]⟩,⟨1,205,[12,66,158,229,287,357,451,519]⟩,⟨0,205,[12,66,158,229,287,357,444,528]⟩]⟩
def row8_586 : State := ⟨[12,66,158,229,287,357,444,519,594],[⟨10,6,[68,158,229,287,357,444,519,594]⟩,⟨10,5,[66,162,229,287,357,444,519,594]⟩,⟨9,42,[66,158,241,287,357,444,519,594]⟩,⟨8,42,[66,158,229,299,357,444,519,594]⟩,⟨0,51,[66,158,229,287,366,444,519,594]⟩,⟨3,97,[66,158,229,287,357,451,519,594]⟩,⟨2,97,[66,158,229,287,357,444,528,594]⟩]⟩
def row8_587 : State := ⟨[66,158,229,288,358,444,519,594],[⟨3,373,[36,66,158,229,288,358,519,594]⟩,⟨0,71,[66,158,229,288,358,465,519,594]⟩]⟩
def row8_588 : State := ⟨[66,67,158,229,287,357,444,519,598],[⟨6,71,[67,177,229,287,357,444,519,598]⟩,⟨6,92,[66,177,229,287,357,444,519,598]⟩]⟩
def row8_589 : State := ⟨[0,66,158,229,288,358,444,519,594],[⟨2,338,[66,159,229,288,358,444,519,594]⟩,⟨0,338,[66,158,230,288,358,444,519,594]⟩,⟨2,374,[66,158,229,288,358,444,520,594]⟩,⟨0,374,[66,158,229,288,358,444,519,595]⟩]⟩
def row8_590 : State := ⟨[0,36,66,158,229,288,357,519,594],[⟨5,337,[36,66,159,229,288,357,519,594]⟩,⟨3,337,[36,66,158,230,288,357,519,594]⟩,⟨3,373,[36,66,158,229,288,358,519,594]⟩,⟨0,375,[0,66,158,229,288,371,519,594]⟩,⟨5,376,[36,66,158,229,288,357,520,594]⟩,⟨3,376,[36,66,158,229,288,357,519,595]⟩]⟩
def row8_591 : State := ⟨[66,158,229,288,357,444,519,595],[⟨3,376,[36,66,158,229,288,357,519,595]⟩,⟨0,73,[66,158,229,288,357,465,519,595]⟩]⟩
def row8_592 : State := ⟨[66,158,165,229,287,357,444,532,594],[]⟩
def row8_593 : State := ⟨[0,66,158,229,288,357,444,519,595],[⟨6,339,[66,159,229,288,357,444,519,595]⟩,⟨6,340,[66,158,230,288,357,444,519,595]⟩,⟨0,374,[66,158,229,288,358,444,519,595]⟩,⟨0,377,[66,158,229,288,357,444,520,595]⟩]⟩
def row8_594 : State := ⟨[66,158,162,229,287,361,444,519,594],[⟨0,378,[10,66,162,229,287,361,444,519]⟩,⟨0,132,[12,66,158,229,287,361,444,519]⟩]⟩
def row8_595 : State := ⟨[0,35,66,158,229,288,357,519,594],[⟨3,131,[36,66,158,229,288,357,519,594]⟩,⟨3,378,[35,66,158,229,288,358,519,594]⟩,⟨0,379,[0,66,158,229,288,370,519,594]⟩,⟨5,380,[35,66,158,229,288,357,520,594]⟩,⟨3,380,[35,66,158,229,288,357,519,595]⟩]⟩
def row8_596 : State := ⟨[66,158,162,229,287,357,444,521,594],[⟨0,380,[10,66,162,229,287,357,444,521]⟩,⟨0,134,[12,66,158,229,287,357,444,521]⟩]⟩
def row8_597 : State := ⟨[0,67,158,229,287,357,444,519,594],[⟨6,324,[67,159,229,287,357,444,519,594]⟩,⟨7,302,[67,158,230,287,357,444,519,594]⟩,⟨6,355,[67,158,229,288,357,444,519,594]⟩,⟨0,381,[67,158,229,287,358,444,519,594]⟩,⟨8,382,[67,158,229,287,357,444,520,594]⟩,⟨6,383,[67,158,229,287,357,444,519,595]⟩]⟩
def row8_598 : State := ⟨[66,158,229,287,358,426,444,519,594],[]⟩
def row8_599 : State := ⟨[0,74,158,229,287,357,444,519,594],[⟨11,314,[74,159,229,287,357,444,519,594]⟩,⟨9,314,[74,158,230,287,357,444,519,594]⟩,⟨9,365,[74,158,229,288,357,444,519,594]⟩,⟨3,384,[74,158,229,287,358,444,519,594]⟩,⟨8,385,[74,158,229,287,357,444,520,594]⟩,⟨6,385,[74,158,229,287,357,444,519,595]⟩]⟩
def row8_600 : State := ⟨[66,158,229,287,358,444,519,575,594],[⟨6,386,[66,158,229,287,351,358,519,594]⟩]⟩
def row8_601 : State := ⟨[0,66,158,229,287,358,444,519,594],[⟨4,292,[66,159,229,287,358,444,519,594]⟩,⟨1,292,[66,158,230,287,358,444,519,594]⟩,⟨0,348,[66,158,229,288,358,444,519,594]⟩,⟨2,282,[66,158,229,287,358,444,520,594]⟩,⟨0,282,[66,158,229,287,358,444,519,595]⟩]⟩
def row8_602 : State := ⟨[66,158,229,287,358,444,468,519,594],[]⟩
def row8_603 : State := ⟨[66,118,158,229,287,358,444,519,594],[]⟩
def row8_604 : State := ⟨[66,158,229,287,358,444,480,519,594],[]⟩
def row8_605 : State := ⟨[10,66,158,229,287,361,444,519,594],[⟨10,387,[68,158,229,287,361,444,519,594]⟩,⟨1,388,[66,158,239,287,361,444,519,594]⟩,⟨0,388,[66,158,229,297,361,444,519,594]⟩,⟨0,51,[66,158,229,287,366,444,519,594]⟩,⟨5,389,[66,158,229,287,361,450,519,594]⟩,⟨4,389,[66,158,229,287,361,444,526,594]⟩]⟩
def row8_606 : State := ⟨[66,158,229,287,358,444,519,594,691],[]⟩
def row8_607 : State := ⟨[0,66,158,229,287,359,444,519,594],[⟨4,296,[66,159,229,287,359,444,519,594]⟩,⟨1,287,[66,158,230,287,359,444,519,594]⟩,⟨0,351,[66,158,229,288,359,444,519,594]⟩,⟨0,40,[66,158,229,287,360,444,519,594]⟩,⟨1,390,[66,158,229,287,359,444,520,594]⟩,⟨1,391,[66,158,229,287,359,444,519,595]⟩]⟩
def row8_608 : State := ⟨[66,158,229,287,358,444,519,553,594],[]⟩
def row8_609 : State := ⟨[66,118,158,229,287,359,444,519,594],[]⟩
def row8_610 : State := ⟨[66,158,229,287,358,444,519,563,594],[]⟩
def row8_611 : State := ⟨[10,66,158,229,287,358,444,519,594],[⟨8,392,[68,158,229,287,358,444,519,594]⟩,⟨1,393,[66,158,239,287,358,444,519,594]⟩,⟨0,394,[66,158,229,297,358,444,519,594]⟩,⟨0,395,[66,158,229,287,365,444,519,594]⟩,⟨0,396,[66,158,229,287,358,450,519,594]⟩,⟨2,397,[66,158,229,287,358,444,526,594]⟩]⟩
def row8_612 : State := ⟨[66,158,229,287,358,444,519,594,674],[]⟩
def row8_613 : State := ⟨[66,118,158,229,287,361,444,519,594],[]⟩
def row8_614 : State := ⟨[66,158,229,287,358,444,519,580,594],[]⟩
def row8_615 : State := ⟨[66,158,229,287,358,444,519,550,594],[⟨7,100,[29,66,158,287,358,444,519,594]⟩]⟩
def row8_616 : State := ⟨[66,158,229,287,358,425,444,519,594],[⟨0,0,[66,158,229,287,357,444,519,594]⟩]⟩
def row8_617 : State := ⟨[66,158,229,287,358,444,519,574,594],[⟨0,0,[66,158,229,287,357,444,519,594]⟩]⟩
def row8_618 : State := ⟨[0,35,66,158,229,287,358,519,594],[⟨3,132,[36,66,158,229,287,358,519,594]⟩,⟨5,341,[35,66,159,229,287,358,519,594]⟩,⟨3,341,[35,66,158,230,287,358,519,594]⟩,⟨3,378,[35,66,158,229,288,358,519,594]⟩,⟨0,133,[0,66,158,229,287,371,519,594]⟩,⟨5,398,[35,66,158,229,287,358,520,594]⟩,⟨3,398,[35,66,158,229,287,358,519,595]⟩]⟩
def row8_619 : State := ⟨[66,158,229,287,358,444,519,595],[⟨3,398,[35,66,158,229,287,358,519,595]⟩,⟨0,75,[66,158,229,287,358,465,519,595]⟩]⟩
def row8_620 : State := ⟨[66,158,229,287,358,444,519,520,594],[]⟩
def row8_621 : State := ⟨[0,66,158,229,287,358,444,519,595],[⟨4,342,[66,159,229,287,358,444,519,595]⟩,⟨1,343,[66,158,230,287,358,444,519,595]⟩,⟨0,374,[66,158,229,288,358,444,519,595]⟩,⟨0,399,[66,158,229,287,358,444,520,595]⟩]⟩
def row8_622 : State := ⟨[66,67,158,229,294,357,444,519,594],[⟨6,75,[67,177,229,294,357,444,519,594]⟩,⟨10,13,[66,177,229,294,357,444,519,594]⟩]⟩
def row8_623 : State := ⟨[8,66,158,229,287,357,444,519,594],[⟨6,2,[67,158,229,287,357,444,519,594]⟩,⟨10,4,[66,159,229,287,357,444,519,594]⟩,⟨7,304,[66,158,237,287,357,444,519,594]⟩,⟨6,357,[66,158,229,295,357,444,519,594]⟩,⟨0,2,[66,158,229,287,358,444,519,594]⟩,⟨3,4,[66,158,229,287,357,448,519,594]⟩,⟨2,304,[66,158,229,287,357,444,524,594]⟩,⟨0,357,[66,158,229,287,357,444,519,599]⟩]⟩
def row8_624 : State := ⟨[0,66,158,236,287,357,444,519,594],[⟨11,325,[66,159,236,287,357,444,519,594]⟩,⟨7,304,[66,158,237,287,357,444,519,594]⟩,⟨6,356,[66,158,236,288,357,444,519,594]⟩,⟨1,382,[66,158,236,287,358,444,519,594]⟩,⟨1,400,[66,158,236,287,357,444,520,594]⟩,⟨1,401,[66,158,236,287,357,444,519,595]⟩]⟩
def row8_625 : State := ⟨[0,66,158,229,294,357,444,519,594],[⟨10,326,[66,159,229,294,357,444,519,594]⟩,⟨7,303,[66,158,230,294,357,444,519,594]⟩,⟨6,357,[66,158,229,295,357,444,519,594]⟩,⟨0,383,[66,158,229,294,358,444,519,594]⟩,⟨8,401,[66,158,229,294,357,444,520,594]⟩,⟨0,402,[66,158,229,294,357,444,519,595]⟩]⟩
def row8_626 : State := ⟨[66,158,229,287,357,425,444,520,594],[]⟩
def row8_627 : State := ⟨[66,158,229,287,357,425,444,519,595],[]⟩
def row8_628 : State := ⟨[9,66,158,229,287,357,444,519,594],[⟨6,2,[67,158,229,287,357,444,519,594]⟩,⟨10,5,[66,162,229,287,357,444,519,594]⟩,⟨9,316,[66,158,238,287,357,444,519,594]⟩,⟨8,316,[66,158,229,296,357,444,519,594]⟩,⟨4,2,[66,158,229,287,361,444,519,594]⟩,⟨3,316,[66,158,229,287,357,449,519,594]⟩,⟨2,316,[66,158,229,287,357,444,525,594]⟩,⟨0,5,[66,158,229,287,357,444,519,598]⟩,⟨0,403,[9,10,66,229,287,357,444,519]⟩]⟩
def row8_629 : State := ⟨[0,66,158,244,287,357,444,519,594],[⟨11,315,[66,159,244,287,357,444,519,594]⟩,⟨7,316,[66,158,245,287,357,444,519,594]⟩,⟨6,366,[66,158,244,288,357,444,519,594]⟩,⟨3,385,[66,158,244,287,358,444,519,594]⟩,⟨0,404,[0,35,66,158,244,357,519,594]⟩,⟨3,405,[66,158,244,287,357,444,520,594]⟩,⟨3,406,[66,158,244,287,357,444,519,595]⟩]⟩
def row8_630 : State := ⟨[0,32,35,66,158,229,357,519,594],[⟨3,403,[33,35,66,158,229,357,519,594]⟩,⟨9,93,[32,36,66,158,229,357,519,594]⟩,⟨0,93,[0,37,66,158,229,357,519,594]⟩,⟨2,404,[0,35,66,169,229,357,519,594]⟩,⟨0,404,[0,35,66,158,244,357,519,594]⟩,⟨11,404,[32,35,66,158,229,357,520,594]⟩,⟨9,404,[32,35,66,158,229,357,519,595]⟩]⟩
def row8_631 : State := ⟨[66,158,229,287,357,425,444,521,594],[⟨0,76,[66,158,229,287,425,444,521,625]⟩,⟨10,407,[66,158,229,287,346,357,444,521]⟩]⟩
def row8_632 : State := ⟨[0,66,158,229,287,350,357,519,594],[⟨6,1,[66,158,229,287,351,357,519,594]⟩,⟨0,77,[0,66,158,229,287,370,519,594]⟩,⟨8,407,[66,158,229,287,350,357,520,594]⟩,⟨6,407,[66,158,229,287,350,357,519,595]⟩]⟩
def row8_633 : State := ⟨[66,158,229,287,357,444,468,519,595],[]⟩
def row8_634 : State := ⟨[66,118,158,229,287,357,444,520,594],[]⟩
def row8_635 : State := ⟨[66,118,158,229,287,357,444,519,595],[]⟩
def row8_636 : State := ⟨[66,158,229,287,357,444,480,520,594],[]⟩
def row8_637 : State := ⟨[66,158,229,287,357,444,480,519,595],[]⟩
def row8_638 : State := ⟨[0,35,76,158,229,287,357,519,594],[⟨3,137,[36,76,158,229,287,357,519,594]⟩,⟨0,408,[0,76,158,229,287,370,519,594]⟩,⟨8,409,[35,76,158,229,287,357,520,594]⟩,⟨2,410,[0,76,158,229,287,357,538,594]⟩,⟨6,409,[35,76,158,229,287,357,519,595]⟩,⟨0,410,[0,76,158,229,287,357,519,615]⟩]⟩
def row8_639 : State := ⟨[0,35,66,158,246,287,357,519,594],[⟨3,139,[36,66,158,246,287,357,519,594]⟩,⟨0,411,[0,66,158,246,287,370,519,594]⟩,⟨3,412,[35,66,158,246,287,357,520,594]⟩,⟨0,413,[0,66,158,246,287,357,538,594]⟩,⟨3,414,[35,66,158,246,287,357,519,595]⟩]⟩
def row8_640 : State := ⟨[0,66,158,229,287,370,519,594],[⟨2,344,[0,66,159,229,287,370,519,594]⟩,⟨0,344,[0,66,158,230,287,370,519,594]⟩,⟨0,379,[0,66,158,229,288,370,519,594]⟩,⟨0,246,[0,66,158,229,322,370,519,594]⟩,⟨2,246,[0,66,158,229,332,370,519,594]⟩,⟨0,133,[0,66,158,229,287,371,519,594]⟩,⟨0,81,[0,37,66,158,229,370,519,594]⟩,⟨5,415,[66,158,229,287,370,520,594]⟩,⟨3,416,[66,158,229,287,370,519,520,594]⟩,⟨2,417,[0,66,158,229,287,370,520,594]⟩,⟨3,415,[66,158,229,287,370,519,595]⟩,⟨5,416,[66,158,229,287,370,519,594,595]⟩,⟨0,417,[0,66,158,229,287,370,519,595]⟩]⟩
def row8_641 : State := ⟨[0,66,158,229,287,357,370,519,594],[⟨0,93,[0,37,66,158,229,357,519,594]⟩,⟨8,418,[66,158,229,287,357,370,520,594]⟩,⟨6,418,[66,158,229,287,357,370,519,595]⟩]⟩
def row8_642 : State := ⟨[0,35,66,158,229,287,370,519,594],[⟨3,140,[36,66,158,229,287,370,519,594]⟩,⟨0,408,[0,76,158,229,287,370,519,594]⟩,⟨2,411,[0,66,171,229,287,370,519,594]⟩,⟨0,411,[0,66,158,246,287,370,519,594]⟩,⟨5,419,[35,66,158,229,287,370,520,594]⟩,⟨2,420,[0,66,158,229,287,370,538,594]⟩,⟨3,419,[35,66,158,229,287,370,519,595]⟩,⟨0,420,[0,66,158,229,287,370,519,615]⟩]⟩
def row8_643 : State := ⟨[10,66,158,229,287,357,444,521],[⟨10,409,[10,68,158,229,287,357,444,521]⟩,⟨1,412,[10,66,158,239,287,357,444,521]⟩,⟨0,248,[10,66,229,270,287,357,444,521]⟩,⟨0,414,[10,66,158,229,297,357,444,521]⟩,⟨1,247,[10,66,229,287,322,357,444,521]⟩,⟨0,415,[66,158,229,287,364,444,521]⟩,⟨10,418,[66,158,229,287,357,364,444,521]⟩,⟨0,419,[10,66,158,229,287,364,444,521]⟩,⟨6,404,[7,10,66,229,287,357,444,521]⟩,⟨1,421,[10,66,158,229,287,357,450,521]⟩,⟨0,142,[10,66,158,229,287,357,444,528]⟩]⟩
def row8_644 : State := ⟨[10,66,158,229,287,357,444,446,519],[⟨0,416,[66,158,229,287,364,444,446,519]⟩]⟩
def row8_645 : State := ⟨[0,35,66,158,229,287,357,519,595],[⟨3,134,[36,66,158,229,287,357,519,595]⟩,⟨5,345,[35,66,159,229,287,357,519,595]⟩,⟨3,346,[35,66,158,230,287,357,519,595]⟩,⟨3,380,[35,66,158,229,288,357,519,595]⟩,⟨3,398,[35,66,158,229,287,358,519,595]⟩,⟨0,417,[0,66,158,229,287,370,519,595]⟩,⟨3,422,[35,66,158,229,287,357,520,595]⟩]⟩
def row8_646 : State := ⟨[0,35,66,158,229,287,357,519,615],[⟨3,141,[36,66,158,229,287,357,519,615]⟩,⟨0,410,[0,76,158,229,287,357,519,615]⟩,⟨2,413,[0,66,171,229,287,357,519,615]⟩,⟨0,420,[0,66,158,229,287,370,519,615]⟩,⟨3,421,[35,66,158,229,287,357,520,615]⟩,⟨3,142,[35,66,158,229,287,357,519,616]⟩]⟩
def row8_647 : State := ⟨[0,76,158,229,287,357,444,519,594],[⟨8,320,[76,159,229,287,357,444,519,594]⟩,⟨6,320,[76,158,230,287,357,444,519,594]⟩,⟨6,177,[76,158,229,288,357,444,519,594]⟩,⟨6,387,[76,158,229,287,358,444,519,594]⟩,⟨8,423,[76,158,229,287,357,444,520,594]⟩,⟨6,423,[76,158,229,287,357,444,519,595]⟩]⟩
def row8_648 : State := ⟨[0,66,158,246,287,357,444,519,594],[⟨9,321,[66,159,246,287,357,444,519,594]⟩,⟨7,42,[66,158,247,287,357,444,519,594]⟩,⟨6,372,[66,158,246,288,357,444,519,594]⟩,⟨3,388,[66,158,246,287,358,444,519,594]⟩,⟨8,424,[66,158,246,287,357,444,520,594]⟩,⟨6,425,[66,158,246,287,357,444,519,595]⟩]⟩
def row8_649 : State := ⟨[0,66,158,229,287,370,444,519,594],[⟨4,317,[66,159,229,287,370,444,519,594]⟩,⟨1,317,[66,158,230,287,370,444,519,594]⟩,⟨0,370,[66,158,229,288,370,444,519,594]⟩,⟨3,51,[66,158,229,287,371,444,519,594]⟩,⟨5,426,[66,158,229,287,370,444,520,594]⟩,⟨3,426,[66,158,229,287,370,444,519,595]⟩]⟩
def row8_650 : State := ⟨[10,66,158,229,287,357,444,521,594],[⟨10,423,[68,158,229,287,357,444,521,594]⟩,⟨10,424,[66,158,239,287,357,444,521,594]⟩,⟨10,425,[66,158,229,297,357,444,521,594]⟩,⟨0,426,[66,158,229,287,364,444,521,594]⟩,⟨5,427,[66,158,229,287,357,450,521,594]⟩,⟨2,97,[66,158,229,287,357,444,528,594]⟩]⟩
def row8_651 : State := ⟨[0,66,158,229,287,357,444,519,615],[⟨4,318,[66,159,229,287,357,444,519,615]⟩,⟨1,319,[66,158,230,287,357,444,519,615]⟩,⟨0,371,[66,158,229,288,357,444,519,615]⟩,⟨0,389,[66,158,229,287,358,444,519,615]⟩,⟨0,427,[66,158,229,287,357,444,520,615]⟩,⟨1,97,[66,158,229,287,357,444,519,616]⟩]⟩
def row8_652 : State := ⟨[66,158,229,287,357,444,519,595,691],[]⟩
def row8_653 : State := ⟨[0,66,158,229,287,357,444,519,595],[⟨4,293,[66,159,229,287,357,444,519,595]⟩,⟨1,294,[66,158,230,287,357,444,519,595]⟩,⟨0,349,[66,158,229,288,357,444,519,595]⟩,⟨0,282,[66,158,229,287,358,444,519,595]⟩,⟨0,283,[66,158,229,287,357,444,520,595]⟩]⟩
def row8_654 : State := ⟨[0,66,158,229,287,357,444,519,596],[⟨4,297,[66,159,229,287,357,444,519,596]⟩,⟨1,289,[66,158,230,287,357,444,519,596]⟩,⟨0,353,[66,158,229,288,357,444,519,596]⟩,⟨0,391,[66,158,229,287,358,444,519,596]⟩,⟨0,428,[66,158,229,287,357,444,520,596]⟩,⟨0,213,[66,158,229,287,357,444,519,597]⟩]⟩
def row8_655 : State := ⟨[66,158,229,287,357,444,468,519,596],[]⟩
def row8_656 : State := ⟨[66,118,158,229,287,357,444,519,596],[]⟩
def row8_657 : State := ⟨[66,158,229,287,357,444,480,519,596],[]⟩
def row8_658 : State := ⟨[10,66,158,229,287,357,444,520,594],[⟨8,429,[68,158,229,287,357,444,520,594]⟩,⟨8,430,[66,158,239,287,357,444,520,594]⟩,⟨8,431,[66,158,229,297,357,444,520,594]⟩,⟨0,432,[66,158,229,287,364,444,520,594]⟩,⟨5,433,[66,158,229,287,357,450,520,594]⟩,⟨2,434,[66,158,229,287,357,444,527,594]⟩]⟩
def row8_659 : State := ⟨[66,158,229,287,357,444,519,595,681],[]⟩
def row8_660 : State := ⟨[66,118,158,229,287,357,444,521,594],[]⟩
def row8_661 : State := ⟨[66,158,229,287,357,444,480,521,594],[⟨10,435,[66,158,229,287,357,437,444,521]⟩]⟩
def row8_662 : State := ⟨[10,66,158,229,287,357,444,519,595],[⟨6,436,[68,158,229,287,357,444,519,595]⟩,⟨6,437,[66,158,239,287,357,444,519,595]⟩,⟨6,438,[66,158,229,297,357,444,519,595]⟩,⟨0,439,[66,158,229,287,364,444,519,595]⟩,⟨3,440,[66,158,229,287,357,450,519,595]⟩,⟨2,441,[66,158,229,287,357,444,526,595]⟩]⟩
def row8_663 : State := ⟨[66,158,229,287,357,444,519,595,675],[]⟩
def row8_664 : State := ⟨[66,118,158,229,287,357,445,519,594],[]⟩
def row8_665 : State := ⟨[66,158,229,287,357,444,519,595,638],[]⟩
def row8_666 : State := ⟨[66,118,158,229,287,357,446,519,594],[]⟩
def row8_667 : State := ⟨[66,158,229,287,357,444,519,595,645],[⟨8,442,[66,158,229,287,357,440,519,595]⟩]⟩
def row8_668 : State := ⟨[66,158,229,287,357,444,519,595,626],[⟨10,101,[15,66,229,287,357,444,519,595]⟩]⟩
def row8_669 : State := ⟨[66,88,158,236,287,357,444,519,594],[]⟩
def row8_670 : State := ⟨[66,158,229,287,357,444,519,595,666],[⟨0,443,[6,158,229,287,357,444,519,595]⟩]⟩
def row8_671 : State := ⟨[0,66,158,229,287,357,445,519,594],[⟨4,298,[66,159,229,287,357,445,519,594]⟩,⟨1,288,[66,158,230,287,357,445,519,594]⟩,⟨0,352,[66,158,229,288,357,445,519,594]⟩,⟨0,390,[66,158,229,287,358,445,519,594]⟩,⟨4,240,[66,158,229,287,357,445,520,594]⟩,⟨1,428,[66,158,229,287,357,445,519,595]⟩]⟩
def row8_672 : State := ⟨[2,66,158,229,287,357,444,519,594],[⟨10,113,[66,161,229,287,357,444,519,594]⟩,⟨7,112,[66,158,232,287,357,444,519,594]⟩,⟨6,112,[66,158,229,290,357,444,519,594]⟩,⟨0,40,[66,158,229,287,360,444,519,594]⟩,⟨3,3,[66,158,229,287,357,445,519,594]⟩,⟨2,3,[66,158,229,287,357,444,520,594]⟩,⟨0,213,[66,158,229,287,357,444,519,597]⟩]⟩
def row8_673 : State := ⟨[66,158,229,287,357,444,519,595,637],[⟨0,0,[66,158,229,287,357,444,519,594]⟩]⟩
def row8_674 : State := ⟨[66,158,229,287,357,444,519,595,644],[⟨8,444,[66,158,229,287,357,439,519,595]⟩,⟨0,0,[66,158,229,287,357,444,519,594]⟩]⟩
def row8_675 : State := ⟨[66,158,229,287,357,444,519,595,674],[⟨0,0,[66,158,229,287,357,444,519,594]⟩]⟩
def row8_676 : State := ⟨[66,158,229,287,357,444,520,595],[⟨3,422,[35,66,158,229,287,357,520,595]⟩,⟨1,88,[66,158,229,287,357,465,520,595]⟩]⟩
def row8_677 : State := ⟨[66,158,165,229,302,357,444,519,594],[]⟩
def row8_678 : State := ⟨[0,66,158,229,287,357,444,520,595],[⟨4,347,[66,159,229,287,357,444,520,595]⟩,⟨1,347,[66,158,230,287,357,444,520,595]⟩,⟨0,377,[66,158,229,288,357,444,520,595]⟩,⟨0,399,[66,158,229,287,358,444,520,595]⟩]⟩
def row8_679 : State := ⟨[66,120,158,229,287,357,444,519,594],[⟨11,4,[66,160,229,287,357,444,519,594]⟩,⟨3,3,[66,158,229,287,357,445,519,594]⟩]⟩
def row8_680 : State := ⟨[11,66,158,229,287,357,444,519,594],[⟨10,6,[68,158,229,287,357,444,519,594]⟩,⟨10,4,[66,159,229,287,357,444,519,594]⟩,⟨9,310,[66,158,240,287,357,444,519,594]⟩,⟨8,363,[66,158,229,298,357,444,519,594]⟩,⟨0,395,[66,158,229,287,365,444,519,594]⟩,⟨3,7,[66,158,229,287,357,450,519,594]⟩,⟨2,434,[66,158,229,287,357,444,527,594]⟩,⟨0,3,[66,158,229,287,357,444,519,595]⟩]⟩
def row8_681 : State := ⟨[0,68,158,229,287,357,444,519,594],[⟨10,330,[68,159,229,287,357,444,519,594]⟩,⟨11,308,[68,158,230,287,357,444,519,594]⟩,⟨10,361,[68,158,229,288,357,444,519,594]⟩,⟨8,392,[68,158,229,287,358,444,519,594]⟩,⟨8,429,[68,158,229,287,357,444,520,594]⟩,⟨6,436,[68,158,229,287,357,444,519,595]⟩]⟩
def row8_682 : State := ⟨[0,66,158,239,287,357,444,519,594],[⟨11,331,[66,159,239,287,357,444,519,594]⟩,⟨9,310,[66,158,240,287,357,444,519,594]⟩,⟨7,362,[66,158,239,288,357,444,519,594]⟩,⟨1,393,[66,158,239,287,358,444,519,594]⟩,⟨8,430,[66,158,239,287,357,444,520,594]⟩,⟨6,437,[66,158,239,287,357,444,519,595]⟩]⟩
def row8_683 : State := ⟨[0,66,158,229,297,357,444,519,594],[⟨8,332,[66,159,229,297,357,444,519,594]⟩,⟨6,309,[66,158,230,297,357,444,519,594]⟩,⟨8,363,[66,158,229,298,357,444,519,594]⟩,⟨0,394,[66,158,229,297,358,444,519,594]⟩,⟨8,431,[66,158,229,297,357,444,520,594]⟩,⟨6,438,[66,158,229,297,357,444,519,595]⟩]⟩
def row8_684 : State := ⟨[0,66,158,229,287,364,444,519,594],[⟨4,327,[66,159,229,287,364,444,519,594]⟩,⟨1,305,[66,158,230,287,364,444,519,594]⟩,⟨0,358,[66,158,229,288,364,444,519,594]⟩,⟨0,395,[66,158,229,287,365,444,519,594]⟩,⟨0,432,[66,158,229,287,364,444,520,594]⟩,⟨0,439,[66,158,229,287,364,444,519,595]⟩]⟩
def row8_685 : State := ⟨[0,66,158,229,287,357,450,519,594],[⟨4,328,[66,159,229,287,357,450,519,594]⟩,⟨1,307,[66,158,230,287,357,450,519,594]⟩,⟨0,359,[66,158,229,288,357,450,519,594]⟩,⟨0,396,[66,158,229,287,358,450,519,594]⟩,⟨5,433,[66,158,229,287,357,450,520,594]⟩,⟨3,440,[66,158,229,287,357,450,519,595]⟩]⟩
def row8_686 : State := ⟨[0,66,158,229,287,357,444,519,604],[⟨4,306,[66,159,229,287,357,444,519,604]⟩,⟨1,329,[66,158,230,287,357,444,519,604]⟩,⟨0,360,[66,158,229,288,357,444,519,604]⟩,⟨0,397,[66,158,229,287,358,444,519,604]⟩,⟨0,441,[66,158,229,287,357,444,520,604]⟩,⟨0,434,[66,158,229,287,357,444,519,605]⟩]⟩
def row8_687 : State := ⟨[66,121,158,229,287,357,444,519,594],[⟨10,5,[66,162,229,287,357,444,519,594]⟩,⟨5,3,[66,158,229,287,357,446,519,594]⟩]⟩
def row8_688 : State := ⟨[0,66,158,229,287,357,393,519,594],[⟨6,94,[66,158,229,287,357,394,519,594]⟩,⟨6,444,[66,158,229,287,357,393,520,594]⟩,⟨6,435,[66,158,229,287,357,393,519,595]⟩]⟩
def row8_689 : State := ⟨[66,158,229,287,357,422,444,519,594],[]⟩
def row8_690 : State := ⟨[49,66,229,287,357,444,519,594,629],[]⟩
def row8_691 : State := ⟨[66,100,158,229,287,357,444,519,594],[]⟩
def row8_692 : State := ⟨[66,158,197,229,287,357,444,519,594],[]⟩
def row8_693 : State := ⟨[66,158,229,287,357,444,476,519,594],[]⟩
def row8_694 : State := ⟨[66,158,229,287,357,444,477,519,594],[⟨10,94,[66,158,229,287,357,438,444,519]⟩]⟩
def row8_695 : State := ⟨[10,66,88,229,287,357,444,519,594],[⟨10,445,[68,88,229,287,357,444,519,594]⟩,⟨0,94,[66,91,229,287,357,444,519,594]⟩,⟨11,226,[10,66,236,287,357,444,519,594]⟩]⟩
def row8_696 : State := ⟨[66,158,229,287,357,406,444,519,594],[]⟩
def row8_697 : State := ⟨[66,158,229,287,357,444,519,629,634],[⟨0,0,[66,158,229,287,357,444,519,594]⟩]⟩
def row8_698 : State := ⟨[66,158,229,287,357,400,444,519,594],[]⟩
def row8_699 : State := ⟨[66,158,229,287,364,444,494,519,594],[⟨3,223,[66,270,287,364,444,494,519,594]⟩,⟨0,0,[66,158,229,287,357,444,519,594]⟩]⟩
def row8_700 : State := ⟨[66,158,229,287,357,425,444,538,594],[]⟩
def row8_701 : State := ⟨[66,158,229,287,357,425,444,519,604],[⟨7,224,[66,270,287,357,425,444,519,604]⟩]⟩
def row8_702 : State := ⟨[66,158,229,287,364,444,468,519,594],[⟨1,225,[66,158,229,287,364,468,519,656]⟩,⟨0,445,[66,158,229,287,364,436,444,519]⟩]⟩
def row8_703 : State := ⟨[66,158,229,287,357,444,519,604,629],[⟨0,0,[66,158,229,287,357,444,519,594]⟩]⟩
def row8_704 : State := ⟨[66,158,229,287,357,429,444,519,594],[⟨2,94,[66,94,158,287,357,444,519,594]⟩]⟩
def row8_705 : State := ⟨[66,158,229,287,357,444,468,519,604],[]⟩
def row8_706 : State := ⟨[66,158,229,287,357,418,444,519,594],[]⟩
def row8_707 : State := ⟨[66,158,229,287,357,407,444,519,594],[]⟩
def row8_708 : State := ⟨[66,158,229,287,357,444,501,519,594],[]⟩
def row8_709 : State := ⟨[66,91,229,287,357,444,494,519,594],[]⟩
def row8_710 : State := ⟨[66,158,229,287,357,376,444,519,594],[]⟩
def row8_711 : State := ⟨[66,158,229,287,364,444,519,594,629],[]⟩
def row8_712 : State := ⟨[66,158,229,287,357,444,468,519,615],[]⟩
def row8_713 : State := ⟨[66,158,229,287,357,425,444,526,594],[]⟩
def row8_714 : State := ⟨[66,158,229,287,357,444,519,629,654],[⟨0,0,[66,158,229,287,357,444,519,594]⟩]⟩
def row8_715 : State := ⟨[66,158,229,287,403,444,519,574,594],[⟨0,0,[66,158,229,287,357,444,519,594]⟩]⟩
def row8_716 : State := ⟨[66,158,229,287,357,444,506,519,594],[]⟩
def row8_717 : State := ⟨[66,158,229,287,357,385,444,519,594],[]⟩
def row8_718 : State := ⟨[48,68,158,229,287,357,444,519,594],[⟨11,446,[68,158,239,287,357,444,519,594]⟩,⟨10,446,[68,158,229,297,357,444,519,594]⟩]⟩
def row8_719 : State := ⟨[48,66,158,229,297,357,444,519,594],[⟨10,446,[68,158,229,297,357,444,519,594]⟩,⟨6,447,[66,158,239,297,357,444,519,594]⟩]⟩
def row8_720 : State := ⟨[66,158,229,287,357,377,444,519,594],[⟨10,1,[66,158,229,287,347,357,444,519]⟩]⟩
def row8_721 : State := ⟨[66,158,229,287,357,420,444,519,594],[]⟩
def row8_722 : State := ⟨[66,80,158,229,287,357,444,519,594],[⟨7,3,[66,158,236,287,357,444,519,594]⟩,⟨3,4,[66,158,229,287,357,448,519,594]⟩]⟩
def row8_723 : State := ⟨[66,148,158,229,287,357,444,519,594],[]⟩
def row8_724 : State := ⟨[66,158,229,287,357,444,519,634,644],[⟨0,0,[66,158,229,287,357,444,519,594]⟩]⟩
def row8_725 : State := ⟨[10,66,158,229,287,357,444,519,634],[⟨6,448,[68,158,229,287,357,444,519,634]⟩,⟨0,449,[66,158,229,297,357,444,519,634]⟩,⟨0,450,[66,158,229,287,364,444,519,634]⟩,⟨0,451,[66,158,229,287,357,444,526,634]⟩]⟩
def row8_726 : State := ⟨[66,81,158,229,287,357,444,519,594],[⟨9,7,[66,158,239,287,357,444,519,594]⟩,⟨3,7,[66,158,229,287,357,450,519,594]⟩]⟩
def row8_727 : State := ⟨[66,158,229,287,357,444,519,637,664],[⟨0,0,[66,158,229,287,357,444,519,594]⟩]⟩
def row8_728 : State := ⟨[66,158,229,287,357,444,519,594,678],[]⟩
def row8_729 : State := ⟨[10,66,158,229,287,357,444,519,654],[⟨6,452,[68,158,229,287,357,444,519,654]⟩,⟨0,453,[66,158,229,297,357,444,519,654]⟩,⟨0,454,[66,158,229,287,364,444,519,654]⟩]⟩
def row8_730 : State := ⟨[66,123,158,229,287,357,444,519,594],[⟨3,7,[66,158,229,287,357,450,519,594]⟩]⟩
def row8_731 : State := ⟨[66,118,158,229,287,370,444,519,594],[⟨0,452,[66,158,229,319,370,444,519,594]⟩]⟩
def row8_732 : State := ⟨[66,118,158,229,287,357,444,538,594],[]⟩
def row8_733 : State := ⟨[66,118,158,229,287,357,444,519,615],[⟨6,453,[66,158,229,319,357,444,519,615]⟩]⟩
def row8_734 : State := ⟨[66,118,158,229,287,364,444,519,594],[⟨0,454,[66,158,229,287,364,444,519,654]⟩]⟩
def row8_735 : State := ⟨[66,118,158,229,287,357,450,519,594],[]⟩
def row8_736 : State := ⟨[66,118,158,229,287,357,444,526,594],[]⟩
def row8_737 : State := ⟨[66,118,158,229,287,367,444,519,594],[⟨1,448,[66,158,258,287,367,444,519,594]⟩,⟨2,450,[66,158,229,287,367,444,557,594]⟩]⟩
def row8_738 : State := ⟨[66,126,158,229,287,357,444,519,594],[⟨11,7,[66,166,229,287,357,444,519,594]⟩,⟨5,7,[66,158,229,287,357,456,519,594]⟩]⟩
def row8_739 : State := ⟨[66,118,158,229,287,357,456,519,594],[]⟩
def row8_740 : State := ⟨[66,118,158,229,287,357,444,519,604],[⟨7,449,[66,158,258,287,357,444,519,604]⟩,⟨2,451,[66,158,229,287,357,444,557,604]⟩]⟩
def row8_741 : State := ⟨[66,158,212,229,287,357,444,519,594],[]⟩
def row8_742 : State := ⟨[66,158,229,262,287,357,444,519,594],[]⟩
def row8_743 : State := ⟨[66,158,229,287,364,444,519,594,637],[⟨3,253,[66,270,287,364,444,519,594,637]⟩]⟩
def row8_744 : State := ⟨[66,158,229,287,357,444,480,538,594],[]⟩
def row8_745 : State := ⟨[66,158,229,287,357,444,480,519,615],[⟨6,254,[66,229,322,357,444,480,519,615]⟩]⟩
def row8_746 : State := ⟨[66,158,229,287,364,444,480,519,594],[⟨1,255,[66,158,229,287,364,480,519,656]⟩]⟩
def row8_747 : State := ⟨[66,158,229,287,357,444,480,526,594],[]⟩
def row8_748 : State := ⟨[66,158,229,287,357,375,444,519,594],[]⟩
def row8_749 : State := ⟨[66,158,229,287,357,419,444,519,594],[]⟩
def row8_750 : State := ⟨[66,91,229,287,357,444,519,594,637],[]⟩
def row8_751 : State := ⟨[66,101,158,229,287,357,444,519,594],[⟨0,29,[12,66,158,229,287,357,444,519]⟩]⟩
def row8_752 : State := ⟨[66,89,158,239,287,357,444,519,594],[]⟩
def row8_753 : State := ⟨[66,158,198,229,287,357,444,519,594],[]⟩
def row8_754 : State := ⟨[66,158,229,287,357,389,444,519,594],[⟨0,94,[66,91,229,287,357,444,519,594]⟩]⟩
def row8_755 : State := ⟨[66,158,229,287,357,444,479,519,594],[]⟩
def row8_756 : State := ⟨[66,158,229,287,364,444,498,519,594],[]⟩
def row8_757 : State := ⟨[66,158,229,287,357,444,519,604,644],[⟨0,0,[66,158,229,287,357,444,519,594]⟩]⟩
def row8_758 : State := ⟨[66,158,229,287,357,444,480,519,604],[]⟩
def row8_759 : State := ⟨[66,158,229,287,357,444,484,519,594],[]⟩
def row8_760 : State := ⟨[66,158,229,287,357,444,474,519,594],[]⟩
def row8_761 : State := ⟨[66,158,229,287,357,402,444,519,594],[]⟩
def row8_762 : State := ⟨[66,158,229,287,357,432,444,519,594],[⟨10,252,[66,158,332,357,432,444,519,594]⟩,⟨0,252,[66,158,229,287,357,432,588,594]⟩]⟩
def row8_763 : State := ⟨[66,158,229,287,364,382,444,519,594],[⟨0,455,[49,66,229,287,364,444,519,594]⟩,⟨10,456,[66,158,229,287,347,364,444,519]⟩]⟩
def row8_764 : State := ⟨[66,158,229,287,364,444,497,519,594],[⟨3,256,[66,270,287,364,444,497,519,594]⟩,⟨0,457,[66,91,229,287,364,444,519,594]⟩]⟩
def row8_765 : State := ⟨[10,66,158,229,287,367,444,519,594],[⟨0,458,[68,158,229,287,367,444,519,594]⟩,⟨1,459,[66,158,239,287,367,444,519,594]⟩,⟨1,259,[10,66,270,287,367,444,519,594]⟩,⟨0,460,[66,158,229,297,367,444,519,594]⟩,⟨0,461,[66,158,229,287,369,444,519,594]⟩,⟨4,462,[66,158,229,287,367,450,519,594]⟩,⟨2,463,[66,158,229,287,367,444,526,594]⟩,⟨0,274,[10,66,158,229,287,367,444,665]⟩]⟩
def row8_766 : State := ⟨[66,158,229,287,364,444,519,594,681],[]⟩
def row8_767 : State := ⟨[66,158,229,287,364,444,466,519,594],[⟨0,464,[66,125,229,287,364,444,519,594]⟩,⟨8,120,[37,66,158,229,364,444,519,594]⟩,⟨1,275,[66,158,229,287,364,466,519,656]⟩]⟩
def row8_768 : State := ⟨[10,66,158,229,287,364,444,519,594],[⟨0,465,[68,158,229,287,364,444,519,594]⟩,⟨1,466,[66,158,239,287,364,444,519,594]⟩,⟨0,466,[66,158,229,297,364,444,519,594]⟩,⟨1,446,[66,158,229,287,364,450,519,594]⟩,⟨0,446,[66,158,229,287,364,444,526,594]⟩]⟩
def row8_769 : State := ⟨[66,158,229,287,364,444,519,594,674],[]⟩
def row8_770 : State := ⟨[68,158,229,287,364,444,519,594],[⟨10,261,[68,229,270,287,364,444,519,594]⟩,⟨11,261,[68,229,287,322,364,444,519,594]⟩,⟨10,467,[15,68,229,287,364,444,519,594]⟩,⟨0,467,[12,68,158,229,287,364,444,519]⟩,⟨0,261,[68,158,229,287,364,444,519,656]⟩,⟨1,261,[68,158,229,287,364,444,519,665]⟩]⟩
def row8_771 : State := ⟨[66,68,158,229,287,364,444,519,594],[⟨4,408,[3,68,158,229,287,364,444,519]⟩,⟨0,140,[12,66,158,229,287,364,444,519]⟩]⟩
def row8_772 : State := ⟨[10,68,158,229,287,364,444,519,594],[⟨11,468,[68,158,239,287,364,444,519,594]⟩,⟨10,468,[68,158,229,297,364,444,519,594]⟩,⟨1,468,[68,158,229,287,364,450,519,594]⟩,⟨0,468,[68,158,229,287,364,444,526,594]⟩]⟩
def row8_773 : State := ⟨[66,158,229,297,364,444,519,594],[⟨4,263,[66,229,270,297,364,444,519,594]⟩,⟨4,262,[66,229,297,322,364,444,519,594]⟩,⟨10,469,[15,66,229,297,364,444,519,594]⟩,⟨4,411,[3,66,158,229,297,364,444,519]⟩,⟨0,270,[66,158,229,297,364,444,519,656]⟩,⟨0,267,[66,158,229,297,364,444,519,665]⟩]⟩
def row8_774 : State := ⟨[66,158,166,229,287,367,444,519,594],[⟨3,262,[66,166,270,287,367,444,519,594]⟩,⟨1,135,[66,158,270,287,367,444,519,594]⟩]⟩
def row8_775 : State := ⟨[10,66,158,229,297,364,444,519,594],[⟨10,468,[68,158,229,297,364,444,519,594]⟩,⟨0,470,[66,158,239,297,364,444,519,594]⟩,⟨0,471,[66,158,229,297,364,450,519,594]⟩,⟨0,472,[66,158,229,297,364,444,526,594]⟩]⟩
def row8_776 : State := ⟨[10,12,68,158,229,287,357,444,519],[⟨1,473,[12,68,158,239,287,357,444,519]⟩,⟨0,473,[12,68,158,229,297,357,444,519]⟩,⟨0,467,[12,68,158,229,287,364,444,519]⟩,⟨1,469,[12,68,158,229,287,357,450,519]⟩,⟨11,474,[10,68,158,229,287,357,451,519]⟩,⟨0,469,[12,68,158,229,287,357,444,526]⟩,⟨10,474,[10,68,158,229,287,357,444,528]⟩]⟩
def row8_777 : State := ⟨[66,158,229,287,364,444,526,594],[⟨4,265,[66,229,270,287,364,444,526,594]⟩,⟨5,264,[66,229,287,322,364,444,526,594]⟩,⟨10,473,[15,66,229,287,364,444,526,594]⟩,⟨4,420,[3,66,158,229,287,364,444,526]⟩,⟨0,277,[66,158,229,287,364,444,526,656]⟩,⟨0,276,[66,158,229,287,364,444,526,665]⟩]⟩
def row8_778 : State := ⟨[66,158,229,287,364,444,450,519,594],[⟨1,276,[66,158,229,287,364,450,519,656]⟩,⟨0,11,[66,158,229,287,364,444,519,656]⟩]⟩
def row8_779 : State := ⟨[10,66,158,229,287,364,444,526,594],[⟨0,468,[68,158,229,287,364,444,526,594]⟩,⟨1,471,[66,158,239,287,364,444,526,594]⟩,⟨0,472,[66,158,229,297,364,444,526,594]⟩,⟨0,475,[66,158,229,287,364,450,526,594]⟩]⟩
def row8_780 : State := ⟨[66,68,158,229,297,357,444,519,594],[⟨0,139,[12,66,158,229,297,357,444,519]⟩]⟩
def row8_781 : State := ⟨[66,68,158,229,287,357,444,526,594],[⟨4,410,[3,68,158,229,287,357,444,526]⟩,⟨0,141,[12,66,158,229,287,357,444,526]⟩]⟩
def row8_782 : State := ⟨[10,66,158,229,287,357,444,538,594],[⟨8,460,[68,158,229,287,357,444,538,594]⟩,⟨1,476,[66,158,239,287,357,444,538,594]⟩,⟨8,477,[66,158,229,297,357,444,538,594]⟩,⟨0,462,[66,158,229,287,364,444,538,594]⟩,⟨5,478,[66,158,229,287,357,450,538,594]⟩,⟨2,479,[66,158,229,287,357,444,540,594]⟩]⟩
def row8_783 : State := ⟨[66,158,229,287,357,444,519,604,691],[]⟩
def row8_784 : State := ⟨[10,66,158,229,287,357,444,526,594],[⟨10,466,[68,158,229,287,357,444,526,594]⟩,⟨1,480,[66,158,239,287,357,444,526,594]⟩,⟨0,481,[66,158,229,297,357,444,526,594]⟩,⟨0,446,[66,158,229,287,364,444,526,594]⟩,⟨4,447,[66,158,229,287,357,450,526,594]⟩]⟩
def row8_785 : State := ⟨[66,158,229,287,357,444,519,604,681],[]⟩
def row8_786 : State := ⟨[66,158,229,287,357,444,519,604,632],[⟨9,482,[66,158,229,287,357,444,514,604]⟩]⟩
def row8_787 : State := ⟨[10,66,158,229,287,357,444,519,604],[⟨7,459,[68,158,229,287,357,444,519,604]⟩,⟨1,483,[66,158,239,287,357,444,519,604]⟩,⟨11,269,[10,66,270,287,357,444,519,604]⟩,⟨0,477,[66,158,229,297,357,444,519,604]⟩,⟨0,463,[66,158,229,287,364,444,519,604]⟩,⟨1,478,[66,158,229,287,357,450,519,604]⟩,⟨0,484,[66,158,229,287,357,444,526,604]⟩]⟩
def row8_788 : State := ⟨[66,158,229,287,357,444,519,604,679],[]⟩
def row8_789 : State := ⟨[66,158,229,287,357,444,519,604,648],[]⟩
def row8_790 : State := ⟨[66,158,229,287,357,444,519,604,627],[⟨11,121,[15,66,229,287,357,444,519,604]⟩,⟨4,485,[66,158,226,287,357,444,519,604]⟩]⟩
def row8_791 : State := ⟨[66,158,229,287,357,444,519,604,659],[]⟩
def row8_792 : State := ⟨[66,158,229,287,357,444,519,604,674],[⟨0,0,[66,158,229,287,357,444,519,594]⟩]⟩
def row8_793 : State := ⟨[66,158,229,287,357,444,519,594,679],[]⟩
def row8_794 : State := ⟨[66,158,229,297,357,450,519,594],[⟨11,268,[66,229,270,297,357,450,519,594]⟩,⟨11,271,[66,229,297,322,357,450,519,594]⟩,⟨7,413,[7,66,229,297,357,450,519,594]⟩,⟨4,413,[3,66,158,229,297,357,450,519]⟩,⟨0,271,[66,158,229,297,357,450,519,656]⟩,⟨0,268,[66,158,229,297,357,450,519,665]⟩]⟩
def row8_795 : State := ⟨[66,158,166,229,287,357,444,519,604],[⟨7,271,[66,166,270,287,357,444,519,604]⟩,⟨7,227,[66,158,270,287,357,444,519,604]⟩]⟩
def row8_796 : State := ⟨[10,66,158,229,297,357,450,519,594],[⟨11,471,[68,158,229,297,357,450,519,594]⟩,⟨11,486,[66,158,239,297,357,450,519,594]⟩,⟨0,471,[66,158,229,297,364,450,519,594]⟩,⟨0,486,[66,158,229,297,357,450,526,594]⟩]⟩
def row8_797 : State := ⟨[66,158,229,297,357,444,526,594],[⟨10,272,[66,229,270,297,357,444,526,594]⟩,⟨0,272,[66,158,229,297,357,444,526,656]⟩]⟩
def row8_798 : State := ⟨[66,158,166,229,287,357,456,519,594],[]⟩
def row8_799 : State := ⟨[10,66,158,229,297,357,444,526,594],[⟨10,472,[68,158,229,297,357,444,526,594]⟩,⟨10,486,[66,158,239,297,357,444,526,594]⟩,⟨0,472,[66,158,229,297,364,444,526,594]⟩,⟨0,486,[66,158,229,297,357,450,526,594]⟩]⟩
def row8_800 : State := ⟨[66,158,229,287,357,444,538,615],[⟨0,266,[66,158,229,322,357,444,538,615]⟩,⟨2,266,[66,158,229,332,357,444,538,615]⟩]⟩
def row8_801 : State := ⟨[66,158,166,229,304,357,444,519,594],[]⟩
def row8_802 : State := ⟨[10,66,158,229,287,357,450,526,594],[⟨10,470,[68,158,229,287,357,450,526,594]⟩,⟨1,486,[66,158,239,287,357,450,526,594]⟩,⟨0,486,[66,158,229,297,357,450,526,594]⟩,⟨0,475,[66,158,229,287,364,450,526,594]⟩]⟩
def row8_803 : State := ⟨[25,66,158,229,287,357,444,519,594],[⟨9,461,[73,158,229,287,357,444,519,594]⟩,⟨11,7,[66,166,229,287,357,444,519,594]⟩,⟨9,7,[66,158,239,287,357,444,519,594]⟩,⟨9,278,[25,66,270,287,357,444,519,594]⟩,⟨6,479,[66,158,229,306,357,444,519,594]⟩,⟨0,461,[66,158,229,287,369,444,519,594]⟩,⟨3,479,[66,158,229,287,357,458,519,594]⟩,⟨2,7,[66,158,229,287,357,444,526,594]⟩,⟨0,7,[66,158,229,287,357,444,519,604]⟩,⟨0,278,[25,66,158,229,287,357,444,665]⟩]⟩
def row8_804 : State := ⟨[66,158,229,287,357,444,519,594,672],[]⟩
def row8_805 : State := ⟨[66,158,229,287,357,424,444,519,594],[]⟩
def row8_806 : State := ⟨[66,158,229,287,357,444,519,594,673],[]⟩
def layer8 : Array State := #[row8_0,row8_1,row8_2,row8_3,row8_4,row8_5,row8_6,row8_7,row8_8,row8_9,row8_10,row8_11,row8_12,row8_13,row8_14,row8_15,row8_16,row8_17,row8_18,row8_19,row8_20,row8_21,row8_22,row8_23,row8_24,row8_25,row8_26,row8_27,row8_28,row8_29,row8_30,row8_31,row8_32,row8_33,row8_34,row8_35,row8_36,row8_37,row8_38,row8_39,row8_40,row8_41,row8_42,row8_43,row8_44,row8_45,row8_46,row8_47,row8_48,row8_49,row8_50,row8_51,row8_52,row8_53,row8_54,row8_55,row8_56,row8_57,row8_58,row8_59,row8_60,row8_61,row8_62,row8_63,row8_64,row8_65,row8_66,row8_67,row8_68,row8_69,row8_70,row8_71,row8_72,row8_73,row8_74,row8_75,row8_76,row8_77,row8_78,row8_79,row8_80,row8_81,row8_82,row8_83,row8_84,row8_85,row8_86,row8_87,row8_88,row8_89,row8_90,row8_91,row8_92,row8_93,row8_94,row8_95,row8_96,row8_97,row8_98,row8_99,row8_100,row8_101,row8_102,row8_103,row8_104,row8_105,row8_106,row8_107,row8_108,row8_109,row8_110,row8_111,row8_112,row8_113,row8_114,row8_115,row8_116,row8_117,row8_118,row8_119,row8_120,row8_121,row8_122,row8_123,row8_124,row8_125,row8_126,row8_127,row8_128,row8_129,row8_130,row8_131,row8_132,row8_133,row8_134,row8_135,row8_136,row8_137,row8_138,row8_139,row8_140,row8_141,row8_142,row8_143,row8_144,row8_145,row8_146,row8_147,row8_148,row8_149,row8_150,row8_151,row8_152,row8_153,row8_154,row8_155,row8_156,row8_157,row8_158,row8_159,row8_160,row8_161,row8_162,row8_163,row8_164,row8_165,row8_166,row8_167,row8_168,row8_169,row8_170,row8_171,row8_172,row8_173,row8_174,row8_175,row8_176,row8_177,row8_178,row8_179,row8_180,row8_181,row8_182,row8_183,row8_184,row8_185,row8_186,row8_187,row8_188,row8_189,row8_190,row8_191,row8_192,row8_193,row8_194,row8_195,row8_196,row8_197,row8_198,row8_199,row8_200,row8_201,row8_202,row8_203,row8_204,row8_205,row8_206,row8_207,row8_208,row8_209,row8_210,row8_211,row8_212,row8_213,row8_214,row8_215,row8_216,row8_217,row8_218,row8_219,row8_220,row8_221,row8_222,row8_223,row8_224,row8_225,row8_226,row8_227,row8_228,row8_229,row8_230,row8_231,row8_232,row8_233,row8_234,row8_235,row8_236,row8_237,row8_238,row8_239,row8_240,row8_241,row8_242,row8_243,row8_244,row8_245,row8_246,row8_247,row8_248,row8_249,row8_250,row8_251,row8_252,row8_253,row8_254,row8_255,row8_256,row8_257,row8_258,row8_259,row8_260,row8_261,row8_262,row8_263,row8_264,row8_265,row8_266,row8_267,row8_268,row8_269,row8_270,row8_271,row8_272,row8_273,row8_274,row8_275,row8_276,row8_277,row8_278,row8_279,row8_280,row8_281,row8_282,row8_283,row8_284,row8_285,row8_286,row8_287,row8_288,row8_289,row8_290,row8_291,row8_292,row8_293,row8_294,row8_295,row8_296,row8_297,row8_298,row8_299,row8_300,row8_301,row8_302,row8_303,row8_304,row8_305,row8_306,row8_307,row8_308,row8_309,row8_310,row8_311,row8_312,row8_313,row8_314,row8_315,row8_316,row8_317,row8_318,row8_319,row8_320,row8_321,row8_322,row8_323,row8_324,row8_325,row8_326,row8_327,row8_328,row8_329,row8_330,row8_331,row8_332,row8_333,row8_334,row8_335,row8_336,row8_337,row8_338,row8_339,row8_340,row8_341,row8_342,row8_343,row8_344,row8_345,row8_346,row8_347,row8_348,row8_349,row8_350,row8_351,row8_352,row8_353,row8_354,row8_355,row8_356,row8_357,row8_358,row8_359,row8_360,row8_361,row8_362,row8_363,row8_364,row8_365,row8_366,row8_367,row8_368,row8_369,row8_370,row8_371,row8_372,row8_373,row8_374,row8_375,row8_376,row8_377,row8_378,row8_379,row8_380,row8_381,row8_382,row8_383,row8_384,row8_385,row8_386,row8_387,row8_388,row8_389,row8_390,row8_391,row8_392,row8_393,row8_394,row8_395,row8_396,row8_397,row8_398,row8_399,row8_400,row8_401,row8_402,row8_403,row8_404,row8_405,row8_406,row8_407,row8_408,row8_409,row8_410,row8_411,row8_412,row8_413,row8_414,row8_415,row8_416,row8_417,row8_418,row8_419,row8_420,row8_421,row8_422,row8_423,row8_424,row8_425,row8_426,row8_427,row8_428,row8_429,row8_430,row8_431,row8_432,row8_433,row8_434,row8_435,row8_436,row8_437,row8_438,row8_439,row8_440,row8_441,row8_442,row8_443,row8_444,row8_445,row8_446,row8_447,row8_448,row8_449,row8_450,row8_451,row8_452,row8_453,row8_454,row8_455,row8_456,row8_457,row8_458,row8_459,row8_460,row8_461,row8_462,row8_463,row8_464,row8_465,row8_466,row8_467,row8_468,row8_469,row8_470,row8_471,row8_472,row8_473,row8_474,row8_475,row8_476,row8_477,row8_478,row8_479,row8_480,row8_481,row8_482,row8_483,row8_484,row8_485,row8_486,row8_487,row8_488,row8_489,row8_490,row8_491,row8_492,row8_493,row8_494,row8_495,row8_496,row8_497,row8_498,row8_499,row8_500,row8_501,row8_502,row8_503,row8_504,row8_505,row8_506,row8_507,row8_508,row8_509,row8_510,row8_511,row8_512,row8_513,row8_514,row8_515,row8_516,row8_517,row8_518,row8_519,row8_520,row8_521,row8_522,row8_523,row8_524,row8_525,row8_526,row8_527,row8_528,row8_529,row8_530,row8_531,row8_532,row8_533,row8_534,row8_535,row8_536,row8_537,row8_538,row8_539,row8_540,row8_541,row8_542,row8_543,row8_544,row8_545,row8_546,row8_547,row8_548,row8_549,row8_550,row8_551,row8_552,row8_553,row8_554,row8_555,row8_556,row8_557,row8_558,row8_559,row8_560,row8_561,row8_562,row8_563,row8_564,row8_565,row8_566,row8_567,row8_568,row8_569,row8_570,row8_571,row8_572,row8_573,row8_574,row8_575,row8_576,row8_577,row8_578,row8_579,row8_580,row8_581,row8_582,row8_583,row8_584,row8_585,row8_586,row8_587,row8_588,row8_589,row8_590,row8_591,row8_592,row8_593,row8_594,row8_595,row8_596,row8_597,row8_598,row8_599,row8_600,row8_601,row8_602,row8_603,row8_604,row8_605,row8_606,row8_607,row8_608,row8_609,row8_610,row8_611,row8_612,row8_613,row8_614,row8_615,row8_616,row8_617,row8_618,row8_619,row8_620,row8_621,row8_622,row8_623,row8_624,row8_625,row8_626,row8_627,row8_628,row8_629,row8_630,row8_631,row8_632,row8_633,row8_634,row8_635,row8_636,row8_637,row8_638,row8_639,row8_640,row8_641,row8_642,row8_643,row8_644,row8_645,row8_646,row8_647,row8_648,row8_649,row8_650,row8_651,row8_652,row8_653,row8_654,row8_655,row8_656,row8_657,row8_658,row8_659,row8_660,row8_661,row8_662,row8_663,row8_664,row8_665,row8_666,row8_667,row8_668,row8_669,row8_670,row8_671,row8_672,row8_673,row8_674,row8_675,row8_676,row8_677,row8_678,row8_679,row8_680,row8_681,row8_682,row8_683,row8_684,row8_685,row8_686,row8_687,row8_688,row8_689,row8_690,row8_691,row8_692,row8_693,row8_694,row8_695,row8_696,row8_697,row8_698,row8_699,row8_700,row8_701,row8_702,row8_703,row8_704,row8_705,row8_706,row8_707,row8_708,row8_709,row8_710,row8_711,row8_712,row8_713,row8_714,row8_715,row8_716,row8_717,row8_718,row8_719,row8_720,row8_721,row8_722,row8_723,row8_724,row8_725,row8_726,row8_727,row8_728,row8_729,row8_730,row8_731,row8_732,row8_733,row8_734,row8_735,row8_736,row8_737,row8_738,row8_739,row8_740,row8_741,row8_742,row8_743,row8_744,row8_745,row8_746,row8_747,row8_748,row8_749,row8_750,row8_751,row8_752,row8_753,row8_754,row8_755,row8_756,row8_757,row8_758,row8_759,row8_760,row8_761,row8_762,row8_763,row8_764,row8_765,row8_766,row8_767,row8_768,row8_769,row8_770,row8_771,row8_772,row8_773,row8_774,row8_775,row8_776,row8_777,row8_778,row8_779,row8_780,row8_781,row8_782,row8_783,row8_784,row8_785,row8_786,row8_787,row8_788,row8_789,row8_790,row8_791,row8_792,row8_793,row8_794,row8_795,row8_796,row8_797,row8_798,row8_799,row8_800,row8_801,row8_802,row8_803,row8_804,row8_805,row8_806]
def row9_0 : State := ⟨[41,66,158,177,229,287,357,444,519,594],[⟨0,0,[12,41,66,158,229,287,357,444,519]⟩]⟩
def row9_1 : State := ⟨[41,66,85,158,229,287,357,444,519,594],[]⟩
def row9_2 : State := ⟨[41,66,158,229,270,287,357,444,519,594],[]⟩
def row9_3 : State := ⟨[66,158,229,287,357,374,444,519,594],[⟨6,1,[158,177,229,287,357,374,444,519,594]⟩,⟨8,1,[158,229,253,287,357,374,444,519,594]⟩,⟨9,1,[158,229,287,310,357,374,444,519,594]⟩,⟨0,2,[41,66,158,229,287,357,444,519,594]⟩,⟨0,3,[66,158,229,287,357,423,444,519,594]⟩,⟨2,3,[66,158,229,287,357,444,493,519,594]⟩,⟨3,3,[66,158,229,287,357,444,519,573,594]⟩,⟨6,4,[66,158,229,287,355,357,444,519,594]⟩,⟨0,5,[66,158,229,287,357,380,444,519,594]⟩,⟨6,6,[66,158,229,287,342,357,444,519,594]⟩,⟨6,7,[66,158,229,287,357,444,468,519,594]⟩,⟨7,6,[66,158,229,287,343,357,444,519,594]⟩,⟨7,7,[66,158,229,287,357,444,519,553,594]⟩,⟨10,6,[66,158,229,287,344,357,444,519,594]⟩,⟨10,7,[66,158,229,287,357,444,519,594,629]⟩]⟩
def row9_4 : State := ⟨[41,66,158,229,287,357,378,444,519,594],[]⟩
def row9_5 : State := ⟨[41,54,66,158,229,287,357,444,519,594],[⟨0,4,[64,66,158,229,287,357,444,519,594]⟩]⟩
def row9_6 : State := ⟨[41,66,158,229,287,357,380,444,519,594],[]⟩
def row9_7 : State := ⟨[0,66,158,229,287,341,357,444,519,594],[⟨10,8,[66,159,229,287,341,357,444,519,594]⟩,⟨7,8,[66,158,230,287,341,357,444,519,594]⟩,⟨6,9,[66,158,229,288,341,357,444,519,594]⟩,⟨6,6,[66,158,229,287,342,357,444,519,594]⟩,⟨6,10,[66,158,229,287,341,358,444,519,594]⟩,⟨8,11,[66,158,229,287,341,357,444,520,594]⟩,⟨6,11,[66,158,229,287,341,357,444,519,595]⟩]⟩
def row9_8 : State := ⟨[41,66,158,229,287,357,425,444,519,594],[]⟩
def row9_9 : State := ⟨[66,158,229,287,357,415,444,519,594],[⟨10,12,[66,177,229,287,357,415,444,519,594]⟩,⟨10,13,[66,229,270,287,357,415,444,519,594]⟩,⟨11,13,[66,229,287,322,357,415,444,519,594]⟩,⟨0,2,[41,66,158,229,287,357,444,519,594]⟩,⟨0,3,[66,158,229,287,357,423,444,519,594]⟩,⟨0,14,[66,85,158,229,287,357,444,519,594]⟩,⟨0,15,[66,158,229,287,357,444,502,519,594]⟩,⟨1,14,[66,103,158,229,287,357,444,519,594]⟩,⟨1,15,[66,158,229,287,357,444,519,583,594]⟩,⟨6,16,[66,158,229,287,345,357,444,519,594]⟩,⟨0,7,[66,158,229,287,357,425,444,519,594]⟩,⟨6,17,[66,158,229,287,357,397,444,519,594]⟩,⟨0,18,[66,158,229,287,357,444,480,519,594]⟩,⟨7,17,[66,158,229,287,357,410,444,519,594]⟩,⟨1,18,[66,158,229,287,357,444,519,563,594]⟩,⟨10,19,[66,158,229,287,346,357,444,519,594]⟩,⟨0,20,[66,158,229,287,357,444,519,594,674]⟩]⟩
def row9_10 : State := ⟨[41,66,158,229,287,357,444,461,519,594],[]⟩
def row9_11 : State := ⟨[0,41,66,158,229,287,357,444,519,594],[⟨0,16,[42,66,158,229,287,357,444,519,594]⟩,⟨4,21,[41,66,159,229,287,357,444,519,594]⟩,⟨1,21,[41,66,158,230,287,357,444,519,594]⟩,⟨0,22,[41,66,158,229,288,357,444,519,594]⟩,⟨0,23,[41,66,158,229,287,358,444,519,594]⟩,⟨2,24,[41,66,158,229,287,357,444,520,594]⟩,⟨0,24,[41,66,158,229,287,357,444,519,595]⟩]⟩
def row9_12 : State := ⟨[41,66,158,229,287,357,444,468,519,594],[]⟩
def row9_13 : State := ⟨[41,66,118,158,229,287,357,444,519,594],[⟨0,17,[66,129,158,229,287,357,444,519,594]⟩]⟩
def row9_14 : State := ⟨[41,66,158,229,287,357,444,480,519,594],[]⟩
def row9_15 : State := ⟨[10,41,66,158,229,287,357,444,519,594],[⟨0,19,[48,66,158,229,287,357,444,519,594]⟩,⟨0,25,[41,68,158,229,287,357,444,519,594]⟩,⟨1,26,[41,66,158,239,287,357,444,519,594]⟩,⟨0,26,[41,66,158,229,297,357,444,519,594]⟩,⟨0,27,[41,66,158,229,287,364,444,519,594]⟩,⟨3,28,[41,66,158,229,287,357,450,519,594]⟩,⟨2,28,[41,66,158,229,287,357,444,526,594]⟩]⟩
def row9_16 : State := ⟨[41,66,158,229,287,357,444,519,594,674],[]⟩
def row9_17 : State := ⟨[41,66,158,229,287,341,357,444,519,594],[⟨0,29,[66,158,229,287,352,357,444,519,594]⟩]⟩
def row9_18 : State := ⟨[41,66,158,229,287,357,444,465,519,594],[⟨0,1,[66,158,229,287,378,444,465,519,594]⟩,⟨3,12,[66,158,229,287,357,461,465,519,594]⟩,⟨6,3,[66,158,229,287,357,444,471,519,594]⟩,⟨6,30,[37,41,66,158,229,357,444,519,594]⟩]⟩
def row9_19 : State := ⟨[41,66,158,229,287,357,391,444,519,594],[⟨6,31,[66,158,229,287,357,395,444,519,594]⟩]⟩
def row9_20 : State := ⟨[41,66,158,229,287,357,444,519,588,594],[⟨3,13,[66,158,229,287,357,461,519,588,594]⟩,⟨2,13,[66,158,229,287,357,444,543,588,594]⟩,⟨6,15,[66,158,229,287,357,444,519,590,594]⟩]⟩
def row9_21 : State := ⟨[66,158,177,229,253,287,357,444,519,594],[⟨9,32,[66,177,253,270,287,357,444,519,594]⟩,⟨0,33,[66,98,158,229,287,357,444,519,594]⟩,⟨0,34,[66,158,229,278,287,357,444,519,594]⟩,⟨2,35,[23,66,158,177,229,287,357,444,594]⟩,⟨0,35,[12,66,158,229,253,287,357,444,519]⟩]⟩
def row9_22 : State := ⟨[66,85,158,177,229,287,357,444,519,594],[⟨0,36,[12,66,85,158,229,287,357,444,519]⟩]⟩
def row9_23 : State := ⟨[66,158,229,287,357,444,519,625,656],[⟨0,37,[66,158,229,287,380,444,519,625,656]⟩,⟨0,38,[66,158,229,287,425,444,519,625,656]⟩,⟨3,39,[66,158,229,287,357,468,519,625,656]⟩,⟨3,40,[66,158,229,287,357,480,519,625,656]⟩,⟨3,41,[35,66,158,229,287,357,519,625,656]⟩,⟨1,32,[66,158,229,287,357,465,519,625,656]⟩,⟨0,42,[66,158,229,287,357,444,519,633,656]⟩,⟨10,43,[15,66,229,287,357,444,519,656]⟩,⟨10,44,[15,66,229,287,357,444,519,625,656]⟩,⟨10,45,[15,66,158,229,287,357,444,519,656]⟩,⟨1,46,[66,158,229,287,357,444,519,650,656]⟩,⟨2,47,[4,66,158,229,287,357,444,519,625]⟩,⟨1,48,[66,158,229,287,357,444,519,625,687]⟩,⟨0,49,[66,158,229,287,357,444,519,625,661]⟩,⟨1,50,[66,158,229,287,357,444,519,625,693]⟩,⟨0,51,[66,158,229,287,357,444,519,625,671]⟩,⟨0,52,[66,158,229,287,357,444,519,594]⟩,⟨8,53,[66,158,229,287,357,444,519,594,656]⟩,⟨10,54,[66,158,229,287,357,444,519,594,625]⟩]⟩
def row9_24 : State := ⟨[66,158,177,229,270,287,357,444,519,594],[⟨0,34,[66,158,229,278,287,357,444,519,594]⟩,⟨0,55,[12,66,158,229,270,287,357,444,519]⟩]⟩
def row9_25 : State := ⟨[66,85,158,229,287,357,444,519,594],[⟨0,2,[41,66,158,229,287,357,444,519,594]⟩,⟨0,33,[66,98,158,229,287,357,444,519,594]⟩,⟨3,56,[66,158,229,287,313,357,444,519,594]⟩,⟨0,57,[66,158,229,287,357,387,444,519,594]⟩,⟨0,58,[66,78,158,229,287,357,444,519,594]⟩,⟨6,59,[66,158,229,287,357,444,461,519,594]⟩,⟨7,60,[66,158,229,287,357,444,519,560,594]⟩,⟨10,60,[66,158,229,287,357,444,519,594,635]⟩]⟩
def row9_26 : State := ⟨[66,158,229,278,287,357,444,519,594],[⟨3,61,[66,158,188,229,287,357,444,519,594]⟩,⟨0,62,[66,158,229,287,340,357,444,519,594]⟩,⟨6,63,[158,229,278,287,357,380,444,519,594]⟩,⟨6,64,[61,66,158,229,287,357,444,519,594]⟩,⟨0,65,[66,158,229,287,357,444,508,519,594]⟩,⟨6,66,[66,158,207,229,287,357,444,519,594]⟩,⟨0,67,[66,158,229,287,357,444,509,519,594]⟩,⟨11,68,[66,229,278,287,357,444,519,563,594]⟩,⟨7,69,[66,146,158,229,287,357,444,594]⟩,⟨7,70,[66,146,158,229,287,357,444,519,594]⟩,⟨7,71,[66,146,158,229,278,287,357,444,594]⟩,⟨0,72,[66,158,229,287,357,444,519,594,706]⟩,⟨9,68,[66,158,278,287,357,444,519,594,637]⟩,⟨10,69,[66,158,223,229,287,357,444,519]⟩,⟨10,70,[66,158,223,229,287,357,444,519,594]⟩,⟨10,71,[66,158,223,229,278,287,357,444,519]⟩]⟩
def row9_27 : State := ⟨[66,158,177,229,278,287,357,444,519,594],[⟨7,73,[66,146,158,177,229,287,357,444,594]⟩,⟨0,74,[12,66,158,229,278,287,357,444,519]⟩,⟨10,75,[66,158,177,223,229,287,357,444,519]⟩]⟩
def row9_28 : State := ⟨[66,85,158,229,287,310,357,444,519,594],[⟨6,76,[98,158,229,287,310,357,444,519,594]⟩,⟨6,77,[66,158,229,310,313,357,444,519,594]⟩,⟨0,2,[41,66,158,229,287,357,444,519,594]⟩,⟨3,78,[66,158,229,287,316,357,444,519,594]⟩,⟨3,79,[36,66,85,158,229,287,357,519,594]⟩]⟩
def row9_29 : State := ⟨[66,158,177,229,287,332,357,444,519,594],[⟨10,51,[66,177,229,287,339,357,444,519,594]⟩,⟨0,61,[66,108,158,229,287,357,444,519,594]⟩,⟨0,62,[66,158,229,287,340,357,444,519,594]⟩,⟨0,80,[12,66,158,229,287,332,357,444,519]⟩]⟩
def row9_30 : State := ⟨[54,66,158,177,229,287,357,444,519,594],[⟨0,81,[12,54,66,158,229,287,357,444,519]⟩]⟩
def row9_31 : State := ⟨[66,158,229,287,380,444,465,519,594],[⟨0,82,[158,177,229,287,380,444,465,519,594]⟩,⟨2,82,[158,229,253,287,380,444,465,519,594]⟩,⟨3,83,[158,229,287,310,380,444,465,519,594]⟩,⟨3,84,[66,158,229,287,444,465,519,576,594]⟩,⟨0,85,[0,66,158,229,287,380,465,519,594]⟩,⟨3,86,[66,158,229,287,380,465,480,519,594]⟩,⟨5,86,[66,158,229,287,380,465,498,519,594]⟩,⟨3,87,[66,158,229,287,380,465,519,594,691]⟩,⟨6,88,[66,158,229,287,342,380,465,519,594]⟩,⟨6,89,[37,66,158,229,380,444,465,519,594]⟩,⟨0,90,[66,158,229,287,358,444,519,594]⟩,⟨0,91,[66,158,229,287,358,444,465,519,594]⟩,⟨0,92,[66,158,229,287,358,380,444,519,594]⟩,⟨3,37,[66,158,229,287,380,465,519,588,594]⟩,⟨0,63,[66,158,229,287,380,444,519,592,594]⟩,⟨5,37,[66,158,229,287,380,465,519,594,656]⟩,⟨2,63,[66,158,229,287,380,444,519,594,662]⟩]⟩
def row9_32 : State := ⟨[66,158,177,229,287,357,380,444,519,594],[⟨0,93,[47,66,177,229,287,357,444,519,594]⟩,⟨0,94,[66,67,158,229,287,357,444,519,594]⟩,⟨0,95,[66,158,229,287,357,428,444,519,594]⟩,⟨0,96,[12,66,158,229,287,357,380,444,519]⟩]⟩
def row9_33 : State := ⟨[0,66,158,229,287,357,465,519,594],[⟨4,97,[66,159,229,287,357,465,519,594]⟩,⟨0,98,[66,158,159,229,287,357,465,519,594]⟩,⟨2,99,[0,66,159,229,287,357,465,519,594]⟩,⟨1,97,[66,158,230,287,357,465,519,594]⟩,⟨2,98,[66,158,229,230,287,357,465,519,594]⟩,⟨0,99,[0,66,158,230,287,357,465,519,594]⟩,⟨0,100,[66,158,229,288,357,465,519,594]⟩,⟨3,101,[66,158,229,287,288,357,465,519,594]⟩,⟨0,102,[0,66,158,229,288,357,465,519,594]⟩,⟨0,103,[0,66,158,229,287,358,465,519,594]⟩,⟨0,85,[0,66,158,229,287,380,465,519,594]⟩,⟨0,104,[0,66,158,229,287,465,519,574,594]⟩,⟨0,105,[0,37,66,158,229,357,519,594]⟩,⟨0,106,[0,37,66,158,229,357,465,519,594]⟩,⟨0,107,[0,37,66,158,229,287,357,519,594]⟩,⟨5,108,[66,158,229,287,357,465,520,594]⟩,⟨7,109,[66,158,229,287,357,465,519,520,594]⟩,⟨2,110,[0,66,158,229,287,357,465,520,594]⟩,⟨3,108,[66,158,229,287,357,465,519,595]⟩,⟨10,109,[66,158,229,287,357,465,519,594,595]⟩,⟨0,110,[0,66,158,229,287,357,465,519,595]⟩]⟩
def row9_34 : State := ⟨[0,66,158,229,287,357,444,465,519,594],[⟨8,111,[66,159,229,287,357,444,465,519,594]⟩,⟨6,111,[66,158,230,287,357,444,465,519,594]⟩,⟨6,112,[66,158,229,288,357,444,465,519,594]⟩,⟨0,91,[66,158,229,287,358,444,465,519,594]⟩,⟨0,113,[0,37,66,158,229,357,444,519,594]⟩,⟨8,114,[66,158,229,287,357,444,465,520,594]⟩,⟨6,114,[66,158,229,287,357,444,465,519,595]⟩]⟩
def row9_35 : State := ⟨[66,158,177,229,287,357,425,444,519,594],[⟨0,115,[66,158,174,229,287,357,444,519,594]⟩,⟨0,95,[66,158,229,287,357,428,444,519,594]⟩,⟨0,116,[12,66,158,229,287,357,425,444,519]⟩]⟩
def row9_36 : State := ⟨[55,66,158,229,287,357,444,519,594],[⟨0,117,[66,158,175,229,287,357,444,519,594]⟩,⟨2,117,[66,158,229,252,287,357,444,519,594]⟩,⟨3,118,[66,158,229,287,309,357,444,519,594]⟩,⟨0,119,[54,66,158,229,287,357,444,519,594]⟩,⟨0,90,[66,158,229,287,358,444,519,594]⟩,⟨6,94,[66,158,229,287,357,358,444,519,594]⟩,⟨0,120,[55,66,158,229,287,358,444,519,594]⟩,⟨0,121,[0,66,158,229,287,357,444,519,594]⟩,⟨6,115,[66,158,229,287,357,444,464,519,594]⟩,⟨7,122,[66,158,229,287,357,444,519,548,594]⟩,⟨10,122,[66,158,229,287,357,444,519,594,624]⟩]⟩
def row9_37 : State := ⟨[55,66,158,229,287,357,444,465,519,594],[⟨0,91,[66,158,229,287,358,444,465,519,594]⟩,⟨0,123,[0,66,158,229,287,357,465,519,594]⟩,⟨6,124,[37,55,66,158,229,357,444,519,594]⟩]⟩
def row9_38 : State := ⟨[66,158,229,287,357,428,444,519,594],[⟨10,42,[66,229,270,287,357,428,444,519,594]⟩,⟨11,42,[66,229,287,322,357,428,444,519,594]⟩,⟨2,125,[66,92,158,229,287,357,444,519,594]⟩,⟨0,65,[66,158,229,287,357,444,508,519,594]⟩,⟨3,125,[66,105,158,229,287,357,444,519,594]⟩,⟨1,65,[66,158,229,287,357,444,519,587,594]⟩,⟨6,126,[66,158,229,287,357,398,444,519,594]⟩,⟨0,127,[66,158,229,287,357,444,490,519,594]⟩,⟨7,126,[66,158,229,287,357,411,444,519,594]⟩,⟨1,127,[66,158,229,287,357,444,519,572,594]⟩,⟨0,84,[66,158,229,287,428,444,519,594,625]⟩,⟨10,128,[66,158,229,287,347,357,444,519]⟩,⟨10,129,[66,158,229,287,347,357,444,519,594]⟩,⟨10,130,[66,158,229,287,347,357,428,444,519]⟩,⟨0,131,[66,158,229,287,357,444,519,594,708]⟩]⟩
def row9_39 : State := ⟨[66,158,177,229,287,357,428,444,519,594],[⟨0,132,[12,66,158,229,287,357,428,444,519]⟩,⟨10,133,[66,158,177,229,287,347,357,444,519]⟩]⟩
def row9_40 : State := ⟨[0,66,158,229,287,357,444,519,549,594],[⟨9,134,[66,159,229,287,357,444,519,549,594]⟩,⟨7,135,[66,158,230,287,357,444,519,549,594]⟩,⟨7,136,[66,158,229,288,357,444,519,549,594]⟩,⟨0,137,[66,158,229,287,358,444,519,549,594]⟩,⟨2,138,[66,158,229,287,357,444,520,549,594]⟩,⟨7,139,[66,158,229,287,357,444,519,550,594]⟩,⟨2,140,[0,29,66,158,287,357,444,519,594]⟩,⟨7,141,[66,158,229,287,357,444,519,549,595]⟩]⟩
def row9_41 : State := ⟨[66,158,177,229,287,357,444,494,519,594],[⟨9,39,[66,177,270,287,357,444,494,519,594]⟩,⟨0,142,[66,88,177,229,287,357,444,519,594]⟩,⟨0,143,[66,99,158,229,287,357,444,519,594]⟩,⟨0,65,[66,158,229,287,357,444,508,519,594]⟩,⟨0,144,[12,66,158,229,287,357,444,494,519]⟩]⟩
def row9_42 : State := ⟨[0,66,158,177,229,287,357,444,519,594],[⟨10,145,[66,159,177,229,287,357,444,519,594]⟩,⟨1,146,[66,158,177,230,287,357,444,519,594]⟩,⟨0,147,[66,158,177,229,288,357,444,519,594]⟩,⟨0,148,[66,158,177,229,287,358,444,519,594]⟩,⟨0,149,[66,158,177,229,287,357,444,520,594]⟩,⟨0,150,[66,158,177,229,287,357,444,519,595]⟩,⟨0,151,[0,12,66,158,229,287,357,444,519]⟩]⟩
def row9_43 : State := ⟨[66,158,177,229,287,357,444,468,519,594],[⟨0,152,[66,137,158,229,287,357,444,519,594]⟩,⟨0,153,[66,158,229,287,357,444,488,519,594]⟩,⟨0,154,[12,66,158,229,287,357,444,468,519]⟩]⟩
def row9_44 : State := ⟨[66,118,158,177,229,287,357,444,519,594],[⟨0,155,[12,66,118,158,229,287,357,444,519]⟩]⟩
def row9_45 : State := ⟨[66,158,229,287,357,444,519,625,637],[⟨1,156,[66,158,253,287,357,444,519,625,637]⟩,⟨7,157,[66,158,270,287,357,444,519,625,637]⟩,⟨0,86,[66,158,229,287,380,444,519,625,637]⟩,⟨0,158,[66,158,229,287,425,444,519,625,637]⟩,⟨10,159,[15,66,229,287,357,444,519,625,637]⟩,⟨0,68,[66,158,229,287,357,444,519,637,669]⟩,⟨4,160,[44,66,158,229,287,357,444,519,625]⟩,⟨0,161,[66,158,229,287,357,444,519,625,685]⟩,⟨0,162,[66,158,229,287,357,444,519,625,652]⟩,⟨0,49,[66,158,229,287,357,444,519,625,661]⟩,⟨0,50,[66,158,229,287,357,444,519,625,683]⟩,⟨0,163,[66,158,229,287,357,444,519,600]⟩,⟨0,164,[66,158,229,287,357,444,519,600,637]⟩,⟨0,145,[66,158,229,287,357,444,519,600,625]⟩]⟩
def row9_46 : State := ⟨[66,158,177,229,287,357,444,480,519,594],[⟨0,165,[66,158,159,229,287,357,444,519,594]⟩,⟨0,153,[66,158,229,287,357,444,488,519,594]⟩,⟨0,166,[12,66,158,229,287,357,444,480,519]⟩]⟩
def row9_47 : State := ⟨[66,119,158,229,287,357,444,519,594],[⟨0,121,[0,66,158,229,287,357,444,519,594]⟩,⟨0,152,[66,137,158,229,287,357,444,519,594]⟩,⟨0,167,[66,118,158,229,287,357,444,519,594]⟩,⟨10,163,[66,159,229,287,357,444,519,594]⟩,⟨0,165,[66,158,159,229,287,357,444,519,594]⟩,⟨0,168,[66,119,159,229,287,357,444,519,594]⟩,⟨0,58,[66,78,158,229,287,357,444,519,594]⟩,⟨2,169,[66,158,229,259,287,357,444,519,594]⟩,⟨3,170,[66,158,229,287,320,357,444,519,594]⟩,⟨6,171,[66,158,229,287,357,404,444,519,594]⟩,⟨6,172,[35,66,119,158,229,287,357,519,594]⟩,⟨0,173,[66,119,158,229,287,357,465,519,594]⟩,⟨6,58,[66,114,158,229,287,357,444,519,594]⟩,⟨7,174,[66,158,229,287,357,444,519,558,594]⟩,⟨10,175,[66,158,229,287,357,444,519,594,655]⟩]⟩
def row9_48 : State := ⟨[66,119,158,177,229,287,357,444,519,594],[⟨10,145,[66,159,177,229,287,357,444,519,594]⟩,⟨0,176,[12,66,119,158,229,287,357,444,519]⟩]⟩
def row9_49 : State := ⟨[66,158,229,287,357,444,488,519,594],[⟨10,46,[66,229,287,322,357,444,488,519,594]⟩,⟨2,17,[66,158,205,229,287,357,444,519,594]⟩,⟨0,67,[66,158,229,287,357,444,509,519,594]⟩,⟨3,177,[66,106,158,229,287,357,444,519,594]⟩,⟨1,72,[66,158,229,287,357,444,519,594,714]⟩,⟨6,178,[66,158,229,287,356,357,444,519,594]⟩,⟨0,127,[66,158,229,287,357,444,490,519,594]⟩,⟨7,126,[66,158,229,287,357,411,444,519,594]⟩,⟨6,179,[66,158,229,287,357,444,519,593,594]⟩,⟨3,180,[66,158,229,287,357,488,519,594,656]⟩,⟨10,181,[66,158,229,287,357,438,444,519]⟩,⟨10,182,[66,158,229,287,357,438,444,519,594]⟩,⟨10,183,[66,158,229,287,357,438,444,488,519]⟩,⟨1,184,[66,158,229,287,357,444,519,594,712]⟩]⟩
def row9_50 : State := ⟨[66,158,177,229,287,357,444,488,519,594],[⟨0,185,[12,66,158,229,287,357,444,488,519]⟩,⟨10,186,[66,158,177,229,287,357,438,444,519]⟩]⟩
def row9_51 : State := ⟨[66,118,158,229,253,287,357,444,519,594],[⟨7,187,[66,158,253,258,287,357,444,519,594]⟩,⟨0,58,[66,78,158,229,287,357,444,519,594]⟩,⟨2,188,[66,158,229,261,287,357,444,519,594]⟩,⟨2,189,[23,66,118,158,229,287,357,444,594]⟩]⟩
def row9_52 : State := ⟨[66,158,177,229,287,357,444,498,519,594],[⟨10,49,[66,177,229,287,357,444,505,519,594]⟩,⟨0,190,[66,130,158,229,287,357,444,519,594]⟩,⟨0,67,[66,158,229,287,357,444,509,519,594]⟩,⟨0,191,[12,66,158,229,287,357,444,498,519]⟩]⟩
def row9_53 : State := ⟨[10,66,158,229,253,287,357,444,519,594],[⟨10,192,[68,158,229,253,287,357,444,519,594]⟩,⟨9,193,[66,158,239,253,287,357,444,519,594]⟩,⟨11,41,[10,66,253,270,287,357,444,519,594]⟩,⟨2,194,[66,158,229,255,287,357,444,519,594]⟩,⟨2,195,[66,158,229,253,297,357,444,519,594]⟩,⟨2,196,[66,158,229,253,287,364,444,519,594]⟩,⟨4,197,[66,158,229,253,287,357,450,519,594]⟩,⟨2,198,[66,158,229,253,287,357,444,526,594]⟩,⟨0,199,[10,23,66,158,229,287,357,444,594]⟩,⟨10,172,[10,66,158,221,229,287,357,444,519]⟩]⟩
def row9_54 : State := ⟨[66,158,177,229,287,357,444,519,594,681],[⟨0,200,[12,66,158,229,287,357,444,519,681]⟩,⟨11,50,[66,177,229,287,357,444,519,594,684]⟩,⟨1,201,[66,155,158,229,287,357,444,519,594]⟩,⟨0,72,[66,158,229,287,357,444,519,594,706]⟩]⟩
def row9_55 : State := ⟨[66,158,177,229,287,357,444,465,519,594],[⟨0,82,[158,177,229,287,380,444,465,519,594]⟩,⟨5,156,[66,177,229,287,357,465,480,519,594]⟩,⟨0,173,[66,119,158,229,287,357,465,519,594]⟩,⟨6,173,[66,122,177,229,287,357,444,519,594]⟩,⟨0,202,[66,136,158,229,287,357,444,519,594]⟩,⟨0,127,[66,158,229,287,357,444,490,519,594]⟩,⟨6,203,[37,66,158,177,229,357,444,519,594]⟩,⟨0,203,[12,66,158,229,287,357,444,465,519]⟩]⟩
def row9_56 : State := ⟨[66,85,158,229,287,357,444,465,519,594],[⟨3,12,[66,158,229,287,357,461,465,519,594]⟩,⟨0,58,[66,78,158,229,287,357,444,519,594]⟩,⟨6,3,[66,158,229,287,357,444,471,519,594]⟩,⟨6,204,[37,66,85,158,229,357,444,519,594]⟩]⟩
def row9_57 : State := ⟨[66,158,177,229,287,357,444,519,588,594],[⟨0,205,[2,158,177,229,287,357,444,519,594]⟩,⟨10,162,[66,177,229,287,357,444,519,591,594]⟩,⟨0,206,[66,149,158,229,287,357,444,519,594]⟩,⟨6,179,[66,158,229,287,357,444,519,593,594]⟩,⟨0,207,[12,66,158,229,287,357,444,519,588]⟩]⟩
def row9_58 : State := ⟨[0,66,158,229,287,310,357,444,519,594],[⟨5,208,[66,159,229,287,310,357,444,519,594]⟩,⟨3,208,[66,158,230,287,310,357,444,519,594]⟩,⟨6,209,[66,158,229,288,310,357,444,519,594]⟩,⟨3,210,[66,158,229,287,310,358,444,519,594]⟩,⟨0,211,[0,36,66,158,229,287,357,519,594]⟩,⟨5,212,[66,158,229,287,310,357,444,520,594]⟩,⟨3,212,[66,158,229,287,310,357,444,519,595]⟩]⟩
def row9_59 : State := ⟨[66,158,229,287,425,444,519,594,625],[⟨4,213,[66,229,270,287,425,444,519,594,625]⟩,⟨5,213,[66,229,287,322,425,444,519,594,625]⟩,⟨0,84,[66,158,229,287,428,444,519,594,625]⟩,⟨4,104,[3,66,158,229,287,425,444,519,625]⟩,⟨0,214,[66,158,229,287,425,444,519,625,674]⟩,⟨0,158,[66,158,229,287,425,444,519,625,637]⟩,⟨1,158,[66,158,229,287,425,444,519,625,644]⟩,⟨0,38,[66,158,229,287,425,444,519,625,656]⟩,⟨1,38,[66,158,229,287,425,444,519,625,665]⟩,⟨10,215,[15,66,229,287,425,444,519,594,625]⟩,⟨0,216,[66,158,229,287,364,444,519,594]⟩,⟨0,217,[66,158,229,287,364,444,519,594,625]⟩,⟨0,218,[66,158,229,287,364,425,444,519,594]⟩]⟩
def row9_60 : State := ⟨[66,158,177,229,287,357,444,519,594,629],[⟨0,219,[12,66,158,229,287,357,444,519,629]⟩,⟨0,220,[66,68,158,229,287,357,444,519,594]⟩,⟨0,221,[66,158,229,287,357,444,519,594,704]⟩]⟩
def row9_61 : State := ⟨[10,66,158,177,229,287,357,444,519,594],[⟨10,217,[68,158,177,229,287,357,444,519,594]⟩,⟨1,222,[66,158,177,239,287,357,444,519,594]⟩,⟨0,222,[66,158,177,229,297,357,444,519,594]⟩,⟨0,223,[66,158,177,229,287,364,444,519,594]⟩,⟨1,224,[66,158,177,229,287,357,450,519,594]⟩,⟨0,224,[66,158,177,229,287,357,444,526,594]⟩,⟨0,225,[10,12,66,158,229,287,357,444,519]⟩]⟩
def row9_62 : State := ⟨[66,158,229,287,357,444,519,625,674],[⟨4,226,[66,177,229,287,357,444,519,625,674]⟩,⟨0,87,[66,158,229,287,380,444,519,625,674]⟩,⟨0,214,[66,158,229,287,425,444,519,625,674]⟩,⟨10,227,[15,66,229,287,357,444,519,625,674]⟩,⟨4,160,[44,66,158,229,287,357,444,519,625]⟩,⟨0,161,[66,158,229,287,357,444,519,625,685]⟩,⟨1,161,[66,158,229,287,357,444,519,625,696]⟩,⟨1,48,[66,158,229,287,357,444,519,625,687]⟩,⟨0,48,[66,158,229,287,357,444,519,625,680]⟩,⟨0,228,[66,158,229,287,357,444,519,598]⟩,⟨0,229,[66,158,229,287,357,444,519,598,674]⟩,⟨0,209,[66,158,229,287,357,444,519,598,625]⟩]⟩
def row9_63 : State := ⟨[66,158,177,229,287,357,444,519,594,674],[⟨0,230,[12,66,158,229,287,357,444,519,674]⟩,⟨0,231,[66,158,162,229,287,357,444,519,594]⟩,⟨0,221,[66,158,229,287,357,444,519,594,704]⟩]⟩
def row9_64 : State := ⟨[12,66,158,229,287,357,444,519],[⟨4,211,[3,12,66,158,229,287,357,444,519]⟩,⟨0,232,[12,68,158,229,287,357,444,519]⟩,⟨0,233,[12,66,68,158,229,287,357,444,519]⟩,⟨0,225,[10,12,66,158,229,287,357,444,519]⟩,⟨0,234,[12,66,162,229,287,357,444,519]⟩,⟨0,235,[12,66,158,162,229,287,357,444,519]⟩,⟨0,0,[12,41,66,158,229,287,357,444,519]⟩,⟨0,236,[12,66,158,177,229,287,357,444,519]⟩,⟨1,237,[12,66,158,241,287,357,444,519]⟩,⟨0,238,[12,66,158,229,241,287,357,444,519]⟩,⟨0,35,[12,66,158,229,253,287,357,444,519]⟩,⟨0,36,[12,66,85,158,229,287,357,444,519]⟩,⟨0,43,[12,66,229,270,287,357,444,519]⟩,⟨0,55,[12,66,158,229,270,287,357,444,519]⟩,⟨0,237,[12,66,158,229,299,357,444,519]⟩,⟨1,238,[12,66,158,229,287,299,357,444,519]⟩,⟨1,35,[12,66,158,229,287,310,357,444,519]⟩,⟨1,36,[12,66,103,158,229,287,357,444,519]⟩,⟨1,43,[12,66,229,287,322,357,444,519]⟩,⟨1,55,[12,66,158,229,287,322,357,444,519]⟩,⟨0,79,[12,66,158,183,229,287,357,444,519]⟩,⟨0,80,[12,66,158,229,287,332,357,444,519]⟩,⟨0,239,[12,66,158,229,287,366,444,519]⟩,⟨0,240,[12,66,158,229,287,357,366,444,519]⟩,⟨0,81,[12,54,66,158,229,287,357,444,519]⟩,⟨0,96,[12,66,158,229,287,357,380,444,519]⟩,⟨6,105,[7,12,66,229,287,357,444,519]⟩,⟨6,113,[7,12,66,158,229,287,357,444,519]⟩,⟨0,116,[12,66,158,229,287,357,425,444,519]⟩,⟨10,140,[12,20,66,158,229,287,357,444,519]⟩,⟨0,144,[12,66,158,229,287,357,444,494,519]⟩,⟨11,140,[12,32,66,158,229,287,357,444,519]⟩,⟨1,144,[12,66,158,229,287,357,444,519,574]⟩,⟨1,241,[12,66,158,229,287,357,451,519]⟩,⟨0,242,[12,66,158,229,287,357,444,451,519]⟩,⟨0,151,[0,12,66,158,229,287,357,444,519]⟩,⟨0,154,[12,66,158,229,287,357,444,468,519]⟩,⟨0,155,[12,66,118,158,229,287,357,444,519]⟩,⟨0,166,[12,66,158,229,287,357,444,480,519]⟩,⟨0,189,[12,66,158,202,229,287,357,444,519]⟩,⟨0,191,[12,66,158,229,287,357,444,498,519]⟩,⟨3,199,[12,35,66,158,229,287,357,444,519]⟩,⟨1,200,[12,66,158,229,287,357,444,519,691]⟩,⟨0,30,[12,66,158,229,287,341,357,444,519]⟩,⟨0,203,[12,66,158,229,287,357,444,465,519]⟩,⟨0,241,[12,66,158,229,287,357,444,528]⟩,⟨1,242,[12,66,158,229,287,357,444,519,528]⟩,⟨1,151,[1,12,66,158,229,287,357,444,519]⟩,⟨1,154,[12,66,158,229,287,357,444,519,553]⟩,⟨1,155,[12,66,141,158,229,287,357,444,519]⟩,⟨1,166,[12,66,158,229,287,357,444,519,563]⟩,⟨2,199,[12,22,66,158,229,287,357,444,519]⟩,⟨0,200,[12,66,158,229,287,357,444,519,681]⟩,⟨1,189,[12,66,158,229,279,287,357,444,519]⟩,⟨1,191,[12,66,158,229,287,357,444,519,580]⟩,⟨1,203,[12,66,158,229,287,357,444,519,549]⟩,⟨0,204,[12,66,158,229,287,357,391,444,519]⟩,⟨0,207,[12,66,158,229,287,357,444,519,588]⟩]⟩
def row9_65 : State := ⟨[12,66,158,229,287,357,444,519,594],[⟨4,121,[3,66,158,229,287,357,444,519,594]⟩,⟨10,216,[68,158,229,287,357,444,519,594]⟩,⟨0,220,[66,68,158,229,287,357,444,519,594]⟩,⟨0,243,[12,68,158,229,287,357,444,519,594]⟩,⟨0,244,[10,66,158,229,287,357,444,519,594]⟩,⟨10,228,[66,162,229,287,357,444,519,594]⟩,⟨0,231,[66,158,162,229,287,357,444,519,594]⟩,⟨0,245,[12,66,162,229,287,357,444,519,594]⟩,⟨9,246,[66,158,241,287,357,444,519,594]⟩,⟨2,247,[66,158,229,241,287,357,444,519,594]⟩,⟨1,248,[12,66,158,241,287,357,444,519,594]⟩,⟨0,45,[12,66,229,270,287,357,444,519,594]⟩,⟨8,246,[66,158,229,299,357,444,519,594]⟩,⟨3,247,[66,158,229,287,299,357,444,519,594]⟩,⟨0,248,[12,66,158,229,299,357,444,519,594]⟩,⟨1,45,[12,66,229,287,322,357,444,519,594]⟩,⟨0,249,[66,158,229,287,366,444,519,594]⟩,⟨10,250,[66,158,229,287,357,366,444,519,594]⟩,⟨0,251,[12,66,158,229,287,366,444,519,594]⟩,⟨6,107,[7,12,66,229,287,357,444,519,594]⟩,⟨3,252,[66,158,229,287,357,451,519,594]⟩,⟨8,253,[66,158,229,287,357,444,451,519,594]⟩,⟨1,254,[12,66,158,229,287,357,451,519,594]⟩,⟨2,252,[66,158,229,287,357,444,528,594]⟩,⟨9,253,[66,158,229,287,357,444,519,528,594]⟩,⟨0,254,[12,66,158,229,287,357,444,528,594]⟩,⟨4,211,[3,12,66,158,229,287,357,444,519]⟩,⟨0,219,[12,66,158,229,287,357,444,519,629]⟩,⟨0,225,[10,12,66,158,229,287,357,444,519]⟩,⟨0,230,[12,66,158,229,287,357,444,519,674]⟩,⟨0,255,[12,66,158,220,229,287,357,444,519]⟩,⟨0,256,[12,66,158,229,287,357,444,519,637]⟩,⟨1,255,[12,66,158,229,284,287,357,444,519]⟩,⟨1,256,[12,66,158,229,287,357,444,519,644]⟩,⟨0,30,[12,66,158,229,287,341,357,444,519]⟩,⟨0,257,[12,66,158,229,287,357,444,519,625]⟩,⟨0,258,[12,66,158,229,287,357,434,444,519]⟩,⟨0,259,[12,66,158,229,287,357,444,519,656]⟩,⟨1,258,[12,66,158,229,287,357,444,511,519]⟩,⟨1,259,[12,66,158,229,287,357,444,519,665]⟩]⟩
def row9_66 : State := ⟨[12,66,158,177,229,287,357,444,519],[⟨0,260,[12,68,158,177,229,287,357,444,519]⟩,⟨0,261,[12,66,162,177,229,287,357,444,519]⟩,⟨1,262,[12,66,158,177,241,287,357,444,519]⟩,⟨0,44,[12,66,177,229,270,287,357,444,519]⟩,⟨0,36,[12,66,85,158,229,287,357,444,519]⟩,⟨0,74,[12,66,158,229,278,287,357,444,519]⟩,⟨0,262,[12,66,158,177,229,299,357,444,519]⟩,⟨1,44,[12,66,177,229,287,322,357,444,519]⟩,⟨1,36,[12,66,103,158,229,287,357,444,519]⟩,⟨1,74,[12,66,158,229,287,329,357,444,519]⟩,⟨0,263,[12,66,158,177,229,287,366,444,519]⟩,⟨0,89,[12,158,177,229,287,357,380,444,519]⟩,⟨6,106,[7,12,66,177,229,287,357,444,519]⟩,⟨0,124,[12,58,66,158,229,287,357,444,519]⟩,⟨0,132,[12,66,158,229,287,357,428,444,519]⟩,⟨1,264,[12,66,158,177,229,287,357,451,519]⟩,⟨0,159,[12,66,177,229,287,357,444,480,519]⟩,⟨0,176,[12,66,119,158,229,287,357,444,519]⟩,⟨0,185,[12,66,158,229,287,357,444,488,519]⟩,⟨0,264,[12,66,158,177,229,287,357,444,528]⟩,⟨1,159,[12,66,177,229,287,357,444,519,563]⟩,⟨1,176,[12,66,143,158,229,287,357,444,519]⟩,⟨1,185,[12,66,158,229,287,357,444,519,569]⟩]⟩
def row9_67 : State := ⟨[12,66,158,177,229,287,357,444,519,594],[⟨10,217,[68,158,177,229,287,357,444,519,594]⟩,⟨10,209,[66,162,177,229,287,357,444,519,594]⟩,⟨1,265,[66,158,177,241,287,357,444,519,594]⟩,⟨0,265,[66,158,177,229,299,357,444,519,594]⟩,⟨0,266,[66,158,177,229,287,366,444,519,594]⟩,⟨1,267,[66,158,177,229,287,357,451,519,594]⟩,⟨0,267,[66,158,177,229,287,357,444,528,594]⟩,⟨0,215,[12,158,177,229,287,357,444,519,629]⟩,⟨0,227,[12,66,177,229,287,357,444,519,674]⟩,⟨0,268,[12,66,158,229,287,357,444,519,704]⟩]⟩
def row9_68 : State := ⟨[66,158,229,287,357,444,519,594,704],[⟨2,269,[66,158,227,229,287,357,444,519,594]⟩,⟨0,72,[66,158,229,287,357,444,519,594,706]⟩,⟨3,269,[66,158,229,286,287,357,444,519,594]⟩,⟨1,72,[66,158,229,287,357,444,519,594,714]⟩,⟨6,178,[66,158,229,287,356,357,444,519,594]⟩,⟨0,131,[66,158,229,287,357,444,519,594,708]⟩,⟨6,270,[66,158,229,287,357,443,444,519,594]⟩,⟨1,184,[66,158,229,287,357,444,519,594,712]⟩,⟨7,270,[66,158,229,287,357,444,518,519,594]⟩,⟨0,184,[66,158,229,287,357,444,519,594,705]⟩]⟩
def row9_69 : State := ⟨[66,158,177,229,287,357,444,519,594,704],[⟨0,268,[12,66,158,229,287,357,444,519,704]⟩]⟩
def row9_70 : State := ⟨[66,118,158,229,287,310,357,444,519,594],[⟨6,271,[137,158,229,287,310,357,444,519,594]⟩,⟨6,272,[66,158,229,310,319,357,444,519,594]⟩,⟨3,273,[66,158,229,287,327,357,444,519,594]⟩,⟨3,255,[36,66,118,158,229,287,357,519,594]⟩]⟩
def row9_71 : State := ⟨[66,158,177,229,287,357,444,519,594,637],[⟨9,40,[66,177,270,287,357,444,519,594,637]⟩,⟨9,68,[66,158,278,287,357,444,519,594,637]⟩,⟨0,256,[12,66,158,229,287,357,444,519,637]⟩,⟨11,48,[66,177,229,287,357,444,519,594,685]⟩,⟨0,274,[66,90,158,229,287,357,444,519,594]⟩,⟨0,72,[66,158,229,287,357,444,519,594,706]⟩]⟩
def row9_72 : State := ⟨[66,158,177,229,287,357,444,519,594,625],[⟨0,83,[158,177,229,287,380,444,519,594,625]⟩,⟨0,84,[66,158,229,287,428,444,519,594,625]⟩,⟨4,226,[66,177,229,287,357,444,519,625,674]⟩,⟨0,257,[12,66,158,229,287,357,444,519,625]⟩,⟨10,84,[158,177,229,287,357,444,519,594,633]⟩,⟨10,257,[15,66,177,229,287,357,444,519,594]⟩,⟨0,275,[60,66,158,229,287,357,444,519,594]⟩,⟨0,131,[66,158,229,287,357,444,519,594,708]⟩]⟩
def row9_73 : State := ⟨[66,85,158,229,287,357,444,519,549,594],[⟨0,276,[66,158,229,287,387,444,519,549,594]⟩,⟨2,277,[66,158,229,287,357,444,549,560,594]⟩,⟨7,278,[66,158,229,287,357,444,519,570,594]⟩,⟨7,258,[29,66,85,158,287,357,444,519,594]⟩]⟩
def row9_74 : State := ⟨[66,158,177,229,287,357,444,519,594,656],[⟨5,157,[66,177,229,287,357,480,519,594,656]⟩,⟨3,180,[66,158,229,287,357,488,519,594,656]⟩,⟨6,213,[158,177,229,287,357,444,519,629,656]⟩,⟨0,259,[12,66,158,229,287,357,444,519,656]⟩,⟨10,161,[66,177,229,287,357,444,519,594,687]⟩,⟨0,279,[66,124,158,229,287,357,444,519,594]⟩,⟨1,184,[66,158,229,287,357,444,519,594,712]⟩]⟩
def row9_75 : State := ⟨[41,66,158,229,287,357,444,519,594],[⟨6,280,[66,158,229,287,357,378,444,519,594]⟩,⟨6,59,[66,158,229,287,357,444,461,519,594]⟩,⟨7,59,[66,158,229,287,357,444,519,543,594]⟩,⟨10,59,[66,158,229,287,357,444,519,594,620]⟩]⟩
def row9_76 : State := ⟨[66,98,158,229,287,357,444,519,594],[⟨0,14,[66,85,158,229,287,357,444,519,594]⟩,⟨0,54,[66,158,177,229,287,357,444,519,594]⟩,⟨2,54,[66,158,229,253,287,357,444,519,594]⟩,⟨6,76,[98,158,229,287,310,357,444,519,594]⟩,⟨0,2,[41,66,158,229,287,357,444,519,594]⟩,⟨3,78,[66,158,229,287,316,357,444,519,594]⟩,⟨6,281,[98,158,229,287,357,380,444,519,594]⟩,⟨0,119,[54,66,158,229,287,357,444,519,594]⟩,⟨0,282,[66,158,229,287,357,388,444,519,594]⟩,⟨0,283,[0,98,158,229,287,357,444,519,594]⟩,⟨0,284,[66,79,158,229,287,357,444,519,594]⟩,⟨6,7,[66,158,229,287,357,444,468,519,594]⟩,⟨6,285,[98,158,229,287,357,444,519,553,594]⟩,⟨1,121,[1,66,158,229,287,357,444,519,594]⟩,⟨7,286,[66,158,229,287,357,444,519,567,594]⟩,⟨8,285,[98,158,229,287,357,444,519,594,629]⟩,⟨4,121,[3,66,158,229,287,357,444,519,594]⟩,⟨10,286,[66,158,229,287,357,444,519,594,640]⟩]⟩
def row9_77 : State := ⟨[66,85,98,158,229,287,357,444,519,594],[]⟩
def row9_78 : State := ⟨[66,85,158,229,270,287,357,444,519,594],[]⟩
def row9_79 : State := ⟨[66,158,196,229,287,357,444,519,594],[⟨10,77,[66,177,196,229,287,357,444,519,594]⟩,⟨0,2,[41,66,158,229,287,357,444,519,594]⟩,⟨0,78,[66,158,199,229,287,357,444,519,594]⟩,⟨2,61,[66,158,187,229,287,357,444,519,594]⟩,⟨0,53,[66,158,229,270,287,357,444,519,594]⟩,⟨3,61,[66,158,188,229,287,357,444,519,594]⟩,⟨1,53,[66,158,229,287,322,357,444,519,594]⟩,⟨10,287,[66,196,229,287,357,425,444,519,594]⟩,⟨6,121,[7,66,158,229,287,357,444,519,594]⟩,⟨0,288,[66,158,229,287,357,433,444,519,594]⟩,⟨10,289,[66,196,229,287,357,444,480,519,594]⟩,⟨0,167,[66,118,158,229,287,357,444,519,594]⟩,⟨0,290,[66,158,229,287,357,444,504,519,594]⟩,⟨11,289,[66,196,229,287,357,444,519,563,594]⟩,⟨1,167,[66,141,158,229,287,357,444,519,594]⟩,⟨1,290,[66,158,229,287,357,444,519,582,594]⟩,⟨10,291,[10,66,196,229,287,357,444,519,594]⟩,⟨4,292,[66,158,181,229,287,357,444,519,594]⟩,⟨0,20,[66,158,229,287,357,444,519,594,674]⟩]⟩
def row9_80 : State := ⟨[66,85,158,229,287,313,357,444,519,594],[]⟩
def row9_81 : State := ⟨[66,85,103,158,229,287,357,444,519,594],[⟨0,2,[41,66,158,229,287,357,444,519,594]⟩,⟨0,61,[66,108,158,229,287,357,444,519,594]⟩]⟩
def row9_82 : State := ⟨[66,85,158,229,287,322,357,444,519,594],[]⟩
def row9_83 : State := ⟨[54,66,85,158,229,287,357,444,519,594],[⟨0,293,[66,97,158,229,287,357,444,519,594]⟩]⟩
def row9_84 : State := ⟨[66,85,158,229,287,357,380,444,519,594],[⟨6,281,[98,158,229,287,357,380,444,519,594]⟩,⟨0,2,[41,66,158,229,287,357,444,519,594]⟩,⟨0,282,[66,158,229,287,357,388,444,519,594]⟩]⟩
def row9_85 : State := ⟨[66,158,229,287,357,387,444,519,594],[⟨0,4,[64,66,158,229,287,357,444,519,594]⟩,⟨0,282,[66,158,229,287,357,388,444,519,594]⟩,⟨0,125,[66,88,158,229,287,357,444,519,594]⟩,⟨0,7,[66,158,229,287,357,425,444,519,594]⟩,⟨2,125,[66,92,158,229,287,357,444,519,594]⟩,⟨2,7,[66,158,229,287,357,444,494,519,594]⟩,⟨3,6,[53,66,158,229,287,357,444,519,594]⟩,⟨3,288,[66,158,229,287,357,444,519,579,594]⟩,⟨6,294,[66,158,229,287,357,383,444,519,594]⟩,⟨6,3,[66,158,229,287,357,444,471,519,594]⟩,⟨0,276,[66,158,229,287,387,444,519,549,594]⟩,⟨6,2,[66,158,229,287,341,357,444,519,594]⟩,⟨7,278,[66,158,229,287,357,444,519,570,594]⟩,⟨2,276,[66,158,229,287,387,444,519,594,625]⟩,⟨10,278,[66,158,229,287,357,444,519,594,642]⟩]⟩
def row9_86 : State := ⟨[66,85,158,229,287,357,387,444,519,594],[]⟩
def row9_87 : State := ⟨[0,66,158,229,287,357,391,444,519,594],[⟨6,295,[66,159,229,287,357,391,444,519,594]⟩,⟨7,296,[66,158,230,287,357,391,444,519,594]⟩,⟨6,297,[66,158,229,288,357,391,444,519,594]⟩,⟨0,298,[66,158,229,287,358,391,444,519,594]⟩,⟨6,125,[66,158,229,287,357,392,444,519,594]⟩,⟨6,299,[66,158,229,287,357,391,444,520,594]⟩,⟨6,300,[66,158,229,287,357,391,444,519,595]⟩]⟩
def row9_88 : State := ⟨[66,85,158,229,287,357,425,444,519,594],[]⟩
def row9_89 : State := ⟨[0,66,158,229,287,357,444,511,519,594],[⟨11,301,[66,159,229,287,357,444,511,519,594]⟩,⟨9,301,[66,158,230,287,357,444,511,519,594]⟩,⟨9,302,[66,158,229,288,357,444,511,519,594]⟩,⟨0,303,[66,158,229,287,358,444,511,519,594]⟩,⟨9,304,[66,158,229,287,357,444,512,519,594]⟩,⟨11,305,[66,158,229,287,357,444,511,520,594]⟩,⟨9,305,[66,158,229,287,357,444,511,519,595]⟩]⟩
def row9_90 : State := ⟨[66,85,158,229,287,357,444,519,574,594],[⟨6,287,[66,158,229,313,357,444,519,574,594]⟩,⟨0,2,[41,66,158,229,287,357,444,519,594]⟩,⟨3,288,[66,158,229,287,357,444,519,579,594]⟩]⟩
def row9_91 : State := ⟨[0,66,85,158,229,287,357,444,519,594],[⟨0,306,[66,86,158,229,287,357,444,519,594]⟩,⟨0,283,[0,98,158,229,287,357,444,519,594]⟩,⟨2,307,[66,85,159,229,287,357,444,519,594]⟩,⟨0,307,[66,85,158,230,287,357,444,519,594]⟩,⟨0,308,[66,85,158,229,288,357,444,519,594]⟩,⟨0,309,[66,85,158,229,287,358,444,519,594]⟩,⟨2,310,[66,85,158,229,287,357,444,520,594]⟩,⟨0,310,[66,85,158,229,287,357,444,519,595]⟩]⟩
def row9_92 : State := ⟨[66,85,158,229,287,357,444,468,519,594],[]⟩
def row9_93 : State := ⟨[66,78,158,229,287,357,444,519,594],[⟨0,33,[66,98,158,229,287,357,444,519,594]⟩,⟨3,56,[66,158,229,287,313,357,444,519,594]⟩,⟨6,311,[66,158,229,287,357,386,444,519,594]⟩,⟨7,312,[66,158,229,287,357,444,519,557,594]⟩,⟨10,312,[66,158,229,287,357,444,519,594,634]⟩]⟩
def row9_94 : State := ⟨[66,78,85,158,229,287,357,444,519,594],[]⟩
def row9_95 : State := ⟨[66,85,158,229,287,357,444,461,519,594],[]⟩
def row9_96 : State := ⟨[66,85,118,158,229,287,357,444,519,594],[⟨0,58,[66,78,158,229,287,357,444,519,594]⟩,⟨0,17,[66,129,158,229,287,357,444,519,594]⟩]⟩
def row9_97 : State := ⟨[66,85,158,229,287,357,444,480,519,594],[]⟩
def row9_98 : State := ⟨[10,66,158,183,229,287,357,444,519,594],[⟨10,313,[68,158,183,229,287,357,444,519,594]⟩,⟨4,314,[66,158,184,229,287,357,444,519,594]⟩,⟨10,291,[10,66,196,229,287,357,444,519,594]⟩,⟨5,315,[66,158,183,239,287,357,444,519,594]⟩,⟨4,315,[66,158,183,229,297,357,444,519,594]⟩,⟨4,316,[66,158,183,229,287,364,444,519,594]⟩,⟨5,317,[66,158,183,229,287,357,450,519,594]⟩,⟨4,317,[66,158,183,229,287,357,444,526,594]⟩]⟩
def row9_99 : State := ⟨[66,85,158,229,287,357,444,519,594,691],[]⟩
def row9_100 : State := ⟨[0,66,103,158,229,287,357,444,519,594],[⟨1,318,[66,104,158,229,287,357,444,519,594]⟩,⟨3,319,[66,103,159,229,287,357,444,519,594]⟩,⟨1,320,[66,103,158,230,287,357,444,519,594]⟩,⟨1,321,[66,103,158,229,288,357,444,519,594]⟩,⟨1,322,[66,103,158,229,287,358,444,519,594]⟩,⟨1,323,[66,103,158,229,287,357,444,520,594]⟩,⟨1,324,[66,103,158,229,287,357,444,519,595]⟩]⟩
def row9_101 : State := ⟨[66,85,158,229,287,357,444,519,553,594],[⟨6,285,[98,158,229,287,357,444,519,553,594]⟩,⟨0,2,[41,66,158,229,287,357,444,519,594]⟩,⟨7,286,[66,158,229,287,357,444,519,567,594]⟩]⟩
def row9_102 : State := ⟨[66,158,229,287,357,444,475,519,594],[⟨10,277,[66,177,229,287,357,444,475,519,594]⟩,⟨10,325,[66,229,287,322,357,444,475,519,594]⟩,⟨0,2,[41,66,158,229,287,357,444,519,594]⟩,⟨0,278,[66,158,229,287,357,444,485,519,594]⟩,⟨2,17,[66,158,205,229,287,357,444,519,594]⟩,⟨0,15,[66,158,229,287,357,444,502,519,594]⟩,⟨1,14,[66,103,158,229,287,357,444,519,594]⟩,⟨8,326,[66,158,229,287,357,444,519,594,694]⟩,⟨6,16,[66,158,229,287,345,357,444,519,594]⟩,⟨0,286,[66,158,229,287,357,444,486,519,594]⟩,⟨6,269,[66,158,229,287,357,442,444,519,594]⟩,⟨0,18,[66,158,229,287,357,444,480,519,594]⟩,⟨7,17,[66,158,229,287,357,410,444,519,594]⟩,⟨7,290,[66,158,229,287,357,444,519,589,594]⟩,⟨10,177,[66,158,229,287,357,437,444,519,594]⟩,⟨0,20,[66,158,229,287,357,444,519,594,674]⟩]⟩
def row9_103 : State := ⟨[66,85,158,229,287,357,444,519,560,594],[]⟩
def row9_104 : State := ⟨[66,85,141,158,229,287,357,444,519,594],[⟨0,269,[66,153,158,229,287,357,444,519,594]⟩]⟩
def row9_105 : State := ⟨[66,85,158,229,287,357,444,519,563,594],[]⟩
def row9_106 : State := ⟨[10,66,85,158,229,287,357,444,519,594],[⟨10,327,[68,85,158,229,287,357,444,519,594]⟩,⟨0,177,[66,89,158,229,287,357,444,519,594]⟩,⟨0,328,[66,85,158,239,287,357,444,519,594]⟩,⟨0,329,[66,85,158,229,297,357,444,519,594]⟩,⟨0,330,[66,85,158,229,287,364,444,519,594]⟩,⟨0,331,[66,85,158,229,287,357,450,519,594]⟩,⟨2,332,[66,85,158,229,287,357,444,526,594]⟩]⟩
def row9_107 : State := ⟨[66,85,158,229,287,357,444,519,594,674],[]⟩
def row9_108 : State := ⟨[66,85,158,229,279,287,357,444,519,594],[⟨3,333,[66,158,229,281,287,357,444,519,594]⟩]⟩
def row9_109 : State := ⟨[66,85,158,229,287,357,444,519,580,594],[⟨6,289,[66,158,229,313,357,444,519,580,594]⟩,⟨0,2,[41,66,158,229,287,357,444,519,594]⟩,⟨3,290,[66,158,229,287,357,444,519,584,594]⟩]⟩
def row9_110 : State := ⟨[66,85,158,229,287,357,391,444,519,594],[⟨0,334,[66,158,229,287,357,399,444,519,594]⟩]⟩
def row9_111 : State := ⟨[66,85,158,229,287,357,444,519,588,594],[⟨3,13,[66,158,229,287,357,461,519,588,594]⟩,⟨0,58,[66,78,158,229,287,357,444,519,594]⟩,⟨6,15,[66,158,229,287,357,444,519,590,594]⟩]⟩
def row9_112 : State := ⟨[66,85,158,229,287,357,444,511,519,594],[⟨3,335,[66,158,229,287,357,444,515,519,594]⟩]⟩
def row9_113 : State := ⟨[66,85,158,229,287,357,444,519,594,665],[⟨2,325,[66,158,229,287,357,444,560,594,665]⟩,⟨0,325,[66,158,229,287,357,444,519,635,665]⟩,⟨0,326,[66,158,229,287,357,444,519,594,677]⟩]⟩
def row9_114 : State := ⟨[66,158,229,270,278,287,357,444,519,594],[⟨7,336,[66,146,158,229,270,287,357,444,594]⟩,⟨10,336,[66,158,223,229,270,287,357,444,519]⟩]⟩
def row9_115 : State := ⟨[66,158,229,270,287,322,357,444,519,594],[⟨0,56,[66,158,196,229,287,357,444,519,594]⟩,⟨0,337,[66,158,229,287,339,357,444,519,594]⟩]⟩
def row9_116 : State := ⟨[66,108,158,229,287,357,444,519,594],[⟨0,2,[41,66,158,229,287,357,444,519,594]⟩,⟨0,338,[66,113,158,229,287,357,444,519,594]⟩,⟨0,14,[66,85,158,229,287,357,444,519,594]⟩,⟨2,56,[66,158,229,256,287,357,444,519,594]⟩,⟨1,14,[66,103,158,229,287,357,444,519,594]⟩,⟨3,56,[66,158,229,287,313,357,444,519,594]⟩,⟨0,339,[66,158,229,287,357,390,444,519,594]⟩,⟨0,58,[66,78,158,229,287,357,444,519,594]⟩,⟨6,60,[66,158,229,287,357,444,478,519,594]⟩,⟨1,58,[66,102,158,229,287,357,444,519,594]⟩,⟨7,60,[66,158,229,287,357,444,519,560,594]⟩,⟨4,340,[66,158,229,287,357,444,519,594,651]⟩]⟩
def row9_117 : State := ⟨[66,108,158,229,287,332,357,444,519,594],[]⟩
def row9_118 : State := ⟨[66,158,229,287,339,357,444,519,594],[⟨10,51,[66,177,229,287,339,357,444,519,594]⟩,⟨7,51,[66,158,253,287,339,357,444,519,594]⟩,⟨6,51,[66,158,229,310,339,357,444,519,594]⟩,⟨0,2,[41,66,158,229,287,357,444,519,594]⟩,⟨0,62,[66,158,229,287,340,357,444,519,594]⟩,⟨10,341,[66,229,287,339,357,425,444,519,594]⟩,⟨7,341,[66,158,287,339,357,444,494,519,594]⟩,⟨6,341,[66,158,229,339,357,444,519,574,594]⟩,⟨6,342,[34,66,158,229,287,444,519,594]⟩,⟨6,343,[34,66,158,229,287,357,444,519,594]⟩,⟨6,344,[34,66,158,229,287,339,444,519,594]⟩,⟨6,345,[66,158,229,287,357,444,519,594,715]⟩,⟨6,346,[35,66,158,229,339,357,444,519,594]⟩,⟨6,347,[66,158,208,229,287,357,444,519,594]⟩,⟨6,348,[66,158,229,287,357,444,519,594,700]⟩,⟨7,346,[22,66,158,287,339,357,444,519,594]⟩,⟨7,347,[66,158,229,282,287,357,444,519,594]⟩,⟨7,348,[66,158,229,287,357,444,519,594,701]⟩,⟨10,346,[10,66,229,287,339,357,444,519,594]⟩,⟨10,347,[66,158,229,287,330,357,444,519,594]⟩,⟨10,348,[66,158,229,287,357,444,519,594,702]⟩]⟩
def row9_119 : State := ⟨[66,158,229,270,287,339,357,444,519,594],[⟨6,349,[34,66,158,229,270,287,444,519,594]⟩]⟩
def row9_120 : State := ⟨[54,66,158,229,270,287,357,444,519,594],[⟨10,350,[66,174,229,270,287,357,444,519,594]⟩,⟨7,350,[66,158,251,270,287,357,444,519,594]⟩,⟨0,351,[66,158,229,277,287,357,444,519,594]⟩]⟩
def row9_121 : State := ⟨[66,158,229,270,287,357,380,444,519,594],[⟨10,37,[177,229,270,287,357,380,444,519,594]⟩,⟨7,37,[158,253,270,287,357,380,444,519,594]⟩,⟨6,63,[158,229,278,287,357,380,444,519,594]⟩,⟨10,42,[66,229,270,287,357,428,444,519,594]⟩,⟨7,42,[66,158,270,287,357,444,496,519,594]⟩,⟨0,352,[51,66,158,229,287,357,444,519,594]⟩,⟨0,65,[66,158,229,287,357,444,508,519,594]⟩]⟩
def row9_122 : State := ⟨[0,66,158,229,287,357,444,519,588,594],[⟨6,353,[66,159,229,287,357,444,519,588,594]⟩,⟨7,354,[66,158,230,287,357,444,519,588,594]⟩,⟨6,355,[66,158,229,288,357,444,519,588,594]⟩,⟨0,356,[66,158,229,287,358,444,519,588,594]⟩,⟨2,357,[66,158,229,287,357,444,520,588,594]⟩,⟨6,358,[66,158,229,287,357,444,519,588,595]⟩]⟩
def row9_123 : State := ⟨[66,158,229,287,357,444,519,629,656],[⟨6,213,[158,177,229,287,357,444,519,629,656]⟩,⟨1,359,[66,158,229,287,357,468,519,629,656]⟩,⟨3,360,[66,158,229,287,357,480,519,629,656]⟩,⟨3,361,[35,66,158,229,287,357,519,629,656]⟩,⟨1,39,[66,158,229,287,357,465,519,629,656]⟩,⟨0,362,[48,66,158,229,287,357,444,519,656]⟩,⟨1,180,[66,158,229,287,357,444,519,649,656]⟩,⟨0,42,[66,158,229,287,357,444,519,633,656]⟩,⟨0,341,[66,158,229,287,357,444,519,629,671]⟩,⟨0,363,[66,158,229,287,357,444,519,595]⟩,⟨0,357,[66,158,229,287,357,444,519,595,656]⟩,⟨0,364,[66,158,229,287,357,444,519,595,629]⟩]⟩
def row9_124 : State := ⟨[66,158,229,270,287,357,425,444,519,594],[⟨0,365,[66,158,165,229,287,357,444,519,594]⟩,⟨0,366,[66,158,229,287,357,444,507,519,594]⟩]⟩
def row9_125 : State := ⟨[2,66,158,229,287,357,444,519,594],[⟨10,367,[66,161,229,287,357,444,519,594]⟩,⟨0,368,[66,158,161,229,287,357,444,519,594]⟩,⟨0,369,[2,66,161,229,287,357,444,519,594]⟩,⟨0,205,[2,158,177,229,287,357,444,519,594]⟩,⟨7,370,[66,158,232,287,357,444,519,594]⟩,⟨2,371,[66,158,229,232,287,357,444,519,594]⟩,⟨1,372,[2,66,158,232,287,357,444,519,594]⟩,⟨6,370,[66,158,229,290,357,444,519,594]⟩,⟨3,371,[66,158,229,287,290,357,444,519,594]⟩,⟨0,372,[2,66,158,229,290,357,444,519,594]⟩,⟨0,373,[66,158,229,287,360,444,519,594]⟩,⟨6,374,[66,158,229,287,357,360,444,519,594]⟩,⟨0,375,[2,66,158,229,287,360,444,519,594]⟩,⟨0,121,[0,66,158,229,287,357,444,519,594]⟩,⟨3,363,[66,158,229,287,357,445,519,594]⟩,⟨6,365,[66,158,229,287,357,444,445,519,594]⟩,⟨1,376,[2,66,158,229,287,357,445,519,594]⟩,⟨1,377,[2,35,66,158,229,287,357,519,594]⟩,⟨1,47,[2,66,158,229,287,357,465,519,594]⟩,⟨1,121,[1,66,158,229,287,357,444,519,594]⟩,⟨2,363,[66,158,229,287,357,444,520,594]⟩,⟨7,365,[66,158,229,287,357,444,519,520,594]⟩,⟨0,376,[2,66,158,229,287,357,444,520,594]⟩,⟨0,377,[2,22,66,158,229,287,357,444,594]⟩,⟨0,47,[2,66,158,229,287,357,444,549,594]⟩,⟨0,378,[66,158,229,287,357,444,519,597]⟩,⟨10,379,[66,158,229,287,357,444,519,594,597]⟩,⟨0,380,[2,66,158,229,287,357,444,519,597]⟩,⟨4,381,[2,3,158,229,287,357,444,519,594]⟩]⟩
def row9_126 : State := ⟨[2,66,158,229,287,357,444,519,588,594],[⟨6,382,[66,161,229,287,357,444,519,588,594]⟩,⟨7,383,[66,158,232,287,357,444,519,588,594]⟩,⟨6,383,[66,158,229,290,357,444,519,588,594]⟩,⟨0,384,[66,158,229,287,360,444,519,588,594]⟩,⟨3,357,[66,158,229,287,357,445,519,588,594]⟩,⟨2,357,[66,158,229,287,357,444,520,588,594]⟩,⟨6,385,[66,158,229,287,357,444,519,588,597]⟩]⟩
def row9_127 : State := ⟨[66,158,229,287,357,444,507,519,594],[⟨0,4,[64,66,158,229,287,357,444,519,594]⟩,⟨0,65,[66,158,229,287,357,444,508,519,594]⟩,⟨3,386,[66,158,190,229,287,357,444,519,594]⟩,⟨6,345,[66,158,229,287,357,444,519,594,715]⟩,⟨6,269,[66,158,229,287,357,442,444,519,594]⟩,⟨0,179,[66,158,229,287,357,444,510,519,594]⟩,⟨7,387,[66,158,229,287,357,412,444,519,594]⟩,⟨9,184,[66,158,229,287,357,444,519,594,709]⟩,⟨10,387,[66,158,229,287,357,444,491,519,594]⟩,⟨11,184,[66,158,229,287,357,444,519,594,710]⟩]⟩
def row9_128 : State := ⟨[66,158,229,270,287,357,444,507,519,594],[]⟩
def row9_129 : State := ⟨[0,66,158,229,287,357,444,519,594,665],[⟨11,388,[66,159,229,287,357,444,519,594,665]⟩,⟨9,388,[66,158,230,287,357,444,519,594,665]⟩,⟨9,389,[66,158,229,288,357,444,519,594,665]⟩,⟨0,390,[66,158,229,287,358,444,519,594,665]⟩,⟨2,391,[66,158,229,287,357,444,520,594,665]⟩,⟨0,391,[66,158,229,287,357,444,519,595,665]⟩,⟨9,392,[66,158,229,287,357,444,519,594,666]⟩,⟨0,381,[0,5,158,229,287,357,444,519,594]⟩]⟩
def row9_130 : State := ⟨[66,158,229,270,287,357,444,519,574,594],[⟨6,341,[66,158,229,339,357,444,519,574,594]⟩,⟨3,393,[66,158,189,229,287,357,444,519,594]⟩,⟨6,345,[66,158,229,287,357,444,519,594,715]⟩]⟩
def row9_131 : State := ⟨[0,66,158,229,270,287,357,444,519,594],[⟨10,394,[66,159,229,270,287,357,444,519,594]⟩,⟨7,394,[66,158,230,270,287,357,444,519,594]⟩,⟨0,395,[66,158,229,271,287,357,444,519,594]⟩,⟨0,396,[66,158,229,270,288,357,444,519,594]⟩,⟨0,397,[66,158,229,270,287,358,444,519,594]⟩,⟨2,398,[66,158,229,270,287,357,444,520,594]⟩,⟨0,398,[66,158,229,270,287,357,444,519,595]⟩]⟩
def row9_132 : State := ⟨[66,158,229,270,287,357,444,468,519,594],[⟨0,399,[66,158,210,229,287,357,444,519,594]⟩,⟨0,67,[66,158,229,287,357,444,509,519,594]⟩]⟩
def row9_133 : State := ⟨[66,118,158,229,270,287,357,444,519,594],[]⟩
def row9_134 : State := ⟨[66,158,229,270,287,357,444,480,519,594],[⟨0,312,[66,158,214,229,287,357,444,519,594]⟩,⟨0,400,[66,158,229,287,357,444,505,519,594]⟩]⟩
def row9_135 : State := ⟨[66,148,158,229,287,357,444,519,594],[⟨0,401,[66,158,173,229,287,357,444,519,594]⟩,⟨0,58,[66,78,158,229,287,357,444,519,594]⟩,⟨2,402,[66,158,229,269,287,357,444,519,594]⟩,⟨1,58,[66,102,158,229,287,357,444,519,594]⟩,⟨3,402,[66,158,229,287,319,357,444,519,594]⟩,⟨6,403,[66,158,229,287,357,421,444,519,594]⟩,⟨0,167,[66,118,158,229,287,357,444,519,594]⟩,⟨6,312,[66,158,229,287,357,444,473,519,594]⟩,⟨1,167,[66,141,158,229,287,357,444,519,594]⟩,⟨7,312,[66,158,229,287,357,444,519,557,594]⟩,⟨10,404,[66,158,229,287,357,444,519,594,670]⟩]⟩
def row9_136 : State := ⟨[66,148,158,229,287,357,444,519,588,594],[]⟩
def row9_137 : State := ⟨[66,158,229,287,357,444,505,519,594],[⟨10,49,[66,177,229,287,357,444,505,519,594]⟩,⟨7,49,[66,158,253,287,357,444,505,519,594]⟩,⟨3,162,[66,158,229,287,357,465,505,519,594]⟩,⟨0,16,[42,66,158,229,287,357,444,519,594]⟩,⟨0,67,[66,158,229,287,357,444,509,519,594]⟩,⟨3,405,[66,158,191,229,287,357,444,519,594]⟩,⟨6,348,[66,158,229,287,357,444,519,594,700]⟩,⟨6,406,[66,158,229,287,349,357,444,519,594]⟩,⟨0,179,[66,158,229,287,357,444,510,519,594]⟩,⟨7,387,[66,158,229,287,357,412,444,519,594]⟩,⟨0,407,[66,158,229,287,357,444,519,594,689]⟩,⟨10,387,[66,158,229,287,357,444,491,519,594]⟩,⟨2,407,[66,158,229,287,357,444,519,594,690]⟩]⟩
def row9_138 : State := ⟨[66,158,229,270,287,357,444,505,519,594],[]⟩
def row9_139 : State := ⟨[10,66,158,229,287,332,357,444,519,594],[⟨10,408,[68,158,229,287,332,357,444,519,594]⟩,⟨9,409,[66,158,239,287,332,357,444,519,594]⟩,⟨8,409,[66,158,229,297,332,357,444,519,594]⟩,⟨4,410,[66,158,229,287,334,357,444,519,594]⟩,⟨10,346,[10,66,229,287,339,357,444,519,594]⟩,⟨4,411,[66,158,229,287,332,364,444,519,594]⟩,⟨5,412,[66,158,229,287,332,357,450,519,594]⟩,⟨4,412,[66,158,229,287,332,357,444,526,594]⟩]⟩
def row9_140 : State := ⟨[66,158,229,270,287,357,444,519,594,691],[⟨0,413,[66,158,229,264,287,357,444,519,594]⟩,⟨6,348,[66,158,229,287,357,444,519,594,700]⟩]⟩
def row9_141 : State := ⟨[0,66,158,229,287,322,357,444,519,594],[⟨10,414,[66,159,229,287,322,357,444,519,594]⟩,⟨1,415,[66,158,230,287,322,357,444,519,594]⟩,⟨6,416,[66,158,229,288,322,357,444,519,594]⟩,⟨1,417,[66,158,229,287,323,357,444,519,594]⟩,⟨1,418,[66,158,229,287,322,358,444,519,594]⟩,⟨0,419,[0,35,66,158,229,322,357,519,594]⟩,⟨0,420,[0,66,127,158,229,287,357,519,594]⟩,⟨1,421,[66,158,229,287,322,357,444,520,594]⟩,⟨1,422,[66,158,229,287,322,357,444,519,595]⟩]⟩
def row9_142 : State := ⟨[66,158,229,270,287,357,444,519,553,594],[⟨7,38,[158,253,270,287,357,444,519,553,594]⟩,⟨11,46,[66,229,270,287,357,444,519,569,594]⟩,⟨2,423,[52,66,158,270,287,357,444,519,594]⟩,⟨1,424,[66,147,158,229,287,357,444,519,594]⟩,⟨0,72,[66,158,229,287,357,444,519,594,706]⟩]⟩
def row9_143 : State := ⟨[66,118,158,229,287,322,357,444,519,594],[]⟩
def row9_144 : State := ⟨[66,158,229,287,357,444,519,637,665],[⟨1,157,[66,158,253,287,357,444,519,637,665]⟩,⟨1,425,[66,158,270,287,357,444,519,637,665]⟩,⟨0,360,[66,158,229,287,357,444,553,637,665]⟩,⟨0,426,[66,158,229,287,357,444,563,637,665]⟩,⟨2,427,[22,66,158,229,287,357,444,637,665]⟩,⟨0,40,[66,158,229,287,357,444,549,637,665]⟩,⟨0,180,[66,158,229,287,357,444,519,641,665]⟩,⟨0,428,[66,89,158,229,287,357,444,519,665]⟩,⟨0,46,[66,158,229,287,357,444,519,643,665]⟩,⟨9,429,[66,158,229,287,357,444,513,637,665]⟩,⟨0,68,[66,158,229,287,357,444,519,637,669]⟩,⟨0,430,[66,158,229,287,357,444,519,604]⟩,⟨0,431,[66,158,229,287,357,444,519,604,665]⟩,⟨0,432,[66,158,229,287,357,444,519,604,637]⟩]⟩
def row9_145 : State := ⟨[66,158,229,270,287,357,444,519,563,594],[⟨2,433,[66,93,158,270,287,357,444,519,594]⟩,⟨0,434,[66,158,166,229,287,357,444,519,594]⟩,⟨9,435,[66,158,229,287,357,444,519,594,684]⟩]⟩
def row9_146 : State := ⟨[10,66,158,229,287,357,444,519,656],[⟨6,436,[68,158,229,287,357,444,519,656]⟩,⟨0,437,[66,68,158,229,287,357,444,519,656]⟩,⟨10,438,[10,68,158,229,287,357,444,519,656]⟩,⟨1,439,[10,66,158,239,287,357,444,519,656]⟩,⟨0,440,[10,66,229,270,287,357,444,519,656]⟩,⟨0,441,[66,158,229,297,357,444,519,656]⟩,⟨3,442,[66,158,229,287,297,357,444,519,656]⟩,⟨0,443,[10,66,158,229,297,357,444,519,656]⟩,⟨1,444,[10,66,229,287,322,357,444,519,656]⟩,⟨0,445,[66,158,229,287,364,444,519,656]⟩,⟨10,446,[66,158,229,287,357,364,444,519,656]⟩,⟨0,447,[10,66,158,229,287,364,444,519,656]⟩,⟨6,419,[7,10,66,229,287,357,444,519,656]⟩,⟨1,448,[10,66,158,229,287,357,450,519,656]⟩,⟨1,361,[10,66,158,229,287,357,468,519,656]⟩,⟨1,427,[10,66,158,229,287,357,480,519,656]⟩,⟨1,449,[10,35,66,158,229,287,357,519,656]⟩,⟨1,41,[10,66,158,229,287,357,465,519,656]⟩,⟨0,450,[10,66,158,229,287,357,444,526,656]⟩,⟨2,377,[4,10,66,158,229,287,357,444,519]⟩,⟨0,346,[10,66,158,229,287,357,444,519,671]⟩]⟩
def row9_147 : State := ⟨[10,66,158,229,270,287,357,444,519,594],[⟨10,451,[68,158,229,270,287,357,444,519,594]⟩,⟨9,431,[66,158,239,270,287,357,444,519,594]⟩,⟨0,452,[66,158,229,270,297,357,444,519,594]⟩,⟨0,453,[66,158,229,270,287,364,444,519,594]⟩,⟨0,454,[66,158,229,270,287,357,450,519,594]⟩,⟨2,455,[66,158,229,270,287,357,444,526,594]⟩]⟩
def row9_148 : State := ⟨[66,158,229,270,287,357,444,519,594,674],[⟨0,402,[66,158,229,265,287,357,444,519,594]⟩,⟨11,435,[66,158,229,287,357,444,519,594,685]⟩]⟩
def row9_149 : State := ⟨[66,123,158,229,287,357,444,519,594],[⟨0,456,[66,139,158,229,287,357,444,519,594]⟩,⟨0,58,[66,78,158,229,287,357,444,519,594]⟩,⟨2,457,[66,158,229,260,287,357,444,519,594]⟩,⟨0,458,[66,123,229,270,287,357,444,519,594]⟩,⟨3,459,[66,158,229,287,321,357,444,519,594]⟩,⟨0,460,[66,123,229,287,322,357,444,519,594]⟩,⟨6,461,[66,158,229,287,357,405,444,519,594]⟩,⟨6,420,[7,66,123,229,287,357,444,519,594]⟩,⟨0,167,[66,118,158,229,287,357,444,519,594]⟩,⟨3,430,[66,158,229,287,357,450,519,594]⟩,⟨8,434,[66,158,229,287,357,444,450,519,594]⟩,⟨0,462,[66,123,158,229,287,357,450,519,594]⟩,⟨6,58,[66,114,158,229,287,357,444,519,594]⟩,⟨7,463,[66,158,229,287,357,444,519,559,594]⟩,⟨0,244,[10,66,158,229,287,357,444,519,594]⟩,⟨10,402,[66,158,229,287,357,444,519,594,654]⟩]⟩
def row9_150 : State := ⟨[66,123,158,229,287,357,444,519,594,656],[⟨3,431,[66,158,229,287,357,450,519,594,656]⟩,⟨0,464,[10,66,158,229,287,357,444,519,656]⟩]⟩
def row9_151 : State := ⟨[66,158,229,287,357,444,519,594,680],[⟨11,161,[66,177,229,287,357,444,519,594,680]⟩,⟨2,50,[66,158,229,287,357,444,549,594,680]⟩,⟨0,48,[66,158,229,287,357,444,519,625,680]⟩,⟨3,406,[45,66,158,229,287,357,444,519,594]⟩,⟨0,184,[66,158,229,287,357,444,519,594,705]⟩,⟨2,465,[66,158,228,229,287,357,444,519,594]⟩,⟨0,466,[66,158,229,287,357,444,519,594,686]⟩,⟨3,269,[66,158,229,286,287,357,444,519,594]⟩,⟨3,407,[66,158,229,287,357,444,519,594,699]⟩,⟨6,16,[66,158,229,287,345,357,444,519,594]⟩,⟨9,72,[66,158,229,287,357,444,519,594,711]⟩,⟨6,269,[66,158,229,287,357,442,444,519,594]⟩,⟨0,348,[66,158,229,287,357,444,519,594,688]⟩]⟩
def row9_152 : State := ⟨[66,158,229,270,287,357,444,519,594,684],[]⟩
def row9_153 : State := ⟨[66,118,158,229,287,332,357,444,519,594],[⟨7,467,[66,158,258,287,332,357,444,519,594]⟩,⟨0,58,[66,78,158,229,287,357,444,519,594]⟩,⟨4,468,[66,158,229,287,338,357,444,519,594]⟩]⟩
def row9_154 : State := ⟨[66,158,229,270,287,357,444,519,580,594],[⟨4,469,[66,158,185,270,287,357,444,519,594]⟩,⟨1,470,[66,158,195,229,287,357,444,519,594]⟩,⟨7,348,[66,158,229,287,357,444,519,594,701]⟩]⟩
def row9_155 : State := ⟨[66,158,229,270,287,357,444,519,588,594],[⟨2,440,[22,66,158,270,287,357,444,588,594]⟩,⟨7,458,[66,145,158,229,287,357,444,588,594]⟩,⟨2,458,[66,158,204,270,287,357,444,519,594]⟩,⟨0,471,[66,158,213,229,287,357,444,519,594]⟩,⟨0,407,[66,158,229,287,357,444,519,594,689]⟩]⟩
def row9_156 : State := ⟨[66,158,229,270,287,357,444,519,594,665],[⟨4,425,[66,229,270,287,357,444,563,594,665]⟩,⟨2,444,[22,66,158,270,287,357,444,594,665]⟩,⟨7,460,[66,145,158,229,287,357,444,594,665]⟩,⟨0,444,[10,66,229,270,287,357,444,519,665]⟩,⟨1,425,[66,158,270,287,357,444,519,637,665]⟩,⟨10,460,[66,158,222,229,287,357,444,519,665]⟩,⟨1,460,[66,144,229,270,287,357,444,519,594]⟩,⟨4,460,[66,158,225,270,287,357,444,519,594]⟩,⟨0,472,[66,158,229,263,287,357,444,519,594]⟩,⟨0,466,[66,158,229,287,357,444,519,594,686]⟩]⟩
def row9_157 : State := ⟨[66,158,174,229,287,357,444,519,594],[⟨0,4,[64,66,158,229,287,357,444,519,594]⟩,⟨0,54,[66,158,177,229,287,357,444,519,594]⟩,⟨10,350,[66,174,229,270,287,357,444,519,594]⟩,⟨0,14,[66,85,158,229,287,357,444,519,594]⟩,⟨0,351,[66,158,229,277,287,357,444,519,594]⟩,⟨11,350,[66,174,229,287,322,357,444,519,594]⟩,⟨1,14,[66,103,158,229,287,357,444,519,594]⟩,⟨1,351,[66,158,229,287,328,357,444,519,594]⟩,⟨6,473,[7,66,174,229,287,357,444,519,594]⟩,⟨6,474,[58,66,158,229,287,357,444,519,594]⟩,⟨0,7,[66,158,229,287,357,425,444,519,594]⟩,⟨10,475,[66,174,229,287,357,444,480,519,594]⟩,⟨0,167,[66,118,158,229,287,357,444,519,594]⟩,⟨0,476,[66,158,229,287,357,444,487,519,594]⟩,⟨11,475,[66,174,229,287,357,444,519,563,594]⟩,⟨1,167,[66,141,158,229,287,357,444,519,594]⟩,⟨1,476,[66,158,229,287,357,444,519,568,594]⟩,⟨10,477,[66,174,229,287,357,444,519,594,674]⟩,⟨0,244,[10,66,158,229,287,357,444,519,594]⟩,⟨0,478,[66,158,229,287,357,444,519,594,703]⟩]⟩
def row9_158 : State := ⟨[54,66,158,174,229,287,357,444,519,594],[]⟩
def row9_159 : State := ⟨[54,66,158,229,287,357,380,444,519,594],[]⟩
def row9_160 : State := ⟨[0,54,66,158,229,287,357,444,519,594],[⟨0,474,[55,66,158,229,287,357,444,519,594]⟩,⟨10,479,[54,66,159,229,287,357,444,519,594]⟩,⟨7,479,[54,66,158,230,287,357,444,519,594]⟩,⟨6,480,[54,66,158,229,288,357,444,519,594]⟩,⟨0,481,[54,66,158,229,287,358,444,519,594]⟩,⟨0,473,[0,66,158,229,287,357,464,519,594]⟩,⟨2,482,[54,66,158,229,287,357,444,520,594]⟩,⟨0,482,[54,66,158,229,287,357,444,519,595]⟩]⟩
def row9_161 : State := ⟨[54,66,158,229,287,357,425,444,519,594],[]⟩
def row9_162 : State := ⟨[54,66,118,158,229,287,357,444,519,594],[⟨0,483,[66,135,158,229,287,357,444,519,594]⟩]⟩
def row9_163 : State := ⟨[54,66,158,229,287,357,444,480,519,594],[⟨10,475,[66,174,229,287,357,444,480,519,594]⟩,⟨3,475,[66,158,229,287,357,464,480,519,594]⟩,⟨0,476,[66,158,229,287,357,444,487,519,594]⟩]⟩
def row9_164 : State := ⟨[10,54,66,158,229,287,357,444,519,594],[⟨0,484,[59,66,158,229,287,357,444,519,594]⟩,⟨10,485,[54,68,158,229,287,357,444,519,594]⟩,⟨9,486,[54,66,158,239,287,357,444,519,594]⟩,⟨8,486,[54,66,158,229,297,357,444,519,594]⟩,⟨0,485,[54,66,158,229,287,364,444,519,594]⟩,⟨3,486,[54,66,158,229,287,357,450,519,594]⟩,⟨2,486,[54,66,158,229,287,357,444,526,594]⟩]⟩
def row9_165 : State := ⟨[54,66,158,229,287,357,444,519,594,674],[⟨10,477,[66,174,229,287,357,444,519,594,674]⟩,⟨0,477,[66,158,229,287,357,444,519,623,674]⟩,⟨0,478,[66,158,229,287,357,444,519,594,703]⟩]⟩
def row9_166 : State := ⟨[0,66,158,229,287,357,380,444,519,594],[⟨10,487,[66,159,229,287,357,380,444,519,594]⟩,⟨7,487,[66,158,230,287,357,380,444,519,594]⟩,⟨6,488,[66,158,229,288,357,380,444,519,594]⟩,⟨0,92,[66,158,229,287,358,380,444,519,594]⟩,⟨0,85,[0,66,158,229,287,380,465,519,594]⟩,⟨2,489,[66,158,229,287,357,380,444,520,594]⟩,⟨0,489,[66,158,229,287,357,380,444,519,595]⟩]⟩
def row9_167 : State := ⟨[66,158,229,287,357,380,425,444,519,594],[⟨6,280,[66,158,229,287,357,378,444,519,594]⟩,⟨0,95,[66,158,229,287,357,428,444,519,594]⟩]⟩
def row9_168 : State := ⟨[47,66,158,229,287,357,444,519,594],[⟨0,2,[41,66,158,229,287,357,444,519,594]⟩,⟨6,90,[67,158,229,287,357,444,519,594]⟩,⟨0,94,[66,67,158,229,287,357,444,519,594]⟩,⟨0,490,[47,67,158,229,287,357,444,519,594]⟩,⟨0,93,[47,66,177,229,287,357,444,519,594]⟩,⟨7,363,[66,158,236,287,357,444,519,594]⟩,⟨2,365,[66,158,229,236,287,357,444,519,594]⟩,⟨1,491,[47,66,158,236,287,357,444,519,594]⟩,⟨6,363,[66,158,229,294,357,444,519,594]⟩,⟨3,365,[66,158,229,287,294,357,444,519,594]⟩,⟨0,491,[47,66,158,229,294,357,444,519,594]⟩,⟨6,121,[7,66,158,229,287,357,444,519,594]⟩,⟨6,280,[66,158,229,287,357,378,444,519,594]⟩,⟨6,492,[66,158,229,287,357,444,462,519,594]⟩,⟨7,492,[66,158,229,287,357,444,519,545,594]⟩,⟨10,493,[66,158,229,287,357,444,519,594,622]⟩,⟨0,494,[10,47,66,229,287,357,444,519,594]⟩]⟩
def row9_169 : State := ⟨[47,66,158,229,287,357,380,444,519,594],[⟨6,92,[67,158,229,287,357,380,444,519,594]⟩,⟨0,88,[47,177,229,287,357,380,444,519,594]⟩,⟨7,489,[66,158,236,287,357,380,444,519,594]⟩,⟨6,489,[66,158,229,294,357,380,444,519,594]⟩]⟩
def row9_170 : State := ⟨[66,158,229,287,357,380,428,444,519,594],[⟨10,495,[66,158,229,287,347,357,380,444,519]⟩]⟩
def row9_171 : State := ⟨[66,118,158,229,287,357,380,444,519,594],[⟨6,496,[137,158,229,287,357,380,444,519,594]⟩,⟨0,496,[66,158,229,287,380,403,444,519,594]⟩,⟨0,497,[66,158,229,287,357,409,444,519,594]⟩]⟩
def row9_172 : State := ⟨[66,158,229,287,357,380,444,480,519,594],[⟨10,86,[177,229,287,357,380,444,480,519,594]⟩,⟨3,86,[66,158,229,287,380,465,480,519,594]⟩,⟨0,498,[66,158,229,287,353,357,444,519,594]⟩,⟨0,127,[66,158,229,287,357,444,490,519,594]⟩]⟩
def row9_173 : State := ⟨[10,66,158,229,287,357,380,444,519,594],[⟨10,499,[68,158,229,287,357,380,444,519,594]⟩,⟨9,500,[66,158,239,287,357,380,444,519,594]⟩,⟨8,500,[66,158,229,297,357,380,444,519,594]⟩,⟨0,499,[66,158,229,287,364,380,444,519,594]⟩,⟨0,501,[66,158,229,287,357,382,444,519,594]⟩,⟨0,494,[10,47,66,229,287,357,444,519,594]⟩,⟨3,500,[66,158,229,287,357,380,450,519,594]⟩,⟨2,500,[66,158,229,287,357,380,444,526,594]⟩,⟨10,494,[10,66,158,229,287,344,357,444,519]⟩]⟩
def row9_174 : State := ⟨[66,158,229,287,357,380,444,519,594,674],[⟨10,87,[177,229,287,357,380,444,519,594,674]⟩,⟨0,87,[66,158,229,287,380,444,519,625,674]⟩,⟨0,502,[66,158,229,287,354,357,444,519,594]⟩,⟨0,131,[66,158,229,287,357,444,519,594,708]⟩]⟩
def row9_175 : State := ⟨[66,158,229,287,357,444,519,600],[⟨0,8,[41,66,158,229,287,357,444,519,600]⟩,⟨0,135,[66,158,177,229,287,357,444,519,600]⟩,⟨6,97,[66,158,253,287,357,444,519,600]⟩,⟨2,111,[66,158,229,253,287,357,444,519,600]⟩,⟨0,296,[66,85,158,229,287,357,444,519,600]⟩,⟨0,354,[66,158,229,270,287,357,444,519,600]⟩,⟨3,134,[66,158,229,287,310,357,444,519,600]⟩,⟨1,301,[66,103,158,229,287,357,444,519,600]⟩,⟨1,388,[66,158,229,287,322,357,444,519,600]⟩,⟨4,295,[66,158,183,229,287,357,444,519,600]⟩,⟨4,353,[66,158,229,287,332,357,444,519,600]⟩,⟨0,479,[54,66,158,229,287,357,444,519,600]⟩,⟨0,487,[66,158,229,287,357,380,444,519,600]⟩,⟨6,503,[7,66,158,229,287,357,444,519,600]⟩,⟨0,504,[66,158,229,287,357,425,444,519,600]⟩,⟨8,505,[20,66,158,229,287,357,444,519,600]⟩,⟨2,506,[66,158,229,287,357,444,494,519,600]⟩,⟨9,507,[32,66,158,229,287,357,444,519,600]⟩,⟨3,508,[66,158,229,287,357,444,519,574,600]⟩,⟨0,509,[0,66,158,229,287,357,444,519,600]⟩,⟨0,510,[66,158,229,287,357,444,468,519,600]⟩,⟨0,511,[66,118,158,229,287,357,444,519,600]⟩,⟨0,512,[66,158,229,287,357,444,480,519,600]⟩,⟨2,513,[66,158,202,229,287,357,444,519,600]⟩,⟨2,514,[66,158,229,287,357,444,498,519,600]⟩,⟨3,515,[35,66,158,229,287,357,444,519,600]⟩,⟨0,516,[66,158,229,287,357,444,519,600,691]⟩,⟨6,21,[66,158,229,287,341,357,444,519,600]⟩,⟨6,146,[66,158,229,287,357,444,465,519,600]⟩,⟨1,517,[1,66,158,229,287,357,444,519,600]⟩,⟨1,518,[66,158,229,287,357,444,519,553,600]⟩,⟨1,519,[66,141,158,229,287,357,444,519,600]⟩,⟨1,520,[66,158,229,287,357,444,519,563,600]⟩,⟨2,521,[22,66,158,229,287,357,444,519,600]⟩,⟨0,522,[66,158,229,287,357,444,519,600,681]⟩,⟨3,523,[66,158,229,279,287,357,444,519,600]⟩,⟨3,524,[66,158,229,287,357,444,519,580,600]⟩,⟨7,208,[66,158,229,287,357,444,519,549,600]⟩,⟨6,320,[66,158,229,287,357,391,444,519,600]⟩,⟨6,415,[66,158,229,287,357,444,519,588,600]⟩,⟨4,525,[3,66,158,229,287,357,444,519,600]⟩,⟨0,526,[66,158,229,287,357,444,519,600,631]⟩,⟨0,527,[10,66,158,229,287,357,444,519,600]⟩,⟨0,528,[66,158,229,287,357,444,519,600,676]⟩,⟨10,168,[66,158,224,229,287,357,444,519,600]⟩,⟨0,164,[66,158,229,287,357,444,519,600,637]⟩,⟨5,529,[66,158,229,284,287,357,444,519,600]⟩,⟨0,530,[66,158,229,287,357,444,519,600,647]⟩,⟨8,531,[66,158,229,287,348,357,444,519,600]⟩,⟨0,145,[66,158,229,287,357,444,519,600,625]⟩,⟨8,307,[66,158,229,287,357,434,444,519,600]⟩,⟨0,532,[66,158,229,287,357,444,519,600,658]⟩,⟨9,319,[66,158,229,287,357,444,511,519,600]⟩,⟨0,533,[66,158,229,287,357,444,519,600,668]⟩]⟩
def row9_176 : State := ⟨[66,158,159,229,287,357,444,519,594],[⟨4,21,[41,66,159,229,287,357,444,519,594]⟩,⟨10,145,[66,159,177,229,287,357,444,519,594]⟩,⟨0,16,[42,66,158,229,287,357,444,519,594]⟩,⟨0,54,[66,158,177,229,287,357,444,519,594]⟩,⟨2,307,[66,85,159,229,287,357,444,519,594]⟩,⟨10,394,[66,159,229,270,287,357,444,519,594]⟩,⟨0,14,[66,85,158,229,287,357,444,519,594]⟩,⟨0,395,[66,158,229,271,287,357,444,519,594]⟩,⟨3,319,[66,103,159,229,287,357,444,519,594]⟩,⟨10,414,[66,159,229,287,322,357,444,519,594]⟩,⟨1,14,[66,103,158,229,287,357,444,519,594]⟩,⟨1,417,[66,158,229,287,323,357,444,519,594]⟩,⟨6,525,[7,66,159,229,287,357,444,519,594]⟩,⟨10,534,[66,159,229,287,357,425,444,519,594]⟩,⟨6,121,[7,66,158,229,287,357,444,519,594]⟩,⟨0,535,[66,158,229,287,357,426,444,519,594]⟩,⟨6,536,[66,118,159,229,287,357,444,519,594]⟩,⟨10,164,[66,159,229,287,357,444,480,519,594]⟩,⟨0,537,[66,119,158,229,287,357,444,519,594]⟩,⟨0,18,[66,158,229,287,357,444,480,519,594]⟩,⟨0,98,[66,158,159,229,287,357,465,519,594]⟩,⟨7,529,[66,141,159,229,287,357,444,519,594]⟩,⟨10,538,[66,159,229,287,357,444,519,563,594]⟩,⟨1,167,[66,141,158,229,287,357,444,519,594]⟩,⟨1,539,[66,158,229,287,357,444,519,564,594]⟩,⟨10,527,[10,66,159,229,287,357,444,519,594]⟩,⟨10,540,[66,159,229,287,357,444,519,594,674]⟩,⟨0,244,[10,66,158,229,287,357,444,519,594]⟩,⟨0,541,[66,158,229,287,357,444,519,594,675]⟩]⟩
def row9_177 : State := ⟨[0,66,158,230,287,357,444,519,594],[⟨9,542,[66,159,230,287,357,444,519,594]⟩,⟨0,543,[66,158,159,230,287,357,444,519,594]⟩,⟨0,544,[0,66,159,230,287,357,444,519,594]⟩,⟨6,545,[66,158,230,288,357,444,519,594]⟩,⟨3,546,[66,158,230,287,288,357,444,519,594]⟩,⟨0,547,[0,66,158,230,288,357,444,519,594]⟩,⟨1,548,[66,158,230,287,358,444,519,594]⟩,⟨6,549,[66,158,230,287,357,358,444,519,594]⟩,⟨0,550,[0,66,158,230,287,358,444,519,594]⟩,⟨0,551,[0,35,66,158,230,287,357,519,594]⟩,⟨0,99,[0,66,158,230,287,357,465,519,594]⟩,⟨1,552,[66,158,230,287,357,444,520,594]⟩,⟨7,553,[66,158,230,287,357,444,519,520,594]⟩,⟨0,554,[0,66,158,230,287,357,444,520,594]⟩,⟨1,555,[66,158,230,287,357,444,519,595]⟩,⟨10,556,[66,158,230,287,357,444,519,594,595]⟩,⟨0,557,[0,66,158,230,287,357,444,519,595]⟩]⟩
def row9_178 : State := ⟨[0,66,158,159,229,287,357,444,519,594],[⟨0,543,[66,158,159,230,287,357,444,519,594]⟩,⟨0,558,[66,158,159,229,288,357,444,519,594]⟩,⟨0,559,[66,158,159,229,287,358,444,519,594]⟩,⟨0,560,[66,158,159,229,287,357,444,520,594]⟩,⟨0,561,[66,158,159,229,287,357,444,519,595]⟩]⟩
def row9_179 : State := ⟨[66,158,229,287,357,444,519,598],[⟨0,9,[41,66,158,229,287,357,444,519,598]⟩,⟨6,100,[66,177,229,287,357,444,519,598]⟩,⟨0,112,[66,158,177,229,287,357,444,519,598]⟩,⟨2,136,[66,158,229,253,287,357,444,519,598]⟩,⟨0,297,[66,85,158,229,287,357,444,519,598]⟩,⟨0,355,[66,158,229,270,287,357,444,519,598]⟩,⟨3,136,[66,158,229,287,310,357,444,519,598]⟩,⟨1,297,[66,103,158,229,287,357,444,519,598]⟩,⟨1,355,[66,158,229,287,322,357,444,519,598]⟩,⟨4,302,[66,158,183,229,287,357,444,519,598]⟩,⟨4,389,[66,158,229,287,332,357,444,519,598]⟩,⟨0,480,[54,66,158,229,287,357,444,519,598]⟩,⟨0,488,[66,158,229,287,357,380,444,519,598]⟩,⟨6,562,[7,66,158,229,287,357,444,519,598]⟩,⟨0,563,[66,158,229,287,357,425,444,519,598]⟩,⟨8,564,[20,66,158,229,287,357,444,519,598]⟩,⟨2,565,[66,158,229,287,357,444,494,519,598]⟩,⟨9,564,[32,66,158,229,287,357,444,519,598]⟩,⟨3,565,[66,158,229,287,357,444,519,574,598]⟩,⟨0,566,[0,66,158,229,287,357,444,519,598]⟩,⟨0,567,[66,158,229,287,357,444,468,519,598]⟩,⟨0,568,[66,118,158,229,287,357,444,519,598]⟩,⟨0,569,[66,158,229,287,357,444,480,519,598]⟩,⟨2,570,[66,158,202,229,287,357,444,519,598]⟩,⟨2,571,[66,158,229,287,357,444,498,519,598]⟩,⟨3,572,[35,66,158,229,287,357,444,519,598]⟩,⟨1,573,[66,158,229,287,357,444,519,598,691]⟩,⟨6,22,[66,158,229,287,341,357,444,519,598]⟩,⟨6,147,[66,158,229,287,357,444,465,519,598]⟩,⟨1,566,[1,66,158,229,287,357,444,519,598]⟩,⟨1,567,[66,158,229,287,357,444,519,553,598]⟩,⟨1,568,[66,141,158,229,287,357,444,519,598]⟩,⟨1,569,[66,158,229,287,357,444,519,563,598]⟩,⟨2,572,[22,66,158,229,287,357,444,519,598]⟩,⟨0,573,[66,158,229,287,357,444,519,598,681]⟩,⟨3,570,[66,158,229,279,287,357,444,519,598]⟩,⟨3,571,[66,158,229,287,357,444,519,580,598]⟩,⟨7,147,[66,158,229,287,357,444,519,549,598]⟩,⟨6,308,[66,158,229,287,357,391,444,519,598]⟩,⟨6,396,[66,158,229,287,357,444,519,588,598]⟩,⟨4,574,[3,66,158,229,287,357,444,519,598]⟩,⟨0,575,[66,158,229,287,357,444,519,598,630]⟩,⟨10,234,[15,66,229,287,357,444,519,598]⟩,⟨10,245,[15,66,158,229,287,357,444,519,598]⟩,⟨0,229,[66,158,229,287,357,444,519,598,674]⟩,⟨4,576,[66,158,220,229,287,357,444,519,598]⟩,⟨0,577,[66,158,229,287,357,444,519,598,639]⟩,⟨5,576,[66,158,229,284,287,357,444,519,598]⟩,⟨1,577,[66,158,229,287,357,444,519,598,646]⟩,⟨6,578,[66,158,229,287,345,357,444,519,598]⟩,⟨0,209,[66,158,229,287,357,444,519,598,625]⟩,⟨8,321,[66,158,229,287,357,434,444,519,598]⟩,⟨0,579,[66,158,229,287,357,444,519,598,657]⟩,⟨9,321,[66,158,229,287,357,444,511,519,598]⟩,⟨1,579,[66,158,229,287,357,444,519,598,667]⟩]⟩
def row9_180 : State := ⟨[66,158,162,229,287,357,444,519,594],[⟨4,22,[41,66,162,229,287,357,444,519,594]⟩,⟨10,209,[66,162,177,229,287,357,444,519,594]⟩,⟨4,16,[44,66,158,229,287,357,444,519,594]⟩,⟨0,54,[66,158,177,229,287,357,444,519,594]⟩,⟨2,321,[66,85,162,229,287,357,444,519,594]⟩,⟨10,416,[66,162,229,270,287,357,444,519,594]⟩,⟨0,14,[66,85,158,229,287,357,444,519,594]⟩,⟨2,417,[66,158,229,273,287,357,444,519,594]⟩,⟨3,321,[66,103,162,229,287,357,444,519,594]⟩,⟨11,416,[66,162,229,287,322,357,444,519,594]⟩,⟨1,14,[66,103,158,229,287,357,444,519,594]⟩,⟨3,417,[66,158,229,287,324,357,444,519,594]⟩,⟨6,574,[7,66,162,229,287,357,444,519,594]⟩,⟨10,580,[66,162,229,287,357,425,444,519,594]⟩,⟨6,121,[7,66,158,229,287,357,444,519,594]⟩,⟨0,581,[66,158,229,287,357,427,444,519,594]⟩,⟨6,576,[66,118,162,229,287,357,444,519,594]⟩,⟨10,582,[66,162,229,287,357,444,480,519,594]⟩,⟨0,167,[66,118,158,229,287,357,444,519,594]⟩,⟨0,583,[66,158,229,287,357,444,482,519,594]⟩,⟨7,576,[66,141,162,229,287,357,444,519,594]⟩,⟨11,582,[66,162,229,287,357,444,519,563,594]⟩,⟨1,167,[66,141,158,229,287,357,444,519,594]⟩,⟨1,583,[66,158,229,287,357,444,519,565,594]⟩,⟨10,584,[10,66,162,229,287,357,444,519,594]⟩,⟨10,229,[66,162,229,287,357,444,519,594,674]⟩,⟨0,585,[12,66,158,229,287,357,444,519]⟩,⟨0,586,[12,66,158,229,287,357,444,519,594]⟩,⟨0,235,[12,66,158,162,229,287,357,444,519]⟩,⟨0,20,[66,158,229,287,357,444,519,594,674]⟩,⟨0,101,[66,158,162,229,287,357,444,519,625]⟩]⟩
def row9_181 : State := ⟨[0,66,158,229,288,357,444,519,594],[⟨8,545,[66,159,229,288,357,444,519,594]⟩,⟨0,558,[66,158,159,229,288,357,444,519,594]⟩,⟨2,547,[0,66,159,229,288,357,444,519,594]⟩,⟨6,545,[66,158,230,288,357,444,519,594]⟩,⟨2,558,[66,158,229,230,288,357,444,519,594]⟩,⟨0,547,[0,66,158,230,288,357,444,519,594]⟩,⟨0,587,[66,158,229,288,358,444,519,594]⟩,⟨6,588,[66,158,229,288,357,358,444,519,594]⟩,⟨0,589,[0,66,158,229,288,358,444,519,594]⟩,⟨0,590,[0,36,66,158,229,288,357,519,594]⟩,⟨0,102,[0,66,158,229,288,357,465,519,594]⟩,⟨2,591,[66,158,229,288,357,444,520,594]⟩,⟨7,592,[66,158,229,288,357,444,519,520,594]⟩,⟨2,593,[0,66,158,229,288,357,444,520,594]⟩,⟨0,591,[66,158,229,288,357,444,519,595]⟩,⟨10,592,[66,158,229,288,357,444,519,594,595]⟩,⟨0,593,[0,66,158,229,288,357,444,519,595]⟩]⟩
def row9_182 : State := ⟨[0,66,158,229,287,288,357,444,519,594],[⟨5,546,[66,159,229,287,288,357,444,519,594]⟩,⟨3,546,[66,158,230,287,288,357,444,519,594]⟩,⟨3,594,[66,158,229,287,288,358,444,519,594]⟩,⟨0,595,[0,35,66,158,229,288,357,519,594]⟩,⟨0,211,[0,36,66,158,229,287,357,519,594]⟩,⟨5,596,[66,158,229,287,288,357,444,520,594]⟩,⟨3,596,[66,158,229,287,288,357,444,519,595]⟩]⟩
def row9_183 : State := ⟨[66,158,229,287,358,444,519,594],[⟨0,23,[41,66,158,229,287,358,444,519,594]⟩,⟨0,148,[66,158,177,229,287,358,444,519,594]⟩,⟨2,148,[66,158,229,253,287,358,444,519,594]⟩,⟨0,309,[66,85,158,229,287,358,444,519,594]⟩,⟨0,397,[66,158,229,270,287,358,444,519,594]⟩,⟨3,210,[66,158,229,287,310,358,444,519,594]⟩,⟨1,322,[66,103,158,229,287,358,444,519,594]⟩,⟨1,418,[66,158,229,287,322,358,444,519,594]⟩,⟨4,322,[66,158,183,229,287,358,444,519,594]⟩,⟨4,418,[66,158,229,287,332,358,444,519,594]⟩,⟨0,120,[55,66,158,229,287,358,444,519,594]⟩,⟨0,92,[66,158,229,287,358,380,444,519,594]⟩,⟨6,597,[7,66,158,229,287,358,444,519,594]⟩,⟨0,598,[66,158,229,287,358,426,444,519,594]⟩,⟨8,597,[20,66,158,229,287,358,444,519,594]⟩,⟨2,598,[66,158,229,287,358,444,495,519,594]⟩,⟨9,599,[32,66,158,229,287,358,444,519,594]⟩,⟨0,600,[66,158,229,287,358,444,519,575,594]⟩,⟨0,601,[0,66,158,229,287,358,444,519,594]⟩,⟨0,602,[66,158,229,287,358,444,468,519,594]⟩,⟨0,603,[66,118,158,229,287,358,444,519,594]⟩,⟨0,604,[66,158,229,287,358,444,480,519,594]⟩,⟨2,603,[66,158,202,229,287,358,444,519,594]⟩,⟨2,604,[66,158,229,287,358,444,498,519,594]⟩,⟨3,605,[35,66,158,229,287,358,444,519,594]⟩,⟨0,606,[66,158,229,287,358,444,519,594,691]⟩,⟨6,490,[66,158,229,287,342,358,444,519,594]⟩,⟨0,91,[66,158,229,287,358,444,465,519,594]⟩,⟨1,607,[1,66,158,229,287,358,444,519,594]⟩,⟨0,608,[66,158,229,287,358,444,519,553,594]⟩,⟨1,609,[66,141,158,229,287,358,444,519,594]⟩,⟨0,610,[66,158,229,287,358,444,519,563,594]⟩,⟨2,611,[22,66,158,229,287,358,444,519,594]⟩,⟨2,612,[66,158,229,287,358,444,519,594,681]⟩,⟨3,613,[66,158,229,279,287,358,444,519,594]⟩,⟨0,614,[66,158,229,287,358,444,519,580,594]⟩,⟨6,10,[66,158,229,287,341,358,444,519,594]⟩,⟨0,615,[66,158,229,287,358,444,519,550,594]⟩,⟨0,298,[66,158,229,287,358,391,444,519,594]⟩,⟨0,356,[66,158,229,287,358,444,519,588,594]⟩,⟨4,607,[3,66,158,229,287,358,444,519,594]⟩,⟨2,608,[66,158,229,287,358,444,519,594,629]⟩,⟨0,611,[10,66,158,229,287,358,444,519,594]⟩,⟨0,612,[66,158,229,287,358,444,519,594,674]⟩,⟨4,609,[66,158,220,229,287,358,444,519,594]⟩,⟨2,610,[66,158,229,287,358,444,519,594,637]⟩,⟨5,613,[66,158,229,284,287,358,444,519,594]⟩,⟨2,614,[66,158,229,287,358,444,519,594,644]⟩,⟨2,615,[66,158,229,287,358,444,519,594,626]⟩,⟨2,298,[66,158,229,287,358,434,444,519,594]⟩,⟨2,356,[66,158,229,287,358,444,519,594,656]⟩,⟨0,303,[66,158,229,287,358,444,511,519,594]⟩,⟨0,390,[66,158,229,287,358,444,519,594,665]⟩]⟩
def row9_184 : State := ⟨[66,67,158,229,287,357,444,519,594],[⟨0,10,[41,67,158,229,287,357,444,519,594]⟩,⟨6,91,[67,158,177,229,287,357,444,519,594]⟩,⟨0,6,[47,66,158,229,287,357,444,519,594]⟩,⟨0,54,[66,158,177,229,287,357,444,519,594]⟩,⟨6,137,[67,158,229,253,287,357,444,519,594]⟩,⟨0,2,[41,66,158,229,287,357,444,519,594]⟩,⟨2,139,[66,158,229,254,287,357,444,519,594]⟩,⟨7,137,[67,158,229,287,310,357,444,519,594]⟩,⟨3,139,[66,158,229,287,311,357,444,519,594]⟩,⟨6,481,[54,67,158,229,287,357,444,519,594]⟩,⟨6,92,[67,158,229,287,357,380,444,519,594]⟩,⟨6,474,[58,66,158,229,287,357,444,519,594]⟩,⟨0,5,[66,158,229,287,357,380,444,519,594]⟩,⟨0,597,[0,67,158,229,287,357,444,519,594]⟩,⟨6,616,[67,158,229,287,357,444,468,519,594]⟩,⟨0,121,[0,66,158,229,287,357,444,519,594]⟩,⟨6,535,[66,158,229,287,357,444,469,519,594]⟩,⟨1,597,[1,67,158,229,287,357,444,519,594]⟩,⟨7,616,[67,158,229,287,357,444,519,553,594]⟩,⟨1,121,[1,66,158,229,287,357,444,519,594]⟩,⟨7,535,[66,158,229,287,357,444,519,554,594]⟩,⟨4,599,[3,67,158,229,287,357,444,519,594]⟩,⟨6,617,[67,158,229,287,357,444,519,594,629]⟩,⟨4,121,[3,66,158,229,287,357,444,519,594]⟩,⟨10,581,[66,158,229,287,357,444,519,594,630]⟩]⟩
def row9_185 : State := ⟨[0,66,158,229,287,358,444,519,594],[⟨4,548,[66,159,229,287,358,444,519,594]⟩,⟨0,559,[66,158,159,229,287,358,444,519,594]⟩,⟨2,550,[0,66,159,229,287,358,444,519,594]⟩,⟨1,548,[66,158,230,287,358,444,519,594]⟩,⟨2,559,[66,158,229,230,287,358,444,519,594]⟩,⟨0,550,[0,66,158,230,287,358,444,519,594]⟩,⟨0,587,[66,158,229,288,358,444,519,594]⟩,⟨3,594,[66,158,229,287,288,358,444,519,594]⟩,⟨0,589,[0,66,158,229,288,358,444,519,594]⟩,⟨0,618,[0,35,66,158,229,287,358,519,594]⟩,⟨0,103,[0,66,158,229,287,358,465,519,594]⟩,⟨2,619,[66,158,229,287,358,444,520,594]⟩,⟨0,620,[66,158,229,287,358,444,519,520,594]⟩,⟨2,621,[0,66,158,229,287,358,444,520,594]⟩,⟨0,619,[66,158,229,287,358,444,519,595]⟩,⟨2,620,[66,158,229,287,358,444,519,594,595]⟩,⟨0,621,[0,66,158,229,287,358,444,519,595]⟩]⟩
def row9_186 : State := ⟨[0,66,158,229,287,357,358,444,519,594],[⟨8,549,[66,159,229,287,357,358,444,519,594]⟩,⟨6,549,[66,158,230,287,357,358,444,519,594]⟩,⟨6,588,[66,158,229,288,357,358,444,519,594]⟩,⟨0,103,[0,66,158,229,287,358,465,519,594]⟩,⟨0,123,[0,66,158,229,287,357,465,519,594]⟩,⟨8,622,[66,158,229,287,357,358,444,520,594]⟩,⟨6,622,[66,158,229,287,357,358,444,519,595]⟩]⟩
def row9_187 : State := ⟨[0,7,66,158,229,287,357,444,519,594],[⟨0,623,[8,66,158,229,287,357,444,519,594]⟩,⟨0,597,[0,67,158,229,287,357,444,519,594]⟩,⟨6,525,[7,66,159,229,287,357,444,519,594]⟩,⟨7,509,[7,66,158,230,287,357,444,519,594]⟩,⟨0,624,[0,66,158,236,287,357,444,519,594]⟩,⟨6,566,[7,66,158,229,288,357,444,519,594]⟩,⟨0,625,[0,66,158,229,294,357,444,519,594]⟩,⟨6,597,[7,66,158,229,287,358,444,519,594]⟩,⟨0,525,[0,66,158,229,287,357,448,519,594]⟩,⟨6,624,[7,66,158,229,287,357,444,520,594]⟩,⟨2,509,[0,66,158,229,287,357,444,523,594]⟩,⟨6,625,[7,66,158,229,287,357,444,519,595]⟩,⟨0,566,[0,66,158,229,287,357,444,519,598]⟩]⟩
def row9_188 : State := ⟨[0,66,158,229,287,357,425,444,519,594],[⟨10,534,[66,159,229,287,357,425,444,519,594]⟩,⟨7,510,[66,158,230,287,357,425,444,519,594]⟩,⟨6,567,[66,158,229,288,357,425,444,519,594]⟩,⟨0,616,[66,158,229,287,358,425,444,519,594]⟩,⟨0,535,[66,158,229,287,357,426,444,519,594]⟩,⟨0,626,[66,158,229,287,357,425,444,520,594]⟩,⟨0,627,[66,158,229,287,357,425,444,519,595]⟩]⟩
def row9_189 : State := ⟨[0,32,66,158,229,287,357,444,519,594],[⟨3,628,[33,66,158,229,287,357,444,519,594]⟩,⟨0,599,[0,74,158,229,287,357,444,519,594]⟩,⟨11,517,[32,66,159,229,287,357,444,519,594]⟩,⟨2,629,[0,66,169,229,287,357,444,519,594]⟩,⟨9,517,[32,66,158,230,287,357,444,519,594]⟩,⟨0,629,[0,66,158,244,287,357,444,519,594]⟩,⟨9,574,[32,66,158,229,288,357,444,519,594]⟩,⟨9,599,[32,66,158,229,287,358,444,519,594]⟩,⟨0,574,[0,66,158,229,287,357,459,519,594]⟩,⟨0,630,[0,32,35,66,158,229,357,519,594]⟩,⟨11,629,[32,66,158,229,287,357,444,520,594]⟩,⟨2,517,[0,66,158,229,287,357,444,535,594]⟩,⟨9,629,[32,66,158,229,287,357,444,519,595]⟩,⟨0,517,[0,66,158,229,287,357,444,519,609]⟩]⟩
def row9_190 : State := ⟨[0,66,158,229,287,357,444,519,574,594],[⟨11,518,[66,159,229,287,357,444,519,574,594]⟩,⟨9,518,[66,158,230,287,357,444,519,574,594]⟩,⟨6,580,[66,158,229,288,357,444,519,574,594]⟩,⟨0,617,[66,158,229,287,358,444,519,574,594]⟩,⟨0,104,[0,66,158,229,287,465,519,574,594]⟩,⟨5,631,[66,158,229,287,357,444,520,574,594]⟩,⟨3,581,[66,158,229,287,357,444,519,575,594]⟩,⟨0,632,[0,66,158,229,287,350,357,519,594]⟩,⟨3,631,[66,158,229,287,357,444,519,574,595]⟩]⟩
def row9_191 : State := ⟨[0,66,158,229,287,357,444,468,519,594],[⟨8,506,[66,159,229,287,357,444,468,519,594]⟩,⟨6,506,[66,158,230,287,357,444,468,519,594]⟩,⟨6,563,[66,158,229,288,357,444,468,519,594]⟩,⟨0,602,[66,158,229,287,358,444,468,519,594]⟩,⟨2,633,[66,158,229,287,357,444,468,520,594]⟩,⟨0,633,[66,158,229,287,357,444,468,519,595]⟩]⟩
def row9_192 : State := ⟨[0,66,118,158,229,287,357,444,519,594],[⟨0,537,[66,119,158,229,287,357,444,519,594]⟩,⟨6,536,[66,118,159,229,287,357,444,519,594]⟩,⟨6,513,[66,118,158,230,287,357,444,519,594]⟩,⟨6,568,[66,118,158,229,288,357,444,519,594]⟩,⟨0,603,[66,118,158,229,287,358,444,519,594]⟩,⟨0,634,[66,118,158,229,287,357,444,520,594]⟩,⟨0,635,[66,118,158,229,287,357,444,519,595]⟩]⟩
def row9_193 : State := ⟨[0,66,158,229,287,357,444,480,519,594],[⟨10,164,[66,159,229,287,357,444,480,519,594]⟩,⟨6,514,[66,158,230,287,357,444,480,519,594]⟩,⟨6,569,[66,158,229,288,357,444,480,519,594]⟩,⟨0,604,[66,158,229,287,358,444,480,519,594]⟩,⟨0,636,[66,158,229,287,357,444,480,520,594]⟩,⟨0,637,[66,158,229,287,357,444,480,519,595]⟩]⟩
def row9_194 : State := ⟨[0,35,66,158,229,287,357,519,594],[⟨3,585,[36,66,158,229,287,357,519,594]⟩,⟨3,225,[35,36,66,158,229,287,357,519,594]⟩,⟨0,211,[0,36,66,158,229,287,357,519,594]⟩,⟨0,638,[0,35,76,158,229,287,357,519,594]⟩,⟨2,551,[0,35,66,159,229,287,357,519,594]⟩,⟨2,639,[0,35,66,171,229,287,357,519,594]⟩,⟨0,551,[0,35,66,158,230,287,357,519,594]⟩,⟨0,639,[0,35,66,158,246,287,357,519,594]⟩,⟨0,595,[0,35,66,158,229,288,357,519,594]⟩,⟨0,419,[0,35,66,158,229,322,357,519,594]⟩,⟨2,419,[0,35,66,158,229,332,357,519,594]⟩,⟨0,618,[0,35,66,158,229,287,358,519,594]⟩,⟨0,640,[0,66,158,229,287,370,519,594]⟩,⟨0,641,[0,66,158,229,287,357,370,519,594]⟩,⟨0,642,[0,35,66,158,229,287,370,519,594]⟩,⟨0,630,[0,32,35,66,158,229,357,519,594]⟩,⟨5,643,[35,66,158,229,287,357,520,594]⟩,⟨3,644,[35,66,158,229,287,357,519,520,594]⟩,⟨2,645,[0,35,66,158,229,287,357,520,594]⟩,⟨2,646,[0,35,66,158,229,287,357,538,594]⟩,⟨3,643,[35,66,158,229,287,357,519,595]⟩,⟨5,644,[35,66,158,229,287,357,519,594,595]⟩,⟨0,645,[0,35,66,158,229,287,357,519,595]⟩,⟨0,646,[0,35,66,158,229,287,357,519,615]⟩]⟩
def row9_195 : State := ⟨[0,35,66,158,229,287,357,444,519,594],[⟨3,586,[36,66,158,229,287,357,444,519,594]⟩,⟨0,647,[0,76,158,229,287,357,444,519,594]⟩,⟨8,521,[35,66,159,229,287,357,444,519,594]⟩,⟨2,648,[0,66,171,229,287,357,444,519,594]⟩,⟨6,521,[35,66,158,230,287,357,444,519,594]⟩,⟨0,648,[0,66,158,246,287,357,444,519,594]⟩,⟨6,584,[35,66,158,229,288,357,444,519,594]⟩,⟨3,605,[35,66,158,229,287,358,444,519,594]⟩,⟨0,649,[0,66,158,229,287,370,444,519,594]⟩,⟨5,650,[35,66,158,229,287,357,444,520,594]⟩,⟨2,651,[0,66,158,229,287,357,444,538,594]⟩,⟨3,650,[35,66,158,229,287,357,444,519,595]⟩,⟨0,651,[0,66,158,229,287,357,444,519,615]⟩]⟩
def row9_196 : State := ⟨[0,66,158,229,287,357,444,519,594,691],[⟨10,522,[66,159,229,287,357,444,519,594,691]⟩,⟨7,522,[66,158,230,287,357,444,519,594,691]⟩,⟨6,229,[66,158,229,288,357,444,519,594,691]⟩,⟨0,606,[66,158,229,287,358,444,519,594,691]⟩,⟨2,652,[66,158,229,287,357,444,520,594,691]⟩,⟨0,652,[66,158,229,287,357,444,519,595,691]⟩]⟩
def row9_197 : State := ⟨[66,158,229,287,357,444,519,595],[⟨0,24,[41,66,158,229,287,357,444,519,595]⟩,⟨0,150,[66,158,177,229,287,357,444,519,595]⟩,⟨2,149,[66,158,229,253,287,357,444,519,595]⟩,⟨0,310,[66,85,158,229,287,357,444,519,595]⟩,⟨0,398,[66,158,229,270,287,357,444,519,595]⟩,⟨3,212,[66,158,229,287,310,357,444,519,595]⟩,⟨1,324,[66,103,158,229,287,357,444,519,595]⟩,⟨1,422,[66,158,229,287,322,357,444,519,595]⟩,⟨4,323,[66,158,183,229,287,357,444,519,595]⟩,⟨4,421,[66,158,229,287,332,357,444,519,595]⟩,⟨0,482,[54,66,158,229,287,357,444,519,595]⟩,⟨0,489,[66,158,229,287,357,380,444,519,595]⟩,⟨6,625,[7,66,158,229,287,357,444,519,595]⟩,⟨0,627,[66,158,229,287,357,425,444,519,595]⟩,⟨8,624,[20,66,158,229,287,357,444,519,595]⟩,⟨2,626,[66,158,229,287,357,444,494,519,595]⟩,⟨9,629,[32,66,158,229,287,357,444,519,595]⟩,⟨3,631,[66,158,229,287,357,444,519,574,595]⟩,⟨0,653,[0,66,158,229,287,357,444,519,595]⟩,⟨0,633,[66,158,229,287,357,444,468,519,595]⟩,⟨0,635,[66,118,158,229,287,357,444,519,595]⟩,⟨0,637,[66,158,229,287,357,444,480,519,595]⟩,⟨2,634,[66,158,202,229,287,357,444,519,595]⟩,⟨2,636,[66,158,229,287,357,444,498,519,595]⟩,⟨3,643,[35,66,158,229,287,357,519,595]⟩,⟨3,650,[35,66,158,229,287,357,444,519,595]⟩,⟨0,652,[66,158,229,287,357,444,519,595,691]⟩,⟨6,11,[66,158,229,287,341,357,444,519,595]⟩,⟨3,108,[66,158,229,287,357,465,519,595]⟩,⟨6,114,[66,158,229,287,357,444,465,519,595]⟩,⟨1,654,[1,66,158,229,287,357,444,519,595]⟩,⟨1,655,[66,158,229,287,357,444,519,553,595]⟩,⟨1,656,[66,141,158,229,287,357,444,519,595]⟩,⟨1,657,[66,158,229,287,357,444,519,563,595]⟩,⟨2,658,[22,66,158,229,287,357,444,519,595]⟩,⟨0,659,[66,158,229,287,357,444,519,595,681]⟩,⟨3,660,[66,158,229,279,287,357,444,519,595]⟩,⟨3,661,[66,158,229,287,357,444,519,580,595]⟩,⟨7,141,[66,158,229,287,357,444,519,549,595]⟩,⟨6,300,[66,158,229,287,357,391,444,519,595]⟩,⟨6,358,[66,158,229,287,357,444,519,588,595]⟩,⟨2,376,[4,66,158,229,287,357,444,519,595]⟩,⟨0,364,[66,158,229,287,357,444,519,595,629]⟩,⟨0,662,[10,66,158,229,287,357,444,519,595]⟩,⟨0,663,[66,158,229,287,357,444,519,595,675]⟩,⟨4,664,[66,158,220,229,287,357,444,519,595]⟩,⟨0,665,[66,158,229,287,357,444,519,595,638]⟩,⟨5,666,[66,158,229,284,287,357,444,519,595]⟩,⟨0,667,[66,158,229,287,357,444,519,595,645]⟩,⟨0,668,[66,158,229,287,357,444,519,595,626]⟩,⟨8,669,[66,158,229,287,357,435,444,519,595]⟩,⟨0,357,[66,158,229,287,357,444,519,595,656]⟩,⟨9,305,[66,158,229,287,357,444,511,519,595]⟩,⟨0,670,[66,158,229,287,357,444,519,595,666]⟩]⟩
def row9_198 : State := ⟨[66,158,165,229,287,357,444,519,594],[⟨4,11,[41,66,165,229,287,357,444,519,594]⟩,⟨10,138,[66,165,177,229,287,357,444,519,594]⟩,⟨0,2,[41,66,158,229,287,357,444,519,594]⟩,⟨0,139,[66,158,179,229,287,357,444,519,594]⟩,⟨0,109,[66,158,165,253,287,357,444,519,594]⟩,⟨2,299,[66,85,165,229,287,357,444,519,594]⟩,⟨10,357,[66,165,229,270,287,357,444,519,594]⟩,⟨2,125,[66,92,158,229,287,357,444,519,594]⟩,⟨0,53,[66,158,229,270,287,357,444,519,594]⟩,⟨3,305,[66,103,165,229,287,357,444,519,594]⟩,⟨10,391,[66,165,229,287,322,357,444,519,594]⟩,⟨1,14,[66,103,158,229,287,357,444,519,594]⟩,⟨1,392,[66,158,229,287,325,357,444,519,594]⟩,⟨6,671,[7,66,165,229,287,357,444,519,594]⟩,⟨10,364,[66,165,229,287,357,425,444,519,594]⟩,⟨6,672,[21,66,158,229,287,357,444,519,594]⟩,⟨0,7,[66,158,229,287,357,425,444,519,594]⟩,⟨6,664,[66,118,165,229,287,357,444,519,594]⟩,⟨10,673,[66,165,229,287,357,444,480,519,594]⟩,⟨0,167,[66,118,158,229,287,357,444,519,594]⟩,⟨6,539,[66,158,229,287,357,444,483,519,594]⟩,⟨7,666,[66,141,165,229,287,357,444,519,594]⟩,⟨10,674,[66,165,229,287,357,444,519,563,594]⟩,⟨1,167,[66,141,158,229,287,357,444,519,594]⟩,⟨7,583,[66,158,229,287,357,444,519,566,594]⟩,⟨7,644,[22,66,158,165,287,357,444,519,594]⟩,⟨10,662,[10,66,165,229,287,357,444,519,594]⟩,⟨10,675,[66,165,229,287,357,444,519,594,674]⟩,⟨0,244,[10,66,158,229,287,357,444,519,594]⟩,⟨10,541,[66,158,229,287,357,444,519,594,676]⟩]⟩
def row9_199 : State := ⟨[0,66,158,229,287,357,444,519,595],[⟨4,552,[66,159,229,287,357,444,519,595]⟩,⟨0,561,[66,158,159,229,287,357,444,519,595]⟩,⟨2,554,[0,66,159,229,287,357,444,519,595]⟩,⟨1,555,[66,158,230,287,357,444,519,595]⟩,⟨2,560,[66,158,229,230,287,357,444,519,595]⟩,⟨0,557,[0,66,158,230,287,357,444,519,595]⟩,⟨0,591,[66,158,229,288,357,444,519,595]⟩,⟨3,596,[66,158,229,287,288,357,444,519,595]⟩,⟨0,593,[0,66,158,229,288,357,444,519,595]⟩,⟨0,619,[66,158,229,287,358,444,519,595]⟩,⟨6,622,[66,158,229,287,357,358,444,519,595]⟩,⟨0,621,[0,66,158,229,287,358,444,519,595]⟩,⟨0,645,[0,35,66,158,229,287,357,519,595]⟩,⟨0,110,[0,66,158,229,287,357,465,519,595]⟩,⟨0,676,[66,158,229,287,357,444,520,595]⟩,⟨7,677,[66,158,229,287,357,444,519,520,595]⟩,⟨0,678,[0,66,158,229,287,357,444,520,595]⟩]⟩
def row9_200 : State := ⟨[0,66,158,229,287,357,444,519,520,594],[⟨7,556,[66,159,229,287,357,444,519,520,594]⟩,⟨7,553,[66,158,230,287,357,444,519,520,594]⟩,⟨7,592,[66,158,229,288,357,444,519,520,594]⟩,⟨0,620,[66,158,229,287,358,444,519,520,594]⟩,⟨7,677,[66,158,229,287,357,444,519,520,595]⟩]⟩
def row9_201 : State := ⟨[0,1,66,158,229,287,357,444,519,594],[⟨0,672,[2,66,158,229,287,357,444,519,594]⟩,⟨3,507,[1,66,159,229,287,357,444,519,594]⟩,⟨2,507,[0,66,160,229,287,357,444,519,594]⟩,⟨1,503,[1,66,158,230,287,357,444,519,594]⟩,⟨0,564,[0,66,158,231,287,357,444,519,594]⟩,⟨1,564,[1,66,158,229,288,357,444,519,594]⟩,⟨0,503,[0,66,158,229,289,357,444,519,594]⟩,⟨1,607,[1,66,158,229,287,358,444,519,594]⟩,⟨0,607,[0,66,158,229,287,359,444,519,594]⟩,⟨0,671,[0,66,158,229,287,357,445,519,594]⟩,⟨1,671,[1,66,158,229,287,357,444,520,594]⟩,⟨1,654,[1,66,158,229,287,357,444,519,595]⟩,⟨0,654,[0,66,158,229,287,357,444,519,596]⟩]⟩
def row9_202 : State := ⟨[0,66,158,229,287,357,444,519,553,594],[⟨9,508,[66,159,229,287,357,444,519,553,594]⟩,⟨7,504,[66,158,230,287,357,444,519,553,594]⟩,⟨7,565,[66,158,229,288,357,444,519,553,594]⟩,⟨0,608,[66,158,229,287,358,444,519,553,594]⟩,⟨2,364,[66,158,229,287,357,444,520,553,594]⟩,⟨1,655,[66,158,229,287,357,444,519,553,595]⟩]⟩
def row9_203 : State := ⟨[0,66,141,158,229,287,357,444,519,594],[⟨1,679,[66,142,158,229,287,357,444,519,594]⟩,⟨7,529,[66,141,159,229,287,357,444,519,594]⟩,⟨7,511,[66,141,158,230,287,357,444,519,594]⟩,⟨7,570,[66,141,158,229,288,357,444,519,594]⟩,⟨1,609,[66,141,158,229,287,358,444,519,594]⟩,⟨1,664,[66,141,158,229,287,357,444,520,594]⟩,⟨1,656,[66,141,158,229,287,357,444,519,595]⟩]⟩
def row9_204 : State := ⟨[0,66,158,229,287,357,444,519,563,594],[⟨10,538,[66,159,229,287,357,444,519,563,594]⟩,⟨7,512,[66,158,230,287,357,444,519,563,594]⟩,⟨7,571,[66,158,229,288,357,444,519,563,594]⟩,⟨0,610,[66,158,229,287,358,444,519,563,594]⟩,⟨2,673,[66,158,229,287,357,444,520,563,594]⟩,⟨1,539,[66,158,229,287,357,444,519,564,594]⟩,⟨1,657,[66,158,229,287,357,444,519,563,595]⟩]⟩
def row9_205 : State := ⟨[0,10,66,158,229,287,357,444,519,594],[⟨0,680,[11,66,158,229,287,357,444,519,594]⟩,⟨0,681,[0,68,158,229,287,357,444,519,594]⟩,⟨10,527,[10,66,159,229,287,357,444,519,594]⟩,⟨11,515,[10,66,158,230,287,357,444,519,594]⟩,⟨0,682,[0,66,158,239,287,357,444,519,594]⟩,⟨10,572,[10,66,158,229,288,357,444,519,594]⟩,⟨0,683,[0,66,158,229,297,357,444,519,594]⟩,⟨0,611,[10,66,158,229,287,358,444,519,594]⟩,⟨0,684,[0,66,158,229,287,364,444,519,594]⟩,⟨0,685,[0,66,158,229,287,357,450,519,594]⟩,⟨0,658,[10,66,158,229,287,357,444,520,594]⟩,⟨2,686,[0,66,158,229,287,357,444,526,594]⟩,⟨0,662,[10,66,158,229,287,357,444,519,595]⟩]⟩
def row9_206 : State := ⟨[0,66,158,229,287,357,444,519,594,674],[⟨10,540,[66,159,229,287,357,444,519,594,674]⟩,⟨7,516,[66,158,230,287,357,444,519,594,674]⟩,⟨8,573,[66,158,229,288,357,444,519,594,674]⟩,⟨0,612,[66,158,229,287,358,444,519,594,674]⟩,⟨2,659,[66,158,229,287,357,444,520,594,674]⟩,⟨0,675,[66,158,229,287,357,444,519,595,674]⟩,⟨0,541,[66,158,229,287,357,444,519,594,675]⟩]⟩
def row9_207 : State := ⟨[0,66,158,229,279,287,357,444,519,594],[⟨9,523,[66,159,229,279,287,357,444,519,594]⟩,⟨9,519,[66,158,230,279,287,357,444,519,594]⟩,⟨3,687,[66,158,229,280,287,357,444,519,594]⟩,⟨9,576,[66,158,229,279,288,357,444,519,594]⟩,⟨3,613,[66,158,229,279,287,358,444,519,594]⟩,⟨3,666,[66,158,229,279,287,357,444,520,594]⟩,⟨3,660,[66,158,229,279,287,357,444,519,595]⟩]⟩
def row9_208 : State := ⟨[0,66,158,229,287,357,444,519,580,594],[⟨9,524,[66,159,229,287,357,444,519,580,594]⟩,⟨9,520,[66,158,230,287,357,444,519,580,594]⟩,⟨6,582,[66,158,229,288,357,444,519,580,594]⟩,⟨0,614,[66,158,229,287,358,444,519,580,594]⟩,⟨2,674,[66,158,229,287,357,444,520,580,594]⟩,⟨3,583,[66,158,229,287,357,444,519,581,594]⟩,⟨0,688,[0,66,158,229,287,357,393,519,594]⟩,⟨3,661,[66,158,229,287,357,444,519,580,595]⟩]⟩
def row9_209 : State := ⟨[66,158,229,287,357,425,444,494,519,594],[⟨9,359,[66,270,287,357,425,444,494,519,594]⟩,⟨0,57,[66,158,229,287,357,387,444,519,594]⟩,⟨0,366,[66,158,229,287,357,444,507,519,594]⟩]⟩
def row9_210 : State := ⟨[64,66,158,229,287,357,444,519,594],[⟨0,2,[41,66,158,229,287,357,444,519,594]⟩,⟨0,115,[66,158,174,229,287,357,444,519,594]⟩,⟨2,115,[66,158,229,251,287,357,444,519,594]⟩,⟨3,115,[66,158,229,287,308,357,444,519,594]⟩,⟨0,119,[54,66,158,229,287,357,444,519,594]⟩,⟨6,280,[66,158,229,287,357,378,444,519,594]⟩,⟨6,689,[66,158,229,287,357,444,467,519,594]⟩,⟨7,689,[66,158,229,287,357,444,519,552,594]⟩,⟨10,689,[66,158,229,287,357,444,519,594,628]⟩]⟩
def row9_211 : State := ⟨[64,66,158,229,287,357,425,444,519,594],[]⟩
def row9_212 : State := ⟨[66,158,229,287,357,425,428,444,519,594],[⟨10,690,[66,158,229,287,347,357,425,444,519]⟩]⟩
def row9_213 : State := ⟨[66,88,158,229,287,357,444,519,594],[⟨0,2,[41,66,158,229,287,357,444,519,594]⟩,⟨0,691,[66,100,158,229,287,357,444,519,594]⟩,⟨0,142,[66,88,177,229,287,357,444,519,594]⟩,⟨0,14,[66,85,158,229,287,357,444,519,594]⟩,⟨7,363,[66,158,236,287,357,444,519,594]⟩,⟨2,365,[66,158,229,236,287,357,444,519,594]⟩,⟨0,669,[66,88,158,236,287,357,444,519,594]⟩,⟨3,692,[66,158,229,287,314,357,444,519,594]⟩,⟨6,121,[7,66,158,229,287,357,444,519,594]⟩,⟨0,57,[66,158,229,287,357,387,444,519,594]⟩,⟨0,58,[66,78,158,229,287,357,444,519,594]⟩,⟨6,492,[66,158,229,287,357,444,462,519,594]⟩,⟨7,693,[66,158,229,287,357,444,519,561,594]⟩,⟨10,694,[66,158,229,287,357,444,519,594,636]⟩,⟨0,695,[10,66,88,229,287,357,444,519,594]⟩]⟩
def row9_214 : State := ⟨[66,88,158,229,287,357,444,494,519,594],[⟨7,364,[66,158,236,287,357,444,494,519,594]⟩]⟩
def row9_215 : State := ⟨[66,158,229,287,357,425,444,507,519,594],[]⟩
def row9_216 : State := ⟨[66,158,229,287,357,425,444,468,519,594],[⟨0,696,[66,158,229,287,357,406,444,519,594]⟩,⟨0,127,[66,158,229,287,357,444,490,519,594]⟩]⟩
def row9_217 : State := ⟨[66,118,158,229,287,357,425,444,519,594],[]⟩
def row9_218 : State := ⟨[66,158,229,287,357,425,444,480,519,594],[⟨0,59,[66,158,229,287,357,415,444,519,594]⟩,⟨6,153,[66,158,229,287,357,444,489,519,594]⟩]⟩
def row9_219 : State := ⟨[66,118,158,229,287,357,444,494,519,594],[⟨7,697,[66,158,258,287,357,444,494,519,594]⟩,⟨0,58,[66,78,158,229,287,357,444,519,594]⟩,⟨2,286,[66,158,229,287,357,444,500,519,594]⟩]⟩
def row9_220 : State := ⟨[66,158,229,287,357,425,444,498,519,594],[⟨6,698,[66,158,229,287,357,401,444,519,594]⟩,⟨0,179,[66,158,229,287,357,444,510,519,594]⟩]⟩
def row9_221 : State := ⟨[10,66,158,229,287,357,444,468,519,594],[⟨10,699,[68,158,229,287,357,444,468,519,594]⟩,⟨6,700,[66,158,239,287,357,444,468,519,594]⟩,⟨8,701,[66,158,229,297,357,444,468,519,594]⟩,⟨0,702,[66,158,229,287,364,444,468,519,594]⟩,⟨3,703,[66,158,229,287,357,450,468,519,594]⟩,⟨8,704,[66,158,229,287,357,444,470,519,594]⟩,⟨2,705,[66,158,229,287,357,444,468,526,594]⟩,⟨1,361,[10,66,158,229,287,357,468,519,656]⟩,⟨10,695,[10,66,158,229,287,357,436,444,519]⟩]⟩
def row9_222 : State := ⟨[66,158,229,287,357,425,444,519,594,681],[⟨0,706,[66,158,229,287,357,418,444,519,594]⟩,⟨9,184,[66,158,229,287,357,444,519,594,709]⟩]⟩
def row9_223 : State := ⟨[66,129,158,229,287,357,444,519,594],[⟨0,2,[41,66,158,229,287,357,444,519,594]⟩,⟨0,152,[66,137,158,229,287,357,444,519,594]⟩,⟨0,14,[66,85,158,229,287,357,444,519,594]⟩,⟨2,312,[66,158,229,258,287,357,444,519,594]⟩,⟨3,402,[66,158,229,287,319,357,444,519,594]⟩,⟨6,707,[66,158,229,287,357,408,444,519,594]⟩,⟨0,167,[66,118,158,229,287,357,444,519,594]⟩,⟨6,59,[66,158,229,287,357,444,461,519,594]⟩,⟨6,58,[66,114,158,229,287,357,444,519,594]⟩,⟨7,60,[66,158,229,287,357,444,519,560,594]⟩,⟨10,708,[66,158,229,287,357,444,519,594,660]⟩]⟩
def row9_224 : State := ⟨[66,129,158,229,287,357,444,468,519,594],[]⟩
def row9_225 : State := ⟨[66,158,229,287,357,425,444,489,519,594],[⟨3,709,[66,107,158,229,357,425,444,519,594]⟩]⟩
def row9_226 : State := ⟨[66,158,229,287,357,425,444,519,594,629],[⟨0,710,[66,158,229,287,357,376,444,519,594]⟩,⟨0,131,[66,158,229,287,357,444,519,594,708]⟩]⟩
def row9_227 : State := ⟨[10,66,158,229,287,357,425,444,519,594],[⟨10,711,[68,158,229,287,357,425,444,519,594]⟩,⟨7,712,[66,158,239,287,357,425,444,519,594]⟩,⟨6,712,[66,158,229,297,357,425,444,519,594]⟩,⟨0,218,[66,158,229,287,364,425,444,519,594]⟩,⟨1,713,[66,158,229,287,357,425,450,519,594]⟩,⟨0,713,[66,158,229,287,357,425,444,526,594]⟩]⟩
def row9_228 : State := ⟨[66,158,229,287,357,425,444,519,594,674],[⟨0,214,[66,158,229,287,425,444,519,625,674]⟩,⟨0,59,[66,158,229,287,357,415,444,519,594]⟩,⟨10,221,[66,158,229,287,357,444,519,594,707]⟩]⟩
def row9_229 : State := ⟨[66,118,158,229,287,357,444,519,574,594],[⟨6,714,[66,158,229,319,357,444,519,574,594]⟩,⟨0,715,[66,158,229,287,403,444,519,574,594]⟩,⟨3,716,[66,158,229,287,357,444,519,585,594]⟩]⟩
def row9_230 : State := ⟨[66,158,229,287,357,425,444,519,594,637],[⟨9,360,[66,270,287,357,425,444,519,594,637]⟩,⟨0,158,[66,158,229,287,425,444,519,625,637]⟩,⟨0,717,[66,158,229,287,357,385,444,519,594]⟩,⟨11,184,[66,158,229,287,357,444,519,594,710]⟩]⟩
def row9_231 : State := ⟨[48,66,158,229,287,357,444,519,594],[⟨0,2,[41,66,158,229,287,357,444,519,594]⟩,⟨10,216,[68,158,229,287,357,444,519,594]⟩,⟨0,220,[66,68,158,229,287,357,444,519,594]⟩,⟨0,718,[48,68,158,229,287,357,444,519,594]⟩,⟨9,430,[66,158,239,287,357,444,519,594]⟩,⟨2,434,[66,158,229,239,287,357,444,519,594]⟩,⟨1,719,[48,66,158,239,287,357,444,519,594]⟩,⟨0,423,[48,66,229,270,287,357,444,519,594]⟩,⟨8,430,[66,158,229,297,357,444,519,594]⟩,⟨3,434,[66,158,229,287,297,357,444,519,594]⟩,⟨0,719,[48,66,158,229,297,357,444,519,594]⟩,⟨1,423,[48,66,229,287,322,357,444,519,594]⟩,⟨10,720,[66,158,229,287,357,381,444,519,594]⟩,⟨6,632,[7,48,66,229,287,357,444,519,594]⟩,⟨8,721,[66,158,229,287,357,444,463,519,594]⟩,⟨9,721,[66,158,229,287,357,444,519,546,594]⟩,⟨0,244,[10,66,158,229,287,357,444,519,594]⟩,⟨10,59,[66,158,229,287,357,444,519,594,620]⟩,⟨0,362,[48,66,158,229,287,357,444,519,656]⟩,⟨1,362,[48,66,158,229,287,357,444,519,665]⟩]⟩
def row9_232 : State := ⟨[48,66,158,229,287,357,444,519,594,629],[⟨10,218,[68,158,229,287,357,444,519,594,629]⟩,⟨11,713,[66,158,239,287,357,444,519,594,629]⟩,⟨10,713,[66,158,229,297,357,444,519,594,629]⟩]⟩
def row9_233 : State := ⟨[66,158,229,287,357,425,444,519,594,707],[]⟩
def row9_234 : State := ⟨[66,137,158,229,287,357,444,519,594],[⟨0,17,[66,129,158,229,287,357,444,519,594]⟩,⟨0,54,[66,158,177,229,287,357,444,519,594]⟩,⟨0,14,[66,85,158,229,287,357,444,519,594]⟩,⟨2,188,[66,158,229,261,287,357,444,519,594]⟩,⟨6,271,[137,158,229,287,310,357,444,519,594]⟩,⟨0,2,[41,66,158,229,287,357,444,519,594]⟩,⟨3,273,[66,158,229,287,327,357,444,519,594]⟩,⟨6,496,[137,158,229,287,357,380,444,519,594]⟩,⟨0,119,[54,66,158,229,287,357,444,519,594]⟩,⟨0,497,[66,158,229,287,357,409,444,519,594]⟩,⟨0,537,[66,119,158,229,287,357,444,519,594]⟩,⟨6,7,[66,158,229,287,357,444,468,519,594]⟩,⟨7,722,[66,115,158,229,287,357,444,519,594]⟩,⟨7,286,[66,158,229,287,357,444,519,567,594]⟩,⟨6,715,[137,158,229,287,357,444,519,594,629]⟩,⟨4,121,[3,66,158,229,287,357,444,519,594]⟩,⟨10,716,[66,158,229,287,357,444,519,594,663]⟩]⟩
def row9_235 : State := ⟨[66,118,137,158,229,287,357,444,519,594],[]⟩
def row9_236 : State := ⟨[66,78,118,158,229,287,357,444,519,594],[]⟩
def row9_237 : State := ⟨[66,158,214,229,287,357,444,519,594],[⟨10,187,[66,177,214,229,287,357,444,519,594]⟩,⟨0,2,[41,66,158,229,287,357,444,519,594]⟩,⟨0,188,[66,158,219,229,287,357,444,519,594]⟩,⟨2,17,[66,158,205,229,287,357,444,519,594]⟩,⟨0,53,[66,158,229,270,287,357,444,519,594]⟩,⟨10,467,[66,214,229,287,322,357,444,519,594]⟩,⟨1,14,[66,103,158,229,287,357,444,519,594]⟩,⟨1,468,[66,158,229,287,337,357,444,519,594]⟩,⟨10,697,[66,214,229,287,357,425,444,519,594]⟩,⟨6,121,[7,66,158,229,287,357,444,519,594]⟩,⟨0,286,[66,158,229,287,357,444,486,519,594]⟩,⟨6,723,[66,158,206,229,287,357,444,519,594]⟩,⟨0,18,[66,158,229,287,357,444,480,519,594]⟩,⟨10,724,[66,214,229,287,357,444,519,563,594]⟩,⟨1,167,[66,141,158,229,287,357,444,519,594]⟩,⟨7,290,[66,158,229,287,357,444,519,589,594]⟩,⟨10,725,[10,66,214,229,287,357,444,519,594]⟩,⟨10,726,[66,158,200,229,287,357,444,519,594]⟩,⟨0,20,[66,158,229,287,357,444,519,594,674]⟩]⟩
def row9_238 : State := ⟨[66,118,158,229,258,287,357,444,519,594],[]⟩
def row9_239 : State := ⟨[66,158,229,265,287,357,444,519,594],[⟨10,272,[66,177,229,265,287,357,444,519,594]⟩,⟨0,2,[41,66,158,229,287,357,444,519,594]⟩,⟨0,273,[66,158,229,276,287,357,444,519,594]⟩,⟨2,269,[66,158,227,229,287,357,444,519,594]⟩,⟨0,53,[66,158,229,270,287,357,444,519,594]⟩,⟨3,61,[66,158,188,229,287,357,444,519,594]⟩,⟨1,468,[66,158,229,287,337,357,444,519,594]⟩,⟨10,714,[66,229,265,287,357,425,444,519,594]⟩,⟨6,121,[7,66,158,229,287,357,444,519,594]⟩,⟨0,716,[66,158,229,287,357,444,506,519,594]⟩,⟨6,723,[66,158,206,229,287,357,444,519,594]⟩,⟨0,290,[66,158,229,287,357,444,504,519,594]⟩,⟨11,727,[66,229,265,287,357,444,519,563,594]⟩,⟨1,167,[66,141,158,229,287,357,444,519,594]⟩,⟨0,728,[66,158,229,287,357,444,519,594,678]⟩,⟨10,729,[10,66,229,265,287,357,444,519,594]⟩,⟨10,730,[66,158,222,229,287,357,444,519,594]⟩,⟨0,20,[66,158,229,287,357,444,519,594,674]⟩]⟩
def row9_240 : State := ⟨[66,118,158,229,287,319,357,444,519,594],[]⟩
def row9_241 : State := ⟨[66,118,158,229,287,357,444,480,519,594],[]⟩
def row9_242 : State := ⟨[66,118,141,158,229,287,357,444,519,594],[⟨6,58,[66,114,158,229,287,357,444,519,594]⟩,⟨0,723,[66,148,158,229,287,357,444,519,594]⟩]⟩
def row9_243 : State := ⟨[66,118,158,229,287,357,444,498,519,594],[]⟩
def row9_244 : State := ⟨[10,66,118,158,229,287,357,444,519,594],[⟨6,731,[68,118,158,229,287,357,444,519,594]⟩,⟨0,730,[66,123,158,229,287,357,444,519,594]⟩,⟨6,732,[66,118,158,239,287,357,444,519,594]⟩,⟨6,733,[66,118,158,229,297,357,444,519,594]⟩,⟨0,734,[66,118,158,229,287,364,444,519,594]⟩,⟨0,735,[66,118,158,229,287,357,450,519,594]⟩,⟨0,736,[66,118,158,229,287,357,444,526,594]⟩,⟨0,729,[10,66,158,229,287,357,444,519,654]⟩]⟩
def row9_245 : State := ⟨[66,118,158,229,287,357,444,519,594,674],[]⟩
def row9_246 : State := ⟨[10,66,158,202,229,287,357,444,519,594],[⟨8,737,[68,158,202,229,287,357,444,519,594]⟩,⟨2,738,[66,158,203,229,287,357,444,519,594]⟩,⟨10,725,[10,66,214,229,287,357,444,519,594]⟩,⟨8,739,[66,158,202,239,287,357,444,519,594]⟩,⟨8,740,[66,158,202,229,297,357,444,519,594]⟩,⟨2,737,[66,158,202,229,287,364,444,519,594]⟩,⟨2,739,[66,158,202,229,287,357,450,519,594]⟩,⟨2,740,[66,158,202,229,287,357,444,526,594]⟩,⟨0,725,[10,66,158,229,287,357,444,519,634]⟩]⟩
def row9_247 : State := ⟨[66,118,158,229,287,357,444,519,594,681],[]⟩
def row9_248 : State := ⟨[66,118,158,220,229,287,357,444,519,594],[⟨2,741,[66,158,229,257,287,357,444,519,594]⟩]⟩
def row9_249 : State := ⟨[66,118,158,229,287,357,444,519,580,594],[⟨2,724,[66,158,229,287,357,444,557,580,594]⟩,⟨6,58,[66,114,158,229,287,357,444,519,594]⟩,⟨3,290,[66,158,229,287,357,444,519,584,594]⟩]⟩
def row9_250 : State := ⟨[66,118,158,229,284,287,357,444,519,594],[⟨1,742,[66,158,229,287,317,357,444,519,594]⟩]⟩
def row9_251 : State := ⟨[66,118,158,229,287,357,444,519,594,644],[⟨8,727,[66,158,229,319,357,444,519,594,644]⟩,⟨1,727,[66,158,229,287,357,444,519,644,654]⟩,⟨3,728,[66,158,229,287,357,444,519,594,692]⟩]⟩
def row9_252 : State := ⟨[66,158,229,287,357,444,480,498,519,594],[⟨6,59,[66,158,229,287,357,444,461,519,594]⟩,⟨0,400,[66,158,229,287,357,444,505,519,594]⟩]⟩
def row9_253 : State := ⟨[10,66,158,229,287,357,444,480,519,594],[⟨10,743,[68,158,229,287,357,444,480,519,594]⟩,⟨6,744,[66,158,239,287,357,444,480,519,594]⟩,⟨6,745,[66,158,229,297,357,444,480,519,594]⟩,⟨0,746,[66,158,229,287,364,444,480,519,594]⟩,⟨3,432,[66,158,229,287,357,450,480,519,594]⟩,⟨0,747,[66,158,229,287,357,444,480,526,594]⟩,⟨1,427,[10,66,158,229,287,357,480,519,656]⟩]⟩
def row9_254 : State := ⟨[66,158,229,287,357,444,480,519,594,674],[⟨0,60,[66,158,229,287,357,444,475,519,594]⟩,⟨1,435,[66,158,229,287,357,444,519,594,687]⟩]⟩
def row9_255 : State := ⟨[42,66,158,229,287,357,444,519,594],[⟨0,2,[41,66,158,229,287,357,444,519,594]⟩,⟨10,163,[66,159,229,287,357,444,519,594]⟩,⟨0,165,[66,158,159,229,287,357,444,519,594]⟩,⟨2,531,[42,66,159,229,287,357,444,519,594]⟩,⟨7,163,[66,158,230,287,357,444,519,594]⟩,⟨2,165,[66,158,229,230,287,357,444,519,594]⟩,⟨0,531,[42,66,158,230,287,357,444,519,594]⟩,⟨6,228,[66,158,229,288,357,444,519,594]⟩,⟨3,231,[66,158,229,287,288,357,444,519,594]⟩,⟨0,578,[42,66,158,229,288,357,444,519,594]⟩,⟨6,748,[66,158,229,287,357,379,444,519,594]⟩,⟨0,121,[0,66,158,229,287,357,444,519,594]⟩,⟨6,59,[66,158,229,287,357,444,461,519,594]⟩,⟨0,160,[42,66,158,229,287,357,465,519,594]⟩,⟨7,749,[66,158,229,287,357,444,519,544,594]⟩,⟨10,749,[66,158,229,287,357,444,519,594,621]⟩]⟩
def row9_256 : State := ⟨[42,66,158,229,287,357,444,480,519,594],[⟨10,164,[66,159,229,287,357,444,480,519,594]⟩,⟨6,514,[66,158,230,287,357,444,480,519,594]⟩,⟨6,569,[66,158,229,288,357,444,480,519,594]⟩]⟩
def row9_257 : State := ⟨[66,158,229,287,357,444,480,488,519,594],[⟨10,750,[66,158,229,287,357,438,444,480,519]⟩]⟩
def row9_258 : State := ⟨[66,129,158,229,287,357,444,498,519,594],[]⟩
def row9_259 : State := ⟨[66,158,229,287,357,444,480,505,519,594],[]⟩
def row9_260 : State := ⟨[66,89,158,229,287,357,444,519,594],[⟨0,2,[41,66,158,229,287,357,444,519,594]⟩,⟨0,751,[66,101,158,229,287,357,444,519,594]⟩,⟨0,14,[66,85,158,229,287,357,444,519,594]⟩,⟨9,430,[66,158,239,287,357,444,519,594]⟩,⟨2,434,[66,158,229,239,287,357,444,519,594]⟩,⟨0,752,[66,89,158,239,287,357,444,519,594]⟩,⟨0,433,[66,89,229,270,287,357,444,519,594]⟩,⟨3,753,[66,158,229,287,315,357,444,519,594]⟩,⟨0,469,[66,89,229,287,322,357,444,519,594]⟩,⟨0,754,[66,158,229,287,357,389,444,519,594]⟩,⟨6,688,[7,66,89,229,287,357,444,519,594]⟩,⟨0,58,[66,78,158,229,287,357,444,519,594]⟩,⟨8,721,[66,158,229,287,357,444,463,519,594]⟩,⟨1,755,[66,158,229,287,357,444,519,562,594]⟩,⟨0,244,[10,66,158,229,287,357,444,519,594]⟩,⟨10,60,[66,158,229,287,357,444,519,594,635]⟩,⟨0,428,[66,89,158,229,287,357,444,519,665]⟩]⟩
def row9_261 : State := ⟨[66,89,158,229,287,357,444,519,594,637],[⟨9,432,[66,158,239,287,357,444,519,594,637]⟩,⟨0,429,[66,89,270,287,357,444,519,594,637]⟩]⟩
def row9_262 : State := ⟨[66,158,229,287,357,444,480,519,594,687],[]⟩
def row9_263 : State := ⟨[10,66,158,229,287,357,444,498,519,594],[⟨10,756,[68,158,229,287,357,444,498,519,594]⟩,⟨9,757,[66,158,239,287,357,444,498,519,594]⟩,⟨8,758,[66,158,229,297,357,444,498,519,594]⟩,⟨0,756,[66,158,229,287,364,444,498,519,594]⟩,⟨3,757,[66,158,229,287,357,450,498,519,594]⟩,⟨2,759,[66,158,229,287,357,444,499,519,594]⟩,⟨2,758,[66,158,229,287,357,444,498,526,594]⟩]⟩
def row9_264 : State := ⟨[66,158,229,287,357,444,480,519,594,681],[⟨0,760,[66,158,229,287,357,444,474,519,594]⟩,⟨0,407,[66,158,229,287,357,444,519,594,689]⟩]⟩
def row9_265 : State := ⟨[66,158,229,287,357,444,480,519,580,594],[⟨1,761,[66,158,229,287,357,414,444,519,594]⟩,⟨1,407,[66,158,229,287,357,444,519,594,698]⟩]⟩
def row9_266 : State := ⟨[66,158,229,287,357,444,480,519,594,644],[⟨8,426,[66,229,322,357,444,480,519,594,644]⟩,⟨1,426,[66,158,229,287,357,480,519,644,656]⟩,⟨2,762,[66,158,229,287,357,441,444,519,594]⟩,⟨1,466,[66,158,229,287,357,444,519,594,697]⟩]⟩
def row9_267 : State := ⟨[66,158,229,287,364,444,519,594],[⟨0,27,[41,66,158,229,287,364,444,519,594]⟩,⟨0,223,[66,158,177,229,287,364,444,519,594]⟩,⟨2,196,[66,158,229,253,287,364,444,519,594]⟩,⟨0,330,[66,85,158,229,287,364,444,519,594]⟩,⟨4,436,[66,229,270,287,364,444,519,594]⟩,⟨0,453,[66,158,229,270,287,364,444,519,594]⟩,⟨3,196,[66,158,229,287,310,364,444,519,594]⟩,⟨1,330,[66,103,158,229,287,364,444,519,594]⟩,⟨5,436,[66,229,287,322,364,444,519,594]⟩,⟨1,453,[66,158,229,287,322,364,444,519,594]⟩,⟨4,316,[66,158,183,229,287,364,444,519,594]⟩,⟨4,411,[66,158,229,287,332,364,444,519,594]⟩,⟨0,485,[54,66,158,229,287,364,444,519,594]⟩,⟨0,763,[66,158,229,287,364,382,444,519,594]⟩,⟨10,232,[15,66,229,287,364,444,519,594]⟩,⟨10,243,[15,66,158,229,287,364,444,519,594]⟩,⟨0,218,[66,158,229,287,364,425,444,519,594]⟩,⟨10,681,[20,66,158,229,287,364,444,519,594]⟩,⟨0,764,[66,158,229,287,364,444,497,519,594]⟩,⟨11,681,[32,66,158,229,287,364,444,519,594]⟩,⟨1,764,[66,158,229,287,364,444,519,577,594]⟩,⟨0,684,[0,66,158,229,287,364,444,519,594]⟩,⟨0,702,[66,158,229,287,364,444,468,519,594]⟩,⟨0,734,[66,118,158,229,287,364,444,519,594]⟩,⟨0,746,[66,158,229,287,364,444,480,519,594]⟩,⟨2,737,[66,158,202,229,287,364,444,519,594]⟩,⟨0,756,[66,158,229,287,364,444,498,519,594]⟩,⟨3,765,[35,66,158,229,287,364,444,519,594]⟩,⟨1,766,[66,158,229,287,364,444,519,594,691]⟩,⟨10,25,[66,158,229,287,341,364,444,519,594]⟩,⟨0,767,[66,158,229,287,364,444,466,519,594]⟩,⟨1,684,[1,66,158,229,287,364,444,519,594]⟩,⟨1,702,[66,158,229,287,364,444,519,553,594]⟩,⟨1,734,[66,141,158,229,287,364,444,519,594]⟩,⟨1,746,[66,158,229,287,364,444,519,563,594]⟩,⟨2,765,[22,66,158,229,287,364,444,519,594]⟩,⟨0,766,[66,158,229,287,364,444,519,594,681]⟩,⟨3,737,[66,158,229,279,287,364,444,519,594]⟩,⟨1,756,[66,158,229,287,364,444,519,580,594]⟩,⟨1,767,[66,158,229,287,364,444,519,551,594]⟩,⟨0,313,[66,158,229,287,364,391,444,519,594]⟩,⟨0,408,[66,158,229,287,364,444,519,588,594]⟩,⟨4,640,[3,66,158,229,287,364,444,519]⟩,⟨4,649,[3,66,158,229,287,364,444,519,594]⟩,⟨0,711,[66,158,229,287,364,444,519,594,629]⟩,⟨0,768,[10,66,158,229,287,364,444,519,594]⟩,⟨0,769,[66,158,229,287,364,444,519,594,674]⟩,⟨4,731,[66,158,220,229,287,364,444,519,594]⟩,⟨0,743,[66,158,229,287,364,444,519,594,637]⟩,⟨5,731,[66,158,229,284,287,364,444,519,594]⟩,⟨1,743,[66,158,229,287,364,444,519,594,644]⟩,⟨10,718,[66,158,229,287,346,364,444,519,594]⟩,⟨0,217,[66,158,229,287,364,444,519,594,625]⟩,⟨0,327,[66,158,229,287,364,434,444,519,594]⟩,⟨0,445,[66,158,229,287,364,444,519,656]⟩,⟨0,451,[66,158,229,287,364,444,519,594,656]⟩,⟨1,327,[66,158,229,287,364,444,511,519,594]⟩,⟨1,445,[66,158,229,287,364,444,519,665]⟩,⟨1,451,[66,158,229,287,364,444,519,594,665]⟩]⟩
def row9_268 : State := ⟨[66,68,158,229,287,357,444,519,594],[⟨0,25,[41,68,158,229,287,357,444,519,594]⟩,⟨10,217,[68,158,177,229,287,357,444,519,594]⟩,⟨0,19,[48,66,158,229,287,357,444,519,594]⟩,⟨0,54,[66,158,177,229,287,357,444,519,594]⟩,⟨10,192,[68,158,229,253,287,357,444,519,594]⟩,⟨0,2,[41,66,158,229,287,357,444,519,594]⟩,⟨2,194,[66,158,229,255,287,357,444,519,594]⟩,⟨0,446,[66,68,229,270,287,357,444,519,594]⟩,⟨11,192,[68,158,229,287,310,357,444,519,594]⟩,⟨3,194,[66,158,229,287,312,357,444,519,594]⟩,⟨1,446,[66,68,229,287,322,357,444,519,594]⟩,⟨10,485,[54,68,158,229,287,357,444,519,594]⟩,⟨10,499,[68,158,229,287,357,380,444,519,594]⟩,⟨0,119,[54,66,158,229,287,357,444,519,594]⟩,⟨0,501,[66,158,229,287,357,382,444,519,594]⟩,⟨6,641,[7,66,68,229,287,357,444,519,594]⟩,⟨0,681,[0,68,158,229,287,357,444,519,594]⟩,⟨10,699,[68,158,229,287,357,444,468,519,594]⟩,⟨0,121,[0,66,158,229,287,357,444,519,594]⟩,⟨8,704,[66,158,229,287,357,444,470,519,594]⟩,⟨1,681,[1,68,158,229,287,357,444,519,594]⟩,⟨11,699,[68,158,229,287,357,444,519,553,594]⟩,⟨1,121,[1,66,158,229,287,357,444,519,594]⟩,⟨9,704,[66,158,229,287,357,444,519,555,594]⟩,⟨4,647,[3,68,158,229,287,357,444,519,594]⟩,⟨10,218,[68,158,229,287,357,444,519,594,629]⟩,⟨0,585,[12,66,158,229,287,357,444,519]⟩,⟨0,586,[12,66,158,229,287,357,444,519,594]⟩,⟨0,233,[12,66,68,158,229,287,357,444,519]⟩,⟨10,7,[66,158,229,287,357,444,519,594,629]⟩,⟨0,437,[66,68,158,229,287,357,444,519,656]⟩,⟨1,437,[66,68,158,229,287,357,444,519,665]⟩]⟩
def row9_269 : State := ⟨[10,66,158,229,287,364,444,519,594],[⟨0,770,[68,158,229,287,364,444,519,594]⟩,⟨0,771,[66,68,158,229,287,364,444,519,594]⟩,⟨0,772,[10,68,158,229,287,364,444,519,594]⟩,⟨1,773,[66,158,239,287,364,444,519,594]⟩,⟨2,774,[66,158,229,239,287,364,444,519,594]⟩,⟨1,775,[10,66,158,239,287,364,444,519,594]⟩,⟨0,438,[10,66,229,270,287,364,444,519,594]⟩,⟨0,773,[66,158,229,297,364,444,519,594]⟩,⟨3,774,[66,158,229,287,297,364,444,519,594]⟩,⟨0,775,[10,66,158,229,297,364,444,519,594]⟩,⟨1,438,[10,66,229,287,322,364,444,519,594]⟩,⟨10,776,[10,15,66,229,287,364,444,519,594]⟩,⟨1,777,[66,158,229,287,364,450,519,594]⟩,⟨0,778,[66,158,229,287,364,444,450,519,594]⟩,⟨1,779,[10,66,158,229,287,364,450,519,594]⟩,⟨0,777,[66,158,229,287,364,444,526,594]⟩,⟨1,778,[66,158,229,287,364,444,519,526,594]⟩,⟨0,779,[10,66,158,229,287,364,444,526,594]⟩,⟨4,642,[3,10,66,158,229,287,364,444,519]⟩,⟨0,447,[10,66,158,229,287,364,444,519,656]⟩,⟨1,447,[10,66,158,229,287,364,444,519,665]⟩]⟩
def row9_270 : State := ⟨[10,66,68,158,229,287,357,444,519,594],[⟨1,780,[66,68,158,239,287,357,444,519,594]⟩,⟨0,780,[66,68,158,229,297,357,444,519,594]⟩,⟨0,771,[66,68,158,229,287,364,444,519,594]⟩,⟨1,781,[66,68,158,229,287,357,450,519,594]⟩,⟨0,781,[66,68,158,229,287,357,444,526,594]⟩,⟨4,638,[3,10,68,158,229,287,357,444,519]⟩,⟨0,225,[10,12,66,158,229,287,357,444,519]⟩]⟩
def row9_271 : State := ⟨[66,158,229,287,357,444,519,604],[⟨0,28,[41,66,158,229,287,357,444,519,604]⟩,⟨0,198,[66,158,177,229,287,357,444,519,604]⟩,⟨2,224,[66,158,229,253,287,357,444,519,604]⟩,⟨0,332,[66,85,158,229,287,357,444,519,604]⟩,⟨7,441,[66,158,270,287,357,444,519,604]⟩,⟨0,455,[66,158,229,270,287,357,444,519,604]⟩,⟨3,197,[66,158,229,287,310,357,444,519,604]⟩,⟨1,317,[66,103,158,229,287,357,444,519,604]⟩,⟨1,412,[66,158,229,287,322,357,444,519,604]⟩,⟨4,331,[66,158,183,229,287,357,444,519,604]⟩,⟨4,454,[66,158,229,287,332,357,444,519,604]⟩,⟨0,486,[54,66,158,229,287,357,444,519,604]⟩,⟨0,500,[66,158,229,287,357,380,444,519,604]⟩,⟨7,683,[7,66,158,229,287,357,444,519,604]⟩,⟨0,701,[66,158,229,287,357,425,444,519,604]⟩,⟨8,648,[20,66,158,229,287,357,444,519,604]⟩,⟨2,713,[66,158,229,287,357,444,494,519,604]⟩,⟨9,682,[32,66,158,229,287,357,444,519,604]⟩,⟨3,700,[66,158,229,287,357,444,519,574,604]⟩,⟨0,686,[0,66,158,229,287,357,444,519,604]⟩,⟨0,705,[66,158,229,287,357,444,468,519,604]⟩,⟨0,740,[66,118,158,229,287,357,444,519,604]⟩,⟨0,758,[66,158,229,287,357,444,480,519,604]⟩,⟨2,736,[66,158,202,229,287,357,444,519,604]⟩,⟨2,747,[66,158,229,287,357,444,498,519,604]⟩,⟨3,782,[35,66,158,229,287,357,444,519,604]⟩,⟨0,783,[66,158,229,287,357,444,519,604,691]⟩,⟨7,26,[66,158,229,287,341,357,444,519,604]⟩,⟨6,195,[66,158,229,287,357,444,465,519,604]⟩,⟨1,651,[1,66,158,229,287,357,444,519,604]⟩,⟨1,712,[66,158,229,287,357,444,519,553,604]⟩,⟨1,733,[66,141,158,229,287,357,444,519,604]⟩,⟨1,745,[66,158,229,287,357,444,519,563,604]⟩,⟨2,784,[22,66,158,229,287,357,444,519,604]⟩,⟨0,785,[66,158,229,287,357,444,519,604,681]⟩,⟨3,732,[66,158,229,279,287,357,444,519,604]⟩,⟨3,744,[66,158,229,287,357,444,519,580,604]⟩,⟨7,222,[66,158,229,287,357,444,519,549,604]⟩,⟨7,329,[66,158,229,287,357,391,444,519,604]⟩,⟨7,452,[66,158,229,287,357,444,519,588,604]⟩,⟨4,685,[3,66,158,229,287,357,444,519,604]⟩,⟨0,786,[66,158,229,287,357,444,519,604,632]⟩,⟨0,787,[10,66,158,229,287,357,444,519,604]⟩,⟨0,788,[66,158,229,287,357,444,519,604,679]⟩,⟨4,462,[66,158,225,229,287,357,444,519,604]⟩,⟨0,432,[66,158,229,287,357,444,519,604,637]⟩,⟨5,739,[66,158,229,284,287,357,444,519,604]⟩,⟨0,789,[66,158,229,287,357,444,519,604,648]⟩,⟨0,790,[66,158,229,287,357,444,519,604,627]⟩,⟨8,315,[66,158,229,287,357,434,444,519,604]⟩,⟨0,791,[66,158,229,287,357,444,519,604,659]⟩,⟨9,752,[66,158,229,287,357,444,513,519,604]⟩,⟨0,431,[66,158,229,287,357,444,519,604,665]⟩]⟩
def row9_272 : State := ⟨[66,158,166,229,287,357,444,519,594],[⟨4,26,[41,66,166,229,287,357,444,519,594]⟩,⟨11,193,[66,166,177,229,287,357,444,519,594]⟩,⟨0,2,[41,66,158,229,287,357,444,519,594]⟩,⟨0,194,[66,158,180,229,287,357,444,519,594]⟩,⟨2,328,[66,85,166,229,287,357,444,519,594]⟩,⟨11,431,[66,166,229,270,287,357,444,519,594]⟩,⟨2,177,[66,93,158,229,287,357,444,519,594]⟩,⟨0,53,[66,158,229,270,287,357,444,519,594]⟩,⟨3,315,[66,103,166,229,287,357,444,519,594]⟩,⟨11,409,[66,166,229,287,322,357,444,519,594]⟩,⟨1,14,[66,103,158,229,287,357,444,519,594]⟩,⟨1,410,[66,158,229,287,326,357,444,519,594]⟩,⟨7,685,[7,66,166,229,287,357,444,519,594]⟩,⟨11,703,[66,166,229,287,357,425,444,519,594]⟩,⟨6,121,[7,66,158,229,287,357,444,519,594]⟩,⟨0,704,[66,158,229,287,357,429,444,519,594]⟩,⟨6,739,[66,118,166,229,287,357,444,519,594]⟩,⟨11,757,[66,166,229,287,357,444,480,519,594]⟩,⟨0,167,[66,118,158,229,287,357,444,519,594]⟩,⟨0,759,[66,158,229,287,357,444,484,519,594]⟩,⟨7,735,[66,141,166,229,287,357,444,519,594]⟩,⟨11,432,[66,166,229,287,357,444,519,563,594]⟩,⟨7,730,[66,145,158,229,287,357,444,519,594]⟩,⟨1,18,[66,158,229,287,357,444,519,563,594]⟩,⟨11,787,[10,66,166,229,287,357,444,519,594]⟩,⟨11,792,[66,166,229,287,357,444,519,594,674]⟩,⟨0,244,[10,66,158,229,287,357,444,519,594]⟩,⟨0,793,[66,158,229,287,357,444,519,594,679]⟩,⟨0,442,[66,158,166,229,287,357,444,594,665]⟩]⟩
def row9_273 : State := ⟨[10,66,158,229,287,357,444,526,594],[⟨10,773,[68,158,229,287,357,444,526,594]⟩,⟨0,781,[66,68,158,229,287,357,444,526,594]⟩,⟨10,775,[10,68,158,229,287,357,444,526,594]⟩,⟨1,794,[66,158,239,287,357,444,526,594]⟩,⟨2,795,[66,158,229,239,287,357,444,526,594]⟩,⟨1,796,[10,66,158,239,287,357,444,526,594]⟩,⟨10,443,[10,66,229,270,287,357,444,526,594]⟩,⟨0,797,[66,158,229,297,357,444,526,594]⟩,⟨3,798,[66,158,229,287,297,357,444,526,594]⟩,⟨0,799,[10,66,158,229,297,357,444,526,594]⟩,⟨10,439,[10,66,229,287,322,357,444,526,594]⟩,⟨0,777,[66,158,229,287,364,444,526,594]⟩,⟨10,780,[66,158,229,287,357,364,444,526,594]⟩,⟨0,779,[10,66,158,229,287,364,444,526,594]⟩,⟨6,639,[7,10,66,229,287,357,444,526,594]⟩,⟨4,800,[66,158,229,287,357,450,526,594]⟩,⟨8,801,[66,158,229,287,357,444,450,526,594]⟩,⟨0,802,[10,66,158,229,287,357,450,526,594]⟩,⟨4,646,[3,10,66,158,229,287,357,444,526]⟩,⟨0,450,[10,66,158,229,287,357,444,526,656]⟩,⟨0,448,[10,66,158,229,287,357,444,526,665]⟩]⟩
def row9_274 : State := ⟨[10,66,158,229,239,287,357,444,519,594],[⟨10,778,[68,158,229,239,287,357,444,519,594]⟩,⟨11,448,[10,66,239,270,287,357,444,519,594]⟩,⟨10,464,[10,66,229,270,287,357,444,519,594]⟩,⟨2,801,[66,158,229,239,297,357,444,519,594]⟩,⟨2,774,[66,158,229,239,287,364,444,519,594]⟩,⟨2,798,[66,158,229,239,287,357,450,519,594]⟩,⟨2,795,[66,158,229,239,287,357,444,526,594]⟩]⟩
def row9_275 : State := ⟨[10,22,66,158,229,287,357,444,519,594],[⟨0,803,[25,66,158,229,287,357,444,519,594]⟩,⟨9,765,[22,68,158,229,287,357,444,519,594]⟩,⟨11,765,[10,72,158,229,287,357,444,519,594]⟩,⟨11,787,[10,66,166,229,287,357,444,519,594]⟩,⟨9,787,[22,66,158,239,287,357,444,519,594]⟩,⟨9,449,[10,22,66,270,287,357,444,519,594]⟩,⟨7,782,[22,66,158,229,297,357,444,519,594]⟩,⟨10,782,[10,66,158,229,304,357,444,519,594]⟩,⟨2,765,[22,66,158,229,287,364,444,519,594]⟩,⟨0,765,[10,66,158,229,287,367,444,519,594]⟩,⟨4,782,[22,66,158,229,287,357,450,519,594]⟩,⟨1,782,[10,66,158,229,287,357,456,519,594]⟩,⟨2,787,[22,66,158,229,287,357,444,526,594]⟩,⟨0,787,[10,66,158,229,287,357,444,519,604]⟩,⟨0,449,[10,22,66,158,229,287,357,444,665]⟩]⟩
def row9_276 : State := ⟨[10,66,158,229,287,357,444,519,594,681],[⟨11,766,[68,158,229,287,357,444,519,594,681]⟩,⟨9,792,[66,158,239,287,357,444,519,594,681]⟩,⟨8,783,[66,158,229,297,357,444,519,594,681]⟩,⟨0,766,[66,158,229,287,364,444,519,594,681]⟩,⟨3,783,[66,158,229,287,357,450,519,594,681]⟩,⟨2,792,[66,158,229,287,357,444,526,594,681]⟩,⟨2,793,[66,158,229,287,357,444,519,594,682]⟩]⟩
def row9_277 : State := ⟨[10,66,158,229,287,357,444,519,594,674],[⟨10,769,[68,158,229,287,357,444,519,594,674]⟩,⟨9,785,[66,158,239,287,357,444,519,594,674]⟩,⟨8,785,[66,158,229,297,357,444,519,594,674]⟩,⟨0,769,[66,158,229,287,364,444,519,594,674]⟩,⟨3,785,[66,158,229,287,357,450,519,594,674]⟩,⟨2,785,[66,158,229,287,357,444,526,594,674]⟩]⟩
def row9_278 : State := ⟨[66,158,229,287,357,444,519,594,674,681],[⟨0,804,[66,158,229,287,357,444,519,594,672]⟩,⟨0,466,[66,158,229,287,357,444,519,594,686]⟩]⟩
def row9_279 : State := ⟨[42,66,158,229,287,357,444,519,594,691],[⟨10,522,[66,159,229,287,357,444,519,594,691]⟩,⟨7,522,[66,158,230,287,357,444,519,594,691]⟩,⟨6,229,[66,158,229,288,357,444,519,594,691]⟩]⟩
def row9_280 : State := ⟨[66,158,229,287,357,444,519,594,674,704],[]⟩
def row9_281 : State := ⟨[66,153,158,229,287,357,444,519,594],[⟨0,2,[41,66,158,229,287,357,444,519,594]⟩,⟨0,401,[66,158,173,229,287,357,444,519,594]⟩,⟨0,14,[66,85,158,229,287,357,444,519,594]⟩,⟨2,402,[66,158,229,269,287,357,444,519,594]⟩,⟨1,14,[66,103,158,229,287,357,444,519,594]⟩,⟨3,402,[66,158,229,287,319,357,444,519,594]⟩,⟨0,805,[66,158,229,287,357,424,444,519,594]⟩,⟨0,167,[66,118,158,229,287,357,444,519,594]⟩,⟨6,60,[66,158,229,287,357,444,478,519,594]⟩,⟨1,167,[66,141,158,229,287,357,444,519,594]⟩,⟨7,60,[66,158,229,287,357,444,519,560,594]⟩,⟨0,806,[66,158,229,287,357,444,519,594,673]⟩]⟩
def row9_282 : State := ⟨[66,153,158,229,287,357,444,519,594,681],[]⟩
def row9_283 : State := ⟨[66,158,229,287,357,444,519,594,674,680],[]⟩
def layer9 : Array State := #[row9_0,row9_1,row9_2,row9_3,row9_4,row9_5,row9_6,row9_7,row9_8,row9_9,row9_10,row9_11,row9_12,row9_13,row9_14,row9_15,row9_16,row9_17,row9_18,row9_19,row9_20,row9_21,row9_22,row9_23,row9_24,row9_25,row9_26,row9_27,row9_28,row9_29,row9_30,row9_31,row9_32,row9_33,row9_34,row9_35,row9_36,row9_37,row9_38,row9_39,row9_40,row9_41,row9_42,row9_43,row9_44,row9_45,row9_46,row9_47,row9_48,row9_49,row9_50,row9_51,row9_52,row9_53,row9_54,row9_55,row9_56,row9_57,row9_58,row9_59,row9_60,row9_61,row9_62,row9_63,row9_64,row9_65,row9_66,row9_67,row9_68,row9_69,row9_70,row9_71,row9_72,row9_73,row9_74,row9_75,row9_76,row9_77,row9_78,row9_79,row9_80,row9_81,row9_82,row9_83,row9_84,row9_85,row9_86,row9_87,row9_88,row9_89,row9_90,row9_91,row9_92,row9_93,row9_94,row9_95,row9_96,row9_97,row9_98,row9_99,row9_100,row9_101,row9_102,row9_103,row9_104,row9_105,row9_106,row9_107,row9_108,row9_109,row9_110,row9_111,row9_112,row9_113,row9_114,row9_115,row9_116,row9_117,row9_118,row9_119,row9_120,row9_121,row9_122,row9_123,row9_124,row9_125,row9_126,row9_127,row9_128,row9_129,row9_130,row9_131,row9_132,row9_133,row9_134,row9_135,row9_136,row9_137,row9_138,row9_139,row9_140,row9_141,row9_142,row9_143,row9_144,row9_145,row9_146,row9_147,row9_148,row9_149,row9_150,row9_151,row9_152,row9_153,row9_154,row9_155,row9_156,row9_157,row9_158,row9_159,row9_160,row9_161,row9_162,row9_163,row9_164,row9_165,row9_166,row9_167,row9_168,row9_169,row9_170,row9_171,row9_172,row9_173,row9_174,row9_175,row9_176,row9_177,row9_178,row9_179,row9_180,row9_181,row9_182,row9_183,row9_184,row9_185,row9_186,row9_187,row9_188,row9_189,row9_190,row9_191,row9_192,row9_193,row9_194,row9_195,row9_196,row9_197,row9_198,row9_199,row9_200,row9_201,row9_202,row9_203,row9_204,row9_205,row9_206,row9_207,row9_208,row9_209,row9_210,row9_211,row9_212,row9_213,row9_214,row9_215,row9_216,row9_217,row9_218,row9_219,row9_220,row9_221,row9_222,row9_223,row9_224,row9_225,row9_226,row9_227,row9_228,row9_229,row9_230,row9_231,row9_232,row9_233,row9_234,row9_235,row9_236,row9_237,row9_238,row9_239,row9_240,row9_241,row9_242,row9_243,row9_244,row9_245,row9_246,row9_247,row9_248,row9_249,row9_250,row9_251,row9_252,row9_253,row9_254,row9_255,row9_256,row9_257,row9_258,row9_259,row9_260,row9_261,row9_262,row9_263,row9_264,row9_265,row9_266,row9_267,row9_268,row9_269,row9_270,row9_271,row9_272,row9_273,row9_274,row9_275,row9_276,row9_277,row9_278,row9_279,row9_280,row9_281,row9_282,row9_283]
def row10_0 : State := ⟨[41,66,158,229,287,357,444,519,594],[⟨0,0,[41,66,158,177,229,287,357,444,519,594]⟩,⟨2,0,[41,66,158,229,253,287,357,444,519,594]⟩,⟨0,1,[41,66,85,158,229,287,357,444,519,594]⟩,⟨0,2,[41,66,158,229,270,287,357,444,519,594]⟩,⟨3,0,[41,66,158,229,287,310,357,444,519,594]⟩,⟨1,1,[41,66,103,158,229,287,357,444,519,594]⟩,⟨1,2,[41,66,158,229,287,322,357,444,519,594]⟩,⟨4,1,[41,66,158,183,229,287,357,444,519,594]⟩,⟨4,2,[41,66,158,229,287,332,357,444,519,594]⟩,⟨6,3,[66,158,229,287,357,378,444,519,594]⟩,⟨0,4,[41,66,158,229,287,357,378,444,519,594]⟩,⟨0,5,[41,54,66,158,229,287,357,444,519,594]⟩,⟨0,6,[41,66,158,229,287,357,380,444,519,594]⟩,⟨6,7,[7,41,66,158,229,287,357,444,519,594]⟩,⟨0,8,[41,66,158,229,287,357,425,444,519,594]⟩,⟨8,7,[20,41,66,158,229,287,357,444,519,594]⟩,⟨2,8,[41,66,158,229,287,357,444,494,519,594]⟩,⟨9,7,[32,41,66,158,229,287,357,444,519,594]⟩,⟨3,8,[41,66,158,229,287,357,444,519,574,594]⟩,⟨6,9,[66,158,229,287,357,444,461,519,594]⟩,⟨0,10,[41,66,158,229,287,357,444,461,519,594]⟩,⟨0,11,[0,41,66,158,229,287,357,444,519,594]⟩,⟨0,12,[41,66,158,229,287,357,444,468,519,594]⟩,⟨0,13,[41,66,118,158,229,287,357,444,519,594]⟩,⟨0,14,[41,66,158,229,287,357,444,480,519,594]⟩,⟨2,13,[41,66,158,202,229,287,357,444,519,594]⟩,⟨2,14,[41,66,158,229,287,357,444,498,519,594]⟩,⟨3,15,[35,41,66,158,229,287,357,444,519,594]⟩,⟨3,16,[41,66,158,229,287,357,444,519,594,691]⟩,⟨0,17,[41,66,158,229,287,341,357,444,519,594]⟩,⟨0,18,[41,66,158,229,287,357,444,465,519,594]⟩,⟨7,9,[66,158,229,287,357,444,519,543,594]⟩,⟨1,10,[41,66,158,229,287,357,444,519,543,594]⟩,⟨1,11,[1,41,66,158,229,287,357,444,519,594]⟩,⟨1,12,[41,66,158,229,287,357,444,519,553,594]⟩,⟨1,13,[41,66,141,158,229,287,357,444,519,594]⟩,⟨1,14,[41,66,158,229,287,357,444,519,563,594]⟩,⟨2,15,[22,41,66,158,229,287,357,444,519,594]⟩,⟨2,16,[41,66,158,229,287,357,444,519,594,681]⟩,⟨3,13,[41,66,158,229,279,287,357,444,519,594]⟩,⟨3,14,[41,66,158,229,287,357,444,519,580,594]⟩,⟨1,18,[41,66,158,229,287,357,444,519,549,594]⟩,⟨0,19,[41,66,158,229,287,357,391,444,519,594]⟩,⟨0,20,[41,66,158,229,287,357,444,519,588,594]⟩,⟨10,9,[66,158,229,287,357,444,519,594,620]⟩,⟨4,10,[41,66,158,229,287,357,444,519,594,620]⟩,⟨4,11,[3,41,66,158,229,287,357,444,519,594]⟩,⟨4,12,[41,66,158,229,287,357,444,519,594,629]⟩,⟨0,15,[10,41,66,158,229,287,357,444,519,594]⟩,⟨0,16,[41,66,158,229,287,357,444,519,594,674]⟩,⟨4,13,[41,66,158,220,229,287,357,444,519,594]⟩,⟨4,14,[41,66,158,229,287,357,444,519,594,637]⟩,⟨5,13,[41,66,158,229,284,287,357,444,519,594]⟩,⟨5,14,[41,66,158,229,287,357,444,519,594,644]⟩,⟨4,18,[41,66,158,229,287,357,444,519,594,625]⟩,⟨2,19,[41,66,158,229,287,357,434,444,519,594]⟩,⟨2,20,[41,66,158,229,287,357,444,519,594,656]⟩,⟨3,19,[41,66,158,229,287,357,444,511,519,594]⟩,⟨3,20,[41,66,158,229,287,357,444,519,594,665]⟩]⟩
def row10_1 : State := ⟨[66,158,177,229,287,357,444,519,594],[⟨0,0,[41,66,158,177,229,287,357,444,519,594]⟩,⟨0,21,[66,158,177,229,253,287,357,444,519,594]⟩,⟨0,22,[66,85,158,177,229,287,357,444,519,594]⟩,⟨10,23,[66,177,229,270,287,357,444,519,594]⟩,⟨0,24,[66,158,177,229,270,287,357,444,519,594]⟩,⟨0,25,[66,85,158,229,287,357,444,519,594]⟩,⟨0,26,[66,158,229,278,287,357,444,519,594]⟩,⟨0,27,[66,158,177,229,278,287,357,444,519,594]⟩,⟨1,21,[66,158,177,229,287,310,357,444,519,594]⟩,⟨1,22,[66,103,158,177,229,287,357,444,519,594]⟩,⟨11,23,[66,177,229,287,322,357,444,519,594]⟩,⟨1,24,[66,158,177,229,287,322,357,444,519,594]⟩,⟨1,25,[66,103,158,229,287,357,444,519,594]⟩,⟨1,26,[66,158,229,287,329,357,444,519,594]⟩,⟨1,27,[66,158,177,229,287,329,357,444,519,594]⟩,⟨4,28,[66,158,177,183,229,287,357,444,519,594]⟩,⟨0,29,[66,158,177,229,287,332,357,444,519,594]⟩,⟨0,30,[54,66,158,177,229,287,357,444,519,594]⟩,⟨6,31,[158,177,229,287,357,380,444,519,594]⟩,⟨0,32,[66,158,177,229,287,357,380,444,519,594]⟩,⟨6,33,[7,66,177,229,287,357,444,519,594]⟩,⟨6,34,[7,66,158,177,229,287,357,444,519,594]⟩,⟨0,35,[66,158,177,229,287,357,425,444,519,594]⟩,⟨6,36,[58,66,158,229,287,357,444,519,594]⟩,⟨6,37,[58,66,158,177,229,287,357,444,519,594]⟩,⟨0,38,[66,158,229,287,357,428,444,519,594]⟩,⟨0,39,[66,158,177,229,287,357,428,444,519,594]⟩,⟨8,40,[20,66,158,177,229,287,357,444,519,594]⟩,⟨0,41,[66,158,177,229,287,357,444,494,519,594]⟩,⟨9,40,[32,66,158,177,229,287,357,444,519,594]⟩,⟨1,41,[66,158,177,229,287,357,444,519,574,594]⟩,⟨0,42,[0,66,158,177,229,287,357,444,519,594]⟩,⟨0,43,[66,158,177,229,287,357,444,468,519,594]⟩,⟨0,44,[66,118,158,177,229,287,357,444,519,594]⟩,⟨10,45,[66,177,229,287,357,444,480,519,594]⟩,⟨0,46,[66,158,177,229,287,357,444,480,519,594]⟩,⟨0,47,[66,119,158,229,287,357,444,519,594]⟩,⟨0,48,[66,119,158,177,229,287,357,444,519,594]⟩,⟨0,49,[66,158,229,287,357,444,488,519,594]⟩,⟨0,50,[66,158,177,229,287,357,444,488,519,594]⟩,⟨2,51,[66,158,177,202,229,287,357,444,519,594]⟩,⟨0,52,[66,158,177,229,287,357,444,498,519,594]⟩,⟨3,53,[35,66,158,177,229,287,357,444,519,594]⟩,⟨1,54,[66,158,177,229,287,357,444,519,594,691]⟩,⟨6,18,[66,158,177,229,287,341,357,444,519,594]⟩,⟨0,55,[66,158,177,229,287,357,444,465,519,594]⟩,⟨1,42,[1,66,158,177,229,287,357,444,519,594]⟩,⟨1,43,[66,158,177,229,287,357,444,519,553,594]⟩,⟨1,44,[66,141,158,177,229,287,357,444,519,594]⟩,⟨11,45,[66,177,229,287,357,444,519,563,594]⟩,⟨1,46,[66,158,177,229,287,357,444,519,563,594]⟩,⟨1,47,[66,143,158,229,287,357,444,519,594]⟩,⟨1,48,[66,143,158,177,229,287,357,444,519,594]⟩,⟨1,49,[66,158,229,287,357,444,519,569,594]⟩,⟨1,50,[66,158,177,229,287,357,444,519,569,594]⟩,⟨2,53,[22,66,158,177,229,287,357,444,519,594]⟩,⟨0,54,[66,158,177,229,287,357,444,519,594,681]⟩,⟨3,51,[66,158,177,229,279,287,357,444,519,594]⟩,⟨1,52,[66,158,177,229,287,357,444,519,580,594]⟩,⟨1,55,[66,158,177,229,287,357,444,519,549,594]⟩,⟨6,56,[66,158,177,229,287,357,391,444,519,594]⟩,⟨0,57,[66,158,177,229,287,357,444,519,588,594]⟩,⟨4,58,[3,66,158,177,229,287,357,444,519,594]⟩,⟨10,59,[158,177,229,287,357,444,519,594,629]⟩,⟨0,60,[66,158,177,229,287,357,444,519,594,629]⟩,⟨0,61,[10,66,158,177,229,287,357,444,519,594]⟩,⟨10,62,[66,177,229,287,357,444,519,594,674]⟩,⟨0,63,[66,158,177,229,287,357,444,519,594,674]⟩,⟨0,64,[12,66,158,229,287,357,444,519]⟩,⟨0,65,[12,66,158,229,287,357,444,519,594]⟩,⟨0,66,[12,66,158,177,229,287,357,444,519]⟩,⟨0,67,[12,66,158,177,229,287,357,444,519,594]⟩,⟨0,68,[66,158,229,287,357,444,519,594,704]⟩,⟨0,69,[66,158,177,229,287,357,444,519,594,704]⟩,⟨4,70,[66,158,177,220,229,287,357,444,519,594]⟩,⟨0,71,[66,158,177,229,287,357,444,519,594,637]⟩,⟨5,70,[66,158,177,229,284,287,357,444,519,594]⟩,⟨1,71,[66,158,177,229,287,357,444,519,594,644]⟩,⟨0,72,[66,158,177,229,287,357,444,519,594,625]⟩,⟨8,73,[66,158,177,229,287,357,434,444,519,594]⟩,⟨0,74,[66,158,177,229,287,357,444,519,594,656]⟩,⟨9,73,[66,158,177,229,287,357,444,511,519,594]⟩,⟨1,74,[66,158,177,229,287,357,444,519,594,665]⟩]⟩
def row10_2 : State := ⟨[66,85,158,229,287,357,444,519,594],[⟨0,75,[41,66,158,229,287,357,444,519,594]⟩,⟨0,1,[41,66,85,158,229,287,357,444,519,594]⟩,⟨0,76,[66,98,158,229,287,357,444,519,594]⟩,⟨0,77,[66,85,98,158,229,287,357,444,519,594]⟩,⟨0,22,[66,85,158,177,229,287,357,444,519,594]⟩,⟨2,22,[66,85,158,229,253,287,357,444,519,594]⟩,⟨0,78,[66,85,158,229,270,287,357,444,519,594]⟩,⟨0,28,[66,85,158,229,287,310,357,444,519,594]⟩,⟨3,79,[66,158,229,287,313,357,444,519,594]⟩,⟨0,80,[66,85,158,229,287,313,357,444,519,594]⟩,⟨0,81,[66,85,103,158,229,287,357,444,519,594]⟩,⟨0,82,[66,85,158,229,287,322,357,444,519,594]⟩,⟨2,81,[66,85,158,183,229,287,357,444,519,594]⟩,⟨2,82,[66,85,158,229,287,332,357,444,519,594]⟩,⟨0,83,[54,66,85,158,229,287,357,444,519,594]⟩,⟨0,84,[66,85,158,229,287,357,380,444,519,594]⟩,⟨0,85,[66,158,229,287,357,387,444,519,594]⟩,⟨0,86,[66,85,158,229,287,357,387,444,519,594]⟩,⟨6,87,[7,66,85,158,229,287,357,444,519,594]⟩,⟨0,88,[66,85,158,229,287,357,425,444,519,594]⟩,⟨8,87,[20,66,85,158,229,287,357,444,519,594]⟩,⟨2,88,[66,85,158,229,287,357,444,494,519,594]⟩,⟨9,89,[32,66,85,158,229,287,357,444,519,594]⟩,⟨0,90,[66,85,158,229,287,357,444,519,574,594]⟩,⟨0,91,[0,66,85,158,229,287,357,444,519,594]⟩,⟨0,92,[66,85,158,229,287,357,444,468,519,594]⟩,⟨0,93,[66,78,158,229,287,357,444,519,594]⟩,⟨0,94,[66,78,85,158,229,287,357,444,519,594]⟩,⟨6,9,[66,158,229,287,357,444,461,519,594]⟩,⟨0,95,[66,85,158,229,287,357,444,461,519,594]⟩,⟨0,96,[66,85,118,158,229,287,357,444,519,594]⟩,⟨0,97,[66,85,158,229,287,357,444,480,519,594]⟩,⟨2,96,[66,85,158,202,229,287,357,444,519,594]⟩,⟨2,97,[66,85,158,229,287,357,444,498,519,594]⟩,⟨3,98,[35,66,85,158,229,287,357,444,519,594]⟩,⟨0,99,[66,85,158,229,287,357,444,519,594,691]⟩,⟨6,19,[66,85,158,229,287,341,357,444,519,594]⟩,⟨0,56,[66,85,158,229,287,357,444,465,519,594]⟩,⟨1,100,[1,66,85,158,229,287,357,444,519,594]⟩,⟨0,101,[66,85,158,229,287,357,444,519,553,594]⟩,⟨7,102,[66,158,229,287,357,444,519,560,594]⟩,⟨0,103,[66,85,158,229,287,357,444,519,560,594]⟩,⟨0,104,[66,85,141,158,229,287,357,444,519,594]⟩,⟨0,105,[66,85,158,229,287,357,444,519,563,594]⟩,⟨2,106,[22,66,85,158,229,287,357,444,519,594]⟩,⟨2,107,[66,85,158,229,287,357,444,519,594,681]⟩,⟨0,108,[66,85,158,229,279,287,357,444,519,594]⟩,⟨0,109,[66,85,158,229,287,357,444,519,580,594]⟩,⟨0,73,[66,85,158,229,287,357,444,519,549,594]⟩,⟨0,110,[66,85,158,229,287,357,391,444,519,594]⟩,⟨0,111,[66,85,158,229,287,357,444,519,588,594]⟩,⟨4,100,[3,66,85,158,229,287,357,444,519,594]⟩,⟨2,101,[66,85,158,229,287,357,444,519,594,629]⟩,⟨10,102,[66,158,229,287,357,444,519,594,635]⟩,⟨2,103,[66,85,158,229,287,357,444,519,594,635]⟩,⟨0,106,[10,66,85,158,229,287,357,444,519,594]⟩,⟨0,107,[66,85,158,229,287,357,444,519,594,674]⟩,⟨2,104,[66,85,158,220,229,287,357,444,519,594]⟩,⟨2,105,[66,85,158,229,287,357,444,519,594,637]⟩,⟨2,108,[66,85,158,229,284,287,357,444,519,594]⟩,⟨2,109,[66,85,158,229,287,357,444,519,594,644]⟩,⟨2,73,[66,85,158,229,287,357,444,519,594,625]⟩,⟨2,110,[66,85,158,229,287,357,434,444,519,594]⟩,⟨2,111,[66,85,158,229,287,357,444,519,594,656]⟩,⟨0,112,[66,85,158,229,287,357,444,511,519,594]⟩,⟨0,113,[66,85,158,229,287,357,444,519,594,665]⟩]⟩
def row10_3 : State := ⟨[66,158,229,270,287,357,444,519,594],[⟨0,2,[41,66,158,229,270,287,357,444,519,594]⟩,⟨10,23,[66,177,229,270,287,357,444,519,594]⟩,⟨0,24,[66,158,177,229,270,287,357,444,519,594]⟩,⟨7,23,[66,158,253,270,287,357,444,519,594]⟩,⟨2,24,[66,158,229,253,270,287,357,444,519,594]⟩,⟨0,78,[66,85,158,229,270,287,357,444,519,594]⟩,⟨0,75,[41,66,158,229,287,357,444,519,594]⟩,⟨0,26,[66,158,229,278,287,357,444,519,594]⟩,⟨0,114,[66,158,229,270,278,287,357,444,519,594]⟩,⟨3,29,[66,158,229,270,287,310,357,444,519,594]⟩,⟨1,82,[66,103,158,229,270,287,357,444,519,594]⟩,⟨0,115,[66,158,229,270,287,322,357,444,519,594]⟩,⟨4,82,[66,158,183,229,270,287,357,444,519,594]⟩,⟨2,115,[66,158,229,270,287,332,357,444,519,594]⟩,⟨3,116,[66,158,188,229,287,357,444,519,594]⟩,⟨3,117,[66,158,188,229,270,287,357,444,519,594]⟩,⟨0,118,[66,158,229,287,339,357,444,519,594]⟩,⟨0,119,[66,158,229,270,287,339,357,444,519,594]⟩,⟨0,120,[54,66,158,229,270,287,357,444,519,594]⟩,⟨0,121,[66,158,229,270,287,357,380,444,519,594]⟩,⟨6,122,[7,66,158,229,270,287,357,444,519,594]⟩,⟨10,123,[66,229,270,287,357,425,444,519,594]⟩,⟨0,124,[66,158,229,270,287,357,425,444,519,594]⟩,⟨8,122,[20,66,158,229,270,287,357,444,519,594]⟩,⟨7,123,[66,158,270,287,357,444,494,519,594]⟩,⟨2,124,[66,158,229,270,287,357,444,494,519,594]⟩,⟨6,125,[21,66,158,229,287,357,444,519,594]⟩,⟨6,126,[21,66,158,229,270,287,357,444,519,594]⟩,⟨0,127,[66,158,229,287,357,444,507,519,594]⟩,⟨0,128,[66,158,229,270,287,357,444,507,519,594]⟩,⟨9,129,[32,66,158,229,270,287,357,444,519,594]⟩,⟨0,130,[66,158,229,270,287,357,444,519,574,594]⟩,⟨0,131,[0,66,158,229,270,287,357,444,519,594]⟩,⟨0,132,[66,158,229,270,287,357,444,468,519,594]⟩,⟨0,133,[66,118,158,229,270,287,357,444,519,594]⟩,⟨0,134,[66,158,229,270,287,357,444,480,519,594]⟩,⟨2,133,[66,158,202,229,270,287,357,444,519,594]⟩,⟨2,134,[66,158,229,270,287,357,444,498,519,594]⟩,⟨6,135,[66,158,206,229,287,357,444,519,594]⟩,⟨6,136,[66,158,206,229,270,287,357,444,519,594]⟩,⟨0,137,[66,158,229,287,357,444,505,519,594]⟩,⟨0,138,[66,158,229,270,287,357,444,505,519,594]⟩,⟨3,139,[35,66,158,229,270,287,357,444,519,594]⟩,⟨0,140,[66,158,229,270,287,357,444,519,594,691]⟩,⟨6,20,[66,158,229,270,287,341,357,444,519,594]⟩,⟨6,57,[66,158,229,270,287,357,444,465,519,594]⟩,⟨1,141,[1,66,158,229,270,287,357,444,519,594]⟩,⟨0,142,[66,158,229,270,287,357,444,519,553,594]⟩,⟨1,143,[66,141,158,229,270,287,357,444,519,594]⟩,⟨11,144,[66,229,270,287,357,444,519,563,594]⟩,⟨0,145,[66,158,229,270,287,357,444,519,563,594]⟩,⟨7,146,[22,66,158,270,287,357,444,519,594]⟩,⟨2,147,[22,66,158,229,270,287,357,444,519,594]⟩,⟨2,148,[66,158,229,270,287,357,444,519,594,681]⟩,⟨7,149,[66,145,158,229,287,357,444,519,594]⟩,⟨7,150,[66,145,158,229,270,287,357,444,519,594]⟩,⟨9,151,[66,158,229,287,357,444,519,594,684]⟩,⟨0,152,[66,158,229,270,287,357,444,519,594,684]⟩,⟨3,153,[66,158,229,270,279,287,357,444,519,594]⟩,⟨0,154,[66,158,229,270,287,357,444,519,580,594]⟩,⟨7,74,[66,158,229,270,287,357,444,519,549,594]⟩,⟨6,111,[66,158,229,270,287,357,391,444,519,594]⟩,⟨0,155,[66,158,229,270,287,357,444,519,588,594]⟩,⟨4,141,[3,66,158,229,270,287,357,444,519,594]⟩,⟨2,142,[66,158,229,270,287,357,444,519,594,629]⟩,⟨10,146,[10,66,229,270,287,357,444,519,594]⟩,⟨0,147,[10,66,158,229,270,287,357,444,519,594]⟩,⟨0,148,[66,158,229,270,287,357,444,519,594,674]⟩,⟨4,143,[66,158,220,229,270,287,357,444,519,594]⟩,⟨9,144,[66,158,270,287,357,444,519,594,637]⟩,⟨2,145,[66,158,229,270,287,357,444,519,594,637]⟩,⟨10,149,[66,158,222,229,287,357,444,519,594]⟩,⟨10,150,[66,158,222,229,270,287,357,444,519,594]⟩,⟨11,151,[66,158,229,287,357,444,519,594,685]⟩,⟨2,152,[66,158,229,270,287,357,444,519,594,685]⟩,⟨5,153,[66,158,229,270,284,287,357,444,519,594]⟩,⟨2,154,[66,158,229,270,287,357,444,519,594,644]⟩,⟨10,74,[66,158,229,270,287,357,444,519,594,625]⟩,⟨8,111,[66,158,229,270,287,357,434,444,519,594]⟩,⟨2,155,[66,158,229,270,287,357,444,519,594,656]⟩,⟨9,113,[66,158,229,270,287,357,444,511,519,594]⟩,⟨0,156,[66,158,229,270,287,357,444,519,594,665]⟩]⟩
def row10_4 : State := ⟨[54,66,158,229,287,357,444,519,594],[⟨0,157,[66,158,174,229,287,357,444,519,594]⟩,⟨0,158,[54,66,158,174,229,287,357,444,519,594]⟩,⟨0,5,[41,54,66,158,229,287,357,444,519,594]⟩,⟨0,30,[54,66,158,177,229,287,357,444,519,594]⟩,⟨2,157,[66,158,229,251,287,357,444,519,594]⟩,⟨2,158,[54,66,158,229,251,287,357,444,519,594]⟩,⟨2,30,[54,66,158,229,253,287,357,444,519,594]⟩,⟨0,83,[54,66,85,158,229,287,357,444,519,594]⟩,⟨0,120,[54,66,158,229,270,287,357,444,519,594]⟩,⟨3,157,[66,158,229,287,308,357,444,519,594]⟩,⟨3,158,[54,66,158,229,287,308,357,444,519,594]⟩,⟨3,30,[54,66,158,229,287,310,357,444,519,594]⟩,⟨1,83,[54,66,103,158,229,287,357,444,519,594]⟩,⟨1,120,[54,66,158,229,287,322,357,444,519,594]⟩,⟨4,83,[54,66,158,183,229,287,357,444,519,594]⟩,⟨4,120,[54,66,158,229,287,332,357,444,519,594]⟩,⟨0,159,[54,66,158,229,287,357,380,444,519,594]⟩,⟨6,160,[7,54,66,158,229,287,357,444,519,594]⟩,⟨0,161,[54,66,158,229,287,357,425,444,519,594]⟩,⟨8,160,[20,54,66,158,229,287,357,444,519,594]⟩,⟨2,161,[54,66,158,229,287,357,444,494,519,594]⟩,⟨9,160,[32,54,66,158,229,287,357,444,519,594]⟩,⟨3,161,[54,66,158,229,287,357,444,519,574,594]⟩,⟨6,157,[66,158,229,287,357,444,464,519,594]⟩,⟨6,158,[54,66,158,229,287,357,444,464,519,594]⟩,⟨0,160,[0,54,66,158,229,287,357,444,519,594]⟩,⟨6,161,[54,66,158,229,287,357,444,468,519,594]⟩,⟨0,162,[54,66,118,158,229,287,357,444,519,594]⟩,⟨0,163,[54,66,158,229,287,357,444,480,519,594]⟩,⟨2,162,[54,66,158,202,229,287,357,444,519,594]⟩,⟨2,163,[54,66,158,229,287,357,444,498,519,594]⟩,⟨3,164,[35,54,66,158,229,287,357,444,519,594]⟩,⟨3,165,[54,66,158,229,287,357,444,519,594,691]⟩,⟨6,5,[54,66,158,229,287,341,357,444,519,594]⟩,⟨6,30,[54,66,158,229,287,357,444,465,519,594]⟩,⟨7,157,[66,158,229,287,357,444,519,547,594]⟩,⟨7,158,[54,66,158,229,287,357,444,519,547,594]⟩,⟨1,160,[1,54,66,158,229,287,357,444,519,594]⟩,⟨7,161,[54,66,158,229,287,357,444,519,553,594]⟩,⟨1,162,[54,66,141,158,229,287,357,444,519,594]⟩,⟨1,163,[54,66,158,229,287,357,444,519,563,594]⟩,⟨2,164,[22,54,66,158,229,287,357,444,519,594]⟩,⟨2,165,[54,66,158,229,287,357,444,519,594,681]⟩,⟨3,162,[54,66,158,229,279,287,357,444,519,594]⟩,⟨3,163,[54,66,158,229,287,357,444,519,580,594]⟩,⟨7,30,[54,66,158,229,287,357,444,519,549,594]⟩,⟨6,83,[54,66,158,229,287,357,391,444,519,594]⟩,⟨6,120,[54,66,158,229,287,357,444,519,588,594]⟩,⟨10,157,[66,158,229,287,357,444,519,594,623]⟩,⟨10,158,[54,66,158,229,287,357,444,519,594,623]⟩,⟨4,160,[3,54,66,158,229,287,357,444,519,594]⟩,⟨10,161,[54,66,158,229,287,357,444,519,594,629]⟩,⟨0,164,[10,54,66,158,229,287,357,444,519,594]⟩,⟨0,165,[54,66,158,229,287,357,444,519,594,674]⟩,⟨4,162,[54,66,158,220,229,287,357,444,519,594]⟩,⟨4,163,[54,66,158,229,287,357,444,519,594,637]⟩,⟨5,162,[54,66,158,229,284,287,357,444,519,594]⟩,⟨5,163,[54,66,158,229,287,357,444,519,594,644]⟩,⟨10,30,[54,66,158,229,287,357,444,519,594,625]⟩,⟨8,83,[54,66,158,229,287,357,434,444,519,594]⟩,⟨8,120,[54,66,158,229,287,357,444,519,594,656]⟩,⟨9,83,[54,66,158,229,287,357,444,511,519,594]⟩,⟨9,120,[54,66,158,229,287,357,444,519,594,665]⟩]⟩
def row10_5 : State := ⟨[66,158,229,287,357,380,444,519,594],[⟨0,6,[41,66,158,229,287,357,380,444,519,594]⟩,⟨6,31,[158,177,229,287,357,380,444,519,594]⟩,⟨0,32,[66,158,177,229,287,357,380,444,519,594]⟩,⟨8,31,[158,229,253,287,357,380,444,519,594]⟩,⟨2,32,[66,158,229,253,287,357,380,444,519,594]⟩,⟨0,84,[66,85,158,229,287,357,380,444,519,594]⟩,⟨0,121,[66,158,229,270,287,357,380,444,519,594]⟩,⟨9,31,[158,229,287,310,357,380,444,519,594]⟩,⟨3,32,[66,158,229,287,310,357,380,444,519,594]⟩,⟨1,84,[66,103,158,229,287,357,380,444,519,594]⟩,⟨1,121,[66,158,229,287,322,357,380,444,519,594]⟩,⟨4,84,[66,158,183,229,287,357,380,444,519,594]⟩,⟨4,121,[66,158,229,287,332,357,380,444,519,594]⟩,⟨0,159,[54,66,158,229,287,357,380,444,519,594]⟩,⟨6,166,[7,66,158,229,287,357,380,444,519,594]⟩,⟨0,167,[66,158,229,287,357,380,425,444,519,594]⟩,⟨8,166,[20,66,158,229,287,357,380,444,519,594]⟩,⟨2,167,[66,158,229,287,357,380,444,494,519,594]⟩,⟨9,166,[32,66,158,229,287,357,380,444,519,594]⟩,⟨3,167,[66,158,229,287,357,380,444,519,574,594]⟩,⟨0,168,[47,66,158,229,287,357,444,519,594]⟩,⟨0,169,[47,66,158,229,287,357,380,444,519,594]⟩,⟨0,38,[66,158,229,287,357,428,444,519,594]⟩,⟨0,170,[66,158,229,287,357,380,428,444,519,594]⟩,⟨2,168,[50,66,158,229,287,357,444,519,594]⟩,⟨2,169,[50,66,158,229,287,357,380,444,519,594]⟩,⟨2,38,[66,158,229,287,357,444,496,519,594]⟩,⟨2,170,[66,158,229,287,357,380,444,496,519,594]⟩,⟨3,168,[53,66,158,229,287,357,444,519,594]⟩,⟨3,169,[53,66,158,229,287,357,380,444,519,594]⟩,⟨3,38,[66,158,229,287,357,444,519,576,594]⟩,⟨3,170,[66,158,229,287,357,380,444,519,576,594]⟩,⟨0,166,[0,66,158,229,287,357,380,444,519,594]⟩,⟨6,167,[66,158,229,287,357,380,444,468,519,594]⟩,⟨0,171,[66,118,158,229,287,357,380,444,519,594]⟩,⟨0,172,[66,158,229,287,357,380,444,480,519,594]⟩,⟨2,171,[66,158,202,229,287,357,380,444,519,594]⟩,⟨2,172,[66,158,229,287,357,380,444,498,519,594]⟩,⟨3,173,[35,66,158,229,287,357,380,444,519,594]⟩,⟨3,174,[66,158,229,287,357,380,444,519,594,691]⟩,⟨6,6,[66,158,229,287,341,357,380,444,519,594]⟩,⟨0,31,[66,158,229,287,380,444,465,519,594]⟩,⟨6,32,[66,158,229,287,357,380,444,465,519,594]⟩,⟨6,168,[66,158,229,287,342,357,444,519,594]⟩,⟨6,169,[66,158,229,287,342,357,380,444,519,594]⟩,⟨6,38,[66,158,229,287,357,444,472,519,594]⟩,⟨6,170,[66,158,229,287,357,380,444,472,519,594]⟩,⟨1,166,[1,66,158,229,287,357,380,444,519,594]⟩,⟨7,167,[66,158,229,287,357,380,444,519,553,594]⟩,⟨1,171,[66,141,158,229,287,357,380,444,519,594]⟩,⟨1,172,[66,158,229,287,357,380,444,519,563,594]⟩,⟨2,173,[22,66,158,229,287,357,380,444,519,594]⟩,⟨2,174,[66,158,229,287,357,380,444,519,594,681]⟩,⟨3,171,[66,158,229,279,287,357,380,444,519,594]⟩,⟨3,172,[66,158,229,287,357,380,444,519,580,594]⟩,⟨1,31,[66,158,229,287,380,444,519,549,594]⟩,⟨7,32,[66,158,229,287,357,380,444,519,549,594]⟩,⟨7,168,[66,158,229,287,343,357,444,519,594]⟩,⟨7,169,[66,158,229,287,343,357,380,444,519,594]⟩,⟨7,38,[66,158,229,287,357,444,519,556,594]⟩,⟨7,170,[66,158,229,287,357,380,444,519,556,594]⟩,⟨6,84,[66,158,229,287,357,380,391,444,519,594]⟩,⟨6,121,[66,158,229,287,357,380,444,519,588,594]⟩,⟨4,166,[3,66,158,229,287,357,380,444,519,594]⟩,⟨10,167,[66,158,229,287,357,380,444,519,594,629]⟩,⟨0,173,[10,66,158,229,287,357,380,444,519,594]⟩,⟨0,174,[66,158,229,287,357,380,444,519,594,674]⟩,⟨4,171,[66,158,220,229,287,357,380,444,519,594]⟩,⟨4,172,[66,158,229,287,357,380,444,519,594,637]⟩,⟨5,171,[66,158,229,284,287,357,380,444,519,594]⟩,⟨5,172,[66,158,229,287,357,380,444,519,594,644]⟩,⟨4,31,[66,158,229,287,380,444,519,594,625]⟩,⟨10,32,[66,158,229,287,357,380,444,519,594,625]⟩,⟨10,168,[66,158,229,287,344,357,444,519,594]⟩,⟨10,169,[66,158,229,287,344,357,380,444,519,594]⟩,⟨10,38,[66,158,229,287,357,444,519,594,633]⟩,⟨10,170,[66,158,229,287,357,380,444,519,594,633]⟩,⟨8,84,[66,158,229,287,357,380,434,444,519,594]⟩,⟨8,121,[66,158,229,287,357,380,444,519,594,656]⟩,⟨9,84,[66,158,229,287,357,380,444,511,519,594]⟩,⟨9,121,[66,158,229,287,357,380,444,519,594,665]⟩]⟩
def row10_6 : State := ⟨[0,66,158,229,287,357,444,519,594],[⟨10,175,[66,159,229,287,357,444,519,594]⟩,⟨0,176,[66,158,159,229,287,357,444,519,594]⟩,⟨2,177,[0,66,159,229,287,357,444,519,594]⟩,⟨0,178,[0,66,158,159,229,287,357,444,519,594]⟩,⟨0,11,[0,41,66,158,229,287,357,444,519,594]⟩,⟨0,42,[0,66,158,177,229,287,357,444,519,594]⟩,⟨7,175,[66,158,230,287,357,444,519,594]⟩,⟨2,176,[66,158,229,230,287,357,444,519,594]⟩,⟨0,177,[0,66,158,230,287,357,444,519,594]⟩,⟨2,178,[0,66,158,229,230,287,357,444,519,594]⟩,⟨2,42,[0,66,158,229,253,287,357,444,519,594]⟩,⟨0,91,[0,66,85,158,229,287,357,444,519,594]⟩,⟨0,131,[0,66,158,229,270,287,357,444,519,594]⟩,⟨6,179,[66,158,229,288,357,444,519,594]⟩,⟨3,180,[66,158,229,287,288,357,444,519,594]⟩,⟨0,181,[0,66,158,229,288,357,444,519,594]⟩,⟨0,182,[0,66,158,229,287,288,357,444,519,594]⟩,⟨0,58,[0,66,158,229,287,310,357,444,519,594]⟩,⟨0,100,[0,66,103,158,229,287,357,444,519,594]⟩,⟨0,141,[0,66,158,229,287,322,357,444,519,594]⟩,⟨2,100,[0,66,158,183,229,287,357,444,519,594]⟩,⟨2,141,[0,66,158,229,287,332,357,444,519,594]⟩,⟨0,183,[66,158,229,287,358,444,519,594]⟩,⟨6,184,[66,158,229,287,357,358,444,519,594]⟩,⟨0,185,[0,66,158,229,287,358,444,519,594]⟩,⟨0,186,[0,66,158,229,287,357,358,444,519,594]⟩,⟨0,160,[0,54,66,158,229,287,357,444,519,594]⟩,⟨0,166,[0,66,158,229,287,357,380,444,519,594]⟩,⟨0,187,[0,7,66,158,229,287,357,444,519,594]⟩,⟨0,188,[0,66,158,229,287,357,425,444,519,594]⟩,⟨2,187,[0,20,66,158,229,287,357,444,519,594]⟩,⟨2,188,[0,66,158,229,287,357,444,494,519,594]⟩,⟨0,189,[0,32,66,158,229,287,357,444,519,594]⟩,⟨0,190,[0,66,158,229,287,357,444,519,574,594]⟩,⟨0,191,[0,66,158,229,287,357,444,468,519,594]⟩,⟨0,192,[0,66,118,158,229,287,357,444,519,594]⟩,⟨0,193,[0,66,158,229,287,357,444,480,519,594]⟩,⟨2,192,[0,66,158,202,229,287,357,444,519,594]⟩,⟨2,193,[0,66,158,229,287,357,444,498,519,594]⟩,⟨0,194,[0,35,66,158,229,287,357,519,594]⟩,⟨0,195,[0,35,66,158,229,287,357,444,519,594]⟩,⟨0,196,[0,66,158,229,287,357,444,519,594,691]⟩,⟨0,7,[0,66,158,229,287,341,357,444,519,594]⟩,⟨0,33,[0,66,158,229,287,357,465,519,594]⟩,⟨0,34,[0,66,158,229,287,357,444,465,519,594]⟩,⟨2,197,[66,158,229,287,357,444,520,594]⟩,⟨7,198,[66,158,229,287,357,444,519,520,594]⟩,⟨2,199,[0,66,158,229,287,357,444,520,594]⟩,⟨0,200,[0,66,158,229,287,357,444,519,520,594]⟩,⟨0,201,[0,1,66,158,229,287,357,444,519,594]⟩,⟨0,202,[0,66,158,229,287,357,444,519,553,594]⟩,⟨0,203,[0,66,141,158,229,287,357,444,519,594]⟩,⟨0,204,[0,66,158,229,287,357,444,519,563,594]⟩,⟨2,205,[0,22,66,158,229,287,357,444,519,594]⟩,⟨2,206,[0,66,158,229,287,357,444,519,594,681]⟩,⟨0,207,[0,66,158,229,279,287,357,444,519,594]⟩,⟨0,208,[0,66,158,229,287,357,444,519,580,594]⟩,⟨0,40,[0,66,158,229,287,357,444,519,549,594]⟩,⟨0,87,[0,66,158,229,287,357,391,444,519,594]⟩,⟨0,122,[0,66,158,229,287,357,444,519,588,594]⟩,⟨0,197,[66,158,229,287,357,444,519,595]⟩,⟨10,198,[66,158,229,287,357,444,519,594,595]⟩,⟨0,199,[0,66,158,229,287,357,444,519,595]⟩,⟨2,200,[0,66,158,229,287,357,444,519,594,595]⟩,⟨2,201,[0,3,66,158,229,287,357,444,519,594]⟩,⟨2,202,[0,66,158,229,287,357,444,519,594,629]⟩,⟨0,205,[0,10,66,158,229,287,357,444,519,594]⟩,⟨0,206,[0,66,158,229,287,357,444,519,594,674]⟩,⟨2,203,[0,66,158,220,229,287,357,444,519,594]⟩,⟨2,204,[0,66,158,229,287,357,444,519,594,637]⟩,⟨2,207,[0,66,158,229,284,287,357,444,519,594]⟩,⟨2,208,[0,66,158,229,287,357,444,519,594,644]⟩,⟨2,40,[0,66,158,229,287,357,444,519,594,625]⟩,⟨2,87,[0,66,158,229,287,357,434,444,519,594]⟩,⟨2,122,[0,66,158,229,287,357,444,519,594,656]⟩,⟨0,89,[0,66,158,229,287,357,444,511,519,594]⟩,⟨0,129,[0,66,158,229,287,357,444,519,594,665]⟩]⟩
def row10_7 : State := ⟨[66,158,229,287,357,425,444,519,594],[⟨0,8,[41,66,158,229,287,357,425,444,519,594]⟩,⟨0,35,[66,158,177,229,287,357,425,444,519,594]⟩,⟨2,41,[66,158,229,253,287,357,425,444,519,594]⟩,⟨0,88,[66,85,158,229,287,357,425,444,519,594]⟩,⟨10,123,[66,229,270,287,357,425,444,519,594]⟩,⟨0,124,[66,158,229,270,287,357,425,444,519,594]⟩,⟨3,41,[66,158,229,287,310,357,425,444,519,594]⟩,⟨1,88,[66,103,158,229,287,357,425,444,519,594]⟩,⟨11,123,[66,229,287,322,357,425,444,519,594]⟩,⟨1,124,[66,158,229,287,322,357,425,444,519,594]⟩,⟨4,90,[66,158,183,229,287,357,425,444,519,594]⟩,⟨4,130,[66,158,229,287,332,357,425,444,519,594]⟩,⟨0,161,[54,66,158,229,287,357,425,444,519,594]⟩,⟨0,167,[66,158,229,287,357,380,425,444,519,594]⟩,⟨6,191,[7,66,158,229,287,357,425,444,519,594]⟩,⟨8,202,[20,66,158,229,287,357,425,444,519,594]⟩,⟨0,209,[66,158,229,287,357,425,444,494,519,594]⟩,⟨9,202,[32,66,158,229,287,357,425,444,519,594]⟩,⟨1,209,[66,158,229,287,357,425,444,519,574,594]⟩,⟨0,210,[64,66,158,229,287,357,444,519,594]⟩,⟨0,211,[64,66,158,229,287,357,425,444,519,594]⟩,⟨0,38,[66,158,229,287,357,428,444,519,594]⟩,⟨0,212,[66,158,229,287,357,425,428,444,519,594]⟩,⟨2,213,[66,92,158,229,287,357,444,519,594]⟩,⟨2,214,[66,92,158,229,287,357,425,444,519,594]⟩,⟨0,127,[66,158,229,287,357,444,507,519,594]⟩,⟨0,215,[66,158,229,287,357,425,444,507,519,594]⟩,⟨3,213,[66,105,158,229,287,357,444,519,594]⟩,⟨3,214,[66,105,158,229,287,357,425,444,519,594]⟩,⟨1,127,[66,158,229,287,357,444,519,586,594]⟩,⟨1,215,[66,158,229,287,357,425,444,519,586,594]⟩,⟨0,188,[0,66,158,229,287,357,425,444,519,594]⟩,⟨0,216,[66,158,229,287,357,425,444,468,519,594]⟩,⟨0,217,[66,118,158,229,287,357,425,444,519,594]⟩,⟨0,218,[66,158,229,287,357,425,444,480,519,594]⟩,⟨2,219,[66,158,202,229,287,357,425,444,519,594]⟩,⟨0,220,[66,158,229,287,357,425,444,498,519,594]⟩,⟨6,221,[35,66,158,229,287,357,425,444,519,594]⟩,⟨1,222,[66,158,229,287,357,425,444,519,594,691]⟩,⟨6,12,[66,158,229,287,341,357,425,444,519,594]⟩,⟨6,43,[66,158,229,287,357,425,444,465,519,594]⟩,⟨6,223,[66,158,229,287,357,397,444,519,594]⟩,⟨6,224,[66,158,229,287,357,397,425,444,519,594]⟩,⟨6,49,[66,158,229,287,357,444,489,519,594]⟩,⟨0,225,[66,158,229,287,357,425,444,489,519,594]⟩,⟨1,188,[1,66,158,229,287,357,425,444,519,594]⟩,⟨1,216,[66,158,229,287,357,425,444,519,553,594]⟩,⟨1,217,[66,141,158,229,287,357,425,444,519,594]⟩,⟨1,218,[66,158,229,287,357,425,444,519,563,594]⟩,⟨7,221,[22,66,158,229,287,357,425,444,519,594]⟩,⟨0,222,[66,158,229,287,357,425,444,519,594,681]⟩,⟨3,219,[66,158,229,279,287,357,425,444,519,594]⟩,⟨1,220,[66,158,229,287,357,425,444,519,580,594]⟩,⟨7,43,[66,158,229,287,357,425,444,519,549,594]⟩,⟨7,223,[66,158,229,287,357,410,444,519,594]⟩,⟨7,224,[66,158,229,287,357,410,425,444,519,594]⟩,⟨7,49,[66,158,229,287,357,444,519,571,594]⟩,⟨1,225,[66,158,229,287,357,425,444,519,571,594]⟩,⟨6,92,[66,158,229,287,357,391,425,444,519,594]⟩,⟨6,132,[66,158,229,287,357,425,444,519,588,594]⟩,⟨4,190,[3,66,158,229,287,357,425,444,519,594]⟩,⟨0,226,[66,158,229,287,357,425,444,519,594,629]⟩,⟨0,227,[10,66,158,229,287,357,425,444,519,594]⟩,⟨0,228,[66,158,229,287,357,425,444,519,594,674]⟩,⟨4,229,[66,158,220,229,287,357,425,444,519,594]⟩,⟨0,230,[66,158,229,287,357,425,444,519,594,637]⟩,⟨5,229,[66,158,229,284,287,357,425,444,519,594]⟩,⟨1,230,[66,158,229,287,357,425,444,519,594,644]⟩,⟨0,59,[66,158,229,287,425,444,519,594,625]⟩,⟨10,60,[66,158,229,287,357,425,444,519,594,625]⟩,⟨10,231,[66,158,229,287,346,357,444,519,594]⟩,⟨10,232,[66,158,229,287,346,357,425,444,519,594]⟩,⟨10,68,[66,158,229,287,357,444,519,594,707]⟩,⟨0,233,[66,158,229,287,357,425,444,519,594,707]⟩,⟨8,101,[66,158,229,287,357,425,434,444,519,594]⟩,⟨8,142,[66,158,229,287,357,425,444,519,594,656]⟩,⟨9,101,[66,158,229,287,357,425,444,511,519,594]⟩,⟨9,142,[66,158,229,287,357,425,444,519,594,665]⟩]⟩
def row10_8 : State := ⟨[66,118,158,229,287,357,444,519,594],[⟨0,234,[66,137,158,229,287,357,444,519,594]⟩,⟨0,235,[66,118,137,158,229,287,357,444,519,594]⟩,⟨0,13,[41,66,118,158,229,287,357,444,519,594]⟩,⟨0,44,[66,118,158,177,229,287,357,444,519,594]⟩,⟨0,51,[66,118,158,229,253,287,357,444,519,594]⟩,⟨0,93,[66,78,158,229,287,357,444,519,594]⟩,⟨0,236,[66,78,118,158,229,287,357,444,519,594]⟩,⟨2,237,[66,158,229,258,287,357,444,519,594]⟩,⟨0,238,[66,118,158,229,258,287,357,444,519,594]⟩,⟨0,96,[66,85,118,158,229,287,357,444,519,594]⟩,⟨0,133,[66,118,158,229,270,287,357,444,519,594]⟩,⟨0,70,[66,118,158,229,287,310,357,444,519,594]⟩,⟨3,239,[66,158,229,287,319,357,444,519,594]⟩,⟨0,240,[66,118,158,229,287,319,357,444,519,594]⟩,⟨1,104,[66,103,118,158,229,287,357,444,519,594]⟩,⟨0,143,[66,118,158,229,287,322,357,444,519,594]⟩,⟨4,108,[66,118,158,183,229,287,357,444,519,594]⟩,⟨0,153,[66,118,158,229,287,332,357,444,519,594]⟩,⟨0,162,[54,66,118,158,229,287,357,444,519,594]⟩,⟨0,171,[66,118,158,229,287,357,380,444,519,594]⟩,⟨6,234,[66,158,229,287,357,403,444,519,594]⟩,⟨6,235,[66,118,158,229,287,357,403,444,519,594]⟩,⟨6,192,[7,66,118,158,229,287,357,444,519,594]⟩,⟨0,217,[66,118,158,229,287,357,425,444,519,594]⟩,⟨8,203,[20,66,118,158,229,287,357,444,519,594]⟩,⟨0,219,[66,118,158,229,287,357,444,494,519,594]⟩,⟨9,207,[32,66,118,158,229,287,357,444,519,594]⟩,⟨0,229,[66,118,158,229,287,357,444,519,574,594]⟩,⟨0,192,[0,66,118,158,229,287,357,444,519,594]⟩,⟨6,217,[66,118,158,229,287,357,444,468,519,594]⟩,⟨0,241,[66,118,158,229,287,357,444,480,519,594]⟩,⟨6,242,[66,118,158,202,229,287,357,444,519,594]⟩,⟨0,243,[66,118,158,229,287,357,444,498,519,594]⟩,⟨6,244,[35,66,118,158,229,287,357,444,519,594]⟩,⟨6,245,[66,118,158,229,287,357,444,519,594,691]⟩,⟨6,13,[66,118,158,229,287,341,357,444,519,594]⟩,⟨6,44,[66,118,158,229,287,357,444,465,519,594]⟩,⟨1,203,[1,66,118,158,229,287,357,444,519,594]⟩,⟨6,219,[66,118,158,229,287,357,444,519,553,594]⟩,⟨6,93,[66,114,158,229,287,357,444,519,594]⟩,⟨6,236,[66,114,118,158,229,287,357,444,519,594]⟩,⟨7,237,[66,158,229,287,357,444,519,557,594]⟩,⟨6,238,[66,118,158,229,287,357,444,519,557,594]⟩,⟨0,242,[66,118,141,158,229,287,357,444,519,594]⟩,⟨6,243,[66,118,158,229,287,357,444,519,563,594]⟩,⟨2,246,[22,66,118,158,229,287,357,444,519,594]⟩,⟨0,247,[66,118,158,229,287,357,444,519,594,681]⟩,⟨3,248,[66,118,158,229,279,287,357,444,519,594]⟩,⟨0,249,[66,118,158,229,287,357,444,519,580,594]⟩,⟨6,51,[66,118,158,229,287,357,444,519,549,594]⟩,⟨6,96,[66,118,158,229,287,357,391,444,519,594]⟩,⟨6,133,[66,118,158,229,287,357,444,519,588,594]⟩,⟨4,207,[3,66,118,158,229,287,357,444,519,594]⟩,⟨6,229,[66,118,158,229,287,357,444,519,594,629]⟩,⟨10,239,[66,158,229,287,357,444,519,594,654]⟩,⟨6,240,[66,118,158,229,287,357,444,519,594,654]⟩,⟨0,244,[10,66,118,158,229,287,357,444,519,594]⟩,⟨0,245,[66,118,158,229,287,357,444,519,594,674]⟩,⟨0,248,[66,118,158,220,229,287,357,444,519,594]⟩,⟨6,249,[66,118,158,229,287,357,444,519,594,637]⟩,⟨0,250,[66,118,158,229,284,287,357,444,519,594]⟩,⟨0,251,[66,118,158,229,287,357,444,519,594,644]⟩,⟨6,70,[66,118,158,229,287,357,444,519,594,625]⟩,⟨8,104,[66,118,158,229,287,357,434,444,519,594]⟩,⟨6,143,[66,118,158,229,287,357,444,519,594,656]⟩,⟨9,108,[66,118,158,229,287,357,444,511,519,594]⟩,⟨6,153,[66,118,158,229,287,357,444,519,594,665]⟩]⟩
def row10_9 : State := ⟨[66,158,229,287,357,444,480,519,594],[⟨0,14,[41,66,158,229,287,357,444,480,519,594]⟩,⟨10,45,[66,177,229,287,357,444,480,519,594]⟩,⟨0,46,[66,158,177,229,287,357,444,480,519,594]⟩,⟨2,52,[66,158,229,253,287,357,444,480,519,594]⟩,⟨0,97,[66,85,158,229,287,357,444,480,519,594]⟩,⟨0,134,[66,158,229,270,287,357,444,480,519,594]⟩,⟨3,71,[66,158,229,287,310,357,444,480,519,594]⟩,⟨1,105,[66,103,158,229,287,357,444,480,519,594]⟩,⟨10,144,[66,229,287,322,357,444,480,519,594]⟩,⟨1,145,[66,158,229,287,322,357,444,480,519,594]⟩,⟨4,109,[66,158,183,229,287,357,444,480,519,594]⟩,⟨4,154,[66,158,229,287,332,357,444,480,519,594]⟩,⟨0,163,[54,66,158,229,287,357,444,480,519,594]⟩,⟨0,172,[66,158,229,287,357,380,444,480,519,594]⟩,⟨6,193,[7,66,158,229,287,357,444,480,519,594]⟩,⟨0,218,[66,158,229,287,357,425,444,480,519,594]⟩,⟨8,204,[20,66,158,229,287,357,444,480,519,594]⟩,⟨2,220,[66,158,229,287,357,444,480,494,519,594]⟩,⟨9,208,[32,66,158,229,287,357,444,480,519,594]⟩,⟨3,230,[66,158,229,287,357,444,480,519,574,594]⟩,⟨0,193,[0,66,158,229,287,357,444,480,519,594]⟩,⟨6,218,[66,158,229,287,357,444,468,480,519,594]⟩,⟨0,241,[66,118,158,229,287,357,444,480,519,594]⟩,⟨2,243,[66,158,202,229,287,357,444,480,519,594]⟩,⟨0,252,[66,158,229,287,357,444,480,498,519,594]⟩,⟨6,253,[35,66,158,229,287,357,444,480,519,594]⟩,⟨6,254,[66,158,229,287,357,444,480,519,594,691]⟩,⟨6,14,[66,158,229,287,341,357,444,480,519,594]⟩,⟨3,45,[66,158,229,287,357,465,480,519,594]⟩,⟨6,46,[66,158,229,287,357,444,465,480,519,594]⟩,⟨0,255,[42,66,158,229,287,357,444,519,594]⟩,⟨0,256,[42,66,158,229,287,357,444,480,519,594]⟩,⟨0,49,[66,158,229,287,357,444,488,519,594]⟩,⟨0,257,[66,158,229,287,357,444,480,488,519,594]⟩,⟨2,223,[66,158,205,229,287,357,444,519,594]⟩,⟨2,258,[66,158,205,229,287,357,444,480,519,594]⟩,⟨0,137,[66,158,229,287,357,444,505,519,594]⟩,⟨0,259,[66,158,229,287,357,444,480,505,519,594]⟩,⟨3,260,[66,106,158,229,287,357,444,519,594]⟩,⟨3,261,[66,106,158,229,287,357,444,480,519,594]⟩,⟨8,151,[66,158,229,287,357,444,519,594,695]⟩,⟨6,262,[66,158,229,287,357,444,480,519,594,695]⟩,⟨6,255,[66,158,229,287,345,357,444,519,594]⟩,⟨6,256,[66,158,229,287,345,357,444,480,519,594]⟩,⟨6,49,[66,158,229,287,357,444,489,519,594]⟩,⟨6,257,[66,158,229,287,357,444,480,489,519,594]⟩,⟨1,204,[1,66,158,229,287,357,444,480,519,594]⟩,⟨7,220,[66,158,229,287,357,444,480,519,553,594]⟩,⟨7,243,[66,141,158,229,287,357,444,480,519,594]⟩,⟨6,252,[66,158,229,287,357,444,480,519,563,594]⟩,⟨2,263,[22,66,158,229,287,357,444,480,519,594]⟩,⟨0,264,[66,158,229,287,357,444,480,519,594,681]⟩,⟨9,249,[66,158,229,279,287,357,444,480,519,594]⟩,⟨0,265,[66,158,229,287,357,444,480,519,580,594]⟩,⟨7,52,[66,158,229,287,357,444,480,519,549,594]⟩,⟨6,97,[66,158,229,287,357,391,444,480,519,594]⟩,⟨6,134,[66,158,229,287,357,444,480,519,588,594]⟩,⟨7,223,[66,158,229,287,357,410,444,519,594]⟩,⟨7,258,[66,158,229,287,357,410,444,480,519,594]⟩,⟨6,137,[66,158,229,287,357,444,519,591,594]⟩,⟨6,259,[66,158,229,287,357,444,480,519,591,594]⟩,⟨4,208,[3,66,158,229,287,357,444,480,519,594]⟩,⟨10,230,[66,158,229,287,357,444,480,519,594,629]⟩,⟨0,253,[10,66,158,229,287,357,444,480,519,594]⟩,⟨0,254,[66,158,229,287,357,444,480,519,594,674]⟩,⟨4,249,[66,158,220,229,287,357,444,480,519,594]⟩,⟨4,265,[66,158,229,287,357,444,480,519,594,637]⟩,⟨5,251,[66,158,229,284,287,357,444,480,519,594]⟩,⟨0,266,[66,158,229,287,357,444,480,519,594,644]⟩,⟨10,71,[66,158,229,287,357,444,480,519,594,625]⟩,⟨8,105,[66,158,229,287,357,434,444,480,519,594]⟩,⟨3,144,[66,158,229,287,357,480,519,594,656]⟩,⟨8,145,[66,158,229,287,357,444,480,519,594,656]⟩,⟨10,260,[66,158,229,287,357,437,444,519,594]⟩,⟨10,261,[66,158,229,287,357,437,444,480,519,594]⟩,⟨1,151,[66,158,229,287,357,444,519,594,687]⟩,⟨0,262,[66,158,229,287,357,444,480,519,594,687]⟩,⟨9,109,[66,158,229,287,357,444,480,511,519,594]⟩,⟨9,154,[66,158,229,287,357,444,480,519,594,665]⟩]⟩
def row10_10 : State := ⟨[10,66,158,229,287,357,444,519,594],[⟨10,267,[68,158,229,287,357,444,519,594]⟩,⟨0,268,[66,68,158,229,287,357,444,519,594]⟩,⟨10,269,[10,68,158,229,287,357,444,519,594]⟩,⟨0,270,[10,66,68,158,229,287,357,444,519,594]⟩,⟨0,15,[10,41,66,158,229,287,357,444,519,594]⟩,⟨0,61,[10,66,158,177,229,287,357,444,519,594]⟩,⟨9,271,[66,158,239,287,357,444,519,594]⟩,⟨2,272,[66,158,229,239,287,357,444,519,594]⟩,⟨11,273,[10,66,158,239,287,357,444,519,594]⟩,⟨0,274,[10,66,158,229,239,287,357,444,519,594]⟩,⟨0,53,[10,66,158,229,253,287,357,444,519,594]⟩,⟨0,106,[10,66,85,158,229,287,357,444,519,594]⟩,⟨10,146,[10,66,229,270,287,357,444,519,594]⟩,⟨0,147,[10,66,158,229,270,287,357,444,519,594]⟩,⟨8,271,[66,158,229,297,357,444,519,594]⟩,⟨3,272,[66,158,229,287,297,357,444,519,594]⟩,⟨10,273,[10,66,158,229,297,357,444,519,594]⟩,⟨1,274,[10,66,158,229,287,297,357,444,519,594]⟩,⟨1,53,[10,66,158,229,287,310,357,444,519,594]⟩,⟨1,106,[10,66,103,158,229,287,357,444,519,594]⟩,⟨11,146,[10,66,229,287,322,357,444,519,594]⟩,⟨1,147,[10,66,158,229,287,322,357,444,519,594]⟩,⟨0,98,[10,66,158,183,229,287,357,444,519,594]⟩,⟨0,139,[10,66,158,229,287,332,357,444,519,594]⟩,⟨0,267,[66,158,229,287,364,444,519,594]⟩,⟨10,268,[66,158,229,287,357,364,444,519,594]⟩,⟨0,269,[10,66,158,229,287,364,444,519,594]⟩,⟨10,270,[10,66,158,229,287,357,364,444,519,594]⟩,⟨0,164,[10,54,66,158,229,287,357,444,519,594]⟩,⟨0,173,[10,66,158,229,287,357,380,444,519,594]⟩,⟨6,194,[7,10,66,229,287,357,444,519,594]⟩,⟨6,195,[7,10,66,158,229,287,357,444,519,594]⟩,⟨0,227,[10,66,158,229,287,357,425,444,519,594]⟩,⟨10,205,[10,20,66,158,229,287,357,444,519,594]⟩,⟨10,221,[10,66,158,229,287,357,444,494,519,594]⟩,⟨11,205,[10,32,66,158,229,287,357,444,519,594]⟩,⟨11,221,[10,66,158,229,287,357,444,519,574,594]⟩,⟨3,271,[66,158,229,287,357,450,519,594]⟩,⟨8,272,[66,158,229,287,357,444,450,519,594]⟩,⟨1,273,[10,66,158,229,287,357,450,519,594]⟩,⟨10,274,[10,66,158,229,287,357,444,450,519,594]⟩,⟨0,205,[0,10,66,158,229,287,357,444,519,594]⟩,⟨0,221,[10,66,158,229,287,357,444,468,519,594]⟩,⟨0,244,[10,66,118,158,229,287,357,444,519,594]⟩,⟨0,253,[10,66,158,229,287,357,444,480,519,594]⟩,⟨0,246,[10,66,158,202,229,287,357,444,519,594]⟩,⟨0,263,[10,66,158,229,287,357,444,498,519,594]⟩,⟨1,275,[10,35,66,158,229,287,357,444,519,594]⟩,⟨1,276,[10,66,158,229,287,357,444,519,594,691]⟩,⟨10,15,[10,66,158,229,287,341,357,444,519,594]⟩,⟨10,53,[10,66,158,229,287,357,444,465,519,594]⟩,⟨2,271,[66,158,229,287,357,444,526,594]⟩,⟨9,272,[66,158,229,287,357,444,519,526,594]⟩,⟨0,273,[10,66,158,229,287,357,444,526,594]⟩,⟨11,274,[10,66,158,229,287,357,444,519,526,594]⟩,⟨1,205,[1,10,66,158,229,287,357,444,519,594]⟩,⟨1,221,[10,66,158,229,287,357,444,519,553,594]⟩,⟨1,244,[10,66,141,158,229,287,357,444,519,594]⟩,⟨1,253,[10,66,158,229,287,357,444,519,563,594]⟩,⟨0,275,[10,22,66,158,229,287,357,444,519,594]⟩,⟨0,276,[10,66,158,229,287,357,444,519,594,681]⟩,⟨1,246,[10,66,158,229,279,287,357,444,519,594]⟩,⟨1,263,[10,66,158,229,287,357,444,519,580,594]⟩,⟨11,53,[10,66,158,229,287,357,444,519,549,594]⟩,⟨10,98,[10,66,158,229,287,357,391,444,519,594]⟩,⟨10,139,[10,66,158,229,287,357,444,519,588,594]⟩,⟨4,194,[3,10,66,158,229,287,357,444,519]⟩,⟨4,195,[3,10,66,158,229,287,357,444,519,594]⟩,⟨10,227,[10,66,158,229,287,357,444,519,594,629]⟩,⟨0,277,[10,66,158,229,287,357,444,519,594,674]⟩,⟨10,244,[10,66,158,220,229,287,357,444,519,594]⟩,⟨10,253,[10,66,158,229,287,357,444,519,594,637]⟩,⟨11,244,[10,66,158,229,284,287,357,444,519,594]⟩,⟨11,253,[10,66,158,229,287,357,444,519,594,644]⟩,⟨10,61,[10,66,158,229,287,357,444,519,594,625]⟩,⟨10,106,[10,66,158,229,287,357,434,444,519,594]⟩,⟨0,146,[10,66,158,229,287,357,444,519,656]⟩,⟨10,147,[10,66,158,229,287,357,444,519,594,656]⟩,⟨11,106,[10,66,158,229,287,357,444,511,519,594]⟩,⟨1,146,[10,66,158,229,287,357,444,519,665]⟩,⟨11,147,[10,66,158,229,287,357,444,519,594,665]⟩]⟩
def row10_11 : State := ⟨[66,158,229,287,357,444,519,594,674],[⟨0,16,[41,66,158,229,287,357,444,519,594,674]⟩,⟨10,62,[66,177,229,287,357,444,519,594,674]⟩,⟨0,63,[66,158,177,229,287,357,444,519,594,674]⟩,⟨2,54,[66,158,229,253,287,357,444,519,594,674]⟩,⟨0,107,[66,85,158,229,287,357,444,519,594,674]⟩,⟨0,148,[66,158,229,270,287,357,444,519,594,674]⟩,⟨3,54,[66,158,229,287,310,357,444,519,594,674]⟩,⟨1,107,[66,103,158,229,287,357,444,519,594,674]⟩,⟨1,148,[66,158,229,287,322,357,444,519,594,674]⟩,⟨4,99,[66,158,183,229,287,357,444,519,594,674]⟩,⟨4,140,[66,158,229,287,332,357,444,519,594,674]⟩,⟨0,165,[54,66,158,229,287,357,444,519,594,674]⟩,⟨0,174,[66,158,229,287,357,380,444,519,594,674]⟩,⟨6,196,[7,66,158,229,287,357,444,519,594,674]⟩,⟨0,228,[66,158,229,287,357,425,444,519,594,674]⟩,⟨10,206,[20,66,158,229,287,357,444,519,594,674]⟩,⟨2,222,[66,158,229,287,357,444,494,519,594,674]⟩,⟨11,206,[32,66,158,229,287,357,444,519,594,674]⟩,⟨3,222,[66,158,229,287,357,444,519,574,594,674]⟩,⟨0,206,[0,66,158,229,287,357,444,519,594,674]⟩,⟨8,222,[66,158,229,287,357,444,468,519,594,674]⟩,⟨0,245,[66,118,158,229,287,357,444,519,594,674]⟩,⟨0,254,[66,158,229,287,357,444,480,519,594,674]⟩,⟨2,247,[66,158,202,229,287,357,444,519,594,674]⟩,⟨2,264,[66,158,229,287,357,444,498,519,594,674]⟩,⟨3,276,[35,66,158,229,287,357,444,519,594,674]⟩,⟨1,278,[66,158,229,287,357,444,519,594,674,691]⟩,⟨10,16,[66,158,229,287,341,357,444,519,594,674]⟩,⟨8,54,[66,158,229,287,357,444,465,519,594,674]⟩,⟨1,206,[1,66,158,229,287,357,444,519,594,674]⟩,⟨9,222,[66,158,229,287,357,444,519,553,594,674]⟩,⟨1,245,[66,141,158,229,287,357,444,519,594,674]⟩,⟨1,254,[66,158,229,287,357,444,519,563,594,674]⟩,⟨2,276,[22,66,158,229,287,357,444,519,594,674]⟩,⟨0,278,[66,158,229,287,357,444,519,594,674,681]⟩,⟨3,247,[66,158,229,279,287,357,444,519,594,674]⟩,⟨3,264,[66,158,229,287,357,444,519,580,594,674]⟩,⟨9,54,[66,158,229,287,357,444,519,549,594,674]⟩,⟨6,99,[66,158,229,287,357,391,444,519,594,674]⟩,⟨6,140,[66,158,229,287,357,444,519,588,594,674]⟩,⟨4,196,[3,66,158,229,287,357,444,519,594,674]⟩,⟨10,228,[66,158,229,287,357,444,519,594,629,674]⟩,⟨0,277,[10,66,158,229,287,357,444,519,594,674]⟩,⟨10,245,[66,158,220,229,287,357,444,519,594,674]⟩,⟨10,254,[66,158,229,287,357,444,519,594,637,674]⟩,⟨11,245,[66,158,229,284,287,357,444,519,594,674]⟩,⟨11,254,[66,158,229,287,357,444,519,594,644,674]⟩,⟨0,62,[66,158,229,287,357,444,519,625,674]⟩,⟨10,63,[66,158,229,287,357,444,519,594,625,674]⟩,⟨10,107,[66,158,229,287,357,434,444,519,594,674]⟩,⟨10,148,[66,158,229,287,357,444,519,594,656,674]⟩,⟨11,107,[66,158,229,287,357,444,511,519,594,674]⟩,⟨11,148,[66,158,229,287,357,444,519,594,665,674]⟩,⟨4,255,[44,66,158,229,287,357,444,519,594]⟩,⟨4,279,[44,66,158,229,287,357,444,519,594,674]⟩,⟨0,68,[66,158,229,287,357,444,519,594,704]⟩,⟨0,280,[66,158,229,287,357,444,519,594,674,704]⟩,⟨2,281,[66,158,227,229,287,357,444,519,594]⟩,⟨2,282,[66,158,227,229,287,357,444,519,594,674]⟩,⟨11,151,[66,158,229,287,357,444,519,594,685]⟩,⟨11,283,[66,158,229,287,357,444,519,594,674,685]⟩,⟨3,281,[66,158,229,286,287,357,444,519,594]⟩,⟨3,282,[66,158,229,286,287,357,444,519,594,674]⟩,⟨10,151,[66,158,229,287,357,444,519,594,696]⟩,⟨10,283,[66,158,229,287,357,444,519,594,674,696]⟩,⟨6,255,[66,158,229,287,345,357,444,519,594]⟩,⟨6,279,[66,158,229,287,345,357,444,519,594,674]⟩,⟨10,68,[66,158,229,287,357,444,519,594,707]⟩,⟨10,280,[66,158,229,287,357,444,519,594,674,707]⟩,⟨6,281,[66,158,229,287,357,442,444,519,594]⟩,⟨8,282,[66,158,229,287,357,442,444,519,594,674]⟩,⟨1,151,[66,158,229,287,357,444,519,594,687]⟩,⟨1,283,[66,158,229,287,357,444,519,594,674,687]⟩,⟨7,281,[66,158,229,287,357,444,517,519,594]⟩,⟨9,282,[66,158,229,287,357,444,517,519,594,674]⟩,⟨0,151,[66,158,229,287,357,444,519,594,680]⟩,⟨0,283,[66,158,229,287,357,444,519,594,674,680]⟩]⟩
def layer10 : Array State := #[row10_0,row10_1,row10_2,row10_3,row10_4,row10_5,row10_6,row10_7,row10_8,row10_9,row10_10,row10_11]
def row11_0 : State := ⟨[66,158,229,287,357,444,519,594],[⟨0,0,[41,66,158,229,287,357,444,519,594]⟩,⟨0,1,[66,158,177,229,287,357,444,519,594]⟩,⟨2,1,[66,158,229,253,287,357,444,519,594]⟩,⟨0,2,[66,85,158,229,287,357,444,519,594]⟩,⟨0,3,[66,158,229,270,287,357,444,519,594]⟩,⟨3,1,[66,158,229,287,310,357,444,519,594]⟩,⟨1,2,[66,103,158,229,287,357,444,519,594]⟩,⟨1,3,[66,158,229,287,322,357,444,519,594]⟩,⟨4,2,[66,158,183,229,287,357,444,519,594]⟩,⟨4,3,[66,158,229,287,332,357,444,519,594]⟩,⟨0,4,[54,66,158,229,287,357,444,519,594]⟩,⟨0,5,[66,158,229,287,357,380,444,519,594]⟩,⟨6,6,[7,66,158,229,287,357,444,519,594]⟩,⟨0,7,[66,158,229,287,357,425,444,519,594]⟩,⟨8,6,[20,66,158,229,287,357,444,519,594]⟩,⟨2,7,[66,158,229,287,357,444,494,519,594]⟩,⟨9,6,[32,66,158,229,287,357,444,519,594]⟩,⟨3,7,[66,158,229,287,357,444,519,574,594]⟩,⟨0,6,[0,66,158,229,287,357,444,519,594]⟩,⟨6,7,[66,158,229,287,357,444,468,519,594]⟩,⟨0,8,[66,118,158,229,287,357,444,519,594]⟩,⟨0,9,[66,158,229,287,357,444,480,519,594]⟩,⟨2,8,[66,158,202,229,287,357,444,519,594]⟩,⟨2,9,[66,158,229,287,357,444,498,519,594]⟩,⟨3,10,[35,66,158,229,287,357,444,519,594]⟩,⟨3,11,[66,158,229,287,357,444,519,594,691]⟩,⟨6,0,[66,158,229,287,341,357,444,519,594]⟩,⟨6,1,[66,158,229,287,357,444,465,519,594]⟩,⟨1,6,[1,66,158,229,287,357,444,519,594]⟩,⟨7,7,[66,158,229,287,357,444,519,553,594]⟩,⟨1,8,[66,141,158,229,287,357,444,519,594]⟩,⟨1,9,[66,158,229,287,357,444,519,563,594]⟩,⟨2,10,[22,66,158,229,287,357,444,519,594]⟩,⟨2,11,[66,158,229,287,357,444,519,594,681]⟩,⟨3,8,[66,158,229,279,287,357,444,519,594]⟩,⟨3,9,[66,158,229,287,357,444,519,580,594]⟩,⟨7,1,[66,158,229,287,357,444,519,549,594]⟩,⟨6,2,[66,158,229,287,357,391,444,519,594]⟩,⟨6,3,[66,158,229,287,357,444,519,588,594]⟩,⟨4,6,[3,66,158,229,287,357,444,519,594]⟩,⟨10,7,[66,158,229,287,357,444,519,594,629]⟩,⟨0,10,[10,66,158,229,287,357,444,519,594]⟩,⟨0,11,[66,158,229,287,357,444,519,594,674]⟩,⟨4,8,[66,158,220,229,287,357,444,519,594]⟩,⟨4,9,[66,158,229,287,357,444,519,594,637]⟩,⟨5,8,[66,158,229,284,287,357,444,519,594]⟩,⟨5,9,[66,158,229,287,357,444,519,594,644]⟩,⟨10,1,[66,158,229,287,357,444,519,594,625]⟩,⟨8,2,[66,158,229,287,357,434,444,519,594]⟩,⟨8,3,[66,158,229,287,357,444,519,594,656]⟩,⟨9,2,[66,158,229,287,357,444,511,519,594]⟩,⟨9,3,[66,158,229,287,357,444,519,594,665]⟩]⟩
def layer11 : Array State := #[row11_0]
def layer : Nat → Array State
  | 0 => layer0
  | 1 => layer1
  | 2 => layer2
  | 3 => layer3
  | 4 => layer4
  | 5 => layer5
  | 6 => layer6
  | 7 => layer7
  | 8 => layer8
  | 9 => layer9
  | 10 => layer10
  | 11 => layer11
  | _ => #[]

def vals (pool : List Nat) := pool.map fun j => dict[j]?.getD 0
def stamp (xs : List Sig) := xs.foldl (fun t w => t+w.toNat) 0
def same (xs ys : List Sig) := xs.all (fun w => ys.contains w) && ys.all (fun w => xs.contains w)
def accept (entry : State) (k : Nat) :=
  let refs := entry.links.map fun lk => let w := vals lk.pool; (stamp w,w)
  checks (fun xs => let h := stamp xs; refs.any fun p => p.1==h && same xs p.2) k (vals entry.pool)
def refOK (prev : Array State) (lk : Link) :=
  if lk.perm<12 then
    match prev[lk.index]? with
    | none => false
    | some s => same ((vals lk.pool).map (phi lk.perm)) (vals s.pool)
  else false

def rowOK (prev : Array State) (k : Nat) (s : State) :=
  decide (vals s.pool).Nodup && (s.links.all (refOK prev) && accept s k)

theorem same_set {xs ys : List Sig} (h : same xs ys=true) : xs.toFinset=ys.toFinset := by
  have halves := Bool.and_eq_true_iff.mp h
  ext w
  simp only [List.mem_toFinset]
  constructor
  · intro m
    simpa using List.all_eq_true.mp halves.1 w m
  · intro m
    simpa using List.all_eq_true.mp halves.2 w m

theorem link_sound {k : Nat} {prev : Array State} {lk : Link}
    (known : ∀ e∈prev.toList,ImpossibleM target k (vals e.pool).toFinset)
    (ok : refOK prev lk=true) : ImpossibleM target k (vals lk.pool).toFinset := by
  unfold refOK at ok
  split at ok
  · rename_i inRange
    cases hg : prev[lk.index]? with
    | none => simp [hg] at ok
    | some e =>
      have eq : ((vals lk.pool).map (phi lk.perm)).toFinset = (vals e.pool).toFinset :=
        same_set (by simpa [hg] using ok)
      have inList : prev.toList[lk.index]?=some e := by simpa using hg
      have pre := known _ (List.mem_of_getElem? inList)
      intro j t short none live
      have moved := target_transport (⟨lk.perm,inRange⟩ : Fin 12) live
      have mapped : (vals lk.pool).toFinset.image (phi lk.perm) =
        ((vals lk.pool).map (phi lk.perm)).toFinset := by ext i; simp
      change Live target j t ((vals lk.pool).toFinset.image (phi lk.perm)) at moved
      rw [mapped,eq] at moved
      exact pre j t short none moved
  · contradiction

theorem row_sound {k : Nat} {prev : Array State} {s : State}
    (known : ∀ e∈prev.toList,ImpossibleM target (k-1) (vals e.pool).toFinset)
    (verified : rowOK prev k s=true) : ImpossibleM target k (vals s.pool).toFinset := by
  have outer := Bool.and_eq_true_iff.mp verified
  have inner := Bool.and_eq_true_iff.mp outer.2
  apply node_sound k (vals s.pool) (of_decide_eq_true outer.1) _ inner.2
  intro xs hit
  obtain ⟨p,hp,pass⟩ := List.any_eq_true.mp hit
  obtain ⟨lk,hlk,rfl⟩ := List.mem_map.mp hp
  have eq : xs.toFinset=(vals lk.pool).toFinset := same_set (Bool.and_eq_true_iff.mp pass).2
  rw [eq]
  exact link_sound known (List.all_eq_true.mp inner.1 _ hlk)

def good (k : Nat) := (layer k).toList.all (rowOK (layer (k-1)) k)

theorem closed_levels (k : Nat)
    (numerical : ∀ j, j≤k → good j=true) :
    ∀ e∈(layer k).toList,ImpossibleM target k (vals e.pool).toFinset := by
  induction k with
  | zero =>
    intro e member
    change e∈([] : List State) at member
    contradiction
  | succ k ih =>
    intro e member
    apply row_sound (k:=k+1) (prev:=layer k)
    · exact ih (fun j hj => numerical j (by omega))
    · exact List.all_eq_true.mp (numerical (k+1) le_rfl) e member

theorem check0 : good 0=true := by decide +kernel
theorem check1 : good 1=true := by decide +kernel
theorem check2 : good 2=true := by decide +kernel
theorem check3 : good 3=true := by decide +kernel
theorem check4 : good 4=true := by decide +kernel
theorem check5 : good 5=true := by decide +kernel
theorem check6 : good 6=true := by decide +kernel
theorem check7 : good 7=true := by decide +kernel
theorem check8 : good 8=true := by decide +kernel
theorem check9 : good 9=true := by decide +kernel
theorem check10 : good 10=true := by decide +kernel
theorem check11 : good 11=true := by decide +kernel
theorem checked (j : Nat) (bound : j≤11) : good j=true := by
  interval_cases j <;> first | exact check0 | exact check1 | exact check2 | exact check3 | exact check4
                             | exact check5 | exact check6 | exact check7 | exact check8 | exact check9
                             | exact check10 | exact check11

theorem closed_fast : ImpossibleM target 11 inputs.toFinset := by
  have e : row11_0∈(layer 11).toList := by change row11_0∈[row11_0]; exact List.mem_cons_self
  have computed := closed_levels 11 checked row11_0 e
  have ident : (vals row11_0.pool).toFinset=inputs.toFinset := by decide +kernel
  rwa [ident] at computed

theorem theta_cost (C : Circuit) (mono : PEqualNP.MetaComplexity.Monotone2 C)
    (truth : ∀ x : Fin 8→Bool,C.eval (List.ofFn x)=true ↔
       ∃ a b : Fin 8,(a.val,b.val)∈pairs ∧ x a=true ∧ x b=true) : 12≤C.size := by
  have co (x : Fin 8→Bool) : C.eval (List.ofFn x)=graph x := by
    apply Bool.eq_iff_iff.mpr
    rw [graph,decide_eq_true_eq]
    exact truth x
  obtain ⟨k,hk,h⟩ := allLive C mono co
  by_contra! short
  exact closed_fast k 0 (by omega) rfl h

end PEqualNP.Outside.Theta1739

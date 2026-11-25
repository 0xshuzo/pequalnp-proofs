import Mathlib
import PEqualNP.Defs

namespace Window2056
open PEqualNP.CircuitLowerBounds
abbrev Sig := BitVec 72
def zero : Sig := 0
def one : Sig := BitVec.allOnes 72
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

def bit (i : Fin 72) (a : Sig) : Bool := a.getLsbD i.val
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

abbrev Row := Fin 72
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

def target : Sig := 68719476735
def bank : List Sig := [0,64424509440,314824432186729365519,944473296560200876032,944473296560436805632,944473296564211679232,1574122160933641912560,1574122160933641916160,1574122160933641973760,2203771025307114406128,2203771025307114409728,2203771025307114467328,2203771025307350335728,2203771025307350339328,2203771025307350396928,2203771025311125209328,2203771025311125212928,2203771025311125270528,3148244321867283890175,3777893186245035491328,4722366482800925736960,4722366482800925737200,4722366482800925740800,4722366482800925798400,4722366482800926720015,4722366482800941465600,4722366482800941465840,4722366482800941469440,4722366482800941527040,4722366482801177395200,4722366482801177395440,4722366482801177399040,4722366482801177456640,4722366482804952268800,4722366482804952269040,4722366482804952272640,4722366482804952330240,4722366482865350246400,4722366482865350246640,4722366482865350250240,4722366482865350307840,4722366482865351229455,4722366482865365975040,4722366482865366036480,4722366482865601904640,4722366482865601908480,4722366482869376778240,4722366482869376778480]
def required : List Sig := [64424509440,314824432186729365519,944473296560200876032,944473296560436805632,944473296564211679232,1574122160933641912560,1574122160933641916160,1574122160933641973760,3148244321867283890175,3777893186245035491328]
def column (w : Sig) := w &&& ~~~(w >>> 36)
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
  · have geom : ∀ r : Fin 72,bit r target=true →
        r.val+36<72 ∧ bit (Fin.ofNat 72 (r.val+36)) target=false := by decide +kernel
    obtain ⟨hv,hn⟩ := geom ⟨i,hi⟩ p
    obtain ⟨v,hm,hp,hh⟩ := mono_row_difference (r := ⟨i,hi⟩) (s := Fin.ofNat 72 (i+36)) z none p hn
    have hn' : v.getLsbD (i+36)=false := by
      change v.getLsbD ((i+36)%72)=false at hh
      rwa [Nat.mod_eq_of_lt hv] at hh
    have col : (column v).getLsbD i=true := by
      change v.getLsbD i=true at hp
      simp [column,BitVec.getLsbD_ushiftRight,BitVec.getLsbD_not,hi,hp,hn',Nat.add_comm 36 i]
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
def cut (w : Sig) : Nat := if w=64424509440 then 32 else if w=314824432186729365519 then 1 else if w=944473296560200876032 then 22 else if w=944473296560436805632 then 26 else if w=944473296564211679232 then 30 else if w=1574122160933641912560 then 5 else if w=1574122160933641916160 then 9 else if w=1574122160933641973760 then 13 else if w=3148244321867283890175 then 0 else if w=3777893186245035491328 then 16 else 0

set_option maxRecDepth 10000
set_option maxHeartbeats 0
theorem compulsory : ∀ w∈required,
  let i := Fin.ofNat 72 (cut w)
  let j := Fin.ofNat 72 (cut w+36)
  bit i target=true ∧ bit j target=false ∧ ∀ a∈bank,bit i a=true → bit j a=false → a=w := by
  have verify : required.all (fun w =>
    let i:=Fin.ofNat 72 (cut w)
    let j:=Fin.ofNat 72 (cut w+36)
    (bit i target && !bit j target) && bank.all (fun a=>decide (bit i a=true → bit j a=false → a=w)))=true := by decide +kernel
  intro w hw
  have ok := Bool.and_eq_true_iff.mp (List.all_eq_true.mp verify w hw)
  have both := Bool.and_eq_true_iff.mp ok.1
  refine ⟨both.1,?_,fun a ha => of_decide_eq_true (List.all_eq_true.mp ok.2 a ha)⟩
  simpa using both.2

theorem noNine : tree 9 required=true := by decide +kernel

theorem lower (C : Circuit) (hC : PEqualNP.MetaComplexity.Monotone2 C)
    (w : List Sig) (legal : ∀ v∈w,v∈bank)
    (correct : ∀ r : Row, C.eval (w.map (bit r)) = bit r target) : 10≤C.size := by
  by_contra! small
  have weq : (execute C.gates w).getD C.output zero=target := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    change bit r ((execute C.gates w).getD C.output zero)=bit r target
    rw [←b_read,execute_bits _ _ _ (fun g hg => by
      have op : g.op=.and ∨ g.op=.or := by simpa using (hC g hg).1
      rcases op with e | e <;> simp [e])]
    exact correct r
  have rep := get_rep (execute C.gates w) C.output
  rw [weq] at rep
  have pro : proper target := by unfold proper; decide
  obtain ⟨k,S,hk,run,sub⟩ := extractM C.gates w hC pro (rep.resolve_right (fun n => n pro))
  have needed : required.toFinset ⊆ S := by
    intro a mem
    obtain ⟨yes,no,only⟩ := compulsory a (List.mem_toFinset.mp mem)
    obtain ⟨v,hv,hp,hn⟩ := mono_row_difference run rfl yes no
    exact (only _ (legal _ (sub _ hv)) hp hn) ▸ hv
  have size := (live_size run).2
  have ten : required.toFinset.card=10 := by decide
  have eq : required.toFinset=S := Finset.eq_of_subset_of_card_le needed (by change k≤C.size at hk; omega)
  exact tree_sound 9 required (by decide) noNine k 0 (by change k≤C.size at hk; omega) rfl (eq.symm ▸ run)
def rowData : List (Nat×Nat) := [(1,1),(1,1),(1,1),(1,1),(1,2),(1,2),(1,2),(1,2),(1,8),(1,8),(1,8),(1,8),(1,512),(1,512),(1,512),(1,512),(2,1),(2,1),(2,1),(2,1),(2,4),(2,4),(2,4),(2,4),(2,256),(2,256),(2,256),(2,256),(2,4096),(2,4096),(2,4096),(2,4096),(4,128),(4,128),(4,128),(4,128),(0,8191),(1,7668),(2,3834),(3,3312),(0,8191),(1,7668),(2,3834),(3,3312),(0,8191),(1,7668),(2,3834),(3,3312),(0,8191),(1,7668),(2,3834),(3,3312),(0,8191),(1,7668),(2,3834),(3,3312),(0,8191),(1,7668),(2,3834),(3,3312),(0,8191),(1,7668),(2,3834),(3,3312),(0,8191),(1,7668),(2,3834),(3,3312),(0,8191),(1,7668),(2,3834),(3,3312)]
def raw : List Sig := [3148244321867283890175,3777893186245035491328,64424509440,0,0,0,0,0,0,0,0,0,0,314824432186729365519,1574122160933641912560,944473296560200876032,1574122160933641916160,4722366482800925736960,4722366482800925736960,4722366482800925736960,4722366482865350246400,944473296560436805632,1574122160933641973760,4722366482800925736960,4722366482800925736960,944473296564211679232]
def rd (r : Row) : Nat×Nat := rowData.getD r.val (0,0)
def point (r : Row) (p : Fin 13) := (rd r).1.testBit p.val
def line (r : Row) (l : Fin 13) := (rd r).2.testBit l.val
def incident (p l : Fin 13) : Bool := decide ((p.val+l.val)%13 ∈ ([0,1,3,9] : List Nat))
def completeStar (p : Fin 13) (r : Row) := point r p && (List.finRange 13).any fun l => incident p l && line r l
def old : Sig := 64424509440
theorem planeOutput : ∀ r : Row, bit r target = (List.finRange 13).any (fun p => completeStar p r) := by decide +kernel
theorem inputsAllowed : ∀ w∈raw,w∈bank := by
  have check : raw.all (fun w=>decide (w∈bank))=true := by decide +kernel
  intro w hw
  exact of_decide_eq_true (List.all_eq_true.mp check w hw)
theorem inputValues : ∀ r : Row,∀ i : Fin 26,bit r (raw.getD i.val zero)=
    (if i.val<13 then point r (Fin.ofNat 13 i.val) else line r (Fin.ofNat 13 i.val)) := by decide +kernel
theorem finished : ∀ p : Fin 13,2≤p.val → (∀ r,completeStar p r=false) ∨ (∀ r,completeStar p r=bit r old) := by decide +kernel
theorem accumulates : zero∈bank ∧ old∈bank ∧ (zero ||| old)=old ∧ (old ||| zero)=old ∧ (old ||| old)=old := by decide
def neigh : List (List Nat) := [[0,1,3,9],[0,2,8,12],[1,7,11,12],[0,6,10,11],[5,9,10,12],[4,8,9,11],[3,7,8,10],[2,6,7,9],[1,5,6,8],[0,4,5,7],[3,4,6,12],[2,3,5,11],[1,2,4,10]]
theorem neigh_ok : ∀ p l : Fin 13, l.val∈neigh.getD p.val [] ↔ incident p l=true := by decide +kernel
def group (p : Fin 13) (m : Fin 16) := (List.finRange 4).foldl (fun v i =>
  if m.val.testBit i.val then v ||| raw.getD (13+(neigh.getD p.val []).getD i.val 0) zero else v) zero
theorem groupsAllowed : ∀ p : Fin 13,2≤p.val → ∀ m : Fin 16,group p m ∈bank := by decide +kernel
end Window2056

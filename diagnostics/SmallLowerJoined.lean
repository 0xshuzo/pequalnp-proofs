import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3678
open CircuitLowerBounds MetaComplexity MetaComplexity.NestedCover EdgeOwnership TopForm
-- The live-signal extraction adapts the proofs of L_meta_5002 and L_meta_3640.
abbrev Sig := BitVec 128
def zero : Sig := 0
def one : Sig := BitVec.allOnes 128
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


def bit (i : Fin 128) (a : Sig) : Bool := a.getLsbD i.val
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





def kept {α : Type} (save : Bool) (x : α) (xs : List α) := if save then x::xs else xs


theorem kept_nd {α : Type} (k : Bool) (a : α) (l : List α)
    (hn : l.Nodup) (ha : a ∉ l) : (kept k a l).Nodup := by cases k <;> simp [kept,hn,ha]

theorem kept_fin (k : Bool) (a : Sig) (l : List Sig) :
    (kept k a l).toFinset = if k then insert a l.toFinset else l.toFinset := by
  cases k <;> simp [kept]


abbrev Row := Fin 128

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


def childTwo (ws : List Sig) (a b : Sig) (d ka kb : Bool) : List Sig :=
  bin d a b :: kept ka a (kept kb b ((ws.erase a).erase b))

theorem erase_fin {l : List Sig} (h : l.Nodup) (a : Sig) : (l.erase a).toFinset = l.toFinset.erase a := by
  ext x
  simp [h.mem_erase_iff]


theorem keep_mem {v : List Sig} {w : Sig} (a : Sig) (k : Bool) :
    w ∈ kept k a v ↔ (w=a ∧ k=true) ∨ w∈v := by cases k <;> simp [kept]

theorem childTwo_swap (v : List Sig) (nd : v.Nodup) (a b : Sig) (d ka kb : Bool) :
    (childTwo v a b d ka kb).toFinset = (childTwo v b a d kb ka).toFinset := by
  ext x
  simp only [childTwo,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    keep_mem,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,bin_comm d b a]
  tauto


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

def targetS : Sig := 0xffffffffffffffff
def loRow (i : Fin 64) : Row := ⟨i.val, by omega⟩
def hiRow (i : Fin 64) : Row := ⟨64+i.val, by omega⟩

def direction (x : Sig) : BitVec 64 := (x &&& ~~~(x >>> 64)).setWidth 64
def cuts (ws : List Sig) : BitVec 64 := ws.foldr (fun w v => direction w ||| v) 0

theorem direction_bit (a : Sig) (i : Fin 64) : (direction a).getLsbD i.val = true ↔
    bit (loRow i) a = true ∧ bit (hiRow i) a = false := by
  have hi := i.isLt
  have full : i.val < 128 := by omega
  simp only [direction,bit,loRow,hiRow,BitVec.getLsbD_setWidth,BitVec.getLsbD_and,
    BitVec.getLsbD_not,BitVec.getLsbD_ushiftRight]
  cases a.getLsbD i.val <;> cases a.getLsbD (64+i.val) <;> simp [hi,full]

theorem cuts_bit (ws : List Sig) (i : Fin 64) : (cuts ws).getLsbD i.val=true ↔
    ∃ a ∈ ws, bit (loRow i) a=true ∧ bit (hiRow i) a=false := by
  induction ws with
  | nil => simp [cuts]
  | cons a ws ih =>
    change (direction a ||| cuts ws).getLsbD i.val = true ↔ _
    rw [BitVec.getLsbD_or,Bool.or_eq_true,ih,direction_bit]
    simp

set_option maxRecDepth 16384 in
theorem signs : ∀ i : Fin 64, bit (loRow i) targetS=true ∧ bit (hiRow i) targetS=false := by decide +kernel

theorem cuts_necessary {k S} (h : Live targetS k 0 S) {ws : List Sig} (he : ws.toFinset=S) :
    cuts ws=BitVec.allOnes 64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  let i : Fin 64 := ⟨j,hj⟩
  rw [BitVec.getLsbD_allOnes]
  simp only [hj,decide_true]
  obtain ⟨w,hw,hp,hn⟩ := mono_row_difference h rfl (signs i).1 (signs i).2
  exact (cuts_bit ws i).mpr ⟨w,List.mem_toFinset.mp (he.symm ▸ hw),hp,hn⟩

def pairsOK {α : Type} (test : α → α → Bool) : List α → Bool
  | [] => true
  | a::tail => tail.all (test a) && pairsOK test tail

theorem pairsOK_mem {α : Type} {test : α → α → Bool} {ws : List α} {a b : α}
    (h : pairsOK test ws=true) (ha : a∈ws) (hb : b∈ws) (ne : a≠b) :
    test a b=true ∨ test b a=true := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    simp only [pairsOK,Bool.and_eq_true,List.all_eq_true] at h
    rcases List.mem_cons.mp ha with rfl | atail
    · exact Or.inl (h.1 b ((List.mem_cons.mp hb).resolve_left (Ne.symm ne)))
    · rcases List.mem_cons.mp hb with rfl | btail
      · exact Or.inr (h.1 a atail)
      · exact ih h.2 atail btail

def moveOK (next : List Sig → Bool) (cap : Nat) (ws : List Sig) (a b : Sig) (d : Bool) :=
  let z := bin d a b
  if z=zero ∨ z=one ∨ z∈ws then true else
    let rest := (ws.erase a).erase b
    let attempt := fun ka kb =>
      let child := z::kept ka a (kept kb b rest)
      if child.length>cap then true else next child
    attempt false false && attempt true false && attempt false true && attempt true true

def noSmall : Nat → List Sig → Bool
  | 0,ws => !(ws.contains targetS)
  | cap+1,ws =>
    if cuts ws != BitVec.allOnes 64 then true else
    if targetS∈ws then false else
    if ws.Nodup then
      pairsOK (fun a b => moveOK (noSmall cap) (cap+1) ws a b false &&
                           moveOK (noSmall cap) (cap+1) ws a b true) ws
    else false

theorem moveOK_child {next : List Sig → Bool} {cap ws a b d}
    (m : moveOK next cap ws a b d=true) {ka kb : Bool}
    (pro : proper (bin d a b)) (fr : bin d a b ∉ ws)
    (len : (childTwo ws a b d ka kb).length ≤ cap) :
    next (childTwo ws a b d ka kb)=true := by
  unfold moveOK at m
  have skip : ¬ (bin d a b=zero ∨ bin d a b=one ∨ bin d a b∈ws) :=
    not_or.mpr ⟨pro.1,not_or.mpr ⟨pro.2,fr⟩⟩
  simp only [if_neg skip,Bool.and_eq_true] at m
  have e : (if (childTwo ws a b d ka kb).length>cap then true else
      next (childTwo ws a b d ka kb)) = true := by
    cases ka <;> cases kb
    · exact m.1.1.1
    · exact m.1.2
    · exact m.1.1.2
    · exact m.2
  rwa [if_neg (Nat.not_lt.mpr len)] at e

theorem noSmall_sound (cap : Nat) (ws : List Sig) (good : noSmall cap ws=true) :
    ImpossibleM targetS cap ws.toFinset := by
  induction cap generalizing ws with
  | zero =>
    intro k t hk ht run
    have kk : k=0 := by omega
    subst k
    obtain ⟨_,eq,_⟩ := run
    have mem : targetS∈ws := List.mem_toFinset.mp (eq.symm ▸ Finset.mem_singleton_self _)
    simpa [noSmall,mem] using good
  | succ cap ih =>
    by_cases cut : cuts ws=BitVec.allOnes 64
    · by_cases out : targetS ∈ ws
      · simp [noSmall,cut,out] at good
      by_cases nd : ws.Nodup
      · have inner : pairsOK (fun a b => moveOK (noSmall cap) (cap+1) ws a b false &&
            moveOK (noSmall cap) (cap+1) ws a b true) ws = true := by
            simpa [noSmall,cut,out,nd] using good
        apply enum_stepM nd out
        intro a ha b hb d ka kb ne fr pro len
        have step (x y : Sig) (v w : Bool)
            (hp : proper (bin d x y)) (hf : bin d x y ∉ ws)
            (hl : (childTwo ws x y d v w).length ≤ cap+1)
            (h : moveOK (noSmall cap) (cap+1) ws x y false &&
                 moveOK (noSmall cap) (cap+1) ws x y true = true) :
            ImpossibleM targetS cap (childTwo ws x y d v w).toFinset := by
          simp only [Bool.and_eq_true] at h
          apply ih
          apply moveOK_child (ka:=v) (kb:=w) (cap:=cap+1) (pro:=hp) (fr:=hf) (len:=hl)
          cases d <;> first | exact h.1 | exact h.2
        rcases pairsOK_mem inner ha hb ne with h | h
        · exact step a b ka kb pro fr len h
        · rw [childTwo_swap _ nd]
          have llen : (childTwo ws b a d kb ka).length = (childTwo ws a b d ka kb).length := by
            have hba : b∈ws.erase a := (List.mem_erase_of_ne ne.symm).mpr hb
            have hab : a∈ws.erase b := (List.mem_erase_of_ne ne).mpr ha
            cases ka <;> cases kb <;> simp [childTwo,kept,List.length_erase_of_mem hba,
              List.length_erase_of_mem hab,List.length_erase_of_mem ha,List.length_erase_of_mem hb]
          exact step b a kb ka (bin_comm d a b ▸ pro) (bin_comm d a b ▸ fr) (llen.symm ▸ len) h
      · simp [noSmall,cut,out,nd] at good
    · intro k t hk ht run
      subst t
      exact cut (cuts_necessary run rfl)

def smallRoots : List Sig := [0x94a5294a5294a5290fffe00000007fff,0x5294a5294a5294a5f00000003fff8000,0x318c6318c6318c6300001fffc0000000,0x294a5294a5294a52f003e000000f801f,0x4a5294a5294a5294007c0007c00003e0,0x8c6318c6318c6318000000f801f00000,0x8421084210842100f801f003e007c00]

abbrev coreSeven := edgeGraph 7 [(0,3),(0,4),(0,6),(1,3),(1,5),(1,6),(2,4),(2,5),(2,6)]

def inputPoint (r : Row) (j : Fin 7) : Bool :=
  bit r (smallRoots.getD j.val zero)

def forcedB (roots : List Sig) (a : Sig) : Bool :=
  (List.finRange 64).any fun i =>
    roots.all fun b => (b == a) || !((direction b).getLsbD i.val)

set_option maxRecDepth 16384
set_option maxHeartbeats 0

theorem smallRootsNeeded : ∀ a ∈ smallRoots, forcedB smallRoots a = true := by
  have all : smallRoots.all (forcedB smallRoots) = true := by decide +kernel
  exact List.all_eq_true.mp all

theorem small_bank {k S} (run : Live targetS k 0 S) (sub : ∀ v ∈ S, v ∈ smallRoots) :
    S=smallRoots.toFinset := by
  ext a
  refine ⟨fun h => List.mem_toFinset.mpr (sub a h),?_⟩
  intro h
  have chk := smallRootsNeeded a (List.mem_toFinset.mp h)
  obtain ⟨i,_,keep⟩ := List.any_eq_true.mp chk
  obtain ⟨v,hv,h1,h2⟩ := mono_row_difference run rfl (signs i).1 (signs i).2
  have mark := (direction_bit v i).mpr ⟨h1,h2⟩
  have pin := List.all_eq_true.mp keep v (sub v hv)
  have eq : v=a := by simpa [mark] using pin
  exact eq ▸ hv

theorem smallRoots_inputs (r : Row) : List.ofFn (inputPoint r) = smallRoots.map (bit r) := by
  rfl

theorem graphSamples : ∀ r : Row, graphFun coreSeven ∅ (inputPoint r) = bit r targetS := by
  decide +kernel

theorem coreSeven_lower (C : Circuit) (binary : IsAO2 7 C)
    (eq : circuitFun 7 C = graphFun coreSeven ∅)
    (numeric : noSmall 9 smallRoots=true) : 10 ≤ C.size := by
  have legal : ∀ g ∈ C.gates, g.op∈({GateOp.and,GateOp.or} : Set GateOp) ∧ g.inputs.length≤2 := by
    intro g hg
    exact ⟨by simpa using binary.1 g hg, Nat.le_of_eq (binary.2.2 g hg)⟩
  have good : ∀ g ∈ C.gates, g.op∈({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) := by
    intro g hg
    rcases binary.1 g hg with h | h <;> simp [h]
  have same : (execute C.gates smallRoots).getD C.output zero = targetS := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    let r : Row := ⟨i,hi⟩
    change bit r ((execute C.gates smallRoots).getD C.output zero) = bit r targetS
    rw [←b_read,execute_bits _ _ _ good,←smallRoots_inputs,←graphSamples]
    exact congrFun eq (inputPoint r)
  have hp : proper targetS := by unfold proper; decide +kernel
  have rep := get_rep (execute C.gates smallRoots) C.output
  rw [same] at rep
  obtain ⟨k,S,hk,run,sub⟩ := extractM C.gates smallRoots legal hp (rep.resolve_right (fun h => h hp))
  have shape := small_bank run sub
  by_contra! short
  change C.gates.length<10 at short
  exact noSmall_sound 9 smallRoots numeric k 0 (by omega) rfl (shape ▸ run)
end PEqualNP.Outside.L_meta_3678

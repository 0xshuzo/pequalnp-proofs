import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19374.Binary
open PEqualNP.CircuitLowerBounds
abbrev Sig := BitVec 308
def zero : Sig := 0
def one : Sig := BitVec.allOnes 308
def neg (a : Sig) : Sig := ~~~a
def bin (d : Nat) (a b : Sig) : Sig :=
  if d=0 then a &&& b else if d=1 then a ||| b else if d=2 then a &&& ~~~b else ~~~a &&& b
def proper (a : Sig) : Prop := a ≠ zero ∧ a ≠ one
def allowed (u : Bool) (d : Nat) : Prop := d<2 ∨ (u=true ∧ d<4)
def flipOp (d : Nat) := if d=2 then 3 else if d=3 then 2 else d
theorem allowed_four {u d} (h : allowed u d) : d=0 ∨ d=1 ∨ (u=true ∧ d=2) ∨ (u=true ∧ d=3) := by
  rcases h with h | ⟨h,j⟩
  · omega
  · have : d=0 ∨ d=1 ∨ d=2 ∨ d=3 := by omega
    rcases this with h1 | h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr (Or.inl ⟨h,h1⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨h,h1⟩))
theorem bin_flip {u d} (h : allowed u d) (a b : Sig) : bin d a b = bin (flipOp d) b a := by
  rcases allowed_four h with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩ <;> simp [bin,flipOp,BitVec.and_comm,BitVec.or_comm]
theorem flip_flip {u d} (h : allowed u d) : allowed u (flipOp d) ∧ flipOp (flipOp d)=d := by
  rcases allowed_four h with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
  all_goals simp_all [flipOp,allowed]

def Live (u : Bool) (target : Sig) : Nat → Finset Sig → Prop
  | 0,S => S={target} ∧ proper target
  | k+1,S => ∃ (U : Finset Sig) (a b : Sig) (d : Nat), allowed u d ∧ S=insert a (insert b U) ∧
      proper a ∧ proper b ∧ a ≠ b ∧
      bin d a b ∉ insert a (insert b U) ∧ Live u target k (insert (bin d a b) U)
theorem Live.stop {u} {target : Sig} (hp : proper target) : Live u target 0 {target} := ⟨rfl,hp⟩
theorem Live.binary {u} {target : Sig} {k : Nat} {U : Finset Sig} {a b : Sig} {d : Nat} (hd : allowed u d)
    (ha : proper a) (hb : proper b) (hab : a ≠ b)
    (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live u target k (insert (bin d a b) U)) :
    Live u target (k+1) (insert a (insert b U)) :=
  ⟨U,a,b,d,hd,rfl,ha,hb,hab,hfresh,tail⟩
theorem Live.ind {u} {target : Sig} {motive : ∀ (k : Nat) (S : Finset Sig), Live u target k S → Prop}
    (stop : ∀ (hp : proper target), motive 0 {target} (Live.stop hp))
    (binary : ∀ {k : Nat} {U : Finset Sig} {a b : Sig} {d : Nat} (hd : allowed u d)
      (ha : proper a) (hb : proper b) (hab : a ≠ b)
      (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live u target k (insert (bin d a b) U)),
      motive k (insert (bin d a b) U) tail →
      motive (k+1) (insert a (insert b U)) (Live.binary hd ha hb hab hfresh tail))
    {k : Nat} {S : Finset Sig} (h : Live u target k S) : motive k S h := by
  induction k generalizing S with
  | zero =>
    obtain ⟨rfl,hp⟩ := h
    exact stop hp
  | succ k ih =>
    obtain ⟨U,a,b,d,hd,rfl,ha,hb,hab,hf,tail⟩ := h
    exact binary hd ha hb hab hf tail (ih tail)

private lemma live_proper {u target k S} (h : Live u target k S) : ∀ a ∈ S, proper a := by
  induction h using Live.ind with
  | stop hp => simpa using hp
  | binary hd ha hb hab hf _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha,hb,fun a h => ih a (Finset.mem_insert_of_mem h)⟩

private lemma live_size {u target k S} (h : Live u target k S) : S.card ≤ k+1 := by
  induction h using Live.ind with
  | stop hp => simp
  | @binary k U a b d hd ha hb hab hf _ ih =>
    have hu : bin d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1 := Finset.card_insert_le (a := a) (s := insert b U)
    have h2 := Finset.card_insert_le (a := b) (s := U)
    omega

def bit (i : Fin 308) (a : Sig) : Bool := a.getLsbD i.val
private lemma bit_zero (i) : bit i zero = false := by simp [bit,zero]
private lemma bit_one (i) : bit i one = true := by unfold bit one; rw [BitVec.getLsbD_allOnes]; simp
private lemma bit_neg (i) (a : Sig) : bit i (neg a) = !(bit i a) := by simp [bit,neg,i.isLt]
private lemma bit_bin (i d) (a b : Sig) : bit i (bin d a b) =
    (if d=0 then bit i a && bit i b else if d=1 then bit i a || bit i b else
      if d=2 then bit i a && !(bit i b) else !(bit i a) && bit i b) := by
  unfold bin
  split_ifs <;> simp [bit]
theorem bit_ext {a b : Sig} (h : ∀ i, bit i a = bit i b) : a=b :=
  BitVec.eq_of_getLsbD_eq fun j hj => h ⟨j,hj⟩

def nrm (u : Bool) (a : Sig) : Sig := if u && bit 0 a then neg a else a
theorem nrm_false (a : Sig) : nrm false a = a := rfl
theorem nrm_bit (a : Sig) : bit 0 (nrm true a) = false := by
  cases h : bit 0 a <;> simp [nrm,h,bit_neg]
theorem nrm_id {u} {a : Sig} (h : bit 0 a = false) : nrm u a = a := by simp [nrm,h]
theorem neg_neg' (a : Sig) : neg (neg a) = a := by simp [neg]
theorem nrm_neg (a : Sig) : nrm true (neg a) = nrm true a := by
  cases h : bit 0 a <;> simp [nrm,h,bit_neg,neg_neg']
theorem proper_neg {a : Sig} (h : proper (neg a)) : proper a := by
  refine ⟨?_,?_⟩
  · rintro rfl
    exact h.2 (by simp [neg,zero,one])
  · rintro rfl
    exact h.1 (by simp [neg,zero,one])
theorem proper_nrm {u} {a : Sig} (h : proper (nrm u a)) : proper a := by
  unfold nrm at h
  split at h
  · exact proper_neg h
  · exact h
def prime (d : Bool) (a b : Sig) := if d then a ||| b else a &&& b
theorem bit_prime (i) (d : Bool) (a b : Sig) : bit i (prime d a b) =
    (if d then bit i a || bit i b else bit i a && bit i b) := by cases d <;> simp [prime,bit]
theorem nrm_prime (d : Bool) (a b : Sig) :
    ∃ e, e<4 ∧ nrm true (prime d a b) = bin e (nrm true a) (nrm true b) := by
  refine ⟨if d then (if bit 0 a then (if bit 0 b then 0 else 2) else (if bit 0 b then 3 else 1))
    else (if bit 0 a then (if bit 0 b then 1 else 3) else (if bit 0 b then 2 else 0)),?_,?_⟩
  · split_ifs <;> omega
  · apply bit_ext
    intro i
    cases d <;> cases ha : bit 0 a <;> cases hb : bit 0 b <;>
      simp only [nrm,bit_prime,ha,hb,bit_bin,bit_neg,Bool.true_and,Bool.false_and,Bool.and_true,Bool.and_false,Bool.false_or,
        Bool.or_false,Bool.true_or,Bool.or_true,Bool.false_eq_true,ite_true,ite_false] <;>
      cases hx : bit i a <;> cases hy : bit i b <;> simp [hx,hy,bit_neg,bit_prime]

def gv (w : List Sig) (g : Gate) : Sig :=
  let xs := g.inputs.map (fun i => w.getD i zero)
  match g.op with
  | .and => xs.foldr (prime false) one
  | .or => xs.foldr (prime true) zero
  | .not => neg (xs.headD zero)
  | _ => zero

def execute (gs : List Gate) (w : List Sig) : List Sig :=
  gs.foldl (fun l g => l ++ [gv l g]) w

def represented (w : List Sig) (v : Sig) : Prop := v ∈ w ∨ ¬proper v
def Repr (u : Bool) (w : List Sig) (v : Sig) : Prop := represented w (nrm u v)

private lemma bin_laws (a : Sig) :
    bin 0 a one = a ∧ bin 1 a zero = a ∧
    bin 0 a zero = zero ∧ bin 1 a one = one ∧
    bin 0 a a = a ∧ bin 1 a a = a ∧ bin 2 a a = zero ∧ bin 3 a a = zero ∧ bin 2 a zero = a ∧
    bin 3 zero a = a ∧ bin 2 zero a = zero ∧ bin 3 a zero = zero ∧ bin 0 zero a = zero ∧ bin 1 zero a = a ∧
    bin 0 one a = a ∧ bin 1 one a = one := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> apply bit_ext <;> intro i <;>
    simp [bit_bin,bit_zero,bit_one]

private lemma neg_laws : neg zero = one ∧ neg one = zero := by simp [neg,zero,one]

private lemma operand_cases {w : List Sig} {a : Sig} (h : represented w a) :
    a = zero ∨ a = one ∨ a ∈ w ∧ proper a := by
  by_cases hz : a = zero
  · exact Or.inl hz
  by_cases ho : a = one
  · exact Or.inr (Or.inl ho)
  exact Or.inr (Or.inr ⟨h.resolve_right (fun x => x ⟨hz,ho⟩),hz,ho⟩)

def witness (u : Bool) (w : List Sig) (z : Sig) : Prop :=
  ∃ d a b, allowed u d ∧ a ∈ w ∧ b ∈ w ∧ proper a ∧ proper b ∧ a ≠ b ∧ z = bin d a b

private lemma bin_rep {u w a b} (d : Nat) (hd : allowed u d) (ha : represented w a) (hb : represented w b)
    (no : u=true → a ≠ one ∧ b ≠ one) :
    represented w (bin d a b) ∨ witness u w (bin d a b) := by
  have rz : represented w zero := Or.inr (fun h => h.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2 rfl)
  obtain ⟨a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16⟩ := bin_laws a
  obtain ⟨b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14,b15,b16⟩ := bin_laws b
  by_cases he : a=b
  · subst b
    left
    rcases allowed_four hd with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩
    · exact a5.symm ▸ ha
    · exact a6.symm ▸ ha
    · exact a7.symm ▸ rz
    · exact a8.symm ▸ rz
  rcases operand_cases ha with rfl | rfl | ⟨ham,hap⟩
  · left
    rcases allowed_four hd with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩
    · exact b13.symm ▸ rz
    · exact b14.symm ▸ hb
    · exact b11.symm ▸ rz
    · exact b10.symm ▸ hb
  · left
    rcases allowed_four hd with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
    · exact b15.symm ▸ hb
    · exact b16.symm ▸ ro
    · exact absurd rfl (no hu).1
    · exact absurd rfl (no hu).1
  rcases operand_cases hb with rfl | rfl | ⟨hbm,hbp⟩
  · left
    rcases allowed_four hd with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩
    · exact a3.symm ▸ rz
    · exact a2.symm ▸ ha
    · exact a9.symm ▸ ha
    · exact a12.symm ▸ rz
  · left
    rcases allowed_four hd with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
    · exact a1.symm ▸ ha
    · exact a4.symm ▸ ro
    · exact absurd rfl (no hu).2
    · exact absurd rfl (no hu).2
  exact Or.inr ⟨d,a,b,hd,ham,hbm,hap,hbp,he,rfl⟩

theorem norm_ne_one (a : Sig) : nrm true a ≠ one := by
  intro h
  have := nrm_bit a
  rw [h,bit_one] at this
  exact Bool.noConfusion this
theorem prime_rep {u w a b} (d : Bool) (ha : Repr u w a) (hb : Repr u w b) :
    Repr u w (prime d a b) ∨ witness u w (nrm u (prime d a b)) := by
  cases u
  · have e : prime d a b = bin (if d then 1 else 0) a b := by cases d <;> rfl
    have h := bin_rep (u:=false) (if d then 1 else 0) (Or.inl (by split <;> omega)) ha hb (by simp)
    unfold Repr
    simp only [nrm_false] at h ⊢
    rwa [e]
  · obtain ⟨e,he,eq⟩ := nrm_prime d a b
    unfold Repr
    rw [eq]
    exact bin_rep e (Or.inr ⟨rfl,he⟩) ha hb (fun _ => ⟨norm_ne_one a,norm_ne_one b⟩)
theorem repr_const {u w} {v : Sig} (h : v=zero ∨ v=one) : Repr u w v := by
  refine Or.inr fun hp => ?_
  have := proper_nrm hp
  rcases h with rfl | rfl
  · exact this.1 rfl
  · exact this.2 rfl
private lemma get_rep {u} (w : List Sig) (i : Nat) : Repr u (w.map (nrm u)) (w.getD i zero) := by
  simp only [List.getD_eq_getElem?_getD]
  cases h : w[i]? with
  | none => exact repr_const (Or.inl rfl)
  | some a => exact Or.inl (List.mem_map_of_mem (List.mem_of_getElem? h))
theorem repr_neg {w a} (h : Repr true w a) : Repr true w (neg a) := by
  unfold Repr
  rwa [nrm_neg]

def isNot (g : Gate) : Bool := match g.op with
  | .not => true
  | _ => false
private lemma gate_rep (u : Bool) (w : List Sig) (g : Gate)
    (h : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (mono : u=false → isNot g=false) :
    Repr u (w.map (nrm u)) (gv w g) ∨ (isNot g=false ∧ witness u (w.map (nrm u)) (nrm u (gv w g))) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at h
  obtain ⟨ho,hl⟩ := h
  have prim (d : Bool) : Repr u (w.map (nrm u)) ((l.map (fun i => w.getD i zero)).foldr (prime d) (if d then zero else one)) ∨
      witness u (w.map (nrm u)) (nrm u ((l.map (fun i => w.getD i zero)).foldr (prime d) (if d then zero else one))) := by
    have unit (v : Sig) : prime d v (if d then zero else one) = v := by
      apply bit_ext
      intro i
      cases d <;> simp [bit_prime,bit_zero,bit_one]
    cases l with
    | nil => exact Or.inl (repr_const (by cases d <;> simp))
    | cons i l =>
      cases l with
      | nil =>
        simp only [List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,unit]
        exact Or.inl (get_rep w i)
      | cons j l =>
        cases l with
        | cons a l => simp at hl
        | nil =>
          simp only [List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,unit]
          exact prime_rep d (get_rep w i) (get_rep w j)
  rcases ho with rfl | rfl | rfl
  · exact (prim false).imp id (fun h => ⟨rfl,h⟩)
  · exact (prim true).imp id (fun h => ⟨rfl,h⟩)
  · cases u
    · exact absurd (mono rfl) (by simp [isNot])
    left
    cases l with
    | nil => exact repr_const (Or.inr (by simp [gv,neg_laws]))
    | cons i l => exact repr_neg (get_rep w i)

private lemma pull_gate {u target} {w : List Sig} {z : Sig} {k S c} (h : Live u target k S)
    (hz : represented w z ∨ (c=1 ∧ witness u w z)) (sub : ∀ a ∈ S, a ∈ w++[z]) :
    ∃ k' S', k' ≤ k+c ∧ Live u target k' S' ∧ ∀ a ∈ S', a ∈ w := by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ w
    · refine ⟨k,S,by omega,h,?_⟩
      intro a ha
      have hu : a ∈ w ∨ a = z := by simpa using sub a ha
      rcases hu with hu | rfl
      · exact hu
      · exact hw
    · have hp := live_proper h z hm
      rcases hz with hr | ⟨rfl,d,a,b,hd,ha,hb,pa,pb,hab,eq⟩
      · exact False.elim ((hr.resolve_left hw) hp)
      · subst z
        let U := S.erase (bin d a b)
        have ht : Live u target k (insert (bin d a b) U) := by simpa [U,Finset.insert_erase hm] using h
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
        exact ⟨_,_,Nat.le_refl _,Live.binary hd pa pb hab hf ht,by simpa using And.intro ha (And.intro hb hu)⟩
  · refine ⟨k,S,by omega,h,?_⟩
    intro a ha
    have hn : a ≠ z := fun hh => hm (hh ▸ ha)
    simpa [hn] using sub a ha

private lemma extract {u target} (gs : List Gate) (w : List Sig)
    (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (mono : u=false → ∀ g ∈ gs, isNot g=false)
    (hp : proper target) (hout : target ∈ (execute gs w).map (nrm u)) :
    ∃ k S, k ≤ gs.countP (fun g => !isNot g) ∧ Live u target k S ∧ ∀ a ∈ S, a ∈ w.map (nrm u) := by
  induction gs generalizing w with
  | nil => exact ⟨0,{target},by simp,Live.stop hp,by simpa [execute] using hout⟩
  | cons g gs ih =>
    obtain ⟨k,S,hk,ht,hs⟩ := ih (w++[gv w g]) (fun a ha => legal a (by simp [ha]))
      (fun hu a ha => mono hu a (by simp [ha])) hout
    have rep := gate_rep u w g (legal g (by simp)) (fun hu => mono hu g (by simp))
    rw [List.map_append] at hs
    have rep' : represented (w.map (nrm u)) (nrm u (gv w g)) ∨
        ((if isNot g then 0 else 1)=1 ∧ witness u (w.map (nrm u)) (nrm u (gv w g))) :=
      rep.imp id (fun h => ⟨by simp [h.1],h.2⟩)
    obtain ⟨l,T,hl,hu,hT⟩ := pull_gate ht rep' hs
    refine ⟨l,T,?_,hu,hT⟩
    rw [List.countP_cons]
    cases hn : isNot g <;> simp [hn] at hl ⊢ <;> omega

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
      change bit i (prime false _ _) = (_ && _)
      rw [bit_prime]; exact congrArg (fun x => bit i (w.getD a zero) && x) ih
  · induction l with
    | nil => exact bit_zero _
    | cons a l ih =>
      change bit i (prime true _ _) = (_ || _)
      rw [bit_prime]; exact congrArg (fun x => bit i (w.getD a zero) || x) ih
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


abbrev Row := Fin 308
def kept {α : Type} (save : Bool) (x : α) (xs : List α) := if save then x::xs else xs
theorem kept_nd {α : Type} (k : Bool) (a : α) (l : List α)
    (hn : l.Nodup) (ha : a ∉ l) : (kept k a l).Nodup := by cases k <;> simp [kept,hn,ha]

theorem kept_fin (k : Bool) (a : Sig) (l : List Sig) :
    (kept k a l).toFinset = if k then insert a l.toFinset else l.toFinset := by
  cases k <;> simp [kept]

theorem live_row_difference {u T k S} (h : Live u T k S) {r s : Row}
    (diff : bit r T ≠ bit s T) : ∃ a ∈ S, bit r a ≠ bit s a := by
  induction h using Live.ind with
  | stop hp => exact ⟨_,by simp,diff⟩
  | @binary k U a b d hd ha hb hab hf _ ih =>
    obtain ⟨v,hv,hd⟩ := ih
    rcases Finset.mem_insert.mp hv with rfl | hu
    · by_cases aeq : bit r a = bit s a
      · refine ⟨b,by simp,?_⟩
        intro beq
        exact hd (by rw [bit_bin,bit_bin,aeq,beq])
      · exact ⟨a,by simp,aeq⟩
    · exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu),hd⟩

def Impossible (u : Bool) (T : Sig) (cap : Nat) (S : Finset Sig) : Prop :=
  ∀ k, k ≤ cap → ¬Live u T k S

def childTwo (ws : List Sig) (a b : Sig) (d : Nat) (ka kb : Bool) : List Sig :=
  bin d a b :: kept ka a (kept kb b ((ws.erase a).erase b))

theorem erase_fin {l : List Sig} (h : l.Nodup) (a : Sig) : (l.erase a).toFinset = l.toFinset.erase a := by
  ext x
  simp [h.mem_erase_iff]

theorem enum_step {u} {T : Sig} {cap : Nat} {ws : List Sig} (hn : ws.Nodup) (out : T ∉ ws)
    (twoStep : ∀ a ∈ ws, ∀ b ∈ ws, ∀ d, allowed u d → ∀ ka kb, a ≠ b → bin d a b ∉ ws →
      proper (bin d a b) → (childTwo ws a b d ka kb).length ≤ cap →
      Impossible u T (cap-1) (childTwo ws a b d ka kb).toFinset) :
    Impossible u T cap ws.toFinset := by
  classical
  intro k hk h
  generalize he : ws.toFinset = S at h
  induction h using Live.ind with
  | stop hp =>
    have mem : T ∈ ws.toFinset := he.symm ▸ Finset.mem_singleton_self _
    exact out (List.mem_toFinset.mp mem)
  | @binary k U a b d hd ha hb hab hf tail _ =>
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
    have sc := live_size tail
    have len : (childTwo ws a b d ka kb).length ≤ cap := by
      rw [←List.toFinset_card_of_nodup nd,eq]
      omega
    exact twoStep a am b bm d hd ka kb hab fresh hz len k (by omega) (eq.symm ▸ tail)

def original : List Sig := [(BitVec.ofNat 308 (36046397799139329+2^60*(1126449931223104+2^60*(1152921487435370498+2^60*262143)))),(BitVec.ofNat 308 (216278386794835974+2^60*(6758699587338624+2^60*(50356236+2^60*2251799813423104)))),(BitVec.ofNat 308 (866803222076178552+2^60*(135173991746772483+2^60*(1007124720+2^60*(1150669704793161728+2^60*3))))),(BitVec.ofNat 308 (6758699587338624+2^60*(432556773589671948+2^60*(3222799104+2^60*(0+2^60*34359738364))))),(BitVec.ofNat 308 (27034798349354496+2^60*(577305589751840816+2^60*(12891196417+2^60*(0+2^60*(1152921470247108608+2^60*255)))))),(BitVec.ofNat 308 (36046397799139329+2^60*(1126449931223104+2^60*(8392706+2^60*(1150669705329770496+2^60*70334384447487))))),(BitVec.ofNat 308 (360463977991393290+2^60*(11264499312231040+2^60*(35167276146708+2^60*(0+2^60*144044819348447232))))),(BitVec.ofNat 308 (720927955982786580+2^60*(22528998624462080+2^60*(72022409833693224+2^60*(0+2^60*(1008806350873952256+2^60*255)))))),(BitVec.ofNat 308 (11827724277842592+2^60*(756974353781925909+2^60*(1080863916208817472+2^60*1098974756991)))),(BitVec.ofNat 308 (23655448555685184+2^60*(361027202957004842+2^60*(11279796865+2^60*2250700302319488))))]
def initial := original.map (nrm true)
def goal : Sig := (-1 : BitVec 154) ++ (0 : BitVec 154)
def pRows : List (Fin 5 × Fin 5) := [(0, 1), (0, 2), (0, 3), (0, 4), (1, 0), (1, 3), (1, 4), (2, 0), (3, 0), (3, 1), (3, 2), (4, 0), (4, 1), (4, 2)]
def nRows : List (Fin 5 × Fin 5) := [(0, 0), (1, 1), (1, 2), (2, 1), (2, 2), (2, 3), (2, 4), (3, 3), (3, 4), (4, 3), (4, 4)]
def samp (k : Row) := if k.val < 154 then nRows.getD (k.val % 11) (0,0) else pRows.getD ((k.val-154)/11) (0,0)
def target (p : Fin 5 × Fin 5) := (7571262 : Nat).testBit (5*p.1.val+p.2.val)
def physical (p : Fin 5 × Fin 5) := PEqualNP.Represents.oneEach p.1 p.2
def Matches (C : Circuit) := PEqualNP.Represents.Represents (fun u v : Fin 5 => (7571262 : ℕ).testBit (5 * u.val + v.val)) C
theorem rowInputs : ∀ k : Row, original.map (bit k) = physical (samp k) := by decide +kernel
theorem rowGoal : ∀ k : Row, bit k goal = target (samp k) := by decide +kernel
theorem realizes (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C) (hr : Matches C) :
    ∃ k S, k ≤ C.gates.countP (fun g => !isNot g) ∧ Live true goal k S ∧ ∀ a ∈ S, a ∈ initial := by
  have he : (execute C.gates original).getD C.output zero = goal := by
    apply bit_ext
    intro r
    rw [←b_read,execute_bits _ _ _ (fun g hg => (legal g hg).1)]
    change (C.wires (original.map (bit r))).getD C.output false = _
    rw [rowInputs r]
    exact (hr (samp r).1 (samp r).2).trans (rowGoal r).symm
  have hp : proper goal := by unfold proper; decide +kernel
  have out := get_rep (u:=true) (execute C.gates original) C.output
  rw [he] at out
  unfold Repr at out
  rw [nrm_id (show bit 0 goal=false by decide +kernel)] at out
  exact extract C.gates original legal (u:=true) (by simp) hp (out.resolve_right (fun h => h hp))

def column (x : Sig) : BitVec 154 := ((x >>> 154) ^^^ x).setWidth 154
def cuts (ws : List Sig) : BitVec 154 := ws.foldr (fun w v => column w ||| v) 0
def differs (i : Fin 154) (w : Sig) := w.getLsbD (154+i.val) ≠ w.getLsbD i.val
theorem cuts_spec (ws : List Sig) (i : Fin 154) :
    (cuts ws).getLsbD i.val = true ↔ ∃ w ∈ ws, differs i w := by
  induction ws with
  | nil => simp [cuts]
  | cons a rest ih =>
    change (column a ||| cuts rest).getLsbD i.val = true ↔ _
    rw [BitVec.getLsbD_or, Bool.or_eq_true, ih]
    have hi : i.val < 308 := by omega
    have eq : (column a).getLsbD i.val = true ↔ differs i a := by
      cases e : a.getLsbD (i.val+154) <;> cases f : a.getLsbD i.val <;>
        simp [column, differs, hi, i.isLt, Nat.add_comm, e, f] at *
    rw [eq]
    simp
theorem goal_differs : ∀ i : Fin 154, differs i goal := by unfold differs; decide +kernel
theorem cuts_full {k ws} (h : Live true goal k (List.toFinset ws)) : cuts ws = -1 := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  let q : Fin 154 := ⟨i,hi⟩
  have hx : bit (⟨154+i,by omega⟩ : Row) goal ≠ bit (⟨i,by omega⟩ : Row) goal := goal_differs q
  obtain ⟨a,ha,hd⟩ := live_row_difference h hx
  have hh := (cuts_spec ws q).mpr ⟨a,List.mem_toFinset.mp ha,hd⟩
  change (cuts ws)[i] = (BitVec.allOnes 154)[i]
  rw [BitVec.getElem_allOnes]
  change (cuts ws).getLsbD i = true at hh
  simpa only [BitVec.getLsbD_eq_getElem hi] using hh

def branches (k : Nat) (ws : List Sig) (go : List Sig → Bool) :=
  ws.all fun a => ws.all fun b => (List.range 4).all fun d => [false,true].all fun ka =>
    [false,true].all fun kb =>
    let z := bin d a b
    let next := childTwo ws a b d ka kb
    decide (a=b ∨ z∈ws ∨ z=zero ∨ z=one ∨ k<next.length) || go next.eraseDups

def canon (ws : List Sig) := ws.insertionSort (fun a b => a.toNat ≤ b.toNat)
def word0 : Sig := BitVec.ofNat 308 (865113547179343896+2^60*(27034798349354496+2^60*201424944))
def word1 : Sig := BitVec.ofNat 308 (866803222076178552+2^60*(135173991746772483+2^60*1007124720))
def word2 : Sig := BitVec.ofNat 308 (11827724277842592+2^60*(756974353781925909+2^60*(5639898432+2^60*1098974756864)))
def word3 : Sig := BitVec.ofNat 308 (11264499312231040+2^60*(720927955982786580+2^60*(1080863915940250880+2^60*1098974756991)))
def word4 : Sig := BitVec.ofNat 308 (11827724277842592+2^60*(756974353781925909+2^60*(1080863916208817472+2^60*1098974756991)))
def word5 : Sig := BitVec.ofNat 308 (878067721388409592+2^60*(856101947729559063+2^60*(1080863916947375600+2^60*1098974756991)))
def word6 : Sig := BitVec.ofNat 308 (23655448555685184+2^60*(361027202957004842+2^60*(11279796865+2^60*2250700302057472)))
def word7 : Sig := BitVec.ofNat 308 (22528998624462080+2^60*(288934407358726184+2^60*(10742663681+2^60*2250700302319488)))
def word8 : Sig := BitVec.ofNat 308 (23655448555685184+2^60*(361027202957004842+2^60*(11279796865+2^60*2250700302319488)))
def word9 : Sig := BitVec.ofNat 308 (889332220700640632+2^60*(424108399105498667+2^60*(11749788401+2^60*2250700302319488)))
def word10 : Sig := BitVec.ofNat 308 (216278386794835974+2^60*(6758699587338624+2^60*(50356236+2^60*2251799276814336)))
def word11 : Sig := BitVec.ofNat 308 (35483172833527776+2^60*(1118001556738930751+2^60*(16919695297+2^60*2251799276814336)))
def word12 : Sig := BitVec.ofNat 308 (35483172833527776+2^60*(1118001556738930751+2^60*(1080863927488614337+2^60*2251799276814463)))
def word13 : Sig := BitVec.ofNat 308 (35483172833527776+2^60*(1118001556738930751+2^60*(16919695297+2^60*2251799277076352)))
def word14 : Sig := BitVec.ofNat 308 (33793497936693120+2^60*(1009862363341512764+2^60*(1080863926682914561+2^60*2251799277076479)))
def word15 : Sig := BitVec.ofNat 308 (34356722902304672+2^60*(1045908761140652093+2^60*(1080863926951481153+2^60*2251799277076479)))
def word16 : Sig := BitVec.ofNat 308 (34919947867916224+2^60*(1081955158939791422+2^60*(1080863927220047745+2^60*2251799277076479)))
def word17 : Sig := BitVec.ofNat 308 (35483172833527776+2^60*(1118001556738930751+2^60*(1080863927488614337+2^60*2251799277076479)))
def word18 : Sig := BitVec.ofNat 308 (900596720012871672+2^60*(1145036355088285247+2^60*(1080863927690039281+2^60*2251799277076479)))
def word19 : Sig := BitVec.ofNat 308 (1083081608871014526+2^60*(141932691334111107+2^60*(1152921488484458748+2^60*2251799277076479)))
def word20 : Sig := BitVec.ofNat 308 (216278386794835974+2^60*(6758699587338624+2^60*(50356236+2^60*2251799813423104)))
def word21 : Sig := BitVec.ofNat 308 (1081391933974179870+2^60*(33793497936693120+2^60*(251781180+2^60*2251799813423104)))
def word22 : Sig := BitVec.ofNat 308 (865113547179343896+2^60*(27034798349354496+2^60*(201424944+2^60*(1150669704793161728+2^60*3))))
def word23 : Sig := BitVec.ofNat 308 (865676772144955448+2^60*(63081196148493825+2^60*(469991536+2^60*(1150669704793161728+2^60*3))))
def word24 : Sig := BitVec.ofNat 308 (866239997110567000+2^60*(99127593947633154+2^60*(738558128+2^60*(1150669704793161728+2^60*3))))
def word25 : Sig := BitVec.ofNat 308 (866803222076178552+2^60*(135173991746772483+2^60*(1007124720+2^60*(1150669704793161728+2^60*3))))
def word26 : Sig := BitVec.ofNat 308 (878067721388409592+2^60*(856101947729559063+2^60*(6378456560+2^60*(1150670803767918592+2^60*3))))
def word27 : Sig := BitVec.ofNat 308 (876941271457186488+2^60*(784009152131280405+2^60*(1080863916410242416+2^60*(1150670803767918719+2^60*3))))
def word28 : Sig := BitVec.ofNat 308 (878067721388409592+2^60*(856101947729559063+2^60*(1080863916947375600+2^60*(1150670803767918719+2^60*3))))
def word29 : Sig := BitVec.ofNat 308 (889332220700640632+2^60*(424108399105498667+2^60*(11749788401+2^60*(1152920405095219200+2^60*3))))
def word30 : Sig := BitVec.ofNat 308 (888768995735029080+2^60*(388062001306359338+2^60*(11481221809+2^60*(1152920405095481216+2^60*3))))
def word31 : Sig := BitVec.ofNat 308 (889332220700640632+2^60*(424108399105498667+2^60*(11749788401+2^60*(1152920405095481216+2^60*3))))
def word32 : Sig := BitVec.ofNat 308 (900596720012871672+2^60*(1145036355088285247+2^60*(17121120241+2^60*(1152921504069976064+2^60*3))))
def word33 : Sig := BitVec.ofNat 308 (900596720012871672+2^60*(1145036355088285247+2^60*(1080863927690039281+2^60*(1152921504069976191+2^60*3))))
def word34 : Sig := BitVec.ofNat 308 (900596720012871672+2^60*(1145036355088285247+2^60*(17121120241+2^60*(1152921504070238080+2^60*3))))
def word35 : Sig := BitVec.ofNat 308 (900596720012871672+2^60*(1145036355088285247+2^60*(1080863927690039281+2^60*(1152921504070238207+2^60*3))))
def word36 : Sig := BitVec.ofNat 308 (1081391933974179870+2^60*(33793497936693120+2^60*(251781180+2^60*(1152921504606584832+2^60*3))))
def word37 : Sig := BitVec.ofNat 308 (1083081608871014526+2^60*(141932691334111107+2^60*(1057480956+2^60*(1152921504606584832+2^60*3))))
def word38 : Sig := BitVec.ofNat 308 (1089840308458353150+2^60*(574489464923783055+2^60*(1152921491707257852+2^60*(2251799277076479+2^60*34359730176))))
def word39 : Sig := BitVec.ofNat 308 (6758699587338624+2^60*(432556773589671948+2^60*(3222799104+2^60*(0+2^60*34359738364))))
def word40 : Sig := BitVec.ofNat 308 (33793497936693120+2^60*(1009862363341512764+2^60*(16113995521+2^60*(2251799813423104+2^60*70334384447484))))
def word41 : Sig := BitVec.ofNat 308 (35483172833527776+2^60*(1118001556738930751+2^60*(16919695297+2^60*(1152921504606584832+2^60*70334384447487))))
def word42 : Sig := BitVec.ofNat 308 (323854355226642408+2^60*(1127013156188715583+2^60*(16986836945+2^60*(1152921504606584832+2^60*70334384447487))))
def word43 : Sig := BitVec.ofNat 308 (612225537619757040+2^60*(1136024755638500415+2^60*(17053978593+2^60*(1152921504606584832+2^60*70334384447487))))
def word44 : Sig := BitVec.ofNat 308 (900596720012871672+2^60*(1145036355088285247+2^60*(17121120241+2^60*(1152921504606584832+2^60*70334384447487))))
def word45 : Sig := BitVec.ofNat 308 (360463977991393290+2^60*(11264499312231040+2^60*(83927060+2^60*(0+2^60*144044819348447232))))
def word46 : Sig := BitVec.ofNat 308 (72092795598278658+2^60*(2252899862446208+2^60*(35167209005060+2^60*(0+2^60*144044819348447232))))
def word47 : Sig := BitVec.ofNat 308 (360463977991393290+2^60*(11264499312231040+2^60*(35167276146708+2^60*(0+2^60*144044819348447232))))
def word48 : Sig := BitVec.ofNat 308 (395947150824921066+2^60*(1129266056051161791+2^60*(1080899094764761045+2^60*(2251799277076479+2^60*144044819348447232))))
def word49 : Sig := BitVec.ofNat 308 (938896017674457210+2^60*(137426891609218691+2^60*(35168216129780+2^60*(1150669704793161728+2^60*144044819348447235))))
def word50 : Sig := BitVec.ofNat 308 (105886293534971778+2^60*(1012115263203958972+2^60*(16130780933+2^60*(2251799813423104+2^60*144115153732894716))))
def word51 : Sig := BitVec.ofNat 308 (395947150824921066+2^60*(1129266056051161791+2^60*(17003622357+2^60*(1152921504606584832+2^60*144115153732894719))))
def word52 : Sig := BitVec.ofNat 308 (972689515611150330+2^60*(1147289254950731455+2^60*(17137905653+2^60*(1152921504606584832+2^60*144115153732894719))))
def word53 : Sig := BitVec.ofNat 308 (395947150824921066+2^60*(1129266056051161791+2^60*(35184195842005+2^60*(1152921504606584832+2^60*144115153732894719))))
def word54 : Sig := BitVec.ofNat 308 (720927955982786580+2^60*(22528998624462080+2^60*(167854120+2^60*(0+2^60*(1008806350873952256+2^60*255)))))
def word55 : Sig := BitVec.ofNat 308 (144185591196557316+2^60*(4505799724892416+2^60*(72022409699409928+2^60*(0+2^60*(1008806350873952256+2^60*255)))))
def word56 : Sig := BitVec.ofNat 308 (720927955982786580+2^60*(22528998624462080+2^60*(72022409833693224+2^60*(0+2^60*(1008806350873952256+2^60*255)))))
def word57 : Sig := BitVec.ofNat 308 (756411128816314356+2^60*(1140530555363392831+2^60*(1152886337322307561+2^60*(2251799277076479+2^60*(1008806350873952256+2^60*255)))))
def word58 : Sig := BitVec.ofNat 308 (1010988813272735868+2^60*(139679791471664899+2^60*(72022410706534648+2^60*(1150669704793161728+2^60*(1008806350873952259+2^60*255)))))
def word59 : Sig := BitVec.ofNat 308 (177979089133250436+2^60*(1014368163066405180+2^60*(16147566345+2^60*(2251799813423104+2^60*(1008876685258399740+2^60*255)))))
def word60 : Sig := BitVec.ofNat 308 (756411128816314356+2^60*(1140530555363392831+2^60*(17087549417+2^60*(1152921504606584832+2^60*(1008876685258399743+2^60*255)))))
def word61 : Sig := BitVec.ofNat 308 (1044782311209428988+2^60*(1149542154813177663+2^60*(17154691065+2^60*(1152921504606584832+2^60*(1008876685258399743+2^60*255)))))
def word62 : Sig := BitVec.ofNat 308 (756411128816314356+2^60*(1140530555363392831+2^60*(72022426753388521+2^60*(1152921504606584832+2^60*(1008876685258399743+2^60*255)))))
def word63 : Sig := BitVec.ofNat 308 (1110116407220369022+2^60*(719238281085951923+2^60*(1152921501375655165+2^60*(2251799277076479+2^60*(1152851135862669312+2^60*255)))))
def word64 : Sig := BitVec.ofNat 308 (216278386794835974+2^60*(6758699587338624+2^60*(50356236+2^60*(0+2^60*(1152851170222399488+2^60*255)))))
def word65 : Sig := BitVec.ofNat 308 (1081391933974179870+2^60*(33793497936693120+2^60*(251781180+2^60*(0+2^60*(1152851170222399488+2^60*255)))))
def word66 : Sig := BitVec.ofNat 308 (216278386794835974+2^60*(6758699587338624+2^60*(35167242575884+2^60*(0+2^60*(1152851170222399488+2^60*255)))))
def word67 : Sig := BitVec.ofNat 308 (1081391933974179870+2^60*(33793497936693120+2^60*(35167444000828+2^60*(0+2^60*(1152851170222399488+2^60*255)))))
def word68 : Sig := BitVec.ofNat 308 (216278386794835974+2^60*(6758699587338624+2^60*(72022409716195340+2^60*(0+2^60*(1152851170222399488+2^60*255)))))
def word69 : Sig := BitVec.ofNat 308 (1081391933974179870+2^60*(33793497936693120+2^60*(72022409917620284+2^60*(0+2^60*(1152851170222399488+2^60*255)))))
def word70 : Sig := BitVec.ofNat 308 (216278386794835974+2^60*(6758699587338624+2^60*(72057576908414988+2^60*(0+2^60*(1152851170222399488+2^60*255)))))
def word71 : Sig := BitVec.ofNat 308 (504649569187950606+2^60*(15770299037123456+2^60*(72057576975556636+2^60*(0+2^60*(1152851170222399488+2^60*255)))))
def word72 : Sig := BitVec.ofNat 308 (793020751581065238+2^60*(24781898486908288+2^60*(72057577042698284+2^60*(0+2^60*(1152851170222399488+2^60*255)))))
def word73 : Sig := BitVec.ofNat 308 (1081391933974179870+2^60*(33793497936693120+2^60*(72057577109839932+2^60*(0+2^60*(1152851170222399488+2^60*255)))))
def word74 : Sig := BitVec.ofNat 308 (33793497936693120+2^60*(1009862363341512764+2^60*(1152921503540973313+2^60*(262143+2^60*(1152851170222399488+2^60*255)))))
def word75 : Sig := BitVec.ofNat 308 (35483172833527776+2^60*(1118001556738930751+2^60*(1152921504346673089+2^60*(262143+2^60*(1152851170222399488+2^60*255)))))
def word76 : Sig := BitVec.ofNat 308 (900596720012871672+2^60*(1145036355088285247+2^60*(1152921504548098033+2^60*(262143+2^60*(1152851170222399488+2^60*255)))))
def word77 : Sig := BitVec.ofNat 308 (227542886107067014+2^60*(727686655570125204+2^60*(1152921492848665868+2^60*(1098974756991+2^60*(1152851170222399488+2^60*255)))))
def word78 : Sig := BitVec.ofNat 308 (1093219658252022462+2^60*(790767851718619029+2^60*(1152921493318657404+2^60*(1098974756991+2^60*(1152851170222399488+2^60*255)))))
def word79 : Sig := BitVec.ofNat 308 (238807385419298054+2^60*(295693106946064808+2^60*(72057587651078669+2^60*(2250700302319488+2^60*(1152851170222399488+2^60*255)))))
def word80 : Sig := BitVec.ofNat 308 (1105047382529865054+2^60*(394820700893697962+2^60*(72057588389636797+2^60*(2250700302319488+2^60*(1152851170222399488+2^60*255)))))
def word81 : Sig := BitVec.ofNat 308 (250071884731529094+2^60*(1016621062928851388+2^60*(1152921503591329549+2^60*(2251799277076479+2^60*(1152851170222399488+2^60*255)))))
def word82 : Sig := BitVec.ofNat 308 (251761559628363750+2^60*(1124760256326269375+2^60*(1152921504397029325+2^60*(2251799277076479+2^60*(1152851170222399488+2^60*255)))))
def word83 : Sig := BitVec.ofNat 308 (1116875106807707646+2^60*(1151795054675623871+2^60*(1152921504598454269+2^60*(2251799277076479+2^60*(1152851170222399488+2^60*255)))))
def word84 : Sig := BitVec.ofNat 308 (1116875106807707646+2^60*(1151795054675623871+2^60*(1152921504598454269+2^60*(2251799813685247+2^60*(1152851170222399488+2^60*255)))))
def word85 : Sig := BitVec.ofNat 308 (1083081608871014526+2^60*(141932691334111107+2^60*(72057577915539708+2^60*(1150669704793161728+2^60*(1152851170222399491+2^60*255)))))
def word86 : Sig := BitVec.ofNat 308 (1116875106807707646+2^60*(1151795054675623871+2^60*(1152921504598454269+2^60*(2251799277076479+2^60*(1152851170222407676+2^60*255)))))
def word87 : Sig := BitVec.ofNat 308 (27034798349354496+2^60*(577305589751840816+2^60*(12891196417+2^60*(0+2^60*(1152921470247108608+2^60*255)))))
def word88 : Sig := BitVec.ofNat 308 (1116875106807707646+2^60*(1151795054675623871+2^60*(1152921504598454269+2^60*(2251799277076479+2^60*(1152921504606838784+2^60*255)))))
def word89 : Sig := BitVec.ofNat 308 (33793497936693120+2^60*(1009862363341512764+2^60*(16113995521+2^60*(0+2^60*(1152921504606846972+2^60*255)))))
def word90 : Sig := BitVec.ofNat 308 (216278386794835974+2^60*(6758699587338624+2^60*(50356236+2^60*(536608768+2^60*(1152921504606846972+2^60*255)))))
def word91 : Sig := BitVec.ofNat 308 (227542886107067014+2^60*(727686655570125204+2^60*(5421688076+2^60*(1099511365632+2^60*(1152921504606846972+2^60*255)))))
def word92 : Sig := BitVec.ofNat 308 (238807385419298054+2^60*(295693106946064808+2^60*(10793019917+2^60*(2250700838666240+2^60*(1152921504606846972+2^60*255)))))
def word93 : Sig := BitVec.ofNat 308 (250071884731529094+2^60*(1016621062928851388+2^60*(16164351757+2^60*(2251799813423104+2^60*(1152921504606846972+2^60*255)))))
def word94 : Sig := BitVec.ofNat 308 (900596720012871672+2^60*(1145036355088285247+2^60*(17121120241+2^60*(1150669704793161728+2^60*(1152921504606846975+2^60*255)))))
def word95 : Sig := BitVec.ofNat 308 (1081391933974179870+2^60*(33793497936693120+2^60*(251781180+2^60*(1150669705329770496+2^60*(1152921504606846975+2^60*255)))))
def word96 : Sig := BitVec.ofNat 308 (1083081608871014526+2^60*(141932691334111107+2^60*(1057480956+2^60*(1150669705329770496+2^60*(1152921504606846975+2^60*255)))))
def word97 : Sig := BitVec.ofNat 308 (1093219658252022462+2^60*(790767851718619029+2^60*(5891679612+2^60*(1150670804304527360+2^60*(1152921504606846975+2^60*255)))))
def word98 : Sig := BitVec.ofNat 308 (1105047382529865054+2^60*(394820700893697962+2^60*(11531578045+2^60*(1152920405631827968+2^60*(1152921504606846975+2^60*255)))))
def word99 : Sig := BitVec.ofNat 308 (1116875106807707646+2^60*(1151795054675623871+2^60*(17171476477+2^60*(1152921504606584832+2^60*(1152921504606846975+2^60*255)))))
def word100 : Sig := BitVec.ofNat 308 (1116875106807707646+2^60*(1151795054675623871+2^60*(35184363696125+2^60*(1152921504606584832+2^60*(1152921504606846975+2^60*255)))))
def word101 : Sig := BitVec.ofNat 308 (1116875106807707646+2^60*(1151795054675623871+2^60*(72022426837315581+2^60*(1152921504606584832+2^60*(1152921504606846975+2^60*255)))))
def word102 : Sig := BitVec.ofNat 308 (1116875106807707646+2^60*(1151795054675623871+2^60*(72057594029535229+2^60*(1152921504606584832+2^60*(1152921504606846975+2^60*255)))))
def bucketId (ws : List Sig) : Fin 97 := ⟨(ws.foldl (fun v w => v+w.toNat) 0) % 97, Nat.mod_lt _ (by decide)⟩
def bucket1g0 : List (List Sig) := []
def bucket1g1 : List (List Sig) := [[word41,word75]]
def bucket1g2 : List (List Sig) := []
def bucket1g3 : List (List Sig) := []
def bucket1g4 : List (List Sig) := []
def bucket1g5 : List (List Sig) := []
def bucket1g6 : List (List Sig) := []
def bucket1g7 : List (List Sig) := []
def bucket1g8 : List (List Sig) := []
def bucket1g9 : List (List Sig) := []
def bucket1g10 : List (List Sig) := []
def bucket1g11 : List (List Sig) := []
def bucket1g12 : List (List Sig) := []
def bucket1g13 : List (List Sig) := []
def bucket1g14 : List (List Sig) := []
def bucket1g15 : List (List Sig) := []
def bucket1g16 : List (List Sig) := []
def bucket1g17 : List (List Sig) := []
def bucket1g18 : List (List Sig) := []
def bucket1g19 : List (List Sig) := []
def bucket1g20 : List (List Sig) := []
def bucket1g21 : List (List Sig) := []
def bucket1g22 : List (List Sig) := []
def bucket1g23 : List (List Sig) := []
def bucket1g24 : List (List Sig) := []
def bucket1g25 : List (List Sig) := []
def bucket1g26 : List (List Sig) := []
def bucket1g27 : List (List Sig) := []
def bucket1g28 : List (List Sig) := []
def bucket1g29 : List (List Sig) := []
def bucket1g30 : List (List Sig) := []
def bucket1g31 : List (List Sig) := []
def bucket1g32 : List (List Sig) := []
def bucket1g33 : List (List Sig) := []
def bucket1g34 : List (List Sig) := []
def bucket1g35 : List (List Sig) := []
def bucket1g36 : List (List Sig) := []
def bucket1g37 : List (List Sig) := []
def bucket1g38 : List (List Sig) := []
def bucket1g39 : List (List Sig) := []
def bucket1g40 : List (List Sig) := []
def bucket1g41 : List (List Sig) := []
def bucket1g42 : List (List Sig) := [[word44,word76]]
def bucket1g43 : List (List Sig) := []
def bucket1g44 : List (List Sig) := []
def bucket1g45 : List (List Sig) := []
def bucket1g46 : List (List Sig) := [[word19,word96]]
def bucket1g47 : List (List Sig) := []
def bucket1g48 : List (List Sig) := []
def bucket1g49 : List (List Sig) := []
def bucket1g50 : List (List Sig) := []
def bucket1g51 : List (List Sig) := []
def bucket1g52 : List (List Sig) := []
def bucket1g53 : List (List Sig) := []
def bucket1g54 : List (List Sig) := []
def bucket1g55 : List (List Sig) := []
def bucket1g56 : List (List Sig) := []
def bucket1g57 : List (List Sig) := []
def bucket1g58 : List (List Sig) := []
def bucket1g59 : List (List Sig) := []
def bucket1g60 : List (List Sig) := []
def bucket1g61 : List (List Sig) := []
def bucket1g62 : List (List Sig) := []
def bucket1g63 : List (List Sig) := []
def bucket1g64 : List (List Sig) := []
def bucket1g65 : List (List Sig) := []
def bucket1g66 : List (List Sig) := []
def bucket1g67 : List (List Sig) := []
def bucket1g68 : List (List Sig) := []
def bucket1g69 : List (List Sig) := []
def bucket1g70 : List (List Sig) := []
def bucket1g71 : List (List Sig) := []
def bucket1g72 : List (List Sig) := []
def bucket1g73 : List (List Sig) := []
def bucket1g74 : List (List Sig) := []
def bucket1g75 : List (List Sig) := []
def bucket1g76 : List (List Sig) := []
def bucket1g77 : List (List Sig) := []
def bucket1g78 : List (List Sig) := []
def bucket1g79 : List (List Sig) := []
def bucket1g80 : List (List Sig) := []
def bucket1g81 : List (List Sig) := []
def bucket1g82 : List (List Sig) := []
def bucket1g83 : List (List Sig) := []
def bucket1g84 : List (List Sig) := []
def bucket1g85 : List (List Sig) := []
def bucket1g86 : List (List Sig) := []
def bucket1g87 : List (List Sig) := []
def bucket1g88 : List (List Sig) := []
def bucket1g89 : List (List Sig) := []
def bucket1g90 : List (List Sig) := []
def bucket1g91 : List (List Sig) := []
def bucket1g92 : List (List Sig) := []
def bucket1g93 : List (List Sig) := []
def bucket1g94 : List (List Sig) := []
def bucket1g95 : List (List Sig) := []
def bucket1g96 : List (List Sig) := []
def table1 : Array (List (List Sig)) := #[bucket1g0,bucket1g1,bucket1g2,bucket1g3,bucket1g4,bucket1g5,bucket1g6,bucket1g7,bucket1g8,bucket1g9,bucket1g10,bucket1g11,bucket1g12,bucket1g13,bucket1g14,bucket1g15,bucket1g16,bucket1g17,bucket1g18,bucket1g19,bucket1g20,bucket1g21,bucket1g22,bucket1g23,bucket1g24,bucket1g25,bucket1g26,bucket1g27,bucket1g28,bucket1g29,bucket1g30,bucket1g31,bucket1g32,bucket1g33,bucket1g34,bucket1g35,bucket1g36,bucket1g37,bucket1g38,bucket1g39,bucket1g40,bucket1g41,bucket1g42,bucket1g43,bucket1g44,bucket1g45,bucket1g46,bucket1g47,bucket1g48,bucket1g49,bucket1g50,bucket1g51,bucket1g52,bucket1g53,bucket1g54,bucket1g55,bucket1g56,bucket1g57,bucket1g58,bucket1g59,bucket1g60,bucket1g61,bucket1g62,bucket1g63,bucket1g64,bucket1g65,bucket1g66,bucket1g67,bucket1g68,bucket1g69,bucket1g70,bucket1g71,bucket1g72,bucket1g73,bucket1g74,bucket1g75,bucket1g76,bucket1g77,bucket1g78,bucket1g79,bucket1g80,bucket1g81,bucket1g82,bucket1g83,bucket1g84,bucket1g85,bucket1g86,bucket1g87,bucket1g88,bucket1g89,bucket1g90,bucket1g91,bucket1g92,bucket1g93,bucket1g94,bucket1g95,bucket1g96]
def bucket2g0 : List (List Sig) := []
def bucket2g1 : List (List Sig) := [[word63,word87,word96], [word68,word76,word99]]
def bucket2g2 : List (List Sig) := []
def bucket2g3 : List (List Sig) := []
def bucket2g4 : List (List Sig) := [[word19,word25,word95]]
def bucket2g5 : List (List Sig) := [[word83,word89,word96], [word83,word90,word94]]
def bucket2g6 : List (List Sig) := []
def bucket2g7 : List (List Sig) := []
def bucket2g8 : List (List Sig) := []
def bucket2g9 : List (List Sig) := []
def bucket2g10 : List (List Sig) := []
def bucket2g11 : List (List Sig) := []
def bucket2g12 : List (List Sig) := []
def bucket2g13 : List (List Sig) := [[word25,word41,word76], [word44,word76,word87]]
def bucket2g14 : List (List Sig) := [[word10,word44,word83], [word70,word76,word100]]
def bucket2g15 : List (List Sig) := []
def bucket2g16 : List (List Sig) := []
def bucket2g17 : List (List Sig) := []
def bucket2g18 : List (List Sig) := [[word24,word41,word76]]
def bucket2g19 : List (List Sig) := []
def bucket2g20 : List (List Sig) := []
def bucket2g21 : List (List Sig) := []
def bucket2g22 : List (List Sig) := [[word44,word76,word99]]
def bucket2g23 : List (List Sig) := [[word23,word41,word76]]
def bucket2g24 : List (List Sig) := []
def bucket2g25 : List (List Sig) := []
def bucket2g26 : List (List Sig) := [[word55,word61,word76]]
def bucket2g27 : List (List Sig) := [[word1,word41,word76]]
def bucket2g28 : List (List Sig) := []
def bucket2g29 : List (List Sig) := []
def bucket2g30 : List (List Sig) := [[word8,word44,word76]]
def bucket2g31 : List (List Sig) := [[word20,word41,word82]]
def bucket2g32 : List (List Sig) := [[word41,word76,word81]]
def bucket2g33 : List (List Sig) := [[word20,word44,word84], [word66,word76,word99]]
def bucket2g34 : List (List Sig) := []
def bucket2g35 : List (List Sig) := []
def bucket2g36 : List (List Sig) := [[word25,word42,word76]]
def bucket2g37 : List (List Sig) := [[word70,word76,word102]]
def bucket2g38 : List (List Sig) := []
def bucket2g39 : List (List Sig) := []
def bucket2g40 : List (List Sig) := []
def bucket2g41 : List (List Sig) := []
def bucket2g42 : List (List Sig) := [[word0,word41,word76], [word25,word40,word76], [word44,word76]]
def bucket2g43 : List (List Sig) := [[word14,word19,word99], [word44,word56,word76]]
def bucket2g44 : List (List Sig) := [[word44,word51,word76]]
def bucket2g45 : List (List Sig) := []
def bucket2g46 : List (List Sig) := [[word41,word74,word76]]
def bucket2g47 : List (List Sig) := []
def bucket2g48 : List (List Sig) := []
def bucket2g49 : List (List Sig) := []
def bucket2g50 : List (List Sig) := [[word38,word39,word96]]
def bucket2g51 : List (List Sig) := []
def bucket2g52 : List (List Sig) := [[word4,word44,word76]]
def bucket2g53 : List (List Sig) := []
def bucket2g54 : List (List Sig) := []
def bucket2g55 : List (List Sig) := []
def bucket2g56 : List (List Sig) := [[word70,word76,word99], [word73,word75,word99]]
def bucket2g57 : List (List Sig) := [[word37,word41,word76]]
def bucket2g58 : List (List Sig) := [[word44,word76,word83]]
def bucket2g59 : List (List Sig) := [[word25,word43,word76], [word44,word47,word76]]
def bucket2g60 : List (List Sig) := [[word44,word60,word76], [word44,word73,word76]]
def bucket2g61 : List (List Sig) := []
def bucket2g62 : List (List Sig) := []
def bucket2g63 : List (List Sig) := []
def bucket2g64 : List (List Sig) := [[word39,word44,word76]]
def bucket2g65 : List (List Sig) := []
def bucket2g66 : List (List Sig) := []
def bucket2g67 : List (List Sig) := []
def bucket2g68 : List (List Sig) := []
def bucket2g69 : List (List Sig) := []
def bucket2g70 : List (List Sig) := []
def bucket2g71 : List (List Sig) := []
def bucket2g72 : List (List Sig) := [[word20,word44,word83], [word21,word41,word83], [word37,word40,word83], [word46,word52,word76]]
def bucket2g73 : List (List Sig) := []
def bucket2g74 : List (List Sig) := []
def bucket2g75 : List (List Sig) := [[word64,word76,word99]]
def bucket2g76 : List (List Sig) := []
def bucket2g77 : List (List Sig) := []
def bucket2g78 : List (List Sig) := []
def bucket2g79 : List (List Sig) := [[word70,word76,word101]]
def bucket2g80 : List (List Sig) := []
def bucket2g81 : List (List Sig) := []
def bucket2g82 : List (List Sig) := [[word25,word44,word76], [word41,word44,word76]]
def bucket2g83 : List (List Sig) := []
def bucket2g84 : List (List Sig) := []
def bucket2g85 : List (List Sig) := []
def bucket2g86 : List (List Sig) := [[word20,word44,word76]]
def bucket2g87 : List (List Sig) := []
def bucket2g88 : List (List Sig) := [[word44,word70,word76]]
def bucket2g89 : List (List Sig) := []
def bucket2g90 : List (List Sig) := []
def bucket2g91 : List (List Sig) := []
def bucket2g92 : List (List Sig) := []
def bucket2g93 : List (List Sig) := []
def bucket2g94 : List (List Sig) := []
def bucket2g95 : List (List Sig) := []
def bucket2g96 : List (List Sig) := []
def table2 : Array (List (List Sig)) := #[bucket2g0,bucket2g1,bucket2g2,bucket2g3,bucket2g4,bucket2g5,bucket2g6,bucket2g7,bucket2g8,bucket2g9,bucket2g10,bucket2g11,bucket2g12,bucket2g13,bucket2g14,bucket2g15,bucket2g16,bucket2g17,bucket2g18,bucket2g19,bucket2g20,bucket2g21,bucket2g22,bucket2g23,bucket2g24,bucket2g25,bucket2g26,bucket2g27,bucket2g28,bucket2g29,bucket2g30,bucket2g31,bucket2g32,bucket2g33,bucket2g34,bucket2g35,bucket2g36,bucket2g37,bucket2g38,bucket2g39,bucket2g40,bucket2g41,bucket2g42,bucket2g43,bucket2g44,bucket2g45,bucket2g46,bucket2g47,bucket2g48,bucket2g49,bucket2g50,bucket2g51,bucket2g52,bucket2g53,bucket2g54,bucket2g55,bucket2g56,bucket2g57,bucket2g58,bucket2g59,bucket2g60,bucket2g61,bucket2g62,bucket2g63,bucket2g64,bucket2g65,bucket2g66,bucket2g67,bucket2g68,bucket2g69,bucket2g70,bucket2g71,bucket2g72,bucket2g73,bucket2g74,bucket2g75,bucket2g76,bucket2g77,bucket2g78,bucket2g79,bucket2g80,bucket2g81,bucket2g82,bucket2g83,bucket2g84,bucket2g85,bucket2g86,bucket2g87,bucket2g88,bucket2g89,bucket2g90,bucket2g91,bucket2g92,bucket2g93,bucket2g94,bucket2g95,bucket2g96]
def bucket3g0 : List (List Sig) := [[word0,word73,word76,word99]]
def bucket3g1 : List (List Sig) := [[word8,word25,word41,word76]]
def bucket3g2 : List (List Sig) := [[word14,word83,word89,word99], [word23,word47,word51,word76], [word23,word56,word60,word76]]
def bucket3g3 : List (List Sig) := [[word20,word70,word76,word99], [word25,word83,word94,word95]]
def bucket3g4 : List (List Sig) := [[word20,word25,word41,word84], [word73,word74,word76,word99]]
def bucket3g5 : List (List Sig) := [[word20,word46,word52,word83], [word37,word56,word59,word83], [word39,word83,word87,word96]]
def bucket3g6 : List (List Sig) := [[word1,word47,word51,word76], [word1,word56,word60,word76]]
def bucket3g7 : List (List Sig) := [[word73,word83,word93,word94]]
def bucket3g8 : List (List Sig) := [[word20,word64,word83,word99], [word25,word38,word39,word95]]
def bucket3g9 : List (List Sig) := [[word25,word49,word51,word76], [word25,word60,word73,word76]]
def bucket3g10 : List (List Sig) := [[word8,word19,word25,word98], [word18,word20,word83,word99]]
def bucket3g11 : List (List Sig) := [[word47,word51,word76,word81], [word56,word60,word76,word81]]
def bucket3g12 : List (List Sig) := [[word18,word20,word73,word99], [word20,word70,word83,word101]]
def bucket3g13 : List (List Sig) := [[word25,word41,word76], [word25,word69,word76,word99]]
def bucket3g14 : List (List Sig) := [[word25,word41,word56,word76]]
def bucket3g15 : List (List Sig) := [[word20,word25,word44,word83], [word20,word41,word44,word83], [word25,word41,word51,word76], [word25,word56,word61,word76], [word25,word56,word62,word76], [word37,word73,word76,word99]]
def bucket3g16 : List (List Sig) := [[word37,word58,word60,word83]]
def bucket3g17 : List (List Sig) := []
def bucket3g18 : List (List Sig) := []
def bucket3g19 : List (List Sig) := [[word20,word35,word83,word101], [word31,word83,word94,word98]]
def bucket3g20 : List (List Sig) := []
def bucket3g21 : List (List Sig) := [[word8,word83,word92,word94], [word20,word44,word70,word83], [word73,word76,word89,word99]]
def bucket3g22 : List (List Sig) := [[word25,word71,word76,word99]]
def bucket3g23 : List (List Sig) := [[word4,word25,word41,word76]]
def bucket3g24 : List (List Sig) := []
def bucket3g25 : List (List Sig) := [[word47,word51,word74,word76], [word56,word60,word74,word76]]
def bucket3g26 : List (List Sig) := [[word20,word33,word83,word99], [word25,word73,word76,word100]]
def bucket3g27 : List (List Sig) := [[word70,word76,word87,word99]]
def bucket3g28 : List (List Sig) := [[word10,word70,word83,word99], [word25,word73,word76,word93], [word37,word47,word50,word83]]
def bucket3g29 : List (List Sig) := [[word25,word41,word76,word83]]
def bucket3g30 : List (List Sig) := [[word21,word73,word83,word99], [word25,word41,word47,word76]]
def bucket3g31 : List (List Sig) := [[word20,word68,word83,word99], [word25,word41,word60,word76], [word25,word41,word73,word76]]
def bucket3g32 : List (List Sig) := []
def bucket3g33 : List (List Sig) := []
def bucket3g34 : List (List Sig) := [[word17,word37,word83,word94], [word20,word34,word83,word99], [word25,word45,word51,word76]]
def bucket3g35 : List (List Sig) := [[word10,word35,word83,word99], [word25,word39,word41,word76]]
def bucket3g36 : List (List Sig) := [[word20,word35,word86,word99], [word37,word47,word51,word76], [word37,word56,word60,word76]]
def bucket3g37 : List (List Sig) := []
def bucket3g38 : List (List Sig) := [[word17,word37,word83,word93], [word25,word47,word52,word76]]
def bucket3g39 : List (List Sig) := [[word25,word76,word85,word99], [word37,word49,word51,word83], [word49,word58,word76,word99]]
def bucket3g40 : List (List Sig) := [[word18,word20,word70,word99]]
def bucket3g41 : List (List Sig) := []
def bucket3g42 : List (List Sig) := [[word8,word76,word79,word99], [word20,word70,word83,word94]]
def bucket3g43 : List (List Sig) := [[word20,word25,word41,word83], [word20,word44,word83,word87], [word25,word55,word60,word76]]
def bucket3g44 : List (List Sig) := [[word8,word70,word76,word99], [word20,word70,word83,word100]]
def bucket3g45 : List (List Sig) := [[word25,word67,word76,word99], [word25,word72,word76,word99]]
def bucket3g46 : List (List Sig) := []
def bucket3g47 : List (List Sig) := [[word14,word38,word39,word99], [word20,word70,word84,word99], [word25,word47,word53,word76]]
def bucket3g48 : List (List Sig) := [[word20,word24,word41,word83]]
def bucket3g49 : List (List Sig) := [[word20,word35,word83,word94], [word25,word73,word76,word102]]
def bucket3g50 : List (List Sig) := []
def bucket3g51 : List (List Sig) := [[word20,word35,word83,word100]]
def bucket3g52 : List (List Sig) := [[word20,word44,word83,word99]]
def bucket3g53 : List (List Sig) := [[word20,word23,word41,word83]]
def bucket3g54 : List (List Sig) := [[word31,word76,word80,word99], [word37,word73,word83,word94]]
def bucket3g55 : List (List Sig) := []
def bucket3g56 : List (List Sig) := [[word20,word55,word61,word83], [word25,word63,word87,word95], [word46,word55,word76,word99], [word70,word76,word99]]
def bucket3g57 : List (List Sig) := [[word1,word20,word41,word83], [word20,word25,word41,word76], [word56,word70,word76,word99]]
def bucket3g58 : List (List Sig) := [[word37,word73,word83,word93]]
def bucket3g59 : List (List Sig) := []
def bucket3g60 : List (List Sig) := [[word8,word20,word44,word83], [word25,word83,word89,word95]]
def bucket3g61 : List (List Sig) := []
def bucket3g62 : List (List Sig) := [[word4,word19,word25,word97], [word20,word41,word81,word83]]
def bucket3g63 : List (List Sig) := [[word20,word66,word83,word99]]
def bucket3g64 : List (List Sig) := [[word20,word32,word83,word99]]
def bucket3g65 : List (List Sig) := [[word73,word76,word93,word99]]
def bucket3g66 : List (List Sig) := [[word4,word70,word76,word99], [word20,word25,word42,word83], [word25,word46,word51,word76], [word25,word54,word60,word76], [word28,word83,word94,word97], [word31,word73,word76,word99]]
def bucket3g67 : List (List Sig) := [[word17,word76,word81,word99], [word20,word70,word83,word102]]
def bucket3g68 : List (List Sig) := [[word4,word83,word91,word94], [word17,word19,word25,word99], [word25,word73,word76,word99]]
def bucket3g69 : List (List Sig) := [[word37,word83,word85,word99]]
def bucket3g70 : List (List Sig) := []
def bucket3g71 : List (List Sig) := []
def bucket3g72 : List (List Sig) := [[word0,word20,word41,word83], [word17,word19,word20,word99], [word20,word25,word40,word83], [word20,word44,word83], [word25,word56,word59,word76], [word70,word76,word83,word99]]
def bucket3g73 : List (List Sig) := [[word20,word44,word56,word83], [word24,word73,word76,word99], [word47,word70,word76,word99]]
def bucket3g74 : List (List Sig) := [[word20,word44,word51,word83], [word70,word73,word76,word99]]
def bucket3g75 : List (List Sig) := [[word70,word83,word94,word99], [word83,word85,word89,word99]]
def bucket3g76 : List (List Sig) := []
def bucket3g77 : List (List Sig) := []
def bucket3g78 : List (List Sig) := [[word23,word73,word76,word99], [word39,word70,word76,word99]]
def bucket3g79 : List (List Sig) := [[word35,word76,word83,word99]]
def bucket3g80 : List (List Sig) := [[word20,word35,word88,word99]]
def bucket3g81 : List (List Sig) := [[word4,word76,word77,word99], [word25,word41,word76,word87]]
def bucket3g82 : List (List Sig) := [[word1,word73,word76,word99], [word4,word20,word44,word83], [word10,word25,word41,word83], [word35,word83,word94,word99]]
def bucket3g83 : List (List Sig) := [[word25,word37,word41,word83], [word25,word58,word60,word76], [word28,word73,word76,word99]]
def bucket3g84 : List (List Sig) := [[word17,word83,word93,word94]]
def bucket3g85 : List (List Sig) := []
def bucket3g86 : List (List Sig) := [[word20,word70,word83,word99], [word20,word73,word82,word99]]
def bucket3g87 : List (List Sig) := [[word20,word37,word41,word83], [word25,word65,word76,word99], [word73,word76,word81,word99]]
def bucket3g88 : List (List Sig) := []
def bucket3g89 : List (List Sig) := [[word20,word25,word43,word83], [word20,word44,word47,word83], [word25,word47,word51,word76], [word25,word56,word60,word76]]
def bucket3g90 : List (List Sig) := [[word20,word44,word60,word83], [word20,word44,word73,word83], [word25,word41,word76,word99], [word25,word51,word60,word76], [word25,word51,word73,word76]]
def bucket3g91 : List (List Sig) := [[word25,word73,word76,word101]]
def bucket3g92 : List (List Sig) := []
def bucket3g93 : List (List Sig) := [[word14,word37,word83,word99], [word17,word36,word83,word99], [word20,word35,word83,word99], [word20,word83,word90,word99], [word28,word76,word78,word99]]
def bucket3g94 : List (List Sig) := [[word20,word39,word44,word83], [word24,word47,word51,word76], [word24,word56,word60,word76]]
def bucket3g95 : List (List Sig) := [[word14,word63,word87,word99], [word25,word47,word50,word76]]
def bucket3g96 : List (List Sig) := [[word25,word70,word76,word99]]
def table3 : Array (List (List Sig)) := #[bucket3g0,bucket3g1,bucket3g2,bucket3g3,bucket3g4,bucket3g5,bucket3g6,bucket3g7,bucket3g8,bucket3g9,bucket3g10,bucket3g11,bucket3g12,bucket3g13,bucket3g14,bucket3g15,bucket3g16,bucket3g17,bucket3g18,bucket3g19,bucket3g20,bucket3g21,bucket3g22,bucket3g23,bucket3g24,bucket3g25,bucket3g26,bucket3g27,bucket3g28,bucket3g29,bucket3g30,bucket3g31,bucket3g32,bucket3g33,bucket3g34,bucket3g35,bucket3g36,bucket3g37,bucket3g38,bucket3g39,bucket3g40,bucket3g41,bucket3g42,bucket3g43,bucket3g44,bucket3g45,bucket3g46,bucket3g47,bucket3g48,bucket3g49,bucket3g50,bucket3g51,bucket3g52,bucket3g53,bucket3g54,bucket3g55,bucket3g56,bucket3g57,bucket3g58,bucket3g59,bucket3g60,bucket3g61,bucket3g62,bucket3g63,bucket3g64,bucket3g65,bucket3g66,bucket3g67,bucket3g68,bucket3g69,bucket3g70,bucket3g71,bucket3g72,bucket3g73,bucket3g74,bucket3g75,bucket3g76,bucket3g77,bucket3g78,bucket3g79,bucket3g80,bucket3g81,bucket3g82,bucket3g83,bucket3g84,bucket3g85,bucket3g86,bucket3g87,bucket3g88,bucket3g89,bucket3g90,bucket3g91,bucket3g92,bucket3g93,bucket3g94,bucket3g95,bucket3g96]
def bucket4g0 : List (List Sig) := [[word5,word8,word20,word83,word99], [word17,word20,word81,word83,word99], [word20,word25,word48,word73,word99]]
def bucket4g1 : List (List Sig) := [[word20,word25,word73,word83,word99], [word20,word25,word78,word80,word99], [word47,word58,word83,word89,word99]]
def bucket4g2 : List (List Sig) := [[word4,word25,word47,word51,word76], [word4,word25,word56,word60,word76], [word14,word39,word83,word87,word99]]
def bucket4g3 : List (List Sig) := [[word17,word20,word25,word51,word83]]
def bucket4g4 : List (List Sig) := [[word17,word20,word25,word83,word101], [word20,word25,word51,word57,word83], [word47,word56,word74,word76,word99]]
def bucket4g5 : List (List Sig) := [[word4,word9,word20,word83,word99], [word20,word25,word47,word51,word57], [word20,word25,word56,word59,word83]]
def bucket4g6 : List (List Sig) := [[word4,word20,word35,word83,word99], [word20,word24,word73,word83,word99], [word20,word47,word70,word83,word99]]
def bucket4g7 : List (List Sig) := [[word20,word70,word73,word83,word99], [word47,word56,word83,word93,word94]]
def bucket4g8 : List (List Sig) := [[word25,word47,word51,word76,word83], [word25,word56,word60,word76,word83]]
def bucket4g9 : List (List Sig) := [[word8,word20,word28,word83,word101], [word8,word25,word83,word94,word98], [word25,word47,word56,word60,word76]]
def bucket4g10 : List (List Sig) := [[word20,word31,word83,word98,word99]]
def bucket4g11 : List (List Sig) := [[word12,word20,word25,word83,word99], [word20,word23,word73,word83,word99], [word20,word39,word70,word83,word99]]
def bucket4g12 : List (List Sig) := [[word8,word20,word83,word92,word99]]
def bucket4g13 : List (List Sig) := [[word20,word35,word47,word83,word99], [word25,word45,word56,word76,word99]]
def bucket4g14 : List (List Sig) := [[word4,word20,word31,word83,word101], [word4,word20,word77,word83,word99], [word8,word25,word38,word39,word98], [word20,word25,word41,word83,word87], [word20,word25,word73,word83,word89], [word25,word39,word47,word51,word76], [word25,word39,word56,word60,word76]]
def bucket4g15 : List (List Sig) := [[word1,word20,word73,word83,word99], [word20,word25,word73,word76,word99], [word37,word47,word56,word76,word99]]
def bucket4g16 : List (List Sig) := [[word6,word20,word28,word83,word99], [word20,word25,word58,word60,word83], [word20,word28,word73,word83,word99]]
def bucket4g17 : List (List Sig) := [[word4,word25,word63,word87,word97]]
def bucket4g18 : List (List Sig) := [[word20,word35,word39,word83,word99], [word37,word49,word56,word83,word99]]
def bucket4g19 : List (List Sig) := [[word13,word20,word25,word83,word99], [word17,word20,word25,word60,word83]]
def bucket4g20 : List (List Sig) := [[word10,word17,word25,word83,word99], [word20,word25,word65,word83,word99], [word20,word73,word81,word83,word99]]
def bucket4g21 : List (List Sig) := [[word4,word20,word29,word83,word99], [word4,word25,word83,word89,word97], [word17,word20,word25,word86,word99], [word17,word25,word37,word83,word99], [word20,word25,word48,word56,word60], [word39,word73,word76,word87,word99], [word47,word56,word76,word89,word99]]
def bucket4g22 : List (List Sig) := [[word20,word25,word47,word51,word83], [word20,word25,word56,word60,word83], [word25,word47,word55,word76,word99]]
def bucket4g23 : List (List Sig) := [[word17,word25,word63,word87,word99], [word20,word25,word41,word83,word99], [word20,word25,word51,word60,word83], [word20,word25,word51,word73,word83]]
def bucket4g24 : List (List Sig) := [[word8,word20,word26,word83,word99], [word20,word25,word73,word83,word101], [word49,word56,word83,word89,word99]]
def bucket4g25 : List (List Sig) := [[word8,word10,word28,word83,word99], [word17,word20,word37,word83,word99]]
def bucket4g26 : List (List Sig) := [[word8,word20,word28,word86,word99], [word20,word28,word78,word83,word99], [word25,word47,word56,word76,word100]]
def bucket4g27 : List (List Sig) := [[word17,word20,word63,word87,word99], [word17,word25,word83,word89,word99], [word20,word24,word47,word51,word83], [word20,word24,word56,word60,word83]]
def bucket4g28 : List (List Sig) := [[word20,word25,word47,word50,word83], [word25,word47,word56,word76,word93]]
def bucket4g29 : List (List Sig) := [[word2,word20,word31,word83,word99], [word20,word25,word70,word83,word99]]
def bucket4g30 : List (List Sig) := [[word0,word20,word73,word83,word99], [word4,word10,word31,word83,word99]]
def bucket4g31 : List (List Sig) := [[word4,word20,word31,word86,word99], [word8,word20,word25,word41,word83], [word17,word20,word83,word89,word99]]
def bucket4g32 : List (List Sig) := [[word20,word23,word47,word51,word83], [word20,word23,word56,word60,word83]]
def bucket4g33 : List (List Sig) := []
def bucket4g34 : List (List Sig) := [[word4,word8,word37,word83,word94], [word17,word20,word25,word83,word94], [word20,word31,word35,word83,word99]]
def bucket4g35 : List (List Sig) := []
def bucket4g36 : List (List Sig) := [[word1,word20,word47,word51,word83], [word1,word20,word56,word60,word83], [word17,word20,word25,word83,word100], [word20,word25,word35,word83,word99], [word20,word25,word47,word51,word76], [word20,word25,word48,word60,word83], [word20,word25,word56,word60,word76], [word20,word28,word31,word83,word99]]
def bucket4g37 : List (List Sig) := []
def bucket4g38 : List (List Sig) := [[word4,word8,word37,word83,word93], [word17,word20,word25,word83,word93]]
def bucket4g39 : List (List Sig) := [[word8,word20,word28,word83,word94], [word20,word25,word49,word51,word83], [word20,word25,word60,word73,word83], [word25,word73,word76,word87,word99]]
def bucket4g40 : List (List Sig) := [[word10,word25,word73,word83,word99]]
def bucket4g41 : List (List Sig) := [[word8,word20,word28,word83,word100], [word20,word47,word51,word81,word83], [word20,word56,word60,word81,word83], [word25,word37,word73,word83,word99]]
def bucket4g42 : List (List Sig) := []
def bucket4g43 : List (List Sig) := [[word20,word25,word41,word83], [word20,word25,word69,word83,word99]]
def bucket4g44 : List (List Sig) := [[word4,word20,word31,word83,word94], [word8,word25,word76,word80,word99], [word20,word25,word41,word56,word83]]
def bucket4g45 : List (List Sig) := [[word20,word25,word41,word51,word83], [word20,word25,word56,word61,word83], [word20,word25,word56,word62,word83], [word20,word37,word73,word83,word99], [word25,word46,word56,word76,word99], [word25,word47,word54,word76,word99]]
def bucket4g46 : List (List Sig) := [[word4,word20,word31,word83,word100]]
def bucket4g47 : List (List Sig) := [[word25,word73,word83,word89,word99]]
def bucket4g48 : List (List Sig) := []
def bucket4g49 : List (List Sig) := [[word11,word20,word25,word83,word99]]
def bucket4g50 : List (List Sig) := []
def bucket4g51 : List (List Sig) := [[word20,word28,word35,word83,word99], [word20,word73,word83,word89,word99]]
def bucket4g52 : List (List Sig) := [[word20,word25,word71,word83,word99]]
def bucket4g53 : List (List Sig) := [[word4,word20,word25,word41,word83]]
def bucket4g54 : List (List Sig) := [[word20,word25,word73,word83,word94], [word37,word47,word56,word83,word94]]
def bucket4g55 : List (List Sig) := []
def bucket4g56 : List (List Sig) := [[word8,word25,word73,word76,word99], [word20,word25,word73,word83,word100]]
def bucket4g57 : List (List Sig) := [[word20,word28,word83,word97,word99], [word20,word70,word83,word87,word99]]
def bucket4g58 : List (List Sig) := [[word20,word25,word73,word83,word93], [word37,word47,word56,word83,word93]]
def bucket4g59 : List (List Sig) := [[word4,word20,word83,word91,word99], [word20,word25,word73,word84,word99]]
def bucket4g60 : List (List Sig) := [[word20,word25,word41,word47,word83], [word25,word39,word83,word87,word95], [word25,word47,word51,word76,word87], [word25,word56,word60,word76,word87]]
def bucket4g61 : List (List Sig) := [[word4,word25,word83,word94,word97], [word10,word25,word47,word51,word83], [word10,word25,word56,word60,word83], [word20,word25,word41,word60,word83], [word20,word25,word41,word73,word83]]
def bucket4g62 : List (List Sig) := [[word8,word25,word63,word87,word98], [word25,word37,word47,word51,word83], [word25,word37,word56,word60,word83], [word25,word47,word58,word76,word99]]
def bucket4g63 : List (List Sig) := []
def bucket4g64 : List (List Sig) := [[word17,word25,word76,word83,word99], [word20,word25,word45,word51,word83], [word20,word35,word83,word87,word99]]
def bucket4g65 : List (List Sig) := [[word17,word20,word25,word88,word99], [word20,word25,word39,word41,word83], [word47,word56,word76,word93,word99]]
def bucket4g66 : List (List Sig) := [[word4,word25,word38,word39,word97], [word8,word25,word83,word89,word98], [word20,word37,word47,word51,word83], [word20,word37,word56,word60,word83], [word31,word47,word56,word76,word99]]
def bucket4g67 : List (List Sig) := [[word4,word8,word76,word81,word99], [word17,word25,word83,word94,word99]]
def bucket4g68 : List (List Sig) := [[word4,word8,word19,word25,word99], [word17,word20,word25,word80,word99], [word20,word25,word47,word52,word83], [word25,word47,word56,word76,word99], [word25,word73,word76,word99]]
def bucket4g69 : List (List Sig) := [[word8,word28,word76,word83,word99], [word20,word25,word83,word85,word99], [word20,word49,word58,word83,word99], [word25,word47,word51,word76,word99], [word25,word56,word60,word76,word99], [word25,word56,word73,word76,word99]]
def bucket4g70 : List (List Sig) := [[word8,word20,word28,word88,word99]]
def bucket4g71 : List (List Sig) := []
def bucket4g72 : List (List Sig) := [[word4,word8,word19,word20,word99], [word8,word20,word79,word83,word99], [word8,word28,word83,word94,word99], [word17,word25,word38,word39,word99]]
def bucket4g73 : List (List Sig) := [[word20,word25,word55,word60,word83], [word24,word47,word56,word76,word99]]
def bucket4g74 : List (List Sig) := [[word4,word31,word76,word83,word99], [word8,word20,word70,word83,word99]]
def bucket4g75 : List (List Sig) := [[word4,word20,word31,word88,word99], [word17,word20,word83,word93,word99], [word20,word25,word67,word83,word99], [word20,word25,word72,word83,word99], [word39,word83,word85,word87,word99]]
def bucket4g76 : List (List Sig) := [[word17,word20,word31,word83,word99], [word17,word20,word38,word39,word99]]
def bucket4g77 : List (List Sig) := [[word4,word31,word83,word94,word99], [word8,word25,word47,word51,word76], [word8,word25,word56,word60,word76], [word20,word25,word47,word53,word83]]
def bucket4g78 : List (List Sig) := [[word4,word20,word31,word80,word99], [word4,word25,word73,word76,word99], [word17,word20,word25,word83,word99], [word20,word25,word48,word57,word99], [word23,word47,word56,word76,word99]]
def bucket4g79 : List (List Sig) := [[word20,word25,word73,word83,word102]]
def bucket4g80 : List (List Sig) := [[word17,word20,word25,word73,word99], [word20,word25,word47,word51,word84], [word20,word25,word56,word60,word84]]
def bucket4g81 : List (List Sig) := [[word8,word20,word35,word83,word99], [word20,word25,word57,word73,word99]]
def bucket4g82 : List (List Sig) := [[word1,word47,word56,word76,word99]]
def bucket4g83 : List (List Sig) := [[word8,word20,word28,word83,word99], [word16,word20,word25,word83,word99], [word17,word20,word24,word83,word99], [word28,word47,word56,word76,word99]]
def bucket4g84 : List (List Sig) := [[word4,word8,word83,word93,word94], [word20,word31,word80,word83,word99], [word25,word73,word76,word83,word99]]
def bucket4g85 : List (List Sig) := [[word25,word47,word73,word76,word99], [word25,word49,word56,word76,word99]]
def bucket4g86 : List (List Sig) := [[word20,word46,word55,word83,word99], [word20,word70,word83,word99]]
def bucket4g87 : List (List Sig) := [[word20,word56,word70,word83,word99], [word25,word73,word83,word94,word99], [word47,word56,word76,word81,word99]]
def bucket4g88 : List (List Sig) := [[word4,word20,word31,word83,word99], [word4,word25,word76,word78,word99], [word15,word20,word25,word83,word99], [word17,word20,word23,word83,word99]]
def bucket4g89 : List (List Sig) := [[word25,word47,word51,word76], [word25,word56,word60,word76]]
def bucket4g90 : List (List Sig) := [[word17,word20,word25,word78,word99], [word25,word39,word73,word76,word99], [word25,word47,word51,word56,word76]]
def bucket4g91 : List (List Sig) := [[word17,word20,word25,word83,word89], [word17,word20,word35,word83,word99], [word20,word25,word83,word95,word99], [word20,word25,word83,word97,word98], [word25,word47,word56,word76,word101]]
def bucket4g92 : List (List Sig) := [[word1,word17,word20,word83,word99], [word37,word47,word58,word83,word99]]
def bucket4g93 : List (List Sig) := [[word3,word20,word31,word83,word99], [word4,word20,word30,word83,word99], [word7,word20,word28,word83,word99], [word8,word20,word27,word83,word99], [word14,word20,word25,word83,word99], [word17,word20,word22,word83,word99], [word17,word20,word28,word83,word99], [word20,word35,word83,word99]]
def bucket4g94 : List (List Sig) := [[word17,word20,word25,word38,word99], [word20,word35,word56,word83,word99]]
def bucket4g95 : List (List Sig) := [[word8,word20,word28,word78,word99], [word20,word73,word83,word93,word99]]
def bucket4g96 : List (List Sig) := [[word4,word20,word70,word83,word99], [word17,word20,word25,word63,word99], [word20,word25,word46,word51,word83], [word20,word25,word54,word60,word83], [word20,word31,word73,word83,word99]]
def table4 : Array (List (List Sig)) := #[bucket4g0,bucket4g1,bucket4g2,bucket4g3,bucket4g4,bucket4g5,bucket4g6,bucket4g7,bucket4g8,bucket4g9,bucket4g10,bucket4g11,bucket4g12,bucket4g13,bucket4g14,bucket4g15,bucket4g16,bucket4g17,bucket4g18,bucket4g19,bucket4g20,bucket4g21,bucket4g22,bucket4g23,bucket4g24,bucket4g25,bucket4g26,bucket4g27,bucket4g28,bucket4g29,bucket4g30,bucket4g31,bucket4g32,bucket4g33,bucket4g34,bucket4g35,bucket4g36,bucket4g37,bucket4g38,bucket4g39,bucket4g40,bucket4g41,bucket4g42,bucket4g43,bucket4g44,bucket4g45,bucket4g46,bucket4g47,bucket4g48,bucket4g49,bucket4g50,bucket4g51,bucket4g52,bucket4g53,bucket4g54,bucket4g55,bucket4g56,bucket4g57,bucket4g58,bucket4g59,bucket4g60,bucket4g61,bucket4g62,bucket4g63,bucket4g64,bucket4g65,bucket4g66,bucket4g67,bucket4g68,bucket4g69,bucket4g70,bucket4g71,bucket4g72,bucket4g73,bucket4g74,bucket4g75,bucket4g76,bucket4g77,bucket4g78,bucket4g79,bucket4g80,bucket4g81,bucket4g82,bucket4g83,bucket4g84,bucket4g85,bucket4g86,bucket4g87,bucket4g88,bucket4g89,bucket4g90,bucket4g91,bucket4g92,bucket4g93,bucket4g94,bucket4g95,bucket4g96]
def bucket5g0 : List (List Sig) := [[word4,word8,word20,word81,word83,word99], [word8,word20,word25,word83,word98,word99], [word20,word25,word47,word48,word56,word99]]
def bucket5g1 : List (List Sig) := [[word20,word25,word73,word83,word99], [word39,word47,word58,word83,word87,word99]]
def bucket5g2 : List (List Sig) := [[word20,word25,word47,word51,word83,word99], [word20,word25,word56,word60,word83,word99], [word20,word25,word56,word73,word83,word99]]
def bucket5g3 : List (List Sig) := [[word4,word8,word20,word25,word51,word83], [word8,word20,word28,word47,word83,word99], [word17,word20,word25,word39,word83,word99]]
def bucket5g4 : List (List Sig) := [[word4,word8,word20,word25,word83,word101]]
def bucket5g5 : List (List Sig) := []
def bucket5g6 : List (List Sig) := [[word20,word24,word47,word56,word83,word99]]
def bucket5g7 : List (List Sig) := []
def bucket5g8 : List (List Sig) := [[word4,word20,word31,word47,word83,word99], [word8,word20,word28,word39,word83,word99]]
def bucket5g9 : List (List Sig) := []
def bucket5g10 : List (List Sig) := [[word8,word20,word25,word47,word51,word83], [word8,word20,word25,word56,word60,word83]]
def bucket5g11 : List (List Sig) := [[word4,word6,word20,word25,word83,word99], [word4,word20,word25,word73,word83,word99], [word20,word23,word47,word56,word83,word99]]
def bucket5g12 : List (List Sig) := []
def bucket5g13 : List (List Sig) := [[word4,word20,word31,word39,word83,word99]]
def bucket5g14 : List (List Sig) := [[word20,word25,word39,word73,word83,word87], [word20,word25,word47,word56,word83,word89]]
def bucket5g15 : List (List Sig) := [[word1,word20,word47,word56,word83,word99], [word20,word25,word47,word48,word83,word99], [word20,word25,word47,word56,word76,word99]]
def bucket5g16 : List (List Sig) := [[word20,word28,word47,word56,word83,word99]]
def bucket5g17 : List (List Sig) := []
def bucket5g18 : List (List Sig) := [[word20,word25,word47,word73,word83,word99], [word20,word25,word49,word56,word83,word99]]
def bucket5g19 : List (List Sig) := [[word2,word8,word20,word25,word83,word99], [word4,word8,word20,word25,word60,word83]]
def bucket5g20 : List (List Sig) := [[word4,word8,word10,word25,word83,word99], [word20,word47,word56,word81,word83,word99]]
def bucket5g21 : List (List Sig) := [[word4,word8,word20,word25,word86,word99], [word4,word8,word25,word37,word83,word99], [word4,word20,word25,word78,word83,word99], [word4,word25,word39,word83,word87,word97], [word39,word47,word56,word76,word87,word99]]
def bucket5g22 : List (List Sig) := [[word20,word25,word47,word51,word83], [word20,word25,word56,word60,word83]]
def bucket5g23 : List (List Sig) := [[word4,word8,word25,word63,word87,word99], [word20,word25,word39,word73,word83,word99], [word20,word25,word47,word51,word56,word83]]
def bucket5g24 : List (List Sig) := [[word20,word25,word47,word56,word83,word101], [word39,word49,word56,word83,word87,word99]]
def bucket5g25 : List (List Sig) := [[word4,word8,word20,word37,word83,word99]]
def bucket5g26 : List (List Sig) := [[word8,word20,word25,word28,word83,word99]]
def bucket5g27 : List (List Sig) := [[word4,word8,word20,word63,word87,word99], [word4,word8,word25,word83,word89,word99], [word17,word25,word39,word83,word87,word99]]
def bucket5g28 : List (List Sig) := []
def bucket5g29 : List (List Sig) := []
def bucket5g30 : List (List Sig) := []
def bucket5g31 : List (List Sig) := [[word4,word8,word20,word83,word89,word99], [word4,word20,word25,word31,word83,word99], [word17,word20,word39,word83,word87,word99]]
def bucket5g32 : List (List Sig) := [[word4,word20,word25,word47,word51,word83], [word4,word20,word25,word56,word60,word83]]
def bucket5g33 : List (List Sig) := []
def bucket5g34 : List (List Sig) := [[word4,word8,word20,word25,word83,word94]]
def bucket5g35 : List (List Sig) := []
def bucket5g36 : List (List Sig) := [[word4,word8,word20,word25,word83,word100]]
def bucket5g37 : List (List Sig) := []
def bucket5g38 : List (List Sig) := [[word4,word8,word20,word25,word83,word93]]
def bucket5g39 : List (List Sig) := [[word20,word25,word47,word56,word60,word83], [word25,word47,word56,word76,word87,word99]]
def bucket5g40 : List (List Sig) := [[word10,word25,word47,word56,word83,word99]]
def bucket5g41 : List (List Sig) := [[word25,word37,word47,word56,word83,word99]]
def bucket5g42 : List (List Sig) := []
def bucket5g43 : List (List Sig) := [[word20,word25,word45,word56,word83,word99]]
def bucket5g44 : List (List Sig) := [[word20,word25,word39,word47,word51,word83], [word20,word25,word39,word56,word60,word83]]
def bucket5g45 : List (List Sig) := [[word20,word37,word47,word56,word83,word99]]
def bucket5g46 : List (List Sig) := []
def bucket5g47 : List (List Sig) := [[word25,word39,word73,word83,word87,word99], [word25,word47,word56,word83,word89,word99]]
def bucket5g48 : List (List Sig) := []
def bucket5g49 : List (List Sig) := [[word17,word20,word25,word83,word87,word99]]
def bucket5g50 : List (List Sig) := []
def bucket5g51 : List (List Sig) := [[word20,word39,word73,word83,word87,word99], [word20,word47,word56,word83,word89,word99]]
def bucket5g52 : List (List Sig) := [[word4,word20,word25,word83,word97,word99], [word20,word25,word47,word55,word83,word99]]
def bucket5g53 : List (List Sig) := []
def bucket5g54 : List (List Sig) := [[word8,word20,word28,word83,word87,word99], [word20,word25,word47,word56,word83,word94]]
def bucket5g55 : List (List Sig) := []
def bucket5g56 : List (List Sig) := [[word8,word25,word47,word56,word76,word99], [word20,word25,word47,word56,word83,word100]]
def bucket5g57 : List (List Sig) := []
def bucket5g58 : List (List Sig) := [[word20,word25,word47,word56,word83,word93]]
def bucket5g59 : List (List Sig) := [[word4,word20,word31,word83,word87,word99], [word20,word25,word47,word56,word84,word99]]
def bucket5g60 : List (List Sig) := []
def bucket5g61 : List (List Sig) := []
def bucket5g62 : List (List Sig) := []
def bucket5g63 : List (List Sig) := []
def bucket5g64 : List (List Sig) := [[word4,word8,word25,word76,word83,word99]]
def bucket5g65 : List (List Sig) := [[word4,word8,word20,word25,word88,word99]]
def bucket5g66 : List (List Sig) := [[word8,word17,word20,word25,word83,word99], [word8,word25,word39,word83,word87,word98]]
def bucket5g67 : List (List Sig) := [[word4,word8,word25,word83,word94,word99]]
def bucket5g68 : List (List Sig) := [[word4,word8,word20,word25,word80,word99], [word25,word47,word56,word76,word99]]
def bucket5g69 : List (List Sig) := [[word20,word25,word73,word83,word87,word99]]
def bucket5g70 : List (List Sig) := []
def bucket5g71 : List (List Sig) := []
def bucket5g72 : List (List Sig) := [[word4,word8,word25,word38,word39,word99]]
def bucket5g73 : List (List Sig) := []
def bucket5g74 : List (List Sig) := [[word8,word20,word25,word80,word83,word99]]
def bucket5g75 : List (List Sig) := [[word4,word8,word20,word83,word93,word99], [word20,word25,word46,word56,word83,word99], [word20,word25,word47,word54,word83,word99]]
def bucket5g76 : List (List Sig) := [[word4,word8,word20,word31,word83,word99], [word4,word8,word20,word38,word39,word99]]
def bucket5g77 : List (List Sig) := []
def bucket5g78 : List (List Sig) := [[word4,word25,word47,word56,word76,word99], [word17,word20,word25,word83,word99]]
def bucket5g79 : List (List Sig) := [[word17,word20,word25,word56,word83,word99]]
def bucket5g80 : List (List Sig) := [[word4,word8,word20,word25,word73,word99], [word17,word20,word25,word47,word56,word99], [word20,word25,word56,word57,word83,word99]]
def bucket5g81 : List (List Sig) := [[word20,word25,word47,word56,word57,word99]]
def bucket5g82 : List (List Sig) := []
def bucket5g83 : List (List Sig) := [[word3,word8,word20,word25,word83,word99], [word4,word8,word20,word24,word83,word99], [word8,word20,word28,word83,word99]]
def bucket5g84 : List (List Sig) := [[word8,word20,word28,word56,word83,word99], [word25,word47,word56,word76,word83,word99]]
def bucket5g85 : List (List Sig) := []
def bucket5g86 : List (List Sig) := [[word8,word20,word25,word73,word83,word99]]
def bucket5g87 : List (List Sig) := [[word25,word47,word56,word83,word94,word99]]
def bucket5g88 : List (List Sig) := [[word4,word7,word20,word25,word83,word99], [word4,word8,word20,word23,word83,word99], [word4,word17,word20,word25,word83,word99], [word4,word20,word31,word83,word99]]
def bucket5g89 : List (List Sig) := [[word4,word20,word31,word56,word83,word99]]
def bucket5g90 : List (List Sig) := [[word4,word8,word20,word25,word78,word99], [word20,word25,word47,word51,word83,word87], [word20,word25,word56,word60,word83,word87], [word25,word39,word47,word56,word76,word99]]
def bucket5g91 : List (List Sig) := [[word4,word8,word20,word25,word83,word89], [word17,word20,word25,word39,word83,word87]]
def bucket5g92 : List (List Sig) := [[word1,word4,word8,word20,word83,word99], [word20,word25,word47,word58,word83,word99]]
def bucket5g93 : List (List Sig) := [[word4,word8,word20,word28,word83,word99]]
def bucket5g94 : List (List Sig) := [[word4,word8,word20,word25,word38,word99]]
def bucket5g95 : List (List Sig) := [[word17,word20,word25,word47,word83,word99], [word20,word47,word56,word83,word93,word99]]
def bucket5g96 : List (List Sig) := [[word4,word8,word20,word25,word63,word99], [word20,word31,word47,word56,word83,word99]]
def table5 : Array (List (List Sig)) := #[bucket5g0,bucket5g1,bucket5g2,bucket5g3,bucket5g4,bucket5g5,bucket5g6,bucket5g7,bucket5g8,bucket5g9,bucket5g10,bucket5g11,bucket5g12,bucket5g13,bucket5g14,bucket5g15,bucket5g16,bucket5g17,bucket5g18,bucket5g19,bucket5g20,bucket5g21,bucket5g22,bucket5g23,bucket5g24,bucket5g25,bucket5g26,bucket5g27,bucket5g28,bucket5g29,bucket5g30,bucket5g31,bucket5g32,bucket5g33,bucket5g34,bucket5g35,bucket5g36,bucket5g37,bucket5g38,bucket5g39,bucket5g40,bucket5g41,bucket5g42,bucket5g43,bucket5g44,bucket5g45,bucket5g46,bucket5g47,bucket5g48,bucket5g49,bucket5g50,bucket5g51,bucket5g52,bucket5g53,bucket5g54,bucket5g55,bucket5g56,bucket5g57,bucket5g58,bucket5g59,bucket5g60,bucket5g61,bucket5g62,bucket5g63,bucket5g64,bucket5g65,bucket5g66,bucket5g67,bucket5g68,bucket5g69,bucket5g70,bucket5g71,bucket5g72,bucket5g73,bucket5g74,bucket5g75,bucket5g76,bucket5g77,bucket5g78,bucket5g79,bucket5g80,bucket5g81,bucket5g82,bucket5g83,bucket5g84,bucket5g85,bucket5g86,bucket5g87,bucket5g88,bucket5g89,bucket5g90,bucket5g91,bucket5g92,bucket5g93,bucket5g94,bucket5g95,bucket5g96]
def bucket6g0 : List (List Sig) := []
def bucket6g1 : List (List Sig) := [[word20,word25,word47,word56,word83,word99]]
def bucket6g2 : List (List Sig) := []
def bucket6g3 : List (List Sig) := [[word4,word8,word20,word25,word39,word83,word99]]
def bucket6g4 : List (List Sig) := []
def bucket6g5 : List (List Sig) := []
def bucket6g6 : List (List Sig) := []
def bucket6g7 : List (List Sig) := []
def bucket6g8 : List (List Sig) := []
def bucket6g9 : List (List Sig) := []
def bucket6g10 : List (List Sig) := []
def bucket6g11 : List (List Sig) := [[word4,word20,word25,word47,word56,word83,word99]]
def bucket6g12 : List (List Sig) := []
def bucket6g13 : List (List Sig) := []
def bucket6g14 : List (List Sig) := [[word20,word25,word39,word47,word56,word83,word87]]
def bucket6g15 : List (List Sig) := []
def bucket6g16 : List (List Sig) := []
def bucket6g17 : List (List Sig) := []
def bucket6g18 : List (List Sig) := []
def bucket6g19 : List (List Sig) := []
def bucket6g20 : List (List Sig) := []
def bucket6g21 : List (List Sig) := []
def bucket6g22 : List (List Sig) := []
def bucket6g23 : List (List Sig) := [[word20,word25,word39,word47,word56,word83,word99]]
def bucket6g24 : List (List Sig) := []
def bucket6g25 : List (List Sig) := []
def bucket6g26 : List (List Sig) := []
def bucket6g27 : List (List Sig) := [[word4,word8,word25,word39,word83,word87,word99]]
def bucket6g28 : List (List Sig) := []
def bucket6g29 : List (List Sig) := []
def bucket6g30 : List (List Sig) := []
def bucket6g31 : List (List Sig) := [[word4,word8,word20,word39,word83,word87,word99]]
def bucket6g32 : List (List Sig) := []
def bucket6g33 : List (List Sig) := []
def bucket6g34 : List (List Sig) := []
def bucket6g35 : List (List Sig) := []
def bucket6g36 : List (List Sig) := []
def bucket6g37 : List (List Sig) := []
def bucket6g38 : List (List Sig) := []
def bucket6g39 : List (List Sig) := []
def bucket6g40 : List (List Sig) := []
def bucket6g41 : List (List Sig) := []
def bucket6g42 : List (List Sig) := []
def bucket6g43 : List (List Sig) := []
def bucket6g44 : List (List Sig) := []
def bucket6g45 : List (List Sig) := []
def bucket6g46 : List (List Sig) := []
def bucket6g47 : List (List Sig) := [[word25,word39,word47,word56,word83,word87,word99]]
def bucket6g48 : List (List Sig) := []
def bucket6g49 : List (List Sig) := [[word4,word8,word20,word25,word83,word87,word99]]
def bucket6g50 : List (List Sig) := []
def bucket6g51 : List (List Sig) := [[word20,word39,word47,word56,word83,word87,word99]]
def bucket6g52 : List (List Sig) := []
def bucket6g53 : List (List Sig) := []
def bucket6g54 : List (List Sig) := []
def bucket6g55 : List (List Sig) := []
def bucket6g56 : List (List Sig) := []
def bucket6g57 : List (List Sig) := []
def bucket6g58 : List (List Sig) := []
def bucket6g59 : List (List Sig) := []
def bucket6g60 : List (List Sig) := []
def bucket6g61 : List (List Sig) := []
def bucket6g62 : List (List Sig) := []
def bucket6g63 : List (List Sig) := []
def bucket6g64 : List (List Sig) := []
def bucket6g65 : List (List Sig) := []
def bucket6g66 : List (List Sig) := []
def bucket6g67 : List (List Sig) := []
def bucket6g68 : List (List Sig) := []
def bucket6g69 : List (List Sig) := [[word20,word25,word47,word56,word83,word87,word99]]
def bucket6g70 : List (List Sig) := []
def bucket6g71 : List (List Sig) := []
def bucket6g72 : List (List Sig) := []
def bucket6g73 : List (List Sig) := []
def bucket6g74 : List (List Sig) := []
def bucket6g75 : List (List Sig) := []
def bucket6g76 : List (List Sig) := []
def bucket6g77 : List (List Sig) := []
def bucket6g78 : List (List Sig) := [[word4,word8,word20,word25,word83,word99]]
def bucket6g79 : List (List Sig) := [[word4,word8,word20,word25,word56,word83,word99]]
def bucket6g80 : List (List Sig) := [[word4,word8,word20,word25,word47,word56,word99]]
def bucket6g81 : List (List Sig) := []
def bucket6g82 : List (List Sig) := []
def bucket6g83 : List (List Sig) := []
def bucket6g84 : List (List Sig) := []
def bucket6g85 : List (List Sig) := []
def bucket6g86 : List (List Sig) := [[word8,word20,word25,word47,word56,word83,word99]]
def bucket6g87 : List (List Sig) := []
def bucket6g88 : List (List Sig) := []
def bucket6g89 : List (List Sig) := []
def bucket6g90 : List (List Sig) := []
def bucket6g91 : List (List Sig) := [[word4,word8,word20,word25,word39,word83,word87]]
def bucket6g92 : List (List Sig) := []
def bucket6g93 : List (List Sig) := []
def bucket6g94 : List (List Sig) := []
def bucket6g95 : List (List Sig) := [[word4,word8,word20,word25,word47,word83,word99]]
def bucket6g96 : List (List Sig) := []
def table6 : Array (List (List Sig)) := #[bucket6g0,bucket6g1,bucket6g2,bucket6g3,bucket6g4,bucket6g5,bucket6g6,bucket6g7,bucket6g8,bucket6g9,bucket6g10,bucket6g11,bucket6g12,bucket6g13,bucket6g14,bucket6g15,bucket6g16,bucket6g17,bucket6g18,bucket6g19,bucket6g20,bucket6g21,bucket6g22,bucket6g23,bucket6g24,bucket6g25,bucket6g26,bucket6g27,bucket6g28,bucket6g29,bucket6g30,bucket6g31,bucket6g32,bucket6g33,bucket6g34,bucket6g35,bucket6g36,bucket6g37,bucket6g38,bucket6g39,bucket6g40,bucket6g41,bucket6g42,bucket6g43,bucket6g44,bucket6g45,bucket6g46,bucket6g47,bucket6g48,bucket6g49,bucket6g50,bucket6g51,bucket6g52,bucket6g53,bucket6g54,bucket6g55,bucket6g56,bucket6g57,bucket6g58,bucket6g59,bucket6g60,bucket6g61,bucket6g62,bucket6g63,bucket6g64,bucket6g65,bucket6g66,bucket6g67,bucket6g68,bucket6g69,bucket6g70,bucket6g71,bucket6g72,bucket6g73,bucket6g74,bucket6g75,bucket6g76,bucket6g77,bucket6g78,bucket6g79,bucket6g80,bucket6g81,bucket6g82,bucket6g83,bucket6g84,bucket6g85,bucket6g86,bucket6g87,bucket6g88,bucket6g89,bucket6g90,bucket6g91,bucket6g92,bucket6g93,bucket6g94,bucket6g95,bucket6g96]
def banks (k : Nat) (i : Fin 97) : List (List Sig) :=
  let t := match k with
    | 1 => table1
    | 2 => table2
    | 3 => table3
    | 4 => table4
    | 5 => table5
    | 6 => table6
    | _ => #[]
  t[i.val]?.getD []
def safeB (k : Nat) (ws : List Sig) : Bool :=
  !(ws.contains goal) && (decide (cuts ws ≠ -1) || decide (k=0) || (banks k (bucketId (canon ws))).contains (canon ws))
def stepB (k : Nat) (ws : List Sig) : Bool := !(ws.contains goal) &&
  branches (k+1) ws (safeB k)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem allStep0 : ∀ i : Fin 97, (banks 1 i).all (stepB 0) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem allStep1 : ∀ i : Fin 97, (banks 2 i).all (stepB 1) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem allStep2 : ∀ i : Fin 97, (banks 3 i).all (stepB 2) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem allStep3 : ∀ i : Fin 97, (banks 4 i).all (stepB 3) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem allStep4 : ∀ i : Fin 97, (banks 5 i).all (stepB 4) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem allStep5 : ∀ i : Fin 97, (banks 6 i).all (stepB 5) = true := by decide +kernel
theorem allSteps (k : Fin 6) : ∀ i : Fin 97, (banks (k.val+1) i).all (stepB k.val) = true := by
  have casesk : k=0 ∨ k=1 ∨ k=2 ∨ k=3 ∨ k=4 ∨ k=5 := by omega
  rcases casesk with rfl | rfl | rfl | rfl | rfl | rfl
  · exact allStep0
  · exact allStep1
  · exact allStep2
  · exact allStep3
  · exact allStep4
  · exact allStep5
theorem safeB_sound (cap : Nat) (bound : cap ≤ 6) (ws : List Sig) (nd : ws.Nodup) (ok : safeB cap ws=true) :
    Impossible true goal cap ws.toFinset := by
  induction cap generalizing ws with
  | zero =>
    have hm : goal ∉ ws := by simpa [safeB] using ok
    intro k hk h
    have eq : k=0 := by omega
    subst k
    have hmem : goal ∈ ws.toFinset := h.1.symm ▸ Finset.mem_singleton_self _
    exact hm (List.mem_toFinset.mp hmem)
  | succ k ih =>
    let cs := canon ws
    have pp : cs.Perm ws := List.perm_insertionSort _ _
    have ews : cs.toFinset=ws.toFinset := by
      ext a; simpa only [List.mem_toFinset] using (pp.mem_iff (a:=a))
    have csnd := pp.nodup_iff.mpr nd
    simp only [safeB,Bool.and_eq_true,Bool.or_eq_true,decide_eq_true_eq] at ok
    have hm : goal ∉ ws := by simpa using ok.1
    rcases ok.2 with (short | zeroCap) | member
    · exact fun j _ hj => short (cuts_full hj)
    · omega
    · have mem : cs ∈ banks (k+1) (bucketId cs) := by simpa using member
      have res := List.all_eq_true.mp (allSteps (⟨k,by omega⟩ : Fin 6) (bucketId cs)) cs mem
      change (!(cs.contains goal) && branches (k+1) cs (safeB k)) = true at res
      simp only [Bool.and_eq_true] at res
      have scan := res.2
      rw [←ews]
      have hm' : goal ∉ cs := fun h => hm (pp.mem_iff.mp h)
      apply enum_step csnd hm'
      intro a ha b hb d hd ka kb ne fresh pro len
      have ed : d∈List.range 4 := List.mem_range.mpr (by rcases hd with h | ⟨_,h⟩ <;> omega)
      obtain ⟨za,zb⟩ := pro
      have h := List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp
        (List.all_eq_true.mp (List.all_eq_true.mp scan a ha) b hb) d ed) ka
        (by cases ka <;> simp)) kb (by cases kb <;> simp)
      simp only [Bool.or_eq_true,decide_eq_true_eq] at h
      rcases h with (he | he | he | he | he) | hk
      · exact (ne he).elim
      · exact (fresh he).elim
      · exact (za he).elim
      · exact (zb he).elim
      · omega
      · have fn := ih (by omega) _ (List.nodup_eraseDups _) hk
        simpa [Impossible] using fn

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem init_ok : (initial.sublists.filter fun ws => decide (ws.length ≤ 7)).all (safeB 6)=true := by decide +kernel
theorem initialND : initial.Nodup := by decide +kernel
theorem actual (C : Circuit) (hf : PEqualNP.MetaComplexity.FanInTwo C) (hr : Matches C) :
    7 + PEqualNP.NotBracket.notCount C ≤ C.size := by
  obtain ⟨k,S,hk,run,sub⟩ := realizes C hf hr
  have le : 7 ≤ k := by
    by_contra h
    let ws := initial.filter (fun w => decide (w ∈ S))
    have hx : ws.toFinset = S := by
      ext w
      simp only [ws,List.mem_toFinset,List.mem_filter,decide_eq_true_eq]
      exact ⟨And.right,fun hw => ⟨sub w hw,hw⟩⟩
    have listed : ws ∈ initial.sublists := List.mem_sublists.mpr List.filter_sublist
    have widthS := live_size run
    have width : ws.length ≤ 7 := by
      rw [←List.toFinset_card_of_nodup (initialND.filter _),hx]
      omega
    have included : ws ∈ initial.sublists.filter (fun v => decide (v.length ≤ 7)) :=
      List.mem_filter.mpr ⟨listed,decide_eq_true width⟩
    exact safeB_sound 6 (by decide) ws (initialND.filter _) (List.all_eq_true.mp init_ok _ included) k (by omega) (hx ▸ run)
  have eq : PEqualNP.NotBracket.notCount C = C.gates.countP isNot := by
    unfold PEqualNP.NotBracket.notCount
    rw [List.countP_eq_length_filter]
    congr 1
    apply List.filter_congr
    intro g _
    cases g with
    | mk op ins => cases op <;> rfl
  have total : C.gates.length = C.gates.countP isNot + C.gates.countP (fun g => !isNot g) := by
    simpa using List.length_eq_countP_add_countP (l:=C.gates) isNot
  change 7 + PEqualNP.NotBracket.notCount C ≤ C.gates.length
  omega

end PEqualNP.Outside.L_meta_19374.Binary
open PEqualNP.Outside.L_meta_19374.Binary in
theorem PEqualNP.Outside.L_meta_19374 (C : PEqualNP.CircuitLowerBounds.Circuit) (hf : PEqualNP.MetaComplexity.FanInTwo C) (hr : Matches C) :
    7 + PEqualNP.NotBracket.notCount C ≤ C.size := actual C hf hr

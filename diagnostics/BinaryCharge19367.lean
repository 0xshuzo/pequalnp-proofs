import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19367.Binary
open PEqualNP.CircuitLowerBounds
abbrev Sig := BitVec 300
def zero : Sig := 0
def one : Sig := BitVec.allOnes 300
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

def bit (i : Fin 300) (a : Sig) : Bool := a.getLsbD i.val
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


abbrev Row := Fin 300
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

def original : List Sig := [(BitVec.ofNat 300 (1127000493261825+2^60*(1127000493261825+2^60*(1152921503534154753+2^60*1023)))),(BitVec.ofNat 300 (15778006905665550+2^60*(15778006905665550+2^60*(14694414+2^60*1073740800)))),(BitVec.ofNat 300 (54096023676567600+2^60*(54096023676567600+2^60*(50380848+2^60*1152921503533105152)))),(BitVec.ofNat 300 (216384094706270400+2^60*(216384094706270400+2^60*(201523392+2^60*(0+2^60*1073741823))))),(BitVec.ofNat 300 (865536378825081600+2^60*(865536378825081600+2^60*(806093568+2^60*(0+2^60*1152921503533105152))))),(BitVec.ofNat 300 (1127000493261825+2^60*(1127000493261825+2^60*(1049601+2^60*(1098438933504+2^60*1098437886975))))),(BitVec.ofNat 300 (2254000986523650+2^60*(2254000986523650+2^60*(1098439985154+2^60*(1124800395214848+2^60*1124800396262400))))),(BitVec.ofNat 300 (4508001973047300+2^60*(4508001973047300+2^60*(1124800399413252+2^60*(1151795604700004352+2^60*1151795605772697600))))),(BitVec.ofNat 300 (387688169682067800+2^60*(387688169682067800+2^60*1151795605061067096))),(BitVec.ofNat 300 (757344331471946400+2^60*(757344331471946400+2^60*(705331872+2^60*1072694271))))]
def initial := original.map (nrm true)
def goal : Sig := (-1 : BitVec 150) ++ (0 : BitVec 150)
def pRows : List (Fin 5 × Fin 5) := [(0, 1), (0, 2), (0, 3), (0, 4), (1, 0), (1, 4), (2, 0), (2, 1), (2, 2), (3, 0), (3, 1), (3, 2), (4, 0), (4, 1), (4, 2)]
def nRows : List (Fin 5 × Fin 5) := [(0, 0), (1, 1), (1, 2), (1, 3), (2, 3), (2, 4), (3, 3), (3, 4), (4, 3), (4, 4)]
def samp (k : Row) := if k.val < 150 then nRows.getD (k.val % 10) (0,0) else pRows.getD ((k.val-150)/10) (0,0)
def target (p : Fin 5 × Fin 5) := (7577150 : Nat).testBit (5*p.1.val+p.2.val)
def physical (p : Fin 5 × Fin 5) := PEqualNP.Represents.oneEach p.1 p.2
def Matches (C : Circuit) := PEqualNP.Represents.Represents (fun u v : Fin 5 => (7577150 : ℕ).testBit (5 * u.val + v.val)) C
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

def column (x : Sig) : BitVec 150 := ((x >>> 150) ^^^ x).setWidth 150
def cuts (ws : List Sig) : BitVec 150 := ws.foldr (fun w v => column w ||| v) 0
def differs (i : Fin 150) (w : Sig) := w.getLsbD (150+i.val) ≠ w.getLsbD i.val
theorem cuts_spec (ws : List Sig) (i : Fin 150) :
    (cuts ws).getLsbD i.val = true ↔ ∃ w ∈ ws, differs i w := by
  induction ws with
  | nil => simp [cuts]
  | cons a rest ih =>
    change (column a ||| cuts rest).getLsbD i.val = true ↔ _
    rw [BitVec.getLsbD_or, Bool.or_eq_true, ih]
    have hi : i.val < 300 := by omega
    have eq : (column a).getLsbD i.val = true ↔ differs i a := by
      cases e : a.getLsbD (i.val+150) <;> cases f : a.getLsbD i.val <;>
        simp [column, differs, hi, i.isLt, Nat.add_comm, e, f] at *
    rw [eq]
    simp
theorem goal_differs : ∀ i : Fin 150, differs i goal := by unfold differs; decide +kernel
theorem cuts_full {k ws} (h : Live true goal k (List.toFinset ws)) : cuts ws = -1 := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  let q : Fin 150 := ⟨i,hi⟩
  have hx : bit (⟨150+i,by omega⟩ : Row) goal ≠ bit (⟨i,by omega⟩ : Row) goal := goal_differs q
  obtain ⟨a,ha,hd⟩ := live_row_difference h hx
  have hh := (cuts_spec ws q).mpr ⟨a,List.mem_toFinset.mp ha,hd⟩
  change (cuts ws)[i] = (BitVec.allOnes 150)[i]
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
def word0 : Sig := BitVec.ofNat 300 (2254000986523650+2^60*(2254000986523650+2^60*2099202))
def word1 : Sig := BitVec.ofNat 300 (4508001973047300+2^60*(4508001973047300+2^60*4198404))
def word2 : Sig := BitVec.ofNat 300 (9016003946094600+2^60*(9016003946094600+2^60*8396808))
def word3 : Sig := BitVec.ofNat 300 (18032007892189200+2^60*(18032007892189200+2^60*16793616))
def word4 : Sig := BitVec.ofNat 300 (36064015784378400+2^60*(36064015784378400+2^60*33587232))
def word5 : Sig := BitVec.ofNat 300 (72128031568756800+2^60*(72128031568756800+2^60*67174464))
def word6 : Sig := BitVec.ofNat 300 (144256063137513600+2^60*(144256063137513600+2^60*134348928))
def word7 : Sig := BitVec.ofNat 300 (288512126275027200+2^60*(288512126275027200+2^60*268697856))
def word8 : Sig := BitVec.ofNat 300 (378672165735973200+2^60*(378672165735973200+2^60*352665936))
def word9 : Sig := BitVec.ofNat 300 (387688169682067800+2^60*(387688169682067800+2^60*361062744))
def word10 : Sig := BitVec.ofNat 300 (577024252550054400+2^60*(577024252550054400+2^60*537395712))
def word11 : Sig := BitVec.ofNat 300 (0+2^60*(0+2^60*1098437885952))
def word12 : Sig := BitVec.ofNat 300 (0+2^60*(0+2^60*1124800395214848))
def word13 : Sig := BitVec.ofNat 300 (0+2^60*(0+2^60*1151795604700004352))
def word14 : Sig := BitVec.ofNat 300 (99176043407040600+2^60*(99176043407040600+2^60*1151795604792369240))
def word15 : Sig := BitVec.ofNat 300 (315560138113311000+2^60*(315560138113311000+2^60*1151795604993892632))
def word16 : Sig := BitVec.ofNat 300 (369656161789878600+2^60*(369656161789878600+2^60*1151795605044273480))
def word17 : Sig := BitVec.ofNat 300 (378672165735973200+2^60*(378672165735973200+2^60*1151795605052670288))
def word18 : Sig := BitVec.ofNat 300 (387688169682067800+2^60*(387688169682067800+2^60*1151795605061067096))
def word19 : Sig := BitVec.ofNat 300 (389942170668591450+2^60*(389942170668591450+2^60*1151795605063166298))
def word20 : Sig := BitVec.ofNat 300 (392196171655115100+2^60*(392196171655115100+2^60*1151795605065265500))
def word21 : Sig := BitVec.ofNat 300 (423752185466446200+2^60*(423752185466446200+2^60*1151795605094654328))
def word22 : Sig := BitVec.ofNat 300 (531944232819581400+2^60*(531944232819581400+2^60*1151795605195416024))
def word23 : Sig := BitVec.ofNat 300 (964712422232122200+2^60*(964712422232122200+2^60*1151795605598462808))
def word24 : Sig := BitVec.ofNat 300 (387688169682067800+2^60*(387688169682067800+2^60*1151796703498953048))
def word25 : Sig := BitVec.ofNat 300 (387688169682067800+2^60*(387688169682067800+2^60*1152920405456281944))
def word26 : Sig := BitVec.ofNat 300 (0+2^60*(0+2^60*(0+2^60*1023)))
def word27 : Sig := BitVec.ofNat 300 (757344331471946400+2^60*(757344331471946400+2^60*(705331872+2^60*1023)))
def word28 : Sig := BitVec.ofNat 300 (387688169682067800+2^60*(387688169682067800+2^60*(1151795605061067096+2^60*1023)))
def word29 : Sig := BitVec.ofNat 300 (1136016497207919600+2^60*(1136016497207919600+2^60*(1151795605758002160+2^60*1023)))
def word30 : Sig := BitVec.ofNat 300 (1145032501154014200+2^60*(1145032501154014200+2^60*(1151795605766398968+2^60*1023)))
def word31 : Sig := BitVec.ofNat 300 (0+2^60*(0+2^60*(1152921503533105152+2^60*1023)))
def word32 : Sig := BitVec.ofNat 300 (387688169682067800+2^60*(387688169682067800+2^60*(1152921503894167896+2^60*1023)))
def word33 : Sig := BitVec.ofNat 300 (0+2^60*(0+2^60*(0+2^60*1047552)))
def word34 : Sig := BitVec.ofNat 300 (15778006905665550+2^60*(15778006905665550+2^60*(14694414+2^60*1047552)))
def word35 : Sig := BitVec.ofNat 300 (387688169682067800+2^60*(387688169682067800+2^60*(1151795605061067096+2^60*1047552)))
def word36 : Sig := BitVec.ofNat 300 (394450172641638750+2^60*(394450172641638750+2^60*(1151795605067364702+2^60*1047552)))
def word37 : Sig := BitVec.ofNat 300 (773122338377611950+2^60*(773122338377611950+2^60*(720026286+2^60*1048575)))
def word38 : Sig := BitVec.ofNat 300 (1151794504113585150+2^60*(1151794504113585150+2^60*(1151795605772696574+2^60*1048575)))
def word39 : Sig := BitVec.ofNat 300 (0+2^60*(0+2^60*(0+2^60*1072693248)))
def word40 : Sig := BitVec.ofNat 300 (6762002959570950+2^60*(6762002959570950+2^60*(6297606+2^60*1072693248)))
def word41 : Sig := BitVec.ofNat 300 (15778006905665550+2^60*(15778006905665550+2^60*(14694414+2^60*1072693248)))
def word42 : Sig := BitVec.ofNat 300 (394450172641638750+2^60*(394450172641638750+2^60*(367360350+2^60*1072693248)))
def word43 : Sig := BitVec.ofNat 300 (757344331471946400+2^60*(757344331471946400+2^60*(705331872+2^60*1072693248)))
def word44 : Sig := BitVec.ofNat 300 (1136016497207919600+2^60*(1136016497207919600+2^60*(1057997808+2^60*1072693248)))
def word45 : Sig := BitVec.ofNat 300 (1145032501154014200+2^60*(1145032501154014200+2^60*(1066394616+2^60*1072693248)))
def word46 : Sig := BitVec.ofNat 300 (387688169682067800+2^60*(387688169682067800+2^60*(1151795605061067096+2^60*1072693248)))
def word47 : Sig := BitVec.ofNat 300 (394450172641638750+2^60*(394450172641638750+2^60*(1151795605067364702+2^60*1072693248)))
def word48 : Sig := BitVec.ofNat 300 (1136016497207919600+2^60*(1136016497207919600+2^60*(1151795605758002160+2^60*1072693248)))
def word49 : Sig := BitVec.ofNat 300 (1145032501154014200+2^60*(1145032501154014200+2^60*(1151795605766398968+2^60*1072693248)))
def word50 : Sig := BitVec.ofNat 300 (15778006905665550+2^60*(15778006905665550+2^60*(1152921503547799566+2^60*1072693248)))
def word51 : Sig := BitVec.ofNat 300 (394450172641638750+2^60*(394450172641638750+2^60*(1152921503900465502+2^60*1072693248)))
def word52 : Sig := BitVec.ofNat 300 (180320078921892000+2^60*(180320078921892000+2^60*(167936160+2^60*1072694271)))
def word53 : Sig := BitVec.ofNat 300 (613088268334432800+2^60*(613088268334432800+2^60*(570982944+2^60*1072694271)))
def word54 : Sig := BitVec.ofNat 300 (721280315687568000+2^60*(721280315687568000+2^60*(671744640+2^60*1072694271)))
def word55 : Sig := BitVec.ofNat 300 (757344331471946400+2^60*(757344331471946400+2^60*(705331872+2^60*1072694271)))
def word56 : Sig := BitVec.ofNat 300 (766360335418041000+2^60*(766360335418041000+2^60*(713728680+2^60*1072694271)))
def word57 : Sig := BitVec.ofNat 300 (775376339364135600+2^60*(775376339364135600+2^60*(722125488+2^60*1072694271)))
def word58 : Sig := BitVec.ofNat 300 (829472363040703200+2^60*(829472363040703200+2^60*(772506336+2^60*1072694271)))
def word59 : Sig := BitVec.ofNat 300 (1045856457746973600+2^60*(1045856457746973600+2^60*(974029728+2^60*1072694271)))
def word60 : Sig := BitVec.ofNat 300 (1136016497207919600+2^60*(1136016497207919600+2^60*(1057997808+2^60*1072694271)))
def word61 : Sig := BitVec.ofNat 300 (1145032501154014200+2^60*(1145032501154014200+2^60*(1066394616+2^60*1072694271)))
def word62 : Sig := BitVec.ofNat 300 (757344331471946400+2^60*(757344331471946400+2^60*(1099143217824+2^60*1072694271)))
def word63 : Sig := BitVec.ofNat 300 (757344331471946400+2^60*(757344331471946400+2^60*(1124801100546720+2^60*1072694271)))
def word64 : Sig := BitVec.ofNat 300 (6762002959570950+2^60*(6762002959570950+2^60*(1125898839398406+2^60*1072694271)))
def word65 : Sig := BitVec.ofNat 300 (15778006905665550+2^60*(15778006905665550+2^60*(1125898847795214+2^60*1072694271)))
def word66 : Sig := BitVec.ofNat 300 (568008248603959800+2^60*(568008248603959800+2^60*(1151795605229003256+2^60*1072694271)))
def word67 : Sig := BitVec.ofNat 300 (757344331471946400+2^60*(757344331471946400+2^60*(1151795605405336224+2^60*1072694271)))
def word68 : Sig := BitVec.ofNat 300 (856520374878987000+2^60*(856520374878987000+2^60*(1151795605497701112+2^60*1072694271)))
def word69 : Sig := BitVec.ofNat 300 (1000776438016500600+2^60*(1000776438016500600+2^60*(1151795605632050040+2^60*1072694271)))
def word70 : Sig := BitVec.ofNat 300 (1072904469585257400+2^60*(1072904469585257400+2^60*(1151795605699224504+2^60*1072694271)))
def word71 : Sig := BitVec.ofNat 300 (1108968485369635800+2^60*(1108968485369635800+2^60*(1151795605732811736+2^60*1072694271)))
def word72 : Sig := BitVec.ofNat 300 (1127000493261825000+2^60*(1127000493261825000+2^60*(1151795605749605352+2^60*1072694271)))
def word73 : Sig := BitVec.ofNat 300 (1136016497207919600+2^60*(1136016497207919600+2^60*(1151795605758002160+2^60*1072694271)))
def word74 : Sig := BitVec.ofNat 300 (1145032501154014200+2^60*(1145032501154014200+2^60*(1151795605766398968+2^60*1072694271)))
def word75 : Sig := BitVec.ofNat 300 (15778006905665550+2^60*(15778006905665550+2^60*(1151796703152584718+2^60*1072694271)))
def word76 : Sig := BitVec.ofNat 300 (394450172641638750+2^60*(394450172641638750+2^60*(1151796703505250654+2^60*1072694271)))
def word77 : Sig := BitVec.ofNat 300 (15778006905665550+2^60*(15778006905665550+2^60*(1152920405109913614+2^60*1072694271)))
def word78 : Sig := BitVec.ofNat 300 (394450172641638750+2^60*(394450172641638750+2^60*(1152920405462579550+2^60*1072694271)))
def word79 : Sig := BitVec.ofNat 300 (6762002959570950+2^60*(6762002959570950+2^60*(1152921503539402758+2^60*1072694271)))
def word80 : Sig := BitVec.ofNat 300 (15778006905665550+2^60*(15778006905665550+2^60*(1152921503547799566+2^60*1072694271)))
def word81 : Sig := BitVec.ofNat 300 (394450172641638750+2^60*(394450172641638750+2^60*(1152921503900465502+2^60*1072694271)))
def word82 : Sig := BitVec.ofNat 300 (757344331471946400+2^60*(757344331471946400+2^60*(1152921504238437024+2^60*1072694271)))
def word83 : Sig := BitVec.ofNat 300 (6762002959570950+2^60*(6762002959570950+2^60*(6297606+2^60*1073740800)))
def word84 : Sig := BitVec.ofNat 300 (11270004932618250+2^60*(11270004932618250+2^60*(10496010+2^60*1073740800)))
def word85 : Sig := BitVec.ofNat 300 (13524005919141900+2^60*(13524005919141900+2^60*(12595212+2^60*1073740800)))
def word86 : Sig := BitVec.ofNat 300 (15778006905665550+2^60*(15778006905665550+2^60*(14694414+2^60*1073740800)))
def word87 : Sig := BitVec.ofNat 300 (33810014797854750+2^60*(33810014797854750+2^60*(31488030+2^60*1073740800)))
def word88 : Sig := BitVec.ofNat 300 (87906038474422350+2^60*(87906038474422350+2^60*(81868878+2^60*1073740800)))
def word89 : Sig := BitVec.ofNat 300 (304290133180692750+2^60*(304290133180692750+2^60*(283392270+2^60*1073740800)))
def word90 : Sig := BitVec.ofNat 300 (394450172641638750+2^60*(394450172641638750+2^60*(367360350+2^60*1073740800)))
def word91 : Sig := BitVec.ofNat 300 (15778006905665550+2^60*(15778006905665550+2^60*(1098452580366+2^60*1073740800)))
def word92 : Sig := BitVec.ofNat 300 (15778006905665550+2^60*(15778006905665550+2^60*(1124800409909262+2^60*1073740800)))
def word93 : Sig := BitVec.ofNat 300 (15778006905665550+2^60*(15778006905665550+2^60*(1151795604714698766+2^60*1073740800)))
def word94 : Sig := BitVec.ofNat 300 (105938046366611550+2^60*(105938046366611550+2^60*(1151795604798666846+2^60*1073740800)))
def word95 : Sig := BitVec.ofNat 300 (322322141072881950+2^60*(322322141072881950+2^60*(1151795605000190238+2^60*1073740800)))
def word96 : Sig := BitVec.ofNat 300 (376418164749449550+2^60*(376418164749449550+2^60*(1151795605050571086+2^60*1073740800)))
def word97 : Sig := BitVec.ofNat 300 (389942170668591450+2^60*(389942170668591450+2^60*(1151795605063166298+2^60*1073740800)))
def word98 : Sig := BitVec.ofNat 300 (392196171655115100+2^60*(392196171655115100+2^60*(1151795605065265500+2^60*1073740800)))
def word99 : Sig := BitVec.ofNat 300 (394450172641638750+2^60*(394450172641638750+2^60*(1151795605067364702+2^60*1073740800)))
def word100 : Sig := BitVec.ofNat 300 (394450172641638750+2^60*(394450172641638750+2^60*(1151796703505250654+2^60*1073740800)))
def word101 : Sig := BitVec.ofNat 300 (394450172641638750+2^60*(394450172641638750+2^60*(1152920405462579550+2^60*1073740800)))
def word102 : Sig := BitVec.ofNat 300 (15778006905665550+2^60*(15778006905665550+2^60*(14694414+2^60*1073741823)))
def word103 : Sig := BitVec.ofNat 300 (757344331471946400+2^60*(757344331471946400+2^60*(705331872+2^60*1073741823)))
def word104 : Sig := BitVec.ofNat 300 (773122338377611950+2^60*(773122338377611950+2^60*(720026286+2^60*1073741823)))
def word105 : Sig := BitVec.ofNat 300 (394450172641638750+2^60*(394450172641638750+2^60*(1151795605067364702+2^60*1073741823)))
def word106 : Sig := BitVec.ofNat 300 (1151794504113585150+2^60*(1151794504113585150+2^60*(1151795605772696574+2^60*1073741823)))
def word107 : Sig := BitVec.ofNat 300 (15778006905665550+2^60*(15778006905665550+2^60*(1152921503547799566+2^60*1073741823)))
def word108 : Sig := BitVec.ofNat 300 (394450172641638750+2^60*(394450172641638750+2^60*(1152921503900465502+2^60*1073741823)))
def word109 : Sig := BitVec.ofNat 300 (0+2^60*(0+2^60*(0+2^60*1098437885952)))
def word110 : Sig := BitVec.ofNat 300 (387688169682067800+2^60*(387688169682067800+2^60*(1151795605061067096+2^60*1098437885952)))
def word111 : Sig := BitVec.ofNat 300 (757344331471946400+2^60*(757344331471946400+2^60*(705331872+2^60*1099510580223)))
def word112 : Sig := BitVec.ofNat 300 (15778006905665550+2^60*(15778006905665550+2^60*(14694414+2^60*1099511626752)))
def word113 : Sig := BitVec.ofNat 300 (394450172641638750+2^60*(394450172641638750+2^60*(1151795605067364702+2^60*1099511626752)))
def word114 : Sig := BitVec.ofNat 300 (0+2^60*(0+2^60*(0+2^60*1124800395214848)))
def word115 : Sig := BitVec.ofNat 300 (54096023676567600+2^60*(54096023676567600+2^60*(50380848+2^60*1125898833100800)))
def word116 : Sig := BitVec.ofNat 300 (0+2^60*(0+2^60*(0+2^60*1151795604700004352)))
def word117 : Sig := BitVec.ofNat 300 (54096023676567600+2^60*(54096023676567600+2^60*(50380848+2^60*1151796703137890304)))
def word118 : Sig := BitVec.ofNat 300 (54096023676567600+2^60*(54096023676567600+2^60*(50380848+2^60*1152920405095219200)))
def word119 : Sig := BitVec.ofNat 300 (69874030582233150+2^60*(69874030582233150+2^60*(1152921503598180414+2^60*1152920406167913471)))
def word120 : Sig := BitVec.ofNat 300 (18032007892189200+2^60*(18032007892189200+2^60*(16793616+2^60*1152921503533105152)))
def word121 : Sig := BitVec.ofNat 300 (36064015784378400+2^60*(36064015784378400+2^60*(33587232+2^60*1152921503533105152)))
def word122 : Sig := BitVec.ofNat 300 (54096023676567600+2^60*(54096023676567600+2^60*(50380848+2^60*1152921503533105152)))
def word123 : Sig := BitVec.ofNat 300 (423752185466446200+2^60*(423752185466446200+2^60*(1151795605094654328+2^60*1152921503533105152)))
def word124 : Sig := BitVec.ofNat 300 (775376339364135600+2^60*(775376339364135600+2^60*(722125488+2^60*1152921504605799423)))
def word125 : Sig := BitVec.ofNat 300 (69874030582233150+2^60*(69874030582233150+2^60*(65075262+2^60*1152921504606845952)))
def word126 : Sig := BitVec.ofNat 300 (430514188426017150+2^60*(430514188426017150+2^60*(1151795605100951934+2^60*1152921504606845952)))
def word127 : Sig := BitVec.ofNat 300 (0+2^60*(0+2^60*(0+2^60*(0+2^60*1023))))
def word128 : Sig := BitVec.ofNat 300 (387688169682067800+2^60*(387688169682067800+2^60*(1151795605061067096+2^60*(0+2^60*1023))))
def word129 : Sig := BitVec.ofNat 300 (757344331471946400+2^60*(757344331471946400+2^60*(705331872+2^60*(1072694271+2^60*1023))))
def word130 : Sig := BitVec.ofNat 300 (15778006905665550+2^60*(15778006905665550+2^60*(14694414+2^60*(1073740800+2^60*1023))))
def word131 : Sig := BitVec.ofNat 300 (394450172641638750+2^60*(394450172641638750+2^60*(1151795605067364702+2^60*(1073740800+2^60*1023))))
def word132 : Sig := BitVec.ofNat 300 (0+2^60*(0+2^60*(0+2^60*(0+2^60*1047552))))
def word133 : Sig := BitVec.ofNat 300 (2254000986523650+2^60*(2254000986523650+2^60*(1098439985154+2^60*(1124800395214848+2^60*1047552))))
def word134 : Sig := BitVec.ofNat 300 (216384094706270400+2^60*(216384094706270400+2^60*(201523392+2^60*(0+2^60*1048575))))
def word135 : Sig := BitVec.ofNat 300 (0+2^60*(0+2^60*(0+2^60*(0+2^60*1072693248))))
def word136 : Sig := BitVec.ofNat 300 (4508001973047300+2^60*(4508001973047300+2^60*(1124800399413252+2^60*(1151795604700004352+2^60*1072693248))))
def word137 : Sig := BitVec.ofNat 300 (216384094706270400+2^60*(216384094706270400+2^60*(201523392+2^60*(0+2^60*1072694271))))
def word138 : Sig := BitVec.ofNat 300 (216384094706270400+2^60*(216384094706270400+2^60*(201523392+2^60*(0+2^60*1073740800))))
def word139 : Sig := BitVec.ofNat 300 (232162101611935950+2^60*(232162101611935950+2^60*(1152921503749322958+2^60*(1072694271+2^60*1073740800))))
def word140 : Sig := BitVec.ofNat 300 (6762002959570950+2^60*(6762002959570950+2^60*(1125898839398406+2^60*(1152920405095219200+2^60*1073740800))))
def word141 : Sig := BitVec.ofNat 300 (105938046366611550+2^60*(105938046366611550+2^60*(1152921503631767646+2^60*(1152920405095219200+2^60*1073740800))))
def word142 : Sig := BitVec.ofNat 300 (270480118382838000+2^60*(270480118382838000+2^60*(1152921503785009392+2^60*(1152920405095220223+2^60*1073740800))))
def word143 : Sig := BitVec.ofNat 300 (187082081881462950+2^60*(187082081881462950+2^60*(1125899007334566+2^60*(1152920406167913471+2^60*1073740800))))
def word144 : Sig := BitVec.ofNat 300 (286258125288503550+2^60*(286258125288503550+2^60*(1152921503799703806+2^60*(1152920406167913471+2^60*1073740800))))
def word145 : Sig := BitVec.ofNat 300 (574770251563530750+2^60*(574770251563530750+2^60*(1152921504068401662+2^60*(1152920406167913471+2^60*1073740800))))
def word146 : Sig := BitVec.ofNat 300 (863282377838557950+2^60*(863282377838557950+2^60*(1152921504337099518+2^60*(1152920406167913471+2^60*1073740800))))
def word147 : Sig := BitVec.ofNat 300 (286258125288503550+2^60*(286258125288503550+2^60*(1152921503799703806+2^60*(1152921504605799423+2^60*1073740800))))
def word148 : Sig := BitVec.ofNat 300 (72128031568756800+2^60*(72128031568756800+2^60*(67174464+2^60*(0+2^60*1073741823))))
def word149 : Sig := BitVec.ofNat 300 (144256063137513600+2^60*(144256063137513600+2^60*(134348928+2^60*(0+2^60*1073741823))))
def word150 : Sig := BitVec.ofNat 300 (216384094706270400+2^60*(216384094706270400+2^60*(201523392+2^60*(0+2^60*1073741823))))
def word151 : Sig := BitVec.ofNat 300 (531944232819581400+2^60*(531944232819581400+2^60*(1151795605195416024+2^60*(0+2^60*1073741823))))
def word152 : Sig := BitVec.ofNat 300 (829472363040703200+2^60*(829472363040703200+2^60*(772506336+2^60*(1072694271+2^60*1073741823))))
def word153 : Sig := BitVec.ofNat 300 (232162101611935950+2^60*(232162101611935950+2^60*(216217806+2^60*(1073740800+2^60*1073741823))))
def word154 : Sig := BitVec.ofNat 300 (538706235779152350+2^60*(538706235779152350+2^60*(1151795605201713630+2^60*(1073740800+2^60*1073741823))))
def word155 : Sig := BitVec.ofNat 300 (286258125288503550+2^60*(286258125288503550+2^60*(1152921503799703806+2^60*(1152920406167913471+2^60*1073741823))))
def word156 : Sig := BitVec.ofNat 300 (270480118382838000+2^60*(270480118382838000+2^60*(251904240+2^60*(1152921503533105152+2^60*1073741823))))
def word157 : Sig := BitVec.ofNat 300 (286258125288503550+2^60*(286258125288503550+2^60*(266598654+2^60*(1152921504606845952+2^60*1073741823))))
def word158 : Sig := BitVec.ofNat 300 (0+2^60*(0+2^60*(0+2^60*(0+2^60*1098437885952))))
def word159 : Sig := BitVec.ofNat 300 (387688169682067800+2^60*(387688169682067800+2^60*(1151795605061067096+2^60*(0+2^60*1098437885952))))
def word160 : Sig := BitVec.ofNat 300 (757344331471946400+2^60*(757344331471946400+2^60*(705331872+2^60*(1072694271+2^60*1098437885952))))
def word161 : Sig := BitVec.ofNat 300 (15778006905665550+2^60*(15778006905665550+2^60*(14694414+2^60*(1073740800+2^60*1098437885952))))
def word162 : Sig := BitVec.ofNat 300 (394450172641638750+2^60*(394450172641638750+2^60*(1151795605067364702+2^60*(1073740800+2^60*1098437885952))))
def word163 : Sig := BitVec.ofNat 300 (1136016497207919600+2^60*(1136016497207919600+2^60*(1057997808+2^60*(1098437885952+2^60*1098437886975))))
def word164 : Sig := BitVec.ofNat 300 (0+2^60*(0+2^60*(0+2^60*(1098438933504+2^60*1098437886975))))
def word165 : Sig := BitVec.ofNat 300 (387688169682067800+2^60*(387688169682067800+2^60*(361062744+2^60*(1098438933504+2^60*1098437886975))))
def word166 : Sig := BitVec.ofNat 300 (1151794504113585150+2^60*(1151794504113585150+2^60*(1072692222+2^60*(1098438933504+2^60*1098437886975))))
def word167 : Sig := BitVec.ofNat 300 (387688169682067800+2^60*(387688169682067800+2^60*(1151795605061067096+2^60*(1098438933504+2^60*1098437886975))))
def word168 : Sig := BitVec.ofNat 300 (1136016497207919600+2^60*(1136016497207919600+2^60*(1057997808+2^60*(1099510579200+2^60*1098437886975))))
def word169 : Sig := BitVec.ofNat 300 (15778006905665550+2^60*(15778006905665550+2^60*(14694414+2^60*(1099511626752+2^60*1098437886975))))
def word170 : Sig := BitVec.ofNat 300 (394450172641638750+2^60*(394450172641638750+2^60*(367360350+2^60*(1099511626752+2^60*1098437886975))))
def word171 : Sig := BitVec.ofNat 300 (757344331471946400+2^60*(757344331471946400+2^60*(705331872+2^60*(1099511626752+2^60*1098437886975))))
def word172 : Sig := BitVec.ofNat 300 (1136016497207919600+2^60*(1136016497207919600+2^60*(1057997808+2^60*(1099511626752+2^60*1098437886975))))
def word173 : Sig := BitVec.ofNat 300 (1145032501154014200+2^60*(1145032501154014200+2^60*(1066394616+2^60*(1099511626752+2^60*1098437886975))))
def word174 : Sig := BitVec.ofNat 300 (1147286502140537850+2^60*(1147286502140537850+2^60*(1068493818+2^60*(1099511626752+2^60*1098437886975))))
def word175 : Sig := BitVec.ofNat 300 (1149540503127061500+2^60*(1149540503127061500+2^60*(1070593020+2^60*(1099511626752+2^60*1098437886975))))
def word176 : Sig := BitVec.ofNat 300 (1151794504113585150+2^60*(1151794504113585150+2^60*(1072692222+2^60*(1099511626752+2^60*1098437886975))))
def word177 : Sig := BitVec.ofNat 300 (394450172641638750+2^60*(394450172641638750+2^60*(1151795605067364702+2^60*(1099511626752+2^60*1098437886975))))
def word178 : Sig := BitVec.ofNat 300 (757344331471946400+2^60*(757344331471946400+2^60*(705331872+2^60*(1099511627775+2^60*1098437886975))))
def word179 : Sig := BitVec.ofNat 300 (0+2^60*(0+2^60*(0+2^60*(0+2^60*1124800395214848))))
def word180 : Sig := BitVec.ofNat 300 (2254000986523650+2^60*(2254000986523650+2^60*(1098439985154+2^60*(1124800395214848+2^60*1124800395214848))))
def word181 : Sig := BitVec.ofNat 300 (2254000986523650+2^60*(2254000986523650+2^60*(1098439985154+2^60*(0+2^60*1124800396262400))))
def word182 : Sig := BitVec.ofNat 300 (2254000986523650+2^60*(2254000986523650+2^60*(2099202+2^60*(1124800395214848+2^60*1124800396262400))))
def word183 : Sig := BitVec.ofNat 300 (0+2^60*(0+2^60*(1098437885952+2^60*(1124800395214848+2^60*1124800396262400))))
def word184 : Sig := BitVec.ofNat 300 (2254000986523650+2^60*(2254000986523650+2^60*(1098439985154+2^60*(1124800395214848+2^60*1124800396262400))))
def word185 : Sig := BitVec.ofNat 300 (11270004932618250+2^60*(11270004932618250+2^60*(1098448381962+2^60*(1124800395214848+2^60*1124800396262400))))
def word186 : Sig := BitVec.ofNat 300 (389942170668591450+2^60*(389942170668591450+2^60*(1151796703501052250+2^60*(1124800395214848+2^60*1124800396262400))))
def word187 : Sig := BitVec.ofNat 300 (15778006905665550+2^60*(15778006905665550+2^60*(1098452580366+2^60*(1124800396262400+2^60*1124800396262400))))
def word188 : Sig := BitVec.ofNat 300 (759598332458470050+2^60*(759598332458470050+2^60*(1099145317026+2^60*(1124801467909119+2^60*1124800396262400))))
def word189 : Sig := BitVec.ofNat 300 (1147286502140537850+2^60*(1147286502140537850+2^60*(1151796704206384122+2^60*(1124801467909119+2^60*1124800396262400))))
def word190 : Sig := BitVec.ofNat 300 (15778006905665550+2^60*(15778006905665550+2^60*(1098452580366+2^60*(1124801468955648+2^60*1124800396262400))))
def word191 : Sig := BitVec.ofNat 300 (394450172641638750+2^60*(394450172641638750+2^60*(1151796703505250654+2^60*(1124801468955648+2^60*1124800396262400))))
def word192 : Sig := BitVec.ofNat 300 (56350024663091250+2^60*(56350024663091250+2^60*(1098490366002+2^60*(1152921503533105152+2^60*1124800396262400))))
def word193 : Sig := BitVec.ofNat 300 (6762002959570950+2^60*(6762002959570950+2^60*(1125898839398406+2^60*(1152920405095219200+2^60*1124801468955648))))
def word194 : Sig := BitVec.ofNat 300 (286258125288503550+2^60*(286258125288503550+2^60*(1152921503799703806+2^60*(1152920406167913471+2^60*1124801468955648))))
def word195 : Sig := BitVec.ofNat 300 (1151794504113585150+2^60*(1151794504113585150+2^60*(1152921504605797374+2^60*(1152920406167913471+2^60*1124801468955648))))
def word196 : Sig := BitVec.ofNat 300 (218638095692794050+2^60*(218638095692794050+2^60*(1098641508546+2^60*(1124800395214848+2^60*1124801468956671))))
def word197 : Sig := BitVec.ofNat 300 (865536378825081600+2^60*(865536378825081600+2^60*(806093568+2^60*(0+2^60*1125898833100800))))
def word198 : Sig := BitVec.ofNat 300 (1136016497207919600+2^60*(1136016497207919600+2^60*(1057997808+2^60*(1125898833100800+2^60*1125898834149375))))
def word199 : Sig := BitVec.ofNat 300 (389942170668591450+2^60*(389942170668591450+2^60*(363161946+2^60*(1125898834148352+2^60*1125898834149375))))
def word200 : Sig := BitVec.ofNat 300 (1136016497207919600+2^60*(1136016497207919600+2^60*(1057997808+2^60*(1125899905794048+2^60*1125898834149375))))
def word201 : Sig := BitVec.ofNat 300 (759598332458470050+2^60*(759598332458470050+2^60*(707431074+2^60*(1125899906841600+2^60*1125898834149375))))
def word202 : Sig := BitVec.ofNat 300 (1138270498194443250+2^60*(1138270498194443250+2^60*(1060097010+2^60*(1125899906841600+2^60*1125898834149375))))
def word203 : Sig := BitVec.ofNat 300 (1147286502140537850+2^60*(1147286502140537850+2^60*(1068493818+2^60*(1125899906841600+2^60*1125898834149375))))
def word204 : Sig := BitVec.ofNat 300 (1151794504113585150+2^60*(1151794504113585150+2^60*(1072692222+2^60*(1125899906841600+2^60*1125898834149375))))
def word205 : Sig := BitVec.ofNat 300 (1147286502140537850+2^60*(1147286502140537850+2^60*(1099506379770+2^60*(1125899906841600+2^60*1125898834149375))))
def word206 : Sig := BitVec.ofNat 300 (1147286502140537850+2^60*(1147286502140537850+2^60*(1068493818+2^60*(1152921504606845952+2^60*1125898834149375))))
def word207 : Sig := BitVec.ofNat 300 (1147286502140537850+2^60*(1147286502140537850+2^60*(1068493818+2^60*(1125899906841600+2^60*1125899906842623))))
def word208 : Sig := BitVec.ofNat 300 (1151794504113585150+2^60*(1151794504113585150+2^60*(1072692222+2^60*(1152921504606845952+2^60*1125899906842623))))
def word209 : Sig := BitVec.ofNat 300 (0+2^60*(0+2^60*(0+2^60*(0+2^60*1151795604700004352))))
def word210 : Sig := BitVec.ofNat 300 (4508001973047300+2^60*(4508001973047300+2^60*(1124800399413252+2^60*(1151795604700004352+2^60*1151795604700004352))))
def word211 : Sig := BitVec.ofNat 300 (4508001973047300+2^60*(4508001973047300+2^60*(1124800399413252+2^60*(0+2^60*1151795605772697600))))
def word212 : Sig := BitVec.ofNat 300 (4508001973047300+2^60*(4508001973047300+2^60*(4198404+2^60*(1151795604700004352+2^60*1151795605772697600))))
def word213 : Sig := BitVec.ofNat 300 (0+2^60*(0+2^60*(1124800395214848+2^60*(1151795604700004352+2^60*1151795605772697600))))
def word214 : Sig := BitVec.ofNat 300 (4508001973047300+2^60*(4508001973047300+2^60*(1124800399413252+2^60*(1151795604700004352+2^60*1151795605772697600))))
def word215 : Sig := BitVec.ofNat 300 (13524005919141900+2^60*(13524005919141900+2^60*(1124800407810060+2^60*(1151795604700004352+2^60*1151795605772697600))))
def word216 : Sig := BitVec.ofNat 300 (392196171655115100+2^60*(392196171655115100+2^60*(1152920405460480348+2^60*(1151795604700004352+2^60*1151795605772697600))))
def word217 : Sig := BitVec.ofNat 300 (15778006905665550+2^60*(15778006905665550+2^60*(1124800409909262+2^60*(1151795604701051904+2^60*1151795605772697600))))
def word218 : Sig := BitVec.ofNat 300 (761852333444993700+2^60*(761852333444993700+2^60*(1124801104745124+2^60*(1151795605772698623+2^60*1151795605772697600))))
def word219 : Sig := BitVec.ofNat 300 (1149540503127061500+2^60*(1149540503127061500+2^60*(1152920406165812220+2^60*(1151795605772698623+2^60*1151795605772697600))))
def word220 : Sig := BitVec.ofNat 300 (15778006905665550+2^60*(15778006905665550+2^60*(1124800409909262+2^60*(1151795605773745152+2^60*1151795605772697600))))
def word221 : Sig := BitVec.ofNat 300 (394450172641638750+2^60*(394450172641638750+2^60*(1152920405462579550+2^60*(1151795605773745152+2^60*1151795605772697600))))
def word222 : Sig := BitVec.ofNat 300 (58604025649614900+2^60*(58604025649614900+2^60*(1124800449794100+2^60*(1152921503533105152+2^60*1151795605772697600))))
def word223 : Sig := BitVec.ofNat 300 (6762002959570950+2^60*(6762002959570950+2^60*(1125898839398406+2^60*(1152920405095219200+2^60*1151795605773745152))))
def word224 : Sig := BitVec.ofNat 300 (286258125288503550+2^60*(286258125288503550+2^60*(1152921503799703806+2^60*(1152920406167913471+2^60*1151795605773745152))))
def word225 : Sig := BitVec.ofNat 300 (1151794504113585150+2^60*(1151794504113585150+2^60*(1152921504605797374+2^60*(1152920406167913471+2^60*1151795605773745152))))
def word226 : Sig := BitVec.ofNat 300 (220892096679317700+2^60*(220892096679317700+2^60*(1124800600936644+2^60*(1151795604700004352+2^60*1151795605773746175))))
def word227 : Sig := BitVec.ofNat 300 (865536378825081600+2^60*(865536378825081600+2^60*(806093568+2^60*(0+2^60*1151796703137890304))))
def word228 : Sig := BitVec.ofNat 300 (1136016497207919600+2^60*(1136016497207919600+2^60*(1057997808+2^60*(1151796703137890304+2^60*1151796704210584575))))
def word229 : Sig := BitVec.ofNat 300 (392196171655115100+2^60*(392196171655115100+2^60*(365261148+2^60*(1151796703138937856+2^60*1151796704210584575))))
def word230 : Sig := BitVec.ofNat 300 (1136016497207919600+2^60*(1136016497207919600+2^60*(1057997808+2^60*(1151796704210583552+2^60*1151796704210584575))))
def word231 : Sig := BitVec.ofNat 300 (761852333444993700+2^60*(761852333444993700+2^60*(709530276+2^60*(1151796704211631104+2^60*1151796704210584575))))
def word232 : Sig := BitVec.ofNat 300 (1140524499180966900+2^60*(1140524499180966900+2^60*(1062196212+2^60*(1151796704211631104+2^60*1151796704210584575))))
def word233 : Sig := BitVec.ofNat 300 (1149540503127061500+2^60*(1149540503127061500+2^60*(1070593020+2^60*(1151796704211631104+2^60*1151796704210584575))))
def word234 : Sig := BitVec.ofNat 300 (1151794504113585150+2^60*(1151794504113585150+2^60*(1072692222+2^60*(1151796704211631104+2^60*1151796704210584575))))
def word235 : Sig := BitVec.ofNat 300 (1149540503127061500+2^60*(1149540503127061500+2^60*(1124801465807868+2^60*(1151796704211631104+2^60*1151796704210584575))))
def word236 : Sig := BitVec.ofNat 300 (1149540503127061500+2^60*(1149540503127061500+2^60*(1070593020+2^60*(1152921504606845952+2^60*1151796704210584575))))
def word237 : Sig := BitVec.ofNat 300 (1149540503127061500+2^60*(1149540503127061500+2^60*(1070593020+2^60*(1151796704211631104+2^60*1151796704211632127))))
def word238 : Sig := BitVec.ofNat 300 (1151794504113585150+2^60*(1151794504113585150+2^60*(1072692222+2^60*(1152921504606845952+2^60*1151796704211632127))))
def word239 : Sig := BitVec.ofNat 300 (865536378825081600+2^60*(865536378825081600+2^60*(806093568+2^60*(0+2^60*1152920405095219200))))
def word240 : Sig := BitVec.ofNat 300 (881314385730747150+2^60*(881314385730747150+2^60*(1152921504353893134+2^60*(1072694271+2^60*1152920405095219200))))
def word241 : Sig := BitVec.ofNat 300 (6762002959570950+2^60*(6762002959570950+2^60*(1125898839398406+2^60*(1152920405095219200+2^60*1152920405095219200))))
def word242 : Sig := BitVec.ofNat 300 (322322141072881950+2^60*(322322141072881950+2^60*(1152921503833291038+2^60*(1152920405095219200+2^60*1152920405095219200))))
def word243 : Sig := BitVec.ofNat 300 (919632402501649200+2^60*(919632402501649200+2^60*(1152921504389579568+2^60*(1152920405095220223+2^60*1152920405095219200))))
def word244 : Sig := BitVec.ofNat 300 (619850271294003750+2^60*(619850271294003750+2^60*(1125899410381350+2^60*(1152920406167913471+2^60*1152920405095219200))))
def word245 : Sig := BitVec.ofNat 300 (935410409407314750+2^60*(935410409407314750+2^60*(1152921504404273982+2^60*(1152920406167913471+2^60*1152920405095219200))))
def word246 : Sig := BitVec.ofNat 300 (1007538440976071550+2^60*(1007538440976071550+2^60*(1152921504471448446+2^60*(1152920406167913471+2^60*1152920405095219200))))
def word247 : Sig := BitVec.ofNat 300 (1079666472544828350+2^60*(1079666472544828350+2^60*(1152921504538622910+2^60*(1152920406167913471+2^60*1152920405095219200))))
def word248 : Sig := BitVec.ofNat 300 (935410409407314750+2^60*(935410409407314750+2^60*(1152921504404273982+2^60*(1152921504605799423+2^60*1152920405095219200))))
def word249 : Sig := BitVec.ofNat 300 (6762002959570950+2^60*(6762002959570950+2^60*(1125898839398406+2^60*(1152920405095219200+2^60*1152920405096266752))))
def word250 : Sig := BitVec.ofNat 300 (935410409407314750+2^60*(935410409407314750+2^60*(1152921504404273982+2^60*(1152920406167913471+2^60*1152920405096266752))))
def word251 : Sig := BitVec.ofNat 300 (1151794504113585150+2^60*(1151794504113585150+2^60*(1152921504605797374+2^60*(1152920406167913471+2^60*1152920405096266752))))
def word252 : Sig := BitVec.ofNat 300 (6762002959570950+2^60*(6762002959570950+2^60*(1125898839398406+2^60*(1152920405095219200+2^60*1152920406167912448))))
def word253 : Sig := BitVec.ofNat 300 (935410409407314750+2^60*(935410409407314750+2^60*(1152921504404273982+2^60*(1152920406167913471+2^60*1152920406167912448))))
def word254 : Sig := BitVec.ofNat 300 (1151794504113585150+2^60*(1151794504113585150+2^60*(1152921504605797374+2^60*(1152920406167913471+2^60*1152920406167912448))))
def word255 : Sig := BitVec.ofNat 300 (6762002959570950+2^60*(6762002959570950+2^60*(1125898839398406+2^60*(0+2^60*1152920406168960000))))
def word256 : Sig := BitVec.ofNat 300 (376418164749449550+2^60*(376418164749449550+2^60*(1152921503883671886+2^60*(0+2^60*1152920406168960000))))
def word257 : Sig := BitVec.ofNat 300 (1081920473531352000+2^60*(1081920473531352000+2^60*(1152921504540722112+2^60*(1023+2^60*1152920406168960000))))
def word258 : Sig := BitVec.ofNat 300 (728042318647138950+2^60*(728042318647138950+2^60*(1125899511143046+2^60*(1072694271+2^60*1152920406168960000))))
def word259 : Sig := BitVec.ofNat 300 (1097698480437017550+2^60*(1097698480437017550+2^60*(1152921504555416526+2^60*(1072694271+2^60*1152920406168960000))))
def word260 : Sig := BitVec.ofNat 300 (1115730488329206750+2^60*(1115730488329206750+2^60*(1152921504572210142+2^60*(1072694271+2^60*1152920406168960000))))
def word261 : Sig := BitVec.ofNat 300 (1133762496221395950+2^60*(1133762496221395950+2^60*(1152921504589003758+2^60*(1072694271+2^60*1152920406168960000))))
def word262 : Sig := BitVec.ofNat 300 (6762002959570950+2^60*(6762002959570950+2^60*(1125898839398406+2^60*(1124800395214848+2^60*1152920406168960000))))
def word263 : Sig := BitVec.ofNat 300 (1097698480437017550+2^60*(1097698480437017550+2^60*(1152921504555416526+2^60*(1124801467909119+2^60*1152920406168960000))))
def word264 : Sig := BitVec.ofNat 300 (1151794504113585150+2^60*(1151794504113585150+2^60*(1152921504605797374+2^60*(1124801467909119+2^60*1152920406168960000))))
def word265 : Sig := BitVec.ofNat 300 (6762002959570950+2^60*(6762002959570950+2^60*(1125898839398406+2^60*(1151795604700004352+2^60*1152920406168960000))))
def word266 : Sig := BitVec.ofNat 300 (1097698480437017550+2^60*(1097698480437017550+2^60*(1152921504555416526+2^60*(1151795605772698623+2^60*1152920406168960000))))
def word267 : Sig := BitVec.ofNat 300 (1151794504113585150+2^60*(1151794504113585150+2^60*(1152921504605797374+2^60*(1151795605772698623+2^60*1152920406168960000))))
def word268 : Sig := BitVec.ofNat 300 (6762002959570950+2^60*(6762002959570950+2^60*(6297606+2^60*(1152920405095219200+2^60*1152920406168960000))))
def word269 : Sig := BitVec.ofNat 300 (394450172641638750+2^60*(394450172641638750+2^60*(367360350+2^60*(1152920405095219200+2^60*1152920406168960000))))
def word270 : Sig := BitVec.ofNat 300 (757344331471946400+2^60*(757344331471946400+2^60*(705331872+2^60*(1152920405095219200+2^60*1152920406168960000))))
def word271 : Sig := BitVec.ofNat 300 (1136016497207919600+2^60*(1136016497207919600+2^60*(1057997808+2^60*(1152920405095219200+2^60*1152920406168960000))))
def word272 : Sig := BitVec.ofNat 300 (6762002959570950+2^60*(6762002959570950+2^60*(1098444183558+2^60*(1152920405095219200+2^60*1152920406168960000))))
def word273 : Sig := BitVec.ofNat 300 (6762002959570950+2^60*(6762002959570950+2^60*(1124800401512454+2^60*(1152920405095219200+2^60*1152920406168960000))))
def word274 : Sig := BitVec.ofNat 300 (0+2^60*(0+2^60*(1125898833100800+2^60*(1152920405095219200+2^60*1152920406168960000))))
def word275 : Sig := BitVec.ofNat 300 (2254000986523650+2^60*(2254000986523650+2^60*(1125898835200002+2^60*(1152920405095219200+2^60*1152920406168960000))))
def word276 : Sig := BitVec.ofNat 300 (4508001973047300+2^60*(4508001973047300+2^60*(1125898837299204+2^60*(1152920405095219200+2^60*1152920406168960000))))
def word277 : Sig := BitVec.ofNat 300 (6762002959570950+2^60*(6762002959570950+2^60*(1125898839398406+2^60*(1152920405095219200+2^60*1152920406168960000))))
def word278 : Sig := BitVec.ofNat 300 (15778006905665550+2^60*(15778006905665550+2^60*(1125898847795214+2^60*(1152920405095219200+2^60*1152920406168960000))))
def word279 : Sig := BitVec.ofNat 300 (394450172641638750+2^60*(394450172641638750+2^60*(1152921503900465502+2^60*(1152920405095219200+2^60*1152920406168960000))))
def word280 : Sig := BitVec.ofNat 300 (430514188426017150+2^60*(430514188426017150+2^60*(1152921503934052734+2^60*(1152920405095219200+2^60*1152920406168960000))))
def word281 : Sig := BitVec.ofNat 300 (538706235779152350+2^60*(538706235779152350+2^60*(1152921504034814430+2^60*(1152920405095219200+2^60*1152920406168960000))))
def word282 : Sig := BitVec.ofNat 300 (971474425191693150+2^60*(971474425191693150+2^60*(1152921504437861214+2^60*(1152920405095219200+2^60*1152920406168960000))))
def word283 : Sig := BitVec.ofNat 300 (757344331471946400+2^60*(757344331471946400+2^60*(1125899538432672+2^60*(1152920405095220223+2^60*1152920406168960000))))
def word284 : Sig := BitVec.ofNat 300 (394450172641638750+2^60*(394450172641638750+2^60*(1152921503900465502+2^60*(1152920405095220223+2^60*1152920406168960000))))
def word285 : Sig := BitVec.ofNat 300 (757344331471946400+2^60*(757344331471946400+2^60*(1152921504238437024+2^60*(1152920405095220223+2^60*1152920406168960000))))
def word286 : Sig := BitVec.ofNat 300 (1136016497207919600+2^60*(1136016497207919600+2^60*(1152921504591102960+2^60*(1152920405095220223+2^60*1152920406168960000))))
def word287 : Sig := BitVec.ofNat 300 (1145032501154014200+2^60*(1145032501154014200+2^60*(1152921504599499768+2^60*(1152920405095220223+2^60*1152920406168960000))))
def word288 : Sig := BitVec.ofNat 300 (1151794504113585150+2^60*(1151794504113585150+2^60*(1152921504605797374+2^60*(1152920405095220223+2^60*1152920406168960000))))
def word289 : Sig := BitVec.ofNat 300 (15778006905665550+2^60*(15778006905665550+2^60*(1125898847795214+2^60*(1152920405096266752+2^60*1152920406168960000))))
def word290 : Sig := BitVec.ofNat 300 (394450172641638750+2^60*(394450172641638750+2^60*(1152921503900465502+2^60*(1152920405096266752+2^60*1152920406168960000))))
def word291 : Sig := BitVec.ofNat 300 (764106334431517350+2^60*(764106334431517350+2^60*(711629478+2^60*(1152920406167912448+2^60*1152920406168960000))))
def word292 : Sig := BitVec.ofNat 300 (1151794504113585150+2^60*(1151794504113585150+2^60*(1072692222+2^60*(1152920406167912448+2^60*1152920406168960000))))
def word293 : Sig := BitVec.ofNat 300 (0+2^60*(0+2^60*(1125898833100800+2^60*(1152920406167912448+2^60*1152920406168960000))))
def word294 : Sig := BitVec.ofNat 300 (394450172641638750+2^60*(394450172641638750+2^60*(1152921503900465502+2^60*(1152920406167912448+2^60*1152920406168960000))))
def word295 : Sig := BitVec.ofNat 300 (1151794504113585150+2^60*(1151794504113585150+2^60*(1152921504605797374+2^60*(1152920406167912448+2^60*1152920406168960000))))
def word296 : Sig := BitVec.ofNat 300 (764106334431517350+2^60*(764106334431517350+2^60*(1125899544730278+2^60*(1152920406167913471+2^60*1152920406168960000))))
def word297 : Sig := BitVec.ofNat 300 (773122338377611950+2^60*(773122338377611950+2^60*(1125899553127086+2^60*(1152920406167913471+2^60*1152920406168960000))))
def word298 : Sig := BitVec.ofNat 300 (782138342323706550+2^60*(782138342323706550+2^60*(1125899561523894+2^60*(1152920406167913471+2^60*1152920406168960000))))
def word299 : Sig := BitVec.ofNat 300 (836234366000274150+2^60*(836234366000274150+2^60*(1125899611904742+2^60*(1152920406167913471+2^60*1152920406168960000))))
def word300 : Sig := BitVec.ofNat 300 (1052618460706544550+2^60*(1052618460706544550+2^60*(1125899813428134+2^60*(1152920406167913471+2^60*1152920406168960000))))
def word301 : Sig := BitVec.ofNat 300 (1151794504113585150+2^60*(1151794504113585150+2^60*(1125899905793022+2^60*(1152920406167913471+2^60*1152920406168960000))))
def word302 : Sig := BitVec.ofNat 300 (574770251563530750+2^60*(574770251563530750+2^60*(1152921504068401662+2^60*(1152920406167913471+2^60*1152920406168960000))))
def word303 : Sig := BitVec.ofNat 300 (764106334431517350+2^60*(764106334431517350+2^60*(1152921504244734630+2^60*(1152920406167913471+2^60*1152920406168960000))))
def word304 : Sig := BitVec.ofNat 300 (863282377838557950+2^60*(863282377838557950+2^60*(1152921504337099518+2^60*(1152920406167913471+2^60*1152920406168960000))))
def word305 : Sig := BitVec.ofNat 300 (1007538440976071550+2^60*(1007538440976071550+2^60*(1152921504471448446+2^60*(1152920406167913471+2^60*1152920406168960000))))
def word306 : Sig := BitVec.ofNat 300 (1079666472544828350+2^60*(1079666472544828350+2^60*(1152921504538622910+2^60*(1152920406167913471+2^60*1152920406168960000))))
def word307 : Sig := BitVec.ofNat 300 (1115730488329206750+2^60*(1115730488329206750+2^60*(1152921504572210142+2^60*(1152920406167913471+2^60*1152920406168960000))))
def word308 : Sig := BitVec.ofNat 300 (1133762496221395950+2^60*(1133762496221395950+2^60*(1152921504589003758+2^60*(1152920406167913471+2^60*1152920406168960000))))
def word309 : Sig := BitVec.ofNat 300 (1142778500167490550+2^60*(1142778500167490550+2^60*(1152921504597400566+2^60*(1152920406167913471+2^60*1152920406168960000))))
def word310 : Sig := BitVec.ofNat 300 (1151794504113585150+2^60*(1151794504113585150+2^60*(1152921504605797374+2^60*(1152920406167913471+2^60*1152920406168960000))))
def word311 : Sig := BitVec.ofNat 300 (15778006905665550+2^60*(15778006905665550+2^60*(1125898847795214+2^60*(1152920406168960000+2^60*1152920406168960000))))
def word312 : Sig := BitVec.ofNat 300 (764106334431517350+2^60*(764106334431517350+2^60*(1125899544730278+2^60*(1152920406168961023+2^60*1152920406168960000))))
def word313 : Sig := BitVec.ofNat 300 (773122338377611950+2^60*(773122338377611950+2^60*(1125899553127086+2^60*(1152920406168961023+2^60*1152920406168960000))))
def word314 : Sig := BitVec.ofNat 300 (1151794504113585150+2^60*(1151794504113585150+2^60*(1152921504605797374+2^60*(1152920406168961023+2^60*1152920406168960000))))
def word315 : Sig := BitVec.ofNat 300 (60858026636138550+2^60*(60858026636138550+2^60*(1125898889779254+2^60*(1152921503533105152+2^60*1152920406168960000))))
def word316 : Sig := BitVec.ofNat 300 (394450172641638750+2^60*(394450172641638750+2^60*(1152921503900465502+2^60*(1152921503533105152+2^60*1152920406168960000))))
def word317 : Sig := BitVec.ofNat 300 (430514188426017150+2^60*(430514188426017150+2^60*(1152921503934052734+2^60*(1152921503533105152+2^60*1152920406168960000))))
def word318 : Sig := BitVec.ofNat 300 (757344331471946400+2^60*(757344331471946400+2^60*(1125899538432672+2^60*(1152921503533106175+2^60*1152920406168960000))))
def word319 : Sig := BitVec.ofNat 300 (1136016497207919600+2^60*(1136016497207919600+2^60*(1152921504591102960+2^60*(1152921503533106175+2^60*1152920406168960000))))
def word320 : Sig := BitVec.ofNat 300 (764106334431517350+2^60*(764106334431517350+2^60*(1125899544730278+2^60*(1152921504605799423+2^60*1152920406168960000))))
def word321 : Sig := BitVec.ofNat 300 (782138342323706550+2^60*(782138342323706550+2^60*(1125899561523894+2^60*(1152921504605799423+2^60*1152920406168960000))))
def word322 : Sig := BitVec.ofNat 300 (1151794504113585150+2^60*(1151794504113585150+2^60*(1152921504605797374+2^60*(1152921504605799423+2^60*1152920406168960000))))
def word323 : Sig := BitVec.ofNat 300 (1097698480437017550+2^60*(1097698480437017550+2^60*(1152921504555416526+2^60*(1072694271+2^60*1152920406168961023))))
def word324 : Sig := BitVec.ofNat 300 (223146097665841350+2^60*(223146097665841350+2^60*(1125899040921798+2^60*(1152920405095219200+2^60*1152920406168961023))))
def word325 : Sig := BitVec.ofNat 300 (394450172641638750+2^60*(394450172641638750+2^60*(1152921503900465502+2^60*(1152920405095219200+2^60*1152920406168961023))))
def word326 : Sig := BitVec.ofNat 300 (538706235779152350+2^60*(538706235779152350+2^60*(1152921504034814430+2^60*(1152920405095219200+2^60*1152920406168961023))))
def word327 : Sig := BitVec.ofNat 300 (757344331471946400+2^60*(757344331471946400+2^60*(1125899538432672+2^60*(1152920405095220223+2^60*1152920406168961023))))
def word328 : Sig := BitVec.ofNat 300 (1136016497207919600+2^60*(1136016497207919600+2^60*(1152921504591102960+2^60*(1152920405095220223+2^60*1152920406168961023))))
def word329 : Sig := BitVec.ofNat 300 (764106334431517350+2^60*(764106334431517350+2^60*(1125899544730278+2^60*(1152920406167913471+2^60*1152920406168961023))))
def word330 : Sig := BitVec.ofNat 300 (836234366000274150+2^60*(836234366000274150+2^60*(1125899611904742+2^60*(1152920406167913471+2^60*1152920406168961023))))
def word331 : Sig := BitVec.ofNat 300 (1151794504113585150+2^60*(1151794504113585150+2^60*(1152921504605797374+2^60*(1152920406167913471+2^60*1152920406168961023))))
def word332 : Sig := BitVec.ofNat 300 (1151794504113585150+2^60*(1151794504113585150+2^60*(1152921504605797374+2^60*(1152921504605799423+2^60*1152920406168961023))))
def word333 : Sig := BitVec.ofNat 300 (288512126275027200+2^60*(288512126275027200+2^60*(268697856+2^60*(0+2^60*1152921503533105152))))
def word334 : Sig := BitVec.ofNat 300 (577024252550054400+2^60*(577024252550054400+2^60*(537395712+2^60*(0+2^60*1152921503533105152))))
def word335 : Sig := BitVec.ofNat 300 (865536378825081600+2^60*(865536378825081600+2^60*(806093568+2^60*(0+2^60*1152921503533105152))))
def word336 : Sig := BitVec.ofNat 300 (964712422232122200+2^60*(964712422232122200+2^60*(1151795605598462808+2^60*(0+2^60*1152921503533105152))))
def word337 : Sig := BitVec.ofNat 300 (1045856457746973600+2^60*(1045856457746973600+2^60*(974029728+2^60*(1072694271+2^60*1152921503533105152))))
def word338 : Sig := BitVec.ofNat 300 (881314385730747150+2^60*(881314385730747150+2^60*(820787982+2^60*(1073740800+2^60*1152921503533105152))))
def word339 : Sig := BitVec.ofNat 300 (971474425191693150+2^60*(971474425191693150+2^60*(1151795605604760414+2^60*(1073740800+2^60*1152921503533105152))))
def word340 : Sig := BitVec.ofNat 300 (935410409407314750+2^60*(935410409407314750+2^60*(1152921504404273982+2^60*(1152920406167913471+2^60*1152921503533105152))))
def word341 : Sig := BitVec.ofNat 300 (919632402501649200+2^60*(919632402501649200+2^60*(856474416+2^60*(1152921503533105152+2^60*1152921503533105152))))
def word342 : Sig := BitVec.ofNat 300 (935410409407314750+2^60*(935410409407314750+2^60*(871168830+2^60*(1152921504606845952+2^60*1152921503533105152))))
def word343 : Sig := BitVec.ofNat 300 (867790379811605250+2^60*(867790379811605250+2^60*(1099246078722+2^60*(1124800395214848+2^60*1152921503534152704))))
def word344 : Sig := BitVec.ofNat 300 (1147286502140537850+2^60*(1147286502140537850+2^60*(1068493818+2^60*(1125899906841600+2^60*1152921503534153727))))
def word345 : Sig := BitVec.ofNat 300 (1151794504113585150+2^60*(1151794504113585150+2^60*(1072692222+2^60*(1152921504606845952+2^60*1152921503534153727))))
def word346 : Sig := BitVec.ofNat 300 (870044380798128900+2^60*(870044380798128900+2^60*(1124801205506820+2^60*(1151795604700004352+2^60*1152921504605798400))))
def word347 : Sig := BitVec.ofNat 300 (1149540503127061500+2^60*(1149540503127061500+2^60*(1070593020+2^60*(1151796704211631104+2^60*1152921504605799423))))
def word348 : Sig := BitVec.ofNat 300 (1151794504113585150+2^60*(1151794504113585150+2^60*(1072692222+2^60*(1152921504606845952+2^60*1152921504605799423))))
def word349 : Sig := BitVec.ofNat 300 (1097698480437017550+2^60*(1097698480437017550+2^60*(1152921504555416526+2^60*(1072694271+2^60*1152921504606845952))))
def word350 : Sig := BitVec.ofNat 300 (872298381784652550+2^60*(872298381784652550+2^60*(1125899645491974+2^60*(1152920405095219200+2^60*1152921504606845952))))
def word351 : Sig := BitVec.ofNat 300 (394450172641638750+2^60*(394450172641638750+2^60*(1152921503900465502+2^60*(1152920405095219200+2^60*1152921504606845952))))
def word352 : Sig := BitVec.ofNat 300 (971474425191693150+2^60*(971474425191693150+2^60*(1152921504437861214+2^60*(1152920405095219200+2^60*1152921504606845952))))
def word353 : Sig := BitVec.ofNat 300 (757344331471946400+2^60*(757344331471946400+2^60*(1125899538432672+2^60*(1152920405095220223+2^60*1152921504606845952))))
def word354 : Sig := BitVec.ofNat 300 (1136016497207919600+2^60*(1136016497207919600+2^60*(1152921504591102960+2^60*(1152920405095220223+2^60*1152921504606845952))))
def word355 : Sig := BitVec.ofNat 300 (764106334431517350+2^60*(764106334431517350+2^60*(1125899544730278+2^60*(1152920406167913471+2^60*1152921504606845952))))
def word356 : Sig := BitVec.ofNat 300 (1052618460706544550+2^60*(1052618460706544550+2^60*(1125899813428134+2^60*(1152920406167913471+2^60*1152921504606845952))))
def word357 : Sig := BitVec.ofNat 300 (1151794504113585150+2^60*(1151794504113585150+2^60*(1152921504605797374+2^60*(1152920406167913471+2^60*1152921504606845952))))
def word358 : Sig := BitVec.ofNat 300 (1151794504113585150+2^60*(1151794504113585150+2^60*(1152921504605797374+2^60*(1152921504605799423+2^60*1152921504606845952))))
def word359 : Sig := BitVec.ofNat 300 (1081920473531352000+2^60*(1081920473531352000+2^60*(1007616960+2^60*(0+2^60*1152921504606846975))))
def word360 : Sig := BitVec.ofNat 300 (1097698480437017550+2^60*(1097698480437017550+2^60*(1022311374+2^60*(1073740800+2^60*1152921504606846975))))
def word361 : Sig := BitVec.ofNat 300 (1151794504113585150+2^60*(1151794504113585150+2^60*(1072692222+2^60*(1125899906841600+2^60*1152921504606846975))))
def word362 : Sig := BitVec.ofNat 300 (1151794504113585150+2^60*(1151794504113585150+2^60*(1072692222+2^60*(1151796704211631104+2^60*1152921504606846975))))
def word363 : Sig := BitVec.ofNat 300 (1151794504113585150+2^60*(1151794504113585150+2^60*(1152921504605797374+2^60*(1152920406167913471+2^60*1152921504606846975))))
def word364 : Sig := BitVec.ofNat 300 (757344331471946400+2^60*(757344331471946400+2^60*(705331872+2^60*(1152921503533105152+2^60*1152921504606846975))))
def word365 : Sig := BitVec.ofNat 300 (1136016497207919600+2^60*(1136016497207919600+2^60*(1057997808+2^60*(1152921503533105152+2^60*1152921504606846975))))
def word366 : Sig := BitVec.ofNat 300 (1138270498194443250+2^60*(1138270498194443250+2^60*(1060097010+2^60*(1152921503533105152+2^60*1152921504606846975))))
def word367 : Sig := BitVec.ofNat 300 (1140524499180966900+2^60*(1140524499180966900+2^60*(1062196212+2^60*(1152921503533105152+2^60*1152921504606846975))))
def word368 : Sig := BitVec.ofNat 300 (1145032501154014200+2^60*(1145032501154014200+2^60*(1066394616+2^60*(1152921503533105152+2^60*1152921504606846975))))
def word369 : Sig := BitVec.ofNat 300 (757344331471946400+2^60*(757344331471946400+2^60*(1099143217824+2^60*(1152921503533105152+2^60*1152921504606846975))))
def word370 : Sig := BitVec.ofNat 300 (1136016497207919600+2^60*(1136016497207919600+2^60*(1099495883760+2^60*(1152921503533105152+2^60*1152921504606846975))))
def word371 : Sig := BitVec.ofNat 300 (1138270498194443250+2^60*(1138270498194443250+2^60*(1099497982962+2^60*(1152921503533105152+2^60*1152921504606846975))))
def word372 : Sig := BitVec.ofNat 300 (757344331471946400+2^60*(757344331471946400+2^60*(1124801100546720+2^60*(1152921503533105152+2^60*1152921504606846975))))
def word373 : Sig := BitVec.ofNat 300 (1136016497207919600+2^60*(1136016497207919600+2^60*(1124801453212656+2^60*(1152921503533105152+2^60*1152921504606846975))))
def word374 : Sig := BitVec.ofNat 300 (1140524499180966900+2^60*(1140524499180966900+2^60*(1124801457411060+2^60*(1152921503533105152+2^60*1152921504606846975))))
def word375 : Sig := BitVec.ofNat 300 (1142778500167490550+2^60*(1142778500167490550+2^60*(1125899897396214+2^60*(1152921503533105152+2^60*1152921504606846975))))
def word376 : Sig := BitVec.ofNat 300 (1136016497207919600+2^60*(1136016497207919600+2^60*(1151795605758002160+2^60*(1152921503533105152+2^60*1152921504606846975))))
def word377 : Sig := BitVec.ofNat 300 (1145032501154014200+2^60*(1145032501154014200+2^60*(1151795605766398968+2^60*(1152921503533105152+2^60*1152921504606846975))))
def word378 : Sig := BitVec.ofNat 300 (757344331471946400+2^60*(757344331471946400+2^60*(705331872+2^60*(1152921503533106175+2^60*1152921504606846975))))
def word379 : Sig := BitVec.ofNat 300 (1136016497207919600+2^60*(1136016497207919600+2^60*(1057997808+2^60*(1152921503533106175+2^60*1152921504606846975))))
def word380 : Sig := BitVec.ofNat 300 (757344331471946400+2^60*(757344331471946400+2^60*(1125899538432672+2^60*(1152921503533106175+2^60*1152921504606846975))))
def word381 : Sig := BitVec.ofNat 300 (1136016497207919600+2^60*(1136016497207919600+2^60*(1152921504591102960+2^60*(1152921503533106175+2^60*1152921504606846975))))
def word382 : Sig := BitVec.ofNat 300 (6762002959570950+2^60*(6762002959570950+2^60*(6297606+2^60*(1152921503534152704+2^60*1152921504606846975))))
def word383 : Sig := BitVec.ofNat 300 (15778006905665550+2^60*(15778006905665550+2^60*(14694414+2^60*(1152921503534152704+2^60*1152921504606846975))))
def word384 : Sig := BitVec.ofNat 300 (394450172641638750+2^60*(394450172641638750+2^60*(367360350+2^60*(1152921503534152704+2^60*1152921504606846975))))
def word385 : Sig := BitVec.ofNat 300 (757344331471946400+2^60*(757344331471946400+2^60*(705331872+2^60*(1152921503534152704+2^60*1152921504606846975))))
def word386 : Sig := BitVec.ofNat 300 (1136016497207919600+2^60*(1136016497207919600+2^60*(1057997808+2^60*(1152921503534152704+2^60*1152921504606846975))))
def word387 : Sig := BitVec.ofNat 300 (1151794504113585150+2^60*(1151794504113585150+2^60*(1072692222+2^60*(1152921503534152704+2^60*1152921504606846975))))
def word388 : Sig := BitVec.ofNat 300 (394450172641638750+2^60*(394450172641638750+2^60*(1098805246302+2^60*(1152921503534152704+2^60*1152921504606846975))))
def word389 : Sig := BitVec.ofNat 300 (394450172641638750+2^60*(394450172641638750+2^60*(1124800762575198+2^60*(1152921503534152704+2^60*1152921504606846975))))
def word390 : Sig := BitVec.ofNat 300 (394450172641638750+2^60*(394450172641638750+2^60*(1151795605067364702+2^60*(1152921503534152704+2^60*1152921504606846975))))
def word391 : Sig := BitVec.ofNat 300 (394450172641638750+2^60*(394450172641638750+2^60*(1152921503900465502+2^60*(1152921503534152704+2^60*1152921504606846975))))
def word392 : Sig := BitVec.ofNat 300 (1136016497207919600+2^60*(1136016497207919600+2^60*(1152921504591102960+2^60*(1152921503534153727+2^60*1152921504606846975))))
def word393 : Sig := BitVec.ofNat 300 (1136016497207919600+2^60*(1136016497207919600+2^60*(1057997808+2^60*(1152921504605798400+2^60*1152921504606846975))))
def word394 : Sig := BitVec.ofNat 300 (1151794504113585150+2^60*(1151794504113585150+2^60*(1072692222+2^60*(1152921504605798400+2^60*1152921504606846975))))
def word395 : Sig := BitVec.ofNat 300 (1151794504113585150+2^60*(1151794504113585150+2^60*(1152921504605797374+2^60*(1152921504605799423+2^60*1152921504606846975))))
def word396 : Sig := BitVec.ofNat 300 (764106334431517350+2^60*(764106334431517350+2^60*(711629478+2^60*(1152921504606845952+2^60*1152921504606846975))))
def word397 : Sig := BitVec.ofNat 300 (773122338377611950+2^60*(773122338377611950+2^60*(720026286+2^60*(1152921504606845952+2^60*1152921504606846975))))
def word398 : Sig := BitVec.ofNat 300 (1142778500167490550+2^60*(1142778500167490550+2^60*(1064295414+2^60*(1152921504606845952+2^60*1152921504606846975))))
def word399 : Sig := BitVec.ofNat 300 (1147286502140537850+2^60*(1147286502140537850+2^60*(1068493818+2^60*(1152921504606845952+2^60*1152921504606846975))))
def word400 : Sig := BitVec.ofNat 300 (1149540503127061500+2^60*(1149540503127061500+2^60*(1070593020+2^60*(1152921504606845952+2^60*1152921504606846975))))
def word401 : Sig := BitVec.ofNat 300 (1151794504113585150+2^60*(1151794504113585150+2^60*(1072692222+2^60*(1152921504606845952+2^60*1152921504606846975))))
def word402 : Sig := BitVec.ofNat 300 (764106334431517350+2^60*(764106334431517350+2^60*(1099149515430+2^60*(1152921504606845952+2^60*1152921504606846975))))
def word403 : Sig := BitVec.ofNat 300 (1151794504113585150+2^60*(1151794504113585150+2^60*(1099510578174+2^60*(1152921504606845952+2^60*1152921504606846975))))
def word404 : Sig := BitVec.ofNat 300 (764106334431517350+2^60*(764106334431517350+2^60*(1124801106844326+2^60*(1152921504606845952+2^60*1152921504606846975))))
def word405 : Sig := BitVec.ofNat 300 (1151794504113585150+2^60*(1151794504113585150+2^60*(1124801467907070+2^60*(1152921504606845952+2^60*1152921504606846975))))
def word406 : Sig := BitVec.ofNat 300 (1151794504113585150+2^60*(1151794504113585150+2^60*(1125899905793022+2^60*(1152921504606845952+2^60*1152921504606846975))))
def word407 : Sig := BitVec.ofNat 300 (1151794504113585150+2^60*(1151794504113585150+2^60*(1151795605772696574+2^60*(1152921504606845952+2^60*1152921504606846975))))
def word408 : Sig := BitVec.ofNat 300 (764106334431517350+2^60*(764106334431517350+2^60*(711629478+2^60*(1152921504606846975+2^60*1152921504606846975))))
def word409 : Sig := BitVec.ofNat 300 (1151794504113585150+2^60*(1151794504113585150+2^60*(1072692222+2^60*(1152921504606846975+2^60*1152921504606846975))))
def word410 : Sig := BitVec.ofNat 300 (764106334431517350+2^60*(764106334431517350+2^60*(1125899544730278+2^60*(1152921504606846975+2^60*1152921504606846975))))
def word411 : Sig := BitVec.ofNat 300 (1151794504113585150+2^60*(1151794504113585150+2^60*(1152921504605797374+2^60*(1152921504606846975+2^60*1152921504606846975))))
def bucketId (ws : List Sig) : Fin 97 := ⟨(ws.foldl (fun v w => v+w.toNat) 0) % 97, Nat.mod_lt _ (by decide)⟩
def bucket1g0 : List (List Sig) := []
def bucket1g1 : List (List Sig) := []
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
def bucket1g29 : List (List Sig) := [[word79,word382]]
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
def bucket1g42 : List (List Sig) := []
def bucket1g43 : List (List Sig) := []
def bucket1g44 : List (List Sig) := []
def bucket1g45 : List (List Sig) := []
def bucket1g46 : List (List Sig) := []
def bucket1g47 : List (List Sig) := []
def bucket1g48 : List (List Sig) := []
def bucket1g49 : List (List Sig) := []
def bucket1g50 : List (List Sig) := []
def bucket1g51 : List (List Sig) := []
def bucket1g52 : List (List Sig) := [[word172,word286]]
def bucket1g53 : List (List Sig) := [[word82,word385], [word171,word285]]
def bucket1g54 : List (List Sig) := []
def bucket1g55 : List (List Sig) := []
def bucket1g56 : List (List Sig) := [[word166,word310], [word176,word288]]
def bucket1g57 : List (List Sig) := []
def bucket1g58 : List (List Sig) := [[word76,word389], [word78,word388], [word81,word384], [word170,word284]]
def bucket1g59 : List (List Sig) := [[word80,word383]]
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
def bucket1g82 : List (List Sig) := [[word173,word287]]
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
def bucket2g0 : List (List Sig) := [[word364,word384,word395]]
def bucket2g1 : List (List Sig) := [[word55,word79,word396]]
def bucket2g2 : List (List Sig) := [[word81,word122,word384], [word173,word286,word396]]
def bucket2g3 : List (List Sig) := []
def bucket2g4 : List (List Sig) := [[word310,word369,word388]]
def bucket2g5 : List (List Sig) := [[word269,word286,word396]]
def bucket2g6 : List (List Sig) := [[word18,word81,word384], [word173,word201,word286]]
def bucket2g7 : List (List Sig) := [[word86,word171,word303]]
def bucket2g8 : List (List Sig) := []
def bucket2g9 : List (List Sig) := [[word214,word233,word287], [word215,word233,word286], [word216,word233,word283]]
def bucket2g10 : List (List Sig) := [[word83,word173,word314], [word173,word233,word287], [word310,word364,word384], [word310,word365,word383], [word310,word368,word382]]
def bucket2g11 : List (List Sig) := []
def bucket2g12 : List (List Sig) := [[word73,word80,word401], [word74,word79,word401]]
def bucket2g13 : List (List Sig) := [[word173,word214,word287], [word173,word279,word286], [word173,word287,word310], [word357,word364,word384]]
def bucket2g14 : List (List Sig) := [[word47,word82,word401], [word316,word318,word401]]
def bucket2g15 : List (List Sig) := [[word18,word173,word286]]
def bucket2g16 : List (List Sig) := []
def bucket2g17 : List (List Sig) := [[word272,word287,word401]]
def bucket2g18 : List (List Sig) := [[word41,word82,word396]]
def bucket2g19 : List (List Sig) := [[word277,word286,word398]]
def bucket2g20 : List (List Sig) := [[word14,word173,word286], [word268,word287,word401], [word270,word310,word384]]
def bucket2g21 : List (List Sig) := [[word83,word173,word310], [word86,word172,word310], [word90,word171,word310]]
def bucket2g22 : List (List Sig) := [[word184,word205,word287]]
def bucket2g23 : List (List Sig) := [[word173,word286,word287]]
def bucket2g24 : List (List Sig) := []
def bucket2g25 : List (List Sig) := [[word184,word203,word287], [word185,word203,word286], [word186,word203,word283], [word293,word310,word401]]
def bucket2g26 : List (List Sig) := [[word122,word173,word287]]
def bucket2g27 : List (List Sig) := []
def bucket2g28 : List (List Sig) := [[word55,word81,word409], [word81,word184,word384], [word182,word203,word287]]
def bucket2g29 : List (List Sig) := [[word81,word364,word384], [word173,word231,word286]]
def bucket2g30 : List (List Sig) := [[word18,word173,word287], [word55,word76,word405], [word55,word78,word403], [word55,word81,word401], [word60,word80,word401], [word64,word74,word401]]
def bucket2g31 : List (List Sig) := [[word55,word80,word397], [word279,word285,word401]]
def bucket2g32 : List (List Sig) := [[word39,word176,word310], [word40,word173,word310], [word43,word81,word401], [word43,word170,word310], [word47,word55,word406], [word51,word55,word401], [word81,word335,word384], [word86,word168,word310]]
def bucket2g33 : List (List Sig) := [[word9,word173,word286], [word171,word173,word286]]
def bucket2g34 : List (List Sig) := []
def bucket2g35 : List (List Sig) := []
def bucket2g36 : List (List Sig) := []
def bucket2g37 : List (List Sig) := [[word81,word86,word384]]
def bucket2g38 : List (List Sig) := []
def bucket2g39 : List (List Sig) := []
def bucket2g40 : List (List Sig) := [[word17,word80,word384], [word18,word79,word384], [word31,word47,word384], [word74,word80,word384]]
def bucket2g41 : List (List Sig) := [[word214,word235,word287], [word322,word364,word384]]
def bucket2g42 : List (List Sig) := [[word80,word384,word396]]
def bucket2g43 : List (List Sig) := [[word55,word81,word384], [word173,word216,word286]]
def bucket2g44 : List (List Sig) := [[word38,word310,word401], [word106,word288,word401], [word106,word310,word387]]
def bucket2g45 : List (List Sig) := []
def bucket2g46 : List (List Sig) := [[word83,word173,word287], [word277,word287,word403], [word279,word283,word403]]
def bucket2g47 : List (List Sig) := [[word283,word284,word401]]
def bucket2g48 : List (List Sig) := [[word86,word173,word288]]
def bucket2g49 : List (List Sig) := [[word18,word82,word386], [word274,word288,word401], [word274,word310,word387], [word277,word287,word401], [word278,word286,word401], [word279,word283,word401]]
def bucket2g50 : List (List Sig) := []
def bucket2g51 : List (List Sig) := [[word31,word55,word385]]
def bucket2g52 : List (List Sig) := [[word173,word184,word287], [word273,word287,word401]]
def bucket2g53 : List (List Sig) := [[word203,word277,word287]]
def bucket2g54 : List (List Sig) := []
def bucket2g55 : List (List Sig) := [[word18,word75,word389], [word18,word77,word388], [word18,word80,word384], [word80,word382,word384], [word351,word353,word401]]
def bucket2g56 : List (List Sig) := [[word18,word104,word375], [word34,word163,word310], [word81,word384,word401], [word173,word287,word335]]
def bucket2g57 : List (List Sig) := [[word80,word81,word384]]
def bucket2g58 : List (List Sig) := [[word8,word80,word384], [word18,word64,word384], [word81,word384], [word325,word327,word401]]
def bucket2g59 : List (List Sig) := []
def bucket2g60 : List (List Sig) := []
def bucket2g61 : List (List Sig) := [[word86,word173,word287], [word99,word284,word384]]
def bucket2g62 : List (List Sig) := [[word81,word150,word384], [word86,word165,word284]]
def bucket2g63 : List (List Sig) := [[word331,word364,word384]]
def bucket2g64 : List (List Sig) := []
def bucket2g65 : List (List Sig) := []
def bucket2g66 : List (List Sig) := []
def bucket2g67 : List (List Sig) := [[word9,word171,word286], [word55,word173,word287], [word81,word99,word384]]
def bucket2g68 : List (List Sig) := []
def bucket2g69 : List (List Sig) := []
def bucket2g70 : List (List Sig) := []
def bucket2g71 : List (List Sig) := []
def bucket2g72 : List (List Sig) := []
def bucket2g73 : List (List Sig) := [[word9,word80,word384], [word18,word65,word384], [word32,word41,word384]]
def bucket2g74 : List (List Sig) := [[word212,word233,word287], [word310,word372,word389]]
def bucket2g75 : List (List Sig) := [[word108,word310,word384]]
def bucket2g76 : List (List Sig) := [[word214,word232,word286], [word233,word277,word287]]
def bucket2g77 : List (List Sig) := [[word81,word365,word384]]
def bucket2g78 : List (List Sig) := [[word277,word287,word406]]
def bucket2g79 : List (List Sig) := []
def bucket2g80 : List (List Sig) := [[word173,word277,word287], [word173,word287,word401], [word203,word233,word287]]
def bucket2g81 : List (List Sig) := [[word277,word287,word405], [word279,word283,word405]]
def bucket2g82 : List (List Sig) := [[word2,word173,word286], [word16,word173,word286], [word18,word173,word283], [word173,word186,word286], [word173,word287]]
def bucket2g83 : List (List Sig) := []
def bucket2g84 : List (List Sig) := [[word173,word203,word287]]
def bucket2g85 : List (List Sig) := []
def bucket2g86 : List (List Sig) := [[word81,word214,word384], [word81,word310,word384], [word150,word173,word287]]
def bucket2g87 : List (List Sig) := []
def bucket2g88 : List (List Sig) := []
def bucket2g89 : List (List Sig) := [[word15,word173,word286]]
def bucket2g90 : List (List Sig) := [[word81,word384,word396]]
def bucket2g91 : List (List Sig) := []
def bucket2g92 : List (List Sig) := [[word184,word202,word286]]
def bucket2g93 : List (List Sig) := []
def bucket2g94 : List (List Sig) := []
def bucket2g95 : List (List Sig) := []
def bucket2g96 : List (List Sig) := [[word310,word384,word385]]
def table2 : Array (List (List Sig)) := #[bucket2g0,bucket2g1,bucket2g2,bucket2g3,bucket2g4,bucket2g5,bucket2g6,bucket2g7,bucket2g8,bucket2g9,bucket2g10,bucket2g11,bucket2g12,bucket2g13,bucket2g14,bucket2g15,bucket2g16,bucket2g17,bucket2g18,bucket2g19,bucket2g20,bucket2g21,bucket2g22,bucket2g23,bucket2g24,bucket2g25,bucket2g26,bucket2g27,bucket2g28,bucket2g29,bucket2g30,bucket2g31,bucket2g32,bucket2g33,bucket2g34,bucket2g35,bucket2g36,bucket2g37,bucket2g38,bucket2g39,bucket2g40,bucket2g41,bucket2g42,bucket2g43,bucket2g44,bucket2g45,bucket2g46,bucket2g47,bucket2g48,bucket2g49,bucket2g50,bucket2g51,bucket2g52,bucket2g53,bucket2g54,bucket2g55,bucket2g56,bucket2g57,bucket2g58,bucket2g59,bucket2g60,bucket2g61,bucket2g62,bucket2g63,bucket2g64,bucket2g65,bucket2g66,bucket2g67,bucket2g68,bucket2g69,bucket2g70,bucket2g71,bucket2g72,bucket2g73,bucket2g74,bucket2g75,bucket2g76,bucket2g77,bucket2g78,bucket2g79,bucket2g80,bucket2g81,bucket2g82,bucket2g83,bucket2g84,bucket2g85,bucket2g86,bucket2g87,bucket2g88,bucket2g89,bucket2g90,bucket2g91,bucket2g92,bucket2g93,bucket2g94,bucket2g95,bucket2g96]
def bucket3g0 : List (List Sig) := [[word9,word277,word286,word401], [word18,word55,word173,word286], [word18,word240,word335,word384], [word18,word310,word370,word388], [word55,word81,word184,word401], [word83,word86,word173,word310], [word86,word214,word230,word310], [word86,word279,word296,word403]]
def bucket3g1 : List (List Sig) := [[word18,word104,word184,word374], [word41,word74,word296,word401], [word47,word55,word277,word401], [word55,word81,word364,word401], [word55,word285,word310,word401], [word86,word284,word296,word401], [word99,word171,word310,word401]]
def bucket3g2 : List (List Sig) := [[word9,word86,word173,word310], [word55,word99,word195,word401], [word55,word99,word208,word310], [word67,word99,word310,word401], [word86,word124,word173,word310], [word86,word171,word173,word310], [word86,word245,word384,word396], [word99,word331,word384,word401]]
def bucket3g3 : List (List Sig) := [[word18,word186,word203,word286], [word18,word310,word377,word384], [word74,word86,word256,word401], [word86,word279,word296,word401]]
def bucket3g4 : List (List Sig) := [[word55,word81,word335,word401], [word86,word184,word203,word287]]
def bucket3g5 : List (List Sig) := [[word47,word55,word184,word405], [word73,word86,word278,word401], [word86,word173,word310,word337], [word99,word188,word279,word401]]
def bucket3g6 : List (List Sig) := [[word18,word310,word365,word384], [word55,word83,word173,word310], [word74,word86,word325,word401], [word86,word331,word384,word396], [word310,word365,word382,word384]]
def bucket3g7 : List (List Sig) := [[word18,word212,word233,word286], [word34,word310,word311,word401], [word55,word99,word332,word401], [word86,word203,word279,word296], [word86,word229,word231,word310], [word86,word279,word313,word401], [word86,word289,word310,word401], [word187,word220,word310,word401], [word190,word217,word310,word401], [word214,word233,word287,word401]]
def bucket3g8 : List (List Sig) := [[word55,word86,word176,word310], [word55,word99,word331,word405], [word310,word364,word384,word401]]
def bucket3g9 : List (List Sig) := [[word2,word214,word233,word286], [word8,word310,word365,word384], [word16,word214,word233,word286], [word18,word119,word122,word384], [word18,word214,word233,word283], [word18,word233,word277,word286], [word18,word357,word365,word384], [word55,word81,word86,word401], [word55,word310,word380,word401], [word86,word351,word355,word401], [word99,word103,word310,word401], [word186,word214,word233,word286], [word214,word233,word287]]
def bucket3g10 : List (List Sig) := [[word18,word139,word150,word384], [word47,word55,word401,word411], [word55,word99,word395,word401], [word55,word177,word310,word401], [word55,word184,word203,word287], [word73,word86,word259,word401], [word74,word83,word259,word401], [word74,word86,word258,word401], [word216,word277,word286,word401], [word310,word364,word384]]
def bucket3g11 : List (List Sig) := [[word18,word277,word286,word406], [word47,word55,word283,word401], [word55,word90,word310,word364], [word74,word86,word296,word365], [word99,word219,word279,word401]]
def bucket3g12 : List (List Sig) := [[word17,word55,word80,word401], [word17,word279,word286,word401], [word18,word55,word79,word401], [word31,word47,word55,word401], [word55,word74,word80,word401], [word74,word279,word286,word401], [word74,word287,word310,word401], [word86,word173,word216,word310], [word86,word277,word310,word393], [word86,word325,word329,word401], [word99,word310,word316,word401], [word286,word310,word384,word396]]
def bucket3g13 : List (List Sig) := [[word18,word173,word277,word286], [word18,word173,word286,word401], [word18,word203,word233,word286], [word55,word322,word364,word401], [word74,word86,word280,word401], [word74,word86,word299,word401], [word83,word212,word233,word310], [word83,word277,word287,word401], [word99,word279,word310,word405], [word99,word310,word389,word405], [word150,word214,word233,word287]]
def bucket3g14 : List (List Sig) := [[word18,word99,word173,word310], [word18,word277,word286,word405], [word41,word279,word296,word401], [word55,word80,word396,word401], [word55,word310,word372,word401], [word74,word86,word143,word401], [word150,word310,word364,word384], [word279,word286,word396,word401]]
def bucket3g15 : List (List Sig) := [[word18,word173,word286], [word83,word233,word277,word310], [word86,word277,word288,word401], [word86,word277,word310,word387]]
def bucket3g16 : List (List Sig) := [[word15,word214,word233,word286], [word18,word269,word286,word401], [word18,word271,word310,word384], [word18,word286,word292,word384], [word31,word41,word55,word396], [word55,word283,word310,word403]]
def bucket3g17 : List (List Sig) := [[word18,word173,word203,word286], [word30,word86,word277,word401], [word55,word99,word310,word403], [word55,word100,word310,word401], [word62,word99,word310,word401], [word73,word86,word310,word403], [word74,word83,word310,word403], [word74,word86,word233,word296], [word83,word189,word214,word233], [word83,word189,word233,word310], [word83,word277,word310,word406], [word86,word189,word218,word233], [word86,word310,word389,word404], [word99,word188,word233,word310], [word184,word212,word287,word401]]
def bucket3g18 : List (List Sig) := [[word55,word105,word310,word401], [word83,word219,word277,word401], [word86,word278,word310,word401], [word86,word279,word297,word401]]
def bucket3g19 : List (List Sig) := [[word18,word150,word173,word286], [word43,word99,word310,word403], [word55,word283,word310,word401], [word55,word286,word297,word401], [word55,word287,word296,word401], [word74,word283,word296,word401], [word83,word173,word277,word310], [word83,word173,word310,word401], [word83,word203,word233,word310], [word86,word173,word296,word310], [word99,word310,word364,word384], [word184,word214,word286,word398], [word184,word277,word287,word401], [word184,word279,word283,word401]]
def bucket3g20 : List (List Sig) := [[word39,word106,word310,word401], [word43,word99,word310,word409], [word47,word55,word314,word401], [word55,word90,word310,word407], [word55,word99,word292,word411], [word55,word99,word310,word401], [word55,word99,word357,word403], [word73,word86,word310,word401], [word74,word83,word310,word401], [word74,word86,word298,word401], [word74,word86,word309,word401], [word74,word86,word310,word398], [word74,word99,word296,word401], [word83,word189,word219,word401], [word83,word277,word310,word405], [word99,word188,word219,word401], [word99,word189,word218,word401]]
def bucket3g21 : List (List Sig) := [[word18,word310,word368,word384], [word43,word283,word310,word401], [word47,word55,word259,word401], [word55,word86,word173,word310], [word74,word86,word320,word401], [word83,word173,word310]]
def bucket3g22 : List (List Sig) := [[word43,word99,word310,word401], [word48,word86,word310,word401], [word49,word83,word310,word401], [word55,word99,word295,word401], [word55,word310,word353,word401], [word74,word86,word296,word405], [word86,word203,word219,word296]]
def bucket3g23 : List (List Sig) := [[word43,word86,word173,word310], [word55,word99,word294,word401], [word55,word99,word357,word401], [word55,word162,word310,word401], [word73,word86,word357,word401], [word74,word83,word357,word401], [word83,word173,word203,word310], [word99,word160,word310,word401], [word184,word203,word287,word401], [word277,word287,word335,word401], [word279,word283,word335,word401]]
def bucket3g24 : List (List Sig) := [[word9,word310,word365,word384], [word18,word279,word286,word403], [word34,word214,word228,word310], [word39,word86,word173,word310], [word73,word86,word203,word310], [word74,word83,word203,word310], [word83,word277,word310,word368], [word86,word279,word296,word365]]
def bucket3g25 : List (List Sig) := [[word2,word184,word203,word286], [word16,word184,word203,word286], [word18,word55,word80,word409], [word18,word80,word184,word384], [word18,word184,word203,word283], [word18,word284,word286,word401], [word39,word274,word310,word401], [word43,word99,word357,word401], [word55,word99,word282,word401], [word55,word353,word357,word401], [word83,word150,word173,word310], [word184,word186,word203,word286], [word184,word203,word287]]
def bucket3g26 : List (List Sig) := [[word86,word106,word279,word401], [word99,word104,word279,word401], [word214,word233,word286,word396]]
def bucket3g27 : List (List Sig) := [[word18,word55,word75,word405], [word18,word55,word77,word403], [word18,word55,word80,word401], [word18,word279,word286,word401], [word34,word86,word173,word310], [word186,word216,word286,word401]]
def bucket3g28 : List (List Sig) := [[word47,word55,word214,word403], [word47,word55,word310,word403], [word55,word99,word264,word401], [word55,word99,word310,word361], [word55,word99,word352,word401], [word55,word170,word310,word401], [word55,word327,word331,word401], [word86,word277,word287,word401], [word86,word279,word283,word401], [word99,word310,word384,word407], [word99,word310,word390,word401]]
def bucket3g29 : List (List Sig) := [[word18,word41,word82,word401], [word18,word43,word80,word401], [word18,word50,word55,word401], [word18,word80,word335,word384], [word55,word80,word81,word401], [word55,word86,word163,word310], [word55,word99,word317,word401], [word150,word184,word203,word287], [word310,word364,word365,word384]]
def bucket3g30 : List (List Sig) := [[word8,word55,word80,word401], [word18,word55,word64,word401], [word55,word81,word86,word365], [word55,word81,word401], [word55,word99,word302,word401], [word74,word296,word365,word401], [word86,word233,word279,word296]]
def bucket3g31 : List (List Sig) := [[word18,word203,word279,word286], [word40,word74,word310,word401], [word41,word73,word310,word401], [word47,word55,word310,word401], [word52,word86,word173,word310], [word55,word80,word86,word364], [word55,word99,word310,word394], [word82,word99,word310,word401]]
def bucket3g32 : List (List Sig) := [[word15,word184,word203,word286], [word41,word55,word173,word310], [word55,word99,word279,word403], [word55,word99,word288,word401], [word55,word99,word310,word387], [word279,word283,word296,word401]]
def bucket3g33 : List (List Sig) := [[word18,word351,word354,word401], [word43,word47,word310,word401], [word55,word99,word284,word401], [word99,word279,word296,word401]]
def bucket3g34 : List (List Sig) := [[word18,word80,word86,word384], [word47,word55,word357,word401], [word55,word81,word150,word401], [word55,word277,word287,word401], [word55,word279,word283,word401], [word83,word214,word233,word314], [word99,word310,word325,word401]]
def bucket3g35 : List (List Sig) := [[word18,word144,word365,word384], [word43,word99,word284,word401], [word43,word99,word310,word384], [word55,word90,word310,word403], [word55,word99,word279,word401], [word55,word331,word364,word401], [word73,word86,word279,word401], [word74,word83,word279,word401], [word82,word86,word310,word396], [word83,word310,word382,word401], [word83,word310,word384,word396], [word86,word279,word296,word405]]
def bucket3g36 : List (List Sig) := [[word9,word86,word171,word310], [word18,word86,word173,word296], [word18,word325,word328,word401], [word34,word277,word310,word365], [word43,word86,word165,word310], [word55,word86,word173,word279]]
def bucket3g37 : List (List Sig) := [[word18,word322,word365,word384], [word55,word99,word326,word401], [word214,word233,word279,word286], [word214,word233,word287,word310]]
def bucket3g38 : List (List Sig) := [[word18,word104,word277,word365], [word55,word90,word310,word401], [word55,word99,word301,word401], [word55,word99,word351,word401], [word60,word86,word310,word401], [word61,word83,word310,word401], [word99,word216,word233,word310], [word214,word310,word364,word384]]
def bucket3g39 : List (List Sig) := [[word18,word214,word233,word286], [word34,word190,word203,word310], [word55,word81,word99,word401], [word86,word187,word203,word310], [word86,word277,word310,word368]]
def bucket3g40 : List (List Sig) := [[word18,word55,word80,word384], [word18,word173,word233,word286], [word43,word90,word310,word401], [word44,word86,word310,word401], [word45,word83,word310,word401], [word55,word99,word260,word401], [word74,word86,word282,word401], [word86,word259,word384,word396], [word99,word310,word388,word403], [word277,word310,word377,word401], [word279,word310,word364,word401]]
def bucket3g41 : List (List Sig) := [[word47,word55,word286,word401], [word55,word90,word357,word401], [word73,word86,word310,word365], [word296,word310,word365,word384]]
def bucket3g42 : List (List Sig) := [[word18,word279,word287,word401], [word55,word90,word203,word310], [word184,word203,word286,word396], [word310,word364,word384,word396]]
def bucket3g43 : List (List Sig) := [[word18,word173,word214,word286], [word18,word173,word286,word310], [word74,word86,word329,word401], [word74,word86,word352,word401], [word99,word310,word388,word401], [word99,word316,word322,word401], [word279,word296,word365,word401]]
def bucket3g44 : List (List Sig) := [[word14,word214,word233,word286], [word18,word55,word86,word375], [word27,word36,word310,word401], [word29,word34,word310,word401], [word55,word99,word145,word401], [word74,word86,word310,word393], [word74,word86,word317,word401], [word86,word184,word200,word310], [word86,word310,word388,word402]]
def bucket3g45 : List (List Sig) := [[word9,word55,word80,word401], [word9,word279,word286,word401], [word18,word55,word65,word401], [word18,word55,word392,word401], [word18,word178,word286,word401], [word32,word41,word55,word401], [word83,word214,word233,word310], [word86,word214,word232,word310], [word283,word310,word384,word401]]
def bucket3g46 : List (List Sig) := [[word47,word55,word279,word401], [word55,word310,word372,word405], [word83,word173,word233,word310], [word99,word310,word384,word401], [word184,word201,word203,word286], [word184,word214,word287,word403]]
def bucket3g47 : List (List Sig) := [[word18,word31,word55,word386], [word18,word41,word55,word406], [word18,word171,word286,word401], [word18,word272,word286,word401], [word27,word99,word279,word401], [word29,word86,word279,word401], [word55,word108,word310,word401], [word73,word86,word233,word310], [word74,word83,word233,word310], [word74,word86,word279,word403], [word74,word86,word288,word401], [word74,word86,word310,word387], [word86,word173,word310,word384], [word86,word189,word233,word279], [word214,word233,word286,word287]]
def bucket3g48 : List (List Sig) := [[word55,word99,word322,word403], [word74,word86,word242,word401], [word74,word86,word284,word401]]
def bucket3g49 : List (List Sig) := [[word2,word277,word286,word401], [word16,word277,word286,word401], [word18,word277,word283,word401], [word42,word55,word310,word401], [word55,word81,word365,word401], [word55,word86,word174,word310], [word55,word99,word310,word406], [word73,word86,word144,word401], [word74,word83,word144,word401], [word74,word286,word296,word401], [word83,word173,word214,word310], [word86,word173,word218,word310], [word99,word357,word384,word401], [word184,word214,word287,word401], [word184,word215,word286,word401], [word184,word216,word283,word401], [word185,word214,word286,word401], [word186,word214,word283,word401], [word186,word277,word286,word401], [word277,word287,word401], [word279,word283,word401]]
def bucket3g50 : List (List Sig) := [[word18,word268,word286,word401], [word49,word86,word284,word401], [word55,word310,word318,word401], [word74,word86,word279,word401], [word83,word184,word203,word314], [word86,word310,word384,word396], [word99,word189,word279,word401], [word99,word203,word310,word384], [word122,word214,word233,word287]]
def bucket3g51 : List (List Sig) := [[word2,word86,word173,word310], [word16,word86,word173,word310], [word18,word245,word341,word384], [word55,word99,word322,word401], [word55,word113,word310,word401], [word55,word283,word310,word405], [word73,word86,word322,word401], [word74,word83,word322,word401], [word74,word86,word321,word401], [word86,word173,word186,word310], [word86,word173,word199,word310], [word99,word111,word310,word401], [word122,word310,word364,word384]]
def bucket3g52 : List (List Sig) := [[word18,word184,word205,word286], [word18,word259,word359,word384], [word55,word99,word225,word401], [word55,word99,word238,word310], [word55,word99,word310,word405], [word55,word101,word310,word401], [word63,word99,word310,word401], [word73,word86,word310,word405], [word74,word83,word310,word405], [word74,word86,word326,word401], [word83,word203,word219,word310], [word99,word203,word218,word310], [word182,word214,word287,word401]]
def bucket3g53 : List (List Sig) := [[word18,word80,word384,word401], [word43,word99,word322,word401], [word55,word90,word279,word401], [word74,word86,word351,word401], [word83,word272,word310,word401], [word86,word357,word384,word396], [word150,word277,word287,word401], [word150,word279,word283,word401], [word184,word203,word214,word287], [word184,word203,word279,word286], [word184,word203,word287,word310], [word214,word231,word233,word286]]
def bucket3g54 : List (List Sig) := [[word18,word214,word233,word287], [word18,word233,word279,word286], [word43,word99,word310,word405], [word55,word99,word358,word401], [word74,word86,word203,word279], [word86,word186,word203,word219], [word99,word186,word203,word310]]
def bucket3g55 : List (List Sig) := [[word18,word31,word41,word384], [word18,word80,word384], [word18,word184,word203,word286], [word18,word245,word365,word384], [word18,word310,word364,word384], [word55,word99,word357,word405]]
def bucket3g56 : List (List Sig) := [[word15,word277,word286,word401], [word18,word122,word173,word286], [word40,word214,word233,word310], [word74,word83,word310,word368], [word83,word268,word310,word401], [word99,word106,word279,word401], [word277,word310,word365,word384]]
def bucket3g57 : List (List Sig) := [[word9,word214,word233,word286], [word31,word99,word310,word384], [word47,word310,word384,word401], [word55,word99,word307,word401], [word83,word189,word277,word401], [word99,word310,word391,word401]]
def bucket3g58 : List (List Sig) := [[word15,word86,word173,word310], [word18,word182,word203,word286], [word18,word296,word365,word384], [word54,word86,word173,word310], [word55,word81,word214,word401], [word55,word81,word310,word401], [word55,word86,word303,word396], [word83,word184,word205,word310], [word86,word199,word201,word310], [word99,word279,word283,word401], [word277,word310,word368,word401]]
def bucket3g59 : List (List Sig) := [[word18,word37,word310,word401], [word18,word80,word150,word384], [word18,word104,word288,word401], [word18,word104,word310,word387], [word18,word279,word286,word405], [word18,word331,word365,word384], [word30,word34,word310,word401], [word55,word90,word310,word365], [word60,word86,word310,word365]]
def bucket3g60 : List (List Sig) := [[word14,word184,word203,word286], [word47,word55,word144,word401], [word73,word310,word365,word401], [word86,word173,word310,word336], [word86,word216,word233,word296], [word86,word218,word233,word279]]
def bucket3g61 : List (List Sig) := [[word18,word144,word156,word384], [word41,word74,word279,word401], [word41,word310,word384,word396], [word83,word184,word203,word310], [word86,word184,word202,word310]]
def bucket3g62 : List (List Sig) := [[word30,word86,word279,word401], [word47,word55,word322,word401], [word55,word81,word396,word401], [word74,word86,word244,word401], [word83,word122,word173,word310], [word86,word151,word173,word310], [word279,word286,word296,word401]]
def bucket3g63 : List (List Sig) := [[word47,word55,word310,word405], [word99,word218,word279,word401], [word184,word203,word286,word287]]
def bucket3g64 : List (List Sig) := [[word83,word182,word203,word310], [word90,word310,word384,word401]]
def bucket3g65 : List (List Sig) := [[word55,word90,word233,word310], [word86,word310,word383,word401], [word86,word310,word384,word397], [word86,word316,word320,word401]]
def bucket3g66 : List (List Sig) := [[word18,word83,word173,word310], [word55,word99,word316,word401], [word74,word86,word330,word401], [word122,word184,word203,word287], [word277,word286,word396,word401]]
def bucket3g67 : List (List Sig) := [[word55,word99,word279,word405], [word99,word269,word310,word401], [word99,word279,word314,word401], [word99,word290,word310,word401], [word99,word292,word310,word384], [word99,word310,word365,word384], [word214,word216,word233,word286]]
def bucket3g68 : List (List Sig) := [[word34,word74,word310,word365], [word34,word184,word198,word310], [word45,word86,word310,word384], [word55,word99,word254,word401], [word55,word99,word310,word348], [word55,word310,word385,word401], [word61,word86,word279,word401], [word86,word173,word310,word396]]
def bucket3g69 : List (List Sig) := [[word55,word90,word322,word401], [word55,word364,word395,word401], [word73,word86,word245,word401], [word74,word83,word245,word401], [word74,word86,word141,word401], [word74,word86,word303,word401]]
def bucket3g70 : List (List Sig) := [[word18,word86,word173,word314], [word18,word184,word203,word287], [word18,word310,word373,word389], [word55,word90,word310,word405], [word55,word99,word331,word403], [word83,word214,word233,word287]]
def bucket3g71 : List (List Sig) := [[word18,word214,word235,word286], [word55,word81,word122,word401], [word55,word99,word305,word401], [word74,word86,word279,word365], [word74,word86,word310,word368], [word86,word269,word310,word396], [word86,word291,word310,word384]]
def bucket3g72 : List (List Sig) := [[word18,word74,word80,word401], [word18,word107,word310,word384], [word40,word184,word203,word310], [word53,word86,word173,word310], [word55,word90,word310,word396], [word55,word310,word327,word401], [word74,word83,word296,word401], [word74,word310,word377,word401], [word86,word173,word201,word310], [word86,word214,word233,word288]]
def bucket3g73 : List (List Sig) := [[word9,word184,word203,word286], [word55,word99,word331,word401], [word55,word131,word310,word401], [word55,word310,word369,word403], [word73,word86,word331,word401], [word74,word83,word331,word401], [word99,word129,word310,word401], [word99,word233,word310,word384]]
def bucket3g74 : List (List Sig) := [[word18,word80,word365,word384], [word55,word286,word292,word396], [word83,word277,word314,word401], [word86,word173,word229,word310]]
def bucket3g75 : List (List Sig) := [[word18,word55,word81,word401], [word43,word99,word331,word401], [word55,word99,word234,word310], [word86,word215,word233,word310], [word99,word279,word310,word403]]
def bucket3g76 : List (List Sig) := [[word18,word55,word286,word386], [word18,word86,word284,word384], [word18,word277,word286,word403], [word55,word99,word363,word401], [word55,word310,word369,word401], [word86,word152,word173,word310], [word86,word186,word203,word296], [word86,word188,word203,word279], [word99,word284,word310,word401], [word184,word214,word233,word287]]
def bucket3g77 : List (List Sig) := [[word55,word86,word175,word310], [word55,word310,word364,word409], [word55,word310,word378,word401], [word74,word86,word233,word279], [word83,word214,word235,word310], [word86,word189,word216,word233], [word99,word322,word384,word401], [word184,word310,word364,word384], [word214,word277,word287,word401], [word214,word279,word283,word401], [word277,word279,word286,word401], [word277,word287,word310,word401], [word279,word283,word310,word401]]
def bucket3g78 : List (List Sig) := [[word60,word310,word365,word401], [word86,word165,word173,word310], [word99,word279,word310,word401], [word99,word310,word389,word401]]
def bucket3g79 : List (List Sig) := [[word18,word277,word286,word401], [word55,word310,word364,word401], [word55,word310,word365,word397], [word55,word310,word368,word396], [word73,word286,word310,word401], [word86,word144,word384,word396], [word86,word173,word279,word310]]
def bucket3g80 : List (List Sig) := [[word47,word55,word245,word401], [word55,word99,word204,word310], [word55,word173,word286,word310], [word74,word99,word279,word401], [word99,word310,word384,word396], [word214,word233,word287,word335]]
def bucket3g81 : List (List Sig) := [[word18,word86,word173,word310], [word43,word310,word364,word401], [word55,word99,word281,word401], [word55,word318,word322,word401], [word74,word86,word316,word401], [word86,word322,word384,word396], [word99,word310,word351,word401], [word184,word214,word287,word405], [word310,word335,word364,word384]]
def bucket3g82 : List (List Sig) := [[word18,word173,word184,word286], [word18,word273,word286,word401], [word55,word357,word364,word401], [word74,word86,word279,word405], [word74,word86,word300,word401], [word83,word277,word310,word403], [word86,word203,word219,word279], [word86,word279,word303,word401]]
def bucket3g83 : List (List Sig) := [[word18,word80,word214,word384], [word18,word80,word310,word384], [word18,word104,word279,word365], [word18,word203,word277,word286], [word40,word74,word296,word401], [word47,word55,word296,word401], [word55,word99,word322,word405], [word184,word203,word216,word286]]
def bucket3g84 : List (List Sig) := [[word14,word277,word286,word401], [word18,word216,word233,word286], [word47,word55,word331,word401], [word74,word86,word296,word403], [word86,word189,word233,word296], [word99,word351,word357,word401]]
def bucket3g85 : List (List Sig) := [[word18,word310,word376,word384], [word74,word86,word356,word401], [word83,word277,word310,word401], [word83,word279,word296,word401], [word86,word214,word233,word287], [word86,word277,word310,word398]]
def bucket3g86 : List (List Sig) := [[word14,word86,word173,word310], [word18,word173,word286,word335], [word83,word184,word203,word287], [word86,word310,word364,word384]]
def bucket3g87 : List (List Sig) := [[word61,word86,word303,word401], [word73,word86,word297,word401], [word74,word83,word277,word401], [word74,word86,word296,word401], [word99,word325,word331,word401], [word277,word286,word287,word401], [word279,word283,word286,word401]]
def bucket3g88 : List (List Sig) := [[word17,word310,word365,word384], [word55,word99,word325,word401], [word74,word310,word365,word384], [word83,word173,word184,word310], [word83,word273,word310,word401], [word86,word173,word188,word310], [word86,word184,word203,word288], [word99,word279,word286,word401]]
def bucket3g89 : List (List Sig) := [[word18,word316,word319,word401], [word45,word86,word310,word396], [word47,word279,word310,word401], [word49,word86,word296,word401], [word55,word270,word310,word401], [word83,word203,word277,word310], [word86,word279,word312,word401]]
def bucket3g90 : List (List Sig) := [[word32,word86,word310,word384], [word55,word99,word251,word401], [word55,word99,word310,word345], [word74,word86,word355,word401], [word74,word279,word365,word401], [word74,word310,word368,word401], [word122,word277,word287,word401], [word122,word279,word283,word401], [word310,word365,word384,word396]]
def bucket3g91 : List (List Sig) := [[word18,word86,word173,word286], [word55,word90,word331,word401], [word55,word214,word233,word287], [word74,word86,word203,word296], [word83,word184,word203,word219], [word86,word185,word203,word310], [word86,word188,word203,word219]]
def bucket3g92 : List (List Sig) := [[word18,word41,word173,word310], [word18,word310,word384,word386], [word34,word220,word233,word310], [word55,word80,word86,word396], [word55,word99,word246,word401], [word55,word99,word267,word401], [word55,word99,word310,word362], [word55,word310,word364,word384], [word83,word173,word310,word335], [word86,word123,word173,word310], [word86,word217,word233,word310]]
def bucket3g93 : List (List Sig) := [[word18,word104,word214,word371], [word18,word259,word365,word384], [word18,word365,word384,word395]]
def bucket3g94 : List (List Sig) := [[word18,word277,word287,word401], [word18,word279,word283,word401], [word55,word279,word364,word401]]
def bucket3g95 : List (List Sig) := [[word55,word99,word280,word401], [word86,word173,word231,word310]]
def bucket3g96 : List (List Sig) := [[word18,word80,word122,word384], [word40,word277,word310,word401], [word40,word279,word296,word401], [word74,word86,word281,word401], [word90,word279,word310,word401], [word99,word178,word310,word401], [word184,word203,word287,word335]]
def table3 : Array (List (List Sig)) := #[bucket3g0,bucket3g1,bucket3g2,bucket3g3,bucket3g4,bucket3g5,bucket3g6,bucket3g7,bucket3g8,bucket3g9,bucket3g10,bucket3g11,bucket3g12,bucket3g13,bucket3g14,bucket3g15,bucket3g16,bucket3g17,bucket3g18,bucket3g19,bucket3g20,bucket3g21,bucket3g22,bucket3g23,bucket3g24,bucket3g25,bucket3g26,bucket3g27,bucket3g28,bucket3g29,bucket3g30,bucket3g31,bucket3g32,bucket3g33,bucket3g34,bucket3g35,bucket3g36,bucket3g37,bucket3g38,bucket3g39,bucket3g40,bucket3g41,bucket3g42,bucket3g43,bucket3g44,bucket3g45,bucket3g46,bucket3g47,bucket3g48,bucket3g49,bucket3g50,bucket3g51,bucket3g52,bucket3g53,bucket3g54,bucket3g55,bucket3g56,bucket3g57,bucket3g58,bucket3g59,bucket3g60,bucket3g61,bucket3g62,bucket3g63,bucket3g64,bucket3g65,bucket3g66,bucket3g67,bucket3g68,bucket3g69,bucket3g70,bucket3g71,bucket3g72,bucket3g73,bucket3g74,bucket3g75,bucket3g76,bucket3g77,bucket3g78,bucket3g79,bucket3g80,bucket3g81,bucket3g82,bucket3g83,bucket3g84,bucket3g85,bucket3g86,bucket3g87,bucket3g88,bucket3g89,bucket3g90,bucket3g91,bucket3g92,bucket3g93,bucket3g94,bucket3g95,bucket3g96]
def bucket4g0 : List (List Sig) := [[word9,word184,word214,word286,word401], [word18,word55,word99,word310,word405], [word18,word55,word125,word310,word365], [word18,word55,word310,word354,word401], [word18,word86,word203,word279,word310], [word55,word86,word233,word296,word310], [word55,word99,word222,word310,word401], [word55,word99,word245,word310,word401], [word55,word99,word310,word401,word407]]
def bucket4g1 : List (List Sig) := [[word9,word74,word86,word310,word401], [word15,word86,word184,word203,word310], [word18,word41,word55,word296,word401], [word18,word55,word80,word335,word401], [word18,word55,word86,word322,word405], [word18,word55,word203,word286,word310], [word18,word61,word86,word310,word401], [word18,word279,word286,word335,word401], [word43,word86,word99,word310,word401], [word47,word55,word184,word214,word401], [word47,word55,word184,word310,word401], [word54,word86,word184,word203,word310], [word55,word86,word274,word310,word401], [word55,word98,word99,word310,word401], [word55,word99,word120,word310,word401], [word55,word99,word149,word310,word401], [word55,word99,word221,word310,word401], [word55,word310,word364,word365,word401], [word74,word86,word124,word310,word401], [word86,word214,word229,word233,word310]]
def bucket4g2 : List (List Sig) := [[word13,word55,word99,word310,word401], [word18,word41,word55,word331,word401], [word18,word55,word86,word277,word403], [word18,word86,word351,word357,word401], [word55,word86,word99,word357,word401], [word55,word283,word296,word310,word401]]
def bucket4g3 : List (List Sig) := [[word18,word45,word86,word310,word401], [word18,word55,word86,word256,word401], [word18,word55,word354,word357,word401], [word18,word86,word277,word296,word401], [word55,word86,word99,word203,word310], [word55,word86,word219,word296,word401], [word55,word86,word277,word279,word401], [word55,word99,word153,word310,word401], [word55,word99,word296,word310,word401], [word86,word152,word214,word233,word310], [word86,word184,word203,word310,word336], [word86,word184,word216,word296,word401], [word86,word184,word218,word279,word401], [word86,word186,word214,word296,word401], [word86,word188,word214,word279,word401], [word86,word279,word296,word401]]
def bucket4g4 : List (List Sig) := [[word9,word55,word90,word310,word401], [word18,word55,word157,word310,word365], [word18,word74,word86,word310,word365], [word18,word310,word365,word384,word401], [word55,word86,word310,word320,word401], [word55,word99,word214,word331,word401], [word55,word99,word310,word331,word401], [word55,word99,word310,word333,word401], [word55,word99,word310,word346,word401], [word74,word86,word310,word337,word401]]
def bucket4g5 : List (List Sig) := [[word9,word55,word86,word245,word401], [word18,word55,word86,word277,word401], [word18,word55,word86,word297,word401], [word18,word55,word86,word308,word401], [word18,word86,word325,word331,word401], [word47,word55,word310,word335,word401], [word55,word73,word86,word310,word401], [word55,word74,word83,word310,word401], [word55,word86,word296,word310,word405], [word55,word99,word184,word279,word401], [word83,word122,word184,word203,word310], [word86,word151,word184,word203,word310]]
def bucket4g6 : List (List Sig) := [[word18,word55,word80,word86,word401], [word18,word55,word86,word325,word401], [word18,word55,word328,word331,word401], [word18,word86,word279,word286,word401], [word18,word122,word310,word359,word384], [word18,word150,word310,word341,word384], [word18,word156,word310,word335,word384], [word18,word310,word365,word384], [word55,word95,word99,word310,word401], [word55,word99,word192,word310,word401], [word86,word214,word233,word279,word310]]
def bucket4g7 : List (List Sig) := [[word18,word41,word279,word310,word401], [word18,word55,word86,word310,word400], [word18,word55,word144,word365,word401], [word43,word55,word99,word310,word401], [word55,word83,word310,word396,word401], [word55,word214,word233,word286,word310], [word86,word150,word279,word296,word401]]
def bucket4g8 : List (List Sig) := [[word18,word55,word86,word245,word365], [word18,word55,word86,word251,word401], [word18,word55,word86,word310,word345], [word18,word86,word214,word233,word310], [word39,word55,word99,word310,word401], [word55,word90,word184,word310,word401], [word55,word99,word310,word339,word401]]
def bucket4g9 : List (List Sig) := [[word9,word55,word86,word331,word401], [word18,word55,word86,word203,word277], [word18,word55,word322,word365,word401], [word18,word83,word184,word203,word310], [word18,word86,word173,word233,word310], [word18,word86,word184,word203,word218], [word18,word184,word214,word233,word286], [word33,word55,word99,word310,word401], [word55,word86,word184,word203,word216], [word55,word86,word277,word310,word365], [word55,word99,word279,word335,word401], [word86,word214,word219,word279,word401], [word99,word214,word279,word310,word401]]
def bucket4g10 : List (List Sig) := [[word10,word55,word99,word310,word401], [word17,word55,word86,word259,word401], [word18,word55,word83,word259,word401], [word18,word55,word86,word246,word401], [word18,word55,word86,word258,word401], [word18,word55,word86,word267,word401], [word18,word55,word86,word310,word362], [word18,word55,word310,word373,word401], [word18,word74,word86,word233,word310], [word18,word150,word310,word365,word384], [word18,word214,word277,word286,word401], [word18,word277,word286,word310,word401], [word41,word55,word99,word310,word401], [word47,word55,word86,word310,word401], [word55,word74,word86,word259,word401], [word55,word99,word154,word310,word401], [word55,word214,word310,word364,word401], [word184,word214,word216,word286,word401]]
def bucket4g11 : List (List Sig) := [[word18,word55,word86,word296,word365], [word34,word55,word99,word310,word401], [word36,word55,word86,word310,word401], [word74,word86,word216,word310,word401], [word86,word184,word203,word310,word396]]
def bucket4g12 : List (List Sig) := [[word18,word55,word86,word306,word401], [word18,word55,word86,word331,word365], [word18,word55,word279,word286,word401], [word18,word55,word287,word310,word401], [word18,word74,word86,word144,word401], [word18,word86,word173,word214,word310], [word55,word86,word190,word203,word310], [word55,word86,word259,word396,word401], [word55,word90,word310,word335,word401], [word55,word99,word116,word310,word401], [word86,word184,word214,word310,word393]]
def bucket4g13 : List (List Sig) := [[word14,word86,word214,word233,word310], [word18,word55,word86,word262,word401], [word18,word55,word86,word280,word401], [word18,word55,word86,word299,word401], [word18,word74,word99,word310,word401], [word18,word86,word184,word203,word314], [word18,word86,word245,word384,word401], [word18,word214,word233,word286,word335], [word55,word86,word212,word233,word310], [word55,word296,word310,word365,word401], [word83,word184,word214,word287,word401]]
def bucket4g14 : List (List Sig) := [[word9,word86,word279,word310,word401], [word18,word55,word86,word143,word401], [word18,word55,word86,word228,word310], [word18,word55,word86,word237,word310], [word18,word55,word86,word253,word401], [word18,word74,word86,word322,word401], [word18,word86,word178,word310,word401], [word18,word184,word214,word286,word405], [word55,word86,word99,word279,word401], [word55,word86,word167,word310,word401], [word55,word99,word310,word342,word401], [word55,word310,word364,word396,word401], [word86,word277,word310,word384,word401]]
def bucket4g15 : List (List Sig) := [[word7,word55,word99,word310,word401], [word9,word55,word286,word310,word401], [word18,word55,word86,word310,word367], [word18,word74,word86,word310,word405], [word18,word86,word203,word219,word310], [word52,word55,word99,word310,word401], [word53,word86,word184,word203,word310], [word55,word86,word233,word277,word310], [word55,word99,word310,word401,word403], [word83,word184,word214,word233,word310], [word86,word184,word201,word203,word310], [word86,word184,word214,word288,word401], [word86,word184,word214,word310,word387], [word86,word188,word214,word233,word310]]
def bucket4g16 : List (List Sig) := [[word18,word41,word55,word277,word401], [word18,word55,word86,word119,word401], [word18,word86,word171,word310,word401], [word18,word86,word272,word310,word401], [word18,word86,word296,word384,word401], [word55,word86,word310,word402,word403], [word55,word99,word212,word310,word401], [word55,word99,word310,word401,word409], [word83,word214,word277,word310,word401], [word86,word218,word277,word310,word401], [word99,word184,word310,word384,word401]]
def bucket4g17 : List (List Sig) := [[word11,word55,word99,word310,word401], [word17,word55,word86,word310,word403], [word18,word27,word86,word277,word401], [word18,word55,word83,word310,word403], [word18,word55,word86,word195,word401], [word18,word55,word86,word208,word310], [word18,word55,word86,word233,word296], [word18,word55,word86,word266,word401], [word18,word55,word93,word310,word401], [word18,word55,word99,word245,word401], [word18,word67,word86,word310,word401], [word18,word86,word279,word310,word365], [word18,word86,word331,word384,word401], [word27,word55,word99,word310,word401], [word29,word55,word86,word310,word401], [word30,word86,word184,word214,word401], [word55,word74,word86,word310,word403], [word55,word86,word90,word310,word401], [word55,word86,word189,word214,word233], [word55,word86,word189,word233,word310], [word55,word86,word277,word310,word406], [word55,word99,word122,word331,word401], [word55,word99,word184,word233,word310], [word55,word99,word310,word403]]
def bucket4g18 : List (List Sig) := [[word2,word86,word277,word310,word401], [word16,word86,word277,word310,word401], [word18,word55,word86,word233,word331], [word18,word55,word86,word248,word401], [word18,word86,word214,word233,word286], [word18,word86,word229,word233,word310], [word26,word55,word99,word310,word401], [word55,word86,word216,word296,word401], [word55,word86,word219,word277,word401], [word55,word99,word277,word310,word401], [word74,word86,word214,word296,word401], [word74,word86,word296,word310,word401], [word83,word184,word214,word219,word401], [word86,word184,word215,word310,word401], [word86,word185,word214,word310,word401], [word86,word186,word277,word310,word401], [word86,word188,word214,word219,word401]]
def bucket4g19 : List (List Sig) := [[word9,word61,word86,word310,word401], [word18,word41,word214,word233,word310], [word18,word55,word86,word140,word401], [word18,word55,word86,word198,word310], [word18,word55,word86,word245,word405], [word18,word55,word283,word296,word401], [word18,word86,word268,word310,word401], [word55,word86,word173,word277,word310], [word55,word86,word173,word310,word401], [word55,word86,word203,word233,word310], [word55,word86,word310,word401,word402], [word55,word283,word310,word401], [word83,word214,word233,word310,word335], [word86,word123,word214,word233,word310], [word86,word152,word184,word203,word310]]
def bucket4g20 : List (List Sig) := [[word17,word55,word86,word310,word401], [word18,word41,word55,word184,word405], [word18,word55,word83,word310,word401], [word18,word55,word86,word155,word401], [word18,word55,word86,word298,word401], [word18,word55,word86,word309,word401], [word18,word55,word86,word310,word398], [word18,word55,word99,word296,word401], [word18,word86,word188,word279,word401], [word18,word86,word189,word277,word401], [word55,word74,word86,word310,word401], [word55,word86,word99,word310,word365], [word55,word86,word184,word204,word310], [word55,word86,word189,word219,word401], [word55,word86,word277,word310,word405], [word55,word86,word310,word396,word409], [word55,word86,word310,word401,word408], [word55,word99,word122,word310,word360], [word55,word99,word150,word310,word342], [word55,word99,word157,word310,word335], [word55,word99,word184,word219,word401], [word55,word99,word189,word214,word401], [word55,word99,word189,word310,word401], [word55,word99,word310,word401], [word73,word86,word310,word401], [word74,word83,word310,word401], [word74,word86,word184,word279,word401], [word83,word184,word214,word310,word405], [word86,word184,word189,word216,word401], [word86,word184,word310,word384,word396], [word99,word310,word335,word384,word401]]
def bucket4g21 : List (List Sig) := [[word18,word55,word86,word320,word401], [word18,word55,word99,word331,word401], [word18,word86,word184,word205,word310], [word41,word47,word55,word310,word401], [word55,word86,word173,word310], [word55,word99,word150,word310,word403], [word55,word99,word184,word322,word401], [word55,word99,word210,word310,word401]]
def bucket4g22 : List (List Sig) := [[word17,word43,word86,word310,word401], [word18,word43,word83,word310,word401], [word18,word55,word86,word259,word403], [word18,word55,word86,word296,word405], [word18,word55,word86,word332,word401], [word43,word74,word86,word310,word401], [word43,word99,word310,word401], [word49,word55,word86,word310,word401], [word55,word86,word310,word396,word401], [word55,word99,word133,word310,word401], [word55,word99,word184,word310,word405], [word55,word99,word203,word310,word401], [word86,word184,word203,word279,word310], [word86,word214,word231,word233,word310], [word99,word122,word279,word310,word401]]
def bucket4g23 : List (List Sig) := [[word17,word55,word86,word357,word401], [word18,word55,word83,word357,word401], [word18,word55,word86,word331,word405], [word18,word55,word245,word341,word401], [word18,word74,word310,word365,word401], [word18,word86,word233,word279,word310], [word18,word122,word277,word286,word401], [word18,word286,word310,word384,word401], [word39,word74,word86,word310,word401], [word46,word55,word86,word310,word401], [word55,word74,word86,word357,word401], [word55,word86,word173,word203,word310], [word55,word99,word144,word335,word401], [word55,word99,word158,word310,word401], [word55,word99,word357,word401], [word55,word122,word310,word364,word401], [word55,word150,word283,word310,word401], [word55,word184,word203,word286,word310], [word184,word214,word287,word335,word401]]
def bucket4g24 : List (List Sig) := [[word17,word55,word86,word203,word310], [word18,word55,word83,word203,word310], [word18,word55,word214,word233,word286], [word18,word55,word233,word286,word310], [word18,word55,word259,word359,word401], [word18,word86,word103,word310,word401], [word18,word86,word184,word203,word310], [word35,word55,word86,word310,word401], [word43,word49,word86,word310,word401], [word43,word86,word310,word396,word401], [word55,word74,word86,word203,word310], [word55,word99,word150,word310,word401], [word73,word86,word150,word310,word401], [word74,word83,word150,word310,word401], [word74,word86,word279,word335,word401], [word83,word86,word214,word233,word310], [word83,word184,word214,word310,word368], [word86,word310,word335,word384,word396]]
def bucket4g25 : List (List Sig) := [[word15,word86,word277,word310,word401], [word18,word41,word55,word401,word411], [word18,word55,word86,word259,word401], [word18,word55,word86,word395,word401], [word18,word55,word169,word310,word401], [word18,word86,word122,word173,word310], [word23,word55,word86,word310,word401], [word54,word86,word277,word310,word401], [word55,word86,word150,word173,word310], [word55,word86,word357,word396,word401], [word55,word99,word226,word310,word401], [word55,word99,word322,word335,word401], [word86,word99,word310,word384,word401]]
def bucket4g26 : List (List Sig) := [[word9,word86,word214,word233,word310], [word18,word55,word86,word241,word401], [word18,word55,word86,word277,word365], [word18,word55,word144,word286,word401], [word18,word86,word219,word279,word401], [word18,word99,word279,word310,word401], [word34,word74,word86,word310,word401], [word43,word99,word150,word310,word401], [word55,word86,word99,word233,word310], [word55,word86,word203,word310,word396], [word55,word86,word310,word329,word401], [word55,word99,word106,word310,word401], [word55,word99,word227,word310,word401], [word55,word99,word310,word335,word405], [word86,word124,word214,word233,word310]]
def bucket4g27 : List (List Sig) := [[word18,word31,word41,word55,word401], [word18,word43,word86,word259,word401], [word18,word55,word80,word86,word365], [word18,word55,word80,word401], [word18,word55,word245,word365,word401], [word18,word55,word310,word364,word401], [word18,word86,word182,word203,word310], [word18,word86,word310,word316,word401], [word18,word184,word216,word286,word401], [word18,word186,word214,word286,word401], [word18,word279,word286,word401], [word55,word99,word150,word357,word401], [word55,word99,word310,word401,word411], [word86,word184,word189,word296,word401], [word86,word277,word310,word336,word401]]
def bucket4g28 : List (List Sig) := [[word18,word55,word86,word349,word401], [word18,word55,word310,word319,word401], [word18,word86,word279,word310,word405], [word18,word86,word310,word389,word405], [word55,word86,word99,word144,word401], [word55,word99,word283,word310,word401], [word55,word277,word310,word365,word401], [word86,word184,word214,word287,word401]]
def bucket4g29 : List (List Sig) := [[word14,word86,word184,word203,word310], [word18,word55,word86,word315,word401], [word18,word55,word286,word310,word405], [word18,word184,word203,word286,word335], [word31,word55,word99,word310,word401], [word55,word86,word275,word310,word401], [word83,word122,word277,word310,word401], [word86,word151,word277,word310,word401], [word86,word214,word233,word310,word337]]
def bucket4g30 : List (List Sig) := [[word18,word55,word86,word310,word347], [word18,word55,word86,word324,word401], [word18,word55,word89,word310,word401], [word18,word55,word296,word365,word401], [word18,word55,word310,word338,word365], [word18,word59,word86,word310,word401], [word52,word74,word86,word310,word401], [word55,word66,word86,word310,word401], [word55,word83,word214,word233,word310], [word55,word86,word99,word322,word401], [word55,word86,word201,word203,word310], [word55,word86,word218,word233,word310], [word55,word99,word118,word310,word401], [word55,word99,word136,word310,word401]]
def bucket4g31 : List (List Sig) := [[word17,word41,word55,word310,word401], [word18,word40,word55,word310,word401], [word18,word55,word80,word150,word401], [word18,word55,word86,word206,word310], [word18,word55,word331,word365,word401], [word18,word150,word279,word286,word401], [word41,word55,word74,word310,word401], [word47,word55,word310,word401], [word55,word86,word99,word310,word405], [word55,word99,word121,word310,word401], [word55,word99,word310,word384,word401], [word74,word86,word122,word296,word401], [word86,word184,word188,word203,word310], [word86,word214,word279,word296,word401], [word86,word279,word296,word310,word401]]
def bucket4g32 : List (List Sig) := [[word18,word55,word86,word194,word401], [word18,word55,word86,word233,word277], [word18,word55,word86,word310,word403], [word18,word55,word91,word310,word401], [word18,word62,word86,word310,word401], [word18,word74,word86,word245,word401], [word18,word86,word188,word214,word233], [word18,word86,word188,word233,word310], [word24,word55,word86,word310,word401], [word30,word55,word86,word310,word401], [word55,word86,word165,word310,word401], [word55,word86,word186,word214,word233], [word55,word86,word186,word233,word310], [word55,word286,word296,word310,word401]]
def bucket4g33 : List (List Sig) := [[word18,word55,word86,word247,word401], [word18,word55,word102,word310,word401], [word18,word55,word144,word156,word401], [word18,word83,word277,word310,word401], [word18,word86,word218,word277,word401], [word28,word55,word86,word310,word401], [word31,word55,word86,word310,word396], [word41,word55,word310,word396,word401], [word55,word86,word183,word203,word310], [word55,word86,word216,word277,word401], [word55,word99,word218,word310,word401], [word86,word184,word216,word218,word401]]
def bucket4g34 : List (List Sig) := [[word18,word43,word86,word310,word403], [word18,word55,word86,word277,word406], [word18,word55,word310,word360,word365], [word18,word86,word184,word203,word286], [word18,word214,word310,word365,word384], [word55,word94,word99,word310,word401], [word55,word184,word214,word287,word401]]
def bucket4g35 : List (List Sig) := [[word2,word55,word99,word310,word401], [word9,word55,word86,word310,word407], [word16,word55,word99,word310,word401], [word17,word55,word86,word279,word401], [word18,word39,word104,word310,word401], [word18,word41,word55,word314,word401], [word18,word41,word184,word203,word310], [word18,word43,word86,word310,word409], [word18,word55,word83,word279,word401], [word18,word55,word86,word292,word411], [word18,word55,word86,word310,word401], [word18,word55,word86,word357,word403], [word18,word55,word96,word310,word401], [word18,word55,word99,word277,word401], [word18,word55,word125,word310,word360], [word18,word55,word153,word310,word342], [word18,word55,word157,word310,word338], [word18,word74,word86,word296,word401], [word18,word86,word188,word219,word401], [word18,word86,word189,word218,word401], [word34,word184,word220,word310,word401], [word47,word55,word150,word310,word401], [word55,word74,word86,word279,word401], [word55,word86,word186,word219,word401], [word55,word86,word189,word216,word401], [word55,word86,word310,word382,word401], [word55,word86,word310,word384,word396], [word55,word86,word320,word322,word401], [word55,word99,word184,word216,word401], [word55,word99,word186,word214,word401], [word55,word99,word186,word310,word401], [word55,word99,word279,word401], [word55,word99,word310,word341,word401], [word83,word184,word203,word310,word335], [word86,word123,word184,word203,word310], [word86,word184,word217,word310,word401], [word86,word277,word310,word396,word401]]
def bucket4g36 : List (List Sig) := [[word18,word41,word55,word259,word401], [word18,word55,word86,word173,word277], [word18,word55,word86,word205,word310], [word18,word55,word86,word250,word401], [word18,word74,word86,word331,word401], [word18,word279,word310,word365,word401], [word34,word184,word214,word310,word365], [word55,word99,word117,word310,word401], [word86,word214,word216,word233,word310]]
def bucket4g37 : List (List Sig) := [[word18,word43,word86,word310,word401], [word18,word55,word86,word223,word401], [word18,word55,word86,word277,word405], [word18,word55,word86,word295,word401], [word18,word86,word277,word314,word401], [word18,word214,word233,word286,word401], [word55,word86,word279,word396,word401], [word55,word86,word310,word397,word401], [word55,word99,word310,word314,word401]]
def bucket4g38 : List (List Sig) := [[word8,word55,word86,word310,word401], [word9,word55,word83,word310,word401], [word18,word55,word86,word294,word401], [word18,word55,word86,word357,word401], [word18,word55,word144,word338,word401], [word18,word55,word161,word310,word401], [word18,word86,word160,word310,word401], [word18,word99,word214,word233,word310], [word18,word104,word184,word214,word365], [word55,word61,word86,word310,word401], [word55,word86,word159,word310,word401], [word55,word90,word310,word401], [word55,word99,word180,word310,word401], [word55,word99,word190,word310,word401], [word55,word99,word209,word310,word401], [word55,word99,word259,word310,word401]]
def bucket4g39 : List (List Sig) := [[word18,word55,word86,word203,word310], [word18,word214,word233,word286], [word53,word86,word277,word310,word401], [word55,word99,word150,word279,word401], [word55,word99,word292,word310,word401], [word55,word99,word310,word365,word401], [word86,word184,word214,word310,word368]]
def bucket4g40 : List (List Sig) := [[word18,word43,word86,word357,word401], [word18,word55,word86,word282,word401], [word18,word55,word86,word304,word401], [word18,word55,word184,word203,word286], [word18,word86,word214,word235,word310], [word45,word55,word86,word310,word401], [word47,word55,word99,word310,word401], [word55,word84,word99,word310,word401], [word55,word86,word97,word310,word401], [word55,word99,word125,word310,word401], [word55,word99,word126,word310,word401], [word83,word86,word184,word203,word310], [word184,word214,word310,word377,word401]]
def bucket4g41 : List (List Sig) := [[word17,word55,word86,word310,word365], [word18,word43,word86,word203,word310], [word18,word86,word104,word279,word401], [word36,word55,word99,word310,word401], [word55,word74,word86,word310,word365], [word55,word86,word184,word198,word310]]
def bucket4g42 : List (List Sig) := [[word9,word86,word184,word203,word310], [word15,word55,word99,word310,word401], [word18,word55,word86,word203,word357], [word18,word55,word95,word310,word401], [word18,word55,word310,word373,word405], [word18,word74,word286,word310,word401], [word54,word55,word99,word310,word401], [word55,word86,word189,word296,word401], [word55,word90,word150,word310,word401], [word55,word99,word196,word310,word401], [word86,word124,word184,word203,word310]]
def bucket4g43 : List (List Sig) := [[word5,word55,word99,word310,word401], [word9,word55,word86,word259,word401], [word18,word41,word55,word214,word403], [word18,word41,word55,word310,word403], [word18,word55,word86,word264,word401], [word18,word55,word86,word310,word361], [word18,word55,word86,word329,word401], [word18,word55,word86,word352,word401], [word18,word86,word310,word384,word407], [word18,word86,word310,word390,word401], [word18,word150,word214,word233,word286], [word55,word86,word291,word310,word401], [word55,word86,word292,word310,word396], [word55,word86,word310,word365,word396], [word55,word99,word184,word331,word401], [word83,word214,word233,word310,word401], [word86,word152,word277,word310,word401], [word86,word214,word233,word296,word310]]
def bucket4g44 : List (List Sig) := [[word18,word55,word86,word310,word393], [word18,word55,word86,word317,word401], [word18,word55,word107,word310,word401], [word55,word99,word157,word310,word401], [word55,word99,word310,word336,word401], [word86,word122,word279,word296,word401]]
def bucket4g45 : List (List Sig) := [[word18,word55,word86,word302,word401], [word18,word55,word86,word310,word386], [word18,word55,word164,word286,word401], [word18,word55,word277,word365,word401], [word18,word86,word277,word310,word403], [word55,word86,word214,word233,word310], [word55,word99,word114,word310,word401], [word55,word99,word214,word310,word403], [word55,word99,word233,word310,word401], [word83,word214,word233,word310], [word86,word184,word203,word310,word337]]
def bucket4g46 : List (List Sig) := [[word17,word86,word310,word384,word401], [word18,word41,word55,word310,word401], [word18,word55,word80,word365,word401], [word18,word55,word86,word259,word365], [word18,word55,word86,word310,word394], [word18,word55,word86,word365,word395], [word18,word55,word245,word286,word401], [word18,word82,word86,word310,word401], [word18,word83,word310,word384,word401], [word55,word83,word184,word203,word310], [word55,word86,word173,word233,word310], [word55,word86,word188,word203,word310], [word55,word99,word151,word310,word401], [word74,word86,word310,word384,word401], [word86,word214,word219,word296,word401], [word86,word277,word279,word310,word401], [word99,word310,word384,word401]]
def bucket4g47 : List (List Sig) := [[word17,word55,word86,word233,word310], [word18,word55,word83,word233,word310], [word18,word55,word86,word279,word403], [word18,word55,word86,word288,word401], [word18,word55,word86,word310,word374], [word18,word55,word86,word310,word387], [word18,word122,word310,word365,word384], [word18,word184,word212,word286,word401], [word43,word86,word214,word233,word310], [word55,word74,word86,word233,word310], [word55,word90,word99,word310,word401], [word55,word99,word135,word310,word401], [word55,word99,word331,word335,word401], [word55,word214,word283,word310,word401], [word55,word277,word286,word310,word401]]
def bucket4g48 : List (List Sig) := [[word0,word55,word99,word310,word401], [word18,word41,word43,word310,word401], [word18,word55,word86,word242,word401], [word18,word55,word86,word284,word401], [word18,word86,word277,word310,word401], [word18,word86,word279,word296,word401], [word39,word86,word214,word233,word310], [word55,word86,word99,word245,word401], [word55,word99,word214,word310,word401], [word73,word86,word214,word310,word401], [word74,word83,word214,word310,word401], [word74,word86,word218,word310,word401], [word86,word310,word384,word396,word401], [word99,word184,word279,word310,word401]]
def bucket4g49 : List (List Sig) := [[word2,word184,word214,word286,word401], [word16,word184,word214,word286,word401], [word17,word55,word86,word144,word401], [word18,word41,word55,word357,word401], [word18,word55,word83,word144,word401], [word18,word55,word286,word296,word401], [word18,word86,word310,word325,word401], [word18,word184,word214,word283,word401], [word18,word184,word277,word286,word401], [word55,word74,word86,word144,word401], [word55,word86,word173,word214,word310], [word55,word86,word233,word310,word396], [word55,word86,word310,word401,word410], [word55,word184,word310,word364,word401], [word83,word150,word214,word233,word310], [word184,word186,word214,word286,word401], [word184,word214,word287,word401]]
def bucket4g50 : List (List Sig) := [[word2,word74,word86,word310,word401], [word3,word55,word99,word310,word401], [word9,word55,word86,word310,word403], [word16,word74,word86,word310,word401], [word17,word55,word99,word310,word401], [word17,word73,word86,word310,word401], [word18,word41,word55,word203,word310], [word18,word43,word86,word284,word401], [word18,word43,word86,word310,word384], [word18,word55,word86,word263,word401], [word18,word55,word86,word279,word401], [word18,word55,word310,word328,word401], [word18,word56,word86,word310,word401], [word18,word72,word86,word310,word401], [word18,word74,word86,word277,word401], [word43,word99,word214,word310,word401], [word55,word74,word99,word310,word401], [word55,word86,word186,word216,word401], [word55,word99,word310,word401,word405], [word74,word86,word184,word216,word401], [word74,word86,word186,word214,word401], [word74,word86,word186,word310,word401], [word74,word86,word279,word401], [word86,word310,word384,word396], [word99,word150,word310,word384,word401]]
def bucket4g51 : List (List Sig) := [[word17,word55,word86,word322,word401], [word18,word55,word83,word322,word401], [word18,word55,word86,word321,word401], [word18,word86,word173,word184,word310], [word18,word86,word259,word384,word401], [word18,word86,word273,word310,word401], [word18,word122,word245,word335,word384], [word34,word86,word214,word233,word310], [word55,word74,word86,word322,word401], [word55,word86,word144,word396,word401], [word55,word99,word109,word310,word401], [word55,word99,word122,word259,word401], [word55,word99,word214,word357,word401], [word55,word99,word310,word357,word401], [word55,word99,word322,word401]]
def bucket4g52 : List (List Sig) := [[word12,word55,word99,word310,word401], [word17,word55,word86,word310,word405], [word18,word55,word83,word310,word405], [word18,word55,word86,word326,word401], [word18,word86,word203,word277,word310], [word18,word150,word259,word335,word384], [word55,word74,word86,word310,word405], [word55,word86,word99,word331,word401], [word55,word86,word203,word219,word310], [word55,word86,word303,word310,word401], [word55,word99,word203,word214,word310], [word55,word99,word310,word396,word401], [word55,word99,word310,word405], [word86,word184,word203,word216,word310], [word99,word279,word310,word335,word401]]
def bucket4g53 : List (List Sig) := [[word9,word55,word86,word310,word401], [word14,word86,word277,word310,word401], [word18,word55,word86,word252,word401], [word18,word55,word86,word301,word401], [word18,word55,word86,word310,word370], [word18,word55,word86,word351,word401], [word18,word55,word104,word310,word365], [word18,word86,word216,word233,word310], [word18,word184,word203,word286,word401], [word18,word277,word286,word335,word401], [word55,word86,word272,word310,word401], [word55,word86,word322,word396,word401], [word55,word310,word335,word364,word401], [word83,word184,word212,word310,word401], [word150,word184,word214,word287,word401]]
def bucket4g54 : List (List Sig) := [[word18,word55,word86,word139,word401], [word18,word55,word86,word146,word401], [word18,word55,word86,word203,word279], [word18,word86,word184,word203,word219], [word18,word99,word184,word203,word310], [word55,word86,word310,word401,word404], [word74,word86,word150,word279,word401], [word86,word150,word310,word384,word396]]
def bucket4g55 : List (List Sig) := [[word9,word43,word86,word310,word401], [word18,word55,word80,word214,word401], [word18,word55,word80,word310,word401], [word18,word55,word86,word260,word401], [word18,word55,word99,word259,word401], [word18,word55,word142,word144,word401], [word18,word86,word173,word310,word335], [word18,word86,word310,word388,word403], [word18,word184,word203,word286], [word18,word214,word279,word286,word401], [word18,word279,word286,word310,word401], [word52,word86,word214,word233,word310], [word55,word83,word296,word310,word401], [word55,word99,word150,word322,word401], [word83,word184,word277,word310,word401], [word86,word188,word277,word310,word401]]
def bucket4g56 : List (List Sig) := [[word9,word55,word86,word357,word401], [word15,word184,word214,word286,word401], [word18,word41,word55,word286,word401], [word18,word41,word55,word310,word386], [word18,word55,word83,word310,word368], [word18,word55,word86,word310,word365], [word41,word55,word214,word233,word310], [word53,word55,word99,word310,word401], [word55,word86,word268,word310,word401], [word55,word99,word150,word310,word405], [word55,word99,word211,word310,word401], [word184,word214,word310,word365,word384]]
def bucket4g57 : List (List Sig) := [[word9,word55,word86,word203,word310], [word15,word74,word86,word310,word401], [word18,word55,word86,word259,word405], [word18,word55,word86,word310,word344], [word18,word55,word310,word376,word401], [word18,word70,word86,word310,word401], [word54,word74,word86,word310,word401], [word55,word71,word86,word310,word401], [word55,word86,word186,word296,word401], [word55,word86,word189,word277,word401], [word55,word86,word276,word310,word401], [word55,word283,word286,word310,word401], [word74,word86,word184,word296,word401], [word83,word184,word189,word214,word401], [word83,word184,word189,word310,word401], [word86,word99,word279,word310,word401], [word86,word184,word189,word218,word401], [word99,word184,word188,word310,word401]]
def bucket4g58 : List (List Sig) := [[word18,word43,word86,word310,word365], [word18,word55,word88,word310,word401], [word18,word58,word86,word310,word401], [word18,word86,word277,word286,word401], [word18,word86,word310,word388,word401], [word18,word86,word316,word322,word401], [word55,word86,word184,word205,word310], [word55,word86,word310,word364,word401], [word55,word99,word122,word310,word403], [word55,word99,word286,word310,word401], [word184,word214,word310,word368,word401]]
def bucket4g59 : List (List Sig) := [[word8,word55,word86,word310,word365], [word18,word27,word34,word310,word401], [word18,word41,word277,word310,word401], [word18,word55,word86,word145,word401], [word18,word55,word86,word357,word365], [word18,word55,word319,word322,word401], [word18,word150,word184,word203,word286], [word47,word55,word214,word310,word401], [word55,word86,word310,word312,word401], [word55,word99,word183,word310,word401], [word74,word86,word310,word336,word401], [word83,word184,word203,word310,word401], [word83,word277,word310,word335,word401], [word86,word123,word277,word310,word401], [word86,word184,word203,word296,word310]]
def bucket4g60 : List (List Sig) := [[word17,word55,word310,word365,word401], [word18,word55,word153,word310,word365], [word18,word86,word214,word233,word296], [word55,word74,word310,word365,word401], [word55,word86,word214,word233,word279], [word55,word99,word152,word310,word401], [word55,word122,word283,word310,word401]]
def bucket4g61 : List (List Sig) := [[word18,word41,word55,word279,word401], [word18,word55,word86,word144,word403], [word18,word86,word310,word384,word401], [word18,word122,word144,word150,word384], [word55,word86,word184,word203,word310], [word55,word99,word122,word310,word401], [word73,word86,word122,word310,word401], [word74,word83,word122,word310,word401], [word74,word86,word151,word310,word401], [word74,word86,word296,word335,word401], [word83,word184,word203,word310], [word86,word310,word382,word384,word401]]
def bucket4g62 : List (List Sig) := [[word18,word27,word86,word279,word401], [word18,word55,word86,word233,word310], [word18,word55,word86,word244,word401], [word18,word55,word99,word310,word403], [word32,word55,word86,word310,word401], [word55,word86,word122,word173,word310], [word55,word99,word181,word310,word401], [word55,word310,word365,word396,word401]]
def bucket4g63 : List (List Sig) := [[word18,word55,word86,word322,word403], [word19,word55,word86,word310,word401], [word34,word190,word214,word310,word401], [word43,word86,word184,word203,word310], [word43,word99,word122,word310,word401], [word55,word99,word214,word279,word401], [word55,word99,word279,word310,word401], [word86,word187,word214,word310,word401]]
def bucket4g64 : List (List Sig) := [[word9,word41,word55,word310,word401], [word18,word43,word86,word233,word310], [word18,word55,word86,word144,word401], [word18,word55,word86,word310,word406], [word18,word55,word277,word286,word401], [word18,word55,word283,word310,word401], [word18,word55,word310,word386,word401], [word18,word86,word357,word384,word401], [word39,word86,word184,word203,word310], [word55,word86,word182,word203,word310], [word55,word99,word122,word357,word401], [word83,word86,word277,word310,word401]]
def bucket4g65 : List (List Sig) := [[word18,word55,word86,word233,word357], [word18,word55,word87,word310,word401], [word18,word55,word99,word310,word401], [word18,word55,word259,word365,word401], [word18,word55,word365,word395,word401], [word18,word57,word86,word310,word401], [word18,word73,word86,word310,word401], [word18,word74,word83,word310,word401], [word18,word86,word189,word279,word401], [word18,word86,word203,word310,word384], [word55,word86,word220,word233,word310], [word55,word99,word156,word310,word401], [word83,word150,word184,word203,word310]]
def bucket4g66 : List (List Sig) := [[word6,word55,word99,word310,word401], [word9,word86,word277,word310,word401], [word18,word43,word86,word144,word401], [word18,word55,word86,word173,word310], [word18,word55,word86,word207,word310], [word18,word55,word86,word322,word401], [word18,word55,word86,word330,word401], [word18,word55,word112,word310,word401], [word18,word55,word125,word259,word401], [word18,word86,word111,word310,word401], [word40,word55,word296,word310,word401], [word55,word86,word110,word310,word401], [word55,word90,word214,word310,word401], [word86,word124,word277,word310,word401], [word184,word214,word286,word396,word401]]
def bucket4g67 : List (List Sig) := [[word18,word43,word99,word310,word401], [word18,word55,word86,word225,word401], [word18,word55,word86,word238,word310], [word18,word55,word86,word310,word405], [word18,word55,word92,word310,word401], [word18,word63,word86,word310,word401], [word18,word86,word203,word218,word310], [word18,word214,word233,word286,word310], [word25,word55,word86,word310,word401], [word34,word86,word184,word203,word310], [word55,word86,word203,word216,word310], [word55,word86,word296,word310,word403], [word74,word86,word310,word396,word401]]
def bucket4g68 : List (List Sig) := [[word9,word55,word86,word279,word401], [word18,word34,word55,word310,word365], [word18,word43,word86,word322,word401], [word18,word55,word80,word122,word401], [word18,word55,word99,word357,word401], [word18,word122,word279,word286,word401], [word55,word85,word99,word310,word401], [word55,word86,word98,word310,word401], [word55,word99,word138,word310,word401], [word55,word99,word191,word310,word401], [word55,word99,word220,word310,word401]]
def bucket4g69 : List (List Sig) := [[word17,word55,word86,word245,word401], [word18,word43,word86,word310,word405], [word18,word55,word83,word245,word401], [word18,word55,word86,word141,word401], [word18,word55,word86,word303,word401], [word18,word55,word86,word358,word401], [word18,word55,word99,word203,word310], [word18,word55,word240,word335,word401], [word18,word55,word310,word370,word403], [word18,word86,word186,word203,word310], [word18,word86,word199,word203,word310], [word18,word86,word277,word310,word365], [word55,word74,word86,word245,word401], [word55,word99,word115,word310,word401], [word55,word99,word132,word310,word401], [word86,word277,word310,word337,word401]]
def bucket4g70 : List (List Sig) := [[word14,word55,word99,word310,word401], [word18,word55,word86,word203,word322], [word18,word55,word86,word357,word405], [word18,word55,word94,word310,word401], [word18,word74,word86,word259,word401], [word55,word83,word277,word310,word401], [word55,word86,word296,word310,word401], [word55,word97,word99,word310,word401], [word55,word99,word310,word338,word401], [word86,word184,word279,word296,word401], [word86,word188,word218,word310,word401]]
def bucket4g71 : List (List Sig) := [[word18,word55,word86,word279,word365], [word18,word55,word86,word310,word368], [word18,word55,word310,word342,word365], [word52,word86,word184,word203,word310], [word53,word74,word86,word310,word401], [word55,word69,word86,word310,word401], [word55,word86,word245,word396,word401], [word86,word214,word233,word310,word384]]
def bucket4g72 : List (List Sig) := [[word18,word31,word86,word310,word384], [word18,word41,word310,word384,word401], [word18,word55,word83,word296,word401], [word18,word55,word86,word307,word401], [word18,word55,word310,word370,word401], [word18,word55,word310,word377,word401], [word18,word86,word188,word277,word401], [word18,word86,word310,word391,word401], [word41,word55,word184,word203,word310], [word43,word86,word296,word310,word401], [word47,word55,word122,word310,word401], [word55,word74,word86,word296,word401], [word55,word86,word186,word277,word401], [word55,word99,word137,word310,word401], [word55,word99,word188,word310,word401], [word86,word186,word188,word214,word401], [word86,word186,word188,word310,word401]]
def bucket4g73 : List (List Sig) := [[word17,word55,word86,word331,word401], [word18,word41,word55,word233,word310], [word18,word55,word83,word331,word401], [word18,word55,word310,word365,word409], [word18,word55,word310,word379,word401], [word18,word86,word212,word233,word310], [word18,word184,word310,word365,word384], [word55,word74,word86,word331,word401], [word55,word86,word214,word234,word310], [word55,word86,word310,word355,word401], [word55,word99,word127,word310,word401], [word55,word99,word150,word245,word401], [word55,word99,word197,word310,word401], [word55,word99,word331,word401], [word86,word214,word218,word233,word310]]
def bucket4g74 : List (List Sig) := [[word9,word55,word86,word310,word365], [word18,word55,word86,word240,word401], [word18,word55,word257,word259,word401], [word55,word86,word203,word296,word310], [word55,word86,word310,word313,word401], [word55,word99,word310,word360,word401], [word83,word184,word214,word314,word401], [word86,word279,word296,word335,word401], [word99,word214,word310,word384,word401]]
def bucket4g75 : List (List Sig) := [[word2,word86,word214,word233,word310], [word16,word86,word214,word233,word310], [word18,word41,word55,word144,word401], [word18,word55,word86,word249,word401], [word18,word55,word310,word365,word401], [word18,word86,word233,word277,word310], [word55,word86,word331,word396,word401], [word55,word99,word148,word310,word401], [word74,word86,word152,word310,word401], [word86,word186,word214,word233,word310]]
def bucket4g76 : List (List Sig) := [[word1,word55,word99,word310,word401], [word18,word47,word55,word310,word401], [word18,word55,word86,word310,word399], [word18,word86,word184,word203,word296], [word18,word184,word214,word286,word403], [word55,word86,word184,word203,word279], [word55,word86,word231,word233,word310], [word55,word86,word355,word357,word401], [word55,word99,word122,word279,word401], [word55,word99,word123,word310,word401], [word83,word214,word219,word310,word401], [word86,word216,word277,word310,word401], [word99,word214,word218,word310,word401]]
def bucket4g77 : List (List Sig) := [[word18,word41,word55,word322,word401], [word18,word43,word310,word365,word401], [word18,word55,word86,word233,word279], [word18,word55,word86,word265,word401], [word18,word74,word86,word310,word403], [word18,word86,word189,word214,word233], [word18,word86,word189,word233,word310], [word18,word86,word277,word310,word406], [word18,word310,word335,word365,word384], [word55,word86,word214,word235,word310], [word55,word86,word310,word311,word401], [word55,word99,word144,word310,word401], [word55,word99,word150,word331,word401], [word55,word190,word220,word310,word401], [word184,word214,word279,word286,word401], [word184,word214,word287,word310,word401]]
def bucket4g78 : List (List Sig) := [[word8,word55,word310,word365,word401], [word17,word86,word279,word310,word401], [word18,word41,word55,word310,word405], [word18,word55,word86,word323,word401], [word18,word55,word119,word122,word401], [word18,word55,word357,word365,word401], [word18,word83,word279,word310,word401], [word18,word86,word218,word279,word401], [word18,word86,word219,word277,word401], [word18,word99,word277,word310,word401], [word55,word99,word219,word310,word401], [word74,word86,word214,word279,word401], [word74,word86,word279,word310,word401], [word86,word186,word214,word219,word401], [word86,word214,word310,word384,word396], [word99,word184,word216,word310,word401], [word99,word186,word214,word310,word401], [word99,word279,word310,word401]]
def bucket4g79 : List (List Sig) := [[word9,word86,word310,word384,word401], [word17,word55,word286,word310,word401], [word18,word55,word139,word150,word401], [word18,word86,word173,word277,word310], [word18,word86,word173,word310,word401], [word18,word86,word203,word233,word310], [word18,word184,word214,word286,word401], [word18,word277,word286,word401], [word55,word74,word286,word310,word401], [word55,word86,word310,word364,word365], [word55,word86,word329,word331,word401], [word55,word90,word122,word310,word401], [word55,word99,word214,word322,word401], [word55,word99,word310,word322,word401], [word55,word310,word364,word401]]
def bucket4g80 : List (List Sig) := [[word4,word55,word99,word310,word401], [word9,word55,word86,word233,word310], [word18,word55,word99,word279,word401], [word18,word74,word86,word310,word401], [word18,word86,word189,word219,word401], [word18,word86,word277,word310,word405], [word18,word122,word214,word233,word286], [word55,word99,word214,word310,word405], [word86,word279,word310,word396,word401]]
def bucket4g81 : List (List Sig) := [[word18,word55,word86,word214,word371], [word18,word55,word86,word245,word403], [word18,word55,word86,word310,word371], [word18,word55,word86,word316,word401], [word18,word86,word173,word310], [word22,word55,word86,word310,word401], [word41,word55,word296,word310,word401], [word55,word83,word99,word310,word401], [word55,word286,word310,word396,word401]]
def bucket4g82 : List (List Sig) := [[word9,word55,word86,word144,word401], [word15,word86,word214,word233,word310], [word18,word49,word86,word310,word401], [word18,word55,word86,word224,word401], [word18,word55,word86,word279,word405], [word18,word55,word86,word300,word401], [word18,word86,word269,word310,word401], [word18,word86,word279,word314,word401], [word18,word86,word290,word310,word401], [word18,word86,word292,word310,word384], [word18,word86,word310,word365,word384], [word18,word182,word214,word286,word401], [word54,word86,word214,word233,word310], [word55,word86,word277,word310,word403], [word83,word184,word214,word310,word403], [word86,word310,word382,word396,word401], [word99,word150,word279,word310,word401]]
def bucket4g83 : List (List Sig) := [[word9,word55,word99,word310,word401], [word18,word40,word55,word296,word401], [word18,word55,word86,word254,word401], [word18,word55,word86,word310,word348], [word18,word55,word90,word310,word401], [word18,word74,word86,word357,word401], [word18,word86,word173,word203,word310], [word18,word150,word277,word286,word401], [word18,word184,word203,word214,word286], [word18,word184,word203,word286,word310], [word55,word99,word124,word310,word401], [word55,word150,word310,word364,word401], [word86,word277,word296,word310,word401]]
def bucket4g84 : List (List Sig) := [[word9,word55,word86,word322,word401], [word14,word184,word214,word286,word401], [word18,word55,word86,word193,word401], [word18,word55,word86,word245,word401], [word18,word55,word86,word296,word403], [word18,word55,word86,word310,word366], [word18,word55,word259,word286,word401], [word18,word55,word310,word381,word401], [word18,word74,word86,word203,word310], [word55,word99,word184,word310,word403], [word86,word214,word233,word310,word336]]
def bucket4g85 : List (List Sig) := [[word9,word55,word86,word310,word405], [word14,word74,word86,word310,word401], [word18,word55,word86,word144,word365], [word18,word55,word86,word255,word401], [word18,word55,word86,word261,word401], [word18,word55,word86,word331,word403], [word18,word55,word86,word356,word401], [word18,word55,word271,word310,word401], [word18,word55,word286,word292,word401], [word18,word68,word86,word310,word401], [word18,word86,word150,word173,word310], [word55,word86,word277,word310,word401], [word55,word86,word279,word296,word401], [word55,word86,word297,word310,word401], [word55,word99,word179,word310,word401], [word83,word184,word214,word310,word401], [word83,word277,word310,word401], [word86,word184,word214,word310,word398]]
def bucket4g86 : List (List Sig) := [[word18,word43,word86,word245,word401], [word18,word55,word86,word184,word374], [word18,word55,word86,word305,word401], [word55,word86,word99,word259,word401], [word55,word86,word213,word233,word310], [word55,word86,word310,word404,word405], [word55,word99,word310,word337,word401], [word55,word184,word283,word310,word401], [word83,word122,word214,word233,word310], [word86,word151,word214,word233,word310]]
def bucket4g87 : List (List Sig) := [[word9,word55,word86,word303,word401], [word9,word55,word86,word310,word396], [word17,word55,word86,word297,word401], [word18,word55,word83,word277,word401], [word18,word55,word86,word236,word310], [word18,word55,word86,word296,word401], [word18,word55,word86,word322,word365], [word18,word55,word86,word340,word401], [word18,word86,word188,word218,word401], [word43,word86,word277,word310,word401], [word55,word74,word86,word277,word401], [word55,word99,word184,word310,word401], [word73,word86,word184,word310,word401], [word74,word83,word184,word214,word401], [word74,word83,word184,word310,word401], [word74,word86,word184,word218,word401], [word74,word86,word188,word214,word401], [word74,word86,word188,word310,word401], [word74,word86,word296,word401], [word86,word184,word189,word279,word401], [word86,word184,word203,word310,word384], [word99,word122,word310,word384,word401], [word184,word214,word286,word287,word401]]
def bucket4g88 : List (List Sig) := [[word18,word55,word86,word310,word373], [word18,word55,word86,word331,word401], [word18,word55,word130,word310,word401], [word18,word55,word153,word245,word401], [word18,word55,word310,word365,word384], [word18,word86,word129,word310,word401], [word18,word86,word233,word310,word384], [word18,word277,word310,word365,word401], [word39,word86,word277,word310,word401], [word55,word86,word128,word310,word401], [word55,word86,word173,word184,word310], [word55,word86,word273,word310,word401], [word55,word99,word239,word310,word401], [word55,word99,word310,word335,word403], [word55,word99,word310,word364,word401], [word83,word182,word214,word310,word401]]
def bucket4g89 : List (List Sig) := [[word18,word43,word86,word296,word401], [word43,word99,word184,word310,word401], [word55,word86,word203,word277,word310], [word55,word99,word213,word310,word401], [word83,word150,word277,word310,word401], [word83,word184,word203,word214,word310], [word86,word184,word203,word218,word310]]
def bucket4g90 : List (List Sig) := [[word18,word43,word86,word331,word401], [word18,word55,word86,word234,word310], [word18,word55,word86,word350,word401], [word18,word55,word86,word355,word401], [word18,word55,word279,word365,word401], [word18,word55,word310,word368,word401], [word18,word83,word214,word233,word310], [word18,word86,word144,word384,word401], [word18,word86,word279,word310,word403], [word55,word99,word182,word310,word401], [word55,word99,word184,word357,word401], [word55,word283,word310,word335,word401], [word122,word184,word214,word287,word401]]
def bucket4g91 : List (List Sig) := [[word2,word86,word184,word203,word310], [word16,word86,word184,word203,word310], [word18,word41,word74,word310,word401], [word18,word55,word86,word203,word296], [word18,word55,word86,word363,word401], [word18,word55,word286,word310,word403], [word18,word86,word284,word310,word401], [word18,word99,word310,word384,word401], [word20,word55,word86,word310,word401], [word34,word86,word277,word310,word401], [word55,word86,word184,word203,word219], [word55,word86,word296,word310,word365], [word55,word99,word310,word335,word401], [word73,word86,word310,word335,word401], [word74,word83,word310,word335,word401], [word74,word86,word122,word279,word401], [word74,word86,word123,word310,word401], [word74,word86,word150,word296,word401], [word86,word122,word310,word384,word396], [word86,word184,word186,word203,word310], [word86,word184,word199,word203,word310], [word86,word216,word218,word310,word401]]
def bucket4g92 : List (List Sig) := [[word18,word55,word86,word203,word331], [word18,word55,word99,word233,word310], [word18,word86,word322,word384,word401], [word55,word86,word173,word310,word335], [word55,word99,word122,word322,word401], [word86,word214,word233,word310,word396]]
def bucket4g93 : List (List Sig) := [[word9,word55,word310,word365,word401], [word18,word55,word86,word233,word322], [word18,word86,word104,word277,word401], [word18,word86,word279,word310,word401], [word18,word86,word310,word389,word401], [word43,word99,word310,word335,word401], [word55,word86,word99,word310,word403], [word55,word86,word106,word310,word401], [word55,word99,word104,word310,word401], [word55,word99,word122,word310,word405], [word55,word99,word216,word310,word401], [word55,word99,word310,word343,word401], [word86,word186,word216,word310,word401]]
def bucket4g94 : List (List Sig) := [[word18,word55,word80,word184,word401], [word18,word55,word86,word235,word310], [word18,word55,word99,word144,word401], [word18,word55,word286,word310,word401], [word18,word86,word214,word233,word314], [word18,word184,word214,word287,word401], [word18,word184,word279,word286,word401], [word55,word86,word214,word228,word310], [word55,word99,word134,word310,word401], [word55,word99,word335,word357,word401]]
def bucket4g95 : List (List Sig) := [[word18,word41,word55,word245,word401], [word18,word55,word86,word147,word401], [word18,word55,word86,word204,word310], [word18,word55,word243,word245,word401], [word18,word74,word86,word279,word401], [word18,word86,word310,word382,word401], [word18,word86,word310,word384,word396], [word21,word55,word86,word310,word401], [word52,word86,word277,word310,word401], [word55,word86,word283,word310,word401], [word55,word99,word310,word359,word401]]
def bucket4g96 : List (List Sig) := [[word18,word43,word286,word310,word401], [word18,word55,word86,word144,word405], [word18,word55,word86,word281,word401], [word18,word55,word99,word322,word401], [word18,word86,word310,word351,word401], [word18,word122,word184,word203,word286], [word40,word184,word214,word310,word401], [word41,word55,word277,word310,word401], [word53,word86,word214,word233,word310], [word55,word86,word99,word310,word401], [word55,word96,word99,word310,word401], [word55,word99,word164,word310,word401], [word55,word99,word310,word334,word401], [word74,word83,word86,word310,word401], [word86,word296,word310,word384,word401]]
def table4 : Array (List (List Sig)) := #[bucket4g0,bucket4g1,bucket4g2,bucket4g3,bucket4g4,bucket4g5,bucket4g6,bucket4g7,bucket4g8,bucket4g9,bucket4g10,bucket4g11,bucket4g12,bucket4g13,bucket4g14,bucket4g15,bucket4g16,bucket4g17,bucket4g18,bucket4g19,bucket4g20,bucket4g21,bucket4g22,bucket4g23,bucket4g24,bucket4g25,bucket4g26,bucket4g27,bucket4g28,bucket4g29,bucket4g30,bucket4g31,bucket4g32,bucket4g33,bucket4g34,bucket4g35,bucket4g36,bucket4g37,bucket4g38,bucket4g39,bucket4g40,bucket4g41,bucket4g42,bucket4g43,bucket4g44,bucket4g45,bucket4g46,bucket4g47,bucket4g48,bucket4g49,bucket4g50,bucket4g51,bucket4g52,bucket4g53,bucket4g54,bucket4g55,bucket4g56,bucket4g57,bucket4g58,bucket4g59,bucket4g60,bucket4g61,bucket4g62,bucket4g63,bucket4g64,bucket4g65,bucket4g66,bucket4g67,bucket4g68,bucket4g69,bucket4g70,bucket4g71,bucket4g72,bucket4g73,bucket4g74,bucket4g75,bucket4g76,bucket4g77,bucket4g78,bucket4g79,bucket4g80,bucket4g81,bucket4g82,bucket4g83,bucket4g84,bucket4g85,bucket4g86,bucket4g87,bucket4g88,bucket4g89,bucket4g90,bucket4g91,bucket4g92,bucket4g93,bucket4g94,bucket4g95,bucket4g96]
def bucket5g0 : List (List Sig) := [[word18,word55,word86,word122,word310,word365], [word18,word86,word150,word279,word310,word401]]
def bucket5g1 : List (List Sig) := [[word9,word18,word55,word86,word310,word401], [word18,word55,word86,word124,word310,word401], [word18,word55,word150,word286,word310,word401], [word55,word86,word214,word296,word310,word401]]
def bucket5g2 : List (List Sig) := [[word18,word55,word86,word184,word214,word403], [word18,word55,word86,word184,word310,word403]]
def bucket5g3 : List (List Sig) := [[word18,word55,word86,word179,word310,word401], [word18,word86,word184,word214,word296,word401], [word55,word86,word99,word150,word310,word401], [word55,word86,word184,word214,word279,word401]]
def bucket5g4 : List (List Sig) := [[word18,word55,word86,word310,word337,word401]]
def bucket5g5 : List (List Sig) := [[word18,word55,word86,word277,word401], [word18,word86,word122,word310,word384,word401], [word55,word86,word122,word184,word203,word310]]
def bucket5g6 : List (List Sig) := [[word18,word55,word86,word122,word233,word310], [word18,word55,word86,word239,word310,word401], [word18,word55,word86,word310,word335,word403], [word18,word55,word214,word310,word365,word401], [word18,word86,word214,word233,word310,word401], [word18,word122,word150,word310,word335,word384]]
def bucket5g7 : List (List Sig) := [[word18,word43,word86,word184,word310,word401], [word18,word55,word86,word213,word310,word401]]
def bucket5g8 : List (List Sig) := [[word18,word55,word86,word122,word144,word401], [word18,word55,word86,word182,word310,word401], [word18,word55,word86,word184,word357,word401], [word18,word86,word214,word233,word310], [word55,word86,word184,word220,word310,word401]]
def bucket5g9 : List (List Sig) := [[word18,word55,word86,word150,word277,word401], [word18,word55,word86,word184,word203,word214], [word18,word55,word86,word184,word203,word310], [word18,word55,word99,word122,word310,word401], [word55,word86,word184,word214,word310,word365]]
def bucket5g10 : List (List Sig) := [[word18,word55,word86,word122,word322,word401], [word18,word184,word214,word286,word310,word401]]
def bucket5g11 : List (List Sig) := [[word18,word43,word86,word310,word335,word401], [word18,word55,word86,word104,word310,word401], [word18,word55,word86,word122,word310,word405], [word18,word55,word86,word214,word343,word401], [word18,word55,word86,word216,word310,word401], [word18,word55,word86,word310,word343,word401], [word18,word74,word86,word214,word310,word401]]
def bucket5g12 : List (List Sig) := [[word18,word55,word86,word134,word310,word401], [word18,word55,word86,word335,word357,word401], [word18,word86,word150,word214,word233,word310]]
def bucket5g13 : List (List Sig) := [[word18,word55,word86,word184,word211,word401], [word18,word55,word86,word203,word310,word335], [word18,word55,word86,word310,word359,word401]]
def bucket5g14 : List (List Sig) := [[word18,word55,word86,word164,word310,word401], [word18,word55,word86,word310,word334,word401], [word55,word86,word122,word296,word310,word401], [word86,word184,word214,word310,word384,word401]]
def bucket5g15 : List (List Sig) := [[word18,word55,word86,word214,word245,word401], [word18,word55,word86,word222,word310,word401], [word18,word55,word86,word245,word310,word401], [word18,word55,word86,word310,word401,word407], [word55,word86,word184,word214,word233,word310]]
def bucket5g16 : List (List Sig) := [[word18,word41,word55,word184,word214,word401], [word18,word41,word55,word184,word310,word401], [word18,word55,word86,word120,word310,word401], [word18,word55,word86,word149,word310,word401], [word18,word86,word184,word212,word310,word401], [word55,word86,word214,word277,word310,word401], [word86,word184,word214,word218,word310,word401]]
def bucket5g17 : List (List Sig) := [[word13,word18,word55,word86,word310,word401], [word18,word27,word86,word184,word214,word401]]
def bucket5g18 : List (List Sig) := [[word2,word86,word184,word214,word310,word401], [word16,word86,word184,word214,word310,word401], [word18,word55,word86,word153,word310,word401], [word18,word55,word86,word214,word296,word401], [word18,word55,word86,word296,word310,word401], [word18,word86,word184,word277,word310,word401], [word55,word86,word184,word214,word219,word401], [word55,word99,word184,word214,word310,word401], [word86,word184,word186,word214,word310,word401]]
def bucket5g19 : List (List Sig) := [[word18,word55,word86,word214,word331,word401], [word18,word55,word86,word310,word331,word401], [word18,word55,word86,word310,word333,word401], [word18,word55,word86,word310,word346,word401], [word18,word55,word122,word310,word365,word401], [word55,word86,word214,word233,word310,word335]]
def bucket5g20 : List (List Sig) := [[word17,word55,word86,word310,word401], [word18,word41,word55,word310,word335,word401], [word18,word55,word83,word310,word401], [word18,word55,word86,word184,word279,word401], [word18,word55,word122,word125,word310,word401], [word18,word86,word184,word189,word214,word401], [word18,word86,word184,word189,word310,word401], [word55,word74,word86,word310,word401], [word55,word86,word184,word214,word310,word405], [word55,word99,word310,word401]]
def bucket5g21 : List (List Sig) := [[word18,word55,word86,word192,word214,word401], [word18,word55,word86,word192,word310,word401]]
def bucket5g22 : List (List Sig) := [[word18,word43,word55,word86,word310,word401], [word18,word86,word184,word203,word310,word401], [word18,word86,word277,word310,word335,word401], [word55,word86,word310,word396,word401], [word55,word99,word214,word310,word335,word401]]
def bucket5g23 : List (List Sig) := [[word9,word55,word86,word184,word310,word401], [word18,word39,word55,word86,word310,word401], [word18,word55,word122,word245,word335,word401], [word18,word122,word184,word214,word286,word401]]
def bucket5g24 : List (List Sig) := [[word17,word55,word86,word150,word310,word401], [word18,word33,word55,word86,word310,word401], [word18,word55,word83,word150,word310,word401], [word18,word55,word86,word279,word335,word401], [word18,word55,word150,word259,word335,word401], [word18,word74,word86,word122,word310,word401], [word18,word86,word184,word203,word310], [word18,word86,word214,word279,word310,word401], [word55,word74,word86,word150,word310,word401], [word55,word99,word150,word310,word401]]
def bucket5g25 : List (List Sig) := [[word10,word18,word55,word86,word310,word401], [word15,word86,word184,word214,word310,word401], [word18,word41,word55,word86,word310,word401], [word18,word55,word86,word259,word401], [word18,word55,word214,word286,word310,word401], [word54,word86,word184,word214,word310,word401]]
def bucket5g26 : List (List Sig) := [[word18,word34,word55,word86,word310,word401], [word18,word55,word86,word184,word214,word365], [word18,word55,word86,word184,word310,word365], [word55,word86,word150,word310,word396,word401]]
def bucket5g27 : List (List Sig) := [[word9,word55,word86,word310,word335,word401], [word18,word55,word86,word116,word310,word401], [word55,word86,word99,word214,word310,word401], [word86,word184,word214,word310,word336,word401]]
def bucket5g28 : List (List Sig) := [[word18,word55,word86,word122,word245,word401], [word18,word86,word150,word184,word203,word310], [word55,word184,word214,word310,word365,word401]]
def bucket5g29 : List (List Sig) := [[word18,word55,word86,word150,word259,word401], [word18,word55,word86,word310,word342,word401], [word55,word86,word122,word277,word310,word401], [word55,word86,word184,word213,word310,word401], [word83,word122,word184,word214,word310,word401], [word86,word151,word184,word214,word310,word401]]
def bucket5g30 : List (List Sig) := [[word7,word18,word55,word86,word310,word401], [word18,word52,word55,word86,word310,word401], [word18,word55,word86,word310,word335,word365], [word18,word55,word86,word310,word401,word403]]
def bucket5g31 : List (List Sig) := [[word18,word55,word86,word122,word296,word401], [word18,word55,word86,word212,word310,word401], [word18,word55,word86,word310,word401,word409], [word18,word86,word184,word310,word384,word401], [word55,word99,word122,word184,word310,word401]]
def bucket5g32 : List (List Sig) := [[word11,word18,word55,word86,word310,word401], [word18,word27,word55,word86,word310,word401], [word18,word55,word86,word122,word331,word401], [word18,word55,word86,word184,word214,word233], [word18,word55,word86,word184,word233,word310], [word18,word55,word86,word310,word403]]
def bucket5g33 : List (List Sig) := [[word18,word26,word55,word86,word310,word401], [word18,word55,word86,word214,word277,word401], [word18,word55,word86,word277,word310,word401], [word18,word55,word122,word144,word150,word401], [word18,word83,word184,word214,word310,word401], [word18,word86,word184,word214,word218,word401], [word55,word86,word184,word214,word216,word401]]
def bucket5g34 : List (List Sig) := [[word18,word55,word86,word144,word184,word401]]
def bucket5g35 : List (List Sig) := [[word18,word55,word86,word122,word310,word360], [word18,word55,word86,word150,word310,word342], [word18,word55,word86,word157,word310,word335], [word18,word55,word86,word184,word219,word401], [word18,word55,word86,word189,word214,word401], [word18,word55,word86,word189,word310,word401], [word18,word55,word99,word184,word214,word401], [word18,word55,word99,word184,word310,word401], [word18,word86,word310,word335,word384,word401], [word55,word86,word184,word203,word310,word335], [word55,word99,word122,word310,word335,word401], [word86,word184,word214,word310,word396,word401]]
def bucket5g36 : List (List Sig) := [[word18,word55,word86,word150,word310,word403], [word18,word55,word86,word184,word322,word401], [word18,word55,word86,word210,word310,word401], [word18,word55,word86,word233,word310,word335], [word55,word86,word190,word214,word310,word401]]
def bucket5g37 : List (List Sig) := [[word18,word43,word86,word310,word401], [word18,word55,word86,word133,word214,word401], [word18,word55,word86,word133,word310,word401], [word18,word55,word86,word184,word214,word405], [word18,word55,word86,word184,word310,word405], [word18,word55,word86,word203,word310,word401], [word18,word86,word122,word279,word310,word401], [word18,word86,word184,word214,word314,word401]]
def bucket5g38 : List (List Sig) := [[word18,word55,word86,word144,word335,word401], [word18,word55,word86,word158,word310,word401], [word18,word55,word86,word357,word401], [word18,word55,word122,word286,word310,word401]]
def bucket5g39 : List (List Sig) := [[word18,word55,word86,word203,word310], [word18,word55,word99,word310,word335,word401], [word18,word86,word214,word219,word310,word401], [word53,word86,word184,word214,word310,word401]]
def bucket5g40 : List (List Sig) := [[word18,word55,word86,word226,word310,word401], [word18,word55,word86,word322,word335,word401], [word55,word86,word99,word122,word310,word401], [word55,word86,word184,word296,word310,word401]]
def bucket5g41 : List (List Sig) := [[word18,word43,word86,word150,word310,word401], [word18,word55,word86,word227,word310,word401], [word18,word55,word86,word310,word335,word405]]
def bucket5g42 : List (List Sig) := [[word18,word55,word86,word150,word357,word401], [word18,word55,word86,word310,word401,word411]]
def bucket5g43 : List (List Sig) := [[word18,word55,word86,word150,word203,word310], [word18,word55,word150,word153,word310,word401], [word55,word86,word214,word233,word310,word401], [word86,word152,word184,word214,word310,word401]]
def bucket5g44 : List (List Sig) := [[word18,word31,word55,word86,word310,word401], [word18,word55,word86,word99,word310,word401], [word55,word86,word296,word310,word335,word401]]
def bucket5g45 : List (List Sig) := [[word18,word55,word86,word118,word310,word401], [word18,word55,word86,word136,word310,word401], [word18,word55,word184,word214,word365,word401], [word18,word55,word184,word310,word365,word401], [word18,word86,word184,word214,word310,word403], [word55,word86,word214,word233,word310]]
def bucket5g46 : List (List Sig) := [[word18,word41,word55,word310,word401], [word18,word55,word86,word121,word310,word401], [word18,word55,word86,word122,word277,word401], [word18,word55,word86,word310,word384,word401], [word86,word184,word214,word279,word310,word401]]
def bucket5g47 : List (List Sig) := [[word55,word184,word214,word286,word310,word401]]
def bucket5g48 : List (List Sig) := [[word17,word55,word86,word214,word310,word401], [word18,word55,word83,word214,word310,word401], [word18,word55,word86,word218,word310,word401], [word18,word86,word277,word310,word401], [word55,word74,word86,word214,word310,word401], [word55,word99,word214,word310,word401]]
def bucket5g49 : List (List Sig) := [[word18,word55,word310,word335,word365,word401], [word18,word86,word122,word214,word233,word310], [word55,word86,word150,word214,word233,word310]]
def bucket5g50 : List (List Sig) := [[word2,word18,word55,word86,word310,word401], [word16,word18,word55,word86,word310,word401], [word18,word41,word55,word150,word310,word401], [word18,word55,word86,word184,word216,word401], [word18,word55,word86,word186,word214,word401], [word18,word55,word86,word186,word310,word401], [word18,word55,word86,word279,word401], [word18,word55,word86,word310,word341,word401], [word18,word74,word86,word184,word214,word401], [word18,word74,word86,word184,word310,word401], [word55,word86,word214,word310,word396,word401]]
def bucket5g51 : List (List Sig) := [[word18,word55,word86,word117,word310,word401], [word18,word86,word182,word214,word310,word401]]
def bucket5g52 : List (List Sig) := [[word18,word55,word86,word310,word314,word401], [word18,word86,word150,word277,word310,word401], [word18,word86,word184,word203,word214,word310], [word55,word99,word150,word214,word310,word401]]
def bucket5g53 : List (List Sig) := [[word9,word55,word86,word310,word401], [word14,word86,word184,word214,word310,word401], [word18,word55,word86,word180,word214,word401], [word18,word55,word86,word180,word310,word401], [word18,word55,word86,word190,word310,word401], [word18,word55,word86,word209,word310,word401], [word18,word55,word86,word214,word259,word401], [word18,word55,word86,word259,word310,word401], [word18,word184,word214,word286,word335,word401], [word55,word86,word184,word212,word310,word401]]
def bucket5g54 : List (List Sig) := [[word18,word55,word86,word150,word279,word401], [word18,word55,word86,word184,word222,word401], [word18,word55,word86,word184,word245,word401], [word18,word55,word86,word292,word310,word401], [word18,word55,word86,word310,word365,word401], [word18,word74,word86,word310,word335,word401]]
def bucket5g55 : List (List Sig) := [[word18,word55,word84,word86,word310,word401], [word18,word55,word86,word125,word310,word401], [word55,word86,word184,word277,word310,word401], [word86,word184,word188,word214,word310,word401]]
def bucket5g56 : List (List Sig) := [[word18,word55,word86,word122,word310,word359], [word18,word55,word86,word150,word310,word341], [word18,word55,word86,word156,word310,word335], [word18,word55,word86,word310,word365]]
def bucket5g57 : List (List Sig) := [[word9,word55,word86,word150,word310,word401], [word15,word18,word55,word86,word310,word401], [word18,word54,word55,word86,word310,word401], [word18,word55,word86,word184,word296,word401], [word18,word55,word86,word196,word214,word401], [word18,word55,word86,word196,word310,word401], [word55,word86,word183,word214,word310,word401], [word55,word86,word184,word189,word214,word401], [word55,word86,word184,word189,word310,word401]]
def bucket5g58 : List (List Sig) := [[word5,word18,word55,word86,word310,word401], [word18,word55,word86,word184,word331,word401], [word18,word55,word86,word184,word346,word401], [word18,word55,word86,word245,word335,word401], [word18,word86,word184,word214,word286,word401]]
def bucket5g59 : List (List Sig) := [[word18,word41,word184,word214,word310,word401], [word18,word55,word86,word157,word310,word401], [word18,word55,word86,word310,word336,word401], [word55,word86,word184,word203,word310,word401], [word55,word86,word277,word310,word335,word401], [word83,word184,word214,word310,word335,word401], [word86,word123,word184,word214,word310,word401]]
def bucket5g60 : List (List Sig) := [[word18,word55,word86,word114,word310,word401], [word18,word55,word86,word150,word310,word365], [word18,word55,word86,word214,word310,word403], [word18,word55,word86,word233,word310,word401]]
def bucket5g61 : List (List Sig) := [[word17,word55,word86,word122,word310,word401], [word18,word55,word83,word122,word310,word401], [word18,word55,word86,word151,word310,word401], [word18,word55,word86,word296,word335,word401], [word18,word86,word310,word384,word401], [word55,word74,word86,word122,word310,word401], [word55,word86,word184,word203,word310], [word55,word99,word122,word310,word401], [word55,word99,word184,word310,word335,word401]]
def bucket5g62 : List (List Sig) := [[word18,word55,word86,word135,word310,word401], [word18,word55,word86,word233,word310], [word18,word55,word86,word331,word335,word401]]
def bucket5g63 : List (List Sig) := [[word0,word18,word55,word86,word310,word401], [word18,word86,word184,word279,word310,word401], [word55,word86,word122,word310,word396,word401]]
def bucket5g64 : List (List Sig) := [[word18,word55,word86,word144,word401], [word18,word55,word184,word214,word286,word401], [word18,word55,word184,word286,word310,word401], [word83,word86,word184,word214,word310,word401]]
def bucket5g65 : List (List Sig) := [[word3,word18,word55,word86,word310,word401], [word17,word18,word55,word86,word310,word401], [word18,word43,word86,word214,word310,word401], [word18,word55,word74,word86,word310,word401], [word18,word55,word86,word310,word401,word405], [word18,word55,word99,word310,word401], [word18,word86,word122,word184,word203,word310], [word18,word86,word150,word310,word384,word401], [word55,word86,word150,word184,word203,word310], [word55,word99,word122,word150,word310,word401]]
def bucket5g66 : List (List Sig) := [[word9,word86,word184,word214,word310,word401], [word18,word55,word86,word109,word310,word401], [word18,word55,word86,word122,word259,word401], [word18,word55,word86,word150,word233,word310], [word18,word55,word86,word214,word357,word401], [word18,word55,word86,word310,word357,word401], [word18,word55,word86,word322,word401], [word55,word86,word99,word184,word310,word401], [word86,word124,word184,word214,word310,word401]]
def bucket5g67 : List (List Sig) := [[word12,word18,word55,word86,word310,word401], [word18,word55,word86,word203,word214,word310], [word18,word55,word86,word310,word396,word401], [word18,word55,word86,word310,word405], [word18,word86,word279,word310,word335,word401]]
def bucket5g68 : List (List Sig) := [[word18,word55,word86,word144,word150,word401], [word18,word55,word286,word310,word335,word401]]
def bucket5g69 : List (List Sig) := [[word18,word55,word99,word150,word310,word401], [word18,word86,word184,word214,word310,word365], [word86,word184,word214,word310,word337,word401]]
def bucket5g70 : List (List Sig) := [[word18,word55,word86,word150,word322,word401], [word55,word83,word184,word214,word310,word401], [word55,word86,word99,word310,word335,word401], [word55,word86,word184,word218,word310,word401], [word55,word86,word188,word214,word310,word401], [word55,word86,word296,word310,word401]]
def bucket5g71 : List (List Sig) := [[word18,word53,word55,word86,word310,word401], [word18,word55,word86,word150,word310,word405], [word18,word55,word86,word211,word310,word401]]
def bucket5g72 : List (List Sig) := [[word18,word55,word86,word184,word277,word401], [word18,word86,word184,word188,word214,word401], [word18,word86,word184,word188,word310,word401], [word55,word86,word184,word186,word214,word401], [word55,word86,word184,word186,word310,word401]]
def bucket5g73 : List (List Sig) := [[word18,word55,word86,word122,word310,word403], [word18,word55,word86,word286,word310,word401]]
def bucket5g74 : List (List Sig) := [[word18,word41,word55,word214,word310,word401], [word18,word55,word86,word183,word310,word401], [word55,word86,word150,word296,word310,word401]]
def bucket5g75 : List (List Sig) := [[word18,word55,word86,word152,word310,word401], [word18,word55,word86,word184,word210,word401], [word18,word55,word122,word310,word359,word401], [word18,word55,word150,word310,word341,word401], [word18,word55,word156,word310,word335,word401], [word18,word55,word310,word365,word401], [word18,word86,word184,word214,word233,word310]]
def bucket5g76 : List (List Sig) := [[word18,word55,word86,word277,word335,word401], [word18,word86,word214,word277,word310,word401], [word55,word86,word214,word219,word310,word401], [word86,word184,word214,word216,word310,word401]]
def bucket5g77 : List (List Sig) := [[word18,word55,word86,word181,word214,word401], [word18,word55,word86,word181,word310,word401]]
def bucket5g78 : List (List Sig) := [[word18,word43,word86,word122,word310,word401], [word18,word55,word86,word214,word279,word401], [word18,word55,word86,word279,word310,word401], [word18,word86,word184,word214,word219,word401], [word18,word99,word184,word214,word310,word401]]
def bucket5g79 : List (List Sig) := [[word18,word55,word86,word122,word357,word401], [word18,word55,word86,word184,word226,word401], [word18,word55,word150,word310,word365,word401], [word18,word86,word214,word233,word310,word335], [word18,word184,word214,word286,word401]]
def bucket5g80 : List (List Sig) := [[word18,word55,word86,word122,word203,word310], [word18,word55,word86,word156,word310,word401], [word18,word55,word310,word335,word338,word401], [word18,word74,word86,word310,word401], [word18,word86,word184,word214,word310,word405]]
def bucket5g81 : List (List Sig) := [[word6,word18,word55,word86,word310,word401], [word9,word55,word86,word214,word310,word401]]
def bucket5g82 : List (List Sig) := [[word55,word86,word184,word214,word310,word403]]
def bucket5g83 : List (List Sig) := [[word18,word55,word85,word86,word310,word401], [word18,word55,word86,word138,word310,word401], [word18,word55,word86,word220,word310,word401], [word18,word150,word184,word214,word286,word401], [word86,word184,word214,word296,word310,word401]]
def bucket5g84 : List (List Sig) := [[word18,word55,word86,word115,word310,word401], [word18,word55,word86,word132,word310,word401], [word18,word55,word86,word136,word184,word401], [word18,word55,word86,word214,word310,word365], [word18,word55,word86,word245,word401], [word18,word74,word86,word150,word310,word401]]
def bucket5g85 : List (List Sig) := [[word14,word18,word55,word86,word310,word401], [word18,word55,word86,word310,word338,word401], [word55,word86,word277,word310,word401], [word83,word184,word214,word310,word401]]
def bucket5g86 : List (List Sig) := [[word55,word86,word122,word214,word233,word310]]
def bucket5g87 : List (List Sig) := [[word17,word55,word86,word184,word310,word401], [word18,word41,word55,word122,word310,word401], [word18,word55,word83,word184,word214,word401], [word18,word55,word83,word184,word310,word401], [word18,word55,word86,word137,word310,word401], [word18,word55,word86,word184,word218,word401], [word18,word55,word86,word188,word214,word401], [word18,word55,word86,word188,word310,word401], [word18,word55,word86,word296,word401], [word43,word86,word184,word214,word310,word401], [word55,word74,word86,word184,word214,word401], [word55,word74,word86,word184,word310,word401], [word55,word99,word184,word310,word401]]
def bucket5g88 : List (List Sig) := [[word18,word55,word86,word127,word310,word401], [word18,word55,word86,word150,word245,word401], [word18,word55,word86,word197,word310,word401], [word18,word55,word86,word331,word401], [word18,word184,word214,word310,word365,word401], [word39,word86,word184,word214,word310,word401], [word55,word86,word182,word214,word310,word401]]
def bucket5g89 : List (List Sig) := [[word18,word55,word86,word310,word360,word401], [word18,word86,word122,word277,word310,word401], [word18,word86,word214,word310,word384,word401], [word55,word86,word150,word277,word310,word401], [word55,word86,word184,word203,word214,word310], [word55,word86,word184,word310,word396,word401], [word55,word99,word122,word214,word310,word401], [word83,word150,word184,word214,word310,word401]]
def bucket5g90 : List (List Sig) := [[word18,word55,word86,word148,word310,word401], [word18,word55,word86,word214,word233,word310]]
def bucket5g91 : List (List Sig) := [[word1,word18,word55,word86,word310,word401], [word17,word55,word86,word310,word335,word401], [word18,word55,word83,word310,word335,word401], [word18,word55,word86,word122,word279,word401], [word18,word55,word86,word123,word310,word401], [word18,word55,word86,word150,word296,word401], [word18,word86,word214,word218,word310,word401], [word34,word86,word184,word214,word310,word401], [word55,word74,word86,word310,word335,word401], [word55,word86,word214,word216,word310,word401], [word55,word99,word150,word184,word310,word401], [word55,word99,word310,word335,word401]]
def bucket5g92 : List (List Sig) := [[word18,word55,word86,word144,word214,word401], [word18,word55,word86,word144,word310,word401], [word18,word55,word86,word150,word331,word401], [word18,word55,word86,word184,word259,word401]]
def bucket5g93 : List (List Sig) := [[word18,word55,word86,word219,word310,word401], [word18,word55,word99,word214,word310,word401], [word18,word86,word104,word184,word214,word401], [word18,word86,word184,word216,word310,word401], [word18,word86,word186,word214,word310,word401], [word18,word86,word279,word310,word401], [word55,word86,word310,word335,word396,word401]]
def bucket5g94 : List (List Sig) := [[word9,word55,word86,word122,word310,word401], [word18,word55,word86,word214,word322,word401], [word18,word55,word86,word310,word322,word401], [word18,word55,word286,word310,word401]]
def bucket5g95 : List (List Sig) := [[word4,word18,word55,word86,word310,word401], [word18,word55,word86,word214,word310,word405], [word18,word86,word184,word203,word310,word335], [word52,word86,word184,word214,word310,word401], [word55,word99,word150,word310,word335,word401]]
def bucket5g96 : List (List Sig) := [[word18,word55,word83,word86,word310,word401], [word18,word55,word86,word259,word335,word401], [word41,word55,word184,word214,word310,word401], [word55,word86,word99,word310,word401]]
def table5 : Array (List (List Sig)) := #[bucket5g0,bucket5g1,bucket5g2,bucket5g3,bucket5g4,bucket5g5,bucket5g6,bucket5g7,bucket5g8,bucket5g9,bucket5g10,bucket5g11,bucket5g12,bucket5g13,bucket5g14,bucket5g15,bucket5g16,bucket5g17,bucket5g18,bucket5g19,bucket5g20,bucket5g21,bucket5g22,bucket5g23,bucket5g24,bucket5g25,bucket5g26,bucket5g27,bucket5g28,bucket5g29,bucket5g30,bucket5g31,bucket5g32,bucket5g33,bucket5g34,bucket5g35,bucket5g36,bucket5g37,bucket5g38,bucket5g39,bucket5g40,bucket5g41,bucket5g42,bucket5g43,bucket5g44,bucket5g45,bucket5g46,bucket5g47,bucket5g48,bucket5g49,bucket5g50,bucket5g51,bucket5g52,bucket5g53,bucket5g54,bucket5g55,bucket5g56,bucket5g57,bucket5g58,bucket5g59,bucket5g60,bucket5g61,bucket5g62,bucket5g63,bucket5g64,bucket5g65,bucket5g66,bucket5g67,bucket5g68,bucket5g69,bucket5g70,bucket5g71,bucket5g72,bucket5g73,bucket5g74,bucket5g75,bucket5g76,bucket5g77,bucket5g78,bucket5g79,bucket5g80,bucket5g81,bucket5g82,bucket5g83,bucket5g84,bucket5g85,bucket5g86,bucket5g87,bucket5g88,bucket5g89,bucket5g90,bucket5g91,bucket5g92,bucket5g93,bucket5g94,bucket5g95,bucket5g96]
def bucket6g0 : List (List Sig) := []
def bucket6g1 : List (List Sig) := []
def bucket6g2 : List (List Sig) := []
def bucket6g3 : List (List Sig) := []
def bucket6g4 : List (List Sig) := []
def bucket6g5 : List (List Sig) := [[word18,word55,word86,word184,word214,word401], [word18,word55,word86,word184,word310,word401]]
def bucket6g6 : List (List Sig) := []
def bucket6g7 : List (List Sig) := [[word18,word55,word86,word122,word214,word310,word401]]
def bucket6g8 : List (List Sig) := []
def bucket6g9 : List (List Sig) := [[word18,word55,word86,word150,word184,word214,word401], [word18,word55,word86,word150,word184,word310,word401], [word18,word55,word86,word310,word335,word401]]
def bucket6g10 : List (List Sig) := []
def bucket6g11 : List (List Sig) := []
def bucket6g12 : List (List Sig) := []
def bucket6g13 : List (List Sig) := [[word18,word55,word86,word150,word310,word335,word401]]
def bucket6g14 : List (List Sig) := []
def bucket6g15 : List (List Sig) := []
def bucket6g16 : List (List Sig) := []
def bucket6g17 : List (List Sig) := []
def bucket6g18 : List (List Sig) := []
def bucket6g19 : List (List Sig) := []
def bucket6g20 : List (List Sig) := []
def bucket6g21 : List (List Sig) := []
def bucket6g22 : List (List Sig) := [[word18,word86,word184,word214,word310,word335,word401]]
def bucket6g23 : List (List Sig) := []
def bucket6g24 : List (List Sig) := []
def bucket6g25 : List (List Sig) := []
def bucket6g26 : List (List Sig) := []
def bucket6g27 : List (List Sig) := []
def bucket6g28 : List (List Sig) := []
def bucket6g29 : List (List Sig) := [[word55,word86,word122,word184,word214,word310,word401]]
def bucket6g30 : List (List Sig) := []
def bucket6g31 : List (List Sig) := []
def bucket6g32 : List (List Sig) := []
def bucket6g33 : List (List Sig) := [[word18,word55,word86,word184,word214,word310,word401]]
def bucket6g34 : List (List Sig) := []
def bucket6g35 : List (List Sig) := [[word18,word55,word86,word310,word401]]
def bucket6g36 : List (List Sig) := []
def bucket6g37 : List (List Sig) := [[word18,word55,word86,word214,word310,word335,word401]]
def bucket6g38 : List (List Sig) := []
def bucket6g39 : List (List Sig) := [[word18,word55,word86,word150,word310,word401]]
def bucket6g40 : List (List Sig) := []
def bucket6g41 : List (List Sig) := []
def bucket6g42 : List (List Sig) := []
def bucket6g43 : List (List Sig) := []
def bucket6g44 : List (List Sig) := []
def bucket6g45 : List (List Sig) := []
def bucket6g46 : List (List Sig) := [[word18,word55,word86,word122,word184,word214,word401], [word18,word55,word86,word122,word184,word310,word401]]
def bucket6g47 : List (List Sig) := []
def bucket6g48 : List (List Sig) := [[word18,word86,word184,word214,word310,word401]]
def bucket6g49 : List (List Sig) := []
def bucket6g50 : List (List Sig) := [[word18,word55,word86,word122,word310,word335,word401]]
def bucket6g51 : List (List Sig) := []
def bucket6g52 : List (List Sig) := [[word18,word86,word150,word184,word214,word310,word401]]
def bucket6g53 : List (List Sig) := []
def bucket6g54 : List (List Sig) := []
def bucket6g55 : List (List Sig) := []
def bucket6g56 : List (List Sig) := [[word18,word55,word86,word122,word150,word310,word335]]
def bucket6g57 : List (List Sig) := []
def bucket6g58 : List (List Sig) := []
def bucket6g59 : List (List Sig) := [[word55,word86,word184,word214,word310,word335,word401]]
def bucket6g60 : List (List Sig) := []
def bucket6g61 : List (List Sig) := []
def bucket6g62 : List (List Sig) := []
def bucket6g63 : List (List Sig) := [[word18,word55,word86,word214,word310,word401]]
def bucket6g64 : List (List Sig) := []
def bucket6g65 : List (List Sig) := []
def bucket6g66 : List (List Sig) := []
def bucket6g67 : List (List Sig) := [[word18,word55,word86,word150,word214,word310,word401]]
def bucket6g68 : List (List Sig) := []
def bucket6g69 : List (List Sig) := []
def bucket6g70 : List (List Sig) := []
def bucket6g71 : List (List Sig) := []
def bucket6g72 : List (List Sig) := []
def bucket6g73 : List (List Sig) := []
def bucket6g74 : List (List Sig) := []
def bucket6g75 : List (List Sig) := [[word18,word55,word122,word150,word310,word335,word401]]
def bucket6g76 : List (List Sig) := [[word18,word55,word86,word122,word310,word401], [word18,word55,word86,word184,word214,word335,word401], [word18,word55,word86,word184,word310,word335,word401]]
def bucket6g77 : List (List Sig) := []
def bucket6g78 : List (List Sig) := []
def bucket6g79 : List (List Sig) := []
def bucket6g80 : List (List Sig) := [[word18,word55,word86,word122,word150,word310,word401]]
def bucket6g81 : List (List Sig) := []
def bucket6g82 : List (List Sig) := []
def bucket6g83 : List (List Sig) := []
def bucket6g84 : List (List Sig) := []
def bucket6g85 : List (List Sig) := [[word55,word86,word184,word214,word310,word401]]
def bucket6g86 : List (List Sig) := []
def bucket6g87 : List (List Sig) := []
def bucket6g88 : List (List Sig) := []
def bucket6g89 : List (List Sig) := [[word18,word86,word122,word184,word214,word310,word401], [word55,word86,word150,word184,word214,word310,word401]]
def bucket6g90 : List (List Sig) := []
def bucket6g91 : List (List Sig) := []
def bucket6g92 : List (List Sig) := []
def bucket6g93 : List (List Sig) := []
def bucket6g94 : List (List Sig) := []
def bucket6g95 : List (List Sig) := []
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

end PEqualNP.Outside.L_meta_19367.Binary
open PEqualNP.Outside.L_meta_19367.Binary in
theorem PEqualNP.Outside.L_meta_19367 (C : PEqualNP.CircuitLowerBounds.Circuit) (hf : PEqualNP.MetaComplexity.FanInTwo C) (hr : Matches C) :
    7 + PEqualNP.NotBracket.notCount C ≤ C.size := actual C hf hr

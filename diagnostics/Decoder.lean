import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_9809.Decoder
open PEqualNP.CircuitLowerBounds
abbrev Sig := BitVec 16
def zero : Sig := 0
def one : Sig := BitVec.allOnes 16
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
def bit (i : Fin 16) (a : Sig) : Bool := a.getLsbD i.val
theorem bit_zero (i) : bit i zero = false := by simp [bit,zero]
theorem bit_one (i) : bit i one = true := by unfold bit one; rw [BitVec.getLsbD_allOnes]; simp
theorem bit_neg (i) (a : Sig) : bit i (neg a) = !(bit i a) := by simp [bit,neg,i.isLt]
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
theorem get_rep {u} (w : List Sig) (i : Nat) : Repr u (w.map (nrm u)) (w.getD i zero) := by
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
inductive Paid (T : Sig) : Nat → Nat → Finset Sig → Prop where
  | stop (hp : proper T) : Paid T 0 0 {T}
  | binary {k n : Nat} {U : Finset Sig} {a b : Sig} {d : Nat}
      (hd : allowed false d) (pa : proper a) (pb : proper b) (ab : a≠b)
      (fresh : bin d a b ∉ insert a (insert b U)) (tail : Paid T k n (insert (bin d a b) U)) :
      Paid T (k+1) n (insert a (insert b U))
  | unary {k n : Nat} {U : Finset Sig} {a : Sig} (pa : proper a)
      (fresh : neg a ∉ insert a U) (tail : Paid T k n (insert (neg a) U)) :
      Paid T k (n+1) (insert a U)
theorem paid_proper {T k n S} (h : Paid T k n S) : ∀ a ∈ S, proper a := by
  induction h with
  | stop hp => simpa using hp
  | binary hd pa pb ab fresh tail ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨pa,pb,fun v hv => ih v (Finset.mem_insert_of_mem hv)⟩
  | unary pa fresh tail ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨pa,fun v hv => ih v (Finset.mem_insert_of_mem hv)⟩
theorem paid_width {T k n S} (h : Paid T k n S) : S.card≤k+1 := by
  induction h with
  | stop hp => simp
  | @binary k n U a b d hd pa pb ab fresh tail ih =>
    have hz : bin d a b ∉ U := fun hv => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hv))
    rw [Finset.card_insert_of_notMem hz] at ih
    have h1 := Finset.card_insert_le (a:=a) (insert b U)
    have h2 := Finset.card_insert_le (a:=b) U
    omega
  | @unary k n U a pa fresh tail ih =>
    have hz : neg a ∉ U := fun hv => fresh (Finset.mem_insert_of_mem hv)
    rw [Finset.card_insert_of_notMem hz] at ih
    have h1 := Finset.card_insert_le (a:=a) U
    omega
theorem paid_zero {T k n S} (h : Paid T k n S) (hn : n=0) : Live false T k S := by
  induction h with
  | stop hp => exact Live.stop hp
  | binary hd pa pb ab fresh tail ih => exact Live.binary hd pa pb ab fresh (ih hn)
  | unary pa fresh tail ih => omega
theorem paid_separates {T k n S} (h : Paid T k n S) {r s : Fin 16} (ht : bit r T ≠ bit s T) :
    ∃ v∈S, bit r v ≠ bit s v := by
  induction h with
  | stop hp => exact ⟨_,by simp,ht⟩
  | @binary k n U a b d hd pa pb ab fresh tail ih =>
    obtain ⟨v,hv,neq⟩ := ih
    rcases Finset.mem_insert.mp hv with rfl | hv
    · by_cases ha : bit r a=bit s a
      · refine ⟨b,by simp,?_⟩
        intro hb
        exact neq (by rw [bit_bin,bit_bin,ha,hb])
      · exact ⟨a,by simp,ha⟩
    · exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hv),neq⟩
  | @unary k n U a pa fresh tail ih =>
    obtain ⟨v,hv,neq⟩ := ih
    rcases Finset.mem_insert.mp hv with rfl | hv
    · refine ⟨a,by simp,?_⟩
      intro eq
      exact neq (by rw [bit_neg,bit_neg,eq])
    · exact ⟨v,Finset.mem_insert_of_mem hv,neq⟩
def origin (w : List Sig) (g : Gate) (z : Sig) :=
  represented w z ∨ (isNot g=false ∧ witness false w z) ∨
  (isNot g=true ∧ ∃ a ∈ w, proper a ∧ z=neg a)
theorem mapped_id (w : List Sig) : w.map (nrm false) = w := by
  change w.map id = w
  exact List.map_id w
theorem physical_gate (w : List Sig) (g : Gate)
    (fit : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2) :
    origin w g (gv w g) := by
  by_cases hn : isNot g=false
  · have r := gate_rep false w g fit (fun _ => hn)
    have m := mapped_id w
    rw [m] at r
    exact r.imp id Or.inl
  · obtain ⟨o,l⟩ := g
    cases o <;> try simp [isNot] at hn
    cases l with
    | nil =>
      left
      exact Or.inr fun h => h.2 (by simp [gv,neg_laws])
    | cons j js =>
      have hread := get_rep (u:=false) w j
      have hr : represented w (w.getD j zero) := by simpa only [Repr,nrm_false,mapped_id] using hread
      rcases operand_cases hr with hz | ho | ⟨hm,hp⟩
      · left
        exact Or.inr fun h => h.2 (by change neg (w.getD j zero)=one; rw [hz,neg_laws.1])
      · left
        exact Or.inr fun h => h.1 (by change neg (w.getD j zero)=zero; rw [ho,neg_laws.2])
      · exact Or.inr (Or.inr ⟨rfl,w.getD j zero,hm,hp,rfl⟩)
theorem paid_pull {T k n S w g z} (run : Paid T k n S) (rep : origin w g z)
    (sub : ∀ a∈S, a∈w++[z]) :
    ∃ k' n' S', k'≤k+(if isNot g then 0 else 1) ∧ n'≤n+(if isNot g then 1 else 0) ∧
      Paid T k' n' S' ∧ ∀ a∈S', a∈w := by
  by_cases hm : z∈S
  · by_cases hw : z∈w
    · refine ⟨k,n,S,by omega,by omega,run,?_⟩
      intro a ha
      rcases (show a∈w ∨ a=z by simpa using sub a ha) with mem | rfl
      · exact mem
      · exact hw
    · let U := S.erase z
      have hu : ∀ a∈U, a∈w := by
        intro a ha
        obtain ⟨ne,mem⟩ := Finset.mem_erase.mp ha
        simpa [ne] using sub a mem
      have tail : Paid T k n (insert z U) := by simpa [U,Finset.insert_erase hm] using run
      rcases rep with rep | ⟨hn,d,a,b,hd,ha,hb,pa,pb,ab,eq⟩ | ⟨hn,a,ha,pa,eq⟩
      · exact False.elim ((rep.resolve_left hw) (paid_proper run z hm))
      · have cov : ∀ a'∈insert a (insert b U), a'∈w := by simpa using And.intro ha (And.intro hb hu)
        have fresh : bin d a b ∉ insert a (insert b U) := fun h => hw (eq.symm ▸ cov _ h)
        exact ⟨k+1,n,_,by simp [hn],by simp [hn],Paid.binary hd pa pb ab fresh (eq ▸ tail),cov⟩
      · have cov : ∀ a'∈insert a U, a'∈w := by simpa using And.intro ha hu
        have fresh : neg a ∉ insert a U := fun h => hw (eq.symm ▸ cov _ h)
        exact ⟨k,n+1,_,by simp [hn],by simp [hn],Paid.unary pa fresh (eq ▸ tail),cov⟩
  · refine ⟨k,n,S,by omega,by omega,run,?_⟩
    intro a ha
    have ne : a≠z := fun h => hm (h ▸ ha)
    simpa [ne] using sub a ha
theorem paid_extract (gs : List Gate) (w : List Sig) (T : Sig)
    (fit : ∀ g∈gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (hp : proper T) (out : T ∈ execute gs w) :
    ∃ k n S, k ≤ gs.countP (fun g => !isNot g) ∧ n ≤ gs.countP isNot ∧
      Paid T k n S ∧ ∀ a∈S, a∈w := by
  induction gs generalizing w with
  | nil => exact ⟨0,0,{T},by simp,by simp,Paid.stop hp,by simpa [execute] using out⟩
  | cons g gs ih =>
    obtain ⟨k,n,S,hk,hn,run,sub⟩ := ih (w++[gv w g]) (fun t ht => fit t (by simp [ht])) out
    obtain ⟨r,t,U,hr,ht,run',cov⟩ := paid_pull run (physical_gate w g (fit g (by simp))) sub
    refine ⟨r,t,U,?_,?_,run',cov⟩
    · rw [List.countP_cons]
      cases he : isNot g <;> simp [he] at hr ⊢ <;> omega
    · rw [List.countP_cons]
      cases he : isNot g <;> simp [he] at ht ⊢ <;> omega
abbrev Row := Fin 16
def Moves (p : Bool) (r s : Row) (a : Sig) : Prop := bit r a=p ∧ bit s a=(!p)
def Oriented (T : Sig) (S : Finset Sig) : Prop :=
  ∃ mark : Sig → Bool, ∀ r s : Row, bit r T=true → bit s T=false → ∃a∈S, Moves (mark a) r s a
theorem move_binary {r s p a b d} (h : allowed false d) (yes : Moves p r s (bin d a b)) :
    Moves p r s a ∨ Moves p r s b := by
  obtain h | h := h
  · obtain rfl | rfl : d=0 ∨ d=1 := by omega
    all_goals cases p <;> cases ar : bit r a <;> cases as' : bit s a <;>
      cases br : bit r b <;> cases bs : bit s b <;> simp_all [Moves,bit_bin]
  · simp at h
theorem move_unary {r s p a} (h : Moves p r s (neg a)) : Moves (!p) r s a := by
  cases p <;> cases ar : bit r a <;> cases as' : bit s a <;> simp_all [Moves,bit_neg]
theorem sign_inventory {T k n S} (h : Paid T k n S) (tight : S.card=k+1) :
    ∃ f : Sig → Bool, (∀ r s : Row, bit r T=true → bit s T=false → ∃a∈S, Moves (f a) r s a) ∧
      (n=0 → ∀v∈S, f v=true) ∧ (n=1 → ∃v∈S, f v=false) := by
  induction h with
  | stop hp =>
    exact ⟨fun _ => true,(fun r s hr hs => ⟨_,by simp,hr,hs⟩), (by simp), (by simp)⟩
  | @binary k n U a b d hd pa pb ab fresh tail ih =>
    have zw : bin d a b ∉ U := fun h => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
    have sz := paid_width tail
    rw [Finset.card_insert_of_notMem zw] at sz
    have h1 := Finset.card_insert_le a (insert b U)
    have h2 := Finset.card_insert_le b U
    have count : U.card=k := by omega
    have na : a∉U := by
      intro ha
      rw [Finset.insert_eq_of_mem (Finset.mem_insert_of_mem ha : a∈insert b U)] at tight
      omega
    have nb : b∉U := by
      intro hb
      rw [Finset.insert_eq_of_mem hb] at tight
      have hh := Finset.card_insert_le a U
      omega
    obtain ⟨f,orient,allpos,negative⟩ := ih (by rw [Finset.card_insert_of_notMem zw,count])
    let mark (v : Sig) := if v=a ∨ v=b then f (bin d a b) else f v
    refine ⟨mark,?_,?_,?_⟩
    · intro r s hr hs
      obtain ⟨v,hv,move⟩ := orient r s hr hs
      rcases Finset.mem_insert.mp hv with rfl | hv
      · rcases move_binary hd move with ha | hb
        · exact ⟨a,by simp,by simpa [mark] using ha⟩
        · exact ⟨b,by simp,by simpa [mark] using hb⟩
      · have ea : v≠a := fun eq => na (eq ▸ hv)
        have eb : v≠b := fun eq => nb (eq ▸ hv)
        exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hv),by simpa [mark,ea,eb] using move⟩
    · intro hn v hv
      by_cases t : v=a ∨ v=b
      · simpa only [mark,if_pos t] using allpos hn (bin d a b) (Finset.mem_insert_self _ _)
      · have um : v∈U := by
          rcases Finset.mem_insert.mp hv with hh | hh
          · exact False.elim (t (Or.inl hh))
          · exact (Finset.mem_insert.mp hh).resolve_left (fun eq => t (Or.inr eq))
        simpa only [mark,if_neg t] using allpos hn v (Finset.mem_insert_of_mem um)
    · intro hn
      obtain ⟨v,mem,sgn⟩ := negative hn
      rcases Finset.mem_insert.mp mem with rfl|mem
      · exact ⟨a,by simp,by simpa [mark] using sgn⟩
      · have ea : v≠a := fun eq => na (eq ▸ mem)
        have eb : v≠b := fun eq => nb (eq ▸ mem)
        exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem mem),by simpa [mark,ea,eb] using sgn⟩

  | @unary k n U a pa fresh tail ih =>
    have zw : neg a ∉ U := fun h => fresh (Finset.mem_insert_of_mem h)
    have sz := paid_width tail
    rw [Finset.card_insert_of_notMem zw] at sz
    have h1 := Finset.card_insert_le a U
    have count : U.card=k := by omega
    have na : a∉U := by
      intro ha
      rw [Finset.insert_eq_of_mem ha] at tight
      omega
    obtain ⟨f,orient,allpos,negative⟩ := ih (by rw [Finset.card_insert_of_notMem zw,count])
    let mark (v : Sig) := if v=a then !(f (neg a)) else f v
    refine ⟨mark,?_,?_,?_⟩
    · intro r s hr hs
      obtain ⟨v,hv,move⟩ := orient r s hr hs
      rcases Finset.mem_insert.mp hv with rfl | hv
      · exact ⟨a,by simp,by simpa [mark] using move_unary move⟩
      · have ea : v≠a := fun eq => na (eq ▸ hv)
        exact ⟨v,Finset.mem_insert_of_mem hv,by simpa [mark,ea] using move⟩
    · intro hn
      omega
    · intro hn
      have hzero : n=0 := by omega
      have htrue := allpos hzero (neg a) (Finset.mem_insert_self _ _)
      exact ⟨a,by simp,by simp [mark,htrue]⟩
def signForced (ws : List Sig) (T a : Sig) (p n : Row) (sgn : Bool) :=
  bit p T && !bit n T && decide (bit p a=sgn) &&
    ws.all (fun b => b==a || bit p b==bit n b)
theorem sign_forced {ws T a p n sgn} (ok : signForced ws T a p n sgn=true)
    {f : Sig → Bool} (ori : ∀ r s : Row, bit r T=true → bit s T=false →
      ∃v∈ws.toFinset, Moves (f v) r s v) : f a=sgn := by
  simp only [signForced,Bool.and_eq_true,Bool.not_eq_true',decide_eq_true_eq,List.all_eq_true] at ok
  obtain ⟨v,hv,first,last⟩ := ori p n ok.1.1.1 ok.1.1.2
  obtain eq | same := Bool.or_eq_true_iff.mp (ok.2 _ (List.mem_toFinset.mp hv))
  · obtain rfl := beq_iff_eq.mp eq
    exact first.symm.trans ok.1.2
  · have e := beq_iff_eq.mp same
    rw [first,last] at e
    have no : ∀ b : Bool, b≠(!b) := by decide
    exact False.elim (no _ e)

-- Parameter levels 0, a, a+b, a+b+c and the two independent new raw inputs.
def bank : List Sig := [43690,52428,65520,65280,61440]
def target : Sig := 0xfea0
theorem noLiveNot : ¬Paid target 4 1 bank.toFinset := by
  intro run
  obtain ⟨f,ori,_,neg⟩ := sign_inventory run (by decide +kernel)
  obtain ⟨v,mem,bad⟩ := neg rfl
  have forced : ∀ w∈bank, ∃ p n : Row, signForced bank target w p n true=true := by decide +kernel
  obtain ⟨p,n,good⟩ := forced v (List.mem_toFinset.mp mem)
  have eq := sign_forced good ori
  simp [bad] at eq
end PEqualNP.Outside.L_meta_9809.Decoder

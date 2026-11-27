import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_9929.LB
open PEqualNP.CircuitLowerBounds
abbrev Sig := BitVec 64
def zero : Sig := 0
def one : Sig := BitVec.allOnes 64
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
def bit (i : Fin 64) (a : Sig) : Bool := a.getLsbD i.val
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
theorem paid_separates {T k n S} (h : Paid T k n S) {r s : Fin 64} (ht : bit r T ≠ bit s T) :
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
abbrev Row := Fin 64
def inputs : List Sig := [0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000]
def sample (r : Row) (j : Fin 6) := bit r (inputs.getD j.val zero)
theorem input_list : List.ofFn (fun j : Fin 6 => inputs.getD j.val zero) = inputs := rfl
theorem sampled (r : Row) : List.ofFn (sample r) = inputs.map (bit r) := by
  rw [←input_list]
  rw [List.map_ofFn]
  rfl
theorem table_eval (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (i : Nat) (r : Row) : bit r ((execute C.gates inputs).getD i zero) =
      (C.wires (List.ofFn (sample r))).getD i false := by
  rw [←b_read,execute_bits _ _ _ (fun g hg => (h g hg).1),sampled]
  rfl
def target : Sig := 0x80c0e0f0f8fcfe
def targetFn (x : Fin 6 → Bool) := decide ((1 * (x 3).toNat + 2 * (x 4).toNat + 4 * (x 5).toNat) < (1 * (x 0).toNat + 2 * (x 1).toNat + 4 * (x 2).toNat))
set_option maxRecDepth 16000
set_option maxHeartbeats 0
theorem target_eq : ∀ r : Row, bit r target=targetFn (sample r) := by decide +kernel
theorem proper_target : proper target := by unfold proper; decide +kernel
def absent (i : Fin 6) : Row := ([0,0,0,1,1,1] : List Row).getD i.val 0
def present (i : Fin 6) : Row := Fin.ofNat 64 ((absent i).val ||| (1 <<< i.val))
theorem required :
    (∀ i : Fin 6, bit (absent i) target ≠ bit (present i) target) ∧
    (∀ i j : Fin 6, i ≠ j →
      bit (absent i) (inputs.getD j.val zero)=bit (present i) (inputs.getD j.val zero)) := by
  decide +kernel
theorem initial (C : Circuit) (fit : PEqualNP.MetaComplexity.FanInTwo C)
    (ev : ∀ x : Fin 6 → Bool, C.eval (List.ofFn x)=targetFn x) :
    ∃ k n, k ≤ C.gates.countP (fun g => !isNot g) ∧ n ≤ C.gates.countP isNot ∧
      Paid target k n inputs.toFinset := by
  have eq : (execute C.gates inputs).getD C.output zero=target := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    let r : Row := ⟨i,hi⟩
    exact (table_eval C fit C.output r).trans ((ev (sample r)).trans (target_eq r).symm)
  have rep := get_rep (u:=false) (execute C.gates inputs) C.output
  rw [eq] at rep
  have haveOut : represented (execute C.gates inputs) target := by simpa only [Repr,nrm_false,mapped_id] using rep
  obtain ⟨k,n,S,hk,hn,run,cov⟩ := paid_extract C.gates inputs target fit proper_target
    (haveOut.resolve_right (fun h => h proper_target))
  have idx (v : Sig) (hv : v ∈ inputs) : ∃ i : Fin 6, inputs.getD i.val zero = v := by
    rw [←input_list] at hv
    exact List.mem_ofFn.mp hv
  have same : S=inputs.toFinset := by
    ext v
    constructor
    · exact fun h => List.mem_toFinset.mpr (cov v h)
    · intro hv
      obtain ⟨i,rfl⟩ := idx v (List.mem_toFinset.mp hv)
      obtain ⟨u,hu,hd⟩ := paid_separates run (required.1 i)
      obtain ⟨j,rfl⟩ := idx u (cov u hu)
      by_cases he : i=j
      · simpa [he] using hu
      · exact False.elim (hd (required.2 i j he))
  exact ⟨k,n,hk,hn,same ▸ run⟩
def reserve (S : Finset Sig) (a b : Sig) (ka kb : Bool) : Finset Sig :=
  S.filter (fun v => (v≠a ∨ ka=true) ∧ (v≠b ∨ kb=true))
theorem reserve_binary (U : Finset Sig) (a b : Sig) (ab : a≠b) :
    reserve (insert a (insert b U)) a b (decide (a∈U)) (decide (b∈U)) = U := by
  ext v
  by_cases ha : v=a <;> by_cases hb : v=b <;> simp_all [reserve]
theorem reserve_unary (U : Finset Sig) (a : Sig) :
    reserve (insert a U) a a (decide (a∈U)) (decide (a∈U)) = U := by
  ext v
  by_cases ha : v=a <;> simp_all [reserve]
abbrev ProofCut := Nat → Nat → Finset Sig → Bool
def within (T : Sig) (K N : Nat) (S : Finset Sig) := ∀ k, k≤K → ∀ n, n≤N → ¬Paid T k n S
def nextCut (check : ProofCut) (k n : Nat) (S : Finset Sig) (z : Sig) (U : Finset Sig) :=
  if z∈S ∨ z=zero ∨ z=one ∨ k+1 < (insert z U).card then true else check k n (insert z U)
theorem nextCut_use {check K N S z U} (ok : nextCut check K N S z U=true)
    {T k n} (fresh : z∉S) (good : Paid T k n (insert z U)) (hk : k≤K) : check K N (insert z U)=true := by
  have properZ := paid_proper good z (Finset.mem_insert_self _ _)
  have width := paid_width good
  simpa [nextCut,fresh,properZ.1,properZ.2,show ¬K+1 < (insert z U).card by omega] using ok
def binaryPage (check : ProofCut) (K N : Nat) (ws : List Sig) :=
  let S := ws.toFinset
  ws.all fun a => ws.all fun b => decide (∀ d : Fin 2, ∀ka kb : Bool,
    a=b ∨ nextCut check (K-1) N S (bin d.val a b) (reserve S a b ka kb) = true)
def unaryPage (check : ProofCut) (K N : Nat) (ws : List Sig) :=
  let S := ws.toFinset
  ws.all fun a => decide (∀ka : Bool,
    nextCut check K (N-1) S (neg a) (reserve S a a ka ka) = true)
def verifyStep (T : Sig) (check : ProofCut) (K N : Nat) (ws : List Sig) :=
  decide (T ∉ ws.toFinset) && (decide (K=0) || binaryPage check K N ws) &&
    (decide (N=0) || unaryPage check K N ws)
theorem step_complete {T check K N ws} (ok : verifyStep T check K N ws=true)
    (claim : ∀ k n P, check k n P=true → within T k n P) : within T K N ws.toFinset := by
  simp only [verifyStep,Bool.and_eq_true,Bool.or_eq_true,decide_eq_true_eq] at ok
  intro k hk n hn run
  generalize he : ws.toFinset = S at run
  cases run with
  | stop hp => exact ok.1.1 (he.symm ▸ Finset.mem_singleton_self _)
  | @binary k' n' U a b d hd pa pb ab fresh tail =>
    have pos : K≠0 := by omega
    have tests := ok.1.2.resolve_left pos
    have aok := List.all_eq_true.mp tests a (List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _))
    have bok := List.all_eq_true.mp aok b (List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)))
    have hd' : d<2 := hd.resolve_right (by simp)
    have hit := (of_decide_eq_true bok ⟨d,hd'⟩ (decide (a∈U)) (decide (b∈U))).resolve_left ab
    change nextCut check (K-1) N ws.toFinset (bin d a b) (reserve ws.toFinset a b _ _) = true at hit
    rw [he,reserve_binary U a b ab] at hit
    exact claim _ _ _ (nextCut_use hit fresh tail (by omega)) _ (by omega) _ hn tail
  | @unary k' n' U a pa fresh tail =>
    have pos : N≠0 := by omega
    have tests := ok.2.resolve_left pos
    have aok := List.all_eq_true.mp tests a (List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _))
    have hit := of_decide_eq_true aok (decide (a∈U))
    change nextCut check K (N-1) ws.toFinset (neg a) (reserve ws.toFinset a a _ _) = true at hit
    rw [he,reserve_unary U a] at hit
    exact claim _ _ _ (nextCut_use hit fresh tail hk) _ hk _ (by omega) tail
def Moves (p : Bool) (r s : Row) (a : Sig) : Prop := bit r a=p ∧ bit s a=(!p)
theorem move_binary {r s p a b d} (h : allowed false d) (yes : Moves p r s (bin d a b)) :
    Moves p r s a ∨ Moves p r s b := by
  obtain h | h := h
  · obtain rfl | rfl : d=0 ∨ d=1 := by omega
    all_goals cases p <;> cases ar : bit r a <;> cases as' : bit s a <;>
      cases br : bit r b <;> cases bs : bit s b <;> simp_all [Moves,bit_bin]
  · simp at h
theorem move_unary {r s p a} (h : Moves p r s (neg a)) : Moves (!p) r s a := by
  cases p <;> cases ar : bit r a <;> cases as' : bit s a <;> simp_all [Moves,bit_neg]
def Ord (S : Finset Sig) (r s : Row) := ∀ a∈S, ¬Moves true r s a
theorem ord_bin {U : Finset Sig} {a b d r s} (hd : allowed false d)
    (h : Ord (insert a (insert b U)) r s) : Ord (insert (bin d a b) U) r s := by
  intro v hv mv
  rcases Finset.mem_insert.mp hv with rfl | hv
  · rcases move_binary hd mv with ha|hb
    · exact h a (by simp) ha
    · exact h b (by simp) hb
  · exact h v (by simp [hv]) mv
theorem zero_ord {T k n S r s} (h : Paid T k n S) (hn : n=0) (ord : Ord S r s) : ¬Moves true r s T := by
  induction h with
  | stop hp => exact ord _ (by simp)
  | binary hd pa pb ab fresh tail ih => exact ih hn (ord_bin hd ord)
  | unary pa fresh tail ih => omega
theorem one_ord {T k n S i j l m} (h : Paid T k n S) (hn : n≤1)
    (hij : Ord S i j) (hjl : Ord S j l) (hlm : Ord S l m)
    (firstDrop : Moves true i j T) : ¬Moves true l m T := by
  induction h with
  | stop hp => exact False.elim (hij _ (by simp) firstDrop)
  | binary hd pa pb ab fresh tail ih =>
    exact ih hn (ord_bin hd hij) (ord_bin hd hjl) (ord_bin hd hlm)
  | @unary k n U a pa fresh tail ih =>
    have z : n=0 := by omega
    by_cases p : Moves true i j (neg a)
    · apply zero_ord tail z
      intro w hw mv
      rcases Finset.mem_insert.mp hw with rfl | hm
      · have pj := (move_unary p).2
        have pl := (move_unary mv).1
        exact hjl a (by simp) ⟨by simpa using pj,by simpa using pl⟩
      · exact hlm w (by simp [hm]) mv
    · apply False.elim
      apply zero_ord tail z _ firstDrop
      intro w hw mv
      rcases Finset.mem_insert.mp hw with rfl | hm
      · exact p mv
      · exact hij w (by simp [hm]) mv

def allSet (S : Finset Sig) (p : Sig → Bool) := (S.filter (fun v => p v = false)).card == 0
theorem allSet_iff {S : Finset Sig} {p : Sig → Bool} :
    allSet S p=true ↔ ∀a∈S,p a=true := by
  simp only [allSet,beq_iff_eq,Finset.card_eq_zero]
  constructor
  · intro h a ha
    cases e : p a with
    | true => rfl
    | false =>
      have m : a∈S.filter (fun v => p v=false) := Finset.mem_filter.mpr ⟨ha,e⟩
      rw [h] at m
      simp at m
  · intro h
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro a m
    obtain ⟨ha,he⟩ := Finset.mem_filter.mp m
    exact Bool.noConfusion ((h a ha).symm.trans he)
def ordb (S : Finset Sig) (r s : Row) := allSet S (fun a => !bit r a || bit s a)
theorem ord_check {S r s} (ok : ordb S r s=true) : Ord S r s := by
  intro a ha mv
  have sub := allSet_iff.mp ok a ha
  simp [mv.1,mv.2] at sub
theorem two_not (C : Circuit) (fit : PEqualNP.MetaComplexity.FanInTwo C)
    (ok : ∀ x : Fin 6 → Bool, C.eval (List.ofFn x)=targetFn x) :
    2 ≤ C.gates.countP isNot := by
  obtain ⟨k,n,hk,hn,h⟩ := initial C fit ok
  by_contra low
  have bad := one_ord (i:=1) (j:=9) (l:=11) (m:=27) h (by omega)
    (ord_check (by decide +kernel)) (ord_check (by decide +kernel)) (ord_check (by decide +kernel))
    (by unfold Moves; decide +kernel)
  exact bad (by unfold Moves; decide +kernel)
abbrev Small := BitVec 8
def flat (v : Small) : Bool := v==0 || v==BitVec.allOnes 8
def charge (v : Small) : Nat := (flat v).toNat
def mass8 (f : Sig → Small) (S : Finset Sig) := ∑ a∈S, charge (f a)
theorem mass_le (f : Sig → Small) (a : Sig) (S : Finset Sig) :
    mass8 f (insert a S) ≤ charge (f a)+mass8 f S := by
  by_cases h : a∈S
  · simp [Finset.insert_eq_of_mem h]
  · simp [mass8,Finset.sum_insert h]
theorem mass_fresh (f : Sig → Small) (a : Sig) (S : Finset Sig) (h : a∉S) :
    mass8 f (insert a S) = charge (f a)+mass8 f S := by simp [mass8,Finset.sum_insert h]
def calc8 (d : Nat) (x y : Small) := if d=0 then x &&& y else x ||| y
def domain8 (bank : List Small) := (0 : Small) :: (BitVec.allOnes 8) :: (bank ++ bank.map (fun a => ~~~a))
def has8 (bank : List Small) (w : Small) := w∈domain8 bank
theorem has8_neg {bank v} (h : has8 bank v) : has8 bank (~~~v) := by
  simp only [has8,domain8,List.mem_cons,List.mem_append,List.mem_map] at h ⊢
  rcases h with h|h|h|⟨a,ha,h⟩
  · subst v; exact Or.inr (Or.inl rfl)
  · subst v; exact Or.inl rfl
  · exact Or.inr (Or.inr (Or.inr ⟨_,h,rfl⟩))
  · subst v; exact Or.inr (Or.inr (Or.inl (by simpa using ha)))
theorem has8_larger {bank v} (z : Small) (h : has8 bank v) : has8 (z::bank) v := by
  simp [has8,domain8] at h ⊢
  tauto
theorem has8_head (z : Small) (bank : List Small) : has8 (z::bank) z := by simp [has8,domain8]
structure Morph8 (f : Sig → Small) : Prop where
  invert : ∀ a, f (neg a) = ~~~(f a)
  binary : ∀d a b, allowed false d → f (bin d a b)=calc8 d (f a) (f b)
inductive R8 (T : Small) : Nat → List Small → Prop where
  | done {bank} (ht : has8 bank T) : R8 T 0 bank
  | step {bank x y n} (d : Nat) (hd : d<2) (hx : has8 bank x) (hy : has8 bank y)
      (tail : R8 T n (calc8 d x y::bank)) : R8 T (n+1) bank
theorem high8 : ∀ x : Small,
    ((255 : Small) &&& x)=x ∧ (x &&& 255)=x ∧ (255 ||| x)=255 ∧ (x ||| 255)=255 := by decide +kernel
theorem low8 : ∀v : Small, ((0 : Small) &&& v)=0 ∧ (v &&& 0)=0 ∧ (0 ||| v)=v ∧ (v ||| 0)=v := by decide +kernel
theorem const_extend (d : Nat) (x y : Small) (bank : List Small) (hx : has8 bank x)
    (hy : has8 bank y) (h : flat x=true ∨ flat y=true) : has8 bank (calc8 d x y) := by
  have zeroIn : has8 bank 0 := by simp [has8,domain8]
  have oneIn : has8 bank (255 : Small) := by simp [has8,domain8]
  simp only [flat,Bool.or_eq_true,beq_iff_eq] at h
  by_cases hd : d=0
  · rw [calc8,if_pos hd]
    rcases h with (rfl|rfl)|(rfl|rfl)
    · rw [(low8 y).1]; exact zeroIn
    · rw [show (BitVec.allOnes 8 &&& y)=y from (high8 y).1]; exact hy
    · rw [(low8 x).2.1]; exact zeroIn
    · rw [show (x &&& BitVec.allOnes 8)=x from (high8 x).2.1]; exact hx
  · rw [calc8,if_neg hd]
    rcases h with (rfl|rfl)|(rfl|rfl)
    · rw [(low8 y).2.2.1]; exact hy
    · rw [show (BitVec.allOnes 8 ||| y)=255 from (high8 y).2.2.1]; exact oneIn
    · rw [(low8 x).2.2.2]; exact hx
    · rw [show (x ||| BitVec.allOnes 8)=255 from (high8 x).2.2.2]; exact oneIn
theorem charge_le (v : Small) : charge v ≤ 1 := by unfold charge; cases flat v <;> decide
theorem charge_neg (v : Small) : charge (~~~v) = charge v := by
  revert v
  decide +kernel
theorem binary_charge (d : Nat) (x y : Small) :
    charge x + charge y ≤ 1 + charge (calc8 d x y) := by
  by_cases xx : flat x=true <;> by_cases yy : flat y=true
  · simp only [flat,Bool.or_eq_true,beq_iff_eq] at xx yy
    rcases xx with rfl|rfl <;> rcases yy with rfl|rfl <;> by_cases h : d=0 <;>
      simp [charge,flat,calc8,h]
  all_goals simp_all [charge]
theorem paid_project {T k n S} (run : Paid T k n S) {f : Sig → Small} (m : Morph8 f)
    (proper8 : flat (f T)=false) (bank : List Small) (supply8 : ∀ a∈S, has8 bank (f a)) :
    ∃ p, R8 (f T) p bank ∧ p+mass8 f S ≤ k := by
  induction run generalizing bank with
  | stop hp => exact ⟨0,.done (supply8 _ (by simp)),by simp [mass8,charge,proper8]⟩
  | @unary k n U a pa fresh tail ih =>
    have zf : neg a∉U := fun h => fresh (by simp [h])
    have sup : ∀ v∈insert (neg a) U, has8 bank (f v) := by
      intro v hv
      rcases Finset.mem_insert.mp hv with rfl|hu
      · rw [m.invert]; exact has8_neg (supply8 _ (by simp))
      · exact supply8 _ (by simp [hu])
    obtain ⟨p,r,le⟩ := ih bank sup
    rw [mass_fresh _ _ _ zf,m.invert,charge_neg] at le
    exact ⟨p,r,by have := mass_le f a U; omega⟩
  | @binary k n U a b d hd pa pb ab fresh tail ih =>
    let z := bin d a b
    have zf : z∉U := fun h => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
    have ze : f z=calc8 d (f a) (f b) := m.binary _ _ _ hd
    have ha := supply8 a (by simp)
    have hb := supply8 b (by simp)
    have tot : mass8 f (insert a (insert b U)) ≤ charge (f a)+charge (f b)+mass8 f U := by
      have aa := mass_le f a (insert b U)
      have bb := mass_le f b U
      omega
    by_cases c : flat (f a)=true ∨ flat (f b)=true
    · have sup : ∀v∈insert z U, has8 bank (f v) := by
        intro v hv
        rcases Finset.mem_insert.mp hv with rfl|hu
        · rw [ze]; exact const_extend d _ _ _ ha hb c
        · exact supply8 _ (by simp [hu])
      obtain ⟨p,r,le⟩ := ih bank sup
      change p+mass8 f (insert z U) ≤ k at le
      rw [mass_fresh _ _ _ zf,ze] at le
      exact ⟨p,r,by have := binary_charge d (f a) (f b); omega⟩
    · have xa : flat (f a)=false := Bool.eq_false_iff.mpr fun h => c (Or.inl h)
      have xb : flat (f b)=false := Bool.eq_false_iff.mpr fun h => c (Or.inr h)
      have sup : ∀v∈insert z U, has8 (f z::bank) (f v) := by
        intro v hv
        rcases Finset.mem_insert.mp hv with rfl|hu
        · exact has8_head _ _
        · apply has8_larger; exact supply8 _ (by simp [hu])
      obtain ⟨p,r,le⟩ := ih (f z::bank) sup
      change p+mass8 f (insert z U) ≤ k at le
      rw [mass_fresh _ _ _ zf] at le
      rw [ze] at r
      have hd' := hd.resolve_right (by simp)
      simp only [charge,xa,xb,Bool.toNat_false,Nat.zero_add] at tot
      exact ⟨p+1,.step d hd' ha hb r,by omega⟩
namespace SmallLive
open PEqualNP.CircuitLowerBounds
abbrev Sig := BitVec 8
def zero : Sig := 0
def one : Sig := BitVec.allOnes 8
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
def bit (i : Fin 8) (a : Sig) : Bool := a.getLsbD i.val
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
def base : List Sig := [170,204,240]
def goal : Sig := 232
theorem hr8 {w bank} (h : has8 bank w) : Repr true (bank.map (nrm true)) w := by
  simp only [has8,domain8,List.mem_cons,List.mem_append,List.mem_map] at h
  rcases h with rfl|rfl|hm|⟨a,ha,rfl⟩
  · exact repr_const (Or.inl rfl)
  · exact repr_const (Or.inr rfl)
  · exact Or.inl (List.mem_map_of_mem hm)
  · apply repr_neg
    exact Or.inl (List.mem_map_of_mem ha)
theorem convert8 {p bank} (run : R8 goal p bank) :
    ∃l S, l≤p ∧ Live true goal l S ∧ ∀v∈S,v∈bank.map (nrm true) := by
  induction run with
  | done h =>
    have nr : nrm true goal=goal := by decide +kernel
    have pg : proper goal := by unfold proper; decide +kernel
    have rep := hr8 h
    change represented _ (nrm true goal) at rep
    rw [nr] at rep
    exact ⟨0,{goal},by omega,Live.stop pg,by simpa using rep.resolve_right (by tauto)⟩
  | @step bank x y k d hd ha hb tail ih =>
    obtain ⟨l,S,le,run,sub⟩ := ih
    let op := decide (d=1)
    have eq : calc8 d x y = prime op x y := by
      obtain rfl|rfl : d=0 ∨ d=1 := by omega
      all_goals rfl
    rw [eq,List.map_cons] at sub
    have rep := prime_rep op (hr8 ha) (hr8 hb)
    obtain ⟨q,U,hq,r,hu⟩ := pull_gate (c:=1) run (rep.imp id (fun h => ⟨rfl,h⟩))
      (fun a hm => by simpa [or_comm] using sub a hm)
    exact ⟨q,U,by omega,r,hu⟩
theorem sep8 {T k S} (p : Live true T k S) (r s : Fin 8) (ne : bit r T≠bit s T) :
    ∃w∈S,bit r w≠bit s w := by
  induction p using Live.ind with
  | stop hp => exact ⟨_,by simp,ne⟩
  | @binary k U a b d hd pa pb ab fresh tail ih =>
    obtain ⟨w,hw,hn⟩ := ih
    rcases Finset.mem_insert.mp hw with rfl|hm
    · by_cases ha : bit r a=bit s a
      · refine ⟨b,by simp,?_⟩
        intro hb
        exact hn (by rw [bit_bin,bit_bin,ha,hb])
      · exact ⟨a,by simp,ha⟩
    · exact ⟨w,by simp [hm],hn⟩
def separates (T : Sig) (S : Finset Sig) := decide (∀r s : Fin 8, bit r T ≠ bit s T →
  (S.filter (fun w => bit r w ≠ bit s w)).Nonempty)
theorem sepB {T k S} (h : Live true T k S) : separates T S=true := by
  apply decide_eq_true
  intro r s ne
  obtain ⟨w,hw,hh⟩ := sep8 h r s ne
  exact ⟨w,Finset.mem_filter.mpr ⟨hw,hh⟩⟩
def sets : List (Finset Sig) := [∅,{170},{204},{240},{170,204},{170,240},{204,240},{170,204,240}]
theorem sub_list {S} (h : ∀w∈S,w∈base) : S∈sets := by
  have sub : S⊆base.toFinset := fun w hw => List.mem_toFinset.mpr (h w hw)
  have power := Finset.mem_powerset.mpr sub
  have eq : base.toFinset.powerset=sets.toFinset := by decide +kernel
  exact List.mem_toFinset.mp (eq ▸ power)
def rootLaw := sets.all (fun S => !separates goal S || decide (S=base.toFinset))
theorem rootLaw_true : rootLaw=true := by decide +kernel
def childLaw := base.all fun a => base.all fun b => (List.range 4).all fun d => sets.all fun U =>
  a==b || (bin d a b ∈ base) || decide (3 < (insert (bin d a b) U).card) ||
    !separates goal (insert (bin d a b) U) || decide (insert a (insert b U) ≠ base.toFinset)
theorem childLaw_true : childLaw=true := by decide +kernel
theorem noLive {k S} (h : Live true goal k S) (low : k≤3) (sub : ∀v∈S,v∈base) : False := by
  have h0 := List.all_eq_true.mp rootLaw_true S (sub_list sub)
  have eq : S=base.toFinset := by simpa [sepB h] using h0
  cases k with
  | zero =>
    have eq' : S={goal} := h.1
    exact (by decide +kernel : base.toFinset≠{goal}) (eq.symm.trans eq')
  | succ k =>
    obtain ⟨U,a,b,d,hd,e,pa,pb,ab,fresh,tail⟩ := h
    have same := e.symm.trans eq
    have aa := sub a (e.symm ▸ Finset.mem_insert_self a (insert b U))
    have bb := sub b (e.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self b U))
    have uu := sub_list (S:=U) (fun w hw => sub w (e.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hw)))
    have dd : d<4 := by rcases hd with h|h; omega; exact h.2
    have h1 := List.all_eq_true.mp childLaw_true a aa
    have h2 := List.all_eq_true.mp h1 b bb
    have h3 := List.all_eq_true.mp h2 d (List.mem_range.mpr dd)
    have h4 := List.all_eq_true.mp h3 U uu
    have missing : bin d a b∉base := by
      intro hm; exact fresh (same.symm ▸ List.mem_toFinset.mpr hm)
    have width := live_size tail
    have upper : ¬3 < (insert (bin d a b) U).card := by omega
    simp [ab,missing,upper,sepB tail,same] at h4
theorem smallPrice {p} (r : R8 goal p base) : 4≤p := by
  by_contra low
  obtain ⟨l,S,hl,h,sub⟩ := convert8 r
  have eq : base.map (nrm true)=base := by decide +kernel
  rw [eq] at sub
  exact noLive h (by omega) sub
end SmallLive
def base8 : List Small := [170,204,240]
def maj8 : Small := 232
theorem majPrice {p} (r : R8 maj8 p base8) : 4≤p := SmallLive.smallPrice r
def project8 (rs : Fin 8 → Row) (a : Sig) : Small :=
  (BitVec.ofBoolListLE (List.ofFn fun i => bit (rs i) a)).cast List.length_ofFn
theorem project_at (rs : Fin 8 → Row) (a : Sig) (i : Fin 8) :
    (project8 rs a).getLsbD i.val=bit (rs i) a := by
  simp only [project8,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [i.isLt]
theorem morph_of (rs : Fin 8 → Row) : Morph8 (project8 rs) := by
  constructor
  · intro a
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have h := project_at rs (neg a) ⟨i,hi⟩
    rw [bit_neg,←project_at rs a ⟨i,hi⟩] at h
    rw [h]
    simp [hi]
  · intro d a b hd
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have h := project_at rs (bin d a b) ⟨i,hi⟩
    rw [bit_bin,←project_at rs a ⟨i,hi⟩,←project_at rs b ⟨i,hi⟩] at h
    rw [h]
    obtain rfl|rfl : d=0 ∨ d=1 := by rcases hd with h|h; omega; simp at h
    all_goals simp [calc8,hi]
structure Chart where
  rows : Fin 8 → Row
  targetOK : project8 rows target=maj8
def faceCut (c : Chart) (K : Nat) (S : Finset Sig) : Bool :=
  allSet S (fun a => decide (project8 c.rows a ∈ domain8 base8)) && decide (K < 4+mass8 (project8 c.rows) S)
theorem face_sound {c K N S} (ok : faceCut c K S=true) : within target K N S := by
  intro k hk n _ h
  simp only [faceCut,Bool.and_eq_true,allSet_iff,decide_eq_true_eq] at ok
  have proper8 : flat (project8 c.rows target)=false := by rw [c.targetOK]; decide
  obtain ⟨p,r,le⟩ := paid_project h (morph_of _) proper8 base8 ok.1
  rw [c.targetOK] at r
  have fee := majPrice r
  have bound := ok.2
  omega

structure Closed where
  K : Nat
  N : Nat
  ws : List Sig
  bad : within target K N ws.toFinset
inductive Hint where
  | trivial
  | equal (i j : Row)
  | drop (i j : Row)
  | four (i j l m : Row)
  | face (idx : Nat)
  | link (idx : Nat)
def isDrop (r s : Row) := bit r target && !bit s target
theorem isDrop_ok {r s} (h : isDrop r s=true) : Moves true r s target := by
  simpa [isDrop,Moves] using h
def verdict (chart : Nat → Chart) (links : Array Closed) (h : Hint) (K N : Nat) (S : Finset Sig) : Bool :=
  match h with
  | .trivial => false
  | .equal i j => (bit i target != bit j target) && allSet S (fun a => decide (bit i a=bit j a))
  | .drop i j => decide (N=0) && isDrop i j && ordb S i j
  | .four i j l m => decide (N≤1) && isDrop i j && isDrop l m && ordb S i j && ordb S j l && ordb S l m
  | .face j => faceCut (chart j) K S
  | .link j => match links[j]? with
    | none => false
    | some v => decide (S=v.ws.toFinset ∧ K≤v.K ∧ N≤v.N)
theorem verdict_ok {chart links h K N S} (yes : verdict chart links h K N S=true) :
    within target K N S := by
  cases h with
  | trivial => simp [verdict] at yes
  | equal i j =>
    simp only [verdict,Bool.and_eq_true,bne_iff_ne,allSet_iff,decide_eq_true_eq] at yes
    intro k hk n hn run
    obtain ⟨v,hv,ne⟩ := paid_separates run yes.1
    exact ne (yes.2 v hv)
  | drop i j =>
    simp only [verdict,Bool.and_eq_true,decide_eq_true_eq] at yes
    intro k hk n hn run
    exact zero_ord run (by have := yes.1.1; omega) (ord_check yes.2) (isDrop_ok yes.1.2)
  | four i j l m =>
    simp only [verdict,Bool.and_eq_true,decide_eq_true_eq] at yes
    intro k hk n hn run
    apply one_ord run (by have := yes.1.1.1.1.1; omega) (ord_check yes.1.1.2)
      (ord_check yes.1.2) (ord_check yes.2) (isDrop_ok yes.1.1.1.1.2) (isDrop_ok yes.1.1.1.2)
  | face j => exact face_sound yes
  | link j =>
    simp only [verdict] at yes
    split at yes
    · contradiction
    · rename_i v h
      obtain ⟨he,hk,hn⟩ := of_decide_eq_true yes
      rw [he]
      exact fun k k' n n' => v.bad k (k'.trans hk) n (n'.trans hn)
def tagBinary (check : Sig → Sig → Nat → Bool → Bool → ProofCut) (K N : Nat) (ws : List Sig) :=
  let S := ws.toFinset
  ws.all fun a => ws.all fun b => decide (∀ d : Fin 2, ∀ka kb : Bool,
    a=b ∨ nextCut (check a b d.val ka kb) (K-1) N S (bin d.val a b) (reserve S a b ka kb) = true)
def tagUnary (check : Sig → Sig → Nat → Bool → Bool → ProofCut) (K N : Nat) (ws : List Sig) :=
  let S := ws.toFinset
  ws.all fun a => decide (∀ka : Bool,
    nextCut (check a a 2 ka ka) K (N-1) S (neg a) (reserve S a a ka ka) = true)
def tagStep (T : Sig) (check : Sig → Sig → Nat → Bool → Bool → ProofCut) (K N : Nat) (ws : List Sig) :=
  decide (T ∉ ws.toFinset) && (decide (K=0) || tagBinary check K N ws) &&
    (decide (N=0) || tagUnary check K N ws)
theorem tag_sound {T check K N ws} (ok : tagStep T check K N ws=true)
    (claim : ∀ a b d ka kb k n P, check a b d ka kb k n P=true → within T k n P) : within T K N ws.toFinset := by
  simp only [tagStep,Bool.and_eq_true,Bool.or_eq_true,decide_eq_true_eq] at ok
  intro k hk n hn run
  generalize he : ws.toFinset = S at run
  cases run with
  | stop hp => exact ok.1.1 (he.symm ▸ Finset.mem_singleton_self _)
  | @binary k' n' U a b d hd pa pb ab fresh tail =>
    have pos : K≠0 := by omega
    have tests := ok.1.2.resolve_left pos
    have aok := List.all_eq_true.mp tests a (List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _))
    have bok := List.all_eq_true.mp aok b (List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)))
    have hd' : d<2 := hd.resolve_right (by simp)
    have hit := (of_decide_eq_true bok ⟨d,hd'⟩ (decide (a∈U)) (decide (b∈U))).resolve_left ab
    change nextCut (check a b d _ _) (K-1) N ws.toFinset (bin d a b) (reserve ws.toFinset a b _ _) = true at hit
    rw [he,reserve_binary U a b ab] at hit
    exact claim _ _ _ _ _ _ _ _ (nextCut_use hit fresh tail (by omega)) _ (by omega) _ hn tail
  | @unary k' n' U a pa fresh tail =>
    have pos : N≠0 := by omega
    have tests := ok.2.resolve_left pos
    have aok := List.all_eq_true.mp tests a (List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _))
    have hit := of_decide_eq_true aok (decide (a∈U))
    change nextCut (check a a 2 _ _) K (N-1) ws.toFinset (neg a) (reserve ws.toFinset a a _ _) = true at hit
    rw [he,reserve_unary U a] at hit
    exact claim _ _ _ _ _ _ _ _ (nextCut_use hit fresh tail hk) _ hk _ (by omega) tail
def cellIndex (ws : List Sig) (a b : Sig) (d : Nat) (ka kb : Bool) :=
  let i := ws.idxOf a
  let j := ws.idxOf b
  if d=2 then ws.length*ws.length*8+i*2+ka.toNat else
    if i≤j then (((i*ws.length+j)*2+d)*2+ka.toNat)*2+kb.toNat
    else (((j*ws.length+i)*2+d)*2+kb.toNat)*2+ka.toNat
def page (chart : Nat → Chart) (links : Array Closed) (dict : Array Hint)
    (ws : List Sig) (mask width : Nat) (a b : Sig) (d : Nat) (ka kb : Bool) :=
  let idx := (mask >>> (width * cellIndex ws a b d ka kb)) % (2^width)
  verdict chart links (dict[idx]?.getD .trivial)
def closeBank (chart : Nat → Chart) (links : Array Closed) (dict : Array Hint)
    (ws : List Sig) (mask width K N : Nat) (ok : tagStep target (page chart links dict ws mask width) K N ws=true) :
    Closed := ⟨K,N,ws,tag_sound ok (fun _ _ _ _ _ _ _ _ yes => verdict_ok yes)⟩
def rowChart0 (i : Fin 8) : Row := ([16, 17, 18, 19, 0, 1, 2, 3] : List Row).getD i.val 0
def chart0 : Chart := ⟨rowChart0,by decide +kernel⟩
def rowChart1 (i : Fin 8) : Row := ([52, 53, 54, 55, 36, 37, 38, 39] : List Row).getD i.val 0
def chart1 : Chart := ⟨rowChart1,by decide +kernel⟩
def rowChart2 (i : Fin 8) : Row := ([32, 33, 36, 37, 0, 1, 4, 5] : List Row).getD i.val 0
def chart2 : Chart := ⟨rowChart2,by decide +kernel⟩
def rowChart3 (i : Fin 8) : Row := ([50, 51, 54, 55, 18, 19, 22, 23] : List Row).getD i.val 0
def chart3 : Chart := ⟨rowChart3,by decide +kernel⟩
def rowChart4 (i : Fin 8) : Row := ([32, 34, 36, 38, 0, 2, 4, 6] : List Row).getD i.val 0
def chart4 : Chart := ⟨rowChart4,by decide +kernel⟩
def rowChart5 (i : Fin 8) : Row := ([40, 42, 44, 46, 8, 10, 12, 14] : List Row).getD i.val 0
def chart5 : Chart := ⟨rowChart5,by decide +kernel⟩
def rowChart6 (i : Fin 8) : Row := ([50, 54, 34, 38, 18, 22, 2, 6] : List Row).getD i.val 0
def chart6 : Chart := ⟨rowChart6,by decide +kernel⟩
def rowChart7 (i : Fin 8) : Row := ([58, 62, 42, 46, 26, 30, 10, 14] : List Row).getD i.val 0
def chart7 : Chart := ⟨rowChart7,by decide +kernel⟩
def rowChart8 (i : Fin 8) : Row := ([49, 51, 53, 55, 17, 19, 21, 23] : List Row).getD i.val 0
def chart8 : Chart := ⟨rowChart8,by decide +kernel⟩
def rowChart9 (i : Fin 8) : Row := ([41, 43, 45, 47, 9, 11, 13, 15] : List Row).getD i.val 0
def chart9 : Chart := ⟨rowChart9,by decide +kernel⟩
def rowChart10 (i : Fin 8) : Row := ([25, 27, 17, 19, 9, 11, 1, 3] : List Row).getD i.val 0
def chart10 : Chart := ⟨rowChart10,by decide +kernel⟩
def rowChart11 (i : Fin 8) : Row := ([61, 63, 53, 55, 45, 47, 37, 39] : List Row).getD i.val 0
def chart11 : Chart := ⟨rowChart11,by decide +kernel⟩
def rowChart12 (i : Fin 8) : Row := ([41, 45, 33, 37, 9, 13, 1, 5] : List Row).getD i.val 0
def chart12 : Chart := ⟨rowChart12,by decide +kernel⟩
def rowChart13 (i : Fin 8) : Row := ([49, 53, 33, 37, 17, 21, 1, 5] : List Row).getD i.val 0
def chart13 : Chart := ⟨rowChart13,by decide +kernel⟩
def rowChart14 (i : Fin 8) : Row := ([59, 63, 51, 55, 27, 31, 19, 23] : List Row).getD i.val 0
def chart14 : Chart := ⟨rowChart14,by decide +kernel⟩
def rowChart15 (i : Fin 8) : Row := ([59, 63, 43, 47, 27, 31, 11, 15] : List Row).getD i.val 0
def chart15 : Chart := ⟨rowChart15,by decide +kernel⟩
def charts : Array Chart := #[chart0,chart1,chart2,chart3,chart4,chart5,chart6,chart7,chart8,chart9,chart10,chart11,chart12,chart13,chart14,chart15]
def chartAt (i : Nat) : Chart := charts[i]?.getD chart0
def hint0 : Hint := .trivial
def hint1 : Hint := .equal 4 0
def hint2 : Hint := .face 0
def hint3 : Hint := .face 2
def hint4 : Hint := .equal 31 27
def hint5 : Hint := .face 1
def hint6 : Hint := .equal 9 1
def hint7 : Hint := .equal 27 19
def hint8 : Hint := .equal 17 1
def hint9 : Hint := .equal 27 11
def hint10 : Hint := .equal 33 1
def hint11 : Hint := .equal 35 3
def hint12 : Hint := .equal 10 9
def hint13 : Hint := .face 4
def hint14 : Hint := .equal 1 0
def hint15 : Hint := .equal 12 9
def hint16 : Hint := .equal 37 36
def hint17 : Hint := .equal 13 9
def hint18 : Hint := .equal 8 1
def hint19 : Hint := .equal 18 2
def hint20 : Hint := .equal 16 1
def hint21 : Hint := .equal 34 2
def hint22 : Hint := .equal 32 1
def hint23 : Hint := .equal 2 0
def hint24 : Hint := .equal 20 18
def hint25 : Hint := .equal 38 36
def hint26 : Hint := .equal 22 18
def hint27 : Hint := .equal 8 2
def hint28 : Hint := .equal 10 8
def hint29 : Hint := .equal 16 2
def hint30 : Hint := .equal 32 2
def hint31 : Hint := .equal 8 4
def hint32 : Hint := .equal 12 8
def hint33 : Hint := .equal 45 37
def hint34 : Hint := .equal 16 4
def hint35 : Hint := .equal 20 16
def hint36 : Hint := .equal 53 37
def hint37 : Hint := .face 10
def hint38 : Hint := .equal 32 4
def hint39 : Hint := .equal 37 33
def hint40 : Hint := .equal 36 4
def hint41 : Hint := .equal 18 10
def hint42 : Hint := .equal 26 10
def hint43 : Hint := .equal 34 10
def hint44 : Hint := .equal 42 10
def hint45 : Hint := .equal 35 19
def hint46 : Hint := .equal 51 19
def hint47 : Hint := .four 1 9 13 45
def hint48 : Hint := .four 1 0 2 18
def hint49 : Hint := .four 1 9 11 27
def hint50 : Hint := .four 1 17 19 51
def hint51 : Hint := .four 1 9 11 43
def hint52 : Hint := .equal 19 18
def hint53 : Hint := .equal 11 9
def hint54 : Hint := .equal 9 3
def hint55 : Hint := .equal 19 17
def hint56 : Hint := .equal 9 5
def hint57 : Hint := .equal 16 12
def hint58 : Hint := .equal 32 12
def hint59 : Hint := .equal 36 12
def hint60 : Hint := .equal 17 3
def hint61 : Hint := .equal 17 5
def hint62 : Hint := .equal 21 17
def hint63 : Hint := .equal 32 20
def hint64 : Hint := .equal 36 20
def hint65 : Hint := .equal 55 54
def hint66 : Hint := .face 6
def hint67 : Hint := .face 3
def hint68 : Hint := .equal 18 3
def hint69 : Hint := .equal 47 45
def hint70 : Hint := .equal 33 3
def hint71 : Hint := .link 0
def hint72 : Hint := .link 1
def hint73 : Hint := .four 1 9 10 26
def hint74 : Hint := .equal 45 13
def hint75 : Hint := .equal 38 34
def hint76 : Hint := .equal 16 10
def hint77 : Hint := .equal 32 10
def hint78 : Hint := .equal 35 11
def hint79 : Hint := .equal 43 11
def hint80 : Hint := .equal 29 27
def hint81 : Hint := .equal 33 5
def hint82 : Hint := .equal 8 3
def hint83 : Hint := .equal 26 19
def hint84 : Hint := .equal 8 5
def hint85 : Hint := .equal 44 37
def hint86 : Hint := .equal 26 11
def hint87 : Hint := .equal 42 11
def hint88 : Hint := .four 1 8 12 44
def hint89 : Hint := .four 1 8 10 26
def hint90 : Hint := .four 1 8 10 42
def hint91 : Hint := .equal 54 38
def hint92 : Hint := .four 1 9 11 26
def hint93 : Hint := .equal 52 20
def hint94 : Hint := .face 8
def hint95 : Hint := .equal 63 55
def hint96 : Hint := .equal 54 22
def hint97 : Hint := .equal 30 27
def hint98 : Hint := .equal 46 44
def hint99 : Hint := .equal 55 53
def hint100 : Hint := .equal 26 22
def hint101 : Hint := .equal 30 26
def hint102 : Hint := .equal 18 6
def hint103 : Hint := .equal 34 6
def hint104 : Hint := .four 2 18 19 27
def hint105 : Hint := .four 1 9 10 42
def hint106 : Hint := .four 1 17 21 53
def hint107 : Hint := .equal 36 5
def hint108 : Hint := .equal 55 51
def hint109 : Hint := .equal 37 35
def hint110 : Hint := .equal 36 6
def hint111 : Hint := .equal 41 37
def hint112 : Hint := .equal 49 37
def hint113 : Hint := .equal 25 19
def hint114 : Hint := .equal 52 22
def hint115 : Hint := .equal 50 38
def hint116 : Hint := .equal 44 12
def hint117 : Hint := .equal 34 3
def hint118 : Hint := .four 1 9 12 44
def hint119 : Hint := .equal 20 17
def hint120 : Hint := .equal 62 46
def hint121 : Hint := .equal 28 26
def hint122 : Hint := .equal 24 12
def hint123 : Hint := .equal 28 24
def hint124 : Hint := .equal 46 42
def hint125 : Hint := .equal 24 20
def hint126 : Hint := .equal 24 10
def hint127 : Hint := .four 1 9 11 25
def hint128 : Hint := .equal 60 28
def hint129 : Hint := .equal 44 28
def hint130 : Hint := .four 10 26 30 62
def hint131 : Hint := .four 1 9 13 44
def hint132 : Hint := .four 1 9 11 42
def hint133 : Hint := .four 19 27 31 63
def hint134 : Hint := .link 2
def hint135 : Hint := .link 3
def hint136 : Hint := .link 4
def hint137 : Hint := .link 5
def hint138 : Hint := .link 6
def hint139 : Hint := .link 7
def hint140 : Hint := .link 8
def hint141 : Hint := .link 9
def hint142 : Hint := .link 10
def hint143 : Hint := .link 11
def hint144 : Hint := .link 12
def hint145 : Hint := .link 13
def hint146 : Hint := .link 14
def hint147 : Hint := .link 15
def hint148 : Hint := .link 16
def hint149 : Hint := .link 17
def hint150 : Hint := .link 18
def hint151 : Hint := .link 19
def hint152 : Hint := .link 20
def hint153 : Hint := .link 21
def hint154 : Hint := .link 22
def hint155 : Hint := .link 23
def hint156 : Hint := .link 24
def hint157 : Hint := .link 25
def hint158 : Hint := .link 26
def hint159 : Hint := .link 27
def hint160 : Hint := .link 28
def hint161 : Hint := .link 29
def hint162 : Hint := .link 30
def hint163 : Hint := .link 31
def hint164 : Hint := .drop 19 35
def hint165 : Hint := .drop 37 53
def hint166 : Hint := .drop 1 17
def hint167 : Hint := .drop 1 33
def hint168 : Hint := .drop 2 34
def hint169 : Hint := .drop 37 36
def hint170 : Hint := .drop 1 0
def hint171 : Hint := .drop 38 36
def hint172 : Hint := .drop 1 35
def hint173 : Hint := .drop 2 0
def hint174 : Hint := .drop 37 33
def hint175 : Hint := .drop 4 0
def hint176 : Hint := .drop 4 36
def hint177 : Hint := .drop 2 18
def hint178 : Hint := .drop 19 18
def hint179 : Hint := .drop 19 17
def hint180 : Hint := .drop 20 0
def hint181 : Hint := .drop 20 17
def hint182 : Hint := .drop 20 18
def hint183 : Hint := .four 2 18 2 18
def hint184 : Hint := .four 19 18 2 34
def hint185 : Hint := .four 1 0 1 0
def hint186 : Hint := .four 1 17 1 17
def hint187 : Hint := .four 19 17 1 33
def hint188 : Hint := .four 2 0 1 33
def hint189 : Hint := .four 19 51 55 35
def hint190 : Hint := .four 1 33 37 33
def hint191 : Hint := .four 1 33 37 53
def hint192 : Hint := .four 19 51 3 35
def hint193 : Hint := .four 1 33 1 33
def hint194 : Hint := .four 2 34 38 34
def hint195 : Hint := .four 1 33 37 36
def hint196 : Hint := .four 2 34 2 34
def hint197 : Hint := .four 1 32 1 32
def hint198 : Hint := .four 1 32 37 36
def hint199 : Hint := .four 1 33 37 35
def hint200 : Hint := .four 2 34 38 36
def hint201 : Hint := .four 1 33 3 33
def hint202 : Hint := .four 2 32 38 36
def hint203 : Hint := .four 1 33 3 35
def hint204 : Hint := .four 4 0 1 33
def hint205 : Hint := .four 1 33 5 33
def hint206 : Hint := .four 4 36 4 36
def hint207 : Hint := .four 2 18 22 54
def hint208 : Hint := .four 37 36 37 36
def hint209 : Hint := .four 37 53 55 53
def hint210 : Hint := .four 1 17 19 17
def hint211 : Hint := .four 37 33 1 17
def hint212 : Hint := .four 1 17 21 17
def hint213 : Hint := .four 1 33 1 17
def hint214 : Hint := .four 37 53 37 53
def hint215 : Hint := .four 2 0 1 17
def hint216 : Hint := .four 1 17 19 18
def hint217 : Hint := .four 2 18 22 18
def hint218 : Hint := .four 1 17 20 17
def hint219 : Hint := .four 1 16 1 16
def hint220 : Hint := .four 1 16 19 18
def hint221 : Hint := .four 2 18 20 18
def hint222 : Hint := .four 1 17 3 17
def hint223 : Hint := .four 4 0 1 17
def hint224 : Hint := .four 1 17 5 17
def hint225 : Hint := .equal 18 11
def hint226 : Hint := .equal 34 11
def hint227 : Hint := .equal 16 11
def hint228 : Hint := .equal 32 11
def hint229 : Hint := .equal 16 13
def hint230 : Hint := .equal 32 13
def hint231 : Hint := .equal 36 13
def hint232 : Hint := .drop 11 35
def hint233 : Hint := .drop 37 45
def hint234 : Hint := .drop 1 9
def hint235 : Hint := .drop 11 27
def hint236 : Hint := .drop 19 27
def hint237 : Hint := .drop 11 9
def hint238 : Hint := .drop 13 9
def hint239 : Hint := .four 11 27 3 35
def hint240 : Hint := .four 19 27 3 35
def hint241 : Hint := .four 1 9 1 9
def hint242 : Hint := .four 11 9 1 33
def hint243 : Hint := .four 11 43 47 35
def hint244 : Hint := .four 1 33 37 45
def hint245 : Hint := .four 11 43 3 35
def hint246 : Hint := .four 11 27 31 63
def hint247 : Hint := .four 37 45 37 45
def hint248 : Hint := .four 11 9 1 17
def hint249 : Hint := .four 1 17 19 27
def hint250 : Hint := .four 11 27 31 27
def hint251 : Hint := .four 11 27 11 27
def hint252 : Hint := .four 1 0 4 36
def hint253 : Hint := .four 1 0 2 34
def hint254 : Hint := .four 2 0 1 9
def hint255 : Hint := .four 37 45 47 63
def hint256 : Hint := .four 1 33 1 9
def hint257 : Hint := .four 37 45 47 45
def hint258 : Hint := .four 1 9 11 9
def hint259 : Hint := .four 37 33 1 9
def hint260 : Hint := .four 1 9 13 9
def hint261 : Hint := .four 1 17 1 9
def hint262 : Hint := .four 19 27 19 27
def hint263 : Hint := .four 19 18 19 18
def hint264 : Hint := .four 19 17 1 9
def hint265 : Hint := .four 19 27 31 27
def hint266 : Hint := .four 1 9 3 9
def hint267 : Hint := .four 4 0 1 9
def hint268 : Hint := .four 1 9 5 9
def hint269 : Hint := .four 19 27 29 27
def hint270 : Hint := .four 2 0 1 8
def hint271 : Hint := .four 2 18 19 26
def hint272 : Hint := .drop 10 35
def hint273 : Hint := .drop 37 44
def hint274 : Hint := .drop 1 8
def hint275 : Hint := .drop 10 26
def hint276 : Hint := .drop 19 26
def hint277 : Hint := .drop 10 8
def hint278 : Hint := .drop 12 8
def hint279 : Hint := .four 10 26 3 35
def hint280 : Hint := .four 19 26 3 35
def hint281 : Hint := .four 1 8 1 8
def hint282 : Hint := .four 10 8 1 33
def hint283 : Hint := .four 10 42 46 35
def hint284 : Hint := .four 1 33 37 44
def hint285 : Hint := .four 10 42 3 35
def hint286 : Hint := .four 37 44 37 44
def hint287 : Hint := .four 10 8 1 17
def hint288 : Hint := .four 1 17 19 26
def hint289 : Hint := .four 10 26 30 26
def hint290 : Hint := .four 10 26 10 26
def hint291 : Hint := .four 19 26 30 62
def hint292 : Hint := .four 37 44 46 62
def hint293 : Hint := .four 37 44 46 44
def hint294 : Hint := .four 1 8 10 8
def hint295 : Hint := .four 37 33 1 8
def hint296 : Hint := .four 1 8 12 8
def hint297 : Hint := .four 1 33 1 8
def hint298 : Hint := .four 1 17 1 8
def hint299 : Hint := .four 19 17 1 8
def hint300 : Hint := .four 19 26 30 26
def hint301 : Hint := .four 19 26 19 26
def hint302 : Hint := .four 19 26 28 26
def hint303 : Hint := .four 1 8 3 8
def hint304 : Hint := .four 4 0 1 8
def hint305 : Hint := .four 1 8 5 8
def hint306 : Hint := .equal 9 2
def hint307 : Hint := .equal 9 4
def hint308 : Hint := .drop 19 51
def hint309 : Hint := .drop 20 16
def hint310 : Hint := .four 2 18 19 18
def hint311 : Hint := .four 2 18 19 51
def hint312 : Hint := .four 19 17 19 17
def hint313 : Hint := .four 19 51 55 51
def hint314 : Hint := .four 19 51 19 51
def hint315 : Hint := .four 19 18 3 35
def hint316 : Hint := .four 19 17 3 35
def hint317 : Hint := .four 19 51 19 35
def hint318 : Hint := .four 37 33 37 33
def hint319 : Hint := .drop 2 9
def hint320 : Hint := .drop 4 9
def hint321 : Hint := .four 2 9 1 33
def hint322 : Hint := .drop 10 34
def hint323 : Hint := .drop 10 18
def hint324 : Hint := .drop 10 0
def hint325 : Hint := .drop 12 0
def hint326 : Hint := .four 10 18 2 34
def hint327 : Hint := .four 4 36 46 36
def hint328 : Hint := .four 10 0 1 33
def hint329 : Hint := .four 2 34 46 34
def hint330 : Hint := .four 10 42 46 34
def hint331 : Hint := .four 2 42 2 34
def hint332 : Hint := .four 10 42 2 34
def hint333 : Hint := .four 10 26 30 54
def hint334 : Hint := .four 10 0 1 17
def hint335 : Hint := .four 2 18 30 18
def hint336 : Hint := .four 10 26 30 18
def hint337 : Hint := .four 2 26 2 18
def hint338 : Hint := .four 10 26 2 18
def hint339 : Hint := .drop 10 9
def hint340 : Hint := .drop 12 9
def hint341 : Hint := .four 10 9 1 33
def hint342 : Hint := .four 10 18 19 27
def hint343 : Hint := .four 10 18 19 51
def hint344 : Hint := .drop 2 42
def hint345 : Hint := .drop 2 26
def hint346 : Hint := .drop 2 8
def hint347 : Hint := .drop 4 8
def hint348 : Hint := .four 2 26 2 26
def hint349 : Hint := .four 2 26 10 26
def hint350 : Hint := .four 2 8 2 8
def hint351 : Hint := .four 2 8 10 8
def hint352 : Hint := .four 2 34 38 42
def hint353 : Hint := .four 2 34 10 34
def hint354 : Hint := .four 2 34 10 42
def hint355 : Hint := .four 2 18 22 62
def hint356 : Hint := .four 2 18 22 26
def hint357 : Hint := .four 2 18 10 18
def hint358 : Hint := .four 2 18 10 26
def hint359 : Hint := .drop 10 42
def hint360 : Hint := .four 19 27 11 43
def hint361 : Hint := .four 10 26 2 34
def hint362 : Hint := .four 10 8 10 8
def hint363 : Hint := .four 10 42 46 42
def hint364 : Hint := .four 10 42 10 42
def hint365 : Hint := .four 10 9 10 9
def hint366 : Hint := .four 10 9 11 9
def hint367 : Hint := .four 10 8 2 34
def hint368 : Hint := .four 10 42 10 34
def hint369 : Hint := .four 10 8 2 18
def hint370 : Hint := .four 10 26 10 18
def hint371 : Hint := .four 1 9 10 9
def hint372 : Hint := .four 1 9 12 9
def hint373 : Hint := .four 4 36 37 36
def hint374 : Hint := .four 4 36 37 45
def hint375 : Hint := .four 2 18 20 16
def hint376 : Hint := .four 4 36 38 32
def hint377 : Hint := .four 1 0 2 0
def hint378 : Hint := .four 1 0 4 0
def hint379 : Hint := .four 1 17 20 16
def hint380 : Hint := .four 4 36 37 32
def hint381 : Hint := .four 5 53 37 32
def hint382 : Hint := .four 1 0 20 0
def hint383 : Hint := .four 1 0 20 16
def hint384 : Hint := .four 1 17 1 0
def hint385 : Hint := .four 4 36 4 0
def hint386 : Hint := .four 1 33 1 0
def hint387 : Hint := .four 1 33 37 32
def hint388 : Hint := .four 1 17 19 16
def hint389 : Hint := .four 2 18 19 16
def hint390 : Hint := .four 2 18 2 0
def hint391 : Hint := .four 2 34 2 0
def hint392 : Hint := .four 3 35 19 16
def hint393 : Hint := .four 2 18 22 52
def hint394 : Hint := .four 37 36 38 36
def hint395 : Hint := .four 37 33 1 0
def hint396 : Hint := .four 1 17 21 52
def hint397 : Hint := .four 37 53 37 36
def hint398 : Hint := .four 1 0 4 52
def hint399 : Hint := .four 2 18 22 16
def hint400 : Hint := .four 1 17 21 16
def hint401 : Hint := .four 1 0 4 16
def hint402 : Hint := .four 19 18 22 54
def hint403 : Hint := .four 37 36 38 54
def hint404 : Hint := .four 37 32 38 34
def hint405 : Hint := .four 1 32 1 0
def hint406 : Hint := .four 19 17 1 0
def hint407 : Hint := .four 19 18 22 18
def hint408 : Hint := .four 1 16 1 0
def hint409 : Hint := .four 19 18 20 18
def hint410 : Hint := .four 21 17 1 0
def hint411 : Hint := .four 1 9 12 8
def hint412 : Hint := .four 5 45 37 32
def hint413 : Hint := .four 1 0 12 0
def hint414 : Hint := .four 1 0 12 8
def hint415 : Hint := .four 1 9 1 0
def hint416 : Hint := .four 1 9 10 8
def hint417 : Hint := .four 3 27 19 16
def hint418 : Hint := .four 1 0 10 0
def hint419 : Hint := .four 1 0 10 8
def hint420 : Hint := .four 2 18 10 8
def hint421 : Hint := .four 2 34 10 8
def hint422 : Hint := .four 37 45 37 36
def hint423 : Hint := .four 1 0 4 44
def hint424 : Hint := .four 1 9 13 8
def hint425 : Hint := .four 1 0 4 8
def hint426 : Hint := .four 1 0 2 42
def hint427 : Hint := .four 19 27 19 18
def hint428 : Hint := .four 1 0 2 26
def hint429 : Hint := .four 1 9 11 8
def hint430 : Hint := .four 1 0 2 8
def hint431 : Hint := .four 19 35 19 35
def hint432 : Hint := .four 38 36 38 36
def hint433 : Hint := .four 1 35 1 35
def hint434 : Hint := .four 1 35 3 35
def hint435 : Hint := .four 2 0 2 0
def hint436 : Hint := .four 4 0 4 0
def hint437 : Hint := .four 20 16 20 0
def hint438 : Hint := .four 20 17 20 17
def hint439 : Hint := .four 20 17 21 17
def hint440 : Hint := .four 20 18 20 18
def hint441 : Hint := .four 20 18 22 18
def hint442 : Hint := .four 10 34 10 34
def hint443 : Hint := .four 10 18 10 18
def hint444 : Hint := .four 10 8 10 0
def hint445 : Hint := .four 12 8 12 0
def hint446 : Hint := .four 12 9 12 9
def hint447 : Hint := .four 12 9 13 9
def done0 : Closed := closeBank chartAt #[] #[hint0,hint1,hint2,hint3,hint4,hint5,hint6,hint7,hint8,hint9,hint10,hint11,hint12,hint13,hint14,hint15,hint16,hint17,hint18,hint19,hint20,hint21,hint22,hint23,hint24,hint25,hint26,hint27,hint28,hint29,hint30,hint31,hint32,hint33,hint34,hint35,hint36,hint37,hint38,hint39,hint40,hint41,hint42,hint43,hint44,hint45,hint46,hint47,hint48,hint49,hint50,hint51] [0x8888888888888888,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000] 0xc71cf3cb2c71befc70bef0000000000000000000000000000000000000000000000000000000000000000000000000000000000000ee92d0ca2080000000000000000000000000000000000000000000000000000000000000000000000000ec86b0ca1860ea1e90c81860000000000000000000000000000000000000000000000000000000000009689e694a0410e48e20c80410e181f0c60410000000000000000000000000000000000000000000000000d565e0ca5d70d30dd0c85d70c771b0c65d70da6580c15d700000000000000000000000000000000000034a41635538e0c80d40d338e0c60d20c338e35140f34138e0cd0cc0000000000000000000000000000000cb14b0ca08a0c90c90c80c80c70c70c60860c41440c1081000000000000000000000000000000000000 6 8 2 (by decide +kernel)
end PEqualNP.Outside.L_meta_9929.LB

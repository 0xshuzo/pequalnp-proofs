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
def base8 : List Small := [170,204,240]
def maj8 : Small := 232
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
theorem face_sound (majPrice : ∀ {p}, R8 maj8 p base8 → 4≤p) {c K N S} (ok : faceCut c K S=true) : within target K N S := by
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
theorem verdict_ok (majPrice : ∀ {p}, R8 maj8 p base8 → 4≤p) {chart links h K N S} (yes : verdict chart links h K N S=true) :
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
  | face j => exact face_sound majPrice yes
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
def closeBank (majPrice : ∀ {p}, R8 maj8 p base8 → 4≤p) (chart : Nat → Chart) (links : Array Closed) (dict : Array Hint)
    (ws : List Sig) (mask width K N : Nat) (ok : tagStep target (page chart links dict ws mask width) K N ws=true) :
    Closed := ⟨K,N,ws,tag_sound ok (fun _ _ _ _ _ _ _ _ yes => verdict_ok majPrice yes)⟩
end PEqualNP.Outside.L_meta_9929.LB

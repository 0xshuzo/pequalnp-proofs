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
theorem const_extend (d : Nat) (x y : Small) (bank : List Small) (hx : has8 bank x)
    (hy : has8 bank y) (h : flat x=true ∨ flat y=true) : has8 bank (calc8 d x y) := by
  simp only [flat,Bool.or_eq_true,beq_iff_eq] at h
  rcases h with (rfl|rfl)|(rfl|rfl) <;> by_cases d0 : d=0 <;>
    simp_all [calc8,has8,domain8,fun v => (high8 v).1,fun v => (high8 v).2.1,
      fun v => (high8 v).2.2.1,fun v => (high8 v).2.2.2]
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
def options8 (bank : List Small) : List Small :=
  (domain8 bank).flatMap fun a => (domain8 bank).flatMap fun b => [a &&& b,a ||| b]
theorem options_mem {d x y bank} (hd : d<2) (hx : has8 bank x) (hy : has8 bank y) :
    calc8 d x y ∈ options8 bank := by
  apply List.mem_flatMap.mpr
  refine ⟨x,hx,List.mem_flatMap.mpr ⟨y,hy,?_⟩⟩
  obtain rfl | rfl : d=0 ∨ d=1 := by omega
  all_goals simp [calc8]
def can8 (T : Small) : Nat → List Small → Bool
  | 0,bs => (domain8 bs).contains T
  | k+1,bs => (domain8 bs).contains T || (options8 bs).eraseDups.any fun z => can8 T k (z::bs)
theorem can8_sound {T k bs} (h : R8 T k bs) : ∀ K, k≤K → can8 T K bs = true := by
  induction h with
  | done hv =>
    intro K hk
    cases K <;> simp [can8,show T∈domain8 _ from hv]
  | @step bs x y n d hd hx hy tail ih =>
    intro K hk
    cases K with
    | zero => omega
    | succ K =>
      simp only [can8,Bool.or_eq_true]
      exact Or.inr (List.any_eq_true.mpr ⟨_,List.mem_eraseDups.mpr (options_mem hd hx hy),ih K (by omega)⟩)
def base8 : List Small := [170,204,240]
def maj8 : Small := 232
def first8 := (options8 base8).eraseDups
theorem checkMaj (all : ∀z∈first8, can8 maj8 2 (z::base8)=false) {p} (r : R8 maj8 p base8) :
    4≤p := by
  by_contra low
  have hz := can8_sound r 3 (by omega)
  change ((domain8 base8).contains maj8 || first8.any fun z => can8 maj8 2 (z::base8))=true at hz
  have hb : (domain8 base8).contains maj8=false := by decide +kernel
  rw [hb,Bool.false_or] at hz
  obtain ⟨z,m,v⟩ := List.any_eq_true.mp hz
  rw [all z m] at v
  contradiction
theorem firstPage0 : can8 maj8 2 (0::base8)=false := by decide +kernel
theorem firstPage1 : can8 maj8 2 (255::base8)=false := by decide +kernel
theorem firstPage2 : can8 maj8 2 (170::base8)=false := by decide +kernel
theorem firstPage3 : can8 maj8 2 (204::base8)=false := by decide +kernel
theorem firstPage4 : can8 maj8 2 (240::base8)=false := by decide +kernel
theorem firstPage5 : can8 maj8 2 (85::base8)=false := by decide +kernel
theorem firstPage6 : can8 maj8 2 (51::base8)=false := by decide +kernel
theorem firstPage7 : can8 maj8 2 (15::base8)=false := by decide +kernel
theorem firstPage8 : can8 maj8 2 (136::base8)=false := by decide +kernel
theorem firstPage9 : can8 maj8 2 (238::base8)=false := by decide +kernel
theorem firstPage10 : can8 maj8 2 (160::base8)=false := by decide +kernel
theorem firstPage11 : can8 maj8 2 (250::base8)=false := by decide +kernel
theorem firstPage12 : can8 maj8 2 (34::base8)=false := by decide +kernel
theorem firstPage13 : can8 maj8 2 (187::base8)=false := by decide +kernel
theorem firstPage14 : can8 maj8 2 (10::base8)=false := by decide +kernel
theorem firstPage15 : can8 maj8 2 (175::base8)=false := by decide +kernel
theorem firstPage16 : can8 maj8 2 (192::base8)=false := by decide +kernel
theorem firstPage17 : can8 maj8 2 (252::base8)=false := by decide +kernel
theorem firstPage18 : can8 maj8 2 (68::base8)=false := by decide +kernel
theorem firstPage19 : can8 maj8 2 (221::base8)=false := by decide +kernel
theorem firstPage20 : can8 maj8 2 (12::base8)=false := by decide +kernel
theorem firstPage21 : can8 maj8 2 (207::base8)=false := by decide +kernel
theorem firstPage22 : can8 maj8 2 (80::base8)=false := by decide +kernel
theorem firstPage23 : can8 maj8 2 (245::base8)=false := by decide +kernel
theorem firstPage24 : can8 maj8 2 (48::base8)=false := by decide +kernel
theorem firstPage25 : can8 maj8 2 (243::base8)=false := by decide +kernel
theorem firstPage26 : can8 maj8 2 (17::base8)=false := by decide +kernel
theorem firstPage27 : can8 maj8 2 (119::base8)=false := by decide +kernel
theorem firstPage28 : can8 maj8 2 (5::base8)=false := by decide +kernel
theorem firstPage29 : can8 maj8 2 (95::base8)=false := by decide +kernel
theorem firstPage30 : can8 maj8 2 (3::base8)=false := by decide +kernel
theorem firstPage31 : can8 maj8 2 (63::base8)=false := by decide +kernel
theorem majPrice {p} (r : R8 maj8 p base8) : 4≤p := by
  apply checkMaj _ r
  intro z h
  have entries : ∀ z ∈ first8, z ∈ [0, 255, 170, 204, 240, 85, 51, 15, 136, 238, 160, 250, 34, 187, 10, 175, 192, 252, 68, 221, 12, 207, 80, 245, 48, 243, 17, 119, 5, 95, 3, 63] := by decide +kernel
  replace h := entries z h
  simp only [List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact firstPage0
  · exact firstPage1
  · exact firstPage2
  · exact firstPage3
  · exact firstPage4
  · exact firstPage5
  · exact firstPage6
  · exact firstPage7
  · exact firstPage8
  · exact firstPage9
  · exact firstPage10
  · exact firstPage11
  · exact firstPage12
  · exact firstPage13
  · exact firstPage14
  · exact firstPage15
  · exact firstPage16
  · exact firstPage17
  · exact firstPage18
  · exact firstPage19
  · exact firstPage20
  · exact firstPage21
  · exact firstPage22
  · exact firstPage23
  · exact firstPage24
  · exact firstPage25
  · exact firstPage26
  · exact firstPage27
  · exact firstPage28
  · exact firstPage29
  · exact firstPage30
  · exact firstPage31
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
    have get := project_at rs a ⟨i,hi⟩
    rw [show (project8 rs (neg a)).getLsbD i = _ from project_at rs (neg a) ⟨i,hi⟩,bit_neg]
    simp [BitVec.getLsbD_not,hi,get]
  · intro d a b hd
    obtain rfl | rfl : d=0 ∨ d=1 := by rcases hd with h|h; omega; simp at h
    all_goals
      apply BitVec.eq_of_getLsbD_eq
      intro i hi
      have vx := project_at rs a ⟨i,hi⟩
      have vy := project_at rs b ⟨i,hi⟩
      rw [show (project8 rs (bin _ a b)).getLsbD i = _ from project_at rs _ ⟨i,hi⟩,bit_bin]
      simp [calc8,vx,vy]
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
    exact zero_ord run (by omega) (ord_check yes.2) (isDrop_ok yes.1.2)
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
def done1 : Closed := closeBank chartAt #[] #[hint0,hint14,hint23,hint3,hint12,hint52,hint53,hint2,hint6,hint1,hint17,hint16,hint19,hint20,hint8,hint21,hint22,hint10,hint54,hint7,hint24,hint25,hint26,hint29,hint55,hint30,hint56,hint33,hint41,hint42,hint43,hint44,hint57,hint35,hint36,hint58,hint39,hint59,hint45,hint46,hint48,hint49,hint47,hint50,hint51] [0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xee00ee00ee00ee00,0xf0f0f0f0f0f0f0f0,0xffff0000ffff0000,0xffffffff00000000] 0xa69b2ca69aebaaaa680000000000000000000000000000000000000000000000000000000000000000000000001e78a61d138e0000000000000000000000000000000000000000000000000000000000001e59231d12491e28601ce2490000000000000000000000000000000000000000000000001df6de1d12081dd4dc1ce2081ca6da1c92090000000000000000000000000000000000001cf5591d10820cc6170ce0821d65541c90821d31921c80820000000000000000000000001d12d01cf0410ce14d0cc0411ca2ca1c90411c81c81c70410c61440c2041000000000000 6 7 2 (by decide +kernel)
def done2 : Closed := closeBank chartAt #[] #[hint0,hint14,hint23,hint3,hint12,hint52,hint53,hint19,hint8,hint1,hint13,hint15,hint16,hint17,hint18,hint6,hint21,hint22,hint10,hint60,hint55,hint26,hint25,hint27,hint28,hint7,hint30,hint61,hint36,hint62,hint41,hint42,hint45,hint46,hint31,hint32,hint33,hint37,hint63,hint39,hint64,hint43,hint44,hint48,hint49,hint47,hint51,hint50] [0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xeeee0000eeee0000,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffffff00000000] 0xb2cbefb2cbaeb6db2b0000000000000000000000000000000000000000000000000000000000000000000000000ea9290d23cf0000000000000000000000000000000000000000000000000000000000009689e69522490e48e20cf2490000000000000000000000000000000000000000000000000e17200d22080d97de0cf20f0dd71b0c92090000000000000000000000000000000000000d059a0d20820d96170cf0820d55950c90820c75130c80820000000000000000000000002923112900410cf0ce0c304128d30b2890410c81480c70410c61440c2041000000000000 6 7 2 (by decide +kernel)
def done3 : Closed := closeBank chartAt #[done1,done2] #[hint0,hint12,hint3,hint13,hint1,hint52,hint17,hint65,hint66,hint67,hint6,hint68,hint19,hint8,hint21,hint10,hint53,hint26,hint69,hint54,hint55,hint7,hint60,hint70,hint2,hint5,hint71,hint72,hint40,hint31,hint32,hint33,hint34,hint35,hint36,hint37,hint38,hint39,hint41,hint42,hint43,hint44,hint45,hint46,hint73,hint49,hint47,hint50,hint51] [0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xeeeeeeeeeeeeeeee,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000] 0xb6dc30befb6db6dbaeb6c00000000000000000000000000000000000000000000000000000000000000000000000000000000000026b8aa08f34d0000000000000000000000000000000000000000000000000000000000000000000000002697e808f28a0a756608d28a0000000000000000000000000000000000000000000000000000000000008dc9648cf10426286008d10425f79d08a10400000000000000000000000000000000000000000000000024f64f25c61c24d24d08909b24a24a08961a24664624460400000000000000000000000000000000000024e49708f41008c51608d41009541308a51325149108440400000000000000000000000000000000000020f1cf0ce14524d14d08c08b24a24a0891452061c60c4144000000000000000000083081000000000000 6 8 2 (by decide +kernel)
def done4 : Closed := closeBank chartAt #[] #[hint0,hint23,hint2,hint69,hint67,hint6,hint33,hint8,hint36,hint10,hint74,hint14,hint13,hint12,hint52,hint53,hint15,hint18,hint19,hint20,hint21,hint22,hint1,hint24,hint25,hint26,hint27,hint28,hint7,hint29,hint55,hint30,hint31,hint32,hint34,hint35,hint38,hint75,hint40,hint41,hint42,hint43,hint44,hint45,hint46,hint49,hint48,hint47,hint50,hint51] [0xa0a0a0a0a0a0a0a0,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000] 0xb6dc71c30b6dbefb6eb6d0000000000000000000000000000000000000000000000000000000000000000000000000000000000000ac22b0891c70000000000000000000000000000000000000000000000000000000000000000000000000aa1a90891450a87270871450000000000000000000000000000000000000000000000000000000000000a69640895960888e208759608686008559600000000000000000000000000000000000000000000000009461f08904131279d30704109c6da0850410996170960410000000000000000000000000000000000000890950942cb3073933122cb0850910822cb08c09000000030f38d3012cb00000000000000000000000008a08a089089088108087087086086085085000000000000083103081081000000000000000000000000 6 8 2 (by decide +kernel)
def done5 : Closed := closeBank chartAt #[] #[hint0,hint14,hint23,hint3,hint53,hint52,hint1,hint2,hint15,hint16,hint17,hint6,hint41,hint20,hint8,hint43,hint22,hint10,hint24,hint25,hint26,hint54,hint7,hint76,hint55,hint77,hint56,hint33,hint34,hint35,hint36,hint38,hint39,hint40,hint9,hint78,hint79,hint45,hint46,hint48,hint49,hint47,hint50,hint51] [0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xfa00fa00fa00fa00,0xffff0000ffff0000,0xffffffff00000000] 0xa28aebaaaa28a69a270000000000000000000000000000000000000000000000000000000000000000000000001e67a51d138e0000000000000000000000000000000000000000000000000000000000001e46e31d12cb1e25961ce2cb0000000000000000000000000000000000000000000000001e181f1d11861de75c1ce1861db29a1cb1860000000000000000000000000000000000001cf4d91d10820cc6170ce0821d61151cb0821d44d21c60820000000000000000000000001d12501cf0410ce14d0cc0411cb1cb1c70411ca2481c60410c41440c2041000000000000 6 7 2 (by decide +kernel)
def done6 : Closed := closeBank chartAt #[done5] #[hint0,hint23,hint16,hint13,hint53,hint65,hint66,hint15,hint2,hint5,hint6,hint19,hint8,hint21,hint10,hint17,hint80,hint25,hint4,hint3,hint27,hint28,hint7,hint29,hint55,hint30,hint56,hint62,hint33,hint61,hint36,hint81,hint39,hint40,hint71,hint41,hint42,hint43,hint44,hint45,hint46,hint49,hint47,hint50,hint51] [0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xfafafafafafafafa,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000] 0xa69b2caeba69a69aaaa690000000000000000000000000000000000000000000000000000000000000000000000000000000000002687a720e30c00000000000000000000000000000000000000000000000000000000000000000000000022672520e28a2645a320c28a00000000000000000000000000000000000000000000000000000000000024e24e20d20d24c24c24b4cb24a24a20922200000000000000000000000000000000000000000000000022181f20e3cf25e6dd20c3cf21c3da20a6da00000000000000000000000000000000000000000000000024d45920e04118b6170cc04125655420a04124910425304125245020f04100000000000000000000000024e08e20d20d0cc14c0cb08b24a24a2090820000000000000000002032071841440c1081000000000000 6 8 2 (by decide +kernel)
def done7 : Closed := closeBank chartAt #[] #[hint0,hint23,hint6,hint2,hint54,hint7,hint53,hint3,hint1,hint56,hint33,hint17,hint8,hint9,hint10,hint78,hint79,hint14,hint52,hint67,hint16,hint5,hint41,hint20,hint43,hint22,hint24,hint25,hint26,hint76,hint55,hint77,hint57,hint35,hint36,hint58,hint39,hint59,hint45,hint46,hint50,hint48,hint49,hint47,hint51] [0xaa00aa00aa00aa00,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xffff0000ffff0000,0xffffffff00000000] 0xaaab2caaaaebaa9a280000000000000000000000000000000000000000000000000000000000000000000000005678a60ce30c0000000000000000000000000000000000000000000000000000000000000e59230ce2085628600cc2080000000000000000000000000000000000000000000000005586df0ce0411d679d1cc04155c6da0c804100000000000000000000000000000000000054e5190d84514cc4971d645154b50b0c84514c64861c14510000000000000000000000000d028f0ce0821cd1450cc0820cb2890c80881c61440c1081000000000000000000000000 6 8 2 (by decide +kernel)
def done8 : Closed := closeBank chartAt #[] #[hint0,hint23,hint2,hint53,hint3,hint1,hint17,hint8,hint9,hint10,hint79,hint14,hint52,hint16,hint18,hint13,hint19,hint20,hint21,hint22,hint24,hint25,hint26,hint27,hint28,hint29,hint55,hint30,hint31,hint32,hint34,hint35,hint36,hint38,hint39,hint40,hint41,hint42,hint43,hint44,hint45,hint46,hint50,hint48,hint49,hint47,hint51] [0xaa00aa00aa00aa00,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000] 0xb2cbaeaaab2cb6db2baaa0000000000000000000000000000000000000000000000000000000000000000000000000000000000000a98280891c70000000000000000000000000000000000000000000000000000000000000000000000000a70a60890890a51240870870000000000000000000000000000000000000000000000000000000000000a38a10891450a07de08714508275c08214500000000000000000000000000000000000000000000000009255b0890411106991070410846170820410965540850410000000000000000000000000000000000000893530922cb1073111102cb08f08e0000000863460852cb1033031012cb00000000000000000000000008a08a089089088108087087000000000000086086085085083103081081000000000000000000000000 6 8 2 (by decide +kernel)
def done9 : Closed := closeBank chartAt #[] #[hint0,hint23,hint1,hint2,hint24,hint25,hint26,hint5,hint18,hint82,hint12,hint83,hint3,hint14,hint52,hint67,hint8,hint29,hint55,hint19,hint10,hint30,hint21,hint84,hint15,hint85,hint16,hint34,hint35,hint36,hint38,hint39,hint40,hint86,hint78,hint87,hint20,hint22,hint45,hint46,hint88,hint89,hint50,hint48,hint90] [0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffaaffaaffaaffaa,0xffff0000ffff0000,0xffffffff00000000] 0xa69b2ca6baaaa69a280000000000000000000000000000000000000000000000000000000000000000000000001e77660d44100000000000000000000000000000000000000000000000000000000000001d46a50d634d3d03a431334d0000000000000000000000000000000000000000000000000e36620d42083212cb0d02080000000000000000000000000000000000000000000000000e07de0d40821dd71b0d00821da6180cd08d0d96170c80820000000000000000000000001d61550d40413134913100413ce28a30d04d30b2890c80411c61440c2041000000000000 6 8 2 (by decide +kernel)
def done10 : Closed := closeBank chartAt #[] #[hint0,hint23,hint3,hint12,hint67,hint53,hint1,hint2,hint15,hint5,hint17,hint18,hint13,hint19,hint8,hint21,hint10,hint24,hint25,hint26,hint6,hint54,hint28,hint7,hint29,hint55,hint30,hint56,hint32,hint33,hint34,hint35,hint36,hint38,hint39,hint40,hint42,hint78,hint44,hint45,hint46,hint89,hint49,hint47,hint50,hint51] [0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffaaffaaffaaffaa,0xffff0000ffff0000,0xffffffff00000000] 0xaaab6daaab2caaaaebaa90000000000000000000000000000000000000000000000000000000000000000000000000000000000002688271d038e0000000000000000000000000000000000000000000000000000000000000000000000002502501cf1cf10e10e08d08d0000000000000000000000000000000000000000000000000000000000001e67651d05140a45e41ce5140000000000000000000000000000000000000000000000000000000000001e38a11d01862607de1ce18624971c1c71861dd71b1d418600000000000000000000000000000000000024f49a1d004108d65808e0411045960820410975951d40412534911c60410000000000000000000000002502501cf1cf10e10e08d08d0000000000000000001cc1cb24a2481c61c6105103081081000000000000 6 8 2 (by decide +kernel)
def done11 : Closed := closeBank chartAt #[] #[hint0,hint23,hint3,hint55,hint1,hint2,hint62,hint5,hint6,hint7,hint10,hint46,hint14,hint12,hint53,hint13,hint15,hint16,hint17,hint18,hint20,hint21,hint22,hint24,hint25,hint26,hint27,hint28,hint29,hint19,hint30,hint31,hint32,hint33,hint34,hint35,hint91,hint37,hint38,hint39,hint40,hint41,hint42,hint43,hint44,hint64,hint51,hint48,hint49,hint47,hint50] [0xaaaa0000aaaa0000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000] 0xc30baecb2c30c71c2fbae00000000000000000000000000000000000000000000000000000000000000000000000000000000000008b92d08a75d0000000000000000000000000000000000000000000000000000000000000000000000000ac86b08a2080aa26909d2080000000000000000000000000000000000000000000000000000000000009689e694a1040a48e209d1040a181f08810400000000000000000000000000000000000000000000000009561e08a04109d0dc0820410896da0880410996170840410000000000000000000000000000000000003ca4563d530c08f09400000008809308230c3d24503c430c08e08d08130c00000000000000000000000008b1cb08a14a0000000000000890890881480861c6084144083083081081000000000000000000000000 6 8 2 (by decide +kernel)
def done12 : Closed := closeBank chartAt #[] #[hint0,hint14,hint23,hint3,hint53,hint52,hint1,hint2,hint17,hint16,hint6,hint41,hint20,hint8,hint43,hint22,hint10,hint24,hint25,hint26,hint54,hint7,hint76,hint55,hint77,hint56,hint33,hint57,hint35,hint36,hint58,hint39,hint59,hint9,hint78,hint79,hint45,hint46,hint48,hint49,hint47,hint50,hint51] [0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00aa00ff00aa00,0xffff0000ffff0000,0xffffffff00000000] 0x9e7aaaa699e7a289e60000000000000000000000000000000000000000000000000000000000000000000000001e57641d034d0000000000000000000000000000000000000000000000000000000000001e36a21d028a1e15551cd28a0000000000000000000000000000000000000000000000001e07de1d01861dd71b1cd1861da2191ca1860000000000000000000000000000000000001ce4981d00820cb5d60cd0821d51141ca0821d34911c60820000000000000000000000001d024f1ce0410cd14c0cb0411ca1ca1c70411c82481c60410c41440c2041000000000000 6 7 2 (by decide +kernel)
def done13 : Closed := closeBank chartAt #[done12] #[hint0,hint23,hint3,hint53,hint52,hint67,hint1,hint13,hint17,hint65,hint6,hint20,hint21,hint10,hint24,hint25,hint26,hint27,hint28,hint7,hint8,hint60,hint55,hint9,hint30,hint31,hint32,hint33,hint61,hint35,hint36,hint2,hint5,hint37,hint38,hint39,hint40,hint71,hint43,hint44,hint45,hint46,hint92,hint49,hint47,hint50,hint51] [0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffaaaaffffaaaa,0xffffffff00000000] 0xaebaebbaeb6daebb2caea00000000000000000000000000000000000000000000000000000000000000000000000000000000000014d80d14c7cc0000000000000000000000000000000000000000000000000000000000000000000000001697a808d5140000000000000000000000000000000000000000000000000000000000000000000000001676e608d28a14528a09f1650974d309428a0000000000000000000000000000000000000000000000008648e284d18616020815f18615e75c09418615b69908a18600000000000000000000000000000000000014c3d808d0411450c308204109759509404109349108a0411503ce0860410000000000000000000000001cd24d1cc10400000000000000000008708b14a14a0851041c82481c6106143103081081000000000000 6 8 2 (by decide +kernel)
def done14 : Closed := closeBank chartAt #[] #[hint0,hint23,hint2,hint69,hint67,hint1,hint39,hint6,hint33,hint8,hint36,hint14,hint13,hint12,hint52,hint53,hint15,hint17,hint18,hint19,hint20,hint22,hint24,hint25,hint26,hint27,hint28,hint7,hint29,hint55,hint40,hint30,hint21,hint31,hint32,hint34,hint35,hint38,hint41,hint42,hint43,hint44,hint64,hint93,hint49,hint48,hint47,hint50,hint51] [0xaaaaaaaa00000000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000] 0xb2cc30befb2cbaeb2db2c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000ab2aa0a02490000000000000000000000000000000000000000000000000000000000000000000000000a92280a01c70a76e60891c700000000000000000000000000000000000000000000000000000000000009e1a50a014508a9230891450888a10871450000000000000000000000000000000000000000000000000a05df09e04131375c30904109b6990870410985d608504100000000000000000000000000000000000008c0950000003093943132cb0870920822cb0910900852cb30f38d3012cb00000000000000000000000000000000000008a10a089089088088087087086086085085083103081081000000000000000000000000 6 8 2 (by decide +kernel)
def done15 : Closed := closeBank chartAt #[] #[hint0,hint14,hint23,hint3,hint53,hint52,hint1,hint2,hint17,hint16,hint6,hint41,hint20,hint8,hint43,hint22,hint10,hint24,hint25,hint26,hint54,hint7,hint76,hint55,hint77,hint56,hint33,hint57,hint35,hint36,hint58,hint39,hint59,hint9,hint78,hint79,hint45,hint46,hint48,hint49,hint47,hint50,hint51] [0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00aa00aa00,0xffff0000ffff0000,0xffffffff00000000] 0x9e7aaaa699e7a289e60000000000000000000000000000000000000000000000000000000000000000000000001e57641d034d0000000000000000000000000000000000000000000000000000000000001e36a21d028a1e15551cd28a0000000000000000000000000000000000000000000000001e07de1d01861dd71b1cd1861da2191ca1860000000000000000000000000000000000001ce4981d00820cb5d60cd0821d51141ca0821d34911c60820000000000000000000000001d024f1ce0410cd14c0cb0411ca1ca1c70411c82481c60410c41440c2041000000000000 6 7 2 (by decide +kernel)
def done16 : Closed := closeBank chartAt #[done15] #[hint0,hint23,hint16,hint13,hint53,hint65,hint66,hint1,hint2,hint17,hint5,hint6,hint19,hint8,hint22,hint24,hint25,hint26,hint27,hint28,hint7,hint29,hint55,hint10,hint70,hint11,hint3,hint31,hint32,hint33,hint34,hint35,hint36,hint81,hint39,hint74,hint41,hint42,hint78,hint79,hint71,hint45,hint46,hint49,hint47,hint50,hint51] [0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000,0xffffffffaaaaaaaa] 0xaebaebbaeb6daebb2caeb00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000028a34d29a30c2aa82921734d00000000000000000000000000000000000000000000000000000000000028a2cb2082a82277662172cb2a552420d2cb00000000000000000000000000000000000000000000000028a2492081c72238a12171c72a07de20d1c721d71b20b1c700000000000000000000000000000000000028a10429a04129941821704118c5950cd0412944d220b04129140f20704100000000000000000000000000000000000000000020320e0cd14d0cc08c28b28b20a0822890892072071841440c1081000000000000 6 8 2 (by decide +kernel)
def done17 : Closed := closeBank chartAt #[] #[hint0,hint14,hint2,hint65,hint94,hint23,hint3,hint12,hint52,hint53,hint1,hint15,hint16,hint17,hint18,hint6,hint19,hint20,hint8,hint21,hint22,hint10,hint95,hint91,hint96,hint24,hint27,hint28,hint7,hint29,hint55,hint30,hint31,hint32,hint33,hint34,hint35,hint36,hint38,hint39,hint40,hint41,hint42,hint43,hint44,hint45,hint46,hint48,hint49,hint47,hint50,hint51] [0xaaaaaaaaaaaaaaaa,0xc0c0c0c0c0c0c0c0,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000] 0xc30cf3cb2c30c71c30c2f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000ae96d0954920000000000000000000000000000000000000000000000000000000000000000000000000ac8ab0953cf0aa7290923cf0000000000000000000000000000000000000000000000000000000000000a89e609528a0a592309228a0a286008f28a00000000000000000000000000000000000000000000000009309f09514519079d19214509c6da08f14508609900000000000000000000000000000000000000000009809809509509719709209209609608f08f00000000000000000000000000000000000000000000000009531409304119221119004108f08e08204108d30b08a0411892071850410840c3082041000000000000 6 8 2 (by decide +kernel)
def done18 : Closed := closeBank chartAt #[] #[hint0,hint14,hint25,hint3,hint52,hint69,hint67,hint26,hint2,hint97,hint16,hint4,hint5,hint13,hint18,hint6,hint19,hint20,hint8,hint21,hint22,hint10,hint24,hint7,hint98,hint99,hint100,hint101,hint33,hint75,hint102,hint36,hint103,hint40,hint41,hint42,hint43,hint44,hint45,hint46,hint48,hint49,hint47,hint104,hint50,hint51] [0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xfcfcfcfcfcfcfcfc,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000] 0xa69b6db2caeba69aaaa680000000000000000000000000000000000000000000000000000000000000000000000000000000000003277e62154920000000000000000000000000000000000000000000000000000000000000000000000002257242153cf3235e22123cf0000000000000000000000000000000000000000000000000000000000003133132152153103103120d231731720f20f0000000000000000000000000000000000000000000000002217602151c731f1de21275221c6da20f1cf0000000000000000000000000000000000000000000000003130932152150d06500d209231761720f08f0000000000000000002032160000000000000000000000003152942130411921110d004130f30e20c04130c10430d04130b2892070411851040c2041000000000000 6 8 2 (by decide +kernel)
def done19 : Closed := closeBank chartAt #[] #[hint0,hint14,hint23,hint3,hint12,hint52,hint1,hint2,hint24,hint25,hint26,hint6,hint27,hint83,hint8,hint29,hint55,hint19,hint10,hint30,hint21,hint15,hint16,hint17,hint18,hint20,hint22,hint31,hint32,hint33,hint34,hint35,hint36,hint38,hint39,hint40,hint86,hint78,hint87,hint45,hint46,hint47,hint48,hint73,hint50,hint105] [0xcccccccccccccccc,0xeeaaeeaaeeaaeeaa,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000] 0xaebb6db2caebaeaa690000000000000000000000000000000000000000000000000000000000000000000000001e88271d238e0000000000000000000000000000000000000000000000000000000000001e67651d22cb1e434d1ce2cb0000000000000000000000000000000000000000000000001e38a11d21861e07de1ce1861dd71b1cb1860000000000000000000000000000000000001d259a1d40410ce1590d10411cb1d81c70411d75951c60410000000000000000000000001d42531d20820d140f0ce0821cd10c1cb0821ca2481c60820c51040c1081000000000000 6 7 2 (by decide +kernel)
def done20 : Closed := closeBank chartAt #[done19] #[hint0,hint14,hint2,hint71,hint13,hint23,hint3,hint52,hint55,hint1,hint15,hint16,hint17,hint18,hint6,hint19,hint20,hint8,hint21,hint22,hint10,hint101,hint42,hint44,hint24,hint25,hint26,hint27,hint29,hint30,hint31,hint32,hint33,hint34,hint35,hint36,hint38,hint39,hint40,hint59,hint45,hint46,hint48,hint49,hint47,hint50,hint51] [0xaaaaaaaaaaaaaaaa,0xcc00cc00cc00cc00,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000] 0xaebbaeb6daebb2cb2caea0000000000000000000000000000000000000000000000000000000000000000000000000000000000000a98e809445100000000000000000000000000000000000000000000000000000000000000000000000009782709438e09619609138e0000000000000000000000000000000000000000000000000000000000000a69640942490a38a10912490a07de08e24900000000000000000000000000000000000000000000000009265d09414518f21c19114508609b00000009a6580891450000000000000000000000000000000000000970970940940961960910910000000000000950950890890000000000000000000000000000000000000942d30920411911d018f04108e08d08204108c2ca0890411881c7185041084083082041000000000000 6 8 2 (by decide +kernel)
def done21 : Closed := closeBank chartAt #[] #[hint0,hint14,hint28,hint3,hint12,hint52,hint53,hint1,hint2,hint15,hint16,hint17,hint5,hint83,hint7,hint67,hint19,hint20,hint8,hint21,hint22,hint10,hint26,hint98,hint27,hint32,hint95,hint34,hint35,hint36,hint38,hint39,hint40,hint41,hint42,hint43,hint44,hint45,hint46,hint48,hint49,hint47,hint50,hint106,hint51] [0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffccffccffccffcc,0xffff0000ffff0000,0xffffffff00000000] 0xa28b2caebaaaa28a69a270000000000000000000000000000000000000000000000000000000000000000000000000000000000003267652154920000000000000000000000000000000000000000000000000000000000000000000000003133132152150d00d00d20d20000000000000000000000000000000000000000000000000000000000002246a321538e0e23a12120d20000000000000000000000000000000000000000000000000000000000002207de2151c731d71b2121c730c6592081c721a65920e1c70000000000000000000000000000000000003135d32150820d00d00d20820000000000000000002032183165d62070870000000000000000000000003152942130410d21510d00410cf1450c30410ce0cd20304130b2892070410c61440c2041000000000000 6 8 2 (by decide +kernel)
def done22 : Closed := closeBank chartAt #[] #[hint0,hint14,hint52,hint12,hint16,hint15,hint18,hint20,hint22,hint2,hint5,hint1,hint26,hint6,hint7,hint10,hint46,hint23,hint25,hint27,hint29,hint30,hint33,hint8,hint36,hint31,hint34,hint38,hint43,hint48,hint51,hint47,hint49,hint50] [0xaaaaaaaaaaaaaaaa,0xcccc0000cccc0000,0xcccccccccccccccc,0xf0f0f0f000000000,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000] 0x2001e02102002001f01e01d00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000001700000000000000000000000000000000000000000000000000000000000000000000000000000000000000001c00000d00000e00000d00000000000000000000000000000000000000000000000000000000000000000000000000001b00000000001a00000b00001900000b00000000000000000000000000000000000000000000000000000000000000000000000000001800001700001600000d00000000000000000000000000000000000000000000000000000000000000001500001100001400000000001300001100000c00001100001200001100000000000000000000000000000000000000001000000f00000000000000000e00000d00000c00000b00000a000009000000000000000000000000000000000000000008000001000007000001000006000001000005000001000004000001000003000001000002000001000000000000 6 7 2 (by decide +kernel)
def done23 : Closed := closeBank chartAt #[] #[hint0,hint14,hint52,hint12,hint16,hint18,hint20,hint107,hint39,hint108,hint6,hint7,hint40,hint96,hint2,hint5,hint23,hint109,hint27,hint29,hint110,hint25,hint111,hint8,hint112,hint38,hint59,hint33,hint64,hint36,hint48,hint51,hint47,hint49,hint50] [0xaaaaaaaaaaaaaaaa,0xcccc0000cccc0000,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000,0xfffffffff0f0f0f0] 0x2102101f02202102001f01e00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001d00001700001c00001700000000000000000000000000000000000000000000000000000000000000000000000000001b00000a00001a00000a00000b00000a00000000000000000000000000000000000000000000000000000000000000000000000000000000001900001800001700001600000a00000000000000000000000000000000000000000000000000001500001000001400001000001300000000001200001000001100001000000000000000000000000000000000000000000f00000e00000d00000c00000000000000000b00000a000009000008000000000000000000000000000000000000000004000001000007000001000006000001000005000001000004000001000003000001000002000001000000000000 6 7 2 (by decide +kernel)
def done24 : Closed := closeBank chartAt #[done22,done23] #[hint0,hint14,hint3,hint52,hint67,hint23,hint12,hint53,hint1,hint13,hint15,hint16,hint17,hint18,hint6,hint20,hint8,hint21,hint22,hint10,hint2,hint26,hint5,hint7,hint46,hint25,hint27,hint28,hint29,hint30,hint31,hint32,hint33,hint34,hint35,hint36,hint71,hint38,hint39,hint40,hint72,hint43,hint44,hint64,hint48,hint49,hint51,hint47,hint50] [0xaaaaaaaaaaaaaaaa,0xcccc0000cccc0000,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000] 0xb6dbaec30b6dbefbaeb6c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000988eb0934100000000000000000000000000000000000000000000000000000000000000000000000000aa82909338e0825d709038e000000000000000000000000000000000000000000000000000000000000a279a59132080a38a10902080a07de08e20800000000000000000000000000000000000000000000000009165d09314508209c0000000976da08e14509565508814500000000000000000000000000000000000009859809351300000000000009709708e50e0955950885080000000000000000000000000000000000002532d22510410900cf08204108e08d08204124c2ca2480410870c60850410840c3082041000000000000 6 8 2 (by decide +kernel)
def done25 : Closed := closeBank chartAt #[] #[hint0,hint14,hint52,hint16,hint15,hint18,hint68,hint22,hint55,hint99,hint1,hint24,hint6,hint113,hint29,hint21,hint33,hint19,hint91,hint2,hint5,hint31,hint102,hint35,hint38,hint41,hint7,hint43,hint45,hint10,hint48,hint47,hint49,hint50,hint51] [0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f000000000,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffccccffffcccc,0xffffffff00000000] 0x2001f02202102002001f01e00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000f00001d00000000000000000000000000000000000000000000000000000000000000000000000000000000000000001c00001100000000000000000000000000000000000000000000000000000000000000000000000000000000000000001b00000c00001a00000c00001900000c00000000000000000000000000000000000000000000000000000000000000001800000000001700000a00001600000a00001500000a00000000000000000000000000000000000000000000000000000000000000001400001300001200001100001000000c00000000000000000000000000000000000000000000000000000f00000800000000000000000000000e00000d00000c00000b00000a000009000008000000000000000000000000000007000001000002000001000006000001000005000001000004000001000003000001000002000001000000000000 6 7 2 (by decide +kernel)
def done26 : Closed := closeBank chartAt #[] #[hint0,hint14,hint52,hint16,hint18,hint68,hint107,hint55,hint75,hint6,hint113,hint29,hint114,hint99,hint111,hint19,hint115,hint39,hint38,hint41,hint7,hint59,hint33,hint93,hint91,hint40,hint2,hint5,hint48,hint47,hint49,hint50,hint51] [0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffccccffffcccc,0xffffffff00000000,0xfffffffff0f0f0f0] 0x1e01e01d02001f01e01d01c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001b00001a00001700001900000000000000000000000000000000000000000000000000000000000000000000000000001800000f00001700000f00000000000000000000000000000000000000000000000000000000000000000000000000001600000900001500000900001400000900001300000900000000000000000000000000000000000000000000000000000000000000000000001200000800001100001000000f00000e00000900000000000000000000000000000000000000000d00000700000c00000700000000000000000000000b00000a000009000008000007000000000000000000000000000003000001000006000001000002000001000005000001000004000001000003000001000002000001000000000000 6 7 2 (by decide +kernel)
def done27 : Closed := closeBank chartAt #[done25,done26] #[hint0,hint14,hint3,hint52,hint55,hint1,hint13,hint15,hint16,hint17,hint66,hint18,hint6,hint19,hint68,hint9,hint67,hint21,hint22,hint10,hint24,hint99,hint26,hint113,hint7,hint29,hint31,hint32,hint33,hint102,hint35,hint91,hint2,hint5,hint71,hint38,hint39,hint40,hint72,hint41,hint42,hint43,hint44,hint45,hint46,hint48,hint49,hint47,hint50,hint51] [0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffccccffffcccc,0xffffffff00000000] 0xbaebefc71c30baebefbad0000000000000000000000000000000000000000000000000000000000000000000000000000000000000918510938130000000000000000000000000000000000000000000000000000000000000000000000000ac7eb09334d0000000000000000000000000000000000000000000000000000000000000000000000000aa72909330c0826180a030c0a862708d30c0000000000000000000000000000000000000000000000009a59238931450a179e0a014509f79d08d14509c6da08c14500000000000000000000000000000000000009155109310400000000000000000008209909809708c10c0965540851050000000000000000000000002932121910410900c308204108f0ce08d04108c08b0820412892071850410840c3082041000000000000 6 8 2 (by decide +kernel)
def done28 : Closed := closeBank chartAt #[] #[hint0,hint14,hint2,hint65,hint94,hint23,hint3,hint12,hint52,hint53,hint1,hint15,hint16,hint17,hint18,hint6,hint19,hint20,hint8,hint40,hint22,hint10,hint75,hint95,hint91,hint24,hint26,hint27,hint28,hint7,hint29,hint55,hint30,hint31,hint32,hint33,hint34,hint35,hint36,hint38,hint39,hint41,hint42,hint59,hint116,hint64,hint93,hint48,hint49,hint47,hint50,hint51] [0xaaaaaaaaaaaaaaaa,0xcccccccc00000000,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000] 0xc30cf3cb2c30c71c30c2f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000ae9ad0954920000000000000000000000000000000000000000000000000000000000000000000000000ac8eb0953cf0aa7690923cf000000000000000000000000000000000000000000000000000000000000093a2709528a0a696409228a0a38a108f28a0000000000000000000000000000000000000000000000000860a00000001907de19214509d71b08f14509a09908a14500000000000000000000000000000000000000000000000009819809209209709708f08f09609608a08a00000000000000000000000000000000000009531409304119221119004108f08e08204108d30b08a0411892071850410840c3082041000000000000 6 8 2 (by decide +kernel)
def done29 : Closed := closeBank chartAt #[] #[hint0,hint14,hint25,hint3,hint52,hint69,hint67,hint1,hint2,hint15,hint16,hint17,hint5,hint18,hint6,hint19,hint20,hint8,hint21,hint117,hint11,hint13,hint26,hint7,hint98,hint99,hint30,hint31,hint32,hint33,hint34,hint35,hint36,hint103,hint39,hint96,hint41,hint42,hint43,hint44,hint45,hint46,hint48,hint49,hint47,hint50,hint51,hint104] [0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000,0xffffffffcccccccc] 0xbefaebbaeb6daebb2caea00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000030c3cf30345132982821245100000000000000000000000000000000000000000000000000000000000030c5d720838e22776621238e3255e421138e00000000000000000000000000000000000000000000000030c5962081c72238a12121c73207de2111c721d71b20e1c700000000000000000000000000000000000000000000000000000020321a0cf64f0d109131761720e08e31609620720700000000000000000000000030c1043150413142932120411911100cf04130e30d20c04130b2892070411851040c2041000000000000 6 8 2 (by decide +kernel)
def done30 : Closed := closeBank chartAt #[] #[hint0,hint23,hint1,hint2,hint24,hint25,hint26,hint14,hint3,hint12,hint53,hint52,hint6,hint27,hint28,hint7,hint8,hint29,hint55,hint19,hint10,hint30,hint21,hint15,hint16,hint31,hint85,hint34,hint35,hint36,hint38,hint39,hint40,hint18,hint20,hint22,hint41,hint42,hint43,hint44,hint45,hint46,hint118,hint49,hint48,hint50,hint51] [0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xfaaafaaafaaafaaa,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000] 0xaebbaeb6daecaebaaa0000000000000000000000000000000000000000000000000000000000000000000000000e97680d44100000000000000000000000000000000000000000000000000000000000000e76a60d430c0e53e40d030c0000000000000000000000000000000000000000000000000d46230d61c72102e22131c70cc0e10c31c70000000000000000000000000000000000000e07de0d40820dd71b0d00820da5d90cc0820d85d70c70870000000000000000000000000d61550d40412134912100410cf38d0cc04120b2892070470c61440c2041000000000000 6 7 2 (by decide +kernel)
def done31 : Closed := closeBank chartAt #[done30] #[hint0,hint14,hint23,hint3,hint12,hint52,hint53,hint2,hint71,hint13,hint1,hint119,hint16,hint62,hint18,hint6,hint19,hint20,hint8,hint21,hint22,hint10,hint98,hint24,hint25,hint26,hint27,hint28,hint7,hint29,hint55,hint30,hint120,hint116,hint31,hint34,hint35,hint36,hint38,hint39,hint40,hint41,hint42,hint43,hint44,hint45,hint46,hint48,hint49,hint47,hint50,hint51] [0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf000f000f000f000,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000] 0xc30cf3cb2c30c30c71c2f0000000000000000000000000000000000000000000000000000000000000000000000000000000000001ee96d1d54920000000000000000000000000000000000000000000000000000000000000000000000001ec1eb1d53cf1ea7291d23cf0000000000000000000000000000000000000000000000000000000000001e89e61d528a1e59231d228a1c71e20000000000000000000000000000000000000000000000000000001e11e11d51d51e00e01d21d20000000000000000000000000000000000000000000000000000000000001d361f1d50820d079d0d20821dc6da1cf0821d96171ca0821c35961c70820000000000000000000000001d53141d30410d21510d00411cf1ce1c70411cd30b1ca0411c91c81c70410c61440c2041000000000000 6 8 2 (by decide +kernel)
def done32 : Closed := closeBank chartAt #[] #[hint0,hint14,hint23,hint3,hint12,hint52,hint53,hint67,hint32,hint2,hint15,hint16,hint17,hint85,hint33,hint5,hint19,hint20,hint8,hint21,hint22,hint10,hint121,hint25,hint101,hint28,hint95,hint29,hint55,hint30,hint31,hint122,hint123,hint36,hint40,hint124,hint42,hint59,hint44,hint45,hint46,hint48,hint49,hint47,hint50,hint51] [0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xfff0fff0fff0fff0,0xffff0000ffff0000,0xffffffff00000000] 0xaaab6db2cb2caaaaebaa90000000000000000000000000000000000000000000000000000000000000000000000000000000000002688672554920000000000000000000000000000000000000000000000000000000000000000000000002622622552552643e42522520000000000000000000000000000000000000000000000000000000000002663a52552552646a42523920000000000000000000000000000000000000000000000000000000000002628e225520826181f25220800000000000000000024925e0000000000000000000000000000000000002535dd2550820d071b0d208224f65924908225a65924e0822585d62480820000000000000000000000002552d42530411d21510d004124f2cb24904124e24d24904124c2ca2480411c61440c2041000000000000 6 8 2 (by decide +kernel)
def done33 : Closed := closeBank chartAt #[] #[hint0,hint14,hint23,hint3,hint12,hint52,hint53,hint2,hint65,hint13,hint1,hint15,hint16,hint17,hint18,hint6,hint19,hint20,hint8,hint21,hint22,hint10,hint99,hint109,hint25,hint75,hint27,hint28,hint7,hint29,hint55,hint30,hint95,hint93,hint31,hint32,hint33,hint34,hint38,hint39,hint40,hint41,hint42,hint43,hint44,hint45,hint46,hint48,hint49,hint47,hint50,hint51] [0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f00000f0f00000,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000] 0xc30cf3cb2c30c30c71c2f0000000000000000000000000000000000000000000000000000000000000000000000000000000000001ee1ed1d54920000000000000000000000000000000000000000000000000000000000000000000000001ec92b1d53cf1ea7291d23cf0000000000000000000000000000000000000000000000000000000000001e89e61d528a1c70e50000001e48e21cf28a0000000000000000000000000000000000000000000000001e11e11d51d50000000000001e01e01cf1cf0000000000000000000000000000000000000000000000001d361f1d50820d079d0d20821dc6da1cf0821d96171ca0821c35961c70820000000000000000000000001d53141d30410d21510d00411cf1ce1c70411cd30b1ca0411c92081c70410c61440c2041000000000000 6 8 2 (by decide +kernel)
def done34 : Closed := closeBank chartAt #[] #[hint0,hint14,hint23,hint3,hint12,hint52,hint53,hint67,hint35,hint2,hint119,hint16,hint62,hint5,hint18,hint6,hint91,hint36,hint13,hint21,hint22,hint10,hint24,hint25,hint26,hint27,hint28,hint7,hint55,hint30,hint125,hint123,hint33,hint34,hint40,hint108,hint120,hint43,hint44,hint64,hint46,hint48,hint49,hint47,hint50,hint51] [0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xfffff0f0fffff0f0,0xffffffff00000000] 0xaaab6db6db2caaaaebaa90000000000000000000000000000000000000000000000000000000000000000000000000000000000003623622552550000000000000000000000000000000000000000000000000000000000000000000000003684672552550000000000000000000000000000000000000000000000000000000000000000000000002668252553cf34d6db2493cf3646db2513cf0000000000000000000000000000000000000000000000002628e22552080000000000000000002490e12607de24f20f0000000000000000000000000000000000003535dd25508234d71c3430820d071c0d108235b69924f0823585d62480820000000000000000000000003552d425304134d1453520411d11450d004134f34e24d04134c2ca2480411c61440c2041000000000000 6 8 2 (by decide +kernel)
def done35 : Closed := closeBank chartAt #[done22,done25] #[hint0,hint14,hint23,hint37,hint12,hint52,hint53,hint2,hint16,hint5,hint1,hint15,hint17,hint18,hint6,hint19,hint20,hint8,hint21,hint22,hint10,hint25,hint24,hint26,hint27,hint28,hint7,hint71,hint29,hint55,hint72,hint30,hint33,hint36,hint31,hint32,hint34,hint35,hint38,hint41,hint42,hint43,hint44,hint45,hint46,hint48,hint49,hint47,hint50,hint51] [0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f000000000,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000] 0xbaec71c30baebaebefbad0000000000000000000000000000000000000000000000000000000000000000000000000000000000001ec86b1d44510000000000000000000000000000000000000000000000000000000000000000000000001ea8291d438e1e86a71d138e0000000000000000000000000000000000000000000000000000000000001c71e60000001e19641d128a1e08e21ce28a0000000000000000000000000000000000000000000000000000000000001e12611d11d11e01e01ce1ce0000000000000000000000000000000000000000000000001d255f1d408278f75c6d10821da6581ce0821d75561ca0821c95551c70820000000000000000000000001d42131d20410d11500cf0411ce1cd1c70411cc20b1ca0411c92081c70410c61440c2041000000000000 6 8 2 (by decide +kernel)
def done36 : Closed := closeBank chartAt #[done23,done26] #[hint0,hint14,hint23,hint37,hint12,hint52,hint53,hint75,hint2,hint16,hint39,hint18,hint6,hint19,hint20,hint8,hint40,hint107,hint74,hint5,hint109,hint25,hint27,hint28,hint7,hint71,hint29,hint55,hint72,hint110,hint96,hint111,hint124,hint33,hint112,hint108,hint36,hint38,hint41,hint42,hint59,hint116,hint64,hint93,hint48,hint49,hint47,hint50,hint51] [0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000,0xfffffffff0f0f0f0] 0xb6db6dc30befb6dbaeb6c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002139242083cf22b92a2103cf00000000000000000000000000000000000000000000000000000000000020886120830c22986821030c22762620f30c0000000000000000000000000000000000000000000000000000000000000000002082252248e220f28f22181f20c28c00000000000000000000000000000000000021355520808221e55d21008270d6da64f0822185d620c08220755420a0820000000000000000000000002132492080412122512100410cf14e0cd04120c20b20804120a2492070410c61440c2041000000000000 6 8 2 (by decide +kernel)
def done37 : Closed := closeBank chartAt #[] #[hint0,hint23,hint1,hint2,hint24,hint25,hint26,hint6,hint27,hint28,hint83,hint14,hint3,hint12,hint53,hint52,hint8,hint29,hint55,hint19,hint10,hint30,hint21,hint31,hint32,hint33,hint15,hint17,hint16,hint34,hint35,hint36,hint38,hint39,hint40,hint18,hint41,hint86,hint43,hint44,hint20,hint22,hint45,hint46,hint47,hint92,hint50,hint48,hint51] [0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffaaaaaaffaaaaaa,0xffff0000ffff0000,0xffffffff00000000] 0xb6dc30b6fbaeb6db2c0000000000000000000000000000000000000000000000000000000000000000000000000eb7ea0d44100000000000000000000000000000000000000000000000000000000000000d47290d62cb3103e83132cb0000000000000000000000000000000000000000000000000e76660d41c70e52a40d01c70c31e30cb0cb0000000000000000000000000000000000000e28600d40820df79d0d00820dc6da0cb08b0d96170c70820000000000000000000000000d61550d404131349131004130f38d30b04b0ca2480c70410c61440c2041000000000000 6 7 2 (by decide +kernel)
def done38 : Closed := closeBank chartAt #[] #[hint0,hint14,hint1,hint2,hint15,hint16,hint17,hint18,hint6,hint23,hint3,hint12,hint52,hint53,hint19,hint20,hint8,hint21,hint22,hint10,hint31,hint32,hint33,hint24,hint26,hint25,hint34,hint35,hint36,hint38,hint39,hint40,hint27,hint113,hint28,hint41,hint126,hint43,hint44,hint29,hint55,hint30,hint45,hint46,hint48,hint127,hint50,hint47,hint51] [0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffccccccffcccccc,0xffff0000ffff0000,0xffffffff00000000] 0xb6dc30befbaeb6db6c0000000000000000000000000000000000000000000000000000000000000000000000000eb72a0d34100000000000000000000000000000000000000000000000000000000000000d16690d324928ea272902490000000000000000000000000000000000000000000000000e65a50d32080e48630d02080e28600c92090000000000000000000000000000000000000df79d0d30820dc6da0d00820d96170c90890d65540c80820000000000000000000000000d31520d104129030f28e04128d30b2890410c80c70c30410c61440c2041000000000000 6 7 2 (by decide +kernel)
def done39 : Closed := closeBank chartAt #[done37,done38] #[hint0,hint14,hint23,hint3,hint12,hint52,hint53,hint1,hint2,hint15,hint16,hint17,hint71,hint13,hint18,hint6,hint19,hint20,hint8,hint21,hint22,hint10,hint24,hint25,hint26,hint72,hint27,hint28,hint29,hint55,hint30,hint123,hint31,hint32,hint33,hint34,hint35,hint36,hint38,hint39,hint40,hint128,hint41,hint43,hint44,hint45,hint46,hint48,hint49,hint47,hint51,hint50] [0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff000000ff000000,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000] 0xc30cb2cf3cb2c30c71c2f00000000000000000000000000000000000000000000000000000000000000000000000000000000000022e96d21549200000000000000000000000000000000000000000000000000000000000000000000000022c8ab2153cf2080ea0000000000000000000000000000000000000000000000000000000000000000002292292152150000000000000000000000000000000000000000000000000000000000000000000000002289e62151c72259232121c722286020f1c72087df2081c70000000000000000000000000000000000002135de2150820d075c0d20822036da20f0822032192080822185d62070820000000000000000000000002152942130410d21510d004120f20e20804120d20c20804120b2892070410c61440c2041000000000000 6 8 2 (by decide +kernel)
def done40 : Closed := closeBank chartAt #[] #[hint0,hint14,hint23,hint3,hint12,hint52,hint53,hint1,hint2,hint15,hint16,hint17,hint5,hint83,hint7,hint42,hint9,hint67,hint21,hint22,hint10,hint24,hint25,hint26,hint28,hint55,hint30,hint32,hint95,hint35,hint120,hint38,hint39,hint40,hint41,hint44,hint129,hint46,hint48,hint49,hint47,hint50,hint51,hint130] [0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffff00ffffff00,0xffffffff00000000] 0x9e7aebaaaa699e7a289e60000000000000000000000000000000000000000000000000000000000000000000000000000000000003233232142140000000000000000000000000000000000000000000000000000000000000000000000003257a42143cf00000000000000000000000000000000000000000000000000000000000000000000000022372321438e0000000000000000002080e200000000000000000000000000000000000000000000000022181f2141c730c6db2081c731e75d20f1c721c6db20e1c700000000000000000000000000000000000031259a2140820c36180c30820cf6590c30820ce6182030823175952070820000000000000000000000003142932120410d11450c30410d01450cf0410ce0cd20304130b2892070410c61440c2041000000000000 6 8 2 (by decide +kernel)
def done41 : Closed := closeBank chartAt #[] #[hint0,hint23,hint1,hint2,hint24,hint25,hint26,hint6,hint27,hint28,hint7,hint14,hint3,hint12,hint53,hint52,hint8,hint29,hint55,hint19,hint10,hint30,hint21,hint31,hint32,hint85,hint15,hint17,hint16,hint34,hint35,hint36,hint38,hint39,hint40,hint18,hint41,hint42,hint43,hint87,hint20,hint22,hint45,hint46,hint131,hint49,hint50,hint48,hint132] [0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffaaffaaaaaaaaaa,0xffff0000ffff0000,0xffffffff00000000] 0xb6dc30b6fbaeb6db2c0000000000000000000000000000000000000000000000000000000000000000000000000eb7ea0d44100000000000000000000000000000000000000000000000000000000000000d47290d62cb3103e83132cb0000000000000000000000000000000000000000000000000e76660d41c70e52a40d01c70c31e30cb0cb0000000000000000000000000000000000000e28600d40820df79d0d00820dc6da0cb08b0d96170c70820000000000000000000000000d61550d404131349131004130f38d30b04b0ca2480c70410c61440c2041000000000000 6 7 2 (by decide +kernel)
def done42 : Closed := closeBank chartAt #[done41] #[hint0,hint14,hint23,hint3,hint12,hint52,hint53,hint1,hint2,hint15,hint16,hint17,hint71,hint13,hint18,hint6,hint19,hint20,hint8,hint21,hint22,hint10,hint24,hint25,hint26,hint98,hint27,hint28,hint7,hint29,hint55,hint30,hint124,hint31,hint32,hint34,hint35,hint36,hint38,hint39,hint40,hint120,hint41,hint42,hint43,hint45,hint46,hint48,hint49,hint47,hint50,hint51] [0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff0000000000,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000] 0xc30cf3cb2c30c30c71c2f00000000000000000000000000000000000000000000000000000000000000000000000000000000000022e96d21549200000000000000000000000000000000000000000000000000000000000000000000000020822c00000022b72a2123cf0000000000000000000000000000000000000000000000000000000000000000000000002290e92122120000000000000000000000000000000000000000000000000000000000002289e62151c72259232121c72088a120f1c72088202081c70000000000000000000000000000000000002135df2150820d079d0d208221c6da20f0822036592080822185d62070820000000000000000000000002152942130410d21510d004120f20e20804120d20c20804120b2892070410c61440c2041000000000000 6 8 2 (by decide +kernel)
def done43 : Closed := closeBank chartAt #[] #[hint0,hint14,hint23,hint3,hint12,hint52,hint53,hint67,hint1,hint2,hint15,hint16,hint17,hint85,hint33,hint19,hint20,hint8,hint44,hint79,hint5,hint24,hint25,hint26,hint28,hint95,hint29,hint55,hint116,hint32,hint34,hint35,hint36,hint39,hint42,hint43,hint129,hint128,hint48,hint49,hint47,hint50,hint51,hint130] [0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000,0xffffffffff00ff00] 0xaeb9e7aaaa699e7a289e60000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002548a224945126582425245100000000000000000000000000000000000000000000000000000000000000000000000000000024926326266225139100000000000000000000000000000000000000000000000024975d24920825c8612522082607de25120824e75d24920800000000000000000000000000000000000025461824908225259625c0820cf6da0d108225961824e0822575952480820000000000000000000000002542cb2490412532cb2520411d11500cf04124e24d24904124c2ca2480411c61440c2041000000000000 6 8 2 (by decide +kernel)
def done44 : Closed := closeBank chartAt #[] #[hint0,hint14,hint23,hint3,hint12,hint52,hint53,hint1,hint2,hint15,hint16,hint17,hint18,hint6,hint65,hint13,hint19,hint20,hint8,hint21,hint22,hint10,hint24,hint25,hint26,hint27,hint28,hint7,hint99,hint29,hint55,hint30,hint31,hint32,hint33,hint108,hint34,hint35,hint38,hint39,hint40,hint95,hint41,hint42,hint43,hint44,hint45,hint48,hint49,hint47,hint50,hint51] [0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff000000000000,0xffff0000ffff0000,0xffffffff00000000] 0xc30cf3c30cb2c30c71c2f00000000000000000000000000000000000000000000000000000000000000000000000000000000000020322e00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000022d8ac21534d22b6ea21234d208a6920834d0000000000000000000000000000000000000000000000002289e62151c72089642121c72088e32081c722286020d1c70000000000000000000000000000000000002135df2150820d079d0d208220371c20808221b69920d0822185d62070820000000000000000000000002152942130410d21510d004120f38e20804120d20c20804120b2892070410c61440c2041000000000000 6 8 2 (by decide +kernel)
def done45 : Closed := closeBank chartAt #[] #[hint0,hint14,hint23,hint3,hint12,hint52,hint53,hint67,hint1,hint2,hint15,hint16,hint17,hint5,hint18,hint6,hint91,hint36,hint93,hint46,hint13,hint24,hint25,hint26,hint27,hint28,hint7,hint55,hint31,hint32,hint33,hint35,hint39,hint120,hint128,hint45,hint48,hint49,hint47,hint50,hint51,hint133] [0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000,0xffffffffffff0000] 0xa69965a289e79659a696400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000024326300000000000000000000000000000000000000000000000000000000000034d69a2493cf26279e2533cf36169a2513cf00000000000000000000000000000000000000000000000034d7df2492082528202532083517df24920825e75c24f20800000000000000000000000000000000000034d6db3430823535962520820d06db0d108235a65824f08235759524808200000000000000000000000034d1453540413532cb2520411d11450d004134f34e24d04134c2ca2480411c61440c2041000000000000 6 8 2 (by decide +kernel)
def done46 : Closed := closeBank chartAt #[done0,done3,done4,done6,done7,done8,done9,done10,done11,done13,done14,done16,done17,done18,done20,done21,done24,done27,done28,done29,done31,done32,done33,done34,done35,done36,done39,done40,done42,done43,done44,done45] #[hint0,hint14,hint23,hint71,hint12,hint52,hint53,hint72,hint1,hint134,hint15,hint16,hint17,hint135,hint136,hint137,hint18,hint138,hint6,hint139,hint19,hint140,hint20,hint8,hint141,hint21,hint142,hint22,hint10,hint143,hint144,hint24,hint25,hint26,hint145,hint146,hint27,hint28,hint7,hint147,hint148,hint29,hint55,hint149,hint150,hint30,hint151,hint152,hint31,hint32,hint33,hint153,hint154,hint34,hint35,hint36,hint155,hint156,hint38,hint39,hint40,hint157,hint158,hint41,hint42,hint159,hint160,hint43,hint44,hint161,hint162,hint45,hint46,hint163,hint48,hint49,hint47,hint50,hint51] [0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000] 0x972e74e9b365cb99325ca0000000000000000000000000000000000000000000000000000000000000000000000000000000000009321bc78c70b9700000000000000000000000000000000000000000000000000000000000000000000008b119438470912830133f7c5c912000000000000000000000000000000000000000000000000000000007af1dba727040870ddb35685c40866c98b05e484080000000000000000000000000000000000000000005c6502d58701025651529505c1024e992a44648102448501f3c2010200000000000000000000000000003a7059b3464081305c2962a5008126488901e380811a3058a12200810e18284060808100000000000000 7 9 2 (by decide +kernel)
def done47 : Closed := closeBank chartAt #[] #[hint0,hint164,hint165,hint2,hint166,hint167,hint168,hint169,hint170,hint171,hint172,hint173,hint174,hint175,hint176,hint177,hint178,hint3,hint179,hint180,hint181,hint182] [0xffffffff,0xffff0000ffff,0xaa00aa00aa00aa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0] 0x1d5351b56b00000000000000000000000000000000000000001d0f41b5088ca128ad080000000000000000000000000000001b44d1cc848adeb8c8848a0888c1ef000000000000000000001b5cd1b0a51ad4a1a4a51a0a819cc6190a4188210000000000 5 6 0 (by decide +kernel)
def done48 : Closed := closeBank chartAt #[done47] #[hint0,hint183,hint184,hint3,hint185,hint186,hint187,hint188,hint189,hint2,hint190,hint191,hint192,hint193,hint194,hint195,hint196,hint197,hint198,hint199,hint200,hint201,hint202,hint203,hint204,hint205,hint206,hint166,hint167,hint170,hint71] [0xffff0000ffff,0xaa00aa00aa00aa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xffffffff00000000] 0x13ee739ce779b000000000000000000000000000000000000000000000000004e9594b70d00000000000000000000000000000000000000004ded54b4ed4ce934a8ea0000000000000000000000000000004b6514c0844a9ea4b8841984619c84000000000000000000004b56d4b0a54a96a4a0a519c27198a5190a4188210000000000 5 6 1 (by decide +kernel)
def done49 : Closed := closeBank chartAt #[done47] #[hint0,hint207,hint208,hint2,hint185,hint50,hint106,hint209,hint210,hint211,hint212,hint213,hint214,hint186,hint215,hint3,hint216,hint217,hint218,hint183,hint219,hint220,hint221,hint222,hint223,hint224,hint166,hint170,hint71] [0xffffffff,0xaa00aa00aa00aa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xffff0000ffff0000] 0x1fcd6b5ad6f5a000000000000000000000000000000000000000000000000001b1591b70d00000000000000000000000000000000000000007cd177b5cd1c4f61a9080000000000000000000000000000007b6b47cc841a8521c4847a2087b884000000000000000000001b4ad1b16b1a8ca1a4a51a0a819cc6190a4188210000000000 5 6 1 (by decide +kernel)
def done50 : Closed := closeBank chartAt #[done48,done49] #[hint0,hint14,hint23,hint3,hint52,hint55,hint1,hint2,hint119,hint16,hint62,hint225,hint20,hint8,hint226,hint22,hint10,hint24,hint25,hint26,hint227,hint228,hint229,hint35,hint36,hint230,hint39,hint231,hint45,hint46,hint48,hint50,hint106,hint71,hint72] [0xaa00aa00aa00aa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xffff0000ffff0000,0xffffffff00000000] 0x1e20e17df8207de0000000000000000000000000000000000000000000000000000000000001dd61c1d034d0000000000000000000000000000000000000000000000001db6991d01861d85d61cd1860000000000000000000000000000000000001ce4951d00820cb1540cd0821d34911c60820000000000000000000000001d024f1ce0410cd10c0cb0411ca2481c60410c51040c2041000000000000 6 6 2 (by decide +kernel)
def done51 : Closed := closeBank chartAt #[done47] #[hint0,hint164,hint165,hint2,hint166,hint167,hint232,hint233,hint234,hint168,hint169,hint170,hint171,hint172,hint173,hint174,hint175,hint176,hint235,hint236,hint177,hint178,hint3,hint179,hint180,hint71,hint13,hint237,hint238,hint182] [0xffffffff,0xffff0000ffff,0x55ff55ff55ff55ff,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0] 0x1f59d1c1ce000000000000000000000000000000000000000000000000001f15c1c16bb6ebbb396b00000000000000000000000000000000000000001c0f01f1081ba6e1ed080000018f590000000000000000000000000000001c0501e084b3a8eb5c84b2c8bb56941a0881ce52000000000000000000001c2301bca51b9ad1b0a51acab1a9291a0a819cc6190a4188210000000000 5 7 0 (by decide +kernel)
def done52 : Closed := closeBank chartAt #[done48,done51] #[hint0,hint239,hint240,hint2,hint241,hint186,hint183,hint184,hint3,hint185,hint187,hint188,hint189,hint190,hint191,hint192,hint193,hint71,hint13,hint242,hint243,hint244,hint245,hint194,hint195,hint196,hint197,hint198,hint199,hint200,hint201,hint202,hint203,hint204,hint205,hint206,hint166,hint167,hint234,hint170,hint72] [0xffff0000ffff,0x55ff55ff55ff55ff,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xffffffff00000000] 0xe89659659679669640000000000000000000000000000000000000000000000000000000000000000000000000e33620d08500000000000000000000000000000000000000000000000000000000000000e07de0d02d00dc75c0cd2cd0000000000000000000000000000000000000000000000000d06da0d92490cd60d0d72492131d320b2490000000000000000000000000000000000000d05500d61040cd54d0d41040cb08b0d31040000000c34910000000000000000000000000d03900cf1450cd38d0cc14520b18b20a1452091492071860c41440c2041000000000000 6 7 1 (by decide +kernel)
def done53 : Closed := closeBank chartAt #[done49,done51] #[hint0,hint246,hint247,hint2,hint241,hint50,hint207,hint208,hint185,hint106,hint209,hint210,hint211,hint212,hint213,hint214,hint186,hint71,hint13,hint248,hint249,hint250,hint251,hint215,hint3,hint216,hint217,hint218,hint183,hint219,hint220,hint221,hint222,hint223,hint224,hint166,hint234,hint170,hint72] [0xffffffff,0x55ff55ff55ff55ff,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xffff0000ffff0000] 0x6268e38e38e58e48e30000000000000000000000000000000000000000000000000000000000000000000000000cf3620d085000000000000000000000000000000000000000000000000000000000000061c2e06105d00da29f0cd2cb00000000000000000000000000000000000000000000000061079d61c2080cd1db0da20860b64b6172080000000000000000000000000000000000000d05100d61040cd08d0d51040cb50b0d31040000000c34910000000000000000000000000d01500cf38e0cd24d0cc1450cb14b0ca2490c81480c71860c41440c2041000000000000 6 7 1 (by decide +kernel)
def done54 : Closed := closeBank chartAt #[done50,done52,done53] #[hint0,hint71,hint13,hint2,hint6,hint53,hint23,hint7,hint17,hint1,hint33,hint9,hint8,hint79,hint10,hint14,hint3,hint52,hint16,hint41,hint20,hint43,hint22,hint24,hint25,hint26,hint76,hint55,hint77,hint57,hint35,hint36,hint58,hint39,hint59,hint45,hint46,hint49,hint50,hint48,hint106,hint72,hint134] [0x55ff55ff55ff55ff,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xffff0000ffff0000,0xffffffff00000000] 0xea4299a6a289a79a50000000000000000000000000000000000000000000000000000000000000000000000000e47e30ce30c0000000000000000000000000000000000000000000000000000000000000e28600ce2490df79d0cc2490000000000000000000000000000000000000000000000000d561c0ce1864136da40c1860d96170c91860000000000000000000000000000000000000ce4960d53cf40c4544133cf0c84880c93cf4054454063cf0000000000000000000000000ce28e0cd1040cc1cc0cb1040c92890c81040c61c60c51040000000c3081000000000000 6 7 2 (by decide +kernel)
def done55 : Closed := closeBank chartAt #[] #[hint0,hint23,hint1,hint2,hint24,hint25,hint26,hint14,hint55,hint3,hint52,hint8,hint227,hint225,hint10,hint228,hint226,hint62,hint16,hint229,hint35,hint36,hint230,hint39,hint231,hint45,hint46,hint252,hint48,hint50,hint253] [0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff55ff55ff55ff55,0xffff0000ffff0000,0xffffffff00000000] 0x39cf7bbde737b000000000000000000000000000000000000000000000000001eab91b96b00000000000000000000000000000000000000001c2501b8e74b54d4ace70000000000000000000000000000001e2f61b8421d6931ac421c84219e27000000000000000000001c0af1b8214b50c4ac214a82149d07198a4188210000000000 5 6 2 (by decide +kernel)
def done56 : Closed := closeBank chartAt #[done55] #[hint0,hint71,hint2,hint13,hint14,hint53,hint3,hint23,hint52,hint17,hint1,hint16,hint8,hint41,hint10,hint43,hint6,hint54,hint7,hint56,hint33,hint9,hint78,hint79,hint24,hint25,hint26,hint76,hint55,hint77,hint57,hint35,hint36,hint58,hint39,hint59,hint45,hint46,hint49,hint48,hint252,hint253] [0x5555555555555555,0xaa00aa00aa00aa00,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xffff0000ffff0000,0xffffffff00000000] 0x9e7a699e7a289e79a60000000000000000000000000000000000000000000000000000000000000000000000000a582408e30c0000000000000000000000000000000000000000000000000000000000000a38a108e28a0a07de08c28a00000000000000000000000000000000000000000000000008f65d08e1c718d71b18c1c709a65808a1c700000000000000000000000000000000000009751608e41009549208c41008951308a40a08549108740700000000000000000000000008f2cf08e10418d20d18c10408a2ca089104187207185104083081000000000000000000 6 7 2 (by decide +kernel)
def done57 : Closed := closeBank chartAt #[] #[hint0,hint23,hint7,hint2,hint6,hint53,hint52,hint3,hint14,hint26,hint1,hint25,hint41,hint8,hint55,hint43,hint10,hint56,hint33,hint17,hint9,hint78,hint79,hint16,hint20,hint22,hint57,hint35,hint36,hint58,hint39,hint59,hint45,hint46,hint49,hint47,hint106,hint252,hint254] [0x3333333333333333,0xaa00aa00aa00aa00,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0,0xffff0000ffff0000,0xffffffff00000000] 0x9a68e39a68e59248e20000000000000000000000000000000000000000000000000000000000000000000000000e17200d034d0000000000000000000000000000000000000000000000000000000000000df79d0d028a0dc6da0cd28a0000000000000000000000000000000000000000000000000d05d90cf2081cd1981cc2080d35d30ca2080000000000000000000000000000000000000d64950d01040d40820cd1040d34910ca10a0000000000000000000000000000000000000d02d00cf0411cd38d1cc0410ca2ca0c90411c81481c60410c41440c2041000000000000 6 7 2 (by decide +kernel)
def done58 : Closed := closeBank chartAt #[] #[hint0,hint1,hint33,hint2,hint6,hint17,hint16,hint14,hint25,hint23,hint26,hint36,hint8,hint35,hint59,hint10,hint39,hint54,hint7,hint53,hint9,hint78,hint79,hint3,hint52,hint41,hint20,hint43,hint22,hint76,hint55,hint77,hint45,hint46,hint49,hint50,hint48,hint254,hint104,hint51] [0xf0f0f0f0f0f0f0f,0xaa00aa00aa00aa00,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xffff0000ffff0000,0xffffffff00000000] 0x8a29e79a58a48e38a20000000000000000000000000000000000000000000000000000000000000000000000000e12e00cf30c0000000000000000000000000000000000000000000000000000000000000db21f0cf2495d979d5cc2490000000000000000000000000000000000000000000000000cf19c0db1c75cc61a5d91c75d36135c91c70000000000000000000000000000000000000d60950cf1040d44920cc1040d34910c91090000000000000000000000000000000000000cf40f0ce0410cc34c0cb0410c92890c80410c71470c60410c41440c2041000000000000 6 7 2 (by decide +kernel)
def done59 : Closed := closeBank chartAt #[done51] #[hint0,hint133,hint255,hint2,hint49,hint51,hint256,hint247,hint241,hint196,hint208,hint185,hint47,hint257,hint258,hint259,hint260,hint261,hint262,hint183,hint263,hint3,hint264,hint265,hint254,hint266,hint267,hint268,hint269,hint234,hint71,hint170] [0xffffffff,0xffff0000ffff,0xaa00aa00aa00aa00,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0] 0xef7bdefc7eef7bd0000000000000000000000000000000000000000000000000000000000001ddbc1c1ce000000000000000000000000000000000000000000000000001c1501e96baba8eae16b00000000000000000000000000000000000000001c0fb1e9081ba591e10800000000000000000000000000000000000000001c0501dc84ab88eada31aac8bad2731a0881ca31000000000000000000001c1901bca51b8ae1b58c1acab1a9291a0a819cc6190a4188210000000000 5 7 1 (by decide +kernel)
def done60 : Closed := closeBank chartAt #[done52,done59] #[hint0,hint8,hint7,hint2,hint6,hint9,hint41,hint52,hint3,hint14,hint55,hint23,hint35,hint1,hint36,hint46,hint10,hint54,hint53,hint56,hint33,hint17,hint78,hint79,hint16,hint43,hint22,hint24,hint25,hint26,hint77,hint58,hint39,hint59,hint49,hint51,hint71,hint253,hint47,hint72] [0xffff0000ffff,0xaa00aa00aa00aa00,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xffffffff00000000] 0xe78e39a68e50e48e20000000000000000000000000000000000000000000000000000000000000000000000000e181f0d034d0000000000000000000000000000000000000000000000000000000000000d971e0d02cb0dd71b0cd2cb0000000000000000000000000000000000000000000000000d061a0d92490d56150cd2492121d220b2490000000000000000000000000000000000000d75160d01040d55130cd10d0d20910cb10b0000000000000000000000000000000000000d03900cf0410cd38d0cc04120b18b20a0412090492071860c41440c2041000000000000 6 7 2 (by decide +kernel)
def done61 : Closed := closeBank chartAt #[done53,done59] #[hint0,hint10,hint33,hint2,hint6,hint79,hint43,hint16,hint14,hint25,hint23,hint39,hint1,hint59,hint36,hint8,hint46,hint54,hint7,hint53,hint56,hint17,hint9,hint3,hint52,hint41,hint20,hint24,hint26,hint76,hint55,hint57,hint35,hint49,hint71,hint48,hint254,hint104,hint72] [0xffffffff,0xaa00aa00aa00aa00,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xffff0000ffff0000] 0x5e68619648630e28610000000000000000000000000000000000000000000000000000000000000000000000000ce81f0cf30c0000000000000000000000000000000000000000000000000000000000005d979d5cf28a0dc25b0cc28a0000000000000000000000000000000000000000000000005cf61a5d92080d51d50cc2085d36135ca2080000000000000000000000000000000000000d64920cf1040d50940cc10c0d34910ca10a0000000000000000000000000000000000000cf40f0ce0410cc34c0cb0410ca18a0c90410c80480c71860c41440c2041000000000000 6 7 2 (by decide +kernel)
def done62 : Closed := closeBank chartAt #[done54,done56,done57,done58,done60,done61] #[hint0,hint23,hint6,hint2,hint54,hint7,hint53,hint1,hint56,hint33,hint17,hint8,hint9,hint10,hint78,hint79,hint14,hint3,hint52,hint16,hint41,hint20,hint43,hint22,hint24,hint25,hint26,hint76,hint55,hint77,hint57,hint35,hint36,hint58,hint39,hint59,hint45,hint46,hint71,hint72,hint13,hint134,hint135,hint136,hint137] [0xaa00aa00aa00aa00,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xffff0000ffff0000,0xffffffff00000000] 0xec46b0ea469a270e60000000000000000000000000000000000000000000000000000000000000000000000000e58240cd2cb0000000000000000000000000000000000000000000000000000000000000e38a10cd1c70e07de0cb1c70000000000000000000000000000000000000000000000000d665d0cd04145471b44b0410da6580c70410000000000000000000000000000000000000cd4d70d641044b4954544100ca4ca0c74104464864414100000000000000000000000000cf24e0cd0820cc1450cb0820ca2480c70870c61440c1081000000000000000000000000 6 7 3 (by decide +kernel)
def done63 : Closed := closeBank chartAt #[] #[hint0,hint23,hint26,hint2,hint1,hint25,hint83,hint18,hint12,hint52,hint3,hint14,hint19,hint8,hint55,hint21,hint10,hint84,hint15,hint85,hint16,hint34,hint35,hint36,hint38,hint39,hint40,hint86,hint78,hint87,hint20,hint22,hint45,hint46,hint89,hint88,hint270,hint106,hint252] [0x3333333333333333,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffaaffaaffaaffaa,0xffff0000ffff0000,0xffffffff00000000] 0x9248e38e69659248e20000000000000000000000000000000000000000000000000000000000000000000000000e15e00d034d0000000000000000000000000000000000000000000000000000000000000d051f0cf2cb28d25e28c2cb0000000000000000000000000000000000000000000000000dd4dc0d01c70db1860cd1c70000000000000000000000000000000000000000000000000da6580d01040d75950cd1040d44920cb10b0d34910c71040000000000000000000000000d01500cf04128d38d28c04128b20b2890410c72070c60410c41440c2041000000000000 6 7 2 (by decide +kernel)
def done64 : Closed := closeBank chartAt #[] #[hint0,hint1,hint25,hint2,hint23,hint26,hint85,hint18,hint15,hint16,hint14,hint36,hint8,hint35,hint40,hint10,hint39,hint82,hint12,hint83,hint3,hint52,hint29,hint55,hint19,hint30,hint21,hint86,hint78,hint87,hint20,hint22,hint45,hint46,hint89,hint270,hint271,hint50,hint48,hint90] [0xf0f0f0f0f0f0f0f,0xcccccccccccccccc,0xff00ff00ff00ff00,0xffaaffaaffaaffaa,0xffff0000ffff0000,0xffffffff00000000] 0x8a29e78a69659238a20000000000000000000000000000000000000000000000000000000000000000000000000e12e00cf30c0000000000000000000000000000000000000000000000000000000000000cf25f0da28a50c55e51828a0000000000000000000000000000000000000000000000000dd19c0cf1c70db4d30cc1c70000000000000000000000000000000000000000000000000da0990cf1045185d650c10451549250a10a0d34910c71040000000000000000000000000cf40f0ce0410cc34c0cb0410ca20a0c90410c72070c60410c41440c2041000000000000 6 7 2 (by decide +kernel)
def done65 : Closed := closeBank chartAt #[done47] #[hint0,hint164,hint165,hint2,hint166,hint167,hint272,hint273,hint274,hint171,hint172,hint173,hint174,hint175,hint176,hint168,hint169,hint170,hint275,hint276,hint179,hint3,hint177,hint180,hint178,hint277,hint278,hint71,hint13,hint182] [0xffffffff,0xffff0000ffff,0xff00ff00ff00ff,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xffaaffaaffaaffaa] 0x1c35a1c5b100000000000000000000000000000000000000000000000000ae339ac5711f53d1b56b00000000000000000000000000000000000000000000018f9b1b4ed1e9081ae6b1e508000000000000000000000000000000ac491ae2d61b44d1dc84aaecbad0841a0881ce52000000000000000000001c4b11c1ef1b5cd1b0a51ad4a1a4a51a0a819cc6190a4188210000000000 5 7 0 (by decide +kernel)
def done66 : Closed := closeBank chartAt #[done48,done65] #[hint0,hint279,hint280,hint2,hint281,hint186,hint187,hint3,hint188,hint183,hint189,hint190,hint191,hint184,hint185,hint192,hint193,hint282,hint283,hint284,hint71,hint13,hint285,hint199,hint200,hint201,hint202,hint203,hint194,hint195,hint204,hint205,hint206,hint196,hint197,hint198,hint166,hint167,hint274,hint170,hint72] [0xffff0000ffff,0xff00ff00ff00ff,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xffaaffaaffaaffaa,0xffffffff00000000] 0xe89679659659669640000000000000000000000000000000000000000000000000000000000000000000000000d08e20e138e0000000000000000000000000000000000000000000000000000000000000e02df0d07900dd2cb0ce70e0000000000000000000000000000000000000000000000000db6990d02101cd4511ce20e0d76170cb20b0000000000000000000000000000000000000d04d00d61040000000c35540cb4cb0d21040c80880d11040000000000000000000000000d03100cf1451ce14e1cd2490cb30b0ca1451c82481c61450c41440c2041000000000000 6 7 1 (by decide +kernel)
def done67 : Closed := closeBank chartAt #[done49,done65] #[hint0,hint130,hint286,hint2,hint281,hint50,hint106,hint209,hint210,hint211,hint212,hint207,hint208,hint185,hint213,hint214,hint186,hint287,hint288,hint289,hint71,hint13,hint290,hint221,hint217,hint215,hint3,hint216,hint222,hint183,hint218,hint223,hint224,hint219,hint220,hint166,hint274,hint170,hint72] [0xffffffff,0xff00ff00ff00ff,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xffaaffaaffaaffaa,0xffff0000ffff0000] 0x6a68e58e38e38e48e30000000000000000000000000000000000000000000000000000000000000000000000006908a169d34d0000000000000000000000000000000000000000000000000000000000000cf2a00d07d00cc29e0cd60d00000000000000000000000000000000000000000000000069d21c69065069b20868d64d0d81d70ca2080000000000000000000000000000000000000d04900d61040000000c35540ca08a0d31040c84880d11040000000000000000000000000d01500cf38e0cd14d0cc2cb0ca18a0c91450c81480c71860c41440c2041000000000000 6 7 1 (by decide +kernel)
def done68 : Closed := closeBank chartAt #[done50,done66,done67] #[hint0,hint18,hint12,hint2,hint23,hint83,hint15,hint1,hint85,hint71,hint13,hint86,hint8,hint87,hint10,hint24,hint25,hint26,hint14,hint3,hint52,hint29,hint55,hint19,hint30,hint21,hint16,hint34,hint35,hint36,hint38,hint39,hint40,hint20,hint22,hint45,hint46,hint89,hint50,hint106,hint48,hint72,hint134] [0xff00ff00ff00ff,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xffaaffaaffaaffaa,0xffff0000ffff0000,0xffffffff00000000] 0xea4e99a89a69e79a50000000000000000000000000000000000000000000000000000000000000000000000000e47630ce30c0000000000000000000000000000000000000000000000000000000000000ce6a20d94924cc5214d74920000000000000000000000000000000000000000000000000e07de0ce1c70dd71b0cc1c70da1860d21d20000000000000000000000000000000000000d94180ce1044d75954cc1044d40824d21120d140f0c71040000000000000000000000000ce20e0cd0410cc14c0cb0410000000c32890c72070c60410c41440c2041000000000000 6 7 2 (by decide +kernel)
def done69 : Closed := closeBank chartAt #[done55] #[hint0,hint14,hint12,hint3,hint23,hint52,hint15,hint2,hint1,hint16,hint71,hint13,hint8,hint19,hint10,hint21,hint24,hint25,hint26,hint18,hint82,hint83,hint29,hint55,hint30,hint84,hint85,hint34,hint35,hint36,hint38,hint39,hint40,hint86,hint78,hint87,hint45,hint46,hint89,hint252,hint48,hint253] [0x55005500550055,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000] 0xa28a69a28a289e79a60000000000000000000000000000000000000000000000000000000000000000000000001e57641ce30c0000000000000000000000000000000000000000000000000000000000001e36a21ce4d31e15551cc4d30000000000000000000000000000000000000000000000001e07de1ce2081dd71b1cc2081da1991d32080000000000000000000000000000000000001cf4581ce1040cd5d60cc1041d50941d31041d24501c81040000000000000000000000001cf24f1ce0410cd14d0cc0411cb1ca0000001c82481c60410c41440c2041000000000000 6 7 2 (by decide +kernel)
def done70 : Closed := closeBank chartAt #[done65] #[hint0,hint291,hint292,hint2,hint89,hint90,hint88,hint293,hint294,hint295,hint296,hint297,hint286,hint281,hint196,hint208,hint185,hint298,hint299,hint3,hint300,hint301,hint183,hint263,hint302,hint270,hint303,hint304,hint305,hint274,hint71,hint170] [0xffffffff,0xffff0000ffff,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffaaffaaffaaffaa] 0xefc7eef7bdef7bd0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001bd4a1c3701b15c1b76d00000000000000000000000000000000000000009dd089c3301d51a1b72d1d0f81a9080000000000000000000000000000009c0909ded61b48d1d6311a84a1d0849a0889ca31000000000000000000001c0b01bdce1b4ad1b16b1a8ca1a4a51a0a819cc6190a4188210000000000 5 7 1 (by decide +kernel)
def done71 : Closed := closeBank chartAt #[done66,done70] #[hint0,hint8,hint55,hint3,hint23,hint19,hint35,hint2,hint1,hint36,hint83,hint18,hint86,hint52,hint14,hint46,hint10,hint24,hint25,hint26,hint82,hint12,hint30,hint21,hint84,hint15,hint85,hint16,hint38,hint39,hint40,hint78,hint87,hint22,hint89,hint90,hint88,hint71,hint253,hint72] [0xffff0000ffff,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffaaffaaffaaffaa,0xffffffff00000000] 0x1e78e61e58e39248e20000000000000000000000000000000000000000000000000000000000000000000000001d06e11d738e0000000000000000000000000000000000000000000000000000000000001e069f1d02cb0000000000000000000000000000000000000000000000000000000000001de75c1d02081db6591ce20e1da6581cb2080000000000000000000000000000000000001d74961d01040cd5550ce10e1ca5541cb1041d34911c81040000000000000000000000001d02501cf0410ce04e0cd1451cb30b1ca0411c82481c60410c41440c2041000000000000 6 7 2 (by decide +kernel)
def done72 : Closed := closeBank chartAt #[done67,done70] #[hint0,hint10,hint25,hint2,hint23,hint21,hint39,hint1,hint40,hint85,hint18,hint87,hint16,hint14,hint36,hint8,hint46,hint24,hint26,hint82,hint12,hint83,hint3,hint52,hint29,hint55,hint19,hint84,hint15,hint34,hint35,hint86,hint20,hint89,hint270,hint271,hint71,hint48,hint72] [0xffffffff,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffaaffaaffaaffaa,0xffff0000ffff0000] 0x5a68650e48618e286100000000000000000000000000000000000000000000000000000000000000000000000058f5e059a34d0000000000000000000000000000000000000000000000000000000000000df5550cf28a0000000000000000000000000000000000000000000000000000000000000ce79d0cf1c70cc71c0cd1cd0c971b0ca1c700000000000000000000000000000000000059a65858f10459751458d10d0d55130ca1040d20910c71040000000000000000000000000cf40f0ce0410cd04d0cc1450ca2ca0c90410c72070c60410c41440c2041000000000000 6 7 2 (by decide +kernel)
def done73 : Closed := closeBank chartAt #[done63,done64,done68,done69,done71,done72] #[hint0,hint23,hint1,hint2,hint24,hint25,hint26,hint18,hint82,hint12,hint83,hint14,hint3,hint52,hint8,hint29,hint55,hint19,hint10,hint30,hint21,hint84,hint15,hint85,hint16,hint34,hint35,hint36,hint38,hint39,hint40,hint86,hint78,hint87,hint20,hint22,hint45,hint46,hint71,hint72,hint134,hint135,hint13,hint136,hint137] [0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffaaffaaffaaffaa,0xffff0000ffff0000,0xffffffff00000000] 0xec32baa90e80e73260000000000000000000000000000000000000000000000000000000000000000000000000e56e40d238e0000000000000000000000000000000000000000000000000000000000000d26230d42cb30e3623112cb0000000000000000000000000000000000000000000000000e15e00d21c70df28a0ce1c70000000000000000000000000000000000000000000000000de75c0d20820db6990ce0820d85960cb08b0d75950c70820000000000000000000000000d41530d204131140f30e04130d24930b04b0ca2480c70410c61440c2041000000000000 6 7 3 (by decide +kernel)
def done74 : Closed := closeBank chartAt #[] #[hint0,hint23,hint1,hint2,hint24,hint25,hint26,hint5,hint14,hint55,hint3,hint52,hint67,hint8,hint227,hint225,hint10,hint228,hint226,hint62,hint16,hint229,hint35,hint36,hint230,hint39,hint231,hint45,hint46,hint252,hint48,hint50,hint253] [0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff55ff55ff55ff55,0xffff0000ffff0000,0xffffffff00000000] 0x79e8207df79e75d0000000000000000000000000000000000000000000000000000000000001dc5db0d034d0000000000000000000000000000000000000000000000001d25120d020830f2cf28d2080000000000000000000000000000000000000da6580d00821d75950cd0821d40820c84c80000000000000000000000001d21510d004128f24e28d04130b0412882481c61440c2041000000000000 6 7 2 (by decide +kernel)
def done75 : Closed := closeBank chartAt #[] #[hint0,hint23,hint1,hint2,hint24,hint25,hint26,hint27,hint12,hint3,hint14,hint55,hint52,hint8,hint29,hint19,hint10,hint30,hint21,hint31,hint15,hint62,hint16,hint34,hint35,hint36,hint38,hint39,hint40,hint225,hint86,hint226,hint87,hint45,hint46,hint252,hint48,hint50,hint253] [0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xff55ff55ff55ff55,0xffff0000ffff0000,0xffffffff00000000] 0x9249a69659249248e30000000000000000000000000000000000000000000000000000000000000000000000000e26610d034d0000000000000000000000000000000000000000000000000000000000000d25920d028a24f30f24d28a0000000000000000000000000000000000000000000000000e00df0d00d00de25d0cd0cd0000000000000000000000000000000000000000000000000dc6da0d00820d96170cd0820d60820ca54a0c35130c30820000000000000000000000000d21510d004124f2ce24d04124c04124a2ca0c92070c30410c61440c2041000000000000 6 7 2 (by decide +kernel)
def done76 : Closed := closeBank chartAt #[] #[hint0,hint53,hint3,hint23,hint67,hint17,hint2,hint1,hint5,hint8,hint41,hint10,hint43,hint24,hint25,hint26,hint54,hint55,hint6,hint7,hint76,hint77,hint56,hint62,hint33,hint57,hint35,hint36,hint58,hint39,hint59,hint45,hint46,hint49,hint252,hint48,hint50,hint253] [0x5555555555555555,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff55ff55ff55ff55,0xffff0000ffff0000,0xffffffff00000000] 0x8e39659248e38a28610000000000000000000000000000000000000000000000000000000000000000000000002206df18b24900000000000000000000000000000000000000000000000000000000000020c60c18b49210a4ca08949200000000000000000000000000000000000000000000000019e75c18b1c721b6991891c72181c71925d600000000000000000000000000000000000020c39518b0c308a4540890c31130c309245020f38d1870c300000000000000000000000020c20c18b18b10a10a089089000000000000207207185185103103081081000000000000 6 7 2 (by decide +kernel)
def done77 : Closed := closeBank chartAt #[done74,done75,done76] #[hint0,hint14,hint53,hint3,hint23,hint52,hint67,hint17,hint2,hint1,hint16,hint5,hint6,hint71,hint72,hint134,hint13,hint8,hint19,hint10,hint21,hint24,hint25,hint26,hint27,hint28,hint7,hint29,hint55,hint30,hint31,hint32,hint33,hint34,hint35,hint36,hint38,hint39,hint40,hint41,hint42,hint43,hint44,hint45,hint46,hint49,hint252,hint48,hint253] [0x5555555555555555,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000] 0xbefc30befbefbaeb6d0000000000000000000000000000000000000000000000000000000000000000000000002ec8eb21345100000000000000000000000000000000000000000000000000000000000022a82921330c0e86a721130c0000000000000000000000000000000000000000000000002269642132492e38a12112492207de20c2490000000000000000000000000000000000002d459d2131040d271b0d11040da65820c1042d75952091040000000000000000000000002d42942130411921520d104140f38d20c0412c92892070411841440c2041000000000000 6 8 2 (by decide +kernel)
def done78 : Closed := closeBank chartAt #[] #[hint0,hint23,hint3,hint306,hint67,hint53,hint1,hint2,hint307,hint5,hint17,hint14,hint225,hint41,hint8,hint226,hint43,hint10,hint24,hint25,hint26,hint54,hint55,hint6,hint7,hint76,hint77,hint56,hint62,hint33,hint57,hint35,hint36,hint58,hint39,hint59,hint45,hint46,hint48,hint49,hint47,hint50,hint51] [0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff55ff55ff55ff55,0xffff0000ffff0000,0xffffffff00000000] 0x9e7aaaa699e7a289e60000000000000000000000000000000000000000000000000000000000000000000000002658241d138e0000000000000000000000000000000000000000000000000000000000002507501d15d710d60d08e5d70000000000000000000000000000000000000000000000001e38a11d11862607de1ce18625d1861d771b0000000000000000000000000000000000002504da1d104108d59908e0411180410975952544d21c60410000000000000000000000002512511d01cf10e10e08d08c0000001c71cb24a2481c61c6105103081081000000000000 6 7 2 (by decide +kernel)
def done79 : Closed := closeBank chartAt #[done56,done78] #[hint0,hint53,hint3,hint23,hint67,hint17,hint2,hint1,hint5,hint6,hint72,hint13,hint8,hint19,hint10,hint21,hint71,hint24,hint25,hint26,hint27,hint28,hint7,hint29,hint55,hint30,hint31,hint32,hint33,hint34,hint35,hint36,hint38,hint39,hint40,hint41,hint42,hint43,hint44,hint45,hint46,hint47,hint49,hint50,hint51] [0x5555555555555555,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000] 0xaaab2caebaaaa690000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002287e718e30c0000000000000000000000000000000000000000000000000000000000000000000000001a672518e2490a45a318c2490000000000000000000000000000000000000000000000000000000000001a286018e1c721f79d18c1c719c6da1891c700000000000000000000000000000000000000000000000020f49918e0c308d61708c0c30965541890c32134911870c300000000000000000000000000000000000020e20e18f18f10c10c08d08d2c92c918b19020520518718710110108308300000000000000000000000020f20f18e18e10d10d08c08c2cb2ca189189207207185185103103081081000000000000000000000000 6 8 2 (by decide +kernel)
def done80 : Closed := closeBank chartAt #[done57,done63] #[hint0,hint23,hint52,hint67,hint14,hint53,hint3,hint26,hint2,hint1,hint25,hint5,hint7,hint6,hint28,hint19,hint8,hint55,hint21,hint10,hint15,hint16,hint17,hint71,hint18,hint72,hint13,hint20,hint22,hint31,hint32,hint33,hint34,hint35,hint36,hint38,hint39,hint40,hint41,hint42,hint43,hint44,hint45,hint46,hint49,hint47,hint252,hint254,hint106] [0x3333333333333333,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000] 0xbefb6dc30befb6eb6c0000000000000000000000000000000000000000000000000000000000000000000000002eb8aa2134100000000000000000000000000000000000000000000000000000000000002297e821334d1a732621034d0000000000000000000000000000000000000000000000002259232132492e286021024921f79d20d2490000000000000000000000000000000000002d355c2121040d009b18f10468d6582171042d65542091040000000000000000000000002d329321204119045018f04118d38d20c0412c92892070411841440c2041000000000000 6 8 2 (by decide +kernel)
def done81 : Closed := closeBank chartAt #[] #[hint0,hint52,hint67,hint3,hint14,hint26,hint2,hint1,hint5,hint7,hint6,hint19,hint8,hint21,hint10,hint15,hint16,hint17,hint18,hint20,hint22,hint31,hint32,hint33,hint34,hint35,hint36,hint38,hint39,hint40,hint41,hint42,hint43,hint44,hint45,hint46,hint252,hint47,hint104,hint106] [0x3333333333333333,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000] 0x9a69659e79a60009640000000000000000000000000000000000000000000000000000000000000000000000000000000000000002236a218e30c0000000000000000000000000000000000000000000000000000000000000000000000001a15e018e28a0df25e18c28a00000000000000000000000000000000000000000000000000000000000019d71b18e1c721a65818c1c719759518a1c700000000000000000000000000000000000000000000000020d20d18e18e0cb0cb0cc0cc0c90c918a18a20520518718700000000000000000000000000000000000020e41418d1040cc0530cb1040ca0d218310421140f1871040c20410c310400000000000000000000000020e20e18d18d0cc0cc0cb0cb0ca0ca1891892072071851850000000000000c40c40c1081000000000000 6 8 2 (by decide +kernel)
def done82 : Closed := closeBank chartAt #[done58,done64] #[hint0,hint1,hint16,hint5,hint14,hint17,hint2,hint25,hint23,hint26,hint33,hint6,hint32,hint36,hint8,hint35,hint40,hint10,hint39,hint3,hint12,hint52,hint53,hint67,hint71,hint18,hint72,hint13,hint19,hint20,hint21,hint22,hint27,hint28,hint7,hint29,hint55,hint30,hint41,hint42,hint43,hint44,hint45,hint46,hint49,hint48,hint254,hint104,hint50,hint51] [0xf0f0f0f0f0f0f0f,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000] 0xb2cc71c30beeb2db2c0000000000000000000000000000000000000000000000000000000000000000000000000eb36a19138e0000000000000000000000000000000000000000000000000000000000001a92a81912cb4e78a618e2cb0000000000000000000000000000000000000000000000000de1e51912084dc9234ce2084e286018b2080000000000000000000000000000000000000d109f19e1045ce55d4dc1046cb6991981045d65544c810400000000000000000000000019149119004118e3ce0cd04118b30b18a0411882480c70411841440c2041000000000000 6 8 2 (by decide +kernel)
def done83 : Closed := closeBank chartAt #[] #[hint0,hint16,hint5,hint2,hint14,hint25,hint23,hint33,hint6,hint36,hint8,hint40,hint10,hint3,hint12,hint52,hint53,hint67,hint18,hint19,hint20,hint21,hint22,hint27,hint28,hint7,hint29,hint55,hint30,hint41,hint42,hint43,hint44,hint45,hint46,hint48,hint49,hint254,hint104,hint50,hint51] [0xf0f0f0f0f0f0f0f,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000] 0x924a289e70009a59230000000000000000000000000000000000000000000000000000000000000000000000000000000000000000e22610cc28a0000000000000000000000000000000000000000000000000000000000000000000000000e01df0cc2080de65d0ca2080000000000000000000000000000000000000000000000000000000000000cb0cb0cc0cc0c90890ca0ca0c70c70c80c80000000000000000000000000000000000000000000000000d515c0cc1863536da34a1860d96170c81860c21450c31860000000000000000000000000000000000000cc0560d510444a3d43531040c80d20c31040c20410c31044503ce3461040000000000000000000000000cc0cc0cb0cb0ca0ca0c90890c80c80c70c70000000000000c60c60c50850c40c40c1081000000000000 6 8 2 (by decide +kernel)
def done84 : Closed := closeBank chartAt #[] #[hint0,hint164,hint165,hint5,hint166,hint167,hint2,hint168,hint169,hint170,hint171,hint172,hint173,hint174,hint175,hint176,hint177,hint178,hint67,hint3,hint179,hint180,hint181,hint182] [0xffffffff,0xffff0000ffff,0xaa00aa00aa00aa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0] 0x1dd573398c00000000000000000000000000000000000000001d91633929952349b1290000000000000000000000000000001b84e354849b20c9d0849a4899461000000000000000000000339ee334a53316b1a8a5324a91a0e7310a4188210000000000 5 7 0 (by decide +kernel)
def done85 : Closed := closeBank chartAt #[] #[hint0,hint164,hint165,hint2,hint166,hint167,hint168,hint169,hint170,hint171,hint172,hint173,hint174,hint175,hint176,hint177,hint178,hint67,hint3,hint179,hint180,hint5,hint181,hint182] [0xffffffff,0xffff0000ffff,0xaa00aa00aa00aa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xffffffff00000000] 0x18d8c18dad000000000000000000000000000000000000000000000000001d52918d6b1dd371b56b00000000000000000000000000000000000000001d4e718d081d8f61b5088ce1392d080000000000000000000000000000001d44218c841b44d1d08492deb94c84920888c1ef0000000000000000000000000000001b5cd1b0a51ad4a1a4a51a0a819cc6190a4188210000000000 5 7 0 (by decide +kernel)
def done86 : Closed := closeBank chartAt #[done84,done85] #[hint0,hint183,hint184,hint67,hint185,hint186,hint3,hint187,hint188,hint189,hint2,hint190,hint191,hint5,hint192,hint193,hint194,hint195,hint196,hint197,hint198,hint199,hint200,hint201,hint202,hint203,hint204,hint205,hint206,hint166,hint167,hint170,hint71,hint72] [0xffff0000ffff,0xaa00aa00aa00aa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xffffffff00000000] 0x86079e79e79f79d00000000000000000000000000000000000000000000000000000000000029c2db28f68f00000000000000000000000000000000000000000000000035961728f20f35559528b20b00000000000000000000000000000000000034f51329210434b44b2901040c708718810400000000000000000000000034f30f28e14534b30b2891451880481871451841440c2041000000000000 6 7 1 (by decide +kernel)
def done87 : Closed := closeBank chartAt #[] #[hint0,hint308,hint165,hint5,hint166,hint167,hint2,hint168,hint169,hint170,hint171,hint172,hint173,hint174,hint175,hint176,hint177,hint178,hint3,hint179,hint309,hint181,hint67,hint182] [0xffffffff,0xffff0000ffff,0xaa00aa00aa00aa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xffff0000ffff0000] 0x18e94319ce0000000000000000000000000000000000000000000000000094a739498c1dd573398c000000000000000000000000000000000000000095a31949291d5153392994e339312900000000000000000000000000000000000000001b84e350849320c94c849248994610000000000000000000003182118ca5339ee334a53316b1a8a5324a91a0e7310a4188210000000000 5 7 0 (by decide +kernel)
def done88 : Closed := closeBank chartAt #[] #[hint0,hint308,hint165,hint166,hint167,hint168,hint169,hint170,hint171,hint172,hint173,hint174,hint175,hint176,hint2,hint177,hint178,hint179,hint309,hint5,hint181,hint3,hint67,hint182] [0xffffffff,0xffff0000ffff,0xaa00aa00aa00aa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xffff0000ffff0000,0xffffffff00000000] 0x4dd3039ce0000000000000000000000000000000000000000000000000000000000000396b0398c03a520398c0000000000000000000000000000000000000000000000000004d080394a056310554a05d170314a000000000000000000000000000000000000000004cc6038e705a10054e7050d4030e704611028e700000000000000000000000000000004c420386300000000000304c04863029ea0446301c67041ef0000000000000000000000000000000382103884031ac02c84029290208401c87018a500c83008210000000000 5 7 0 (by decide +kernel)
def done89 : Closed := closeBank chartAt #[done87,done88] #[hint0,hint310,hint311,hint263,hint3,hint185,hint50,hint210,hint312,hint188,hint313,hint2,hint190,hint191,hint5,hint314,hint193,hint194,hint195,hint315,hint67,hint196,hint197,hint198,hint199,hint200,hint316,hint201,hint202,hint203,hint204,hint205,hint206,hint317,hint170,hint167,hint71,hint72] [0xffff0000ffff,0xaa00aa00aa00aa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xffff0000ffff0000,0xffffffff00000000] 0x9640008e38e38e200000000000000000000000000000000000000000000000000000000000000000000000000038f3a12d02d00000000000000000000000000000000000000000000000000000000000002e031f2d079038e28a2cb30c00000000000000000000000000000000000000000000000039d71b2d025010421a1042493986582cc24c0000000000000000000000000000000000003905d62d51451140d310414538c48c2d11451080c81091450000000000000000000000003903502cf18600000000000038c34c2ca186109089108187105185103081000000000000 6 7 1 (by decide +kernel)
def done90 : Closed := closeBank chartAt #[done84,done87] #[hint0,hint207,hint208,hint5,hint185,hint50,hint2,hint106,hint209,hint210,hint211,hint212,hint213,hint214,hint186,hint215,hint3,hint216,hint67,hint217,hint218,hint183,hint219,hint220,hint221,hint222,hint223,hint224,hint166,hint170,hint71,hint72] [0xffffffff,0xaa00aa00aa00aa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xffff0000ffff0000] 0x3fee739ce779c000000000000000000000000000000000000000000000000001b57b33b4e000000000000000000000000000000000000000085539839ee1cd1832d2900000000000000000000000000000093af6854841ac5434c849262983c8400000000000000000000338ae1b58c32ceb328a5324a91a0e7310a4188210000000000 5 7 1 (by decide +kernel)
def done91 : Closed := closeBank chartAt #[done85,done88] #[hint0,hint207,hint208,hint2,hint185,hint50,hint106,hint209,hint210,hint318,hint212,hint191,hint214,hint186,hint215,hint3,hint216,hint67,hint217,hint218,hint183,hint219,hint220,hint5,hint221,hint222,hint223,hint224,hint170,hint166,hint71,hint72] [0xffffffff,0xaa00aa00aa00aa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xffff0000ffff0000,0xffffffff00000000] 0x3feef7bdef0000000000000000000000000000000000000000000000000000000000000001dd8c18dad0000000000000000000000000000000000000000000000000018d2918d4a1b15b1b74d00000000000000000000000000000000000000001dce718d087d1197b5cd1c8f81a9080000000000000000000000000000001dc4218c848b6d57d0841a8531c8848a2087b8840000000000000000000000000000001b4ad1b16b1a8ca1a4a51a0a819cc6190a4188210000000000 5 7 1 (by decide +kernel)
def done92 : Closed := closeBank chartAt #[done86,done89,done90,done91] #[hint0,hint14,hint23,hint3,hint52,hint55,hint67,hint1,hint2,hint119,hint16,hint62,hint5,hint225,hint20,hint8,hint226,hint22,hint10,hint24,hint25,hint26,hint227,hint228,hint229,hint35,hint36,hint230,hint39,hint231,hint45,hint46,hint48,hint50,hint106,hint71,hint72,hint134,hint135] [0xaa00aa00aa00aa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xffff0000ffff0000,0xffffffff00000000] 0x9a59238618a286000000000000000000000000000000000000000000000000000000000000031f69e2123cf00000000000000000000000000000000000000000000000021d71b2121c731a65820f1c70000000000000000000000000000000000003105172120820cd1560cf08231551320708200000000000000000000000031229121004118f10e0cd04130b2892070411851040c2041000000000000 6 7 2 (by decide +kernel)
def done93 : Closed := closeBank chartAt #[] #[hint0,hint164,hint165,hint5,hint166,hint167,hint2,hint168,hint233,hint234,hint171,hint172,hint173,hint174,hint175,hint176,hint177,hint236,hint67,hint3,hint179,hint180,hint181,hint319,hint320,hint182] [0xffffffff,0xffff0000ffff,0xaa00aa00aa00aa,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0] 0x1e5593398c000000000000000000000000000000000000000000000000001e078338ce95e579b26c00000000000000000000000000000000000000001d91633929952349b12900000000000000000000000000000000000000001b84e354849b20c9d0849cc8494a109a4899461000000000000000000000339ee334a53316b1a8a5318a518ce7324a91a0e7310a4188210000000000 5 7 0 (by decide +kernel)
def done94 : Closed := closeBank chartAt #[done93] #[hint0,hint183,hint240,hint67,hint241,hint186,hint3,hint187,hint188,hint189,hint2,hint190,hint191,hint5,hint192,hint193,hint194,hint244,hint196,hint321,hint199,hint200,hint201,hint202,hint203,hint204,hint205,hint206,hint166,hint167,hint234,hint71,hint37] [0xffff0000ffff,0xaa00aa00aa00aa,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xffffffff00000000] 0x81f75d75d75d75e75c00000000000000000000000000000000000000000000000000000000000000000000000029b2da28f64f0000000000000000000000000000000000000000000000000000000000003585d628f20f35455428b20b00000000000000000000000000000000000000000000000034f34f29229234b34b2902900d30d318818800000000000000000000000000000000000034f44f29210434b44b2901040c708718810400000000000000000000000000000000000034f30f28e14534b30b2891451880481871451861450c30411841440c2041000000000000 6 7 1 (by decide +kernel)
def done95 : Closed := closeBank chartAt #[done93] #[hint0,hint207,hint247,hint5,hint241,hint50,hint2,hint106,hint209,hint210,hint211,hint212,hint213,hint214,hint186,hint215,hint3,hint249,hint67,hint217,hint183,hint221,hint222,hint223,hint224,hint166,hint234,hint71,hint13] [0xffffffff,0xaa00aa00aa00aa,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xffff0000ffff0000] 0xe6f39ce739ceb390000000000000000000000000000000000000000000000000000000000001b57833aee0000000000000000000000000000000000000000000000000085136839ee1cd1532d29000000000000000000000000000000000000000093a4e852141ac6b34cd39264983e0f00000000000000000000000000000093a2e850841ac4b34c849262983c84000000000000000000000000000000338ae1b58c32ceb328a5324a91a0e7318a518c21310a4188210000000000 5 7 1 (by decide +kernel)
def done96 : Closed := closeBank chartAt #[done94,done95] #[hint0,hint23,hint6,hint3,hint55,hint7,hint67,hint1,hint2,hint62,hint33,hint5,hint41,hint8,hint43,hint10,hint306,hint53,hint307,hint17,hint225,hint226,hint24,hint25,hint26,hint76,hint77,hint57,hint35,hint36,hint58,hint39,hint59,hint45,hint46,hint49,hint50,hint106,hint71,hint13,hint72,hint37] [0xaa00aa00aa00aa,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xffff0000ffff0000,0xffffffff00000000] 0xa689e69249659249230000000000000000000000000000000000000000000000000000000000000000000000002e276120f34d0000000000000000000000000000000000000000000000000000000000002207de20f1c72dd71b20d1c70000000000000000000000000000000000000000000000002ce5da20f0410cc1190cd0412d85d62070410000000000000000000000000000000000002cf2cf20e21518d18d0cc0d42d32d22072071911900c10c10000000000000000000000002cf28f20e08218d14d0cc0822c92892070871841440c1081000000000000000000000000 6 7 2 (by decide +kernel)
def done97 : Closed := closeBank chartAt #[] #[hint0,hint164,hint165,hint2,hint166,hint167,hint168,hint169,hint170,hint322,hint171,hint172,hint173,hint174,hint175,hint176,hint177,hint178,hint3,hint323,hint179,hint180,hint181,hint324,hint325,hint182] [0xffffffff,0xffff0000ffff,0xaa00aa00aa00aa,0xff00ff00ff00ff,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0] 0x1e5591b98c000000000000000000000000000000000000000000000000001b86e1e0781b06c1de5700000000000000000000000000000000000000001d8f61b908952349310800000000000000000000000000000000000000001b84e1d4849320c9508418c841ca739208894610000000000000000000001b9ee1b4a51b16b1a8a518ca518d291a0a819cc6190a4188210000000000 5 7 0 (by decide +kernel)
def done98 : Closed := closeBank chartAt #[done97] #[hint0,hint183,hint184,hint3,hint185,hint186,hint326,hint2,hint187,hint188,hint189,hint190,hint191,hint192,hint193,hint194,hint195,hint196,hint197,hint198,hint327,hint328,hint329,hint330,hint331,hint332,hint199,hint200,hint201,hint202,hint203,hint204,hint205,hint206,hint166,hint167,hint170,hint71] [0xffff0000ffff,0xaa00aa00aa00aa,0xff00ff00ff00ff,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xffffffff00000000] 0x1e58e38e38e38e48e20000000000000000000000000000000000000000000000000000000000000000000000001e12e01ce7ce0000000000000000000000000000000000000000000000000000000000001de75c1ce24e1da6da1cb24b0000000000000000000000000000000000000000000000001ce1ce1d91d81cb1cb1d71d61c91c91d50d40000000000000000000000000000000000001ce4d21d11041cb40b1cf1040c80880c91040000000000000000000000000000000000001ce30e1cd1451cb30b1ca1450c90490c81451c71451c31860c41440c2041000000000000 6 7 1 (by decide +kernel)
def done99 : Closed := closeBank chartAt #[done97] #[hint0,hint207,hint208,hint2,hint185,hint50,hint333,hint106,hint209,hint210,hint211,hint212,hint213,hint214,hint186,hint215,hint3,hint216,hint217,hint218,hint183,hint219,hint220,hint334,hint335,hint336,hint337,hint338,hint221,hint222,hint223,hint224,hint166,hint170,hint71] [0xffffffff,0xaa00aa00aa00aa,0xff00ff00ff00ff,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xffff0000ffff0000] 0x4228208208208218200000000000000000000000000000000000000000000000000000000000000000000000000cd2df0ce78e00000000000000000000000000000000000000000000000000000000000041425d40e3ce0d221c0cb2490000000000000000000000000000000000000000000000000ce0ce0db41a0cb0cb0d90d80c90c90d741700000000000000000000000000000000000040e5954141040cb0930d210440944940f1040000000000000000000000000000000000000ce14e0cd30c0cb1cb0ca1450c91490c81c70c31450c31860c41440c2041000000000000 6 7 1 (by decide +kernel)
def done100 : Closed := closeBank chartAt #[done98,done99] #[hint0,hint14,hint23,hint3,hint52,hint55,hint1,hint2,hint119,hint16,hint62,hint19,hint20,hint8,hint21,hint22,hint10,hint12,hint15,hint86,hint87,hint24,hint25,hint26,hint29,hint30,hint34,hint35,hint36,hint38,hint39,hint40,hint45,hint46,hint48,hint50,hint106,hint71,hint72] [0xaa00aa00aa00aa,0xff00ff00ff00ff,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xffff0000ffff0000,0xffffffff00000000] 0x1e60e58e39248e38e20000000000000000000000000000000000000000000000000000000000000000000000001e17201d034d0000000000000000000000000000000000000000000000000000000000001df79d1d01861dc6da1cd1860000000000000000000000000000000000000000000000001ce5991d00820cb1580cd0821d75951c60820000000000000000000000000000000000001d01d01d41d41cd1cd1d30d31c61c61d21d21c21c21d10d10000000000000000000000001d024f1ce0410cd10c0cb0411ca2481c60410c51040c2041000000000000000000000000 6 7 2 (by decide +kernel)
def done101 : Closed := closeBank chartAt #[done84,done93,done97] #[hint0,hint164,hint165,hint5,hint166,hint167,hint2,hint322,hint233,hint234,hint168,hint169,hint170,hint171,hint172,hint173,hint174,hint175,hint176,hint323,hint236,hint3,hint177,hint178,hint67,hint179,hint180,hint71,hint72,hint134,hint13,hint324,hint325,hint339,hint340,hint182] [0xffffffff,0xffff0000ffff,0xff00ff00ff00ff,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0] 0xe33631913cf0000000000000000000000000000000000000000000000000000000000000e22e219130c6215e154f30c0000000000000000000000000000000000000000000000001912111a024918f50f55f24918c24c79d71b0000000000000000000000000000000000000d109119a10454f58f55910454c10c6175961891095544d300000000000000000000000019149119014518f38e0cd14518c14c0cb28a1891491881c71841440c2041000000000000 6 8 0 (by decide +kernel)
def done102 : Closed := closeBank chartAt #[done85] #[hint0,hint164,hint165,hint2,hint166,hint167,hint322,hint233,hint234,hint168,hint169,hint170,hint171,hint172,hint173,hint174,hint175,hint176,hint323,hint236,hint177,hint178,hint67,hint3,hint179,hint180,hint5,hint71,hint37,hint324,hint325,hint339,hint340,hint182] [0xffffffff,0xffff0000ffff,0xff00ff00ff00ff,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xffffffff00000000] 0xc33cf0c34100000000000000000000000000000000000000000000000000000000000000000000000000da30c0c338e0e13210d038e0000000000000000000000000000000000000000000000000000000000000da28a0c32cb0e02a00d02cb59f55f5ce2cb0000000000000000000000000000000000000000000000000c31c70c32080d01d00de2080ce4ce0dd2080cb20b0c371b0000000000000000000000000000000000000da0820c31040d00900d91045ce50e5d81045cb10b5955140c81080d34920000000000000000000000000000000000000d04500cf1450ce34d0cc1450cb14b0ca2490c81480c71860c41440c2041000000000000 6 8 0 (by decide +kernel)
def done103 : Closed := closeBank chartAt #[done86,done94,done98,done101,done102] #[hint0,hint326,hint240,hint3,hint241,hint186,hint2,hint183,hint184,hint67,hint185,hint187,hint188,hint189,hint190,hint191,hint5,hint192,hint193,hint71,hint72,hint134,hint13,hint328,hint330,hint244,hint332,hint341,hint194,hint195,hint196,hint197,hint198,hint199,hint200,hint201,hint202,hint203,hint204,hint205,hint206,hint166,hint167,hint234,hint170,hint135,hint136] [0xffff0000ffff,0xff00ff00ff00ff,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xffffffff00000000] 0xbadaaaaaaaacaabaa90000000000000000000000000000000000000000000000000000000000000000000000001a83a71929920000000000000000000000000000000000000000000000000000000000004259231923124218a118e30e00000000000000000000000000000000000000000000000041281f19e28a40e74e19c28a25b21b0cc28a00000000000000000000000000000000000019265219a10418e64e19810418c08c0d710418a10a5955130000000000000000000000004123d219114540e3ce18d1450cc1cc0cb1450ca14a2481c71841440c2041000000000000 6 8 1 (by decide +kernel)
def done104 : Closed := closeBank chartAt #[done87] #[hint0,hint308,hint165,hint5,hint166,hint167,hint2,hint322,hint233,hint234,hint168,hint169,hint170,hint171,hint172,hint173,hint174,hint175,hint176,hint323,hint236,hint3,hint177,hint178,hint179,hint309,hint71,hint13,hint324,hint325,hint339,hint340,hint67,hint182] [0xffffffff,0xffff0000ffff,0xff00ff00ff00ff,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xffff0000ffff0000] 0xc36591864510000000000000000000000000000000000000000000000000000000000000000000000005556185553cf0e13611913cf0000000000000000000000000000000000000000000000000000000000005605d755530c0df2df19130c55e5de54f30c00000000000000000000000000000000000000000000000018651455524919121119d24918f50f55c24918c24c5556da0000000000000000000000000000000000000000000000000d109119910454f58f55810454c10c5575961891095544d30000000000000000000000001860410c314519149119014518f38e0cd14518c14c0cb28a1891491881c71841440c2041000000000000 6 8 0 (by decide +kernel)
def done105 : Closed := closeBank chartAt #[done88] #[hint0,hint308,hint165,hint166,hint167,hint322,hint233,hint234,hint168,hint169,hint170,hint171,hint172,hint173,hint174,hint175,hint176,hint2,hint323,hint236,hint177,hint178,hint179,hint309,hint5,hint71,hint13,hint324,hint325,hint339,hint340,hint3,hint67,hint182] [0xffffffff,0xffff0000ffff,0xff00ff00ff00ff,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xffff0000ffff0000,0xffffffff00000000] 0x1845801145100000000000000000000000000000000000000000000000000000000000000000000000000000000000001138e0113cf0115d70113cf0000000000000000000000000000000000000000000000000000000000000000000000000182cb01134d01f59601f34d0212e100f34d00000000000000000000000000000000000000000000000000000000000001824901128a02055501f28a01e25e00f28a01d55d00d28a0000000000000000000000000000000000000000000000000111860111c70114d30111c700f18f01c1c700d4cd01b1c700a1ca0116990000000000000000000000000000000000000180820110c300000000000000f08f0170c300d50d0160c300a0ca0155140070c701349200000000000000000000000000000000000001104101110400f40f00e10400d30c00b10400a10a009208007107006145003103002041000000000000 6 8 0 (by decide +kernel)
def done106 : Closed := closeBank chartAt #[done89,done104,done105] #[hint0,hint342,hint343,hint262,hint3,hint241,hint50,hint2,hint310,hint311,hint263,hint185,hint210,hint312,hint188,hint313,hint190,hint191,hint5,hint314,hint193,hint71,hint13,hint328,hint330,hint244,hint240,hint332,hint341,hint194,hint195,hint315,hint67,hint196,hint197,hint198,hint199,hint200,hint316,hint201,hint202,hint203,hint204,hint205,hint206,hint317,hint234,hint167,hint170,hint72,hint134] [0xffff0000ffff,0xff00ff00ff00ff,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xffff0000ffff0000,0xffffffff00000000] 0xcb1000befbefbf0bee0000000000000000000000000000000000000000000000000000000000000000000000000000000000000004934ad1d41d40000000000000000000000000000000000000000000000000000000000000000000000001ec42b1d4a944923cf1c74100000000000000000000000000000000000000000000000000000000000004a9a271d439410436610438e4a49641d03900000000000000000000000000000000000000000000000004948e21e12cb12029f1042cb4907901dd2cb11c29c10e2cb0000000000000000000000000000000000001d46541db1451c70da1041451d06501d81451ce0ce1171451cb14b1045950000000000000000000000004944541d31860000000000004904501cf18610e24e10d18c10b18b10a2481c5185103081000000000000 6 8 1 (by decide +kernel)
def done107 : Closed := closeBank chartAt #[done90,done95,done99,done101,done104] #[hint0,hint333,hint247,hint2,hint241,hint50,hint207,hint208,hint5,hint185,hint106,hint209,hint210,hint211,hint212,hint213,hint214,hint186,hint71,hint72,hint134,hint13,hint334,hint3,hint249,hint336,hint338,hint215,hint216,hint67,hint217,hint218,hint183,hint219,hint220,hint221,hint222,hint223,hint224,hint166,hint234,hint170,hint135,hint136] [0xffffffff,0xff00ff00ff00ff,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xffff0000ffff0000] 0xaea9e79e79e99e89e70000000000000000000000000000000000000000000000000000000000000000000000002103a60d19510000000000000000000000000000000000000000000000000000000000005e03245d16d121e2e30ce30c0000000000000000000000000000000000000000000000007518a15e024920e1df0de24974c70c5db2490000000000000000000000000000000000000d16115da1040ce08e0d91040cc60c5d61040c91095544d20000000000000000000000000d11512103cf0ce28e0cd1450cc14c20b28a0c91492071860c41440c2041000000000000 6 8 1 (by decide +kernel)
def done108 : Closed := closeBank chartAt #[done91,done102,done105] #[hint0,hint333,hint247,hint2,hint241,hint50,hint207,hint208,hint185,hint106,hint209,hint210,hint318,hint212,hint191,hint214,hint186,hint71,hint37,hint334,hint249,hint336,hint338,hint215,hint3,hint216,hint67,hint217,hint218,hint183,hint219,hint220,hint5,hint221,hint222,hint223,hint224,hint234,hint166,hint170,hint72,hint134] [0xffffffff,0xff00ff00ff00ff,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xffff0000ffff0000,0xffffffff00000000] 0xa689a69a69a79a50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000e03cf0c34100000000000000000000000000000000000000000000000000000000000000000000000000c330c0c334d0cf3640d08d00000000000000000000000000000000000000000000000000000000000000e028a0c32cb61d2e26105d00db2a10cd2cb0000000000000000000000000000000000000000000000000e01c70c32086907de61d2080cd1dc0db20868b64b6172080000000000000000000000000000000000000c30820c31040d05100d61040cd08d0d51040cb50b0d31040c81080c34910000000000000000000000000000000000000d01500cf38e0cd24d0cc1450cb14b0ca2490c81480c71860c41440c2041000000000000 6 8 1 (by decide +kernel)
def done109 : Closed := closeBank chartAt #[done92,done96,done100,done103,done106,done107,done108] #[hint0,hint71,hint72,hint134,hint13,hint14,hint6,hint2,hint28,hint3,hint23,hint7,hint32,hint1,hint33,hint42,hint8,hint44,hint10,hint12,hint52,hint53,hint67,hint15,hint16,hint17,hint5,hint19,hint20,hint21,hint22,hint24,hint25,hint26,hint29,hint55,hint30,hint34,hint35,hint36,hint38,hint39,hint40,hint45,hint46,hint49,hint50,hint48,hint106,hint135,hint136,hint137,hint138] [0xff00ff00ff00ff,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xffff0000ffff0000,0xffffffff00000000] 0xd33cb1baec30bafbad0000000000000000000000000000000000000000000000000000000000000000000000006ac9eb1d24100000000000000000000000000000000000000000000000000000000000001eaa681d234d6a79a51d034d00000000000000000000000000000000000000000000000069d8241d228a25b8e225028a6a181f1cd28a00000000000000000000000000000000000069261e1dd14559051c25b1456996171cd14559551324a1450000000000000000000000001d23921d11861d02d024f1861cd38d1cc1861ca2ca2481861c5185103081000000000000 6 8 2 (by decide +kernel)
def done110 : Closed := closeBank chartAt #[] #[hint0,hint164,hint165,hint2,hint166,hint167,hint168,hint169,hint170,hint171,hint172,hint173,hint174,hint175,hint176,hint344,hint177,hint178,hint3,hint179,hint180,hint345,hint181,hint274,hint13,hint182,hint346,hint347] [0xffffffff,0xffff0000ffff,0xaa00aa00aa00aa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00] 0x18f7b18dad000000000000000000000000000000000000000000000000001cb5a18d6b1e5391b56b00000000000000000000000000000000000000001e2f7000001d8f61b50894e3392d080000000000000000000000000000001cab518c841b44d1d08492e0b94c8492088946100000000000000000000018def18ca51b5cd1b0a51ad4a1a4a51a0a819cc6190a4188210000000000 5 7 0 (by decide +kernel)
def done111 : Closed := closeBank chartAt #[done110] #[hint0,hint183,hint184,hint3,hint185,hint186,hint187,hint188,hint189,hint2,hint190,hint191,hint348,hint349,hint192,hint193,hint194,hint195,hint281,hint90,hint13,hint196,hint197,hint198,hint199,hint200,hint350,hint351,hint201,hint202,hint203,hint352,hint204,hint205,hint206,hint353,hint354,hint166,hint167,hint170,hint71] [0xffff0000ffff,0xaa00aa00aa00aa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffffff00000000] 0x2689a69a69a69a79a500000000000000000000000000000000000000000000000000000000000000000000000026426324f24f0000000000000000000000000000000000000000000000000000000000002622a124f80f2497df24928a00000000000000000000000000000000000000000000000025e75c24f1cf2436da2491c725865824a1ca00000000000000000000000000000000000024f5d62551042544d200000024a44a2501040c60860c710400000000000000000000000024f2cf24e14524334c24914524a2ca2481450c70470c61450c41440c2041000000000000 6 7 1 (by decide +kernel)
def done112 : Closed := closeBank chartAt #[done110] #[hint0,hint207,hint208,hint2,hint185,hint50,hint106,hint209,hint210,hint211,hint212,hint355,hint213,hint214,hint186,hint215,hint3,hint216,hint217,hint218,hint281,hint89,hint13,hint183,hint219,hint220,hint221,hint350,hint351,hint222,hint356,hint223,hint224,hint357,hint358,hint166,hint170,hint71] [0xffffffff,0xaa00aa00aa00aa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000] 0x4258e38e38e38e48e30000000000000000000000000000000000000000000000000000000000000000000000000e24210ce0ce0000000000000000000000000000000000000000000000000000000000000cd2a00ce7ce0c379e0c328a00000000000000000000000000000000000000000000000041721d40e3ce0d071b0c32080d21da0ca20800000000000000000000000000000000000040e6584171040d65540000000ca0930d210440844840f1040000000000000000000000000ce14e0cd30c0c32cb0c31450ca18a0c91450c81480c71860c41440c2041000000000000 6 7 1 (by decide +kernel)
def done113 : Closed := closeBank chartAt #[done111,done112] #[hint0,hint14,hint23,hint3,hint52,hint55,hint1,hint2,hint119,hint16,hint62,hint18,hint13,hint19,hint20,hint8,hint21,hint22,hint10,hint24,hint25,hint26,hint27,hint12,hint29,hint30,hint31,hint15,hint34,hint35,hint36,hint38,hint39,hint40,hint225,hint86,hint226,hint87,hint45,hint46,hint48,hint50,hint106,hint71,hint72] [0xaa00aa00aa00aa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000] 0x1ec0eba69a69aaaa680000000000000000000000000000000000000000000000000000000000000000000000001e77a61d23cf0000000000000000000000000000000000000000000000000000000000001e51e41d21d21e30e21cf1cf0000000000000000000000000000000000000000000000001e181f1d21861de75c1cf1861c76da1c71860000000000000000000000000000000000001d05191d20820cd1580cf0821c35d61c70821d55131c60820000000000000000000000001d22511d00410cf10e0cd0411cc1cb0000001ca2481c60410c51040c2041000000000000 6 7 2 (by decide +kernel)
def done114 : Closed := closeBank chartAt #[done65,done110] #[hint0,hint164,hint165,hint2,hint166,hint167,hint359,hint233,hint234,hint168,hint169,hint170,hint171,hint172,hint173,hint174,hint175,hint176,hint275,hint236,hint177,hint178,hint3,hint179,hint180,hint72,hint13,hint277,hint278,hint339,hint340,hint71,hint182] [0xffffffff,0xffff0000ffff,0xff00ff00ff00ff,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00] 0xc371c0c34100000000000000000000000000000000000000000000000000000000000000000000000000d66db0c338e0e03200d038e0000000000000000000000000000000000000000000000000000000000000da0df0c32cb0de29e0d02cb59d55d58e2cb0000000000000000000000000000000000000000000000000000000000000d01d00dc2080ce4ce0db2080cb20b0c36990000000000000000000000000000000000000d64920c31040d00900d810458e50e59710458b10b5955140c81080d34920000000000000000000000000c31860c31450d04500cf1450ce34d0cc1450cb14b0ca2490c81480c71860c41440c2041000000000000 6 8 0 (by decide +kernel)
def done115 : Closed := closeBank chartAt #[done66,done111,done114] #[hint0,hint290,hint360,hint2,hint51,hint186,hint183,hint184,hint3,hint185,hint187,hint188,hint189,hint190,hint191,hint361,hint192,hint193,hint72,hint13,hint258,hint362,hint363,hint244,hint364,hint365,hint366,hint194,hint195,hint71,hint196,hint197,hint198,hint199,hint200,hint367,hint201,hint202,hint203,hint204,hint205,hint206,hint368,hint166,hint167,hint170,hint134] [0xffff0000ffff,0xff00ff00ff00ff,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffffff00000000] 0xee000b2cb2cb2d000b2b0000000000000000000000000000000000000000000000000000000000000000000000000000000000000d80ea0d10d10000000000000000000000000000000000000000000000000000000000000000000000000e93680d19d10c35960c334d0000000000000000000000000000000000000000000000000000000000000e69640d12d10c85630c32cb0e18a10cd2cd0000000000000000000000000000000000000000000000000d181f0de2490d30dd0c32490cd70d0db24921a1d920b2490000000000000000000000000000000000000d15d10d81040000000000000cd5cd0d61040cb08b0d51140c91090c34d20000000000000000000000000d13910d01450c804f0c31450cd38d0cc14520b18b20a1452091492071860c41440c2041000000000000 6 8 1 (by decide +kernel)
def done116 : Closed := closeBank chartAt #[done67,done112,done114] #[hint0,hint130,hint255,hint2,hint49,hint50,hint207,hint208,hint185,hint106,hint209,hint210,hint211,hint212,hint213,hint214,hint186,hint72,hint13,hint258,hint362,hint249,hint289,hint290,hint215,hint3,hint216,hint217,hint218,hint71,hint183,hint219,hint220,hint221,hint369,hint222,hint223,hint224,hint370,hint166,hint170,hint134] [0xffffffff,0xff00ff00ff00ff,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000] 0x6690009e79e79e80009e70000000000000000000000000000000000000000000000000000000000000000000000000000000000000d76660d00d00000000000000000000000000000000000000000000000000000000000000000000000000cf3650d09100c35960c334d00000000000000000000000000000000000000000000000000000000000065e2e36506100d95220c32cb0db2a10cd2cb00000000000000000000000000000000000000000000000065081f65e2080d20dd0c32080cd1dc0db20864b68b6582080000000000000000000000000000000000000d05500d71040000000000000cd08d0d61040cb54b0d41130c81080c34910000000000000000000000000d01500cf38e0c30410c31450cd24d0cc1450cb14b0ca2490c81480c71860c41440c2041000000000000 6 8 1 (by decide +kernel)
def done117 : Closed := closeBank chartAt #[done68,done113,done115,done116] #[hint0,hint72,hint13,hint2,hint14,hint28,hint3,hint23,hint32,hint1,hint42,hint8,hint44,hint10,hint12,hint52,hint53,hint15,hint16,hint17,hint71,hint19,hint20,hint21,hint22,hint24,hint25,hint26,hint29,hint55,hint30,hint34,hint35,hint36,hint38,hint39,hint40,hint45,hint46,hint48,hint50,hint106,hint134,hint135] [0xff00ff00ff00ff,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000] 0xeb1aa000a28a69a270000000000000000000000000000000000000000000000000000000000000000000000000000000000000000e68650cd2cb0000000000000000000000000000000000000000000000000000000000000000000000000cc0cc0cd0cd0ca18a0cb0cb0000000000000000000000000000000000000000000000000000000000000e48e20cd2490e181f0cb2490c32080c32490000000000000000000000000000000000000000000000000d769e0cd1c719575c18b1c70c61450c31c70db6990c91c70000000000000000000000000000000000000cd4980d710418b3d61951040c20d40c31040d34910c91041903ce1871040000000000000000000000000cd0cd0cc0cc0cb0cb0ca18a0000000000000c90c90c80c80c70c70c51850c40c40c3081000000000000 6 8 2 (by decide +kernel)
def done118 : Closed := closeBank chartAt #[done59,done70,done101,done114] #[hint0,hint133,hint255,hint5,hint49,hint51,hint2,hint196,hint208,hint185,hint47,hint257,hint258,hint259,hint260,hint256,hint247,hint241,hint183,hint263,hint67,hint3,hint261,hint264,hint265,hint262,hint254,hint371,hint267,hint372,hint71,hint281,hint72,hint13,hint269,hint266,hint268,hint234,hint170,hint134,hint135] [0xffffffff,0xffff0000ffff,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00] 0xa279659659669659650000000000000000000000000000000000000000000000000000000000000000000000001903a41917110000000000000000000000000000000000000000000000000000000000005593231916910d82e218e30c00000000000000000000000000000000000000000000000085181f19e2490ce21d19c24950c4db55a2490000000000000000000000000000000000005511111995960ce08e19810454c10c5575965491095134920000000000000000000000001911511903cf18e28e18d14518c14c0cb28a1891490c81c71841440c2041000000000000 6 8 1 (by decide +kernel)
def done119 : Closed := closeBank chartAt #[done102] #[hint0,hint133,hint255,hint2,hint49,hint51,hint373,hint374,hint208,hint185,hint47,hint257,hint258,hint318,hint260,hint244,hint247,hint241,hint183,hint263,hint67,hint3,hint261,hint264,hint265,hint262,hint5,hint254,hint371,hint267,hint372,hint281,hint269,hint266,hint268,hint234,hint170,hint71] [0xffffffff,0xffff0000ffff,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffffff00000000] 0xe58e38e38e48e30000000000000000000000000000000000000000000000000000000000000000000000000000000000000000c34100c34510000000000000000000000000000000000000000000000000000000000000000000000000c334d0c338e0d03a20d17510000000000000000000000000000000000000000000000000000000000000da2cb0c330c0d93210d16d10d82e00ce30c0000000000000000000000000000000000000000000000000da2080c32490d10df0c32490ce21e0dd24950c4dc55b2490000000000000000000000000000000000000da0820c31040d11110d95960ce08e0d810454c10c5575965491095134920000000000000000000000000000000000000d11510d03cf0ce28e0cd1450cc14c0cb28a0c91490c81c60c41440c2041000000000000 6 8 1 (by decide +kernel)
def done120 : Closed := closeBank chartAt #[done60,done71,done103,done115,done118,done119] #[hint0,hint19,hint52,hint67,hint14,hint8,hint3,hint55,hint23,hint35,hint2,hint1,hint36,hint5,hint7,hint6,hint42,hint46,hint10,hint12,hint53,hint15,hint16,hint17,hint71,hint18,hint72,hint13,hint21,hint22,hint24,hint25,hint26,hint27,hint28,hint30,hint31,hint32,hint33,hint38,hint39,hint40,hint43,hint44,hint49,hint51,hint253,hint47,hint134,hint135,hint136,hint137] [0xffff0000ffff,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffffff00000000] 0xcf2c70b6dbefb6eb6c0000000000000000000000000000000000000000000000000000000000000000000000002ab9aa2923cf0000000000000000000000000000000000000000000000000000000000002a9a272922cb2a696428f2cb00000000000000000000000000000000000000000000000035c7e329220818e8a128f2083607de28b20800000000000000000000000000000000000035259d29c1046cf69929810435759528b1040d409318810400000000000000000000000035231229114518f40f28e14534b30b2891451880481871451841440c2041000000000000 6 8 2 (by decide +kernel)
def done121 : Closed := closeBank chartAt #[done104] #[hint0,hint133,hint255,hint5,hint49,hint51,hint2,hint196,hint208,hint185,hint47,hint257,hint258,hint259,hint260,hint256,hint247,hint241,hint310,hint104,hint263,hint3,hint210,hint249,hint312,hint265,hint262,hint254,hint371,hint267,hint372,hint281,hint67,hint269,hint266,hint268,hint234,hint170,hint71] [0xffffffff,0xffff0000ffff,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000] 0x56692492492500092400000000000000000000000000000000000000000000000000000000000000000000000000000000000055569a1864510000000000000000000000000000000000000000000000000000000000000000000000000c365918638e1903a319175100000000000000000000000000000000000000000000000000000000000055561855530c55a3221916d10d92e118e30c00000000000000000000000000000000000000000000000056051455524955155f1952490ce21e19d24954c51c55b24900000000000000000000000000000000000000000000000055111119a5d70ce08e19910454c10c5585d65491095544d20000000000000000000000001860410c31451911511903cf18e28e18d14518c14c0cb28a1891490c81c71841440c2041000000000000 6 8 1 (by decide +kernel)
def done122 : Closed := closeBank chartAt #[done105] #[hint0,hint133,hint255,hint49,hint51,hint373,hint374,hint208,hint185,hint47,hint257,hint258,hint318,hint260,hint244,hint247,hint241,hint2,hint310,hint104,hint263,hint210,hint249,hint312,hint265,hint262,hint5,hint254,hint371,hint267,hint372,hint281,hint3,hint67,hint269,hint266,hint268,hint170,hint234,hint71] [0xffffffff,0xffff0000ffff,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000] 0x4679a69a69a500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001a45a0114510000000000000000000000000000000000000000000000000000000000000000000000000000000000000113cf01141001165901141000000000000000000000000000000000000000000000000000000000000000000000000001130c01134d01161801134d00f36401075000000000000000000000000000000000000000000000000000000000000001a28a0112cb0205d70202cb0192e30106d00182a200d2cb00000000000000000000000000000000000000000000000001a1c701120802151402020801045f01120800d1de01d20800b51c01b20800000000000000000000000000000000000001a0820110c30000000000000100d001959600d08d0180c300b0cb0175950080c80144d200000000000000000000000000000000000001104101110401011000f38e00d24d00c10400b10b00a249008108007185003103002041000000000000 6 8 1 (by decide +kernel)
def done123 : Closed := closeBank chartAt #[done106,done121,done122] #[hint0,hint52,hint67,hint3,hint14,hint55,hint23,hint35,hint2,hint1,hint5,hint7,hint6,hint46,hint10,hint12,hint53,hint15,hint16,hint17,hint18,hint21,hint22,hint24,hint25,hint26,hint27,hint28,hint30,hint31,hint32,hint33,hint38,hint39,hint40,hint43,hint44,hint253,hint51,hint47,hint71,hint72,hint134] [0xffff0000ffff,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000] 0xaa90000e89a69e79a500000000000000000000000000000000000000000000000000000000000000000000000000000000000000028d28d20e20e0000000000000000000000000000000000000000000000000000000000000000000000002247e320e30c0c32cb20830c00000000000000000000000000000000000000000000000000000000000022286020e24928a1c720824921f79d20c24900000000000000000000000000000000000000000000000029561c20e1860c31450c31860cb6da20c18629961720918600000000000000000000000000000000000028e4962151040c20410c31040cc0d42031042934912091040d004f0c610400000000000000000000000028e28e20d20d0000000000000cc0cc20b20b2892892072070c60c60c50c50c40c40c1081000000000000 6 8 2 (by decide +kernel)
def done124 : Closed := closeBank chartAt #[done61,done72,done107,done116,done118,done121] #[hint0,hint21,hint16,hint5,hint14,hint10,hint2,hint25,hint23,hint39,hint1,hint40,hint33,hint6,hint44,hint36,hint8,hint46,hint3,hint12,hint52,hint53,hint67,hint15,hint17,hint71,hint18,hint72,hint13,hint19,hint20,hint24,hint26,hint27,hint28,hint7,hint29,hint55,hint31,hint32,hint34,hint35,hint41,hint42,hint49,hint48,hint254,hint104,hint134,hint135,hint136,hint137] [0xffffffff,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000] 0xcf2c70b2cbeeb2db2c0000000000000000000000000000000000000000000000000000000000000000000000004ab8ea19034d0000000000000000000000000000000000000000000000000000000000000cfa6819028a18c9e618d28a00000000000000000000000000000000000000000000000049d9644902084a38a118d2080e01df18a20800000000000000000000000000000000000059051e49d10470d6da1991040d809718a1045955134881040000000000000000000000001904500cf14518d38d18c14518a2ca1891451880480c71451841440c2041000000000000 6 8 2 (by decide +kernel)
def done125 : Closed := closeBank chartAt #[done108,done119,done122] #[hint0,hint16,hint5,hint2,hint14,hint25,hint23,hint39,hint1,hint33,hint6,hint36,hint8,hint3,hint12,hint52,hint53,hint67,hint15,hint17,hint18,hint19,hint20,hint24,hint26,hint27,hint28,hint7,hint29,hint55,hint31,hint32,hint34,hint35,hint41,hint42,hint48,hint49,hint254,hint104,hint71,hint72,hint134] [0xffffffff,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000] 0xaa90e89659e69640000000000000000000000000000000000000000000000000000000000000000000000000000000000000000c22cb0c330c0000000000000000000000000000000000000000000000000000000000000000000000000c32490c328a0e36e20cc28a0000000000000000000000000000000000000000000000000000000000000c31c70c32080cb8600cc2080c97de0ca2080000000000000000000000000000000000000000000000000c21450c318635575c34c1860db6990ca1860d81570c81860000000000000000000000000000000000000c20410c310444c3d63551040ca0d40c31040d30520c81044503ce3461040000000000000000000000000000000000000cc0cc0cb08b0ca0ca0c90c90c80c80c70c70c60c60c50850c40c40c1081000000000000 6 8 2 (by decide +kernel)
def done126 : Closed := closeBank chartAt #[done62,done73,done77,done79,done80,done81,done82,done83,done109,done117,done120,done123,done124,done125] #[hint0,hint14,hint23,hint3,hint12,hint52,hint53,hint67,hint1,hint2,hint15,hint16,hint17,hint5,hint71,hint18,hint72,hint6,hint13,hint19,hint20,hint8,hint21,hint22,hint10,hint24,hint25,hint26,hint27,hint28,hint7,hint29,hint55,hint30,hint31,hint32,hint33,hint34,hint35,hint36,hint38,hint39,hint40,hint41,hint42,hint43,hint44,hint45,hint46,hint134,hint135,hint136,hint137,hint138,hint139,hint140,hint141,hint142,hint143,hint144,hint145] [0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000] 0xf3beb9e37db5d33cb10000000000000000000000000000000000000000000000000000000000000000000000003709ef25855500000000000000000000000000000000000000000000000000000000000026e92d2584510ec7ab25545100000000000000000000000000000000000000000000000026aa682582083679a52552082648e22512080000000000000000000000000000000000003566a12580820d381f0d50820de75c25108235b6992480820000000000000000000000003582d72560411d51540d304149140f24e04134c2ca2480411c61440c2041000000000000 6 8 3 (by decide +kernel)
def done127 : Closed := closeBank chartAt #[] #[hint0,hint375,hint376,hint2,hint377,hint378,hint379,hint380,hint185,hint381,hint382,hint383,hint384,hint385,hint386,hint387,hint388,hint389,hint3,hint390,hint391,hint392,hint170,hint166] [0xf0f0f0f0f0f0f0f,0x3333333333333333,0xff55ff55ff55ff55,0xffff0000ffff0000,0xffffffff00000000] 0x2d6b5af7b5ad6000000000000000000000000000000000000000000000000001d5351b98c00000000000000000000000000000000000000001d0f41b90894e33931080000000000000000000000000000001b84e1d0849320c94c849208894610000000000000000000001b9ee1b4a51b16a1a4a51a0a819cc6190a4188210000000000 5 6 1 (by decide +kernel)
def done128 : Closed := closeBank chartAt #[] #[hint0,hint393,hint394,hint2,hint377,hint252,hint386,hint395,hint378,hint396,hint208,hint185,hint397,hint398,hint384,hint399,hint388,hint389,hint3,hint390,hint400,hint401,hint170,hint166] [0xffffffff,0x3333333333333333,0xf0f0f0f0f0f0f0f0,0xff55ff55ff55ff55,0xffff0000ffff0000] 0x2d6bded6b5ad60000000000000000000000000000000000000000000000000094e339396b00000000000000000000000000000000000000001b2b51b9081a9081ae8b00000000000000000000000000000093a0e94c8492c8b946101a0481bc84000000000000000000001b9ad1b0a51acab1a9291a0a819cc6190a4188210000000000 5 6 1 (by decide +kernel)
def done129 : Closed := closeBank chartAt #[done127,done128] #[hint0,hint23,hint26,hint2,hint1,hint25,hint52,hint55,hint3,hint14,hint225,hint8,hint226,hint10,hint62,hint16,hint229,hint35,hint36,hint230,hint39,hint231,hint45,hint46,hint48,hint252,hint71,hint106,hint72] [0x3333333333333333,0xf0f0f0f0f0f0f0f0,0xff55ff55ff55ff55,0xffff0000ffff0000,0xffffffff00000000] 0x7cce77b1eb38000000000000000000000000000000000000000000000000001de561b56b00000000000000000000000000000000000000001b1ec1b529428ca42d290000000000000000000000000000001d6931b4841ca301ac841bc841a5c9000000000000000000001b4ad1b02142ceb4282142429418e6190a4188210000000000 5 6 2 (by decide +kernel)
def done130 : Closed := closeBank chartAt #[done127] #[hint0,hint1,hint25,hint2,hint23,hint26,hint119,hint62,hint16,hint14,hint36,hint8,hint35,hint231,hint10,hint39,hint55,hint3,hint52,hint227,hint225,hint228,hint226,hint45,hint46,hint48,hint71,hint50,hint253] [0xf0f0f0f0f0f0f0f,0xcccccccccccccccc,0xff55ff55ff55ff55,0xffff0000ffff0000,0xffffffff00000000] 0x339e737b8eb39000000000000000000000000000000000000000000000000001e1571b96b00000000000000000000000000000000000000001d9161b9298d2548ad290000000000000000000000000000001d8551b8848d2138ac848c8848a609000000000000000000001b9ee1b4211ad8b1a8211a4291a0e6190a4188210000000000 5 6 2 (by decide +kernel)
def done131 : Closed := closeBank chartAt #[done47] #[hint0,hint402,hint403,hint2,hint48,hint253,hint252,hint394,hint377,hint404,hint378,hint405,hint386,hint208,hint185,hint384,hint406,hint3,hint407,hint408,hint263,hint409,hint410,hint170,hint71,hint13] [0xffffffff,0xffff0000ffff,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff55ff55ff55ff55] 0x338bdef7bdef7000000000000000000000000000000000000000000000000001b54a1bace00000000000000000000000000000000000000008d1088ba0e1c8f51a9080000000000000000000000000000008b88e8d1f31a84a1c8848a0888c1ef000000000000000000001b8ae1b58b1a8ca1a4a51a0a819cc6190a4188210000000000 5 6 1 (by decide +kernel)
def done132 : Closed := closeBank chartAt #[done48,done131] #[hint0,hint8,hint55,hint3,hint23,hint225,hint35,hint2,hint1,hint36,hint20,hint52,hint14,hint46,hint10,hint24,hint25,hint26,hint228,hint226,hint62,hint16,hint230,hint39,hint231,hint48,hint253,hint252,hint71,hint13,hint72] [0xffff0000ffff,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff55ff55ff55ff55,0xffffffff00000000] 0xfeef35adef59000000000000000000000000000000000000000000000000003ceb33b98c00000000000000000000000000000000000000003e2f63b9083d5083b28c0000000000000000000000000000003ce123b8841ac841b04c3c60f3a084000000000000000000003b92e3b4211b0ac1ac2a3a12839821190a4188210000000000 5 6 2 (by decide +kernel)
def done133 : Closed := closeBank chartAt #[done49,done128,done131] #[hint0,hint10,hint25,hint2,hint23,hint226,hint39,hint1,hint231,hint22,hint16,hint14,hint36,hint8,hint46,hint24,hint26,hint55,hint3,hint52,hint227,hint225,hint62,hint229,hint35,hint48,hint72,hint71,hint13,hint134] [0xffffffff,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff55ff55ff55ff55,0xffff0000ffff0000] 0x25de6f3996b3900000000000000000000000000000000000000000000000000956759356b00000000000000000000000000000000000000001b3171b4e71a8e71aecb000000000000000000000000000000956349348494c8492e2b1c04f19c84000000000000000000001b5cd1b0211acab1a82919d0719821190a4188210000000000 5 6 2 (by decide +kernel)
def done134 : Closed := closeBank chartAt #[done50,done129,done130,done132,done133] #[hint0,hint23,hint1,hint2,hint24,hint25,hint26,hint14,hint55,hint3,hint52,hint8,hint227,hint225,hint10,hint228,hint226,hint62,hint16,hint229,hint35,hint36,hint230,hint39,hint231,hint45,hint46,hint72,hint134,hint71,hint13,hint135,hint136] [0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff55ff55ff55ff55,0xffff0000ffff0000,0xffffffff00000000] 0xe025f79d0dc25b0000000000000000000000000000000000000000000000000000000000000da5590ce2cb0000000000000000000000000000000000000000000000000d04900ce1c724d28d24b1c70000000000000000000000000000000000000d85d60ce0820d55130cb0820d20820c74470000000000000000000000000d014f0ce04124d20c24b04124a0412472070c61440c2041000000000000 6 6 3 (by decide +kernel)
def done135 : Closed := closeBank chartAt #[] #[hint0,hint14,hint23,hint3,hint12,hint52,hint53,hint1,hint2,hint15,hint16,hint17,hint18,hint6,hint19,hint20,hint8,hint21,hint22,hint10,hint24,hint25,hint26,hint27,hint28,hint7,hint29,hint55,hint30,hint31,hint32,hint33,hint34,hint35,hint36,hint38,hint39,hint40,hint41,hint42,hint43,hint44,hint45,hint46,hint48,hint49,hint47,hint50,hint51] [0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000] 0xb6dc30befb6dbaeb6c00000000000000000000000000000000000000000000000000000000000000000000000022b8aa2134100000000000000000000000000000000000000000000000000000000000002297e821334d22766621034d0000000000000000000000000000000000000000000000002259232131c72228602101c721f79d20d1c700000000000000000000000000000000000021155c2130820ce6da0d008221961720d0822165542070820000000000000000000000002132922110410d014f0ce04120d20c20804120b2892070410c61440c2041000000000000 6 7 2 (by decide +kernel)
def done136 : Closed := closeBank chartAt #[done127] #[hint0,hint375,hint376,hint2,hint377,hint378,hint411,hint380,hint185,hint412,hint413,hint414,hint415,hint381,hint382,hint383,hint384,hint385,hint386,hint387,hint416,hint389,hint3,hint417,hint418,hint419,hint390,hint388,hint391,hint71,hint13,hint420,hint421,hint392,hint170,hint234] [0xf0f0f0f0f0f0f0f,0x3333333333333333,0x5555555555555555,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000] 0x8a28a28a28e38a28a20000000000000000000000000000000000000000000000000000000000000000000000000e13610d24100000000000000000000000000000000000000000000000000000000000000e02600d230c0df5df0d030c0000000000000000000000000000000000000000000000000dc1dc0d220859a55a5902080de0dd0cc2080000000000000000000000000000000000000d20920dc1045906d059a1040cc6580d71045881085955140000000000000000000000000d24d20d11450d03ce0cd1450cc2ca0c91450c81480c71860c41440c2041000000000000 6 7 1 (by decide +kernel)
def done137 : Closed := closeBank chartAt #[done128] #[hint0,hint393,hint394,hint2,hint377,hint252,hint131,hint208,hint185,hint386,hint395,hint378,hint422,hint423,hint415,hint397,hint398,hint384,hint416,hint389,hint3,hint399,hint417,hint418,hint419,hint390,hint388,hint424,hint71,hint13,hint425,hint401,hint420,hint170,hint234] [0xffffffff,0x3333333333333333,0x5555555555555555,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000] 0x8618618618a28618610000000000000000000000000000000000000000000000000000000000000000000000000e05a00d138e0000000000000000000000000000000000000000000000000000000000000cf7df0d12cb0cc79e0ce2cb0000000000000000000000000000000000000000000000005194d95112080dd0dc0ce2080cb1cb0db2080000000000000000000000000000000000005116915191040ce6170d61040cb08b0d51045081085134920000000000000000000000000d14100cf1450ce34d0cc1450cb14b0ca2490c81480c71860c41440c2041000000000000 6 7 1 (by decide +kernel)
def done138 : Closed := closeBank chartAt #[done129,done136,done137] #[hint0,hint12,hint53,hint52,hint3,hint14,hint23,hint26,hint2,hint1,hint25,hint7,hint6,hint28,hint19,hint8,hint55,hint21,hint10,hint17,hint16,hint71,hint13,hint31,hint32,hint33,hint34,hint35,hint36,hint38,hint39,hint40,hint41,hint42,hint43,hint44,hint45,hint46,hint48,hint252,hint47,hint72,hint134] [0x3333333333333333,0x5555555555555555,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000] 0x22a9e79e7229a289e60000000000000000000000000000000000000000000000000000000000000000000000002257242123cf00000000000000000000000000000000000000000000000000000000000022366221230c2212e020f30c00000000000000000000000000000000000000000000000021f79d21224921c6da20f24921961720c24900000000000000000000000000000000000021151121214510e0ce10f14521621520c14520950921314500000000000000000000000021229221118610f40f10e18620c34c20b186209289207186105185103081000000000000 6 7 2 (by decide +kernel)
def done139 : Closed := closeBank chartAt #[done130,done136] #[hint0,hint15,hint17,hint16,hint2,hint14,hint1,hint25,hint23,hint26,hint33,hint6,hint32,hint36,hint8,hint35,hint40,hint10,hint39,hint53,hint3,hint52,hint71,hint13,hint19,hint21,hint27,hint28,hint7,hint29,hint55,hint30,hint41,hint42,hint43,hint44,hint45,hint46,hint48,hint49,hint72,hint253] [0xf0f0f0f0f0f0f0f,0x5555555555555555,0xcccccccccccccccc,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000] 0x9a6a699a65289e79a600000000000000000000000000000000000000000000000000000000000000000000000012536411138e0000000000000000000000000000000000000000000000000000000000001232a21112cb12172010e2cb0000000000000000000000000000000000000000000000001191df11120851879d50e20811c6da10b2080000000000000000000000000000000000001190d911114551855850e14511711610b14550854851314500000000000000000000000011149111018610e3ce10d18610b30b10a186108248107186105185103081000000000000 6 7 2 (by decide +kernel)
def done140 : Closed := closeBank chartAt #[] #[hint0,hint18,hint6,hint2,hint14,hint28,hint23,hint7,hint32,hint1,hint33,hint42,hint8,hint44,hint10,hint53,hint3,hint52,hint17,hint16,hint19,hint21,hint24,hint25,hint26,hint29,hint55,hint30,hint34,hint35,hint36,hint38,hint39,hint40,hint45,hint46,hint48,hint50,hint252,hint253] [0xff00ff00ff00ff,0x5555555555555555,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xffff0000ffff0000,0xffffffff00000000] 0x9249e79249a69659240000000000000000000000000000000000000000000000000000000000000000000000000e37a20ce30c0000000000000000000000000000000000000000000000000000000000000e181f0ce2490de75c0cc2490000000000000000000000000000000000000000000000000d55db0ce18641469940c1860d85d60c91860000000000000000000000000000000000000d54d50ce10441445440c1040c94c90d210440644640f1040000000000000000000000000ce28e0cd0820cc1cc0cb0820c92890c80820c61c60c50820c40c40c3081000000000000 6 7 2 (by decide +kernel)
def done141 : Closed := closeBank chartAt #[done131] #[hint0,hint402,hint403,hint2,hint48,hint253,hint132,hint208,hint185,hint252,hint394,hint377,hint404,hint378,hint422,hint426,hint415,hint92,hint263,hint3,hint384,hint406,hint407,hint427,hint428,hint429,hint424,hint71,hint13,hint409,hint430,hint425,hint170,hint234] [0xffffffff,0xffff0000ffff,0x5555555555555555,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00] 0x8208208208618208200000000000000000000000000000000000000000000000000000000000000000000000000ce7df0d034d0000000000000000000000000000000000000000000000000000000000000d779e0d02cb0d629d0cd2cb0000000000000000000000000000000000000000000000000dc0db0d02080cd1cd0da2084cb48b4d92080000000000000000000000000000000000000d06180d71040cd08d0d61044cb10b4d55144c81084d24510000000000000000000000000d03cf0ce1450cd24d0cc1450cb14b0ca2490c81480c71860c41440c2041000000000000 6 7 1 (by decide +kernel)
def done142 : Closed := closeBank chartAt #[done132,done141] #[hint0,hint20,hint8,hint52,hint3,hint14,hint19,hint55,hint23,hint35,hint2,hint1,hint36,hint7,hint6,hint42,hint46,hint10,hint53,hint17,hint16,hint71,hint13,hint21,hint24,hint25,hint26,hint27,hint28,hint30,hint31,hint32,hint33,hint38,hint39,hint40,hint43,hint44,hint48,hint253,hint51,hint252,hint72] [0xffff0000ffff,0x5555555555555555,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffffff00000000] 0x2aa9e79e7a69a289e60000000000000000000000000000000000000000000000000000000000000000000000002a582429138e0000000000000000000000000000000000000000000000000000000000002a38a12912cb2a07de28e2cb00000000000000000000000000000000000000000000000029765d29120828d71b28e20829a65828b20800000000000000000000000000000000000029751729114529629528e14528b50b2931451080c811214500000000000000000000000029131129008228e3ce28d08228b30b289082108188107082105185103081000000000000 6 7 2 (by decide +kernel)
def done143 : Closed := closeBank chartAt #[done133,done137,done141] #[hint0,hint22,hint10,hint16,hint2,hint14,hint21,hint25,hint23,hint39,hint1,hint40,hint33,hint6,hint44,hint36,hint8,hint46,hint53,hint3,hint52,hint17,hint71,hint13,hint19,hint24,hint26,hint27,hint28,hint7,hint29,hint55,hint31,hint32,hint34,hint35,hint41,hint42,hint48,hint49,hint72,hint134] [0xffffffff,0x5555555555555555,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000] 0x4e99a69a64e89e79a600000000000000000000000000000000000000000000000000000000000000000000000012576411034d00000000000000000000000000000000000000000000000000000000000010f8e211028a10c86010d28a0000000000000000000000000000000000000000000000004d87de4d020811d71b10d20811a1d910a2080000000000000000000000000000000000004d85184d014511711610d14510a0ca1151454c85084d214500000000000000000000000011045010f08210d38d10c08210a2ca109082108188107082105185103081000000000000 6 7 2 (by decide +kernel)
def done144 : Closed := closeBank chartAt #[done134,done135,done138,done139,done140,done142,done143] #[hint0,hint14,hint53,hint3,hint23,hint52,hint17,hint2,hint1,hint16,hint6,hint71,hint13,hint8,hint19,hint10,hint21,hint24,hint25,hint26,hint27,hint28,hint7,hint29,hint55,hint30,hint31,hint32,hint33,hint34,hint35,hint36,hint38,hint39,hint40,hint41,hint42,hint43,hint44,hint45,hint46,hint72,hint134,hint135,hint136,hint137,hint138] [0x5555555555555555,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000] 0x1ee0ed1ec1eb0ea3290000000000000000000000000000000000000000000000000000000000000000000000001e87e71cf34d0000000000000000000000000000000000000000000000000000000000001e67251cf28a1e45a31cd28a0000000000000000000000000000000000000000000000001e28601cf2081df79d1cd2081dc6da1ca2080000000000000000000000000000000000001d04991cf1040ce6170cd1041d65541ca1041d34911c81040000000000000000000000001d02501cf0410ce14e0cd0411cc1cb1ca0411c82481c60410c41440c2041000000000000 6 7 3 (by decide +kernel)
def done145 : Closed := closeBank chartAt #[done136] #[hint0,hint24,hint26,hint25,hint2,hint23,hint1,hint16,hint14,hint17,hint33,hint6,hint32,hint36,hint8,hint35,hint40,hint10,hint39,hint52,hint3,hint53,hint7,hint28,hint19,hint55,hint21,hint18,hint20,hint22,hint41,hint42,hint43,hint44,hint45,hint46,hint47,hint254,hint49,hint104,hint71,hint13,hint215] [0xf0f0f0f0f0f0f0f,0x3333333333333333,0xaaaaaaaaaaaaaaaa,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000] 0x965965aaaa689e696400000000000000000000000000000000000000000000000000000000000000000000000012336211138e0000000000000000000000000000000000000000000000000000000000001212a01112cb11f59e10e2cb0000000000000000000000000000000000000000000000001111dd11a20850e4dc51820810b11b1042080000000000000000000000000000000000001110d111a14550e64e51814510b5cb11614550854851314500000000000000000000000011149111018610e3ce10d18610b30b10a186108248107186105185103081000000000000 6 7 2 (by decide +kernel)
def done146 : Closed := closeBank chartAt #[] #[hint0,hint23,hint52,hint3,hint14,hint55,hint1,hint2,hint119,hint16,hint62,hint225,hint20,hint8,hint226,hint22,hint10,hint26,hint25,hint229,hint35,hint36,hint230,hint39,hint231,hint45,hint46,hint252,hint106,hint50,hint215,hint188] [0xaa00aa00aa00aa,0x3333333333333333,0xf0f0f0f0f0f0f0f0,0xffff0000ffff0000,0xffffffff00000000] 0x3defffdee779b000000000000000000000000000000000000000000000000003eab93c1ad00000000000000000000000000000000000000003e2f63c0c63d6933b4c60000000000000000000000000000003c2503b8211b4ad1ac2139a463c421000000000000000000003c12f3b8841b44c1ac843a9283988419484184410000000000 5 6 2 (by decide +kernel)
def done147 : Closed := closeBank chartAt #[done146] #[hint0,hint27,hint7,hint28,hint2,hint23,hint6,hint71,hint13,hint14,hint32,hint1,hint33,hint42,hint8,hint44,hint10,hint52,hint3,hint53,hint26,hint25,hint19,hint55,hint21,hint15,hint16,hint17,hint20,hint22,hint34,hint35,hint36,hint38,hint39,hint40,hint45,hint46,hint47,hint106,hint50,hint252,hint215,hint188] [0xff00ff00ff00ff,0x3333333333333333,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0,0xffff0000ffff0000,0xffffffff00000000] 0xaaaaebaaa9e99e89e600000000000000000000000000000000000000000000000000000000000000000000000012582411038e0000000000000000000000000000000000000000000000000000000000001238a11102cb1207de10e2cb00000000000000000000000000000000000000000000000011069d11824948e45c49624911b69910b24900000000000000000000000000000000000011055011814548e5ce49614510b54b1141454894c949114500000000000000000000000011031010f18610e08e10d18610b30b10a186109189104207105185103081000000000000 6 7 2 (by decide +kernel)
def done148 : Closed := closeBank chartAt #[] #[hint0,hint29,hint19,hint55,hint3,hint23,hint8,hint52,hint14,hint35,hint2,hint1,hint36,hint7,hint6,hint42,hint46,hint10,hint53,hint26,hint25,hint28,hint21,hint15,hint16,hint17,hint18,hint22,hint31,hint32,hint33,hint38,hint39,hint40,hint43,hint44,hint47,hint51,hint252,hint254,hint188] [0xffff0000ffff,0x3333333333333333,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffffff00000000] 0x9e7a289e79269259240000000000000000000000000000000000000000000000000000000000000000000000002a37a229138e0000000000000000000000000000000000000000000000000000000000002a181f2912cb29e75c28e2cb00000000000000000000000000000000000000000000000029161b29620828e29a28a20829961728b20800000000000000000000000000000000000029151129614528e54e28d14528b50b29314510848810714500000000000000000000000029131129018628e3ce28d18628b30b289186108188107082105185103081000000000000 6 7 2 (by decide +kernel)
def done149 : Closed := closeBank chartAt #[done137] #[hint0,hint30,hint21,hint25,hint2,hint23,hint10,hint16,hint14,hint39,hint1,hint40,hint33,hint6,hint44,hint36,hint8,hint46,hint52,hint3,hint53,hint26,hint7,hint28,hint19,hint55,hint15,hint17,hint18,hint20,hint31,hint32,hint34,hint35,hint41,hint42,hint47,hint254,hint49,hint104,hint71,hint13,hint215] [0xffffffff,0x3333333333333333,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000] 0x965aaa965a689e69640000000000000000000000000000000000000000000000000000000000000000000000001235a211034d00000000000000000000000000000000000000000000000000000000000010f86011028a10c7de10d28a0000000000000000000000000000000000000000000000004d049d4d820810d11c10420811b1da10a2080000000000000000000000000000000000004d06504d814510d5cd11614510a0ca1151454c85084d214500000000000000000000000011045010f18610d38d10c18610a2ca109186108188107082105185103081000000000000 6 7 2 (by decide +kernel)
def done150 : Closed := closeBank chartAt #[done135,done138,done145,done147,done148,done149] #[hint0,hint23,hint52,hint3,hint14,hint53,hint26,hint2,hint1,hint25,hint7,hint6,hint28,hint19,hint8,hint55,hint21,hint10,hint15,hint16,hint17,hint18,hint20,hint22,hint31,hint32,hint33,hint34,hint35,hint36,hint38,hint39,hint40,hint41,hint42,hint43,hint44,hint45,hint46,hint71,hint72,hint13,hint134,hint135,hint136,hint137] [0x3333333333333333,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000] 0x1ed0ec1eb1eaa680e70000000000000000000000000000000000000000000000000000000000000000000000001e67651d138e0000000000000000000000000000000000000000000000000000000000001e46a31d12cb1e22a11ce2cb0000000000000000000000000000000000000000000000001e07de1d12081dd71b1ce2081da6581cb2080000000000000000000000000000000000001d14d71d01040ce0960cd1041cb1d51c71041d44d21c81040000000000000000000000001d12511d00410ce3ce0cd0411cb30b1ca0411c82481c60410c41440c2041000000000000 6 7 3 (by decide +kernel)
def done151 : Closed := closeBank chartAt #[] #[hint0,hint1,hint16,hint2,hint14,hint62,hint23,hint3,hint52,hint55,hint225,hint20,hint8,hint226,hint22,hint10,hint25,hint26,hint36,hint35,hint231,hint39,hint227,hint228,hint45,hint46,hint48,hint50,hint215,hint311,hint204,hint223] [0xaa00aa00aa00aa,0xf0f0f0f0f0f0f0f,0xcccccccccccccccc,0xffff0000ffff0000,0xffffffff00000000] 0x3fff7bbcdef7a000000000000000000000000000000000000000000000000001e6581bd8c00000000000000000000000000000000000000001b6171bcc63a9363b0c60000000000000000000000000000001beaf1d0211b26c1c82119a261c021000000000000000000001bc4e1b4843b10b3a8843a5083988419484184410000000000 5 6 2 (by decide +kernel)
def done152 : Closed := closeBank chartAt #[done151] #[hint0,hint31,hint33,hint32,hint2,hint1,hint6,hint71,hint13,hint14,hint28,hint23,hint7,hint42,hint8,hint44,hint10,hint16,hint17,hint25,hint26,hint36,hint35,hint40,hint39,hint3,hint12,hint52,hint53,hint19,hint20,hint21,hint22,hint29,hint55,hint30,hint45,hint46,hint49,hint50,hint48,hint215,hint311,hint204,hint223] [0xff00ff00ff00ff,0xf0f0f0f0f0f0f0f,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xffff0000ffff0000,0xffffffff00000000] 0xb2caebaa99e89e79e600000000000000000000000000000000000000000000000000000000000000000000000012556411038e00000000000000000000000000000000000000000000000000000000000011f4e31102cb65d8a164e2cb00000000000000000000000000000000000000000000000011046011f24964e6de65d24965c6da64b24900000000000000000000000000000000000011061011714510e58e11514510b50b11314510948911114500000000000000000000000011009010f18610e30e10d18610b30b10a186109189104207105185103081000000000000 6 7 2 (by decide +kernel)
def done153 : Closed := closeBank chartAt #[] #[hint0,hint34,hint36,hint35,hint2,hint1,hint8,hint19,hint52,hint3,hint14,hint55,hint23,hint7,hint6,hint42,hint46,hint10,hint16,hint17,hint25,hint26,hint33,hint32,hint40,hint39,hint12,hint53,hint18,hint21,hint22,hint27,hint28,hint30,hint43,hint44,hint49,hint51,hint253,hint254,hint267,hint204] [0xffff0000ffff,0xf0f0f0f0f0f0f0f,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xff00ff00ff00ff00,0xffffffff00000000] 0xa28a69a279669659640000000000000000000000000000000000000000000000000000000000000000000000001235a211138e00000000000000000000000000000000000000000000000000000000000011d52111130c10d81f10e30c00000000000000000000000000000000000000000000000011149e11d28a10e11c10428a25b21a24c28a00000000000000000000000000000000000011165111814510e5ce11614510c54c11414510a4ca11214500000000000000000000000011109111018610e3ce10d18624c1cc24b18624a18a2481c7105185103081000000000000 6 7 2 (by decide +kernel)
def done154 : Closed := closeBank chartAt #[] #[hint0,hint38,hint40,hint39,hint2,hint1,hint10,hint21,hint16,hint14,hint25,hint23,hint33,hint6,hint44,hint36,hint8,hint46,hint17,hint26,hint32,hint35,hint3,hint12,hint52,hint53,hint18,hint19,hint20,hint27,hint28,hint7,hint29,hint55,hint41,hint42,hint49,hint48,hint254,hint104,hint223,hint267] [0xffffffff,0xf0f0f0f0f0f0f0f,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xff00ff00ff00ff00,0xffff0000ffff0000] 0xa69a289e69259249240000000000000000000000000000000000000000000000000000000000000000000000001237e211034d00000000000000000000000000000000000000000000000000000000000059b8605902cb11f79d10d2cb00000000000000000000000000000000000000000000000059061c59b24910d11a10424959961758b24900000000000000000000000000000000000011055010f14510d50d10c14510b4cb10a14510948910814500000000000000000000000011045010f18610d38d10c18610b1cb10a1861091891081c7105185103081000000000000 6 7 2 (by decide +kernel)
def done155 : Closed := closeBank chartAt #[done135,done139,done145,done152,done153,done154] #[hint0,hint1,hint16,hint2,hint14,hint17,hint25,hint23,hint26,hint33,hint6,hint32,hint36,hint8,hint35,hint40,hint10,hint39,hint3,hint12,hint52,hint53,hint18,hint19,hint20,hint21,hint22,hint27,hint28,hint7,hint29,hint55,hint30,hint41,hint42,hint43,hint44,hint45,hint46,hint71,hint72,hint13,hint134,hint135,hint136,hint137] [0xf0f0f0f0f0f0f0f,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000] 0xed4ac0eb4aaa680e70000000000000000000000000000000000000000000000000000000000000000000000000e63250d034d0000000000000000000000000000000000000000000000000000000000000e42630d028a0e27610cd28a0000000000000000000000000000000000000000000000000d91a00d01c74977de48d1c70dd71b0ca1c70000000000000000000000000000000000000d009a0d910448d5184971040ca0d60c31044955134871040000000000000000000000000d04500cf0410cd38d0cc0410ca2ca0c90410c72070c60410c41440c2041000000000000 6 7 3 (by decide +kernel)
def done156 : Closed := closeBank chartAt #[] #[hint0,hint431,hint317,hint214,hint2,hint186,hint193,hint196,hint208,hint185,hint432,hint433,hint434,hint435,hint318,hint436,hint206,hint183,hint263,hint3,hint312,hint437,hint438,hint439,hint440,hint441,hint167,hint166,hint170,hint13,hint173,hint175] [0xffffffff,0xffff0000ffff,0xaa00aa00aa00aa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0] 0x9f9fbbc9ec9a000000000000000000000000000000000000000000000000002655823dad000000000000000000000000000000000000000025d1623d299d2549b52900000000000000000000000000000023c6f254a59b62d9d0a59a4a99ca310000000000000000000023e0f238c62358b228c6224c9220e7214c520c410000000000 5 6 1 (by decide +kernel)
def done157 : Closed := closeBank chartAt #[done156] #[hint0,hint225,hint52,hint3,hint14,hint8,hint55,hint23,hint35,hint2,hint1,hint36,hint46,hint10,hint119,hint16,hint62,hint226,hint22,hint24,hint25,hint26,hint228,hint230,hint39,hint231,hint50,hint253,hint13,hint188,hint204,hint71] [0xffff0000ffff,0xaa00aa00aa00aa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xffffffff00000000] 0x13f4f87de6c7a000000000000000000000000000000000000000000000000004e7174b54a00000000000000000000000000000000000000004c6964b4e74d6934a8e70000000000000000000000000000004b5f24c4844c1ee4a8841984219c84000000000000000000004b56d4b0a54a96a4a0a519c27198a5190a4188210000000000 5 6 2 (by decide +kernel)
def done158 : Closed := closeBank chartAt #[done156] #[hint0,hint226,hint16,hint2,hint14,hint10,hint25,hint23,hint39,hint1,hint231,hint36,hint8,hint46,hint3,hint52,hint55,hint119,hint62,hint225,hint20,hint24,hint26,hint227,hint229,hint35,hint50,hint48,hint13,hint215,hint223,hint71] [0xffffffff,0xaa00aa00aa00aa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xffff0000ffff0000] 0x1df1f9dde6c7a000000000000000000000000000000000000000000000000001af381b129000000000000000000000000000000000000000074e17730e71d8d51a4e7000000000000000000000000000000731f474c841c8511a484741ef71c84000000000000000000001b1ac1aca51a5491a0a519c27198a5190a4188210000000000 5 6 2 (by decide +kernel)
def done159 : Closed := closeBank chartAt #[done55,done146,done151,done157,done158] #[hint0,hint14,hint23,hint3,hint52,hint55,hint1,hint2,hint119,hint16,hint62,hint225,hint20,hint8,hint226,hint22,hint10,hint24,hint25,hint26,hint227,hint228,hint229,hint35,hint36,hint230,hint39,hint231,hint45,hint46,hint71,hint13,hint72,hint134,hint135,hint136] [0xaa00aa00aa00aa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xffff0000ffff0000,0xffffffff00000000] 0x1e30e21e10e07de0000000000000000000000000000000000000000000000000000000000001dd61c1d034d0000000000000000000000000000000000000000000000001db6991d01861d85d61cd1860000000000000000000000000000000000001ce4951d00820cb1540cd0821d34911c60820000000000000000000000001d024f1ce0410cd10c0cb0411ca2481c60410c51040c2041000000000000 6 6 3 (by decide +kernel)
def done160 : Closed := closeBank chartAt #[done156] #[hint0,hint431,hint317,hint214,hint2,hint186,hint193,hint442,hint368,hint247,hint241,hint196,hint208,hint185,hint432,hint433,hint434,hint435,hint318,hint436,hint206,hint443,hint370,hint262,hint183,hint263,hint3,hint312,hint437,hint71,hint13,hint444,hint445,hint365,hint366,hint446,hint447,hint440,hint441,hint167,hint166,hint234,hint170,hint173,hint175] [0xffffffff,0xffff0000ffff,0xff00ff00ff00ff,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0] 0x12c6ab7aa1296a81270000000000000000000000000000000000000000000000000000000000000000000000001263a511345100000000000000000000000000000000000000000000000000000000000012432311334d6a266169134d00000000000000000000000000000000000000000000000011325312028a1115d111f28a10d28d10479d0000000000000000000000000000000000001130d311c14569161169b14568d14d69961810a14a11759500000000000000000000000011351311218611140f10e18610d18d10c2cb10a18a109207105185103081000000000000 6 7 1 (by decide +kernel)
def done161 : Closed := closeBank chartAt #[done157,done160] #[hint0,hint41,hint42,hint7,hint2,hint6,hint8,hint19,hint52,hint3,hint14,hint55,hint23,hint35,hint1,hint36,hint46,hint10,hint71,hint13,hint28,hint32,hint33,hint44,hint12,hint53,hint15,hint16,hint17,hint21,hint22,hint24,hint25,hint26,hint30,hint38,hint39,hint40,hint50,hint51,hint253,hint188,hint204,hint72] [0xffff0000ffff,0xff00ff00ff00ff,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xffffffff00000000] 0x12b12a2694e812726600000000000000000000000000000000000000000000000000000000000000000000000012592311138e00000000000000000000000000000000000000000000000000000000000011d82211130c12181f10e30c0000000000000000000000000000000000000000000000001116de11d28a11c6da10e28a25921824c28a00000000000000000000000000000000000011159111714510e58e11514510c0cc11414510a14a1044d20000000000000000000000001113d111018610e3ce10d18624c1cc24b18624a18a2481c7105185103081000000000000 6 7 2 (by decide +kernel)
def done162 : Closed := closeBank chartAt #[done158,done160] #[hint0,hint43,hint44,hint33,hint2,hint6,hint10,hint21,hint16,hint14,hint25,hint23,hint39,hint1,hint40,hint36,hint8,hint46,hint71,hint13,hint28,hint7,hint32,hint42,hint3,hint12,hint52,hint53,hint15,hint17,hint19,hint20,hint24,hint26,hint29,hint55,hint34,hint35,hint50,hint49,hint48,hint215,hint223,hint72] [0xffffffff,0xff00ff00ff00ff,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xffff0000ffff0000] 0x62b12a6294e812712600000000000000000000000000000000000000000000000000000000000000000000000010f96411034d00000000000000000000000000000000000000000000000000000000000061e8e26102cb1212a010d2cb00000000000000000000000000000000000000000000000061069f61e24911d21c10d24961b69960b24900000000000000000000000000000000000011055011714510d0cd11614510b54b1141451091491044d200000000000000000000000011045010f18610d38d10c18610b1cb10a1861091891081c7105185103081000000000000 6 7 2 (by decide +kernel)
def done163 : Closed := closeBank chartAt #[done135,done140,done147,done152,done159,done161,done162] #[hint0,hint136,hint13,hint2,hint14,hint6,hint28,hint23,hint7,hint32,hint1,hint33,hint42,hint8,hint44,hint10,hint3,hint12,hint52,hint53,hint15,hint16,hint17,hint19,hint20,hint21,hint22,hint24,hint25,hint26,hint29,hint55,hint30,hint34,hint35,hint36,hint38,hint39,hint40,hint45,hint46,hint71,hint72,hint134,hint135,hint137,hint138] [0xff00ff00ff00ff,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xffff0000ffff0000,0xffffffff00000000] 0xee42d0ec42b0aa0e90000000000000000000000000000000000000000000000000000000000000000000000000e88e70cf34d0000000000000000000000000000000000000000000000000000000000000e69640cf28a0e38a10cd28a0000000000000000000000000000000000000000000000000d97200cf1c74177de40d1c70dd71b0ca1c70000000000000000000000000000000000000cf55a0d910440d4984171040d65540ca1044134914071040000000000000000000000000cf2cf0ce1450cd20d0cc1450ca2ca0c91450c72070c61450c41440c3081000000000000 6 7 3 (by decide +kernel)
def done164 : Closed := closeBank chartAt #[done141,done160] #[hint0,hint45,hint46,hint36,hint2,hint8,hint10,hint21,hint16,hint14,hint25,hint23,hint39,hint1,hint40,hint33,hint6,hint44,hint19,hint52,hint3,hint55,hint35,hint7,hint42,hint12,hint53,hint15,hint17,hint18,hint24,hint26,hint27,hint28,hint31,hint32,hint51,hint49,hint71,hint13,hint254,hint267,hint72] [0xffffffff,0xffff0000ffff,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00] 0x12a1295289e652512400000000000000000000000000000000000000000000000000000000000000000000000010f8e211034d0000000000000000000000000000000000000000000000000000000000001178601102cb11f29e10d2cb00000000000000000000000000000000000000000000000011011d10424911c21b10d24951a4d950b24900000000000000000000000000000000000011061011714510d0cd11614550b48b51514550914951349200000000000000000000000011045010f18610d38d10c18610b1cb10a1861091891081c7105185103081000000000000 6 7 2 (by decide +kernel)
def done165 : Closed := closeBank chartAt #[done135,done142,done148,done153,done161,done164] #[hint0,hint19,hint52,hint3,hint14,hint8,hint55,hint23,hint35,hint2,hint1,hint36,hint7,hint6,hint42,hint46,hint10,hint12,hint53,hint15,hint16,hint17,hint18,hint21,hint22,hint24,hint25,hint26,hint27,hint28,hint30,hint31,hint32,hint33,hint38,hint39,hint40,hint43,hint44,hint71,hint72,hint13,hint134,hint135,hint136,hint137] [0xffff0000ffff,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffffff00000000] 0x26d26c26b0eaa680e700000000000000000000000000000000000000000000000000000000000000000000000026686525034d0000000000000000000000000000000000000000000000000000000000002648e225028a26181f24d28a00000000000000000000000000000000000000000000000025769e2501c724c75c24d1c725b69924a1c700000000000000000000000000000000000025051825710424d25624910425551324a1040d20910c71040000000000000000000000002502d024f14524d38d24c14524a2ca2481450c70470c61450c41440c2041000000000000 6 7 3 (by decide +kernel)
def done166 : Closed := closeBank chartAt #[done135,done143,done149,done154,done162,done164] #[hint0,hint21,hint16,hint2,hint14,hint10,hint25,hint23,hint39,hint1,hint40,hint33,hint6,hint44,hint36,hint8,hint46,hint3,hint12,hint52,hint53,hint15,hint17,hint18,hint19,hint20,hint24,hint26,hint27,hint28,hint7,hint29,hint55,hint31,hint32,hint34,hint35,hint41,hint42,hint71,hint72,hint13,hint134,hint135,hint136,hint137] [0xffffffff,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000] 0x46d0ec0eb46aa680e70000000000000000000000000000000000000000000000000000000000000000000000000e67a50cf30c0000000000000000000000000000000000000000000000000000000000000ce9230cf2490cb8a10cc24900000000000000000000000000000000000000000000000045881f44f1c70de75c0cc1c70db19a0c91c700000000000000000000000000000000000044f4d94581040cc0d70c31040d60950c91044544d24471040000000000000000000000000cf40f0ce1450cc34c0cb1450c92890c81450c70470c61450c41440c2041000000000000 6 7 3 (by decide +kernel)
def done167 : Closed := closeBank chartAt #[done144,done150,done155,done163,done165,done166] #[hint0,hint14,hint23,hint3,hint12,hint52,hint53,hint1,hint2,hint15,hint16,hint17,hint18,hint6,hint19,hint20,hint8,hint21,hint22,hint10,hint24,hint25,hint26,hint27,hint28,hint7,hint29,hint55,hint30,hint31,hint32,hint33,hint34,hint35,hint36,hint38,hint39,hint40,hint41,hint42,hint43,hint44,hint45,hint46,hint71,hint13,hint72,hint134,hint135,hint136,hint137] [0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000] 0x2320f123022f0eeb6c00000000000000000000000000000000000000000000000000000000000000000000000022b8aa2134100000000000000000000000000000000000000000000000000000000000002297e821334d22766621034d0000000000000000000000000000000000000000000000002259232131c72228602101c721f79d20d1c700000000000000000000000000000000000021155c2130820ce6da0d008221961720d0822165542070820000000000000000000000002132922110410d014f0ce04120d20c20804120b2892070410c61440c2041000000000000 6 7 4 (by decide +kernel)

theorem total_gate_count (gs : List Gate) :
    gs.countP (fun g => !isNot g)+gs.countP isNot=gs.length := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    cases e : isNot g <;> simp [List.countP_cons,e] at * <;> omega
theorem root6 : within target 5 6 inputs.toFinset := face_sound (c:=chart0) (by decide +kernel)
theorem root5 : within target 6 5 inputs.toFinset := face_sound (c:=chart0) (by decide +kernel)
theorem lower : ¬PEqualNP.MetaComplexity.HasCircuitSize 6 targetFn 11 := by
  rintro ⟨C,fit,small,ev⟩
  obtain ⟨k,n,hk,hn,r⟩ := initial C fit ev
  have len := total_gate_count C.gates
  change C.gates.length≤11 at small
  have card : inputs.toFinset.card=6 := by decide +kernel
  have ww := paid_width r
  rw [card] at ww
  have needs := two_not C fit ev
  have actualTwo : 2≤n := by
    by_contra z
    exact one_ord (i:=1) (j:=9) (l:=11) (m:=27) r (by omega)
      (ord_check (by decide +kernel)) (ord_check (by decide +kernel)) (ord_check (by decide +kernel))
      (by unfold Moves; decide +kernel) (by unfold Moves; decide +kernel)
  have cases' : n=2 ∨ n=3 ∨ n=4 ∨ n=5 ∨ n=6 := by omega
  rcases cases' with rfl|rfl|rfl|rfl|rfl
  · have b : within target 9 2 inputs.toFinset := done46.bad
    exact b k (by omega) _ (by omega) r
  · have b : within target 8 3 inputs.toFinset := done126.bad
    exact b k (by omega) _ (by omega) r
  · have b : within target 7 4 inputs.toFinset := done167.bad
    exact b k (by omega) _ (by omega) r
  · exact root5 k (by omega) _ (by omega) r
  · exact root6 k (by omega) _ (by omega) r

end PEqualNP.Outside.L_meta_9929.LB

theorem PEqualNP.Outside.L_meta_9929_Negation : ¬ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => decide ((1 * (x 3).toNat + 2 * (x 4).toNat + 4 * (x 5).toNat) < (1 * (x 0).toNat + 2 * (x 1).toNat + 4 * (x 2).toNat))) 11) :=
  PEqualNP.Outside.L_meta_9929.LB.lower

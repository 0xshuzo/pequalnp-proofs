import PEqualNP.Defs
-- The two-mode live-state and cofactor checker follows L_meta_1674 and L_meta_670.
-- The truth table, restrictions and search certificates below are instance-specific.
-- Shared forest and cofactor certificates from L_meta_1674 and PR 11111 for L_meta_1677.
-- The original credit line is retained below.
-- The checker and the bound certificates are adapted from PEqualNP/Outside/L_meta_1667.lean (Apache-2.0).
-- Two modes: u=false are monotone runs (AND, OR); u=true are runs up to complement, where negation is free.
namespace PEqualNP.Outside.L_meta_43634
open PEqualNP.CircuitLowerBounds
def nat80 (xs : List Nat) : Nat := xs.foldl (fun a n => (a <<< 80) + n) 0
def seg80 {n : Nat} (xs : List Nat) : BitVec n := BitVec.ofNat n (nat80 xs)
abbrev Sig := BitVec 512
def zero : Sig := 0
def one : Sig := BitVec.allOnes 512
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
def bit (i : Fin 512) (a : Sig) : Bool := a.getLsbD i.val
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
-- Remove a last computed signal from a backward derivation. A gate whose value
-- is already available, or is unused by the suffix, needs no entry in the plan.
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
abbrev Wire (R : Type) := R → Bool
def inv {R} (a : Wire R) : Wire R := fun r => !(a r)
def combine {R} (isOr : Bool) (a b : Wire R) : Wire R :=
  if isOr then fun r => a r || b r else fun r => a r && b r
def comb {R} (d : Nat) (a b : Wire R) : Wire R :=
  if d=0 then combine false a b else if d=1 then combine true a b else
    if d=2 then combine false a (inv b) else combine false (inv a) b
def Constant {R} (a : Wire R) : Prop := ∃ b : Bool, a = fun _ => b
noncomputable def cost {R} (a : Wire R) : Nat := by
  classical exact if Constant a then 1 else 0
noncomputable def mass {R} (xs : List (Wire R)) : Nat := (xs.map cost).sum
def Available {R} (u : Bool) (pool : List (Wire R)) (v : Wire R) : Prop :=
  v ∈ pool ∨ Constant v ∨ (u=true ∧ inv v ∈ pool)
def supply {R} (u : Bool) (pool xs : List (Wire R)) := ∀ a ∈ xs, Available u pool a
def Reach {R} (u : Bool) (roots : List (Wire R)) : Nat → List (Wire R) → Prop
  | 0,b => b=roots
  | p+1,c => ∃ (op : Bool) (bank : List (Wire R)) (a b : Wire R), Reach u roots p bank ∧ Available u bank a ∧
      Available u bank b ∧ c=combine op a b :: bank
theorem Reach.start {R u} {roots : List (Wire R)} : Reach u roots 0 roots := rfl
theorem Reach.two {R u} {roots : List (Wire R)} {p bank a b} (op : Bool) (h : Reach u roots p bank)
    (ha : Available u bank a) (hb : Available u bank b) : Reach u roots (p+1) (combine op a b :: bank) :=
  ⟨op,bank,a,b,h,ha,hb,rfl⟩
theorem Reach.ind {R u} {roots : List (Wire R)} {motive : ∀ p bank, Reach u roots p bank → Prop}
    (start : motive 0 roots Reach.start)
    (two : ∀ {p bank a b} (op : Bool) (h : Reach u roots p bank) (ha : Available u bank a)
      (hb : Available u bank b), motive p bank h →
      motive (p+1) (combine op a b :: bank) (Reach.two op h ha hb))
    {p bank} (h : Reach u roots p bank) : motive p bank h := by
  induction p generalizing bank with
  | zero =>
    obtain rfl := h
    exact start
  | succ p ih =>
    obtain ⟨op,bank,a,b,h,ha,hb,rfl⟩ := h
    exact two op h ha hb (ih h)
def kept {α : Type} (save : Bool) (x : α) (xs : List α) := if save then x::xs else xs
def Run {R} (u : Bool) (goal : Wire R) : Nat → List (Wire R) → Prop
  | 0,zs => List.Perm [goal] zs
  | s+1,zs => ∃ (op : Nat) (ka kb : Bool) (a b : Wire R) (rest : List (Wire R)), allowed u op ∧ (a::b::rest).Perm zs ∧
      Run u goal s (comb op a b :: kept ka a (kept kb b rest))
theorem Run.stop {R u} {goal : Wire R} : Run u goal 0 [goal] := List.Perm.refl _
theorem Run.perm {R u} {goal : Wire R} {s : Nat} {xs zs : List (Wire R)} (p : xs.Perm zs)
    (h : Run u goal s xs) : Run u goal s zs := by
  cases s with
  | zero => exact List.Perm.trans h p
  | succ s =>
    obtain ⟨op,ka,kb,a,b,rest,hd,q,h⟩ := h
    exact ⟨op,ka,kb,a,b,rest,hd,q.trans p,h⟩
theorem Run.two {R u} {goal : Wire R} {s : Nat} {a b : Wire R} {rest : List (Wire R)} (op : Nat) (hd : allowed u op) (ka kb : Bool)
    (h : Run u goal s (comb op a b :: kept ka a (kept kb b rest))) : Run u goal (s+1) (a::b::rest) :=
  ⟨op,ka,kb,a,b,rest,hd,List.Perm.refl _,h⟩
theorem Run.ind {R u} {goal : Wire R} {motive : ∀ s ws, Run u goal s ws → Prop}
    (stop : motive 0 [goal] Run.stop)
    (perm : ∀ {s xs zs} (p : List.Perm xs zs) (h : Run u goal s xs), motive s xs h → motive s zs (Run.perm p h))
    (two : ∀ {s a b rest} (op : Nat) (hd : allowed u op) (ka kb : Bool) (h : Run u goal s (comb op a b :: kept ka a (kept kb b rest))),
      motive s _ h → motive (s+1) (a::b::rest) (Run.two op hd ka kb h))
    {s ws} (h : Run u goal s ws) : motive s ws h := by
  induction s generalizing ws with
  | zero => exact perm h Run.stop stop
  | succ s ih =>
    obtain ⟨op,ka,kb,a,b,rest,hd,p,h⟩ := h
    exact perm p (Run.two op hd ka kb h) (two op hd ka kb h (ih h))
theorem mass_cons {R} (a : Wire R) (xs) : mass (a::xs)=cost a + mass xs := by
  simp [mass]
theorem mass_kept {R} (a : Wire R) (xs) (k : Bool) : mass xs ≤ mass (kept k a xs) := by
  cases k <;> simp [kept,mass_cons]
theorem inv_constant {R} {a : Wire R} (h : Constant a) : Constant (inv a) := by
  obtain ⟨v,rfl⟩ := h
  exact ⟨!v,rfl⟩
theorem inv_inv' {R} (a : Wire R) : inv (inv a)=a := by
  funext r
  simp [inv]
theorem cost_inv {R} (a : Wire R) : cost (inv a)=cost a := by
  have : Constant (inv a) ↔ Constant a := ⟨fun h => inv_inv' a ▸ inv_constant h,inv_constant⟩
  by_cases h : Constant a
  · simp only [cost,if_pos h,if_pos (this.mpr h)]
  · simp only [cost,if_neg h,if_neg (fun x => h (this.mp x))]
theorem avail_inv {R u} {bank : List (Wire R)} {a} (hu : u=true) (h : Available u bank a) : Available u bank (inv a) := by
  rcases h with h | h | ⟨_,h⟩
  · exact Or.inr (Or.inr ⟨hu,(inv_inv' a).symm ▸ h⟩)
  · exact Or.inr (Or.inl (inv_constant h))
  · exact Or.inl h
theorem both_constant {R} {a b : Wire R} (op) (h : Constant a) (g : Constant b) :
    Constant (combine op a b) := by
  obtain ⟨v,rfl⟩ := h
  obtain ⟨w,rfl⟩ := g
  cases op <;> exact ⟨_,rfl⟩
theorem from_constant {R u} (op) {a b : Wire R} {bank}
    (h : Constant a ∨ Constant b) (ha : Available u bank a) (hb : Available u bank b) :
    Available u bank (combine op a b) := by
  rcases h with ⟨v,rfl⟩ | ⟨v,rfl⟩
  · cases op <;> cases v
    · exact Or.inr (Or.inl ⟨false, by funext x; simp [combine]⟩)
    · simpa [combine] using hb
    · simpa [combine] using hb
    · exact Or.inr (Or.inl ⟨true, by funext x; simp [combine]⟩)
  · cases op <;> cases v
    · exact Or.inr (Or.inl ⟨false, by funext x; simp [combine]⟩)
    · simpa [combine] using ha
    · simpa [combine] using ha
    · exact Or.inr (Or.inl ⟨true, by funext x; simp [combine]⟩)
theorem available_cons {R u} {bank v} (w : Wire R) (h : Available u bank v) :
    Available u (w::bank) v :=
  h.imp (List.mem_cons_of_mem _) (Or.imp id (And.imp id (List.mem_cons_of_mem _)))
theorem extend_two {R u} (roots : List (Wire R)) {p bank a b} (op) (hp : Reach u roots p bank)
    (ha : Available u bank a) (hb : Available u bank b) :
    ∃ q next, Reach u roots q next ∧ Available u next (combine op a b) ∧
        (∀ v, Available u bank v → Available u next v) ∧
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
theorem comb_prime {R u} {bank : List (Wire R)} {d a b} (hd : allowed u d) (ha : Available u bank a) (hb : Available u bank b) :
    ∃ op x y, comb d a b=combine op x y ∧ Available u bank x ∧ Available u bank y ∧ cost x=cost a ∧ cost y=cost b := by
  rcases allowed_four hd with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
  · exact ⟨false,a,b,rfl,ha,hb,rfl,rfl⟩
  · exact ⟨true,a,b,rfl,ha,hb,rfl,rfl⟩
  · exact ⟨false,a,inv b,rfl,ha,avail_inv hu hb,rfl,cost_inv b⟩
  · exact ⟨false,inv a,b,rfl,avail_inv hu ha,hb,cost_inv a,rfl⟩
theorem extend_comb {R u} (roots : List (Wire R)) {p bank a b} (d) (hd : allowed u d) (hp : Reach u roots p bank)
    (ha : Available u bank a) (hb : Available u bank b) :
    ∃ q next, Reach u roots q next ∧ Available u next (comb d a b) ∧
        (∀ v, Available u bank v → Available u next v) ∧
        q+cost a+cost b ≤ p+1+cost (comb d a b) := by
  obtain ⟨op,x,y,e,hx,hy,cx,cy⟩ := comb_prime hd ha hb
  rw [e,←cx,←cy]
  exact extend_two roots op hp hx hy
theorem mem_kept {α : Type} {k : Bool} {x a : α} {xs} (h : x ∈ kept k a xs) :
    x=a ∨ x∈xs := by cases k <;> simp_all [kept]
theorem contraction {R u} {goal : Wire R} (nc : ¬Constant goal) {s ws}
    (h : Run u goal s ws) (roots : List (Wire R)) {p bank}
    (hp : Reach u roots p bank) (hs : supply u bank ws) :
    ∃ q next, Reach u roots q next ∧ Available u next goal ∧ q+mass ws ≤ p+s := by
  classical
  induction h using Run.ind generalizing p bank with
  | stop =>
    exact ⟨p,bank,hp,hs _ (by simp),by simp [mass,cost,nc]⟩
  | perm eq _ ih =>
    have hsub : supply u bank _ := fun v hv => hs v (eq.mem_iff.mp hv)
    obtain ⟨q,W,hW,hv,hl⟩ := ih hp hsub
    exact ⟨q,W,hW,hv,by simpa only [mass,←(eq.map cost).sum_eq] using hl⟩
  | @two s a b rest op hd ka kb _ ih =>
    obtain ⟨r,T,hT,hz,inc,le⟩ := extend_comb roots op hd hp (hs a (by simp)) (hs b (by simp))
    have ht : supply u T (comb op a b :: kept ka a (kept kb b rest)) := by
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
theorem restrict_comb {R S : Type} (rows : S → R) (d) (a b : Wire R) :
    restrictRows rows (comb d a b) = comb d (restrictRows rows a) (restrictRows rows b) := by
  unfold comb
  split_ifs <;> rfl
theorem restrict_run {R S : Type} {u} (rows : S → R) {goal s ws} (h : Run u goal s ws) :
    Run u (restrictRows rows goal) s (ws.map (restrictRows rows)) := by
  induction h using Run.ind with
  | stop => exact Run.stop
  | perm p _ ih => exact Run.perm (p.map _) ih
  | two op hd ka kb _ ih =>
    simp only [List.map_cons,restrict_kept,restrict_comb] at ih ⊢
    exact Run.two op hd ka kb ih
theorem projected_bound {R S : Type} {u} (rows : S → R) {goal s ws} (h : Run u goal s ws)
    (nc : ¬Constant (restrictRows rows goal)) {roots : List (Wire S)} {p bank L}
    (hp : Reach u roots p bank) (hs : supply u bank (ws.map (restrictRows rows)))
    (hl : ∀ q bs, Reach u roots q bs → Available u bs (restrictRows rows goal) → L ≤ q) :
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
theorem obs_bin (d : Nat) (a b : Sig) :
    observe (bin d a b) = comb d (observe a) (observe b) := by
  funext r
  simp only [observe,bit_bin,comb]
  split_ifs <;> rfl
theorem map_kept {α β : Type} (f : α → β) (d : Bool) (a : α) (l : List α) :
    (kept d a l).map f = kept d (f a) (l.map f) := by cases d <;> rfl
theorem kept_nd {α : Type} (k : Bool) (a : α) (l : List α)
    (hn : l.Nodup) (ha : a ∉ l) : (kept k a l).Nodup := by cases k <;> simp [kept,hn,ha]
theorem kept_fin (k : Bool) (a : Sig) (l : List Sig) :
    (kept k a l).toFinset = if k then insert a l.toFinset else l.toFinset := by
  cases k <;> simp [kept]
theorem list_run {u} {T : Sig} {k S} (h : Live u T k S) (v : List Sig)
    (hv : v.Nodup) (eqv : v.toFinset = S) : Run u (observe T) k (v.map observe) := by
  classical
  induction h using Live.ind generalizing v with
  | stop hp =>
    have eq : [T].Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp) hv
      simpa [eqv]
    exact Run.perm (eq.map _) Run.stop
  | @binary k U a b d hd ha hb hab fresh _ ih =>
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
    change Run _ _ _ ((bin d a b::kept ka a (kept kb b rest)).map observe) at progress
    rw [List.map_cons,map_kept,map_kept,obs_bin] at progress
    have perm : (a::b::rest).Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp [hab,ar,br,hr]) hv
      ext j
      by_cases ja : j=a <;> by_cases jb : j=b <;> simp_all [er]
    exact Run.perm (perm.map _) (Run.two d hd ka kb progress)
theorem table_inv (f : Wire Row) : table (inv f) = neg (table f) := by
  rw [←table_observe (neg (table f)),obs_neg,observe_table]
theorem table_prime (d : Bool) (f g : Wire Row) :
    table (combine d f g) = prime d (table f) (table g) := by
  apply bit_ext
  intro r
  rw [bit_table,bit_prime,bit_table,bit_table]
  cases d <;> rfl
theorem available_rep {u} {bank : List (Wire Row)} {a} (h : Available u bank a) :
    Repr u ((bank.map table).map (nrm u)) (table a) := by
  rcases h with hm | ⟨b,rfl⟩ | ⟨rfl,hm⟩
  · exact Or.inl (List.mem_map_of_mem (List.mem_map_of_mem hm))
  · apply repr_const
    cases b
    · exact Or.inl (bit_ext fun i => (bit_table _ i).trans (bit_zero i).symm)
    · exact Or.inr (bit_ext fun i => (bit_table _ i).trans (bit_one i).symm)
  · have := table_inv a
    refine Or.inl ?_
    rw [←nrm_neg,←this]
    exact List.mem_map_of_mem (List.mem_map_of_mem hm)
theorem reach_live_sub {u} {roots : List (Wire Row)} {p bank}
    (h : Reach u roots p bank) {T k S} (run : Live u T k S)
    (sub : ∀ a ∈ S, a ∈ (bank.map table).map (nrm u)) :
    ∃ l V, l ≤ p+k ∧ Live u T l V ∧ ∀ a ∈ V, a ∈ (roots.map table).map (nrm u) := by
  induction h using Reach.ind generalizing k S with
  | start => exact ⟨k,S,by omega,run,sub⟩
  | @two p bank a b d h ha hb ih =>
    rw [List.map_cons,List.map_cons,table_prime] at sub
    have rep := prime_rep d (available_rep ha) (available_rep hb)
    obtain ⟨k',S',hk,run',sub'⟩ := pull_gate (c:=1) run (rep.imp id (fun h => ⟨rfl,h⟩))
      (fun a hm => by simpa [or_comm] using sub a hm)
    obtain ⟨l,V,hl,hr,hs⟩ := ih run' sub'
    exact ⟨l,V,by omega,hr,hs⟩
def plainWord (a : Sig) : Bool := !(bit 0 a)
theorem nrm_map {u} {w : List Sig} (h : w.all plainWord=true) : w.map (nrm u)=w := by
  have e : w.map (nrm u) = w.map id := by
    apply List.map_congr_left
    intro a ha
    exact nrm_id (by simpa [plainWord] using List.all_eq_true.mp h a ha)
  rw [e,List.map_id]
theorem reach_live {u} {roots : List Sig} {p bank T} (hp : proper T) (nT : plainWord T=true) (nR : roots.all plainWord=true)
    (h : Reach u (roots.map observe) p bank) (hit : Available u bank (observe T)) :
    ∃ k S, k ≤ p ∧ Live u T k S ∧ ∀ a ∈ S, a ∈ roots := by
  have hm := available_rep hit
  rw [table_observe] at hm
  unfold Repr at hm
  rw [nrm_id (by simpa [plainWord] using nT)] at hm
  have mem := hm.resolve_right (fun hn => hn hp)
  obtain ⟨l,V,hl,hr,hs⟩ := reach_live_sub h (Live.stop hp) (by simpa using mem)
  refine ⟨l,V,by omega,hr,?_⟩
  have e : (roots.map observe).map table = roots := by simp [List.map_map,Function.comp_def,table_observe]
  rw [e,nrm_map nR] at hs
  exact hs
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
theorem raw_required {u T k S} (h : Live u T k S) (roots : List Sig) (a : Sig)
    (sub : ∀ v ∈ S, v ∈ roots) (r s : Row) (diff : bit r T ≠ bit s T)
    (isolated : ∀ v ∈ roots, v ≠ a → bit r v = bit s v) : a ∈ S := by
  obtain ⟨v,hv,hd⟩ := live_row_difference h diff
  by_cases veq : v=a
  · simpa [veq] using hv
  · exact False.elim (hd (isolated v (sub v hv) veq))
def inputs : List Sig := [(seg80 [0xaaaaaaaa,0xaaaaaaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaaaaaaa]),(seg80 [0xcccccccc,0xcccccccccccccccccccc,0xcccccccccccccccccccc,0xcccccccccccccccccccc,0xcccccccccccccccccccc,0xcccccccccccccccccccc,0xcccccccccccccccccccc]),(seg80 [0xf0f0f0f0,0xf0f0f0f0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f0f0f0]),(seg80 [0xff00ff00,0xff00ff00ff00ff00ff00,0xff00ff00ff00ff00ff00,0xff00ff00ff00ff00ff00,0xff00ff00ff00ff00ff00,0xff00ff00ff00ff00ff00,0xff00ff00ff00ff00ff00]),(seg80 [0xffff0000,0xffff0000ffff0000ffff,0xffff0000ffff0000,0xffff0000ffff0000ffff,0xffff0000ffff0000,0xffff0000ffff0000ffff,0xffff0000ffff0000]),(seg80 [0xffffffff,0xffffffff0000,0xffffffff00000000,0xffffffff00000000ffff,0xffff00000000ffffffff,0xffffffff0000,0xffffffff00000000]),(seg80 [0xffffffff,0xffffffff000000000000,0xffffffffffffffff,65535,0xffffffffffff00000000,0xffffffffffff,0xffff0000000000000000]),(seg80 [0xffffffff,0xffffffffffffffffffff,0xffff0000000000000000,65535,0xffffffffffffffffffff,0xffffffff000000000000,0]),(seg80 [0xffffffff,0xffffffffffffffffffff,0xffffffffffffffffffff,0xffffffffffffffff0000,0,0,0])]
def graph : Sig := (seg80 [0xfeeaeee0,0xeeeae8c0feeaeee0eeea,0xe8c0feeaeee0eeeae8c0,0xfeeaeee0eeeae8c0feea,0xeee0eeeae8c0feeaeee0,0xeeeae8c0feeaeee0eeea,0xe8c0feeaeee0eeeae8c0])
def sample (r : Row) (j : Fin 9) := bit r (inputs.getD j.val zero)
def edge (x : Fin 9 → Bool) : Bool :=
  (x 1 && x 2) || (x 0 && x 1 && x 3) || (x 0 && x 2 && x 3) || (x 0 && x 4) || (x 1 && x 3 && x 4) || (x 0 && x 2 && x 5) || (x 0 && x 3 && x 5) || (x 1 && x 3 && x 5) || (x 2 && x 3 && x 4 && x 5)
theorem edge_table : ∀ r : Row, bit r graph = edge (sample r) := by decide +kernel
theorem graph_proper : proper graph := by unfold proper; decide +kernel
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
def rename (f : Row → Row) (a : Sig) := table fun r => bit (f r) a
theorem bit_rename (f : Row → Row) (a : Sig) (r : Row) :
    bit r (rename f a) = bit (f r) a := bit_table _ _
theorem observe_rename (f : Row → Row) (a : Sig) :
    observe (rename f a) = restrictRows f (observe a) := by funext r; exact bit_rename f a r
theorem rename_bin (f : Row → Row) (d : Nat) (a b : Sig) :
    rename f (bin d a b) = bin d (rename f a) (rename f b) := by
  apply bit_ext
  intro r
  simp only [bit_rename,bit_bin]
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
theorem live_rename {u T k S} (h : Live u T k S) (f : Row → Row) (onto : Function.Surjective f) :
    Live u (rename f T) k (S.image (rename f)) := by
  have inj := rename_inj f onto
  obtain ⟨fz,fo⟩ := rename_constants f
  have pp (v) (p : proper v) : proper (rename f v) :=
    ⟨fun e => p.1 (inj (e.trans fz.symm)),fun e => p.2 (inj (e.trans fo.symm))⟩
  induction h using Live.ind with
  | stop hp => simpa using Live.stop (pp _ hp)
  | @binary k U a b d hd ha hb hab hf _ ih =>
    have fresh : rename f (bin d a b) ∉ (insert a (insert b U)).image (rename f) := by
      intro hm
      obtain ⟨v,hv,eq⟩ := Finset.mem_image.mp hm
      exact hf (inj eq ▸ hv)
    simp only [Finset.image_insert,rename_bin] at fresh ih ⊢
    exact Live.binary hd (pp _ ha) (pp _ hb) (fun hh => hab (inj hh)) fresh ih
theorem mono_row_difference {u T k S} (h : Live u T k S) (none : u=false) {r s : Row}
    (pos : bit r T = true) (negRow : bit s T = false) :
    ∃ a ∈ S, bit r a = true ∧ bit s a = false := by
  induction h using Live.ind with
  | stop hp => exact ⟨_,by simp,pos,negRow⟩
  | @binary k U a b d hd ha hb hab hf _ ih =>
    obtain ⟨v,hv,hp,hn⟩ := ih
    rcases Finset.mem_insert.mp hv with rfl | hu
    · rw [bit_bin] at hp hn
      subst none
      rcases allowed_four hd with rfl | rfl | ⟨h,_⟩ | ⟨h,_⟩
      · cases p : bit r a <;> cases q : bit s a <;> cases u : bit r b <;> cases z : bit s b <;> simp_all
      · cases p : bit r a <;> cases q : bit s a <;> cases u : bit r b <;> cases z : bit s b <;> simp_all
      · exact Bool.noConfusion h
      · exact Bool.noConfusion h
    · exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu),hp,hn⟩
def Lower (u : Bool) (roots : List Sig) (T : Sig) (L : Nat) : Prop :=
  ∀ p bank, Reach u (roots.map observe) p bank → Available u bank (observe T) → L ≤ p
theorem reach_up {R u} {roots : List (Wire R)} {p bank} (h : Reach false roots p bank) : Reach u roots p bank := by
  have up {bank : List (Wire R)} {a} (h : Available false bank a) : Available u bank a :=
    h.imp id (Or.imp id (fun h => Bool.noConfusion h.1))
  induction h using Reach.ind with
  | start => exact Reach.start
  | two op h ha hb ih => exact Reach.two op ih (up ha) (up hb)
theorem lower_down {u roots T L} (h : Lower true roots T L) : Lower u roots T L := by
  cases u
  · exact fun p bank hr ha => h p bank (reach_up hr) (ha.imp id (Or.imp id (fun h => Bool.noConfusion h.1)))
  · exact h
def Impossible (u : Bool) (T : Sig) (cap : Nat) (S : Finset Sig) : Prop :=
  ∀ k, k ≤ cap → ¬Live u T k S
def Essential (T : Sig) (roots : List Sig) (a : Sig) : Prop :=
  ∃ r s : Row, bit r T ≠ bit s T ∧ ∀ v ∈ roots, v ≠ a → bit r v = bit s v
theorem lower_impossible {u roots T L} (hp : proper T) (nT : plainWord T=true) (nR : roots.all plainWord=true)
    (essential : ∀ a ∈ roots, Essential T roots a)
    (noRun : Impossible u T L roots.toFinset) : Lower u roots T (L+1) := by
  intro p bank h ha
  obtain ⟨k,S,hk,run,hs⟩ := reach_live hp nT nR h ha
  have he : roots.toFinset = S := by
    ext a
    rw [List.mem_toFinset]
    refine ⟨fun hm => ?_,hs a⟩
    obtain ⟨r,s,hd,iso⟩ := essential _ hm
    exact raw_required run roots a hs r s hd iso
  by_contra! small
  exact noRun k (by omega) (he.symm ▸ run)
theorem observe_proper {v : Sig} (hv : proper v) : ¬Constant (observe v) := by
  rintro ⟨b,h⟩
  have hr : Repr false [] v := by
    apply repr_const
    cases b
    · exact Or.inl (bit_ext fun i => (congrFun h i).trans (bit_zero i).symm)
    · exact Or.inr (bit_ext fun i => (congrFun h i).trans (bit_one i).symm)
  have hr' : represented [] v := hr
  exact (hr'.resolve_left (by simp)) hv
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
theorem lower_slice {u} {roots other : List Sig} {T G : Sig} (pT : proper T) (nT : plainWord T=true) (nR : roots.all plainWord=true) (pG : proper G)
    (r : Row → Row) (eq : rename r T = G)
    (covered : ∀ a ∈ roots, Available u (other.map observe) (observe (rename r a)))
    (singles : Finset Sig) (necessary : ∀ a ∈ singles, Essential T roots a)
    (constant : ∀ a ∈ singles, Constant (observe (rename r a)))
    (L : Nat) (prior : Lower u other G L) : Lower u roots T (L + singles.card) := by
  classical
  intro p bank hh ha
  obtain ⟨k,S,hk,run,sub⟩ := reach_live pT nT nR hh ha
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
  have supp : supply u (other.map observe) ((front.map observe).map (restrictRows r)) := by
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
theorem cover_sound {u T k S} (h : Live u T k S) {ws : List Sig} (he : ws.toFinset=S)
    {width : Nat} {r s : Fin width → Row} {sig} (correct : Sep T width r s sig)
    (oriented : Bool) (zeroNot : oriented=true → u=false) :
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
theorem cover_required {u T ws k} (h : Live u T k (List.toFinset ws)) {n : Nat} {r s : Fin n → Row} {sig}
    (correct : Sep T n r s sig) :
    covered (!u) sig ws = BitVec.allOnes n := by
  apply cover_sound h rfl correct
  simp
def Slice (u : Bool) (raw : List Sig) (T d : Sig) (L : Nat) : Prop :=
  ∃ (f : Row → Row) (roots : List Sig), (∀ r, bit (f r) d = true) ∧
    (∀ a ∈ raw, Available u (roots.map observe) (restrictRows f (observe a))) ∧
    ¬Constant (restrictRows f (observe T)) ∧
    ∀ p bank, Reach u (roots.map observe) p bank → Available u bank (restrictRows f (observe T)) → L ≤ p
def masked (d a : Sig) := a &&& d
def availableB (u : Bool) (d : Sig) (pool : List Sig) (a : Sig) :=
  let m := masked d a
  m == zero || m == d || (pool.map (masked d)).any (fun v => v==m) ||
    (u && (let c := masked d (neg a); (pool.map (masked d)).any (fun v => v==c)))
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
def poolSupply (u : Bool) (f : Row → Row) (bank : List (Wire Row)) (pool : List Sig) :=
  ∀ a ∈ pool, Available u bank (restrictRows f (observe a))
theorem availableB_sound {u} {f : Row → Row} {d a : Sig} {bank pool}
    (dom : ∀ r, bit (f r) d = true) (supplyB : poolSupply u f bank pool)
    (check : availableB u d pool a = true) : Available u bank (restrictRows f (observe a)) := by
  simp only [availableB,List.any_map,Function.comp_def,Bool.or_eq_true,Bool.and_eq_true,beq_iff_eq,List.any_eq_true] at check
  rcases check with ((hz | ho) | ⟨v,hv,he⟩) | ⟨hu,v,hv,he⟩
  · exact Or.inr (Or.inl ⟨false,masked_zero dom hz⟩)
  · exact Or.inr (Or.inl ⟨true,masked_one dom ho⟩)
  · exact masked_eq dom he ▸ supplyB v hv
  · have h := avail_inv hu (masked_eq dom he ▸ supplyB v hv)
    rw [obs_neg] at h
    have e : inv (restrictRows f (inv (observe a))) = restrictRows f (observe a) := by
      funext r
      simp [inv,restrictRows]
    rwa [e] at h
abbrev Choice := Nat × Sig × Sig
def choiceVal (c : Choice) := bin c.1 c.2.1 c.2.2
def allowedB (u : Bool) (d : Nat) := decide (d<2) || (u && decide (d<4))
theorem allowedB_ok {u d} (h : allowedB u d=true) : allowed u d := by
  simpa [allowedB,allowed] using h
def choiceOK (u : Bool) (d : Sig) (pool : List Sig) (c : Choice) :=
  allowedB u c.1 && (availableB u d pool c.2.1 && availableB u d pool c.2.2)
theorem pay_choice {u} {f : Row → Row} {d : Sig} {roots bank pool q}
    (dom : ∀ r, bit (f r) d = true) (hp : Reach u roots q bank) (hs : poolSupply u f bank pool)
    (c : Choice) (valid : choiceOK u d pool c = true) :
    ∃ next, Reach u roots (q+1) next ∧ poolSupply u f next (choiceVal c :: pool) := by
  simp only [choiceOK,Bool.and_eq_true] at valid
  obtain ⟨op,x,y,e,hx,hy,_,_⟩ := comb_prime (allowedB_ok valid.1) (availableB_sound dom hs valid.2.1)
    (availableB_sound dom hs valid.2.2)
  refine ⟨_,Reach.two op hp hx hy,?_⟩
  intro a hm
  rcases List.mem_cons.mp hm with rfl | hm
  · rw [choiceVal,obs_bin,restrict_comb,e]
    exact Or.inl (by simp)
  · exact available_cons _ (hs _ hm)
def makePool (u : Bool) (d : Sig) (pool : List Sig) : List Choice → Option (List Sig)
  | [] => some pool
  | c::cs => if choiceOK u d pool c then makePool u d (choiceVal c::pool) cs else none
theorem makePool_sound {u} {d : Sig} {f : Row → Row} (dom : ∀ r, bit (f r) d = true)
    {roots bank q pool} (hp : Reach u roots q bank) (hs : poolSupply u f bank pool)
    (cs : List Choice) {result} (ok : makePool u d pool cs = some result) :
    ∃ next, Reach u roots (q+cs.length) next ∧ poolSupply u f next result := by
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
def poolCut (u : Bool) (d : Sig) (L k p : Nat) (pool ws : List Sig) :=
  decide (k+p < L+ws.countP (isMaskedConstant d)) && ws.all (availableB u d pool)
theorem poolCut_sound {u raw T d L} (slice : Slice u raw T d L) (cs : List Choice)
    {pool ws cap} (built : makePool u d raw cs = some pool)
    (nd : ws.Nodup) (cut : poolCut u d L cap cs.length pool ws = true) :
    Impossible u T cap ws.toFinset := by
  intro k hk h
  obtain ⟨f,roots,dom,base,nc,lo⟩ := slice
  obtain ⟨bank,hr,hs⟩ := makePool_sound dom (Reach.start (roots:=roots.map observe)) base cs built
  simp only [poolCut,Bool.and_eq_true,decide_eq_true_eq] at cut
  obtain ⟨ineq,all⟩ := cut
  have coveredS : supply u bank ((ws.map observe).map (restrictRows f)) := by
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
theorem freeWord_ok {u roots w} (ok : freeWord roots w = true) :
    Available u (roots.map observe) (observe w) := by
  simp only [freeWord,Bool.or_eq_true,beq_iff_eq,List.contains_eq_mem,decide_eq_true_eq] at ok
  rcases ok with (rfl | rfl) | hm
  · exact Or.inr (Or.inl ⟨false,funext bit_zero⟩)
  · exact Or.inr (Or.inl ⟨true,funext bit_one⟩)
  · exact Or.inl (List.mem_map_of_mem hm)
def checkMap (ms : List Move) (raw : List Sig) (T : Sig) (base : List Sig) (G : Sig) :=
  movedWord ms T == G && raw.all (fun a => freeWord base (movedWord ms a))
theorem map_correct {u ms raw T base G} (ok : checkMap ms raw T base G = true) :
    rename (movedRow ms) T = G ∧
    ∀ a ∈ raw, Available u (base.map observe) (observe (rename (movedRow ms) a)) := by
  simp only [checkMap,Bool.and_eq_true,beq_iff_eq,List.all_eq_true,moved_eq_rename] at ok
  exact ⟨ok.1,fun a ha => freeWord_ok (ok.2 a ha)⟩
theorem lower_map {u ms raw T base G L} (ok : checkMap ms raw T base G = true)
    (pT : proper T) (nT : plainWord T=true) (nR : raw.all plainWord=true) (pG : proper G)
    (hL : Lower u base G L) : Lower u raw T L := by
  obtain ⟨eq,supp⟩ := map_correct ok
  simpa using lower_slice pT nT nR pG (movedRow ms) eq supp ∅ (by simp) (by simp) L hL
theorem slice_correct {u ms raw T base G L d} (ok : checkMap ms raw T base G = true)
    (all : movedWord ms d = one) (properG : proper G) (hL : Lower u base G L) :
    Slice u raw T d L := by
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
  plainWord T && raw.all plainWord && xs.all (fun a => witnessB T raw a.1 a.2)
theorem essential_ok {T raw xs} (ok : checkEssential T raw xs = true) :
    ∀ a ∈ (xs.map Prod.fst).toFinset, Essential T raw a := by
  simp only [checkEssential,Bool.and_eq_true] at ok
  intro a ha
  obtain ⟨⟨a,r,s⟩,hm,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
  exact witnessB_sound (List.all_eq_true.mp ok.2 _ hm)
theorem essential_plain {T raw xs} (ok : checkEssential T raw xs = true) :
    plainWord T=true ∧ raw.all plainWord=true := by
  simp only [checkEssential,Bool.and_eq_true] at ok
  exact ok.1
theorem lower_count {u raw T} (properT : proper T) (xs : List (Sig × Row × Row))
    (ok : checkEssential T raw xs = true) :
    Lower u raw T ((xs.map Prod.fst).toFinset.card-1) := by
  intro p bank hr hit
  obtain ⟨k,S,hk,run,sub⟩ := reach_live properT (essential_plain ok).1 (essential_plain ok).2 hr hit
  have le : (xs.map Prod.fst).toFinset.card ≤ S.card := by
    apply Finset.card_le_card
    intro a ha
    obtain ⟨r,s,hd,iso⟩ := essential_ok ok a ha
    exact raw_required run raw a sub r s hd iso
  have bound := live_size run
  omega
def checkLift (ms : List Move) (T : Sig) (raw : List Sig) (base : List Sig) (G : Sig)
    (xs : List (Sig × Row × Row)) :=
  checkMap ms raw T base G && checkEssential T raw xs &&
    xs.all (fun a => movedWord ms a.1 == zero || movedWord ms a.1 == one)
theorem lift_ok {u ms T raw base G xs L} (ok : checkLift ms T raw base G xs = true)
    (properT : proper T) (properG : proper G) (low : Lower u base G L) :
    Lower u raw T (L+(xs.map Prod.fst).toFinset.card) := by
  simp only [checkLift,Bool.and_eq_true] at ok
  obtain ⟨eq,supp⟩ := map_correct ok.1.1
  apply lower_slice properT (essential_plain ok.1.2).1 (essential_plain ok.1.2).2 properG _ eq supp _ (essential_ok ok.1.2) _ L low
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
def typeWord (t : Nat) : Sig := bin (t/81) (inputs.getD (t/9 % 9) zero) (inputs.getD (t % 9) zero)
def varsX (m : Nat) : List Sig := if m<512 ∨ 2048≤m then vars m else vars m ++ [typeWord (m/512-1)]
def vertex (m j : Nat) := if m.testBit j then inputs.getD j zero else zero
def graphGoal (m : Nat) : Sig :=
  let x := vertex m
  if m=2110 then (x 1 &&& x 2) ||| (x 1 &&& x 3) ||| (x 2 &&& x 3) ||| (x 4) ||| (x 2 &&& x 5) ||| (x 3 &&& x 5) else
  if m=2109 then (x 2) ||| (x 0 &&& x 3) ||| (x 0 &&& x 4) ||| (x 3 &&& x 4) ||| (x 3 &&& x 5) else
  if m=2107 then (x 1) ||| (x 0 &&& x 3) ||| (x 0 &&& x 4) ||| (x 0 &&& x 5) ||| (x 3 &&& x 4 &&& x 5) else
  if m=2105 then (x 0 &&& x 3) ||| (x 0 &&& x 4) ||| (x 3 &&& x 4) ||| (x 3 &&& x 5) else
  if m=2103 then (x 0 &&& x 1) ||| (x 0 &&& x 2) ||| (x 1 &&& x 2) ||| (x 0 &&& x 4) ||| (x 1 &&& x 4) ||| (x 0 &&& x 5) ||| (x 1 &&& x 5) ||| (x 2 &&& x 4 &&& x 5) else
  if m=2095 then (x 0) ||| (x 1 &&& x 2) ||| (x 1 &&& x 3) ||| (x 2 &&& x 3 &&& x 5) else
  if m=2094 then (x 1 &&& x 2) ||| (x 1 &&& x 3) ||| (x 2 &&& x 3) ||| (x 2 &&& x 5) ||| (x 3 &&& x 5) else
  if m=2079 then (x 0 &&& x 2) ||| (x 1 &&& x 2) ||| (x 0 &&& x 3) ||| (x 1 &&& x 3) ||| (x 0 &&& x 4) ||| (x 2 &&& x 3 &&& x 4) else
  if m=2078 then (x 1 &&& x 2) ||| (x 1 &&& x 3) ||| (x 2 &&& x 3) ||| (x 4) else
  if m=2077 then (x 2) ||| (x 0 &&& x 3) ||| (x 0 &&& x 4) ||| (x 3 &&& x 4) else
  if m=2075 then (x 0 &&& x 3) ||| (x 1 &&& x 3) ||| (x 0 &&& x 4) else
  if m=2071 then (x 0 &&& x 1) ||| (x 0 &&& x 2) ||| (x 1 &&& x 2) ||| (x 0 &&& x 4) ||| (x 1 &&& x 4) else
  if m=2063 then (x 0) ||| (x 1 &&& x 2) ||| (x 1 &&& x 3) ||| (x 2 &&& x 3) else
  if m=60 then (x 2 &&& x 3) ||| (x 4) ||| (x 2 &&& x 5) ||| (x 3 &&& x 5) else
  if m=57 then (x 0 &&& x 3) ||| (x 0 &&& x 4) ||| (x 0 &&& x 5) ||| (x 3 &&& x 4 &&& x 5) else
  if m=54 then (x 1 &&& x 2) ||| (x 1 &&& x 4) ||| (x 1 &&& x 5) ||| (x 2 &&& x 4 &&& x 5) else
  if m=53 then (x 0 &&& x 2) ||| (x 0 &&& x 4) ||| (x 0 &&& x 5) ||| (x 2 &&& x 4 &&& x 5) else
  if m=51 then (x 0 &&& x 1) ||| (x 0 &&& x 4) ||| (x 1 &&& x 4) ||| (x 0 &&& x 5) ||| (x 1 &&& x 5) else
  if m=46 then (x 1 &&& x 2) ||| (x 1 &&& x 3) ||| (x 2 &&& x 3 &&& x 5) else
  if m=44 then (x 2 &&& x 3) ||| (x 2 &&& x 5) ||| (x 3 &&& x 5) else
  if m=39 then (x 0 &&& x 1) ||| (x 0 &&& x 2) ||| (x 1 &&& x 2) ||| (x 0 &&& x 5) ||| (x 1 &&& x 5) else
  if m=35 then (x 0 &&& x 1) ||| (x 0 &&& x 5) ||| (x 1 &&& x 5) else
  if m=30 then (x 1 &&& x 2) ||| (x 1 &&& x 3) ||| (x 2 &&& x 3 &&& x 4) else
  if m=29 then (x 0 &&& x 2) ||| (x 0 &&& x 3) ||| (x 0 &&& x 4) ||| (x 2 &&& x 3 &&& x 4) else
  if m=25 then (x 0 &&& x 3) ||| (x 0 &&& x 4) ||| (x 3 &&& x 4) else
  if m=23 then (x 0 &&& x 2) ||| (x 1 &&& x 2) ||| (x 0 &&& x 4) else
  if m=19 then (x 0 &&& x 1) ||| (x 0 &&& x 4) ||| (x 1 &&& x 4) else
  if m=14 then (x 1 &&& x 2) ||| (x 1 &&& x 3) ||| (x 2 &&& x 3) else
  if m=7 then (x 0 &&& x 1) ||| (x 0 &&& x 2) ||| (x 1 &&& x 2) else
  (x 1 &&& x 2) ||| (x 0 &&& x 1 &&& x 3) ||| (x 0 &&& x 2 &&& x 3) ||| (x 0 &&& x 4) ||| (x 1 &&& x 3 &&& x 4) ||| (x 0 &&& x 2 &&& x 5) ||| (x 0 &&& x 3 &&& x 5) ||| (x 1 &&& x 3 &&& x 5) ||| (x 2 &&& x 3 &&& x 4 &&& x 5)
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
  | 0 => (nat80 [0x1000000000000,0x10000000000000001,65536,4294967296,0x1000000000000,0x10000000000000001])
  | 1 => (nat80 [0x10000000000000000,65536,0,0x1000000000000,1])
  | 2 => (nat80 [1,65536,0,0,0x10000000000000001])
  | 3 => (nat80 [65536,0,0,1])
  | 4 => (nat80 [4294967296,0x1000000000000,0x10000000000000001])
  | 5 => (nat80 [0x1000000000000,1])
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
def supportPairs (_ : Nat) (mask : Nat) : List (Sig × Row × Row) :=
  (selected mask).map fun (i,a) =>
    let r := (mask >>> (9+9*i)) &&& 511
    (a,Fin.ofNat 512 r,Fin.ofNat 512 (r ||| (1 <<< i)))
def graphPairs (m hints : Nat) : List (Sig × Row × Row) :=
  (selected m).map fun (i,a) =>
    let r := (hints >>> (9*i)) &&& 511
    (a,Fin.ofNat 512 r,Fin.ofNat 512 (r ||| (1 <<< i)))
def properB (T : Sig) := T != zero && T != one
theorem proper_of (T : Sig) (h : properB T = true) : proper T := by
  simpa only [properB,proper,Bool.and_eq_true,bne_iff_ne] using h
abbrev ColumnInfo := Nat × Nat × Nat × Nat × Nat
def colFree (m z o : Nat) := m ^^^ (m &&& (z ||| o))
def chartGoal (m : Nat) : Sig := graphGoal m
def rawMask (m : Nat) (c : ColumnInfo) : Nat := m % 512+512*(c.1/512)
def colCheck (m : Nat) (c : ColumnInfo) (prior : Nat → Nat) : Bool :=
  let (z,o,q,s,L) := c
  let ms := fixRows z o
  let raw := rawMask m c
  let free := colFree raw (z % 512) o
  let G := movedWord ms (chartGoal m)
  let xs := supportPairs (z/512+80) s
  let count := (xs.map Prod.fst).toFinset.card
  properB G && checkMap ms (varsX raw) (chartGoal m) (varsX free) G &&
    (movedWord ms (subcube z o)==one) &&
    (if q=0 then checkEssential G (varsX free) xs && decide (L ≤ count-1)
     else properB (graphGoal q) &&
       checkLift (fixRows (colFree free q 0) 0) G (varsX free) (varsX q) (graphGoal q) xs &&
       decide (L ≤ prior q+count))
theorem col_sound {u} {m : Nat} (c : ColumnInfo) (prior : Nat → Nat)
    (valid : ∀ q, Lower u (varsX q) (graphGoal q) (prior q))
    (ok : colCheck m c prior = true) : Slice u (varsX (rawMask m c)) (chartGoal m) (subcube c.1 c.2.1) c.2.2.2.2 := by
  revert ok
  obtain ⟨z,o,q,s,L⟩ := c
  intro ok
  let ms := fixRows z o
  let raw := rawMask m (z,o,q,s,L)
  let free := colFree raw (z % 512) o
  let G := movedWord ms (chartGoal m)
  let xs := supportPairs (z/512+80) s
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
def carryOK (old rep : Nat) (swaps : List Nat) :=
  (properB (graphGoal old) && plainWord (graphGoal old) && (varsX old).all plainWord) && properB (graphGoal rep) &&
    checkMap (swaps.map swapRows) (varsX old) (graphGoal old) (varsX rep) (graphGoal rep)
theorem carry_of {u old rep L swaps} (ok : carryOK old rep swaps = true)
    (h : Lower u (varsX rep) (graphGoal rep) L) : Lower u (varsX old) (graphGoal old) L := by
  simp only [carryOK,Bool.and_eq_true] at ok
  exact lower_map ok.2 (proper_of _ ok.1.1.1.1) ok.1.1.1.2 ok.1.1.2 (proper_of _ ok.1.2) h
def boundsBefore (entries : List (Nat × Nat)) (q : Nat) :=
  ((entries.find? (fun a => a.1 == q)).map Prod.snd).getD 0
theorem before_sound {u} (entries : List (Nat × Nat))
    (sound : ∀ e ∈ entries, Lower u (varsX e.1) (graphGoal e.1) e.2) (q : Nat) :
    Lower u (varsX q) (graphGoal q) (boundsBefore entries q) := by
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
def ValidPool (u : Bool) (raw : List Sig) (T : Sig) (c : BoundPool) :=
  ∃ (f : Row → Row) (roots : List Sig) (bank : List (Wire Row)),
    (∀ r, bit (f r) c.domain = true) ∧ ¬Constant (restrictRows f (observe T)) ∧
    (∀ q ws, Reach u (roots.map observe) q ws → Available u ws (restrictRows f (observe T)) → c.bound ≤ q) ∧
    Reach u (roots.map observe) c.paid bank ∧ poolSupply u f bank c.wires ∧ True
theorem build_valid {u raw T d lb} (h : Slice u raw T d lb) (cs : List Choice) {ws}
    (build : makePool u d raw cs = some ws) : ValidPool u raw T ⟨d,lb,cs.length,ws⟩ := by
  obtain ⟨f,roots,dom,sup,nc,prior⟩ := h
  obtain ⟨bank,hr,hs⟩ := makePool_sound dom (Reach.start (roots:=roots.map observe)) sup cs build
  exact ⟨f,roots,bank,dom,nc,prior,by simpa [BoundPool.paid] using hr,hs,trivial⟩
theorem valid_exclude {u raw T c} (valid : ValidPool u raw T c) (k : Nat) (rest : List Sig)
    (choice : Choice) (paid : Bool)
    (known : ∀ a ∈ rest, availableB u c.domain c.wires a = true)
    (buy : if paid then choiceOK u c.domain c.wires choice = true
       else availableB u c.domain c.wires (choiceVal choice) = true)
    (bound : k+c.paid+paid.toNat <
      c.bound+(choiceVal choice :: rest).countP (isMaskedConstant c.domain))
    (nd : (choiceVal choice :: rest).Nodup) :
    Impossible u T k (choiceVal choice :: rest).toFinset := by
  intro t ht run
  obtain ⟨f,roots,bank,dom,nc,lo,hp,hs,_⟩ := valid
  let ws := choiceVal choice::rest
  have done (n : Nat) (out : List (Wire Row)) (reach : Reach u (roots.map observe) n out)
      (zs : poolSupply u f out (choiceVal choice::rest)) (le : n = c.paid+paid.toNat) : False := by
    have covered : supply u out ((ws.map observe).map (restrictRows f)) := by
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
    · have point : ∀ v ∈ c.wires, Available u out (restrictRows f (observe v)) :=
        fun v hu => hc v (List.mem_cons_of_mem _ hu)
      exact availableB_sound dom point (known _ hm)
def scalarPoolCut (u : Bool) (c : BoundPool) (k : Nat) (rest : List Sig) (op : Choice) :=
  let z := choiceVal op
  let extra := !(availableB u c.domain c.wires z)
  ((k+c.paid+extra.toNat < c.bound+(z::rest).countP (isMaskedConstant c.domain)) &&
    rest.all (availableB u c.domain c.wires)) && (!extra || choiceOK u c.domain c.wires op)
theorem scalarPoolCut_sound {u raw T c} (valid : ValidPool u raw T c) {k rest op}
    (nd : (choiceVal op::rest).Nodup) (cut : scalarPoolCut u c k rest op = true) :
    Impossible u T k (choiceVal op::rest).toFinset := by
  let extra := !(availableB u c.domain c.wires (choiceVal op))
  apply valid_exclude valid k rest op extra _ _ _ nd
  · simp only [scalarPoolCut,Bool.and_eq_true,List.all_eq_true] at cut
    exact cut.1.2
  · simp only [scalarPoolCut,Bool.and_eq_true,Bool.or_eq_true] at cut
    cases he : availableB u c.domain c.wires (choiceVal op) <;> simp_all [extra]
  · simp only [scalarPoolCut,Bool.and_eq_true,decide_eq_true_eq] at cut
    exact cut.1.1
def materialize (u : Bool) (raw : List Sig) (cs : List Choice) (d : Sig) (lb : Nat) : Option BoundPool :=
  (makePool u d raw cs).map (fun pool => ⟨d,lb,cs.length,pool⟩)
theorem materialize_sound {u raw T d L cs c} (slice : Slice u raw T d L)
    (h : materialize u raw cs d L = some c) : ValidPool u raw T c := by
  unfold materialize at h
  cases he : makePool u d raw cs with
  | none => simp [he] at h
  | some pool =>
    simp only [he,Option.map_some,Option.some.injEq] at h
    subst c
    exact build_valid slice cs he
abbrev Bits := BitVec 152
abbrev Signals := Bits × Bits
abbrev Decor := Sig × Signals
def ofRows {n : Nat} (r : Fin n → Row) (v : Sig) : BitVec n :=
  (BitVec.ofBoolListLE (List.ofFn (fun i => bit (r i) v))).cast List.length_ofFn
theorem ofRows_bit {n : Nat} (r : Fin n → Row) (v : Sig) (i : Fin n) :
    (ofRows r v).getLsbD i.val = bit (r i) v := by
  simp only [ofRows,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [i.isLt]
def pairSig (r s : Fin 152 → Row) (a : Sig) : Signals := (ofRows r a,ofRows s a)
def properPairs (T : Sig) (r s : Fin 152 → Row) :=
  ∀ i, bit (r i) T = true ∧ bit (s i) T = false
theorem pair_sep {T r s} (h : properPairs T r s) : Sep T 152 r s (pairSig r s) := by
  exact ⟨h,fun a i => ⟨ofRows_bit _ _ _,ofRows_bit _ _ _⟩⟩
def faithful (r s : Fin 152 → Row) (x : Decor) := x.2 = pairSig r s x.1
def bv {n : Nat} (d : Nat) (a b : BitVec n) : BitVec n :=
  if d=0 then a &&& b else if d=1 then a ||| b else if d=2 then a &&& ~~~b else ~~~a &&& b
def dbin (d : Nat) (x y : Decor) : Decor := (bin d x.1 y.1,bv d x.2.1 y.2.1,bv d x.2.2 y.2.2)
theorem ofRows_bin {n : Nat} (r : Fin n → Row) (d : Nat) (a b : Sig) :
    ofRows r (bin d a b) = bv d (ofRows r a) (ofRows r b) := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have h := ofRows_bit r (bin d a b) ⟨j,hj⟩
  rw [bit_bin,←ofRows_bit r a ⟨j,hj⟩,←ofRows_bit r b ⟨j,hj⟩] at h
  rw [h]
  unfold bv
  split_ifs <;> simp [hj]
theorem faithful_bin {r s x y} (d) (hx : faithful r s x) (hy : faithful r s y) :
    faithful r s (dbin d x y) := by
  change x.2 = _ at hx
  change y.2 = _ at hy
  simp only [faithful,dbin,pairSig,ofRows_bin,hx,hy]
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
    decodeBank k (bits >>> 10) (ws++[dbin ((bits >>> 8) &&& 3) a b])
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
      exact faithful_bin _ (faithful_get base _) (faithful_get base _)
def asRow (cols : Nat → Bits) (i : Fin 152) : Row :=
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
theorem asRow_bit (cols : Nat → Bits) (i : Fin 152) (j : Fin 9) :
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
  if m=2110 then (x 1 &&& x 2) ||| (x 1 &&& x 3) ||| (x 2 &&& x 3) ||| (x 4) ||| (x 2 &&& x 5) ||| (x 3 &&& x 5) else
  if m=2109 then (x 2) ||| (x 0 &&& x 3) ||| (x 0 &&& x 4) ||| (x 3 &&& x 4) ||| (x 3 &&& x 5) else
  if m=2107 then (x 1) ||| (x 0 &&& x 3) ||| (x 0 &&& x 4) ||| (x 0 &&& x 5) ||| (x 3 &&& x 4 &&& x 5) else
  if m=2105 then (x 0 &&& x 3) ||| (x 0 &&& x 4) ||| (x 3 &&& x 4) ||| (x 3 &&& x 5) else
  if m=2103 then (x 0 &&& x 1) ||| (x 0 &&& x 2) ||| (x 1 &&& x 2) ||| (x 0 &&& x 4) ||| (x 1 &&& x 4) ||| (x 0 &&& x 5) ||| (x 1 &&& x 5) ||| (x 2 &&& x 4 &&& x 5) else
  if m=2095 then (x 0) ||| (x 1 &&& x 2) ||| (x 1 &&& x 3) ||| (x 2 &&& x 3 &&& x 5) else
  if m=2094 then (x 1 &&& x 2) ||| (x 1 &&& x 3) ||| (x 2 &&& x 3) ||| (x 2 &&& x 5) ||| (x 3 &&& x 5) else
  if m=2079 then (x 0 &&& x 2) ||| (x 1 &&& x 2) ||| (x 0 &&& x 3) ||| (x 1 &&& x 3) ||| (x 0 &&& x 4) ||| (x 2 &&& x 3 &&& x 4) else
  if m=2078 then (x 1 &&& x 2) ||| (x 1 &&& x 3) ||| (x 2 &&& x 3) ||| (x 4) else
  if m=2077 then (x 2) ||| (x 0 &&& x 3) ||| (x 0 &&& x 4) ||| (x 3 &&& x 4) else
  if m=2075 then (x 0 &&& x 3) ||| (x 1 &&& x 3) ||| (x 0 &&& x 4) else
  if m=2071 then (x 0 &&& x 1) ||| (x 0 &&& x 2) ||| (x 1 &&& x 2) ||| (x 0 &&& x 4) ||| (x 1 &&& x 4) else
  if m=2063 then (x 0) ||| (x 1 &&& x 2) ||| (x 1 &&& x 3) ||| (x 2 &&& x 3) else
  if m=60 then (x 2 &&& x 3) ||| (x 4) ||| (x 2 &&& x 5) ||| (x 3 &&& x 5) else
  if m=57 then (x 0 &&& x 3) ||| (x 0 &&& x 4) ||| (x 0 &&& x 5) ||| (x 3 &&& x 4 &&& x 5) else
  if m=54 then (x 1 &&& x 2) ||| (x 1 &&& x 4) ||| (x 1 &&& x 5) ||| (x 2 &&& x 4 &&& x 5) else
  if m=53 then (x 0 &&& x 2) ||| (x 0 &&& x 4) ||| (x 0 &&& x 5) ||| (x 2 &&& x 4 &&& x 5) else
  if m=51 then (x 0 &&& x 1) ||| (x 0 &&& x 4) ||| (x 1 &&& x 4) ||| (x 0 &&& x 5) ||| (x 1 &&& x 5) else
  if m=46 then (x 1 &&& x 2) ||| (x 1 &&& x 3) ||| (x 2 &&& x 3 &&& x 5) else
  if m=44 then (x 2 &&& x 3) ||| (x 2 &&& x 5) ||| (x 3 &&& x 5) else
  if m=39 then (x 0 &&& x 1) ||| (x 0 &&& x 2) ||| (x 1 &&& x 2) ||| (x 0 &&& x 5) ||| (x 1 &&& x 5) else
  if m=35 then (x 0 &&& x 1) ||| (x 0 &&& x 5) ||| (x 1 &&& x 5) else
  if m=30 then (x 1 &&& x 2) ||| (x 1 &&& x 3) ||| (x 2 &&& x 3 &&& x 4) else
  if m=29 then (x 0 &&& x 2) ||| (x 0 &&& x 3) ||| (x 0 &&& x 4) ||| (x 2 &&& x 3 &&& x 4) else
  if m=25 then (x 0 &&& x 3) ||| (x 0 &&& x 4) ||| (x 3 &&& x 4) else
  if m=23 then (x 0 &&& x 2) ||| (x 1 &&& x 2) ||| (x 0 &&& x 4) else
  if m=19 then (x 0 &&& x 1) ||| (x 0 &&& x 4) ||| (x 1 &&& x 4) else
  if m=14 then (x 1 &&& x 2) ||| (x 1 &&& x 3) ||| (x 2 &&& x 3) else
  if m=7 then (x 0 &&& x 1) ||| (x 0 &&& x 2) ||| (x 1 &&& x 2) else
  (x 1 &&& x 2) ||| (x 0 &&& x 1 &&& x 3) ||| (x 0 &&& x 2 &&& x 3) ||| (x 0 &&& x 4) ||| (x 1 &&& x 3 &&& x 4) ||| (x 0 &&& x 2 &&& x 5) ||| (x 0 &&& x 3 &&& x 5) ||| (x 1 &&& x 3 &&& x 5) ||| (x 2 &&& x 3 &&& x 4 &&& x 5)
theorem bit_vertex (m : Nat) (v : Nat → Bits) (i : Fin 152) (j : Fin 9) :
    bit (asRow v i) (vertex m j.val) =
    ((if m.testBit j.val then v j.val else 0) : Bits).getLsbD i.val := by
  by_cases hh : m.testBit j.val = true
  · simpa [vertex,hh] using asRow_bit v i j
  · simp [vertex,hh,bit_zero]
theorem bit_liftGoal (m : Nat) (v : Nat → Bits) (i : Fin 152) :
    bit (asRow v i) (graphGoal m) = (liftGoal m v).getLsbD i.val := by
  have pos (j : Nat) (hj : j<9) : (vertex m j).getLsbD (asRow v i).val = ((if m.testBit j then v j else 0) : Bits).getLsbD i.val := bit_vertex m v i ⟨j,hj⟩
  by_cases h0 : m=2110
  · simp only [graphGoal,liftGoal,if_pos h0,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 1 (by decide),pos 2 (by decide),pos 3 (by decide),pos 4 (by decide),pos 5 (by decide)]
  by_cases h1 : m=2109
  · simp only [graphGoal,liftGoal,if_neg h0,if_pos h1,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 0 (by decide),pos 2 (by decide),pos 3 (by decide),pos 4 (by decide),pos 5 (by decide)]
  by_cases h2 : m=2107
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_pos h2,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 0 (by decide),pos 1 (by decide),pos 3 (by decide),pos 4 (by decide),pos 5 (by decide)]
  by_cases h3 : m=2105
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_pos h3,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 0 (by decide),pos 3 (by decide),pos 4 (by decide),pos 5 (by decide)]
  by_cases h4 : m=2103
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_pos h4,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 0 (by decide),pos 1 (by decide),pos 2 (by decide),pos 4 (by decide),pos 5 (by decide)]
  by_cases h5 : m=2095
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_pos h5,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 0 (by decide),pos 1 (by decide),pos 2 (by decide),pos 3 (by decide),pos 5 (by decide)]
  by_cases h6 : m=2094
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_pos h6,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 1 (by decide),pos 2 (by decide),pos 3 (by decide),pos 5 (by decide)]
  by_cases h7 : m=2079
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_pos h7,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 0 (by decide),pos 1 (by decide),pos 2 (by decide),pos 3 (by decide),pos 4 (by decide)]
  by_cases h8 : m=2078
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_neg h7,if_pos h8,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 1 (by decide),pos 2 (by decide),pos 3 (by decide),pos 4 (by decide)]
  by_cases h9 : m=2077
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_neg h7,if_neg h8,if_pos h9,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 0 (by decide),pos 2 (by decide),pos 3 (by decide),pos 4 (by decide)]
  by_cases h10 : m=2075
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_neg h7,if_neg h8,if_neg h9,if_pos h10,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 0 (by decide),pos 1 (by decide),pos 3 (by decide),pos 4 (by decide)]
  by_cases h11 : m=2071
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_neg h7,if_neg h8,if_neg h9,if_neg h10,if_pos h11,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 0 (by decide),pos 1 (by decide),pos 2 (by decide),pos 4 (by decide)]
  by_cases h12 : m=2063
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_neg h7,if_neg h8,if_neg h9,if_neg h10,if_neg h11,if_pos h12,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 0 (by decide),pos 1 (by decide),pos 2 (by decide),pos 3 (by decide)]
  by_cases h13 : m=60
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_neg h7,if_neg h8,if_neg h9,if_neg h10,if_neg h11,if_neg h12,if_pos h13,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 2 (by decide),pos 3 (by decide),pos 4 (by decide),pos 5 (by decide)]
  by_cases h14 : m=57
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_neg h7,if_neg h8,if_neg h9,if_neg h10,if_neg h11,if_neg h12,if_neg h13,if_pos h14,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 0 (by decide),pos 3 (by decide),pos 4 (by decide),pos 5 (by decide)]
  by_cases h15 : m=54
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_neg h7,if_neg h8,if_neg h9,if_neg h10,if_neg h11,if_neg h12,if_neg h13,if_neg h14,if_pos h15,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 1 (by decide),pos 2 (by decide),pos 4 (by decide),pos 5 (by decide)]
  by_cases h16 : m=53
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_neg h7,if_neg h8,if_neg h9,if_neg h10,if_neg h11,if_neg h12,if_neg h13,if_neg h14,if_neg h15,if_pos h16,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 0 (by decide),pos 2 (by decide),pos 4 (by decide),pos 5 (by decide)]
  by_cases h17 : m=51
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_neg h7,if_neg h8,if_neg h9,if_neg h10,if_neg h11,if_neg h12,if_neg h13,if_neg h14,if_neg h15,if_neg h16,if_pos h17,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 0 (by decide),pos 1 (by decide),pos 4 (by decide),pos 5 (by decide)]
  by_cases h18 : m=46
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_neg h7,if_neg h8,if_neg h9,if_neg h10,if_neg h11,if_neg h12,if_neg h13,if_neg h14,if_neg h15,if_neg h16,if_neg h17,if_pos h18,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 1 (by decide),pos 2 (by decide),pos 3 (by decide),pos 5 (by decide)]
  by_cases h19 : m=44
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_neg h7,if_neg h8,if_neg h9,if_neg h10,if_neg h11,if_neg h12,if_neg h13,if_neg h14,if_neg h15,if_neg h16,if_neg h17,if_neg h18,if_pos h19,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 2 (by decide),pos 3 (by decide),pos 5 (by decide)]
  by_cases h20 : m=39
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_neg h7,if_neg h8,if_neg h9,if_neg h10,if_neg h11,if_neg h12,if_neg h13,if_neg h14,if_neg h15,if_neg h16,if_neg h17,if_neg h18,if_neg h19,if_pos h20,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 0 (by decide),pos 1 (by decide),pos 2 (by decide),pos 5 (by decide)]
  by_cases h21 : m=35
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_neg h7,if_neg h8,if_neg h9,if_neg h10,if_neg h11,if_neg h12,if_neg h13,if_neg h14,if_neg h15,if_neg h16,if_neg h17,if_neg h18,if_neg h19,if_neg h20,if_pos h21,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 0 (by decide),pos 1 (by decide),pos 5 (by decide)]
  by_cases h22 : m=30
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_neg h7,if_neg h8,if_neg h9,if_neg h10,if_neg h11,if_neg h12,if_neg h13,if_neg h14,if_neg h15,if_neg h16,if_neg h17,if_neg h18,if_neg h19,if_neg h20,if_neg h21,if_pos h22,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 1 (by decide),pos 2 (by decide),pos 3 (by decide),pos 4 (by decide)]
  by_cases h23 : m=29
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_neg h7,if_neg h8,if_neg h9,if_neg h10,if_neg h11,if_neg h12,if_neg h13,if_neg h14,if_neg h15,if_neg h16,if_neg h17,if_neg h18,if_neg h19,if_neg h20,if_neg h21,if_neg h22,if_pos h23,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 0 (by decide),pos 2 (by decide),pos 3 (by decide),pos 4 (by decide)]
  by_cases h24 : m=25
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_neg h7,if_neg h8,if_neg h9,if_neg h10,if_neg h11,if_neg h12,if_neg h13,if_neg h14,if_neg h15,if_neg h16,if_neg h17,if_neg h18,if_neg h19,if_neg h20,if_neg h21,if_neg h22,if_neg h23,if_pos h24,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 0 (by decide),pos 3 (by decide),pos 4 (by decide)]
  by_cases h25 : m=23
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_neg h7,if_neg h8,if_neg h9,if_neg h10,if_neg h11,if_neg h12,if_neg h13,if_neg h14,if_neg h15,if_neg h16,if_neg h17,if_neg h18,if_neg h19,if_neg h20,if_neg h21,if_neg h22,if_neg h23,if_neg h24,if_pos h25,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 0 (by decide),pos 1 (by decide),pos 2 (by decide),pos 4 (by decide)]
  by_cases h26 : m=19
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_neg h7,if_neg h8,if_neg h9,if_neg h10,if_neg h11,if_neg h12,if_neg h13,if_neg h14,if_neg h15,if_neg h16,if_neg h17,if_neg h18,if_neg h19,if_neg h20,if_neg h21,if_neg h22,if_neg h23,if_neg h24,if_neg h25,if_pos h26,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 0 (by decide),pos 1 (by decide),pos 4 (by decide)]
  by_cases h27 : m=14
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_neg h7,if_neg h8,if_neg h9,if_neg h10,if_neg h11,if_neg h12,if_neg h13,if_neg h14,if_neg h15,if_neg h16,if_neg h17,if_neg h18,if_neg h19,if_neg h20,if_neg h21,if_neg h22,if_neg h23,if_neg h24,if_neg h25,if_neg h26,if_pos h27,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 1 (by decide),pos 2 (by decide),pos 3 (by decide)]
  by_cases h28 : m=7
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_neg h7,if_neg h8,if_neg h9,if_neg h10,if_neg h11,if_neg h12,if_neg h13,if_neg h14,if_neg h15,if_neg h16,if_neg h17,if_neg h18,if_neg h19,if_neg h20,if_neg h21,if_neg h22,if_neg h23,if_neg h24,if_neg h25,if_neg h26,if_neg h27,if_pos h28,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 0 (by decide),pos 1 (by decide),pos 2 (by decide)]
  simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_neg h7,if_neg h8,if_neg h9,if_neg h10,if_neg h11,if_neg h12,if_neg h13,if_neg h14,if_neg h15,if_neg h16,if_neg h17,if_neg h18,if_neg h19,if_neg h20,if_neg h21,if_neg h22,if_neg h23,if_neg h24,if_neg h25,if_neg h26,if_neg h27,if_neg h28,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
  simp only [pos 0 (by decide),pos 1 (by decide),pos 2 (by decide),pos 3 (by decide),pos 4 (by decide),pos 5 (by decide)]
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
  let n := v.toNat % 2305843009213693921
  (n*(n+971)) % 2305843009213693921
def keySet (xs : List Sig) := xs.foldl (fun v x => v+keyWord x) 0
def closeChild (u : Bool) (pools : List BoundPool) (links : Nat → List (List Sig)) (k : Nat)
    (rest : List Sig) (op : Choice) :=
  let ws := choiceVal op::rest
  (links (keySet ws)).any (sameWords ws) || pools.any (fun p => scalarPoolCut u p k rest op)
theorem closeChild_sound {u raw T pools links k rest op}
    (pValid : ∀ p ∈ pools, ValidPool u raw T p)
    (lValid : ∀ tag xs, xs ∈ links tag → Impossible u T k (List.toFinset xs))
    (nd : (choiceVal op :: rest).Nodup)
    (h : closeChild u pools links k rest op = true) :
    Impossible u T k (choiceVal op :: rest).toFinset := by
  simp only [closeChild,Bool.or_eq_true,List.any_eq_true] at h
  rcases h with ⟨xs,hx,ok⟩ | ⟨p,hp,ok⟩
  · rw [sameWords_sound ok]
    exact lValid _ _ hx
  · exact scalarPoolCut_sound (pValid _ hp) nd ok
abbrev CovPair := Cov × Bool
def preCov (u : Bool) (ws : List Decor) : CovPair := (coverage (!u) ws,u)
def restCov (v : Cov) (a b : Bits) (ka kb : Bool) :=
  if ka then (if kb then v.1 else takeOne v b) else if kb then takeOne v a else takeTwo v a b
theorem delOne_sub (ws : List Decor) (a : Decor) (k : Bool) : (delOne ws a k).Sublist ws := by
  cases k
  · exact List.erase_sublist
  · exact List.Sublist.refl _
theorem keep_sub (ws : List Decor) (a b : Decor) (ka kb : Bool) :
    (delTwo ws a b ka kb).Sublist ws := (delOne_sub _ _ _).trans (delOne_sub _ _ _)
theorem len_keep (ws : List Decor) (a b : Decor) (ka kb : Bool) (ha : a ∈ ws) (hb : b ∈ ws) (ne : a≠b) :
    (delTwo ws a b ka kb).length =
      ws.length - (if ka then 0 else 1) - (if kb then 0 else 1) := by
  have hm : b ∈ ws.erase a := (List.mem_erase_of_ne (Ne.symm ne)).mpr hb
  cases ka <;> cases kb <;> simp [delTwo,delOne,List.length_erase_of_mem ha,List.length_erase_of_mem hb,List.length_erase_of_mem hm]
def movedChoice (op : Nat) (a b : Decor) : Choice := (op,a.1,b.1)
abbrev NodeContext := Nat × Nat × List Decor × CovPair × List BoundPool × (Nat → List (List Sig))
def evalMove (c : NodeContext) (op : Nat) (a b z : Decor) (ka kb : Bool) :=
  let (cap,n,ws,cov,pools,links) := c
  let len := 1+(n - (if ka then 0 else 1) - (if kb then 0 else 1))
  if len>cap then true else
    let d := !cov.2
    let rs := restCov cov.1 (column d a.2) (column d b.2) ka kb
    if (rs ||| column d z.2) != BitVec.allOnes 152 then true else
    if !properB z.1 || ws.any (fun v => v.1==z.1) then true else
      let rest := (delTwo ws a b ka kb).map Prod.fst
      closeChild cov.2 pools links (cap-1) rest (movedChoice op a b)
def moveFront (ws : List Decor) (op : Nat) (a b : Decor) (ka kb : Bool) :=
  (dbin op a b).1 :: (delTwo ws a b ka kb).map Prod.fst
theorem evalMove_sound {u raw T r s ws pools links cap a b op ka kb}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : a≠b) (hcap : 0<cap)
    (pv : ∀ p ∈ pools, ValidPool u raw T p)
    (lv : ∀ tag xs, xs ∈ links tag → Impossible u T (cap-1) (List.toFinset xs))
    (pro : proper (dbin op a b).1) (fresh : (dbin op a b).1 ∉ ws.map Prod.fst)
    (test : evalMove (cap,ws.length,ws,preCov u ws,pools,links) op a b (dbin op a b) ka kb = true) :
    Impossible u T (cap-1) (moveFront ws op a b ka kb).toFinset := by
  let z := dbin op a b
  let rest := delTwo ws a b ka kb
  let child := z.1 :: rest.map Prod.fst
  have sub : rest.Sublist ws := keep_sub _ _ _ _ _
  have ndc : child.Nodup := List.nodup_cons.mpr ⟨fun hm => fresh ((sub.map _).subset hm),
    nd.sublist (sub.map _)⟩
  have fr : ws.any (fun v => v.1==z.1) = false := by
    apply Bool.eq_false_iff.mpr
    intro hh
    obtain ⟨x,hx,he⟩ := List.any_eq_true.mp hh
    exact fresh (beq_iff_eq.mp he ▸ List.mem_map_of_mem hx)
  have pp : properB z.1 = true := by simpa [properB,proper] using pro
  have leq : 1+(ws.length-(if ka then 0 else 1)-(if kb then 0 else 1)) = child.length := by
    change _ = (z.1::rest.map Prod.fst).length
    rw [List.length_cons,List.length_map,len_keep _ _ _ _ _ ha hb ne,Nat.add_comm 1]
  intro k hk h
  have hsz := live_size h
  change child.toFinset.card ≤ k+1 at hsz
  rw [List.toFinset_card_of_nodup ndc] at hsz
  have len : child.length ≤ cap := by omega
  unfold evalMove at test
  change (if 1+(ws.length-_ - _) > cap then true else _) = true at test
  rw [leq,if_neg (by omega)] at test
  have sep := cover_required h (pair_sep pairs)
  let d := !u
  have g : (coverage d rest).1 = covered d (pairSig r s) (rest.map Prod.fst) :=
    cov_word _ _ (fun v hv => faith _ (sub.subset hv))
  have rz : (coverage d rest).1 = restCov (coverage d ws) (column d a.2) (column d b.2) ka kb :=
    cover_two d a b ha hb ne ka kb
  have hf := faithful_bin op (faith _ ha) (faith _ hb)
  change column d (pairSig r s z.1) ||| covered d (pairSig r s) (rest.map Prod.fst) = _ at sep
  change z.2 = pairSig r s z.1 at hf
  rw [←hf,←g,rz,BitVec.or_comm] at sep
  have be : ((restCov (coverage (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 152) = false := by
    simpa using sep
  change (if (restCov (coverage (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 152 then true else if !properB z.1 || ws.any (fun v => v.1==z.1) then true else _) = true at test
  rw [be,pp,fr] at test
  exact closeChild_sound (op:=movedChoice op a b) (rest:=rest.map Prod.fst) pv lv ndc test k hk h
def testPair (ctx : NodeContext) (a b : Decor) (op : Nat) :=
  let z := dbin op a b
  let attempt := evalMove ctx op a b z
  attempt false false && attempt true false && attempt false true && attempt true true
def opsOf (u : Bool) : List Nat := if u then [0,1,2,3] else [0,1]
theorem opsOf_mem {u d} (h : allowed u d) : d ∈ opsOf u := by
  rcases allowed_four h with rfl | rfl | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · cases u <;> simp [opsOf]
  · cases u <;> simp [opsOf]
  · simp [opsOf]
  · simp [opsOf]
def testRow (ctx : NodeContext) (a : Decor) (bs : List Decor) :=
    bs.all (fun b => (opsOf ctx.2.2.2.1.2).all (testPair ctx a b))
def testAll (ctx : NodeContext) : List Decor → Bool
  | [] => true
  | a::bs => testRow ctx a bs && testAll ctx bs
theorem all_binary {ctx ws} (h : testAll ctx ws=true) {a b : Decor} (ha : a∈ws) (hb : b∈ws)
    (ne : a≠b) : (∀ d, allowed ctx.2.2.2.1.2 d → testPair ctx a b d=true) ∨
      (∀ d, allowed ctx.2.2.2.1.2 d → testPair ctx b a d=true) := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    simp only [testAll,Bool.and_eq_true,testRow,List.all_eq_true] at h
    rcases List.mem_cons.mp ha with rfl | haTail
    · have bm := (List.mem_cons.mp hb).resolve_left (Ne.symm ne)
      exact Or.inl fun d hd => h.1 b bm d (opsOf_mem hd)
    · rcases List.mem_cons.mp hb with rfl | hbTail
      · exact Or.inr fun d hd => h.1 a haTail d (opsOf_mem hd)
      · exact ih h.2 haTail hbTail
theorem testPair_at {ctx a b d} (h : testPair ctx a b d = true) (ka kb : Bool) :
    evalMove ctx d a b (dbin d a b) ka kb = true := by
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
    (ha : a ∈ ws) (hb : b ∈ ws) (ka kb : Bool) (v : Sig) :
    v ∈ (delTwo ws a b ka kb).map Prod.fst ↔
    v ∈ ws.map Prod.fst ∧ (v≠a.1 ∨ ka=true) ∧ (v≠b.1 ∨ kb=true) := by
  have wn := nd.of_map
  have dn := wn.sublist (delOne_sub ws a ka)
  simp only [delTwo,List.mem_map,mem_delone wn,mem_delone dn]
  constructor
  · rintro ⟨w,hw,rfl⟩
    exact ⟨⟨_,hw.1.1,rfl⟩,hw.1.2.imp (fun ne eq => ne (unique_value nd hw.1.1 ha eq)) id,
          hw.2.imp (fun ne eq => ne (unique_value nd hw.1.1 hb eq)) id⟩
  · rintro ⟨⟨w,hm,rfl⟩,h1,h2⟩
    exact ⟨w,⟨⟨hm,h1.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,
        h2.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,rfl⟩
theorem binary_front {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a∈ws) (hb : b∈ws) (ne : a.1≠b.1) (d : Nat) (ka kb : Bool) :
    (moveFront ws d a b ka kb).toFinset =
      (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
  ext v
  have av := List.mem_map_of_mem (f:=Prod.fst) ha
  have bv' := List.mem_map_of_mem (f:=Prod.fst) hb
  simp only [moveFront,childTwo,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    kept_value nd ha hb,keep_mem,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,dbin]
  by_cases va : v=a.1 <;> by_cases vb : v=b.1 <;> cases ka <;> cases kb <;> simp_all
theorem childTwo_swap {u} (v : List Sig) (nd : v.Nodup) (a b : Sig) (d : Nat) (hd : allowed u d) (ka kb : Bool) :
    (childTwo v a b d ka kb).toFinset = (childTwo v b a (flipOp d) kb ka).toFinset := by
  ext x
  simp only [childTwo,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    keep_mem,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,bin_flip hd a b]
  tauto
theorem node_sound {u raw T r s ws pools links cap}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (out : T ∉ ws.map Prod.fst)
    (pv : ∀ p ∈ pools, ValidPool u raw T p)
    (lv : ∀ tag xs, xs ∈ links tag → Impossible u T (cap-1) (List.toFinset xs))
    (checks : testAll (cap,ws.length,ws,preCov u ws,pools,links) ws = true) :
    Impossible u T cap (ws.map Prod.fst).toFinset := by
  by_cases hc : cap=0
  · intro k hk h
    have ke : k=0 := by omega
    subst k
    generalize he : (ws.map Prod.fst).toFinset = S at h
    obtain ⟨hS,_⟩ := h
    exact out (List.mem_toFinset.mp (by rw [he,hS]; exact Finset.mem_singleton_self _))
  have hc' : 0<cap := by omega
  apply enum_step nd out
  intro a ha b hb d hd ka kb ne fresh pro len
  obtain ⟨a,haW,rfl⟩ := List.mem_map.mp ha
  obtain ⟨b,hbW,rfl⟩ := List.mem_map.mp hb
  have ab : a≠b := fun e => ne (congrArg Prod.fst e)
  have one (a b : Decor) (d : Nat) (aa : a∈ws) (bb : b∈ws) (ne' : a.1≠b.1) (ka kb : Bool)
      (pr : proper (bin d a.1 b.1)) (fr : bin d a.1 b.1 ∉ ws.map Prod.fst)
      (test : testPair (cap,ws.length,ws,preCov u ws,pools,links) a b d = true) :
      Impossible u T (cap-1) (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
    rw [←binary_front nd aa bb ne']
    exact evalMove_sound pairs faith nd aa bb (fun e => ne' (congrArg Prod.fst e)) hc' pv lv
      pr fr (testPair_at test ka kb)
  rcases all_binary checks haW hbW ab with hh | hh
  · exact one a b d haW hbW ne ka kb pro fresh (hh d hd)
  · rw [childTwo_swap _ nd _ _ d hd]
    exact one b a (flipOp d) hbW haW (Ne.symm ne) kb ka (bin_flip hd a.1 b.1 ▸ pro)
      (bin_flip hd a.1 b.1 ▸ fresh) (hh _ (flip_flip hd).1)
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
theorem rotate_excluded {u T n} {ws : List Sig} (hi : Impossible u T n ws.toFinset)
    (p : List Move) (ok : autoOK T p = true) : Impossible u T n (ws.map (movedWord p.reverse)).toFinset := by
  simp only [autoOK,Bool.and_eq_true,beq_iff_eq] at ok
  have onto : Function.Surjective (movedRow p) := fun r => ⟨movedRow p.reverse r,composed_id ok.2 r⟩
  intro k hk h
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
  exact hi k hk run
abbrev Packing := Nat × Nat × Nat × Nat × Nat × Nat × Nat × (Nat → Nat)
def emptyPacking : Packing := (0,0,0,0,0,0,0,fun _ => 0)
private def limbs80 (pages : Array (Array Nat)) (i : Nat) : Nat :=
  ((pages[i/32]?).getD #[])[i%32]?.getD 0
def packedAt (word : Nat → Nat) (pos len : Nat) :=
  let i := pos/80
  let shift := pos % 80
  let lo := word i >>> shift
  if shift+len ≤ 80 then lo &&& ((1 <<< len)-1)
  else (lo ||| (word (i+1) <<< (80-shift))) &&& ((1 <<< len)-1)
def lookupWord (nb slots sw vw iw pw : Nat) (data : Nat → Nat) (h : Nat) : Option (Nat × Nat) :=
  let a := h % nb
  let sh := packedAt data (a*sw) sw
  let row := (h/nb+sh) % slots
  let word := packedAt data (nb*sw+row*vw) vw
  if (word >>> (iw+pw)) == h/(nb*slots) % 16 then
    some (word &&& ((1 <<< iw)-1),(word >>> iw) &&& ((1 <<< pw)-1))
  else none
def lookupShort (nb slots sw vw iw pw : Nat) (data : Nat → Nat) (h : Nat) : Option (Nat × Nat) :=
  let a := h % nb
  let sh := packedAt data (a*sw) sw
  let row := (h/nb+sh) % slots
  let word := packedAt data (nb*sw+row*vw) vw
  if (word >>> (iw+pw)) == h/(nb*slots) % 4 then
    some (word &&& ((1 <<< iw)-1),(word >>> iw) &&& ((1 <<< pw)-1))
  else none
abbrev Forest := Nat × Nat × (Nat → Bits × Bits) × List ColumnInfo × List (List Nat) ×
  (Nat → Packing) × (Nat → Nat → Option (Nat × Nat))
def Forest.mask (g : Forest) : Nat := g.1
def Forest.mode (g : Forest) : Bool := !(g.1.testBit 10)
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
theorem chart_bit (m : Nat) (v : Nat → Bits) (i : Fin 152) :
    bit (asRow v i) (chartGoal m) = (chartSamples m v).getLsbD i.val := by
  exact bit_liftGoal m v i
theorem chart_pairs {m : Nat} {p q : Nat → Bits}
    (hp : chartSamples m p = BitVec.allOnes 152) (hq : chartSamples m q = 0) :
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
def prefixWidth (d : Nat) := 10*(d-1)
def denseRowWidth (d flags : Nat) := flags % 16 + (if d=0 then 0 else 10) + flags/16
def denseRowStart (d raw dict : Nat) :=
  (dict % 65536)*prefixWidth d + (dict/65536)*(raw+d)
def forestRecord (tab : Packing) (raw i : Nat) : Nat :=
  let (_,d,_,dict,flags,_,marker,word) := tab
  let width := 10*d+raw+d
  if marker<1024 then packedAt word (i*width) width else
    let off := denseRowStart d raw dict+i*denseRowWidth d flags
    let pre := packedAt word off (flags % 16)
    let lastBits := if d=0 then 0 else 10
    let last := packedAt word (off+flags % 16) lastBits
    let mask := packedAt word (off+flags % 16+lastBits) (flags/16)
    let base := (dict % 65536)*prefixWidth d
    packedAt word (pre*prefixWidth d) (prefixWidth d) |||
      (last <<< prefixWidth d) ||| (packedAt word (base+mask*(raw+d)) (raw+d) <<< (10*d))
def storedDepth (_g : Forest) (depth : Nat) := depth
def readNode (g : Forest) (k i : Nat) : Nat × List Decor × List Decor :=
  let raw := wiresOf g
  let (_,depth,_,_,_,_,_,data) := g.levels k
  let len := 10*storedDepth g depth
  let width := len+raw.length+depth
  let recp := forestRecord (g.levels k) raw.length i
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
    materialize g.mode (varsX (rawMask g.mask ci)) (chosenSteps bank ops paid d) (subcube ci.1 ci.2.1) ci.2.2.2.2
theorem buildRule_sound (g : Forest)
    (cols : ∀ ci ∈ g.cols, Slice g.mode (varsX (rawMask g.mask ci)) (targetOf g) (subcube ci.1 ci.2.1) ci.2.2.2.2)
    {i ops depth bank paid c} (h : buildRule g ops depth bank i paid = some c) :
    ValidPool g.mode (vars g.mask) (targetOf g) c := by
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
def forceDatum {α : Type} : Nat → (Nat → α) → α
  | 0, next => next 0
  | n+1, next => next (n+1)
def readSortedHints (data : Nat → Nat) (dict cw d gapBits : Nat) :
    Nat → Nat → Nat → List (Nat × Nat)
  | 0,_,_ => []
  | left+1,st,first =>
    forceDatum st fun pos => forceDatum first fun base =>
    forceDatum (packedAt data pos 32) fun head =>
    forceDatum (Nat.log2 (head ^^^ (head+1))) fun ones =>
    forceDatum (base+(ones <<< gapBits)+packedAt data (pos+ones+1) gapBits) fun key =>
    forceDatum (packedAt data (dict+key*(cw+d)) (cw+d)) fun pair =>
      (pair &&& ((1 <<< cw)-1),pair >>> cw) ::
        readSortedHints data dict cw d gapBits left (pos+ones+1+gapBits) (key+1)
def promoteHints {α : Type} (a b : Nat) (xs : List α) : List α :=
  let rec collect : List α → Nat → List α → List α → List α → List α
    | [],_,first,second,other => first ++ second ++ other.reverse
    | x::tail,i,first,second,other =>
      if i=a then collect tail (i+1) [x] second other
      else if i=b then collect tail (i+1) first [x] other
      else collect tail (i+1) first second (x::other)
  collect xs 0 [] [] []
def forestHints (tab : Packing) (raw i : Nat) : List (Nat × Nat) :=
  let (num,d,cw,dict,flags,ow,marker,data) := tab
  if marker<1024 then
    let start := num*(10*d+raw+d)
    let pos := start+num*ow+packedAt data (start+i*ow) ow
    getPairs data cw d (packedAt data pos 6) (pos+6+marker)
  else
    let off := denseRowStart d raw dict + num*denseRowWidth d flags
    let pairs := off+num*ow
    let priority := decide (4096≤marker)
    let pos := pairs+(marker-(if priority then 4096 else 1024))*(cw+d)+packedAt data (off+i*ow) ow
    let n := packedAt data pos 5
    let gap := packedAt data (pos+5) 3
    if !priority || decide (n≤1) then readSortedHints data pairs cw d gap n (pos+8) 0 else
      let width := (n-1).log2+1
      let a := packedAt data (pos+8) width
      let b := if n=2 then 1-a else packedAt data (pos+8+width) width
      let extra := if n=2 then width else 2*width
      let xs := readSortedHints data pairs cw d gap n (pos+8+extra) 0
      promoteHints a b xs
def stateSet (g : Forest) (k i : Nat) := (readNode g k i).2.2.map Prod.fst
def linkedSet (g : Forest) (k : Nat) (pair : Nat × Nat) : Option (List Sig) :=
  if pair.1 ≥ (g.levels k).1 then none else
    (g.autos[pair.2]?).map fun perm => (stateSet g k pair.1).map (movedWord (perm.map swapRows).reverse)
theorem linkedSet_sound (g : Forest) (k : Nat)
    (names : ∀ x ∈ g.autos, autoOK (targetOf g) (x.map swapRows) = true)
    (earlier : ∀ i < (g.levels k).1, Impossible g.mode (targetOf g) k (stateSet g k i).toFinset)
    {pair out} (h : linkedSet g k pair = some out) :
    Impossible g.mode (targetOf g) k out.toFinset := by
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
  let rules := (forestHints (g.levels k) raw.length i).filterMap (fun (a,b) => buildRule g ops depth bank a b)
  let ls := fun tag => ((g.index k tag).bind (linkedSet g (k-1))).toList
  decide values.Nodup && !(values.contains (targetOf g)) &&
    (if k=0 then true else testAll (k,ws.length,ws,preCov g.mode ws,rules,ls) ws)
theorem nodeVerified_sound (g : Forest) (k i : Nat)
    (samples : properPairs (targetOf g) (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2))
    (cols : ∀ ci ∈ g.cols, Slice g.mode (varsX (rawMask g.mask ci)) (targetOf g) (subcube ci.1 ci.2.1) ci.2.2.2.2)
    (names : ∀ x ∈ g.autos, autoOK (targetOf g) (x.map swapRows) = true)
    (prior : k>0 → ∀ j < (g.levels (k-1)).1, Impossible g.mode (targetOf g) (k-1) (stateSet g (k-1) j).toFinset)
    (checked : nodeVerified g k i = true) : Impossible g.mode (targetOf g) k (stateSet g k i).toFinset := by
  simp only [nodeVerified,Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true',List.contains_eq_mem] at checked
  have hN := checked.1.1
  have hT : targetOf g ∉ stateSet g k i := by simpa [stateSet] using checked.1.2
  by_cases h0 : k=0
  · subst k
    intro t lo h
    have ht : t=0 := by omega
    subst t
    generalize he : (stateSet g 0 i).toFinset = S at h
    obtain ⟨hS,_⟩ := h
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
  (chartSamples g.mask (fun j => (g.samples j).1) == BitVec.allOnes 152) &&
  (chartSamples g.mask (fun j => (g.samples j).2) == 0) &&
  g.cols.all (fun c => colCheck g.mask c prior) &&
  g.autos.all (fun p => autoOK (targetOf g) (p.map swapRows))
theorem forest_all (g : Forest) (top : Nat) (prior : Nat → Nat)
    (lower : ∀ q, Lower g.mode (varsX q) (graphGoal q) (prior q))
    (geometry : graphValid g prior = true) (rows : checkedTables g top) :
    ∀ k ≤ top, ∀ i < (g.levels k).1, Impossible g.mode (targetOf g) k (stateSet g k i).toFinset := by
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
theorem root_index {g top prior k i ws} (low : ∀ q, Lower g.mode (varsX q) (graphGoal q) (prior q))
    (geom : graphValid g prior = true) (blocks : checkedTables g top) (le : k ≤ top)
    (idx : indexedRoot g k i ws = true) : Impossible g.mode (targetOf g) k ws.toFinset := by
  simp only [indexedRoot,Bool.and_eq_true,decide_eq_true_eq] at idx
  rw [←sameWords_sound idx.2]
  exact forest_all g top prior low geom blocks _ le i idx.1
theorem lower_forest {g prior i hints} (low : ∀ q, Lower g.mode (varsX q) (graphGoal q) (prior q))
    (geom : graphValid g prior = true) (blocks : checkedTables g g.cap)
    (idx : indexedRoot g g.cap i (vars g.mask) = true) (hp : properB (targetOf g) = true)
    (ess : checkEssential (targetOf g) (vars g.mask) (graphPairs g.mask hints) = true)
    (all : (graphPairs g.mask hints).map Prod.fst = vars g.mask) :
    Lower g.mode (vars g.mask) (targetOf g) (g.cap+1) := by
  apply lower_impossible (proper_of _ hp) (essential_plain ess).1 (essential_plain ess).2 _ (root_index low geom blocks (Nat.le_refl _) idx)
  intro a ha
  apply essential_ok ess a
  rw [all]
  exact List.mem_toFinset.mpr ha
def Known (u : Bool) (entries : List (Nat × Nat)) := ∀ e ∈ entries, Lower u (varsX e.1) (graphGoal e.1) e.2
def extendKnown (old : List (Nat × Nat)) (L : Nat) (carries : List (Nat × List Nat)) :=
  carries.map (fun v => (v.1,L)) ++ old
theorem extend_ok {u old L m carries} (previous : Known u old)
    (main : Lower u (varsX m) (graphGoal m) L)
    (ok : carries.all (fun v => carryOK v.1 m v.2) = true) :
    Known u (extendKnown old L carries) := by
  intro e he
  rcases List.mem_append.mp he with hx | h
  · obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hx
    exact carry_of (List.all_eq_true.mp ok _ hv) main
  · exact previous e h
theorem baseKnown : Known true [] := by simp [Known]
theorem known_down {u es} (h : Known true es) : Known u es := fun e he => lower_down (h e he)
def lanePlace (v : Nat) (upper : Nat) := 2^153*upper+v
def combineLanes {α : Type} (f : α → Bits) : List α → Nat
  | [] => 0
  | x::xs => lanePlace (f x).toNat (combineLanes f xs)
def units : Nat → Nat
  | 0 => 0
  | n+1 => lanePlace 1 (units n)
theorem laneSmall (x : Bits) : x.toNat < 2^153 :=
  lt_trans x.isLt (by decide +kernel)
theorem place_and (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u &&& lanePlace b.toNat v = lanePlace (a &&& b).toNat (u &&& v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_and,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<153 <;> simp only [h,ite_true,ite_false,BitVec.toNat_and,Nat.testBit_and]
theorem place_or (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u ||| lanePlace b.toNat v = lanePlace (a ||| b).toNat (u ||| v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_or,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<153 <;> simp only [h,ite_true,ite_false,BitVec.toNat_or,Nat.testBit_or]
theorem place_xor (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u ^^^ lanePlace b.toNat v = lanePlace (a ^^^ b).toNat (u ^^^ v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_xor,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<153 <;> simp only [h,ite_true,ite_false,BitVec.toNat_xor,Nat.testBit_xor]
theorem lanes_and {α} (f g : α → Bits) (xs) :
    combineLanes f xs &&& combineLanes g xs = combineLanes (fun x => f x &&& g x) xs := by
  induction xs with
  | nil => simp [combineLanes]
  | cons a xs ih => simp only [combineLanes,place_and,ih]
theorem lanes_or {α} (f g : α → Bits) (xs) :
    combineLanes f xs ||| combineLanes g xs = combineLanes (fun x => f x ||| g x) xs := by
  induction xs with
  | nil => simp [combineLanes]
  | cons a xs ih => simp only [combineLanes,place_or,ih]
theorem lanes_xor {α} (f g : α → Bits) (xs) :
    combineLanes f xs ^^^ combineLanes g xs = combineLanes (fun x => f x ^^^ g x) xs := by
  induction xs with
  | nil => simp [combineLanes]
  | cons a xs ih => simp only [combineLanes,place_xor,ih]
def fullMarks (r packed : Nat) := ((packed+r) >>> 152) &&& r
theorem unit_bit (n i : Nat) (hi : i<n) : (units n).testBit (153*i) = true := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
    rw [units,lanePlace,Nat.testBit_two_pow_mul_add _ (by decide +kernel : 1 < 2^153)]
    cases i with
    | zero => simp
    | succ i =>
      have di : 153*(i+1)-153=153*i := by omega
      have ge : ¬153*(i+1)<153 := by omega
      simp only [ge,ite_false,di]
      exact ih _ (by omega)
set_option maxRecDepth 8192 in
theorem guardBit (a : Bits) : (a.toNat+1).testBit 152 = (a==BitVec.allOnes 152) := by
  by_cases h : a=BitVec.allOnes 152
  · subst a
    decide +kernel
  · have lim := a.isLt
    have ne : a.toNat ≠ 2^152-1 := by
      intro eq
      apply h
      apply BitVec.eq_of_toNat_eq
      simpa only [BitVec.toNat_allOnes] using eq
    have lt : a.toNat+1<2^152 := by omega
    rw [Nat.testBit_eq_false_of_lt lt]
    exact (beq_eq_false_iff_ne.mpr h).symm
set_option maxRecDepth 8192 in
theorem mark_at {α} (f : α → Bits) (xs : List α) (i : Nat) (hi : i<xs.length) :
    (fullMarks (units xs.length) (combineLanes f xs)).testBit (153*i) =
      (f xs[i]==BitVec.allOnes 152) := by
  simp only [fullMarks,Nat.testBit_and,Nat.testBit_shiftRight,unit_bit _ _ hi,Bool.and_true]
  induction xs generalizing i with
  | nil => simp at hi
  | cons a xs ih =>
    simp only [combineLanes,List.length_cons,units,lanePlace]
    have sum (u v x : Nat) : 2^153*u+x+(2^153*v+1)=2^153*(u+v)+(x+1) := by omega
    rw [sum,Nat.testBit_two_pow_mul_add _ (show (f a).toNat+1<2^153 from by have := (f a).isLt; omega)]
    have hi' : i < xs.length+1 := hi
    cases i with
    | zero => simpa using guardBit (f a)
    | succ i =>
      have ge : ¬153*(i+1)+152<153 := by omega
      have di : 153*(i+1)+152-153=153*i+152 := by omega
      simp only [ge,ite_false,di,List.getElem_cons_succ]
      apply ih i (by omega)
abbrev PackedSig := Nat × Nat
abbrev PackedCov := Nat × Nat × Nat
def packedSig {α} (s : α → Signals) (xs : List α) : PackedSig :=
  (combineLanes (fun x => (s x).1) xs,combineLanes (fun x => (s x).2) xs)
def packedCov {α} (c : α → Cov) (xs : List α) : PackedCov :=
  (combineLanes (fun x => (c x).1) xs,combineLanes (fun x => (c x).2.1) xs,
   combineLanes (fun x => (c x).2.2) xs)
def packedColumn (d : Bool) (a : PackedSig) :=
  if d then a.1 ^^^ (a.1 &&& a.2) else a.1 ^^^ a.2
theorem xor_meet (a b : Bits) : a ^^^ (a &&& b) = a &&& ~~~b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_xor,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases b.getLsbD i <;> rfl
theorem packed_column {α} (s : α → Signals) (xs : List α) (d : Bool) :
    packedColumn d (packedSig s xs) = combineLanes (fun x => column d (s x)) xs := by
  cases d <;> simp only [packedColumn,packedSig,column,Bool.false_eq_true,ite_false,ite_true,lanes_and,lanes_xor,xor_meet]
def packedOp (op : Nat) (a b : PackedSig) : PackedSig :=
  if op=0 then (a.1 &&& b.1,a.2 &&& b.2) else if op=1 then (a.1 ||| b.1,a.2 ||| b.2)
  else if op=2 then (a.1 ^^^ (a.1 &&& b.1),a.2 ^^^ (a.2 &&& b.2))
  else (b.1 ^^^ (b.1 &&& a.1),b.2 ^^^ (b.2 &&& a.2))
theorem packed_op {α} (a b : α → Decor) (xs : List α) (op : Nat) :
    packedOp op (packedSig (fun x => (a x).2) xs) (packedSig (fun x => (b x).2) xs) =
    packedSig (fun x => (dbin op (a x) (b x)).2) xs := by
  by_cases h0 : op=0
  · simp only [packedOp,h0,ite_true,packedSig,lanes_and,dbin,bv]
  by_cases h1 : op=1
  · simp [packedOp,h1,packedSig,lanes_or,dbin,bv]
  by_cases h2 : op=2
  · simp [packedOp,h2,packedSig,lanes_and,lanes_xor,xor_meet,dbin,bv]
  · have e (x y : Bits) : ~~~x &&& y = y &&& ~~~x := BitVec.and_comm _ _
    simp only [packedOp,h0,h1,h2,ite_false,packedSig,lanes_and,lanes_xor,xor_meet,dbin,bv,e]
def takePacked (c : PackedCov) (a b : Nat) (ka kb : Bool) :=
  let without1 := fun w => c.1 ^^^ (c.1 &&& (c.2.1 &&& w))
  let without2 := c.1 ^^^ (c.1 &&& ((c.2.1 &&& (a ||| b)) ||| (c.2.2 &&& (a &&& b))))
  if ka then (if kb then c.1 else without1 b)
  else if kb then without1 a else without2
theorem takePacked_ok {α} (c : α → Cov) (a b : α → Bits) (xs : List α) (ka kb : Bool) :
    takePacked (packedCov c xs) (combineLanes a xs) (combineLanes b xs) ka kb =
    combineLanes (fun x => restCov (c x) (a x) (b x) ka kb) xs := by
  cases ka <;> cases kb <;>
    simp only [takePacked,packedCov,lanes_and,lanes_or,lanes_xor,xor_meet,restCov,takeOne,takeTwo,
      Bool.false_eq_true,ite_false,ite_true]
def contextWire (c : NodeContext) (i : Nat) := c.2.2.1.getD i defaultDecor
def checkAt (c : NodeContext) (i j op : Nat) (ka kb : Bool) :=
  let a := contextWire c i
  let b := contextWire c j
  evalMove c op a b (dbin op a b) ka kb
def combField (c : NodeContext) (d ka kb : Bool) (op i j : Nat) :=
  let a := contextWire c i
  let b := contextWire c j
  restCov c.2.2.2.1.1 (column d a.2) (column d b.2) ka kb |||
    column d (dbin op a b).2
def onMarks {α : Type} (f : α → Bool) (mask : Nat) : List α → Bool
  | [] => true
  | x::xs => if mask=0 then true else
    ((mask &&& 1 == 0) || f x) && onMarks f (mask >>> 153) xs
theorem marked_ok {α} (f : α → Bool) (mask : Nat) (xs : List α) (i : Nat) (hi : i<xs.length)
    (bitOn : mask.testBit (153*i)=true) (ok : onMarks f mask xs=true) : f xs[i]=true := by
  induction xs generalizing mask i with
  | nil => simp at hi
  | cons x xs ih =>
    have ne : mask≠0 := by intro e; simp [e] at bitOn
    simp only [onMarks,ne,ite_false,Bool.and_eq_true,Bool.or_eq_true,beq_iff_eq] at ok
    cases i with
    | zero =>
      have nonzero : mask &&& 1 ≠ 0 := by
        intro he
        have at0 := congrArg (fun n : Nat => n.testBit 0) he
        simp only [Nat.testBit_and] at at0
        change mask.testBit 0=true at bitOn
        simp [bitOn] at at0
      exact ok.1.resolve_left nonzero
    | succ i =>
      apply ih (mask:=mask >>> 153) (i:=i) (by simpa using hi) _ ok.2
      simpa only [Nat.testBit_shiftRight,Nat.mul_succ,Nat.add_comm] using bitOn
abbrev Batch := Nat × Nat × Nat × List PackedSig × PackedCov
def makeBatch (k n : Nat) (xs : List NodeContext) : Batch :=
  (k,n,units xs.length,(List.range n).map (fun i => packedSig (fun c => (contextWire c i).2) xs),
    packedCov (fun c => c.2.2.2.1.1) xs)
def laneWire (b : Batch) (i : Nat) := b.2.2.2.1.getD i (0,0)
theorem laneWire_at (k n) (xs) {i : Nat} (h : i<n) :
    laneWire (makeBatch k n xs) i = packedSig (fun c => (contextWire c i).2) xs := by
  simp [laneWire,makeBatch,List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_range,h]
theorem masked_comp (d x : Sig) : masked d (neg x) = d ^^^ masked d x := by
  apply bit_ext
  intro r
  simp only [masked,neg,bit,BitVec.getLsbD_and,BitVec.getLsbD_not,BitVec.getLsbD_xor,r.isLt,decide_true,Bool.true_and]
  cases d.getLsbD r.val <;> cases x.getLsbD r.val <;> rfl
def constantLoss (p : Decor → Bool) (a : Decor) (keep : Bool) :=
  if keep then 0 else (p a).toNat
theorem lossBound (p : Decor → Bool) (ws : List Decor) (a : Decor) (keep : Bool) :
    ws.countP p ≤ (delOne ws a keep).countP p + constantLoss p a keep := by
  cases keep
  · simp only [delOne,Bool.false_eq_true,ite_false,constantLoss,List.countP_erase]
    split
    next h => simp [h.2]; omega
    next => omega
  · simp [delOne,constantLoss]
theorem keptCount (p : Decor → Bool) (ws : List Decor) (a b : Decor) (ka kb : Bool) :
    ws.countP p - constantLoss p a ka - constantLoss p b kb ≤
    (delTwo ws a b ka kb).countP p := by
  have h1 := lossBound p ws a ka
  have h2 := lossBound p (delOne ws a ka) b kb
  simp only [delTwo]
  omega
noncomputable def force {β : Type} (n : Nat) (f : Nat → β) : β := Nat.rec (f 0) (fun k _ => f (Nat.succ k)) n
theorem force_eq {β : Type} (n : Nat) (f : Nat → β) : force n f = f n := by cases n <;> rfl
noncomputable def forceMap {α β : Type} (f : α → Nat) (l : List α) : (List Nat → β) → β :=
  List.rec (fun k => k []) (fun a _ ih k => force (f a) fun x => ih fun xs => k (x::xs)) l
theorem forceMap_eq {α β : Type} (f : α → Nat) (l : List α) (k : List Nat → β) : forceMap f l k = k (l.map f) := by
  induction l generalizing k with
  | nil => rfl
  | cons a l ih =>
    change force (f a) (fun x => forceMap f l fun xs => k (x::xs)) = _
    rw [force_eq,ih]
    rfl
def nmask (d : Nat) (a : Sig) : Nat := Nat.land a.toNat d
noncomputable def anyEq (m : Nat) (l : List Nat) : Bool := List.rec false (fun v _ ih => or (Nat.beq m v) ih) l
def nconst (d m : Nat) : Bool := or (Nat.beq m 0) (Nat.beq m d)
noncomputable def navail (u : Bool) (d : Nat) (pm : List Nat) (m : Nat) : Bool :=
  or (or (nconst d m) (anyEq m pm)) (and u (anyEq (Nat.xor d m) pm))
theorem nmask_eq (d a : Sig) : nmask d.toNat a = (masked d a).toNat := (BitVec.toNat_and _ _).symm
theorem beq_toNat (a b : Sig) : Nat.beq a.toNat b.toNat = (a==b) := by
  rw [Bool.eq_iff_iff,Nat.beq_eq,beq_iff_eq]
  exact BitVec.toNat_inj
theorem nconst_eq (d a : Sig) : nconst d.toNat (nmask d.toNat a) = isMaskedConstant d a := by
  rw [nmask_eq]
  have e : Nat.beq (masked d a).toNat 0 = (masked d a == zero) := by
    have z0 : zero.toNat=0 := by simp [zero]
    rw [←beq_toNat,z0]
  rw [nconst,e,beq_toNat]
  rfl
theorem anyEq_eq (x d : Sig) (pool : List Sig) : anyEq x.toNat (pool.map (nmask d.toNat)) = (pool.map (masked d)).any (fun v => v==x) := by
  induction pool with
  | nil => rfl
  | cons a l ih =>
    change or (Nat.beq x.toNat (nmask d.toNat a)) (anyEq x.toNat (l.map (nmask d.toNat))) = _
    rw [ih,nmask_eq,beq_toNat,List.map_cons,List.any_cons,Bool.beq_comm]
theorem navail_eq (u : Bool) (d a : Sig) (pool : List Sig) :
    navail u d.toNat (pool.map (nmask d.toNat)) (nmask d.toNat a) = availableB u d pool a := by
  have x : Nat.xor d.toNat (masked d a).toNat = (masked d (neg a)).toNat := by
    rw [masked_comp]
    exact (BitVec.toNat_xor _ _).symm
  rw [navail,nconst_eq,nmask_eq,x,anyEq_eq,anyEq_eq]
  simp only [availableB,isMaskedConstant]
def unav (u : Bool) (p : BoundPool) (w : Decor) : Nat := cond (availableB u p.domain p.wires w.1) 0 1
def slowCost (u : Bool) (p : BoundPool) (ws : List Decor) (k : Nat) (a b : Decor) (op : Nat) (ka kb : Bool) : Bool :=
  let const := fun w : Decor => isMaskedConstant p.domain w.1
  let z := bin op a.1 b.1
  let cm := ws.countP const - constantLoss const a ka - constantLoss const b kb + (isMaskedConstant p.domain z).toNat
  (((ws.map (unav u p)).sum == cond ka 0 (unav u p a) + cond kb 0 (unav u p b)) &&
    decide (k+p.paid+(!availableB u p.domain p.wires z).toNat < p.bound+cm)) &&
    (availableB u p.domain p.wires z || (availableB u p.domain p.wires a.1 && availableB u p.domain p.wires b.1))
def zN (op x y : Nat) : Nat := cond (Nat.beq op 0) (Nat.land x y) (cond (Nat.beq op 1) (Nat.lor x y)
  (cond (Nat.beq op 2) (Nat.xor x (Nat.land x y)) (Nat.xor y (Nat.land x y))))
theorem zN_eq (op : Nat) (d a b : Sig) : zN op (nmask d.toNat a) (nmask d.toNat b) = nmask d.toNat (bin op a b) := by
  have tn (x y : Sig) : Nat.land x.toNat y.toNat = (x &&& y).toNat := (BitVec.toNat_and x y).symm
  have tx (x y : Sig) : Nat.xor x.toNat y.toNat = (x ^^^ y).toNat := (BitVec.toNat_xor x y).symm
  have tor (x y : Sig) : Nat.lor x.toNat y.toNat = (x ||| y).toNat := (BitVec.toNat_or x y).symm
  simp only [nmask_eq]
  unfold zN
  by_cases h0 : op=0
  · subst h0
    change Nat.land _ _ = _
    rw [tn]
    congr 1
    apply bit_ext
    intro r
    simp only [masked,bin,bit,ite_true,BitVec.getLsbD_and]
    cases a.getLsbD r.val <;> cases b.getLsbD r.val <;> cases d.getLsbD r.val <;> rfl
  by_cases h1 : op=1
  · subst h1
    change Nat.lor _ _ = _
    rw [tor]
    congr 1
    apply bit_ext
    intro r
    simp only [masked,bin,bit,Nat.one_ne_zero,ite_true,ite_false,BitVec.getLsbD_and,BitVec.getLsbD_or]
    cases a.getLsbD r.val <;> cases b.getLsbD r.val <;> cases d.getLsbD r.val <;> rfl
  have e0 : Nat.beq op 0=false := Bool.eq_false_iff.mpr (fun h => h0 (Nat.eq_of_beq_eq_true h))
  have e1 : Nat.beq op 1=false := Bool.eq_false_iff.mpr (fun h => h1 (Nat.eq_of_beq_eq_true h))
  by_cases h2 : op=2
  · subst h2
    change Nat.xor _ (Nat.land _ _) = _
    rw [tn,tx]
    congr 1
    apply bit_ext
    intro r
    simp only [masked,bin,bit,OfNat.ofNat_ne_zero,OfNat.ofNat_ne_one,ite_true,ite_false,BitVec.getLsbD_and,BitVec.getLsbD_xor,BitVec.getLsbD_not,r.isLt,decide_true,Bool.true_and]
    cases a.getLsbD r.val <;> cases b.getLsbD r.val <;> cases d.getLsbD r.val <;> rfl
  have e2 : Nat.beq op 2=false := Bool.eq_false_iff.mpr (fun h => h2 (Nat.eq_of_beq_eq_true h))
  rw [e0,e1,e2]
  change Nat.xor _ (Nat.land _ _) = _
  rw [tn,tx]
  congr 1
  apply bit_ext
  intro r
  simp only [masked,bin,bit,h0,h1,h2,ite_false,BitVec.getLsbD_and,BitVec.getLsbD_xor,BitVec.getLsbD_not,r.isLt,decide_true,Bool.true_and]
  cases a.getLsbD r.val <;> cases b.getLsbD r.val <;> cases d.getLsbD r.val <;> rfl
def nloss (d x : Nat) (keep : Bool) : Nat := cond keep 0 (cond (nconst d x) 1 0)
theorem nloss_eq (d : Sig) (a : Decor) (keep : Bool) :
    nloss d.toNat (nmask d.toNat a.1) keep = constantLoss (fun w : Decor => isMaskedConstant d w.1) a keep := by
  rw [nloss,nconst_eq,constantLoss]
  cases keep
  · cases isMaskedConstant d a.1 <;> rfl
  · rfl
abbrev QS := Nat × Nat × Nat × Nat × Nat × List Nat × List Nat × Bool
noncomputable def quickSpec (u : Bool) (k : Nat) (ws : List Decor) (p : BoundPool) : QS :=
  let d := p.domain.toNat
  let ms := ws.map (fun w : Decor => nmask d w.1)
  (d,ms.countP (nconst d),p.bound,Nat.add k p.paid,(ms.map fun m => cond (navail u d (p.wires.map (nmask d)) m) 0 1).sum,ms,p.wires.map (nmask d),u)
noncomputable def forceBool {β : Type} (b : Bool) (f : Bool → β) : β := Bool.rec (f false) (f true) b
noncomputable def forcePool {β : Type} (u : Bool) (k : Nat) (ws : List Decor) (p : BoundPool) (f : QS → β) : β :=
  force p.domain.toNat fun d => forceMap (nmask d) p.wires fun pm => forceMap (fun w : Decor => nmask d w.1) ws fun ms =>
  force (ms.countP (nconst d)) fun c => force p.bound fun l => force (Nat.add k p.paid) fun t =>
  force (ms.map fun m => cond (navail u d pm m) 0 1).sum fun v => forceBool u fun u => f (d,c,l,t,v,ms,pm,u)
theorem forcePool_eq {β : Type} (u k ws p) (f : QS → β) : forcePool u k ws p f = f (quickSpec u k ws p) := by
  have e (b : Bool) (f : Bool → β) : forceBool b f = f b := by cases b <;> rfl
  simp only [forcePool,force_eq,forceMap_eq,e]
  rfl
noncomputable def forcePools {β : Type} (u : Bool) (k : Nat) (ws : List Decor) (ps : List BoundPool) : (List QS → β) → β :=
  List.rec (fun f => f []) (fun p _ ih f => forcePool u k ws p fun q => ih fun qs => f (q::qs)) ps
theorem forcePools_eq {β : Type} (u k ws ps) (f : List QS → β) : forcePools u k ws ps f = f (ps.map (quickSpec u k ws)) := by
  induction ps generalizing f with
  | nil => rfl
  | cons p ps ih =>
    change forcePool u k ws p (fun q => forcePools u k ws ps fun qs => f (q::qs)) = _
    rw [forcePool_eq,ih]
    rfl
def kwN (v : Nat) : Nat :=
  let n := v % 2305843009213693921
  (n*(n+971)) % 2305843009213693921
abbrev Lane := NodeContext × Nat × Nat × List QS × List Nat × Nat
noncomputable def laneOf (c : NodeContext) : Lane :=
  let ws := c.2.2.1.map (fun w : Decor => w.1.toNat)
  (c,c.2.2.1.length,cond c.2.2.2.1.2 4 2,c.2.2.2.2.1.map (quickSpec c.2.2.2.1.2 (c.1-1) c.2.2.1),ws,(ws.map kwN).sum)
noncomputable def forceLanes {β : Type} (cs : List NodeContext) : (List Lane → β) → β :=
  List.rec (fun f => f []) (fun c _ ih f => force c.2.2.1.length fun n => force (cond c.2.2.2.1.2 4 2) fun l =>
    forceMap (fun w : Decor => w.1.toNat) c.2.2.1 fun ws => force (ws.map kwN).sum fun t =>
    forcePools c.2.2.2.1.2 (c.1-1) c.2.2.1 c.2.2.2.2.1 fun qs => ih fun ys => f ((c,n,l,qs,ws,t)::ys)) cs
theorem forceLanes_eq {β : Type} (cs) (f : List Lane → β) : forceLanes cs f = f (cs.map laneOf) := by
  induction cs generalizing f with
  | nil => rfl
  | cons c cs ih =>
    change force c.2.2.1.length (fun n => force (cond c.2.2.2.1.2 4 2) fun l =>
      forceMap (fun w : Decor => w.1.toNat) c.2.2.1 fun ws => force (ws.map kwN).sum fun t =>
      forcePools c.2.2.2.1.2 (c.1-1) c.2.2.1 c.2.2.2.2.1 fun qs => forceLanes cs fun ys => f ((c,n,l,qs,ws,t)::ys)) = _
    rw [force_eq,force_eq,forceMap_eq,force_eq,forcePools_eq,ih]
    rfl
noncomputable def fastCost (s : QS) (i j op : Nat) (ka kb : Bool) : Bool :=
  force (s.2.2.2.2.2.1.getD i 0) fun x => force (s.2.2.2.2.2.1.getD j 0) fun y =>
  let av := navail s.2.2.2.2.2.2.2 s.1 s.2.2.2.2.2.2.1
  let hi := Nat.add s.2.2.1 (Nat.sub (Nat.sub s.2.1 (nloss s.1 x ka)) (nloss s.1 y kb))
  let lo := s.2.2.2.1
  and (Nat.beq s.2.2.2.2.1 (Nat.add (cond ka 0 (cond (av x) 0 1)) (cond kb 0 (cond (av y) 0 1))))
  (cond (Nat.ble (Nat.succ lo) hi)
    (force (zN op x y) fun z => or (av z) (and (Nat.ble (Nat.add lo 2) hi) (and (av x) (av y))))
    (cond (Nat.ble lo hi) (nconst s.1 (zN op x y)) false))
theorem spec_get {d : Nat} (ws : List Decor) (i : Nat) (hd : nmask d zero=0) :
    (ws.map (fun w : Decor => nmask d w.1)).getD i 0 = nmask d (ws.getD i defaultDecor).1 := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases ws[i]? with
  | none => exact hd.symm
  | some v => rfl
theorem fast_slow {u k p ws i j op ka kb} (h : fastCost (quickSpec u k ws p) i j op ka kb=true) :
    slowCost u p ws k (ws.getD i defaultDecor) (ws.getD j defaultDecor) op ka kb=true := by
  have z0 : nmask p.domain.toNat zero=0 := by
    have : zero.toNat=0 := by simp [zero]
    simp [nmask,this]
  have su : (((ws.map (fun w : Decor => nmask p.domain.toNat w.1)).map fun m => cond (navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat)) m) 0 1).sum) =
      (ws.map (unav u p)).sum := by
    rw [List.map_map]
    refine congrArg List.sum (List.map_congr_left ?_)
    intro w _
    change cond (navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat)) (nmask p.domain.toNat w.1)) 0 1 = _
    rw [navail_eq]
    rfl
  simp only [fastCost,quickSpec,force_eq,spec_get _ _ z0,su,List.countP_map,Function.comp_def,nconst_eq] at h
  generalize ws.getD i defaultDecor=a at h ⊢
  generalize ws.getD j defaultDecor=b at h ⊢
  replace h : and (Nat.beq (ws.map (unav u p)).sum (Nat.add (cond ka 0 (cond ((navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat))) (nmask p.domain.toNat a.1)) 0 1)) (cond kb 0 (cond ((navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat))) (nmask p.domain.toNat b.1)) 0 1))))
   (cond (Nat.ble (Nat.succ (Nat.add k p.paid)) (Nat.add p.bound (Nat.sub (Nat.sub (ws.countP (fun w : Decor => isMaskedConstant p.domain w.1)) (nloss p.domain.toNat (nmask p.domain.toNat a.1) ka)) (nloss p.domain.toNat (nmask p.domain.toNat b.1) kb))))
    (or ((navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat))) (zN op (nmask p.domain.toNat a.1) (nmask p.domain.toNat b.1))) (and (Nat.ble (Nat.add (Nat.add k p.paid) 2) (Nat.add p.bound (Nat.sub (Nat.sub (ws.countP (fun w : Decor => isMaskedConstant p.domain w.1)) (nloss p.domain.toNat (nmask p.domain.toNat a.1) ka)) (nloss p.domain.toNat (nmask p.domain.toNat b.1) kb)))) (and ((navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat))) (nmask p.domain.toNat a.1)) ((navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat))) (nmask p.domain.toNat b.1)))))
    (cond (Nat.ble (Nat.add k p.paid) (Nat.add p.bound (Nat.sub (Nat.sub (ws.countP (fun w : Decor => isMaskedConstant p.domain w.1)) (nloss p.domain.toNat (nmask p.domain.toNat a.1) ka)) (nloss p.domain.toNat (nmask p.domain.toNat b.1) kb)))) (nconst p.domain.toNat (zN op (nmask p.domain.toNat a.1) (nmask p.domain.toNat b.1))) false)) = true := h
  rw [zN_eq,nconst_eq,navail_eq,navail_eq,navail_eq,nloss_eq,nloss_eq] at h
  have ca : isMaskedConstant p.domain (bin op a.1 b.1)=true → availableB u p.domain p.wires (bin op a.1 b.1)=true := by
    intro zc
    simp only [availableB,isMaskedConstant,Bool.or_eq_true] at zc ⊢
    exact Or.inl (Or.inl zc)
  simp only [Nat.add_eq,Nat.sub_eq,Nat.succ_eq_add_one,Bool.and_eq_true,Nat.beq_eq] at h
  obtain ⟨hu,h⟩ := h
  simp only [slowCost,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq]
  refine ⟨⟨hu,?_⟩,?_⟩
  all_goals
    generalize ws.countP (fun w => isMaskedConstant p.domain w.1) - constantLoss (fun w : Decor => isMaskedConstant p.domain w.1) a ka -
      constantLoss (fun w : Decor => isMaskedConstant p.domain w.1) b kb = c at h ⊢
    generalize isMaskedConstant p.domain (bin op a.1 b.1)=r at h ca ⊢
    generalize availableB u p.domain p.wires (bin op a.1 b.1)=q at h ca ⊢
    cases h1 : Nat.ble (k+p.paid+1) (p.bound+c)
    · rw [h1] at h
      cases h2 : Nat.ble (k+p.paid) (p.bound+c)
      · simp [h2] at h
      · have := Nat.ble_eq.mp h2
        simp only [h2,cond_true,cond_false] at h
        subst h
        rw [ca rfl]
        simp <;> omega
    · rw [h1] at h
      have l1 := Nat.ble_eq.mp h1
      simp only [cond_true,Bool.or_eq_true,Bool.and_eq_true,Nat.ble_eq] at h
      rcases h with rfl | ⟨l2,ha,hb⟩
      · simp <;> omega
      · first
        | (have : (!q).toNat ≤ 1 := Bool.toNat_le _
           omega)
        | simp [ha,hb]
theorem anyEq_iff (m : Nat) (l : List Nat) : anyEq m l=true ↔ m ∈ l := by
  induction l with
  | nil => simp [anyEq]
  | cons a l ih =>
    change or (Nat.beq m a) (anyEq m l)=true ↔ _
    rw [Bool.or_eq_true,ih,Nat.beq_eq,List.mem_cons]
noncomputable def linkAt (fl : Nat → Option (List Nat)) (l : Lane) (i j op : Nat) (ka kb : Bool) : Bool :=
  force (l.2.2.2.2.1.getD i 0) fun x => force (l.2.2.2.2.1.getD j 0) fun y => force (zN op x y) fun z =>
  Option.rec false (fun ys => forceMap (fun v => v) ys fun ys =>
    and (anyEq z ys) (and (l.2.2.2.2.1.all fun v => or (and (not ka) (Nat.beq v x)) (or (and (not kb) (Nat.beq v y)) (anyEq v ys)))
      (ys.all fun v => or (Nat.beq v z) (and (and (or ka (not (Nat.beq v x))) (or kb (not (Nat.beq v y)))) (anyEq v l.2.2.2.2.1)))))
    (fl (Nat.add (kwN z) (Nat.sub (Nat.sub l.2.2.2.2.2 (cond ka 0 (kwN x))) (cond kb 0 (kwN y)))))
theorem keySet_sum (xs : List Sig) : keySet xs = (xs.map keyWord).sum := by
  have go (a : Nat) : xs.foldl (fun v x => v+keyWord x) a = a+(xs.map keyWord).sum := by
    induction xs generalizing a with
    | nil => rfl
    | cons x xs ih => rw [List.foldl_cons,ih,List.map_cons,List.sum_cons,Nat.add_assoc]
  exact (go 0).trans (Nat.zero_add _)
theorem delTwo_sum (f : Decor → Nat) {ws : List Decor} {a b : Decor} (ha : a ∈ ws) (hb : b ∈ ws) (ne : a≠b) (ka kb : Bool) :
    ((delTwo ws a b ka kb).map f).sum = (ws.map f).sum - (cond ka 0 (f a)) - (cond kb 0 (f b)) := by
  have er {l : List Decor} {x : Decor} (hx : x ∈ l) : (l.map f).sum = f x + ((l.erase x).map f).sum := by
    have := ((List.perm_cons_erase hx).map f).sum_eq
    rwa [List.map_cons,List.sum_cons] at this
  have hm : b ∈ ws.erase a := (List.mem_erase_of_ne (Ne.symm ne)).mpr hb
  have e1 := er ha
  have e2 := er hb
  have e3 := er hm
  cases ka <;> cases kb <;> simp only [delTwo,delOne,Bool.false_eq_true,ite_true,ite_false,cond_true,cond_false] <;> omega
theorem fastCost_good {u p k ws a b op ka kb} (ha : a∈ws) (hb : b∈ws) (ne : a≠b) (al : allowedB u op=true)
    (h : slowCost u p ws k a b op ka kb=true) :
    scalarPoolCut u p k ((delTwo ws a b ka kb).map Prod.fst) (movedChoice op a b)=true := by
  let const := fun w : Decor => isMaskedConstant p.domain w.1
  let z := bin op a.1 b.1
  let rest := delTwo ws a b ka kb
  have ck := keptCount const ws a b ka kb
  change ws.countP const - constantLoss const a ka - constantLoss const b kb ≤ rest.countP const at ck
  simp only [slowCost,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at h
  obtain ⟨⟨hu,hc⟩,hz⟩ := h
  have sum := delTwo_sum (unav u p) ha hb ne ka kb
  rw [hu] at sum
  have zs : ((delTwo ws a b ka kb).map (unav u p)).sum=0 := by omega
  have hs : (rest.map Prod.fst).all (availableB u p.domain p.wires)=true := by
    apply List.all_eq_true.mpr
    intro _ hm
    obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hm
    have v := List.sum_eq_zero_iff.mp zs _ (List.mem_map_of_mem hw)
    cases e : availableB u p.domain p.wires w.1
    · simp [unav,e] at v
    · rfl
  have opOK : (!(!availableB u p.domain p.wires z) || choiceOK u p.domain p.wires (movedChoice op a b))=true := by
    simp only [Bool.or_eq_true,Bool.and_eq_true] at hz
    rcases hz with hz | ⟨x,y⟩
    · simp [z,hz]
    · simp [choiceOK,movedChoice,x,y,al]
  change k+p.paid+(!availableB u p.domain p.wires z).toNat < p.bound+(ws.countP const - constantLoss const a ka -
        constantLoss const b kb+(isMaskedConstant p.domain z).toNat) at hc
  dsimp only [rest] at hs
  have ez : choiceVal (movedChoice op a b)=z := rfl
  simp only [scalarPoolCut,ez,hs,opOK,Bool.and_true,decide_eq_true_eq,List.countP_cons,
      List.countP_map,Function.comp_def]
  change k+p.paid+(!availableB u p.domain p.wires z).toNat <
      p.bound+(rest.countP const + if isMaskedConstant p.domain z then 1 else 0)
  cases hc' : isMaskedConstant p.domain z <;> simp [hc'] at hc ⊢ <;> omega
theorem zN_full (op : Nat) (a b : Sig) : zN op a.toNat b.toNat = (bin op a b).toNat := by
  have e (v : Sig) : nmask one.toNat v = v.toNat := by
    rw [nmask_eq]
    congr 1
    exact BitVec.and_allOnes
  have := zN_eq op one a b
  rwa [e,e,e] at this
theorem getW (ws : List Decor) (i : Nat) :
    (ws.map (fun w : Decor => w.1.toNat)).getD i 0 = (ws.getD i defaultDecor).1.toNat := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases ws[i]? with
  | none =>
    have z0 : zero.toNat=0 := by simp [zero]
    exact z0.symm
  | some v => rfl
theorem wire_ne {c : NodeContext} {i j} (nd : (c.2.2.1.map Prod.fst).Nodup)
    (hi : i<c.2.2.1.length) (hj : j<c.2.2.1.length) (hij : i≠j) : (contextWire c i).1 ≠ (contextWire c j).1 := by
  have gi : contextWire c i = c.2.2.1[i] := by simp [contextWire,List.getD_eq_getElem?_getD,hi]
  have gj : contextWire c j = c.2.2.1[j] := by simp [contextWire,List.getD_eq_getElem?_getD,hj]
  rw [gi,gj]
  intro e
  apply hij
  apply (List.Nodup.getElem_inj_iff nd (hi:=by simpa using hi) (hj:=by simpa using hj)).mp
  simpa using e
theorem link_sound {c : NodeContext} {fl i j op ka kb} (nd : (c.2.2.1.map Prod.fst).Nodup)
    (hfl : ∀ tag ys, fl tag=some ys → ∃ xs ∈ c.2.2.2.2.2 tag, ys=xs.map BitVec.toNat)
    (hi : i<c.2.2.1.length) (hj : j<c.2.2.1.length) (hij : i≠j) (h : linkAt fl (laneOf c) i j op ka kb=true) :
    (c.2.2.2.2.2 (keySet (choiceVal (movedChoice op (contextWire c i) (contextWire c j)) ::
      (delTwo c.2.2.1 (contextWire c i) (contextWire c j) ka kb).map Prod.fst))).any (sameWords
      (choiceVal (movedChoice op (contextWire c i) (contextWire c j)) ::
      (delTwo c.2.2.1 (contextWire c i) (contextWire c j) ka kb).map Prod.fst))=true := by
  have mem (t) (ht : t<c.2.2.1.length) : contextWire c t ∈ c.2.2.1 := by
    simp [contextWire,List.getD_eq_getElem?_getD,ht]
  have hne := wire_ne nd hi hj hij
  have ha := mem i hi
  have hb := mem j hj
  have hab : contextWire c i ≠ contextWire c j := fun e => hne (congrArg Prod.fst e)
  have kv (v : Sig) := kept_value nd ha hb ka kb v
  have sum := delTwo_sum (fun w : Decor => keyWord w.1) ha hb hab ka kb
  have wi : contextWire c i = c.2.2.1.getD i defaultDecor := rfl
  have wj : contextWire c j = c.2.2.1.getD j defaultDecor := rfl
  simp only [linkAt,laneOf,force_eq,getW,←wi,←wj,zN_full] at h
  generalize contextWire c i=a at *
  generalize contextWire c j=b at *
  change Option.rec false _ (fl (keyWord (bin op a.1 b.1)+(((c.2.2.1.map (fun w : Decor => w.1.toNat)).map kwN).sum -
    (cond ka 0 (keyWord a.1)) - (cond kb 0 (keyWord b.1)))))=true at h
  have tot : ((c.2.2.1.map (fun w : Decor => w.1.toNat)).map kwN).sum = (c.2.2.1.map (fun w : Decor => keyWord w.1)).sum := by
    rw [List.map_map]
    rfl
  rw [tot,←sum] at h
  have tag : keySet (choiceVal (movedChoice op a b) :: (delTwo c.2.2.1 a b ka kb).map Prod.fst) =
      keyWord (bin op a.1 b.1)+((delTwo c.2.2.1 a b ka kb).map (fun w : Decor => keyWord w.1)).sum := by
    rw [keySet_sum,List.map_cons,List.sum_cons,List.map_map]
    rfl
  rw [←tag] at h
  generalize keySet (choiceVal (movedChoice op a b) :: (delTwo c.2.2.1 a b ka kb).map Prod.fst)=t at h ⊢
  cases hf : fl t with
  | none => simp [hf] at h
  | some ys =>
    obtain ⟨xs,hx,rfl⟩ := hfl t ys hf
    rw [hf] at h
    simp only [forceMap_eq,List.map_id',Bool.and_eq_true,List.all_eq_true,Bool.or_eq_true,anyEq_iff,Nat.beq_eq,Bool.not_eq_true'] at h
    obtain ⟨h1,h2,h3⟩ := h
    have back {v : Sig} (hv : v.toNat ∈ xs.map BitVec.toNat) : v ∈ xs := by
      obtain ⟨w,hw,e⟩ := List.mem_map.mp hv
      exact BitVec.toNat_inj.mp e ▸ hw
    apply List.any_eq_true.mpr
    refine ⟨xs,hx,?_⟩
    simp only [sameWords,Bool.and_eq_true,List.all_eq_true,List.contains_eq_mem,decide_eq_true_eq]
    constructor
    · intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact back h1
      · obtain ⟨hw,va,vb⟩ := (kv v).mp hv
        obtain ⟨w,hm,rfl⟩ := List.mem_map.mp hw
        rcases h2 _ (List.mem_map_of_mem hm) with ⟨x,y⟩ | ⟨x,y⟩ | x
        · rcases va with va | va
          · exact absurd (BitVec.toNat_inj.mp y) va
          · simp [va] at x
        · rcases vb with vb | vb
          · exact absurd (BitVec.toNat_inj.mp y) vb
          · simp [vb] at x
        · exact back x
    · intro v hv
      rcases h3 _ (List.mem_map_of_mem hv) with x | ⟨⟨x,y⟩,m⟩
      · exact List.mem_cons.mpr (Or.inl (BitVec.toNat_inj.mp x))
      · refine List.mem_cons_of_mem _ ((kv v).mpr ⟨?_,?_,?_⟩)
        · obtain ⟨w,hw,e⟩ := List.mem_map.mp m
          exact BitVec.toNat_inj.mp e ▸ List.mem_map_of_mem hw
        · rcases x with x | x
          · exact Or.inr x
          · refine Or.inl fun e => ?_
            subst e
            simp at x
        · rcases y with x | x
          · exact Or.inr x
          · refine Or.inl fun e => ?_
            subst e
            simp at x
noncomputable def fallbackAt (fl : Nat → Option (List Nat)) (l : Lane) (i j op : Nat) (ka kb : Bool) : Bool :=
  or (and (and (Nat.ble (Nat.succ i) l.2.1) (and (Nat.ble (Nat.succ j) l.2.1) (and (Nat.ble (Nat.succ op) l.2.2.1) (not (Nat.beq i j)))))
    (or (l.2.2.2.1.any fun s => fastCost s i j op ka kb) (linkAt fl l i j op ka kb))) (checkAt l.1 i j op ka kb)
theorem fallback_sound {c : NodeContext} {fl i j op ka kb} (nd : (c.2.2.1.map Prod.fst).Nodup)
    (hfl : ∀ tag ys, fl tag=some ys → ∃ xs ∈ c.2.2.2.2.2 tag, ys=xs.map BitVec.toNat)
    (h : fallbackAt fl (laneOf c) i j op ka kb=true) :
    checkAt c i j op ka kb=true := by
  simp only [fallbackAt,Bool.or_eq_true,Bool.and_eq_true] at h
  rcases h with ⟨⟨hi,hj,ho,hn⟩,h | h⟩ | h
  · have hi := Nat.ble_eq.mp hi
    have hj := Nat.ble_eq.mp hj
    have ho := Nat.ble_eq.mp ho
    change Nat.succ i ≤ c.2.2.1.length at hi
    change Nat.succ j ≤ c.2.2.1.length at hj
    change Nat.succ op ≤ cond c.2.2.2.1.2 4 2 at ho
    have al : allowedB c.2.2.2.1.2 op=true := by
      cases hu : c.2.2.2.1.2 <;> simp [hu] at ho <;> simp [allowedB] <;> omega
    have mem (t) (ht : t<c.2.2.1.length) : contextWire c t ∈ c.2.2.1 := by
      simp [contextWire,List.getD_eq_getElem?_getD,ht]
    obtain ⟨_,hm,ok⟩ := List.any_eq_true.mp h
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hm
    have hne := wire_ne nd hi hj (fun e => by simp [e] at hn)
    have closed := fastCost_good (mem i hi) (mem j hj) (fun e => hne (congrArg Prod.fst e)) al (fast_slow ok)
    have cut : c.2.2.2.2.1.any (fun p => scalarPoolCut c.2.2.2.1.2 p (c.1-1)
        ((delTwo c.2.2.1 (contextWire c i) (contextWire c j) ka kb).map Prod.fst)
        (movedChoice op (contextWire c i) (contextWire c j)))=true :=
      List.any_eq_true.mpr ⟨p,hp,closed⟩
    simp only [checkAt,evalMove,closeChild,cut,Bool.or_true]
    repeat' split
    all_goals rfl
  · have cut := link_sound nd hfl (Nat.ble_eq.mp hi) (Nat.ble_eq.mp hj) (fun e => by simp [e] at hn) h
    simp only [checkAt,evalMove,closeChild,cut,Bool.true_or]
    repeat' split
    all_goals rfl
  · exact h
def swapIdx (v t : Nat) : Nat := cond (Nat.beq t (v &&& 15)) (v >>> 4) (cond (Nat.beq t (v >>> 4)) (v &&& 15) t)
def validSwap (v : Nat) : Bool := and (Nat.ble ((v &&& 15)+1) (v >>> 4)) (Nat.ble ((v >>> 4)+1) 9)
set_option maxRecDepth 8192 in
theorem swap_table : ∀ v : Fin 144, validSwap v.val=true → ∀ t : Fin 9, swapIdx v.val t.val<9 ∧
    wordMove (swapRows v.val) (inputs.getD t.val zero) = inputs.getD (swapIdx v.val t.val) zero := by decide +kernel
theorem swap_input {v t : Nat} (hv : validSwap v=true) (ht : t<9) : swapIdx v t<9 ∧
    wordMove (swapRows v) (inputs.getD t zero) = inputs.getD (swapIdx v t) zero := by
  have lt : v<144 := by
    simp only [validSwap,Bool.and_eq_true,Nat.ble_eq,Nat.shiftRight_eq_div_pow] at hv
    omega
  exact swap_table ⟨v,lt⟩ hv ⟨t,ht⟩
def idxOf (perm : List Nat) (t : Nat) : Nat := perm.foldl (fun t v => swapIdx v t) t
theorem idx_move {perm : List Nat} (ok : perm.all validSwap=true) {t : Nat} (ht : t<9) :
    movedWord (perm.map swapRows).reverse (inputs.getD t zero) = inputs.getD (idxOf perm t) zero := by
  rw [movedWord,List.foldr_reverse,List.foldl_map]
  induction perm generalizing t with
  | nil => rfl
  | cons v perm ih =>
    simp only [List.all_cons,Bool.and_eq_true] at ok
    obtain ⟨lt,e⟩ := swap_input ok.1 ht
    rw [List.foldl_cons,e,ih ok.2 lt]
    rfl
noncomputable def decodeN : Nat → Nat → List Nat → List Nat
  | 0,_,ws => ws
  | n+1,bits,ws => force (zN ((bits >>> 8) &&& 3) (ws.getD (bits &&& 15) 0) (ws.getD ((bits >>> 4) &&& 15) 0))
      fun z => decodeN n (bits >>> 10) (ws++[z])
theorem decodeN_eq (F : Sig → Nat) (F0 : F zero=0) (Fb : ∀ op a b, F (bin op a b)=zN op (F a) (F b))
    (n bits : Nat) (ds : List Decor) :
    (decodeBank n bits ds).map (fun w => F w.1) = decodeN n bits (ds.map fun w => F w.1) := by
  have gd (ds : List Decor) (i : Nat) : (ds.map fun w => F w.1).getD i 0 = F (ds.getD i defaultDecor).1 := by
    simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
    cases ds[i]? with
    | none => exact F0.symm
    | some v => rfl
  induction n generalizing bits ds with
  | zero => rfl
  | succ n ih =>
    rw [decodeN,force_eq,decodeBank,ih,gd,gd,←Fb,List.map_append]
    rfl
theorem selectLive_map {α β : Type} (f : α → β) (bits : Nat) (ws : List α) :
    (selectLive bits ws).map f = selectLive bits (ws.map f) := by
  induction ws generalizing bits with
  | nil => rfl
  | cons w ws ih =>
    rw [List.map_cons,selectLive,selectLive]
    split
    · rw [List.map_cons,ih]
    · exact ih _
noncomputable def fastState (g : Forest) (k i : Nat) (perm : List Nat) : List Nat :=
  let raw := (selected g.mask).map fun e => (inputs.getD (idxOf perm e.1) zero).toNat
  let (_,depth,_,_,_,_,_,data) := g.levels k
  let len := 10*depth
  force (forestRecord (g.levels k) (selected g.mask).length i) fun rec =>
  selectLive (rec >>> len) (decodeN depth (rec &&& ((1 <<< len)-1)) raw)
theorem fastState_eq (g : Forest) (k i : Nat) {perm : List Nat} (ok : perm.all validSwap=true) :
    fastState g k i perm = ((stateSet g k i).map (movedWord (perm.map swapRows).reverse)).map BitVec.toNat := by
  let ms := (perm.map swapRows).reverse
  let F (a : Sig) : Nat := (movedWord ms a).toNat
  have F0 : F zero=0 := by
    change (movedWord ms zero).toNat=0
    rw [moved_eq_rename,(rename_constants _).1]
    simp [zero]
  have Fb (op a b) : F (bin op a b)=zN op (F a) (F b) := by
    change (movedWord ms (bin op a b)).toNat = zN op (movedWord ms a).toNat (movedWord ms b).toNat
    rw [zN_full,moved_eq_rename,rename_bin,moved_eq_rename,moved_eq_rename]
  have raw : (wiresOf g).map (fun w => F w.1) = (selected g.mask).map fun e => (inputs.getD (idxOf perm e.1) zero).toNat := by
    simp only [wiresOf,rawDecor,List.map_map]
    apply List.map_congr_left
    rintro ⟨j,a⟩ hm
    obtain ⟨hj,rfl⟩ := selected_entry hm
    exact congrArg BitVec.toNat (idx_move ok hj)
  have len : (wiresOf g).length = (selected g.mask).length := by simp [wiresOf,rawDecor]
  unfold fastState stateSet readNode
  rcases g.levels k with ⟨a,depth,b,c,d,e,f,data⟩
  simp only [force_eq,storedDepth,len]
  rw [List.map_map,List.map_map,selectLive_map,←raw,←decodeN_eq F F0 Fb]
  rfl
noncomputable def linkedFast (g : Forest) (k : Nat) (pair : Nat × Nat) : Option (List Nat) :=
  if pair.1 ≥ (g.levels k).1 then none else
    (g.autos[pair.2]?).bind fun perm => cond (perm.all validSwap) (some (fastState g k pair.1 perm)) none
noncomputable def flOf (g : Forest) (k : Nat) : Nat → Option (List Nat) := fun tag => (g.index k tag).bind (linkedFast g (k-1))
noncomputable def batchMove (fl : Nat → Option (List Nat)) (u : Bool) (b : Batch) (xs : List Lane) (i j op : Nat) (ka kb : Bool) :=
  let (k,n,r,_,cov) := b
  let len := 1+(n-(if ka then 0 else 1)-(if kb then 0 else 1))
  if len>k then true else
    let a := laneWire b i
    let b' := laneWire b j
    let z := packedOp op a b'
    let mask := fullMarks r (takePacked cov (packedColumn (!u) a) (packedColumn (!u) b') ka kb ||| packedColumn (!u) z)
    onMarks (fun c => fallbackAt fl c i j op ka kb) mask xs
theorem batchMove_at {fl u} (k n) (xs : List NodeContext) {i j op : Nat} {ka kb}
    (hi : i<n) (hj : j<n) {q : Nat} (hq : q<xs.length)
    (budget : xs[q].1=k) (arity : xs[q].2.1=n) (mode : xs[q].2.2.2.1.2=u) (nd : (xs[q].2.2.1.map Prod.fst).Nodup)
    (hfl : ∀ tag ys, fl tag=some ys → ∃ zs ∈ xs[q].2.2.2.2.2 tag, ys=zs.map BitVec.toNat)
    (pass : batchMove fl u (makeBatch k n xs) (xs.map laneOf) i j op ka kb=true) :
    checkAt xs[q] i j op ka kb=true := by
  let len := 1+(n-(if ka then 0 else 1)-(if kb then 0 else 1))
  have eval : checkAt xs[q] i j op ka kb =
      if len>k then true else if combField xs[q] (!u) ka kb op i j != BitVec.allOnes 152 then true
      else if !properB (dbin op (contextWire xs[q] i) (contextWire xs[q] j)).1 ||
        xs[q].2.2.1.any (fun v => v.1==(dbin op (contextWire xs[q] i) (contextWire xs[q] j)).1)
      then true else closeChild u xs[q].2.2.2.2.1 xs[q].2.2.2.2.2 (k-1)
        ((delTwo xs[q].2.2.1 (contextWire xs[q] i) (contextWire xs[q] j) ka kb).map Prod.fst)
        (movedChoice op (contextWire xs[q] i) (contextWire xs[q] j)) := by
    simp only [checkAt,evalMove,budget,arity,mode,len,combField] <;> rfl
  by_cases small : len>k
  · simp [eval,small]
  · let r := units xs.length
    let a := laneWire (makeBatch k n xs) i
    let b := laneWire (makeBatch k n xs) j
    let cov := packedCov (fun c : NodeContext => c.2.2.2.1.1) xs
    change (if len>k then true else onMarks _ (fullMarks r
       (takePacked cov (packedColumn (!u) a) (packedColumn (!u) b) ka kb |||
        packedColumn (!u) (packedOp op a b))) (xs.map laneOf)) = true at pass
    rw [if_neg small] at pass
    have ca : a = _ := laneWire_at k n xs hi
    have cb : b = _ := laneWire_at k n xs hj
    dsimp only [r,cov] at pass
    rw [ca,cb,packed_op,packed_column,packed_column,packed_column,takePacked_ok,lanes_or] at pass
    by_cases hit : combField xs[q] (!u) ka kb op i j = BitVec.allOnes 152
    · apply fallback_sound nd hfl
      have m := marked_ok _ _ _ q (by simpa using hq) (by
        rw [mark_at _ _ _ hq]
        exact beq_iff_eq.mpr hit) pass
      simpa only [List.getElem_map] using m
    · rw [eval,if_neg small,if_pos (bne_iff_ne.mpr hit)]
noncomputable def batchPair (fl : Nat → Option (List Nat)) (u : Bool) (b : Batch) (xs : List Lane) (i j op : Nat) :=
  let f := batchMove fl u b xs i j op
  f false false && f true false && f false true && f true true
noncomputable def batchRow (fl : Nat → Option (List Nat)) (u : Bool) (b : Batch) (xs : List Lane) (i : Nat) (js : List Nat) :=
    js.all (fun j => (opsOf u).all (batchPair fl u b xs i j))
noncomputable def batchRows (fl : Nat → Option (List Nat)) (u : Bool) (b : Batch) (xs : List Lane) : List Nat → Bool
  | [] => true
  | i::js => batchRow fl u b xs i js && batchRows fl u b xs js
theorem batchRows_at {fl u} (k n) (xs : List NodeContext) {q : Nat} (hq : q<xs.length)
    (budget : xs[q].1=k) (arity : xs[q].2.1=n) (mode : xs[q].2.2.2.1.2=u) (nd : (xs[q].2.2.1.map Prod.fst).Nodup)
    (hfl : ∀ tag ys, fl tag=some ys → ∃ zs ∈ xs[q].2.2.2.2.2 tag, ys=zs.map BitVec.toNat)
    (js : List Nat)
    (bounds : ∀ j ∈ js, j<n) (allRows : batchRows fl u (makeBatch k n xs) (xs.map laneOf) js=true) :
    testAll xs[q] (js.map (contextWire xs[q])) = true := by
  induction js with
  | nil => rfl
  | cons i js ih =>
    simp only [batchRows,Bool.and_eq_true,batchRow,List.all_eq_true] at allRows
    simp only [List.map_cons,testAll,testRow,Bool.and_eq_true,List.all_eq_true,List.mem_map]
    have hi := bounds i List.mem_cons_self
    refine ⟨?_,ih (fun j hj => bounds j (List.mem_cons_of_mem _ hj)) allRows.2⟩
    rintro _ ⟨j,hj,rfl⟩ op hop
    have hj' := bounds j (List.mem_cons_of_mem _ hj)
    rw [mode] at hop
    have pass := allRows.1 j hj op hop
    have check := @batchMove_at fl u k n xs i j op
    simp only [batchPair,Bool.and_eq_true] at pass
    simp only [testPair,Bool.and_eq_true]
    exact ⟨⟨⟨check hi hj' hq budget arity mode nd hfl pass.1.1.1,check hi hj' hq budget arity mode nd hfl pass.1.1.2⟩,
      check hi hj' hq budget arity mode nd hfl pass.1.2⟩,check hi hj' hq budget arity mode nd hfl pass.2⟩
noncomputable def runBatch (fl : Nat → Option (List Nat)) (u : Bool) (k n : Nat) (xs : List NodeContext) :=
    batchRows fl u (makeBatch k n xs) (xs.map laneOf) (List.range n)
theorem runBatch_at {fl u k n} {xs : List NodeContext} {q} (hq : q<xs.length)
    (hb : xs[q].1=k) (ha : xs[q].2.1=n) (hm : xs[q].2.2.2.1.2=u) (nd : (xs[q].2.2.1.map Prod.fst).Nodup)
    (hfl : ∀ tag ys, fl tag=some ys → ∃ zs ∈ xs[q].2.2.2.2.2 tag, ys=zs.map BitVec.toNat)
    (hn : xs[q].2.2.1.length=n)
    (pass : runBatch fl u k n xs=true) : testAll xs[q] xs[q].2.2.1=true := by
  have all := batchRows_at k n xs hq hb ha hm nd hfl (List.range n) (fun _ => List.mem_range.mp) pass
  have eq : (List.range n).map (contextWire xs[q]) = xs[q].2.2.1 := by
    apply List.ext_getElem
    · simp [hn]
    · intro i h1 h2
      simp [contextWire,List.getD_eq_getElem?_getD,h2]
  rwa [eq] at all
def contextOf (g : Forest) (k i : Nat) : NodeContext :=
  let raw := wiresOf g
  let (num,depth,cw,iw,pw,offw,lw,data) := g.levels k
  let (ops,bank,ws) := readNode g k i
  let rules := (forestHints (g.levels k) raw.length i).filterMap (fun (a,b) => buildRule g ops depth bank a b)
  let ls := fun tag => ((g.index k tag).bind (linkedSet g (k-1))).toList
  (k,ws.length,ws,preCov g.mode ws,rules,ls)
theorem flOf_ok (g : Forest) (k i tag : Nat) (ys) (h : flOf g k tag=some ys) :
    ∃ xs ∈ (contextOf g k i).2.2.2.2.2 tag, ys=xs.map BitVec.toNat := by
  change ∃ xs ∈ ((g.index k tag).bind (linkedSet g (k-1))).toList, _
  unfold flOf at h
  cases hp : g.index k tag with
  | none => simp [hp] at h
  | some pair =>
    simp only [hp,Option.bind_some,linkedFast] at h
    simp only [Option.bind_some,linkedSet]
    split at h
    · contradiction
    next v =>
      cases ha : g.autos[pair.2]? with
      | none => simp [ha] at h
      | some perm =>
        simp only [ha,Option.bind_some] at h
        cases hv : perm.all validSwap with
        | false => simp [hv] at h
        | true =>
          simp only [hv,cond_true,Option.some.injEq] at h
          refine ⟨(stateSet g (k-1) pair.1).map (movedWord (perm.map swapRows).reverse),?_,?_⟩
          · simp [v]
          · exact h.symm.trans (fastState_eq g _ _ hv)
def prelim (T : Sig) (c : NodeContext) :=
  let ws := c.2.2.1.map Prod.fst
  decide ws.Nodup && !(ws.contains T)
theorem from_context (g : Forest) (k i : Nat) :
    nodeVerified g k i = (prelim (targetOf g) (contextOf g k i) &&
      (if k=0 then true else testAll (contextOf g k i) (contextOf g k i).2.2.1)) := rfl
theorem makeBlock {g k start n} (h : ∀ (i : Nat), start ≤ i → i < start + n → nodeVerified g k i = true) :
    block g k start n=true := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [block,Bool.and_eq_true]
    exact ⟨h _ (by omega) (by omega),ih (fun i le lt => h i le (by omega))⟩
def contexts (g : Forest) (k start n : Nat) :=
  ((List.range n).map (start+·)).map (contextOf g k)
def header (g : Forest) (k start n ar : Nat) :=
  (contexts g k start n).all (fun c => c.2.1==ar && prelim (targetOf g) c)
noncomputable def rowCut (g : Forest) (k start n ar lo len : Nat) :=
  let xs := contexts g k start n
  let b := makeBatch k ar xs
  forceLanes xs fun ys => (List.range len).all (fun d =>
    let i := lo+d
    batchRow (flOf g k) g.mode b ys i (List.range' (i+1) (ar-(i+1))))
theorem rowCut_at {g k start n ar lo len} (h : rowCut g k start n ar lo len=true)
    (i : Nat) (l : lo ≤ i) (r : i < lo+len) :
    batchRow (flOf g k) g.mode (makeBatch k ar (contexts g k start n)) ((contexts g k start n).map laneOf)
      i (List.range' (i+1) (ar-(i+1)))=true := by
  simp only [rowCut,forceLanes_eq] at h
  have ha := List.all_eq_true.mp h (i-lo) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le l] using ha
theorem rowCut_merge {g k start n ar lo a b}
    (h : rowCut g k start n ar lo a=true) (t : rowCut g k start n ar (lo+a) b=true) :
    rowCut g k start n ar lo (a+b)=true := by
  simp only [rowCut,forceLanes_eq]
  apply List.all_eq_true.mpr
  intro j hj
  have jlt := List.mem_range.mp hj
  by_cases first : j<a
  · exact rowCut_at h (lo+j) (by omega) (by omega)
  · exact rowCut_at t (lo+j) (by omega) (by omega)
theorem cutsRun {g k start n ar} (h : rowCut g k start n ar 0 ar=true) :
    runBatch (flOf g k) g.mode k ar (contexts g k start n)=true := by
  let xs := contexts g k start n
  have go (lo num : Nat) (eq : lo+num=ar) :
      batchRows (flOf g k) g.mode (makeBatch k ar xs) (xs.map laneOf) (List.range' lo num)=true := by
    induction num generalizing lo with
    | zero => rfl
    | succ num ih =>
      simp only [List.range'_succ,batchRows,Bool.and_eq_true]
      refine ⟨?_,ih (lo+1) (by omega)⟩
      have ok := rowCut_at h lo (by omega) (by omega)
      simpa only [show ar-(lo+1)=num by omega] using ok
  unfold runBatch
  rw [List.range_eq_range']
  exact go 0 ar (by omega)
theorem cutsBlock {g k start n ar} (hd : header g k start n ar=true)
    (h : rowCut g k start n ar 0 ar=true) : block g k start n=true := by
  apply makeBlock
  intro i lo hi
  let xs := contexts g k start n
  have hm : contextOf g k i ∈ xs := by
    apply List.mem_map.mpr
    exact ⟨i,List.mem_map.mpr ⟨i-start,List.mem_range.mpr (by omega),by omega⟩,rfl⟩
  obtain ⟨q,hq,e⟩ := List.getElem_of_mem hm
  have one := List.all_eq_true.mp hd _ hm
  simp only [Bool.and_eq_true,beq_iff_eq] at one
  have hb : xs[q].1=k := by rw [e]; rfl
  have ha : xs[q].2.1=ar := e ▸ one.1
  have nd : (xs[q].2.2.1.map Prod.fst).Nodup := by
    have p := one.2
    simp only [prelim,Bool.and_eq_true,decide_eq_true_eq] at p
    rw [e]
    exact p.1
  have hfl : ∀ tag ys, flOf g k tag=some ys → ∃ zs ∈ xs[q].2.2.2.2.2 tag, ys=zs.map BitVec.toNat := by
    rw [e]
    exact fun tag ys h => flOf_ok g k i tag ys h
  have hm : xs[q].2.2.2.1.2=g.mode := by rw [e]; rfl
  have hn : xs[q].2.2.1.length=ar := by rw [e]; exact one.1
  rw [from_context,Bool.and_eq_true]
  refine ⟨one.2,?_⟩
  split
  · rfl
  · exact e ▸ runBatch_at hq hb ha hm nd hfl hn (cutsRun h)
def boxes (g : Forest) (k start n ar lo num : Nat) : Nat → Prop
  | 0 => rowCut g k start n ar lo num=true
  | d+1 => boxes g k start n ar lo (num/2) d ∧ boxes g k start n ar (lo+num/2) (num-num/2) d
theorem boxesCut {g k start n ar lo num d} (h : boxes g k start n ar lo num d) :
    rowCut g k start n ar lo num=true := by
  induction d generalizing lo num with
  | zero => exact h
  | succ d ih =>
    have v := rowCut_merge (ih h.1) (ih h.2)
    simpa only [Nat.add_sub_of_le (Nat.div_le_self num 2)] using v
def cells (g : Forest) (k start n ar rows : Nat) : Nat → Prop
  | 0 => header g k start n ar=true ∧ boxes g k start n ar 0 ar rows
  | d+1 => cells g k start (n/2) ar rows d ∧ cells g k (start+n/2) (n-n/2) ar rows d
theorem cellsBlock {g k start n ar rows d} (h : cells g k start n ar rows d) :
    block g k start n=true := by
  induction d generalizing start n with
  | zero => exact cutsBlock h.1 (boxesCut h.2)
  | succ d ih =>
    have v := block_merge (ih h.1) (ih h.2)
    simpa only [Nat.add_sub_of_le (Nat.div_le_self n 2)] using v
def listPieces {α} (f : α → Bool) (xs : List α) : Nat → Prop
  | 0 => xs.all f=true
  | d+1 => listPieces f (xs.take (xs.length/2)) d ∧ listPieces f (xs.drop (xs.length/2)) d
theorem pieces_all {α f xs d} (h : @listPieces α f xs d) : xs.all f=true := by
  induction d generalizing xs with
  | zero => exact h
  | succ d ih =>
    have ap : ((xs.take (xs.length/2)) ++ (xs.drop (xs.length/2))).all f=true := by
      simp only [List.all_append,ih h.1,ih h.2,Bool.and_self]
    simpa only [List.take_append_drop] using ap
theorem slice_self {u} {raw : List Sig} {T : Sig} {L : Nat} (pT : proper T) (h : Lower u raw T L) :
    Slice u raw T one L := by
  refine ⟨id,raw,fun r => bit_one r,fun a ha => ?_,observe_proper pT,h⟩
  exact Or.inl (List.mem_map_of_mem ha)
theorem plainA {u} {m q cap : Nat} {prior : Nat → Nat} (low : ∀ q, Lower u (varsX q) (graphGoal q) (prior q))
    (e : (graphGoal q == graphGoal m && (varsX q == vars m) && (prior q == cap+1) && properB (graphGoal m) &&
      decide (vars m).Nodup && poolCut u one (cap+1) cap 0 (vars m) (vars m)) = true) :
    Impossible u (graphGoal m) cap (vars m).toFinset := by
  simp only [Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at e
  obtain ⟨⟨⟨⟨⟨e1,e2⟩,e3⟩,e4⟩,e5⟩,e6⟩ := e
  have h := low q
  rw [e1,e2,e3] at h
  exact poolCut_sound (slice_self (proper_of _ e4) h) [] rfl e5 e6
theorem cut_root {u} {m cap : Nat} {prior : Nat → Nat} {ws : List Sig}
    (low : ∀ q, Lower u (varsX q) (graphGoal q) (prior q)) (ci : ColumnInfo)
    (ok : colCheck m ci prior = true)
    (cut : (decide ws.Nodup && poolCut u (subcube ci.1 ci.2.1) ci.2.2.2.2 cap 0 (varsX (rawMask m ci)) ws)=true) :
    Impossible u (graphGoal m) cap ws.toFinset := by
  simp only [Bool.and_eq_true,decide_eq_true_eq] at cut
  exact poolCut_sound (col_sound ci prior low ok) [] rfl cut.1 cut.2
theorem index_root {u} {g : Forest} {m cap i : Nat} {prior : Nat → Nat} {ws : List Sig}
    (hm : g.mask=m) (hu : g.mode=u) (low : ∀ q, Lower u (varsX q) (graphGoal q) (prior q))
    (geom : graphValid g prior = true) (blocks : checkedTables g cap)
    (idx : indexedRoot g cap i ws = true) : Impossible u (graphGoal m) cap ws.toFinset := by
  subst hm
  subst hu
  exact root_index low geom blocks (Nat.le_refl _) idx
def essOK (m hints : Nat) : Bool :=
  let xs := graphPairs m hints
  properB (graphGoal m) && checkEssential (graphGoal m) (vars m) xs && (xs.map Prod.fst == vars m)
theorem plain_low {u} {m hints cap : Nat} (ok : essOK m hints = true)
    (a : Impossible u (graphGoal m) cap (vars m).toFinset) : Lower u (vars m) (graphGoal m) (cap+1) := by
  simp only [essOK,Bool.and_eq_true,beq_iff_eq] at ok
  apply lower_impossible (proper_of _ ok.1.1) (essential_plain ok.1.2).1 (essential_plain ok.1.2).2 _ a
  intro v hv
  apply essential_ok ok.1.2 v
  rw [ok.2]
  exact List.mem_toFinset.mpr hv
def target (x : Fin 6 → Bool) : Bool := Nat.testBit (4276809440 * 2 ^ 32 + 4008372416) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
def smallCircuit : Circuit := ⟨[⟨.or,[5,4]⟩,⟨.and,[3,2]⟩,⟨.or,[6,7]⟩,⟨.and,[8,0]⟩,⟨.and,[5,7]⟩,⟨.or,[10,9]⟩,⟨.or,[8,0]⟩,⟨.and,[12,3]⟩,⟨.or,[13,2]⟩,⟨.and,[11,4]⟩,⟨.or,[9,1]⟩,⟨.and,[14,16]⟩,⟨.or,[15,17]⟩], 18⟩
theorem witnessMonotone : ∀ g ∈ smallCircuit.gates,
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [smallCircuit,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact ⟨Or.inl rfl,by decide⟩ | exact ⟨Or.inr rfl,by decide⟩
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem witnessCorrect : ∀ x : Fin 6 → Bool, smallCircuit.eval (List.ofFn x) = target x := by
  decide +kernel
theorem witnessSize : smallCircuit.gates.length = 13 := rfl
theorem noNotReuse {gates : List Gate} (fit : ∀ g ∈ gates,
    (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (h : ∀ g ∈ gates, g.op ≠ GateOp.not) :
    ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  obtain ⟨ops,arity⟩ := fit g hg
  refine ⟨?_,arity⟩
  rcases ops with a | b | c
  · exact Or.inl a
  · exact Or.inr b
  · exact (h g hg c).elim
def rawSix : List Sig := vars 63
def sampleInstance (r : Row) (i : Fin 6) : Bool := bit r (rawSix.getD i.val zero)
theorem instanceList : List.ofFn (fun i : Fin 6 => rawSix.getD i.val zero) = rawSix := rfl
theorem instanceSampled (r : Row) : List.ofFn (sampleInstance r) = rawSix.map (bit r) := by
  rw [←instanceList,List.map_ofFn]
  rfl
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem instanceTable : ∀ r : Row, bit r graph = target (sampleInstance r) := by decide +kernel
theorem instanceEval (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (i : Nat) (r : Row) : bit r ((execute C.gates rawSix).getD i zero) =
      (C.wires (List.ofFn (sampleInstance r))).getD i false := by
  rw [←b_read,execute_bits _ _ _ (fun g hg => (h g hg).1),instanceSampled]
  rfl
def lowRow (i : Fin 6) : Row := Fin.ofNat 512 (([10, 4, 2, 3, 1, 5] : List Nat).getD i.val 0)
def highRow (i : Fin 6) : Row := Fin.ofNat 512 ((1 <<< i.val) ||| (([10, 4, 2, 3, 1, 5] : List Nat).getD i.val 0))
set_option maxHeartbeats 1000000 in
theorem allInstanceRequired :
    (∀ i : Fin 6, bit (lowRow i) graph ≠ bit (highRow i) graph) ∧
    (∀ i j : Fin 6, i ≠ j →
      bit (lowRow i) (rawSix.getD j.val zero) =
      bit (highRow i) (rawSix.getD j.val zero)) := by decide +kernel
theorem physicalSigned (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (computes : ∀ x : Fin 6 → Bool, C.eval (List.ofFn x)=target x) :
    ∃ k, k ≤ C.gates.countP (fun g => !isNot g) ∧ Live true graph k rawSix.toFinset := by
  have goalEq : (execute C.gates rawSix).getD C.output zero = graph := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    exact (instanceEval C legal C.output r).trans ((computes (sampleInstance r)).trans (instanceTable r).symm)
  have out := get_rep (u:=true) (execute C.gates rawSix) C.output
  rw [goalEq] at out
  unfold Repr at out
  have pg : bit 0 graph = false := by decide +kernel
  rw [nrm_id pg] at out
  obtain ⟨k,S,hk,run,sub⟩ := extract (u:=true) C.gates rawSix legal (by simp) graph_proper
    (out.resolve_right (fun h => h graph_proper))
  have ns : rawSix.all plainWord = true := by decide +kernel
  rw [nrm_map ns] at sub
  have idx (a : Sig) (ha : a ∈ rawSix) : ∃ i : Fin 6, rawSix.getD i.val zero = a := by
    rw [←instanceList] at ha
    exact List.mem_ofFn.mp ha
  have eq : S = rawSix.toFinset := by
    ext a
    constructor
    · exact fun h => List.mem_toFinset.mpr (sub a h)
    · intro ha
      obtain ⟨i,rfl⟩ := idx a (List.mem_toFinset.mp ha)
      apply raw_required run rawSix (rawSix.getD i.val zero) sub (lowRow i) (highRow i)
        (allInstanceRequired.1 i)
      intro v hv hn
      obtain ⟨j,rfl⟩ := idx v hv
      apply allInstanceRequired.2 i j
      rintro rfl
      exact hn rfl
  exact ⟨k,hk,eq ▸ run⟩
theorem replaceShort 
    (lower : Impossible true graph 11 rawSix.toFinset) (gates : List Gate) (o : Nat)
    (fit : ∀ g ∈ gates, (g.op=GateOp.and ∨ g.op=GateOp.or ∨ g.op=GateOp.not) ∧ g.inputs.length≤2)
    (correct : ∀ x : Fin 6 → Bool, (Circuit.mk gates o).eval (List.ofFn x)=target x) :
    ∃ (gs : List Gate) (out : Nat), (∀ g ∈ gs, (g.op=GateOp.and ∨ g.op=GateOp.or) ∧ g.inputs.length≤2) ∧
       gs.length≤gates.length ∧ ∀ x : Fin 6 → Bool, (Circuit.mk gs out).eval (List.ofFn x)=target x := by
  classical
  by_cases big : 13 ≤ gates.length
  · exact ⟨smallCircuit.gates,smallCircuit.output,witnessMonotone,witnessSize.symm ▸ big,witnessCorrect⟩
  by_cases mono : ∀ g ∈ gates, g.op ≠ GateOp.not
  · exact ⟨gates,o,noNotReuse fit mono,Nat.le_refl _,correct⟩
  push Not at mono
  obtain ⟨g,hg,hop⟩ := mono
  have lt : gates.countP (fun q => !isNot q) < gates.length := by
    rcases Nat.lt_or_ge (gates.countP (fun q => !isNot q)) gates.length with h | h
    · exact h
    · have eq := List.countP_eq_length.mp (Nat.le_antisymm List.countP_le_length h) g hg
      simp [isNot,hop] at eq
  have legal : PEqualNP.MetaComplexity.FanInTwo (Circuit.mk gates o) := by
    intro g hg
    simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using fit g hg
  obtain ⟨k,hk,run⟩ := physicalSigned (Circuit.mk gates o) legal correct
  change k ≤ gates.countP (fun q => !isNot q) at hk
  exact (lower k (by omega) run).elim
def g7Y : Array (Bits × Bits) := #[((seg80 [0xb5dfb5dfb5dfb5dfb5,0xdfb5dfb5dfb5dfb5dfb5]),(seg80 [0x942094209420942094,0x20942094209420942094])),((seg80 [0xeeeeeeeeeeeeeeeeee,0xeeeeeeeeeeeeeeeeeeee]),(seg80 [0x281228122812281228,0x12281228122812281228])),((seg80 [0xdb7bdb7bdb7bdb7bdb,0x7bdb7bdb7bdb7bdb7bdb]),(seg80 [0x38803880388038803,0x88038803880388038803])),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g7C : List ColumnInfo := []
def g7A : List (List Nat) := [[],[33],[16],[16,32],[32,16],[32]]
def g7D3 (j : Nat) := if j=0 then 0x7 else 0
def g7L : Nat → Packing
  | 3 => (1,0,1,0,0,0,0,g7D3)
  | _ => emptyPacking
def g7I (_ _ : Nat) : Option (Nat × Nat) := none
def g7 : Forest := ⟨7,3,fun i => g7Y[i]?.getD (0,0),g7C,g7A,g7L,g7I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g7P3_0 : block g7 3 0 1=true := by
  apply cellsBlock (ar:=3) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g7B3 : block g7 3 0 1=true := g7P3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g7T : checkedTables g7 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g7 0 0 0 = true)
  · exact (rfl : block g7 1 0 0 = true)
  · exact (rfl : block g7 2 0 0 = true)
  · exact g7B3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g7G : graphValid g7 (boundsBefore []) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low7 : Lower true (varsX 7) (graphGoal 7) 4 := lower_forest (g:=g7) (i:=0) (hints:=262658) (before_sound [] baseKnown) g7G g7T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K7 := extendKnown [] 4 [(7,[]),(14,[16,32,48]),(19,[66,50]),(25,[49,66]),(35,[82,50,67]),(44,[32,49,80,16,65])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V7 : Known true K7 := extend_ok (m:=7) baseKnown low7 (by decide +kernel)
def g15Y : Array (Bits × Bits) := #[((seg80 [0xf3726f175edd8fff37,0x26f175edd8fff3726f17]),(seg80 [0xb6401617a14a562b64,0x1617a14a562b6401617])),((seg80 [0xffdfd3fdeffefb5ffd,0xfd3fdeffefb5ffdfd3fd]),(seg80 [0x6806517410004cc680,0x6517410004cc68065174])),((seg80 [0xbebffcfbbf77fefbeb,0xffcfbbf77fefbebffcfb]),(seg80 [0x84b80c89401e01184b,0x80c89401e01184b80c89])),((seg80 [0xf1f6afa674dbf5ef1f,0x6afa674dbf5ef1f6afa6]),(seg80 [0x191aaba288249b8191,0xaaba288249b8191aaba2])),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g15C : List ColumnInfo := [(0,1,14,0,4)]
def g15A : List (List Nat) := [[],[33],[48],[48,33]]
def g15D4 (j : Nat) := if j=0 then 0x1f else 0
def g15L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,g15D4)
  | _ => emptyPacking
def g15I (_ _ : Nat) : Option (Nat × Nat) := none
def g15 : Forest := ⟨15,4,fun i => g15Y[i]?.getD (0,0),g15C,g15A,g15L,g15I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g15P4_0 : block g15 4 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g15B4 : block g15 4 0 1=true := g15P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g15T : checkedTables g15 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g15 0 0 0 = true)
  · exact (rfl : block g15 1 0 0 = true)
  · exact (rfl : block g15 2 0 0 = true)
  · exact (rfl : block g15 3 0 0 = true)
  · exact g15B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g15G : graphValid g15 (boundsBefore K7) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low15 : Lower true (varsX 15) (graphGoal 15) 5 := lower_forest (g:=g15) (i:=0) (hints:=403179530) (before_sound K7 V7) g15G g15T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K15 := extendKnown K7 5 [(15,[]),(27,[16,66])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V15 : Known true K15 := extend_ok (m:=15) V7 low15 (by decide +kernel)
def g23Y : Array (Bits × Bits) := #[((seg80 [0xef67f2dfef5eec7fef,0x67f2dfef5eec7fef67f2]),(seg80 [0x4445c02001a080c544,0x45c02001a080c54445c0])),((seg80 [0xb698ddbb9aabffc1b6,0x98ddbb9aabffc1b698dd]),(seg80 [0xa0c8d445a5c030c6a0,0xc8d445a5c030c6a0c8d4])),((seg80 [0xd5fe8ff7dff9bff0d5,0xfe8ff7dff9bff0d5fe8f]),(seg80 [0x8120b0a02044e3008,0x120b0a02044e3008120b])),(0x0,0x0),((seg80 [0x7aa375aebd96ea5f7a,0xa375aebd96ea5f7aa375]),(seg80 [0x1a3235514e0178221a,0x3235514e0178221a3235])),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g23C : List ColumnInfo := []
def g23A : List (List Nat) := [[],[32,65]]
def g23D3 (j : Nat) := if j=0 then 0xf else 0
def g23L : Nat → Packing
  | 3 => (1,0,1,0,0,0,0,g23D3)
  | _ => emptyPacking
def g23I (_ _ : Nat) : Option (Nat × Nat) := none
def g23 : Forest := ⟨23,3,fun i => g23Y[i]?.getD (0,0),g23C,g23A,g23L,g23I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g23P3_0 : block g23 3 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g23B3 : block g23 3 0 1=true := g23P3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g23T : checkedTables g23 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g23 0 0 0 = true)
  · exact (rfl : block g23 1 0 0 = true)
  · exact (rfl : block g23 2 0 0 = true)
  · exact g23B3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g23G : graphValid g23 (boundsBefore K15) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low23 : Lower true (varsX 23) (graphGoal 23) 4 := lower_forest (g:=g23) (i:=0) (hints:=68719740932) (before_sound K15 V15) g23G g23T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K23 := extendKnown K15 4 [(23,[]),(2075,[50])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V23 : Known true K23 := extend_ok (m:=23) V15 low23 (by decide +kernel)
def g29Y : Array (Bits × Bits) := #[((seg80 [0xdefdfcf7fefffffede,0xfdfcf7fefffffedefdfc]),(seg80 [0x880848080000400888,0x8480800004008880848])),(0x0,0x0),((seg80 [0x6f4e177c79577eab6f,0x4e177c79577eab6f4e17]),(seg80 [0x41c61683e6220c9241,0xc61683e6220c9241c616])),((seg80 [0xa9b78bcded7ccf27a9,0xb78bcded7ccf27a9b78b]),(seg80 [0x10d781320c92362510,0xd781320c92362510d781])),((seg80 [0xf522e75b2feb5e5df5,0x22e75b2feb5e5df522e7]),(seg80 [0x3430a7a450709a9034,0x30a7a450709a903430a7])),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g29C : List ColumnInfo := []
def g29A : List (List Nat) := [[],[67],[50],[50,66],[66,50],[66]]
def g29D3 := limbs80 #[#[0x2b10910ae42042b50810,0x19d43887948421af4244,0x91e61230602790e2]]
def g29D4 := limbs80 #[#[0xfc21fe21f843e887c10,0x48f30918301f887e9]]
def g29H4 := limbs80 #[#[0x7900d600006500008,0x8244000000000,0xf0000000a1008300000,0x18004a00000000003b0]]
def g29D5 (j : Nat) := if j=0 then 0xf else 0
def g29H5 := limbs80 #[#[0xe0000000343078000024,0x600000003c0000000712,0x28198fe,0x50000000000b40000000,0xd44e20026000000f38c,0x1d2000000000,0x54c0000000e34000000,0x186001cc0000,0xf740,0x7080000000000002580,0x40000,0x9840]]
def g29L : Nat → Packing
  | 3 => (7,2,1,0,0,6,0,g29D3)
  | 4 => (7,1,1,0,0,6,0,g29D4)
  | 5 => (1,0,1,0,0,0,0,g29D5)
  | _ => emptyPacking
def g29I : Nat → Nat → Option (Nat × Nat)
  | 4 => lookupWord 2 41 2 8 3 1 g29H4
  | 5 => lookupWord 6 89 1 10 3 3 g29H5
  | _ => fun _ => none
def g29 : Forest := ⟨29,5,fun i => g29Y[i]?.getD (0,0),g29C,g29A,g29L,g29I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g29P3_0 : block g29 3 0 7=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g29B3 : block g29 3 0 7=true := g29P3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g29P4_0 : block g29 4 0 7=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g29B4 : block g29 4 0 7=true := g29P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g29P5_0 : block g29 5 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g29B5 : block g29 5 0 1=true := g29P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g29T : checkedTables g29 5 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g29 0 0 0 = true)
  · exact (rfl : block g29 1 0 0 = true)
  · exact (rfl : block g29 2 0 0 = true)
  · exact g29B3
  · exact g29B4
  · exact g29B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g29G : graphValid g29 (boundsBefore K23) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low29 : Lower true (varsX 29) (graphGoal 29) 6 := lower_forest (g:=g29) (i:=0) (hints:=68853956612) (before_sound K23 V23) g29G g29T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K29 := extendKnown K23 6 [(29,[]),(53,[67,83]),(54,[16,67,83]),(57,[50,66,82])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V29 : Known true K29 := extend_ok (m:=29) V23 low29 (by decide +kernel)
def g30Y : Array (Bits × Bits) := #[(0x0,0x0),((seg80 [0xfe7faf77fffbbfbffc,0xff5eeffff77f7ff9febd]),(seg80 [0x28070c080040612850,0xe18100080c250a01c30])),((seg80 [0xa7b1d7bcdbfe6bff4f,0x63af79b7fcd7fe9ec75e]),(seg80 [0x8070d303550092d100,0xe1a606aa0125a201c34c])),((seg80 [0x5beef8dbb7cff7ccb7,0xddf1b76f9fef996fbbe3]),(seg80 [0x1350b0e442a08e0426,0xa161c885411c084d42c3])),((seg80 [0xaba87d9d523df74357,0x50fb3aa47bee86aea1f6]),(seg80 [0x12ac6da2a9e8513225,0x58db4553d0a2644ab1b6])),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g30C : List ColumnInfo := [(0,16,14,0,4)]
def g30A : List (List Nat) := [[],[50]]
def g30D4 (j : Nat) := if j=0 then 0x1f else 0
def g30L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,g30D4)
  | _ => emptyPacking
def g30I (_ _ : Nat) : Option (Nat × Nat) := none
def g30 : Forest := ⟨30,4,fun i => g30Y[i]?.getD (0,0),g30C,g30A,g30L,g30I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g30P4_0 : block g30 4 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g30B4 : block g30 4 0 1=true := g30P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g30T : checkedTables g30 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g30 0 0 0 = true)
  · exact (rfl : block g30 1 0 0 = true)
  · exact (rfl : block g30 2 0 0 = true)
  · exact (rfl : block g30 3 0 0 = true)
  · exact g30B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g30G : graphValid g30 (boundsBefore K29) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low30 : Lower true (varsX 30) (graphGoal 30) 5 := lower_forest (g:=g30) (i:=0) (hints:=824902682624) (before_sound K29 V29) g30G g30T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K30 := extendKnown K29 5 [(30,[]),(46,[84])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V30 : Known true K30 := extend_ok (m:=30) V29 low30 (by decide +kernel)
def g39Y : Array (Bits × Bits) := #[((seg80 [0x75ef25b6f9ffa3f75e,0xf25b6f9ffa3f75ef25b6]),(seg80 [0x110025800680040110,0x2580068004011002580])),((seg80 [0x9af9fe4df6c77fe9af,0x9fe4df6c77fe9af9fe4d]),(seg80 [0x1480c0834002000,0x1480c08340020001480c])),((seg80 [0xd5b2db235de5bc7d5b,0x2db235de5bc7d5b2db23]),(seg80 [0x8cb40223a04a40d8cb,0x40223a04a40d8cb40223])),(0x0,0x0),(0x0,0x0),((seg80 [0xaf6772f89edee90af6,0x772f89edee90af6772f8]),(seg80 [0x87612706102325087,0x61270610232508761270])),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g39C : List ColumnInfo := [(4,0,35,0,4)]
def g39A : List (List Nat) := [[],[82],[16],[16,82]]
def g39D4 (j : Nat) := if j=0 then 0x1f else 0
def g39L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,g39D4)
  | _ => emptyPacking
def g39I (_ _ : Nat) : Option (Nat × Nat) := none
def g39 : Forest := ⟨39,4,fun i => g39Y[i]?.getD (0,0),g39C,g39A,g39L,g39I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g39P4_0 : block g39 4 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g39B4 : block g39 4 0 1=true := g39P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g39T : checkedTables g39 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g39 0 0 0 = true)
  · exact (rfl : block g39 1 0 0 = true)
  · exact (rfl : block g39 2 0 0 = true)
  · exact (rfl : block g39 3 0 0 = true)
  · exact g39B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g39G : graphValid g39 (boundsBefore K30) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low39 : Lower true (varsX 39) (graphGoal 39) 5 := lower_forest (g:=g39) (i:=0) (hints:=35184372351490) (before_sound K30 V30) g39G g39T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K39 := extendKnown K30 5 [(39,[]),(51,[66,50]),(2071,[84]),(2094,[32,49,16])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V39 : Known true K39 := extend_ok (m:=39) V30 low39 (by decide +kernel)
def g43Y : Array (Bits × Bits) := #[((seg80 [0xdadebf5bfd9fdadebf,0x5bfd9fdadebf5bfd9fda]),(seg80 [0x1a2544cbc5431a2544,0xcbc5431a2544cbc5431a])),((seg80 [0xaf7fd2ff7b79af7fd2,0xff7b79af7fd2ff7b79af]),(seg80 [0xab805d1aaa48ab805d,0x1aaa48ab805d1aaa48ab])),(0x0,0x0),((seg80 [0xffffffffffffffffff,0xffffffffffffffffffff]),(seg80 [0xf403810058b1f40381,0x58b1f403810058b1f4])),(0x0,0x0),((seg80 [0x77b9edfcffe677b9ed,0xfcffe677b9edfcffe677]),(seg80 [0x474e1886b146474e18,0x86b146474e1886b14647])),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g43C : List ColumnInfo := [(0,8,35,0,4)]
def g43A : List (List Nat) := [[],[81],[16],[16,80],[80,16],[80]]
def g43D4 (j : Nat) := if j=0 then 0x1f else 0
def g43L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,g43D4)
  | _ => emptyPacking
def g43I (_ _ : Nat) : Option (Nat × Nat) := none
def g43 : Forest := ⟨43,4,fun i => g43Y[i]?.getD (0,0),g43C,g43A,g43L,g43I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g43P4_0 : block g43 4 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g43B4 : block g43 4 0 1=true := g43P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g43T : checkedTables g43 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g43 0 0 0 = true)
  · exact (rfl : block g43 1 0 0 = true)
  · exact (rfl : block g43 2 0 0 = true)
  · exact (rfl : block g43 3 0 0 = true)
  · exact g43B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g43G : graphValid g43 (boundsBefore K39) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low43 : Lower true (varsX 43) (graphGoal 43) 5 := lower_forest (g:=g43) (i:=0) (hints:=316659751457290) (before_sound K39 V39) g43G g43T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K43 := extendKnown K39 5 [(43,[]),(45,[32,49,16])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V43 : Known true K43 := extend_ok (m:=43) V39 low43 (by decide +kernel)
def g60Y : Array (Bits × Bits) := #[(0x0,0x0),(0x0,0x0),((seg80 [0x997f936d85e9997f93,0x6d85e9997f936d85e999]),(seg80 [0x188228104489188228,0x10448918822810448918])),((seg80 [0x61d2fd6617e761d2fd,0x6617e761d2fd6617e761]),(seg80 [0x212c00a03122212c00,0xa03122212c00a0312221])),((seg80 [0x16fbe7bafaba16fbe7,0xbafaba16fbe7bafaba16]),0x0),((seg80 [0xece6caff151cece6ca,0xff151cece6caff151cec]),(seg80 [0xc411940e0800c41194,0xe0800c411940e0800c4])),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g60C : List ColumnInfo := [(16,0,44,0,4)]
def g60A : List (List Nat) := [[],[83],[50],[50,82],[82,50],[82]]
def g60D4 (j : Nat) := if j=0 then 0x1f else 0
def g60L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,g60D4)
  | _ => emptyPacking
def g60I (_ _ : Nat) : Option (Nat × Nat) := none
def g60 : Forest := ⟨60,4,fun i => g60Y[i]?.getD (0,0),g60C,g60A,g60L,g60I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g60P4_0 : block g60 4 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g60B4 : block g60 4 0 1=true := g60P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g60T : checkedTables g60 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g60 0 0 0 = true)
  · exact (rfl : block g60 1 0 0 = true)
  · exact (rfl : block g60 2 0 0 = true)
  · exact (rfl : block g60 3 0 0 = true)
  · exact g60B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g60G : graphValid g60 (boundsBefore K43) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low60 : Lower true (varsX 60) (graphGoal 60) 5 := lower_forest (g:=g60) (i:=0) (hints:=140738027323392) (before_sound K43 V43) g60G g60T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K60 := extendKnown K43 5 [(60,[]),(2063,[64,81,33,50]),(2077,[16,80,32,66]),(2078,[81,33,50])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V60 : Known true K60 := extend_ok (m:=60) V43 low60 (by decide +kernel)
def g2105Y : Array (Bits × Bits) := #[((seg80 [0x877fcc7abbf2f53f0e,0xff98f577e5ea7e1dff31]),(seg80 [0xc059c8050704092180,0xb3900a0e081243016720])),(0x0,0x0),(0x0,0x0),((seg80 [0xff953fbdf7fd7fe9ff,0x2a7f7beffaffd3fe54fe]),(seg80 [0x240424822000800048,0x8490440010000901092])),((seg80 [0x21fec3ef3f7b8bde43,0xfd87de7ef717bc87fb0f]),(seg80 [0x9220350c06030ca12,0x4406a180c0619424880d])),((seg80 [0xfd987a63f6ae1447fb,0x30f4c7ed5c288ff661e9]),(seg80 [0x49f05a5c1d4154a493,0xe0b4b83a82a94927c169])),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g2105C : List ColumnInfo := [(32,0,25,0,4)]
def g2105A : List (List Nat) := [[],[64]]
def g2105D4 (j : Nat) := if j=0 then 0x1f else 0
def g2105L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,g2105D4)
  | _ => emptyPacking
def g2105I (_ _ : Nat) : Option (Nat × Nat) := none
def g2105 : Forest := ⟨2105,4,fun i => g2105Y[i]?.getD (0,0),g2105C,g2105A,g2105L,g2105I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g2105P4_0 : block g2105 4 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g2105B4 : block g2105 4 0 1=true := g2105P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g2105T : checkedTables g2105 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g2105 0 0 0 = true)
  · exact (rfl : block g2105 1 0 0 = true)
  · exact (rfl : block g2105 2 0 0 = true)
  · exact (rfl : block g2105 3 0 0 = true)
  · exact g2105B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g2105G : graphValid g2105 (boundsBefore K60) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low2105 : Lower true (varsX 2105) (graphGoal 2105) 5 := lower_forest (g:=g2105) (i:=0) (hints:=281543830405128) (before_sound K60 V60) g2105G g2105T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K2105 := extendKnown K60 5 [(2105,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V2105 : Known true K2105 := extend_ok (m:=2105) V60 low2105 (by decide +kernel)
def g31Y : Array (Bits × Bits) := #[((seg80 [0xe97f5ccf6fbacfb99f,0x5ff7eb78e02dbc913bff]),(seg80 [0x480484828402709098,0x1110e74a0021841121f4])),((seg80 [0x97d5e3ffb9cdfa4776,0xb97d7fcfffd2637efd30]),(seg80 [0x8001e410122384266,0x835200a8a2a0148f830])),((seg80 [0x7bafb37a9f5b751b74,0xfce2b66f5fd3ee73e60e]),(seg80 [0x3147e1280084050981,0x80c8866155c46e32060e])),((seg80 [0x97d6de610f37976f4f,0xd51c9b8c8583b92f4b57]),(seg80 [0xe0e0799a6b150e8d05,0xd70c1825128331274b43])),((seg80 [0xfcaf6c957db4ebfe89,0x43bfe0f4fcbf75ce16e9]),(seg80 [0x2043302ae1872221,0xc22a00a4f45c20ce1609])),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g31C : List ColumnInfo := [(0,1,2078,0,5),(0,2,2077,0,5),(0,8,2071,0,5),(4,0,27,0,5),(16,0,15,0,5),(4,2,25,0,4),(4,8,19,0,4),(16,1,14,0,4),(16,8,7,0,4)]
def g31A : List (List Nat) := [[],[16,66]]
def g31D4 (j : Nat) := if j=0 then 0x26d6214c10 else 0
def g31D5 := limbs80 #[#[0xdc310c2fca6085f14c10,0x20040c2a98480bf28861,0x100]]
def g31H5 (j : Nat) := if j=0 then 0x1e8 else 0
def g31D6 := limbs80 #[#[0x2900fd42fc30fe20fc10,0xa2101272906208078a5c,0x2ce6a10620808398a418,0x1cc520e4288600]]
def g31H6 (j : Nat) := if j=0 then 0x30a806e1000 else 0
def g31D7 (j : Nat) := if j=0 then 0x43b2a190813f else 0
def g31H7 (j : Nat) := if j=0 then 0x11a03773e400030 else 0
def g31L : Nat → Packing
  | 4 => (1,3,4,0,0,0,0,g31D4)
  | 5 => (4,2,4,0,0,6,0,g31D5)
  | 6 => (4,1,4,0,0,8,0,g31D6)
  | 7 => (1,0,4,0,0,0,0,g31D7)
  | _ => emptyPacking
def g31I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 2 0 5 0 1 g31H5
  | 6 => lookupWord 1 7 0 6 2 0 g31H6
  | 7 => lookupWord 1 11 0 7 2 1 g31H7
  | _ => fun _ => none
def g31 : Forest := ⟨31,7,fun i => g31Y[i]?.getD (0,0),g31C,g31A,g31L,g31I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g31P4_0 : block g31 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g31B4 : block g31 4 0 1=true := g31P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g31P5_0 : block g31 5 0 4=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g31B5 : block g31 5 0 4=true := g31P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g31P6_0 : block g31 6 0 4=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g31B6 : block g31 6 0 4=true := g31P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g31P7_0 : block g31 7 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g31B7 : block g31 7 0 1=true := g31P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g31T : checkedTables g31 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g31 0 0 0 = true)
  · exact (rfl : block g31 1 0 0 = true)
  · exact (rfl : block g31 2 0 0 = true)
  · exact (rfl : block g31 3 0 0 = true)
  · exact g31B4
  · exact g31B5
  · exact g31B6
  · exact g31B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g31G : graphValid g31 (boundsBefore K2105) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low31 : Lower true (varsX 31) (graphGoal 31) 8 := lower_forest (g:=g31) (i:=0) (hints:=69122656266) (before_sound K2105 V2105) g31G g31T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K31 := extendKnown K2105 8 [(31,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V31 : Known true K31 := extend_ok (m:=31) V2105 low31 (by decide +kernel)
def g47Y : Array (Bits × Bits) := #[((seg80 [0xc3bdcafe3dff7f4758,0xf0fff7e8b1af3c5f5bd9]),(seg80 [0x1264053dc034d30390,0x20bf2f8c2208244d4359])),((seg80 [0x7f673573facbbbbef7,0x9ff55f3f5e74f7e0a7f6]),(seg80 [0x81460509a07b1a8594,0x441540c3e6061e083c4])),((seg80 [0x3d7ff97dff71deda7f,0xeecf8bd7f6fd7373f479]),(seg80 [0x6201aa800804802868,0xc28089d340951a137430])),((seg80 [0xcbbe6fc298bff77ffe,0x553a75f8492bdd9f0fae]),(seg80 [0xe030d0d41c41247a4a,0x5410103105b89d1a0cae])),(0x0,0x0),((seg80 [0xf4e8f6ae951758f5b0,0xffb2b6d0bb9af8bc7967]),(seg80 [0x501f1a03be18207db8,0x9923024ab2d258b43963])),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g47C : List ColumnInfo := [(0,1,2094,0,5),(0,8,39,0,5),(2,0,45,0,5),(4,0,43,0,5),(32,0,15,0,5),(2,1,44,0,4),(4,8,35,0,4),(32,1,14,0,4),(32,8,7,0,4)]
def g47A : List (List Nat) := [[],[48,33]]
def g47D4 (j : Nat) := if j=0 then 0x2786055121 else 0
def g47D5 := limbs80 #[#[0xbd42506fea890df55121,0x2001002a98480bfa9283,0x308]]
def g47H5 (j : Nat) := if j=0 then 0x270 else 0
def g47D6 := limbs80 #[#[0x3300fd41fd21fc30fe20,0x4059cc520e4208099970,0x90620807398b424c7210,0x20a41883001062]]
def g47H6 (j : Nat) := if j=0 then 0x5d9ea8 else 0
def g47D7 (j : Nat) := if j=0 then 0x43b2a190813f else 0
def g47H7 (j : Nat) := if j=0 then 0x6405f48005300000980 else 0
def g47L : Nat → Packing
  | 4 => (1,3,4,0,0,0,0,g47D4)
  | 5 => (4,2,4,0,0,6,0,g47D5)
  | 6 => (4,1,4,0,0,8,0,g47D6)
  | 7 => (1,0,4,0,0,0,0,g47D7)
  | _ => emptyPacking
def g47I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 2 0 5 0 1 g47H5
  | 6 => lookupWord 1 7 0 6 2 0 g47H6
  | 7 => lookupWord 1 11 0 7 2 1 g47H7
  | _ => fun _ => none
def g47 : Forest := ⟨47,7,fun i => g47Y[i]?.getD (0,0),g47C,g47A,g47L,g47I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g47P4_0 : block g47 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g47B4 : block g47 4 0 1=true := g47P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g47P5_0 : block g47 5 0 4=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g47B5 : block g47 5 0 4=true := g47P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g47P6_0 : block g47 6 0 4=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g47B6 : block g47 6 0 4=true := g47P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g47P7_0 : block g47 7 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g47B7 : block g47 7 0 1=true := g47P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g47T : checkedTables g47 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g47 0 0 0 = true)
  · exact (rfl : block g47 1 0 0 = true)
  · exact (rfl : block g47 2 0 0 = true)
  · exact (rfl : block g47 3 0 0 = true)
  · exact g47B4
  · exact g47B5
  · exact g47B6
  · exact g47B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g47G : graphValid g47 (boundsBefore K31) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low47 : Lower true (varsX 47) (graphGoal 47) 8 := lower_forest (g:=g47) (i:=0) (hints:=175922263623690) (before_sound K31 V31) g47G g47T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K47 := extendKnown K31 8 [(47,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V47 : Known true K47 := extend_ok (m:=47) V31 low47 (by decide +kernel)
def g55Y : Array (Bits × Bits) := #[((seg80 [0xffee9d1e5eb7fc9e9d,0xcffbcfb9a73ff2f5f937]),(seg80 [0x120590329a8b09090,0xb95e63241122953823])),((seg80 [0x86b3e6ffef4f3be96b,0x77b4b947fdf18f1f46ee]),(seg80 [0x41c21504a5ec76f051,0x704a96385001e1f4606])),((seg80 [0x7fb76ffdefcbb3ebfb,0xbc7772cfdff38d3baef9]),(seg80 [0x861960005213010f28,0x182a12185a63812088f9])),(0x0,0x0),((seg80 [0xa2dddbaaddb6edfe86,0xd3aeefbda94ef2eed14f]),(seg80 [0x8884a48c56534e2f02,0xd102a094c348d86ac14c])),((seg80 [0xd9a73610099fb0d53f,0x5b436a822b9bbc5cfad0]),(seg80 [0xcc108ed2fde140f75f,0x4240c4823fd2da5cf2d0])),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g55C : List ColumnInfo := []
def g55A : List (List Nat) := [[],[32,65]]
def g55D4 (j : Nat) := if j=0 then 0x1f else 0
def g55L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,g55D4)
  | _ => emptyPacking
def g55I (_ _ : Nat) : Option (Nat × Nat) := none
def g55 : Forest := ⟨55,4,fun i => g55Y[i]?.getD (0,0),g55C,g55A,g55L,g55I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g55P4_0 : block g55 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g55B4 : block g55 4 0 1=true := g55P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g55T : checkedTables g55 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g55 0 0 0 = true)
  · exact (rfl : block g55 1 0 0 = true)
  · exact (rfl : block g55 2 0 0 = true)
  · exact (rfl : block g55 3 0 0 = true)
  · exact g55B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g55G : graphValid g55 (boundsBefore K47) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low55 : Lower true (varsX 55) (graphGoal 55) 5 := lower_forest (g:=g55) (i:=0) (hints:=175990580447248) (before_sound K47 V47) g55G g55T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K55 := extendKnown K47 5 [(55,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V55 : Known true K55 := extend_ok (m:=55) V47 low55 (by decide +kernel)
def g59Y : Array (Bits × Bits) := #[((seg80 [0x9bdfeffebb5ef79e5e,0xd666bf7bffbffe73dd7b]),(seg80 [0xc000bd8a00801c124a,0xc000044e2e993a03cc62])),((seg80 [0xe47355f7d6e17eeba7,0xedbd7c9f2d4669be6fc4]),(seg80 [0xcb16900e1464222b59,0x8eb43096281448b26bc4])),(0x0,0x0),((seg80 [0xfffe74fbf5e3cfe3ab,0x2dddeeb7ef69f39eb6f5]),(seg80 [0xac00a74cb90c1d5a2,0x1409ce210120d31c34b1])),((seg80 [0xa9fbbb870e9ef47fd7,0xdbe3f37973fe5fe94b9b]),(seg80 [0x157a00305334416c35,0x136063b1514201e80319])),((seg80 [0x770e5e1ae739df0b69,0xf6d9cfd68347b4eeb836]),(seg80 [0xb5f4f35002442f6268,0x72e188b49bc62cee9816])),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g59C : List ColumnInfo := [(0,2,2105,0,5),(0,8,51,0,5),(16,0,43,0,5),(32,0,27,0,5)]
def g59A : List (List Nat) := [[]]
def g59D6 (j : Nat) := if j=0 then 0x7209f else 0
def g59L : Nat → Packing
  | 6 => (1,0,2,0,0,0,0,g59D6)
  | _ => emptyPacking
def g59I (_ _ : Nat) : Option (Nat × Nat) := none
def g59 : Forest := ⟨59,6,fun i => g59Y[i]?.getD (0,0),g59C,g59A,g59L,g59I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g59P6_0 : block g59 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g59B6 : block g59 6 0 1=true := g59P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g59T : checkedTables g59 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g59 0 0 0 = true)
  · exact (rfl : block g59 1 0 0 = true)
  · exact (rfl : block g59 2 0 0 = true)
  · exact (rfl : block g59 3 0 0 = true)
  · exact (rfl : block g59 4 0 0 = true)
  · exact (rfl : block g59 5 0 0 = true)
  · exact g59B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g59G : graphValid g59 (boundsBefore K55) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low59 : Lower true (varsX 59) (graphGoal 59) 7 := lower_forest (g:=g59) (i:=0) (hints:=316728470934026) (before_sound K55 V55) g59G g59T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K59 := extendKnown K55 7 [(59,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V59 : Known true K59 := extend_ok (m:=59) V55 low59 (by decide +kernel)
def g61Y : Array (Bits × Bits) := #[((seg80 [0xbffffffffffffdffef,0xfdf7f7bfff7ffffe9ffe]),(seg80 [0x18400014010aa12400,0xc44b004327429068764])),(0x0,0x0),((seg80 [0xd08ceeede6cabfad3f,0x4f2ddbcd89df1559627f]),(seg80 [0x98f60b7040f15a00bd,0x4fb543d883091159205f])),((seg80 [0x7f3c25d7c9ee7afc11,0xe7fd5f4345f2be9d6dad]),(seg80 [0x60b9ac2bf830608c44,0xb3f05e011583969d6ca8])),((seg80 [0x5aeffb4e5d35f767f3,0xbbeeadfb73af63eff083]),(seg80 [0xa3af850896941403c3,0xb08809d3c10bd0e95083])),((seg80 [0xf7fd86b42f22aad03e,0xdf581ff7adb4ccc1ff59]),(seg80 [0x1029487726c155236,0x7118653388bc84c0fb19])),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g61C : List ColumnInfo := [(0,4,57,0,6),(0,8,53,0,6),(0,32,29,0,6),(0,1,60,0,5),(16,0,45,0,5),(16,1,44,0,4)]
def g61A : List (List Nat) := [[],[83],[50],[50,82],[82,50],[82]]
def g61D3 (j : Nat) := if j=0 then 0xb05831504208410 else 0
def g61D4 := limbs80 #[#[0x8410821595d63208410,0x2085657510821043922a,0x75cc658c810aaae62a04,0x94420421f3a0cb190211,0x108bae63288408476711,0xb22c6290219358e52148,0x8a40861e6458c520430e,0x1879926314810c3ac931,0x3d9442c431b30ac82902,0x8430caacb188421845d7,0x2ebaec610861279d3630,0xb18429865563144214c2,0xc61555cc6214530c38a8,0xe74d9421cc24f3a6c610,0x1940218f6eca80a010c3,0x861e3a2c728043c91084,0xc82146210dc57310a310,0x20843395d8428c421d48,0xc3d769504308792a9884,0x75354c218beeca98a610,0x30868f3a6a6a9843559c,0x3ce9a9ca610c3e741815,0x260c018d59261d4c21a,0x8aca094887c7064584c4,0x125190d00f4e8dcd0c4b,0x5b9ada1957b6155493d3,0x4102081e9ddd1c,0x0,0x10408200000000000]]
def g61H4 (j : Nat) := if j=0 then 0x4 else 0
def g61D5 := limbs80 #[#[0x18f990520425d6314810,0x108f99353087a4421042,0x410bd98420043e421080,0x8410fc98021043f16008,0x8410f910821043e6320,0x308410dd54c21043e652,0x5408410dd15021043775,0x66408410bd1902104376,0x6e528c810bd98632042f,0x27d658c8109f19632043,0x427f658c8109f9963204,0x427d65108109f194420,0x20427f65108109f99442,0x520436e5214810be9805,0x52042be6414810b758c,0x8c520427e6014810de98,0x98c520427d6314810d75,0xf990520433d6414810d7,0x9f58e520427e6414810c,0xd7d4d530427e6494810,0x10be983530427c6254c1,0xb109f98b530437a60d4c,0xb10db94842c42f66110,0x94b109fd9442c427d651,0x108430f58c4210c27e64,0x5408430b7d8c210c3765,0xf65084309f594210c33e,0x5d658c430b798a310c27,0x37462944309f98a510c3,0xc3745108530dd98a510c,0x4c33c5408530b758c214,0x14c27e65085309f19421],#[0x514c37462145309f9885,0xc218c3d63108630dd988,0x82318c27e6508630b7d8,0x94421cc2de628c630f69,0xf59421cc2dd6308730dd,0x9f98a51cc27f65087309,0x1bd98450087795014021,0x21b798c50086dd631402,0x21b718d50086be64140,0x4021af19150086df6354,0x940219f982500877b509,0x4940219f58e500877441,0x608c421bd987500867e6,0x4428c421f98ca31086f6,0xd5538c421f998a31087e,0x774548c421f594e31087,0x86f4648c421dd9523108,0x87e66210421bd992310,0x3086f66110c21dd54c41,0x430873e5410c21d754c4,0xf430867e6510c219f594,0x97430867c65d0c21d754,0xd97430867e65d0c219f5,0x754c53086f66114c219f,0xd7d4d530867e6514c21d,0x19f191530867c6054c21,0x21af992530875f5394c2,0xc21bd987530867d6594c,0x4c219f98353086be64d4,0xd4c21cf593530877661d,0x1150219f993530873e64,0x6015021cf95054086f66],#[0xe60950219f58c540867e,0x7e64948319f58e540867,0x67e6294231b758c508c6,0xc6dd6314a31bd986328c,0x8c67e6094a31af990528,0x42078060090009f99252,0x1202103f06c0cc1802a0,0x83c0720de1a43005a0a8,0x58a813224c468871081f,0xd219e324630c016e2c45,0x1da3a8738e11bc36c6c0,0xe4448710b20a3fc7c8f3,0xd49792c24c48c9011a22,0xaf95c2ac540a51472824,0x99231260cbd1742d65a0,0x33606a8d39a133c660ca,0xae744e59c53846fcdb1b,0x804fd9f23de7a4f19dd3,0x51722844a8710b21041a,0xda5549890d1ea3a4688c,0x794ec9c1352674c89852,0x558a995029a528a45442,0xcb4d66ac7588af95dab8,0xdd7a2ee5d0b956fadc5a,0x8930c612c0d802fd5f4b,0x1800140a700b1e636c61,0x4008000004100200244,0x4108104104ca410c1040,0x11010020440430400c1a,0x1a410030a90441010c,0x404000102906a002,0x10016410016810000810],#[0x104000404008100000,0x59040040a010e8003a01,0xa8064a020240420190,0x901003040014642641a0,0x1001000102080001040,0x2080c01c01c01c01c01c,0x8104004008100308110,0x42041004040001040040,0x20400000410810400b10,0x400b008407000400204,0x400020400c0042070040,0x81000040c010010300,0x4000100000000004004,0x1a040000040]]
def g61H5 := limbs80 #[#[0x168005681073012,0x104940320db0b84680,0x1043b4400018152070,0x7ad000290c0000002290,0x8001a5d0002c70dbc000,0x230dba4bd87210411801,0x1e0b110286411f22,0x101f36000001acae00,0x3e50281500000000000,0x414b06182051a0000007,0x40925ba00072d800082d,0xfe5ec098000000000302,0x7640a000b10886083,0x6c1893600000,0xf690400040282171600,0x1e0e0004827140411b,0x438e000000000]]
def g61D6 := limbs80 #[#[0xf421042e8a2985d94430,0xfaa6085f94810be29021,0x78c430bf296217f53042,0xf18c617c514c2fca2187,0x631086fca010df94730e,0xea610df54c21fa20843f,0x94831bf2a0437c54086f,0x100217e528c6fca118df,0x52043f884087f8c810fe,0xa6087f54c10ff29021fc,0x8530fe10861fc42c43fe,0x8043fc21cc3f843187f0,0x87fca010ff54021fe2,0x610ffd0c21fe21843ff5,0xc21ff29843fd53087f8a,0x463fe54087f8a810ffd4,0x8c7fc6518ff94231fe28,0xe12012000ff29463fc52,0x40ac13420c388550810c,0x48a6d49c8bd059e73866,0x3926fad5190af3594aad,0x288709207bf07acef1d1,0x4544a7c4d99892964346,0x74edf5a9b155c2b0541a,0x7aca06cab90315e07be5,0x306908052d07aca06292,0x289a1243000e412602,0xac9883018ac98f42c86,0x29263400629062486002,0x21400929263d0b21400a,0xa00314931a0031683d0b,0x38840290510c00310620],#[0x831443000ca14420149,0xa886001c83546028c518,0x830012520c490c004106,0x63d092180072d08b18,0xaa48441242010200830,0x529261949318051a4201,0x50018920a0028c49080,0x320c2800a52050014839,0x86180041a83000a3540,0x22083000a4106001470,0xa8064506001481800424,0x16830d420c002a8500c8,0x8a48430c00196841c003,0x112100]]
def g61H6 := limbs80 #[#[0x4520041208a0012b0993,0x23953471032430422800,0x5400002250120228608,0x7f03c3591993400c22e2,0x24f600480004ebd402,0x10ee4d9980c800000,0x1269981200000000,0x92cc03306d5086000,0x5c0000000002c682100,0x3024d94a34cbc1d00001,0x40001607e091c0c6000,0x46070fd6218c373a0621,0xc42a628db02241684a2a,0x5be21201c316808c804b,0x25124d54049486584ea0,0xf82f827d50c4421440b7,0x80d64c64133f0b3207,0x2975830584c00,0x740a2839505fe0294390,0x16a000af7c155061c15,0xb10fa14ac06c14f00,0xc000036a000189d1c198,0x143fa82e6438605,0x26444c080338a7305100,0xd811f061000141d982d8,0xbaa10a2b0503da00ea52,0x272832a1082be04860,0xc0004146802661c00003,0x4ed0b992d487cf052811,0x13ba6d1ee1609c280430,0x20468066f0bc483343db,0x1a1a94253041a118000],#[0x90525ac14f812000000,0x50848000e40e00000004,0x12e118000190de4c640c,0x60400000000f1,0x349f204b000041140000,0xe208440007205f0f2000,0xf077020380f000030,0xf8b33a1074c5a03b40d0,0x68e5a400000655111022,0x82ad22c21d4000383754,0x48215b70,0x7ca8540003135003040f,0x87dd07485101a0501dc0,0x60ad6869d0d0e20e519e,0xcde08a4c2d1134216020,0x36111c200c4135134f4,0x4000580100010824447a,0x1e819e89ce90e3286601,0xf2ce6113410000000,0xe8360000a0ac00000000,0x6dc8445220fc47d40f,0xc1950e6214180de82800,0x34320000d66d013603d5,0x2a0002a86a04f6064010,0x81c70dec51dc00402cf0,0x954834f0d6602c012e,0x112919d86913c405741e]]
def g61D7 := limbs80 #[#[0xfe30fd30fc30ff10fc10,0x4c00fe31fc31fc21ff30,0x881134873c194a03b130,0x8c012a874522042a1d14,0xc012a874523004aa1d14,0x80c8745230042a1d148,0xd148810a8745220421d1,0x2a1]]
def g61H7 := limbs80 #[#[0x204220000b0842c40804,0x14800000000390798061,0x2b28890048ba044a184,0xc85002400101e0238000,0x581c42fa42,0x1886e30000f0db01,0x5400000000030e400,0x1ff2180000000e700000,0x8ce05a00082d6b88000e,0x1ca808cc071,0x1dc2000000000105e,0x244dc03cae060000,0xf11cc000225874000000,0xe510453098c2600048,0x48a00,0x501dc11db7c458a620,0xd478000000000e0b7818,0x40000006400001c16000,0x8d2b396f888000a0841c,0x7cc2205a0e102a41f60,0x140005c0484803220922,0x88006265f00060668036,0x60d00000010600000001,0x5c2745790bc4c0002a19,0xd858313f030000000000,0x1ea18504000547000209,0xee0b8c8003c3561160,0x7c1911600008400000]]
def g61D8 (j : Nat) := if j=0 then 0x4407f else 0
def g61H8 := limbs80 #[#[0x81608806000002961690,0x29c0074750d084,0x800a00000481a0800000,0x188000407380ca21b54,0x1304002800]]
def g61L : Nat → Packing
  | 3 => (1,5,3,0,0,0,0,g61D3)
  | 4 => (37,4,3,0,0,8,0,g61D4)
  | 5 => (146,3,3,0,0,11,0,g61D5)
  | 6 => (52,2,3,0,0,11,0,g61D6)
  | 7 => (9,1,3,0,0,9,0,g61D7)
  | 8 => (1,0,3,0,0,0,0,g61D8)
  | _ => emptyPacking
def g61I : Nat → Nat → Option (Nat × Nat)
  | 4 => lookupWord 1 2 0 4 0 0 g61H4
  | 5 => lookupWord 15 101 4 13 6 3 g61H5
  | 6 => lookupWord 58 293 6 15 8 3 g61H6
  | 7 => lookupWord 25 163 5 13 6 3 g61H7
  | 8 => lookupWord 4 31 4 11 4 3 g61H8
  | _ => fun _ => none
def g61 : Forest := ⟨61,8,fun i => g61Y[i]?.getD (0,0),g61C,g61A,g61L,g61I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g61P3_0 : block g61 3 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g61B3 : block g61 3 0 1=true := g61P3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g61P4_0 : block g61 4 0 37=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g61B4 : block g61 4 0 37=true := g61P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g61P5_0 : block g61 5 0 4=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g61P5_4 : block g61 5 4 96=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g61P5_100 : block g61 5 100 46=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g61B5 : block g61 5 0 146=true := (@block_merge g61 5 0 4 142 g61P5_0 (@block_merge g61 5 4 96 46 g61P5_4 g61P5_100))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g61P6_0 : block g61 6 0 2=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g61P6_2 : block g61 6 2 21=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g61P6_23 : block g61 6 23 29=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g61B6 : block g61 6 0 52=true := (@block_merge g61 6 0 2 50 g61P6_0 (@block_merge g61 6 2 21 29 g61P6_2 g61P6_23))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g61P7_0 : block g61 7 0 9=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g61B7 : block g61 7 0 9=true := g61P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g61P8_0 : block g61 8 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g61B8 : block g61 8 0 1=true := g61P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g61T : checkedTables g61 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g61 0 0 0 = true)
  · exact (rfl : block g61 1 0 0 = true)
  · exact (rfl : block g61 2 0 0 = true)
  · exact g61B3
  · exact g61B4
  · exact g61B5
  · exact g61B6
  · exact g61B7
  · exact g61B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g61G : graphValid g61 (boundsBefore K59) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low61 : Lower true (varsX 61) (graphGoal 61) 9 := lower_forest (g:=g61) (i:=0) (hints:=175991253368844) (before_sound K59 V59) g61G g61T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K61 := extendKnown K59 9 [(61,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V61 : Known true K61 := extend_ok (m:=61) V59 low61 (by decide +kernel)
def g62Y : Array (Bits × Bits) := #[(0x0,0x0),((seg80 [0xffffbfefd7ffffbfdf,0xfc7bffffffffbff5dbff]),(seg80 [0xa9411402004040cf05,0xb84022002d08aa9413b1])),((seg80 [0x3acbd7fa3effaffffe,0x1bcd775efbf7f48be77e]),(seg80 [0x2a00ad981ae961072,0x121555f90b5440be04e])),((seg80 [0xffb5691df9de5d60ff,0xffb6c9e7651bcb7e7cab]),(seg80 [0x4b0c18693432b329b,0x12b289d5e083416c6caa])),((seg80 [0x962e795fad636ccce7,0x73f5a4e255c957faf684]),(seg80 [0x59f20f291809ab49e4,0x60b4ac6e49e81cfad604])),((seg80 [0xd9b9e53579fab4d027,0xefd77fcbea025acebd43]),(seg80 [0x7c4ab2e9311c7c6816,0x4f45c88bca0e3ec2bd43])),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g62C : List ColumnInfo := [(0,8,54,0,6),(0,16,46,0,5),(0,32,30,0,5),(0,48,14,0,4)]
def g62A : List (List Nat) := [[],[84]]
def g62D3 := limbs80 #[#[0xc629221831906394810,0xc30632]]
def g62D4 := limbs80 #[#[0x9ed9510042e86244010,0x10b518d10042e4624401,0x810ad993310427765440,0x4810d394e520434d5394,0x14c10d3d8e520434c639,0x414c109798c530426e62,0x5494c10c7951530423e6,0x45384110d914a104431e,0x4c5314910da14b104435,0x34c6314910d3d4c52443,0x431c5414d10d3d8c5244,0x4426e6294d10c7d50534,0x8423e6494d109798e53,0x51842b664cc6109b98a5,0x253c423e6414e109b189,0x9251cc26e62947308f99,0x191500c66c62540318f9,0x302a241e18120c06008f,0x6c66605a544e48423c36,0xa8a29c96908a847e7872,0xd2ccc6c0bab4ae]]
def g62H4 (j : Nat) := if j=0 then 0x23c else 0
def g62D5 := limbs80 #[#[0x6c52442bca6085b94810,0x7ca998cf95030ae29a21,0xe84010fa88021f910042,0xa188217e50043ee20087,0xe52042fca2087dcc410f,0xca6087754c10be29821e,0xc4110fb082217e53043b,0x29a21dc53443d8a4887e,0x10843bea6885f94d10be,0x63085f94210fb88421fb,0x4e10bea8c21f731843e8,0x9e217c53c42fca7085f1,0x10c3b8621877cc030bf2,0x3986f95030bf288617d5,0x31bf28e617d51cc3be6,0x663df310c6fca018df54,0x37ca998df94331bea8,0x251007434150802c1003,0xa84d230fc7437190b454,0x4fc77381b4cc612e15c,0x72a54ca34f255208d422,0xd6a33594c5602f574b55,0x1c040c040ef7639dc0d,0x10041104000401000c07,0x40100401c08f0220080,0x84030003c08802007020,0x802204000812100c4100,0x84032008060481000a06,0x204010580200]]
def g62H5 := limbs80 #[#[0x8cb40000000e1000300,0x7c0049d00000000000,0x2c000000000000000000,0x30b0003,0x0,0x39b001a518b,0x23e1000799001b500000,0x300800001c2000000c,0x5000,0xc8000000000012300000,0xa0000002098000000036,0x1232c6800000000002,0xe2a8e448,0x430000000000000000,0x1810000000,0xc0000000000,0x0,0x16999a0000000000,0x1e0010c0000,0x180daa800cae,0xe3924780000000000,0x0,0xa8624acbc2200031c000,0x95620c1ed0800,0x0,0xc4800e9a000000000000,0x7d2000002]]
def g62D6 := limbs80 #[#[0xfc30ff10fe10fd10fc10,0x36241200ff31fc31ff30,0x8044601118048d755d48,0xcf2300cd1805460111,0x1a300af23]]
def g62H6 := limbs80 #[#[0x6800d1016116fd2281e9,0x60800c26894c3f26eb02,0x800000974420a1000845,0x35bc81a8a000c3c1442b,0x2097e100180801d6,0xb64000000008b4006430,0xf948008c4002ceba869e,0xb6e0f0a65b8ff95410e3,0x8d00146898da0e2ee9fe,0x1348570000014c0c65,0x402716700001c28cc800,0x639502b34752c00481c4,0xd7dcc62022c1229c81de,0xca126c]]
def g62D7 (j : Nat) := if j=0 then 0x7209f else 0
def g62H7 := limbs80 #[#[0x68a04e980082013b4c45,0x3d0a3ee6000401]]
def g62L : Nat → Packing
  | 3 => (2,4,2,0,0,3,0,g62D3)
  | 4 => (36,3,2,0,0,8,0,g62D4)
  | 5 => (50,2,2,0,0,9,0,g62D5)
  | 6 => (8,1,2,0,0,8,0,g62D6)
  | 7 => (1,0,2,0,0,0,0,g62D7)
  | _ => emptyPacking
def g62I : Nat → Nat → Option (Nat × Nat)
  | 4 => lookupWord 1 2 0 5 1 0 g62H4
  | 5 => lookupWord 12 191 3 11 6 1 g62H5
  | 6 => lookupWord 17 89 5 11 6 1 g62H6
  | 7 => lookupWord 3 17 3 8 3 1 g62H7
  | _ => fun _ => none
def g62 : Forest := ⟨62,7,fun i => g62Y[i]?.getD (0,0),g62C,g62A,g62L,g62I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g62P3_0 : block g62 3 0 2=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g62B3 : block g62 3 0 2=true := g62P3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g62P4_0 : block g62 4 0 36=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g62B4 : block g62 4 0 36=true := g62P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g62P5_0 : block g62 5 0 6=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g62P5_6 : block g62 5 6 44=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g62B5 : block g62 5 0 50=true := (@block_merge g62 5 0 6 44 g62P5_0 g62P5_6)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g62P6_0 : block g62 6 0 8=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g62B6 : block g62 6 0 8=true := g62P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g62P7_0 : block g62 7 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g62B7 : block g62 7 0 1=true := g62P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g62T : checkedTables g62 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g62 0 0 0 = true)
  · exact (rfl : block g62 1 0 0 = true)
  · exact (rfl : block g62 2 0 0 = true)
  · exact g62B3
  · exact g62B4
  · exact g62B5
  · exact g62B6
  · exact g62B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g62G : graphValid g62 (boundsBefore K61) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low62 : Lower true (varsX 62) (graphGoal 62) 8 := lower_forest (g:=g62) (i:=0) (hints:=352533332101120) (before_sound K61 V61) g62G g62T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K62 := extendKnown K61 8 [(62,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V62 : Known true K62 := extend_ok (m:=62) V61 low62 (by decide +kernel)
def g2079Y : Array (Bits × Bits) := #[((seg80 [0x7ddffdadaee848fbfe,0x24e2a7edb32fe384b2af]),(seg80 [0x203006000010028104,0x802244d501208020ac])),((seg80 [0x962a8b5f65bfffedcf,0xdf19f80ae5d23e5a2d7a]),(seg80 [0x207d1b061014002884,0x100584c55a23210293a])),((seg80 [0xcd10ffedd9fee9757,0xf6fe56b01cc2373b43e1]),(seg80 [0xc900a01808e8911453,0x664a01810810052b0241])),((seg80 [0xf2ae6e82bfe5bd6ea9,0x3dd7e8374b996c6dce1c]),(seg80 [0x58000071a5201c0238,0x3c1c802102140c4dc600])),((seg80 [0xfdfef553dd9990928f,0x3b070758abe5d6f57053]),(seg80 [0x86c6a04d36870422ab,0x50031d9020e44a745053])),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g2079C : List ColumnInfo := [(2,0,29,0,6)]
def g2079A : List (List Nat) := [[],[50]]
def g2079D6 (j : Nat) := if j=0 then 0x3f else 0
def g2079L : Nat → Packing
  | 6 => (1,0,1,0,0,0,0,g2079D6)
  | _ => emptyPacking
def g2079I (_ _ : Nat) : Option (Nat × Nat) := none
def g2079 : Forest := ⟨2079,6,fun i => g2079Y[i]?.getD (0,0),g2079C,g2079A,g2079L,g2079I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g2079P6_0 : block g2079 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g2079B6 : block g2079 6 0 1=true := g2079P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g2079T : checkedTables g2079 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g2079 0 0 0 = true)
  · exact (rfl : block g2079 1 0 0 = true)
  · exact (rfl : block g2079 2 0 0 = true)
  · exact (rfl : block g2079 3 0 0 = true)
  · exact (rfl : block g2079 4 0 0 = true)
  · exact (rfl : block g2079 5 0 0 = true)
  · exact g2079B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g2079G : graphValid g2079 (boundsBefore K62) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low2079 : Lower true (varsX 2079) (graphGoal 2079) 7 := lower_forest (g:=g2079) (i:=0) (hints:=68853958660) (before_sound K62 V62) g2079G g2079T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K2079 := extendKnown K62 7 [(2079,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V2079 : Known true K2079 := extend_ok (m:=2079) V62 low2079 (by decide +kernel)
def g2095Y : Array (Bits × Bits) := #[((seg80 [0xeffe7feffb81efe56,0xd11917dd777d3d66cc64]),0x0),((seg80 [0xf617fa6995efe159f7,0x2ef6bfa1e982cf1811bf]),(seg80 [0x58921802402200a40,0x2068e4101010708013c])),((seg80 [0xdf72790b2ffaec2938,0x7bff6c2aa93088eb6783]),(seg80 [0x42728628402c1905a0,0x107960282a8c88636483])),((seg80 [0xf7470ed2ceb76b47d9,0xdf7de316c08a5393b25a]),(seg80 [0x82240a05cacc049033,0x5d102114ccc800b39242])),(0x0,0x0),((seg80 [0x7e46deb52a5f3a16b,0x52c3618e8721ff85b7b0]),(seg80 [0xed1955f788a2490806,0x46c189b397215944b7b0])),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g2095C : List ColumnInfo := [(0,32,2063,0,5)]
def g2095A : List (List Nat) := [[],[50]]
def g2095D5 (j : Nat) := if j=0 then 0x3f else 0
def g2095L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,g2095D5)
  | _ => emptyPacking
def g2095I (_ _ : Nat) : Option (Nat × Nat) := none
def g2095 : Forest := ⟨2095,5,fun i => g2095Y[i]?.getD (0,0),g2095C,g2095A,g2095L,g2095I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g2095P5_0 : block g2095 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g2095B5 : block g2095 5 0 1=true := g2095P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g2095T : checkedTables g2095 5 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g2095 0 0 0 = true)
  · exact (rfl : block g2095 1 0 0 = true)
  · exact (rfl : block g2095 2 0 0 = true)
  · exact (rfl : block g2095 3 0 0 = true)
  · exact (rfl : block g2095 4 0 0 = true)
  · exact g2095B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g2095G : graphValid g2095 (boundsBefore K2079) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low2095 : Lower true (varsX 2095) (graphGoal 2095) 6 := lower_forest (g:=g2095) (i:=0) (hints:=422212734027776) (before_sound K2079 V2079) g2095G g2095T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K2095 := extendKnown K2079 6 [(2095,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V2095 : Known true K2095 := extend_ok (m:=2095) V2079 low2095 (by decide +kernel)
def g2103Y : Array (Bits × Bits) := #[((seg80 [0xf7af79b6bf7b2cbcd5,0x34d2bdf57c647cc6aa96]),(seg80 [0x80208010010000240,0x1000044100041000a880])),((seg80 [0xeedbaf5bd5eedbc3e6,0xd2edc22a93fff5292579]),(seg80 [0x12800100208000100,0x850000000124200111])),((seg80 [0x327bb87f6df178312a,0xbb7b71c3d00b6bb554c6]),(seg80 [0x4211f1820946334811,0x8478628051084b951446])),(0x0,0x0),((seg80 [0x52c8fce45f9c9eefc9,0x6b6f2ef8e4dc0659d223]),(seg80 [0xd095224c5401284807,0xa34202b88ec800c95222])),((seg80 [0x1956e3789d78e759dc,0x2d8c7cb78bb9da5e5d08]),(seg80 [0x4c0552e65201204a4,0x2c18382a8f30415e4408])),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g2103C : List ColumnInfo := [(1,0,54,0,6),(2,0,53,0,6),(4,0,51,0,5),(16,0,39,0,5),(32,0,2071,0,5),(20,0,35,0,4),(36,0,19,0,4),(48,0,7,0,4)]
def g2103A : List (List Nat) := [[],[84],[66],[66,82],[82,66],[82],[16],[16,84],[16,66],[16,66,82],[16,82,66],[16,82]]
def g2103D3 (j : Nat) := if j=0 then 0xcc0764c93148110 else 0
def g2103D4 := limbs80 #[#[0xa4290221b858d2148110,0x887c1324c52044371b1,0x85c632481109e0ec98a4,0x4920442d4ba464902217,0x10d9264b0064885c9731,0x3aa641922193595320c9,0x8648846d76d4832442a7,0x11bdc9654c91087ee8b2,0x454a324421fba2ca9922,0x4910c3cc9a9c648862d6,0x37bb2a4292219358d521,0x31aa48864c63d4952442,0x22187d936354910c3ec8,0xc654c9314821fba2c7a9,0x550d20a5ae9196a29064,0x326996c2a80651ddc56,0x998130fce4ccb4644c34,0xfae2cab26249f9e1c9b1,0x10000107735b432b12,0x2a408282000001,0x305080290c200]]
def g2103H4 (j : Nat) := if j=0 then 0x60 else 0
def g2103D5 := limbs80 #[#[0x97d8d52443e12148110,0x10d34c9500caad648c92,0x110fc4c520443f121481,0x8110fa4c920443f36148,0x48110fa14920443ea324,0x348110be58d20443eb52,0x320c910be58032442fb6,0xd650c910dbd4832443cd,0x6d524c9109f994324427,0x27e654c9109f59532443,0x436d528c910be5823244,0x442bd648c910d7d4e324,0x24427d658c910af99232,0x524436d52149109f9963,0x452442de6314910b758c,0x4952442fb60549109f99,0xd8d52442dc6354910dbd,0x718d524437b6054910b7,0x9fd8d524435f6354910d,0xdbd4a52442f96094910,0x209f58f524427d659491,0x520fad8121482fb60485,0x8520dbd4d214836d5348,0x4c520f34c931482ee65c,0x2545209f995314827c65,0x32d4520b7d8d51482ef6,0xd63d4520db8cb514836d,0xed644c920f3d4d324827,0x2ee658c920bb58632482,0x827d6550d20d7d4d4348,0x482ef6254d209f995434,0x34827f6154d20d7d4d53],#[0x534827d61d4d209fd915,0x1544ca7f61540329f593,0xa8240027f61542329fd8,0xe8ae2a0a22408a1c84e0,0xb126439083c0e4348c62,0x61865d16e571505293e4,0xe1ec781da739bc6a99e6,0x4a4c9023a8ba2285a0a7,0x9aa0a6a94a227c9c2649,0xd2e8b8adcb42caafab8a,0x5348cf336cab1ec6312b,0x5e137ede36cd835ad,0xa81465230b014009106,0x400010020020400c6164,0x2c03041c410810400400,0x40540c20040c20c014,0x408f0082c020140c2041,0x1001030042c021850820,0x3047040070045c0200,0x41081001101103080001,0xc10000400400800000,0x440400055230040c100,0x81641000001001001]]
def g2103H5 := limbs80 #[#[0x1f8280094d480500c02,0xbc1a10000302c4440000,0x842067cc800000301083,0x380ec20001449714c34,0x28784003c04c500000,0x2c0a43f081c5cb0,0x1454003c98000304,0xe532460313f1d4cdb180,0x832024001c584848c041,0x3817c4f632]]
def g2103D6 := limbs80 #[#[0x3e548ca7aa919734c832,0xfea4885f54910fc90221,0xfd4520f790a41ed21482,0xea9a41ee32483da64905,0xd500cafaa3905fd4d20b,0x864885f54232beaa2657,0x14910ff19221fd32443f,0xa9221fe52443faa4887f,0x51483fa62907f48520ff,0xa6907f50d20ffa8a41fd,0xc3609012001ff53483fa,0x8c12b298218719885010,0x55dd2f3c49f10bf0e2b3,0xdbbebba6e5d8a6097a5b,0x670318b416703795dd72,0x28840214931670318b31,0xc00290710c0031071808,0x90c00318a2486001c490,0x6280073168314003906,0x290590c003948180862d,0x620a00398a4189218009,0x5001ce62b2720808310,0x31060018620c00298a41,0xa01083000831060014a,0x821243000a20c0020a01,0x310c24860014c5484418,0x1470008518473148]]
def g2103H6 := limbs80 #[#[0x13c814e00104c640085,0x51cc2400040cc0000265,0x839100a0000008209f00,0x400000000001e0780001,0x3e00000000000e07be0b,0x93a000060340001328f0,0x80006302000000000002,0xc0aa02b0001c0e,0x3af60788204000683100,0x432c00000003c19c,0x7610000,0x90700014c1d853d82300,0x199d800000012038855b,0x66000218500000001c22,0x1625b013789dc1,0x4181b8b6906a245c0970,0x25a020003d8147612c10,0x84462254114000700ad0,0x6990508ca62b405b087e,0x68f0e80000000c005608,0x2051a2bf803483e80,0x1857501c6866a2e0c0b8,0x160002400381831176c9,0x6070404f985c89e30,0x6809803582f5c230,0x8600014428b2d0000401,0x814600021a3f84850,0x8000000000010031ca08,0x5c000245348a20000c0b,0xa58052809c000082ae7,0x183b616a221c0005,0x6819765c000],#[0x4280800000000709200,0x1800800f7a744c340002,0x7ce23f59d0000b05e000,0xb65e00000000000b6,0xc0005003604440c80000,0x23e04091d0000316e701,0x6036a0d881bc89370,0x7c4a7847507e0003c0e8,0x201238200000e09,0xa42e0001416203000]]
def g2103D7 := limbs80 #[#[0xfd32fc32ff20fd20fd10,0x8405ba8c66401a00fe32,0x50ca440865432910210c,0x50ca4600a64329180219,0x65432918025d9]]
def g2103H7 := limbs80 #[#[0x30310400d0,0x1003268300000000000,0x80f000000000180e0001,0xab0c0002b394be154001,0x4a17088257084,0x90000000000122800000,0x41100008ac00000063,0x1008001a32209c8240,0x0,0x143a0000000000,0x148600d0000000000000,0xf06000000000010c000,0xa4990d800000000,0xd00f85bc5200000000,0x218f49600053380000,0x186280a0000,0x68f90000000002840000,0x0,0x0,0x0,0x19ed0eeb800050d00000,0xd2800000000000002c9a,0x4a6000000082c,0x380e0000000000e07454,0xd00059cc00089cb65800,0x40000a0890a7a4d92a83,0x190921cd2b1b,0x85c00000000000000000,0xa050002,0x3048000a71801e32b054,0xde060000002472000916,0x42a000000000083]]
def g2103D8 (j : Nat) := if j=0 then 0x405f else 0
def g2103H8 := limbs80 #[#[0xa16000a08007193d0,0x11372c800680001c9546,0x84837d0d03fa30b44ecb,0x473c1000c09488005929,0x400000a2a00308d52c0a,0x80]]
def g2103L : Nat → Packing
  | 3 => (1,5,3,0,0,0,0,g2103D3)
  | 4 => (26,4,3,0,0,8,0,g2103D4)
  | 5 => (73,3,3,0,0,10,0,g2103D5)
  | 6 => (31,2,3,0,0,10,0,g2103D6)
  | 7 => (6,1,3,0,0,8,0,g2103D7)
  | 8 => (1,0,3,0,0,0,0,g2103D8)
  | _ => emptyPacking
def g2103I : Nat → Nat → Option (Nat × Nat)
  | 4 => lookupWord 1 2 0 4 0 0 g2103H4
  | 5 => lookupWord 10 59 5 12 5 3 g2103H5
  | 6 => lookupWord 33 211 6 15 7 4 g2103H6
  | 7 => lookupWord 18 191 4 13 5 4 g2103H7
  | 8 => lookupWord 6 37 4 11 3 4 g2103H8
  | _ => fun _ => none
def g2103 : Forest := ⟨2103,8,fun i => g2103Y[i]?.getD (0,0),g2103C,g2103A,g2103L,g2103I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g2103P3_0 : block g2103 3 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g2103B3 : block g2103 3 0 1=true := g2103P3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g2103P4_0 : block g2103 4 0 26=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g2103B4 : block g2103 4 0 26=true := g2103P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g2103P5_0 : block g2103 5 0 4=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g2103P5_4 : block g2103 5 4 69=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g2103B5 : block g2103 5 0 73=true := (@block_merge g2103 5 0 4 69 g2103P5_0 g2103P5_4)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g2103P6_0 : block g2103 6 0 3=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g2103P6_3 : block g2103 6 3 14=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g2103P6_17 : block g2103 6 17 14=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g2103B6 : block g2103 6 0 31=true := (@block_merge g2103 6 0 3 28 g2103P6_0 (@block_merge g2103 6 3 14 14 g2103P6_3 g2103P6_17))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g2103P7_0 : block g2103 7 0 6=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g2103B7 : block g2103 7 0 6=true := g2103P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g2103P8_0 : block g2103 8 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g2103B8 : block g2103 8 0 1=true := g2103P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g2103T : checkedTables g2103 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g2103 0 0 0 = true)
  · exact (rfl : block g2103 1 0 0 = true)
  · exact (rfl : block g2103 2 0 0 = true)
  · exact g2103B3
  · exact g2103B4
  · exact g2103B5
  · exact g2103B6
  · exact g2103B7
  · exact g2103B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g2103G : graphValid g2103 (boundsBefore K2095) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low2103 : Lower true (varsX 2103) (graphGoal 2103) 9 := lower_forest (g:=g2103) (i:=0) (hints:=35253091828226) (before_sound K2095 V2095) g2103G g2103T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K2103 := extendKnown K2095 9 [(2103,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V2103 : Known true K2103 := extend_ok (m:=2103) V2095 low2103 (by decide +kernel)
def g2107Y : Array (Bits × Bits) := #[((seg80 [0x97356bf67bef721e8b,0xd773c41dea8dd1bd490f]),(seg80 [0x402200006000002010,0x140000107000408c0900])),((seg80 [0xfbefd95bcddbbff176,0xbdac2ba2dd7b7e0295d0]),0x0),(0x0,0x0),((seg80 [0x58281d7d3af640cdf2,0xf8ef70716f8c2552aaa7]),(seg80 [0xa781a0f188fa88508d,0xaaac61099c291282a7])),((seg80 [0xec303ef7f40b2be58c,0xe56c76cd25d492eb6631]),(seg80 [0x12c8684813b86e8700,0x81fe550c045612036611])),((seg80 [0x180736cb6936cf07a7,0xda5899d7074df1c522fa]),(seg80 [0x355190aa154270c846,0xc85089a90729925120fa])),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g2107C : List ColumnInfo := [(2,0,57,0,6)]
def g2107A : List (List Nat) := [[],[84],[67],[67,83],[83,67],[83]]
def g2107D6 (j : Nat) := if j=0 then 0x3f else 0
def g2107L : Nat → Packing
  | 6 => (1,0,1,0,0,0,0,g2107D6)
  | _ => emptyPacking
def g2107I (_ _ : Nat) : Option (Nat × Nat) := none
def g2107 : Forest := ⟨2107,6,fun i => g2107Y[i]?.getD (0,0),g2107C,g2107A,g2107L,g2107I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g2107P6_0 : block g2107 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g2107B6 : block g2107 6 0 1=true := g2107P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g2107T : checkedTables g2107 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g2107 0 0 0 = true)
  · exact (rfl : block g2107 1 0 0 = true)
  · exact (rfl : block g2107 2 0 0 = true)
  · exact (rfl : block g2107 3 0 0 = true)
  · exact (rfl : block g2107 4 0 0 = true)
  · exact (rfl : block g2107 5 0 0 = true)
  · exact g2107B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g2107G : graphValid g2107 (boundsBefore K2103) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low2107 : Lower true (varsX 2107) (graphGoal 2107) 7 := lower_forest (g:=g2107) (i:=0) (hints:=35253225783304) (before_sound K2103 V2103) g2107G g2107T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K2107 := extendKnown K2103 7 [(2107,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V2107 : Known true K2107 := extend_ok (m:=2107) V2103 low2107 (by decide +kernel)
def g2109Y : Array (Bits × Bits) := #[((seg80 [0x4bdc76ca9b94927fc3,0x76d4c56bbac518e83d35]),(seg80 [0x340308201e280c04e1,0x308440aa6810ca02931])),(0x0,0x0),((seg80 [0xfd36e7f5eaaf394fff,0x9d39d2d7a435eb1583a0]),0x0),((seg80 [0xf3f39d4b7e526cf537,0xf2823c297b4ba77b705a]),(seg80 [0x850450101100100,0x21091003015002])),((seg80 [0xfe49b9ab5399e7cfcc,0x12c43b5e898e71ea8c8f]),(seg80 [0x1a4039240c0005010,0xdcc23ac40024304a848c])),((seg80 [0x94fb72cd644c4f1697,0x3b8bdfe27108d6ac6dc8]),(seg80 [0x1a04831a98aa8cb65e,0x106ab1c63288cc2c2dc8])),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g2109C : List ColumnInfo := [(4,0,2105,0,5)]
def g2109A : List (List Nat) := [[],[64]]
def g2109D5 (j : Nat) := if j=0 then 0x3f else 0
def g2109L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,g2109D5)
  | _ => emptyPacking
def g2109I (_ _ : Nat) : Option (Nat × Nat) := none
def g2109 : Forest := ⟨2109,5,fun i => g2109Y[i]?.getD (0,0),g2109C,g2109A,g2109L,g2109I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g2109P5_0 : block g2109 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g2109B5 : block g2109 5 0 1=true := g2109P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g2109T : checkedTables g2109 5 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g2109 0 0 0 = true)
  · exact (rfl : block g2109 1 0 0 = true)
  · exact (rfl : block g2109 2 0 0 = true)
  · exact (rfl : block g2109 3 0 0 = true)
  · exact (rfl : block g2109 4 0 0 = true)
  · exact g2109B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g2109G : graphValid g2109 (boundsBefore K2107) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low2109 : Lower true (varsX 2109) (graphGoal 2109) 6 := lower_forest (g:=g2109) (i:=0) (hints:=281543830405128) (before_sound K2107 V2107) g2109G g2109T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K2109 := extendKnown K2107 6 [(2109,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V2109 : Known true K2109 := extend_ok (m:=2109) V2107 low2109 (by decide +kernel)
def g2110Y : Array (Bits × Bits) := #[(0x0,0x0),((seg80 [0x9e7789e5789e8e5fc5,0x4acaa1af7f05aac27229]),(seg80 [0x61883198b1215c020a,0x2988612b0c31b0427208])),((seg80 [0xffeb7fa0d922bfb996,0x8edd0526f282f37c82db]),(seg80 [0x20080460e040220a1,0x204e002002000c3])),((seg80 [0x470f7bff3a0dfba666,0xd3fac4f9a98b8e1745b0]),(seg80 [0x981204000042004050,0x650900000800e040530])),((seg80 [0xeef6ff9fa4f046ebe9,0xfdffbb140cff45e03944]),0x0),((seg80 [0xd7b797528f51f837d8,0x8a3e4471d5517cedee02]),(seg80 [0x244850a9f088d50100,0xb00b6c3a111150c1ea00])),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g2110C : List ColumnInfo := [(2,0,60,0,5)]
def g2110A : List (List Nat) := [[],[50],[81],[81,50]]
def g2110D5 (j : Nat) := if j=0 then 0x3f else 0
def g2110L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,g2110D5)
  | _ => emptyPacking
def g2110I (_ _ : Nat) : Option (Nat × Nat) := none
def g2110 : Forest := ⟨2110,5,fun i => g2110Y[i]?.getD (0,0),g2110C,g2110A,g2110L,g2110I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g2110P5_0 : block g2110 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g2110B5 : block g2110 5 0 1=true := g2110P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g2110T : checkedTables g2110 5 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g2110 0 0 0 = true)
  · exact (rfl : block g2110 1 0 0 = true)
  · exact (rfl : block g2110 2 0 0 = true)
  · exact (rfl : block g2110 3 0 0 = true)
  · exact (rfl : block g2110 4 0 0 = true)
  · exact g2110B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g2110G : graphValid g2110 (boundsBefore K2109) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low2110 : Lower true (varsX 2110) (graphGoal 2110) 6 := lower_forest (g:=g2110) (i:=0) (hints:=140737757317120) (before_sound K2109 V2109) g2110G g2110T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K2110 := extendKnown K2109 6 [(2110,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V2110 : Known true K2110 := extend_ok (m:=2110) V2109 low2110 (by decide +kernel)
def g63Y : Array (Bits × Bits) := #[((seg80 [0xcfe4f933fb337fe035,0x62ee755bbb106666f6f5]),(seg80 [0xc8a0a103c88a762001,0x20440450391026646034])),((seg80 [0x359f969d6dcec3ffcb,0x9d6eb2cc64ebab9d4f38]),(seg80 [0x7597808ccc80c29c81,0x242ea2c8046923084e38])),((seg80 [0xfaaf1ef804aafa6d45,0x9f59dd35c55fd5b451d2]),(seg80 [0x82081e700008086344,0xd8005925c012d4b411c2])),((seg80 [0x19906de49945b913ee,0x8bf5bea263b65b493daf]),(seg80 [0x10049a01145391226,0x8b519022638649413d8b])),((seg80 [0x945ecf477e7066d43a,0xe6b3c9eb1caeb8729a43]),(seg80 [0x325e4440207008cc0a,0x42b243ab04ae98129241])),((seg80 [0xe7e0b1c9ace79737bc,0x339f4e76d2add60b624e]),(seg80 [0x669b5023ecb283833b,0x2b890f56d2add20b4246])),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g63C : List ColumnInfo := [(0,8,2103,0,9),(2,0,61,0,9),(1,0,62,0,8),(16,0,47,0,8),(32,0,31,0,8),(0,4,2107,0,7),(0,32,2079,0,7),(4,0,59,0,7),(0,1,2110,0,6),(0,2,2109,0,6),(0,16,2095,0,6),(1,8,54,0,6),(2,4,57,0,6),(2,8,53,0,6),(2,32,29,0,6),(0,48,2063,0,5),(1,16,46,0,5),(1,32,30,0,5),(2,1,60,0,5),(4,2,2105,0,5),(4,8,51,0,5),(8,0,55,0,5),(16,1,2094,0,5),(16,8,39,0,5),(18,0,45,0,5),(20,0,43,0,5),(32,1,2078,0,5),(32,2,2077,0,5),(32,8,2071,0,5),(36,0,27,0,5),(48,0,15,0,5),(1,48,14,0,4),(4,32,2075,0,4),(8,32,23,0,4),(18,1,44,0,4),(20,8,35,0,4),(36,2,25,0,4),(36,8,19,0,4),(48,1,14,0,4),(48,8,7,0,4)]
def g63A : List (List Nat) := [[]]
def g63D5 := limbs80 #[#[0x1d1210c0946007348430,0xc184213764843065376,0xdd0734844061485dd921,0x5845061485dd92110293,0xa50835c9611419420d72,0x545204419218d7010d10,0x487541cc635452021e53,0x6006314d21614859d843,0x18d21251701c06348494,0xe51701c063484955c070,0x1c063487985c07018d21,0x50094600735952161274,0x20d6519540614859d832,0x48540648835946550092,0x608821cd655018521476,0x1cd65503916087359540,0x543541cc634855066282,0xdd0325455021f5418d21,0xc951d527318f6254198,0x251701c0635458260063,0x1cd21903985c07018d51,0x94195e1d640ca5061b84,0x591782f81f5907314d21,0xc1ec0fb34ab4a95a1793,0xa3c93c87c5cc33c2ec27,0x9e31e13d46d15d0ed07c,0xa12a011a828fd090d6a4,0x30c203a90c3d4841ea01,0x52b10a3581d48a428c55,0xcb97a155ec9280ea5307,0xc33a95ea52af6e857652,0x7a9847d0b332958992a],#[0x9a968ad28e5e94637403,0xa98c4d4ba0299c0352d8,0x535cc2980ea4b214710b,0x413cc1cbe60f5f306c89,0x914aa2929505f4882ca4,0x7cc3f0e51e8128f44954,0x229108642209002ca481,0x4e26930964a249208e46,0xaed66ab51a6d2689409e,0x81bede6eb71b6da6cb61,0x4ea34fa6d2e9347a2d0b,0x709838516f371b4d86ad,0x5045,0x80800000000000000000,0x0,0x6020000000000,0x521000000000]]
def g63D6 := limbs80 #[#[0x20d545842020f7648020,0x551711483020d7114830,0x60576148305917114830,0xdd842484301cc4248430,0x61854484301cc5248430,0x1d073484301507348430,0x59073484301d47348430,0xa1073484306007348430,0xdd87448430dd07348430,0xe01544843020d5448430,0xe1d6448430a1d6448430,0xa0e42484301ce4248430,0xdda5248430a0e5248430,0xdda5448430a1e5448430,0xddb54484301cf2148430,0x21776484302137648430,0xa1376484306177648430,0x6007354430a177648430,0x60472550306087354430,0x60672950306047259030,0xe0976d043020d54c8430,0x59171d0830e1d64d0830,0xe11615803260672d5030,0x60264584321d07058432,0x5d664980325d26498032,0x98c53484401cc5348440,0xdd07348440dd85348440,0x1ce4348440e107348440,0x216634844021e4348440,0x1d7744844061a7348440,0x61776484402177648440,0x1cc3254440a177648440],#[0xdd03254440dc83254440,0xdd05354440dd83254440,0xa0f7254440dd33254440,0x1ce63548406047354840,0x21d52cc44021e6354840,0xa0f72cc440dd562cc440,0xa1c4348450a0f75cc440,0xe147348450dd84348450,0x1cd614845010d6148450,0x20d644845090d6148450,0x60843584501ce4348450,0x61073584506087358450,0x1cd4258450dd07358450,0x21d425845020d4258450,0x20d725845010d7258450,0x94d725845090d7258450,0x60b7458450dd33258450,0x608630c9106007358452,0x18d710c910610630c910,0x6106310d106086310d10,0xe14631491018d7010d10,0x9cc63189106106318910,0xd9243189109ce4318910,0x5d07218d105c87218d10,0x6087418d105d07418d10,0x6087518d105d47518d10,0x9d17218d101d17218d10,0x21d5148110dca7218d10,0x18c325011094d5148110,0xa1c32501106043250110,0x1cf3250110d883250110,0x21c6350910d933250110],#[0x6007350910a086350910,0xcc95154110a007350910,0xe127688110e146354510,0x60863cc11020d7494910,0x613650c92060432d0110,0x5d47518d205d07418d20,0xdd57118d206047518d20,0xdd75418d206075418d20,0x20d7550520d903250120,0xd5063545201cc6354520,0x5507354520dd06354520,0x1da5354520d507354520,0xa0f54545201db5454520,0x20d7190920a0f7454520,0x20d71d51206075494d20,0x2167610d2120d7010921,0xa027610d216167610d21,0x20d7014921a167610d21,0x6006314d215d06314d21,0xa106314d216146314d21,0x5d0641812120d7015121,0x9ce43181211957418121,0x5d06418d216005418d21,0x5c07018d216006418d21,0x5d07418d219d07018d21,0x5d47518d216007418d21,0x20d5418d216007518d21,0x20d7018d2121d5418d21,0x5d17018d212117018d21,0xdd57018d21dd17018d21,0x1957418d21e117018d21,0x9d27018d211d57418d21],#[0xdd75418d215d67418d21,0x20d70909216007359521,0xd506390d216006390d21,0x20d709492120d5490d21,0x20063c852120d7095121,0xe0063c852160063c8521,0x61063d812120d70d5121,0x9ce42d81219cc63d8121,0x5d243d812118e43d8121,0xdc270d91215c070d9121,0x594650c94019673d9121,0xe11700c94020d650c940,0x9d1710c9405d1710c940,0x9da740c940d96650c940,0x616760c940216760c940,0x61f540c940a16760c940,0x18d7114940d97540c940,0x94d711494020d7114940,0x6146314d406086314d40,0x18d7214d40a086314d40,0xe1d62189406067214d40,0x5c87218d4020d6518940,0x5d47518d406047218d40,0xdc97118d406047518d40,0x5957218d40dd57118d40,0x5cb7118d406075418d40,0xe09651954020d6519540,0x61052485406103248540,0x1cc534854018c5348540,0x61053485401d85348540,0x21c6348540a085348540,0x6107348540a086348540],#[0xa1073485406187348540,0x61476485402147648540,0x18e4348540a147648540,0x1da52485401ce4348540,0xdd032541401db5448540,0x1d832545401cc3254540,0xdc83254540a183254540,0xa107354540dd83254540,0xa0f7254540a0f5254540,0x1cc32585406047354940,0xa1832585401d43258540,0xdd43258540dc83258540,0x60873585402087358540,0x1cf325854018f3258540,0xa0f6258540dd73258540,0x60873595402087359540,0x18d7190940a087359540,0x14d719494020d7190940,0xa0f62989406067294d40,0xa0c62cc540a1c52cc540,0xa1e42cc54021d52cc540,0xa1f52cc540a1e52cc540,0x60762cc540a1f54cc540,0xd5063cc94099463cc940,0x20d65cc94059465cc940,0x18f32d41409d965cc940,0x20d72d454018d52d4540,0x20d72d514020d71d5140,0x60463d8940a1c32d8540,0x20d65d8940a0863d8940,0x5c67018d42a1273d8940,0x5d6740c9506075418d42],#[0xd93420c9509db420c950,0xe1d42109509db540c950,0xa086310d506086310d50,0x5d07218d505c87218d50,0x5d07418d506047218d50,0x1d17218d50dc97118d50,0x5d27218d50d517218d50,0x5cb7118d506075418d50,0x21c63485501cc6348550,0xd5063485506106348550,0x21a4348550d507348550,0xdd032545501db5448550,0x18f32545506086354550,0x60863cc95018d7190950,0xd5063cc950a0863cc950,0xe0863d45501db54cc950,0x20d42d455018d42d4550,0xd5273d89509cc63d8950,0x608630c951600630c951,0xa10630c951a00630c951,0x18d701095161f640c951,0x18f521815160b6414d51,0x60063189519cf5218151,0x5c07018d51a0f6418951,0x9c87018d515c87018d51,0x5d07218d515c87218d51,0x5d07418d516007218d51,0x20d7018d511c97018d51,0x5c97018d512117018d51,0xd517018d519c97018d51,0x1d17218d51dc97018d51,0xdd17218d51d517218d51],#[0x9ca7018d515ca7018d51,0x6087355151dca7218d51,0x9d843d495118d70d0951,0xd9063d49519cc63d4951,0x20d6414a10a0f64d4951,0x5517114e20e11650ca20,0x20d71d52205917114e20,0x597540ca40e11710ca40,0x1d0734864090d7114a40,0xe107348640dd07348640,0x59273486401ce4348640,0x20d4258640dd33254640,0x600735864259754cca40,0x20d619824220d5458642,0xe1d640ca50e056218243,0x593320ca50591710ca50,0x59053486501cc5348650,0x20d64486505907348650,0xe1d6448650a1d6448650,0x1ce6348650e1a4348650,0x1cc72592505927348650,0xdcb7159250a0b7159250,0x59073c86501cf7259250,0xa0f745472059272cc650,0x9cd72d9330ddb5254730,0x60273d973160273d8b31,0xdd832547401cc5348740,0x20d42583511ce4348750,0x7d0ee17c1f6007358754,0x1fa3ec7b8ef1be2fc3f8,0xe93d1f97b2ee5bcaf93f,0xed57a7d4f69dd37a6b4b],#[0xadb5769eced97aeb59ea,0xc5f8af0fe1bc1f6d6d9d,0x799f2e63ec7b8ef1be33,0x9f4ee97d2ba3f3e676ce,0x8ef17e1faf35aeb3d57a,0xf36e6bccf9772de4fc7b,0x5a439e3c9f74ecdd5baa,0x417306e48c29b933086e,0x248ba9cc0f30704cba1c,0xdc07308b03cc22807307,0xed05cc3ad1b0c4322cb0,0x97c9f231f50c14780730,0x14905cc5199f2a5d6641,0xc2cc0f30b107cc2bc0f3,0x317207cc5bc8928c201c,0x499dd89267703cc5d417,0x8c67a45c8a1cbd2c8563,0x3439e5550e7c124b9e9c,0x3d0e7e7fb21f4252c7b5,0x3b4b21228e6837231a21,0xdc30863874a1961b2865,0x94b1fca72e64714218,0xa58b028262c0a05bb088,0x6c094b218832e694ac39,0x9a94b086b4ec39b5fec8,0x26689491a223246809cb,0xb99ca72e666cc2199172,0x267409cc1bd53086e7fc,0xc21d425307420ca9d0a5,0xf30702aca1d92f0a754f,0x94b80625060008cbe253,0x2b3097094b2453d0e900],#[0x16cc24d290e9379aa249,0x52d0c964b43254233094,0x9094b2688526984a3b26,0x34592c9c1d4b26c272e8,0x8a4ac3a3c272e8e094c2,0xe28252c9d4abaa313f30,0xd8d084c6312f0d8b08cb,0x301a43201c08cb6bc232,0xec1752c305827300752c,0xcc0654eec1852c30214e,0x32c0c28cb040a32c0b09,0xfca03a39280e60c2038a,0xa32c0a89cb03a312a0e8,0x28cc035fd080d7ec2034,0x4a32c0f314a83ca7300d,0x26cb204966ec13084b82,0x6c23301b0f4b8494eec1,0x1d08cc074232c1a09cc0,0x44a52615094b8502730,0x6212cc88853b081e24ca,0xa884832a214fc2084a52,0x222228498812b0a1f214,0x498a5b2c8284bc2888b3,0x92823614108d83042329,0x1c88aca72c2489cb08e3,0x4ac80224c88a93f302b8,0x84c0112f0c0376b200d,0x272c2709cb094af2405,0x14b43ec069262609cb0b,0xdcf32c3785496c61325b,0x3253438cc632c387ecb0,0xd023303428cb0c94b0c],#[0xc3535498d4a52e3909cc,0x98e8932c364ec30d93b0,0x223d4ac28f0932c3b534,0xc28f8b3223e28498f4b7,0xb284a4349928232c494b,0x4c31006b2c4c1acb12cf,0x3b0c4128cb0fd4b0c3f5,0x8cb114d5264409cc109,0x4272c4628c8920a32247,0x74e3b3d9fae9334f4342,0x18a52f0509cc41d38ecf,0xf85343be150ecfc294b4,0x3e54d0cf95cc23e4a52e,0xfa08cc3e938ecfb294b,0xbbf4252cfd543b3f8273,0x2900254b40538ecff094,0x49c0d2b0b0208cc42097,0x52d26094b4a52f0b0428,0x94b4ac252d2a094b4a02,0x252d2c573b4b54ced270,0x9cc42d4d0d0a5543434,0x528ed10094bc3023310e,0x56841cd0952d0f094b44,0x514d0d135543458252d3,0x1a094bc552d0d174b434,0xc752d0d1c534346de0eb,0xd3837c8c657b05184a3a,0x3365390cd84f3b35c252,0xcdb094b37d2b0ee04e4,0xcc354872ed53849b553d,0xb0adc4ac3b694cecd617,0xbc2b789728dd2849b752],#[0xe127301acc4bc6b312e4,0x94c4c94ced3117cc4c0,0x5290ce3094b488253121,0x3084b448252ce2094c38,0xa95526e95449ba5e0c72,0x3a09cbce5530f2570c93,0x4edc3253b254b4f0732f,0xae4084b3a14d30e77149,0x8b94a32ee652c3b91a30,0x30eb55433ac212d2439c,0x4c3c02530ef25ca3c447,0x730eb54b93b02730f309,0x94b4d92aeaee09cbbc95,0xa124f41749bd4252d370,0x69c93d1a524f468c93d1,0xd490d1f37c8c7d7b051e,0x784ac7e1f231f2dc8c7,0x48d527917ecb650a3312,0x9609cc6553b0d933549e,0xe3d3aed8e094be5cd527,0x9b45c41e40e127984ac3,0xb9402331b552c36d1730,0x304e7bca94618e6522d4,0xc313ca32c5408cb13427,0x52e5a094b94c832c4f4a,0x643965c9065945499802,0x7d2e5a1f4c1647930595,0x1f4c171c9065c1f4996c,0x5c9285d6bca975c9065e,0x573ca175cd285d72ca17,0x5d1526583bca958792e5,0x50094bd547926613bca9],#[0xd4d290f5352c2541e6a9,0x154094bd44212f524b43,0xa5642b31572149d582b3,0xc9616841d80ef235879b,0xc3d04e5275f174b58596,0xf31424b435082731404e,0x3aa56ce52d5d4b434fc2,0x2d0d5e38c8d75c3095c9,0x79aa58825315a4f4b50d,0x5b309440acc58c852d63,0xa0b4c530852d4c28cbd1,0x1952e54809cc53c25314,0x4b174c53027314755cc5,0xe99a1274e2bc95342531,0xfa14b43e85e2c9a0094b,0xc6a02731a2783ae9c812,0x27a5094be90252fa309c,0x4c6782731ae09cc6b4a5,0xd2b9d4acae74a72f9f08,0xac96a46d27aa55416ad2,0x4d0cab7eb26d8ad25ac2,0x7eba3402530aa4fcc2a5,0xc272ecd28ca3393d0cd1,0x94549b25d300c908cc33,0x290728ca3acab250328c,0xc3094b2791526cb3bcab,0xa84252cc7094b28c252c,0xaa22849a812b0a9f2cc8,0xab10f728c46cc23112f0,0x28a51b4b3186b30c5384,0xcba95a30aa53dca294f1,0x30aa729cc290a330a429],#[0x9432bce728a628cba9da,0x252cb66832ad45730af5,0x4f432c53f30ad4eba2b8,0xe0928af094c2f43730b1,0x59cc2bdf12aaf83ca2b,0xc0852ab04ac2ac13b08b,0xb96dc22ddb108b708cc2,0xae02530ba4a42ae9290a,0xab84ebaae1970ab86442,0x9af1970abc6442af13ee,0x8bf2ec82fc2530bb6c4,0xc3b04272eac214aafd3b,0x530be4fcc2c53ae8b24a,0x1ca2cd2aeab425ca3002,0x252ccc094b320252ca82,0x8cc350bd2cd315cc348,0x9e12ac27e4a3089128c2,0x3344a6ccd729b2344a6c,0xad2b0f6b6941dacd729b,0x6470c15912d0d6c17cc5,0x598a72f643dca590f129,0xf677142595c3096570c1,0xc6102531694bcada0a32,0xf8779b26192d0d85094,0xcbdb54ce76d4b3b6212f,0x9296f21cbda8232f6e09,0xec25c14d077059cc5be0,0x3b097109cc5c13d09704,0x94c5d93f097608cc5c5,0x13f097a4fc25e5390979,0x7094c5f13f097c4e425f,0x1970b78174c5edb1097],#[0x7354b95d0bb21812fc86,0xdfc25317d174c5f82731,0xfb733c8e0cab21822949,0xa0c53f3030094b8b4252,0x202e084b8bc27303125c,0xc84f52b0a2e4ec20b8bb,0x7299908cbe6c272f3e2f,0xeba670972862094be689,0x9003100d00009729b84,0x4c02401100710348174,0x81e20db069831c1680a0,0xa0ad851827c13208c03f,0xc3401980c806082e416,0x60ff07d83dc1e00ec07,0x944476233115886c41c2,0x28914089e44d226112c8,0x8b2c5862b51558a84522,0xa30d1798bac5c62db169,0x20d6469a34519b8c8c62,0x7c3b61d70e987303781b,0xfd8fcc7d63e31ea0f307,0x88643b218108482440a1,0x23e11d08d246122c912c,0xc97e4b2255127092848c,0xe27b13b89cc4da269131,0x34a8a5312949454a1a4f,0x842be15d0aca55d2aa95,0x700b665ab2ce1650b185,0x6062ff17c8bc65d02e41,0x991cc76633315988cc34,0x268133c99c4cd265d32a,0xd1ac4d526a134c9a44d1],#[0x127013759b78d946c235,0xaa9d2ce8673b3949c64e,0xf4c79e3cb1e1cefe76b3,0x3ed1f48f947be3db1eb8,0x503c8114009fe4fe27e9,0x342da14108a83d41aa0b,0xc114889044221f10e886,0xf9476237d1ae8c745c22,0x51d27e937494246120e8,0x9954c2a5f52e09624a9a,0xa7253829b94d8a69533a,0xa0a4ff27c53d29d94e8,0x42901470a30514288143,0xa78538299d4bea5052,0x582aa1540a985482a215,0x5c8adc56a2b21580ab85,0x58dac4d616afc57a2bb1,0xd6beb575a4ad05672b2a,0x25cbae3d70eb7f5bbad9,0xc97d4bd15e4aef9754ba,0x38618309d83ec146062f,0x1a18c0c586283121880c,0xc986483221900c786383,0x33619a0cbf65bb2bd940,0x2d19684b4059e0ce8670,0xb35a5ac2d536a234c5a4,0x5eda26cb3639b0cd7e6b,0xf53789bb4dd26e2b6f5b,0xc8ae38714b885c32e006,0x758baa5d16e7b7333979,0x5dc2ed9768bb25d82eb9,0x17933c79e2cf0677ebba],#[0xcded6f5f7abbd25e72f3,0xbc7d53e75f22f897c0bd,0xae0330047fe3fd1fa4f,0x8a83dc19e0ab04781cc,0x43ea1cb0d1861c2d2125,0x512a891446a22510a881,0x4c56a2a514a8a144ea26,0x4b19d8cac6362f31718b,0xf5c78e3b71d38e5c6d23,0x447213905c80e3f71f38,0x931c95e49f24791cc8c6,0xa5552a294d4a4a515279,0x69734b5a5952c295d4ac,0xa66433169874c1a5fd2f,0x5c9aa4d32689339998cc,0xe3e70937c9ba4db26c93,0x3c69df4eda74f39f9cbc,0x50127dd3e69ef4f5a79d,0x1438a185092839414a06,0x51e28e1463a2b512288,0x8d4b8a5852a293548da4,0x8754069f34eaa6e53529,0xaa1545a9b54baa4d516a,0xacfd62aaeb568ab05562,0xabef5efaed574ab955bc,0xab2158eac65618b08580,0x1acfd676b37599acb564,0xccb5f5ad6d556a2b4a5a,0xbf2de96ecb725b72da96,0x74eba0dcd2e4d710b845,0xde7ef2f780bbc5da2eb7,0xd7e8bf05f62f9f7c2bda],#[0x960ab04581ac09601eff,0xe986cc30616308583ac1,0x69631b16789bc4761f30,0x25f91cc7f63db1cd8dac,0xcafe55f29f947c9fe4df,0x7323989cc0e5df2df967,0x9ce0e6e73639a9cd0e66,0x234019f8cf8678b3a59c,0x38d1868a3441a18d0868,0x800ba000302a01b481a,0x11802e05043818008000,0xc600c5010f06228c7b83,0x20c38800680481303e06,0x8210ac124654038403ca,0xa0c03805107d8005ba0a,0xcb1181099e04e090ca13,0xd41945c88060e024004,0x6150560a218209c1081c,0xf0582741307024b80b0a,0x721180a238c6502f00e1,0x4a004981ec805000394,0x20d4248728d02008e803,0x847943410839c1823489,0x81928412e4102540f60,0xc350d218242040390474,0xf7e921e71d6c750ac0c,0xbf490c0140a1e505bf49,0x502f71050c904000001,0x706c929c18d045e2820,0x807381c7941002813b8,0x20ec03e6ca00015b09dd,0x810000000076c201941a],#[0x18f8200005ba15,0x501405ee84000001ce84,0xf9283000000000000860,0x40803b6176582cd8401d,0x34060f7801086f904c05,0x9b42014c0800000,0x60346868d0800b810,0x1374200c0400021810,0x6a08030100ab08043020,0x880013d88009c0800000,0x18e040000000013d,0x40000b4100470200000,0xc3c4100190a381969,0xc8402922b2100000,0x400000000000000,0xce84000a3a2da0c3c410,0x7ca09010000cc18aee86,0x13220077282e,0x8000002dc0800059080,0x2c04000001701f5846d,0x29e0c5a8200003942006,0x2c3d6100cba10e4401a8,0x5702368538429606,0x34e8402ac21b0d9a1941,0x6e840000000003504000,0x1611590f58403,0x1007206000000,0x1a820000000000000000,0xda100001702000000000,0xe3a100002d840002ed0d,0x80a7b310052100000000,0x2001b7b3180167bd8c01],#[0x100a4,0x870200000000000000,0x27484000000013a4200,0x1cb429c18bce8403ae84,0xea0800000006d040036,0xed1000000558401361ab,0xc682788800033686c774,0x6481c117841005bb0a0,0x33cb0,0x180800042e08053d988,0x236100941008d862704,0x2bdcd4509b16584c8400,0x3d099d50400001ed0843,0x382d3d0a361a605b61d,0x157021ed08432800381e,0x33aa0838d89b6,0x1c080000000000000000,0x4ce040000030bd880002,0x38d4,0xc6040258195c1000,0x4f90b0daa2d41,0xe214ee0ca0800000000,0xc040000018080000000,0x602000000000000000,0xe040000,0x64200000001c6b5100,0x8200013419a0eb020000,0x16c0db020001ac0cd066,0x52e0806d0403ad0db020,0x9682000000c079c08000,0xc06047ea83d70410bc60,0x5b0b0100d62c100001],#[0x59081d080000012d8b06,0x580806b031b080000000,0x282000000000001ac080,0xa0cd066835b0bdf14401,0xa20001cf44016b823411,0x93440000011a08d06cf2,0x100000000000030100f9,0xb0afc84000128201e735,0x99080190c72624c7263c,0xa73055a625b20066e0,0x1010000000000000000,0x8040000000000000000,0x701e8e]]
def g63H6 := limbs80 #[#[0x126a80,0x300000000000000000,0x35a0000000000,0xc8000000000000000000,0x1678004980000051,0x654005b800000f6000,0x308000000000000,0x0,0x0,0xb26ae00484ac800,0xb580000000005a4,0x0,0x1b300000000,0x1a20000000000000,0x3100000000,0x64a000000000000000,0x4f80000000cf00000000,0x61c00001c8801,0x2528480000515ac498,0x6360000133f8c00000,0x0,0x5ba000000000123ab4,0x8000000000001b18a8,0x1,0x0,0x4b00600000a40015742a,0x10b,0x0,0x1c00000000000,0x0,0xc5800]]
def g63D7 := limbs80 #[#[0x48020551200815414c20,0x80735042098d2108376,0x98d5108073544205d941,0x584201cd540837254420,0x8074584201cd6108043,0xdd161082545842055161,0x10830508420c154d4420,0xc152148305d8420c165,0x5c4520c1641483055052,0x48430109210c17614830,0xc07348430151210c052,0x551210c075484301d121,0x48430909210c16448430,0xc32148430951210c252,0xdd5210c37448430d5121,0x504301c9410c37648430,0xc37250430d09410c073,0x1cd510c07254430dc542,0x55030d49510c16154430,0xc371550301cd540c072,0x951610c07458430dc954,0x58830951620c34258430,0xc371590301c9640c354,0x9ce420c17190830dc964,0x948309ce520c34290830,0xc172950305c6540c352,0x593210c154c84309ca54,0xd0430593410c142d0430,0xc272d04305db410c172,0x5c7420c165d083059342,0xd4430553510c176d0830,0xc164d48309cb510c172],#[0x5c7540c176d48305c752,0x150329cb540c172d5030,0xc976550325c0540c965,0x585600c95458032dc154,0x58032595600c96458032,0xc874584321c1610cb75,0x991610ca545843255161,0x59032dd1610cb7058432,0xc96198032552600ca65,0x992600c975980325d260,0x994325c2640ca6598032,0x10170d4832553320c970,0x5c45310171148405c432,0x4844014d211017214c40,0x10161484401d52110073,0x98921102534844090d21,0x484409cd211026348440,0x1037648440dd52110374,0x1cd5110053544400c951,0x54440589511016154440,0x103325444098d5110262,0xdd1511037254440d4951,0x5484098d521007354840,0x10073584401c96110371,0x9496110175584405c961,0x948401cd651005358840,0x1007298c405c66210171,0x54b311037198c401d663,0xcc4405cb3110162cc440,0x10375cc440dcb3110332,0x5c75210172d444054b51,0x584421cd6010b7650842],#[0x1437098c425c66210b70,0x58521140734845010d21,0x4845090d211416448450,0x140735045098d2114253,0xdd541141765045058541,0x5845010d611407350850,0x14074584501cd6114072,0x5d161141725845050961,0x58450cc9611424258450,0x1437458450dc96114342,0x1cd6014b76548525c662,0x584521c1611484358452,0x14a43584525516114873,0xdd16114b705845294d61,0x98c52dc26314b7590c52,0x14d54584531c16114f71,0xdc96015073580545c662,0xc91018c324417198854,0x441760c9105c43244170,0x9cc42441761091018c42,0x10d1018c434436210910,0x44063149105c44344170,0x94c5244176149105c452,0x14d10d88524427314910,0x4417114d105c05344063,0xd945444176151105d853,0x18910588624406318910,0x442731891090c6244174,0x194634406418d1015063,0x18d101d0634407218d10,0x4416518d105906344075,0x5d4634417418d105c863],#[0x18d10990634425418d10,0x4427418d109c86344265,0xd90634435418d109d463,0x18d10dd0634437218d10,0x44165195105906444375,0x50520440634811018920,0x50110dc5204415148110,0x44063501101894044032,0xd894044332501101cd40,0x50910509414406350510,0x44076509101cd4244063,0x54550440635411018950,0x54510d89504433254110,0x440655451018d5144053,0xd4951443325451094d51,0x5891018d624435454510,0x442535891090d6244073,0x1cd644407259110dc162,0x59110dc9644436459110,0x44043881101cd6544373,0x95220442438811019220,0x9091018e424427688110,0x4406490d109ce4244176,0x18e524427290d105ca43,0x94d105da524417494910,0x4417695110d525344174,0x9ce64443629891018e62,0xc811018f204427399510,0x44062cc91018f3044362,0x5973244164cc91019332,0xcc9109533244174cc910,0x44063d01100cb4044364],#[0xd8b4044332d01105db40,0xd091018f4244062d0910,0x44063d41105db4244171,0x5db5244171d491018f52,0xd51105c75444165d5110,0x44063d89109cf5444176,0x90f6244174d891019362,0xd95109536244253d8910,0x483650c9205503248174,0x5c453480631492018c42,0x18d20190634805418d20,0x4807518d201d06348065,0x5d4634817418d205c463,0x18d209d0634825418d20,0x4836418d20d506348275,0xdd4634837418d20dc463,0x5012018d404803250120,0x480765052018d4148073,0x18d5048032541205d541,0x5452018d514805354520,0x48154545201d95148073,0xdd151483545452094d51,0x909205c6424806390920,0x4817190d209da4248273,0x18e5248053949205d643,0x9492094e524815494920,0x4817494d20d525248276,0x18f204827395120d5253,0xcc5205d33148154cc520,0x48063d0120dd73148374,0x18f5048272d052018f41,0xd51205c75448063d4520],#[0x48171d912094f6148273,0x18c42487640c9215d365,0x10d21194434857010921,0x4867610d215c04348565,0x5c0524846314921d9443,0x14d21550534846314d21,0x4876414d219c85348570,0x18c6048443181215c054,0x18121194604846418121,0x48643181215d06048554,0x9cc60486541812194c60,0x18d21190634845418d21,0x4847418d211c06348465,0x5c0634855418d211d463,0x18d215d4634857418d21,0x4867418d219c06348654,0xd90634875418d219d463,0x18d21dd0634877018d21,0x48676191215c06448775,0x1955448574195215c065,0x551211d9544847355121,0x4847359121dc15448764,0x18e4248774595211cd65,0x90d2118e434857090921,0x4847590d211c24348465,0x5c2434855490d211da43,0x90d21d92434875490d21,0x4846394921dc24348765,0x5c2534846594d215c252,0x94d219da534857494d21,0x4857095121d925348754,0x952634855498d219da54],#[0xd51215532148463c8521,0x48432d81219cf5448570,0x90b6048554d812118f60,0xd812194b6048643d8121,0x48764d81219cf6048653,0x1cf6448470d912119764,0xd91219c36448570d9121,0x50174d9521dc36448673,0x54832500760c94019432,0xc94058832501540c940,0x501710c9405c03250165,0x5d832501750c9405d032,0xc9409d032502650c940,0x503320c9409d83250275,0xd8832503540c940d4832,0x1494018c52503650c940,0x50176149405c45250152,0x5c4535006314d4094c52,0x189409c8535017214d40,0x50165189405886250063,0x9d86250263189405c462,0x18d401d4635007218d40,0x5017218d405c46350165,0x9c8635026518d405d463,0x18d40d50635027518d40,0x5037518d40dc86350371,0x14921500324854059465,0x4854018d215005348540,0x50075485401cd2150065,0x9092150154485401d921,0x48540949215024348540,0x50276485409cd2150253],#[0xdd1215036548540d5121,0x50540dd9215037548540,0x5037050540cc94150032,0x1895050032541401cd42,0x541401c9505006354140,0x5037254140d895050332,0x18d5150053545400c951,0x545401cd515007254540,0x5037254540d495150332,0x1cd525006354940dd951,0x585400c9615037154940,0x50073585401c96150063,0xdc9615036258540cc961,0x90940dc9655007359540,0x5006390d405c64250063,0x9ca435017290d405c643,0x9494018e525005394940,0x50352949405da5250171,0x18e625027294d405ca53,0x995405ca655036298940,0x50063c854014f2150273,0x9db2150073c854019721,0xcc54014b3150365c8540,0x50072cc5401973150062,0x54b3150076cc5401d731,0xcc54090b3150172cc540,0x50332cc5409cb3150252,0xd8b3150354cc540d4b31,0xcc540dcb3150365cc540,0x50065cc94018f3250375,0x9db3250265cc94059732,0xd4140d973250354cc940],#[0x50332d414018f5050032,0x18f5150032d4540d8b50,0xd45405cb5150152d4540,0x50063d4940ccb5150272,0x9cf5250176d49405c752,0xd51405cb5450171d5140,0x50032d85409cf5450272,0xccb6150142d854018f61,0xd894014f6250362d8540,0x50171d89405976250063,0xd536250273d894099762,0x14d415d8525046314941,0x50732181415806050565,0x5c863505701894158862,0x19541d50635066518d41,0x50774595411cd6550565,0x5da52504639494118e42,0xd4941597325046398941,0x50554d89415db5250463,0x5c0635097114d425c362,0x18d425d4635097118d42,0x5087359542d506350a70,0x1d832540640c9505c754,0xc9505c032541420c950,0x541760c9505d03254171,0xcc832542760c9509d032,0xc950d5032543420c950,0x541421095018c4254364,0x9c8435417210d5018c43,0x189505c4625406318950,0x5407418d501c86354273,0x5d0635417218d505c463],#[0x18d509d0635427218d50,0x5437218d50dc46354354,0x1cd215406348550dd063,0x4855090d215407648550,0x5435448550c852154273,0xcc9415437448550d9121,0x509501cd425406350950,0x54063545500c95154371,0x5c6425406390950cc951,0x90d505c6435434290950,0x54063c85509ca4354172,0x9cf2154243c85501cf21,0xcc55050b3154331c8550,0x54332cc5509cb3154172,0x5c73254064cc95018f32,0xd0550d933254354cc950,0x54172d055050b4154063,0x18f4254332d05509cb41,0xd45500cb5154273d0950,0x54242d455050b5154063,0x5c75454332d455090f51,0xd895010f6254142d8550,0x54273d89505d36254063,0x18c3254571d9150d5362,0xc9515c032545540c951,0x545701095118c4254764,0x9d8435457010d5194c42,0x1815114c605476414d51,0x547321815118c6054462,0x10c625476218151d4860,0x189515c0625446318951,0x5447018d51d906254673],#[0x5c0635447418d511c863,0x18d519c0635457218d51,0x5475418d519d06354672,0xdc8635477018d51d9063,0x549511cd425446350951,0x5447355151dd15254462,0x18e43547629095118e42,0xcc9515533254462cc951,0x54764cc951d533254570,0x5c34254463d095114f42,0xd49519db4254653d0951,0x54570d495118f5254443,0xd935254673d49515d352,0xd815118b6054432d8151,0x54752d8151ccb6054463,0x5c36254463d895110f62,0xd9151d936254574d8951,0x54a73d91519cb6454572,0x10f6154a7418d525c063,0x189545c06255171d9152,0x5517218d545c46355171,0x5903284170d89549c863,0x14a1098c528416414a10,0x8407350a105905384273,0x1cd64840725921055162,0xcca10593328437259210,0x84164d4a105db4284254,0x59432881540ca209cf52,0x10e2098c42881760ca20,0x8826314a205d84388165,0x594538816414e2055053,0x506205d8548817114e20],#[0x88176506205854188073,0x1cd51880725462014d51,0x5522098d518816154620,0x88254586205516188073,0x1cd6588371592201cd64,0x90e2098e428837459620,0x8815498e2098e5288171,0x593318835498e2095263,0xd06205db4188254cc620,0x88263d46205935188263,0x5c75488165d52209cf51,0xca405943290273d5220,0x902750ca405d43290171,0x54852903540ca40d4832,0x14a405d8529017114a40,0x9027214e405c45390243,0x14d2190043486400c921,0x486401d1219007348640,0x902524864090d2190164,0xdd12190354486409cd21,0x50640dd9219037548640,0x90032546401cd4290370,0x1cd51900535464010d51,0x54640cc9519016154640,0x9037454640dc95190352,0x1cd619037154a401cd52,0x592401cd629014258640,0x9017190a401cd6590073,0x10e529027290e405ca43,0x94a405c6529005394a40,0x90052cc6409ca5390174,0x54b3190075cc6401cb31],#[0xcc64090b3190172cc640,0x90352cc640ccb3190252,0xdd73190372cc640d5331,0xcca405973290164cca40,0x90172d464054b5190354,0x90f5290176d4a405c752,0xd52405c75490165d5240,0x9095414e429cb5490172,0x1cd5490b6514e425c053,0x586421c1619096158242,0x90a63586425516190873,0x98e609096198242dc161,0x18243dc6639087098e42,0x90d62182435846090d60,0x5886290e62182435c460,0x98a435c86590d6519643,0x90d62d82435876090d71,0x58b6190e62d82435c760,0xca505c432941640ca50,0x943320ca509d03294174,0x5d8429414210a50d0832,0x4865010d219425310a50,0x94074486501cd2194053,0x90d2194164486501d521,0x486509cd219426348650,0x9437648650dd12194321,0xdc94194332506505d941,0x58a50509619437150a50,0x94073592501c96494073,0x14e429437259250dc564,0xc86505c6629417190a50,0x94073c865014f2194043],#[0x9cf2194243c865059321,0xcc6505933194331c8650,0x94332cc6509cb3194172,0x5973294164cca50d0b31,0xd06505db4194171cca50,0x94a53d0a505db4294332,0x10d6194853582525c043,0x98252d51619485358652,0x9497098e521c26394a63,0x9cb5494d71d5253dc663,0x98e545c6629517098a54,0xc82634872059454c8070,0x1cd50c8263503201cd40,0x547201cd51c826354320,0xc82635472094d51c8154,0x5d331c837458720dd151,0x5532155063c8765d5320,0xc847358321dc154c8473,0x50842cc154cc72155263,0x487305c452cc15214b30,0xcc164487301d521cc052,0x94921cc243487305d521,0x48730d9121cc35448730,0xcc37648730dd521cc374,0x1c951cc073543301cd40,0x54730d4951cc15254730,0xcc25458b30dd152cc372,0x5ca43cc17190b30d5162,0xd53305c652cc27290f30,0xcc170d93309cb54cc171,0x55052cc673d93305cb64,0x553319cc52cc56414b31],#[0xcc6525833190960cc465,0x55262cc65458b3155162,0xd0b3195332cc554ccb31,0xcc673d833159352cc765,0x5c042cca73d97319cf62,0x153325c054cc97014b32,0xcc9709933255161cc971,0x5c452d01710cb405c754,0x4874014d21d017114f40,0xd0263487401d521d0073,0xcc950d003254340dd921,0x547400c951d037254340,0xd037254740cc951d0053,0x5c662d007354b40dd951,0xcc740dcb31d0152cc740,0xd0473583410c960d0775,0xdc960d07325834194960,0x98f411c263d057098b41,0xd0873583425c453d0b70,0xdc263d087098f421c165,0x4875090d21d407348750,0xd4332547501cd51d4263,0x5c662d437458750cc961,0x583511cd52d447350b51,0xd4542583511cd60d4432,0x5c262d47325835190960,0x98f521c263d487358352,0xd507058754dc263d4970,0x5c262d5370587541cd61,0x98f541c263d517198b54,0x97e3f8fa3b8de2f87f71,0xa5e8f9fe7e9f2779da6f],#[0xaceafab6aba9e9fa769b,0xb5ecfafebeaf6bbadeb5,0xbeef7bdaefb7edeb76dc,0xc9f1fc771bc5f0fbfafd,0xcef37cdb35ccf2fcb72b,0xd7f5dd6f57d3f3fcfb3d,0xdfb7ddef77ddb75dbf67,0xebfade9f9fe779be5f8f,0xf73d7efbbdeefb9edfb3,0x510e43ff6fcfeef9fdd,0xa10c4641106554510e44,0xc6368fb004a0fb00488,0x63780f0837198c636da,0x839811063995cea56011,0x3c499083c4b1063c40f0,0x8da0c63881f0e3c4790a,0x598c63b1a0c63ad98c63,0x11063b8030e3bc0f083b,0x106580790458186c8584,0xa42c910642c990442c7,0x84bd7ec84b80f0e42c69,0x4b990e64b948ea4c176c,0xc55eea4b958ea4b996e6,0x558ea4c596e64c590e64,0x56ea4bd50ea4bd5eea4c,0x90443156ea4c950ea4c9,0xe430690843071064307,0x707507200070f1cc07,0xc172c80a843000a8430,0x3443000fc43000bd98e6,0xc43000cc43001054aea1,0x86e81f1a4e729172c80c],#[0xd0624ca30825d86e8221,0x6ad8850a24c830a24cb,0xe91471069141f0e8cc11,0x2d566ea2bd86e8fa0070,0x8830a300030c2dd66ea,0x8a3082e8bd062e8830a3,0x82e82f0b9062f8a5082e,0xf0eb34270eb2c0f0873d,0xe8d8958e6d88070eb481,0xf058070e1680f08d5d5e,0x1b0030c3408303374030,0x9c270f0880f093c80f09,0x15acb0a41f0f09d5aeb0,0xb0e6435b8c6444070f0a,0xb0e4d2b4a6441a8e6439,0xe525b4e65290b0a4d45,0x8455a8e64502d0e44c2b,0x475e8e647c29065558ec,0x9e68c8461a8e64782d0e,0x105064a1050c49505064,0xab0e3667b04365050649,0x90c5408f0a538c106539,0xe6380af0853cc10653c2,0x837c2f0e3742b0e375b4,0x46da8e646829063798ec,0xe42b0e4e5ace64e42d0c,0x829064e98ec84ec2f0e4,0xab08565ace6565b8c656,0xb0e5656cea5656aea564,0xa6394290656c2f0e5642,0xc39db4e63a64ca63a5ec,0x3a02f0e3902b0e3916ce],#[0xfdace64fc29063996eca,0x829065042f0e4fc2b0e4,0x2b0e575ace6575b8c657,0x9063c4290657c2f0e574,0xe84a588e84a5ace63c0c,0x64b56eea4a568ea4a58e,0x4a9a8e64b1a8e64ac2d0,0xa9ab0a4a9af084a9ab08,0x42b0e515b4e6519af0a4,0x630838429065988b0a59,0xb0e3aa430a3a9ab0e386,0xc5088d0c50d030250da,0xa3d98ae83d8c5063d829,0x3ecc9043ec8d0a3d88b0,0x48f0a3ec890a3eccf04,0xc9043f0c5063dc2b0e4,0xaf083f0a9083f0cf043f,0xb083e1b2e43e02b0e408,0xa3e08b0a3e0ad083e0a,0xa3f4890a3f4d7023f48d,0x400c506401b6e440c8f0,0x18c5064182d0e4002b0e,0x4cb043e42d0e4182b0e4,0x8b0a3e58ae83e4cd043e,0xb043e98ee84108d0a3e4,0x83e8ab083e8cd043e8c,0x63b96eea4156aea3e8ad,0x5818ec858c2906510290,0xbca90642c29065888906,0xdb0e64c5b0e64b98ec84,0xab044bd6eea4bd68ea4b,0x9064318ec851daf044bd],#[0xca521af044cdab044cc8,0x6e642f0ee3c29065a96e,0xe41ace6e442906e6cc10,0x42f0ee4c2f0ee702f0e,0x9c506009c106009c6ec0,0xc30a009c708009c30800,0xb0c011a8e600dc70a009,0xe01db4c602029060142,0xe02a3ac80402b0c01829,0x3c8b0a0302d0e0382d0,0x256aec0023ac80002d06,0x8290e605ace667c2b0c0,0x290c684290e61d8ec860,0x90c6142d0c68c2d0c688,0xe6695b0c66982d066102,0xe6942b0e694ab08695ac,0x62568ec63568ec6202f0,0x282d0e624290e625a8e6,0xd68ec63968ec6302d0c6,0xace66a02d0662c2d0c63,0xf0e641ace6641ace65b5,0xec659ace65b82d0664c2,0xe65dace665d6cec6656c,0x6696cec66d6cec6602f0,0xbc290c654290c6502d06,0x4290c6708d0c674290c5,0xc5065c98ae85c4c5065c,0xd0e5e02b0e5e16aea5c8,0x45cc2d0e5ec2b0e5ec2,0xa5e58ee85e58ae85cccd,0x5d0cd045d08d0a5e48b0,0xa58ec86796eea5e96aea],#[0x429066b16eca6a8290c6,0x2b0cea9b8e6eac29066b,0xf0ef09ace6f082906eb0,0xa6eb9b8e6ec02906f042,0xceb56eeceb5b4c6eb9e0,0xebc290eec5a8e6ec48b0,0x91ace6ee5ace6e842b0c,0x82f0ee89ace6eedace6e,0x6aece942f0cea02f0cee,0x506ef48f08e9c2f0ee99,0x6ea42d0eef82d0eef4c,0xaf202f0cf1c2b0cec829,0xee02d06ed88906f196ac,0xd4290f1d9a8e71d82d06,0x1a8e71e02b0d1d58ac91,0xa8e71d02b0d1dc290f1e,0xeed1ec2f0d1fc290f1d1,0xf1f1a8e71f08b0d1ed6,0xd1f48f0d1e82b0d1e429,0x7208e60902d071f82b0,0x81aac807213000712300,0x2b0c0a4ab0c0ac290e0,0x8ac81298aec1218ac80b,0xf0e1242b0c1304d06131,0xc0b88b0c0c56eec0c58,0xc14c4d0614e13000bc2b,0xe08b0a0e23ac81442b0,0x448b0a0d82d0e0dc2d0e,0x42f0e0483f0e0458aec0,0x8aec1002f0c0f98ac80b,0xf0e1398f0e1358ac813d,0xec0502f0c05c490605c2],#[0xc0563ac8054370e0516a,0x1516aec1082f0e0596ae,0xe82d0e0e4cd040e42f0e,0x98ac80d02d0e0e8cd040,0x2b0c0d58ac80d42b0c0c,0xb0c1158ac81118ac810c,0xc1656aca1602f0c15c2,0x526049072342d0f2442b,0x2203f0f21c4d0725de0e,0x70c507270cd05270370f,0x42d0f274cd052742d0f2,0xb0e61fdb8e61f1ace729,0xce6201a8e6201f8e61f5,0xe201a90e200290e201a,0xc1e96cca1e96aca1e9af,0x2082b0c2056aca2042b0,0x8a42ca2882d062103d06,0x16aca285acc6284c30c2,0x6eec23644c6235b8e622,0xe622648a62248b0c235,0xc6219acc6239b0e6229b,0xc2196eec219d6e821a44,0x22c290e22da8e622c8b0,0x3c2b0c21da90e22e410a,0x5acc629a44c62943d062,0xd106258d304250d10625,0xf0c1d56aca1d5acc61d4,0xc62482f0c1d9acc61d82,0xc241a90e245a8e6245ac,0x261acc629dacc62682b0,0xdcc90626c290626ccb02,0x1acc61e02f0c1ddacc61],#[0xc304279aee42796aca1e,0x304274c302274c302270,0xe898c2d0e97c8b04264c,0x8981a8e69802d0c9858e,0x925a8e69258ae8aad8ee,0x4c2d0c92c2d0e924290e,0x42d0c9502d069342d0c9,0x2d0ca39ace6a302d0696,0xd0c9a168ec9ac2d0ca6c,0xe699d68ec99a40c69982,0xc9a42d0e99c290e99da8,0xabc2d0cac82d069b42d0,0xd9a8e69d9b0e49d9ace6,0xc2d0e9d96eea9d968ea9,0x68ea9c9b0c69ddb0c69c,0xcec890290c8716eea9c9,0xc8582f0e868c106869a,0xea8e7d04a8e7b04a8c2d,0x9e8290c9ecc106a95ab0,0xa8290c8ac2b0e9e9ace6,0x56cec8b4370e8a96cec8,0x2b0e8a58ae88a5ace68a,0x8e69b829068b02f0e8a4,0xc6a016ceca102d0c9bda,0xea05ace6a056ceca0240,0xad02906a0c2f0ea042b0,0xd96ecaadc2f0ead02b0e,0x8cf0e8cc2f0e8cc2906a,0x2b0e8d9ace68c8cb048c,0x9068d42f0e8d0c1068d0,0xeaa216aeaa21ace6a202,0xaa1d6aeaa1db30ea216c],#[0xb08cd04b082b0ea1d6ce,0x4cd04b04c106b0dace6,0x8290c9f42b0eb1c2b0eb,0x2d0c9fc290c9f9a8c69f,0xeca8c1a8c68c0290c8bc,0xe8ba430a8b82d0c8c56,0xe8f82d0ca18290ca15ab,0x905b6e48fdb2e48e02b0,0xe16eea9016aea8e42b0e,0xc2d0cae96ecaae4290ca,0x89069148f049156ecaae,0xd049e1ab049e1a9049e0,0xcaa296ecaa25af049e1a,0xef6df8e6f6c3d0ef596e,0xf942d06f843d06f7c3d0,0x243d06fb1d6e8f983d0e,0xcc107024c1070202f0ef,0x2906f458aecf48370ef3,0x906fe9d2e8fe03b0efdc,0xafd429070383b0f03c3,0x7315a8e73108907040e9,0x33c2d073356eed3282d0,0xc9b8e62be54a62bc2907,0x8290e2cd6eea2cd6eec2,0x2b0c2d1b8e62d42b0c2b,0xd0e2e42d0e30829062d8,0xe3068ee43042d063102,0xe308d10e2f4d1062f4d1,0x30cd1062fa54a62f8d50,0xecd50e2e4d3042e654a6,0xd1062fcd3042f0d3042,0x2b0c2e0d506310d30431],#[0x8e6c1829063156ca6314,0xcc1c2d0ec18290ec19a,0x6c2168ecc302d0cc282d,0xc8c2d0cc75ace6c702d0,0xa82d0ccb58ceccac2d0c,0x82b0eca8ab08ca9ace6c,0x350ec4c8d0cc4c2f0eca,0xd0ccc56ee8c5240c6c54,0xccd23ec8cce40c6cd88,0x8cc8890ccd63ec8cd48d,0xbc5acecbbc290cba88b0,0x967b04c942d0cb9c330e,0x246a8c9642a8c967d04c,0xace6bcc3f0ebd18cecbd,0x8e6c402f0ebcc2b0ebcd,0xcc5c2d0cc458ec8c45a,0xec59ace6c598cecc6029,0xcbc2b0ecbc2f0ec582b0,0xe0cb04be18ec8cc02f0e,0x8cd04ce82906be5ace6b,0xcd04ce48d0ccf5ace6ce,0x8c6bd82906cec2b0ece4,0x8bd42d0cbdd8ec8bd9a,0xcc698ec8c68290cc6663,0xbec8d0cc082d0cc6c290,0xf08b02c09b6e4c01b2e4,0x82906cf98ee8c058ae8b,0xa8e7100350f0e9d8e70e,0x9071142d07110290f0f9,0x71782f0f0c029071842,0xd0e03f0f0d8c10717cc1,0x190330f13c29070dd6ae],#[0x44290718c330f1916aed,0xda8e73882d0713429071,0x290739c2d073996eed38,0xce66fcdb006fd6aa939c,0x7058ae8700db00701a,0xe6bdace66bdace6814db,0x7d1ace66d9ace679c2f0,0xc8290c6cc2f0e7d1ace6,0x663087a42f0e6c8c1066,0xe2a86ec290c6ea65087a,0x30a6e1aae86e242a86e1,0xc7e82b0e6f16cec6e64,0x67243f0873c290c7e08d,0x728c50675d8ae8724c50,0x2cd30272dc2e072cc506,0xcad0872cab0872ccd047,0xa90873c8d0a72c8b0a72,0xf0a73c890a73caf0873c,0x6738c506721c6e074c8,0xe7482b0e748c506748c1,0x7302d0e7582b0e7582d0,0x518ee87518ae8730cd04,0x4cd047348d0a7508b0a7,0x2b0e7fd6eea7556aea73,0xd067f42d0c780290c6f4,0x7942d067716eca80c2,0x8795a908795af00795ab,0x2ac29068502d06799ad0,0xc8ab092c82d0f2b02d0f,0x16ced29ddaa92a42b0f2,0x3032a82f0f2cc2f0f2a,0xae8b21ace6b202b0eb55],#[0xeb582906b242b0eb218,0x6b6c2b0eb682906b5c2b,0xb742b0eb602906b38290,0x442b0eb408f08b282906,0xcab0934c2d06b502b0eb,0x2d0f355a8e73582d0f34,0x507368ab093642907360,0xed348d0cd350b00d34c,0xd2d0b00d24db00d2833,0xcfc290cd05ace6d2cdb0,0x8370ed0242a8cfe7b04,0xf506dac290cda82b0ed,0x6cecd14290cd10c506db,0xb0ed0dace6d0c330ed15,0xcd85a8e6d802f0ed0c2,0xed942b0ed95b4e6d982d,0xdb56cecdb4290cdbc2f0,0xc16cecdc0eb08dc0330e,0x82b0edb9ace6db8330ed,0x3506d8c2d06dc42f0edb,0xce6dcc330edc83106dd0,0xecddc370edcd6cecdcdd,0x6d45ace6d403106dd56c,0xd182906e002906dfc290,0x74f506d726508d9c290c,0xcb04d51c2e0d50c506d,0xad08d50ab08d50cd04d5,0x6e0d64af08d5ca908d5c,0xe8d59b6e4d69b2e4d55c,0x73b82d0f3a98ee8d6d8a,0x3bc33093a42d0f3b5a8e,0xbcdb001bcdf001b02907],#[0xdb001c08d0a1bd8ae81,0x8b0a19d8ee819d6aea1c,0xf0c16c2d0e1988b0a18c,0x72e449072e049072dc2,0x2a18b002a02d062a849,0x2b029062ad8b0a2a18d0,0x782b0eb8caf08b7cc506,0x5a8e7071ace707cdf010,0x6aed0502f0d0542d0707,0xf0d36c2b0d05ccb05081,0xa831cc50737cab093782,0x63302d0e3202d063396a,0x32d6aa83288b08335a8e,0x196b003182d0633c8906,0x8c5063456b083196d003,0x8b0d1982906e20c50634,0xd071a48b091a1ace71a8,0xb3c4cb051ac2f0d1948,0x90918ae908cc5073cc8b,0x982f0f090890b0918ae,0x542f0f0bc2f0f0ac2b0f,0x4290636033031bd6aa83,0x2906e382906e282906e2,0xb091c829071c429071c0,0x73e029073dc2d073d8a,0xe438c5073e88b0b3e429,0x4da34ec4dac8c84d9cd0,0xe145064d545064dd450c,0x233084e235064e231064,0x830452dcb0e52637084e,0x6c44493b0244a850452e,0xc44a76c844a80c644a9],#[0x845a18e6458650e448e5,0x45dc8e645c650e45a76c,0x4d3b0254dcd0e450e506,0xe76c854e80c654e96c45,0xcce655e76c8558e50c54,0xe6447dcb0e550e50655d,0xe6484650e48218e6482b,0x849abaa8499cb0e571c8,0x3668308366bf0a48e2ee,0x452d0654696c85328508,0x52d06534630e544e50c5,0xe50c535130a53602e853,0xcec548e700538630e534,0x853ce70053c610c541c,0xc46a18e6469cb0e374e7,0x468650e468610e469c8e,0x6a750846a730846a9504,0xe350046e330046dcd0e4,0xcd0c46dcb0c46e2b0246,0x3044e46506470650c46d,0xe5667308565cb0e4e69,0x84fdcb0e3925f0a391cb,0x5765b0a5746106501cae,0xce76c83ce1ce63cdcb0e,0x293043c0630e3cce10c3,0xcec83d0e3083c1cae83c,0xb084a9cd0e4a461063c9,0xc859e70c859dcb0e515c,0x8590e50c59ce10c59e76,0x5a2950459ce506594e30,0x868304384e5065a4e308,0x8e10c4f53f024f685043],#[0x170a3f51b0e4f0e50c4f,0x70e3ee72e83d8e50c421,0xc42672e841ce30e404e,0xc428e30e40a5aea3dce5,0x3f4e3083e1cae83e0e50,0xf5cce83f5cae83f5c8e8,0x5caea3f4e7083f5cee83,0xcee840dcae840dceea3f,0xce8421cae8420e30840d,0xea418e30e3d4e308421c,0xe41281063f8e30e41a5a,0x4bce308428e7083fce30,0x69cf0ee3dcb044cdcb04,0x4630ee68e30ce692d06e,0x3300e51cf0ee668106e6,0x2a8e4a5aa8e45cb0ce52,0xc8e74e106e41cac8e49f,0x6e58e106e54e106e71ca,0xe61c8e6e60e506e59c8e,0x19cd04e5dcb04e5ce506,0xdcee802ce50e029cb0c0,0xe50603ce106035cb0802,0xb0e690650e60276c8600,0xc8681cb0e69c650e619c,0x6615cb0e60e730860e76,0x625cb0e6967308694610,0x29c8ec629cee86265ea8,0x9f2a862a2504628e50c6,0x1506639cd0c629f6a862,0xd0662dc90662c650663d,0x86adcb0e6a25b0a6a1c,0x664ce3085b276c85ace3],#[0x6413106645cd0664dc90,0x49370e64294ec642d4e6,0xe910664d350664e24ec6,0x250664e210664e950664,0x302675cd06669c90666a,0xea5ca72e85f272e85c51,0x85d5cee85d5cae85d65a,0x5f5ceea5d5caea5d4e70,0xece30e5c0e3085f5cae8,0x8e30e5ee5eea5ece3025,0xe3025f8e30e5e4e7025d,0x7085dce7025dce3025d0,0x66a4e3085fce3025fce,0xeefdc90eefce30cf0061,0xebdcd06f05c906f05cf0,0xdcac8f165aa8f11cb0c,0x8e506ed0e106ecce106f,0xcb08e80e708e7dcaece7,0xf0ae81cb0ae81cf08e81,0xa8ea1cf02e8dcb02e8dc,0x2ef4e702ef1cac8ea1f2,0xed86106f1ce302ef8e30,0xd4e302ed4e506ed9c8e6,0xdcb0d1d5cd08eddcb02e,0x23051e5cee91f1cb0d1d,0x5071f5cb0d1e5f2a91e6,0xc065ceec06618e60646,0x608618e6084650e064e3,0x68e30c085ceec0852d0,0x88e30c069ceec06a18e6,0x8e30c089ceec0892d060,0x82c8072db00070650e08],#[0x8ea0721ee807218e8072,0x80721ea807218a80721,0xc06dceec06e1d080721b,0x7d290607d470007ce30,0x8ce70c07dceec07e72c8,0xce30c08dceec08e72c80,0xe30c095ceec094650e08,0x10e081c90e080650e094,0xec075cf0e080e50e080e,0xc099ceec098e30c075ce,0x9ce30c079ceec078e30,0xa0e3080a29f020a1ceec,0x1cd080a1cb080a1c9080,0xcb0a0a1c90a0a1cf080a,0x700119cf0a0a1cd0a0a1,0xc11a72c811929061194,0x412e7704125cf0e11ce7,0xbe1b040bdcf0412dcb0,0x4dcb0204dcac814a1d04,0x27702135cf0c0f9cf020,0x190605dcf02141cb0214,0xf0c05dcac805df2a805e,0xc8155cf02061cb02061c,0x211463020c9cf02159ca,0xf06302165cf0c15c630,0xf4e3020ece3040f1cee4,0xa1d052561b05254e3020,0x2d0722a1d0525a1b0525,0x50f24286ed238650f23d,0xed248e50f24676e92306,0x9251ceed24dceed22dce,0x25d150f2665eed264e30],#[0x69c8ed269ceed25dc8ed,0x5cf0d279caed279ceed2,0xf6a9284630326dcf0d22,0xf0d2892b032812f0327d,0x529a8305298630328dc,0x61e5190e1f6c0e61f685,0x1e5ceec1e618e61e684c,0xfa84c61f8650e1e4e30c,0xe10e20280e6201ceec1,0x810a20286ea20280ea20,0x6e81ea810e202870a202,0xc1e9ceec1ea5aca1ea0,0x6209cb0c1ea07081e8e3,0x1ee730c20a00ea2091d0,0x11ceec20ce30c1edceec,0x1cd06211c906210e5062,0xcd0a211cb0a211c90a21,0x10e27d3f0227dcf0a211,0x828d2d0628e96ea2806,0x82912d06290e30c28d1b,0x21626e4214e30c2911b0,0x15ceec21606e821618e6,0x206e8230650e214e30c2,0x6506239ccc6239ceec23,0xf0c1d607081d5cb0c21c,0xc6249cf0c1da07081d9c,0x81ddcb0c2406302241cc,0x97a8304279cf0c1de070,0x88650e978e50c97a06e8,0x1c8e698e06e898a18e69,0x2e8aa86506991c8c699,0xc6ab0e50caaa5ecaaaa],#[0x6ab65ecaab202e8ab28,0xc919c8ec9191b08918e5,0x91dc8ec93ce50c919cee,0x44e50c91dc8ec91d1b08,0x650e944e50c945c8ec9,0xc8ec94218e694280c694,0x8e692280c69213504921,0xc921c8ec9211b089221,0x4925c8ec948650e920e5,0x925c8ec92618e6925350,0x24650e924610e925ccec,0x680e6926950492693049,0xcd0e925cb0e924e10e92,0x8ec92d1b0892ce50e925,0x892ce50c92dceec92dc,0xc92dcb0c92e050892e03,0x938650c94c650c92dcd0,0x5c650e955c8ec955c8ec,0x9c8ec959c8ec929c8ec9,0xe50c931c8ec931ccec95,0x506934e506935c8ec960,0x8935cd06935c9069346,0xa935cb0a935c90a935cb,0x9646506951cf0a935cd0,0x2d1b08a2e80c6a2ce506,0x1cceca321ce6a30e50ca,0x650ca39cb0ea329304a3,0x506a3dcceca41cceca34,0x6a661ceca7218eca706,0x8a452d06a44650ea652d,0xa5c650ea44e50ca451b0,0x692d06a68610ea5d3f02],#[0x53b02a74650ea68e50ca,0x22e4a48650ea74e50ca7,0x50ea49cceca492d06a4a,0xeca7e24e4a7d3b02a7c6,0x2a50650ea7dcceca7dc8,0xa60e50ca511b08a513b0,0x852d06a84650ca6c610c,0x1cceca4c650ea78e50ca,0x1b08a553b02a55cceca8,0x50ca892d06a88e50ca55,0x649722b02a593b02a58e,0x696ce50c96a366497230,0x99618e699626e499680c,0x94e50c995ceec995c8ec,0xdceec9a9c8ec9a8650e9,0xc8c69b115069ae58c69a,0xd0c9a605089a465069b1,0xc6ac280c6acce50cab9c,0x6ac5c8c6ac51106ac258,0x9c5cb0eabe5b0aabc610,0xc5f0ea9c618e69c626e4,0x4650e9c4e50c9c5f6ea9,0xf0ea9d618e69d680c69d,0x8e69d8e50c9d5f6ea9d5,0x69ddc8c69dce5069d9c,0x49d219049d225069dc65,0xaf21f049d21d049d21b0,0xfe80c6afc650eaf0e50c,0xa9b02af4e506b00e50ca,0x1f0886e02e886ce106af,0x4e887202e8871ccec86d,0xc871ccec871caec8720],#[0xc871c90c870e70c870e1,0x85e1cec891cf0c870610,0x64630e895ccec895ccec,0x630e89c670e865ccec8,0x5eca8994300899ccec86,0x4ea874630e899ccec89a,0xec88602ea88604ec8760,0xc8565aca8551d0c88604,0x869ccec8692906869cce,0x825eca880e708868670e,0x9ccec8a0630e881ccec8,0x6302859ccec889ccec87,0x70887dccec87c650c858,0x288dcb0088c630288e7,0xa88dcb0888dcf0288dcb,0x88dcd0a88dcb0a88dc90,0x8ed304a8d2b02a8dcf0a,0xe84caa8e80caa8ed504a,0x4300aa286a8a8e8302a8,0xacaa925ecaaa12d06aa1,0xeca952906a95c8eca925,0xaa992d06a98e708a95cc,0xa9dccecaa5c8eca9a5ec,0xedc8c69ec63029746302,0xdcb0e9e9c90c9ec61069,0x61068adc8c68adf4a68a,0x8c69c1cb0e8a5c90c8ac,0xc9be05089bc63029bdc,0x6ad5c8c6a09f0a6a09cd,0x8d5c8c68d5cb0ead1c8c,0xc933048c9ceca8d46106,0x293048c9ccec8ca1ce68],#[0x9506a2065068dce1068d,0xecab11c8c6b11cb0ea1e,0x2b0a1ce6b093504b09c,0x6b0a9504b0a9304b08e3,0xb1a0508b186302b1a84e,0xce106b0dcccab19c8ca,0x8e30eb14e506b14e70eb,0x63029fce506b1dcea8b1,0x90c8be83049f283029f0,0x48ba83028b863028c5c,0xa8ec6302a1a85048ba83,0x8f0e50c8e222e48e1cec,0xf1ccca8f1caca8f1c8ca,0x863028fe26e48fdceca8,0xe30e8f8e3048f8e7048e,0x7048edcee48edcae48ec,0xe4909ceea8edcaea8ece,0x28f0e3028e0e304909ca,0x8f1caea8f1c8ea8f0e70,0xfce3028fdceea8f1ccea,0x4e302904e30290ce30e8,0xe3028e4e30e904e30490,0x7048f4e7028f4e3048e4,0x6ae0e304910e302910e,0x2ae86106ae5c90cae061,0x9e219049e065069e4630,0xe21f049e21d049e21b04,0x46106a25cd049e1cb049,0x1b08f71ceecf5606e8f5,0x8e6f6d1d0ef58650ef71,0xef6d190ef6ec0e6f6e1,0xef5e18e6f5d3504f5d1d],#[0xf6206e8f6200e8f60650,0x620108f61cac8f61ceec,0x9cac8f75cb0cf620708f,0xe10ef68e106f68650ef7,0xb00f7e06eaf651d06f64,0xecf8200eaf7d1d06f7ec,0x700682c900ce506f85ce,0xff12d06ff0650f0052d0,0x8610effd3f02ffc650e,0x650f0091b090092d070,0x650f0111b090113b0301,0xd07019cac90013b02ff4,0x2ff8650f0151b090192,0x4f891b0901d2d0701d3b,0xf9226e4f923664f8a306,0x91ceecf9206e8f9218e6,0x9ceecfa606e8fa4650ef,0xccc6fae0086fad1506fa,0xb0cf9e0108f9c6506fad,0x70320487031110702dc,0x4fbce106fc1c8e6fc061,0xf291f08f29cb08fbdcb0,0x29cac8f28e70cf29caec,0x5cf0cf2a0708f2a0108f,0x4300f38630ef351b08f3,0xaecf2c630ef3a5acaf39,0x702943010291b08f31c,0xf02281070225acb0292d,0xf406106fd06302f8dc90,0x406106f41f4a6f420486,0x5ccc6fba0086fba0708f,0x86fe5cb0cfb46302fb],#[0x487035ccc6fe5f0a6fe6,0x2fd46302fd9cb08fc60,0x2f520708f4d1b02fd91f,0x4861070446302fec630,0xc8e304fc8630304c6107,0x9cd04fcdcb04fcdcb02f,0x18e731c650f31a06e931,0x8e7304650732206e931e,0xf304e30d3051b093061,0x9308e10f31280e731065,0x308e30d309ceed3091b0,0xdceed30dcb0d30a0309,0x13f03340e507314e30d3,0xe30d3452d07344610f34,0x6e5324e30d3492d07348,0xf325ceed32618e73262,0xd2f86507331ceed32c65,0x3006303339cf0d2fdcf0,0xb69c862be98862bdcf0d,0x4650e2b4e30c2b5ceec2,0xceec2c618e62c684c62c,0xac82ba5ac82c8e70c2c5,0x62c1cb0c2b9f70a2b9c,0x62f5c8e62f5cee8304e1,0x2edcee82ece50e2e4e10,0x4e506311cb082edcb04,0xa98862fa98e62f69ee83,0x9c8630e988630e9c862f,0xee82ee9f042ee9b042ee,0xc2e29f082ee9b082ee9,0xcc2676c8c269ec8c2dcb,0xc1a9304c18e10cc25c8e],#[0x1a5ea8c1a80e6c1a9504,0x9cb0ec18e10ec18e308c,0xc8ecc1ce50ec19cd0ec1,0xec8c1df6a8c1ce50cc1d,0xec3676e8c35cec8c29c,0x6c20e50cc39c8ecc38e1,0xc21c906c20e308c20e50,0x81cf08c21cb08c21cd06,0xe10cc7a76c8c7a9ec8c,0xcb0ec70e308c729304c7,0x6c8c91cec8c7dcec8c75,0xc8c8dcec8c8a76c8c868,0x6cb9c8ecc3e80c6c3dce,0xcb270c6cadcceccba80c,0x4dcb0ecaa7308ca9c8c6,0x65ec8c55f6e8c4e5ec8c,0x5d04c525b04c51f6e8c5,0x8c6cce5ec8cda5ec8cc6,0x4cca5b04cc91106cce5,0x6ce25f08cca5b08cca5f,0xba9ccecba5f2eaba4e10,0xa276c8ba286c8bbdcec8,0x1ccecbc276c8bc1ccecb,0xf4ecbc4630ebc0e50cbc,0x8ecbc9ccecb99150cbc5,0xe8bca72e8bc9ccecbc9c,0xabace70ebc8e30ebca74,0xbb5f2eabb5ccecbadf4e,0xb8e708bb0e50cbb5ccec,0x5cec8c9dcf08bb9c908b,0x86c8c9680c8c96aea8c9,0x508c968308c968302c96],#[0xcca1f0ecca11302ca28,0xcca5c8ecca5c8ecc9915,0xc41c8c6c49cb0ebcdcce,0xbdcb0ec59c8c6c5dcd0e,0x9cec8bea9304be1cb0ec,0x5ea8cea9504cea9304ce,0xec8cf1c8c8cf1f6a8cf2,0x4bd5cd08cf1cb08cf1c,0x8bf9f6a8bfa8504bd683,0xbf5cec8c01cec8bf9c8c,0xf4e704bf5cee4bf5cae4,0xdcee8bf5cae8bf65ea8b,0x5ea8c0ce304c0dcae4c0,0xae8bece302bedcae8c0e,0xa8bfa5aa8bf8e702bf9c,0x8bf9cae8bf9c8e8bfa5e,0xc025f0abf9cee8bf9cce,0x1cae8c025aa8c00e302,0xe302c10e30ec01cee8c,0xcce8c11cae8c125ea8c1,0x704bfce702bfce304bf1,0x4c14e302c14e304c04e,0xd0e69ac9109f106cdce3,0xfe84c70fc650f0e4e30,0x280e71025ac90e8e70d,0xdf0eb0ece10f10258eb1,0xcac90ece30d0edceed0e,0x8eb0f8e1070f9cac9105,0xf0f8e10f0f9c90f0fa5,0xb10ce30d0f1cf0f0f8e5,0xf4e30d10dceed10df0e,0x60e309110e5071111507],#[0xa84c7158e30d14a9ac91,0xcac91525ac914ce70d15,0x90f154e107155cac915d,0xd17682c9171cf0f155c,0xf165cac916dcac9168e3,0x11dceed119cf0f165c90,0xc4e107125caed189ccc7,0x4e30d0d682c90d1cac90,0x74e90c272e90c0630f0d,0xf0f0c0e30f0c1c90f0c2,0xd0cdcaed0c8e70f0c1c,0xf17a8107179cac9180e3,0x141ccc7121cf0f179c90,0x35cee5135cb09129ccc7,0x5c8e7134e505134e3051,0xcee512ce30312ce50713,0x303138e50712dc8e712d,0x3130e507139c8e7138e,0x3130e505130e305130e3,0x385cd05131cb05131cb0,0x88e70d38672c938618e7,0x1cac9381f2a93825aa93,0x5ac9391cb0d381f30b38,0xee93965aa9395f6e9392,0xc6710630e6f8e50c6f9c,0xe710e50c7121ce671280,0x6fce50c71658ca714670,0x1dc8c871dcae86fea300,0xa58ca7094700709c8ca7,0xe50c718670e708e10c70,0x10670ce506700630e718,0xc6820e506705c8ca70c6],#[0xc820e10c82202e882280,0x814e50c828670e820e50,0x1684e6816a500816a300,0xe2b0282ce308815cae88,0x630882dcec882e250482,0x506832a500830670e818,0xe681ce308811cae8810e,0x482ce506824e50681dcc,0x8029900801cb0882dcd0,0x69f008029d008029b00,0x1c8c66c0e3006b93f008,0x61067a1c8c67a061066c,0x8c67d461066ddc8c66dc,0xec6c4610c6cc61067d5c,0x6d1ccec6d4630e6c5cc,0x6d1c90a6d1cd006d1c90,0xadcf0a6d1cd0a6d1cb0a,0xce50c7ad1b087ad3b027,0x86c87a4e50c7cc610c7b,0xca7a6c5087a6c3087a6,0xa87a685007a683007a68,0x67c129067ba83087a686,0x7a92d067c4e50c7c12d0,0xb1ccec7c8650e7a9c8ec,0x51b087b4e50c7b11b087,0x63087b603087b61d067b,0x3086e285006e283006e0,0xca7ec610c7de85086e28,0x87d8610c7e1ccec7ee58,0x72e32e072c63087e5130,0x2d1d0872d1b0872d2d06,0xd190873ce50c72d130a7],#[0xceca73d170a73d1f0873,0x9067392d0676236e074d,0xe738e10c73a58ca7392,0xc7492d06748670e73861,0x724650e748630e748e50,0x5ce30075e72e8724e300,0x274e875e72e875e85067,0xe50c73202e87312d0673,0x6e8751c8ca740650e730,0x7292d06765130a7520,0x872e5aea728e308728e3,0x73e810673ce30872dcce,0x3e710873dcee873dcae8,0xdcaea73ce70873e77087,0x5f0a73e590a73dceea73,0x30874dcce874dc8e874e,0xe74dccea74dc8ea74ce,0x720e308761cae8760e3,0x748e700738e30e720e30,0x5a5eea758e300758e300,0xe700740e300730e30e7,0xe300751ccea741c8ea74,0x30e751ceea751caea750,0x8734e300734e300764e,0x768e708744e700744e3,0x7fce7007f8e308768e30,0x8c650678c61066f4e300,0x225047822304780650c7,0xcd0c781cb0c781f0ca78,0x8ec78a58ca788650c781,0x67f06506785150677dc,0x7f465067f4610c7f061],#[0x7f5c9067f5cd007f5c90,0x6c610676c6106809cd06,0xa32e0839cb00791ceca7,0x36e084461068411b0883,0x5048491b0883d1b0884e,0xea834e506835c8ca84a2,0x67786106775cb0084a5a,0x211cd08795cb00794610,0x14e7012053f01219cb09,0xa2305208650720ce7012,0x2f012c21b092d1cb0d20,0x3012b8e7012b52b012c5,0x12d61b012d4e7012bce,0x12da1d092d61b092d61d,0x2da1b092da1d012da1b0,0x65f2eab321ce6b321d09,0x9cb0eb20e708b64e700b,0xcaeab3ce106b71cb0eb6,0x50f34dcb04b4dcb00b4d,0x735dc8e735e80e7358e,0xcd3290c4d31cb05350e5,0xd35f4e6d3658c6d34e50,0x38e506d29cce6d291506,0xe90c4deea300d2dcce6d,0xe506de51506df0e50cde,0xae8de25aa8de2a300de8,0xe8dee5ea8dee5aa8dedc,0x8cfe8500cfe8300cfdca,0xd091700d028508cfe830,0xa0610cda9cb0ed08e300,0x11300dad1700da696c8d,0x8506db0e300db1ccecdb],#[0xb0ed0dc8c6d11cb0edb2,0xc6dbdcb0ed95cd0ed81c,0xedb8630edb9ccecdb9c8,0xdd1cd06dc5c906dc5cb0,0xcd150cdc9f4ecdc9f0c6,0x51506dddf6c8dda5ec8d,0x630ed3ce50cd3dc8c6d4,0xec8d4a9304d40e300d40,0xdf8e50cdf4e506d4dc,0x4d1ce300df4e506e04e3,0xd9e8304d9dcf04d1dc90,0x751908d5e5b04d228504,0xdcce4d51cae4d5274e8d,0xcce4d5dcae4d5dc8e4d5,0xaa8d5e8106d5dcee4d5d,0x8d5e7108d5e5ea8d5e5,0x4d65c8e4d665f0ad5e77,0xd65cee4d65cce4d65cae,0x79cce4d79cae4d78e30e,0x1cae8d54e300d565ea8d,0x5ea8d625aa8d60e700d6,0xce8d61cae8d61c8e8d62,0xa8d68e300d69cee8d61c,0xd7dcee8d69cae8d6a5a,0xd7dcae8d7e5ea8d7ce30,0x90e300d6ce300d59cce8,0x9cce6e09f504d91f304d,0xe506e0dcce6e0ce106e0,0xd04e11cb04e11cb00e10,0xe73b1cee93b9cee93a9c,0x93adcb053ace1073b1c8,0x17dcb0d3a1f30b3a1cb0],#[0x7a06e8178e70817dcee8,0xa5eea18676e8180e30c1,0xe70c1adcae81b0630818,0x7081b9ccca1b5caea1bc,0x19c63081a1cac81a06,0x818dc8e818c63001a4e3,0x194e3081a1cee81a0e30,0xa4e300190e300198e700,0xc67081d12f001cce3001,0x6700170630c175cf0c16,0x7081c9caca1c4e3001a8,0x72e219072dce7012ec6,0x12e9c90d2e619072e619,0x2a619072f067012f4670,0x7df2a8b79cb042a5cb02,0xa7708b7ce702b7dcae2b,0xe700b80e302b89cae2b8,0x702b84e302b8dcaeab80,0x7061cb00b906106b94e,0x7074e107079cce7078e1,0x65c8e70646507075ccc,0x68e507075c8e7074e507,0xdcb09069cd01069cb010,0xcb03370e301084e10706,0xb0431dcb0231ce303379,0xe63265ca6325cb0831dc,0x83265aa8324e506325c8,0x339c8e633a5ca6338e30,0x3280e6330e50e320e506,0xa5aa832a5ee8334e10e3,0xcb00328e308329cee832,0xee832dcb08329cd00329],#[0xae14e300e1ce50633e5,0x11b4e30119ce300e1a5f,0x95cb093c1cb033c0e30,0xb4e303098e703091cac5,0x8e3030b8e7030b1cac50,0xe30834e5aa834e19070a,0x8e635df7011ba5ee8350,0x2358e304358e50635dc,0x4e2dcae4e2dcb04359cb,0x1c8e302e34e702e30e70,0xd8e5073d1c8e73d0e303,0x5cb013d4e5073d9c8e73,0xcb093d5cb053d5cd013d,0x24c00c8004d001800001,0x804e0021e00eb006180,0xfa8071c0346018500b,0x26a0126008dc0440020a,0xb802c7015580a5c05040,0x406c0033e018980be405,0xf50078803af01c900de,0x1901088081a03fd01f20,0x7023b8119c08a4044202,0x4d1025e0129c092e048,0xa94052b028b013f409ce,0x1c0b68059f02c5015c00,0x18cc0c3605f802ef817,0x35881a580cfc06660325,0x30038981bd40db806c40,0x2079903bf01d840e9a07,0x10b0083d040681f900f6,0x35c117408a20444821c0,0x9024ac122c0901047602],#[0x4ea826cc1326096404a,0xa78053182900142e09f3,0x20ae7056902aac152c0,0xc170e0b7105a982ca016,0x30f018080bdb05e302e8,0x7603314194c0c7c06308,0xa06b9035741a740d1706,0xe3e070a0376c1b6a0d9,0xdea0ee0076583a881ce0,0x641f020f55079683c601,0x841502054100607e703e,0x87284308214810840835,0x8608b0844f0223011000,0x6120708f0846f8234011,0x256c1294093504930245,0xd6826741315098084b68,0x604fc4277813a709c104,0xa3f85174288414270a0,0x5610a9f0544429b614bd,0x615e00ae2056602afc1,0xc2cde16510b1b858682c,0x5d502e4216ef0b6605a7,0xf85fc82f9417a70bbe0,0xf0c530623030c4184c0c,0x195d0c9c0648431fa18c,0x40219e60ce9066b0330a,0x8c35161a550d1b8685c3,0x86cfc36341af50d5f86a,0xdf406f2837501b860daf,0x7c0e2f070e8384c1c0b0,0x61d190e758732c39521c,0x3b661da00ec3875683a6],#[0x8843bf41de70eeb8770c,0x307ad43d081e6e0f2c87,0xfb807d443e4e1f000f7,0x30100107f743f721f91,0xe020c81050081d040902,0x843002166109f0845c41,0x88b0441c21e410e00869,0x7f88b48455e227d11230,0xa11d388da84696232b11,0x24881236890c047f423c,0xa7c251b1277093104954,0xc04b9e25b412ca095c84,0x899844c90262e130a097,0x38509b8c4d7e26a41343,0xc913d489e144eac27331,0xc2833140c09ff84fc827,0x51c228c614458a1a0509,0x66452e6294d148f8a410,0x58a920543229f514e38a,0x156c0aafc55522a8f153,0xb7c15aa8ace856442b02,0xc02c3f16020af6457622,0xc59c42cbe16498b1e858,0xb6805ad42d4d168b8b40,0x1c0b8445bf22de116e20,0x8175a8ba485cfc2e5b17,0x2f6b17a60bc785dfa2ed,0x3e300317ef0bedc5f20,0x806172309118368c1146,0x8c5886286312b18840c3,0x9070c7a4639031a918c0,0xd8195a0ca3c64ce32441],#[0x4337819a58ccb4662432,0x6864340919f00ceec673,0x2e8694834911a338d110,0xb0d5546a5c35081a728d,0x1afc8d7306b5c35921ab,0x6c81b550d9c86c7a3610,0xfa37591b998dc446dd23,0xc6ffc37db1bdd0de506e,0xe3487162387f1c278e09,0xc18e570726239101c798,0xa1d0f8e7e473b839b51c,0x3ad01d5a8ea6c74ea3a4,0x6fe3b5f1da18ec7875fe,0xf478163be31de68eec47,0x8f3bc798a3c981e358f0,0xed40f6587abc3d381e8b,0x9f1f370f9047c1a3ddc1,0x23f531f968fbec7d963e,0x7fdc3fd71fda0fe0c7ee,0x2b8811c4064201f1006c,0x69050c823a40f8206410,0x210e107b08378419820b,0x2f3216710a9c84f84253,0x36436a21a610c8886104,0x88898441d21fa10f0c87,0x1390898444a0223c1118,0xc7115948a84452822851,0x72317918308bca45bd22,0x46fe236a91a888ce8465,0xf58478123b011d108e44,0x809086480c23f491f3c8,0x923dc91b448b42448921],#[0x4dd1264892d6493e248f,0x6e251b9283c93e049db2,0xe4add256012a9c95164a,0x97784b9c25b412cf8961,0x170986e4c18260092f6c,0xb133b0997a4ca6263e13,0x26cd935e09aba4d40268,0xe82272f938c89bec4dca,0x864f1e277593b149d3c4,0x49fce4faa27c493d909e,0x429ca0f85053281b1405,0xb5144e4a21c50ea28651,0x92906147d0a368519228,0x52c9295694a2ca4b8522,0x6f05356299d14c6ca5f0,0xa4a7f853d129d514e4ca,0x952c4a90a546a2a23150,0xabe95578aa6455092a6e,0x342b0b157b0ab9c55a62,0xc56b92b52159c4aca456,0xae9857262b8595bd0ad9,0x58afee57d42bd295dec,0x162e8b11e58682c2096,0x2c989647cb21a58fb2c7,0x9b22cce965d4b2c65943,0xe25a5b2d1a16838b3b05,0xcb5e25ad92d5896a4cb4,0x6ea0b6e85b4c2d9416c1,0x3a970fcb81e5bf12de69,0xa2e92973f8b9a65cb02e,0x5dfd2ef1976fcbb0c5d4,0xd7e5e942f3217914bc40],#[0x2cbeb65f2b2f7b17b70b,0x980a8c0205fdc2fd517e,0x7818330c13060673021,0xc230d0185c8c28861193,0x6252311b1882cc3d061,0xc64862e8315a18a70c4f,0xfecc78e639d31bd98d1c,0x21921cc8da6448321198,0x329f99450c9dc64c8325,0x5ee32e8996accaee6568,0x3a667b3333998dccc066,0x8ce5466fb336e99aeccd,0x9f44cf56679733b799d2,0x321a12cd05a680b33f71,0x434761a338d138688134,0x69b234bf1a568d264691,0x4da6a4a35181a804d3b2,0xd0d63e6af635631aa7cd,0x9aeacd72c6b7835a69ac,0x62f9b0e4d82c6c0235ef,0x2336779b338d9586c7f3,0x46dc536d19b5dcdabc6d,0xdd326e6e37219b870dbe,0xd2cde3e6ef737699bae8,0xe9bf60df706f9337b99b,0x38469c1ace076701d37f,0x15338921c400e1ce70c5,0xea71d638d91c654e2ec7,0xe53a727639231c878e3,0xcddce692731239799cb1,0xb9d00ce7dc73c739d11,0x13a5f1d23ce8d674473a],#[0x75913ab31d4e0ea1a74e,0xce4763a3b059d75ceb78,0x90ee0876ec3b5e9da84e,0x9df20ef30776d3ba39dc,0xc469e194f06c780d3bf3,0x3e3c919e3e0f19c78a53,0x279cd3cda1e634f2d879,0xf5847a9f3d359e920f41,0xe38f6de7b503d8e9ebc8,0x59f040f7e07bd83dd41e,0x3e589f260f8f27c463e1,0xd683ea69f498f9ee7cdd,0x787e1f3ef71f700fb1a7,0xfd8c7e9e3f441f97cfc,0xfe1cfed07f3e3f8a9fbc,0x1920008ffce7fc93fd51,0x44064a029d00e4805040,0x818d40aea04d1020080e,0x48082224105207850384,0xdd0586828b4137a095d0,0xa0e3106b68339418f20b,0x21ea105107f483d141d7,0xec425ea125108ea84564,0x4859042b0a15010a2684,0xc6a860942f82174d0b7,0xadd0d2886744330a1931,0xc21d090e4687104374a1,0x43f521f090f22876b43a,0x89c4441a21c1108c8821,0xe689444489a23e1118a8,0x5142e89f644e4a267512,0x2bd5159a8aa34537a290],#[0xe522e9116f48b4a458f2,0x2463a23119182e8bf945,0x8d344688233b1197e8ca,0xbb68dba46caa35cd1aba,0x251cce8e3a4709a37d91,0x23c4d1df48ed24755a3a,0x7d8a3e5d1f008f55479a,0x4d48142404d1ff28fdb4,0xc90d948512421d20ce90,0x2322916a48a42448d21f,0x9e1248c921448ef246d5,0x3a4c5525d892d64954a4,0x49eea4f012738937449a,0x40549fea4fd527da93e5,0xb894514a21a50bd28449,0x5298094a64a49251e928,0x55b92a9895234a812538,0x257912b8095a94ac12,0x14b2fa58f92c46960e4b,0x96ca4b5da5aa52d0a967,0xec297534b9e25c452dde,0xe52f5697944bc325df92,0xa60cd302497f54be925e,0xc58a627130fc98604c26,0x1f4c81263ad31b498c64,0x99994cb8a6525325899,0x341e99fa4ceda6705335,0xa1534d69a4a4d1ba688d,0xfa6b3935729aaa4d4ca6,0x4d9e26c5536049af44d6,0xbce4dd426e4136f69b68,0xf09c564e13a703937e69],#[0x939be9cc94e5f2725938,0x74b93a329d044e7ba73a,0xd2276393ade9d584ea1a,0x4efd2778d3b9a9dc04e,0x9e5e4f26278e13c449e1,0xd669e9f4f46a79d13cd2,0xe93e1e9eee4f6927af93,0xa7ee93f4e9f874fb027c,0x29280d5403e9fff4fed,0xac504c2822940eca0665,0x2a0f85072283494180a0,0x42faa16d50ada84e1422,0x765438ca1bb50d3a8651,0x6a88b1442ea1f450f328,0x516028a8144fea26a512,0x336519028c0945cca2d1,0x8ea39d51c528dcd46aea,0x94850a41b5200a8fa147,0x92794902a4715227a910,0x81293e149d0a4d3525fa,0x652b8295314a6ca52652,0xa5f152e9a96d14b40a58,0xd02a660531fa98a94c24,0x9d4db2a6c25358a9a814,0xa9c594e12a6fc537a29b,0x3ab29d154e70a72b5391,0xac53ce29e214ef0a7675,0xca80f53fa29f794f8ea7,0x50eca8605429aa0ed503,0x37d518aa8b35449aa211,0xd2a5215260a917547baa,0x54dbaa6855322a97b54a],#[0xa2555042a7c953b2a9c8,0x6caa97553daa9955488a,0xd5614aaf4556f2ab2955,0xaeb95724ab6c55a1aacb,0x27ab0b55816abe255e22,0x2565b2b2655908ac7056,0xad30568b2b3ed59d8acd,0xb84ad9d56c0ab5ad5aaa,0x795c8cae2457042b7915,0x2bb695d7eae9b573cab9,0x7a82bce95e4eaf17577b,0xcb57ddabe815f0caf6f5,0xeb02f5809abfd95fccaf,0x619ab0b1584aac1d5609,0x50d6262b121587bac369,0x1ac6ad6336b18558b6ac,0x59132c83163e2b1da58e,0x2a05943ac9c564aeb23d,0xfeb2ef596facb016560b,0x166b0b349599cacc6d65,0xcf4d677ab3ab59caacdd,0x21ad0c16838b3f759f2a,0xc5a542d25168eeb4635a,0xb5325a862d3a969a2b4b,0xb78b5a85ac42d5d16a9e,0xb16c96b6255b042d77d6,0xadb556d7eb6a35b43ad9,0xbad2dced6e3ab7075b75,0xbc5bd32de556f02b76b5,0x4b80a5bfdadf956f9eb7,0x7144b8855c37ae119704,0x41171e8b8de5c60ae2d9],#[0x2e591729cb9315c8a2e,0x5cf4ae70d7366b99c5cc,0xaa75d462e98d747cba19,0x54bb155d7f2eb857588b,0xd773cbb835db32ed4176,0xf0997822bc005def2eee,0x472f1d578bcbc4e5e1ba,0x15e86af3d579a6bca85e,0xbda85ebdaf59d7a8cbd2,0xca4be345f0d2f7c57bb6,0x197dbabeb05f492f9e97,0xafe317ec6bf475f92afc,0xdb00197facbfc15fd0,0x7f60353015d808ec02b6,0x2c0ea606bb031d815cc0,0x82eac14e6097b0455820,0x80983b0c1bb60d33060d,0x2b0959848ec22c610cb0,0x616930ab5851ac278613,0x34a619a30c658600c2e8,0x62c39961bf30dbd86c2c,0xd8828c3f561ebb0f1d87,0x12a98926c472622c310c,0x91b140989dcc4d5625bb,0xd62b2315498a8cc53762,0xc5ce62dcb169d8b24c57,0xc60c626630b3181d8bd0,0xa98d1ec67d6335319418,0xb1bfd8dd6c6d0635d31a,0x3b431d498e7cc72b638a,0xd863e2b1ed18f1cc7796,0x2c81c640631ff18fd0c7],#[0x9134c8846430b2119906,0x46d9210c8f06469b22d1,0x325c192b4c9456497b2,0x64edb27399362c99d64c,0xa4c6517b287593fec9f1,0x44ca94653f329c194c4c,0x995e0cae4656632ad995,0x2da196a6cb37658bb2c0,0xdab2e919732cb8265bb3,0x56607b2fed97cecbd065,0xcc71662b330fd9866cc2,0x9beccd06658b32819910,0xd99a8ecd296687333d99,0x337a59b80cdb166ca335,0x725b38f19c52ce1266ff,0xbd6753b3a259ce6ce596,0xccf1b6781b3bc59dbcce,0x9f4ccf8867b533d319e5,0xa9a02ccffd67ecb3f09,0x2b4249a0e2d058681f34,0x6888343d5a1b8d0be685,0x16d68ab34539a266d122,0xcad1cb68d9b4671a2fcd,0x9a486d235690f347fda3,0x4ac9a54ed28969373496,0x84b4bd1a5aed2cb6961b,0xa69aa34d15a664d31e69,0xd3e969e4b4eb1a710d36,0x8b4d4416a18b506da80a,0x8da994d4b46a49351d1a,0xb551daa50d5116a7bb53,0xadc3567dab16d5786aae],#[0x2f6b03b57d1abb2d5cc6,0x8d6846b3335959ac86d6,0xadced6d46b60b5a91ad2,0xd39ae7ed7266b8235be5,0x2b5ea9af2cd7866bb735,0x6c12b605daff0d7d46be,0x8996c3b36181b086d82d,0x48d8fd6c76b634db188d,0xdb326d97f6cb63653db2,0x6869b404d9de6ce2366a,0x4c36a19b4ceda3c6d173,0xb6d7fb6bc1b5a6dac16d,0xdb606da436cf5b660db1,0x7c8dbcf6dd936e59b70a,0xedb83adc136e0336fc1b,0xb7269b902dc766e2cb70,0xe98b7455b9eedcce6e52,0xaf6eccb75bdbac2dd446,0x6ddfd6ef437759bb90dd,0xbd0ede6f6f29b78c9bc3,0xbc5bdccdec66f58b7a59,0x5b7d71be7adf226f89b7,0x6fe4b7ec5bf32df836fb,0x36700d38029bff0dfdd,0x94e0b77049381a5c0a2e,0xdc256e116707eb8389c1,0x8731c34ce18970af3850,0x2f38911c43ee20170f3b,0x4716b38ac1c534e27b71,0xe34b719f38cb5c62ae2f,0x734e38b71c0b8dadc6ba,0x11c7e8e3d671e038eb9c],#[0x391a1c890e4377211b90,0x262392cdc944e485723a,0x2c7289393e1c9cee4d77,0xae58872ba395a9ca9ce5,0xcbd6e5d572e2396d9cb4,0x96dcc94e632730a3980d,0x1b9ab9cd44e68e733bb9,0x738639bfdcde6e6df736,0x77773af39cfdce4ce714,0xdee7e773e1b9eb9cf42e,0x9d072e8207407b9ff9cf,0xa2bdd116e86b742d3a12,0x953a449d1e8e8df74653,0x74b93a555d28ae93874,0xea0274f1ba6fdd342e99,0x4d0ea577526ba915d442,0x89d58ceaae7545ba9f1d,0x3acb1d648eb1475803ab,0x5cbbadfdd6eeeb5e75a1,0x175f8baf35d77aebad7,0xaec5576223b0cdd846ec,0xd98cecb276503b205d8d,0x4e9da36ed09767a3b379,0xbbb681daeeed5d76a5bb,0x770ebb821dbe6edd676d,0xe90773bbb975dc9aee3d,0x2eee6776a3bb19dd4ae,0x1dec4ef50779dbbc59de,0xbf65df8eefb277d03be0,0x1ebc061e016eff377f33,0x778573c261e0faf05578,0xf14d7895bc455e1eef0d],#[0x3b6f1bf78cabc615e2ec,0x61e4e0f24a79173c829e,0xbcc1de5c2f2cc7955bca,0x9c93cde1e6c4f3487998,0xa79fbbcf81e792f3ac7,0x6f4647a253d0d1e832f4,0xe988f4a97a4a3d1fde8e,0x4d5ea2cf5047a77bd375,0xbbd60deae4f5547aa23d,0x7af13d745eb76f5a57ac,0x65c7b233d8c1ec3ef5f8,0x9af6b27b4abd9fdecd6f,0x1ee4af7157b7b3db95ed,0xded1ef30f77e7bb13dcf,0x123e041effaf7e87be9b,0x77c47be1d1f0aef8397c,0xf9037c743e329f15ef89,0x2e2f95a7ca53e4b9f230,0xe1f3cef9c37cd23e625f,0x3e941f47afa227d03be7,0xd6b3eaf5f54cfa8e7d35,0x607da2becb5f632faf97,0xcfbc67dd53ee35f6f8fb,0xf8d4fc4e7e173f015f7c,0x395f994fcaa7e4f3f1f9,0xa3f50dfa76fd227e843f,0x7ed5bf62dfaeefd607ea,0xe147effbf7a5fba8fdc0,0xfafe717f2e3f8cdfc46f,0x5fdbafecc7f55bfa49fc,0xfd3dfe80ff2b7f873fbb,0xef3ff3dff50ff887fb6b],#[0x68024c00ca0020fff97f,0xdb805f40272010d006,0x2b1014580984044e01e1,0xd603ab01ba80d0c06060,0xc0966047502318107c07,0x15f40a8e052902808138,0x52819740c5205f102de8,0xd039281c040dba06bf03,0x853041781fe40f66076,0x29e08f904678227c10e6,0x64140a09ef04ea8264c1,0x82aa415060a590514828,0x5d082dbc16560b09056f,0x63061a8302417d60bbf0,0xa0d1d067e832f419260c,0x1c7e0deb06de836141a9,0xc041dae0eb907478397c,0x283f841f2e0f71079683,0x8558424420d61035080,0x1c708cd84564223210e1,0x1e1263091b8488423de1,0xc26de1321097984abc25,0x525428ca143f09ff84ee,0xd8855c42a4614df0a5b8,0xb0b378590c2c3615d30a,0x17650b9685c042d96169,0xc2182b0bfb85f5c2f36,0xac320e18e10c5b861c43,0x8682433a619a50caf864,0xd7f86b4c35121a670d20,0x30deb86e7436aa1b3d0,0xa1ca30e3c8713438521c],#[0x3b6e1d730ea98743439a,0xb043d561e7d0f1d877bc,0xa87e243e961f1d0f7687,0x103b8816c403e1ff30fd,0x19b10ae8849441fa20b5,0x6a227b111f8881443b22,0xc46822307117388b5c45,0x91d4486e23ff11e088df,0xc08953c4a5a24f5125b8,0x113188981c4bba25a712,0x26e3136889ac44d22265,0xf5e278713ad89d144e32,0x8c50d2283313fc89f2c4,0x8a60c528228f714678a2,0x5328a8e453fe29d714d7,0x3f15918ac1c55b62aaf1,0x62c0f15e88ae8c56ca2b,0x599a2cb916488b164588,0x66c5ade2d5116988b414,0x98ba1c5c9a2e0116ea8b,0x17b88bcdc5e2e2edf175,0x5f18198c0345fba2fa5,0x8230fb186d8c2ec61363,0x4641231e118d78c58462,0xcb2c655a326b19258c87,0xee8ce5c66ca332b197e8,0xf1a648d284689e342719,0x35db1ad18d5d46a9634f,0xe3e36e71b528d9dc6c46,0xc6fbe37b11bc28dd346,0x8e36c712e38731c248e0,0xcdb8e66472d239331c82],#[0xb31d3a8e8ec741639d51,0xe3b891daf8eca475ba3a,0x79223c591e108eff4778,0x6647a8a3d171e798f33c,0x18f8fc7c1a3ddb1ee28f,0x1f858fb8c7d823e8d1f3,0xfef1fec8fe5c7eea3f45,0xc640a5204190144804e3,0xc8366417720a79049481,0x9c48492423920fb9073,0x9f90c8485d642b1214c9,0x521f590ed4872a436b21,0x44b3224791194888a442,0xb2e457722a29144489be,0x2c8d1646532307916dc8,0x91e348e96470b237591b,0x42792084900247c923d5,0x2324709231c913a48732,0xe49d724df9263c92ba49,0x95824a872525928a493f,0xf24972a4b53259492bf4,0x79325498ee4c3b260692,0x26da935ec9aaa4d17266,0xeb3273c9393c9c424ddf,0x424f5f279093bbc9da24,0x4a096502d27f993f449f,0x448ca21a50e52856941d,0x12947eca366518928af9,0xb296694a94a4f6525b29,0x53b329c494d7ca65a530,0x96654852a2694ffca7aa,0xbcab7a557b2a9e953eca],#[0x95b34ad0656572b16957,0xbdf95e3caeae57392b77,0x492c799626cb0c657fb2,0x25a412cfe966fcb32e59,0xb68a5b232d7796af4b4f,0xfcb82a5bcf2ddf96e24,0xe973bcb99a5c972e3597,0x2f00976e4bafa5d532e8,0xf2d2f7697adcbcfe5e45,0xda5fc32fd297e14be7a5,0x4c156607b30209806cbf,0x8744c34a618330a1983d,0x6198a6cc4c2623931069,0x331d498df4c6ba632131,0x64e93245990ecc7de63c,0xc1265c732c699534ca2a,0x6ccdb266a93334998fcc,0x99f4ccf66678333a999c,0x4739a2c4d11268653413,0xc934d29a5c4d25e690f3,0x66ab535399a8f4d41a69,0xd7026b63359d9ac4cd5d,0x17cd84a6bfd35ea9aeac,0x29b45cd9da6cc5363e9b,0x37079b7acdb6a6d8536a,0xf1137709baa4dcee6e37,0x66701137e99be4cdea26,0x4e1fa70e738599c1c4e0,0xc724e342717938a09c46,0x6c9ca14e496722b38f89,0xd39df9ce04e6a2730f39,0x74bf3a4f9d1dce87e73f],#[0xb4275513a969d3fce9be,0x74ecce76253b049d774e,0x9dda4ee6276f13b659da,0xc439e10cf01277bd3bc8,0xb93cbb9e4fcf20a78cb3,0xe7a7d3d219e814f3d279,0xf7027b373d859eb8cf57,0x30cf8de7c473e039ef1c,0x19f6b4faf27d373e7c9f,0x18050200a0567e093ee,0xec0d000404c0703c09,0xe08c30874105b8170002,0xa0944303800682310010,0x9141190143005829101f,0x10dc106c12c0ac1218c4,0x11b04500000664c09845,0x81c2090e0c8182505047,0x41b0308824a0d8320880,0x2120e5160543b0c02c8e,0x310c0740e31485c14c2,0x5088c112130782705e84,0x613019048760083a000d,0x824424248af064781041,0xc024650546b08c140905,0x204991328c82090f001c,0x41dc312a8523c1851e19,0x607073324d6314c221c2,0xe104f421044658522ec3,0x42b44139c4d0d0d31d13,0xa1ec424d0142f833198e,0xc190f25a03402812264e,0x12103d084983e0ba194e],#[0x1345614e0a4421244987,0x4504b1621d1424280a8e,0x85f1346d1ac368d2370e,0xa2d4d640928430826916,0x803098454a8511d85986,0xe5f016ce8c21a0d33a18,0xa374aa9bb96318b57ce0,0x5f0a0f1f8478a50d6780,0xb60cdef3703d0aa6791c,0xf42f7efe38099abf9d5,0xc3d03d0a1e90eb27b817,0x43dd1a1f3d87cc0050fe,0xe4193746871f058c663,0x8aae105060a22fc1632f,0xa237ae91920c14538e84,0xf4c84f238f44190c31d4,0xa46417e8418bf420d1f8,0x912a48ea48f746871c7,0xa923a9232f4925491cf5,0x247524752465e924a923,0xe0b1d3a4929d24952475,0x9ba3439cd6225782c75,0x3d111fb1f4c8507ec99,0x6c71858add90532f4399,0xc74fc84b2122dd6c6580,0xc639776c83aad6c74986,0xbdb165621648e21632c3,0x49318427b4c20c3c858d,0xa7e3163c9b20cb8af8c9,0xc630b1d5b2c64c793641,0x7170b2149162f2e8d843,0xce1c1e246e58b58438b4],#[0xcc6db1d71858f9ec20c5,0xced24898d2164a7b083,0x3990a3a9431d4a18ea5,0xea3fd0e00a1abb62a64f,0x5d1a3033e9081f9a78c8,0xfcc050ae71365d48a693,0xa8d4f286d87d99195da7,0x4f80db38cca7943f2efa,0xcaec6e2387f06c6a7943,0xfb6f39098fa814b1a1b7,0xff8032ca2895f0710eb1,0x49a463f9044091ba3430,0x73c264321503f1fca04d,0x6413ea5b27294bd1632,0x8442948afae40c2e61fd,0xfbb684c63423f0827a5a,0x83c138025f8537ac10bd,0x5005116fc9de04283f89,0x78964df8099e59bf817d,0x8bd3121d3fff4208066,0xa0c1459cb5aa426707d5,0x3c182883ff45a1441828,0xf7f01a00033effc54102,0x927fc02a800043aaf283,0xe128428cffbf40280046,0x6b590213ff86864663f,0xdaec25183e4f209f9283,0x89499de80c197f9c8c65,0x827e21819affaa210a4b,0x721012f383a512539c2,0xf0f26b42eb27ef684a79,0x18be919aca77e04e050c],#[0x499676fe7f90475d4e81,0xc640663fe10e028cec7a,0x282fe839032d39c127f2,0xc046efea090066be4b42,0xa00aa1021f746873fdd4,0x3074ee060c5e10c1dbfe,0x27e49811451dc18377a0,0xe5cd1caae4fa90490811,0xc043195a6bf4b10110f7,0x1cd1b9e6b06a437be1c1,0xbfff81b99983f83639bd,0xa6c71fc059194512be0e,0x7032309e70607be8450c,0xaa90cc60e49a3194ddff,0x810f1dbd1999442ead3,0x2bffd13436341bfc2a49,0x8a2c585218b6fc39b19a,0x1727ea028547ff30509c,0x4e250050cefe91280286,0xcb2f2c32066198d0ddf,0x890cefa7a9488547742,0xe0b1c9e70c4527bfe023,0x7d791503305e0d202923,0x8ebc8a819b3ef0970331,0x9098f9c103fb48357082,0x504204405c9a1470f719,0xeb2cc125c4a4cefb793,0x8a402243be1f0c4c0051,0xcef03a9093e20306485f,0x1979f994084cfbc25c0c,0x1e402935c240848ebda8,0xf6a06557082c7ac10745],#[0x6f4e65021b5c24084cf3,0xcdfb548cbccd679c25a,0x990bce014183fb6a3089,0x1072ffe528028647e353,0x2477524952466a4905fa,0x1346bf1784c85352495,0xbc163dd1a1b079ffe59d,0xc26243a05f0d4d3121e,0xf8c4e811dddd08340be1,0xa9d2004227e284110cfb,0x236ff0b26ea38fbc1191,0x66671f1bdd0238f8d8d4,0xba6721935ad8e3fe0d84,0x25615597aba67219597a,0xa5617df56c25617df56c,0xa20859788dd2b0b2f11b,0xfa530319ade2526c4cef,0x1a159ff6d1a12dd85834,0xd44c9caf03ca377feca7,0x404c3e3fd4463098088a,0xb4869fd50248e6e48f94,0xcbae31067e90d8b72f01,0x20246a459cd308da27b4,0x6767ee2d9081fbfb7022,0xf6020248680fdffbc22a,0x1d7ffd180809109a83ff,0xfde0078a378c1955c9a4,0xc3010206717ddd346215,0xca1200687d60a4ad0a9f,0x59a88612ff6a342857ff,0x28999b3dac8caae2da0c,0xd8dc76d07797c41f3e02],#[0x38e0c9efcdb6c428694,0x8cd17dc009487bf841d,0x285147f2e002a56f9eb1,0xa330ffe7f0400483fe15,0x5c5b418b241ac26570ee,0xaea760c311a642f84d8d,0x814891c311a644763b06,0x48307d3e69a2209510bf,0xd54f69928f3118526337,0xee6c50a428bf62b90810,0xfe8e52e2434bc9e0090a,0xd928a1497aff40c10cfc,0xc8c50a03f0d94012341f,0x4159de9075fe45c0ca7f,0x2edf11d259bdba9062f0,0x67a0646fc9639cfd4345,0x282ac0021eda3be8b42c,0xa002433f9c86242fbff,0x98fd76c080200a267fe3,0x1ebc63b78949adff08d0,0x33f788428ec3ea202ccf,0x423990f6eb047cc98427,0x298888ced4cb22bfe0d8,0x5991ccef436911c3907c,0x3c42ed7b226d7b22776d,0x424949f51dd0a921dd36,0x32387cb0a665b7582939,0x9ba425cbfe368a17cc28,0x9e6103fedd282667c5b,0xf48b4a99a3af8f30ca4e,0xbf9f216460fc25654cc9,0x642ac617f408e944f4c8],#[0x9014b1e4c4c5233e9cc4,0xe899913cbe51335eff38,0x5878c77fca810a1bf504,0x334eb1c145b9fdd44c,0x41c81947e32322e7f817,0x6020806683fe114814c7,0xe2aad0befc555a103fff,0xf84380a36fe7de88dc07,0x9b8337fe60018010a20f,0xffcd510491d6e38325ae,0xb5e329365fbc44a2927,0x33f7f8e802d9b9f00003,0xfdb4451b2f42afa77124,0xed8fdec167fe2bba4cdb,0xbf7443329e305122a58e,0x3d540ae8567ac8e16161,0x2083edb8b6457c9c2c21,0xfa2c0a0a184f128a307e,0x4cbcd378a361b66e615b,0x266266682f9fd1331243,0x828f6100cae6a38ffffa,0x1f48c732ca4fc9a642a3,0x16afb6a0a3f3d0a7450a,0x592584b7910a9614ac8d,0x8785bc48686f842ecacf,0x6ff8a2ecfba04715490c,0x32c22376c8b46990ec12,0x308f0a8b8b796884953a,0x98bec0459533e15f4961,0x3a3dcc56950f5dbd5061,0x428cedd516bb76b71330,0x664fff19ad4cdcf429d1],#[0xc8c97cd6942b7fa46bb2,0xb8575a99fb49e3245278,0x5fd6dcc655f6d6c8c1fc,0x2810e64c9c450876ea8a,0x217a1f6dc5b2628fc85a,0x6cea60430f293f64990a,0xe1810c5afb7ac9233a37,0x1337bfe34001a1b1f04f,0x9085fda1c48cddfb7ee0,0x9c882b175ae59a9b398,0xc1216212362f7839b80d,0x462ce48d46161ed6d246,0xe8e904347f6f4d14303,0x36d0d8b392351858706c,0xf6d1d28d2ad0eef8528,0x14f0dc63303f4a0d1211,0x3d0080cf3d2157ab10ca,0x693b344cc9f04e103ffd,0x50a788d2cb8cde956058,0x484f6f0d4d981cde9508,0x20c721b1b7d83a4baae8,0x4a84283b31d72149ff66,0x91cc3627806816ce0e6f,0x4da1daf5a45a925ecf5,0x2192feb4555a1d08ff78,0x5ebb408eaf0ce46c5016,0xcbdc10b267562eb6187f,0x60d47486bff6bb646f1b,0x5ec21313c044306777ef,0x2aa10bafc524a0b08784,0xa59b1a94edd8730f4fd3,0x8fbfbdd18443417d77b1],#[0x1be77b14d9833b630ced,0xaa1693726084a4dc9821,0x77ef60caf3aea3049c1a,0x6c6cbc43033fa924b685,0x3bba55cc293a7e995508,0xc077a0f2937f46f9b23c,0xae1b47381471e3bd8d2c,0x2eb33dd52b87075f8b44,0x2267d15a4855f8d55c28,0xa929393e81905fde3684,0xc9b2133f097840336566,0x2b4fd1065267918c8ce0,0x5b8adc12bfff1245c001,0x7e0108a3afffc54a2092,0x90dfde0081fc108451e,0x869f24688d87f060e,0x1147dff804228f6fd828,0x5672872f040c841ff050,0x1104f8991590b9843719,0x4edef360797fda894308,0x3b6f59822861a4c6e842,0xcd828050d0fc993a0404,0xa00021c50c9f9118527f,0x2191977ee3091446fe8b,0x11967a226ffa28008f1f,0xa60d177ad62848f3e2ad,0x41d89a2d9f210505267e,0xd7c0b8099d0f58ff8002,0x1c9e6028c7e784301482,0xc400901f89c31949c88c,0x4695eb5fe5304843d63f,0x7d6004486ffdf99e18da],#[0x557e1d834277f908d3fc,0xd0657c28642bb64d82c8,0x8f30b1085cffc288b404,0x1399e61614a6e7f6144f,0xff7fe895402069afe7a2,0x7b088c237fe601410cf1,0x9a1f0a96990cab5b945b,0x47be7c48251dffd34991,0xb0248bf6740429dec816,0x852fc660414034cfc646,0x81a857e42846b7362c02,0x8cb0f18cbffecd16a581,0x9f3ff826d0003409c4a2,0x20429f40cb1ffc980809,0x1997ff020a0024f27d03,0xd92364a8f918cb51d568,0x76c705e3590defcc4846,0x5914014303e0808485ab,0xa7d0325acfba01021a5e,0x33a3276834f8f2c4650,0x3efd7f02832417b43ab1,0xae35830433f7eb45ab23,0x2c8ff36459ff3e0c0648,0x5f7ecea0285f7ecb2004,0x64aff4a56819bbd58a6,0x4f0b0546deac1518b4fa,0x21ad610d3fd3a0010234,0xc97db090effc841289f4,0x3f519e78d71204784ed8,0x2430f43c2810911c706e,0x8c96fed00a131f9b1590,0x33359bc700067cf4fd],#[0xcfd0fec0019ba1fd8,0xe35919f8d8c4856b378e,0x3d210f68491b10f68505,0xda50b428f6847ee6404f,0x220b9fa4126651d218bf,0x83ae3c066a53fa569260,0x46143718c6ed9360b214,0x9fe50b4299e82d477f8b,0xfa7d45123da1b7acb1b1,0xb58f2ae59a6f8125292a,0xba0199bbe36fa54081a3,0x2ed7b3044d2bc8b5227d,0x4a3eeb91123e3f185209,0x15fa29d4a350544924e1,0x842072a4c54b07918a69,0x89515c42d23af3119404,0x518c688671c3a29dea0a,0x61061feb584ca2dbd1fa,0xe7e4e811c7d2a5b23f3f,0xbfdf1f10059dde248424,0xeb42c2c9eddca832a1b,0xe6c52d0713bc88e7ec2,0x52d079790f8fa08942a1,0x1768b852878784d5086c,0xec20fbf1d249f205a01d,0x50f1eb42c2cb5c6163e7,0xe601a232a1d5f6ed1422,0x6bf53011d8ccd97292df,0x8a801a1bae21810338e,0x5a91c2bfe0680268cff8,0x5446216bd70e22669f80,0xdb35da3cff820000cfce],#[0x8b9c7a49977fe016a47,0x226dfd06c480821c677b,0xf6b535965f86c5130210,0xd54850afff946200d0f5,0xb30ad0f0776504952dfe,0x1148c67d8a930aefae08,0xbbdc1ab9b555a14cf946,0xa17cee053290de6f7060,0x2199dda2d5685379b555,0xe06b8ae4944cfdedcbeb,0x41c4cd693c52722910fe,0xa6d08c9829385251f43e,0xcbc382a96cede7097028,0x64f3213d92d908af7059,0xcfdf4b33267ec80ccadf,0x47d7d4c484effeaa8040,0x304b57f9280903e9fa05,0x4ccb853253f311890b4a,0xf4f32767ec90cb9970a6,0x70418581768f5f5107dd,0xe04849d7efc0580124d6,0x353328cbf10c0819bde,0x74ff828865ae1f0c2466,0xf6e7c08527f46a430028,0x8f884a4323fe54a442c3,0x32fe059247b75020d1fe,0x7f201190aaffd1a84014,0x4dccc8597fc92008c865,0x8c652e7f818d193040f2,0xf6ec82efda8192ef900,0x3dc04549c999fe83105,0xec603359c1280a48bb43],#[0xf4a31050c7cee404e5e3,0xf6ff185273e63210a1df,0x549301124fe055150010,0x236d0c1efc63d13c9da,0xf7f0b435bf8e285129bd,0x885a15bfe0b30d663101,0x300485faf1a04090af37,0x1fd4630bf8d1236f5fa8,0x13fc9382090c52fc1949,0x8d993ab10a3d8f885849,0xa11af94e01484b19ed08,0xea34207fd9b99949f181,0xaf814320d067be4134b0,0x30029a1445ffa2d0518d,0x467e08854e949b28be4e,0x5fa7e009219c3f2a4819,0x51af530446878bebd09,0x7e80564a1bf060846bd8,0xbc7aba4a500c39f54b34,0xa6aa085d3c5926100a67,0x80b0119c5abce7c42e3e,0x2442468c1b825085ffc,0xce5f5ff043633f7fff2,0xcc9d7ed096566f2d032,0x10f066868c98266faea0,0xcbafaa4810bcf8a91a48,0x527497e84810e9fd2024,0x3253e3a82833f27f6a06,0xfaff821b19e82d5d10a4,0xf90436330b3728114862,0xef2d01a80d04f9020ebf,0x904069d9eb1fbd00915f],#[0xcffff2805448afa7ce80,0x203f5901512343acb504,0x7f902105ea902112da8,0xff004aa43531f27810b2,0x8d725971c314804521dd,0x7ee34664333c3da690a9,0xfaca42397ff624a2467a,0x59ffa180823abb4838d7,0x3ff58400923dfbfa88c8,0x131cbab37808693dc08b,0x94955f9296342cbdbd7a,0x3547ff3f805210134d9b,0x76a49943f7ff29024002,0x5888e0ffba4e21050ed8,0x1886eb81020670a61d5a,0x2bfe4520802343bf705f,0xc65261a77a7475f5d04a,0x2ed5c943fc0a93a89a2e,0xf25c8a35dd916fd1c08a,0xd5a1141be2ea03088875,0x30ffe1414124530560ef,0x4855fff8506009176329,0x9041122cc86932a2c19b,0x33a187ff80b0000252fa,0x65fff20028867f7fd546,0xa288ed874c4196ce1014,0x707578085ab028b7ffac,0x1e20d32939f37434b85f,0xf87216e85c267e432529,0xa39b93d2d49e27ada10d,0x17993071dfa73215fe00,0x4ce354a367afa33f4886],#[0xffc4013042872fc93919,0xc1915e0041d3aa5bb088,0x5a955b377a0535a1db8e,0x427fc287230347937886,0x2f582c468ffe59160023,0x1c845f6e44affc0a2033,0x760c88f6410be0d0ede8,0xad0f6c7e336c29ad10dc,0x497e6d1ad0a493ffb841,0x2080d1aff46b4276acd6,0xa90517fd5204a13fa681,0xb5dd649ffa180823dff5,0xc84c13b41e1a3d047a97,0xbd065a961b3164273d20,0x4d6161fe461b064345b,0xa21941e980ba810c4f4f,0x54a157ffe141802437c2,0xc6fa194623f64427e6ea,0xc218d99e814052f11d60,0x3fda819230b175ea8a7a,0xfbe2643890f8e3090215,0xa9091c1881fa0c6242db,0x51990a56d8a4d0a2979b,0x40852fff90017133e3e4,0x420e888d82c08807441c,0xbbaf088026733ca3ab52,0x70f2a4859b30c2c61858,0xc87960e1fc59b2842c3f,0x5107059f5f64ceb3190e,0xc96435c06562414b1ff9,0x5468e1d13542346be55a,0x824313f171e090bbcef6],#[0xfaba6e40810e8ffad89,0xbe2d92642afffd50088e,0x845b24c8636de2c1642f,0x84d08691f1f8c2904927,0xcc244894de6312145cd8,0xf5b050dc7368518ffc67,0x9205d1a7c1828617fa9,0x8a90c80f35455fff18a2,0x42995df54902169e208f,0x560516fafe00b11fbf4e,0x45f72c48b42c24f90109,0xa7b00a38f4dcc8bfc0f6,0x255fa8168637c2ea6d0b,0xadd762f32db83f7908a,0x63778840ec85978a5443,0x27804d953b8142cadebb,0xb0692f18e7fe30a00242,0x819946f7b62c4b52a30e,0xeff3197af545067aa20d,0x9068fe05909c9e1b1a61,0x32b29f8e8b3b468857bd,0x9450dff130a656ff8985,0x70f88507e6e3212fefd8,0xbf552239589739524366,0x129bf5f246020269df6,0x4fd390802871f1f81050,0x61482447e57e18091a29,0xff88720122ac0a295ffc,0x2c0090df0c796201342,0x9709941fbe75021463fe,0x457b28e387,0x86c34c905961eb80d518],#[0xfa6231c4c2b3ca928d80,0x21423a8bb921122bf634,0xb7e5d4cccf99828467d1,0xfd66e6482c3828129113,0x9fe660a130e851436258,0xc9064a782ad874d4b28e,0x75b1062c4cfa2428445d,0xa4170218b141ff443526,0xfeb3e3e11c908b468d53,0x3351db0387428aa13546,0xc186c2d7828a1810013e,0x2e4bb32617d67b658585,0x13a31528bb06ef26c984,0xf16688a1f22644f9aed9,0xee08c6ba42a62825e221,0x3377bd11906831d72264,0x214787353ab3076f08f0,0x3e00c94f6041c7d018f7,0xc47f0471f8473c443cf,0xe11cb80906cd9c8684ee,0x751629c621dc225c2147,0x8f280332616286056b88,0x869c18b7f5e360012383,0x5303dd08a163cc18c798,0xd084486ed506af4a5808,0xab1aa468f5fcd0000d03,0x1dd78d800482a7c01927,0x9a08682341602bec21b0,0xa8b9e105cf082173410b,0x85915f082ef5ed0c8b70,0x82038144cf7c10d07b62,0x91c20b9f4829cd0b5e2],#[0x501b117c818d80b0113d,0x52db2c64b61826031e0c,0x8537679f70d0d1c21006,0x8a0d5c5742169f6944c,0x8efcea8845f808b7bf5,0xd9d44efa305094fc68c1,0x43e5c1f60822f180324,0x5e9093d18a3c189b61de,0x264297d098f18a097a42,0xc7cc5afc5322135f8bc,0x43ec5056ea0abbb3189d,0x71729291361ab0cbd82a,0x36051f07f801955c1058,0x602135f300d082f28282,0xaf10064b32122e10b1ec,0xfad28849f810c0f300a3,0x287c23bde048ef83106a,0x98d9f8201084f17ea804,0x5dda0e2c2c83b418794,0x8351ec212acf5f308b41,0x3c861e0c50f98808443c,0x1424e1f4e065008cc896,0xbc68b924bb32164c0a29,0x1fc80193d860a1c06830,0xf6a20e54a832e5c5d08d,0xdd2105e7811083ae438b,0x5c212e10a9b3014233d4,0xb0ed04036834c081dca2,0x8425c2165872c201961c,0x10f08ad820b610a2782b,0x21901e282bb3b45bd7c9,0x9da0c6b7882a377025dc],#[0x5508ae061811e210e2c2,0xed4c78e6141af4850d10,0xbe18cbe84c70d1055085,0xdd95450f9880849e1082,0x41ae109708518531f5d0,0x420d83028cc8ba2f704,0x62f5410a0faaa139870,0x82e6282a6cc05086f905,0xa54aa4d7a20b5e882e62,0x9b5e035d8f0b5f4c5271,0xdea8246dea83e4fd8889,0x951d7fe8066d7380212,0x88d080ff0004203f8201,0xb818d1d6b18ebe9895d5,0x7708a8ae083a3c75a38,0xb0ea00216bf4863a6593,0x2abdf3c1bdf345b1f21f,0x291be11406597d90834,0x2be3161207bce8fce04e,0x9c62c271279a3d2be44a,0xa3f7bcf07e702701484c,0x6c5e7432f05c084aab64,0x3ac889e5c9993316638f,0x69743a61828e5f0183d,0xc947afc8683594267103,0xbcaab130a94eae0cb654,0x5251ec57251aa5974422,0x40db50c2ff86838b0bdc,0x760db50cbf211991489d,0x44a7430f141672b31c81,0x5141a7b2639f3486b7f1,0x51c326565638a8c593df],#[0xa7d248937cd163a51071,0x53484187a4992690a690,0x9106df10c8cfa1106664,0x3f01e61129d9d93ad099,0xfc848a7c147cc58f7412,0xbdc20a011bfc0cdbf216,0xd075f4c48f4d15096c20,0xe3aa0abe98a3f18b9fa9,0x460a934f5da4a40e9d31,0x3fe4a74cbcfcd2837be6,0x92be98bbf3d8992be98a,0xa0fbe596500cd2798802,0xbd248c5fe594032f3f34,0xc4c9bd7e4899e089906e,0xcdc107b625175814415e,0xec08c817ea051a5a3452,0xe21433411bc90493c1cf,0x1413bd1058ca0bac2a29,0x538d80850bc8a297020f,0x351f58d444fb7d0c685e,0x29398251b012fa62fbd6,0xfd106e8c6e8787055e08,0xd9ec820cde4829398251,0xe0cd674267b2899e8920,0x239be2f524b04356d08a,0x750c9fcb66665137fa38,0xdfe1107b61e68f96603c,0x953a292319d199e41a8c,0xaee89ab8f27066e76c11,0xc16a3dc2ac8b24633a3c,0xa0f4c16a427f550108b7,0x15fac868742a51c17458],#[0xd2883a7d441e56563fba,0xbf268109cfee022021b1,0xdba44433688a1d79831d,0x34a10da22861b7e88650,0x441d683e1e381a05e0d7,0x1f0a83a97a7650b36577,0x63e0fad7e0661bc8028f,0xe3b16199c6f200a30f80,0x78681644c0547f033c27,0x2cd1e510c823aed023f,0x2711ab32dbc20a3e83e2,0x5824ef8af8840689b251,0xac52a85465b5472a842f,0x38c38eced84d1364a20e,0xc9eea20eac52a850b3a8,0x50d33e4c9ce74419df11,0x62d1c1089b0d31704478,0xe890a16133e4c8ca3829,0xa3e60e5941262d63241f,0x2638a0a59412381bb43a,0xc6a28f1fb5132e28e674,0x167941e3f0a0e292d8f2,0x3b244691778863d79a08,0xb83560516eec22638608,0xb2125ae304225df508b6,0x5af99132cdf0c0cda976,0x4c834183914448376484,0x18846f6042f4831f43a6,0x7e4260238443dc860fb0,0x853c4438ee31eb0ba0f,0xf9401911e8083c71410f,0xeda4b9a1002d842dc851],#[0xf70c83f2117c23970120,0x4af2f60c1d382332208,0x2c6505564515591454e5,0x555c21ae109de8824f66,0xc8938b12e1089fd07408,0x47c090cc88cc88ccc8cc,0x1f4af64207bbc643d212,0xccba021218a483c7ba08,0x41dc8c563113ee60147,0x4ed5a28f8125591454e5,0x6851f7d3145e3428ea70,0x1546d815d95443418bc,0xbb2a8a2f1a1467b1181f,0x64826c0aecaa2cd85b02,0xe988c0929f98f8d0a2a,0x8c5cd078fd88d084e482,0x90e57ba2b21cd84dc505,0x5053a170bdbb541c798a,0x56439b0d591454e505cd,0x30b8b1d143e6a8389998,0x516848fb0151f8f07165,0x51d3fcc83ed85c203f34,0x26407e2c930190d67326,0x21a16c91261e21923f6a,0xe1a2c79825704153f75d,0xe2241d845648ad84135,0x213df043627e51bbe505,0xed454f11db08222b82fc,0x3f0990bf5c2640e8c517,0x3838fd309923f4c2644e,0x1c3e11e242996e259649,0x96b8391c4377b820eda3],#[0xb08277a002c2465c18f1,0xbf0a0c3fac264cf8931d,0x9506bb42ed1894a8ca2e,0x2caa3daa101a5a200d7d,0x7e9cc69c34c686968b8f,0x6126304f2d2c8dff231b,0x74e642fa628f14c61b0c,0x82019a626033eb1522f4,0x2b36d10bca0a9fb0d07a,0xa3d7a20a6a146e245748,0xd221908e5d00a93cf402,0x6a1c307a41d7f9543267,0x83d6aa41aea13be904be,0xbc8f0065f3a94a8e1e02,0x50767c4798f263f64e0a,0x144cd380a1377b6143c0,0x75f4c58ca085ea441d59,0x3e31324d055d20a3c22c,0x5f4c42f918ad50a9c58b,0xcc8a21f886433224e2c5,0x8d8ab1b169e8b28ccc88,0xd83f3ae2ba9180c78c55,0x5a4c2d28dc9848b4389a,0x9c0efbd044a728253a1c,0x6c35fb751938f2420a90,0x79208b1874c956451002,0x13ff4800332bf0500843,0x28042d8e0d9db307ae06,0x609469ff8140019b5f70,0xc75e88c72d5041d18a4e,0xb729fcc85970120e3f40,0xc6021ad8196a82fbcaa2],#[0xa15b8621fa9808b8ab83,0x8bfc80c951b153fe0631,0xe5863e04915f80c8708,0x691d47cbc2197b3858d8,0x1c10450e76644e93264b,0x88651805b419f490d809,0xb014cfa03239f90147f7,0x517f9106042b01ecb831,0x93245e20946eff9a8808,0xad8149cc128d3db11607,0xc78c71d0318bfc5a4590,0x720422d610db8626c0bb,0x4cc84f24068426f8c70a,0x7b76a83b342450ec71eb,0x4552301effc4064a36d1,0xfc0a2c7286647703a5dc,0x31bbe104978144ee052d,0x9e3225bec111e5513795,0x8324c3a6493a11ad097,0xb7fe028042a7c331ea2e,0x2f6a63cf8c51effc4065,0xc746da261c56143d8083,0x7fe90006687b010615f0,0xcdf30a828577d3941c2,0xd99f8032237e4c64f212,0xa90640fed18f0c7ce388,0xc0a167e0431f3e608b1f,0x3c93da12bc3e66407266,0xe1e851619d217479318,0x285182e70280e39705db,0x610abc3e664dce90f0f4,0x613a2c5a74861fa40192],#[0x4fb203245d08c0ad87c0,0xe84074390d8874853c42,0x4901971d28832769a0d0,0x28f10609017235f83ef8,0xd145d0b3619d2145e34,0x3e02a8e2e850b9985c5,0xcc6cf055071742ed31c2,0x55066c182b21851822f0,0xcd88032c3643ea304cf0,0x88c64af0d02c981c763a,0x4e6821a0e70d3d202cd5,0x517423a4400065259748,0x4281c1a9e0e39320d728,0x827f6401495e6400cb17,0x299168687ac582ef142c,0xaa15889b022e89630f1e,0xc5d0b556b484e7ea741c,0x2908472e80549e7a0151,0x3acb2a42c7e3a864b721,0x96687d920a23c280805,0x923e28322f563b7fa185,0x802550b4e90e2d2c7a3,0x401ee08839fcf244e7aa,0x24d2140e0dbd5053b598,0x487a2cc268e0cbfc0c54,0x1917ab1ce90a2e852a85,0xfa62df9093f8653245f9,0xb108ed0e7e0439f3044a,0x1862c40bc166837ec818,0x1d8e1f77c7190b2d75c,0xf34467906a302bc31091,0x10da14be540424b560ae],#[0x3a20a1c65060f0341ec2,0xa830c58b36107e840425,0x5c1f50fa65777417b76,0x33a103aed764ccd895e5,0xb0862c4ae0820c58a5f2,0xcc8c2162c35862c71618,0x1f3d1935c42cdddd15b0,0xd3ddae085ab6a8a9e534,0x65129d58146cfeb4109c,0x7b8e4004319e3ec34906,0x7dffe02203348e0d381b,0xa42fcbc24400cf76a814,0x48008577c188313fb200,0x81f08e1ecf041a169f7,0xd5d94842e176899f8201,0x20d0ddd1569fa6242cde,0x7083879c20ddf082c7a4,0x6ee890ddd163f75a0e1e,0xa8a5a64c19381ceac48,0xdcd04c04708a7fa044a3,0x16b0ba0f4fe9224a4e08,0x3a680841e10978c865c3,0x3a424f964990cc8b7217,0x6d8d45d615106c30cd05,0x40e2c1d02141e2825c21,0x44e041e282078a09708,0x6a83fb98051e3dd05af7,0xb2a62849d210ae0a26b0,0x178a5322162666144e0e,0xec91a8c5c378317f8283,0x17906889cd0510ca3d92,0x7d6b51af450c3c18ad84],#[0x9840196d9a8f9fbad060,0xa8c0fad6a347713074b4,0x95da377ca0a8e94596d9,0x4180d2e11913a27ba1ab,0xe721690b56fea1910cf5,0x868307b69064e067485c,0xc5b485e72e20eda415bd,0xfb631e9d2a2cf8863a41,0x414352314253f954c84e,0x80a0f7f152217a731d31,0x7e02838b2aa51acd091f,0x9334bce82842ebfa8644,0x2e283e7aa0284c2feba0,0x84321efcf6264e788287,0x7302ed275aa0a3d7452c,0x23c2005f73630cfc18fc,0x48c5094c5045eb18cc86,0x21af190e5aa097a2870d,0x10cdc062e06782863c4,0x949c130123820bdd4a98,0x14e9085bba99092c3283,0x45f6b064f49e00426c2,0xfd8a27726f8c97685917,0x34bba31aa17d37e0a112,0x589948ced14728664770,0x864bb8a051dd9da28edd,0x4d30620a9348ba266ff6,0xaecf02211de304daf086,0x99d3bb113a20aadea6c9,0xa7b1c75d2332b423cf48,0xca257c61d324b98983ea,0xacc08400b63db44cb38d],#[0x2687d820b8d0a7c331eb,0xece83af8c3a6487b0107,0x46065c730a0ebf101931,0x4d58a9362270396168ff,0xd2061e740650fbbfa065,0xd09ca4669b9a0eaa1d04,0x9bdc3059d20c7967a199,0x328bf0085081f0fbd001,0xe18c0101a4270286fb20,0x5efa8a0d83b17b860abb,0x4c7df092032e9d0bdc30,0xba0bcd0e3dd044e04b4e,0x45704147d13199f5a2c7,0xf838f4863a3a1174d808,0x13317866313bea837235,0xd059e10c7d742c9f7fa2,0x284b7aa095c10474889c,0xb80d5ea90a9f9881f808,0xd416fe2a442f4e634d58,0x111f80a0fb1a4324d079,0xcf541033780a13dd180a,0x73d505484bdf0c7ec505,0x31c7a6e4ccbb084af041,0x282010b1f14d1099b3c3,0x41f5e10c80ff0004233f,0xb5f4c4b8425cc844ee4c,0x193bd72a0033117d280c,0x107fb22132db48c3ebc2,0x79831cfc0873e421d7d3,0xa98e4a3b3028a5b7141c,0xc678451fc80322bf4883,0x4c39a90032db351b7f4c],#[0x418f8856ea095c105f5,0x326475633306455494d9,0x70856ea08ccb468ebf20,0xc0108af04127ff140194,0x8756433d4d51a4302169,0xa21f10add4148574494,0x7afa834ff1319e9092ac,0xee01425f1169c6900a49,0x27bea11010b06e89460e,0xf110d0129c0a26756d24,0xbfdf03260726359c0449,0x84fb4109cab3a3399092,0xa46e7964c888247d3d4c,0x49bc80a3e628283eb216,0xc31a8bbf6903277ed206,0xbda51c05753476fec083,0x23d38cc9a382002bc12b,0x4819290fb0109df6c819,0x84efb640c94f7c107dfb,0x7be083efda40c9487d80,0x51071e1893ecac63c42a,0x190cc891f5048fa8287c,0x5041804cc88cc893d3e2,0xcd05cf041301e7820bdd,0xc1e76cc192d626176c30,0xec53ec2181b52e8c5d04,0x73fe5021003eb5e0ca05,0x880c94e5054bb0556051,0x104c5affa065ab2288bf,0xcd2c5db0f6c23ac21f3c,0xc7482136a5d1031d2084,0xa096a3468d80831db060],#[0xe86ac2a2806d1a340698,0x82c66fa419be9052685c,0x8cdf4831485f45214df4,0x43dedb8c86fa411be905,0xc983d669a0c2de4cc867,0x7215d107e62ee5063362,0x2d9d0a9a15e1131bb8d4,0x6f4c8019b610bbe81903,0x1c9a200ad820b3e44c6d,0x941c9a107e28a4276e0a,0xb663c66fa4191b3a2143,0x1fe63006580fcd60ca9d,0x3c0925d1778370b1e0c4,0x421b679e2c8cc4dd260e,0x8032f1c0251b5c4a21d,0xcf40c7dfbd36b23347fa,0xa0f44a7249474e976484,0x5b41e887c04397b3883d,0x210b820bbb961a328d68,0xbc4458f21bbe6881093c,0x34e044f41107de82209,0xda951c7fc124b9208357,0x5c885de82197e5e26433,0x2105c1046c1a20cd9b8,0xf41127842768c1078fc0,0x85d1fec1907fc01110f,0x87224066ee08c73e214f,0x636fe031b01b3028bbf,0xa1c0683874411ca47df4,0xd963aad1bb2433414e10,0xc8c061f310108b8422e,0x5c213b8ea0d1f5055d28],#[0xa42487cc404213d74084,0x7041b0ee33e88b5f0c47,0xe0a82e0801177e810941,0xa92f141d27d959180a82,0x4476033d2120cf887788,0xd1c1d84243cc6518f7a8,0xf80c78f7414f884b8c43,0x831b82cb8ac2afd218db,0xfe80909a07c100090d1b,0x5d0a3cba4c26bc924183,0x663704223cba4c225d0a,0xbf7055991e0f0d0e1a15,0x3e543570414f885231e8,0x48bfc322ebe601a11682,0x9cc905a82bf0c8823d44,0xd0c80798051ae10acc84,0xca0a6c9a2cec40595bca,0x8194df4883165adbc20b,0x29f2483241d0a2e42fd,0xc906929b949021c4a337,0x24aa7e43276d626fbe40,0xd054636891ff6190876e,0x6c786870d097dac1909c,0xdb0d3c8cab25f528cbee,0xb816f44c320f10a3d218,0x1ebc444de49a45375c16,0x7a287ded9032521f6282,0xde821ddee084522f190d,0xfc235e8a1c8a14fe9844,0x5a25383d3a1566150652,0xcecd8209e0e4718dd9b0,0x65249c6e6458f7f28c0c],#[0x48fb14032ac6cec4a3de,0xfd663ece01932a26bf06,0xaf1c87cf0821ccd4c8c5,0x75e0cb3d4217f6c4342,0x90b2984ed79b07868738,0x8be08b2d04043d7c200c,0x33bbb6ed0b04329183c1,0xc558fabdd19825f4bc02,0xc19be2c84a6d989085e0,0x1ec4457e6312134d29a8,0xb8f8866531e08fbe888b,0x82cfd22c8ca01af53a0c,0x7b0107a7d514d9d442e0,0xc17a8c9834f48c73bc15,0xabca6089992e140a3e49,0xc907d52f064dd7f2991,0x50077d9428457e1906ee,0xa4d141a1cba10eff0406,0x14d03ba8d3a312c7c438,0x54006622fd420330eed6,0x7c435c2163d8c04277ae,0xef88e7e04303cc028c6,0x8b0000436334127f4899,0x48ba2d84203cc028c9ff,0x2ebdc0b050a39d21ad06,0x3f6f119013383db45d14,0x7c3828407b248351f10c,0x220e3a6928cb97182a30,0xc98c1f0e0a105e504af7,0xa27be42418bf0e0a133e,0xaa01334d214708b1e1d1,0xd18a7c42c7a18509197f],#[0x309a383bc8872e0920c3,0x921334622fe398f9e480,0x4243a2883cfb26317cc4,0x417324173c848317e1c1,0x41139a0acd0f3241732,0x3268cea3afa62e648257,0xc43afa622f0c74465834,0x946386882a84afd4c627,0x95f4c4661197708642e,0xb16b3e0c47a889ef1901,0xf6a82131cebaa13662b0,0x109bf088326b9fa0425b,0x41b3f0402139ec20422e,0xc4190f308cb614042f80,0xa8ebe98abe98abe98830,0x868489fc1ec2149a33,0x2943f09dc04190d2f903,0x810916909e8fa3c98ed,0x50f92506cfc10084e7b,0xde0496383538367436d5,0x2028e1e0f2c0216b262b,0xcfc100846d857d84313c,0x1913a3145b4639745506,0x10ebe98830c41933f8d1,0x125faa0e5e86c86855f6,0x541b3e2815088eee8042,0x8af6d506497ea8324bf,0xb7a36d87a3c98ed2943f,0x58fd840842f4a032058c,0x964ccb3e421d7d316fc8,0x1f5e10c91f9d819943fe,0x206010d5f4c55f1874c8],#[0x9cf610213b808321a5f,0x834220217c020d9f8201,0x2d861fee]]
def g63H7 := limbs80 #[#[0x700044260a0008c2615,0x1a040185c00010100016,0x21a44084540009030,0xa0008805058481a09038,0xa040ac06000027402060,0x40d270a44a2a08014121,0x40e330b01402020703c1,0x800120210128046b0004,0x8f41c5304000000000,0xe020101800071f40432,0x440001000c2140088002,0x724a2e040bcf80200014,0x9814000a000000a063b8,0xa0301020080040c16160,0x8080996408330005c140,0x4346d121b80603040001,0x36c1827000105c430021,0x119f0bb78ca079a92bc2,0x464c5d6a3190d4bc06cb,0x4e31d4243060f0ba6e2b,0x8eb181aa4f9b887c1d84,0xa7e836c425956ec9aaa,0x8f0c3ac0719cd4648001,0xcb1fa6579b6ca1394156,0xb256123f49c61200000a,0x82749fab13cfbb3c44d4,0x234555095922612c472d,0x6d24594a84ee2670afd9,0x58e46600030ede9278d,0x3525ed164264000333b,0x2a7dc87f0040003046e,0x29d215011400053a000],#[0x16dea92e1218bf6000,0x884d00c8de8530d12ff0,0x891f13a2c00e9873132b,0x6cb8031ad35821b10585,0xbe202f22b98f8140000,0x42934e5ac536a1f8e79,0xd9f16ec8369521140325,0x39200000010022a3725a,0xbe0f511b383032a00003,0x4e526355271226d21e98,0xcfa8c7e83e3131c1692b,0x34f3bf6eba0dbad80001,0x8867b1783e36eb22ff0,0x53ca691c1648940082a4,0x34e705e36a4d950e0c1e,0xaebda35b4e3dc384f7c,0x1296603da7f91d649b81,0x5226869ec266a9bab,0x90ca702ab9dd2aba280,0x87a1b05b00000000001b,0xd3d0888ab9991c6891ab,0x31806e71161169a24483,0x84b0a4479c6662fb8c1a,0x60005c980971b6e45678,0x4a40001056e96fae,0x1c5f800000030cc,0x68c1c014813720280000,0x162e00016c11c2b2c,0x90000000012b0c85d665,0xdba3bb386cea88f38d46,0x8201477ed8f8280007b,0x5c440c27926c1321b],#[0x98033da01d1474b00c9e,0xd60b6000408ee7411d90,0xf0a9aa8d0972620001cf,0x8cfcdffbf12443beda27,0x8281129ef1122ac81043,0xfa3f41252f9422c0cfb4,0xe1f2a44caf146a89d602,0xe6a0f4f02a268e84930d,0x691f58708001ee13357c,0x446c511aa3a00063fa47,0x31f24d141e7207bd3502,0xbccaeab5d0df0904cfca,0xa92500010caf22112859,0x811c93b1a00006c9,0x3e8001a06e217a7e0000,0x4b8a5482ac62e05044a8,0x41f28c5fc5dac75a33f2,0x3376f33a11f048000667,0xaa65c406c0002a280006,0x18ca328400050c746f8a,0x8863b4a853b2acc90000,0x15800000050df66153c3,0x60ad722cbb770a6a0349,0x18d520c89c00001af1a3,0x44266d69a2000138c64f,0x20a9ae18a30dc0120005,0x8e5cac000007348ed104,0xe7a6451e5f215167ad8c,0xce4bbc4530001098ac61,0x1000048fe271aec69334,0x41d48ae5b000000bdc05,0x2b703700012a50000aea],#[0xebe790001018e8b0e313,0x110ca06f501a96000030,0x28bd10f2a321d200001e,0x78d95be509235cc4035e,0x1c0faba489ba418000a,0x9390e92cc6e603c3d600,0x2728834071e4a5c7289e,0x1200022f8cf620230182,0x8ed80002b88000ec801,0xe2b482529df0e5cd6033,0x417b228029600051c9,0xa6b71ea9313e44600000,0xcad2c95000080a80e363,0xa384d9a383a28cb790b6,0x8f466eaee0003ad543f8,0x83c79bb6003343325e2,0xabc82f40003bb8000000,0xb00018062b22edcc3ba,0x53022ffec300003a78a,0x7bcfce7543f8cca89800,0x74a4850720b17c22000,0x1a6223c05265aade63d8,0xa22bd15d68aeb35077a9,0xe00acc00042eb6dd5c1,0x7d9a992c2e16670b6a4d,0x169af08039b64e78a834,0x409260ed01e6a2e977e8,0xbe80b67253854e0a7aa4,0x386e549ad85a4979cc51,0xa42d011da71c1cf447e9,0x2b381ed5153adcaf8688,0x7f719045b8000212eb46],#[0xe09a4000586aebf240d4,0x60bd26a218ca6030420f,0xbc9e178000c1f8001410,0x6983083a4c8264a2e0e4,0x54192c3c00053240000c,0x80f800031ee30e2ed02e,0x4acb227690de05dbc7,0x212d1881800001a221c0,0x53a7aa]]
def g63D8 := limbs80 #[#[0x480201502014c2010c20,0x54420508205042048420,0x59020584205502054820,0x9502094c2090c2059420,0xcc820cc42098c2098820,0xd4820d4420d0820d0420,0x150301483010830d5020,0x54430508305043048430,0x58830584305503054830,0x94830908305943059030,0xd0430c84309883095030,0xd5030d4830d4430d0830,0x55032548325083215032,0x59432590325843258032,0x99432990329803295032,0xd5032d4832d0832cc832,0x148400c840d9432d9032,0x54840544404844014c40,0x90c40594405884058440,0x98c409884094c4094840,0xd4440cc840cc440c8440,0x548425084214c42d4840,0x94c42594425844258042,0x58043d484298c4298842,0x98843594435884358443,0x4845010c50108500c850,0x58850584505085050450,0x94c5090c509085059050,0xcc850cc450c845098850,0x5485210c52d0850d0450,0x59052584525805255052,0x98c529885294c5290c52],#[0x58853584535805355053,0x58454580549885359053,0xc91098c549885458854,0x14d101491010d1010910,0x1911018d101891015110,0x50510501104811019510,0x54910545105411050910,0x59510591105891055110,0x9491090d109091088110,0x98d10989109511094d10,0xcc110c81109951099110,0xd4110d0910d0110cc910,0xd9110d8910d5110d4910,0x10d20109200c920d9510,0x18d201512014d2014920,0x50520501201952019120,0x59120551205452054120,0x9492090d209092059520,0xc812098d209512094d20,0xd0520d0120cc520cc120,0xd8520d5120d4520d4120,0x109210c921d9520d9120,0x1512114d211492110d21,0x195211912118d2118121,0x90921595215912155121,0x9512194d219492190d21,0xd8121d5121c852198d21,0x149400c940d9521d9121,0x1954018d401894014d40,0x54140509405054048540,0x58540551405494054540,0x90d40909405954058940],#[0x98d409894094d4094940,0xcc940cc540c854099540,0xd5140d4940d4540d4140,0xc941d9540d8940d8540,0x189411814114d4114941,0x54941509411954118d41,0x59541589415814155141,0x94d419494190d4190941,0xcc941995419894198141,0xd8141d5141d4941d0941,0x14d4214942d9541d8941,0x90d42595425514218d42,0xd8142d514294d4294942,0x109500c950d9542d8542,0x4855018d501895010d50,0x90950545505095050550,0xcc950cc550c855090d50,0xd5150d4550d0950d0550,0xc951d9150d8950d8550,0x1815114d5110d5110951,0x549515095118d5118951,0x94d5190d519095155151,0xd5151d4951d0951cc951,0x10d52d9151d8951d8151,0xd81529495290d5218d52,0x1895418154d9152d8552,0xca10d8954d815418d54,0x14e1014a1010e1010a10,0x54a1050a104821015210,0x596105921058a1055210,0x94e1094a1090e1090a10,0xcca1098e1098a1095210],#[0xca20d5210d4a10d0a10,0x14e2014a2010e2010a20,0x55220546205062015220,0x596205922058a2058620,0x94e2094a2090e2090a20,0xcc620c822098e2095220,0xca40d5220d4620d0620,0x506404864014e4014a40,0x5524054a405464050a40,0x596405924058a4058640,0x94e4094a4090e4090a40,0xcca40cc640c864098a40,0x14e42d5240d4a40d4640,0x59242586425824255242,0x9824294e4290e4259642,0xd9642d5242d4a4298e42,0x552431964318a4318243,0x5964358a435864358243,0xd52439964398a4398243,0xd9643d8a43d8643d8243,0x14e5010e5010a500ca50,0x5865050a505065048650,0x90a50596505925058a50,0xc865098a5094e5090e50,0xd0a50d0650cca50cc650,0x582525525214e5210e52,0x90e52596525925258652,0xd4a5298e529825294e52,0x586535825355253d5252,0xd525398a535925358a53,0x98a545965458a5458254,0x1532014f2010f2098e54],#[0x50720503204872018f20,0x55320547205432050b20,0x90f20597205932058720,0x9932098f209532094f20,0xd0720d0320cc720cc320,0xd9320d5320d4320d0b20,0x1532114f2110f21d9720,0x59321583215532118f21,0xcc72198f219532159721,0x10b30d9721d9321d5321,0x1933018b301533014b30,0x50730503304873019730,0x54b30547305433050b30,0x5933058b305873055330,0x94b3090f3090b3059730,0xd0330c873098b3095330,0xd4730d4330d0b30d0730,0xd8b30d8730d5330d4b30,0x14b3110b31d9730d9330,0x1933118b311833115331,0x5533154b3150b3119731,0x597315933158b3158331,0x98b319533194b3190b31,0xd5331d4b31d0b31ccb31,0xd9731d9331d8b31d8331,0x553321533214b3210b32,0x59732593325873258332,0x993329533294b3290b32,0xd9732d9332d533299732,0x4874014f4014b400cb40,0x5874054b405474054340,0x94f4094b405974058b40],#[0xccb40cc74098f4098b40,0xcb41d4b40d4740d4340,0x54b4150b4114f4114b41,0x94b415974158b4158341,0xccb4198f4198b4194f41,0x5834214f4214b42d4b41,0x98f4294f425974258742,0x4875010f5010b500cb50,0x553505475050b5050750,0x90b505935058b5058750,0xc875098f5098b5090f50,0xd0b50d0750ccb50cc750,0x5535154b5150b510cb51,0x90b515935158b5158351,0xccb5198f5198b5194f51,0x59352587525835210f52,0x587545835498f5290f52,0xe5f1f98f5498b5458b54,0x5f6f777b7d7e7f3e9dcd,0xddedf5fabcfe77377fbf,0xeff77b7d7dfeeeff7dbd,0x3bffff7f7f9fbfd7dfed,0x4f01ba93a0ee84e84399,0x93c10e64f07b913c18e4,0x64f87b913e18e44f81ba,0x9c2e26ec0183ba13e10e,0xe90c0539c3002eb0b853,0x399c474a63504399fa0a,0x2ea201a312a680c48b04,0x1bb0ee0eec2b02ba0820,0x98c44a95b892a06eae30,0xbf2112b0aa24ac2a092a],#[0x10aa25042a0940f8c44a,0x5a7b115452e255173b14,0x5a8ec84b15b892c90c65,0x4c8abb15a8ec85694b89,0x95ebaa25795b8932baa2,0x4bc23812e7eca5794b8,0x212ed6844bb4a112f0ee,0xea4b94ba92ed6c84bb43,0xa91350ee04d423813456,0xca64d2e29934bea44d2e,0x5ba134bea84d2eaa134b,0x5ae045afb2934b8ca4d1,0xa4319169ec44594b8916,0x898c4560b3b1162aec45,0x616b81182cec560abb15,0x188ec84627b111852e24,0x4c0a3b1302cec460abb1,0x1428ec85096b81422eec,0x45714b895c2cec508abb,0xb15c34ea570cba95c98c,0xe24716b811c2cec570ab,0xbb11c7eca4727b111c52,0xeec4d8a3b1362cec470a,0xb3b1462aec5196b81462,0x2aec58263116052e2580,0x8b399229ac4488b3b160,0xa40e64e97b813a2ae848,0xe8c3a93a3ee84e8e3a13,0x3a28e64e8bb813a36ea4,0x530b3994c9ec4530bba1,0x11a2ae8590b399642ae8,0x846a43191a52e24696b8],#[0x21442cec468abb11a8ec,0xec510abb14428ec5123b,0xb891e5ae0478bbb1442c,0xaec479fb291e90c64794,0xb3b1482aec520b3b11e2,0x2ae8538aba12494c6490,0x1fb29208ec84814b8920,0x828ec4e0b3b1202aec48,0x28abb14a52e2528bbb13,0x6252e25896b81622cec5,0x588abb1627aca58a3b21,0x92632ea49a2b21262cec,0x44f17b813c2cec498d3a,0x213c40e64f13b913c48e,0xe04f0dba93c30ea4f23b,0x3913ca6e24f0bb813cae,0x8e64f243993c9ee44f26,0xfba93c78ea4f25b993c2,0x2ce659a3b21505ae0541,0x923913e5ee04f9eb2928,0xe38e84f903993e4ee44f,0xf8a3993e2ee04f8fba13,0x682ce65a1fb29522ee84,0xb596b82d6fc84b88aba1,0x2d85ae0b60abb2fe2aec,0xbc0bbb2e49cc4b90abb,0xab002aecbc26b12f05ae,0xe0b70abb30034eac00cb,0xb82f42eecb98abb2dc5a,0x8e6ba8abb3022aecbd16,0xaba2fa2ce6be8bba2ea2,0x94c6bc8abb2da5ae0b68],#[0x96b82de2eecbc8abb2f2,0x82aecb80abb2f62aecb7,0x116b83042aecbe0bbb2e,0xee28e6bb0abb3047acac,0x90bbb0082ee8bb8a39a,0xaa2c2028bbb02494c6,0xc028abb00a8ac80293b9,0x80e2aec0a22b20282ee,0xe6050bbb00e4ee403a8b,0x3100c2aec098bba01428,0x4ea0a8cba82a2eec0327,0xabb02e2eec040abb02a3,0x2ae8080b398202ae2080,0x8abb01a94c6068abb000,0xc94c6070abb0022eec06,0x4a2b20122aec010abb01,0x302aec07a2b201e2eec0,0x58bb88162aec0c1eb28,0x9982ee8060a3981828e6,0x46723b217c48e45f2431,0x91802cec6723b219c4ce,0xec681fb29a04ce468123,0x3b17e28ec66a9b099a2c,0xcec67933919e2cec5f8a,0xb3b16c4ce45b0a3b1822,0x4cec62a73b18a2cec628,0x933916e2cec638b3b170,0xc8ec8630b3b16e8ec85b,0xc93391722cec630a3b18,0x762cec640b3b1727eca5,0x650ab81942ae85d8ab89,0x1842cec5d13391742ae8],#[0x864933919228ec6123b2,0xb1a47eca690b3b1928ec,0xe6618bb81862cec5e0b3,0xb81882ce66a0ab89a828,0xce66a8bba18828e6620b,0xbbb32ea2c2cb8aba1aa2,0x2aecc49239312a2c2c48,0x28b0b142aeccc0bbb312,0xa2aecc18bbb31448e4c5,0x8a531b222aecc28a39b1,0xe7acac38bbb3222aecc,0xc58abb3102aecc98abb3,0x3347acacd0abb3282eec,0x6c78a39b1c2ee2c70abb,0x940494c7080bba31e28e,0xc90912b94248ac90113b,0xb2c2a4ae50a93b940a8a,0xeed08a531c222eed009e,0xabb4068ac901b2a14062,0x4ae509b2a14262eed018,0xbbb40c2aed09a2b2426,0x89eed020bba41028e704,0xe8d3ac2832eb0a13bb40,0xfa8ac8fea531bfa4ae4f,0x58abb4168ac9058abb3,0xbfc94c6ff12b93fc2eed,0x1000abb4182aecff1eb2,0x8c1c2ae9000ab8c002ae,0xc8ff92b93fe2ae9070ab,0xbb40e2aecff9eb2bfe8a,0xac90b0abb41a4ae5068b,0xbb8c122aed0b1fb2c2c8],#[0x34eb078cbac1e28e7048,0xa39c142ce70b8ab8c2e,0x82ae90c0b39c302ee905,0xe10398389cc40e28b083,0x3a40e60ea8b083a2eec0,0x158bbb03a2aec0ea2b20,0x83ea2c20f8abb0568ac8,0xc0c8bba0442eec0f9039,0x203c9cc40f17b803c2ae,0xe61326b104c2eec0f22b,0xba8588ac8160abb04c44,0xaec0d0abb05834ea160c,0x6b104e2eec1027310402,0x7aca170abb04e44e613a,0x8ab88522ee8118abb05c,0x25ee0108abb0362ae814,0x40bbb0428ac810903984,0x5e7aca178abb0508ac81,0x170bba04a2ee2120abb0,0xc622ced1f9139c7e40e7,0xd178a3b45a44e7211039,0xb4642ced201139c8028e,0xed139139c4e2ee91a8a3,0x3b47228ed1817b84602c,0x4eb208cbac8244e7208b,0xb3b45044e7140b3b4823,0x2ced220b3b47628ed198,0x8ab8c7a2ee91b16b8454,0x4eae11d16b848e2ae91e,0xa0b3b45244e714bb3847,0x7844e71e0a3b4685ee11,0x158b3b48a7ecb228b3b4],#[0x4905ae1240bb8c6e5ae1,0x7240ab8c902ae1242ab8,0x84922ee91c16b845894e,0xc2228aba4922ae12496b,0xba08a94c622a73108aa2,0xeec229f3288a7aca228f,0xeb28a094c62828b08a02,0x9ac428a8b08a27cca281,0x9eb28a294c628a7310a2,0xca2c2230bbb0a27cca28,0x3253188c9cc42326b108,0xa6a2c2298bbb08c3ee82,0x2425318a69cc429a6b10,0x90a66424281909028e6,0x4242929090a2a4242829,0x9090a2e4242839090a6a,0xa6242829890a6e424293,0x3a890a4e6242839890a4,0x6ea24293a890a2ea2428,0xeb288494c62126b1084a,0x9cc4290abb0847cca211,0x1f328a47aca2925318a4,0x694c621a6b10862aec29,0x3a73108e2aec219eb288,0x989ac4260bbb08e94c62,0x2a0abb0983ae82625318,0x8a83ae82a25318a89cc4,0x6248a398922aec2a1eb2,0xa89298e624a72989298a,0xe6270ab889c9eea24a63,0x2989c98a62726b889c2c,0xcea2726ba89c9ce62727],#[0xeb288894c62222bb0969,0x2aec26a53189a2aec221,0xa5b909e90e427a5b889e,0x428e62525ba89e90ea27,0xb9e398947ee4251e3909,0xe87eca840eba2103ee87,0x7a8a3b20c2eec7a0a3b1,0x1f028ec7c29b09ea5ee0,0x67d93b91f648e47d8bbb,0x9a1836ea7d8c3a9f640e,0xec770abb1dc3ae8770b3,0x3b20e2aec83a431a0e2c,0xae07f26311ec5ee07b0b,0xabb1de3ae877a7b11fc5,0x2eec7c8a3b1f22cec778,0x1fb2a142cec800abb200,0x29ac4788b3b2142aec85,0x127b12042ce6788ab89e,0x1a34ea810cbaa0444e68,0x7824319fe5ae07f8b39a,0x1e07eca780eba1e090c6,0xc808abb2022cec780abb,0x82165ee07d0ab89e42ce,0xe67e9eb29e67eca8596b,0xba1fa28e67e8bb81fa40,0xee8cf0b39a1c7eca820b,0x7b833e2eecd70bbb33c3,0x3ee8d0a8b0b42a2c2cf9,0x8abb33628e6d20bbb342,0x9cc4d017b83402aecd7,0x10abb3389ac4d416b835,0x622aecd50eba3542eecd],#[0xd60a39b4a2aecd88eba3,0xb525ae0d48b39b582ae2,0xcd58abb33adae0d4a531,0x2b645ae0d917b83462ae,0xe6d38a39b4c2ee2d31eb,0xb2d083ae9420fba4f028,0xeed3c8bbb5042eed3b9e,0xabb4e83ae93a0a39cf62,0x7acb3a8eba4ea2aed418,0xabb4fc2eed3d0abb4ea,0x2ae3400a39cf82aed43,0xb1eb2cec3ae93b0b39d0,0xfa2ae3408abb4fe2aed3,0x338dba8cea2c2338a39c,0xe4a2c23928b08e22eec,0xc340dba8d0a2c2340bbb,0xb0e8a2c23a0bbb0d02ae,0xe8350a398d47ca6350ab,0x210d4a6643528190d42e,0x6843529210d4a2843528,0x9390d4a2e43528390d4a,0xa4863528218d4a6e4352,0x283a0d4a4e63528398d4,0x8a6e835293a0d4a2e835,0x28abb0e694c6398abb0c,0xd28ac834a7310d22aec3,0x368cba8da9ac4368bbb0,0xea32ea3aa2b20ea2aec,0x2380bba0d628e6358abb,0xa0e02ce6381f298e02ae,0xec3725318dc2aec330ab,0xbb0de7ac8378bbb0dc2a],#[0x8ec9d8a398d82ee2361e,0xb3b27828ec9e0a3b2842,0x7ec89f1e31a7c2ceca20,0x1fb228c78c6a30dba27c,0x690c6a18b3b26c7ea8a4,0xea3b227a2cec9b8b3b28,0x8a8ec8a28b3b27e28ec9,0x9c8b39a722ae29c8b3b2,0xa922ae89c9faa2727aa8,0x89c2431a702ae8a48b39,0xb2808ec8a00b3b2708ec,0xa89d0ab8a742ceca00a3,0xb8a8e2ae89d1faa2747a,0xce6a50ab8a9434eca38c,0x8b0baa2eecf00bbb3a82,0x2aecf10bbb3aa2aeceaa,0x8abb3c22aece81e29bae,0x62eeceb27313ac2aece8,0xc0abb3c62aeceda6b13b,0xbc2ae2ef0bba3b028e6e,0xef0b39bbc7ca6ef1e29b,0x3b894c6ee0abb3a42ae8,0x8ee9eb23a62eecee0abb,0x9bb428e6ec8bb8bb27ac,0xc9500bbb5582eed4f8a3,0xbb5402aed500cbad408a,0xaed570cbad5c8ac9570b,0xdba5447ac9511f31d442,0x7aa9520a39d487eed510,0x8abb53832eb4e0bba548,0xa32eb4ea2b253a2aed56,0x3a2b254e2eed508abb53],#[0x4a2aed578cbad5e2aed5,0x548ab8d522ee9528a39d,0x53c2ae9549eaa5522ce7,0x9540abb53c32eb4f22b2,0x8d542eed540abb5508ac,0xe3518aba5547aa9550ab,0x39d4c2ee3531fbb54636,0xc6748aba1d62ce6758a,0xb3b1ca2cec718b3b1aea,0x90c6720b3b1b04ce46c0,0x13391b42cec720a3b1c8,0xc2cec6d1fb29b490c66d,0x40aba1ba2ae06e8b3b1c,0xc02cec6d8aba1d02ae07,0x751fb29d42cec738a3b1,0x9c22ee0708b3b1bc2cec,0x710b399d82ae0760a39,0x81da2ee8710a399c42ee,0xe70f0aba1da2ce6768ab,0xb84387ecb0d0bba43c28,0xae9110ab84442ae90e0a,0xa39c3e2ee10f9fb2c482,0x2ee1100b39c4a2ae1128,0xab844c2ee9100a39c40,0xa52e3268aba44c2ce713,0xbba4a82ced269139c9,0xa22ced251139c9444e73,0x2c1139cb028ed2895b8c,0xcba32eb2e94b8cba2ced,0xd259139c962ced2e8d3a,0x9cb228ed2915b8ca42ce,0xed2f14b8cbc2ced2c913],#[0xba4aa2ee12a94b8c9c2c,0x2e3308aba4b62ae12d8b,0xa3b4a62ced261139cc25,0x2ced2f9fb2cbe2ced2d0,0xb3b49e44e72794b8c9e,0x444e73114b8cc42ee12b,0x82539cc4a2e3310ab84c,0xc62ee92b8bb84ae52e32,0x318ab84c644e73194b8c,0xa2432ea892ab02242ae9,0x68c93b923248e48c8d3a,0xaa3230ea8c8fba23240e,0xe6938eba240aec0900db,0x3b21e2aec878eba21e2c,0x6e28b0b3b2462aec918b,0x4b8a38c8c48b263122c5,0x3ae8880f3b2489ec48e1,0x8a3b22e2cec880abb220,0xc2aec8f0eba23c2eec8b,0x98b3b24a2aec928b3b23,0x342ce6898ab82269ac48,0x940ab82509ec4908fba2,0x22290c68e94b8a3a2ce6,0xc888abb2227aca888eba,0x82282cec8f8abb23e2ce,0xca9314b8a4c56e28c0ab,0xb82363ee88d9eb2a2a7e,0xeca910bba23628e68d8b,0xa39d182ce6948ab82527,0x3ae943a531d0e9ac5438,0xabb5269cc5498abb50e,0x7acb440eba5109ac544],#[0x78eba51e2eed458abb51,0x1a2aed4a27315282aed4,0x488ab852228e7468bb85,0xd123ae944a531d122ce7,0x1490abb5202aed449eb2,0x9ab828e7470bb851c2ae,0xe8ae1faa2b87aa8ae0b3,0x3b29690c6a5a7b12962a,0xceca60b3b2b098c4ac0b,0x7b12aa28eca926312a42,0x36e0a98b3b2b22cecaaa,0xcb82b436e8a98c39aa6,0x34ecad0cba2b434e6ad,0x81f29aa078a6a80ab82a,0xa07ea8a81eaa2a02ce6a,0xae8b39aba2ae0ae8aba2,0x2ac90c6ab0b3b29a2ae8,0x8a70cb829c2cecab0a3b,0x22ae32e0ab8cba29c7ec,0xa8a88ab82a232e8ab9fb,0xb82a82ae8a89faa2a27a,0x4e6ad8cb82b630e6aa0d,0xb39abc2ae0af0d3b2b63,0x36e1590bba56828e75a0,0x8bb856a36e9590c39d64,0x22ae15c8bba56a28e75a,0xc0cb85702ae95c8b39d7,0x662ae95d0ab857432e95,0x5b0bb856c30e7598db85,0x6a2ee81a0bb886828e7,0xa1e8bbb0622ee81a8bb8,0xb0642aec1e8d3a87a32e],#[0xca1822b20602aec1f0bb,0xbb0702eec198abb0607a,0xaec1f9fb287e8ac81f8a,0xcba8742ee21b0bb806c2,0x2ae0200abb07434ea1d0,0x8bba06e2ee01b8ab8880,0x2ee3340aba0822ae020,0x28abb4d82aed320bba4d,0xce2aed330abb4da2aed3,0x371139cdc2eed33a2b24,0xce244e7388abb4dc8ac9,0x3350bb84d42aed389eb2,0x84d62ae1390abb4de2ee,0xe9398ab84e62ee9358bb,0xb80b228e62c0bb88b02a,0xaec2f0bbb0ae28e62c8b,0x2b90aa2ce62e0ab88b82,0x7aca2a8eba0aa94c62a9,0x8ab80ba2aec2d8abb0aa,0x628e62d0bb80b42ae22e,0x80b3b2542ce6998ab8a6,0x5690c697933925e2cec9,0x9893392622cec959fb2a,0xa582ae0960b3b2623ae8,0xa99133926448e4968ab8,0x9a5c2ee0970b3b2647ec,0xe69a8ab826a2ee8970a3,0xb836c28e6da8bb8b6a2c,0x4c6dc92b937228e6db0b,0xabb3667ecad98eba3669,0x2aecdd2531b744ae4dd0,0x13b93682ae2de0ab8378],#[0x28e6db9eb2b7c4ae4df,0xf8ab837e28e6dc0bb837,0x2a28e74b8bb8d2e2ce6d,0x4b1eb2d2c4ce54b1eb2d,0x5362aed4d0eba5342aed,0x74c8bb85322ae34d8ab8,0x9d327ee14c9e3853228e,0xa83c8a398f22ee23c9e3,0x298f42ee03d0bba0f27a,0xee83d1eaa0f428e63d1f,0xb398fc36e83b8c398ee2,0x8ac83b25318ec4ae43b0,0x22b20f82aec3b0cba8ec,0xa2eec3e0abb0f836ea3e,0xf9ebb0fa32e83e9eb20f,0xfe7aa83f8ab88fe2ae03,0x3d9fbb0f030e63c0aba0,0xac628e63d8bb88f62ee0,0x6b10aba2c62ce6b18ab8,0x92c22cecaf9fb22c478c,0xe0b00b3b2c228ecb0933,0xb82ca2ae8b00ab8ac02a,0xee2f38b39aca2ae2b28a,0xfaa3ce7aa8f38a39bce2,0x7ea8f41e29bd02ee8f39,0x8abb3c832e8f78d39bde,0x62aecf5a531bd64ae4f5,0x28cba3ca7ac8f28bbb3d,0xdc32e8f61eb23d832ecf,0xf71eaa3dc2ae2f70ab83,0xbe030e6f30aba3dc7ea8,0x2f48bb83d232ecf80d39],#[0x8d7a28e6f50a39bd22ee,0xe55e0bba57a28e75e8bb,0xbb58032eb600abb5784c,0xae3608ab85822eed600a,0xbb8d7e2ee15f8aba5822,0x2ee0300bb88be28e75f8,0xab88c62ae0318bb80c2,0x83ae8e02ab03802ee031,0x8bb838aaec0e40bb8b8,0x8232eae08eba3829ac4e,0xe30dbab8c30eae30d3ab,0xb922ae0e4a7b13922ee0,0x6e59039b863ae8e70ab8,0x93844ae4e11eb2b9644e,0xe0e39eb2b843ae8e1133,0xb839e3ae8e79fb2b942e,0xaa8408bb89022ae8e78a,0xeaa1042ee0410bba1027,0x2ee8418bb81062ee8411,0x9eaa10a2ae2428ab810a,0x30e4400db89002ae842,0x90bb89082ee0421fbb10,0xe47ea8f91eaa3e42ee2f,0xfa0bb83e87ea8f98bba3,0x3ec2ae2fb0ab83ec2ee8,0x4f88aba3ec7ea8fb1eaa,0xb3ee34e4fb8cb8bee30e,0xe2430bb8bea2ee0fa8cb,0x3990e2ee0438a3990c2e,0xae0448a399102ee0440a,0xab81142ce6448ab89122,0x2ae2b494b8acc2ae2450],#[0x8ab8ace2ae0b38b39ad2,0x2ce6b50ab82d42ce6b3,0xc0bb8bf02ae2b40ab82d,0xf628e6fc8bb83f228e6f,0xfe0b39bf62ae2fd8ab83,0xd8428e6fd0ab8bf82ae0,0x7618bb858628e7610bb8,0x858a28e7620bb858828e,0xe1630b39d8a2ae3628ab,0x3992ab0c64a8ab8d8c2a,0x8c64ac72992b1c864a98,0x7299411c865046219411,0x1ca85046aa14118c6504,0x2c319551ec8504632141,0xcb6c455ac3115664e655,0xb2c3192cb6c44b2c3112,0x5ab0c656adb115a60e64,0x4cadb1132b0c44c99399,0x95eb0c6579839932b0c6,0x44d443192f16644b9939,0x211710e64d4431935166,0xc856403115862e845adb,0xb295862e8562db2158b2,0xc646193b158b6ca562c,0xd31930b0c64c1939918b,0xb0c650983b13060e64c2,0x193995cb0c6571939942,0x664e6472c3191cc4a647,0x19939946b0c651ac3193,0x2264e6582c3196062e85,0x48adb212264e648ac319,0x93ab0c64eacaa12262e8],#[0x6532d2993ab4864e9839,0x2164b0c659193994cb0c,0x86592c21964b6c8592c3,0x2a164b2a8592d29964b4,0xec5139b2144e0c8512d,0x8ba148c6a852193b1446,0xb0c849193b148c0ca521,0x2db2124b4c8492cb2124,0x4b2ca492c3292462e849,0x92c39124b6ca492d3292,0x24b6e4492d39124b2e44,0x492d2a124b2a8492c2a1,0x124b2e8492c3a124b6a8,0xa492c3a924b6e8492d3a,0x9920b6ea492d3a924b2e,0xe649993996264e652993,0x39950b0e64f183993c64,0x4e654983993e64e64a19,0x6aa2e31ca6b8c721ae26,0xb2cabfacb22feb2c8b5c,0x1839ae4b4c6b91939ad8,0xc64e6c01939af0b4c6bc,0x71939adcb4c6b73129ad,0xf4b4c6b9acb22dcc2a8b,0xc0ad31b0264e6bd2d31a,0xaeab486baacb230264e6,0x8b7acaa2fab2a8baad29,0xa2fcb2a8bf2cb22dec2a,0xe6c11939af860e6ba2da,0x39aecb6e4bb2c392ec64,0xe6022d318091aa801ac,0xd3180ab2c8092cb20086],#[0x60e603ad3180e60e602a,0x2c21814b2c80b30aa02c,0x4b0e6052d29814b48605,0x52c3a014b4a8052caa01,0xb2c80bacb282ab6e80,0x8acb2002c2a800acb28,0x996b0c6659839812b2a8,0x667183997cb0c65f1939,0x9980b0c660193999cb0c,0x846699399a0b0c668183,0xba19a62e866adb219b04,0xc65f99ba99a62ea6699,0x93999eb0c66798ba97eb,0xb0c660b129982c0a6609,0xb1aa182c2a8609839982,0x2c4a668ac3b18266e860,0x9ad219a664e668ac319a,0x6ab6c85aacaa1a6b4a66,0x5b18ba96ab6ca5a98ba1,0x98ab0c662993996cb0c6,0x662c0b898a62ea629939,0x997104ec62c13998b00c,0xa6639939970b0c65c312,0x3998eb0c663b12998ec0,0x2e863b1aa18ec2a86399,0x9b218ce0c86318b898c6,0x60ec6319ba98c62ea633,0x18b899062e25c993b18c,0x62e86431aa190c2a864,0x4183b190c6ca64303299,0x76b6c85dac3217664ec6,0x5dadb2976b0ca5d98ba1],#[0x976b2e25dadb817662ea,0x85dacaa176b0a85dadb8,0xa176b0e85dadaa176b4a,0xea5dadba176b4e85dacb,0xba976b4ea5dacba976b0,0x2e269193999264e65d2d,0x93997a64e65e19399a46,0xb4c6c4acb232f1aa8cb1,0x1939b30b4c6cc1839b12,0x260e6c52d31b14c0a6c5,0xc9939b32b4c6ccb129b3,0x18b086c62cb2332c2a8c,0xc62caa318b4a6c62d21b,0xb08b2cac1acb2306b4a8,0x6c82cb2b0864e6c22d31,0x1b0cc4a6c31939b20b4c,0xc8c330aa30c64e6c32d3,0x39b24b4c6c93029b24b2,0x2e2c2ad29b1ab486c699,0x8b8b0e62e2c8acb2b0a6,0x62e2c9acb230ec2a8c39,0xad2a32ab2a8caac2a32a,0x860e6c599b8b16b6a8ca,0xd18b8b3464e6ca18b8b2,0x4b0e6c72db8b1c64e6c,0x2ad31c0a60e7012d31c,0x40260e700ad31c0260e7,0x908c0a142266e900acb2,0x9c0cb4c70198ba422b2c,0xa9031839c0cb4c703312,0x21c10b4c70419ba40cc2,0x6eb05acaa410b4a7042d],#[0xdb8c1cb6e10730aa4186,0xf0e60e4590838b2a9072,0xacb2054b6ec0e2cb2038,0x666e40e983903ae6840e,0xf993905662e415b8a105,0x5a66e40f983903ec6a40,0x16993905a62e416b0a90,0x44b284112cb205ac2a8,0x8112d2a044b2a8112da1,0x103262e20cadba044b0e,0xe21319b883cb2ca0cb8a,0xb285862e21639a104c62,0x2a80d30a903462e20d2c,0x8b884e66e2102cb2034c,0xb2c81718b885cc6a4139,0xad2a046b2a811ac2a046,0x266e210acaa052b6a811,0x418b885066e410983904,0x5e62e217993905062e41,0x122db884864e41798b90,0x45c60e5172db9048b0e4,0x518993947e62e51f99b9,0x948462e52119b946260e,0xc916bd21c5b164316993,0xba45a62e916adb245ab2,0xed1699bac5a62eb1699,0xcb247cf4871f2dbb45ab,0x66e91f18ba47cb6c91f2,0xb8a145e66eb1f18bac7c,0x62e52038a148062eb17,0x931a9464c2a519193948,0x64c2a91919b946460e51],#[0x192c3b46466e91931aa4,0x48662e521b0a9486b6ed,0x5232caa46ab2851a9939,0x944ee28513993948c62e,0xeb18392146066e318193,0xa147262e31c99bac6062,0x6eb1c98bac7262e91cb9,0x8b8c50b4ed1cacbb4726,0x66e3199939450c2a5141,0x98b8c7666e919b129466,0x6c6a91db0aa476c6a51d,0xdacbb47662eb1d98ba47,0x6cb0a91b18b8c88b4ed1,0x1eadaa46cb4a91b2caa4,0x474f2e51d3cb8c74b2a9,0x51e193945262e514bd39,0x948a62e322993947862e,0xe51598b945664e52298b,0xb949064e52418b949064,0x4e51618b9458b4e5242c,0x92188a64e52498b94926,0x64e622983988ab4c622b,0xbd990a2b6ec22b9ba08a,0xc66e42331a908c62e428,0x9983988cb4c623302988,0x90b6642418b90a6c2a42,0x292cb288462e2212d298,0x88e66e22398b8886b2ca,0x22a18b889860e623ad31,0x8888b4a624ac2989262e,0xc47bac311ee62e42218b,0x319ee66e47b98391eeb6],#[0xc6842db121060e67bac,0x8399e8b0c67a45909e8b,0x60ec7a2c3b1e864e67a1,0xc598a0ab6ec7a193b1e8,0xa64e6829839a0ab0c682,0x33d9920c64ec82983b20,0xc60ec83193920c62e48,0x7c31a91f0b0c67a993b2,0x9f0c0a67c19b91f060e4,0x484b0a921260e67c2c31,0x1a12c4a684993921262e,0xe47dadb11f664e684ac3,0x399f6b0c67d99b91f660,0x6ca862c31a18b6c48618,0xd21a18b284862d99218b,0x62e2772caa218b4a6862,0x393a1dce2e8773d991dc,0xc60ec772db29dcb2ca77,0x3993b1dcb4ec772cbb1d,0xeb2ca83bc31a0e62e28,0x7b193b20e60ec83adb2a,0x9fc60e67b2c319ec66e2,0x27799399fcb0c67f18b8,0x19dec4a677b0a91de62e,0xc67c99b89f264e677ac3,0xa920062e28018399f2b0,0x4e6802c31a00c0a68031,0x939a14b0c68518b8a146,0xb6c478acb11e262e2789,0x99399e2b4c678ac319e2,0x264ec78adb29e2b2ca78,0xe2c319f8b2a878aca01e],#[0x4b0c6812db120460e67,0x86ac31a1a62e2869939a,0xa1ab0ca869939a1ab4c6,0x686adb2a1ab4ca86acb2,0xa21ab4a686ac29a1ab48,0xe47f98b89feb6a886aca,0xb91e062e27819391fe62,0x2e48098b8a0264e47818,0x8b91e462e27919392026,0xb2ca792c329e464e4791,0x2cb89e4b6ca792d329e4,0x4b2e4792c391e4b6e279,0x92caa1e4b6e4792d391e,0xe4b2ea792c3a9e4b6a87,0x8198b9206b6ea792d3a9,0x21662e48598b8a1664e4,0x47e98391fa64e6859939,0x920862e48218399fa66e,0x86cf4590b3c64e682193,0x39b3cb4c6cf3921b3ce0,0xe8cf2cb233c64e6cf18,0x598b5ab6eccf39ba33ce,0xb4c6d6b921b5ae086d6c,0x2cb235a64e6d69839b5a,0xc64e4d718b935cf664d7,0x9839342c6a4d0acb235,0x42c0a6d0b821b4266e4d,0xd830a936060e6d0ad31b,0xb60e486d8193936062e4,0x4d22d9934864e6d83129,0x9b48b4a6d22d21b48b28,0xc8cdbd9933662e2cdac3],#[0xb8b5eb2eccdacb2b36b2,0x6e2d02cb2b5eb2c8d798,0x8b8b5060e6d02d31b406,0x62e2ce1939b50b4c6d41,0x3129b38e486ce30a9338,0x4e086d119b8b4464e6ce,0x518b8b5460e6d12d31b4,0x54c0a6d53821b54c6a4d,0xd898b8b6264e6d52d31b,0xb4ab486d29939b62e486,0x4d498b935262e2d4ad29,0x9352e2e4d4b8b8b5264e,0xe4ce98b933a62e2ceb93,0x3935662e4d598b8b5664,0x4e4d918b936462e2d919,0x9b94f0b0e6d31939b646,0x60e73bad31cee60e73c1,0x3d99504b6ed3b9939cee,0x266e53cb1a94f262e541,0x2b0a950a60e73cb029cf,0xe862e33a2d994f662e54,0x3d18b8ceab2cb41acb2c,0xd0c62e33f1839cf466e3,0x53b18b8cecb0a73e18b8,0x98ceb4c633b1298ce62e,0xc8392cb20e2b2c833983,0x990d460e6342d318d0b2,0x86352da10d4b284352d,0xc3a0d4b0e6352d218d4b,0xb2c839acb20c8b6e8352,0xac218d660e634ad318d2,0x716429d98b90ccb48635],#[0xd9939a7660e69dac31a7,0x82b0ec9dadb2276c6a89,0xa09839a82b0c6a0c598a,0x284b6c8a0b1aa28264e6,0x8a1193928462e4a13d99,0x1288b0c69e2db2284c6a,0xc6a2193928862e4a238a,0x9927cc0649f1939a88b0,0x284a3319928cc064a331,0xd99290c486a3312128cc,0x62e29b2d21a90b284a42,0x31aa26cc2a89b3d9926c,0xcc4ea9b30baa6cb6c89b,0xb2d3b26cb2ec9b183b26,0x86f0c6a198b8a8664ec9,0xa1adb2286c6a8a1b0aa2,0xa6ee2849b993b28660ec,0x69e99b8a7a64e69bac31,0x127e62e29f9839a7ab0c,0xc6a29939a7eb0c69fb9a,0x31a72b6c49c9939a8ab0,0x6c89cb1aa27264e69cac,0x1aa29264e6a4ac31a92b,0xb086a4adb2292b0c8a4b,0x193927062e49c2d21a92,0x464e4a018b928062e2a0,0xd31aa27464e49d18b927,0x74b2e29d2db2274b0c89,0x9d2cb9274b0e49d2db8a,0x274b0e89d2db9274b4e4,0x2ea2dba274b4e89d2cba,0x9ba8b4c6ea3029ba9164],#[0xeaea2cb23a864e6ea183,0x29bbf1662efadbb3a8c0,0x4e6ef9839bbeb4c6efb0,0x8b93c0f664f02cb23be6,0xe684eaacb23c064e4f01,0xb029baa66e4ea98393aa,0x4e284f11839baab4c6ea,0xb9939bc464e4f118b93c,0xa0b486ebaca13aeb664e,0xe82cb23a0f664e818b8b,0x3c262e2f0acbb3a0b2ca,0x4e898b8ba2b2caf0acb2,0x8bac64e6e8b129ba2e28,0xe6eb2d31bacc0a6eb19b,0x29bb6e684ed98b8bb660,0x2e2f19939bb6b4c6edb0,0xd21bb064e6f1b129bc66,0x64e4e918b93a462e2e92,0x99393b862e4ee18b8bb8,0x2b6e4ecac393b2b6e2ec,0xf9839d3eb4c74fac39bb,0x56c2a955acb253ec2a94,0x512cb2558c2a9562cb25,0x538b665523039d44c665,0x956b0aa55ab2c94e30aa,0x953cb087529839d42b2c,0xc86e19399b8b0c66e18b,0x319d6b0ca6e18ba1b8b0,0x2e875adb21d664e675ac,0xd211d6b06475adb29d66,0xb4a675ad219d6b4a475a,0x18b81ad12a874ad399d6],#[0xe62e06b98ba1acb6c86b,0x198b81c664e66bac319a,0xb262e06c99399c6b0c67,0x6c99399b2b0c66cb1299,0x1ca62e86cadb21b2c2a8,0x87299399cab0c67298b8,0x29b0b2ca6c18b81b062e,0xc67218b81c864ec6c2db,0xb81b464ec72183b1c8f0,0x2e86d2db21b4c2a86d18,0x8ba1ccc6a87318b81cc6,0x62e06e993b1ccc0ca731,0x98ba1bab6c86eac321ba,0xab0e06eadb29bab0ca6e,0xeadb81bab4e06eacb81b,0xbab4a86eacaa1bab0a86,0x6eacba1bab0e86eadaa1,0x9bab0ea6eadba1bab4e8,0x8742dba9bab4ea6eacba,0x99b662e06dad2a1d0b2a,0xca7018399c066e070193,0x399ce62e073983b1c0c0,0x4e67518b81d464ec7399,0xdb29bc64e66f18b81bc6,0xb0ca7619399d862e0762,0x99399be62e06fad399d8,0x6b4a70f2d21c3c62e86f,0xd2cb2c3262e10cc4aa44,0x34b2c90d30aa43462e10,0xdacaa444b2a90e18ba4,0x44260e70e99b843a62e1,0x52a18ba49a62e11218b8],#[0x94a8b2a52a2d214a8b28,0xa92e3caa4b862e9302d2,0xb84b066e12898b8494f4,0x6cb2eacb2cba62e12e98,0xcb2496c2a92598b8496b,0x62e92c98b84b262e925a,0x18ba4bcb2c92f18b84bc,0xab2a92a98ba49c62e127,0x98b84c2b2a92dad2a4a,0xa666e12998b849862e93,0x2798b84be62e12d3032c,0x4a062e12818b84c462e1,0x68918ba4c662e13198ba,0x924eb064939839a3264e,0xc68b2db2a46b2ca91ad9,0x31a38e0c68b1839a2cb0,0x4a6883929a4864e68e2c,0xaa22064e6882c31a20c,0x64e68f2c31a3cb0c68bb,0x9939a2664e692ac31a4a,0x260e68d2c31a34b2a889,0x42d21a5064e690ac31a4,0x28c2a888acaa250b4a69,0x8a2cb9228b4ca8a2cb2a,0xa28b6a88a2caa228b4e4,0x6931839a30b4ea8a2cba,0x951864e6911839a3664e,0xa5462ca9518b665462c1,0x29d18b6e5462c39518b4,0x4a7452cb2d26b0e7462d,0xc38524b4a746ad31d16e,0xb0c4a7b1a929eb6e1492],#[0xac31a9ec0a6a7adb129e,0x8b0c4ae31a92b864e6a7,0xe2c31ab8c0a6ae2db12b,0x9662e0a5ad992b8b064a,0xac18b82b0b6c8a5b0aa2,0x2b0c6a8ac30aa2b100c4,0x6a618b829864ecac2db2,0x9aa464e6a62c31a98c4a,0xc6aa9839aa4b0c6a9302,0x29ab262e0ac9939aaab0,0x4e6acac31ab2c4a6acb0,0x21ab4c086a9993b2b26,0xc0c8ad3031ab4c486ad3,0x2c31aa062e0a831b22b4,0xab0c6aeadb22a064e6a8,0xeac21abab6c8aeac322b,0x9c64eca698b829ab486a,0xa898b82a2c6c8a730322,0x2a2b6c8a8ac322a2c6a8,0xa8ad382a2b2e0a8ac38,0x92a2b2e4a8ac392a2b6e,0xe8a8ac3a2a2b6e4a8ad3,0x39abcb6e8a8ad3a2a2b2,0x4e6af2d392bcb2e4af19,0xca1568b6655a2c19568b,0xc2a9582d21d68b4855a2,0xb0aa57662e9582cb2560,0x2b4c758b129d62b2c95d,0x930aa56ec2a9589839d6,0x6ab0875ab121d64c0875,0x1a2cb2068b2c21a2d21d,0x6866ea1a2cb286866e8],#[0x81cacb0872b2a41a2ca1,0xa872b4ca1c98ba072b4c,0xc81aacb206a66e01a98b,0xb806ab0e01a99ba06ab4,0xe81aad2a06ab2a81aad,0x8b807af2a81e2dba06ab,0x62e01f18ba87ab2ca1e9,0x98b806062e81f2cb207c,0x66ec1998bb06666e019,0xb18b807e62ea1c18b807,0x74b2ca1d18b8074b4ca1,0x3498ba07662e01d98ba8,0x4ca62e13618b84c8b2a9,0x33318b84cc62e13698b8,0x84dc66e33399b84ce62e,0xe13898bacdc62e33718b,0xb8cd466e13518b8ce262,0x2e13819b84d662e137ad,0xc398b0b4a62c2ca90b06,0xb6e02eac380bab4a62ca,0x2caa268b4a69a2db88ba,0x662e29598b825662e095,0x618b825862e298b0aa25,0x58b2e2962d38258b2e09,0x962cbaa58b6a8962caa2,0xa6460e69699b8a5ab4ea,0x6daacb0b6a64e69918b8,0x9b76b4c6ddacb0b76b4c,0xe6db2d31b6c66e0db193,0x21b6cb6e0db2c3836c60,0x2a8db2c39b6cb4a6db2d,0xaa36662e0d998b837ab],#[0xb6e0de2c38378b2c8d9b,0x9839b68b2a8de2db8b78,0xb0e74bad29d2eb4a54b,0xdac3853662e34b2d29d3,0xf2b4863cadb8d36b6e14,0x3d2db80f4b0e03d2c398,0xf4b0e63d2d218f4b086,0x3fac380feb6e83d2c3a,0x1ac8b086b22db88feb6e,0xe0b018b82c062e0afad2,0x3a2c0b2e8b02d382c0b2,0xa6f6ad31bcec0a6f3ad,0xc21bd064e6f6ad31bdac,0xb2caf218b83c8b486f42,0xadb8bdcb6e0f72c383dc,0xcb0875f2c39d7ab4875e,0xadb8582b0e160ad21d7,0x80b6e42fac390beb6e36,0xe02cb138062e2e02cb0b,0xb9862e2e418b9380b4c4,0x4e62cb139862e2e62cb0,0x838a66e0e298b9398b4c,0xe4e6acb139ab6e0e2ac3,0xb8b8c66e0e318b8b8262,0x2e2e598b8b9262e0e499,0x8b938462e2e118b93966,0xb6e440ac3910266e2e39,0x2c3a104b6e0412c38104,0xa62e0fb19b83e8b6e841,0x32db910cb0e4432db8be,0xd064e4b318b92ccb0e64,0xb42cb8ad064e4b418b92],#[0x3f8b0e0fe2d392d0b2e4,0x161ac38586b6e2fe2db8,0x858cb0e1632c39d86b6e,0x644b481912cb6e3632db,0x99133266456c81915b26,0xc856492a15922a85649,0x92192320c64c49b21592,0x24e45148b91452486594,0x49b912522e449493b145,0x522ea4949ba12522e849,0xf492a2ff22a8bfc9ba92,0x8322a866c81918120645,0x5dc8ba17722a85ac8399,0x32f26ea5dc8ba97726e8,0x40e48aa30724a8cbc8aa,0x903920a40e4921039208,0xa80e48aa03920a80e492,0xba03920e80e49aa03924,0x2a81549ba83920ea0e49,0x92945b20a516c92145b2,0x26e916c9aa45b22a916c,0x48aa47d26eb16c83ac5b,0xb22e31cc9b946520e519,0x2c83988b24a622c82988,0xa322a428c9ba88b20ea2,0x23481908d26ea28c9b90,0x21126647bc8191ef2664,0x47a48191e92664844819,0x11e924a47a48291e9248,0xa67a48299e924867a483,0xaa1e920e67a48319e924,0xca7a49ba1e926a87a48],#[0x9ba9e920ea7a49b29e92,0x24a682c829a0b20ec7a4,0xc9aa20b22a882c831a0b,0xd22848349b2a0b20ca82,0x348a920d20a483492120,0xd20c48349a920d24a48,0x8349b920d20e48349b12,0xa0d26e88349aa20d22a8,0xa83483aa0d26ca834832,0x91eb20647ac83b20d26e,0x6484c9991f120647c499,0x991f720647dc99921320,0x2e077499921920648649,0x9a91dd22a47748b89dd2,0x22a87749b11dd22c4774,0x48b29dd20ca7749aa1dd,0xd22ea7749b29dd24ca77,0x3c93b1dd22ec77493a9d,0xf20ca83c9aa20f22a88,0x78c9b2a0f24ca83c8b2a,0xa1b20c678c9b11e322e2,0x27948b89e524e686c831,0x91e522e47948391e526e,0x84cf481933d26e479493,0x21b3d24a4cf482933d24,0xe6cf4929b3d20a6cf49,0x9ba33d26a8cf48aa33d2,0x20a6d6c9bab3d20eacf4,0x49aa35b22a8d6c929b5b,0xd20a4d7492135d2284d7,0x749a935d24a4d748a935,0x5d22a8d749b935d20e4d],#[0xd7483ab5d26e8d749aa3,0x3432664cfc81933f26ea,0x4d848193612664d0c819,0x933722a4cdc8b8b37266,0xeacdc9aa33722a8cdc9a,0xaa35f22a8d7c93ab3722,0xa73bc9994f120653c49,0x83acef20e73bc929cef2,0x26e54148a950526eb3bc,0xc9994f320653cc9bad05,0x724869dc9218cf208633,0x14921a8326e89dc839a7,0x6d2664a249992792284a,0x9b49a126d22849b48b82,0x26d22e89b49b226d20c8,0x49d49b228720c8a1c93a,0x1ba92086ea493927522e,0xe8ea483a3a920e6ea492,0xa13c12486efc821bbf26,0x664f149993ab2684f048,0x8ba3a12684e848a13a12,0x20866e4921d3f24e8e84,0x48aa1b924a66e49219b9,0x724a675c9219d724a86e,0xc48ba9d722a875c9399d,0xc920e07249b29b120ca6,0x7249aa1c922a87249b81,0x9c926ca7248329c926c8,0x873483b1c926ea72483a,0x81bb20e06ec9b21cd20c,0xa86ec9b81bb24e06ec8b,0xba1bb20e86ec92a1bb22],#[0x2ea6ec9ba1bb24e86ec8,0x8381d926c87049ba9bb2,0x26e07649381d922e0764,0x48ba9d924e67648399d9,0xf26648948aa4a326ea76,0xe499929f22a891c99924,0xb326c8ac48322b12664a,0xa8c821abb2086a84831a,0x6924e8a8c8b92a322e0,0xa1a49ba06922e81a48aa,0x122a81cc9ba86922e,0x26400ea0051001900064,0x200498020e00e8005f00,0xe40068402f2016300a,0x25e01208087c040001e3,0xee02e1016480aa405080,0xc06b80341019680c3405,0xfac07ba03c501cd00e1,0x36811240866041401fe0,0x8026d013080958048f02,0x58902b5015200a68050,0xc6a060f02f2016e40b42,0x5c0d7c06ac0346019840,0x1ca00e1c06fb037501b,0x3e081e680f00076f03a8,0x700424020a0100c07eb0,0xa08f7046c02308113a08,0x12e2095f04a68248c121,0x83c13d609d904df02690,0xe82a8015160a6c052102,0x59102c2015d40ad4055,0xbca05cd02dbc16b20b3a],#[0x920c2c060c0300417c80,0x19740c9b063f031ac18,0x34d41a420d0306738335,0xd58364c1af60d6306a58,0xb070f038281bea0dce06,0xec5075503a201cc60e4,0xebe0f43078e03c081dcc,0xe81fa80fb607c783dc81,0x41ac20941033080b03f,0x887043a8219a10b6084a,0x8a08bb045882288112b0,0x120708f704724236a11,0x25781296093804948245,0xd3c26721316097784b58,0x284f142746138809b904,0xa3405110284a140409f,0x4fd0a71853102954148b,0xc156b0aab854b02a301,0x42bd615ce0add856942b,0x597c2c9216280b08857f,0x8605bb82d8a16a60b430,0xc0bb885d802e8417200b,0x18020bf605f2c2f5a178,0xe618570c22060a8302e,0xb431b018bd0c50062283,0x652c326c191a0c80063,0xcf28671c335819810cb6,0x6e0d2a868e0343c1a030,0x1ad20d5d06a9035141a,0x36ae1b2b0d8b86c0435e,0xf9037741ba00dc706df0,0xc071d838961c200e0506],#[0xe85073d0399c1cb00e4,0xda50ec7875c43a9a1d2c,0x241dff0ef2077443b721,0x43d2a1e750f22878bc3c,0x7c583dea1ee00f6907ae,0xd107e003ec41f4d0f970,0x7100887fec3fb41fba0f,0x20ad1043881c04096202,0x28a212d1084083bc419a,0x504376219f10bf085984,0x8898c4472222410fe887,0x17708b3845742296113e,0x9711b988d58468623191,0xc242211fe88f7c477423,0x498624a2124289180488,0x5ac4a96252b1286093b0,0xa097d44b9c25ad12c689,0x1348099f04cb22638130,0x71c138209b844d7426a3,0x60279713ba89d344e682,0x503c27ff13f489f544f,0xa2685100286a142b0a0e,0xa30a494521428e314600,0x614e98a6e0532a296b14,0x2a76152a8a8d0541e29f,0x6542b0715728aaf45532,0xc8572a2b7b15b28ad185,0x8b08857fc2be215e30ae,0x6650b2a0590a2c5d1627,0x6616a20b4905a0c2cdd1,0x42df416e30b6bc5b142d,0x5d0a2e6717210b8945c2],#[0xc445de42ee417618ba8c,0xc8be605ee22f4f17978b,0x182e0c0d0600c2fe017d,0xe6185d8c28c61103070,0x23160189f0c490620e3,0x63f631de18de0c67463,0xca74650e327119260c89,0x9e0cc4865ce32cf195b0,0x119d30ce3866d8335b19,0x344d1a170d03067d833c,0x9c834c31a560d22068d0,0x1c6ac8353f1a920d4346,0xd88c6c0035d91adc0d6,0xb5c0da4c6d0036671b23,0x801bae0dce86e1836db1,0x38051bf50df2c6f4e37,0x714638801c2e0e0f8704,0x54c7268390e1c778e31c,0xb0e73c736839961cb78e,0x1d3e0e96074603a121cf,0xb1e1d7b0eb5c75623a94,0x903ba41dc38ed8c767a3,0xc78a83c371e070ef9877,0xf3ec79b83cb81e4b0f1c,0xcb8f5cc7aac3d371e8e0,0xc1f1a8f8447bd23dc11e,0x3ed31f5f8fa787cf43e5,0xf0e3f641fa28fc947df6,0x547ff43fdb1fe18fea07,0x902e0811640622022100,0x9e904a4822840f3206f,0x1520f2906cc831c41622],#[0x2428e213910948846042,0x86564313217890b44855,0xf34874e437921af10d0c,0x51111c8850440f21f810,0x22749133c89724499223,0x58322b5915148a3c4505,0x3e45f822ea916f08b484,0x88d6246892332119048c,0x1d6c8e8c4722237a91b5,0x291f508f62478e23bc9,0x4243812134906a481d24,0x4915247e923709166489,0x370499424be125589268,0x3494624a0824f3127389,0x12b3895564a822534929,0x5c012d5c965a4b0a2578,0x2b260492f8897724ba02,0xc4ca62647931a8989c4c,0x9a824d1f267f13380997,0x7a89b944db226c4935ac,0x3139ac9c9a4e34270513,0x278313b809d7c4ea3274,0xfd627d813e249e984f1b,0xc650422817140449fe24,0x8a19a50b3284c141e8a0,0x4670a2da5142288b143c,0x1a94888a41051d528d79,0x4294f14a2ca4b8524829,0x5342299294c14a5be52c,0x79e53b629ce14dfca6c8,0x2ca866541a2a0214fb4a,0x9531ca946548d2a3a951],#[0xaaa154f8aa4a55062a72,0xe92ae615680ab10556c2,0x565a2b2295878ac0c55,0xadb456c52b5295a30ace,0xe18aeb057422b9015be0,0x995f78af8457b62bcd95,0x2c3496110b03a58072bf,0x9092c7896364b1705892,0x3c59872cb096518b24e5,0x4b3ee59e32cea966d4b3,0x698cb4825a292d0d9681,0x8a16bbcb5a25aaf2d431,0xf2dd196df8b6b45b332d,0x5c532e1797028b7d25bb,0x9de5cd72e5c17258b8ea,0x90bafe5d5c2e991741cb,0x1789cbc185de12ee1976,0xf7017af0bd365e742f23,0x8d2fb317d04be385f042,0x260032ff117f04bf525f,0xc15e6082302f98114c04,0x4c8c22660fd306c982f4,0xb986c0c332617430a998,0x313c98940c458620330e,0x316317b98b60c5626298,0x9a63a331bb98d5cc65c6,0xc8a6643d320918fb8c7,0x93f8c99a64b1324a191b,0xe5196b0caf4655e329c9,0xc333199914cc3865ec32,0x671c337899b20cd40668,0xf70679d33bd19d74ce7a],#[0xe4d09e682633fd19f70c,0x1a49cd1f068cf34501a1,0x4e61a6a4d322696834a6,0x6e35259a89cd41a69f03,0xe6ad1355d9aa98d5226a,0xd6d86b51359d9ac48d5d,0x54d7e26bda35d69ae34,0x21b284d8e06c4536181b,0x36b21b514da3c6cea366,0xdf936ea9b6f0db486d89,0xee6e5f37209b8a4dc226,0xddc86ec437531ba54dc,0xbdb0deb26f3937901bc1,0xfd1bf64df7e6f9f37c39,0x2383f9c1a4e088702037,0x711b387f1c374e18670a,0x37c719738bb9c548e274,0x64e476722238ff1c774e,0x9cb9ce58e7294393b1c9,0x9b21cd40e65c731c397e,0x1b39fe1cf70e78273913,0x874b23a469d180e87674,0xea98752b3a8a1d3cce9b,0x7f8ebb875af3ac89d590,0xe9da04ecba763a3b0a1d,0x3b951dc14edd276c73b4,0x7b73bcb1ddfceed67748,0x6a78223c089dfc4efa47,0x4f16078983c379e158f0,0xe4e8f25279073c759e35,0xe89e6b0f332797a3cad1,0xb3d291e8c8f43079f33c],#[0x7b273d799eb00f5487a7,0x7bc7bb03dc81eda0f694,0x3cf8de7c473e129eff8f,0x9f444f9ec7cd43e589f2,0xedb1f63cfada7d4b3e95,0x613f221f870fbf87dd53,0xa7ef13f649faa4fd127e,0xff1a7f703fa91fcc8fe1,0x85000e7fea3fe61fe9c,0xea022100e6805e402220,0x407aa039d01a480bd404,0x18c40bba053d0254810f,0x3e820440f22072503588,0x1053a827c412a208f904,0xc71060a82ef416aa0b0,0xd020e4906fa835f419e2,0x7420aa100507da83c241,0x84bf424c211e108ae843,0xaa28536428d2141509ce,0x390b7685a542c9215ed0,0x219250c58860242f2a17,0x37921b5d0d4c86834330,0x8f43b821d610e7287194,0xa87f443ea21f010f5887,0x10e28859441ea2085101,0x41111ca88c544512220d,0xea25e912c289424491a2,0x4506227c113aa89b644c,0xac2454d229cd14988a26,0xac8b3b4592a2c0d15be8,0x917868b9d45c022d9116,0x314d187c8c1645f5a2f6],#[0x7d2335519728c954637a,0xd46b9235391a788d1a46,0x8e2c47032379d1b828d9,0xd9c8eb6474ca39b91c8e,0x391eca8f36478423bb51,0xa406520048fd847dba3e,0x87a2430d212290694827,0x7d48b324519224c91134,0x891f148eaa46dd234291,0x24f492644925248a9241,0xc1525c092c34955a4a45,0x124de526ba9342498d24,0x4a18a502d27de93c949d,0x4cb4a53251ed28c89448,0x2955d4a9f2545929de9,0x12c4e960f4af2256d12b,0x5af12d48968b4b35a593,0xa625cb52e1696ec4b6a2,0x24be525ead2f2097704b,0x98974c33a60dd301697f,0x27299124c79263693172,0x8d337e999c4cbb265613,0xa69e934c29a3d4d0c267,0xd9126c1135c89ab74d49,0xc74dd126e0136c29b414,0x89c454e172702d37de9b,0x39a09cb54e4a271e938c,0x5e93ac69d464e92a73f9,0x1278393bd69dc44ecfa7,0x4f47279e13cac9e3d4f1,0xf3a4f8927bbd3d969eaf,0xb69fc44fd027e013ed49],#[0x14076a021500527fd13f,0x8349416ca0a15042281a,0xbaa85514278a117507a2,0x15101287714380a19250,0xa2c75150a89d544a4a23,0x6cea34f5195a8c0d45d6,0x9d4818a3e551da28e414,0xa9345494ca47a5225a90,0x2bba955d4a5ca512527c,0x1252fca97594b76a5a05,0x4a66d532fa99194c48a6,0x4e24a6f1536729ab14d2,0xe894efea76453a629cd9,0x92a0314fd6a7d853e2a9,0x54542a1e550b6a845541,0x9555497aa45151cca8c1,0x6a9e854e2aa6955300a,0x554f4aa52551c2a85d54,0xac2155dcaad355562aa6,0xc3aada956b8ab3e558da,0x755fe2af815774aba655,0xaca1563cab1755872ac1,0xa96ad26567d2b379596a,0xc15ba0ada956c62b59d5,0x2ba415cd8ae445710ab7,0x7912bc0d5dd6aece5756,0xdd57dd2be595ee4af4e5,0xb04c58172c0316000af,0x6192b0b0584bac1f160b,0x5796286b11e58822c369,0x7ac7a56384b1a758c1ac,0x59412c9696492b223590],#[0x30a59732cb1d6572b296,0x52b38759b92cd116660b,0xd6860b41659f8acf4167,0xd3a9698eb4a05a3b2d13,0xd52d5f16aa8b52b5a8ba,0xd5b0f2d81d6be4b5d15a,0xb6cb5b522d9f56cb6b63,0xf54b7755ba42dc8d6e00,0x8d7060b8135bf52df256,0x2e34d7160b89c5c3f2e1,0xcc1ae5797274b9115c74,0x2e5d04ae7817390b9a25,0xabac25d49ae9dd74a0ba,0x76f2bb515d992ec2d75c,0x1257840bbf75de5aee7d,0xaaf3217944bc7e5e312f,0x5ec02f56d7a70bd125e7,0xe455f072f7997b92bda4,0xd6bed35f56afa257ce0b,0x17eb6bf3b5f91afbf17d,0xffe97fb4bfae5fc52fde,0x67b025d80c4c02f600d2,0x660bc305798256c0fb60,0xc2496110307f1838ec19,0x626c2f7616d30aa984f4,0x598752c37561a830cd58,0x311cd88b0c4316200b0f,0x2a53146d89bec4b06247,0x962f7316fd8b1ec56a6,0xc695633a319498c68c6,0x8ea4c7376387b1bc58d8,0xb99002c7cf63d231df9],#[0xbb230d912ec866642832,0x64b2b2505923ac8f9646,0xa1964feb27819372c985,0xa0cab26549b29a1948cc,0x196e8cb3f659332be595,0x30c19808cbe565db32e6,0x7bb3349992ccc726629b,0xc66c73359d9a90cd1c66,0xce64671d338499bcacdb,0xe68cf026773b3ae19d1e,0xe99fb2cfb367c4b3d5d9,0xb4169a088d027680733f,0x875342f5a148d08f6836,0xb068bfb4545a27ed11a6,0x2d2696917b4845a3ccd1,0xa66cd3256979b4b31a53,0x4da7ced3b369c534d7d,0xab529da910d4656a21b5,0x6aca355c1aa7ad50a6a6,0x6396b0a357cdabaed5b4,0xbad6c66b57b59c9aca6d,0x1aee4d7566b9635c0dad,0x60b9afe8d7e66bdbb5e6,0x70b62e1b132d87b6c263,0x76cc0b6529b23ad9056c,0xda266d07367e1b3a2d9a,0x5fedad46d55b69f5b49e,0xbdb772db876daf36ccdb,0x37211b8e0dc416e0cb6f,0xeb2b7521ba20dcda6e59,0x176f003776dbb60dd7a6,0xadea36f3e37969bc7ade],#[0xbecedf3b6f8e37bc9bd7,0xc5c014dfde6fdbb7e2d,0x9b8391c16ae08c702fb8,0x70cab85c1c2a8e13c708,0x22571023877dc394e1b1,0x86e2a6713b38989c49ce,0xdc692e329718038b85c5,0x8fd5c794e3a471bf38d9,0x4a391d9c8ace439720e3,0x727fb9385c99ae4b372,0xe5a072c139561ca68e52,0xcdae647730a397c9cb96,0xadce14e6de735ab9a45c,0x39f6dcf4ce77573a5b9c,0x454ba23dd0eae8447408,0xa874bbba4fdd22ee8de7,0xeea587512ba7e9d3b6e9,0xd694eb17756fbab05d51,0x9d7aaebb375c73ad95,0x93b291d900ec5976173b,0x76abbb505da44ecf0766,0xe0276f23b715db1eed73,0xb6eeb177433b941dc62e,0x9df42ef7b779f3bc29dd,0xc239e0def03b7800bbf3,0xbdbc50de23af0dd785db,0x579113c7f5e394f1a478,0xf31379753cab5e4faf25,0x784f3b079c3bcdc1e67c,0x1e8bcf4397a063cf75e,0xbd479e9eaf4d37a4f3d2,0xae6bd6cdeb30f5717aa0],#[0xa87b3e3d94dec34f5f07,0x6f7567b973dbfdeda8f6,0xf02af7f27bec3de81eef,0x3c9f186f89c7c3abe125,0x3e6e5f30cf9547c90be,0x7d3ebe959f45efa027cf,0xb727da0bec29f5ccfab1,0xcefc2e7e00bef4df748f,0xdfa34fcea7e603f24df8,0xf719fb46fd887eacbf4d,0x56bfa21fca8fe297efcb,0x27fa63fc89fe04fed37f,0x97fef3fecdff2aff7,0x18500a2803ec01660063,0x2602b101348083c03860,0x409ce0477020180dec06,0x19dc0c5205cf02c78150,0x40820f40fde077103788,0x504fe8267c12aa08fb04,0xc1305cd82c6c15660a5,0xbce0daf06ae8342418ee,0x2c1e9a0edd0735838b41,0x843ac20de101107e483e,0x9488492423c611810899,0x410a0284edc26d612f50,0x2159b0a9d8530c292a14,0x2e5216bd0b3e858742b9,0x2c430e6182d0be085dfc,0x2866c4330619310c7486,0xd9e86b9c35421a510cf,0xcd30e338704437961b85,0xfa1e370efc876ec3a7a1],#[0xc3eb61f1b0f7787b143c,0x83d4410e202d0ff287e6,0x6e889f4445a21e310c08,0xf122788f94470e233511,0x25eb12bf894cc49ce248,0xf6e2753137289a844c66,0x54521a28b514278a03c4,0x8a9b4545629c314c98a5,0x5f28adfc563e2af9154d,0x8916858b30458ee2c371,0x22efd17558b96c5bee2d,0x61a2306518008be745ea,0xa3c644a31bb18b58c454,0xd8d08c67ba3375197c8c,0x1afe8d64c6a5634cb1a3,0x7b31ba58dc746d7e3667,0x4a38e91c598e1e470163,0x474e63a231ce38e60c72,0xf1b477ee3b851d9c8eb4,0x248f7847b0e3d331e618,0xb1feb8fdfc7e163ea71f,0x419b209b9033c811a402,0x67a4301215f909b48436,0x44897e4461220690e4c8,0x918f48bee45a5229f914,0x3f291edc8ea646f3234b,0xb324a8923e4914648512,0x24ae3254c929ac940a49,0x98c24c1125e092d9c968,0x6fc9b0e4d3d267293264,0xa93b1c9cee4e3926fd93,0x28389407c9f9a4f5f279],#[0x1b728b3944cca1da50b1,0x2531d29679495ca4025,0xca99654652a0b94f2ca7,0x5ab4ac7255ed2abf9546,0x2a95fbcaf3e575d2b829,0x52d0396654b24a58b12c,0x5bd72dbc96c44b5665a5,0xaa25cf32e5c971fcb846,0xdcbd465e612efc9768cb,0x97facbf3e5f752f9b97b,0xbc98444c19260793015,0x2b316f98a6cc49261dd3,0xa6459320898f34c70663,0xcc2665af32a3993e4c96,0xe74ce966715336f999cc,0x69a37cd116684333e999,0x35229a784d33a6951348,0xc4535ed9addcd6366ab1,0x426dbf36a49b3f4d91a6,0x4df3a6f3937659b9ccdc,0xc374e14e705d38039bf4,0x1c9c764e32a7167388f9,0x1399b9cbdce586727739,0x74b33a299d024e7b6738,0xc6e75e53ad09d594ea1a,0xceef6773b3b629d9ece,0x9e274f0be78213bf19df,0xd159e734f32279373c76,0x753da59ebf4f5767a873,0x27cdb3e279efdcf7627b,0xfd3e7e633eff9f65cfa8,0xfdcff767f833f9a9fb8c],#[0x7a0535021680cb402d9f,0x4136a08d503fe81cb40c,0x41541d8a0d45062682b5,0x4e85694291a136508ee8,0x50dba869f432da17cd0b,0x214d101287bb43bba1ce,0x10a276512ee8911445da,0x345a7a2b8515528a6345,0x8d1d4674a31f5181a8bb,0xd768e59470ea36fd1aca,0xc520128faf47b3a3c851,0xa474d231e91354871a41,0x9eea4dd5260e92934912,0xaf4aa3a53f52942943f4,0xa970f4b56a59452c0295,0x31e298a14c20a5f052ea,0xadd34a29a034cd9a6585,0x9a70d5378a9b574d7ba6,0x4eeda76453ac29d134e5,0xf934f98a7b0d3ca69e1d,0x6a0b7502ba806d3f869,0x5448aa1f150d0a852d42,0x900d4776a35b5178a8a1,0xaca94554992a47b5218a,0x35369a99ed4c1aa5b952,0xa85b5406a9f354eeea72,0x4a6a9f754c2aa4255152,0xdd56feab375577aaa8d5,0xab46d598aac675605aae,0x763ab9e55c36add956c1,0x7f5812abf155edeaf1b5,0xeb1d558d1ac4bd61b2b0],#[0x662eb2bb593eac92d642,0x1a5682eb3cd59c2acd25,0x5ad6dd6aeab5015a55ad,0x5bccadc856d9ab6815b1,0x90b5c5fae1d5708eb7fb,0x56ba495cf0ae685729ab,0x577eebb8f5d9baeb6575,0xf62d7a1abcc55e3daf0c,0x86afaad7cdebe0f5eeea,0x15ff9afef57f02bf415f,0xc1e760bfb049d815ec04,0x682c3196158b0a0d8426,0xb5897ec45f6208b0e558,0xb19a58beec5b762bbb14,0x42fb1fd58f22c7396369,0x4364eab26159276c8d56,0xacbb165adb2ba59542ca,0x9a8acce76638b310d980,0xd7d9db2ce876713b369d,0xbb426da07acff967d5b3,0x68fbb46d5a2b2d129687,0x38769a2b4bc5a536d24b,0x96d4e96a48b50c5a7b6d,0x5ad62d6556aeeb569daa,0x6215b072d7e36bb2b5c8,0x33b681db32ad9216c6ab,0x56df5b6e05b64edacf6d,0xddff6ec8b749db952dc5,0xadfb76f99b7b45bcd2,0x95c306e1157061b81a5c,0xb8d55c5eee291711fb87,0x28eb92fdc8b6e41371dc],#[0xfb7347b9915cb86e5717,0xee8777403b9e85cea2e6,0xd496e9d374b5ba425d18,0xecdd6faeb25756abaa1d,0x9bb4bdd99aec737614ba,0x7749bb925dbeaed9d76b,0x3b77f7bbdedde02eec1,0x7af157787bbc2e5e0e2f,0x5e64ef2f97947bc88de3,0xd2ede8caf41d79d9bcda,0x21bd7adeb72f56f7a89b,0x57bc3bdcb5edc2f6997b,0xf9297c62be1f5f06af7e,0x57afa757d15be7adf2ea,0xcdf7aefb877da2bebf5f,0xbf625fa4efcc37e2ebf0,0xf94bfb15fd0afe1d7eea,0xdf8045c00e5ffc2ff9b7,0xb01dd80cbc050e024300,0x6f3031b816dc0a5e044,0x396094304418200c0e96,0x6c180e0b77056b8295c1,0x83e0c1dae0e0f06a9832,0x9118475c229e10bf0807,0xa30a2784fac26a612db0,0xe171b0b41857cc2a4e14,0x348e19830c65860cc2f4,0x3fc38961bcb0d8f86afc,0xd87bfc3d0e1e2b0ed387,0x10fb8866c41be20370fc,0x59b126b890bc470e22d3,0xf6288f13f589ccc4cce2],#[0xc57362b2315518a78c51,0xba9c5bb62d2f16558b0e,0xd78c41c61262fa3177d8,0xb19f38ce1c65b6325318,0x36bb1b1d8d5fc6986343,0x2c638e31c178df4c6e9e,0x8c76b63b0f1d338e7ac7,0x8f9fc7bb63d271e398ef,0x1119057c80fe3fd31f9b,0xa322719110c870e42db2,0x647cf23b191b3c8c8645,0x96ce4ab724e39243c90c,0x9dc9c064d6f26719315c,0x19430ca01e4f77278793,0x29a794b3ca47e51cb28a,0x6db2b0d9552ca91653e7,0xae59972c61960bcaf165,0xcb9f65c5f2de396c2cb4,0x827cbfc65f232f33976e,0x1d98e9cc5de622b30b39,0xf334d9978ccaa664f732,0x69cb34939a1cccf3666f,0xa4e6c5f35df9acecd4d6,0x9ce0066f3b37599b79cd,0x9c9ece45671cb38a19c2,0xadd9d49ce8ce73a73977,0x533c479debcee3676833,0x67b073d499e82cf36679,0xfcce7d873e6f9f05cf6c,0x47d014680373fcb9fbfc,0x1a0f1d062e825340c1a0,0x432fa16cd0a7684a7421],#[0x9474469a20bd0f6e86fb,0xbe8b9f4583a29ad13ce8,0xd1e2e8eab46ffa349d18,0x4bcd2416917f4863a3f1,0x1fa560d2a2e945749cfa,0x74ca5a625d2fc697134b,0x9c974e05a6e4d35669a0,0xfc69f4b4f57a77ad3a86,0x2d44e6a1af5085a81cd3,0xa96dd4a66a47b51e3a8c,0x479aa08d4f26a707533d,0x8f559baaa8d5426a95f5,0xead9f5693ab26d580eab,0x6136afff579baba8d5c3,0xebd665eb2a35907ac51d,0x1ad7dd6ab6b4f35a25ac,0x5c51ae08d6f56b7235b4,0xbaf5d93ae9fd73a6b92f,0x86be175eadaf2cd786eb,0xd8236c0875ff1afcdd7d,0xeed865ec2a36103b063,0x49b189d8b66c4f36223b,0x36437b1fad8ecec70763,0xcb6b655fb286d9306c91,0xbdecd6b6675b31fd982e,0xda01ecf8b6791b3a5d9,0xb49eda3f6d1676877b42,0xaabb535da856d39f6983,0xcf6c0bb5d9dad4ed5eb6,0x6dbdf6d7fb68adb2ded8,0xbcceddf36ea5b736db8c,0x2bdc0a6dfdb6fcbb7c2d],#[0x1b87ddc336e1377079b8,0x728bb917dc766e317714,0x71b7357b99bdcc56e58b,0x6e9677473ba0edceeee,0xdd8f6ebbf7593baa1dd4,0xbfeddeb6eeab76ffbb50,0xc1bcb4de486f1737855b,0xf7b0fbd68de996f42379,0xf98b7c7dbe10deeeef6c,0x9d6fc577dcfbebbdf40e,0x2dff26fef77f2bbf6ddf,0xc0c5e049f01e7808bc01,0x30fc16ae0a07044b81d7,0xe3843fc1fee0e3f06778,0xf0b378559c284e12bf08,0x1b170d37865bc309e176,0x44e20b70f8b8781c39be,0xbc4e5e25b7123b88c9c4,0x8b4dc582e2ab714c78a1,0x9938c69c606e2f3f1713,0xa71bd78da5c6b3e349f1,0xe3d5f1dff8eabc72ae38,0x856e41cf20638fedc7ca,0xedc8d1e45b7225f90f5c,0xf92f5c95be49d7246b91,0x290b942fc9f3e4e67269,0x70f2b179557ca91e5337,0x5e5b2f2d139643cb04e5,0xcbfbe5eff2f039751cb8,0x925cc74e629f30e39835,0xe79a27ccf9e667732c39,0x736db9b2fcd72e6a9f34],#[0x71ef38879c19cdf0e6e7,0xf2e76973ac79d13ce60e,0xbcf7de7a8f3ca39e13ce,0xa075d018e7faf3f4b9f4,0x3b7a187d0a0e83ef417b,0xef46c3a309d14ce889f4,0xe93a74947a455d207e8e,0x32de985f4ba3a577d298,0xd3d3c8e9d674dffa6b5d,0x3a8d9d451ea1675027a7,0x54ebaa25d4e4ea5df524,0xf2f56ebab35d57ceaadf,0x1eb3cf5953ac63d60fea,0xd73beb88f5bb7ad8fd6a,0xfd9d7c7ebd175e03aeb9,0x37b0c7d84aec147602fa,0x764c3b201d8d5ec55762,0xcf1766ebb339d978ecab,0x89ed347691bb441d9fee,0xfdb0eed7476b23b54fda,0xb79ddba9edc1f6d7bb66,0x203b8b7dc41ee0b76fbf,0x2f740fb9d3dccaee52f7,0xeed877647bae1dd44ee9,0xe48ef17f7827bbd3ddcc,0xa9deb5ef4f77a07bcdbd,0xfbe9ddf31ef8677bb7bd,0x7fcfbf75dfa1efc1f7d9,0x5378207c0c9e036f0097,0xf09bf8423c1d1e0c9f0,0xe1d9f0da7866bc2f9e16,0xc1fe25cf11af885bc3e7],#[0xe002d820f8418023a004,0x120300a0a090681044c0,0x603d078082860881c1b,0x42472609604262311486,0x9c2209418102b040cf04,0x740c3b84434140484c18,0x52100e1cc3a223287074,0xc0043b049c4062418288,0x516200b8601641a13083,0xa02170d06c4e02010e13,0x892211a4a484228a8127,0x4b8ca2b17854c94e9900,0x354d49c5a3b1084a68a0,0x6cb38d4b43cacc5a3c6e,0x759a89872c3192494c62,0x130198dee0e13b69f81a,0xfe45011b7fe49211abc5,0x2bf8384e3fc1c515244f,0xc5c4e7fc58131bdc1c27,0x1e7cc755011fb5663279,0x397265d8908abfac3075,0x93685fa1462f091ccb53,0xeb08ebf536c42397e9b1,0x8d679512bd4515956612,0xd0e7af46117b5663ed59,0xb7c86a2050ca710d1708,0x329121c9b28814357262,0x8468aba8689b942388a6,0x995bd3a1059498f24d5f,0x24fb487ab8c045ca7f98,0x16cd5c3005c80344e0aa,0x3cd29309b948601ff956],#[0x57c91259420d3b7e1320,0x5ecb1850c9c63f4d8998,0xfb436899f1ff090285a4,0xe6be48a9c78f4d899a3d,0xca11ce2311c52249e84b,0xfe5250cc11ac3257262d,0xaf1489b942878643080d,0x6dd54b0a195c3d08142c,0x8ca394b5223dfeb225f,0xaa58929ed64d1ccf5f51,0xdab31a7d212119b7ae8a,0x79f690fb56635d63588b,0x29634258d097e3428634,0x2223ca106bfac8090e4d,0x684e9fe62659390f7e73,0xf34b20aa417ff62aa880,0xe50cc8863438fca94c83,0x4e86d425c1e49340d13b,0x39aa5b2cf25223bd0b07,0x1a4b3e620ad486cd258e,0x538c8ef5141ad7fb14c2,0x696c68bb948799058dbf,0xdb44b254b62ef4937196,0x33c46ef42c1d7f48164c,0x308d0f7b888451f53645,0x3449c2344d39744a74c9,0x94e7e884165d06344958,0xa4611a1dd7090f3e4609,0x84866dd68449df8f6a21,0x44f3622e7f5100ca9f44,0xfa122063093267ae8099,0x515aec453f0bede4503],#[0xcebcf30247beccc133d8,0x622df97daf0513fa5322,0xa32e1cf430e381322f09,0x928cabfc2f542478e184,0x132b78d7192fd91227d0,0x8eb7807beccc13173fc6,0xd23af421af42197e984c,0xfa5a351d7a10e7fe9782,0x24ce52ebc2650f4931c1,0x5594cd775c79345b9065,0x8c71088afbd46142a7ef,0xa5328ff3617247a72841,0x1f3d1ad0859f690ca9f2,0x729fe6265bf8e04aab1a,0x84cbdf1ba997ba79899,0xbfec2e48d4f4002113fc,0x922d3d00084dff6ce48d,0x11774c045a7a00109383,0xdf7e492009372048b730,0xc7ee6022cdcc045b9024,0xe2315aa8a299e239f690,0xbd6042cbb729137290c9,0xe132efd09b9a47de8911,0x9fb8240a77aea522b7ae,0x830cbb94864f38f131f,0x89f11272856e1854227d,0x9475d74f1157444f88c3,0xd943df4a1af4e8739689,0x49add9455d2863ef4a24,0xd13289b28d976a208bd4,0xfbd2893650d6b486385e,0xea89865497a1cd6eca28],#[0xc9b5d61d8cd20770871,0x315add1182e27446aaca,0x9eef04cb5da228bccc8,0x7afa6418888e22eac711,0xc5be5d3a2a7c5318af08,0xad57049c354315e10e34,0xa149e851e02898669c72,0xc1af0468a33cbe150727,0x560ce35ca1b7ca09b4c,0xee32b7c0002b0676f800,0x332e96fc8ab7c08995f2,0xf02ee328d7286df2824e,0x173c02ac19b0a5dbc8f1,0x598c6a50c739435f2af9,0x269943df9cc88bb90d3d,0x7b43292456f436fd4e3,0x4658fd11e6b79011a67e,0x451977c08669117d198c,0x10e88f6642653e31d7c2,0x237c4f2ccab8cf022ef8,0xe859032e7877b326f402,0x186ff0478f598f31a638,0x16606c6c616db098661,0xf2d4196bb43a995b3e41,0x5103d4a1d4ccb61744ec,0xb2d7a0b1b766d0597635,0xf1399252e9a1644f76d0,0x751f804b1997fe909188,0xe85830ff8209799b0f08,0x4a1d7b7c6d32cda6515d,0xbf31e4b133b7c096328d,0x4ca2e99438feb962719a],#[0x70d320655e6bd42465e7,0x199bf42064ad1349a330,0xe12277b43a332d438d08,0x3178f51913df1240cc3b,0x8abff4848c474bb7aea,0xf0520655d63588a3e3e2,0x1943d5230659a1e4a46c,0x2de523b493d2997a5cec,0xdf5256cc1c38c1907e7,0x861dea3a9993df220cb,0x1484ea3db3425daa863d,0x84b4c2107aba8f191b7f,0xb7b8f23c11d6a4688786,0x8a28cd96e445d1fa7551,0xe8306413e50d6d50ebd8,0x9ca1e022728d6f4641f7,0xf2a1e23abd190627ca1a,0xfb823f4473efa3a64ebc,0x90335436d9194927641a,0x2319a63fc18d047a8691,0xd4be0b065849d9065fa3,0x360cb1082b0766b031c1,0xbe822eb3573f2319623a,0xb6391bde11d0e5cf811f,0x532617e10165d1ee1dd1,0xa649e5d0e1e8404267b7,0xd0b22c1a1db884213b0e,0x427da689b2cc13b23776,0x208c198e221cffcc2462,0x7f4d9ccb5f208c19635f,0xc33273961031a1a7321c,0x57d91b8caba9cec8c1e1],#[0x63ae041c03356b001c33,0xe8d099fe11e2c133c69c,0xb15b3178691917721db4,0x49359f115b0d3464a2c9,0x2ac06b87ea6462ff2406,0xf894650f8e4d907fdb22,0x1dfe3119993e8494656e,0x8e1ff1b2919971b5588c,0xdb96ffc24624ce6bac00,0x1c60c6b06869c61c700c,0x4e54a670e30635fbd088,0x99e8b6646f5810b2c43d,0x4a94ca1f0a4332d0634c,0xccb26a3c5163e05991be,0x4b038475fb0722c7eb8a,0xe0830cdc9f75400ce38f,0xa8c8d13476448e698c3d,0x71821e6711e544b7db12,0x3ff648bbf692d55a457e,0xafa0225795420cb9c62d,0xc8fbfc89758120de4641,0x53c522e1faf648d2295c,0x928ea072308c07325147,0xd331fb2460e98c6b8457,0xcd4c91d318fbfe2bc00c,0x154bf928dda25b82664f,0x25a4cacb1fe915a20068,0x71c93e4c8e3ea3d4b51d,0x4c63998fd9232afb5264,0x928dda1638266d92869f,0x29118fd10241068154bf,0xacc315a55a36ff1cdda9],#[0x6047ae3e7c00cd1eb1a8,0x3299bb2170caf6455e65,0xaeb022dacb65095a8419,0x7cfa2420ca147b95c8eb,0x262f873e00665c3c5494,0x1d4c8df4b875335dd2ef,0x16597b4166be33c250fe,0x7365471bc068b4eaa842,0x8f079b7930755b322fe0,0x6c65f807a0cbbfc07206,0xe7f8832a16be2de4d96d,0x228effa1b2a3c98e2b45,0x401664f9536999b67abf,0xde4aae4cd5f16f268f3c,0xa38f9ed881a39f8c1e4d,0x221097c60f261f35d081,0x94fc6eb2a7d4a5d65d70,0xa84c2fe82c9996fe00cb,0x5a1e56845790d064a3fc,0xe54822fd86a66af8d793,0xad1c342ca1ad992ff2d0,0x5951cbf09005977e92d0,0x7f78032fbd03508bfad4,0x6184733c232f833532e2,0xd0211bc742a00675fd68,0x2fe983acbae4242101e5,0xb0f245d2068adfb00165,0x2eda138ea324fc3c2453,0x91b30f0d728adaea4d1,0xbe905fb44019b672fdaa,0x754c9b665dbe43106901,0x354938c099b6f90e0fc8],#[0x9a9271813357f812745b,0x5140c119e22581526b66,0x285f0f848c9c751903ff,0xbbea32107ca3229f1e12,0x187a13d515bc98925d98,0x4ae8b63aeb2635b81a3d,0x1d9b1923225db2078bb6,0xdae5996216b742661ffe,0x44c90949832f8e44c81e,0x7bf09247706e72650c3e,0x838f598e38e50994623f,0x330174d8e3ad61931e89,0x363885add09983db5a83,0x3071ce4c610f942658d5,0x14011ecc5d6a32d96129,0xe31d61f118bee63465ce,0x1eaa515ac99d085e1f88,0x7519cbcedb320903ef49,0x5f21f7804bdb2c7f0194,0xb6f332c1f90c3c9b6645,0xa4c492ed1c511cc99bbd,0xad98d3d598cbb4d8dbae,0xa9ec1decca3c0f549193,0x28d9f8544bb661ea5f48,0xc874f7d16b48d8f4af99,0x6c718ca5833345158e28,0x31e6acc75d56630cc15e,0xc22bf48e5c758db2a7ab,0x2e0e3ad61923ad61927b,0x64732662487233933c28,0xb32e7e8cc7d6c3393287,0x467dfe9e0c711cbec17],#[0x825ec704affc8b1eab91,0x3850047b36778383d99c,0x32163d2f6651230ff91b,0xec7e43efaa66c330617b,0x9681085f4dec32c5b1b1,0x256fc398464865a832f3,0x91e01bd84643b482e75,0x7fb00320dec220ea7fb1,0x9bfc06883a405e2ce141,0xfb0045c373011871c08,0x5371238dcc0450f25f13,0xc4aafc124d2ff0008e35,0x7d61707249638a817318,0x5fec8ca642eb41207f8d,0x926a7e0118de4041af18,0x55faa40236c421e7a501,0x4b3b384b5598b3281bd2,0x5d023efd702791976274,0x5a833c43eb6c8833a8fc,0x861e81e24c41a38be84,0x1ee0c892cbf60c66669c,0x3810e70218ad7089b518,0x823cf8094902cd06da49,0x478bb7e889d3b920335f,0x7e0997f33411675fab10,0x45bebf04aaa2b5e2317d,0x84979e41d0e644db7ac8,0x8222d7087a755139cb40,0x1575c20c1490f9a631d7,0xdeba0f0475ae10f0c8d1,0xa1228f580fd170d1c846,0x78088be02189e211179e],#[0x87cc5437d08880f908b9,0xe75aad9032a68c97d3ac,0xf810f79a0be023871831,0xb3c60c69cbccc8a3c21a,0x3277c22af810d7bf2011,0x1e196a628e5fc0115acd,0xe821ed4630ed74922b7a,0x218888e22b010ba20839,0x40b59a0f843eeb629e8,0xbc1881247f58d808c1c7,0xbd1434cabaabb7824483,0x1e0be5143b8d8f38698d,0x5a851c0d5ca2aebf0245,0x3f193bb231f764639fcc,0xb718cd22d1e43348938e,0x683e2a85192df18cd22c,0x469bf0fd4523a7288ce6,0x230447cbe6711457e304,0xd71e44247772a5908a3e,0x41cf85f9234fd7418a36,0xe99473f80db748ccb1c6,0xd102661efaf812344a52,0xc70a70196a1f60265af7,0xb263553e1509df758032,0x4f7b41b52867ae1363ae,0x46991b3808e322462712,0x67264d89fe48bbe67e22,0xe4f04c96e6f0540a18b8,0xfbafd13f112461cff245,0x48dd2827a65df3b3c448,0x6f4c7d6a06f0cdbe767e,0x6f99f88919544fc448ed],#[0xc98c7fa8912bb053b133,0x5af848a32b792e099639,0x84d91bd9b6d9972c4754,0xd388e9033ae6978a4688,0xff0f211abb51190d228f,0x60f32e5e33745cc698f6,0x2de4930cdd20a7b65287,0x2867ef6c0daccc192d8c,0x8e959407526744e114f,0xd5163d3172a8ce00ecf8,0x972e40f120be4cc7b96b,0x3931c3474c84dcb9f08b,0x3246f7278f4c1d6c33c7,0xf7450c0671ff8c244248,0x40fc2ad1a305fcde9163,0x4f54483e10e7e3597982,0x9bbca56c9dd342290ce8,0x35af98f4f9a3126d7870,0x533fd91c3d345ca28c51,0xfe4009b003465b01b209,0xad1a75a24238fe3408bd,0xd607d48be8e1f0cc092b,0xc875a87862267b287b49,0x8a6c4cf5e52d30ccdb1,0x9f1b4cb87e77507522b1,0xa330474d1900b1aad96a,0x35ce208fbfc41103b88a,0xffc61221240fe3408ab,0x7976605049d9efb02824,0x7f0da380ceab0b9c4121,0xc1895493df86d1c0666b,0x8729e8b50f10d86618ef],#[0x49972f0111627fa3848e,0xa37e4d1f84160ca9fc13,0xe464f0e3d465da5c512d,0xef810e78562ba3091cf7,0x46d388e11547843df021,0xd630fc1524c3388d74d7,0x197bcc7accbb1b7916a5,0x318462101d49a336f58,0x86cd1820d46972711e3a,0xa928d02567240f1277c0,0x9748f9f42c81953d35d5,0x148c764155898a5efee1,0x204cd9c447194b2fdbda,0x4c65e34c7ae4260ea91e,0x8d3d458f76f55e118bb6,0x44af4ca193a54d8fa54d,0x6c32ee50970bb9459178,0x8b8d9e48d0cd22b09188,0x38e3f192bec8c7dd968c,0x64eceb63eef46c8dad89,0x5ba2c197b31a64ef8f46,0xc1ce1338cc316bb0fa3b,0x4bd947eb698c29f1450c,0x918186683c3f5892361b,0xdf57c4582e9a32003cfc,0xf6645e5d78823e69a31c,0x7414265c3e71048cf0e,0x1f795bc032f4318bd965,0xa07a49921878a840e49b,0x1f8d8f6a2c2951886c32,0xf493d16bd6630f52e065,0x337887bf520f2349e85b],#[0xafef543926798b0b3d89,0x48b07fa9c8bb8c411670,0xfd164662fac83641fa18,0x39545990f0ffa2d89290,0x6b3304bbd79c89624650,0xeb11c65b3304abcd52c4,0x9056bd5a4e69354c6c61,0xcb3b0fc195349487c71,0xfcc84609049d9267f510,0x93477d6991c7fb20aa30,0x8a658bf7f2c8521bd105,0x786a8a198b970591be9a,0x8433efa3a64f6e185421,0x10455c6e96236c4e441e,0x8f3c148195758d622ee3,0xaa245fac851b6aa1d34,0xcd4c210791fc2880671e,0x2fa4164ce298cbe51450,0xb4c51421d48d3f72c665,0xf81175e2522ca1c51423,0x7eda528596be99164ca3,0xcc5a29bf8d063cac98b4,0xf268b484fbb5a7733ae7,0xffc9c01cd035a068ba38,0x8b46af0fe9a200e68af0,0xf3025c913f5a922ef1a1,0x88e3a9169398c78aca23,0x97e86917246f53d02345,0x84897ea04b484bfc92d1,0x40611979a80346278b46,0xf718422ae370068dbfe,0xee16a46d688858437f1a],#[0x2d7ade6a47edbd389977,0x509a3f385a91dbf82632,0x2984dd5ed0964cd2f014,0x1bf2c9917f58502d1efb,0x917f58502d1e12e28a13,0x7214237fe180194bda01,0xa0cbecb64c5f60793431,0x7d81e4d5f6c0b26596d8,0xfec1971c00832fb2d931,0x87843de021d3e1507d9a,0x1ad690cbf6c019378087,0xf76325c70020dc0313d2,0x1d1d6b50484fec210335,0x3ad56c99e0a40cb3c243,0xa01069fb100ca2f11a0f,0x410b666126afd884577,0x302211c7981108c8fc86,0x338a63b7a320d6b48735,0xa4bb8cb3482ea8d1f6c9,0x8ce01a4bd0ebfaaa642f,0x10f7b635519a46f5382a,0x31455fd90551b6210f62,0x45ff00c85af420659fc9,0xcff24ee4669f5e06208f,0xeff812221f10ef30c926,0x62415c2e4191259e6241,0x125d0240c698ee81217f,0x3cf2111249bf1d898bfb,0x2af08c5fd890decec4ca,0x39c8a3248fac9314643e,0xbcab2e0b3765a4641f1e,0x96c75dd151947dfed115],#[0xa49df28664a0f622ca1e,0x158c9bfc09c8b31c8707,0x3990591bf059907d90fb,0x2c57ae8659390eb52d8c,0x8261233192594b4f144b,0x2cf15ac45afe128c80eb,0xeb9362347ab192bba2a3,0xd8c962bd7432c25260e7,0x20b35de8e4add482c97d,0x5d066cc3be000cd54e18,0xfab320ebfc8b62397c42,0xcbf4e6c650a7f11e4600,0xbd28a71163c86831f990,0x5b7d24d021669a728d35,0x67fc3c4ec669ca15b632,0xb4e2699ca197b742b033,0xbce73199aa1caa416633,0x722d51bcb199830f1993,0x331c846bfca53230f1e8,0x99b2e0ff9b12457b4ee1,0xa453319dda4a6a9faa2,0xc790d0637d6a32238e3f,0x3fee24ea33c7dbc9d466,0xfb32324fda224f74111b,0x65ef85aa58933f41115b,0x78f52d1236cd18f4a825,0xd6cb5065a872d42233ef,0x192d76ca21fd1fdb0852,0x299e9ecc8311fdf33db2,0x918cd75e42052abda34a,0x29c62868abfc28f84e14,0xd3fc4e4263742c32b6b6],#[0xce298e2efcd891f320b1,0x5e6991bf059931aad084,0x622d3f0ae422d54f88a0,0x3dc513b9cb1e714c6bb5,0xca068c2b551454f8a634,0x2aeba8381a3ec610d6ff,0x53d035211bc45906f842,0x9ac62d1e7f35406a3ae7,0x8f2c7d48b4746f1164cb,0x5678e98c6be630891d31,0x46589dac5a3c435e258,0x42b3843e90e0661fafd8,0xf99951a4c715a2c7461a,0x802d01c5303a9805a56f,0x44efc906d00cf5cb0878,0xd66068a9fcc46a66d8e5,0x3ca88b30344ac696a659,0xc2622ca38d089561e4ab,0xccb9e039996be7b1165c,0x6f00c89c71f8c85f9e02,0x18fcc9e2923928dbd84e,0xe667a00c44bb168efa63,0xaffec690e0676f97eb46,0xd92e53e1a99673d46e46,0x75d6a45a3e7840832c66,0x45a30fe9ca8a3fa40d16,0xf119661f5a9168cbfd6a,0xae8d3d08a81ae314a228,0x62b192b5800e1996fc21,0x80489fa8975464f4e31f,0x726c83fe4388b3b9c7f3,0x94b5b69196bf84a3207c],#[0xb1cb354366a2cd5dd151,0xeee3644847f95c47c4b6,0x4a19627d920dbfdd1460,0x840cacf46419d9a4911f,0xf7a04240cf5a601913c6,0xcd7a8011a3f916b23367,0x31c7223f7646355fc022,0xf8a6c00cca7e945c47d9,0xd5324eb21cd0eb80474,0xb4c63ac640a32c65510b,0xa666fc16645dd6caa375,0x1eaa3e456728662cf101,0xc124a58d49a68a58c7c2,0x935f5e208c5fe480c97c,0xe319f70483ef44483dc8,0x85c541a1a68574b20f93,0x5d6c91bc5b4c91f02cc9,0x6f08d07c550a377ca232,0xabb2a8992ff7704755bf,0x12b34179265931bfd94c,0x3a1848e9c30cc9197030,0xe4119766a9f0716250e6,0x4121d199c72cbf923978,0x8e505466daf342711c3d,0x365ce3bee06670ee3638,0x76d606670af36340e1d8,0x2f598c92b7a78be8d9c,0x5ebbc889485b2d9997e3,0x7fca5d04067ed40aa166,0x280813430c0bc99a3255,0x1a7d598f75c21e211d1f,0xa465de217eec23d3fa34],#[0x8e04c9d905407267cd21,0x998fbe323a32afdac44c,0x9331e551fcc8c3f2117c,0x1ae324b8d569a14d222f,0x9630a70b32e669e82cbd,0x8b31a71b17d32e44add9,0x4e16650ec34c954c6c79,0xf8c53650fbe313c32c61,0x1ab93c1810a81d230654,0x81a27be0045bba492732,0xaa919abec8c79c255ad0,0xf104d97057ea2e24d53c,0xe4f2329a2281ca1a66a7,0x8b397b194bdb3594cc18,0x9e643edb0cc99159ca19,0x3ca3c1fca4b5af4d665,0x8cd3990c9afa34269fd2,0x9fa331f792064ef8c0ec,0x719f2281edfd6465cc87,0x97f564644c61b321a449,0xf82cc9885f1a0b32f321,0xe99973d6a646edb0cc8d,0x5b5199a290d99023d5d,0x325629428699d7990e3e,0x143357a003e043437e0b,0x2ed7747cbf2f440a7c5,0xcab8d2f5091c3a460c8b,0x97bcc31d1640d158c8e8,0x8ccbc3c7e208f1d5a1f1,0xe3e208c8de22c95e6554,0xbc645ad4b63ec72cb261,0xe65a3475b5ca71346c6],#[0xd71b15a36d758c5a34fc,0x53f5da2d1a2bcc42b36,0xc04bafd922876f480cac,0xa04487a0107bc0e6ca8e,0xa6f73335d48c7d40883e,0x315d6332a3dbb59065ff,0x48b4715c6c72a3c3d008,0x3cb5920330ff08445be7,0xb08479d6432fddc90199,0x1cebf5650245d48d7cfa,0x8064580f7aed32a3aeb2,0xda64d336f5c245a3d7b7,0x1ac288f7ed691bd487df,0xa54a4a1870390346d8c2,0x57592215987039ca8dae,0x9c8b481f62068b5f3532,0xecc4cdde4532b2b38e1b,0x8bd2943ca1921285aeba,0xc3c75802b47d8e43c650,0xe3ff1a4d490df4e8cc4c,0x1e717695976cdf98c238,0x51575e81a2a1c944d8c2,0x8d22d2171b103465d7b9,0xeac684adb3f98d08ebda,0x21066cb03f648ebfdab5,0x841a63f1d41298cf51e5,0xa9961a3a64226d93668b,0xf126418cffcd923d63e1,0xece251f5c087f68c9550,0x71d0cc2b2871886c3297,0x1cb2b46338cfbd943084,0x232e3ad6e234f787ea29],#[0xb1332069d36411cfd61,0xb0d91434ce195ec754e5,0xcf35dbe9230f151b791e,0xe44946f1164ac579194,0xc49987ed8e1232e33c2d,0x88f228c28fec64769272,0x722e59aa858e3a19d75,0x63f9a48da823d45f4869,0xf5848fb43f5adc471352,0xa38fc79224f0f9136a6f,0xcc552b8dd39246587ad0,0xa68a3b7eb6992b2fcf0d,0x79c1e4791d2c6a8d90fe,0x475a1c88e343f1a48c38,0x35365f0c3433207a4992,0x7bd48a19cb9f298a2134,0x99abf861a19730e6c65b,0x48fb942bee3246fd4890,0xf5642658c5363dfc6304,0xfc32132c6c491ed5864e,0x3c8284216bf58c6133e7,0x4e0269d272253c828425,0xd99df5ca8b12597cec32,0x4844679ffaf93782064a,0x869995fe38222492f89f,0x48c9bca1a227e695d480,0x6869dccfd7dad124c7cb,0xcdde5cad0ca1fd88102d,0x17e368802da1bf4ccad0,0x1808c34125bf71ca1341,0x71fea244017f122e674e,0x2b88dbfe0910f327592],#[0xb1272d93e598b09317ef,0x2a5471bada24ad78c692,0xabd797611f5756bcab41,0xd650b2d65686458dac8a,0x33624c5ad2af49c29491,0x1118f03214adfeb60d57,0x4ad5e4270a477a06d32c,0x5296c568689a9efc0ca2,0xa89f304f619c35ab3276,0xde08d9806b9328f4fc48,0x554294bae5d6dc12557a,0xa0b8665f21d5157a89ea,0xfe3a2d124e154b646f85,0xff43904917ddb8c194ae,0xb219a2bebd5144626959,0xd3a6485f0c3432975868,0xc5a76067dec563fad824,0x8918787161473a6246e0,0x8e8919bc1aba19b7f18e,0xfdc648928b8e909977f1,0xb8a6c911c5c5459c798a,0xafbf7e960923395a1920,0x64fd2644c8cf1f930132,0xfa08933c77a22e53c564,0xde226e3fe255d1216729,0x404ca145c78953424c1b,0xe544a12557d204c81ff1,0xf425e8492b3d2d11a4df,0x317fa0264ce76f84cb27,0x915b53cae126770c6003,0x7adfbc4628cba2a336c7,0x5f5aa08bdca38c604ce8],#[0x475fa5002484463b1467,0x87d1d092571f0c958909,0xee3a1244711f00033a9e,0x9a13661f1f45284903d4,0xcf44ad0b88e000d09f85,0xa50cb5a543d1800348e1,0x219d7fc08a3de1498fcd,0x99636bf3b3288f1ae38,0x58649c71225c81227f81,0x70c2194d3126f44891e3,0x747092738a6c7ba1436f,0xc2365b278891e252d93c,0xb903f069a24f4259f8cb,0xdc2a97a6b13c02304b6c,0x1b7c47dd90a46f4960fe,0x3cf0f64164606a1abd05,0xb044052d7d2fbedda524,0xe206955eb135a8fbe387,0xbb733633ee50b3d724ca,0xadf7633ef88fbb2148af,0x2067dfebb9c99014aaca,0x613158fe22249efd581b,0xecc91d9c4219b67fca24,0x8012f3fa6405d4672eb8,0x9047270b134c8afe30de,0xcf0a51584a93d9a09a73,0x2fd6dd8ca2357828d63e,0x800cc1e8bb065dd9c045,0x5eb9a8684b649a0c3d74,0xcde44ce385258096333,0xe62474c8fa7719866f22,0x5122163e413b8ce31f1a],#[0x18a6f08c0cc4e5742aff,0xc60986914ede999ba14a,0xe93322eb234c8d46bf45,0x79169e3c684dfeac0536,0x8df11a7f80a2ea8f3ebb,0xe945be3f1204f81112e3,0x7a0119b087942b0f234a,0x18499a0ff66ff2471feb,0x2f238c70a253a6499d25,0x524bfcf0e006679fd1e0,0xe91f20e0867913eaf1a0,0x40491a68694e9b654d0c,0xe970a38c9e5fae148eff,0x81a53bf4ad15d269df07,0x63decd64480ffc8d5b64,0x2ed25511a063fb35911c,0x38c1939d66293be886df,0xc9e91a58a667ae60b53,0xb0c9bd7ef5a5d3829428,0x703a66078266e850fbc6,0x3471847b0fd6fb8c5520,0x5143a4314c661e9288a2,0x6a3b0cf5c535832ed44e,0x5f8f991052898bd83ec8,0xf0a36c812cb04c8b3ad0,0xf71f1046d835d39d0498,0xde1f1048cb573a8d0491,0xaeaa5338f64e78e2a445,0xc0a1488327a7538529bd,0x689a06ea9655691343fa,0x6ceca19e630d19dc63e1,0xcfc88a672891a47f0426],#[0x12b09599336cd8accd39,0xd9db301666dd0a1ae7b9,0x21e7f2a4d01987ad50c8,0x4087d78581256f321cf7,0xdd019193f64642fd6b32,0x34fd91933ac15288cf1e,0x7e90334702632e5d1192,0xc233233c4b50ec8cc94b,0xb266ec85f28da0999adf,0xba32424e6242753d9193,0x10d743c441ae8788a5c1,0x86da6d10651e5cf1177d,0x1c9068cede5c202cbbe8,0x3c73e7a08f33e5ea2a07,0x65f98aa32f7e1b83466c,0xe25514661fb03db48889,0xc635a8f11b6047f4118b,0xff176c3e2407847b2919,0x6703b47c46033ae8232,0xcdfff8a9289243c23a32,0xf2662680f5e01c1aa434,0x11e27d70904cd31fcac5,0x835867d11bedf5d98d0d,0xa5eff669c567412ad926,0x7c05c8671c5c60c93f7a,0xc14918f140649ebf4a0c,0xcb5e45eac0d0bf7ad2e9,0x5be0d8e9433e7f69c640,0x10e2b8d4dad7da59181a,0x92b59749620869087041,0x5f8c1c7a8bd04a8facb9,0xe3e9432695ae99d9a14b],#[0x5ed134cc3307289a5699,0x4c193c5674125bca9986,0xb2a444e5b3e5b3d54682,0x14196a9accded156799e,0xd05fa963257c889c294d,0x11587a34207df2ad38c0,0x69155e04577926839ed9,0x99fdb31903cf0f612c60,0x11a11c061843417c398c,0x6f907d29f084976fe122,0x7e7ac0922409dfd8e24,0xc107234cd7a51e5024a9,0xf8c1d70961e826561b70,0x8396bc719d3560f6466d,0xf569af6e6f11faeb24a5,0x54103af1c694b54130b5,0xf164d5213417e16a644b,0x95bc48933bd32a265c,0x6286acf849209987ebfe,0xf1c0d9bb0678f13eb820,0x647a3c018a54ec76fe08,0x3d11d70a537e78159957,0x5a489a0bfaa8d0599546,0x71c292c05a199ae3caac,0x7b15d5648407cce70246,0x9078889dfa568ae9348c,0xe2441c9e8431f9eb0247,0xdadc657abae995dc12b9,0xb0a63287f0119596c3e1,0xbdc78598a567f9a4c81f,0xef0146d9b2dd530655a0,0xcc3a1851a139f7a232e7],#[0x41c73c88dc0d3c059929,0x317ccebe38bd91a2dbf4,0x85ffb27c532b025d7f66,0xb27c4abc093047812eb4,0xe22baca9018430ecc4cf,0xb3d6a3ca1f1975b24a1e,0x9c5e661afe5fb230c7c,0x92899c32096a5c00d55f,0xa848b01a5696f0523af7,0x59998ff099f558a8bf4d,0xd60490f3a873cccc89f9,0x2905f8c3fd924ceff20c,0x573af649531778a1d7a9,0xa91e4796743af52561d4,0x696a517cacc4cb39f5cb,0x22b30f543d48479ba30d,0x327087c6d56c92f32ced,0xe07ea4234f3746c35595,0x9041a171347026a96a66,0x13f3428f492a53793746,0xe58360567efb7b24580d,0xd2c02667f426c8019c2d,0x71fe8d1ec9481fe4720b,0x3eee7d5653df48072c06,0xcf8a63237f440e700341,0xceca65832a1dbd716a65,0xd925871e16a654e298c9,0x7fe19e06c927797c2073,0x40d9a5496b8e43759527,0xffab8a4b63feae51b5f8,0x93532ed7d4635b249a38,0x74400cddfd8033133979],#[0x719f5811476c74023c7e,0xbf62e85533c7f0554aa6,0x3f82aa359abf62e8359a,0x257ec9a05965fc424216,0xc5999adeaa8422bb2484,0x680ca112d3c8b6676eb0,0x952abe4ce51480d35c79,0xec08385953b718f8c385,0xd7fdc083c4952f7fb8e1,0xdcb486f1f16d1024c6a5,0xa684ae85b356ccbf939d,0x9c08f5f257d54068f518,0x3f718e465e12d4cd8bfc,0x4a9b3f718e4611c25a9b,0xcb144c665e7f262a0e12,0x88d173649810e2d2b287,0xb2357843a4cb99d7c7fd,0xa4569f84e88e681afe5f,0x47cd731a4a4cefd738a4,0xc282931bc7d7a02119a6,0xb47362039337ebfcac41,0x2509ffe39a34992447fe,0xc98ceabebfe610028b9b,0x7c642e57d8d633d607e0,0xc9ed234247c9ba565682,0xcf13a5ef41778ecc0e92,0x442139ec884241ea72ec,0x94820d1b81fa908dcf6,0xa570168e3621654e0fd8,0x925f62d1a99b703f5211,0x7461ad2d2b475be3c2ca,0x5e161093b81fa908cbf3],#[0xb7fb3e5b9f0b2a58fc7e,0x227cb3a8266e0fcd1a99,0xb21e17e04acacf6a7c64,0x1a57d5f5e9782495327f,0x4d8ce1d318c23e457513,0xa2eafcc2ef24a4817f34,0xf5c6b2259007354c0fe4,0xd5b1e292466f6fa8098c,0xa1f9d632d6bb6ba04454,0xd60ca14acac9634bb211,0x18958fb59de33acf5e47,0x6e49dbfddba5e11d688,0x72caf0f8cb52d7e64ccd,0x297f3200b2b4b12bf3a6,0x8ace369e80d1e1ea4294,0x77b6aa39db24c8f68094,0xd92627e05d7409a9a6,0x508aeae6a137e17d7cee,0xa87532d7f59ea65b7d03,0xd9242123e4243b21237f,0x2d7ec9a05965e4242115,0xace1e5912033cbf88484,0x31c80a76d7f6458718f4,0xc65dc84496bff8e1558c,0xc3c06fa401f01f211d7d,0x338624c57655bd4f34c1,0xe0a495eb5ef0523afb8d,0x6fe450a3664348fcad2d,0x7b2dd1bfc62b1221ff45,0x4bdbc334a92266bcd2a4,0x709ebbd1a50135c56fe2,0xcc68cb3ecc6d29729135],#[0x592b7ebde43c88e2517d,0x8f230b482685f8f58a92,0x7c3388254969c0e49765,0x95e695238ff0e3d5b243,0x94092eb4d98cbca9b326,0xa831ef79c311b739a8c7,0x4a9c087dd83ad5c81a13,0x63d7d62049df8c94dc8b,0x404ec84bb58fefa14ee5,0x7b5862cccd85cfe2866e,0xa0c9abff64ae06a60813,0x3b8cb83414b039ac65c1,0xc60b9b52601f82e75206,0xe334708eb7022336a4ad,0x2740965da10358a434c5,0x633115c1a0a60f64cfb,0x43f492273338434eccca,0x6061a9e89a96f64b9b52,0xc4c18ee32e0c2126457,0x216330849a31988ea83,0x328ff53444f36a50ff4b,0x11e77fab7861230be1b0,0x47c7e1e2501277fe88e8,0x6160812e7ffca8318812,0x89d457458c80264af8ce,0x8fcb592a49ae31b82c06,0x7afef7b34c12b72f220f,0x6652c892f330d47419a0,0xc3c381157f5208abafcd,0x1f3e18f01003461b9808,0x237707bd690495c3ec01,0x9acb180251a37bc0c201],#[0xe9284cc84fc19e85c496,0x4c1d05aac47f1125947,0x18c86eb40f1d554ef0b3,0xf99e7833469e0c313635,0x94b1c2fe200486f61209,0x8d250a8d03e315be4084,0x109307e26b1ea9c490e1,0x31bea200495e3c86867e,0x842fc312a0c0fc442488,0x2348666983e7fb228e86,0x136758c7dc45c490e18c,0xa7ed92079d626b1c8807,0xcfde45dfd171db240fb5,0x23cb953033efe9008b07,0x33c7e507733f92bcba,0x6713fffa9900915e1391,0x893049ce80c65df02565,0x265ac53b29133eff83d7,0x4a1f835f8a42457f4c2,0x7f50d460812a71be2c08,0x567406303f342fc5212b,0x770c44cebfac1ebc4982,0x3d65a919fc9188019eb8,0x199dbf4ec20400d03f07,0xe7e6328e136a5d7e9693,0x720127bb4ec80cd9d018,0x55f0d924a9c0873f83f1,0xcd240cc9f8c0a48cd38,0x397b71ac0ccbdee08a5f,0x5d7c804042c53cba9203,0xfa501917c610459d6204,0xade51c26d498fd280c91],#[0x4bbc2124ff8f14f8b304,0x5e441033cfdf0a178246,0x3d2d208db89e9690488e,0xc510be18303289f9a08b,0x882a0856fe1a46066c2b,0x5e05a4d0f6f860c0cdce,0x24cf5f1850471ee48388,0xd7f29f848cbebe7d4100,0x547874e02665dcf4a311,0x667114122739a8f11002,0x98424c1fe73ea0801264,0x499bd3c186244fcc42f0,0x5e4410344fd468678308,0x48103297863048233d72,0x8ce0004a2f86692066af,0x983fc71ce012445f8f,0x230b010348ebad45e479,0x8d85f707f0e402647e5d,0x3d3061a9834081e47844,0xfb7820963f6be5d04126,0xc472f8674c040d0bac40,0x45cf4ee98081a2703d59,0x5eb601267ada08babad0,0x8019c65d6383690b5f5,0xca27e56ab94b0949dbcb,0x46dfd021c1d21bd492c,0x478de926a1c1b46543af,0xcc11eb0c599966ab3af0,0x680cbb8f5f0408fbe1d7,0x29639ac65e820c995c79,0xc1cbeb68250c77197a08,0x1f211abc5803dccf3fe],#[0xbd9c599a10dd0c5f471f,0x1e5b2032ef1d7cc11abb,0xc7d15e082935c79680ca,0x9d8bfc9c08e10d3b3328,0xcbd8424b8f5d8186a7e6,0x412863e8af40312863b8,0x22e58f8449f1d987f98,0x67f82257b74a8019c78d,0xdd01967ff8e05ba0812e,0xa670633ba6fc240ab3ca,0x32e47f80ccccde4c5f32,0x645d7fee7a60929fa020,0x50f9c496bf35994a0912,0x490fed4dd0019d00bf0,0x5928e5001a97eb3ab7f0,0xd3e80626af2ba7123d63,0xc0096dec593f334f0668,0x13de6e1c495fe6c18e87,0xe3aed9220c2e8f84903f,0x8921fc959644801aa783,0x41063afb224eb139f207,0x1a66b347b72046067a74,0x661fc6402353a2083ef0,0xe5a3032cff643ee09dee,0xff6ccc9bff7af1260901,0x8451fc113b0872c0666,0xfa9091b3588204807542,0x38968c0cd9d018c6fe81,0xe08019f7fef5e24c123,0x9df3207f90310033a73f,0xf52af333387968c0ca1e,0x697e52d8197b94b6065a],#[0xe0141187b93710b89952,0x760211d80d4fc08011e7,0x2464be8c4686bb01090d,0x68ef6ef42332ee7a586,0x342fc0a08a9aeab800,0x4efbeae2a41a3bc39040,0x8a38330fe32011a48f74,0x428f1b5be325e1092b95,0x14ed8be3522649ca87d,0xc64052d7ff1c2ab18719,0xe69823e0b9129231dc61,0xb8c38ca44b8f5d8186a7,0x9a30d93c65d658b21063,0x9272a53d0a46787e5731,0x31ae24adf6f551712df1,0x67833465e3291350dae3,0xab23042cdc594394dc59,0x44eecf19236b7c6443f3,0x53010c331063ab26c7e6,0xb1fd911662aa39d81256,0x642ab4d2bf13fc6e6091,0x681acc04bb9825b7ba8,0x973f8a8baccdd7c00193,0x3e247253e15081fc2451,0x91a62ab8a9f8892b7590,0x48f8a4e1ee7a450385e2,0x9de2246dbddea8ab5c20,0xba81704cd5d821d49987,0x142759e7ef9fad870926,0x4904f610c7234d29e7f,0xcb91c2970cdbe38d6393,0xc6c916a8e119a218610],#[0x304bdfff32230e609516,0x6d0f039dc12571183bc3,0x808a35157c4ad0801a35,0x50cc334037a8a99fc918,0xe7704a9fc89883c2405b,0x34246d156817b26d0ac8,0xa9cfe48c5451a493f08,0xd049ac353d4669756f13,0x49f95a10ba8d3b92f98a,0xd819e3f91c042ea28d4,0x2565af087499733e76da,0xe60a657b73092d9b3814,0x9c28558c893265561554,0x34b77a6f3093606a5e3,0xf06fa9b03477a6e0829b,0xa6c0cf1e0dc253606868,0x46069574c99042a7f820,0x8e07f315d8474af8e1b9,0x8acebf120092bf9cf600,0x734d4f65b8cf71cf7c15,0x87a09bdec320a1d1a353,0xc77f0f6457ba3fd6af45,0xeaa884969457f8a08e4c,0x411d698b5fa09123f035,0xa0931f90a611992d7f81,0xe68e6e434651fc58ea78,0xccf61de104a0e922d238,0x126a9ffe8c68867a54ff,0x51f141277ebc1887712a,0x1e0c63ee03f811c7039,0x2266390e1953855556cc,0x337ffa187e24012a758c],#[0xd9983095beb887cca4c1,0xf30df9012003c18c75da,0xfc2aa83606893e301167,0x33ac03c19734f30d8666,0xbe386fb08f3f91bdba12,0x54ff6a822b7f00a360cc,0xa5c660951cf8cb702303,0x1988bf23b42d1a278d63,0xe0ead0cd7ee0933fa208,0xfa678188fdfd4118198b,0x4755cac0095deaac2330,0xe124103525caf88a0911,0x411ea1d762081a0bf7de,0x486fe542c819b575eeb,0x244ff6a822ec6bf445,0x380953b0388012276071,0x49a35243040d7b181173,0x494b3d0cb3c2a026d7f,0x206a2d4f41236b1078c5,0x4742ab3d04799678141,0xaab30488b06364987e05,0xb304aeea18b2441a02fe,0x12571e27598242eb83b8,0xcb2200f99d7ffcd4980f,0xc281ac521a27220de8c1,0xa87b830670bfaee608e5,0x6a3f30485e733acc123b,0x53f33c7f244428a3465f,0x90b8f03e200488f5cab,0x1e449c5a3c4c5e733a8a,0x8444edd6032e38260f79,0x12798b904249cc116631],#[0x4a6c9293d83df0b23550,0xc1883c332784b5733472,0xb956b0ca07eb7f0047e,0xdaa959a0962b3adfc012,0x481c24bcd353f328ffaa,0xcc92c2f1f41207ffb271,0x99b06a3e282447a7a3a8,0xf2ba0953f5f64e290384,0x17e6389648d6d9b52119,0x53b61b9866027ff98230,0x835f99c102437928419,0x43fe87c0a482940ea841,0xd005f98c75eb6572909,0x4e7f9ad00670f4f69a8c,0xda35b645f8e3d649004a,0x2e7c376619809ffe608c,0xd235411c0135d7ca5b03,0xc3de220f944f031223f6,0x47d4504593d56aa2004a,0x8d4ebf12effeeb208012,0xb20c324d4c708a3ecd80,0x311646609b50d630319e,0x74bff34071807c4b11ad,0x8841a123698fce481146,0xf208c21751a9b5d632af,0xe839062ac0d320f11083,0x7a62ae3bf54491b4287d,0xc6320e8fbabfc4238a5b,0x4d16a4fc0278a136811,0x865eed658e3307e1a185,0x990814cc297a46588756,0xbfc54ba0114d2b88971f],#[0x470b091aa065ff555128,0x8a5eccdff9442895173d,0x54b841614dda114ff992,0x11f2597f2226a25ec759,0x8a625e3e2e823cf59aa6,0xd9e75d0d2709042f3f92,0xe478ac299c5c6706cd84,0xd0cedec0609e19f7098a,0xa6f1123f0eb32362de84,0x504a5d6c1ac5081d89a,0xcdd4f4238a4a52e4f77d,0x9cd4aafa915143ca2686,0xc9aa7a84b98484b83aa9,0x6c66669ff175ab1f2ab0,0xf94ccca597229159b2df,0x84d926654ff992724d7,0xc92bf4c881eed251c7f5,0x6670e0411b28ebfc0426,0x92231eb10199ebe31010,0x28fab6a0e8923af9889d,0x12246efc7b448cafb323,0xb8f8c455409237f52b1b,0xbc02820958d15e538cd1,0x8bc4503e79c4139246ff,0xa24f702c97805542358a,0x8ff8849820983075c0fd,0x1805542366696c06cab5,0xacc3fa9e02752330a663,0xe23806d8eacb3806bc72,0x1c0ae3f00a58983f2250,0x3104a03815fca8076260,0x13312ffd26c4b8b9fbc0],#[0x3fbe864482c8b0c32067,0x1912e64447bf22589727,0x889ccb95233cc888edfa,0x4444b1fe6958f57d2a09,0x89cdbb4548d4176bf6e2,0x548d33c47a3ba4444b8e,0x76239fe820931d139c70,0x4668e159101ec20a91b6,0x14e7c7ab36254797820,0x787a93919eb9e40ea40d,0xd2b124bac15b2a190353,0x67ac407dd103405e23c7,0xf7d72a0e60959e588505,0x2683258cf8f08ce549d,0x659a73bfc12b6913f8ae,0x4915e2356d0ad2b3e304,0x36fd6939a40cf8c62b36,0xcf012419343f0498d4ce,0x514b9eb2c2da38fef5f5,0x59161a5519d638eaa570,0xe9780460973d66a51090,0x4712bff23051544c599,0x126923f807b4591f5e23,0x638ff2840552963ee207,0x3c1927da1709c7ccc531,0x3c83a24277c80346606c,0x529e22af2b7e3da240fa,0xfe88ddd3318c02aa11ac,0x5624ae7ff805d9204f98,0xb91138f2736503c2f8fa,0x1e69b240cf8f0ed5a449,0x9bcbd0f30c512ccd3f8],#[0x7c48a4e27d74990d3145,0xb06551f12293efae92d4,0xd346050aefa8a0c3c13c,0x846b1de32684fbb26c90,0xa20834a7c65542482696,0x9ffba3a16861293fa216,0x58b92893ff475391494a,0xb9a43fca5c4cb9e924c6,0x42bf652642b69f8c3088,0x3fd1004959e7ff016c92,0xfe45c5659fc21c4e4925,0x9c7afd20175214792881,0xcd0d3450d0adfe8e02b5,0x8ac407986134271d984a,0x7e216a6b305eb78f5034,0x4cbc8c8942c34c44e42b,0xb4f042d0bbf3f611bb5a,0x84a137d78c3037417260,0xc252142c388190a141e4,0x2420f381428be5214243,0xa670fdcab12661780914,0xa11125ef010eb97e00ba,0x91b37277c8892c4f7277,0x6dc113accb5e7e0483c4,0xe529c03034a742f9332f,0xc1f5cc0a4e7e1c032173,0x994a1ec180f00c0d43d6,0xc8e98fe888c0cf9ff490,0x84ce76d98899c63ffb34,0xeb2b35b19f7284093d86,0x5b7876143347b2f82654,0xf81a28419d7c7d20160a],#[0x5587ff81920b0fc99919,0x8c9a260fd84345f28493,0x8c262b1fc444923ec460,0xf12123b3884336cff944,0xd0001960bfe9009981a7,0x678a813441ff27111bbf,0x8004986d21be408d1169,0xca4df53d8099e634bbff,0x85aa7d38006670f97198,0x61891b870426596b570a,0xbc5b7b3209a179fec493,0x24e44872341e30022930,0xf406dfe3892593926acb,0x77cdb142cdb7fe28c8c3,0xccc3c2a0c51f7cf75123,0x92d0a56b961342719cb0,0x254fd80993638babfa94,0xc24420611c3d20670fd1,0xb26c661e07ad651249be,0x92ee892879433194bfe3,0x5123d7f56e28664fd809,0x704a558bf5dc1227fad6,0x1a791ab661222acb37bf,0x22bf04891c8d054a7091,0x7b6b619206795f697671,0xa6828234efc9ea178412,0x92b5f66e028f12a3eeb,0x3cf58324133ed7d624c2,0x5ffa0d8691143573c488,0x3fdd0c8a97fa166c8295,0x2277d0934e332df7428a,0xf434948ce2bc132aff51],#[0x850ebe597b4524346e7e,0x59c829bb8d8ae90a46e,0xdc85236a2728bbcae228,0x90c8ebdf53d6247de073,0x3e098e7d5c638024659f,0x4ae095b9824523ee850f,0x93efad5a59704a9b1e38,0x30065c870c58330787e8,0xb5a3fa4a249db4289de2,0xa23459c4e88f3ff9448a,0xef4434fc7a45919942fd,0x921f2dac8caa1713a23,0x21fc0ef60927717f6940,0xf1c7a582495cefd6c124,0xebf4b04903f7eb6091d0,0xd0495ebec697a5d04a43,0xae87adfba091aa87ca8f,0x2b7e96092aa519780033,0x8f4b049487affb048e97,0xfec64f87affb048e87a9,0x6b8f984b1c89380662cb,0x90abcfd544919f804006,0x2f13f3892f05979faa14,0x89333901765f59d67f41,0x4361eea167cb84957bf3,0xc9b8e97b4476c3dda4cb,0x979446c39e155982d4e6,0x198d74d496e3c60d59a6,0x21b1511709cd90d7092b,0xa42658865528668c25c3,0x57d2159fb669469662e3,0x120254ad71c79a024e22],#[0x4ad71c79a024eff123d2,0x2c33a00b3d77bcb07034,0xb73ff649784ffe1846e,0xd0124573abc6fa9242a9,0x9866ff637d924ccbe67a,0x34c7d3020166a2f69841,0x2a5f8100b38476b1ef00,0x124cca93bfa2bab60128,0x34a5c7f89160690b8ff,0x8e7eba2c0d246dfeba65,0x245e5485c7f893281a48,0x10a4a53751d7cd9571fe,0x5cc421ccd3525130fa15,0x6651e4a20797150898d0,0xcfcfa401a02597b722ae,0x6b1da99ebe6ac50c4d0b,0xaf43525043d5829b3351,0xd66547cf2b87328ebc46,0xa92469bf1d6b6a4a1cfe,0xf87eb7129297af953a5,0xfc63d42524f701bc2ca3,0xd342959bb2f175d4cebb,0x721ecf722179525acb09,0x7ff8ac04e48efc9b324f,0x5f21c92508fe3d00a927,0xf52924a5bd13b99a73e7,0x733263b6144cc3af11a,0xa9a1cfed600654ccc31e,0x849b3dc88872ffa492a4,0x8fbf26cc85e5496b2de9,0x909a4bec1d0d6acf54d9,0x31b859e0186728d37eb0],#[0x86df099b0cfb1ae8a385,0x290db859a130d4f26684,0xe454fda4cc89a471918,0x84943ff3e084b04953a,0x92b2f4f07919c67cfa50,0xef1919b7674588f7f48,0xd37f3c7a08e07eba22b7,0x8dd3aa103467e2758066,0x8dc003acc67827fd1172,0x11913fc880199a1f34c,0x10019bbfd1100332e3ae,0x498947fef100498ff4,0x9477e3ec012c6688fff4,0xdd4a2b7e587a826618,0x51934e893128ffdbe012,0x469ffc05341d217ffeeb,0xa0b7622fbc0a62fa416f,0x102d3148efc112250ce3,0x18d11a23a294569a67ff,0xe0e4699f1fe34b0490b5,0x3c579e58aa094d872df3,0xea7fe012225f5bf98090,0xfe011cb855967803444b,0x9dfa77f500800d307fcd,0x619f3cbd6632c7d8acc,0x125465a9a242ced0b278,0x37007b7c16619afe5402,0xcd11e9842cbd5b7301b,0x5496e743d3433e63e325,0x50ec4053e8ebfed1010f,0xfa44c77923696222838a,0xd57bc8cbfe5e0c63242f],#[0x329132affb44043d5252,0x58fccaccb1b43c89943f,0x8fa50c93d5de9ad7c294,0xbea39a08d3fbfe4d8248,0xd6464bba4937f1ad688d,0xb2da94336fe35ad1193e,0x2865e4f528656fd4a193,0x5af852b9a29a990adfea,0xc123c7347d28671c6dd3,0x61e30feb1541267fff26,0x6640fc1e44cbda07a826,0xd3433f07f0528660f6c3,0x924039b30d7c488d8943,0x858c36b6cc5ecbd5595b,0x8acabe865a2b78cdaaca,0x9be00678cfd280cb9ec1,0xbb0067682f287a0cf89e,0xfa846846fc184195a3bd,0x2ff5dfb008f89fd01935,0xf66d8019c25e50a74034,0x9f802d1299f47e108a1e,0xf7e9ab899bbf4c89c4ce,0xda019a0df08469d78422,0x1a4b085ef84b54ca5e01,0x81940b859fbe12d532e0,0xb8e4cc99f5d36cc00d1d,0x479910b8e4cc85aee990,0x267887800b2b79400597,0xb5c4cc1d7c4c85fd5d66,0xc831862feaeb31339797,0x6aa0d99a28598c333345,0x332d42a5cb2cfa9e4437],#[0xa1d9710b9143d67a8728,0x50edd8a32cc3f88852ed,0x671d2455df888931e024,0x32c9f5e222d7914e1999,0xda466fcb6a09983db6c3,0x66518bea520a133cf81a,0xab42ab427a4ad699a65d,0x492078fedd088924039c,0x61e3fdd0889234ff07a9,0x53cf87a1a498d3fc2226,0xf5124a0f83540391134a,0x648b9f4d9665df1e12f1,0xd75e38b23a8f1122ef5e,0x2b76ec1d19983eb84c8b,0x6df4813236c0f83f1a53,0xc3a120db606db039f848,0x8bb4cd1500f69987ce21,0xb161acf98722a69983c6,0xf8916b3c653c52684970,0x5236d81d7c541ba332ea,0x37149a503ab1a8f9c443,0xd196b3eb0c5933d678ce,0x67bc4edf8733899a2a0d,0xc7338999bf0b33899cf4,0xd012b4a7a4b0c54c68ef,0x494f4965314ad05e1951,0x17e2d913133c19d60d4b,0x7860d95133e7e0995133,0xc3f5e585f5c2f115134c,0x82acfd5fc406ca64ce51,0x72cfd5f9482acdcd4f84,0xb3fa5e35914a57574e87],#[0x70f0c0341567af8f56c9,0x19b1b766d2aba27328d6,0x11d933173a61169ad03f,0x98c634652f1830ac276d,0x42672f066d530675f5c4,0x248dc0e7a91ebaf0cb9,0xa8b4f894d997fe1ebd5a,0x59d0a33c998b4e1f4899,0xf205fa924af00caacc49,0xf910762b34f89c12c7e7,0x1c598763527e2704a997,0xe0cb467f4a4586622853,0x832470184aa0ce9f1402,0x8e5f831219f4e7432f2a,0x63fc22d659444348906a,0x19681e758c8b3cc1441b,0xa8c97ac593091581079c,0x3e855933c22419475d13,0x98e32f24194781a85d18,0xb475ffa3236964c25e73,0x44da607b78cccb381367,0xbbb130964c2528cd8d22,0x3377683751acf9e1120c,0xab3d3a208934771a7691,0x96b3c694d96b3dba1499,0x2d17a7a42933d27fc401,0x6f2cb487ce4216de3893,0xbc660cb42bc68684af0e,0x832d145fd021120d19ad,0xa1565cf089065e02f04f,0x46c58f2131082de42a6b,0x4899f3b8c34a13393f90],#[0x4619f9b7e7048ae7c2b,0xb6b2ad5f37f38244cbf6,0xafe8491656b9c48dc5c2,0xa4655fd0922cad617123,0x8433ff41186fe1225627,0xa32e6b08a3297a8f9032,0xdec6824c4673d652d308,0x56e28cc14ff8d046519b,0xf2494670a7de3c462fc,0xb6034a33a9f7c682317a,0xb5993735c44cf2919303,0x183ad20c812f5df91831,0xe71147e1e3c8a391e311,0xca5f1cc65e0dc49966a3,0xebcc6451e306454e7090,0xb8c4627b1d079fe42320,0x8b9fc333228f1188a877,0x7d11bc61286c33cd7f08,0x4d43e1123e88a3066949,0xc0656f2eae03307faee6,0x8a5fc2aeb2eafb2254b5,0x1180d5f517abcc6a9730,0xb52378d85e90903ebdd2,0x5cc230d2976d1f78da17,0xa4cd2e257a112ef2209a,0x99a83f4a26c99e8bf914,0x2d07e1229499e93fc26c,0xbacb5f5d59996bc31af3,0xfd77324b8a5404297f0a,0x76f2aebccb10f5d79943,0xc8fe173099a3f85c6426,0xa5ea4973f6be8a52e624],#[0x91d1e048b90d13d7f282,0x4f809e0099f47c50d2f6,0x1bbc1423a33644335466,0x188dbdee2a08e3373c8d,0x468dde31833846853efe,0xfa8c1257aec8e4619b9e,0x218c68cd0bd93336e736,0xdc1851090d4f8c95a084,0x6cb87af465183a018d96,0x89becaadd9a0e8b2f4a,0x6bc6647dce6df142919d,0xda033774c428578d13f1,0xab078651863ff22a7b56,0x133ce373f2297108ec91,0x655bebd7a011eba4dfe9,0xea8cc86d7e7118abb176,0xbf411f29091ed19dba0a,0x6bf411a0c9fd50479a16,0x78fe0456cb8be8819d6d,0x34706f08cb057faa08d2,0xc8b9a4aa136628e8d5f3,0x6928e0ca9eb986418eef,0x914790b089f48e418c19,0x2c99e8bef6e91338989f,0xcc9976596400d159f8b1,0xf88d2a275e23570400ec,0xdbe2824491f188b05607,0xcc850fe132967a332419,0x2cadc75bab2c43e800c,0x3e63c64524a1c213a2bd,0xa3b6351cb0cd1d04eaca,0x333709e04d66d11e07cd],#[0xd997021a4b266caae129,0x261466b6ca334237cd32,0x70120f3d4e109033d37d,0xba9a4868cd180e1e666b,0xd98e232bb32f70a9d019,0xe8584bd9132d0f065ce3,0x9235e1a8cb1e35e1a04c,0x3fa08c92e4f907da7b51,0x634746500a169cb99211,0x9359a0a9cb50490b5f04,0x6401fb5924f7a1c750d1,0xacd72ccdfc2699316ab0,0xb8648f8331d627e5903c,0x9354b4360c8b85b64c8f,0x2b79f96640c7a060016a,0x915a07980934361d3b13,0xf023745a5c499a34ee4c,0x494ef0cbd489cd964f59,0x57cf1a47d5ad8178f093,0x41f67e04c95da40c8bb,0x5378ca0cb1008cacd0e2,0xb159abae32b237b8e016,0x5cc6094ccd2d61]]
def g63H8 := limbs80 #[#[0x1f00006090c8600005,0x40010300014060a83000,0x1c020500814004400000,0x182c240f1000c1805020,0xa0003412030088800000,0xa0606004a4040080c000,0x420060209800000581c5,0x1442060600812010280,0x101c1216048340a100f,0x2008001e28018180001,0x400001182006029846c,0x100a190008c601a0400c,0x103e00008081801000,0x90000c020e0087000030,0xc0c0000c1e000480c001,0x8201b020042a17110007,0x500a0d0303406011e03,0x10480c100388402034e,0x10080080000008501404,0x2a000d0000291010dc0a,0x2412001201004070d86c,0x402032180600c141a038,0x704076150609c7c071,0x2130382c0c0f24924020,0x4001e1703c0e07000140,0x803c4c00000021f0102,0x6c0a000b0000a2c00,0x10484c681105000040c,0x4e442a0e80a170300000,0x60a03000127502000,0xa400000083c2c01108,0x20700814060289804060],#[0x2008340a061200c420,0x4500b308301c53130000,0x484c0903840200f0000,0x1500c004f4000cf81e2f,0x10399016180b0701203,0x12260709c84030390014,0xfc4002070b8120003024,0x9830064d0381800000c2,0x70000ca20b020ac28150,0xc1b0587c280903010260,0x3009038591a19218780,0x4c1601028ec20320400,0x120388800040282a0803,0x5048f0dc062684c000d,0x4a40a0cc402a0180c04,0x380803050001e3b0c9f4,0xa084120b1a0205c11028,0x5012080611258006c000,0x84a0182c76040b800242,0x8b6c3330000408008102,0x884c2c023bc56610980,0x182d0001a0a1bc181f37,0x1802a880218038185402,0x6e0007c02051601112,0x14003500808087842810,0x18081811010000434018,0xc2c80c16640485014010,0xa090b01402010d010383,0x386e650780600198440,0x840fe11418b43eb30507,0x10280a0d000e4640100,0x9d146c13078200601],#[0x67040642a020099c04,0x8b6f73300004c73810c,0x4118080b1c014601d578,0xa17184380f1100802490,0x230080802370081cbc0,0x4140417841b208091ec0,0x1284c0236b201c070300,0x7b8207000a9800041804,0x1c0004804390400d2fa9,0x1e0c0584d1c0d3541800,0x10063984c0000041cc,0x68306c07398540e0f057,0xa070c2f8060100000421,0x6198b040088500000025,0xcf200080180602059a40,0x9fc0e296380c6e020509,0x8b8b64ea8967c3586562,0x4b6179698c94b9cd31b5,0x225a000004667cde6a16,0x528334c16d633c67f0f6,0x486b41d60000,0xb794ad4bbe6dccdf9e6,0xca2b7aec2bde93de44f9,0x6a60000003f3b0f4ba92,0x835e6ca3eb787ab41815,0x533a08d11adb61b6bc37,0x70a880001bdf00000000,0x53dd800000001cf18000,0xe4e13c7b496c89959093,0x68b600006bba,0x3814fd15086bc15623d5,0xea752095e9d5d3224348],#[0x24705557820394dd,0xb01ef1d8592678a5a03e,0x80001c90dc40ea42eae5,0x327d7003e2fc3498f4ae,0x6035535de3d053f28000,0x99bd18275d410870e048,0x71c9d50d132400005aa1,0x897add830000392f8316,0x2c5919bedcbb014b0c2e,0xebeec37e80007b5c8201,0x11ddab2504f2833ff32e,0x4a2560f5b2aaf48f5b5c,0xa4dd69dd7d7aa03d580b,0x23350c4b5544f4f45d80,0x58e2501f6a5541866ade,0x63d7da218cd98b900c6d,0x92148b84b4c303f58000,0x127a0000305e42259a1c,0x6502ed56800044f2508e,0xc9cf0c6323e262bc2cd7,0xe830e96112f200004a15,0x398c52dd284894c8344b,0x1aa9122984ed8d0dca85,0x922bc578b0b280004ce8,0x726418ba344dd9ece267,0xa2c828ff3b90ccb1b43a,0xc0177b9b80005b6d42b7,0x80000240a545480e3c9a,0x909fb4428000251fcb4f,0x8d3f31cad1ebab9f34e2,0x733d0afd4849dc97c120,0xaaccaccf8463c87dfbdb],#[0x70b38357dc4e624341ed,0x6527126a00002b028881,0x71f08000000003538000,0x708afd68dcbd99828000,0x88559449aa8a9cd80000,0xfd8b7a3aebd40000318f,0x72ce3c4c800013c4b95c,0xa22fc50f5bdae4ee0000,0x3c09000059a7a984,0x15f0000497f80002936,0x59b610d20cc9d99f,0x507c800069c7e145,0x70c9a09e3a3900000000,0x418859d3542ae8ea9030,0x80003be99ceeabf4c4c2,0x42c0747e993838fd527a,0x41dee17300002007240a,0xb0c4783c73749294c383,0x5b6c9153d57c683109e1,0x1bbca8c352c439ee0000,0x50034909a168d336fa3b,0x9f880007a094d19,0x12be00000000116d0000,0x610c8000000000cb,0x80004898e08700000000,0x362db32831118ae4301,0x800000004072208fdd87,0x783581b18ca4124eb4f5,0x2bcb8000023662a80000,0x804cbd7480bdfb0ecaa1,0x7a3c205163c90d4241c5,0xf47e457904be83816d6d],#[0x800000002b4580007cda,0x214dac47504f755f6045,0xf1a77ae7800008e40000,0x290d6bcb5a24,0x7c583a8101e78000,0x89b80004b721d670000,0x2355bcf57ac1e25b9557,0x8000757cb245e077308f,0x3ab5eafca252e07a4d1c,0xebe39d6bc280ebc3e061,0x52d5d54780003d43,0xe241b11061b980006394,0x8000309acc52800031cf,0x59cd9a18146a1162d15d,0x2aee749e83ed00001c0b,0x599614b213976254e223,0x98f943c550712d090000,0x73ecdd777277133bb2ef,0xd4e58000000011cb8000,0xfd0b4c1a0d5a00000d6d,0x13b0a0a3018b80003261,0x6ab8637e758800000103,0xc04000002a20d2464009,0xe8e080000000118b33c5,0x582204129b9ffa107530,0x73cf11a65246acdb4b3c,0x34b00005aaa153e2d36,0x15110000000040b242e1,0xf4cf0000792cf96c0000,0xd2ff88488a70372,0x7460712e39e24ad38000,0x78cbacd32ac480000000],#[0xc0afcbc358ef28648000,0x1bebe96e149692350234,0x5a760465dd127c698b80,0xf1cc72b0f81b922eb82d,0x7aa220b1402b3b7fe32f,0x9d0edb372359a3b46420,0x781854efc3379c87e96b,0x508858ab3e1620f,0x80004906f1c400000000,0x45554ce680007b198119,0x5c5a21f33cc468c58ad5,0xa9185b8d8000036218d0,0x80001d003bd880006a77,0x63e80f8af0e1fdf931,0x40bd63fa804e8c046d4e,0xc112b2056c3bc05c5892,0xc23f88d42b0d82336103,0x7af5800068255399,0xbd28052bdbf9800040fb,0xcbb580003ba488f9,0x301d80003b470000,0xdaf9ad5fbd0cd3b859bf,0x29e3bb177507c2e2db27,0x61e869e9c2593a024044,0x15a013579f6000079af,0x7d61b47672523ab218f1,0x6b1e18fe5a37d2f2a4e2,0x73fcac055b6d80002a6f,0x2d49500c3b2154dc5898,0x83bbc8f1f16800000295,0xd8ac70a5056f31d75276,0x1a38091631c500006388],#[0x30a11c1744d5abaa,0xf145d9f3aafb5889dad2,0x3a6df18142fe6d2df4d8,0xd1dc7bad8d5371e4aca9,0x54a52b1ac90b5535d477,0xd199900628d8041,0x1499e32b910e252a1147,0x4abde4e184abe4b6,0x248bf024800043f90000,0x40de085f4a8f,0x627c3a9a746b2213d004,0x6248d143db262078444a,0x8880c1b529373ce60069,0x750e7ab8aba43870082c,0x9c456107fac21940a962,0x239da9c60989f042434b,0xcc79c6b8b3acd3550ec,0xeb808a9e85462d750000,0x934d4b1ddaa33273b95b,0xfa9d6238d49342df4c2f,0x639100006303f00554d0,0xc525381980003cbe4036,0x2623a0a00006be81520,0x4c53241544b910a819de,0x9082034ccc73f85eeb14,0x5b93a445c48c14a72b97,0xcb0f84fb51397d85d4eb,0xf527a90d8417c810203d,0x10b7945abce40105,0x30d146c6af6e091,0x337423dff00ee4370000,0x63e08892854bf4ea2915],#[0x23fa1222bc72287452ac,0x392b0321e88eba828000,0xc0cc8b8e9cb772e23ab5,0xd9e04bbe44ae0bc8eb0a,0x8ca2ac9f028c0532ea47,0xc4111713d8998f8e313,0xf0f3bc0321777994cbf6,0x20dbb525a8b180001038,0xcc020157b957433d8000,0xc178ed63e8d3a419dc6c,0xd4823534b4252813e37a,0xbd336942442080004088,0x6916e882ad4688d31a56,0x8c9d616f8c92eb10eb1f,0x155b98b081333b7f0ae4,0x1ca638d8350c155d0000,0x5a1700db084b9c61721c,0xfb3e49c3e135c4888bfe,0x31d455441bedc394bc15,0xf2f86ada9c3a8839fa80,0x197b84cec26d4a44b3a1,0xe11d78e3ccb0e2c77bc7,0x80003ad6f341ecd7d351,0x348b08c7009d84aa2c2,0xd450800052930af38000,0x2ad080005aa562904b07,0x78e7e25b7cfc0c3e,0x80000000000000001169,0xdd889bfeb9e080004314,0x332c00001c081c305827,0x800000000c7d693bb491,0x38476c0cc44240c71873],#[0x4af1c9f0606580002ae9,0x7b0bca9752adb03a62cf,0xeaef3c08c9500000243b,0xfc51e367a4c77b0c834d,0x2ea92cdc53b0a197d5e,0xac000000151289468000,0x58a6996028bea38ae2ca,0xcc50152673ec4363d28a,0x8aed1be1db032934ac9c,0x6b4a3b44381e0152d458,0x22ae349a4344892010b0,0x32fe9caa4be4f149c923,0xb2c5f84c454588df9c5c,0x7a7bdabb80a270c038fe,0x98aa9ac088e17bf68452,0x682f53dc1bd114a7d21b,0x21517028fc1b12990000,0xdcd95974d3522af7f14c,0x34214caccca251d6fcc1,0xf55260b82be0257df9c8,0x3093805351029a267aa9,0x3199208b79609d81a9f8,0xc98cabb66b924b711382,0xa200906693603a2d2265,0x3cebdbe2f9822c16,0x89835433093d889eec81,0x288d7a05e123aaf49a1a,0x934134d3a03ba233e9f1,0x60d6b89d8d781a142bce,0x6b9e800074fa14648000,0x1d16f885000010845cb1,0xb48ce4f78961bc0ad96f],#[0x1d17bf800000afbf4ec,0xa7ea48b18ab0813,0xcc39800070c080000000,0x6c6ab3b6b1d2,0x8000297ef405d50409c2,0x15841b6f58c6085fe826,0x1350c86d800024448000,0x202b800058c6c8b88000,0x1411a46731f2b2c35bf4,0x9d7653593a10dccc7443,0x8b04fa706d347a0d3c83,0x2d3a73500000254ae0c8,0xfa50022050d5b812b8ea,0xfa6b9820eb68cbaf0c72,0x927f81c000003229098e,0x189944bd6bc838495b73,0x156e50acbd6a5371175,0xf983d354d1e8e9abc8cf,0x900bbbca2cdeb429982e,0x1b92d0ae99b74875ac48,0xac1adabae95e99fe63f3,0x73022022e52484226b00,0x6ba5f1640258740e3b08,0x7381e9ed22e03d3cc95b,0x856e8bc28281a2ad69b3,0x1529c537fad894e4f00a,0x7515b0793bacdb5eb45d,0x532b358ca02064697045,0xd37bd248039c7d3ba808,0x9a4dfbd2ac0128cd703f,0xba98c5224d13645388e9,0x8c872aaf3526945e2c76],#[0x5a5d3a8eaa514c640b8b,0x291afbf7429b6a915ab9,0xa47a83ee785dd32031eb,0x64c6331a0adc28b59a2a,0xe22e6ba63331221d6862,0x12a515442a2846503db,0xea281051a8687b630c36,0xa8ee7071bc8ad932cb91,0xa506212d2067440b831c,0xdd22ca3e752d62c9d2f8,0xdb7b72ebc25cfd291099,0x441f993e259c38964bf,0xe49c7832b03804b9a486,0x549435647c235aa4dd8d,0xf80178c1421fb3574566,0x7d4f23abfd38701fc1a6,0xfa82348fc3b3516e9d5c,0x50a2ba6f8492699efc62,0xfbd65334d24aa3ffe304,0xf81b1cdcb9a1702113a9,0x5c23ebfc0c5512b4b92d,0x6baef571bd013d242184,0x50f4648500007c14b8ce,0xb06b3a0602638d9b06f,0x1ac880004c3cf269844d,0xd5869d31607300000000,0x6c8eeb10527180001815,0x227108d4a8be38580000,0xfb2a2a83a278d44063ae,0x6b158a5c69764b272550,0x5383e579c3b0000029ec,0x860c2e7697a08f20000],#[0xe93130c943c1d187c0cc,0xe11b84569a5e3b5b5042,0xb54ec8e680001938e21e,0xa4cc4c38b77113a6570,0xe1268c1ca23f60f2b340,0xb01971a9e13e701080c1,0xab394ab20c274351034,0x3ce3152ca8f6dab31a57,0xdcac6240496ad1bf8000,0x12ecac576806d9a42d0b,0x600a11a83a43e2b1,0x3b551cd600007504ba04,0x3be413f0b51b4a495518,0xba79206300004acd0000,0xcd1e1cc4ad3932081b9c,0x92e19a0a90e3740083e8,0x1c1278eb43dcba7b6b31,0xb9889c5b69ab4d890000,0x740ef8df63f209d03825,0x1c0f645ccc3f8a26c42c,0x822c442b0bef6325fcc5,0xb88cbc8e49652575e1aa,0x6cf16287181ca2444b6f,0x3457cd17ed39d2731117,0x9037e1aca8bf893053b1,0xacba0000000058ed513f,0x5b11800030e894277ae0,0x138689b4c407d4391d80,0x24c8fabf8179915fb9e3,0xe1bb1928ebc080001274,0x435a6b3811fb54aad3cf,0x8254381680007a0fc98d],#[0x4c7f31dcbd3f9c03ccfe,0xb174583aaaa0f0da8000,0x36564708948d1944a51,0x3bbdcd3398b691d96a31,0xa0dc929c2a60ab450000,0xd3a5344814752001ea36,0x80003114d32f0000722d,0x594468e1a115e01a8274,0x925eb00d32691bc99b4e,0x93f51c9058eeb0291191,0x23cc21e444e892150d0f,0xa25321f9b8a60a0760d7,0x141c255962d81d5cf377,0xfd59a856d833339e3d21,0x2d700b46447fc4f01398,0xd4794cc900001d3d7ba2,0x21aa72b2800000002cb7,0xbc6fa19bb200087f7119,0x7b9580000c5da8a384a5,0x800010570000000034a3,0xd08300000c89c461eb9a,0x24d40000493aa1d25844,0xcc5980006a01d33f1ba8,0x6a63b3a2d36480002b23,0x905544ff3b4ec17c88bc,0x39500002c240a93,0x547473533318dcf6f197,0x590200001cdfb8af497f,0x800073e972319acc1497,0xcc0d79665c3d80002d51,0x6506bce082ceb8c7,0x84074306000000007955],#[0x894309b87a7580005955,0x7485aba3,0xa25fa085abd961956090,0x301451ba6a89c0f509c8,0xd07601da80007bce0000,0xfd103ab753bd03297401,0x2c8a01d09bbb7a667baf,0x8d236d512b30530c6429,0x7bd3f3efed49ec55d06e,0xe0e675058cccf8230000,0x4094380638a4e2470582,0x2ad41bb7b1e5e05cc83b,0x49a500007bfd0000,0xc56200007d021369d82e,0x68bbb41100a7800020ba,0x900b8e523a8f425bb99,0x590100005542d06e,0x58ca3bd4a9b05adee875,0xd2a8d82f800013880000,0xb1df6128246e72a73804,0x2185331ff9639a96d4b3,0x442874c5f15322d9135d,0xa077d261110553439abd,0x4a11800022c54d7b92c3,0x21b7e564ca3db8ca8000,0xea7d8be6105d3c71454b,0x39ad00004a967159d122,0x48cddc193096f87d254c,0x8000595afbb922179032,0x5a3d0000193e8cad999a,0x80006c22800000000000,0x82dbb101a05bfba6d366],#[0x52cfa500893d2872e1f5,0xd51a0c24c9706d143a7e,0x942cb2f343cabd3ab074,0xb0a5ced00860b8f7c75,0x124e7ad3651db0e0,0x6936c2eea9bc902a0000,0x75866bd30ad1a980cc3f,0xe10f92a7fa4b6abeb3ea,0x3c54c90c62375b1272b6,0xb06aa1a3784e09cb1caf,0x3378f13c3cf3697b3471,0x18549aafc10a5cec3b05,0x2bac099252ac811a5978,0x2acbe44a90d8d290802c,0x53f140ddc554a10aa4f6,0x216b64b8357ee5730000,0x9bc250bb64b31c918d6e,0x20aa6186a219835f2410,0xebe540cebd71413244b0,0x6ab9800049a1ab4a911e,0xda5603d59a9dca3e91f5,0xa13ce9bdf0598034253d,0x5227c0d93ad7a83cd44f,0x62892811e16751669cca,0xfa031d6a62243b424368,0x5d14fa50fa223d2a,0x246de32280005b70a1a2,0xaa0b6d2c3a67486c8913,0xb6c1b151d36d482b329,0x2d300000428411aedad0,0x9b5ff2d63284c94f74e7,0x42635c44000062984207],#[0xe1d3e93b2213714a19ef,0x2239a58c11c4a9e2dc80,0x4ac780eb800029f9,0xb8b9487e49c0c9218000,0x7bf00b9a34bbb4fd71ee,0xbab3d55800033b52959,0x13b9bb491097a57a1109,0xec83398376,0x3d4071b8c19809299d4a,0x88f80d38c2a43ca6faf9,0x406c4aab2d0a6d2b502d,0x249800005ce05249a0d5,0x800014fe38e93ca0e43d,0x80000000000000001358,0xca0211c000074b6c83e,0x42d342f3bbfa04a3ae5,0x5a940c66800000004d5b,0xdc961a30586d6a7f0000,0x5402d9120000000050fa,0x2b1c190750da50fca111,0x80001446000058f72410,0x43a74a9221a49c04,0x219c921689b1000012ca,0xb9d9800053f190bf0000,0xc541375f88bc843,0xe0e2a8b3000000006c49,0x78d1bbdd6c8014b483a7,0x1831d31b8a8d4b9b0000,0x856f800008fc2a6e257e,0xf89c4d73e2065b2e0d31,0x1b8d19add853fb565086,0x9c9d800043ff000004bf],#[0xb0f0b36410abf36b38c4,0xc904f56c597dbb51140f,0x8000029ada0e142a6d21,0x6a9be129000034a8a565,0xb028695842dceb1e8000,0xd4da4c626aeda11e59df,0xe29f60f0000062ba7a8c,0xa45ff91da1c280002bb1,0x692aab8e1a4d18022cf0,0x629fb94a89f6954d,0x80595a4c08117c8471f7,0x8000010430ffbb20e033,0x146694180002b2a82fd,0x3572188180006cf70c26,0x4b09b11b799c7a649b6e,0xd1b0dd0550d0c9ea444f,0xa387020ea1bc69c70360,0x5384598a40578c32100c,0x4c3812da38e70000,0x707b7cf9b0e5d9f47c16,0xf4b44a111c737087d12f,0xb346bac162887d87e270,0x88ad23c018efcac672e8,0xc85275587c7de4f4db76,0x51fc7d839c8869db341e,0x1255e9da44d6b1a3f2f4,0x2286d9c368c57a62bb1b,0x5566005a93f588a409a,0x4371b1eff428b8dc2520,0xb03754748b0f5861b234,0xb11f12fffb12e9eae576,0xe4341840f33b48a96d1b],#[0x485b73e5a4e9ba6acadf,0x3c134ae9e3d7120c656b,0xaf012d2e4fcd47a70a0,0xa2b1e1ccea2a1a87e4a1,0x7d2e6b1d104b2d617b40,0xbd4824f3b2e30510f07c,0x792c1c7743b2d807bbf7,0x42724972c07bf9894b32,0xe0d2fcc07cad3aea44a8,0x6b433a09d83f79a94bb4,0xb92571e6d84358394313,0xa4a3164a954832dd050,0xb8c4d4181479c1d0000,0xf396000031f1a29e0000,0x1478706451b26d2efa66,0xda0dc4d269badd170503,0x14e7a99139fce27c8295,0x124124a1c57f21fe819a,0x1493f97d7c9bb3931366,0x14833342a81d1c27c4cd,0x19b4717780007338e94d,0xf14fc560dabf433ea1b9,0x91f25bcdb85adb001d52,0xd55e71277c34d9a08be7,0x33d839c6fc146b09738c,0xa4e5157452b6453efa3a,0xb3beac68a57d5c511d58,0x52e87d7f94fafce392a6,0x26b0d6a8c389d8a7431,0xe2782d40e07ebb344895,0x99065a651846e091ec47,0xdc5ed23b999e504dbcc0],#[0x6bd0805a7b4f44dbf432,0x1a1b6446a94979398af1,0xf142dcd280a413828d60,0x8548e083f094fa86604f,0x8379ac18629cf8fbba72,0xb361e3c7c1631d4dd802,0x8d3c6144924f8a453a97,0x3c86823cf940055d9208,0xb8bcb36be1ac615d0000,0x915093f8f4df03ad74b5,0x432800007aa3ed03c566,0x395e50298000638a2aa0,0x212218886d13ecce,0x8158e15c0000524f2c5f,0x58602ad10000425ab92e,0x318e3cff8431a369581a,0xf8e80000049fa8fd8000,0xcb3580000000000044ba,0x1165ba42617e20b4a9a5,0xd9e565813818ca0280b4,0xa18d82dd800059d4e55a,0x4199d09d00b9f49e64f8,0x190e51d2af74468,0x83d25bfbd39d00000af5,0x80006cd17ccacc8d6862,0xe32ce4c2ec1f7bfd9924,0x9ad76324a9e16b365cfb,0x219d4c9961e7516a6406,0x1b56d023bc7980000000,0xc111e0b519a29ca98000,0xc31900000a12f86a01d8,0x2572f98ada8f8bb3d817],#[0x24b8e307194100000000,0x44a4a069bad99bda4b70,0x821c0dd000000000000,0x800011b3ac7c31ca63c6,0xe99b5b8999143c7bc89c,0x5501bc26a3288000402a,0x8c9b0000026ee18f1b54,0x908909873c849a58ab26,0x8c0dd8368bd1e3a30a23,0xa1d20cf9be61ce6308,0xc48da878fb96d93431d5,0x505435695afa8000208d,0x634998ace37500000000,0x151ad5825569f879b1fd,0x640c2c6efc4c60a9cb23,0x52e69d1f114e89790000,0xd288e4358000551e8866,0x6baac1802c6f309b1ba0,0xca2f30b72ccb31bba865,0x6433b1fbbaf60230b90e,0x2afa244eb84d00002d54,0xb21df24bf1720b6a34bc,0x8000521a0b05d87fc110,0x5b0b4b338cd480007d84,0x1cef40d7b37c49b28000,0xebba1b4c75431a1f0000,0x4be74b855d28,0x7118aa5dfb5bc23593e3,0x3d8ba8de800070804cf8,0x2a1e00000000,0x6318637a648900006cd5,0x2d53c41be36589dbe9fa],#[0x294cb192eae3d3bc0000,0x697180007ba10000,0xc9f48000657b136a8000,0x221447cf058ecc6e0c2,0x486fda99eaaed3cd,0x43eb000000000cd00000,0x80000975d0688000032d,0x8000301c7b85f3ccf196,0x800049d1facb0d189176,0xf85613bf642d80002c3e,0xe9c14b52b0165876a317,0x73333197d421f253bb7c,0x3090e37d53b25924,0xf52f233903a93bfb5d50,0x82eb4413d1e963010173,0xa330d478fd4cb0121257,0x4d7790cf800000000c1f,0xd8f313c12c56000038c8,0x65470ae40000314828c3,0xca18f4afa40651526bb7,0x9b8780007a79ad071a85,0x95119c5be1216847f133,0x10ed942bb37dec1da12b,0x7b6efc60c8528000,0x39faeac9605000001108,0x34950951dcb50a8b910f,0xdd6500419bb8fd23e373,0x5108dd8d7913,0xa2bc9808ea272b6760d6,0x5a68000034fd,0x80001d32000000003bc4,0x300f0000220ba4b2c4d1],#[0x80001117f1a000000000,0x800050243206800038f7,0x99ffab5ac970cd16222c,0x428e78a083eae90bb347,0x48ad8000000000000190,0xd5853aaba19d80004046,0x511f8c30f2a58000326c,0x1c3c00001d6ca9c95b98,0x241e51c18998d1308000,0x987afc18ac81800031ae,0xdb16e212530e55680181,0xdb3c800011279185dccb,0x11a8a0fa189f451c2a68,0x19f78bd9f17c21378000,0xca8b4925e509e0972896,0x800000007a320000600d,0x2b8fbc36999fbae6094b,0x800031af80000000494e,0xf9ce9ac6ca32c067a11c,0x3800542e59d7c495,0x3abb000000002a6c41ff,0x6228800000003508,0x40e4b16dca9193c68000,0xd2048000000062b04aff,0x409d443d4bc80001567,0x12a63386154fe9931a5f,0x7ce9]]
def g63D9 := limbs80 #[#[0x1485010c42100320c020,0x50941501214811015053,0x90a40882105515254550,0xcc321c825494e5294243,0xd4b51d4342d0740ccb31,0xefdfbf7efef6eede7f54,0x620c9620cd610ffffbf7,0x61182650c1650c6630ca,0x202a920282659016590d,0x62290622a5512a5412aa,0x63290632936229262291,0x65291652936429164292,0x63512625116252920513,0x61029200116551164512,0x65011640126301262011,0x422e1422d3612eb202d1,0x642d1642d2632d0632e2,0x6156b20553652d1652d3,0x65551645526355162551,0x63762427614275161751,0x65753647516475263750,0x62051620516105365751,0x627d1617d16505164052,0x647d1647de437d2627d1,0x620d1610d3657d1657d3,0x650d2630da430d2620d1,0x63353623506235361351,0x62591615936535165350,0x6359a435984359262591,0x62891618916559164592,0x61191658926389262891,0x63196531926219162191],#[0x61417514155141164192,0x54410634136241062413,0x62651616536441754415,0x63656536545365262651,0x61955519516565164652,0x54952639526295162951,0x63327213136031164955,0x65313643116431263310,0x637a7317916079365311,0x65793647916479263790,0x6281f328116081365791,0x65813648116481262811,0x42399423936039365811,0x6539063393623906239b,0x628d9428d1608d365391,0x60451658d2638d2628d1,0x62450624575245552453,0x54450634565345453453,0x52991609936445754455,0x63996539926299162995,0x61091600916499554992,0x65093640916409f32091,0x64851618516085365091,0x60113658516585364851,0x63112621194211161111,0x423d3613d3603d165112,0x605d3653d1653d0633da,0x645d2635db425d1615d1,0x6191160913655d1655d1,0x611d1601d16591263911,0x631d6531d2621d5521d1,0x6149360491641d5541d2],#[0x60693644906349652493,0x53694536975269161691,0x64697546955469263696,0x639d1619d1609d165691,0x621516115160151649d2,0x61611606116515262151,0x65611656126261162611,0x62211622116121160213,0x616d1606d16421554212,0x546d5546d2626d1626d1,0x622516125160251646d7,0x614d3604d26325262251,0x60710634d3624d0624d3,0x63712627116271161711,0x62a1161a1160a1165712,0x202ad2029263a1262a11,0x502af402ad402af302af,0x422af322ac322af502ad,0x522af422ae422ad422ac,0x622af522ae522ad522ac,0x432af622ae622ad622ac,0x632ae532ac532ae432ac,0x542ad542ac542ae632ac,0x642ad642ac642af542ae,0x652ad652ac652af642ae,0x4252f3252c3252f652ae,0x5252f4252e4252d4252c,0x4352f5252e5252d5252c,0x5452e5352c5352e4352c,0x2102f5452e5452d5452c,0x5102f4102d4102f3102d,0x4202d4202f3202f5102d],#[0x4302c4302f5202d5202f,0x5402c5402e5302c5302e,0x302ef202ef5402e5402d,0x502ed502ef402ed402ef,0x512ef412ed412ef312ef,0x422ec422ec322ef512ed,0x432ec432ee522ec522ee,0x542ec632ee532ec532ee,0x642ef542ee542ed542ec,0x3156f652ec652ef642ec,0x5156d5156f4156d4156f,0x5256e4256c4256c3256f,0x5356e4356c4356e5256c,0x5456d5456c5456e5356c,0x4076d4076f3076f5456e,0x3176d2176f5076d5076f,0x5176d5176f4176d4176f,0x4276d4276f3276d6176f,0x4376c4376f5276d5276f,0x5476e6376e5376c5376e,0x6476f5476e5476d5476c,0x2106e6576d6576e6476d,0x5106f4106d4106f2106d,0x4206d4206c4206f5106d,0x5206d5206c5206f4206e,0x5406d5406c5406f5206e,0x507ef407ed407ef5406e,0x417ef217ed217ef507ed,0x617ef517ed517ef417ed,0x427ee427ed427ec427ef,0x527ee527ed527ec527ef,0x547ec547ef627ec627ef],#[0x647ec647ef547ee547ed,0x210ed210ef657ec657ef,0x320ef510ed510ef310ef,0x520ed520ec520ef320ec,0x5036e530ec530ef520ee,0x3136f2136d2136f5036d,0x6136f5136d5136d4136f,0x4236f3236c3236f6136d,0x5236d5236c5236e4236d,0x6236d6236c6236f5236e,0x5336c5336e4336f6236e,0x5436d5436e6336c6336e,0x6536e6536d6536c6536f,0x415af315af215ad215af,0x325ac325af515ad515ad,0x525ac525ae425ad425af,0x535ae435af525ae525ad,0x508af545ad545ae535ac,0x318af218ad218af508ad,0x328ac328af518ad518af,0x528ae528ad528ac528af,0x211ad211ae538ac538af,0x321af411ad411af311af,0x421ad421ac421af321ac,0x2142e431ac431af421ae,0x4142d4142f3142f2142d,0x4242c4242f3242c3242f,0x6242c6242f4242e4242d,0x6442c6342e4342c4342f,0x3166f2166d2166f6442c,0x3266c3266f4166d4166f,0x4266e4266d4266c4266f],#[0x2196d2196e4366c4366f,0x3296f4196d4196f3196f,0x4296d4296c4296f3296c,0x6032e4396c4396f4296e,0x4232c4232c3232f6032c,0x4332c4332e5232c5232e,0x5432c6332e5332c5332e,0x6432f5432e5432d5432c,0x437af6532c6532f6432c,0x547ae537ac537ae437ac,0x6082f547ae547ad547ac,0x4282d4282c4282f6082c,0x5282d5282c5282f4282e,0x5482f6282c6282f5282e,0x6482f5482e5482d5482c,0x603af6582c6582f6482c,0x323af603ae603ad603ac,0x523ae423ad423af323ac,0x623af523ae523ad523ac,0x433af623ae623ad623ac,0x633ac633ae533ac533ae,0x653ac653af543ad543ae,0x328ec328ef653ae653ad,0x528ee528ed528ec528ef,0x6046c6046e538ec538ef,0x4246c4246f3246c3246f,0x6246c6246f4246e4246d,0x6446c6346e4346c4346f,0x429af329ac329af6446c,0x439af429ae429ad429ac,0x610ae600ad600ae439ac,0x520ad520af420ad420ad],#[0x540ae540ad540ac540af,0x650ad650ae640ad640af,0x4286c4286e6086d6086e,0x5486c5486e5286c5286e,0x6486d6486f5486e5486d,0x5212d5212e6586d6586e,0x603ec603ee5312c5312f,0x433ee523ec523ee423ef,0x543ec633ee533ec533ee,0x605ef653ec653ef543ed,0x525ed525ed615ee605ed,0x635ee535ec535ee435ef,0x655ed655ef545ed545ee,0x5392c5392e5292c5292e,0x604ac604ae431ec431ee,0x644ac634ae434ac434af,0x436ae606ad606af644ac,0x646ad646ae636ae436ac,0x6062c6062e439ec439ee,0x6162d6162f6062e6062d,0x6262e6262d6262c6262f,0x6562c6562f5462d5462f,0x606ed606ef6562e6562d,0x646ed646ee626ed626ee,0x624ec624ef604ec604ee,0x1b802000200002c634ef,0x284046807d00cc01480,0xd024c040c06f80cb015c,0xf901c9035a06440b9814,0xa5813e0260047008700,0x906800c7818102dd056c,0xfd03dc07860e701bf035],#[0x12082370456088010681,0x40a1a13d426984bb0932,0xd8859a0afe15782a3052,0x195c31c861f0bf017602,0x10e2e1bd836886a90d00,0xeb07b80f261de03ad873,0x223c4368843103e1ffc3,0x5125e243447788df1160,0xfc89da137626444b5095,0x2a7053f0a66148c28884,0x166e2c6c5788aca1566,0x20be417882e6c5b90b6,0x327063a0c50185c30506,0x51a86348867d0cd91978,0xfe8de51b96369c6c30d6,0x3a7073a0e4f1c74388c6,0x1e703c547818ee11d80,0x10fe71f943eb07c48f6,0x429c8459066209440948,0x72280449488410e4218c,0x111e5238c46848bc916,0x4ad894c927c24a048a89,0xa26b64cec98a12f925b0,0xd13fe27d24f149cd137,0x5340a59148e28ca50fca,0x32ac2551ca92150329bc,0xc160b2bd05718ad5158,0x5ad8b4d16742caa58c8b,0xa2ec25cfcb9116fe2dac,0x1918152fe65f14bd3178,0x6384c5d189130ee6130c,0x2331665a0c9f992131ec],#[0x2d9a37342467d4cea99b,0x6bb0d621ab2352869fcd,0x137366dd4da91b2f3612,0x351c5138527004df71bc,0x7438e759ccc39507204e,0xc3b267608eb69d4a3a48,0x1f9e1d3c0e778cee09da,0x7b00f509e803ce07944f,0x83ee87d38f929f0b3dd2,0x25a02d400c7f80fdf1f9,0x839d06620aa412281c50,0xb432c85cd0a8a12d420e,0x29a241443e87e10ec21b,0x8bcd16ca2b1450c89b51,0x9472e8de11aca330462e,0x30a447484e8ff91ee23b,0x93f5271a4c3494091ed2,0xb4b60961d2b4a5434a42,0x4226614c8c988d2ff25d,0x9c6937da6d94d7c9a813,0xe4f7c9e793bc27584e72,0x3fa85a5072a0613fca7d,0xa46d48028e75192a2a14,0xf5376a6714bca95d527c,0x3d2a505468a82d4fca9d,0xabf55712ac25546aa3d5,0x3571cadc95a92b385638,0x252c275806af895dfaba,0xb319658ac9058fcb1a56,0x35ac6b50d6922d0659c6,0x152e0a5bdcb7556d72d8,0xbc0d76b2eae5d00b9597],#[0x85f2abdbd7ac2f365e40,0x283025600abf897e7afa,0xc3f586930aa612ac1a58,0x3631ac5e18b1314f624c,0x29b2326422c7c18eab1a,0xcb89968b2b16540c9f59,0x36754ce119ae33306618,0x45b46e6892d0a5a0133d,0xd4b5a8934ee699ad2c1a,0x6b88d6a9ac6b5736aa2,0x31b63f6c42d831afa35e,0xdbf9b70b6c66d4ad9e5b,0x46f06dda9ba8b7366e36,0x2e383e7036dff9be9b7a,0xe475c7ab8ca7142e1fdc,0x473bce6f9cca3969727e,0x533a8474d2e931d15ba0,0xeda9da4bb2575eaeb0dd,0x6784aefdddebbbb97738,0x953d04799cf279e3b3c5,0xf70ded1bd837acaf521e,0x87cb2f8e9f0ebe007bca,0xaa3f2a7e0cfb89f583e8,0x89ffa3fca7f36fdedf,0x181c902da049c0728093,0xe7c1af832305a20a1c11,0xa6a13bc24e844507d60,0x986ad0cb2180c2df8569,0x12c40287bf0f021ccc37,0x132e250c47a88c3111e2,0x78b0d156a295c50c89d7,0x2f46348c1f17ca2e8c5b],#[0x1c0236ec6b78d3d1a123,0x38f151dc63ab473f8e4f,0x36c83a90251f8a3e2c7a,0x248e482c8dc916122324,0x793b326de4c8c9669295,0x524a8494cf29265134a0,0x2d46595cb1195cb2b2e5,0xd983d2fc25e14b9996eb,0x8c4cee999b32666314c3,0x37966dccd8c9ad334f26,0x29d4d39ea72d4e319c13,0xd04f6f9e7b3c9a7804ed,0x410a815d0029fc93efa7,0xda1d3433e854d088a0b3,0xdd519fa2f1458289b510,0x49a2922521da3fd47768,0x4a6094b9e961d2a7a517,0x1d3d8a76d4e1a9b2533,0x534ea585486a8b750c2a,0x7ab3155aeaa45521a9fd,0x395654ac4f581eaecd5b,0x5d0ab8856e7ad6d5a4eb,0x7afef5f5ebd8d78baed1,0x74d8cbb14161b6c1d581,0x6652cbdd94db255641ec,0x9b4a168b6d00d9d6b357,0x865ae7b58d6ac6d4d5a7,0x6e9adc2db65b6896c9ed,0x2b885708edfedbe0b785,0x835ce1b9817282e415c6,0x7652ebf5d64ba8974a6e,0xbbc757832ef65dd0bb6b],#[0x6e5ec6bd4b7a0ef36de5,0x7e16fb55f49be3b7c06f,0xdc063804aff75fccbf57,0x81e0e4c1798257037e04,0x86d30c8e16fc299849b0,0xdc52f89b31226218c3d5,0xa4e331c6338c13176e2b,0x901b1ed63a3c7038d8b1,0x5c9419213232e44dc867,0x9c6525ca2793bb26b64b,0x96f72c9e576cac9954b2,0xaccef996f317e605cbd3,0x84e6eccdaf9ae7351668,0x9e933c0e762ce819ca33,0xd06fa05b3fb67d8cf7f,0x78e8d6d183a27b43e685,0xa64b4bde964d28da46f4,0xfd455a83b4f5e9b9d34d,0x6e6abfd54da9ef529ea3,0xadc35aa6b33d633abef5,0x4d825afbf5e66bb2d721,0x5c6ca1d909b18b627ec3,0xb54769bed16d9fbb38b6,0x3000c1c136d3ed8adadd,0xc9039008c7c140a08183,0x60d089602050c4f04983,0xc9c6c5a1068651040890,0x82231304474043400482,0x870607a2d351d1a15142,0x1cc0c24845082393a361,0xa1245e318887d08958c1,0x51025c0923b019f48253],#[0xb3bab089164a493fb064,0x49fe3e840291f4ab408e,0x49042ef700167fd3c441,0x27fe8920153fb4c043ef,0x8adcfa5024f781b8a02c,0xac1915c7a4428efc6e20,0x41fe3cc4029bb328829d,0xe510a3be54093ecf9201,0xbb9ff00014ce41915f79,0xa0131f9d9900a5c7b500,0x299d4562467ebdc02176,0x77d6107b8c494e7fc000,0x127edc02145b28267880,0x21759041ff70024e7f00,0x67f42073ffe0209e6b12,0x2e720777e841087f0904,0x8a6f300c8a0e5fe00015,0x794c050efb0117bf0f50,0xf857280aeff8580a056f,0x3feb21141fec8ca0151c,0x20151fc504cefde58093,0x750c89d57cb8127ee43e,0x291fc24114fbe648051,0x9a0509785988c767c3e4,0xad91390cfad9a0577f85,0x884800128fdd6a4507fc,0x9a23b9fea012840dbf9,0x2a7388307fdc480523c4,0x507fa59020159f2f38a0,0xf289249ccc5028bf8010,0xe32a029b3ea0422a123c,0x53a495c7b500b7f42073],#[0x15d1f79cd02989d24a,0x70c00567d4b44e6cff65,0x577fe1ea002a5081cdcf,0xa0ffb1089cff302080,0x46c273edc0218814e794,0xfa320120be77b00a2f9e,0x149fdc1098bee010a277,0x827b3f2e8402ab9d880,0xfeb2413df99824517ff0,0x105bee540547fd648273,0x67e598914bfa103adce2,0xbfc3924510672429d84b,0x4ffa9400a6fefd72a8a6,0xc40c7efe680507ed010a,0x2f99c4100acf87a8014a,0xa0efb95014ef15c70412,0xb92304f3cd4a4534e620,0x8b396ca2151fdc91828,0xb8a4127fde141283fc56,0xa6230a8657eff8010f,0xdfea2045e18a0a29f7b1,0xcf4114a860d6729e080a,0x13e31459e66400245f3c,0x283f72fc40293ef2d040,0x24eec036540b4ff9e150,0xde1a0292fe2c849f7164,0x40ab6302228ff08111ae,0x92a051766510527ea3cd,0xfecc32822b363caa29bb,0xe52083c0921c9f300149,0xfdc8880547fafc40287d,0xfde182293ffb1941155],#[0x67cf3122818107fc0645,0x64d7fdc7509cf9f2824f,0x186040907ee489145e20,0xa29cbcaa293ddc6081f,0x473e52098c067df4c0,0x784300a763138236fa82,0x293e6960285f37045be,0xe245bd3f880293f31de4,0xb247a8155e9e88053377,0x824dee33227b98c0273f,0xa145fbcc5050bfe21584,0xffb0014120fd142623e8,0x2a3673fd00151fa224d3,0x47a002b1f1219c3fe000,0xfec998052f7bac041f9e,0xadff9820521ffa080a69,0x2931ff60813c5ed61247,0x3854055b5d61a04837f8,0x70247c48772ff0405367,0x98ff8f1d80a542077bc9,0x1051673fc041493e768,0x98608245ff8628283dff,0x1f0000240f27c000903f,0x23dfbf8e8014be6041ff,0x9ab82679bc038ffc0494,0x18effb444a2fbc326014,0x74b06dab8c0c8f3e8011,0x317e7a8229bcc9dc44a5,0x2f81da57c0f66237b08,0x40f7ffd5704f7e618914,0x8413ac40d6fb3411491f,0x8413dfbe9a09d88149fc],#[0xef2c051b3d7c900a8fdc,0x83fe43e20149fc504c77,0xa8f5b0340ab78cc0424,0x100a6f27f14273e9cc54,0xe9713dffba832293f21f,0xd27860141f9afd80504d,0x9be09ae43cc0283f3412,0x41e14e12455743960511,0x24527e7f14139f93a191,0xb2784f7fd5af828ae43e,0x44fefcc00a0cab958a42,0x49fae010b1031fbf8e01,0x58151fd27b9a02a783c0,0xffbc50503da80546ff1a,0x141befee608a4ecb8106,0x87d04513e80111ae74a1,0x93e69400a6fcc889149f,0x8a59e540523e4ec4804,0xef9992a0527db8046f04,0xde895f1f944f297e0491,0x1e1792941385e4094c4b,0xc53b5d50234af0304090,0x8e7e733038ca6ffd0ea1,0x4501fe18812995eb804,0x7d6e4023cfcc64433fb2,0xcc644bc1a90a09d4cc98,0x26aff3944c4fb3c5144f,0xab4c4a2ff3c51357cfca,0xa9f4b48463f440344acf,0x5b5da3580e3275f45ae0,0x489f4070234af58411a4,0x4a0f3730e90553271a20],#[0xe617c88b6ba2231f5720,0x360469f4a9408f572049,0x9e7d01d023e588f22ae2,0x6188b49981c6524ce338,0x14987f03502490b3826d,0xb625251fd11621926fd3,0xaf58d1293cd98a4f6aa4,0x918c9c99c7613d611327,0xc5263f0c8427de431169,0x4328f24cd28d6a425be5,0x936b68903faa02469c11,0xa1c46eec281fec9008eb,0x88a1ae0fc851833239a8,0xd458f438d252637e326d,0x3a5c0a8c4ce3b09c78c2,0x8bfba462305838c2188d,0xf0645bd8e12ef030bb44,0xf66f79422a112f5a464b,0xa7fca80acfd97de5a293,0xbc0e32a9db4f192490fd,0x52a3e0492bf4ca4d7efa,0xa81ccc4906e1096abbd0,0x98c877b7fc408a663218,0x9159be9a914179f12029,0x62281615af022f9fb40a,0x5e10f51248a71921ffab,0xf379e21149ffe9e2002a,0x812498c867ffb1c6029b,0x9981c6587c2125e1490f,0x1e61314a23c03321e6f0,0x8c547924c5281ff01023,0x9948f631c432387c2e73],#[0xb86c4e2a3291879e6293,0xd0e338ae7f404a91efc,0xc01cb520ffebd540a4fe,0xe5f34575f9edea02a9c,0x97c1a31fd7bb5a2933e4,0x52b3f4245b377c191488,0x25323e5ef0116de5f2a0,0x38ccc245bf5f1c628dae,0xb08a3feea205aff32412,0x891629a8640f9e513459,0x2cc50d6c4510ecc8f781,0xe04a768e1a4546fa7913,0xd0ca7145ff8c692815d5,0x9d02672d4e0529f4245b,0x8d225e77225b8f804d79,0x38b4fd0bec4f75f02558,0x73f225758c5877920d76,0xd142836224c6554de312,0xd901c8e526c4498caa9b,0xfd01202a493fec781914,0x4782c2394df9b1b2714e,0x7e60901524df9a7a1185,0x8bf5657273ccd8d938a8,0x4fbc2a4ba522fee9f182,0xce7a2019b3d14eca7ae,0x1c5a265f545d89a47d18,0xf7f045ee31619fa6037b,0x2d5e8a6a23d333599941,0xa2d31bd09efe7404de94,0x11006943119948d2211f,0xa46bf9b610e59160e72e,0x50f2b5d7804ca48188cc],#[0xefe6760e04c2d3cf7907,0x914443e34595b8570122,0xbe0b108ca108fa288b7e,0x7a2298c2708eb044788c,0x45132faa2819b3d140ce,0x8a8ef821bd8d16ec4dbf,0x3cd3659858cb6f26deb1,0x2a3b49dd429a137a042a,0x51a49c54a524e63e0cce,0x2a3f084ba1885a691e9c,0xe5b43f500b6ff48e640,0xa6fc6cc61548ed046949,0xa2ccbfc8208e3e341046,0xd9937c1688b6f3243eb1,0xd93008917e324b307196,0xc78dc213d9966e010ac7,0x91612659b9a533e64dc8,0xa8f93792a92b3f8bc89a,0x97f964f2147f57d9422,0x516537cc3c3910a832fa,0x9548b0f261f730155f22,0xc0a5232c7d45246b77c8,0xf7c421c9eeecfb8d148f,0xca3dc7130c299dc61a08,0x291fab038df3688ab2a0,0x8d4e74f5ca951ccbe3d5,0x1f109b0f8d408c3f1540,0x5a22c3f921f5884587f,0xc8b7ce49660e32c3e4df,0x679b24267edfc10485ce,0x83e4de4aa4aa2f226a45,0x3be072cae4247cb55044],#[0x2f22504952f16054c903,0x9d84b12d24c3c6360412,0x3f76061fa9041c4cb262,0x1a2d5bf2822ccfc8208e,0x2e326fc1a22bbce087c9,0xa697f6213dfa36598063,0xa6f31f0e348ae94e77a0,0x1c917cbbc135e6fec2a4,0x3f9c02abf298261c40b8,0xf65304f316442c245c25,0x8df8c5167b83be30161f,0x88a3fcb022ce08a19478,0xa2271ca8d0e338a077ce,0x1fb30e86115c19ce4b79,0x33949e3b3a80555db813,0x65324c915166a451e23,0x38ca8e7ce3eb8a2bde86,0xb82141f2e0427bf7e3c0,0x1617f7fe948c502e3fcc,0xba7260c14dfd7fc69306,0xaaf388c58aaf2efb8822,0x249cf063941fccfdc800,0xfa8b8888248eb8dd2c49,0xc70e90463397f128494e,0x2a3fe3c8263fafb59214,0x3dfe76b8a2abff3a1624,0xff85c10a2fdf9d00e32a,0x67fff3a231815c1e125b,0x8785eec2071e14d22509,0x88296a5a702cffbb71a2,0x1644a72529d24a7f9e5c,0x148479318a6ce78f9230],#[0x85c823ef4a08b7ebc236,0x334ac2abefbe89814af7,0xc7eece83ca34f4112fbe,0xb8e232eee24047bd3804,0xf74974e94ec6650461a8,0x8c35c28651cd24ba74a6,0x92c28e546e28e4f30ccc,0xff11258638b6d0a9a511,0x29c6b0a6fe4c960a38b6,0x2584f273ff81a01ac2cb,0xa62c48577f49b7c68aaf,0xca40957f936ec68aabff,0xa74a67cc8170e499e708,0x860475f4302e2c937496,0x3ab18a96cbf3d4866af5,0xeac40a6f361b96205972,0xfce335881607dfb44511,0xfe722ee20567df58c4f1,0x328e825c2f4615e0bd14,0x4937f9ef542e32b51a43,0xbfce668cb8cae6748654,0x52bc512851ef1d07a729,0x28d427abf1949fea854e,0xa43328e2bcbc48c2bdaa,0xeb1961f39fe8c5d42c51,0x8a7b9e8cbb0aaff339a0,0x3808e8e2bc17a28af05e,0xa8e4c02250af01d847ca,0x270893b2751364da8aba,0x71951ff8371d22a5d547,0x9237b580123df9c1e0,0xce0344aeac9094afc8ac],#[0x73794507becc527b6092,0x289cf37944d7ef2896cf,0x7746c149e24b8941ee6f,0x26d167649146a647427b,0x3997884f7cfcb84144c7,0x7d265188e046cf668065,0xdc3e3389f3d9a01943cc,0x935193ed2290e1e07194,0x55f35110fbeb609ef532,0x2bd0213ed649411e8f82,0x100528ce5e702d7f5182,0x338e0961d24429df91b4,0xc3b42943f6fb0c12eea0,0xe70437c5d63831dc5063,0x2f62140ffc05580a42f8,0x4e4b0cc3394d7a01273c,0x98129a48bbb0a6f8fba8,0x4af9b822976dea09b9c4,0xf149f3460e8547d10f41,0x989c3f5887f8a6f1710f,0xeafc6291ad5d428f68e7,0x52bf8c53318ba851ee5,0x7ced1c7140b8fa339814,0x33d00aafe6ea4e502bbe,0x4e924fd6257c8a8fe7a,0x27925dfbacbe051bd1a4,0xa24d450e720a24f800a8,0xa8651da8a209a8a208b8,0xce8305d4ec9a394370d,0x92c3e74eeea92abf1e7c,0x8b8a207ee24b1fc7166a,0xc450c7620515b86d4328],#[0x70c2957f806ac0ff193e,0xde551143f82066477032,0x8e557c91e260cc8c3323,0xa29ffab804c159fef680,0x984557f1cecc4150dd08,0x263dc0817e028a7f0e61,0x287179e51387ba250f5a,0x20e648f13eee2511b62,0x9d0c3e279d2f6011d56e,0x6e04a3bb0115ff4d6805,0x427a3bf632798cec91af,0xe54ca60aca5fc0e7df29,0xdcc0c39283e14f00a0f3,0x786a23955724864d88a1,0x3c28865be7ee0098557e,0xa2435a25d8a8895e218e,0x1b008e3f8d2ca088259b,0x78489fa05df813441e3,0xcbcd32e0557d3ed36453,0xb131197d8988b5a9f253,0xa68e35b9a26ae5a68db5,0xc7a81291abec789a6b49,0x5330a3794a4539e5c789,0xf7d4cc273dda998507bb,0xf7d4cc273bc097e53094,0xacd01206c5a2672a1590,0x651b26229590f261d9f,0x595c6422cd7b0889f481,0x83686be4c0455f3684]]
def g63H9 := limbs80 #[#[0x20c220006010401120a,0x7001a02030c0f230100,0xc0b002500010e002f0f,0x21b18000201000e0001,0x801030d040101040602,0x1c0d002001130c021703,0x2050118010801090504,0x2401051034040302051f,0x301135d00040e130354,0x360304040f0014012903,0x5011305310805020504,0x1c061c01050c0101,0x501010a01141e0505,0x60b0103001c0d030001,0x2d03192405084509020e,0x1070013001306100311,0x1000500001c1e140202,0x1b034003003116071813,0x1b020601261501240100,0x23000503000100180102,0x10007011a02000b2712,0x190103010202010406,0x1d000b1d000102350002,0x45401070412012c0d3d,0x22011b250008020016,0x212f100a79040d050f02,0x210b0027090510046000,0x10105030c2223110202,0x9050100024e02080103,0x31c0703000000101e02,0x30203111a1d21080a05,0xf060a01140705000203],#[0x1818010121060a000107,0x119110d0d0e0a021a,0x3050401340120050009,0x50608001e050f21050c,0x1809050e1004540e,0x1b0501160d1606020601,0x1201080023561d1a0205,0x9120006210306473209,0x200061600110a0f0504,0x104902000010022513,0xb064502180108001269,0x52c000e003f31000006,0xd0212290000010e030a,0x1000004080914384d01,0xb025b0202150401060f,0x10105062108000522,0x5080f01012704112700,0x6010c00101e4d120544,0x905024d030c0023000f,0xa082b040022170c0a0b,0x18110a151004010f121b,0x70a61031605042b5813,0x270a020a1919360003,0x120009350b0203000000,0x2f160c030007040d863a,0x10c0604010101188700,0x1d010118000601031a42,0x414d0a0e040104090001,0x71121208010619200104,0xf04030c07010e080022,0xc0c08040a030b06030e,0x6055c0d370008160202],#[0x30f0f0c191904331f,0x30907060204011f3121,0x12051001201d69032e2f,0x17120118012500025415,0x1d0609091d0a1b1c4b00,0x200170d04660b4a0004,0x166d00040401004d4803,0x90f38060b0a11790c00,0xc0109060d1465103500,0x82e1d20110e3303020f,0x260b11710c0009162d0a,0x130f091e8d2b13261600,0xf201010013027000c1e,0x5723e711042f02551200,0xf02010b010500972427,0xb000261106406050103,0x125e0c04790c01007922,0x3a1d0002193a20370413,0x6d100208010200000403,0x111c07fe25094d160500,0x2014a000004061d0421,0x52423cc9f6b71a4508,0x4c4d5a7c0000000000,0x700c200a717a00,0x65e089f45e29d711dc00,0xcb1728c391dc876ca3e7,0xe093e46209c84f4921a7,0x1a0bb6c1c868b000047,0x1d7d2c3be96774ba3871,0xacc575c467c28000050,0xb3ac0451b0b14800003d,0xdc734a00000000635144],#[0xcef62b69b0eb213c2912,0xc1581298fab803aa3317,0xa2f182f452597ef3412c,0xb8aa66a002d1ec5625,0xf199db80fc0000994200,0xc5a843a797632a22b0,0x6500008414a537f10300,0x514ba5bde851238278,0x968a80001cf8a9f32e00,0x900005373e52dc354f7,0xcc02316a0d21000015,0xe66767caa60000000000,0x7192925177c72386bfd6,0x63e1cb00007a2aaa3e32,0x1f6261000051dd4664fb,0x9fe013765b08840000c8,0x2e0000933100008501f7,0x3ea9c6e6a900003b3e94,0xd71abd000037626871b6,0x3d0000faa830f5a819f7,0xec389c12e5468044092b,0x9096d2050000e0c2d1,0x86c7524c0000000000,0x69e96d0c7ed4c1b2bd00,0x5df5e7b6abf062dab972,0x5286a645c97309c5d1c2,0x2d85523cb57c80ca0913,0xbf245bf991004167c290,0xcadb2f803d056379fbcc,0xf7a623201419f7f31edb,0x582aa7f86ac5d69563,0xfcac5b26de00000be500],#[0x140000cbae735f9b0fda,0x42a47d00000000e58c01,0x85e9780000717e000073,0xeaf5a48b2cf3633858,0x2208a4888add000000,0x75ed270000f3e685cd00,0x2952b458d8c67dd45db8,0xe43627a4b1a01ac7fba0,0x806d7bde299d7c,0x8a8bd400007640000000,0x936339387e5ce51c458c,0xa9000000003bd6629dd6,0xfc91b38906000069e0a9,0x16acac2340b617b0b887,0x976f54b6d701f8e771,0x5f12301d188c8f541c00,0x6e5b849d1651a6271af5,0x3863689c9ee879836a37,0x418f6000000000000c9,0xd0581caaaad4f320351,0xba9c2679498d6195a1,0xd5338900003731dc9900,0xd9f05004ad00008d3794,0x45e25e85f69a017927a6,0xea775f6cd265797481a8,0x5aec67c86331066754eb,0x7a5a569ae22313566a4,0x130895d6b9f87683f54c,0xd500007a0e855301bb76,0x38fad70000bc93000089,0x4b784a586b9473940d9c,0xa4d63834517b52000029],#[0x33dfcaf642ceb1,0x1157e510f8f2793d4100,0x21603abfb17f9d91314,0x4b359ce54400007c0d63,0x90000000008a76000027,0xf377da75320000407209,0x1b00004773d92d0000e6,0x282c7b46aff90b414353,0x10547f0a171a5b20f4c4,0xf2e2560000000000000a,0x8f38ad0000370d94cd8a,0xe465d5000000000000c4,0xd3a4f508400000000010,0x860999e8b256ba2bb967,0xca403fca2e5518cb406b,0xe71a2b3efa4e215a798,0xa74fe784e450bb3f45,0xd34a2d895f0000000000,0x64b1b5354d0b559ae319,0x6d00000d1780e3402ccc,0x7a0000499e4608a3f478,0x9409f5e1b900000000b3,0x6f00007636658887ff83,0x3c77f30000121d00000c,0xb12a8e19b80000721b68,0x6b495eb9805698e88d4a,0xf236ae5a4686ac607f3a,0xd60a640000746246f6d3,0x81b863fa00000a3d17,0x3a1263183f6d4d59b900,0x3e7c06fc3ba90258cfc8,0x724a110000983d00eee9],#[0x856d68d0737e67edfb,0xa3000032f2e969f08f00,0x5ed1fa3980000d6fc41,0x975d3e1990252000084,0xba863542b000000000e0,0xc66291b3764c0195cb3,0xe9580a5bb10000f67517,0xf31ade31df0171d750a6,0xf65140e27ba804f012b5,0x4241515a932b951247f4,0x242ff5,0xe9d58e0000c78d5c4800,0xaf63f80000178b4c2de2,0x39ad8a075b38ac6b4c,0xf06ad4469b746000000,0x223b8595400004cc877,0xea49a553e78687000085,0x415b0900009b2e578aec,0x82750d587fd8cb05b50b,0x5900001185b416726d6a,0xc83b4820faf9051bc47a,0x28c7c550c778ee000067,0xf9e7cfabb549ded75306,0x5a0239c5ab4079416e70,0x2ecbbce0c63ad1c3156c,0xe9a0f7000006df4b0858,0x6dc170792bf08320400c,0x383ef5e8f833bbbb17,0x7cbbf81b44230e000000,0x197799283308000030,0x4d0000c8e89ac9958400,0x540bc300003ce3810ed8],#[0x3785dba28c,0x8a341321ee0000073400,0x6413fd0000c12f00002a,0xd26670000564f0000f8,0xb830b7efb89101e056,0x540770000c77ccbd700,0xfcd88093a4dd12000068,0xf045b299229a29464e83,0xc931a474da4c0000b0,0xa9e7fd000093d6c0d900,0x2bc7427016975125ab,0x1acc79ba4c88ba7e00,0xae16e86752a0c0b89300,0x340110e1f80000aadb63,0x9f000053060000a10a25,0xf687bd5a173038caef6,0x5a0000000000006571e0,0x27360772d1e1a8dfea,0x7b0000698fe8d60c7700,0x5900005d1bcc1e000074,0x161ae60000f150000055,0xd57adc0000e458718337,0x27640000884241,0xc60000fa980000cb1200,0x36b6ee0000f7f5e169e7,0xf7ba8af175,0x2214ac000024bc228700,0x11e289ded24a46590,0x3a204a426c0000000000,0xb10000c0809217a9bcb4,0x9947b65dd1df3bd9c,0x26000099610000061200],#[0xf0000042ec067f5486ec,0x760000885febe3222cf1,0xed000050a6c8472c3695,0xd600009aae5c141917b5,0x2f5cb1c21dcc565314a,0x43d0185745da749d52,0xe7b6b8ca810000220100,0xbbc12cea1bd8d4064690,0x13f1e52236887859c524,0x1c00000000b6c60000c2,0x3c00000bf1cd468016c2,0xf186b2660fab2ad44833,0x922d0dab580adfccee85,0xef45620000c233c121f5,0xc4000085fb0000891a90,0x5fda68acc7b80ce8ed03,0xc3e68500000cfa0000bb,0x19e50fc055642be6dd46,0x68e372000054d8051441,0xa1e0cd0000f5def2ffac,0x513a54858d2206,0x25be00005b2cf4e700,0x3419cb00000000f24400,0xd63300007b5a0000db,0x4d2a9aad8596000000,0xe63fb0afa710000000,0x10b3000000,0x9c3700ced36bc79a00,0x4c4f5d15b1ea600600,0x797422cf000000,0x243e00000000a3ad00,0xa46a68200000000000],#[0x86010000000000,0x9700000000511b000000,0x1454e1b4185403a40b03,0xf9552787f200004982a7,0xbc3678abe280eaca728,0xa38b9d48064b2ddb368a,0xe20000c9452c7acae2c0,0xd3cc25fed0b50000a2,0xc0000423c0000000000,0x17000058530000c624ad,0xcb02c300000b7c09da57,0xce82c50a6cf272f1e372,0x757992908ae0ea47eeba,0x1c25a4dcfe3548b0ebe7,0xb35b51519798a1623e33,0xa8c4e03826d5dca225f6,0x2d0613f943af000084,0xc096c848150577000000,0x90206ca17d9304f97057,0x63000050b914a6a57d60,0x515c6ec2fdf3d8b2dfd1,0x1a6f0baea1257ec44fa,0xacbdbc4db42f86a62b8,0x19f037ea04c28c52a795,0x7a77fc3af49061d893,0x7ceb4c89075a84251a00,0xfa383200002b8520aef5,0xd3ea7a70967878ae27,0xab0000171169bbbcb800,0x422549b99300007d3ee7,0x9a428d1a1e16bc05e3ea,0x87000007038243414241],#[0x101a0284cf91af000083,0xa70000972202ca0000e5,0xfa8844ca7d0000c14147,0x3b15bc3ccbd828156b12,0x950000654c094e73a610,0x62c2bfbb01c777897b6a,0x78a77f89efa5fc650bc9,0x6deb53361abd10ca9940,0xb31ba5f036ead251bde6,0x6862f0902f5b74a80d93,0xdb98bc6967f94db267c7,0x8e8ced68709651706fa0,0x1df15a4152bd45fb10b8,0xb95533d18d9b20fcdb13,0x1720108983044e6ac264,0x2ff4a2cc12db90e32100,0x73805f61d9d497d14512,0x3544ebaad5123da52632,0x28452201b605b8265ae7,0xa64524fcd3d5563d2b,0x440000b4bf7690ace700,0xc56180000000081c360,0xe27ee44dbb98f8a685,0xeb25c4c1ad612345df45,0x7583a92a79ea54362f75,0x5813df6f7b28a90fbbc,0x9b043b33d3fbf0b33e71,0xd300000000c052612008,0xa6ea6c5879ed01,0x12f1418023f300,0x8a48d94fdc416d4200,0x9a25f47800],#[0x439b6b82b2bafb000000,0x127a0c000082068c79eb,0x32fcbb0000000030dfe1,0x942303e3000000002a,0x56d5e118006d0093eb00,0x7a5807652ee1d266f4a5,0x6398680454ad9ac2765,0x9a03fb8a907918d37d44,0x30d75cac2036430d2e3a,0xc43c001100ed748a95,0xed259d0c2e0652853d00,0x8bd6967ce19b1b211d8b,0xe67b500000413800003a,0x7ee7c99baa0000000071,0x9f5b54167a7ae7f4e9eb,0xcd9291b0b133c139734a,0xf909ea0761f56eb4f3b3,0xc6cf58b6b7a18bb00a,0xe1c1660000973ce79200,0x8424aecbbfd076371dd3,0xfe2c4bf4c59a9d6c3152,0x61fc1f0000d9a6b4ca32,0xa2399c51960000655556,0x33fc0f504900008632d2,0xf200000000451b2ae59b,0x514ecd45f960c5a5625,0xb8eb5bb10700000000dd,0x85f53c228f000000006a,0xac00006c9df96054424a,0xceb707a1110676f8b079,0x4d000009fde91b259ec8,0xbd96d31d19b49ac944d3],#[0x27b85b,0xfeb472a3740000a31700,0xdb4e00000000f7bff6,0xa225c027e956a2923a00,0xd12684940802d8019447,0xd57a445a72a6d8c74049,0x7c000047db607bf56fb2,0x5332040000ccb30000b9,0x5b6bfa000007c30000aa,0xd0000052410000268d41,0x9199ca50f346cd0c1d67,0x66a7823bdc0000000050,0x4c770e549429cda31607,0xd79c62212be755694ac1,0xf2019735e15d8000022,0xdbf04600000000b38512,0xd87b1d0b5d9cc4279105,0x1484d8c183c3000017,0xbe5038909dd8a447a400,0x2500001b5775e6253fb2,0x7d21861604b5c1ca2c76,0xf49c35352c891234be1c,0x7da682b8b84c0028683c,0xb03c951d1c4d39b1a168,0xfe0000e2955b49aac746,0x5f67e61626b9f0467bca,0x45a334d175000091c11a,0xf1016833b5ca6f782f3b,0x62c15cabcf5517dc9734,0x3a8fd14df1c61abb1b,0x6388703c45e424d200,0x3ff04cd0d607dd856100],#[0xac6bdc63b3cff9a2733,0xb60000b39e1bf9f18153,0xc5ec490000c619c672c2,0x52413905943d3d000076,0xf9f002aa836ad4f3757a,0xc9d05c3b0ec02a7254bc,0xf4743437a8c3a133e2b9,0x7ab0913164a000004b,0x190000f776153b000000,0x4e00005396e0d472d34c,0xf215b057190000072088,0xe05600000000c68f84,0x4ec3c0000595d313700,0xc818d2213568600000c0,0xed1187c65954d107cdf5,0x179859912955fa47d1f3,0x31cd8329ca312d31e1,0xd32027504bfc5d97bb00,0xda6699eb96000042ccc4,0x1cf93d8ccad3f1c92a90,0x6601b70000208d4996a7,0xade3bbe27aacc23849dc,0xf188b289b704d691ab,0x89a2f36cd90eb27600,0x6e0a3c2cfc58a79acd00,0x3614c8dda18bab8b98,0xa5b4c4264470e5943700,0xfe872b000009234b065c,0x243cddd77962d94b6cc0,0xc3686aa0a3665c34bc0,0xd40000d48767096a742b,0x4ce2e4130ff77ad0ec17],#[0x74a7a83620bdca3754,0x5cc60328b3f0f9eb00,0xbaa595753968e5c09c00,0x75426600000000035768,0x344f00002be7b0,0xcc82d0851f6513000000,0x9980aa036383ce408619,0x99c920000069e500004b,0xba5d4a9a24d379bba447,0x74b759f7a91d3420a8bb,0xc52b44f74be6a81346,0xbe000054da0000000000,0x6264000020c4d582d1,0x4e61890000372cd52500,0xa4a81db214811c683505,0xa3162c000000006cd7ba,0x4b6253425f03070000db,0xbcb75b5c916433caf4,0xeb0000000057adf98b00,0x2f8a2f565087aa518e8c,0x2d0000000000003745fc,0xa027ac14af01aa2a3474,0x9392a92712000000005a,0xafc860000258f000035,0xf500007a948569b8c082,0xea410bc3d1a86fd9aae2,0xec396f82b879fa9c0cf4,0x2224297a65f7433c59b5,0x92fa67000000007aee16,0x700005b9414a5671fc3,0xef00007bac1384c0e9f5,0xb19100001cd502],#[0xbea435658b0657000000,0x8fb83b00000000b035d3,0x61000096b45b247c73a1,0x250000abc100007aac14,0x95f800000000c15ffc,0x81c20000c808000000,0xa388c688634cb000000,0x3866d58093c62002abfc,0xf7915d000079ab496654,0x7e22dae67c89f8c46402,0x81935b6a63c85ef3c0e4,0x5c7ac807e208f17b6966,0x10e89739e2a682,0x786683e5578761ce00,0xb8d1000000008d0400,0x74fac1a4b236669a9600,0x32c2430bac7785b9175,0x3a61d1645c36c9ea207d,0x2400d3aa7b3489706516,0xc6aa8601bcfcfb28c345,0x458d35b27c01c98c08f2,0x1238000090a7000002,0x5dd24b876a000016be00,0x136f46,0x57000026bba7d5a2a500,0xbbc90000dd330000c4,0xab34cec19fac33e1ed00,0xa7017900006c7ca71874,0x4a4b000000000000b9,0xa1d8566b0a0000f08100,0xb533c5b96b0c185498aa,0x8025780000332000002a],#[0x36008400000000048033,0x59e6181cf838d099e4,0xbdb53a64fd0000664d00,0xe4f01b4a1ac3386a18,0x5c4ada183102200b4600,0xf5f649f39de1fdf8dabc,0xa9c0082dd965c3994c,0xe121f49c61a1eb681b00,0x78017468ec5d3a00573a,0xea8c708acaa84135ca9a,0x7f6a89c06ea4b8e89085,0x1536ff000059a1e8d79a,0xd900008146a769ca1c91,0xcd375bfa3a381e0000e8,0x364a360000ad40d79868,0x6240b2484c1647482c69,0x80eb26e8c467247be4a8,0xc45547e43032f912ea5b,0x8b199b820000121932,0x6500005162b0981c9b00,0xfa716d89fe3c76c42161,0xfa680f362e1095c788c4,0x630000e417e1f703f6ea,0xd2a66c6a392b03e68a84,0x770738b5354d487554c9,0x320000a8acb38d1a8786,0xf32d01266812e03673ad,0x137bc6fba2510000d2,0xcfa6e3a83485739b689b,0xcc07e484ba47a53b8dcc,0x4642ebc5fd612e351d37,0xfd7a7102b3715598a3b4],#[0xce07564c8eb1fe290940,0x9a22fb1737f7eb08bb85,0xaac6546b29fc222026a5,0xa8e6a5f92493cb250545,0xb3a915069b456a17c702,0x40da41a7e8e26e0d074a,0x1000041f9fce2000025,0x56e503b872ba5cf35613,0x610000173ef59fe44701,0xe57b30e05c924cbdf3,0x55000086415343d05100,0x9d1c320000e5e2027fb4,0xd520e1d0b823f33a01,0xd40000b7e18521b4b500,0x40abe83729f149fc8cdc,0xeda5081a43a26b0000b4,0xc8f2992cd6000084533a,0x8e00000000f1e93611eb,0x3fb897e0a2aaa51602a3,0x76000029e10000686797,0xc81889f6788bd47c01,0x4febc018cc000009c200,0x2a000043fee1e7ba0fd1,0xa4dccd023aab000004,0x4e1d4b3824fc2a4bda00,0xf05a44b7f40a0000a0,0x6d9b718825b0c5e28500,0x4c3d06f50000000044,0x1d000000000000fcf800,0xd97a3f6abcc22ef5ac64,0x17b4fbead0dc0e24443b,0xdf729c7ca4dbf7cd28f8],#[0x10eb60824606c2c4ee34,0x6fc92c83c7730d3c537c,0xcf05a9068842de82f4e2,0x2732fa0c11821ace0ea,0x5fb8b4090d6b351948b4,0x346b56e9e4e63c5d4e2c,0x2523b61af8221ee0cac9,0x489330b025e1d769f1b9,0x3708195767,0x441025414cd194e400,0x4c0000691482ee095600,0xd64631777be20ee1ffcc,0x519bfe02ed8d53a06694,0xa4014ae09e000015af89,0xc8e347306196ef2445f9,0x6d2500000000047a73,0x260420e9a368de58a500,0x4b70159b5cecc74274,0x5221f1d400,0x5749c60922c2000000,0xe1ba5d5d1e775ecb0d00,0xa3238362b90000448e28,0xd60000c76ccb8f84c8e4,0xb2cbf500000000038c42,0x71185433424fb79441,0x7000000005c55a69d00,0x4a3c74d58aebb616faab,0x1b00009b2b4852504dd7,0xacb943371b14bc42f6,0x71296e19a8b506000000,0xfeb4bd0000000025d4ec,0x93000040236237061567],#[0x701fe1f2c0c96c4afb,0x6fa72642c8b2b5874100,0x130cbb161abd20000fb,0xc12a60000017ec00000c,0x5928beea4df0e10000d2,0x1e005d0000708c566969,0x8b870000cb22a144b7,0x16aad78cf9bd000000,0xf5a300000000a24d00,0x1a2b15c18cf642000000,0x94fbc6798a5946517b31,0xcab52f780b108544a9f0,0x7f754fc6a8c0289008b6,0x5fbe000000000249beb,0x72d97a002a4b24af3,0xd5e21a9a88a14e77b300,0x71acf0849529f2aa2300,0x6a26d20000ac8361f623,0x19a1877b165290000cb,0xb7ca1d29dc4c30000049,0xb513ee9232fb1a262ad0,0xc50275741baa2b3b77c8,0x34336e00004d3c0c8dd8,0xf0766234c2a6b19ceff0,0x6649afc39341ae000075,0xdea5c6978e39337d2db3,0xa9b177ae0000d655bc,0x41922a91c70564434c00,0xe0d3cf40c8eaa78ab629,0x2ab585f896dca62c6926,0xa22bf31ab7de1c91b3,0x5875d7bc8b000055a000],#[0x22d23bf99fec78593583,0x4503c6ea49155a000078,0x6362a064dd53817a6d5a,0xbe039c6a0db59785dd8c,0x1600000000abf3000009,0xbfb1c4d76099d0a37f8a,0xfd1a69400000000041,0x6a33ff281a00007c3e00,0xe93b1c198e00000000c6,0xc1c37cf9c30000146baa,0xef0000000000000000f6,0xb8fc0000000000002b,0x263beb23da73a5000000,0x82000028270bddd0e22d,0xcb990c63ec0000fbd850,0x2e906811a74bcd00003b,0x34313f4d3f000050bf87,0x82977e2802484831da61,0xf89ffbee010fe8,0xa58300,0xa7e8f2000049e3c61000,0xd479da58000000008b,0x246fc30cc55b00,0x690f05c2613200,0x59995098c600002b7800,0xed0000a64ce9e93ae072,0x82619b8ca2e887118416,0x9a0988d2746861626292,0x8570f67a050000ea3b58,0x33a24061ac0364c7582c,0x5e4888b3620000000011,0x28000e4345abfc0000ec],#[0x470113fcba006903a3f5,0xa552bb0000861c60d7eb,0x54d987288f93c95a30a0,0x9b12232b3172a16b97a1,0x30726aa16ff637e34959,0x46f5167a57e0ff0b5e26,0xb7aa6ed06768b7326808,0xa022249ae46b8306db2a,0xae21fca780b95ba3b299,0xf8615eb5bfa001a44962,0x3b344199e2c235a7a3b6,0xd6a6a34491c56ce4c3a9,0x4e00000000ba73f003e6,0xaf0000000016630b041a,0x83e4d70000696354ef77,0xe4de00008cc304,0x379cb16b00,0x1b719ced0f688ad73b00,0x89593aec3fd1cfa5bbf7,0x277bd38926a8fee2d415,0x5c917f98100000065347,0xbf1ac000009bc208fb13,0x5883ac2cce0000229368,0x8bf24e0000598c5ce605,0xb62480000ab9eca7a82,0x1fe4cc1159f702739aeb,0x9d444b9a08a01060a4,0xa97837c567e930393700,0xcde68c7ca92b9f0000b0,0xebd50000582be2,0xfe64310000192ffb6400,0x66ecab71e8397ff85ae4],#[0x6923e0bbf695876c6deb,0xf700000000e0300000ba,0x3bb30000e616c3273c,0x35d0000081fb000000,0x9b73087c117c619300,0xd3508e320b7192fbc500,0x81b7c1352a809f34c9da,0x730000f5f5facb51c89b,0xd72aec6324843d703a60,0xaaf51eaa6a60d145ffc6,0x540acb10c540ed02e34,0x3431fa0000000061a07c,0x8e000090d2613c59e716,0x9c0033db1f9be163ab02,0x43f95329f9000009859c,0xb4d99ad5c5a4ed55b3f0,0x86565c70218482e41ad0,0xcc8a4ff7440cda7ce8f2,0x57d09ac5b1f79571b1f5,0x97902d4cbcf6cc17e1,0x9720205ac499ffeb8800,0xf5230b7419b45900009a,0xf000007904bd11e11f41,0x7cc0d207000015ba48,0x9ce1de5be2d19857f000,0xdf4cd01d43000000003b,0xcbab1c,0x378199e8e62100,0x1d3b99980000000000,0x8105cf000049c8f91900,0x6a745c30000000078,0x7a652341a951f378f8b7],#[0x876b00007b,0x27547000002721d9d400,0x8caa06dabb39869cab,0xcf1a61000093448b3000,0x1f0000997924b0548d30,0xc9691ca9c4e8f4000096,0xa8631000008ab2000058,0x830000000069d88a19b3,0x58000000000000b6e148,0x48339523b13910000016,0x132a1294930000000080,0x51a80000935a67,0xb33261efd816000000,0x58d8ef14d02730c97d00,0x86d01eb21673a2000071,0x1de74c172f9598000063,0xd273d9806a7c4e000026,0x51dc652b75e964fb6102,0x7642b7d2c700006a8d97,0xb982a365b6495861cc44,0xc3786a8c000017f4b7,0xe339d636b5a580f73a00,0xfd0000000018141c3404,0xe8d3594ad8339ff47758,0x9800004b92007e58e6d2,0x7d69291bf219dd1d2be8,0x67e6e40000438b955d10,0xc3e9b54b17a1,0x2ae5ef3b3accfd1b5900,0xa60000110249320c82c7,0xc0f9729660dae8b1ca35,0xe9b4969088f4668234a2],#[0xaf7326c454164868c783,0x3e5affc77d829ea468a8,0x89105bc26571a5513b31,0x5a493c75f9c42c95e067,0xb608b3760ecd389a9ef9,0xbe00b0b949158d879726,0xd40000029834016a283c,0x8b2412000064a175e906,0x90c46e44f8117257c4c0,0x9d00003bb437934984e1,0x70c8f7db4f486cb24967,0xf462c992587cb07b4de5,0xdd0000dc2b415300005a,0x8ee57e8cdcf854929452,0xdb4b186bb70d36d694bb,0xb20c478f58e4360703,0xff4c5033183c9f6c7200,0x944c7f7278c29a000044,0x7d0b03906bdf48,0xc35d00004a92710800,0x994c2c26063424285c00,0xdaa316e536fd84,0xf30000eb67ca91000000,0x96581120d0f889725ab9,0x2d4d49370b000068d3ec,0xe78300000000000013,0x0,0xa0d5d660588053a91600,0x40ad809b00000000c0,0xb2f226ea55d9c1417300,0xd79ec3aa17bcf44a39,0x80d80000c96aecf200],#[0x5253232456265eed5182,0xd720cc7ba865911b7db9,0x77fca1000027dcd66b13,0xa27100a5d983b4b7b422,0x74000068ea000059b48a,0xc0e6291fda35e1c540,0xaf322d12100000000000,0x5bd1587af6f95c6cea,0x4adb9b4d2f0000f00000,0x4732f699d94bd08c163a,0xcd8a26c899e12d000067,0x57c5102aa07d2c427dc,0x3f333b5c47d4c63a0896,0x6c6178e3c25c4333d414,0x923997b0f20000fcd359,0x5e2260000014e6d8a8f4,0x8498b929cef49c54f470,0xbfa59096f20869b7b72c,0xd986e71b02ba15f4c799,0xb8c770875ae3330000dc,0xa90000959900001cb65b,0xb20000000000009229ea,0xe5d85de9fc0000502bdc,0xb34d500000ebbe48db85,0xde1d090000a7bdd32bd9,0x76621588a223259ac633,0xfd0d08174d622825c7c9,0xe7718467000092970b,0x3e5586e5f7375d816000,0xd251d6f365f68ee007b0,0xdc00000000000076d0d3,0x870b250000d5190877c0],#[0x96ce0000f8d5956050,0x5e929bfb130000260000,0x2b3c50590000cb7b2a,0x7dc4600000fc40038a00,0x92,0xb0714311b6c000,0xb627ca91288a40b85500,0x6c9a1300000000113029,0xee52ac7ba64ca061ba41,0xe054a131fe2883873b9,0xbec968e2ad000000009d,0x304bffeb055376529fc7,0x42c369000055ee66ccbd,0x4c749e594300002baf1b,0xeb890aec0383b766cb69,0xf1eb897955165600003a,0x3229ecb0ddd8e9000091,0x327beccb6e553e27b067,0xb400007211b971000014,0xb4b2e72a9bc91ecaf34a,0xbafdfd47f639fa47f4,0x67b51c6a000000,0x6d8a75489e8989e53800,0x3df57200002b790a2183,0x7ef8eb16e20336907ad7,0xba440cc9dff545a21ff6,0xfc00007054306bc55c7a,0x3f4415a18a0425b8b1c2,0x9000065112c521af062,0x581a001222874e30bc71,0x830000da1a8005091dd8,0xdc6c981557893f53b082],#[0x32384b404f80a4a7e7d6,0xb70000685bf3dcdc9ab0,0x2edc112b7687e36290b5,0xb400004b8c938f5843f9,0x6d3a014e86097369a8c,0x390000b1c04092562de7,0xe4f12a7400000012e660,0x8a03602d20939b000031,0x5013b9f61e00003565db,0x483958e29d52000073,0x29025b44220000422700,0x814700000000520d5d,0x8abf00000000000000,0x1206a41ccc00009a5000,0x12d64bf5b900003bcc02,0x4850000061368443b5,0x894bce760a34e5e25500,0x6400003d230000932c56,0x39810000b5b480,0xb7a692e3a34f00,0x14433513bc0000012400,0x52e10000e2af56924d,0x69110000cb6d00,0x1ce0158c1aeb23747100,0xbe564a6c13456808ab95,0x41aefcca81031d122a0,0xa1fb1ed7338670966e54,0xb4c47581277ba0d3e80b,0x969126146c034e40ab01,0x92bc813d132975d37752,0x687467f7dc89e07088,0xfa06d69e7042031303],#[0xb57b6b5d2c79b955e00,0x476550a0b6740f8018bc,0xec1b0000000049,0x608995f93966718b3b00,0xcff312457f00007546fc,0x329cd804d4bc90065f19,0xe3654327f64908c8ff6b,0xc70000a047f903a55188,0x81f439ca665cade8f329,0x8036c406f1a4f97c3952,0x62db00000000c3bf82,0x3d797aec947575f32200,0x6316d10900a6ec137063,0x73532346f7df2a1f80,0x40407c1ab35ad70a100,0x555c09048c1250054b25,0xd8f5000072b10000e3,0x2521e2fcbc841e000000,0x18a66f15152a03000037,0xd97786e80968c8e60b92,0x14b00d670a23481c1507,0x5a6837c23500b92bc5a,0xdc44a4e5ae9cf1d7f1a7,0xdaf70000019eb8e018,0xd1dbf8c2a9b700,0x15abb2000099f413dd00,0xea70ded7b2cb4bd314c7,0xeb000000003b112b1617,0x57449f95f402ba14d9d6,0x501bb82917]]
def g63D10 := limbs80 #[#[0x186411024010420887f,0x1282a028681202802066,0x5a8aa3a0a8398e4290ea,0x4a90a5a1484a10859906,0x8aa0a9298a721887a94a,0x8260761503406801aa4a,0x6317055138470fe358b,0x4a7a849aa3e871f2759b,0x4e9382d8b40c82feb7ac,0xb2bc8b1b44f0c40efabc,0x701040c0080c15153bcc,0x3001400a3428b0c3860,0x6300aa00ce006700328,0xc802a00a8028007798,0x3bf80190057a00cf0030,0xbe0060028015fa806300,0x9c00ca00ca8061806002,0x801d7003a80338019401,0xa018c029805300ae0065,0x802bd006780190056]]
def g63H10 := limbs80 #[#[0x17000600031701041901,0x71400001b0500041e0e,0x22011000000102080a01,0x805020903064d000104,0x1105070b01004b000300,0x3131104032302000206,0x2519030e060108030405,0xc0f02001303052a0002,0x2050100130e3a281300,0x1d06030078010029020a,0x3009220001001c180102,0xc15030a1e05000a0025,0x273d410018000405032c,0xa000b000b20111c0f32,0x70000101b0801430721,0x8805500c03702210,0x3010932031b001a0104,0x504010708031190014b,0x160d250b410002450092,0x1a060607010400170d00,0x3a4a0c04603702560040,0xc9390003836751757a01,0x646b08621f752f504a71,0xb700034960001241224e,0x453708816b4cf05a6e94,0xc379a6037b4531865d30,0x9940fb3be433557706b3,0xdc27b91ac0000839e0fb,0x45d4209edfe965a5f92b,0xb3c4a7e0256ba98f6d16,0x7b87426c2492e2e876b,0xe09de6055116014cacad],#[0xd1da62205dc000ccd9e4,0x537332cb88af66780000,0x1652fd0e0900c94c0007,0x21f5e6f800030a5cd227,0x5a0b4f7e7cac43672000,0x30caaa240000003,0xa5a40dc989b6a3e3a700,0xd92c000a39322f405eaf,0x325d6c6a93331bf56e,0x49d1de2ac000d9549690,0xc526d7a40000000000a1,0xc9ce380000000108bb7d,0x47367c32cec2f65a1b90,0x3035066c4fc000978ac,0xa81fc802bb00004c2400,0x7361e5b309780001594,0x6aeea858540000e,0x1388000e64f27900,0x6e3e1340000002c46f3c,0x6ad7fd678038f0882c02,0xebcc789766e44ff8467a,0x1c199cb0000000666791,0x5f8000d4d6a240001a01,0xd18bb1bf64870000000f,0x633ae27c00081b6c16e5,0xd5fa56370276f4000c84,0xa4ab9584fbcb78b6b5ec,0xed9f8000688098ccb56a,0x47496f000000001c9601,0x4005005892de0002cfe,0x1592d370001c5d6,0xbcbac79e5b26a9800000],#[0xc137aa7a8823d4000c8a,0xcf95694650000f170002,0xe0002979715f4b47255a,0xab8250871d52fe84a85a,0x614515e14ec8fa090c0a,0x3dcfda39b6e6866ee1c9,0x268ab3a3259cae78f94a,0xe80574fcdb9450583147,0x4283f0f08e077c495837,0x35480002aabb7f41,0x62681860001730f33c00,0x163300004a083334b8,0x532872b0b85e92537400,0x800050aa5addcb956033,0x5ebc912d12c17252b7bc,0xd08af79546c065ce1820,0x6f54954ab6d15a500009,0xc84ced90003b4563176d,0xba74afa6be696e267a63,0x1a369c64cc390d624f0,0x350583d0b24cd1020a00,0x58065fc002bc78efc700,0x9ed852cf7089c04ad925,0xab338000f9a00000002a,0x591d8a12a1aaedc35bb2,0x58fc12d2aaa5bfc7e232,0xc4ca20169e61c2a6ebee,0x7e510001e6609c091131,0xde6189400064a0000bab,0x6e5908000096282c8bd6,0x5d1e8f4bd5850d500026,0x87358c48952041351ad2],#[0x7c473f434d6d75c81e4,0x58a0c19d5c44f50516b4,0x99ab0001d0f4c9913ab8,0xc85000000030f4000042,0x70d91759e07c0000e762,0x600002525430b3795758,0xdadf24a0003e64d6c38c,0x1c8000d3cc889b3412dc,0x69860b538def0626e5c3,0x34b938d144c4236203fa,0xe2db70914c6810000000,0x58e84000063b663d64e2,0x3dbd000017cc0001afe0,0x620e43306e315729dbaf,0xa4b6020002d7c30b64ef,0xef3484a102985b1c8c16,0xc4a7688667346f1ceb98,0x1a3d9a5151ac521020cc,0xfba3c92360bea530ae,0x900003469bac000d1580,0x8608ace0380007cefa2,0xa040ddb48a2e14364000,0x2c671000000043c8dbb3,0x30d8000000025f4000c6,0xf0e8cfac78c1aa5a4000,0x3ec900000000001,0x7b06d88c6ad66cd232c0,0x913d210d2d70eb87,0x3a06c53caaeba30000,0x38dd614610a8a7f0acb0,0x280c08486b00003959aa,0x2f8ab50000aa859034ca],#[0x34be0000cfa0002,0x6c3026c574f800000000,0x7764d30000000f8278a,0x8c41c07c28598b75c000,0x53d108a8f19db150ad08,0xf06ed2f627d0003a37ca,0x63309802eb3e230d3a0,0x2ba86f9ecf747322185f,0x1e0119a1c7646c000002,0xdc8c88291ffe2600039f,0xb0f47ea246d71870458d,0x40d70f6df81a82c3639a,0x6ed20001de3abc5697b2,0xd9144c000047e0ea246c,0x9bb0ed584f1a00092527,0x38c8970ccc2d54e0,0x2d6d2053c5019ab4400,0x4a7a23aaebaa750f0000,0xf0f0c055400065a80003,0xd437263854437b85d5ca,0x96600018e5916c000e0b,0x50cbcb25293c0b9c63,0x9d719eaada54a28247c0,0x30bc179407900009a,0x31c32ffad8d015d0b9cc,0x550086200039bf7,0x51bea6400064f2ace00,0x321d7e9018282c000000,0x4c58d5cfb04000f088,0x6000342026289b57a740,0x61b1eda000351712295a,0x59640f648f434451f313],#[0xd96fb0a4cb3f000c0006,0x9750002988334495e87,0x2d8678400097d216c36b,0x98777e042c18651adbfc,0xb95eca500022df0000c,0x0,0x86800000038cd70a2248,0x9c000d0e518f6219451d,0x62bbeacaa4400075,0xc40a0186b8a01d001000,0xe28c00037282dd38d7,0xa4d002330f8000cd280,0xad0f91600028ee827400,0xa2e0d71655b1dc6416e7,0xa9c08bd07d360abed32d,0xaa56d1a72749c3f30337,0xd761a6dda7ec5485febb,0xe100028df0002a670000,0x80000000e2ff59278c2c,0x8b6e63fd8f227a00011c,0x1d12a0dc44000e7ee968,0x1b39c930000d2b40002,0x2e5ea044000000000000,0x173c8e1e4336685e8000,0x9b20c558b100000000,0xb368aa506b5eea800000,0xec1fb2926732ca9988d0,0x39c95b21f39f27ad0eb1,0xb26826418ddbac9c1aa9,0xb4eaa9fe84330c3da8c3,0xe8d485400000039cfd36,0x92caec64b12c000d5bf],#[0x7ad1cf20d9adc9e66cd1,0xd0c4000000031248b312,0xbbdcc9b86798122c6ec6,0xe0b3ac700006016587b,0x8d21fcd2f1b0712e6f55,0x12cc19fe3ac778000813,0x2eb90141554394487800,0xb7558000000000001f5d,0x3a4d5ce147,0x3a613b00015b6d97c48e,0xf3d0002c3f00023494]]
def g63D11 (j : Nat) := if j=0 then 0x8103f else 0
def g63H11 := limbs80 #[#[0xb9f9215c1c040a3090a1,0x10060359e80038736f5c,0xa6000664c3a2c4fc8e45,0x35a354c1e0864d1800,0x612d0a85d139b9d00314,0x221e534a2e7ccc00109,0xf944a04c8e]]
def g63L : Nat → Packing
  | 5 => (47,6,6,1507364,86,9,1028,g63D5)
  | 6 => (596,5,6,4850105,121,13,1141,g63D6)
  | 7 => (2844,4,6,6030587,123,17,1248,g63D7)
  | 8 => (3412,3,6,2425543,106,17,1156,g63D8)
  | 9 => (844,2,6,786473,70,15,1086,g63D9)
  | 10 => (41,1,6,65537,0,10,1038,g63D10)
  | 11 => (1,0,6,65537,0,0,1026,g63D11)
  | _ => emptyPacking
def g63I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 11 241 1 10 6 0 g63H6
  | 7 => lookupWord 149 683 9 14 10 0 g63H7
  | 8 => lookupWord 711 3251 9 16 12 0 g63H8
  | 9 => lookupWord 853 4201 8 16 12 0 g63H9
  | 10 => lookupWord 211 1039 8 14 10 0 g63H10
  | 11 => lookupWord 10 47 5 10 6 0 g63H11
  | _ => fun _ => none
def g63 : Forest := ⟨63,11,fun i => g63Y[i]?.getD (0,0),g63C,g63A,g63L,g63I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P5_0 : block g63 5 0 47=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g63B5 : block g63 5 0 47=true := g63P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P6_0 : block g63 6 0 27=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P6_27 : block g63 6 27 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P6_123 : block g63 6 123 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P6_219 : block g63 6 219 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P6_315 : block g63 6 315 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P6_411 : block g63 6 411 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P6_507 : block g63 6 507 89=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g63B6 : block g63 6 0 596=true := (@block_merge g63 6 0 219 377 (@block_merge g63 6 0 27 192 g63P6_0 (@block_merge g63 6 27 96 96 g63P6_27 g63P6_123)) (@block_merge g63 6 219 192 185 (@block_merge g63 6 219 96 96 g63P6_219 g63P6_315) (@block_merge g63 6 411 96 89 g63P6_411 g63P6_507)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P7_0 : block g63 7 0 96=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P7_96 : block g63 7 96 6=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P7_102 : block g63 7 102 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P7_198 : block g63 7 198 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P7_294 : block g63 7 294 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P7_390 : block g63 7 390 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P7_486 : block g63 7 486 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P7_582 : block g63 7 582 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P7_678 : block g63 7 678 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P7_774 : block g63 7 774 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P7_870 : block g63 7 870 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P7_966 : block g63 7 966 86=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P7_1052 : block g63 7 1052 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P7_1148 : block g63 7 1148 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P7_1244 : block g63 7 1244 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P7_1340 : block g63 7 1340 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P7_1436 : block g63 7 1436 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P7_1532 : block g63 7 1532 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P7_1628 : block g63 7 1628 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P7_1724 : block g63 7 1724 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P7_1820 : block g63 7 1820 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P7_1916 : block g63 7 1916 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P7_2012 : block g63 7 2012 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P7_2108 : block g63 7 2108 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P7_2204 : block g63 7 2204 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P7_2300 : block g63 7 2300 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P7_2396 : block g63 7 2396 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P7_2492 : block g63 7 2492 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P7_2588 : block g63 7 2588 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P7_2684 : block g63 7 2684 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P7_2780 : block g63 7 2780 64=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g63B7 : block g63 7 0 2844=true := (@block_merge g63 7 0 1340 1504 (@block_merge g63 7 0 582 758 (@block_merge g63 7 0 198 384 (@block_merge g63 7 0 96 102 g63P7_0 (@block_merge g63 7 96 6 96 g63P7_96 g63P7_102)) (@block_merge g63 7 198 192 192 (@block_merge g63 7 198 96 96 g63P7_198 g63P7_294) (@block_merge g63 7 390 96 96 g63P7_390 g63P7_486))) (@block_merge g63 7 582 384 374 (@block_merge g63 7 582 192 192 (@block_merge g63 7 582 96 96 g63P7_582 g63P7_678) (@block_merge g63 7 774 96 96 g63P7_774 g63P7_870)) (@block_merge g63 7 966 182 192 (@block_merge g63 7 966 86 96 g63P7_966 g63P7_1052) (@block_merge g63 7 1148 96 96 g63P7_1148 g63P7_1244)))) (@block_merge g63 7 1340 768 736 (@block_merge g63 7 1340 384 384 (@block_merge g63 7 1340 192 192 (@block_merge g63 7 1340 96 96 g63P7_1340 g63P7_1436) (@block_merge g63 7 1532 96 96 g63P7_1532 g63P7_1628)) (@block_merge g63 7 1724 192 192 (@block_merge g63 7 1724 96 96 g63P7_1724 g63P7_1820) (@block_merge g63 7 1916 96 96 g63P7_1916 g63P7_2012))) (@block_merge g63 7 2108 384 352 (@block_merge g63 7 2108 192 192 (@block_merge g63 7 2108 96 96 g63P7_2108 g63P7_2204) (@block_merge g63 7 2300 96 96 g63P7_2300 g63P7_2396)) (@block_merge g63 7 2492 192 160 (@block_merge g63 7 2492 96 96 g63P7_2492 g63P7_2588) (@block_merge g63 7 2684 96 64 g63P7_2684 g63P7_2780)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P8_0 : block g63 8 0 26=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P8_26 : block g63 8 26 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P8_122 : block g63 8 122 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P8_218 : block g63 8 218 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P8_314 : block g63 8 314 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P8_410 : block g63 8 410 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P8_506 : block g63 8 506 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P8_602 : block g63 8 602 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P8_698 : block g63 8 698 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P8_794 : block g63 8 794 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P8_890 : block g63 8 890 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P8_986 : block g63 8 986 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P8_1082 : block g63 8 1082 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P8_1178 : block g63 8 1178 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P8_1274 : block g63 8 1274 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P8_1370 : block g63 8 1370 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P8_1466 : block g63 8 1466 71=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P8_1537 : block g63 8 1537 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P8_1633 : block g63 8 1633 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P8_1729 : block g63 8 1729 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P8_1825 : block g63 8 1825 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P8_1921 : block g63 8 1921 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P8_2017 : block g63 8 2017 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P8_2113 : block g63 8 2113 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P8_2209 : block g63 8 2209 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P8_2305 : block g63 8 2305 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P8_2401 : block g63 8 2401 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P8_2497 : block g63 8 2497 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P8_2593 : block g63 8 2593 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P8_2689 : block g63 8 2689 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P8_2785 : block g63 8 2785 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P8_2881 : block g63 8 2881 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P8_2977 : block g63 8 2977 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P8_3073 : block g63 8 3073 21=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P8_3094 : block g63 8 3094 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P8_3190 : block g63 8 3190 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P8_3286 : block g63 8 3286 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P8_3382 : block g63 8 3382 30=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g63B8 : block g63 8 0 3412=true := (@block_merge g63 8 0 1729 1683 (@block_merge g63 8 0 794 935 (@block_merge g63 8 0 314 480 (@block_merge g63 8 0 122 192 (@block_merge g63 8 0 26 96 g63P8_0 g63P8_26) (@block_merge g63 8 122 96 96 g63P8_122 g63P8_218)) (@block_merge g63 8 314 192 288 (@block_merge g63 8 314 96 96 g63P8_314 g63P8_410) (@block_merge g63 8 506 96 192 g63P8_506 (@block_merge g63 8 602 96 96 g63P8_602 g63P8_698)))) (@block_merge g63 8 794 480 455 (@block_merge g63 8 794 192 288 (@block_merge g63 8 794 96 96 g63P8_794 g63P8_890) (@block_merge g63 8 986 96 192 g63P8_986 (@block_merge g63 8 1082 96 96 g63P8_1082 g63P8_1178))) (@block_merge g63 8 1274 192 263 (@block_merge g63 8 1274 96 96 g63P8_1274 g63P8_1370) (@block_merge g63 8 1466 71 192 g63P8_1466 (@block_merge g63 8 1537 96 96 g63P8_1537 g63P8_1633))))) (@block_merge g63 8 1729 864 819 (@block_merge g63 8 1729 384 480 (@block_merge g63 8 1729 192 192 (@block_merge g63 8 1729 96 96 g63P8_1729 g63P8_1825) (@block_merge g63 8 1921 96 96 g63P8_1921 g63P8_2017)) (@block_merge g63 8 2113 192 288 (@block_merge g63 8 2113 96 96 g63P8_2113 g63P8_2209) (@block_merge g63 8 2305 96 192 g63P8_2305 (@block_merge g63 8 2401 96 96 g63P8_2401 g63P8_2497)))) (@block_merge g63 8 2593 480 339 (@block_merge g63 8 2593 192 288 (@block_merge g63 8 2593 96 96 g63P8_2593 g63P8_2689) (@block_merge g63 8 2785 96 192 g63P8_2785 (@block_merge g63 8 2881 96 96 g63P8_2881 g63P8_2977))) (@block_merge g63 8 3073 117 222 (@block_merge g63 8 3073 21 96 g63P8_3073 g63P8_3094) (@block_merge g63 8 3190 96 126 g63P8_3190 (@block_merge g63 8 3286 96 30 g63P8_3286 g63P8_3382))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P9_0 : block g63 9 0 9=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P9_9 : block g63 9 9 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P9_105 : block g63 9 105 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P9_201 : block g63 9 201 92=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P9_293 : block g63 9 293 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P9_389 : block g63 9 389 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P9_485 : block g63 9 485 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P9_581 : block g63 9 581 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P9_677 : block g63 9 677 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P9_773 : block g63 9 773 71=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g63B9 : block g63 9 0 844=true := (@block_merge g63 9 0 389 455 (@block_merge g63 9 0 105 284 (@block_merge g63 9 0 9 96 g63P9_0 g63P9_9) (@block_merge g63 9 105 96 188 g63P9_105 (@block_merge g63 9 201 92 96 g63P9_201 g63P9_293))) (@block_merge g63 9 389 192 263 (@block_merge g63 9 389 96 96 g63P9_389 g63P9_485) (@block_merge g63 9 581 96 167 g63P9_581 (@block_merge g63 9 677 96 71 g63P9_677 g63P9_773))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P10_0 : block g63 10 0 41=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g63B10 : block g63 10 0 41=true := g63P10_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P11_0 : block g63 11 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g63B11 : block g63 11 0 1=true := g63P11_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63T : checkedTables g63 11 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g63 0 0 0 = true)
  · exact (rfl : block g63 1 0 0 = true)
  · exact (rfl : block g63 2 0 0 = true)
  · exact (rfl : block g63 3 0 0 = true)
  · exact (rfl : block g63 4 0 0 = true)
  · exact g63B5
  · exact g63B6
  · exact g63B7
  · exact g63B8
  · exact g63B9
  · exact g63B10
  · exact g63B11
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63G : graphValid g63 (boundsBefore K2110) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem fullLower : Impossible true graph 11 rawSix.toFinset := by
  rw [show graph = targetOf g63 by decide +kernel]
  exact root_index (g:=g63) (top:=11) (i:=0) (before_sound K2110 V2110) g63G g63T (by decide) (by decide +kernel)
end PEqualNP.Outside.L_meta_43634
open PEqualNP.Outside.L_meta_43634 in
theorem PEqualNP.Outside.L_meta_43634 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809440 * 2 ^ 32 + 4008372416) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276809440 * 2 ^ 32 + 4008372416) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  rintro s ⟨⟨gates,o⟩,fit,sz,correct⟩
  have legal : ∀ g ∈ gates, (g.op=PEqualNP.CircuitLowerBounds.GateOp.and ∨
      g.op=PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op=PEqualNP.CircuitLowerBounds.GateOp.not) ∧
      g.inputs.length≤2 := by
    intro g hg
    simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using fit g hg
  obtain ⟨gs,out,mono,small,ok⟩ := replaceShort fullLower gates o legal correct
  refine ⟨⟨gs,out⟩,?_,small.trans sz,ok⟩
  intro g hg
  simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using mono g hg

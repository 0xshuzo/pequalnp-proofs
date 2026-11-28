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
private def pages512 (a : Array (Nat → Nat)) (i : Nat) : Nat :=
  ((a[i/512]?).getD (fun _ => 0)) (i%512)
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
def g63D5 := limbs80 #[#[0x1c0634848794d5148110,0x5009220d6519540e6170,0x6087359540608821cd65,0x2ec1ee61701c06354791,0x8e31e13d15c93c5cc33c,0xc5d4bc52bfd0b8c926d4,0x252505293d212521a52,0x244070c1420304040]]
def g63D6 := limbs80 #[#[0x20d711483020f7648020,0x59171148305517114830,0x61854484301cc5248430,0x1d473484301507348430,0x60073484305907348430,0xdd07348430a107348430,0x1ce424843020d5448430,0xa0e5248430a0e4248430,0xdda5448430dda5248430,0x60073544301cf2148430,0x20d54c84306067295030,0x59171d0830e1d64d0830,0x1d07058432e116158032,0x1cc53484405d26498032,0xdd07348440dd85348440,0x1ce4348440e107348440,0x1cc325444061a7348440,0xdd03254440dc83254440,0xdd05354440dd83254440,0x1ce6354840dd33254440,0xdd562cc44021e6354840,0xa0f75cc440a0f72cc440,0xe147348450dd84348450,0x1cd614845010d6148450,0x1ce434845090d6148450,0xdd073584506084358450,0x20d42584501cd4258450,0x10d725845021d4258450,0x90d725845020d7258450,0xdd3325845094d7258450,0x608630c91060b7458450,0x6086310d1018d710c910],#[0x18d7010d106106310d10,0x9cc6318910e146314910,0x5d07418d105c87218d10,0x5d47518d106087418d10,0x1d17218d106087518d10,0xdca7218d109d17218d10,0x94d514811021d5148110,0x604325011018c3250110,0x1cf3250110d883250110,0xcc9515411021c6350910,0x20d7494910e146354510,0x60432d011060863cc110,0x5d47518d205d07418d20,0xdd75418d206047518d20,0xd5063545201cc6354520,0xd5073545205507354520,0x1db54545201da5354520,0x6075494d20a0f5454520,0x6006314d215d06314d21,0xa106314d216146314d21,0x5d0641812120d7015121,0x5d06418d219ce4318121,0x5c07018d216006418d21,0x5d07418d219d07018d21,0x5d47518d216007418d21,0x2117018d216007518d21,0xdd17018d215d17018d21,0xe117018d21dd57018d21,0xdd75418d219d27018d21,0x20d70909216007359521,0xd506390d216006390d21,0x20d709492120d5490d21],#[0x20063c852120d7095121,0xe0063c852160063c8521,0x9cc63d812120d70d5121,0x19673d91219ce42d8121,0x20d650c940594650c940,0xd96650c9405d1710c940,0xd97540c94061f540c940,0x94d711494018d7114940,0x6146314d406086314d40,0x18d7214d40a086314d40,0x20d6518940e1d6218940,0x6047218d405c87218d40,0x6047518d405d47518d40,0x20d65195405957218d40,0x6103248540e096519540,0x18c53485406105248540,0x1d853485401cc5348540,0xa0853485406105348540,0x18e43485406187348540,0xdd032541401ce4348540,0xa0f52545401d83254540,0x1d432585401cc3258540,0x2087358540dc83258540,0xa0f625854018f3258540,0x60873595402087359540,0x14d7194940a087359540,0xa0f62989406067294d40,0x99463cc94060762cc540,0x59465cc940d5063cc940,0x18d52d454018f32d4140,0x20d72d514020d72d4540,0x20d65d8940a0863d8940],#[0xe1d42109509db540c950,0xa086310d506086310d50,0x6047218d505c87218d50,0xd517218d505d07418d50,0x1cc63485506075418d50,0xd507348550d506348550,0xdd032545501db5448550,0x18d719095018f3254550,0xa0863cc95060863cc950,0x1db54cc950d5063cc950,0x18d42d4550e0863d4550,0x9cc63d895020d42d4550,0x600630c951d5273d8950,0xa00630c951608630c951,0x18f521815161f640c951,0x60063189519cf5218151,0x5c07018d51a0f6418951,0x9c87018d515c87018d51,0x6007218d515c87218d51,0x1c97018d515d07418d51,0x9c97018d515c97018d51,0xdd17218d51dc97018d51,0x9cc63d4951dca7218d51,0xa0f64d4951d9063d4951,0x5517114e2020d6414a10,0x1d0734864090d7114a40,0x1ce4348640dd07348640,0x59754cca40dd33254640,0xe1d640ca50e056218243,0x1cc5348650593320ca50,0x9cd72d93305905348650,0x60273d973160273d8b31],#[0x1ce43487501cc5348740,0xb1de2fc3f87d0ee17c1f,0xbe93d1f97b2ee5bc9f8f,0xcbd67aaf4f69dd37a6b4,0xe1bc1f6d6d9dadb4f676,0xec7b8ef1be33c5f8af0f,0x2ba3f3e676ce799f2e63,0xc3f5e6b5d67a9f4ee97d,0x799f2ee5bc9f8f71de2f,0x6f93ee9d9bab755e6dcd,0x887185221e6108894872,0x2401e608a79742302e60,0xb207982c00e608e7175,0x84b1b6184a35960f80e6,0x456281825800e61300b9,0x98622be5470ac831d0fe,0xe60de0f983681e618c0b,0xf98708d250f403983881,0x25900407987302e61c80,0x22934e0ce5d105493443,0x9065862e873182c24936,0xc0941c3020c72c0831b,0x636592022c931e30e507,0x9e6b912b29a4c98a4932,0x2722a1ca01c9727b018c,0xca6c0632bb6d90a28687,0x41f3a6507c5a962a3c1c,0x58a4be841eaf6107aea9,0x842184a58aa75872104a,0xe447eee9220bb6488285,0x9842236e5c80b9841f9a,0xde149431952490a4c928],#[0x1197781fe608a4594259,0xb3d50b87598303ba0c00,0xe76862f08660ba74872e,0x18ca4cc27476311da18b,0xb47f982c1d61cb620963,0x6bf640247786789d5d4,0x81e85860221dd81c8586,0x603906581613980821dd,0x5012f89404a861012419,0x96033be5812f49504bee,0x66010da8404366101041,0x970293a541443980410,0x4e60221a97062e590181,0xa28209a860826b9640a8,0xb7e442eef9609be25026,0x48564008e6442c7f980b,0xe84e58281098019de180,0x36d9960fb9a49fae5927,0xe84e603841960da1618,0xc528693101f6183c5293,0x611096585625961519a4,0x1846419610a161842898,0x911394a4c4c1398121f6,0x5d1747e8653906445041,0x297529f1d93c7c764eb6,0x1a1d3e88765190a594c4,0x868650266114042974fa,0x84661427c765110a5940,0x8e765b0ee5148139850,0xe2c20d7674765484e615,0x5686865522a195812965,0x569d1d55ecc75571da19],#[0x9187587469f219149d82,0x745a19d91223984404a5,0x4d7225985c096616e758,0x98471d2191e23985c952,0xa4d2888934a3318d6612,0x9975f2261d6abd924aa2,0x1a6126be925faf6497e2,0x4197492161d20b185482,0x8ee513410965a15e4522,0xa75754ca2e612c89724b,0xdaca4936b1924d84a597,0x62848658a760960b3924,0x7a9066164cc9558bae45,0xdec52937a14a4de6d996,0x4802620de454937b94a4,0x6058d3951792a5c5c998,0x831a1aa4c7675861684e,0xa5c6a2c981a2321c68c0,0x7951c0ba606e2e931b0b,0xb25c64c2941c3065070b,0x858464b3d51926a93198,0x5661967687651d21d94,0xacf7467056619a329366,0xa08a59acab646b2c20da,0xa056966905e618056936,0x6995645a4bd8468c0d51,0x1ae1298679fa59827686,0x761ae6118432966c33d5,0x61888972628ca598e419,0x877e33591f6b0936422e,0x655f243977d0c25df876,0xf9834a1a18d476957c9d],#[0x160102119843106510a7,0x59954098651026a9340b,0x9aa4d065b954118e5104,0x8b9843e04a58fe12963d,0x289a58fc25983e95254f,0xcab1853297e50ca5c943,0x3390e60c841983210e5c,0xd67d743615e50ccb185,0x536b8e50dae094369fe6,0x14dc7d843724e60dad49,0x853a9d214e83295371d6,0x24cee7f75399f5d4e674,0x5873c8ca54f012983b2e,0xd5d4e47f98379f5d0e07,0x12964004a58d03394389,0x36250f411984384a5908,0xe53947f14251fccc953d,0xeaca0dba53947f94251f,0xb276866f08e61ba75876,0x6d97e51b25c946caf609,0x5b8be846d2f611b4bd82,0x6779de1ddccf64769de5,0x51c2119770219cdbe767,0x847121a0dc4939870b82,0xe11ce7d84719fa11c47d,0xf84749fe11d07c84741f,0x25c9ca7f84751f211d47,0x12970c11641d8429375a,0x1f5d1f075850c9fe6034,0x2482081b81400e809000,0xc04703e83603202e02a0,0x7907406985f85885004],#[0xa209e09809108d08607d,0x20cb0c20be0ba0af0a60,0x8fa8f10ed0e50de0d60d,0x1691290e90a9069028fe,0x292e92a92692291e91a9,0x94a94694293e93a93693,0x6696295e95a95695294e,0x297e97a97697296e96a9,0x99a99699298e98a98698,0xb69b29ae9aa9a69a299e,0x29ce9ca9c69c29be9ba9,0x9ea9e69e29de9da9d69d,0x6a029fe9fa9f69f29ee,0x2a1ea1aa16a12a0ea0aa,0xa3aa36a32a2ea2aa26a2,0x56a52a4ea4aa46a42a3e,0x2a6ea6aa66a62a5ea5aa,0xa8aa86a82a7ea7aa76a7,0xa6aa2a9ea9aa96a92a8e,0x2abeabaab6ab2aaeaaaa,0xadaad6ad2aceacaac6ac,0xf6af2aeeaeaae6ae2ade,0x2b0eb0ab06b02afeafaa,0xb2ab26b22b1eb1ab16b1,0x46b42b3eb3ab36b32b2e,0x2b5eb5ab56b52b4eb4ab,0xb7ab76b72b6eb6ab66b6,0x96b92b8eb8ab86b82b7e,0x2baebaaba6ba2b9eb9ab,0xbcabc6bc2bbebbabb6bb,0xe6be2bdebdabd6bd2bce,0x2bfebfabf6bf2beebeab],#[0xc1ac16c12c0ec0ac06c0,0x36c32c2ec2ac26c22c1e,0x2c4ec4ac46c42c3ec3ac,0xc6ac66c62c5ec5ac56c5,0x86c82c7ec7ac76c72c6e,0x2c9ec9ac96c92c8ec8ac,0xcbacb6cb2caecaaca6ca,0xd6cd2cceccacc6cc2cbe,0x2ceeceace6ce2cdecdac,0xd0ad06d02cfecfacf6cf,0x26d22d1ed1ad16d12d0e,0x2d3ed3ad36d32d2ed2ad,0xd5ad56d52d4ed4ad46d4,0x76d72d6ed6ad66d62d5e,0x2d8ed8ad86d82d7ed7ad,0xdaada6da2d9ed9ad96d9,0xc6dc2dbedbadb6db2dae,0x2ddeddadd6dd2dcedcad,0x484c0f821919d000ade,0xd0c824b8004c6280ae,0x582413a0981b07446704,0x1b83e06514131c3133c1,0x3006619188600830ca,0x3a10000000030000b721,0x50cb61dc210000427420,0x9b0afc84000101e50f61,0xa871b310000190f6c201,0x791006302df31000005f,0xcec4001e45ac08]]
def g63H6 := limbs80 #[#[0x120a80,0x300000000000000000,0x35a0000000000,0xc1000000000000000000,0x1678004980000011,0x654005b800000f6000,0x308000000000000,0x0,0x0,0xb26ae00484ac800,0xb58000000000588,0x0,0x1a300000000,0x1a20000000000000,0x3100000000,0x64a000000000000000,0x4f80000000cf00000000,0x61c00001c1801,0x2528480000515ac498,0x6360000123f8c00000,0x0,0x5ba000000000123ab4,0x8000000000001b188a,0x1,0x0,0x4b00600000a400144c2a,0x10b,0x0,0x1c00000000000,0x0,0xc5800]]
def p0 := limbs80 #[#[0x48020551200815414c20,0x80735042098d2108376,0x98d5108073544205d941,0x584201cd540837254420,0x8074584201cd6108043,0xdd161082545842055161,0x10830508420c154d4420,0xc152148305d8420c165,0x5c4520c1641483055052,0x48430109210c17614830,0xc07348430151210c052,0x551210c075484301d121,0x48430909210c16448430,0xc32148430951210c252,0xdd5210c37448430d5121,0x504301c9410c37648430,0xc37250430d09410c073,0x1cd510c07254430dc542,0x55030d49510c16154430,0xc371550301cd540c072,0x951610c07458430dc954,0x58830951620c34258430,0xc371590301c9640c354,0x9ce420c17190830dc964,0x948309ce520c34290830,0xc172950305c6540c352,0x593210c154c84309ca54,0xd0430593410c142d0430,0xc272d04305db410c172,0x5c7420c165d083059342,0xd4430553510c176d0830,0xc164d48309cb510c172],#[0x5c7540c176d48305c752,0x150329cb540c172d5030,0xc976550325c0540c965,0x585600c95458032dc154,0x58032595600c96458032,0xc874584321c1610cb75,0x991610ca545843255161,0x59032dd1610cb7058432,0xc96198032552600ca65,0x992600c975980325d260,0x994325c2640ca6598032,0x10170d4832553320c970,0x5c45310171148405c432,0x4844014d211017214c40,0x10161484401d52110073,0x98921102534844090d21,0x484409cd211026348440,0x1037648440dd52110374,0x1cd5110053544400c951,0x54440589511016154440,0x103325444098d5110262,0xdd1511037254440d4951,0x5484098d521007354840,0x10073584401c96110371,0x9496110175584405c961,0x948401cd651005358840,0x1007298c405c66210171,0x54b311037198c401d663,0xcc4405cb3110162cc440,0x10375cc440dcb3110332,0x5c75210172d444054b51,0x584421cd6010b7650842],#[0x1437098c425c66210b70,0x58521140734845010d21,0x4845090d211416448450,0x140735045098d2114253,0xdd541141765045058541,0x5845010d611407350850,0x14074584501cd6114072,0x5d161141725845050961,0x58450cc9611424258450,0x1437458450dc96114342,0x1cd6014b76548525c662,0x584521c1611484358452,0x14a43584525516114873,0xdd16114b705845294d61,0x98c52dc26314b7590c52,0x14d54584531c16114f71,0xdc96015073580545c662,0xc91018c324417198854,0x441760c9105c43244170,0x9cc42441761091018c42,0x10d1018c434436210910,0x44063149105c44344170,0x94c5244176149105c452,0x14d10d88524427314910,0x4417114d105c05344063,0xd945444176151105d853,0x18910588624406318910,0x442731891090c6244174,0x194634406418d1015063,0x18d101d0634407218d10,0x4416518d105906344075,0x5d4634417418d105c863],#[0x18d10990634425418d10,0x4427418d109c86344265,0xd90634435418d109d463,0x18d10dd0634437218d10,0x44165195105906444375,0x50520440634811018920,0x50110dc5204415148110,0x44063501101894044032,0xd894044332501101cd40,0x50910509414406350510,0x44076509101cd4244063,0x54550440635411018950,0x54510d89504433254110,0x440655451018d5144053,0xd4951443325451094d51,0x5891018d624435454510,0x442535891090d6244073,0x1cd644407259110dc162,0x59110dc9644436459110,0x44043881101cd6544373,0x95220442438811019220,0x9091018e424427688110,0x4406490d109ce4244176,0x18e524427290d105ca43,0x94d105da524417494910,0x4417695110d525344174,0x9ce64443629891018e62,0xc811018f204427399510,0x44062cc91018f3044362,0x5973244164cc91019332,0xcc9109533244174cc910,0x44063d01100cb4044364],#[0xd8b4044332d01105db40,0xd091018f4244062d0910,0x44063d41105db4244171,0x5db5244171d491018f52,0xd51105c75444165d5110,0x44063d89109cf5444176,0x90f6244174d891019362,0xd95109536244253d8910,0x483650c9205503248174,0x5c453480631492018c42,0x18d20190634805418d20,0x4807518d201d06348065,0x5d4634817418d205c463,0x18d209d0634825418d20,0x4836418d20d506348275,0xdd4634837418d20dc463,0x5012018d404803250120,0x480765052018d4148073,0x18d5048032541205d541,0x5452018d514805354520,0x48154545201d95148073,0xdd151483545452094d51,0x909205c6424806390920,0x4817190d209da4248273,0x18e5248053949205d643,0x9492094e524815494920,0x4817494d20d525248276,0x18f204827395120d5253,0xcc5205d33148154cc520,0x48063d0120dd73148374,0x18f5048272d052018f41,0xd51205c75448063d4520],#[0x48171d912094f6148273,0x18c42487640c9215d365,0x10d21194434857010921,0x4867610d215c04348565,0x5c0524846314921d9443,0x14d21550534846314d21,0x4876414d219c85348570,0x18c6048443181215c054,0x18121194604846418121,0x48643181215d06048554,0x9cc60486541812194c60,0x18d21190634845418d21,0x4847418d211c06348465,0x5c0634855418d211d463,0x18d215d4634857418d21,0x4867418d219c06348654,0xd90634875418d219d463,0x18d21dd0634877018d21,0x48676191215c06448775,0x1955448574195215c065,0x551211d9544847355121,0x4847359121dc15448764,0x18e4248774595211cd65,0x90d2118e434857090921,0x4847590d211c24348465,0x5c2434855490d211da43,0x90d21d92434875490d21,0x485709492118e5248765,0x5d2534857094d2119653,0x94d21d52534867694d21,0x48676951215c25448764,0x18f214865498d2155263],#[0xd51215c35448554c8521,0x48463d81210cb6048673,0x94b6048643d812190b60,0xd81219cf6048653d8121,0x48470d91211976448764,0x9cf6448570d91211cf64,0xc9405d36548770d9121,0x501520c9401d83250065,0x59432501620c94055032,0xc9405c432501700c940,0x501760c9405d43250174,0x9d432502740c94099432,0xc940cc832502760c940,0x503650c940d503250352,0x5c452501521494018c52,0x14d4094c525017614940,0x5017214d405c45350063,0x5886250063189409c853,0x189405c4625016518940,0x5007218d409d86250263,0x5c4635016518d401d463,0x18d405d4635017218d40,0x5027518d409c86350265,0xdc8635037118d40d5063,0x48540594655037518d40,0x50053485401492150032,0x1cd21500654854018d21,0x485401d9215007548540,0x50243485409092150154,0x9cd21502534854094921,0x48540d51215027648540,0x5037548540dd12150365],#[0xcc9415003250540dd921,0x541401cd425037050540,0x50063541401895050032,0xd895050332541401c950,0x545400c9515037254140,0x500725454018d5150053,0xd495150332545401cd51,0x54940dd9515037254540,0x50371549401cd5250063,0x1c96150063585400c961,0x58540cc9615007358540,0x5007359540dc96150362,0x5c6425006390940dc965,0x90d405c6435006390d40,0x50053949409ca4350172,0x5da52501719494018e52,0x94d405ca535035294940,0x503629894018e6250272,0x14f2150273995405ca65,0xc85401972150063c8540,0x50365c85409db2150073,0x1973150062cc54014b31,0xcc5401d73150072cc540,0x50172cc54054b3150076,0x9cb3150252cc54090b31,0xcc540d4b3150332cc540,0x50365cc540d8b3150354,0x18f3250375cc540dcb31,0xcc9405973250065cc940,0x50354cc9409db3250265,0x18f5050032d4140d9732,0xd4540d8b5050332d4140],#[0x50152d454018f5150032,0xccb5150272d45405cb51,0xd49405c75250063d4940,0x50171d51409cf5250176,0x9cf5450272d51405cb54,0xd854018f6150032d8540,0x50362d8540ccb6150142,0x5976250063d894014f62,0xd89409976250171d8940,0x5046314941d536250273,0x580605056514d415d852,0x18941588625073218141,0x5066518d415c86350570,0x1cd655056519541d5063,0x9494118e425077459541,0x50463989415da5250463,0x5db5250463d494159732,0x14d425c36250554d8941,0x5097118d425c06350971,0xd506350a7018d425d463,0xc9505c7545087359542,0x541420c9501d83254064,0x5d032541710c9505c032,0xc9509d032541760c950,0x543420c950cc83254276,0x18c42543640c950d5032,0x10d5018c435414210950,0x54063189509c84354172,0x1c86354273189505c462,0x18d505c4635407418d50,0x5427218d505d06354172,0xdc4635435418d509d063],#[0x48550dd0635437218d50,0x54076485501cd2154063,0xc8521542734855090d21,0x48550d91215435448550,0x5406350950cc94154374,0xc95154371509501cd42,0x90950cc9515406354550,0x54342909505c64254063,0x9ca435417290d505c643,0xc85501cf2154063c8550,0x54331c85509cf2154243,0x9cb3154172cc55050b31,0xcc95018f3254332cc550,0x54354cc9505c73254064,0x50b4154063d0550d9332,0xd05509cb4154172d0550,0x54273d095018f4254332,0x50b5154063d45500cb51,0xd455090f5154242d4550,0x54142d85505c75454332,0x5d36254063d895010f62,0xd9150d536254273d8950,0x545540c95118c3254571,0x18c42547640c9515c032,0x10d5194c425457010951,0x5476414d519d84354570,0x18c60544621815114c60,0x18151d48605473218151,0x544631895110c6254762,0xd906254673189515c062,0x18d511c8635447018d51,0x5457218d515c06354474],#[0x9d0635467218d519c063,0x18d51d90635475418d51,0x5446350951dc86354770,0xdd15254462549511cd42,0x9095118e425447355151,0x54462cc95118e4354762,0xd533254570cc95155332,0xd095114f4254764cc951,0x54653d09515c34254463,0x18f5254443d49519db42,0xd49515d35254570d4951,0x54432d8151d935254673,0xccb6054463d815118b60,0xd895110f6254752d8151,0x54574d89515c36254463,0x9cb6454572d9151d9362,0x18d525c06354a73d9151,0x55171d915210f6154a74,0x5c46355171189545c062,0xd89549c8635517218d54,0x8416414a105903284170,0x590538427314a1098c52,0x59210551628407350a10,0x84372592101cd6484072,0x5db4284254cca1059332,0xca209cf5284164d4a10,0x881760ca205943288154,0x5d8438816510e2098c42,0x14e20550538826314a20,0x8817114e205945388164,0x5854188073506205d854,0x5462014d518817650620],#[0x88161546201cd5188072,0x55161880735522098d51,0x592201cd648825458620,0x88374596201cd6588371,0x98e528817190e2098e42,0x98e20952638815498e20,0x88254cc6205933188354,0x5935188263d06205db41,0xd52209cf5188263d4620,0x90273d52205c75488165,0x5d432901710ca4059432,0xca40d4832902750ca40,0x9017114a405485290354,0x5c4539024314a405d852,0x486400c9219027214e40,0x900734864014d2190043,0x90d2190164486401d121,0x486409cd219025248640,0x9037548640dd12190354,0x1cd429037050640dd921,0x5464010d519003254640,0x90161546401cd5190053,0xdc9519035254640cc951,0x54a401cd529037454640,0x90142586401cd6190371,0x1cd6590073592401cd62,0x90e405ca439017190a40,0x9005394a4010e5290272,0x9ca539017494a405c652,0xcc6401cb3190052cc640,0x90172cc64054b3190075,0xccb3190252cc64090b31],#[0xcc640d533190352cc640,0x90164cca40dd73190372,0x54b5190354cca4059732,0xd4a405c75290172d4640,0x90165d524090f5290176,0x9cb5490172d52405c754,0x14e425c0539095414e42,0x90961582421cd5490b65,0x5516190873586421c161,0x98242dc16190a6358642,0x9087098e4298e6090961,0x5846090d6018243dc663,0x182435c46090d6218243,0x90d65196435886290e62,0x5876090d7198a435c865,0xd82435c76090d62d8243,0x941640ca5058b6190e62,0xcc832941740ca505c432,0x10a5050842943420ca50,0x940434865094c4294176,0x1d521940734865014d21,0x4865090d219416448650,0x94321486509cd2194263,0x5d9419437648650dd121,0x50a50dc9419433250650,0x9407358a505096194371,0xdc56494073592501c964,0x90a5014e429437259250,0x94043c86505c66294171,0x5932194073c865014f21,0xc86509cf2194243c8650,0x94172cc6505933194331],#[0xd0b3194332cc6509cb31,0xcca505973294164cca50,0x94332d06505db4194171,0x5c04394a53d0a505db42,0x5865210d619485358252,0x94a6398252d516194853,0xdc6639497098e521c263,0x98a549cb5494d71d5253,0xc807098e545c66295170,0x1cd40c82634872059454,0x543201cd50c826350320,0xc8154547201cd51c8263,0xdd151c82635472094d51,0xd53205d331c837458720,0xc84735532155063c8765,0x55263c847358321dc154,0x14b3050842cc154cc721,0xcc052487305c452cc152,0x5d521cc164487301d521,0x4873094921cc24348730,0xcc37448730d9121cc354,0x1cd40cc37648730dd521,0x547301c951cc07354330,0xcc37254730d4951cc152,0xd5162cc25458b30dd152,0x90f305ca43cc17190b30,0xcc171d53305c652cc272,0x5cb64cc170d93309cb54,0x14b3155052cc673d9330,0xcc465553319cc52cc564,0x55162cc6525833190960,0xccb3155262cc65458b31],#[0xcc765d0b3195332cc554,0x9cf62cc673d833159352,0x14b325c042cca73d9731,0xcc971153325c054cc970,0x5c754cc9709933255161,0x14f405c452d01710cb40,0xd00734874014d21d0171,0xdd921d0263487401d521,0x54340cc950d003254340,0xd0053547400c951d0372,0xdd951d037254740cc951,0xcc7405c662d007354b40,0xd0775cc740dcb31d0152,0x94960d0473583410c960,0x98b41dc960d073258341,0xd0b7098f411c263d0570,0x1c165d0873583425c453,0x48750dc263d087098f42,0xd42634875090d21d4073,0xcc961d4332547501cd51,0x50b515c662d437458750,0xd4432583511cd52d4473,0x90960d4542583511cd60,0x583525c262d473258351,0xd497098f521c263d4873,0x1cd61d507058754dc263,0x98b545c262d537058754,0x87f7198f541c263d5171,0x9da6f97e3f8fa3b8de2f,0xa769ba5e8f9fe7e9f277,0xadeb5aceafab6aba9e9f,0xb76dcb5ecfafebeaf6bb],#[0xbfafdbeef7bdaefb7ede,0xcb72bc9f1fc771bc5f0f,0xcfb3dcef37cdb35ccf2f,0xdbf67d7f5dd6f57d3f3f,0xe5f8fdfb7ddef77ddb75,0xedfb3ebfade9f9fe779b,0xf9fddf73d7efbbdeefb9,0x10e440510e43ff6fcfee,0x488a10c46411065545,0x636da0c6368fb004a0fb,0x56011063780f0837198c,0xc40f0839811063995cea,0x4790a3c499083c4b1063,0x98c638da0c63881f0e3c,0xf083b598c63b1a0c63ad,0xc858411063b8030e3bc0,0x442c7106580790458186,0x42c690a42c910642c990,0xc176c84bd7ec84b80f0e,0x996e64b990e64b948ea4,0x90e64c55eea4b958ea4b,0xeea4c558ea4c596e64c5,0xea4c956ea4bd50ea4bd5,0x6430790443156ea4c950,0x1b4070e4306908430710,0xa8430007075071e8070f,0xd98e60c172c80a843000,0x4aea13443000fc43000b,0x2c80cc43000cc4300105,0xe822186e81f1a4e72797,0xa24cbd0624ca30825d86,0x8bc1106ac8850a24c830]]
def p1 := limbs80 #[#[0x90070e90471069041f0e,0xd66ea2d566ea2bd86e8f,0x830a308830a300030c2d,0x5082e8a3082e8bd062e8,0x873d82e82f0b9062f8a,0xeb381f0eb24270eb1c0f,0xd4d5ee8d7958e6d78070,0x5c030f048070e1680f08,0xf09198030c34083033,0x5aeb08c270f0780f093b,0x70f0915acb0941f0f08d,0xe6439b0e6435b8c64440,0xa4d45b0e4d2b4a6441a8,0x44c2b0e525b4e65290b0,0x558ec8455a8e64502d0e,0x82d0e475e8e647c29065,0x50649e68c8461a8e647,0x50649105064a1050c495,0x6539ab0e3667b043650,0x653c290c5408f0a538c1,0x375b4e6380af0853cc10,0x798ec837c2f0e3742b0e,0x42d0c46da8e646829063,0x2f0e4e42b0e4e5ace64e,0x8c656829064e98ec84ec,0xea564ab08565ace6565b,0xe5642b0e5656cea5656a,0x3a5eca6394290656c2f0,0x916cec39db4e63a64ca6,0x96eca3a02f0e3902b0e3,0x2b0e4fdace64fc290639,0x8c657829065042f0e4fc],#[0xe5742b0e575ace6575b,0x63c0c9063c4290657c2f,0x4a58ee84a588e84a5ace,0xac2d064b56eea4a568ea,0x9ab084a9a8e64b1a8e64,0xaf0a4a9ab0a4a9af084a,0xb0a5942b0e515b4e6519,0xe386630838429065988,0x250dab0e3aa430a3a9ab,0x3d8290c5088d0c50d030,0xd88b0a3d98ae83d8c506,0xccf043ecc9043ec8d0a3,0x2b0e4048f0a3ec890a3e,0xf043f0c9043f0c5063dc,0xe408af083f0a9083f0c,0x83e0ab083e1b2e43e02b,0x3f48d0a3e08b0a3e0ad0,0xc8f0a3f4890a3f4d702,0x2b0e400c506401b6e44,0x2b0e418c5064182d0e40,0xd043e4cb043e42d0e418,0xa3e48b0a3e58ae83e4c,0x43e8cb043e98ee84108d,0x3e8ad083e8ab083e8cd0,0x1029063b96eea4156aea,0x889065818ec858c29065,0x8ec84bca90642c290658,0x8ea4bdb0e64c5b0e64b9,0x44bdab044bd6eea4bd6,0x44cc89064318ec851daf,0x5a96eca521af044cdab0,0x5cc106e542f0ee2c2906],#[0x2f0ee31ace6e342906e,0xc6ec0042f0ee3c2f0ee6,0x308009c506009c106009,0xa009c30a009c708009c,0x60142b0c011a8e600dc7,0x18290e01db4c6020290,0x382d0e02a3ac80402b0c,0x2d0603c8b0a0302d0e0,0x2b0c0256aec0023ac800,0xec8608290e605ace667c,0xc688290c684290e61d8,0x6610290c6142d0c68c2d,0x695ace6695b0c66982d0,0x202f0e6942b0e694ab08,0x5a8e662568ec63568ec6,0x2d0c6282d0e624290e62,0xd0c63d68ec63968ec630,0xe65b5ace66a02d0662c2,0x664c2f0e641ace6641ac,0x6656cec659ace65b82d0,0x602f0e65dace665d6cec,0x2d066696cec66d6cec6,0x290c5bc290c654290c65,0x5065c4290c6708d0c674,0xea5c8c5065c98ae85c4c,0xe5ec2d0e5e02b0e5e16a,0x5cccd045cc2d0e5ec2b0,0xe48b0a5e58ee85e58ae8,0x96aea5d0cd045d08d0a5,0x290c6a58ec86796eea5e,0x9066b429066b16eca6a8,0x6ea02b0ce99b8e6e9c2],#[0x6ef42f0eef9ace6ef829,0xea9e0a6ea9b8e6eb0290,0xb48b0cea56eecea5b4c6,0x42b0ceac290eeb5a8e6e,0xace6e81ace6ed5ace6e7,0xf0ced82f0ee79ace6edd,0xee896aece842f0ce902,0xeee4c506ee48f08e8c2f,0xeb82906e942d0eee82d0,0x96acaf102f0cf0c2b0c,0x2d06ed02d06ec88906f,0x8ac91bc290f1c1a8e71c,0x90f1c9a8e71c82b0d1bd,0xf1b9a8e71b82b0d1c42,0xd1d56eed1d42f0d1e429,0x1cc290f1d9a8e71d88b0,0xe02b0d1dc8f0d1d02b0d,0x1230007208e60902d071,0x290e081aac8072130007,0xac80b02b0c0a4ab0c0ac,0x61318ac81298aec1218,0xc0c58f0e1242b0c1304d,0xbc2b0c0b88b0c0c56ee,0x442b0c14c4d0614e1300,0xc2d0e0e08b0a0e23ac81,0x8aec0448b0a0d82d0e0d,0xac80b42f0e0483f0e045,0xc813d8aec1002f0c0f98,0x605c2f0e1398f0e1358a,0x516aec0502f0c05c490,0x596aec0563ac8054370e,0x42f0e1516aec1082f0e0],#[0xcd040e82d0e0e4cd040e,0xb0c0c98ac80d02d0e0e8,0xc810c2b0c0d58ac80d42,0xc15c2b0c1158ac81118a,0x22c2b0c1656aca1602f0,0x45e0e5248490721c2d0f,0x8370f2083f0f2044d072,0x2d0f258c507258cd0525,0xce727c2d0f25ccd0525c,0xe61f5b0e61fdb8e61f1a,0xe201ace6201a8e6201f8,0x1e9af0e201a90e200290,0x42b0c1e96cca1e96aca,0x3d062082b0c2056aca2,0xc30c28a42ca2882d0621,0x8e62216aca285acc6284,0xc2356eec23644c6235b,0x6229b0e622648a62248b,0x21a44c6219acc6239b0e,0x2c8b0c2196eec219d6e8,0xe410a22c290e22da8e62,0x3d0623c2b0c21da90e22,0x106255acc629a44c6294,0xc61d4d106258d304250d,0x61d82f0c1d56aca1d5ac,0x245acc62482f0c1d9acc,0x682b0c241a90e245a8e6,0xccb02261acc629dacc62,0xacc61dcc90626c290626,0xaca1e1acc61e02f0c1dd,0x2270c304279aee42796,0x4264c304274c302274c3],#[0x9758ee897c2d0e96c8b0,0x9d8ee8971a8e69702d0c,0x4290e915a8e69158ae8a,0x2d0c93c2d0c91c2d0e91,0xd069542d0c9402d06924,0xca5c2d0ca29ace6a202,0x69882d0c99168ec99c2d,0x98da8e698d68ec98a40c,0xa42d0c9942d0e98c290e,0x9ace6aac2d0cab82d069,0x68ea9c9a8e69c9b0e49c,0xc69bc2d0e9c96eea9c9,0xea9b968ea9b9b0c69cdb,0x685dacec884290c8656e,0xa7c2d0c84c2f0e85cc10,0x85ab0ea7e7d04a7e7b04,0x9ace69d8290c9dcc106a,0x6cec898290c89c2b0e9d,0xce68956cec8a4370e899,0xe8942b0e8958ae8895a,0xc9ada8e69a829068a02f,0x9f240c69f16ceca002d0,0xf42b0e9f5ace69f56cec,0x2b0eac029069fc2f0e9,0x2906ac96ecaacc2f0eac,0xb048b8cf0e8bc2f0e8bc,0x68c02b0e8c9ace68b8c,0x6a1029068c42f0e8c0c1,0xa116ceaa116aeaa11ace,0xd6ceaa0d6aeaa0db30e,0xdace6af8cd04af82b0ea,0x2b0eaf4cd04af4c106af],#[0x8c69e8290c9e42b0eb0c,0xc8ac2d0c9ec290c9e9a,0xc8b56eca8b1a8c68b029,0xa05ab0e8aa430a8a82d0,0xd02b0e8e82d0ca08290c,0x42b0e8f5b6e48edb2e48,0x290cad16eea8f16aea8d,0xecaadc2d0cad96ecaad4,0x49d089069048f049056,0x49d1ad049d1ab049d1a9,0xf496ecaa196ecaa15af0,0x6c3d0ef5df8e6f5c3d0e,0x83d0ef842d06f743d06f,0x2f0ef143d06fa1d6e8f8,0x70ef2cc107014c107010,0xefcc2906f358aecf383,0xf02c3906fd9d2e8fd03b,0x30e90afc429070283b0,0x102d072fda8e72f88907,0xc29073242d0731d6eed3,0x6eec2c9b8e62be54a62b,0xb0c2b8290e2cd6eea2cd,0x62d82b0c2d1b8e62d42,0x63102d0e2e42d0e30829,0x2f4d10e3068ee43042d0,0xf8d50e308d10e2f4d106,0x654a630cd1062fa54a62,0xd3042ecd50e2e4d3042e,0x304310d1062fcd3042f0,0xa63142b0c2e0d506310d,0xec09a8e6c0829063156c,0xc182d0cc0c2d0ec08290],#[0x602d06c1168ecc202d0c,0xc2d0cc7c2d0cc65ace6c,0xace6c982d0cca58cecc9,0xf0ec982b0ec98ab08c99,0xc6c44350ec3c8d0cc3c2,0x6cc88d0ccb56ee8c4240,0xcc48d0ccc23ec8cbe40c,0x988b08cb8890ccc63ec8,0xc330ebb5acecbac290cb,0x7d04c867b04c842d0cb8,0xcecbc246a8c8642a8c86,0xebbdace6bbc3f0ebc18,0x8c35a8e6c302f0ebbc2b,0xc50290cc4c2d0cc358ec,0x482b0ec49ace6c498cec,0x2f0ecac2b0ecac2f0ec,0xace6bd0cb04bd18ec8cb,0xce6cd8cd04cd82906bd5,0xecd4cd04cd48d0cce5a,0x8bc9a8c6bc82906cdc2b,0xc566308bc42d0cbcd8ec,0x5c290cc598ec8c58290c,0x1b2e4bdc8d0cbf82d0cc,0x8ae8be08b02bf9b6e4bf,0x8e70d42906ce98ee8bf5,0xf0e1a8e70e8350f0d5d,0x716c29070fc2d070f829,0x164c1071602f0f0b0290,0xc96aed0cc3f0f0c4c107,0x96aed178330f12429070,0x290712c2907174330f17,0xeed375a8e73702d0711c],#[0xa938429073842d073816,0x701ace66fcdb006fd6a,0x810db007058ae8700db0,0x9c2f0e6bdace66bdace6,0xdace67cdace66d9ace67,0xc1066c8290c6cc2f0e7c,0x5087a663087a42f0e6c8,0xa86e1e2a86ec290c6ea6,0xc6e6430a6e1aae86e242,0x7dc8d0c7e42b0e6f16ce,0x24c5067243f0873c290c,0xcc506728c50675d8ae87,0xcd0472cd30272dc2e072,0xb0a72cad0872cab0872c,0x873ca90873c8d0a72c8,0x74c8f0a73c890a73caf,0x748c106738c506721c6e,0x582d0e7482b0e748c506,0xcd047302d0e7582b0e7,0x8b0a7518ee87518ae873,0xaea734cd047348d0a750,0xc6f42b0e7f96eea7556,0xa8082d067f02d0c78029,0x795ab007942d067716ec,0x99ad08795a908795af00,0x82d0f29429068442d067,0x2b0f2b0ab092b02d0f29,0xf0f2896ced285daa928c,0xeb4503032902f0f2b42,0xeb118ae8b11ace6b102b,0xb4c2b0eb482906b142b0,0x282906b5c2b0eb582906],#[0x82906b642b0eb502906b,0x2b0eb342b0eb308f08b1,0xd0f334ab093342d06b40,0x73482d0f33da8e73402,0xd24c507350ab0934c29,0xd18330ed248d0cd250b0,0x1cdb00d1d0b00d14db00,0xe7b04cec290ccf5ace6d,0x2b0ecf8370ecf242a8ce,0x506da0f506d9c290cd98,0xed056cecd04290cd00c,0xecfc2b0ecfdace6cfc33,0xd882d0cd75a8e6d702f0,0xac2f0ed842b0ed85b4e6,0x330eda56cecda4290cd,0x330edb16cecdb0eb08db,0xf0eda82b0eda9ace6da8,0x6dc03506d7c2d06db42,0xcdbddce6dbc330edb831,0xdc56cecdcc370edbd6ce,0xec2906d35ace6d303106,0xc290cd082906df02906d,0xc506d64f506d626508d8,0xd04d40cb04d41c2e0d40,0x8d4cad08d40ab08d40c,0x4d45c6e0d54af08d4ca9,0xd5d8ae8d49b6e4d59b2e,0x9da8e73a02d0f3918ee8,0x29073a4330938c2d0f3,0x8ae81bcdb001bcdf001b,0xaea1c0db001c08d0a1bd,0xa18c8b0a19d8ee819d6],#[0x72c42f0c16c2d0e1988b,0x2a849072cc49072c8490,0xa18d002a18b002a02d06,0xcc5062b029062ad8b0a2,0xdf010682b0eb7caf08b6,0xd07065a8e7061ace706c,0x50716aed0402f0d0442,0x93602f0d3542b0d04ccb,0x3396aa831cc507364ab0,0x35a8e63302d0e3202d06,0xc890632d6aa83288b083,0x6d003196b003182d0633,0x506348c5063456b08319,0xe71908b0d1802906e10c,0xd17c8d0718c8b09189ac,0x3b48b0b3accb051942f0,0x818ae90818ae907cc507,0xc2b0f0882f0f080890b0,0x6aa83542f0f0ac2f0f09,0x906e14290636033031a5,0x71a82906e282906e182,0x73c0ab091b029071ac29,0x3cc29073c829073c42d0,0x4a96c4448c5073d08b0b,0xce50645e76c844a80c64,0x61063c8610650276c854,0xac8e64e106e325aa8e34,0xe6085cac8f051302675c,0x608a18e60692d0608618,0x721ee8070650e0892d0,0x8e72c807ce30c06e18ea,0xe72c8118e30c08e72c80],#[0xcac805df2a805e190605,0x30c1e52b032686302115,0xe96a06e8968e30c214e,0x8a98650698218e697865,0xaa680c6aa0e50ca9a02e,0x111b0890d1b08908e506,0xdc8ec91218e691280c69,0x2d06a592d06a5680c6a1,0x50ca653b02a64e50ca59,0xec98630649613b02a6ce,0x6ab51106ab1150699dc8,0x9b618e69b626e49b4610,0xcc65069cc650e9b5f0ea,0x4e106aea19049c225069,0xccec88d430088e02e886,0x2ea87a04ea868630e88d,0x685dccec84a5aca84a0,0xe875ccec874670e85d29,0x89df4a689e80caa7c630,0x9c8c68c5f0a69f9c8c6,0x863029edcccab09c8cab,0x6302a0a85048aa83048a,0x5069d46302ad86106ad4,0xe6f4c6106a1619049d06,0x4f792d06ff92d06ff618,0xf31110701d1506f9a306,0xc86302fc9f4a6f320486,0x630303c6302fdd1b02f,0x650730a18e7304650f30,0x30c2b69c862be98862bc,0xc82ba5ac82ca18e62c4e,0x630e9c862fa98862f9ca],#[0xc4e5ea8c0a9c8630e988,0xd28504bc68304bc5c8c6,0xa5ac90d684c70e4e30d0,0x84c7140e30d1329ac914,0x8e736dcac91525ac9136,0xa936a5aa937272c936e1,0x67125aa937dcac9369f2,0x815cec88261ce671280c,0xa0e50681ce506815cce6,0x1c8c67d061067a1c8c67,0x80ca7a5ccec6c461067d,0xeca73e85006e283006e2,0x734e300759ceea73dc,0x67ec61066f4e300768e3,0x82dc8ca83c6106804610,0xe11506d2658c6d24e506,0xce50cd2df0c6dc11506d,0xe70817dcee817ce506d3,0xcca1b4e70c1ace30c178,0x12d1caca1c5cac81a1c,0xe438e301185c8e632467,0x4da34ec4dac8c84d9cd0,0xe145064d545064dd450c,0x233084e235064e231064,0x830452dcb0e52637084e,0x50c4493b0244a850452e,0xc845a18e6458650e448e,0xe451c8e645c650e45a76,0x54e96c454d3b0254dcd0,0x5e76c8558e50c54e80c6,0xdcb0e550e50655dcce65,0x650e48218e6482be6447],#[0xaa8499cb0e571c8e6484,0x8366bf0a48e2ee849ab,0x654696c8532850836683,0x534630e544e50c5452d0,0x35130a53602e85352d06,0x1ccec548e700538e50c5,0xe70853ce70053c610c54,0x8ec46a18e6469cb0e374,0x846a9504468610e469c,0x46dcd0e46a750846a73,0x46e2b0246e350046e330,0x70650c46dcd0c46dcb0c,0x5cb0e4e693044e465064,0x5f0a391cb0e566730856,0xb0a575cae84fdcb0e392,0xc83ce1ce63cdcb0e5765,0x43c0630e3cce10c3ce76,0x3d0e3083c1cae83c2930,0x15cb084a9cd0e4a5cec8,0xe76c859e70c859dcb0e5,0xe308590e50c59ce10c59,0x3085a2950459ce506594,0x43868304384e5065a4e,0xc4f8e10c4f53f024f685,0x3d8e50c4211b0e4f0e50,0x1ce30e404e70e3ee72e8,0xa5aea3dce50c42672e84,0xcae83e0e50c428e30e40,0xae83f5c8e83f4e3083e1,0x83f5cee83f5cce83f5c,0x840dceea3f5caea3f4e7,0x420e30840dcee840dcae],#[0xd4e308421cce8421cae8,0x8e30e41a5aea418e30e3,0xe7083fce30e41281063f,0xb044cdcb044bce308428,0xce592d06e59cf0ee2dc,0xee568106e54630ee58e3,0xe39cb0ce423300e41cf0,0x44e106e61cac8e39f2a8,0xe506e49c8e6e48e106e,0xcb04e4ce506e51c8e6e5,0x50e029cb0c019cd04e4d,0x6035cb0802dcee802ce,0xe60276c8600e50603ce1,0x69c650e619cb0e690650,0xe730860e76c8681cb0e,0x673086946106615cb0e6,0xcee86265ea8625cb0e69,0x2a862a2504629c8ec629,0x6639cd0c629f6a8629f,0x662dc90662c650663d15,0x6adcb0e6a25b0a6a1cd0,0x4ce3085b276c85ace308,0x13106645cd0664dc9066,0x370e64294ec642d4e664,0x10664d350664e24ec649,0x664e210664e950664e9,0x85c5cd06669c90666a25,0x5d65aea5ca72e85f272e,0xd4e7085d5cee85d5cae8,0x5cae85f5ceea5d5caea5,0xe3025ece30e5c0e3085f,0x7025d8e30e5ee5eea5ec],#[0x25d0e3025f8e30e5e4e,0x25fce7085dce7025dce3,0xef061066a4e3085fce30,0xf5cf0eeedc90eeece30c,0x1cb0ceadcd06ef5c906e,0xe106ebce106efe5aa8f0,0x708e6dcaece68e506ec0,0xae71cf08e71cb08e70e,0x2e7dcb02e7dcf0ae71cb,0xee1cac8e91f2a8e91cf0,0xce302ee8e302ee4e702,0x4e506ec9c8e6ec86106f,0xcd08ecdcb02ec4e302ec,0xee91d9cb0d1c5cb0d1bd,0xd1cdf2a91ce23051cdc,0xc06618e606465071ddcb,0x84650e064e30c065cee,0x69ceec068e30c085ceec,0xe30c089ceec088e30c0,0x18e807282c8072db0007,0xb080721ea807218a8072,0x7dceec06e1d080721,0xc07dceec07d290607d47,0x94650e08dceec08ce70,0x80650e094e30c095ceec,0xe50e080e10e081c90e0,0xe30c075ceec075cf0e08,0xeec078e30c099ceec098,0x20a1ceec09ce30c079c,0x80a1c9080a0e3080a29f,0xa1cf080a1cd080a1cb0,0xa1cd0a0a1cb0a0a1c90a]]
def p2 := limbs80 #[#[0x929061194700119cf0a0,0x7704125cf0e11ce70c11,0xb040bdcf0412dcb0412e,0x204dcac814a1d040be1,0x2135cf0c0f9cf0204dcb,0x5dcf02141cb02142770,0x55cf02061cb02061cf0c,0xc63020c9cf02159cac81,0xcee40f06302165cf0c15,0x3020f4e3020ece3040f1,0x52421d0523e1b0523ce,0xf2252d072121d052421b,0x218650f22a86ed220650,0x15ceed230e50f22e76e9,0xce309239ceed235ceed2,0xc8ed245150f24e5eed24,0xeed251c8ed251ceed245,0xd20dcf0d261caed261c,0x3265f6a926c6303255cf,0x2806303275cf0d2712f0,0xf6c0e61f685052828305,0x618e61e684c61e5190e1,0x84c61f8650e1e5ceec1e,0x10e20280e6201ceec1fa,0xa20286ea20280ea200e,0x81ea810e202870a20281,0x1e9ceec1ea5aca1ea06e,0x91d06209cb0c1ea0708,0xdceec1ee730c20a00ea2,0xe506211ceec20ce30c1e,0x90a211cd06211c906210,0xa211cd0a211cb0a211c],#[0xa280610e27d3f0227dcf,0x2911b0828d2d0628e96e,0x1626e42151b082912d06,0x5ceec21606e821618e62,0xceec23206e8230650e21,0xb0c21c6506239ccc6239,0x81d9cf0c1d607081d5c,0x2241ccc6249cf0c1da07,0x1de07081ddcb0c240630,0x78e50c96a8304279cf0c,0x9c8c6981c8e697e06e89,0x5ecaaa202e8aa25ecaa9,0x50c909ceec909c8ec90a,0xc90dc8ec90dc8ec92ce,0xe934e50c935c8ec934e5,0x93218e693280c6930650,0x111b089113504911c8ec,0x5c8ec938650e910e50c9,0xc8ec91618e6915350491,0x50e914610e915ccec915,0xe6916950491693049146,0xe915cb0e914e10e91680,0x91d1b0891ce50e915cd0,0x1ce50c91dceec91dc8ec,0xdcb0c91e050891e03089,0x650c93c650c91dcd0c91,0x50e945c8ec945c8ec928,0xec949c8ec919c8ec94c6,0xc921c8ec921ccec949c8,0x924e506925c8ec950e50,0x25cd06925c9069246506,0x5cb0a925c90a925cb089],#[0x6506941cf0a925cd0a92,0x50ca1d1b08a1ce506954,0x4a21cceca221ce6a20e,0xca24650ca29cb0ea2293,0xa606506a2dcceca31cce,0x34650ea561ceca6218ec,0x4e50ca351b08a352d06a,0x610ea4d3f02a4c650ea3,0x2e4a38650ea64650ea58,0xea39cceca392d06a3a2,0xca6dc8eca6e24e4a6c65,0xa413b02a40650ea6dcce,0x74650ca5c610ca511b08,0x1cceca3c650ea692d06a,0x1b08a453b02a45cceca7,0xb02a493b02a492d06a79,0xc695ce50c95a36649622,0xc98618e698626e498680,0x998650e984e50c985cee,0xa258c699dceec999c8ec,0x6050899465069a1c8c69,0x80c6abce50caa9cd0c99,0xb0aaadc8c6ab658c6ab2,0xc9b5f6ea9b5cb0eaae5,0xa9c618e69c680c69c4e5,0x9c8e50c9c5f6ea9c5f0e,0xc1c8c69cce5069c9c8e6,0x21f049c21d049c21b049,0x80c6aec650eae0e50cae,0xb02ae4e506af0e50caee,0xec8611f0886202e88629,0xc865caec86604e8865cc],#[0x864e70c864e10c865cce,0x85cf0c864610c865c90c,0x9ccec889ccec8521cec8,0xccec855ccec858630e88,0x4ec87a04ec86a5eca88d,0x885dccec85d1d0c87a0,0xc86dccec8925eca874e7,0x84c630284dccec87dcce,0x827708871ccec870650c,0x1cb02881cb0088063028,0xc90a881cb08881cf0288,0xf0a881cd0a881cb0a881,0x4a7ed304a7d2b02a7dc,0x8a7e8302a7e84caa7ed5,0xa912d06a914300a9286a,0x85c8eca825acaa825eca,0x8e708a85cceca852906a,0xc8eca8a5ecaa892d06a8,0x3029646302a8dcceca95,0xc9dc61069ddc8c69dc6,0xc89c610689dcb0e9d9c9,0x9adc8c69b1cb0e895c90,0xf9cd0c9ae05089ac6302,0x5cb0eac1c8c6ac5c8c69,0x33048b9ceca8c461068c,0x3048b9ccec8ba1ce68b9,0x6a1065068cce1068c29,0xab01c8c6b01cb0ea0e95,0xafa1ce6af93504af9cec,0xfa9504afa9304af8e302,0xe0508b086302b0a84e6a,0xe506b04e70eafce106af],#[0x506b0dcea8b08e30eb04,0xc8ae83049e283029e0e,0xa8de83028a863028b5c9,0x8e1c8ca8e0e50c8d1cec,0xedceca8e1ccca8e1caca,0x8e3048e8e7048d863028,0xcee48ddcae48dce30e8e,0xeea8ddcaea8dce7048dd,0x28d0e3048f9cae48f9c,0xa8e1c8ea8e0e7028e0e3,0x8edceea8e1ccea8e1cae,0xf4e3028fce30e8ece302,0x4e30e8f4e3048f4e3028,0xe7028e4e3048d4e3028d,0x304900e302900e7048e4,0x49d1c90cad06106ad0e,0x49d21f049d21d049d21b,0xf4606e8f45cd049d1cb0,0x48650ef611b08f61ceec,0xec0e6f5e18e6f5d1d0ef,0x3504f4d1d0ef5d190ef5,0x6e8f5200e8f50650ef4d,0x8f51cac8f51ceecf520,0x8f65cb0cf520708f5201,0xf58e106f58650ef69cac,0x6e06eaf551d06f54e10e,0x200eaf6d1d06f6ecb00f,0x82c8ffce506f75ceecf7,0x50efe12d06fe0650eff6,0x8ff8610efed3f02fec6,0x90013b03000650eff91b,0xff13b02fe4650f0011b0],#[0x51b090092d07009cac8,0xd2d0700d3b02fe8650f0,0x26e4f823664f791b0900,0xeecf8206e8f8218e6f82,0xecf9606e8f94650ef81c,0x6f9dccc6f9e0086f9dce,0x21cb0cf8e0108f8c650,0xb1c8e6fb061070220487,0x9cb08fadcb04face106f,0xcac8f19caecf191f08f1,0xf0cf1a0708f1a0108f19,0xf28630ef251b08f25c,0xcf1c630ef2a5acaf2943,0x1943010191b08f21cae,0x1281070125acb0192d07,0x6106fc06302f7dc90f0,0x86faa0708f306106f3,0xb0cfa46302fa5ccc6faa,0xc6fd5f0a6fd60086fd5c,0x2fc5cb08fb60487025cc,0x346302f420708f3d1f0,0xb8e304fb861070386107,0x1cd04fbdcb04fbdcb02f,0x18e72ee06e930606e930,0x50f2ece30d2ed1b092ee,0x92f0e10f2fa80e72f86,0xd2f203092f1ceed2f11b,0x2fce30d2f5ceed2f5cb0,0x2c610f3293f03328e507,0xe26e530d2d073312d073,0x650f30dceed30e18e730,0xf0d2e06507319ceed314],#[0xd2e86303321cf0d2e5c,0x62c4650e2b5ceec2b5cf,0x2b8e70c2c5ceec2c684c,0x4e1062c1cb0c2b9f70a,0x4e1062f5c8e62f5cee83,0xcb042edcee82ece50e2e,0xee8304e506311cb082ed,0x42ee9b042ee98e62f69,0x82ee9b082ee9ee82ee9f,0xc169ec8c1dcb0c2e29f0,0x8e10cc15c8ecc1676c8,0xa80e6c0a9504c0a9304c,0xcb0ec08e10ec08e308c0,0x8ecc0ce50ec09cd0ec09,0xc8c19cec8c0df6a8c0dc,0xcc28e10ec2676e8c25ce,0xc10e308c10e506c11c8e,0x11cb08c11cd06c11c906,0xa76c8c6a9ec8c71cf08c,0xe308c629304c60e10cc6,0xec8c6dcec8c65cb0ec60,0xc8c7a76c8c7686c8c81c,0xcc2e80c6c2dcec8c7dce,0xc9dcceccaa80c6ca9c8e,0x9a7308c99c8c6ca270c6,0x5f6e8c3e5ec8c3dcb0ec,0x5b04c41f6e8c465ec8c4,0xec8cca5ec8cb65d04c42,0x4cb91106cbe58c6cbe5,0x8cba5b08cba5f04cba5b,0xb95f2eab94e106cd25f0,0x9286c8badcec8b99ccec],#[0x276c8bb1ccecb9276c8b,0x630ebb0e50cbb1ccecbb,0xcecb89150cbb5f4ecbb4,0xe8bb9ccecbb9c8ecbb9c,0xebb8e30ebba74e8bba72,0xba5ccecb9df4eab9ce70,0xa8e708ba1ccecba5f2ea,0x5cec8c8dcf08ba9c908b,0x86c8c8680c8c86aea8c8,0x508c868308c868302c86,0xcc91f0ecc911302c928,0xcc95c8ecc95c8ecc8915,0xc31c8c6c39cb0ebbdcce,0xd1cb0ecadcb0ec49cd0e,0xa9304cd9cec8bda9304b,0xf6a8ce25ea8cda9504cd,0xb08ce1cec8ce1c8c8ce1,0xc8be9f6a8be9cd08ce1c,0x4be5cec8bf1cec8be9c8,0xbe4e704be5cee4be5cae,0xfdcee8be5cae8be65ea8,0xe5ea8bfce304bfdcae4b,0xcae8bdce302bddcae8bf,0xea8bea5aa8be8e702be9,0xe8be9cae8be9c8e8bea5,0x2bf25f0abe9cee8be9cc,0xbf1cae8bf25aa8bf0e30,0xe302c00e30ebf1cee8,0x1cce8c01cae8c025ea8c,0xe704bece702bece304be,0x304c04e302c04e304bf4,0xf0d29ac90f1f106ccce],#[0xb0ea80e70e8e70d0e465,0xd9f0eb0d8e10f0ea58e,0xe1cac90edcac90d9ceed,0x1c90f0e258eb0e0e1070,0xcf0f0e0e50f0e0e10f0e,0x5070ddceed0f5f0eb0f5,0xd140e3090f8e5070f91,0x713dcac9145cac9138e7,0x159cf0f13dc90f13ce10,0x4dcac9154e30d15e82c9,0x5ceed101cf0f14dc90f1,0xe10710dcaed171ccc710,0x30d0c282c90bdcac90b4,0xe90b272e90b0630f0c0e,0xf0b0e30f0b1c90f0b274,0x169caed0b8e70f0b1cf0,0x61c90f1628107161cac9,0x1ccc7129ccc7109cf0f1,0xe30511dcee511dcb0911,0x50711dc8e711ce50511c,0xe7115cee5114e303114e,0x7120e303120e507115c8,0x118e303118e507121c8e,0x19cb03118e505118e305,0x8e70d36dcd05119cb051,0x5ac9379cb0d369f30b36,0x50c6f9cee937df6e937a,0xca714670e710e50c710e,0x86fea3006fce50c71658,0x709c8ca71dc8c871dcae,0x18e10c70a58ca7094700,0xc610670ce506700e50c7],#[0x80c6818e506705c8ca70,0x50c818e10c81a02e881a,0x810e50c820670e818e,0x881284e6812a500812a3,0x8262b02824e308811cae,0x2aa50082863088262504,0x4e30880dcae880ce5068,0x99007fdcb08825cd0482,0xf007fe9d007fe9b007fe,0xc66c0e3006b93f008029,0x66ddc8c66dc61066c1c8,0x6d4630e6c4610c6cc610,0xd1cd006d1c9006d1ccec,0x1cd0a6d1cb0a6d1c90a6,0x1b087ad3b027adcf0a6d,0x3087a686c87a4610c7bd,0x7a683007a6c5087a6c,0x67ba83087a686a87a685,0x7c4e50c7c12d067c1290,0xc8650e7a9c8ec7a92d06,0x51b087b51b087b1ccec7,0x63087b603087b61d067b,0x10c7da85086e283086e0,0xc7ddccec7ea58ca7e86,0x672c63087e113087d461,0x7392d06760e50c72d2d0,0x38e10c73a58ca7392906,0x8e50c7492d06748610e7,0x72e8724e300724650e74,0x2e875e850675ce30075e,0xc7312d0673274e875e7,0x6765c8ca740650e730e5],#[0x728e308728e3007292d0,0x3ce30872dcce872e5aea,0xdcee873dcae873e81067,0xe70873e770873e710873,0xf0a73e590a73dcaea73c,0x874dcce874dc8e874e5,0xe74dccea74dc8ea74ce3,0x720e308761cae8760e30,0x48e700738e30e720e300,0xe30e75a5eea758e3007,0xc8ea740e700740e30073,0xaea750e300751ccea741,0x764e30e751ceea751c,0x8744e700744e308734e3,0x7f8e7007f4e308768e70,0x80650c78c650678ce300,0x1f0ca782250478223047,0x650c781cd0c781cb0c78,0x50677dc8ec78a58ca788,0x67f0610c7ec65067851,0x67f1cd007f1c9007f065,0x76c610676dcd067f1c90,0x391b08831cb00791ceca,0xd1b088351b0884061068,0xcb0083e5aea82e250483,0xb0079461067786106775,0x1201cb091f9cd08795c,0x71f4e7011fce7011ed3f,0x2b9cb0d1f223051f0650,0x9d2b012ad2f012aa1b09,0xce7012a4e3012a0e7012,0x1b092be1d012be1b012b],#[0xd012c21b012c21d092be,0xe6b221d092c21b092c21,0x8b54e700b55f2eab221c,0xb61cb0eb59cb0eb10e70,0x3dcb00b3dcaeab2ce106,0x680e7340e50f335cb04b,0xcb05338e507345c8e734,0x4e6d24e50cd2290c4d21,0xe6d28e506d19cce6d19f,0xcdde90c4ddea300d1dcc,0xdd2a300dd8e506dd4e50,0xde5aa8dddcae8dd25aa8,0xe8300cedcae8dde5ea8d,0x8508cee8308cee8500ce,0xb0ecf8e300cf91700cf2,0xd9696c8d90610cd99c,0xda1ccecda11300d9d17,0xd01cb0eda28506da0e30,0x85cd0ed71cb0ecfdc8c6,0x9ccecda9c8c6dadcb0ed,0xcd06db5c906db5cb0eda,0xec8dbd150cdb9f4ecdb9,0xc6d351506dcdf6c8dca5,0x4d30e300d30630ed2dc8,0xde8e50cde5cec8d3a930,0xce300de4e506df4e300,0xe8304d8dcf04d0dc904d,0x74e8d665b04d128504d8,0x8e4d4dcce4d41cae4d42,0xe4d4dcce4d4dcae4d4dc,0x8d4e5aa8d4e8106d4dce,0xd4e7708d4e7108d4e5ea],#[0x55cae4d55c8e4d565f0a,0x8e30ed55cee4d55cce4d,0x5ea8d69cce4d69cae4d6,0x700d51cae8d44e300d46,0xe8d525ea8d525aa8d50e,0x8d51cce8d51cae8d51c8,0xd5a5aa8d58e300d59cee,0x6ce300d6dcee8d59cae8,0x9cce8d6dcae8d6e5ea8d,0xf304d80e300d5ce300d4,0x106df9cce6df9f504d81,0xe00e506dfdcce6dfce,0x9391cd04e01cb04e01cb,0x399c8e7399cee93a1cee,0x89cb09395cb05394e107,0x206e8179cb0d389f30b3,0x630818a5eea18676e818,0x7081b9caea1bdcae81b0,0x1a4e30019c63081a06,0x81a0e30818dc8e818c63,0x198e700194e3081a1cee,0xcce3001a4e300190e300,0x5cf0c16c67081d12f001,0xe3001a86700170630c17,0x9072c4e7012d467081c8,0xd2ce19072ce19072ca1,0x22a619072d867012ddc9,0xb6df2a8b69cb042a5cb0,0x7a7708b6ce702b6dcae2,0xe700b70e302b79cae2b,0xe702b74e302b7dcaeab7,0x107051cb00b806106b84],#[0xc7064e107069cce7068e,0x7055c8e70546507065cc,0x58e507065c8e7064e50,0x5dcb09059cd01059cb01,0x1cb03358e301074e1070,0xcb0431dcb0231ce30336,0x5063265ca6325cb0831d,0xa6338e3083265aa8324e,0xe320e506339c8e633a5c,0x334e10e33280e6330e50,0x29cee832a5aa832a5ee8,0x9cd00329cb00328e3083,0xe50633e5ee832dcb0832,0x300e0a5f0ae04e300e0c,0x93a9cb033a8e30119ce,0x3088e703081cac5085cb,0xa8e7030a1cac50a4e30,0x4e5aa834e1907098e303,0xdf7011a25ee8350e3083,0xe304358e50635dc8e635,0xae4e1dcb04359cb02358,0x2e24e702e20e704e1dc,0x73b9c8e73b8e3031b0e3,0x3bce5073c1c8e73c0e50,0xbdcb053bdcd013bdcb01,0x184012c00b80001cb093,0x4b4041c039402fc02400,0x77406cc064405d4054c0,0x94808d80880082407cc0,0xb000ab00a4409f809a80,0xd540cf00c700bcc0b6c0,0xf080ec40e800e280db80],#[0x8c104810040fb00f6c0,0x1f011ac1168112410d01,0x374132012cc128012341,0x59c153414a4142c13d41,0x75c16f01694164c15f41,0x970191018a8184817e81,0xb481ae81a8c1a4019d01,0xd501ce41c941c281bb81,0x301f741edc1e1c1dbc1,0x22021c0215c20fc20982,0x3d42380232c22d8228c2,0x66425e8256c24b824702,0x8e028882808276826d82,0xb042aa42a4c29b029582,0xd582cf42ca02c302b942,0x382fac2ed02e382de02,0x300325831b83144309c3,0x56834fc3460341033883,0x8fc383c378036dc35fc3,0xb083ab83a3039e039903,0xe443d703ca43c483b9c3,0x9c40103fb03f503eb83,0x2f0425c41f8419441144,0x56c44e04468440443744,0x820476c46f8468045fc4,0xa7c49f849a8491848a44,0xd3c4c6c4c144b904afc4,0xf544ed04e684e044da04,0x2d05248519850c050484,0x53454ac544853a453445,0x7d0570c5698563455a05,0xb085a7859b458fc58785],#[0xe205d7c5cd45c3c5bb85,0xb860085f6c5f0c5e785,0x36062c8623061a061446,0x580650464ac644063f46,0x86467a0671c66b865f46,0xb246a9c6a04698868f46,0xd5c6d106ca46c186ba86,0x146f986f0c6e606df06,0x2c8726471b8712470c07,0x43473ec73a8735473107,0x724765c760875b074d47,0xa08799478fc784c77e87,0xce87c387bac7b2c7a947,0xfc87f307e987df07d487,0x28081f8818880f0805c7,0x508848c8418837082e48,0x86887b88710869085d88,0xbb08aec8a60896c88f08,0xeb08e588dc48d648c7c8,0x1e8915c908c8ff88f508,0x42c93d4935492bc92589,0x65095e4957894e894889,0x94c98989824977c96e09,0xb749b109ab09a4c99dc9,0xe1c9d389ca09c3c9bd89,0xbca0309f849f149e849,0x3dca334a2b4a210a15ca,0x5f8a594a53ca4d4a44ca,0x880a7e4a778a718a690a,0xbe4ab68aa88a9f0a950a,0xe70adecad60acb0ac54a,0x15cb0d0affcaf90aebca]]
def p3 := limbs80 #[#[0x3c0b330b29cb23cb1dcb,0x64cb5b0b514b494b448b,0x924b894b7f8b778b6c8b,0xbecbb4cbab0ba40b9b8b,0xeb0be38bd9cbd0cbc80b,0x110c090bffcbf84bf10b,0x408c370c2ecc220c1a8c,0x6e0c670c608c524c4b0c,0x9e4c938c890c80cc780c,0xc48cbf8cb58cac8ca80c,0xef4ce64cdd8cd48cca4c,0x180d0d4d064cfe8cf74c,0x48cd41cd34cd288d1dcd,0x74cd6b4d620d5a0d50cd,0x9e4d938d8b4d838d7a4d,0xcecdc6cdbecdb2cda80d,0xfc8df04de74ddd8dd5cd,0x2bce200e160e0cce058d,0x55ce4cce41ce3b4e34ce,0x800e78ce6cce658e5ece,0xb24ea70e9b0e8ece858e,0xe24ed98ed18ec88ebd8e,0x1a4f0d0f01cef4cef00e,0x548f480f3b8f304f250f,0x7fcf76cf6a4f660f5d8f,0xac4fa18f98cf908f85cf,0xd88fcfcfc74fbb8fb48f,0x1090040ff70fee4fe38f,0x44d03bd0321027501dd0,0x6e9062905b9050504990,0x9f1099508dd084507810,0xc910c010b7d0af90a4d0],#[0xf350e7d0ded0d710d050,0x211119910f5106d0fd50,0x55514cd143d139512c91,0x7e1177516ed165515c51,0xaf11a6119ad194118711,0xde51d351cb91c051b991,0x7d20091fb11f291e891,0x32922cd226121f521192,0x67525a92509245123952,0x8cd285127ed275d26e92,0xb7d2ac92a7129c529512,0xe292d992d352cc12c152,0x195310530612f792edd2,0x47d33f53329328d31fd3,0x79136ed35f9357d34f93,0xa4139c9391d388538113,0xd193c7d3bc93b293ab13,0x2d3f613ef53e953d9d3,0x309427941cd415d40d54,0x54144e1447943f9438d4,0x83547ad4731468145c94,0xb354a9149d5493148994,0xe1d4d994cf94c594bd94,0xb150014f994f314ebd4,0x2b1524551ed515d51015,0x5cd553d548553f1533d5,0x8b55811577d56e956455,0xa815a3d59f159ad59455,0xc755c295b8d5b495ac55,0xf615f055e755ddd5d015,0x1a1614960e5604d5fd95,0x4b16421634d62b162256],#[0x8156731666565b5653d6,0xb596a6d69e16949689d6,0xe3d6dad6d2d6cc16c396,0xf57089701d6f756eb96,0x48573b5733d727d71c57,0x75d76a1761975b9754d7,0xa8d79e5794178b178257,0xd817ce17c517bc17b357,0x3d7f797f1d7e957df57,0x3c5831d828d81bd81298,0x6a9864185b18521848d8,0x96588bd8829879d87158,0xc098b958b058a3989fd8,0xecd8e4d8df98d358c5d8,0x195910990498fd18f458,0x41d93a9930d92c192219,0x66195f59591951994919,0x8fd988997f5978196c99,0xc0d9b799ae19a1599919,0xf219e8d9dc99d319cc59,0x1dda131a0c9a0759fd99,0x451a401a37da2b1a259a,0x725a69da5f5a56da4d9a,0xa7da9d1a969a875a7a9a,0xd7dacddac49abb1ab05a,0x31af99af0daea5ae19a,0x2edb279b1e9b171b0d5b,0x5c5b539b481b3e9b371b,0x8c9b815b791b72db699b,0xb3dbac5ba39b9c9b94db,0xe81bde5bd4dbc8dbbedb,0x1edc145c095bfb9bf35b],#[0x485c3b1c361c30dc275c,0x7a1c6edc661c59dc515c,0xab1ca45c9a5c901c851c,0xe51cdc9cd1dcc3dcb81c,0xf9d059cfd1cf55cef9c,0x41dd37dd2e9d265d1a5d,0x709d661d5cdd571d4e1d,0x9ddd94dd8d1d81dd7a5d,0xd5ddc95dc15db25da45d,0xb1e031df71dec1de01d,0x335e2b1e249e1a1e131e,0x5a5e549e4c9e409e3a1e,0x85de7ede761e6b1e641e,0xb95eb21ea65e9a9e8ede,0xe39ed99ed01eca5ec15e,0x129f099f005ef61eec5e,0x3adf341f281f21df1a1f,0x651f5e5f581f4fdf42df,0x9adf931f86df7c1f71df,0xbd1fb75fb21faa9fa49f,0xf01fe89fdf1fd21fc3df,0x1e6015200c60039ff85f,0x45203de03660302025e0,0x75e06e2063e05a604f20,0x9ea0982091208ae080e0,0xc060b860b3e0aea0a960,0xeaa0e320dea0d560c920,0x132109a0fde0f4a0f020,0x3da1376132e129212021,0x7061656159a1532146e1,0xa2e198618f2184e17a61,0xd7a1ce21c4a1bb61ae61],#[0xaa1ffa1f721ece1e1e1,0x396232a228a21da21222,0x6622606256624d224462,0x8d6286227f6277e26ee2,0xbb62b222aa22a1e296e2,0xe622dca2d362ca62c4a2,0xae304a2fda2f2e2ebe2,0x2da326a31f6319231023,0x5d6355634b6343233ae3,0x916385a37a2370636763,0xc223b863b2a3a8a39de3,0xefa3e923e0a3d723cd23,0x1ae4106408a3ffa3f7e3,0x3da43964322429a42624,0x66a45d6457244de444e4,0x8e6484247ca476a46f24,0xb424ab64a5649d6495e4,0xe0e4d964d024c924bd64,0x9e4ffe4f7e4ede4e5a4,0x26a51fa51a2515650ea5,0x4fe5486540a537252f65,0x6ca5676561655d655765,0x93258ea5862580a57465,0xb565af25a9e5a2a59ae5,0xd5e5ce25c8a5c2a5bc65,0xf6e5f0e5eba5e465dce5,0x1ca613660da60725fe65,0x452639a6302625662166,0x682661e65c2654a64ce6,0x8b2683267c6676266c66,0xa626a2e69ce69a2694e6,0xcae6c1e6ba66b326aee6],#[0xebe6e3e6df66d826d3e6,0xf6706a6ffa6f9e6f066,0x39a733672da722e717e7,0x582752e74ae744673ee7,0x78a772e76ee766275ca7,0x9727906788e782277ca7,0xbce7b667ada7a5a79ee7,0xe527dce7d4a7cd27c5a7,0xba804a7fd27f4e7ed67,0x2ce8272820281a6812e8,0x56a84e2843683ba834e8,0x7c6873e86e2867285f28,0x9fa89aa8926889688528,0xca28c3a8bea8b668a9a8,0xeaa8e8a8e0e8d5e8d068,0xf4a8f2a8f0a8eea8eca8,0xfea8fca8faa8f8a8f6a8,0x8a906a904a902a900a8,0x12a910a90ea90ca90aa9,0x1ca91aa918a916a914a9,0x26a924a922a920a91ea9,0x30a92ea92ca92aa928a9,0x3aa938a936a934a932a9,0x44a942a940a93ea93ca9,0x4ea94ca94aa948a946a9,0x58a956a954a952a950a9,0x62a960a95ea95ca95aa9,0x6ca96aa968a966a964a9,0x76a974a972a970a96ea9,0x80a97ea97ca97aa978a9,0x8aa988a986a984a982a9,0x94a992a990a98ea98ca9],#[0x9ea99ca99aa998a996a9,0xa8a9a6a9a4a9a2a9a0a9,0xb2a9b0a9aea9aca9aaa9,0xbca9baa9b8a9b6a9b4a9,0xc6a9c4a9c2a9c0a9bea9,0xd0a9cea9cca9caa9c8a9,0xdaa9d8a9d6a9d4a9d2a9,0xe4a9e2a9e0a9dea9dca9,0xeea9eca9eaa9e8a9e6a9,0xf8a9f6a9f4a9f2a9f0a9,0x2aa00a9fea9fca9faa9,0xcaa0aaa08aa06aa04aa,0x16aa14aa12aa10aa0eaa,0x20aa1eaa1caa1aaa18aa,0x2aaa28aa26aa24aa22aa,0x34aa32aa30aa2eaa2caa,0x3eaa3caa3aaa38aa36aa,0x48aa46aa44aa42aa40aa,0x52aa50aa4eaa4caa4aaa,0x5caa5aaa58aa56aa54aa,0x66aa64aa62aa60aa5eaa,0x70aa6eaa6caa6aaa68aa,0x7aaa78aa76aa74aa72aa,0x84aa82aa80aa7eaa7caa,0x8eaa8caa8aaa88aa86aa,0x98aa96aa94aa92aa90aa,0xa2aaa0aa9eaa9caa9aaa,0xacaaaaaaa8aaa6aaa4aa,0xb6aab4aab2aab0aaaeaa,0xc0aabeaabcaabaaab8aa,0xcaaac8aac6aac4aac2aa,0xd4aad2aad0aaceaaccaa],#[0xdeaadcaadaaad8aad6aa,0xe8aae6aae4aae2aae0aa,0xf2aaf0aaeeaaecaaeaaa,0xfcaafaaaf8aaf6aaf4aa,0x6ab04ab02ab00aafeaa,0x10ab0eab0cab0aab08ab,0x1aab18ab16ab14ab12ab,0x24ab22ab20ab1eab1cab,0x2eab2cab2aab28ab26ab,0x38ab36ab34ab32ab30ab,0x42ab40ab3eab3cab3aab,0x4cab4aab48ab46ab44ab,0x56ab54ab52ab50ab4eab,0x60ab5eab5cab5aab58ab,0x6aab68ab66ab64ab62ab,0x74ab72ab70ab6eab6cab,0x7eab7cab7aab78ab76ab,0x88ab86ab84ab82ab80ab,0x92ab90ab8eab8cab8aab,0x9cab9aab98ab96ab94ab,0xa6aba4aba2aba0ab9eab,0xb0abaeabacabaaaba8ab,0xbaabb8abb6abb4abb2ab,0xc4abc2abc0abbeabbcab,0xceabccabcaabc8abc6ab,0xd8abd6abd4abd2abd0ab,0xe2abe0abdeabdcabdaab,0xecabeaabe8abe6abe4ab,0xf6abf4abf2abf0abeeab,0xabfeabfcabfaabf8ab,0xaac08ac06ac04ac02ac,0x14ac12ac10ac0eac0cac],#[0x1eac1cac1aac18ac16ac,0x28ac26ac24ac22ac20ac,0x32ac30ac2eac2cac2aac,0x3cac3aac38ac36ac34ac,0x46ac44ac42ac40ac3eac,0x50ac4eac4cac4aac48ac,0x5aac58ac56ac54ac52ac,0x64ac62ac60ac5eac5cac,0x6eac6cac6aac68ac66ac,0x78ac76ac74ac72ac70ac,0x82ac80ac7eac7cac7aac,0x8cac8aac88ac86ac84ac,0x96ac94ac92ac90ac8eac,0xa0ac9eac9cac9aac98ac,0xaaaca8aca6aca4aca2ac,0xb4acb2acb0acaeacacac,0xbeacbcacbaacb8acb6ac,0xc8acc6acc4acc2acc0ac,0xd2acd0acceacccaccaac,0xdcacdaacd8acd6acd4ac,0xe6ace4ace2ace0acdeac,0xf0aceeacecaceaace8ac,0xfaacf8acf6acf4acf2ac,0x4ad02ad00acfeacfcac,0xead0cad0aad08ad06ad,0x18ad16ad14ad12ad10ad,0x22ad20ad1ead1cad1aad,0x2cad2aad28ad26ad24ad,0x36ad34ad32ad30ad2ead,0x40ad3ead3cad3aad38ad,0x4aad48ad46ad44ad42ad,0x54ad52ad50ad4ead4cad],#[0x5ead5cad5aad58ad56ad,0x68ad66ad64ad62ad60ad,0x72ad70ad6ead6cad6aad,0x7cad7aad78ad76ad74ad,0x86ad84ad82ad80ad7ead,0x90ad8ead8cad8aad88ad,0x9aad98ad96ad94ad92ad,0xa4ada2ada0ad9ead9cad,0xaeadacadaaada8ada6ad,0xb8adb6adb4adb2adb0ad,0xc2adc0adbeadbcadbaad,0xccadcaadc8adc6adc4ad,0xd6add4add2add0adcead,0xe0addeaddcaddaadd8ad,0xeaade8ade6ade4ade2ad,0xf4adf2adf0adeeadecad,0xfeadfcadfaadf8adf6ad,0x8ae06ae04ae02ae00ad,0x12ae10ae0eae0cae0aae,0x1cae1aae18ae16ae14ae,0x26ae24ae22ae20ae1eae,0x30ae2eae2cae2aae28ae,0x3aae38ae36ae34ae32ae,0x44ae42ae40ae3eae3cae,0x4eae4cae4aae48ae46ae,0x58ae56ae54ae52ae50ae,0x62ae60ae5eae5cae5aae,0x6cae6aae68ae66ae64ae,0x76ae74ae72ae70ae6eae,0x80ae7eae7cae7aae78ae,0x8aae88ae86ae84ae82ae,0x94ae92ae90ae8eae8cae],#[0x9eae9cae9aae98ae96ae,0xa8aea6aea4aea2aea0ae,0xb2aeb0aeaeaeacaeaaae,0xbcaebaaeb8aeb6aeb4ae,0xc6aec4aec2aec0aebeae,0xd0aeceaeccaecaaec8ae,0xdaaed8aed6aed4aed2ae,0xe4aee2aee0aedeaedcae,0xeeaeecaeeaaee8aee6ae,0xf8aef6aef4aef2aef0ae,0x2af00aefeaefcaefaae,0xcaf0aaf08af06af04af,0x16af14af12af10af0eaf,0x20af1eaf1caf1aaf18af,0x2aaf28af26af24af22af,0x34af32af30af2eaf2caf,0x3eaf3caf3aaf38af36af,0x48af46af44af42af40af,0x52af50af4eaf4caf4aaf,0x5caf5aaf58af56af54af,0x66af64af62af60af5eaf,0x70af6eaf6caf6aaf68af,0x7aaf78af76af74af72af,0x84af82af80af7eaf7caf,0x8eaf8caf8aaf88af86af,0x98af96af94af92af90af,0xa2afa0af9eaf9caf9aaf,0xacafaaafa8afa6afa4af,0xb6afb4afb2afb0afaeaf,0xc0afbeafbcafbaafb8af,0xcaafc8afc6afc4afc2af,0xd4afd2afd0afceafccaf],#[0xdeafdcafdaafd8afd6af,0xe8afe6afe4afe2afe0af,0xf2aff0afeeafecafeaaf,0xfcaffaaff8aff6aff4af,0x6b004b002b000affeaf,0x10b00eb00cb00ab008b0,0x1ab018b016b014b012b0,0x24b022b020b01eb01cb0,0x2eb02cb02ab028b026b0,0x38b036b034b032b030b0,0x42b040b03eb03cb03ab0,0x4cb04ab048b046b044b0,0x56b054b052b050b04eb0,0x60b05eb05cb05ab058b0,0x6ab068b066b064b062b0,0x74b072b070b06eb06cb0,0x7eb07cb07ab078b076b0,0x88b086b084b082b080b0,0x92b090b08eb08cb08ab0,0x9cb09ab098b096b094b0,0xa6b0a4b0a2b0a0b09eb0,0xb0b0aeb0acb0aab0a8b0,0xbab0b8b0b6b0b4b0b2b0,0xc4b0c2b0c0b0beb0bcb0,0xceb0ccb0cab0c8b0c6b0,0xd8b0d6b0d4b0d2b0d0b0,0xe2b0e0b0deb0dcb0dab0,0xecb0eab0e8b0e6b0e4b0,0xf6b0f4b0f2b0f0b0eeb0,0xb0feb0fcb0fab0f8b0,0xab108b106b104b102b1,0x14b112b110b10eb10cb1],#[0x1eb11cb11ab118b116b1,0x28b126b124b122b120b1,0x32b130b12eb12cb12ab1,0x3cb13ab138b136b134b1,0x46b144b142b140b13eb1,0x50b14eb14cb14ab148b1,0x5ab158b156b154b152b1,0x64b162b160b15eb15cb1,0x6eb16cb16ab168b166b1,0x78b176b174b172b170b1,0x82b180b17eb17cb17ab1,0x8cb18ab188b186b184b1,0x96b194b192b190b18eb1,0xa0b19eb19cb19ab198b1,0xaab1a8b1a6b1a4b1a2b1,0xb4b1b2b1b0b1aeb1acb1,0xbeb1bcb1bab1b8b1b6b1,0xc8b1c6b1c4b1c2b1c0b1,0xd2b1d0b1ceb1ccb1cab1,0xdcb1dab1d8b1d6b1d4b1,0xe6b1e4b1e2b1e0b1deb1,0xf0b1eeb1ecb1eab1e8b1,0xfab1f8b1f6b1f4b1f2b1,0x4b202b200b1feb1fcb1,0xeb20cb20ab208b206b2,0x18b216b214b212b210b2,0x22b220b21eb21cb21ab2,0x2cb22ab228b226b224b2,0x36b234b232b230b22eb2,0x40b23eb23cb23ab238b2,0x4ab248b246b244b242b2,0x54b252b250b24eb24cb2],#[0x5eb25cb25ab258b256b2,0x68b266b264b262b260b2,0x72b270b26eb26cb26ab2,0x7cb27ab278b276b274b2,0x86b284b282b280b27eb2,0x90b28eb28cb28ab288b2,0x9ab298b296b294b292b2,0xa4b2a2b2a0b29eb29cb2,0xaeb2acb2aab2a8b2a6b2,0xb8b2b6b2b4b2b2b2b0b2,0xc2b2c0b2beb2bcb2bab2,0xccb2cab2c8b2c6b2c4b2,0xd6b2d4b2d2b2d0b2ceb2,0xe0b2deb2dcb2dab2d8b2,0xeab2e8b2e6b2e4b2e2b2,0xf4b2f2b2f0b2eeb2ecb2,0xfeb2fcb2fab2f8b2f6b2,0x8b306b304b302b300b2,0x12b310b30eb30cb30ab3,0x1cb31ab318b316b314b3,0x26b324b322b320b31eb3,0x30b32eb32cb32ab328b3,0x3ab338b336b334b332b3,0x44b342b340b33eb33cb3,0x4eb34cb34ab348b346b3,0x58b356b354b352b350b3,0x62b360b35eb35cb35ab3,0x6cb36ab368b366b364b3,0x76b374b372b370b36eb3,0x80b37eb37cb37ab378b3,0x8ab388b386b384b382b3,0x94b392b390b38eb38cb3],#[0x9eb39cb39ab398b396b3,0xa8b3a6b3a4b3a2b3a0b3,0xb2b3b0b3aeb3acb3aab3,0xbcb3bab3b8b3b6b3b4b3,0xc6b3c4b3c2b3c0b3beb3,0xd0b3ceb3ccb3cab3c8b3,0xdab3d8b3d6b3d4b3d2b3,0xe4b3e2b3e0b3deb3dcb3,0xeeb3ecb3eab3e8b3e6b3,0xf8b3f6b3f4b3f2b3f0b3,0x2b400b3feb3fcb3fab3,0xcb40ab408b406b404b4,0x16b414b412b410b40eb4,0x20b41eb41cb41ab418b4,0x2ab428b426b424b422b4,0x34b432b430b42eb42cb4,0x3eb43cb43ab438b436b4,0x48b446b444b442b440b4,0x52b450b44eb44cb44ab4,0x5cb45ab458b456b454b4,0x66b464b462b460b45eb4,0x70b46eb46cb46ab468b4,0x7ab478b476b474b472b4,0x84b482b480b47eb47cb4,0x8eb48cb48ab488b486b4,0x98b496b494b492b490b4,0xa2b4a0b49eb49cb49ab4,0xacb4aab4a8b4a6b4a4b4,0xb6b4b4b4b2b4b0b4aeb4,0xc0b4beb4bcb4bab4b8b4,0xcab4c8b4c6b4c4b4c2b4,0xd4b4d2b4d0b4ceb4ccb4],#[0xdeb4dcb4dab4d8b4d6b4,0xe8b4e6b4e4b4e2b4e0b4,0xf2b4f0b4eeb4ecb4eab4,0xfcb4fab4f8b4f6b4f4b4,0x6b504b502b500b4feb4,0x10b50eb50cb50ab508b5,0x1ab518b516b514b512b5,0x24b522b520b51eb51cb5,0x4b00050180a03c080575,0xb4100f8101c13d000,0xf04001e0021e0816025c,0x3a0b0208d44068c39101,0x10020c302453124c6094,0xec0e4381c1206f040981,0x34310eb06830830c0908,0x9c16135082511e0e5158,0x6314450742250205f041,0x74248ca10c203a471008,0x791a069004c243c05182,0x32281e70d47b08808248,0x42200b05c8211906052c,0x16008522e8c31c4a44f8,0xe7130123f4313dc2c1d4,0x1610c64150ad101c41c4,0xeb128524e19810994224,0x84084443d4c033836158,0x6c1b424111942e876320,0x383e0a331103051293a8,0xe0370043442120561245,0x17060b934432261261e8,0x620312e815389640c4,0xd212421608387680c385]]
def p4 := limbs80 #[#[0x82691685f1346d1a4028,0x661a8b53602640928430,0xc26115288d851814761,0xa3a5b8797d4a18814060,0xc062436536f9887850a1,0x60f0a2d3dfe70321aed,0x709960cdde61a6b2d99a,0x76c9e5acbdd7a4113367,0xc44cfd87ca6b2865a6b2,0x2b18dd6863d5a1f761e3,0xfc5634f290641ead0c3e,0x608fc9d12f3282e45820,0x28cc8798891e7899391,0xa61958d5f5f1213359ff,0x8c7ab43487e2644c32b1,0x890e446bd524439119c8,0x3c890e44672233911d3c,0x121c88ce44672233911d,0x224ead0e7568674890e9,0x242d35f09083d5a189f5,0x4161ae86a3cba2730efe,0x468b28eb6ab1d4ac40f2,0xf3636acb63c7f214909,0x1b8958f25d18fbaf4636,0x56313d6874c609038959,0x483ce0f4646c36564cae,0xf11915c3241c32412b86,0x8be6764650e9d4ac6d8,0xa9533db2b38b07ed490b,0x5d4ac7a9b28317dd60e3,0x9bdbad11ad958f534b06,0x8f310c798863cc433644],#[0x2042868ed8b9d1cd0242,0x956f084a5314909cedf2,0x68563855b8a4a232dd1b,0x77c43e0fa0265e76e4d0,0x922d19977c438b6fb28d,0xf2d23a425b1aef8865c2,0xbaf75933f86ed5330e96,0x3c24cd65b0bdc1aaed0f,0x799a4f3fcb14281ead0f,0x446f970c8ca5fcf7c117,0x6183213f974ebd0abacc,0xcaa10ca596ac124585cc,0xa40f06c8476d0f5e118f,0x499b06e92d0f5e161760,0x378d508510c97802085d,0x8219eb6ec7044cfaf0f,0x8edfac134e04cf1ffc10,0xa39160b9160b78c8f0c,0xbf8c43047e4582bce715,0x43b707072d3a62400ce,0x3c1800109a49fe02a840,0x33fc8602663c68a1417e,0x39c2e011e1b2d8dad182,0x42c1e6d8b2328e63688c,0x118ff2102853618326a6,0x621c1d6bb257b2eafecc,0x90b205c93292184d684b,0x3a3196cf1248512e18a1,0xbe038e000ce78ccc264f,0x80663c6a214414b85995,0x519b1700654af62ef288,0x3811a7e3a1c08c7f0a54],#[0xf418570010e3d5a18e38,0x642c1db0160f384ec64f,0x44dfe5828a01bcb63a,0xa14cda1a307277c55024,0xfdaa8086e0cbf7e1ea01,0x195e0868f9f372a84051,0x17b830ff0d405332425b,0x41951ec6c1e7f0204cb6,0xcdfc10648e0fb1c7f018,0x3abb842189e0e117a890,0xf7ac0a00ce1d724a6590,0x49a466ef7f244a523477,0x5468417edc8030866f7,0xc3841133169f970cca8f,0x661bad0fbf5e1044cd1f,0x781910b5f8ac6dc87b00,0xb90884c7fe018828687b,0x19b2c8ce02903e2b1a3f,0x8198b0fd0e0668afc288,0x7044c5c20f994176bc28,0x34651b4a8e5e8a242238,0x2853618326ef68fae200,0x3141795be7b889a0f922,0xa90843f9c061945ff844,0x3f508108587e870331ba,0x2084cc3e064ee7d10329,0x40cbcca091bb041c35fc,0xf3e8819b30f81923fdf4,0x461ae26527f4c870881f,0x242c7c898f1faa904143,0x2b1d3f0528428657d498,0x223b39121c88db9044c3],#[0x11345bf902c242b72087,0x3ab431ead0c21d7fe15d,0xf6a01439bb11d858050f,0xd2c1100cedfc56337623,0x64d3a0324f5e20828e9f,0x8c3f06689a38ebc5014,0x24a67d9b81108fb371a,0x471719e8600f363efe9d,0xe2829985951c5c67a1a5,0x1ed967365e78a0a66179,0x6f5b2ea82143db2ce6ca,0xb96a0e7cea6c463c9832,0x7fe4c02a165fe4e5424,0x4c0683e12464f773b0a3,0xf3e776da9b67cffe2904,0x86b65aeef421afe4c149,0xe11b0c20365b034195f0,0x3fd3e2c480484d50e808,0xfd3da149cceef2749212,0x80cd49ffc0088121a23,0x95042f3c841e7fec0044,0xe917f906215f44071797,0xfaf8038c85efcc318019,0xfc24a8512ff154000110,0x8604cb9c3c63eb53b643,0xe0e78a83af14a72337e5,0x64f5bb758850d9b63174,0xcfa860a92c3851396730,0xbf8018850b9e1d90499a,0xdbff11c080483a32a140,0x878c7da876c8b81eaf48,0x2f1db1ca83d10216d8f3],#[0xfc84191e541e8929a183,0x6107eeaf1e830850885f,0x316101b20deb0975223f,0xb4ec4d4215df1868004,0xe1f1c92b050ceffcd185,0x2453ac1a14947c381219,0x1c0ca7556851bf1c76d1,0x484193c104857841f7e8,0x8f92805949be0c2166f7,0x5e74642f7720648d2163,0xa151ffd6b8a2021c5d,0x2269bff0e480a09fd68,0x1934baa8a846fe1f42aa,0x2c5f0c3299f1ba319e4c,0xd88ff0e284e1fe4c50a2,0x155935ff060415090f5e,0xee109d532f46091111f,0x88b82a882f9395098fae,0x3c59a109c338710ab82a,0x1532d7b6207d0436129b,0x69459217fda080a38758,0xe18664a6732bf6109bf7,0x338332288584dea184ef,0x466e928a4b367568a4b3,0x462019c0b80d937c50e4,0x8ab31484fb362090b5a8,0xdeb18ccd7b33010a40f,0x18deef0e080fc0878ccd,0x8d89e543299de549b25d,0x2157f3005157fe2240,0x180821a1fad2609079a5,0xe5632169f2b19089ffc0],#[0xe3510a03e1b430266553,0xa3b8397fc00500003441,0x127f19204920b9cc1931,0x36a17ba5636ca4e9f226,0xa3d3e43415a8687ff02,0x6f2ca48660d5897eb992,0x3476300f624fd1b85666,0x887ca4866bb93a10d52a,0x427a5cd2a42f65cb9565,0x5fb00a34f4cab23392cd,0xb9f3285034369a52518,0x448690797864230d7b43,0xdfff1408854d1d1f8a04,0x7890ade681ec9946e546,0xe8d0d9947af54d14d679,0x1b2d337053e69720a3a7,0x40b1b2bb2c91842f0d1b,0xddaa72447c6de0b2660f,0x517890ecd58e8d8d9e78,0x5edf0c8ed66a308afc17,0xb347353e2308a45788ad,0xc1b3b478a2c332fe28c,0xf45cbfd676460cffecc,0x803079993f4686ccbb03,0xca3cca8fa382c09a1bbf,0x3cce36be224daf88891f,0xa8cabfa5c4a8c1f8a418,0xebcf6508829fe4b5fc69,0x8d3d32ac9e9bd65a0810,0xda246ce6b3d384850d55,0x21b13f87c75099ebfc97,0x87f32280443620d3d130],#[0x5feab624617abc184286,0xd44461373d66875c0284,0x56ad054d8a5fd0566b82,0x1bf71dc06ace9fb3711a,0x176904377fe30e80981a,0x2564337ee3b80d59d9b7,0x1e3cff6d13cc67b7c429,0x4be2ff446b7cd2420122,0xd103033cf90a3da34865,0x5b0384c54c90b491ffe1,0xa45a76165b7e4da5350c,0x22b8bee20d868f1e68ac,0x12de86a628383f6ef8a4,0xe68acb1eb99eb2c3ffa6,0x542186afb69d155678f1,0x1c2b21e0f1446526bd7e,0x8855abfa56321cdc1ea8,0x7f30108f5fa7b8cd0756,0x34138215da8bdad6c36d,0x3839bc87bfae60a8c09,0x8b6564afb69c98833eb0,0xe95285cffb294365676,0x3b0b32aaf0292d861f9e,0x1fa1af93c6f882905f54,0x84975aa0c1b0db0fd0f6,0x930d97d76cc109ebb660,0x1975801c1ddc6e28f21d,0xd2a50ca75f6608fcd8cf,0xa2a3c3c53690c2e3f3c1,0xc3b0b369d48614937eae,0xe2aac4e182cbc0a32f7a,0x89c2801e49b7b1387f6c],#[0x61949035d613484f36ed,0x3db5a5352437903279fb,0x3263f10c9085c31a9033,0x75201295fa331213b8b2,0x4082492e2cb8277ff40c,0x200a19cffc0c8c9d7fc6,0xf788198243df44084fe0,0xbf870400436f5342469f,0xff1184147dff80210a3f,0x47c459e710d1ff9c484d,0x8a00008817d0c7490a2a,0xcf6e641de5ed03c3e68a,0xad564033b5b4e0817b60,0x4a4a597fc61c10a183ff,0x228a2fc9a8800878a4d9,0xf581008eb8f824551f89,0x9344fbd69091a7984883,0xcf92420a4ae072516efe,0x8f3c0fdf48048573e0a7,0x8c7fc52c20a441feb0a4,0xf10fe465b644c1e1e202,0xdfd260913c0f9f280486,0x8923bf3f2f5021e2695d,0x98c1ed0cfac230fc4600,0x7a789890b92eb2e8cb4d,0x1112b2a7fc3c01a2268f,0x4f71ab032933bc0a4ede,0xfa7ba582000089261998,0x4bf6a4d923a645450ce6,0x50dde89aea334c46f11,0x4e249daff1908a78b060,0x99f5897124869ed3824d],#[0x278be8850a3fac492584,0x5b0d0828c0d5bbc75046,0x1a19e44c1e4ba31b7fa,0xeffe308248f9f1f08688,0x240530de40c9dc0f9032,0x16465ad33d20663fff23,0x64173c02841039e881eb,0x66f6d4099720dd8fbb1c,0x3ffad8019bdf07210428,0x31873e104cb987c81910,0x90405237dbee0047a97e,0x1219f1f9a2bc0143aeff,0x4a651f8a5080a4661e38,0x15068577ec6480856d72,0x797a40cd1f11c16577ec,0xd92635b649b03e40c8db,0xd7a10d7f5eaa40920ea,0x25f70487e77124513c61,0xa964cebad8c411f8bd23,0x81435f93abe0a0b49f1,0xe090837d0105484fe2fb,0xf2006642bc7f4023d36,0x5e3fa011f2a1e400cd95,0x285dd8e3277ea18132a1,0xe0213cf90b728454d8b7,0xe4307c555990bb9423fe,0x88824902220f5f87234d,0xacba32a61d6ca0cdeddf,0xcc8370edf8217fa21e4b,0x3c64f4193ef55990aefe,0xffd284259897d4a07b94,0x1f1cc00d116fda0f59a9],#[0xee2329238688219b3f0e,0xa1fc4c80249e23285027,0xa875a49553ad75cf442,0xf50a2fe199c227e36db1,0x991f63c2d204807d3874,0xf74d5c365d03d1332785,0x9aa665d7dd7c92180a88,0x8f6f92164e2e6ca0ebf,0xd20c670fb698c9b5d411,0x4ac9ae1e00e74357c3ed,0x45d97baf440b9b28388d,0xeebd0f8f5b1a4a943d28,0xa0643d35c03094a1117,0x71f08ed6ea63423cdc33,0x3c46a5652ea563173650,0x8880190e56f0fb17b99e,0x783811d1f0fdf4253f92,0xaa0902425f8e3e011e6d,0x1132385ff55a24913fe,0x3e1845966bfa859187c,0x23bd85968e7fd652011e,0x85859c970b32effc0113,0x2800d3cfe186a30087dd,0xfaf8418c850ffedc460,0x7f84818512ff14860011,0x77a40c64383c1f50190a,0xfec122119ae691b0aaee,0xb83a6cbd8e3fe6f31975,0xff3798cbd7d682524370,0x30ed60910d4c3b58c850,0xa8c8871702231f48723d,0x1251ce7fe1b233b9b051],#[0x2d192c0b1b10ecd82bb8,0x908b8277c854805d4383,0x432a3dc290869a1c90,0x971400067ef8629903fb,0x2e2a4623dbe0c02844ff,0x50b94d89719fa68122,0x6be2a8c95f1546437176,0xca20e88e14844d7d8a19,0x68049143820c4edbc1fb,0x8b0033637e0990753f08,0x72ffd5448d54ec4a32f1,0x1fc9238c2143c7940a19,0xcaff40c8854707c08214,0x91c1e2041a3f46622a10,0xb8ffe130042865ffc825,0x97fb140412183fca108c,0xe0083766c16308bd4485,0x4ff440c8054f4ca12945,0x8af687d0801a1c1e482,0x787102106650d5ecab5,0x331fe1c084f3f57a5846,0x1939fe2328501ffcd403,0x34bbf8686b080873ced2,0x93af463cff3e21bc3428,0x31e61ae8512d8cc10b21,0x5ccf0aa719888a2bf664,0x91be200c60900ff62cc8,0x931cfef506469d783040,0xe2838048fb7488949de5,0xe1dacc42ec5f14349227,0x64ebd4500a428aff192d,0x8fca9913eb014ca1e7ca],#[0x7612d241a23fda60066c,0x3ba4ef3341fe7110284c,0x56fe0891fec31b65affe,0x48f97810243387ac4019,0xd80a31f16048ca57ed68,0xd1fd0732058bf00a4a3,0xd676a964d4bef50a9161,0x32692c10b37c4d584014,0xfc8111899f0ac1e3c42c,0xf200264268960e074277,0xa4833b76f0d2523397ff,0x9f2033427d502ca5ce1e,0xba7021f60d0dd9b045cf,0x4332f7c3af032abfec89,0x8195bcb6fa87c0cfdff2,0xc218b0f6d29c0cedf3e8,0x99bb78692919d9da6c00,0x1e7f9525233376c3d205,0x22bf0f87aaa01a09ee04,0x3fd540c0d239ebc4fa81,0x26c091ff9c8244915f84,0x22ec08dfef4268921ffb,0x2085f43f702113f0f032,0x843cbfa50a1086660f70,0x858fd890b293ed83944,0x84ce9f8f1748cc4fcc4b,0x41e77e09211d3ffd288c,0x718812967f8a2008ece9,0x3ed4422cff3201248a3c,0xb4cbb5a105f4cb6d010c,0x1134de5864bdfc5b54c,0xfd10310213537fcf8205],#[0x801403438f6b8f22c79f,0xa9a61bbd3494c4ceaff4,0x9a302e8a3762191fef50,0xe8cf621d8a13ff292810,0x89d13920fd00c98ad023,0x929f93028a2620945df1,0xa7c60a867bf42c963e1d,0x92444b3633f252a280ff,0x1a08120fd00c987f8340,0x7c8924c8a79f42157ffc,0xfe2010100957fc912450,0x301433b3fc9a00cc86d,0x8f7b5c22cbf0020e3ff9,0x9a02146e0516ff049123,0x976484b7fa00db8550bd,0x45cd216eeda79352fbe,0xbc044ca40be0226520bf,0xb6c65e7905938fb00a30,0xfec20f9d907cbe221aa3,0xf8804208d0ebfe4948be,0xc2257d018ddc06e3086f,0x190a4ab06ecd4321f727,0x4d1be2ba85c1225e1e6a,0xcc7f9ab899bf8690008,0xbfccd64d88544687f484,0x11b93e1113cc042f250c,0x70c4321f5261e8826a19,0xd8c6407dd643217117f0,0x7ad50303443f643212be,0xcff21a8141fe4a06286c,0xad0b0d16b424ff144011,0xc3024214bf18ddcd8bb],#[0x21a1f9f943215a91e8c9,0xc4bbac4ac29bf492d81,0x40913f5d051650db5881,0xa888fd3a19d0abffe0d0,0xa5161760e2f8128e0e2,0xc556ea29f421a9fcd008,0xdb5e1f032a7fd103254a,0xffa50132dbd2af4460a1,0x88df282c71a42133062c,0x40c08cce1ffc1a4652ed,0xd9341a15ecec00858ffe,0x9491daf1bc32923afda9,0x2566a74941cd685bcfd2,0x60ddf065043350fd0ca1,0x62b3d3e44a2ac4876434,0x2436b2e6dc2c2e7f2846,0x99a478a883491ce25c45,0x50c2fc507214297c18b3,0x83c582000439bf9a8748,0x1f85384851ff2211238b,0x8f9853848645be129214,0x957ad0acca87f1320093,0xf8e29542482afe80996b,0xe68fccf51a180f252a3d,0xfe148124857379994686,0x2e34185e6843150ff25d,0x523e7f8455196bc3af03,0x7cc802906e05145ff101,0xa26fe82a8b6e115190b5,0xd580b6428df6028e7f34,0x88f87d088e71f62990d0,0x4287d694ed97678e4d14],#[0xf952942863b63070c132,0xffc392028cff214db2b3,0x570194acc5bb071ed18e,0xd45108f44e7e64832b89,0x3207b2d8e1e03b1216ad,0xfd5cea68772e483eecba,0x83551973c1aa8cbcdffc,0xe38852426feba2032467,0x388a703452219e193c42,0xdfbf10604925447eb0d2,0xad002143e8fe10c0804a,0x900485eb7e3644902c5e,0xfff88e2140dc0a243f89,0xfc21a01237c1f8834922,0xe3d65a665e53e3102162,0xd28cc86edb6284e71ae0,0x477e94664bbc4286a4ef,0x7fe204d0090bf8813402,0xdc07028e3af640656d85,0xdfedd00cbce5e08311e0,0x5261f55128f0a80149,0xfea69901fd20084a3c2a,0x883617ef104a3d535444,0x45ed154617bd3518bfde,0xed135234a1b1e11e10c2,0x399520432dd3d81a934d,0x57fc5829940cfce0c1fc,0x2d5566849cc87df81432,0xb5d75ecc80c40576f0a,0x4356183efcc44f7fa10d,0x6557e4683fb1a8bbf31,0x9d18199968704237a6b2],#[0x46a69e951d786b4642e3,0xf05121d0d5f05129a7a5,0xc624301f586a3bb05155,0x7c6d3e120aba247ff4e8,0xcbf4cc9197e9990dd233,0x53b1a0ca9a4a5f446642,0x34e1d63972341f7d5332,0x95f090c8c7c81a8fb866,0x76f082b7cb841f7ecd0c,0x34fa032b5e99d475f0cc,0x2903527ae4c2c339a0cb,0x7a73c052e1d0874621be,0x1b2e408657425792160f,0x383c68146d7c8128c9fa,0xb30e8c63f410e6f702a,0x1c7e498f9f9890342ce9,0x66b1a175372021296734,0xac317f5454864c944ef6,0x81f9a0f1783b6c03d693,0x749378413149511e1d1c,0xb1479145917c84721c68,0xda942962c40d72970858,0xa4578aa83e2f7452f85,0x21010c2b5cafc255b3e8,0x7ba2b717416a50c0ddcf,0x1bbc7058f282c7e94191,0x8aafd458033c108efe04,0x16847e1046e3c4085c6d,0xccba28dc1fba9454742c,0x6f341b9fb01474f32a0f,0x808497f110616579a8e5,0x8ced041c195872a477e8]]
def p5 := limbs80 #[#[0xd028f0cef1a313b6d594,0x15fd00108afe800844b8,0x10945ae051abfa0021,0x6427bae83a2d7028d5fd,0x91e85d15a5a410818270,0x65fc600c9dc818d330d1,0x5440335a8ca084862c10,0xfa1008437e8402103ffc,0x4e8a9ab9a0d1f4eba10d,0xb1bbebf4219de84f09f4,0xdbaeb32a7faaa232edd0,0x4287a7fa5146858be438,0xe820e058932abfa26f00,0xa65517bf220e982683a6,0xaf6f24c8447f406810d]]
def g63D7 := pages512 #[p0,p1,p2,p3,p4,p5]
def g63H7 := limbs80 #[#[0x700044260a0008c2615,0x1a040185c00010100016,0x21a44084540009030,0xa0008805058481a09038,0xa040ac06000027402060,0x40d270a44a2a08014121,0x40e330b01402020703c1,0x800120210128046b0004,0x8f41c5304000000000,0xe020101800071f40432,0x440001000c2140088002,0x724a2e040bcf80200014,0x9814000a000000a063b8,0xa0301020080040c16160,0x8080996408330005c140,0x4346d121b80603040001,0x26a7627000105c430021,0x111f07378aa04f28dbc2,0x2aec5d6a318a44bc06cb,0x9e31d416b041f0a46893,0x8e6e01284963887c1e82,0xa7e850c425956e7daaa,0x8f0c3ac0719cd4450001,0xbb1486579a10a1892736,0xb178123f49c617800006,0x827463a9e5c9733c44d4,0x2343d50958af60dc472d,0x2d24594a83a62670afd9,0x58e2b000030c7e9278b,0x35180d164182000333b,0x298dc87f0040003046e,0x29d21a0114000522e00],#[0x1685a8de1218bf6000,0x884d00c8de0e30ad2990,0xc91f1230c00e90b3132b,0x6cb8031ad35821aa5586,0xbe14ceafb9138190000,0xb419f4e5aaa366578c19,0xd94368f804f521126723,0x3920000001002296325a,0xbe0f5113183032a00003,0x4e526355271218521e98,0xcfa8c7e83430e1c1692b,0x2bf24368f20dbad80001,0x8867aaa83e368ea2ff0,0x524865bc0fc85d0082a4,0x34e69d620e4d950bac1f,0xae74a209489da924f7c,0xd25ee055a7f91d646181,0x515a8496a8466a39a,0xa08ca7027b9dd2102190,0x8795704000000000001a,0x524e888aa2991c688dab,0x1ea06e71160aa1a24454,0x84aa1c2b7c4661d78782,0xc0005c9805f9b6e45678,0x2c2000106ae5f784,0x1c5f800000030cc,0xb0a7a01980e520280000,0x800162880016779a8927,0x8d4000000126d486f645,0x53a323222c8e08cd8d46,0xe8201477ed8f8280007a,0x5a980c278d8c18212],#[0x98033da01d0ef46c8c9e,0x7e0b6000408ae7411390,0x709da6950972430001c9,0x8cfc86fbf12443a5ba25,0xba81729411122ac809c3,0xfa34c125295c16008032,0xe1fa96ccaf12b489d602,0xe6a0cee9ba268e84930d,0x6914784d8001e883357c,0x446c4a6aa3a000626247,0x1f1238927c6ae7a5149b,0xbccaeaa0b08608d6cfca,0xa925000107ef22112859,0x811c5cb1a00006c9,0x3e8001a06e03ba7e0000,0x4b899453aaace05029c8,0x414487a7c5da7bda33f2,0x337692b953f048000647,0xaa65c406c000295c0006,0x187e328400050c746f8a,0x8553b4a83c31aac5a000,0xa9800000050b964253c3,0xd08492283b77068a0348,0x98b120c89c000019d1a2,0x29664ce920000138c60d,0x7ea9ae10e30dc0120005,0x8e5cac000007348e8102,0xe7a62a1e40a0f367ad8c,0xce4a404530001098ac61,0x10000459e271aec69334,0xc1d486c59da0000a5405,0x4302d80012680000a8d],#[0xc5e790001018e8b0e313,0xb0a3a07549aa8fa00030,0x28bd10f26621d2000013,0x78d8f7e509235cc4020c,0x1c0faba4891a418000a,0x9390e5c4c6e603c3d600,0x1888834071e4a5c7280f,0x1200021d4cf620230182,0x8ed80002720000e7c81,0xe2b4825262f0bfcd6033,0x417b225829600051c9,0xeb71e69b0ea44600000,0x4846c95000080a80bd63,0x9644d9a21fa28ca15071,0x9b446e9ce00039c143f8,0x832f9bb60032032b061,0xabc82f40003bb8000000,0xb000180629f4edcc3ba,0x51dc2ffea8c000383ca,0x7a4dc8ad43f87f289800,0x78a48507606dfa80000,0x1a6223a69265a9c663d8,0x822bd0f9657e9ff077a9,0x8709bc00041cb684da7,0x7d9a992c2e1666a2ea4d,0x1692d052b93448b09934,0x408e60ed01e665e977e8,0xbe8070f177854e09ba67,0xe66e5492b83fc979c799,0x642d011da71c1cf447e8,0x211013f4a9384aaf8688,0x7f719045b8000212ea06],#[0x80922000586ae76240d4,0x60a7249a110a41305a09,0xa47e178000c200001416,0xb382a0232c8264a2e14c,0x541c2c3c00053240000a,0x815800031ee1e22ed02e,0x49bb224e90de05da45,0x211bf881800001ca1580,0x5235aa]]
def p6 := limbs80 #[#[0x480201502014c2010c20,0x54420508205042048420,0x59020584205502054820,0x9502094c2090c2059420,0xcc820cc42098c2098820,0xd4820d4420d0820d0420,0x150301483010830d5020,0x54430508305043048430,0x58830584305503054830,0x94830908305943059030,0xd0430c84309883095030,0xd5030d4830d4430d0830,0x55032548325083215032,0x59432590325843258032,0x99432990329803295032,0xd5032d4832d0832cc832,0x148400c840d9432d9032,0x54840544404844014c40,0x90c40594405884058440,0x98c409884094c4094840,0xd4440cc840cc440c8440,0x548425084214c42d4840,0x94c42594425844258042,0x58043d484298c4298842,0x98843594435884358443,0x4845010c50108500c850,0x58850584505085050450,0x94c5090c509085059050,0xcc850cc450c845098850,0x5485210c52d0850d0450,0x59052584525805255052,0x98c529885294c5290c52],#[0x58853584535805355053,0x58454580549885359053,0xc91098c549885458854,0x14d101491010d1010910,0x1911018d101891015110,0x50510501104811019510,0x54910545105411050910,0x59510591105891055110,0x9491090d109091088110,0x98d10989109511094d10,0xcc110c81109951099110,0xd4110d0910d0110cc910,0xd9110d8910d5110d4910,0x10d20109200c920d9510,0x18d201512014d2014920,0x50520501201952019120,0x59120551205452054120,0x9492090d209092059520,0xc812098d209512094d20,0xd0520d0120cc520cc120,0xd8520d5120d4520d4120,0x109210c921d9520d9120,0x1512114d211492110d21,0x195211912118d2118121,0x90921595215912155121,0x9512194d219492190d21,0xd8121d5121c852198d21,0x149400c940d9521d9121,0x1954018d401894014d40,0x54140509405054048540,0x58540551405494054540,0x90d40909405954058940],#[0x98d409894094d4094940,0xcc940cc540c854099540,0xd5140d4940d4540d4140,0xc941d9540d8940d8540,0x189411814114d4114941,0x54941509411954118d41,0x59541589415814155141,0x94d419494190d4190941,0xcc941995419894198141,0xd8141d5141d4941d0941,0x14d4214942d9541d8941,0x90d42595425514218d42,0xd8142d514294d4294942,0x109500c950d9542d8542,0x4855018d501895010d50,0x90950545505095050550,0xcc950cc550c855090d50,0xd5150d4550d0950d0550,0xc951d9150d8950d8550,0x1815114d5110d5110951,0x549515095118d5118951,0x94d5190d519095155151,0xd5151d4951d0951cc951,0x10d52d9151d8951d8151,0xd81529495290d5218d52,0x1895418154d9152d8552,0xca10d8954d815418d54,0x14e1014a1010e1010a10,0x54a1050a104821015210,0x596105921058a1055210,0x94e1094a1090e1090a10,0xcca1098e1098a1095210],#[0xca20d5210d4a10d0a10,0x14e2014a2010e2010a20,0x55220546205062015220,0x596205922058a2058620,0x94e2094a2090e2090a20,0xcc620c822098e2095220,0xca40d5220d4620d0620,0x506404864014e4014a40,0x5524054a405464050a40,0x596405924058a4058640,0x94e4094a4090e4090a40,0xcca40cc640c864098a40,0x14e42d5240d4a40d4640,0x59242586425824255242,0x9824294e4290e4259642,0xd9642d5242d4a4298e42,0x552431964318a4318243,0x5964358a435864358243,0xd52439964398a4398243,0xd9643d8a43d8643d8243,0x14e5010e5010a500ca50,0x5865050a505065048650,0x90a50596505925058a50,0xc865098a5094e5090e50,0xd0a50d0650cca50cc650,0x582525525214e5210e52,0x90e52596525925258652,0xd4a5298e529825294e52,0x586535825355253d5252,0xd525398a535925358a53,0x98a545965458a5458254,0x1532014f2010f2098e54],#[0x50720503204872018f20,0x55320547205432050b20,0x90f20597205932058720,0x9932098f209532094f20,0xd0720d0320cc720cc320,0xd9320d5320d4320d0b20,0x1532114f2110f21d9720,0x59321583215532118f21,0xcc72198f219532159721,0x10b30d9721d9321d5321,0x1933018b301533014b30,0x50730503304873019730,0x54b30547305433050b30,0x5933058b305873055330,0x94b3090f3090b3059730,0xd0330c873098b3095330,0xd4730d4330d0b30d0730,0xd8b30d8730d5330d4b30,0x14b3110b31d9730d9330,0x1933118b311833115331,0x5533154b3150b3119731,0x597315933158b3158331,0x98b319533194b3190b31,0xd5331d4b31d0b31ccb31,0xd9731d9331d8b31d8331,0x553321533214b3210b32,0x59732593325873258332,0x993329533294b3290b32,0xd9732d9332d533299732,0x4874014f4014b400cb40,0x5874054b405474054340,0x94f4094b405974058b40],#[0xccb40cc74098f4098b40,0xcb41d4b40d4740d4340,0x54b4150b4114f4114b41,0x94b415974158b4158341,0xccb4198f4198b4194f41,0x5834214f4214b42d4b41,0x98f4294f425974258742,0x4875010f5010b500cb50,0x553505475050b5050750,0x90b505935058b5058750,0xc875098f5098b5090f50,0xd0b50d0750ccb50cc750,0x5535154b5150b510cb51,0x90b515935158b5158351,0xccb5198f5198b5194f51,0x59352587525835210f52,0x587545835498f5290f52,0xe5f1f98f5498b5458b54,0x5f6f777b7d7e7f3e9dcd,0xddedf5fabcfe77377fbf,0xeff77b7d7dfeeeff7dbd,0x3bffff7f7f9fbfd7dfed,0x4f01ba93a0ee84e84399,0x93c10e64f07b913c18e4,0x64f87b913e18e44f81ba,0x9c2e26ec0183ba13e10e,0xe90c0539c3002eb0b853,0x399c474a63504399fa0a,0x2ea201a312a680c48b04,0x1bb0ee0eec2b02ba0820,0x98c44a95b892a06eae30,0xbf2112b0aa24ac2a092a],#[0x10aa25042a0940f8c44a,0x5a7b115452e255173b14,0x5a8ec84b15b892c90c65,0x4c8abb15a8ec85694b89,0x95ebaa25795b8932baa2,0x4bc23812e7eca5794b8,0x212ed6844bb4a112f0ee,0xea4b94ba92ed6c84bb43,0xa91350ee04d423813456,0xca64d2e29934bea44d2e,0x5ba134bea84d2eaa134b,0x5ae045afb2934b8ca4d1,0xa4319169ec44594b8916,0x898c4560b3b1162aec45,0x616b81182cec560abb15,0x188ec84627b111852e24,0x4c0a3b1302cec460abb1,0x1428ec85096b81422eec,0x45714b895c2cec508abb,0xb15c34ea570cba95c98c,0xe24716b811c2cec570ab,0xbb11c7eca4727b111c52,0xeec4d8a3b1362cec470a,0xb3b1462aec5196b81462,0x2aec58263116052e2580,0x8b399229ac4488b3b160,0xa40e64e97b813a2ae848,0xe8c3a93a3ee84e8e3a13,0x3a28e64e8bb813a36ea4,0x530b3994c9ec4530bba1,0x11a2ae8590b399642ae8,0x846a43191a52e24696b8],#[0x21442cec468abb11a8ec,0xec510abb14428ec5123b,0xb891e5ae0478bbb1442c,0xaec479fb291e90c64794,0xb3b1482aec520b3b11e2,0x2ae8538aba12494c6490,0x1fb29208ec84814b8920,0x828ec4e0b3b1202aec48,0x28abb14a52e2528bbb13,0x6252e25896b81622cec5,0x588abb1627aca58a3b21,0x92632ea49a2b21262cec,0x44f17b813c2cec498d3a,0x213c40e64f13b913c48e,0xe04f0dba93c30ea4f23b,0x3913ca6e24f0bb813cae,0x8e64f243993c9ee44f26,0xfba93c78ea4f25b993c2,0x2ce659a3b21505ae0541,0x923913e5ee04f9eb2928,0xe38e84f903993e4ee44f,0xf8a3993e2ee04f8fba13,0x682ce65a1fb29522ee84,0xb596b82d6fc84b88aba1,0x2d85ae0b60abb2fe2aec,0xbc0bbb2e49cc4b90abb,0xab002aecbc26b12f05ae,0xe0b70abb30034eac00cb,0xb82f42eecb98abb2dc5a,0x8e6ba8abb3022aecbd16,0xaba2fa2ce6be8bba2ea2,0x94c6bc8abb2da5ae0b68],#[0x96b82de2eecbc8abb2f2,0x82aecb80abb2f62aecb7,0x116b83042aecbe0bbb2e,0xee28e6bb0abb3047acac,0x90bbb0082ee8bb8a39a,0xaa2c2028bbb02494c6,0xc028abb00a8ac80293b9,0x80e2aec0a22b20282ee,0xe6050bbb00e4ee403a8b,0x3100c2aec098bba01428,0x4ea0a8cba82a2eec0327,0xabb02e2eec040abb02a3,0x2ae8080b398202ae2080,0x8abb01a94c6068abb000,0xc94c6070abb0022eec06,0x4a2b20122aec010abb01,0x302aec07a2b201e2eec0,0x58bb88162aec0c1eb28,0x9982ee8060a3981828e6,0x46723b217c48e45f2431,0x91802cec6723b219c4ce,0xec681fb29a04ce468123,0x3b17e28ec66a9b099a2c,0xcec67933919e2cec5f8a,0xb3b16c4ce45b0a3b1822,0x4cec62a73b18a2cec628,0x933916e2cec638b3b170,0xc8ec8630b3b16e8ec85b,0xc93391722cec630a3b18,0x762cec640b3b1727eca5,0x650ab81942ae85d8ab89,0x1842cec5d13391742ae8],#[0x864933919228ec6123b2,0xb1a47eca690b3b1928ec,0xe6618bb81862cec5e0b3,0xb81882ce66a0ab89a828,0xce66a8bba18828e6620b,0xbbb32ea2c2cb8aba1aa2,0x2aecc49239312a2c2c48,0x28b0b142aeccc0bbb312,0xa2aecc18bbb31448e4c5,0x8a531b222aecc28a39b1,0xe7acac38bbb3222aecc,0xc58abb3102aecc98abb3,0x3347acacd0abb3282eec,0x6c78a39b1c2ee2c70abb,0x940494c7080bba31e28e,0xc90912b94248ac90113b,0xb2c2a4ae50a93b940a8a,0xeed08a531c222eed009e,0xabb4068ac901b2a14062,0x4ae509b2a14262eed018,0xbbb40c2aed09a2b2426,0x89eed020bba41028e704,0xe8d3ac2832eb0a13bb40,0xfa8ac8fea531bfa4ae4f,0x58abb4168ac9058abb3,0xbfc94c6ff12b93fc2eed,0x1000abb4182aecff1eb2,0x8c1c2ae9000ab8c002ae,0xc8ff92b93fe2ae9070ab,0xbb40e2aecff9eb2bfe8a,0xac90b0abb41a4ae5068b,0xbb8c122aed0b1fb2c2c8],#[0x34eb078cbac1e28e7048,0xa39c142ce70b8ab8c2e,0x82ae90c0b39c302ee905,0xe10398389cc40e28b083,0x3a40e60ea8b083a2eec0,0x158bbb03a2aec0ea2b20,0x83ea2c20f8abb0568ac8,0xc0c8bba0442eec0f9039,0x203c9cc40f17b803c2ae,0xe61326b104c2eec0f22b,0xba8588ac8160abb04c44,0xaec0d0abb05834ea160c,0x6b104e2eec1027310402,0x7aca170abb04e44e613a,0x8ab88522ee8118abb05c,0x25ee0108abb0362ae814,0x40bbb0428ac810903984,0x5e7aca178abb0508ac81,0x170bba04a2ee2120abb0,0xc622ced1f9139c7e40e7,0xd178a3b45a44e7211039,0xb4642ced201139c8028e,0xed139139c4e2ee91a8a3,0x3b47228ed1817b84602c,0x4eb208cbac8244e7208b,0xb3b45044e7140b3b4823,0x2ced220b3b47628ed198,0x8ab8c7a2ee91b16b8454,0x4eae11d16b848e2ae91e,0xa0b3b45244e714bb3847,0x7844e71e0a3b4685ee11,0x158b3b48a7ecb228b3b4],#[0x4905ae1240bb8c6e5ae1,0x7240ab8c902ae1242ab8,0x84922ee91c16b845894e,0xc2228aba4922ae12496b,0xba08a94c622a73108aa2,0xeec229f3288a7aca228f,0xeb28a094c62828b08a02,0x9ac428a8b08a27cca281,0x9eb28a294c628a7310a2,0xca2c2230bbb0a27cca28,0x3253188c9cc42326b108,0xa6a2c2298bbb08c3ee82,0x2425318a69cc429a6b10,0x90a66424281909028e6,0x4242929090a2a4242829,0x9090a2e4242839090a6a,0xa6242829890a6e424293,0x3a890a4e6242839890a4,0x6ea24293a890a2ea2428,0xeb288494c62126b1084a,0x9cc4290abb0847cca211,0x1f328a47aca2925318a4,0x694c621a6b10862aec29,0x3a73108e2aec219eb288,0x989ac4260bbb08e94c62,0x2a0abb0983ae82625318,0x8a83ae82a25318a89cc4,0x6248a398922aec2a1eb2,0xa89298e624a72989298a,0xe6270ab889c9eea24a63,0x2989c98a62726b889c2c,0xcea2726ba89c9ce62727],#[0xeb288894c62222bb0969,0x2aec26a53189a2aec221,0xa5b909e90e427a5b889e,0x428e62525ba89e90ea27,0xb9e398947ee4251e3909,0xe87eca840eba2103ee87,0x7a8a3b20c2eec7a0a3b1,0x1f028ec7c29b09ea5ee0,0x67d93b91f648e47d8bbb,0x9a1836ea7d8c3a9f640e,0xec770abb1dc3ae8770b3,0x3b20e2aec83a431a0e2c,0xae07f26311ec5ee07b0b,0xabb1de3ae877a7b11fc5,0x2eec7c8a3b1f22cec778,0x1fb2a142cec800abb200,0x29ac4788b3b2142aec85,0x127b12042ce6788ab89e,0x1a34ea810cbaa0444e68,0x7824319fe5ae07f8b39a,0x1e07eca780eba1e090c6,0xc808abb2022cec780abb,0x82165ee07d0ab89e42ce,0xe67e9eb29e67eca8596b,0xba1fa28e67e8bb81fa40,0xee8cf0b39a1c7eca820b,0x7b833e2eecd70bbb33c3,0x3ee8d0a8b0b42a2c2cf9,0x8abb33628e6d20bbb342,0x9cc4d017b83402aecd7,0x10abb3389ac4d416b835,0x622aecd50eba3542eecd],#[0xd60a39b4a2aecd88eba3,0xb525ae0d48b39b582ae2,0xcd58abb33adae0d4a531,0x2b645ae0d917b83462ae,0xe6d38a39b4c2ee2d31eb,0xb2d083ae9420fba4f028,0xeed3c8bbb5042eed3b9e,0xabb4e83ae93a0a39cf62,0x7acb3a8eba4ea2aed418,0xabb4fc2eed3d0abb4ea,0x2ae3400a39cf82aed43,0xb1eb2cec3ae93b0b39d0,0xfa2ae3408abb4fe2aed3,0x338dba8cea2c2338a39c,0xe4a2c23928b08e22eec,0xc340dba8d0a2c2340bbb,0xb0e8a2c23a0bbb0d02ae,0xe8350a398d47ca6350ab,0x210d4a6643528190d42e,0x6843529210d4a2843528,0x9390d4a2e43528390d4a,0xa4863528218d4a6e4352,0x283a0d4a4e63528398d4,0x8a6e835293a0d4a2e835,0x28abb0e694c6398abb0c,0xd28ac834a7310d22aec3,0x368cba8da9ac4368bbb0,0xea32ea3aa2b20ea2aec,0x2380bba0d628e6358abb,0xa0e02ce6381f298e02ae,0xec3725318dc2aec330ab,0xbb0de7ac8378bbb0dc2a],#[0x8ec9d8a398d82ee2361e,0xb3b27828ec9e0a3b2842,0x7ec89f1e31a7c2ceca20,0x1fb228c78c6a30dba27c,0x690c6a18b3b26c7ea8a4,0xea3b227a2cec9b8b3b28,0x8a8ec8a28b3b27e28ec9,0x9c8b39a722ae29c8b3b2,0xa922ae89c9faa2727aa8,0x89c2431a702ae8a48b39,0xb2808ec8a00b3b2708ec,0xa89d0ab8a742ceca00a3,0xb8a8e2ae89d1faa2747a,0xce6a50ab8a9434eca38c,0x8b0baa2eecf00bbb3a82,0x2aecf10bbb3aa2aeceaa,0x8abb3c22aece81e29bae,0x62eeceb27313ac2aece8,0xc0abb3c62aeceda6b13b,0xbc2ae2ef0bba3b028e6e,0xef0b39bbc7ca6ef1e29b,0x3b894c6ee0abb3a42ae8,0x8ee9eb23a62eecee0abb,0x9bb428e6ec8bb8bb27ac,0xc9500bbb5582eed4f8a3,0xbb5402aed500cbad408a,0xaed570cbad5c8ac9570b,0xdba5447ac9511f31d442,0x7aa9520a39d487eed510,0x8abb53832eb4e0bba548,0xa32eb4ea2b253a2aed56,0x3a2b254e2eed508abb53],#[0x4a2aed578cbad5e2aed5,0x548ab8d522ee9528a39d,0x53c2ae9549eaa5522ce7,0x9540abb53c32eb4f22b2,0x8d542eed540abb5508ac,0xe3518aba5547aa9550ab,0x39d4c2ee3531fbb54636,0xc6748aba1d62ce6758a,0xb3b1ca2cec718b3b1aea,0x90c6720b3b1b04ce46c0,0x13391b42cec720a3b1c8,0xc2cec6d1fb29b490c66d,0x40aba1ba2ae06e8b3b1c,0xc02cec6d8aba1d02ae07,0x751fb29d42cec738a3b1,0x9c22ee0708b3b1bc2cec,0x710b399d82ae0760a39,0x81da2ee8710a399c42ee,0xe70f0aba1da2ce6768ab,0xb84387ecb0d0bba43c28,0xae9110ab84442ae90e0a,0xa39c3e2ee10f9fb2c482,0x2ee1100b39c4a2ae1128,0xab844c2ee9100a39c40,0xa52e3268aba44c2ce713,0xbba4a82ced269139c9,0xa22ced251139c9444e73,0x2c1139cb028ed2895b8c,0xcba32eb2e94b8cba2ced,0xd259139c962ced2e8d3a,0x9cb228ed2915b8ca42ce,0xed2f14b8cbc2ced2c913]]
def p7 := limbs80 #[#[0xba4aa2ee12a94b8c9c2c,0x2e3308aba4b62ae12d8b,0xa3b4a62ced261139cc25,0x2ced2f9fb2cbe2ced2d0,0xb3b49e44e72794b8c9e,0x444e73114b8cc42ee12b,0x82539cc4a2e3310ab84c,0xc62ee92b8bb84ae52e32,0x318ab84c644e73194b8c,0xa2432ea892ab02242ae9,0x68c93b923248e48c8d3a,0xaa3230ea8c8fba23240e,0xe6938eba240aec0900db,0x3b21e2aec878eba21e2c,0x6e28b0b3b2462aec918b,0x4b8a38c8c48b263122c5,0x3ae8880f3b2489ec48e1,0x8a3b22e2cec880abb220,0xc2aec8f0eba23c2eec8b,0x98b3b24a2aec928b3b23,0x342ce6898ab82269ac48,0x940ab82509ec4908fba2,0x22290c68e94b8a3a2ce6,0xc888abb2227aca888eba,0x82282cec8f8abb23e2ce,0xca9314b8a4c56e28c0ab,0xb82363ee88d9eb2a2a7e,0xeca910bba23628e68d8b,0xa39d182ce6948ab82527,0x3ae943a531d0e9ac5438,0xabb5269cc5498abb50e,0x7acb440eba5109ac544],#[0x78eba51e2eed458abb51,0x1a2aed4a27315282aed4,0x488ab852228e7468bb85,0xd123ae944a531d122ce7,0x1490abb5202aed449eb2,0x9ab828e7470bb851c2ae,0xe8ae1faa2b87aa8ae0b3,0x3b29690c6a5a7b12962a,0xceca60b3b2b098c4ac0b,0x7b12aa28eca926312a42,0x36e0a98b3b2b22cecaaa,0xcb82b436e8a98c39aa6,0x34ecad0cba2b434e6ad,0x81f29aa078a6a80ab82a,0xa07ea8a81eaa2a02ce6a,0xae8b39aba2ae0ae8aba2,0x2ac90c6ab0b3b29a2ae8,0x8a70cb829c2cecab0a3b,0x22ae32e0ab8cba29c7ec,0xa8a88ab82a232e8ab9fb,0xb82a82ae8a89faa2a27a,0x4e6ad8cb82b630e6aa0d,0xb39abc2ae0af0d3b2b63,0x36e1590bba56828e75a0,0x8bb856a36e9590c39d64,0x22ae15c8bba56a28e75a,0xc0cb85702ae95c8b39d7,0x662ae95d0ab857432e95,0x5b0bb856c30e7598db85,0x6a2ee81a0bb886828e7,0xa1e8bbb0622ee81a8bb8,0xb0642aec1e8d3a87a32e],#[0xca1822b20602aec1f0bb,0xbb0702eec198abb0607a,0xaec1f9fb287e8ac81f8a,0xcba8742ee21b0bb806c2,0x2ae0200abb07434ea1d0,0x8bba06e2ee01b8ab8880,0x2ee3340aba0822ae020,0x28abb4d82aed320bba4d,0xce2aed330abb4da2aed3,0x371139cdc2eed33a2b24,0xce244e7388abb4dc8ac9,0x3350bb84d42aed389eb2,0x84d62ae1390abb4de2ee,0xe9398ab84e62ee9358bb,0xb80b228e62c0bb88b02a,0xaec2f0bbb0ae28e62c8b,0x2b90aa2ce62e0ab88b82,0x7aca2a8eba0aa94c62a9,0x8ab80ba2aec2d8abb0aa,0x628e62d0bb80b42ae22e,0x80b3b2542ce6998ab8a6,0x5690c697933925e2cec9,0x9893392622cec959fb2a,0xa582ae0960b3b2623ae8,0xa99133926448e4968ab8,0x9a5c2ee0970b3b2647ec,0xe69a8ab826a2ee8970a3,0xb836c28e6da8bb8b6a2c,0x4c6dc92b937228e6db0b,0xabb3667ecad98eba3669,0x2aecdd2531b744ae4dd0,0x13b93682ae2de0ab8378],#[0x28e6db9eb2b7c4ae4df,0xf8ab837e28e6dc0bb837,0x2a28e74b8bb8d2e2ce6d,0x4b1eb2d2c4ce54b1eb2d,0x5362aed4d0eba5342aed,0x74c8bb85322ae34d8ab8,0x9d327ee14c9e3853228e,0xa83c8a398f22ee23c9e3,0x298f42ee03d0bba0f27a,0xee83d1eaa0f428e63d1f,0xb398fc36e83b8c398ee2,0x8ac83b25318ec4ae43b0,0x22b20f82aec3b0cba8ec,0xa2eec3e0abb0f836ea3e,0xf9ebb0fa32e83e9eb20f,0xfe7aa83f8ab88fe2ae03,0x3d9fbb0f030e63c0aba0,0xac628e63d8bb88f62ee0,0x6b10aba2c62ce6b18ab8,0x92c22cecaf9fb22c478c,0xe0b00b3b2c228ecb0933,0xb82ca2ae8b00ab8ac02a,0xee2f38b39aca2ae2b28a,0xfaa3ce7aa8f38a39bce2,0x7ea8f41e29bd02ee8f39,0x8abb3c832e8f78d39bde,0x62aecf5a531bd64ae4f5,0x28cba3ca7ac8f28bbb3d,0xdc32e8f61eb23d832ecf,0xf71eaa3dc2ae2f70ab83,0xbe030e6f30aba3dc7ea8,0x2f48bb83d232ecf80d39],#[0x8d7a28e6f50a39bd22ee,0xe55e0bba57a28e75e8bb,0xbb58032eb600abb5784c,0xae3608ab85822eed600a,0xbb8d7e2ee15f8aba5822,0x2ee0300bb88be28e75f8,0xab88c62ae0318bb80c2,0x83ae8e02ab03802ee031,0x8bb838aaec0e40bb8b8,0x8232eae08eba3829ac4e,0xe30dbab8c30eae30d3ab,0xb922ae0e4a7b13922ee0,0x6e59039b863ae8e70ab8,0x93844ae4e11eb2b9644e,0xe0e39eb2b843ae8e1133,0xb839e3ae8e79fb2b942e,0xaa8408bb89022ae8e78a,0xeaa1042ee0410bba1027,0x2ee8418bb81062ee8411,0x9eaa10a2ae2428ab810a,0x30e4400db89002ae842,0x90bb89082ee0421fbb10,0xe47ea8f91eaa3e42ee2f,0xfa0bb83e87ea8f98bba3,0x3ec2ae2fb0ab83ec2ee8,0x4f88aba3ec7ea8fb1eaa,0xb3ee34e4fb8cb8bee30e,0xe2430bb8bea2ee0fa8cb,0x3990e2ee0438a3990c2e,0xae0448a399102ee0440a,0xab81142ce6448ab89122,0x2ae2b494b8acc2ae2450],#[0x8ab8ace2ae0b38b39ad2,0x2ce6b50ab82d42ce6b3,0xc0bb8bf02ae2b40ab82d,0xf628e6fc8bb83f228e6f,0xfe0b39bf62ae2fd8ab83,0xd8428e6fd0ab8bf82ae0,0x7618bb858628e7610bb8,0x858a28e7620bb858828e,0xe1630b39d8a2ae3628ab,0x3992ab0c64a8ab8d8c2a,0x8c64ac72992b1c864a98,0x7299411c865046219411,0x1ca85046aa14118c6504,0x2c319551ec8504632141,0xcb6c455ac3115664e655,0xb2c3192cb6c44b2c3112,0x5ab0c656adb115a60e64,0x4cadb1132b0c44c99399,0x95eb0c6579839932b0c6,0x44d443192f16644b9939,0x211710e64d4431935166,0xc856403115862e845adb,0xb295862e8562db2158b2,0xc646193b158b6ca562c,0xd31930b0c64c1939918b,0xb0c650983b13060e64c2,0x193995cb0c6571939942,0x664e6472c3191cc4a647,0x19939946b0c651ac3193,0x2264e6582c3196062e85,0x48adb212264e648ac319,0x93ab0c64eacaa12262e8],#[0x6532d2993ab4864e9839,0x2164b0c659193994cb0c,0x86592c21964b6c8592c3,0x2a164b2a8592d29964b4,0xec5139b2144e0c8512d,0x8ba148c6a852193b1446,0xb0c849193b148c0ca521,0x2db2124b4c8492cb2124,0x4b2ca492c3292462e849,0x92c39124b6ca492d3292,0x24b6e4492d39124b2e44,0x492d2a124b2a8492c2a1,0x124b2e8492c3a124b6a8,0xa492c3a924b6e8492d3a,0x9920b6ea492d3a924b2e,0xe649993996264e652993,0x39950b0e64f183993c64,0x4e654983993e64e64a19,0x6aa2e31ca6b8c721ae26,0xb2cabfacb22feb2c8b5c,0x1839ae4b4c6b91939ad8,0xc64e6c01939af0b4c6bc,0x71939adcb4c6b73129ad,0xf4b4c6b9acb22dcc2a8b,0xc0ad31b0264e6bd2d31a,0xaeab486baacb230264e6,0x8b7acaa2fab2a8baad29,0xa2fcb2a8bf2cb22dec2a,0xe6c11939af860e6ba2da,0x39aecb6e4bb2c392ec64,0xe6022d318091aa801ac,0xd3180ab2c8092cb20086],#[0x60e603ad3180e60e602a,0x2c21814b2c80b30aa02c,0x4b0e6052d29814b48605,0x52c3a014b4a8052caa01,0xb2c80bacb282ab6e80,0x8acb2002c2a800acb28,0x996b0c6659839812b2a8,0x667183997cb0c65f1939,0x9980b0c660193999cb0c,0x846699399a0b0c668183,0xba19a62e866adb219b04,0xc65f99ba99a62ea6699,0x93999eb0c66798ba97eb,0xb0c660b129982c0a6609,0xb1aa182c2a8609839982,0x2c4a668ac3b18266e860,0x9ad219a664e668ac319a,0x6ab6c85aacaa1a6b4a66,0x5b18ba96ab6ca5a98ba1,0x98ab0c662993996cb0c6,0x662c0b898a62ea629939,0x997104ec62c13998b00c,0xa6639939970b0c65c312,0x3998eb0c663b12998ec0,0x2e863b1aa18ec2a86399,0x9b218ce0c86318b898c6,0x60ec6319ba98c62ea633,0x18b899062e25c993b18c,0x62e86431aa190c2a864,0x4183b190c6ca64303299,0x76b6c85dac3217664ec6,0x5dadb2976b0ca5d98ba1],#[0x976b2e25dadb817662ea,0x85dacaa176b0a85dadb8,0xa176b0e85dadaa176b4a,0xea5dadba176b4e85dacb,0xba976b4ea5dacba976b0,0x2e269193999264e65d2d,0x93997a64e65e19399a46,0xb4c6c4acb232f1aa8cb1,0x1939b30b4c6cc1839b12,0x260e6c52d31b14c0a6c5,0xc9939b32b4c6ccb129b3,0x18b086c62cb2332c2a8c,0xc62caa318b4a6c62d21b,0xb08b2cac1acb2306b4a8,0x6c82cb2b0864e6c22d31,0x1b0cc4a6c31939b20b4c,0xc8c330aa30c64e6c32d3,0x39b24b4c6c93029b24b2,0x2e2c2ad29b1ab486c699,0x8b8b0e62e2c8acb2b0a6,0x62e2c9acb230ec2a8c39,0xad2a32ab2a8caac2a32a,0x860e6c599b8b16b6a8ca,0xd18b8b3464e6ca18b8b2,0x4b0e6c72db8b1c64e6c,0x2ad31c0a60e7012d31c,0x40260e700ad31c0260e7,0x908c0a142266e900acb2,0x9c0cb4c70198ba422b2c,0xa9031839c0cb4c703312,0x21c10b4c70419ba40cc2,0x6eb05acaa410b4a7042d],#[0xdb8c1cb6e10730aa4186,0xf0e60e4590838b2a9072,0xacb2054b6ec0e2cb2038,0x666e40e983903ae6840e,0xf993905662e415b8a105,0x5a66e40f983903ec6a40,0x16993905a62e416b0a90,0x44b284112cb205ac2a8,0x8112d2a044b2a8112da1,0x103262e20cadba044b0e,0xe21319b883cb2ca0cb8a,0xb285862e21639a104c62,0x2a80d30a903462e20d2c,0x8b884e66e2102cb2034c,0xb2c81718b885cc6a4139,0xad2a046b2a811ac2a046,0x266e210acaa052b6a811,0x418b885066e410983904,0x5e62e217993905062e41,0x122db884864e41798b90,0x45c60e5172db9048b0e4,0x518993947e62e51f99b9,0x948462e52119b946260e,0xc916bd21c5b164316993,0xba45a62e916adb245ab2,0xed1699bac5a62eb1699,0xcb247cf4871f2dbb45ab,0x66e91f18ba47cb6c91f2,0xb8a145e66eb1f18bac7c,0x62e52038a148062eb17,0x931a9464c2a519193948,0x64c2a91919b946460e51],#[0x192c3b46466e91931aa4,0x48662e521b0a9486b6ed,0x5232caa46ab2851a9939,0x944ee28513993948c62e,0xeb18392146066e318193,0xa147262e31c99bac6062,0x6eb1c98bac7262e91cb9,0x8b8c50b4ed1cacbb4726,0x66e3199939450c2a5141,0x98b8c7666e919b129466,0x6c6a91db0aa476c6a51d,0xdacbb47662eb1d98ba47,0x6cb0a91b18b8c88b4ed1,0x1eadaa46cb4a91b2caa4,0x474f2e51d3cb8c74b2a9,0x51e193945262e514bd39,0x948a62e322993947862e,0xe51598b945664e52298b,0xb949064e52418b949064,0x4e51618b9458b4e5242c,0x92188a64e52498b94926,0x64e622983988ab4c622b,0xbd990a2b6ec22b9ba08a,0xc66e42331a908c62e428,0x9983988cb4c623302988,0x90b6642418b90a6c2a42,0x292cb288462e2212d298,0x88e66e22398b8886b2ca,0x22a18b889860e623ad31,0x8888b4a624ac2989262e,0xc47bac311ee62e42218b,0x319ee66e47b98391eeb6],#[0xc6842db121060e67bac,0x8399e8b0c67a45909e8b,0x60ec7a2c3b1e864e67a1,0xc598a0ab6ec7a193b1e8,0xa64e6829839a0ab0c682,0x33d9920c64ec82983b20,0xc60ec83193920c62e48,0x7c31a91f0b0c67a993b2,0x9f0c0a67c19b91f060e4,0x484b0a921260e67c2c31,0x1a12c4a684993921262e,0xe47dadb11f664e684ac3,0x399f6b0c67d99b91f660,0x6ca862c31a18b6c48618,0xd21a18b284862d99218b,0x62e2772caa218b4a6862,0x393a1dce2e8773d991dc,0xc60ec772db29dcb2ca77,0x3993b1dcb4ec772cbb1d,0xeb2ca83bc31a0e62e28,0x7b193b20e60ec83adb2a,0x9fc60e67b2c319ec66e2,0x27799399fcb0c67f18b8,0x19dec4a677b0a91de62e,0xc67c99b89f264e677ac3,0xa920062e28018399f2b0,0x4e6802c31a00c0a68031,0x939a14b0c68518b8a146,0xb6c478acb11e262e2789,0x99399e2b4c678ac319e2,0x264ec78adb29e2b2ca78,0xe2c319f8b2a878aca01e],#[0x4b0c6812db120460e67,0x86ac31a1a62e2869939a,0xa1ab0ca869939a1ab4c6,0x686adb2a1ab4ca86acb2,0xa21ab4a686ac29a1ab48,0xe47f98b89feb6a886aca,0xb91e062e27819391fe62,0x2e48098b8a0264e47818,0x8b91e462e27919392026,0xb2ca792c329e464e4791,0x2cb89e4b6ca792d329e4,0x4b2e4792c391e4b6e279,0x92caa1e4b6e4792d391e,0xe4b2ea792c3a9e4b6a87,0x8198b9206b6ea792d3a9,0x21662e48598b8a1664e4,0x47e98391fa64e6859939,0x920862e48218399fa66e,0x86cf4590b3c64e682193,0x39b3cb4c6cf3921b3ce0,0xe8cf2cb233c64e6cf18,0x598b5ab6eccf39ba33ce,0xb4c6d6b921b5ae086d6c,0x2cb235a64e6d69839b5a,0xc64e4d718b935cf664d7,0x9839342c6a4d0acb235,0x42c0a6d0b821b4266e4d,0xd830a936060e6d0ad31b,0xb60e486d8193936062e4,0x4d22d9934864e6d83129,0x9b48b4a6d22d21b48b28,0xc8cdbd9933662e2cdac3],#[0xb8b5eb2eccdacb2b36b2,0x6e2d02cb2b5eb2c8d798,0x8b8b5060e6d02d31b406,0x62e2ce1939b50b4c6d41,0x3129b38e486ce30a9338,0x4e086d119b8b4464e6ce,0x518b8b5460e6d12d31b4,0x54c0a6d53821b54c6a4d,0xd898b8b6264e6d52d31b,0xb4ab486d29939b62e486,0x4d498b935262e2d4ad29,0x9352e2e4d4b8b8b5264e,0xe4ce98b933a62e2ceb93,0x3935662e4d598b8b5664,0x4e4d918b936462e2d919,0x9b94f0b0e6d31939b646,0x60e73bad31cee60e73c1,0x3d99504b6ed3b9939cee,0x266e53cb1a94f262e541,0x2b0a950a60e73cb029cf,0xe862e33a2d994f662e54,0x3d18b8ceab2cb41acb2c,0xd0c62e33f1839cf466e3,0x53b18b8cecb0a73e18b8,0x98ceb4c633b1298ce62e,0xc8392cb20e2b2c833983,0x990d460e6342d318d0b2,0x86352da10d4b284352d,0xc3a0d4b0e6352d218d4b,0xb2c839acb20c8b6e8352,0xac218d660e634ad318d2,0x716429d98b90ccb48635],#[0xd9939a7660e69dac31a7,0x82b0ec9dadb2276c6a89,0xa09839a82b0c6a0c598a,0x284b6c8a0b1aa28264e6,0x8a1193928462e4a13d99,0x1288b0c69e2db2284c6a,0xc6a2193928862e4a238a,0x9927cc0649f1939a88b0,0x284a3319928cc064a331,0xd99290c486a3312128cc,0x62e29b2d21a90b284a42,0x31aa26cc2a89b3d9926c,0xcc4ea9b30baa6cb6c89b,0xb2d3b26cb2ec9b183b26,0x86f0c6a198b8a8664ec9,0xa1adb2286c6a8a1b0aa2,0xa6ee2849b993b28660ec,0x69e99b8a7a64e69bac31,0x127e62e29f9839a7ab0c,0xc6a29939a7eb0c69fb9a,0x31a72b6c49c9939a8ab0,0x6c89cb1aa27264e69cac,0x1aa29264e6a4ac31a92b,0xb086a4adb2292b0c8a4b,0x193927062e49c2d21a92,0x464e4a018b928062e2a0,0xd31aa27464e49d18b927,0x74b2e29d2db2274b0c89,0x9d2cb9274b0e49d2db8a,0x274b0e89d2db9274b4e4,0x2ea2dba274b4e89d2cba,0x9ba8b4c6ea3029ba9164],#[0xeaea2cb23a864e6ea183,0x29bbf1662efadbb3a8c0,0x4e6ef9839bbeb4c6efb0,0x8b93c0f664f02cb23be6,0xe684eaacb23c064e4f01,0xb029baa66e4ea98393aa,0x4e284f11839baab4c6ea,0xb9939bc464e4f118b93c,0xa0b486ebaca13aeb664e,0xe82cb23a0f664e818b8b,0x3c262e2f0acbb3a0b2ca,0x4e898b8ba2b2caf0acb2,0x8bac64e6e8b129ba2e28,0xe6eb2d31bacc0a6eb19b,0x29bb6e684ed98b8bb660,0x2e2f19939bb6b4c6edb0,0xd21bb064e6f1b129bc66,0x64e4e918b93a462e2e92,0x99393b862e4ee18b8bb8,0x2b6e4ecac393b2b6e2ec,0xf9839d3eb4c74fac39bb,0x56c2a955acb253ec2a94,0x512cb2558c2a9562cb25,0x538b665523039d44c665,0x956b0aa55ab2c94e30aa,0x953cb087529839d42b2c,0xc86e19399b8b0c66e18b,0x319d6b0ca6e18ba1b8b0,0x2e875adb21d664e675ac,0xd211d6b06475adb29d66,0xb4a675ad219d6b4a475a,0x18b81ad12a874ad399d6]]
def p8 := limbs80 #[#[0xe62e06b98ba1acb6c86b,0x198b81c664e66bac319a,0xb262e06c99399c6b0c67,0x6c99399b2b0c66cb1299,0x1ca62e86cadb21b2c2a8,0x87299399cab0c67298b8,0x29b0b2ca6c18b81b062e,0xc67218b81c864ec6c2db,0xb81b464ec72183b1c8f0,0x2e86d2db21b4c2a86d18,0x8ba1ccc6a87318b81cc6,0x62e06e993b1ccc0ca731,0x98ba1bab6c86eac321ba,0xab0e06eadb29bab0ca6e,0xeadb81bab4e06eacb81b,0xbab4a86eacaa1bab0a86,0x6eacba1bab0e86eadaa1,0x9bab0ea6eadba1bab4e8,0x8742dba9bab4ea6eacba,0x99b662e06dad2a1d0b2a,0xca7018399c066e070193,0x399ce62e073983b1c0c0,0x4e67518b81d464ec7399,0xdb29bc64e66f18b81bc6,0xb0ca7619399d862e0762,0x99399be62e06fad399d8,0x6b4a70f2d21c3c62e86f,0xd2cb2c3262e10cc4aa44,0x34b2c90d30aa43462e10,0xdacaa444b2a90e18ba4,0x44260e70e99b843a62e1,0x52a18ba49a62e11218b8],#[0x94a8b2a52a2d214a8b28,0xa92e3caa4b862e9302d2,0xb84b066e12898b8494f4,0x6cb2eacb2cba62e12e98,0xcb2496c2a92598b8496b,0x62e92c98b84b262e925a,0x18ba4bcb2c92f18b84bc,0xab2a92a98ba49c62e127,0x98b84c2b2a92dad2a4a,0xa666e12998b849862e93,0x2798b84be62e12d3032c,0x4a062e12818b84c462e1,0x68918ba4c662e13198ba,0x924eb064939839a3264e,0xc68b2db2a46b2ca91ad9,0x31a38e0c68b1839a2cb0,0x4a6883929a4864e68e2c,0xaa22064e6882c31a20c,0x64e68f2c31a3cb0c68bb,0x9939a2664e692ac31a4a,0x260e68d2c31a34b2a889,0x42d21a5064e690ac31a4,0x28c2a888acaa250b4a69,0x8a2cb9228b4ca8a2cb2a,0xa28b6a88a2caa228b4e4,0x6931839a30b4ea8a2cba,0x951864e6911839a3664e,0xa5462ca9518b665462c1,0x29d18b6e5462c39518b4,0x4a7452cb2d26b0e7462d,0xc38524b4a746ad31d16e,0xb0c4a7b1a929eb6e1492],#[0xac31a9ec0a6a7adb129e,0x8b0c4ae31a92b864e6a7,0xe2c31ab8c0a6ae2db12b,0x9662e0a5ad992b8b064a,0xac18b82b0b6c8a5b0aa2,0x2b0c6a8ac30aa2b100c4,0x6a618b829864ecac2db2,0x9aa464e6a62c31a98c4a,0xc6aa9839aa4b0c6a9302,0x29ab262e0ac9939aaab0,0x4e6acac31ab2c4a6acb0,0x21ab4c086a9993b2b26,0xc0c8ad3031ab4c486ad3,0x2c31aa062e0a831b22b4,0xab0c6aeadb22a064e6a8,0xeac21abab6c8aeac322b,0x9c64eca698b829ab486a,0xa898b82a2c6c8a730322,0x2a2b6c8a8ac322a2c6a8,0xa8ad382a2b2e0a8ac38,0x92a2b2e4a8ac392a2b6e,0xe8a8ac3a2a2b6e4a8ad3,0x39abcb6e8a8ad3a2a2b2,0x4e6af2d392bcb2e4af19,0xca1568b6655a2c19568b,0xc2a9582d21d68b4855a2,0xb0aa57662e9582cb2560,0x2b4c758b129d62b2c95d,0x930aa56ec2a9589839d6,0x6ab0875ab121d64c0875,0x1a2cb2068b2c21a2d21d,0x6866ea1a2cb286866e8],#[0x81cacb0872b2a41a2ca1,0xa872b4ca1c98ba072b4c,0xc81aacb206a66e01a98b,0xb806ab0e01a99ba06ab4,0xe81aad2a06ab2a81aad,0x8b807af2a81e2dba06ab,0x62e01f18ba87ab2ca1e9,0x98b806062e81f2cb207c,0x66ec1998bb06666e019,0xb18b807e62ea1c18b807,0x74b2ca1d18b8074b4ca1,0x3498ba07662e01d98ba8,0x4ca62e13618b84c8b2a9,0x33318b84cc62e13698b8,0x84dc66e33399b84ce62e,0xe13898bacdc62e33718b,0xb8cd466e13518b8ce262,0x2e13819b84d662e137ad,0xc398b0b4a62c2ca90b06,0xb6e02eac380bab4a62ca,0x2caa268b4a69a2db88ba,0x662e29598b825662e095,0x618b825862e298b0aa25,0x58b2e2962d38258b2e09,0x962cbaa58b6a8962caa2,0xa6460e69699b8a5ab4ea,0x6daacb0b6a64e69918b8,0x9b76b4c6ddacb0b76b4c,0xe6db2d31b6c66e0db193,0x21b6cb6e0db2c3836c60,0x2a8db2c39b6cb4a6db2d,0xaa36662e0d998b837ab],#[0xb6e0de2c38378b2c8d9b,0x9839b68b2a8de2db8b78,0xb0e74bad29d2eb4a54b,0xdac3853662e34b2d29d3,0xf2b4863cadb8d36b6e14,0x3d2db80f4b0e03d2c398,0xf4b0e63d2d218f4b086,0x3fac380feb6e83d2c3a,0x1ac8b086b22db88feb6e,0xe0b018b82c062e0afad2,0x3a2c0b2e8b02d382c0b2,0xa6f6ad31bcec0a6f3ad,0xc21bd064e6f6ad31bdac,0xb2caf218b83c8b486f42,0xadb8bdcb6e0f72c383dc,0xcb0875f2c39d7ab4875e,0xadb8582b0e160ad21d7,0x80b6e42fac390beb6e36,0xe02cb138062e2e02cb0b,0xb9862e2e418b9380b4c4,0x4e62cb139862e2e62cb0,0x838a66e0e298b9398b4c,0xe4e6acb139ab6e0e2ac3,0xb8b8c66e0e318b8b8262,0x2e2e598b8b9262e0e499,0x8b938462e2e118b93966,0xb6e440ac3910266e2e39,0x2c3a104b6e0412c38104,0xa62e0fb19b83e8b6e841,0x32db910cb0e4432db8be,0xd064e4b318b92ccb0e64,0xb42cb8ad064e4b418b92],#[0x3f8b0e0fe2d392d0b2e4,0x161ac38586b6e2fe2db8,0x858cb0e1632c39d86b6e,0x6456c81912cb6e3632db,0x2192324a85648aa15920,0x4e45148b914524865949,0x8aa19b24a8bfc8aa2ff2,0x24a8cbc8aa32f22a85ac,0x492103920840e48aa307,0x920a80e492903920a40e,0xe49aa03924a80e48aa03,0x3920ea0e49ba03920e80,0x16c82945b22a81549ba8,0xc5b26a916c8aa45b24a5,0x51948aa47d26eb16c83a,0x988b20a622c9b946520e,0xa428c9ba88b20ea22c92,0x191ef266423481908d22,0x66484481921126647bc8,0x9291e920a47a48191e92,0x24a67a48299e924867a4,0x48aa1e920e67a48319e9,0x926ca7a48329e926a87a,0x2c829a0b26ea7a483a9e,0xb26a882c8aa20b24a68,0x8348a120d26ca82c832a,0x20d22a483482920d2484,0x483483120d26a4834929,0x2a0d26a88348aa20d26c,0x647c48191eb26ca83483,0x99213206484c9991f120,0x2e277481921920647dc9],#[0x8aa1dd26a47748a91dd2,0x22ca7748329dd26a8774,0x48ba9dd26ca7749329dd,0xf26a883c8aa20f24ea77,0xf482933d26ca83c832a0,0x3d20a6cf4921b3d24a4c,0xcf49aa33d22a8cf4929b,0xb5b20a6d6c9bab3d20ea,0x4d749aa35b22a8d6c929,0x935d20a4d7492135d228,0xa8d749a935d24a4d748a,0x193432064cfc9aa35d22,0x664d848193612664d0c8,0x8aa35f26a8cdc8aa3372,0x26653c48194f126a8d7c,0xc83acef24a73bc829cef,0x320653cc8a950526eb3b,0xdc9218cf208633c9994f,0xa92284a14921a8324869,0xefc821bbf2486ea4821b,0xd3f2684f048a13c12486,0xa6c49219d724866e4921,0xa1c922a87249b29b120c,0x86a849b29c920ca7249a,0xaa07322a81a4821abb20,0x6644cc99915b26644b48,0x83193126c85648321592,0x26e44948b912524ec514,0x48ba92526e84948ba125,0x3206460481917d26ea49,0xdc9ba17722e85dc83998,0x5b248516c9ba97722ea5],#[0x28c83988b22e31cc9ba4,0x1e924847a49ba8a326e4,0x682c83b1e926e87a4831,0xa20d26e483483920d20c,0xec8349baa0d20ea8349b,0x9921926647dc9991eb20,0x6c47748b11dd22e07749,0x8b2a0f24ec7748bb1dd2,0x26c478c8b89e324ca83c,0x4939a1b20c686c8319e3,0x520e47949b89e522e279,0xf49b91e524e47948b91e,0x3d20e6cf492133d2064c,0xd749b935d20e4d749ba3,0x33f26ead7483ab5d26e8,0x4cdc8a933722e2cdc999,0x9cef24eacdc8bab3726a,0xe69dc9bad0526e541483,0x9928926649e49ba27720,0x6849b48a126d22e09b49,0x8ba26d26c89b483226d2,0x26c8a1c83228724e89b4,0x4839ba924e49d48b9275,0x52664eac9ba3a920e8ea,0x849a13a12284e849993c,0xb920866e493a3a122e8e,0x75c92a1b922a86e49299,0x9d722a875c9399d724a6,0x87249b81c920e07248ba,0xb1c926ea72483a9c926c,0xe06ec9b21cd20c873483,0xb81bb24e06ec8b81bb20],#[0xe86ec92a1bb22a86ec9,0x9ba1bb24e86ec8ba1bb2,0x26c87049ba9bb22ea6ec,0x49381d922e07648381d9,0x924e67648399d926e076,0x948aa4a326ea7648ba9d,0x9f22a891c99924f26648,0xac48322b12664ae49992,0x2a322e0a8c831ab326c8,0x81a48ba06924e8a8c8b9,0x126ea1a48ba86926e,0x27000ee0052001980068,0x4004a8021600eb006080,0xe60069002fa016600a,0x262012300890040801e7,0xfa02e6016700ab405120,0xc06c00346019980c5005,0xfb807c003c901cf00e2,0x36011240868041601ff8,0x5026c013040956048e02,0x58602b3815140a60050,0xc60060a02ef816d40b3c,0x440d7206a60343019700,0x81c880e1006f5037201b,0x3de01e540ef6076a03a5,0x6b042102088100207e60,0x408f3046a822f8113208,0x12d4095904a402480121,0x81c13c609d104da8266c,0x902a5415040a63051d02,0x58a82bf015bc0ac9055,0xbbd05c602d8416960b2d],#[0x7e0c21060602fd417ae0,0xc195c0c9006398318418,0x349c1a280cf6066c8331,0xcc836081ad80d55069e0,0x80705837e01bc40dbb06,0xeb2074b839d41ca00e3,0xe940f2f078403bbc1da6,0x9c1f800fa207bd83d741,0x4160206e1020080183f,0x87e84364217810a40841,0x7b08b38454c226a111b0,0xe11f608ef046e8234c11,0x25581285092f04904242,0xcfc26521306096f04b14,0xa04ed02724137809b184,0xa2c850d0282a13f409e,0x4ee0a6a052d42938147d,0xf4155e0aa5054782a141,0x82bba15c10ad7856642a,0x59442c74161b0b01857b,0x7f05b842d7016990b3c8,0xe0bb205d4c2e6a17130b,0x17f50bef85ef42f3c177,0xce184a0c1b860743014,0x9831a018b60c4c062003,0x6514326019130c7c863,0xcf08670c3350197c0cb3,0x6a0d28068cc343219fe0,0x41acc0d5a06a7c350a1a,0x36a01b240d8806bec35d,0xf78376a1b9b0dc406dd4,0x9071bc38881c190e0206],#[0xe81873b839901caa0e4,0xd9f0ec4875b03a901d25,0x161df80eee077283b641,0xc3d1e1e6f0f1f878a43c,0x7c403dde1eda0f6607ac,0xcd87de43eb81f470f940,0x1100587fd03fa61fb30f,0x20a61040881a8408a202,0x27c21261080883a0418c,0x244360219610ba885784,0x88960445e221910f9087,0x17088b08455e228b1138,0x8b11b408d28466e230d1,0x2241611f888f4c475a23,0x496c2494123b89148487,0x5704a7a251d127f8937c,0x3097a04b8225a012bf09,0x1341899c04c98262b130,0x70f137c09b504d582696,0x42278813b289cf44e4a2,0x501c27f013ed09f184f,0xa22c50e2285b14238a0a,0x9c0a45c51f828d414588,0x714e28a6a8530e295d14,0x2a6715228a890540029e,0x6382afb156b8aabc5516,0x9057102b6e15ac0ace45,0x8b04457da2bd215db0ae,0x65d0b25858e62c4b161e,0x56169a0b44c59ea2ccd1,0x22de316da8b6785af42d,0x5ce22e5417178b84c5c0],#[0xbf45dbc2ed017578ba3c,0x30be145eba2f3b178d8b,0x18250c0885fe62fcd17d,0xd218538c23c60e8305c,0xd8314a18940c43861e23,0x463ca31ca18d38c62062,0xca1864e0325a191a8c83,0x928cbe4659c32b7194f0,0xc19c88cde466ae334519,0x34391a0d0cfe067b033a,0x99c34ae1a4b8d1cc68a8,0xbc6a9a35291a870d3dc6,0xd82c6bd035c11ad00d5,0xb4f0d9e86cce364e1b17,0x641b9f8dc786de036c01,0x837ea1be78dec06f1637,0x710a38631c1f8e088700,0x4d0722c38f01c680e2a4,0xa0e6b4732439741ca78e,0x1d2c8e8d4741c39f01ce,0xafe1d6b0eadc75203a71,0x543b861db38ed10763a3,0x478643c151df70ef1c77,0xf36079763c971e3a0f14,0xbb0f5487a683d151e7d0,0x81f088f7b87b8c3da01e,0x3eae1f4d8f9e87cac3e3,0xec43f3e1f8f8fc007dac,0xbc7fa83fb41fce8fe087,0x1023c80c6403b200f0ff,0x8a1040081d640ca205b,0xec20de1062482c841392],#[0x442662125108a8840e41,0x860242e9216410aa8850,0xe8886fa434f219a10c60,0xf1106887f843e321e290,0x225e112888918446c221,0x555229e9146089e244d8,0xdc45c722d2916308ae84,0xc8cfe46572319918408b,0x1c988e2446ef236111a8,0xe811e7c8ef8475923a21,0xf241d92064900247e923,0x48e12464922a090fe485,0x308495f24a3924849200,0x6893fc49d524d99266c9,0x92a6494ec4a4e251b128,0x5a592c8495f04ad5255d,0xf525e992eb097044b6a2,0xc4c6e262b930c8982e4b,0x9a144ce72663932a0990,0x6d09b284d7c26a9934d0,0x7938d49c2c4dfe26ea13,0x276793aa49d0c4e6b272,0xf9a27bb13d3c9e264ee5,0x4a500527f893f509f6a4,0xa1205076282e140f4a0,0x456ca25a5104286c142d,0xf994780a38c519428b71,0x2292e14924a434520628,0x5301297194b0ca53a528,0x71c537529ad94cf4a644,0x24a7e453d929e214eb4a,0x9520ca8be544a2a19950],#[0xa86953dca9be54c02a50,0xa12ac295560aa8055252,0xe56122afe1575cab7e55,0xad22567b2b2d95908ac4,0xcf8ae2056fa2b6b95ac0,0x595e54aef4576e2baa15,0x2c1015ff0afaa57bf2bd,0x8c02c5416240b0e05849,0xa4593b2c8b163f0b1ba5,0x4b35659972cc4965a4b2,0x685cb3ec59de2ce8166e,0x6416a8cb5085a622d1d1,0x12daa96cc4b61c5ae72d,0x5c072df116ef4b73a5b7,0x9485c8c2e3697128b852,0x5cba645d102e73972f0b,0x97764bb7c5d932ebb175,0xf48179b0bc985e252efb,0x3b2f8a97bc0bd985eb42,0xc5fb12fc817dbcbeae5f,0xc0b6602e300617fc8bf9,0x388c18460ab3043181a4,0x29857cc2906123308098,0x3113187f4c3b461b130c,0x2c6315398a1cc4be6246,0xfa6353319398c1cc5bc6,0xcc80663ed31e098e74c6,0x92b4c8fa646232221906,0xbc1956cca54650e32741,0xa3308997cccb96659b32,0x66ca334f199d4cc9c663,0xecc674b339419c30cdd8],#[0x9ccff867d333d399e28c,0x1a354d14e687d34271a0,0x4bd1a55cd27e6917347d,0x1c34fc1a750d376699d3,0x66a7d35341a94cd47c6a,0xd6326afd35739aaf4d53,0xf08d73c6b8735ad9acec,0x99b140d83c6bf235ee9a,0x368b1b3d8d99e6c9b363,0xda936c29b5b4daaa6d3a,0x506e1036f89b764db826,0xdd2a6e75372b9b918dc,0xbc74de146eea37689bad,0xd69be34dee46f52379c9,0x7381a1c074dff06fd437,0x70ce38591c248e0f0705,0x2e6714b38959c414e1da,0x30e3dc71d638d99c644e,0x9ca6ce4f4724639141c8,0x98e1cc18e5c872d13958,0xd239d99ce50e6f2734a3,0xa746a3a229d05ce7e473,0xea1074e63a671d2b4e92,0x6f0eb34756c3aa71d480,0xf1d90cec3a75f93ae91d,0x3b759db18ed5476883b2,0x7773bab1dcfcee587709,0xe877e13be81dec0ef247,0xcf0dc78573c171e054ef,0xe3dcf1cc78c43c551e24,0xc69e5a4f2ac79373c8b9,0x63d061e7b0f3a479ae3c],#[0x7ae03d569e9ecf4c07a3,0x7267b673da39ec80f604,0x18f84c7bfe3dee1eed0f,0x1f318f9567c8a3e339f1,0xeb59f510fa427cff3e70,0x173efc9f744fb627d8a3,0x27ea53f3f1f978fc7c7e,0xfe847f243f831fb98fd8,0xf5cff7a7f9f3fc09fd70,0xba0105005680153ffd9f,0x40582028901188076402,0x1474098a042901ca80ca,0xb481bf40d02061502ce8,0x104b082374108207e503,0xb65058682ac4149209f,0xaf20d410676831d417d2,0x441e9a0efd0756838041,0x847a4229a10cd082683f,0xa1a84f2426b213010944,0x290aee856142a7214dd0,0x218150bd085be42d0a16,0x356a1a450cc0863e430e,0x4a439521c490de486d34,0x87ae43c721ded0ece87,0x1056881443fc21f710f9,0x2f1113c887e442e220f5,0xaa24cd123488fa446da2,0x44e1a26a1131a896e44a,0xa784528228a5140489dd,0x188af1456da2ae5152a8,0x516f68b55459ba2c6916,0x302917ea8bcd45d122e4]]
def p9 := limbs80 #[#[0x582322918de8c4946122,0x446942340d19e28cce46,0x8de546df2367d1af28d5,0xd168e72472a238a11c00,0x411e4c8ef6476323aa91,0xa3f651f848f9947bca3d,0x85aa421120a490294807,0x3d48932441521ca90d24,0xc91b348cba45e522c491,0x247c92274906247b1239,0xb2125489288493824959,0x224ced263e9304496f24,0x49f924f312760938a49b,0x48a4a32a50ed28489409,0x7c951b4a7e25351295c9,0x52bc095c84acea55bd2a,0x59cd2cb696434b11a581,0x82a5b992d8696a44b462,0xa4bc1a5d912e9297294b,0x984f4c0f25fbd2f8897a,0x1de98c84c54a624530e2,0x5d32e699514c95a64353,0x268b5342699ef4ce5a66,0xd6a26ad9352c9a694d23,0x7b4dab26ccd36269af34,0xe9bf84df0a6ef937449b,0x39029c664e23270b1382,0x4ad3a289cf74e6ba72c1,0x9a76fd3b3a9d774ea927,0x4f1f2789d3c0c9dee4ee,0xee74f60a7a793cf49e5e,0xc9f6f4fa5a7cad3e2c9],#[0x93fca9fcb4fda27e7d3f,0x81f140c0a04b50172804,0x90283fd41cea0c1504ea,0xb50d52861542d4a13c50,0xa27051252888143f8a1d,0x61ca2f65169a8aa94524,0x2d4762a38c51ada8ce14,0xa91cd4890a41d51f728f,0x28aa93d9499ca4b2524c,0xaf52cb295cd4ab0a53d5,0xea60a52fe2978d4b82a5,0x4d5aa68c5335299254c5,0xcf14e34a6ff5373a9b45,0x629e994f0aa77253afa9,0x54202a0454fe8a7df53e,0x8ed54642a2b550fca859,0x36a98054aeaa4f95230a,0x95426a9eb54e8aa6c153,0xaa85550eaa6b5522aa8c,0x902ac0d55eaaad7555a2,0xf55ca2ade156a6ab3f55,0xac3b5609aafdd57a4aba,0x9caacc0564a2b1e1589e,0x255ad2ad4356932b4015,0x2b8a15c08addb56dcab6,0x75d2ba6d5d08ae665722,0x7457a8abcb55e14aee75,0xeafe357e2abe8d5f2eaf,0x60c0b04758172c04d5fd,0x3d161b2b0b5584dac1c5,0x32c5fd62b2b13e588cac,0x590cac7c563c0b1ba58d],#[0x2a3593f2c97d64a2b22d,0x8ab32459872cb816594b,0x96798b3b259c6acdb166,0xd21168c2b43a5a082cfa,0xa1ad45569dab4c55a58a,0x65adc2d6896b18b56a5a,0xb6655b1ead8556be8b5d,0xe82b70d5b702daf16d32,0xed6f8eb7aa5bc12dd816,0x2e1a5708eb8345c0b2df,0xc8aae3c9719eb8a75c3f,0xc05ccdae5c972b4b9345,0xba555d132e82973c4b9,0x7614bae15d61aea7574f,0xf65775ebb865dad2ecb9,0x22f1617864bc0e5df92e,0x5e872f3a97990bca25e4,0xdd15eccaf5c97aacbd31,0xecbe5e5f1c2f8517bf8b,0xd7dccbec65f572fa1d7c,0xfe157ecabf395f8aafc0,0x2cb00857fd8bfba5fd2a,0x26081b03a5816ac08560,0xc1d460d5b061d82a4c12,0x53ac2816132308d18408,0x898668c2ff616d30afd8,0x30ff987c6c3bc61c5b0d,0x26ab12a188d8c43c620d,0x9662bdb15358a3ac4f66,0xec6236300b177d8b82c5,0x8dbcc6c4634e319f98c9,0xeed8f1cc75b639831c29],#[0x1b213d9046c7f163ee31,0x6478b23359152c885643,0x9a664c4b25b19288c911,0xbeca406510327d593a6c,0xd9608cacf655ab2a2594,0x2f09972acb7565a2b2c9,0x45331959850cc0465f2b,0xf6691333f199b8ccaf66,0xcdf666e6b36959af0cd4,0xd8ace93673c339299c42,0x319ed6cf45678d33ba19,0x33fb59faccfb967d033e,0x83f34141a06ed0226800,0x436889b4395a1a4d0ae6,0x8d1fc68e1b4691a2f2d1,0xa594d2b96943b497da45,0xea5a6f8d347698f34bcd,0x735101a842d3fd69ecb4,0x6a96b5421a9acd4a26a3,0x5d26ad6b5631aae0d54d,0xecd65e6b233582dabd8d,0xdae14d6ee6b6235a75ac,0x5f11af16d77d6ba735cb,0x3cb6141b062d8136bf13,0xe6c8c3638db16ad89d6c,0xd9bb6cd1b6639b2d0d93,0x52ada6b6d2136849b3c8,0x1db6a0db1d6d7ab6b25b,0x3706db80edbd86dd8b6e,0xe7cb736db948dc6f6e24,0xac6eca375bdba8add0e6,0x4de386f08377b9bba0dd],#[0xbdf8decf6f58b7a1dbca,0xf19bf3edf736fa637c7d,0x4381e1c092e0206ffa37,0x709638415c1d4e0d1705,0x1bd70ce385d9c2c2e148,0xb6e23e7107387e9c3cce,0xdc5c2e2c1714c389e5c4,0x8e31c6c2e33c718b38bf,0x15b9035c7dae3cf71d93,0x5724a391d9c8c4e44972,0xe535728b393b1c992e4b,0xbfae5d872d339615cabc,0xe1cd30e66d732239885c,0x39d99ce62e700736bb9a,0x41aba06dd002e7cf73cd,0x327480ba329d146e86a7,0xce9e174d73a60dd2c8e9,0xd5a4ea9d7533ba921d42,0xe31d6beeb3d758bbabb5,0xd3b0b5d814ebe275dc3a,0x766fbb321d952ec77762,0xd8876b5bb52dda2cecfb,0xcaee3a77073b759db6ee,0x1de56ef0577643ba55dc,0xc05ddff2efc577c5bbd6,0x823c32de14af06678223,0xe78d5bc619e2a6f12d78,0xf29979383c8d5e40af1d,0x694f3377987bcbdde588,0x19e7caf3c179ca3cd95e,0xbd289e8f4f4587a123d0,0xaa8bd4d9ea36f4f57a62],#[0x307b023d769eb3ef5747,0x4f6de7b5abda15ecb6f6,0xef36f7797bafbdca1ee0,0x1d1f08cf8207bfd3df3d,0x2be4f5f212f8d77c523e,0x7d013e76df36af9877cb,0xaf67d633ea39f4d8fa36,0xd8fbb37dc33ed65f652f,0x1f93efc6f7e22bf061f7,0xf52dfa52fd0e7e6f3f2f,0x1abf839fbb2fdaf7ebfb,0xe7f6c3fab5fd1afe5d7f,0xff937fb43fcf5fe40fef,0x97002b8003bff8dff76,0x4201bf00bc8048401aa0,0x407de037f018680a1c04,0x161c0a6e04d9024c8112,0xc581d240dfa067f03008,0x10484822a410c2080703,0xb1b0552828a4137e096,0x9e60cbb06338304c1702,0x541cae0de706bb834e41,0x83fac1ee20f17076983a,0x8c48451421be107d0817,0x37097c84aac24c211eb0,0xe14910a1884edc271613,0x2c3e15b30ab98544c297,0xe942ece17230b5b859d4,0xc8629430f218250bee85,0xd1a8677c333219490c6,0xbc90dad86c1c35821a7b,0xe21d2b0e76872bc38661],#[0xc3c9e1e0f0ef1876e43a,0x7f8c3eee1f1f0f6b87a3,0xe8885b4423620d310378,0x111a088b5c44f6222b10,0x24db12388909447b2238,0xd4a264112ea896444a46,0x144ffa27a3139e89bf44,0x8a584523a28b114408a1,0x56d8a9dc542629ed14c7,0x8116018aedc56da2b2d1,0xe2dfb16d38b55459de2c,0x5fb22f6d17818ba745c9,0x64c625230c118378c064,0x8cc9c65c6327718fd8c,0x1a818d264686233d319c,0x6bb1b298d88c6b8a356d,0x5e37f11bdd8de046e223,0xc72fe392f1c698e23c70,0xedbc75fa3a8d1d218e76,0xa78f3a479223c3b1de48,0xf1f6e8fa147c1e3dab1e,0x409520188ff347f1e3f2,0x47241fd20df905a4822a,0x348776435d218390a3c8,0x914ec89ea44a1221d910,0x37091acc8c9e45f122ca,0xb1242791fd48f3e474d2,0xe49e124cc925ac920648,0x96c24b11256092994947,0x2fc990a4c3b25f292e64,0xb9371c9aee4d39267d93,0x27b793c749d9a4e61271],#[0xb32831940bc9fd64faf,0xfa521b28e69454ca1fa5,0xca78a535f298894b1ca4,0x569caa6654e72a3b9504,0xa695b94ad2a56532afe9,0x72c7c9621cb03657a92b,0x5ac32d32967fcb346594,0x8765bdd2dd196da4b61a,0x74bb125d472e709722cb,0x97b44bd0a5e5b2f0e977,0x2e97fd4bf5e5f5f2f88,0x1330e298604c25a60c13,0x6633f317c98adcc4de62,0xc9ee6493321598f6cc73,0x9fccc5a65f932e19955c,0x899f0cceda6725335a99,0x34959a314d106683533f,0xb2d35609a96cd4026999,0x1e6cad361b9afa4d6ee6,0xcdd1a6e2b36dd9b584da,0xbf24df266f4b377a9baf,0x909c30ce102705538049,0x3390d9c76ce352715f38,0x738f39989cba4e576726,0xa2674bf3a3e9d0fce7d2,0x7cecae76173ad09d55ce,0x9ddf4ee7a76ff3b609da,0xc859e2b4f0e678193be6,0x533d149e774f33a79693,0xa7bb93d969eb54f51e7a,0xfaf27d3d3e6d9f1ccf83,0xb44fd2a7e5d3f079f6ec],#[0x3a009cffce7fa73f9a9f,0x40a4a044501b680a3403,0x2ed4144a08ad03de8191,0xfe844141fda0ebd069a8,0x50b5a85714297a132508,0x1c750daa86894323a181,0x76a2295108687df43c2a,0xf450da26b512ea892f44,0x8bed45dba2d2515b28a7,0xb0a8d254674a322d1866,0xfd1db28e7d471aa37b51,0xa428520be900547d8a3c,0x953a48fd23a2915f4878,0x794a08a4f1d26d693094,0x695d54ab9a5465299294,0x2f7a976f4b85a5a2d2c3,0x5ed322e98cb4c3da609d,0xba6bdd350e9a194cdda6,0x4e4da713d383e9bd14db,0xe534ef9a76053a229cdd,0x929f7d4f8ea7b7d3d069,0xd4216a0b75034a80453f,0x8b1d44fea21d50dba852,0x10a8f754722a343517ba,0xb52cda950d49a2a48152,0xa7215369a9a4d4c7ea5e,0x22aa8bb5424a9f3d4ede,0xf5548aa9fb54daaa59d5,0xaaf755712ab2d5568aa9,0x6c5ab4ed59baac995622,0x455775aba2d5c6aade15,0xeb0935830abfbd5f36af],#[0x63b2b17d589fac42561a,0xcb565b6b2915923ac82d,0x8ad1ed6872b3c559b7ac,0x5b2ead78d6b22b5475a7,0x7cb5bbfadcd56e0eb6bd,0xceb9075c4fae17d7016b,0x57566ba4b5cf8ae65572,0xf11d7792bb815d9baebb,0xe3af58d7a56bccb5e4ca,0x35f52af9c57c6ebdf95e,0xc0976017aff5d7ec2bef,0x3e6c1cb60b1b04cd818a,0x7586dec30f6160b091d8,0xb146d8952c4696214b0f,0x38bb1aa58c86c5eb62c3,0xfd6447b21058feac78f6,0x2ca6b650ab269592b6c8,0x980acba36597b2bfd958,0x87d9b36cd496674b31a5,0xcb3d6d9df6ceb76735b3,0x685db41e5a03acfed67d,0x24f6905b46dda2c2d10f,0x32d3b569adb4bfda54ed,0xdaafad5216a54b51cda8,0x5d45ae0ed6af6b19b57b,0x9ab634db0c2d7ef6bd0b,0x96d5db6945b3ead99f6c,0xdcd76e33b6ff5b6fadb2,0xdc2de936f06b76adba82,0x15c0c2dff36fd0b7d15b,0xb88ddc3b6e1737090b83,0x201b8ea5c68ae2f9714e],#[0xeb72bfb94c5c95ae4597,0x2e769737cb9a45cc7ee5,0xd282e8c7742eb9fedcf7,0xaa5d4e6ea1974e4ba5ed,0x4bb095d786eb69758fba,0x76c6bb50dd9d6ec93763,0xf377776bb9dddbf6edbb,0x72f05377f9bbed5dedae,0xde442f1f378c3bc475e1,0xced5e6baf3157955bc98,0x9ebd395e966f46b7a06b,0xd7b40bd89debb6f5937a,0xf8237bdebddd5ee5af6d,0x366f96b7c90be38df0de,0x9df592fa797d1cbe7c5f,0xbf205f83efbb97da9bec,0xf11bf6fdfafefd157e67,0xd77fc0bfcc5fdb6fe937,0xb00d58046c00e6002eff,0x4d7020f80e8c0636023,0xf66072303318178c0a56,0x1c13e6095f045f8210c0,0x835cc19860bfb059f82a,0x80783f0c1e7e0eaf06ff,0x8b091b8474c227e10c70,0xe14fb0a3184f4c260e12,0x304617630b578584c2b0,0xb5c344619a30c7b8626c,0x78734c38b61c030dc186,0xfe987dcc3d661e0b0eb,0x37b11598881c42be20ab,0xbe267312e78945c48962],#[0xc53162913144989f1c4d,0xb27c57a62b23154f8a8b,0xd58bc0c5d162d9b16798,0xf18f58c62c61b6304f17,0x34cf1a278ce2c6596323,0xefe36fb1b218d78c6abe,0xc72f6392f1c438e02c6,0x8f28c77f63b471d498e8,0x258fe1c7d4e3dfb1ead,0xcb2185909ac835e41032,0x645ef22c3913dc88d643,0x931648d723f391cbc8d0,0x25c98464b932583929ec,0x393b9c9c664d97269793,0x28b7943bca0be4fef27b,0x4f72a1d94daca55e520b,0xe657b32b6d9592cab4e5,0xcb6265a7f2cf5964acb0,0x7accbbf65d3b2e3b96f4,0x25986dcc1fe603b2fbd9,0xf324d98f8cc6b662ff31,0x67cf3395999dccb3e64f,0x6666a6334e19a4fcd0de,0xbcdc166d4736619afdcd,0x9c20ce0666fd337a59ba,0x9e39ccbce4de71b3387d,0x573b4b9d6dcea46748b3,0x6790f3c4b9e03cef6e77,0xf8ee7b933d739e87cf2d,0xcacfd5e7e433ed59f43c,0x3a072d023680573fc59f,0x4231a0edd068682af411],#[0x73f4367a18bd0b7684ff,0xb68997447fa218d0fbe8,0xd1a1e8ca345fba2c7d14,0x43cd20068f77475fa36f,0x1ba4ded262e925748cfa,0xf4ba1a5a3d2bb6950b4a,0x9a934d03a663d315697f,0xbbe9d474e57a6f9d367e,0xfd40d69fab4f81a799d3,0xa8e8d463ea26750d9a83,0x36fa982d4af6a4ef5231,0x775491aa23d4ffea74b5,0x6ab8b5589aaa0d53dea9,0x5d26adf35693ab23d581,0x67d6246b0975803abcfd,0x3acf6d6686b2df591bac,0x5b45ad82d6b1eb5035a3,0x9975c89ae1ad6f7eb71b,0x3ebbf75da1aea6d743eb,0xd7e06be675edfaf44d79,0x68d822ec08f5ff9afdd,0x37b100d871ec2cf6115b,0xb6321b170d8a86c4e362,0xc94b644fb1fdd8eb6c6e,0x79ecb4b6565b297d93ee,0x6d9bcecd67667fb31dd9,0xb412d9f96cf376761b39,0x991b4a7da3eed16f6869,0xb36af1b54bda8e6d3bb6,0xed9476c53b60ddaf26d6,0xb8a6dbaf6d79b697db39,0xdddbddede4f6ee5b746d],#[0x5b88cdc2dee0b7700db7,0x72c9b938dc886e397717,0x91f7439b9f4dce4ee65b,0xa6ec1b75a7baa8dd3eee,0xddf1eeefb7725bb59dd9,0xccede4def1a7787bbc15,0x1bbd64de9e6f46379d1b,0x77c57be09dee9ef6ab7b,0xfb737d77be92df32ef91,0xcdefdd77e79bf1cdf7c6,0xfe023f00777ff9bfcedf,0xc10fe0757031b813dc06,0x3bdc1aee0bff057f8277,0x5384ebc249e10f707ff8,0xf0ca38609c2e2e16070a,0x1ed70eb38719c368e1a1,0x99e23a71127884bc3ffe,0xbc51ee280f13778985c4,0x8b85c59ce2bef158f8a7,0x9838c79c620e30271787,0x3f1bbf8da1c6afe34471,0xe3d2f1df38ea1c727e38,0x87ae421720638fe9c7d1,0xa5c92ce484723739163c,0x393d7c9c6e4cc725db92,0x2a7794f1ca55e51af286,0xb3f2d1b963dcaf1e564f,0xe5fbf2f679769cb88e5,0xccb1e64af31a7987bcc2,0xad7cd44e68f733df99af,0xe79c21cde0e6ddf365b9,0x73a439d11ce80e72ef38],#[0x75c73ac39d51cea0e74c,0xe0e76c73b439d91cec0e,0x1cf00e77c73bc39dd1ce,0x9e51cf20e78c73c439e1,0xd439e91cf40e79c73cc3,0xc73dc39ed1cf60e7ac73,0xe7cc73e439f11cf80e7b,0xfc0e7dc73ec39f51cfa0,0xd1cfe0e7ec73f439f91c,0x3a011d000e7fc73fc39f,0x40c3a051d020e80c7404,0x2c74143a091d040e81c7,0xe83c741c3a0d1d060e8,0xd0a0e84c74243a111d08,0x191d0c0e85c742c3a151,0xc3a1d1d0e0e86c74343a,0x74443a211d100e87c743,0x89c744c3a251d120e88c,0x60e8ac74543a291d140e,0x1d180e8bc745c3a2d1d1,0xa351d1a0e8cc74643a31,0x743a391d1c0e8dc746c3,0xc747c3a3d1d1e0e8ec74,0xe90c74843a411d200e8f,0x240e91c748c3a451d220,0xd1d260e92c74943a491d,0x3a511d280e93c749c3a4,0x4ac3a551d2a0e94c74a4,0x6c74b43a591d2c0e95c7,0xe97c74bc3a5d1d2e0e9,0xd320e98c74c43a611d30,0xc1fd340e99c74cc3a651],#[0xe0b00160f8418023a004,0x5014480c090681044c0,0x60388a8282867001c1b,0x8e25e093204451311886,0xc4e090885409040c884,0x2a383b0781a13080241e,0x20a00e1cc34651286868,0xcc10021c9c4083215884,0x116181005e840b20b083,0xa02170d2683603130087,0x892211a4a48421034527,0x9a4c941158bc294e9900,0x354d49c58971d8846612,0x6cb38d4b43cacc5a3c6e,0xf21689872c3192494c62,0x8335d391c27a48e130,0xf06808d3ffa01846af14,0xcf91c271fd62a1a9227f,0x5c4e7f958135d391c270,0xebfa3ed011f7ef21d9b9,0xd72659a908abf884b168,0x618bf428c3f4b168a647,0x611d7e32ac423f7e3632,0xaee2a257a2285974c0cd,0x35fb9d08bbf790f7ef21,0x7cca82050c3b26a2d772,0xb8921d5aa0814347262a,0x57328acd445ca11c457b,0x4ca5edd1399749a89919,0x127da439cc6022d53fcc,0x5759abf4007a00d1b055,0x17a2506107548601ffa7]]
def p10 := limbs80 #[#[0xabfb12170f31b74fa264,0x28f548c2860692fe30a1,0xeff08bc4cfefe808142d,0x2f5af922871fbfac4cd1,0x972847388e3f389021b1,0x4fc30943325f62891c98,0x4738a445ca143b415840,0xfb8ee75850cae1e840a1,0x26232ae72e911f782122,0x4660c499cfbe345a3f7b,0x77ef21a7ca8311987f0c,0x8f3ed21efde431f7a311,0x9a50f5087a843f58adba,0x399115e0e835ff68186c,0x80682e9fe62659390c7e,0x4deb8da0aa417ffa06c8,0x267d199936ea1d7e12a6,0xd072f02d42525c90646a,0x9636cacf5967ca911df3,0x8589a92ef9100a521a38,0xcbb61c647788a0c63f18,0x655c01f514754861d398,0xc91d68964cf58bbcac5c,0xb916ee2377cf41e7ecdc,0x9324aee47bdc4422cfa0,0x22eda8975dc92552e895,0x94913298fd9139940eea,0x8c64d48aee47324225e7,0x53e4c910cdbc9089a3f5,0xc0132c9e6c458ff22019,0xe451bf42449ef1a44ef5,0x99ec02e1cec45be079d],#[0xc1322ee3cf302473ce66,0x4de20c453f0f3af050bf,0x1d289465931e861b7026,0x89f244a32aff0358848f,0x5fea8994be6b8c87e644,0xa8991e9f8073ce66098b,0x30052671c8431c8432fd,0x31cdf8256a38e42197c8,0xc03292672975d132f749,0x4ba7c365336e0b351a2d,0x83a0e731088883ea30a1,0x31f095328fea30b923e3,0x23d438f8611e659f690c,0xcc4cb54ff31329f3604a,0x13fc084ca9f45d4ca9fd,0xc91a7f8c2e48d2f40021,0x2e4ec4b2f4002127f8d9,0x8e6022d33e04b2f40021,0x8124fbfa018024dc8120,0x690e78e6022a8e6022dc,0x21db88f0e54516ee239f,0x12237eaee650fee241d5,0xbf5689977e028e691c79,0x9afef39120523f38a915,0x13e4818651d521d9b9b8,0x234e6f8883942a74a2a1,0x122651c74b1e22e1a9be,0x5106ca1efa50f6a743d5,0xab445c4eca2ce9435f7a,0x3da24881b28cbc968822,0x55f7a5106ca1aeb48739,0xc7a93619576e86b89d94],#[0xa0c8b5c088f6691a3c21,0x41e1cdd11a2e27446aac,0x886cf78261ced1141e66,0x43c7d320c6a8e22aae38,0xaa15720b2ca5f14c73b8,0x151cae0931f6473b8439,0x86c410d8a3c049b0cdbc,0x337578207519e9e8a830,0x8c19e672869f8262d,0xe19c654f9000460ce9f2,0x38cc3c1bf228df022173,0xe3e419c6599ca1a7e098,0xc8b3f501f08c23044f91,0x76b31e894398e50c7dbb,0xc64532863f1cc89b721a,0xfc918aaa490bbd0cbb61,0x318263f447d15d4046d1,0x55465df0219a441f466,0xe043a2bc9908d8f8c75f,0x44afc5c5996723c08bb,0x71d0b2065cf0cf664de8,0x8605bfc11e3d6634d34c,0x2b9991b1b185b695619,0xdfca832d7687532977d,0x6aa2270f03a9996c2e89,0xc7995be731b746e732ec,0x311e86724bda8f3244b5,0xe10c35f8706332ffc403,0x15df3d079ff09345665c,0x2e8943afcf45a65caa65,0x19abcb8b35899f3d7063,0x3d54ca2a99434febc507],#[0x1993c7320655f678848c,0xd0819a3f420640e492cd,0x36df09133e3da332e438,0xf968cdeb54648f7c4903,0x1f10455ff88066238d03,0x91b7f8b41147de8c451f,0x431832a78b460cba2bca,0x9c2456899ea0de54ca59,0x65e4c2cd5b353884109,0x3d908649f09d4cd1ef91,0xd3fd080568f53a12d7b2,0x2e34254fdcc7589460cc,0x3a99a67cf23c11c73751,0xd7b024519b65c88b54c3,0x41e7fb20c897ca1e5aa1,0x943c394338c3ce4def06,0x1d79e183c47678320d2f,0x90738e847e88eb1c4b05,0x1a4640cd90db646504dd,0x7cc88c668c74084819f2,0x53836a7e74195937641b,0x6a3a360cb9062e56cda1,0x47df9a13746697e2319,0x4f4691d66f784790573e,0x3e5d4c9ddf0ae655f661,0xd8753244aac7dfa50190,0x316b8f326da86debdcc9,0xc33121b8fa10d96e8ee9,0x58b7d023066388b67fe0,0x32197f8282b2b7d02306,0x60f0d9990bfef3a99987,0x78a347c38b8ca3c58ae4],#[0xf30e31cfd0dc4234c751,0xf5a6c6848ff68b26099,0x91d46817660fe8464db9,0xf240645353f11538e68c,0xf5b222ac07a27e26460f,0x4656ef89465eec50d917,0x2311803fd3119993e489,0x758011fbfc04c2330e37,0x1c0332e4efe30cc491f5,0x380c910e0c7b6a1b6987,0x2c7836e12a678870632e,0xb39aa2572ad991bf5773,0xcc85d30953287c2ccccb,0x7c9a56655343e28adf02,0x19e21c604419e7ddb22c,0xd3187b940619aab8db80,0xd39922aa9ea26c5c899c,0x8d203e9acce2b3cec544,0x4f18857fcc9147c7a015,0xf1320e7901103e19e065,0x52cf9a4f3fd6138c090c,0xa51578bc5228cfce648d,0xd0a33a9475523d08ca46,0xce00336eaf9923072c63,0x9993e2532572c63eff8,0x820068d297ea51a3ce6e,0xa80d1c2186c2cb5fe519,0x7b8a6475c5bd4c8ebc47,0xa9436f9631eeaf99230e,0xd1a52fd4a347991c1334,0xf5c9dc529116fd1029c0,0xd1eb00a166d11c91a34f],#[0xc839a8c60478e3f7800c,0x939f4226e9bf442e5c9e,0x318e479ce3022eae9610,0x40f58a51ebe8de0651ab,0xcd77079e4c5feef0019b,0x5d08bdf875322794e1d4,0x2b76f9cc85f5b9ce661c,0x46cc8bfa9c3151d4c46a,0x77f148c6a3d1e99e4c1d,0x433c9ad2960c3f2c0c19,0xa98ea345c7c151150b1e,0x99a8b55b32c67a042533,0xcf265ebec1a8c1f620e1,0x5c906a366b1a39334790,0x87cf7146a38f9cda8d47,0xa75963f857320e48351,0xab7f0065aa7e026ca9f1,0x341820f35509ddfce64c,0x321c9068d837d5a111e4,0xcc27f07162a4027cd253,0x32efc21c51a3f5bad62e,0x3508bf8e49151c3f0a07,0xf842532e27e78032f3d0,0x33afe3807423ddc232,0xf46e64f74e81099dba06,0x2b7cd073287f4405b2c7,0x93f87848b5e5c9160c6a,0xa2a734b3543b68cf2a8c,0x89b678ff64823669999c,0xdf21aa9d025f488ff540,0xdb7c8707e43c960db32e,0xd1fe449f759a7a78f848],#[0x2a645118d9a67a78f848,0xcf2a8c91fe1aa0608ce9,0xa3269f1e122a8f87c246,0x7b30443b3317aa323278,0xc98f6ea65e8d3c9baa29,0x876c894876c91f758e3a,0xadd0998bf11c510668aa,0x3ef1c89923cbd8b32d78,0x9173932a79e44c9c5c36,0xc7284cab93d7bf092427,0x5f5b0c9cfc0c1c7acc65,0x84cd1e5eb419988b86c6,0x7d9e50995bd0d8ebc56e,0x2f2d9f5978b86c6dce4c,0x8c9e731a32e726044f66,0xfa4703a70fc479ae30f8,0xdb6644327bd24719ed9a,0x737b654fd2b0caa33a75,0xfc861e0db326ef21b7a,0x685da3ef48d9edb79996,0x598d8b86c6de69660887,0x6659c2f14918b8d98d3b,0x543b669cc2fa454f60cf,0x96348d8f4ee3528ddf93,0x2c199928ee628c1105ed,0x75b506986626f363a965,0xdb2eb1b654ed6631fbc8,0xc3217d6c326d6a857e91,0x2deea9fd23f637b197d6,0x6638f299c9956e8fbd23,0xca0428ce5a5b9d9973f4,0x5b3fe458e14d54119f3e],#[0xeccd1d1417b33b637b1c,0x9d9950c43fe46ce4c089,0xefaa48c3317676644d7b,0x5f4dec32b5b1b1ec7e43,0x98466a7950650ff2a0c8,0x7b08c847a4915a4c1f03,0x907b088ba5fae4247150,0x8e911a4a78501fec00c,0x660e60236c70226fe290,0xc1cc04526cbe26dec011,0x249a1fe0011efae3f313,0x1524b5f45a57b3128df8,0x4950bad0481febdf34ab,0xe01189e404197c5dd333,0x2011af308dbd280c9a3b,0x84a3c3af91426f4967d5,0xfbf9893c8da3d3a219a7,0xf10fec3220ce31fb2c08,0xf22e47441a3b3e232a0c,0xc496df83453334e0430,0x39c086b95c222e7648d6,0x7fe2c720f241ae924e04,0x4dfa217c8e480cd7e08f,0x61fccd0455f3eac411e7,0x368228f61cf1183cdf82,0xaf20ca6722603f861147,0x570862755103fca8324b,0xa0304527bcd318ebc112,0x30f04795c21853d44d3a,0x8bd0a4ad9666d18469eb,0x1117c0439b88441f7884,0xcc5517908926c61172f0],#[0x245d9038cd192e664c0f,0x87bec5bc047887063ae,0x61041d75e664d9c21afc,0x63e1157e04395ea8046a,0xa8393147cfd1115acd30,0x21ae762118f492177a18,0xc6a8e22b0163841073e8,0xb59b0f843265829f410,0xc40923fc8d808c9a720,0xb034cb86ab07c1214a9f,0x64f28a55c6c75c34c6df,0x50a3a9a728a3afc09166,0xf193bb231f76463df953,0x718cd22d1e433489b4e3,0x53f150a3253e319a4499,0x304755d4133f70510566,0x30447d5f3388bb9f1822,0x71c64247cfe8f8c831ea,0x257eb7c91b7d6618a32c,0x99463f21213d2236c719,0xe81334afd7c091a3cd2e,0x74e04195a9f602656978,0x4c64e7a2a1232f58032c,0xcf0a36a50cf1e06c71d6,0x34ecdb808f166a81e249,0x39320e4ff245df33f112,0x23c1325b9a2f10286ed3,0xe79e327e2248db3fc916,0x48dde44f4cbbe67b8891,0xaf4c7bed37e28dbe67be,0xb7ccfc448c3a4fc448e1,0x72631fea244aedc9d899],#[0x16be0aa8cad97982656e,0x181b207d36db3289ccd5,0xfe38ca9033e7a3304cd9,0x3f898c2317951190d224,0x4e2b2e1e287a2a69a63d,0x16ea898660c0a5ed973b,0xca19f3db2b966640fac6,0x238570550c99c9b924b,0x7aa2c7e04d6519c653de,0x5d13113c486f93318c4d,0x3931c3374c84189cf845,0xba51ef278fc0598c33b7,0x978c2c0671ff81864248,0x227f980f51b3366c997b,0x37544c3e10f7eb4271c1,0x317ab56c85d8b0988679,0x92c3acd74b311a4a78e1,0xc9df5c8e3fe6175d9b9a,0xff224eb003434bc5b248,0x36803c4a908e3f5a045e,0x7591f965f476fc8c0191,0xb21975ad28899ec29dd2,0x5e1f7c91cbf396b3330f,0xa7a2d328ef51f245a42f,0x28cd99e68c999522eca5,0xf47b88238ff1044cac3b,0x81ff818642481fad0228,0x5c4ead0a092b63e68504,0x8e482900438e40f71048,0xeb30ea498724148021ad,0x3187a297587461997a3,0xd265cbc044ac0f1d0267],#[0x1045d1bbf28e83297e50,0xfc8c9e1d6a8cbbdb1449,0x3df021ec2ee2e8d22b5e,0x7460be0e11767087be04,0x37431f8d6e4c51f2c675,0x458c38f5997604f9177,0x4063cbaf25c7a489fbdf,0x10e18b0418d50f4e23c7,0x6a4a34488f6089e24ef8,0x7a47afa1640ca9e50e9,0x495e8a94ba0714bdf980,0x813346528e32ad371730,0x98cba698e1e00c1b73be,0x8dbb458c311c7419bbec,0x881f2ca192ad0d8ead0d,0x18655ca14f05728b8770,0x93cdbc91a1826561221d,0x69c7e3257d918cb5968c,0x2481960cb5e8d9252c13,0x1c74196134d3267c7a33,0x18e9b38cd2463207d1eb,0x3b28ed9698c31e9450cc,0x3279ecc6abeb1246c363,0xbc5a32a779a320c3ef92,0x6645c4ebc411c3cd18f2,0x682845d03f71048cf0cf,0xe7f5780650cb013d965f,0x9dd24c81fbcd3276c1b1,0xfcad631920a5443a30ca,0xc23d17bd6630f4a6032a,0x5e21cfd2c3c8c10d8a7c,0xef99b24af94b0a7d8923],#[0x59bfa9c8bb8c41146b77,0x8b23327f601b20fd0c24,0x3459b0c77e156c49887e,0x660947c75e90624169db,0x8e329ccc128eb983118e,0xc63134e69352c6c69c32,0xf0ef552a69310f8e326a,0x8ca145276491fe440328,0xfd6991c7fed0551affe3,0xb7df1590a407c4e645e0,0x14330700f3227cb914cb,0x1c4b051e9d28a842f4b5,0x1c6f06236c4e44d9086b,0xc5a08a3ef4622ee31045,0x12fd6428d5ec8e9a47bf,0xee63e4fe1440338f0551,0x732078a632fb25143327,0xa2843a91b7ae58ccbdea,0xf3c2a4593b8a28456d8,0x1687995bfda2c9953f02,0x68a4fe341cf564e1a3c7,0xe1a43759ccb0ace39f38,0x8a00e681e91a8a39af10,0x8ddf9fc588039a3bf3fe,0x441c91bf5a922cf1e986,0xbce4c349ad6b8165c3f9,0xf402e1c903fa56046cbc,0x403f9041a40dfa5068c3,0x68461d7286a30bcd6342,0xeea08451c6e86a32fe29,0xe24a46b6a9bd084fe341,0xaf1be948e1d3db09967e],#[0x107be712523a7f22c645,0x309b9be212c99a1e028a,0x7e59322ffa3443473cf1,0x17fd1a21a3aadc514262,0x214227fe1801953d2019,0x1879e364c1e78b934307,0x3c5c99bf18164cb2d314,0x3065d70020c3cf1b260f,0x843df010f9e8a836e97e,0xad21c7fb0064df010d73,0xa2eb80106e018cf486b,0xeb5a82427f6108198739,0x1764dfe2d0459f090f4a,0x83efb100ca0f11a0eb89,0xa733093232c032cbd00,0x984ebcc0884637e65701,0x4c7ef0641aeb4877e5e1,0xe32ae005d51b6c5440f1,0x6bb743cfdaa9913f50c,0x8ad6a766913c760aa338,0xbbfb41546bcc23bcc235,0xd0084caf42065af09b0c,0x96572330fef031047803,0x812228f8867d8649347f,0x11c0f4191261e6241cff,0xd0249cd50ee81217f624,0x38c314d9f1d898bfb125,0x8c5fd892e9cec4d6fef,0xa28c93bd4ad8a349d477,0xd80799ab8611917e3ad7,0x185ff2e22af7fb445cf1,0xcfa333209ef83a2a5beb],#[0xa24ff02722ef64383d24,0x9cc89f82cc935c87be2c,0x9dba1964e43ae7ac690e,0xc24dcfa9a2b7dc512ca9,0x7818465efd128c9ee740,0xa6c46cf563205ff2e22e,0x51533b7432f170d8f7c7,0x998ec87258d29cc839c8,0x419a3caf80033169d393,0xacc8b8feb2d88e9f5287,0xf869b19646ff0791b03d,0x4a29c456f21a0c7e6438,0x7d20d02154ca39465c4f,0xfe9d076330e50ab6325d,0x71328e50cbe3815819bb,0x30e31998bae129ccd1da,0x8a582796333643c6648c,0x63908d7f8c13234e3e6c,0xd1108f5c84d05c755a26,0x453d173da4a4b4ed914c,0x21a0e57c723223ae3f0a,0x60b2a8cf1f0d06a8cd6f,0x4641fda224eba088d9f8,0xe07306248fe8222a7f66,0x1a246a9158f8282508e3,0x4194bac39088ceb5f9ac,0x56ca24c41f288126b1e5,0x9e4c8353f3d675b2192c,0x9c62840a5171d04a299f,0xb35167fad3a0b8292bd9,0x7213a381619652c12f9,0x1c11f5d891c3a731abcd],#[0x44fc16646fd479903c53,0xfe2b909aa87e228179a6,0x443cb1878a6358b188aa,0xd872a28a5f14c617b8a2,0x25c6a38fd0879dc0a1cc,0xd4848e91645bc108b31e,0x1a3cf8f901a8f3381d40,0x7c9868e91d22c8239ee6,0xe58c6bf7a112b963188f,0xf08fb0d1e3d9e21c167a,0xfc1f6860330fe7cc0230,0xa66531d468a23df3d868,0x68cf430aad8734e77c64,0x9f922d2019fb8741e40e,0x635163f98c94cdb58a89,0x5445d8d449efdc5455d7,0x522cab890881397255dc,0x77f83722d76b691656e4,0x191b4e3f190bfba0599,0xf8adf9247349c730915e,0x67c17971b8e905f9631c,0xf2db686033c7fbf328e6,0x97bbe9299475f86e468f,0x71c9868fbfcda1169a6c,0x346df0715177c18d45dc,0x51966de3930d197f8e4c,0x7461f89964ae314ac08e,0xc594498ea2f1460bf435,0x1237c64baa3478718f7,0xa1b22fe90e22ead7afce,0x5a2f18465efd128c9dd8,0x1cb30985f87460bfe5c4],#[0x571b2489bf95c47e6963,0x50cb43ec9149fee8a317,0x1032c3c19066cd2468fa,0x592101021e36c032771a,0xd9e200466ff54ac8cd0e,0x638e447eec8c7abf8045,0xe3d600664bf122e23aea,0x1aa649d643b9df7409eb,0x5a635f7240a36e4aa216,0xd3327e0b326dd6caa336,0x37551f61efd0a3657280,0xcc125af79897732b51f4,0x44d8faf10460ff24064b,0x8f8c7738245d7a2241ee,0x27071106869a09e2c838,0xc949b246f52d3237c0b3,0xf8de1194fc5428ddf288,0x655d9544143fddc11e60,0xc04acd19d832c9c5feca,0xf4743091e7fbb2217ca2,0xeb104651c0e9f0786254,0x6d48f68ccf31a2fe48ed,0x1cdfe8b88cb1d704e23e,0xd0b652db5f703339571b,0x5b6b8a03339379b1b07e,0xfe49795c649ce6ab56cc,0xd46ae65991359cd6ccc3,0x4a9bfe52e82033ee7417,0x76ff2f106ccd68ff5bb9,0xf6341c7b598f73a1b884,0xdb8f4232ef817eec23cb,0x8c9bbf09107e6d87e91]]
def p11 := limbs80 #[#[0x426f9331e7c7374652e3,0xa44df266351edf99187e,0x3996335c647799a93429,0x254eccbdf270b32f565f,0x63638d598db4d8be997a,0xcbdf270b328761a64a9,0x8c1963e310d943cf8e2f,0x241cc870e8e860429276,0x291ad081a377c008b6e9,0x24979d32119abec8c75c,0x34cd67e209847187f22e,0x94cc5e8ae9329a1a59f0,0xf7e851b2be7632a7816d,0xf32ccb3e643ae2ccc9b0,0x4e8e0011c6783f9494bc,0xf8eed91987321939ec68,0xd3990f3f46630f12064c,0x434886723e45cea8e4cc,0x65e6430feac8c8d6c366,0x2ccc89f82cc9c05f1ce6,0x6ac063d334ebc62646ae,0x6436fa1654666dac7e44,0x9f82cc85953581a675e,0x31e9450cc5c4357810d,0x18324d2cb99e8ed52f59,0x31cdd1957553c42478ed,0xf31ef197baf33a2c81a3,0x5d69908cc351e3f10474,0x4cb261e3e208c91d22c9,0x1340fabc645ae7ac61a7,0x1a36fa9c234688cb1cb6,0x670d19638da8d1963ee6],#[0x84065602df583868d07e,0x70c5476021e7cc916397,0xa0441f50223bd00839ea,0xc836ffb27b999aea463e,0xeef4020c47dcd151edd2,0x2229f2170d1c471b58a8,0x724066afcac901987f04,0x473d7d90423ceb21972c,0x51d7590d7cfb228122ea,0xa3a7d78064580e7ac1d1,0x521a7b748da669ea80e1,0xc3f4218d2e9ce3c6903e,0xa8ded252b421875231a8,0xe2532571a23059875238,0xcfb0deae1a40fb51a8bd,0x963af3a313357d12eac2,0xf18522e5210e1af0f05,0xd91899878fa228d1c7d9,0xde847c87c029b09a13e9,0x20fd086d2ec30b2ea95f,0xc3ee62a28fb91a8bb54a,0x11c7b50170d2071b51a8,0x7f54f3b31212b50ffb12,0xcf8df5bc0ccb217cc91f,0xd1bacdf81a63eda61a58,0x3965f494cb0cdd3211b2,0x464a48789322f77fe992,0x8c3293ece255fca423c7,0x650f44fcd1468b28710e,0x6aba82676f1a209e33ef,0x26cfd61234c71cdc4669,0x7b1969f02c4cc89b70d9],#[0x2813e472d138c0d33972,0x69dd265338fa6fa48c3f,0x97c5e0707224a4748b21,0x91fa49f224cc3e0f7091,0xd3a19c7dc1e4591a3c71,0xe32fa474ab8ccb31601c,0x6e23eda03afcd246e861,0xf9137427fac247dd2f8e,0x46c07cd0a38fc79222e2,0x958ff61dcc54b3cc3392,0x34cc2a7f268a3976cb4c,0x7c69236c3ea8f23d4630,0x3277493228e383911f45,0xfd6b5f49052abef0d243,0xb9f66c6da73e40a19e6b,0x9217f20484cd5fc3490c,0xb1cfe35422475ca15f71,0x48fa6c3267ca2132b6a1,0xcc6a899f3fe910994d62,0x29e423a129e423a112df,0x497d87bac270134c4f49,0x2d20019ab70f7d7862c,0x88927b0a7d21119ebf56,0x3f3282d2021a70d7f8e0,0xc912487e18464de33511,0xfe808098a434ef6fe7d,0x15f97614866972c08885,0xfdc7284d051f2da303ad,0xfc48b99d3870130d0496,0x443ceb2649c7fa891101,0x6ef22c5ebe22e236ff82,0x48cf8c64318931acffb7],#[0x6bad72d04ac279bada2,0x326c2d64513eb5db08ea,0xe4382940d870f32870a4,0xbfe259aaf2ec4982bc55,0x27c0169946199e064295,0xa47f03289286bc00e0a4,0xce7de44ee2a9d0521a36,0x659c9f8914aba645ec33,0xb70491ef1bc11a302c72,0xa28fca7bb2a14a58c671,0x67ac89f4a4170cc3c69a,0xdd8a194ccff2a49124d4,0x562626999fe2b104917d,0x8659e3e319bb2457d43c,0x171fe4c126b2649de1a4,0x7b26244e08d9760671d6,0xa19a7f1ac89197872414,0xe909967f1ac8919bc29b,0x1a2cf3d89fde81892bb6,0x5785219033a86c90110f,0xebf0602659e7efe0c124,0x8a2378ac8c1f88d01919,0xd1202c46fd04499f95e8,0x33424c03af11371ff365,0x264eff5004ca00ed78c,0xd1190cff8641092abe9,0xbd1328cfc84bd092447e,0x9c35400cc1fe00992b5e,0x1519975c544e4eb38499,0x63026700d2baa330471b,0xcef788e3f18a08a1e11d,0xa18c48d179fc1002484b],#[0x8011c6f0b8ee8493b5f0,0x21240f9bbdd09207e77e,0x3427e946c0d987d71d8,0xe00499931e88dc771b80,0x82931fd94a19778ee723,0x33843a70433eff410cc7,0x489fe042658846f5452,0x912257ab619271c48972,0xdd0a1a738610cb498907,0x2544a3e23b84939d4363,0x10770ae83328947c46de,0x2304b6d0a93f069a021b,0x7c0167f6e154b92b53c0,0xaadfc664c3e2beec8523,0xf6ed293d4fd664128606,0x471f15dd80602973e17b,0xbc724ace206983e23303,0xb2148cf3b733633ae50b,0x14acc0bdf76338f8afb,0x3f8b03640cfbff0e388b,0x5ff289192c2e3f888924,0xce9c71d99023da421997,0xfc61bd002597f8c91aa8,0x4134aff829afc7924ed1,0x518cbecf0a51dd3247b3,0xdb808bde1cbb19456dc4,0x197ae900198bd4460cb3,0xc48a66bf7150d092c934,0xa1f220a1f22571db8d8,0xfb9f979891c0b1f2ee33,0x942cff5122263d48bb8c,0xadd0a54e137846f4c0e5],#[0x1eefa2e304c34887774e,0x6690427a4ea8bac8d2a3,0x8f9c0659965e3c6845fc,0x1124eb8df11a7fa412ea,0x1e4691d0117e3f1204f8,0x338ff1bd008cda73d546,0x9277c86c24cc11e0abb1,0xfbe35f05e471ac144ac9,0x635e340a4b7ede1c00cc,0xb4c48671bff8340a38c5,0x5233fb22147121a6bd5,0x9a77a9f93051f54627f3,0x54596240d281e9ab4754,0x35911f687ccd64482fe5,0xf4438fa5692a88d1b9f3,0xd95c94cfab2dee57149d,0x910d5a065b1d98b14caf,0x850d3ead8648c34da155,0x718a8622b0756078266e,0x152883912be847b1fadf,0x32ee20728b1f7aa58cc3,0x730752a69bb0cf996358,0x91671a43f1f86a0a5034,0x71d049afe46d90298609,0xf0d0495ee3e208c966b8,0xea5489dbc3e209022ae3,0x60a5173d992a675a5daf,0x91b4bf5814290b2d8af3,0x85eb1eab89a10fa172c6,0x4fe084cd85fa130d30d1,0x1599b229b320a8e5113c,0xd73dc89bc6bc881c0b9],#[0xad50c8d5e0340b336e85,0x321cf721f7f0a4d01987,0xedcb320c53c78581256f,0xc88f5e9d01911bf64646,0x1d119136fd91937d7c3d,0x8cc58c7a90336fc2436e,0x4ccd8fd119919c3caf6c,0x2f6464ce11bb267c36d0,0xc456e09d19336fd9190b,0x1e22efa21ee0f1127b83,0xb9977d10d3aca20cb39b,0x55a2e1436d068ce5e9c2,0x9c1a334163dcc819d76b,0x7613c225f76f651973f8,0xdbf411bbb4a3a8ccb1f2,0xa261308cf14c6751987c,0x30f3a08dbf9d361f123b,0x93dd1b2320679a68f88d,0x200b7621a64fffa98144,0x334c7f0f67a23134076f,0x9fd8c948688f03c3a241,0x481aa592683848cd91be,0xf5652be7aa5b72aacc74,0x4af1fa56e7e939147185,0x4069b42ab221a473e819,0x7770c1909d2e7a176b03,0xcf34943034a7c9b1d286,0x434873c1115b571aa31,0x206aaf8c02c91cc3a493,0xcf4e8c6852fbea8ac10b,0x8645a5699e3e9432088,0x496f2a66194b91699866],#[0x22cfee1a092b21f1d1d0,0x73c1512b3e601589face,0x65589f8a9a06fdeeda31,0xa1fa369c6068efc86326,0x7926839a5c88ccbb1a13,0xa7eb309630348eee0457,0x10d1de1cc640ff2cc64e,0x2125d3f8488449568186,0xe24bfd8e240f88cf0a75,0x946b40928467af581240,0xa0995c7da508391a471e,0xe583d919a7faa2bc4187,0x73ebac92960f09f1c672,0x52d128884fd5a6bdb03f,0x6ff929912d1282a7c71a,0x77a6184cbbfee2e56248,0xa09987fbfd0c227a9126,0xf1e07874206286acf850,0xa5bd6dfc11f255b6460c,0xf6f02b32caa1c6be0314,0xe8e73348c1c623cc14ac,0x299acbd3305a489a0bf6,0x2dfab9c0915c76e36321,0xd5a3aa4d3b43c4755920,0xdcf5eb024794bc4440f4,0x8eeedc12b1e244184362,0x118596c7c332dc656ab1,0x54ed6142475f8b196bf8,0x79ea60ca3487daf32e29,0xbde7a232e7cf9c8db31,0xb06deb999a5ecaa1851a,0x2ab9190cdfa22e39e448],#[0x8c604b0fc55664ace3e6,0x2b2714271a42ff4a3f82,0xdb90e8c4ce947f0ddc09,0xa11e4c92b7b911e45484,0xccd3336d6233c0d1d687,0x629800d49f8c1a2b3343,0xd374291f7ba9448eda53,0xf8362a2fe362120e069d,0xf44accc51fd53335f9b4,0xe6493a7fadb63024e7ba,0x553bd40f3949490fc08f,0x81e7292b2f0635e7324a,0x1899773e217291d46317,0x1a11c4666cba034a2fa5,0x49925d695da81669c50f,0xc466693d22a62f887a5f,0x7680f901a66e6f8d08cb,0x22a527a2746a70342f50,0x3f6e648381a17ea608f4,0xc0d90033a63f6099059c,0x2903faae01789804cefe,0x43f0a761c0ce3f993395,0xe4d81c0068af3b9f06ca,0x43d76ea94cb9f52c64af,0x2994ba963203d14cb445,0x491f67050f7324b8d3f9,0x6b80de45499ff2578532,0xff07940f3e0a1b31292e,0x8e4c924c61ff078a43a1,0x91899d3ad1299475f19,0xf7f013e7f70400cd5e1c,0xdfe0552a99d6f8c08b53],#[0xfd83a0d66cfd83a154ce,0x4ff946e656ff02a8d66c,0xe84cfeb6e64cfd8b6e65,0x936ccf58694d3336bb58,0xa84069cfbd680ca152fb,0xe9f63d0ec48a95995774,0x22a5efe71c53a1b62454,0x178d042c6a9d7f5d0db8,0xeccdd36a9b01686fd9,0x85a80d00fd54d081e8ba,0x2034c4abfc4e047cca83,0xe61d84069bbe7da5cc3c,0x3e31c8db08454ddf3ed2,0x1b9e0c2cb9ed6b16334e,0x601679f5f8e2852f4c93,0x10ad0d0f334ccd5edcc2,0x9387fdae452919f7e305,0xf214084669dbc7b58152,0x66fd7f5d9b6221498ddb,0x40a992647ff0c6b641b2,0xf98280897a64a0bffc6b,0xdac67a64fc20b19c67c7,0xf0ae8594a49f1912c1fa,0xef59dc3a4b27a48d08d,0xe8419f08c9ccfa74bde9,0xcdf1a11bde8a7427bd14,0x2f048a9d3fdce5e6848d,0x4a66dcdf1a11b2f410ed,0x4a91e27cf122a497d836,0x3b9be34232f88ccd9783,0x1ec1129ae7f3e1e24109,0xa099b3bf6c94ccdf2ac1],#[0x22561678c7a78c8df2ae,0x8f43108454cee998d9be,0x58c611eaa3ac58d33ccf,0x77ca52433d3626c670e,0x6c8039a8707ea51667c7,0x92347ccb422c67aea919,0x9735db1d0204a6ad8f14,0x2b0b236bbfc646f7eeb1,0xe8ef0c9b3f711f583295,0xfe89e970571a27542c7d,0x8cb94b7e64ccd84c48ee,0x732c49b1bf3a67260ff7,0x7c1a8f9e9aa0594bf5a0,0xc8cc931bd31aa8167039,0x3f20e3a0894d387d5e19,0x9a84df8df5f77014c931,0x9fc67a996df40d4233a3,0x938112cc848dfea1d4cb,0x6e659790ce84cfeb6e64,0x6240674ff946e65cfd8b,0x3a73e966cbcaf4aee1f9,0x224b1ffe3932d0caac05,0xd226e66c611e75d08eac,0x9cccb43c2b4acd99097,0xe6f4a099e75d0e8a9892,0x2a8c8695f5dd37429263,0x7f8c56920bfe8bdfd021,0x625246cc798948f6274d,0xd19525b9a8dfc497873a,0xbf47349d9691364a5e3b,0x39c15aa0a35279cc68ca,0x941346fc7a8e422c951c],#[0x50a4b4f14443b2d75549,0x238ff0f35039223e5c8c,0xda6cc7dca9b32691e625,0xe2a6230e38c6635a0496,0xe7a28c5720688ea0c7b1,0x49df81110d70d2a7021,0xc1b0ebc1277a71e7d62,0x6666cb7f143372027642,0xd2ecea6088813530d29a,0x114b2f9ef8eec8ca5abf,0x95cbcc915a46e2e85542,0xafebc66bca52e864c4b4,0x108b14c434aaf5da3847,0x8a62d2e8f1815812d3d,0xccedcf74cca370722aa1,0x94b7a0cc4b490fcac09c,0x8eec8e4582733b9bdfd4,0x93770722b2053132f9bf,0x53c4b4a9ff5a052c6290,0x8e8486ef8d81967fd291,0x1247fc722c08f87f1c9,0xffd6218c4092bebcee09,0xc01330fe0eb1844096b,0x4e7189c070346f84652e,0xc1286979117d7951c252,0xb7e6bb7192279fdcf621,0xf5208a3cf8c47870c497,0x689839808d22381147,0x4124677b00478fc2de02,0x48dcf03080489da5cf5a,0xf2ab1cb892d73fb3f09c,0x6bbf1125b67e55099925],#[0x9d79b2678c38262f4973,0x34d42989abc5e4684f48,0x9094d029d959d78c53,0xdf4b5b8d084943af0fe4,0xb8c467124385b5d45468,0x48f18a1a15ea424c1fcc,0x59e5f921242cf0fe9002,0xc67ba6655d0d44bd4c4a,0xd702b893d95b4ed25334,0xfb8e65c62040e26ee31e,0x81daa5c90baf65e97240,0xce3fa4022c67396655f,0x886999a8834ea6f2e54c,0x5100340ff53f48047c38,0xa031b778895859c2bf90,0xca44cf1c356c02181a6b,0xfc1a1223fa61132861c8,0x40953c1fb0840252fa58,0x2fa983f0684a9fcd3d04,0x8ff157de00e0955d018c,0x7f20a20067ae95a51133,0x610200685f4b9c701a45,0xd12d2ebc5b498cce5fe4,0xf7480cd5d018d7e39b50,0x54e0435fc8fd9500939d,0x1f4d8a48cd3c1d884a92,0xcdb1ee08a1f48d240cc,0x21535f9a92033a7c6a2c,0xc610451eb1022e3e4020,0xb498fd280c91fa501907,0xff8c50fd8704aded4344,0xcfdf914d448c97784241],#[0x9c4f8b482457ce261033,0x181960fcd0459f169046,0x3f85a1819a0af144ef0c,0x3cbe18303357fceac195,0x2823a8e22262a6a16935,0x336fafbe848012478f85,0x4cd3b9c74c47ae01b81,0x42c718cf92004a6f0e9c,0xfc7be848012555679282,0x14c485f8c52c68a424c1,0x85fc8d0cd42909337a6a,0xbf13648233ed7cf32504,0x507d234903357a408194,0xc5001344cfaf88a8002,0x1a57da8ccd75500985f5,0x8f18a804ccff3c0fa808,0x530681c9aea889139b9c,0x4b5ef9e5d04126ba6662,0x91b5010346d472796a10,0x1b5010344f2756711c3e,0x24cf9b4116575a08b1f9,0xd45f7146d206be3be4c0,0xba3b94b0949d3cb08019,0xe40628e91bfdc9e450bf,0x9124628da30e1d78236f,0x3e735c8bbc23d7823c9b,0x9afce220479eaf38e08e,0x5685652832667deb4065,0xcda095b8ba1594a0a5ee,0x8c5f388812b3efe9668f,0x99a156e072fa3cf33630,0x654eb9860666e2719a6],#[0xe94149cfbd680ca1f9a4,0xf13811db9ee99976b188,0x92eb6e6351bd95a52af,0xac62b290c4adc5d0aca9,0x1c1937ea551fe6104ad,0x446fcc860033ceb408b5,0x2afffd0a6a11025eaff0,0x8cccf1fc481577953a03,0xf093333378564aca95c1,0xfe7343824f7e0101968b,0x4973e311e149489310f3,0xfea6e800ce92de542ebc,0x9e0095dd2220dd001a63,0xc4d1f442f1238ebc5e07,0xa658ecaccbc6299a7290,0x8e24cff92cd703e004b4,0x90b3da47c2481fcdbe0c,0x838554801a978cf5f25c,0xd7226e39a7c44f1253ca,0xb7fefc29823b3c2083dd,0x9008ccf0820f3e366359,0xcbdd331e744684acc3f5,0xc91f36c02181a03f30c0,0x7e089d97b0e0666fc74c,0x224f2a08120bfaec1917,0xc0cd5d018c6fccdf1a1,0x678f9b6010c0d19d73,0x64efe04c400cedefc362,0xa1a6670fcc303297a465,0x94b6065ae52d8196bc41,0x82651c4762a7a2d49a1f,0x964238fff8c027bffa3],#[0xd8e6232b5e008456bc01,0xf4d0e2334ee714a62408,0x6fa14114b5c578000d15,0xc8aaa41a2bcb81400034,0x330fd6402341c9e881fb,0xada9f192f08495fa02b8,0x251fcc19324c1c3ea147,0x2963ffc7265a1d8580a7,0x64f32464a4ee2e876160,0x616912eb6e6351bd95a5,0xae178cb5fabe326e2e87,0x1d17a1482f97d57319ab,0xc4951c4f532f253e322c,0x14cc3c2d226a4bcd5635,0x60e4371650d5371655e3,0x81f192b6a7c649be7564,0xc628c056eac9b1f9910a,0x64451c70ce760495b988,0x2b4d21e33816181a37bf,0x5dbc84ef3a15a7b2d54a,0xd2109d664ebe40449834,0x47073d15081fc1551963,0xdc1cd44fc4495b158be2,0x78a4eddcf48a17938a46,0xe224628529d328cf6437,0x94cc133576ea864cdbd9,0x41b3efdfbf186e124d7,0x2413de26bc9a696e3d21,0xe470a5c332fd73b181c1,0x1b22c467cc4688618432,0x12cbfa08427430351593,0xa5e0e770499c62998c1c]]
def p12 := limbs80 #[#[0x328d445f8ab420068d43,0xcc3350bef2522f0e4430,0xdc128bd2644641a29b10,0x91b464a45ec83a1da39,0xa4bc3910cea34967d28d,0x24e6039aa3343cb020c2,0xfd5a11aa8d3a2878f168,0xe08f5f62851ab9d46a2c,0x65af6e61300b3e5fed0f,0x22995f16e47acd1d1bc1,0x31570624cc30badb162,0x696cf8de7026c0d43f73,0xdf536068cf8dd005360,0xd819e3c1ba2a6c0d0d1e,0xc0d2ae1b320854ff4014,0xe17eb9db08e95f1d2630,0x62fdf5200933f5cf6008,0x9c697b2dc6738e7be0ad,0xf413430e44952c8d1a93,0xafcbcc8af57bf8abec30,0x5d21258919fe5047b273,0x11c0ca5afd04859fd39d,0x49ee9a73119828ffa14,0x5a39b50d1947e3bb43e5,0xdb1c3bc2095da53a59a1,0x24d4bfe39cd848f4adff,0x33e50491fe5648a5c2c4,0x20f0631c741fc08f33b2,0x22706d8e194b93711766,0x98bffe403f520094bcf4,0x999da1297fa82f4280e0,0xa843f5012083c18d755e],#[0xe4dc51b03421f8c0455f,0x5c641e0ca5eade8c3317,0xf9a6fb08ebf59b8b9091,0xa3c608194bfa051b0665,0x2f0704a8c7c75389181a,0x6622fc42e85a342fdeed,0x87948663f3824cfe4c20,0x557a188f9fc491819832,0x31dcac0095b1ade6232c,0x841840d4b647e4a0902b,0x11d7ce3bc94121397687,0x482fed42c819b575eeb4,0x1223c608195735fb250,0xc04a558ce40090ab19c8,0x174185ec206b5cc2135d,0x1244af904ac66809b1fe,0x8984b43e8242f680fd94,0x11e4d53e823d87bfe382,0x5c382415931b2281fa14,0x38257654e51a20d033f1,0x24cebc9f0e0913ea99ec,0xebf49b5a3afff9a9109e,0xe88b14c4346f280de8d3,0x5290e419c67e2b1c11d3,0x19e38244e3d9f0e091d9,0xd959e3f92212451a14fb,0x12275e4f90024569e65b,0x58e69e03bc4c9c7b3e94,0x8440f5b041975d0307be,0x24e346a0841c8e08b3ee,0x50d929273073e0463da0,0x802f0cc1f224c5668e1],#[0x4e1d6c3285f8dfc011f3,0x62a566825ac5e37f0048,0x227092f38decacb3feab,0x6815478fa0903fe399e0,0x3352c67ca091dfb99546,0xace8252ff2399e022709,0x76563af5912db32c124f,0x5397139866897fe38231,0x6491fec888121baa7819,0xadfe1781a0114a2febb0,0x341765635f7d32b8684,0x9b1f4a5a00cf9dbd82c3,0x36896d9378f5eb00c012,0xcb1f89d9866897fe3823,0x388b4227804d71f296c0,0xa4d7888b110bd0c484fe,0x277e94114478ed748012,0x8c477e255ff1eb04801,0x3f6030c9a3a38451f6d8,0x81730cc1c13573dc464a,0x4674bff1cb6300f89635,0x2fc251a123698f4f4019,0x4fff96c665e251713632,0xf3e1700e3581a652f111,0x36f4c1cd67ea8922f8c8,0x9ec62b0e8fabdfc13b18,0xc140d16aaf4962430368,0x290cb8986d8e3347a429,0x7d0a10299412f08cb10f,0xa2fed88740229a77126d,0xff5616123782dbfe5544,0x4a297b19bfe488512b08],#[0x5d0b842414d1e0917fa1,0xc238930fe481d44b1c73,0x514c9baf53a08e3fdb54,0xb5d7ce6a4c432c9af8a,0xbcafb20a617b8162d9a2,0x1219db908c8bc33ec4b0,0x52bc448fc3acc91087d1,0x9412b78966b8844ec4d,0x83acf023914a50d2e39f,0xe16949fd400a9758890d,0x93567e4973090354fa24,0x28a666dfe6f12ebd6641,0xfc6a6658c726a059bb9f,0x100b9247317fae93927b,0x24afd3220ce5c8a35fea,0x99e391046ca3dff82017,0x9012fa880667cfae2041,0x563139074491efad615c,0x818a5fc7b4480d7d9919,0xcfdaaaa0494bfc45c6c4,0xa08250d6efdcf39227,0xf1154f9e7a09c9297fcf,0x939c10b2f014d88d6154,0xfa820508266a8af03f68,0x29b11b03e178b651cc7,0x6df8ad082b48cf98b88e,0x8e49873ab2ce195f3956,0xbb5f0260c4c5fc19438,0x412a0e147f1409d89907,0x1907fcd3625e11fcf00c,0x3f43224369d2c3206783,0x12c62237bfa4189796be],#[0x6b4e908ce3111303fa19,0x2587b4444435a4103631,0x719c4846a1b3dc570bc2,0xd33c6c63a27844b0f62d,0x7bfd041243d8b5a7c908,0x7f8d111b9f1306268d63,0x5f5eacd894de9e081198,0x49c8cf50e08bc903408b,0x929d69215d0c81a93cbd,0x8c3c103405e07c71318,0x2ad1c12b3cb09282cf58,0x64bdbeb8347152571fae,0x1cff84ada40ffca84884,0x189c51a507840232cd3,0x69cd236faf6c85c9387e,0x232687c288294ce977e2,0x8990b68e3ebd7f6b1840,0x6519c631fa24c8514b1f,0x60963fdb5288486d3a59,0xfe0a1a2a899287e17804,0xb005aca97ebc4608f07b,0x80aa50c73e40e24d263,0x5a155b1f9714c18c7f85,0xd9f200d199329e0c9b8,0x742bf8f6890b1ae20e89,0xc5c47014d88d6170f114,0xff1865c9027cc7f446ce,0x239b289ea78e2631247b,0x36fae05c8d2037a48dc6,0xf65a8259987f85c60b92,0x6f1e931db628a10a5eb1,0xc1158c326b51f43015c],#[0xc3e22832f42fe832d464,0xc9a1bcf41b276df88932,0xe985510a09a5a4dad678,0x27342547c558ac9c0d31,0x3e2a110442c6a1ff199d,0x5309973d2858cb26a512,0x642c71f1c611005a5bfd,0xb38fff824a92433e614,0x47f80bc2a92497f1284d,0x65a42aea511bfd36059,0x5995bf98c896b3cf1f88,0xa2684c23df059bb6fc2,0xb309e37aeb1a915808fb,0x842f6df60cb2b7eac566,0x157f7e82b0f1a4c3d84a,0x789a86e90e4c159e885a,0x65c00c850b6f0742117f,0x24cbafa90a125cda90a1,0x85624cdae824509da75e,0x7c0430f4fc11754cfd97,0xbe44496a7333bd08892f,0xccbcafe864bc494a3333,0x34f74df26658eba3106,0x498705008449794b1c03,0x305e0181aa7c4b3e3d81,0x21819c3ff49099539d8,0x5444cebdff734c8f99fd,0x8ceb942e23d8684e87a6,0x433071a7c132d6da59ad,0x2dd7d7c40308a5f740e1,0x6484fbe4cc8ef99d142,0xacb84345e50927d36ffe],#[0x1fc44492bec4608d9646,0xed210ccbaff9448c9617,0x26ffa40266e73e890811,0xa21b86208cc5ff400065,0x6c1df20468aa413f6409,0xec04cf3ae8bffc002494,0x8006672fc6998ca0d965,0xb04265a5b868a85887e3,0x9105c9cff6249b0c48df,0xcacc7ac9844185e4dbd9,0xe38927bb8eab2e93913b,0x3ccdd1e940ccd3f8203f,0x20c51e71f75123461ee8,0xe74a2684c23c2ccccbca,0x4c91a8aace944d31a86,0x59474d4819c3e892b7ec,0x87a1eb5944928f909108,0x4b1f8198cbdfe81c9b19,0xffa5c50ccdfb01325ba2,0x12bfdb8246ff5aca2478,0x5b984892344af7ee0943,0x415723437236248f3c8d,0x44819f731e5b9c48efa1,0x348fa8fc93c209318758,0xcae86de25271a7aa4282,0x28267d9fec0984125791,0xd40286ac7891075f308,0xa07e3086a0452abfe49b,0xb0e334df7428b3fdd0c8,0x5a6782659fea2440fc82,0x5f48d10d1bafbe015291,0xceb63384291ba1436fb6],#[0x81ca2afb9c50829c08a6,0x8deb123ef133ae4291b8,0x9c638024411fc86479f7,0x48a47dd0a1d7c1318f1,0xcb82545e71502b8256ea,0x5d0660f87d1271f81cc2,0x9377c649de2300650f31,0x47dffe512288ac7f8144,0x45919862fda23211e274,0xca31713a23af443cfc7a,0x2573bf70400925f8cac8,0x3d1fd6c12405fc0ef609,0x1fd6c12381eb8f830492,0xde1741280fcfe0c1240f,0x44c81eba3f41267aeb98,0x8469e000cf500d2ba903,0x3fec12381ecdfc1824aa,0xec12381f263e0c12501f,0x47601980c5f90a3c1f3f,0x91df8040066a1f3096b9,0x1b39faa149039cfd544,0x34d9d57f804f1bd7892d,0x37034d8faf12657400cc,0xf9873b4997330e7ab2ee,0x45598218e6c9b5d2f688,0x96160d59a255c64cc35b,0xdba18e13731735c16939,0x2866af8b8640648a6e12,0xc36966edba426588655,0xf7a4049dd37ff61a3a65,0x24affe1dd40a0256cd75,0xbbde60301a366bafbd20],#[0xd147c70336cf1bd6351f,0xeb79492970a0baff9925,0x924ed1e2be480923b95e,0x6684f6df0330caff6b79,0xe91dad7b800d31f6ee0e,0xc623b2601292a9fdc1cc,0xa4c6a42e3fd293a2a48f,0xa48dbfd740b1a94b8ff4,0x7fa502c6a488e7eba4c6,0x1d7cd9571fe949c5485c,0x4e294493c0ec114a5471,0x7871c8c58d199ad1733,0x404b2f2e84c56655d4a2,0x7cb60a189a079f9f480a,0x87aa24366684d6ba533d,0x472e6598fc031e94a4a0,0x7511949518e2cc94cfdd,0x9297c7889d4949314afd,0xa7bc49fccb14f87f370a,0xf85cd7533c67d0790289,0x81e1496b2c372d121664,0x2417e26cc93dc8733dc8,0x97f1e8054933ffd46027,0xf858566daf9f62872491,0x951334c7e2c7a94924a1,0x8051533bc4c25ccc5ae9,0x6ddfc521292a6363fb1,0x3c292d6539309267b91,0x44b5ab3e536632fc4d99,0x619d0b55fac242690fd1,0x57af5745582991683780,0x5a856f2660b635e89994],#[0x6642d238c9496c6bf330,0xf4a20c12569db22c7e52,0xf2338efde2921092b7fc,0xce9c311efe912565e9e0,0x19f2fae88a5da3c64661,0x68efa4eb00cc585d30c8,0xc675b7fa22c70ba75420,0x220066af79a642e099ac,0xf44400cc3d6b804624ff,0xff3c401273db040066cf,0x4b8cccaf900034ca11,0x1fc3aea0998650caff7b,0x4c43bf89f8048517128b,0x415168dffd7ee8a82722,0xcf02983e205bd1b3e440,0xcfc892250cebd0038cd3,0x398a5d5273e004815868,0xc7f8e0c1246f7751349e,0xa2825369ae69f8391a57,0x8c2ec47480342f55e796,0x4bb1de00d12b71dff804,0x40200348179576006708,0xeb3197be456640fe59fe,0x68de678859bc030cfde1,0xe6611c7f2921092a0b29,0xee65eacade2d9a8bbb65,0xf890cedcf04ca1999beb,0xfa3aff87921baa4c5ad0,0xc91b179243314ac3e482,0x5ff4e86319217fd296a7,0xbfe1e486ea9316ab3e46,0x32f652f22652feca44ca],#[0x9ccad66b9e0a505bfb2b,0x465f9ffa6c12447d2864,0xd249bfcc63446df51cd0,0x8dbfcc634468f959192d,0xa943297ea50c887ed742,0xde0cd4c852ff51432947,0x8fa50ce38d4b35cf0528,0xd450491fffe9b048e12a,0xc89963caea09997ac3fa,0xbfc92866ef186cc91e0b,0xcdabe24488721f1219f9,0x6d9b1387aab2c7049766,0x23458e85caaca99d869,0xc07f4a032b7b080b28fc,0x427b703067e4f19e0033,0x2be17c0ca11df9980338,0x33f37f4064d7ea11a1,0x19e93db8dd00d09f19a3,0xc54cf2be0845aefc4d80,0x9983f80a6c2670fc116,0xb78211979c108a1fc017,0x7bed5aa654f40e900cc2,0xf33f7dab54ca94d25f99,0x4afae33460068ee4f90b,0x9b72664e82f4c89b7266,0xf41cca9e941ccba3cc88,0x75e1321786ba8c4cf10,0x2f0d751899cbcad2e133,0xcb4efa3b33b149893186,0x3ccb2afc9e4437aaa0fb,0x2ff6e4f4798fd6322a40,0x519641fc440a67dad956],#[0x8ba7e2222c780917ba6f,0x58232d7d56d999b0eba4,0xf2c3504cdde38b332e07,0x2fcd405099e7e41da464,0xb4070976b4cca2759946,0xebf6e8444921c9e3324a,0x876444d33d7f74222489,0xe3fd815fbe224951e05a,0x199a3e6899225c7c44cc,0x6f546eafeca9953c7aed,0x978a4d11e688ba669ae3,0x8a4d21e9a8274660ce9c,0x2877970c59338674e69b,0xe276fc341c2664d413a3,0xe13337f0507099ce1679,0x169afd2c324b1a33f5a0,0x7e8573242d11c383999c,0x9ac11899d2e7b06c1a4d,0x936184cf1fa26184cd5f,0xc1a6472e9bc4184d29e5,0xdcd6fe20559f28b82289,0xe0f498672cfd5f8502ac,0xd0559f57e2be6b3094a,0xd9b4a0f4da0d1acf9cb2,0xd35fd2ededa40ff21e69,0xe96e6634652cba64664c,0x1ee523c70287a9833af8,0x90d9a396ade4c0069cba,0x4926684aee98928236f5,0xe099be2704b9fbf592fd,0x37da4fc4e094b6ff224d,0xfded850b0cc19ecce2cd],#[0x433d7a5419134af12a0c,0xb8c265348906acf3c344,0xb191438886402853c196,0x64c240610dd4365a271e,0xde42ac8df08906515fb1,0x97db7920cabd0d42e8c,0xe1699ed1d7fd45c9a593,0x964c252e43cca369b4c9,0x6ca359dbe1120ca878b0,0x811268ad36f922668f14,0x21b2877f742933077e70,0x4852670eff88032867ef,0x583c848e3d7126508f8f,0x8448346432f4c0d96805,0xb215656f844832867f40,0x83f9c12223975aa133b7,0x79dfce090b6fd811a6f9,0xebdaaf1237072adaca35,0xfd04693f8488bdae5c48,0x994a6cadc33e40cb12af,0x7fc68232e438fb1a092d,0x25d7ef119bd717d4668a,0x6e3f1a08cdc1b4c2519e,0x91b13cb325671cea519e,0xbbce22b7da41900afddf,0xa1054f844af800cc19b7,0xd0832b7847420cc6ec84,0x8aab7308a9f6284d96b1,0x343091bfbd4308c06dd6,0x433b479e6d2696913cd9,0x984433e449ab7308d36,0x1564ce11fc9a5266c712],#[0x9499c03fb1564cc15f85,0x5010a9f6284d942bfc26,0x7312667fa92884cf8e2b,0xfe42cb7a925afde734cb,0x256f691d1e613721a17c,0xef0a08e353ce7a8da3ea,0xbf467b230d4f39ea30e3,0xf38b93336fa60fd46092,0x5218f8c83c4e66319486,0x86ca5ab7a3199aa418d9,0x991f7d307e28520232fc,0x33572ace4af1a37ceef1,0x7e4502e17b32d72c6da0,0x606cc0d857fa44cf3e4e,0x83089f48999df915bc86,0x232fb74899e2c4fc8a2b,0x9a2bd19903386b12c99c,0x5266af2306650e7c8019,0xc28cc1c6ca59330413c2,0xf33337b1c21206784fe2,0x7e7093d6f1434662a7b0,0x8d1b388b8c24cfa22b40,0x1998c0a99a7680f]]
def g63D8 := pages512 #[p6,p7,p8,p9,p10,p11,p12]
def g63H8 := limbs80 #[#[0x1f00006090c8600005,0x40010300014060a83000,0x1c020500814004400000,0x182c240f1000c1805020,0xa0003412030088800000,0xa0606004a4040080c000,0x420060209800000581c5,0x1442060600812010280,0x101c1216048340a100f,0x2008001e28018180001,0x400001182006029846c,0x100a190008c601a0400c,0x103e00008081801000,0x90000c020e0087000030,0xc0c0000c1e000480c001,0x8201b020042a17110007,0x500a0d0303406011e03,0x10480c100388402034e,0x10080080000008501404,0x2a000d0000291010dc0a,0x2412001201004070d86c,0x402032180600c141a038,0x704076150609c7c071,0x2130382c0c0f24924020,0x4001e1703c0e07000140,0x803c4c00000021f0102,0x6c0a000b0000a2c00,0x10484c681105000040c,0x4e442a0e80a170300000,0x60a03000127502000,0xa400000083c2c01108,0x20700814060289804060],#[0x2008340a061200c420,0x4500b308301c53130000,0x484c0903840200f0000,0x1500c004f4000cf81e2f,0x10399016180b0701203,0x12260709c84030390014,0xfc4002070b8120003024,0x9830064d0381800000c2,0x70000ca20b020ac28150,0xc1b0587c280903010260,0x3009038591a19218780,0x4c1601028ec20320400,0x120388800040282a0803,0x5048f0dc062684c000d,0x4a40a0cc402a0180c04,0x380803050001e3b0c9f4,0xa084120b1a0205c11028,0x5012080611258006c000,0x84a0182c76040b800242,0x8b6c3330000408008102,0x884c2c023bc56610980,0x182d0001a0a1bc181f37,0x1802a880218038185402,0x6e0007c02051601112,0x14003500808087842810,0x18081811010000434018,0xc2c80c16640485014010,0xa090b01402010d010383,0x386e650780600198440,0x840fe11418b43eb30507,0x10280a0d000e4640100,0x9d146c13078200601],#[0x67040642a020099c04,0x8b6f73300004c73810c,0x4118080b1c014601d578,0xa17184380f1100802490,0x230080802370081cbc0,0x4140417841b208091ec0,0x1284c0236b201c070300,0x7b8207000a9800041804,0x1c0004804390400d2fa9,0x1e0c0584d1c0d3541800,0x10063984c0000041cc,0x68306c07398540e0f057,0xa070c2f8060100000421,0x6198b040088500000025,0xcf200080180602059a40,0x9fc0e296380c6e020509,0x8bb3e4dd8967c389e54a,0x4b8f79698c9939cd31b5,0x22ac80000473fcd36a0f,0x52d334c16d4b3c74f0f6,0x486b41d60000,0xba3cb1bbc025cc4f9e6,0x4a7ffb312bfc13fbc4ea,0x6ab1000003f3b0f4bae2,0x22f6ca5eba2fafe1815,0x537208d11b21e1b6bc49,0x70a880001bfc80000000,0x53fb000000001ce40000,0x64d5bc85496c89959093,0x8000000068b600006bdc,0xb814fa5e886bc15623f3,0xeac5a095e9d5d35fc22b],#[0x247ad540820394d2,0xb01ef1d8592678a5a03e,0x1c965c51ea95eb2b,0x32cd7003e33d349d74ae,0x6035538de3ef540c0000,0x99bd18275d2d0870e048,0x71c9d4fd136180005aed,0x897add6a0000392f8354,0x2c6919bedcb8814b0c40,0x6c08c3a800007b8d0201,0x11ddab6204e50376f369,0x4a7a60f5b2f4f494db5c,0xa4d269dd7d62203d580b,0xa36e8c5b5530f25c5d67,0x58e2501f6aa7c1866b24,0x63f65a768cce8bb70c78,0x926c0bad34c3040e0000,0x12ca0000305e427a9a71,0xe4f2ed3f800044e4d08e,0xc9cf0c7122406305accc,0xe830e961133680004a0e,0x398c5323a84894c0345b,0x9af3127e04e08cfdcad5,0x9280456030b280004a5a,0xf2b518ba345dd9ece2b8,0x230fa8ff3bb7ccb0344b,0x40177bc000005b984301,0x293a531480e3c9f,0x109fb4538000250e4b82,0x8d2b31cad1ebabc3b4d7,0xf3748a21c849dc9c4120,0xab142cc60471c87dfbf9],#[0x70b383895c5e629641ed,0x651492bb00002b420881,0x71f08000000003858000,0x708afd50dcba19828000,0x88559459aada1ccd8000,0xfd727a8e6bf28000318f,0x7315bc5c800013e5395c,0xa283c4ff5bf964e10000,0x3c1c800059a7a984,0x15f0000497f80002936,0x59b610d20cc1599f,0x507c800069c7e145,0x70c9a09e3a8c80000000,0x418859d3543ce8ea9030,0x80003a429ce1abf4c4c2,0xc3087488993838fd52ca,0xc1dee17300002007241d,0xb0c4783c739f12e443ab,0x5b979153d563e83109e1,0x9bdda8c3530bb9ee0000,0xd0034909a168d36ffa8e,0x9f880007a094d07,0x121a80000000116d0000,0x610c8000000000cb,0x4898e08700000000,0x2325b6c834f18ae4341,0x800000004072208fdd6e,0x783581b18ca612a134e7,0x2beb0000028a62190000,0x804cbd5c00bdfb4cca17,0x7a11205163e90d2e41c5,0xf488456084bb02366d55],#[0x800000002a2a00007ccf,0x214daa4a504f7547e045,0xf1a77b2d800008e40000,0x290d6beada79,0x7c683ad101e78000,0x89b80004b9c9d4f0000,0x23873ce77b09e2ad9540,0x75643245e077308f,0x3affea2122a5607a4d0b,0xec001d53c2d0ebe46061,0x8000531cd53380003d2f,0xe294b11061b9800063b9,0x8000309acc62800031cf,0xd9cd9a6e124d1162d15d,0x2b32f4a2040700001c1e,0x599614b093bc62a76278,0x18f943e5d0712cf90000,0x7406dd5ef2c792283334,0xd4da0000000011cb8000,0xfcfb4c2c0d4300000d55,0x13d2a0a3018b800032b2,0x6b01e3a7f56f00000103,0x404000002a75d298c009,0xe8e080000000118b33e6,0xd82204251bc47a67f530,0x73ee11a652992cd04b73,0x37f00005af4152a2d22,0x15008000000040b24327,0x74cf0000792cf96c0000,0xd1c788488a7039d,0x746ef12e39e24b1a8000,0x78cbacc8ab0c00000000],#[0xc0afcbe3d8ef28648000,0x1c05e96e149b12890288,0x5ac68465dd017a4c8ba9,0x71cc72faf81b9282b82d,0x7aee20b1402b3ba8e36a,0x9cfedb37238b23d5e432,0xf81854e2c3701a50696b,0x4f88571b3fee266,0x80004906f1c400000000,0x453e4cda80007b578119,0x5c6a21f33cc468c58b1c,0x29185bb50000023198d0,0x80001cf03bf700006ac8,0x63e80f8b3561fdf931,0x40bd6244004e8c19ea61,0xc112b2056c4d405c5892,0x429288d42b4b82876103,0x7a1d8000682553be,0xbd1582605c12000040fb,0xcbd700003bc908f9,0x301d80003b7b8000,0xda1fad483cfcd3d9d9bf,0x29e3bb5574f7c328db64,0x61e869e9c2abba024044,0x15a013579f6000079af,0xfd49b480f2a4bafc18f1,0xea2418fe5a8b533724d6,0x7413ac1adb9880002abf,0xad35500c3b5ed4d15898,0x3dd48f1f168000002e4,0x58ac70a5055731d752c7,0x9a8b891631c5000063b1],#[0x800030a11c2944cb2bcc,0x7145d9f3aa20d889db19,0xbabe7181433e6d1a7259,0x51dc7bcf8d3cf1e4aa55,0x54a72b58c90b5521d482,0xd08190062dd0041,0x149e6366910e25171147,0x4a1a64d604ab64b4,0xa492f024800044118000,0x40de085f4ade,0x62cc3a14f24da26b5004,0x629b5143db632078445a,0x8880c1b529373a5a0069,0x74fe7b022bc8b870082c,0x9c566107fa1b9940a962,0x23c229c60989f042437f,0xcbf9c768b72cd2150ec,0xeba98a1605322d5c8000,0x922ccb5bdaef32c4395b,0x7a15e28c549343254c41,0x63b800006343700554c7,0x4513381980003cbac036,0x2b33a0a00006c03950f,0x4c632427c4b710a819de,0x9082022c4c7e785eeb52,0x5a392456c48c1254ab97,0xcb4d84eb51397d6cd4de,0xf515290d8429c810203d,0x10b7946abcd88105,0x34b14776a1e6091,0x339ea3fd700ee4488000,0x63fe08928537f25b2915],#[0x22439277bc7ca87452f6,0x392b035f688ebad28000,0xc0cc8bb61cb573283aff,0x59e04bdf44ad8be8eb48,0x8ca4aca282db851eea9a,0x8c5211713d7098f8e351,0xf0f3bc18a1777994cc0e,0x20dbb25f28b180001038,0xcc178157b95743750000,0xc178ed4be8d3a42bdc77,0xd48c3520b4372813e234,0x3d1f6942443280004088,0xe916e882ad3288d31aa9,0x8a52e16f8c986b4eeb5c,0x154498b081333a358b2a,0x1ca838d834fc15458000,0xda6d00db084b9c617210,0xfb75c9c3e135c4900c14,0x31d455301c07c394bc15,0x733b6b211c4c0839fad0,0x197b84c5c2bdca97b3c6,0x611d78e3ccafe30efbe7,0x3b1df378eccd5384,0x37cb08c7009d84aa30a,0xd460800052e28b380000,0xab1800005af0e2dfcb45,0x78e7e2ad7cec0c4f,0x80000000000000001169,0xdd6f9a45b9e080004352,0xb36700001c1b9c425827,0x800000000c87693bb496,0x38476c20445340c71873],#[0xcb3649f0606580002ae9,0xfb49cae6d2f7b03a6316,0x6b33bc1c49500000244c,0x7c61e392a4bf7b4a822d,0x2ea931545270a6f7d47,0x2c158000150189468000,0xd8a6996028bea3b36312,0x4c601513f4064232d2d9,0x8a1d1bff5b42a934aca1,0x6b7e3a29b81e0152d468,0x22f8349ec37a892010b0,0xb33e9caa4a417149c923,0xb30d784c453188df9a4a,0x7acbdb0500a270c038fe,0x18aa9b0888e17c0f0462,0x682f523f9bf012555271,0x21517028fc2d12e88000,0xdcce5974d384ab3af14c,0x34334cac4ca451d6fcbd,0xf53c60b82bfda26579c8,0x3093805351029a7b7af3,0xb199208b79609d68a9f8,0xc98cabd7ebb94b9b93aa,0xa20090669230ba2d22b6,0x3cdedbfff9822c28,0x9835445093d889eec8b,0x288d7a05e123ab391a70,0x937834c9203ba287e9f1,0x60d6b89d8d5f9a6babed,0x6bc30000725d14728000,0x1d057885000010845cb1,0xb251e4f78961bc1e596f],#[0x1d17c1080000b3cf4df,0xacea49218ab0813,0xcc4b000070c080000000,0x6c7633d831d2,0x8000297ef41b54f409c2,0x156b1b9a58c6085fe826,0x1383486d800024558000,0x202b800058c6c8b88000,0x1424a46731f2b30adc0d,0x9d5dd38aba685cc37454,0x8a22fac0ed207a0d3c8d,0x2d26738280002536e0c8,0x7aa2827550d5b812b8ea,0xfabc1820eb93cbd10c7d,0x12cf81c00000327d898e,0x189944b9ebe838495b9e,0x156e4facbf525231175,0xf983d22e51e8e9abc8cf,0x900bbbea2cd3b43b982e,0x9a3850ae99b74875ac58,0x2c2cdb04695e99fe640c,0x7341a022e51284346b40,0x6bca716402aaf421bb46,0x73aa69ed23263d28c95b,0x85568be302d1a2f769b3,0x1516c523fb1f14d9700a,0x750430793bceda2fb24b,0x53663573a020624c7045,0xd3a5529a83c0fd27a808,0x9aa07bf12c16a8cd703f,0x3ae84510cd02646388e9,0x8a4faaf93514124bac81],#[0xdaae3ade2aa3cc720a36,0x291afc0fc2e9eae0db02,0x24848408785dd35db1eb,0x64c633580b22a8b59a7f,0x62826bcab33122726862,0x12a515442ee8473023f,0xea281051a8687b8f8c36,0xa8ee7071ba515932cbb8,0xa4f6212d2067441f035a,0xdd114a917519e311533b,0x5a357330c212fa5f9099,0x452f993e2ac43b1e4bc,0xe4a0f832b03804b9a24f,0x5494354c7c355af05d74,0xf80178c14274b388c54e,0x7a61a3ce7d24701fc1a6,0xfad2349543d4d16e9d45,0xd0a2bac00497e99efc70,0x7bf4d36e529d24156343,0xf81b1cd1b9a1702113cc,0x5c35ec130c6512feb92d,0x6bd0f559bcf13d122184,0x50f4648f00007c2738ce,0xb44b3c4e02638d9b06f,0x1b1000004c4e72ba845d,0xd56d9d1d607300000000,0x6c946b4e52c200001815,0x22c188d4a8be38580000,0x7a262ad3a2c9524963d0,0x6b538a1269764b64253b,0x53ac656143d2000029ec,0x860c32d697a08f20000],#[0xe93130c943e25187c0cc,0xe11b84669aaf3b8cd042,0xb539c8e680001938e273,0xa9f44be0ba1913a6558,0xe1268c2ea29260f2b377,0xb01971a9e13e701080c1,0x8afd94aaa0c274471034,0x3cd7951928f6dafd1aa9,0xdcabe293496ad1bf8000,0x1331ac676806d9a42cfb,0x600a11a83a96e2fb,0xbb869ccb800074f4ba04,0x3c00940a3509ca9bd506,0x3a13206300004b148000,0x4d0c9cc4ad2532081bc1,0x93279a0a90e374160404,0x1c1278eb43fa3acb6b6b,0xb9889c6b69ab4d700000,0x7248f8df640b89d03825,0x1c22646c4c510a7bc43e,0x8280c43d0bef6362fcc5,0x388cbc93c965255d61aa,0x6ce3e2d7181ca2974a34,0x3467cd066d25d2c39117,0x9037e1aca8bf893053d3,0xacb78000000058ed513f,0x5b4f800030e894397b26,0x13af09b4c248544a9d67,0xa4c0fb078179915fb9e3,0xe1bb1928ebe1000012c4,0x438beb7091fb5256d3ee,0x82a6b81680007a67498d],#[0x4c8931dcbd2b9c194cee,0x3174583aaa16f0da8000,0x233647b0948d1944aa4,0x3bdecd1f98b691d96a85,0xa0dc92ea2ab1ab7b0000,0xd3c9b458147fa001ea10,0x3114d36980007281,0xd94468e1a115e01a82c5,0x92afb00d32ba1be99b80,0x940d9c95d8eeb0291191,0x23eba1e444dc120e0cff,0x22a5a1f9b8a60a0760d7,0x942e2542631e9a63f3a2,0x7d42a856d83333c2bd0f,0xad580a2ac489c4e313bd,0xd4834cc900001d297bc6,0x21aa72fc800000002cb5,0xbc7a219bb200087f7119,0x7bba80000c6ca8a384a7,0x10570000000034a5,0xd08300000c91446febbf,0x24c98000493aa1d25844,0x4c6980006a01d2289a3a,0x6ab4b3c7539080002b61,0x105544ef3b81417c88bc,0x3ba00002c360ae3,0x547ef3853356dce87197,0xd90200001cd4b8af497f,0x724272859b13949b,0xcc20f9665c4f00002a62,0x64f6bcd5031638c7,0x8247c223800000007955],#[0x94309b87ac600005955,0x724eabc8,0xa2b0a085abf7e1956090,0x301451ba6ad940f509c8,0x507601da80007bed0000,0xfd003b00d3de0225f417,0x2c9181d09bdcfab77bd1,0x8d11ed3bab6ad34a643b,0x7bf274096d35ec65d06e,0xe0e674f58cc3f8230000,0x4094380638a4e2998569,0x2b1b1bd931e5e05cc83b,0x49a500007a450000,0xc54a00007cf21394d82e,0xe8bbb42400a7800020ba,0x900b8e5223af437bbbd,0x59010000552ed06e,0x58ca3bf329b05adee875,0xd2f2d82f800013b08000,0xb1df612824797218b804,0xa185335d79639ae654b1,0xc43a7258f153231f922e,0x2077d2b21105537a1b06,0x4a690000230ccd63130b,0x21b7e54cca90b8ca8000,0xeacd8a41905d3c7bc537,0x39ad00004ae5f159d122,0x48cddc2b3096f87d2538,0x8000595afbdaa26d9032,0x5a900000193e8cad199a,0x80006c34800000000000,0x83223101a05bfbcb5391],#[0x531724f0893d2872e1f5,0xd5088c36c9706d033ace,0x143eb337c23e3d26b074,0xb485ce000860bb6fc80,0x12a0fb1a650c30e0,0xe936c33329bc902a0000,0xf56d6bf18b192980cc50,0x610f92f27a9dea1b3404,0xbc64c90c628adb507300,0x306aa1a3784e09cb1cae,0x33a3713c3ce5e97b347c,0x18549af9c10a5cdf3a23,0x2a3b899252f6811a5978,0x2b13645a90d8d2e0002c,0x540ac0ddc53da10aa4f6,0x216b64b63565e55a8000,0x9be2d0bb62571c970d56,0x20aa6186a20f82302423,0xec0140cebd59413244b0,0x6b03000049a1ab7e911e,0xdaa883f41aeb4a9191f5,0xa13ce9bdf05980342529,0xd27cc0d93a1ca83cd45f,0x62d8a811e16751669cc1,0xfa031d5262793b794393,0x5d03faa37a773d17,0x2478e36000005b9b21a2,0xaa0b6d18bab8486c8913,0x8b971b531d22d48cb365,0x2d1c800042d411aedb17,0x9b8e731d32d4c94f74db,0x42b45c55000062e7c207],#[0xe1d3e93b226af14a19ef,0x228d257311c4a9e2dc8a,0x4b0f00eb800029f9,0xb8b9487e49c0c9218000,0x7c098bbeb4b934ed71ee,0xbcdbd3e800033d6a959,0x93db3b7d1097a5619109,0xec837183a0,0x3d2c71b8c19809299d36,0x88f80d24c217bca8fa1f,0x406c4af52cfa6d18502d,0xa49c80005a59d29c20d5,0x14ee38e93a53644e,0x8000000000000000138a,0xca3a11c000074b4c83e,0x43f34413be0204a3b2b,0x5ae38c74000000004d44,0xdc9a9a84586d6acf0000,0x541859120000000050fa,0x2b5a190750da50fca111,0x1457000058f72423,0x800043cbcae1a1a49c1a,0x219c926c89b100001311,0xb9d98000540b10bf0000,0xc6413a0788bc843,0xe0e2a8b3000000006c59,0x78d1bbfaec8a14b28239,0x1831d3598adccbbf8000,0x8557800008fc2abea565,0xf89c4d5b62065b688d1d,0x9bb499add853fb87d086,0x9ca180004246000004bb],#[0xb0f0b39010abf39638c4,0x4904f554597dbb839422,0x800002e95a65943c6d10,0x6a156129000034a9a54d,0xb028695843236b5c0000,0x54cf4c706b32211e59df,0x62ec60f000006303fadc,0xa46e791da1c280002a3c,0x692aabb59a9f98022a5b,0x62ecb94a89f69539,0x80595a9e88117c8e71f7,0x8000010430ffbb5e6033,0x146694180002a26833d,0x355a188180006ce88c38,0x4b47b11b799c7ab59b99,0xd1b0dcf550d0c9ea445f,0xa3af826621bc69c7038e,0x53acd98a40578c44100c,0x4c499320b8e70000,0x707b7a5cb0e5d9f47c28,0x74b24a689c7df087d12f,0xb22b3b0962d87d6ee2c1,0x8ad23e098efcb0df32e,0xc85275417c87e4e6dba1,0xd1fc7d6a9a50e9db3430,0x12a869da44cc31a3f338,0x22d6d9c368c57ab3bb59,0x853f6005a93f588a409a,0x439c31eff43ab8dc250e,0x3037547f0b4d5861b288,0x311f12227b50e9eae55e,0xe4461840f37348a96d0a],#[0x485b7401a4dd3abbcb25,0x3c25cb2f63f5920c6553,0x8b34921c64ecd48470a0,0xa2fbe1ccea7e9ad7e253,0x7d1aeb5b104b2d497b77,0x3d3424e63329025df07c,0x792c1c81c3d45807bc10,0x42c2c972c07bf9894b6c,0x60d2fcbcfcacbb2fc4a9,0x6a293a09d83f79a94bd6,0xb92571e6d84358394351,0xa9cb164a95482275050,0xa374d2d81479c2f0000,0xf3bb000031f1a2eb8000,0x1482f06451b26d1b7ab7,0x5a0dc4c7e9badd0584f3,0x14dba99139fce2cc82e5,0x12942254456621fe819a,0x1498f97d7ca032389391,0x148d3379a81d1c39c4c4,0x19b4717780007227e94d,0xf14fc548db07437621b9,0x11f25a3eb85adb3f9a62,0x5546f1277c46d9a08c03,0xb3f6b9c6fc26eb4773b4,0xa4d9955bd219c52afa8d,0xb3dfac75a564dc611d41,0x532e7d6694eafcd812f1,0x26b0d528c4a1d717443,0xe2c8ad2ce07ebb6dc895,0x19065ab61846e091ec57,0xdc6d528f199e504dbcbd],#[0xebef805a7b81c4d0f444,0x1a70e249a94979398b35,0xf142dcc800a413ab0a64,0x534e083f094fad6604f,0x83a42c2a62eaf8fbbac3,0x323163e7c1631a60d802,0x8d28614492a20a983ae7,0x3c8f828ff94005461208,0xb8bcb396e1ac615d0000,0x9150941174d403cf74b3,0x436500007aefecf3c54e,0x395e5029800063b2aaed,0x8000212218886d02ecc5,0x8158e15c000052a1ac6d,0x58602b1880004211b92e,0x318e3cef8443a394581a,0x78e8000004a328fd8000,0xcb6f00000000000044b8,0x1165ba95617e20b4a9a5,0xd9e565683818ca0280b4,0xa18d8324000059d4e543,0x4199d09d00b9f49e64e9,0x80000190e50baa1ec475,0x83d25a44d3c180000b39,0x80006cd17ccaca526862,0xe367e4c2ec317c141924,0x1b1e6224a9e16b365ceb,0x219d4c9de1e7516a6247,0x1b885023bc8380000000,0xc111e0b519a29a560000,0xc35700000a6a786a01d8,0x2264f98adadf0bd55817],#[0xa4b6e345194100000000,0x44a6a069bb201bf8cb9a,0x8821c0dd000000000000,0x800011b3ac8631ca623d,0xe99b5bb219143c85c89c,0x54f1bc38a2250000402a,0x8c9f800002bf618f1b86,0x908909873c8e9aab2b63,0x8c2158368bf0e3c78a78,0xa1d20cf9be61ce6346,0xc4932878fbbbd93431d5,0x505435515a200000208d,0x637d98ace39f80000000,0x950955695551f879b1fd,0x641fac79fc5c60a9cb60,0x532c9d0d914e89790000,0x5213e4478000550d0866,0x6bcd41802a4e309b1bc5,0xca8330b72cc231bba865,0x6445b1fbbb3a0284b90e,0xab3c245eb84d00002d3d,0xb272f29e71720b953257,0x8000526f8b44587fc110,0x5b494b6d0cca00007d6b,0x1ce240d7b3a5c9b28000,0x6bdb9b80752f1a740000,0x800000004c02cbaddd16,0x7118aaaefb5bc2899240,0x3d72a8de800070804ce9,0x800000002a7300000000,0x635663a4e49080006cca,0x2a63442de23389dbe9fa],#[0x294cb192eb29d23c8000,0x697180007bc58000,0xc9f48000656293958000,0x82764486f058ecbee0c2,0x486fda146af8d3ec,0x4405000000000cc68000,0x80000975d06880000368,0x8000301c7bae73ec7196,0x49d1fb128d071176,0xf856123d643f80002c50,0x69c14a2db0165876a355,0x73333197d433f2a63ba6,0x80003090e3a6d3d3d924,0xf51ba371023b3c12dd3a,0x330442651e963408173,0xa36b5478fd38b01212aa,0x4d5f10cf800000000c31,0xd8f313e1ac66000038c8,0xe5330b2a0000314828c3,0xca6ef4af2246d1526bd8,0x9bb000007ac9acf71ad5,0x925e1c6be1216847f133,0x10ed943db3a76c2fa12b,0x7b99fc6f48528000,0x39faeb10e05000001108,0xb4998951dcb30adb110f,0xdd4d00419bda7d23e39d,0x5108dd747913,0xa3061808ea7c2b9260d6,0x800000005ab9000034ed,0x80001d1e000000003be4,0x300f0000220ba4b144d1],#[0x80001117f1a000000000,0x50243206800038f7,0x19ffab8c4970cd04a281,0x42ddf8a08243690bb37c,0x48ad8000000000000190,0x556c3af5a19d80004046,0xd11f8c42f218000032bd,0x1c4d80001d54a9c95bbc,0x243051c18998d1308000,0x987afc2aac8b800031ae,0xdb54e269d34c55500181,0xdb74000011279185dcc2,0x11a8a0fa189f450aaab9,0x19f78bf8717c21378000,0xcadac925e4f9e0972896,0x800000007a860000600d,0x2a37bc48199fbb2c094b,0x800031af80000000494e,0x79ce9b0e4a86c067a11c,0x3800544059d7c49a,0x3b04800000002abcc1ff,0x627d0000000034f8,0x40e4b16dcae113e68000,0xd2048000000062fa4b3f,0x41d5454d2580000154f,0x92f133ae953a69931ab0,0x7cdc]]
def g63D9 := limbs80 #[#[0x1485010c42100320c020,0x50941501214811015053,0x90a40882105515254550,0xcc321c825494e5294243,0xd4b51d4342d0740ccb31,0xefdfbf7efef6eede7f54,0x620c9620cd610ffffbf7,0x61182650c1650c6630ca,0x202a920282659016590d,0x62290622a5512a5412aa,0x63290632936229262291,0x65291652936429164292,0x63512625116252920513,0x61029200116551164512,0x65011640126301262011,0x422e1422d3612eb202d1,0x642d1642d2632d0632e2,0x6156b20553652d1652d3,0x65551645526355162551,0x63762427614275161751,0x65753647516475263750,0x62051620516105365751,0x627d1617d16505164052,0x647d1647de437d2627d1,0x620d1610d3657d1657d3,0x650d2630da430d2620d1,0x63353623506235361351,0x62591615936535165350,0x6359a435984359262591,0x62891618916559164592,0x61191658926389262891,0x63196531926219162191],#[0x61417514155141164192,0x54410634136241062413,0x62651616536441754415,0x63656536545365262651,0x61955519516565164652,0x54952639526295162951,0x63327213136031164955,0x65313643116431263310,0x637a7317916079365311,0x65793647916479263790,0x6281f328116081365791,0x65813648116481262811,0x42399423936039365811,0x6539063393623906239b,0x628d9428d1608d365391,0x60451658d2638d2628d1,0x62450624575245552453,0x54450634565345453453,0x52991609936445754455,0x63996539926299162995,0x61091600916499554992,0x65093640916409f32091,0x64851618516085365091,0x60113658516585364851,0x63112621194211161111,0x423d3613d3603d165112,0x605d3653d1653d0633da,0x645d2635db425d1615d1,0x6191160913655d1655d1,0x611d1601d16591263911,0x631d6531d2621d5521d1,0x6149360491641d5541d2],#[0x60693644906349652493,0x53694536975269161691,0x64697546955469263696,0x639d1619d1609d165691,0x621516115160151649d2,0x61611606116515262151,0x65611656126261162611,0x62211622116121160213,0x616d1606d16421554212,0x546d5546d2626d1626d1,0x622516125160251646d7,0x614d3604d26325262251,0x60710634d3624d0624d3,0x63712627116271161711,0x62a1161a1160a1165712,0x202ad2029263a1262a11,0x502af402ad402af302af,0x422af322ac322af502ad,0x522af422ae422ad422ac,0x622af522ae522ad522ac,0x432af622ae622ad622ac,0x632ae532ac532ae432ac,0x542ad542ac542ae632ac,0x642ad642ac642af542ae,0x652ad652ac652af642ae,0x4252f3252c3252f652ae,0x5252f4252e4252d4252c,0x4352f5252e5252d5252c,0x5452e5352c5352e4352c,0x2102f5452e5452d5452c,0x5102f4102d4102f3102d,0x4202d4202f3202f5102d],#[0x4302c4302f5202d5202f,0x5402c5402e5302c5302e,0x302ef202ef5402e5402d,0x502ed502ef402ed402ef,0x512ef412ed412ef312ef,0x422ec422ec322ef512ed,0x432ec432ee522ec522ee,0x542ec632ee532ec532ee,0x642ef542ee542ed542ec,0x3156f652ec652ef642ec,0x5156d5156f4156d4156f,0x5256e4256c4256c3256f,0x5356e4356c4356e5256c,0x5456d5456c5456e5356c,0x4076d4076f3076f5456e,0x3176d2176f5076d5076f,0x5176d5176f4176d4176f,0x4276d4276f3276d6176f,0x4376c4376f5276d5276f,0x5476e6376e5376c5376e,0x6476f5476e5476d5476c,0x2106e6576d6576e6476d,0x5106f4106d4106f2106d,0x4206d4206c4206f5106d,0x5206d5206c5206f4206e,0x5406d5406c5406f5206e,0x507ef407ed407ef5406e,0x417ef217ed217ef507ed,0x617ef517ed517ef417ed,0x427ee427ed427ec427ef,0x527ee527ed527ec527ef,0x547ec547ef627ec627ef],#[0x647ec647ef547ee547ed,0x210ed210ef657ec657ef,0x320ef510ed510ef310ef,0x520ed520ec520ef320ec,0x5036e530ec530ef520ee,0x3136f2136d2136f5036d,0x6136f5136d5136d4136f,0x4236f3236c3236f6136d,0x5236d5236c5236e4236d,0x6236d6236c6236f5236e,0x5336c5336e4336f6236e,0x5436d5436e6336c6336e,0x6536e6536d6536c6536f,0x415af315af215ad215af,0x325ac325af515ad515ad,0x525ac525ae425ad425af,0x535ae435af525ae525ad,0x508af545ad545ae535ac,0x318af218ad218af508ad,0x328ac328af518ad518af,0x528ae528ad528ac528af,0x211ad211ae538ac538af,0x321af411ad411af311af,0x421ad421ac421af321ac,0x2142e431ac431af421ae,0x4142d4142f3142f2142d,0x4242c4242f3242c3242f,0x6242c6242f4242e4242d,0x6442c6342e4342c4342f,0x3166f2166d2166f6442c,0x3266c3266f4166d4166f,0x4266e4266d4266c4266f],#[0x2196d2196e4366c4366f,0x3296f4196d4196f3196f,0x4296d4296c4296f3296c,0x6032e4396c4396f4296e,0x4232c4232c3232f6032c,0x4332c4332e5232c5232e,0x5432c6332e5332c5332e,0x6432f5432e5432d5432c,0x437af6532c6532f6432c,0x547ae537ac537ae437ac,0x6082f547ae547ad547ac,0x4282d4282c4282f6082c,0x5282d5282c5282f4282e,0x5482f6282c6282f5282e,0x6482f5482e5482d5482c,0x603af6582c6582f6482c,0x323af603ae603ad603ac,0x523ae423ad423af323ac,0x623af523ae523ad523ac,0x433af623ae623ad623ac,0x633ac633ae533ac533ae,0x653ac653af543ad543ae,0x328ec328ef653ae653ad,0x528ee528ed528ec528ef,0x6046c6046e538ec538ef,0x4246c4246f3246c3246f,0x6246c6246f4246e4246d,0x6446c6346e4346c4346f,0x429af329ac329af6446c,0x439af429ae429ad429ac,0x610ae600ad600ae439ac,0x520ad520af420ad420ad],#[0x540ae540ad540ac540af,0x650ad650ae640ad640af,0x4286c4286e6086d6086e,0x5486c5486e5286c5286e,0x6486d6486f5486e5486d,0x5212d5212e6586d6586e,0x603ec603ee5312c5312f,0x433ee523ec523ee423ef,0x543ec633ee533ec533ee,0x605ef653ec653ef543ed,0x525ed525ed615ee605ed,0x635ee535ec535ee435ef,0x655ed655ef545ed545ee,0x5392c5392e5292c5292e,0x604ac604ae431ec431ee,0x644ac634ae434ac434af,0x436ae606ad606af644ac,0x646ad646ae636ae436ac,0x6062c6062e439ec439ee,0x6162d6162f6062e6062d,0x6262e6262d6262c6262f,0x6562c6562f5462d5462f,0x606ed606ef6562e6562d,0x646ed646ee626ed626ee,0x624ec624ef604ec604ee,0x1b802000200002c634ef,0x284046807d00cc01480,0xd024c040c06f80cb015c,0xf901c9035a06440b9814,0xa5813e0260047008700,0x906800c7818102dd056c,0xfd03dc07860e701bf035],#[0x12082370456088010681,0x40a1a13d426984bb0932,0xd8859a0afe15782a3052,0x195c31c861f0bf017602,0x10e2e1bd836886a90d00,0xeb07b80f261de03ad873,0x223c4368843103e1ffc3,0x5125e243447788df1160,0xfc89da137626444b5095,0x2a7053f0a66148c28884,0x166e2c6c5788aca1566,0x20be417882e6c5b90b6,0x327063a0c50185c30506,0x51a86348867d0cd91978,0xfe8de51b96369c6c30d6,0x3a7073a0e4f1c74388c6,0x1e703c547818ee11d80,0x10fe71f943eb07c48f6,0x429c8459066209440948,0x72280449488410e4218c,0x111e5238c46848bc916,0x4ad894c927c24a048a89,0xa26b64cec98a12f925b0,0xd13fe27d24f149cd137,0x5340a59148e28ca50fca,0x32ac2551ca92150329bc,0xc160b2bd05718ad5158,0x5ad8b4d16742caa58c8b,0xa2ec25cfcb9116fe2dac,0x1918152fe65f14bd3178,0x6384c5d189130ee6130c,0x2331665a0c9f992131ec],#[0x2d9a37342467d4cea99b,0x6bb0d621ab2352869fcd,0x137366dd4da91b2f3612,0x351c5138527004df71bc,0x7438e759ccc39507204e,0xc3b267608eb69d4a3a48,0x1f9e1d3c0e778cee09da,0x7b00f509e803ce07944f,0x83ee87d38f929f0b3dd2,0x25a02d400c7f80fdf1f9,0x839d06620aa412281c50,0xb432c85cd0a8a12d420e,0x29a241443e87e10ec21b,0x8bcd16ca2b1450c89b51,0x9472e8de11aca330462e,0x30a447484e8ff91ee23b,0x93f5271a4c3494091ed2,0xb4b60961d2b4a5434a42,0x4226614c8c988d2ff25d,0x9c6937da6d94d7c9a813,0xe4f7c9e793bc27584e72,0x3fa85a5072a0613fca7d,0xa46d48028e75192a2a14,0xf5376a6714bca95d527c,0x3d2a505468a82d4fca9d,0xabf55712ac25546aa3d5,0x3571cadc95a92b385638,0x252c275806af895dfaba,0xb319658ac9058fcb1a56,0x35ac6b50d6922d0659c6,0x152e0a5bdcb7556d72d8,0xbc0d76b2eae5d00b9597],#[0x85f2abdbd7ac2f365e40,0x283025600abf897e7afa,0xc3f586930aa612ac1a58,0x3631ac5e18b1314f624c,0x29b2326422c7c18eab1a,0xcb89968b2b16540c9f59,0x36754ce119ae33306618,0x45b46e6892d0a5a0133d,0xd4b5a8934ee699ad2c1a,0x6b88d6a9ac6b5736aa2,0x31b63f6c42d831afa35e,0xdbf9b70b6c66d4ad9e5b,0x46f06dda9ba8b7366e36,0x2e383e7036dff9be9b7a,0xe475c7ab8ca7142e1fdc,0x473bce6f9cca3969727e,0x533a8474d2e931d15ba0,0xeda9da4bb2575eaeb0dd,0x6784aefdddebbbb97738,0x953d04799cf279e3b3c5,0xf70ded1bd837acaf521e,0x87cb2f8e9f0ebe007bca,0xaa3f2a7e0cfb89f583e8,0x89ffa3fca7f36fdedf,0x181c902da049c0728093,0xe7c1af832305a20a1c11,0xa6a13bc24e844507d60,0x986ad0cb2180c2df8569,0x12c40287bf0f021ccc37,0x132e250c47a88c3111e2,0x78b0d156a295c50c89d7,0x2f46348c1f17ca2e8c5b],#[0x1c0236ec6b78d3d1a123,0x38f151dc63ab473f8e4f,0x36c83a90251f8a3e2c7a,0x248e482c8dc916122324,0x793b326de4c8c9669295,0x524a8494cf29265134a0,0x2d46595cb1195cb2b2e5,0xd983d2fc25e14b9996eb,0x8c4cee999b32666314c3,0x37966dccd8c9ad334f26,0x29d4d39ea72d4e319c13,0xd04f6f9e7b3c9a7804ed,0x410a815d0029fc93efa7,0xda1d3433e854d088a0b3,0xdd519fa2f1458289b510,0x49a2922521da3fd47768,0x4a6094b9e961d2a7a517,0x1d3d8a76d4e1a9b2533,0x534ea585486a8b750c2a,0x7ab3155aeaa45521a9fd,0x395654ac4f581eaecd5b,0x5d0ab8856e7ad6d5a4eb,0x7afef5f5ebd8d78baed1,0x74d8cbb14161b6c1d581,0x6652cbdd94db255641ec,0x9b4a168b6d00d9d6b357,0x865ae7b58d6ac6d4d5a7,0x6e9adc2db65b6896c9ed,0x2b885708edfedbe0b785,0x835ce1b9817282e415c6,0x7652ebf5d64ba8974a6e,0xbbc757832ef65dd0bb6b],#[0x6e5ec6bd4b7a0ef36de5,0x7e16fb55f49be3b7c06f,0xdc063804aff75fccbf57,0x81e0e4c1798257037e04,0x86d30c8e16fc299849b0,0xdc52f89b31226218c3d5,0xa4e331c6338c13176e2b,0x901b1ed63a3c7038d8b1,0x5c9419213232e44dc867,0x9c6525ca2793bb26b64b,0x96f72c9e576cac9954b2,0xaccef996f317e605cbd3,0x84e6eccdaf9ae7351668,0x9e933c0e762ce819ca33,0xd06fa05b3fb67d8cf7f,0x78e8d6d183a27b43e685,0xa64b4bde964d28da46f4,0xfd455a83b4f5e9b9d34d,0x6e6abfd54da9ef529ea3,0xadc35aa6b33d633abef5,0x4d825afbf5e66bb2d721,0x5c6ca1d909b18b627ec3,0xb54769bed16d9fbb38b6,0x3000c1c136d3ed8adadd,0xc9039008c7c140a08183,0x60d089602050c4f04983,0xc9c6c5a1068651040890,0x82231304474043400482,0x870607a2d351d1a15142,0x1cc0c24845082393a361,0xa1245e318887d08958c1,0x51025c0923b019f48253],#[0xb3bab089164a493fb064,0x49fe3e840291f4ab408e,0x49042ef700167fd3c441,0x27fe8920153fb4c043ef,0x8adcfa5024f781b8a02c,0xac1915c7a4428efc6e20,0x41fe3cc4029bb328829d,0xe510a3be54093ecf9201,0xbb9ff00014ce41915f79,0xa0131f9d9900a5c7b500,0x299d4562467ebdc02176,0x77d6107b8c494e7fc000,0x127edc02145b28267880,0x21759041ff70024e7f00,0x67f42073ffe0209e6b12,0x2e720777e841087f0904,0x8a6f300c8a0e5fe00015,0x794c050efb0117bf0f50,0xf857280aeff8580a056f,0x3feb21141fec8ca0151c,0x20151fc504cefde58093,0x750c89d57cb8127ee43e,0x291fc24114fbe648051,0x9a0509785988c767c3e4,0xad91390cfad9a0577f85,0x884800128fdd6a4507fc,0x9a23b9fea012840dbf9,0x2a7388307fdc480523c4,0x507fa59020159f2f38a0,0xf289249ccc5028bf8010,0xe32a029b3ea0422a123c,0x53a495c7b500b7f42073],#[0x15d1f79cd02989d24a,0x70c00567d4b44e6cff65,0x577fe1ea002a5081cdcf,0xa0ffb1089cff302080,0x46c273edc0218814e794,0xfa320120be77b00a2f9e,0x149fdc1098bee010a277,0x827b3f2e8402ab9d880,0xfeb2413df99824517ff0,0x105bee540547fd648273,0x67e598914bfa103adce2,0xbfc3924510672429d84b,0x4ffa9400a6fefd72a8a6,0xc40c7efe680507ed010a,0x2f99c4100acf87a8014a,0xa0efb95014ef15c70412,0xb92304f3cd4a4534e620,0x8b396ca2151fdc91828,0xb8a4127fde141283fc56,0xa6230a8657eff8010f,0xdfea2045e18a0a29f7b1,0xcf4114a860d6729e080a,0x13e31459e66400245f3c,0x283f72fc40293ef2d040,0x24eec036540b4ff9e150,0xde1a0292fe2c849f7164,0x40ab6302228ff08111ae,0x92a051766510527ea3cd,0xfecc32822b363caa29bb,0xe52083c0921c9f300149,0xfdc8880547fafc40287d,0xfde182293ffb1941155],#[0x67cf3122818107fc0645,0x64d7fdc7509cf9f2824f,0x186040907ee489145e20,0xa29cbcaa293ddc6081f,0x473e52098c067df4c0,0x784300a763138236fa82,0x293e6960285f37045be,0xe245bd3f880293f31de4,0xb247a8155e9e88053377,0x824dee33227b98c0273f,0xa145fbcc5050bfe21584,0xffb0014120fd142623e8,0x2a3673fd00151fa224d3,0x47a002b1f1219c3fe000,0xfec998052f7bac041f9e,0xadff9820521ffa080a69,0x2931ff60813c5ed61247,0x3854055b5d61a04837f8,0x70247c48772ff0405367,0x98ff8f1d80a542077bc9,0x1051673fc041493e768,0x98608245ff8628283dff,0x1f0000240f27c000903f,0x23dfbf8e8014be6041ff,0x9ab82679bc038ffc0494,0x18effb444a2fbc326014,0x74b06dab8c0c8f3e8011,0x317e7a8229bcc9dc44a5,0x2f81da57c0f66237b08,0x40f7ffd5704f7e618914,0x8413ac40d6fb3411491f,0x8413dfbe9a09d88149fc],#[0xef2c051b3d7c900a8fdc,0x83fe43e20149fc504c77,0xa8f5b0340ab78cc0424,0x100a6f27f14273e9cc54,0xe9713dffba832293f21f,0xd27860141f9afd80504d,0x9be09ae43cc0283f3412,0x41e14e12455743960511,0x24527e7f14139f93a191,0xb2784f7fd5af828ae43e,0x44fefcc00a0cab958a42,0x49fae010b1031fbf8e01,0x58151fd27b9a02a783c0,0xffbc50503da80546ff1a,0x141befee608a4ecb8106,0x87d04513e80111ae74a1,0x93e69400a6fcc889149f,0x8a59e540523e4ec4804,0xef9992a0527db8046f04,0xde895f1f944f297e0491,0x1e1792941385e4094c4b,0xc53b5d50234af0304090,0x8e7e733038ca6ffd0ea1,0x4501fe18812995eb804,0x7d6e4023cfcc64433fb2,0xcc644bc1a90a09d4cc98,0x26aff3944c4fb3c5144f,0xab4c4a2ff3c51357cfca,0xa9f4b48463f440344acf,0x5b5da3580e3275f45ae0,0x489f4070234af58411a4,0x4a0f3730e90553271a20],#[0xe617c88b6ba2231f5720,0x360469f4a9408f572049,0x9e7d01d023e588f22ae2,0x6188b49981c6524ce338,0x14987f03502490b3826d,0xb625251fd11621926fd3,0xaf58d1293cd98a4f6aa4,0x918c9c99c7613d611327,0xc5263f0c8427de431169,0x4328f24cd28d6a425be5,0x936b68903faa02469c11,0xa1c46eec281fec9008eb,0x88a1ae0fc851833239a8,0xd458f438d252637e326d,0x3a5c0a8c4ce3b09c78c2,0x8bfba462305838c2188d,0xf0645bd8e12ef030bb44,0xf66f79422a112f5a464b,0xa7fca80acfd97de5a293,0xbc0e32a9db4f192490fd,0x52a3e0492bf4ca4d7efa,0xa81ccc4906e1096abbd0,0x98c877b7fc408a663218,0x9159be9a914179f12029,0x62281615af022f9fb40a,0x5e10f51248a71921ffab,0xf379e21149ffe9e2002a,0x812498c867ffb1c6029b,0x9981c6587c2125e1490f,0x1e61314a23c03321e6f0,0x8c547924c5281ff01023,0x9948f631c432387c2e73],#[0xb86c4e2a3291879e6293,0xd0e338ae7f404a91efc,0xc01cb520ffebd540a4fe,0xe5f34575f9edea02a9c,0x97c1a31fd7bb5a2933e4,0x52b3f4245b377c191488,0x25323e5ef0116de5f2a0,0x38ccc245bf5f1c628dae,0xb08a3feea205aff32412,0x891629a8640f9e513459,0x2cc50d6c4510ecc8f781,0xe04a768e1a4546fa7913,0xd0ca7145ff8c692815d5,0x9d02672d4e0529f4245b,0x8d225e77225b8f804d79,0x38b4fd0bec4f75f02558,0x73f225758c5877920d76,0xd142836224c6554de312,0xd901c8e526c4498caa9b,0xfd01202a493fec781914,0x4782c2394df9b1b2714e,0x7e60901524df9a7a1185,0x8bf5657273ccd8d938a8,0x4fbc2a4ba522fee9f182,0xce7a2019b3d14eca7ae,0x1c5a265f545d89a47d18,0xf7f045ee31619fa6037b,0x2d5e8a6a23d333599941,0xa2d31bd09efe7404de94,0x11006943119948d2211f,0xa46bf9b610e59160e72e,0x50f2b5d7804ca48188cc],#[0xefe6760e04c2d3cf7907,0x914443e34595b8570122,0xbe0b108ca108fa288b7e,0x7a2298c2708eb044788c,0x45132faa2819b3d140ce,0x8a8ef821bd8d16ec4dbf,0x3cd3659858cb6f26deb1,0x2a3b49dd429a137a042a,0x51a49c54a524e63e0cce,0x2a3f084ba1885a691e9c,0xe5b43f500b6ff48e640,0xa6fc6cc61548ed046949,0xa2ccbfc8208e3e341046,0xd9937c1688b6f3243eb1,0xd93008917e324b307196,0xc78dc213d9966e010ac7,0x91612659b9a533e64dc8,0xa8f93792a92b3f8bc89a,0x97f964f2147f57d9422,0x516537cc3c3910a832fa,0x9548b0f261f730155f22,0xc0a5232c7d45246b77c8,0xf7c421c9eeecfb8d148f,0xca3dc7130c299dc61a08,0x291fab038df3688ab2a0,0x8d4e74f5ca951ccbe3d5,0x1f109b0f8d408c3f1540,0x5a22c3f921f5884587f,0xc8b7ce49660e32c3e4df,0x679b24267edfc10485ce,0x83e4de4aa4aa2f226a45,0x3be072cae4247cb55044],#[0x2f22504952f16054c903,0x9d84b12d24c3c6360412,0x3f76061fa9041c4cb262,0x1a2d5bf2822ccfc8208e,0x2e326fc1a22bbce087c9,0xa697f6213dfa36598063,0xa6f31f0e348ae94e77a0,0x1c917cbbc135e6fec2a4,0x3f9c02abf298261c40b8,0xf65304f316442c245c25,0x8df8c5167b83be30161f,0x88a3fcb022ce08a19478,0xa2271ca8d0e338a077ce,0x1fb30e86115c19ce4b79,0x33949e3b3a80555db813,0x65324c915166a451e23,0x38ca8e7ce3eb8a2bde86,0xb82141f2e0427bf7e3c0,0x1617f7fe948c502e3fcc,0xba7260c14dfd7fc69306,0xaaf388c58aaf2efb8822,0x249cf063941fccfdc800,0xfa8b8888248eb8dd2c49,0xc70e90463397f128494e,0x2a3fe3c8263fafb59214,0x3dfe76b8a2abff3a1624,0xff85c10a2fdf9d00e32a,0x67fff3a231815c1e125b,0x8785eec2071e14d22509,0x88296a5a702cffbb71a2,0x1644a72529d24a7f9e5c,0x148479318a6ce78f9230],#[0x85c823ef4a08b7ebc236,0x334ac2abefbe89814af7,0xc7eece83ca34f4112fbe,0xb8e232eee24047bd3804,0xf74974e94ec6650461a8,0x8c35c28651cd24ba74a6,0x92c28e546e28e4f30ccc,0xff11258638b6d0a9a511,0x29c6b0a6fe4c960a38b6,0x2584f273ff81a01ac2cb,0xa62c48577f49b7c68aaf,0xca40957f936ec68aabff,0xa74a67cc8170e499e708,0x860475f4302e2c937496,0x3ab18a96cbf3d4866af5,0xeac40a6f361b96205972,0xfce335881607dfb44511,0xfe722ee20567df58c4f1,0x328e825c2f4615e0bd14,0x4937f9ef542e32b51a43,0xbfce668cb8cae6748654,0x52bc512851ef1d07a729,0x28d427abf1949fea854e,0xa43328e2bcbc48c2bdaa,0xeb1961f39fe8c5d42c51,0x8a7b9e8cbb0aaff339a0,0x3808e8e2bc17a28af05e,0xa8e4c02250af01d847ca,0x270893b2751364da8aba,0x71951ff8371d22a5d547,0x9237b580123df9c1e0,0xce0344aeac9094afc8ac],#[0x73794507becc527b6092,0x289cf37944d7ef2896cf,0x7746c149e24b8941ee6f,0x26d167649146a647427b,0x3997884f7cfcb84144c7,0x7d265188e046cf668065,0xdc3e3389f3d9a01943cc,0x935193ed2290e1e07194,0x55f35110fbeb609ef532,0x2bd0213ed649411e8f82,0x100528ce5e702d7f5182,0x338e0961d24429df91b4,0xc3b42943f6fb0c12eea0,0xe70437c5d63831dc5063,0x2f62140ffc05580a42f8,0x4e4b0cc3394d7a01273c,0x98129a48bbb0a6f8fba8,0x4af9b822976dea09b9c4,0xf149f3460e8547d10f41,0x989c3f5887f8a6f1710f,0xeafc6291ad5d428f68e7,0x52bf8c53318ba851ee5,0x7ced1c7140b8fa339814,0x33d00aafe6ea4e502bbe,0x4e924fd6257c8a8fe7a,0x27925dfbacbe051bd1a4,0xa24d450e720a24f800a8,0xa8651da8a209a8a208b8,0xce8305d4ec9a394370d,0x92c3e74eeea92abf1e7c,0x8b8a207ee24b1fc7166a,0xc450c7620515b86d4328],#[0x70c2957f806ac0ff193e,0xde551143f82066477032,0x8e557c91e260cc8c3323,0xa29ffab804c159fef680,0x984557f1cecc4150dd08,0x263dc0817e028a7f0e61,0x287179e51387ba250f5a,0x20e648f13eee2511b62,0x9d0c3e279d2f6011d56e,0x6e04a3bb0115ff4d6805,0x427a3bf632798cec91af,0xe54ca60aca5fc0e7df29,0xdcc0c39283e14f00a0f3,0x786a23955724864d88a1,0x3c28865be7ee0098557e,0xa2435a25d8a8895e218e,0x1b008e3f8d2ca088259b,0x78489fa05df813441e3,0xcbcd32e0557d3ed36453,0xb131197d8988b5a9f253,0xa68e35b9a26ae5a68db5,0xc7a81291abec789a6b49,0x5330a3794a4539e5c789,0xf7d4cc273dda998507bb,0xf7d4cc273bc097e53094,0xacd01206c5a2672a1590,0x651b26229590f261d9f,0x595c6422cd7b0889f481,0x83686be4c0455f3684]]
def g63H9 := limbs80 #[#[0x20c220006010401120a,0x7001a02030c0f230100,0xc0b002500010e002f0f,0x21b18000201000e0001,0x801030d040101040602,0x1c0d002001130c021703,0x2050118010801090504,0x2401051034040302051f,0x301135d00040e130354,0x360304040f0014012903,0x5011305310805020504,0x1c061c01050c0101,0x501010a01141e0505,0x60b0103001c0d030001,0x2d03192405084509020e,0x1070013001306100311,0x1000500001c1e140202,0x1b034003003116071813,0x1b020601261501240100,0x23000503000100180102,0x10007011a02000b2712,0x190103010202010406,0x1d000b1d000102350002,0x45401070412012c0d3d,0x22011b250008020016,0x212f100a79040d050f02,0x210b0027090510046000,0x10105030c2223110202,0x9050100024e02080103,0x31c0703000000101e02,0x30203111a1d21080a05,0xf060a01140705000203],#[0x1818010121060a000107,0x119110d0d0e0a021a,0x3050401340120050009,0x50608001e050f21050c,0x1809050e1004540e,0x1b0501160d1606020601,0x1201080023561d1a0205,0x9120006210306473209,0x200061600110a0f0504,0x104902000010022513,0xb064502180108001269,0x52c000e003f31000006,0xd0212290000010e030a,0x1000004080914384d01,0xb025b0202150401060f,0x10105062108000522,0x5080f01012704112700,0x6010c00101e4d120544,0x905024d030c0023000f,0xa082b040022170c0a0b,0x18110a151004010f121b,0x70a61031605042b5813,0x270a020a1919360003,0x120009350b0203000000,0x2f160c030007040d863a,0x10c0604010101188700,0x1d010118000601031a42,0x414d0a0e040104090001,0x71121208010619200104,0xf04030c07010e080022,0xc0c08040a030b06030e,0x6055c0d370008160202],#[0x30f0f0c191904331f,0x30907060204011f3121,0x12051001201d69032e2f,0x17120118012500025415,0x1d0609091d0a1b1c4b00,0x200170d04660b4a0004,0x166d00040401004d4803,0x90f38060b0a11790c00,0xc0109060d1465103500,0x82e1d20110e3303020f,0x260b11710c0009162d0a,0x130f091e8d2b13261600,0xf201010013027000c1e,0x5723e711042f02551200,0xf02010b010500972427,0xb000261106406050103,0x125e0c04790c01007922,0x3a1d0002193a20370413,0x6d100208010200000403,0x111c07fe25094d160500,0x2014a000004061d0421,0x52423c8bf6b71a4508,0x4c375a7c0000000000,0x700c200a717a00,0x65e089f45e29d711dc00,0xcb1728c391dc656ce6e7,0xe093e46209c84f4921a7,0x1a0bb6c19868b000047,0x1d7d303be96774ba3871,0xaccc3f5ccf7cc5000050,0xb3ac0451b0b14800003c,0xdc734a00000000635144],#[0xcef62b69b0eb213cc612,0x83581298fab803aa3317,0xa2f182f452597ef3412c,0xb8aa66a002d1ec3e25,0xf199db80fc0000994200,0xc5a843a797632a22b0,0x6500008414a537f10300,0x514ba5bde851238278,0x968a80001cf8a9f32e00,0x900005373e52dc354f7,0xcc02316a0cb3000015,0xe66767caa60000000000,0x7192925177c72386bfd6,0x63e1cb00007a2aaa3e32,0x1f6261000051dd4664fb,0x9fe013765b08840000c8,0x2e0000933100008501f7,0x3ea9c6e6a900003b3e94,0xd71abd000037626871b6,0x3d0000faa830f5a819f7,0xec389c12e5468044092b,0x9096d2050000e0c2d1,0x86c7524c0000000000,0x69e96d0c5fd4c1b2bd00,0x5df5e7b6abf062dab972,0x5286a645c97309c5d1c2,0x2d85523cf47c61ca0913,0x82245bf991004167c290,0xcadb2f803d056379fbcc,0xf7a623201419f7f31edb,0x582aa7f86ac5d69563,0xfcac4126de00000be500],#[0x140000cbae735f9b0fda,0x42a47d00000000e58c01,0x85e9780000717e000073,0xeaf5a48b2d08633858,0x2208a4888add000000,0x75ed2b0000f3e685cd00,0x2952b458d8c67dd45db8,0x9b3627a4b1a01ac7fba0,0x806d7bde299d7c,0xdf8bd400007640000000,0x936339387e5c9c1c318c,0xa9000000003bd6629dd6,0xfc91b38906000069e0a9,0x16aceb2340b617b0b887,0x976f54b6d701f8e771,0x5f12301cb08c69541c00,0x6e5b849d2151a6271af5,0x3863689c73e879836a37,0x418f6000000000000c9,0xd0581caaaad50320351,0xba9c2679498d6195a1,0xd5338900003731dce400,0xd9f05004ad00008d3b94,0x45e25e85f69a017927a6,0xea775f6cfc65797481a8,0x5aec4bc86331066754eb,0x7a5a569ae22313566a4,0x130895d6b9f87683f54c,0xd500007a0e855301bb76,0x24fad70000bc6c000089,0x4b784a586b9473940d9c,0xa4d63834517b52000029],#[0x33dfcaf642ceb1,0x1157e510f8f2793d4500,0x21603abfb17f9d91314,0x4b359ce54400007c0d63,0x90000000008a76000027,0xf377da75320000407209,0x1b00004773d92d0000e6,0x282c5c46aff90b414353,0x10547f0a171a5b20f4c4,0xf2e2560000000000000a,0x8f38ad0000370d94cd8a,0xe465d5000000000000c4,0xd3a4f508400000000010,0x860999e8b256ba2bb967,0xca403fca2e5518cb406b,0xe71a2b3efa4e215a798,0xa74fe784e450bb3f45,0xd34a2d895f0000000000,0xd6b1b5354d0b559ae319,0x6d00000d2280e3402ccc,0x7a0000499e4608a3f478,0x9409f5e1b900000000b3,0x5200007636658887ff83,0x3c77f30000121d00000c,0xb12a8e19b80000721b68,0x6b495eb9805698e88d4a,0xf236ae5a4686ac607f3a,0xd60a640000746246f6d3,0x81b863fa00000a3d17,0x3a1263183f6d4f59b900,0x3e7c06fc27a90258cfc8,0x724a110000983d00eee9],#[0x856d68d0737e67edfb,0xa3000032f2e969f08f00,0x5ed27a3980000d6fc41,0x975d3e1990252000084,0xba863542b000000000e0,0xc66291b3764c0195cb3,0xe9580a5bb10000f67517,0xf31ade31df0171d750a6,0xf65140e27ba804f012b5,0x4241515a932b951247f4,0x242ff5,0xe9d58e0000c78d5c3300,0xee63f80000178b4cc8e2,0x39ad8a075b38ac4f4c,0xf06ad4469b746000000,0x223b8595400004c8a77,0xa049a553e78687000085,0x415b0900009b2e578aec,0x82750d587fd8cb05b50b,0x5900001185b416726d6a,0xc83b4820faf9051bc47a,0x28c7c550c778ee000067,0xf9e7cfabb549ded75306,0x400239c5ab4079416e70,0x2ecbbce0c63ad1c3156c,0x9fa0f7000006df4b0858,0x6dc170792bf08320400c,0x383ef5e8f833bbbb17,0x7cbbf81b44230e000000,0x197799283308000030,0x4d0000c8e89ac9958400,0xd20bc300003c9a810ed8],#[0x3785dba28c,0x8a341321ee0000073400,0x6413fd0000c12f00002a,0xd26670000564f0000f8,0xb830b7efb89101e056,0x540770000c77ccbd700,0xfcd88093a4dcae000068,0xf045b299229a29464e83,0xc931a474da4c0000b0,0xa9e7fd000093d6c0d900,0x2bc7427016975125ab,0x1acc79ba4cddba7e00,0xae16e86752a0c0b89300,0x340110e1f80000aadb63,0x9f000053060000a10a25,0xf687bd5a173038cedf6,0x5a0000000000006571e0,0x27360772d1e1a8dfea,0x7b0000698fe8d60c5800,0x5900005d25ccbf000074,0x161ae60000f150000055,0xd57adc0000e458718337,0x27640000884241,0xc60000fa980000cb1200,0x36b6ee0000f7f5e169e7,0xf7ba8af175,0x2214ac000024bc228700,0x11e289decb5a46590,0x3a204a426c0000000000,0xf00000c0809217a9bcb4,0x9947b65dcb1f3bd9c,0xc3000099610000061200],#[0xf0000042ec067f5486ec,0x760000885febe3222cf1,0xed000050a6c8472c2295,0xd600009aae5c141917b5,0x2f5cb1c1bdc8765314a,0x43d0185745da749d52,0xe7b6b8ca810000220100,0xbbc12cea1bd8d4064690,0x13f1e52236887859c524,0x1c00000000b6c60000c2,0x3c00000bf1cd4a8016c2,0xf186b2660fab2ad44833,0x922d1aab580adfcca285,0xef45620000c233c121f5,0xc4000085fb0000891a90,0x5fda68ac89b80ce8ed03,0xc3e68500000d0d0000bb,0x19e50fc055642be6dd46,0x4ce372000054d8051441,0xa1e0cd0000f5def2ffac,0x513a54858cb406,0x25be00005b2cf4e700,0x3419cb00000000f24400,0xd63300007b5a0000db,0x4d2e9aad8596000000,0xe63fb0afa710000000,0x10b3000000,0x9c2300ced36bc79a00,0x4c395d20b1ea600600,0x797422cf000000,0x243e00000000a3ad00,0xa46a68200000000000],#[0x86010000000000,0x9700000000511b000000,0x1454e1b4185403a40b03,0xf9552787f200004982a7,0xbc3678abe280eac7a28,0xa38b9d48064b2ddb368a,0xe20000c9452c5bcae2c0,0xd3cc25fed0b50000a2,0x190000423c0000000000,0x17000058530000c624ad,0xcb02c300000b7c09da57,0xce82c50a6cf272f1e372,0x757992908ae0ea47eeba,0x1c25a4dd113548b0ebe7,0xb35b51519798a1623e33,0xa8c4e03826d5dca225f6,0x2d1713f943af000084,0xc096c848150577000000,0x90206ca17d9304f97057,0x63000050b914a6a57d60,0x515c51c2fdf3d8b2dfd1,0x1a6f0baea1257ec30fa,0xacbdbc4db42f86a62b8,0x19f037ea04c28c52a795,0x7a77fc26f49061d893,0x7ceb4c89075a84251a00,0xfa383200002b8520aef5,0xd3ea7a70967878ae27,0xab0000171169bbbc7c00,0x422549b99300007d42e7,0x9a428d1a1e16bc05e3ea,0x87000007038243414241],#[0x101a0284cf91af000083,0xa70000972202ca0000e5,0xfa8844ca7d0000c14147,0x3b15bc3c8dd828156b12,0x950000654c094e73a610,0x62c2bfbb01c777897b6a,0x78a77f89efa5fc650bc9,0x6deb53361abd1dca9940,0xb31ba5f036ead251bde6,0x6862f0902f5b74a80d93,0xdb98bc6967f94db267c7,0x8e8ca168709651706fa0,0x1df15a4152bd49fb10b8,0xb95533d18d9b20fd0013,0x1720108983044e6ac264,0x2ff4a2cc12db90e32100,0x73805f61d9d497d14512,0x3544ebaad5123da52632,0x28452201b605b8265ae7,0xa64524fcd3d5563d2b,0x440000b4bf7690ad0400,0xc56180000000081c360,0xe27ee44dbb98f8a685,0xeb25c4c1ad612345df45,0x5683a92a79ea54362f75,0x5813df6f7b28a90fbbc,0x9b043b33d3fbf0b33e71,0xd300000000c052612008,0xa6ea6cd379ed01,0x12f1418023f300,0x8a48d94fdc2d6d4600,0x9a25f47800],#[0x439b6b82b2bafb000000,0x127a0c000082068c5aeb,0x32fc7f0000000030dfe1,0x942303e3000000002a,0x56d5e118006d1393eb00,0x7a5807652ee1d266f4a5,0x6398680454ad9acc465,0x9a03fb8a907918d37d44,0x30d75cac1a36430d323a,0xc43c001100ed748a95,0xed259d0cc90652853d00,0x8bd6967c989b1b211d8b,0xe67b500000413800003a,0x7ee7c99baa0000000071,0x9f5b54167a7ae7f4e9eb,0xcd9291b0b133c139734a,0xf909ea0761f56eb4f3b3,0xc6cf58b6b7a18bb00a,0xe1c1660000973ce79200,0x8424aecbbfd076371dd3,0xfe2cd0f4c59a9d6c2152,0x61fcc00000d9a6b4ca32,0xa2399c51960000655556,0x33fc0f504900008632d2,0xf200000000451b2ae59b,0x1614ecd45f960c5a5625,0xb8eb5bb10700000000dd,0x85f53c228f000000006a,0xac00006c72f96054424a,0xceb707a1110676f8b079,0x4d000009fde91b259ec8,0xbd96d31d23b49ac944d3],#[0x27b85b,0xfeb472a3740000a31700,0xdb4e00000000f7bff6,0xa225c027e956a2923a00,0xd12684940802d8019447,0xd57a445a72a6d8c74049,0x7c000047db607bf56fb2,0x5332040000ccf20000b9,0x5b6bfa000007c30000aa,0xd0000052410000268d41,0x9199ca50f346cd0cbe67,0x66a7823bdc0000000050,0x4c770e549429cda31607,0xd79c47212be755694ac1,0xf2019735e15d8000022,0xdbf04600000000b38512,0xd87b1d0b5d9c86279105,0x1484d8c183c3000017,0xbe5038909dd8a447a400,0x2500001b5775e6253fb2,0x5e21861604b5c1ca2c76,0xa69cce352c891234be1c,0x7da682b8b84c0028683c,0xb03ce31d264d3db1a168,0xfe0000e2955b49aac746,0x5f67e61626b9f0467bca,0x45a334d175000091c11a,0xf1016833b5ca6f782f3b,0x62c15cabcf5517dc6e34,0x3a8fd14df1c61abb1b,0x6388703c45e424d200,0x3ff04cd0d607dd856100],#[0xac6bdc63b3d129a2733,0xb60000b39e1bf9f18153,0xc5ec340000c619c672c2,0x52413905943d41000076,0xcf002aa836ad4f3757a,0xc9d05c3b0ec02a7254bd,0xf4743437a8c3a133e2b9,0x7ab0913164a000004b,0xbc0000f776153b000000,0x4e00005396e0d472d34c,0xf215b057190000072088,0xe05600000000c68f84,0x4ec280000595d313700,0xc818d2213568600000c0,0xed1187c65954d107cdf5,0x179859912955fa47d1f3,0x31cd8329ca312d35e1,0xd32027504bfc4397bb00,0xda6699eb96000042ccc4,0x1cf93d8c8cd3f1c92a90,0x4a01b70000208d4996a7,0xade3bbe27aac843849dc,0xf188b289b704d691ab,0x89a2f36cd90eb27600,0x6e0a3c2d0f58a79acd00,0x3614c8dda18bab8b98,0x78b4c4264470e5943700,0xfe872b000009234b065c,0x243c96d77962d94b6cc0,0xc3686aa0a3665c34bc0,0xd40000d48767096a742b,0x4ce2e4130ff77ad0ec17],#[0x74a7a83620bdca3754,0x5c880328b3f0f9eb00,0xbaa595753968e5c09c00,0x75426600000000035768,0x344f00002be7b0,0xcc82d0851f6513000000,0x9980aa036383ce408619,0x99c920000069e500004b,0xba5cb89a24d379bba447,0x74b759f7a91d3820a8bb,0xc52b44f74be6a81346,0xbe000054da0000000000,0x6264000020c4d582d1,0x4e61890000372cd52500,0xa4a81db214811c683505,0xa3162c000000006c93ba,0x4b6253425f03070000db,0xbcf65b5c916433caf4,0x50000000057adf98b00,0x208a2f565087aa518e8d,0x2d0000000000003745fc,0xa027ac14af01aa2a3474,0x9392a92712000000005a,0xafc640000258f000035,0xf500007a948569b8c082,0xea410bc3d1a86fd9aae2,0xec396f82b879fa9c0cf4,0x2224297a65f7433cd4b5,0x92fa67000000007aee16,0x700005b9414a5671fc3,0xef00007bac1384c0e9f5,0xb19100001cfe02],#[0xbea435658b0657000000,0x8fb83b00000000b035d3,0x61000096b45b247c55a1,0xc20000abc100007aac14,0x95f800000000c15ffc,0x81c20000c808000000,0xa388c688634cb000000,0x3866d58093c62002abfc,0xf7915d000079ab496654,0x7e22dae67c89f8c46402,0x81935b6a63c85ef3c0e4,0x5c7ac807e208f17b6966,0x10e89739e2a682,0x786683e5578761ce00,0xb8d1000000008ca900,0x74fac1a4b236669a9600,0xa82cc130bac7785b9175,0x3a61d1645c36c9ea207c,0x2400d3aa7b3489706516,0xc6aa8601bcfd0e28c345,0x458d39b27c01c98c08f2,0x1238000090a7000002,0x5dd24b876a000016be00,0x136f46,0x57000026bba7d5a2a500,0xbbc90000dd370000c4,0xab34cec19faccce1ed00,0xa7017900006c5da71874,0x4a4b000000000000b9,0xa1d8566b0a0000f08100,0xb533c5b96b0c175498aa,0x8025780000332000002a],#[0x36008400000000048033,0x59e6181cf838d099e4,0xbdb53a64fd0000664d00,0xe4f01b4a1ac3386a18,0x424ada183102200b4600,0xa7f649f39de1fdf8dabc,0xa9c0082dd965c3994c,0xe121f49cd5a1eb681b00,0x78017468ec5d3e00573a,0xea8c538acaa84135ca9a,0x7f6a89c06ea4b8e89085,0x1536ff000059a1e8d79a,0xd900008146a769ca1c91,0xcd375bfa3a381e0000e8,0x364a360000ad44d79868,0x6240b2484c1647482c69,0x80eb26e8c467247be4a8,0xc45547e43032f912ea5b,0x8b199b820000121932,0x6500005162b0981c7000,0xfa716d89fe3c57c42161,0xfa680f362e1095c788c4,0x630000e417e1f703f6ea,0xd2a66c6a392b03e68a84,0x770738b5354d4c7554c9,0x360000a8acb38d1a8786,0xf32d14266812e03673ad,0x137bc6fba2510000d2,0x8fa6e3a83485739b689b,0xcc07e484ba47a53b8dcc,0x4642ebc5fd612e351d37,0xfd7a7102b3715598a3b4],#[0xce07564c68b1fe290940,0x9a22fb1737f7eb08bb85,0xaac6546b29fc1c2026a5,0xa8e6a5f92493cb250545,0xb3a915069b456a17c702,0x40da41a7e8e26e0d184a,0x1000041f9fc99000025,0x56e503b872ba5cf35613,0x610000173ef59fe44701,0xe57b30e05ce14cf7f3,0x55000086415343d05100,0x9d1ccb0000e5e2027fb4,0xd520e1d0b823f33a01,0x910000b7e18521b4b500,0x40abe83729f149fce0dc,0xeda5081a43a26b0000b4,0xc8f2992c92000084533a,0x8e00000000f1e93611eb,0x3fb897e0a2aaa51602a3,0x76000029e10000686797,0xc81889f6788bd47c01,0x4febc018cc000009c200,0x2a000043fee1e7ba0fd1,0xa4dccd153aab000004,0x4e1d4d3824fcc74bda00,0xf05a44b7f40a0000a0,0x6d9b718825b0c5e28500,0x4c2906f50000000044,0x1d000000000000fd0b00,0xd97a3f6abcc22ef5ac64,0x17b4fbead0dc0e24443b,0xdf729c7ce7dbf7cd2cf8],#[0x10eb60824606c2c4ee34,0x6fc92c83c7730d3c3c7c,0xcf05a9068842de82f4e2,0x2732fa0c11821ad03ea,0x45b8b4090d6b351948b4,0x346b56e9e4e63c5cb92c,0x2523b61af8221ee0cac9,0x489330b025e1d769f1b9,0x3708195767,0x441025414cfb94e400,0x360000691482ee095600,0xd64631777be20ee1ffcc,0x519bfe02ed8cbaa06694,0xa4014ae09e000015af89,0xc8e347306196ef2445f9,0x6cb600000000047a73,0x260420e9a368de58a500,0x4b70159b5d06c74274,0x5221f1d400,0x5749c60922c2000000,0xe1ba5d5cb2775ecb0d00,0xa3238362b90000448e28,0xd60000c76ccb8f84c8e4,0xb2cbf500000000038c42,0x71185433424fb79441,0x7000000005c3da69d00,0x4a3cd9d58aebb616faab,0x1b00009b2b4852504dd7,0xac7d43371b14bc2ef6,0xd8296e19a8b506000000,0xfeb4bd0000000025d4ec,0x93000040236237061567],#[0x701fe1f2c0c96c35fb,0x6fa72642c8b2b5874100,0x130cbb161abd20000fb,0xc12a60000017ec00000c,0x5928beea4df0e10000d2,0x1e005d0000708c566969,0x8b870000cb22a144b7,0x16aad78cf9bd000000,0xf5a300000000a24d00,0x1a2b15c18cf642000000,0x94fbc6798a5946517b31,0xcab52f780b108544a9f0,0x7f754fc6a8c0289008b6,0x5fbe000000000249beb,0x72d97a002a4b24af3,0xd5e21a9a88a14e77b300,0x71aca4849529f2aa2300,0x6a26d20000ac6261f623,0x19a1877b165290000cb,0xb7ca1d29dc4cca000049,0xb513ee9232fb1a262ad0,0xc50275741baa2b3b77c8,0x34336e00004d400c67d8,0xf0766234c2a6b19ca3f0,0x6649afc39341ae000075,0x97a5c6978e39337d31b3,0xa9b177ae0000d655bc,0x41922a91c70564434c00,0xe0d3cf40c8eaa78ab629,0x2ab585f896dc792c4d26,0xa22bf31ab7de1c6bb3,0x5875d7bc66000055a000],#[0x22d23bf99fec59593583,0x4503c6ea49155a000078,0x4862a064dd53817a6d5a,0xbe039c6a0db59785dd8c,0x1600000000abf3000009,0xbfb1c4d76099d0a37f8a,0xfd2469400000000041,0x6a33ff281a00007c2a00,0xe93b1c198e00000000c6,0xc1c37cf9c30000146baa,0xef0000000000000000f6,0xb8fc0000000000002b,0x2a3beb23da73a5000000,0x82000028270bddd0e22d,0xcb990c63ec0000fbd850,0x2e906811a74bcd00003b,0x34313f4d43000050bf87,0x82977e2802484831da61,0xf89ffbee010fe8,0xa58300,0xa7e8f2000049e3c61000,0xd479da58000000008b,0x246fc30cc55b00,0x690f05c2613200,0x59995098c600002b7800,0xed0000a64ce9e93ae072,0x82619b8c77e887118416,0x9a0988d2746861626292,0xdc70f67a050000ea3b58,0x33a24061ac0364c7582c,0x444888b3620000000011,0x28000e4345abfc0000ec],#[0x470113fc7e006903a3f5,0xa552bb0000861c60d7eb,0x54d987288f93c95a30a0,0x9b12232b3172a16b97a1,0x30726aa16ff637e34959,0x46f5167a57e0ff0b5e26,0xb7aa6ed06768b7326808,0xa022249ae46b8306db2a,0xae21fca780b95ba3b299,0xf8615eb5bfa001a44962,0x3b344199e2c235a7a3b6,0xd6a6a34491c56ce4c3a9,0x4e00000000ba73f003e6,0xaf0000000016630b041a,0x83e4d70000696354ef77,0xe4de00008c8504,0x379cb16b00,0x1b719ced1c688ad73b00,0x89593aec2bd1cfa5bbf7,0x277bd38926a8fee2d415,0x5c917f98100000065347,0xbf1ac000009bc208fb13,0x5883ac2cfa0000229368,0x8bf24e0000598c5c9d05,0xb62480000ab9eca7a82,0x1fe4cc1159f702739aeb,0x9d484b9a08a01060a4,0xa97837c567e930393700,0xcde68c7ce92b9f0000b0,0xebd50000582be2,0xfe64310000192ffb6400,0x66ecea71e8397ff85ae4],#[0x6923e0bbf695876c50eb,0xa00000000e0300000ba,0x3bb30000e616c3273d,0x35d0000081fb000000,0x9b73087c117c619300,0xd3508e320b7192fbc500,0x81b7c1352a809f34c9da,0x730000f5f5facb51c89b,0xd72aec6324843d703a60,0xaaf51eaa6a60d145ffc6,0x540acb10c540ed02e34,0x3431fa0000000061a07c,0x8e000090d2613c59e716,0x710033db1f9be163ab02,0x43f95329f9000009859c,0xb4d99ad5c5a4ed55b3f0,0x86565c70218482e41ad0,0xcc8a4ff7440cff7c9ef2,0x57d09ac5b1f79571b1f5,0x97902d4ebd09ccbbe1,0x9720205ac499ffeb8800,0xf5230b7419b45900009a,0xf000007904bd1ee11f41,0x7cf8d207000015ba48,0x9ce1de5be2d19857f000,0x24c901d47000000003b,0xcbab1d,0x378199e8e62100,0x1d3f99980000000000,0x8105cf000049c8f91900,0x6a745c30000000078,0x7a652341a951f378f8b7],#[0x876b00007b,0x27547000002721d9d400,0x8c7b06dabb39869cab,0xcf1a61000093448b3000,0x1f0000997924b0548d30,0xc9691ca9c4e8f4000096,0xa8631000008ab2000058,0x830000000069d88a19b3,0x58000000000000b6e148,0x48339523b13910000016,0x132a1294930000000080,0x51a80000935a67,0xb33261efd816000000,0x58d8ef14d02730c97d00,0x86d01eb21673a2000071,0x1de74c172f9598000063,0xd273d9806a7c38000026,0x51dc492b75e964fb6102,0x7642b7d2c700006a8d97,0xb982a365b6495861cc44,0xc3786a8c000017f4b7,0xe339d636b5a580f73a00,0xfd0000000018141ccd04,0xe8d3594ad8339ff47758,0x9800004b92007e58e6d2,0x7d69291bf219dd1d2fe8,0x67e6e40000438b955d10,0xc3e9b54b17a1,0x2ae5ef3b3acd101b5900,0xa60000110249320cdbc7,0xc0f9729660dae8b1ca35,0xe9b4969088f4668234a2],#[0xaf7326c454164868c783,0x3e5affc77d829ea468a8,0x89105bc26571a5513b31,0x5a493c75f9c42c95e067,0xb608b3760ecd3c9a9ef9,0x8100b0b949158d879726,0xd40000029834016a283c,0x8b2412000064a175e906,0x90c46e44f8117257c4c0,0x9d00003bb437934984e1,0x70c8f7db4f486cb24967,0xf462c992587cef7b4de5,0xdd0000dc1e415300005a,0x8ee57e8d01f854929452,0xdb4b186bb70d3ad694bb,0xb20c478f58e4360703,0xff4c3a33183c746c5400,0x944c607278c29a000044,0x7cad03906bdf48,0xc35d00004a92710800,0x994c1f26063424285c00,0xdaa316e536fd84,0xf30000eb67ca91000000,0x6d581120d0f889725ab9,0x2d4cb7370b000068d3ec,0xe78300000000000013,0x0,0xa0d5d660588053a91600,0x40ad809b00000000c0,0xb2f226ea55d9c1417300,0xd79ec3aa17bcf44a39,0x80d80000c96aed0700],#[0x5253232456265eed5282,0xd720cc7ba865911b7db9,0x77fc76000027dcd66b13,0xa27100a5d983b4b7b422,0x74000068ea000059b48a,0xc0e6291fda35e1c540,0xaf322d12100000000000,0x5bd1587af6f95cd7ea,0x4adb9b4d330000f00000,0x4732f699d94bd08c163a,0xf98a26c899e12d000067,0x57cd102aa07d2c427dc,0x3f333b5c32d4c63a0896,0x6c6178e3c25c2f33d414,0x923997b0f20000fcfd59,0x5e2260000014e6d8a8f4,0x6398b929cef49c54f470,0xbfa59096f20869b7b72c,0x9586e71b02ba15f4c799,0xb8c770875ae3330000dc,0xa90000959900001cf55b,0xf10000000000009229ea,0xe5d85de9fc0000502bdc,0xb34d510000ebbe48db85,0xde1cab0000a7bdd32bd9,0x76621588a223259ac633,0xfd0caa174d622825c7c9,0xe7718467000092970b,0x3e5586e5f7375d816000,0xd251d6f365f68ee007b0,0xdc00000000000076d0d3,0x870b250000d5190877c0],#[0x96ce0000f8d5956050,0x5e929bfb130000260000,0x2b3c50590000cb7b2a,0x7dc4600000fc2c038a00,0x92,0xb0714311b6c000,0xb627ca91288a40b85500,0x6c9a1300000000113029,0xee52ac7ba64c7561ba41,0x1b054a131fe2883873b9,0xbec968e2ad000000009d,0x344bffeb055376529fc7,0x42c369000055ee66ccbd,0x4c749e594300002baf1b,0xeb890aec0383b766cb69,0xf1eb897955165600003a,0x3229ecb0ddd8e9000091,0x327beccb6e553e27b067,0xb400007211b971000014,0xb4b2e72a9bc91ecaf34a,0xbafdfd4bf639fa47f4,0x67b51c4e000000,0x6d8a75489e8989e53800,0x3df57200002b790a2183,0x7ef8eb16e20336907ad7,0xba440cc9dff545a21ff6,0xfc00007054306bc55c7a,0x3f4415a18a0425b8b1c2,0x9000065112c3b1af062,0x581a001222874e30bc71,0x830000da1a8005091dd8,0xdc6c6f1557893f53b082],#[0x32384b404f80a4a7e7d6,0xb70000685bf3dcdce5b0,0x2edc112b7687e36290b5,0xf300004b8c938f5843f9,0x6d3a014e86097369a8c,0x390000b1c04092562de7,0xe4f12a7400000012e660,0x8a03602d28939b000031,0x5013b9f61e00003565db,0x483958e29d53000073,0x2d025b44220000422700,0x814700000000520d5d,0x8abf00000000000000,0x1206a41c8e00009a5000,0x12d64bf5b900003bcc02,0x4850000061368443b5,0x894bce760a34e5e25500,0x6400003d290000932c56,0x39810000b5b480,0xb7a692e3a34f00,0xaf433513bc0000012400,0x52e10000e2af56924c,0x69110000cb6d00,0x1ce0158cbdeb23747100,0xbe564a6c13456808ab95,0x41aefcce81031d122a0,0xa1fb1ed7338670966e54,0xb4c47581277ba0d3e80b,0x969126146c034e40ab01,0x92bcda3d1f2975d37752,0x687467f7dcdee07088,0xfa06d69e7042031303],#[0xb57b6b5d2c79b955e00,0x476550a0b6740f8018bc,0xec180000000049,0x468995f93966718b3b00,0xcff312457f00007546fc,0x329c9404d4bc6a065f19,0xe3654327f64908c8ff6b,0xc70000a047f903a55188,0x81f439ca665cece8f329,0x8036c406f1a4f97c2552,0x62db00000000c3bf82,0x3d797aece27575f32200,0x6316d10900a6ec137063,0x73532346f7df2a1f80,0x40407c1ab35ad70a100,0x555c09048c1250054b25,0xd8f5000072b10000e3,0x2521e2fc80841e000000,0x18a66f15152a03000037,0xd97786e80968c8e60b92,0x14b00d670a23481c1507,0x5a6837c1d500b92bc5a,0xdc44a4e5ae9ca5d7f1a7,0xdaf70000019eb8e018,0xd1dbf8c2a9b700,0x15abb2000099f413dd00,0xea70ded7b2cb4bd314c7,0xeb000000003b112b1617,0x57449f95f402ba14d9d6,0x501bb82917]]
def g63D10 := limbs80 #[#[0x186411024010420887f,0x1282a028681202802066,0x5a8aa3a0a8398e4290ea,0x4a90a5a1484a10859906,0x8aa0a9298a721887a94a,0x8260761503406801aa4a,0x6317055138470fe358b,0x4a7a849aa3e871f2759b,0x4e9382d8b40c82feb7ac,0xb2bc8b1b44f0c40efabc,0x701040c0080c15153bcc,0x3001400a3428b0c3860,0x6300aa00ce006700328,0xc802a00a8028007798,0x3bf80190057a00cf0030,0xbe0060028015fa806300,0x9c00ca00ca8061806002,0x801d7003a80338019401,0xa018c029805300ae0065,0x802bd006780190056]]
def g63H10 := limbs80 #[#[0x17000600031701041901,0x71400001b0500041e0e,0x22011000000102080a01,0x805020903064d000104,0x1105070b01004b000300,0x3131104032302000206,0x2519030e060108030405,0xc0f02001303052a0002,0x2050100130e3a281300,0x1d06030078010029020a,0x3009220001001c180102,0xc15030a1e05000a0025,0x273d410018000405032c,0xa000b000b20111c0f32,0x70000101b0801430721,0x8805500c03702210,0x3010932031b001a0104,0x504010708031190014b,0x160d250b410002450092,0x1a060607010400170d00,0x3a4a0c04603702560040,0xc9390003836751757a01,0x646b08621f752f504a71,0xb700034960001241224e,0x453708816b4cf05a6e94,0xc379a6037b4531865d30,0x9940fb3be433557706b3,0xdc27b91ac0000839e0fb,0x45d4209edfe965a5f92b,0xb3c4a7e0256ba98f6d16,0x7b87426c2492e2e876b,0xe09de6055116014cacad],#[0xd1da62205dc000ccd9e4,0x537332cb88af66780000,0x1652fd0e0900c94c0007,0x21f5e6f800030a5cd227,0x5a0b4f7e7cac43672000,0x30caaa240000003,0xa5a40dc989b6a3e3a700,0xd92c000a39322f405eaf,0x325d6c6a93331bf56e,0x49d1de2ac000d9549690,0xc526d7a40000000000a1,0xc9ce380000000108bb7d,0x47367c32cec2f65a1b90,0x3035066c4fc000978ac,0xa81fc802bb00004c2400,0x7361e5b309780001594,0x6aeea858540000e,0x1388000e64f27900,0x6e3e1340000002c46f3c,0x6ad7fd678038f0882c02,0xebcc789766e44ff8467a,0x1c199cb0000000666791,0x5f8000d4d6a240001a01,0xd18bb1bf64870000000f,0x633ae27c00081b6c16e5,0xd5fa56370276f4000c84,0xa4ab9584fbcb78b6b5ec,0xed9f8000688098ccb56a,0x47496f000000001c9601,0x4005005892de0002cfe,0x1592d370001c5d6,0xbcbac79e5b26a9800000],#[0xc137aa7a8823d4000c8a,0xcf95694650000f170002,0xe0002979715f4b47255a,0xab8250871d52fe84a85a,0x614515e14ec8fa090c0a,0x3dcfda39b6e6866ee1c9,0x268ab3a3259cae78f94a,0xe80574fcdb9450583147,0x4283f0f08e077c495837,0x35480002aabb7f41,0x62681860001730f33c00,0x163300004a083334b8,0x532872b0b85e92537400,0x800050aa5addcb956033,0x5ebc912d12c17252b7bc,0xd08af79546c065ce1820,0x6f54954ab6d15a500009,0xc84ced90003b4563176d,0xba74afa6be696e267a63,0x1a369c64cc390d624f0,0x350583d0b24cd1020a00,0x58065fc002bc78efc700,0x9ed852cf7089c04ad925,0xab338000f9a00000002a,0x591d8a12a1aaedc35bb2,0x58fc12d2aaa5bfc7e232,0xc4ca20169e61c2a6ebee,0x7e510001e6609c091131,0xde6189400064a0000bab,0x6e5908000096282c8bd6,0x5d1e8f4bd5850d500026,0x87358c48952041351ad2],#[0x7c473f434d6d75c81e4,0x58a0c19d5c44f50516b4,0x99ab0001d0f4c9913ab8,0xc85000000030f4000042,0x70d91759e07c0000e762,0x600002525430b3795758,0xdadf24a0003e64d6c38c,0x1c8000d3cc889b3412dc,0x69860b538def0626e5c3,0x34b938d144c4236203fa,0xe2db70914c6810000000,0x58e84000063b663d64e2,0x3dbd000017cc0001afe0,0x620e43306e315729dbaf,0xa4b6020002d7c30b64ef,0xef3484a102985b1c8c16,0xc4a7688667346f1ceb98,0x1a3d9a5151ac521020cc,0xfba3c92360bea530ae,0x900003469bac000d1580,0x8608ace0380007cefa2,0xa040ddb48a2e14364000,0x2c671000000043c8dbb3,0x30d8000000025f4000c6,0xf0e8cfac78c1aa5a4000,0x3ec900000000001,0x7b06d88c6ad66cd232c0,0x913d210d2d70eb87,0x3a06c53caaeba30000,0x38dd614610a8a7f0acb0,0x280c08486b00003959aa,0x2f8ab50000aa859034ca],#[0x34be0000cfa0002,0x6c3026c574f800000000,0x7764d30000000f8278a,0x8c41c07c28598b75c000,0x53d108a8f19db150ad08,0xf06ed2f627d0003a37ca,0x63309802eb3e230d3a0,0x2ba86f9ecf747322185f,0x1e0119a1c7646c000002,0xdc8c88291ffe2600039f,0xb0f47ea246d71870458d,0x40d70f6df81a82c3639a,0x6ed20001de3abc5697b2,0xd9144c000047e0ea246c,0x9bb0ed584f1a00092527,0x38c8970ccc2d54e0,0x2d6d2053c5019ab4400,0x4a7a23aaebaa750f0000,0xf0f0c055400065a80003,0xd437263854437b85d5ca,0x96600018e5916c000e0b,0x50cbcb25293c0b9c63,0x9d719eaada54a28247c0,0x30bc179407900009a,0x31c32ffad8d015d0b9cc,0x550086200039bf7,0x51bea6400064f2ace00,0x321d7e9018282c000000,0x4c58d5cfb04000f088,0x6000342026289b57a740,0x61b1eda000351712295a,0x59640f648f434451f313],#[0xd96fb0a4cb3f000c0006,0x9750002988334495e87,0x2d8678400097d216c36b,0x98777e042c18651adbfc,0xb95eca500022df0000c,0x0,0x86800000038cd70a2248,0x9c000d0e518f6219451d,0x62bbeacaa4400075,0xc40a0186b8a01d001000,0xe28c00037282dd38d7,0xa4d002330f8000cd280,0xad0f91600028ee827400,0xa2e0d71655b1dc6416e7,0xa9c08bd07d360abed32d,0xaa56d1a72749c3f30337,0xd761a6dda7ec5485febb,0xe100028df0002a670000,0x80000000e2ff59278c2c,0x8b6e63fd8f227a00011c,0x1d12a0dc44000e7ee968,0x1b39c930000d2b40002,0x2e5ea044000000000000,0x173c8e1e4336685e8000,0x9b20c558b100000000,0xb368aa506b5eea800000,0xec1fb2926732ca9988d0,0x39c95b21f39f27ad0eb1,0xb26826418ddbac9c1aa9,0xb4eaa9fe84330c3da8c3,0xe8d485400000039cfd36,0x92caec64b12c000d5bf],#[0x7ad1cf20d9adc9e66cd1,0xd0c4000000031248b312,0xbbdcc9b86798122c6ec6,0xe0b3ac700006016587b,0x8d21fcd2f1b0712e6f55,0x12cc19fe3ac778000813,0x2eb90141554394487800,0xb7558000000000001f5d,0x3a4d5ce147,0x3a613b00015b6d97c48e,0xf3d0002c3f00023494]]
def g63D11 := limbs80 #[#[0x8103f]]
def g63H11 := limbs80 #[#[0xb9f9215c1c040a3090a1,0x10060359e80038736f5c,0xa6000664c3a2c4fc8e45,0x35a354c1e0864d1800,0x612d0a85d139b9d00314,0x221e534a2e7ccc00109,0xf944a04c8e]]
def g63L : Nat → Packing
  | 5 => (10,6,6,524294,51,7,1024,g63D5)
  | 6 => (354,5,6,4260098,121,12,1056,g63D6)
  | 7 => (2794,4,6,6030581,123,16,1242,g63D7)
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
abbrev SixBits := Bool × Bool × Bool × Bool × Bool × Bool
abbrev SixRows := Fin 512 × Fin 512 × Fin 512 × Fin 512 × Fin 512 × Fin 512
def readSix (r : SixRows) (v : Sig) : SixBits := ⟨bit r.1 v,bit r.2.1 v,bit r.2.2.1 v,bit r.2.2.2.1 v,bit r.2.2.2.2.1 v,bit r.2.2.2.2.2 v⟩
def sixCost (x : SixBits) : Nat := (#[0,2,1,1,1,1,2,0,2,2,2,2,2,2,3,2,1,2,1,2,2,1,2,1,1,2,2,1,1,2,2,1,1,2,2,1,1,2,2,1,1,2,1,2,2,1,2,1,2,3,2,2,2,2,2,2,0,2,1,1,1,1,2,0] : Array Nat)[1 * x.1.toNat+2 * x.2.1.toNat+4 * x.2.2.1.toNat+8 * x.2.2.2.1.toNat+16 * x.2.2.2.2.1.toNat+32 * x.2.2.2.2.2.toNat]?.getD 3
def crossOp (d : Nat) (a b : Bool) :=
  if d=0 then a && b else if d=1 then a || b else if d=2 then a && !b else !a && b
def applySix (d : Nat) (a b : SixBits) : SixBits := ⟨crossOp d a.1 b.1,crossOp d a.2.1 b.2.1,crossOp d a.2.2.1 b.2.2.1,crossOp d a.2.2.2.1 b.2.2.2.1,crossOp d a.2.2.2.2.1 b.2.2.2.2.1,crossOp d a.2.2.2.2.2 b.2.2.2.2.2⟩
theorem readSix_bin (r : SixRows) (d) (a b : Sig) :
    readSix r (bin d a b) = applySix d (readSix r a) (readSix r b) := by
  simp only [readSix,applySix,bit_bin,crossOp]

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem six_cost_binary : ∀ (d : Fin 4) (a b : SixBits),
    sixCost (applySix d a b) ≤ sixCost a + sixCost b := by decide +kernel

theorem measure_live_tree (w : Sig → Nat) (hb : ∀ {d u} (a b), allowed u d →
    w (bin d a b) ≤ w a + w b) {u T k S} (h : Live u T k S) :
    S.card = k+1 → w T ≤ ∑ s ∈ S, w s := by
  induction h using Live.ind with
  | stop hp => simp
  | @binary k U a b d hd ha hb' ab fr tail ih =>
    intro saturated
    have zU : bin d a b ∉ U := fun m => fr (by simp [m])
    have bound := live_size tail
    rw [Finset.card_insert_of_notMem zU] at bound
    have bc := Finset.card_insert_le (a:=b) (s:=U)
    have ac := Finset.card_insert_le (a:=a) (s:=insert b U)
    have aU : a ∉ insert b U := by
      intro p
      rw [Finset.insert_eq_of_mem p] at saturated
      omega
    have bU : b ∉ U := by
      intro p
      rw [Finset.insert_eq_of_mem p] at saturated ac
      omega
    rw [Finset.card_insert_of_notMem aU,Finset.card_insert_of_notMem bU] at saturated
    have tp : (insert (bin d a b) U).card = k+1 := by rw [Finset.card_insert_of_notMem zU]; omega
    have step := ih tp
    rw [Finset.sum_insert zU] at step
    rw [Finset.sum_insert aU,Finset.sum_insert bU]
    have price := hb a b hd
    omega

theorem six_cut {u T k S} (r : SixRows) (size : S.card = k+1)
    (cost : (∑ s ∈ S, sixCost (readSix r s)) < sixCost (readSix r T)) :
    ∀ t, t ≤ k → ¬ Live u T t S := by
  intro t ht live
  have wid := live_size live
  have eq : S.card=t+1 := by omega
  apply Nat.not_lt_of_ge (measure_live_tree (fun a => sixCost (readSix r a)) (by
    intro d v a b h
    rw [readSix_bin]
    obtain h|h|⟨_,h⟩|⟨_,h⟩ := allowed_four h
    all_goals subst d
    · exact six_cost_binary 0 _ _
    · exact six_cost_binary 1 _ _
    · exact six_cost_binary 2 _ _
    · exact six_cost_binary 3 _ _) live eq) cost
def cubWitness : Array Nat := #[18958699836,14580926268,40082197308,14312491836,14244318012,45197840973,11912364557,11912368717,20502566037,11928883789,11929436814,22650565779,40082197052,40082196796,14580860732,20519505468,8138279686,22735529238,14077436686,11929603644,27030496794,40082309201,12130812505,14145594638,14145560838,39847242538,22768176444,44644454989,6678089020,39847243306,20502549777,20586614076,22667374106,14077470234,44445322044,64918411557,22667372058,46289210940,39847242282,39947901033,14580851370,28240910889,65191023633,22768034970,39847237865,42572980486,45334681701,23170828092,44311104316,14580847217,20519504956,45416939601,8138425002,14145627414,14580847209,14145629462,15219693861,15219593997,39846193706,28624732988,11929408077,14077436442,12130787994,23170827068,14077536810,14143463686,28102366225,39947980092,18438654122,23945843469,23945943333,39847242022,20586474682,14312491324,14077438506,14145693990,23945812261,23740358854,22667372318,44243996220,44210465322,65344123467,45198462524,14649100092,45334777404,28104463377,45284366889,45536103228,64935209514,6761879845,20586472602,39847267516,12198038076,27030529562,14380665660,45334680141,23945941285,23945810213,7802200326,39947905194,12096733850,28236591755,11929409613,12130929468,20519360281,20502316825,46490569532,45198365261,7835820694,14077436166,6677893453,11929408093,49336631637,14060630603,45284349989,45284350245,65191031955,7735725372,33226392234,39947979836,28104604851,28291321404,28343046795,23979922059,23975727755,15252624011,15253672587,12031643719,14145564999,44243900517,64851302693,40081935164,65344185882,55491470490,46834405965,44210367018,65207838234,28104596497,14077469210,65191156785,28240794381,45743624781,63145908777,28624734012,64918428201,65327354637,39847240234,65412276486,22667374138,23740290065,14077407819,27064192572,28624687721,28154972732,55474431130,54946210970,57027110426,28154973756,58314070309,58850941221,65191040277,64914217253,65191154705,28240908841,18941922620,31760729916,63145777705,62600518185,65191165107,28240786059,21131871548,18472160572,65191155761,44653039164,45198429756,53310049596]
def cubTag (k i : Nat) : Nat :=
  match k with
  | 5 => cubWitness[((#[0,1,2,3,4,5,6,6,6,7] : Array Nat)[i-0]?.getD 0)]?.getD 0
  | 6 => cubWitness[((#[8,8,9,10,11,12,13,14,10,3,15,16,10,17,18,19,2,19,20,21,22,9,23,24,25,2,26,27,28,29,19,30,31,32,33,34,33,33,35,36,37,36,38,34,39,2,40,41,42,41,43,44,45,46,47,47,2,2,46,46,46,48,40,2,36,49,50,24,49,38,51,15,15,52,38,53,54,55,39,24,38,38,56,56,56,39,40,56,40,57,56,57,58,38,38,59,60,61,62,62,63,14,38,64,24,38,39,54,65,1,40,66,67,19,15,47,68,60,69,70,15,12,46,46,67,46,71,70,72,70,72,2,72,13,73,74,38,69,75,76,77,77,1,77,78,12,12,79,80,64,81,82,38,64,83,38,79,38,1,79,1,1,1,2,3,2,46,46,40,61,36,54,1,84,85,86,85,3,15,26,60,60,15,84,85,87,87,31,15,70,48,36,24,87,36,88,70,15,89,90,36,90,36,36,91,70,33,92,15,36,36,93,81,33,94,36,95,96,39,97,73,70,70,65,98,46,99,2,100,47,2,47,2,2,24,24,46,46,56,54,56,101,102,103,56,40,102,56,29,29,104,105,104,104,38,38,36,46,46,56,56,46,36,36,85,29,29,32,56,24,24,24,19,15,15,47,101,15,101,106,46,107,2,38,38,101,108,38,18,56,57,107,57,60,31,15,15,38,38,38,33,101,38,38,101,38,38,109,38,110,46,111,46,47] : Array Nat)[i-40]?.getD 0)]?.getD 0
  | 7 => cubWitness[((#[2,84,84,2,112,2,31,43,113,31,2,2,2,46,19,2,1,67,99,35,24,46,114,115,19,67,115,115,24,26,3,43,116,15,117,118,15,115,115,119,3,67,120,2,67,67,67,36,67,67,38,38,24,15,2,19,2,47,47,2,15,15,15,15,15,19,15,85,53,47,2,2,24,70,2,2,121,122,2,67,2,123,20,123,2,24,2,115,124,2,2,115,2,125,126,115,115,115,127,79,79,128,15,24,128,24,128,15,15,15,15,20,115,26,115,67,2,53,85,2,20,2,2,115,67,115,24,24,24,24,24,24,24,36,38,46,3,26,120,1,99,15,15,129,129,35,2,88,67,38,46,38,38,38,19,34,56,15,15,38,38,38,90,36,69,129,53,36,38,38,69,69,42,38,38,32,15,35,38,43,31,36,36,57,70,70,33,38,130,38,38,33,38,38,33,38,33,38,33,31,38,38,36,129,129,53,34,69,38,38,36,69,36,36,38,38,129,69,36,36,69,38,38,42,64,64,64,38,38,70,70,15,15,24,36,38,36,90,90,39,39,99,99,15,15,84,38,64,38,99,99,33,38,15,70,38,38,15,38,46,24,35,84,41,99,24,42,41,43,2,35,46,46,70,46,46,24,131,2,24,34,24,132,24,41,70,38,41,41,38,24,35,41,99,24,133,41,2,2,24,2,2,24,24,2,2,24,131,2,34,38,38,38,38,38,38,35,129,38,84,38,2,38,43,42,36,35,36,34,43,70,38,38,46,46,38,38,36,36,54,134,54,70,39,39,39,36,15,39,60,60,135,136,38,87,39,19,60,38,70,60,60,70,38,38,115,115,62,56,85,39,85,85,2,2,62,62,62,85,2,115,137,34,56,56,99,138,39,85,120,85,90,34,99,85,99,99,85,56,56,57,56,56,57,57,58,38,59,85,60,59,26,38,38,38,56,2,60,60,15,56,126,60,60,62,139,67,42,35,96,67,26,38,41,2,39,64,31,64,140,141,35,46,38,39,67,99,39,142,83,46,38,38,38,24,83,83,35,35,24,24,35,143,144,46,2,46,46,2,2,38,64,64,64,64,39,64,64,31,41,31,64,67,38,38,38,39,64,64,64,64,38,35,67,99,38,135,135,135,38,140,31,38,38,38,99,129,79,42,129,46,46,99,38,99,1,38,99,38,38,38,46,46,46,64,38,46,38,69,15,46,46,46,129,52,67,46,1,58,38,38,42,60,145,38,35,38,38,38,15,42,70,35,35,24,24,146,46,1,1,67,146,36,35,46,35,1,79,1,46,46,1,99,46,129,38,38,38,46,2,2,70,70,46,46,46,38,2,2,147,38,139,72,38,38,38,2,70,72,42,42,42,46,38,38,38,46,38,2,2,38,88,42,42,88,1,38,38,1,70,70,67,1,148,67,64,1,64,67,1,148,64,64,99,46,84,46,19,38,39,60,24,46,46,147,15,70,35,24,46,41,64,38,38,38,144,38,149,38,35,31,38,38,35,38,38,38,46,38,2,31,35,150,70,35,129,38,60,39,70,70,38,64,64,64,64,79,35,35,24,79,46,35,79,46,38,38,46,79,64,151,64,38,79,38,46,84,35,24,46,38,79,35,46,38,38,60,1,79,1,2,2,143,34,59,141,39,46,152,143,143,39,39,46,143,34,46,46,46,46,99,64,35,39,143,64,39,99,138,41,2,1,99,129,129,46,46,59,99,87,153,38,46,99,46,46,38,46,46,46,67,58,38,59,38,60,59,38,64,38,38,38,38,143,87,2,15,2,24,143,87,46,46,46,2,136,136,154,155,136,136,136,67,1,156,38,64,46,46,39,60,99,15,46,136,157,157,15,143,38,143,60,39,38,136,64,129,36,36,89,89,56,67,31,39,115,115,115,115,56,2,33,31,99,56,56,56,57,58,38,88,60,88,38,56,60,56,60,86,84,115,86,115,85,85,99,26,26,15,60,26,26,67,15,26,26,26,15,26,57,15,15,39,35,132,35,94,94,42,34,41,15,15,41,42,158,70,67,39,39,33,31,31,36,31,31,33,35,35,35,20,34,15,70,67,1,63,67,79,70,159,70,67,160,116,24,15,70,88,67,88,151,151,70,67,160,15,36,36,24,36,15,90,90,70,1,63,2,63,2,36,142,90,90,159,70,35,161,161,70,70,159,35,159,35,70,35,35,67,36,159,70,70,70,70,158,33,36,33,33,33,15,15,53,53,24,36,70,36,36,36,36,159,70,70,70,33,33,33,41,151,70,42,129,129,129,36,36,36,129,70,70,15,162,36,33,151,33,36,36,15,162,151,36,36,70,36,34,33,36,15,160,160,129,36,84,41,84,67,2,2,39,87,34,70,70,35,163,64,41,41,64,33,142,87,2,87,67,70,70,35,70,70,70,42,41,84,84,36,36,159,15,70,70,41,88,70,70,70,70,70,70,88,70,70,64,64,15,84,38,41,64,41,84,84,70,150,88,70,70,38,70,84,64,41,46,38,38,2,85,2,67,88,67,39,38,67,164,36,2,144,38,36,31,33,34,33,38,35,33,36,46,143,46,24,2,24,2,2,2,46,46,2,2,35,39,99,87,81,2,24,2,2,2,2,31,115,46,35,46,42,39,31,147,39,39,144,99,99,144,115,35,39,115,115,165,46,46,56,56,35,35,56,40,41,2,41,35,115,40,115,115,56,56,31,166,142,85,167,2,2,2,2,2,162,34,39,115,115,115,46,56,56,40,115,115,115,115,115,41,40,168,144,85,38,46,2,46,46,47,47,46,87,2,2,38,38,46,36,36,2,46,46,46,2,2,46,85,85,46,2,56,56,2,56,56,56,46,56,2,56,56,31,31,2,31,2,2,2,15,15,39,33,169,170,2,31,31,33,33,115,99,35,64,15,39,115,39,115,99,33,99,42,39,15,38,38,2,2,26,2,2,15,129,2,3,31,31,2,2,2,56,56,15,15,57,57,1,67,36,70,36,36,2,36,15,36,90,38,38,38,38,171,26,2,136,136,38,15,171,26,38,15,38,38,38,32,38,38,38,38,38,2,38,56,60,70,26,67,69,38,70,56,38,15,38,38,38,57,38,57,57,60,60,57,57,57,38,31,135,85,69,88,38,38,64,88,88,38,38,56,57,38,33,60,38,150,38,15,38,32,15,15,15,33,38,33,38,15,38,150,32,38,33,15,38,32,38,38,38,38,15,38,33,33,38,32,38,38,38,15,2,2,38,56,56,56,38,38,38,70,67,160,15,36,24,15,15,172,38,90,70,46,159,70,87,2,126,46,46,46,46,2,46,46,46,2,41,90,2,2,159,70,31,36,36,36,33,38,36,129,36,99,15,15,15,90,15,15,15,70,15,38,15,173,84,84,144,35,84,84,46,84,46,46,56,35,144,2,2,129,36,38,164,69,60,60,164,39,69,60,57,57,57,57,57,57,39,39,39,60,57,99,90,15,15,2,24,2,2,35,67,60,35,57,60,60,60,174,36,36,33,129,36,2,2,15,15,15,84,84,38,84,38,38,38,38] : Array Nat)[i-1227]?.getD 0)]?.getD 0
  | 8 => cubWitness[((#[67,67,26,67,67,2,128,2,15,128,15,15,15,38,90,160,38,36,36,36,39,39,39,115,56,57,39,39,39,39,135,46,46,129,46,46,129,67,67,67,38,38,38,38,38,67,67,39,150,38,38,38,129,38,38,38,38,38,87,39,87,39,46,46,129,46,46,67,87,136,136,136,136,115,56,57,139,39,159,159,90,142,142,159,159,159,159,159,159,36,36,87,142,142,159,159,88,88,88,88,39,175,175,39,175,2,175,90,35,35,115,35,35,115,142,142,2,2,2,2,139,115,115,115,115,115,85,85,169,39,39,39,39,115,99,99,169,169,67,67,70,26,26,70,70,57,15,85,57,38,38,90,90] : Array Nat)[i-3259]?.getD 0)]?.getD 0
  | _ => 0
def cubRows (word : Nat) : SixRows := ⟨Fin.ofNat 512 ((word >>> 0) % 64),Fin.ofNat 512 ((word >>> 6) % 64),Fin.ofNat 512 ((word >>> 12) % 64),Fin.ofNat 512 ((word >>> 18) % 64),Fin.ofNat 512 ((word >>> 24) % 64),Fin.ofNat 512 ((word >>> 30) % 64)⟩

def crossOK (g : Forest) (k i : Nat) : Bool :=
  let S := (stateSet g k i).toFinset
  let r := cubRows (cubTag k i)
  decide (S.card = k+1) && decide ((∑ s ∈ S, sixCost (readSix r s)) < sixCost (readSix r (targetOf g)))

def spanOK (g : Forest) (k start n : Nat) : Prop :=
  ∀ i, start ≤ i → i < start+n →
    nodeVerified g k i = true ∨ Impossible g.mode (targetOf g) k (stateSet g k i).toFinset

theorem spanOld {g k a n} (h : block g k a n = true) : spanOK g k a n :=
  fun i lo hi => Or.inl (block_at h i lo hi)

theorem spanSix {g k a n} (h : ((List.range n).all (fun j => crossOK g k (a+j))) = true) : spanOK g k a n := by
  intro i lo hi
  have v := List.all_eq_true.mp h (i-a) (List.mem_range.mpr (by omega))
  rw [Nat.add_sub_of_le lo] at v
  simp only [crossOK,Bool.and_eq_true,decide_eq_true_eq] at v
  exact Or.inr (six_cut (cubRows (cubTag k i)) v.1 v.2)

theorem spanMerge {g k a n m} (h : spanOK g k a n) (h' : spanOK g k (a+n) m) :
    spanOK g k a (n+m) := by
  intro i hi hj
  by_cases lt : i<a+n
  · exact h i hi lt
  · exact h' i (by omega) (by omega)

theorem forest_span (g : Forest) (top : Nat) (prior : Nat → Nat)
    (lower : ∀ q, Lower g.mode (varsX q) (graphGoal q) (prior q))
    (geometry : graphValid g prior = true) (rows : ∀ k ≤ top, spanOK g k 0 (g.levels k).1) :
    ∀ k ≤ top, ∀ i < (g.levels k).1, Impossible g.mode (targetOf g) k (stateSet g k i).toFinset := by
  simp only [graphValid,Bool.and_eq_true,List.all_eq_true,beq_iff_eq] at geometry
  intro k
  induction k with
  | zero =>
    intro hk i hi
    rcases rows 0 hk i (by omega) (by omega) with ok|done
    case inr => exact done
    apply nodeVerified_sound g 0 i (chart_pairs geometry.1.1.1 geometry.1.1.2)
      (fun x hx => col_sound _ prior lower (geometry.1.2 x hx)) geometry.2 (by omega)
    exact ok
  | succ k ih =>
    intro hk i hi
    rcases rows (k+1) hk i (by omega) (by omega) with ok|done
    case inr => exact done
    apply nodeVerified_sound g _ i (chart_pairs geometry.1.1.1 geometry.1.1.2)
      (fun x hx => col_sound _ prior lower (geometry.1.2 x hx)) geometry.2
      (fun _ => by simpa using ih (by omega))
    exact ok
theorem root_span {g top prior k i ws} (low : ∀ q, Lower g.mode (varsX q) (graphGoal q) (prior q))
    (geom : graphValid g prior = true) (blocks : ∀ k ≤ top, spanOK g k 0 (g.levels k).1) (le : k ≤ top)
    (idx : indexedRoot g k i ws = true) : Impossible g.mode (targetOf g) k ws.toFinset := by
  simp only [indexedRoot,Bool.and_eq_true,decide_eq_true_eq] at idx
  rw [←sameWords_sound idx.2]
  exact forest_span g top prior low geom blocks _ le i idx.1
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP5_0 : spanOK g63 5 0 10 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossB5 : spanOK g63 5 0 10 := crossP5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP6_0 : spanOK g63 6 0 27 := by
  apply spanOld
  apply cellsBlock (ar:=6) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP6_27 : spanOK g63 6 27 13 := by
  apply spanOld
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP6_40 : spanOK g63 6 40 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP6_72 : spanOK g63 6 72 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP6_104 : spanOK g63 6 104 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP6_136 : spanOK g63 6 136 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP6_168 : spanOK g63 6 168 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP6_200 : spanOK g63 6 200 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP6_232 : spanOK g63 6 232 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP6_264 : spanOK g63 6 264 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP6_296 : spanOK g63 6 296 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP6_328 : spanOK g63 6 328 26 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossB6 : spanOK g63 6 0 354 := (spanMerge (spanMerge (spanMerge crossP6_0 (spanMerge crossP6_27 crossP6_40)) (spanMerge crossP6_72 (spanMerge crossP6_104 crossP6_136))) (spanMerge (spanMerge crossP6_168 (spanMerge crossP6_200 crossP6_232)) (spanMerge crossP6_264 (spanMerge crossP6_296 crossP6_328))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP7_0 : spanOK g63 7 0 96 := by
  apply spanOld
  apply cellsBlock (ar:=6) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP7_96 : spanOK g63 7 96 6 := by
  apply spanOld
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP7_102 : spanOK g63 7 102 96 := by
  apply spanOld
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP7_198 : spanOK g63 7 198 96 := by
  apply spanOld
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP7_294 : spanOK g63 7 294 96 := by
  apply spanOld
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP7_390 : spanOK g63 7 390 96 := by
  apply spanOld
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP7_486 : spanOK g63 7 486 96 := by
  apply spanOld
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP7_582 : spanOK g63 7 582 96 := by
  apply spanOld
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP7_678 : spanOK g63 7 678 96 := by
  apply spanOld
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP7_774 : spanOK g63 7 774 96 := by
  apply spanOld
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP7_870 : spanOK g63 7 870 96 := by
  apply spanOld
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP7_966 : spanOK g63 7 966 86 := by
  apply spanOld
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP7_1052 : spanOK g63 7 1052 96 := by
  apply spanOld
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP7_1148 : spanOK g63 7 1148 79 := by
  apply spanOld
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP7_1227 : spanOK g63 7 1227 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP7_1259 : spanOK g63 7 1259 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP7_1291 : spanOK g63 7 1291 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP7_1323 : spanOK g63 7 1323 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP7_1355 : spanOK g63 7 1355 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP7_1387 : spanOK g63 7 1387 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP7_1419 : spanOK g63 7 1419 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP7_1451 : spanOK g63 7 1451 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP7_1483 : spanOK g63 7 1483 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP7_1515 : spanOK g63 7 1515 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP7_1547 : spanOK g63 7 1547 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP7_1579 : spanOK g63 7 1579 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP7_1611 : spanOK g63 7 1611 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP7_1643 : spanOK g63 7 1643 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP7_1675 : spanOK g63 7 1675 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP7_1707 : spanOK g63 7 1707 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP7_1739 : spanOK g63 7 1739 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP7_1771 : spanOK g63 7 1771 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP7_1803 : spanOK g63 7 1803 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP7_1835 : spanOK g63 7 1835 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP7_1867 : spanOK g63 7 1867 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP7_1899 : spanOK g63 7 1899 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP7_1931 : spanOK g63 7 1931 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP7_1963 : spanOK g63 7 1963 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP7_1995 : spanOK g63 7 1995 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP7_2027 : spanOK g63 7 2027 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP7_2059 : spanOK g63 7 2059 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP7_2091 : spanOK g63 7 2091 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP7_2123 : spanOK g63 7 2123 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP7_2155 : spanOK g63 7 2155 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP7_2187 : spanOK g63 7 2187 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP7_2219 : spanOK g63 7 2219 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP7_2251 : spanOK g63 7 2251 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP7_2283 : spanOK g63 7 2283 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP7_2315 : spanOK g63 7 2315 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP7_2347 : spanOK g63 7 2347 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP7_2379 : spanOK g63 7 2379 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP7_2411 : spanOK g63 7 2411 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP7_2443 : spanOK g63 7 2443 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP7_2475 : spanOK g63 7 2475 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP7_2507 : spanOK g63 7 2507 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP7_2539 : spanOK g63 7 2539 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP7_2571 : spanOK g63 7 2571 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP7_2603 : spanOK g63 7 2603 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP7_2635 : spanOK g63 7 2635 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP7_2667 : spanOK g63 7 2667 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP7_2699 : spanOK g63 7 2699 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP7_2731 : spanOK g63 7 2731 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP7_2763 : spanOK g63 7 2763 31 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossB7 : spanOK g63 7 0 2794 := (spanMerge (spanMerge (spanMerge (spanMerge (spanMerge crossP7_0 (spanMerge crossP7_96 crossP7_102)) (spanMerge (spanMerge crossP7_198 crossP7_294) (spanMerge crossP7_390 crossP7_486))) (spanMerge (spanMerge (spanMerge crossP7_582 crossP7_678) (spanMerge crossP7_774 crossP7_870)) (spanMerge (spanMerge crossP7_966 crossP7_1052) (spanMerge crossP7_1148 crossP7_1227)))) (spanMerge (spanMerge (spanMerge (spanMerge crossP7_1259 crossP7_1291) (spanMerge crossP7_1323 crossP7_1355)) (spanMerge (spanMerge crossP7_1387 crossP7_1419) (spanMerge crossP7_1451 crossP7_1483))) (spanMerge (spanMerge (spanMerge crossP7_1515 crossP7_1547) (spanMerge crossP7_1579 crossP7_1611)) (spanMerge (spanMerge crossP7_1643 crossP7_1675) (spanMerge crossP7_1707 crossP7_1739))))) (spanMerge (spanMerge (spanMerge (spanMerge (spanMerge crossP7_1771 crossP7_1803) (spanMerge crossP7_1835 crossP7_1867)) (spanMerge (spanMerge crossP7_1899 crossP7_1931) (spanMerge crossP7_1963 crossP7_1995))) (spanMerge (spanMerge (spanMerge crossP7_2027 crossP7_2059) (spanMerge crossP7_2091 crossP7_2123)) (spanMerge (spanMerge crossP7_2155 crossP7_2187) (spanMerge crossP7_2219 crossP7_2251)))) (spanMerge (spanMerge (spanMerge (spanMerge crossP7_2283 crossP7_2315) (spanMerge crossP7_2347 crossP7_2379)) (spanMerge (spanMerge crossP7_2411 crossP7_2443) (spanMerge crossP7_2475 crossP7_2507))) (spanMerge (spanMerge (spanMerge crossP7_2539 crossP7_2571) (spanMerge crossP7_2603 crossP7_2635)) (spanMerge (spanMerge crossP7_2667 crossP7_2699) (spanMerge crossP7_2731 crossP7_2763))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP8_0 : spanOK g63 8 0 26 := by
  apply spanOld
  apply cellsBlock (ar:=6) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP8_26 : spanOK g63 8 26 96 := by
  apply spanOld
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP8_122 : spanOK g63 8 122 96 := by
  apply spanOld
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP8_218 : spanOK g63 8 218 96 := by
  apply spanOld
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP8_314 : spanOK g63 8 314 96 := by
  apply spanOld
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP8_410 : spanOK g63 8 410 96 := by
  apply spanOld
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP8_506 : spanOK g63 8 506 96 := by
  apply spanOld
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP8_602 : spanOK g63 8 602 96 := by
  apply spanOld
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP8_698 : spanOK g63 8 698 96 := by
  apply spanOld
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP8_794 : spanOK g63 8 794 96 := by
  apply spanOld
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP8_890 : spanOK g63 8 890 96 := by
  apply spanOld
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP8_986 : spanOK g63 8 986 96 := by
  apply spanOld
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP8_1082 : spanOK g63 8 1082 96 := by
  apply spanOld
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP8_1178 : spanOK g63 8 1178 96 := by
  apply spanOld
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP8_1274 : spanOK g63 8 1274 96 := by
  apply spanOld
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP8_1370 : spanOK g63 8 1370 96 := by
  apply spanOld
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP8_1466 : spanOK g63 8 1466 71 := by
  apply spanOld
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP8_1537 : spanOK g63 8 1537 96 := by
  apply spanOld
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP8_1633 : spanOK g63 8 1633 96 := by
  apply spanOld
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP8_1729 : spanOK g63 8 1729 96 := by
  apply spanOld
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP8_1825 : spanOK g63 8 1825 96 := by
  apply spanOld
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP8_1921 : spanOK g63 8 1921 96 := by
  apply spanOld
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP8_2017 : spanOK g63 8 2017 96 := by
  apply spanOld
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP8_2113 : spanOK g63 8 2113 96 := by
  apply spanOld
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP8_2209 : spanOK g63 8 2209 96 := by
  apply spanOld
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP8_2305 : spanOK g63 8 2305 96 := by
  apply spanOld
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP8_2401 : spanOK g63 8 2401 96 := by
  apply spanOld
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP8_2497 : spanOK g63 8 2497 96 := by
  apply spanOld
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP8_2593 : spanOK g63 8 2593 96 := by
  apply spanOld
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP8_2689 : spanOK g63 8 2689 96 := by
  apply spanOld
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP8_2785 : spanOK g63 8 2785 96 := by
  apply spanOld
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP8_2881 : spanOK g63 8 2881 96 := by
  apply spanOld
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP8_2977 : spanOK g63 8 2977 96 := by
  apply spanOld
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP8_3073 : spanOK g63 8 3073 21 := by
  apply spanOld
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP8_3094 : spanOK g63 8 3094 96 := by
  apply spanOld
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP8_3190 : spanOK g63 8 3190 69 := by
  apply spanOld
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP8_3259 : spanOK g63 8 3259 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP8_3291 : spanOK g63 8 3291 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP8_3323 : spanOK g63 8 3323 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP8_3355 : spanOK g63 8 3355 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP8_3387 : spanOK g63 8 3387 25 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossB8 : spanOK g63 8 0 3412 := (spanMerge (spanMerge (spanMerge (spanMerge (spanMerge crossP8_0 crossP8_26) (spanMerge crossP8_122 (spanMerge crossP8_218 crossP8_314))) (spanMerge (spanMerge crossP8_410 crossP8_506) (spanMerge crossP8_602 (spanMerge crossP8_698 crossP8_794)))) (spanMerge (spanMerge (spanMerge crossP8_890 crossP8_986) (spanMerge crossP8_1082 (spanMerge crossP8_1178 crossP8_1274))) (spanMerge (spanMerge crossP8_1370 crossP8_1466) (spanMerge crossP8_1537 (spanMerge crossP8_1633 crossP8_1729))))) (spanMerge (spanMerge (spanMerge (spanMerge crossP8_1825 crossP8_1921) (spanMerge crossP8_2017 (spanMerge crossP8_2113 crossP8_2209))) (spanMerge (spanMerge crossP8_2305 crossP8_2401) (spanMerge crossP8_2497 (spanMerge crossP8_2593 crossP8_2689)))) (spanMerge (spanMerge (spanMerge crossP8_2785 crossP8_2881) (spanMerge crossP8_2977 (spanMerge crossP8_3073 crossP8_3094))) (spanMerge (spanMerge crossP8_3190 (spanMerge crossP8_3259 crossP8_3291)) (spanMerge crossP8_3323 (spanMerge crossP8_3355 crossP8_3387))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP9_0 : spanOK g63 9 0 9 := by
  apply spanOld
  apply cellsBlock (ar:=6) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP9_9 : spanOK g63 9 9 96 := by
  apply spanOld
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP9_105 : spanOK g63 9 105 96 := by
  apply spanOld
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP9_201 : spanOK g63 9 201 92 := by
  apply spanOld
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP9_293 : spanOK g63 9 293 96 := by
  apply spanOld
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP9_389 : spanOK g63 9 389 96 := by
  apply spanOld
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP9_485 : spanOK g63 9 485 96 := by
  apply spanOld
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP9_581 : spanOK g63 9 581 96 := by
  apply spanOld
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP9_677 : spanOK g63 9 677 96 := by
  apply spanOld
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP9_773 : spanOK g63 9 773 71 := by
  apply spanOld
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossB9 : spanOK g63 9 0 844 := (spanMerge (spanMerge (spanMerge crossP9_0 crossP9_9) (spanMerge crossP9_105 (spanMerge crossP9_201 crossP9_293))) (spanMerge (spanMerge crossP9_389 crossP9_485) (spanMerge crossP9_581 (spanMerge crossP9_677 crossP9_773))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP10_0 : spanOK g63 10 0 41 := by
  apply spanOld
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossB10 : spanOK g63 10 0 41 := crossP10_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP11_0 : spanOK g63 11 0 1 := by
  apply spanOld
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossB11 : spanOK g63 11 0 1 := crossP11_0
theorem crossT : ∀ k ≤ 11, spanOK g63 k 0 (g63.levels k).1 := by
  intro k hk
  interval_cases k
  · intro i lo hi; change i<0 at hi; omega
  · intro i lo hi; change i<0 at hi; omega
  · intro i lo hi; change i<0 at hi; omega
  · intro i lo hi; change i<0 at hi; omega
  · intro i lo hi; change i<0 at hi; omega
  · exact crossB5
  · exact crossB6
  · exact crossB7
  · exact crossB8
  · exact crossB9
  · exact crossB10
  · exact crossB11
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63G : graphValid g63 (boundsBefore K2110) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem fullLower : Impossible true graph 11 rawSix.toFinset := by
  rw [show graph = targetOf g63 by decide +kernel]
  exact root_span (g:=g63) (top:=11) (i:=0) (before_sound K2110 V2110) g63G crossT (by decide) (by decide +kernel)
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

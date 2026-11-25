import PEqualNP.Defs

-- The two-mode live-state and cofactor checker follows L_meta_1674 and L_meta_670.
-- The graph, restrictions and all search certificates below are for L_meta_10968.

-- Shared forest and cofactor certificates from L_meta_1674 and PR 11111 for L_meta_1677.
-- The original credit line is retained below. The two root certificates here cover the unpinned graph.

-- The checker and the bound certificates are adapted from PEqualNP/Outside/L_meta_1667.lean (Apache-2.0).
-- Two modes: u=false are monotone runs (AND, OR); u=true are runs up to complement, where negation is free.
namespace PEqualNP.Outside.L_meta_10968
open PEqualNP.CircuitLowerBounds
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

def inputs : List Sig := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000]
def graph : Sig := 0xfffffffffffffffefffffffffffffffefffffffffffefffcfffffffffffafff0fffffffeffffffeefffffefeffffeeeefffefffcffeeffccfefefcfcaaaa0000
def sample (r : Row) (j : Fin 9) := bit r (inputs.getD j.val zero)
def edge (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 5) || (x 1 && x 6) || (x 3 && x 6) || (x 0 && x 7) || (x 1 && x 7) || (x 4 && x 7) || (x 2 && x 8) || (x 3 && x 8) || (x 5 && x 8)
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
def varsX (m : Nat) : List Sig := if m<512 then vars m else vars m ++ [typeWord (m/512-1)]
def vertex (m j : Nat) := if m.testBit j then inputs.getD j zero else zero
def graphGoal (m : Nat) : Sig :=
  let x := vertex m
  (x 0 &&& x 4) ||| (x 1 &&& x 5) ||| (x 2 &&& x 5) ||| (x 1 &&& x 6) ||| (x 3 &&& x 6) ||| (x 0 &&& x 7) ||| (x 1 &&& x 7) ||| (x 4 &&& x 7) ||| (x 2 &&& x 8) ||| (x 3 &&& x 8) ||| (x 5 &&& x 8)
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
  | 0 => 0x10000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001
  | 1 => 0x1000000000000000000000000000000010000000000000000000000000000000100000000000000000000000000000001
  | 2 => 0x100000000000000010000000000000000000000000000000000000000000000010000000000000001
  | 3 => 0x10000000000000000000000000000000000000000000000000000000000000001
  | 4 => 0x1000000000000000100000000000000010000000000000001
  | 5 => 0x100000000000000000000000000000001
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

def supportPairs (t : Nat) (mask : Nat) : List (Sig × Row × Row) :=
  (selected mask).map fun (i,a) =>
    let r := if t/81==2 && i==t/9 % 9 then 1 <<< (t % 9) else if t/81==2 && i==t % 9 then 1 <<< (t/9 % 9) else 0
    (a,Fin.ofNat 512 r,Fin.ofNat 512 (r ||| (1 <<< i)))

def graphPairs (m hints : Nat) : List (Sig × Row × Row) :=
  (selected m).map fun (i,a) =>
    let r := 1 <<< ((hints >>> (4*i)) &&& 15)
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
  (x 0 &&& x 4) ||| (x 1 &&& x 5) ||| (x 2 &&& x 5) ||| (x 1 &&& x 6) ||| (x 3 &&& x 6) ||| (x 0 &&& x 7) ||| (x 1 &&& x 7) ||| (x 4 &&& x 7) ||| (x 2 &&& x 8) ||| (x 3 &&& x 8) ||| (x 5 &&& x 8)
theorem bit_vertex (m : Nat) (v : Nat → Bits) (i : Fin 152) (j : Fin 9) :
    bit (asRow v i) (vertex m j.val) =
    ((if m.testBit j.val then v j.val else 0) : Bits).getLsbD i.val := by
  by_cases hh : m.testBit j.val = true
  · simpa [vertex,hh] using asRow_bit v i j
  · simp [vertex,hh,bit_zero]
theorem bit_liftGoal (m : Nat) (v : Nat → Bits) (i : Fin 152) :
    bit (asRow v i) (graphGoal m) = (liftGoal m v).getLsbD i.val := by
  have pos (j : Nat) (hj : j<9) : (vertex m j).getLsbD (asRow v i).val = ((if m.testBit j then v j else 0) : Bits).getLsbD i.val := bit_vertex m v i ⟨j,hj⟩
  simp only [bit,graphGoal,liftGoal,BitVec.getLsbD_and,BitVec.getLsbD_or]
  simp only [pos 0 (by decide),pos 1 (by decide),pos 2 (by decide),pos 3 (by decide),pos 4 (by decide),pos 5 (by decide),pos 6 (by decide),pos 7 (by decide),pos 8 (by decide)]
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
def packedAt (word : Nat → Nat) (pos len : Nat) :=
  let i := pos/8192
  let shift := pos % 8192
  let lo := word i >>> shift
  if shift+len ≤ 8192 then lo &&& ((1 <<< len)-1)
  else (lo ||| (word (i+1) <<< (8192-shift))) &&& ((1 <<< len)-1)


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

def neighbor10968 (i : Fin 9) : Nat := [4, 5, 5, 6, 0, 1, 1, 0, 2].getD i.val 0
def absentRow10968 (i : Fin 9) : Row := Fin.ofNat 512 (1 <<< neighbor10968 i)
def presentRow10968 (i : Fin 9) : Row := Fin.ofNat 512 ((1 <<< i.val) ||| (1 <<< neighbor10968 i))

set_option maxHeartbeats 1000000 in
theorem requiredInputs :
    (∀ i : Fin 9, bit (absentRow10968 i) graph ≠ bit (presentRow10968 i) graph) ∧
    (∀ i j : Fin 9, i ≠ j →
      bit (absentRow10968 i) (inputs.getD j.val zero) =
      bit (presentRow10968 i) (inputs.getD j.val zero)) := by decide +kernel


theorem twoRoots (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (computes : PEqualNP.MetaComplexity.circuitFun 9 C = edge) (small : C.size ≤ 14) :
    ∃ (u : Bool) (k : Nat), k ≤ (if u then 13 else 14) ∧ Live u graph k inputs.toFinset := by
  have goalEq : (execute C.gates inputs).getD C.output zero = graph := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    exact (table_eval C legal C.output r).trans ((congrFun computes (sample r)).trans (edge_table r).symm)
  have len : C.gates.length ≤ 14 := small
  have mode : ∃ u : Bool, (u=false → ∀ g ∈ C.gates, isNot g=false) ∧ C.gates.countP (fun g => !isNot g) ≤ (if u then 13 else 14) := by
    by_cases hn : ∀ g ∈ C.gates, isNot g=false
    · refine ⟨false,fun _ => hn,?_⟩
      have := List.countP_le_length (p:=fun g => !isNot g) (l:=C.gates)
      simp only [Bool.false_eq_true,ite_false]
      omega
    · refine ⟨true,by simp,?_⟩
      push Not at hn
      obtain ⟨g,hg,hx⟩ := hn
      have lt : C.gates.countP (fun g => !isNot g) < C.gates.length := by
        rcases Nat.lt_or_ge (C.gates.countP (fun g => !isNot g)) C.gates.length with h | h
        · exact h
        · have eq := List.countP_eq_length.mp (Nat.le_antisymm List.countP_le_length h) g hg
          simp only [Bool.not_eq_true'] at eq
          exact absurd eq hx
      simp only [ite_true]
      omega
  obtain ⟨u,mono,count⟩ := mode

  have out := get_rep (u:=u) (execute C.gates inputs) C.output
  rw [goalEq] at out
  unfold Repr at out
  have pg : bit 0 graph = false := by decide +kernel
  rw [nrm_id pg] at out
  obtain ⟨k,S,hk,run,sub⟩ := extract C.gates inputs legal mono graph_proper
    (out.resolve_right (fun h => h graph_proper))
  have ns : inputs.all plainWord = true := by decide +kernel
  rw [nrm_map ns] at sub
  have idx (a : Sig) (ha : a ∈ inputs) : ∃ i : Fin 9, inputs.getD i.val zero = a := by
    rw [←input_list] at ha
    exact List.mem_ofFn.mp ha
  have eq : S = inputs.toFinset := by
    ext a
    constructor
    · exact fun h => List.mem_toFinset.mpr (sub a h)
    · intro ha
      obtain ⟨i,rfl⟩ := idx a (List.mem_toFinset.mp ha)
      apply raw_required run inputs (inputs.getD i.val zero) sub (absentRow10968 i) (presentRow10968 i)
        (requiredInputs.1 i)
      intro v hv hn
      obtain ⟨j,rfl⟩ := idx v hv
      apply requiredInputs.2 i j
      rintro rfl
      exact hn rfl
  exact ⟨u,k,hk.trans count,eq ▸ run⟩

theorem directSplit
    (m : ∀ k, k ≤ 14 → ¬Live false graph k inputs.toFinset)
    (s : ∀ k, k ≤ 13 → ¬Live true graph k inputs.toFinset) :
    ¬ PEqualNP.MetaComplexity.HasCircuitSize 9 edge 14 := by
  rintro ⟨C,legal,small,computes⟩
  obtain ⟨mode,k,hk,run⟩ := twoRoots C legal (funext computes) small
  cases mode
  · exact m k hk run
  · exact s k hk run
def g145Y : Array (Bits × Bits) := #[(0x3ff63ff63ff63ff63ff63ff63ff63ff63ff63f,0x49204920492049204920492049204920492049),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0xc7fbc7fbc7fbc7fbc7fbc7fbc7fbc7fbc7fbc7,0x92409240924092409240924092409240924092),(0x0,0x0),(0x0,0x0),(0xf8fdf8fdf8fdf8fdf8fdf8fdf8fdf8fdf8fdf8,0x24812481248124812481248124812481248124),(0x0,0x0)]
def g145C : List ColumnInfo := []
def g145A : List (List Nat) := [[],[116],[64],[64,112],[112,64],[112]]
def g145D3 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x7
def g145L : Nat → Packing
  | 3 => (1,0,1,0,0,0,0,g145D3)
  | _ => emptyPacking
def g145I (_ _ : Nat) : Option (Nat × Nat) := none
def g145 : Forest := ⟨145,3,fun i => g145Y[i]?.getD (0,0),g145C,g145A,g145L,g145I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g145P3_0 : block g145 3 0 1=true := by
  apply cellsBlock (ar:=3) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g145B3 : block g145 3 0 1=true := g145P3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g145T : checkedTables g145 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g145 0 0 0 = true)
  · exact (rfl : block g145 1 0 0 = true)
  · exact (rfl : block g145 2 0 0 = true)
  · exact g145B3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g145G : graphValid g145 (boundsBefore []) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowS145 : Lower true (varsX 145) (graphGoal 145) 4 := lower_forest (g:=g145) (i:=0) (hints:=4) (before_sound [] baseKnown) g145G g145T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KS145 := extendKnown [] 4 [(145,[]),(292,[32,16,84,135])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VS145 : Known true KS145 := extend_ok (m:=145) baseKnown lowS145 (by decide +kernel)
def g102Y : Array (Bits × Bits) := #[(0x0,0x0),(0xf71fc7ff03fffff8f71fc7ff03fffff8f71fc7,0x710490a285040120710490a28504012071049),(0xbe838fffc07e3ff0be838fffc07e3ff0be838,0x4368db4c326089204368db4c326089204368db),(0x0,0x0),(0x0,0x0),(0xeee63ffffff803ffeee63ffffff803ffeee63f,0x8872490408512400887249040851240088724),(0x193dc0fffffffc00193dc0fffffffc00193dc0,0x982db6e083060384982db6e083060384982db6),(0x0,0x0),(0x0,0x0)]
def g102C : List ColumnInfo := []
def g102A : List (List Nat) := [[],[81,98]]
def g102D3 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xf
def g102L : Nat → Packing
  | 3 => (1,0,1,0,0,0,0,g102D3)
  | _ => emptyPacking
def g102I (_ _ : Nat) : Option (Nat × Nat) := none
def g102 : Forest := ⟨102,3,fun i => g102Y[i]?.getD (0,0),g102C,g102A,g102L,g102I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g102P3_0 : block g102 3 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g102B3 : block g102 3 0 1=true := g102P3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g102T : checkedTables g102 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g102 0 0 0 = true)
  · exact (rfl : block g102 1 0 0 = true)
  · exact (rfl : block g102 2 0 0 = true)
  · exact g102B3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g102G : graphValid g102 (boundsBefore KS145) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowS102 : Lower true (varsX 102) (graphGoal 102) 4 := lower_forest (g:=g102) (i:=0) (hints:=17827152) (before_sound KS145 VS145) g102G g102T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KS102 := extendKnown KS145 4 [(102,[]),(163,[32,117,101]),(178,[66,50,117,101]),(195,[32,117])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VS102 : Known true KS102 := extend_ok (m:=102) VS145 lowS102 (by decide +kernel)
def g147Y : Array (Bits × Bits) := #[(0xfdf00fff81fc7e3ffbe01fff03f8fc7ff7c03f,0x45c09245142904808b81248a28520901170249),(0xe6a8703ffe007fc7cd50e07ffc00ff8f9aa1c0,0x96a9b6d618b228112d536dac316450225aa6db),(0x0,0x0),(0x0,0x0),(0xfbb781ffffff8007f76f03ffffff000feede07,0x235249820c03122046a49304180624408d492),(0x0,0x0),(0x0,0x0),(0x64ffe3ffffffff80c9ffc7ffffffff0193ff8,0x24920410040040004924082008008000924),(0x0,0x0)]
def g147C : List ColumnInfo := [(2,0,145,0,4)]
def g147A : List (List Nat) := [[],[64]]
def g147D4 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1f
def g147L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,g147D4)
  | _ => emptyPacking
def g147I (_ _ : Nat) : Option (Nat × Nat) := none
def g147 : Forest := ⟨147,4,fun i => g147Y[i]?.getD (0,0),g147C,g147A,g147L,g147I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g147P4_0 : block g147 4 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g147B4 : block g147 4 0 1=true := g147P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g147T : checkedTables g147 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g147 0 0 0 = true)
  · exact (rfl : block g147 1 0 0 = true)
  · exact (rfl : block g147 2 0 0 = true)
  · exact (rfl : block g147 3 0 0 = true)
  · exact g147B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g147G : graphValid g147 (boundsBefore KS102) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowS147 : Lower true (varsX 147) (graphGoal 147) 5 := lower_forest (g:=g147) (i:=0) (hints:=116) (before_sound KS102 VS102) g147G g147T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KS147 := extendKnown KS102 5 [(147,[]),(294,[32,132,84,117])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VS147 : Known true KS147 := extend_ok (m:=147) VS102 lowS147 (by decide +kernel)
def g110Y : Array (Bits × Bits) := #[(0x0,0x0),(0xe003ffc07ffffffe003fffff80ffd386b20f0f,0x41a8128d052280541a82502916291304a21111),(0xfffc00007ff01fffffc007ffff01a37d4800f0,0x81311b160644c89893136232244d835c485555),(0xffffffff80001ffffffff80000003f407df000,0x5c05c18178702e01c0380bc38703340753333),(0x0,0x0),(0x1ffffffffffffffe663f7600ff,0x1602602058081301202404c00000642314aaaa),(0xffffffffffffe0000000000000019dd38dff00,0x1803800060001c01c038070040808c9308cccc),(0x0,0x0),(0x0,0x0)]
def g110C : List ColumnInfo := []
def g110A : List (List Nat) := [[],[50,101]]
def g110D4 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1f
def g110L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,g110D4)
  | _ => emptyPacking
def g110I (_ _ : Nat) : Option (Nat × Nat) := none
def g110 : Forest := ⟨110,4,fun i => g110Y[i]?.getD (0,0),g110C,g110A,g110L,g110I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g110P4_0 : block g110 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g110B4 : block g110 4 0 1=true := g110P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g110T : checkedTables g110 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g110 0 0 0 = true)
  · exact (rfl : block g110 1 0 0 = true)
  · exact (rfl : block g110 2 0 0 = true)
  · exact (rfl : block g110 3 0 0 = true)
  · exact g110B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g110G : graphValid g110 (boundsBefore KS147) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowS110 : Lower true (varsX 110) (graphGoal 110) 5 := lower_forest (g:=g110) (i:=0) (hints:=17851728) (before_sound KS147 VS147) g110G g110T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KS110 := extendKnown KS147 5 [(167,[48,32,117,101])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VS110 : Known true KS110 := extend_ok (m:=110) VS147 lowS110 (by decide +kernel)
def g179Y : Array (Bits × Bits) := #[(0xf003ff87fe1fffc01ffff87fffe474a4007c1f,0xa12845108440228940a01108826014a45294a5),(0xfffc0007ffe1ffffe00fffffc0335be20f83e0,0xc030162028040b0182c0a00108225922318c63),(0x0,0x0),(0x0,0x0),(0xfffffff80001fffffff0007ffccfd11df0001f,0x240980130884c020302c2120087c108a5294a),(0x1ffffffffff80004d2fe80003e0,0xb82e045c111702c140b005c104d26c9ce739c),(0x0,0x0),(0xfffffffffffe000000000000033aa61bfffc00,0xc03000600018030180c046021182211084210),(0x0,0x0)]
def g179C : List ColumnInfo := [(0,32,145,2,5),(32,0,147,0,5),(1,0,178,0,4),(2,0,145,0,4),(2,32,145,0,4),(16,0,163,0,4)]
def g179A : List (List Nat) := [[],[64]]
def g179D4 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x5bd4940
def g179D5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x20128240d140ff40fd40fd20
def g179H5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x60
def g179D6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x163440df
def g179H6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1e45a16f9
def g179L : Nat → Packing
  | 4 => (1,2,3,0,0,0,0,g179D4)
  | 5 => (3,1,3,0,0,5,0,g179D5)
  | 6 => (1,0,3,0,0,0,0,g179D6)
  | _ => emptyPacking
def g179I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 2 0 4 0 0 g179H5
  | 6 => lookupWord 1 5 0 7 2 1 g179H6
  | _ => fun _ => none
def g179 : Forest := ⟨179,6,fun i => g179Y[i]?.getD (0,0),g179C,g179A,g179L,g179I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g179P4_0 : block g179 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g179B4 : block g179 4 0 1=true := g179P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g179P5_0 : block g179 5 0 3=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g179B5 : block g179 5 0 3=true := g179P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g179P6_0 : block g179 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g179B6 : block g179 6 0 1=true := g179P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g179T : checkedTables g179 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g179 0 0 0 = true)
  · exact (rfl : block g179 1 0 0 = true)
  · exact (rfl : block g179 2 0 0 = true)
  · exact (rfl : block g179 3 0 0 = true)
  · exact g179B4
  · exact g179B5
  · exact g179B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g179G : graphValid g179 (boundsBefore KS110) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowS179 : Lower true (varsX 179) (graphGoal 179) 7 := lower_forest (g:=g179) (i:=0) (hints:=1048660) (before_sound KS110 VS110) g179G g179T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KS179 := extendKnown KS110 7 [(179,[]),(211,[101]),(358,[32,132,101,84,117]),(422,[32,132,117,100])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VS179 : Known true KS179 := extend_ok (m:=179) VS110 lowS179 (by decide +kernel)
def g181Y : Array (Bits × Bits) := #[(0xc00fff0ffffffc00fffff0fffeea3a5303f03f,0x84a08a210802284a0280220882200a53145145),(0x0,0x0),(0xfff0000ffc3fffff003fffffc009adfd000fc0,0xc42c405090b10c4b11404108092d994d34d3),(0x0,0x0),(0xfffffff0003fffffffc000fffd77e88afc003f,0x90130026104c0100c0584120152a08828a28a),(0x3fffffffffff00012697f4000fc0,0x2e09c08b822702609026009c11269264b2cb2c),(0x0,0x0),(0xffffffffffc0000000000000039d530dfff000,0x300e000c00380380e03808e0208d5104c30c30),(0x0,0x0)]
def g181C : List ColumnInfo := [(0,4,145,32,5)]
def g181A : List (List Nat) := [[],[116],[82],[82,116],[64],[64,112],[64,82],[64,82,112],[112,64],[112],[112,82,64],[112,82]]
def g181D5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x3f
def g181L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,g181D5)
  | _ => emptyPacking
def g181I (_ _ : Nat) : Option (Nat × Nat) := none
def g181 : Forest := ⟨181,5,fun i => g181Y[i]?.getD (0,0),g181C,g181A,g181L,g181I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g181P5_0 : block g181 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g181B5 : block g181 5 0 1=true := g181P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g181T : checkedTables g181 5 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g181 0 0 0 = true)
  · exact (rfl : block g181 1 0 0 = true)
  · exact (rfl : block g181 2 0 0 = true)
  · exact (rfl : block g181 3 0 0 = true)
  · exact (rfl : block g181 4 0 0 = true)
  · exact g181B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g181G : graphValid g181 (boundsBefore KS179) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowS181 : Lower true (varsX 181) (graphGoal 181) 6 := lower_forest (g:=g181) (i:=0) (hints:=2098436) (before_sound KS179 VS179) g181G g181T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KS181 := extendKnown KS179 6 [(181,[]),(309,[32,84,135]),(405,[133,101]),(421,[32,84,116,100,134]),(433,[82,50,131,99]),(436,[32,16,65,49,83,115,99,134])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VS181 : Known true KS181 := extend_ok (m:=181) VS179 lowS181 (by decide +kernel)
def g227Y : Array (Bits × Bits) := #[(0x7fffffc01fffff8003ffc01ffe000db5f91c0,0x50a50548542805506a824834144160595996db),(0xf8007ffffe00ffffffffffffffffff35e1fe3f,0x60060010000200600300100000800800613249),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0xffff80000000ffffffc00001fffff3f14c6007,0x84c8566198cca9854c2b6159590a43f10c4db6),(0xfffffffffffe0000013ead8038,0x6f06782e170ce06703382619e13813e8c8db6),(0xffffffffffff00000000000000000cea9e5fc0,0x70078030180f007803c0381e01c04a2864924),(0x0,0x0)]
def g227C : List ColumnInfo := [(32,0,195,0,4)]
def g227A : List (List Nat) := [[],[101]]
def g227D4 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x3f
def g227L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,g227D4)
  | _ => emptyPacking
def g227I (_ _ : Nat) : Option (Nat × Nat) := none
def g227 : Forest := ⟨227,4,fun i => g227Y[i]?.getD (0,0),g227C,g227A,g227L,g227I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g227P4_0 : block g227 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g227B4 : block g227 4 0 1=true := g227P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g227T : checkedTables g227 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g227 0 0 0 = true)
  · exact (rfl : block g227 1 0 0 = true)
  · exact (rfl : block g227 2 0 0 = true)
  · exact (rfl : block g227 3 0 0 = true)
  · exact g227B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g227G : graphValid g227 (boundsBefore KS181) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowS227 : Lower true (varsX 227) (graphGoal 227) 5 := lower_forest (g:=g227) (i:=0) (hints:=17825879) (before_sound KS181 VS181) g227G g227T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KS227 := extendKnown KS181 5 [(227,[]),(230,[32,101,117])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VS227 : Known true KS227 := extend_ok (m:=227) VS181 lowS227 (by decide +kernel)
def g119Y : Array (Bits × Bits) := #[(0xfffffffffffffffffff569564be49d7500003f,0x482a452129148521214161560be09c05555555),(0xffff000003fffff0000bf42d4ef262a9fc0fc0,0x14c000db00026400669b0244a9260200c30c3),(0xfffffffffc0000000008e7ccb19b907603f000,0x82701609c05837820b88e70c909290763cf3cf),(0x0,0x0),(0xfffffffffffffffffffd0b1e74157ff000003f,0x1380984e026138044c0c0a08741563f0aaaaaa),(0xc8af3b7e9c20e03ffc0,0x1c00e0700381c008700408d325690208c30c30),(0x6754a985f269dfc0000,0xe000ff8003fe000f8006454a904d069df3cf3c),(0x0,0x0),(0x0,0x0)]
def g119C : List ColumnInfo := [(0,1,102,16,5)]
def g119A : List (List Nat) := [[],[81,98],[64],[64,81,98]]
def g119D5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x7f
def g119L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,g119D5)
  | _ => emptyPacking
def g119I (_ _ : Nat) : Option (Nat × Nat) := none
def g119 : Forest := ⟨119,5,fun i => g119Y[i]?.getD (0,0),g119C,g119A,g119L,g119I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g119P5_0 : block g119 5 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g119B5 : block g119 5 0 1=true := g119P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g119T : checkedTables g119 5 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g119 0 0 0 = true)
  · exact (rfl : block g119 1 0 0 = true)
  · exact (rfl : block g119 2 0 0 = true)
  · exact (rfl : block g119 3 0 0 = true)
  · exact (rfl : block g119 4 0 0 = true)
  · exact g119B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g119G : graphValid g119 (boundsBefore KS227) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowS119 : Lower true (varsX 119) (graphGoal 119) 6 := lower_forest (g:=g119) (i:=0) (hints:=17827156) (before_sound KS227 VS227) g119G g119T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KS119 := extendKnown KS227 6 [(119,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VS119 : Known true KS119 := extend_ok (m:=119) VS227 lowS119 (by decide +kernel)
def g183Y : Array (Bits × Bits) := #[(0x3ffffffffffffff6783aaace149000fc003f,0x5820a821282148142283aa8c8048145145145),(0xffffffc0003fffc00b82dca6b831203f000fc0,0x29005300db0099066b825ca2a01100c30c30c3),(0x3fffffffc0000009cd1cd9425e200003f000,0x4e109c109c10de0b89cc1cd8025c24d34d34d3),(0x0,0x0),(0x3ffffffffffffffa162d5a1393dfc000003f,0x7004e004e004e00c081605421313128a28a28a),(0xffc00000000000000915e285ddcf000003ffc0,0x270027002700100011a2055d820b2cb2cb2c),(0x0,0x0),(0x4ea977125e06ffffc0000,0x80380038003800200440801104e06c30c30c30),(0x0,0x0)]
def g183C : List ColumnInfo := [(4,0,179,0,7)]
def g183A : List (List Nat) := [[],[64]]
def g183D7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x7f
def g183L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g183D7)
  | _ => emptyPacking
def g183I (_ _ : Nat) : Option (Nat × Nat) := none
def g183 : Forest := ⟨183,7,fun i => g183Y[i]?.getD (0,0),g183C,g183A,g183L,g183I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g183P7_0 : block g183 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g183B7 : block g183 7 0 1=true := g183P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g183T : checkedTables g183 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g183 0 0 0 = true)
  · exact (rfl : block g183 1 0 0 = true)
  · exact (rfl : block g183 2 0 0 = true)
  · exact (rfl : block g183 3 0 0 = true)
  · exact (rfl : block g183 4 0 0 = true)
  · exact (rfl : block g183 5 0 0 = true)
  · exact (rfl : block g183 6 0 0 = true)
  · exact g183B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g183G : graphValid g183 (boundsBefore KS119) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowS183 : Lower true (varsX 183) (graphGoal 183) 8 := lower_forest (g:=g183) (i:=0) (hints:=1049940) (before_sound KS119 VS119) g183G g183T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KS183 := extendKnown KS119 8 [(183,[]),(423,[32,132,117,100]),(435,[130,50,99]),(438,[32,64,48,131,117,99])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VS183 : Known true KS183 := extend_ok (m:=183) VS119 lowS183 (by decide +kernel)
def g231Y : Array (Bits × Bits) := #[(0x1ffffe0003ffffc0004cf47f38c1c4a0f8000,0xd40549405680a9480ab4c543f3041c48739ce7),(0xfe000000003ffffffff9f4784b320bfdf07c1f,0x98000d800b0001900121d010022008d8108421),(0xffffffffffc00000000273b2d655ec120003e0,0xe0918e048c1231e091c273b2d6102812b5ad6b),(0x0,0x0),(0x0,0x0),(0xfffffffffffffffffffa859f07c5f6a40003ff,0x12610091024c2012200040d01c5d6254a5294),(0x2456978fe6252007c00,0x1c7e011e038fc023c02056978de6203ef7bde),(0x73aa5b8895b2bff8000,0x1f8001e003f0003c0022aa4088943238c6318),(0x0,0x0)]
def g231C : List ColumnInfo := [(0,1,102,128,5),(0,4,195,32,5),(1,0,230,0,5),(4,0,227,0,5),(64,0,167,0,5),(32,4,195,0,4),(128,1,102,0,4)]
def g231A : List (List Nat) := [[],[32,117]]
def g231D5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1be41
def g231D6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1ac6881ff
def g231H6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xc0
def g231L : Nat → Packing
  | 5 => (1,1,3,0,0,0,0,g231D5)
  | 6 => (1,0,3,0,0,0,0,g231D6)
  | _ => emptyPacking
def g231I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 2 0 4 0 0 g231H6
  | _ => fun _ => none
def g231 : Forest := ⟨231,6,fun i => g231Y[i]?.getD (0,0),g231C,g231A,g231L,g231I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g231P5_0 : block g231 5 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g231B5 : block g231 5 0 1=true := g231P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g231P6_0 : block g231 6 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g231B6 : block g231 6 0 1=true := g231P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g231T : checkedTables g231 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g231 0 0 0 = true)
  · exact (rfl : block g231 1 0 0 = true)
  · exact (rfl : block g231 2 0 0 = true)
  · exact (rfl : block g231 3 0 0 = true)
  · exact (rfl : block g231 4 0 0 = true)
  · exact g231B5
  · exact g231B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g231G : graphValid g231 (boundsBefore KS183) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowS231 : Lower true (varsX 231) (graphGoal 231) 7 := lower_forest (g:=g231) (i:=0) (hints:=17827159) (before_sound KS183 VS183) g231G g231T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KS231 := extendKnown KS183 7 [(231,[]),(246,[32,64,48,117]),(498,[64,130,48,50])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VS231 : Known true KS231 := extend_ok (m:=231) VS183 lowS231 (by decide +kernel)
def g243Y : Array (Bits × Bits) := #[(0xffffffff8007ffffffdc9363d9415ac00f801f,0x90a048102502488120c93218140528a5294a5),(0xfffffffffffc002a44b4afe8f401f07fe0,0x2c000a00000010008a00a0aa803006318c63),(0x0,0x0),(0x0,0x0),(0xffff00000007ffffffef798a1a360b7e00001f,0x1230092c04a049202422608a1a240954a5294a),(0xfffffffffff8000000201b64366f4d800003e0,0x5c40ae3028c571c147201b44146f4db9ce739c),(0x24569b45573c00007c00,0x9f80cfc04f067e027824561b45570c39ce739c),(0x13aa5dc49781bfff8000,0xe000f000700780038011085444138021084210),(0x0,0x0)]
def g243C : List ColumnInfo := [(32,0,211,0,7)]
def g243A : List (List Nat) := [[],[101],[64],[64,101]]
def g243D7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x7f
def g243L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g243D7)
  | _ => emptyPacking
def g243I (_ _ : Nat) : Option (Nat × Nat) := none
def g243 : Forest := ⟨243,7,fun i => g243Y[i]?.getD (0,0),g243C,g243A,g243L,g243I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P7_0 : block g243 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g243B7 : block g243 7 0 1=true := g243P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243T : checkedTables g243 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g243 0 0 0 = true)
  · exact (rfl : block g243 1 0 0 = true)
  · exact (rfl : block g243 2 0 0 = true)
  · exact (rfl : block g243 3 0 0 = true)
  · exact (rfl : block g243 4 0 0 = true)
  · exact (rfl : block g243 5 0 0 = true)
  · exact (rfl : block g243 6 0 0 = true)
  · exact g243B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243G : graphValid g243 (boundsBefore KS231) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowS243 : Lower true (varsX 243) (graphGoal 243) 8 := lower_forest (g:=g243) (i:=0) (hints:=17825876) (before_sound KS231 VS231) g243G g243T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KS243 := extendKnown KS231 8 [(243,[]),(486,[32,132,101,117])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VS243 : Known true KS243 := extend_ok (m:=243) VS231 lowS243 (by decide +kernel)
def g311Y : Array (Bits × Bits) := #[(0x3fffffffffffffffff1685c8b653b7c000003f,0x8a4151484a290a44141605c896413355555555),(0xfffff80000ffffe0009e42fc7d4c8400000fc0,0x2c0a65836cb04c88669e42fc350c8433cf3cf3),(0x3fffffffff00000000af785c83b0ab00fff000,0x13800270006f00b88b305c8010aa030c30c3),(0x0,0x0),(0x3fffffffffffffffffd0b1c4a9bfd48000003f,0x309c061380c27010c0c0b00429bec4aaaaaaaa),(0xc00000000000000000c8af2b5ecc4a7f03ffc0,0xe0001c00038001000089014ac0404c30c30c),(0x0,0x0),(0x0,0x0),(0x6754b7112b657ffc0000,0x3f0007e000fc001e006444a2112b0530c30c30)]
def g311C : List ColumnInfo := [(0,1,294,16,6)]
def g311A : List (List Nat) := [[],[130],[64],[64,130]]
def g311D6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x7f
def g311L : Nat → Packing
  | 6 => (1,0,1,0,0,0,0,g311D6)
  | _ => emptyPacking
def g311I (_ _ : Nat) : Option (Nat × Nat) := none
def g311 : Forest := ⟨311,6,fun i => g311Y[i]?.getD (0,0),g311C,g311A,g311L,g311I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g311P6_0 : block g311 6 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g311B6 : block g311 6 0 1=true := g311P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g311T : checkedTables g311 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g311 0 0 0 = true)
  · exact (rfl : block g311 1 0 0 = true)
  · exact (rfl : block g311 2 0 0 = true)
  · exact (rfl : block g311 3 0 0 = true)
  · exact (rfl : block g311 4 0 0 = true)
  · exact (rfl : block g311 5 0 0 = true)
  · exact g311B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g311G : graphValid g311 (boundsBefore KS243) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowS311 : Lower true (varsX 311) (graphGoal 311) 7 := lower_forest (g:=g311) (i:=0) (hints:=8590984532) (before_sound KS243 VS243) g311G g311T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KS311 := extendKnown KS243 7 [(311,[]),(407,[32,132,117,101])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VS311 : Known true KS311 := extend_ok (m:=311) VS243 lowS311 (by decide +kernel)
def g437Y : Array (Bits × Bits) := #[(0xffffffc1ffffc92d389940f740000007fc01ff,0x80a2008441100829308000f708a45229148a45),(0x0,0x0),(0xffffffff81a52a0abb8d8801ff00003fe00,0x12c0450008209a50a02b1090026130984c2613),(0x0,0x0),(0xfff00001ffffefe1835e2102c0000ff80001ff,0x304160882402700815a2100d148a45229148a),(0xfffffffe0000209965726e4d3fe0000003fe00,0x240098001381208141106c4d0582c160b0582c),(0x0,0x0),(0x24d69a05573c00000ffffc0000,0x3808e0111c0200d60a05560826130984c26130),(0x132a5dc49781bffff000000000,0xc00f0021e004012a1cc48300b81c0e070381c0)]
def g437C : List ColumnInfo := [(0,1,292,144,6),(0,4,145,288,6),(0,16,292,129,6),(0,32,145,260,6),(0,128,292,17,6),(0,256,145,36,6),(1,0,436,0,6),(4,0,433,0,6),(16,0,421,0,6),(32,0,405,0,6),(128,0,309,0,6)]
def g437A : List (List Nat) := [[],[133],[116],[116,133],[82],[82,130],[82,116],[82,116,130],[130,82],[130],[130,116,82],[130,116],[32,84,135],[32,84,116,132],[32,132,84,117],[32,132,117],[32,64,80,135],[32,64,80,112,128],[32,64,128,80,117],[32,64,128,117],[32,112,84,64,132],[32,112,84,128],[32,112,132,80],[32,112,132,84,80],[64],[64,133],[64,112],[64,112,133],[64,82],[64,82,130],[64,82,112],[64,82,112,130],[64,130,82],[64,130],[64,130,112,82],[64,130,112],[80,32,66,135],[80,32,66,116,132],[80,32,132,66,114],[80,32,132,114],[80,66,135],[80,66,112,128],[80,66,130,114],[80,66,130,112,32],[80,114,66,132],[80,114,66,64,128],[80,114,132],[80,114,132,64],[112,64],[112,64,133],[112],[112,133],[112,82,64],[112,82,64,130],[112,82],[112,82,130],[112,130,64,82],[112,130,64],[112,130,82],[112,130],[128,32,66,84,117],[128,32,66,117],[128,32,84,114],[128,32,84,116,66],[128,66,80,117],[128,66,117],[128,66,82,32,114],[128,66,82,114],[128,114,66,80,84],[128,114,66,84],[128,114,84,64],[128,114,84]]
def g437D8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xa98765432102ff
def g437L : Nat → Packing
  | 8 => (1,0,4,0,0,0,0,g437D8)
  | _ => emptyPacking
def g437I (_ _ : Nat) : Option (Nat × Nat) := none
def g437 : Forest := ⟨437,8,fun i => g437Y[i]?.getD (0,0),g437C,g437A,g437L,g437I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g437P8_0 : block g437 8 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g437B8 : block g437 8 0 1=true := g437P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g437T : checkedTables g437 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g437 0 0 0 = true)
  · exact (rfl : block g437 1 0 0 = true)
  · exact (rfl : block g437 2 0 0 = true)
  · exact (rfl : block g437 3 0 0 = true)
  · exact (rfl : block g437 4 0 0 = true)
  · exact (rfl : block g437 5 0 0 = true)
  · exact (rfl : block g437 6 0 0 = true)
  · exact (rfl : block g437 7 0 0 = true)
  · exact g437B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g437G : graphValid g437 (boundsBefore KS311) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowS437 : Lower true (varsX 437) (graphGoal 437) 9 := lower_forest (g:=g437) (i:=0) (hints:=8592033028) (before_sound KS311 VS311) g437G g437T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KS437 := extendKnown KS311 9 [(437,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VS437 : Known true KS437 := extend_ok (m:=437) VS311 lowS437 (by decide +kernel)
def g247Y : Array (Bits × Bits) := #[(0xf71d5750119a8355f2a6c4320000ff000000ff,0x410d5750010a8154f226002015151515151515),(0x809e4bd873461a0d44223e700ff00ff00ff00,0x6009c08004344120d442020703030303030303),(0x2bc5c88dae5895e205f3a0e00000000ff0000,0x829c5c88d2e4091e204f32064f4f4f4f4f4f4f),(0x0,0x0),(0xfbf2a182a4161cba4977d412ff0000000000ff,0xaf0a080841418a00951d4122a2a2a2a2a2a2a),(0x8264b344869b6e518791d3900000000ffff00,0x82203340809b6c108300d38b0b0b0b0b0b0b0),(0x93534d287c9ef0209acb5cc000000ff000000,0x934345283c9ae0209acb5c8fcfcfcfcfcfcfc),(0x4ca924f70cd3e0baf802a80ffffff00000000,0x402000f70c1260b00802880c0c0c0c0c0c0c0),(0x0,0x0)]
def g247C : List ColumnInfo := [(0,4,211,32,8),(4,0,243,0,8),(64,0,183,0,8),(0,64,181,2,7),(1,0,246,0,7),(16,0,231,0,7),(32,0,211,0,7),(32,4,211,0,7),(0,1,102,144,6),(0,16,102,129,6),(2,0,181,0,6),(2,64,181,0,6),(128,0,119,0,6),(1,16,102,128,5),(17,0,230,0,5),(128,1,102,16,5),(128,16,102,1,5),(129,16,102,0,4)]
def g247A : List (List Nat) := [[],[64]]
def g247D6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x3097d8794760d5f7394560
def g247D7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x6082880c28b1028808ace0c161c030fcf8b0e01639e99964a402feb8ec1df94760efca2b077e514c2bebb4a377dcd60
def g247H7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x37e
def g247D8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x30b28922718510388286000f40f30b28922718510388286001134c2892271a51440e20a18004113cd2892271851220a18003cf38c2892271851220a18003cf34c2ca2489c694510388286001240f30b2a79a59030a180d2a79a59030a1809a522870962408900f000ffd87fd61ffd83fd60ff4c3fd10df5977e51
def g247H8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x85c30000001b3c0000d091e20000008400000000
def g247D9 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xb398a4104047f
def g247H9 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x15c038c0001580000000000000001b2280000000000000000000000000000000000000000035790000000000001c800008000004403f4000002
def g247L : Nat → Packing
  | 6 => (2,3,5,0,0,3,0,g247D6)
  | 7 => (6,2,5,0,0,8,0,g247D7)
  | 8 => (8,1,5,0,0,10,0,g247D8)
  | 9 => (1,0,5,0,0,0,0,g247D9)
  | _ => emptyPacking
def g247I : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 1 2 0 5 1 0 g247H7
  | 8 => lookupWord 2 23 0 8 3 1 g247H8
  | 9 => lookupWord 2 59 1 8 3 1 g247H9
  | _ => fun _ => none
def g247 : Forest := ⟨247,9,fun i => g247Y[i]?.getD (0,0),g247C,g247A,g247L,g247I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P6_0 : block g247 6 0 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g247B6 : block g247 6 0 2=true := g247P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P7_0 : block g247 7 0 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P7_2 : block g247 7 2 4=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g247B7 : block g247 7 0 6=true := (@block_merge g247 7 0 2 4 g247P7_0 g247P7_2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P8_0 : block g247 8 0 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P8_2 : block g247 8 2 6=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g247B8 : block g247 8 0 8=true := (@block_merge g247 8 0 2 6 g247P8_0 g247P8_2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P9_0 : block g247 9 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g247B9 : block g247 9 0 1=true := g247P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247T : checkedTables g247 9 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g247 0 0 0 = true)
  · exact (rfl : block g247 1 0 0 = true)
  · exact (rfl : block g247 2 0 0 = true)
  · exact (rfl : block g247 3 0 0 = true)
  · exact (rfl : block g247 4 0 0 = true)
  · exact (rfl : block g247 5 0 0 = true)
  · exact g247B6
  · exact g247B7
  · exact g247B8
  · exact g247B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247G : graphValid g247 (boundsBefore KS437) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowS247 : Lower true (varsX 247) (graphGoal 247) 10 := lower_forest (g:=g247) (i:=0) (hints:=17827156) (before_sound KS437 VS437) g247G g247T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KS247 := extendKnown KS437 10 [(247,[]),(487,[32,132,117]),(499,[130,50]),(502,[32,64,48,131,117])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VS247 : Known true KS247 := extend_ok (m:=247) VS437 lowS247 (by decide +kernel)
def g375Y : Array (Bits × Bits) := #[(0xbaad5d0d78056bc21b38a5c0000000000003ff,0x8aad590978056ac21a38204555555555555555),(0x82ccf2f582768288becec0e00000ffc00ffc00,0x82888215827482089ec8c0a30cc330cc330cc3),(0x69b4819308b55c53f6816a9003ff003ff00000,0x29b4809100844813e68168803c0f03c0f03c0f),(0x0,0x0),(0xf5418ea6a4aac12247f88d90000000000003ff,0x754086a684aa812045c08d9aaaaaaaaaaaaaaa),(0x4c9330085dcbae344d52537ffc00003ffffc00,0x440330080c03240401120350c0300c0300c030),(0x6a6cd6ea9e8415ffa03619000000ffc0000000,0x686454ea1c8015f72036190cf33ccf33ccf33c),(0x0,0x0),(0x952a4f3b5578326d10e5b80fffff0000000000,0x90084f22517812681064900f03c0f03c0f03c0)]
def g375C : List ColumnInfo := [(0,1,358,16,8)]
def g375A : List (List Nat) := [[],[130],[64],[64,130]]
def g375D8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xff
def g375L : Nat → Packing
  | 8 => (1,0,1,0,0,0,0,g375D8)
  | _ => emptyPacking
def g375I (_ _ : Nat) : Option (Nat × Nat) := none
def g375 : Forest := ⟨375,8,fun i => g375Y[i]?.getD (0,0),g375C,g375A,g375L,g375I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g375P8_0 : block g375 8 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g375B8 : block g375 8 0 1=true := g375P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g375T : checkedTables g375 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g375 0 0 0 = true)
  · exact (rfl : block g375 1 0 0 = true)
  · exact (rfl : block g375 2 0 0 = true)
  · exact (rfl : block g375 3 0 0 = true)
  · exact (rfl : block g375 4 0 0 = true)
  · exact (rfl : block g375 5 0 0 = true)
  · exact (rfl : block g375 6 0 0 = true)
  · exact (rfl : block g375 7 0 0 = true)
  · exact g375B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g375G : graphValid g375 (boundsBefore KS247) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowS375 : Lower true (varsX 375) (graphGoal 375) 9 := lower_forest (g:=g375) (i:=0) (hints:=8607761748) (before_sound KS247 VS247) g375G g375T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KS375 := extendKnown KS247 9 [(375,[]),(471,[32,132,117])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VS375 : Known true KS375 := extend_ok (m:=375) VS247 lowS375 (by decide +kernel)
def g439Y : Array (Bits × Bits) := #[(0x4484654115f52ea25f87000000000ff80001ff,0x4084254105152ea05b06229148a45229148a45),(0x8289b929b2222aec33e80000001ff00003fe00,0x8289212932222ae831e861b0d86c361b0d86c3),(0xf89a258e20557019d0c8007fc0000007fc0000,0xa09a25882045701140c80984c26130984c2613),(0x0,0x0),(0xb0664bb95626830b80bb00003fe000000001ff,0xb0204ab81222800b80b945229148a45229148a),(0x9b598a4289b8d92aa1cff8000000007fffe00,0x9049804009881028a14160b0582c160b0582c),(0x0,0x0),(0x2e4a165acbc86174053400003ffffff8000000,0xc421002c8c841140400984c26130984c26130),(0xd52160534a2adc6d5842ffffc0000000000000,0x542140534a220c6c1002e070381c0e070381c0)]
def g439C : List ColumnInfo := [(2,0,437,0,9),(1,0,438,0,8),(4,0,435,0,8),(16,0,423,0,8),(256,0,183,0,8),(0,1,294,144,7),(0,4,147,288,7),(0,16,294,129,7),(0,32,145,262,7),(0,128,292,19,7),(0,256,147,36,7),(17,0,422,0,7),(32,0,407,0,7),(128,0,311,0,7),(260,0,179,0,7),(1,128,292,18,6),(2,32,145,260,6),(4,32,145,258,6),(16,128,292,3,6),(32,4,147,256,6),(32,256,147,4,6),(36,0,147,0,5)]
def g439A : List (List Nat) := [[],[130],[32,132,117],[32,64,128,117],[64],[64,130],[128,32,66,117],[128,66,117]]
def g439D6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x637e1b7350950
def g439D7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xa2069a902a6a2a00f4780ddf73d0950ddf7350950dd77348550
def g439H7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xd0
def g439D8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x3c3054504522182c3450462a98305490d1412264b95223a60d162638688141407cc972a4c88e98345890d1028280f24447eed624464c78b0e030911203f76b1220364c78b0a03b7090f911e2838089321c7796f400a60f800ffe85a87ff42543fea12a1fd48750fea42a873f54952fbb8aa977dcd50
def g439H8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x5000000000000006156004900f0001200
def g439D9 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x4d23ee32b2892071859048c38828418005944913eeaca2481c61641230e20a1060016513b8d32b2892071859048c38828418005ae34c2ca2481c61641230e20818004ee30b2892071859048c38820600125133ee34c2ca2481c61641230e208180059444fb8d2ca2481c61641230e208180055344f38d30b2892071859048c308180055344eac69230a100af4b48afa467514a31842003fe54ff553fc54ffd43fd50ffd03fd40ff483f521
def g439H9 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x62c0021c0000000000b18000001ee10000061a00001218000068c22c6c00448a2001c0c0fc0
def g439D10 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x72c8310403ff
def g439H10 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x2e2800000a9400000000000007c240b6230180000148e43207b22f8972765486d8c000000018c40000000000000000800a8800000e500021200000000000000ea20000000000000000082000000000000000002270440200000000049c00
def g439L : Nat → Packing
  | 6 => (1,4,5,0,0,0,0,g439D6)
  | 7 => (3,3,5,0,0,6,0,g439D7)
  | 8 => (8,2,5,0,0,10,0,g439D8)
  | 9 => (9,1,5,0,0,10,0,g439D9)
  | 10 => (1,0,5,0,0,0,0,g439D10)
  | _ => emptyPacking
def g439I : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 1 2 0 4 0 0 g439H7
  | 8 => lookupWord 1 17 0 8 2 2 g439H8
  | 9 => lookupWord 3 29 3 10 3 3 g439H9
  | 10 => lookupWord 6 67 4 11 4 3 g439H10
  | _ => fun _ => none
def g439 : Forest := ⟨439,10,fun i => g439Y[i]?.getD (0,0),g439C,g439A,g439L,g439I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g439P6_0 : block g439 6 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g439B6 : block g439 6 0 1=true := g439P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g439P7_0 : block g439 7 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g439P7_1 : block g439 7 1 2=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g439B7 : block g439 7 0 3=true := (@block_merge g439 7 0 1 2 g439P7_0 g439P7_1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g439P8_0 : block g439 8 0 3=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g439P8_3 : block g439 8 3 2=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g439P8_5 : block g439 8 5 3=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g439B8 : block g439 8 0 8=true := (@block_merge g439 8 0 3 5 g439P8_0 (@block_merge g439 8 3 2 3 g439P8_3 g439P8_5))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g439P9_0 : block g439 9 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g439P9_1 : block g439 9 1 8=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g439B9 : block g439 9 0 9=true := (@block_merge g439 9 0 1 8 g439P9_0 g439P9_1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g439P10_0 : block g439 10 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g439B10 : block g439 10 0 1=true := g439P10_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g439T : checkedTables g439 10 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g439 0 0 0 = true)
  · exact (rfl : block g439 1 0 0 = true)
  · exact (rfl : block g439 2 0 0 = true)
  · exact (rfl : block g439 3 0 0 = true)
  · exact (rfl : block g439 4 0 0 = true)
  · exact (rfl : block g439 5 0 0 = true)
  · exact g439B6
  · exact g439B7
  · exact g439B8
  · exact g439B9
  · exact g439B10
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g439G : graphValid g439 (boundsBefore KS375) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowS439 : Lower true (varsX 439) (graphGoal 439) 11 := lower_forest (g:=g439) (i:=0) (hints:=8590984532) (before_sound KS375 VS375) g439G g439T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KS439 := extendKnown KS375 11 [(439,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VS439 : Known true KS439 := extend_ok (m:=439) VS375 lowS439 (by decide +kernel)
def g503Y : Array (Bits × Bits) := #[(0x29c60154c0000000000001fff0000000001fff,0x29c00050851528a9454a2a51528a9454a2a515),(0xc1cd5283a0000000003ffe000fff8003ffe000,0xc18d4202a3031818c0c6063031818c0c606303),(0x28d3cc32a000fff80000000000007ffc000000,0x28d2cc12a04f027813c09e04f027813c09e04f),(0x0,0x0),(0xd48cc1c040000007ffc0000000000000001fff,0xc40cc1804a2a51528a9454a2a51528a9454a2a),(0x5638ad993fff00000000000000007fffffe000,0x1620018900b005802c01600b005802c01600b0),(0x2350d04740000000000000000fff8000000000,0x225090455cfce7e73f39f9cfce7e73f39f9cfc),(0x90120a2d80000007fffffffff0000000000000,0x1012082d10c086043021810c086043021810c0),(0xae2930685ffffff80000000000000000000000,0x800930605f00f807c03e01f00f807c03e01f00)]
def g503C : List ColumnInfo := [(64,0,439,0,11),(0,64,437,2,10),(1,0,502,0,10),(4,0,499,0,10),(16,0,487,0,10),(256,0,247,0,10),(0,1,358,144,9),(0,4,211,288,9),(0,16,358,129,9),(0,256,211,36,9),(2,0,437,0,9),(2,64,437,0,9),(32,0,471,0,9),(66,0,437,0,9),(128,0,375,0,9),(1,16,358,128,8),(4,256,211,32,8),(16,1,358,128,8),(17,0,486,0,8),(32,4,211,256,8),(32,256,211,4,8),(65,0,438,0,8),(80,0,423,0,8),(128,1,358,16,8),(128,16,358,1,8),(256,4,211,32,8),(260,0,243,0,8),(320,0,183,0,8),(1,64,436,2,7),(5,0,498,0,7),(16,64,421,2,7),(32,64,405,2,7),(36,0,211,0,7),(36,256,211,0,7),(64,32,145,262,7),(64,128,292,19,7),(96,0,407,0,7),(128,64,309,2,7),(129,0,358,0,7),(129,16,358,0,7),(144,1,358,0,7),(192,0,311,0,7),(288,4,211,0,7),(292,0,211,0,7),(3,64,436,0,6),(6,64,433,0,6),(34,64,405,0,6),(65,128,292,18,6),(66,1,292,144,6),(66,16,292,129,6),(66,32,145,260,6),(66,128,292,17,6),(66,256,145,36,6),(68,32,145,258,6),(80,128,292,3,6),(96,256,147,4,6),(130,64,309,0,6),(192,1,294,16,6),(258,64,181,0,6),(320,32,145,6,6),(67,128,292,16,5),(70,32,145,256,5),(81,128,292,2,5),(82,128,292,1,5),(98,4,145,256,5),(322,4,145,32,5),(322,32,145,4,5)]
def g503A : List (List Nat) := [[],[130],[32,132,117],[32,64,128,117],[64],[64,130],[128,32,66,117],[128,66,117]]
def g503D7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1c53c25c01c00893e080540529a1d917915815a11a0df09e05f01a0065485463c5bc01c00b52771370a1dc4dc2d41f810962e929d17d1561160de05f00458ba4a787ec6344d837c26c1f817c0151a4450e30ca2234720fc0072b7a16879859064c6bb53c1e8528ac1a57e9f8350a515828f25ca84c0ae3b0724d656538390960f41acb3a706a12c1e8359574e0d425830e654f06a12e2b060e4a9e19425c510
def g503D8 (j : Nat) : Nat := if 3 ≤ j then 0 else (if j<1 then 0x17c2783e05207401a08b0bd14a27430c5608c0de1742783e05600da2944f87c8ae0de17c2783e05204a07488810b17c27c3e45f84f07c0bc01705309d90e1f22ec4f06f09e0f817802e10d10d19a2f4528aa11e17817802b0be94c27c3f4618ae11c1bc2f84e07c0ac01b45cca70f515c2383785f09c0f81281d00631712884f87c8b91422ac4f08d11c1b03585f09c0f81701f009494b2724387c89b1161d83784b07c0bc018c5e4a70f91362183106f0960f817802e4a490e1f63344d8860de12c1f02f0058a0e2e25387d8cc16a2784706d0be12c1f02f01c00f940c5e4a70fb19a26c458760de12c1f02f006832044660cbd14a2743105785f09e0fc17003769fd95f630d7a35c1d63f568d2733a4cd1b264c68f0ccc086f60ba52dc8b3c6c25ad66a8da75e916a2067d69d8a6f999665a392da4008e062c087fe128819dfe87d79ef57a5de2e75e1cf97241c066e1db0869499de657d8f661dd7cc5c2d65556514e951253884b4923d464911e4250ff43dd4ebf37a0cfb30e8bb02cc4abd28749b4252c8d721607c31cb86ba18ec5bc15204b310a435d0b4c254075412a0254000cdf6634294760cf7e0d91d09609df6a74294560ed7e0f4294560ed7e0d42945609df6a74294530b5fe9d4294530cafe879859064caf6879859064b5de9d424c651d9b5959490b60bd92855490b60b796849750b60f8b5967450b60f8b5957450b60bd92855450b6097b2a5425c760e79e49815c760e79249815c760e79909815c760e79509815c760cdb6624294760cdb6614294760cf964981d0760e975c965e0d60ea79d164e0d60ea75d164e0d60e9759154e0d60e9759783d0960d9b5959490960bd92855490960cf36538390960b796849750960f8b5967450960f8b5957450960bd92855450960e73e5f8350960e7325f8350960ee39d38350960ee35d38350960c77e5f8350960e975978350960e73e0e42dc560e73e0d42dc560e73e0f925c560e73e0c925c560e73e0e425c56097b2a5425c560e73e0d425c560cd76538394560cf3e0d92d0560e75e0d7150560d9d5909155130d9b5959490930bd92855490930b796849750930f8b5967450930f8b5957450930bd9285545093097b2a5425c530d8f6516494530f2d5917150530c3fe5f8650910c3fe5c86509108dd6a76420554ad568f6420554b596848759542b2d6908658571a3daa36458571a792a14258571cb9e59824c741acbea15490b60a97e9165e0d60ad528554e0d60e935978390960ea35938390960e935978350960c5765f8394560c8f6199494740ad528554e0d4098fe999494540a6d2a17150540d2de597150540cb3e598350720b992859559120d8b6516494520f295917150520e39e1b925c510e39e18925c510e39e1a425c5109792a5425c510e39e19425c51089d6a76420554 else (if j<2 then 0x81302b02604f86708dc4e08410e17c1b83e05e00a3646a8d1389410e15c1f02f004833328c38c658bb14e2ac4e08f07c0ac0981b007039d21a31c5e8a715a2684408d0fa1741f02c04e0540a12424640c717c29c5709713c224448780fc1b82f04e04e0580b806006015d21c3e4640c31442b84f08d11c1b82f04d0780f81580414cd17528a414678b50ea178178070058c2183c9c50717927c3f0670890f01f83704d07c0bc07004649b8be14e2ac4d09e1181f83585a0bc1381381602e018023265c5f0a71562684989e1181f83585a0bc1241f02702c05c03004e4a493e1f2320618a215c2784688c0fc1b82f04d07c0ac022a668ba94527e2dc4b8550ba0f817802d592a0a2ea4f8778ba10a1dc2e83e05e00ca2ea4fc5b89a10e1542f02f004d17f16e25c2a85507c0bc010a668ba93f16a2543e83e05e009d27a41c5e8a715a2684408d0fe1742e83e05809c0a8142595a2932c5f45e8a611a16c1f02f005da2932c5f45e8ad0b60f817802519b1792924345e8a912c2342d83e05e00c62f25345e8a912c2083685b07c0bc0172c98bc94921a2f45308d0b60f817802c50020e2e25387d0cd17a2b0570830fc1b82702f01c010940c5e4a68bd14c2342d83e05e00a06608d5129fa2ea2944d08e04a054016c5e4668bd1521e42c83e05e0090672b911b1792922e4530890bc0bc016c5f8928c41922a05709e11c1f83705e09c0f816803e4848c818e2f85709e1121e03f06e0bc1381381602e00c023c4b8748c81862885709e11c1b03705e09a0f01f02b0080c21822838bc93e25c3b0670890f01f83704d07c0bc07004649f12717c2ac4d09e1181f83585a0bc13813816027f12717c2ac4d09c0fc1ac2d05e0920f813816027494e25c3a4640c31442b84f08c0fc1b03705e09a0f815804450717129c4b8750cd17a2b0570830fc1b82702f01c010e24a290508ae13c2383f06e0bc1381f021026894e2522c45509e11c1f83606e09c0f81381f01c00f527c3f85d0a512a1e83683e05e00a044a4e8770ba14a2543d06f09a0f8178030d402233065e8a51331d43105785f09e0fc17003a8998f31d43305188f0ae13c1f82e0058420822e890698d2f44f4770c51741fc2703f05a0740200e0d10a213025c8a510c1742744687d0dc1702f84f07e0bc06804c1c12113025c8a59392623ac660b613a2343e86e0b817c2783f05e03402a4834c697229a3ac660bc14c2744686e0be12c1f82f01a011a28a3e8660b51141e83785d0960fc1780334870f61c62fc2f84d07c08c0901b005b94726e30c598ac11e17c1f023025033c2f652c9f0eb1862b04606f0ba13c1f02b007690d18e2e84785d07c09c0b8025592a2d21e2e84785d07c0bc013a534638ba11a1fc2e83e04e05c014a514870e514a2684385b09e0f816802c0e31722844f87c8a015e else 0x2c81782521d60d008c08e4a40eb17206400c27f827020c11c90a1d60f40c811a48585d02189fe0d40f8109c1a81f020e1441803105e09b8b714e25c438770de15c2b84706e0bc03804a1442183105e0a413026e2dc5389710e1dc378570be11c2383704e07c03805b4c193d1061f42583e03c0089212320638be14e2b84b89e1122243c07e0dc17c2704e04e05c0180534870fe1d2320618a215c2784688e0dc1782683c07c0ac0223086093a14008249f0fe1d8338448780fc1b82683e05c07c07004e49b8be14e2ac4d09e1181f83585a0be13827027027c99717c29c5589a1262784607e0d61682f84e0920f81381464a493e1fc3a4640c31442b84f08d1181f83705e09a0f815804850020129c3f8750cd17a2b0570830fc1bc2704e05c07c07004a97a94521c3e8748b91502944d0871141b42c05f08e0f81780a009830a5ea528748b91502944d0871141883405f08e0f81780a00952f52844d4850e91722a0550871141883405f08e0f81780a00952f542a814a50e91722a0550871041e83405f08e0f81780a0090b204b2881170f61ca2904d8860d616c1f0250280500203085902594408b87b0e514826c4306b0b60f812814028011542a3245c8a81542144287a0de1381780a006b9371962ec538a7138210438770ae0f))
def g503H8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xe614510000030000f700000060000000f800003572
def g503D9 (j : Nat) : Nat := if 10 ≤ j then 0 else (if j<5 then (if j<2 then (if j<1 then 0x6b2ac9215dbe595490badf0eb2a85d6c8759542f96b2ce8a17cb5957450aedf2caa2851fd98d9371aeec9ec9b8d7d64764dc6b7b28432e35f990219718ff4c6c8b8d7764f645c6beb23b22e35bd94d8971afac8ec4b8f3de19615c79e90cb0ae35f79458571e7bb22c2b8f3d591615c7bcf04b0ae3de48258571ef3212c2b8f79509615c6bef2c90ae35dd93e01719bfcb30928cdf6626494767b09324a3e3f6499251baec9cc928ddb64a64946eeb23324a337d9859251d9ec22c928cdf66064946ef320324a3b6d8690a51f973248528edb61942947ceac898ca3f66424c651fb2a126328dede5161d07d6ac8b0e83be58258741b7bcb263a0ebd61931d06f6f2898e83eb5644c741df2c1263a0e7de19715073eb0cb8a83db5645c541b3fca2cbb069f59584d826ff30aa6c17749155360f36b2c85b07ab59242d83e5aa9216c1e6d6550b60cfac0ae3b04df66251d82afb2f28ec167f9459560bba48aa8b06d75d7835835bac9c1ac1b5d54e0d60f36b2c84b07ab59242583e5aa9212c1bcf8390960f36b2a84b06f3e0d425833bf07b8ac19df835c560abecbca2b06d7e0e5158357ac8c0e8137d9894740d3f434a3a069f61a51d02e7b2928e81b6d8294740f97214a3a06af61941d023fb23c3a81e3d659d140f1eb2ae8a05dd245545036baa9c1a811fe98dc540cefc1ee2a067de07715023f930b8a819df835c540cbfc3ca2a05cf652515036bf0728a816bf9650540edab8a82a059fe51654c2ee922aa261e6d6590930f56b2484987cb552424c3cdacaa126157d9794530bb6ca4a3905bbe5941c8379b06a0e41e6d9559120e76b22e2905db65251483cdac928a41ead6450520ef2b8a82906bbe1a424435d90d21221aef8650910d76432848873de59714433ef08b8a21cf5645c510ef3c92e28877924971443bcc84b8a21de5425c510b7bcb2e2886bde1971442def2ca0a21eb5645051093f4c684b2e1fa1d85d931bb0f41ec9a5d85a0f64c6f43b07b269761583d931ed0f40ec98f587a0764d6b41d03b26b560e81d934eb0ac0ec963f9459664d2eb2b073269b59582992ce922c2ac963f9459564a5ecbec8b25a764f64592d6b23b22c927f9859464d36c12ca324afe61641934f2cac00c9ab96460064d3bb2102aa69d590815534dacac2485e2d6599242b97cb2a9215d92455490abcb2243a85e2d659d142f16b2ae8a15d92455450a1fb31b26e34bd942197187f4c6c8b8d7a640825c63d930a12e35e79258571a7bcb242b8c9fe598494747b08b24a3975874c651c7bc32e2a0f2d591715074bacbc1ac127f9859740d36b2b05a06ab61a42d0317f0eb228193f8755140d2eb2f06a06a759383502ec922aa641acd6460f20ce6c1ee39047be6171c8339b06b8e41b2f8455120bb248aa89055b65e5148257b28432218f7865c510 else 0xcf9ecf8c8f7a4f66cf520f348f224f09ceec4ed3ceb8ce9b4e7a0e5b4e418e22ce040deccddbcdc0cda98d924d7ecd6a0d504d3a4d258d094cf48ce24cc60cad8c8ecc7b4c654c4ccc380c1bcc048bee8bdc4bcb4bb54ba30b858b680b494b2a8b094af0cad48ab70a9c0a838a638a488a33ca1b49fa09dc89ca49b6c9a34983496989510940091d890a08fa48e6c8ce48be88a88892887f08690854483d082ac81387fec7eb47d7c7bcc7a80792077fc769c752873dc72b8716c70206f386e006c786adc697c68086680650c6398623861145f8c5e2c5ca45b4459e4583456705510538851ec50504edc4d7c4bcc4a3048e4475c45c0449c438c422c40903f803e703d743c503b4039f438f837d436d835a0347c33943298318830642f7c2e802d842c742b502a542958285c274c263c255424802398229c21b420e020341f601e641d541c581b481a6019641804170815e414c0140012a0114010940f840e740d780c900ba80a84099c088c076806bc05c004d803f002f401f801100001bff4260760fbfa14a3b05ff64742583efe8528ac1f7d4294560bfec8e84987df5ca514c3efe8528a61f7d4294530fbab926328fddd0931947eea8498ca3ebe7459360f3eb22a9b079f59742d82fdb29216c1f6d5490b60ef7cba85b077b25d42d83f5ce8a16c1fad7450b60fb6aa285b06fb90981d837da84c0ec1dee42dc760ef6a16e3b077be4971d83bd924b8ec1dee425c760ef6a12e3b077d48571d82efb2928ec1f6e4294760fb6a14a3b05fb64b41d837eb03a0ec1df57150760f5f3a2c8b07af5d164583e7ce8aa2c1e7d6455160f3eb2e84b06f7e0f42582fdb29212c1f6d5490960ef7cba84b077b25d42583f5ce8a12c1fad7450960fb6aa284b079f595425837bf06a12c1dee42dc560ef6a16e2b077be4971583bd924b8ac1dee425c560ef6a12e2b077d48571582efb2928ac1f6e4294560fb6a14a2b06f7e0f41582fdb25a0ac1bdf8350560efab8a82b07af9d1644c3d7ae8b2261f3e7455130f9eba2a89879f591544c3cfacab9261e7d65d0930bf6ca484987db552424c3bdf2ea1261dec9750930fd73a284987eb5d1424c3edaa8a12615ff9750930f3eb2a849873f593714c3bdc85b8a61ded42dc530e7fcb2e29873f591714c3bdf24b8a61dec925c530ef7212e29877b509714c3bea42b8a6177d9494530f3eb24a2987db90a514c3eda8528a61ebd64d0530bf6c9682987af591414c3beae2a0a61aff865c910d7e432e4886bfe1b424435f90da12217f591d0910affcba84886bfe19424435f90ca1221a7f63e1975d3eb1f0cbae9f595869934fb0bc02c97749161564f1f3a2cab278f5d16559357f30b20c9abd6460464d3fc36c8aa5d764f64552eeb23b22a9a7f8659154dbbb2102aa6dd590815536dacac2485f2d6599242f9) else (if j<3 then 0xb921c5912c2f09c1f05c018190450a42647f164470ac2707c17006064110300bc2909c18c5f0bc2707c170068300ba2889a1845815c2f09c1f0440803401c0ba288651683f0bc230681f0540d006054140300b82809f17c2f09c1f05c01909c2306316c540dc2f09c1d04c0b006264152440a02708f170370bc2707417006844cc32e8a226c72190570bc2707c1600684490a2889a190570bc2707c16005c210631703f0bc2704c0b0040144be2106316c570bc2607c1302c016cc32f8831c45e0dc2f0981f0440d00604588418456118370bc2607c150058842084109e1903f0981f05c01509b1744e0f42f09c13024432c5d1383d0bc260701f04c0950a427061158460f8370bc2607c150061444c12f0a527466178520bc2707c170069444c12f086178541382f09c1f05c0184c12e0a527466178521382f09c1f05c01a4bc2848e17854124360bc2305c01610029466178521243e0bc2507c170060821c1460d5314b92747417849104390dc2307c1700897c1694649c2105e1243f0941f05c0181f03f4a527464140570bc2707c140200e00706a1103e4a12685015c2f09c1f0480803801c8a22147a134430b42707c1122027c1724710c2989d21864170501544f09c1f05c022910420a227484170501544e118350bc2707c1303c022c5b150470bc1e04c0b00422889e1e861160570bc27078110200d006c2987c18c5c0f0370bc250701e04c0b0068548b8294861fc5d11c2f0941e05c018190448861fc5a1283709c1e05c0168ba2187d1684a0dc27078150340161162989e18c5b150440dc2d09c1e04c0b0070641122889f170440dc2f07817005c438be2187d18456118370bc260781500686ad9056d10420bc20c6716c5411c2e05c01c15a2f45d148450b8170040428b9280861f45d1542f0881e05c01810a2f4a02145d1544a1142e05c0168b92809e1f45a0dc2f098150340174a42787d18456118370bc260781500612989e1e451138460cc2f0981e0540181a84587e178540dc2f09c1e05c016915428bd294861f05d1283709c1e05c01be225e13de041df31de21dd39dc15daddda09d881d695d4e5d2f9d06dce1dcc1dc9cdc7e1c61dc481c2d1c0d1be81bc1dba31b86db659b495b2a9b0bdaee5acd1aae5a8bda6e5a50da2e5a10d9f359dad9b3598bd970d952192e5910d8f358dad8c118a2587998611846182c580c57f297d8d7bc97a057805761973f1726970b96ee16ccd6b4569e5685d66d5652562e960ad5ec15cc15ae9594d57c5563d543d52b550794ec94d194b7d49b947cd45e14445429540e53f213d713bc139e937fd35fd344d324d30892ed92d152aed28d9275125b523c921f120a51f6d1d451b6d1a0d18ad177515ed147912dd119110090e810cbd0abd094907d5066104c50365022d00f4ff80fdd0fc70fb4 else (if j<4 then 0x171162e0a426c861e45b134460cc2f09c1e05c01eca32789318861178511584e1183e0dc2e0b8270781e0440a78bd2949e258751906114056138460f8370b82e09c1e0781500a6254851906317856138460dc2e0b8250701e04c0a0289645162548717856138460d0370b82e0941c078170180258be254861cc5e1584e118340dc2e0b8250701e04c0a02c0274a62546418c5e1584e1143c0f8370b82e0941e04c0a029129891218761845014448138460f8330b8270781e0540241aa438be2187b18451138470b82f0981e0440d00402310e2187d1945d1445611c2e0bc260781700706b570428b82e8851d465174551284011c2d0b81405c050098730bd2909e1f46316c53138460dc2f0981e04c0b008b449122e4a22787b1945d14455138460d42f0981e0580f009e2eca22787b18451138460dc2e0bc2607811034010089448bb284a22787b19455138460dc2f0981e0540d0089448b9298791c465174511544e114460d0370b82f0981e0580f00a8805762e4a42787d1845914c4e114460d0330a42f0981e0580f01402d190448bd2187d1985e14855108370b42f0941e05c023190454861e8751985e14855108300dc2d0bc250781203c02721464115428bd2987d1985e148551143a0dc2d0bc250781700a485190454a61e8751985e148551143a0dc2d0bc250781203c0281d22e4a12187c1644e1183e0d42c0bc270781303c060092448b928c9d2187b1905d128420e83709c1e05c020088649122e4a3274861ec641744e1183e0d42c0bc270781303c0600a8758b928c992187c1644e10c430f8320d42c0bc23078170180298b92987c1644e10c460c8350b02f08c1e05c060080658b9284861ec641744e10c460c8350b02f08c1e05c060099418b92987b1905d1384310c3a0f8320d42c0bc23078170180284a12187c1644e1183e0d42f09c1e05c060075294861f05d134420d42f09c1e05c050069454a52787d19064170501584e0f8370bc27078170089448b92849e1f05c140561344d1183e0dc2f09c1d0781303c0281c83f4811885815c2f0941f0480803801a110300be27865174530bc2707c1503401a8a62748b2186716c4b0b42707c170060458a62748e18c5b14c4f0b42707c1302c01c110300be2747e19c5d10c2d09c1f05c01a110300be2989d1f86316c5511c2d09c1f04c0b0080440c02f89e1945d14c2f09c1f05c0180c02e8a626c861945d14c4b0bc2707c170070458a626c8e1945d15c2b09c1f05c018110300be2989b1f8651745311c2b09c1f05c01e190440c02f8a62786117c2f09c1f04c0b00703f0c42e8a22686117c2f09c1f045c2707c18c5b150470b42707c1302c0188bc2906316c540fc2f0941c07c1302c01a1f06a188601162989e184570bc2707c150074310ba2889917c2f09c1f054040058641103 else 0x34000098781152949e1f8751906114056138460f8370b82f098270781e05402c510454861f46418c5e14c5612c4e114460dc2e0bc260941c0781302c02e5925e5152187f1785613845118340dc2e0bc260941c0781701802b4861f87317856138460d0370b82f098250701e04c0a02c026510451052987d19063178531584b138451143c0f8370b82f098250781302c03297a4550d294861e871164501544a1083a0d4280bc270781700802a1784a1161e8711404a0dc2f09c1e04408034000081284861f8761845014448138460f8330bc2609c1e078150099441103eca32787b188611785115849138460f8370b82f098270781e0440d010034198458bd2949e1f8751906114056138460f8370b82f098270781e05402f0bb28c861cc5b14c4c10c2d09c1e04c0b00706611b44ca32687319c5b150470bc1e04c0f007c2eca32787318c5b14c4c11c2d09c1e04c0b0079441152187d19063178531584b13845118370b82f098250701e04c0a02c0200c964939454861fc5e1584e114460dc2e0bc260941c078170180298bd2187e1cc5e1584e118370b82f098250701e04c0a02c0275122f4861d467168470b42b0941e05c01a510451052987d19063178531584b138451143c0f8370b82f09825078130280b008037515428bd2987519c5a1143f0b42b0941e05c01e19d328be1d45d148450ac270781700606750a2f4a52187517455128450ac27078170079284861f8761845014448138460f8330bc2609c1e078150098668be1d455128470ac27078150340181924e1302809e1f45d1504c110370bc270701e05c0220fa2e8a22787a18450128370bc27078110200d0000220a22787a1c8651405513c2f09c1e0540803401e8ba280a22787a194501544a0dc2f09c1e054080340220f8398ba2889e1e4501444e0dc2f09c1e0440d00822e8a02987a19455128420e8370a82f08c1a078150340258bb204861f45512c460dc2f08c1e0540d0070588b82809e1e065174501544d11c2f09c1d0781203c0241a0650b8280861f86316c50130350bc270781700861ec5b1544d1183e0d42c0bc270781404c0a027e1ec5b1544d1183e0d42c0bc270781404c0a0278458bc2909e1f87418456138460f8370b82f098270781e0540400a8450ba2889a18c5b14c4c110370b4270781302c02019056152448be2787e1945d1404a0c42f09c1e05c022192448be2786517452108350ac270781700706418457152448be2787e18459148350bc2707817008874190428b82989e1f86517451128350a02f09c1e05c0241922f0a6274861945d1544a108350ac270781700822e8a22187e19452128330bc270781503401c0fe2e8a22787914051138370bc27078110200d0080448be290a6278651544a108370ac27078150340210a42787d174560dc2f09c1e05c0))) else (if j<7 then (if j<6 then 0xc2707c170140300b8701a1304ba288811d05a134450f4360b02f09c1f05c0500994490d314ba28c9e214731905c14056124410e43709c1f05c0100a870172424c12e8a32649e204731905e134450f4360b02f09c1f05c0500b86451944909304ba28c99278811cc64170501584d1143d0d82c0bc2707c170140341d07151d314ba28c9a21474170521344310c3d0cc360b02f08c1f05c0500c0714c52e4ba294741705213443114330d82c0bc2307c170140281c06551d314ba2849a214731905c1584d10c450cc360b02f08c1f05c0500c06490a414c52e8a51cc64170561344310c390f4330d82c0bc2307c170140305b15e51b30cb9270831d05e124410e4370941f05c010090744bc2908617854124460ac270741700686c178461103ecc32f4a526c75190501404f0bc2707c140200e00a8440fd314b92849d1c4621404f0bc2707c120200e0000241103f4c52e4a127471188501484d0dc2f09c1f0480e0091304b9280a1264711985613c2f09c1f0580e0079304a0284991f47119856124470ac2707c1603802011d314b9280a51c46615849104390dc290bc230641f0580e00a0474c52e4a02849d1c4621584911c2f09c1f0580e0088440fd314bd2949d1d4621404f0bc2707c160000201f878198440fd314b92849d1c46214052134370bc2707c120200e00b1304b9284991c4621404f0bc2707c120200e0000200a1264891c466158490dc2f09c1b0580e00706412a4711044cc32f4831d4621484d114370b42f0941f0480e00802c91844cc32f48420c7119856134450cc370bc2507c160380262106412c4411542cc32f4a31d4621484d1143d0dc2d0bc2507c120380200c130ca228c9d1ec66134470b42707c160280e0078654c42cc822147b1984d10c370ac2d08c1f0580e008884195310b3288a51ec66134430ec370ac2d08c1f0580e00984490d314ba2889d1c8641705015c2f09c1f05c02051a424c12e8a2260721905c1405613845118370bc2707c1303c0500b2434c52e8a51c86417055108420e8370bc2307c17014024111318a62647e1905c158491183e0dc2d09c1f05c0228a22747a1905c154470b42707c1203c050070444c2288991e864164470b42707c170068641122889d1e8641784d118370b42707c1303c05008d308a51e864174420e8370b42307c1701401c9b25e91a44cc32f0a6274831d864170501544a1083a0dc2707c1700802e1724691442cc32f0a6274831d8641744a1083a0d4280bc2707c1700802e1f87819a44cc32e0a2274831c864170501544e118330d42f09c1f04c0f00c1441142aca32787b188611785115849138460f8370b82f098270781e0440b01d8448ad2949e1f463170531504b130440f0370b02f090270701e050130200b00d06e1252949e1e875184581404a0dc2f09c1e044080 else 0x8140480f01402a1ad268701d4661785414855134450e8350bc250941e0501203c0500b46411a2e0bd294861f4661785414855134450e8300dc2d0b425078140540a03c0500d86b190454821c0751985e150521544d1143a0dc2d0bc250941e050150280f0140341762e4601885815849124410f8370bc250641e040170040278b92787e1d066178511204e1043e0dc260941c0781603c0600a5428b82f49d2187e1785414855134450e8370b42f09425078140480f014030115274821c0761785414855134450e8370b42f09425078140480f01402e0f4370a420c7c170531504b1182b09c1f0500e0084290831f05c14c5412c460ac2707c140200e0078440c02f0a42607418c5c14c5412c4c1103c0dc2c0bc2409c1c07c1404c0b0040000d8601162989d1f863174531544b134450f4370b42f094270741d04c0b00b8761b05e118458c62f8a627876184570bc2707c150088770c42e89b2145b1383e0cc2a0bc2707c150300d008c310bb2145b1383e0cc2a0bc2707c150300d00786415050110300b82809f1684a108370bc270681f05c03009864170300b8280981945d1504c110370bc270701f05c024114420f9304bc290991d0621605d1485213c2f09c1f0580200a0450a4264791d06617856124470ac2707c1603802115045109304bc290991c8681b0621784f0bc2707c16038026114424c12f0a4264741885d1485213c2f09c1f0580400802611330cba2889b1c86414c4b10c3b0dc2b0bc2309c1b07c130580200b07e1e06611330cba2889b1c86414c4b10c3b0dc2b0bc2309c1b07c130580200cb30cbc20c7418c5b14c4c1103c0dc2c0bc2704c0b0040244c12f8811d06316c53138460d4370bc2607c130240b0091304be2047418c5b14c4e118350dc2f0981f04c0902c02411330cbc278831d06116451138460dc2e0bc2607c110340100a5314ba2889d1d865174531283b0a82f0981f0540d008a414c52e89d1d865174520ec2f0981f0540d007b30cbc26c7316c551383e0d42c0bc2704c0b007c32cc32ec7316c551244e0f8350b02f0981c07c1302c02510b30cbc2909b1d06116451138460f8370b82f0981f0440d00402a19054511304bc294991d466178501282f09c1f05c022191454991e4751985e144460ac2707c1700706515c54511304bc294991d462168560bc2707c170089444c12e0a420476178541382f09c1f05c01c1d42848c2047617854124360bc2706c170071304b8294991d46617852138280bc2707c170078650a5278811e4751985e158491182b09c1f05c020194424c12f0a5278811d4621685015849104390d8280bc2707c1700402e4c12e49c20476178561243e0bc2507c170071304b9270811c85a14056124410e4360a02f0941f05c010098821d1464c12e8a220474170501484d1143d0d82c0b) else (if j<8 then 0x140540f01402e1995d93c471162e4a61f06116452138451183d0f8340c42e09c1e078170180500d17789614c4a138421183e0c8330a82e09c1e06c1e05c0600995589614c4a138460f8320cc2a0b82606c1e05c06008e2f8961d45e14c4a138460f8330a82e09c1e06c1e0540c029e2f8961d45e14c4a138460f8330a82e0981b0781503009009a2f891180651785514c561344e1183e0d82e0981e0540c0240d00ad278942586518c5e154531544c138441143c0f8340d42c0b8240941c0781404c0a0240b81cc25485190631785514c561344e110450f03e0d0360b42e090250701e050130280902e1644ce2e4a6244861c46019c5e1584e104380f8300d8290b82605c0600c0318be254861c46018c5e14c5612c4e118340dc2e0b42e0941c078130280902c032591338b92849e2587419c5e14c4a138410e03e0cc290b8250781701802e591418b9278961d06717856104380f8330a82e0941e05c0600a1858b9278961dc5e14c4a138440f8330a8290b82605c060099658be25877178531284e1103e0cc2a0a42e0841e05c06009e2e4a1278961c46018c5e14c5612c4e1103e0d0360b42e0941e04c0a0240b00c9338b9278961d067178511204e1043e0d8250701e05c06009d278942548418c5e154531584d138450f03e0d0370b82d0b8240941c0781404c0a0240b8593448be2486517454144561183e0d42c0b8270781e04c0f01802a593444ce2f8961c86517454158460c8350b02e08c1a0781701802ad11338be258721945d150561083e0c8350b02e08c1e05c0600a1748b9298912186517454144511204e1183e0d42e0981e04c0f01802c593448b928c9e2486517454144551304e1183e0d42e09c1e0781303c0600c1758b929891200861d8651745414448138430e83e0c8350b823078170180318b9298961d8651745414448138460c8350b8230681e05c0600a1658b929891218721945d15054138460c8350b8230681e05c0600a9418b9298961c865174541504e10c3a0f8320d42e08c1e05c0600aa7d8bb27891218761845c138430e83e0c8310b8230681e05c0600c02c1f1444fe2f8961c861140561244e1183e0dc2e0b8260781102402a5122e4a624865150511584d138460f8360b826078150300903402a591458be244861c865150561344e118320d82b0b8230681e0540c03402e611645162e4a625872194541584d138420f8320d82b0b823078150300d00c164516244601945d150511584d138441183e0d0370b82e0981d0781303c0600ce2f8961c4601945d15056138410e03e0c0360a42e0841e05c0600a9444a1278911c46517454144561344e1183e0d0370b82e0981d0781303c0600cc7c5762e4a625874184591484e1183d0f8340c42e0981e05c0601402c8b82f49e1f4661785414855134450e8350b42507 else (if j<9 then 0x580f0180300b878179441113e0fb2987e1c861140561244e1183e0dc2e0bc2609c1e0781102403459144113204861f872194541584d13843118360ac2e08c1a078150300d00c1845914411342903284a61f872194541584d138431083e0d82b0b823078150300d00d92987e1c4601945d1505613841104380f8360a42f098210781603c0600ba5e1154349e1e8701d461164501544d108450e8300dc2f098170140200b8791795c174444a61f874184591484e114460f43e0c42f098270781e0580f0180500dc671384d11e1f8531284e10c460f8320cc2a0b8270781b0781503c0600b9645544e1314587e14c4a138431183e0c8330a82e0981b0781503c0600be2f87d178531284e1183e0c8330a82e09c1e06c1e0540c029866510444a61e871180651785514c561344b138431183e0dc2e0b8270781b078120540c0240d00f8721352146418c5e154531584d12c4e114450f03e0d0360b42e094250701e050130280902c0200f8474ca2f4a52107519c5d1544a100450fc2d0b41e0501503c0500a965939338b9284861e46019c5e1584e104410e03e0d8290b82605c0600c030510458bd2187e1c46018c5e14c5612c4e114460dc2e0b42f098250701e04c0a0240b00e165939338b92849e1f067178531284e104380f8330a42e0941e05c0600b965939401062e49e1f87419c5e158410e03e0cc2a0bc260941e05c0600b98593e2e49e1fc5e14c4a138440f8330a8290b82605c06009965939338be1fc5e14c4a138440f8330a8290b821078170180298b92849e1e46018c5e14c5612c4e114440f8360b42e0941e04c0a0240b00c44149d210631785514c561344b138451143c0f8340dc2e0b42f098250941c0781404c0a0240b00804150d328bd274841dc5d1544a100450fc2d0b41e0501701402659344911338be1e8651745415843118350b02e08c1a0781701802ad12444ce2f87a1945d1505610c420f8350b02e08c1e05c0600a46793e2e4a1200861f86517454144481384310c3a0f8320d42e08c1e05c0600ce2e4a61f865174541444813843118320d42e08c1a078170180285962e4a12187a1945d1505413843118350b8230681e05c0600a142901418b92987a1945d150541384310c3a0f8350b8230781701802c91e2ec992187e1845c1384310c3a0f8320c42e08c1a078170180300b066119441113e0fe2eca61e861140561244e1183e0dc2e0b8270781e0440900c964510458bb204861e865150561344e10c460d82b0b8230681e0540c0340306116451044d0a418bb284a61e865150561344e10c420f8360ac2e08c1e0540c034036198468bc1d46517455128401143f0b42d078140540f0140278b92987918065174541584e104410e03e0d8290b8210781701802a19d5c11d448bd2949c1d46517455128401143f0b42d078 else 0x5906017b28075170530e03c0cc180701402c0f01003009164179208720e833078150300902584c11928073178300d826040110240185924c119208720e83608c1e0481502409ad0a404821c83e0c8330b8230681e05409a571280911cc5e0c034078110240168921244a1083e0c8330a82a08c1a078150270785922e891208420f8320c8230681e05409027a244820f8320cc2b0681e0540954c42cc9b1cc631284d104430ec330b42108c1f04c160280a61e8654c1310b3208831cc6612c4d104430ec370ac2d0842307c130580a02c5310b326c8220c7612c4d104430ec370ac2d0842307c130580a02ac785dc5f87e14c4a138431183e0c8330a82f098270781b078160340f0180301e0485112987a1c4601945e154531584d12c4e10c460f8370b82f098270781b078120540c0240d01005e14d2146418c5e154531584d12c4e114450f03e0d0360b42f098250941c0781404c0902e9644c9284861f871180671785613841104380f8360a42f098260580f0180300c848510454861f87118063178531584b13845118340dc2e0b42f098250701e04c0a0240b00e9644c92849e1f87419c5e14c4a138410e03e0cc290bc260941e0580f018030591401012787e1d06717856104380f8330a82f098250781603c0600b18449e1f877178531284e1103e0cc2a0a42f098260580f0180285913387e1dc5e14c4a138440f8330a8290bc260841e0580f01802a1212849e1f87118063178531584b138451103e0d82d0b825078130280902c0325945ed104409b2187c1cc601945d1505413043110300d02b0bc2408c18078140500f01003a6116517b44113421032987c1cc601945d15054130431003c0d02b0bc2408c1e0501403c0400f164d12444ce1f8721945d1505610c460c8350b02f098230681e0580f018030d12444ce1f8721945d1505610c420f8350b02f098230781603c0600b1741d1284802187e1d86517454144481384310c3a0f8350bc2608c1e0580f0180344a61f8761945d150511204e10c460c8350bc2608c1a0781603c0600b164911284861f8721945d1505413843118320d42f098230681e0580f01803050a405012987e1c865174541504e10c430e83e0d42f098230781603c0600c25e16b264861f8761845c1384310c3a0f8310b8230681e0))))
def g503H9 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x80328410000000f0f082f000000050214030000000000001500000004934000d134c3a000000010c400000000000000000000000015600000000000c0f8000000205c0000000b0f40000000000e0ec000000102230280000000000000082b000380b5931829e1300000001450c94084858fc0000000000c04a00d000141a000000000000000000000000024e00000009138000000304b0001421bd6800000036060002607c094000e1180009947c452146e4f00004587809832413f208000002300dc000637000000000000003004c0cc000e159c2c00000001058000909800000000000000402d070000b0900000000000c05c000902405310c301f0001c4980800000000000510902a0000000704c0000000000000000080e103f0000000000263900000000000000f5580000000000000080e00000430000c0f000281b311c000a11185b000000000000000000000000000000000000000000000105a000302ea8b6c35000000000000000002818000000018f0000716400000000000000000000163a1949c1d0001836a14b400000103421000003568401000000000000000000000000000000000000003a3e0000000d044000000023bb01784a109c0000000000000001ea570000a362039000000000000000000000000301900000000000000000000051554b3000000000000000000000000000000004575366010a05000000000000001c060003c28301c557000305490b40c00000068178008b106001208002
def g503D10 (j : Nat) : Nat := if 7 ≤ j then 0 else (if j<3 then (if j<1 then 0xd134c354b844ab849fe490e48154713462c45604482439b42904197407a3fc03eeb3e5e3dbf3d173c663beb3b5e3abf3a4439ae3921389437f53717369c3618357034da344433c032c73216318030bd30152f9a2ef22e412dab2d032c762bc52b1d2a8729fa299128d7286e27f3274b26ac261f259b2520249323fd235522b6222921b7213320a61fe31f5f1edb1e2a1d8b1cf51c441bdb1b4e1aaf19fe197a18db1845179416da1629155d1506148213f5133b129c120f117910f5107a0fb70f2a0e940e190da70d080c720bc10b220ab90a35099f0900086107a706f6067205ca053404830408038d02ee027c022501ce0165010e00a5004e0000fff42d83ffd0760ffd41d83ffd0960ffd42583ffd0560ffd41583ff5c930fff424c3ff50930fff414c3ff50530ffd72443ffd0910ffd42442ff61a64bfd81993bfe0164f7d85592ffe0564bfd81193dfd9154f7d64553fbd8642fed6190bfbd8542fed6150b7fd9371dfd64dc77fe1971dfc865c77fd9171dfd645c77fd8971dfd625c77fe0171f7e64947df59251f7c64946ff61b41fbd64d07fd58741ff531d06ffe1941bfd86507ef99141fbd64507df5d760bfd84d83bf59360f7d54d83fb90b60fed42d82ff60760dff71d837f5c760f7e51d83df5d560efd64583df55160fee42583fb50960dff715837f5c560f7e51582ff60740f7e51d03ef50740fbe74503ef5d140f7d54502ffe0540dff715037f5c540f7e51503efd0540fbd41503df5d530efd644c3df55130fee424c3fb50930dff714c37f5c530f7e514c3fb50720fed71483fb50520bff814837f5c520f7e51482ffe1110efd64443fb90910fed42443fd5c510ff541442dfe1975e7d725979fd0965e7d425973fa1f64cfd87d939f61764ede83d93b760f64ef681d93bd60764afd869939f59664ebf64992f760e64bed829939f61564ebe74593af5d164e7d65593afd9164afe861939f59464ebd64192fe60064b7f865539fd9154e7d64553db59642bed8490beb99242fad6490bdb55242def8750b7b21d42f6d6550beb9d142fad7450bdb55142cff64dc73f59371dee42dc77b50b71cff865c73f21971cff645c73f59171def825c77b20971dee425c77b50971df5615c77d48571b7d849479fd9251e7d64947db90a51f6d42947dd4c651afe86d06bf61b41ebd64d06fb60b41aff86506bf21941ebd645077d5c541e7d65d839f59560bdf83582bfa1b40afd86d039f59740ebd64d03cf55340bed82d03eb90b409ff875039f59540ebd64503cf55140bdf83503eb90940e7d654c2fb61320eed64c83db55320def71c837b5c720f6e51c83db5d520bef84483bb59120f6d544837bdc520ded71483db94520e7d65482bfe1910afc864437d5c510a7f84596dd20554e6d6590bab59242f2d5490b9b5954297d87946f360f20 else (if j<2 then 0xa056170983c10070088c844210a04c190b8502a130883617098381e0903804c280c85c281007036140b844180f058038803e1708c451489c32170a056170983c100700888830178a44c1d0c85c281585c260f0401c0203511050260e0642e140a84c220d85c260e078240e01317488421489a42180b052261107832140b84c1e0b0100521f0c45c29150944c220f06c2c170904c1c0e048140262787c31170a45425130883c1b0b05c24130703812040280002c178762c11854260e058024541409c3c1c0cc582b0b84c1c0803803854170a04e1e0cc58280d85c260e0401c01f1489c3e188b8522a130883c1b0b05c241307038120402a0c8542711050270fc5c261106c2e1307038160118b850270f45c251306c2e130703812050078642e148783316080381b0a05c220c0702c0202a8b851210fc5a220d85c220e0501c01c170a0421f0cc58240c85c260e058034451489c3e188b8522a130883c1b0b05c241307038120402a8c8441409c3f17098441b0b84c1c0e05803e2e1409c3d170944c1b0b84c1c0e04814000101105e29138662c1006c2a130702c01a328ba421f8b4441b0b8441c0b00644a188b8522a130883c1b0b058260e0702408051190ac42200b8421e8cc58230a05c200e0580407a35590ad44210bc421e8cc5a2a118582e120702c026218bc421e8c45a291308c2c17090381204028044571787a2d150842e120702c016218ba50210f45a29130842e120702c01c3d1945e201087a291308c2c1709038120500806e2e9489c3d168a44c220c8502e12070240a011190a844174a04e1e8cc58200d8502e120401c022b21528844174a04e1e8cc5a2a1106c2c1709038140700a0aa2e9409c3d188b452261106c2c1709038120402804c551789c3d168a844190b8481c0a038038823a1945d291387a2d1489844190b8481c0a038048652a8bc4e1e8a44c220d8582e12070240a01089c421f0c45c2915098441e0d8582e120903812040298882f0f85c281406c2e13070200e00d1143c1d0b850280d85c260e0401c01aa18ba51210f05a261107832140b84c1c0b010044441f4a24d180b056170983c1004c8a44e180ac2e130782801222884311785c240f04812464228862e1106c2e120782c0171045c1b0b8481e0902802445218a4311707c2e120782409614080281285c260f05002442170862c11858160089b2299d8986a972995f194b99354923790ed8fc78e988d4e8c1f8ac3898b8889879986b285e684e484068304820281007fe37ec67d8e7ca77ba57a9a79b378c377a676c875e17515741c72f67206710d70146f366e856d7a6c8a6bb56ace69f0690067e366fc6615651c6447637b628b61bf60ea5fc45ed45ded5ceb5c1f5b385a63597c589e57d2572156705580548753bb52dd51e4512a50704fa44ebd4ddf4 else 0xe170983c12050088c8451489a441d0cc5e150983c1600d1908830178a44d1e0e8662d11854260f05804044180bc52260e8622c168ac2e130782c01e32110602f148983a188b056170983c1600f190a844180b850260e0662c1585c260f0401c022180bc52270c45c2915098441e0d8582e12098381e0a048100a0000c0a830170a04c1c0cc5e170983c1600d15060281307c38198b046150983c1600e1186631170a438198b0401c0d8502e110603c160121f0d4451489c31160b452270b84c1e09028040843b190882690c5a25108642e130683c16010190a84490c5a25108642e130683c1600e110602f148983a188b8522a12898441e0d8582e12098381e0a048100a0000d8c844180b850260ec5a251086c2e130683c160200804c642a0c05c281307033160ac2e13078200e0100bc52270c45c2915098441e0d8582e12098381e0a0481402a321508830170a04c198b84c220d85c260e0782c0242a0a04c220e0662c0d85c260d0580344a234c25e291347430160a04e170983c100600004844984b850268e0642c170a454270b84c1e0a020180262210850260c85c291509c2e1307828080600808930978823a188b452261106c2c170903c12050090c832140803316080381b0a05c260b00803c54a3112612e1488238198b844190d85c240f0481c0263251889309788238198b844190d85c240f0481c0242288031168a44c220d8582e120782408050080c840190a04e198b4481d0a05c240f05803c642009c33160742e120782c0162290a612f1447431168a44c220f06c2c170903c120500a108278b44c1e0c8502e1305802c6419c5a260f0642817090301e0b00688828130622d14898441e0d8582e120782408050090c854a24c25d268e4642e140a82e13078240e011190ac54a249a32170a054170983c12070078c854a20ca32170a4421a0b8441e0b007288328c85c291087434170883c1600d208e866140842e140a04c170983c12070078e930970a0411d0b850281305c260f0481c020324c25c289388239190b8502a1305c260f0481c0243251084289388232170a054260b84c1e09038044741449842170a04a210e8682e110782c01e3a0a42e14094421a0b8441e0b0060c828104642e15094421a0b8441e0b00708440144642e15094421d0d05c220f05803c70a390a612f1488238160a84a210e86828170983c160100aa4c200b84a210e86828170883c16010070883e9449a301409c2e13078200c000070c844984ba50289347232140a84e170983c140403004c7a32112502893464281509c2e130782808060088c844900823215094421b0a85c220f05018020421908942940a23215094421d0d8542e11078280c0134c0591f09446150983c14060058602e1409838190b8502b0b84c1e0803803c7c321788c42140983217)) else (if j<5 then (if j<4 then 0x40a84a261107836160b848260e07024080500b8b82e1409c3c1c0c45a2814090401c0d8502e10098301c080401c000198bc50291387c3a188a05425130883c1b0b05c24130703812040280605c2c8b850270f0622d140a44a220d85c260d070201405038058843b8ba421f8b44a220f0642817098341c080481c026321545d210fc5a251107832140b84c1a0e040240e0131145c281387c38188b8522a12898441e0d8582e12098381c09020140001a190c044178a44e1e0e8622d140a048200e06c28170804c180e040200e0000d8ca451789c3e1d0c45a28150883c190a05c241307038160200b0ca2e1489a421f0e8622d140a448261107832170904c1c0e05808030421908a2f140a44e1f0e86228150944c220f06c2c170904c1c0e048100a01b1945c281387831168a052251106c2e1306838100903805045170a04e1e0c45a2814894441b0b84c1a0e040240e0148ba52249087431170a452261107832140b04c1c0e048100a0161f2c944174a24e248c0662e148a84c220f06c2c16098381c0903808033174a24e250e46031170a45425130883c1b0b058260e07024080500c28a2f1248439180cc5c2a13088301b0b0542c1106038160200b28943174a44a1c8c0662e15098421c0f06036160a858220e05808030998bc4a1d0c45a28150883c190a058260e0702c0401350c5d29124843a188b4502912098441e0c858260e0702c040168bc4a1d0c4502a12898441e0d8582c130703812040280506aae10c5c2f1087a39188b452261088c2c150b844240c070201207008068823a8b85d291387a39188b452261088830190a05c221207020140503804036405745c2e9409c3d1c8c45a291308444180d8582a17088481c08050140e0100e0c03a1709c421e0e0622d14090401c0d8502e10090301c080401c000198bc4c210f87431168a05224130883c190b848240e0501c040160ec5e27100843e1d0c4502a12898441e0d8582e1209038120402806044174a24e1e0e4642e140a048200e06c28170804c180e040200e0000c908642c510882e9449c3d180c85c2815098441e0d8582e12098381c0a0281c0401d1928845174843e1c8c0642e1509842220c06c2c150b848220c070280e0200d90864a21128441174a43e1c8c0642e1509842210e078301b0b0542e1208838140701007e2e944843c1689842220f0642817098341c0805808020141728a2e9449c3d180c0582a12894441e0d85c260d07020160100ba612e1408238160a04c170983c100600003d268c85c2914894421d0c85c2211078241404028a41190b85229128843a1b0a85c221107824140402924d208c85c2914894421d0d8542e110883c120a02014c64220c05e260e8662d0b84c1e0b0068c830170a44d200e8662d1285c260f05803c44180bc52260e8622c168a44 else 0x40b844260d07824120700807474984b850208e4642e140a04a210e86828170884c1a0f048240e0100c8c930970a24e208e4642e140a848251087434170884c1a0f048240e0100d0fc78331928d44984b851271047232170a05424128843a1a0b844260d07824120700807d30970a24c208e4642e140a84825108743417088441e090481c020181f8cd46984ba4c208e4642e140a84825108743417088441e09058040323a4b850208f47232170a04a210e86828170884c1a0d0580402c3211a612e940a24d1c8c8502a12894421d0d8542e11098341e09050100c01b210fc78331908c44984ba50289347232140a84a251087436150b844260d07824140403008064984ba50289347232140a84a251087436150b844260d0782414040300686c2f11a612e1409a38190b8502812080381b0a05c20130603c1008038000363f1e0cc64a3112612e1409a381c0c85c281509844190d85c260e078240e01b1c28e42984bc52268e07430160a84c211107836170983c1602008061311489a3e180b054251107836150804c1e0a03804026361788c44984bc52268e86032170a050241007036140b840260c0782010070000745c23112612f1489a3a190b850241007036140b840260c0782010070000685c224c25c281347038190b8502a13088321b0b84c1c0f0481c02e3f1e0cc44984b850268e07032170a05426110643617098381e0903806436944843e1d0c45c29148904c220f06428170904c1c0e048100a0181d8c8449449c3c1c8c0662c14090401c0d8502e10098301c080401c0001a1e0bd449449c3c1c8c0662e148a84a26108883c1b0b05c2413070341c08050140e0200f889289387c39180c45c29150944c220f06c2c170904c1c0e048100a01951089210f87230198b8542610888301b0b0542e12088301c0a03808032a211284409487c39180cc5c2a13084421c0f06c2c150b848220e0501c0401b1788a1e0e0622d140a048200e06c28170804c180e040200e0000b8f0649987c3a188b4502a1107832140b848260e070280e0200b0f0743250a51210f87431168a05224130883c190b848260e070280e0200d0f0650f87431140a84a261107836160b848260e07024080500b45d289087c3a188b85229130883c190a05c241307038120402805c662711a88449449c3c1c8c0662e148a84a26108883c1b0b05c2413070341c080481c040201145d289387c39180c45c29150944c220f06c2c170904c1c0e048100a01a93a8845174843e1c8c0662e1509842220d8582a1709044180e05808033275108942208ba521f0e46033170a84c21108703c1b0b0542e1208838160200e0ce4e998bc3e1d0c45a28150883c190a05c241307038160200b0ce4ea18ba51210f87431168a05224130883c190b848260e0702c0401919c9e2f0f874311) else (if j<6 then 0x1f0e07230188b4502a1289842220e878301b0b0542e120884c1c0d07020140503808020241e0bd5c2e51089289387c381c8c0622d140a84a26108883a1e0c06c2c150b8482213070341c08050140e020080a24e2611a662e944843c1c8c0662e148a84a2610884381e0c06c2c150b044220c070201207010040472750881331749a421e0e0662e148a84a2610884381e0c06c2c150b848221106038100b01004044331308e2e9487839180c45a28150944c21110743c180d8582a160884c1c0d07020120701004044335749c4c235108a2e9449c3c1c8c0622d140a84a26108883a1e0c06c2c150b044260e06838100903808020274d45d2712094391d0c4662e148a4482610084381e0c064281608044180e0402c040100f8f933170ba522412484391c8c0662e148a84a2610084381e0c06c2c150b040220c07020120701004048a14cc5d2712092421c8e0662e148a84a26108703c180d8582a1608044180e0402c04010100fa2e178904a1c8e46031168a0542513080441d0f06036160a858201206838100903808020211f2b945170ba512712094391c8c0622d140a84a26110743c180d8582a16080481a0e040240e02008091341a8ba4e1f0e47431190b850291209842210e07830190a05c2411088301c080501c04010108f0642c8b85d289087c391c8c0642e140a84a2610884381e0c06c2c150b848221106038100a0281c0401013284411749a421f0e47032170a0542513084421c0f06036160a85c2411088301c080501c04010110c85423110602e1409838198b050241007036140b840260c0782010070080003823114622e1409c38188b4502812080381b0a05c20130603c1008038000343b190bc44178a44d1f0cc5a29128843a1b0a85c221306834120700806476361788c45188bc52270e8622c168a44e170983c120500005846228c45e29138703a180c45a2814090401c0d8502e10098301e080401c0001c0c05c281307031168a050241007036140b840260c07820100700006044984b850268e0642c170a45425128843a1b0a85c22130683c120a020180001c1188930970a04d1c0c85c29150944a210e86c2a170884c1a0f0482808060000706522112612f1047430188b4522610888321b0b0542e11090301e090481c0201c1c0c94722112612e138823a180c45a291308444190d8582a1708848180f048240e0100f90865221108130978a23a180c45a2913084441c0f06436160a85c221207824120700807c84381948845211088130978a23a180c45a2913084441c0f06436160a85c2212078241207008088642a512612e9347232170a052210e86828170884c1a0f048240e0100c8fc7833190a944984ba4d1c8c85c28148843a1a0a05c22130683c1209038040383f1e0e866a34c25c281047232170a0502510874341 else 0xbd32944843e1c0e46033170a4542513084421c0f06036160a85c2411088301c08050140e0200808c783217a52)))
def g503H10 (j : Nat) : Nat := if 2 ≤ j then 0 else (if j<1 then 0x6121193013a1af00786187509ec134c0e2819d2111a200000006738229224400000001b10b40640001207b50a560f00000000000000000a0f80048d1161238c94220c2000000000000e210f0900000000041ca403261de0000517940b80000308e0000d26a80e600000001c12e0000e19e3256e0382622e99920980001809b2010c0460000000000000000e0fda1902015800361c9a1734221a080f99cd229911220b0c045825f01786680726780526636a22ca9b83211404ee16f909542636137b21705b3403b024d3269826c0000618dd0ac821d008660eac25c0000606bc20f70af624141a60001b11941f680ce0e0042774105a1f4623c8128a1e1e00f2250a27a0001227ce02ec0854029223a40ca0000a03e4035201d624a5908c5e6e196817b0082000000b4e1f2268721ce000181bd600ca20c0000608bc2745a84c25380f430fc0000e1800000a0e1b110a1300001e0de01c160aa0001b24400010174402c0001f22c0000000120a76a89c0740000a1456000000000000000a1b8008c626e00000093a0ee418581fe00012e3a6097d21cc0ece07c2270413ae0d900a80000605e20b2000000009221924c815b120e001620baa056024ec0fe000000cc000120e8a06e204321660000e12ce05400004279618981e40000011ee16b607069e9e1564161d2620001a25a125e221ea15fe23521b4d0a7a03cc232000140c622824037418200000000000021c72261f240622e00000000b0a84624610361c4aa7980fb21e800000000c1ba0001c0dbb250000180040001627260d320f2000061c321520001f24a000010ff408800000001400922300001525241eef0ee824941bf418f21a40000801e000081eb21a359b94127005be176000081f80000000081151a25721e0000000001d280a2a14e4012000151aa0000028901fa00001233267a81b1610d82220001401a8a7e0000066da0f6a209617c21d6e0e449b661d01a83a1064265a20af26f814a0001c28140300000804c0000e25800013004d0fa2199b22fe10e219470d41e3e0001c1d861b3c1abe04a0000924e000000000001c06872300000605d815cda6ca022225400000020000005bc0000c0d6627f508aaa23c213218a0000209000000000000030a200016247220461412024000021e7608e0001c22ac15161fc46758193606de12baa840001b260c17f800721b60000f08d211a0226023600000001814c00008dfe0000000000000000f0f7e206413f1248f10700bc0154c094406382140001202ae100e0ad217000000000000140014003c2160a1408026900011200101006801c1e15408064400b0808a2862648820400eac0e3cf8306043b206b0413700c03c003818200000010a0401100001030010100000810d0c2048a48303b12604980201818a5c0410000083050600280 else 0x100dc00000000a0a00000c0c8200b210a00018218000060ae00006072e1d40000000125bad20b80d041160001213ca120f11460260001525801eda287221ae077024241644634000000002a7b2168a146b26581628683100600006067a14361cdc1a9a0d40001a2560000007fc284a11c0000426ba09e721af22a00013226823e00000000d9b641ad011210880000409d8225c019de3be2669255219aa148c2391206b215a05000000124e16c000160b650a1a0a40000c0406689012200000000a0c11212e6788138791f21f0e5f8d21961586108a26800000000000040be00014a820000000121a1e13200000000000000009a37d2460001c1ddc5b4000000000000000000000000094701dbc1e2000062160000e203e05840c540)
def g503D11 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x2a23181714130e0c8b0a09080706850584048303820201800064c88c88605c504c38322c2824201c1a141610120c0e0808060001a2a181714130e0c8b0a0908070685058404830382020180006084504c38302c2824201c1a141610120c0e080806000162e2214130e0c0b0a0908070685058404830382020180005c3c38322c2824201c1a141610120c0c08060001327170f0e0c8b0a0908070685058404830302800050a85c504c3c38322c2824201c1a141610120c0c080600017221714130f0e0c8b0a09080706850584048303028000585c4838322c2824201c1a1414120c0c0a00012191713100f0e0c8b0a09080706850584040302018000585c3c38302c2824201c1a141610120c0c08060001414100b0a090584838201002cc888605c504c38322c2c2a16120e0806011322214130c8b0a85848382018034504c302c282616120e080400c22100c8b080685058403828030888450322c201c1a1416100e0a00e2a190b0a0584838280248450402c282416120e0a00b0a0985848382010020845c403e2c221416100c0a00c2a17130f8b080685058403020180382c2a16120e08047c62b8cac6a109528b480e75069a60454e4a844a3bc34e2e828220c1be16011a0b403e000ffcc9ff593fe327ff41ffa83ffd83feb07ff40ffa81ff4c3fe907fd10efaebbfd937eb277d54fdc85fb50affb8dfd71efca3fbc83f69067d65
def g503H11 (j : Nat) : Nat := if 2 ≤ j then 0 else (if j<1 then 0xc00000000000000000000000000000102f800000000001a0b8000000000000000000813a000343a80005d1b630800000001820c6fc8488000d11e0000000000000000001a63801000000000000005ea08000015628000a0560000000557300000000000000010fc000000000000000000104588480000c147946e04fc925f09004e1c0bf17e11d04350499000000014b98000890e0000805c414f0e80000000586510660000000000020df8a2c000506c5d7e703663822a9658000024548000201b4029c04807d000161ee018800000002192c5d8000000172440000000691e000000071ca0000000000000440000000000078040000521400028260000000142c90ad0000000000028290000425b0368000000000000000000805a00000002800811a000000000000000000000000000000000202580000000000000038b500000000f6080000000000000000000000000000000000000811c0000000803a00028028000206120dc00028b40000e0ec0000000c38a00000000000000000000000000446e00000000000d128000000000000000000000008c1e0a800000003061b0b6000381f800004f20000000549c0000000183c80000000000000000a5e143b1e00000000619800004e48c8d24a981c4c0f302501080002c1a800000000000000000088ec0000c5398cdd90600020431c1600000002604387600000000000000000000000000000000000003c20800000010198000316a0001d03c00050c9b10000010370000000022bc0000000a02f925b40780006928227c00038cb0000000000000000000000000000000000000344800000000000000038670000000345b8000f389b056c1c000051740000000689b00000000000000000000000000440e0000000000038390000018bd52f05a00000001c25380ee104000000000000000000000000000000000000000000001a28e0620000805d0a0c000601448de2174c31e82321540000000278871624133001b04dc56f826a745b89700000000000587c000000000000000099800000000000f103e2e40000000692000024b4f8a20000000342c000090a400000000000f0ee0003f41800020e4000140880000000000000078c000000002012750b06e60002c438000317b922f021a03c914dca56c5262c40000a070000000010a1104fc39902cfd8041a4000000021660000665c90b00000000c22800000000000e0668be2d380001c4980000000000140168ac2019073481d4629515da1800000000793600014428000003e000000000000000000000000000001aafd00d000090d000000003818212a000000010a80000000000000000000000000000000000000000000000001431a20974bc05202044f4121106010b0001951200701760025000010000c0a202800349410501001112009 else 0x582a00000000000000000000001458000000f0c0480000000d8e360a204700005934125c0006827000081fc00000000000000000000000000000000000000000000184f7c93602ce1c0000303480ae000000000000000000000000000000000000052c1000000000002c1d000000000000000000000000000000b0abe2240006836d07b58a00000000000000000000000000000000002693ad942006d4f986b3114817183d0000000000000004819002a00000000000f1060000000000000003238000000000000000000000000000002c1f0000611983220194822083c0000d656c849954000000000008140000182b00000000000085e19c02d2a00000000000a16d232bc038000000000038035c950001811800078b86132426000000000000000000000000000000000000000000000000000000000000201028530000806c0000000d18e000000000000000000000000000000000000000000001430c000000000000000000049e00004221c10800000000000c493042599122c8000684e000000037c480000001604ec24b8c570106ae241780000000000000000000000000000000000000000000040ab0000908)
def g503D12 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x161420304006ff
def g503H12 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x51684c402405a52000000b1721160366de57000cad415c4e006000b820000004d0d53000054000007f81000d08e14cd120db91e13000592000000000312d8ce09000000a0e0009d200070a000848b0100062d000a8f00000000024f10c10f31020b004d90ccc8511cf000000050423c01ead
def g503L : Nat → Packing
  | 7 => (9,5,7,0,0,10,0,g503D7)
  | 8 => (93,4,7,0,0,14,0,g503D8)
  | 9 => (325,3,7,0,0,16,0,g503D9)
  | 10 => (206,2,7,0,0,16,0,g503D10)
  | 11 => (24,1,7,0,0,12,0,g503D11)
  | 12 => (1,0,7,0,0,0,0,g503D12)
  | _ => emptyPacking
def g503I : Nat → Nat → Option (Nat × Nat)
  | 8 => lookupWord 2 23 0 8 4 0 g503H8
  | 9 => lookupWord 30 307 3 14 7 3 g503H9
  | 10 => lookupWord 111 607 7 16 9 3 g503H10
  | 11 => lookupWord 75 757 4 15 8 3 g503H11
  | 12 => lookupWord 12 73 3 12 5 3 g503H12
  | _ => fun _ => none
def g503 : Forest := ⟨503,12,fun i => g503Y[i]?.getD (0,0),g503C,g503A,g503L,g503I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g503P7_0 : block g503 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g503P7_1 : block g503 7 1 5=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g503P7_6 : block g503 7 6 3=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g503B7 : block g503 7 0 9=true := (@block_merge g503 7 0 1 8 g503P7_0 (@block_merge g503 7 1 5 3 g503P7_1 g503P7_6))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g503P8_0 : block g503 8 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g503P8_1 : block g503 8 1 28=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g503P8_29 : block g503 8 29 57=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g503P8_86 : block g503 8 86 7=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g503B8 : block g503 8 0 93=true := (@block_merge g503 8 0 29 64 (@block_merge g503 8 0 1 28 g503P8_0 g503P8_1) (@block_merge g503 8 29 57 7 g503P8_29 g503P8_86))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g503P9_0 : block g503 9 0 64=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g503P9_64 : block g503 9 64 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g503P9_160 : block g503 9 160 57=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g503P9_217 : block g503 9 217 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g503P9_313 : block g503 9 313 3=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g503P9_316 : block g503 9 316 9=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g503B9 : block g503 9 0 325=true := (@block_merge g503 9 0 217 108 (@block_merge g503 9 0 64 153 g503P9_0 (@block_merge g503 9 64 96 57 g503P9_64 g503P9_160)) (@block_merge g503 9 217 96 12 g503P9_217 (@block_merge g503 9 313 3 9 g503P9_313 g503P9_316)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g503P10_0 : block g503 10 0 8=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g503P10_8 : block g503 10 8 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g503P10_104 : block g503 10 104 5=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g503P10_109 : block g503 10 109 82=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g503P10_191 : block g503 10 191 15=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g503B10 : block g503 10 0 206=true := (@block_merge g503 10 0 104 102 (@block_merge g503 10 0 8 96 g503P10_0 g503P10_8) (@block_merge g503 10 104 5 97 g503P10_104 (@block_merge g503 10 109 82 15 g503P10_109 g503P10_191)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g503P11_0 : block g503 11 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g503P11_1 : block g503 11 1 11=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g503P11_12 : block g503 11 12 12=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g503B11 : block g503 11 0 24=true := (@block_merge g503 11 0 1 23 g503P11_0 (@block_merge g503 11 1 11 12 g503P11_1 g503P11_12))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g503P12_0 : block g503 12 0 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g503B12 : block g503 12 0 1=true := g503P12_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g503T : checkedTables g503 12 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g503 0 0 0 = true)
  · exact (rfl : block g503 1 0 0 = true)
  · exact (rfl : block g503 2 0 0 = true)
  · exact (rfl : block g503 3 0 0 = true)
  · exact (rfl : block g503 4 0 0 = true)
  · exact (rfl : block g503 5 0 0 = true)
  · exact (rfl : block g503 6 0 0 = true)
  · exact g503B7
  · exact g503B8
  · exact g503B9
  · exact g503B10
  · exact g503B11
  · exact g503B12
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g503G : graphValid g503 (boundsBefore KS439) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowS503 : Lower true (varsX 503) (graphGoal 503) 13 := lower_forest (g:=g503) (i:=0) (hints:=8607761748) (before_sound KS439 VS439) g503G g503T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KS503 := extendKnown KS439 13 [(503,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VS503 : Known true KS503 := extend_ok (m:=503) VS439 lowS503 (by decide +kernel)
def g511Y : Array (Bits × Bits) := #[(0x3fffe00000000000000001ffff,0x5055282a94154a0aa5055282a94154a0aa5055),(0x7fffc00000000ffff80003fffe0000,0x300318018c00c6006300318018c00c60063003),(0xffff0000000000000000000007fffc00000000,0x5330299814cc0a6605330299814cc0a660533),(0x1ffff00000000000000000,0x30f018780c3c061e030f018780c3c061e030f),(0xffff80000000000000000000000001ffff,0xa0aa5055282a94154a0aa5055282a94154a0aa),(0x7fffffffe0000,0xacc056602b3015980acc056602b3015980acc),(0x1ffffffff8000000000000,0xccf0e678733c399e1ccf0e678733c399e1ccf0),(0xffffffffffffe000000000000000000000,0xf00878043c021e010f00878043c021e010f00),(0xffff0000000000000000000000000000000000,0xf000f8007c003e001f000f8007c003e001f000)]
def g511C : List ColumnInfo := [(8,0,503,0,13)]
def g511A : List (List Nat) := [[],[64]]
def g511D13 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x3ff
def g511L : Nat → Packing
  | 13 => (1,0,1,0,0,0,0,g511D13)
  | _ => emptyPacking
def g511I (_ _ : Nat) : Option (Nat × Nat) := none
def g511 : Forest := ⟨511,13,fun i => g511Y[i]?.getD (0,0),g511C,g511A,g511L,g511I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g511P13_0 : block g511 13 0 1=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g511B13 : block g511 13 0 1=true := g511P13_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g511T : checkedTables g511 13 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g511 0 0 0 = true)
  · exact (rfl : block g511 1 0 0 = true)
  · exact (rfl : block g511 2 0 0 = true)
  · exact (rfl : block g511 3 0 0 = true)
  · exact (rfl : block g511 4 0 0 = true)
  · exact (rfl : block g511 5 0 0 = true)
  · exact (rfl : block g511 6 0 0 = true)
  · exact (rfl : block g511 7 0 0 = true)
  · exact (rfl : block g511 8 0 0 = true)
  · exact (rfl : block g511 9 0 0 = true)
  · exact (rfl : block g511 10 0 0 = true)
  · exact (rfl : block g511 11 0 0 = true)
  · exact (rfl : block g511 12 0 0 = true)
  · exact g511B13
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g511G : graphValid g511 (boundsBefore KS503) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g511R : Impossible true graph 13 inputs.toFinset := by
  rw [show graph = targetOf g511 by decide +kernel]
  exact root_index (g:=g511) (top:=13) (i:=0) (before_sound KS503 VS503) g511G g511T (by decide) (by decide +kernel)
def mo145Y : Array (Bits × Bits) := #[(0x3ff63ff63ff63ff63ff63ff63ff63ff63ff63f,0x49204920492049204920492049204920492049),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0xc7fbc7fbc7fbc7fbc7fbc7fbc7fbc7fbc7fbc7,0x92409240924092409240924092409240924092),(0x0,0x0),(0x0,0x0),(0xf8fdf8fdf8fdf8fdf8fdf8fdf8fdf8fdf8fdf8,0x24812481248124812481248124812481248124),(0x0,0x0)]
def mo145C : List ColumnInfo := []
def mo145A : List (List Nat) := [[],[116],[64],[64,112],[112,64],[112]]
def mo145D3 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x7
def mo145L : Nat → Packing
  | 3 => (1,0,1,0,0,0,0,mo145D3)
  | _ => emptyPacking
def mo145I (_ _ : Nat) : Option (Nat × Nat) := none
def mo145 : Forest := ⟨1169,3,fun i => mo145Y[i]?.getD (0,0),mo145C,mo145A,mo145L,mo145I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo145P3_0 : block mo145 3 0 1=true := by
  apply cellsBlock (ar:=3) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo145B3 : block mo145 3 0 1=true := mo145P3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo145T : checkedTables mo145 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block mo145 0 0 0 = true)
  · exact (rfl : block mo145 1 0 0 = true)
  · exact (rfl : block mo145 2 0 0 = true)
  · exact mo145B3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo145G : graphValid mo145 (boundsBefore []) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowM145 : Lower false (varsX 145) (graphGoal 145) 4 := lower_forest (g:=mo145) (i:=0) (hints:=4) (before_sound [] (known_down baseKnown)) mo145G mo145T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KM145 := extendKnown [] 4 [(145,[]),(292,[32,16,84,135])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VM145 : Known false KM145 := extend_ok (m:=145) (known_down baseKnown) lowM145 (by decide +kernel)
def mo102Y : Array (Bits × Bits) := #[(0x0,0x0),(0xf71fc7ff03fffff8f71fc7ff03fffff8f71fc7,0x710490a285040120710490a28504012071049),(0xbe838fffc07e3ff0be838fffc07e3ff0be838,0x4368db4c326089204368db4c326089204368db),(0x0,0x0),(0x0,0x0),(0xeee63ffffff803ffeee63ffffff803ffeee63f,0x8872490408512400887249040851240088724),(0x193dc0fffffffc00193dc0fffffffc00193dc0,0x982db6e083060384982db6e083060384982db6),(0x0,0x0),(0x0,0x0)]
def mo102C : List ColumnInfo := []
def mo102A : List (List Nat) := [[],[81,98]]
def mo102D3 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xf
def mo102L : Nat → Packing
  | 3 => (1,0,1,0,0,0,0,mo102D3)
  | _ => emptyPacking
def mo102I (_ _ : Nat) : Option (Nat × Nat) := none
def mo102 : Forest := ⟨1126,3,fun i => mo102Y[i]?.getD (0,0),mo102C,mo102A,mo102L,mo102I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo102P3_0 : block mo102 3 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo102B3 : block mo102 3 0 1=true := mo102P3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo102T : checkedTables mo102 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block mo102 0 0 0 = true)
  · exact (rfl : block mo102 1 0 0 = true)
  · exact (rfl : block mo102 2 0 0 = true)
  · exact mo102B3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo102G : graphValid mo102 (boundsBefore KM145) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowM102 : Lower false (varsX 102) (graphGoal 102) 4 := lower_forest (g:=mo102) (i:=0) (hints:=17827152) (before_sound KM145 VM145) mo102G mo102T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KM102 := extendKnown KM145 4 [(102,[]),(163,[32,117,101]),(166,[118]),(178,[66,50,117,101]),(195,[32,117]),(202,[50,101,117]),(298,[129,33,50,99,118]),(330,[49,33,101,133,117]),(332,[49,133,117]),(354,[81,98,50,67,132,116]),(360,[49,82,66,132,116])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VM102 : Known false KM102 := extend_ok (m:=102) VM145 lowM102 (by decide +kernel)
def mo147Y : Array (Bits × Bits) := #[(0xfdf00fff81fc7e3ffbe01fff03f8fc7ff7c03f,0x45c09245142904808b81248a28520901170249),(0xe6a8703ffe007fc7cd50e07ffc00ff8f9aa1c0,0x96a9b6d618b228112d536dac316450225aa6db),(0x0,0x0),(0x0,0x0),(0xfbb781ffffff8007f76f03ffffff000feede07,0x235249820c03122046a49304180624408d492),(0x0,0x0),(0x0,0x0),(0x64ffe3ffffffff80c9ffc7ffffffff0193ff8,0x24920410040040004924082008008000924),(0x0,0x0)]
def mo147C : List ColumnInfo := [(2,0,145,0,4)]
def mo147A : List (List Nat) := [[],[64]]
def mo147D4 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1f
def mo147L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,mo147D4)
  | _ => emptyPacking
def mo147I (_ _ : Nat) : Option (Nat × Nat) := none
def mo147 : Forest := ⟨1171,4,fun i => mo147Y[i]?.getD (0,0),mo147C,mo147A,mo147L,mo147I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo147P4_0 : block mo147 4 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo147B4 : block mo147 4 0 1=true := mo147P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo147T : checkedTables mo147 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block mo147 0 0 0 = true)
  · exact (rfl : block mo147 1 0 0 = true)
  · exact (rfl : block mo147 2 0 0 = true)
  · exact (rfl : block mo147 3 0 0 = true)
  · exact mo147B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo147G : graphValid mo147 (boundsBefore KM102) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowM147 : Lower false (varsX 147) (graphGoal 147) 5 := lower_forest (g:=mo147) (i:=0) (hints:=116) (before_sound KM102 VM102) mo147G mo147T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KM147 := extendKnown KM102 5 [(147,[]),(294,[32,132,84,117]),(300,[32,49,84,135])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VM147 : Known false KM147 := extend_ok (m:=147) VM102 lowM147 (by decide +kernel)
def mo110Y : Array (Bits × Bits) := #[(0x0,0x0),(0xe003ffc07ffffffe003fffff80ffd386b20f0f,0x41a8128d052280541a82502916291304a21111),(0xfffc00007ff01fffffc007ffff01a37d4800f0,0x81311b160644c89893136232244d835c485555),(0xffffffff80001ffffffff80000003f407df000,0x5c05c18178702e01c0380bc38703340753333),(0x0,0x0),(0x1ffffffffffffffe663f7600ff,0x1602602058081301202404c00000642314aaaa),(0xffffffffffffe0000000000000019dd38dff00,0x1803800060001c01c038070040808c9308cccc),(0x0,0x0),(0x0,0x0)]
def mo110C : List ColumnInfo := []
def mo110A : List (List Nat) := [[],[50,101]]
def mo110D4 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1f
def mo110L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,mo110D4)
  | _ => emptyPacking
def mo110I (_ _ : Nat) : Option (Nat × Nat) := none
def mo110 : Forest := ⟨1134,4,fun i => mo110Y[i]?.getD (0,0),mo110C,mo110A,mo110L,mo110I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo110P4_0 : block mo110 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo110B4 : block mo110 4 0 1=true := mo110P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo110T : checkedTables mo110 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block mo110 0 0 0 = true)
  · exact (rfl : block mo110 1 0 0 = true)
  · exact (rfl : block mo110 2 0 0 = true)
  · exact (rfl : block mo110 3 0 0 = true)
  · exact mo110B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo110G : graphValid mo110 (boundsBefore KM147) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowM110 : Lower false (varsX 110) (graphGoal 110) 5 := lower_forest (g:=mo110) (i:=0) (hints:=17851728) (before_sound KM147 VM147) mo110G mo110T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KM110 := extendKnown KM147 5 [(167,[48,32,117,101]),(334,[49,33,101,133,117]),(419,[32,131,67,117,101,100]),(426,[81,50,114,66,129,97]),(458,[97,114,131,66,81,83])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VM110 : Known false KM110 := extend_ok (m:=110) VM147 lowM110 (by decide +kernel)
def mo179Y : Array (Bits × Bits) := #[(0xf003ff87fe1fffc01ffff87fffe474a4007c1f,0xa12845108440228940a01108826014a45294a5),(0xfffc0007ffe1ffffe00fffffc0335be20f83e0,0xc030162028040b0182c0a00108225922318c63),(0x0,0x0),(0x0,0x0),(0xfffffff80001fffffff0007ffccfd11df0001f,0x240980130884c020302c2120087c108a5294a),(0x1ffffffffff80004d2fe80003e0,0xb82e045c111702c140b005c104d26c9ce739c),(0x0,0x0),(0xfffffffffffe000000000000033aa61bfffc00,0xc03000600018030180c046021182211084210),(0x0,0x0)]
def mo179C : List ColumnInfo := [(0,32,145,2,5),(32,0,147,0,5),(1,0,178,0,4),(2,0,145,0,4),(2,32,145,0,4),(16,0,163,0,4)]
def mo179A : List (List Nat) := [[],[64]]
def mo179D5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x50481a0fd40fd20
def mo179D6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x163440df
def mo179H6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x345fd
def mo179L : Nat → Packing
  | 5 => (2,1,3,0,0,4,0,mo179D5)
  | 6 => (1,0,3,0,0,0,0,mo179D6)
  | _ => emptyPacking
def mo179I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 5 0 6 1 1 mo179H6
  | _ => fun _ => none
def mo179 : Forest := ⟨1203,6,fun i => mo179Y[i]?.getD (0,0),mo179C,mo179A,mo179L,mo179I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo179P5_0 : block mo179 5 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo179B5 : block mo179 5 0 2=true := mo179P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo179P6_0 : block mo179 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo179B6 : block mo179 6 0 1=true := mo179P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo179T : checkedTables mo179 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block mo179 0 0 0 = true)
  · exact (rfl : block mo179 1 0 0 = true)
  · exact (rfl : block mo179 2 0 0 = true)
  · exact (rfl : block mo179 3 0 0 = true)
  · exact (rfl : block mo179 4 0 0 = true)
  · exact mo179B5
  · exact mo179B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo179G : graphValid mo179 (boundsBefore KM110) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowM179 : Lower false (varsX 179) (graphGoal 179) 7 := lower_forest (g:=mo179) (i:=0) (hints:=1048660) (before_sound KM110 VM110) mo179G mo179T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KM179 := extendKnown KM110 7 [(179,[]),(211,[101]),(358,[32,132,101,84,117]),(364,[32,49,84,100,135]),(422,[32,132,117,100])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VM179 : Known false KM179 := extend_ok (m:=179) VM110 lowM179 (by decide +kernel)
def mo181Y : Array (Bits × Bits) := #[(0xc00fff0ffffffc00fffff0fffeea3a5303f03f,0x84a08a210802284a0280220882200a53145145),(0x0,0x0),(0xfff0000ffc3fffff003fffffc009adfd000fc0,0xc42c405090b10c4b11404108092d994d34d3),(0x0,0x0),(0xfffffff0003fffffffc000fffd77e88afc003f,0x90130026104c0100c0584120152a08828a28a),(0x3fffffffffff00012697f4000fc0,0x2e09c08b822702609026009c11269264b2cb2c),(0x0,0x0),(0xffffffffffc0000000000000039d530dfff000,0x300e000c00380380e03808e0208d5104c30c30),(0x0,0x0)]
def mo181C : List ColumnInfo := [(0,4,145,32,5)]
def mo181A : List (List Nat) := [[],[116],[82],[82,116],[64],[64,112],[64,82],[64,82,112],[112,64],[112],[112,82,64],[112,82]]
def mo181D5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x3f
def mo181L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,mo181D5)
  | _ => emptyPacking
def mo181I (_ _ : Nat) : Option (Nat × Nat) := none
def mo181 : Forest := ⟨1205,5,fun i => mo181Y[i]?.getD (0,0),mo181C,mo181A,mo181L,mo181I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo181P5_0 : block mo181 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo181B5 : block mo181 5 0 1=true := mo181P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo181T : checkedTables mo181 5 := by
  intro k hk
  interval_cases k
  · exact (rfl : block mo181 0 0 0 = true)
  · exact (rfl : block mo181 1 0 0 = true)
  · exact (rfl : block mo181 2 0 0 = true)
  · exact (rfl : block mo181 3 0 0 = true)
  · exact (rfl : block mo181 4 0 0 = true)
  · exact mo181B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo181G : graphValid mo181 (boundsBefore KM179) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowM181 : Lower false (varsX 181) (graphGoal 181) 6 := lower_forest (g:=mo181) (i:=0) (hints:=2098436) (before_sound KM179 VM179) mo181G mo181T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KM181 := extendKnown KM179 6 [(181,[]),(217,[50,101]),(309,[32,84,135]),(405,[133,101]),(409,[50,133,101]),(421,[32,84,116,100,134]),(433,[82,50,131,99]),(436,[32,16,65,49,83,115,99,134])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VM181 : Known false KM181 := extend_ok (m:=181) VM179 lowM181 (by decide +kernel)
def mo227Y : Array (Bits × Bits) := #[(0x7fffffc01fffff8003ffc01ffe000db5f91c0,0x50a50548542805506a824834144160595996db),(0xf8007ffffe00ffffffffffffffffff35e1fe3f,0x60060010000200600300100000800800613249),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0xffff80000000ffffffc00001fffff3f14c6007,0x84c8566198cca9854c2b6159590a43f10c4db6),(0xfffffffffffe0000013ead8038,0x6f06782e170ce06703382619e13813e8c8db6),(0xffffffffffff00000000000000000cea9e5fc0,0x70078030180f007803c0381e01c04a2864924),(0x0,0x0)]
def mo227C : List ColumnInfo := [(32,0,195,0,4)]
def mo227A : List (List Nat) := [[],[101]]
def mo227D4 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x3f
def mo227L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,mo227D4)
  | _ => emptyPacking
def mo227I (_ _ : Nat) : Option (Nat × Nat) := none
def mo227 : Forest := ⟨1251,4,fun i => mo227Y[i]?.getD (0,0),mo227C,mo227A,mo227L,mo227I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo227P4_0 : block mo227 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo227B4 : block mo227 4 0 1=true := mo227P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo227T : checkedTables mo227 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block mo227 0 0 0 = true)
  · exact (rfl : block mo227 1 0 0 = true)
  · exact (rfl : block mo227 2 0 0 = true)
  · exact (rfl : block mo227 3 0 0 = true)
  · exact mo227B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo227G : graphValid mo227 (boundsBefore KM181) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowM227 : Lower false (varsX 227) (graphGoal 227) 5 := lower_forest (g:=mo227) (i:=0) (hints:=17825879) (before_sound KM181 VM181) mo227G mo227T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KM227 := extendKnown KM181 5 [(227,[]),(230,[32,101,117]),(234,[48,32,118]),(482,[128,32,50,67,101,117])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VM227 : Known false KM227 := extend_ok (m:=227) VM181 lowM227 (by decide +kernel)
def mo302Y : Array (Bits × Bits) := #[(0x0,0x0),(0x7ff001ff80ffc07ff003ffffe03ff4b12b0007,0x42a8d4251a148b42a9aa4a8a458a64b1235b6d),(0x7ffffe0000fffffffffc00ffffc068db9401f8,0x4c098362c191204c1306c0c891340d3841249),(0x7fffffffff00007fffffff0000000ff00e8e00,0x1702e0b8305e1c1701c0702f0e1c0df00cb6db),(0x0,0x0),(0x800000000000007fffffffffffff99af6d703f,0x180300c040602018020080300000190c082492),(0x0,0x0),(0x0,0x0),(0xffffffffffffff800000000000006754f2ffc0,0x600c0100008000600c0300c010202200724924)]
def mo302C : List ColumnInfo := [(2,0,300,0,5)]
def mo302A : List (List Nat) := [[],[49,133]]
def mo302D5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x3f
def mo302L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,mo302D5)
  | _ => emptyPacking
def mo302I (_ _ : Nat) : Option (Nat × Nat) := none
def mo302 : Forest := ⟨1326,5,fun i => mo302Y[i]?.getD (0,0),mo302C,mo302A,mo302L,mo302I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo302P5_0 : block mo302 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo302B5 : block mo302 5 0 1=true := mo302P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo302T : checkedTables mo302 5 := by
  intro k hk
  interval_cases k
  · exact (rfl : block mo302 0 0 0 = true)
  · exact (rfl : block mo302 1 0 0 = true)
  · exact (rfl : block mo302 2 0 0 = true)
  · exact (rfl : block mo302 3 0 0 = true)
  · exact (rfl : block mo302 4 0 0 = true)
  · exact mo302B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo302G : graphValid mo302 (boundsBefore KM227) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowM302 : Lower false (varsX 302) (graphGoal 302) 6 := lower_forest (g:=mo302) (i:=0) (hints:=8591017296) (before_sound KM227 VM227) mo302G mo302T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KM302 := extendKnown KM227 6 [(302,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VM302 : Known false KM302 := extend_ok (m:=302) VM227 lowM302 (by decide +kernel)
def mo362Y : Array (Bits × Bits) := #[(0x0,0x0),(0xf003ff0ff87ff007ffff87fffcd47c560003ff,0xa4280a201120a4521481102080501c1694a529),(0x0,0x0),(0xfffc000ffffffff801fff87fc35353a20ffc00,0xc0302c40a002c060580a01010a425122318c63),(0x0,0x0),(0xfffffff0007ffffffe00007ffcafd11df0001f,0x140b002c20b0080602c220a00a741086318c6),(0x7fffffffffff80004d2fe8007fe0,0x982c08b044c09048130004c100d22c94a5294),(0x0,0x0),(0xffffffffff80000000000000033aa61bff8000,0xe03000c00700e0701c044702118a6118c6318)]
def mo362C : List ColumnInfo := [(2,0,360,0,4),(8,0,354,0,4),(32,0,330,0,4),(64,0,298,0,4)]
def mo362A : List (List Nat) := [[],[131,101],[49,133],[49,81,97,129],[81,134],[81,99,129,49],[97,83],[97,131,81,83],[129,49,83,101],[129,99]]
def mo362D5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xc190fd20fd10
def mo362D6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x7209f
def mo362H6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x7a170000eb0000004e000000f3a600b500000031004000004200000000
def mo362L : Nat → Packing
  | 5 => (2,1,2,0,0,4,0,mo362D5)
  | 6 => (1,0,2,0,0,0,0,mo362D6)
  | _ => emptyPacking
def mo362I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 2 29 0 8 1 3 mo362H6
  | _ => fun _ => none
def mo362 : Forest := ⟨1386,6,fun i => mo362Y[i]?.getD (0,0),mo362C,mo362A,mo362L,mo362I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo362P5_0 : block mo362 5 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo362B5 : block mo362 5 0 2=true := mo362P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo362P6_0 : block mo362 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo362B6 : block mo362 6 0 1=true := mo362P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo362T : checkedTables mo362 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block mo362 0 0 0 = true)
  · exact (rfl : block mo362 1 0 0 = true)
  · exact (rfl : block mo362 2 0 0 = true)
  · exact (rfl : block mo362 3 0 0 = true)
  · exact (rfl : block mo362 4 0 0 = true)
  · exact mo362B5
  · exact mo362B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo362G : graphValid mo362 (boundsBefore KM302) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowM362 : Lower false (varsX 362) (graphGoal 362) 7 := lower_forest (g:=mo362) (i:=0) (hints:=12902752336) (before_sound KM302 VM302) mo362G mo362T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KM362 := extendKnown KM302 7 [(362,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VM362 : Known false KM362 := extend_ok (m:=362) VM302 lowM362 (by decide +kernel)
def mo119Y : Array (Bits × Bits) := #[(0xfffffffffffffffffff569564be49d7500003f,0x482a452129148521214161560be09c05555555),(0xffff000003fffff0000bf42d4ef262a9fc0fc0,0x14c000db00026400669b0244a9260200c30c3),(0xfffffffffc0000000008e7ccb19b907603f000,0x82701609c05837820b88e70c909290763cf3cf),(0x0,0x0),(0xfffffffffffffffffffd0b1e74157ff000003f,0x1380984e026138044c0c0a08741563f0aaaaaa),(0xc8af3b7e9c20e03ffc0,0x1c00e0700381c008700408d325690208c30c30),(0x6754a985f269dfc0000,0xe000ff8003fe000f8006454a904d069df3cf3c),(0x0,0x0),(0x0,0x0)]
def mo119C : List ColumnInfo := [(0,1,102,16,5)]
def mo119A : List (List Nat) := [[],[81,98],[64],[64,81,98]]
def mo119D5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x7f
def mo119L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,mo119D5)
  | _ => emptyPacking
def mo119I (_ _ : Nat) : Option (Nat × Nat) := none
def mo119 : Forest := ⟨1143,5,fun i => mo119Y[i]?.getD (0,0),mo119C,mo119A,mo119L,mo119I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo119P5_0 : block mo119 5 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo119B5 : block mo119 5 0 1=true := mo119P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo119T : checkedTables mo119 5 := by
  intro k hk
  interval_cases k
  · exact (rfl : block mo119 0 0 0 = true)
  · exact (rfl : block mo119 1 0 0 = true)
  · exact (rfl : block mo119 2 0 0 = true)
  · exact (rfl : block mo119 3 0 0 = true)
  · exact (rfl : block mo119 4 0 0 = true)
  · exact mo119B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo119G : graphValid mo119 (boundsBefore KM362) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowM119 : Lower false (varsX 119) (graphGoal 119) 6 := lower_forest (g:=mo119) (i:=0) (hints:=17827156) (before_sound KM362 VM362) mo119G mo119T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KM119 := extendKnown KM362 6 [(119,[]),(315,[129,33,50,99,118]),(461,[49,116,133]),(476,[64,49,16,113,133]),(489,[49,82,116,130,66])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VM119 : Known false KM119 := extend_ok (m:=119) VM362 lowM119 (by decide +kernel)
def mo183Y : Array (Bits × Bits) := #[(0x3ffffffffffffff6783aaace149000fc003f,0x5820a821282148142283aa8c8048145145145),(0xffffffc0003fffc00b82dca6b831203f000fc0,0x29005300db0099066b825ca2a01100c30c30c3),(0x3fffffffc0000009cd1cd9425e200003f000,0x4e109c109c10de0b89cc1cd8025c24d34d34d3),(0x0,0x0),(0x3ffffffffffffffa162d5a1393dfc000003f,0x7004e004e004e00c081605421313128a28a28a),(0xffc00000000000000915e285ddcf000003ffc0,0x270027002700100011a2055d820b2cb2cb2c),(0x0,0x0),(0x4ea977125e06ffffc0000,0x80380038003800200440801104e06c30c30c30),(0x0,0x0)]
def mo183C : List ColumnInfo := [(4,0,179,0,7)]
def mo183A : List (List Nat) := [[],[64]]
def mo183D7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x7f
def mo183L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,mo183D7)
  | _ => emptyPacking
def mo183I (_ _ : Nat) : Option (Nat × Nat) := none
def mo183 : Forest := ⟨1207,7,fun i => mo183Y[i]?.getD (0,0),mo183C,mo183A,mo183L,mo183I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo183P7_0 : block mo183 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo183B7 : block mo183 7 0 1=true := mo183P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo183T : checkedTables mo183 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block mo183 0 0 0 = true)
  · exact (rfl : block mo183 1 0 0 = true)
  · exact (rfl : block mo183 2 0 0 = true)
  · exact (rfl : block mo183 3 0 0 = true)
  · exact (rfl : block mo183 4 0 0 = true)
  · exact (rfl : block mo183 5 0 0 = true)
  · exact (rfl : block mo183 6 0 0 = true)
  · exact mo183B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo183G : graphValid mo183 (boundsBefore KM119) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowM183 : Lower false (varsX 183) (graphGoal 183) 8 := lower_forest (g:=mo183) (i:=0) (hints:=1049940) (before_sound KM119 VM119) mo183G mo183T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KM183 := extendKnown KM119 8 [(183,[]),(219,[50,101]),(423,[32,132,117,100]),(435,[130,50,99]),(438,[32,64,48,131,117,99])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VM183 : Known false KM183 := extend_ok (m:=183) VM119 lowM183 (by decide +kernel)
def mo231Y : Array (Bits × Bits) := #[(0x1ffffe0003ffffc0004cf47f38c1c4a0f8000,0xd40549405680a9480ab4c543f3041c48739ce7),(0xfe000000003ffffffff9f4784b320bfdf07c1f,0x98000d800b0001900121d010022008d8108421),(0xffffffffffc00000000273b2d655ec120003e0,0xe0918e048c1231e091c273b2d6102812b5ad6b),(0x0,0x0),(0x0,0x0),(0xfffffffffffffffffffa859f07c5f6a40003ff,0x12610091024c2012200040d01c5d6254a5294),(0x2456978fe6252007c00,0x1c7e011e038fc023c02056978de6203ef7bde),(0x73aa5b8895b2bff8000,0x1f8001e003f0003c0022aa4088943238c6318),(0x0,0x0)]
def mo231C : List ColumnInfo := [(0,1,102,128,5),(0,4,195,32,5),(1,0,230,0,5),(4,0,227,0,5),(64,0,167,0,5),(32,4,195,0,4),(128,1,102,0,4)]
def mo231A : List (List Nat) := [[],[32,117]]
def mo231D6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1ac6881ff
def mo231L : Nat → Packing
  | 6 => (1,0,3,0,0,0,0,mo231D6)
  | _ => emptyPacking
def mo231I (_ _ : Nat) : Option (Nat × Nat) := none
def mo231 : Forest := ⟨1255,6,fun i => mo231Y[i]?.getD (0,0),mo231C,mo231A,mo231L,mo231I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo231P6_0 : block mo231 6 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo231B6 : block mo231 6 0 1=true := mo231P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo231T : checkedTables mo231 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block mo231 0 0 0 = true)
  · exact (rfl : block mo231 1 0 0 = true)
  · exact (rfl : block mo231 2 0 0 = true)
  · exact (rfl : block mo231 3 0 0 = true)
  · exact (rfl : block mo231 4 0 0 = true)
  · exact (rfl : block mo231 5 0 0 = true)
  · exact mo231B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo231G : graphValid mo231 (boundsBefore KM183) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowM231 : Lower false (varsX 231) (graphGoal 231) 7 := lower_forest (g:=mo231) (i:=0) (hints:=17827159) (before_sound KM183 VM183) mo231G mo231T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KM231 := extendKnown KM183 7 [(231,[]),(235,[50,101]),(238,[32,48,101,117]),(246,[32,64,48,117]),(483,[130,50,67])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VM231 : Known false KM231 := extend_ok (m:=231) VM183 lowM231 (by decide +kernel)
def mo243Y : Array (Bits × Bits) := #[(0xffffffff8007ffffffdc9363d9415ac00f801f,0x90a048102502488120c93218140528a5294a5),(0xfffffffffffc002a44b4afe8f401f07fe0,0x2c000a00000010008a00a0aa803006318c63),(0x0,0x0),(0x0,0x0),(0xffff00000007ffffffef798a1a360b7e00001f,0x1230092c04a049202422608a1a240954a5294a),(0xfffffffffff8000000201b64366f4d800003e0,0x5c40ae3028c571c147201b44146f4db9ce739c),(0x24569b45573c00007c00,0x9f80cfc04f067e027824561b45570c39ce739c),(0x13aa5dc49781bfff8000,0xe000f000700780038011085444138021084210),(0x0,0x0)]
def mo243C : List ColumnInfo := [(32,0,211,0,7)]
def mo243A : List (List Nat) := [[],[101],[64],[64,101]]
def mo243D7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x7f
def mo243L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,mo243D7)
  | _ => emptyPacking
def mo243I (_ _ : Nat) : Option (Nat × Nat) := none
def mo243 : Forest := ⟨1267,7,fun i => mo243Y[i]?.getD (0,0),mo243C,mo243A,mo243L,mo243I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo243P7_0 : block mo243 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo243B7 : block mo243 7 0 1=true := mo243P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo243T : checkedTables mo243 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block mo243 0 0 0 = true)
  · exact (rfl : block mo243 1 0 0 = true)
  · exact (rfl : block mo243 2 0 0 = true)
  · exact (rfl : block mo243 3 0 0 = true)
  · exact (rfl : block mo243 4 0 0 = true)
  · exact (rfl : block mo243 5 0 0 = true)
  · exact (rfl : block mo243 6 0 0 = true)
  · exact mo243B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo243G : graphValid mo243 (boundsBefore KM231) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowM243 : Lower false (varsX 243) (graphGoal 243) 8 := lower_forest (g:=mo243) (i:=0) (hints:=17825876) (before_sound KM231 VM231) mo243G mo243T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KM243 := extendKnown KM231 8 [(243,[]),(486,[32,132,101,117])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VM243 : Known false KM243 := extend_ok (m:=243) VM231 lowM243 (by decide +kernel)
def mo311Y : Array (Bits × Bits) := #[(0x3fffffffffffffffff1685c8b653b7c000003f,0x8a4151484a290a44141605c896413355555555),(0xfffff80000ffffe0009e42fc7d4c8400000fc0,0x2c0a65836cb04c88669e42fc350c8433cf3cf3),(0x3fffffffff00000000af785c83b0ab00fff000,0x13800270006f00b88b305c8010aa030c30c3),(0x0,0x0),(0x3fffffffffffffffffd0b1c4a9bfd48000003f,0x309c061380c27010c0c0b00429bec4aaaaaaaa),(0xc00000000000000000c8af2b5ecc4a7f03ffc0,0xe0001c00038001000089014ac0404c30c30c),(0x0,0x0),(0x0,0x0),(0x6754b7112b657ffc0000,0x3f0007e000fc001e006444a2112b0530c30c30)]
def mo311C : List ColumnInfo := [(0,1,294,16,6)]
def mo311A : List (List Nat) := [[],[130],[64],[64,130]]
def mo311D6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x7f
def mo311L : Nat → Packing
  | 6 => (1,0,1,0,0,0,0,mo311D6)
  | _ => emptyPacking
def mo311I (_ _ : Nat) : Option (Nat × Nat) := none
def mo311 : Forest := ⟨1335,6,fun i => mo311Y[i]?.getD (0,0),mo311C,mo311A,mo311L,mo311I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo311P6_0 : block mo311 6 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo311B6 : block mo311 6 0 1=true := mo311P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo311T : checkedTables mo311 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block mo311 0 0 0 = true)
  · exact (rfl : block mo311 1 0 0 = true)
  · exact (rfl : block mo311 2 0 0 = true)
  · exact (rfl : block mo311 3 0 0 = true)
  · exact (rfl : block mo311 4 0 0 = true)
  · exact (rfl : block mo311 5 0 0 = true)
  · exact mo311B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo311G : graphValid mo311 (boundsBefore KM243) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowM311 : Lower false (varsX 311) (graphGoal 311) 7 := lower_forest (g:=mo311) (i:=0) (hints:=8590984532) (before_sound KM243 VM243) mo311G mo311T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KM311 := extendKnown KM243 7 [(311,[]),(407,[32,132,117,101]),(411,[48,32,132,117,101])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VM311 : Known false KM311 := extend_ok (m:=311) VM243 lowM311 (by decide +kernel)
def mo366Y : Array (Bits × Bits) := #[(0x0,0x0),(0xf8001fffffff00ff1d203397a2ac000003f03f,0x520d4825205216141d002390a2a91451451451),(0xffffe0007fffff00637e8b807608003f000fc0,0x60498136046424262336098066085145145145),(0xffffffff800000009d8e48e9a5400fc0fc0000,0x800e003801783838150a48c1a54030c30c30c3),(0x0,0x0),(0xffffffffffffffffa049c585ccf7f000000fff,0x900240098000008048c0050854a28a28a28a),(0x9175383e5b400000fff000,0x4e013804e0040408075102e5802cb2cb2cb2c),(0x0,0x0),(0x4e937660389bffff000000,0x7001c00700080804881362010830c30c30c30)]
def mo366C : List ColumnInfo := [(2,0,364,0,7),(4,0,362,0,7),(8,0,358,0,7),(0,64,292,10,6),(64,0,302,0,6),(32,0,334,0,5)]
def mo366A : List (List Nat) := [[],[49,133]]
def mo366D6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x30bd58453be58053
def mo366D7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x10e8a46008543a2918026a03faa7fc53
def mo366H7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x2e000439
def mo366D8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x468817f
def mo366H8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1c02
def mo366L : Nat → Packing
  | 6 => (2,2,3,0,0,3,0,mo366D6)
  | 7 => (2,1,3,0,0,6,0,mo366D7)
  | 8 => (1,0,3,0,0,0,0,mo366D8)
  | _ => emptyPacking
def mo366I : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 1 5 0 6 1 1 mo366H7
  | 8 => lookupWord 1 3 0 5 1 0 mo366H8
  | _ => fun _ => none
def mo366 : Forest := ⟨1390,8,fun i => mo366Y[i]?.getD (0,0),mo366C,mo366A,mo366L,mo366I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo366P6_0 : block mo366 6 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo366B6 : block mo366 6 0 2=true := mo366P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo366P7_0 : block mo366 7 0 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo366B7 : block mo366 7 0 2=true := mo366P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo366P8_0 : block mo366 8 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo366B8 : block mo366 8 0 1=true := mo366P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo366T : checkedTables mo366 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block mo366 0 0 0 = true)
  · exact (rfl : block mo366 1 0 0 = true)
  · exact (rfl : block mo366 2 0 0 = true)
  · exact (rfl : block mo366 3 0 0 = true)
  · exact (rfl : block mo366 4 0 0 = true)
  · exact (rfl : block mo366 5 0 0 = true)
  · exact mo366B6
  · exact mo366B7
  · exact mo366B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo366G : graphValid mo366 (boundsBefore KM311) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowM366 : Lower false (varsX 366) (graphGoal 366) 9 := lower_forest (g:=mo366) (i:=0) (hints:=8607786320) (before_sound KM311 VM311) mo366G mo366T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KM366 := extendKnown KM311 9 [(366,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VM366 : Known false KM366 := extend_ok (m:=366) VM311 lowM366 (by decide +kernel)
def mo413Y : Array (Bits × Bits) := #[(0xffffffffffffffffff324ac3e653ba80000fff,0x50802a20128805201432424184033a09249249),(0x0,0x0),(0x3ffff00003ffff000b5b54027c1e640fc0000,0x98294c0adb02a64266b4a14027c1c6471c71c7),(0x3ffffffffc00000000668749bb5cb3f000000,0xe032700c9c033784b80468608bb5cb071c71c7),(0x3ffffffffffffffff58b1cca9be948003f03f,0x1038040e0103800c048318421348492492492),(0x0,0x0),(0x0,0x0),(0xfc000000000000000048af2b5ecc4a4003ffc0,0x23c008f0023c00700008c2a5ac84064924924),(0xe754b7112b657ffc0000,0x3c000f0003c000800431497100a2038e38e38)]
def mo413C : List ColumnInfo := [(0,256,145,12,6)]
def mo413A : List (List Nat) := [[],[116],[50],[50,116],[64],[64,112],[64,50],[64,50,112],[112,64],[112],[112,50,64],[112,50]]
def mo413D6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x7f
def mo413L : Nat → Packing
  | 6 => (1,0,1,0,0,0,0,mo413D6)
  | _ => emptyPacking
def mo413I (_ _ : Nat) : Option (Nat × Nat) := none
def mo413 : Forest := ⟨1437,6,fun i => mo413Y[i]?.getD (0,0),mo413C,mo413A,mo413L,mo413I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo413P6_0 : block mo413 6 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo413B6 : block mo413 6 0 1=true := mo413P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo413T : checkedTables mo413 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block mo413 0 0 0 = true)
  · exact (rfl : block mo413 1 0 0 = true)
  · exact (rfl : block mo413 2 0 0 = true)
  · exact (rfl : block mo413 3 0 0 = true)
  · exact (rfl : block mo413 4 0 0 = true)
  · exact (rfl : block mo413 5 0 0 = true)
  · exact mo413B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo413G : graphValid mo413 (boundsBefore KM366) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowM413 : Lower false (varsX 413) (graphGoal 413) 7 := lower_forest (g:=mo413) (i:=0) (hints:=8589969412) (before_sound KM366 VM366) mo413G mo413T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KM413 := extendKnown KM366 7 [(413,[]),(441,[50,82]),(473,[98,131,82])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VM413 : Known false KM413 := extend_ok (m:=413) VM366 lowM413 (by decide +kernel)
def mo427Y : Array (Bits × Bits) := #[(0xffffff80000ffffe000197fe6b4815500003e0,0x5140952836a504a482b192fe61481540b5ad6b),(0x3fffffffffffffffff8d2a2d536a4ee007c1f,0x9980263004c600c9012092a2d43000e894a529),(0x0,0x0),(0x3fffffffff0000000055b43e4d5c5180f8000,0xe0153802a70056f015c543436455c418739ce7),(0x0,0x0),(0x3fffffffffffffffffaa58e2545fea5f0001f,0x19c00338006700260025082145f6046318c6),(0x0,0x0),(0xfc00000000000000000245795afe6252007fe0,0x21e0043c0087800380245010a8662134a5294),(0x73aa5b8895b2bff8000,0x3e0007c000f8001c00218a4988809238c6318)]
def mo427C : List ColumnInfo := [(0,1,298,128,5),(0,8,163,256,5),(1,0,426,0,5),(8,0,419,0,5)]
def mo427A : List (List Nat) := [[],[48,81,135]]
def mo427D6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xe413f
def mo427L : Nat → Packing
  | 6 => (1,0,2,0,0,0,0,mo427D6)
  | _ => emptyPacking
def mo427I (_ _ : Nat) : Option (Nat × Nat) := none
def mo427 : Forest := ⟨1451,6,fun i => mo427Y[i]?.getD (0,0),mo427C,mo427A,mo427L,mo427I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo427P6_0 : block mo427 6 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo427B6 : block mo427 6 0 1=true := mo427P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo427T : checkedTables mo427 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block mo427 0 0 0 = true)
  · exact (rfl : block mo427 1 0 0 = true)
  · exact (rfl : block mo427 2 0 0 = true)
  · exact (rfl : block mo427 3 0 0 = true)
  · exact (rfl : block mo427 4 0 0 = true)
  · exact (rfl : block mo427 5 0 0 = true)
  · exact mo427B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo427G : graphValid mo427 (boundsBefore KM413) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowM427 : Lower false (varsX 427) (graphGoal 427) 7 := lower_forest (g:=mo427) (i:=0) (hints:=12885983319) (before_sound KM413 VM413) mo427G mo427T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KM427 := extendKnown KM413 7 [(427,[]),(442,[48,81,32,66,135]),(459,[131,101]),(462,[32,49,113,101,129])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VM427 : Known false KM427 := extend_ok (m:=427) VM413 lowM427 (by decide +kernel)
def mo430Y : Array (Bits × Bits) := #[(0x0,0x0),(0x1ffffffffc003ffd524a373e833c0007c1f,0xd4804a40148058051520013288339294a529),(0xfffe0000fffffffc003ed51a38816c800f83e0,0x14980a6c0519049049be541230016086318c63),(0xffffffff0000000000073b22915bd881f00000,0x58e02c70165e09e09e063922115bd88e739ce7),(0x0,0x0),(0xffffffffffffffffffc859e43c4e4f7e0003ff,0x6100308018601101100009e00c420c48421084),(0x0,0x0),(0x4569b47773c00007c00,0x7e013f009f801e01e000569a45770c2d6b5ad6),(0x33aa5dc49781bfff8000,0x8001c000e00020020001820dc08401318c6318)]
def mo430C : List ColumnInfo := [(8,0,422,0,7)]
def mo430A : List (List Nat) := [[]]
def mo430D7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x7f
def mo430L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,mo430D7)
  | _ => emptyPacking
def mo430I (_ _ : Nat) : Option (Nat × Nat) := none
def mo430 : Forest := ⟨1454,7,fun i => mo430Y[i]?.getD (0,0),mo430C,mo430A,mo430L,mo430I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo430P7_0 : block mo430 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo430B7 : block mo430 7 0 1=true := mo430P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo430T : checkedTables mo430 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block mo430 0 0 0 = true)
  · exact (rfl : block mo430 1 0 0 = true)
  · exact (rfl : block mo430 2 0 0 = true)
  · exact (rfl : block mo430 3 0 0 = true)
  · exact (rfl : block mo430 4 0 0 = true)
  · exact (rfl : block mo430 5 0 0 = true)
  · exact (rfl : block mo430 6 0 0 = true)
  · exact mo430B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo430G : graphValid mo430 (boundsBefore KM427) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowM430 : Lower false (varsX 430) (graphGoal 430) 8 := lower_forest (g:=mo430) (i:=0) (hints:=8859452752) (before_sound KM427 VM427) mo430G mo430T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KM430 := extendKnown KM427 8 [(430,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VM430 : Known false KM430 := extend_ok (m:=430) VM427 lowM430 (by decide +kernel)
def mo437Y : Array (Bits × Bits) := #[(0xffffffc1ffffc92d389940f740000007fc01ff,0x80a2008441100829308000f708a45229148a45),(0x0,0x0),(0xffffffff81a52a0abb8d8801ff00003fe00,0x12c0450008209a50a02b1090026130984c2613),(0x0,0x0),(0xfff00001ffffefe1835e2102c0000ff80001ff,0x304160882402700815a2100d148a45229148a),(0xfffffffe0000209965726e4d3fe0000003fe00,0x240098001381208141106c4d0582c160b0582c),(0x0,0x0),(0x24d69a05573c00000ffffc0000,0x3808e0111c0200d60a05560826130984c26130),(0x132a5dc49781bffff000000000,0xc00f0021e004012a1cc48300b81c0e070381c0)]
def mo437C : List ColumnInfo := [(0,1,292,144,6),(0,4,145,288,6),(0,16,292,129,6),(0,32,145,260,6),(0,128,292,17,6),(1,0,436,0,6),(4,0,433,0,6),(16,0,421,0,6),(32,0,405,0,6),(128,0,309,0,6)]
def mo437A : List (List Nat) := [[],[133],[116],[116,133],[82],[82,130],[82,116],[82,116,130],[130,82],[130],[130,116,82],[130,116],[32,84,135],[32,84,116,132],[32,132,84,117],[32,132,117],[32,64,80,135],[32,64,80,112,128],[32,64,128,80,117],[32,64,128,117],[32,112,84,64,132],[32,112,84,128],[32,112,132,80],[32,112,132,84,80],[64],[64,133],[64,112],[64,112,133],[64,82],[64,82,130],[64,82,112],[64,82,112,130],[64,130,82],[64,130],[64,130,112,82],[64,130,112],[80,32,66,135],[80,32,66,116,132],[80,32,132,66,114],[80,32,132,114],[80,66,135],[80,66,112,128],[80,66,130,114],[80,66,130,112,32],[80,114,66,132],[80,114,66,64,128],[80,114,132],[80,114,132,64],[112,64],[112,64,133],[112],[112,133],[112,82,64],[112,82,64,130],[112,82],[112,82,130],[112,130,64,82],[112,130,64],[112,130,82],[112,130],[128,32,66,84,117],[128,32,66,117],[128,32,84,114],[128,32,84,116,66],[128,66,80,117],[128,66,117],[128,66,82,32,114],[128,66,82,114],[128,114,66,80,84],[128,114,66,84],[128,114,84,64],[128,114,84]]
def mo437D8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x98765432102bf
def mo437L : Nat → Packing
  | 8 => (1,0,4,0,0,0,0,mo437D8)
  | _ => emptyPacking
def mo437I (_ _ : Nat) : Option (Nat × Nat) := none
def mo437 : Forest := ⟨1461,8,fun i => mo437Y[i]?.getD (0,0),mo437C,mo437A,mo437L,mo437I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo437P8_0 : block mo437 8 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo437B8 : block mo437 8 0 1=true := mo437P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo437T : checkedTables mo437 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block mo437 0 0 0 = true)
  · exact (rfl : block mo437 1 0 0 = true)
  · exact (rfl : block mo437 2 0 0 = true)
  · exact (rfl : block mo437 3 0 0 = true)
  · exact (rfl : block mo437 4 0 0 = true)
  · exact (rfl : block mo437 5 0 0 = true)
  · exact (rfl : block mo437 6 0 0 = true)
  · exact (rfl : block mo437 7 0 0 = true)
  · exact mo437B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo437G : graphValid mo437 (boundsBefore KM430) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowM437 : Lower false (varsX 437) (graphGoal 437) 9 := lower_forest (g:=mo437) (i:=0) (hints:=8592033028) (before_sound KM430 VM430) mo437G mo437T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KM437 := extendKnown KM430 9 [(437,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VM437 : Known false KM437 := extend_ok (m:=437) VM430 lowM437 (by decide +kernel)
def mo490Y : Array (Bits × Bits) := #[(0x0,0x0),(0xfffff8007fffffffffde2d8339c932c00f83ff,0x4200100100008008001a29002080321294a529),(0x0,0x0),(0x1fffffff8007fffc0039d3724fa05c01f07c00,0x8028a02402500a1011b953224b001006318c63),(0x0,0x0),(0xe00000000007ffffffcd320e9a768b7e00001f,0xb2c04e04e02ca02505120e1a64884c6318c6),(0xfffffffffff80000000251e4366f4d80007fe0,0x14c30288288530c1460000c4146f4da94a5294),(0x45e9b45573c000f8000,0x18fc04f04f063f027804569b45570c2d6b5ad6),(0x33aa5dc49781bff00000,0x1f0007007007c0038002a851849301b18c6318)]
def mo490C : List ColumnInfo := [(128,0,362,0,7)]
def mo490A : List (List Nat) := [[],[131,101]]
def mo490D7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x7f
def mo490L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,mo490D7)
  | _ => emptyPacking
def mo490I (_ _ : Nat) : Option (Nat × Nat) := none
def mo490 : Forest := ⟨1514,7,fun i => mo490Y[i]?.getD (0,0),mo490C,mo490A,mo490L,mo490I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo490P7_0 : block mo490 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo490B7 : block mo490 7 0 1=true := mo490P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo490T : checkedTables mo490 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block mo490 0 0 0 = true)
  · exact (rfl : block mo490 1 0 0 = true)
  · exact (rfl : block mo490 2 0 0 = true)
  · exact (rfl : block mo490 3 0 0 = true)
  · exact (rfl : block mo490 4 0 0 = true)
  · exact (rfl : block mo490 5 0 0 = true)
  · exact (rfl : block mo490 6 0 0 = true)
  · exact mo490B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo490G : graphValid mo490 (boundsBefore KM437) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowM490 : Lower false (varsX 490) (graphGoal 490) 8 := lower_forest (g:=mo490) (i:=0) (hints:=13171187792) (before_sound KM437 VM437) mo490G mo490T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KM490 := extendKnown KM437 8 [(490,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VM490 : Known false KM490 := extend_ok (m:=490) VM437 lowM490 (by decide +kernel)
def mo247Y : Array (Bits × Bits) := #[(0xf71d5750119a8355f2a6c4320000ff000000ff,0x410d5750010a8154f226002015151515151515),(0x809e4bd873461a0d44223e700ff00ff00ff00,0x6009c08004344120d442020703030303030303),(0x2bc5c88dae5895e205f3a0e00000000ff0000,0x829c5c88d2e4091e204f32064f4f4f4f4f4f4f),(0x0,0x0),(0xfbf2a182a4161cba4977d412ff0000000000ff,0xaf0a080841418a00951d4122a2a2a2a2a2a2a),(0x8264b344869b6e518791d3900000000ffff00,0x82203340809b6c108300d38b0b0b0b0b0b0b0),(0x93534d287c9ef0209acb5cc000000ff000000,0x934345283c9ae0209acb5c8fcfcfcfcfcfcfc),(0x4ca924f70cd3e0baf802a80ffffff00000000,0x402000f70c1260b00802880c0c0c0c0c0c0c0),(0x0,0x0)]
def mo247C : List ColumnInfo := [(0,4,211,32,8),(4,0,243,0,8),(64,0,183,0,8),(0,64,181,2,7),(1,0,246,0,7),(16,0,231,0,7),(32,0,211,0,7),(32,4,211,0,7),(0,1,102,144,6),(0,16,102,129,6),(2,0,181,0,6),(2,64,181,0,6),(128,0,119,0,6),(1,16,102,128,5),(128,1,102,16,5),(128,16,102,1,5)]
def mo247A : List (List Nat) := [[],[64]]
def mo247D8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1ee5a517314921460039cd522e6292428c006b98a4a2e624851800d7358b45cc524851800e7b96abdab41c605c5da0891e803fd61ff583fd30ff4437d65
def mo247D9 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x16eca842047f
def mo247H9 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x6200000000000010000000000073000000000000000084b90000000b00f10000000000
def mo247L : Nat → Packing
  | 8 => (5,1,4,0,0,9,0,mo247D8)
  | 9 => (1,0,4,0,0,0,0,mo247D9)
  | _ => emptyPacking
def mo247I : Nat → Nat → Option (Nat × Nat)
  | 9 => lookupWord 1 37 0 8 3 1 mo247H9
  | _ => fun _ => none
def mo247 : Forest := ⟨1271,9,fun i => mo247Y[i]?.getD (0,0),mo247C,mo247A,mo247L,mo247I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo247P8_0 : block mo247 8 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo247P8_1 : block mo247 8 1 4=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo247B8 : block mo247 8 0 5=true := (@block_merge mo247 8 0 1 4 mo247P8_0 mo247P8_1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo247P9_0 : block mo247 9 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo247B9 : block mo247 9 0 1=true := mo247P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo247T : checkedTables mo247 9 := by
  intro k hk
  interval_cases k
  · exact (rfl : block mo247 0 0 0 = true)
  · exact (rfl : block mo247 1 0 0 = true)
  · exact (rfl : block mo247 2 0 0 = true)
  · exact (rfl : block mo247 3 0 0 = true)
  · exact (rfl : block mo247 4 0 0 = true)
  · exact (rfl : block mo247 5 0 0 = true)
  · exact (rfl : block mo247 6 0 0 = true)
  · exact (rfl : block mo247 7 0 0 = true)
  · exact mo247B8
  · exact mo247B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo247G : graphValid mo247 (boundsBefore KM490) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowM247 : Lower false (varsX 247) (graphGoal 247) 10 := lower_forest (g:=mo247) (i:=0) (hints:=17827156) (before_sound KM490 VM490) mo247G mo247T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KM247 := extendKnown KM490 10 [(247,[]),(251,[50,101]),(487,[32,132,117]),(499,[130,50]),(502,[32,64,48,131,117])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VM247 : Known false KM247 := extend_ok (m:=247) VM490 lowM247 (by decide +kernel)
def mo253Y : Array (Bits × Bits) := #[(0x6842e55a0aee4af6e969292000fff000000fff,0x6042c14202ae48f26061290055055055055055),(0x0,0x0),(0x113fc2d054a15c1deca6677000000000fff000,0x112ec2d014815c15eca6026533533533533533),(0xe7345117acfed591529ac05000000fff000000,0x453051162c7ed4115218c0530f30f30f30f30f),(0x1cec18b8375a2919902598bfff000000000fff,0x1c2c10b83140010980009030aa0aa0aa0aa0aa),(0xc999b227796972a934516f1000000000fff000,0xc8913027696822a810516d1accaccaccaccacc),(0xa6468ba7b080afe44797156000000fff000000,0xa2468aa190802be40587152cf0cf0cf0cf0cf0),(0x52b27ce54d15b2661d4e90cffffff000000000,0x2902c054c11b2041d0e00cf00f00f00f00f00),(0x0,0x0)]
def mo253C : List ColumnInfo := [(0,4,217,32,7)]
def mo253A : List (List Nat) := [[],[116],[99],[99,116],[50,101],[50,116,101],[50,82,98],[50,82,116,98],[82],[82,116],[82,99],[82,99,116],[98,50,83],[98,50,116,83],[98,83],[98,83,116],[64],[64,112],[64,99],[64,99,112],[64,50,101],[64,50,112,101],[64,50,82,98],[64,50,82,112,98],[64,82],[64,82,112],[64,82,99],[64,82,99,112],[64,98,50,83],[64,98,50,112,83],[64,98,83],[64,98,83,112],[112,64],[112],[112,99,64],[112,99],[112,50,64,101],[112,50,101],[112,50,82,64,98],[112,50,82,98],[112,82,64],[112,82],[112,82,99,64],[112,82,99],[112,98,50,64,83],[112,98,50,83],[112,98,83,64],[112,98,83]]
def mo253D7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xff
def mo253L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,mo253D7)
  | _ => emptyPacking
def mo253I (_ _ : Nat) : Option (Nat × Nat) := none
def mo253 : Forest := ⟨1277,7,fun i => mo253Y[i]?.getD (0,0),mo253C,mo253A,mo253L,mo253I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo253P7_0 : block mo253 7 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo253B7 : block mo253 7 0 1=true := mo253P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo253T : checkedTables mo253 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block mo253 0 0 0 = true)
  · exact (rfl : block mo253 1 0 0 = true)
  · exact (rfl : block mo253 2 0 0 = true)
  · exact (rfl : block mo253 3 0 0 = true)
  · exact (rfl : block mo253 4 0 0 = true)
  · exact (rfl : block mo253 5 0 0 = true)
  · exact (rfl : block mo253 6 0 0 = true)
  · exact mo253B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo253G : graphValid mo253 (boundsBefore KM247) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowM253 : Lower false (varsX 253) (graphGoal 253) 8 := lower_forest (g:=mo253) (i:=0) (hints:=52454660) (before_sound KM247 VM247) mo253G mo253T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KM253 := extendKnown KM247 8 [(253,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VM253 : Known false KM253 := extend_ok (m:=253) VM247 lowM253 (by decide +kernel)
def mo375Y : Array (Bits × Bits) := #[(0xbaad5d0d78056bc21b38a5c0000000000003ff,0x8aad590978056ac21a38204555555555555555),(0x82ccf2f582768288becec0e00000ffc00ffc00,0x82888215827482089ec8c0a30cc330cc330cc3),(0x69b4819308b55c53f6816a9003ff003ff00000,0x29b4809100844813e68168803c0f03c0f03c0f),(0x0,0x0),(0xf5418ea6a4aac12247f88d90000000000003ff,0x754086a684aa812045c08d9aaaaaaaaaaaaaaa),(0x4c9330085dcbae344d52537ffc00003ffffc00,0x440330080c03240401120350c0300c0300c030),(0x6a6cd6ea9e8415ffa03619000000ffc0000000,0x686454ea1c8015f72036190cf33ccf33ccf33c),(0x0,0x0),(0x952a4f3b5578326d10e5b80fffff0000000000,0x90084f22517812681064900f03c0f03c0f03c0)]
def mo375C : List ColumnInfo := [(0,1,358,16,8)]
def mo375A : List (List Nat) := [[],[130],[64],[64,130]]
def mo375D8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xff
def mo375L : Nat → Packing
  | 8 => (1,0,1,0,0,0,0,mo375D8)
  | _ => emptyPacking
def mo375I (_ _ : Nat) : Option (Nat × Nat) := none
def mo375 : Forest := ⟨1399,8,fun i => mo375Y[i]?.getD (0,0),mo375C,mo375A,mo375L,mo375I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo375P8_0 : block mo375 8 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo375B8 : block mo375 8 0 1=true := mo375P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo375T : checkedTables mo375 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block mo375 0 0 0 = true)
  · exact (rfl : block mo375 1 0 0 = true)
  · exact (rfl : block mo375 2 0 0 = true)
  · exact (rfl : block mo375 3 0 0 = true)
  · exact (rfl : block mo375 4 0 0 = true)
  · exact (rfl : block mo375 5 0 0 = true)
  · exact (rfl : block mo375 6 0 0 = true)
  · exact (rfl : block mo375 7 0 0 = true)
  · exact mo375B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo375G : graphValid mo375 (boundsBefore KM253) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowM375 : Lower false (varsX 375) (graphGoal 375) 9 := lower_forest (g:=mo375) (i:=0) (hints:=8607761748) (before_sound KM253 VM253) mo375G mo375T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KM375 := extendKnown KM253 9 [(375,[]),(381,[49,133]),(471,[32,132,117]),(493,[49,116,133]),(508,[64,49,16,113,133])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VM375 : Known false KM375 := extend_ok (m:=375) VM253 lowM375 (by decide +kernel)
def mo379Y : Array (Bits × Bits) := #[(0x9aa01f4df80ffb003a38e5c0000000000003ff,0x8a201d49780dfb003a38604555555555555555),(0x827570f502711a035f8e8af00000003ffffc00,0x805540f500701a005e8c80a30cc330cc330cc3),(0x0,0x0),(0x6d1c819308bfccd0f2a1229003ffffc0000000,0x2d1c0091008bc890628122903c0f03c0f03c0f),(0xf1c98ea6a4a2c12a43dccd90000000000003ff,0x71c982a684a2002a41c48d9aaaaaaaaaaaaaaa),(0x4c9b30085dcbae3c4956537ffc0000000ffc00,0x4c8a30080c8ba41401524350f03c0f03c0f03c),(0x6a64d6ea9e8415f7a43219000000fffff00000,0x4220960a9e0405678032190cc330cc330cc330),(0x0,0x0),(0x952a4f3b5578326d10e5b80fffff0000000000,0x90204f22517012691024980f03c0f03c0f03c0)]
def mo379C : List ColumnInfo := [(0,1,362,16,8)]
def mo379A : List (List Nat) := [[],[131,101],[49,133],[49,81,97,129],[81,134],[81,99,129,49],[97,83],[97,131,81,83],[129,49,83,101],[129,99],[64],[64,131,101],[64,49,133],[64,49,81,97,129],[64,81,134],[64,81,99,129,49],[64,97,83],[64,97,131,81,83],[64,129,49,83,101],[64,129,99]]
def mo379D8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xff
def mo379L : Nat → Packing
  | 8 => (1,0,1,0,0,0,0,mo379D8)
  | _ => emptyPacking
def mo379I (_ _ : Nat) : Option (Nat × Nat) := none
def mo379 : Forest := ⟨1403,8,fun i => mo379Y[i]?.getD (0,0),mo379C,mo379A,mo379L,mo379I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo379P8_0 : block mo379 8 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo379B8 : block mo379 8 0 1=true := mo379P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo379T : checkedTables mo379 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block mo379 0 0 0 = true)
  · exact (rfl : block mo379 1 0 0 = true)
  · exact (rfl : block mo379 2 0 0 = true)
  · exact (rfl : block mo379 3 0 0 = true)
  · exact (rfl : block mo379 4 0 0 = true)
  · exact (rfl : block mo379 5 0 0 = true)
  · exact (rfl : block mo379 6 0 0 = true)
  · exact (rfl : block mo379 7 0 0 = true)
  · exact mo379B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo379G : graphValid mo379 (boundsBefore KM375) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowM379 : Lower false (varsX 379) (graphGoal 379) 9 := lower_forest (g:=mo379) (i:=0) (hints:=12902752340) (before_sound KM375 VM375) mo379G mo379T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KM379 := extendKnown KM375 9 [(379,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VM379 : Known false KM379 := extend_ok (m:=379) VM375 lowM379 (by decide +kernel)
def mo431Y : Array (Bits × Bits) := #[(0x919f1595cd3ce058f0a8558000003f000,0xaaac919b1595cd1c8058f0a005934d34d34d3),(0xffffe3a71fee12580803d3d700d40000fc003f,0x4cc81871fca00180803d31600551451451451),(0x1c62c74a0bb161589838517c003f000fc0,0x470f002247480b816058983851545145145145),(0x13b9ff183d8275b240921ac00fc0000000,0x97f012a9ff183d827590409212c0f3cf3cf3cf),(0x0,0x0),(0xfffff40cb260d0ce115566a936eff000000fff,0x18001408a020d0461104008106a8a28a28a28a),(0x0,0x0),(0x122a49a54f279ea821f695300000fff000,0xe00012204024032616a820e09522cb2cb2cb2c),(0x9d5249ea134f8aebe00ea03ffff000000,0x9540086003088222600a8030c30c30c30)]
def mo431C : List ColumnInfo := [(1,0,430,0,8)]
def mo431A : List (List Nat) := [[]]
def mo431D8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xff
def mo431L : Nat → Packing
  | 8 => (1,0,1,0,0,0,0,mo431D8)
  | _ => emptyPacking
def mo431I (_ _ : Nat) : Option (Nat × Nat) := none
def mo431 : Forest := ⟨1455,8,fun i => mo431Y[i]?.getD (0,0),mo431C,mo431A,mo431L,mo431I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo431P8_0 : block mo431 8 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo431B8 : block mo431 8 0 1=true := mo431P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo431T : checkedTables mo431 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block mo431 0 0 0 = true)
  · exact (rfl : block mo431 1 0 0 = true)
  · exact (rfl : block mo431 2 0 0 = true)
  · exact (rfl : block mo431 3 0 0 = true)
  · exact (rfl : block mo431 4 0 0 = true)
  · exact (rfl : block mo431 5 0 0 = true)
  · exact (rfl : block mo431 6 0 0 = true)
  · exact (rfl : block mo431 7 0 0 = true)
  · exact mo431B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo431G : graphValid mo431 (boundsBefore KM379) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowM431 : Lower false (varsX 431) (graphGoal 431) 9 := lower_forest (g:=mo431) (i:=0) (hints:=8591017303) (before_sound KM379 VM379) mo431G mo431T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KM431 := extendKnown KM379 9 [(446,[64])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VM431 : Known false KM431 := extend_ok (m:=431) VM379 lowM431 (by decide +kernel)
def mo439Y : Array (Bits × Bits) := #[(0x4484654115f52ea25f87000000000ff80001ff,0x4084254105152ea05b06229148a45229148a45),(0x8289b929b2222aec33e80000001ff00003fe00,0x8289212932222ae831e861b0d86c361b0d86c3),(0xf89a258e20557019d0c8007fc0000007fc0000,0xa09a25882045701140c80984c26130984c2613),(0x0,0x0),(0xb0664bb95626830b80bb00003fe000000001ff,0xb0204ab81222800b80b945229148a45229148a),(0x9b598a4289b8d92aa1cff8000000007fffe00,0x9049804009881028a14160b0582c160b0582c),(0x0,0x0),(0x2e4a165acbc86174053400003ffffff8000000,0xc421002c8c841140400984c26130984c26130),(0xd52160534a2adc6d5842ffffc0000000000000,0x542140534a220c6c1002e070381c0e070381c0)]
def mo439C : List ColumnInfo := [(2,0,437,0,9),(1,0,438,0,8),(4,0,435,0,8),(16,0,423,0,8),(256,0,183,0,8),(0,1,294,144,7),(0,4,147,288,7),(0,16,294,129,7),(0,32,145,262,7),(0,128,292,19,7),(0,256,147,36,7),(17,0,422,0,7),(32,0,407,0,7),(128,0,311,0,7),(260,0,179,0,7),(1,128,292,18,6),(4,32,145,258,6),(16,128,292,3,6),(32,4,147,256,6),(32,256,147,4,6),(36,0,147,0,5)]
def mo439A : List (List Nat) := [[],[130],[32,132,117],[32,64,128,117],[64],[64,130],[128,32,66,117],[128,66,117]]
def mo439D8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x140a92189ff50950
def mo439D9 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x8a07dd59240e30b209187105083000a2695c65651240e30b209187105083000adc61648b2091871040c001c7dc69640b2091871040c001e91e71a61630b209186103000869240c633003fd54ff153fd50ff503fd20
def mo439H9 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x100d
def mo439D10 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x72c8310403ff
def mo439H10 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1790000000000581f88000054200000000010c000000000000000000001900000000000000001402400284020000000000000000000000028f44c180000302003
def mo439L : Nat → Packing
  | 8 => (1,2,5,0,0,0,0,mo439D8)
  | 9 => (5,1,5,0,0,9,0,mo439D9)
  | 10 => (1,0,5,0,0,0,0,mo439D10)
  | _ => emptyPacking
def mo439I : Nat → Nat → Option (Nat × Nat)
  | 9 => lookupWord 1 5 0 5 0 1 mo439H9
  | 10 => lookupWord 3 53 1 10 3 3 mo439H10
  | _ => fun _ => none
def mo439 : Forest := ⟨1463,10,fun i => mo439Y[i]?.getD (0,0),mo439C,mo439A,mo439L,mo439I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo439P8_0 : block mo439 8 0 1=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo439B8 : block mo439 8 0 1=true := mo439P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo439P9_0 : block mo439 9 0 5=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo439B9 : block mo439 9 0 5=true := mo439P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo439P10_0 : block mo439 10 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo439B10 : block mo439 10 0 1=true := mo439P10_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo439T : checkedTables mo439 10 := by
  intro k hk
  interval_cases k
  · exact (rfl : block mo439 0 0 0 = true)
  · exact (rfl : block mo439 1 0 0 = true)
  · exact (rfl : block mo439 2 0 0 = true)
  · exact (rfl : block mo439 3 0 0 = true)
  · exact (rfl : block mo439 4 0 0 = true)
  · exact (rfl : block mo439 5 0 0 = true)
  · exact (rfl : block mo439 6 0 0 = true)
  · exact (rfl : block mo439 7 0 0 = true)
  · exact mo439B8
  · exact mo439B9
  · exact mo439B10
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo439G : graphValid mo439 (boundsBefore KM431) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowM439 : Lower false (varsX 439) (graphGoal 439) 11 := lower_forest (g:=mo439) (i:=0) (hints:=8590984532) (before_sound KM431 VM431) mo439G mo439T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KM439 := extendKnown KM431 11 [(439,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VM439 : Known false KM439 := extend_ok (m:=439) VM431 lowM439 (by decide +kernel)
def mo443Y : Array (Bits × Bits) := #[(0xfb84210659b662d4734a6b2e00000000ff00ff,0xa280010658a62254734a082425252525252525),(0xc6d6fda4d40344741308f3000000ff00ff00,0x30c454e4a0d40304740308c363636363636363),(0x0,0x0),(0x7fa4e40c50c05d7a71f140e00ff0000000000,0xc5aa4e40450005d7271f140e1f1f1f1f1f1f1f),(0xfd6d78c44a7280b8c0b7c6920000ff000000ff,0x16578c0005080a08095c6924a4a4a4a4a4a4a),(0x4032d9a74219cc519b90db9ff00000000ff00,0x403291854218cc1013805381c1c1c1c1c1c1c),(0x0,0x0),(0x48a926913c9e72a086ca54c0000ffffff0000,0x40a82090309440a0820210890909090909090),(0x2754927a84d3e2baf803a80ffff0000000000,0x2540027a84c322888802a80e0e0e0e0e0e0e0)]
def mo443C : List ColumnInfo := [(0,8,179,256,8),(8,0,435,0,8),(0,256,147,40,7),(1,0,442,0,7),(2,0,441,0,7),(16,0,427,0,7),(32,0,411,0,7),(256,0,179,0,7),(0,1,298,144,6),(0,16,298,129,6),(0,32,145,258,6),(8,32,145,258,6),(128,0,315,0,6),(1,16,298,128,5),(128,1,298,16,5),(128,16,298,1,5)]
def mo443A : List (List Nat) := [[],[64]]
def mo443D8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1eeda928398a31460039a8398a418a30016c4a0e620c51800b73588398a41c851800ec6894c00ff547fd50ff4c3fd10
def mo443D9 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x16eca864204ff
def mo443H9 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x14c00000000340000000b20244200000000000b00
def mo443L : Nat → Packing
  | 8 => (4,1,4,0,0,8,0,mo443D8)
  | 9 => (1,0,4,0,0,0,0,mo443D9)
  | _ => emptyPacking
def mo443I : Nat → Nat → Option (Nat × Nat)
  | 9 => lookupWord 1 23 0 7 2 1 mo443H9
  | _ => fun _ => none
def mo443 : Forest := ⟨1467,9,fun i => mo443Y[i]?.getD (0,0),mo443C,mo443A,mo443L,mo443I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo443P8_0 : block mo443 8 0 4=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo443B8 : block mo443 8 0 4=true := mo443P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo443P9_0 : block mo443 9 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo443B9 : block mo443 9 0 1=true := mo443P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo443T : checkedTables mo443 9 := by
  intro k hk
  interval_cases k
  · exact (rfl : block mo443 0 0 0 = true)
  · exact (rfl : block mo443 1 0 0 = true)
  · exact (rfl : block mo443 2 0 0 = true)
  · exact (rfl : block mo443 3 0 0 = true)
  · exact (rfl : block mo443 4 0 0 = true)
  · exact (rfl : block mo443 5 0 0 = true)
  · exact (rfl : block mo443 6 0 0 = true)
  · exact (rfl : block mo443 7 0 0 = true)
  · exact mo443B8
  · exact mo443B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo443G : graphValid mo443 (boundsBefore KM439) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowM443 : Lower false (varsX 443) (graphGoal 443) 10 := lower_forest (g:=mo443) (i:=0) (hints:=12885983316) (before_sound KM439 VM439) mo443G mo443T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KM443 := extendKnown KM439 10 [(443,[]),(475,[131,101])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VM443 : Known false KM443 := extend_ok (m:=443) VM439 lowM443 (by decide +kernel)
def mo445Y : Array (Bits × Bits) := #[(0x49e800b66d34ea78e120b70000000007fc01ff,0x94000b669042a78a100341148a45229148a45),(0x0,0x0),(0x93317741c440b27c1dd03980001ff00003fe00,0x3317340c440826c01d02184c26130984c2613),(0x47c55913624eef811b9907003fe00000000000,0x47c55913624aef001b98070fc7e3f1f8fc7e3f),(0x7e1ef0109d194ca00bea490000000ff80001ff,0x521ee0000419448008ea49229148a45229148a),(0x4cb2e9d08c2660a9c8edcffc000000003fe00,0x4c80c9d088264001c0adc0b0582c160b0582c),(0x0,0x0),(0x26a49264f0e39103765aa60000000ffffc0000,0x24a0124090e291035610824c26130984c26130),(0x995249ea129f15d7c015407ffffff000000000,0x9802002010151093c0050070381c0e070381c0)]
def mo445C : List ColumnInfo := [(8,0,437,0,9)]
def mo445A : List (List Nat) := [[],[116],[82],[82,116],[64],[64,112],[64,82],[64,82,112],[112,64],[112],[112,82,64],[112,82]]
def mo445D9 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xff
def mo445L : Nat → Packing
  | 9 => (1,0,1,0,0,0,0,mo445D9)
  | _ => emptyPacking
def mo445I (_ _ : Nat) : Option (Nat × Nat) := none
def mo445 : Forest := ⟨1469,9,fun i => mo445Y[i]?.getD (0,0),mo445C,mo445A,mo445L,mo445I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo445P9_0 : block mo445 9 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo445B9 : block mo445 9 0 1=true := mo445P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo445T : checkedTables mo445 9 := by
  intro k hk
  interval_cases k
  · exact (rfl : block mo445 0 0 0 = true)
  · exact (rfl : block mo445 1 0 0 = true)
  · exact (rfl : block mo445 2 0 0 = true)
  · exact (rfl : block mo445 3 0 0 = true)
  · exact (rfl : block mo445 4 0 0 = true)
  · exact (rfl : block mo445 5 0 0 = true)
  · exact (rfl : block mo445 6 0 0 = true)
  · exact (rfl : block mo445 7 0 0 = true)
  · exact (rfl : block mo445 8 0 0 = true)
  · exact mo445B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo445G : graphValid mo445 (boundsBefore KM443) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowM445 : Lower false (varsX 445) (graphGoal 445) 10 := lower_forest (g:=mo445) (i:=0) (hints:=8592065796) (before_sound KM443 VM443) mo445G mo445T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KM445 := extendKnown KM443 10 [(445,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VM445 : Known false KM445 := extend_ok (m:=445) VM443 lowM445 (by decide +kernel)
def mo477Y : Array (Bits × Bits) := #[(0xc92d04471d89356256fd2b9300000007fc01ff,0x12804470d81252204f8218108a45229148a45),(0x0,0x0),(0x12e66e6d332714a5618c74ca401ff000000000,0x80e66e6913261424618c64ca47e3f1f8fc7e3f),(0x878abb84460df3a0beac00bffe0000003fe00,0x860aa28442013320baa8002826130984c2613),(0xefc39f009292ab04a90f333640000ff80001ff,0xa43990090128a04210712165148a45229148a),(0x0,0x0),(0x209925c229772eb8f125594dc000000003fe00,0x209905c229572c88f005594d7d9ecf67b3d9ec),(0x24d4d25baa7a1057de90c86400000ffffc0000,0x2494421822681051da00c86026130984c26130),(0x132a493ced55e0c9b44396e03ffff000000000,0x13080114a851e0c994411220381c0e070381c0)]
def mo477C : List ColumnInfo := [(0,4,217,256,7),(0,64,405,8,7),(4,0,473,0,7),(64,0,413,0,7),(0,1,332,144,6),(0,8,145,320,6),(0,16,332,129,6),(0,128,332,17,6),(1,0,476,0,6),(4,8,145,320,6),(16,0,461,0,6),(64,256,145,12,6)]
def mo477A : List (List Nat) := [[],[116],[98,131],[98,131,116],[64],[64,112],[64,98,131],[64,98,131,112],[112,64],[112],[112,98,131,64],[112,98,131]]
def mo477D8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x17530eca8642067f
def mo477L : Nat → Packing
  | 8 => (1,0,4,0,0,0,0,mo477D8)
  | _ => emptyPacking
def mo477I (_ _ : Nat) : Option (Nat × Nat) := none
def mo477 : Forest := ⟨1501,8,fun i => mo477Y[i]?.getD (0,0),mo477C,mo477A,mo477L,mo477I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo477P8_0 : block mo477 8 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo477B8 : block mo477 8 0 1=true := mo477P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo477T : checkedTables mo477 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block mo477 0 0 0 = true)
  · exact (rfl : block mo477 1 0 0 = true)
  · exact (rfl : block mo477 2 0 0 = true)
  · exact (rfl : block mo477 3 0 0 = true)
  · exact (rfl : block mo477 4 0 0 = true)
  · exact (rfl : block mo477 5 0 0 = true)
  · exact (rfl : block mo477 6 0 0 = true)
  · exact (rfl : block mo477 7 0 0 = true)
  · exact mo477B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo477G : graphValid mo477 (boundsBefore KM445) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowM477 : Lower false (varsX 477) (graphGoal 477) 9 := lower_forest (g:=mo477) (i:=0) (hints:=8640292868) (before_sound KM445 VM445) mo477G mo477T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KM477 := extendKnown KM445 9 [(477,[]),(505,[82])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VM477 : Known false KM477 := extend_ok (m:=477) VM445 lowM477 (by decide +kernel)
def mo491Y : Array (Bits × Bits) := #[(0x59e4248e710e245f2d7a1b6000000ff000000,0x658e4248e1100245f2d7a03667676767676767),(0xf34177b121f60119f42260730000ff0000ffff,0x4140520121220118f402204121212121212121),(0x0,0x0),(0xfb0cc874a2901f4a71f140e00ff0000ff0000,0x8390cc8002280134870f14060b0b0b0b0b0b0b),(0x0,0x0),(0xfadea1c8341a9cb24837ce12ff0000000000ff,0xa96a188141888a00835cc121e1e1e1e1e1e1e),(0x8064b74c865b6ed18390d3900000000ffff00,0x8060174c845b6c108300938d4d4d4d4d4d4d4),(0x915349287c9ef0209eca5cc0000ffff000000,0x811249206c9ec020928058898989898989898),(0x4ea924f70cd3e0baf803a80ffff0000000000,0x468124760c5360b20802280e0e0e0e0e0e0e0)]
def mo491C : List ColumnInfo := [(0,1,362,128,8),(1,0,490,0,8),(8,0,483,0,7),(32,0,459,0,7),(64,0,427,0,7),(128,0,362,0,7),(128,1,362,0,7),(256,0,235,0,7),(0,8,163,320,6),(0,256,195,40,6),(2,0,489,0,6),(8,256,195,32,5),(32,256,195,8,5),(64,8,163,256,5)]
def mo491A : List (List Nat) := [[],[131,101]]
def mo491D7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x40702feba263f750d31
def mo491D8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x6b14941ec51c851800e5251629071800a5a907b1471800a6ad483d8a418a3001ac4a0f629051800b6ad07b148314600326cfe631fc8400ff50ffd62ff50bfd32ff4c7fd21
def mo491H8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x244f80
def mo491D9 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xeca8642047f
def mo491H9 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1100200000280000000065030000db00003a000000e90092a400
def mo491L : Nat → Packing
  | 7 => (2,2,4,0,0,4,0,mo491D7)
  | 8 => (6,1,4,0,0,9,0,mo491D8)
  | 9 => (1,0,4,0,0,0,0,mo491D9)
  | _ => emptyPacking
def mo491I : Nat → Nat → Option (Nat × Nat)
  | 8 => lookupWord 1 11 0 6 1 1 mo491H8
  | 9 => lookupWord 2 29 0 8 3 1 mo491H9
  | _ => fun _ => none
def mo491 : Forest := ⟨1515,9,fun i => mo491Y[i]?.getD (0,0),mo491C,mo491A,mo491L,mo491I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo491P7_0 : block mo491 7 0 2=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo491B7 : block mo491 7 0 2=true := mo491P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo491P8_0 : block mo491 8 0 6=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo491B8 : block mo491 8 0 6=true := mo491P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo491P9_0 : block mo491 9 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo491B9 : block mo491 9 0 1=true := mo491P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo491T : checkedTables mo491 9 := by
  intro k hk
  interval_cases k
  · exact (rfl : block mo491 0 0 0 = true)
  · exact (rfl : block mo491 1 0 0 = true)
  · exact (rfl : block mo491 2 0 0 = true)
  · exact (rfl : block mo491 3 0 0 = true)
  · exact (rfl : block mo491 4 0 0 = true)
  · exact (rfl : block mo491 5 0 0 = true)
  · exact (rfl : block mo491 6 0 0 = true)
  · exact mo491B7
  · exact mo491B8
  · exact mo491B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo491G : graphValid mo491 (boundsBefore KM477) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowM491 : Lower false (varsX 491) (graphGoal 491) 10 := lower_forest (g:=mo491) (i:=0) (hints:=12902752343) (before_sound KM477 VM477) mo491G mo491T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KM491 := extendKnown KM477 10 [(491,[]),(506,[64,32])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VM491 : Known false KM491 := extend_ok (m:=491) VM477 lowM491 (by decide +kernel)
def mo494Y : Array (Bits × Bits) := #[(0x0,0x0),(0xffbe2d6552da519822172148000007f01fc07f,0xa320c41000251982215200042850a142850a1),(0x219ae929cd02cd5c2576030003f800003f80,0x93000ae901c802cd5c256201162c58b162c58b),(0x508339d4022db3c4743ab501fc000fe00000,0x3c1083215402098304743a950e1c3870e1c387),(0x0,0x0),(0xffdae1033a21ca4909c8d7b0fe000000003fff,0x2048a1003a21880000c095b02850a142850a14),(0x44265e8bd6a26643e024ae0000000fffc000,0xc044201e8bd4a2644180042ab162c58b162c58),(0x48b9a4e4bcb285e17a4455000007f0000000,0x48b1a4e4bca205c16a4455bd7af5ebd7af5e),(0x2754920534ad14b58f8813fffff800000000,0x27541200142410a10a0002c183060c183060)]
def mo494C : List ColumnInfo := [(128,0,366,0,9),(0,128,364,2,8),(4,0,490,0,8),(8,0,486,0,8),(64,0,430,0,8),(2,0,364,0,7),(2,128,364,0,7),(32,0,462,0,7),(72,0,422,0,7),(256,0,238,0,7),(0,4,202,288,6),(0,8,166,320,6),(0,64,292,10,6),(128,64,292,10,6),(12,0,482,0,5),(32,4,202,256,5),(36,0,458,0,5),(66,0,300,0,5),(130,64,292,8,5),(256,4,202,32,5),(256,8,166,64,5),(260,0,234,0,5),(264,0,230,0,5),(6,128,360,0,4),(10,64,292,0,4),(34,128,332,0,4),(288,4,202,0,4)]
def mo494A : List (List Nat) := [[]]
def mo494D6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x2281dd5e0f2aaa2c6b0a636cd921cd63582dab2239ac6b063721d634c960
def mo494D7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x63c2098c1000a004019600b0c14205250d88307058f08282043e28201258c282061c1e007801031810a09070c501a2e0084e282c6c00b1b0024604c00f80186045018966656461162599978d8451989e361122a0b803a6a8ca1a809ca6c95a488ea1c839f87a9d4739b86a99c639805e96c539404a9143f8e8328bc2b8a01c84407800f3d6455163df5741c563f75541c563df5721c563df4715c163d7d545c463df9845c063fd48158d32d7d7654d32f5d6354d32f6d5358932f3d6455161e7d5458d61edd634c961d7d7655131f3d6455131f5d5458d31f755458531bed821cd60bf5811cd60edc7358d60ef48158d609fc874c960edd634c960bdc835c560edd634c560bed8218d40bf58118d40bf98018d40df4815d930ef96358130ef96358120d6d545c863d75545c463d79545c063ed56358531
def mo494H7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x6000038b7b
def mo494D8 (j : Nat) : Nat := if 2 ≤ j then 0 else (if j<1 then 0xa80214263858a1300722323228028c0f190c01488a8d004202a34012322c08048c1514012324c08042c2e34012323070048d810065478a8d0051f191028028f1c2c5460500730505c4068a00e54a0a880e00c4058a890052c4c502802971e2c507803284d152a4098e1c24204b359b2634580619254474d152a4098e1c24204e16284a80e1422307881600068a121c2840688160005141e3058a121d305c813183c40b000446a80f1a2a5488d1410259a1e343c68a952234506000346c9909a2a5c70e1200059a1f203a68a962424204b162a405080b00020a13910c1e0187c9909a2a5890f142428001a50589101d2601d4474d152a4098e1c24204c1f081601078d0e9a2a5890e1210258d93203a68a961a10250f1414203c000792a13454a902638709081309c205804343c6c94d152c487090a0006931e28487c030f162a4070a130002498f16284c80a121c2c000c343e4c80e9a2a5890e1210269a262c424840b0105078b111124205809284c78a13213c30780a343d6c60b806343058a8c10182c000a284c90f121c3602058a901e30405800125058a13223040580014505a911182c4c041416a4446888816024a13901a183c038f141e304070b0002498a1318203c0008262c509501e304c000a263c5290f182e02098f14a54478c8c1e028d13241a102c039a243c3420580718a44468b8d1e283000164878c121f363c58091e2c487cd9316020a0a13a03e6c98f01250789d01f263c58099c34d926af343990cbfe5bb2c294cc9fa4b923390c47f63d31ce8d2c5f22c3146895c4421eb0d384e41ce0950288033f91f84fa07bf3d71e82f18777bae1d02e5171437fdb9ed7c6a63391906c375dd2d9d60cab353028893e49914ad24011bc88b41fa020f5c78c3959becd6c65c2fd96f4af052c27e12c08e442d1f08e8c6bc3271710a904b021a0e7065c2c010d064022808a000ffae8b1ffd6458ffeb92c7ff5c163ffac6a1ffd6358bfeb1a65ff59161ffa86b0ffd62587fe992c3ff59131ffa8698ffd624c7fe99263ff5cd60ff8e6b07fd63583feb92c1ff58960ffa64b07fd71583feb0ac1ff4c560ffa42b07fd63503fe31a81ff58540ffa62a07fd764c3feb1a61ff5c930ffac4987fd324c3feb8a61ff58530ffa62987fd214c3feb1a41ff58520ffa62907fd62443fe99221df55163fe8e2b1f7d5418efeb90c77f5c463bfae031f7d6454fbeb1aa7df54d43efaa6b15fd764cbeeb1a65df54d32fdac49977d545877eb1ac3df54d61efaa6a0dfd764c7beaa263f758d31efaa698ff5614c6febb2437f5cd21efaa690fed62487f699243fd58521dfac6b05fd764c3fcb02617f5d920bfae6907ed32483f690a41fe58120bfaec885fd73442feb9221fd4c510fea42887f960443fc98221cf59154b7ae831ded7218efab88c77e5c063 else 0x11a20920447084440a240144088a0885218344209860d1088e1020ca8c141d08a4e1020ca8f162842030509462c204843202c507081048b0200c9090a8700a1e3054500549810068c1c00ca0b801a2c0803440a0064c8)
def mo494H8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xac00197a60c3621b84f69400a3e006904800c275300a82fc4b06ad94407a800040eca1c6006c062f2600001ee800006a56d0000030446c3288800973c0604842
def mo494D9 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x246984903cc2891871050007b46d03cc2c82461c414001ca1e69340f30b2091871040c002291a61240f30a2461c410300082c59240f30b2081c414001ca164903cc2c820710500073479a51340f30b209186140020d2479a51240f30a24618500083481a51340f30b209186140020d1e7144903cc2c820614001e91a4d038c2c82461c414001e69849038c28918710500073291a4d038c2c82461c4140020c2859240e30b2081c414001ed2691e6944d038c2c824618500091030a2471023d038c2c91c409172ab850493d111f538463cae12c1f833c4e06c06606c003fd64ff58ffc63ff50ffd62ff4cbfd61ff507fd31ff487fd60ff503fd30ff483fd10df5537d53
def mo494H9 (j : Nat) : Nat := if 2 ≤ j then 0 else (if j<1 then 0x1e5d69800000003a8aaa000000000d9000000000000000005280000000000000000000000000000000000000000000000000000d1000000000000000000000024e0000000000000000000000000000000000000000000000000000000008000000000000000000074e0016b800001d5400000756000000000000000000000000000000000000000000000000000000000000000000000000000006c000000000000000000000000000000000000000001638002ae00000000000000000000000000000000000000000000001b2c0000000000000534000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000113c0000019a0000000000000000000000000000000000000000000000000000000000000000016a3cfd350008900000063a00000612000001dc0000000000013e0000000000098a00000000498000001880000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000187800000000000000000000000000000000000000000001de8000000000000000161c0000099400000000000000000000000000000000146000000000000000000000000000000000359f13000002ac716000000000000000000072d00000000000000000000000000000000000088645800000000000000000000000000000000000000000000c6000000004320000000000000000000000000000000000000000000000000000000000000000000000028180000000000000000000000000014dc0000000000000000000003220000000000000000000000000001f00000000000000000000000000000d340000000000000000000000000003850000000029c0000000000090c003080000000000000000000000000000a80001360000000024900000000000b2a90c0000000000000000000000000000000000000000000000000f840004029400000000219000000000000a8000000000000006080000000000000000ac40000000000000000000000000000000000000000000000000000aa69d800e1800000000000000001a3c90000000000000000000000176c0000000000000000000000000000000080000000054800000000000000000001680000000000000000000000000000000000000000000000000000000000000000000000000000000000000a040013f7154b113000000001c6800001ae400591000000000000000000000000000157800000000000000000000000000055800000000000000000000000000083600000000000000000007120000058f00000000000000000000bc00000140000100800 else 0x6740000000000000000000000000a800088e000000000000)
def mo494D10 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x20c4188037f
def mo494H10 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x5bd45e133731494b0000000e770295e00041eb4014a24f221c008220
def mo494L : Nat → Packing
  | 6 => (4,4,5,0,0,5,0,mo494D6)
  | 7 => (36,3,5,0,0,10,0,mo494D7)
  | 8 => (92,2,5,0,0,13,0,mo494D8)
  | 9 => (17,1,5,0,0,11,0,mo494D9)
  | 10 => (1,0,5,0,0,0,0,mo494D10)
  | _ => emptyPacking
def mo494I : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 1 7 0 6 2 0 mo494H7
  | 8 => lookupWord 9 47 5 10 6 0 mo494H8
  | 9 => lookupWord 23 769 2 11 7 0 mo494H9
  | 10 => lookupWord 4 23 4 9 5 0 mo494H10
  | _ => fun _ => none
def mo494 : Forest := ⟨1518,10,fun i => mo494Y[i]?.getD (0,0),mo494C,mo494A,mo494L,mo494I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo494P6_0 : block mo494 6 0 4=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo494B6 : block mo494 6 0 4=true := mo494P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo494P7_0 : block mo494 7 0 4=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo494P7_4 : block mo494 7 4 32=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo494B7 : block mo494 7 0 36=true := (@block_merge mo494 7 0 4 32 mo494P7_0 mo494P7_4)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo494P8_0 : block mo494 8 0 5=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo494P8_5 : block mo494 8 5 44=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo494P8_49 : block mo494 8 49 43=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo494B8 : block mo494 8 0 92=true := (@block_merge mo494 8 0 5 87 mo494P8_0 (@block_merge mo494 8 5 44 43 mo494P8_5 mo494P8_49))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo494P9_0 : block mo494 9 0 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo494P9_2 : block mo494 9 2 15=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo494B9 : block mo494 9 0 17=true := (@block_merge mo494 9 0 2 15 mo494P9_0 mo494P9_2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo494P10_0 : block mo494 10 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo494B10 : block mo494 10 0 1=true := mo494P10_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo494T : checkedTables mo494 10 := by
  intro k hk
  interval_cases k
  · exact (rfl : block mo494 0 0 0 = true)
  · exact (rfl : block mo494 1 0 0 = true)
  · exact (rfl : block mo494 2 0 0 = true)
  · exact (rfl : block mo494 3 0 0 = true)
  · exact (rfl : block mo494 4 0 0 = true)
  · exact (rfl : block mo494 5 0 0 = true)
  · exact mo494B6
  · exact mo494B7
  · exact mo494B8
  · exact mo494B9
  · exact mo494B10
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo494G : graphValid mo494 (boundsBefore KM491) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowM494 : Lower false (varsX 494) (graphGoal 494) 11 := lower_forest (g:=mo494) (i:=0) (hints:=8876221776) (before_sound KM491 VM491) mo494G mo494T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KM494 := extendKnown KM491 11 [(494,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VM494 : Known false KM494 := extend_ok (m:=494) VM491 lowM494 (by decide +kernel)
def mo255Y : Array (Bits × Bits) := #[(0x9aec3a4b00c47d000000fff000000000000fff,0xac4120a00c47d055055055055055055055055),(0x301556a238b123000fff000000fff000fff000,0x100452a2100023003003003003003003003003),(0xd387f12cd41446000000000000000fff000000,0xd287702cd01046533533533533533533533533),(0xc8f8cc2b0e2f2000000000fff000000000000,0x48d8cc2b0e0f230f30f30f30f30f30f30f30f),(0xb4a69a9dd36908fff000000000000000000fff,0xb0228895d221000aa0aa0aa0aa0aa0aa0aa0aa),(0x6318858486ed5a000000000000000ffffff000,0x2118850006ed18accaccaccaccaccaccaccacc),(0xa02213d5f17b8000000000ffffff000000000,0xa02211d4f1708cf0cf0cf0cf0cf0cf0cf0cf0),(0x4496452671805fffffffff000000000000000,0x4092440251800f00f00f00f00f00f00f00f00),(0x0,0x0)]
def mo255C : List ColumnInfo := [(4,0,251,0,10)]
def mo255A : List (List Nat) := [[],[50,101],[64],[64,50,101]]
def mo255D10 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1ff
def mo255L : Nat → Packing
  | 10 => (1,0,1,0,0,0,0,mo255D10)
  | _ => emptyPacking
def mo255I (_ _ : Nat) : Option (Nat × Nat) := none
def mo255 : Forest := ⟨1279,10,fun i => mo255Y[i]?.getD (0,0),mo255C,mo255A,mo255L,mo255I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P10_0 : block mo255 10 0 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo255B10 : block mo255 10 0 1=true := mo255P10_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255T : checkedTables mo255 10 := by
  intro k hk
  interval_cases k
  · exact (rfl : block mo255 0 0 0 = true)
  · exact (rfl : block mo255 1 0 0 = true)
  · exact (rfl : block mo255 2 0 0 = true)
  · exact (rfl : block mo255 3 0 0 = true)
  · exact (rfl : block mo255 4 0 0 = true)
  · exact (rfl : block mo255 5 0 0 = true)
  · exact (rfl : block mo255 6 0 0 = true)
  · exact (rfl : block mo255 7 0 0 = true)
  · exact (rfl : block mo255 8 0 0 = true)
  · exact (rfl : block mo255 9 0 0 = true)
  · exact mo255B10
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255G : graphValid mo255 (boundsBefore KM494) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowM255 : Lower false (varsX 255) (graphGoal 255) 11 := lower_forest (g:=mo255) (i:=0) (hints:=17851732) (before_sound KM494 VM494) mo255G mo255T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KM255 := extendKnown KM494 11 [(255,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VM255 : Known false KM255 := extend_ok (m:=255) VM494 lowM255 (by decide +kernel)
def mo383Y : Array (Bits × Bits) := #[(0x9aa45e5b01c478000000000000000000000fff,0xa84565a00c478555555555555555555555555),(0x341d56a278a127000000000000fff000fff000,0x140d56a2700027303303303303303303303303),(0xd7c7f12c901447000000fff000000fff000000,0xd2c7302c900043033033033033033033033033),(0x88788c2b0e2f2000fff000fff000000000000,0x85888290e0f200f00f00f00f00f00f00f00f),(0xb4a69a9dd36908000000000000000000000fff,0xb4228885d32900aaaaaaaaaaaaaaaaaaaaaaaa),(0x6318858486ed5afff000000000000ffffff000,0x2110810002e5180cc0cc0cc0cc0cc0cc0cc0cc),(0xa02213d5f17b8000000000ffffff000000000,0xa02211d0f1708cf0cf0cf0cf0cf0cf0cf0cf0),(0x0,0x0),(0x4496452671805fffffffff000000000000000,0x4084450651804f00f00f00f00f00f00f00f00)]
def mo383C : List ColumnInfo := [(0,1,366,16,10)]
def mo383A : List (List Nat) := [[],[49,133],[64],[64,49,133]]
def mo383D10 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1ff
def mo383L : Nat → Packing
  | 10 => (1,0,1,0,0,0,0,mo383D10)
  | _ => emptyPacking
def mo383I (_ _ : Nat) : Option (Nat × Nat) := none
def mo383 : Forest := ⟨1407,10,fun i => mo383Y[i]?.getD (0,0),mo383C,mo383A,mo383L,mo383I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo383P10_0 : block mo383 10 0 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo383B10 : block mo383 10 0 1=true := mo383P10_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo383T : checkedTables mo383 10 := by
  intro k hk
  interval_cases k
  · exact (rfl : block mo383 0 0 0 = true)
  · exact (rfl : block mo383 1 0 0 = true)
  · exact (rfl : block mo383 2 0 0 = true)
  · exact (rfl : block mo383 3 0 0 = true)
  · exact (rfl : block mo383 4 0 0 = true)
  · exact (rfl : block mo383 5 0 0 = true)
  · exact (rfl : block mo383 6 0 0 = true)
  · exact (rfl : block mo383 7 0 0 = true)
  · exact (rfl : block mo383 8 0 0 = true)
  · exact (rfl : block mo383 9 0 0 = true)
  · exact mo383B10
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo383G : graphValid mo383 (boundsBefore KM255) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowM383 : Lower false (varsX 383) (graphGoal 383) 11 := lower_forest (g:=mo383) (i:=0) (hints:=8607786324) (before_sound KM255 VM255) mo383G mo383T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KM383 := extendKnown KM255 11 [(383,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VM383 : Known false KM383 := extend_ok (m:=383) VM255 lowM383 (by decide +kernel)
def mo447Y : Array (Bits × Bits) := #[(0x3235b692180dc9733800000000000ff80001ff,0x1214a692180c89713045229148a45229148a45),(0x8400cd670a5a673126000000001ff00003fe00,0x4008d030a4a432106c361b0d86c361b0d86c3),(0x162e0c0ff74c30498000007fc0000007fc0000,0x6220c06f54c204180130984c26130984c2613),(0xcc5939a6a0d702457c00ff8000000000000000,0xcc5939a6a0d700417c3f1f8fc7e3f1f8fc7e3f),(0x43fb9120a388c5c5440000003fe000000001ff,0x1eb1120a2804404448a45229148a45229148a),(0xf8d81b7894b5041833ff000000000007fffe00,0xf8d8107800910418302c160b0582c160b0582c),(0x0,0x0),(0xed02641c098128a2d80000003ffffff8000000,0xe800400c010120828930984c26130984c26130),(0x9c402836a62930685ffffffc0000000000000,0x10402010a20930601c0e070381c0e070381c0)]
def mo447C : List ColumnInfo := [(8,0,439,0,11)]
def mo447A : List (List Nat) := [[],[64]]
def mo447D11 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1ff
def mo447L : Nat → Packing
  | 11 => (1,0,1,0,0,0,0,mo447D11)
  | _ => emptyPacking
def mo447I (_ _ : Nat) : Option (Nat × Nat) := none
def mo447 : Forest := ⟨1471,11,fun i => mo447Y[i]?.getD (0,0),mo447C,mo447A,mo447L,mo447I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo447P11_0 : block mo447 11 0 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo447B11 : block mo447 11 0 1=true := mo447P11_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo447T : checkedTables mo447 11 := by
  intro k hk
  interval_cases k
  · exact (rfl : block mo447 0 0 0 = true)
  · exact (rfl : block mo447 1 0 0 = true)
  · exact (rfl : block mo447 2 0 0 = true)
  · exact (rfl : block mo447 3 0 0 = true)
  · exact (rfl : block mo447 4 0 0 = true)
  · exact (rfl : block mo447 5 0 0 = true)
  · exact (rfl : block mo447 6 0 0 = true)
  · exact (rfl : block mo447 7 0 0 = true)
  · exact (rfl : block mo447 8 0 0 = true)
  · exact (rfl : block mo447 9 0 0 = true)
  · exact (rfl : block mo447 10 0 0 = true)
  · exact mo447B11
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo447G : graphValid mo447 (boundsBefore KM383) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowM447 : Lower false (varsX 447) (graphGoal 447) 12 := lower_forest (g:=mo447) (i:=0) (hints:=8591017300) (before_sound KM383 VM383) mo447G mo447T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KM447 := extendKnown KM383 12 [(447,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VM447 : Known false KM447 := extend_ok (m:=447) VM383 lowM447 (by decide +kernel)
def mo479Y : Array (Bits × Bits) := #[(0x10672d0e84068c4500000000000ffe000007ff,0x43210c8006844528a514a294528a514a2945),(0xb25ed1bca8565003000000007ff000003ff800,0x105611aca016000318630c618c318630c618c3),(0x48f6f3856e70104c001ffc0000000000000000,0x48f6f3856e70104807e0fc1f83f07e0fc1f83f),(0x90127a333d56270ffe00000000001ffc00000,0x90127a32154406002604c0981302604c09813),(0x5dac29e78229138b000003ff800000000007ff,0x59ac08a302091302514a294528a514a294528a),(0x0,0x0),(0x67d8c029173d915600000000000001fffff800,0x6688c00016299114e59cb39672ce59cb39672c),(0x868286d00deacd98000003fffffffe00000000,0x860086500de048988610c2184308610c218430),(0x5e011218708826a7fffffc0000000000000000,0x1600001810882687f81f03e07c0f81f03e07c0)]
def mo479C : List ColumnInfo := [(4,0,475,0,10)]
def mo479A : List (List Nat) := [[],[64]]
def mo479D10 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1ff
def mo479L : Nat → Packing
  | 10 => (1,0,1,0,0,0,0,mo479D10)
  | _ => emptyPacking
def mo479I (_ _ : Nat) : Option (Nat × Nat) := none
def mo479 : Forest := ⟨1503,10,fun i => mo479Y[i]?.getD (0,0),mo479C,mo479A,mo479L,mo479I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo479P10_0 : block mo479 10 0 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo479B10 : block mo479 10 0 1=true := mo479P10_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo479T : checkedTables mo479 10 := by
  intro k hk
  interval_cases k
  · exact (rfl : block mo479 0 0 0 = true)
  · exact (rfl : block mo479 1 0 0 = true)
  · exact (rfl : block mo479 2 0 0 = true)
  · exact (rfl : block mo479 3 0 0 = true)
  · exact (rfl : block mo479 4 0 0 = true)
  · exact (rfl : block mo479 5 0 0 = true)
  · exact (rfl : block mo479 6 0 0 = true)
  · exact (rfl : block mo479 7 0 0 = true)
  · exact (rfl : block mo479 8 0 0 = true)
  · exact (rfl : block mo479 9 0 0 = true)
  · exact mo479B10
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo479G : graphValid mo479 (boundsBefore KM447) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowM479 : Lower false (varsX 479) (graphGoal 479) 11 := lower_forest (g:=mo479) (i:=0) (hints:=8606738532) (before_sound KM447 VM447) mo479G mo479T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KM479 := extendKnown KM447 11 [(479,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VM479 : Known false KM479 := extend_ok (m:=479) VM447 lowM479 (by decide +kernel)
def mo495Y : Array (Bits × Bits) := #[(0x3f3a834c60da9000000000007ff00000000000,0x3d0a834c60da930f61ec3d87b0f61ec3d87b0f),(0x4900b62d3d2a9000000003ff800001ffc007ff,0x4800a005350a91012024048090120240480901),(0x948a4b6286efa000001ffc00000000003ff800,0x808a4b2286ed80550aa1542a8550aa1542a855),(0xa6c540a745ccd800ffe00000000ffe00000000,0x860040a305cc98330660cc198330660cc19833),(0x0,0x0),(0x142409981084bfff00000000000000003fffff,0x14240088000028aa1542a8550aa1542a8550aa),(0xf99cb6c20909480000000000000fffffc00000,0x319c1640080146ccd99b33666ccd99b33666cc),(0x2f84832ac312800000003fffff00000000000,0x2f0483288212cf09e13c2784f09e13c2784f0),(0x69435055d24307fffffffc0000000000000000,0x6941105450020700e01c0380700e01c0380700)]
def mo495C : List ColumnInfo := [(1,0,494,0,11)]
def mo495A : List (List Nat) := [[]]
def mo495D11 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1ff
def mo495L : Nat → Packing
  | 11 => (1,0,1,0,0,0,0,mo495D11)
  | _ => emptyPacking
def mo495I (_ _ : Nat) : Option (Nat × Nat) := none
def mo495 : Forest := ⟨1519,11,fun i => mo495Y[i]?.getD (0,0),mo495C,mo495A,mo495L,mo495I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo495P11_0 : block mo495 11 0 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo495B11 : block mo495 11 0 1=true := mo495P11_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo495T : checkedTables mo495 11 := by
  intro k hk
  interval_cases k
  · exact (rfl : block mo495 0 0 0 = true)
  · exact (rfl : block mo495 1 0 0 = true)
  · exact (rfl : block mo495 2 0 0 = true)
  · exact (rfl : block mo495 3 0 0 = true)
  · exact (rfl : block mo495 4 0 0 = true)
  · exact (rfl : block mo495 5 0 0 = true)
  · exact (rfl : block mo495 6 0 0 = true)
  · exact (rfl : block mo495 7 0 0 = true)
  · exact (rfl : block mo495 8 0 0 = true)
  · exact (rfl : block mo495 9 0 0 = true)
  · exact (rfl : block mo495 10 0 0 = true)
  · exact mo495B11
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo495G : graphValid mo495 (boundsBefore KM479) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowM495 : Lower false (varsX 495) (graphGoal 495) 12 := lower_forest (g:=mo495) (i:=0) (hints:=8607786327) (before_sound KM479 VM479) mo495G mo495T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KM495 := extendKnown KM479 12 [(495,[]),(510,[64])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VM495 : Known false KM495 := extend_ok (m:=495) VM479 lowM495 (by decide +kernel)
def mo503Y : Array (Bits × Bits) := #[(0x29c60154c0000000000001fff0000000001fff,0x29c00050851528a9454a2a51528a9454a2a515),(0xc1cd5283a0000000003ffe000fff8003ffe000,0xc18d4202a3031818c0c6063031818c0c606303),(0x28d3cc32a000fff80000000000007ffc000000,0x28d2cc12a04f027813c09e04f027813c09e04f),(0x0,0x0),(0xd48cc1c040000007ffc0000000000000001fff,0xc40cc1804a2a51528a9454a2a51528a9454a2a),(0x5638ad993fff00000000000000007fffffe000,0x1620018900b005802c01600b005802c01600b0),(0x2350d04740000000000000000fff8000000000,0x225090455cfce7e73f39f9cfce7e73f39f9cfc),(0x90120a2d80000007fffffffff0000000000000,0x1012082d10c086043021810c086043021810c0),(0xae2930685ffffff80000000000000000000000,0x800930605f00f807c03e01f00f807c03e01f00)]
def mo503C : List ColumnInfo := [(64,0,439,0,11),(0,64,437,2,10),(1,0,502,0,10),(4,0,499,0,10),(16,0,487,0,10),(256,0,247,0,10),(0,1,358,144,9),(0,4,211,288,9),(0,16,358,129,9),(0,256,211,36,9),(2,0,437,0,9),(2,64,437,0,9),(32,0,471,0,9),(128,0,375,0,9),(1,16,358,128,8),(4,256,211,32,8),(17,0,486,0,8),(32,4,211,256,8),(32,256,211,4,8),(128,1,358,16,8),(128,16,358,1,8),(260,0,243,0,8),(36,0,211,0,7),(64,32,145,262,7),(64,128,292,19,7),(129,0,358,0,7),(129,16,358,0,7),(34,64,405,0,6)]
def mo503A : List (List Nat) := [[],[130],[32,132,117],[32,64,128,117],[64],[64,130],[128,32,66,117],[128,66,117]]
def mo503D9 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x6a69e968e61572f271f150177749161564
def mo503D10 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x16a6c57ce1a3252a4f183454b11223070816080817b4669b2633868c56294a84f183454b1124347081608081aa6c484d5b3164a54a64278c192858811183840b04040cd362417cd5a3252a909e3068a96204460e102c1010314d931a0426ad18ac529909e3068a96204868e102c101034569ce9ab662c96294a78c192858891183840b04040c16a6be74d5a3258a4f183454b11223070816080817a94e95198ac5aacb931e242694264888d18ad50a1220386ca17204c60f102c001768cc911192e52a52a13a6ca97224c68f122830002ed19d2a3325ca1220386ca17204c60f102c001568cc9115b2e50a911b2e4c7890e0429b2633960c5729546cb17244c70e121029d3244674d18ae52a8d962e4898e1c242800294d9319ab062b94aa446cb1626387090814e259f69c959dd6ed435199014d78adc8786a047422c003ff50960ffd41583ff5c930ffd424c3ff50530ffd72443ff50910f7d85592ff60464f7d64552ff61941fbd64507df55160f7d54503df55130
def mo503H10 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xe0
def mo503D11 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xc2ea2692265651240e34a2c82461c4103000c289a489a65651240e34a2c82461c4103000bb6ba489a61651240e34a2c82461c414002c99c69959434a2c824618500082e9a489c69959434a2c82461850009a669959440d28a2461850007a689e71a65650e34a2c820614002499c69859434a2c82461850008248985952c91c4095b95c52c3e4bd23454084007fd64ff8c9ff507feb07fd40ffa61ff483fe8877d54
def mo503H11 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x28e606e300039800000000000001e08558003820018d8000000000000003c001e68000000000000060bc1cd2800000000000005d200111800f850a400701001fa0000000004a00070a000003440009120000000081ba1305d860000000000050028098
def mo503D12 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x594831006ff
def mo503H12 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x3a2200b10f928200094140a72dc190e00093006001f17c9161001f4ad93a520a00300e0354749350800b30230
def mo503L : Nat → Packing
  | 9 => (1,3,5,0,0,0,0,mo503D9)
  | 10 => (15,2,5,0,0,12,0,mo503D10)
  | 11 => (9,1,5,0,0,10,0,mo503D11)
  | 12 => (1,0,5,0,0,0,0,mo503D12)
  | _ => emptyPacking
def mo503I : Nat → Nat → Option (Nat × Nat)
  | 10 => lookupWord 1 2 0 4 0 0 mo503H10
  | 11 => lookupWord 7 71 3 11 4 3 mo503H11
  | 12 => lookupWord 6 31 4 11 4 3 mo503H12
  | _ => fun _ => none
def mo503 : Forest := ⟨1527,12,fun i => mo503Y[i]?.getD (0,0),mo503C,mo503A,mo503L,mo503I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo503P9_0 : block mo503 9 0 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo503B9 : block mo503 9 0 1=true := mo503P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo503P10_0 : block mo503 10 0 8=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo503P10_8 : block mo503 10 8 7=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo503B10 : block mo503 10 0 15=true := (@block_merge mo503 10 0 8 7 mo503P10_0 mo503P10_8)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo503P11_0 : block mo503 11 0 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo503P11_1 : block mo503 11 1 8=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo503B11 : block mo503 11 0 9=true := (@block_merge mo503 11 0 1 8 mo503P11_0 mo503P11_1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo503P12_0 : block mo503 12 0 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo503B12 : block mo503 12 0 1=true := mo503P12_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo503T : checkedTables mo503 12 := by
  intro k hk
  interval_cases k
  · exact (rfl : block mo503 0 0 0 = true)
  · exact (rfl : block mo503 1 0 0 = true)
  · exact (rfl : block mo503 2 0 0 = true)
  · exact (rfl : block mo503 3 0 0 = true)
  · exact (rfl : block mo503 4 0 0 = true)
  · exact (rfl : block mo503 5 0 0 = true)
  · exact (rfl : block mo503 6 0 0 = true)
  · exact (rfl : block mo503 7 0 0 = true)
  · exact (rfl : block mo503 8 0 0 = true)
  · exact mo503B9
  · exact mo503B10
  · exact mo503B11
  · exact mo503B12
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo503G : graphValid mo503 (boundsBefore KM495) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowM503 : Lower false (varsX 503) (graphGoal 503) 13 := lower_forest (g:=mo503) (i:=0) (hints:=8607761748) (before_sound KM495 VM495) mo503G mo503T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KM503 := extendKnown KM495 13 [(503,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VM503 : Known false KM503 := extend_ok (m:=503) VM495 lowM503 (by decide +kernel)
def mo507Y : Array (Bits × Bits) := #[(0x698608d0e0000000000001fff0000000001fff,0x69800850e51528a9454a2a51528a9454a2a515),(0xa1c5171180000000003ffe0000007fffffe000,0x80c5161083031818c0c6063031818c0c606303),(0x0,0x0),(0x4cd3ccf68000fff8000000000fff8000000000,0x4cd28c94804f027813c09e04f027813c09e04f),(0xd08cd18460000007ffc0000000000000001fff,0x900cd1840a2a51528a9454a2a51528a9454a2a),(0x5638bd9d3fff00000000000000000003ffe000,0x5638898d20fc07e03f01f80fc07e03f01f80fc),(0x2350c04340000000000000000ffffffc000000,0x230040435cb0e5872c3961cb0e5872c3961cb0),(0x90120a2d80000007fffffffff0000000000000,0x12002910c086043021810c086043021810c0),(0xae2930685ffffff80000000000000000000000,0xa00130605f00f807c03e01f00f807c03e01f00)]
def mo507C : List ColumnInfo := [(1,0,506,0,10),(8,0,499,0,10),(16,0,491,0,10),(32,0,475,0,10),(64,0,443,0,10),(256,0,251,0,10),(0,1,362,144,9),(0,8,179,320,9),(0,16,362,129,9),(0,256,211,40,9),(2,0,505,0,9),(128,0,379,0,9),(0,32,217,258,8),(0,64,433,10,8),(1,16,362,128,8),(8,256,211,32,8),(16,1,362,128,8),(17,0,490,0,8),(32,256,211,8,8),(64,8,179,256,8),(72,0,435,0,8),(128,1,362,16,8),(128,16,362,1,8),(256,8,179,64,8),(264,0,243,0,8),(2,32,217,256,7),(2,64,433,8,7),(34,0,473,0,7),(40,0,211,0,7),(40,256,211,0,7),(96,0,411,0,7),(129,0,362,0,7),(34,8,145,320,6),(72,32,145,258,6),(98,0,409,0,6),(288,64,145,10,6),(74,32,145,256,5),(290,64,145,8,5)]
def mo507A : List (List Nat) := [[],[131,101],[64],[64,131,101]]
def mo507D9 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x3e06c10644c10411036003226002a2e4c00bfecaa82b07ef55141582ffb2aa0a61fbd5450530
def mo507D10 (j : Nat) : Nat := if 2 ≤ j then 0 else (if j<1 then 0x810104b4aa9a7a3a362a2e22261a1e12120e02024b0312d2aa6a4161493108e0f0c8c8a0b08890687048482030080d100b0aa9a78544c423c32342a2c22241a1c1212080c0202e412d2aa8289e161513108e0f0c8d0a8a88090687048482030080d2e8e0ccb4aa9a7858544c42383c32342a2c2222181c1212080c020363432acab2417129310910e8f0c8d0a8b08890607048502830080d0cab2ac9c785a4a443c32342a2c22241a1c1214080c0202e3d2aa6a51c17149492908f0c0d0a8a8808860704858302830000d0c4705c52524a3c3032282c22241a1c1212080c0002a289f1c1714948f0c0d0a8a88090687048482030000a8e4aa9a7c705c52523c30342a2c2222181c1212080c0002e372aa51c161492908f0c0d0a8b08888607048502830000b8fa9a7c7058523c30342a2c22241a1c1212080c0002b2aa6a522231697149493108f0c0d0a8a8808860704058302830000d88c5a5c52524c423c3032282c22241a1c1012080c0002c229f16971495108f0c0d0a8a88090687040482030000b4aa988a7c5a5c5254423c30342a2c2222181c1012080c000312aa5222316961493108f0c0d0a8b08888607040502830000c2988a7c5a5854423c30342a2c22241a1c1012080c0002c3c332aa6a51d16961492908f0c0d0a8a8808860704858302830000d8c4ac745a58524a3c3032282c22241a1c1212080c0002d2a289f1d1696148f0c0d0a8a88090687048482030000b0e4aa9a7c745a58523c30342a2c2222181c1212080c0002e332aa51d169692908f0d0a8b08888607048502830000b4aa9a7c745a5a3c342a2c22261c1a1c1212080c0002a32acab27241a18961412100e0d8a0b0907840582038000b8cab2ac9c78625a524c3c362c2e2614080e0244840322c2aa49915138b88860785838080d0b0aa9060585048403836282e2022181e1016080e0002e424032acab24191412100e0d8a0b880907840582038000b8ca9c90605c5048403836282a241e1016080e00028424032acaa241896171415110f0d8b0b89858380a0ca989064543e2c2a2026160e01a40342c2a1816158b8985838060b8b0a89858503e2e261e160184034322016140d8b89878582672637a5b24d0764230e579cb6f5822a554549cb4b024251648533fa1e74e5c6d333c1854b6455727412348643d31bc0c8458427711a07542ec12306802640cc0330003ff59564ffd6458bff61161ffd64587ff55161ffd82587ff5c961ffd62587ff54961ffd42587ff58541ffd61487ff55160ffd72583ff54960ffd42583ff50560ffd21583ff55130ffd724c3ff54930ffd424c3ff50530ffd214c3ff55110ffd72443ff54910ffd42443ff50510ffd21442ff61954fbd6450bbf59161bfd84186ff61941bfd85507ef59141fbd54506ef61061bed82186fe60061 else 0x4846422c2aa7251495129310910e8f0c8d0a8a09060704858302830080e900b0ac9c7c52524a443c32342a2c2222181c1214080c020304840332d2aa492908e8d8a8b888887848582838080a9211900c8b0aa9450544a4c42443a3c32362c2a2e242222181e1412160c0a0e0402044443c332d2aa6a498181615129310910e8f0c8d0a8a880886070485830283)
def mo507H10 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x100a3001a740016a21b008
def mo507D11 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x12213258a92182c509101c3450b10203840a081800183c64992182c509101c3450a101c205040c000aa0264858a121c305881218384080c0009202c5498f16283868a16204860e10203000288501a1e2c5070d14284860e10203000246498f16283868a162040708101800112c54509101c3450b102430708141030002680d192c5458a12203868a16204860e10282060005d2a2406c90c16284880e1a28588101c205040c000ba4404c78b141c3450b102430708101800132a3858a0d142c4090c1c20504080412212a4870b141a28588101c2050408048a8b14203450b10243060a081007a02a4c78e16283868a16204860e102020132a3858a0d142c4090c1c2050408043bf6e5cc373ea5cce886e717aa6a3e85c080876001ff593feaa7fd72ffac5ff54bfea17fd61ff8c3ff507fe90ffd60ffa81ff4c3fe907fd10
def mo507H11 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x80b000911e2089b00051e91b000301000108228e9c423000f1c000000000000000000000000000858000000a66000000000c0ad0d00060744b78ee13000e8cd5f551000000000000000a80000000443f0f000000000000015865510000d5a00000021d616000000000804000000000000000e4cc00000000f52000603000000341000a6300000000000000060694200026171f227598b8be9ae5d000000f1a00034e618000125454000000000000922000000000000000000000000f2400000000000000000008d000b4685e000000000000000821000f02e5900000000000028f00050e000c0c000614547d12000000000297890000a09000000317000000948d60000000000000000000d0500000000000000000000000000044d000000000000000553000799000000819000000000000f57626000000000000000313081a91200040
def mo507D12 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x5103081006ff
def mo507H12 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x240e440000000120000038606cc10014b113d30029990f4a38d640021a00333585a09324d00000e0a9e4c70ed2487357c5000160282312
def mo507L : Nat → Packing
  | 9 => (4,3,6,0,0,7,0,mo507D9)
  | 10 => (41,2,6,0,0,13,0,mo507D10)
  | 11 => (15,1,6,0,0,11,0,mo507D11)
  | 12 => (1,0,6,0,0,0,0,mo507D12)
  | _ => emptyPacking
def mo507I : Nat → Nat → Option (Nat × Nat)
  | 10 => lookupWord 2 11 2 8 2 2 mo507H10
  | 11 => lookupWord 20 211 3 12 6 2 mo507H11
  | 12 => lookupWord 7 41 4 10 4 2 mo507H12
  | _ => fun _ => none
def mo507 : Forest := ⟨1531,12,fun i => mo507Y[i]?.getD (0,0),mo507C,mo507A,mo507L,mo507I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo507P9_0 : block mo507 9 0 4=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo507B9 : block mo507 9 0 4=true := mo507P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo507P10_0 : block mo507 10 0 3=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo507P10_3 : block mo507 10 3 8=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo507P10_11 : block mo507 10 11 30=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo507B10 : block mo507 10 0 41=true := (@block_merge mo507 10 0 3 38 mo507P10_0 (@block_merge mo507 10 3 8 30 mo507P10_3 mo507P10_11))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo507P11_0 : block mo507 11 0 15=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo507B11 : block mo507 11 0 15=true := mo507P11_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo507P12_0 : block mo507 12 0 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo507B12 : block mo507 12 0 1=true := mo507P12_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo507T : checkedTables mo507 12 := by
  intro k hk
  interval_cases k
  · exact (rfl : block mo507 0 0 0 = true)
  · exact (rfl : block mo507 1 0 0 = true)
  · exact (rfl : block mo507 2 0 0 = true)
  · exact (rfl : block mo507 3 0 0 = true)
  · exact (rfl : block mo507 4 0 0 = true)
  · exact (rfl : block mo507 5 0 0 = true)
  · exact (rfl : block mo507 6 0 0 = true)
  · exact (rfl : block mo507 7 0 0 = true)
  · exact (rfl : block mo507 8 0 0 = true)
  · exact mo507B9
  · exact mo507B10
  · exact mo507B11
  · exact mo507B12
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo507G : graphValid mo507 (boundsBefore KM503) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowM507 : Lower false (varsX 507) (graphGoal 507) 13 := lower_forest (g:=mo507) (i:=0) (hints:=12902752340) (before_sound KM503 VM503) mo507G mo507T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KM507 := extendKnown KM503 13 [(507,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VM507 : Known false KM507 := extend_ok (m:=507) VM503 lowM507 (by decide +kernel)
def mo509Y : Array (Bits × Bits) := #[(0x8b321059000000000000000fffe00000007fff,0x8b32105120aa415482a905520aa415482a9055),(0x0,0x0),(0xf41c1f0000000003fff800000000003fff8000,0xf01c07000a6614cc29985330a6614cc2998533),(0x28e505800001fffc00000000001fffc0000000,0x28a00100061e0c3c187830f061e0c3c187830f),(0xc290ea60000000000007fff000000000007fff,0x4080ca20415482a905520aa415482a905520aa),(0x7a1f82ffffe0000000000000000003fff8000,0x6a1782d15982b305660acc15982b305660acc),(0x475d3df70000000000000000001fffc0000000,0x475d3cf7f9e1f3c3e787cf0f9e1f3c3e787cf0),(0x5c2a25bc000000000007ffffffe00000000000,0x1408258c9e013c027804f009e013c027804f00),(0x31c8c207fffffffffff8000000000000000000,0x1408002e001c0038007000e001c0038007000)]
def mo509C : List ColumnInfo := [(0,64,437,8,10),(64,0,445,0,10),(0,1,364,144,9),(0,16,364,129,9),(0,128,364,17,9),(1,0,508,0,9),(4,0,505,0,9),(8,0,437,0,9),(8,64,437,0,9),(16,0,493,0,9),(32,0,477,0,9),(128,0,381,0,9),(0,4,217,288,8),(0,32,217,260,8),(256,0,253,0,8),(0,256,145,44,7),(4,32,217,256,7)]
def mo509A : List (List Nat) := [[],[116],[82],[82,116],[64],[64,112],[64,82],[64,82,112],[112,64],[112],[112,82,64],[112,82]]
def mo509D10 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x40f32b2ea2a92689c71a51641230e20a180060e34cacb2a92689c71a51641230e20a18005e4003feb8ffd41
def mo509D11 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x16a4a0e629062080cff
def mo509H11 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xcb04048
def mo509L : Nat → Packing
  | 10 => (2,1,5,0,0,8,0,mo509D10)
  | 11 => (1,0,5,0,0,0,0,mo509D11)
  | _ => emptyPacking
def mo509I : Nat → Nat → Option (Nat × Nat)
  | 11 => lookupWord 1 5 0 7 1 2 mo509H11
  | _ => fun _ => none
def mo509 : Forest := ⟨1533,11,fun i => mo509Y[i]?.getD (0,0),mo509C,mo509A,mo509L,mo509I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo509P10_0 : block mo509 10 0 2=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo509B10 : block mo509 10 0 2=true := mo509P10_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo509P11_0 : block mo509 11 0 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo509B11 : block mo509 11 0 1=true := mo509P11_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo509T : checkedTables mo509 11 := by
  intro k hk
  interval_cases k
  · exact (rfl : block mo509 0 0 0 = true)
  · exact (rfl : block mo509 1 0 0 = true)
  · exact (rfl : block mo509 2 0 0 = true)
  · exact (rfl : block mo509 3 0 0 = true)
  · exact (rfl : block mo509 4 0 0 = true)
  · exact (rfl : block mo509 5 0 0 = true)
  · exact (rfl : block mo509 6 0 0 = true)
  · exact (rfl : block mo509 7 0 0 = true)
  · exact (rfl : block mo509 8 0 0 = true)
  · exact (rfl : block mo509 9 0 0 = true)
  · exact mo509B10
  · exact mo509B11
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo509G : graphValid mo509 (boundsBefore KM507) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowM509 : Lower false (varsX 509) (graphGoal 509) 12 := lower_forest (g:=mo509) (i:=0) (hints:=8642389252) (before_sound KM507 VM507) mo509G mo509T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KM509 := extendKnown KM507 12 [(509,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VM509 : Known false KM509 := extend_ok (m:=509) VM507 lowM509 (by decide +kernel)
def mo511Y : Array (Bits × Bits) := #[(0x3fffe00000000000000001ffff,0x5055282a94154a0aa5055282a94154a0aa5055),(0x7fffc00000000ffff80003fffe0000,0x300318018c00c6006300318018c00c60063003),(0xffff0000000000000000000007fffc00000000,0x5330299814cc0a6605330299814cc0a660533),(0x1ffff00000000000000000,0x30f018780c3c061e030f018780c3c061e030f),(0xffff80000000000000000000000001ffff,0xa0aa5055282a94154a0aa5055282a94154a0aa),(0x7fffffffe0000,0xacc056602b3015980acc056602b3015980acc),(0x1ffffffff8000000000000,0xccf0e678733c399e1ccf0e678733c399e1ccf0),(0xffffffffffffe000000000000000000000,0xf00878043c021e010f00878043c021e010f00),(0xffff0000000000000000000000000000000000,0xf000f8007c003e001f000f8007c003e001f000)]
def mo511C : List ColumnInfo := [(4,0,507,0,13),(8,0,503,0,13),(1,0,510,0,12),(2,0,509,0,12),(16,0,495,0,12),(64,0,447,0,12),(0,1,366,144,11),(0,16,366,129,11),(0,64,437,10,11),(17,0,494,0,11),(32,0,479,0,11),(128,0,383,0,11),(256,0,255,0,11),(0,4,219,288,10),(0,8,183,320,10),(0,128,364,19,10),(0,256,211,44,10),(1,16,366,128,10),(2,64,437,8,10),(16,1,366,128,10),(36,0,475,0,10),(66,0,445,0,10),(128,1,366,16,10),(128,16,366,1,10),(260,0,251,0,10),(264,0,247,0,10),(1,128,364,18,9),(2,128,364,17,9),(3,0,508,0,9),(10,0,437,0,9),(10,64,437,0,9),(32,4,219,256,9),(32,256,211,12,9),(34,0,477,0,9),(64,8,183,256,9),(65,0,446,0,9),(129,0,366,0,9),(129,16,366,0,9),(130,0,381,0,9),(132,0,379,0,9),(256,8,183,64,9),(3,128,364,16,8),(18,128,364,1,8),(288,4,219,0,8),(320,8,183,0,8)]
def mo511A : List (List Nat) := [[],[64]]
def mo511D7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x6543e061706fe06154756a015476a2a1344a6a01344815895543e07dc010e3bc1bd6beb5b2a1fc0de00fc6038ef06c338e8877437ed7f6b654359fecbfe27c0ff85fc0ee01ab1df6bfb5aaa0248fe0770079ae4b8ae0b7add86793d44061002c654e9719c52e97560531b1b13a5c6708ba5d5814c70e55e5770ba2597560531c3b1789dc2e8965d5814c70e55dc754ba2597560531c3b1771d22e8965d5814c74a55ed2e8966157560531a1953a5c6714ba5d5814c686c4e9719c22e97560531b0953a5d62e9855d5814c64a55ed2e8966157560531
def mo511D8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x3543e042d509cb0a543c0c2c1bf030a86d44bc0c3d1d350f030f477c0c22d024adc5f83303f81fc0ec023180c7407706fb5fb5b54333fb2fb2bf13c0ff0bf00e71d712950fc0bc017181c7706dc484a6051da1bed7ed6515b50048fc025c78879c77b5fb59c4a542b3fb2ff13c0ff0bf03700eb1d21ded7ed6550bc5f03fc0dc027eaf33aee4366cf31eae20a72192480720033cabaae594e4b30298e7b1749cb29c9660531e72ae338a5d2eac0a63cec5c6708ba5d5814c71dabb85d12cbab0298f395754ba2597560531e762e91744b2eac0a63625cda66096615754c68da9b2e3174bab0298e395719c52e97560531c762e33845d2eac0a630ed5dc2e8965d5814c794abac5d30abab0298f2952e8966157560531
def mo511H8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x590000370033007068000000a6c20000a100003500da001400000000
def mo511D9 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x490f06161bf0613a470de13e03c016d2586f09b004748b29c3784d802a1df09906e009243c1fc1f817005c4186fc1fc113abf5692153fa5fc4f07f0be0fc0d8059603a0540a614b29451ca36c500a513c1903285e07e0140456818e696f1de35c5789e0f81bc2f03f01e01a0a0ce98ea9771ee33c5b89e0f81dc2f03f03605c03ecf0d031c128a47c5f0640fe06c02b8d98e498d2d253c778d715e2783e06f0bc0fc0d80f010ac075ceb55039632162f81f804e1d3ae75aa81cbd8be07e01079eb061d3ae75aa81cbd8be0498c0c780f31d837b5f6b312aa133f65ecaf89c0fe17c0438f7122a1c0fe03c01a3071e837b5f6b712d97c0c84c14740ea1bdafb59a86cbb8bc0d01fc0310ee1bdafb5aa844c78be0780fc0b8059a031e62cc3b8630db1402984e8640fc1182e83f00c0214a38f21ddafb5b8915059fb2fe4a48f8bf1381fc2f817011a1fa039c69949579258e88b68377766e16365c250c4a34453dc3262de2801f61770c1000e67db66d4a95d581e6edb66c8a95d581eaddba299854c570eadca6695854c570eadda8299854c570fad4a6615814c570c67db66d4a95d581c6edb66c8a95d581e27dc62a5855d581a6dcca660965d531f25db9259855d531f25c96655855d531ab5cca661855d531f25d98259855d5319ed5cb29c9660531be55c529c9660531bec5c229c9660531ced5c62e97560531cf55c52e97560531cfc5c22e97560531ced4ba2597560531fa54966157560531a6dcc96a0a64c550cb54ba6157560531
def mo511H9 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x800000000000004a000085000000009c000027000000c693002900002b003d0000000000000008000072b1740000
def mo511D10 (j : Nat) : Nat := if 3 ≤ j then 0 else (if j<1 then 0xff3c2c1ae6b7252819a65e95e4f8bc2f89c1f84e0280a0505333c6b9acc94a065e95e4991e2f88c1f85c0903e06809ac0a811ce5e94a5792e3b8d62f88e2707e1385c0f81a038098581473c8eaaeab72468297e4a91e2f0be270681f85e03809850cea3b8deafab69ec7697e4b8be270781f85c0f8160254eaaeab2a147296a579362f89c1f85c0f80a01f9463c6b9ad894a1a6197e4f8be2607e1703e01e73cc06fe3c6b9ad894a066e9865f93e2f8981f85c0b8092c10ea36ebbaca839f47397e4d8be260681f85c0f80e024144c08eca0c7595e4b8be260701f85c0e03e058086503063c0e8376bdad892a067e9965d95e4891e2f8981807e1703e02d0ec376bdad892a16789965f93a4591e2f8981f85c0e03e0380a0598f43b0ddaf6b62b0ad9f65f93a4491a2f89e170380f80e0298f1ae6b1a065995e4e91a2f89e170380f80601f35eada5d9525693a338be2689c1e85c0f81a058086eb5b736d5db3b6c7dafe6b75ac16a81a6b6901a0667819b06561914634188c610d7e65dc16fa5a61604567551352254364eb13544bc9281482d1ae45090e5422103a3f10f443b38e6737c4d8f34f0ccb3154bee2e6cb432b98a8e28b09d425c88fc22188241f587831cfc6f11a64641175457314304aa11203e60e2433b0bb429008cc1e005bc10802840530001fb7259855d531ffab0abaac298eff5b6684855c2feed990ab0ae17fb6c88558570bfeb6242ac2b87bddba615315c3deed2b0a98ae1ef76a1854c570fdb94cc2a62b87fd585585315c3f6e5330a98aa1ff5615614c550ebeb4ebb32242db7cb9619855d737edb152bab039df6d4a95d581cfdb6454aeac0dbedb221d855875be5d30abaac3eb769c9661531f5b94e4b30a98fadc96681854c7d6ec392cc2a633f72e9985d531edbb304b2ea98f6dc96655754c7daedcb0abaa63eb7259855d531f6bb2ac2aea98fb5d98615754c7f2e4b30abaa63bb76a0961d531fda94e4b30298fed4965d5814c7deadbb0ab0a63ef52dd8558531f7ab60c2ac298fbd587615614c7deac2aeab0a63fd56157558531bfab703aac298fadca661531603deac2ac298b01bf56cda121570ddbb5053262b86edca6695315c3d6e5330a98ae13f76e8854c570bf9b6442a62b85fd5b1215315c3f6a5330298ae1ef5615814c570f7ab0ab0a62b857dcb96a13154376ed414c98aa1bb7299a54c550f5b94cc2a62a87ed4a660531543deac2ac298aa18df6a1a665487b4fb6c4c30abae37ca96157560796ed492cc2a63cb765c9661531e5b92ccab0a98dbcdb221d854c6dead890ec2a63cb76609661531d6b974c2aea98fa5c96615754c756ed412c3aa637d56d4a760531bf8b6453b0298fad587259814c7d6a4b30ac0a633f52e97560531f6ab0abab0298fb55855d5614c6deadc0eab0a63cb72598564131 else (if j<2 then 0x68ee3e8ce358b22e88e270781e84e1703e0680e036544c18deafab11c07699664972568f63e8d6338aa2e896270781e8561703e06816036cf1a0c7297a4390e3b8de2b8ae270781b85e038080513033a8ee37abead2869ec721da5c95a3e8ce2a8be2689c1e07e1685c0f81a0580d850cf31ca5e90e438ee378ae2b89c1e06e1781603808b3d8db1c2629625690e438ee378ae2b89c1e06e1781603809b3a8ee37abead6869ec75992669725d8f6338be270781f85c0f81602d4e83aabaaca851c07398a5a94a3a8d6288be2289c1a07e1285c0f80a02eb03aeeb2a0a6396e538ee358a62b8981a06e1703e038094c00ec376bdada84a16791d2659763d8ce298b62585c0e03e0580ae3c8ea2a6839ec7690a438ee368aa2b88e170380f80e024161d78f31ce5995a4290e3b8da2a8ae2385c0e03e0380963c8ebac68396e4e90e368aa2b89c0e03e03807e3c8ea366839ec719665690a458ee3d8ce368aa2b88e170380f8160380b9d78f43b6bdad8ac2a6851c656912458f6368b22f89627856170380f8160380ce3d0ec376bdad8ac2ae859e6659665e912438ee368be2785c0e03e0380be3c0e9a047196656902418e6368a22f88627846170380f806029502ba8ef2d4871765515c4d8fc338ac2f89c268781f0541683e0701602f2f43bcb321c5b156438fc358b42f09c1305a0c83e0700e026360d1d28432641925415c4f0dc2b8bc2705e0700834827318c5f14e5712e3f0cc358b42f08e268781f04c1683e0700e02c3454827719665174571363f0d4338ac2f096268781f0541683e0701602fd2aba8ef1fc5d9545713c338ac2f89c268781f05a0f81c0580a0c4271984619445713c370a22f09a1e07c1781c020360d18e9286611865115c4f0dc2e8bc268781f04e022340428e91865115c4991c370ba2f0821f05a0883e070090d1d283bc7d19c5f15c4f0ce2b0bc2705a0c83e07008cbd0eca46871ec7b15c4d90e470dc2f0821f0520f81c03809f4b2f43bc7b15c4d91c358b42f09c168320f81c038089412f11e271164410ec310de290a4268601f0441683e01009b41cb09cc6716e5b15c4b8fc330d62d0bc2389a1e07c1305a0f81c0380bd41cb09dc6599c5d974571363f0ce2b0bc2589a1e07c1505a0f81c0580bd40aea3bcb71745713c338ac2f89c268781f05a0f81c05809d400ef2d46717c4f0ce2b0bc2705a0c83e07007c3bcb716c57136470d62d0bc2705a0c83e0700e0216932185f936458be278761f85e0f80e01a694a14789806717e499044789e1f85e0f81a01fabeadc9120a7e96057928478be270681f85e0f816022b02a047397a5792e3b8d62f88e2707e1385c0f80e022b5baeeb39e47397a5295e4b8ee358be2389c1f84e1703e0680e02b35cc04e91d65c95e4d8f6338be2589c1f8561703e06816026160502 else 0x544c0cea3a4ee372849e8711d2649725607601f0dc2a6819e661966569124602e01636348c3708e08a3162a2ae0dc20a3662b83709a08a3122b8308bc26823348c338bc2780e00cd230ce2f09600ad2194c338bc25803548aea3a2e89d4670d437096014d23196470cc370920b804540aea3a2e89d46515c3705415805b196470dc130520b803a426b9ad855916298be0f8049a42831e6418e6358a62989e19866178260f81a01808c410deafab52127e97a5789c1f85e0f80682e0b7244829605f8be2707e1783e03806c410deafab72527e97a578be2707e17826859ca91785711c3f0dc2707c1783c0b80a01c1672a8aa17c4211c3f0dc2f09c1a07c1783c0f81c038092c14e93aebbaca839e47397a538ee358a62f88e2706c1f84e1703e0380bad61453aebbaca811ce5e94a538ee358a62f88e2706c1f84e1703e0380bcc0ce93b6b4a165e9564d8ce298be2589c1d0761703e05809ac14e93acdbaeeb2a0e791ce5a97a5295a3b8fa338d6298be2389c1b07e1385c0f81a0380e8c14f1a02811c26096250902388de288a2270601885c0f802028b0637abeace82a04701ca6296a5))
def mo511H10 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x72e000010021a24c880068e45729210165a0012ad0747d20003a659725a2dadbae1dc3000000017980000001a8c02005900051986078
def mo511D11 (j : Nat) : Nat := if 6 ≤ j then 0 else (if j<3 then (if j<1 then 0x6888657c62045f405c585928561c5358504c4cb049ec470443f841583e4c3b4037ec35dc33a832042fd02d782b68293426b8241821781e901c141a7018a81698146411e80ffc0d5c0b280864067803d802340003ffd855d561fff615655c3ffd8558570fff215615c3ffda854570fff615515c3ffd8558550bff2a5865d7f7d855d565f7f615755c6ffda521d61eff69d85587bfca761561eff68185587bfd8761561eff21d85587bfd855d561fdf61575586ffda81d561dff66197546ffda921d51dff65d85547f7d985d551fdf61575547ff59760551dff66190547ff58164151ff7661754c7fdd955d531ff7615754c7bfd8558580eff699855c3bfda161570eff619855c2ffda121570eff615655c3f7d8559570eff615815c3bfd8558570bff6a1515c3bfd8554570ffd605515c3fdda84c570ff7695315c3fdd854c570ff7215315c3f7d8559550eff61561543fdda84c550ff769531543fdd854c550ddf6999521f77da165487aff68497616bfda121d85df75d9932177ed7664885dfd69d912177f5a664485dfd5d9912177f5a064485bbf698985d6feda226175edf2a5855d7b7da661575edf685855d7b7c9861575edf619855d67fca961d65bdf69487596feda221d65edf69d85597b7ca761565edf68185597b7d8761565edf21d85597b7d855d565bdf69497606feda225d819ff2a575607b7d855d581bf768c855c6feda221571bfd684855c79fd855d571f5f615755c6f7da521d61bfb68887586dfda721561bf768c85586feda221561bfd68485586ff9a021561edf61575586bfda81d5619ff6a487546f7da521d51bfb68887546ff5a121d51cff65d8554777d985d551edf61575547f757560551bf7694874c7edd8725931ef76a5854c7bdda761531ef729d854c7bdd9761531ef7655854c7bdda061531ef7661854c7bdd8761531ef721d854c7edc9661531fb7259754c7bdd855d531fd7615754c6fdda81d531fb7258754c7fd4a760531ff55d5814c7fd58758531ff5615614c7fd57558531ff51d5614c7bdd85641319ff2a565603b7d8559580fb729931603bdd854c580ff558531602efda621570bf768c855c2feda221570bfd684855c3b7d8559570fb7299315c3bdd854c570ff5605315c3fd5614c570b7f69c85582fdda321560bfb68885582ff5a121560edf615655427fca960550fb729931543bdd854c550ff560531543fd5614c550bf768c85442feda221510bfd68485442afda621d85afb688876177d5a364485cdf2a5855d797d8761575e5f615755c6f5da521d31bf3688874c6fd5a121d31db7660964c76dd9725931db7259954c7adc96615319f76a4854c6ddda721531bf3688854c6fd5a121531bf6680854c7b5d855d531af76a0754c7bd58760531fb5259814c7bd58560531ef5615614c76dc9664131 else (if j<2 then 0x2f1309c3c1e0b8381e060140ce5b244e26033164a056271186c28178984e1e0f04c1e060162a053244d26033164a056271186c2f1309c3c1e0b8381602a2c10e58980cc59281589c461b0bc4c260b8381e06013cb54b1789a451f0d4582f1309c3c1d0f0502e0e078180602a204b548a00fa602f15890401d0c06e28178804a180f0402e0807800064ba1dcb13b198bc56270cc542f13094381e0a83c0c026a0af4772d52c5a2b1386e2e168bc4c250e0782e060180a2803b9629341988cc5e2b12c8c37170bc4c260a8241e060152f0772d8cc5e2b12c8c33150bc4c260a8241e060120ce5b244e26033164a056270dc5c29178984c1e0983c0c02b962a053244d26033164a056270dc5c2f130983c170702c05443964913c980cc5928158923e1b8b85e261107820170703c0c02e572b14a204bc572491c4e1f0b83c0c01c1f2b95a204d25e2b93c5e270f85c160200f160a0430c857278ac5e270b8058ad2e962822f9288e2f138683e170780c03d36974b1411e0ae4d1e8dc5e270f85c1e050108bc5b250fe4d238bc4c1c0f85c1e0300e160a33c572b648984be4f170bc4c1f0b8078b0519e2c15cad922693097c9e2e178983e13011140993c572b248984be49238bc44180f858100f012703401ccc65b2b92c76351788c4c1f098581e030121435daccf0733196cae4b1d8d45e231307c26160780c050500ea652e95c9a3d198bc4a260f8542c0f02808a751d4ae4b178983e160781402c45920713095c9e28178983e1700c160a037922793095c9e2e178983e1700e160a33c54c9134984ae4f170bc4c1f098078a0429e4913095c9247170bc44180f858100f011160a0ac53c91309446e2e178983e01b9e8ec6eaf56c953e97c9a47170bc4c1c0f85c060259e2b95b24502592b93c5c2f1307c2e0100f3047836d76b448a0cf65f2591c5e240c07c2c0f018098a2c01da823a99c962f13858180f00d141823d122832b934864717890301f0b0301e030128f32b9348a2f13858180f018058a2ad4ca5d2a934662f128983a160781403e442e41d63fc63e223d323b6a397e367230de2d66288624ea212a1d8e191a1512107a0c2a07fe04620179fce1f8fdf369f081ed75eb41e6a9e211dc35d82dd46dd0adcc81c855c429c0f9bc61b87db499b0b5ae39aa79a6b9a1b59d8999ed962d92498e898a1586c1836d7fd17c117899754571f16f096bb5691566bd644160ed5de15a8d56a953314f954bd54815450941fd3f5d3be538b5341d32312f912b8927c923c11fdd1bf919c5170113d110590d4d09d506a5037500b0fd14fa08f690f2d0eeecec28e8d4e658e298dfd4dbccd7e8d4dcd11ccd80c9e4c6b4c3ccc078bbe0b7b4b418b07cac50a8d8a53ca20c9e4c9a20966092c48ee08bd488ec85bc82f87fec7c7479b076ec73e070f86e586b7 else 0x82391b8b8522f10898301f0885c02038288e87536d76b3419f0e0733196cae4b1d8d4522f11898341f098581e0301b3027b24504732e95c96431d8dc562f118983e130b03c0602a60cf275aed6c91419e8e65d2b92c863b1b8b8562f11898341f0985c060346bcf35dad9228239974a2572590c7637170ac5e23130683e130b80c064d69e6bb5b24cf4732e944ae4b218ec6e2b1788c4c1f098581e050180c9acc09ec9239964ae4b218ec6e2b1788c4c1f098581e050180b1833c9d6b648a0cba53258dc5c2b1788c4c1a0d85c06028604f648a08e65d2895c9a43218ec6e2b1788c4c1f0985c0a03017306793a9b6bb5b245067a39964ba512b92c8a3b1e8cc6e2e158bc46260d07c26170280c080586b14679aed6c9248a08e65d2895c96431d8dc5c2b1788c4c1a0f84c2e050180edac509d0ec6ea08e07532974ae4d1e8cc522f12898381f0a8581e050194e8763757ab53d1c0ea652e95c9a3d198a45e25130703e150b03c0a0326b3067a3b1babd5b2450a7c3a964ae4d228f46e2e168bc4a260e07c2a170280c0773d1d8dd5ead926853d984ca592f934863b1b8b85e260e07c2e03018cf074ae56c91401ccc2592b92482391b8b8522f10898301f0885c02033604ed5eac8e0752e95c9a3d198a45e25130703e150b03c0a02c608f35dad1209142984c65b2b92c863b1b8ac5e23120603e130b03c06034600e86daed689540a0cf4753098cb6572690c863b1b8ac5e231384c2c0c0780c0763c1d0db5dacd067a3998cb65726904863b1a8a45e231384c2c0c0780c06858eb8f07436d04733196cae4d2090c7635148bc462709858180f0180cc783a1b6bb5a2a1567a3998cb65726904863b1a8a45e231384c2c0c0780c06e3cd76b23996cae4d2090c7635148bc462709858180f0180a9ae3d56c943a96ca255268dc5a2f128983a160781406028204b149200fc602e958903d140bc40270c07820170403c0002d524862f1348c35160bc4c270f0743c170703c0c03013141743b96c813b198bc56270cc542f13094381e0a83c0c02aa0af4772d524862d948ac4b1f0dc5c2d178984a1c0f0482e060180c1783b96c8633178ac4b230cc542f130982a090781804ca58f26033164a056249186e26138783c170703c0c02619c7938980cc59281589c37170a45e26138783c1307818054298f26930198b2502b1386e2e178984e1e0f05c1c0b01410e3c980cc59281589c37170bc4c260b8381e06012d2d4b1f8bc4d230d4582f1309c3c1d0f05c1c0f0300c050d05d0ee3c9d8cc5e2b138662a178984a1c0f0541e06014d2d7a3b52c7e2d948ac4e1b8b85a2f13094381e0b8180602a68d2b80bc1d293431ecc4662f15896461b8b85e2613054120f0300c1b0bc1dc7e33178ac4b230cc542f130982a090781804c359227930184a056271186c)) else (if j<4 then 0x450c7a3f168be4e2190c7637158bc46230d07c26170583c0602e9bcbe58a08f26033168b0572590c7637158bc46270d87c26170583c0a0301b691431e0cc5a2f92c84431d8cc5e2313878361f0985c160f0280c0604157ab248a04fa5e2b92880401c0d8502f1009c301f0805c100f0000c8acae56c9130184b0582b9388c3e1b0a05e26138783e160b8381e060080d07cb0182b95b244d26030960bc57271187c36178984e1e0f8582e0e0580d648a0cf65f2710c7636150bc46270f06c3e130b82c1e03015c914197c9c42218ec6c2a1788c4e1e0d87c26170583c0602b922832d9388636150bc46270f06c36170583c06025922833d960ae4e2110c7636150bc46270f06c3e130b82c1e050180c648a0cbe4e2110c7636150bc46270f06c3e130b82c1e050180b0aeaf56c91429f4b85f271187a3e1a8d8582f130944e1e0e87c2c150b8381a0f0301406040572b64a218c25f278bc4c1f0b83c034cf202f87cae56c94409b8c25f278bc4c1f0b82c048401babd5b249027836960ba502b92080381b8a05e20130603e100b8201e0001c8de49214f87832970be4e229187c37170bc4c260e07c2c170703c0c0301a2c8672f96c963c9c0e26033164a057271187c37170a45e261307c2c13078180732f962a053258f26834980cc592815c9c461f0dc5c2f130983e160b8381603621cbe59258f26033164a05727118723e188dc5c2f130883e160b8381e0601b8bc5b250f2572691c5e260e07c2e0f01807c5e2d926843d980be4d218ec6e2f130703e170780c04c58572b654980c2582f9388c3e1b0bc4c260f8582e0e0781805858582b95b2a4d26030960bc57271187c36178984c1f0b05c1c0b018166549e4c0612815c9c461f0d85e261307c2c170703c0c02a222ce542a4e26033164a057271187c36140bc4c260f858260f0300c0b0a81426930198b2502b9388c3e1b0bc4c260f8582e0e0580b088424c0662c940ae4e230f86c2817898441f0b05c1c0f0300b0b0a64c0662c940ac461c8c06c2f130983e0e0781804e3757ab6562b4fa5c2f93888461f0d85e26130703e160b8381e060180ce54a04b0592815c9c461f0d85e261307c2c170703c0c010151595cad9226030960bc57241007037140bc40260f8402e080780006056572b648980c2582c15c9c41230f86e2e178984c180f8582e0e078180683e580c15cad9226834980c2582f15c9c461f0dc5c2f130983e160b838160362b2b959244c2582f140ae4e1f0dc5e220c07c2e0f0136bb5b248f0632e15c94421d0dc542f110983e120b8281e050100be49214f6652c17c9a421d0dc5e260f85c1e0201115c6eaf56c953e970be4e229187c37170bc4c260e07c2c170703c0c0301a1006daed6895419f4c6582b92c8e2f120603e17078098b0d628cf074ae56c9038984b6512b924 else (if j<5 then 0x2313070341f0a84c2e0501814e5a2a90c5d2d144aa451d8f86835160b84a250e07828120b8381a0f0301406038a4691431e8b8562590c7c32198a85c2313878361e0905c1c0b0781806034a4691431e8f45c2b12c863e190d8562e1188c341e0905c1c0b0781806034a4691431e8b8512b12c863e190cc54291708c4e1e0d87824170702c1e060280c074c221c783c980c0592815892411f0c06c2917084461a0c8782017070241e060080ee964952c7c2c940ac4d228f86835160bc4c25138783a1e0a05c1c0d078180a0301dd2d4b1e8cc5e269186a2c148bc4c270f0743c170703c0c0301692182a450c7c3d1f0b4512b13486451f0d06c2d170944a1c0c8782817070341e060280c0834b558ae3e168a256269147c341a8b05c25128703c140b8381a0f030140603624a91431e0f4602e15892411f0c06c29170844a1c0f0402e0e0483c0c0101bd2886a58f87c2c1589a451f0d06c2d170944a1c0f0502e0e0683c0c050180d884c052c7a30990a256270d85c260b8381e060115217aa44e4622f14cac4b218f86437170ac5c23128703c120a83c0c0301a34290bd5227631988b4562590c7c321b8b8562e11894381e0905c0c0301ad2a92bd1d2ed49a18f47939198b45b2915896431f0c86e2e168ac5e261189438190f0482e06018119b0d11d292451e4e66231948ac4b218f86436168ac5c2312870321e0905c0c0301dcb549198bc4d228ec7c35160a45e26138783a1e0a0482e0e078180603396aac57174b056269147c341a8b05c25128703c140b8381a0f0301406034a02f65aa44e4662d968ac4b218f86437170ac5c23128703c120a83c0c0301b5017b2d5227631998b65a2b12c863e1b8b8562e11894381e0905c0c0301a5057a3a5dcb549a04e4662d968ac4b218f86e2e168ac5e261189438190f0482e060180f8ae2f1669430190b05f2590c76331788c4e1b0f84c2e0b0780c05c57178b34a180c8582f92c863b1b8ac5e231187c26170583c0602e2b3315cacd28812f140ae49208e46e291788446190f8442e090780406456662b959a51025e2815c92411c8dc522f1088c321f0885c120f0300406832d267c3a180c65c2815c96431d8cc502f1189c361f098541e030180a3499f0d86031970a0572590c76331788c4e1b0f84c2e0b0680b885aed667c3018cb8502b92c863b1b8ac5e231384c2e0b0780c05c582186031970a0572590c76331788c4e130b82c1e0301416085aed667c3018cb8502b92c863b198bc46270985c160f0180b885ad0c0632e140a64b1b8ac5e231185c160f018090af2f962943c998bc57249008e270f85c1e0201f8d9632f9687934998bc57278bc4e1f0b82c044569b4ba58a08f45f2590c7637158bc46270d87c26170583c0602ed22863f168be4b218ec662f1189c3c1b0f84c2e0b0780c055a else 0x237154a9409e8c2612c940ac44211181601f2452230984a055230d06435148b84e0d058082922a554613095482461a0c86c25058071b22a9147a2894488321b09412d4821c321b08c01948213023099868321b094321b00c8a955184c055209186836090541601a20cbe58a450479208e46a29178844e190f8442e09078040545620abd5b24d02853d184ca5c2c9788c3d1d8f86a331b0b0542f130944e1e0e87c2c150b8381a0f030140604f178b64a1e0f0592a90c863b1b8ac5e2313070341f0985c160f0180c0b0d6572b6542a4c0612c168a25620118723e188d8502f130844c180f8582217070241e0600811254a0cf45c2b1088c3b1f0cc6c2a1708c4c1a0f04c2e0e0583c0c0301935e55968b8512b1088c3b1f0cc6c2a1708c4c1a0f04c2e0e0583c0c0301a6b254a18b65c299388c3b190d8542e11898341b0905c1c0b07818060329b4a9419e8b25c2895884461e8ec7c35198d8542e11898341e0985c1c0b078180a0301f161af2acb45c2895884461d8f86636150b846260d07826170702c1e060280c070d757ab6562a508592815888461e8f86a36160bc4c25130703e160a85c1c0d078180a030208dd5ead958ab429e8c2652e164bc44230ec7c331b0bc4c260e07c2c170703c0c0301e0a941184b0592815880461c8f86236140bc4c21130603e160885c1c09078180203b920853c1e4c25d21914763d198d4562d118983a130b834160f0280c06542572b648984b2411c8dc522f108983e110b8241e010146bb5b248f07831964b85521114743d190dc5a2a1789444260e07c2a120b834140f02808080411babd5b24d0a793d994b25d2190c7637158bc46260e07c26170583c06036211046eaf56c93429e4f46132970b25e2290c8c3b1f0cc6e2e158bc4c2313070341f0b04c2e0e0583c0c030279006daed6891419e4c853218ec662b1206c2e0b0780c052ad922652d96c863d1a8ac5a231307422170682c1e050180aa82ac922652d1549a37168b44e0d0781403cc09e8dd5ead92681411c0e2612c95486451d8f46637168ac5a23130703a130b03c0a03020541813d1babd5b248e07531984b25521914763d198dc5a2b1688c4c1c0e84c2c0f0280c0815060cf4753b1babd5b24d02853c9f0e47132964b25521914763d198dc5c2d158bc4a)))
def mo511H11 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x739664a0005a5ac9d25000000000dc6000000421000215c0b000d9e63b000000a9c448000d9df22a99a09000f2012971b000724e3400011facb000d0192c1cd93d00092a9030008800000004a3933c130009369310000000008050003959ab639097100aa1c28045000e12000b98000cca6ba111906840316000e4c64e000110344000000e435490005475a2000000846d04000f0c81e03f5a0da4d9bac8f5051c00081481da191c5041b35d3ab30e2f24f79f00000022e60e54b442e27c4de3c81a00000000083202bf23d3812dc023a693780d90a4cc000ac723e908000f174c4b26ccef0fa1800000920644500b3c521801104185900b39114200c001
def mo511D12 (j : Nat) : Nat := if 4 ≤ j then 0 else (if j<2 then (if j<1 then 0x405ca0795a4839312d29251b151711120d0a07010132096108b4a0a894786c585c484c3838202c181c0804058a17876594a42322e2a261b16151712110c0e0b02015a58f8b4a0a8986c585c484c38382c181c080404d78754a3e322e2a261b16151712110c0e0b020132b96928b4a0a89888685c484c38382c181c0804050825a2c2a261b161712130e0e0b060702010125e1d96528c8b8a8986c58545c484430382c0804cae5a4a2d282a261b161712120e0b060702010131716120c0bc908c4c3c2c1c0305c58302f2717130f0b0700b1817160d0c0bc9c5c4c3c2c14034a8a43c302b2717130f0b0700c120c0ac908c4c3c2c1c0286438302b271417130f090700c140d0c0ac9c5c4c3c2c1402c84302b2717130b0700916130c0a06c5c4c3c1c02a5e5a3e2f262317130e0f0b070100e1716100b0ac9c5c4c3c2c1c000364b262217130e0f0b070100b281d0ec945c483c281c02a7a492b271617120f0b0100b28601e12504cc948c5c4c28101c038b07b252117130a040700aae0557b2a8b53e0a555463283b4f709cb536326274b0893b522d23d746988b4512121c742d084150311fd33e887ac4f311de33ad87394e331be336d06bb4d3119ef32d863a4c3717eb2ee85c14b4316132b385464a4d143b27b84df498f12cb24d048548e5115721e842548190fd71ee83cb47630e6f1c3036c46ad0d1b198831846010b9716b82c345590a5713f826b44b90917116821043eb077f0e281ac432305e70b3014f4273049708900fd41d5035b06180b641550273048008540f101b30318058409300ef01800254033002b0000ffebb30bffd76217ff930bafff61975ffec2aebffd87597ff90eb2fff61565ffebaacbffc97607ffaeac0fff61571ffe42ae3ffd87587ff90eb0fff61561ffe42ac3ffd75587ff8eab0fff66151ffecbaa3ffd87547ff90ea8fff61551ffebaaa3ffd90547ffacac07ff58580ffea8b01ffd865c3ffb0ab87ff21570ffeb2ae1ffd815c3ffac2b87ff54570ffec2ac1ffc85583ffb0ca87ff61550ffeb2aa1ffd81543ffac2a87ff54550ffec2a21ffc85442ffb2a43dff64487dfecbb0bbfc976177fb2cc2eff5d985dfec8b0bbfd906177fb0ec2eff21d85dfec330b7fd97216ffb2242dff66175efec3aebbfd855d7efb0abadff66075bfec88ebbfd85597efb0ab2eff61d81dfec2b037fd985c77fb0ab8f7f5d571dfec2ac37fd98546ffb2ea8eff61551fbebaaa3ff581547fbb3098ff765d31feec3a63fdc874c7fbb2a98ff761531fee42a63fdd754c7fb8ea98ff764131dfec2b01fdd316037fb0ab87f74c570dfec2ac1bfd85543fba62a86ff61510b7ecb10f77d9521efdb2443d7f65c85b7ecb10b7dd93216fdb2442dfd64485bfcc810bb7d855d67fb303aedf61565f6e4b263bdd854c7fab0298ff558531 else 0xa25211e1b1615171211110c0e080b060507020101d2b1c9692504c0c8b4b4a0a8948478606c58545c4844483038202c18141c0804080a65a48484530322d282a25211e181b1615171211120c0e080b060507020101f2b17160c0b4a0ac9080706c505c404c303c202c101c0005c985c5948302c2b24201c1b141710110c0f080b040700017205756104f4b8ac9484746c545c444c343c242c141c0405cad5d58412e282b25211d1b151711130d0f090b0507010172052104b8ac948474645c444c343c242c141c04050ad5d59493d2e282b25211d191711130d0f090b050702010182052104b8ac9484746c545c44443c242c141c040508158412e29251b151711130d0d0b050701012205756104f4b0b8a0ac94887478646c545c444c343c242c141c0804070ad5d58412e282b25211d1b151711130d0f090b050702010182052104b8a0ac94847464505c444c343c242c141c080405c6d5d583c312c2c2b24201c1b141710130c0f080b04070001821520f0c0b0ac9080706c505c4044303c202c101c00058806e5e58403e2e2b24201c1b141710130c0f080b040700018201b1716500f4c0c8a0ac9c5c4c3c2c1c044ac825e58423e2c2b26221e1b161712130e0f0a0b060702010192b9796508f4c0c8b0bc9884746c5c4c383c2c1c040545c58402c2b24201c1b141710130c0f080b0407000152120171652100c0b0ac9080706c505c4044303c202c101c00064ac824a2c2b26221e1a1712130e0f0a0b060702010152b92504cc9888505c4c383c2c1c0403c806d5d5a48413d2f25221e1b17120c0f0b0702010152092108b4a0ac988488786c585c4848303c282c181c08040625e5a48403d322c2b24201c1b141710120f080b0407000172ba6979692108f8b4a0ac9888786c585c48483c282c181c08040685c5a483d2b252317120c0f0b0700e958b4a0ac988878685c48483c282c181c080404c8248403d302e2b24201c1b141710120f080b0407000165756920f0c4b8ac9080706c505c40483c202c101c00058ac84824a2c2b26221e1b161712120f0a0b06070201016211b5756924f4bc9488786c5c48303c2c1c0804c848049413032282b2717130b0700e601e92500e4c4b4ac9484746c545c44483c24281c04058a0795d5a493c39312d2b25211d1b151711120f090a0701018289e1d1b575692504f0e4c4b4ac9484746c58545c4448303c242c04070b0a2795d5a484839312d2b25211d1b16151711120c0f090b0101a281e920e4c4b4ac9484746c545c44483c24281c04055aca278746e494039312d2b25211d1b16151711120c0f090b0101a2c289e1b92120e4c4ac9484746c58545c4448303c242c0406278746d5d5a493c39312d2b25211d1b16151711120c0f090b0101a609e5756920e4b4ac9484746c58545c4448303c242c) else (if j<3 then 0xd282b2621221d1e191b1615171211120c0f0a090b06050702010289717961692128f0f4c0c8b4a0ac9884887478646c58545c484448303c28242c18141c08040946d5d5a5455413d30312c2e292b2620221d1e191a14171211120c0f0a090b06050702010242c57564c0c4b0b8a4ac98808874786468505c484448303c28242c18141c0804081ac6e54554130322d2d282b2620221d1e191a14171211120c0f0a090b06050702010222c1b4c0c8b4a0ac98808874786468505c484448303c28242c18141c08040786d5d5a54553e31312c2d282b2620221d1e191a14171211120c0f0a090b060507020102357568c4b0b4a0ac98808874786468505c484448303c28242c18141c080407884806e4941312e2b25211d1b151711120f090b050701017211b5756924f4c4b8ac9484746c545c44483c242c141c0406084806d5d5a4940413c3d30312c2e282b2621221d1e191b1615171211120c0f0a090b06050702010282b575692124c0c4b0b8a0ac9884887478646c58545c484448303c28242c18141c080408cac84806e494130322d2c2b2621221d1e191b1615171211120c0f0a090b060507020102321201b5756924f8c4c4b0b0ac9884887478646c58545c484448303c28242c18141c080409085585a49312e29251b151711120d0b050701013209652908c0c8b4b4a0a89484786064505c48444c383438202c18141c080407e58564230322d2e292a25211e181914171211110c0e080b060507020101d2120965290108c0c8b4b4a0a8948478606c58545c4844443038202c18141c08040849149423d30322c2e292a25211e181914171211130e0d0e080b060507020101fa524508f0f0c8b0b4a0a8948478606c58545c48444c383438202c18141c0804080463c3d30322d282a25211e181b1615171211130e0d0e080b060507020101e24528f8c4c8b0b4a0a89484786064505c48444c383438202c18141c080407a94918149423c3d30322c2e292a25211e181b1615171211110c0e080b0605070201022158f8c4c8b0b8a4a89484786064505c4844443038202c18141c080407184854a3c3e31322c2d282a25211e181b1615171211110c0e080b06050702010202b239692504c0c8b4b4a0a89884786068505c48444c383438202c18141c08040825a484530322d282a2620211e181a14171211130e0d0e080b060507020101e2c209652504c0c8b4b8a0a89484786064505c48444c383438202c18141c080408082594130322d2c2a25211e1b1615171211130e0d0e080b060507020101d96528c4c8b4b0a894847864505c48444c383438202c18141c080406c8259494130322d2e282a25211e181b1615171211110c0e080b060507020101f96158c4c8b4b8a0a89484786064505c4844443038202c18141c08040708482594a31322d2c2 else 0x2b575652904f0f0c4b0b8a0ac94808874786464505c48444c38343c28242c18141c08040905c59493c3e30312e282b2520221d1e191914171211130e0d0f0a090b06050702010222b1b97960f4c8b0b8a0ac9484746c545c444c343c242c141c04068b0825e594940423d30322c2e282b2520221d1e191914171211130e0d0f0a090b06050702010262b20979650108f0f4c0c8b0b0ac9884887478646c58545c48444c38343c28242c18141c0804098815d5a49413c312c2e282b2620221d1e191a14171211130e0d0f0a090b06050702010232b5756924c0c4b0b8a0ac98808874786468505c48444c38343c28242c18141c0804088ac82494130322d2c2b26221d1e191a14171211130e0d0f0a090b06050702010202b205756924f8c4c4b0b0ac988874786468505c48444c38343c28242c18141c0804088815d5a484842312d2b25211d1b151711120c0f090b050701019201b57569290104f0f8c0c4b0b4a0ac9884887478646c58545c484448303c28242c18141c080409cae989a5e5a4940423c3d30322c2))
def mo511H12 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x78d954fd240004a2d83c08320144c5d3aa72b17f0708b747181d8000538000a1310bba4c144fab0003057495a3cf882407229d1690a1410d930000cb40806396946c8a900a97808827900ad2e70da9c2c90000d470001121a0a23a00005020455c14aaf5294a5e58d601833b29d0f8000c0e80d38e8e3800012b0000001948e3e0005990000a7d11a3ab68a000045640eb4a4c15044d99f8a946a7c500010fe7277348000c605b178f69d6c2d31adc5deb5cb40004c4f085400e4d12e82c07233320c60a5a421d2142641eb53000b4d80e1c001c014d608cfc4f67c643185ca60055a18ea9b8bc668146a13c92661d1c0ae3550543554d222a2362a2f11088d80ce92d438966093ca3144561ab4a841e4f912af25c3f00011628a2b985c46038940c25d488a13b32000b3012bf41838373de92e320647c29a9cd8b84aab4dfc72a5f994d09d0a80ed00990c36bf95c12378ca0e0088c778b4b26560eb2581e19add51a4e21be04a8c6a781bb161308426c82378b0048843d2b28100dfd2a45092a601f432d3f1cb0b5d50082fc86ad1f085b0a795e8c3f8f43121b78ccc6e00022caf0ad3491ef47f8cb88c1aae0147070a21011700155064147d070f0d086350497a02a68604650112ae011c10160d06072878000e261f040c050040012b0c760232000f001148
def mo511D13 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x80b96203c60b15244070d142c4090c1c205040c000c172c3058a92203868a16204860e102820600055012203058a92203860b102430708141030002a5cb121e3058a92203860b102430708141030002cac80c162a4880e1a2858812183840a08180015182a4880e1a2858812183840a081800122e5878c162a4880e1a2858812183840a08180016405cb0b15244070d142c4090c1c205040c000a92182c549101c3058812183840a08180013404880c162a4880e1a28588101c205040c000aa62e5890f182c549101c3450b10203840a08180017182c549101c30588101c205040c0008a1243058a92203868a16204070814103000285880c16284868a16204860c14103000243c60b14243450b10243060a081800112c4860b14244060b10243060a081800122c3058a121a285881218305040c000896243058a121a28588101828206000445498b121c28300012789498a1620385009a0b9728d98397a071c67c5e35584bf41839b30928520818410708a045000ffd87ffc87ffd86ffd76ffd85ffc85ffd75ffc75ffd65ffd81ffd71ffd61ffd51ffd80ffd70ffd60ffd50ffd10bfd85fdd31
def mo511H13 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xd4c0c3f31c28d2701175c0611630000009c674f00065fbcc0689c9113852003a22000f9570284e3d633a000c0a000a19e147d5292a3e16700034826cc9470e05a265a0c757504115000208b01842000439000c9811fc2a00000090ff17ec4dd393f05d71cb32000fd114b000000fca00015b19700081a2cdc23000829555000000f9103de34ac2e07151000e96f1071d00044d52d469000a25000605762000b5300070b1875c5d60b46b0d1402c836ee38b6bb1e4d4190a59e5ef6d341000006700693a4722bc21b49864c16000000000f1804400011b000f431569d016600012e96f6cf2378c7ebac2ca3c93332f724b4aa6a630658645b3b412535209254636e20026a507d25cb0006ce000320c2035259cc0147880142901a6120420a041c00100441812600113061c002
def mo511D14 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x48a20610200fff
def mo511H14 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xb1fa30020ed458ff9400100e6002c3010c5003a451a920020b00053002ca1340000000a0a8c0008884249207a214500d
def mo511L : Nat → Packing
  | 7 => (11,7,6,0,0,10,0,mo511D7)
  | 8 => (14,6,6,0,0,10,0,mo511D8)
  | 9 => (24,5,6,0,0,12,0,mo511D9)
  | 10 => (81,4,6,0,0,14,0,mo511D10)
  | 11 => (179,3,6,0,0,16,0,mo511D11)
  | 12 => (112,2,6,0,0,15,0,mo511D12)
  | 13 => (20,1,6,0,0,12,0,mo511D13)
  | 14 => (1,0,6,0,0,0,0,mo511D14)
  | _ => emptyPacking
def mo511I : Nat → Nat → Option (Nat × Nat)
  | 8 => lookupWord 2 29 0 8 4 0 mo511H8
  | 9 => lookupWord 3 53 0 8 4 0 mo511H9
  | 10 => lookupWord 7 41 3 10 5 1 mo511H10
  | 11 => lookupWord 28 157 6 12 7 1 mo511H11
  | 12 => lookupWord 60 263 8 13 8 1 mo511H12
  | 13 => lookupWord 36 179 7 12 7 1 mo511H13
  | 14 => lookupWord 6 37 4 10 5 1 mo511H14
  | _ => fun _ => none
def mo511 : Forest := ⟨1535,14,fun i => mo511Y[i]?.getD (0,0),mo511C,mo511A,mo511L,mo511I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P7_0 : block mo511 7 0 4=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P7_4 : block mo511 7 4 7=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo511B7 : block mo511 7 0 11=true := (@block_merge mo511 7 0 4 7 mo511P7_0 mo511P7_4)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P8_0 : block mo511 8 0 7=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P8_7 : block mo511 8 7 7=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo511B8 : block mo511 8 0 14=true := (@block_merge mo511 8 0 7 7 mo511P8_0 mo511P8_7)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P9_0 : block mo511 9 0 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P9_1 : block mo511 9 1 17=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P9_18 : block mo511 9 18 6=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo511B9 : block mo511 9 0 24=true := (@block_merge mo511 9 0 1 23 mo511P9_0 (@block_merge mo511 9 1 17 6 mo511P9_1 mo511P9_18))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P10_0 : block mo511 10 0 21=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P10_21 : block mo511 10 21 47=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P10_68 : block mo511 10 68 13=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo511B10 : block mo511 10 0 81=true := (@block_merge mo511 10 0 21 60 mo511P10_0 (@block_merge mo511 10 21 47 13 mo511P10_21 mo511P10_68))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P11_0 : block mo511 11 0 25=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P11_25 : block mo511 11 25 96=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P11_121 : block mo511 11 121 7=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P11_128 : block mo511 11 128 44=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P11_172 : block mo511 11 172 7=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo511B11 : block mo511 11 0 179=true := (@block_merge mo511 11 0 121 58 (@block_merge mo511 11 0 25 96 mo511P11_0 mo511P11_25) (@block_merge mo511 11 121 7 51 mo511P11_121 (@block_merge mo511 11 128 44 7 mo511P11_128 mo511P11_172)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P12_0 : block mo511 12 0 16=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P12_16 : block mo511 12 16 50=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P12_66 : block mo511 12 66 46=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo511B12 : block mo511 12 0 112=true := (@block_merge mo511 12 0 16 96 mo511P12_0 (@block_merge mo511 12 16 50 46 mo511P12_16 mo511P12_66))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P13_0 : block mo511 13 0 2=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P13_2 : block mo511 13 2 18=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo511B13 : block mo511 13 0 20=true := (@block_merge mo511 13 0 2 18 mo511P13_0 mo511P13_2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P14_0 : block mo511 14 0 1=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo511B14 : block mo511 14 0 1=true := mo511P14_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511T : checkedTables mo511 14 := by
  intro k hk
  interval_cases k
  · exact (rfl : block mo511 0 0 0 = true)
  · exact (rfl : block mo511 1 0 0 = true)
  · exact (rfl : block mo511 2 0 0 = true)
  · exact (rfl : block mo511 3 0 0 = true)
  · exact (rfl : block mo511 4 0 0 = true)
  · exact (rfl : block mo511 5 0 0 = true)
  · exact (rfl : block mo511 6 0 0 = true)
  · exact mo511B7
  · exact mo511B8
  · exact mo511B9
  · exact mo511B10
  · exact mo511B11
  · exact mo511B12
  · exact mo511B13
  · exact mo511B14
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511G : graphValid mo511 (boundsBefore KM509) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511R : Impossible false graph 14 inputs.toFinset := by
  rw [show graph = targetOf mo511 by decide +kernel]
  exact root_index (g:=mo511) (top:=14) (i:=0) (before_sound KM509 VM509) mo511G mo511T (by decide) (by decide +kernel)

end PEqualNP.Outside.L_meta_10968
open PEqualNP.Outside.L_meta_10968 in
theorem PEqualNP.Outside.L_meta_10968 : ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 9 (fun x : Fin 9 → Bool => (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 5) || (x 1 && x 6) || (x 3 && x 6) || (x 0 && x 7) || (x 1 && x 7) || (x 4 && x 7) || (x 2 && x 8) || (x 3 && x 8) || (x 5 && x 8)) t → 15 ≤ t := by
  intro t hs
  by_contra! small
  obtain ⟨C,hf,hsize,heq⟩ := hs
  exact directSplit mo511R g511R ⟨C,hf,by omega,heq⟩

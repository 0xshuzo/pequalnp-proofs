import PEqualNP.Defs

-- The two-mode live-state and cofactor checker follows L_meta_1674 and L_meta_670.
-- The graph, restrictions and all search certificates below are for L_meta_10992.

-- Shared forest and cofactor certificates from L_meta_1674 and PR 11111 for L_meta_1677.
-- The original credit line is retained below. The two root certificates here cover the unpinned graph.

-- The checker and the bound certificates are adapted from PEqualNP/Outside/L_meta_1667.lean (Apache-2.0).
-- Two modes: u=false are monotone runs (AND, OR); u=true are runs up to complement, where negation is free.
namespace PEqualNP.Outside.L_meta_10992
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
def graph : Sig := 0xfffffffffffffffffffffffffffffffffffffffffffefffcfffffffffefefcfcfffffffefffffffafffffefefffffafafffefffcfffafff0eeeeccccaaaa0000
def sample (r : Row) (j : Fin 9) := bit r (inputs.getD j.val zero)
def edge (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 6) || (x 0 && x 7) || (x 2 && x 7) || (x 4 && x 7) || (x 1 && x 8) || (x 2 && x 8) || (x 5 && x 8) || (x 7 && x 8)
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
  (x 0 &&& x 4) ||| (x 1 &&& x 5) ||| (x 2 &&& x 6) ||| (x 3 &&& x 6) ||| (x 0 &&& x 7) ||| (x 2 &&& x 7) ||| (x 4 &&& x 7) ||| (x 1 &&& x 8) ||| (x 2 &&& x 8) ||| (x 5 &&& x 8) ||| (x 7 &&& x 8)
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
  (x 0 &&& x 4) ||| (x 1 &&& x 5) ||| (x 2 &&& x 6) ||| (x 3 &&& x 6) ||| (x 0 &&& x 7) ||| (x 2 &&& x 7) ||| (x 4 &&& x 7) ||| (x 1 &&& x 8) ||| (x 2 &&& x 8) ||| (x 5 &&& x 8) ||| (x 7 &&& x 8)
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

def neighbor10992 (i : Fin 9) : Nat := [4, 5, 6, 6, 0, 1, 2, 0, 1].getD i.val 0
def absentRow10992 (i : Fin 9) : Row := Fin.ofNat 512 (1 <<< neighbor10992 i)
def presentRow10992 (i : Fin 9) : Row := Fin.ofNat 512 ((1 <<< i.val) ||| (1 <<< neighbor10992 i))

set_option maxHeartbeats 1000000 in
theorem requiredInputs :
    (∀ i : Fin 9, bit (absentRow10992 i) graph ≠ bit (presentRow10992 i) graph) ∧
    (∀ i j : Fin 9, i ≠ j →
      bit (absentRow10992 i) (inputs.getD j.val zero) =
      bit (presentRow10992 i) (inputs.getD j.val zero)) := by decide +kernel


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
      apply raw_required run inputs (inputs.getD i.val zero) sub (absentRow10992 i) (presentRow10992 i)
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
def KS145 := extendKnown [] 4 [(145,[]),(290,[16,84,135]),(388,[32,16,116,84,101,134])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VS145 : Known true KS145 := extend_ok (m:=145) baseKnown lowS145 (by decide +kernel)
def g149Y : Array (Bits × Bits) := #[(0xfdf00fff81fc7e3ffbe01fff03f8fc7ff7c03f,0x45c09245142904808b81248a28520901170249),(0x0,0x0),(0xe6a8703ffe007fc7cd50e07ffc00ff8f9aa1c0,0x96a9b6d618b228112d536dac316450225aa6db),(0x0,0x0),(0xfbb781ffffff8007f76f03ffffff000feede07,0x235249820c03122046a49304180624408d492),(0x0,0x0),(0x0,0x0),(0x64ffe3ffffffff80c9ffc7ffffffff0193ff8,0x24920410040040004924082008008000924),(0x0,0x0)]
def g149C : List ColumnInfo := [(4,0,145,0,4)]
def g149A : List (List Nat) := [[],[64]]
def g149D4 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1f
def g149L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,g149D4)
  | _ => emptyPacking
def g149I (_ _ : Nat) : Option (Nat × Nat) := none
def g149 : Forest := ⟨149,4,fun i => g149Y[i]?.getD (0,0),g149C,g149A,g149L,g149I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g149P4_0 : block g149 4 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g149B4 : block g149 4 0 1=true := g149P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g149T : checkedTables g149 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g149 0 0 0 = true)
  · exact (rfl : block g149 1 0 0 = true)
  · exact (rfl : block g149 2 0 0 = true)
  · exact (rfl : block g149 3 0 0 = true)
  · exact g149B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g149G : graphValid g149 (boundsBefore KS145) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowS149 : Lower true (varsX 149) (graphGoal 149) 5 := lower_forest (g:=g149) (i:=0) (hints:=1796) (before_sound KS145 VS145) g149G g149T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KS149 := extendKnown KS145 5 [(149,[]),(294,[16,84,135]),(389,[32,132,84,101]),(390,[32,16,116,84,101,134]),(401,[130,50,83,101]),(404,[32,16,65,49,131,83,101]),(418,[16,114,50,84,67,100,134])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VS149 : Known true KS149 := extend_ok (m:=149) VS145 lowS149 (by decide +kernel)
def g197Y : Array (Bits × Bits) := #[(0x2fc38ff01fff1ff02fc38ff01fff1ff02fc38,0x42ccdb2a5451240242ccdb2a5451240242ccdb),(0x0,0x0),(0xfdcbc7fffe07fe3ffdcbc7fffe07fe3ffdcbc7,0x1448490c186040841448490c18604084144849),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0xece607fffff8003fece607fffff8003fece607,0x8a7b6b06085892808a7b6b06085892808a7b6),(0x1b3df8ffffffffc01b3df8ffffffffc01b3df8,0x893124c081060030893124c081060030893124),(0x0,0x0)]
def g197C : List ColumnInfo := []
def g197A : List (List Nat) := [[],[96,114]]
def g197D3 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xf
def g197L : Nat → Packing
  | 3 => (1,0,1,0,0,0,0,g197D3)
  | _ => emptyPacking
def g197I (_ _ : Nat) : Option (Nat × Nat) := none
def g197 : Forest := ⟨197,3,fun i => g197Y[i]?.getD (0,0),g197C,g197A,g197L,g197I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g197P3_0 : block g197 3 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g197B3 : block g197 3 0 1=true := g197P3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g197T : checkedTables g197 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g197 0 0 0 = true)
  · exact (rfl : block g197 1 0 0 = true)
  · exact (rfl : block g197 2 0 0 = true)
  · exact g197B3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g197G : graphValid g197 (boundsBefore KS149) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowS197 : Lower true (varsX 197) (graphGoal 197) 4 := lower_forest (g:=g197) (i:=0) (hints:=33555975) (before_sound KS149 VS149) g197G g197T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KS197 := extendKnown KS149 4 [(197,[]),(212,[64,16,49])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VS197 : Known true KS197 := extend_ok (m:=197) VS149 lowS197 (by decide +kernel)
def g179Y : Array (Bits × Bits) := #[(0xc00fff0ffffffc00fffff0fffeea3a5303f03f,0x84a08a210802284a0280220882200a53145145),(0xfff0000ffc3fffff003fffffc009adfd000fc0,0xc42c405090b10c4b11404108092d994d34d3),(0x0,0x0),(0x0,0x0),(0xfffffff0003fffffffc000fffd77e88afc003f,0x90130026104c0100c0584120152a08828a28a),(0x3fffffffffff00012697f4000fc0,0x2e09c08b822702609026009c11269264b2cb2c),(0x0,0x0),(0xffffffffffc0000000000000039d530dfff000,0x300e000c00380380e03808e0208d5104c30c30),(0x0,0x0)]
def g179C : List ColumnInfo := [(0,2,145,32,5)]
def g179A : List (List Nat) := [[],[116],[81],[81,116],[64],[64,112],[64,81],[64,81,112],[112,64],[112],[112,81,64],[112,81]]
def g179D5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x3f
def g179L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,g179D5)
  | _ => emptyPacking
def g179I (_ _ : Nat) : Option (Nat × Nat) := none
def g179 : Forest := ⟨179,5,fun i => g179Y[i]?.getD (0,0),g179C,g179A,g179L,g179I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g179P5_0 : block g179 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g179B5 : block g179 5 0 1=true := g179P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g179T : checkedTables g179 5 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g179 0 0 0 = true)
  · exact (rfl : block g179 1 0 0 = true)
  · exact (rfl : block g179 2 0 0 = true)
  · exact (rfl : block g179 3 0 0 = true)
  · exact (rfl : block g179 4 0 0 = true)
  · exact g179B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g179G : graphValid g179 (boundsBefore KS197) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowS179 : Lower true (varsX 179) (graphGoal 179) 6 := lower_forest (g:=g179) (i:=0) (hints:=1048660) (before_sound KS197 VS197) g179G g179T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KS179 := extendKnown KS197 6 [(179,[]),(307,[16,84,135])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VS179 : Known true KS179 := extend_ok (m:=179) VS197 lowS179 (by decide +kernel)
def g213Y : Array (Bits × Bits) := #[(0xf003ff87fe1fffc01ffff87fffe474a4007c1f,0xa12845108440228940a01108826014a45294a5),(0x0,0x0),(0xfffc0007ffe1ffffe00fffffc0335be20f83e0,0xc030162028040b0182c0a00108225922318c63),(0x0,0x0),(0xfffffff80001fffffff0007ffccfd11df0001f,0x240980130884c020302c2120087c108a5294a),(0x0,0x0),(0x1ffffffffff80004d2fe80003e0,0xb82e045c111702c140b005c104d26c9ce739c),(0xfffffffffffe000000000000033aa61bfffc00,0xc03000600018030180c046021182211084210),(0x0,0x0)]
def g213C : List ColumnInfo := [(0,64,145,4,5),(64,0,149,0,5),(1,0,212,0,4),(4,0,145,0,4),(4,64,145,0,4),(16,0,197,0,4)]
def g213A : List (List Nat) := [[],[64]]
def g213D4 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x5bd4940
def g213D5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x20128240d140ff40fd40fd20
def g213H5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x70
def g213D6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x163440df
def g213H6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x685be532a
def g213L : Nat → Packing
  | 4 => (1,2,3,0,0,0,0,g213D4)
  | 5 => (3,1,3,0,0,5,0,g213D5)
  | 6 => (1,0,3,0,0,0,0,g213D6)
  | _ => emptyPacking
def g213I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 2 0 4 0 0 g213H5
  | 6 => lookupWord 1 5 0 7 2 1 g213H6
  | _ => fun _ => none
def g213 : Forest := ⟨213,6,fun i => g213Y[i]?.getD (0,0),g213C,g213A,g213L,g213I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g213P4_0 : block g213 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g213B4 : block g213 4 0 1=true := g213P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g213P5_0 : block g213 5 0 3=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g213B5 : block g213 5 0 3=true := g213P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g213P6_0 : block g213 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g213B6 : block g213 6 0 1=true := g213P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g213T : checkedTables g213 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g213 0 0 0 = true)
  · exact (rfl : block g213 1 0 0 = true)
  · exact (rfl : block g213 2 0 0 = true)
  · exact (rfl : block g213 3 0 0 = true)
  · exact g213B4
  · exact g213B5
  · exact g213B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g213G : graphValid g213 (boundsBefore KS179) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowS213 : Lower true (varsX 213) (graphGoal 213) 7 := lower_forest (g:=g213) (i:=0) (hints:=33555972) (before_sound KS179 VS179) g213G g213T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KS213 := extendKnown KS179 7 [(403,[33,129,97]),(419,[16,32,112,84,96,134]),(433,[130,50,83,101]),(434,[16,114,50,84,67,100,134])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VS213 : Known true KS213 := extend_ok (m:=213) VS179 lowS213 (by decide +kernel)
def g391Y : Array (Bits × Bits) := #[(0x7ff001ff80ffc07ff003ff80fffff49a2b0007,0x42a8d4251a148b42a9aa251a948a64922b5b6d),(0x7ffffe0000fffffffffc0000ffc069da9401c0,0x14c298b62c591214c130b62c191349da8436db),(0x7fffffffff00007fffffffff00000ef10e8e38,0x700e038301e1c0701c038301e1c04d10c9249),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x800000000000007fffffffffffff99af6d703f,0x180300c0406020180200c0002000192c002492),(0xffffffffffffff800000000000006754f2ffc0,0x600c0100008000600c030040c0202200724924)]
def g391C : List ColumnInfo := [(1,0,390,0,5)]
def g391A : List (List Nat) := [[],[16,135]]
def g391D5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x3f
def g391L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,g391D5)
  | _ => emptyPacking
def g391I (_ _ : Nat) : Option (Nat × Nat) := none
def g391 : Forest := ⟨391,5,fun i => g391Y[i]?.getD (0,0),g391C,g391A,g391L,g391I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g391P5_0 : block g391 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g391B5 : block g391 5 0 1=true := g391P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g391T : checkedTables g391 5 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g391 0 0 0 = true)
  · exact (rfl : block g391 1 0 0 = true)
  · exact (rfl : block g391 2 0 0 = true)
  · exact (rfl : block g391 3 0 0 = true)
  · exact (rfl : block g391 4 0 0 = true)
  · exact g391B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g391G : graphValid g391 (boundsBefore KS213) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowS391 : Lower true (varsX 391) (graphGoal 391) 6 := lower_forest (g:=g391) (i:=0) (hints:=4294969223) (before_sound KS213 VS213) g391G g391T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KS391 := extendKnown KS213 6 [(436,[64,81,48,49])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VS391 : Known true KS391 := extend_ok (m:=391) VS213 lowS391 (by decide +kernel)
def g405Y : Array (Bits × Bits) := #[(0xffc03fffc7fe00ffc3fe1ffff9476800003ff,0x242a2828092148a4289044084314349294a529),(0x0,0x0),(0xffffc03fffffff0003ffe1fe271f141f07c00,0x40b030b0500580c0b10280408871f006318c63),(0x0,0x0),(0xffffffc007fffffffc0001ffdea67000f801f,0x88c040c262461108c023089100ea4325294a52),(0x0,0x0),(0x0,0x0),(0xf0000000007fffffffffffe0005f08be0fffe0,0x1008100800802010004000200000008421084),(0xffffffffff8000000000000003289bfff00000,0xe03020300701c0e0238111c13080bf18c6318)]
def g405C : List ColumnInfo := [(1,0,404,0,5),(4,0,401,0,5),(16,0,389,0,5),(256,0,149,0,5),(17,0,388,0,4),(260,0,145,0,4)]
def g405A : List (List Nat) := [[],[130],[32,132],[32,64,128],[64],[64,130],[128,32,66],[128,66]]
def g405D4 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x31823f64547309bd89534426d6214d10
def g405D5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x182204090020001882188201141080db8ae4c8d018160c02faa3987bd4930bfa8a61fb304c2fea6885f94d10bea9a217c53443f260885bd4930
def g405H5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x68c1a9000000c2000000f000000000
def g405D6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x21d1080c864202aa59d1081101300ff30fd30fd10
def g405H6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x32081000c500000002c2e6449b5c40a1b6131e5100000c0d936500000000a1000000000800
def g405D7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x163440df
def g405H7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xd5405a00398000054bb562a4ac40159b20000000208012
def g405L : Nat → Packing
  | 4 => (3,3,3,0,0,4,0,g405D4)
  | 5 => (10,2,3,0,0,7,0,g405D5)
  | 6 => (3,1,3,0,0,7,0,g405D6)
  | 7 => (1,0,3,0,0,0,0,g405D7)
  | _ => emptyPacking
def g405I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 19 0 8 2 2 g405H5
  | 6 => lookupWord 4 29 4 10 4 2 g405H6
  | 7 => lookupWord 3 19 5 9 2 3 g405H7
  | _ => fun _ => none
def g405 : Forest := ⟨405,7,fun i => g405Y[i]?.getD (0,0),g405C,g405A,g405L,g405I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g405P4_0 : block g405 4 0 3=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g405B4 : block g405 4 0 3=true := g405P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g405P5_0 : block g405 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g405P5_1 : block g405 5 1 9=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g405B5 : block g405 5 0 10=true := (@block_merge g405 5 0 1 9 g405P5_0 g405P5_1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g405P6_0 : block g405 6 0 3=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g405B6 : block g405 6 0 3=true := g405P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g405P7_0 : block g405 7 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g405B7 : block g405 7 0 1=true := g405P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g405T : checkedTables g405 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g405 0 0 0 = true)
  · exact (rfl : block g405 1 0 0 = true)
  · exact (rfl : block g405 2 0 0 = true)
  · exact (rfl : block g405 3 0 0 = true)
  · exact g405B4
  · exact g405B5
  · exact g405B6
  · exact g405B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g405G : graphValid g405 (boundsBefore KS391) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowS405 : Lower true (varsX 405) (graphGoal 405) 8 := lower_forest (g:=g405) (i:=0) (hints:=8589936388) (before_sound KS391 VS391) g405G g405T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KS405 := extendKnown KS391 8 [(405,[]),(422,[16,84,135])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VS405 : Known true KS405 := extend_ok (m:=405) VS391 lowS405 (by decide +kernel)
def g183Y : Array (Bits × Bits) := #[(0x3fffffffffffffffffb94049bf55b28003f03f,0x814150284a050a4214b8404097451205145145),(0xfffff80000ffffe00036bb4666c1ae40000fc0,0x100a62036c404c80663633462401ae134d34d3),(0x3fffffffff00000000066c749abd8b00fc0000,0x59380b270166f04b8026c449abd8b0f3cf3cf),(0x0,0x0),(0x3fffffffffffffffff58b1cca8bed4bf00003f,0x61c00c380187008c000a10c28bac48a28a28a),(0xc0000000000000000048af2b5fcc4a40000fc0,0x27e004fc009f800f00488c295bcc406cb2cb2c),(0x0,0x0),(0xe754b7112b657ffff000,0x3800070000e00010004510b300002070c30c30),(0x0,0x0)]
def g183C : List ColumnInfo := [(0,2,149,32,6)]
def g183A : List (List Nat) := [[],[81],[64],[64,81]]
def g183D6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x7f
def g183L : Nat → Packing
  | 6 => (1,0,1,0,0,0,0,g183D6)
  | _ => emptyPacking
def g183I (_ _ : Nat) : Option (Nat × Nat) := none
def g183 : Forest := ⟨183,6,fun i => g183Y[i]?.getD (0,0),g183C,g183A,g183L,g183I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g183P6_0 : block g183 6 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g183B6 : block g183 6 0 1=true := g183P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g183T : checkedTables g183 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g183 0 0 0 = true)
  · exact (rfl : block g183 1 0 0 = true)
  · exact (rfl : block g183 2 0 0 = true)
  · exact (rfl : block g183 3 0 0 = true)
  · exact (rfl : block g183 4 0 0 = true)
  · exact (rfl : block g183 5 0 0 = true)
  · exact g183B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g183G : graphValid g183 (boundsBefore KS405) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowS183 : Lower true (varsX 183) (graphGoal 183) 7 := lower_forest (g:=g183) (i:=0) (hints:=1050452) (before_sound KS405 VS405) g183G g183T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KS183 := extendKnown KS405 7 [(183,[]),(311,[16,84,135])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VS183 : Known true KS183 := extend_ok (m:=183) VS405 lowS183 (by decide +kernel)
def g407Y : Array (Bits × Bits) := #[(0xfffffffffffffffffec91513674a78000003ff,0x481440548129029028c914126242525294a529),(0xfc00fffe0003fff801f405383e999001f00000,0x90a612982db05320cdf005383e9881ce739ce7),(0xfffffffc00000039c4f6930e803e007c00,0xe13804e009c01bc1701184b6130e80c6318c63),(0x0,0x0),(0xfffffffffffffe428bea0bc9e8000f801f,0x1c087010e021c0180008be80909aca5294a52),(0x0,0x0),(0x0,0x0),(0xffff0000000000000022fa117cb687c00fffe0,0x1800300060020022600104900108421084),(0x19d26ecc07137fff00000,0x200e001c0038004000c0240c06136318c6318)]
def g407C : List ColumnInfo := [(2,0,405,0,8)]
def g407A : List (List Nat) := [[],[64]]
def g407D8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x7f
def g407L : Nat → Packing
  | 8 => (1,0,1,0,0,0,0,g407D8)
  | _ => emptyPacking
def g407I (_ _ : Nat) : Option (Nat × Nat) := none
def g407 : Forest := ⟨407,8,fun i => g407Y[i]?.getD (0,0),g407C,g407A,g407L,g407I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g407P8_0 : block g407 8 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g407B8 : block g407 8 0 1=true := g407P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g407T : checkedTables g407 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g407 0 0 0 = true)
  · exact (rfl : block g407 1 0 0 = true)
  · exact (rfl : block g407 2 0 0 = true)
  · exact (rfl : block g407 3 0 0 = true)
  · exact (rfl : block g407 4 0 0 = true)
  · exact (rfl : block g407 5 0 0 = true)
  · exact (rfl : block g407 6 0 0 = true)
  · exact (rfl : block g407 7 0 0 = true)
  · exact g407B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g407G : graphValid g407 (boundsBefore KS183) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowS407 : Lower true (varsX 407) (graphGoal 407) 9 := lower_forest (g:=g407) (i:=0) (hints:=4294969220) (before_sound KS183 VS183) g407G g407T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KS407 := extendKnown KS183 9 [(407,[]),(423,[16,84,135]),(437,[81,49]),(438,[16,64,48,83,135])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VS407 : Known true KS407 := extend_ok (m:=407) VS183 lowS407 (by decide +kernel)
def g435Y : Array (Bits × Bits) := #[(0x7fffffe0ffffc92a21b355e900000000ff00ff,0x2029004241100822019145e845454545454545),(0x8003fffffff81a51a0dee1520000ff0000ff00,0x4b0228008209a5120ce404013131313131313),(0x0,0x0),(0x0,0x0),(0xfffc0000ffffefe3ba248209000000ff0000ff,0x40c20b0482402701b82482018a8a8a8a8a8a8a),(0xffffffff000020925965f93400ff000000ff00,0x9004c00138120825121b9102c2c2c2c2c2c2c),(0x0,0x0),(0x24dd460b16d0ff0000ffff0000,0xe0070081c0200d8460a101030303030303030),(0x1324dd980e26ffffff00000000,0x70038010e004012488100626c0c0c0c0c0c0c0)]
def g435C : List ColumnInfo := [(1,0,434,0,7),(2,0,433,0,7),(16,0,419,0,7),(32,0,403,0,7),(0,1,290,144,6),(0,2,145,288,6),(0,16,290,129,6),(0,32,145,258,6),(128,0,307,0,6),(256,0,179,0,6),(1,16,290,128,5),(2,32,145,256,5),(16,1,290,128,5),(17,0,418,0,5),(128,1,290,16,5),(128,16,290,1,5),(256,2,145,32,5),(256,32,145,2,5),(129,0,290,0,4),(129,16,290,0,4)]
def g435A : List (List Nat) := [[],[81],[16,84,135],[16,64,80,135],[64],[64,81],[80,16,65,135],[80,65,135]]
def g435D5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x333dcf6254540
def g435D6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x2841a307001a9c3809faeda8e81bbd8b5150377b12a2a05df7354520
def g435H6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x40
def g435D7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x2844300424142424200624142238428d0a110c014685088e00a3428443005224078e12203860a10182028001f284070c14203c4080c0006101e38488c78b0e02480c1220263c585012407090d8d1618040e901b1a2c3007a726c90e1a7c5c8564ff2e8750dc00ffd4740ffd4540ff54540ffd4520ff54520ff4c520bf59654bf59740cfd5254be58054bb58b50bbd8940
def g435H7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x4800009100a0050000d3000000000000d20000000000d95600000000000000
def g435D8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x8a079c49038c28918710508300092281e71240e30a2461c41420c002481e71240e30a2461c41420c002281c51240e30a2461c414208082281c51240e30a2461c414208089449038c28918710508201c99c51240e30a2461c414208081c69240e30a24618508201c81c59449038c28918710408086615f4a4f63009318033001fe54feaa7f153fea1fd50ffa07f503fa41fd10
def g435H8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x66c0078762e0000000010600080fc20000000050b001b8800000e300000000000000000000c4e00382000000000000005100000000000000384800000a6400000000e0800000000000000005446a042800001a6b0000000000000000000000002aa0000033520ae0c0000000000000000000000000c
def g435D9 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1882013f
def g435H9 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x20180000000000000000000001e3001a400000000000000000000000005c20000000000000000000000fc96c0000004424a391aa4d0200000000000000000000000018100034521c440000003100000000000000000000003e180000000042000b0a00000286cca0000000054a0000000058a00000262000000007d0000000000000000004021
def g435L : Nat → Packing
  | 5 => (1,4,5,0,0,0,0,g435D5)
  | 6 => (4,3,5,0,0,6,0,g435D6)
  | 7 => (12,2,5,0,0,10,0,g435D7)
  | 8 => (9,1,5,0,0,10,0,g435D8)
  | 9 => (1,0,5,0,0,0,0,g435D9)
  | _ => emptyPacking
def g435I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 2 0 4 0 0 g435H6
  | 7 => lookupWord 2 31 0 8 2 2 g435H7
  | 8 => lookupWord 6 89 1 11 4 3 g435H8
  | 9 => lookupWord 6 97 3 11 4 3 g435H9
  | _ => fun _ => none
def g435 : Forest := ⟨435,9,fun i => g435Y[i]?.getD (0,0),g435C,g435A,g435L,g435I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g435P5_0 : block g435 5 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g435B5 : block g435 5 0 1=true := g435P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g435P6_0 : block g435 6 0 4=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g435B6 : block g435 6 0 4=true := g435P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g435P7_0 : block g435 7 0 4=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g435P7_4 : block g435 7 4 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g435P7_6 : block g435 7 6 6=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g435B7 : block g435 7 0 12=true := (@block_merge g435 7 0 4 8 g435P7_0 (@block_merge g435 7 4 2 6 g435P7_4 g435P7_6))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g435P8_0 : block g435 8 0 9=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g435B8 : block g435 8 0 9=true := g435P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g435P9_0 : block g435 9 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g435B9 : block g435 9 0 1=true := g435P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g435T : checkedTables g435 9 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g435 0 0 0 = true)
  · exact (rfl : block g435 1 0 0 = true)
  · exact (rfl : block g435 2 0 0 = true)
  · exact (rfl : block g435 3 0 0 = true)
  · exact (rfl : block g435 4 0 0 = true)
  · exact g435B5
  · exact g435B6
  · exact g435B7
  · exact g435B8
  · exact g435B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g435G : graphValid g435 (boundsBefore KS407) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowS435 : Lower true (varsX 435) (graphGoal 435) 10 := lower_forest (g:=g435) (i:=0) (hints:=4296015956) (before_sound KS407 VS407) g435G g435T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KS435 := extendKnown KS407 10 [(435,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VS435 : Known true KS435 := extend_ok (m:=435) VS407 lowS435 (by decide +kernel)
def g439Y : Array (Bits × Bits) := #[(0xc2a879850ea6986b3c41000000000000ff00ff,0x400878850c86906a3441454545454545454545),(0x5897c212c24b0a6ed515000000ff000000ff00,0x5097c01042490a6e4405131313131313131313),(0xe546fd9cf00e2c4200d40000ff0000ff000000,0xc444f59cd00e0c4200d40f0f0f0f0f0f0f0f0f),(0x0,0x0),(0xb671d1560780cf300b3400000000ff000000ff,0xb671811203004c100b348a8a8a8a8a8a8a8a8a),(0x12d231d851215cdd3f200ff0000000000ff00,0x128230d8512058191f02c2c2c2c2c2c2c2c2c),(0x0,0x0),(0x4592a2e11878631520a9ff000000ffffff0000,0x1820260007023050000303030303030303030),(0x3a480c2a6955d482064effffffff0000000000,0x2a0008022800d000020ac0c0c0c0c0c0c0c0c0)]
def g439C : List ColumnInfo := [(4,0,435,0,10),(1,0,438,0,9),(2,0,437,0,9),(16,0,423,0,9),(32,0,407,0,9),(17,0,422,0,8),(34,0,405,0,8),(0,1,294,144,7),(0,2,149,288,7),(0,16,294,129,7),(0,32,149,258,7),(5,0,434,0,7),(6,0,433,0,7),(128,0,311,0,7),(256,0,183,0,7),(1,16,294,128,6),(3,0,436,0,6),(4,1,290,144,6),(16,1,294,128,6),(32,2,149,256,6),(128,1,294,16,6),(128,16,294,1,6),(132,0,307,0,6),(256,2,149,32,6),(256,32,149,2,6),(260,0,179,0,6),(129,16,294,0,5),(132,1,290,16,5),(258,32,149,0,5)]
def g439A : List (List Nat) := [[],[81],[16,84,135],[16,64,80,135],[64],[64,81],[80,16,65,135],[80,65,135]]
def g439D5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1863e939360580dc965
def g439D6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x6801000000000000000b901000e881000000d881d881f0c1c6c0b0aaa49e98928c86807a74645e5848423c3630201000c73e4f81603725971cf9360580dc965cd3e17936037259719f94e0d715c165c6be53825c57059656ea91d78259560a6be9191e0976d431af94e09815db50a3b688865d971d421efa266287d875087be8997a1951d428eda22197654750967e9191d97735431e79260587d855087be8998ddb615429cfa261773d85509d668c956036154299fa461b7354550a73e8986dcd5154299da421b7354550a7368886dcd51542b59a32176158150ad668c85585605423eba266361d4150
def g439H6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xf0
def g439D7 (j : Nat) : Nat := if 2 ≤ j then 0 else (if j<1 then 0xbc7b679e78f78077175974a73b72370b6f36ed6de6cf6c06b16a269368466c65463c6366276186005f15eb5dc5cd5be58b58557656755854953a52251c50d4fe4ef4d74bf4b94b349b44d43e42f4204083f93ea3c93b13ab39338436335434532430c2b529d29727625522b2131f21da1a718f15c13b0ff0f90d80b708d087081057000f37c930fb2ccbb6f9261f65996bdb2dc06e4b2e7be0780dc965cf7c0b01b92cb9ed8160372597cdf0dc2ee4b2f9be1665dc965f37b2ccbb92cbb6f85e0372596edf2ac06e4b2edbe1580dc965be7c9b01b92cbb5f65e0d705976decbc12e0b2ef3e0f725c165cefc1ee2b82cb9ef82dc5705973bf06b8ae0b2e7be09715c165eb7c970eb28cbd6f97e0965197adf0fc12ca32e7be4b8759465cf7cbf04b28cb9ef87e09651973df30b2ae432f7ae49655c065ee7c92cab9ec1cec97e0965583cdf2bc12cab05afe518159560b77c9302b2ac157e981d5655833d92fc12cab075bdd78259560eb63af04b2ac1e6f65e09655833df24c2ee2b067b6488754560f37c92caa8ac19ef9261676d433df24c3ceda84efe51819db50cf7caf04bb6a19ed95e0976d433df23c12eda867b647825db50cf7c1702bb6a15bf9460576d42bdf24c0aeda867be09815db50cf7cbf04bb6a19ef87e0976d433df24c3ecba857be4987d9750af7c92edb2ea13bf9460765d433df2fc12cba867be1f82597509deca10cb8ea13ed9221971d431ff0cbb2e3a863f219765c750af7c92ecb8ea11fd98a1f61d433df24c3ec3a857be4987d87508ffcbb0bb0ea13ef9261761d423fb2f432a3a84ef65086547509f6c910ca8ea18ff865d951d431f90cbb2a3a857be4976547509dfca303b2aa15dd91d9773543abecab2ee6a8773e4965dcd50aefc8acbb9aa15df9361f61542bdf24c3ec2a867d60587d85508fecc6edb0aa11ff985db61542bbf26bb6c2a857be4976d85509f7c930bb0aa19dd85dcf61542ef12ac06c2a86fc60580d8550cefc2ee6b0aa1b9f84dcd6154277f28c32a2a84fbe4986545509deca10ca8aa13ed92219515433bf0db9aa2a8677a1b7354550ceec36e6a8aa19dc86dcd51543abacbb9aa2a86de2176158150dbc42ac2b02a17bb94585605437d724c36a0a84fe66361d4150bddca2c3a82a15ed92a1d654433dd2fc12ca8867b25f8259510cf743f04b2a219ec87e09654438df24c3ecb32d9be4987d96659b7c930fb2ccb5cf93603725974df0dc2ee4b2f1bdd665dc965ce7c1ee4b82cb96f92e1d651972df0fc12ca32e5be61655c8658f7cc2cab90cbceb9259570196bd724b2ae032f33e49655cf60ae7c92cab9ec156d921d5655823df24c2ee2b047b64887545608f7c930b3b6a11ef9261e76d423df24c3ecba847be4987d8750ae7c92cbb9aa199f84dcd615427d724c36a0a84d664c8558150 else 0x30030d7005a004c2080623085a0902803d02802c0025426a8032a08022d2802d0021470041430056004002c96008196490870e86b80346d80c01a36c0143a1ae000096030048e46d8000243a1a200e1c600a1c6008a36009288d3007c1078208341b002942004984b84000018a00028a020004000f0410b024b04072388203c00980001032c8104410382000a1a0c341e0828e6084c10782083b82102000123c0e1000004000e8810083c104000f0410770420400024781c2038609901269802300206881d102e40412030100400281a207440f0c15003a205c9c3080a183c307860f0f82170f8210002914010491a0903a9144815010a206c40d8818770c2e183c3078781c006400004025d82104414ba51821b80170030e86b8032a68022c15caa5427137412050124e2684043a1ae00d1c8db0070e86e8140243740143a1ae00e1ae00a31178a439c02c39c010581be3e0b80584793441c5e29e4f1e8b8230107f1f04386f8f821f93c7a2e08800107c2f0f0220a60fe642f91c7e2c0f809bf1bd9bcabbbbb5b9db7cb64b55b34b1cb04af5addac5ab6ab0aaaa92a71a50a2fa179ed9d59ab98a97295a9429219129038f48e58cd8b58af8a088887986a85b84c83d82e82881080a7fb7e37cb7)
def g439H7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x25c00615a1804001542d1600305000a0e3580000000188400000000c5889000000000006930000000008dfa610348800c6cc13c2800645e3c007c151c0000020978f65080237f1000000506001a04c180032900900
def g439D8 (j : Nat) : Nat := if 3 ≤ j then 0 else (if j<1 then 0x63c2c1e026c4cb0bac00af2aba4adfab40ac0aaccaabaa50a86a9d4a67a968a4aa904a33a8a8a1ca84ca0ba8009f2a79c9d9a7309c6a6fc9b3a69898ca5fc97ba5d096ea594961a52893aa4c4921a440902a3e48f3a3a88e6a37c8d3a3208bca2cc8a5a25888ca1fc863a148844a0dc82ba088816a0247ff9f987c49e9c7899db87529cec72f9c5870a9bbc6dd9b186ae9a44685996063e986c5f797905ca96a459b961056e955c53b94804fe938c4c592a049492144639108428902c3f18f703c68ebc3978df836e8d5433d8c983128bdc2dd8b082b08a6427d897824488bc21d88001ea87541bf86a019485fc16b855813a849410d83d80e0832c0b5828808c81e4065814003a809c0138000fef85dc965fee65dc965fef80dc965fed80dc965f7f65dc165fef72dc165dff71dc165f7f655c165fef725c165dff715c165dfd715c165dff8759465fef8259465fef8259760eff8159560efd8159560fef8259560bfd819db50dff815db50dfd815db50dfe765db50fef825db50bff815db50dfd87d9750dfd76d9750bfd81d9750dff8759750f7f6559750fef8259750bff8159750bff865c750bfc865c750dfd765c750dfe87d8750dfd87d8750bfd85d8750bff8654750bfe8654750bfc8654750dfd7654750f7d6554750bfd81d9550f7f6559550fef8259550bff8159550dfe87d8550dfd87d8550dff76d8550dfd76d8550bfd85d8550fdf73d8550ff980d8550bff8558550fdf7358550bff8654550bfe8654550bfd8654550bfc8654550f7d6554550ffb6158150ff96158150ffb61d4150ff961d4150dfe8759510dfc8759510fef8259510def825da65e7d87d9665b7d87d9665e7f6599565def85dc965def80dc965ded80dc965f6f85dc965def75dc965eee65dc965def72dc165bdf835c165bef825c165def725c165d7f8759465f6f82594659ff8759465bef8259465ded655c865df9655c065eef8259760bef8259760ddd655cf60eef8259560d7f7559560d7c7559560e7f6559560bef82595609fd85dc5609fc8754560e7d65545609fd859db509fd879db50def825db50bef825db509fd87d97509ff8759750bef82597509fd87d8750bef8259550ddf65dcd50ddd65dcd50ddf73d8550ddf7358550ddf7354550bf986d41509fd861d510bef8259510bf78558510df775585109ef825da659ed829d665c7d87d96659df835c265c7e769946597f8759465d6d655c865d6e755c865de9729c065df2719c065cf9655c065cfa765c065dda735c065dd9735c065de9725c065df2715c065df1715c065c7e75d9760cdf655cf60cdd655cf609dd831d5609ed821d5609f5811d5609ef825db509dd831db509ed821db509f5811db509dd839d9509df835d9509ef825d9509f5811d9509f88758150b7885581509bd849d5109df835d510 else (if j<2 then 0xa5e5308804989795948e8de4e3e2e1600030605c5450383791938d8f898b858781810181715140e0d2a28e4e3e2e1e06038605c54503837130f0b0783028180e58571655544e4d64636261a02035615d513934ad95938d8d898680d5a5857546564636261a0202d615d3a80805585755544e4d64636261a02031555136808059897948e8da5a4e3a3a2a160203450a497918f8a878081b9a14a5e4e3e2a16020002e6a625e50ac2e96928e8a84b181715140e0d4a48e4e3e2e1e0603a625e3a35805181715140e0d0a090807e404e303e202e101e04020005a625e56523a37130f0b058100c18171615140e0de464e363e262e161a02044605c5438361c1f91938d8f898a8487818119a9897948e8dc5c160266a625e3a3717130f0b058100c1817140e0985e464a323e262c141e060425237178f05806140d4a4807c5c1e0a040002c605c38352923178f0780a1817140e0dc5e3c1e0a0602e625e523a352f17138f0f0b0580d1708a6c5e40403a202c101e000345c50201e9b1790138c0e880b04078001017140e0da8c7a6c5e4e3a2c1e034605c34282314100c0b0504078000e0d0a0807c504e30302c14101e0003a361f17938f8b058000987c5e4e3e2c1601c3428211c1f14138c0c0b04078100800100d0a084707c504e30302c101e040200042625e3a3717138f0f0b058100c0807a6c5e404e303a202c101e0003a6a625e523a352f17130f0b04c14124d896462c141e0602850493625918b05078180a128d09a6e4a4a2c181e0a02d484a34269a928b06078280b14128d49a6e4a4a2c181e0a030341e170e04078070d07c6c50403c202c101e000325e523a371b1793130f0b04b17540886c5248202c101e02c38211e1b16920b07809989795948e8de6e5e4e3e2e1603458545038379b97938f8b8580c181715140ee6e5e4e3e2e1e060345234279b938a8780815140e0de6e5e4e3e2e1e02c605c545038379b97938f8b8780d1918171615140e0de6e5e4e3e2e1a03c58545038379b97938f8b8680c160e0de6a5e4e3e2a16028359a97938d8a8780818171514920e0d87e6e4e3e2a1e038545038379b938f8a8780a120e0de625e463e2a1e028545038379b918f8a8780a1615140e0de6e4e3e2a1602c5038359b938d8a878091715140e0de4e362a1e02838379b17938f8b0780914920e89e685e4e2c1e028605c52483a279a17928f8b0780d0d0987e645e463e2c1e02858352e1f9b17938f8b0580b17130d0887c5e4e362c1e02e352e1f9b17938f8b0580a0e0d09e645e463e2c1e0284438379b17938f8b0580a0e0d08c5e4e362c1e0245038279917918f8b0780a1409e645e463e2c1e02450479b17938f8b05809130e0887c5e4e362c1e02838341f9a17938f8a0780a0d07e685e4e3e281e02434291b15938f0b078091409c645e4 else 0x164e4da020153936003544d2b61a01569518d8680806140da1601252368580408072202a121011c68528e8486818079a942ba3a16018428e803080764a32202a12101a0602c38378181008068e8dc4c3c2c14020226a523b0f04806170e4762c14118711d918b0505807948dc12010209188880b046086202e0102191880b8180607c1a020121f0480308622202c114351f0505008060d47c1014014209108880b0460d47c141e02018348028dc1200c2108880b0451707a22202c1183c38341c908e88880b040480c08a22202c1601a88107a2400f04802171007c113041100f0e0d07242322c101202c403422880b050070d8882221040201c930d0b0471a140e0dc3814120226a523b0f04806100807c3101e8821a43a2401288143a2400c1f0f04048051a0743a28114201f0e8804507c3c10110691c1e910e8861707c3822202011c1f0f040440724c3c1012018683c341c930c8e08880b040480d1a1488c382228141204039201f0d8861a0e0764c362181f0d8a0600564c38180105c501f81005171407c241e01))
def g439H8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x382462f55203823703ec4595a1c0000000000170340004867428081a783ed00400e4c622cbde0430000000243a800040b579b0000602c0000807ac30200974d698ab00a985e010c009e80e115ce0ef59c3402a20d709c00014130a2de0c6088c000187e0001814c000686a0001202b406b81fe44441ac044804b7062a190d107a2b4115c1771365279f2b60000c27d065e24660020312840206dc21f4b1e0760000000000000000001a918000083a0000800c321f08000000003441ae6620a54081b1fd0540000000181a28743904a08a837a8660001411f438a825b0aea0ec00068459c1c614342cc04880dd616183e000000000003c0b000094f02172845b47044554490caef82b2ca44560c2d8000f0238042522000000728494814e8813018e5e193300000c1a0000000583554480618000187330f0c10509de179c30e0002c9f000080f200004250000b50e000301ef02380e0c87e42ad033000098cc000000040254009094305f000000037164a31e45c00000000000f4e1c0680006068f06ec8fc0000000a09840a1c04002e805400000000000e00f8124236fa52900200004074888000c000203d001d9104000000000008296e2100001017000058b5c108000b0368113442d019301e000243f86460001c90fc3698145061e0f00004934c02618ae01c704d20ac61b3028800070300003417a12700000000000000000006109f358000d0f720cb43080000001e02f49a8000e41da0fc000000034660002f22682d0a9401000d81061e240150205e210780a17421d09b0a600000c2400f0800002122c58102101820e100042045780
def g439D9 (j : Nat) : Nat := if 2 ≤ j then 0 else (if j<1 then 0x68a12203e6cb90263078816103810005cc172a5070dcd97263c58704040010305ca941c37365c98f161c06982e58a941c37365c98f1614000f305c70dcc942e4c7890e030c17283868a101f325c813183c409081c0014305ca941c37364c789081c06982e3868a101f345c813183c40a081c0013305ca0e1a28407cd17204c60f102820700050a0e1b1f345c98f1410380c3460b941c363e68b931e2820701e60b94243c707cd91183c50701c70b941c344074d17204c60d10282070004ca0d14203e68b90263078814103800223868a101f345c813183c40a081c00113460b941c363e68b931e2820701e506c7cd17263c5040e02cb941a203a68b902630688141038002260b941c1f305c98d1e203820200080d14203e68b902630788141c000f305c70d14203e68b90263078814103800263868a101f345c813183c40a081c00111c345080f9a2e4098c1e2050700040b8e1a203a68b902630688141038002268a0d14203e68b90263078814103800245070a101f345c813183c40a0e00081a2828407cd17204c60f102838002068c17283868a101f345c813183c40a081c0015345090f0f9b223078a0e030b941c203a68b902630688141038002260b941c343e60b931c3c40701c343e60b931c3c4070404000d28407078d17204c60e102820700040b8e1a203c68b90263070a0e00079728407080f1a2e4098c1c28380020386878d17204c60e10282070003cbd41c223868b9126305040e038a0e0f182e4c70e1020380c305ca941c37365c98f161c06e6cb931e2c2807305cb1528386e6cb931e2c280e305ca921c343e6c98f121c06982e5090e139b223c50701850909cd911e2838098dca2f589721d8858a0c980c1f907bdde887785d727429c8d7025b9a6c3da7d67c9967637184a5ee171f59e15df55f94f351d94154f5d3614ae9244478d1744469088409cf9c3c28eb03904dd93538cd13150be52e48b152a7ca30269492822c88351ec473b1b1462c174855513b448c10583a70cc42c20968200067c168040009f0114000ffecb32ffd71997ff32acbffdc165ffae0b2ffd65197feb2ec1ffd9560ffacab07ff71583fea8ac1ff9db50ffaeda87ff65d43feb2ea1ff5c750ffec3a87fd51d43ffb2aa1ff59550ffec2a87fd61543fea8aa1ff59510bfaed32dfe75997bfb2ccb7f5c665bfae132efe65597f7b92cb7fdc165bfcea32f7e65197beb28cbfb5c865ff4e032dfd70197fcb80cb7f9d760bfaebb06ff65d837eb2ec1f75cf60bfae3b05ff75582fe3aac1bfd9560dfacab05ff71583fdb02c17fddb50bfceda85fd76d42fe3b6a17f5c750bfeeca85fe76542febb2a17f1d950fbee6a85ff71543fcb02a1fed4150bfeea885fe75442febaa217f1d510feac2887f9604433fb2ccb7bdc965bdae432df970196eeb9ec177dcd50 else 0x182e54a0e1b92224c70d1e2848b0c1438202054b9528354084d912634688161438102260b9528386e488931c3478a122c3050e080815305ca0e1a9c3a5c8931a3c489081c08123460b940e97224c68f122420702040c172a5070dc911263868f14245860a1c10102a68c1728386c5c911263868f14245040e0808153460b941c343c5c911263868f14245040e080816305ca0e1a1e2e488931c3478a122820704040a97281d345c8931a3440a081c080f2e5070d50223874d17244498e1a3440a081c10102e60b8d0f17224c68f12282070203c70d0f17224c68f122820702038c171b1e2c4498e1a3848a081c10102260b8e1b1e2c4498e1a3848a081c1010245c6874d17224c68d10282070203c70d101d345c911263868d10282070404099720344474d17244498e1a3440a081c10102868c1728386878b11243470914103820204cd182e5070d0f16224868e12282070404099a1c344074d17244490d1a205040e080813386870d111c3a68b112434688141038202050d1728344074d17244490d1a205040e0808142e5080e1a203c68b92224868e102820704040a982e54a0e1a284880f9b2e4098c1e205840e0400172a5070d1424407cd97204c60f102c20702000a982e54a0e1b9b2e4c78b0e034b9528344880e9b2e4098c1a205840e0009941a28407cc97204c60f102420700044a941b9b2e4c78b0e0808001b9b2e4c78b0a00041414203e64b902630788121038002060b952838)
def g439H9 (j : Nat) : Nat := if 2 ≤ j then 0 else (if j<1 then 0xb026aa4bd0a686d0000410583dde8d587a000072e8000000179aef44416a32260000000465ecce2e14c00000330000a5c5440b81c8255a0dcb36b803000181f4316c67b000148bed38467290a241980000a86b438e5e4000000000015a1b03af18454f4ba4ac04701e72b0861dc3b00000000000000028400000c8e401b396100000000000028d0000000240bfe39110624200ad048e0000d24c000125a000189f442c8000ac8124d80000000000161e0000000064b000016238864a0b77138494b87714b6b97c20b0e6c000071e8c3400000001a117c010e18000000000000e600000e0a248600005063221d52cda7200000002217800002500000000582a000169ec52280006077e9c5d0980000001a1360c180009123f1040000000000000000000000000000021351a8900002a50000180a00000002c41240300000003825000000000000126e026847fa211431702e7064c93f549b24120172157e0d000034e8e55543f000000000000c0a901f000181180007e9400000001848480c000029709277a1764c7680d4c0000000000001327d0040001c095c1e881dc24a0002543d0120000a2480000000000109a00000000000000000005095e0f8a01c0004e79b4c578524240000007d52240004a200001b55581e385f00000000c180000632060808c678880001e9317472295e00bf0fca92800000000002b23800000000000b438000d4c2c1c40000000147ac060000000000005218000484cf0ca0000b37481a00000000000563d000000000007e6830740003400f07470202044000715e50b800000003c39f31000038ae780e000059a800061670001c1cc0000a1aa0474a3b02e800071180000000000034ca000051480008084000270d0000dccd40b10372080d2dd7a3f13cfa47211379d40000000b04e0003410800000000001c1f881b000161c00001355bcb800000003a3a60120000000185e0000b1ac00000000001805031d000000000001d9280003c260000000000000000000000000084bb7a24000542d000049ad7317a1b3480a9b8000063f0001e978047383424cd40580002673051e000000000002c820000c21b2180001c228000786720d2a11c0003976e070000000078850000fa4c0003a2d42da0000148800094da0001f01b849c923c162f0bf096c0d68183cc28000cc9c81fccbedc940000e16b8308000d11baa5b00300000000000062548190000000000031121232113c416d87a30a00001525280d60a939c0000125030e5823e4350000805279e8000000070af8001427f05602cd608b732c26c005f897ff48e88b44970981043200fe8800252c31e84b14f0000460440c620c0c60c22580403880050c300120114414500b10510008544208a0ca0406002a90c32890010403060c7147003000002000002302042305 else 0x41be20a489300018635939be2f74eae1b38ac8000000100e673ea852108965bc000000000000001325704e0000e56dc3c8000e04860d78b2302b251000018af80)
def g439D10 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1550d9a59048c38828418003e69641230e20a106000c61755438d9a59048c38828418004985d43879859048c38820600105079859048c388206000d3479859048c388206000d6941e61641230e20818003975101c61641230c206000ea0a347095c420b416800ff997fd65ff197ff60ff583ff50ff543fd10
def g439H10 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x14500038234071b21532a42e6088048d09f4127513a1b407dc248c44f3d6c940000846335cd1f912c0bf40da8e393ef01dc2b000204200000000000000249702d00000000003c891489c39a51c00000014860001f4860d800000004bbc0b3543c00b81ec27c4b53ad3013c00000058570260002c4b44f7433f0f72450002a020000000000000040c1911000000000000000000d0ba4e5d218010138e47000092d80005d10000b0e800072c1c439ceaa21b0d39090094446d00c00020c6e27902000094c4c3c20ecf2c049df121053a259114000000054908bef0a000000000000000003739d006c0b3104000000180a0002f43d268000446fc0e80577269454000f4a7937506d03fd0ca52610a082a205bc3ea4eb52b00000000d15c21c9200003ce2327000150a02f331c10186430003894252023d86d24baf22a8b7703e22c00000000002038000208e4420722311e42000000050002029a0600000003c171cdc440711350684b84c164d481d02d3218591c000f067b3ec1250358c54f02902792c2c6d80cf068c4a0002c37f40a8107c25cc2e4aae26000000000038110000c241dac4440000c90803c138101928608a50c1872c01811c80010c1411040001
def g439D11 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x3148310403ff
def g439H11 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x3c5921a3242cc0000000000000000000000000008118200000d8800022a114d7428d8361c00000816180045c00000000000064400d60000008500000000006500000000002b200000d029002
def g439L : Nat → Packing
  | 5 => (1,6,5,0,0,0,0,g439D5)
  | 6 => (24,5,5,0,0,8,0,g439D6)
  | 7 => (140,4,5,0,0,12,0,g439D7)
  | 8 => (151,3,5,0,0,14,0,g439D8)
  | 9 => (76,2,5,0,0,14,0,g439D9)
  | 10 => (8,1,5,0,0,10,0,g439D10)
  | 11 => (1,0,5,0,0,0,0,g439D11)
  | _ => emptyPacking
def g439I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 2 0 4 0 0 g439H6
  | 7 => lookupWord 8 59 4 11 5 2 g439H7
  | 8 => lookupWord 52 293 7 15 8 3 g439H8
  | 9 => lookupWord 84 547 6 15 8 3 g439H9
  | 10 => lookupWord 43 239 6 14 7 3 g439H10
  | 11 => lookupWord 6 61 3 10 3 3 g439H11
  | _ => fun _ => none
def g439 : Forest := ⟨439,11,fun i => g439Y[i]?.getD (0,0),g439C,g439A,g439L,g439I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g439P5_0 : block g439 5 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g439B5 : block g439 5 0 1=true := g439P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g439P6_0 : block g439 6 0 24=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g439B6 : block g439 6 0 24=true := g439P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g439P7_0 : block g439 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g439P7_1 : block g439 7 1 25=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g439P7_26 : block g439 7 26 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g439P7_122 : block g439 7 122 18=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g439B7 : block g439 7 0 140=true := (@block_merge g439 7 0 26 114 (@block_merge g439 7 0 1 25 g439P7_0 g439P7_1) (@block_merge g439 7 26 96 18 g439P7_26 g439P7_122))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g439P8_0 : block g439 8 0 35=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g439P8_35 : block g439 8 35 50=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g439P8_85 : block g439 8 85 66=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g439B8 : block g439 8 0 151=true := (@block_merge g439 8 0 35 116 g439P8_0 (@block_merge g439 8 35 50 66 g439P8_35 g439P8_85))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g439P9_0 : block g439 9 0 6=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g439P9_6 : block g439 9 6 46=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g439P9_52 : block g439 9 52 24=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g439B9 : block g439 9 0 76=true := (@block_merge g439 9 0 6 70 g439P9_0 (@block_merge g439 9 6 46 24 g439P9_6 g439P9_52))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g439P10_0 : block g439 10 0 8=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g439B10 : block g439 10 0 8=true := g439P10_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g439P11_0 : block g439 11 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g439B11 : block g439 11 0 1=true := g439P11_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g439T : checkedTables g439 11 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g439 0 0 0 = true)
  · exact (rfl : block g439 1 0 0 = true)
  · exact (rfl : block g439 2 0 0 = true)
  · exact (rfl : block g439 3 0 0 = true)
  · exact (rfl : block g439 4 0 0 = true)
  · exact g439B5
  · exact g439B6
  · exact g439B7
  · exact g439B8
  · exact g439B9
  · exact g439B10
  · exact g439B11
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g439G : graphValid g439 (boundsBefore KS435) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowS439 : Lower true (varsX 439) (graphGoal 439) 12 := lower_forest (g:=g439) (i:=0) (hints:=4296017748) (before_sound KS435 VS435) g439G g439T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KS439 := extendKnown KS435 12 [(439,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VS439 : Known true KS439 := extend_ok (m:=439) VS435 lowS439 (by decide +kernel)
def g511Y : Array (Bits × Bits) := #[(0xffff000000000000ffff,0x55505550555055505550555055505550555055),(0xffff00000000000000000000ffff0000,0x33053305330533053305330533053305330533),(0xffff00000000ffff00000000ffff00000000,0xf000f000f000f000f000f000f000f000f000f),(0xffff000000000000,0xf330f330f330f330f330f330f330f330f330f),(0xffff00000000000000000000ffff,0xaaa0aaa0aaa0aaa0aaa0aaa0aaa0aaa0aaa0aa),(0xff0000000000000000000000000000ffff0000,0xcc0acc0acc0acc0acc0acc0acc0acc0acc0acc),(0xffffffff00000000,0xf0ccf0ccf0ccf0ccf0ccf0ccf0ccf0ccf0ccf0),(0xffffffffffff0000000000000000,0xf000f000f000f000f000f000f000f000f00),(0xffffffffff0000000000000000000000000000,0xf000f000f000f000f000f000f000f000f000)]
def g511C : List ColumnInfo := [(0,8,439,64,13)]
def g511A : List (List Nat) := [[],[81],[16,84,135],[16,64,80,135],[64],[64,81],[80,16,65,135],[80,65,135]]
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
theorem g511G : graphValid g511 (boundsBefore KS439) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g511R : Impossible true graph 13 inputs.toFinset := by
  rw [show graph = targetOf g511 by decide +kernel]
  exact root_index (g:=g511) (top:=13) (i:=0) (before_sound KS439 VS439) g511G g511T (by decide) (by decide +kernel)
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
def KM145 := extendKnown [] 4 [(145,[]),(290,[16,84,135]),(388,[32,16,116,84,101,134])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VM145 : Known false KM145 := extend_ok (m:=145) (known_down baseKnown) lowM145 (by decide +kernel)
def mo149Y : Array (Bits × Bits) := #[(0xfdf00fff81fc7e3ffbe01fff03f8fc7ff7c03f,0x45c09245142904808b81248a28520901170249),(0x0,0x0),(0xe6a8703ffe007fc7cd50e07ffc00ff8f9aa1c0,0x96a9b6d618b228112d536dac316450225aa6db),(0x0,0x0),(0xfbb781ffffff8007f76f03ffffff000feede07,0x235249820c03122046a49304180624408d492),(0x0,0x0),(0x0,0x0),(0x64ffe3ffffffff80c9ffc7ffffffff0193ff8,0x24920410040040004924082008008000924),(0x0,0x0)]
def mo149C : List ColumnInfo := [(4,0,145,0,4)]
def mo149A : List (List Nat) := [[],[64]]
def mo149D4 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1f
def mo149L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,mo149D4)
  | _ => emptyPacking
def mo149I (_ _ : Nat) : Option (Nat × Nat) := none
def mo149 : Forest := ⟨1173,4,fun i => mo149Y[i]?.getD (0,0),mo149C,mo149A,mo149L,mo149I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo149P4_0 : block mo149 4 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo149B4 : block mo149 4 0 1=true := mo149P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo149T : checkedTables mo149 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block mo149 0 0 0 = true)
  · exact (rfl : block mo149 1 0 0 = true)
  · exact (rfl : block mo149 2 0 0 = true)
  · exact (rfl : block mo149 3 0 0 = true)
  · exact mo149B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo149G : graphValid mo149 (boundsBefore KM145) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowM149 : Lower false (varsX 149) (graphGoal 149) 5 := lower_forest (g:=mo149) (i:=0) (hints:=1796) (before_sound KM145 VM145) mo149G mo149T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KM149 := extendKnown KM145 5 [(149,[]),(294,[16,84,135]),(389,[32,132,84,101]),(390,[32,16,116,84,101,134]),(401,[130,50,83,101]),(404,[32,16,65,49,131,83,101]),(418,[16,114,50,84,67,100,134])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VM149 : Known false KM149 := extend_ok (m:=149) VM145 lowM149 (by decide +kernel)
def mo197Y : Array (Bits × Bits) := #[(0x2fc38ff01fff1ff02fc38ff01fff1ff02fc38,0x42ccdb2a5451240242ccdb2a5451240242ccdb),(0x0,0x0),(0xfdcbc7fffe07fe3ffdcbc7fffe07fe3ffdcbc7,0x1448490c186040841448490c18604084144849),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0xece607fffff8003fece607fffff8003fece607,0x8a7b6b06085892808a7b6b06085892808a7b6),(0x1b3df8ffffffffc01b3df8ffffffffc01b3df8,0x893124c081060030893124c081060030893124),(0x0,0x0)]
def mo197C : List ColumnInfo := []
def mo197A : List (List Nat) := [[],[96,114]]
def mo197D3 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xf
def mo197L : Nat → Packing
  | 3 => (1,0,1,0,0,0,0,mo197D3)
  | _ => emptyPacking
def mo197I (_ _ : Nat) : Option (Nat × Nat) := none
def mo197 : Forest := ⟨1221,3,fun i => mo197Y[i]?.getD (0,0),mo197C,mo197A,mo197L,mo197I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo197P3_0 : block mo197 3 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo197B3 : block mo197 3 0 1=true := mo197P3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo197T : checkedTables mo197 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block mo197 0 0 0 = true)
  · exact (rfl : block mo197 1 0 0 = true)
  · exact (rfl : block mo197 2 0 0 = true)
  · exact mo197B3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo197G : graphValid mo197 (boundsBefore KM149) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowM197 : Lower false (varsX 197) (graphGoal 197) 4 := lower_forest (g:=mo197) (i:=0) (hints:=33555975) (before_sound KM149 VM149) mo197G mo197T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KM197 := extendKnown KM149 4 [(197,[]),(212,[64,16,49]),(326,[16,135]),(387,[33,129,97]),(402,[16,114,50,67,100,134])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VM197 : Known false KM197 := extend_ok (m:=197) VM149 lowM197 (by decide +kernel)
def mo179Y : Array (Bits × Bits) := #[(0xc00fff0ffffffc00fffff0fffeea3a5303f03f,0x84a08a210802284a0280220882200a53145145),(0xfff0000ffc3fffff003fffffc009adfd000fc0,0xc42c405090b10c4b11404108092d994d34d3),(0x0,0x0),(0x0,0x0),(0xfffffff0003fffffffc000fffd77e88afc003f,0x90130026104c0100c0584120152a08828a28a),(0x3fffffffffff00012697f4000fc0,0x2e09c08b822702609026009c11269264b2cb2c),(0x0,0x0),(0xffffffffffc0000000000000039d530dfff000,0x300e000c00380380e03808e0208d5104c30c30),(0x0,0x0)]
def mo179C : List ColumnInfo := [(0,2,145,32,5)]
def mo179A : List (List Nat) := [[],[116],[81],[81,116],[64],[64,112],[64,81],[64,81,112],[112,64],[112],[112,81,64],[112,81]]
def mo179D5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x3f
def mo179L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,mo179D5)
  | _ => emptyPacking
def mo179I (_ _ : Nat) : Option (Nat × Nat) := none
def mo179 : Forest := ⟨1203,5,fun i => mo179Y[i]?.getD (0,0),mo179C,mo179A,mo179L,mo179I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo179P5_0 : block mo179 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo179B5 : block mo179 5 0 1=true := mo179P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo179T : checkedTables mo179 5 := by
  intro k hk
  interval_cases k
  · exact (rfl : block mo179 0 0 0 = true)
  · exact (rfl : block mo179 1 0 0 = true)
  · exact (rfl : block mo179 2 0 0 = true)
  · exact (rfl : block mo179 3 0 0 = true)
  · exact (rfl : block mo179 4 0 0 = true)
  · exact mo179B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo179G : graphValid mo179 (boundsBefore KM197) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowM179 : Lower false (varsX 179) (graphGoal 179) 6 := lower_forest (g:=mo179) (i:=0) (hints:=1048660) (before_sound KM197 VM197) mo179G mo179T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KM179 := extendKnown KM197 6 [(179,[]),(307,[16,84,135])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VM179 : Known false KM179 := extend_ok (m:=179) VM197 lowM179 (by decide +kernel)
def mo213Y : Array (Bits × Bits) := #[(0xf003ff87fe1fffc01ffff87fffe474a4007c1f,0xa12845108440228940a01108826014a45294a5),(0x0,0x0),(0xfffc0007ffe1ffffe00fffffc0335be20f83e0,0xc030162028040b0182c0a00108225922318c63),(0x0,0x0),(0xfffffff80001fffffff0007ffccfd11df0001f,0x240980130884c020302c2120087c108a5294a),(0x0,0x0),(0x1ffffffffff80004d2fe80003e0,0xb82e045c111702c140b005c104d26c9ce739c),(0xfffffffffffe000000000000033aa61bfffc00,0xc03000600018030180c046021182211084210),(0x0,0x0)]
def mo213C : List ColumnInfo := [(0,64,145,4,5),(64,0,149,0,5),(1,0,212,0,4),(4,0,145,0,4),(4,64,145,0,4),(16,0,197,0,4)]
def mo213A : List (List Nat) := [[],[64]]
def mo213D5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x50481a0fd40fd20
def mo213D6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x163440df
def mo213H6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x345fd000
def mo213L : Nat → Packing
  | 5 => (2,1,3,0,0,4,0,mo213D5)
  | 6 => (1,0,3,0,0,0,0,mo213D6)
  | _ => emptyPacking
def mo213I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 5 0 6 1 1 mo213H6
  | _ => fun _ => none
def mo213 : Forest := ⟨1237,6,fun i => mo213Y[i]?.getD (0,0),mo213C,mo213A,mo213L,mo213I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo213P5_0 : block mo213 5 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo213B5 : block mo213 5 0 2=true := mo213P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo213P6_0 : block mo213 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo213B6 : block mo213 6 0 1=true := mo213P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo213T : checkedTables mo213 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block mo213 0 0 0 = true)
  · exact (rfl : block mo213 1 0 0 = true)
  · exact (rfl : block mo213 2 0 0 = true)
  · exact (rfl : block mo213 3 0 0 = true)
  · exact (rfl : block mo213 4 0 0 = true)
  · exact mo213B5
  · exact mo213B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo213G : graphValid mo213 (boundsBefore KM179) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowM213 : Lower false (varsX 213) (graphGoal 213) 7 := lower_forest (g:=mo213) (i:=0) (hints:=33555972) (before_sound KM179 VM179) mo213G mo213T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KM213 := extendKnown KM179 7 [(213,[]),(358,[16,84,135]),(403,[33,129,97]),(419,[16,32,112,84,96,134]),(433,[130,50,83,101]),(434,[16,114,50,84,67,100,134])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VM213 : Known false KM213 := extend_ok (m:=213) VM179 lowM213 (by decide +kernel)
def mo391Y : Array (Bits × Bits) := #[(0x7ff001ff80ffc07ff003ff80fffff49a2b0007,0x42a8d4251a148b42a9aa251a948a64922b5b6d),(0x7ffffe0000fffffffffc0000ffc069da9401c0,0x14c298b62c591214c130b62c191349da8436db),(0x7fffffffff00007fffffffff00000ef10e8e38,0x700e038301e1c0701c038301e1c04d10c9249),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x800000000000007fffffffffffff99af6d703f,0x180300c0406020180200c0002000192c002492),(0xffffffffffffff800000000000006754f2ffc0,0x600c0100008000600c030040c0202200724924)]
def mo391C : List ColumnInfo := [(1,0,390,0,5)]
def mo391A : List (List Nat) := [[],[16,135]]
def mo391D5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x3f
def mo391L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,mo391D5)
  | _ => emptyPacking
def mo391I (_ _ : Nat) : Option (Nat × Nat) := none
def mo391 : Forest := ⟨1415,5,fun i => mo391Y[i]?.getD (0,0),mo391C,mo391A,mo391L,mo391I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo391P5_0 : block mo391 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo391B5 : block mo391 5 0 1=true := mo391P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo391T : checkedTables mo391 5 := by
  intro k hk
  interval_cases k
  · exact (rfl : block mo391 0 0 0 = true)
  · exact (rfl : block mo391 1 0 0 = true)
  · exact (rfl : block mo391 2 0 0 = true)
  · exact (rfl : block mo391 3 0 0 = true)
  · exact (rfl : block mo391 4 0 0 = true)
  · exact mo391B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo391G : graphValid mo391 (boundsBefore KM213) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowM391 : Lower false (varsX 391) (graphGoal 391) 6 := lower_forest (g:=mo391) (i:=0) (hints:=4294969223) (before_sound KM213 VM213) mo391G mo391T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KM391 := extendKnown KM213 6 [(391,[]),(436,[64,81,48,49]),(453,[97,130,49,67,84]),(454,[16,96,114,48,67,84,130])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VM391 : Known false KM391 := extend_ok (m:=391) VM213 lowM391 (by decide +kernel)
def mo405Y : Array (Bits × Bits) := #[(0xffc03fffc7fe00ffc3fe1ffff9476800003ff,0x242a2828092148a4289044084314349294a529),(0x0,0x0),(0xffffc03fffffff0003ffe1fe271f141f07c00,0x40b030b0500580c0b10280408871f006318c63),(0x0,0x0),(0xffffffc007fffffffc0001ffdea67000f801f,0x88c040c262461108c023089100ea4325294a52),(0x0,0x0),(0x0,0x0),(0xf0000000007fffffffffffe0005f08be0fffe0,0x1008100800802010004000200000008421084),(0xffffffffff8000000000000003289bfff00000,0xe03020300701c0e0238111c13080bf18c6318)]
def mo405C : List ColumnInfo := [(1,0,404,0,5),(4,0,401,0,5),(16,0,389,0,5),(256,0,149,0,5),(17,0,388,0,4),(260,0,145,0,4)]
def mo405A : List (List Nat) := [[],[130],[32,132],[32,64,128],[64],[64,130],[128,32,66],[128,66]]
def mo405D4 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x26d6214d10
def mo405D5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xc4104012821408017d53442f8a6887e4c110
def mo405H5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x822
def mo405D6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x10c84055432101bc0fd30fd10
def mo405H6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x10060000b29400000048000091
def mo405D7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x163440df
def mo405H7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xfab10000c5bdc240163900
def mo405L : Nat → Packing
  | 4 => (1,3,3,0,0,0,0,mo405D4)
  | 5 => (3,2,3,0,0,6,0,mo405D5)
  | 6 => (2,1,3,0,0,5,0,mo405D6)
  | 7 => (1,0,3,0,0,0,0,mo405D7)
  | _ => emptyPacking
def mo405I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 2 0 6 0 2 mo405H5
  | 6 => lookupWord 1 23 0 8 2 2 mo405H6
  | 7 => lookupWord 2 11 0 8 1 3 mo405H7
  | _ => fun _ => none
def mo405 : Forest := ⟨1429,7,fun i => mo405Y[i]?.getD (0,0),mo405C,mo405A,mo405L,mo405I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo405P4_0 : block mo405 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo405B4 : block mo405 4 0 1=true := mo405P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo405P5_0 : block mo405 5 0 3=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo405B5 : block mo405 5 0 3=true := mo405P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo405P6_0 : block mo405 6 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo405B6 : block mo405 6 0 2=true := mo405P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo405P7_0 : block mo405 7 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo405B7 : block mo405 7 0 1=true := mo405P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo405T : checkedTables mo405 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block mo405 0 0 0 = true)
  · exact (rfl : block mo405 1 0 0 = true)
  · exact (rfl : block mo405 2 0 0 = true)
  · exact (rfl : block mo405 3 0 0 = true)
  · exact mo405B4
  · exact mo405B5
  · exact mo405B6
  · exact mo405B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo405G : graphValid mo405 (boundsBefore KM391) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowM405 : Lower false (varsX 405) (graphGoal 405) 8 := lower_forest (g:=mo405) (i:=0) (hints:=8589936388) (before_sound KM391 VM391) mo405G mo405T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KM405 := extendKnown KM391 8 [(405,[]),(422,[16,84,135])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VM405 : Known false KM405 := extend_ok (m:=405) VM391 lowM405 (by decide +kernel)
def mo183Y : Array (Bits × Bits) := #[(0x3fffffffffffffffffb94049bf55b28003f03f,0x814150284a050a4214b8404097451205145145),(0xfffff80000ffffe00036bb4666c1ae40000fc0,0x100a62036c404c80663633462401ae134d34d3),(0x3fffffffff00000000066c749abd8b00fc0000,0x59380b270166f04b8026c449abd8b0f3cf3cf),(0x0,0x0),(0x3fffffffffffffffff58b1cca8bed4bf00003f,0x61c00c380187008c000a10c28bac48a28a28a),(0xc0000000000000000048af2b5fcc4a40000fc0,0x27e004fc009f800f00488c295bcc406cb2cb2c),(0x0,0x0),(0xe754b7112b657ffff000,0x3800070000e00010004510b300002070c30c30),(0x0,0x0)]
def mo183C : List ColumnInfo := [(0,2,149,32,6)]
def mo183A : List (List Nat) := [[],[81],[64],[64,81]]
def mo183D6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x7f
def mo183L : Nat → Packing
  | 6 => (1,0,1,0,0,0,0,mo183D6)
  | _ => emptyPacking
def mo183I (_ _ : Nat) : Option (Nat × Nat) := none
def mo183 : Forest := ⟨1207,6,fun i => mo183Y[i]?.getD (0,0),mo183C,mo183A,mo183L,mo183I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo183P6_0 : block mo183 6 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo183B6 : block mo183 6 0 1=true := mo183P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo183T : checkedTables mo183 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block mo183 0 0 0 = true)
  · exact (rfl : block mo183 1 0 0 = true)
  · exact (rfl : block mo183 2 0 0 = true)
  · exact (rfl : block mo183 3 0 0 = true)
  · exact (rfl : block mo183 4 0 0 = true)
  · exact (rfl : block mo183 5 0 0 = true)
  · exact mo183B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo183G : graphValid mo183 (boundsBefore KM405) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowM183 : Lower false (varsX 183) (graphGoal 183) 7 := lower_forest (g:=mo183) (i:=0) (hints:=1050452) (before_sound KM405 VM405) mo183G mo183T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KM183 := extendKnown KM405 7 [(183,[]),(311,[16,84,135])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VM183 : Known false KM183 := extend_ok (m:=183) VM405 lowM183 (by decide +kernel)
def mo231Y : Array (Bits × Bits) := #[(0xffff000003fffff0000f1e1eeb6ca42803f000,0xa92a02ada80aa520256b0e1ee32484283cf3cf),(0xfffffffffffffffffff3e9d4d9889fe200003f,0x304c48c1312306424243e0d489089e82555555),(0xfffffffffc000000000066ed2733d477fc0fc0,0x2700009c00037800b80262c0200d4730c30c3),(0x0,0x0),(0x0,0x0),(0xfffffffffffffffffff58b1e74957bf000003f,0xc380930e024c38048c040b0a74956170aaaaaa),(0x48af3b7e9c20e000fc0,0xfc00e3f0038fc008f00488d3b5e9020cf3cf3c),(0xe754a985f269dfff000,0xfc0003f0000f00045140185b2284c30c30),(0x0,0x0)]
def mo231C : List ColumnInfo := [(0,2,197,32,5)]
def mo231A : List (List Nat) := [[],[81],[96,114],[96,81,114]]
def mo231D5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x7f
def mo231L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,mo231D5)
  | _ => emptyPacking
def mo231I (_ _ : Nat) : Option (Nat × Nat) := none
def mo231 : Forest := ⟨1255,5,fun i => mo231Y[i]?.getD (0,0),mo231C,mo231A,mo231L,mo231I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo231P5_0 : block mo231 5 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo231B5 : block mo231 5 0 1=true := mo231P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo231T : checkedTables mo231 5 := by
  intro k hk
  interval_cases k
  · exact (rfl : block mo231 0 0 0 = true)
  · exact (rfl : block mo231 1 0 0 = true)
  · exact (rfl : block mo231 2 0 0 = true)
  · exact (rfl : block mo231 3 0 0 = true)
  · exact (rfl : block mo231 4 0 0 = true)
  · exact mo231B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo231G : graphValid mo231 (boundsBefore KM183) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowM231 : Lower false (varsX 231) (graphGoal 231) 6 := lower_forest (g:=mo231) (i:=0) (hints:=34604631) (before_sound KM183 VM183) mo231G mo231T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KM231 := extendKnown KM183 6 [(343,[16,84,135])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VM231 : Known false KM231 := extend_ok (m:=231) VM183 lowM231 (by decide +kernel)
def mo407Y : Array (Bits × Bits) := #[(0xfffffffffffffffffec91513674a78000003ff,0x481440548129029028c914126242525294a529),(0xfc00fffe0003fff801f405383e999001f00000,0x90a612982db05320cdf005383e9881ce739ce7),(0xfffffffc00000039c4f6930e803e007c00,0xe13804e009c01bc1701184b6130e80c6318c63),(0x0,0x0),(0xfffffffffffffe428bea0bc9e8000f801f,0x1c087010e021c0180008be80909aca5294a52),(0x0,0x0),(0x0,0x0),(0xffff0000000000000022fa117cb687c00fffe0,0x1800300060020022600104900108421084),(0x19d26ecc07137fff00000,0x200e001c0038004000c0240c06136318c6318)]
def mo407C : List ColumnInfo := [(2,0,405,0,8)]
def mo407A : List (List Nat) := [[],[64]]
def mo407D8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x7f
def mo407L : Nat → Packing
  | 8 => (1,0,1,0,0,0,0,mo407D8)
  | _ => emptyPacking
def mo407I (_ _ : Nat) : Option (Nat × Nat) := none
def mo407 : Forest := ⟨1431,8,fun i => mo407Y[i]?.getD (0,0),mo407C,mo407A,mo407L,mo407I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo407P8_0 : block mo407 8 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo407B8 : block mo407 8 0 1=true := mo407P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo407T : checkedTables mo407 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block mo407 0 0 0 = true)
  · exact (rfl : block mo407 1 0 0 = true)
  · exact (rfl : block mo407 2 0 0 = true)
  · exact (rfl : block mo407 3 0 0 = true)
  · exact (rfl : block mo407 4 0 0 = true)
  · exact (rfl : block mo407 5 0 0 = true)
  · exact (rfl : block mo407 6 0 0 = true)
  · exact (rfl : block mo407 7 0 0 = true)
  · exact mo407B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo407G : graphValid mo407 (boundsBefore KM231) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowM407 : Lower false (varsX 407) (graphGoal 407) 9 := lower_forest (g:=mo407) (i:=0) (hints:=4294969220) (before_sound KM231 VM231) mo407G mo407T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KM407 := extendKnown KM231 9 [(407,[]),(423,[16,84,135]),(437,[81,49]),(438,[16,64,48,83,135]),(469,[97,130,49,83]),(486,[16,96,114,48,84,67,130])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VM407 : Known false KM407 := extend_ok (m:=407) VM231 lowM407 (by decide +kernel)
def mo435Y : Array (Bits × Bits) := #[(0x7fffffe0ffffc92a21b355e900000000ff00ff,0x2029004241100822019145e845454545454545),(0x8003fffffff81a51a0dee1520000ff0000ff00,0x4b0228008209a5120ce404013131313131313),(0x0,0x0),(0x0,0x0),(0xfffc0000ffffefe3ba248209000000ff0000ff,0x40c20b0482402701b82482018a8a8a8a8a8a8a),(0xffffffff000020925965f93400ff000000ff00,0x9004c00138120825121b9102c2c2c2c2c2c2c),(0x0,0x0),(0x24dd460b16d0ff0000ffff0000,0xe0070081c0200d8460a101030303030303030),(0x1324dd980e26ffffff00000000,0x70038010e004012488100626c0c0c0c0c0c0c0)]
def mo435C : List ColumnInfo := [(1,0,434,0,7),(2,0,433,0,7),(16,0,419,0,7),(32,0,403,0,7),(0,1,290,144,6),(0,2,145,288,6),(0,16,290,129,6),(0,32,145,258,6),(128,0,307,0,6),(256,0,179,0,6),(1,16,290,128,5),(2,32,145,256,5),(16,1,290,128,5),(17,0,418,0,5),(128,1,290,16,5),(128,16,290,1,5),(256,2,145,32,5),(256,32,145,2,5),(129,0,290,0,4)]
def mo435A : List (List Nat) := [[],[81],[16,84,135],[16,64,80,135],[64],[64,81],[80,16,65,135],[80,65,135]]
def mo435D7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x24111c210684470041a110c01080c1220263c584882603e00ff54540ff54520ff4c520be58054
def mo435D8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x4503ce2071851230e20a106001140f3892071851230e20a106001145038a2481230e20a104038e2892048c388284100c3892061230c284100b38b2892051230e208100dd8511d49c2a003faa9fc54fea87f503fa41fd10
def mo435H8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x65000002100000000000000000000002d1300000000b8000000000000000000000000000e18000122000000000000000000838000066000000000
def mo435D9 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1882013f
def mo435H9 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x70072000000026380c00304000009178800860000000000308213f300092d17a8308000000000000000000000000000001d300000000000000000000000000000000000000000000042
def mo435L : Nat → Packing
  | 7 => (4,2,5,0,0,8,0,mo435D7)
  | 8 => (6,1,5,0,0,9,0,mo435D8)
  | 9 => (1,0,5,0,0,0,0,mo435D9)
  | _ => emptyPacking
def mo435I : Nat → Nat → Option (Nat × Nat)
  | 8 => lookupWord 2 53 0 9 2 3 mo435H8
  | 9 => lookupWord 4 59 2 10 3 3 mo435H9
  | _ => fun _ => none
def mo435 : Forest := ⟨1459,9,fun i => mo435Y[i]?.getD (0,0),mo435C,mo435A,mo435L,mo435I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo435P7_0 : block mo435 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo435P7_1 : block mo435 7 1 3=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo435B7 : block mo435 7 0 4=true := (@block_merge mo435 7 0 1 3 mo435P7_0 mo435P7_1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo435P8_0 : block mo435 8 0 6=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo435B8 : block mo435 8 0 6=true := mo435P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo435P9_0 : block mo435 9 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo435B9 : block mo435 9 0 1=true := mo435P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo435T : checkedTables mo435 9 := by
  intro k hk
  interval_cases k
  · exact (rfl : block mo435 0 0 0 = true)
  · exact (rfl : block mo435 1 0 0 = true)
  · exact (rfl : block mo435 2 0 0 = true)
  · exact (rfl : block mo435 3 0 0 = true)
  · exact (rfl : block mo435 4 0 0 = true)
  · exact (rfl : block mo435 5 0 0 = true)
  · exact (rfl : block mo435 6 0 0 = true)
  · exact mo435B7
  · exact mo435B8
  · exact mo435B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo435G : graphValid mo435 (boundsBefore KM407) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowM435 : Lower false (varsX 435) (graphGoal 435) 10 := lower_forest (g:=mo435) (i:=0) (hints:=4296015956) (before_sound KM407 VM407) mo435G mo435T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KM435 := extendKnown KM407 10 [(435,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VM435 : Known false KM435 := extend_ok (m:=435) VM407 lowM435 (by decide +kernel)
def mo455Y : Array (Bits × Bits) := #[(0xfffffffc0000ffffc00065a6896bd1560000f0,0x94a04aa836aa092905a64a6892a5156bbbbbb),(0xfffffffff00000000da29988fa93600f000,0x3260a9302a4c0adb02acd809888da936777777),(0xfffffffffffffffff3cd08fa423eb0f0f0f,0x38001c00070001c00302880888402ca111111),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0xfffffffffffffffff216395b13d3d00000f,0x5c0cce033380cce024c0016315313d35eeeeee),(0xfff00000000000000000115e685ddcf0f00ff0,0x6000f0003c000f000700115840418c20444444),(0xcea977125e06fff000,0x800f0003c000f0003800062037125000888888)]
def mo455C : List ColumnInfo := [(1,0,454,0,6),(2,0,453,0,6),(64,0,391,0,6),(0,1,326,128,5),(0,2,197,256,5),(4,64,387,0,4),(128,0,326,0,4),(128,1,326,0,4)]
def mo455A : List (List Nat) := [[],[97,130],[16,135],[16,96,114,130],[96,16,130,114],[96,114]]
def mo455D6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x7542015d94ea46f03fa85f920
def mo455D7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x7a8817f
def mo455H7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x340000d60d800000000000001280210000000000314000000000106c80000000000000001
def mo455L : Nat → Packing
  | 6 => (2,1,3,0,0,5,0,mo455D6)
  | 7 => (1,0,3,0,0,0,0,mo455D7)
  | _ => emptyPacking
def mo455I : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 2 37 1 8 1 3 mo455H7
  | _ => fun _ => none
def mo455 : Forest := ⟨1479,7,fun i => mo455Y[i]?.getD (0,0),mo455C,mo455A,mo455L,mo455I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo455P6_0 : block mo455 6 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo455P6_1 : block mo455 6 1 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo455B6 : block mo455 6 0 2=true := (@block_merge mo455 6 0 1 1 mo455P6_0 mo455P6_1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo455P7_0 : block mo455 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo455B7 : block mo455 7 0 1=true := mo455P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo455T : checkedTables mo455 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block mo455 0 0 0 = true)
  · exact (rfl : block mo455 1 0 0 = true)
  · exact (rfl : block mo455 2 0 0 = true)
  · exact (rfl : block mo455 3 0 0 = true)
  · exact (rfl : block mo455 4 0 0 = true)
  · exact (rfl : block mo455 5 0 0 = true)
  · exact mo455B6
  · exact mo455B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo455G : graphValid mo455 (boundsBefore KM435) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowM455 : Lower false (varsX 455) (graphGoal 455) 8 := lower_forest (g:=mo455) (i:=0) (hints:=4328523399) (before_sound KM435 VM435) mo455G mo455T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KM455 := extendKnown KM435 8 [(455,[]),(470,[16,64,48,135]),(500,[64,81,48,49])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VM455 : Known false KM455 := extend_ok (m:=455) VM435 lowM455 (by decide +kernel)
def mo247Y : Array (Bits × Bits) := #[(0x2a45956e817f9152a58e5c00000ffc00003ff,0x20458522805f9102a58e14154551545515455),(0xf031b0bc81f51b90ebaa9af0000000000ffc00,0xb03190b481f41980eaa898a4cd334cd334cd33),(0xbe5a88411b0fccc2f671829003ff003ff00000,0x345a08410903cc80664182903c0f03c0f03c0f),(0x0,0x0),(0x61cf8624a5a2c12a438d4d9ffc0000000003ff,0x61cb84248582000a41810492a8aa2a8aa2a8aa),(0x4c99308a5ccbae3c49575370000000000ffc00,0x4c88200a5c0ba63c0157435b32ccb32ccb32cc),(0x6a64d6ea9e8415f7a43319000000003ff00000,0x4a24d6aa968411778032190fc3f0fc3f0fc3f0),(0x952a4f3b5578326d10e4b80fffffffc0000000,0x80200308507802651024180c0300c0300c0300),(0x0,0x0)]
def mo247C : List ColumnInfo := [(0,2,213,32,8)]
def mo247A : List (List Nat) := [[],[81],[64],[64,81]]
def mo247D8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xff
def mo247L : Nat → Packing
  | 8 => (1,0,1,0,0,0,0,mo247D8)
  | _ => emptyPacking
def mo247I (_ _ : Nat) : Option (Nat × Nat) := none
def mo247 : Forest := ⟨1271,8,fun i => mo247Y[i]?.getD (0,0),mo247C,mo247A,mo247L,mo247I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo247P8_0 : block mo247 8 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo247B8 : block mo247 8 0 1=true := mo247P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo247T : checkedTables mo247 8 := by
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
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo247G : graphValid mo247 (boundsBefore KM455) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowM247 : Lower false (varsX 247) (graphGoal 247) 9 := lower_forest (g:=mo247) (i:=0) (hints:=34604628) (before_sound KM455 VM455) mo247G mo247T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KM247 := extendKnown KM455 9 [(247,[]),(375,[16,84,135])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VM247 : Known false KM247 := extend_ok (m:=247) VM455 lowM247 (by decide +kernel)
def mo439Y : Array (Bits × Bits) := #[(0xc2a879850ea6986b3c41000000000000ff00ff,0x400878850c86906a3441454545454545454545),(0x5897c212c24b0a6ed515000000ff000000ff00,0x5097c01042490a6e4405131313131313131313),(0xe546fd9cf00e2c4200d40000ff0000ff000000,0xc444f59cd00e0c4200d40f0f0f0f0f0f0f0f0f),(0x0,0x0),(0xb671d1560780cf300b3400000000ff000000ff,0xb671811203004c100b348a8a8a8a8a8a8a8a8a),(0x12d231d851215cdd3f200ff0000000000ff00,0x128230d8512058191f02c2c2c2c2c2c2c2c2c),(0x0,0x0),(0x4592a2e11878631520a9ff000000ffffff0000,0x1820260007023050000303030303030303030),(0x3a480c2a6955d482064effffffff0000000000,0x2a0008022800d000020ac0c0c0c0c0c0c0c0c0)]
def mo439C : List ColumnInfo := [(4,0,435,0,10),(1,0,438,0,9),(2,0,437,0,9),(16,0,423,0,9),(32,0,407,0,9),(17,0,422,0,8),(34,0,405,0,8),(0,1,294,144,7),(0,2,149,288,7),(0,16,294,129,7),(0,32,149,258,7),(128,0,311,0,7),(256,0,183,0,7),(1,16,294,128,6),(3,0,436,0,6),(32,2,149,256,6),(128,1,294,16,6),(128,16,294,1,6),(132,0,307,0,6),(256,2,149,32,6),(256,32,149,2,6),(129,16,294,0,5),(258,32,149,0,5)]
def mo439A : List (List Nat) := [[],[81],[16,84,135],[16,64,80,135],[64],[64,81],[80,16,65,135],[80,65,135]]
def mo439D7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x4401e183c3062710d1704490e5500cf6c910ea8ac13bd94219515427db24432a2a847b6488754560
def mo439D8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x3251d090d0300cc98282c021261e080900a1a160f870444308619140a08a18c9861f00228262220c8c6c4c3404050a0988c383b231b110f030162620100f4d8a080744058203c0007085463d362d160f010160f8d8a080784058203c000608880605f3727170102422201817cdc9c7c4c050988880605f271f0101613cc8bc9c583c040905f362f271f160b0121e16118bc9c783c04060583f342f271f140f01533253478885051fb3e8724cd15f278424730bb1301d42702b000dfd715c165efd8159560bfd8654550bfc8654550f7d6554550ff96158150dfc8759510ded655c865df9655c0659fc8754560e7d65545609fd861d510dd9735c065de9725c065df1715c0659dd831d5609ed821d5609f5811d5609f88758150
def mo439H8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x50ed4f9003680000d160401898
def mo439D9 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x825c8931a3c4890e040594264480b88921a3848a0a1c101020509901717244498e1a3c50914103820204c990182d4088e1d34588921a3440a081c10102a4064588921a3848a081c10101c58a8c16203a68b11243468814103820204c9904d16224868d102820704040793203860b0f1a2c4490d1c205040e080813284c91120305e6cb931e2c280e284c807cc97204c60f102420700040a13224060bcd931e2c058b1423345c813183c40a081c000f211f345c98f1410380a201f345c813183c40a0e0006942630508cd17204c60f10282070004480b0f982e4c70f1602880c0f1a2e4098c1c2838001a2e345c81318385040e0006100f182e4c70e102c05142644866cb931e2c280b284c88c161f364c78b017094fa8e92d60c90b7aa9c9868b67ca7246465ae4ec3f235a2981e414c0a6001ff5c165ffaca32ffd65583fea8ac1ff59550ffac2a87fd51543feb2a21fb5c865bfae032ff970196fe3aac1bf59560bfaeca85fc76543fcb02a17f5d510bf8ea887f960442f6b90cb7e5c065
def mo439H9 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x10055000000000090700000000000000000000000000b00000010f00000000048a0000000000000000000002c50000000000000000d100000000000000000000000000000000002e000000000000021000000000000000000811000000000802000745000000000000000000000000d09000000000000000000000d120005ce000000000e0d6cf000000000d10000000351f85000000000000000000000000000ad000030e00000053100060a000000000000000000000b0c728000000000303824000000000000000000a32000000000000000000000000000000000000a30000000000000000000000000000000000000000000000d04000000e4d0002010000000000000008ca000000000000000000000000a0800000000000000010500000000000000032d50600000000014e00000024f000000000000000000d4a00940
def mo439D10 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x134b2091871050830006289a284d2c82461c41420c002080f30b2091871040c001aaa03cc2c82461c410300072070e30b2091861030006da204ae2a003fd65ff197fd60ff543fd10
def mo439H10 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x61120a78a710000150dd4440e2fa121885c7f0080d444302014a90d13203c0bb92d4312d5068077940000241c80000082423094800009ad70f0008cb80cd2e0000313ca8480001ce00000000050174b8d2c6d0c0a4eb04205000e529479d068b0c400040e00084ac22154f8700011f24207f24d291408005
def mo439D11 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x3148310403ff
def mo439H11 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1d80030400000001e87c400cc800000000440018a61e038312000000000004100000c48005082
def mo439L : Nat → Packing
  | 7 => (4,4,5,0,0,7,0,mo439D7)
  | 8 => (19,3,5,0,0,11,0,mo439D8)
  | 9 => (21,2,5,0,0,12,0,mo439D9)
  | 10 => (5,1,5,0,0,9,0,mo439D10)
  | 11 => (1,0,5,0,0,0,0,mo439D11)
  | _ => emptyPacking
def mo439I : Nat → Nat → Option (Nat × Nat)
  | 8 => lookupWord 2 11 2 9 2 3 mo439H8
  | 9 => lookupWord 10 223 2 12 5 3 mo439H9
  | 10 => lookupWord 14 73 6 12 5 3 mo439H10
  | 11 => lookupWord 3 37 2 10 3 3 mo439H11
  | _ => fun _ => none
def mo439 : Forest := ⟨1463,11,fun i => mo439Y[i]?.getD (0,0),mo439C,mo439A,mo439L,mo439I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo439P7_0 : block mo439 7 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo439P7_1 : block mo439 7 1 3=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo439B7 : block mo439 7 0 4=true := (@block_merge mo439 7 0 1 3 mo439P7_0 mo439P7_1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo439P8_0 : block mo439 8 0 7=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo439P8_7 : block mo439 8 7 5=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo439P8_12 : block mo439 8 12 7=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo439B8 : block mo439 8 0 19=true := (@block_merge mo439 8 0 7 12 mo439P8_0 (@block_merge mo439 8 7 5 7 mo439P8_7 mo439P8_12))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo439P9_0 : block mo439 9 0 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo439P9_2 : block mo439 9 2 11=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo439P9_13 : block mo439 9 13 8=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo439B9 : block mo439 9 0 21=true := (@block_merge mo439 9 0 2 19 mo439P9_0 (@block_merge mo439 9 2 11 8 mo439P9_2 mo439P9_13))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo439P10_0 : block mo439 10 0 5=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo439B10 : block mo439 10 0 5=true := mo439P10_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo439P11_0 : block mo439 11 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo439B11 : block mo439 11 0 1=true := mo439P11_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo439T : checkedTables mo439 11 := by
  intro k hk
  interval_cases k
  · exact (rfl : block mo439 0 0 0 = true)
  · exact (rfl : block mo439 1 0 0 = true)
  · exact (rfl : block mo439 2 0 0 = true)
  · exact (rfl : block mo439 3 0 0 = true)
  · exact (rfl : block mo439 4 0 0 = true)
  · exact (rfl : block mo439 5 0 0 = true)
  · exact (rfl : block mo439 6 0 0 = true)
  · exact mo439B7
  · exact mo439B8
  · exact mo439B9
  · exact mo439B10
  · exact mo439B11
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo439G : graphValid mo439 (boundsBefore KM247) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowM439 : Lower false (varsX 439) (graphGoal 439) 12 := lower_forest (g:=mo439) (i:=0) (hints:=4296017748) (before_sound KM247 VM247) mo439G mo439T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KM439 := extendKnown KM247 12 [(439,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VM439 : Known false KM439 := extend_ok (m:=439) VM247 lowM439 (by decide +kernel)
def mo471Y : Array (Bits × Bits) := #[(0xff70b411a126ea56d1c869f2000000001fc07f,0x14500011a124ca56d1c028e04a952a54a952a5),(0xd652f93a82116ced1d38520003f800000000,0x669452d93282116cec1c38523e7cf9f3e7cf9f),(0x3949ce34b10bfc1090222f01fc000fe03f80,0xb83108883431093c10002003060c183060c183),(0x0,0x0),(0xffadaf18fc4694984215d492000007f000007f,0xc02daf081c4210880211d412952a54a952a54a),(0x0,0x0),(0x8065b71f8c54c533981db900000000003f80,0x8065370b8c54c123981db8f9f3e7cf9f3e7c),(0x91524941786503266e954cfe0007ffffc000,0x80504040002401242c010c20408102040810),(0x4ea9248a495a2bafa32a80fffff800000000,0x4aa1248848420203830280c183060c183060)]
def mo471C : List ColumnInfo := [(2,0,469,0,9),(64,0,407,0,9),(0,2,213,256,8),(0,64,403,4,8),(1,0,470,0,8),(16,0,455,0,8),(4,0,403,0,7),(4,64,403,0,7),(256,0,213,0,7),(256,2,213,0,7),(0,1,326,144,6),(0,16,326,129,6),(17,0,454,0,6),(128,0,343,0,6),(1,16,326,128,5),(16,1,326,128,5),(128,1,326,16,5),(128,16,326,1,5),(5,64,402,0,4),(129,16,326,0,4),(144,1,326,0,4),(260,2,145,0,4),(262,64,145,0,4)]
def mo471A : List (List Nat) := [[],[97,130],[64],[64,97,130]]
def mo471D6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x6974212101c3f13c21e10814f4965c57054bea2a690aa0985b92598154920
def mo471D7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xa61d8f084a5a10804404085071c0f8000410630a1f138431110298763c2e1e020a31f9793868068a458404e1e018371f13878050dc7c4e1e0174d90c55f2ed68a14b21cc8491705c00eed6558952df5715c152fd47348550f755348550df57548530ff121541309fd861d520f6d6554920fe58154920e6d6558952af4865c552f5953541308fd861d5209dd831d520
def mo471H7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xb20000000040005100b8da4500
def mo471D8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x14c7c28500aa6386470a0a01e3a5c284426294a78a8500e413c588111211c60a529e2214039018293c4448472440529470500e4878e14162048280916294c70a13081c000a531c323858700e44829101e161c042912a23e5c88b0904484990a13a549850c00061015a73a589870103c72588130e01c99053214468b11161828001aa64284e1a2c4440b0c12c80a101b081c000821314c8511a2220586097314c8509c344440b0c12c80c15142e1c03901a294c70b13081c000b203c5088e17081c000a1a2c4470c16204060b081c000e203458a111e26103800164070788130e01c98f1c1d2c409870124c80d53214478b11102c304d203c5298e1a2a5c380a203c68a8e192e1c049121264274d972238500b8698328107d97a276b7346fd6b866c6355f75b955f5214ea4894363f83a535231b2c827c2141c118a1450e4098053000ffaeca97fd6554bfeb82a5ff58950ffaa4a87fd624c3fea9261ff59520ffac6905fd7654bbeb2aa5fb58952feae2a97f552547ee39aa1df54d50feaa2a87f521542febaa61fd54530fea42987f9504c2febb2417f5d520bf8ea905fd73483f6a9241fb4c920feaa2907f960483fca8241ed55151
def mo471H8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x60eb6001a500000f100012800167e8e0b078180000000e5958a24000035bd3066e1400a0788b018be361a000000b000000a180
def mo471D9 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xb2a49038d28b20908300075240e34a2c82050830006a655244e34a28908300069855244e30a2420c0018a2055240e34a28908300071244f2c814239240e34b205091b6b143980661b003fd62ff54bfd50ff4c3fd20fd547f521
def mo471H9 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x40b02903311d3c0c148b32e7a250006b6b72d5800e140000041ca3400000590c3a001005dd65800385a1564c450007c345e43e62fb8d035e000006c1cc26670b932e0580000049200000000001a348200060e484004b4925a4e4d80095d27cc67bb150a44704d8d32c0008080110
def mo471D10 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x24e5204037f
def mo471H10 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x2c20000000000000134000000000000000000000000002d025006c800004100000000000001060000000000000000000000000000000000000000000003480000000000000000076800000000000000000001a40040c00000000000b4000000000150000000000000000000000000000000180
def mo471L : Nat → Packing
  | 6 => (3,4,5,0,0,6,0,mo471D6)
  | 7 => (14,3,5,0,0,9,0,mo471D7)
  | 8 => (32,2,5,0,0,12,0,mo471D8)
  | 9 => (7,1,5,0,0,9,0,mo471D9)
  | 10 => (1,0,5,0,0,0,0,mo471D10)
  | _ => emptyPacking
def mo471I : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 1 23 0 8 2 2 mo471H7
  | 8 => lookupWord 6 41 3 10 4 2 mo471H8
  | 9 => lookupWord 13 73 6 11 5 2 mo471H9
  | 10 => lookupWord 3 127 0 9 3 2 mo471H10
  | _ => fun _ => none
def mo471 : Forest := ⟨1495,10,fun i => mo471Y[i]?.getD (0,0),mo471C,mo471A,mo471L,mo471I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo471P6_0 : block mo471 6 0 3=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo471B6 : block mo471 6 0 3=true := mo471P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo471P7_0 : block mo471 7 0 5=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo471P7_5 : block mo471 7 5 9=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo471B7 : block mo471 7 0 14=true := (@block_merge mo471 7 0 5 9 mo471P7_0 mo471P7_5)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo471P8_0 : block mo471 8 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo471P8_1 : block mo471 8 1 22=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo471P8_23 : block mo471 8 23 9=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo471B8 : block mo471 8 0 32=true := (@block_merge mo471 8 0 1 31 mo471P8_0 (@block_merge mo471 8 1 22 9 mo471P8_1 mo471P8_23))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo471P9_0 : block mo471 9 0 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo471P9_2 : block mo471 9 2 5=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo471B9 : block mo471 9 0 7=true := (@block_merge mo471 9 0 2 5 mo471P9_0 mo471P9_2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo471P10_0 : block mo471 10 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo471B10 : block mo471 10 0 1=true := mo471P10_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo471T : checkedTables mo471 10 := by
  intro k hk
  interval_cases k
  · exact (rfl : block mo471 0 0 0 = true)
  · exact (rfl : block mo471 1 0 0 = true)
  · exact (rfl : block mo471 2 0 0 = true)
  · exact (rfl : block mo471 3 0 0 = true)
  · exact (rfl : block mo471 4 0 0 = true)
  · exact (rfl : block mo471 5 0 0 = true)
  · exact mo471B6
  · exact mo471B7
  · exact mo471B8
  · exact mo471B9
  · exact mo471B10
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo471G : graphValid mo471 (boundsBefore KM439) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowM471 : Lower false (varsX 471) (graphGoal 471) 11 := lower_forest (g:=mo471) (i:=0) (hints:=4328523396) (before_sound KM439 VM439) mo471G mo471T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KM471 := extendKnown KM439 11 [(471,[]),(487,[16,84,135]),(501,[81,49]),(502,[16,64,48,83,135])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VM471 : Known false KM471 := extend_ok (m:=471) VM439 lowM471 (by decide +kernel)
def mo503Y : Array (Bits × Bits) := #[(0x938654f5000000000000000000fff000000fff,0x838640e5455455455455455455455455455455),(0x3591c32a000000000fff000000000000fff000,0x1491c322133133133133133133133133133133),(0x8aaa3a61000000fff000000fff000fff000000,0xaa2186000f00f00f00f00f00f00f00f00f00f),(0x0,0x0),(0x3694bc02000000000000fff000000000000fff,0x3410bc008aa8aa8aa8aa8aa8aa8aa8aa8aa8aa),(0xa25810f8000fff000000000000000000fff000,0xa24810582cc2cc2cc2cc2cc2cc2cc2cc2cc2cc),(0xc51c23c1000000000000000000000fff000000,0xc51c2381ff0ff0ff0ff0ff0ff0ff0ff0ff0ff0),(0x4c03001efff000000000fffffffff000000000,0x1001a300300300300300300300300300300),(0x4161ed80ffffffffffff000000000000000000,0x41002480c00c00c00c00c00c00c00c00c00c00)]
def mo503C : List ColumnInfo := [(64,0,439,0,12),(0,64,435,4,11),(1,0,502,0,11),(2,0,501,0,11),(16,0,487,0,11),(32,0,471,0,11),(4,0,435,0,10),(4,64,435,0,10),(0,1,358,144,9),(0,2,213,288,9),(0,16,358,129,9),(0,32,213,258,9),(17,0,486,0,9),(34,0,469,0,9),(128,0,375,0,9),(256,0,247,0,9),(1,16,358,128,8),(2,32,213,256,8),(3,0,500,0,8),(16,1,358,128,8),(32,2,213,256,8),(128,1,358,16,8),(128,16,358,1,8),(256,2,213,32,8),(256,32,213,2,8),(5,64,434,0,7),(6,64,433,0,7),(129,16,358,0,7),(144,1,358,0,7),(145,0,358,0,7),(258,32,213,0,7),(288,2,213,0,7),(290,0,213,0,7)]
def mo503A : List (List Nat) := [[],[81],[16,84,135],[16,64,80,135],[64],[64,81],[80,16,65,135],[80,65,135]]
def mo503D6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1a325c4704b9688865d570
def mo503D7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xe16e15c86f801251fd00254607715e1370034c3b020ba1dd17e0bf0043430710c1c86d810bc34b0259e108c07803cc96d1b12a1921d965e365c12e5a2219755c30db2e5b7688865d570a6d9c32999164172583f245d1635c541581309da5c42dda15897148326d6d1b169c8650520b995c3219745c5414834c96d1b12a1921d965
def mo503H7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x70
def mo503D8 (j : Nat) : Nat := if 2 ≤ j then 0 else (if j<1 then 0x9a27400b43b410ae0b400ba27400ba2643e801f44c85d003f800ec5f05a0836800e150447b82b821ec5f09e0b4109716e005717c25c00d4de880b0af84e87e0b810ba33446c5f0426c5f05b003c2be3384f43f042ec5a0415020561d020a8103b0e8105315810401c30783f82f801f07f05f003c2bb042e0fe0be00622c120608190c1d0fe0be007a1fa2f82f80200d14101a081a1fa1f82f80210bc8a164505c2443700190b412e1a21b827023243f056003b0e90ec10690fc15820f8374418618191dc0857041c3185f0b61528df17e27c3f85700ac3185f0b615e1071be2fc4f87700acb185b0ac86b03e00603185b0a989e0fb07e00e0600be16291c1f60fc01c0c01702d12383bc1f80398fc1de0be00925a4ac8e28e51bc1740680431862f23aa3f82e83d01a01185f0af49f1071ba1f82b8040ca09522204747f8ae13e1e82f80530f61ce2dc54c600ce15c278270455be5aada2599d8656d559d4bd3dd2fd21d13d004ecce44d0cc84bfcac493485471c63c4542c418bfa3ec3e3bd5bcd3bf3b13ae3a5b9237eb70b5d354b4c349340b2d314311308b002fd2e42d62cdaba296282a6f25ba4824523722e9f49ba99696d14391a1010d20a307403a0005b6cb26158160176b6d972d2aecc10edcf62a1936408758b9f854322c810eb15ee9b0259765c962e9d972bb2e4c0ac5d3b2a5765c98158b5dad234243b00b16bd5a36848760162e9d972bb2e4c02c5d3b2a5765c98058a5deda14ec0b00b14becba5c98160162f1daecb9302c02c54fd6c4a7648865c2eb65932ac8aecb86b6db7688865d570b9eb624baecb12e1e3b261765c9625c2bb65932ac8aecb063f8a8645905c960cdf14cc8b20b92c13e76e89420d71582f365934abb2c2b0576cb2655915d930a5f96ccc322b926179b2c9a55d9614c3f2cbaac6b8ac0987e98a458d7158130f9b2e8b1ae2b0261bb669d63505604c3f2cbaac6a0ac0987ed1635c54158130e37968d0b2e4324187f691a165c864837d2d23424bac4906fc5a36849758920bdcb624baecb12413eb6d0a7645624825dedd10c4a2e29059bdb7218945c520b73b6643128b8a416776cc865d171482bf25cb42b12e2905de4b7685625c520c3fb72d390ca0a41a7d6c5a7219414830fed3b2e432829063dd9768c8650520abd96ed4ac4a0a4167d6dc865c541482dead990cb8a829079b5865d17150520f3690cba2e2a0a41e6d5d1835c541483ed2ba2c4b8a82907da5744c97150520fb62e8b8a82b0241adb260a265576443c765c2ecb92c48878ec985d97258910a6d972d2aecc10ed6da2c9a55d9801db9b2d8950c90ecb2dce5b121d765c962b9d36043aecb92c5b3a5d9a01d97258a9f2d894ec910cb8636cb9688865d570d2db6ed110cbaae171b2c9a55d9615c276cd994cc82e4b0636c98289955d910 else 0x1b17a2742c842146b80700352a0a950783ec1f801e87686d07e008d0ee0b400fa2740)
def mo503H8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1c13c080000168c4436300000000515006003c049740d01612d87000e0800000900
def mo503D9 (j : Nat) : Nat := if 4 ≤ j then 0 else (if j<2 then (if j<1 then 0x76585609ff2a57258560f3f5d97258560ddf655915d930cff661915c930bfd6849758930fbb5d97258930edf619755c530eef618945c530fcf594945c530e7f619745c530f5f595745c5309ff6889758530f9f69576585309ff2a57258530f3f5d97258530cff65d8650530ddf65d6550530fde5d57158130fee2917158130f7e5d17158130bfe69d4158130fde5d54158130ffc5c54158130cff6859721920cff261915d920ff368c9758920bfb6849758920ff96849758920fbb25d7658920fbb6857658920bfb29d9158920dfb65d9158920fbb5d99158920dfb6519158920aff69c865c520eef618945c520eef218945c520e7f619745c520e7f219745c520eef251835c520e7f5d1835c520dfb6a5625c520dfb2a5625c520fbb5d9625c520feb251625c520f7b5d1625c520ff9685625c520feb251325c520f7b5d1325c520ebf2a17658520cff65d8650520aff69c8650520cff65c8650520cff65d8350520dfb6a56250520dfb65d6250520fbb5d96250520dfb65d3250520efd6197150520efd2197150520efd60d7150520ff95897150520ff94c97150520fee2917158120f7e5d17158120bfe69d4158120ffc5c54158120cff6899721910cff69d9221910cff6919221910aff688985d910edf261955d910cff261925d910aff69c9858910cff2a19758910cff2619758910aff6a48758910ebf2a17658910ebf2617658910cff2619458910efb2617258910bdb2898560176bdb289955d876edb6957660876ede6957660076cfd61d9121d62ded6519121d62df96499121d62cfe61d9021d62df664d9021d62dfc6459021d62bbd684875d962bbe680875d962dbd5d9911d962cfe61d901d962dbe5d9901d962cfb261965c962bf9684965c962bfa680965c962f3b261765c962f3b681765c962dbb261765c962f3b21d765c962f3b5d8765c962bfa680765c9629ef6909760562f3b5d97260562afd6848760162f3b5d97260162cfb69d9221970cfb29d9221970cfb6859221970bdb289955d970af768c865c970afb688865c970f3b5d972589708ff6889858570f1f6957658570bdb289955d960afe2a1905c960bbe299905c9609fd6849758960f3b5d972589609ef69097585609fb6889758560bdb289955d930abf299985c9309fd6849758930f3b5d972589309ef69097585309fb6889758530fb658d7258130fb658d7158130fb658d4158130c7f6859721920bf96849758920a7f69c865c520af768c865c5209ef69097585209fb6889758520a7f69c8650520af768c8650520f6d5d17150520cdf6959721910cdf261955d910bdb289955d9108ff6a48758910abf6988758910afb6888758910f3b5d97258910afb688874c910adb2898560176cdb2a1921d965b5b289955d970ad768c865d570adb688865d570f965d56358130 else 0xe1f06d1343e0b02f03402c8ed348a02b87c1b43e0b02f03402d4b42e49827875178490c43e0bc0e00c87e9e85a0e71c0771bc5f1383e09c1310f4398b62ac7b198661584e0982b04cc7b1bc5f15e4b0fc3b8831886f1785f1384e0f82b011c6c8f02c0a0234701404e0c03e0802f0000391bc471023c0ed1c06e0f82207c02f11c408f03c0e2294701b83e0bc02c9745711a4247e1784e0f82707c0e00cc6f1023d47d1004e0f82f009c6f15d20c6f1745f1344f0f43d0ac0900d9625785a1583886f17c4f0fc2e0180331bc578831bc5f13c3e0ac02718c5c8e22b47d1bc5f0f82d07402f18c5c96c3c8e51fc5f13c3e0b41d00ca2b0871dc6f1684f0f02809c12bc92f0f3c22f023bc6ee8bb7eed6bb2cebfbad0eab3a88e993a2ce84b9c6e63b94ce47b8f0e2e388ae173838e02b7c8ddcb730dbe36d4da4b678d953644d8835f2d71358cd55351cd3e34b6d24b464d103408cf6b398cdfb35acc8b2cccaa328ec9d3264c92b1fec71b184c55b128c39b0aec1b3048c0bb00abfeafe0be52f5cbc92ef6bb72eb8ba7ae8eb9d2e64b92ae30b832ddeb6c2d8cb57ad26b40acacb1d2c28af72ba4addab3eac6aad8aaaaa86a93aa2aa81a9eca72299aa60295ca4928f6a2aa868a0ea7f89f7a7ba9e8277c9cea7169bca6ce9ad269099da65298e261e98125e0976a5c0964a58295ca54e94d251a942a4f091ca3cc8d622da899a206864a11e82fa05e8049fb27d49ede79f9e0a76d1d6872e1c306ef1b0269219f266718e261e18045e196e059615bc54d148e50193564bd9264483919043f906c3f90f663ba0e7e3800d783410c9a3070b9e2c80aa229a89d825688c820b07b81d106c619205ca146848810503a00c882c208e81bc05700e801a8000edf6158160176efb2a57660876efb6897660876efe6897660076cff6459061d62dfd61d9121d62dfe61d9021d62efe2a19021d62df764d9021d62dfd6459021d62bfd684875d962dfd61d911d962dfe61d901d962efb261965c962fbb261765c962fbb681765c962fbb259765c962dbf2a57660562dfb2a57260562f7b5d97260562ef768c8760162aff6848760162efd6848760162bfd6848760162dbf2a57660162dfb2a57260162fbb5d97260162aff29d8160162ebf5d98160162efb5c98160162cff69d9221970cff29d9221970cff6859221970f5f655915d970cff6849858970cff2619758970bfd6849758970f3f6857658970ebf2617658970f3f25d7658970efb2617258970fbb5d97258970aff2a19158970cff2619158970f3f5d99158970cff6889858570f3f6897658570ddf655915d960cff661915c960cff261915c960dfe645905c960bfd6849758960fbb5d97258960fd75d4835c560fe7250835c560f9f5d5635c560faf251635c560f3f5d1635c5609ff6889758560f9f695) else (if j<3 then 0x1401a87a082257437043e0a820a45611800d0b0258691582604691782600361e456083917826083c1b440b06d10c30f06d102c18c5d10371dc00bc07002f01c009c7218800c0606c0088f22347f004f001b001d1fc02003d1d810a46b042b001056470b1bc54c6f1745f1344f0f43d0ac0900cc6317c5b15c38c621bc5e17c4e13c3e0fc2e0ac0421885e168554711fc5f13c3f09c12e1885e168570871cc771bc5f13c3704c0619665409e1dc5710c370bc0700b1601815c1713f87f13c2f0090605705d966544f61fc5f13c2f00b0601765808e1dc5711c330bc0700b0601765a9513f87f17c3f0090605705e9513f87f17c4f0090604f22787c1b41f0070701805c4f32387c1b41f009060160544f82787619c1f00962d8a62408e1d856118320bc0600b060170584f92387619c1f0090601705815c1ec5b12c3b0bc0b00bc60570581523889c1fc02318c5c1623848c1fc01c580605705c960589505707419c5711c370ac1f01c0449b8621725550c1d06715c470dc2f01c0341805c160554a5230781ac1f01c02c580605705e1625a152544fc1dc5711c370ac1707c070121601815c17258162541523b07b16c4b0ec2b05c1f02c0481805c1613c8e12307f00813c4b02f87f1343f0bc0205e15c174589645495a1fc5d17c4d1343f0b42707c0d012c6f1502787d174450f42f0340291b45650a1f45d1343d09c1f03402d9865d90838c7715c470f8260bc0700c661970599063e0e420c7715c470f82609c1f01c0419e65d9063e0e421c5711c3e0982f01c0371bc6317c570e31886f1785f1384f0f83e0ac03f18c5c8e0388a02b47d1743e0b02f03403718c5f102380e22c8951c06d1744d0f82c0bc0d0100601745415a4247e1784e0f82707c0e00dc7b1b85e1502c0a0240871c050134300f8200bc0001185e15d278871dc6d0f827049c6f16c570f31886f1785f1384f0f83e0ac0389323b47f17c4f0e82f00824c8e3288802347f17c4e13c3a0bc0331bc545413c0f12409d1f06e1784e0bc0e00e46c5815d15a428891f85e1383e09c1f03803b1bc544f03c4b02f86e1343c0f82f0380371bc571113c0fe1784d0f03e0bc0e00cc578ce20c621bc5e1784f0f83e0ac0308ea308a22347f1784f0f82f00ac545413f8c12409d1f06e1782f0380305815d15e328891f85e1383e09c1f0380371513f8c12c0be1b43c0f82f03802f15c444fe3385d0f03e0bc0e00a6288ac2208b1ec5612c3c0902f02c0318a22b08822c6b1584b0f0240bc0b00cb358a22b08822c6612c3c0902f02c0319083908e1d86715c470f8260bc0700cc6f15c1f82f005c408e0388be1f06d1744d0c03e0b02f0340388e0388a02b87c1b45d0f82c0bc0d00cc6f1513c0fc384b02f87e1343c0f82f03803b15c444f03f0e12987e1784d0f03e0802f03803f1023b4d else 0x2c5d13429084060170581551c47707c02147700271dc009c5b12c230ac07006e1fc07003e1fc0700325415e1c3a5787b0bc01295e1ec2f004e1f06d07c01387f01c00f87f01c00f07f02c00f0781ac1f01c01707710216057c1d06b05c1f007e1f4350d41f00513e87d0d43f01401a87707c0d004c5787513401009d114330f401715e1f44d004e1f44f03401387d09410e87d0bc050044544fa1f4470740189a14008d124330cc1d008268174574490b40181761f4490b4016c7f01c00c16420c6609c1f006f01c00ac5e0a820e15048f43ac00f15d1f82f0048554671582108f03a4660ac1141b85415621c1141523e4760bc01647e09c10d1522347b0c83f0064550eb00345688f02c01215f01c00e1571d43609c016c5e1382a084b1584b0c83b01801ac5b002717847003c5747e1382f0054548fa2247e1382609c1221b823450e9ba202d16820a820543a08246b1502186e13c0100785784d0f82c08513c4902384c0c431857a2384c084a3288b178212c5b0c83e0ac06006c578cd1f82f0054578ca2247e09c1191d423450d9d6202e3209e08390c190f820b150300861b82f00401e15e3309d0f82144f03049023821457c2688e08407408090c423820ec5c102c101c10c30b040704b0c2317040b87715c30d0e61ac56044c5707e0bc01307e0bc00f15c1f82f00406e15622c17045857077143068902230730f82307c0230730e82609c0141a45782a09c1f02c01f07b0cc3a0982b01c01f87d174300c81141e6218460046380961982604561243600322d0961a4360981181ea2382a00450f82a003a1d45e09025005a1f82f003257457043a1e820a8750e820e87d1782f004e0a820943e0a820c0e42586d0d81142002284a004d340d02c09e1f4320470380b02686a0a81182002382a004a1f43e0902f))
def mo503H9 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x4208000a07f8ba0002821403f52b5c74007000304700000009107848602800010350101c454190003846c04800050240000003488000311294cdd1d1321e067c70000805c0008c5f92a8470000f22441424b8b06842102e188e4370003c11b895a0ae4a7646429000042ba82f5cc6020d08acb72093d3452a35311c2949a0000000d0db02690c24310002428c04c445a2ce4b10001402b0a4000910c000f8eccc5e0e6c00525602a0003d447096c08e0150271889816e2b6939945ca41b0b2034c00780b12e790c5112415b06911430ff03a88f6cafa43fa24491164024068337072b39e08ed070003804000e018e418085003b835c2c0000806c0000000cbb0000d1124a1c2b60b4000d42981e34c1440000220758de4b4b108000d0cb41d12d403e6cd40a35c51cc0225b93500f4000701b438000043c60ee80c83012f0c060000a48f51161403150202020b5b24002d0501036d30070017030702010a00
def mo503D10 (j : Nat) : Nat := if 7 ≤ j then 0 else (if j<3 then (if j<1 then 0xeb1282987ff64576483ffaecb8a41ffd735c520ffebb282907ff5cd41483ffb24bb221ffd9758910ffeca2c4887df615805db7fb04c02edbfd8160176fbecaaec3b6ff5d9821dbefb22bb2cbbfd9061d62dfec390eb17fb6488758affb2243ac5ff59121d62ffcc810eb17bf21d7658bdfb22bb2c5efd905d962dfec38ecb17bf5d87658affb223b2c5fec985c962ff6cb2e4b17fb2597258bfdaecb92c5fec765c962bfe4bb02b16ff61d8158bdfaecc0ac5bfd8460562ff6b9302b15ff25d8058b7fb0ec02c5bfc8760162f7ebb300b17fb5c98058b7fb02c02c5dfd925d970efec8aecb87df655765c3efaecbaae1f7d755cd70dfe432e4b877f5d9725c3bfae6b92e1bfc9858970bfecbac4b87bf5d9625c3fdae4b12e1f7d955d960fbebb2eab06ff661725837f930b92c1bfd875c960efebb2e4b07f720d72583dfac6b92c1ff9905c960bfecbac4b05ff25d62583dfaecb12c1fed7258960fbeb2ae2b07f720d71583dfac6b8ac17fd9758560bfe4bac2b07bf5d961583efaeab0ac1efd6458560ffcb92e0b07fe5c570583efb2abb261f7d765d530dfecc2e4986ff61d724c37fb0cb9261dfd765c930bfecbac4985ff25d624c3dfaecb1261fed7258930dfec3ae2986ff619714c3efaeab8a61f7d655c530fde4a2e29877f5d1714c2ffb2eb0a617fc9758530f7ebb2c2987df5d5614c3dfac8b0a61ff57158530bfecb282986ff619414c3efacaa0a61ff97258130ffcb8ac0987fe505604c37f930bb241fed9758920ff64bac4907fb645624837fb0eb8a41bfd865c520dfe432e2907ef25171483bfae8b8a41bfd835c520ff6b12e2907fb4c9714837f930b0a417fd9758520bfe4bac2907bf5d961483dfac8b0a41ff57158520bfecba82906ff61d41482ffb2ca0a41bfd8650520dfe43282906ff60d41483fdac4a0a41fed3250520ffab8a82907fe5c570483ff282b8241ff97158120ffca0ac0906ff26176443efb2abb221bfc9858910bfecbac4886ff21d62443dfaecb1221fed7258910dfe43a64886df615805db7daecc10edbf97660076dfcc13003b5df64476596feb2243ac57f99021d62bfac88ecb15fe6407658b7d930b92c5eed765c9629fec910cb875f655765c36f90cbaae1d7d765d570ebebaae6b84ff261625c39faecb12e13fc9858570e7ebb2c2b84ff648875836fb0ebaac1f5d7520d60f3ebaac6b07de5d5705836fb0ebaa61b7d865d530fbcbaac0984ff658874827fb2e43241eed76589209fecb90c884ff648864436f90eb2a2176c9261576db6c2b043b6de615801db7b306c00edbe98260076df8c0b003b5db64876596eeb223b2cb779901d9659fac890eb14fe6408758a7d930b92c5ced765c9629eec990cb84fb648865c27eb22432e13f8985c160f6cb1ac09847f65c864827bb26432413f59121920 else (if j<2 then 0x1547a321b8a85e22130683c120a8201a02846e2f1387c2a00c180b8582a0f0711f8bc4e1f0982c0342e160a83c1cc76371789c360b00c0c05c2c150783b8fc5e1f00a0c05c2c150783b8bc4e1f00a0c05c2c150783b8fc5e2700a2c15c2c150721f8bc4e1f0b038030b0160a93c1c49c3e1b8bc4e1607006960ae16278389187c371789c3c0e00d0a03c1387c371789c2e012170a84c1e08c3e1b8bc4e1f00b0c05c2c150783a0fc5e270f85c03030170b0560fc5e270f84c1e0160e0571f8bc3c170070b03b8bc4e1e0b80385c2c14070278fc5e260b8050602e130783811c7e2f138702e0188a8471f8a84e1c0805c0242c0ec3e1b8bc4e1e0b8048381587c37178782e010160a0381387c37178982e015125111eb11971155110110ad10470fe10f330edf0e8b0e130d890cff0c750bc70b3d0ae90a8309f9098108e5086d07bf075906e1067b05df050d048303f90327029d01cb00f9004affc0ff48feacfddafd3efca2fbd0fb34fa62f990f8bef7fef72cf65af5e2f510f41af348f240f1c8f150f0c6efacee5ced0cebbce9a6e856e772e5c8e4aee35ee28ce196e046df50de6cdcc2db60d9c8d866d794d644d476d326d18ed02ccecacd8ccc3cca80c954c7e0c6eac5f4c4b6c3c0c2cac17abfacbdccbbecba42b916b7c6b664b502b3e8b2aab100aff8aebaad46ac3eaaeea9e6a902a7a0a5d2a470a356a188a0389f309dce9c009a9e98e29780961e94bc93a291f890f08f7c8e088d128bb089f488da87e4867084fc834081a8807c7f747ddc7c207af4792677d676987500739e72187122702c6f486dd46d026be86b1669a2681c6672651064086282617a604e5eec5d425b625a2458d4577255fe547852bc51364f8c4e064d104bf64b00498c484e472246084482430e41e2405c3e8e3d743c6c3ab03984383436c03582340e331831fe308a2f042dd82cbe2b4a2a8a28ce2790265224de23fa228621a21ff81e961dd61cf21bc61a64194a188a16bc1548147612f0117c10080f900e9a0db60cf60c360b760a92099c08a607f807260642057004e6045c039c02b8020a015c00c00001ffd9060976ffec1300bb7ff605805dbffb24bb0edffd9161d62ffec830eb17ff61c8758bffb2043ac5ffc875d962ffec8aecb17ff61c7658bffb0ec0ac5ffd7660562ffec2302b17ff61d8058bff90ec02c5ffd8160162ffec92ecb87ff659725c3ffaecb92e1ffd935c970ffeb9ae4b87ff65d625c3ff92eb12e1ffd9158970ffec92ecb07ff64576583ffb2cb92c1ffd765c960ffec8ae4b07ff65d62583ff92eb12c1ffd9158960ffebb2e2b07ff58971583ffae4b0ac1ffd925d930ffec8aec987ff659724c3ffaecb9261ffd915c930ffecbac4987ff25d624c3ffb22b1261ffd765c530ffeb92e2987ff589714c3ffae4b0a61ffd7650530ff else 0x3a9a0d05a2813878321a8a05a22128603c14090481e050100ba551e8ea683514880461e0d4502b10894301e0a05c0a020154ac41214d8421e8943c140905c0a01a9b49a429a4a8421d8844a1e0a0482e0500f2ba3c9a4904e1e8b0522e1305c0c01a5e2bc542b13084201187832198b84a231187020170180a15e2b13083361008c3c190cc5c251188c3e030118ac4c210e274201187832198b446230f80c0422b13084399b080461e0c86a231187c0601f1e8d85c2a9207839168ae3a1b8a85e22130782412078080563d1b8bc57250f876218e47c331b8b85e2613078260a0548da5d1e8b4551c0dc542f110983c120b8080412f150923e1c4b250228f06c29170844c180f0402e060080ac6c2b118823c1e0e45a2a8e06a2a168884c1c0d07828120903c0a020190da5c2b1147d1e0c46c2e13078260f03007a5e2a1588a411f0e23e170983c170300746c2b104783d1c8b0551c0d4542d10098381a0f050241207814040311b8ad218f46637168bc4a270e874260b008080602e160a83c1c47e2b1788c4e1b0f84c260f018090602e160a83c1d080471d8dc562f1189c36190983c06028180b8582a0f0731d8dc562f1189c36190b80c0442c152a0389248c3e188dc522f1088c321f08858100e0142f078b018279241387c371789c2e01a1c2c060ae170a93c9008c3e1b8bc4e1f00f2f16030160a93c1c4904e1f0dc5c2f130883e160b818050b0182b85c2c15278389008c3e1b8b85e261387834170300a8602e960b2542a0f45a260fc5e270f85c06020580c15c2e160a93e0e06e2f1387c260f00f0c8581e0e0582812c76301b8a05e20138603c100b8000523715c431d8dc5e270f04c12a30188b85d2c0f4722d1489a3d190dc542f1109c341e09054100d0184d8602e95486228f46e2f1387824150681002022180bc4e214ac431d8dc5a270f050260b0100404636150702c14090451e8c06e28178804e180f0402e000140d8602e15c451e8dc5e270f05c0323d1b0b854160a048238e06e28178804a180f0402e000140f06c2e15a4e238fc5e250f05c03036190c05e2a0f0702c140963b180dc502f1009c301e0805c0002e582ba55264f4451e8c86e2a178884e1a0f0541a000138dc5610c76371689c3c1304a89c42958863b1b8b44e1e0a04c130b0578ac4c9e0f874218ec6e2f1309c360b0102c15d2a4f472291147a321b8a85c270d0782a0d00009a541e88a3d190dc542e138683c150403403e2b0c8431d8dc5c241386c128389b0c05c2a0f0702c14090461f0c06e28178804e180f040200f0000c8581c0b050241187c301b8a05e20138603c100803c000281b0ae220e06e2f13878260f00b0fa782e160702c1408e381b8a05e20130603c100803c0002b1f8b8581e0e058298ec6037140bc40260c07820170000a2602a8f0722d)) else (if j<5 then (if j<4 then 0xc0401c582ba542a8e452228e06a2a170904a1a0f0502e050100a2743a95079391008a381a8a85c24128683c140b8140402895c64228f06236170983c13078180362b8c0612c9208a3c1b0a45c20130643c100b81802027150a93f180c258289208a3c188d8522e10098321e080441e060080c160ae15c66228f06236170983c130781803cb0578a857188823e170983c1703006978ae950aa391488a321a8a85c24128603c140b814040289d0ea541e4e440228c86a2a170904a180f0502e050100a178af1588e3219098431f0d46636168b848250e07828130502c02030958893b190c84c218f86a331b0b45c24128703c1409828120ac57cae309209c471f0cc542e128703c1703008150a38c45c270cc542d0e0643c170300715e2a5488e301849048230c46c29170804a1c0f0402e060080b4542b1127e30184b050230c46c29170804a1c0c87820110781802030570ac44a38c84e230d85c250e0643c1703008178af158893f190c84e2210c7c35198d85a2e12094381e0a04c14090592f054a851c622e1388c33150b84a1c0c8782e060122bc542a540893f184904a230d8562e1305c0c022574a93f180c259241208c311a8b05c20128703c100b8180202c9547d341a88045190d4502e12094301e0a05c0a020134ad37190c84c218f86a331a8b05c24128703c1409828120ab1527432100863b1709044230f80c0362a4e8642010c662e12088461f01806c559b0c840218d848221187c060191b0a83c1c8b452270e86e2a178884e1a0f048240f0100a46e2a9083b1588c3c120b80c02e361b8aa4111070331588c3c120983c0601f1b8aa420ec56230f0482e0300b2f15d2a15882391187835150b444250c0782817028080503c9549c401e4e440230f06a2a168884a180f0502e050100a846208e0722d1409c3c190d4542d11094301e0a048240f0280805c3d992be561e4904e230f8662a178984a1c0f05c0c0265428a2e138762a1709438190f05c0c01c1e4a8541e8e452201187835150ac42250c0782817028080552b104813a1087a2d1287828120b814039371549a40950843d158844a1e0a0482e050102b854a88f45a289209c3f150bc44250c078241701009c6c33152a4451f0e248241187036148b842250e07820170300405e37150ac44204f07c38964a0461c0d8522e1089438190f040220f0300406836570ac44a28f84e230f85c250e0643c170300886e2e152a1451709c461d8a85c250e0643c170300946caf150a950228f27c3892094461f0ac5c260b81804c32574793892090461c0d4582e10894381e0805c0c010142ba56208ea68351008c3c1a8a05a22128603c140b8140402a9b0c95c2e9527a389649048230e06a2c170844a1c0f0402e060080c255271047d341a880461e0d4502d11094301e0a05c0a02015882 else 0x9f87a2b1688c4a190e84c2e050180997834570b8582a4fc3a1b8b45e251287c2a130781404cbc180b950a3876291688c4a190e84c2e0501808978ae178b25a2a9527a1f8b45e251287c2a170280946c36190c05c2a4f0712c9449c381b8a45e21138643a110883c020311b8a9409f87a2b1688c4a1b0e8442e050180846c37150a9401187435158b446250d874221307814060281b0c8549f87435168943a1307814036361b8a854a04f43d168943a1702806c6c2f15289430f4562d1188c321d0885c0a030118d8602f154831d8ac461e0905c0601a1e8d85e2a906331588c3c120b80c03637188bc561cc723e198dc5c2f1309c3c1e0982814936180ba55200f4751f0d46637170ac5e261189c3c1b0f0482a040080cc6c30178b456271007b1f0d46637170b45a24138783a1e0a04c16020080d46031170bc401e8e0722d1489a381a8a85a22128683c14090481e050100d0602e95882411c4ea3c188d85a2e128983a1e0a048260f0301405d36180bc552690a3d158844a1e0a0482e050108d8541c8b452268e06e2a178884e1a0f0482e020128dc561c4b251268f06c29170844c190f0402e060080986c30170ae228f468311b8b85e26138783c130781804e36180bc542a9007c388f85c260f05c0c01f1b8b4561ec723e198dc5c2f1309c3c1e0982814536582ba592a9007d1f0d46636158b846260d8782415060340202e950aa4d1147e2a178884e1a0f05c0401c9b0da2d1489a381b8a85e22138683c120b808044b0574aa4e210e4451c0d4542d11094341e0a05c0a020144da562108a3c188d85c260f04c1e0600e4d86d2b0e440228f46e2d158844e1d0f0502e0501249a409508a3d158844a1e0a0482e0500e4a855268e440228fc5e261387c03237154792c9449a3c1b0a45c21130643c100b818020271b8a8409e0f0712c94490451e0c46c29170844c190f040220f03004064b0570b056209047d1e0c46c2e1307828120983c0c0271b2c15e2a90478391047c2e130782e0600f4d86d2b118843c1d098431f0d46636168b84a250e07828130482c040329b0dd5d2b0e440238f46e2d158844a1e0a05c0a024934812a1146a2b108943c140905c0a01d1b2bc54a911479270c46c2917084481e0805c0c010138dc5622102783c1c4b250230c46c29170844a1c0c87820110781802032570b0562251882411f86c2e12870321e0a0482e060132f46caf168ac46208f27b1f0d46636168b84a250e078281305024160bd170a950a310486198a85c250e0643c140905c0c026582bc56261007c391d080431d8b846230e0402e030132f15e2b130803e1c8e840218cc5c2311870201701809c5719886391f0cc6e2e1709c3c1e0982813cb0574ae3119884451f0d46636158b844260d8782415060340202e950aa391488a3f150b84e1a0f05) else (if j<6 then 0x6009876270180261e0d41e030054a8570ec2e00a160a83b0f064350583c0270e8662e004c3d0780c0130f4321f0280c0183449c3a1983c0a00f8722d0c87c0a03007c3d128442e050180386c2a48c3a1a88c1e05009c3d128442e0501803b1f0482600947c120b80c0168e46c140904c1a00f474260905c0600d476221089828120a8044568f824170180306e2a154451c8d8260f0098aa228fc0600b1563e130482600d1562e130482153695a3e130482e030080da541f08a391b098241306805a6d114762e1380c01e2b47c260905c0600e168a83911478311b098260f00b8ad1f09824170180386cae9584517094321e0904c12cbc1b4a92610c7a2e13048260161b2b92510c7c260a04c0262b8c462218f82600f15c623110c5c10c95c62311147c1701804257190c4642111472360983402f188c4451d8b82e030088ae311888a3e0b80c0222a15c62311488a391b04c1e01715c62311147c170180415d2b0c464211145a190f04c12caf0c4642110c7a2d0c878260165e4ac311849842218f45c1300b2bc31190924c2110c7c1300a2ba549b0c461261088a1e09825a549b0c46126108863d0f04c02d33154461d8b801a32992ba561088a2d0c86c1c017194ca4d210844515094321e0905803532574ac349a498422286c1c0169949a421a4d2512610884250f0482c01d178aa4910c7600d15492228fc0600c94492228e85e030078dc558f46637168bc4a270e874260b00807c6d30978a9418e46a2b1688c4a1b0e8442e050180927a36978a944a146635158b446210e8442e05018094622f168ac398e47c331b8b85e26138783e16098290602e160a83c1d0b8542611478311b8b0562f1208c4e1c0d87c28130983c080301d2f15e2c168a8570f86637158bc46230f84c2c020124da570fc562f1189c361b0b80c030b0182b85e2c968aa549f87835158b446250d8742615078140602e580c15c2e960b2542a4f43f1789c3e1700f2b9501c49049230e06e291788446190f8442e010122c060ae1727e1f0dc5e270b80596030570ba542a4fc3e1b8bc4e1f00d2c060ae170b0549f87832198ac461b0a82c1e030122f15c2c1548e1d0cc56230d85c0601a1b8c45c2b874331588c361701806160af168ac39168a44a230f06a2a168884a1a0e8482a0f0280805cb0182b85c2c152783b0f06435168943a150583c0a026570b0552249049230e06c2917084461a0c87c2c110b8180202c580c15c2e960b2542b07e2b1788c4e1b0f84c2e030132c15d2c9583b1588c361701805c60b1172ba582c950aa3a0e0662b1186c260f0180916030570ba582c950a93c1e8e0741c0dc562f1189c361f0984c1e030192c060ae174b0592a1527a3a0ec56230d84c1e030120d0602c1527838964a2461c0dc522f10894321f088441e010162bc592d154a944 else 0x51d89c06008c7a250884c0158b44a1108463e05801e1d8bc0)))
def mo503H10 (j : Nat) : Nat := if 2 ≤ j then 0 else (if j<1 then 0x5a15501a7871f50d6535b02c000068370001825d86380005499b10a73b8000e38779c514b68bea37932ec051623a0000799800028910001e1980000000fa1666a5cad682991a12a1d1500000f0ab06a3a58a3070000c7088d540d1900ca9c40000000f30c0000000000051000000000415e6190c73400022d5d4cc6694000782a0001e24000000000000e0fc00011bb004eb1f00000a210001c4b755379ac0001821e46280000001112ec1300006cd499900000000d06400034467083e4c80002c4200000000000000000000000e475a16680d2316f97c0004879c3348675c85ea08152104c4438800000000003d1a4075d0ee00000170000c0f000020058638a8f601d9c4162c50000297f03a00000534c064c1c0000c330d08c000323ff174000000069c17d3ae2dc000000041360000812e0ad045800000000000403ea2d00006813b1434175101c8140001c17045e304900006108000000000000002e52b6a90000c36311000002115130c0635c44543ee2174c851418048c739401d480c4ef61b582b308904cf2a27c360000e59000000000000000040d83438e0522fbc0ec0004059591400000000000b497c49ef136a4f917762a000020057cdcc2b000000000001a23ab3904d2812c000000041160000000000000007cf209226448000b19f935400000000001f0f69520000807c00000004835808b26cc0004a6a303089cac578a6e0000000014c80000000000282700000000000000052a3e444466c0000ca400000003b160000d52600000000000e543a33281080005988580c0006482f0be00000003c34651000000000000000000000000000105a632fc2a00810001a079b6ac05300000000000493ff09aa6640000000209800000001a2a000010c000059b80001e310000000049a000000000000446e00024358cc2d5380000d0d800030cb3884000508db162c970c4a18b60001604acc700001088000000000000000000000029d4712423240000000303666d871a68b990fa00025656332202a000000000000000000026780000000c61341c986470f5228d86958bf916b030c0000000aa0f320ecda0000d08e52cc0000000c44a00024a14e62000185ccc1600007537435c000497134b670c693cf89c90fe0002224530b00008adc00011b7000121f800000006044e022c2c0000984d6041640ca9e6c25aa4800044c10001e03c00000000000c0f0869800000414893814315f75140002a5eb18572d60000e1c466fe43400014235c3a185266844ec02120001ba20483891491a8a44c00000000000000010c32960060c71e31006880002c01800044440027420121530081000822010010002470c00060440412840050010cc04434f08b0801c00c32801030880c10000401830410c4381300002000000203043083001901041006007 else 0x102a696581cf000000000000a0a6ce63920f10100700000000537e94500000000000780200000000a20500ca52a0003d1f000000012a30000000071320045725800000000000139ec7d0000d0564be404b8035c0734c10000711e0003c1800000001669c930266500e7069900bc023380ac27fccb00c2f0c4a028850105720c3e8714c0a630c1aa3add0668611f07b422f65f0000e0c00003932813bd170000044d0000000108d80006c7f1d48000000051180001a29763f2a38159269757115a62018181ba8280000a42200000007a9d000112d0000000000000000c350000000000000000000d916419c000005ae553c81a5e2b834722b81bd834789580e020768651031810c000394780000000000182780008806624e800b0330000000042f00000000000000000000000f8380000000e0940000817b205000000033543098000001c934e11470000816f919000041542839c6080005008689a65600008081e02694a4a0980d2000000018a4100122f7044007c000000000000000626400000000000a074a18d00704c9787c02c9ce9ae7000010a3ba57a02b108600014b008520000068e0246217a52200038bd0000c13c033b853c816613b6298000197f051608ec65e7a7020a2c5890208000000102bbb4d8000e166000000064ccc1572584000287b0000e8c00000000000000000007123000000000002a)
def mo503D11 (j : Nat) : Nat := if 3 ≤ j then 0 else (if j<1 then 0x6c505c404c303c20201c00054605e1e181b17130f090700b1817161507c5c4c3c2c02858382c28271c1b141710130c0e080807000121b151088c7c5c4c38202c02e70605e543e211e191b161712130e0e0905000131b150e88478646c585c484c383824101406c4c412a231f15130e080b00c151308c706c505c404c30382c000386c605c3c2c28271c1b141710130c0e080807000149b1817950f88478646c585c484c383824101486c58543a211e191b161712130e0e0905000121b1508c7c544c382c0244c412a231f15130e080b00b15130e08c7c5c484c3c028543828231c1b1416130c0e0b0000e150f08c706c50584c30382c00034605e5632211e191b1616130e0e0904050158c88478646c58584c383824101385430231f1610130f00915130e088786c505c404c30382c0003c70605c3c382c28261e181b141710130c0e0808070001615130f088786c505c404c30382c0003c58382c28261e181b141710130c0e08080700013150f0e0a088786c50544c30382c0003c6c5442201f17130e080b00b1b9513104a8807c544c38202c034544c221e181b171211130f00c15130e08878606c5c444c3c0305c54504c3c24231c1b141710120e0b000111f160e0b0ac706c505c40483820201c000467c6c56483a211e191b161712120e09040511715140f0e0908c706c505448382c0004054504c3c3824211d1b141710120e0b000111e17151308c7c5c4848303c0307854504c44231d17120c0f00c181716150f0ec5c4c3c2c02c605c583c38231f17130f00bc8f31c6c3c305abf92f3eb9c2d9ab432c96af02ae2a85293ea16278a9ab25ee93e241a8d9229e87c21228151f9e7b21de27391bf66c81a3264f183e5d6166a58915a653e149a50313ae4c8128a481115643e10a24030fae3c40e8a3890dae3420c722f70b8e2cc0ada29909f625c08fa22b082e1de06fa19705de160051212b04460ee032a0a70216062012202f005e0003ff60976ffd805dbff5d876ffd821dbff61d62ffc8758bff5d962ffc7658bff60562ffd8058bff5d970ffd735c3ff5c970ffd625c3ff58570ffd76583ff5c960ffd62583ff5c560ffd61583ff5d930ffd724c3ff58930ffd714c3ff58530ffd414c3ff5d920ffd73483ff5c520ffd61483ff50520ffd76443ff5cd10ffd43443ff58910ffd32443df61576f7d851daff60876fed821daff60076ff9801dbdf5d965f7c76596ff61d62bfc8758bbf5d962fed7258aff21970dfd765c3df5d570f7d655c37f5cd70bfd87582ff21d60f7d75583df59560fdc83583bf58d60ff970582ff61d30bfd864c3df5d530f7d654c3fe58130bfd87482ff21d20bfd86482ff21920bfd83483fb58920fed32483fe5c120ff960482ff61910bfc86443df59510bfd83442ff60910ff970443fe50110bed821dafe60076 else (if j<2 then 0x5c58543c3b1e191b1615171211130e0d0f0a090a0507020101a181716150f0e4746c545c444c343c242c0404858561e1b151711130d0f090b0100e581857171615878606c545c444c343c24241c04050605c58543c3a1e181b1615171211130e0d0f0a09090702010195818571716150e878606c58545c48444c38343c2824241c08040697d5c5c5855261e1b151711110f090b010111b15488786c545c444c34342c040386c605c54403c3a231e191b1615171211130e0d0e080907020101a1b181716951513100f4a88c78646c585454404c383438202c080406e70605e5454403e211d181b1615171211130e0d0e080b02010191b181715100f0e8808474606c58545c48444c383438202c0804068786c5c5444403c39242620231e191b1615171211110c0e080b020101c1b1615100f0e88c78646c58545c48444c38343820241c08040666c6c605e54403c3a20211d181b1615171211130e0d0e080b020101b1b1615100e88474606c58545c48444c383438202c080405d787a6c6d5e5444403c39242620231e191b1615171211110c0e080b020101e5f1b5717161511100e4988c78646c58545c4844443038202c080406c56303220231e191b16151610130e0d0e0809070201016181795158c0c8808474606c585458404c383438202c080406056303220211d181b16151610130e0d0e080b02010155e9515118c0c49098808c78646c58545840443038202c08040657d5c54463031242620231e191b16151610110c0e080b0201019954d8c0c49098808c786464505840443038202c08040586c6454403c3a20221e181b1615171211130e0d0e080907020101a1b1916951513100f4a0a8808878606c585454404c383438202c0804071787a7264655e545444403d242620221e181b1615171211110c0e080b020101f5f1b1957171511100e49098808878606c58545c4844443038202c0804076715c5e54413435242620221e181914171211110c0e080b020101a1e1b1715921211100f0e8808c78646c58545c484448303820241c0804074786c5c5a54544e4848403d282a20231e191b16151510120c0e080b020101e1e1b18171695151413921211104a0a8808c786464505440483038202c080407e7c6e5c5c56484844403a20211d181b1615171211120c0e080b020101c9f1b17169515139212104a0a8808474606c58545440483038202c08040751c1d1b17130f09048181716150f0e470746c5c4c3c241403c605c58542c2824211d181b141710130c0f080b00015181716150f0ec5c4c3c2c02c605c544c231c1b141710130c0d080b00011181716150f0ec7c5c4c3c02c58543a1e191b151711130d0f090a0600011585716150e878646c545c444c343c2428180482c2824221e1b141710130c0f080b0001018170f0b0a09088786 else 0x605c58551d1b151711130d0f090b010101b1548c746c545c444c34342c0403860))
def mo503H11 (j : Nat) : Nat := if 2 ≤ j then 0 else (if j<1 then 0x313000018b300000000000000000000000000000011a60001694c0000000c555405034980000001c934c2668600d86a333d1cf84f00000002808b03700002383b4d4410d0e5a5b400040efcb800003800100c00002737c09786b53636362933000044936354000000081e200014a146f77d0fa04d136b84af90c5b944858051c040ba4000730cb43d9e34e8542c9e98bee0e800000003a72c72991d0000908ea0ec0007940f4d7393880bc04685a4e90c00000000001c9f98514a36311c60f604a35c10000000000000000001a02800000009508000000000009db8000000000003546000000000000000000000068c2000100f994cfa740000000204dd1c97011aa304e0281e519e0002f22d0e10000e38c00020656482073096a5e550103392ce70000078b80000000706e0000000000380000001099375ea0690000000106c800000000000000000000017af806d800079b4000374880000000000000041391397e68f0388000b25e00000000000e83063a2e9d800000000000000064a0000000292c800075ab67060990000f1a934f673f008a000041680004283c747e7bfa42f81652fda9840004e9b00000001342000000000000000000044b0000000000000000000066fe4e10000a105719d8635d84e9cec5ab1b401a4a0958e988d65c68a9e481c3826f07e00000000000e0e989790fa000000000000000598100000000000409c618e00024b706360000000000000000000000292b000031e985f4000487b7464000000018aba9d0000354e10b300000002815800095a204ec51669e040e60000817914ef3360001b62e878c1d241e53461886121fc4f400058d7ad8c0003d6f54120001dbe15410000c049f842c2d8e28a0587a0dcec00c8690e00000006c0c000165a5248000000000000b6a80000000000357c0ac70000000000000000000693146f00000000000084ee2d6183723d80001805c46914e3119e1d6784a00035310000000160a8000200648bcc0a303b800070a40001cdaf01a000000020628000a9380000b72064f00000000000000094cea9fce74cadbd5cd014c471022a41d681b000000000000000082b000044e1f9400001eb8450000000ea8000000000000004246b55a80ca007ba8f218cc75e00fb2100000394d80e0000b1b5890ab6f2430e178993514b12b8747ea39253e4092993b41f00005a6a198000032580000a1000000468800090c5639c842bae7ccbdf3dec00d8a01173619dce8693810e0000000000007dade7a000030b0000061a8000564900000000000786f41bea306400878f2102b0840381ca122ca21810b7b8210012a418410114048800030a701c0351049c04061802220121134253807500803084254806298402424801000208080785e3080403020c600650090c21822130420881118080 else 0x5cb20001e1c80000001a56bc0a895271da000010698a981ef90a8a422460b04462b000058e6cc875a6674f085ffcfe7b6e9e080000001c5b093611c5e41d592244b000000005388c118000a58609bd82691530001da0056480000000a376cef38ba60a15b13cfb0866000120b8000188b14be0001d58f0a51d1ee8b46504c9270b079f0418da9300000003453dacbf126429000000009d1d62255109cbd00c8a8df0344a9a81320000000488721d5a26865f65bf000121d40000000c9ce00000007888349c00021476ae5d17a000042e000092de000000058be000043cc847940af67660cdc4832b90c240000c1a00000001227c41a80f2d67b2b4f4249100838cab30000000000006434000000000000003821e99dc2be06010de4018000000015228000000000000000000659400011442a55000000000001a4b737288bc00000000000e2c8816800024dc00000007a7de1dcc2988ac000099d4324c4df8e9c000183e000000005192e0080000000686d80a7cd688440000000024f8000519a00f340860598009e9a244180002187f95be4d3c5a41056084d687057006d03b356ee854e0c2a2b8005800039e60001804e950208bc9a40000000c1ca0001e6c000074250a4400000000000000207a88a1004f824400000000000000053c0000000042fe8068000c4806997310f84ba5dec37114594f10000000000010c400010a040003adf0001876d842785d000001f914d8000000022e000030034c54c07632678b7755c42aab3ee338d0f43b98cf680000001c2c5e59ecf80001298c0000000000000000000000a1a00003867000000002bdc000045b8943206c00002c572b31b74000000043061961163000082a946944780000f305817921704d98d2d255c04be8af22620000000000070fa00000000000000041b4c51f14361817b9ec5d80000001e230000684ed53c892ac82a8550001e59c00012150001d24400072480001410883f904864f40003f45a095c50f4a4000069c40001c0c000000000001406711400000000000000000002971d0d0b6ff4330001632800068390001493d020000000000000000417a0000000000032bd000162b40608000e13c8236c5b28b4000000000006a77a0ed294396e0000457d048c0000)
def mo503D12 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x470d142c4090c1c2040600034c172c563868a16204860e10203000221c3450b1024307081400061c2a223868a16204860c1400071b2a223868a16204860c1400071518223868a14243060a00034e192a203868a16204860c1400079f38549088e1a28588101828000f0e1a2c4870808f8ed41233bcbb22a5306e007fd76ff8edff58bfeb87fd60ffa61ff483fe8877d65
def mo503H12 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x34173c837421145a128a1a00da41400094eb241d148b4800014326520f0048e213b00054160008007c4a0c4a00011071066632d07ec08100fc1b0001a29c06bc84d03c9388014c4b008121dc4c1b512003b1152eec0be4d1821bac284f988490080f351dd2d69028038c38341b8baf09b41e946c0000000c1d8483c50205704cb9259350114418dcfe743001a8372ce012410d021f40fac4374520257222cb36d1bb34f2c182b000120c2090000f922321c30062f5011536c219e06c50a7297acfc33dca980a3914c3688dd8126cd6844d52dc1c84a5409b40e31dbac903b1444000f104c470420049c120427631000040b0308449ea1ae20e93d20f483552fcc0c5cda43f00022439214c3000004cabc6c6000000000b0bd823a8c0839a136029653312164fa41430890b621398133944000704660f54aa14330ebe2ab518c2ac0bb8312abd5b3a102532f0b652fa11a428c546042804313fc100bf0c002f13000e2617142a56006f433007016a15090a1c03011590000d000001021c022b0e036e0006010d
def mo503D13 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x71440c2006ff
def mo503H13 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x194400000001a04001a321000000000000000622b100000000000000000002a400199000491000000000008c4003e100000121000000000000000000000000000000000050000f4c088007c5e4a000000000000000000000081872d8200000000505000000000000000000000000000000000000002c1800001e1d0
def mo503L : Nat → Packing
  | 6 => (1,7,6,0,0,0,0,mo503D6)
  | 7 => (9,6,6,0,0,8,0,mo503D7)
  | 8 => (73,5,6,0,0,12,0,mo503D8)
  | 9 => (217,4,6,0,0,14,0,mo503D9)
  | 10 => (249,3,6,0,0,16,0,mo503D10)
  | 11 => (83,2,6,0,0,14,0,mo503D11)
  | 12 => (9,1,6,0,0,10,0,mo503D12)
  | 13 => (1,0,6,0,0,0,0,mo503D13)
  | _ => emptyPacking
def mo503I : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 1 2 0 4 0 0 mo503H7
  | 8 => lookupWord 3 23 4 11 4 3 mo503H8
  | 9 => lookupWord 36 181 8 14 7 3 mo503H9
  | 10 => lookupWord 119 769 6 15 8 3 mo503H10
  | 11 => lookupWord 145 937 5 15 8 3 mo503H11
  | 12 => lookupWord 45 197 8 14 7 3 mo503H12
  | 13 => lookupWord 6 89 1 11 4 3 mo503H13
  | _ => fun _ => none
def mo503 : Forest := ⟨1527,13,fun i => mo503Y[i]?.getD (0,0),mo503C,mo503A,mo503L,mo503I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo503P6_0 : block mo503 6 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo503B6 : block mo503 6 0 1=true := mo503P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo503P7_0 : block mo503 7 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo503P7_1 : block mo503 7 1 8=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo503B7 : block mo503 7 0 9=true := (@block_merge mo503 7 0 1 8 mo503P7_0 mo503P7_1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo503P8_0 : block mo503 8 0 12=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo503P8_12 : block mo503 8 12 61=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo503B8 : block mo503 8 0 73=true := (@block_merge mo503 8 0 12 61 mo503P8_0 mo503P8_12)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo503P9_0 : block mo503 9 0 6=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo503P9_6 : block mo503 9 6 70=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo503P9_76 : block mo503 9 76 96=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo503P9_172 : block mo503 9 172 45=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo503B9 : block mo503 9 0 217=true := (@block_merge mo503 9 0 76 141 (@block_merge mo503 9 0 6 70 mo503P9_0 mo503P9_6) (@block_merge mo503 9 76 96 45 mo503P9_76 mo503P9_172))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo503P10_0 : block mo503 10 0 21=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo503P10_21 : block mo503 10 21 34=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo503P10_55 : block mo503 10 55 96=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo503P10_151 : block mo503 10 151 40=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo503P10_191 : block mo503 10 191 58=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo503B10 : block mo503 10 0 249=true := (@block_merge mo503 10 0 55 194 (@block_merge mo503 10 0 21 34 mo503P10_0 mo503P10_21) (@block_merge mo503 10 55 96 98 mo503P10_55 (@block_merge mo503 10 151 40 58 mo503P10_151 mo503P10_191)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo503P11_0 : block mo503 11 0 2=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo503P11_2 : block mo503 11 2 45=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo503P11_47 : block mo503 11 47 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo503B11 : block mo503 11 0 83=true := (@block_merge mo503 11 0 2 81 mo503P11_0 (@block_merge mo503 11 2 45 36 mo503P11_2 mo503P11_47))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo503P12_0 : block mo503 12 0 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo503P12_1 : block mo503 12 1 8=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo503B12 : block mo503 12 0 9=true := (@block_merge mo503 12 0 1 8 mo503P12_0 mo503P12_1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo503P13_0 : block mo503 13 0 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo503B13 : block mo503 13 0 1=true := mo503P13_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo503T : checkedTables mo503 13 := by
  intro k hk
  interval_cases k
  · exact (rfl : block mo503 0 0 0 = true)
  · exact (rfl : block mo503 1 0 0 = true)
  · exact (rfl : block mo503 2 0 0 = true)
  · exact (rfl : block mo503 3 0 0 = true)
  · exact (rfl : block mo503 4 0 0 = true)
  · exact (rfl : block mo503 5 0 0 = true)
  · exact mo503B6
  · exact mo503B7
  · exact mo503B8
  · exact mo503B9
  · exact mo503B10
  · exact mo503B11
  · exact mo503B12
  · exact mo503B13
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo503G : graphValid mo503 (boundsBefore KM471) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowM503 : Lower false (varsX 503) (graphGoal 503) 14 := lower_forest (g:=mo503) (i:=0) (hints:=4329571924) (before_sound KM471 VM471) mo503G mo503T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KM503 := extendKnown KM471 14 [(503,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VM503 : Known false KM503 := extend_ok (m:=503) VM471 lowM503 (by decide +kernel)
def mo511Y : Array (Bits × Bits) := #[(0xffff000000000000ffff,0x55505550555055505550555055505550555055),(0xffff00000000000000000000ffff0000,0x33053305330533053305330533053305330533),(0xffff00000000ffff00000000ffff00000000,0xf000f000f000f000f000f000f000f000f000f),(0xffff000000000000,0xf330f330f330f330f330f330f330f330f330f),(0xffff00000000000000000000ffff,0xaaa0aaa0aaa0aaa0aaa0aaa0aaa0aaa0aaa0aa),(0xff0000000000000000000000000000ffff0000,0xcc0acc0acc0acc0acc0acc0acc0acc0acc0acc),(0xffffffff00000000,0xf0ccf0ccf0ccf0ccf0ccf0ccf0ccf0ccf0ccf0),(0xffffffffffff0000000000000000,0xf000f000f000f000f000f000f000f000f00),(0xffffffffff0000000000000000000000000000,0xf000f000f000f000f000f000f000f000f000)]
def mo511C : List ColumnInfo := [(8,0,503,0,14)]
def mo511A : List (List Nat) := [[],[81],[16,84,135],[16,64,80,135],[64],[64,81],[80,16,65,135],[80,65,135]]
def mo511D14 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x3ff
def mo511L : Nat → Packing
  | 14 => (1,0,1,0,0,0,0,mo511D14)
  | _ => emptyPacking
def mo511I (_ _ : Nat) : Option (Nat × Nat) := none
def mo511 : Forest := ⟨1535,14,fun i => mo511Y[i]?.getD (0,0),mo511C,mo511A,mo511L,mo511I⟩
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
  · exact (rfl : block mo511 7 0 0 = true)
  · exact (rfl : block mo511 8 0 0 = true)
  · exact (rfl : block mo511 9 0 0 = true)
  · exact (rfl : block mo511 10 0 0 = true)
  · exact (rfl : block mo511 11 0 0 = true)
  · exact (rfl : block mo511 12 0 0 = true)
  · exact (rfl : block mo511 13 0 0 = true)
  · exact mo511B14
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511G : graphValid mo511 (boundsBefore KM503) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511R : Impossible false graph 14 inputs.toFinset := by
  rw [show graph = targetOf mo511 by decide +kernel]
  exact root_index (g:=mo511) (top:=14) (i:=0) (before_sound KM503 VM503) mo511G mo511T (by decide) (by decide +kernel)

end PEqualNP.Outside.L_meta_10992
open PEqualNP.Outside.L_meta_10992 in
theorem PEqualNP.Outside.L_meta_10992 : ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 9 (fun x : Fin 9 → Bool => (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 6) || (x 0 && x 7) || (x 2 && x 7) || (x 4 && x 7) || (x 1 && x 8) || (x 2 && x 8) || (x 5 && x 8) || (x 7 && x 8)) t → 15 ≤ t := by
  intro t hs
  by_contra! small
  obtain ⟨C,hf,hsize,heq⟩ := hs
  exact directSplit mo511R g511R ⟨C,hf,by omega,heq⟩

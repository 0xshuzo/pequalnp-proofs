import PEqualNP.Defs

-- The two-mode live-state and cofactor checker follows L_meta_1674 and L_meta_670.
-- The graph, restrictions and all search certificates below are for L_meta_34784.

-- Shared forest and cofactor certificates from L_meta_1674 and PR 11111 for L_meta_1677.
-- The original credit line is retained below. The two root certificates here cover the unpinned graph.

-- The checker and the bound certificates are adapted from PEqualNP/Outside/L_meta_1667.lean (Apache-2.0).
-- Two modes: u=false are monotone runs (AND, OR); u=true are runs up to complement, where negation is free.
namespace PEqualNP.Outside.L_meta_34784
open PEqualNP.CircuitLowerBounds
private def word80 (xs : List Nat) : Nat :=
  xs.foldl (fun a b => (a <<< 80) ||| b) 0

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

def inputs : List Sig := [(BitVec.ofNat 512 (word80 [0xaaaaaaaa,0xaaaaaaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaaaaaaa])),(BitVec.ofNat 512 (word80 [0xcccccccc,0xcccccccccccccccccccc,0xcccccccccccccccccccc,0xcccccccccccccccccccc,0xcccccccccccccccccccc,0xcccccccccccccccccccc,0xcccccccccccccccccccc])),(BitVec.ofNat 512 (word80 [0xf0f0f0f0,0xf0f0f0f0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f0f0f0])),(BitVec.ofNat 512 (word80 [0xff00ff00,0xff00ff00ff00ff00ff00,0xff00ff00ff00ff00ff00,0xff00ff00ff00ff00ff00,0xff00ff00ff00ff00ff00,0xff00ff00ff00ff00ff00,0xff00ff00ff00ff00ff00])),(BitVec.ofNat 512 (word80 [0xffff0000,0xffff0000ffff0000ffff,0xffff0000ffff0000,0xffff0000ffff0000ffff,0xffff0000ffff0000,0xffff0000ffff0000ffff,0xffff0000ffff0000])),(BitVec.ofNat 512 (word80 [0xffffffff,0xffffffff0000,0xffffffff00000000,0xffffffff00000000ffff,0xffff00000000ffffffff,0xffffffff0000,0xffffffff00000000])),(BitVec.ofNat 512 (word80 [0xffffffff,0xffffffff000000000000,0xffffffffffffffff,0xffff,0xffffffffffff00000000,0xffffffffffff,0xffff0000000000000000])),(BitVec.ofNat 512 (word80 [0xffffffff,0xffffffffffffffffffff,0xffff0000000000000000,0xffff,0xffffffffffffffffffff,0xffffffff000000000000,0])),(BitVec.ofNat 512 (word80 [0xffffffff,0xffffffffffffffffffff,0xffffffffffffffffffff,0xffffffffffffffff0000,0,0,0]))]
def graph : Sig := (BitVec.ofNat 512 (word80 [0xffffffff,0xfffffffffffffffeffff,0xfffaffffffffffffeeee,0xffeeffeeeeccaa00ffff,0xfffffffffffffffffffe,0xfffffffaffffffffffff,0xeeeeffeeffeeeeccaa00]))
theorem graph_proper : proper graph := by unfold proper; decide +kernel
theorem input_list : List.ofFn (fun j : Fin 9 => inputs.getD j.val zero) = inputs := rfl
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
  (x 0 &&& x 3) ||| (x 1 &&& x 4) ||| (x 0 &&& x 5) ||| (x 1 &&& x 5) ||| (x 3 &&& x 5) ||| (x 0 &&& x 6) ||| (x 1 &&& x 6) ||| (x 4 &&& x 6) ||| (x 5 &&& x 6) ||| (x 0 &&& x 7) ||| (x 2 &&& x 7) ||| (x 3 &&& x 7) ||| (x 4 &&& x 7) ||| (x 6 &&& x 7)
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
  | 0 => (word80 [0x1000000000000,0x10000000000000001,0x10000,0x100000000,0x1000000000000,0x10000000000000001])
  | 1 => (word80 [0x10000000000000000,0x10000,0,0x1000000000000,1])
  | 2 => (word80 [1,0x10000,0,0,0x10000000000000001])
  | 3 => (word80 [0x10000,0,0,1])
  | 4 => (word80 [0x100000000,0x1000000000000,0x10000000000000001])
  | 5 => (word80 [0x1000000000000,1])
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
  (x 0 &&& x 3) ||| (x 1 &&& x 4) ||| (x 0 &&& x 5) ||| (x 1 &&& x 5) ||| (x 3 &&& x 5) ||| (x 0 &&& x 6) ||| (x 1 &&& x 6) ||| (x 4 &&& x 6) ||| (x 5 &&& x 6) ||| (x 0 &&& x 7) ||| (x 2 &&& x 7) ||| (x 3 &&& x 7) ||| (x 4 &&& x 7) ||| (x 6 &&& x 7)
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
private def limbs80 (pages : Array (Array Nat)) (i : Nat) : Nat :=
  ((pages[i/32]?).getD #[])[i%32]?.getD 0

def packedAt (word : Nat → Nat) (pos len : Nat) :=
  let i := pos/80
  let shift := pos % 80
  let lo := word i >>> shift
  if shift+len ≤ 80 then lo &&& ((1 <<< len)-1)
  else (lo ||| (word (i+1) <<< (80-shift))) &&& ((1 <<< len)-1)


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

private def countBits64 (x : Nat) : Nat :=
  let a := x - ((x >>> 1) &&& 0x5555555555555555)
  let b := (a &&& 0x3333333333333333) + ((a >>> 2) &&& 0x3333333333333333)
  let c := (b + (b >>> 4)) &&& 0x0f0f0f0f0f0f0f0f
  ((c * 0x0101010101010101) >>> 56) &&& 127

private def hintAddress (data : Nat → Nat) (off rows fmt idx : Nat) : Option (Nat × Nat) :=
  if fmt<32 then some (off+rows*fmt,packedAt data (off+idx*fmt) fmt) else
    let width := fmt % 32
    let delta := (fmt/32) % 32
    let span := (fmt/1024) % 256
    let count := fmt/262144
    let rw := rows.log2+1
    let start := off+(idx/64)*(64+rw)
    let bits := packedAt data start 64
    if !bits.testBit (idx % 64) then none else
      let rank := packedAt data (start+64) rw + countBits64 (bits &&& ((1 <<< (idx % 64))-1))
      let marks := off+((rows+63)/64)*(64+rw)
      let base := marks+((count+span-1)/span)*width
      some (base+count*delta, packedAt data (marks+(rank/span)*width) width +
        packedAt data (base+rank*delta) delta)

def forestHints (tab : Packing) (raw i : Nat) : List (Nat × Nat) :=
  let (num,d,cw,dict,flags,ow,marker,data) := tab
  if marker<1024 then
    let start := num*(10*d+raw+d)
    let pos := start+num*ow+packedAt data (start+i*ow) ow
    getPairs data cw d (packedAt data pos 6) (pos+6+marker)
  else
    let off := denseRowStart d raw dict + num*denseRowWidth d flags
    match hintAddress data off num ow i with
    | none => []
    | some (pairs,ptr) =>
      let priority := decide (4096≤marker)
      let pos := pairs+(marker-(if priority then 4096 else 1024))*(cw+d)+ptr
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

def graphValid (g : Forest) (prior : Nat → Nat) :=
  (chartSamples g.mask (fun j => (g.samples j).1) == BitVec.allOnes 152) &&
  (chartSamples g.mask (fun j => (g.samples j).2) == 0) &&
  g.cols.all (fun c => colCheck g.mask c prior) &&
  g.autos.all (fun p => autoOK (targetOf g) (p.map swapRows))

def indexedRoot (g : Forest) (k i : Nat) (ws : List Sig) :=
  decide (i < (g.levels k).1) && sameWords (stateSet g k i) ws
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

theorem cut_root {u} {m cap : Nat} {prior : Nat → Nat} {ws : List Sig}
    (low : ∀ q, Lower u (varsX q) (graphGoal q) (prior q)) (ci : ColumnInfo)
    (ok : colCheck m ci prior = true)
    (cut : (decide ws.Nodup && poolCut u (subcube ci.1 ci.2.1) ci.2.2.2.2 cap 0 (varsX (rawMask m ci)) ws)=true) :
    Impossible u (graphGoal m) cap ws.toFinset := by
  simp only [Bool.and_eq_true,decide_eq_true_eq] at cut
  exact poolCut_sound (col_sound ci prior low ok) [] rfl cut.1 cut.2

private def wavePosition (data : Nat → Nat) (pw : Nat) :
    List (Nat × Nat) → Nat → Nat → Nat × Nat
  | [], pos, label => (pos,label)
  | (offset,zeros)::tail, pos, label =>
    let start := offset+(pos/64)*(64+pw)
    let bits := packedAt data start 64
    let n := pos % 64
    let rank := packedAt data (start+64) pw + countBits64 (bits &&& ((1 <<< n)-1))
    if bits.testBit n then wavePosition data pw tail (zeros+rank) (2*label+1)
    else wavePosition data pw tail (pos-rank) (2*label)

private def indexWave (width maxKind pw tail iw aw : Nat) (levels : List (Nat × Nat))
    (ranges : Array (Nat × Nat)) (data : Nat → Nat) (h : Nat) : Option (Nat × Nat) :=
  let a := h % width
  let t := h/width
  let b := width+t % width
  let t2 := t/width
  let c := 2*width+t2 % width
  let pick := (packedAt data (2*a) 2 + packedAt data (2*b) 2 + packedAt data (2*c) 2) % 3
  let v := if pick=0 then a else if pick=1 then b else c
  if packedAt data (6*width+v) 1 != (t2/width) % 2 then none else
    let z := wavePosition data pw levels v 0
    let bounds := ranges[z.2]?.getD (0,0)
    let i := z.1-bounds.1
    if z.2 < maxKind then some (bounds.2+i,0)
    else if z.2=maxKind then
      let val := packedAt data (tail+i*(iw+aw)) (iw+aw)
      some (val &&& ((1 <<< iw)-1),val >>> iw)
    else none

def kwDir (u p n : Bool) : Prop := p≠n ∧ (u=false → p=true)
structure PolarRooms (u : Bool) (S : Finset Sig) (T : Sig) where
  owns : Sig → Row → Row → Prop
  total : ∀ p n, bit p T=true → bit n T=false → ∃ v, owns v p n
  valid : ∀ {v p n}, owns v p n → v∈S ∧ kwDir u (bit p v) (bit n v)
  unique : ∀ {v w p n}, owns v p n → owns w p n → v=w
  rect : ∀ {v p n p' n'}, owns v p n' → owns v p' n → owns v p n

def polarLeaf (u : Bool) (T : Sig) : PolarRooms u {T} T where
  owns v p n := v=T ∧ bit p T=true ∧ bit n T=false
  total p n hp hn := ⟨T,rfl,hp,hn⟩
  valid := by rintro v p n ⟨rfl,hp,hn⟩; exact ⟨by simp,by simp [kwDir,hp,hn]⟩
  unique := by rintro v w p n ⟨rfl,_,_⟩ ⟨eq,_,_⟩; exact eq.symm
  rect := by rintro v p n p' n' ⟨e,hp,_⟩ ⟨_,_,hn⟩; exact ⟨e,hp,hn⟩

def kwBoolGate (d : Nat) (x y : Bool) : Bool :=
  if d=0 then x && y else if d=1 then x || y else if d=2 then x && !y else !x && y
def kwTurn (d : Nat) (a : Bool) :=
  (if d=3 then !a else a) == decide (d=1)
def kwTurnGate (d : Nat) (p n value : Bool) :=
  if value=decide (d=1) then kwTurn d p else kwTurn d n
theorem kwGateTable : ∀ (u : Bool) (d : Fin 4) (pa pb na nb : Bool),
    allowed u d.val → kwDir u (kwBoolGate d.val pa pb) (kwBoolGate d.val na nb) →
      kwDir u (if kwTurnGate d.val pa na (kwBoolGate d.val pa pb) then pa else pb)
        (if kwTurnGate d.val pa na (kwBoolGate d.val pa pb) then na else nb) := by
  unfold kwDir allowed
  decide +kernel

def polarFork {u : Bool} {U : Finset Sig} {T a b : Sig} {d : Nat} (hd : allowed u d)
    (ha : a∉U) (hb : b∉U) (hz : bin d a b∉U)
    (H : PolarRooms u (insert (bin d a b) U) T) : PolarRooms u (insert a (insert b U)) T := by
  let z := bin d a b
  let branch := fun r : Row => if kwTurn d (bit r a) then a else b
  let sel := fun p n : Row => if bit p z=decide (d=1) then branch p else branch n
  have pick (p n) : sel p n=a ∨ sel p n=b := by
    dsimp only [sel,branch]; split <;> split <;> simp
  have outside (p n) : sel p n ∉ U := by
    rcases pick p n with eq | eq
    · simpa only [eq] using ha
    · simpa only [eq] using hb
  have separates (p n) (h : kwDir u (bit p z) (bit n z)) :
      kwDir u (bit p (sel p n)) (bit n (sel p n)) := by
    have lt : d<4 := by rcases hd with h | ⟨_,h⟩ <;> omega
    have gate (r : Row) : bit r z = kwBoolGate d (bit r a) (bit r b) := by
      dsimp only [z,kwBoolGate,bin]; split_ifs <;> simp [bit,r.isLt]
    have ok := kwGateTable u ⟨d,lt⟩ (bit p a) (bit p b) (bit n a) (bit n b) hd
      (by simpa only [←gate] using h)
    change kwDir u (if kwTurnGate d (bit p a) (bit n a) (kwBoolGate d (bit p a) (bit p b)) then _ else _)
      (if kwTurnGate d (bit p a) (bit n a) (kwBoolGate d (bit p a) (bit p b)) then _ else _) at ok
    rw [←gate] at ok
    by_cases side : bit p z=decide (d=1)
    · cases ha : kwTurn d (bit p a) <;> simpa only [sel,side,ite_true,branch,kwTurnGate,ha,
        Bool.false_eq_true,ite_false] using ok
    · cases ha : kwTurn d (bit n a) <;> simpa only [sel,side,ite_false,branch,kwTurnGate,ha,
        Bool.false_eq_true,ite_true] using ok
  refine { owns := fun v p n => (v∈U ∧ H.owns v p n) ∨ (v=sel p n ∧ H.owns z p n)
           total := ?_
           valid := ?_
           unique := ?_
           rect := ?_ }
  · intro p n hp hn
    obtain ⟨v,hv⟩ := H.total p n hp hn
    rcases Finset.mem_insert.mp (H.valid hv).1 with eq | mem
    · have vz : v=z := eq
      refine ⟨sel p n,Or.inr ⟨rfl,?_⟩⟩
      rw [←vz]
      exact hv
    · exact ⟨v,Or.inl ⟨mem,hv⟩⟩
  · intro v p n h
    rcases h with ⟨mem,hv⟩ | ⟨e,hv⟩
    · exact ⟨Finset.mem_insert_of_mem (Finset.mem_insert_of_mem mem),(H.valid hv).2⟩
    · subst v
      have inS : sel p n ∈ insert a (insert b U) := by
        rcases pick p n with eq | eq <;> simp [eq]
      exact ⟨inS,separates p n (H.valid hv).2⟩
  · intro v w p n h1 h2
    rcases h1 with ⟨vU,hv⟩ | ⟨ve,hv⟩ <;> rcases h2 with ⟨wU,hw⟩ | ⟨we,hw⟩
    · exact H.unique hv hw
    · apply False.elim
      apply hz
      change z∈U
      rw [←H.unique hv hw]
      exact vU
    · apply False.elim
      apply hz
      change z∈U
      rw [←H.unique hw hv]
      exact wU
    · exact ve.trans we.symm
  · intro v p n p' n' h1 h2
    rcases h1 with ⟨vU,hv⟩ | ⟨ve,hv⟩ <;> rcases h2 with ⟨wU,hw⟩ | ⟨we,hw⟩
    · exact Or.inl ⟨vU,H.rect hv hw⟩
    · exact False.elim (outside p' n (we ▸ vU))
    · exact False.elim (outside p n' (ve ▸ wU))
    · refine Or.inr ⟨?_,H.rect hv hw⟩
      have e : bit p z = bit p' z := by
        have v1 := (H.valid (H.rect hv hw)).2.1
        have v2 := (H.valid hw).2.1
        cases ep : bit p z <;> cases ep' : bit p' z <;> cases en : bit n z <;> simp_all
      by_cases h : bit p z=decide (d=1)
      · simpa only [sel,h,ite_true] using ve
      · have h' : bit p' z≠decide (d=1) := e ▸ h
        simpa only [sel,h,h',ite_false] using we

theorem kwWidth {u T k S} (h : Live u T k S) : S.card ≤ k+1 := by
  induction h using Live.ind with
  | stop hp => simp
  | @binary k U a b d hd ha hb hab hf tail ih =>
    have hu : bin d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1 := Finset.card_insert_le (a:=a) (insert b U)
    have h2 := Finset.card_insert_le (a:=b) U
    omega

theorem polarTight {u T k S} (run : Live u T k S) (tight : S.card=k+1) :
    Nonempty (PolarRooms u S T) := by
  induction k generalizing S with
  | zero =>
    obtain ⟨rfl,_⟩ := run
    exact ⟨polarLeaf u T⟩
  | succ k ih =>
    obtain ⟨U,a,b,d,hd,rfl,_,_,hab,hfresh,tail⟩ := run
    have fresh : bin d a b∉U := fun h => hfresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
    have li := kwWidth tail
    rw [Finset.card_insert_of_notMem fresh] at li
    have le1 := Finset.card_insert_le (a:=a) (insert b U)
    have le2 := Finset.card_insert_le (a:=b) U
    have ha : a∉U := by
      intro h
      rw [Finset.insert_eq_of_mem (Finset.mem_insert_of_mem h : a∈insert b U)] at tight
      omega
    have hb : b∉U := by
      intro h
      rw [Finset.insert_eq_of_mem h] at tight le1
      omega
    have eq : (insert (bin d a b) U).card=k+1 := by
      rw [Finset.card_insert_of_notMem fresh]
      omega
    obtain ⟨H⟩ := ih tail eq
    exact ⟨polarFork hd ha hb fresh H⟩

def polarOnly (u : Bool) (S : Finset Sig) (T v : Sig) (p n : Row) :=
  bit p T=true ∧ bit n T=false ∧ ∀ w∈S, kwDir u (bit p w) (bit n w) → w=v

theorem polarOwn {u S T v p n} (H : PolarRooms u S T) (one : polarOnly u S T v p n) : H.owns v p n := by
  obtain ⟨w,hw⟩ := H.total p n one.1 one.2.1
  have eq := one.2.2 w (H.valid hw).1 (H.valid hw).2
  exact eq ▸ hw

theorem polarCross {u S T k a b p n pa pb na nb} (size : k+1=S.card) (different : a≠b)
    (A : polarOnly u S T a p na) (B : polarOnly u S T b p nb)
    (C : polarOnly u S T a pa n) (D : polarOnly u S T b pb n) : Impossible u T k S := by
  intro j hj run
  have lb := kwWidth run
  have tight : S.card=j+1 := by omega
  obtain ⟨H⟩ := polarTight run tight
  exact different (H.unique (H.rect (polarOwn H A) (polarOwn H C)) (H.rect (polarOwn H B) (polarOwn H D)))
def kwProbe (xs q : Nat) : Row := Fin.ofNat 512 ((xs >>> (9*q)) &&& 511)
def CutRow (g : Forest) (k start n : Nat) : Prop :=
  ∀ j, start≤j → j<start+n → nodeVerified g k j=true ∨ Impossible g.mode (targetOf g) k (stateSet g k j).toFinset
theorem mixedEmpty (g : Forest) (k a : Nat) : CutRow g k a 0 := by
  intro j lo hi
  omega
theorem checkedRow {g k a n} (h : block g k a n=true) : CutRow g k a n :=
  fun j lo hi => Or.inl (block_at h j lo hi)
theorem joinRow {g k a x y} (first : CutRow g k a x) (last : CutRow g k (a+x) y) :
    CutRow g k a (x+y) := by
  intro j lo hi
  by_cases e : j<a+x
  · exact first j lo e
  · exact last j (by omega) (by omega)
def mixedTables (g : Forest) (top : Nat) := ∀ k ≤ top, CutRow g k 0 (g.levels k).1
theorem mixedForest (g : Forest) (top : Nat) (prior : Nat → Nat)
    (lower : ∀ q, Lower g.mode (varsX q) (graphGoal q) (prior q))
    (geometry : graphValid g prior=true) (rows : mixedTables g top) :
    ∀ k ≤ top, ∀ i < (g.levels k).1, Impossible g.mode (targetOf g) k (stateSet g k i).toFinset := by
  simp only [graphValid,Bool.and_eq_true,List.all_eq_true,beq_iff_eq] at geometry
  intro k
  induction k with
  | zero =>
    intro hk i hi
    rcases rows 0 hk i (by omega) (by omega) with checked | done
    · exact nodeVerified_sound g 0 i (chart_pairs geometry.1.1.1 geometry.1.1.2)
        (fun x hx => col_sound _ prior lower (geometry.1.2 x hx)) geometry.2 (by omega) checked
    · exact done
  | succ k ih =>
    intro hk i hi
    rcases rows _ hk i (by omega) (by omega) with checked | done
    · exact nodeVerified_sound g _ i (chart_pairs geometry.1.1.1 geometry.1.1.2)
        (fun x hx => col_sound _ prior lower (geometry.1.2 x hx)) geometry.2
        (fun _ => by simpa using ih (by omega)) checked
    · exact done
theorem mixedRoot {g top prior k i ws} (lower : ∀ q, Lower g.mode (varsX q) (graphGoal q) (prior q))
    (geom : graphValid g prior=true) (blocks : mixedTables g top) (le : k≤top)
    (idx : indexedRoot g k i ws=true) : Impossible g.mode (targetOf g) k ws.toFinset := by
  simp only [indexedRoot,Bool.and_eq_true,decide_eq_true_eq] at idx
  rw [←sameWords_sound idx.2]
  exact mixedForest g top prior lower geom blocks _ le i idx.1
def polarCell (ws : List Sig) (T v : Sig) (p n : Row) :=
  bit p T && !bit n T && ws.all (fun w => (bit p w==bit n w) || w==v)
theorem polarCell_sound {ws T v p n} (h : polarCell ws T v p n=true) :
    polarOnly true ws.toFinset T v p n := by
  simp only [polarCell,Bool.and_eq_true,Bool.not_eq_true',List.all_eq_true] at h
  refine ⟨h.1.1,h.1.2,?_⟩
  intro w hw sep
  have e : (bit p w==bit n w)=false := beq_eq_false_iff_ne.mpr sep.1
  simpa only [e,Bool.false_or,beq_iff_eq] using h.2 w (List.mem_toFinset.mp hw)
def polarWord (T : Sig) (ws : List Sig) (k v : Nat) :=
  let pos := kwProbe (v >>> 8)
  let negs := kwProbe (v >>> 35)
  let owner (x y : Row) := (ws.find? (fun w => bit x w != bit y w)).getD zero
  let a := owner (pos 0) (negs 1)
  let b := owner (pos 0) (negs 2)
  decide (k+1=ws.toFinset.card) && decide (a≠b) &&
    polarCell ws T a (pos 0) (negs 1) && polarCell ws T b (pos 0) (negs 2) &&
    polarCell ws T a (pos 1) (negs 0) && polarCell ws T b (pos 2) (negs 0)
theorem polarWord_sound {T ws k v} (h : polarWord T ws k v=true) : Impossible true T k ws.toFinset := by
  simp only [polarWord,Bool.and_eq_true,decide_eq_true_eq] at h
  exact polarCross h.1.1.1.1.1 h.1.1.1.1.2 (polarCell_sound h.1.1.1.2)
    (polarCell_sound h.1.1.2) (polarCell_sound h.1.2) (polarCell_sound h.2)
def polarSeries (g : Forest) (k start n : Nat) (data : Nat→Nat) :=
  (List.range n).all (fun j =>
    let r := data j
    if r=0 then nodeVerified g k (start+j) else polarWord (targetOf g) (stateSet g k (start+j)) k r)
theorem polarBlock {g k start n data} (mode : g.mode=true)
    (ok : polarSeries g k start n data=true) : CutRow g k start n := by
  intro j lo hi
  have h := List.all_eq_true.mp ok (j-start) (List.mem_range.mpr (by omega))
  have e : start+(j-start)=j := by omega
  dsimp only at h
  split at h
  · left; simpa only [e] using h
  · right; rw [mode]
    apply polarWord_sound
    simpa only [e] using h
theorem mixedLower {g prior i hints} (low : ∀ q, Lower g.mode (varsX q) (graphGoal q) (prior q))
    (geom : graphValid g prior = true) (blocks : mixedTables g g.cap)
    (idx : indexedRoot g g.cap i (vars g.mask) = true) (hp : properB (targetOf g) = true)
    (ess : checkEssential (targetOf g) (vars g.mask) (graphPairs g.mask hints) = true)
    (all : (graphPairs g.mask hints).map Prod.fst = vars g.mask) :
    Lower g.mode (vars g.mask) (targetOf g) (g.cap+1) := by
  apply lower_impossible (proper_of _ hp) (essential_plain ess).1 (essential_plain ess).2 _ (mixedRoot low geom blocks (Nat.le_refl _) idx)
  intro a ha
  apply essential_ok ess a
  rw [all]
  exact List.mem_toFinset.mpr ha



def target (x : Fin 8 → Bool) : Bool := decide (∃ i < ([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)
def smallCircuit : Circuit := ⟨[⟨.or,[5,7]⟩,⟨.or,[2,4]⟩,⟨.or,[4,5]⟩,⟨.or,[1,6]⟩,⟨.or,[3,6]⟩,⟨.or,[0,8]⟩,⟨.and,[11,10]⟩,⟨.and,[13,12]⟩,⟨.and,[7,9]⟩,⟨.and,[8,0]⟩,⟨.and,[6,1]⟩,⟨.or,[14,15]⟩,⟨.or,[19,16]⟩,⟨.or,[20,17]⟩,⟨.or,[21,18]⟩], 22⟩

theorem witnessMonotone : ∀ g ∈ smallCircuit.gates,
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [smallCircuit,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact ⟨Or.inl rfl,by decide⟩ | exact ⟨Or.inr rfl,by decide⟩

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem witnessCorrect : ∀ x : Fin 8 → Bool, smallCircuit.eval (List.ofFn x) = target x := by
  decide +kernel

theorem witnessSize : smallCircuit.gates.length = 15 := rfl

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


def sevenInputs : List Sig := vars 255
def sampleSeven (r : Row) (i : Fin 8) : Bool := bit r (sevenInputs.getD i.val zero)
theorem sevenList : List.ofFn (fun i : Fin 8 => sevenInputs.getD i.val zero) = sevenInputs := rfl
theorem sevenSampled (r : Row) : List.ofFn (sampleSeven r) = sevenInputs.map (bit r) := by
  rw [←sevenList,List.map_ofFn]
  rfl

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem sevenTable : ∀ r : Row, bit r graph = target (sampleSeven r) := by decide +kernel

theorem sevenEval (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (i : Nat) (r : Row) : bit r ((execute C.gates sevenInputs).getD i zero) =
      (C.wires (List.ofFn (sampleSeven r))).getD i false := by
  rw [←b_read,execute_bits _ _ _ (fun g hg => (h g hg).1),sevenSampled]
  rfl

def lowRow (i : Fin 8) : Row := Fin.ofNat 512 (1 <<< ([3, 4, 7, 0, 1, 0, 0, 0] : List Nat).getD i.val 0)
def highRow (i : Fin 8) : Row := Fin.ofNat 512 ((1 <<< i.val) ||| (1 <<< ([3, 4, 7, 0, 1, 0, 0, 0] : List Nat).getD i.val 0))

set_option maxHeartbeats 1000000 in
theorem allSevenRequired :
    (∀ i : Fin 8, bit (lowRow i) graph ≠ bit (highRow i) graph) ∧
    (∀ i j : Fin 8, i ≠ j →
      bit (lowRow i) (sevenInputs.getD j.val zero) =
      bit (highRow i) (sevenInputs.getD j.val zero)) := by decide +kernel

theorem physicalSigned (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (computes : ∀ x : Fin 8 → Bool, C.eval (List.ofFn x)=target x) :
    ∃ k, k ≤ C.gates.countP (fun g => !isNot g) ∧ Live true graph k sevenInputs.toFinset := by
  have goalEq : (execute C.gates sevenInputs).getD C.output zero = graph := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    exact (sevenEval C legal C.output r).trans ((computes (sampleSeven r)).trans (sevenTable r).symm)
  have out := get_rep (u:=true) (execute C.gates sevenInputs) C.output
  rw [goalEq] at out
  unfold Repr at out
  have pg : bit 0 graph = false := by decide +kernel
  rw [nrm_id pg] at out
  obtain ⟨k,S,hk,run,sub⟩ := extract (u:=true) C.gates sevenInputs legal (by simp) graph_proper
    (out.resolve_right (fun h => h graph_proper))
  have ns : sevenInputs.all plainWord = true := by decide +kernel
  rw [nrm_map ns] at sub
  have idx (a : Sig) (ha : a ∈ sevenInputs) : ∃ i : Fin 8, sevenInputs.getD i.val zero = a := by
    rw [←sevenList] at ha
    exact List.mem_ofFn.mp ha
  have eq : S = sevenInputs.toFinset := by
    ext a
    constructor
    · exact fun h => List.mem_toFinset.mpr (sub a h)
    · intro ha
      obtain ⟨i,rfl⟩ := idx a (List.mem_toFinset.mp ha)
      apply raw_required run sevenInputs (sevenInputs.getD i.val zero) sub (lowRow i) (highRow i)
        (allSevenRequired.1 i)
      intro v hv hn
      obtain ⟨j,rfl⟩ := idx v hv
      apply allSevenRequired.2 i j
      rintro rfl
      exact hn rfl
  exact ⟨k,hk,eq ▸ run⟩

theorem replaceShort 
    (lower : Impossible true graph 13 sevenInputs.toFinset) (gates : List Gate) (o : Nat)
    (fit : ∀ g ∈ gates, (g.op=GateOp.and ∨ g.op=GateOp.or ∨ g.op=GateOp.not) ∧ g.inputs.length≤2)
    (correct : ∀ x : Fin 8 → Bool, (Circuit.mk gates o).eval (List.ofFn x)=target x) :
    ∃ (gs : List Gate) (out : Nat), (∀ g ∈ gs, (g.op=GateOp.and ∨ g.op=GateOp.or) ∧ g.inputs.length≤2) ∧
       gs.length≤gates.length ∧ ∀ x : Fin 8 → Bool, (Circuit.mk gs out).eval (List.ofFn x)=target x := by
  classical
  by_cases big : 15 ≤ gates.length
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
private theorem checkedCells {g k start n} (arity depth : Nat)
    (h : cells g k start n arity 0 depth) : CutRow g k start n :=
  checkedRow (cellsBlock h)

def g41Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x3ff63ff63ff63ff63f,0xf63ff63ff63ff63ff63f])),(BitVec.ofNat 152 (word80 [0x492049204920492049,0x20492049204920492049]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xc7fbc7fbc7fbc7fbc7,0xfbc7fbc7fbc7fbc7fbc7])),(BitVec.ofNat 152 (word80 [0x924092409240924092,0x40924092409240924092]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xf8fdf8fdf8fdf8fdf8,0xfdf8fdf8fdf8fdf8fdf8])),(BitVec.ofNat 152 (word80 [0x248124812481248124,0x81248124812481248124]))),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g41C : List ColumnInfo := []
def g41A : List (List Nat) := [[],[83],[48],[48,80],[80,48],[80]]
def g41D3 (j : Nat) := if j=0 then 0x7 else 0
def g41L : Nat → Packing
  | 3 => (1,0,1,0,0,0,0,g41D3)
  | _ => emptyPacking
def g41I (_ _ : Nat) : Option (Nat × Nat) := none
def g41 : Forest := ⟨41,3,fun i => g41Y[i]?.getD (0,0),g41C,g41A,g41L,g41I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g41B3 : CutRow g41 3 0 1 := by
  have g41P3_0 : CutRow g41 3 0 1 := by
    apply checkedCells 3 0
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
  exact g41P3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g41T : mixedTables g41 3 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty g41 0 0
  · exact mixedEmpty g41 1 0
  · exact mixedEmpty g41 2 0
  · exact g41B3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g41G : graphValid g41 (boundsBefore []) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low41 : Lower true (varsX 41) (graphGoal 41) 4 := mixedLower (g:=g41) (i:=0) (hints:=3) (before_sound [] baseKnown) g41G g41T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K41 := extendKnown [] 4 [(41,[]),(82,[16,67,101]),(97,[83,67,100]),(98,[16,83,67,100]),(137,[117,101]),(193,[99,67,117]),(208,[64,16,33,99,117])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V41 : Known true K41 := extend_ok (m:=41) baseKnown low41 (by decide +kernel)
def g43Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfdf00fff81fc7e3ffb,0xe01fff03f8fc7ff7c03f])),(BitVec.ofNat 152 (word80 [0x45c09245142904808b,0x81248a28520901170249]))),((BitVec.ofNat 152 (word80 [0xe6a8703ffe007fc7cd,0x50e07ffc00ff8f9aa1c0])),(BitVec.ofNat 152 (word80 [0x96a9b6d618b228112d,0x536dac316450225aa6db]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfbb781ffffff8007f7,0x6f03ffffff000feede07])),(BitVec.ofNat 152 (word80 [0x235249820c0312204,0x6a49304180624408d492]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x64ffe3ffffffff80c,0x9ffc7ffffffff0193ff8])),(BitVec.ofNat 152 (word80 [0x249204100400400,0x4924082008008000924]))),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g43C : List ColumnInfo := [(2,0,41,0,4)]
def g43A : List (List Nat) := [[],[48]]
def g43D4 (j : Nat) := if j=0 then 0x1f else 0
def g43L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,g43D4)
  | _ => emptyPacking
def g43I (_ _ : Nat) : Option (Nat × Nat) := none
def g43 : Forest := ⟨43,4,fun i => g43Y[i]?.getD (0,0),g43C,g43A,g43L,g43I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g43B4 : CutRow g43 4 0 1 := by
  have g43P4_0 : CutRow g43 4 0 1 := by
    apply checkedCells 4 0
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
  exact g43P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g43T : mixedTables g43 4 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty g43 0 0
  · exact mixedEmpty g43 1 0
  · exact mixedEmpty g43 2 0
  · exact mixedEmpty g43 3 0
  · exact g43B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g43G : graphValid g43 (boundsBefore K41) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low43 : Lower true (varsX 43) (graphGoal 43) 5 := mixedLower (g:=g43) (i:=0) (hints:=83) (before_sound K41 V41) g43G g43T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K43 := extendKnown K41 5 [(43,[]),(83,[16,67,101]),(106,[16,48,32,98,66]),(113,[65,33,83,99]),(153,[65,33,117,101]),(195,[115,67,101,84]),(216,[64,49,32,97,33,117]),(226,[16,112,32,83,66,99]),(240,[64,81,32,115,33,98])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V43 : Known true K43 := extend_ok (m:=43) V41 low43 (by decide +kernel)
def g51Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x2fc38ff01fff1ff02,0xfc38ff01fff1ff02fc38])),(BitVec.ofNat 152 (word80 [0x42ccdb2a5451240242,0xccdb2a5451240242ccdb]))),((BitVec.ofNat 152 (word80 [0xfdcbc7fffe07fe3ffd,0xcbc7fffe07fe3ffdcbc7])),(BitVec.ofNat 152 (word80 [0x1448490c1860408414,0x48490c18604084144849]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xece607fffff8003fec,0xe607fffff8003fece607])),(BitVec.ofNat 152 (word80 [0x8a7b6b06085892808,0xa7b6b06085892808a7b6]))),((BitVec.ofNat 152 (word80 [0x1b3df8ffffffffc01b,0x3df8ffffffffc01b3df8])),(BitVec.ofNat 152 (word80 [0x893124c08106003089,0x3124c081060030893124]))),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g51C : List ColumnInfo := []
def g51A : List (List Nat) := [[],[64,81]]
def g51D3 (j : Nat) := if j=0 then 0xf else 0
def g51L : Nat → Packing
  | 3 => (1,0,1,0,0,0,0,g51D3)
  | _ => emptyPacking
def g51I (_ _ : Nat) : Option (Nat × Nat) := none
def g51 : Forest := ⟨51,3,fun i => g51Y[i]?.getD (0,0),g51C,g51A,g51L,g51I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g51B3 : CutRow g51 3 0 1 := by
  have g51P3_0 : CutRow g51 3 0 1 := by
    apply checkedCells 4 0
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
  exact g51P3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g51T : mixedTables g51 3 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty g51 0 0
  · exact mixedEmpty g51 1 0
  · exact mixedEmpty g51 2 0
  · exact g51B3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g51G : graphValid g51 (boundsBefore K43) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low51 : Lower true (varsX 51) (graphGoal 51) 4 := mixedLower (g:=g51) (i:=0) (hints:=65605) (before_sound K43 V43) g51G g51T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K51 := extendKnown K43 4 [(51,[]),(58,[48,32]),(75,[16,67,101]),(89,[48,97,33,32,80]),(120,[48,97,32,33]),(147,[65,117,101]),(154,[16,112,32,50,67,84,101]),(163,[16,116,100]),(170,[16,48,32,116,100]),(177,[64,16,33,50,83,115,99]),(178,[80,65,32,50,113,49,99]),(184,[64,49,32,82,114,98]),(202,[16,112,32,50,67,101,84])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V51 : Known true K51 := extend_ok (m:=51) V43 low51 (by decide +kernel)
def g99Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfe7d01c7fc0fc7cfe7,0xd01c7fc0fc7cfe7d01c7])),(BitVec.ofNat 152 (word80 [0x51d124928a290a051,0xd124928a290a051d1249]))),((BitVec.ofNat 152 (word80 [0x3f8b8e38fff007f3f8,0xb8e38fff007f3f8b8e38])),(BitVec.ofNat 152 (word80 [0x884b924930c3210884,0xb924930c3210884b9249]))),(0x0,0x0),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x3fe7703ffffff803fe,0x7703ffffff803fe7703f])),(BitVec.ofNat 152 (word80 [0x100024924104020100,0x2492410402010002492]))),((BitVec.ofNat 152 (word80 [0xc018ffc0fffffffc01,0x8ffc0fffffffc018ffc0])),(BitVec.ofNat 152 (word80 [0x200049248208040200,0x4924820804020004924]))),(0x0,0x0),(0x0,0x0)]
def g99C : List ColumnInfo := [(1,0,98,0,4)]
def g99A : List (List Nat) := [[],[101],[16],[16,101]]
def g99D4 (j : Nat) := if j=0 then 0x1f else 0
def g99L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,g99D4)
  | _ => emptyPacking
def g99I (_ _ : Nat) : Option (Nat × Nat) := none
def g99 : Forest := ⟨99,4,fun i => g99Y[i]?.getD (0,0),g99C,g99A,g99L,g99I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g99B4 : CutRow g99 4 0 1 := by
  have g99P4_0 : CutRow g99 4 0 1 := by
    apply checkedCells 4 0
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
  exact g99P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g99T : mixedTables g99 4 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty g99 0 0
  · exact mixedEmpty g99 1 0
  · exact mixedEmpty g99 2 0
  · exact mixedEmpty g99 3 0
  · exact g99B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g99G : graphValid g99 (boundsBefore K51) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low99 : Lower true (varsX 99) (graphGoal 99) 5 := mixedLower (g:=g99) (i:=0) (hints:=85) (before_sound K51 V51) g99G g99T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K99 := extendKnown K51 5 [(99,[]),(105,[48,97,33,32,80]),(114,[64,81,32,50]),(169,[80,113,33,50,99]),(201,[48,97,33,32,80,117]),(209,[65,33,50,101,117]),(210,[16,112,32,50,67,84]),(225,[80,113,33,50,67])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V99 : Known true K99 := extend_ok (m:=99) V51 low99 (by decide +kernel)
def g59Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xf003ff87fe1fffc01f,0xfff87fffe474a4007c1f])),(BitVec.ofNat 152 (word80 [0xa12845108440228940,0xa01108826014a45294a5]))),((BitVec.ofNat 152 (word80 [0xfffc0007ffe1ffffe0,0xfffffc0335be20f83e0])),(BitVec.ofNat 152 (word80 [0xc030162028040b0182,0xc0a00108225922318c63]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffff80001ffffff,0xf0007ffccfd11df0001f])),(BitVec.ofNat 152 (word80 [0x240980130884c0203,0x2c2120087c108a5294a]))),((BitVec.ofNat 152 (word80 [0x1ffffff,0xffff80004d2fe80003e0])),(BitVec.ofNat 152 (word80 [0xb82e045c111702c14,0xb005c104d26c9ce739c]))),((BitVec.ofNat 152 (word80 [0xfffffffffffe000000,0x33aa61bfffc00])),(BitVec.ofNat 152 (word80 [0xc0300060001803018,0xc046021182211084210]))),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g59C : List ColumnInfo := [(0,16,41,2,5),(16,0,43,0,5),(1,0,58,0,4),(2,16,41,0,4),(8,0,51,0,4)]
def g59A : List (List Nat) := [[],[48]]
def g59D4 (j : Nat) := if j=0 then 0x5bd4940 else 0
def g59D5 := limbs80 #[#[0x240d140ff40fd40fd20,0x2012]]
def g59H5 (j : Nat) := if j=0 then 0x4 else 0
def g59D6 (j : Nat) := if j=0 then 0x18989f else 0
def g59H6 (j : Nat) := if j=0 then 0x1208000270005 else 0
def g59L : Nat → Packing
  | 4 => (1,2,3,0,0,0,0,g59D4)
  | 5 => (3,1,3,0,0,5,0,g59D5)
  | 6 => (1,0,3,0,0,0,0,g59D6)
  | _ => emptyPacking
def g59I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupShort 1 2 0 2 0 0 g59H5
  | 6 => lookupShort 1 11 0 5 2 1 g59H6
  | _ => fun _ => none
def g59 : Forest := ⟨59,6,fun i => g59Y[i]?.getD (0,0),g59C,g59A,g59L,g59I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g59B4 : CutRow g59 4 0 1 := by
  have g59P4_0 : CutRow g59 4 0 1 := by
    apply checkedCells 5 0
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
  exact g59P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g59B5 : CutRow g59 5 0 3 := by
  have g59P5_0 : CutRow g59 5 0 3 := by
    apply checkedCells 6 0
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
  exact g59P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g59B6 : CutRow g59 6 0 1 := by
  have g59P6_0 : CutRow g59 6 0 1 := by
    apply checkedCells 5 0
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
  exact g59P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g59T : mixedTables g59 6 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty g59 0 0
  · exact mixedEmpty g59 1 0
  · exact mixedEmpty g59 2 0
  · exact mixedEmpty g59 3 0
  · exact g59B4
  · exact g59B5
  · exact g59B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g59G : graphValid g59 (boundsBefore K99) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low59 : Lower true (varsX 59) (graphGoal 59) 7 := mixedLower (g:=g59) (i:=0) (hints:=65603) (before_sound K99 V99) g59G g59T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K59 := extendKnown K99 7 [(59,[]),(91,[16,67,101]),(155,[65,117,101])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V59 : Known true K59 := extend_ok (m:=59) V99 low59 (by decide +kernel)
def g107Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfe1ff01fffe3ffc03f,0xe1fe1fffb19d500f00ff])),(BitVec.ofNat 152 (word80 [0x1440a1414048028281,0x44044008218911111111]))),((BitVec.ofNat 152 (word80 [0x1fffe01ffc7fffc0,0x1ffe1fc6d3a20f00f00])),(BitVec.ofNat 152 (word80 [0x5882c18582810b0305,0x882804112d3823333333]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x1fffffe0007fffff,0xfe0001ff9e1bc000f00f])),(BitVec.ofNat 152 (word80 [0x6113020613124c2426,0x13089201e12caaaaaaa]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffe0000000007fffff,0xfffffe000be08f00fff0])),(BitVec.ofNat 152 (word80 [0x800404080400100808,0x400040000004444444]))),((BitVec.ofNat 152 (word80 [0xffffffffffff800000,0x6446ffff0000])),(BitVec.ofNat 152 (word80 [0x1808101800603030,0x118111824046c8888888]))),(0x0,0x0),(0x0,0x0)]
def g107C : List ColumnInfo := [(1,0,106,0,5),(2,0,105,0,5),(8,0,99,0,5),(64,0,43,0,5)]
def g107A : List (List Nat) := [[],[96,49]]
def g107D6 (j : Nat) := if j=0 then 0x4e09f else 0
def g107L : Nat → Packing
  | 6 => (1,0,2,0,0,0,0,g107D6)
  | _ => emptyPacking
def g107I (_ _ : Nat) : Option (Nat × Nat) := none
def g107 : Forest := ⟨107,6,fun i => g107Y[i]?.getD (0,0),g107C,g107A,g107L,g107I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g107B6 : CutRow g107 6 0 1 := by
  have g107P6_0 : CutRow g107 6 0 1 := by
    apply checkedCells 5 0
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
  exact g107P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g107T : mixedTables g107 6 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty g107 0 0
  · exact mixedEmpty g107 1 0
  · exact mixedEmpty g107 2 0
  · exact mixedEmpty g107 3 0
  · exact mixedEmpty g107 4 0
  · exact mixedEmpty g107 5 0
  · exact g107B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g107G : graphValid g107 (boundsBefore K59) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low107 : Lower true (varsX 107) (graphGoal 107) 7 := mixedLower (g:=g107) (i:=0) (hints:=83) (before_sound K59 V59) g107G g107T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K107 := extendKnown K59 7 [(107,[]),(115,[16,67,101]),(211,[64,16,49,101,117]),(217,[96,49,33,66,117]),(227,[115,67,101]),(241,[65,33,83,99,115]),(242,[64,81,32,115,97])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V107 : Known true K107 := extend_ok (m:=107) V59 low107 (by decide +kernel)
def g121Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xffc03fe1fffffc03f,0xfff0fffff1560700f0ff])),(BitVec.ofNat 152 (word80 [0x204848044120048480,0x81220020900606111111]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffc001ff0ffffc0,0x3fff0fff20b57b000f0f])),(BitVec.ofNat 152 (word80 [0x489012288242892125,0x2240284020b151aaaaaa]))),((BitVec.ofNat 152 (word80 [0xfffffffe000ffffff,0xc0000ff01fb5240f0000])),(BitVec.ofNat 152 (word80 [0x82e160b00b842e0606,0xb844282179524777777]))),((BitVec.ofNat 152 (word80 [0xf00000000000ffffff,0xfffff000134bf8f00ff0])),(BitVec.ofNat 152 (word80 [0x30180c10c08300808,0xc000304034828444444]))),((BitVec.ofNat 152 (word80 [0xffffffffffff000000,0xcea8c5fff000])),(BitVec.ofNat 152 (word80 [0xc0203001000c03030,0x30088c084820c1888888]))),(0x0,0x0),(0x0,0x0)]
def g121C : List ColumnInfo := [(0,16,41,64,5),(8,0,113,0,5),(16,0,105,0,5),(1,0,120,0,4),(32,0,89,0,4),(64,16,41,0,4)]
def g121A : List (List Nat) := [[],[80]]
def g121D4 (j : Nat) := if j=0 then 0x5dd4530 else 0
def g121D5 (j : Nat) := if j=0 then 0xc8404fd30 else 0
def g121H5 (j : Nat) := if j=0 then 0x3 else 0
def g121D6 (j : Nat) := if j=0 then 0x23468bf else 0
def g121H6 (j : Nat) := if j=0 then 0x4 else 0
def g121L : Nat → Packing
  | 4 => (1,2,3,0,0,0,0,g121D4)
  | 5 => (1,1,3,0,0,0,0,g121D5)
  | 6 => (1,0,3,0,0,0,0,g121D6)
  | _ => emptyPacking
def g121I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupShort 1 2 0 2 0 0 g121H5
  | 6 => lookupShort 1 2 0 2 0 0 g121H6
  | _ => fun _ => none
def g121 : Forest := ⟨121,6,fun i => g121Y[i]?.getD (0,0),g121C,g121A,g121L,g121I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g121B4 : CutRow g121 4 0 1 := by
  have g121P4_0 : CutRow g121 4 0 1 := by
    apply checkedCells 5 0
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
  exact g121P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g121B5 : CutRow g121 5 0 1 := by
  have g121P5_0 : CutRow g121 5 0 1 := by
    apply checkedCells 6 0
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
  exact g121P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g121B6 : CutRow g121 6 0 1 := by
  have g121P6_0 : CutRow g121 6 0 1 := by
    apply checkedCells 5 0
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
  exact g121P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g121T : mixedTables g121 6 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty g121 0 0
  · exact mixedEmpty g121 1 0
  · exact mixedEmpty g121 2 0
  · exact mixedEmpty g121 3 0
  · exact g121B4
  · exact g121B5
  · exact g121B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g121G : graphValid g121 (boundsBefore K107) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low121 : Lower true (varsX 121) (graphGoal 121) 7 := mixedLower (g:=g121) (i:=0) (hints:=393219) (before_sound K107 V107) g121G g121T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K121 := extendKnown K107 7 [(121,[]),(122,[16,67,101]),(171,[33,65,115,83,101]),(185,[83,118]),(203,[33,65,117]),(218,[64,16,49,101,117])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V121 : Known true K121 := extend_ok (m:=121) V107 low121 (by decide +kernel)
def g179Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xf003ff0ffffff003ff,0xff87ffc3545d520f83e0])),(BitVec.ofNat 152 (word80 [0xa0a80a209002a0a814,0x910008a445812318c63]))),((BitVec.ofNat 152 (word80 [0xfffc000ff87ffffc01,0xfff87ffcd372a6007c1f])),(BitVec.ofNat 152 (word80 [0xc0310c402120c43118,0x8201210052302694a529]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffff0007ffffffe,0x7ffcafd11df0001f])),(BitVec.ofNat 152 (word80 [0x2c05002c20b00c020,0x2c220a00a541186318c6]))),((BitVec.ofNat 152 (word80 [0x7fffffff,0xffff80004d2fe8007fe0])),(BitVec.ofNat 152 (word80 [0xb02608b044c090241,0x30004c100907c94a5294]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffffff80000000,0x33aa61bff8000])),(BitVec.ofNat 152 (word80 [0xc03800c00700e0381,0xc04470211aa6018c6318]))),(0x0,0x0)]
def g179C : List ColumnInfo := [(1,0,178,0,4),(2,0,177,0,4),(16,0,163,0,4),(32,0,147,0,4),(128,0,51,0,4)]
def g179A : List (List Nat) := [[],[65,117],[16,116],[16,112,64,84],[64,16,81,113],[64,81],[80,65,113,16],[80,113],[112,84],[112,81,65,64]]
def g179D4 (j : Nat) := if j=0 then 0x57d4d10 else 0
def g179D5 (j : Nat) := if j=0 then 0xc1a0fd30fd10 else 0
def g179H5 (j : Nat) := if j=0 then 0xc else 0
def g179D6 (j : Nat) := if j=0 then 0x23440bf else 0
def g179H6 := limbs80 #[#[0x1003a012000000000000,0x2e000553000000dc00,0x1601900001100]]
def g179L : Nat → Packing
  | 4 => (1,2,3,0,0,0,0,g179D4)
  | 5 => (2,1,3,0,0,4,0,g179D5)
  | 6 => (1,0,3,0,0,0,0,g179D6)
  | _ => emptyPacking
def g179I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupShort 1 2 0 2 0 0 g179H5
  | 6 => lookupShort 2 37 0 6 1 3 g179H6
  | _ => fun _ => none
def g179 : Forest := ⟨179,6,fun i => g179Y[i]?.getD (0,0),g179C,g179A,g179L,g179I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g179B4 : CutRow g179 4 0 1 := by
  have g179P4_0 : CutRow g179 4 0 1 := by
    apply checkedCells 5 0
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
  exact g179P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g179B5 : CutRow g179 5 0 2 := by
  have g179P5_0 : CutRow g179 5 0 2 := by
    apply checkedCells 6 0
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
  exact g179P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g179B6 : CutRow g179 6 0 1 := by
  have g179P6_0 : CutRow g179 6 0 1 := by
    apply checkedCells 5 0
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
  exact g179P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g179T : mixedTables g179 6 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty g179 0 0
  · exact mixedEmpty g179 1 0
  · exact mixedEmpty g179 2 0
  · exact mixedEmpty g179 3 0
  · exact g179B4
  · exact g179B5
  · exact g179B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g179G : graphValid g179 (boundsBefore K121) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low179 : Lower true (varsX 179) (graphGoal 179) 7 := mixedLower (g:=g179) (i:=0) (hints:=65605) (before_sound K121 V121) g179G g179T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K179 := extendKnown K121 7 [(179,[]),(186,[16,112,32,50,67,84])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V179 : Known true K179 := extend_ok (m:=179) V121 low179 (by decide +kernel)
def g233Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x3fc7f80fffe3ffc07,0xf8ffffe3fec106038e3f])),(BitVec.ofNat 152 (word80 [0x80801020404000810,0x10040040000000249249]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfc007fff01ffc3fff8,0xfe1ffc3d21dd1c01c7])),(BitVec.ofNat 152 (word80 [0x109112244848089021,0x2208448080215c492492]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x7ffffe0003ffff,0xff001fffc3ba900071f8])),(BitVec.ofNat 152 (word80 [0x222244081110922244,0x409091000b8a80924924]))),((BitVec.ofNat 152 (word80 [0xffff8000000003ffff,0xffffe000007f28e07e00])),(BitVec.ofNat 152 (word80 [0x40c01830606120c081,0x80200609107508492492]))),((BitVec.ofNat 152 (word80 [0xfffffffffffffc0000,0x3066bff8000])),(BitVec.ofNat 152 (word80 [0x830060408180030306,0x4c11812230223924924]))),(0x0,0x0)]
def g233C : List ColumnInfo := [(8,0,225,0,5)]
def g233A : List (List Nat) := [[],[117],[83,118],[83,99,115],[99],[99,117],[115,83,101],[115,101]]
def g233D5 (j : Nat) := if j=0 then 0x3f else 0
def g233L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,g233D5)
  | _ => emptyPacking
def g233I (_ _ : Nat) : Option (Nat × Nat) := none
def g233 : Forest := ⟨233,5,fun i => g233Y[i]?.getD (0,0),g233C,g233A,g233L,g233I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g233B5 : CutRow g233 5 0 1 := by
  have g233P5_0 : CutRow g233 5 0 1 := by
    apply checkedCells 5 0
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
  exact g233P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g233T : mixedTables g233 5 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty g233 0 0
  · exact mixedEmpty g233 1 0
  · exact mixedEmpty g233 2 0
  · exact mixedEmpty g233 3 0
  · exact mixedEmpty g233 4 0
  · exact g233B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g233G : graphValid g233 (boundsBefore K179) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low233 : Lower true (varsX 233) (graphGoal 233) 6 := mixedLower (g:=g233) (i:=0) (hints:=3) (before_sound K179 V179) g233G g233T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K233 := extendKnown K179 6 [(233,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V233 : Known true K233 := extend_ok (m:=233) V179 low233 (by decide +kernel)
def g234Y : Array (Bits × Bits) := #[(0x0,0x0),((BitVec.ofNat 152 (word80 [0x1ff803fffc3ff007fe,0x1fffff0f3c429f000f0f])),(BitVec.ofNat 152 (word80 [0x485428280890a45214,0x484082200c428b555555]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x1ffffc03fffffff800,0x1fe1fff0d496690f00f0])),(BitVec.ofNat 152 (word80 [0x826131309004c06098,0x80842402900669333333]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x1ffffffc003fffffff,0xe001ffff2b972600f0ff])),(BitVec.ofNat 152 (word80 [0x108040422121088420,0x11090800239004888888]))),((BitVec.ofNat 152 (word80 [0xe0000000003fffffff,0xfffe00001369f8f0ff00])),(BitVec.ofNat 152 (word80 [0x3018180c2060100c0,0x2003044102170222222]))),((BitVec.ofNat 152 (word80 [0xffffffffffc0000000,0xcea8c5ff0000])),(BitVec.ofNat 152 (word80 [0x1c06020300380e0701,0x1c11c0884e8884cccccc]))),(0x0,0x0)]
def g234C : List ColumnInfo := [(8,0,226,0,5)]
def g234A : List (List Nat) := [[],[115,101]]
def g234D5 (j : Nat) := if j=0 then 0x3f else 0
def g234L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,g234D5)
  | _ => emptyPacking
def g234I (_ _ : Nat) : Option (Nat × Nat) := none
def g234 : Forest := ⟨234,5,fun i => g234Y[i]?.getD (0,0),g234C,g234A,g234L,g234I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g234B5 : CutRow g234 5 0 1 := by
  have g234P5_0 : CutRow g234 5 0 1 := by
    apply checkedCells 5 0
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
  exact g234P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g234T : mixedTables g234 5 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty g234 0 0
  · exact mixedEmpty g234 1 0
  · exact mixedEmpty g234 2 0
  · exact mixedEmpty g234 3 0
  · exact mixedEmpty g234 4 0
  · exact g234B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g234G : graphValid g234 (boundsBefore K233) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low234 : Lower true (varsX 234) (graphGoal 234) 6 := mixedLower (g:=g234) (i:=0) (hints:=823152720) (before_sound K233 V233) g234G g234T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K234 := extendKnown K233 6 [(234,[]),(248,[65,33,117])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V234 : Known true K234 := extend_ok (m:=234) V233 low234 (by decide +kernel)
def g123Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xc007ffffe0ffff72a6,0xa10baa00000fc003f03f])),(BitVec.ofNat 152 (word80 [0x82500a004204403202,0x21032a05145145145145]))),((BitVec.ofNat 152 (word80 [0xfff800ffffffe03d4a,0x8666308003f000fc0fc0])),(BitVec.ofNat 152 (word80 [0x602c02800082350a,0x844210030c30c30c30c3]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffff0000ffffad84,0xb85846c000003f00003f])),(BitVec.ofNat 152 (word80 [0x2084308b0489000d84,0x985804eaaaaaaaaaaaaa]))),((BitVec.ofNat 152 (word80 [0xffffffffff0000804d,0x6156adc0fc0000000fc0])),(BitVec.ofNat 152 (word80 [0xb01402c002e048045,0x2114a9dc71c71c71c71c]))),((BitVec.ofNat 152 (word80 [0x9171,0x18b1d83f00003ffff000])),(BitVec.ofNat 152 (word80 [0xc0180300830088071,0x20c010410410410410]))),((BitVec.ofNat 152 (word80 [0x4e93,0x4f80057fffffc0000000])),(BitVec.ofNat 152 (word80 [0x300600c010c0104880,0x4a800420820820820820]))),(0x0,0x0),(0x0,0x0)]
def g123C : List ColumnInfo := [(1,0,122,0,7),(2,0,121,0,7),(8,0,115,0,7),(16,0,107,0,7),(32,0,91,0,7),(64,0,59,0,7),(0,8,82,33,6),(0,16,41,66,6),(1,8,82,32,5),(2,16,41,64,5),(9,0,114,0,5),(17,0,106,0,5),(24,0,99,0,5),(32,8,82,1,5),(40,0,83,0,5),(64,16,41,2,5),(80,0,43,0,5),(3,0,120,0,4),(25,0,98,0,4),(26,0,97,0,4),(33,0,82,0,4),(33,8,82,0,4),(34,0,89,0,4),(41,0,82,0,4),(65,0,58,0,4),(66,0,41,0,4),(66,16,41,0,4),(82,0,41,0,4)]
def g123A : List (List Nat) := [[],[16,67,101]]
def g123D5 := limbs80 #[#[0x55140443cc5515150110,0x443cc5514154110e3965,0x5537154140e396455150,0x50d50ccf73d89515034e,0x40b6785b54603c6e0154,0x40]]
def g123D6 := limbs80 #[#[0x59110551105411050110,0x545405414054520d9110,0x50550d89405954055140,0x59150585505515050d50,0x5515250d52d9150d8550,0xef5f9fbf5de7f3bd8154,0x777bb7dae7f3b8fc3df6,0xc05d549551885525fcf,0x2fdc102dccac5482a55,0x435d40edc1a3dc1e7d9,0x1275940e550215d20559,0x40b55163dd02ddc667dc,0x401dc521dd85050427d9,0x4cf550015d8415d49054,0xd415c68455201dd463dc,0x9cd5c6675902b550e654,0xf0280015c626d88ed54,0x9c441f4dc652e1507c2e,0xf47638db2c55cabd4e,0xd2cb5da5ce6591a8942a,0xaf6b9bb5d366f278bbf5,0x131e38c03020381828d0,0x8d10b9100f1e26360518,0x47b2841ec48010c87d08,0x138440100801c384970,0xc843b2140401010dc21b,0x68400000159080005019,0xe94200de10ac5243812d,0x7b44bc448080000e0480,0xe05b4101]]
def g123H6 := limbs80 #[#[0x1e0140004eb000c00268,0x8a60550]]
def g123D7 := limbs80 #[#[0x94954549505094048110,0xfffefbf7f3efdfdbbfbb,0xaa5590eaa87495281b12,0x20ea90854042801643e4,0x915450a821d900ac81e5,0xaa91a438ca1c1d860aca,0x500ec19f61a3b0d1d921,0xc954d4aa2a55132b2095,0x2b06954dcac9256192a0,0x46814c420d41e002760d,0x93847d053a0d12dc9e1f,0x9fc77dc669d956216953,0x6bca968d9d25d9063486,0x668391305712c06eeb7,0x2930a5103c31745151e3,0x64a0d8e4a042025829b8,0x480a531930405253e588,0xdc046cc0942ee19461c8,0xe1b04fba343376121f80,0x9a688bf54221d3889afc,0x8e0221e7104c5fbd2089,0x3ccc48c7ce809a6b8439,0x80946e74d232f084e021,0x966388d45a799a935fe,0x4edcc73a6988ca033f31,0x46de00881a6cc6067d44,0xae047ada0ae047bdc442,0x9e10]]
def g123H7 := limbs80 #[#[0x5a42a6665250010a804a,0x6e8e2b240a0a1a486221,0xa140400068048d5ab46a,0x1ff7f75ffffef80910,0x80b30100303420003600,0x59b4ed4ec306550c98a5,0x4]]
def g123D8 := limbs80 #[#[0xa814c2905104a454bffb,0x938980554aa550a99550,0x7c70f1e95dd24436aa9f,0x220c802ea926cb104290,0x67900d00899c6303969,0xe48496e1c240d35097c8,0x981c88f9f4012fcd701e,0x7fa8028600385f644]]
def g123H8 := limbs80 #[#[0x1280000000076a000,0x3800000026800000,0x0,0xe802199b000000,0x15b7000,0x3160000000000000,0x78432486507c0000,0x4c00000000000000,0x8900000000000000,0x3f340000000,0x7462e00000029d490,0x509591a4300000000,0x0,0x930000,0x0,0x900e00224000001b1105,0xc200000000072eb0,0x24000000022c0081340,0x21e00000,0x163e2800000036400000,0x2899100348018,0x61563002011e000000]]
def g123D9 (j : Nat) := if j=0 then 0xa4188201bf else 0
def g123H9 := limbs80 #[#[0x82000000001180a,0x5008e0000000,0xac900000000003b02011,0xb2000000001,0x100009f0002000000000,0x1d02800001c008c0005]]
def g123L : Nat → Packing
  | 5 => (7,4,5,0,0,6,0,g123D5)
  | 6 => (38,3,5,1114133,85,9,1048,g123D6)
  | 7 => (34,2,5,655368,67,10,1066,g123D7)
  | 8 => (11,1,5,131073,16,8,1049,g123D8)
  | 9 => (1,0,5,0,0,0,0,g123D9)
  | _ => emptyPacking
def g123I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupShort 2 17 3 6 3 1 g123H6
  | 7 => indexWave 21 3 6 399 6 1 [(189,50),(259,18),(329,47)] #[(0,0),(47,1),(14,5),(51,0),(1,0)] g123H7
  | 8 => lookupShort 13 197 3 9 6 1 g123H8
  | 9 => lookupShort 4 71 1 7 4 1 g123H9
  | _ => fun _ => none
def g123 : Forest := ⟨123,9,fun i => g123Y[i]?.getD (0,0),g123C,g123A,g123L,g123I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123B5 : CutRow g123 5 0 7 := by
  have g123P5_0 : CutRow g123 5 0 7 := by
    apply checkedCells 6 0
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
  exact g123P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123B6 : CutRow g123 6 0 38 := by
  have g123P6_0 : CutRow g123 6 0 1 := by
    apply checkedCells 5 0
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
  have g123P6_1 : CutRow g123 6 1 4 := by
    apply checkedCells 6 0
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
  have g123P6_5 : CutRow g123 6 5 33 := by
    apply checkedCells 7 3
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
  exact (@joinRow g123 6 0 1 37 g123P6_0 (@joinRow g123 6 1 4 33 g123P6_1 g123P6_5))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123B7 : CutRow g123 7 0 34 := by
  have g123P7_0 : CutRow g123 7 0 6 := by
    apply checkedCells 6 0
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
  have g123P7_6 : CutRow g123 7 6 17 := by
    apply checkedCells 7 2
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
  have g123P7_23 : CutRow g123 7 23 11 := by
    apply checkedCells 8 1
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
  exact (@joinRow g123 7 0 6 28 g123P7_0 (@joinRow g123 7 6 17 11 g123P7_6 g123P7_23))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123B8 : CutRow g123 8 0 11 := by
  have g123P8_0 : CutRow g123 8 0 2 := by
    apply checkedCells 6 0
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
  have g123P8_2 : CutRow g123 8 2 9 := by
    apply checkedCells 7 1
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
  exact (@joinRow g123 8 0 2 9 g123P8_0 g123P8_2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123B9 : CutRow g123 9 0 1 := by
  have g123P9_0 : CutRow g123 9 0 1 := by
    apply checkedCells 6 0
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
  exact g123P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123T : mixedTables g123 9 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty g123 0 0
  · exact mixedEmpty g123 1 0
  · exact mixedEmpty g123 2 0
  · exact mixedEmpty g123 3 0
  · exact mixedEmpty g123 4 0
  · exact g123B5
  · exact g123B6
  · exact g123B7
  · exact g123B8
  · exact g123B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123G : graphValid g123 (boundsBefore K234) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low123 : Lower true (varsX 123) (graphGoal 123) 10 := mixedLower (g:=g123) (i:=0) (hints:=65603) (before_sound K234 V234) g123G g123T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K123 := extendKnown K234 10 [(123,[]),(219,[64,16,49,101,117])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V123 : Known true K123 := extend_ok (m:=123) V234 low123 (by decide +kernel)
def g187Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x3fffffc1ffff722c9,0xc6ea80003f8001fc07f])),(BitVec.ofNat 152 (word80 [0x280280084044032080,0xc0ca80a142850a14285]))),((BitVec.ofNat 152 (word80 [0xfc003ffffffe03d52c,0x5d8c60000000fe03f80])),(BitVec.ofNat 152 (word80 [0x310b1050080823d12c,0x54840468d1a3468d1a3]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffc0001ffffad8ca,0x93211a01fc07f000007f])),(BitVec.ofNat 152 (word80 [0x400c0160809000504a,0x912012142850a142850a]))),((BitVec.ofNat 152 (word80 [0xffffffffe0000804f6,0x691ab3fe000000003f80])),(BitVec.ofNat 152 (word80 [0x8050058002e04804c2,0x2812b33870e1c3870e1c]))),((BitVec.ofNat 152 (word80 [0x91711,0xa28774000007ffffc000])),(BitVec.ofNat 152 (word80 [0x26026011300880611,0x228304a142850a142850]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x4e917,0x7e4005fffff800000000])),(BitVec.ofNat 152 (word80 [0x38038021c01048915,0x424004c183060c183060]))),(0x0,0x0)]
def g187C : List ColumnInfo := [(1,0,186,0,7),(2,0,185,0,7),(8,0,179,0,7),(16,0,171,0,7),(32,0,155,0,7),(128,0,59,0,7),(0,2,137,48,6),(0,16,41,130,6),(2,16,41,128,5),(18,0,169,0,5),(32,2,137,16,5),(34,0,153,0,5),(128,16,41,2,5),(144,0,43,0,5),(3,0,184,0,4),(9,0,178,0,4),(10,0,177,0,4),(17,0,170,0,4),(33,0,154,0,4),(40,0,147,0,4),(48,0,137,0,4),(129,0,58,0,4),(130,0,41,0,4),(130,16,41,0,4),(136,0,51,0,4)]
def g187A : List (List Nat) := [[],[65,117],[48],[48,65,117]]
def g187D5 := limbs80 #[#[0x509404836a5d54250120,0x483ca5515250120dab75,0x1cb70595408fb805d954,0x8185b54f033a]]
def g187D6 := limbs80 #[#[0x50120d9510d891054910,0x59120585205512054520,0x551405494050940d9120,0x58154d9540d894059540,0x7efd7bbbdbe7f3bd8154,0xa10ff5eef573f7dbbd7e,0x2b9085750aee000dc996,0x8bba8d5751e2a83d5486,0x8aeb214b74336ca43dcc,0x9522baa077538eec515d,0x5d5aeaa3695453eca975,0x4dc98bb830b725e6e0b1,0xe1dc991b93207264ee0c,0xc844002b94137278ae4,0x7231964a0471f8d05824,0x88bc5a2ad469b48a24f8,0x8a331180be5dce46e341,0xa0194044b000a7532954,0x8007c118854168f18110,0x44808040200c04000290,0x2000080804d0501ba,0x210030140400c84c8400,0x116100000000800e]]
def g187H6 := limbs80 #[#[0x340000000000002270,0x8c000000003300000310,0x3080008800001]]
def g187D7 := limbs80 #[#[0xfbbefedd545454048110,0x85a804eca0ec406c6fff,0xa92a88ec492848ec84ac,0x2626262a40ec10eca8ac,0x4a2c862a862c262a2628,0x122caa2c6a2a6a2c4a2a,0xc19c490b81a0026c122c,0x25092643cf3344b026c7,0xe7ede7749bb66d805a55,0xe0070c4a6e9624388a0,0xa824a4c722029028f14,0x3008523004428e2628a8,0x8d3040b0b138e3c1cb86,0x36192ba58288dc88a508,0xe1444ec280903feb09af,0xf109cff87004ebd605bf,0x4841de80771de00a03fe,0x99c898eb9131df1107ef,0xce26449d7052469c7a48,0x37a3156c248f06275b02,0x18778491bc240bc4f223,0x51ea]]
def g187H7 := limbs80 #[#[0x8000000001111012ad0,0xe5c000000086400b,0x4090e4141f444000,0x520b35f0786100026510,0x801531b10849130031c4,0x31a02046e1b1d80f0ac,0xc040081800000000,0x4400c5d9200216c120d0,0x1b878000324ae1c562,0x20f530000]]
def g187D8 := limbs80 #[#[0xd41fe98ff503fa41fd10,0x62a0d830007f553faa3f,0x26506222300a1e40fc6,0x8a100a24718f9648e108,0x8b1e280930a147484963,0x42038a02971658a08c81,0x1628212a330]]
def g187H8 := limbs80 #[#[0x932f0001816854098405,0x600063c1800b09000002,0x48011e00000000035004,0xd520ba0000002102ba3c,0xf96c1000b20086604000,0x762c26cb005200,0x80064128305315198b9a,0x460a2892800d88861,0x3ea30]]
def g187D9 (j : Nat) := if j=0 then 0xa4188201bf else 0
def g187H9 := limbs80 #[#[0xd0000038c22000006886,0xc100001eb300000006,0xca645019004a]]
def g187L : Nat → Packing
  | 5 => (5,4,5,0,0,6,0,g187D5)
  | 6 => (33,3,5,917521,69,9,1037,g187D6)
  | 7 => (26,2,5,327685,51,10,1065,g187D7)
  | 8 => (7,1,5,0,0,9,0,g187D8)
  | 9 => (1,0,5,0,0,0,0,g187D9)
  | _ => emptyPacking
def g187I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupShort 2 37 0 7 3 2 g187H6
  | 7 => lookupShort 11 71 4 10 6 2 g187H7
  | 8 => lookupShort 11 67 5 9 5 2 g187H8
  | 9 => lookupShort 3 29 2 7 3 2 g187H9
  | _ => fun _ => none
def g187 : Forest := ⟨187,9,fun i => g187Y[i]?.getD (0,0),g187C,g187A,g187L,g187I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187B5 : CutRow g187 5 0 5 := by
  have g187P5_0 : CutRow g187 5 0 5 := by
    apply checkedCells 6 0
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
  exact g187P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187B6 : CutRow g187 6 0 33 := by
  have g187P6_0 : CutRow g187 6 0 2 := by
    apply checkedCells 6 0
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
  have g187P6_2 : CutRow g187 6 2 31 := by
    apply checkedCells 7 3
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
  exact (@joinRow g187 6 0 2 31 g187P6_0 g187P6_2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187B7 : CutRow g187 7 0 26 := by
  have g187P7_0 : CutRow g187 7 0 1 := by
    apply checkedCells 6 0
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
  have g187P7_1 : CutRow g187 7 1 11 := by
    apply checkedCells 7 1
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
  have g187P7_12 : CutRow g187 7 12 14 := by
    apply checkedCells 8 1
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
  exact (@joinRow g187 7 0 1 25 g187P7_0 (@joinRow g187 7 1 11 14 g187P7_1 g187P7_12))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187B8 : CutRow g187 8 0 7 := by
  have g187P8_0 : CutRow g187 8 0 7 := by
    apply checkedCells 7 0
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
  exact g187P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187B9 : CutRow g187 9 0 1 := by
  have g187P9_0 : CutRow g187 9 0 1 := by
    apply checkedCells 6 0
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
  exact g187P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187T : mixedTables g187 9 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty g187 0 0
  · exact mixedEmpty g187 1 0
  · exact mixedEmpty g187 2 0
  · exact mixedEmpty g187 3 0
  · exact mixedEmpty g187 4 0
  · exact g187B5
  · exact g187B6
  · exact g187B7
  · exact g187B8
  · exact g187B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187G : graphValid g187 (boundsBefore K123) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low187 : Lower true (varsX 187) (graphGoal 187) 10 := mixedLower (g:=g187) (i:=0) (hints:=65603) (before_sound K123 V123) g187G g187T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K187 := extendKnown K123 10 [(187,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V187 : Known true K187 := extend_ok (m:=187) V123 low187 (by decide +kernel)
def g235Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x7ff83ff83fffffd8,0x970a41400f801f003ff])),(BitVec.ofNat 152 (word80 [0x500508010800100c8,0x8500014210842108421]))),((BitVec.ofNat 152 (word80 [0xff80003fffc1ff81ef,0xa34310c000003e007c00])),(BitVec.ofNat 152 (word80 [0x6216110a0048209eb,0xa14300416b5ad6b5ad6b]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffc00001fffc87,0xc524474c1f00000f801f])),(BitVec.ofNat 152 (word80 [0x48098004c108240005,0x85240548c6318c6318c6]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffffffffe000031,0x2e4c7a200007c00fffe0])),(BitVec.ofNat 152 (word80 [0x104200210001081010,0x2087a02108421084210]))),((BitVec.ofNat 152 (word80 [0x44,0x90af89b3e007fff00000])),(BitVec.ofNat 152 (word80 [0x600c02060210302004,0xa481a0842108421084]))),((BitVec.ofNat 152 (word80 [0x33a,0x529a034bfff800000000])),(BitVec.ofNat 152 (word80 [0x807004380421c04332,0x520a020318c6318c6318]))),(0x0,0x0)]
def g235C : List ColumnInfo := [(8,0,227,0,7),(32,0,203,0,7),(64,0,171,0,7),(128,0,107,0,7),(0,2,137,96,6),(1,0,234,0,6),(2,0,233,0,6)]
def g235A : List (List Nat) := [[],[115,101]]
def g235D7 := limbs80 #[#[0x1552e2a46f03ee21f510,0x4b8a9]]
def g235D8 (j : Nat) := if j=0 then 0x346111bf else 0
def g235H8 (j : Nat) := if j=0 then 0x15 else 0
def g235L : Nat → Packing
  | 7 => (2,1,3,0,0,5,0,g235D7)
  | 8 => (1,0,3,0,0,0,0,g235D8)
  | _ => emptyPacking
def g235I : Nat → Nat → Option (Nat × Nat)
  | 8 => lookupShort 1 2 0 3 1 0 g235H8
  | _ => fun _ => none
def g235 : Forest := ⟨235,8,fun i => g235Y[i]?.getD (0,0),g235C,g235A,g235L,g235I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235B7 : CutRow g235 7 0 2 := by
  have g235P7_0 : CutRow g235 7 0 2 := by
    apply checkedCells 6 0
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
  exact g235P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235B8 : CutRow g235 8 0 1 := by
  have g235P8_0 : CutRow g235 8 0 1 := by
    apply checkedCells 6 0
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
  exact g235P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235T : mixedTables g235 8 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty g235 0 0
  · exact mixedEmpty g235 1 0
  · exact mixedEmpty g235 2 0
  · exact mixedEmpty g235 3 0
  · exact mixedEmpty g235 4 0
  · exact mixedEmpty g235 5 0
  · exact mixedEmpty g235 6 0
  · exact g235B7
  · exact g235B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235G : graphValid g235 (boundsBefore K187) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low235 : Lower true (varsX 235) (graphGoal 235) 9 := mixedLower (g:=g235) (i:=0) (hints:=83) (before_sound K187 V187) g235G g235T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K235 := extendKnown K187 9 [(235,[]),(249,[65,33,117])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V235 : Known true K235 := extend_ok (m:=235) V187 low235 (by decide +kernel)
def g243MarkBits := limbs80 #[#[0x9080706050403020100,0xc100f000e0d0c0c0b0a,0x1a191817161514131211,0x1a232221201f1e1d1c1b,0x2a142029280027262524,0x201f1f1f2d002c102b10,0x36353433321331302f2e,0x133b3a13193938202037,0x394241403f3e3d3c1a2a,0x242202282045444340,0x4b4a2049484038472a46,0x504f4e13494d28334c20,0x134f1f5251512020102a,0x442a3957205655245453,0x2a3b5920395220560658,0x5d4b5d5c5b5a3b2a2c,0x402a1360555d5f1a1b5e,0x63562424200213624161,0x2a1b4113522e641a4f22,0x1f2a525d686867666520,0x1f1f102a22131f3f203f,0x696a1320131b20206960,0x34346e6d6c066b202056,0x726d0671205d203b706f,0x246868733f5d20206d1f,0x193b5176754056741a63,0x246077454913681a636d,0x303b1356495b24792078,0x33137a13345540206d5f,0x684b1320491f3d244949,0x137d13287c137b495b4b,0x5520205d7f405d20347e],#[0x2d418063132455412a13,0x221f2052815d3424692a,0x4f833d064024492e6882,0x86561333408549002084,0x1b8a89561304887f8713,0x248d203d718c68138b51,0x5b684920408f134a138e,0x91139022222d56852220,0x51936d200013924e563b,0x951f6d20948a13130020,0x5c13961b193b96242063,0x33448a988320133f9720,0x491300755b3f20551b7b,0x13566052204160676d3b,0x6249975495f96960b91,0x6d00402e9b689a5b5449,0x5c1a499c201f20556056,0x9f9e201a202013209d68,0x20221f24492271332076,0x4d1f061aa185401fa020,0x92242a406d3a831b1322,0x2020634120a40044a3a2,0x1356382a52a369202068,0x5276137640a51a4a2044,0xa713204c10a620562a74,0x524949203d2aa9a84f81,0x8471ab5113139313aa40,0x5c96ac2024912a248a20,0x5b3f561a6d3b5c740656,0x7b52ad0e430069133863,0x91ae1300442a1351132a,0x563f064d5649205663af],#[0x7f3323377b13203b1924,0x402aad20441e5c131a20,0xb01a4f2020525213374f,0x33135c40132039913641,0x1ab1407649204f4e5f41,0xb420b35cb22a203b1b68,0x561a205013b5068d5655,0xa1332c487f6d4b192a40,0x2a206d8324202a7b7b39,0x2098442a20b720b62052,0x56562a4b5120b8207b56,0x4802203a0b137d574f13,0xa20eba20400ab9395649,0xbcbb3b3db32a56714b68,0x56086500663a13521fbd,0x3f939f1a20551f563b5c,0x133f5f1f3bbe9768205d,0x881a3c1a13bf6d132020,0x56403fc01339334b2063,0xc1202022108d55400c40,0x416802c2694a24911320,0x1300881f9a13852e2022,0x41132020562ec363396d,0xc513a04052c45624a013,0xc64124133b5652402a2a,0x68564420c15c3fc70624,0x4151066d1b89136d2ac8,0x3d1a2040566d20be4313,0x6933515524691320133d,0x69203d405b332e551f40,0x134a693d131320515d13,0x402a5d13399413203d20],#[0x133b5c13204413202a2a,0x2013511a202056201313,0x2a562a131f132469693b,0x6d1320242a241f5c1356,0x5b562a136d135520be51,0x20202e55132420496913,0x552a2013201356132413,0x4d2a56132a1320245f20,0x132469302067135b5d1f,0x2a205a205c1320131320,0x1313131a22304413c91a,0x202040406913205b4413,0x13441313402a20205b1a,0x222a3d2a132039132e20,0x133b135b5a20ca22695c,0x5b132013a7cb4920203b,0x4a2013132a242022555b,0xca2013be5020206d1320,0x13551f201a502a205b3b,0x3b202e561320131f2040,0x5d40562a3d132020563d,0x201f4413832013565d30,0x2013133022402a1f3320,0x44202a132a6d1a206d13,0x3dbe302a13242a131f13,0x1369402024201320204a,0x3b5d20201313136d8320,0x243b403d2030333d2a1a,0x2a441320]]
def g243Labels : Array Nat := #[0x10403201418083,0x140302010580b0,0x200220104a012,0x10001180856081,0x800210088c042,0x14040411094460,0x400220104c022,0x2203503816012,0x140302014180b0,0x420201808222,0x43020180a022,0x10403180856083,0x220320300a013,0x228020104a090,0x2203502896013,0x10010019050690,0x10403180c56083,0x200201808281,0x4a0201808222,0x410502c14412,0x420201408222,0x610502c14412,0x411501c54412,0x440502c14242,0x440088c42442,0x10403201058083,0x682182c06283,0x400088c42622,0x6080019082690,0x1408220104c0a1,0x4003201088222,0x611502c14413,0x208001a0c2690,0x200182c06281,0x104a0088c426a2,0x400120108c021,0x208020300a090,0x140300184906b0,0x6011411094431,0x620500854422,0x10403088c52283,0x140100184d0690,0x611201408413,0x1400220104c022,0x2080019082690,0x208020104a090,0x280203008281,0x410101c04412,0x4040009044260,0x60a001a0426b0,0x10403181416083,0x280182c06281,0x440089402442,0x2202403012012,0x420088842622,0x411201408412,0x400201408412,0x60a001a0c26b0,0x240181c06241,0x2230412890631,0x220120108a013,0x220201808221,0x60a00190826b0,0x400201808422,0x410201408412,0x601120108c031,0x400020104c021,0x200412890621,0x682203008283,0x8000008848260,0x8002180c4e042,0x2280500856090,0x240101804241,0x601120104c031,0x440081402442,0x1408220104c0a2,0x60a000a0426b0,0x4040011084460,0x80014120d8441,0x420008842622,0x808001a0c86c0,0x104a02018084a2,0x682182c04283,0x410201418412,0x420008848622,0x2040011082450,0x420088c42622,0x2210201808231,0x10401201818081,0x611502c04413,0x20400190c2650,0x240413090641,0x60a020300a0b0,0x220412890621,0x440089442442,0x4040413094460,0x2040019082450,0x601020104c031,0x800210084c041,0x60114120d4431,0x610201408412,0x8010088c48250,0x2040402052050,0x8080182c0e0c0,0x200201808221,0x420201808422,0x20804120d2490,0x280203008221,0x240001804241,0x2230201808231,0x800250285c042,0x420008850622,0x20400190c2450,0x230412890621,0x280182c04281,0x610201408213,0x400120104c021,0x4040089446260,0x20a001a0c2690,0x200020300a090,0x640089402642,0x620201808423,0x4040009444260,0x2002502896012,0x8001088c4a241,0x140820884c62a2,0x410201408612,0x60a00120c24b0,0x1408220108c0a1,0x100100184d0690,0x2201502896013,0x808000a0482c0,0x2202100884213,0x10001180c56081,0x20404120d2450,0x208000a04a290,0x40404120d4460,0x104a0088c424a2,0x800110084c041,0x611402414413,0x410201448412,0x600120108c021,0x4040081446260,0x80804120d84c0,0x80100884c8250,0x1408220108c0a2,0x10403081412083,0x2040503816050,0x440503814442,0x620502054422,0x60a001a0c24b0,0x400020108c022,0x4a0088c42622,0x208001a0c2490,0x208020300a290,0x80804110d84c0,0x420201c08422,0x608001a0c2690,0x2040503812050,0x10401181c16081,0x411502c14412,0x10010201058090,0x40020884c6222,0x400120304c021,0x20a020300a090,0x8001180c4e041,0x6040011084460,0x240403010241,0x420201848422,0x8001412058041,0x440101c04442,0x80004120da450,0x10010201418090,0x2220201808231,0x800250289c042,0x80100884ca250,0x8000010888460,0x2202180c86213,0x808008240a2c0,0x208000a042690,0x280102c06281,0x2230412890231,0x208001a042690,0x10403201818083,0x800208848a042,0x60a020300a090,0x640009042642,0x420201808622,0x808200a0482c0,0x200413090641,0x440089442642,0x140820884862a2,0x6040089046260,0x200220108a012,0x200020108a012,0x8000088c4a260,0x282182c06281,0x240413010641,0x60a001a0c2690,0x2040019082650,0x411201408212,0x440101804442,0x2040403012050,0x808008240a0c0]
def g243Mark (j : Nat) := (g243Labels[packedAt g243MarkBits (8*j) 8]?.getD 0) <<< 8
def g243Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xffc7ff09001e000f07,0x400ecfe4719df8fe0ee])),(BitVec.ofNat 152 (word80 [0x20802281866313119,0x2c4603588b86ca00]))),((BitVec.ofNat 152 (word80 [0xfff8fff2800000f0f8,0xe70310e0881e21f0ff52])),(BitVec.ofNat 152 (word80 [0x408140020a2295154d,0x68110f0011401207300]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfff007e00f0000,0xe80c1f030fe03e00ff9b])),(BitVec.ofNat 152 (word80 [0xb12080030cc626210,0x200409030260bc4c8c82]))),((BitVec.ofNat 152 (word80 [0xffff00058001f000ff,0x100fe003f0003fff00dc])),(BitVec.ofNat 152 (word80 [0x8c008c45e4894aca80,0xb00e80010000304800fc]))),((BitVec.ofNat 152 (word80 [0xe7801ffff00,0x1ff00003ffffc0000001])),(BitVec.ofNat 152 (word80 [0x100010000110000022,0x48204000ec8300000000]))),((BitVec.ofNat 152 (word80 [0x7ffe000000,0x1ffffffc0000000000e1])),(BitVec.ofNat 152 (word80 [0xe024e08046018c8cc4,0x97cb9298000400001065]))),(0x0,0x0)]
def g243C : List ColumnInfo := [(1,0,242,0,7),(2,0,241,0,7),(16,0,227,0,7),(32,0,211,0,7),(64,0,179,0,7),(128,0,115,0,7),(3,0,240,0,5),(17,0,226,0,5),(18,0,225,0,5),(33,0,210,0,5),(34,0,209,0,5),(48,0,195,0,5),(129,0,114,0,5),(130,0,113,0,5),(144,0,99,0,5),(160,0,83,0,5),(35,0,208,0,4),(50,0,193,0,4),(65,0,178,0,4),(66,0,177,0,4),(80,0,163,0,4),(96,0,147,0,4),(145,0,98,0,4),(146,0,97,0,4),(161,0,82,0,4),(192,0,51,0,4)]
def g243A : List (List Nat) := [[],[65,117],[16,116],[16,112,64,84],[64,16,81,113],[64,81],[80,65,113,16],[80,113],[112,84],[112,81,65,64]]
def g243D5 := limbs80 #[#[0x50d31481104c93148110,0x50941481104c94148110,0xd0d414811050d4148110,0x591434c1104c95148110,0x60c75501106087550110,0x54d43501105094150110,0x59554501105515250110,0x21572501109955450110,0x61743501105524150110,0x5535050110d8f4350110,0x60c71509105535250110,0xe1d41881106147150910,0xe0d418c110509418c110,0x50941c81105d1548c110,0x50e42501306147350130,0x50f215013060e5450130,0x5d56318d4050f6150130,0xe1572d8d406087050d40,0x591434c2105094148610,0x50d625021058d4350210,0xd8770bde8b8d6a6d358e,0x1b53696d1d9d33665cca,0x876f0dc5b636a6ccd95b,0x770ed1d93b0f4ce53c9b,0x2fc1f43d87a8f49e8bc6,0x192154614089531a350c,0x401364e223713e159001,0xda5cc4217058f5508518,0x60e7197658a5c1513930,0x501d75250605441814de,0x59299bdc8a6d706dd59,0x86311544916438d06150],#[0xd5dc8d597295c5d002d,0x75d837d640565c876d73,0xa1615168364ce358549,0x415438cd585e35867c5e,0x97464265a425425cb619,0x40875c9c039235bdcc32,0x1fe44765736e34c98119,0x5448816228d619d73740,0x496d7260e55093582812,0x18b595105962cc59,0x41a06d00000000000000,0x8005694224002b81c87,0x3c]]
set_option maxRecDepth 32768 in
def g243D6 := limbs80 #[#[0x50430589410c16150430,0xc17650430595410c164,0x5d1610c37650430dcd41,0x590309d1610c17558430,0xc161d0430dc5640c171,0x597410c164d043058b41,0x149105d05044176d0430,0x44174149105cc5244170,0x4c52044021481105d852,0x48110505204414048110,0x44153481105452044143,0x5d920441734811059120,0x48110905204423148110,0x44340481109912044251,0xd91204434348110d0520,0x4c110505304437348110,0x441534c11050d3044142,0x5d130441644c11055130,0x4c91059532443214c110,0x4402150110dc53244176,0x1d540440715011014940,0x50110505404413250110,0x441505011050d4044142,0x55140441535011054940,0x5011058d404416250110,0x44175501105c94044165,0x9054044232501105d940,0x50110949404424250110,0x44265501109894044254,0xc854044275501109c940,0x50110d41404434350110,0x4435450110d4d4044352],#[0xd95404436350110d8940,0x50110dc9404437150110,0x4407150910dd54044373,0x94942441765091054942,0x50910989424425450910,0x4416450d10dd94244371,0xd8d524437650d105d943,0x58910591624436454910,0x4407359110dd16244373,0xdcd644437259110dc164,0x8811050a204414188110,0x44165881105922044154,0xd0a2044254881105d220,0x8c11050630441328c110,0x441648c1105523044142,0x50a32441748c1105ca30,0x901105da32441708c910,0x441659011058a4044142,0x5d25244170949105c242,0x989105ce624417694910,0x44140c81105ca6444174,0x5c72044142c811050720,0xd01105d32044173c8110,0x44175d01105cb4044171,0x5c74244170d0910d4340,0xd0d105db4244175d0910,0x44172d0d105c34344164,0x5535044143d41105db43,0xd41105c75044164d4110,0x44264d41105d35044173,0x5d76244174d8910d0f50,0xd91105d36344172d8d10],#[0x4c121501301cd404c172,0x549404c1435013050940,0x50130909404c15450130,0x4c25450130949404c243,0xd89404c36150130c8540,0x50130dc5404c36550130,0x4c36250930dd9414c373,0xdc5644c37059130dd942,0xc85305ca644c37259130,0x4c176c85305d3214c142,0x5db414c173d05305c341,0xd09305db424c170d0930,0x4c174d85305cb614c362,0x58c6350161185405cb64,0x18d405c8635017118d40,0x50370505409c46350175,0x1cd615037050d401c143,0x58540dc9615036258540,0x5017090540dc96350373,0xd8e435017290d40d8641,0x985405d6615017298540,0x50172d85405ca6350361,0x5c76350175d85405cf61,0x486105d76350172d8d40,0x84162486105092184141,0x48540841744c21050d30,0x50210551408414350210,0x841655021058d4084162,0xdcd40843725021095140,0x50610509418437650210,0x84370506105914184162,0xdd9428417650a1058942],#[0x55210dd9438417650e10,0x84176552105955484164,0x551628414358a10dc154,0x58a105cd628417158a10,0x8427458a109516284174,0xdcd648437259210d0d62,0xd06105c2548416495210,0x84164d061058b4184142,0x58b4284172d06105c341,0xd0e105db4284170d0a10,0x8c154502305cb4384170,0x595408c1625023058540,0x50630dd9408c37150230,0x8c16250630585418c142,0xdd9418c373506305d941,0x50a305d9428c16250a30,0x8c376552305d9548c376,0xdc9648c3715923050d62,0x952305c2548c37559230,0x8c170d063050b418c176,0x5c3428c176d06305cb41,0xd0e305c3438c176d0a30,0xd037358740dc961d0172,0xdc963d037158f40dd561,0x9de3f8f63787f7558f40,0xaf6bbaeab7abe7e9f67c,0xba2e6b7addb72d6b3abe,0xbd6f4bcef0bbaedbb2ea,0xc9f1fc5efcbeaf9be2f6,0xd3f3ecf73bceb37cd72f,0xdcf6edb76cd9f66d7b5d,0xe5f8fe3b7cdeb79ddb75],#[0xebbadeafaae9fa6e7b9d,0xf3bcbef3baee7b6ed7b3,0xfc3ecfabe9fa3e6f93dc,0xa3081632c185bf8fd3f2,0x7eb20aea2641744b2814,0x1fac6f074b2c709b08b2,0xb01c2ca5d2ca3f0b438d,0xdd42c51814c0435fac63,0xb4a0a106512eacf7ea1a,0x800db063420c28d09b06,0x8ed2ac1354730ad54db9,0x3b3d22c80562c0845fac,0x6993cc205a0aa8f203c,0xa1bca0e86f237c19e40f,0xec65005c3b3a0ca8f282,0xea1ad9d2caf103c1979f,0x2f0e709ca18a453010b7,0x3c1914b308345ea1ae4,0xcb302d501c2ba142c515,0x599328fdeb02031ec2aa,0xe538e6d830c21443b0ea,0x4730c292a22871ea6a10,0xa662a83da2a13aa9aa8,0xe4666ba1edcee817a6a1,0x30d6baa4179ea1ad43d0,0xe3530c21490b08301ac,0xaa17662a85242c285c3b,0xb026095b206e62ca3f96,0x1c10769a861954ba81cb,0x7aa63b9ea1ac68a848d4,0x30c20d50b023584b148a,0x67a86ad72b8a329a8479],#[0x438c1971b2e61c41c106,0x5eba641b22c29719b001,0x1da7a18650f0218aca18,0xf0c3084c64ba23622a9,0x637a2a106662a85198aa,0x1ab1030437aca98a4eb0,0xa50244290eba64199ea,0xb81be7ac4ae98aa2bcc3,0xae83010c232a36e6004f,0xea18e15ecac842c094dc,0x9aa83656b21f41b06ff9,0x1ac0c846f087452ba836,0x86f064253a94edb2865a,0xb52b13801b070e88b209,0xa01f08c49ec1ac12e826,0x5306c281956c86252a12,0x9c13ae46c4eb2c9a62a8,0x6f31ac32d46f0c9e94b2,0x19a53a650f4fb1a723a8,0xa36aaa11e1cae65813c,0xc017e36e72389b28fd0b,0x2ea374eb135d0b022640,0x7c19b81f083252294ed7,0x4a406e4fc01bdcb02590,0x42c193e38e66d42c0939,0x95f0e83ac991e41b0540,0xd94b20815ec4d666ba1c,0xbd2d0c1473c08785b0f0,0xfa672a1fa9e847992b13,0x8fd4c64e407c28114eea,0x2e606c1c654e40e47cb2,0x9ea3f067c10c34491ea],#[0xe46f0ec0b581f0ae443c,0xc0cac1b0ae706c22053a,0xb0c3e72c018ab2863007,0x6c21a85f070a8ea19046,0x1f0aa659423855262990,0x4ab205266ea3f9eb92b8,0x54e426e54b13412e84a6,0x342c09454e413b07c220,0x695ac88570b91e81b026,0x3c07c2aa01f06e44eb13,0x83c3b0e7a0cc29881b0b,0x4be06c321d1b0ce146c3,0x9b210b02a542c28655ee,0x62f95c08b90f02446d2,0xaa1544b04df73b98e5b7,0xb06e484c244c6b0c5488,0x3b9bf53b0c050ec13dc1,0x3ee6d8a6a11c1b2a6c85,0x68b9a393f06994ac3051,0xd3d046f06c19ae210842,0xe17c0c281b0b3b4fb1b8,0x653aca0588b28ed5f005,0xe606c3261b2a0da06c0c,0x9001b0cc307c28c95f00,0x8201ac29594aecc288a1,0x1a65cc629692b93c9cae,0x6f89bb3c13ecada07c,0xbabc8970aa006c2b953b,0xf006f57182641b006392,0xfc11bdcce06279b980e3,0x6b0c2643c28a41b0a6e4,0xec38951ee3031ac3060],#[0x41b053d87a148d52ec19,0x43c08e94ae31756b0cc,0x151aca9453ba8041b02c,0x2c55c3b38c302d607c11,0x1bc630ae24eb20141b03,0x64094b18e53ca46f4e41,0x1bc9cb02a390b13aa268,0x64b06c39a01f088889a,0xb14801f04e7474380ceb,0xf02e81ac31201f046556,0xf439241f0ac74f311bc1,0xcae81725c290cef06a00,0xf4393c6b04b672ba1e5,0x952c88f42c20d03b04fc,0x9564039a12c51271b90e,0x883b0e9e0ec19645f046,0x7106c11bc1b033255431,0x2a99aa8d68e418750f02,0x87606c14055ac7185321,0x1335b3012673b90e59ae,0x64a73ba0867cc4ae52a,0x3136a9b023f06c2840c3,0xb0e764fb91b10b02544e,0xfb18e03b0ad60cc29603,0x56ca978eb23b5b2e8788,0x56b22195acb1507c2afd,0x9f6e10306c0caa56e26d,0x56b0c601b02bd5caa28,0x9c1b0b3e0dc0a1c1b034,0x2e0dc0a729e841906c2c,0x9e46f044292b9bca3f06,0xc147dba9090b082143c2],#[0x18755f0e7392a13c81b0,0x8fa92a0bc8470cf98fc,0xc115df2ca540ec1a5a15,0x706074e32b6952ca331a,0xfc3b3e52831d73b911e3,0x3f0e7b52a1301cae05c4,0x56982654cc4db92aa3c8,0xc3b04d672ba086ba8420,0x59fb92b81b05274ba01a,0xde7aa8ba31c21094ac53,0x1988421003f06a366ba1,0x9cc1b0ae456984650f06,0xa024ea01bc3d0e381bc2,0x136a26ecf18fb18f92ee,0xa2bf5343be95ec4c84f3,0xc0846bf04194fc191552,0xb0efa66aa3206f012d72,0xea1adc930aa589b84094,0x38e46f672a1667b02ae8,0x1ac31492a83194e991bd,0x9f0ea4207c13983b04d4,0x86ea123d5eca9656b2a5,0xa41f049d42c20883b071,0x2130c212c6b046d47c2c,0x495ca609770a12006b0b,0x29611c28283b0e1a07c1,0xa8381b0b3640c1095ca6,0x6f46c380db6e6384ab,0xb92ac1b0a6307c12a5b7,0xf06734fc1a7652c4396c,0x8b20681f04bf73b98663,0x3f02c856b20a182a8da8],#[0x5590cfa27006430c28ec,0x15f00659fc02b9b420da,0x96cba0b11aca5b0fc026,0x6a9aa85806c14f01f02e,0x260dc1a5d0f022a4eb2b,0x654a40c04bba1a5b281,0x8a772ba0659aead6aea1,0x3898eb0a2b4aa09ad1aa,0xe70656884e10f0a700ec,0xa9b141b0d350ec116a2a,0xae61992c0bc8370a976c,0xfc10bc6b0a2756b2079c,0x3ee65656438741b0e670,0x4bb8c09cd025942c213e,0x53aa46f57b12594a42e4,0x356c34153f060498aa25,0x254aa4e407c131d03042,0xe706c0ce03306620ec39,0x814c64e84ec34981f0a,0x46f0fc207a12c4f973ba,0x9b99b700da3ac19313ce,0x32957b0b215ec69646a,0xa193d3ec813a6c08ec1f,0xb04bb9eb8ab9b2e68ca7,0xfc11f81f0a9984a0c5c1,0x22ca4a46b2a61cae8700,0x56b296624a8419ea0aba,0x4c304d68ea1ada22a856,0x4aea113d2a84a693c107,0x1622ca501bc30683b0ad,0xe30fc39c984a8da56b2b,0x541b08a806c0cbd4ac4],#[0x4dd66ba23256c63907c2,0x10645b0ceb24c2a90630,0xca1981c1990eb064da4a,0xa196152c6971ac295652,0xb02be81c1a6938a46fa6,0x7c3c1972ea9556b94846,0x6b052152291b95ec8121,0xfc1a594a84aa8fb9af8,0x83f049b07c1bf94ae8ec,0x6c2cfdaae68d4e4197,0x866b029f16c1c313ac89,0x7f56884c81f04e958c23,0xa650f02381ac1158ff02,0x2f246a8b99b286b94e41,0x206d5ac53952bac4e4ae,0xa91d53213001f005e94b,0xba425cee8190fc13ba24,0xb0aba53213355f010452,0x7a9b9a790eae0cc20cce,0x5b030b71b91212eeafb4,0x73b993dca82b95390300,0x956ea004ab2245cae829,0x41410de24a8566cb8ae,0xa26871e25c1a7d5ac88,0x970ec3919770e9f43c0a,0x3a01f02c947b138556c4,0x44753211b93aa06f5329,0x14795ac90553a91ba52c,0xca924fa19aabc841992a,0xc28254ae90853311b952,0xeea039ec02b94ac4db18,0x9c20219aa8dc06c1ce11],#[0x330a334abac51c2e4821,0x56bb062ba843019c281c,0x19ae8718eb20ae12c533,0xa72b81890b081747c2ba,0x1a3706ce52b146db100d,0xf8731825c1b033f57b22,0xa546b0c7642c29606b0a,0x4290fc38b41b053e72b8,0x214cc50cd510c33e69e8,0x6d452993904f04cf30c,0xc20c94cc4d953901b83b,0x6ed1c1ac31c94e42e406,0x8b0bd45f090916c3c1a2,0x1b04bf17c0c1d5ac6968,0x70c03450b02763bc1874,0x95462991ac314d0f0a19,0x11ac32c41f08a89fb1b5,0xa90b082006c11981b0e3,0x2f52c3c4e52c81707c2a,0x3b93ac88957b1371cf02,0x46f06c232d4cc4c057c3,0xab81f0a6e60423693c6,0x63f57b22152ec8149fc,0xc10c55ac33742c0964c7,0x9041952b14e95f0e8417,0xac30e156c46272b9162b,0x4ac48b4ea19bd5702321,0x9f392b847084088aa105,0x81b0aa6a7408fc6f021d,0xb983a8fd4a64e86cb9a7,0x446f064092410741b073,0x3952b1364630add73b89],#[0x3943b0e956ca01be9a86,0x90806c2aee7ee63b07c1,0xafd0b023766a1b505f0,0xa8d455b1a5db2e61a54a,0xc0cc11ac4e186b23a99a,0xf06a954ba8314aa4e806,0xbc2874ef0a2b95c08753,0x6b04f806c29b5cae8221,0x53b8bf4c30ad607c2ba0,0x83b06f694b291d3ee46f,0x856b0c452f085e92a1bc,0x3d9aa85954a8b9dccea5,0x5c3ac18d46b0cb306c14,0xbca3ee66d07c207d52ec,0x6f54b134d52ca9792c1,0x346c5b030c42c291d3e4,0x66e0cc09657300e106c,0xb20895ac51516c317c1b,0x302fa52b13052cc86b94,0x9c21094a426e09c2b1a4,0x4ee72834c1986ba84178,0x7c13303b082806c14b9,0x4330e8d76b28fd190ae8,0x1a6a193d4a846e06c1a6,0x405f0ceb6d283681f0e3,0x785590afd3c846f4ab8c,0x9a94ac4c054b124a3ac8,0x65810c282c23052606c2,0x19781b0b2e57c39f10b0,0x84cb06c2afe56ca194fc,0xc21021a852354b21894a,0xb02520cc1a5c6b0c4931],#[0x6c282c1f065e06c1cf50,0x1b04e74e901bd4aec7f0,0x5aaa2841b081f56b14d0,0xabc64190dc0a4df2a8f4,0xd4fc199626ca4a88a1bc,0xdd3f072555c0978370e8,0x2472c09d4370a9256b1c,0x93554ec6292c23c94ee5,0x4b872b91e53ea06f42c0,0x135606e60231c28ec6b0,0x6631ac31dd5acb3430c,0xc2b9503042689c21001b,0x4a8551ac31181f050007,0x2b145a07060a4fb1b7a2,0x1f06e6acc08aeb286295,0x7cb29ca7ee2aea7a11c0,0x956eb2356b14683d0e35,0x556b29d63ee6b784c23e,0x493b046f54b22853aa6e,0xe452b9c5df2a91f46b13,0x9e46b06f811c13ed4ca4,0x4394eb204d0b0224adc1,0x24983b0e4f734018a56c,0x66d54bb1881f086a4eb,0x32b681b0ae807c232c6b,0x308bc4ab222952eace4f,0xd103695eca599e392b84,0x1f0b2543c090c1f08a76,0x4ea11be66eab042c09dc,0x9ebfbfefffeffd5ac812,0x1ff0bffdd3770037f,0x80000000000000000380],#[0x5a000000000000000016,0x1680000000000000000,0x5a000000000000000,0x1680000000000000,0x5a000000000000,0x1680000000000,0x5a000000000,0x1680000000,0x5a000000,0x1680000,0x5a000,0x1680,0x449c778b61060f20005a,0x61602904b385eed5982c,0x9905a2516036e1a10539,0x202a4a7cc929a1e03be0,0xd931a12030d588d941d2,0x31d48cd141c16033d886,0x8a41a02ccd80d5318180,0xda90e561f2403a629ef5,0x1e0335a8ce929918036,0x5830101c030558ee562,0x8904120409894000609,0x156020149240a1901807,0x4a2b40e10030081c182e,0x642a52520a0340b0837,0x376848090108a4ac360e,0x4031037e019c221e2611,0x3603961b8443c70a2202,0x23c444c9924e6b43bf02,0x60c401201a01ed050120,0x2166c21b0a02103dda14],#[0x1881cad0803ba42403dd,0x4040138443c843cb0be0,0x30c0d16c4a04807b842,0x27029b0d90d90c786207,0x3635a081762b219a0b01,0x85dc5893c62b211a0a69,0x419a0cd04396218a14f8,0xc86683df18a3c625702b,0xfc623218ee31990f586,0x8462854e046f7d145321,0xc0ad0690a6c26914d06c,0x53038]]
def g243H6 := limbs80 #[#[0x61401158402142854822,0x411a4610216588219a40,0x22051049625059401901,0x5c3c4304a8d450528066,0x52c09c10064100474ca,0x2f3cc489edf9adb98c06,0xc995694d0dbfa2679840,0xffd1c00000000000001e,0x452a400fff5fffffbfff,0x680efb80384b811c,0xe4605c17550000000000,0xb4f06f1cc9320c801f25,0xa37e284e9358b4458704,0x626a195349f63d206e24,0x14ed651e882178f11493,0xa1ec43108a0166238405,0x6c5105f6208]]
set_option maxRecDepth 32768 in
def g243D7 := limbs80 #[#[0xd08105901050c1050810,0x584305083050430d0c10,0xd0430984305903058830,0x1091058c4058440d0830,0x4c110481101491014110,0x50d1050910501104c910,0x59110589105491054110,0x901108c9108c11088110,0x99110989109491090910,0xd0d10d0910d0110c8110,0xd9110d8d10d8910d4110,0x50530501304853010930,0x90130591305893050930,0xc8530991309893090930,0xd8530d0930d0530d0130,0x18d4018540d9130d8930,0x58d405854050d4050540,0x98d409854090d4090540,0x48610d8d40d8540d0d40,0x50a1050610502104c210,0x58a10586105521050e10,0xd061098a109521059210,0x50230d4210d0e10d0a10,0x5523050e3050a3050630,0x952305923058a3058630,0x58740d0e30d0a30d0630,0xdeed6fb757e7f3758f40,0xd6df5f9fbfdfafb7bbd5,0xef3f9bbfdedfefb7bbbd,0xdfefeff3f7f8fbfdbdfe,0x4248f58a68eb91059435,0xdccd86ba10157320e0],#[0x88024b15b3564be8ec31,0x94b85741620ac4a8b905,0x83a25717e56e145058a7,0x41629c86874ca5c2c94b,0x65e0ae4f5e504a83bb5c,0xae724d5900a4b1cd077,0x69c1dd0d1932857a5124,0x58a5a12a5605767476c,0x49a4b14d4b652a4ae291,0x2bb052970c892cb35e50,0x953564c6c68655158458,0x77334f2a2486dce124b2,0xb66ac81415db225b1950,0x4825415d931db1c56154,0xa815d9394b8444b655cf,0x5c2c34a19362549a0ae4,0x782bb0c7a312456e654a,0xbb060576be8a841c25d4,0xe25714a92c871850e683,0x72120ee5a015d90b1a1a,0xaec00e1ccd83bae207,0xe821050e993b89505764,0x95c5318b28545751a84,0x51702bb121973488ac37,0x3b8326953260aec5185,0xa5b0776a056e1046dcd7,0x4b76b60aed4109d29b12,0x1a682c5752d88a83bad4,0x4ee2510d0eb02bb4f417,0xc18d592ca1314e077036,0x45d089ab24e2b70800ae,0x4e20ba0829723824e844],#[0x2ba070775d00eed7d259,0xdb09758c92c848a5c2aa,0x5725684c414ddc84b1a1,0x482a94c15d80a4b2130,0xaed8dadcd702bb170772,0x18d5c44b1b84107760a0,0xdc2f03b9622970228ec3,0x402ba2a79412432e6e4a,0xbb5d3564aa8ae434a5cd,0x511759084c42cadce683,0x61b612eafd750d702bb1,0xae529259263ca09d49,0xe8ec1dd7382bb5929742,0xd2590ea5b0ae7931240a,0xdac02bb393b638e52e09,0x82bb0b4262ae0aed5415,0x84519731e0eed3c15d64,0x4174a692c65415ca494b,0x4980eec5815da8a0b157,0x56e2b815d9a25b81b297,0x9998d0e69db99b2970cc,0x15c650c39c24173a66ac,0x9728aa5a3564068ac214,0x4b86339632e0ae8f12d8,0x412b7324f2827029d479,0xb712a4ae2b0adc8ab038,0x7e0ae8a415d87a3a10a7,0x4a854a5c1314ba132671,0x54d59289cb1d00773cec,0x5c8f94ba281b730af042,0x7b4a1cc4b64240eec5ca,0xb86529743a14eafc95c4],#[0x335644e22e914d590614,0x622a52e9692dc1914ba3,0x66ac95da4c8e82bb6549,0xc4301dc991ab2506143b,0x885c9f9cb18107730482,0xd8094b82c0773a88ac2f,0x8db99b05762262ca2c1d,0xb5c0772360ee388c9945,0x5762c0aed75ec84a82b,0x40ed486b8a5cc924b11f,0xd0e6b81dccd82bb04467,0x41d058830cb9914254a6,0xe1c4a82bb1e1973708e8,0x1083bb002b729a82c561,0x3bb303564bc6e8724a5c,0x2005759436e770a5c0f0,0x576580ee3a10588594b8,0x1262cb452596d82bb2e0,0xae4ecd59020cb9a23572,0x5c15d54b0aa4d39637e0,0x5c5422a10a3771126ac8,0x483b9674b769aa2a8a09,0xa1ae35640c52e0e41dc4,0x62974388aea1cc596fb4,0x412482a95889c9fa0a1d,0xe52e474adc271cb90e7a,0xc80029d6303b8b229701,0xc9dc4b1aa1c90576066a,0xcabd909349653e52e87,0xb0aa150772a856e36d85,0x9470776a20aecdcd5905,0x81525c5ae48e0548996b],#[0x52b028471d588b17b943,0x5ae8a195097b2aa15827,0x84a0d04917b932815324,0x355304132284f627504c,0x9297b9404f64325ae891,0xa99583752a5eea54b5c,0x1a75423ccca858b5cacc,0x1423b06a8555551426b2,0xb8fa82920d0d440a14c8,0x2ea560d0093aa9164d65,0x90b5cb340a1158164510,0x5089a6b15c2d724eca85,0xac0a9152d74445ae51a0,0xa12e2f74345ae8de0484,0x583522aca84e60948ac0,0x404902847cbdc8dc1a99,0xb068648b5ca2c0aa1581,0xea99d509216b93683504,0x8bdca132aa448154385a,0xc9c96b95765429d0484b,0x40aa1383212b04c454b5,0xa1c82422aca855e09497,0x76622c9acb38b5ca2412,0x1965ae4e204866c0aa1f,0xea852e0550ec0a1337d4,0x665950a03b291682722a,0x994ac1a11c81502a9ec,0xf0c1a8154d650aca8572,0x99158143505ae845350,0x9280522b0280495550c4,0xc712d00ea560594ac0a1,0x405aea94bdc8abea0927],#[0xae590b5d10b2aa162d74,0x560c85727b1304d65285,0x5c8aa7b14281622b00e4,0x916ba344d622aea84de0,0x90ae65544b0464560504,0x87f712d06e4560590940,0x76a09e874d3d8a316b8d,0x9ac8d1358a726b99b4d,0xa924bdc6196b9c94d640,0xb5d8b40b8ae4d72a89e,0xc1940b94d4d73ce5eeb7,0x26b8892f719e9cc8c60d,0x2304d65869ac88935c74,0x8173b69ac93cb5d9326b,0x3b65ae698b5d6226bae7,0x9ac9753d91a16bb3a814,0xc019dc60c1a14c2f72b8,0xbdd57a6b2514d642e9ae,0x9926b19681759b02c4b8,0x6b1424c65849aed7d39c,0x4e4e7292da86b935c592,0xd624a5ee73e05cd733a1,0x9a9aeb520dc5716bac94,0xae2ea0dc0da6bb068171,0xa0dcd717ba854d43a65,0x50ada6b9094f743506e1,0x716ba352d757302e1720,0xba314f43c29ec8460dd5,0x62f732c9ac940b5ca497,0x712a9ac8a205c6da6b2a,0xc9ec51135d6527b1a681,0xec44b5c6a96bb342f759],#[0x8bdd61a73b304d75925a,0xcec26b2192d727e9ae4c,0xa6bb2f82702d02e13cb5,0xb052f762c5aecb205c17,0x2d73ca5ae39535917a6b,0x5c89aed3cbdc973ea095,0xcae3053596497b9504d6,0xa693590a97b8964e6284,0xb5d7227a1526f73365ee,0x6316b94a2d757c5ee0c0,0x73ae775626102e2493d9,0x174f73345aeb29359122,0x3732b028534b5d87c0b8,0xb69ccb260d08ea6a1c98,0xee7753594596b8268154,0x93d8e117b8164e54c05,0x9d64bab1344f4276caa9,0xd97bac22d76429ac92d3,0xa1c94d73c4cae1053509,0xe4c72369ec882050e6b2,0x70649ae5893d96197b95,0xc9ae351358d326bb514f,0xe328bdce127b91b4d762,0x535ce496ba4b4d65845a,0xccdc0badb4d642c9ac80,0xc1312e4d63b09ac8153d,0x9024d64229ac8ba0dc4a,0x2d743c9eca999552326b,0x4845eea593d94b26b206,0x9aa9253591016bb30665,0x9393d88b41b8434f624c,0x5cc940b8166742b89ac],#[0x9732a1c24d65ae9ecb12,0x7b8b04d643c9ac85201c,0xc26f73b906844d3594b1,0xf716502a8b93592fa7b2,0x7cc8ed060950997b92f4,0xee3459952317b8404d62,0x599d097a6b9d44d64245,0xdc0da6b2214c74345aea,0xaa6a1602f71be9ae46d3,0xaa492f71ba9ac8c59950,0x176626104a8760dc28b2,0x62c8cee106050ca97b84,0xa9cc8693592e37b9854d,0xe45cb5c5316b93e4d645,0x609c9727b23083725c5e,0xd902739674d75d09aed7,0xb2b1c84d62ae9ae59cb5,0x94981739a9ae66a05066,0x6743849ac7093591aa6b,0xa09acb18bdd9826b968,0x9aeb89d589026b295817,0xc59358f297b8c12d75ae,0x3d8a027b1964f63809ce,0xe126b94a65547c5aeb19,0x6b2a581755c9ec859bdc,0x5e81732a9ce529358e4a,0xd64305aec6539c8da6b2,0x84ca8700bdca726bb304,0x2836d35d8ba6b2be6c73,0xa05cada6bb014d71950,0xdc9916ba954f42c09ae6,0x1c0aa4d2d75165ae0e93],#[0x3a1a4d63329ae388b5c7,0x84d646e9ccb09358e7a7,0x72649aed713594d27396,0xf0282b935d0d26b8684c,0xe4b93d910b2b2c84d70c,0x1ffffffffffffffff02,0xe207fffffffffffffff8,0xff901fffffffffffffff,0xfffe607fffffffffffff,0xfffffa01ffffffffffff,0xffffffea07ffffffffff,0xffffffb01fffffffff,0xe000000000,0x3b2000000,0xec80000,0x3b2000,0xec80,0x13283a4092010c0003b2,0xd0b0627708ba1d8061e,0x492f0469104a3ba0d9c3,0x9a8a65d98285b0156a51,0x1e48229f527829d3c6fe,0xe9ef268a95524148bba,0xbd4adeeb352b9ca9b29,0xdb3b572d0a32e8c75b08,0x87bcdceec3a7ee50380e,0x144010b1c19701cbf5cf,0xd170e0048f51edc66915,0xfa39c1306003e34aba29,0xebfb6299e180d8045b7a,0xb803f32251f960f89804,0xd1105004f42b42c21958],#[0x6299d94098042b92c249,0xb72ea89f14860048bc3,0xb004237ada318910a804,0xe93090045382da71b928,0x42da4190d004dc1b5291,0xa3d32a79f110b00453f3,0xa805048be34a6178c004,0x3188a8046bcb22c9e140,0xa23971088804ac43e30a,0xbc236a9a4968c003bb2a,0xc004c4438b125178c004,0xd11890046c0b42b9e168,0x92ea4188c803d3832259,0x6bc2fa1998d878050c1b,0xa802c26219b970e06004,0xc8e080049c3b5ae21980,0x6281f980b0046b9aea91,0x832a79e189289804f3fb,0xa003eb82da4991188003,0xe908a804b3cb12599918,0xca31690088045b82f289,0x8bfb6ada2160c8043362,0xb004d44372aa0148e004,0xf940a804740ba30a2970,0x8a21913078043b7b1271,0xe42352922190c803db62,0xc0040372a239c1388004,0xb9007805046bab0261a8,0x91d988e89003bada8a21,0x7bd31279f168c8042b7a,0x9004ec73eae23170b004,0x1988a80443b2d229a918],#[0x1259b90898044b9afa72,0x3b82f241c920a004239b,0xb0043b6b0259c9188004,0xb138b0044bb2ea79e960,0x9231c130a0046bb30261,0x372c261c938b003f35a,0x9803fb3aca29b910a804,0xd928a00433ab2a61a120,0xfa61d120a80493c30251,0xd40372b1e148a0040382,0x800463c32a89d948b804,0x28381129203088c0b090,0x2018b91408a808a09820,0x631208cd284a00004325,0x29086a1434205c1e2400,0xb1e2d191d16197b2a1a,0x227b087e0a3076015c15,0x42404008bc215b992132,0x48820601763625e10978,0x35b71446a067891efe0,0x7f40224c443cf014647c,0xcc61136b0222018e290e,0x848f603907a151aae122,0xec322025f808503403ab,0x968e26268c113cb64bd6,0x7c03de821d7fc1249f21,0x400840e2fb0899f30264,0x91981bc035b71445d624,0xa12178a23277062e4ea9,0x9116f89117e024f010cb,0x907a8453d4713201ef80,0x5d0915780d12f0064403],#[0x3086f8077c88e7084206,0x33e1120f510d581a40c6,0x43bb091f8077e024dd44,0x8448903d1a6887891b40,0xe0219e246903ccbc18cf,0xa20790318f510f6b0226,0xa8885e90631559445db8,0x42e8483f321cc68226df,0x12761a9322019cc84820,0x98de8091e268c8206732,0xf0a322af80887c224cd4,0xe5a0321df22413d044a0,0x697843ab848dd4b064a,0x626487c08f734869036c,0x7410c7a88680abe050c9,0x449438642ce920f31113,0x1d16b0648ec94c87c22,0x7b0855c231f94f44481a,0x64c55c23481caf1110a0,0x4883db43da51443e1127,0x33be4493ea0a200539fc,0x6b4222f32a21f611ee04,0xc4466061e40c79114d92,0xefa9220fca7a23e01889,0x5c08e7f4022360357e02,0x5e108c25e266028bec22,0x78e088f603d38688f404,0x780d9f22633c0400900c,0x8d2f0867c2243be448f5,0xab031138893456523598,0x4789a324c21592f12a01,0x4806b26867c224598c22],#[0x680601403009e2472a8,0x22fc0443fc0893d0436c,0x1a01cff01222b0343c8a,0x895f0286410398427b0,0x697d2a25bc04a80863b,0x11ab03d8af1137f24356,0xe04132ec8431f3d244ae,0xc40ee423ab84864133,0x88eb84880a31a63ef0c4,0xe025720635607b810cf0,0x660496f012a40c78486b,0x4d65444f0463de426809,0xfc04801514bd190ef912,0x1940f7510ef2c789900e,0x6f404d8429fd0088729,0xc6c544c9176e28870256,0x10f46c4cbf013add864e,0xc73423be448be0488bf0,0x50e1907c81116e043e08,0xe2226f490efae12140d2,0x483d4433c48e7d414495,0x551937e021cc68221e48,0xc048012c096057c88d3b,0x9d122381ae40c624d0ef,0x5560675c245b71445815,0x3511120770918819ce02,0x12253b1a0ce5234e073e,0xc44af4263b088f823df0,0x49a428c698dbc818f62b,0x2045481bc03b311e9534,0x257e031843863b848f0f,0xc21c9f21d72063ae5a03],#[0x6ac0d0119c230f206318,0xc801240d2075c818eb84,0xc234047c11a780b1c016,0x90f7c0488c77c890023e,0xcb621e62224f8d0445f8,0x1cbac7c5d8b2e84bc420,0xe98f23e630dec907ca87,0xf560656ae98ca30d8c25,0x2ab58b6a856c897685d0,0xb44075416aa1574c43d4,0x6ea90d3d898edb2343f8,0x8797426025ab12728532,0x60532b10f81c714c7350,0x88485c58e6a10f63d439,0x50abe98850dfa26d50b7,0xdb236fa98d5c0ae5d0f5,0xe7221cca1416c5063d0c,0x44ab08f250db562c0e98,0x4785921e1648ae0471a5,0x416f01512c22b6c8e22c,0x459742d8f50fb8418e19,0x63c0f98cfac8c31a6336,0xb116ac5186c49e315711,0xf1762831ea2590d844da,0x2c512b14d50b30a63ab0,0x9b5620cd8b7a543b212e,0x83166c31de63ab0ab660,0x98b83f4c65186c65b0a7,0x5510a30d8cf80e6a841e,0x5918f654455a10f81ce6,0xe58496c8b32a639aa11f,0xa867809dd85327708319],#[0xaa875d313754c76c8a76,0x1961b116ac5aa85bc42d,0xc0a8959853271762d5da,0x9ed0c68333e5a2166c43,0x7d314534c66d91b6ac43,0x64e869c9887610f8bb12,0x2]]
def g243H7 := limbs80 #[#[0x91215808202a5682012,0x6a8024424a4184620a80,0x5042218844441022240,0x1461604965241405982,0x1a4128819a08055644aa,0x20558006a912882100,0x60925005004420058621,0x5205a19108812144800,0x28406882182160062015,0x158948469a5811855a0,0x98a4000241a018608001,0xa0025890001a29806412,0x85888962509a800a0005,0x2818420864a50885014a,0x25000505010024150029,0xa496004492080290880,0x604000a0120a911a1600,0x6880425009254549a022,0x1645598454a821105182,0x44989610005824251900,0x56956184545888a20058,0x561210a05015442a5200,0x45404125058948951004,0x9a261295940555109444,0x800510a0404554804401,0x9a9a6254214152220418,0x5a951020502a12510aa9,0x5402a055015894251025,0x58aa5486284806226148,0x11a6250841215a080648,0x81800520506198618011,0x61a025048660a4402486],#[0x80286881940490a12948,0x1942429080608096a0a,0x224080041182a4444810,0x802822a80605a1412485,0x2286115145805aa829a0,0xa0a50a42014806a8424a,0x1928009625aa18a8124,0x4228040005240060586,0x61a881848056a2868220,0x89185585628566009a05,0x9840116152526809209,0x9051a8814602205a8204,0x9540401920858020a54,0x924a16122a086969601,0x5418120224400108048,0x44a1901041a440691809,0x81219928549aa4160140,0x138f20038c6f9605020,0xa9ddb93060b8474fe481,0xaf27650911730eb95997,0x4856aa0825ce82b6a1f8,0xe9abd849d10582422453,0x1160a20080dc6683c145,0x2d0209ca18f48122d30c,0xb2507cc0310e0575cb10,0x3330c548125206514381,0x4c13f8fd1be810cf91ac,0x5861f5409a8ccc8a0352,0xe074e8081010a090032e,0x307585c506c3ed2837d7,0x10da4b036242892c5336,0x84402889ed2850d6058b],#[0xb4af51800c05c1685527,0xab289d04050487781963,0x2f513048d40028e41ea2,0x683a0312c4204abde148,0xd058591566c11a48e40,0xced257a68a46ca0225b0,0xfdc30a12286829305279,0x9590f064668a70e4c8c8,0xa18f220897986402685c,0x6fba44cd60a6bf445241,0x835fb000f64294dad178,0x64f3c68119321d4ea52d,0x6100651410ecc7323c63,0x3951f54a30c85a43f266,0x6395cd9c5d07dc8ab708,0x3f1527f8e6d04dce0501,0x8f7b558834f1e2e044c4,0xd8c6c571ce4e111af0cc,0xb02a5f671c1ff658f89c,0x3a1ce78ff22e030788bf,0xba979c01b2dfc699bc4f,0x17f6f1752f57099b1982,0xbcd00353513cab11a102,0xdec6e1609de04d753c92,0xd6553b19c2e32114b623,0xcf3ce1f7984b97d6af9f,0x9ef1cd10ef9e82d16b99,0x6fcda726907d02ba1a5a,0xd665818464c5cd689e19,0xd3aaa7f20528654930c7,0x8dae639600e150e6f695,0x3292e3f58c376b13cc4c],#[0xf7fad9da72751c5c328b,0xe72a4acb23891ffb02d9,0x19f4f0b93adf436a1951,0xdf32f3bca75c7c5a62d3,0xb939b55aaa1f97d6ea06,0x69db1119abf86af93692,0xf7ef5c0000cec6316022,0xf7f7001ffffbffffffff,0xfffff83efffbfefffffd,0xffffffc3cd7ffff7f7fd,0xffbffffe2d3fffffffff,0xffefffdfb1e9fbffdfdf,0xfffbfffffe930dfefffe,0xfffffffffff4b57ffbff,0xffffffefffefe69fffff,0xff9fffffffff7e3cdfff,0xffffdffffdfffffa24ff,0x9ffff7f7ffffffbfd307,0xb5fffffffbfff7f7fea7,0xb17fff9dbffffffffff5,0xfda9ffefffdffff7fffd,0xe3c00000000000000,0x72a0000000000000,0x395000000000000,0x1ca80000000000,0xe54000000000,0x72a00000000,0x3950000000,0x1ca800000,0xe540000,0x72a000,0x39500],#[0x40000000000000001ca8,0x2a0000000000000000e5,0x39500000000000000007,0xfdca8000000000000000,0x75200040bfffffbff7ff,0x1114068022e882418a86,0x5d62204a5c41605808a2,0x99c1e382e848e820060a,0xd22993d21c418a1080e4,0xb2147204110bcd8e2b0,0x181402165b8a768f5301,0x625aac299805f2d1724,0x464d9c020c835a2500,0x162648bdb0982f1d60f4,0x5c943b875b430640ff19,0x42006d58a1b0219108df,0x9a00287b429f26b5c84e,0x16808629586ea3004352,0xe8bf873650e3f08880f7,0x7fa66fdffffffffe8924,0xffff399ffffefe7fffff,0xdffbfa07efffffffbfff,0xffffff922fdfff6fffe6,0xfffffdfe9f77ffff69f7,0xefffffffd56cffffffbf,0xff7ffff7ffaf3ffedfbe,0xfffffdfffff996fffddf,0xfefffddfffffeda7fffd,0xffffeffffffffb74dff6,0xffbfffbffffffefbe1ff,0x1fefffcfffffffefe0ff,0x2fffffdfd7fbfd5fff17],#[0xcd00000fffffff7ffff9,0x8a859e15a6f369cc63bb,0xe027b357855f382c4fb1,0x647009aa67f166650d25,0x74da87e7c7913240988d,0xf0c64048e8cc04749c3c,0x81046a822a3a4831afe6,0x9d4f02398902282a8879,0x900f978a0e5d78d9456a,0xe04a83982de19638e150,0x6e5e16e634012a4f4989,0x96510ba414430e4730d7,0x511020d478e9cc1a266a,0x4927841b128a8e031c22,0xc98e81d107882348167b,0x9313a81272a82a9286ca,0x36d18bc40e189ae619,0x85ae91169561d484c10a,0x223108b23b10c0a358e7,0x4636045588a5e501927e,0xd2200bb78eec28e8d488,0xb0e4de103c3969100ec,0xbf0200384c3e00b3c44f,0x76400ccf82911a225a00,0x2431989e56e167117815,0xcda91830de1450425882,0xee8ac71ce16e83ce10da,0x10d2e3b1115e21212c2e,0x2c3ce3535da33b8e0a4b,0x8d8ae68bd24232a065bb,0x989da3994ec3134c8158,0x44382dee5be938a4960a],#[0x5419a3a3181bd02618f4,0x618ef8e18aa222419688,0xc8a082dfaf250d93bc44,0x8870ac490865928a742e,0xecc4c42ea4234b6e83d6,0x40190cc593162a4298,0xe45cc6d66a3acf862b98,0x91ebbe64839348526aa5,0x1c9120ee1b0705650afa,0xb33c4269bf3640029a64,0x98a637b10f64de91fc48,0x852d6112fa2e809185bb,0x193accaf031a1556f150,0xc46955868c8eda8930f,0x79f152e29296a4fde0b8,0x39b1125a993b222692b0,0xe0950ae99388579aacc4,0x40722aba2f71e29118f7,0xd7cfc4223a3579c94a04,0xb454aa6e6b4816aee72b,0xc2b0918825511c2271a9,0x7e249aa2010b0a350af,0xa098c4d2a8e8e3251475,0xca6b4385b0662a03d042,0x92f880910847bd9024ef,0x57e3931bf427e0968405,0x305a788c09398f08d081,0x6402132c56b8f347a392,0x3e1333e37e9b84f57285,0xb5928c6a72cd24dd0e3e,0x192ee64cce2682eb82a5,0x15fa426893683d909e86],#[0x63e56418845c291c842a,0xd8e919124e0236010221,0xc50fbb2ef75121a5e21a,0x6e69c5256b0d3a41590b,0x2b3748d4613ad0804ed4,0x5388c56f8aba585887a6,0x4076ca68c7ab7b0c7c45,0x3e8e622e6249338facd4,0x6228e454a3799a7cc691,0xe8ec95ce4fda52eeb8c4,0xf190c08f6d21aa7234c9,0x9835ac4d7963c3259222,0xe8b2c20195ba43a17625,0x91123b188b287e224a36,0x3ce72e0da67309f5c94e,0xbc4220d14a2e39bed901,0x542a2fc4dcbf0e34d99,0xaf808122ae133841d9a9,0xea10d04e83b56a5f114c,0xa966ec0c28265629440e,0x1eeee141bbc6bbb2e098,0xc02270132a80409fc590,0x7a451941447b8a4c502a,0x27a793b6ae5107048e11,0x2749234e341c2c21b382,0x1e174b35491486660bc0,0xaa9fc87f0a2236413425,0x8aee393968e2fb08c842,0xce453990824ef0e802e6,0x6c62d8b5eb0b93aab458,0x51dbaca79795f42dc3c,0x23388be7a59232edba64],#[0x6926cc450188a524187a,0x73186bd88b2a38e0dbe5,0x21c047826648f4bea11a,0xc38888b8165b192825b8,0x3042490d64899c785cd0,0x839ac94c8df98d648788,0xb141f8a3ad264c37a1ae,0x26be1a6258a351181536,0x28c62e179486869bc0c3,0x99e8a4710fef3b3880c3,0xace5850f664da8e40496,0xbc4193cbead28c80a2d4,0xc659f3af8ea1f66790b,0x5251d0c44693c642da41,0x42388b0]]
def g243D8 := limbs80 #[#[0x8c21050130440400c010,0xffeefbfbdbbb7afd0240,0x414b10958c92c4ca621f,0x4a6266b0939845cc2426,0x2c65b5066b0885904cc6,0x80f2807a303ba1ac58da,0x1c58e22cad54358b2be4,0xd101c58cf28091648c98,0x6279b0a4d8922c893633,0x871640c983458662c8d1,0xe6c471639ca03459062c,0x501e2c4136448b0c6140,0x10c58c26c87a4038b1be,0x28b0b4d8562c47b5038b,0x16478b13458466c6b161,0x843c523e31ac585f4809,0x13e841f430fa08f485ba,0xf90d7aa8fd546ea81f59,0xb1af509bac47d203eb21,0x14ea027d857c647e643f,0xbe547f211fd093aa47d4,0xe84de644eb0af5057a86,0x93ac6bd430ea01f5083,0x1f508fe84fd437f901f9,0xf2a37d00fa429d433f29,0x415eb127d0dbe82ff503,0x43d411e211f5093cc6be,0xfa86df437fa19f1857e8,0x9857e809d427fa11f505,0x1274c8f8849f414fa0b7,0xb0007988fa82df214f3,0xa84403982d8230190120],#[0x8587f07486a86085604,0xcd0c20b60aa8a209a091,0x29081000f90f00e48d90,0x14793e93392b92411a91,0x9a98c98397916b15f955,0xa9cf1c61be1b49ab9a19,0xa1620a9ff9f79ef9e31d,0x5da54a4e240a37230a24,0x6aa9a9b28e280a70269a,0xafa2e8ad7acdac62be2b,0x4ab3b33232231730d304,0x5b99387377b6835db54b,0x3fc3ed3e0bd6bc43b2ba,0x56c4743d42fc25c17409,0x5caac9e492c81c74463c,0xcfecefce44d5ccb4bfcb,0x59d4f543d32d29519d11,0xf5b1da1d97588d79569d,0x6045f4deaddedd2dcadb,0x4044929144002182c908,0x43003948704b818a0e14,0x830499102d1950a4c30d,0x892dc492040a90212764,0x10944095c9247f4306b8,0x10ee2492e2492e224b67,0x7046f3026e20441026f1,0x8c0bbc08885ce095980b,0xc7290947b0225f0092bf,0x9810f7048cc08202b840,0x16fe82466044c08fd011,0xd41261f02189d7045748,0x115c206b44928f06022d],#[0x10f8231384328107a88,0xe013710223840cd606fd,0xbcc246b036703dc60223,0xe7a4112fe5284c79a094,0x815406bf40510e303280,0xaff90084ea033fe02474,0x9e300229e4c44c792c09,0x56808f207688ecb2e26,0x74cfc08a0cf3f02276f8,0x7e0123fc022f011b0c0e,0x734202330c0c781ee44f,0xc6050d940723819fe013,0x5e10dc714db8cf227bca,0xe12010a4efc2251e2122,0x980952f815b36591e1b7,0x68139e4c44d787b9131f,0xc42445b605bfb2513598,0x1fc894ff71013bfc020f,0x10293fa644b4c574e29a,0x892ece04ad9f018fc2d,0x457da02aebc067f804bf,0xad7a92046591c10bf000,0x5b2c26287804bc80da38,0x28ebc073df9050a1bc82,0xde563028bf2e20287da0,0x7da02903dc89e935e713,0x75e031fb30253df8ac27,0xe010ff0090ed8099c015,0x7f80495cdc40a1f]]
def g243H8 := limbs80 #[#[0x540846844155882110a,0xaa115a42122101944219,0x6684092519a090081028,0x854a6059502250a25502,0x2850401000912210244,0x18914458a426614aa419,0x50a111205414402a0508,0x29406402021802945144,0x96081882445011244a68,0x80824126060a61801101,0x20620848988060a0108a,0x2289840a50064a212486,0x448a2840120882110a10,0x8906480051044402205,0x15a182549084602294,0x480904a9805525090288,0x5a12a98116200986100,0x4142868aa0045950450,0x8404606262096622801,0x602810140528501605a8,0x41622482144911885848,0xa6569048940502156104,0x480905a0509922551458,0x5012612120a509416a0,0x24028460842890295488,0x224059a02a5802a80858,0x50810452544086208985,0x404960225a0812025041,0x920a1a04618009099502,0x28011049141841045100,0x8661a48a0890060516a5,0x6458940095aa9090226a],#[0x90a04a90a66510400109,0x6a501102866058862a40,0x2802a0202025a406aa41,0x88190248a80248808656,0xa1461980698a01680889,0x96490202044200160084,0xaa601a5120645489501a,0x88a001291164858a204,0x1829894aa052206a9201,0x80524259191020400492,0x9a860219084898806009,0x1492640808400821969,0xedb5a0a48a546114a984,0x22d089c8d8f2209a2f20,0xa706298e68e00d1ace8c,0x131aa7ee2c7050760d07,0x41ec39605d2146da3500,0x1d81513020850472983e,0x4830632592ebf1e14c10,0x2b0fe000ad6274f21f3e,0x404748ce431165287711,0x24110b5c342e40c562bc,0x15d8084124914f41b0f1,0xd3531dd83245cca3514e,0xc18ec16f576034548ca3,0x2478aa8833734413815d,0x243ab661250414235938,0xd9500c8d100a41b3fa0,0x50c0eab9198d06262bd2,0x9282082b6f00c0024838,0x6a0a3f20948a2cc8ab19,0x98c9d1448a40d36cd48a],#[0x5135255961a299c75028,0xb244a5460503034842f2,0xa1141b082202472464e8,0x189ee9d6fc6ed0de0e87,0x25d5d86dbeb4bcdb1600,0x425d92b9b73f6916c5d8,0xb41c18e12b355b45a62b,0xec111e46dd6b564a2854,0x2d548ad00179f35b7e7f,0x70f90868bad16f4f8071,0x8d8437a3c497597c68c5,0x2138feb5220b8a40f987,0xfa48571e512ecb9236e9,0xfae6ae86a90a846bf796,0x4a2abfff9a765d34e653,0x714dc67ad996232ee708,0x21d91bdfb764119bce09,0x20fb0e5dac3ec4bcee7d,0x3e3fbf618dca9870e800,0x469366d8d527da4def44,0xd35ecb0ee6f5f985ec4a,0x9aa43df7de41f1f3806d,0x74856fb63713c3860b69,0xcff7ad7ca9ef9bd572bb,0xafdad97ecc973afa0c78,0x35db7bac8fd8b50a37db,0xa9beb6af6942bf6c9dad,0x6f97210ba372cfbad327,0xcd420acd2ddcde11ba7a,0x5d6d45d1fff6eeda73c3,0xd5ff15a8d93bc000afad,0x2a0b5403ee32fc02a7d5],#[0xf105d58c075bb0dc28de,0x8e35e3f3f95fe9121c2,0xb66fd1f37dfa92cdad12,0xc6fdce7d1416efa38f70,0x7e41286a759a2141556f,0xf89246fe0eb9f875a4fd,0x7e4e94cfdb7734999f48,0x4fad90b91ce1af4d9e67,0xfe1127e661a3f08cfc9f,0x3780000000f7,0x1d300000000,0xe98000000,0x74c00000,0x3a60000,0x1d3000,0xe980,0x6000000000000000074c,0xd300000000000000003a,0xe980000000000000001,0x74c000000000000000,0x3a600000000000000,0x1d30000000000000,0xe9800000000000,0xffffffe74c0000000000,0xdfffffff001fffdffbfb,0xfffffffff83dff7effff,0xffffffdfffc3d7ffffff,0xfffffffffffe2ebfffff,0x1041d2405ffff1f3ffff,0xfa806800200a793900a,0x4288214030090344aa88,0xf1e4a52211065011059d],#[0x8bc0625104405114a82e,0x4ce83500b8160894c881,0x8a6c10b96f10ac044f23,0xacc39704492e401303c5,0x62531e1a04d090401899,0xea8220fb40ba830ea788,0x273fc00841b020255485,0x698113c244db184109c5,0x22424137a240482028ec,0xaaf800163412b0c48106,0x620490efd0189a962132,0xbd0c4757e9ddf502fbff,0x93ffed1caf02ff2a2fa2,0x69efbfddd37df3ed649d,0x147afbaf7b75efffebc6,0x51fdebeceabffdfaf664,0x5c178b44ffecbbfe566b,0x70eb1d7fb3bf7efdf4cf,0x864613022502c8855fb8,0x67289bce7812942a3886,0x8a23a0e24ac8643b2a9e,0xb31bae6ab83ac07aad82,0xab3e4e0931052139f668,0x390f052b726c2b874f52,0x3455c12da4622a8c3611,0x4cdc3b3c2b33320ecbb9,0x6e2137039191084f04af,0x2495e43749b0c8760aee,0xa95e24c78b582ebccf33,0x3d64f740bac49f306855,0x72a6794b475eb914f00,0xa223aa22e6f957c2af1],#[0x2d093a4eda2bd8b543b,0x6ba89ae2b412924d50ab,0xad2404974906e217a290,0x4ba58d7a1d111891d42e,0x885a35b458082c90802f,0x3ceca6cc0a2cb9b5246a,0x5cc979b02f8792d268ca,0x8816a0ec67cb824ad9b2,0x4483b3a4361ad6440baa,0x2945a4df143e2e59c72,0x419f8418b866e3f9cca5,0x1ac6b53b978ae01d76ae,0x5546c9b37451590f654d,0xde304114e6b9ba303234,0x4b440d3498812e4a110a,0xed4a432639bb0e2483aa,0x97b6225613e0cf0192f0,0xb24204288b9c4530c444,0x131a4c4a0d8eb4be068f,0x388302361a56792f8446,0x7a401b99eb141338f071,0x253f0a9af363cbab6938,0x42da3aa54432b8459bd9,0x802b56e234da6516241a,0x2bd1a2d812a6c3d3bd45,0x9ba2b26a044d4d8d4494,0xa94e96b1406de251122e,0x3d32132e468e8d704c53,0xa4ae1aa4f0ba3322ca3a,0x2658dac2e90e1442e220,0xc7bc0ac0215bcd57957a,0xb39d22c29550e4b8e222],#[0xb4c8f5d0d6895510e023,0x600c75ac74e669266f25,0x1e6868cad33f235ce883,0x64ca11484d092e6390bd,0xcc68b844f79948f3b2af,0x2d10e24b0ab94f45a8a0,0x28d4ca6da5a0362942c7,0x393021e0da84a18998c0,0xe302ca908e8d112be8ad,0x8aefc39702ac952c347b,0x24c12208540b0b4e2e9b,0x9503a832b5158ecea0a5,0x2eada0d35cbfcd630a78,0x92a0c29c1378e21b5245,0xa3664703ae2cadb2b24d,0xa422c6b9c27298d54373,0x16356a3052be08b665b8,0x220e111e454959433208,0x331ab0e51f12de55512b,0x899a4e061c3ce2d3124,0x333124278c988b29290e,0x8c526de960e4b70d2441,0xaa8cd291ae4242b88ee7,0xe2a2b38bd0c4129a5781,0x83800b8275111006d68b,0x8d412a4e058de8f7ead8,0x1d9d00e6308c2958cc96,0xe95d22b3bd60aec0d464,0x38be274b852f29bbda41,0x63f277125c78a0dbe40c,0x6ca5b9c78f390d091149,0x2a40b62ae989ce2efa8],#[0x376928e53ba9c4f65888,0x69a8d695d3da030f2461,0x4b2525289a0ce7c8d365,0x9484f33bfaeff0e2e34,0x8a0aecc56ec62ab066e3,0xb2e6423304168df0f769,0x68fe0b4e33d14524d290,0xe53cb1c4dea96020092d,0xc92cce62c2b4ccb4913a,0xe25d8e7f25343440e0a6,0x8d3097cb456914b91246,0x8e4202bccc2debd946bc,0x2852732dd1193e285869,0x622d336a6213a9c46dad,0x553ba8a6c616442bc9b1,0x3dab384af2bee6901e02,0x5ad5274b99984140b7e2,0x12082d0234c4ea2e30f0,0x200566ad0a2ab9236f3f,0x86a77197492909324121,0x832e0bc72359cd22670b,0x6a03192f548cbe549bcf,0x2fbd5632514f06dba38e,0x14d4e57f12ca41592047,0x8b9a2701172357a440ac,0xcc262515644ba8c5e522,0xac6652334f3aaab44dd3,0x6ae7ba1e406927860899,0x55639a254faa045489c7,0x7c95f2327135c86d947a,0x71b1e7879196e428cd63,0x1038e2a95ee61b3c84e4],#[0x58ab07b9d4b0b93ac218,0xbe28329a4e993afc6cf3,0xae58aa344ce9d20b400a,0x611ba0e3790bb46f88e1,0x57abaa9813a56acc1840,0x61f10e8f]]
def g243D9 := limbs80 #[#[0x204609806108220087f,0x42ba31a1189006812028,0x830b0a20610204c43bcb,0xc00400025800e8004a2,0x24006000480024801,0x3]]
def g243H9 := limbs80 #[#[0x16221085500015022081,0x810098512180009591,0x1849968680890082a108,0x24106060a11808222621,0x6824642a2426542a5410,0x91661128204689599686,0x256581020a1968a54804,0x64400650428900918880,0x909494a02820a1151240,0x39cd432425120225a895,0x5517f08502d047270c03,0x3cfb8bb942e0701925a0,0x5e1109409a7dd1188066,0x109bbb91d6617086296,0x40010c00115005201646,0x8903802001181d0b0018,0x4010e080c080d088000,0x90802800080080b000,0x46c001c5e0384894406,0xefefe5eed8f401000044,0xebfbfb6bf5f007bee6ff,0xaffefef7f7ffa33f87ff,0x8effef58fbfdc98cdb7f,0x80003feffbf7decda753,0xf0000000000000000064,0xef6ff7ff4bff7db6,0xbc00cc00000000000000,0x9fff719cb6fb7fc63db6,0x6d5befe5adad9bd1aaf3,0xbddb6b5750daf9bf70e6,0xd914a1aa34ac801ff9df,0x1a011a921bbc3a1ab29b],#[0x362a89b93b009109c3c0,0xbab31ae9331af306221b,0x8848b823d3a208d8acaa,0xbd8ad8be88b4359399b2,0xa32488a1268811153a9a,0x13fb23bb24b71b99083b,0x380928b8aa2936baa095,0x8ad10b89b1383a511a2,0x9ab4b2315109391bbc9c,0x2438589ec241a713a082,0xf9b31b18af89812a0a93,0x918088a3a2aebb723689,0x938bf0bb31a42c0a79a0,0x33593394292f92f3be8,0x12bbc2131a400b51b394,0x229aaa2a2be116b9eaa1,0x632c13d89caaf0a52429,0x3bbb831ab93d0a3cbc93,0xb9b8b926128908b8cca5,0x438d0838971432a70b0a,0x1be087b8fb9d23fc87bb,0xa9c2494108c9b11a2894,0x2387923cbc1baa2108e8,0x8693510d895ac]]
def g243D10 (j : Nat) := if j=0 then 0x3f else 0
def g243H10 := limbs80 #[#[0x85c022a0a40080201480,0xa486152080,0x8511a944c006460030e0,0x9e8814ca241000098011,0x525430680008dbae4a1,0x1e2bb4623a46e2c4a000,0x36e583e93b82480064e0,0x4005a1412090c523c62b,0x28a11ac09880d2940000,0x1836640030ab2801a,0xaa450080000001828000,0xce0032b2]]
def g243L : Nat → Packing
  | 5 => (61,5,5,2359336,102,528516,1032,g243D5)
  | 6 => (966,4,5,5767489,121,23601387,1067,g243D6)
  | 7 => (804,3,5,2162793,103,124002574,1085,g243D7)
  | 8 => (135,2,5,524298,52,12,1058,g243D8)
  | 9 => (10,1,5,65537,0,8,1034,g243D9)
  | 10 => (1,0,5,0,0,0,0,g243D10)
  | _ => emptyPacking
def g243I : Nat → Nat → Option (Nat × Nat)
  | 6 => indexWave 46 2 8 846 6 4 [(414,61),(630,51)] #[(0,0),(51,3),(3,0),(109,0)] g243H6
  | 7 => indexWave 656 4 11 12879 10 4 [(5904,966),(8229,1051),(10554,689)] #[(0,0),(689,2),(627,49),(1113,111),(2,0),(736,0)] g243H7
  | 8 => indexWave 597 4 11 11673 10 4 [(5373,804),(7473,1324),(9573,803)] #[(0,0),(803,7),(667,337),(1460,473),(7,0),(1133,0)] g243H8
  | 9 => indexWave 125 3 9 2439 8 4 [(1125,303),(1563,135),(2001,156)] #[(0,0),(156,12),(84,63),(207,0),(12,0)] g243H9
  | 10 => lookupShort 15 83 7 10 4 4 g243H10
  | _ => fun _ => none
def g243 : Forest := ⟨243,10,fun i => g243Y[i]?.getD (0,0),g243C,g243A,g243L,g243I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243B5 : CutRow g243 5 0 61 := by
  have g243P5_0 : CutRow g243 5 0 3 := by
    apply checkedCells 6 0
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
  have g243P5_3 : CutRow g243 5 3 48 := by
    apply polarBlock (data:=fun j => g243Mark (j+0)) rfl
    decide +kernel
  have g243P5_51 : CutRow g243 5 51 10 := by
    apply polarBlock (data:=fun j => g243Mark (j+48)) rfl
    decide +kernel
  exact (@joinRow g243 5 0 3 58 g243P5_0 (@joinRow g243 5 3 48 10 g243P5_3 g243P5_51))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243B6 : CutRow g243 6 0 966 := by
  have g243P6_0 : CutRow g243 6 0 2 := by
    apply checkedCells 5 0
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
  have g243P6_2 : CutRow g243 6 2 47 := by
    apply checkedCells 6 3
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
  have g243P6_49 : CutRow g243 6 49 48 := by
    apply checkedCells 7 3
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
  have g243P6_97 : CutRow g243 6 97 14 := by
    apply checkedCells 7 1
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
  have g243P6_111 : CutRow g243 6 111 48 := by
    apply polarBlock (data:=fun j => g243Mark (j+58)) rfl
    decide +kernel
  have g243P6_159 : CutRow g243 6 159 48 := by
    apply polarBlock (data:=fun j => g243Mark (j+106)) rfl
    decide +kernel
  have g243P6_207 : CutRow g243 6 207 48 := by
    apply polarBlock (data:=fun j => g243Mark (j+154)) rfl
    decide +kernel
  have g243P6_255 : CutRow g243 6 255 48 := by
    apply polarBlock (data:=fun j => g243Mark (j+202)) rfl
    decide +kernel
  have g243P6_303 : CutRow g243 6 303 48 := by
    apply polarBlock (data:=fun j => g243Mark (j+250)) rfl
    decide +kernel
  have g243P6_351 : CutRow g243 6 351 48 := by
    apply polarBlock (data:=fun j => g243Mark (j+298)) rfl
    decide +kernel
  have g243P6_399 : CutRow g243 6 399 48 := by
    apply polarBlock (data:=fun j => g243Mark (j+346)) rfl
    decide +kernel
  have g243P6_447 : CutRow g243 6 447 48 := by
    apply polarBlock (data:=fun j => g243Mark (j+394)) rfl
    decide +kernel
  have g243P6_495 : CutRow g243 6 495 48 := by
    apply polarBlock (data:=fun j => g243Mark (j+442)) rfl
    decide +kernel
  have g243P6_543 : CutRow g243 6 543 48 := by
    apply polarBlock (data:=fun j => g243Mark (j+490)) rfl
    decide +kernel
  have g243P6_591 : CutRow g243 6 591 48 := by
    apply polarBlock (data:=fun j => g243Mark (j+538)) rfl
    decide +kernel
  have g243P6_639 : CutRow g243 6 639 48 := by
    apply polarBlock (data:=fun j => g243Mark (j+586)) rfl
    decide +kernel
  have g243P6_687 : CutRow g243 6 687 48 := by
    apply polarBlock (data:=fun j => g243Mark (j+634)) rfl
    decide +kernel
  have g243P6_735 : CutRow g243 6 735 48 := by
    apply polarBlock (data:=fun j => g243Mark (j+682)) rfl
    decide +kernel
  have g243P6_783 : CutRow g243 6 783 48 := by
    apply polarBlock (data:=fun j => g243Mark (j+730)) rfl
    decide +kernel
  have g243P6_831 : CutRow g243 6 831 48 := by
    apply polarBlock (data:=fun j => g243Mark (j+778)) rfl
    decide +kernel
  have g243P6_879 : CutRow g243 6 879 48 := by
    apply polarBlock (data:=fun j => g243Mark (j+826)) rfl
    decide +kernel
  have g243P6_927 : CutRow g243 6 927 39 := by
    apply polarBlock (data:=fun j => g243Mark (j+874)) rfl
    decide +kernel
  exact (@joinRow g243 6 0 447 519 (@joinRow g243 6 0 159 288 (@joinRow g243 6 0 49 110 (@joinRow g243 6 0 2 47 g243P6_0 g243P6_2) (@joinRow g243 6 49 48 62 g243P6_49 (@joinRow g243 6 97 14 48 g243P6_97 g243P6_111))) (@joinRow g243 6 159 144 144 (@joinRow g243 6 159 48 96 g243P6_159 (@joinRow g243 6 207 48 48 g243P6_207 g243P6_255)) (@joinRow g243 6 303 48 96 g243P6_303 (@joinRow g243 6 351 48 48 g243P6_351 g243P6_399)))) (@joinRow g243 6 447 240 279 (@joinRow g243 6 447 96 144 (@joinRow g243 6 447 48 48 g243P6_447 g243P6_495) (@joinRow g243 6 543 48 96 g243P6_543 (@joinRow g243 6 591 48 48 g243P6_591 g243P6_639))) (@joinRow g243 6 687 144 135 (@joinRow g243 6 687 48 96 g243P6_687 (@joinRow g243 6 735 48 48 g243P6_735 g243P6_783)) (@joinRow g243 6 831 48 87 g243P6_831 (@joinRow g243 6 879 48 39 g243P6_879 g243P6_927)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243B7 : CutRow g243 7 0 804 := by
  have g243P7_0 : CutRow g243 7 0 7 := by
    apply checkedCells 6 0
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
  have g243P7_7 : CutRow g243 7 7 48 := by
    apply checkedCells 7 3
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
  have g243P7_55 : CutRow g243 7 55 48 := by
    apply checkedCells 7 3
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
  have g243P7_103 : CutRow g243 7 103 48 := by
    apply checkedCells 7 3
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
  have g243P7_151 : CutRow g243 7 151 48 := by
    apply checkedCells 7 3
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
  have g243P7_199 : CutRow g243 7 199 48 := by
    apply checkedCells 7 3
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
  have g243P7_247 : CutRow g243 7 247 48 := by
    apply checkedCells 7 3
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
  have g243P7_295 : CutRow g243 7 295 42 := by
    apply checkedCells 7 3
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
  have g243P7_337 : CutRow g243 7 337 48 := by
    apply checkedCells 8 3
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
  have g243P7_385 : CutRow g243 7 385 48 := by
    apply checkedCells 8 3
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
  have g243P7_433 : CutRow g243 7 433 40 := by
    apply checkedCells 8 3
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
  have g243P7_473 : CutRow g243 7 473 48 := by
    apply polarBlock (data:=fun j => g243Mark (j+913)) rfl
    decide +kernel
  have g243P7_521 : CutRow g243 7 521 48 := by
    apply polarBlock (data:=fun j => g243Mark (j+961)) rfl
    decide +kernel
  have g243P7_569 : CutRow g243 7 569 48 := by
    apply polarBlock (data:=fun j => g243Mark (j+1009)) rfl
    decide +kernel
  have g243P7_617 : CutRow g243 7 617 48 := by
    apply polarBlock (data:=fun j => g243Mark (j+1057)) rfl
    decide +kernel
  have g243P7_665 : CutRow g243 7 665 48 := by
    apply polarBlock (data:=fun j => g243Mark (j+1105)) rfl
    decide +kernel
  have g243P7_713 : CutRow g243 7 713 48 := by
    apply polarBlock (data:=fun j => g243Mark (j+1153)) rfl
    decide +kernel
  have g243P7_761 : CutRow g243 7 761 43 := by
    apply polarBlock (data:=fun j => g243Mark (j+1201)) rfl
    decide +kernel
  exact (@joinRow g243 7 0 385 419 (@joinRow g243 7 0 151 234 (@joinRow g243 7 0 55 96 (@joinRow g243 7 0 7 48 g243P7_0 g243P7_7) (@joinRow g243 7 55 48 48 g243P7_55 g243P7_103)) (@joinRow g243 7 151 96 138 (@joinRow g243 7 151 48 48 g243P7_151 g243P7_199) (@joinRow g243 7 247 48 90 g243P7_247 (@joinRow g243 7 295 42 48 g243P7_295 g243P7_337)))) (@joinRow g243 7 385 184 235 (@joinRow g243 7 385 88 96 (@joinRow g243 7 385 48 40 g243P7_385 g243P7_433) (@joinRow g243 7 473 48 48 g243P7_473 g243P7_521)) (@joinRow g243 7 569 96 139 (@joinRow g243 7 569 48 48 g243P7_569 g243P7_617) (@joinRow g243 7 665 48 91 g243P7_665 (@joinRow g243 7 713 48 43 g243P7_713 g243P7_761)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243B8 : CutRow g243 8 0 135 := by
  have g243P8_0 : CutRow g243 8 0 12 := by
    apply checkedCells 6 1
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
  have g243P8_12 : CutRow g243 8 12 48 := by
    apply checkedCells 7 3
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
  have g243P8_60 : CutRow g243 8 60 3 := by
    apply checkedCells 7 0
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
  have g243P8_63 : CutRow g243 8 63 48 := by
    apply checkedCells 8 3
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
  have g243P8_111 : CutRow g243 8 111 24 := by
    apply checkedCells 8 2
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
  exact (@joinRow g243 8 0 60 75 (@joinRow g243 8 0 12 48 g243P8_0 g243P8_12) (@joinRow g243 8 60 3 72 g243P8_60 (@joinRow g243 8 63 48 24 g243P8_63 g243P8_111)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243B9 : CutRow g243 9 0 10 := by
  have g243P9_0 : CutRow g243 9 0 10 := by
    apply checkedCells 7 1
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
  exact g243P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243B10 : CutRow g243 10 0 1 := by
  have g243P10_0 : CutRow g243 10 0 1 := by
    apply checkedCells 6 0
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
  exact g243P10_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243T : mixedTables g243 10 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty g243 0 0
  · exact mixedEmpty g243 1 0
  · exact mixedEmpty g243 2 0
  · exact mixedEmpty g243 3 0
  · exact mixedEmpty g243 4 0
  · exact g243B5
  · exact g243B6
  · exact g243B7
  · exact g243B8
  · exact g243B9
  · exact g243B10
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243G : graphValid g243 (boundsBefore K235) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low243 : Lower true (varsX 243) (graphGoal 243) 11 := mixedLower (g:=g243) (i:=0) (hints:=65605) (before_sound K235 V235) g243G g243T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K243 := extendKnown K235 11 [(243,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V243 : Known true K243 := extend_ok (m:=243) V235 low243 (by decide +kernel)
def g250MarkBits := limbs80 #[#[0xc6140000103082040000,0x2c500004000a2482081,0x14d04104104100100130,0x522511900413c1381001,0x10413c00414c00400400,0x5719604154150100100,0x5a640601041041001055,0xd04000070004105b0016,0x15d5003de05405904105,0x604704c0460002c03c1,0xd04d0416e051f1810000,0x8400400413c004100105,0x413c101400600091b8e2,0x10560140140005266a50,0x3000510009c100004004,0x40a40040040013040068,0x10400]]
def g250Labels : Array Nat := #[0x1080182c07088,0x1020412891428,0x3008051083450,0x14080c1403442,0x60a004220a0b0,0x1482182c0708a,0x10008180e16088,0x60a020108a0b0,0x4008411094428,0x420201808422,0x8002412898442,0x80200c0e0b060,0x2080052283490,0x2040503816050,0x14080c160344a,0x60a00522834b0,0x1020010891428,0x4040011084460,0x440501804442,0x40400c1607060,0x4008412294428,0x104a00c0e034a2,0x4040051285460,0x148218240708a,0x4040411084460,0x410502c14412,0x4000412294428,0x3030412891438,0x400020108c022,0x4200c0e03422,0x104a02018084a2,0x60a020300a0b0,0x300824128b01a,0x440101804442,0x410402c14412,0x104a00c0e024a2,0x8020052289460,0x140824160941a,0x3030402891038,0x410201408412,0x2040011082450,0x80800522894c0]
def g250Mark (j : Nat) := (g250Labels[packedAt g250MarkBits (6*j) 6]?.getD 0) <<< 8
def g250Y : Array (Bits × Bits) := #[(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffff07ffffc6710,0x3f03ffa3cc199d])),(BitVec.ofNat 152 (word80 [0xa40a40210101002114,0x514514514528a1cc0884]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xf000ffff83ff819000,0xfc0000fc00000efeee])),(BitVec.ofNat 152 (word80 [0xc12c11400842090002,0xcb2cb2cb2ce58006faae]))),((BitVec.ofNat 152 (word80 [0xffff000003ffff0c10,0x3f000fc0001f8cf1670d])),(BitVec.ofNat 152 (word80 [0x3005821014030401,0x86186186184304112718]))),((BitVec.ofNat 152 (word80 [0xfffffffffc000032c0,0x3f000ffe04f0187f0])),(BitVec.ofNat 152 (word80 [0x84086000218101249,0x2492492492124e010550]))),((BitVec.ofNat 152 (word80 [0x249ef,0xc003ffff00007001f803])),(BitVec.ofNat 152 (word80 [0x180180420602048a2,0x820820820840000d003]))),((BitVec.ofNat 152 (word80 [0x1902f,0xfffc000000007ffe0002])),(BitVec.ofNat 152 (word80 [0xe00e008438040900c,0x30c30c30c3187ba80000]))),(0x0,0x0)]
def g250C : List ColumnInfo := [(8,0,242,0,7),(32,0,218,0,7),(64,0,186,0,7),(128,0,122,0,7),(0,8,82,160,6),(2,0,248,0,6),(16,0,234,0,6),(10,0,240,0,5),(24,0,226,0,5),(32,8,82,128,5),(34,0,216,0,5),(128,8,82,32,5),(136,0,114,0,5),(144,0,106,0,5),(42,0,208,0,4),(48,0,202,0,4),(66,0,184,0,4),(72,0,178,0,4),(80,0,170,0,4),(96,0,154,0,4),(130,0,120,0,4),(152,0,98,0,4),(160,0,82,0,4),(160,8,82,0,4),(168,0,82,0,4),(192,0,58,0,4)]
def g250A : List (List Nat) := [[],[65,117]]
def g250D5 := limbs80 #[#[0x54120d91414814250120,0x501435053050d404c132,0xbaae6ab5545055050d50,0xf4bccf1baceaba6e978d,0xc18260c36c6196314a9a,0x261c19060cbca05d5025,0x51628ab2b1e098b04d56,0x2c00f62d3106948342a7,0x6d4d2d0cecccac8c6c4c,0x6417003e2e0dedcdad8d]]
def g250D6 := limbs80 #[#[0x50120509105902050420,0x58d2054d205412050520,0xd8d20941209012059120,0x50530501304c930d9120,0x59530591305513050d30,0x54d405414050d4050940,0xd8d40d89409414059540,0xd814150d4118141d9540,0xd9543d8943d814359543,0x54d5050d50505504c950,0xd9150d8d50d895055150,0x596105921058a10d8553,0x58a20542205062050220,0x50630502305962059220,0x5923058a305523054e30,0x5964058a405424059630,0x5925058a505865050650,0x9fbf5f6ef6fafcfe7b3b,0xafcddf6f777b7daebf5b,0xd7e7eef6fabcfe6f2f7b,0x3d3b2040eed03f9fafb7,0x1b918b2840d2b8819a86,0xb000ae8b28a18e5ac600,0x4e264152b20082a8943b,0xaa6551b2278aa8e22a9a,0x65a4a98562c8e22a9a6a,0xdaa13adaa6d84bb11c28,0xa13b7ac60c4ba297ec60,0x1ec284d98a9ba42ca454,0x92a8c84b9216ee462eb8,0xc80ceb9197eca272a10d,0xac53b06c284644babac6],#[0x4b91b42a4fc5b82012e6,0xa2a7ec8295b204528030,0xf4284be4aa057acac10a,0x2ca5c5ba133ee09b4990,0x631aa142da64394a1344,0x4b92a6c84e9eb20a12e,0xb1842ee441eb28368e46,0x1512e4715ba087ec459d,0x7ec816a991596ca149b9,0xcad85ba8752850faa085,0x36eb91e16e8b44ba9b7a,0xeb13d72c5004b92b62ca,0xabe16e460aba0d12e8cd,0x6c28458eba8312eaf85b,0x6e25c4baa266e61c6baa,0x89aa12d3eea0c4bb063,0xb919031ee4a0eba8912e,0xa12e62c835f902116e8e,0x4232e4744bab4cc84354,0x12ea84fba053ae8284ba,0xea484ba8bbec8110aa29,0x7faa0b212e82deb28e16,0x4ba2ac2840d8b29012e4,0x10e22e6518a9a262861c,0x12e08c4bb3972c6130a,0xce4790b2b992a65b0a13,0x8d70a18312e6684ba2db,0x9cb2b11ee6a1cb13742a,0xa93c16e8cc5b9133ee00,0xb032e47deb28912e6a50,0x3ee4584ba3a7ac4c0eba,0xe9085b9982ee835eb232],#[0x705baba62642deb20516,0xca14166c6199b19712e6,0x90312e81e3293816e449,0x2ea8229eb136ba861389,0x6e650fb9967eca0c4b92,0x90db8866e42684ba9a2,0x45ba0712e48eeaa313ee,0xba0b76c4945b98872c4c,0x6dfffc5,0x4c000000000000000,0x218004c0000000000000,0x5f12806102603ed8687,0x2e9521e05501e05ee9c,0x49870a1e2744829b40c,0x9480415840c0a451b140,0x6f8071612d8480602320,0x37a1980d361037431388,0x9b22301d64c498133610,0x2df221de228605012c91,0x2b2]]
def g250H6 := limbs80 #[#[0xd0000008642000b0b0,0x0,0xe40000000000000,0xe00000000000000a7000,0x30000000000000000004,0xca00006,0x8c006847004100000,0x943000000cf000,0x10500000000000000260,0x80000004400000000002,0x11000090008,0xe20,0x0,0xa500000000000000ed0]]
def g250D7 := limbs80 #[#[0x54143505404c12044020,0x7af9f942408c22084153,0x5fffefdf7efeddfbfbdb,0x61d3d8601659258c1943,0xa940b4596c564035840d,0x93516439505d1642458c,0x45959363245925360545,0x5384c8d162c918165412,0x3656850cd164a5551d16,0x31164b9504d3647458a5,0x5411162aa900a153ba54,0x3990493637458ad3624a,0x6349506d165aa502a940,0x91640a54293642950413,0x89e9402854d93626a940,0x9506a64174d95136064d,0x2950751654458b5165c,0xd424a9411d434554de95,0x52d534b50ded3279d815,0x552ed543b548ed412b54,0x4b500af612b5086d532b,0x429b589ed634b8c92d62,0xee42bb595ad642b58cad,0x852d606bd90ad612b908,0xb591ed42bb540ad637b5,0x23b5412d432bd8cae52b,0xd626b948ed324b5952d4,0xfee624b50aae626b552a,0x7ffe03ffffffffffffff,0x46180080000000000000,0xee3fadb2d9f732c4d663,0xc02ca7e25b93cb86c037],#[0x4d85002ce7209b550c45,0x16cec9c4c02f29235cd5,0x251fd8500ac50029231d,0x402d265dd58f49c6c02b,0x8cc5802620da958f4a05,0x19930d87002ee8a299d4,0x8299544f0985402aa4a0,0x4c283000839728888060,0x88c241180c31d045891a,0x2121f34aa389822e2332,0x88c294c4880a8b21c699,0xc4da359c23dfe5288323,0x491774ea2dd71fe2613c,0xa22716630d82d9c230e6,0x12ba1443f9e1944fbca1,0x92e8dc443f400993c01,0xe6285e381d11a50d0c3b,0xb1df2e04bd5c0cb2d8ab,0x6df9560518f82495ba5,0xfe241a28749257a120f4,0x5b2c226cba144be91134,0xc24aec0c70d904147884,0x245eb549142eceea5061,0xf10225630c67c124b717,0x48d2ba14479781480e7,0x5c0e227b91af98a16be4,0xfe82d9c23bb012dc612,0x1a32b4c8fc6082b5944,0xe627ac618cfdf611327e,0x45261c24b3fc804c457,0xa8998aa64c33144326fb,0x998c2fe0441f86045930],#[0xecb238cc69923c1964cf,0x1c212de90f98a08b2d98,0x1711175b156318e7a843]]
def g250H7 := limbs80 #[#[0x5aa88860011018511058,0x60596108601004090019,0x51145489aa1509408645,0x95565218002252206500,0x6061814405599025604,0x460000a208286182a22,0x42281428a01161a42a46,0x1f160560aa45092a1208,0x753cd0384024dda4c42,0x742aa8d6155cc024da9c,0x1422f81141945022870c,0x29808028422776842e33,0x80006040003b50800011,0x40026a0081e02100801,0x1365324c56605c614020,0x20440880991081190c00,0xff7fff9eefedfee3900c,0x3ffeff7ffdffffd7c01f,0x39ffefeff7ffffffbf8e,0xaf0003dfdfffdfefff,0xe61ba00000000000000,0x69,0x26a0b8504ec098000400,0x6800a4700110a9108303,0x10060a042404c4116080,0x1d4656575cdd8d400180,0x55dd84a279aa8adfb538,0x2390ecc48f7343a4cc2a,0xc926b7ca0d833f85dae7,0x89cba3d3dc04e369a4b3,0x4ad755f058eb352ed96a,0x190856b20d]]
def g250D8 := limbs80 #[#[0xa4108308510482507ffd,0x3942a8640a818c298620,0x23e1504c0154ea1d41a6,0x20ee96baf54e95429bcb,0xd2ce2800878ac7449847,0x8501446155c10c82468c,0x3bc052f824b3110d3814,0x25798487b083be3b607,0xb5c249339f80a6f0236,0xe7811ec80c7f796041d2,0x17ecc0c1e42c4a0ec419]]
def g250H8 := limbs80 #[#[0x18a25968115800568224,0x15810908002125205006,0x85888212114214a44060,0x25828041025820225186,0xb0d50154958220698280,0xa1a6848267304be6b365,0xc214304b1542290c94c9,0x1f97842818a5b4164d7,0x1b7051c10e634d1a0124,0x69044162cf2befd17432,0x54a80000000000000000,0x754010ba2e5581516a5,0x380000049c0215,0x560000000000,0xfffbe7fdfe5600000000,0x92cbf994498e01fffedf,0xfebfdbed33f41a753481,0xeb18e,0xa397733b2f036341cd06,0x131d8f27d3a9b3ab7bd1,0x8db179c721c9db01952d,0x69d717c1bf9b7f677d87,0x14357719f2b]]
def g250D9 (j : Nat) := if j=0 then 0x1882013f else 0
def g250H9 := limbs80 #[#[0x4217828000016110a80,0x3e78035f1d6712800000,0x4670380334035000076f,0x4e6c0c18065845486457,0x630100004]]
def g250L : Nat → Packing
  | 5 => (18,4,5,720903,67,8,1027,g250D5)
  | 6 => (188,3,5,1966148,87,4985033,1050,g250D6)
  | 7 => (111,2,5,786446,68,20455691,1073,g250D7)
  | 8 => (17,1,5,131073,16,9,1048,g250D8)
  | 9 => (1,0,5,0,0,0,0,g250D9)
  | _ => emptyPacking
def g250I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupShort 6 139 2 8 5 1 g250H6
  | 7 => indexWave 104 3 9 2031 8 1 [(936,242),(1301,91),(1666,249)] #[(0,0),(249,12),(82,21),(258,0),(12,0)] g250H7
  | 8 => indexWave 65 4 8 1449 7 1 [(585,111),(873,152),(1161,61)] #[(0,0),(61,7),(51,68),(162,78),(7,0),(122,0)] g250H8
  | 9 => lookupShort 7 41 5 8 5 1 g250H9
  | _ => fun _ => none
def g250 : Forest := ⟨250,9,fun i => g250Y[i]?.getD (0,0),g250C,g250A,g250L,g250I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g250B5 : CutRow g250 5 0 18 := by
  have g250P5_0 : CutRow g250 5 0 1 := by
    apply checkedCells 6 0
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
  have g250P5_1 : CutRow g250 5 1 17 := by
    apply polarBlock (data:=fun j => g250Mark (j+0)) rfl
    decide +kernel
  exact (@joinRow g250 5 0 1 17 g250P5_0 g250P5_1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g250B6 : CutRow g250 6 0 188 := by
  have g250P6_0 : CutRow g250 6 0 12 := by
    apply checkedCells 6 1
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
  have g250P6_12 : CutRow g250 6 12 9 := by
    apply checkedCells 7 1
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
  have g250P6_21 : CutRow g250 6 21 48 := by
    apply polarBlock (data:=fun j => g250Mark (j+17)) rfl
    decide +kernel
  have g250P6_69 : CutRow g250 6 69 48 := by
    apply polarBlock (data:=fun j => g250Mark (j+65)) rfl
    decide +kernel
  have g250P6_117 : CutRow g250 6 117 48 := by
    apply polarBlock (data:=fun j => g250Mark (j+113)) rfl
    decide +kernel
  have g250P6_165 : CutRow g250 6 165 23 := by
    apply polarBlock (data:=fun j => g250Mark (j+161)) rfl
    decide +kernel
  exact (@joinRow g250 6 0 69 119 (@joinRow g250 6 0 12 57 g250P6_0 (@joinRow g250 6 12 9 48 g250P6_12 g250P6_21)) (@joinRow g250 6 69 48 71 g250P6_69 (@joinRow g250 6 117 48 23 g250P6_117 g250P6_165)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g250B7 : CutRow g250 7 0 111 := by
  have g250P7_0 : CutRow g250 7 0 7 := by
    apply checkedCells 6 0
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
  have g250P7_7 : CutRow g250 7 7 48 := by
    apply checkedCells 7 3
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
  have g250P7_55 : CutRow g250 7 55 13 := by
    apply checkedCells 7 1
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
  have g250P7_68 : CutRow g250 7 68 10 := by
    apply checkedCells 8 1
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
  have g250P7_78 : CutRow g250 7 78 33 := by
    apply polarBlock (data:=fun j => g250Mark (j+184)) rfl
    decide +kernel
  exact (@joinRow g250 7 0 55 56 (@joinRow g250 7 0 7 48 g250P7_0 g250P7_7) (@joinRow g250 7 55 13 43 g250P7_55 (@joinRow g250 7 68 10 33 g250P7_68 g250P7_78)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g250B8 : CutRow g250 8 0 17 := by
  have g250P8_0 : CutRow g250 8 0 2 := by
    apply checkedCells 6 0
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
  have g250P8_2 : CutRow g250 8 2 15 := by
    apply checkedCells 7 2
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
  exact (@joinRow g250 8 0 2 15 g250P8_0 g250P8_2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g250B9 : CutRow g250 9 0 1 := by
  have g250P9_0 : CutRow g250 9 0 1 := by
    apply checkedCells 6 0
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
  exact g250P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g250T : mixedTables g250 9 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty g250 0 0
  · exact mixedEmpty g250 1 0
  · exact mixedEmpty g250 2 0
  · exact mixedEmpty g250 3 0
  · exact mixedEmpty g250 4 0
  · exact g250B5
  · exact g250B6
  · exact g250B7
  · exact g250B8
  · exact g250B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g250G : graphValid g250 (boundsBefore K243) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low250 : Lower true (varsX 250) (graphGoal 250) 10 := mixedLower (g:=g250) (i:=0) (hints:=823218240) (before_sound K243 V243) g250G g250T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K250 := extendKnown K243 10 [(250,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V250 : Known true K250 := extend_ok (m:=250) V243 low250 (by decide +kernel)
def g251MarkBits := limbs80 #[#[0x8038180a04018080200,0x1a0c0582800090481c00,0x4c24110803c1c0305828,0x6c34190c05c2c150a0,0xd020682a1c0882412000,0xa091007c3c000105c121,0xc420b120544622018840,0x8a41828138984a040100,0x60a0060315810022a12,0x15070245e2e1682c581f,0x61d1905416311802c12,0x502235108841234048cc,0xc0dc06040a830021a1b0,0x10a85c74001c810041f1,0xa01050f00a0102854762,0x4c170d0600e3e1a8247,0x8c42410485c30401f8a,0x2283812142210c864202,0x48190101248238988c00,0x161f2407894492186030,0x1c962117084461904890,0x88149c4d18890004c0b8,0xf03830002411860163c1,0x2500180020041793c301,0x82e0b2985c4e1429024a,0x82c08090182c46020010,0x22950121f0683016240a,0x1b04884121f0a81c2a21,0x624c2b094262d1115456,0x10124e0c0e0641a1f11c,0xe15c3411020543221218,0x61581c0458038544a291],#[0xa37141284a59270e8062,0x8ba121b824b80d2d9686,0x3c28118a0262d1183,0x4840b61d2989430092f,0x221201c4e011080c3e17,0x4600300940e032f82c52,0x8cc453170e898612e010,0x39980417001943a64179,0x40e0244666348a0d0033,0xa6c359a8422111988485,0x84671158bce06f37154d,0x88cec753a08442730a9c,0x388c420a059dc420704,0x113d1388a693c9d8f01a,0x2a4e03824b8000387498,0x44f87b0a93846111c1a4,0xf82c467e1188c3a7d0a8,0xa1088418232aa0500103,0xa1c428b89e8441a08201,0x6d0a8010c152e0003,0x1840021348845e041184,0x44114121a0a0744a873e,0x7345040122f448d8000a,0x4a8d20230468b108e0d2,0x402a8f118051c1d0688c,0x1a4c421d3d9a4469248a,0x414a5848384a88446941,0xe1d1da14000b3488c121,0xc3e69038244240082440,0x268002140264209805a5,0x486538154d884004308,0x9e1727422003b01c3a07],#[0x21c0027c3a3b4f86800,0x54e27c0e0445ea004a5c,0x118542001d0044a1a080,0x3484148212601c12a35,0xc2317a4402a500090e04,0xd2a717a88120014a985,0x9982e4717890c443080a,0xe86020450208c20100b,0xb3e2a10c1e219902a03,0xa8a9080842a092a2242e,0xac2010058007040270ac,0xa870ca430e0d84682048,0x108170120048a28801a0,0x445119c4d221179a85e2,0xc424d118004a541188d0,0x88c3a4e108243a230008,0xea48161d002a8200711,0x1010aacd400109c046a7,0x463a10ab000a20a88c20,0xa400af0001d46ae082b4,0x81882a4050000a89a001,0x2001643a400080042265,0x895550e0d201119a4ce8,0xc00241290d642310ac49,0x82ce2210882846855990,0x522882a211d8e85c230a,0xb65a805220011ad04600,0x1601591a5221d0085cd2,0x40462134adc001f2d024,0x89412150a81cd414048,0x157030421d1781cb8690,0x4330a801720c049b5702],#[0x40e405d80554104d01d7,0x8848a55539550c090b8b,0x5acc428d1181cd40030,0x820b90c46961281c0069,0x121d009705e0b521a846,0xe11a002a88d7a105e08c,0x82fc46210a800d2075f0,0x910854140713af04e2f0,0xc10431c042006000070a,0xd82211188402234d2189,0x1b4a8700ea0c12141182,0x39a856095308c2a2361,0xbe038000ec30d1a80423,0x202351a509c18038903a,0xb800c60f88d8a4000310,0x3834f66922800422f000,0x721b218eae0e0543e0c0,0x2001781046ae653248e1,0x28cb001c02209080204,0x3340e23190004a2f6600,0x380749c100a81c002751,0xa0f9516e1c5189042ce,0xe023048840000018219e,0xa40e21191a85c00081cc,0xb87c4291002b8469a049,0x122ad93c702e08c2a6a0,0xe23010402ab80ab40462,0x45eb6688013c2d0f9903,0x900d22120041a42b4207,0x17ab4e68912254001508,0x5c0e951a8651721174d3,0x46006b02412d5381381e],#[0x1c0053010fc4ad704854,0xd0b800070801c0e28350,0xd000240017108002a230,0x81a22ad82a150e2b42e1,0x574691082c8a5c048610,0x11c1221053602a1d38a5,0x1188c9c1d6c8282a091c,0x10048545e986c1a4e600,0x40da04a9c52002e00042,0x84d21d03855b60911845,0x78ad0c3834b700e230e0,0x94d024126d259a90c922,0x17018403a216f1c1ba0,0x412152282dbe694c1500,0x845c2e0200502a643502,0xe9a400e471841c40048,0x7b518412c404481c1642,0x44073f98c3015728009e,0x30d20b0003546c2108bd,0xb995a100008c343a488,0x81d00148da7387012150,0xa2e749d0382b002193ce,0x452ea4802450172a1ec2,0x88c02070a88c380c1084,0x1088c129a0488c56c10e,0x28348003a090e9c54e1f,0xf8243a697589534,0x116ced0e99050ec3488c,0x78742a9a083b83a1a0a8,0xd0a01c16073e0e812017,0x40017bc042094688cd22,0xd02b4308400a71181d5],#[0xa8d6ca3089a446210480,0x14800e60f0b84442da0b,0x10808c026a00884001f,0x2e0011bc870f1000515a,0x68aa2111881e6150080c,0x82611a7d00004121a3e2,0x62a3d4fe3b430ede82d0,0xe2120100468d1c075eef,0xc42bc16868e64c008002,0x1849c15001f134090013,0x234a800450b85c005b,0x402388cca690d0556069,0x462108951469110a1802,0x54c82100068e0004107c,0xd02c762166a69224e038,0xf20011f2077c01c00aa0,0xefa34af012726f9ccaa0,0x90a09108412896200240,0xbf086387d9c400174693,0xd000002304bd49e8611,0x1039bf42015002f49823,0x2e5d024021d003fdfc,0x49aa24a24500694100c,0x8050a68e570742a00120,0x9058860045008542a103,0x423000003a6922c051a8,0xce000003240207178be0,0x91812094a85400100488,0xea88150444855b42381,0x1d0204008a33ea89b421,0x126b15a68d28611c142e,0xec16c70693c46105390c],#[0x327da421019b412e0349,0x93e8857708838550a1e8,0x8508d142300139b50,0x51ac151824e269858240,0x874424c863e8167c1182,0x814c3a092a2080eda10,0x90d10e1c072e02a1a4f,0x2abc3eba04200291008a,0x74008d0ab250c10118b8,0x27c0e75080ec5601048,0x3d800aa290e8008a210,0x425109d4000a72084460,0x80e428843c462517854f,0x847a755188420a311ad,0xd094165411804764e2a,0x211482cc21f350000015,0x3aa048a091a104b09d32,0xec1201108700e004d170,0x1be82e4008208120a3a1,0xb0388c04a323c44e0095,0x2210581c5e110f08d707,0x5451304c483840049a4d,0x840467635172222b060a,0x4b6914000c3d43a0b30,0x23179a628692a0048007,0x5ceb000aca81a800545c,0x5430a203800f41d26151,0xa81c120b048762c0910c,0xb08938122304a5496bc0,0x1004801b4b63f1702e4,0xd21d038400023002c82,0x2a09108042036202e],#[0x45281b44e0617012692a,0xbc069a83a38368749c1d,0x2a840e81c161d3e051b2,0x18a8fe3489412091082c,0xd1c61a5e000681400082,0x7d914866b8ba884a0a0,0xc2812800a91904842304,0x820156ea3a341d000450,0x9b4dc090008c02231186,0x46a14422300030749b17,0x732a1cc471b518540038,0xe040118e0f6820b88d46,0x8ce609039a8460700000,0x1800d6ae7d9ec0f1c000,0x5538b800a303ab90a231,0x51d17950e2380e800421,0x98da22be8461d2008d3,0xe17001cc2f1e2003,0x45278e64e5185400da17,0x1d0803640a334a363e07,0x207c3986820384129c47,0x504617049a534862a3e8,0xe8242e23119b40e69769,0xd432264207001394e7b0,0xa7b9101d4ea30e800026,0x146014105c460050288d,0x88d4ea2119f000005180,0x1184249230a825080911,0x733685446868ec94464c,0x46004d2800e1704ba00e,0x25440036a8c70a36d01d,0x8a2ce2170bc75461a118],#[0x3468681278178543a103,0xe733988c8e10663250c2,0xc802f080024c82089005,0x5c007c0001d3c8211c9,0x385c203a11854d29a00,0x9a42854992811840daa3,0x201551a8c5e9a36875fc,0xed46ae38100288608074,0x29a446150480134234d1,0xb4d101465434c7c12c14,0x91180546822008ce2e,0x880155b280e62311a142,0x28c469a17ca8e3293dab,0xe88d5c540ba342aa73c,0x100b85400383981e4085,0x28000e9b546a251874e2,0x78471f080843b2b11950,0x81c469a39a6846fa502,0x119001882693e898233,0x600039c0706d0aa0a580,0x25a73398550c4722a344,0x548e140aa8d04c13d84,0x50279042f1188442382a,0x3a8d0c2f082594623,0x54400aa8e3a23949510c,0xc1464011a69921711802,0x4c9c2e0700ab96c85519,0x5187412174d01c20100,0x4891788c460903b1c204,0xd6c9a00024121551a8e5,0x1cc20072a4b8126903a9,0x4d21a40690bcbc466d51],#[0x105b0050c6d4f308e607,0x174d48c00710a9a412,0x8cd2a30488c007b1181c,0xf1a56ca34685c2e86368,0x39828c46a303a8080a34,0x2071185c012b4d2782a2,0xc460739be800710aa08d,0xa79341d0a8e0da2f3828,0x17800e6a7039ec209a0b,0x23118554e86118562200,0x629a2a21944233818480,0x8c5e548a0248a9e45026,0x704098154f2388a69062,0x56d1cc007c5708cf8869,0x67c0088c0ea34f2682a8,0xe720001f0007b0a81c4,0x2b80e094311c0e865110,0x200253d33991ccd21500,0x9a03a9c006d03a794e23,0x4600381000e735708420,0x540e6800854289a7d1c4,0x1be85e1703804d201004,0xf9a1008a4003a98e2fa1,0x5411a8c001006000702,0x42a869a88c80fa258008,0x1c000036cd26c233d85,0x2a000d2078f855041d57,0x2a3e08c5ea20a9c53409,0x2e8e5188d3cbe1183047,0xd83b2551be820e704ab8,0x8000212b8ab6846239ba,0xd258014e15518014e400],#[0xe07000e146693dab9346,0x8f6737d08d344c370242,0x3314600001cc2a1036a1,0x39a6a564c4301c02102a,0x6a549ccf61551a9c8a07,0x5e072a2389c01081a4d2,0xb54e860088d3c8a0828c,0x19500e07519cc00780ab,0x6d08e6d2711cd8f62f1,0x6406d219461041218460,0x8c215398014e1511840e,0x8bc469e3d9c0009e11a7,0x118bc20075181c5e150b,0x39930e69a369cc004c,0x4e9a571a50c9a399c812,0x9c004c38a690c2300805,0xd08ca89e9c4d03a40452,0x95108c46da0804000234,0x4000039c980151026680,0xc80232a28ce609119313,0xaa00139239cdf4861785,0x8001986d0388c007111,0x9e3d8e0e2a926001cf2a,0x46077d1ec2a853daf812,0x694f1d4f0262a2311a8c,0x728d533a431f00e1d118,0x60801ce60739c8cd2a21,0x911cd8e2a21c28c708,0xee711800d2840008c0,0x100a89e51a5800000000,0x1c20004d08c2a1500,0x1751228000000ab8e25c],#[0xe215002682a230e81ce2,0x461d4d074e12e0bc1c,0x188d3c174f1cce66d938,0x33985cda9a95800e6475,0xecc264ece673201b42e7,0x4966d2605d349a11a8c2,0xa68e66d0b9cd34735185,0x9d8e000a33988d341739,0xa3663327682399cd469a,0x730b88d46]]
def g251Labels : Array Nat := #[0x611201408413,0x104a0088c426a2,0x220051081621,0x2000502896012,0x1440100844442,0x3040412892450,0x411402410212,0x220412890621,0x280202201281,0x208020300a090,0x10001180c56081,0x104a0200a084a2,0x4008412294428,0x611502c14412,0x3040412882450,0x200220300a012,0x280182c06281,0x611201408412,0x22100c1403412,0x4040413094421,0x400220108c022,0x410502c14412,0x14400c0e03442,0x410201408412,0x400220024c022,0x1440082402442,0x104a02010484a2,0x802000a041228,0x14080c1403442,0x208001a0c2690,0x400502c14412,0x200020108a012,0x2210402210219,0x200100a04209,0x104a02002484a2,0x611502c14413,0x240100a04209,0x208001a0c2490,0x4000412294428,0x2200c1403221,0x220200a01221,0x8080008841288,0x208411084409,0x104a02008484a2,0x1040200825028a,0x200402210209,0x10000008250288,0x60a020300a0b0,0x802008a043228,0x4040412294428,0x104a0088c424a2,0x1480008841288,0x2040502852050,0x1440088c42642,0x20400188c2650,0x10040008250288,0x1020412891428,0x2080200a0a090,0x400201408412,0x1001412891409,0x420201801222,0x10040180e16088,0x60100c1413090,0x6002050a03412,0x60a001a0c26b0,0x6011088c42412,0x104a00c06434a2,0x60a020220a0b0,0x40404110d4460,0x220320108a013,0x10008088652288,0x208412290609,0x200220220a012,0x420200248422,0x1440088c42442,0x208180e06209,0x1020008841228,0x4040008244228,0x420201808422,0x420088c42422,0x60a020104a0b0,0x10040008244288,0x40014110d4421,0x10480088c426a2,0x2080052283490,0x10000180e16088,0x240501804209,0x60114120d4431,0x60a00510834b0,0x1080088c43288,0x1440502854442,0x10420200248422,0x1080008841288,0x1440182c06442,0x102000a041228,0x220202208421,0x14400c0643442,0x4008008244228,0x60a00190c26b0,0x60a00110824b0,0x40010c1407021,0x2230200a08231,0x1020009041228,0x420201048422,0x280203008281,0x104a02018084a2,0x10008180e16088,0x140310180500b,0x410201404612,0x440101804442,0x8020008848260,0x410182c06412,0x420088c42622,0x440089442642,0x2040503816050,0x108000a041288,0x240100a04241,0x440100844442,0x2210180e06219,0x108200a04128a,0x240403010241,0x682203001283,0x2230200a01231,0x240101804241,0x10008008250288,0x602100a0420b,0x102001a0c1628,0x10204120d1428,0x611502414413,0x60a00522834b0,0x208402210209,0x1001101805009,0x8020412898460,0x682182c06283,0x220201808221,0x10403180c56083,0x611182c06413,0x140341205140b,0x2203502896013,0x240413010241,0x2203503816013,0x40014120d4421,0x148200884128a,0x40020c0487022,0x60a00190826b0,0x60241229060b,0x400020108c022,0x104a00894424a2,0x608100a0420b,0x208101804209,0x104a00894426a2,0x3008051083450,0x611501814413,0x602052281683,0x208100a04209,0x3040402052050,0x6018008244238,0x240182c06441,0x2040403012050,0x1001410891409,0x60a40221020b,0x240502a14209,0x4040413094460,0x1080182c07088,0x22300c1403231,0x420200a08422,0x140340301100b,0x8080182c0e0c0,0x410402c14412,0x148200a04128a,0x104a00814024a2,0x3040502056050,0x1080089443288,0x410041408412,0x60a100a0420b,0x104020502d1483,0x2202050243412,0x20800190c2690,0x80800188c26c0,0x4000040245021,0x100080182d0688,0x430201808432,0x20400190c2650,0x208020224a090,0x140341289140b,0x682051081681,0x10008009050288,0x2800c1403281,0x440088c42642,0x200412290609,0x4200c0e03422,0x80020c024b042,0x220050a81621,0x8000402418050,0x140310084500b,0x8001412058041,0x60a004220a0b0,0x200040a01221,0x1000a0182d0688,0x1482182c0708a,0x420203008422,0x108001a0c1688,0x800150084c041,0x80200188c1628,0x60a41229060b,0x20800188c2690,0x240412294409,0x240412890241,0x10014120d1409,0x2080203007090,0x3030008841238,0x10420201048422,0x104a00c0e034a2,0x2080051083490,0x204001a0c2650,0x60800190c2690,0x208020180a090,0x10040181c160c0,0x60a41229020b,0x4200c1403422,0x60240221020b,0x200180e06209,0x104a0040a084a2,0x8010180c4c050,0x208200a08209,0x208202208209,0x400088c42622,0x410102c04412,0x2002412892412,0x602180e0620b,0x611402414413,0x410241609412,0x1408220108c0a2,0x1080009041288,0x9001089403209,0x60a020108a0b0,0x10402180e1608a,0x108008a443288,0x611502c04413,0x4040011084460,0x208413090609,0x2040502856050,0x60a001a0c24b0,0x10000201418090,0x1408220104c0a2,0x1040a00825028a,0x4008411094428,0x240100a04409,0x80020188c8242,0x4000008244228,0x4040009044260,0x800210084c042,0x140202014180b0,0x420089442622,0x440089442442,0x20a088642409,0x10001051091481,0x100010c0653081,0x220320180a013,0x8020010888460,0x40004120d4421,0x20a402210209,0x60110c1407031,0x148200904128a,0x8010088c48250,0x220203008421,0x8010182c0c050,0x140400804920c0,0x2040412892450,0x400120108c021,0x440182c06442,0x4008009044228,0x800110084c041,0x60a001a0426b0,0x2040503012050,0x220010a81621,0x148201a04168a,0x808000a0482c0,0x1040a0182d028a,0x3040010882450,0x10420182406422,0x1001403011009,0x10040180c560c0,0x682203008283,0x6018088646238,0x2230201808231,0x80200188c8660,0x40400190c4660,0x2230412890631,0x1001100845009,0x240413090641,0x2040011082450,0x2080052282490,0x4040411084460,0x148001a0c1688,0x220040a01221,0x148200a44128a,0x240051281641,0x440503814442,0x440081402442,0x1040a0182d068a,0x2230410890631,0x14034120d140b,0x80200c0e0b060,0x8002412898442,0x3040051083450,0x20a412290209,0x14400c1403442,0x2400c1603241,0x100100184d0690,0x80800522894c0,0x4040089446260,0x800150285c041,0x808008240a0c0,0x440501804442,0x148201a0c168a]
def g251Mark (j : Nat) := (g251Labels[packedAt g251MarkBits (9*j) 9]?.getD 0) <<< 8
def g251Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xc000003f8001f807f0,0x3101fe3731cc79f7f22])),(BitVec.ofNat 152 (word80 [0x81414141028a002820,0x100c63330cc38b1e00]))),((BitVec.ofNat 152 (word80 [0x3fc0007e07f804,0x1c619c003c22f863f805])),(BitVec.ofNat 152 (word80 [0x50d0d0d0a1868a1a14,0x86199402202a1215401]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x7f800007f0,0x2081e00840c3007c7ffb])),(BitVec.ofNat 152 (word80 [0x4a8a8a8a9534595150,0x80a008c443007460fb]))),((BitVec.ofNat 152 (word80 [0x3fc000000007f801,0xc0fe001380fc007f801c])),(BitVec.ofNat 152 (word80 [0x870707070e1830e0e0,0x4092001200f8125a8008]))),((BitVec.ofNat 152 (word80 [0x3fc000007ffff80009,0xff00001c00ffff800042])),(BitVec.ofNat 152 (word80 [0x242424244841248489,0x7208021400b01c000000]))),((BitVec.ofNat 152 (word80 [0x3fffffff800000000e,0x1fff000000009d])),(BitVec.ofNat 152 (word80 [0x80808081020410100,0x8480000000094]))),((BitVec.ofNat 152 (word80 [0xc0000000000000000f,0xffffffe00000000000e0])),(BitVec.ofNat 152 (word80 [0x30303030604186060f,0xbe4d5380000020000000]))),(0x0,0x0)]
def g251C : List ColumnInfo := [(8,0,243,0,11),(1,0,250,0,10),(32,0,219,0,10),(64,0,187,0,10),(128,0,123,0,10),(2,0,249,0,9),(16,0,235,0,9),(0,2,137,112,7),(0,8,82,161,7),(0,16,41,194,7),(9,0,242,0,7),(10,0,241,0,7),(24,0,227,0,7),(33,0,218,0,7),(34,0,217,0,7),(40,0,211,0,7),(48,0,203,0,7),(65,0,186,0,7),(66,0,185,0,7),(72,0,179,0,7),(80,0,171,0,7),(96,0,155,0,7),(129,0,122,0,7),(130,0,121,0,7),(136,0,115,0,7),(144,0,107,0,7),(160,0,91,0,7),(192,0,59,0,7),(1,8,82,160,6),(2,16,41,192,6),(3,0,248,0,6),(16,2,137,96,6),(17,0,234,0,6),(18,0,233,0,6),(32,2,137,80,6),(32,8,82,129,6),(64,2,137,48,6),(64,16,41,130,6),(128,8,82,33,6),(128,16,41,66,6),(11,0,240,0,5),(25,0,226,0,5),(26,0,225,0,5),(33,8,82,128,5),(35,0,216,0,5),(41,0,210,0,5),(42,0,209,0,5),(48,2,137,64,5),(50,0,201,0,5),(56,0,195,0,5),(66,16,41,128,5),(80,2,137,32,5),(82,0,169,0,5),(96,2,137,16,5),(98,0,153,0,5),(129,8,82,32,5),(130,16,41,64,5),(138,0,113,0,5),(145,0,106,0,5),(146,0,105,0,5),(152,0,99,0,5),(160,8,82,1,5),(168,0,83,0,5),(192,16,41,2,5),(208,0,43,0,5),(43,0,208,0,4),(49,0,202,0,4),(58,0,193,0,4),(67,0,184,0,4),(73,0,178,0,4),(74,0,177,0,4),(81,0,170,0,4),(97,0,154,0,4),(104,0,147,0,4),(112,0,137,0,4),(112,2,137,0,4),(114,0,137,0,4),(153,0,98,0,4),(154,0,97,0,4),(161,0,82,0,4),(161,8,82,0,4),(162,0,89,0,4),(176,0,75,0,4),(193,0,58,0,4),(194,0,41,0,4),(194,16,41,0,4),(200,0,51,0,4),(210,0,41,0,4)]
def g251A : List (List Nat) := [[],[65,117]]
def g251D6 := limbs80 #[#[0x551520c5765915454831,0xc5a7591545483161964,0x5915454831e1d6455152,0x5483165974551520c7a0,0x68176551520c5865d954,0x551520c5a45d95454831,0xc5a95d954548316a176,0x659545483165d8655152,0x54831e9d96551520c787,0x65f84551520c576e1154,0x591520c574e416454831,0xc59564174548315d790,0x6557454831619955d152,0x54831a61955d1520c596,0x651925d5640c7a065974,0xe01640c5986497559031,0xc598261525c03168975,0x551525c0316909854970,0x5c03161154549700c564,0x6a154549700c5a655152,0x549700c794551525c031,0xc498615525c03161584,0x615525c031e618554970,0x5c03161584551700c7a4,0xe5182601750c7a266164,0x609750c7a0609805d431,0x44394611825d43165984,0x611520c5106a16554831,0xc510695865483144165,0x65992614314419264185,0x54940441a65515250110,0x44185591525011059564],#[0x54831541102858554940,0x54110659520c55044194,0xdd164549504418459152,0x595524416454a4154110,0x4c6a7e55805493128d91,0x551520c5406816450d61,0xc54061d545483150186,0xe615454831501a855152,0x5483150185591520c540,0x501a8591520c54061964,0x5d5520c5406a16554831,0xc5406a1755483150186,0xea17554831503985d552,0x5483150165611520c540,0x501a4619520c5405d584,0x595640c5406958654831,0xc540689855903150185,0x6a3925d831501a661564,0x6003150154549800c540,0x503a25d9800c5405d552,0x5d9850c540e897661031,0xc5406499061431503a2,0x65192614315019464185,0x6143150196649850c540,0x503a265d860c54065d92,0x54831541406519054931,0x54140659520c55050194,0x661520c5505019754831,0xc550503a95483154140,0x50197550315414065954,0x5503154140661540c550,0x541406a5650c550501a9],#[0x695960c5505016565031,0x54950501865915254140,0x503a46195254140e9183,0xa0d52541405926354950,0x54140e897655150501a4,0xe859355150500a164d54,0x58550501a6a4d5454140,0x501a6551615414059152,0x549815414028d9159550,0x541406a5549c55050394,0x6a5549cd505019855273,0x551525019454a8154140,0x503a164d545494028593,0xa4d54549406829355152,0x54940e997559152501a6,0xe819759552500a364565,0x5d552503a465d6554940,0x5019324d755494064491,0x64d7554940e91915d552,0x54940e85935d552500a1,0xe91965d552503a464d75,0x5d552501a4a457554940,0x501a4a4d755494068293,0xa4d6454d405959359153,0x58540699545496150165,0x65565a0d645017559152,0x60261501a9e0a815d940,0x541a8e49769cd405d552,0x611520c5506818454831,0xc55069d8454831541a6,0xe918754831542a761152,0x5483154184dd1520c550],#[0x541a8dd1520c55061b74,0xe41520c550e637454831,0xc55061f905483154184,0x68186550315418659154,0x5496154374549800c550,0x549645498090550e8d87,0x60d8055152e596460154,0x55152e858360154548a1,0x5909160d5454b9661980,0x60d54549762458355152,0x54b74245835515261891,0xe4583551525939160d54,0x55152dd39160d5454986,0x28d91619545499124586,0xa0d5454ba36458655152,0x5499659283551525d964,0x61a8355152e8164a0d54,0x5496161594a056454996,0x6519059552584a165954,0xa8adc1eda65515258710,0xea4d725b91dc73a39717,0x9ba2dcf2a6b534b965c9,0x566a9d54ba8dd36699d4,0x5caae4d666b1d58baad5,0x5b2ad1d68bb2d592ec95,0x786ac2dde86e9570bb6c,0x9e33b19789ec3d61e70e,0xa794eca5e47b2378d9c6,0xe3670f31d98bcad65672,0x49da4bd0de7333959c9c,0xd61ea67527a8ed45e96b,0xb693b19d85eb4b595ac9],#[0xcdc56e2770db83da66d2,0x2f8b5c4ee25ef23723b8,0xd8e657327935c99e49f2,0x60fa95d49e8d743ba17c,0xe4af05f723b31d8aec4f,0x7c2be13ec8f457a27cb1,0x21b6d089333037f88fc1,0x85efb2c2667b0a762cb8,0x2e039576a725d80a5f69,0x3767b62cb453e69066fb,0x8ed349ae65a958f48173,0x4126d854a76d0325a701,0x1e702ecc229b68a38dba,0xecc829b68838d8155460,0xfb81e7add4ca56a46592,0x74cb3d3565a26b2ecac2,0xe3e5d8fa9162e48bb008,0x4b5bb2ce1b8b13298d40,0xc0060db9b303d806c4aa,0xda4676ccb3e5e6d8bb4a,0x3ed84f136dd87830c38d,0xdf06587312e15575b455,0x178fb60991f816dbbc2a,0x801a49b015bad22fe359,0x590b07cd31e9ced0a58a,0xbad02bcc68db72ac156b,0xb465a153aa72429b704,0x2131f48fe11b675daa82,0x615801b5921bd80c4b59,0x5b42380d310c96e83887,0x7cd3a6996daa8476aa47,0x6ea65084f36c802db624],#[0x95b1aece8c7968aa3d84,0x2d08bb96a5c4b8568f6d,0x1a16d9abb37866da5da7,0x98b8b6a4ec8ece76c933,0x3696dcf2ab002af1966e,0x2c80b742399a45db7d05,0x4c8cd7968986b057e44c,0x7766fd7d8c88bed87d2b,0x64bb3bc0690a379631d3,0xd80ed64942a321b5903c,0x9da9f0c728fb81c98bb3,0x6d4075b6519eb239d65d,0x5b6ad98bb362b698fceb,0x96b2429c6da58536a2c6,0x58602cb1aecb88bb409,0x31f2c88f1540b038dba,0x6c8f3fa08b0ddcaa25e8,0x57604acbb31e95d8f033,0xddb22cd5d9bb430c692,0x1ea5d9424b401d1540af,0x99b3b0c6ac5a60fb140d,0x748809b52676b2303769,0xdba358ec0b52e682b9eb,0xc4b240d5640a9176e039,0x61a6d970336e8603b590,0x67db7496f52b1309ed04,0x50118d801289cb15aa6a,0xfba8218db3672a05c64b,0xa058c6cc2dcc0436aa4c,0xc3f698970b6ebb1d903e,0x9e73d746b7bb62e95dbd,0x21428db81c18db34ba65],#[0x790af33d855986c2da47,0x1cd85a316803e32c948b,0xa4c5cdb42f6ab4b1a676,0x1186b6eb167a3b40cdca,0x688869b678e4c31c5559,0x3962c23d805416e8f34b,0xd0d31a41698f1136001b,0x81ec02b3b706a25ba3c,0xdf86b6c4e2bb002d2baa,0x74359da635b4b0563365,0xd7679aebb2fcc4421d4f,0x84d24fcbdd9eb52c8a32,0x7b069d9ccb615505a64d,0x9d2aaec7f7186aab5d31,0x611ed5766039db4ae3dd,0x1b65045da033269988bb,0xaac007bc659bc6f6cb28,0x12569a6d5b529b99b45d,0x894336d34e1947e7cbaa,0x6c65a9903d96bb3d5665,0x5b00d01daa7d2a05cb6f,0xcabb55bee1c116b215e0,0x95d6e670036b2075b428,0x1363b02da11ba612cd85,0x2846dda6610fdaa9c768,0xda907dabb516d618dabb,0x84d02749a85f6e7636ab,0xe67e98d5f34d302db81e,0x2a752c8431da993bacb4,0x4d016530b400daa790ec,0xd646598d30ed75d956ff,0x82d2a568e98d05b6074d],#[0x43165a0d2f4c8d01a49d,0x1cf036ec24bb913dac0b,0xc16065b0ad05da933965,0xd9820b0c1d1c769a721a,0x25d802aee5a9262e0098,0x516a1ae66ecd871b73c,0x44353303b25a37d46db1,0x480f05654242db19b169,0xdba610edaa9ac6998e4b,0x68cb423b659ec536d0cd,0xe70618df3730e2b790b0,0xa0d1b704179a62e8edd4,0xecafc5836bc6d22f31e5,0x964a52ddcd8e96003aaa,0x3bdb28856d569a72d0b1,0x43e69e51eb4e9667b4a8,0x4c5ed748939647edac1b,0x293a71b62aa8c03d72ac,0x1b677bab22fcc59226bb,0x6c4ab6cbc1,0x0,0x280,0xa000000000000000005,0x140000000000000000,0x2800000000000000,0x311d08b0051d83ee968c,0x4db0c682683011aa0c29,0x8c3911e0400870684998,0x1b4203c]]
set_option maxRecDepth 32768 in
def g251D7 := limbs80 #[#[0x5d154548315915454831,0x61954548315d95454831,0x65d54548316595454831,0x5d16454831e115454831,0x61164548315d56454831,0xe1d645483165d6454831,0x6117454831e416454831,0x64174548316197454831,0x65974548316557454831,0xa6174548316617454831,0xe197454831e117454831,0x5d580548315d18054831,0x5d58454831e5d8054831,0x5d38054831e5d8454831,0x5d784548315d78054831,0xe41645503165d6455031,0x61975550316197455031,0x65176550316417655031,0xe5d86550316617655031,0x64381550315db8155031,0x6417559031e157459031,0x66175590316497559031,0xe157559031a617559031,0xe558759031e418759031,0x5d780590315d38059031,0x261525c03165f8559031,0x591525c031551525c031,0x615525c031611525c031,0x651525c031641525c031,0xa61525c031661525c031,0xe41525c031e11525c031,0xe61525c031e51525c031],#[0x611545c031591545c031,0x659545c031615545c031,0x611645c031661545c031,0xe41645c031661645c031,0xe61645c031e55645c031,0x619805d031e51855c031,0xe41865d031619855d031,0x609805d431e55865d031,0x611825d431e51805d431,0x651825d431641825d431,0xe51825d431e41825d431,0x611520c510595520c510,0x619520c510615520c510,0xe41730c510e4d650c510,0x641840c510595840c510,0x649850c510641850c510,0x590314c110548314c110,0x650314c110648314c110,0x5903150110654314c110,0x55151501106583150110,0x55152501105915150110,0x59552501105915250110,0x5d554501106155250110,0x59564501106595450110,0xa4564501106156450110,0x24585501105918350110,0x54a6150110e498650110,0x59331501105526150110,0x59552505105515250510,0x54831541105d55450510,0x64831541105943154110,0x65431541106503154110],#[0x54941541106583154110,0x59541541105514154110,0x591525411025d5254110,0x61152541105d15254110,0x64d52541106195254110,0x65952541106515254110,0xdd15254110a455254110,0x5915454110dd95254110,0x61954541105d15454110,0xdd954541106595454110,0x61164541105956454110,0x6456554110dd16454110,0x5958454110a456554110,0x592415411054a4154110,0x552615411054a6154110,0x597315411054b3154110,0x5d154545105915454510,0x5d15454910dd95454510,0xdd954549106595454910,0xdd164549105956454910,0x65d65549106456554910,0xa5d6554910a456554910,0x5957454910e196554910,0x6568754910e418654910,0xa5f83549105977454910,0x65281591105d56455110,0x65681595106528759110,0x59152905106568759510,0x61154985105515298510,0x59553cc51059552cc510,0x59154545315915354531,0x5d154549315915454931],#[0x65954549316195454931,0x6116454931e115454931,0xe416454931dd56454931,0xe557454931e616454931,0x61180549315518054931,0xe118054931dd58054931,0xdd58454931e558054931,0x6438454931dd78054931,0x5914358531dd78454931,0x64152585315955258531,0x6416458531dd55258531,0xdd552985316415298531,0x551520c54050d61dc131,0x595520c540591520c540,0x611520c5405d5520c540,0x619520c540615520c540,0xe61520c54061d520c540,0x619540c540615540c540,0x661540c54061d540c540,0x615640c540595640c540,0x61d640c540619640c540,0x615650c540661640c540,0x661650c540619650c540,0x619750c540615750c540,0xe61750c540661750c540,0xe49760c540661760c540,0x551800c540549800c540,0x5d5800c540591800c540,0x595840c5405d9800c540,0x5d9840c5405d5840c540,0x641850c5405d9850c540,0x651850c540649850c540],#[0x651860c54065d850c540,0x65d860c540655860c540,0x551514c54054d514c540,0x591524c540551524c540,0x5d5524c540595524c540,0x651524c540641524c540,0x591534c540e15524c540,0xe51874c540e49764c540,0x5483154140653874c540,0x59431541405503154140,0x65031541406483154140,0x65831541406543154140,0x660315414065c3154140,0x55131541405493154140,0x24552541405913154140,0x58d525414024d5254140,0x5cd52541405915254140,0x619525414060d5254140,0x9cd525414098d5254140,0xe455254140a0d5254140,0x5d95454140e4d5254140,0x64554541406195454140,0x659545414064d5454140,0xa4d5454140a455454140,0x55161541405496154140,0x59561541405916154140,0x59563541405516354140,0x61964541405956454140,0x65564541406456454140,0x5d96554140a456454140,0x64d65541406456554140,0xa4565541406516554140],#[0x5497154140a4d6554140,0xe5171541405517154140,0xe5573541405517354140,0x5498154140e497654140,0xe5181541405518154140,0xe5183541405518354140,0x54a3154140e518654140,0x59231541405523154140,0x54a61541405963154140,0xdc661541405526154140,0x59263541405526354140,0x552715414054a7154140,0x65671541406527154140,0x64a73541405527354140,0x65673541406527354140,0x54a81541406627354140,0x65281541405528154140,0x55283541406568154140,0x65683541406528354140,0x553315414054b3154140,0x55371541405973154140,0x55381541405977154140,0x55161545405d95454540,0xa4564545406456454540,0xe5171545405517154540,0xe518754540e497654540,0x64261545405526154540,0x65271545405527154540,0x653875454065f8654540,0x64081549405508154940,0x55083549406508154940,0x65083549406408354940],#[0x64d54549406455454940,0xa4554549406595454940,0x5516354940a4d5454940,0x5d563549405956354940,0x5d564549405956454940,0x64d65549406456554940,0x65d65549406516554940,0xa4d6554940a456554940,0x5d573549405517354940,0x24d75549402457554940,0x64d75549406457554940,0xa4575549406597554940,0xe457554940a4d7554940,0xe597554940e4d7554940,0x61180549405518054940,0x5d663549405926354940,0x5d673549405527354940,0x65273549406427354940,0x65776549406568754940,0x64383549406438154940,0x5956454d405956354d40,0xa4d6454d4064d6454d40,0xe517354d405d96554d40,0xe518754d40e458754d40,0x6527354d406427354d40,0x6538754d406438754d40,0x2458355140e497655140,0xe418655140e458355140,0x64283551406568155140,0x65a83551406568355140,0x59152585405515258540,0x5d552585405955258540],#[0x5d564585406595458540,0x655645854064d6458540,0xe418758d406538758540,0x6538758d406438758d40,0xa4565591406456559140,0xe4d7559140a4d6559140,0x5958159140e597559140,0xe4181591406158159140,0x61583591405958359140,0x5968159140e418359140,0x65681591406428159140,0x596835914065e8159140,0x65683591406428359140,0x24d815954065a8359140,0xe498759540e418759540,0xe598759540e518759540,0x65687595406568159540,0x662875954065a8759540,0x65f83595406538359540,0xe49765c5406538759540,0x657845c5405db845c540,0xe19645cd40e15545cd40,0xe19765cd40e15755cd40,0x604815d540e49765cd40,0xe49765d54060c835d540,0x245835d540e51815d540,0xe51835d540e45835d540,0xe51865d540e49865d540,0xe06815d540652815d540,0x652835d540642835d540,0xe09815d9405db835d540,0x642815d940e41815d940],#[0x617825d940e0a815d940,0x657825d940647825d940,0x551518c540a47825d940,0x591528c540551528c540,0x5d5528c540595528c540,0xe49768c540615548c540,0x5515298540e497694540,0x66175985405d55298540,0x5d580985405498098540,0x611529c5406556498d40,0x661549c540615549c540,0x661649c540619649c540,0xe45759c540615759c540,0xe49769c540619769c540,0x661549cd40615549cd40,0x661649cd40619649cd40,0x619769cd40615759cd40,0x551809cd40e49769cd40,0x5d5809cd40591809cd40,0x5d5849cd405d9809cd40,0x55152cc5405d9849cd40,0x59552cc54059152cc540,0x64152cc5405d552cc540,0x59553cc54059153cc540,0xe4986dd54059564cc540,0x64154545415d95454541,0xdd954545416595454541,0x5d954549415538054541,0x64154549416195454941,0xdd954549416595454941,0x64165549415d96554941,0xa5d655494165d6554941],#[0x5518054941e196554941,0x55383549415538054941,0x6568759541e558759541,0x55152dc14155151dc141,0x591520c55059552dc141,0x61d520c550611520c550,0xe41520c550dd1520c550,0x591540c550e61520c550,0x619540c550611540c550,0x549800c55061d540c550,0xdd1800c550551800c550,0x655840c550641840c550,0x65d840c550659840c550,0xe51870c550a5d840c550,0x617740c550613740c550,0x663740c55061b740c550,0xdd1524c550651524c550,0x549614c550e41524c550,0x5d9525055054a614c550,0x61d52505506195250550,0xe1d5250550e195250550,0xe195450550e415250550,0x54971505506196550550,0x54a71505505517150550,0x65671505505527150550,0x64081549506578750550,0x65881549506508154950,0x65d64549505d16454950,0xe418154950e457454950,0xe418454950e5d8154950,0xe4d8454950e458454950,0x65b7454950e5d8454950],#[0x65381549505d38054950,0x5d9645515065b8154950,0xa4564551506416455150,0xe4d6455150e456455150,0x2458355150e517655150,0xe418655150e458355150,0x64283551505928355150,0x65e835515065a8355150,0x61d52585505915258550,0xe415258550e1d5258550,0x65954585505915458550,0x65165585506416458550,0x54a71585505497158550,0x65671585505967158550,0x61580591506578758550,0xe518759150e498759150,0x65287591506528159150,0x5d1525c5506578759150,0xe11525c5505d9525c550,0xe41525c550e19525c550,0xe19655c550e11545c550,0x61d528c550611528c550,0xdd1528c550659528c550,0xe41528c550dd9528c550,0x549808c550549618c550,0x61d52905505915290550,0x5956490550e415290550,0x54971905506416490550,0x59180905505498090550,0x61d52985506115298550,0x6115498550e415298550,0x54980985505497198550],#[0x5d9529c5505d1529c550,0x619529c550611529c550,0x611549c550e41529c550,0x619659c550661549c550,0x615749c550661659c550,0x549809c550e45749c550,0x64564551516416455151,0x5918055151a456455151,0x55380585515915458551,0x6528759151e4d8759151,0x55161dc15159154dc151,0x611541c552591541c552,0x659541c552619541c552,0x611641c552595641c552,0xa4d6455152595801c552,0xe617655152e4d7655152,0x60580551525918055152,0x619805515260d8055152,0xa0d8055152a058055152,0x5918155152e4d8055152,0x61981551525d98155152,0x2458355152dd18155152,0x5d983551525918355152,0xdd183551526198355152,0x2458655152e458355152,0x64586551526418655152,0xe418655152a458655152,0xe4d8655152e458655152,0x5da81551525928155152,0x652815515261a8155152,0x5928355152dd28155152,0x61a83551525da8355152],#[0x65283551526428355152,0x61b7455152dd28355152,0x643865515265b8055152,0xe4187591526158159152,0x6168159152e558759152,0x65780591526528159152,0xa61545c1526578759152,0xe11545c152dd1545c152,0xe17815c152597815c152,0x61954dc55259154dc552,0x5d164dc55265954dc552,0x55180dc55261164dc552,0x59584dc55259580dc552,0xe558159154e498059154,0x6568159154e558359154,0xe19645c1546568359154,0xe45735c154245735c154,0x590815cd54e19765c154,0x593815cd545d8815cd54,0x604815d9545db815cd54,0x24d815d954e49805d954,0x656815d954e4d815d954,0x615649c554e06815d954,0xe41649cd54619649cd54,0xe4d769cd54619769cd54,0x64164dcd545d9859cd54,0x6416450d6159180dcd54,0x61164549616595454961,0x64165549616556454961,0x59580549616516554961,0x59780549615958454961,0x24586551616416455161],#[0x6118059561e498059161,0x61152dc16155152dc161,0xe0a715c164e09715c164,0x657825c1645d7825c164,0x5d5849c564e45759c564,0x5915454631e4980dd564,0x5d15454a315915454a31,0x6595454a316195454a31,0x6116454a31e115454a31,0x5d96554a31e416454a31,0xe557354a31e196554a31,0x5958054a315957454a31,0x5958454a315cd8054a31,0x5955258631e416455231,0x595525c2316415258631,0xe4d655d231659525c231,0xe557354a416556454a41,0xe4980592415cd8054a41,0x591525c241e458559241,0x6416498e41641645ce41,0x5515250710e557354a61,0x5d554507105955250710,0x5915454b105915454710,0x6595454b105d95454b10,0x5d564553105956454b10,0x5515258710e5d8655310,0x65954587105915458710,0xfe8ef8df87f87d87b877,0xd97b97a97796f95f95b8,0x9cf9ce9cb9bb9af97e97,0xeb9e79de9dc9db9da9d8,0xb9fa9f49f09ee9ed9ec9],#[0xa7aa6fa6ba5fa5ba3fa3,0xcbabdaafa9fa7ea7da7b,0xeadbadaad9ad3acfacea,0xafcaeeaedaebae7ae5ad,0x59b4fb4eb4db4bb2fb1b,0xeb6db6bb6ab5eb5bb5ab,0xb9bb99b8fb8eb8bb7ab6,0xc9bb9baebabba7b9eb9d,0x3bd1bcebcdbccbcbbcab,0xbdabd9bd8bd6bd5bd4bd,0x5dc5bc3fc3dbecbe6bdc,0xdc7bc7ac77c6fc6dc5fc,0xcb7cb5cafc9fc9bc7ec7,0xd4ccfcceccdccbcbecbb,0xccdbcdacd9cd8cd7cd5c,0xcebceace7ce4cdecddcd,0x1ed1bcfacf6ceecedcec,0xbd3ed3dd3bd37d2fd1fd,0xd59d57d53d4fd4ed4dd4,0x6dd6bd67d5ed5dd5bd5a,0xbd7cd7ad79d76d73d6ed,0xd9ad99d98d97d8fd8ed8,0xaddacdabd9ed9dd9cd9b,0xadc9dc8dc7dbcdb9daed,0xdd4dd0dcedcddccdcbdc,0xe4de0ddcddadd9dd8dd6,0xbdf8df4decdeade9de6d,0xe4be3ee3de3be37e2fe1,0x5ee5be5ae57e4fe4ee4d,0xbe7ce7ae79e6ee6de6be,0xe99e97e95e8fe8ee8de8,0xaeeadeabea7e9ee9de9b],#[0xeecdecbecaec9ebaeb9e,0xee9edcedaed9ed8ed3ec,0x17f0ff0ef0df0beeceea,0xaf2ef2df2bf25f1ef1bf,0xf59f55f4ef4df4cf4bf4,0x8bf8af89f87f6cf6af5a,0xcf9af99f96f8ef8df8cf,0xfc8fc6fc5facfa6fa5f9,0x6105bfd8fd2fccfcafc9,0xa2da05921798cca8c088,0x917eca0f6cd650603f30,0x1e6a4600f74a31319a21,0xaa8a9851a91ed62cb0f6,0x164986ca13a7365ad889,0x52126a55a8374cc4a7d9,0x41f29298f9a08ecafd12,0xba317086539165769128,0x2244e0dd2bf4cb2a078d,0xeb3e330a926d965a4afd,0x958a16047cd232ec0dd2,0xed30d23ee91966732830,0x96b92334819a81755f8a,0x6bae59619586ca8caeb5,0x623ca11a57e81823d32d,0xf690a211f4925857a944,0x28a0a159617982aa2f63,0x934e6cb5ff115903460f,0xcad65afd3d3287f38187,0xb2893857a0a0992cb13,0x7584c96d33786965cfe6,0x23c83648fd64aca3eb6d,0x548b520123196174aed2],#[0x8fa23f086d3a3c43a9c8,0xd214ae0e60377f942360,0x8a38faca4da81974447c,0x2a0f96ae122cbee03ee9,0x24d4a245e28c97832cbb,0x64d93701301ba83769cc,0xc2d383a013d04c35e09d,0x447cd3800dc61b6b3b30,0x3ce98a921742caacd964,0xaa88a2b996449aab2e86,0x46358eca8c27a6170a60,0x30fa592b8832ed3b267a,0x606e978475651a886d03,0xba1604aed0308156827e,0xa09e5c28ca861aa8ba95,0x9f64b2c3d8b9a8364d3c,0xb558637106cc222b5658,0x2d25be436943b25b4d6e,0x9b42193502b164a14b02,0x7d8c7a3a4582ca2be3c6,0x592ca13906594a712f44,0x5aa525173516b3279620,0xeacf26d97449fec28ea1,0xbcc86d4068d561a4c832,0xc9165b6e7ff084e0c4a3,0x5f4b9bba565c5824d050,0x651f8d8ba04efa550f42,0x6e7065971560aa8adb0d,0x43fb0a2d15da44989cd3,0x4774215b6d3c9511e503,0x53c949965d7d7cf0c3c4,0xa462074c483e9a0929b7],#[0x495da447638b296edc61,0x2bd34e6c1651562194e4,0x6908e4cb2ebd3b5862ec,0x39b1cd98b6932cb80c43,0x5d83ca28e6f660335914,0x61a9c8c1f7411b9eb94c,0xb4a1e381850f20cbb000,0x469987cb1047ae60d921,0xf8c1651111ff41192298,0x502ead1355869216acb0,0x95484182aa34c02ea727,0x48f83ce998d17b4135be,0x5321b4e8e8cda09a02ed,0x81fa701183d0304e0dd2,0xcd3edadbe50511f748ca,0x823c6db09263a586b587,0xbf9ea9868132bab463ce,0x5c0c286cdd614414caea,0x65db6d77b4a2c87da918,0xc97801da900924cb2d50,0x49104c8de232286e2602,0xdb6134234f306e47564,0x3aedb60bba4c4d32cb02,0xa23e1b9c30f50d590d88,0x5a2ce6986334f312609f,0x5cb4833371752e4f6ca,0x8da50f1d2c31b2ade5ae,0xca8ec236a24c2cf42960,0x9204cb2e000fda08d586,0x2bbd8615907ca57f1d61,0xb6c3c1a57691272bb489,0xe8277506e939a83a0635],#[0x2cab055469c02d41e615,0xcd82aa2fc9a65d742114,0x21e890311b506e0c7a3b,0x3287e805a88887dd2328,0x493540baaf68261aeb3e,0x7407694b13e330ad3e98,0x95aa83a849a0a1ddec31,0x97509c65d0dc4f959457,0xac2000ea5f04cb28151a,0x134f0e0215fa448dc0b,0xb81753d0e7cb5c699658,0x2baaf9065d5bd4132c2f,0x937374acb6dbe5842e13,0x39c1d75dd136cbaa51c5,0x8afd224273e5b180af49,0xc6993133aec139a5980a,0x4fb62d5a520256b21344,0x21a0cb26851d591301fb,0x4db61a47752c96890fa6,0xcb0db4c1d64b54865391,0xa40de22c2068ef61b6a7,0x3427c6565689aea3b10f,0x788f4494805a9800d34c,0xa586c485cd261a126a55,0xd3142fa6146a01752f7b,0x2eb1f348cc20f96b2c7f,0x9419a4009b8bb46cc059,0x10b292c1b6a4653e3308,0xe819611f506e10da60d2,0x423101a424d334c02043,0x7507cb562db61cd905f4,0xa065d516df0e0036d753],#[0x746c14197601982aa344,0x48b4b7d1a5463e8d232c,0x99216829428b4ca03459,0x2c741a63ed853684dd00,0x56553cb0d01851e5daec,0xaa030b6a0028f2ed7ec8,0xbc1ef4011add9644ceac,0xa959603cdac383e5fe80,0xaaa45a5b6992f8730c03,0x533996b0842a717507e5,0x9c479862f94acb812b46,0x9f6c3453126181062b2a,0xc69c0c62b2b5b3459442,0x44738e7a0c8e3cc36980,0xc616c3004ec614e67db,0xac55951591aca69b79a4,0x9146e43eda6928b7d1a5,0xa545c60d449f1e597512,0x5faca5daeb3eb3127add,0x97730d17c2da0008b1d0,0x91862155ecabae346a24,0xcb2ce58699842c34d754,0xa574e32814bc9a09458a,0xd295980455fcab9a7d65,0x24c3002a55d00c7a30c6,0x6883150b2e01bed84926,0x88d4856547236b2b54e1,0xa5f6b29ba5d28d8a96b4,0x29591047630b18285920,0x2ec0fcb55442a16bb47b,0x6449d8c349f0169ab14a,0x231e5dae770b2c28b159],#[0x4a328114858623c8fd00,0xd656ac12d383f15dd92c,0xb1fafb618d98f2ed7c46,0x897830c6dc79a46f90ec,0x3b1a494468d41b6c4592,0xd29be386a0da90b4a99,0xd40c5bb2b4b2d165d49e,0x5f3d1a437cb5d0696a15,0x23cc30005ae80bd2c740,0x4658fe27f419d48d65d7,0xea04c399603a42d22668,0x39c30d4a266028d3c892,0x84fe9339896ecc0bb1a6,0x934815163a0000b1d05d,0xa839a4cd01a24f683548,0x9984d695ca3ab30730b1,0x580aed5c251937308953,0xc1837d948a0654ec61eb,0xcaba7215953a53eeca49,0x2c480b075a44a93c395e,0xf00fa009069d1dc6cb65,0xb7d2123125d80690aec9,0x682f738f0cfa075a652c,0x344021a0cad4250b1a16,0x29f6d3c94c55955c4e2e,0x1228d898aeeca4407854,0x263189a19588642b2a71,0x4261c3bb55470aa10e38,0xe8abe88468ab0cb4b319,0x297470929d7575120c18,0x5a14b40cd2b8ce1e6037,0xb364f354e1e387447931],#[0xdd62b30aa42fa6634e4b,0xa1131c20e1542e4704c5,0x2d0b1a28e8e020c34ca2,0x47448aeec97b9d903814,0x8aa12a1bd41ad0690e65,0xeab2b88aa5450e53aec,0x669cf962b289e359657a,0xcfd285769e0e1c9bfa2,0x62542cbc7b2ea0531397,0x71e5dab253b302044ba3,0x15069a91da605184c848,0xa93f1f6ca494945cdcc9,0x88cfd5d96b7df2d25091,0xf24b5020039a61281dd2,0x59a7a05cecc078e1aa1b,0xc308063ea08b4a2c3508,0x1113832afe859a79d620,0xfa85966558acb2aecb66,0x84ca31e1d699584a2c34,0x59628616ed7da3910779,0xe98a41851d0b1d25d0d6,0x10e140bbae161a4c62f2,0xc2dc2fb90b069b1c1958,0xb2c71b1541a2e28d3ed8,0x1bc818d2bce4a6983e3a,0x8f015d2bf50eea62a139,0x427306daed9855602c32,0x9a79d088d333071619f3,0xb1fe5b6994836aecb985,0x2c8c2ec88c32734edbcb,0x28798020e118bbac5659,0xebb56efd619483810394],#[0x503d62b2342385a88b22,0x9b40196160b0d05d5185,0xa58b256e446805590b26,0xd651228aaec893cd30cb,0x2c97349502ccfac06372,0x5de24bb30900612be62b,0xe6be58ee62b2eb1871a6,0x32ea59833a53cd98c30f,0xa1c2e5cc30ceb7e5d355,0x4404aea039712ec7ea13,0x680f0f35461960d0d6cb,0x595486a16bb6aef65421,0x4b92884ea2d96a30c3eb,0xa5214b41960a3a580a19,0xe2517576859d2a026b65,0x2ac28807060e0b70b506,0x6599838b0d0cc5576512,0x32f21231c30e0c2c44a1,0x1dbcc3c9f125d62a3435,0xca9867891f2c2b479654,0x342c1286a92b54eaa3fc,0x6a988c8d9921a053661,0x6a56581b823487a197a,0x1a7417d45176414e1d0c,0xb76610b0d06a0709c69e,0xa9ac71619f44f2a194c4,0x15832ed40d3a0bfe2fb,0x29d76570abd31a6c2dc3,0x50e0cf6605371434b00,0x8589655425238d763760,0x39c6176534e0c2c1712a,0x49ed331e63ea08965aed],#[0xb661512234f0411fa003,0xe6d9c3837d943c06aac,0x1d24b48928e26184270b,0xcde5921807b52ebb5331,0xdacae9153a070e4351a6,0x984c0a9d0424e15d24b5,0x9a6a7dd964896ea61b2f,0x349ac85b3ed80d422fba,0x877532c1cd2892c465a3,0xcb3bc05e961f97b06923,0x3f72b0a22a8780d85ad,0x25560ca9cebb1e84a69,0xc2bb567016188762b2cb,0xa470f97302a91c9867e9,0x2b93ed87aca17b9e7afb,0xaa25c3020fb61aef5554,0x4569d3f2c7411d386a80,0x75174395763d62450b12,0x54e8e0c9c0515dd94a1a,0x3070605f631b40c73159,0x31b4d624796581cc8d21,0x996604e4c2bfefbaa64a,0x345847e98125228194b0,0xa05a7419b45176815c2c,0xa1d10a89f6b25c8af596,0xab05510161e6272743a4,0x896c04b402748576a11f,0xb14b5644464339a6d12e,0xe61d30f7125d8d9662c2,0xb5d273656e178407a9af,0x46c53099660e61d0532c,0x610dabb21e24ea4fc2ef],#[0x2705d8e16132cc2161a7,0xb200ea85a169650b28e,0x86014e0cac00446999a5,0xa5a5ae9a3336aeae2287,0x31b5092a1d609c98a51,0x9a3608c7d423e086985,0xcb256446901c892ecc03,0x53b8932a03b8d800358a,0xb38697431bcbb4390c9c,0xf7c2a1684e5ae21a3417,0x545ff90ac8b44b7a0609,0x9a1c3817d8b5d059aac,0xa4ec1aab2da859c62f3,0xc265a395e4a3a042ea80,0x303114b6a367225ca322,0x695006d005e7de54e738,0x3cb4e5b5792d02998d5a,0x4272d7242d972b0eacac,0x5758925541a691965036,0xb2847064f450b74060b9,0xe05bb2e9abf5649522ab,0x1c18177594b85d6e3650,0x4d34464ae903871b0c0b,0x18028bf206b9d56587c7,0x5396da65297c9863d0be,0x1b2d004c34e82e980f09,0x7e5d3336b2a1840584b1,0xd601c1838322ac3120b,0x43a5ab229a476a40e70b,0xa1650ce892ed032aa51,0x7350219ad50095c2d449,0x8377526a9bbe1d699610],#[0x19a44e823e29746e41c1,0xf2434eb7c2f86d5943c8,0xc387a422fc81a805e990,0xcc00e74652c725741af3,0xa396172864407879894b,0xb9b5852d244c1a6a58e9,0x42c0a6ce3e920162aa2d,0x64e00482214f414a11c2,0x196a9d766e488d3b1c70,0xd5acb9e3f0161eaf3ef2,0xc55954b42747820e9a63,0x74d338d5a84fe3cd230c,0x66e9a4c30fc26e98fa1a,0xd1205c6b542143862737,0x62f2ca51c031d296ecb2,0x1a40dc2dd069f1b5950d,0x8deb0ba9ca6892ea83c6,0xff50f42c6a4131c1d084,0x12ba90d602c24c4a7551,0xd31b2706a0f31434ba2,0xde7023494e44974320b,0x1875a573cddc0654706,0x4d0cc044845d24e38543,0x1659970674005163a4bb,0x4d61261657fa2fd0b2aa,0xcc602c3d2670e05f11a3,0xa2ae98f73835105829a0,0x92eae329f766e4daa004,0x736a4d6d486228e86033,0x9ec2659800734e8bc6d,0x5536ecdb46376599c3d2,0xf5a939e315491c3069ac],#[0xc001a8e551c52af446a9,0x30091f2c5d4b590365c7,0xf2438151a2dbb208c269,0x30c2872a56a4160b7537,0x9c5cc02f4a7540583af2,0x8e328910cae2bbb2ce94,0x5943549607060e1b472a,0x666816f3830b0d9b5857,0x34d26385a73f928b05a6,0x6318ab251b23e18a822,0xc6a14c5a487942e0cb7a,0x656ed75c0191bc5acbb1,0xe9790147bb2ca136831e,0x166a246802d2234d51c2,0x292c3417e059a79f0a7d,0x25a513556ba8e86e603,0x118e9530e829855a20fb,0x60078aaeca4285739f8e,0x57913a665448d0058a56,0x12118e0e706574565b2d,0x5695c450f2c0c8d1a0bd,0x4142929a90da1539b580,0x78c2cd2ea444e99942db,0x75596178a323b89cba0,0x1542c1161a6bbd8554b2,0x96661eca83d647e900e6,0x288a1e505270b5107287,0x6892ec83379767a8b6d3,0xad73518b6d32ae28e874,0xcb4b930e82b06b30e732,0x112234e84286a39fcda,0x1911a66499739cf647ea],#[0xa6d48c2186995d52aebb,0x69afc2c7531c28594071,0xc0e963a4be62ac30da58,0x75f7d25e5155d92b50b2,0x369a5b43a814e259637,0xf3099299512d14ebb2c8,0x539e30c287070a45dd5d,0xc2e7e103870b082a3797,0x3aacae3911a902126b1b,0x1714ed78a8e80da54221,0x1b040a6835f4b6eba043,0xe7bb2c2cc85734d985d,0xd1a79296fd052b17e86,0x3d11f8a1a859b616e980,0x920331f4c91125a74e9c,0xa6c96a125218b9a76a5e,0x9c3c35465b6996789301,0x8e92fe70b0f24961a6c0,0xea38b15934e596cbacc5,0x8a602d359723e435b8d2,0xa63692a750b473fc4b76,0x830c4f28596341f6b25c,0x516b4e2cb3f30b65e409,0x99112e180150f2ccaaf9,0x22c7417396da658c8953,0xa7a0c9942ca156a5e536,0xd2bdd1268d898b942df8,0x61b2c3418129d647e818,0x9ca2814ca24b20680c69,0x30c286aa6591f32274c2,0x619b650d433fb8d8606e,0xee9a877533c18d00348d],#[0xc52931d3e8e541c44a32,0xe46f473f41008d1a0b,0xb4eeabd986255d1d0c23,0xbba5ad22ccc5e5d3404,0xde702860396ac8910d3a,0x7c3206fc4b86d362ebb4,0x387a514ea81691965035,0x3244f7aa4597dac970bb,0x3923f52074b5a41ae02c,0x9c98511850d39be4ae98,0xcbac3ce15d8fe47aa6e2,0x51262c749a7089a0cc1a,0x8eb2da69cc89d34132d6,0xe61d04de47680153eb01,0x86174096ac88d407a994,0xec863c940aa624bac0e7,0xc9631bb28f18dd88770e,0xb14a44b28aaec8d8e7a0,0x2f3098b2976bc1434bc7,0xa5058e0c0e5044690ab6,0x2cf016a6537b2cb12449,0xe02b4ae3a85941518acc,0x29a80d596cc2cc70e15e,0xcc01123e40d238062ee9,0x62638b43b93878405d42,0x7089a586928b2968da59,0x88b251470a05f638702f,0xe60da31b4e933f574a75,0x925a529173176b2bb08b,0x50dabb366aa6860c70f2,0x79595c63872ba248271a,0x30aea211a9c414e538dc],#[0x6c098948d98166a2de47,0x5ed95832602b4c883099,0x2c7456629964c8602c35,0xb73905ecb29ece6945fd,0x4b0e5b6994e392ecaf44,0x3462b28a02258476d42d,0x405a61b04cd0050d665b,0x5d04682ae9a250834ba0,0x942e383000d29d5411cb,0x38c4ba16242cd298c036,0x542cc1885be994a3334a,0x1a8da490b4aaab0aa961,0xc9711c1857b8ead49c6a,0xae942d0b488954dc77da,0xeba285c05df2c390d1a7,0x830d15c618621a07cb0a,0x6091260c0aa2e36a0167,0x62898595ff642c6b2a4d,0xd90acb5b4c3a0af909d4,0x63a4300e2c864e4a6903,0xd3212c56596336f0cf91,0x353421237905ba6c0089,0x5913a433942cb3270be0,0x50a9bdc636992650b2ec,0xe818d70aed52aed50769,0x12a8553775caba9ed18,0x8a5ad229a74592c801f4,0xab500188932387315645,0x34cc9913a5d89c2cba18,0x69b9cfc83facbe827722,0x3c75615da5db488bc517,0x4a4c750b858405e60d31],#[0x9a5d8d84ca31d175da6d,0x8e18a168da41374a2586,0x9970b2925817a571d081,0xb1691a115ecb51844699,0x253948cb6524d0634b05,0x42f282462ce80da697d4,0x589f585a818b49d0901e,0xc30d32c44a6a43c80f4d,0xa60d541a34d34a1d9844,0xe6d635970cb8fac2bab2,0x3ce0c2030c25c301852,0xa965d7404e2ecdd29598,0xaed613dba61c00ad343,0xa41491c883cd1ea85887,0x88e6b610b6622218e913,0xd70b4827c55a14a41cd2,0x2da76f9b5c86451261b4,0x40e50446823f96b42ce4,0x90650b2cca38775324e1,0xe9a2a93bd4ac8b6912dd,0x8b51a5a22e950335b2d2,0x69ce738aec13929a80f5,0x6f735f93cc108d4600de,0xe0b0d000d016124d544a,0x47e8b3396b210348ca1c,0x106fb28580da108c9e22,0x6a2a28bb2ed0be5b5d38,0x36c55956401b4c78a198,0x3eb08f046e736a542d0b,0x1a4a690948deacf591b0,0x2ca1e501750aa80c14,0xe531f41564b7a448632d],#[0x210a1bd601d30be72e81,0xc3068f0e1b578932787,0x52a5892c9602a9a15ca3,0xb003da672e25b9c84fbe,0xcdaa0064de592c996743,0x66940c32b40d5c057494,0x4844349951c4d6cb9d61,0x88d43c018f15a9c8f31f,0x6ab6603e36b2f2c3f595,0x634c0d1c1a843a12b8d0,0x107dc9ad2b93306187b0,0xe1ed74c330892ca0da9d,0xd8ab2a4b031a5439f749,0x25a67e094d486a18e9a8,0xd3108c26518b423437a8,0x11752281690a3a1804c6,0xdca9834d18ab2ab0bb59,0xfacb550a1e50ca71b500,0xe80530b34f4100fa63c0,0xa59b9f92771f7c2a0e44,0x4a5ab228e58e8f030e34,0xd26a465805503c9b980b,0xb289f96da6580e3c3640,0x62650818e10e15d90c62,0x4084e624952aa8f3adf9,0x23f4e04abf96b3d4cb26,0x5652554b5482c3469ae5,0x206b1e68d885194e4948,0xca2234d569c2837da32c,0x287a70122abb2ae44690,0xd32b318dd9226caa30d,0x4d393bf26763ed91c3c3],#[0xb7b8d80050d6c351ec5a,0x58ab2a86fb6000665343,0x2a846e46ac8d71c3318c,0x200cc07a6b2cdabb3d2d,0x6e996cb54ec565d3450f,0x297e9f7550b2cc91f586,0x574a7c481a0b4157cc07,0x766b9f718e1f01692531,0x4420569a1536b0cfd9c5,0x555b22a346da46a1acaa,0x391071e02c1d88a14c5a,0xb22cc05e95c437752f82,0x24b90d269b463a065a5a,0x538584339e1cb586e169,0x96ca54e70ea60150b4a0,0x65cdd62b274228910915,0xc2abed878a52ab05a4e3,0x6542cbb1e5869a292234,0x26e9a5945b078d3dda91,0x2e17d98da6abe2abb2b4,0x14b509d0e18aa5461b61,0xd07d6172f612c980317a,0x2b5271a85a7dbd43c06,0xda761942a9ae42669ce7,0x254626e94fb62d4296c2,0x8d1434ba2c07839aa24b,0x927a8100fb549cea1a85,0x6d2552706a20c62b4946,0x14f39854235a95400685,0x9f9b5643c495d406a706,0x9c3c3cca5be994416b41,0x559165532ecdb479658a],#[0x2ca3b6950868a7d16cec,0x144eacac2ca168d9b65f,0xa1e58cd80f0d53b8796,0x1aecaea9d6446201cb0b,0x9687197b86002a69a555,0x5e12169d36472c88c9f5,0xb45f4901a85a369595bb,0x957688d4ac9b6880e4ce,0xd3808206947438102fb3,0xfe0eb4c8aa85a967d42,0xec49a1624e4bb2330168,0x61cbb5130e826438322e,0xaa48329f459f44976605,0xae9025a67d51cc2ba4cc,0x9996b9cf28e6054c0eb4,0x30618815a5539e30b74b,0x34e8bc09a61791ca838f,0x8214b1d05f05b699424c,0x38abe82033870a8718da,0x5eb0c40286a3694e8b25,0xd81c6a42d1a6cfce1a6e,0xc06e706150e6f2ed0a22,0xd8070d368ada4b1e31c,0x411643d0c6d42488464f,0x6b9cf7125941689748cb,0x15e76f2c910017a585d9,0xb0b13975b5a2aa0e8706,0xa30bb23444e9ac062aca,0xb6987385d2e563f58652,0x2c71315944f51dd03c83,0xc258acb2b434ea2ed3eb,0x6da541ed427437ac03a1],#[0x8350b925961ca0dcc3bb,0x73a9e25bb300c56615a3,0x3e8c8595b0682a3b1c61,0x50734aff2d2a9ced4cb2,0x2d96b11ecc1a6ee161e6,0xd34f101e0e933832ba23,0x60352f2c0b42d768202c,0xebd95087943d3ede7068,0x8d0e16bb595cf4b2c2e,0xe9e664e32f46485a14d9,0xc6f299765c4b0d300c34,0x596cb222705c69e70ae,0xab5c5465b1434a913a4b,0xf28feaa5766c18acbace,0x462938baeb4d865cdf71,0xf69354de211740123099,0x20b4f42c07849899618c,0x183d022950ad87161aca,0x1c84646f27db487f1e,0x1e01b4012cc3a098c8fd,0x349a91dcdbca9d22c696,0xbd1dfcc2285821334d2d,0x143e38f0cf996da6568b,0x94bef94929c2ba525186,0x40cd2b8ac55915d8ab46,0x86189b62acaa4c85a44d,0x2a05889a5884e1c0e512,0x551fab058a6d5d8e570b,0xe0e6a0486b2a8f6b1597,0xb0f5e1b596391c8b23d,0x31691e8ca1bf18dd9268,0x5e0fb592a5612a2da287],#[0x73af2a74211a3c1194b8,0x35a6b28e1c8bba2669a2,0x51b3616694c501b52188,0x71871b0e6d4497536943,0x80f5a772602c3cd4846a,0xefcb0b2a75d9498f2e94,0xe89e5892ecc1aaf940e1,0xd381af9688184ba4e870,0x1050d1c092d50e6a7e30,0x18dd91a975424785ba00,0xb3014bc6719b11ea9b8d,0x6b0068d25243469e6835,0x392e618820cb4cd8911a,0x6c34e6fb16a94d25ad1b,0x9866e4e3d0c1e0868245,0x36010161e4d04b4cfda3,0x1e22348674119037508c,0xa12a1c3117d268e09e80,0x8d1b36636924d96b4888,0x10b590ce29b29910b4c8,0x83b31402d5c7ca3ba866,0xe8c351d155d92f48063,0xa594b323f45b3461540e,0x52a21c3957f52ab0652b,0x59995b85d72fa0d1f62d,0xe90e820336aeae3b2d96,0x534ed42f9656c453d33d,0xa644942cc05424e80218,0xb04c56a5349734a4d96d,0xd8a342b6235866d585d0,0xad5211e30c287b186188,0xb23d8a1cc5a536aeb0ba],#[0x167df086403ba6111bc,0x1c786c85cfd11f0e3aa,0xa9d0384056a32f5e463a,0x65999307469e40783a9c,0xcd8bc940b1c18d2030a1,0xf5cca8e8ab4e5b59522e,0x23a84a694542378a1a57,0x34d634056494df6cb495,0x66acd0cac35145d97002,0x5e1d69964782c961949a,0x1274c804537641602c25,0x5a56e62548e1c0368032,0xa55f0160eaf1bf467cb1,0xdc50b52d09e56571596c,0x1f580c78ddc065244e98,0x2c3d680c696225eb5040,0x46f231348552a95182e0,0x9457764ae24d282284a,0x54ebb286cb5c67b23f40,0x40c4ae253501f44b8000,0x4c09bcd537ae2abb29cd,0x458b0d340cafe55d023b,0x6b65929b50b282931564,0xf0f49c31765410850e1,0x937f647c3154e6546008,0x3dcb45da753eb018e1c1,0x26baa6f6c56a14a54aaa,0x11a9c64e3d0af06d619f,0xcc26921a0d3651aec8b2,0xd2d423478291da004d8a,0x2c4b802fd1cc2b9ec568,0x77d0381165d90462ac8a],#[0x5929938263a542d64a91,0xa6d18fa1a022abb2c723,0xa22abb2c0d4544748f2c,0x875955e02b4cd9b59753,0xb2931071a0d90e048bba,0x388946bb28ac55915965,0xb844e8d9655b281eaa15,0x55b301cb14a14b5e0cb5,0x5851c542d195f15a8d29,0x22bcd754e210eb4aec41,0x4d62f2ca4011a69c91cb,0xb159854970b2ec712e03,0x1c1ae4586990651aecac,0x816e71f0c0b407a61b0e,0xcb8d3a0bce17b9e7666e,0xa31cb068c228d8250f2c,0x365d1350b00638e9a84e,0xd90c4ba465458d2c2ca,0x6214353949306189a38b,0x855e9b5c1434b0247aa3,0xb080e42573a0df6c35f,0x9580a24d3800ac545fe7,0xe12d691478a54e501c1,0x97b068fbed93c3ca9d3,0x31a53cd43cc1885869b5,0xba9d4fb0c70f0734aff8,0x368aaec9721231c20da,0xab797638a28d0da8e766,0x53d06481669e7d427237,0xe925365c633db1598448,0x35ea8b81cad0cc34e301,0x6cdabac3e58e90037e2e],#[0x54681c96b34877911a73,0x34a1aa7950ca90ec351a,0x1c2d42cbb1c58682ef8c,0x506b654310674b05a12a,0x46aa2e23eda992a1553b,0xda0050dabb43a44e9758,0xb102a698f7732a2fe91,0x6f62b2c97c0576ac63cd,0xd1a4a99ad38e3f0061a,0x8d20a88e615d814744fe,0xc67b423237ab8576aac8,0x53cc1a61ed42b9cf4cb9,0x91ac2966c46597631b4d,0x85d9472c34c613ed7492,0x5328a1396b862bbb2c71,0xa25c2d4054a25d29b023,0x8aa545e790ae29b21986,0x732d2b18fa0981cbca3b,0xa738d8bd1a5a63e98874,0x54609682d37aaa30b099,0xa987415bbd976ae489d3,0x577646e16b2582a16599,0xd004130e989e3a35328c,0x299983084e033a54384d,0x2b859413e25ca069175d,0xacd39c7175d2be4272d7,0xe8f326f2ed0528550069,0xcae18da4abd08d0e18df,0xd26b048b12600010eb4,0x21619397f7477f83ba81,0x2c8d91d794d0458d2bd7,0x37a2abb294ca650aa47],#[0x5c4f693548934a0dc059,0xc34cb2911a665e36b2c,0x5976288ed482acb6595f,0x2ba87d615d973b4e7a28,0xed3ef2ae7113a4a9176b,0x1c283774dbc33f622695,0xad32f270e1c0c70b0829,0xc59d23f4c06a87966500,0x2b911a6985acbabd7040,0x812d2968b6590b581b2c,0xb5da4a96b48af969a0b3,0x4cd7b8fa23ecc6d2588f,0x10888d255ce15d2bb02b,0xe7d65a503ef2ae8a8d96,0x874136c5ca165600d30b,0x940e0d0cba04c2a8d829,0x45844e9c033ab0cddaad,0x770b2e6f39a51d1089d3,0x93a00ae31cc068446901,0xb0bc263e8e8053f2a228,0x26201b4e76a95a906d26,0xb00fa53ca42b22266369,0x75d29ecd4cc4ae8830c4,0xe903a8aaec96486a14d8,0xb5cb0976bec54d344a4a,0xa26140a60b4683367eb4,0xd661f6751aecb134aa91,0xf414bb09a96154cbb36a,0x80d25ab224d185d2a728,0x82686a4ef70b0c6e4619,0x31b508fcb56457d4ecb0,0x393d11acbac2c5b6991b],#[0x1ce9c5d9b880f41719c,0x2762f2ca2111a60d1fad,0x44aa362602b29e826e9a,0x1d1206a75d5d87db286f,0x32a8c2ecafb32a1249b,0xc3c0586b1142d0cfe6e6,0xfffffffe7064f4450d52,0xffffffffe001ffffffff,0xfffffffffe081fffffff,0xffff7fffffe101ffffff,0xfffffffffffe181fffbf,0x77fffa77bffee1fdffff,0xfffbbfeff7ff7a27df7d,0x5ff82e9ff,0x35c0,0x20000000000000000372,0x72000000000000000037,0x37200000000000000003,0x3720000000000000000,0x372000000000000000,0x37200000000000000,0x3720000000000000,0x372000000000000,0x37200000000000,0x3720000000000,0x372000000000,0x37200000000,0x3720000000,0x372000000,0x37200000,0x3720000,0x372000],#[0x37200,0x3720,0x20000000000000000372,0x72000000000000000037,0x37200000000000000003,0x3720000000000000000,0x372000000000000000,0x37200000000000000,0x68298887c19584760838,0xa5cb15364b510be3a08c,0x94822847f91de06fd19d,0x9eb03cb7b2b9ea592752,0x5be28eeeb912daf34cec,0xcb99241468712fc2ab02,0x9855d5552d4c850e539d,0x2585d5fd37935cbf6e65,0xfaafe9659f5e63f93263,0x1a89801c34ef41b63ec1,0x7a288b000db5f26cfc58,0x1e6820068010672b1948,0xd13a69230a800d4642a9,0xb264e85c1b88400ec67a,0x965ab0fe62238c400cb5,0xe9692c900652206800e,0x10075b4958802d0a00,0xa400ec68ab524662589,0x28078010473b414e7d2a,0x6a2988000ce56a70f66f,0xf0582689c01016ead512,0x7d1064240a400e461a70,0x1a74cc561f86000eb602,0x7803094689330d000ec6],#[0x12881b5d426d2107c011,0x4010d72298fe74288b40,0x89400ef642a53c7a2809,0x228a800ff73ae93e812d,0x7f290b0010f7231d4069,0x4a812a0980101732fd46,0x8d0a6c1f88000f666afd,0xe26502611d058010e6c2,0x171af1085e1a06800d45,0x11e7fb896e832b8bc010,0x107732fd3a73270980,0xa400fd712f11c712007,0x2b89c00d560a78ea6727,0x551b86400f670af5107d,0x6c91358b400d25ba40da,0x415a8a360cc01137eb89,0x9c2da29e2c8ac01267c3,0xc75b1142812588401589,0x1046bacd2273228a0010,0xe261ab1286c2707c0,0x7400ec65264e64c1d09,0x268c400fb6aad4f8511a,0x2e1105800ef722f9346e,0xe04a138640084361387c,0xe8b83b1707800aa481e4,0x1220dc572009c00b2489,0x95d248f45d2388400bc5,0xb451a0ce6531c8a000c,0x4008d3d98c8e2e0f8400,0x83000b94fa1cea4e2006,0x18880009f471fcbc4e16,0x491a85c009b429b0a245],#[0xa03f1884800993f9bcc0,0x50e6632609800843a198,0xba08e6521b87c00bd5a2,0x47c04143e0012c00c05,0x12e1005404c154c240d4,0x16181200ac1120540db6,0xc1c0c8049e100b08b3a0,0x2400d0b064e0ac6200dc,0x87824c85684781ae086,0xfd077a0781406c8eba1,0x47c08c7da18488844834,0x44ac4b1e090ae035c1a4,0x28ba0907830304d05542,0x24c8803b045227417218,0x80780cce11c1624f608a,0xa15c07074c39474439e1,0x761889461c093214119,0x410084c068469827a0ee,0xa4f20d610e160c941607,0x4d24e23a83584c11c444,0x826fc008ad85d04684e4,0xc040bf60481d444c080b,0x1e03e100840e4c18094,0x445508012941ca2046ee,0x844c0142066503403e09,0x30e1a26d0cb0ac8c9201,0x360143813c85f05780c1,0x6e08e01ec146024be07,0x4ec04838037400000a1e,0x6476616a0d45e0826110,0x611096489616c08c3c43,0x5845e0440f660128886c],#[0xc0b660a61a2ae289c008,0x6e43e46b05a41e40063,0xbea15400e08c40c4c25f,0x5820114c7707086944cc,0x2acc6ae1960225402c65,0x48a8802b80487c0c0874,0x24201456094bd87448d0,0x210a0c23b00c064628a1,0xde0c10608a090c15e05,0x528467f40a2250e921ae,0x8888820b242e83a4ad66,0x36e144948e160586da05,0x94098e12412bd06d45a4,0x4ea1a48d85826a223c1,0x3a80607aa040a1488c5e,0x4284c1043ca74a3bc0d8,0x47044242583440a00a45,0x68e02201c0888c050080,0xd468a0047805fa1a2768,0x24066d01e85480808b08,0xbc404a614184ec4c0e04,0x220d255a0a8202634044,0xd08946d80406015926,0x7c80409c66181927cc61,0x80d81e40a041a1241a4,0x4ffa0421c22b3ade40a9,0x9b7300a3bbcd530a900,0xf04f4ba7300a3173e2c1,0x814805de9693d4a02dad,0x4b42dbe5ee17a15481c2,0xde4327b4fb0908027fb3,0x76dc54543330f11a10bf],#[0xcda8bd3ea42b7e00c76f,0x442bf72311481dbe0058,0xdc106806be390a2afe94,0x7be5041cbfd881670bed,0x6fc8cf490a1ede6d1142,0x9fcc645698307b2de880,0x61f2ac665ab99e00148c,0x485b633bc8982525460c,0x10e9f80106474a642a4,0xb1822a5302d47ab242cf,0xb946876bd13cdea2cbc5,0x98251abfd8c410a1a6d0,0xc5925c4483cfc40190ef,0x6e8ae1000a7aff7858c0,0x22e031c96a99df1041d2,0xa4f520dfc43a9d10ac30,0x50805343bbe84042a5ee,0x4052e9f0ed09486737f8,0x48c707e692e5251e4c4e,0xd464e9798051cf010e3e,0x3ae68343f9550948667f,0x199a23b229b9c0e5352a,0xdc5083b18d1247fd299,0x97fa0d0adfcb024666f6,0xe2c5b0ac09f516867a60,0xc19a44003fce6142d397,0x4617f51021ca5db5a251,0x868601de32b553314b81,0xc07414de284403d5e685,0x7c42fbc3436bd161610f,0x9d7b85188a66ff426642,0x6094b67d2128e0cd2225],#[0x8d098f8380010bf7a5e4,0xbee8b950e000d1b0ff63,0x614efa394f52000097e,0x9524ecb5f61a02a66fa2,0x119961f410bd42b1f095,0x2846858ff349713344bf,0x4db900a3bbed01466ff6,0xec4e4255eea25bcec80a,0x16d8d0149c0bd100a527,0x603991489ef0fe35a152,0xaba5245f588ed27a0a77,0x931a895f3700d50b875b,0x529888797dd807c3a687,0x3c8906f716a22935f364,0x7480d0945a253897a325,0x1672682344419a44a66f,0xcfa340525df240a3a76e,0xed204ed0f444a1ca2a96,0x436856836f3a8d114cde,0xa49bcd882527bc3c2921,0x221b1e3606297efe398a,0x880a4f68005215819615,0x5d110e06a82bc8cde54,0x52201dde952cd29401bf,0x52818747100a533e711c,0x405666610d49b35f290a,0x914cf6c8f3526dddc0a3,0x9eacd0fda7af42659e28,0x428a57b184252005f8ec,0xff04a02296de2241ed63,0x450ce45dba3257b1318d,0xcdf6129010f041f434e4],#[0x84d48061deab56cc69f4,0x40bb094a2fe0a83bbfa8,0xe62fb4a88865e9444a3c,0x5c9f306e295ef0b300a4,0x452343c8b259c2300d21,0x611050a4f97a0f4fc3a0,0x110002949f2430885e7e,0xd0948f7d592150a523fe,0x9c254ad8144f058477f4,0x75322ebf8e070a176f84,0xfc0b42429538780322ff,0x42a1d2d6faa398fa2275,0x7d3c46cba43dbfa03d04,0x92332d181452ff810605,0x7c8030f57983026237e9,0x40c7b791a12917a51133,0x5907d9a44dbf8109485e,0x840292af1a5000a580c6,0x85836be8c22286a7abf1,0x92b0de798051dbddac82,0xa92dc688367d43032a2d,0x9803be81d2a946ff2ca2,0xa248542944f27020391a,0x50f85edd1901fb0106d7,0x27e58c152630ffa38508,0x6ce064034877f7e10548,0x111f762284a7e3cd0021,0x6a1eb780018783dd040b,0x806936e4028cd543a733,0xe51f3e3fe8c40a1b8e11,0x2099a9f16e76428653c4,0x4c5b35440bd8083cfb41],#[0x2922083aed0cfed19b6,0xac214b038f9231cdf184,0xed920a1ffacb425bcd93,0xcf6026263fd1487865a1,0x4949988e6818be929807,0xca491d329ab53a024c73,0x586a87ae682bbc2580a4,0xe9b1a38ff24993f7c18,0x189a741b06923f118f,0x54a5d311a0ee83edf30,0x28a73d64a2aa32ff0cc9,0x13d96a92afc6100a4a3e,0xb5ec04191999992152f9,0x94a6564e24e3286d30a8,0x3530a64aa53d9fe03857,0x8079d3f6912f300a3c33,0xa5b9e18200c42b255814,0x958ff021293afe858100,0x9fcd04a894b07837222a,0x87f780505bd957c3344a,0xf34e841538bf75302e42,0xb0949b7fe81094926505,0x17478c0187da618e8f23,0xf0cfcb8008757819938a,0xd27b4002928fca7a8ddf,0x54a4be480c32f1e4044c,0xa3cfe13228666b9da172,0xa2dbc9f849910d17382,0xdf2fd425a2f6c509b9e0,0xe0391641bf558bbed2aa,0x4018fef01854ae7a1728,0x370acceffe12923fc926],#[0x3ba4a61d05099a770817,0x34c2a2d3a9104a442ceb,0xa9d5527bf21042857a81,0xf8e10c6ffc3160d0c17c,0xfd808363ffe982a4261c,0x4c854b4fc0083833488c,0x687cb6738052aa70bb10,0x41d33712a90aa7ef014,0x82c9cfaa33088287562f,0x3f0040296bfa2d0cb1f1,0x737324216ce742529006,0x194147b20810f041a024,0x3090fc03a3f5c1f1c194,0x2a486071b81c51686960,0xe8802b700cf75260d5ce,0xba307b9fc1c4601c4665,0x67ee8542758777054c55,0x42f9186d7428acc633a3,0xe2b08070fb97626c7840,0x56f7985672a8a83bd146,0xc3570414b601c533e461,0xf64100045fb7490a9bae,0x60713cf2a8a0e601468,0xc156a2c43844708956b0,0x8f28561c861dc563c13d,0xba3e4f0d4c14461b7018,0x8ac23844708a0e868c55,0xd17c34b018525cb74733,0xb11bf80c604dfb9bb752,0x118fe35266c2abdcdcb,0x10eab00e2f3caa2aaf84,0xfe0c30ff61a9b8764332],#[0xb11c2200d3fe61eee08c,0x8be4daa30053e1aec4e8,0x2c7e9907a834d105cde1,0xb95453c21699545a1d1e,0x407028b98e0aa1bc0a37,0x207028aeb00e2f3a1384,0x58de1cd848e6a1d1df7c,0xfccc8d0fcb830c0c9814,0xa8d5200045fb749af1f2,0xaca1c3d5c1038144071f,0xe18bb20c024b00b78703,0xe78b5060b5385f7e1c28,0x93ec4fa68b4353a48dc3,0xd4fa7100402000c7]]
def g251H7 := limbs80 #[#[0x26181155592442a842a4,0x1140920800159449546,0x1446a042201940088a0,0xa401124a68a9a250a822,0x6986064010891418400,0x91140612145941452682,0x6289580126162445099,0x58411292508022680502,0xa4109080654880098560,0x601010a2040082200a0,0x16088886044226020224,0x98295201a2600626854,0x22645026690924054491,0x49920628022ccb936870,0x113ee14a50ec2d346607,0x61c01795a5c0d438185b,0x844683781201979294dc,0x1881758c6c9cef0e8cd,0xd008c451e47601527326,0x40000050057da0350883,0x20081309420001014120,0x1928320040800802410c,0x9c090048401058c0b0,0x28858002b00020825043,0x823300020070410c81,0x2c02001302032009903f,0x5720048842820b00a21,0xff194000000000000068,0xf7fc007ffefffffffeff,0xfffff0f7fbfffffffffe,0xffffffc7affffffeffff,0xffffffff2e7fffffffff],#[0xffffffffdcf9ffffffff,0x3fffff7ff4e7fffeff,0x17700000,0x660000,0xf6d9800,0x8a108000000000000000,0x300082b030084000000,0x1504000000a0040011,0x1806c6008e100344650,0x4002a0123002101069,0x8044000de000a0802429,0x8b0410280010900,0xdf53a9b0512400000000,0x631f912efbcf38c26dfc,0x6f588b60990af083e2b8,0x221c9e66db572fc6ae1b,0xfee2bcacb84acfac250b,0xa238a930bd2289c6e01b,0xa21c3a4ea56a185350a,0x9600a361fb3674c7a988,0x2e7692e25822d28163fa,0x308a]]
set_option maxRecDepth 32768 in
def g251D8 := limbs80 #[#[0x54831591520c55454831,0xc58454831601520c574,0x591540c78454831e0152,0x550315d5540c57455031,0xc78155031619540c576,0x61d640c575590315d164,0x5c031e15640c78059031,0xc5645c031551700c552,0xe11700c5855c03161170,0x5d031591720c5545c831,0xc5865d031615740c580,0x54831441825d43160175,0xc51059431441640c510,0x441840c5106083144173,0x5cc73441860c51061431,0x4c11020530440314c110,0x442614c1105453044141,0x5494044151501100c540,0x50110585404415450110,0x44165501105914044163,0x6154044183501105d540,0x50110945404418650110,0x4414350510cc54044261,0x59541441545051054941,0x50510615414417550510,0x4438150d105914344386,0x5495044141541100c550,0x54110585504415454110,0x44165541105915044163,0x6115044183541105d150,0x54110905504418654110,0x4437454110cc55044261],#[0x54d514437654110dd550,0x54510591514415454510,0x4438654510dd95144174,0x58d52441545491021d52,0x54910595524416454910,0x44181549105d15244173,0x61952441845491060d52,0x54910a05524418754910,0x4437654910dd15244287,0xe05534416354d10e0d52,0x551105d1544416455110,0x443765511061d5444186,0x5d564441655911054961,0x59110a05644418759110,0x4418159510dd16444287,0xa1d65442815951061d65,0x5d11059574441645cd10,0x4415290510e197544386,0x61e434418090d1059241,0x98510592514437690d10,0x441539851054a6144143,0x61261441759851055261,0x9cd109ce614424398510,0x44152cc51050f3144181,0x5973144164cc51054f31,0xdd1105977444373cc510,0x44185dd91060f7644185,0x54d514c54354531a0f76,0x54531591514c55454531,0x4c56454931551524c643,0x611524c580549315d152,0x54931a1d524c58754931],#[0x4c78454931e01524c775,0x61d544c5865513159154,0x58531549614c54358531,0x4c58759131601644c564,0xe01644c77459131a1d64,0x94531e01744c78559131,0x4c552985315d2514c564,0x593704c561dc13154770,0xc5405483150180dd131,0x501650c5405903150154,0x60031501760c5405d431,0xc54061031501820c540,0x501514c5406183150185,0x55131501534c54054931,0x4c54059131501614c540,0x501764c5405d53150165,0x61d31501864c54061531,0x4c54094d31502514c540,0x503854c540dd93150375,0xc550503874c540e1931,0x54140549505013154140,0x50163541405855050154,0x5c550501655414059150,0x541405d9505017354140,0x501865414060d5050181,0x98d5050261541408c550,0x541409cd505027154140,0x5033154140a0d5050281,0xe05505037354140dc550,0x54540551515015354540,0x501645454058d5150161,0x6195150176545405c551],#[0x54540985515018754540,0x5038654540e0d5150271,0x20d525008154940e1d51,0x5494058d525015454940,0x50173549405955250164,0x6015250176549405d552,0x5494061d525018454940,0x50287549409cd5250263,0xe05525037654940dcd52,0x54d4058d535038354940,0x5017354d405955350164,0x61d535018654d405d953,0x54d409cd535026354d40,0x5038754d40e195350381,0x60d5450181551405d954,0x55140a05545018655140,0x50154585405496150283,0x5d561501655854059161,0x58540e0d615018758540,0x5016558d405516350387,0xa05635018758d405d563,0x58d40e15635038158d40,0x50175591405956450387,0x61564501835914060564,0x59540a0d645028159140,0x501845954060d6550181,0xa0d65502815954061d65,0x59540e05655028759540,0x501525c540e1d6550383,0x59171501635c54055171,0x5c5405d571501735c540,0x501545cd40e117150176],#[0x5d973501755cd4059173,0x5cd40e1173503815cd40,0x500815d540e197350385,0x60575501765d54020d75,0x5d54061975501835d540,0x503815d540a0d7550281,0x60576503865d540e0d75,0x5d940a0576501855d940,0x501528c5405463150382,0x59231501618c54055231,0x8c5405d631501658c540,0x501838c5406023150176,0x59251501619454061631,0x94540602515017694540,0x5016494d4058e5350183,0x61a535018194d405ce53,0x9854054a615018794d40,0x50180985405d66150154,0x592635015498d40dc661,0x98d40606635017598d40,0x501529c54061e6350185,0x59271501639c54055271,0x9c5405da71501759c540,0x501849c54060e7150180,0x55273501869c54061671,0x9cd405d673501649cd40,0x501819cd406027350176,0x61673501849cd4060a73,0xcc54054b31501869cd40,0x50164cc5405533150153,0x6173150175cc54059731,0xcc54061f3150186cc540],#[0x50152dc540ddb3150375,0x61b7550165dc54055371,0x5454150d5150585dd940,0x50563545415515150553,0xdd95150773545415d951,0x54941551525078054541,0x50576549415955250563,0x60d52505815494160152,0x5494161d525058654941,0x5077354941a1d5250681,0xe0d525078054941dd952,0x55141601545057655141,0x5057659541dd95450586,0xa1d65505875954160165,0x5d541e01755078359541,0x5057694541e017650786,0x54b7050551dc14160273,0xdc1415977050554dc141,0x541520c55061b7550586,0x60031541640c55055031,0xc55061031541820c550,0x543740c55061c3154185,0x58531541544c55054931,0x4c55098531541874c550,0x5415250550e1d3154374,0x59541541635055055141,0x505505d9415417150550,0x542715055061d4154186,0xe1d415438650550e0d41,0x54950591525408154950,0x54184549506055254174,0xe01525437454950a0552],#[0x55150591545438154950,0x54183551506055454176,0xa0d54542815515061954,0x58550551615415258550,0x54171585505956154164,0xe0d61542715855061d61,0x59150e1d615438458550,0x54181591506016454174,0xa0564541875915061564,0x59150e05645428759150,0x541545c5505497154387,0x5d971541745c55059571,0x5c550e1571543845c550,0x541528c550e057454386,0x59231541618c55055231,0x8c55060231541658c550,0x543748c55061e3154184,0x592415415290550dda31,0x905505c6415416590550,0x541529855061e4154180,0x60261541719855055261,0x9855061e615418498550,0x541549c55054a7154374,0x5da71541749c55059671,0x9c55061271541809c550,0x541879c55061a7154185,0x61b7154164dc55055371,0x54d5161b7454181dd150,0x54580551515915454564,0x59161545545855161954,0x591515d9645478058551,0x54587591516056454580],#[0xdd1645468759151a0564,0x9855154e61547805d951,0x54554dc1516026154554,0x5937354564dc15158770,0xdd1516037454580dcd51,0x549541c5526037654586,0x60071549651c55259071,0x5515259154549841c552,0x54981551526015454976,0xa0554549865515260d54,0x55152dd15454a8355152,0x5497459152e195454b80,0x61d64549855915260564,0x59152e016454a8159152,0x548815c152e1d6454b81,0xe157054b815c15255170,0x5c55259571549545c552,0x54b835d152e057454b85,0x59671549549c552e1574,0xdc5525537154954dc152,0x54974dc5525977154964,0x61b7154984dc55260371,0x59154605645518059154,0x5528359154a056455183,0x591705538359154e0564,0x5c1545cd70551715c154,0x552735c1549c57055176,0x20573551765c55459171,0x5cd545d973551645cd54,0x551805d9542057655381,0xe0176552815d95460576,0x9c554e0d76553815d954],#[0x551649cd545da7155164,0x61673551809cd545da73,0xdc15460f7055164dc154,0x55186dc5546037155186,0x6037655180dcd5459373,0x54961551525856450d61,0x58580549615955258564,0x61d52585845496160552,0x54961a1d525868154961,0x5878054961dd15258773,0x619545856455161e1152,0x59161601645878155161,0x58580595616156458583,0x54b705858090d6161165,0xdc1615937058554dc161,0x59184dd5616137358584,0x9c570591755c1645c570,0x5c5645d571593825c164,0x591759c564e057559380,0x61e71591849c56460271,0xdd5646037559185dc164,0x8c5545463154d518c581,0x591528c55454a3159151,0x54a315cd528c56554a31,0x8c58454a31601528c574,0xe11528c78054a3161952,0x55231591548c78654a31,0x8c56458631549618c586,0x61d648c5765923159561,0x59631e15648c78059231,0x8c5525c231545708c783,0x591738c7865c23159170],#[0x5464154d51905655d231,0x9056554a415915290564,0xe01529058054a415cd52,0x59641615649058059241,0x905525c2415457090587,0x59173907865c24159170,0x59251591619456498e41,0x94587592516056494576,0x55152985645ce5159170,0x54a61601529857354a61,0x9878155261e015298584,0xa0d70986435c26154970,0x50710e1173987845c261,0xc41655071055141c4152,0x54d51c4186507105d541,0x54b1059151c415454710,0xc416554b1059152c4154,0x5d952c417454b105cd52,0x5531061952c418454b10,0xc4186553105d954c4164,0x59161c41545871054961,0x5931059564c417358710,0xc4181593105d964c4175,0x7d8f71df855931061d64,0x9f33de7acef9bf36e3fc,0xf56e9fcff9fd3f67dcfa,0xfabed7baef5ceb7d6bab,0xde5bbb6b6becfd9baff5,0x5cfb9d736e5dbfb7d6f6,0xebbb772edddabb3756ea,0xdd7b6f65ebbcf792efdd,0x7e2fbdf6beb7d2f85efb],#[0x717dfebfb7f2fddfabf3,0xbe6fcdb97f2ee5bc7f8f,0xafd3fa6f3fe7ecfb9ef3,0xd9db3765ebfd7baef5ce,0xdb776e6dbdb5b676aecf,0xb7766ebdd5ba772edfdb,0x7defadf3bdf7aeefdddb,0xf3be5fc7b8defedfbbf3,0x9eabd3fa774de97cff9e,0xdbdafaff5eebbd6fad75,0xdf3bdf7aeefdd7b7f6ee,0x7cbf8ff1de37c5f7eefb,0x3fa5f3fe7bcef9cf37e6,0xbbf73ebfd77adf59eafd,0xf99f2fe57c9f8befbdef,0x3f63ebfd5fa9f3fe77cd,0x97f27defbbf73edfdafb,0xf77edfd9faff57e9fcff,0x7fcff5fe7fc7f6fe9fc3,0x83281413b2a141bb2414,0xae84fd4aa8172830d331,0xc8189c72011003304c3e,0xcff31b08112eaa4efcea,0x58bfee623b9aed960832,0x4a2cb79bd2e85001723,0x3feec7084b300fa370e0,0x7acb81bd2e82c602a414,0xb233895320fe8232b3cc,0x293819b28168232d4291,0x9723cae8003eaa65e91b,0x1bbdae8243fb0a093d2e,0xf3cae82f2870d40aeaa5],#[0xbfaa809147284fd32a8d,0x632a22abb093212726d9,0x32416abb094314f2adf1,0x305dbcaa8d600f24a29e,0x62b8852e51b9acb61817,0x3894b2ae10232b3dbeae,0x292f2c710272b3b91b2d,0x11f2c843d2ea1f0872a5,0xcaa87bbf6ea58d2aa84f,0xeec843cee9403f6ea5e2,0x2012823314394b2b603c,0xb67b23080fcd2c8582fb,0x238fb2c22aeb08ffb9ac,0xbd32a8e129b0c0fbfaec,0x2eaa5148872b5fbcae98,0x232b3d11b2c845ba8615,0x32ad894f2a3239aed740,0xed348832a8aca2ca3a92,0xc86bcaecdcd32a99147a,0x410d7295d8872b968872,0x148aca728832a8b0232d,0xd2aa6d8bdaa87a823214,0x5320fc0832a3514b2a34,0xb2a0153aa817bd6ecd99,0x301111b2738abf09403c,0x428ca2cb5e807263e83f,0xee2330ad615322ffd82a,0x31432a5119b2822a330e,0x11b2138c7aca85582a42,0xe30a0f94f2336bcae995,0xb0f883cae851b9aed822,0x26e739aec0033b201221],#[0x4298d32d5cbfae623807,0x601722579492336d82a,0x2ca2cb603daa87b23aea,0x91f23348832b608872b8,0xef277abdaec712e32412,0xee84f8832e002bb08ee0,0xa8e211f2b3a2330e003e,0xd43ba2ec260fb2c16bca,0x24883285524ae8062830,0xebeae77194f2b5ecb2ca,0x872a888872b74bcee93,0x3ac8709432a4f3caea85,0xaec84023213980f24d7d,0x2d3939aecddbcae9733c,0x4229c32a143d2ecd9823,0x3780f243c0072731582a,0x48a7275fbd2e99411b29,0x1c52e1400f30870832a5,0xeb0a17bd2a8db233080f,0xeecdcbfee82382330ee2,0xa6158872a3115720fe3c,0x1349e324228872b8c56a,0x882ef082392b2c7111f2,0x84f2a11bd2a8eb11f2a,0x47ac95ca22ec0600f257,0x832e85d8322238872a54,0xae780bfeec2382331430,0xa8879c32814582a4293e,0xa8a2bf093eac2a8dc53a,0x1839acb6153b28708832,0x4d32a81ebfaec70bdaea,0xaeaa52011f2935582a42],#[0xfae823ac3092d023293f,0xee670857213b89728343,0xa1100727853eae793bf,0x82311f2734a370ef2adb,0x308232142883205554aa,0xeca2cb9ac82c92739aec,0xd852223bcaa88a8832ef,0x872ae095328ffadb072c,0x329414a2ca5880730138,0x2ab52eaa5191572a8782,0x8ebbd2eb91827213700b,0xe18872a341632a16bcaa,0xabdeec71233040e8832a,0x15720fd82730ee3faa47,0x432cdcb2b0887abac939,0xb2af581b21908b7247f5,0x283d466e27718b289082,0xefcd92a477547099509b,0xb71372b4901f2d2215b2,0x1ad2a8fad8aa845cf2c8,0x427083589f2c3881f28f,0x952e23d46e93801b303a,0x326842f3091da2b0c62d,0x28af9af209f9ab287954,0xb3f272ea6387f212889f,0x2cd8aa5133bac85f2f2c,0x701f20ed81b31680bd2e,0x863304bd8aa4fa5eac81,0x8acb080b724a9436e825,0x30809542c9382ab0d94a,0x24abaf30f1a542c91745,0x8cebab280501f29318b7],#[0xb0302a92d89f28b0332a,0x854286f615f22fd0b922,0x833214b2f706fd863292,0x8aca4a4270c010bb2ac2,0x30ac3ad30b5615b2c005,0xc96808b2b534af0d9629,0xa64276e91ba57098abaa,0xd74bacaf39a3283ca62e,0x25a2ca22b0acb2001b30,0x8b7246a592a4780b7255,0x62eb6c58aca0fc0aea46,0xaeb9ba6f02b105f2d46a,0xed9458aa5072d70aaa3b,0xae00c52e25a6aed4fc0a,0x17b4ac863b6b0d9115f2,0xda6b0ceb01f2d305dac8,0xb3308c60372898402ed1,0x4f0a1981b2e8202b30ee,0x708519ab209503330613,0x3009253092326b0351d4,0xd360b12e332630967c55,0x1706f2d2006b20fb2f30,0x3af30a609732c242f30f,0xc06e9042d30b554aacb7,0x1b205ad5aa8722ab0c4b,0x320b1d72ca4aa670e008,0xc8cd81f303bc032e858c,0x6fc60c86164aac90434a,0xf2cfac871c06ed0015b2,0xb8c720b395f22fe406e8,0xaf321370333061a630ce,0x530e613e6ec7cbaeea96],#[0x2c868402ea84a530c0da,0x2830c2ac98595f31354f,0x899372300deac81695f,0xc81b311d193288c05d3,0x6542a8e3da322262670a,0x55b2c71402ea860b3283,0x46e937d42a866caacb5e,0xb0b0989b2f4995b2efed,0x2a78a072c155432c8430,0xef602b2afbb070c2b973,0x5d8bf20da9332b49af70,0x216b2a3f58aa4f4cab29,0xd52c82c5912670caf0d8,0x5b2b6c402ea95c06ea55,0xf2169a032816406e8ee0,0xcf69ab287986f28ef81,0x932a032c16d42c937ad3,0x401b304426708093330,0xf5930c70d8aa99aa530c,0xc02ea66b030a10403280,0x632c2201b2b7f342c94f,0x522b51f3208bcfac8778,0x2c3ed552325d5aa87a26,0x88908f2ae72f30d4487f,0x25b4ac9192f308ee4e2c,0x62072c231032d9b13721,0x8bb2e80b6f0c1ec22c98,0xf3071a3330860d930823,0x7082f572c6d9342ca122,0x2c20af30d1d9ed2e34d4,0x860d5aa877d5aa86f867,0xee59720f6542a8c6542a],#[0x205b2d41af7090daf30e,0x89f290b2f708f286b209,0x22e9455532325aab0c10,0xd2219d5d227102b311ec,0x26fda67056aa8b0d185e,0x89d442865f197258415f,0x6276ec43252eca98332,0x28b32e0086b208258aa5,0xc02ea89407200f3032c1,0xf706f64c2ca7215f2735,0xacb1487b2ca4542a889a,0xccc3aaed994aaca2fb0,0xef92930cb7caaca84a93,0x94a630ec081f2d5981f2,0xba52eaca34b0a198bb2f,0x342c95122b0d2f34ac87,0x2e90d9a3292ad972104,0x2a9281f3246fd4322844,0x20a2b6aca11af30d1230,0xc4381b2efb492c90486f,0x22402ea899f3247881f2,0x2545273483728a2a6eec,0xd432334a052e14dd2c84,0x2b311e0af278055b2100,0x2a8da3e2ea3826704b38,0x30c6b3309450af272a55,0x9678e7229de0ac615033,0x7893329030c32c7abb2c,0x6a7720a28af2756be2eb,0x95f2145867292daf70a6,0x5728a281f2c4d402e70d,0x2a4794032e3081b21542],#[0xc935c62ea1d0b32f95d9,0xb089a722939732a79d42,0xebaaca3da5308f202b2,0xc81f216f993288988f28,0xd42a88b8e32ca007b2f9,0x9aca8cad30acb88b2f03,0xf2137242ed578f72564c,0x20942d30ac1063319215,0xa318633010c12ca269af,0xd981b31998b12e33c02c,0x3b72a4c20672c495532c,0x81b30c19ab20a0933290,0xf21028c7200a0b52e36,0xf2b5e09f2a0e0bf234cb,0xcdcaf2cb3406b209d15,0x9732f324652f72137547,0xf82072c1734f20945470,0xe89b212b89b290c552a8,0xa52eb6f22b2e65ad308e,0x92c623d97210d81b2841,0xb281795f2a53033286f5,0x300501f2c602f523375d,0x36389f28b0c36ea1981b,0x1309b28b1af3091a2a92,0x71af28744030a092ab2a,0x572c84fc2ee82c96b2b0,0x63301003328a49972886,0x6ec23a8f0d0ec02ea028,0x28992630e60b0aa8efd9,0xa0266e8f022acb69033,0x23d92e8ffa530ec11ab2,0x2b4ac8b9d97211dd9326],#[0xc720b08af2752a6b0d9,0x8b2230c02ec00433080a,0x70c68c02eaa6033214ad,0x20e71ab28784f2c87d29,0x8639af2a19d4320dc81f,0x9660ac81405f2d33b4aa,0x2c06ecfc2970a968e32c,0xad30912af723374aacb6,0xa122939372b48a8b0cf7,0x2a88c4aacb32a0328149,0x292c34ac8c915f2efdd4,0xb75592a471c06ed1701b,0xe42ee844deac81cc02c,0xa4052e30b32a86409f20,0xb724b940aa92ed97211,0x42a883d452334c572809,0x2ec7328b0d1e88f2b52d,0x3123402cb464032286cc,0x93381b30f24aacb5f01b,0x7f90b2c6f9332a9505f2,0x101b2e08d5aa87984726,0x95b2cfc05f250b423200,0x32686d42a8c0a5b06ae,0xacb95af7070da42ec654,0xa17c32c809a2aed9f4a,0xb486b210cda2ca29d93,0x6601f292389f283b8c32,0x438708290b9234cd52a8,0x1b2ce88b32e8c2f7090,0x1f2d24402e91dcaaca30,0x12e32a5f074e09f283c0,0xd7da52eacf552a8b58b],#[0xca9a6eec4958d2230a6f,0xfc402ea83ad32af08332,0x558aca4226704b495b28,0xc33080995f26fe0b32ab,0x2b2d10d42c80006b306f,0xf209b09b2f99402ea030,0x30775972823c02ea6086,0xd8601f2c39c02ecfd06b,0xe322b0ccd61aa41d2670,0x605b2d3f15f2a32d42a8,0x26f0c2055b2271063200,0xcf2610d5aa8702ab0c10,0x30c2385f294781f205a1,0xed120332aa9d930670d9,0xa024f2ca42c572009406,0x84f2c8bb1af281b402e,0x457300901b2c5ca42ea,0xd52c9725972c238bf22b,0xaaed0906f2d1488f2a3e,0x32a785930623d42a8deb,0xa8c22032c1d95f273517,0x865a730a0bd5aa87434a,0x80c032eddc5320092932,0x381b3062cbacb0620320,0x2f70f0405b31451f7203,0x42a88326aea47cdac890,0xf217b9332b4a4bacb135,0xea563030a46b432c1201,0x735c02cb7e252ec64c06,0x44072286ce30d81af50,0x515b2900432ea19af707,0x2632ab54052eddb0b206],#[0xc9263e42aea42a470aab,0x328a53430d918c72a0a1,0xd382a30c60a730a0a83,0x10289b292b0bf20ea2f3,0x8640eec2c08b2a3a1772,0x589b205b16f2302402cb,0x15f2d35a0320484aaca9,0x4ac8bca72eac21f7241c,0x7095c83330cc28acb07b,0x208c542c932427080154,0x912402ea8315b26fe9f3,0x3706f210b542c944af30,0xf4052286c02ea0195f27,0x1372700baacb868bf231,0x8b0cee8b72f8d2530cec,0x70d4baf2a946b02a72da,0xb425972270d5b2a72a9,0x46355aec7115b2d322f7,0xf2cab2b5d06330488b72,0x401b30ec95b2d44d9720,0xa6aecdc55aa873c16ec2,0x52e80801b20e9272eccd,0xf0d4d2430af2252ea64a,0x353595067081b2b9022,0xc0d1ab286fa470a0726f,0xc18db2d048b720de2530,0xb87f2ca2b470c1f0bf22,0x8b724b09692302402cae,0x4aa8cd81f306281f2007,0xb2a3d457080955aa8783,0x28753bac92ec52c80901,0x82f06f2acdd46e9359af],#[0x8542a8b62f2a8f0542c,0x6a670d7e037286b81b2e,0x95b2d380bf231f85f294,0x2b0cc8af30f0401f2d30,0x6ea535430d3887f20e62,0x2aced42a886542a88940,0x7004072c869a7238485f,0x80c130a09c01228695b2,0x954708002f30d37d52a8,0x3430a42d42a8dd3e2eb9,0x47098ba53096815b2138,0x2e802caf0c30a6b02ae5,0xa8849732a7901b2ea542,0x91aaf3033588b2a3fd42,0x36a970c8d2930d562d30,0x78b72c3189b2e03d42c9,0x2f30735863304b402a96,0x67098e867228f9772a27,0xb2219baf2c9e15f2a33a,0x6b1d42c9732f123375e,0xb06a570840343081025f,0x56d92a47509b2ea002f2,0x1deaa81d2f70ef2a2b0d,0x22b0f9cd8aa518c22e80,0x2ead09ab2c18406e900,0xb2f9f572a666552a8fa4,0xcb46d92a47a28b0d1401,0xd0dd92e670d94c670af2,0xb43e2ec7cd5aa875c02e,0x82930c7e18f288e0c720,0xa43080e81b318f442e64,0xe32ca0a0328292570a06],#[0xb2141c072b4602f2af40,0xeac3bb70d9786b20a585,0xc7b5b0c4ac06ec2f3ae,0xacda2ca28bbaed948333,0xd2ab2813542e8fc8332a,0xa2b300522b0d99b830a1,0x1f2aed06f2d195430cdc,0x30d3281b2ea481f291c8,0x280f0bb2e4826322b52a,0xa41594e67089b20e5c07,0x1d0bb224e81f284e01b2,0x1af2cb472f30cf62032a,0xa72ec63aab0d922530e6,0x2530010b72f98af308f2,0x30e0381f2e059932883c,0x218e9d3209089b283a25,0xa3701f2f9a0e32d4a457,0xe42f30ef655d267149ac,0x915b2d9501b2a0b89f20,0x54522841a7287ec53300,0x3328a5a57097ed5b2671,0x32807043217d0bf22c80,0xab6c22c80c4072686be,0x823af70b41bb2ed95ad3,0xceb6b0845c06e912592c,0xa22b0b6881b2ae9a62ea,0x3e2c92e0b32e8336b0c4,0x32c86d8aa4f38b52e30,0xb282dc572474c232c014,0xc62b95b2c51a930cc78b,0x9459af287601f2171572,0x22af5313e8df290595f2],#[0xc96b2afa42308012032c,0x292c8c4d92a47001b2f0,0x5b0c7115f2cfd0c32e77,0xf2b69347082cbaaeac3d,0xcb192f32337406ea5381,0x670caf0cdd8c3300a30a,0x9b05f30608b72f985972,0x6c5328092570b86c0aeb,0x1af209f1f724748c72c2,0x72b9b95f26fd063282e,0x72706937290101b2cb21,0x2ef0a52eccf423300104,0xc29a2f0cab8af26cca55,0x8b9ef238d01f2d15a032,0x12432e652f30f12402ea,0x4272492ad30ac6a6aed5,0xbb20db83330cbd9720ee,0xaa87750ac99a9af209e8,0xa8c295f2b5f193288355,0xb689772a74546e936c2a,0x95d92a473d42c99507f2,0x2430acc95f20ddd42a8,0x2430a62deac82881d304,0x430845412ca7ab470c1e,0x30a1081f218a09b28b13,0x26868632a212f70d0db0,0xd358ab26440c7300a405,0x83a6aec0609b2a3daf30,0x6cbacb070c32a0b9f320,0x59328238c3218f3aaea9,0x97249281f284d95b2d73,0xac824542c851c02ca359],#[0x7174c2ca25b430846d5,0xe83a67056b87b2d682f3,0x76ad308f303328920b32,0x25eac81da6f0d85d92a4,0xd5aa8795912e23a2b0cf,0xf309001a3288101b305f,0x2e94686f291b82b2b0ca,0xb3f4faca19997254826,0x875d42a8a655aa8752f7,0xdf81b30a455aa8719af2,0x6542c9364c2ca71d42a8,0xad7090e06730473030a4,0xbf2c2d0bb238f81f2a07,0x32ef0af50335b33088b8,0xecf62f70cf622b0ceca5,0xb3ac0324070633046c06,0x3285f214788b2ae7af30,0x6c12ca2a063239f05b31,0xc33009a2b0cd72530cd,0xb72e0201f2b9ea5ee767,0x2eac0b8708164fb0c728,0xca1ed972117272eacdc0,0x88295f2efe4f2c99b58a,0x471772a7585b2ab50332,0xc4012686d5320d9a6f30,0xaf30d3201b2b87193293,0x6b307881f2d5b0632c37,0x30eee8e72c9e403200f0,0x31408b724c88e72a96a4,0x8fc4af0d7401f2d19af5,0x62177282658acb91406e,0xe492ed00be2c922caacb],#[0xb72e0195b2a350bf236,0x6b210d4e2c895c230c01,0x724a2b3708a60c32e6f8,0xe91a402ea008b72f8c8b,0x98343084b492ca8d406,0x9424530072430ac806f2,0x6552a87d0b324b1d52c9,0x88b2aa405b21425a5222,0x972983542a8d0d5aa876,0x6e8ef8b32e8b8f72d5e1,0x24bc2f3071dda2ca2327,0x8302430c04c02ed950b7,0x72f30d3695b2d00426e,0x72aac928597211224330,0x97321039332a94c02cb9,0x2b2b0d552a88101f30c1,0x3288bbbac99c0a927528,0xc8505c2c8499732a6f99,0x936402ea8c2d70cf6d52,0x178672b93402eac6546e,0x1a2b0d230b724af592ca,0xa52c95b381221bd432b8,0xaf2873c02a98ed432885,0x30c618b32c0c16f2b061,0x2878863218e552a87ea9,0x12f2f2cb33da2a8291ab,0x61c92cb179f3208981b3,0x90c7280b5932c23ad30a,0x83728802d3091e451300,0xf30d172930c614ab215d,0x2a463a530f179f320832,0x20e2c22e8008c3282b37],#[0x71201b306355aa8788b3,0x452550e3854526842f30,0xf2d30a610bb231d4aacb,0x2530a0d5972623a2f0ca,0x1f216a34b20f0c06ea52,0xaa4f840eec2ba6724a28,0xec03d8aa51b2f30ef2d8,0xcaad912270a930cbbbaa,0x6fa430b1f5432734a970,0xb837288fd5b2873592a4,0x2f30b3c2430f1ab0aa91,0x1f215a3e2ea03a630ab5,0x2a933c02eab62a30d450,0x2c09a650e8c402a8092f,0x1644e3095d15b2c2f0c3,0x4bcc2ca250b724cd0632,0xc2eea42ad328653030a,0x503289736b0c0fd92c67,0xb3096643b215adfac81b,0x30ceed7aca675e308522,0xc9123530c61505269db1,0x8f29ff20525e2c8b659a,0x78b52c8ce07330ef59b2,0x2b532cf0de328669b721,0x1b726945032a9697f270,0x7b2aa31ff2000b52c8bf,0x2c866117296650321631,0xa9f5b2ca279b322a0df,0xc62562a8f727aea08353,0xf2d62c87c59b0c002b30,0x7d62c912de2c866d9ac8,0xd9acab6312cb1559aed3],#[0x132ca3bc6eb649b72056,0x2c860d9aecf662320589,0x306220f217297b2aa3de,0xaa0d9d2285df5227e073,0xd19ff2173ab32a659b32,0x353069edfd2272b530c,0x59b20dda13209bdb2ca7,0xb3267359aed36b52c8ac,0x2cb8459acad0dfb0825d,0x227e37b0c60db3227350,0x9261b72a9eb7b0cd0df3,0x9f35308ef1b72003d62c,0x4cb29059fb21781b722,0x2b2cb7c5652300d02caa,0x7ac67c3630cd11b32c95,0x30b64c3eec93c5b0d755,0xa619fb20561172166ab,0x8b5d9aa85359b2285b53,0x73a17267643aeb845f2c,0xc5b2ca76dcd268d5e309,0x1b7229e5130d73a7aeb7,0xcaec8dd02ca9e9ff3052,0x321881b72a68de286dec,0x2d7e59aed385b5267350,0xb0a45ae78317f212545b,0x243c32005623205e3130,0x12132c7a2132c6fdb30c,0xb7b0d75d62c9031d926a,0x9b2685a7aecb297b2d03,0x2c90197f27015fb0a19d,0xc902562c8f3352c8ba56,0x800d03269dd02cad2562],#[0x66dcac86759d2685de30,0x6db2ca6fb7b085362b20,0xdcac8d137f0d75d03269,0x52c8c9c1b20073c2ece6,0x32aa020f2050d9f28f2b,0x26a02b30cd2d02ca689b,0x8d0dfac876b5308c71b3,0xd0b530a9ed9ac6f65e2c,0x4d9aca60d632125e2b20,0x9b7269e9b3290bb52ca6,0xfb2272d9f2a534cacb13,0x2cab79b72a9f1172165d,0x2ac3d62ecf6b130aef50,0xc51d632300db52273503,0x17d9aca66dcac86cd9b0,0x6503229dde328d0d632b,0x4cb2b055230c25d9aed3,0x530ab7dcb268d59ac8ee,0x7215645ae775ccaca8cb,0xc903b7f08531b721501b,0xa9f1b7269fd9b0d73562,0x123130ad2d1b2059502c,0x41b7269e352c8bd59b2d,0x5f2c86c562c8eeb530b8,0x9eea5343b2187e330c23,0xb2117d05229dd02ca61d,0xa87ddfac87045b0c015f,0x29fd2321053132c65562,0xa0d9f2d125b2ca7a1b72,0x9d7acad12b30cc7502ca,0x1db269bd9acb76623217,0x3215c59acb75b130a62],#[0x6ec7027aecb23530ad25,0x2d338cb2cb1392ed14c7,0xc75a7aed11b8cc311b7b,0xc1a7d22b346922b02172,0xe5b2ca781b32aaca7b30,0x43aead243b2a0e27aec6,0x72ec790732c6f0cb2cf2,0x2c90e27aecad3130ef7c,0x26fd3530ac79fb2c0356,0x67cd9f291246aec7ed9b,0xddb2ca75352caa9d62e,0xdbc52f0545f247f59b27,0x5b32a258cf2ea76330c1,0xb3214a5b2ca78a173072,0xeea55a7b0a3d35303481,0x246a3930c75633027759,0x36c0cb205aa13301a1ff,0x2ac5f318e8cb2c09b786,0xca7f0cb13530ed25b30c,0x9ff285327b0cb2d632c7,0x9f291da17301a2132c78,0x2c918a7d2353ab2cacb5,0x2d76312c710b8d302cdf,0xf0cc3ac94c472ec741ff,0x688cb2d1f27aeac58732,0xed9b2d0d8cb276bb570a,0x732d20a0b283f1ff248,0x52ecf0b932acddb32e73,0x2c87ebc3017b1b72caa3,0xec7027b035245f246a5f,0x76ac76ec279b72ad2472,0x4cde286e34730a0a0cf2],#[0x6b57269457aca90a7f0d,0xc3aec93db52e2643b0a0,0xff21769b32e955fb2672,0x72c1b8cf216e43aecb69,0x2a61d1b2b9ba7b0ea3a1,0xe8f4730c7ade328609b7,0x387326b359b22fd0772,0xa7b0f2959acb77b130d,0xa7aea5bd02cac79db2c9,0x3aeaa0d9b290db7f0975,0xd309aa7b0ee6b530c954,0x221a4732a0a27d0f2927,0x274c3ee92927d0352635,0xa859f2d0da7aed574752,0x843eec67b53229443f28,0x45f246343f229e46aecf,0x732908c3d2e3827b2370,0xb27595630b091df2e8c8,0x229e633082945ee75e27,0xab3e1306723130eeec3d,0x54502cacc59aea668cf2,0x4a132c7835308a30cb21,0xb5308a3a1330720cb2ab,0x52c89159b2145b533099,0x32a9d43aec9537ae8f03,0x2163a7aed106330c2887,0xca68cf2a630cf26b0ab7,0x1b41b000759f21371b32,0x638d301f873217cdaaa9,0xa7eecd3d02eca245b2eb,0x930c75a7b0a07a7b083f,0xb0a3ca7aec6527b284e3],#[0x2cea8cb2d162132e7a38,0xcf327d3097b7ca6b5077,0x7a3530ccb9ff217617b2,0xdc3ac94ca1330775fac8,0xb97209b477210b5032e9,0x5f0c010732e9c46aea3c,0x73025c3f290b59f26f64,0xc86fb7b080187320e821,0x2a2dfac8783950309dfa,0x5f32a42c6f22b02792,0x2a7b06b3c6f236e59f0c,0x355309987326b2a7b306,0x7b26ed4730c098cb2d0f,0xeed37d9ac90dc692297a,0x2e66d230c1a1ff3173d9,0x2bbc3b275827f0e9ac5d,0x86b52c95744aec90df32,0xfb530a68db2ca79d9b26,0x9ff2c0227b0b9ea7aecc,0xdf26a15fac878a7b0e59,0xb2a6ddff209fc5ae8559,0xa802c4aecbea172c750c,0xf17b62e6989b32cc6d9a,0x3b27aecac35728a2b530,0x6a133019473300a59d23,0xb112302d1acb9e43b000,0x7b0e6a5b72a75a132e77,0xf0d7545b280959eed362,0xe30d6232c4a27b0cae45,0x78a7b30d745f300927a,0x2b46aeb9e43aea9f2133,0xb2173071a7b2b690cb21],#[0x9b32ccb8732cb20772a9,0xdf26620cf22b40cb2ad5,0xf2c62a7b0353d9ae91a1,0x214eb57288f8cf2cc80c,0xa51b2127d9b2a521b7,0x3e330c1743aecc6c732,0xa4732274a13307a43b2e,0x45ae97762b20b64730c2,0x7d307f43aeaa7a7f0352,0x32aadc3d2e21d7ae67c2,0x2e2ca172e71c3f28b407,0x63117216543b2f17c6d,0x51b130b0b8cb2cd527b3,0x6a132e79ab2cad046b03,0x8cb2caeb530aa027d0ee,0x7f0d4c47720b0c72ec76,0xf270dbc2caa927b063d2,0xecb60cf26b38cf236b59,0x69e315310eb530ed1c5a,0x771b7274bc3f28b0c3d2,0xa9fb20e3a7aecd49fb29,0xa7b291ca7f23703130f1,0x772ef959f2d1da7b0007,0x72e6b59b2286e272c0f8,0x24598cb2ea727aec8187,0xab48cf214f45ae7839ff,0x573c52e3b38b301027b0,0x30cb3007352caca07720,0x27b0ccca7b305fb530ec,0xcb2ccc9ff2053bc2ecb8,0xb2d5b077217927aed198,0x290fd9d2e309ff2d75a7],#[0x90445ac8093c2caab8cf,0x7b7b2147a7f275959ae,0xd1fb273f41b2a3fa7b20,0xd02caa7d9b2d1da7aecb,0x9f233b5aaa907472ec6f,0xf22c1b7b2947bc32e975,0xed36ab307648732e9146,0xec9df26b843aea9ed9e,0xfc5ae853073291127b3,0xf59b213746f03536232c,0x37ca36c27d304c8cf2d1,0x172302c3b2292b7c636c,0xb2923b5330b7d9b27373,0x2700b132b570cb2cc827,0xf0bd632cf6c5ee855d63,0x1fc6b227f392e8efa7b0,0xfa172c27a7b2d59bc2c9,0x8cf274d1b721488cf217,0x8b03290732d118cb2916,0x2cacf41aed0e0732cad3,0x319d38f228fc7720a2b5,0xaacc5ee8533530acc0cb,0x6aa7ae8f1b7b2746b530,0x98cb2ea33530e8d0cf2b,0xdfae909c1eec7c476ec7,0x9aa855d9ae8ee45d2ed0,0xb2e008cb26b4d9b27445,0x291dd9f28ee27eec6ac5,0x9771b720e5353295759b,0xb646eec6627d0f0a59aa,0x5c3ac8a83530cc6de328,0x732cac6352225a13302],#[0x92ec7ba7b2f57312e8f1,0xd22a2d9b28ee1fb2177b,0x2cb6c7720b3d9b2a00a7,0x801a7f0d4e07320089b3,0x5897f2d265fb281a37f0,0x27b30c443aec94e2720,0xcf2cb05cb26be279237,0x7d3040c77216b35708a7,0xb239a0cb2c6d45ee6e32,0x2e25a7b2759e272179b8,0xa68b53307e355308d475,0x55a7b0e8ea7b26b343ee,0x6d03289a62b20609fb28,0x41acb0f0732ed437b2d4,0xff209441b0a070732c91,0xb0cc841aec7c3170ef7d,0x2692dfac87543aeab7a7,0x302a7b2931c5ee6dec3b,0xd23533061a7d306a3132,0xa27eec6e27aec6ac3eea,0xa7b30b90732f1c476ec7,0x772d5707330d28cb20e7,0xaec660cb283f8cf291f8,0xe91bdb2ca7427b28f1c6,0x6a5fac8745f32181392,0x81a7b2e05b8b0189a7b3,0xe5fb3072a7aeccaa7eec,0x563288dc5ee7621df2c8,0x7aec828772c6bdf32399,0x9228f8772005a7b22a2a,0x280b43aecaa46aecb5b8,0x7e217282845f2809473],#[0xfd59ae9006330c29b553,0xd51b217a38b0b9e59d22,0xc5ae802a7f2f9a477214,0x572294627205e43d2f17,0x72ab7c3ac809a7b30ccb,0xecfc38b0cfa2132c799b,0x6940cf2a6a2b30e9a59a,0x68c3aeacc59aed003512,0x8d9aed173930c1b3570e,0xcb2151c3d2292a7b0ef,0x7b2a07a7b22b30cf2ab9,0x2c88145ae801d990e30a,0xe975d1ac90707326a5df,0x976b972c1bc6ae90745a,0x8d9ff2c53c1b280e9ff2,0x3d02e696e350271c1d2e,0x502ed178cb2cb207330a,0x7b0cd35fb26199fb2978,0xd30405fac873b7b0ed0a,0x275b8732b6d59ae6f627,0xcae27f22a2d1aca3ca7b,0x41bc3018951923658cb2,0x843aeca68cf2cb8a7b28,0xc3aeac7d9aead0a7b26d,0x3aeaa03c72ca2c5eec66,0xb229e59ae8f2b170f04c,0xec7c8732e6eb53074843,0xcce27b0caeb8d2239562,0x123c52e972792e3927ae,0xe3c50e3b45eecd0d9ae9,0x3152302c3f295243b269,0xe7288638b304b0732ec5],#[0xf2e7d1fb20030772c8fd,0x30bb9b32c6127aeb6ea0,0x91f35330be45ae78db53,0x9c873205c3530aa0c3ac,0xd9ff252937b0855bc30f,0xcb2b6bb630ed143b0a3,0xfac87945b30095fb0c18,0xb23538cf2a0a3570caa5,0x2ea4e272c4a59b2b73a7,0xc560732154c5aed75873,0xd8312cb208cb2cab1fb2,0x7c5ae78cb5308a127d26,0x97b2d12d632f009fb2d7,0xcf2155a13210ba7d0353,0xeec955b3282627aecc00,0x30195aacafa472ec7843,0xcf21fb3173a0f205d217,0x611fb2c2eab2c921a7b0,0xe5cf288e5fac875c3aec,0x2172e720cf2ca8d7aca8,0x790353c4f2756a132c79,0xb2e8ca7b2ae9b930c1ba,0x2102b5530688cb2e691d,0xcbf27b0eef43ac94e5b7,0x1f5cac8bea7b26e9a7ee,0x345aec66a7aed20a7b0d,0xa7b2aed45f2d7e27b312,0x6aec6c27f0353b533068,0xf0cafbc2c90f9ff3000c,0x307f38b31949ff2975a7,0xd260732b7c59b2cfd27b,0xa159d2686b570e99b130],#[0xa1fb30522b70e9a27d0e,0xa7d0ea1a7b2724a7f0e6,0x2ea96a7eed1543aeaaa,0xaa9758cb2a3d47720b45,0x21569fb2802c5f255259,0xe99ab32163b52a2ac8cf,0xb00cf2150a7b30bc3530,0x8b8b083f0cf205a27f0c,0xb5503480cf212f8cb2ca,0x72ec7559eed380732cfb,0x32ef0a7b0caf9b32cd1c,0x2ccfb5308a1b530e6887,0xb68c3b200e59f2737073,0x9a43ac94d8cf303bbc32,0x50cb2cf535530aa3c52e,0x39720a2b7b0d772b70f0,0x7f290e9b72184d9b2912,0x32c1bb92cacda7f2e059,0x2d4e43aea61a133077b9,0xc7355074835330d20cb,0xb0392ca638732ed38733,0x843b2b86dff281b27b0c,0x476ec75b7b0802a7b22d,0x92ed190cb2eb838d0329,0xb2e9027b2b9eb52c881b,0x26945aacaf81fb2d771d,0x69e37b2946a7f0d0f353,0xfd27ae908a7b30d34392,0x9b1530f78cf2cd359d26,0x31330f7c72ec73a7aecc,0x7d0e59c76ec75502e905,0xaec67c3aeaacb130d022],#[0xc890c5f24bc20b2c8143,0x69427b0c628cf2cccdca,0xfa59b29458cb26b33552,0xc8732efb615067246aec,0xc1b2e8dc4eec6727ae91,0x530c93bc2cac89b72ce4,0x70e960cf2ca827b0f0a3,0xe972172c1b45b2ed0b5,0xab38cf2152d1d223b2b7,0x9343b2f9927b0ea127b0,0x827b0ea1b5302acc3aec,0x613067797f2126df5223,0x97210b43d2692d9d2744,0x32ef0c3ac90f35122943,0x18a59aed1227b215a35,0xa75c5f24b91b32caa27b,0xbc43aea689fb273e5b2c,0xbd9d273e9b32149c6b22,0x59b273ed9ae8fc27eea5,0x5aed77213306fc5ae777,0xf0cab3130d0346aec814,0xe8f0db2ca793130f1827,0x6f6c69236c9db2ebdb52,0xb10732e8241aed10d62e,0x1c3f28b39ff200227b0c,0xbc32e9a46b2f948732e9,0x1b300743b063d97b2cee,0xf0cb1a7d26b33530c94c,0x232f27b0cd5312cb1027,0x8efdaacb18b530e7e46b,0x9a0b212ab552294392c,0x7a7ae76d27b0e9ab9303],#[0x43eec9327b017bb930c2,0xcf2cab599233b5cac88e,0xf0c51d9d23443130d1e0,0xeb6d0cb2f0ba0b2a3cd9,0x18b59d233ea7d237027a,0x788732a081ff28018cf2,0x1c5f24a2b130f14472ec,0xa7b312f59ac91da7b0cb,0x9aa8018772e7fc6aed18,0xf0d4d97b2f03c1f2ab05,0x1521b721555b2ca73a7,0x353a7903523530ce4c77,0xa2df72384a7aead4a7f2,0xac3ee859a7f0ef887726,0x17b2d1e27b300a502caa,0x7e62b527aecba3570e8d,0xb09775fac879d9b2830b,0x2d0e45f24b08772c8037,0xe9c873269927aed1597b,0x8ebc32f056330c228732,0xda7d2724b7b097587330,0x732ea527b0cb2073216,0x4eecd12792353c39229e,0xf2cafdff287443aeccbc,0x2e60a7ae2a5bc2cacd0c,0xc67c3f269e51b2188c5b,0x9a9b721495fd26729b32,0x259b2735a7aecbaa7b30,0x27aea993c2ed290cb2e6,0x7d2e3937aa2b543f28b0,0xf0cf827eec913130d01a,0xec60b8b091b46d227f38],#[0x324a7b0ea359f0d7345a,0x5ba7d2324b170d0e27b2,0x944eec6ca7aec800732a,0x732c82c5d30360732a9,0x530c933570aaab570e7e,0xaec8e21320a31fb3000b,0x2ccac3eecd1b7f250b44,0x9100732c9227b0e62073,0x8d46ae91b5652700b52c,0x10cf216c8cf2d0f35330,0x732cb2a7f215a312c92,0xcb2cb1bc30b9da172c74,0xf20e70cf2c69d9b23440,0x2e9b8732ebfd02eac38c,0x91ed62c91e0772cf98cb,0xa20cb215320f2129ccac,0xed9acb774730c1adff20,0x59b2d35b12cacfd9b233,0xcb2cb2ccac90ea7b2f9a,0x7210accae905b530ebe0,0x2e724730c26dfb2a19db,0xe8ed9f290dd9b233b213,0xffc5b2e668cf212a27f0,0xfff8007fffffffffffff,0xffff8207ffffffffffff,0xfffff8407fffffffffff,0xffffff8607ffffffffff,0xfffffff8807fffffffff,0xffffffff8a07ffffffff,0xfffffffff8c07fffffff,0xffffffffff8e07ffffff,0xfffffffffff9007fffff],#[0xffffffffffff9207ffff,0xfffffffffffff9407fff,0xffffffffffffff9607ff,0xfffffffffffffff9807f,0x7fffffffffffffff9a07,0x7fffffffffffffff9c0,0x7fffffffffffffff9e,0xa207fffffffffffffffa,0xfa407fffffffffffffff,0xffa607ffffffffffffff,0xfffa807fffffffffffff,0xffffaa07ffffffffffff,0xfffffac07fffffffffff,0xffffffae07ffffffffff,0xfffffffb007fffffffff,0x7ffffb207ffffffff,0x34000000000,0x34a0000000,0x34a000000,0x34a00000,0x34a0000,0x34a000,0x34a00,0x34a0,0xa000000000000000034a,0x4a000000000000000034,0x34a00000000000000003,0x34a0000000000000000,0x34a000000000000000,0x34a00000000000000,0x34a0000000000000,0x34a000000000000],#[0x44000034a00000000000,0xaaa043981a0808de02,0x2b40138d087483abc18e,0x1383c6a1c010cf205e84,0x10a7a84e6e2498112d08,0x1b410cff063622f1a164,0x3e320a08fa10778038e0,0x484e4625c6125008d784,0x8b660589c2afb94db8a2,0xa0d0cb08631130261770,0x7e9c8e0df8c6d3d35559,0xd40131f4ccf4c2776b3a,0x8d8e4571220f50b1c829,0x4e097ab4aa424b05208c,0xf54a2ea2bd4fed274f93,0x2c9315f2cacd4553aa9f,0xfa5af27d7438b7b95a92,0x89645a3194987dec19d5,0x6d5fd69b5342619c6ecb,0xc5fee0586ee136ba1b0a,0x5add708e97a73c739625,0xfbd595e718f1a777c73b,0x7fb23f455f606f9097b8,0xa5b12c408b419801014d,0xcf3b7ed1300a223a7c1a,0x4579223487a0c80118c0,0xadc312bbaae9921a7d1b,0x26094e468a81a801013a,0xae535cc7ae6a4a56839d,0x24d1002d87810000fcba,0x8c62f2af2728e1de6b17,0xa5711a348900d800e635],#[0x6df34cc1ac69da38801c,0xe3f8c2240721100106bd,0xbeaaea22547f9ba6493,0x25891e3a8ac1c000d132,0xdb326b72a69523e859b,0xe5b92a370701380103bc,0x4e7354cbafea122a7c1a,0xe6b1603b8a415001063f,0xd0a3eeeeb5ec52b4971f,0x5311235896168013349,0xdc328bfaae9d2167397,0x84d1002987a0b800fe3b,0xac92d2a1a5e851e86896,0xa679543f8b413800f3b6,0x2eb372c92e6ae280891e,0xa488ea2e08a19001133f,0x2caac4a3a64871d87096,0xc6a956410ba16000fb37,0xce5b68c1ac09da50881d,0xa531002c0680f001063c,0xed933eb929e9c2247999,0x8529103288610000ff3a,0x4cc30cb528a9d22c6d98,0x2559283707013000eb37,0x6ef37cceae2a7a5e819b,0xa5a128380921100104be,0xf1a3e2de30aa825c8b1b,0xe6493e3c8960f001424a,0x5153f0eab3abe294869d,0x2861ae558f828801444a,0x11f42eef33ac12b2a726,0x86d95a3f8a6110013c4c],#[0xf1941af738acc2ce94a2,0xc64938380b01600135c9,0x913bfedd330b6296941d,0x25812e398d0218013eca,0xcec36ed2af2ab264871f,0xc6a15e3f8da148010cbd,0x4fb3a2d02f2b1a748d1f,0x868960488bc158012fc7,0xad7b2cbd2aa9b2267f1b,0xc77952460dc1c00106bd,0x13547b0abe0e731eb5a4,0x7b974430c60d0015d53,0x537c710c3c6ca2c69fa3,0xc6c972468b21b8014b50,0x31dc4efb384c328c931d,0x6709583d8b010001464c,0x905bbcdcb54bd2968e9e,0x27497e460a61180130c7,0xd2cc62f637ac229c9121,0xe6213c448c4170015bcf,0x7033e6e3322b32888019,0xc5a9403c0aa150012e45,0xef1b96cbae0a5a46881c,0x6d9523c88810001133f,0xb1d41efd3a6d72e8901e,0x86793e3f0be16001404a,0x328456f7b6aca2b89da2,0x8569163a8a4128015f50,0xeeb90d4300a22267799,0xa61924380b01d8011641,0x5033c0da310b02828d9c,0x85c910318880c8012bc6],#[0x515c04e2312a6a28791b,0x85a9123609813801494c,0x3083b0d92d8a6a3c899d,0x257910368b0180013b48,0x6fcbb6db32ab5a58809c,0x65511a36094158012dc4,0x9003a8d62f6a9a44831b,0xc721724e0ec1380124c2,0x92ac54f5b80cd2e4aca0,0x5c11e3089a1580150d1,0xcffba6ccaeaa325c819c,0x868150348941400126c5,0x520440fd394cd2de9f1d,0xc6312e3b8b01200143cc,0x10b3d8e231cb62808c9c,0xa77182568d81c0012646,0x30e3d6f0372c9ad4a1a5,0x45411e398d0180013348,0x6feb9cd02ecaa248891b,0x679463a0a2140012e44,0x301bc6dc31abe2ca8e1c,0xe779603a0bc178012946,0xb1e428f4b74c0ad0a4a2,0xe6b162450ca0f801474d,0x6fcbaedcb3ac32d0a322,0x86e958498aa178012744,0x94248d18c2cf9368bba8,0xe5d12038090118016a56,0x32d47102388ca2c0a11e,0xa63962460e21800158d0,0x12c45b003b6d9318ac1f,0x473176488de1b80166d3],#[0xd18c04f8bc0deb02a0a2,0x8929c84e0d41480130c9,0x535473053b4d833abba9,0xa7213837096158016052,0x51b412e937ec92e49da2,0x267144400a00e8013ecb,0xb033a0d5b08b1a76839b,0x479180448b61c00137c6,0xd08be4e8b4cc0aba9f23,0x87097a4b096158014049,0x307bc4d7afeafa7c8e1f,0xc5e9363c8ae1580136c8,0xf01bacd6b06b426a911c,0xa6c178478b4180012544,0x4fe37aceae8ac272971f,0xa611383c0ac120012043,0xfab94dab0ab1278869f,0x27f968488de188011743,0x326c5b01b7cc3ac4a326,0x276160498e2188014a4e,0xb2a45705b8eca2e4a324,0xa470d22985e118015c4f,0x505beae6b3cb02648318,0xc731583c0ce168013846,0xf3d4a115426e8322a823,0xc5c128410b21500163d4,0x8f237acbadaa7a287a99,0xc7e9a4538e4118011b41,0x52e462feb9cd3af0a9a5,0xc4c0f63488e128016151,0xb07b8cd4af6a825c7a18,0xa4d8da2c0840f0012a46],#[0xafc3b0d831aaba4a7f99,0x64e8f83888e108011dc2,0x318be6d5ae2929fe7118,0xa7c1c05b8d61f801454c,0xf16432f2374c62d0a223,0x45310e2f87e1180143cb,0x72443ef2b78c32c68b9a,0x8558e624062090014c4e,0x109bc2d92ee9da287719,0x85992c348921200137c8,0x50bbcee7b42ad248829b,0x85610c3709c168012346,0x6f7b66b82ca9f25a7c19,0x529002a8860d8012542,0x115c12e8338b92307b18,0x858124380a00f801434b,0x2e0b34bf2b09fa287c1a,0x85410c338880d80111c0,0x6ebb54c72e2ad2647d99,0x66013e3a8aa11001123f,0xcff3acdbb28bcaa8951f,0xe5c902370a2138012043,0xd023bcd7304aea928d9d,0x473186430a4100011ec5,0xd31c5f083b8c72fead24,0x67e9b2568fe258015c51,0xb2845102bb6dd336b326,0xc6b928378a6110014c4d,0x2f13aad7b1cc1aa48e1e,0x46b154430d0188011a41,0x522c6702ba6cd2eaa0a0,0xa5c1183b0ae1700151d0],#[0x9123fadc318b626a879c,0x66b1603b8981700134c8,0xf0388d42eeb026c889c,0x769a2460be1380111c3,0xf17beedf318b328a97a2,0x876992420ac13001344a,0xd26c4b003b4e4312b526,0xa839884e0da1e00153d0,0xf12beaf1b72d5328ae26,0x4611483d0a01000140c9,0xd0f3fee8b38b827a891e,0x6092e3b88a148013447,0x51ac24f7398cca9c939e,0xe5f11639096150013c4b,0x8cd306b9abea625c821b,0x4a8e22a07a0e800ed36,0xec6ae0a7a6a851de6a16,0xc5a8e0260780b800e635,0xec4af2aea9a97a407e9a,0xa51908358a212000eeb7,0x8cc2e4ae28c93a0e7197,0xc539083209813800df34,0xcd9b24b22868d9e66b17,0x2458d62d08012000ffba,0xd630eaca648c9e66895,0x6469063508a18800fcba,0xcc1aeea6a58829ce6314,0xa5992a3e08a0f000d9b4,0xab92aea32748d202791a,0x310a62104e0a800dc32,0xaae28094216741a44f10,0x4589263589a14000cf31],#[0x4c2acaa427c96220791a,0xc418e82e08a12000ddb4,0xcccaeaa9a4a881e26294,0x4a0ee2b0820e000eab5,0x6e533cbf2be9a2067198,0x66892c350880f800fd3b,0x6ebb62caae2ad2688c1d,0x4490ec328580c0011941,0xc62dca3a467d9ca6516,0x4bf00428a812000ec36,0x207fa0ec238406bc0428,0x981574201105e0b01983,0xd809825e056001202b0,0xac0d8309104449a1106e,0x680982a4440ab81d0408,0x4470de12c110907ae0c0,0xd01a0428b0500dc0c4d8,0xc835c2a86d0de05c0301,0x488d01e03e26b0281ab0,0x9d857050370301c30c0,0x90e07007486a1550ba16,0x5e080211618443ac1b00,0x3a2248a83490c84c0dd0,0xc00718030a8c88991b2,0x1318307441f8280783a,0x288802f8450f11f437c0,0x2010f0c84b8410ae14e4,0x11d0688b906245401090,0xd20c8282390021897801,0x8c9a172610b30192102,0xd845412a082a5110504,0x3045090481392c03213e],#[0xa048890fa831330ac40,0x100e44a311c2aa4c5128,0x804170b008600c938922,0x140a0683983423d0d008,0x58954604ec48181e0c82,0x3042100cd0562002291,0x41c4c88e30051c8e857b,0xe11a0b11e40f26887c2f,0xd4d098084c3604b0252,0x2900a00be0a0f8101042,0x884256c68890c044a884,0x482087026a2f42c27e80,0x3c0520a101a5e0008248,0x675005068430391c4228,0x700504a1c4420bb1f13a,0x1c8292a1291a20540666,0x1a0924610142363786c8,0x10b02301002142c770be,0x781202a1aa3524e4d99b,0xe00b179208ec1f43a21,0x2731552822e470a64294,0x51384b00c478bf0782ac,0x553a88d43b1380446486,0x3a03d84ab862d4245612,0x48197c3805245944995a,0xc9c424808258c1031076,0xfa9192f8421a4a11712b,0x9713c0a90213a14b45e4,0x8158e159e32229250c71,0x98394d88c544a6603923,0x3451a954322458749924,0xe8008573fb62b00054c2],#[0x2c8f10edc5f40042db8b,0xe501942fbc051f73f303,0x67f981998fb110149df8,0x187f7d70c8ac8c5951d9,0x658048597f4241a2f940,0xf6286d83373d1828417f,0xb5b0cd973f84c7ba10eb,0xd203699aeff620c8a95b,0x5ff808085ce7d49913f,0xfe715965cc154e60261e,0xe56db0c3dbf618a52647,0xc1476c6bfa32c21af023,0x5904283ea52288a188c4,0x8a2fd9f38194d87e7f63,0x1c3e7a71e8c469dc7ae0,0x962910b7ec092f4b3ac8,0xf3d49aec2b9bb81474fd,0x326bfe0c3090b56f6051,0x87acbd108f98a5197d80,0x3243b89069ff58ccca40,0x6f92451cfe6a2257a7e0,0xa5088c5e4180a0df1a91,0x1234315c53c1b54586cb,0xa4c3728518ffce9e60,0x461ee8435fa848817c01,0xd090952773f3032eef90,0x87fe1016543171186463,0xca09bf7250b2ffb9284,0x8cfe7c4a273021f88be0,0x7d0b3648f91464efa44c,0x2189e6193f0183e0042c,0x18612183a2d8f5ffc214],#[0xd84450d064932523b83c,0x422f48c72fe679427bd1,0xb028c4f314a3cfe131ec,0x6d0343f7a60a01a1aaf7,0x4b8fff4a0121765c4714,0x3bb258f1a90ba315f322,0x1100ffa51908dc314d44,0x289e62946afd106a20b8,0xf980565f7b820d7ceb82,0xbc986121e9079361a153,0x8bb4b142902988438761,0x65dbf61c95226d1864f7,0x148dff9e32033007c4b0,0x7fe4f1f2044870bfb451,0x7c687de2111fcc314a42,0x80d9cb00214dffcac27,0x6a242343cf232bbab2c1,0xfc1850090da6e4f45b75,0x131c59bd37563344aa21,0x2976e64e42926a21f79,0x194f42a5bc08dcf5bbbc,0x5068666ff0eb301990fc,0x454114f5e5f702656fe8,0x858dee2d5b118fe814a,0x517ff5ad4c10c8f0f858,0xdfed001087c3fe00380a,0x99c74a94ab785028a415,0x81a53de44c90ee241d1f,0x6a8ef00638fff20d2450,0x45250a944fa50e46ae78,0x74c150b08e6ee0518df9,0x1af023ef120b22def614],#[0xc09bf7250baf91dea302,0xcd86e50a3e7c9b6d4c10,0xbe30292b50c6de1e94c0,0xa4e19192929d0da21144,0xa85f780a48d28c6a39e8,0x488ee4fc0086869eb10e,0x119adc52c93cde2208f8,0x3e00c0520f8486bbe97b,0x50217292dad266bf0230,0xe84a1f3ef5cb32cbfa25,0x4ebba1671604507c7da1,0x466553ea3c860a34cec2,0x6285d66fd04810c9ff10,0x66122b9fb870148cd969,0x60f0914cff201322a59d,0x6006a41e249e8ab39110,0xdd0216aa4ca36c51c9fc,0x93a6e4f45c3ed724a152,0x7c288f911cc77ee67c10,0x2c3a178a2768d3fa0c60,0x94840a2f73b59029410f,0x1724179e618a5268864c,0x7ff3f32d8124875c564,0x278f004312228d0e6029,0x99c221b59b960042b3ff,0x4c2d3ffe19a802195f0d,0x454bcc5f702685a74248,0xe7e6065cfe131ede2101,0x1f2c50ccf8c1166f111b,0xa7d085114ddfa0271973,0x1e4663e2784b06868a4e,0x25e591d233f31a163f08],#[0x19a8f2c40292d0f24af,0x86c4fbf6520291bf0eb3,0xae08ba69f9825266d803,0x8c07c288eff0188a45f3,0x866fba9b8c086dfada8c,0xf9c0214991ff9c565d88,0x9b2f3c5a0424990b456b,0xc4b065860e226123e888,0xd111f314a30392451807,0xca87fe4618202129e0d0,0x9efd288085603df4e92c,0x74dbfc3425e0471eaa8c,0x3ff26202c730f0f5bb0,0x448353cd8871f64f6614,0x131f7c11b12cd1687235,0x6bf247bab7f4842297b8,0x58211a9b7c41199d75e1,0x2c8300a577f8202111ae,0x63f81a08a687d0484b3c,0xef68c9d4691af10d5788,0xfe60005207d6e80ca9f7,0x5f3f048ca2ecf2002142,0x9f6e6d18814a9fe5c0c9,0x350c26125f0b33418402,0xbe5c4bb7650d1357f382,0x10010e1ff0d9200715a6,0x76faa08084a28d83770f,0x4dd8086af3e444cb4fba,0x1aa1f6064153f8884fc5,0xddd316004333f8211b02,0xf65cfb0335a9e1a910b4,0x111fc603221f90105485],#[0x58a029adfa35f0089c41,0x8254f5c3c806593f524,0xa657a798109162edf24,0x99f67203214af329c028,0x41880862bfa456546029,0xe46c5c4a65480445d3e3,0x28262dbfa1cb4a8677ff,0x29b5fb4a844a1a67bc12,0xed3b3a833550bfe54803,0xe7f34000a52049f50064,0xe3b0540e1808a3cc784b,0xa142ffe029390294fc87,0x85a223c9d81084f8e861,0x4d8f6620426ae30261cc,0xd981c01a972c2bb7b13d,0x42180a577c5c3610a1a0,0x1d1fc06f2404029ecff6,0xddd24fc9c3ab408891e2,0x7786a04303e46e733021,0x3e005479e47c75066574,0x1926e30146dfe0120655,0x52f3f98c03021929f5,0x2229eaed25e52cdfacb0,0x40433536f8823338f6a,0x3b4f8f8584285f7a38a,0x1223bc625201ebf30c18,0x426b2496640433b77302,0xedeb1902002152ad5e00,0xc0e02965ff4a20217ee2,0x7a2c2cc1bd050338d6bf,0xca8f87d56eac1811a268,0x607c4b014840b397f500],#[0x575a6d6c6a129b13fa0c,0xa4fbd9d04a427a1207fb,0xc052cd5c7a8468bc2000,0xe83eda0cb781181e8660,0x40439dead2180a55ec50,0xa78edc294d4ba87fe848,0xcc98b091ad43a2a3049a,0xf6f8a0658ae70e2182a6,0x2972c43205bffb500cdd,0xa43f79091f142cf5fc02,0xcd0c054d6faaa502157c,0x100044b7fe01019725bc,0xb700ba04293fd7e4c173,0x1ff8004042f17e37bc66,0x1d3a8d1dfe33a44701a2,0xe42042275670656fce88,0x9574687d9fa5032902f7,0x588a4c2fe00c954f2c51,0xa27be40c6be7268927e4,0xcf8a065665a23f5584d2,0xfc13f1fd59903b2286dc,0x2010fc7ec218983014ed,0xc85ed48321bfc1e615,0x7c7fc620234410a293ea,0xcc2c4f3ff6737008087f,0x7ecec084076fd0af661c,0x3280f6676fb25006a8b,0x6e92153e69880cd5fa00,0xa03449fdcb800a9582f9,0x303313ea07708dc22334,0x4f004345ae066891a61d,0x547d330265251e077368],#[0xb4ad0944efbb4b5fc182,0x191482fd80684478a6ee,0x2b00a6969b1d2855bf11,0xc9a998aa31811847edd6,0x9baaacabf8064b7702f4,0x7e3cbd6e0410e057c810,0x5ff0040c30f02193c234,0xa065c94fb19231814f4c,0xa978fea084542299bf10,0xf10f7e3581140fcc1041,0x10230df52d41604253c8,0x63ff3e60a19d6644afc8,0x4d3533b47fec15a82144,0xb7fb314981431dcdf56b,0x7c419beffe480a426c24,0x11ae0beafda014cdf859,0x22cae6886c0229e7e0a8,0x6b3050e1894ccff20021,0xa5e11bbff240d84361f,0x47f80304252f3ffbd001,0xe36182a68ff5cf0c48cf,0xa523f22c45234042377,0x6fa1b105014c36efb938,0x147820c0543df7040293,0xa4b343583b84a41bfe50,0x7f56131046044563d613,0x804042d76c69fb6e068a,0x1bbca0c667e00546affa,0x2f461210a22dd68e4112,0xcff6295f0a5200a7565,0xf1b08a0808a4c764e81e,0x9480dfe9100cd0ff6e0],#[0x8dfa36102021a9f2fd7a,0xfd671adb49149f2d032,0xa054342adff0109c4153,0x2050f92560c2df80925f,0x40425148ffdb6384e86,0x247742e80cbc478bb7d5,0xff0a0480021d7f4d6854,0x42ed4436b7fc14893383,0xa37d2582ba6a6649a742,0x531f7c7430d375651054,0xac37f01a135c34c8c043,0xdb419efc0498a7d4cc90,0x86a73a4bd852f7e7f27,0xfe0120659bfcc180a4dc,0xf41453aa685df41810bd,0xa417cb983990b44d37b,0x187842f8405231f2f18,0x132910f078090149eb82,0x9b9f0d0405021f9ff825,0x154d7e0242be27a31a0a,0xd1011a100d1b57e0223b,0x6a65500214f25787f363,0xa8906851fc16b823c5e0,0x2718585204a59e121f3e,0x80d4483e9610a1a7f202,0xdde904052b6d06eb94ec,0x9401930ff6e120015319,0x7a4194021d4e7af08b9f,0xdaca3568fb088a1a2ad8,0x43e1f910119d571e4042,0x2ef96832a3ffe3b04ad0,0x5402229664fecc896088],#[0x3324d3a12159ff015186,0x70402c2893bea824ac05,0x3a090a9fb644c88e9e0e,0x21422dfe238602979ee,0x1919fad04841ae90d9fd,0x7080859afb1508cdfc80,0x88911f7098f1204a6b7d,0xd7fb820149cffcd8f488,0x7412967848757e40947,0x5e00547d8fc820cb97e2,0xcf1931cf845404c60448,0x10c178f9d522eb02207e,0x8777ec70a11dfe0ea210,0x92fc212915fb09dca860,0x307587b403363db2084e,0x1d4d0e8252a3ee960404,0xffd051010c2fb548242c,0x10d70a029b0f8c701482,0xba53600d4b6738254bf,0x287ccbefd23287e55064,0x259aa5fc08c4e1265d84,0xb11806880d3d54194f48,0xcb92a4e22319136ff951,0x4088060d45c75e18d130,0xd6628099c5fff8ca6e85,0x202191f8f4f1598043e7,0xcde00149b810c5ff422d,0x6eed801094db880085bb,0x223bd2d122c19fce4094,0x49c39810a883f2092520,0x401915ffd95840431029,0x30f017f2bc11001155ff],#[0xb87c01810fd777a5e521,0x81a3cafefbc2490f8ff9,0xcebea7022947f9574ce,0x9df0f3100cddff55f614,0x7dd90190bef7120efc04,0xd7e011a9878a13480877,0xe3893950665762202942,0x116fbf2380a5028f998a,0x1ea39ab8e4c23fbf2102,0x226068e333a5402944f5,0xe19c535740888fff0dbb,0xb5b430f9fe4f40042d3,0x44599e60261fa5f88109,0xa97dfd3ad30890eb5f2,0x11810fef84506b7642d1,0x21dbe10f2019b5e0e20,0x2e29f533242cbe4eba19,0x4c053df01205d4f42c05,0xee45510140a88acd2cbd,0x80d28b9abbe240904723,0x76e1429bfff540ac5302,0x7982f1d2968ef0147ae1,0xa80744244603f6785088,0x42afdc1119abfe9da1e,0x80cf9ff86303293e4f40,0xcedfcfb0c06a2f3c608,0xa0c029ecf5a318252c73,0xf23d9a92fc04847e18bc,0x3f2c01095fe1c23019b0,0x5894e6cf83e0431d2123,0x2119fc486021577c90a0,0x63a70ec63590c0fe200],#[0xd404286dc17d0c568af9,0x4b27f81c6c609353c3da,0x788292e010e274ad6101,0xac47e02042a9f002a33,0x4b2f6b9d28cb4ffc2501,0x57fb0a62e8806aa2b4cc,0x1196fc810757fa400148,0x33db553fb6cf083a9568,0xdfa48280a58ffce85850,0x37d0333b383e0d9a1430,0xc889098da6e3242e7fcd,0xccfc3203337ae280ca4f,0xd9e35980cd94f87ac066,0xeafe00c957c5e52c3054,0x9fad048caa547da8084,0x9fc69e440043ebc00042,0xf8260a890d0679f30217,0xb510d281442bee805082,0x69880ccacdf61010b4cd,0x10d01d20c81f803187fa,0xe15523d284a7b60e3bc0,0x22a813ff2e6e002a653,0x810c1e849364fea40104,0xf302e34ed29a99f83e15,0x984fe7848524f8487de1,0xbabbd0c042e6be7f981,0xfe2c96343102666820c1,0x9f44c0ccc934e8485d69,0x2743aa1da9b7c41199fb,0xa2d0fa1c182129fdc62,0xcc919c727089d6085464,0x3fb801a2182a708fff93],#[0xa933fc0b4dd019f32621,0x13179fec4960858aeec0,0xbbfcda80808691e75eb0,0x70e20880d3ce1ccc042,0x40042ebfb98800219bf9,0x8bc84d43fe6614293e4f,0x29687ec0c30262fbd1,0xd033861442f108aa5f70,0xfe5879f04404563ffa9,0x2100a51e211f3a24c7fd,0xa106f73110052cde17,0xc6484239bfa0602961f4,0x2965280ce6f8081098fb,0x9e83183d9f4572086eff,0xa8112efe3a1e80ae8113,0x15dc104c437fc4996264,0xcccc1944f73c83b84a6c,0xa7f8104082221be04c69,0x40202183f81623a033a3,0x649d0c2f0754410aefa6,0x6c0538be0a0211df06ef,0x8d149e5a41904d9ec809,0xe05042cbf549e420a582,0xe1000527dff1180a4a45,0x8a6ff4e6c7a44444894b,0x922d8f3aa4a5fb030c09,0x22f9e5a266cec28fe091,0x69133e65ed80cbced404,0x8a4577fe042010a5f5c9,0x4052165e12f640679fb7,0x3fbb60a04a08512d7cb8,0xd9db0f10a0681be1226],#[0xec678129c253b8820112,0x4487f4c0722406827fc5,0xce0ac8895dc11f6081a5,0x20c6fd4202909ff676d5,0xefadeb02222756864ee9,0x8467dde085808605bfe,0xe200213ba174065a7540,0x782000310cfac301480f,0xf049de3129705f2e11a1,0x185145a72ce1ba42ea6b,0xd7208437ffdfa28ac0a7,0x3d2a1e5f640cc8ec21e5,0xf0700541b20227d96275,0x213aff9069880a99df,0x2740530aaf5cc08507f2,0x4f4a8787aae0420def45,0x7836482ce1808af6589d,0x4b87c6380a40be488bcb,0xddcffec58948043db08,0xf6fffbf9e5da7670c08,0xaed5266ef60db2b42568,0xe70865241e0d7002961b,0x6d120cdc7d685180a583,0x53e766f4411000a80ff8,0xd9d010a47f53608640a6,0x7a208bfe5c1f81d346b2,0x6a4f968196dfea0c4822,0x4ff172002171fb0a8c08,0xbbf78c90c07b9a40194b,0x78391858b682414a8e49,0x9ec08423fced5380100a,0x50096018afc035e217bd],#[0xc7425ba04817e5845b1f,0x5b1c440448bf98d12214,0xfafc5e1a302a65707fbd,0xaa09fabe6a4610150222,0x51b13305f91f51ac4003,0xf540cdc6978820a94bf6,0x647f98ba0214f91196b4,0xc2610966897f81568818,0x8085d3e119a0005347a,0x82182fff40100a50783c,0x88bfcbca0331bfd04659,0x54a1e9ba41967e72011,0x814a254804453dfd2271,0x664fc7d18850344bff57,0x47e8b0dc50222b2d2810,0x1faa052010d3ff1008be,0x69bb2e6e442014f3510e,0x84fed805094fc9138c08,0x5febb63a848717f04810,0x3c33d81ba83475d4328d,0x7cd0021340841873021f,0xa614310283ec52080a5a,0xb27f1c0b85094c2f7bbd,0x2151e430b090b3fc7490,0x121e0e8e60d496fc90d1,0x2d5c17408737f8bcc061,0x590e07c006a7a08653e3,0xdd05280443d3fa70ec63,0x91d9c1a1baf6583293ff,0x43a3ffa5932880872d73,0xcf80105d0a2e4e047d80,0x2a4e7168109178400148],#[0x7c0ce1acc6706613e600,0x4257472f8402844c7708,0x90f27e424923d284a82b,0x536f88233383e6928588,0x9dfd00a10ccaec44052b,0x49637ffecab0444506a2,0x450a6bcf84663fe6005,0xdf8940328cfd6022eeb8,0x299350e8196deb88108,0xdd83e420021d0eecc07a,0x3526821d2ff13c0014b4,0x88bcc3a428f06757f3c,0x8c0529bffa514d320638,0x1946b9f6800295ce76e,0xd9f1211bcfa8065cfc9b,0xa00901131d3e72006677,0x1c1880877cc09cfc4de5,0xbf052021a5fa241a38bd,0xf800814b0f8e8e8c85e7,0xfa3002136fd0002922c0,0x72361b8fd49043014cc,0x4a880c2505d419f1e5f2,0x5eec99d810decb1381cb,0x43171efc9194bf18192,0xd4f8015190297fe47eb3,0x427d819ba0296c8f8a0,0xffb0309823455443066,0x22b3aff26065b3c00a8d,0xb01480ebc107d3df40a5,0x4237fafac0d50d007c4,0xae48cc3c798b08d4f1e2,0x8edf27e0a19d664476a5],#[0x6b9d88a7f6ccc00a96c8,0x947821a55f8360421a81,0xb974454d33af290dbaee,0x6044399d8481eb6a4194,0x9cbaffb3226757e8cf16,0xe14233d9659967210113,0xa02948b17f810108efd8,0x20d66043fbf07d380fa4,0x12903f1819157886c07e,0xbcfa217d25c65395f518,0x5283fe8567465862022,0x20148dfa604c90726128,0x6a406737e65450957ac,0x2a0cc2fd5cb014d5fdff,0x9f60a132b5f9dd8cd840,0x20126c08d129f5006434,0x2928eefe0c01094c2f1f,0x4207fe415b13301f7500,0x9c7c6ce0db010e427ee1,0xe2a3d7f46ae5f53610d8,0xfcc0cc6ffe74c08533eb,0x74cdb710032122273f27,0x29100c5eeed0422f948,0xafac04085b610972f004,0x49a089863d5e43620511,0x17e0160d0d2f213f9103,0x9600654663847e4c0ce4,0xdbfb2644114d278185f4,0x8019a7c243ae0d974066,0xa1ff60a42900d13445fd,0x76c08052b3cb06100435,0xc5ff83c4e50808843e],#[0x3c253b6412f0ea1434bf,0xd4120c1094fa7fe74662,0xe5454df07e600054ce7e,0x308000a847d33698c184,0xaa035e44404535fee6ed,0xabf950010b3f410f1d9e,0xeae851010c39ebf1d023,0x21731c01911ae582139,0x2c51bf620a068e7ff7a0,0xb9b290e60597d7e4204,0x51b3f1810485eaa58cad,0x2fa3aac91330220233e2,0xb2f7fc04042e9e00546,0x19b5ab6640428a2fd881,0x66b747ab00217bff5818,0xd03603f880084ee903a4,0x901a03fffca418378c89,0xedfe4f4004297970da9d,0xcbca7d00d11fc5811699,0xd3b3a83304343fe11835,0xb67242e7fa683cc067e,0xe1010f1eb0984259a197,0x67ab8dec3054a6fea35d,0xa80a802129e3fe0170a0,0x9d9d4198697e2a119cfd,0x1a7ef000cb1f1ca032f6,0xfb520a0296ee00547362,0x288029dafa5cc100a573,0x321b9fb906842be0fe45,0x18bdeef69850da8bfb20,0xb8a160c00280aa5bdc25,0xfc14229dfb4001491718],#[0xa46227128c387e301957,0x345f8092f242433ed000,0x17c9034290fdd4b1e830,0x8cc10a1fc3cdd0503453,0x9510077edd682343eb34,0x9231fc60328a5e270396,0x28f1e6002102f932b22,0x728e0cb47e01025241c0,0x93f68002911ecb1d08d8,0xf050108409baeca36267,0x215a12ba3e7d6f412145,0x51a294f3a142a4ac3813,0x11129fdfffc92f96c908,0x8c48a680a91b9d830b2,0xb378c080560891bff090,0xb4121637c908001b1598,0x483c1c9990c80445aef8,0xc01a955c5e3e40278064,0xfd77706234019b4ee1cd,0xde75159e489a0a96b87f,0x2ba59c4085acfc320334,0x33a7fe12032c5e70c452,0x79ff505014a1f7a438e0,0x534f043b3fec89e94253,0x80c1f002174ff4230495,0x7f2c01098fbbd0130a1b,0xc417c2c8844a7d4640,0xc4ea33aff8284505e243,0xebfb0b941006045772fa,0xfd3c7f6bc2a7b0406cb7,0xc0090320530bfc08084c,0x4080a9c5fcc68910a17f],#[0x4b9f97606066bbf6b48e,0x5057d4604a4e3000ea01,0x2706c487f53e00f14109,0x6f4d810cf7981458f34c,0x84637ecb1381baa88979,0xc040520bf901909bf590,0x22010a7e7933d810aa7f,0x9b033ca080881bfc0d27,0x65021c3fa438b2033b3f,0xcafc8bc8c086c78ba89,0x2eff5080a4a0beef6985,0x51edfe3602916fbc0029,0x64e3e8640c052f5f840,0x900a17eeac45494a9e14,0x9620021eb2e593223cfd,0xbfe2365ab5008ad7a70f,0x79d444fcb0ef9043322f,0x57801079d45232c2ad13,0xd28a890d5e52064bec23,0x719dd2422fc42a119527,0xa0509a476a3242edf851,0x8c814c271bdc0014b8ee,0xff6001522f1094cefdc5,0xb80555fdb30c515240a4,0xa467fbe9d8e202088a,0x3e5fa0bf02200a7cbc01,0x2be408303f4313410005,0xc780ce5791a75fcc4033,0xefc04b3c17cb847222f3,0xf902105dbd9921a4a883,0xfa9ce70184b00068de6d,0xa6e333a5402961ffe4],#[0x2af4136246a03fa97041,0xd8eb8052d69c280cb9f1,0x198216cfdcb3b84a503f,0x78440043c8f93845d669,0x5f232284463e8084e2b1,0xca42ff894065cbcc0a8f,0x950088577c0283d3d200,0x31f40080855fc02243ff,0x41122f1dd41a163ec019,0x214a6b0a0ffef9e4300b,0xd8f0020d8fc6f390252e,0xc9342ee0a91bff11080c,0xc002902bf060656f0da0,0x140d11f01c219a9a00c9,0x391f10f00c46fffe2485,0x75fa60457bd8151d7d06,0xa177a159499e161e1106,0x3f9dd4002945f4ec9730,0xbeaeb60021ded22f1a4e,0x10bca0014b17e00547a8,0xa1e9aa04088afe40032f,0x2949f991b2ca4303fe,0x801070f414c28563e8b8,0x16b6f8032007947065d7,0x19518fa02109f27a002,0xe59442abf130584ad3d9,0x5fd064b2bff2002149e2,0x7ba2a24064a88938860,0x35a0a9603f93c7f01068,0xfc232be64cc00a948f88,0x9326f8c90c16778c4a4a,0xb6c00ca8fe024e6810e4],#[0x65d885f68cae825287f,0xd9010ceeac8109de5e50,0xc9f0433e162d303ff140,0x200846f1ff15a61b3034,0x3bb47fec1485434403f9,0x9a7424281fe000866c05,0x49102a945040466c4264,0x9f7f454802554deff69,0x6f3f57ea621ca667d401,0x7fa9e7023d7f9788506,0x354ef091022296bf008a,0xe0727068d8894d0fffe7,0xf0ad18252978614eb40c,0xdc7b28043b9fb0805209,0xa87c70525fbb010f287e,0x658f24e8c96f4b7891da,0x632edf2840014adadb40,0x501922ff78a92913cf28,0x31af10e46faac8343278,0xf9f924186029ab7cc04c,0xc089062f96042d5dc251,0x983604243fc5e925d444,0x2be8593ca703f30c5293,0x1081558d96f627a9a07b,0x1605ce1ccc042e3ef192,0xf7b81265d0d77f2e01a9,0xccc81394c77f194682a5,0xc86eed1ca620022325b,0x9cd83387cf2b032c7e08,0x40448d73ed00052e503f,0xf3d1b921d5b39aef3104,0x210834e7e881019bd564],#[0xeff0f5c3b0a68f0f420c,0x1a26f023b7f455420218,0x17c997424becc9ad9080,0x9f16824333df77932e86,0xe6201951f0eed010ae81,0x52b536f882333cd1c881,0x2afc1a000a5ebfdad182,0xff1720a84872bf9c8129,0x73ed00052a1f98151ba8,0x57bfd8530251100d548d,0x42f8e60261a3c116c08,0x812271f3d35847d721b4,0x402979f3c084dfcf46b3,0xafbf321243014ec7e250,0xe55010cb02a7cc820214,0x510085ebe00805263fa6,0x1880c8050e6f10949ffe,0x1a677b5114dea8a0f9f,0x390190e40abd47e785d1,0x4253bbc9c0808587764b,0x7fe0bd40431df310bb91,0xc96f179bf803080c089a,0x2f6064ee7eb88cad2f48,0xa02162780058645e12a7,0x2239e117c8280877786b,0xe0518053b3f2501de160,0x1e214ff5d45823dc17a9,0x2df5a090a4fec90b2086,0xa4140529665b9fc20347,0xa3d5e0b800149514e7f6,0xbb9a27aa2b0287182165,0xeaedf051010e2f0414d1],#[0xe1c14416a241eb90427b,0x927e4042525e047ae2f8,0x9c1e0f0202170e577094,0xfac142355fcb0182b876,0x3806449dd4fa9c682a6d,0x3f03840005323fde3475,0x7cc0342b3d146ce8086e,0xb5fcffb52c78003450b4,0x1ff3002a456afd005021,0x7781273f1c5005640443,0x6bc08dbf4f84d2663245,0xfc66e808593171a2188a,0x86e482cbf28892202981,0xdcffc1245690c6f81010,0xef025a89433b2fea1910,0x71429978203477ea00c9,0x996fa3c04052cbe9a242,0x2fae620ce731fc52800a,0xf81a1bfce5e1cd98d194,0x10c2361f000a38ca2dc4,0x73089119d1bc520338df,0x80ff4a90d852793f6783,0x187f02b46b40d01ea00c,0x94bc73bf0415299f8015,0x71ed2602ca76bf91b460,0xe1d4022886fa81342f5f,0x6c310850f6e9f37fa086,0xee1f01965ff3228403bf,0x23fedc00ca9e7943197b,0xb569b021af0238fc1019,0x17e6b0850b9e930265e2,0x45be346739314dc96883],#[0x22140cc9d8b49aba88b8,0x57e88c6f0c8a3570e8fb,0x6e2834f84c77c44ae10,0x4673b048a5a3002ade92,0x17a273fabea34f269324,0x83d389682a4886ead1f1,0xdab341eb90e2242fb8a6,0xc2a318ee0c54b16afa8e,0x13945d1f1699d1948713,0xb44235f61a8eaea720a4,0x14df16002914e2511b98,0x9eb0a34491c9f6152179,0x10ba278788487f17aebf,0xcf112be8ec88447c9719,0xc1278e2838f2253fb228,0xfaa8c2f81eb39526a6ad,0xb0494944adef385a528c,0x1c4f0bafab1af054ae7e,0xda68391c805873b01c22,0x8266246a423d0b12291d,0xf44161e117a3992fc2a3,0x4642d7b942c520fa887e,0xbea4007bed926257695c,0x173c2dbd7b955235f99a,0x21f9bb208a44c5328657,0xec2e9a30a8f4b3e8a63e,0x44256f61b046203eb977,0x8e100fc63b408a561beb,0x1969a164e4b41524be0c,0x3c1fc32edc708bd213fd,0x333c35f1c31ebf1241d7,0xe18a46353228f98229a1],#[0x7fa5a93afdb6aa423fe8,0x5e75c24170b5c3463621,0x37ea20019927c0042adc,0x3b2f4973e52e8774a452,0x467d2e80526a6d1e818c,0xb4bcf080e35e85491c6c,0xfa910ecf7a52101f0480,0x5f8890a0055bd1f1a49,0x81e7a4f30c83cb6cc363,0xa8530d062faa02d2190b,0xf3c2a1364f46b7e1769d,0x67798caad54f29c96d81,0x7b89ec3da4e168cb6f0c,0x1c17038b6a12ce7168d4,0xb8a68382f099095d5e45,0x8bc7df0aa910828ecd27,0x7d469c3171aa8a63f1a8,0xc2fcc8a33c45b1428b5,0x2853ea241d668799ab73,0x2b04f46afa3b22129f08,0x6381a1d3d2519321cf0a,0x5c493048a382f0fbd104,0xed8747fa682a42991b24,0xa452e1fae15d44626cd6,0x28ea63afb0d9ecb4d09e,0x340433e1d7566833b7b2,0xf8890657e0254657048a,0x8fff2859f52f17138a1,0x25112e620b0c2e4b10a9,0xbc236948788a38598c6e,0xf20ab939243724e24840,0x4134152e38a0846edae1],#[0x6cfba3293e7a350847fc,0x85223f1ac06856744147,0x1b0c8a41787883ea49de,0xe451c6fc0230f1270427,0x4ffa8453c1a7d91a5daa,0xf7485a143534e03420ac,0x714c61cdf50c3c6a5e7f,0x6e60563f2942e83be8f3,0x8f21cf0807ae9e1f9787,0xc1a9308583d549c7fdaa,0x5a7437297004a53bf33,0x14a43c4610027bd03834,0x496922c1228d0ff85212,0xaf9d8e12335c4a21bcaf,0xb4c87e4b65524582451,0x413c2b1f94907934bba8,0x510de8c58e7b074df026,0xfc41ec50a5d72d4ef109,0xb3225e2514c97e151ead,0x493f792d0a4b7ca0bb1b,0x51e6a1ad3dc482842c4a,0x4d0588f2d270b49846e4,0x2198bbfb0a9227832386,0xc5d475016995bbccce6d,0x75ef6451c5]]
def g251H8 := limbs80 #[#[0x52669065140a6a581689,0x406a058a422982811a20,0x1880082415102055100,0x85a2a4464464a0844008,0x8456400211a62040649,0x50860401922015400015,0xa21102206440444904,0x211050181996a4504184,0x18580810592480685491,0x4aa9068511140691996a,0x126a241601a802168a00,0x51520204a20544020052,0x9a00406688a261905464,0x8108151609180444a080,0x69682402060202902a80,0x908a41485a014a408a5a,0x291898668001a6265420,0xa50219a9440010055504,0x2002018090040811545,0x11001159018494a04214,0x2828610089609901294,0x265510900450940880a0,0x95592210045490085954,0x58602004129940010816,0x19a2806aa252a2810488,0x4a86496922a260200814,0x111a810009168060582,0x44884a61584208211604,0xa519a285249109690542,0x5014a80580868690980,0xa5911464042825554828,0x168196001050040a00],#[0x1081501260121414950,0x1441241096516895a52,0x821291a28009a650498a,0x90281010400811111a21,0x65a8118aa82205000104,0x1812224940a18a00a441,0x91442065046402005041,0xa2955022244564609441,0x845a48a1694811988004,0x2156100011890490400,0x9114002209469a180011,0x6851284861014a912644,0x85118028824400514215,0x98009560204294155152,0x59600059a41406400480,0x92666455418624002680,0x4281445a04090808264,0x9191aaa622a041689956,0x126a05009688049610a2,0xa55a2658404811508215,0x48084841912501061881,0x19684122165194542210,0xa1814948981159845106,0x4068511016482919480,0x229a2885269845154544,0x68169a208489a2898005,0x656a5051296154242611,0xa1a28514006859601222,0x19a0516488459415a906,0x501182a88a4424011460,0xa4088404102508940811,0xa2642911269498106220],#[0x2a61112601015a69802,0x21029a806a8885216045,0x2a000218a60024a16800,0x4105428452418462a509,0xa1404182092804504900,0x2590202a989284020162,0x41640162558456801568,0x28185695106801460028,0x85294006421400a25250,0x6a4650a8502212000456,0x41041040a04105645844,0x4811a080505112611042,0x5242280816191401064a,0x288a02a986444549a055,0x8a2a1008100501961206,0x6245950aa1090400820,0x50605a88946a2020114,0x820990a8a02902a00968,0x888066269a6998142806,0x810a106046084248204a,0x10180581290a0156a920,0x34922151171b8364420a,0xb2b22a5a38e08e9256f1,0x432b30002814e0a1995,0x7a7b2886871545a89e68,0xa17a93a325036a11f919,0x5da4763d20e934974a58,0x4b89f84c32e0328d7b8,0x3176e0241e94c0519264,0x8010f0b8700c5503ae5,0xee79a49450163830873,0xe9a883c04bd8b24002a1],#[0x9def48d002049b237b55,0xce00501da43a52248182,0x7284476067e00e5a3348,0x88caf8274c707a6c5130,0x94d0215534801bf6ac2d,0x74089e304237d96d25bc,0x16aa17aa12643ec2386c,0x3e348257706b40219145,0xd4879bed970b38023086,0x1c0f63898a049980973d,0x65b35563e88227db911d,0xf1631b2700046004100c,0x13e48163e51600282642,0x6520f1e49cad9a145d77,0x9a014708d8040f540045,0x82da2860b4851c09ee44,0xfa2c150168819c65e522,0x2682082129f895d826,0x78d2023ac98839f4144,0x47128188117a47f91b34,0x5979a09a0b91207c05c4,0x63645a064d4141720523,0x7b74910e8e18cb908b87,0x97b9496757c01a22d102,0xfe0241803824e3402081,0x2ba00838a6245cc81505,0x63a131e06ab0359ab94e,0xa034efe47b0e9040104,0xa3b0a8047480cd3e4eaa,0x553ed83000ca45607259,0x58cb2abe325b377f185e,0x6ec5c6545ae0e19f1251],#[0x4d02a20000762347d0c0,0xa10823ca80f1cb1c3117,0x681811f6281b36a416f2,0x81a1691732028988c0a6,0x6100f4a3000034cd5080,0x198641380a20405020a,0x9904026ec1225048b840,0x81120450c80e468519d3,0xa518084202427ef85de0,0x861147a400a3d4208670,0xd76d517c38a84a810072,0x8a80d921c1c2d016c887,0x8963a0a92c0448e51a68,0xa8a2ac4d581f64284ce8,0x200b0d02c4411bea5006,0x1210bc80c15078508650,0x1a40c569483187292d0,0x90cea8d088206202051d,0x2452070d8c42005b1c42,0x2a1f6110e441c04136e9,0x545d82348efe0351830a,0x7d2581038fb80146760,0x188300886b10705090c5,0xa822130402411219274a,0xec2a05c5140c11d37030,0xa60555f6001801266384,0x8a0681d1291195132302,0x10a10cec491700813cea,0x5028a0524a299f70148b,0xf1704d3c20065dd04953,0x6bf31ce6024900ea5295,0x178808800052002d1cc1],#[0x417faa60105023916286,0x59898a239d78c244a48,0x521995d92b20068d0306,0x5c39a0c1a0042541fa1,0xebcd01abaa2927b2a08e,0x17c0359b90004c801040,0x10f839f9c1887518304c,0x96b019011cdb6363306e,0x4098a191d1dd812409ab,0xb00c3417069e801c9c88,0xa0a56b040211f342d018,0x99f8401040311fe0866e,0x85f00198a9955a095312,0x94aa2120544131a138d4,0x4883998ec30668e220e3,0x842b0d0e0c2137022c2,0x3c828d61010447120239,0x4ca0430081ad418c12a4,0xa560000000000000c57a,0xf8005ffeff7ff5f7f6e5,0xdf81aafffffafbfff7e5,0xfdf0367d7fbe9fefff7b,0xff998516fefbb79fb9ee,0xfbcff86a7df7fbb3eff7,0xf7fffd8846fadfbeddfd,0xee9ffcf89e7f9fbff9ff,0x7f9f9ff50bafffdbfeef,0xfffdfedbf8d5f7ff7f7f,0xedff47cfff0f05bffff7,0xffffdef7f7f90cfff3ff,0xf6b7ffedbbff9276fffb,0xfbffefebcebe79447b7c],#[0xfffd7fffff3fbb95e2db,0xebe2fffbafdbfff9777f,0xe3fbffffdcfeffff9947,0xa9bf3fffffff9fffd9ae,0xe6bfdb7fffffafffff1c,0x2037fe5f6df7fffbfff9,0xfa1f7bf5afbffffdffff,0xfda3b36fffffde7defdd,0xf7da567ff9dfffff7fed,0xffffa72a9ff77eeff7fb,0xcffffa8cffeff9ffcb8d,0xffe9ffaa7d5fffdf7fff,0xf9feffb2c47ffffe779b,0xff79ff7fadff7fffefaf,0xbdbdbff7bafb7fd7fbeb,0xff7ff7fd7f316f7bffbf,0x3dff7f61efbb31fbfedb,0xfffef7eeffffb4d7fde7,0x9fffffdfb7fd6b667ffd,0xdf55fd383edb,0x39e00,0x3a70,0x700000000000000003a7,0xa700000000000000003a,0x3a700000000000000003,0x3a70000000000000000,0x3a7000000000000000,0x3a700000000000000,0x3a70000000000000,0x3a7000000000000,0x3a700000000000,0x3a70000000000],#[0x3a7000000000,0x3a700000000,0x3a70000000,0x3a7000000,0x3a700000,0x3a70000,0xfffffbffbfffffba7000,0xffffffffbffffff8003f,0x6befffffffffffff81ef,0xcffffffffffffffff83e,0x7cffffffbfffdfbfff85,0x9b3de20057d81413bf8,0x18aa99435c7e715f4217,0xd90baa811be1d5f028e9,0xc060c96a22aa4566e948,0xb81b8d7cab5e941bbf94,0xe180a0e7b581fa296e16,0xe6c1c58f7eb80485050f,0x9773fac1033d88ef2fc4,0xab693678114bcc93f1de,0xa9edbf58e12876202afd,0xe9851904ea138f5cb51f,0x51b1dad344794cd2ebc2,0x8e3264901c0015b66fa7,0x970e57cdc95f996d7995,0x4be6e366c1b76617979c,0x6f57dce2df8576198c7f,0xde1bfaee19d0208f19f6,0x35c79d57bc85936779b2,0xd67fbfffb7ffffffff9c,0x1f4fb5ff75ffffffff69,0xea10fffef7bf7f7dffff],#[0xffa2d37ffffffefdff7f,0xf7fa4a5ff7ffddfbffff,0xffffa67effffffbfdfff,0xcffff285fbfefbfdfef7,0xfeffffaa2ffdfffffeff,0xfeeffff2c07fffdfffff,0xfffff7f7adf7dffffffe,0xffff7ffdfafcffffebff,0xffefbffbffb1afffffff,0xffffffff7deb39ffefff,0xfff7ffffff9fb57fffef,0xfdfffffdf77fdb75ffff,0xffffffff7ffffbb947fb,0xfbff7fffdfffff63b17d,0xfffffafffeffffffbcff,0xb7efffffffffbffffbec,0x2a3fdfffffffffefffc0,0xc48f6bfffbfffff7fffc,0x7c667dbfbffefffffffe,0xffc83fffffffff1ffcf7,0xfffca07ffbedfdfffffe,0xfffbcbdfffbeffffffff,0xfffffcdcffffeeddffdf,0xbffffecf9fbff7b7fff7,0xfffd1777fffff7df,0xb90c7c0fd34800000000,0x9fcabe4af2cc8d5c8b61,0x5d5500b9c5e3e325888a,0xc2a4ff22f1186c44c5ea,0xb0f75b6948d39e33b48c,0xf84550b70f568387ac3f,0xe6b3957fbe3cf326f324],#[0x47836d43e317881959d6,0x5b605746ac0d45aebfb6,0x299a105f42e0141eb3bd,0x58de85369c92b604e0dd,0xb7059f3d7aa4f3009b41,0x9e0de6df10ebc1c2aa30,0xbf14aadc479ab29004c1,0xb8d1c25ff762bfbc81a5,0xf9570480a46b6319197a,0xc2c5ea30911b6b4b4b0e,0xa0ef851b0d5edece7228,0x3c1745930b38058b8d93,0x9e36119fa7e4846c7143,0x2aa84c0c64dd710a0fc3,0xede6a71cab67d6ba4a90,0x8f8814ba6529400858c,0xd1e710103580b43ca89b,0xd313b6f59fa55166fa99,0xbd62ed812bb8eacd5205,0xb515a9415a3ad2b2c887,0x77524e5c710c9045eb30,0xb2d30ab25c652c4b712b,0x8d4dd9af175f79c0d056,0x664d53ab6b4dc6061020,0x9ae8d03a6a500ac3bde2,0x30e1675b8443aab3115,0xfab01dbfa23d03f8bfcd,0xefe2ef199bbf46f22c54,0x7ddc1fd46e3032bdaf3d,0x41564f52f6bebdb6a5b5,0x91c894951ce3892b5a0a,0x8dcfa6b7606be5c61f0e],#[0xd34b38b0df2295d3cac1,0xa1c80ac614639c94c46f,0x585763a3a6086e2f1c79,0xbb4d9dadbf75d89d5bf2,0xf0c314c98fd5169fd5df,0x5975d7d256160e9c7d47,0xf631f2a99b0dc2b05956,0xff9cbe1be2b14f7a01c0,0xba42f6f3c46d982c193,0x7a0a2455ea9d7041854d,0x54c65f120c951408ea41,0xd86984a5b46e196a29b6,0x3577a46949ea0e4c4aa2,0xbf14f834c07e8db3308b,0x55cbb2b87249b64e02af,0x37356e90fce66ea714e9,0x921d8f2367838829cda6,0x69a5207b404d126f5499,0xc926d7620d1046a65462,0xfe26f7b28e645c241d5b,0x7fa67c32e9e13ad8a946,0x71ae971c18cde20e0d70,0x18e9534e8674b53881e4,0xc2e625f1a59f741b22cb,0x57478114662f8b00294f,0x84f5eecb85fab1d5a221,0x4f236b43434a751019c1,0xf45626a218688d8e14e4,0xbab5a18085286bcb3f1a,0x8b9618e07123e8e5c806,0x272385cb4f5e767a303b,0x4bc9c34f0ab37f95c4b6],#[0xfe20f87ea6d470a94d73,0xa686dc5ce0bd48b99661,0x542ae1631b5ed8ee1011,0x2e1afb4576fbd4368ddd,0xcefe50d7fc87454aaaa9,0x7179c1d46caa6917b90a,0xacf862033849d941ceb2,0x1109eb2ac1be8f1546af,0xcad0aefe760db7ecef6d,0x44960ba1a5cbf0dd82a8,0x8dbd4220ad17ea8adeea,0x6df72258b7d44a62904c,0xb46c2f6f8d15b930c20,0x769df7548f0c6baad776,0x22b4a60da4774db887d9,0x326665221b5552c21796,0x584b53443687d2849c2c,0x5b7650f786b1f5fc6717,0x312a9f4ce362d35faab6,0xfce1a2e98118c14232e6,0xdd860b9b5b92d5138785,0xe0404e429389ab3ce625,0xf315f8f9c646ef51a38,0xc49c23a9f7579bd4c96f,0x88249aad69147]]
set_option maxRecDepth 32768 in
def g251D9 := limbs80 #[#[0x5c031590315503154831,0xc5105d4315d0315c831,0x501104c5104c1101cd10,0x545105411050d1050510,0x585105511054d1054910,0x5cd10595105911058d10,0x905105d9105d5105d110,0x9851094d109451090d10,0xdcd10cc5109cd1098d10,0x50531dd910dd510dd110,0x58531551315493154531,0x945315d5315d13159131,0xdd531dd131dc13198531,0x54540541404c5400c540,0x585405514054d4054940,0x5c540595405914058d40,0x8c5405d9405d5405cd40,0x98d409854094d4094540,0xdc540cc5409cd409c540,0x50d41dd940dd540dcd40,0x5514154d415494154541,0x5d9415d5415954158d41,0x9cd4198d4194d4194541,0xdd941dd541dcd41dc141,0x54950505504c5500c550,0x5c550591505855055150,0x98550905508c5505d150,0x50d51dd150dc5509c550,0x59151585515515154d51,0x9855190d515d9515c151,0xdd151dcd51dc1519cd51,0x59152551521c552dd951],#[0x9c5525d1525c5525c152,0x59154dd152dc552dc152,0x5d9545cd545c5545c154,0xdc554dc1549cd549c554,0x5496150d61dd954dcd54,0x5d161595615916155161,0xdc1619cd6190d615d561,0x5c164dd561dd161dcd61,0xdc1649c5645d5645c564,0x5463150e31dd564dc564,0x586315523154e3154a31,0x5c231596315923158e31,0x54a41546415d2315ce31,0x5c241596415924154e41,0x50e5198e4194e415ce41,0x5ce515c2515925158651,0x5c2615526154a6190e51,0x50f105071090e615ce61,0x5531054f1054b1054710,0x597105931058f1058710,0x94f1090f105d3105cf10,0xaf67f9ee77cc71098f10,0xbe6f7bbeedb7eddb6ebf,0xdaf5fd6f3fbfefebf6fb,0xe6f7fdfb7ddef7addf6f,0xf3bcdf2fbfef7bbebf9f,0xf7fdef77dbf6bd7f57cf,0xfdff5fd3effbbedfafe7,0x1fffffbfdff3fbfebf9,0xc4245e16045e1608861,0xd16081935d0005e01fb1,0xdd61551451dd18cb6081],#[0x551405e19f85619f80e0,0x1b5964e754838161c022,0x1f915d4e05e1602554ca,0x548d81e090965480e159,0xe1550e066141c1e1c027,0x81c56160e3550da7e018,0x5d4021dd1f91dd4a4361,0x975d84155ceec1e14111,0xcd0d6107ee50f18d6188,0xa064d5dcc88261d20261,0x98984c42602715dce674,0xddcd6148b46044105dad,0x6148ce601a8261932954,0x985d71975d210d607142,0x30d7a1ce0261f3595cc3,0xdc4ec2619e42e1cd42e1,0x69553228549ac2e16e18,0xc20ce1a0576001026167,0x61da68a0df8c609242a1,0x2e015cde11c8a20e602,0xdfe85520c2610cc9e110,0xdd9458dcc7c7e159cce1,0x28596cc461a64ae0e617,0x62d8dd0bd05dab585d0a,0x20629460017290cac2e0,0xcd61354261cb0d61b20d,0x53c2e145c261d815dcc5,0x5480d2dd4b975cf254dd,0x52dd4654dd09cc61a0d7,0x68e85961575cea372042,0xe102745486cc61a18261,0x905d854d6048695503ce],#[0x8c145d049d592502619b,0x6064525d72d75d947454,0xf290cbce60124260d702,0xcae0dd42e105d45d2e,0xe103df5973185cf302e1,0xa8a058c2a1c707615d8d,0xeadf594aef5502c9618e,0x5cf289611642e00b585c,0x9455130ce09097550115,0x2c260c957a1c40de072,0xdd47c2e1b402e01d6fdd,0x175ce04c602197548c58,0x8ad8dd83c2a1c52954d4,0x60642a5503b46064dfdd,0xd75dacc2e18602e02e02,0x1d585d43125d40545d32,0x592cd9dd42ef590d82e1,0x3790426e5531985ce9ed,0x17d05dabb55482d45913,0x6166c2e1abc2a1c34260,0x985d9602614982e05082,0x664c6020cde0452954dc,0xe16bc261c48261894d60,0xd4dd4f42e12fc9e021c2,0x8bd4dd0302618c8d611d,0x5960d761c41261018d61,0xd95900c2e14b6c54d3e8,0xefb45488b75842c9e10f,0x61dd97dce4c2619ec2e0,0xd2551b42619799dd8382,0x3247e11c18dcdc82e155,0xe16c175cc429551c975d],#[0x555cf48e60181f592ac2,0x42545d93c261a3cd6107,0x5521185d074261eb7798,0x8c6121682058c9e153e8,0x9a4c60e14d614c28619f,0x5d03d96100c2e0c62854,0x4260e4575d8e3250ca18,0xeb985dac8de0140c6021,0x61f3f79442d459240ae0,0xc2e1343254c88461a502,0xc4f454b3375442e86058,0x61ea4261cf826188d85c,0x94592e0c61dfc2e140c2,0xadd8dcc3d45d0a8260d7,0xe0424261ef6c94d3c2e1,0xad610e0260e9026126f7,0xdb826108d75ceccce1a0,0x61a9c96116a4550dc260,0x4d61b55260018de0dc8d,0x71185d320261d1585cc7,0xe1830e6008985d8a02e1,0xd05db3cd617557a1ca4d,0x740e600d02605364551b,0xdd4a29dd4a0ee0c2c2e1,0x42e1509f596ac261f1d2,0x728596059dccdb46070,0x61d29fdd84c2e02c0e60,0x545d004260d7e85d9f82,0x8ac2e00b8d6141d0dd65,0x61e358544c68615fd0dd,0x175d041761c01d590ec2,0x8bf7544272dcc887614d],#[0x5d29aadd4389612898dd,0xe8594409610d105d8594,0x99cde073685500145d31,0xe142d8dd46d4dd93e854,0xc260638de045c260df0e,0xf298dd4c1d596d42e02f,0x61d6b290ca18dcc74261,0x585d732e592ca8605f82,0x530261f495e0dd545517,0x61e98260d358546bc260,0x505db38260178ce12002,0x395dcc868549a9761f2,0x54abc2605ba8594e195d,0x37cc42c2e0dd496153d7,0xc554dd1ced5d1fd75d20,0x5504286118e8e1600261,0x4d6101e8e118d85d8be8,0x23125d44896112505d80,0x600c8de04342e12c0961,0xd85db20c601f47616302,0x244de04442e0c6685524,0x600cd85cec8261c58260,0x745487d45d2a945d3082,0xb24de0649854570ce120,0x594db454b18261a3975d,0x745484cce02094dd94ea,0x970261f0026157c76163,0x61eea4551402e1af9754,0xd75d204de062985d44c2,0xd197a1d44261ca8261da,0x610247e19907e0dc4261,0xb4606ccce0601f591c8e],#[0xc04261d568549b02601e,0x61088c60e18d61718261,0xd85cef175d0a4260decd,0x3102e0d58c60619e5924,0x60e6cde104c2e1afc2e0,0x5761d44261c70261f502,0xd0c261d2585d4c28dd4a,0x5d00105db3585d940261,0x8de0406654ca09e0e1d7,0x654de183eedd030ee0c3,0x60294d605da954ec84e1,0x18dd03c261c88261eb82,0x53a8549802619b42e1ae,0x54adc26023c261670260,0x42602777cc439761e4d7,0x7242601f185cc7c2611e,0xdd869d59249761412859,0xee00298dcd43250cbd0,0x840261eec2a1c4826127,0x54f2285521545d0097dd,0x82a1cb125d6a68601fa9,0xf542615758dd44cde070,0x61ca50596714dd0b3250,0xf4548314618142602797,0x5f8261ee4261f2c26152,0x5492c2e0d5c261c0a8a0,0xc2e10b945d6d68552017,0x8a0261278d6056cda1c1,0xdd054d607014551718dd,0x285d4e02e0c6a8553254,0xd8585d29c2e106826153,0xe071d761ce35600e02e1],#[0x19e140c261d1d0dd84cd,0x504261e30261e64c6061,0xe02069dd43d8dd9402e0,0xd6181d75d2a3758424c,0x6d85d6acd618a0d6143,0xdcc40c60e0d96140ee59,0x2e0edd8dd877290cc17,0x5728e160b75043826197,0x6010d45d4f57dcce0261,0x19dc4d97a1e4c261ed0e,0xc90e601b076158245919,0x5d955754b0d45512c260,0x9f592f2855304de18a10,0x86cee10399dd8d82e12f,0x591c4261da8461a88d61,0xce60078261d675548264,0xbd761ea0261a402e170,0x615389e0d4cce0e0985d,0x6455188de144df58c4c2,0x46f794426d590e346054,0x592eb250caef5902cd61,0x261d10ce05fd85d46dd,0x31c5959695529c26149,0x5904f4a0440ee04dae55,0x77984382e1460d61875f,0x959f5944d55cee505daf,0xe0e542a1c4545d8e82e1,0x4ce0608260e79761ecc4,0x118e601a745481d4dd0b,0x548af454b55759010e60,0xc9e14f585cf202e0d074,0x18026029026109826068],#[0x5cf1cd605e2854988961,0x68552a18dd4af4a05455,0x8399dcc382a1c582e186,0x55204961234d61b1995d,0xc2611b4260d2c2610c68,0x18c261eab460724c6120,0x594f585d47c2e146a85d,0x42e19042618919dd425d,0xc9cde14ac261db0260e7,0xe16077504268596a2c50,0x98585e49e18e97e090a8,0x399e100d95500d25d40,0x61974a20dd68551f59dd,0x1f58f3285498725cc1c2,0xc29f590ad45d53c76199,0x611f770c42cce0e055dc,0xe8dd9f94dd063758438c,0x5f4261f094dd8e955cf4,0x59330d60668e601ae859,0x8c619f42a1c7985cc3df,0x728c61a142e1064261f3,0x60df4260d382a1c5525d,0x82e01584e0e598546dcc,0xa9c261c34261c458586f,0x614c99e005cde01c985d,0x260c98261e894592dc2,0xe9cd60ddcc61e0d8dd43,0xdd24cce0a7c7615be954,0x261094d6147e9550a17,0x4ac2601ed7dce057dd8e,0x60e3cc608d0260db585d,0x261c782616904e12582],#[0xedae50d402e0f0d55ced,0x614c595d4257dd200261,0x52dd43d25d6aa8595442,0x2bc2a1c8370c4398584c,0x5daa155cf0145d94c2e1,0x261f4e8e058d754a6d7,0xf0575d304de1430de065,0x611f185d83d8dd0a175c,0x68550a4c612117dd2042,0x6958944c47615b146141,0x54f558586bd75d214260,0xce601102e1311520dd72,0xaad05dab2d50d46954c3,0x618d105967595d8db454,0x58dcc4d95d42d7610104,0x6d3250c8ae50d6026017,0x61c80d601602e18b525d,0xd2551e4c609817dd0a42,0x1202611e905926c2e16d,0xa1ca9761f057dcd44e60,0xd25d70905966d8dc5182,0x8769551dc261934d601d,0x61122860df9f58ead85d,0x8260240e6142c2e022c9,0x42e8549957dd0402619e,0xe01fee50c3155cc23798,0x945923a85918ce60080c,0xde4261f15d5911c260e3,0xdd0749e061cd6183c260,0xaa5943905d9ccd618318,0x1f5a6050826192f79043,0x60d476592a1add197659],#[0x5add88705d8eb0591276,0x36e0e0b6602a1add86,0xa0cdb9618d8f619276e0,0xf85901cfe0e23394cd79,0xecf61988fe1900fe0e2,0x591b4f611af354d2b055,0x9a590c7620601a61c59a,0xd87060cf76e184385c5a,0xdd88b358ce5a59570f61,0xb05510eb595b38593578,0x223858d6305932da61cf,0x611b0f61cfb0590ab059,0xf85929cfe19079a04d8f,0x4389cc7f960199a5908,0x59450fe14ecfe105b661,0xcf60d0f05910f6602ce0,0x59da5d8d766184385c5a,0x61cb30a04f7059102b59,0x9a5da2b6204e1add929a,0x53358d1765490f05904,0xe05070618eb659325a5d,0x7958c2f65cce0f60dacf,0x945a591e4f61d836600a,0x5cc7cfe1ceebe159f6e1,0x1add180f60d21add52b8,0x144f61920fe022eb6199,0xdd455a61499a5d50f6e0,0x2b5958b659040fe1829a,0x1af89c589a90f0dadd4f,0x61884f6168b858585add,0x9a592f8f6028b6a1c40f,0x24eb6159ab5d990fe0c5],#[0xe015e0594f38590bf6e0,0x9aa1c578590a3055118f,0xb2cfe1d95a5d6b785948,0x5da20fe119f059120f61,0xcfe0cef0590d76e1305a,0x8d7060e1f85971b06021,0x61cd4fe059b6548d0f61,0x4f61185a2062eb595a4f,0x1176e1040fe105385907,0x551b38a0454f61d8b059,0x3620ce1a5d9a1a61d56b,0x91b960c2f0550fdadd55,0x55129aa0f0f0610fb654,0x9a61eb4fe1739add84b0,0xcf8f60164fe14b1add82,0x551538594338584d4fe1,0xda5d4d1a5d521a5526f0,0x6570550f0fe0d55a5500,0xe0cf9a6170cf60302061,0x5a5d4b36e1accf601d8f,0xa36b5519cf60524f6023,0xa0d91a5d51b854c7da5d,0x7858c75aa0c9ab59446b,0xb2dadd9a5a592fda61ef,0x5d90f89c4df6e02cda5d,0x8fe199cfe02b5a5d1b1a,0xd29a5d902b595a8fe198,0xa1d98f6190cf6150cf61,0x7621c40f61ceda9c67da,0x4538584dda5d99f658d4,0x9ce236e0d47661acda5d,0xda5ce83059235add8dda],#[0x19b050d8b354cd76548e,0xa1cb1a6062f66194705d,0x9a5ce236a05ff85450da,0x51cf60d1365921705922,0x61949a5d4ef620e09add,0xb8606f5a61f3b0590e4f,0x73ab55197958c3b6e060,0x6196f0a0e1da5da32059,0x76548d4f614d7654928f,0x461a5d9b1a5530dae186,0x60dab6610030614f5a59,0xf6e1000fe1a230592a8f,0xd04f60d19a20504fe0cd,0xe015cf61873860738fe0,0x7958cda058ceda5d529a,0x1c5aa1c59a592bf0a0cf,0xdd83cf60e8b660002b60,0xfe1d8b98c4db0550d38,0x843960cd8f60da4f6191,0x98ce30604ea0591976dd,0xfe06878585a5a60c9b6,0x921aa050b9cc4d8fe150,0x6061f059128f61529a5d,0xf0602d5add451a605070,0xceb850c7da5d19da5d51,0xe02a366124cf618df0a0,0x7858d40fe1184fe0c576,0x804f61878fe0d9f0dd05,0x61da6b594e4f61d94f61,0x36e04e39dd83b95942cf,0x8079604db998cdb65900,0xe1d99a5da25add871a5d],#[0x385c597961038f61d98f,0x340f61dacfe14f1a592c,0xe0008f61914f61ce5a59,0x4f618d0f61a34fe1408f,0x62cf60db1aa0505a61c5,0x550d7059230fe0501ae0,0x786045785507dadd85f0,0x457059110fe0d94f6184,0x602576e0ce1aa062da5d,0x8fe028369cce1aa0d060,0xd9b85c4df620609add9a,0x61aa0f611a4fe19a1a61,0x9add988f619a4f61aab6,0x6ddadd835a5c67cfe04f,0x618ab95903b894c7da59,0xb059036b5954a060258f,0xcd9a5d4fcf61520f6188,0xe16b5add4eeb54cdf99c,0x5a5ccfda61508fe1864f,0x594fe18e4fe1cd7358c4,0x60d0795c4d8fe00b389c,0xcf6192b6613276605fda,0x52f6e1327921c270590f,0x60515ae0507858c3da59,0x785d47cf61820fe01ccf,0x4ecfe1d86b60591add84,0x5d500fe04e790c4da059,0xf9584db6e0c43055121a,0x22da59745add83eb551a,0x619b3890c7f06194da60,0x7060ce9a5d525aa1dccf,0x88b8944d4fe14d5a5d90],#[0x61259a20d05a58ebdadd,0xcfe04f2060e55add87a0,0x10385c58b05511f66024,0xe1451aa1d57654923055,0xcf61519a596bcfe05a0f,0x25f6e03078984df6548f,0x55125a61dccf61524fe0,0x9a5d4f36612a1ae0d070,0x225aa1cfab619c5a5d40,0x5903da61c09add053059,0x1ae022cfe1cdcf6051f8,0x1aaba05930590070e110,0x5d68ab551a5a9c623059,0xcf6151cf61cdf859089a,0xc41ae19078605cda5d8f,0x6016f6e1aa0f61dab658,0x70616d4f60265a59490f,0x8df661b25add8e5add4d,0xe1ce70590df6e10a4fe1,0x8f60c9b96182f35cd14f,0x6b7358c78fe02f7960c3,0xdd8d76e0601add1a6059,0x70a04e8f61499a5d67da,0x25adcd89a6140f66014,0x4c4db961839a58d2f959,0x1a5c621a5d925a58d739,0x26b55181a5d2b0fe0da,0x58ce1a5cd9cfe14579e1,0x8fe028785932385850f6,0xf0e05d8f8f618e5a591e,0x596c5a5d8dcfe1195a60,0x3858c3205945799c4d9a],#[0x16b85851385941f85533,0x590a4f614d0fe185cf60,0xfe1cf36610a786045b6,0xd306014da61905add4b,0x551870a061f8a045b059,0xcf61181a5d4d78a05ceb,0x4d795ccdb0604f4f61d1,0x5d9139984d8fe0e83898,0x8f61964fe19d3398ce5a,0x84b660c4335cce795d8d,0x5d4f4f61cf36e1b24f61,0x8f61837858c6dadd1870,0x9ab660304fe1680fe0d8,0x544d5a5d68339cce4f61,0x7858f18fe01576e00a78,0x2a2b60d936e124dadd91,0x61d15a5d335a5d8d36e1,0x366130796142f85946cf,0xda5905da5d73ab591c,0xa0cfb898584fe18d5a59,0xba59183a601cfa604f3a,0x50fa58d13a58d0fa604f,0x60157a58ce7a5d98ba59,0x7aa059ba591a7a58cd7a,0x4d7a5952ba60cfba5d8e,0x58cdfa614f3a5d8d7a59,0x3a5d4f3aa04fba59187a,0x59ba58d8ba594d3a600b,0x618e7a58cffa58d23a60,0x7a60507a5d92baa04f3a,0x2f7a61d9ba602b7a5d18,0xe0687a5d1afa59527a60],#[0x7a61903a591b3a5cd8ba,0xce7ae022fa5ccf3a6068,0x6000bae0287a60503a61,0x7a5d52ba60d07a5d8dfa,0x22fa60c57a5d9a7a5d19,0x6140ba59523aa0da3a60,0x3a5d9aba61a23a614b3a,0xda3a619a3ae0e2fa61cf,0x5d51fa616b7a5ccdfa60,0x7aa0d07a5d917a60287a,0x73ba61cfba60e23a2068,0xa05a3a61503a59503a61,0x7a5ccefaa1c5ba5919fa,0xcd7a5cce7a5d183aa068,0x61457a5d4efa60e2fa5c,0xfa5d1a7a605a3a6105ba,0xfffa5d4d7a61907a594f,0xfffe003fffffffffffff,0xfffff081ffffffffffff,0xffffff880fffffffffff,0xfffffffc607fffffffff,0xffffffffe403ffffffff,0xffffffffff281fffffff,0xfffffffffff980ffffff,0xffffffffffffce07ffff,0xfffffffffffffe803fff,0xfffffffffffffff481ff,0x7fffffffffffffffa80f,0x3fffffffffffffffd60,0x681fffffffffffffffec,0xfb80ffffffffffffffff,0xffde07ffffffffffffff],#[0xffff003fffffffffffff,0xfffff881ffffffffffff,0xffffffc80fffffffffff,0xfffffffe607fffffffff,0xfffffffff403ffffffff,0xffffffffffa81fffffff,0x3fffffd80ffffff,0x2e000000,0xc0053a02b2000175c000,0x96107e0e800c7a0a1a07,0x961b40191616ea14a212,0x1a26e624ca22a4203c1d,0xe231ce2fb02d8c2b3c29,0x9a3c5639f037da35e033,0x82470844f2429a40d63e,0xb6520050184df44bb849,0x7a5c305a4c580255e253,0xca671c64ba629c604a5e,0xa4733470b86e3c6be269,0xa67e9c7caa7aa0781275,0xea89d08766850c82bc80,0xd894be92ca904a8e208b,0x29fc09d649afe98d696,0xc4aac6a88ca640a3f6a2,0x2cb5aab336b136af1cac,0xbec15cbf16bc78ba48b8,0x96cc66ca3ac858c5f2c3,0x32d706d4b6d276d084ce,0xcee1c8dfc6ddaedb92d9,0x82ed04eaeae86ae5f4e3,0x88fab4f832f568f2acef,0x2507ef059d02f8ffe8fd],#[0x5d158f12d1106f0e030b,0xf3227120711d911b5d18,0x752fa32cc32a5527c124,0x513db13af93827357332,0xf54b5948cf45f5434740,0x5758ad563b53c3507f4d,0x366fd637360b55e115b,0x2173e371176ee16c4b6a,0x580937e417b21787176,0x8b8d958abb8803850983,0x879b2f98a79605933390,0xc9a8d1a599a33da0819d,0x25b6d5b41db0e3ae5dab,0x88a401c05fbdd9bb85b9,0xc27888013084b6d5e852,0xe8c318b001207a32d4e7,0x90c6f2789801237eb555,0xae9206b2185c00fb6bab,0x62a9d0a571c884010a72,0xe5642d4fc551d88800e4,0xf168ac51a541c05000,0xf400da5f258e86026070,0x50b00104773253888308,0x11c88400f766ab10a652,0x676230a000ee6aac1166,0x922621f09800e66127d1,0xae51e732a0cc011b75ad,0x6cab5186f22888011077,0xea63aa522712609400f6,0xf66c2e52a7a300bc00,0x7400f06f3152a6f23894,0x880010d74b4134651e0],#[0x31f88000ea5fa89045d2,0xa662006c00ed65240fe5,0x8fe6a2586c00ea61a8d0,0x26cf8641c09c00ef6628,0x5b281166b1f87000dc5e,0xe6f2fd347b2b0c000ee,0x1076eadcf8612006c01,0x4400fa662b5186d26884,0x78d000cd5ca28ea43170,0x81f88400fa6fadd2a742,0xc7e2b88400ea61285206,0x13a832b080012175b456,0xacd22702009001066faf,0x6cab522712a080010d73,0xd352248e8551c89400f8,0xc352a20da4c1a88000,0x6800f768a89085f1a088,0x9000f26f2bd1e761d8,0x91806c00fe6d2c8fa5f2,0x885278b800d154a40e44,0x8ec581d86801147bb614,0xb2132661c08000d059a6,0x5c29ce65a1d074010972,0x137b3214075250bc00e2,0x12d7ab195072258a001,0x9000f062278de491a860,0x98ac010c78b25426c240,0xd1d05c010f69ab50c6f2,0xe84320ac010a7bb35286,0xd8a922d884011d743013,0xb214671228a001228236,0x63a910e6e22880011c75],#[0xd15a264f6612089400df,0xd358a610e692789400,0x9000f66e2b92c7c290a4,0xd86c00e55aa6108682a8,0xf2a89801067430138671,0xa5b22080011e7eb4d487,0x9326b238c400ec6bab8e,0xab5165e2007000f0642a,0x80b412879300c800f968,0xe05ba44ec5f260a0011b,0xe55ba54ec501f89c00,0x8800ec6228d106221074,0x690001017130d3e79250,0xd2709c01057031d568e3,0xe6f22080010473b19186,0x8f4631e05400f65daad1,0x28912732a09000d85d28,0x6b2e114582186400f665,0xfd6fac5145c1f0980106,0xd75a24904551a84400,0x9000f46a2ad1e6817878,0x40a000e25f27cf2611b0,0x82107800de63abd1e662,0xa7d2b0a4011e7c359747,0x912641f87c011c793193,0xad90072300c000fd69ac,0x7b32558882d8a800fc68,0xe9672d51c6e248900117,0x10575b2948792a89400,0x7000f36a2b0f861200a0,0xe8740104702bd1670240,0xa1b86c00d35a275005c1],#[0x2721c8a000ea57a54ea4,0x50e512006000e4652b51,0xa65065f2108c00db5e26,0x6f2d8ee581f07c00e15e,0xf85e27d0860248a400fe,0xee6a2e928591d06c00,0x78010e7331d387929078,0xb87800f86b289025d1f8,0x61c85400fb70ad9266f2,0xa6c1f08400cb54228d85,0xcfc571b88000eb5fa7d1,0xb454883290b000ee682b,0x742f9266b230ac010c75,0xdd602a5166d288b00118,0x11277b393a782a08000,0x16799c15748e378f0,0xb08401347fb6996a6419,0x834098013d8eb715c8c2,0xc8d2d880011d82b995a8,0xd0a712c8c4013684b8d5,0x3395c701c88400f26aac,0x823d1889e368d0013a7f,0x27434d3a862c0b00128,0x169a044ddab6450e801,0x8801418fbbd667a280b8,0xf868010674ad11e77240,0x8330f401076e2d52e6f1,0xc6425094013184385528,0x59c933687c012079af52,0x2d13e6a1f87c014690bc,0x8fb5156822e8d800fa6d,0xe368aa10e5d26898014f],#[0x11f7cb4938832b8a400,0x94014c90be19aa9360e4,0xc8d4011c7db113c752b0,0xc26884010e76b4d5a812,0x676270c0013e852fd3c7,0x150862f0c80131883a57,0x3cd9c892b87c01408abb,0x88365648e2f8b4013a88,0x337eb7d666c17038013e,0x1297f31d3878280c401,0x24015091b695c9431108,0xe8b001398a3b5748f349,0xa2509801438a3613e832,0x85f1f8780129843a5867,0xd1c5d1987c011a79b213,0xbad6c8b318d0011672ad,0x76b355c712a0cc01709d,0x1874b011a6a19850010c,0x11d74b5d80902483801,0xc8012884b75568a328f0,0x88c4013d8aba98c94300,0xc31098013e8ab7d5a8c2,0x29b380d4018fa240dac8,0x91e6c1d89c013f8c3b18,0xb85628d2d8bc00fe70b2,0x75b31648b35114012c84,0x4390bc19a983408400fd,0xfd6dad9347b308e001,0xdc010064a9d046a238d8,0x6110013587ba18ca23c8,0xd20080015795b7d5c7e3,0x4832e09c00f9712dd005],#[0xde521e87c011a7bb915,0xba54c792a0ac00cd5321,0x72b1152842b0ac014d90,0x49963816c8b260a00129,0x1508f3c55e862f0e401,0xf8012c87bc56c90270a4,0x1874014a8c3d1b8b2400,0x422880011679b85446f2,0xe6b23098011b783211c6,0x95a912c88400fa6b2d51,0xbd19aa23a93c014891bd,0x712c50c5519864013d92,0x72a0c5da496358f4010e,0x13084b8d9c94308cc01,0xc4012b803755c792d8d4,0xd0a801107232150822e0,0x5268800172a641572902,0x67a2288c013c87b856c7,0xd4a7d2989001087934d3,0xa9d04632286c010a72b0,0x76b294a7828098010469,0x8079b2d487f298ac0114,0x840cc500bc356104bc07,0x220904ca0c3fe10320b2,0x8104c250e01f15702e04,0x8603703618270c282219,0x850551102411a041d07a,0x34c1085a17054143b60d,0x120db836090da009a844,0xe0ad06121800141a05c,0x3726c570703d26605834,0x840109309b82c191a00c],#[0x1b8188001c0108601018,0x21102302c978540220c,0x4058191083a25082145,0x170211b86a03c010e081,0xe20516239030420214d,0x1d4252f8ca1724a12406,0xa1061b449150502803d,0x10d198742e13e2c4b0,0x54274404c8458bc902c0,0x1fc461e4c2344851384c,0xaf1352788896c343927d,0x56a68950321066818810,0x9300bf148a1126218e0,0x4a1388d2cd0711cb847a,0x1487e302b02982e008e8,0x8bc393840224a393b28a,0x194d0b2859100c599494,0x383bb0abfd5c60047246,0x810dec5d1321dbb0ee54,0xb383fee0a62436bcb408,0x64f5b3e9accdf4f17626,0x33dbc1d5908dff936026,0xdf30a81e068cfdbdaa0a,0xdf71f04464c3f8b68ccd,0xb40275eacfc1d7412067,0xedd8b28cfde8b428cd1,0x8dd8505bdcad3904110d,0x48685dc5fb148dc809f,0x7260a1525a4ebb598dfe,0xa9b754d66ee30dc65873,0x1b7a1c132aff5718011e,0x78a59d3e90da419a21e3],#[0x46b43f7d98003334670,0x94cd5686e878c7437aba,0x2052085f65ab5cb8537e,0xbfa003346dfa8044cf6e,0xf851032f7a4840199bc2,0x114ecf0923d4820cb9f,0x60213bdb3f024e675e17,0x91eed0194bf2806457c9,0xc01101e0eee84aff2c0c,0x20b87e9200cdbd74220f,0x647b809cfd93a40a302,0x30329f81193abb061197,0x36426934b718032063ff,0x3006555e9eb8466ff94e,0x2244e702667f12084aec,0x811ee4a8c7485256fcbc,0x5bccc6d92d7c24dc219f,0xe248150caa7808b1b57a,0x96be35f815b4c90d4cf8,0x864fe04c021734fd801,0x5580215bfc68a180cf37,0x4691aa01f9093ec21eb6,0x34228fd2908b3fbe126,0xaefcc4c02177e3d99167,0x842f3fb0371983ea780c,0xaf6063c0fc9032d38ac0,0xdfe84d8085afca45e066,0x473e52805203a6280214,0x85cfa539c0ccabc04,0xea9401a1785c045c7fa4,0x24932ee421afb01536f3,0x556b5a2c3fa6f4196b8f],#[0x7cd5f194b333d2ed24a2,0x14a0cfbe0fb708c9f20c,0x10d0f5a678e866cc3f68,0xab00d893c1a05ffc0d60,0x220a1e9f828880cb1a21,0x401145fe881080fa85cc,0x53fe0800cc797e04abfc,0xf240caddabac0b9a0349,0x4fa310594bfd1001943b,0x89edc3080336fc662646,0xb4033c7caac1953dbc0c,0x5f5c0644a7e03257f3ae,0xaafcce70214bfe0800cb,0xc09078f3011696611c10,0x2a43e9b0654fd801903f,0x41e1c7509a43a7f89e03,0x7bc68222ccf5f81a012,0xcb40848f2e1906517981,0x481db4e00cb9e0983233,0x4085a7c35c2100fda309,0x349a35e404008537e48a,0x8e7026fc01103c975e1,0xf03422b609c1905e8241,0x3000ceb44394368721a7,0x143f87d9f60bb686ffae,0xbb7013d7f887032c9261,0x8227a0f222109e0e0210,0x2e8b065cfc2858328fc6,0x6d63c330910dbf5a045a,0x455fa8d0452db861006,0x72cb00a033cdc21ceb3c,0x73c78fe670a46693c118],#[0x532370c200ca1fbb3419,0xaae6242b3e50b0216b4c,0x11a7c46845c7908109ea,0x241091974e90199561f0,0xfaa9a0006889ce04ccfe,0x50065dc42187f64064af,0xa720cbce00d1ca4327e1,0xe11c7f58d00666405cfe,0x45af60630f6f45990678,0xacc08417d4e04221e7c9,0xcb3fe60899e319065f6,0xb6420f3df952670fe824,0x40444fb086bc843e60fd,0x675bc68229be8d816d4,0x942de3c4266ee9f97004,0xe12175c9e04257e49841,0x9a8081a396e504263e28,0x7f1822361fd90196bf5e,0x836eda403297f9430196,0x49edd2d910c814483d00,0x2deda388286effd01819,0xe8419f03f240cb96e419,0xfe80192ba1c0196bfee8,0xcf6fa60212f02fc84e1,0x11b7df86032b7f2c4b88,0x5a09a571086c780ca38e,0xa1e808ce3f4438f0e4d4,0x26b49535c43b5c244c3f,0x8a0085ca7808b239e546,0x47e2b02103f1a00ca0e9,0x243c7a20649fbc4a9947,0x1933b14a0cacfd1003c6],#[0x60cddf1b68e06704fe0,0x3333c500210f04709e5b,0x65e7c80042574ebc90,0x33378c350a6bbcd3141f,0xfa616c90209a43eebd40,0x400350fa1089439c09bb,0xc0108db7a0c8d5d69c41,0x83397f9f5813302d34fe,0x2b02102e38440e3b8786,0xfee0ea047cff0c00cb4e,0x880646fbf0c06513c218,0x497845ef402ebd80680f,0xfd604ceb403c05f5083f,0x11a38475a57088b307f2,0x933fe2dc38001a3243f0,0xaf0422c7fe403257d701,0x61e00042725bef14833e,0x7e0461fac60066bf2409,0x1d644affa0c8dc560c8,0x207d85d7855685d8123f,0x3d043afcb0064d79a004,0xc560c91ea410659c3088,0xe831865fa0c95e98a64c,0x3d033df0473ac3e02317,0xd2c22a26841d215ab2db,0x2580858f337859bad033,0x420f86e89594ec196183,0xbc996b34840689d7e920,0x60675fa8d04515f4226,0xbae5a0423fc0237edecd,0xea0c80e0d9072c307010,0x3694c001a739720644f8],#[0xee0523077b136fb31784,0x63c4e1105fe850042adf,0xd3f5c3c23ae8e112ab4c,0x200332ade1107e948455,0x87802488f520832e17fa,0xaa0813577a4941977f7f,0xb2146987800109d9e91d,0x11822dbb340842e166da,0x7c1c042675c0c878239f,0x1832ee4df08ade5b0643,0x88da700641eb422479e4,0xcfb9d088187b60c9ba90,0x1fb461203427e1dae828,0xf180c93c4ff9c50123bf,0x16ba1c01959e0ff02113,0x58ec0468ebc0326f1701,0xdff5a62133ad03738445,0xe12679a7c0ef01223846,0x44dc95583e14941dca61,0xeb19c2db57b60338f138,0x90e1fb52600cc1164fd,0xe0845afae032635436b4,0x9705e19436f2f1819a57,0xb48110088e66e52e2cdd,0x6c156ea6b339c09bc4fa,0x33745bd3220a6bb4ed28,0xb878c95ec0c65cfe1b01,0x806747cbc10215fe0118,0x911ff820032c7fcdb26,0x10945fa0c83fdad60b,0x75500cd9fa60c0ca4ffd,0x3011d1ff12a0c1990e1d],#[0xb01143ebb0d91986cfe6,0xba1f7541209fe00109b3,0x89dd9a0c91fd91a00ccb,0xd3603317cd865066dee0,0xd0dffe93ce40104d25d7,0xc832c750630f05e6133a,0x8f1fd03951a09a23f8a,0xfb7260a990288dd2dfc2,0x75a27021d472e8280cfa,0xc16fc11099c3f97eb026,0xeb8191bffb4b4c40c0d3,0x1983b43d8cbd4e4192bf,0x3fdccd4c3021d3f0b690,0x20440fed9011bbf70323,0x79dc662911683f2f0201,0x831a6df6732c0069b7f7,0x9f11a1163f67786acd5a,0x314c8abdfe0008fb8843,0xa62221fb5db8b6019ebd,0x700ca1e23fa86596677b,0xc0cf23dc1e1f1349cfba,0x100665fa8d04548fe511,0xfc01129faa11e90b5e0a,0x31d65e851656c8b8320,0x3c77fcca4e2c66242d7b,0xe1106f9be117508e1160,0x4c991ac191bf06064427,0xb2759a3f02d40199b02e,0xf5d088c66ee84f52f677,0x2c7790963846aa3e022e,0x37fe6e98828d01f70803,0x2fe94a20850ee1fc2833],#[0x8495e9a3193f9755010b,0xf9031e7ebf04400ce767,0xf319ec4b72821771087d,0x36170114e611a7f6aebe,0x9a910033b652c192f409,0x7fe473cacb372526a7fe,0x33093498700cb139c09b,0x6de986d8309111becae5,0x903db2f181983e67bf99,0x32f6d87880666fc181,0x2664dbeeea5c0d15ff96,0x338517abfd94bcfed18,0x5aff8b0641983fe8f6c9,0x7838084aef849de83606,0xfc226720634ed5fc0652,0xa11ebff6ed588004d284,0x5f9100651fa21adc3fc7,0x65ce018ebf5d4696c8d1,0x179fcccca40866facbe0,0x8ff480010adfe68321b0,0x658e520644c2d87860cd,0xd5019cbf460640fb3f9d,0x3400ca5e9841329732c7,0x5d220c9db70c200cd1fd,0x91e1833d7a7fe74150ce,0xd42f0320eafb84a1e50,0xd82900cedd086be6546f,0x1cbf2c06557f020fbeff,0x69dabf80cb5f949920cc,0x11fa9c832475063af84,0xe04a5cfe1e82665df7a8,0x16e3c096dea935642d7c],#[0xdc5f808bbff994c23330,0x9e78fe8b69223bca1865,0xcc3e13845c7fa400085,0x3bba169fd802103f58c0,0x64f4a4832f5390649518,0x16e832ce0434fe50d006,0x964480cf1843fb3ccddf,0xcc0019b3f2fa6e65cc3f,0x23a2bf81093acf0117be,0x3b7ff6b265e9100351cc,0xc96c1c58848e8c3f7083,0x35ed90963bf81933ca04,0x83d394694067cf94c583,0x4d1bbb5bb0b1dabdb019,0xf001aa44e2a425b47408,0xc80fb040842ff220c46,0xf484516163b86a19b296,0xc6a500670bdfe80465fb,0x22ace022ac7f9822b65,0x19fbfe9a154d8b63536,0x5d87b19a9c849851f817,0x2467206391ff6c608e1f,0xf83032179031af1cacb0,0x4669fb0032837e0c0cad,0xe83e1a3277a5b2a8103,0x5f59c020cddf5a639f61,0x627186ad05fb116ac0ce,0x93d60c0a90cba38440ef,0x19f6fdf957c68495e421,0x21cbf46064af3f2c980,0x3216d43bba135e0a6000,0x53f60064ad3463c7f205],#[0x26f74c085dd9ebda8412,0x27ec00c82fd19ac80431,0xf6f600658e11e17f8632,0xdaf4c300067afaa8065a,0x5fa2732c70f500cad808,0x32fd18192b8fc1001982,0x11e7f3f55ef9340951c2,0x8800cdbf2f08933eb87c,0x2a6201295f42021383fe,0x3308fbfcb041947fcfc7,0x742d7b031f7b130fc967,0xe1026567c701084e5349,0xc0703353dd4c04086087,0xa1f889322309364277ed,0x111563b01189fca9e110,0x22ee752708d1eb18e6b6,0x9001119fae140cbbf0a8,0x314a278081454b67f91a,0xceb0f808ddd9a0c9cffe,0x90d3fe6088ad02e4a42,0x3337feb888019e52e954,0x101995f210212bfd3070,0x434ffe5c4402404bfd0,0x21110a31c90b6fb7188,0xf0ec00cbb487808d6d1d,0xc2dd534b3407d8ca5983,0xea98933f2909e9490658,0xc049efcf324600683602,0x804a10147c42595e6c7c,0xcfd6ac1936f4bf3c56,0xaa00a59ff30440fe95b2,0x339610acfd445a20ff8],#[0x9a30fabfde65ce3b76ae,0x482117bcfc600090451d,0x42cb67920c20e04473fc,0x2065178b43042fb6c500,0x73810b4f8399081f5e1,0x5a4d1e27088b9c84407f,0x7df04019a47b92b0c4e,0x7f08a832d78163990034,0xf1854019abe0f683033c,0x66432fca0896c9e44848,0xe1257e3a020335b6f8b0,0x34662b064378243421d9,0x47e6c3283337f0e13520,0xc8b77781a1221cd8642,0x200cd045f3df00925c32,0x70e0cc8519c308a1fd88,0xfcc00ca1e54f51c0068b,0xf9506487fcd820090c5f,0x8a4de5c808da57aa08d5,0x4ee40c71d78064abd009,0xcd808a5fa303233cb408,0x50dc4241cc23535c045d,0x6957f020c9e0e02107d5,0x724c833b7ffcd4ebd240,0x888e11f7edae00334781,0xa4d5d089cfc175b1019e,0x8937075fd806453d5200,0x913e12fbf54e2c62443e,0x8456688e11cfcfa0a023,0x7dd380651f108bfe09c7,0x4b2116cf01160afe0426,0xbdf96064cb52f08d0fd0],#[0xca5832d3e0491f1d380c,0x42077e12238710042876,0x6be95061ed4e1935c9e0,0x76d3028021a253e3a832,0xc5ba0ca9f5f5500cc6ff,0xf887090335b264c1099,0xa02032e72063a7898084,0x64497c15193a9e03217f,0x341b013423fb92ab0380,0xc91d6441973119324785,0x7edf4b76546c690ff400,0x132bf81075b0784cb32,0x77a70c91e3e4900cd4df,0xa2643307f4f2320ceb44,0xa1c0a0ce1fd0481973f5,0x7a728883305d9f8456f9,0x4217e500c98c1d12424,0xc067c194ef780a3d79a0,0xd61c4c004403ec102133,0xa320f1087bbea4ea37b2,0x12bf2c2c858880d49f82,0x272be115e3e8021667c1,0xc7d0844e0fbaf500ce8f,0x64d7f9000845e421c708,0x4dde1e0324fb0875fd80,0x940a1d132f8c329e1ce0,0x608ad87880650707ff20,0x490650d00baf601a27c4,0xf4b387844732b9c089e9,0xe7e1422d7b0318779960,0x81a11e983d0213a9831e,0x2129cd6dd31190fbbeb],#[0xfaa401485fa30320bea7,0x81a24199d37aaa8121aa,0xf1a08cd5d79545e069ae,0xa7c4224fd25599c1260e,0x3ca8f4d6092b7e3f048a,0x230f13844f7c2a00810d,0x66afb0059d67dfff2c0,0x929fc2d99e33761ff028,0xbe325af08fb3df48fc20,0xbc232e0cb96f197f0093,0x460643a6f809e38dc191,0x601a2cefc04d9c818d3f,0x981a22fb84118a5b5b8b,0x118bf5c28195be1f5dc2,0x571befc1aa6438fc738a,0x8e86a69b4890a9d7a206,0x6fc1b8c0201128d5a11c,0x6e046ce4584bb850d30f,0x45333767f1642a033ec4,0xc788a218b4e87a5748dd,0x68d8bbacdeb3e4a57ee,0x3b626b8101b3b1e0e708,0x9ffc3b66354101acbde8,0xbdfe64506555d7f008c1,0x2ca880d25ffc2e065600,0x655fd73f2011db3fcd,0x1a79bff10c6800d0dfa0,0x2df240652fe7d464b00,0x3e202bd6a0c78e11001a,0x2e091dc8ea0cb1e36f0e,0x45277de28ccda238c,0xab5fee08aaf6c4b9002d],#[0x789c140001aa3f8d280c,0xc1964701106e3702327e,0x6001abdec10211be5c4,0x7fb9bd2400d05f0a71b2,0xf2ed3c6104bd7ba97421,0x30a650346aebac408e3e,0x40682f2fecac050682e6,0x893ae635cc8edfdb008a,0x7fe017450ce7a049b910,0x227c958946346274238,0x2f800084073f46072240,0x28ff3bcc2430d27f8049,0x1c116bfffb8bd36a4069,0x91a253ef4894b81a37af,0x8ac14801bfdf5d85c8c2,0x8158cd40698cb3906bce,0xcf2c8dce1a8540894fe,0x7d5c2c7c11f3ff691694,0x52065d9422ffc936a406,0x31921b79eff000472fda,0x19e7d7f0ee0123cef56,0xe84025d7ec630ffb1c28,0x5bd9c096a984ab2bc2c7,0xa0aaec020443bf4b0c48,0x3d2b24046e908acdfeff,0x6480d29b79f5520cf1f4,0x19d3bef146664eff05e6,0x8af0fc8403367b61c8b0,0x2cc19819c30c3c30ce06,0xff5e88199be689065aff,0xc0d4bfe06163f0804aa6,0xdb0a740d01cb8fc6055d],#[0x63780033a7795f8cb851,0xff851032afac0908cdfe,0x88f64636d3fc1a400ce1,0xfc2268f440d3767b7e02,0x7c7f360283385784190b,0x419ca5fe800cbdd70321,0x9229f854019aa5ffd307,0x3033cfd46628470f7f79,0x6bdf81fa8011fbcfa6c,0x211e00cd15a77db12b04,0x53c83f0464ef2bf196bd,0x863810b9db344dba000d,0x889a0ce5fc380e06637e,0x4000a45fcf8042357d7f,0xf95fb8c043e7900c927c,0x41a3a0688dbd2400cdaf,0x27a67e7584819f3ff0c,0x732137f8f6f08d20fd1,0xffebc4283250a400dbcf,0x600f542979fa780032d7,0xc9033a3f1400849fd2f8,0xa4699afc0402387e1cf2,0x8d6f103213a1fa7291cf,0x684fc6d5200cebdd0e0,0x1819a3e0481ebfeb4a66,0x704c4841cfe00458fb58,0xa5211d7e46e7894804be,0xe9981987fee0108c3f73,0xfa20509dfe029c23d7fa,0x93994338c9ebfdb8ed22,0xb2c2066376e474277cbd,0xcfb284cfc4c102143d],#[0xd004808870832c6a29d2,0x666f880323e409bc0fa,0x347fc581a80ce1f9df92,0x4c88913c2247fb797303,0xcdfc00801985cf851819,0x111dfb71032d7a6c400c,0xe98101a51d19ba98298,0x4b96e1ccaf4000d6df3c,0x10f69ac6021bdb628021,0x5f2d5e4819e74f5d4009,0x93c11e01066ea780c9,0x8ccedfa6c1907ea547dc,0x806a4fc69541993bcef4,0x67afee3032f47c604962,0x234dde8812cbeda56120,0xbdd60033f7cbd10328fe,0xe1800328c2d7e0402486,0x660fbb9032df0384adf,0x3419d7137e08d5ff4d16,0xca5fe67584019d3fc6d7,0x2006edfea4c22a7795f8,0x302034c645faf3a1a505,0x150f5994cd834c787b5d,0x32fcd008a9a7fa03a80d,0xd813e01203597db85803,0x215b3e18f09067cff0cf,0x932225f0001096f56640,0x851277281a6df064a256,0xb6cc685519ff8830486f,0xe9277813538f64e65378,0x36efff52011c57af7f95,0x53cf43819a9bff923003],#[0x1fc204d4f119ccb1e5fb,0xf3aac936a4069dbc2125,0x823f7ffc7a646f00101a,0xca800cd57184a39ac49e,0x99fb424cff6a02297c3,0x8819f3b4bcac456689ac,0x10abf309708d5fb7906,0x9a1fc800a84888b7ab32,0xe890810db7b53f10824,0x6d981ab7af1c11692287,0x8c80430a88bcfff84416,0x32615d7f50024736a7dd,0x32fc8de9d600096dede7,0xf8decd060684fa7acd03,0x66a70fe2066ecdbe8c81,0x4d7eef0b0067cd7a0006,0xed21021b2df1fb0d8203,0xb26426b01b9bf010b2e2,0xa1f39440195bfe1688e6,0x419e9be02607e3807220,0xffa3d22e3813bbf16980,0x948afe19310033c8c1fe,0xf3a360d801362f0058f5,0xc84085aea90065cf8f92,0x6004d33ae714781225d5,0x337bf5180085eece8dc,0x984819e7c46845ac3a63,0x3307943f64201a1be5b,0x4c800d5627b84c5f89d0,0x3c00db60002253e1ab37,0xe30093b8d7e1584124df,0xaa00ca1ffd01032c130b],#[0xacda9fd36c6040ce1fd,0x48b0214b4c3d2ba46c22,0x4d5f0a8230fa2e04617e,0xe0002127c49845efc206,0x4c2f002044effd8022cb,0x67a780b6cc686b7d78,0xa1a0031f8003366c9df0,0x49af280210bff64f428,0x3309034479fedd00cd78,0x740d1bef9ea20476cfe3,0x8ef6c24ee5034947ad46,0xf318b402507c52a34006,0x819dbfa0efc9033afc8,0x40d0dffca80019aaabcb,0xa62959001bdbff429417,0x4a9c20081a739fe1c224,0x100952fff0008804347e,0xc9077777a0281f85c8f0,0x307f92bb48dd659addab,0xd32590bfd001927d4c02,0x978048cfb3ab01810c5f,0x5357f9c3000690ff100c,0xfd2e40001a47113d823c,0xfbc0819f3f3ac240cdd4,0x289a48a67eb408ddc3a,0x4c070203663d640d2804,0x9b7844c1021c33fff429,0x3cf1810342ec091fe092,0x359be4eec119064435bd,0x3bc6823b7f9e68266150,0x7137e08cbd7f130465f2,0x732e0671f5163db80129],#[0x63209034cf3cc0454dbe,0x1a07d0e3c3b804aef0d3,0xf979c300068ae1755aec,0xe80217bb1f705280694e,0xe4e08ebc7ff84011d5e3,0x8f660a1021e3e049b73f,0x4596004044a1f4382342,0x82c4043d7950019644fc,0x3b7ffa2600cc0d12f160,0xca17f00046cc8f82003,0xfee2f8ab5203557fb600,0x10ccc0dba3c7fcc023a7,0x166166243643974f9412,0x9fee8da2ec8271408a07,0x8889ffabf6c73662a600,0x1762c201a7157e8c8304,0x1b3f87954560a03507e2,0x427e44d00cdceed6e072,0x79d593b812678eadad42,0x38f55144d6af76a00216,0x2447ab90810b54fc3f8,0xec00cb1977559d4069bc,0x22507bfa44eeca06bef2,0xa7e41005225e7c117728,0x6f2e60662e1f5de040ce,0x30194a9fbdb0d90688ff,0x41983fe8f4c0019cbff3,0x4208a1f922419621e586,0x19fff084b0210406b1fd,0x42f7c2881946f78f008e,0xcfa845a6f80991eae420,0xea4c22cfe0008af90209],#[0x4be8e2c1242c08008bdf,0x5995d835072bf3422834,0x2868252fdea504662e0f,0x787212157cc484db1aee,0x8e31c7fc1b5380946f0,0xc1cc842f0f0977f9fa01,0x65afc11003303e0641f3,0x6f84adf39b0118bbe120,0x8b770334708d73d55784,0x8328567c0019a7801133,0x897c21a67000111df30a,0x20f02f000881c56f9604,0xdbffbe082a8f10826fb9,0x953fb0c0994bf874cc0c,0x42ce97d64047ed7c081,0x2606c47e2801090fe0de,0xce3e10474fa7e508aa62,0x1c389fb2c141a07e049b,0x19b02037789f5696402,0xbeb8000043673ffac041,0xf00455fc4f0ecde50a58,0x49b113845debc7045df3,0x7eb8d38bc6069bbc0401,0xd17f4090bfcf28b0332,0x90f44e800cdded9adb24,0x9f94008f1f9de6024896,0x15b09034afdce948471f,0x57e415065bc646deddfb,0x5a08b9e5b01943ff1032,0xec84917184a332e1221f,0x48bf52380854ef2bf194,0xf9ad8848e964184bd403],#[0x66120662fe1ad103348e,0x5a801375c59a88090d1d,0xb0505081103ff1ca504f,0x498d01fdcc6040cf4fe5,0x66287ade040cf5c29c79,0x1e5091e183387fc7a000,0x308b3f401167ffa9008c,0x969f9422a99981b37fa9,0x3c008f50afb695841a03,0xc2400d435fd6008db3de,0x6e355bfb048ce9fbf192,0x9121bcc0d91fe3780033,0x19b7e1008bdffedfc5a,0x47e5142951801a933caa,0x7cc6e2d80671cdf49024,0x17c1f8004d63fa47e204,0x269aff58403033a7bf87,0xed9c10e021b83038f549,0x53e49602173fae0000cc,0x810a2fc7d744172d6045,0x3ff8550dc2a0351bab91,0xa0ccc3e6804513ad9a8f,0x77ebc8a7c4400d7d5f94,0xd12f9ba185045140452,0x5fdada5033327fa16550,0xe70939fd8640cb787849,0x481903fc40320fd57840,0xf3456b0d4ec362042d79,0x286b0fafc26d480d0ae0,0x81083f02569fe983903a,0x47cf9de6024896a67f41,0x64af8ad00335be70042],#[0xa80d51edebb203347d32,0x7d4f2b03314bf2e6159,0x107732a1243fca34a033,0x499d48a0ca5a0fd10336,0x2142dfa8011daf36151,0x3c008c1e70006537e884,0x20420bf30b061890e3ea,0x698ff8d21c22006927d8,0xd5a788454fc7cb40e4cc,0xcf9ff68cb2a30500006,0x43b7c7804197ba4a3f85,0xab052006fd7c1541c800,0xefd90c042c61e96d3624,0x1f600021bbcb0ca080cf,0x32a400670fa6c400cd4d,0x125f0001087f80499ffc,0x37e5840cb4bf0134f121,0x3f440067afc9a7297434,0x5a06827aabca40343d40,0xa0804c9d9f70468f3446,0x7fde46040cebfec7398c,0xf540401ad7ff3f49023c,0xfe8da9237981b2be437a,0x1900cedffb2a003366d2,0x876febd9581993ff8ed,0x9f4f184033d3fa898000,0x4120690fceb7b2100d2d,0x1880429d90913b7e1096,0x452006e1c478ac08f6fa,0x100200698dbed2e24aa8,0x854b233fc37810b9ff4b,0x4819d3e9084bb850d3df],#[0x670b61e9cca1f97190,0x9681a39cd8642461d700,0x217781054fca4057f9a5,0x1183f822006617bb230,0xe77e4819efcec0967c52,0x800cc51fe77984d5a383,0x34f73e4bd03034061ff4,0xf9ca200cd1e768153590,0x3db87f92bb48dd659b4b,0xcc1ffe56c6ca10a2c1ac,0x1254d6a57024f7878400,0x330bfac000021b9c1312,0x791ac6210036717b7182,0x54033a7fc32c006622fd,0x1187ff66a10090c5ffa9,0x3b00ca6f078721077a94,0x654ffe7088e003417d,0x8c6fe2605b5101115fb4,0x7580be2129e0258bcd00,0x2f30f90b061a18512b61,0x3ca24f442e6494e2c8cf,0x242fbf6f49095fb93326,0xaae0c0c77b3e85b7a55b,0x5cb5d3251ca26ebd4bee,0xf0cdfc772865372c8909,0x9ed37353130e8930e9c8,0xa5cc8b2885664cb52214,0x27b4daab85b7a7434061,0xbbf65d0cc4815e2e2a86,0x607a99f590a984be2195,0xd308fb2334aefe4cd018,0xaffc909995253f23a173],#[0xc40ec942926dd1e999b8,0x673de9909ed36aae151]]
set_option maxRecDepth 32768 in
def g251H9 := limbs80 #[#[0xa28a60140001950a4221,0x6019a140050a12952149,0x28651048000489409509,0x4a841055001a459a1a50,0x58858058490a084aa5a4,0x12250958110001608122,0xa86821a8208220220851,0x82a14102609591981880,0x8285019698420101840,0x19288240a65424050466,0x56481606009608008109,0x884400980106620a4281,0x50506220910001a02aa,0x490008a899908a4a060,0x480811202500195a4a0,0x2842494196005905604a,0x15200488451855918941,0x88096282299a458259a0,0x224a16a1025008a48146,0x86480912955008a5052a,0x1406500504a24011002,0xa000285a829819520994,0x85802240080042629488,0xa80206a046a0a0020020,0x5800a04600016660544a,0x25a04809605099561082,0x69001004244a62290245,0x41004546684508840902,0x208a89486a159018094,0x58900114a6a985a2442,0x25805a08994062a9460,0xa2a00004508410000110],#[0x2025604a8a0401281104,0x2209a8220486168a4046,0x48622809405404552120,0x26062180880041100184,0x5119022a848805801022,0x4a510915620190008501,0x615511818a821152608a,0x64201016654120294150,0xa9402215916108442462,0x81429664412a14584091,0x818985085550428a1602,0x56860145250264091295,0x2605400508a068110102,0x16484545920014212818,0x18005680aa205522114,0x22218566212481480900,0x465a50902242544a4980,0x1a11580100182140299,0x88456209000548125580,0x4916220094aa9aa58020,0x60806898424989488688,0x59429664458442526468,0x9a215a648226602922a4,0x10a02461149a441456a,0x1810100086600a88105a,0x50226528821586515800,0x1518041891126096a862,0x119466502194840848aa,0x5401501620812119aa0,0x1885a064088659041168,0x546222964a8862109160,0x852268242060a8040508],#[0x50152162a6a211406285,0x90446419521565658005,0x54812080200200a12189,0x4121a000209644908209,0x40005400662a4412129,0x491001629109a1211010,0xa0024686818122121140,0xa68914455201609a0605,0x90108180056808840900,0x91042568495250812011,0x114229992846a00a8684,0x9a20455a2a062a4a9009,0xa12582084826080a0214,0x820086802656645020a2,0x1100a0450501a6405100,0x6a59868582a408026491,0x51a5499951a59664084a,0xa1120aa0948949265580,0x4200091100a904082051,0x4450906aaa5108108145,0x462a48a0184a02152915,0x942212a120658946401a,0x48821908946280291402,0x85921515224445480199,0x620626a2402818665116,0x52202a448985a1911020,0x8481849068a108614829,0xa0102aa1804aa0602960,0x19401080215995858141,0x61541144002102041856,0x8a82214104a049884061,0xa6861a0000a04802441],#[0x925a224861995aa4a404,0x4a41a9081294009a8190,0x4482822125208426a411,0x14902440a24686100642,0x2a869282000148582059,0x90a205a1640020524648,0x10242008650890515481,0x80698824881545481104,0x5615a849598202662406,0x440812a966908409a69,0x60180210261980845500,0x89402002482196588540,0x8f0a9591422828601898,0x4013966518f0b24c4c01,0xb002292f3dc4c130a490,0x749c504b99a216be6bf1,0x827c05492f46b153531,0x8041edfa715218182a4a,0x8dc6d4142b36c6c0cc2c,0xb51e3148043b7059c1e0,0x899d8fc143e88c2e68c0,0xbd132ca875c0f1d10756,0x5c8d9cf6a9e4d49a473,0x7539ed394bb174c2112d,0x930c812691061e506282,0x8c79579232725cd43805,0x451a82ec850834e129a2,0x5a088062d34c06ba601d,0xaca1786b6848802017d2,0x2c717532ff21768e2469,0x1e17604540d7824c834,0x54b3a21e3420deccd518],#[0xc14102215114638e1e4,0xc188e20aba7250054f06,0x8845c08c408d662d0172,0x5d5ce28da1913fbb04e4,0x26743f140618ac6b404,0x1228cc83859a32dc20ea,0xca080107308014cc159e,0x995a47fa2061ab861a29,0x893b80693056ae806aae,0xbc071f0b1272bf110052,0x342140932fce400883cd,0x196041f0a189b8038541,0xc84b13119ec2c0b0b82a,0xb4ab7f76468a2b2d302f,0xad0f4009b826f261f347,0x16d0833547cc48a240d5,0xb242958d214c8e940040,0x367082207425b063280,0x541352552f2c4c22378f,0xf0c00083fb1341ba089,0x386b098048c0314af062,0xa98746d66c9566346289,0x905e2295a414b88182ba,0x1fac829bca891702a060,0xe904ccd5c2c485a4c214,0x6747072a990801259c8d,0xaa4bab9702120a162795,0x77012dd141c217c16a56,0xac0cdee64c8706a959aa,0x8f20730868b8856120dc,0xab9191808805a6a15778,0x99e3658353760bf2104d],#[0x6dc6bd89964b5b5c360a,0xa1d0251261dfdd3203bb,0x483ac38c542261458798,0xc62cf4e7ffbddf4c028c,0x416f9edbc27e764f0002,0xef15fb96e75a77c402a,0xe2ffc3a75feb34f9600a,0x50bbb7c9d48e3c59f181,0xc6088c7e5bf63f3db30,0xc1d746bffdcbf57afaba,0xe8463774fff0fd1c999f,0xa70a1e4cfdf72977bff7,0x3a8171847623c771f45b,0xfb48326f3a487c97ddd5,0x643486deb292118ee588,0xf87dd0ea9db67fdd16dc,0x4f24ce1fa7be487d5317,0xef979d84420586e2dff7,0x7aa73d489137f363e2cd,0xcfbd35fd137748af0efe,0x7e75bc69a294c3f90f7b,0xffe75dca1c57f0127bbf,0xcd9272c2530b96a7923d,0xd6bf7f73db1186e81e32,0x9fe765bfd5f632a2352f,0xecde146f563e46a7ab3b,0x5aff481d973c30e022a4,0x53ee45b8f3fc731d12dd,0x55b2fadb6dcefcc3c6ed,0xe71b7b9f572e3db87dc7,0xebf3c0c45bc9ddef905f,0x86a09ee57af665f5d220],#[0x1d7fefdddc2d18ac0e46,0x2d779bc11e5f93dbfd49,0x26f60c3868ffc17fb379,0xc503fdefdeb54ff6e95e,0x30a621be5a237c3f55ff,0xd395606d5c40f95ce41f,0x30f2bb8cee6be41ae98f,0x83fe59b16fb2b7373777,0xb63dcb85de87cd9decb7,0xb81d397b2ee64c8e3b74,0xf743d7308cf927f5cdd5,0xa9ffbfc637419e83e7be,0xa13caffccbbbba563edf,0x6b5fb5f31a2f7de95ef0,0xd4af9b94d35a699e5791,0x7cea01b3ba6db7a675b6,0xaff6face9dce03bffea5,0xb93e5ffcd361ca5355aa,0x73fdd51ffbf63a950b57,0x4b9e599152f9477917a9,0x3ea952d542ed48f48fcd,0xd936fe25dfc9fb9f1ddd,0xb76bf73c114fce93f485,0xcacb577b432fdb6a8117,0xf2da67cb3ad561ded071,0x2adf7c72beffc5d4fa17,0xb1b76faf77b37f36fb44,0x1c0a7ec4d87575af7868,0x2417f2fbf1ef1ca6daf5,0x54987de97935f25f7b6e,0xf495a9e5fe143e7decaa,0x2e9300e5df6a2f576fe8],#[0x36626a77f1fdf6fbdbd5,0xf6ce4ebb4edafa2d7bed,0x32c7c9fef0f9c6757431,0x77bf15446bf03f4143f7,0x2918a1f3cfadb4,0xffff77e5368000000000,0xffbbfbfe000dffbfff7f,0xd52eb9ee4075febfffff,0xb8efb65b781d7efffd6f,0xfffffffff70527f7ffdf,0xdfddfeec7760d6d5bfd1,0xabdf7fbff3dc21abeffe,0xebfbfd7fffef84fffef7,0xffdebbfd3dffb0ba5fbf,0xffbafffffffdfe1acf4f,0xffffffefff779fc3c177,0xff5bfbdf9feffef886bf,0xffdfddbffdffcdef12af,0x7d7effffd9fbb9ffe28c,0xe77fbeffedff7df7f458,0x987fffffbefbff3fff8b,0x36bf9f74fffbff75f7f1,0xc741ff5ff7fcbdc776fc,0xd0f4b6bfddcf7feff6fd,0xfb2037b777ffbbbbbfff,0xffe43bfd9ff9bfaeff5e,0xbefc8dd5bf7bffdfdfff,0xff8f929e5fed77fddaef,0xb7fff26cd5ff7ffffdfd,0xfffafe510dfff5a7bd5f,0xbffaeca89ffaffff5bf,0x2ac621095f6300128d82],#[0x11a2c442cd406308020,0xdb04520125ab62d8b698,0x58889d2000b870a30603,0x8231048a0417611c4808,0x3600882602f5408306,0x9d240800085fac5420,0x4080a0a0222ccc13a430,0x6c7e132a403018618be,0x24881320440883168c0,0x4897200128043086429a,0x408046027916c784ca44,0x50112d250d8d1000198a,0xb04c20a03342c256833c,0x3e004a409433f015a468,0xad02078d08280034c04d,0x362860460e94003b0ce9,0x6db0b080ad00b2168c1,0x10dde0002b2052920885,0x9bf8201048c8525085,0x8483876b4646e412060a,0xb0047244246097250500,0x64094e6c21881012e292,0x19d2081901608e82,0x2500063ade40107ce260,0x884172876c110346c9a6,0x70458464f00a34d028d4,0x91a074001e5e08060538,0x40661933d5d20278c7,0xa150a808807c10c008e4,0x138a45640a0fa420bda1,0x110a30225861f9920046,0x84118800e2413fcc0500],#[0xa80040505c6c08090420,0xb28c210c1b279502f107,0x22743928b0003c20a805,0xad0a13bc218ec0542101,0x614832022110a4888560,0x74010000c0168018d0df,0x7a50823e502381411a20,0xa4000000000000000044,0x1fffffffffffffffe8,0x8101fffffffffffffffc,0xf03fff7ffffffffffbff,0xfe0bdfffffffffffffff,0x2141fb9e095e84516a3e,0x8fa047c7c7eb98f12ca7,0x30e80a04c3e5e565e3b9,0x2553016420a2bf5f906f,0xe144c4306cabd0234240,0x845d210668ff4ca3db22,0x416b2940dd000498d1cb,0xe861c821d093e942423,0x9881201c83d505996d9e,0xc847a981c8818a1eda91,0x3f5906992010f33823e7,0x38ee594c33a23c930620,0xcb821ad528644a8ec5a3,0x50031a2484f209d62830,0x60a17ba8b4a911474444,0xa02b288dbedee02a2288,0x72d2c8b5345e87457882,0x627c82b0a3242e8b679,0xe0183fd4b71aa5e317d4,0x84cc5a456a00aa144313],#[0x2c21f78137a001399466,0xb2cb39151b881d7b000d,0x380d888c02832d800511,0x8728f129af8c1f22c528,0x80eca4f5e38eb65d0cc8,0xe1e996443b34f022c23,0x6383ec25e68c12d03a8a,0x25c80d00542c633d151,0x2202107d03004400161f,0x5001c218a04100080404,0x5022243a0c001400089,0x21002088c0320010800,0x30011400400a4410,0x1840401022c80000c005,0x40400082045f00000022,0x84004002808cc0618018,0xd8003490091c0000000,0x81a0400214223a880000,0x90004002444048000000,0x4621020609409120108,0x200081000a00124a000,0x32404a1842000024f24c,0x2908a0401a4124a709,0x8240542144014009680,0xd0442002120440029304,0x940240048420c0000266,0xc500021080820247204d,0x3b98a400480020000109,0x27b89041180030104021,0x5020000001234468088,0xa1a000000000000000,0x143400000000000000],#[0x28680000000000000,0x50d0000000000000,0xa1a000000000000,0x143400000000000,0x28680000000000,0x50d0000000000,0xa1a000000000,0x143400000000,0x28680000000,0x50d0000000,0x559aaf64508a1a000000,0xc617331f31b960c7eef8,0xe3884b1d57f624543b89,0xb655ca641058c4cd2121,0xde9a4c9dc61b607b960b,0x9f94ffa80f9e69aa6792,0x34e32118bc682edef209,0x7bf142fea7394eaca41f,0xce10b348bdbc2fa7dd38,0x82c9e42cf0ff6b2a0848,0x8c6ceb1248a2d4130c12,0x47aae9d3d25d7248888e,0x5a32fcb3cdae663c6133,0xd5e9a9edf1b1914518e9,0xbe00259f8c0846dee2ff,0x5409c1151b2903651ad,0xb2c1daad3752883e6a6d,0xd0b26a80b460a32964b8,0xb1dd7db059271b33cfa2,0xf18d60d84663cacf584f,0xc9b1da227c7aa89accc1,0xd649b6b3ce9db9e55b61],#[0x3289f409e2bf6dac61c6,0x72ee275b2802e78f1a93,0x601c4dcb1713d71c9ee4,0x5f9f3bd5ffa2bd0cf35d,0xd1a4838418e4413a5af3,0x15107363a98903ea426d,0x275e8cdc4372b7990eca,0x244746e078b4d5c483b0,0x4755d4a5947b696b5a98,0xa1adfbe6750abbcc691a,0xebfd090aead322c071be,0x1bcad4ae36d64ece7d75,0xd2eb932baf568b614376,0xe99c1c1420f56ba8dfc3,0xf26c3900bfc462305d2,0x9629a650228598b5986c,0x507ebcfa9c9c561fa367,0xd243ab0e186cd74f7801,0x7d942735a65c8d6b064f,0xd730fcc56806c4b341b4,0xcf63461257aca30d7730,0x40b65493de32ee5f47bc,0xb144aaabe503fa11c20a,0x34d98af976d7be535044,0x6beb5b2e835241c04db4,0x82c337aaa6f59e63e502,0xa19945846ff92a9baed9,0x9db2d13459c8d8a6ded2,0x11fa98e84ec27362b854,0xcf1a1cd681c626977239,0x390fac544f251d33e8eb,0x2423f04183e968668a5b],#[0xb562383fe332f531a0aa,0x3b607ebc9230acdcb024,0xc893f6cd1c282ebf6edd,0xa3455e30350518b0cf4a,0x2e670748a5dc3239d48c,0xfb8ac6ca937657b0dc5a,0xdb3ef8498195a1235759,0xe3ae9496f057521cd34b,0x3e14576d898ca8a5734,0x844b4d597e9cd6918e25,0x5a9a37976b91ad33ec01,0x128db39e19f3c372bb31,0x14d42cd31ca8f1e6daf4,0xa30f6ca356bb3af5d0d4,0x5f555a63379cd1a591f3,0xcc796a8c2e94f33b605a,0x825da4ede777289fd5fe,0xaa971b4aad65fb1834ce,0x4a15510eb7522cb174a2,0x6f31b6d9be8487322334,0xabca9da6ebdd0f0ae744,0x98b1196de9ec51de9ffa,0x664966e93ec6d12baa0c,0xd8d61d5405c6fd1ff257,0x365cc99cf6ab5b46aa68,0x5df8257563f88adce260,0x1b19cb0356c6265179cc,0xce342ae99e8aabe7cea,0x1d498bb35a2717f7bcc,0xa43d686739514d4d463b,0xb0b32bf8bed782d076b4,0x2af15cfe0c1296c2a59d],#[0x2bbd8e8d5ee0eb3d7a2,0xf7b92c7d2c81964c9bc3,0x8df11f879b15cc9b2875,0x305c6c40aa801726b475,0xdd6ab714e9824cc4a825,0x71f3adb59fec490dad37,0x8e7e6a3da2596ec12a8a,0x837f0b4547f70d539dc4,0x9a56e614f5df9a8e4e27,0x857393b395e0f1cf503b,0xbc95c82dd329b82ed592,0x28d7658b824b4a30175e,0x3d584e7e8dd89dba35a4,0xca123223ce759be48d79,0x7c7750a2c4f941b2351,0x4a633f2a396be9cf4495,0x763ce4da9ed47666c956,0x4ce212d65d94f4557051,0x5281a284762c7386eb1c,0xc68a6645136ac3451ac1,0xab083b5bdbe2377012be,0xd6d4664f1123b0b56fe9,0x2a11c8c405e223939208,0xb0f500ee6578ecd2cd7a,0xa5bfa3ebcde8ea8bb4c4,0xf95c6106925589c7051f,0x82f8b6f0b9758f233133,0xdba9960d2c19438afcd0,0x73e52b325b88ddc33ed9,0x6619df4c32e61731c595,0xe11ef931eab19661214b,0x57ea8c5524e2efa58c41],#[0x1590e38d8ea9f5ea564a,0xe33e6c254046bf9286c8,0x75662ef79edb5c5bf2a,0xbc3782b7d4be2579961b,0x85a602aef99cbd23d7b6,0x29579178a6cde22f98b6,0xabadd0f72f74af9c6d38,0xa2d01522ad354fe8915c,0x73b6e57d67c35f4ccd4a,0x70ec13829a65ead67615,0x528b3a62aeec17d59ece,0x45074e163e9fcce1a8e7,0x18e5867d72323f7b6862,0x5492d0d1cfabed8cec6]]
def g251D10 := limbs80 #[#[0x54951541415013144031,0xc4261946418c56458554,0xefeff6f7f7fbf5eedf5f,0x80ca9282ea1ffff7f7f7,0x2c2c6b8032a8e4b900ae,0x33aa6c9b9ca2ede8b9fd,0x38ba6e668baf4aa489bb,0x74a8a54c232b8bcee0f2,0xe092a91c2a888b9e22ed,0xa2e008bae26e349ba8a6,0xda2ec89b8522ec29ba9,0x8ba5d2a254a88d28234b,0x928ba922eb7338bd2a38,0x2a369b98a2ecc8ba126e,0x3d283e9b8322e772a975,0xb8722ea96a80a2e7b2b8,0x52a90a6e108b8622ea28,0xc989b8c2ac932a97a6ea,0x42c908b9f5aa069ba342,0x89d2c230aa1d4a235309,0x8b85a6e708ba7a6eb49b,0x8d6a00a6e2b0b21a2ed8,0x2c249bb1da6028ba9baa,0xecaa449b84a6eb29ba15,0xbaa22edb5988c28694b0,0x72ba3a6e828bafd2c3e9,0xa292a94a2ed08b98a2ec,0xa6ec28ba72acb33ba3d4,0xb222e1b2a964aa409ba2,0x4a8fcaa569b9b22e829b,0x3e9b8154a255208d0623,0x6e693b8ba2e9b530b566],#[0x26ed12b23baa8a8ba82,0xba2e4c67818ae28728ba,0x38a0ae2c8b8aa762c298,0x86d8b8364e738b8262a9,0xe2ca38b08e2eb38b8162,0x8e2c838a89e2ecd8ba8,0x918ae28258b2162a238a,0x69939a62eb59988e2ea5,0x2ea99398e287f930ae4c,0xe62e318aa7e2c2b8ba36,0x189e2c7f931e62a7f8a9,0x38b8d66e858b27e2e939,0xa858b9ce4a7f929e62e1,0xe2a678b26e6e638ba0e2,0x8ae26278b1a64e718b19,0x921ee4a698b8564a678b,0x698b8464873898ae2e27,0x2a838b0b628778aa5e2e,0xde4e358a9de2ec38a18e,0xb2fe287b8a98e2a258b1,0xd938c648638ba166ec38,0xec78b9c6482b9318e2c8,0x62cb98b99e6ea39989e2,0xa9e0e639399e2cb7921b,0x8a9a64a278b2a62ed18b,0x278b09e4a638bb266ea5,0x487f9b8162c25939b64c,0x9e2c81931fe2c638b29e,0x21f62c979ba0e0627938,0x38b9b62e63938ae2a299,0xffffffffffff8aa06262,0xfffffffffffffc01ffff],#[0xfffffffffffffff903ff,0xffffffffffffffff407,0x200000000000000007ec,0x613135839e093810c000,0x88314cb2928048c01da8,0xc4e8127e450d0103ae0d,0x6c7d9e862c1761588d4e,0xa5a15980e9f257719c56,0xc2a009f5268594ea3eb8,0x9344c0070ae9427c290d,0x499945a008e3d19a9d3c,0x9639128440091c1db6b4,0x7c8f3692448008d39d8e,0xdb0ac3c954500081b85,0x7bf5aaa83c15c660095c,0x90c05aca53e9484e009,0xc0086b896e9736134520,0x44008539976913713c5,0x92848008336172903493,0x3a12c4c0086ba1889c3c,0x983a938420096409aca3,0x8a9b39938560083b6976,0xa18aa23f9785e00883a9,0xe3ad72943d13c400086b,0x8abe1aeb33d11040008,0xc0081379748a341103e0,0x84e0097425b4b8409746,0x154680085b797e993411,0x3b154460085b8984a040,0x9e3591c4c00893b99aa8,0xcec24a18866009dc35a6,0x6174963d9584e0095c29],#[0xeb757497389305800793,0x8bb998e923412448007,0xe00943f1a6b1411785e0,0x3e0096425c6b74115c4,0x958660086ba98ca24397,0x329083c0095beda8b244,0x86034040b81c26015887,0xb0207608244b4120d08,0xe0d03408560b830685d,0x8890662f0d0b03e221a0,0x41d9302655010e060320,0xe350f09d00100a010370,0x135111b0261a01128747,0xf46f0e2b88600190b14,0x492380e3a058ac009924,0x8918fa00e9b4b9088851,0xd6100133bdfd0075c7bd,0x1559e809b3d93804cd9f,0x913a0ebd08126f7b8da4,0x1267cf4ba8238af5a460,0x928f3f2c60a257ce3400,0x1a31c2c41227eeee1550,0x419f79ba4513a972bc09,0x8f0a21094c4c65d51063,0xb00a07faf4842049c36f,0xb98412348faba8241f91,0x37c2b8524e6b009c79de,0x9fa820091bcddc0238e3,0x6fe6c80503a11ae2091b,0xf9e6809d7ff98b290093,0xc1d408d31d42e8d0c12c,0x9dfd618823c778b8c156],#[0x128ff9a202827fa6202,0x47599cc008f3f0bc880,0xc36f88e055425376f060,0x4cc2f1504a5fe6060047,0x439cf4a09577e3d30510,0x3cb04930f7b3b182bdf1,0x396252ff3030023cc8e2,0xa07038f3d000250c11ad,0x84a4cfe540118fa79740,0x7d5feb1800240ef8f0aa,0xf950a48004b1f5c6a404,0x27c82009223983a81217,0x858a40240fe4e148049d,0xe880012b77c39689277f,0x1e09f446b4ed1254c7f7,0xf787ce0a4e779009ecf6,0x2378b202353ff5201450,0x9078be704eba838f841,0x36f3e92080495ed7f382,0x279e17521081289f481,0x3d100473ff3104c73d7d,0x14e5009297f5e000246f,0xbc2f3427bbf479828d8e,0x75fce42a012349d78047,0xa0483f26c84054ff1f80,0x1e882abcbe884fbcf1e0,0x903ebd4f90412639fff,0xa1258cf169109033ed22,0x9067ddbe09d766569c,0x73051bff41008db35d60,0xf5ba850be320011ccfba,0x5c6100483cfcb08141df],#[0xa0204bdbe3c2aa12923f,0x150591c47582489fe624,0xc304fa5258957e7acf44,0x42632ea8831a17c54008,0x8eb79ec411ceffed5c1,0x75b115efe480461ae686,0x8049b99f53bb22a337fa,0x840ab79aa8823ee71314,0xca124effc0e00239a7b6,0x82011cf3f0e2050bbbe9,0x80024eff222080499ffc,0x8c3fa0e129e127723ff0,0x8e79f94e09d6fe840,0xf39c823ef88982471c7b,0xa12923cc6008c7d8069d,0x130ffae24104883e3c2a,0x414012f2ef50308e7720,0x93bc761090b04b1fce64,0x8e3340708dbfc7896080,0x7ffdb0db8a85ab7cd420,0x250475e3f4395a280260,0xf2af708b4bb4fc275fca,0x3c23eecf9845b0efa709,0xef84271dac66847dd625,0x9a40a2ccfe7d8210accb,0x4894013476b1d211ec3f,0xfc08830a081317c7f0e8,0xce2791023afe0bae0475,0xf60011cf9eec9a1f1c16,0x2f34238ef9cc55004a93,0xc632b209177fe202793c,0x976fbdc613cf9c00465],#[0x6580bf8811f7c6c98216,0x495fe65450024aef5004,0x66a22816098bfcca5200,0xff286801237ee1008dbc,0x230edfc408c35fcc08a3,0x80491f9deb1023a8ef50,0x98259accd3c28dfce528,0x412671bac08d3e15701a,0x8d1e00bd0661ffe3c896,0xf419946fd0811e70fd40,0xda784ebdf3c0023c61a2,0x445a1412e7e4fa811a97,0x134bccfff16a205b3e15,0x623c004ad51bfc04242c,0x8166cb1f8f051412e7c1,0xfac012001a0bff7fc5a8,0x10d424dff33f8ba20575,0xf2811ef7e64805027fd8,0x931540130fd346050b5e,0x91809216b19c21207789,0xb804d393e60047defec4,0x98b667c2682ec610660f,0x6398246ff508046bec80,0xf93ec1449feb4228fe21,0xb0baa811c25f8520662c,0x465afe60459fea1008d,0xf8611e7e2e7211857fa2,0x2e23801217e2802329c9,0x1608c7ff72c37a382c9c,0x4008fbe364ac5004b13e,0x1284fe1616142481faf,0xd13f378c08c3fe84354],#[0x19c77e610466f45943a0,0x42fb3fca082457d149a0,0xcfc1f120475fe9626202,0xc6b828246ff1d8342024,0x4024cf8ce8c081412d75,0x408e235f300238f998d4,0xfe88131accd9c2859bf1,0x24afe7cf006402c136f,0xcd408fb9e61137b98c09,0xf788408eab494f08e355,0x812e7fb77e48280b04ed,0x4bbeff2084fab93fdd20,0xcfa9420242fea201a890,0x584f1f5811ef0f03028d,0x3f7c8208f39eb80d0a09,0x81397bcd98145fc7804c,0xf020299d85e6118c3ff0,0x17fe1f7005065f]]
def g251H10 := limbs80 #[#[0x5921aa09888814811021,0x1414592294445a252221,0x401144a990861242929,0x5008a20a08051449205a,0xa5228886a04105185645,0x12a25904204402445422,0x82aa4906205162602516,0x2002a081859110a0940a,0x5824005088806850a818,0x4915a012292214060165,0x2282a042254206249824,0x404006a664a54168011a,0x42015401241a52441285,0x6210a192806492164501,0x101441566a481448011,0x2a880920611808002002,0x88005515805880641205,0x1892991a508020a40900,0xa2288442468494008821,0x25200456190950281202,0x902984000011a0820842,0xa5610229a20061889928,0x40041692012020909808,0x1000201221420529a010,0xa4191102a09401a09a80,0xa950815008a5a0408a04,0x10608541202605526109,0x66984591050890551111,0x244005855202188a5284,0x201140810660a2410285,0x42a51689289aa9a54016,0x8a6019a2956041180846],#[0x24002559510259a08088,0x42550849060a06090442,0x28a69101060644184610,0xa224645a542650688080,0x88184281084089020550,0x211862080155584a1806,0x1908802844120010604,0x140040481090208209a0,0x604511a1941a55021a12,0x14a688290955a1448082,0x402025a10a14a0808000,0x9a080a808102540aa04,0x82040424a00645420909,0x494a0288264642620895,0x9a162029a450118426a0,0xa86299604852a2049866,0x1a884208216a49856010,0x52624454090044822468,0x1058895204aa09912091,0x15180212209a06480829,0x9480619449a040229815,0x80080100128590209802,0x2a459505468014148228,0x800462a4242612642909,0x80480509814429144612,0x80582028404001820500,0xa800884080120a922812,0x585614a280a010516800,0x998150a0292aa144861,0x20091008101406486,0x100a12148498402aa024,0xc89d154bd581a9164a40],#[0x852099e6b401e4ce12dc,0x4c4a6128e00f8a411e4,0xbc54b89b5688da6e9815,0xd3a09ad2288631586c76,0x1567ace6890d995195c,0xaa52002e72d8f2a90c25,0x2b2a216ec8fe7d174cbc,0xdc68d0940ced18c89cea,0x4938c148e52458504602,0xaf874101ce001d044c41,0x18009643093002002012,0x4ef3dab1047ec30d106c,0x8c17cc81eba47fb96d4c,0x125a0e816c706137cab2,0x67f5d3b19563b3648c05,0x2115a884a270016f305,0x843adc14a9a145824ca4,0x86c88008388b148a1d1c,0x3290a050a4801c1cc46e,0xfc7847c8480050221e04,0x381107249a0822687604,0xde42d0285a0547622418,0x9023845a503a2ca30be4,0x528aee842302502d2368,0x3b40ac4fcc1827fd973a,0xc1d2b0d6917a20178,0xb54b4901406621850676,0x15180c619d06a201400a,0x316621810f032bad262c,0xa023d00f74ad5b830518,0x371cdb39440e062d24e,0x1071004e246b1d110],#[0x2a78a8a1525d379244,0x84062e81a2f1a410df22,0x95c0962b33e029a5c001,0x661e0c4770ae84012401,0x155c0f337554aa622eb,0xb5848a135d1446248024,0x4049c2815fa2745a4d20,0xa089b00019560041007f,0x6049302801bcdb12492c,0x88b2f33c081e96851bc1,0xdc950b94ca0215f5b231,0x34d69ec8428a25212652,0xc990e374746287f2b2,0x260061124342202c5261,0xc0081509c7c03042f88c,0x615905a100343ea31b1,0x184f86098662161aa343,0xa464881eb78043592a37,0x3d8a2d1ad17954a25b23,0xa4144e205557f7d58d0a,0xf64544f8a9b8ee2351d4,0xc22494491b3a91b1c31a,0x18204d23af9315c03412,0xf60a65066140380a4069,0x4be6045291bf345f226b,0x4ed33c856e56f4443084,0x125a10245a06a0bec770,0x8234a41cc5e0400e2078,0xc1c524c80260545a8811,0x1910ed5e00a632636920,0x1bf3c8563a3e65e127e9,0x165035d01d30469595ca],#[0x88534edfc302a06daea3,0x54f8eefb524a21270efc,0x1b0612c4c726c77674ae,0x914f4a6e5ba9e398078d,0x8000000104043b0e47c,0x448706aca1c9995e8,0x8038c80c8c80421ef258,0x9c067dea041352266ea8,0x1c809ed280a6b451280d,0xbb900d1c0b0233c54630,0xdc1a210138474006a0a0,0xed207c12e5b8ea75c8a6,0x50f941616fde12fe97da,0xb5a008f01bb99d32b6f8,0xc8e5d8d41fc14758676,0x91eb0e04b0232a34ec5f,0x1e442b2018a27374cdc8,0xb541496cc70c2ad24f18,0xc149580dc83342dcc01b,0xb109a2b58e309431200b,0x40c40ab4e8ae4e234128,0xabe2e8522970a2b23754,0x48dfd01e4547980123a9,0x1a29999960ea471cd03e,0x4520223d82f1a4788064,0x6482c309244f641d0e00,0x624b0a611be941b30626,0x81c4e9148020012300dc,0x251a50ac0d43500a1221,0x102e65334d1650021c01,0xe0813055d55c720b4829,0x58f6c5259108a272c968],#[0x31cdf8f65beb65724594,0x1a6d718825fc98b516b1,0x9a0ef412926401912007,0xab79db6100666eee8b56,0x812437f66fbc6adb4480,0x883502f53b1f46e53e39,0xe94d5c14e007b472d289,0xb9ddb1d0f32b7ae7662d,0xd16cb61f70ac80147a09,0x65e5c0afa8ce1eb1a7ed,0x68000000a904eecaaa82,0x1bffffffff3fffffe8,0xe07bffefffffffdfdffe,0xfc0f5ffffffdffffdefd,0xfde16dfd7fffffdffffb,0xfffe1e3fffdff7ffffff,0xffffe25dffcdffffdaf7,0xffffce2cffffffffdfff,0xffffffe34dbffdd7ffff,0xfffffffc3c1ffffbffff,0xffffffffe43fffffffff,0xffffffff7e4bdfffffff,0xffffffffffe53dffffff,0xd6fdfffffffe5bbfffff,0xfdfddd6fffbfc63bfdbc,0xfffabddffedff66abd7f,0xbecfffcfffeef76717f3,0xfbfffeffcffffffe783d,0x5bfffbf6fffffffe27ed,0xd7f7fdff7dfffe7ffe86,0x94bbefffff7bffffffe8,0xe9c3fffedffffffeff6e],#[0x24a3810000411fffffff,0x400a7e00600000210000,0x100a8a0000001400000,0xa90000000000004,0x200180a9400000010001,0x4800a980000020000,0x80000aa0004100000,0xaa880000000,0x100020aac3080000,0x200000ab2000000,0xab600000,0xab80000,0xab8000,0xab800,0xab80,0x80000000000000000ab8,0xb80000000000000000ab,0x94cfbf91416e97bba8ea,0x5e11970b59b761d15711,0xd73dd1e500b79115bac7,0xd3712a772d04b553b371,0x29325f06360f8292d96f,0xf726b359bc7afb5f99d1,0x3837799083177b05b8f9,0x301807a6d6bf3f31117b,0x35295ab338f7651e16f3,0xf777823a41517b11447b,0xacf17d15d7312034c39e,0xcb575577a9d07bb876d1,0x562350586f7c9a250c31,0xa2f507959aa1a1b4191f,0x1dbb96df2bb6d3a719a7],#[0x1af5af183f80d43d7a94,0x6f1795b3fb9185948fba,0x5302103d4c16bdac98a1,0x9bb50d7b2d98363d6c96,0xa053b10f3797aaf4b9a7,0x1f2a9b0f3d562b8cb43f,0x53eb8cd2c39999a11ff3,0x90166f25d05d6e39f184,0x514fd199699961b972a1,0xf9c38515619798cfb391,0x65b02967f8134292359b,0x3fbab0db13b87bbb3779,0xf80b10db4b89d6d52192,0x37b47921f01f6a19498e,0xd94efbad2f9bc15f551f,0x5abd30339511387124f5,0xb758db2506d90f25793,0x2563b7f7ae95713a7b7f,0xb8058758fb36d9957436,0x7ff76d1d596f5317458e,0x1926da8ba11a61011833,0x15e5873b6f8b1b2f95bc,0x9751b79b3b4d09d7b786,0x291fd051b7bb894258af,0x5333033a7d3fd43b6af7,0x8ab6b75c9aedb71b859a,0xcb3e15856ff2736b9c11,0xf2410fd027b6b62db1fa,0x817a6bc0363f97785f99,0x8d74797b79f29b31191b,0x736f7253ffb7353d6338,0x86d5514a7377b4544364],#[0x212817ef9cd2d7b8d991,0x96497df323b9b065c231,0x171909b7790b50f02f8f,0x9193703101ae72a50c1,0x38991175e9b6d4f36e7c,0x5f3bdf7c1515a598093a,0x59a1fae157977d92988b,0xf93919559529d11d8ff4,0xb21af9a831cd555bc3bb,0xa58950e948318598f783,0xf00f8e765d7c52851a38,0xaa59db27d179ab9bed39,0xf8c523db8112733b049,0xbc170ab67d3a10f178f8,0x8d3af543a3b2759175a,0xddc257759239276ebb2b,0xf2c120970737f7c7223b,0x8c98a38b95dd2b97a39d,0xcd5ff7237e74d75b3247,0xb4a93ad1abb959a92f37,0x30783b2e12fd3cb1d3ab,0xefa652f53d171f50dad9,0x968fb079e15295cb3673,0x81510545da859511e991,0x498f5b0b6d985da21a9f,0x7881249997b839ab82d4,0xa4975960170b7dd0e32e,0x536f9a233633c9563161,0x97ebba52ed06f28fa9b2,0x4557bd30f7bf54591d7d,0x17d16b10ad]]
def g251D11 := limbs80 #[#[0x18d50a81c4288152fffb,0xd61ca354720d41c634c6,0x64d1c0982800ac955330,0x1fae46a2f15694429d8c,0x3838281840605809544,0x1517120e110d00040102,0xb0086401d9007747051a,0x8000e001c0005baa010c,0x840077f40085003bea00,0xa021fe60087100efb880,0xfea]]
def g251H11 := limbs80 #[#[0x9682044a085aaa156412,0x45652440966024850915,0x10010815442502082982,0x551260024a6a0022495a,0x226a5404429a4190a098,0x88a54002960900682296,0x84486211186094181a50,0x62a29480016290150600,0x502112028652440a5a28,0x4a888152080206400250,0x8012441402a801148224,0x129c3114bc0612050414,0xe0491c381c09ab1cb504,0x690450a941440b4520,0x627fa32032471dcb2082,0xa1ba2a66524017611995,0x684399207f1ea28d960,0x410000a00200240402,0x28406005201c00041001,0x18c2414013106042310a,0x114024044100280e4,0x8c41002e048c4800880,0x5900810800601c8a020,0x47884,0x2b44ed9f2eae72d28a60,0x123fe9ad7b9f9eca8400,0xf44be61fe739b6dfc7bb,0xffc8ec9f7f55fedfdc91,0xe29f328a14fd5cd3f1d7,0x6580001abffbb,0xeb000000000,0xcfdeffffffdd60000000],#[0xffffffffff7f803bffff,0xf1dffff,0xde74ca25370000007a00,0x572444c27019e9a470fd,0xf57a23a3059a0edc2dba,0x6cd50042c135502e0e,0xf799dca0000000000000,0xcca525389ea8bda02a2e,0x49ea35abab19f6a3892,0x2c95e6da02e6c06d3b76,0xfcaca4087a1aaee50be6,0x63882c595a878325c8ee,0xbcb52d991290a76ebb6a,0xd7bc305ae2d683e6fa72,0x4fa92b690a11b7a98a1a,0x74976178beabbb6f8b0a,0x83b22d19dab3b4abd9e2,0xc4b023d8fac1bfa9fb96,0xa2b93048aeac916d59aa,0x9a6cfb8638bd2dcad6]]
def g251D12 (j : Nat) := if j=0 then 0x80c101002ff else 0
def g251H12 := limbs80 #[#[0xed152003e08000001621,0x4e00000000007701,0xd71460001c4000000,0x6d000003300000000000,0x8fd9303a0064078cc000,0xba0000000a4e00018e54,0xb8000]]
def g251L : Nat → Packing
  | 6 => (349,6,7,7536825,120,1319110,1037,g251D6)
  | 7 => (2201,5,7,19989366,154,115613998,1382,g251D7)
  | 8 => (2754,4,7,13042495,138,441467217,1412,g251D8)
  | 9 => (1560,3,7,3866838,104,391913776,1242,g251D9)
  | 10 => (262,2,7,851984,68,68690222,1107,g251D10)
  | 11 => (16,1,7,131073,16,9,1043,g251D11)
  | 12 => (1,0,7,0,0,0,0,g251D12)
  | _ => emptyPacking
def g251I : Nat → Nat → Option (Nat × Nat)
  | 7 => indexWave 174 3 10 3564 9 1 [(1566,418),(2232,114),(2898,445)] #[(0,0),(445,2),(106,10),(453,0),(2,0)] g251H7
  | 8 => indexWave 1135 4 12 22527 12 1 [(10215,2201),(14319,1535),(18423,727)] #[(0,0),(727,11),(596,331),(1666,462),(11,0),(1047,0)] g251H8
  | 9 => indexWave 1451 5 13 28998 12 1 [(13059,1684),(18372,2141),(23685,3060)] #[(0,0),(3060,3),(1073,262),(4128,1459),(3,1684),(3319,0),(2270,0)] g251H9
  | 10 => indexWave 845 5 12 16725 11 1 [(7605,1495),(10645,1440),(13685,1163)] #[(0,0),(1163,35),(100,859),(2503,1463),(35,1495),(1987,0),(704,0)] g251H10
  | 11 => indexWave 150 3 9 3102 9 1 [(1350,367),(1934,215),(2518,219)] #[(0,0),(219,6),(89,132),(345,0),(6,0)] g251H11
  | 12 => lookupShort 6 71 3 7 4 1 g251H12
  | _ => fun _ => none
def g251 : Forest := ⟨251,12,fun i => g251Y[i]?.getD (0,0),g251C,g251A,g251L,g251I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251B6 : CutRow g251 6 0 349 := by
  have g251P6_0 : CutRow g251 6 0 2 := by
    apply checkedCells 6 0
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
  have g251P6_2 : CutRow g251 6 2 8 := by
    apply checkedCells 7 1
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
  have g251P6_10 : CutRow g251 6 10 48 := by
    apply polarBlock (data:=fun j => g251Mark (j+0)) rfl
    decide +kernel
  have g251P6_58 : CutRow g251 6 58 48 := by
    apply polarBlock (data:=fun j => g251Mark (j+48)) rfl
    decide +kernel
  have g251P6_106 : CutRow g251 6 106 48 := by
    apply polarBlock (data:=fun j => g251Mark (j+96)) rfl
    decide +kernel
  have g251P6_154 : CutRow g251 6 154 48 := by
    apply polarBlock (data:=fun j => g251Mark (j+144)) rfl
    decide +kernel
  have g251P6_202 : CutRow g251 6 202 48 := by
    apply polarBlock (data:=fun j => g251Mark (j+192)) rfl
    decide +kernel
  have g251P6_250 : CutRow g251 6 250 48 := by
    apply polarBlock (data:=fun j => g251Mark (j+240)) rfl
    decide +kernel
  have g251P6_298 : CutRow g251 6 298 48 := by
    apply polarBlock (data:=fun j => g251Mark (j+288)) rfl
    decide +kernel
  have g251P6_346 : CutRow g251 6 346 3 := by
    apply polarBlock (data:=fun j => g251Mark (j+336)) rfl
    decide +kernel
  exact (@joinRow g251 6 0 154 195 (@joinRow g251 6 0 10 144 (@joinRow g251 6 0 2 8 g251P6_0 g251P6_2) (@joinRow g251 6 10 48 96 g251P6_10 (@joinRow g251 6 58 48 48 g251P6_58 g251P6_106))) (@joinRow g251 6 154 96 99 (@joinRow g251 6 154 48 48 g251P6_154 g251P6_202) (@joinRow g251 6 250 48 51 g251P6_250 (@joinRow g251 6 298 48 3 g251P6_298 g251P6_346))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251B7 : CutRow g251 7 0 2201 := by
  have g251P7_0 : CutRow g251 7 0 11 := by
    apply checkedCells 6 1
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
  have g251P7_11 : CutRow g251 7 11 48 := by
    apply checkedCells 7 3
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
  have g251P7_59 : CutRow g251 7 59 48 := by
    apply checkedCells 7 3
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
  have g251P7_107 : CutRow g251 7 107 48 := by
    apply checkedCells 7 3
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
  have g251P7_155 : CutRow g251 7 155 48 := by
    apply checkedCells 7 3
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
  have g251P7_203 : CutRow g251 7 203 48 := by
    apply checkedCells 7 3
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
  have g251P7_251 : CutRow g251 7 251 48 := by
    apply checkedCells 7 3
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
  have g251P7_299 : CutRow g251 7 299 32 := by
    apply checkedCells 7 3
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
  have g251P7_331 : CutRow g251 7 331 48 := by
    apply checkedCells 8 3
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
  have g251P7_379 : CutRow g251 7 379 48 := by
    apply checkedCells 8 3
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
  have g251P7_427 : CutRow g251 7 427 35 := by
    apply checkedCells 8 3
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
  have g251P7_462 : CutRow g251 7 462 48 := by
    apply polarBlock (data:=fun j => g251Mark (j+339)) rfl
    decide +kernel
  have g251P7_510 : CutRow g251 7 510 48 := by
    apply polarBlock (data:=fun j => g251Mark (j+387)) rfl
    decide +kernel
  have g251P7_558 : CutRow g251 7 558 48 := by
    apply polarBlock (data:=fun j => g251Mark (j+435)) rfl
    decide +kernel
  have g251P7_606 : CutRow g251 7 606 48 := by
    apply polarBlock (data:=fun j => g251Mark (j+483)) rfl
    decide +kernel
  have g251P7_654 : CutRow g251 7 654 48 := by
    apply polarBlock (data:=fun j => g251Mark (j+531)) rfl
    decide +kernel
  have g251P7_702 : CutRow g251 7 702 48 := by
    apply polarBlock (data:=fun j => g251Mark (j+579)) rfl
    decide +kernel
  have g251P7_750 : CutRow g251 7 750 48 := by
    apply polarBlock (data:=fun j => g251Mark (j+627)) rfl
    decide +kernel
  have g251P7_798 : CutRow g251 7 798 48 := by
    apply polarBlock (data:=fun j => g251Mark (j+675)) rfl
    decide +kernel
  have g251P7_846 : CutRow g251 7 846 48 := by
    apply polarBlock (data:=fun j => g251Mark (j+723)) rfl
    decide +kernel
  have g251P7_894 : CutRow g251 7 894 48 := by
    apply polarBlock (data:=fun j => g251Mark (j+771)) rfl
    decide +kernel
  have g251P7_942 : CutRow g251 7 942 48 := by
    apply polarBlock (data:=fun j => g251Mark (j+819)) rfl
    decide +kernel
  have g251P7_990 : CutRow g251 7 990 48 := by
    apply polarBlock (data:=fun j => g251Mark (j+867)) rfl
    decide +kernel
  have g251P7_1038 : CutRow g251 7 1038 48 := by
    apply polarBlock (data:=fun j => g251Mark (j+915)) rfl
    decide +kernel
  have g251P7_1086 : CutRow g251 7 1086 48 := by
    apply polarBlock (data:=fun j => g251Mark (j+963)) rfl
    decide +kernel
  have g251P7_1134 : CutRow g251 7 1134 48 := by
    apply polarBlock (data:=fun j => g251Mark (j+1011)) rfl
    decide +kernel
  have g251P7_1182 : CutRow g251 7 1182 48 := by
    apply polarBlock (data:=fun j => g251Mark (j+1059)) rfl
    decide +kernel
  have g251P7_1230 : CutRow g251 7 1230 48 := by
    apply polarBlock (data:=fun j => g251Mark (j+1107)) rfl
    decide +kernel
  have g251P7_1278 : CutRow g251 7 1278 48 := by
    apply polarBlock (data:=fun j => g251Mark (j+1155)) rfl
    decide +kernel
  have g251P7_1326 : CutRow g251 7 1326 48 := by
    apply polarBlock (data:=fun j => g251Mark (j+1203)) rfl
    decide +kernel
  have g251P7_1374 : CutRow g251 7 1374 48 := by
    apply polarBlock (data:=fun j => g251Mark (j+1251)) rfl
    decide +kernel
  have g251P7_1422 : CutRow g251 7 1422 48 := by
    apply polarBlock (data:=fun j => g251Mark (j+1299)) rfl
    decide +kernel
  have g251P7_1470 : CutRow g251 7 1470 48 := by
    apply polarBlock (data:=fun j => g251Mark (j+1347)) rfl
    decide +kernel
  have g251P7_1518 : CutRow g251 7 1518 48 := by
    apply polarBlock (data:=fun j => g251Mark (j+1395)) rfl
    decide +kernel
  have g251P7_1566 : CutRow g251 7 1566 48 := by
    apply polarBlock (data:=fun j => g251Mark (j+1443)) rfl
    decide +kernel
  have g251P7_1614 : CutRow g251 7 1614 48 := by
    apply polarBlock (data:=fun j => g251Mark (j+1491)) rfl
    decide +kernel
  have g251P7_1662 : CutRow g251 7 1662 48 := by
    apply polarBlock (data:=fun j => g251Mark (j+1539)) rfl
    decide +kernel
  have g251P7_1710 : CutRow g251 7 1710 48 := by
    apply polarBlock (data:=fun j => g251Mark (j+1587)) rfl
    decide +kernel
  have g251P7_1758 : CutRow g251 7 1758 48 := by
    apply polarBlock (data:=fun j => g251Mark (j+1635)) rfl
    decide +kernel
  have g251P7_1806 : CutRow g251 7 1806 48 := by
    apply polarBlock (data:=fun j => g251Mark (j+1683)) rfl
    decide +kernel
  have g251P7_1854 : CutRow g251 7 1854 48 := by
    apply polarBlock (data:=fun j => g251Mark (j+1731)) rfl
    decide +kernel
  have g251P7_1902 : CutRow g251 7 1902 48 := by
    apply polarBlock (data:=fun j => g251Mark (j+1779)) rfl
    decide +kernel
  have g251P7_1950 : CutRow g251 7 1950 48 := by
    apply polarBlock (data:=fun j => g251Mark (j+1827)) rfl
    decide +kernel
  have g251P7_1998 : CutRow g251 7 1998 48 := by
    apply polarBlock (data:=fun j => g251Mark (j+1875)) rfl
    decide +kernel
  have g251P7_2046 : CutRow g251 7 2046 48 := by
    apply polarBlock (data:=fun j => g251Mark (j+1923)) rfl
    decide +kernel
  have g251P7_2094 : CutRow g251 7 2094 48 := by
    apply polarBlock (data:=fun j => g251Mark (j+1971)) rfl
    decide +kernel
  have g251P7_2142 : CutRow g251 7 2142 48 := by
    apply polarBlock (data:=fun j => g251Mark (j+2019)) rfl
    decide +kernel
  have g251P7_2190 : CutRow g251 7 2190 11 := by
    apply polarBlock (data:=fun j => g251Mark (j+2067)) rfl
    decide +kernel
  exact (@joinRow g251 7 0 1086 1115 (@joinRow g251 7 0 510 576 (@joinRow g251 7 0 251 259 (@joinRow g251 7 0 107 144 (@joinRow g251 7 0 11 96 g251P7_0 (@joinRow g251 7 11 48 48 g251P7_11 g251P7_59)) (@joinRow g251 7 107 48 96 g251P7_107 (@joinRow g251 7 155 48 48 g251P7_155 g251P7_203))) (@joinRow g251 7 251 128 131 (@joinRow g251 7 251 48 80 g251P7_251 (@joinRow g251 7 299 32 48 g251P7_299 g251P7_331)) (@joinRow g251 7 379 48 83 g251P7_379 (@joinRow g251 7 427 35 48 g251P7_427 g251P7_462)))) (@joinRow g251 7 510 288 288 (@joinRow g251 7 510 144 144 (@joinRow g251 7 510 48 96 g251P7_510 (@joinRow g251 7 558 48 48 g251P7_558 g251P7_606)) (@joinRow g251 7 654 48 96 g251P7_654 (@joinRow g251 7 702 48 48 g251P7_702 g251P7_750))) (@joinRow g251 7 798 144 144 (@joinRow g251 7 798 48 96 g251P7_798 (@joinRow g251 7 846 48 48 g251P7_846 g251P7_894)) (@joinRow g251 7 942 48 96 g251P7_942 (@joinRow g251 7 990 48 48 g251P7_990 g251P7_1038))))) (@joinRow g251 7 1086 576 539 (@joinRow g251 7 1086 288 288 (@joinRow g251 7 1086 144 144 (@joinRow g251 7 1086 48 96 g251P7_1086 (@joinRow g251 7 1134 48 48 g251P7_1134 g251P7_1182)) (@joinRow g251 7 1230 48 96 g251P7_1230 (@joinRow g251 7 1278 48 48 g251P7_1278 g251P7_1326))) (@joinRow g251 7 1374 144 144 (@joinRow g251 7 1374 48 96 g251P7_1374 (@joinRow g251 7 1422 48 48 g251P7_1422 g251P7_1470)) (@joinRow g251 7 1518 48 96 g251P7_1518 (@joinRow g251 7 1566 48 48 g251P7_1566 g251P7_1614)))) (@joinRow g251 7 1662 288 251 (@joinRow g251 7 1662 144 144 (@joinRow g251 7 1662 48 96 g251P7_1662 (@joinRow g251 7 1710 48 48 g251P7_1710 g251P7_1758)) (@joinRow g251 7 1806 48 96 g251P7_1806 (@joinRow g251 7 1854 48 48 g251P7_1854 g251P7_1902))) (@joinRow g251 7 1950 144 107 (@joinRow g251 7 1950 48 96 g251P7_1950 (@joinRow g251 7 1998 48 48 g251P7_1998 g251P7_2046)) (@joinRow g251 7 2094 48 59 g251P7_2094 (@joinRow g251 7 2142 48 11 g251P7_2142 g251P7_2190))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251B8 : CutRow g251 8 0 2754 := by
  have g251P8_0 : CutRow g251 8 0 3 := by
    apply checkedCells 6 0
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
  have g251P8_3 : CutRow g251 8 3 48 := by
    apply checkedCells 7 3
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
  have g251P8_51 : CutRow g251 8 51 48 := by
    apply checkedCells 7 3
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
  have g251P8_99 : CutRow g251 8 99 48 := by
    apply checkedCells 7 3
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
  have g251P8_147 : CutRow g251 8 147 48 := by
    apply checkedCells 7 3
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
  have g251P8_195 : CutRow g251 8 195 48 := by
    apply checkedCells 7 3
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
  have g251P8_243 : CutRow g251 8 243 19 := by
    apply checkedCells 7 2
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
  have g251P8_262 : CutRow g251 8 262 48 := by
    apply checkedCells 8 3
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
  have g251P8_310 : CutRow g251 8 310 48 := by
    apply checkedCells 8 3
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
  have g251P8_358 : CutRow g251 8 358 48 := by
    apply checkedCells 8 3
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
  have g251P8_406 : CutRow g251 8 406 48 := by
    apply checkedCells 8 3
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
  have g251P8_454 : CutRow g251 8 454 48 := by
    apply checkedCells 8 3
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
  have g251P8_502 : CutRow g251 8 502 48 := by
    apply checkedCells 8 3
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
  have g251P8_550 : CutRow g251 8 550 48 := by
    apply checkedCells 8 3
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
  have g251P8_598 : CutRow g251 8 598 48 := by
    apply checkedCells 8 3
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
  have g251P8_646 : CutRow g251 8 646 48 := by
    apply checkedCells 8 3
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
  have g251P8_694 : CutRow g251 8 694 48 := by
    apply checkedCells 8 3
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
  have g251P8_742 : CutRow g251 8 742 48 := by
    apply checkedCells 8 3
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
  have g251P8_790 : CutRow g251 8 790 48 := by
    apply checkedCells 8 3
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
  have g251P8_838 : CutRow g251 8 838 48 := by
    apply checkedCells 8 3
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
  have g251P8_886 : CutRow g251 8 886 48 := by
    apply checkedCells 8 3
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
  have g251P8_934 : CutRow g251 8 934 48 := by
    apply checkedCells 8 3
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
  have g251P8_982 : CutRow g251 8 982 48 := by
    apply checkedCells 8 3
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
  have g251P8_1030 : CutRow g251 8 1030 48 := by
    apply checkedCells 8 3
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
  have g251P8_1078 : CutRow g251 8 1078 48 := by
    apply checkedCells 8 3
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
  have g251P8_1126 : CutRow g251 8 1126 48 := by
    apply checkedCells 8 3
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
  have g251P8_1174 : CutRow g251 8 1174 48 := by
    apply checkedCells 8 3
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
  have g251P8_1222 : CutRow g251 8 1222 48 := by
    apply checkedCells 8 3
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
  have g251P8_1270 : CutRow g251 8 1270 48 := by
    apply checkedCells 8 3
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
  have g251P8_1318 : CutRow g251 8 1318 48 := by
    apply checkedCells 8 3
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
  have g251P8_1366 : CutRow g251 8 1366 48 := by
    apply checkedCells 8 3
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
  have g251P8_1414 : CutRow g251 8 1414 45 := by
    apply checkedCells 8 3
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
  have g251P8_1459 : CutRow g251 8 1459 48 := by
    apply checkedCells 9 3
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
  have g251P8_1507 : CutRow g251 8 1507 48 := by
    apply checkedCells 9 3
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
  have g251P8_1555 : CutRow g251 8 1555 48 := by
    apply checkedCells 9 3
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
  have g251P8_1603 : CutRow g251 8 1603 48 := by
    apply checkedCells 9 3
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
  have g251P8_1651 : CutRow g251 8 1651 33 := by
    apply checkedCells 9 3
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
  have g251P8_1684 : CutRow g251 8 1684 48 := by
    apply polarBlock (data:=fun j => g251Mark (j+2078)) rfl
    decide +kernel
  have g251P8_1732 : CutRow g251 8 1732 48 := by
    apply polarBlock (data:=fun j => g251Mark (j+2126)) rfl
    decide +kernel
  have g251P8_1780 : CutRow g251 8 1780 48 := by
    apply polarBlock (data:=fun j => g251Mark (j+2174)) rfl
    decide +kernel
  have g251P8_1828 : CutRow g251 8 1828 48 := by
    apply polarBlock (data:=fun j => g251Mark (j+2222)) rfl
    decide +kernel
  have g251P8_1876 : CutRow g251 8 1876 48 := by
    apply polarBlock (data:=fun j => g251Mark (j+2270)) rfl
    decide +kernel
  have g251P8_1924 : CutRow g251 8 1924 48 := by
    apply polarBlock (data:=fun j => g251Mark (j+2318)) rfl
    decide +kernel
  have g251P8_1972 : CutRow g251 8 1972 48 := by
    apply polarBlock (data:=fun j => g251Mark (j+2366)) rfl
    decide +kernel
  have g251P8_2020 : CutRow g251 8 2020 48 := by
    apply polarBlock (data:=fun j => g251Mark (j+2414)) rfl
    decide +kernel
  have g251P8_2068 : CutRow g251 8 2068 48 := by
    apply polarBlock (data:=fun j => g251Mark (j+2462)) rfl
    decide +kernel
  have g251P8_2116 : CutRow g251 8 2116 48 := by
    apply polarBlock (data:=fun j => g251Mark (j+2510)) rfl
    decide +kernel
  have g251P8_2164 : CutRow g251 8 2164 48 := by
    apply polarBlock (data:=fun j => g251Mark (j+2558)) rfl
    decide +kernel
  have g251P8_2212 : CutRow g251 8 2212 48 := by
    apply polarBlock (data:=fun j => g251Mark (j+2606)) rfl
    decide +kernel
  have g251P8_2260 : CutRow g251 8 2260 48 := by
    apply polarBlock (data:=fun j => g251Mark (j+2654)) rfl
    decide +kernel
  have g251P8_2308 : CutRow g251 8 2308 48 := by
    apply polarBlock (data:=fun j => g251Mark (j+2702)) rfl
    decide +kernel
  have g251P8_2356 : CutRow g251 8 2356 48 := by
    apply polarBlock (data:=fun j => g251Mark (j+2750)) rfl
    decide +kernel
  have g251P8_2404 : CutRow g251 8 2404 48 := by
    apply polarBlock (data:=fun j => g251Mark (j+2798)) rfl
    decide +kernel
  have g251P8_2452 : CutRow g251 8 2452 48 := by
    apply polarBlock (data:=fun j => g251Mark (j+2846)) rfl
    decide +kernel
  have g251P8_2500 : CutRow g251 8 2500 48 := by
    apply polarBlock (data:=fun j => g251Mark (j+2894)) rfl
    decide +kernel
  have g251P8_2548 : CutRow g251 8 2548 48 := by
    apply polarBlock (data:=fun j => g251Mark (j+2942)) rfl
    decide +kernel
  have g251P8_2596 : CutRow g251 8 2596 48 := by
    apply polarBlock (data:=fun j => g251Mark (j+2990)) rfl
    decide +kernel
  have g251P8_2644 : CutRow g251 8 2644 48 := by
    apply polarBlock (data:=fun j => g251Mark (j+3038)) rfl
    decide +kernel
  have g251P8_2692 : CutRow g251 8 2692 48 := by
    apply polarBlock (data:=fun j => g251Mark (j+3086)) rfl
    decide +kernel
  have g251P8_2740 : CutRow g251 8 2740 14 := by
    apply polarBlock (data:=fun j => g251Mark (j+3134)) rfl
    decide +kernel
  exact (@joinRow g251 8 0 1366 1388 (@joinRow g251 8 0 646 720 (@joinRow g251 8 0 262 384 (@joinRow g251 8 0 99 163 (@joinRow g251 8 0 3 96 g251P8_0 (@joinRow g251 8 3 48 48 g251P8_3 g251P8_51)) (@joinRow g251 8 99 96 67 (@joinRow g251 8 99 48 48 g251P8_99 g251P8_147) (@joinRow g251 8 195 48 19 g251P8_195 g251P8_243))) (@joinRow g251 8 262 192 192 (@joinRow g251 8 262 96 96 (@joinRow g251 8 262 48 48 g251P8_262 g251P8_310) (@joinRow g251 8 358 48 48 g251P8_358 g251P8_406)) (@joinRow g251 8 454 96 96 (@joinRow g251 8 454 48 48 g251P8_454 g251P8_502) (@joinRow g251 8 550 48 48 g251P8_550 g251P8_598)))) (@joinRow g251 8 646 336 384 (@joinRow g251 8 646 144 192 (@joinRow g251 8 646 48 96 g251P8_646 (@joinRow g251 8 694 48 48 g251P8_694 g251P8_742)) (@joinRow g251 8 790 96 96 (@joinRow g251 8 790 48 48 g251P8_790 g251P8_838) (@joinRow g251 8 886 48 48 g251P8_886 g251P8_934))) (@joinRow g251 8 982 192 192 (@joinRow g251 8 982 96 96 (@joinRow g251 8 982 48 48 g251P8_982 g251P8_1030) (@joinRow g251 8 1078 48 48 g251P8_1078 g251P8_1126)) (@joinRow g251 8 1174 96 96 (@joinRow g251 8 1174 48 48 g251P8_1174 g251P8_1222) (@joinRow g251 8 1270 48 48 g251P8_1270 g251P8_1318))))) (@joinRow g251 8 1366 702 686 (@joinRow g251 8 1366 318 384 (@joinRow g251 8 1366 141 177 (@joinRow g251 8 1366 48 93 g251P8_1366 (@joinRow g251 8 1414 45 48 g251P8_1414 g251P8_1459)) (@joinRow g251 8 1507 96 81 (@joinRow g251 8 1507 48 48 g251P8_1507 g251P8_1555) (@joinRow g251 8 1603 48 33 g251P8_1603 g251P8_1651))) (@joinRow g251 8 1684 192 192 (@joinRow g251 8 1684 96 96 (@joinRow g251 8 1684 48 48 g251P8_1684 g251P8_1732) (@joinRow g251 8 1780 48 48 g251P8_1780 g251P8_1828)) (@joinRow g251 8 1876 96 96 (@joinRow g251 8 1876 48 48 g251P8_1876 g251P8_1924) (@joinRow g251 8 1972 48 48 g251P8_1972 g251P8_2020)))) (@joinRow g251 8 2068 336 350 (@joinRow g251 8 2068 144 192 (@joinRow g251 8 2068 48 96 g251P8_2068 (@joinRow g251 8 2116 48 48 g251P8_2116 g251P8_2164)) (@joinRow g251 8 2212 96 96 (@joinRow g251 8 2212 48 48 g251P8_2212 g251P8_2260) (@joinRow g251 8 2308 48 48 g251P8_2308 g251P8_2356))) (@joinRow g251 8 2404 192 158 (@joinRow g251 8 2404 96 96 (@joinRow g251 8 2404 48 48 g251P8_2404 g251P8_2452) (@joinRow g251 8 2500 48 48 g251P8_2500 g251P8_2548)) (@joinRow g251 8 2596 96 62 (@joinRow g251 8 2596 48 48 g251P8_2596 g251P8_2644) (@joinRow g251 8 2692 48 14 g251P8_2692 g251P8_2740))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251B9 : CutRow g251 9 0 1560 := by
  have g251P9_0 : CutRow g251 9 0 35 := by
    apply checkedCells 7 3
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
  have g251P9_35 : CutRow g251 9 35 48 := by
    apply checkedCells 8 3
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
  have g251P9_83 : CutRow g251 9 83 48 := by
    apply checkedCells 8 3
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
  have g251P9_131 : CutRow g251 9 131 48 := by
    apply checkedCells 8 3
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
  have g251P9_179 : CutRow g251 9 179 48 := by
    apply checkedCells 8 3
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
  have g251P9_227 : CutRow g251 9 227 48 := by
    apply checkedCells 8 3
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
  have g251P9_275 : CutRow g251 9 275 48 := by
    apply checkedCells 8 3
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
  have g251P9_323 : CutRow g251 9 323 48 := by
    apply checkedCells 8 3
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
  have g251P9_371 : CutRow g251 9 371 48 := by
    apply checkedCells 8 3
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
  have g251P9_419 : CutRow g251 9 419 48 := by
    apply checkedCells 8 3
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
  have g251P9_467 : CutRow g251 9 467 48 := by
    apply checkedCells 8 3
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
  have g251P9_515 : CutRow g251 9 515 48 := by
    apply checkedCells 8 3
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
  have g251P9_563 : CutRow g251 9 563 48 := by
    apply checkedCells 8 3
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
  have g251P9_611 : CutRow g251 9 611 48 := by
    apply checkedCells 8 3
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
  have g251P9_659 : CutRow g251 9 659 48 := by
    apply checkedCells 8 3
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
  have g251P9_707 : CutRow g251 9 707 48 := by
    apply checkedCells 8 3
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
  have g251P9_755 : CutRow g251 9 755 48 := by
    apply checkedCells 8 3
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
  have g251P9_803 : CutRow g251 9 803 48 := by
    apply checkedCells 8 3
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
  have g251P9_851 : CutRow g251 9 851 8 := by
    apply checkedCells 8 1
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
  have g251P9_859 : CutRow g251 9 859 48 := by
    apply checkedCells 9 3
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
  have g251P9_907 : CutRow g251 9 907 48 := by
    apply checkedCells 9 3
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
  have g251P9_955 : CutRow g251 9 955 48 := by
    apply checkedCells 9 3
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
  have g251P9_1003 : CutRow g251 9 1003 48 := by
    apply checkedCells 9 3
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
  have g251P9_1051 : CutRow g251 9 1051 48 := by
    apply checkedCells 9 3
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
  have g251P9_1099 : CutRow g251 9 1099 48 := by
    apply checkedCells 9 3
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
  have g251P9_1147 : CutRow g251 9 1147 48 := by
    apply checkedCells 9 3
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
  have g251P9_1195 : CutRow g251 9 1195 48 := by
    apply checkedCells 9 3
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
  have g251P9_1243 : CutRow g251 9 1243 48 := by
    apply checkedCells 9 3
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
  have g251P9_1291 : CutRow g251 9 1291 48 := by
    apply checkedCells 9 3
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
  have g251P9_1339 : CutRow g251 9 1339 48 := by
    apply checkedCells 9 3
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
  have g251P9_1387 : CutRow g251 9 1387 48 := by
    apply checkedCells 9 3
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
  have g251P9_1435 : CutRow g251 9 1435 28 := by
    apply checkedCells 9 2
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
  have g251P9_1463 : CutRow g251 9 1463 32 := by
    apply checkedCells 10 3
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
  have g251P9_1495 : CutRow g251 9 1495 48 := by
    apply polarBlock (data:=fun j => g251Mark (j+3148)) rfl
    decide +kernel
  have g251P9_1543 : CutRow g251 9 1543 17 := by
    apply polarBlock (data:=fun j => g251Mark (j+3196)) rfl
    decide +kernel
  exact (@joinRow g251 9 0 803 757 (@joinRow g251 9 0 371 432 (@joinRow g251 9 0 179 192 (@joinRow g251 9 0 83 96 (@joinRow g251 9 0 35 48 g251P9_0 g251P9_35) (@joinRow g251 9 83 48 48 g251P9_83 g251P9_131)) (@joinRow g251 9 179 96 96 (@joinRow g251 9 179 48 48 g251P9_179 g251P9_227) (@joinRow g251 9 275 48 48 g251P9_275 g251P9_323))) (@joinRow g251 9 371 192 240 (@joinRow g251 9 371 96 96 (@joinRow g251 9 371 48 48 g251P9_371 g251P9_419) (@joinRow g251 9 467 48 48 g251P9_467 g251P9_515)) (@joinRow g251 9 563 96 144 (@joinRow g251 9 563 48 48 g251P9_563 g251P9_611) (@joinRow g251 9 659 48 96 g251P9_659 (@joinRow g251 9 707 48 48 g251P9_707 g251P9_755))))) (@joinRow g251 9 803 392 365 (@joinRow g251 9 803 152 240 (@joinRow g251 9 803 56 96 (@joinRow g251 9 803 48 8 g251P9_803 g251P9_851) (@joinRow g251 9 859 48 48 g251P9_859 g251P9_907)) (@joinRow g251 9 955 96 144 (@joinRow g251 9 955 48 48 g251P9_955 g251P9_1003) (@joinRow g251 9 1051 48 96 g251P9_1051 (@joinRow g251 9 1099 48 48 g251P9_1099 g251P9_1147)))) (@joinRow g251 9 1195 192 173 (@joinRow g251 9 1195 96 96 (@joinRow g251 9 1195 48 48 g251P9_1195 g251P9_1243) (@joinRow g251 9 1291 48 48 g251P9_1291 g251P9_1339)) (@joinRow g251 9 1387 76 97 (@joinRow g251 9 1387 48 28 g251P9_1387 g251P9_1435) (@joinRow g251 9 1463 32 65 g251P9_1463 (@joinRow g251 9 1495 48 17 g251P9_1495 g251P9_1543))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251B10 : CutRow g251 10 0 262 := by
  have g251P10_0 : CutRow g251 10 0 6 := by
    apply checkedCells 7 0
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
  have g251P10_6 : CutRow g251 10 6 48 := by
    apply checkedCells 8 3
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
  have g251P10_54 : CutRow g251 10 54 48 := by
    apply checkedCells 8 3
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
  have g251P10_102 : CutRow g251 10 102 30 := by
    apply checkedCells 8 3
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
  have g251P10_132 : CutRow g251 10 132 48 := by
    apply checkedCells 9 3
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
  have g251P10_180 : CutRow g251 10 180 48 := by
    apply checkedCells 9 3
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
  have g251P10_228 : CutRow g251 10 228 34 := by
    apply checkedCells 9 3
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
  exact (@joinRow g251 10 0 102 160 (@joinRow g251 10 0 6 96 g251P10_0 (@joinRow g251 10 6 48 48 g251P10_6 g251P10_54)) (@joinRow g251 10 102 78 82 (@joinRow g251 10 102 30 48 g251P10_102 g251P10_132) (@joinRow g251 10 180 48 34 g251P10_180 g251P10_228)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251B11 : CutRow g251 11 0 16 := by
  have g251P11_0 : CutRow g251 11 0 1 := by
    apply checkedCells 7 0
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
  have g251P11_1 : CutRow g251 11 1 15 := by
    apply checkedCells 8 2
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
  exact (@joinRow g251 11 0 1 15 g251P11_0 g251P11_1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251B12 : CutRow g251 12 0 1 := by
  have g251P12_0 : CutRow g251 12 0 1 := by
    apply checkedCells 7 0
    simp only [cells,boxes]
    repeat' apply And.intro
    all_goals decide +kernel
  exact g251P12_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251T : mixedTables g251 12 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty g251 0 0
  · exact mixedEmpty g251 1 0
  · exact mixedEmpty g251 2 0
  · exact mixedEmpty g251 3 0
  · exact mixedEmpty g251 4 0
  · exact mixedEmpty g251 5 0
  · exact g251B6
  · exact g251B7
  · exact g251B8
  · exact g251B9
  · exact g251B10
  · exact g251B11
  · exact g251B12
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251G : graphValid g251 (boundsBefore K250) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low251 : Lower true (varsX 251) (graphGoal 251) 13 := mixedLower (g:=g251) (i:=0) (hints:=65603) (before_sound K250 V250) g251G g251T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K251 := extendKnown K250 13 [(251,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V251 : Known true K251 := extend_ok (m:=251) V250 low251 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255R : Impossible true graph 13 sevenInputs.toFinset := by
  change Impossible true (graphGoal 255) 13 sevenInputs.toFinset
  exact cut_root (m:=255) (before_sound K251 V251) (4, 0, 251, 0, 13) (by decide +kernel) (by decide +kernel)

end PEqualNP.Outside.L_meta_34784

open PEqualNP.Outside.L_meta_34784 in
theorem PEqualNP.Outside.L_meta_34784 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o fit _ correct
  exact replaceShort g255R gates o fit correct

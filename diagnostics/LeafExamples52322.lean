import PEqualNP.Defs

-- The two-mode live-state and cofactor checker follows L_meta_1674 and L_meta_670.
-- The graph, restrictions and all search certificates below are for L_meta_52322.

-- Shared forest and cofactor certificates from L_meta_1674 and PR 11111 for L_meta_1677.
-- The original credit line is retained below. The two root certificates here cover the unpinned graph.

-- The checker and the bound certificates are adapted from PEqualNP/Outside/L_meta_1667.lean (Apache-2.0).
-- Two modes: u=false are monotone runs (AND, OR); u=true are runs up to complement, where negation is free.
namespace PEqualNP.Outside.L_meta_52322
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
def graph : Sig := (BitVec.ofNat 512 (word80 [0xffffffff,0xffffffffffffffffffff,0xfffefffffffffffffffa,0xfffeffeefefcaa00ffff,0xffffffffffffffffffff,0xfffffffeffffffffffff,0xfffafffeffeefefcaa00]))
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
  (x 0 &&& x 3) ||| (x 1 &&& x 4) ||| (x 2 &&& x 4) ||| (x 0 &&& x 5) ||| (x 1 &&& x 5) ||| (x 3 &&& x 5) ||| (x 0 &&& x 6) ||| (x 2 &&& x 6) ||| (x 3 &&& x 6) ||| (x 4 &&& x 6) ||| (x 5 &&& x 6) ||| (x 0 &&& x 7) ||| (x 1 &&& x 7) ||| (x 2 &&& x 7) ||| (x 3 &&& x 7) ||| (x 4 &&& x 7) ||| (x 5 &&& x 7) ||| (x 6 &&& x 7)
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
namespace PriceThree
abbrev LocalSix := BitVec 6
private def localFun (x : LocalSix) : Wire (Fin 6) := fun i => x.getLsbD i.val
private def localWord (f : Wire (Fin 6)) : LocalSix :=
  (BitVec.ofBoolListLE (List.ofFn f)).cast List.length_ofFn
private theorem local_read (f : Wire (Fin 6)) (i : Fin 6) :
    (localWord f).getLsbD i.val = f i := by
  simp only [localWord,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [i.isLt]
private theorem local_ext {a b : LocalSix} (eq : ∀ i : Fin 6, localFun a i = localFun b i) : a=b :=
  BitVec.eq_of_getLsbD_eq fun j h => eq ⟨j,h⟩
private theorem local_back (x : LocalSix) : localWord (localFun x)=x := by
  apply local_ext
  intro i
  exact local_read _ _
private theorem local_inv (a : Wire (Fin 6)) : localWord (inv a) = ~~~localWord a := by
  apply local_ext
  intro i
  change (localWord (inv a)).getLsbD i.val = (~~~localWord a).getLsbD i.val
  rw [local_read, BitVec.getLsbD_not, local_read] <;>
    simp [inv, i.isLt]
private theorem local_combine (op : Bool) (a b : Wire (Fin 6)) :
    localWord (combine op a b) = if op then localWord a ||| localWord b else localWord a &&& localWord b := by
  cases op <;> apply local_ext <;> intro i
  · change (localWord (combine false a b)).getLsbD i.val = (localWord a &&& localWord b).getLsbD i.val
    rw [local_read, BitVec.getLsbD_and, local_read, local_read] <;> rfl
  · change (localWord (combine true a b)).getLsbD i.val = (localWord a ||| localWord b).getLsbD i.val
    rw [local_read, BitVec.getLsbD_or, local_read, local_read] <;> rfl
private def localBag (B : List LocalSix) := 0 :: 63 :: (B ++ B.map (fun a => ~~~a))
private theorem local_available {bank v} (ha : Available true bank v) :
    localWord v ∈ localBag (bank.map localWord) := by
  simp only [localBag,List.mem_cons,List.mem_append,List.mem_map]
  rcases ha with hv | ⟨b,rfl⟩ | ⟨_,hn⟩
  · exact Or.inr (Or.inr (Or.inl ⟨_,hv,rfl⟩))
  · cases b
    · exact Or.inl (by decide +kernel)
    · exact Or.inr (Or.inl (by decide +kernel))
  · right; right; right
    exact ⟨_,⟨_,hn,rfl⟩,by rw [local_inv]; simp⟩
private def genLocal (B : List LocalSix) :=
  ((localBag B).flatMap fun a => (localBag B).flatMap fun b => [a &&& b, a ||| b]).eraseDups
private theorem local_next {bank a b} (op : Bool) (ha : Available true bank a) (hb : Available true bank b) :
    localWord (combine op a b) ∈ genLocal (bank.map localWord) := by
  simp only [genLocal,List.mem_eraseDups,List.mem_flatMap]
  refine ⟨_,local_available ha,_,local_available hb,?_⟩
  cases op <;> simp [local_combine]
private def localMiss (M : LocalSix) : Nat → List LocalSix → Bool
  | 0,B => !(localBag B).contains M
  | n+1,B => !(localBag B).contains M && (genLocal B).all (fun w => localMiss M n (w::B))
private theorem local_prefix {roots p bank} (h : Reach true roots p bank) (M : LocalSix) :
    ∀ d, localMiss M (p+d) (roots.map localWord) = true → localMiss M d (bank.map localWord) = true := by
  induction h using Reach.ind with
  | start => intro d hd; simpa only [Nat.zero_add] using hd
  | two op h ha hb ih =>
    intro d hd
    have old := ih (d+1) (by simpa only [Nat.succ_add,Nat.add_succ] using hd)
    simp only [localMiss,Bool.and_eq_true,List.all_eq_true] at old
    exact old.2 _ (local_next op ha hb)
private def missesPair (M a b : LocalSix) :=
  decide (M ≠ (a &&& b) ∧ M ≠ ~~~(a &&& b) ∧ M ≠ (a ||| b) ∧ M ≠ ~~~(a ||| b))
private def fastLast (M : LocalSix) (B : List LocalSix) :=
  !(localBag B).contains M && (localBag B).all (fun a => (localBag B).all (missesPair M a))
private theorem fastLast_sound {M B} (h : fastLast M B=true) : localMiss M 1 B=true := by
  simp only [fastLast,Bool.and_eq_true,List.all_eq_true,missesPair,decide_eq_true_eq] at h
  change (!(localBag B).contains M && (genLocal B).all (fun w => !(localBag (w::B)).contains M))=true
  rw [Bool.and_eq_true]
  refine ⟨h.1,List.all_eq_true.mpr ?_⟩
  intro w hw
  have grow : M ∈ localBag (w::B) → M=w ∨ M = ~~~w ∨ M ∈ localBag B := by
    simp only [localBag,List.map_cons,List.mem_cons,List.mem_append]
    tauto
  have outside : M ∉ localBag B := by simpa using h.1
  have absent : M ∉ localBag (w::B) := by
    intro hm
    have yes := grow hm
    simp only [genLocal,List.mem_eraseDups,List.mem_flatMap,List.mem_cons,List.not_mem_nil,or_false] at hw
    obtain ⟨a,ha,b,hb,eq⟩ := hw
    have ne := h.2 a ha b hb
    rcases eq with rfl | rfl
    · exact yes.elim ne.1 (fun x => x.elim ne.2.1 outside)
    · exact yes.elim ne.2.2.1 (fun x => x.elim ne.2.2.2 outside)
  simpa using absent
private def fastTwo (M : LocalSix) (B : List LocalSix) :=
  !(localBag B).contains M && (genLocal B).all (fun w => fastLast M (w::B))
private theorem fastTwo_sound {M B} (h : fastTwo M B=true) : localMiss M 2 B=true := by
  simp only [fastTwo,Bool.and_eq_true,List.all_eq_true] at h
  change (!(localBag B).contains M && (genLocal B).all (fun w => localMiss M 1 (w::B)))=true
  rw [Bool.and_eq_true]
  exact ⟨h.1,List.all_eq_true.mpr (fun w hw => fastLast_sound (h.2 w hw))⟩

private def majRoots : List LocalSix := [25,42,52]
private def majGoal : LocalSix := 56

private def permWord (p : Fin 6 → Fin 6) (w : LocalSix) := localWord fun i => localFun w (p i)
private theorem perm_not (p) (w) : permWord p (~~~w) = ~~~(permWord p w) := by
  apply local_ext
  intro i
  change (localWord _).getLsbD i.val = (~~~localWord _).getLsbD i.val
  rw [local_read, BitVec.getLsbD_not,local_read] <;>
    simp [localFun, (p i).isLt, i.isLt]
private theorem perm_and (p) (a b) : permWord p (a &&& b) = permWord p a &&& permWord p b := by
  apply local_ext
  intro i
  change (localWord _).getLsbD i.val = (localWord _ &&& localWord _).getLsbD i.val
  rw [local_read,BitVec.getLsbD_and,local_read,local_read] <;>
    simp only [localFun,BitVec.getLsbD_and]
private theorem perm_or (p) (a b) : permWord p (a ||| b) = permWord p a ||| permWord p b := by
  apply local_ext
  intro i
  change (localWord _).getLsbD i.val = (localWord _ ||| localWord _).getLsbD i.val
  rw [local_read,BitVec.getLsbD_or,local_read,local_read] <;>
    simp only [localFun,BitVec.getLsbD_or]
private def embeds (p : Fin 6 → Fin 6) (a b : List LocalSix) := (localBag a).all fun w => (localBag b).contains (permWord p w)
private theorem emb_ok (p) (a b) : embeds p a b = true ↔ ∀ w ∈ localBag a, permWord p w ∈ localBag b := by
  simp only [embeds,List.all_eq_true,List.contains_eq_mem,decide_eq_true_eq]
private theorem bag_cons (x w : LocalSix) (B : List LocalSix) :
    x ∈ localBag (w::B) ↔ x=w ∨ x = ~~~w ∨ x ∈ localBag B := by
  simp only [localBag,List.map_cons,List.mem_cons,List.mem_append]
  tauto
private theorem emb_cons {p a b} (h : embeds p a b=true) (w) :
    embeds p (w::a) (permWord p w::b)=true := by
  apply (emb_ok _ _ _).mpr
  intro x hx
  apply (bag_cons _ _ _).mpr
  rcases (bag_cons _ _ _).mp hx with rfl | rfl | old
  · exact Or.inl rfl
  · exact Or.inr (Or.inl (perm_not _ _))
  · exact Or.inr (Or.inr ((emb_ok _ _ _).mp h x old))
private theorem emb_move {p a b w} (h : embeds p a b=true) (mw : w ∈ genLocal a) :
    permWord p w ∈ genLocal b := by
  simp only [genLocal,List.mem_eraseDups,List.mem_flatMap,List.mem_cons,List.not_mem_nil,or_false] at mw ⊢
  obtain ⟨x,hx,y,hy,hw⟩ := mw
  refine ⟨_,(emb_ok _ _ _).mp h x hx,_,(emb_ok _ _ _).mp h y hy,?_⟩
  rcases hw with rfl | rfl
  · exact Or.inl (perm_and _ _ _)
  · exact Or.inr (perm_or _ _ _)
private theorem pullMiss {p M} (fixed : permWord p M=M) (n : Nat) {a b}
    (cov : embeds p a b=true) (no : localMiss M n b=true) : localMiss M n a=true := by
  induction n generalizing a b with
  | zero =>
    simp only [localMiss,Bool.not_eq_true',List.contains_eq_mem,decide_eq_false_iff_not] at no ⊢
    intro hm
    exact no (fixed ▸ (emb_ok _ _ _).mp cov M hm)
  | succ n ih =>
    simp only [localMiss,Bool.and_eq_true,Bool.not_eq_true',List.contains_eq_mem,decide_eq_false_iff_not,List.all_eq_true] at no ⊢
    refine ⟨fun hm => no.1 (fixed ▸ (emb_ok _ _ _).mp cov M hm),?_⟩
    intro w hw
    exact ih (emb_cons cov _) (no.2 _ (emb_move cov hw))

private def axisData : Array Nat := #[181896,178256,153217,145937,120898,117258]
private def rootHints : Array Nat := #[0,8,10,0,12,0,0,0,64,72,74,0,0,0,0,0,65,73,0,0,76,0,0,0,0,0,0,77,0,75,0,67,67,0,75,0,77,0,0,0,0,0,0,76,0,0,73,65,0,0,0,0,0,74,72,64,0,0,0,12,0,10,8,0]

private def rootTag (w : LocalSix) := rootHints[w.toNat]?.getD 0
private def rootCase (w : LocalSix) := BitVec.ofNat 6 (rootTag w / 8)
private def rootAxis (w : LocalSix) (i : Fin 6) := Fin.ofNat 6 ((axisData[rootTag w % 8]?.getD 0 >>> (3*i.val)) % 8)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem firstPortfolio : ∀ w ∈ genLocal majRoots,
    permWord (rootAxis w) majGoal = majGoal ∧ embeds (rootAxis w) (w::majRoots) (rootCase w::majRoots)=true ∧
      rootCase w ∈ ([0,1,8,9] : List LocalSix) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem cheapFirst0 : localMiss majGoal 2 (0::majRoots)=true := by apply fastTwo_sound; decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem cheapFirst1 : localMiss majGoal 2 (1::majRoots)=true := by apply fastTwo_sound; decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem cheapFirst8 : localMiss majGoal 2 (8::majRoots)=true := by apply fastTwo_sound; decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem cheapFirst9 : localMiss majGoal 2 (9::majRoots)=true := by apply fastTwo_sound; decide +kernel

private theorem local_miss_three : localMiss majGoal 3 majRoots=true := by
  change (_ && _) = true
  rw [Bool.and_eq_true]
  refine ⟨by decide +kernel,List.all_eq_true.mpr ?_⟩
  intro w hw
  obtain ⟨fixed, emb, sel⟩ := firstPortfolio w hw
  apply pullMiss fixed 2 emb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at sel
  rcases sel with e | e | e | e
  · simpa only [e] using cheapFirst0
  · simpa only [e] using cheapFirst1
  · simpa only [e] using cheapFirst8
  · simpa only [e] using cheapFirst9

private theorem local_now {M n B} (h : localMiss M n B=true) : M ∉ localBag B := by
  cases n with
  | zero => simpa only [localMiss,Bool.not_eq_true',List.contains_eq_mem,decide_eq_false_iff_not] using h
  | succ n =>
    simp only [localMiss,Bool.and_eq_true] at h
    simpa only [Bool.not_eq_true',List.contains_eq_mem,decide_eq_false_iff_not] using h.1
theorem majority_six_price {p bank} (reach : Reach true (majRoots.map localFun) p bank)
    (ok : Available true bank (localFun majGoal)) : 4 ≤ p := by
  by_contra small
  have le : p ≤ 3 := by omega
  have start : localMiss majGoal (p+(3-p)) ((majRoots.map localFun).map localWord)=true := by
    rw [show p+(3-p)=3 by omega]
    change localMiss majGoal 3 [localWord (localFun 25), localWord (localFun 42), localWord (localFun 52)] = true
    simpa only [majRoots,local_back] using local_miss_three
  have no := local_now (local_prefix reach _ _ start)
  have yes := local_available ok
  rw [local_back] at yes
  exact no yes

end PriceThree
namespace PatternFive
abbrev LocalSix := BitVec 7
private def localFun (x : LocalSix) : Wire (Fin 7) := fun i => x.getLsbD i.val
private def localWord (f : Wire (Fin 7)) : LocalSix :=
  (BitVec.ofBoolListLE (List.ofFn f)).cast List.length_ofFn
private theorem local_read (f : Wire (Fin 7)) (i : Fin 7) :
    (localWord f).getLsbD i.val = f i := by
  simp only [localWord,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [i.isLt]
private theorem local_ext {a b : LocalSix} (eq : ∀ i : Fin 7, localFun a i = localFun b i) : a=b :=
  BitVec.eq_of_getLsbD_eq fun j h => eq ⟨j,h⟩
private theorem local_back (x : LocalSix) : localWord (localFun x)=x := by
  apply local_ext
  intro i
  exact local_read _ _
private theorem local_inv (a : Wire (Fin 7)) : localWord (inv a) = ~~~localWord a := by
  apply local_ext
  intro i
  change (localWord (inv a)).getLsbD i.val = (~~~localWord a).getLsbD i.val
  rw [local_read, BitVec.getLsbD_not, local_read] <;>
    simp [inv, i.isLt]
private theorem local_combine (op : Bool) (a b : Wire (Fin 7)) :
    localWord (combine op a b) = if op then localWord a ||| localWord b else localWord a &&& localWord b := by
  cases op <;> apply local_ext <;> intro i
  · change (localWord (combine false a b)).getLsbD i.val = (localWord a &&& localWord b).getLsbD i.val
    rw [local_read, BitVec.getLsbD_and, local_read, local_read] <;> rfl
  · change (localWord (combine true a b)).getLsbD i.val = (localWord a ||| localWord b).getLsbD i.val
    rw [local_read, BitVec.getLsbD_or, local_read, local_read] <;> rfl
private def localBag (B : List LocalSix) := 0 :: 127 :: (B ++ B.map (fun a => ~~~a))
private theorem local_available {bank v} (ha : Available true bank v) :
    localWord v ∈ localBag (bank.map localWord) := by
  simp only [localBag,List.mem_cons,List.mem_append,List.mem_map]
  rcases ha with hv | ⟨b,rfl⟩ | ⟨_,hn⟩
  · exact Or.inr (Or.inr (Or.inl ⟨_,hv,rfl⟩))
  · cases b
    · exact Or.inl (by decide +kernel)
    · exact Or.inr (Or.inl (by decide +kernel))
  · right; right; right
    exact ⟨_,⟨_,hn,rfl⟩,by rw [local_inv]; simp⟩
private def genLocal (B : List LocalSix) :=
  ((localBag B).flatMap fun a => (localBag B).flatMap fun b => [a &&& b, a ||| b]).eraseDups
private theorem local_next {bank a b} (op : Bool) (ha : Available true bank a) (hb : Available true bank b) :
    localWord (combine op a b) ∈ genLocal (bank.map localWord) := by
  simp only [genLocal,List.mem_eraseDups,List.mem_flatMap]
  refine ⟨_,local_available ha,_,local_available hb,?_⟩
  cases op <;> simp [local_combine]
private def localMiss (M : LocalSix) : Nat → List LocalSix → Bool
  | 0,B => !(localBag B).contains M
  | n+1,B => !(localBag B).contains M && (genLocal B).all (fun w => localMiss M n (w::B))
private theorem local_prefix {roots p bank} (h : Reach true roots p bank) (M : LocalSix) :
    ∀ d, localMiss M (p+d) (roots.map localWord) = true → localMiss M d (bank.map localWord) = true := by
  induction h using Reach.ind with
  | start => intro d hd; simpa only [Nat.zero_add] using hd
  | two op h ha hb ih =>
    intro d hd
    have old := ih (d+1) (by simpa only [Nat.succ_add,Nat.add_succ] using hd)
    simp only [localMiss,Bool.and_eq_true,List.all_eq_true] at old
    exact old.2 _ (local_next op ha hb)
private def missesPair (M a b : LocalSix) :=
  decide (M ≠ (a &&& b) ∧ M ≠ ~~~(a &&& b) ∧ M ≠ (a ||| b) ∧ M ≠ ~~~(a ||| b))
private def fastLast (M : LocalSix) (B : List LocalSix) :=
  !(localBag B).contains M && (localBag B).all (fun a => (localBag B).all (missesPair M a))
private theorem fastLast_sound {M B} (h : fastLast M B=true) : localMiss M 1 B=true := by
  simp only [fastLast,Bool.and_eq_true,List.all_eq_true,missesPair,decide_eq_true_eq] at h
  change (!(localBag B).contains M && (genLocal B).all (fun w => !(localBag (w::B)).contains M))=true
  rw [Bool.and_eq_true]
  refine ⟨h.1,List.all_eq_true.mpr ?_⟩
  intro w hw
  have grow : M ∈ localBag (w::B) → M=w ∨ M = ~~~w ∨ M ∈ localBag B := by
    simp only [localBag,List.map_cons,List.mem_cons,List.mem_append]
    tauto
  have outside : M ∉ localBag B := by simpa using h.1
  have absent : M ∉ localBag (w::B) := by
    intro hm
    have yes := grow hm
    simp only [genLocal,List.mem_eraseDups,List.mem_flatMap,List.mem_cons,List.not_mem_nil,or_false] at hw
    obtain ⟨a,ha,b,hb,eq⟩ := hw
    have ne := h.2 a ha b hb
    rcases eq with rfl | rfl
    · exact yes.elim ne.1 (fun x => x.elim ne.2.1 outside)
    · exact yes.elim ne.2.2.1 (fun x => x.elim ne.2.2.2 outside)
  simpa using absent
private def fastTwo (M : LocalSix) (B : List LocalSix) :=
  !(localBag B).contains M && (genLocal B).all (fun w => fastLast M (w::B))
private theorem fastTwo_sound {M B} (h : fastTwo M B=true) : localMiss M 2 B=true := by
  simp only [fastTwo,Bool.and_eq_true,List.all_eq_true] at h
  change (!(localBag B).contains M && (genLocal B).all (fun w => localMiss M 1 (w::B)))=true
  rw [Bool.and_eq_true]
  exact ⟨h.1,List.all_eq_true.mpr (fun w hw => fastLast_sound (h.2 w hw))⟩

private def majRoots : List LocalSix := [43,42,76,112]
private def majGoal : LocalSix := 22
private def permWord (p : Fin 7 → Fin 7) (w : LocalSix) := localWord fun i => localFun w (p i)
private theorem perm_not (p) (w) : permWord p (~~~w) = ~~~(permWord p w) := by
  apply local_ext
  intro i
  change (localWord _).getLsbD i.val = (~~~localWord _).getLsbD i.val
  rw [local_read, BitVec.getLsbD_not,local_read] <;>
    simp [localFun, (p i).isLt, i.isLt]
private theorem perm_and (p) (a b) : permWord p (a &&& b) = permWord p a &&& permWord p b := by
  apply local_ext
  intro i
  change (localWord _).getLsbD i.val = (localWord _ &&& localWord _).getLsbD i.val
  rw [local_read,BitVec.getLsbD_and,local_read,local_read] <;>
    simp only [localFun,BitVec.getLsbD_and]
private theorem perm_or (p) (a b) : permWord p (a ||| b) = permWord p a ||| permWord p b := by
  apply local_ext
  intro i
  change (localWord _).getLsbD i.val = (localWord _ ||| localWord _).getLsbD i.val
  rw [local_read,BitVec.getLsbD_or,local_read,local_read] <;>
    simp only [localFun,BitVec.getLsbD_or]
private def embeds (p : Fin 7 → Fin 7) (a b : List LocalSix) := (localBag a).all fun w => (localBag b).contains (permWord p w)
private theorem emb_ok (p) (a b) : embeds p a b = true ↔ ∀ w ∈ localBag a, permWord p w ∈ localBag b := by
  simp only [embeds,List.all_eq_true,List.contains_eq_mem,decide_eq_true_eq]
private theorem bag_cons (x w : LocalSix) (B : List LocalSix) :
    x ∈ localBag (w::B) ↔ x=w ∨ x = ~~~w ∨ x ∈ localBag B := by
  simp only [localBag,List.map_cons,List.mem_cons,List.mem_append]
  tauto
private theorem emb_cons {p a b} (h : embeds p a b=true) (w) :
    embeds p (w::a) (permWord p w::b)=true := by
  apply (emb_ok _ _ _).mpr
  intro x hx
  apply (bag_cons _ _ _).mpr
  rcases (bag_cons _ _ _).mp hx with rfl | rfl | old
  · exact Or.inl rfl
  · exact Or.inr (Or.inl (perm_not _ _))
  · exact Or.inr (Or.inr ((emb_ok _ _ _).mp h x old))
private theorem emb_move {p a b w} (h : embeds p a b=true) (mw : w ∈ genLocal a) :
    permWord p w ∈ genLocal b := by
  simp only [genLocal,List.mem_eraseDups,List.mem_flatMap,List.mem_cons,List.not_mem_nil,or_false] at mw ⊢
  obtain ⟨x,hx,y,hy,hw⟩ := mw
  refine ⟨_,(emb_ok _ _ _).mp h x hx,_,(emb_ok _ _ _).mp h y hy,?_⟩
  rcases hw with rfl | rfl
  · exact Or.inl (perm_and _ _ _)
  · exact Or.inr (perm_or _ _ _)
private theorem pullMiss {p M} (fixed : permWord p M=M) (n : Nat) {a b}
    (cov : embeds p a b=true) (no : localMiss M n b=true) : localMiss M n a=true := by
  induction n generalizing a b with
  | zero =>
    simp only [localMiss,Bool.not_eq_true',List.contains_eq_mem,decide_eq_false_iff_not] at no ⊢
    intro hm
    exact no (fixed ▸ (emb_ok _ _ _).mp cov M hm)
  | succ n ih =>
    simp only [localMiss,Bool.and_eq_true,Bool.not_eq_true',List.contains_eq_mem,decide_eq_false_iff_not,List.all_eq_true] at no ⊢
    refine ⟨fun hm => no.1 (fixed ▸ (emb_ok _ _ _).mp cov M hm),?_⟩
    intro w hw
    exact ih (emb_cons cov _) (no.2 _ (emb_move cov hw))

private def axisData : Array Nat := #[1754760,1682184]
private def axisOf (t : Nat) (j : Fin 7) : Fin 7 := Fin.ofNat 7 ((axisData[t % 2]?.getD 0 >>> (3*j.val)) % 8)
private def state0 (_ : Nat) := majRoots
private def extras1 : Array (List LocalSix) := #[[],[4],[8],[10],[12],[64],[68],[92],[110],[124],[126]]
private def state1 (i : Nat) := (extras1[i]?.getD []) ++ majRoots
private def extras2 : Array (List LocalSix) := #[[],[2,10],[2,124],[4],[4,8],[4,10],[4,12],[4,16],[4,32],[4,34],[4,46],[4,48],[4,64],[4,68],[4,72],[4,80],[4,92],[4,110],[4,116],[4,122],[4,124],[4,126],[8],[8,10],[8,12],[8,32],[8,34],[8,48],[8,64],[8,68],[8,80],[8,92],[8,110],[8,116],[8,120],[8,122],[8,124],[8,126],[10],[10,12],[10,34],[10,48],[10,64],[10,68],[10,78],[10,80],[10,92],[10,94],[10,110],[10,116],[10,122],[10,124],[10,126],[12],[12,46],[12,48],[12,64],[12,68],[12,80],[12,92],[12,110],[12,116],[12,122],[12,124],[12,126],[14,110],[14,126],[20,64],[40,124],[64],[64,68],[64,92],[64,106],[64,110],[64,124],[64,126],[68],[68,80],[68,92],[68,110],[68,116],[68,122],[68,124],[68,126],[72,122],[92],[92,110],[92,116],[92,122],[92,124],[92,126],[110],[110,122],[110,124],[110,126],[124],[124,126],[126]]
private def state2 (i : Nat) := (extras2[i]?.getD []) ++ majRoots
private def badData : Array Nat := #[(word80 [0x2000000,0x400000]),(word80 [0x3000000,0x0]),5242880,0,4456448,0,5570560,0,(word80 [0x2020000,0x0]),(word80 [0x3030000,0x0]),0,0,0,0,0,0,4194368,0,5242960,0,4456516,0,(word80 [0xc0c00000c0c0,0xc0c00000c0d50055]),(word80 [0x404000004040,0x4040000040400000]),0,0,0,0,0,0,(word80 [0xc0000000c0,0xc0000000c00000]),(word80 [0x4000000040,0x40000000400000]),(word80 [0x2000000,0x2000000000000000000]),(word80 [0x3000000,0x3000000000000000000]),0,0,0,0,0,0,(word80 [0x2020000,0x2020000000000000000]),(word80 [0x3030000,0x3030000000000000000]),0,0,0,0,0,0,0,0,0,0,0,0,(word80 [0xc0c0,0xc0c00000]),(word80 [0x4040,0x40400000]),0,0,0,0,0,0,(word80 [0xc0,0xc00000]),(word80 [0x40,0x400000]),(word80 [0x2000000,0x20000000000]),(word80 [0x3000000,0x30000000000]),0,0,0,0,0,0,(word80 [0x2020000,0x20200000000]),(word80 [0x3030000,0x30300000000]),0,0,0,0,0,0,0,0,0,0,0,0,(word80 [0x0,0xc0c00000c0c00000]),4629700418014806016,0,0,0,0,0,0,54043195541028864,18014398513676288,(word80 [0x2000000,0x2000000020000000200]),(word80 [0x3000000,0x3000000030000000300]),0,0,0,0,0,0,(word80 [0x2020000,0x2020000020200000202]),(word80 [0xaa00ab030000,0x3030000030300000303]),0,(word80 [0x220022000000,0x0]),0,(word80 [0xa000a000000,0x0]),0,(word80 [0x20002000000,0x0]),0,0,0,0,0,0,3233808384,1077936128,0,(word80 [0xaa000000,0x0]),0,(word80 [0x22000000,0x0]),0,(word80 [0xa000000,0x0]),12582912,(word80 [0x2000000,0x400000])]
private def badMask (w : LocalSix) := badData[w.toNat]?.getD 0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem badMask_ok : ∀ a v : LocalSix, (badMask a).testBit v.toNat = !(missesPair majGoal a v) := by decide +kernel

private def allowsWord (cover : Nat) (w : LocalSix) := cover.testBit w.toNat
private def paidCell (B : List LocalSix) (cover : Nat) :=
  (!allowsWord cover majGoal) && (localBag B).all (allowsWord cover) &&
  (localBag B).all (fun w => (cover &&& badMask w) == 0) &&
  (genLocal B).all fun w => allowsWord cover w && allowsWord cover (~~~w)
private theorem antiPair : ∀ w : LocalSix, w ≠ majGoal → ~~~w ≠ majGoal →
    ∀ a b : Bool, missesPair majGoal (if a then w else ~~~w) (if b then w else ~~~w)=true := by decide +kernel
private theorem pairRev (a b : LocalSix) : missesPair majGoal a b=missesPair majGoal b a := by
  simp only [missesPair,BitVec.and_comm a b,BitVec.or_comm a b]
private theorem paidCell_sound {B K} (pass : paidCell B K=true) : localMiss majGoal 2 B=true := by
  simp only [paidCell,Bool.and_eq_true,Bool.not_eq_true',List.all_eq_true,beq_iff_eq] at pass
  obtain ⟨⟨⟨off,old⟩,clean⟩,moves⟩ := pass
  have avoid {v} (on : allowsWord K v=true) : v≠majGoal := by
    intro eq
    subst v
    rw [off] at on
    contradiction
  have guard {a v} (ha : a∈localBag B) (hV : allowsWord K v=true) : missesPair majGoal a v=true := by
    have eq := congrArg (fun n : Nat => n.testBit v.toNat) (clean a ha)
    change K.testBit v.toNat=true at hV
    simpa [Nat.testBit_and,hV,badMask_ok] using eq
  have oldNo : !(localBag B).contains majGoal = true := by
    have no : majGoal ∉ localBag B := fun p => avoid (old _ p) rfl
    simpa using no
  apply fastTwo_sound
  simp only [fastTwo,Bool.and_eq_true,List.all_eq_true]
  refine ⟨oldNo,?_⟩
  intro w hw
  have win := moves w hw
  have membership {a} (ha : a∈localBag (w::B)) : allowsWord K a=true := by
    rcases (bag_cons a w B).mp ha with rfl | rfl | original
    · exact win.1
    · exact win.2
    · exact old _ original
  simp only [fastLast,Bool.and_eq_true,List.all_eq_true]
  have no : majGoal ∉ localBag (w::B) := fun hx => avoid (membership hx) rfl
  refine ⟨by simpa using no,?_⟩
  intro a ha b hb
  by_cases origA : a ∈ localBag B
  · exact guard origA (membership hb)
  by_cases origB : b ∈ localBag B
  · rw [pairRev]
    exact guard origB (membership ha)
  have da := (bag_cons a w B).mp ha
  have db := (bag_cons b w B).mp hb
  have core := antiPair w (avoid win.1) (avoid win.2)
  rcases da with rfl | rfl | bad
  · rcases db with rfl | rfl | bad
    · exact core true true
    · exact core true false
    · contradiction
  · rcases db with rfl | rfl | bad
    · exact core false true
    · exact core false false
    · contradiction
  · contradiction

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end0 : localMiss majGoal 2 (state2 0)=true := by apply paidCell_sound (K:=(word80 [0xdcb9c000b031,0x901188098c0d00039d3b])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end1 : localMiss majGoal 2 (state2 1)=true := by apply paidCell_sound (K:=(word80 [0xfcbdc000f0f1,0xd011880b8f0f0003bd3f])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end2 : localMiss majGoal 2 (state2 2)=true := by apply paidCell_sound (K:=(word80 [0xfcbdc000b0f1,0xd011880b8f0d0003bd3f])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end3 : localMiss majGoal 2 (state2 3)=true := by apply paidCell_sound (K:=(word80 [0xdcb9c000b033,0x91118889cc0d00039d3b])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end4 : localMiss majGoal 2 (state2 4)=true := by apply paidCell_sound (K:=(word80 [0xddb9c000b033,0x91118889cc0d00039dbb])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end5 : localMiss majGoal 2 (state2 5)=true := by apply paidCell_sound (K:=(word80 [0xfcbbc000f033,0xd111888bcc0f0003dd3f])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end6 : localMiss majGoal 2 (state2 6)=true := by apply paidCell_sound (K:=(word80 [0xdcb9c000b033,0x91118889cc0d00039d3b])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end7 : localMiss majGoal 2 (state2 7)=true := by apply paidCell_sound (K:=(word80 [0xdcb9c801b033,0x91318c89cc0d80139d3b])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end8 : localMiss majGoal 2 (state2 8)=true := by apply paidCell_sound (K:=(word80 [0xdcb9d000b833,0x91118889cc1d000b9d3b])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end9 : localMiss majGoal 2 (state2 9)=true := by apply paidCell_sound (K:=(word80 [0xfcfdc000b233,0x91118889cc4d0003bf3f])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end10 : localMiss majGoal 2 (state2 10)=true := by apply paidCell_sound (K:=(word80 [0xdcbbc000b033,0x91118889cc0d0003dd3b])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end11 : localMiss majGoal 2 (state2 11)=true := by apply paidCell_sound (K:=(word80 [0xdcb9c000b033,0x99318c99cc0d00039d3b])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end12 : localMiss majGoal 2 (state2 12)=true := by apply paidCell_sound (K:=(word80 [0xdcb9cc00b033,0x91118889cc0d00339d3b])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end13 : localMiss majGoal 2 (state2 13)=true := by apply paidCell_sound (K:=(word80 [0xdcb9c000b033,0x91118889cc0d00039d3b])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end14 : localMiss majGoal 2 (state2 14)=true := by apply paidCell_sound (K:=(word80 [0xddb9cc00b033,0x91118889cc0d00339dbb])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end15 : localMiss majGoal 2 (state2 15)=true := by apply paidCell_sound (K:=(word80 [0xdcb9c000b033,0x91118889cc0d00039d3b])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end16 : localMiss majGoal 2 (state2 16)=true := by apply paidCell_sound (K:=(word80 [0xdcb9c000b133,0x91118889cc8d00039d3b])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end17 : localMiss majGoal 2 (state2 17)=true := by apply paidCell_sound (K:=(word80 [0xdcbbc401b033,0x91118889cc0d8023dd3b])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end18 : localMiss majGoal 2 (state2 18)=true := by apply paidCell_sound (K:=(word80 [0xdcb9c000b033,0x91118889cc0d00039d3b])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end19 : localMiss majGoal 2 (state2 19)=true := by apply paidCell_sound (K:=(word80 [0xdcb9c000b033,0xb111888dcc0d00039d3b])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end20 : localMiss majGoal 2 (state2 20)=true := by apply paidCell_sound (K:=(word80 [0xfdb9c000b0b3,0x91118889cd0d00039dbf])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end21 : localMiss majGoal 2 (state2 21)=true := by apply paidCell_sound (K:=(word80 [0xdcbbc000b033,0xb111888dcc0d0003dd3b])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end22 : localMiss majGoal 2 (state2 22)=true := by apply paidCell_sound (K:=(word80 [0xddb9c000b031,0x901188098c0d00039dbb])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end23 : localMiss majGoal 2 (state2 23)=true := by apply paidCell_sound (K:=(word80 [0xfdb9c000f031,0xd011880b8c0f00039dbf])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end24 : localMiss majGoal 2 (state2 24)=true := by apply paidCell_sound (K:=(word80 [0xddb9c000b033,0x90118809cc0d00039dbb])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end25 : localMiss majGoal 2 (state2 25)=true := by apply paidCell_sound (K:=(word80 [0xddb9d000b0b1,0x901188098d0d000b9dbb])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end26 : localMiss majGoal 2 (state2 26)=true := by apply paidCell_sound (K:=(word80 [0xfdfdc000b031,0x901188098c0d0003bfbf])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end27 : localMiss majGoal 2 (state2 27)=true := by apply paidCell_sound (K:=(word80 [0xddb9c000b031,0x90b18d098c0d00039dbb])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end28 : localMiss majGoal 2 (state2 28)=true := by apply paidCell_sound (K:=(word80 [0xddb9cc00b031,0x911188898c0d00339dbb])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end29 : localMiss majGoal 2 (state2 29)=true := by apply paidCell_sound (K:=(word80 [0xddb9c000b031,0x901188098c0d00039dbb])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end30 : localMiss majGoal 2 (state2 30)=true := by apply paidCell_sound (K:=(word80 [0xddb9c000b131,0x901188098c8d00039dbb])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end31 : localMiss majGoal 2 (state2 31)=true := by apply paidCell_sound (K:=(word80 [0xddb9c000b031,0x901188098c0d00039dbb])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end32 : localMiss majGoal 2 (state2 32)=true := by apply paidCell_sound (K:=(word80 [0xddbbc041b031,0x901188098c0d8203ddbb])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end33 : localMiss majGoal 2 (state2 33)=true := by apply paidCell_sound (K:=(word80 [0xddb9c000b031,0x901188098c0d00039dbb])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end34 : localMiss majGoal 2 (state2 34)=true := by apply paidCell_sound (K:=(word80 [0xfdb9c000b0b1,0x911188898d0d00039dbf])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end35 : localMiss majGoal 2 (state2 35)=true := by apply paidCell_sound (K:=(word80 [0xddbdc000b031,0xb111888d8c0d0003bdbb])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end36 : localMiss majGoal 2 (state2 36)=true := by apply paidCell_sound (K:=(word80 [0xfdb9c000b0b1,0x901188098d0d00039dbf])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end37 : localMiss majGoal 2 (state2 37)=true := by apply paidCell_sound (K:=(word80 [0xddfbc000b031,0xb011880d8c0d0003dfbb])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end38 : localMiss majGoal 2 (state2 38)=true := by apply paidCell_sound (K:=(word80 [0xfcb9c000f031,0xd011880b8c0f00039d3f])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end39 : localMiss majGoal 2 (state2 39)=true := by apply paidCell_sound (K:=(word80 [0xfcbbc000f033,0xd011880bcc0f0003dd3f])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end40 : localMiss majGoal 2 (state2 40)=true := by apply paidCell_sound (K:=(word80 [0xfcfdc000f031,0xd011880b8c0f0003bf3f])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end41 : localMiss majGoal 2 (state2 41)=true := by apply paidCell_sound (K:=(word80 [0xfcb9c000f031,0xd0318c0b8c0f00039d3f])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end42 : localMiss majGoal 2 (state2 42)=true := by apply paidCell_sound (K:=(word80 [0xfcb9cc00f031,0xd411882b8c0f00339d3f])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end43 : localMiss majGoal 2 (state2 43)=true := by apply paidCell_sound (K:=(word80 [0xfcb9c000f031,0xd011880b8c0f00039d3f])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end44 : localMiss majGoal 2 (state2 44)=true := by apply paidCell_sound (K:=(word80 [0xfcbbc000f031,0xd011880b8c0f0003dd3f])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end45 : localMiss majGoal 2 (state2 45)=true := by apply paidCell_sound (K:=(word80 [0xfcb9c000f431,0xd011880b8c2f00039d3f])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end46 : localMiss majGoal 2 (state2 46)=true := by apply paidCell_sound (K:=(word80 [0xfcb9c000f031,0xd011880b8c0f00039d3f])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end47 : localMiss majGoal 2 (state2 47)=true := by apply paidCell_sound (K:=(word80 [0xfcbbe000f031,0xd011880b8c0f0007dd3f])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end48 : localMiss majGoal 2 (state2 48)=true := by apply paidCell_sound (K:=(word80 [0xfcbbc011f031,0xd011880b8c0f8803dd3f])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end49 : localMiss majGoal 2 (state2 49)=true := by apply paidCell_sound (K:=(word80 [0xfcb9c000f031,0xd011880b8c0f00039d3f])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end50 : localMiss majGoal 2 (state2 50)=true := by apply paidCell_sound (K:=(word80 [0xfcb9c000f031,0xf111888f8c0f00039d3f])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end51 : localMiss majGoal 2 (state2 51)=true := by apply paidCell_sound (K:=(word80 [0xfcb9c000f0b1,0xd011880b8d0f00039d3f])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end52 : localMiss majGoal 2 (state2 52)=true := by apply paidCell_sound (K:=(word80 [0xfcbbc000f031,0xf011880f8c0f0003dd3f])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end53 : localMiss majGoal 2 (state2 53)=true := by apply paidCell_sound (K:=(word80 [0xdcb9c000b033,0x90118809cc0d00039d3b])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end54 : localMiss majGoal 2 (state2 54)=true := by apply paidCell_sound (K:=(word80 [0xdcbbc000b033,0x90118809cc0d0003dd3b])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end55 : localMiss majGoal 2 (state2 55)=true := by apply paidCell_sound (K:=(word80 [0xdcb9c000b033,0x90399c09cc0d00039d3b])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end56 : localMiss majGoal 2 (state2 56)=true := by apply paidCell_sound (K:=(word80 [0xdcb9cc00b033,0x90118809cc0d00339d3b])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end57 : localMiss majGoal 2 (state2 57)=true := by apply paidCell_sound (K:=(word80 [0xdcb9c000b033,0x90118809cc0d00039d3b])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end58 : localMiss majGoal 2 (state2 58)=true := by apply paidCell_sound (K:=(word80 [0xdcb9c000b033,0x90118809cc0d00039d3b])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end59 : localMiss majGoal 2 (state2 59)=true := by apply paidCell_sound (K:=(word80 [0xdcb9c000b033,0x90118809cc0d00039d3b])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end60 : localMiss majGoal 2 (state2 60)=true := by apply paidCell_sound (K:=(word80 [0xdcbbc005b033,0x90118809cc0da003dd3b])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end61 : localMiss majGoal 2 (state2 61)=true := by apply paidCell_sound (K:=(word80 [0xdcb9c000b033,0x90118809cc0d00039d3b])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end62 : localMiss majGoal 2 (state2 62)=true := by apply paidCell_sound (K:=(word80 [0xdcbdc000b033,0xb111888dcc0d0003bd3b])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end63 : localMiss majGoal 2 (state2 63)=true := by apply paidCell_sound (K:=(word80 [0xfcb9c000b0b3,0x90118809cd0d00039d3f])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end64 : localMiss majGoal 2 (state2 64)=true := by apply paidCell_sound (K:=(word80 [0xdcbfc000b033,0xb011880dcc0d0003fd3b])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end65 : localMiss majGoal 2 (state2 65)=true := by apply paidCell_sound (K:=(word80 [0xfcbbc001f033,0xd011880bcc0f8003dd3f])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end66 : localMiss majGoal 2 (state2 66)=true := by apply paidCell_sound (K:=(word80 [0xfcbbc000f033,0xf011880fcc0f0003dd3f])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end67 : localMiss majGoal 2 (state2 67)=true := by apply paidCell_sound (K:=(word80 [0xdcb9cc01b031,0x9113c8898c0d80339d3b])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end68 : localMiss majGoal 2 (state2 68)=true := by apply paidCell_sound (K:=(word80 [0xfdb9d000b0b1,0x901188098d0d000b9dbf])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end69 : localMiss majGoal 2 (state2 69)=true := by apply paidCell_sound (K:=(word80 [0xdcb9cc00b031,0x901188098c0d00339d3b])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end70 : localMiss majGoal 2 (state2 70)=true := by apply paidCell_sound (K:=(word80 [0xdcb9cc00b031,0x901188098c0d00339d3b])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end71 : localMiss majGoal 2 (state2 71)=true := by apply paidCell_sound (K:=(word80 [0xdcb9cc08b031,0x901188098c0d10339d3b])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end72 : localMiss majGoal 2 (state2 72)=true := by apply paidCell_sound (K:=(word80 [0xdcb9cc01b031,0x911188898c0d80339d3b])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end73 : localMiss majGoal 2 (state2 73)=true := by apply paidCell_sound (K:=(word80 [0xdcbbcc01b033,0x90118809cc0d8033dd3b])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end74 : localMiss majGoal 2 (state2 74)=true := by apply paidCell_sound (K:=(word80 [0xfcb9cc00b0b1,0x901998098d0d00339d3f])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end75 : localMiss majGoal 2 (state2 75)=true := by apply paidCell_sound (K:=(word80 [0xdcbbcc00b031,0xb013c80d8c0d0033dd3b])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end76 : localMiss majGoal 2 (state2 76)=true := by apply paidCell_sound (K:=(word80 [0xdcb9c000b031,0x901188098c0d00039d3b])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end77 : localMiss majGoal 2 (state2 77)=true := by apply paidCell_sound (K:=(word80 [0xdcb9c000b031,0x901188098c0d00039d3b])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end78 : localMiss majGoal 2 (state2 78)=true := by apply paidCell_sound (K:=(word80 [0xdcb9c080b031,0x901188098c0d01039d3b])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end79 : localMiss majGoal 2 (state2 79)=true := by apply paidCell_sound (K:=(word80 [0xdcbbc001b031,0x901188098c0d8003dd3b])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end80 : localMiss majGoal 2 (state2 80)=true := by apply paidCell_sound (K:=(word80 [0xdcb9c000b031,0x901188098c0d00039d3b])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end81 : localMiss majGoal 2 (state2 81)=true := by apply paidCell_sound (K:=(word80 [0xdcb9c000b031,0xb1318c8d8c0d00039d3b])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end82 : localMiss majGoal 2 (state2 82)=true := by apply paidCell_sound (K:=(word80 [0xfcb9c000b0b1,0x909189098d0d00039d3f])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end83 : localMiss majGoal 2 (state2 83)=true := by apply paidCell_sound (K:=(word80 [0xdcbbc000b031,0xb0318c0d8c0d0003dd3b])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end84 : localMiss majGoal 2 (state2 84)=true := by apply paidCell_sound (K:=(word80 [0xddb9cc00b031,0xb111888d8c0d00339dbb])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end85 : localMiss majGoal 2 (state2 85)=true := by apply paidCell_sound (K:=(word80 [0xdcb9c000b031,0x901188098c0d00039d3b])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end86 : localMiss majGoal 2 (state2 86)=true := by apply paidCell_sound (K:=(word80 [0xdcbbc001b031,0x901188098c0d8003dd3b])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end87 : localMiss majGoal 2 (state2 87)=true := by apply paidCell_sound (K:=(word80 [0xdcb9c000b031,0x901188098c0d00039d3b])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end88 : localMiss majGoal 2 (state2 88)=true := by apply paidCell_sound (K:=(word80 [0xdcb9c000b131,0xb111888d8c8d00039d3b])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end89 : localMiss majGoal 2 (state2 89)=true := by apply paidCell_sound (K:=(word80 [0xfcb9c000b0b1,0x901188098d0d00039d3f])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end90 : localMiss majGoal 2 (state2 90)=true := by apply paidCell_sound (K:=(word80 [0xdcbbc000b031,0xb011880d8c0d0003dd3b])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end91 : localMiss majGoal 2 (state2 91)=true := by apply paidCell_sound (K:=(word80 [0xdcbbc001b031,0x901188098c0d8003dd3b])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end92 : localMiss majGoal 2 (state2 92)=true := by apply paidCell_sound (K:=(word80 [0xdcbbc401b031,0xb111888d8c0d8023dd3b])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end93 : localMiss majGoal 2 (state2 93)=true := by apply paidCell_sound (K:=(word80 [0xfcbbd001b0b1,0x901188098d0d800bdd3f])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end94 : localMiss majGoal 2 (state2 94)=true := by apply paidCell_sound (K:=(word80 [0xdcbbc001b031,0xb011880d8c0d8003dd3b])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end95 : localMiss majGoal 2 (state2 95)=true := by apply paidCell_sound (K:=(word80 [0xfcb9c000b0b1,0x901188098d0d00039d3f])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end96 : localMiss majGoal 2 (state2 96)=true := by apply paidCell_sound (K:=(word80 [0xfcbbc000b0b1,0xb011880d8d0d0003dd3f])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end97 : localMiss majGoal 2 (state2 97)=true := by apply paidCell_sound (K:=(word80 [0xdcbbc000b031,0xb011880d8c0d0003dd3b])); decide +kernel
private theorem stage2 : ∀ i : Nat, i < 98 → localMiss majGoal 2 (state2 i)=true
  | 0,_ => end0
  | 1,_ => end1
  | 2,_ => end2
  | 3,_ => end3
  | 4,_ => end4
  | 5,_ => end5
  | 6,_ => end6
  | 7,_ => end7
  | 8,_ => end8
  | 9,_ => end9
  | 10,_ => end10
  | 11,_ => end11
  | 12,_ => end12
  | 13,_ => end13
  | 14,_ => end14
  | 15,_ => end15
  | 16,_ => end16
  | 17,_ => end17
  | 18,_ => end18
  | 19,_ => end19
  | 20,_ => end20
  | 21,_ => end21
  | 22,_ => end22
  | 23,_ => end23
  | 24,_ => end24
  | 25,_ => end25
  | 26,_ => end26
  | 27,_ => end27
  | 28,_ => end28
  | 29,_ => end29
  | 30,_ => end30
  | 31,_ => end31
  | 32,_ => end32
  | 33,_ => end33
  | 34,_ => end34
  | 35,_ => end35
  | 36,_ => end36
  | 37,_ => end37
  | 38,_ => end38
  | 39,_ => end39
  | 40,_ => end40
  | 41,_ => end41
  | 42,_ => end42
  | 43,_ => end43
  | 44,_ => end44
  | 45,_ => end45
  | 46,_ => end46
  | 47,_ => end47
  | 48,_ => end48
  | 49,_ => end49
  | 50,_ => end50
  | 51,_ => end51
  | 52,_ => end52
  | 53,_ => end53
  | 54,_ => end54
  | 55,_ => end55
  | 56,_ => end56
  | 57,_ => end57
  | 58,_ => end58
  | 59,_ => end59
  | 60,_ => end60
  | 61,_ => end61
  | 62,_ => end62
  | 63,_ => end63
  | 64,_ => end64
  | 65,_ => end65
  | 66,_ => end66
  | 67,_ => end67
  | 68,_ => end68
  | 69,_ => end69
  | 70,_ => end70
  | 71,_ => end71
  | 72,_ => end72
  | 73,_ => end73
  | 74,_ => end74
  | 75,_ => end75
  | 76,_ => end76
  | 77,_ => end77
  | 78,_ => end78
  | 79,_ => end79
  | 80,_ => end80
  | 81,_ => end81
  | 82,_ => end82
  | 83,_ => end83
  | 84,_ => end84
  | 85,_ => end85
  | 86,_ => end86
  | 87,_ => end87
  | 88,_ => end88
  | 89,_ => end89
  | 90,_ => end90
  | 91,_ => end91
  | 92,_ => end92
  | 93,_ => end93
  | 94,_ => end94
  | 95,_ => end95
  | 96,_ => end96
  | 97,_ => end97
  | i+98,ht => by omega
private def map1 : Array (Array Nat) := #[#[0,194,0,190,6,183,0,0,44,0,76,171,106,0,0,0,7,182,0,0,0,0,0,0,0,0,0,0,0,0,0,0,45,0,77,170,0,0,0,0,0,0,0,0,0,0,0,153,107,0,0,0,0,0,0,0,0,0,0,152,0,0,0,138,138,0,0,0,152,0,0,0,0,0,0,0,0,0,0,107,153,0,0,0,0,0,0,0,0,0,0,0,170,77,0,45,0,0,0,0,0,0,0,0,0,0,0,0,0,0,182,7,0,0,0,106,171,76,0,44,0,0,183,6,190,0,194,0],#[6,42,0,40,6,38,0,0,8,0,10,36,12,0,0,6,14,34,0,0,0,0,0,0,0,0,0,0,0,0,0,0,16,0,18,32,0,0,0,0,0,0,6,6,0,0,20,30,22,0,0,6,0,0,0,28,0,0,0,26,0,0,0,24,24,0,0,0,26,0,0,0,28,0,0,0,6,0,0,22,30,20,0,0,6,6,0,0,0,0,0,0,32,18,0,16,0,0,0,0,0,0,0,0,0,0,0,0,0,0,34,14,6,0,0,12,36,10,0,8,0,0,38,6,40,0,42,6],#[44,74,0,72,8,70,0,68,44,0,46,66,48,0,0,44,17,64,0,0,0,0,0,0,0,0,0,0,0,0,0,0,50,0,52,62,0,0,0,0,0,0,44,44,0,0,0,60,54,0,0,44,0,0,0,0,0,0,0,58,0,0,0,56,56,0,0,0,58,0,0,0,0,0,0,0,44,0,0,54,60,0,0,0,44,44,0,0,0,0,0,0,62,52,0,50,0,0,0,0,0,0,0,0,0,0,0,0,0,0,64,17,44,0,0,48,66,46,0,44,68,0,70,8,72,0,74,44],#[76,104,2,102,10,100,0,0,46,0,76,98,78,0,0,76,19,96,0,0,0,0,0,0,0,0,0,0,0,0,0,0,53,94,80,92,0,0,0,0,0,0,76,76,0,0,0,90,82,88,0,76,0,0,0,0,0,0,0,86,0,0,0,84,84,0,0,0,86,0,0,0,0,0,0,0,76,0,88,82,90,0,0,0,76,76,0,0,0,0,0,0,92,80,94,53,0,0,0,0,0,0,0,0,0,0,0,0,0,0,96,19,76,0,0,78,98,76,0,46,0,0,100,10,102,2,104,76],#[106,128,0,126,12,124,0,0,48,0,78,122,106,0,0,106,23,120,0,0,0,0,0,0,0,0,0,0,0,0,0,0,55,0,83,118,0,0,0,0,0,0,106,106,0,0,108,116,110,0,0,106,0,0,0,0,0,0,0,114,0,0,0,112,112,0,0,0,114,0,0,0,0,0,0,0,106,0,0,110,116,108,0,0,106,106,0,0,0,0,0,0,118,83,0,55,0,0,0,0,0,0,0,0,0,0,0,0,0,0,120,23,106,0,0,106,122,78,0,48,0,0,124,12,126,0,128,106],#[138,150,0,148,24,147,0,0,56,0,84,143,112,0,0,138,25,146,0,0,134,144,0,0,0,0,0,0,0,0,0,0,57,0,85,142,0,0,0,0,0,0,138,138,0,0,0,141,113,0,0,138,0,0,0,0,0,0,0,140,0,0,0,138,138,0,0,0,140,0,0,0,0,0,0,0,138,0,0,113,141,0,0,0,138,138,0,0,0,0,0,0,142,85,0,57,0,0,0,0,0,0,0,0,0,0,144,134,0,0,146,25,138,0,0,112,143,84,0,56,0,0,147,24,148,0,150,138],#[152,166,0,164,26,162,0,0,58,0,86,160,114,0,0,152,31,158,0,0,0,0,0,0,0,0,0,0,0,0,0,0,61,0,91,156,0,0,0,0,0,0,152,152,0,0,0,154,117,0,0,152,0,0,0,0,0,0,0,152,0,0,0,140,140,0,0,0,152,0,0,0,0,0,0,0,152,0,0,117,154,0,0,0,152,152,0,0,0,0,0,0,156,91,0,61,0,0,0,0,0,0,0,0,0,0,0,0,0,0,158,31,152,0,0,114,160,86,0,58,0,0,162,26,164,0,166,152],#[170,180,0,178,32,176,0,0,62,0,92,174,118,0,0,170,37,172,0,0,0,0,0,0,0,0,0,0,0,0,0,0,67,0,99,170,0,0,0,0,0,0,170,170,0,0,0,161,123,0,0,170,0,0,0,0,0,0,0,156,0,0,0,142,142,0,0,0,156,0,0,0,0,0,0,0,170,0,0,123,161,0,0,0,170,170,0,0,0,0,0,0,170,99,0,67,0,0,0,0,0,0,0,0,0,0,0,0,0,0,172,37,170,0,0,118,174,92,0,62,0,0,176,32,178,0,180,170],#[182,188,0,186,34,184,0,0,64,0,96,177,120,0,130,182,39,182,0,0,0,0,0,0,0,0,0,0,0,0,0,169,71,0,101,172,0,0,0,0,0,0,182,182,0,0,0,163,125,0,0,182,0,0,0,0,0,0,0,158,0,0,0,146,146,0,0,0,158,0,0,0,0,0,0,0,182,0,0,125,163,0,0,0,182,182,0,0,0,0,0,0,172,101,0,71,169,0,0,0,0,0,0,0,0,0,0,0,0,0,182,39,182,130,0,120,177,96,0,64,0,0,184,34,186,0,188,182],#[190,192,4,190,40,187,0,0,72,0,102,179,126,0,0,190,41,186,0,0,0,0,0,0,0,0,0,0,0,0,0,0,73,0,103,178,0,0,0,0,136,0,190,190,0,0,0,165,127,0,0,190,0,0,0,0,0,0,0,164,0,0,0,148,148,0,0,0,164,0,0,0,0,0,0,0,190,0,0,127,165,0,0,0,190,190,0,136,0,0,0,0,178,103,0,73,0,0,0,0,0,0,0,0,0,0,0,0,0,0,186,41,190,0,0,126,179,102,0,72,0,0,187,40,190,4,192,190],#[194,194,0,192,42,189,0,0,74,0,104,181,128,0,132,194,43,188,0,0,0,0,0,0,0,0,0,0,0,0,0,0,75,0,105,180,0,0,0,0,0,0,194,194,0,0,0,167,129,0,133,194,0,0,0,0,0,0,0,166,0,0,0,150,150,0,0,0,166,0,0,0,0,0,0,0,194,133,0,129,167,0,0,0,194,194,0,0,0,0,0,0,180,105,0,75,0,0,0,0,0,0,0,0,0,0,0,0,0,0,188,43,194,132,0,128,181,104,0,74,0,0,189,42,192,0,194,194]]
private def tag1 (i : Nat) (w : LocalSix) := ((map1[i]?).getD #[])[w.toNat]?.getD 0
private def pass1 (i : Nat) := (genLocal (state1 i)).all (fun w =>
    let t := tag1 i w
    decide (t/2 < 98) && (permWord (axisOf t) majGoal == majGoal) &&
      embeds (axisOf t) (w::state1 i) (state2 (t/2)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem pass1_0 : pass1 0=true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem pass1_1 : pass1 1=true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem pass1_2 : pass1 2=true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem pass1_3 : pass1 3=true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem pass1_4 : pass1 4=true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem pass1_5 : pass1 5=true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem pass1_6 : pass1 6=true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem pass1_7 : pass1 7=true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem pass1_8 : pass1 8=true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem pass1_9 : pass1 9=true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem pass1_10 : pass1 10=true := by decide +kernel
private theorem selected1 : ∀ i : Nat, i < 11 → pass1 i=true
  | 0,_ => pass1_0
  | 1,_ => pass1_1
  | 2,_ => pass1_2
  | 3,_ => pass1_3
  | 4,_ => pass1_4
  | 5,_ => pass1_5
  | 6,_ => pass1_6
  | 7,_ => pass1_7
  | 8,_ => pass1_8
  | 9,_ => pass1_9
  | 10,_ => pass1_10
  | i+11, ht => by omega
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem old1 : ∀ i : Fin 11, !(localBag (state1 i.val)).contains majGoal = true := by decide +kernel
private theorem stage1 (i : Nat) (hi : i < 11) : localMiss majGoal 3 (state1 i)=true := by
  change (_ && _)=true
  rw [Bool.and_eq_true]
  refine ⟨old1 ⟨i,hi⟩,List.all_eq_true.mpr ?_⟩
  intro w hw
  have v := List.all_eq_true.mp (selected1 i hi) w hw
  simp only [Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq] at v
  exact pullMiss v.1.2 2 v.2 (stage2 _ v.1.1)
private def map0 : Array (Array Nat) := #[#[0,20,0,18,2,17,0,0,4,0,6,15,8,0,0,0,3,16,0,0,0,0,0,0,0,0,0,0,0,0,0,0,5,0,7,14,0,0,0,0,0,0,0,0,0,0,0,13,9,0,0,0,0,0,0,0,0,0,0,12,0,0,0,10,10,0,0,0,12,0,0,0,0,0,0,0,0,0,0,9,13,0,0,0,0,0,0,0,0,0,0,0,14,7,0,5,0,0,0,0,0,0,0,0,0,0,0,0,0,0,16,3,0,0,0,8,15,6,0,4,0,0,17,2,18,0,20,0]]
private def tag0 (i : Nat) (w : LocalSix) := ((map0[i]?).getD #[])[w.toNat]?.getD 0
private def pass0 (i : Nat) := (genLocal (state0 i)).all (fun w =>
    let t := tag0 i w
    decide (t/2 < 11) && (permWord (axisOf t) majGoal == majGoal) &&
      embeds (axisOf t) (w::state0 i) (state1 (t/2)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem pass0_0 : pass0 0=true := by decide +kernel
private theorem selected0 : ∀ i : Nat, i < 1 → pass0 i=true
  | 0,_ => pass0_0
  | i+1, ht => by omega
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem old0 : ∀ i : Fin 1, !(localBag (state0 i.val)).contains majGoal = true := by decide +kernel
private theorem stage0 (i : Nat) (hi : i < 1) : localMiss majGoal 4 (state0 i)=true := by
  change (_ && _)=true
  rw [Bool.and_eq_true]
  refine ⟨old0 ⟨i,hi⟩,List.all_eq_true.mpr ?_⟩
  intro w hw
  have v := List.all_eq_true.mp (selected0 i hi) w hw
  simp only [Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq] at v
  exact pullMiss v.1.2 3 v.2 (stage1 _ v.1.1)
private theorem local_miss_three : localMiss majGoal 4 majRoots=true := stage0 0 (by decide)
private theorem local_now {M n B} (h : localMiss M n B=true) : M ∉ localBag B := by
  cases n with
  | zero => simpa only [localMiss,Bool.not_eq_true',List.contains_eq_mem,decide_eq_false_iff_not] using h
  | succ n =>
    simp only [localMiss,Bool.and_eq_true] at h
    simpa only [Bool.not_eq_true',List.contains_eq_mem,decide_eq_false_iff_not] using h.1
theorem pattern_price {p bank} (reach : Reach true (majRoots.map localFun) p bank)
    (ok : Available true bank (localFun majGoal)) : 5 ≤ p := by
  by_contra small
  have le : p ≤ 4 := by omega
  have start : localMiss majGoal (p+(4-p)) ((majRoots.map localFun).map localWord)=true := by
    rw [show p+(4-p)=4 by omega]
    change localMiss majGoal 4 [localWord (localFun 43),localWord (localFun 42),localWord (localFun 76),localWord (localFun 112)] = true
    simpa only [majRoots,local_back] using local_miss_three
  have no := local_now (local_prefix reach _ _ start)
  have yes := local_available ok
  rw [local_back] at yes
  exact no yes


end PatternFive

namespace PatternFour
abbrev LocalSix := BitVec 6
private def localFun (x : LocalSix) : Wire (Fin 6) := fun i => x.getLsbD i.val
private def localWord (f : Wire (Fin 6)) : LocalSix :=
  (BitVec.ofBoolListLE (List.ofFn f)).cast List.length_ofFn
private theorem local_read (f : Wire (Fin 6)) (i : Fin 6) :
    (localWord f).getLsbD i.val = f i := by
  simp only [localWord,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [i.isLt]
private theorem local_ext {a b : LocalSix} (eq : ∀ i : Fin 6, localFun a i = localFun b i) : a=b :=
  BitVec.eq_of_getLsbD_eq fun j h => eq ⟨j,h⟩
private theorem local_back (x : LocalSix) : localWord (localFun x)=x := by
  apply local_ext
  intro i
  exact local_read _ _
private theorem local_inv (a : Wire (Fin 6)) : localWord (inv a) = ~~~localWord a := by
  apply local_ext
  intro i
  change (localWord (inv a)).getLsbD i.val = (~~~localWord a).getLsbD i.val
  rw [local_read, BitVec.getLsbD_not, local_read] <;>
    simp [inv, i.isLt]
private theorem local_combine (op : Bool) (a b : Wire (Fin 6)) :
    localWord (combine op a b) = if op then localWord a ||| localWord b else localWord a &&& localWord b := by
  cases op <;> apply local_ext <;> intro i
  · change (localWord (combine false a b)).getLsbD i.val = (localWord a &&& localWord b).getLsbD i.val
    rw [local_read, BitVec.getLsbD_and, local_read, local_read] <;> rfl
  · change (localWord (combine true a b)).getLsbD i.val = (localWord a ||| localWord b).getLsbD i.val
    rw [local_read, BitVec.getLsbD_or, local_read, local_read] <;> rfl
private def localBag (B : List LocalSix) := 0 :: 63 :: (B ++ B.map (fun a => ~~~a))
private theorem local_available {bank v} (ha : Available true bank v) :
    localWord v ∈ localBag (bank.map localWord) := by
  simp only [localBag,List.mem_cons,List.mem_append,List.mem_map]
  rcases ha with hv | ⟨b,rfl⟩ | ⟨_,hn⟩
  · exact Or.inr (Or.inr (Or.inl ⟨_,hv,rfl⟩))
  · cases b
    · exact Or.inl (by decide +kernel)
    · exact Or.inr (Or.inl (by decide +kernel))
  · right; right; right
    exact ⟨_,⟨_,hn,rfl⟩,by rw [local_inv]; simp⟩
private def genLocal (B : List LocalSix) :=
  ((localBag B).flatMap fun a => (localBag B).flatMap fun b => [a &&& b, a ||| b]).eraseDups
private theorem local_next {bank a b} (op : Bool) (ha : Available true bank a) (hb : Available true bank b) :
    localWord (combine op a b) ∈ genLocal (bank.map localWord) := by
  simp only [genLocal,List.mem_eraseDups,List.mem_flatMap]
  refine ⟨_,local_available ha,_,local_available hb,?_⟩
  cases op <;> simp [local_combine]
private def localMiss (M : LocalSix) : Nat → List LocalSix → Bool
  | 0,B => !(localBag B).contains M
  | n+1,B => !(localBag B).contains M && (genLocal B).all (fun w => localMiss M n (w::B))
private theorem local_prefix {roots p bank} (h : Reach true roots p bank) (M : LocalSix) :
    ∀ d, localMiss M (p+d) (roots.map localWord) = true → localMiss M d (bank.map localWord) = true := by
  induction h using Reach.ind with
  | start => intro d hd; simpa only [Nat.zero_add] using hd
  | two op h ha hb ih =>
    intro d hd
    have old := ih (d+1) (by simpa only [Nat.succ_add,Nat.add_succ] using hd)
    simp only [localMiss,Bool.and_eq_true,List.all_eq_true] at old
    exact old.2 _ (local_next op ha hb)
private def missesPair (M a b : LocalSix) :=
  decide (M ≠ (a &&& b) ∧ M ≠ ~~~(a &&& b) ∧ M ≠ (a ||| b) ∧ M ≠ ~~~(a ||| b))
private def fastLast (M : LocalSix) (B : List LocalSix) :=
  !(localBag B).contains M && (localBag B).all (fun a => (localBag B).all (missesPair M a))
private theorem fastLast_sound {M B} (h : fastLast M B=true) : localMiss M 1 B=true := by
  simp only [fastLast,Bool.and_eq_true,List.all_eq_true,missesPair,decide_eq_true_eq] at h
  change (!(localBag B).contains M && (genLocal B).all (fun w => !(localBag (w::B)).contains M))=true
  rw [Bool.and_eq_true]
  refine ⟨h.1,List.all_eq_true.mpr ?_⟩
  intro w hw
  have grow : M ∈ localBag (w::B) → M=w ∨ M = ~~~w ∨ M ∈ localBag B := by
    simp only [localBag,List.map_cons,List.mem_cons,List.mem_append]
    tauto
  have outside : M ∉ localBag B := by simpa using h.1
  have absent : M ∉ localBag (w::B) := by
    intro hm
    have yes := grow hm
    simp only [genLocal,List.mem_eraseDups,List.mem_flatMap,List.mem_cons,List.not_mem_nil,or_false] at hw
    obtain ⟨a,ha,b,hb,eq⟩ := hw
    have ne := h.2 a ha b hb
    rcases eq with rfl | rfl
    · exact yes.elim ne.1 (fun x => x.elim ne.2.1 outside)
    · exact yes.elim ne.2.2.1 (fun x => x.elim ne.2.2.2 outside)
  simpa using absent
private def fastTwo (M : LocalSix) (B : List LocalSix) :=
  !(localBag B).contains M && (genLocal B).all (fun w => fastLast M (w::B))
private theorem fastTwo_sound {M B} (h : fastTwo M B=true) : localMiss M 2 B=true := by
  simp only [fastTwo,Bool.and_eq_true,List.all_eq_true] at h
  change (!(localBag B).contains M && (genLocal B).all (fun w => localMiss M 1 (w::B)))=true
  rw [Bool.and_eq_true]
  exact ⟨h.1,List.all_eq_true.mpr (fun w hw => fastLast_sound (h.2 w hw))⟩

private def majRoots : List LocalSix := [21,5,38,56]
private def majGoal : LocalSix := 11
private def permWord (p : Fin 6 → Fin 6) (w : LocalSix) := localWord fun i => localFun w (p i)
private theorem perm_not (p) (w) : permWord p (~~~w) = ~~~(permWord p w) := by
  apply local_ext
  intro i
  change (localWord _).getLsbD i.val = (~~~localWord _).getLsbD i.val
  rw [local_read, BitVec.getLsbD_not,local_read] <;>
    simp [localFun, (p i).isLt, i.isLt]
private theorem perm_and (p) (a b) : permWord p (a &&& b) = permWord p a &&& permWord p b := by
  apply local_ext
  intro i
  change (localWord _).getLsbD i.val = (localWord _ &&& localWord _).getLsbD i.val
  rw [local_read,BitVec.getLsbD_and,local_read,local_read] <;>
    simp only [localFun,BitVec.getLsbD_and]
private theorem perm_or (p) (a b) : permWord p (a ||| b) = permWord p a ||| permWord p b := by
  apply local_ext
  intro i
  change (localWord _).getLsbD i.val = (localWord _ ||| localWord _).getLsbD i.val
  rw [local_read,BitVec.getLsbD_or,local_read,local_read] <;>
    simp only [localFun,BitVec.getLsbD_or]
private def embeds (p : Fin 6 → Fin 6) (a b : List LocalSix) := (localBag a).all fun w => (localBag b).contains (permWord p w)
private theorem emb_ok (p) (a b) : embeds p a b = true ↔ ∀ w ∈ localBag a, permWord p w ∈ localBag b := by
  simp only [embeds,List.all_eq_true,List.contains_eq_mem,decide_eq_true_eq]
private theorem bag_cons (x w : LocalSix) (B : List LocalSix) :
    x ∈ localBag (w::B) ↔ x=w ∨ x = ~~~w ∨ x ∈ localBag B := by
  simp only [localBag,List.map_cons,List.mem_cons,List.mem_append]
  tauto
private theorem emb_cons {p a b} (h : embeds p a b=true) (w) :
    embeds p (w::a) (permWord p w::b)=true := by
  apply (emb_ok _ _ _).mpr
  intro x hx
  apply (bag_cons _ _ _).mpr
  rcases (bag_cons _ _ _).mp hx with rfl | rfl | old
  · exact Or.inl rfl
  · exact Or.inr (Or.inl (perm_not _ _))
  · exact Or.inr (Or.inr ((emb_ok _ _ _).mp h x old))
private theorem emb_move {p a b w} (h : embeds p a b=true) (mw : w ∈ genLocal a) :
    permWord p w ∈ genLocal b := by
  simp only [genLocal,List.mem_eraseDups,List.mem_flatMap,List.mem_cons,List.not_mem_nil,or_false] at mw ⊢
  obtain ⟨x,hx,y,hy,hw⟩ := mw
  refine ⟨_,(emb_ok _ _ _).mp h x hx,_,(emb_ok _ _ _).mp h y hy,?_⟩
  rcases hw with rfl | rfl
  · exact Or.inl (perm_and _ _ _)
  · exact Or.inr (perm_or _ _ _)
private theorem pullMiss {p M} (fixed : permWord p M=M) (n : Nat) {a b}
    (cov : embeds p a b=true) (no : localMiss M n b=true) : localMiss M n a=true := by
  induction n generalizing a b with
  | zero =>
    simp only [localMiss,Bool.not_eq_true',List.contains_eq_mem,decide_eq_false_iff_not] at no ⊢
    intro hm
    exact no (fixed ▸ (emb_ok _ _ _).mp cov M hm)
  | succ n ih =>
    simp only [localMiss,Bool.and_eq_true,Bool.not_eq_true',List.contains_eq_mem,decide_eq_false_iff_not,List.all_eq_true] at no ⊢
    refine ⟨fun hm => no.1 (fixed ▸ (emb_ok _ _ _).mp cov M hm),?_⟩
    intro w hw
    exact ih (emb_cons cov _) (no.2 _ (emb_move cov hw))

private def axisData : Array Nat := #[181896]
private def axisOf (t : Nat) (j : Fin 6) : Fin 6 := Fin.ofNat 6 ((axisData[t % 1]?.getD 0 >>> (3*j.val)) % 8)
private def state0 (_ : Nat) := majRoots
private def extras1 : Array (List LocalSix) := #[[],[2],[4],[6],[8],[16],[24],[32],[34],[40],[46],[62]]
private def state1 (i : Nat) := (extras1[i]?.getD []) ++ majRoots
private def badData : Array Nat := #[4503599627372544,3072,2560,3840,4785074604081152,0,0,0,2056,3084,2570,9799982325021314831,0,0,0,576469548530665472,4503668346847232,0,0,0,4785147618525184,0,0,0,0,0,0,149533581412352,0,0,0,8796093024256,4503599628419072,0,0,0,4785074605195264,0,0,0,0,0,0,2281736192,0,0,0,134219776,4503668347895824,0,0,0,(word80 [0x0,0xf0f1001100110011]),5787125521171087360,3472275312702652416,1157425104234217472,0,0,0,34816,67553994410557440,22517998136852480,13510798882111488,4503599627372544]
private def badMask (w : LocalSix) := badData[w.toNat]?.getD 0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem badMask_ok : ∀ a v : LocalSix, (badMask a).testBit v.toNat = !(missesPair majGoal a v) := by decide +kernel

private def allowsWord (cover : Nat) (w : LocalSix) := cover.testBit w.toNat
private def paidCell (B : List LocalSix) (cover : Nat) :=
  (!allowsWord cover majGoal) && (localBag B).all (allowsWord cover) &&
  (localBag B).all (fun w => (cover &&& badMask w) == 0) &&
  (genLocal B).all fun w => allowsWord cover w && allowsWord cover (~~~w)
private theorem antiPair : ∀ w : LocalSix, w ≠ majGoal → ~~~w ≠ majGoal →
    ∀ a b : Bool, missesPair majGoal (if a then w else ~~~w) (if b then w else ~~~w)=true := by decide +kernel
private theorem pairRev (a b : LocalSix) : missesPair majGoal a b=missesPair majGoal b a := by
  simp only [missesPair,BitVec.and_comm a b,BitVec.or_comm a b]
private theorem paidCell_sound {B K} (pass : paidCell B K=true) : localMiss majGoal 2 B=true := by
  simp only [paidCell,Bool.and_eq_true,Bool.not_eq_true',List.all_eq_true,beq_iff_eq] at pass
  obtain ⟨⟨⟨off,old⟩,clean⟩,moves⟩ := pass
  have avoid {v} (on : allowsWord K v=true) : v≠majGoal := by
    intro eq
    subst v
    rw [off] at on
    contradiction
  have guard {a v} (ha : a∈localBag B) (hV : allowsWord K v=true) : missesPair majGoal a v=true := by
    have eq := congrArg (fun n : Nat => n.testBit v.toNat) (clean a ha)
    change K.testBit v.toNat=true at hV
    simpa [Nat.testBit_and,hV,badMask_ok] using eq
  have oldNo : !(localBag B).contains majGoal = true := by
    have no : majGoal ∉ localBag B := fun p => avoid (old _ p) rfl
    simpa using no
  apply fastTwo_sound
  simp only [fastTwo,Bool.and_eq_true,List.all_eq_true]
  refine ⟨oldNo,?_⟩
  intro w hw
  have win := moves w hw
  have membership {a} (ha : a∈localBag (w::B)) : allowsWord K a=true := by
    rcases (bag_cons a w B).mp ha with rfl | rfl | original
    · exact win.1
    · exact win.2
    · exact old _ original
  simp only [fastLast,Bool.and_eq_true,List.all_eq_true]
  have no : majGoal ∉ localBag (w::B) := fun hx => avoid (membership hx) rfl
  refine ⟨by simpa using no,?_⟩
  intro a ha b hb
  by_cases origA : a ∈ localBag B
  · exact guard origA (membership hb)
  by_cases origB : b ∈ localBag B
  · rw [pairRev]
    exact guard origB (membership ha)
  have da := (bag_cons a w B).mp ha
  have db := (bag_cons b w B).mp hb
  have core := antiPair w (avoid win.1) (avoid win.2)
  rcases da with rfl | rfl | bad
  · rcases db with rfl | rfl | bad
    · exact core true true
    · exact core true false
    · contradiction
  · rcases db with rfl | rfl | bad
    · exact core false true
    · exact core false false
    · contradiction
  · contradiction

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end0 : localMiss majGoal 2 (state1 0)=true := by apply paidCell_sound (K:=(word80 [0x0,0xef80c5c5a3a301f7])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end1 : localMiss majGoal 2 (state1 1)=true := by apply paidCell_sound (K:=(word80 [0x0,0xef80c5d5aba301f7])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end2 : localMiss majGoal 2 (state1 2)=true := by apply paidCell_sound (K:=(word80 [0x0,0xff80c5c5a3a301ff])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end3 : localMiss majGoal 2 (state1 3)=true := by apply paidCell_sound (K:=(word80 [0x0,0xef80c5c5a3a301f7])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end4 : localMiss majGoal 2 (state1 4)=true := by apply paidCell_sound (K:=(word80 [0x0,0xef85c5c5a3a3a1f7])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end5 : localMiss majGoal 2 (state1 5)=true := by apply paidCell_sound (K:=(word80 [0x0,0xefc0c5c5a3a303f7])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end6 : localMiss majGoal 2 (state1 6)=true := by apply paidCell_sound (K:=(word80 [0x0,0xef80c5c5a3a301f7])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end7 : localMiss majGoal 2 (state1 7)=true := by apply paidCell_sound (K:=(word80 [0x0,0xefa0c5e5a7a305f7])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end8 : localMiss majGoal 2 (state1 8)=true := by apply paidCell_sound (K:=(word80 [0x0,0xef80c5c5a3a301f7])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end9 : localMiss majGoal 2 (state1 9)=true := by apply paidCell_sound (K:=(word80 [0x0,0xef80e5c5a3a701f7])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end10 : localMiss majGoal 2 (state1 10)=true := by apply paidCell_sound (K:=(word80 [0x0,0xef80c5c5a3a301f7])); decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem end11 : localMiss majGoal 2 (state1 11)=true := by apply paidCell_sound (K:=(word80 [0x0,0xef80cdc5a3b301f7])); decide +kernel
private theorem stage1 : ∀ i : Nat, i < 12 → localMiss majGoal 2 (state1 i)=true
  | 0,_ => end0
  | 1,_ => end1
  | 2,_ => end2
  | 3,_ => end3
  | 4,_ => end4
  | 5,_ => end5
  | 6,_ => end6
  | 7,_ => end7
  | 8,_ => end8
  | 9,_ => end9
  | 10,_ => end10
  | 11,_ => end11
  | i+12,ht => by omega
private def map0 : Array (Array Nat) := #[#[0,11,1,0,2,0,3,0,4,0,0,0,0,0,0,0,5,10,0,0,0,0,0,9,6,0,0,0,0,8,0,7,7,0,8,0,0,0,0,6,9,0,0,0,0,0,10,5,0,0,0,0,0,0,0,4,0,3,0,2,0,1,11,0]]
private def tag0 (i : Nat) (w : LocalSix) := ((map0[i]?).getD #[])[w.toNat]?.getD 0
private def pass0 (i : Nat) := (genLocal (state0 i)).all (fun w =>
    let t := tag0 i w
    decide (t/1 < 12) && (permWord (axisOf t) majGoal == majGoal) &&
      embeds (axisOf t) (w::state0 i) (state1 (t/1)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem pass0_0 : pass0 0=true := by decide +kernel
private theorem selected0 : ∀ i : Nat, i < 1 → pass0 i=true
  | 0,_ => pass0_0
  | i+1, ht => by omega
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem old0 : ∀ i : Fin 1, !(localBag (state0 i.val)).contains majGoal = true := by decide +kernel
private theorem stage0 (i : Nat) (hi : i < 1) : localMiss majGoal 3 (state0 i)=true := by
  change (_ && _)=true
  rw [Bool.and_eq_true]
  refine ⟨old0 ⟨i,hi⟩,List.all_eq_true.mpr ?_⟩
  intro w hw
  have v := List.all_eq_true.mp (selected0 i hi) w hw
  simp only [Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq] at v
  exact pullMiss v.1.2 2 v.2 (stage1 _ v.1.1)
private theorem local_miss_three : localMiss majGoal 3 majRoots=true := stage0 0 (by decide)
private theorem local_now {M n B} (h : localMiss M n B=true) : M ∉ localBag B := by
  cases n with
  | zero => simpa only [localMiss,Bool.not_eq_true',List.contains_eq_mem,decide_eq_false_iff_not] using h
  | succ n =>
    simp only [localMiss,Bool.and_eq_true] at h
    simpa only [Bool.not_eq_true',List.contains_eq_mem,decide_eq_false_iff_not] using h.1
theorem pattern_price {p bank} (reach : Reach true (majRoots.map localFun) p bank)
    (ok : Available true bank (localFun majGoal)) : 4 ≤ p := by
  by_contra small
  have le : p ≤ 3 := by omega
  have start : localMiss majGoal (p+(3-p)) ((majRoots.map localFun).map localWord)=true := by
    rw [show p+(3-p)=3 by omega]
    change localMiss majGoal 3 [localWord (localFun 21),localWord (localFun 5),localWord (localFun 38),localWord (localFun 56)] = true
    simpa only [majRoots,local_back] using local_miss_three
  have no := local_now (local_prefix reach _ _ start)
  have yes := local_available ok
  rw [local_back] at yes
  exact no yes


end PatternFour

namespace FourColumnFace

private def value {n : Nat} (w : BitVec n) : Wire (Fin n) := fun i => w.getLsbD i.val
private theorem value_zero {n : Nat} : value (0 : BitVec n) = fun _ => false := by
  funext i
  simp [value]
private theorem value_one {n : Nat} : value (BitVec.allOnes n) = fun _ => true := by
  funext i
  simp [value,i.isLt]
private theorem value_inv {n : Nat} (w : BitVec n) : value (~~~w) = inv (value w) := by
  funext i
  simp [value,inv,i.isLt]
private def sample {n : Nat} (code : Nat) (i : Fin n) : Row :=
  Fin.ofNat 512 ((code >>> (8*i.val)) % 256)
private theorem value_sample {n : Nat} (r : Fin n → Row) (w : Sig) :
    restrictRows r (observe w) = value (ofRows r w) := by
  funext i
  exact (ofRows_bit r w i).symm
private def supplyWords {n : Nat} (roots : List (BitVec n)) :=
  0 :: BitVec.allOnes n :: (roots ++ roots.map (fun w => ~~~w))
private theorem supplied {n : Nat} {roots : List (BitVec n)} {w}
    (h : w ∈ supplyWords roots) : Available true (roots.map value) (value w) := by
  simp only [supplyWords,List.mem_cons,List.mem_append,List.mem_map] at h
  rcases h with rfl | rfl | hw | ⟨v,hv,rfl⟩
  · exact Or.inr (Or.inl ⟨_,value_zero⟩)
  · exact Or.inr (Or.inl ⟨_,value_one⟩)
  · exact Or.inl (List.mem_map_of_mem hw)
  · right; right
    refine ⟨rfl,?_⟩
    rw [value_inv,inv_inv']
    exact List.mem_map_of_mem hv
private def constantWeight {n : Nat} (w : BitVec n) :=
  if w = 0 ∨ w=BitVec.allOnes n then 1 else 0
private theorem constantWeight_le {n : Nat} (w : BitVec n) : constantWeight w ≤ cost (value w) := by
  classical
  unfold constantWeight
  split
  next h =>
    have hc : Constant (value w) := by
      rcases h with rfl | rfl
      · exact ⟨_,value_zero⟩
      · exact ⟨_,value_one⟩
    simp only [cost,if_pos hc,Nat.le_refl]
  next => exact Nat.zero_le _
private theorem weights_le {n : Nat} (ws : List Sig) (r : Fin n → Row) :
    ((ws.map (ofRows r)).map constantWeight).sum ≤ mass ((ws.map observe).map (restrictRows r)) := by
  induction ws with
  | nil => simp [mass]
  | cons w ws ih =>
    simp only [List.map_cons,List.sum_cons,mass_cons]
    rw [value_sample]
    exact Nat.add_le_add (constantWeight_le _) ih

private def polarity {n : Nat} (b : Bool) (w : BitVec n) := if b then ~~~w else w
private theorem preserveNonconstant {n : Nat} {w : BitVec n} (h : ¬Constant (value w)) (b : Bool) :
    ¬Constant (value (polarity b w)) := by
  cases b
  · exact h
  · change ¬Constant (value (~~~w))
    rw [value_inv]
    intro bad
    have e := inv_constant bad
    rw [inv_inv'] at e
    exact h e
private theorem preservePrice {n : Nat} {w : BitVec n} {Q : Nat} {roots : List (BitVec n)}
    (base : ∀ q bank, Reach true (roots.map value) q bank → Available true bank (value w) → Q ≤ q) (b : Bool) :
    ∀ q bank, Reach true (roots.map value) q bank → Available true bank (value (polarity b w)) → Q ≤ q := by
  intro q bank path hits
  apply base q bank path
  cases b
  · exact hits
  · change Available true bank (value (~~~w)) at hits
    rw [value_inv] at hits
    have reuse := avail_inv rfl hits
    rw [inv_inv'] at reuse
    exact reuse
def works {n : Nat} (roots : List (BitVec n)) (G : BitVec n) (Q : Nat)
    (b : Bool) (T : Sig) (k : Nat) (ws : List Sig) (code : Nat) :=
  let r : Fin n → Row := sample code
  let words := ws.map (ofRows r)
  decide ws.Nodup && (ofRows r T == polarity b G) &&
    words.all (fun w => (supplyWords roots).contains w) && decide (k < Q + (words.map constantWeight).sum)
theorem physical {n : Nat} {roots : List (BitVec n)} {G : BitVec n} {Q : Nat}
    {b T k ws code} (nc : ¬Constant (value G))
    (base : ∀ q bank, Reach true (roots.map value) q bank → Available true bank (value G) → Q ≤ q)
    (ok : works roots G Q b T k ws code=true) : Impossible true T k ws.toFinset := by
  simp only [works,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq,List.all_eq_true,List.contains_eq_mem] at ok
  let r : Fin n → Row := sample code
  have goal : restrictRows r (observe T) = value (polarity b G) := (value_sample r T).trans (congrArg value ok.1.1.2)
  have nonconst : ¬Constant (restrictRows r (observe T)) := by
    rw [goal]
    exact preserveNonconstant nc b
  have stock : supply true (roots.map value) ((ws.map observe).map (restrictRows r)) := by
    intro f mem
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp mem
    obtain ⟨w,hw,rfl⟩ := List.mem_map.mp ha
    rw [value_sample]
    apply supplied
    simpa only [decide_eq_true_eq] using ok.1.2 _ (List.mem_map_of_mem hw)
  intro p hp live
  have path := list_run live ws ok.1.1.1 rfl
  have low : ∀ q bank, Reach true (roots.map value) q bank → Available true bank (restrictRows r (observe T)) → Q ≤ q := by
    rw [goal]
    exact preservePrice base b
  have h := projected_bound r path nonconst Reach.start stock low
  have wgt := weights_le ws r
  have need := ok.2
  change k < Q + ((ws.map (ofRows r)).map constantWeight).sum at need
  omega

private def pricedFace : Nat → Sig → Nat → List Sig → Nat → Bool
  | 0 => works ([25, 42, 52] : List (BitVec 6)) 56 4 false
  | 1 => works ([43, 42, 76, 112] : List (BitVec 7)) 22 5 false
  | 2 => works ([43, 42, 76, 112] : List (BitVec 7)) 22 5 true
  | 3 => works ([21, 5, 38, 56] : List (BitVec 6)) 11 4 false
  | 4 => works ([21, 5, 38, 56] : List (BitVec 6)) 11 4 true
  | _ => fun _ _ _ _ => false
theorem pricedFace_sound {tag T k ws code} (ok : pricedFace tag T k ws code = true) :
    Impossible true T k ws.toFinset := by
  by_cases ht : tag = 0
  · subst tag
    change works ([25, 42, 52] : List (BitVec 6)) 56 4 false T k ws code = true at ok
    apply physical (ok:=ok)
    · rintro ⟨b,e⟩
      have zero : false=b := congrFun e (0 : Fin 6)
      have one : true=b := congrFun e (3 : Fin 6)
      cases b <;> contradiction
    · intro _ _ r h
      exact PriceThree.majority_six_price r h
  by_cases ht : tag = 1
  · subst tag
    change works ([43, 42, 76, 112] : List (BitVec 7)) 22 5 false T k ws code = true at ok
    apply physical (ok:=ok)
    · rintro ⟨b,e⟩
      have zero : false=b := congrFun e (0 : Fin 7)
      have one : true=b := congrFun e (1 : Fin 7)
      cases b <;> contradiction
    · intro _ _ r h
      exact PatternFive.pattern_price r h
  by_cases ht : tag = 2
  · subst tag
    change works ([43, 42, 76, 112] : List (BitVec 7)) 22 5 true T k ws code = true at ok
    apply physical (ok:=ok)
    · rintro ⟨b,e⟩
      have zero : false=b := congrFun e (0 : Fin 7)
      have one : true=b := congrFun e (1 : Fin 7)
      cases b <;> contradiction
    · intro _ _ r h
      exact PatternFive.pattern_price r h
  by_cases ht : tag = 3
  · subst tag
    change works ([21, 5, 38, 56] : List (BitVec 6)) 11 4 false T k ws code = true at ok
    apply physical (ok:=ok)
    · rintro ⟨b,e⟩
      have zero : false=b := congrFun e (2 : Fin 6)
      have one : true=b := congrFun e (0 : Fin 6)
      cases b <;> contradiction
    · intro _ _ r h
      exact PatternFour.pattern_price r h
  by_cases ht : tag = 4
  · subst tag
    change works ([21, 5, 38, 56] : List (BitVec 6)) 11 4 true T k ws code = true at ok
    apply physical (ok:=ok)
    · rintro ⟨b,e⟩
      have zero : false=b := congrFun e (2 : Fin 6)
      have one : true=b := congrFun e (0 : Fin 6)
      cases b <;> contradiction
    · intro _ _ r h
      exact PatternFour.pattern_price r h
  have far : 5 ≤ tag := by omega
  obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le far
  rw [Nat.add_comm 5 j] at ok
  change false = true at ok
  contradiction
private def fetchPrefix (codes : List Nat) : List Sig :=
  codes.foldl (fun bank c => bank ++ [bin (c/1024) (bank.getD (c%32) zero) (bank.getD (c/32%32) zero)])
    ([0,2,3,4,5,6,7].map (fun i => inputs.getD i zero))
private def takeLive (mask : Nat) (bank : List Sig) : List Sig :=
  ((bank.zipIdx).filter (fun pair => mask.testBit pair.2)).map Prod.fst
private abbrev Ticket := Nat × Nat × Nat × Nat × List Nat
private def ticketOK (t : Ticket) : Bool :=
  pricedFace t.1 (chartGoal 253) t.2.1 (takeLive t.2.2.1 (fetchPrefix t.2.2.2.2)) t.2.2.2.1
theorem ticket_sound {t : Ticket} (ok : ticketOK t = true) :
    Impossible true (chartGoal 253) t.2.1 (takeLive t.2.2.1 (fetchPrefix t.2.2.2.2)).toFinset :=
  pricedFace_sound ok
private def ticketPage0 : List Ticket := [
  (0,6,11028,211198591467537,[1056, 1185, 1218, 1221, 1344, 327, 1411]),
  (1,7,5976,9008440637131072,[1056, 1184, 1217, 1186, 1250, 3428]),
  (2,7,7768,5990162166267969,[1056, 1184, 1089, 1186, 3300, 3334]),
  (3,6,15882,5570929102160,[1056, 1184, 1186, 1250, 1220, 1284, 1286]),
  (4,6,12050,71575924129800,[1056, 1184, 1218, 1282, 1221, 359, 1411])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ticketPage0_ok : ticketPage0.all ticketOK = true := by decide +kernel
def acceptedTickets : Prop := [ticketPage0].all (fun page => page.all ticketOK) = true
theorem acceptedTickets_ok : acceptedTickets := by
  unfold acceptedTickets
  simp only [List.all_cons, List.all_nil, ticketPage0_ok, Bool.and_self]
end FourColumnFace
end PEqualNP.Outside.L_meta_52322
theorem PEqualNP.Outside.L_meta_52322 : PEqualNP.Outside.L_meta_52322.FourColumnFace.acceptedTickets :=
  PEqualNP.Outside.L_meta_52322.FourColumnFace.acceptedTickets_ok

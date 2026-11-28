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
  (x 0 &&& x 3) ||| (x 1 &&& x 4) ||| (x 2 &&& x 4) ||| (x 0 &&& x 5) ||| (x 1 &&& x 5) ||| (x 3 &&& x 5) ||| (x 0 &&& x 6) ||| (x 2 &&& x 6) ||| (x 3 &&& x 6) ||| (x 4 &&& x 6) ||| (x 5 &&& x 6) ||| (x 0 &&& x 7) ||| (x 1 &&& x 7) ||| (x 2 &&& x 7) ||| (x 3 &&& x 7) ||| (x 4 &&& x 7) ||| (x 5 &&& x 7) ||| (x 6 &&& x 7)
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

def closeChild (u : Bool) (pools : List BoundPool) (links : Nat → List Sig → List (List Sig)) (k : Nat)
    (rest : List Sig) (op : Choice) :=
  let ws := choiceVal op::rest
  (links (keySet ws) ws).any (sameWords ws) || pools.any (fun p => scalarPoolCut u p k rest op)

theorem closeChild_sound {u raw T pools links k rest op}
    (pValid : ∀ p ∈ pools, ValidPool u raw T p)
    (lValid : ∀ tag query xs, xs ∈ links tag query → Impossible u T k (List.toFinset xs))
    (nd : (choiceVal op :: rest).Nodup)
    (h : closeChild u pools links k rest op = true) :
    Impossible u T k (choiceVal op :: rest).toFinset := by
  simp only [closeChild,Bool.or_eq_true,List.any_eq_true] at h
  rcases h with ⟨xs,hx,ok⟩ | ⟨p,hp,ok⟩
  · rw [sameWords_sound ok]
    exact lValid _ _ _ hx
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

abbrev NodeContext := Nat × Nat × List Decor × CovPair × List BoundPool × (Nat → List Sig → List (List Sig))
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
    (lv : ∀ tag query xs, xs ∈ links tag query → Impossible u T (cap-1) (List.toFinset xs))
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
    (lv : ∀ tag query xs, xs ∈ links tag query → Impossible u T (cap-1) (List.toFinset xs))
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

def cubRows (word : Nat) : SixRows := ⟨Fin.ofNat 512 ((word >>> 0) % 256),Fin.ofNat 512 ((word >>> 8) % 256),Fin.ofNat 512 ((word >>> 16) % 256),Fin.ofNat 512 ((word >>> 24) % 256),Fin.ofNat 512 ((word >>> 32) % 256),Fin.ofNat 512 ((word >>> 40) % 256)⟩

def inlineSix (T : Sig) (k : Nat) (ws : List Sig) (word : Nat) : Bool :=
  let S := ws.toFinset
  let r := cubRows word
  decide (S.card = k+1) && decide ((∑ v ∈ S, sixCost (readSix r v)) < sixCost (readSix r T))

theorem inlineSix_sound {T k ws word} (ok : inlineSix T k ws word=true) (u : Bool) :
    Impossible u T k ws.toFinset := by
  simp only [inlineSix,Bool.and_eq_true,decide_eq_true_eq] at ok
  exact six_cut (cubRows word) ok.1 ok.2

def closeSix (T : Sig) (k : Nat) (marks : List Nat) (ws : List Sig) : List (List Sig) :=
  if marks.any (inlineSix T k ws) then [ws] else []

theorem closeSix_sound {T k marks ws xs} (h : xs ∈ closeSix T k marks ws) (u : Bool) :
    Impossible u T k xs.toFinset := by
  unfold closeSix at h
  split at h
  next e =>
    obtain ⟨word,_,hw⟩ := List.any_eq_true.mp e
    have same : xs=ws := by simpa only [List.mem_singleton] using h
    subst xs
    exact inlineSix_sound hw u
  next => simp at h

private def sixWordsP0 : Array Nat := #[88254062072085,76437625258176,145756158756117,211450904773909,154258250956992,40871513556237,180750011891904,71778567980301,211726856422677,75111463390236,105863428449324,105833363219493,145756159216668,88254064111668,176508124275756,150089780762649,106378832126112,158898759938100,193995892359360,14482833409317,71812928506908,89683505725632,79990553053320,72293971657089,167504131424448,211519625527456,211726856437840,142663785382209,40737849484332,142526344331553,176094196564104,79445084936217,211450904739984,71881649559608,48538033619136,211726858462260,48434551750848,110140745859144,211795577144613,75111462929685,149843024576704,71812930085940,141875672023176,76025302354988,211726856883228,211450906813492,211692496356621,150222926780472,123386626326600,76025302106208,22557243736208,211450905234460,40871516995776,105863428186152,211399364345988,83618919694401,14414112637008,36837959671968,79509509440789,75111462895760,83683345203344,145255996407888,176111443804296,211692496109640]
private def sixWordsP1 : Array Nat := #[211795574851593,145962316138505,180479428921416,176542484333845,71506927829064,83752065696033,211519625234472,149641358311616,79578230162725,176748645851232,211416543993889,176748641716233,61783910979609,150222925725985,14590091985988,14620274197572,150154205267221,105742699610184,83618919949349,211795576883240,89271183611960,27767252977856,27797435187648,48705130561665,142116191219768,71610007060616,36563073925256,176508127674689,79336773259569,211416546280741,110175106121808,110110681104520,211519623202825,211692495642657,49083494433089,176508123562049,61680432218304,14590096187552,211386479944748,211662431330344,211399364118537,211675315767305,154052089381008,23300484907104,14383930441872,14414112653456,105833364009009,123356561096769,96997946163489,154120809873697,167366690341153]
private def sixWords : Array (Array Nat) := #[sixWordsP0,sixWordsP1]
private def sixMenuStartsP0 : Array Nat := #[2,32,33,49,65,83,131,177,193,210,242,275,322,354,385,401,417,433,451,499,547,595,643,689,705,721,737,759,868,930,965,1047,1157,1233,1251,1300,1363,1410,1442,1474,1510,1605,1681,1700,1762,1795,1846,1939,1986,2017,2033,2052,2114,2146,2178,2211,2258,2290,2322,2355,2402,2434,2468,2531]
private def sixMenuStartsP1 : Array Nat := #[2579,2626,2659,2705,2721,2737,2754,2786,2817,2834,2865,2881,2897,2913,2929,2945,2962,2994,3025,3042,3075,3123,3169,3186,3217,3234,3266,3298,3329,3347,3394,3426,3457,3474,3507,3553,3570,3602,3634,3666,3698,3730,3761,3780,3844,3910,4004,4068,4130,4162,4198,4291,4338,4371,4419,4466,4498,4533,4609,4628,4691,4738,4769,4786]
private def sixMenuStartsP2 : Array Nat := #[4818,4851,4899,4950,5043,5090,5124,5187,5234,5266,5297,5314,5348,5410,5444,5506,5537,5553,5575,5685,5762,5798,5892,5955,6003,6054,6147,6197,6275,6327,6439,6550,6642,6677,6756,6821,6904,7028,7094,7192,7318,7411,7457,7476,7537,7553,7571,7622,7716,7782,7877,7956,8019,8066,8099,8146,8178,8211,8259,8305,8325,8402,8436,8498]
private def sixMenuStartsP3 : Array Nat := #[8532,8597,8678,8774,8865,8885,8968,9097,9237,9316,9380,9442,9474,9508,9573,9651,9697,9714,9746,9780,9844,9907,9953,9971,10024,10153,10294,10389,10472,10595,10645,10722,10756,10818,10849,10866,10899,10946,10978,11009,11029,11108,11171,11219,11267,11314,11346,11378,11415,11524,11590,11681,11700,11762,11795,11845,11922,11955,12001,12019,12068,12132,12197,12277]
private def sixMenuStartsP4 : Array Nat := #[12355,12403,12456,12583,12693,12771,12818,12851,12900,12964,13031,13142,13236,13300,13363,13410,13444,13507,13554,13585,13605,13683,13730,13763,13812,13874,13907,13954,13987,14034,14067,14113,14131,14178,14209,14225,14241,14258,14291,14339,14386,14419,14465,14481,14498,14530,14562,14594,14628,14689,14707,14754,14785,14801,14818,14851,14899,14948,15012,15076,15138,15173,15250,15284]
private def sixMenuStartsP5 : Array Nat := #[15349,15426,15458,15493,15571,15619,15666,15699,15748,15810,15842,15875,15922,15955,16002,16035,16083,16133,16211,16260,16323,16370,16407,16515,16564,16627,16675,16725,16802,16834,16866,16901,16978,17013,17094,17188,17252,17315,17365,17445,17524,17588,17655,17764,17826,17862,17956,18017,18039,18147,18194,18229,18308,18371,18418,18450,18482,18516,18582,18679,18791,18899,18954,19112]
private def sixMenuStartsP6 : Array Nat := #[19235,19283,19331,19379,19427,19478,19571,19620,19685,19766,19861,19942,20040,20169,20305,20322,20354,20386,20418,20450,20483,20534,20627,20675,20722,20754,20787,20835,20886,20981,21059,21110,21204,21269,21346,21383,21496,21619,21668,21738,21890,21928,22055,22163,22211,22259,22305,22324,22388,22451,22499,22547,22595,22643,22690,22723,22773,22851,22900,22966,23060,23124,23189,23272]
private def sixMenuStartsP7 : Array Nat := #[23395,23442,23475,23523,23570,23602,23638,23732,23796]
private def sixMenuStarts : Array (Array Nat) := #[sixMenuStartsP0,sixMenuStartsP1,sixMenuStartsP2,sixMenuStartsP3,sixMenuStartsP4,sixMenuStartsP5,sixMenuStartsP6,sixMenuStartsP7]
private def sixMenuWordsP0 : Array Nat := #[5,21,25,6,3,4,25,62,25,40,62,8,21,2,7,9,15,0,11,15,9,27,12,28,11,87,5,61,18,30,34,6,30,34,18,30,48,6,30,37,7,10,11,15,36,14,0,0,2,5,10,11,13,17,0,2,13,17,2,3,3,4,14,18]
private def sixMenuWordsP1 : Array Nat := #[36,3,14,18,24,34,36,40,3,4,6,34,36,20,3,25,46,4,18,36,61,25,46,61,1,26,1,5,5,26,3,5,14,18,21,52,3,5,14,26,52,1,6,26,30,37,10,26,10,14,21,3,5,6,14,26,52,10,14,26,10,11,19,71]
private def sixMenuWordsP2 : Array Nat := #[3,24,25,71,3,6,0,11,5,6,0,5,6,5,10,0,2,13,35,5,13,35,0,8,3,8,3,25,85,86,3,5,8,4,10,14,6,47,6,10,14,2,23,12,23,27,5,16,38,5,19,26,4,40,7,68,22,9,64,11,17,29,9,42]
private def sixMenuWordsP3 : Array Nat := #[0,5,9,0,9,15,57,2,9,13,13,99,12,16,5,76,27,0,6,12,0,15,13,27,28,0,5,2,9,12,63,2,22,2,11,2,6,2,16,7,12,9,37,9,9,16,17,88,2,14,16,22,2,5,12,16,17,22,5,12,34,89,12,16]
private def sixMenuWordsP4 : Array Nat := #[66,90,9,12,9,30,10,12,16,20,30,41,2,16,22,16,28,19,63,91,16,43,72,10,16,19,73,5,12,16,30,41,30,6,13,14,34,6,14,34,6,13,46,18,38,6,10,2,9,13,0,9,17,0,2,9,12,13,17,0,9,12,10,14]
private def sixMenuWordsP5 : Array Nat := #[6,10,13,14,18,19,48,18,48,6,37,49,7,11,7,8,10,11,12,17,11,44,95,96,0,7,64,17,2,3,5,10,11,17,45,5,10,11,16,39,32,54,0,5,6,11,13,14,5,6,11,14,6,13,18,0,6,18,0,4,17,24,36,100]
private def sixMenuWordsP6 : Array Nat := #[0,4,24,5,6,10,11,65,4,13,24,0,2,5,11,13,17,33,0,5,8,10,11,13,35,0,1,2,13,17,21,2,13,6,11,13,14,29,6,11,14,29,6,13,14,18,47,4,6,7,10,11,14,15,29,6,10,11,29,6,10,11,14,29]
private def sixMenuWordsP7 : Array Nat := #[53,0,2,4,6,9,17,18,24,0,2,4,9,12,24,6,11,29,10,3,10,17,45,54,47,6,10,38,10,11,13,17,43,69,11,13,17,31,4,6,14,34,36,40,2,3,4,24,36,9,12,23,66,20,23,66,19,20,16,20,92,10,20,42]
private def sixMenuWordsP8 : Array Nat := #[53,16,20,37,6,18,34,56,2,3,6,46,47,25,46,2,3,4,6,9,19,1,3,14,26,1,5,6,14,52,3,5,14,18,26,52,1,3,5,6,14,52,93,0,2,3,5,8,3,4,5,8,10,14,18,26,3,5,8,10,14,18,21,24]
private def sixMenuWordsP9 : Array Nat := #[40,3,4,6,8,26,1,3,6,8,9,12,19,23,6,18,5,67,1,10,14,26,1,9,10,13,14,1,10,14,94,1,3,1,9,3,6,26,37,1,3,8,47,1,3,26,50,10,29,74,0,1,7,10,11,14,15,29,1,3,7,8,10,11]
private def sixMenuWordsP10 : Array Nat := #[14,15,29,0,6,10,15,29,64,3,10,15,29,64,3,6,8,10,11,29,74,97,2,3,98,3,5,10,45,75,3,5,2,3,33,45,33,51,51,4,25,2,3,4,3,25,3,4,39,4,11,13,14,36,4,11,14,36,0,4,15,3,4,15]
private def sixMenuWordsP11 : Array Nat := #[4,15,65,0,4,4,15,3,65,3,4,5,6,10,15,75,3,4,15,53,0,4,5,6,15,36,45,5,7,10,11,5,7,13,35,101,5,13,14,35,102,7,8,5,10,35,77,7,78,79,0,2,3,8,3,4,8,21,3,5,6,8,21,3]
private def sixMenuWordsP12 : Array Nat := #[8,21,24,25,3,6,8,3,4,8,0,1,4,5,10,11,14,29,1,4,7,10,11,14,29,3,4,5,10,103,1,3,8,44,51,4,104,105,3,4,6,8,1,3,4,8,3,4,7,8,42,72,77,1,3,4,7,8,15,2,3,11,31,5]
private def sixMenuWordsP13 : Array Nat := #[11,17,28,14,45,47,14,15,2,3,45,51,2,3,14,0,9,80,0,7,9,11,15,7,11,15,7,15,6,7,15,0,6,7,15,0,46,3,6,47,38,65,3,6,14,28,31,31,33,43,44,7,8,31,22,23,32,37,81,9,17,0,2,9]
private def sixMenuWordsP14 : Array Nat := #[0,12,13,0,12,0,13,17,42,16,0,17,0,6,0,33,13,17,0,2,9,17,55,9,43,84,0,38,59,60,5,17,5,12,22,2,14,22,9,16,17,63,2,16,22,32,2,16,23,32,19,37,10,16,20,41,43,16,19,5,12,30,41,2]
private def sixMenuWordsP15 : Array Nat := #[12,16,17,22,19,22,12,22,12,16,30,41,70,10,16,41,5,16,41,10,19,16,22,41,0,9,12,13,0,48,10,83,6,10,13,0,1,1,62,106,18,19,7,8,11,0,13,54,0,5,6,11,13,5,6,11,5,11,16,39,0,32,54,15]
private def sixMenuWordsP16 : Array Nat := #[35,0,5,11,13,33,35,44,5,7,16,1,2,13,21,1,13,21,0,1,21,1,5,6,11,33,1,4,7,31,1,21,0,1,5,21,76,9,14,3,7,17,28,45,3,10,11,17,38,45,10,11,16,39,6,11,13,14,6,11,14,0,6,12]
private def sixMenuWordsP17 : Array Nat := #[13,18,4,6,7,11,14,6,10,11,38,6,11,14,53,0,4,6,12,13,18,24,0,4,12,24,6,11,10,11,13,35,43,69,11,13,31,35,31,1,9,21,69,112,113,114,1,9,21,0,28,0,1,7,21,31,4,6,7,11,6,11,31,10]
private def sixMenuWordsP18 : Array Nat := #[56,5,8,5,50,8,9,12,19,1,3,8,10,14,26,1,4,5,6,10,14,40,0,2,3,4,5,8,24,3,5,14,1,3,5,8,10,14,18,24,26,40,1,3,4,5,6,8,10,14,0,2,5,9,12,19,9,58,82,5,17,67,9,16]
private def sixMenuWordsP19 : Array Nat := #[58,2,3,9,19,23,58,10,19,58,2,3,6,18,9,10,16,58,82,0,2,3,6,8,47,1,3,5,8,26,0,2,3,4,6,8,0,1,4,6,7,11,15,29,1,3,4,6,7,8,11,15,29,33,33,39,7,59,8,107,15,60,4,13]
private def sixMenuWordsP20 : Array Nat := #[4,59,60,5,8,10,11,15,35,5,8,15,0,8,35,16,50,2,21,5,13,23,0,22,23,4,15,59,60,108,109,0,1,2,3,8,1,4,25,0,1,2,3,5,8,1,3,8,25,1,3,4,7,8,0,16,1,4,5,10,11,13,15,1]
private def sixMenuWordsP21 : Array Nat := #[3,4,5,7,10,11,15,1,44,51,1,4,7,15,1,3,4,5,6,7,8,10,11,15,3,7,1,3,4,7,8,15,53,110,0,1,4,5,6,7,15,1,35,45,0,1,4,0,2,12,84,0,2,11,31,5,17,28,111,20,39,43,12,19]
private def sixMenuWordsP22 : Array Nat := #[80,20,27,55,0,4,38,3,4,38,3,38,20,28,39,20,22,33,43,55,20,22,39,7,8,28,31,8,31,33,43,44,70,1,4,44,51,1,31,44,51,1,3,8,28,31,1,3,4,8,31,33,70,83,0,1,10,1,14,2,16,32,5,16]
private def sixMenuWordsP23 : Array Nat := #[17,15,16,1,16,0,1,5,6,7,13,1,5,6,7,0,7,17,28]
private def sixMenuWords : Array (Array Nat) := #[sixMenuWordsP0,sixMenuWordsP1,sixMenuWordsP2,sixMenuWordsP3,sixMenuWordsP4,sixMenuWordsP5,sixMenuWordsP6,sixMenuWordsP7,sixMenuWordsP8,sixMenuWordsP9,sixMenuWordsP10,sixMenuWordsP11,sixMenuWordsP12,sixMenuWordsP13,sixMenuWordsP14,sixMenuWordsP15,sixMenuWordsP16,sixMenuWordsP17,sixMenuWordsP18,sixMenuWordsP19,sixMenuWordsP20,sixMenuWordsP21,sixMenuWordsP22,sixMenuWordsP23]
private def sixMenuAtP0 : Array Nat := #[0,1,2,3,1,1,1,4,4,5,6,7,8,9,10,11,1,1,1,12,13,14,1,1,15,16,1,1,1,1,1,1,1,17,18,19,17,20,21,20,22,23,4,1,1,1,24,25,26,27,26,28,1,26,1,26,26,26,4,1,1,29,30,31]
private def sixMenuAtP1 : Array Nat := #[32,33,1,1,19,34,34,34,35,36,37,38,39,38,40,41,42,42,1,43,42,44,45,46,47,1,48,1,1,1,49,1,16,1,2,2,1,50,1,51,52,1,53,14,1,1,54,1,55,1,26,1,56,1,1,1,1,57,1,58,59,1,1,60]
private def sixMenuAtP2 : Array Nat := #[1,61,62,52,63,64,26,1,65,1,66,26,1,1,1,1,33,67,67,68,1,33,1,67,69,1,4,4,69,4,4,1,70,67,71,68,1,67,1,67,1,67,67,6,67,72,1,1,1,67,67,7,67,7,7,73,1,1,1,1,74,8,75,75]
private def sixMenuAtP3 : Array Nat := #[76,26,1,26,77,42,78,1,10,79,1,80,81,10,82,68,83,79,1,1,1,9,1,1,1,26,1,1,1,1,1,84,85,12,86,68,1,1,68,1,83,87,75,1,68,88,83,1,1,68,26,1,89,90,13,91,1,69,92,93,1,26,94,95]
private def sixMenuAtP4 : Array Nat := #[94,1,96,96,97,23,79,94,88,97,1,1,77,1,42,1,1,1,1,42,1,69,69,98,99,83,26,100,26,26,100,26,1,101,102,26,103,1,1,67,69,104,14,26,26,26,26,26,1,105,1,33,33,33,33,1,1,1,1,33,1,1,1,1]
private def sixMenuAtP5 : Array Nat := #[1,106,106,106,106,1,1,1,1,4,107,108,67,1,1,109,110,108,111,67,112,69,113,114,1,103,115,1,116,117,1,1,1,1,1,49,1,1,1,33,118,119,119,1,120,121,121,67,1,69,122,123,67,18,124,1,16,1,1,1,125,1,119,67]
private def sixMenuAtP6 : Array Nat := #[126,75,106,67,75,86,127,128,79,79,16,129,7,67,1,7,88,7,7,7,16,1,88,7,1,7,106,7,7,67,7,7,7,79,67,130,131,49,132,133,134,49,20,26,26,66,1,1,1,135,136,137,26,26,138,135,1,139,140,1,141,142,42,143]
private def sixMenuAtP7 : Array Nat := #[144,53,26,14,53,1,4,145,26,26,16,4,145,4,146,67,67,1,1,42,1,1,26,26,1,1,1,1,147,148,42,149,150,151,152,26,153,97,154,75,75,155,23,156,154,154,23,154,23,3,88,26,1,16,88,157,26,94,77,1,7,158,7,23]
private def sixMenuAtP8 : Array Nat := #[26,26,68,67,159,143,1,160,97,26,42,26,1,42,1,1,145,77,1,26,26,26,69,69,88,1,161,162,163,152,164,75,75,106,164,75,75,165,166,26,167,154,168,169,1,154,75,75,75,1,1,170,170,4,171,172,88,88,124,173,75,26,26,174]
private def sixMenuAtP9 : Array Nat := #[79,26,175,14,176,170,7,68,26,1,26,26,26,69,106,177,178,1,31,179,180,181,182,183,184,185,186,187,188,189,1,34,190,1,16,191,192,193,16,194,195,196,61,197,16,198,199,200,201,202,203,204,205,206,47,207,208,209,210,4,211,209,4,57]
private def sixMenuAtP10 : Array Nat := #[212,213,198,214,215,216,217,218,219,220,57,1,1,1,49,221,1,222,223,1,224,4,225,226,1,26,1,67,227,228,1,229,230,26,1,231,232,233,234,235,236,237,238,26,230,239,240,23,241,242,243,237,1,244,245,77,57,77,1,7,88,246,1,247]
private def sixMenuAtP11 : Array Nat := #[248,7,249,1,60,1,1,1,7,250,97,1,1,251,252,253,2,1,229,4,4,1,254,255,256,257,26,258,259,260,26,61,261,262,263,26,261,264,265,1,266,267,26,26,1,237,75,1,75,1,49,1,1,268,269,4,270,271,272,1,273,1,274,1]
private def sixMenuAtP12 : Array Nat := #[275,276,277,278,278,279,278,280,281,282,283,284,1,285,286,287,1,288,289,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,33,33,1,33,1,33,33,67,67,42,1,69,69,1,1,1,69]
private def sixMenuAtP13 : Array Nat := #[290,170,1,106,1,290,49,1,291,67,67,68,1,79,1,1,1,67,1,71,1,1,42,1,67,79,1,42,1,67,1,1,1,1,1,1,187,67,67,67,33,1,42,42,1,1,1,1,1,1,1,1,26,1,1,1,1,26,1,1,1,1,1,1]
private def sixMenuAtP14 : Array Nat := #[16,1,7,1,1,1,16,1,1,1,1,1,1,292,7,42,1,67,1,138,106,67,1,106,7,7,7,7,1,67,67,1,1,214,1,42,106,42,42,1,49,96,290,1,1,1,96,1,1,1,1,1,1,1,26,1,1,67,1,1,1,67,1,1]
private def sixMenuAtP15 : Array Nat := #[1,1,26,1,1,1,1,1,26,1,1,1,26,1,1,1,1,1,1,26,1,1,1,1,1,1,1,26,26,1,1,1,42,74,76,42,1,1,1,26,26,1,1,42,26,26,42,42,42,26,231,26,26,26,26,26,42,42,42,42,42,26,1,1]
private def sixMenuAtP16 : Array Nat := #[26,26,26,231,26,1,1,1,1,1,1,293,1,106,87,86,75,1,77,42,77,78,1,1,1,1,26,88,1,1,1,1,26,26,130,1,294,274,295,296,296,69,274,1,297,298,68,1,299,1,300,94,96,96,42,1,1,97,42,1,298,1,1,67]
private def sixMenuAtP17 : Array Nat := #[42,274,301,57,1,26,26,88,298,26,1,302,1,42,42,26,1,1,1,1,26,23,1,1,1,42,1,1,1,1,1,1,1,1,26,26,1,1,1,1,1,1,1,1,1,1,303,77,23,77,68,1,77,77,1,1,42,1,42,1,1,77,77,1]
private def sixMenuAtP18 : Array Nat := #[1,1,1,16,77,42,1,1,1,274,1,42,42,42,77,42,57,1,77,77,1,1,1,77,77,42,42,42,1,42,42,42,42,77,42,42,26,1,1,26,26,1,1,77,1,42,78,77,1,1,1,1,26,26,69,69,294,304,87,274,57,294,57,67]
private def sixMenuAtP19 : Array Nat := #[26,1,138,1,1,294,26,1,26,1,305,1,67,69,26,1,4,92,92,92,26,26,26,26,8,26,26,26,26,26,69,69,69,69,1,69,1,1,12,1,75,1,68,26,306,26,68,68,1,57,296,305,1,69,92,42,26,93,26,92,92,1,92,42]
private def sixMenuAtP20 : Array Nat := #[1,92,1,1,1,1,14,1,3,1,42,1,26,26,26,26,26,307,26,299,172,26,42,26,26,26,42,42,42,1,42,1,1,1,1,308,309,26,75,291,1,1,26,1,1,1,1,287,7,1,68,1,42,26,42,26,26,42,42,42,42,42,1,26]
private def sixMenuAtP21 : Array Nat := #[26,42,42,26,26,26,1,42,1,42,42,33,33,33,16,310,311,312,170,67,1,313,1,314,315,316,317,318,290,319,320,321,322,122,120,323,79,79,1,103,1,116,103,324,115,16,325,67,67,325,1,326,86,33,327,1,16,88,1,1,1,1,1,69]
private def sixMenuAtP22 : Array Nat := #[7,1,1,129,69,69,69,1,1,1,1,1,292,1,138,7,86,299,293,274,67,1,42,328,49,112,69,1,1,67,1,130,26,1,1,274,1,49,329,1,330,331,26,291,136,26,26,128,1,119,1,1,1,1,1,1,16,16,1,332,333,170,125,1]
private def sixMenuAtP23 : Array Nat := #[26,326,75,106,26,26,75,138,334,26,42,128,42,138,138,42,1,69,335,1,42,154,143,1,336,26,1,26,67,26,1,26,1,42,1,1,1,337,338,151,152,26,1,339,340,42,1,1,26,23,7,1,1,1,341,16,1,88,342,7,7,26,26,77]
private def sixMenuAtP24 : Array Nat := #[26,343,214,1,26,26,26,42,42,1,1,75,26,67,67,344,143,1,97,42,77,42,42,26,302,345,346,346,26,347,77,348,77,349,42,42,42,42,77,143,1,346,346,77,143,143,3,3,145,26,350,351,42,143,143,143,77,143,42,231,42,143,346,1]
private def sixMenuAtP25 : Array Nat := #[42,1,26,1,1,26,148,26,69,1,352,145,353,1,354,14,69,355,88,356,357,358,152,92,1,1,1,77,356,357,163,152,26,26,359,75,75,106,359,75,75,360,307,361,26,362,154,363,364,1,154,75,75,75,1,1,26,79,26,26,7,287,365,14]
private def sixMenuAtP26 : Array Nat := #[366,170,7,139,42,26,26,42,26,42,42,106,42,42,42,26,26,75,367,346,368,369,42,346,26,370,371,14,42,42,42,1,346,42,42,42,26,1,42,1,26,372,373,42,42,42,42,374,1,375,376,377,16,191,378,379,380,381,382,383,384,385,1,386]
private def sixMenuAtP27 : Array Nat := #[387,387,388,389,390,391,184,392,393,394,395,214,396,397,57,1,187,398,26,187,399,308,400,214,401,303,23,402,403,404,405,406,309,407,248,23,408,409,251,1,410,237,411,412,413,414,4,415,416,417,1,418,57,419,420,332,261,421,422,422,26,257,423,424]
private def sixMenuAtP28 : Array Nat := #[267,425,426,427,428,1,429,1,430,431,432,271,433,434,26,4,435,436,437,438,437,439,440,441,231,440,7,442,443,428,265,261,444,445,261,446,447,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
private def sixMenuAtP29 : Array Nat := #[1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
private def sixMenuAtP30 : Array Nat := #[1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,290,290,1,1,16,1,1,1,1,1,1,1,1,1,290,26,1,170,1,106,1,290,290,49,1,291,1,67,67,75,1,26,1,26,1,1,1,1,1,1,1,1,1,1,1,1,1]
private def sixMenuAtP31 : Array Nat := #[1,1,1,26,42,26,1,42,1,1,1,1,26,26,26,1,1,1,1,26,300,1,57,26,1,1,16,16,1,1,23,1,42,1,1,26,1,1,1,1,1,1,1,303,88,23,3,1,77,16,16,26,42,3,26,1,77,42,77,1,42,1,57,1]
private def sixMenuAtP32 : Array Nat := #[26,1,77,77,77,1,26,57,1,26,1,305,69,92,26,92,26,26,26,26,26,26,26,69,130,1,274,57,69,274,92,92,1,1,1,26,26,1,1,1,274,26,26,1,26,26,42,42,42,1,1,1,1,1,1,1,1,1,1,1,42,42,26,42]
private def sixMenuAtP33 : Array Nat := #[42,1,274,26,26,42,42,1,1,26,42,42,26,1,26,1,1,1,42,42,448,449,313,1,450,316,318,290,326,451,452,67,71,1,332,453,454,455,151,152,346,346,26,26,456,96,139,139,26,139,26,26,371,346,26,372,1,1,1,1,1,1,1,1]
private def sixMenuAtP34 : Array Nat := #[1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
private def sixMenuAt : Array (Array Nat) := #[sixMenuAtP0,sixMenuAtP1,sixMenuAtP2,sixMenuAtP3,sixMenuAtP4,sixMenuAtP5,sixMenuAtP6,sixMenuAtP7,sixMenuAtP8,sixMenuAtP9,sixMenuAtP10,sixMenuAtP11,sixMenuAtP12,sixMenuAtP13,sixMenuAtP14,sixMenuAtP15,sixMenuAtP16,sixMenuAtP17,sixMenuAtP18,sixMenuAtP19,sixMenuAtP20,sixMenuAtP21,sixMenuAtP22,sixMenuAtP23,sixMenuAtP24,sixMenuAtP25,sixMenuAtP26,sixMenuAtP27,sixMenuAtP28,sixMenuAtP29,sixMenuAtP30,sixMenuAtP31,sixMenuAtP32,sixMenuAtP33,sixMenuAtP34]
private def atSix (v : Array (Array Nat)) (i : Nat) : Nat := ((v[i/64]?).getD #[])[i%64]?.getD 0
private def sixOffset : Nat → Nat
  | 6 => 0
  | 7 => 7
  | 8 => 142
  | 9 => 787
  | 10 => 1829
  | 11 => 2168
  | 12 => 2217
  | 13 => 2222
  | _ => 0
private def inlineMenu (m k i : Nat) : List Nat :=
  if m=253 then
    let mnum := atSix sixMenuAt (sixOffset k+i)
    let offsetCode := atSix sixMenuStarts mnum
    (List.range (offsetCode % 16)).map (fun j => atSix sixWords (atSix sixMenuWords (offsetCode / 16 + j)))
  else []

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
  cases tag with
  | zero =>
    change works ([25, 42, 52] : List (BitVec 6)) 56 4 false T k ws code = true at ok
    apply physical (ok:=ok)
    · rintro ⟨b,e⟩
      have zero : false=b := congrFun e (0 : Fin 6)
      have one : true=b := congrFun e (3 : Fin 6)
      cases b <;> contradiction
    · intro _ _ r h
      exact PriceThree.majority_six_price r h
  | succ tag =>
    cases tag with
    | zero =>
      change works ([43, 42, 76, 112] : List (BitVec 7)) 22 5 false T k ws code = true at ok
      apply physical (ok:=ok)
      · rintro ⟨b,e⟩
        have zero : false=b := congrFun e (0 : Fin 7)
        have one : true=b := congrFun e (1 : Fin 7)
        cases b <;> contradiction
      · intro _ _ r h
        exact PatternFive.pattern_price r h
    | succ tag =>
      cases tag with
      | zero =>
        change works ([43, 42, 76, 112] : List (BitVec 7)) 22 5 true T k ws code = true at ok
        apply physical (ok:=ok)
        · rintro ⟨b,e⟩
          have zero : false=b := congrFun e (0 : Fin 7)
          have one : true=b := congrFun e (1 : Fin 7)
          cases b <;> contradiction
        · intro _ _ r h
          exact PatternFive.pattern_price r h
      | succ tag =>
        cases tag with
        | zero =>
          change works ([21, 5, 38, 56] : List (BitVec 6)) 11 4 false T k ws code = true at ok
          apply physical (ok:=ok)
          · rintro ⟨b,e⟩
            have zero : false=b := congrFun e (2 : Fin 6)
            have one : true=b := congrFun e (0 : Fin 6)
            cases b <;> contradiction
          · intro _ _ r h
            exact PatternFour.pattern_price r h
        | succ tag =>
          cases tag with
          | zero =>
            change works ([21, 5, 38, 56] : List (BitVec 6)) 11 4 true T k ws code = true at ok
            apply physical (ok:=ok)
            · rintro ⟨b,e⟩
              have zero : false=b := congrFun e (2 : Fin 6)
              have one : true=b := congrFun e (0 : Fin 6)
              cases b <;> contradiction
            · intro _ _ r h
              exact PatternFour.pattern_price r h
          | succ tag =>
            change false = true at ok
            cases ok
end FourColumnFace
private def paidWordsP0 : Array Nat := #[23711441814912,211198591467537,288258104866443568,288301952075841544,216191750032071048,10176946012177,88579557638272,75334817693824,216186079806491984,216212571571651728,216186079810716816,288244828807105572,216178353047080336,216178353042885968,288271247669462284,14414062043144,14383996813313,152068008562933832,211691564449800,150171322013548673,211661382238209,150105350242123841,176095943229448,158901577484107936,176065761017857,142662732611904,72025527894144,158893880902713504,106243534372992,150171322013548609,36972171362688,152141676915753096,44567265551488,36455835762952,81066034675059008,150237291637456961,44019673998337,44669943680128,158897179437596832,44122352126977,41372348581248,14880988726656,147985492762984580,154740892608266372,44668869937280,72024588370048,44395065772096,142117380915264,152138378380869768,79446178562049,72023514628224,142421274919176,211660442714113,211690507485192,81073761203325248,158910424914624672,10722406826368,216178353042900048,10480811245952,36972171100544,150184567490576449,10480811262080,176083997851653,149592637997061]
private def paidWordsP1 : Array Nat := #[176066817720384,149575457865792,44566258918528,36565808129088,10451937200256,10038009727012,36840618926208,44393992031296,48689360675904,36839612294272,36323209584652,10450930568320,158423091085317,44395132881984,152207647613419656,158963150135263392,152154923399413896,158910425921257632,10055256902692,176747173650496,150358894577728,40738503271436,150221455624224,36340456760332,14453303413796,158676494155840,88582627868800,211387573895185,211661382238225,10175985551424,211417756106760,211387573895169,150359431448640,152084552574844937,10450863458432,150184567490576513,176337400660032,142661793087808,176065760755713,74858075865089,145258076471304,150114197672640521,152154922392780936,211147055726593,10452876738688,48537643781125,61783525038097,150087791544321,150358374484032,10038949265440,211521237975072,27699184736304,40871127155980,27699184736272,54117008412952,105695942819841,72293044715904,150114197672640577,72023917281408,105834457628673,71883261247520,176095942967304,53984384585752,27729132523792]
private def paidWordsP2 : Array Nat := #[61680849006609,79750563905664,105864639840264,14574032325696,71777648640264,105726125031432,44667812972672,10205933338944,149843910099008,72053587722248,44291313901632,79750043811968,36973244842368,153475336470806600,142148523556872,88580497621120,142422331899912,71779779379208,72157069590560,150114128953163841,147845854786257028,150184498771099777,147916222456676420,154601254631538820,154671622301958212,106241403666560,150100952195612737,36564667278400,54117010510104,211147173167112,145223850426368,75336947941504,145430814228544,36972238210432,152071307097817160,44291313902656,40979961029760,36973244843392,142119394181184,79752174518400,216243186434097312,79990146205824,79577829345312,106378425278592,288253758042804544,10722524268672,37109616345408,216225662691782993,288284493546590488,216212416810526020,211385560629249,288244828811299876,37111205994624,288442171728936996,288271247665333516,288442171728674848,216313797703409697,216207971342917824,211793989353504,288442068648149004,216177249223738512,216313797701830665,288442068647886856,40871129252876]
private def paidWordsP3 : Array Nat := #[44395066034240,36323209585672,150237292711215233,41097470674240,154740891534508100,79579842641952,44668870199424,72023514890368,216212386628774925,152154853673304136,216225632510031897,152207646539661384,216313797701370121,216173916144566720,288442171729133600,216186079806506064,152084554655219784,216181716321060960,44567265550464,288252933396500608,145430814163008,48434967741445,216181582661191872,216185997954681024,216190391823667332,152154853673304200,216186079810718864,53984384593944,211795046318112,288258074692556848,216185997954682048,216199243835152576,216185997948628068,36564667277376,158840055096688736,288244858989315364,288258104870572336,288244858993509668,288258104874766640,216186131610668325,216199377491925297,79750044074112,216225662691782937,150184498771099713,216212416810526085,288271114003293196,150359431449664,216212386628774988,288278914181958661,288292056582926353,288278810701669381,74888258535432,288244858985186596,216178353047110800,216313797703409704,216313797701830696,216243703835543592,216212571567440976,216243703835543561,288441895777304612,288441895777042464,216207971338707136,216174019622224320,216178331432002916]
private def paidWordsP4 : Array Nat := #[288288118305468544,288441792698286088,288441762633056257,288441762631483393,216186079810686352,216178331433845184,216185997950470336,216178353042900304,216186079806508112,216173916140356032,216181582656981184,216178353047094672,216178353047111056,216178353042916688,216186079806524496,216186079810702480,216243703835083017,216185997950471360,216178331433846208,288258074684692528,288292160063215633,288441895777501216,288284359884550168,150100953269371009,152084552574845000,158826809619660896,154539680906625092,36696353669440,157917432167546960,40871129253132,61783527135249,48537645878277,150100952195612681,152071307097817097,81066035618253064,108088045705627912,151223606047178896,71611600420864,74310533096423808,156676165812912260,156649674858856580,75336947875968,158823511084777568,72295057981824,79338247045152,149846040805440,149574400901121,105726125293576,36840618927232,14483251266596,48434967749636,211387573895172,106243534635136,79752174780544,44291314163776,10451937201280,10038009728032,75593643197568,10038076836900,288319162798837888,155550248725938320,155523757771882640,211400509128708,44393992292416]
private def paidWordsP5 : Array Nat := #[40871062144012,108095772351801376,152084552574844968,158826809619660840,158840055096688680,108122263710083080,152071307097817128,48965312324736,81073763342387264,81073762264434816,106241521107072,141877936488456,79204582965249,71508118552584,142662732612928,211387573895173,72295057982848,158839986377212000,158910356195147936,152084483855368264,10175985552448,71611600420896,154635471040102468,147853580240764996,142524756787488,88582627803264,216243186427781153,44392935065664,81073762264418561,36697293193536,156510035808370756,216313556247822401,216208242974926857,10481884987776,176748113174592,48434967749637,27729132523824,61680848998417,40871129253124,54117010510096,71881130508576,158897178363838560,158826810693419168,147923950058700868,10038009727008,36455902610700,158897179437596768,158826809619660960,158910424914624608,158840055096688800,14453303479332,14453303479300,152154922392780809,23383144468800,152154922392780872,149832718400897120,149903088218833056,151301701319622800,147923950058700932,79444165265409,61680849006608,154601253557780548,147845853712498756,216313526061926472]
private def paidWordsP6 : Array Nat := #[44393992030272,216181854301096065,151223604973420624,154671623375716484,147916223530434692,145961317827648,155479878908002369,216182130244389185,14483251266820,151231331501686864,216178555691799889,44036920975365,41238665700480,154705840858038340,40962714051648,156605795994976324,288252933396496512,72025528156288,40871062144260,149574400901184,149708064980992,14483184157956,216181716325271712,216243203613966472,216173933324435848,216174036806304160,216243307095834784,216313659729690696,216313556245717088,216208242982822024,216181854294780064,44292387643456,216208518926575688,48417787880452,48537645878276,48537578769412,36971231576448,216313556245717025,216185997948628036,198300771454812425,44669943679104,10175985551488,189301268359940105,146727663153791072,216199243829885104,216185997948628132,216199243829885040,14849983974528,211521237975040,146798032971727008,149903088218833025,149832718400897089,149903088218833088,149832718400897096,198308468153649161,147923948984942660,145430814687296,288305968658515328,288245241126325376,216243173482086532,288271629406971008,216186528293203108,154705840858038404,53984384593936]
private def paidWordsP7 : Array Nat := #[216186131610668356,288261729623742592,216243186427781280,216181854301096096,216313659726006344,216208518930260040,216191577313259832,216243156245569576,216243156251885704,216208518926115081,216313659725545737,216178331432002948,216185997948628100,288274940877086848,288267214113480832,216212916505949360,216212640554300528,216174157595943208,216174157602259336,216182130248534081,216177249219527760,216212416810525965,288389532612563008,151293974791356560,156579305040920644]
private def paidWords : Array (Array Nat) := #[paidWordsP0,paidWordsP1,paidWordsP2,paidWordsP3,paidWordsP4,paidWordsP5,paidWordsP6,paidWordsP7]
private def paidItemsP0 : Array Nat := #[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,19,24,21,20,25,26,21,27,28,29,30,31,32,8,13,33,34,35,36,35,37,35,38,39,40,41,42,43,17,44,45,46,47,48,49,50,51,8,13,34]
private def paidItemsP1 : Array Nat := #[51,52,53,54,55,52,56,54,55,8,13,51,52,53,55,10,28,57,58,29,59,60,61,62,63,29,59,60,53,64,64,65,66,67,68,69,70,71,72,73,74,75,0,76,70,72,73,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93]
private def paidItemsP2 : Array Nat := #[94,95,68,96,97,98,99,70,100,101,102,94,103,104,97,105,51,68,99,106,56,99,101,107,108,52,101,109,110,111,112,102,108,51,55,101,102,105,52,107,102,113,28,114,115,116,117,118,119,120,114,106,99,121,122,123,58,124,125,58,59,126,58,127]
private def paidItemsP3 : Array Nat := #[97,125,128,122,129,123,130,131,132,133,134,128,135,136,137,138,139,55,99,140,141,7,137,142,143,144,145,121,146,147,148,149,150,151,152,124,138,153,154,155,19,59,60,44,93,156,103,53,157,158,159,160,138,161,162,163,164,71,165,28,166,18,95,122]
private def paidItemsP4 : Array Nat := #[167,18,29,32,17,18,30,31,57,22,31,33,34,35,35,26,168,169,57,169,170,171,171,57,172,170,49,57,22,49,51,57,47,57,45,8,13,55,56,173,13,57,167,174,23,175,176,177,10,53,57,178,10,57,4,57,179,57,180,32,57,58,181,176]
private def paidItemsP5 : Array Nat := #[182,31,181,182,179,57,176,183,35,53,58,35,59,176,184,185,186,176,187,57,188,18,18,31,40,53,62,43,189,190,88,191,78,68,78,192,69,162,193,68,78,194,73,194,70,79,194,76,78,195,196,26,88,49,197,49,68,93,192,198,6,49,199,200]
private def paidItemsP6 : Array Nat := #[199,200,50,201,49,202,2,52,68,203,204,205,89,203,206,207,92,208,89,203,209,89,203,207,68,70,210,210,94,95,211,33,51,212,213,190,36,58,179,190,10,214,215,16,104,8,188,188,216,217,218,106,114,115,114,117,55,157,219,189,190,218,53,115]
private def paidItemsP7 : Array Nat := #[125,189,190,220,126,179,221,55,190,220,124,124,127,126,220,214,222,223,69,93,224,154,162,115,138,225,123,156,226,55,226,55,226,227,228,229,230,147,231,232,146,231,232,145,233,145,124,138,145,7,234,235,124,145,155,183,190,236,183,237,103,176,238,239]
private def paidItemsP8 : Array Nat := #[240,241,242,176,104,243,168,177,8,168,244,185,184,188,245,246,207,247,248,9,10,207,249,189,247,248,250,205,204,2,251,204,246,2,246,252,253,254,10,207,211,188,215,8,10,189,214,189,214,218,222,224,255,256,224,255,257,258,259,11,258,259,8,260]
private def paidItemsP9 : Array Nat := #[261,262,263,264,265,266,267,268,267,269,270,271,204,272,249,259,9,204,249,272,10,57,207,245,267,271,218,263,264,268,273,274,183,183,190,179,237,183,275,240,276,10,57,183,277,9,57,189,241,278,278,257,14,277,17,21,60,279,26,132,162,226,280,281]
private def paidItemsP10 : Array Nat := #[97,282,283,284,97,105,156,285,286,287,34,97,105,288,289,97,289,290,51,97,99,105,106,288,289,97,105,288,289,97,99,101,289,97,289,291,31,106,121,154,58,106,121,148,154,292,93,117,293,19,31,99,106,121,154,162,280,19,99,106,121,139,154,280]
private def paidItemsP11 : Array Nat := #[19,99,294,99,121,295,296,297,19,25,31,100,298,19,32,95,24,27,31,95,100,25,95,299,27,17,38,57,138,36,172,37,172,38,39,17,18,25,57,99,125,177,25,133,138,210,300,17,19,17,31,57,106,125,133,17,20,57,102,301,17,20,57,99]
private def paidItemsP12 : Array Nat := #[301,25,57,99,301,19,99,102,138,17,138,17,20,25,26,18,167,210,301,138,28,31,57,106,210,302,55,57,95,302,57,100,20,95,55,106,57,95,102,106,19,99,102,19,99,102,106,163,303,19,32,26,32,154,26,155,26,32,38,154,281,32,155,154]
private def paidItemsP13 : Array Nat := #[38,155,281,304,191,210,305,306,307,31,78,210,281,36,69,193,38,68,308,69,69,308,31,38,69,304,309,31,70,309,71,71,309,310,19,70,71,72,304,28,281,311,74,281,74,311,281,312,28,74,308,313,314,315,31,70,71,72,304,38,193,316,317,28]
private def paidItemsP14 : Array Nat := #[31,74,308,314,308,309,318,308,309,162,319,88,94,125,191,320,133,138,300,83,84,86,99,321,322,323,324,325,326,26,121,327,31,44,46,106,162,280,328,329,330,70,162,280,55,94,207,331,93,332,333,19,70,99,138,26,93,70,162,138,167,162,163,99]
private def paidItemsP15 : Array Nat := #[162,280,280,121,154,166,225,301,162,28,167,68,99,121,154,225,301,26,166,225,121,154,225,334,335,336,308,318,28,94,202,217,337,338,339,155,340,26,99,225,297,318,95,93,94,138,167,70,119,225,280,341,26,70,99,342,343,68,226,280,281,51,86,297]
private def paidItemsP16 : Array Nat := #[344,297,345,55,280,55,99,162,280,344,346,51,99,102,140,344,135,95,167,132,135,332,34,55,97,105,156,283,288,289,290,347,348,55,128,154,349,121,154,105,285,288,350,38,55,97,105,289,55,105,106,288,55,105,288,106,121,226,106,121,106,116,118,121]
private def paidItemsP17 : Array Nat := #[31,106,121,349,351,51,99,106,226,281,352,38,55,121,154,226,51,302,353,20,25,99,100,220,354,38,55,121,154,55,106,302,353,102,302,128,156,355,356,127,213,357,213,357,55,121,358,359,28,95,299,106,156,189,55,220,210,302,121,302,55,121,28,95]
private def paidItemsP18 : Array Nat := #[121,28,360,115,361,362,363,68,115,353,297,364,297,365,121,154,212,302,93,135,51,226,100,119,302,349,360,93,115,138,225,55,226,366,367,368,369,68,226,353,93,115,138,225,370,68,166,301,18,20,220,354,93,138,225,28,55,68,99,106,117,226,371,117]
private def paidItemsP19 : Array Nat := #[126,297,345,357,371,93,117,93,115,97,156,372,373,28,95,26,93,115,131,167,28,95,99,93,220,26,68,93,115,167,60,374,26,93,117,371,375,376,377,378,68,93,117,371,94,95,167,301,302,332,26,93,167,26,68,93,167,68,93,115,68,93,302,331]
private def paidItemsP20 : Array Nat := #[26,93,115,167,332,379,306,332,379,380,167,332,379,121,154,381,382,106,119,210,138,332,379,19,99,106,226,280,383,384,99,280,19,99,280,19,99,162,280,55,106,140,162,280,385,55,121,154,382,386,382,386,148,150,151,152,387,388,31,38,154,342,343,55]
private def paidItemsP21 : Array Nat := #[225,241,295,55,154,225,26,70,166,297,93,225,55,106,121,154,99,212,389,121,154,342,343,26,299,125,333,349,106,210,225,26,225,93,128,166,93,128,26,95,99,121,166,55,121,154,18,96,301,26,70,166,55,121,390,55,99,121,154,20,89,95,160,20]
private def paidItemsP22 : Array Nat := #[25,26,166,70,121,166,70,225,341,31,106,121,226,349,391,31,60,97,106,349,26,93,115,106,114,121,106,121,225,226,26,121,225,68,93,121,127,293,392,132,333,349,26,299,349,121,154,188,216,343,393,26,121,154,225,220,394,106,121,390,147,342,343,106]
private def paidItemsP23 : Array Nat := #[121,237,278,100,220,226,354,106,210,20,95,395,26,95,166,26,93,128,167,20,95,167,26,93,95,166,26,115,225,154,225,93,333,138,162,163,165,396,280,297,396,138,162,280,138,162,363,397,131,398,342,343,399,400,342,343,399,297,318,106,138,167,297,131]
private def paidItemsP24 : Array Nat := #[335,398,401,308,309,401,106,167,26,93,95,225,17,100,299,21,402,35,138,172,35,57,172,18,57,133,299,18,35,57,60,210,220,17,26,38,57,102,125,167,210,300,21,57,28,57,167,57,95,106,301,32,57,95,301,302,299,301,31,57,106,403,404,301]
private def paidItemsP25 : Array Nat := #[57,172,358,392,405,35,57,57,299,299,65,182,57,232,406,57,232,234,19,25,31,96,19,26,32,94,95,154,163,194,210,279,306,306,162,281,31,68,163,303,69,162,167,193,316,407,408,409,410,83,88,168,169,411,25,44,83,99,191,246,191,321,57,94]
private def paidItemsP26 : Array Nat := #[114,138,211,380,31,86,330,331,412,413,22,303,331,333,329,321,26,38,44,70,93,162,414,415,416,20,70,220,20,93,99,163,23,93,163,138,306,417,418,419,25,99,176,182,329,20,89,182,334,162,182,334,25,414,280,339,20,176,68,93,94,95,308,70]
private def paidItemsP27 : Array Nat := #[95,114,176,225,309,176,335,26,95,309,182,242,31,94,162,335,416,90,94,176,308,94,106,280,95,176,309,95,309,86,420,421,140,353,28,94,114,167,211,55,302,347,352,356,422,34,213,290,36,302,106,212,297,121,353,106,353,147,148,263,121,220,356,55]
private def paidItemsP28 : Array Nat := #[127,220,188,263,106,188,216,423,19,31,68,79,93,115,140,362,369,424,68,371,371,68,69,93,425,121,280,425,131,211,426,68,99,106,57,207,93,94,95,188,211,99,106,268,93,121,280,68,93,99,106,170,360,68,99,106,115,349,384,20,128,226,226,427]
private def paidItemsP29 : Array Nat := #[18,20,99,106,357,93,94,95,117,117,28,95,114,356,55,224,226,357,428,429,430,55,114,226,147,149,217,297,339,343,378,263,268,335,117,131,431,335,117,131,211,263,432,114,115,99,106,121,280,94,95,99,106,121,280,55,117,220,117,427,433,55,114,117]
private def paidItemsP30 : Array Nat := #[226,114,357,106,167,280,93,99,106,117,121,280,434,435,375,376,375,435,436,437,93,211,438,106,290,35,154,343,295,106,121,147,148,439,147,242,241,295,220,241,242,55,220,241,242,18,238,147,18,106,18,121,220,18,55,121,55,121,176,182,220,147,276,440]
private def paidItemsP31 : Array Nat := #[18,55,106,220,18,106,121,220,147,440,18,55,220,103,441,442,443,444,340,445,241,276,395,309,342,446,237,278,94,167,237,278,55,94,226,240,276,55,106,114,226,240,276,280,95,106,114,280,25,437,94,106,280,447,309,95,99,106,121,280,55,95,99,114]
private def paidItemsP32 : Array Nat := #[121,176,182,226,94,114,55,95,226,55,95,114,226,94,95,106,280,95,99,121,94,241,401,93,94,95,401,177,448,449,168,188,245,57,245,245,450,188,207,245,451,9,57,416,452,9,411,453,188,207,245,207,245,414,207,245,244,246,176,454,172,455,422,456]
private def paidItemsP33 : Array Nat := #[256,457,458,459,460,211,315,461,462,400,263,264,315,188,211,249,463,464,57,465,172,465,57,466,10,351,467,57,237,468,237,188,278,468,19,162,280,332,121,154,226,281,121,128,355,106,121,154,302,93,226,343,393,115,370,93,343,393,19,99,121,154,162,280]
private def paidItemsP34 : Array Nat := #[19,99,99,162,166,280,57,95,99,210,355,31,57,106,210,57,355,19,28,31,281,19,210,318,31,210,281,94,99,125,162,280,26,121,154,210,99,210,19,162,31,106,125,133,162,280,99,100,162,226,280,281,301,70,162,167,280,99,162,167,280,99,167,100]
private def paidItemsP35 : Array Nat := #[138,162,280,19,70,99,138,280,94,138,167,301,138,162,167,280,231,469,470,343,121,154,342,102,297,302,55,119,121,128,154,121,154,355,38,115,281,115,128,219,68,297,115,226,343,68,115,302,331,28,115,297,318,115,226,226,281,302,28,68,99,106,38,55]
private def paidItemsP36 : Array Nat := #[226,281,226,281,68,302,331,68,115,226,281,370,115,128,219,370,117,297,345,371,99,121,128,28,115,318,114,226,297,345,121,280,115,343,377,378,393,93,332,333,370,93,115,332,333,370,55,121,138,154,162,225,280,296,387,55,225,55,121,154,225,378,446,121]
private def paidItemsP37 : Array Nat := #[154,295,342,343,93,121,154,225,121,154,399,121,154,343,355,382,55,106,210,225,38,55,121,162,280,31,99,106,119,121,31,106,121,225,280,31,106,121,225,388,471,31,106,121,154,210,225,121,154,343,393,55,121,154,343,393,154,188,295,343,382,342,381,399]
private def paidItemsP38 : Array Nat := #[472,26,94,95,99,114,121,138,210,306,318,306,470,38,70,93,100,125,138,162,167,300,138,162,245,280,162,167,280,167,182,28,38,68,93,102,115,125,226,297,318,343,378,188,216,376,93,121,154,343,240,242,95,231,232,241,242]
private def paidItems : Array (Array Nat) := #[paidItemsP0,paidItemsP1,paidItemsP2,paidItemsP3,paidItemsP4,paidItemsP5,paidItemsP6,paidItemsP7,paidItemsP8,paidItemsP9,paidItemsP10,paidItemsP11,paidItemsP12,paidItemsP13,paidItemsP14,paidItemsP15,paidItemsP16,paidItemsP17,paidItemsP18,paidItemsP19,paidItemsP20,paidItemsP21,paidItemsP22,paidItemsP23,paidItemsP24,paidItemsP25,paidItemsP26,paidItemsP27,paidItemsP28,paidItemsP29,paidItemsP30,paidItemsP31,paidItemsP32,paidItemsP33,paidItemsP34,paidItemsP35,paidItemsP36,paidItemsP37,paidItemsP38]
private def paidMenusP0 : Array Nat := #[0,1,17,33,49,65,81,97,113,129,145,161,177,194,225,242,279,386,417,435,482,513,530,562,596,658,690,723,770,802,840,961,984,1106,1137,1153,1174,1267,1313,1332,1394,1427,1474,1506,1538,1570,1604,1666,1698,1732,1794,1826,1863,1970,2002,2033,2050,2081,2097,2113,2130,2161,2178,2209]
private def paidMenusP1 : Array Nat := #[2225,2242,2274,2308,2373,2450,2482,2513,2529,2546,2578,2611,2658,2690,2722,2753,2771,2818,2849,2865,2884,2946,2977,2994,3025,3042,3074,3105,3122,3154,3185,3203,3250,3282,3314,3348,3414,3505,3521,3542,3635,3682,3715,3763,3809,3826,3857,3874,3909,3986,4018,4050,4081,4097,4115,4161,4179,4225,4241,4258,4290,4321,4339,4388]
private def paidMenusP2 : Array Nat := #[4449,4466,4497,4514,4548,4610,4641,4661,4737,4755,4801,4818,4849,4868,4930,4963,5010,5044,5106,5139,5185,5203,5251,5302,5394,5426,5457,5474,5507,5555,5601,5617,5633,5651,5699,5747,5794,5827,5875,5921,5938,5970,6005,6084,6146,6177,6193,6210,6246,6340,6402,6434,6465,6483,6531,6577,6595,6642,6673,6689,6705,6722,6754,6787]
private def paidMenusP3 : Array Nat := #[6833,6849,6866,6898,6929,6945,6963,7010,7043,7091,7142,7235,7283,7329,7346,7378,7411,7458,7489,7506,7539,7585,7602,7634,7670,7762,7793,7811,7858,7889,7907,7955,8002,8033,8051,8098,8130,8161,8178,8210,8241,8258,8290,8322,8353,8369,8385,8402,8433,8449,8466,8500,8564,8625,8641,8658,8690,8723,8770,8802,8833,8849,8865,8882]
private def paidMenusP4 : Array Nat := #[8914,8945,8962,8993,9010,9041,9060,9121,9139,9186,9218,9250,9282,9314,9348,9410,9442,9476,9540,9602,9636,9698,9729,9746,9778,9810,9841,9857,9876,9939,9986,10017,10033,10050,10082,10113,10129,10145,10161,10180,10244,10310,10405,10483,10535,10644,10708,10771,10820,10886,10979,11032,11159,11267,11314,11346,11377,11397,11475,11524,11585,11603,11649,11668]
private def paidMenusP5 : Array Nat := #[11730,11762,11794,11831,11941,12018,12054,12149,12229,12308,12372,12434,12468,12532,12593,12613,12689,12708,12770,12802,12834,12868,12931,12980,13042,13074,13107,13154,13189,13266,13297,13314,13346,13381,13460,13523,13571,13617,13634,13667,13714,13747,13793,13810,13841,13861,13939,13986,14018,14050,14085,14161,14181,14258,14290,14325,14403,14450,14482,14517,14595,14650,14803,14857]
private def paidMenusP6 : Array Nat := #[14995,15044,15107,15156,15218,15250,15282,15314,15347,15393,15413,15489,15506,15538,15572,15635,15683,15731,15778,15811,15860,15922,15956,16017,16033,16052,16117,16195,16242,16276,16340,16402,16434,16470,16562,16595,16641,16658,16691,16747,16916,16978,17012,17077,17156,17219,17267,17314,17348,17413,17494,17589,17667,17715,17763,17812,17876,17938,17972,18035,18082,18116,18179,18227]
private def paidMenusP7 : Array Nat := #[18274,18306,18338,18370,18403,18450,18484,18547,18594,18626,18660,18722,18754,18789,18868,18934,19027,19077,19155,19202,19234,19267,19314,19350,19446,19538,19570,19603,19649,19666,19701,19779,19826,19861,19938,19974,20066,20100,20166,20259,20308,20371,20420,20484,20546,20580,20643,20692,20755,20803,20855,20962,20995,21044,21110,21205,21282,21316,21378,21413,21492,21555,21604,21666]
private def paidMenusP8 : Array Nat := #[21700,21761,21778,21812,21874,21907,21955,22002,22035,22082,22117,22195,22243,22291,22339,22388,22452,22516,22579,22627,22678,22773,22851,22899,22948,23011,23062,23155,23203,23254,23347,23393,23409,23425,23443,23491,23540,23604,23666,23699,23747,23796,23859,23908,23971,24018,24050,24085,24163,24211,24258,24290,24322,24356,24419,24466,24500,24564,24627,24674,24708,24771,24818,24851]
private def paidMenusP9 : Array Nat := #[24899,24948,25014,25113,25250,25283,25332,25397,25474,25508,25569,25585,25603,25650,25682,25714,25745,25762,25795,25843,25892,25959,26068,26129,26146,26177,26195,26244,26306,26337,26353,26369,26389,26470,26562,26598,26694,26788,26849,26865,26889,27027,27076,27139,27189,27269,27348,27411,27457,27473,27490,27522,27557,27638,27730,27763,27810,27844,27905,27924,27987,28035,28082,28115]
private def paidMenusP10 : Array Nat := #[28162,28197,28278,28370,28401,28418,28451,28498,28530,28562,28593,28611,28659,28706,28739,28785,28803,28855,28962,28993,29011,29057,29075,29122,29153,29171,29218,29253,29330,29361,29379,29430,29526,29619,29666,29700,29761,29780,29841,29860,29927,30035,30087,30195,30243,30289,30306,30339,30386,30420,30486,30579,30627,30676,30738,30771,30822,30914,30946,30980,31042,31073,31090,31123]
private def paidMenusP11 : Array Nat := #[31169,31189,31266,31298,31331,31380,31442,31473,31490,31523,31571,31621,31699,31748,31812,31874,31907,31957,32034,32066,32097,32115,32162,32196,32261,32343,32452,32514,32548,32609,32629,32712,32834,32867,32916,32980,33043,33091,33139,33185,33202,33233,33251,33298,33330,33364,33428,33491,33539,33587,33634,33666,33698,33730,33761,33777,33795,33842,33876,33937,33955,34002,34033,34050]
private def paidMenusP12 : Array Nat := #[34082,34113,34129,34146,34179,34227,34273,34291,34337,34354,34385,34404,34467,34516,34580,34642,34675,34726,34818,34852,34917,34996,35058,35092,35155,35203,35253,35332,35394,35426,35462,35559,35668,35732,35794,35828,35893,35972,36036,36098,36129,36145,36163,36211,36261,36339,36387,36435,36482,36515,36564,36628,36690,36723,36772,36836,36898,36931,36981,37060,37124,37187,37235,37284]
private def paidMenusP13 : Array Nat := #[37346,37381,37460,37525,37609,37746,37780,37842,37877,37956,38019,38069,38148,38213,38293,38373,38454,38550,38644,38709,38787,38834,38866,38898,38938,39090,39129,39268,39331,39378,39416,39540,39603,39652,39714,39749]
private def paidMenus : Array (Array Nat) := #[paidMenusP0,paidMenusP1,paidMenusP2,paidMenusP3,paidMenusP4,paidMenusP5,paidMenusP6,paidMenusP7,paidMenusP8,paidMenusP9,paidMenusP10,paidMenusP11,paidMenusP12,paidMenusP13]
private def paidAtP0 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,1,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,3,0,4,5,0,6,7,7,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,8,0,0,0,0,0,0]
private def paidAtP1 : Array Nat := #[0,9,0,0,0,0,4,5,0,0,0,0,10,0,0,0,0,0,0,0,0,10,0,10,10,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,9,0,0,0,0,0,11,0,0,0,0,0,0,0,0,12,0,0,0,0,0,0,0,0]
private def paidAtP2 : Array Nat := #[0,13,0,0,0,0,0,0,0,0,0,0,0,14,15,0,16,17,18,19,20,21,0,22,23,24,25,26,27,28,29,0,30,31,32,33,34,35,36,35,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,0,0,0,0,53,54,0,0]
private def paidAtP3 : Array Nat := #[0,0,0,0,55,56,0,0,57,58,0,0,59,60,61,62,0,0,0,63,64,0,0,0,0,65,0,0,0,0,0,66,67,68,31,0,0,0,69,70,31,71,72,0,73,63,74,0,35,75,76,77,0,78,79,80,0,0,81,82,0,83,57,84]
private def paidAtP4 : Array Nat := #[85,86,87,88,89,38,90,85,91,89,0,0,92,93,0,0,0,0,94,0,0,95,96,0,97,0,0,98,99,100,98,101,0,0,102,103,104,105,0,106,107,0,0,0,108,109,110,111,0,112,113,114,115,0,116,0,0,0,0,117,118,18,119,120]
private def paidAtP5 : Array Nat := #[18,121,0,122,123,0,124,125,125,0,126,121,0,0,0,127,128,129,130,131,132,133,134,121,0,135,136,0,136,137,0,0,0,18,138,0,0,0,0,0,121,139,140,141,142,143,121,144,141,145,146,147,148,5,149,0,150,34,151,0,152,0,153,0]
private def paidAtP6 : Array Nat := #[0,154,155,0,0,0,156,157,0,0,92,158,159,0,160,161,162,0,1,0,163,0,164,165,0,0,0,0,0,0,0,166,167,0,0,168,0,169,170,171,172,173,7,174,0,175,0,176,0,177,178,179,0,0,180,181,0,0,182,0,0,183,184,0]
private def paidAtP7 : Array Nat := #[0,0,64,0,0,0,0,185,0,186,187,188,189,0,190,0,83,0,57,0,0,57,11,191,0,192,193,0,194,195,0,196,197,198,199,0,200,88,188,0,0,201,0,202,203,204,205,204,206,207,0,208,188,0,209,210,0,211,0,0,0,0,0,0]
private def paidAtP8 : Array Nat := #[0,0,0,212,213,0,93,214,0,0,0,215,216,0,0,0,0,0,0,55,0,0,0,0,0,0,217,218,219,219,0,220,0,221,0,221,221,221,0,0,222,221,205,223,224,224,8,221,224,224,225,226,188,0,227,110,0,0,228,0,108,229,0,121]
private def paidAtP9 : Array Nat := #[0,0,0,230,231,232,0,0,0,55,233,0,0,9,234,0,0,0,0,0,9,235,9,9,0,9,236,237,238,0,0,5,0,0,0,239,240,0,0,241,240,0,242,0,0,0,0,243,244,0,0,10,0,0,0,0,245,246,247,248,241,249,250,0]
private def paidAtP10 : Array Nat := #[232,0,251,252,0,0,0,0,0,0,136,0,0,0,0,0,0,188,190,0,0,188,0,0,0,253,0,0,254,255,0,9,256,0,0,0,0,188,0,257,0,0,0,254,0,0,121,258,0,0,0,259,0,0,260,0,0,0,0,0,261,0,0,210]
private def paidAtP11 : Array Nat := #[262,0,263,263,0,0,264,0,0,0,0,263,0,0,265,13,266,267,0,268,269,270,0,0,0,271,0,0,0,272,0,0,0,0,0,0,0,273,274,275,0,276,277,0,0,0,0,0,0,0,0,0,0,0,0,0,278,0,279,280,188,281,0,11]
private def paidAtP12 : Array Nat := #[11,282,283,0,0,284,0,0,0,238,0,285,286,287,0,288,289,0,0,290,125,0,291,292,293,294,295,296,0,108,297,298,299,300,301,302,303,304,305,306,0,307,308,309,310,311,312,0,313,0,314,0,315,316,17,0,317,318,23,0,319,320,321,322]
private def paidAtP13 : Array Nat := #[323,324,0,325,326,0,327,328,329,330,331,332,331,333,334,142,335,336,0,337,338,0,339,0,340,341,338,339,0,342,0,0,338,0,43,121,121,343,0,35,0,121,317,339,0,0,0,0,0,0,344,345,346,105,347,0,0,348,349,350,351,0,0,352]
private def paidAtP14 : Array Nat := #[353,0,354,45,0,355,356,357,0,358,0,359,360,361,362,363,364,365,0,366,367,368,369,370,0,0,50,0,371,372,0,373,0,374,252,0,375,376,377,378,379,380,381,55,382,0,380,0,0,0,0,383,384,385,386,0,55,387,55,388,389,35,55,390]
private def paidAtP15 : Array Nat := #[391,55,392,392,0,0,0,0,386,0,55,393,394,55,0,395,0,0,0,386,0,0,396,0,0,397,384,398,399,396,382,400,401,53,377,317,402,293,0,400,0,403,396,396,404,0,0,396,0,0,405,406,293,0,101,293,0,407,408,377,409,0,0,0]
private def paidAtP16 : Array Nat := #[410,411,0,405,412,55,413,0,389,414,415,416,417,393,418,419,64,0,420,421,422,0,0,423,424,0,425,0,0,0,0,0,426,425,427,428,0,429,430,431,432,83,433,434,435,436,437,0,438,0,439,440,441,442,0,0,0,443,408,444,336,445,0,336]
private def paidAtP17 : Array Nat := #[446,447,448,83,0,101,0,449,450,336,0,451,451,317,452,339,453,454,0,55,386,455,0,0,0,456,457,55,0,0,312,0,0,0,458,459,0,0,0,0,0,0,0,460,461,462,463,459,464,465,466,467,459,468,55,55,469,57,470,21,79,471,380,0]
private def paidAtP18 : Array Nat := #[79,0,0,472,473,474,0,0,55,475,476,477,478,479,480,481,482,474,473,55,0,0,0,483,484,117,485,486,79,487,488,489,490,55,491,0,339,0,35,0,492,462,474,493,55,489,494,386,55,79,0,0,495,495,496,497,498,416,499,500,501,502,503,504]
private def paidAtP19 : Array Nat := #[101,0,0,505,0,0,0,506,507,105,508,293,342,509,510,0,311,511,0,0,512,110,512,350,0,513,514,425,515,516,517,518,519,520,386,521,0,519,522,523,524,0,525,526,527,528,529,530,531,532,533,0,0,304,293,534,431,535,536,537,538,0,539,540]
private def paidAtP20 : Array Nat := #[541,516,542,101,0,0,543,0,544,543,293,545,546,101,101,425,547,548,101,549,0,550,111,339,551,552,553,554,555,293,556,557,0,558,412,0,0,412,0,559,113,560,561,562,457,563,0,412,564,565,564,566,377,312,0,567,568,569,570,570,312,312,557,412]
private def paidAtP21 : Array Nat := #[404,339,377,404,339,404,567,0,390,571,572,573,574,18,575,576,577,129,578,334,334,579,0,580,119,140,580,119,0,121,581,582,583,584,585,121,586,587,0,588,0,121,129,121,129,589,590,0,0,591,592,593,0,0,594,595,0,596,0,0,597,0,0,159]
private def paidAtP22 : Array Nat := #[598,0,599,600,601,602,603,0,0,0,0,0,604,0,605,0,606,607,608,609,0,610,611,612,0,613,614,0,0,0,615,616,617,0,0,618,619,620,621,0,622,623,624,625,179,626,513,627,0,253,0,0,0,0,0,0,628,0,0,629,0,630,630,631]
private def paidAtP23 : Array Nat := #[0,632,64,633,0,64,0,634,635,636,0,637,638,0,180,0,0,639,640,0,641,0,0,350,642,643,644,645,101,646,431,121,647,0,0,648,108,649,650,651,652,0,0,653,654,655,0,209,0,211,0,57,0,656,657,658,659,660,210,94,661,0,662,57]
private def paidAtP24 : Array Nat := #[57,663,0,0,664,665,666,659,667,668,0,669,670,671,672,673,674,675,676,677,678,0,0,0,0,679,680,681,682,683,0,678,55,684,685,686,687,55,544,688,689,690,681,691,692,693,694,199,0,0,695,696,678,697,678,698,693,699,0,700,678,678,701,690]
private def paidAtP25 : Array Nat := #[701,56,0,0,0,0,195,0,0,0,702,668,703,347,704,283,0,253,0,705,0,535,535,0,0,0,0,0,706,707,708,709,0,0,0,710,711,712,0,154,154,154,154,704,0,713,714,715,716,717,718,719,154,713,720,721,0,722,0,0,0,0,0,230]
private def paidAtP26 : Array Nat := #[231,232,0,723,0,0,0,0,0,724,0,685,0,64,56,0,0,0,725,726,727,728,0,729,730,408,731,732,0,408,733,734,735,0,408,638,736,737,738,739,740,723,741,742,743,741,638,744,121,371,252,745,140,746,0,0,242,0,0,747,0,748,0,749]
private def paidAtP27 : Array Nat := #[750,751,752,753,754,755,625,754,756,0,0,252,0,0,757,758,0,0,253,0,759,0,0,252,0,760,761,0,0,0,0,260,0,0,0,0,762,0,763,763,252,0,252,0,747,0,0,274,0,0,764,765,276,0,766,0,0,271,0,0,0,0,0,267]
private def paidAtP28 : Array Nat := #[276,0,767,0,0,0,768,0,0,769,0,770,771,772,0,153,121,0,0,0,257,773,218,121,774,218,286,287,0,0,0,286,0,287,286,775,0,0,0,0,0,0,0,0,0,0,0,0,0,513,0,408,0,0,0,350,0,0,0,0,0,776,0,407]
private def paidAtP29 : Array Nat := #[0,599,0,55,0,0,0,101,101,293,0,101,101,0,513,777,778,0,304,779,780,425,0,425,781,425,408,0,0,782,783,0,55,784,55,0,55,55,55,0,57,0,785,786,311,55,0,293,777,787,777,304,101,543,0,293,101,425,101,408,293,293,101,55]
private def paidAtP30 : Array Nat := #[311,393,0,312,0,0,0,312,407,312,101,312,117,0,293,788,789,0,790,0,121,791,0,21,0,792,793,0,0,0,0,794,795,796,380,0,797,798,0,799,800,801,802,803,804,561,805,334,777,0,806,334,0,0,0,0,0,0,21,0,0,21,807,0]
private def paidAtP31 : Array Nat := #[21,0,396,0,0,396,0,396,0,0,808,809,810,101,0,811,415,812,0,813,439,512,0,523,814,407,815,816,816,817,818,0,819,820,809,312,0,816,0,0,0,821,822,823,824,825,78,824,826,827,828,829,830,831,832,0,833,415,415,0,415,0,0,0]
private def paidAtP32 : Array Nat := #[834,386,835,386,386,55,495,503,506,507,836,837,838,839,840,511,841,842,843,810,515,515,515,844,845,512,523,846,304,847,848,849,0,425,850,851,850,850,412,0,0,0,101,852,425,552,552,552,552,412,853,854,412,412,0,412,0,855,566,0,312,567,0,412]
private def paidAtP33 : Array Nat := #[0,0,0,0,231,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,856,857,858,0,859,0,860,0,861,862,0,816,0,0,567,808,863,407,688,693,689,0,0,864,865,350,723,723,0,866,0,0,408,867,0,723,0,0,0,0,0,0,0,0]
private def paidAtP34 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,824,0,0,311,101,304,425,425,412,0,0,0,0,0,0,0,0,0,0,0]
private def paidAt : Array (Array Nat) := #[paidAtP0,paidAtP1,paidAtP2,paidAtP3,paidAtP4,paidAtP5,paidAtP6,paidAtP7,paidAtP8,paidAtP9,paidAtP10,paidAtP11,paidAtP12,paidAtP13,paidAtP14,paidAtP15,paidAtP16,paidAtP17,paidAtP18,paidAtP19,paidAtP20,paidAtP21,paidAtP22,paidAtP23,paidAtP24,paidAtP25,paidAtP26,paidAtP27,paidAtP28,paidAtP29,paidAtP30,paidAtP31,paidAtP32,paidAtP33,paidAtP34]
private def paidOffset : Nat → Nat
  | 6 => 0
  | 7 => 7
  | 8 => 142
  | 9 => 787
  | 10 => 1829
  | 11 => 2168
  | 12 => 2217
  | 13 => 2222
  | _ => 0
private def paidList (m k i : Nat) : List Nat :=
  if m=253 then
    let off := atSix paidMenus (atSix paidAt (paidOffset k+i))
    (List.range (off % 16)).map (fun j => atSix paidWords (atSix paidItems (off / 16 + j)))
  else []
private def dualTicket (T : Sig) (k : Nat) (ws : List Sig) (code : Nat) : Bool :=
  FourColumnFace.pricedFace (code / 72057594037927936) T k ws (code % 72057594037927936)
private def closeBoth (u : Bool) (T : Sig) (k : Nat) (six paid : List Nat) (ws : List Sig) :=
  if six.any (inlineSix T k ws) || (u && paid.any (dualTicket T k ws)) then [ws] else []
private theorem closeBoth_sound {u T k six paid ws xs} (h : xs ∈ closeBoth u T k six paid ws) :
    Impossible u T k xs.toFinset := by
  unfold closeBoth at h
  split at h
  next e =>
    have same : xs=ws := by simpa only [List.mem_singleton] using h
    subst xs
    rcases Bool.or_eq_true.mp e with old | fresh
    · obtain ⟨w,_,hw⟩ := List.any_eq_true.mp old
      exact inlineSix_sound hw u
    · obtain ⟨hu,pp⟩ := Bool.and_eq_true.mp fresh
      obtain ⟨w,_,hw⟩ := List.any_eq_true.mp pp
      rw [hu]
      exact FourColumnFace.pricedFace_sound hw
  next => simp at h
def nodeVerified (g : Forest) (k i : Nat) :=
  let raw := wiresOf g
  let (num,depth,cw,iw,pw,offw,lw,data) := g.levels k
  let (ops,bank,ws) := readNode g k i
  let values := ws.map Prod.fst
  let rules := (forestHints (g.levels k) raw.length i).filterMap (fun (a,b) => buildRule g ops depth bank a b)
  let ls := fun tag query => ((g.index k tag).bind (linkedSet g (k-1))).toList ++ closeBoth g.mode (targetOf g) (k-1) (inlineMenu g.mask k i) (paidList g.mask k i) query
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
  · intro tag query xs hx
    rcases List.mem_append.mp hx with old | extra
    · have e : ((g.index k tag).bind (linkedSet g (k-1)))=some xs := by simpa using old
      obtain ⟨pair,_,h⟩ := Option.bind_eq_some_iff.mp e
      exact linkedSet_sound g _ names (prior (by omega)) h
    · exact closeBoth_sound extra



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
    (hfl : ∀ tag ys, fl tag=some ys → ∀ query, ∃ xs ∈ c.2.2.2.2.2 tag query, ys=xs.map BitVec.toNat)
    (hi : i<c.2.2.1.length) (hj : j<c.2.2.1.length) (hij : i≠j) (h : linkAt fl (laneOf c) i j op ka kb=true) :
    (c.2.2.2.2.2 (keySet (choiceVal (movedChoice op (contextWire c i) (contextWire c j)) ::
      (delTwo c.2.2.1 (contextWire c i) (contextWire c j) ka kb).map Prod.fst)) (choiceVal (movedChoice op (contextWire c i) (contextWire c j)) ::
      (delTwo c.2.2.1 (contextWire c i) (contextWire c j) ka kb).map Prod.fst)).any (sameWords
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
    obtain ⟨xs,hx,rfl⟩ := hfl t ys hf (choiceVal (movedChoice op a b) :: (delTwo c.2.2.1 a b ka kb).map Prod.fst)
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
    (hfl : ∀ tag ys, fl tag=some ys → ∀ query, ∃ xs ∈ c.2.2.2.2.2 tag query, ys=xs.map BitVec.toNat)
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
    (hfl : ∀ tag ys, fl tag=some ys → ∀ query, ∃ zs ∈ xs[q].2.2.2.2.2 tag query, ys=zs.map BitVec.toNat)
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
    (hfl : ∀ tag ys, fl tag=some ys → ∀ query, ∃ zs ∈ xs[q].2.2.2.2.2 tag query, ys=zs.map BitVec.toNat)
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
    (hfl : ∀ tag ys, fl tag=some ys → ∀ query, ∃ zs ∈ xs[q].2.2.2.2.2 tag query, ys=zs.map BitVec.toNat)
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
  let ls := fun tag query => ((g.index k tag).bind (linkedSet g (k-1))).toList ++ closeBoth g.mode (targetOf g) (k-1) (inlineMenu g.mask k i) (paidList g.mask k i) query
  (k,ws.length,ws,preCov g.mode ws,rules,ls)


theorem flOf_ok (g : Forest) (k i tag : Nat) (ys) (h : flOf g k tag=some ys) (query : List Sig) :
    ∃ xs ∈ (contextOf g k i).2.2.2.2.2 tag query, ys=xs.map BitVec.toNat := by
  suffices old : ∃ xs ∈ ((g.index k tag).bind (linkedSet g (k-1))).toList, ys=xs.map BitVec.toNat by
    obtain ⟨xs,mem,eq⟩ := old
    exact ⟨xs,List.mem_append_left _ mem,eq⟩
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
  have hfl : ∀ tag ys, flOf g k tag=some ys → ∀ query, ∃ zs ∈ xs[q].2.2.2.2.2 tag query, ys=zs.map BitVec.toNat := by
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

def target (x : Fin 8 → Bool) : Bool := decide (∃ i < ([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)
def smallCircuit : Circuit := ⟨[⟨.or,[1,6]⟩,⟨.or,[6,7]⟩,⟨.or,[0,2]⟩,⟨.or,[4,10]⟩,⟨.or,[3,5]⟩,⟨.or,[2,8]⟩,⟨.or,[3,8]⟩,⟨.or,[4,7]⟩,⟨.or,[0,9]⟩,⟨.and,[15,13]⟩,⟨.and,[16,12]⟩,⟨.and,[14,5]⟩,⟨.and,[9,11]⟩,⟨.or,[17,18]⟩,⟨.or,[21,19]⟩,⟨.or,[22,20]⟩], 23⟩

theorem witnessMonotone : ∀ g ∈ smallCircuit.gates,
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [smallCircuit,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact ⟨Or.inl rfl,by decide⟩ | exact ⟨Or.inr rfl,by decide⟩

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem witnessCorrect : ∀ x : Fin 8 → Bool, smallCircuit.eval (List.ofFn x) = target x := by
  decide +kernel

theorem witnessSize : smallCircuit.gates.length = 16 := rfl

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

def lowRow (i : Fin 8) : Row := Fin.ofNat 512 (1 <<< ([3, 4, 4, 0, 1, 0, 0, 0] : List Nat).getD i.val 0)
def highRow (i : Fin 8) : Row := Fin.ofNat 512 ((1 <<< i.val) ||| (1 <<< ([3, 4, 4, 0, 1, 0, 0, 0] : List Nat).getD i.val 0))

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
    (lower : Impossible true graph 14 sevenInputs.toFinset) (gates : List Gate) (o : Nat)
    (fit : ∀ g ∈ gates, (g.op=GateOp.and ∨ g.op=GateOp.or ∨ g.op=GateOp.not) ∧ g.inputs.length≤2)
    (correct : ∀ x : Fin 8 → Bool, (Circuit.mk gates o).eval (List.ofFn x)=target x) :
    ∃ (gs : List Gate) (out : Nat), (∀ g ∈ gs, (g.op=GateOp.and ∨ g.op=GateOp.or) ∧ g.inputs.length≤2) ∧
       gs.length≤gates.length ∧ ∀ x : Fin 8 → Bool, (Circuit.mk gs out).eval (List.ofFn x)=target x := by
  classical
  by_cases big : 16 ≤ gates.length
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
theorem g41P3_0 : block g41 3 0 1=true := by
  apply cellsBlock (ar:=3) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g41B3 : block g41 3 0 1=true := g41P3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g41T : checkedTables g41 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g41 0 0 0 = true)
  · exact (rfl : block g41 1 0 0 = true)
  · exact (rfl : block g41 2 0 0 = true)
  · exact g41B3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g41G : graphValid g41 (boundsBefore []) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low41 : Lower true (varsX 41) (graphGoal 41) 4 := lower_forest (g:=g41) (i:=0) (hints:=3) (before_sound [] baseKnown) g41G g41T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K41 := extendKnown [] 4 [(41,[]),(73,[101]),(84,[32,16,67,101]),(97,[83,67,100]),(104,[48,16,33,82,66,100]),(137,[117,101]),(148,[32,16,67,117,101]),(161,[83,67,116,100]),(168,[48,16,33,82,66,116,100]),(193,[99,67,117]),(200,[48,16,33,98,66,117]),(208,[64,16,33,99,117]),(224,[80,16,33,99,66,116])]
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
theorem g43G : graphValid g43 (boundsBefore K41) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low43 : Lower true (varsX 43) (graphGoal 43) 5 := lower_forest (g:=g43) (i:=0) (hints:=83) (before_sound K41 V41) g43G g43T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K43 := extendKnown K41 5 [(77,[33,101]),(85,[32,16,67,101]),(89,[65,33,101]),(92,[32,49,65,101]),(113,[65,33,83,99]),(116,[32,81,67,49,99]),(120,[48,65,32,82,98]),(149,[32,16,67,117,101]),(153,[65,33,117,101]),(156,[32,49,65,117,101]),(177,[65,33,83,115,99]),(180,[32,81,67,49,115,99]),(184,[48,65,32,82,114,98])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V43 : Known true K43 := extend_ok (m:=43) V41 low43 (by decide +kernel)
def g105Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xdf7ec03c3ffe0fbefd,0x80787ffc1f7dfb00f0ff])),(BitVec.ofNat 152 (word80 [0x820404444444210408,0x8888888420810111111]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x1fbf43c3c3fff03f7e,0x878787ffe07efd0f0f0f])),(BitVec.ofNat 152 (word80 [0x40808888888420810,0x11111110841020222222]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xe03fbc03fc3fffc07f,0x7807f87fff80fef00ff0])),(BitVec.ofNat 152 (word80 [0x81011111110841020,0x22222221082040444444]))),((BitVec.ofNat 152 (word80 [0xffc03ffc003fffff80,0x7ff8007fffff00fff000])),(BitVec.ofNat 152 (word80 [0x102022222221082040,0x44444442104080888888]))),(0x0,0x0),(0x0,0x0)]
def g105C : List ColumnInfo := [(1,0,104,0,4),(8,0,97,0,4),(32,0,73,0,4),(64,0,41,0,4)]
def g105A : List (List Nat) := [[],[101],[83],[83,99],[99,83],[99],[48],[48,101],[48,80],[48,80,96],[48,96,80],[48,96],[80,48],[80,48,99],[80],[80,96],[80,99],[80,99,48],[96,48,83],[96,48],[96,80],[96],[96,83,48],[96,83]]
def g105D3 := limbs80 #[#[0x23ea6a1221e12148110,0x8028]]
def g105D4 := limbs80 #[#[0x2fd0910bd42443e48110,0x609085870]]
def g105H4 (j : Nat) := if j=0 then 0x20000200 else 0
def g105D5 (j : Nat) := if j=0 then 0xd1027d10 else 0
def g105H5 := limbs80 #[#[0x7c8400000800000001e2,0x10c02280000000088000,0x6]]
def g105D6 (j : Nat) := if j=0 then 0x3904f else 0
def g105H6 := limbs80 #[#[0x9000000000000000000,0xc0000400016800025000]]
def g105L : Nat → Packing
  | 3 => (2,3,2,0,0,5,0,g105D3)
  | 4 => (3,2,2,0,0,5,0,g105D4)
  | 5 => (1,1,2,0,0,0,0,g105D5)
  | 6 => (1,0,2,0,0,0,0,g105D6)
  | _ => emptyPacking
def g105I : Nat → Nat → Option (Nat × Nat)
  | 4 => lookupShort 1 11 0 3 1 0 g105H4
  | 5 => lookupShort 2 23 1 7 2 3 g105H5
  | 6 => lookupShort 1 23 0 7 0 5 g105H6
  | _ => fun _ => none
def g105 : Forest := ⟨105,6,fun i => g105Y[i]?.getD (0,0),g105C,g105A,g105L,g105I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g105P3_0 : block g105 3 0 2=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g105B3 : block g105 3 0 2=true := g105P3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g105P4_0 : block g105 4 0 3=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g105B4 : block g105 4 0 3=true := g105P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g105P5_0 : block g105 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g105B5 : block g105 5 0 1=true := g105P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g105P6_0 : block g105 6 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g105B6 : block g105 6 0 1=true := g105P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g105T : checkedTables g105 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g105 0 0 0 = true)
  · exact (rfl : block g105 1 0 0 = true)
  · exact (rfl : block g105 2 0 0 = true)
  · exact g105B3
  · exact g105B4
  · exact g105B5
  · exact g105B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g105G : graphValid g105 (boundsBefore K43) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low105 : Lower true (varsX 105) (graphGoal 105) 7 := lower_forest (g:=g105) (i:=0) (hints:=3) (before_sound K43 V43) g105G g105T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K105 := extendKnown K43 7 [(105,[]),(169,[118]),(201,[101,117]),(212,[32,16,67,101,117]),(225,[83,67,100,116]),(232,[48,16,33,82,66,100,116])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V105 : Known true K105 := extend_ok (m:=105) V43 low105 (by decide +kernel)
def g150Y : Array (Bits × Bits) := #[(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfe7d01c7fc0fc7cfe7,0xd01c7fc0fc7cfe7d01c7])),(BitVec.ofNat 152 (word80 [0x51d124928a290a051,0xd124928a290a051d1249]))),((BitVec.ofNat 152 (word80 [0x3f8b8e38fff007f3f8,0xb8e38fff007f3f8b8e38])),(BitVec.ofNat 152 (word80 [0x884b924930c3210884,0xb924930c3210884b9249]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x3fe7703ffffff803fe,0x7703ffffff803fe7703f])),(BitVec.ofNat 152 (word80 [0x100024924104020100,0x2492410402010002492]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xc018ffc0fffffffc01,0x8ffc0fffffffc018ffc0])),(BitVec.ofNat 152 (word80 [0x200049248208040200,0x4924820804020004924]))),(0x0,0x0)]
def g150C : List ColumnInfo := [(2,0,148,0,4)]
def g150A : List (List Nat) := [[],[116],[33],[33,116]]
def g150D4 (j : Nat) := if j=0 then 0x1f else 0
def g150L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,g150D4)
  | _ => emptyPacking
def g150I (_ _ : Nat) : Option (Nat × Nat) := none
def g150 : Forest := ⟨150,4,fun i => g150Y[i]?.getD (0,0),g150C,g150A,g150L,g150I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g150P4_0 : block g150 4 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g150B4 : block g150 4 0 1=true := g150P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g150T : checkedTables g150 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g150 0 0 0 = true)
  · exact (rfl : block g150 1 0 0 = true)
  · exact (rfl : block g150 2 0 0 = true)
  · exact (rfl : block g150 3 0 0 = true)
  · exact g150B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g150G : graphValid g150 (boundsBefore K105) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low150 : Lower true (varsX 150) (graphGoal 150) 5 := lower_forest (g:=g150) (i:=0) (hints:=268502080) (before_sound K105 V105) g150G g150T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K150 := extendKnown K105 5 [(209,[16,66,50,99,83]),(216,[49,66,98,82]),(240,[65,82,49,99])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V150 : Known true K150 := extend_ok (m:=150) V105 low150 (by decide +kernel)
def g61Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xc00fff0ffffffc00ff,0xfff0fffeea3a5303f03f])),(BitVec.ofNat 152 (word80 [0x84a08a210802284a02,0x80220882200a53145145]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfff0000ffc3fffff00,0x3fffffc009adfd000fc0])),(BitVec.ofNat 152 (word80 [0xc42c405090b10c4b,0x11404108092d994d34d3]))),((BitVec.ofNat 152 (word80 [0xfffffff0003fffffff,0xc000fffd77e88afc003f])),(BitVec.ofNat 152 (word80 [0x90130026104c0100c,0x584120152a08828a28a]))),((BitVec.ofNat 152 (word80 [0x3fffffff,0xffff00012697f4000fc0])),(BitVec.ofNat 152 (word80 [0x2e09c08b8227026090,0x26009c11269264b2cb2c]))),((BitVec.ofNat 152 (word80 [0xffffffffffc0000000,0x39d530dfff000])),(BitVec.ofNat 152 (word80 [0x300e000c00380380e0,0x3808e0208d5104c30c30]))),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g61C : List ColumnInfo := [(0,4,41,16,5)]
def g61A : List (List Nat) := [[],[83],[66],[66,83],[48],[48,80],[48,66],[48,66,80],[80,48],[80],[80,66,48],[80,66]]
def g61D5 (j : Nat) := if j=0 then 0x3f else 0
def g61L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,g61D5)
  | _ => emptyPacking
def g61I (_ _ : Nat) : Option (Nat × Nat) := none
def g61 : Forest := ⟨61,5,fun i => g61Y[i]?.getD (0,0),g61C,g61A,g61L,g61I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g61P5_0 : block g61 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g61B5 : block g61 5 0 1=true := g61P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g61T : checkedTables g61 5 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g61 0 0 0 = true)
  · exact (rfl : block g61 1 0 0 = true)
  · exact (rfl : block g61 2 0 0 = true)
  · exact (rfl : block g61 3 0 0 = true)
  · exact (rfl : block g61 4 0 0 = true)
  · exact g61B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g61G : graphValid g61 (boundsBefore K150) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low61 : Lower true (varsX 61) (graphGoal 61) 6 := lower_forest (g:=g61) (i:=0) (hints:=132099) (before_sound K150 V150) g61G g61T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K61 := extendKnown K150 6 [(61,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V61 : Known true K61 := extend_ok (m:=61) V150 low61 (by decide +kernel)
def g93Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xffc01ff87fc3fff00,0xffff1ffed2e680007c1f])),(BitVec.ofNat 152 (word80 [0x222894451108808a4a,0xa02444252268a5294a5]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffe0007ffc3ffff,0xffffe11773400f83e0])),(BitVec.ofNat 152 (word80 [0x40b018162050082c0c,0x2c140089146346318c63]))),((BitVec.ofNat 152 (word80 [0xffffffff80003ffff,0xff001ffce8f541f0001f])),(BitVec.ofNat 152 (word80 [0x84c120980261113010,0x30588900a8d154a5294a]))),((BitVec.ofNat 152 (word80 [0xf0000000000003ffff,0xffffe0005f98fe0003e0])),(BitVec.ofNat 152 (word80 [0x701c0e0438221c060,0x40600e104b9898c6318c]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffffffffffc0000,0x3280bbffffc00])),(BitVec.ofNat 152 (word80 [0x80201000400020080,0x80801000000021084210]))),(0x0,0x0),(0x0,0x0)]
def g93C : List ColumnInfo := [(1,0,92,0,5),(4,0,89,0,5),(8,0,85,0,5),(16,0,77,0,5),(9,0,84,0,4),(20,0,73,0,4)]
def g93A : List (List Nat) := [[],[66],[32,67],[32,48,64],[48],[48,66],[64,32,50],[64,50]]
def g93D4 := limbs80 #[#[0x9bd89544426d6215110,0x31825f635474]]
def g93D5 := limbs80 #[#[0x3527f7bbf6f4050110,0x5f405d50654155045435,0x66ad0941001546b525d4,0xc08024050462b13e3bb,0x4040201642000001201]]
def g93H5 := limbs80 #[#[0x0,0x110006000000,0x2200000080000,0x0,0x0,0x900000000000]]
def g93D6 := limbs80 #[#[0x540a0380ff40fd40fd10,0x3140cc503]]
def g93H6 := limbs80 #[#[0x8300008021d1e45,0x30206001759c10088490,0x40000008500009447009,0x4]]
def g93D7 (j : Nat) := if j=0 then 0x1605f else 0
def g93H7 := limbs80 #[#[0x944000000002cec01473,0x54e80a0281096]]
def g93L : Nat → Packing
  | 4 => (3,3,3,0,0,4,0,g93D4)
  | 5 => (10,2,3,262147,34,7,1030,g93D5)
  | 6 => (3,1,3,0,0,6,0,g93D6)
  | 7 => (1,0,3,0,0,0,0,g93D7)
  | _ => emptyPacking
def g93I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupShort 1 83 0 6 2 2 g93H5
  | 6 => lookupShort 4 29 3 8 4 2 g93H6
  | 7 => lookupShort 3 19 2 7 2 3 g93H7
  | _ => fun _ => none
def g93 : Forest := ⟨93,7,fun i => g93Y[i]?.getD (0,0),g93C,g93A,g93L,g93I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g93P4_0 : block g93 4 0 3=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g93B4 : block g93 4 0 3=true := g93P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g93P5_0 : block g93 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g93P5_1 : block g93 5 1 9=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g93B5 : block g93 5 0 10=true := (@block_merge g93 5 0 1 9 g93P5_0 g93P5_1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g93P6_0 : block g93 6 0 3=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g93B6 : block g93 6 0 3=true := g93P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g93P7_0 : block g93 7 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g93B7 : block g93 7 0 1=true := g93P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g93T : checkedTables g93 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g93 0 0 0 = true)
  · exact (rfl : block g93 1 0 0 = true)
  · exact (rfl : block g93 2 0 0 = true)
  · exact (rfl : block g93 3 0 0 = true)
  · exact g93B4
  · exact g93B5
  · exact g93B6
  · exact g93B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g93G : graphValid g93 (boundsBefore K61) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low93 : Lower true (varsX 93) (graphGoal 93) 8 := lower_forest (g:=g93) (i:=0) (hints:=132099) (before_sound K61 V61) g93G g93T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K93 := extendKnown K61 8 [(93,[]),(117,[83]),(124,[32,16,49,65,81]),(157,[118]),(181,[83,118]),(188,[32,16,49,65,81,118])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V93 : Known true K93 := extend_ok (m:=93) V61 low93 (by decide +kernel)
def g107Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfe1ff01ff1ffffc03f,0xe1fe1fffd19d300f00ff])),(BitVec.ofNat 152 (word80 [0x1440a140a408028281,0x44044008018931111111]))),((BitVec.ofNat 152 (word80 [0x1fffe001fc7fffc0,0x1ffe1fc4d3aa0000f00])),(BitVec.ofNat 152 (word80 [0x5892c192c8514b2325,0x892805114d3aabbbbbbb]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x1ffffffe007fffff,0xfe0001ffbe1b40f0f00f])),(BitVec.ofNat 152 (word80 [0x6103020300620c0406,0x3088203e1002222222]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffe0000000007fffff,0xfffffe000be08f00fff0])),(BitVec.ofNat 152 (word80 [0x800404040080100808,0x400040000004444444]))),((BitVec.ofNat 152 (word80 [0xffffffffffff800000,0x6446ffff0000])),(BitVec.ofNat 152 (word80 [0x1808180100603030,0x118111824046c8888888]))),(0x0,0x0),(0x0,0x0)]
def g107C : List ColumnInfo := [(2,0,105,0,7)]
def g107A : List (List Nat) := [[],[99],[48],[48,96],[96,48],[96]]
def g107D7 (j : Nat) := if j=0 then 0x3f else 0
def g107L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g107D7)
  | _ => emptyPacking
def g107I (_ _ : Nat) : Option (Nat × Nat) := none
def g107 : Forest := ⟨107,7,fun i => g107Y[i]?.getD (0,0),g107C,g107A,g107L,g107I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g107P7_0 : block g107 7 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g107B7 : block g107 7 0 1=true := g107P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g107T : checkedTables g107 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g107 0 0 0 = true)
  · exact (rfl : block g107 1 0 0 = true)
  · exact (rfl : block g107 2 0 0 = true)
  · exact (rfl : block g107 3 0 0 = true)
  · exact (rfl : block g107 4 0 0 = true)
  · exact (rfl : block g107 5 0 0 = true)
  · exact (rfl : block g107 6 0 0 = true)
  · exact g107B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g107G : graphValid g107 (boundsBefore K93) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low107 : Lower true (varsX 107) (graphGoal 107) 8 := lower_forest (g:=g107) (i:=0) (hints:=83) (before_sound K93 V93) g107G g107T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K107 := extendKnown K93 8 [(109,[33,101]),(121,[65,33,101]),(185,[65,33,117,101])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V107 : Known true K107 := extend_ok (m:=107) V93 low107 (by decide +kernel)
def g171Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xff0ff01fe3f8ffe0,0x3fc7f1ffd675000f00ff])),(BitVec.ofNat 152 (word80 [0xa0a20a14148120142,0x82902402163411111111]))),((BitVec.ofNat 152 (word80 [0xff000fffe003ff1fff,0xc007fe3f317a00f00f00])),(BitVec.ofNat 152 (word80 [0x2c2c42c18590a04583,0xb214084b17a33333333]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffc001fff,0xfff8003fede10f00f00f])),(BitVec.ofNat 152 (word80 [0x303083020600c48604,0xc01890829c122222222]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffff0000000001fff,0xffffffc01388f000fff0])),(BitVec.ofNat 152 (word80 [0x404004040801000808,0x10020010000044444444]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffffffffffe000,0x2816ffff0000])),(BitVec.ofNat 152 (word80 [0x808008081002001010,0x20040020000088888888]))),(0x0,0x0)]
def g171C : List ColumnInfo := [(2,0,169,0,7)]
def g171A : List (List Nat) := [[],[117],[48],[48,117]]
def g171D7 (j : Nat) := if j=0 then 0x3f else 0
def g171L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g171D7)
  | _ => emptyPacking
def g171I (_ _ : Nat) : Option (Nat × Nat) := none
def g171 : Forest := ⟨171,7,fun i => g171Y[i]?.getD (0,0),g171C,g171A,g171L,g171I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g171P7_0 : block g171 7 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g171B7 : block g171 7 0 1=true := g171P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g171T : checkedTables g171 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g171 0 0 0 = true)
  · exact (rfl : block g171 1 0 0 = true)
  · exact (rfl : block g171 2 0 0 = true)
  · exact (rfl : block g171 3 0 0 = true)
  · exact (rfl : block g171 4 0 0 = true)
  · exact (rfl : block g171 5 0 0 = true)
  · exact (rfl : block g171 6 0 0 = true)
  · exact g171B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g171G : graphValid g171 (boundsBefore K107) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low171 : Lower true (varsX 171) (graphGoal 171) 8 := lower_forest (g:=g171) (i:=0) (hints:=83) (before_sound K107 V107) g171G g171T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K171 := extendKnown K107 8 [(205,[33,101]),(213,[32,16,67,101]),(217,[65,33,101]),(220,[32,49,65,101]),(236,[48,33,16,81,65,100]),(241,[65,33,83,99]),(244,[32,81,67,49,99]),(248,[48,65,32,82,98])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V171 : Known true K171 := extend_ok (m:=171) V107 low171 (by decide +kernel)
def g233Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xc0fc0fc0fdf81fbf7f,0x3f7efec0007c00f83ff])),(BitVec.ofNat 152 (word80 [0x820820820810410202,0x8204040210842108421]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xff000fff01ffe03fbf,0xfc07f7f400f801f07c1f])),(BitVec.ofNat 152 (word80 [0x41041041020820404,0x10408080421084210842]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffff00001ffffc03f,0xfff807f81f003e007fe0])),(BitVec.ofNat 152 (word80 [0x82082082041040808,0x20810100842108421084]))),((BitVec.ofNat 152 (word80 [0xfffffffffe0000003f,0xfffff803e0003fff8000])),(BitVec.ofNat 152 (word80 [0x104104104082081010,0x41020201084210842108]))),((BitVec.ofNat 152 (word80 [0xffffffffffffffffc0,0x3ffffc0000000])),(BitVec.ofNat 152 (word80 [0x208208208104102020,0x82040402108421084210]))),(0x0,0x0)]
def g233C : List ColumnInfo := [(1,0,232,0,7),(8,0,225,0,7),(32,0,201,0,7),(64,0,169,0,7),(128,0,105,0,7),(9,0,224,0,4),(33,0,200,0,4),(40,0,193,0,4),(65,0,168,0,4),(72,0,161,0,4),(96,0,137,0,4)]
def g233A : List (List Nat) := [[],[118],[101],[101,117],[117,101],[117],[83],[83,118],[83,99],[83,99,115],[83,115,99],[83,115],[99,83],[99,83,117],[99],[99,115],[99,117],[99,117,83],[115,83,101],[115,83],[115,99],[115],[115,101,83],[115,101],[48],[48,118],[48,101],[48,101,117],[48,117,101],[48,117],[48,80],[48,80,118],[48,80,96],[48,80,96,112],[48,80,112,96],[48,80,112],[48,96,80],[48,96,80,117],[48,96],[48,96,112],[48,96,117],[48,96,117,80],[48,112,80,101],[48,112,80],[48,112,96],[48,112],[48,112,101,80],[48,112,101],[80,48],[80,48,118],[80,48,99],[80,48,99,115],[80,48,115,99],[80,48,115],[80],[80,118],[80,96],[80,96,112],[80,112,96],[80,112],[80,99],[80,99,115],[80,99,48],[80,99,48,112],[80,99,112,48],[80,99,112],[80,115,99],[80,115],[80,115,48,96],[80,115,48],[80,115,96],[80,115,96,48],[96,48,83],[96,48,83,117],[96,48],[96,48,115],[96,48,117],[96,48,117,83],[96,80],[96,80,117],[96],[96,112],[96,117],[96,117,80],[96,83,48],[96,83,48,115],[96,83],[96,83,112],[96,83,115],[96,83,115,48],[96,115,80,83],[96,115,80],[96,115,83],[96,115,83,80],[96,115],[96,115,48],[112,48,83,101],[112,48,83],[112,48,99],[112,48],[112,48,101,83],[112,48,101],[112,80,101],[112,80],[112,96],[112],[112,101,80],[112,101],[112,83,48,99],[112,83,48],[112,83,96],[112,83],[112,83,99,48],[112,83,99],[112,99,80],[112,99,80,83],[112,99,83,80],[112,99,83],[112,99,48],[112,99]]
def g233D3 := limbs80 #[#[0x887805915350d2148110,0x4180360709aa26498a40,0x2]]
def g233D4 := limbs80 #[#[0x54d214811050d2148110,0x4c93148110d4d2148110,0xd9131481105093148110,0xdc1654c9105d9544c910,0xf83d0e632cc3ad8ad21e,0x5c21bb21ab214c28ca98,0xea1cdaa3caa34c22bb22,0x440063a71c069ba52c1d,0xaedcb668c676cd5a3364,0x10100800040a0a0480b,0x32100a42c04000000]]
def g233H4 := limbs80 #[#[0x804c4000000023000000,0x30d]]
def g233D5 := limbs80 #[#[0x481104c5204412148110,0x443534811054d2044143,0x59532441604c91055132,0x54910d5132442654c910,0x443635491058d5244153,0x3ef55eadd3e3f0f58f52,0x54c3f1f0ee76bb1bccf6,0xd50c03747c4c8675309,0x541b55075721d5087553,0xd772345d4a364185906f,0x91137437d90dd643adc8,0x1dd9457658585917447d,0x473dc9c57696d924d729,0x77476dd1d87477dc1cb7,0x30b74b3dca8576835ca0,0xa8fc6e2309800774d15d,0x25b2ad3e9546a14e46a2,0xf1b89bfde8ec703619cc,0xafd71b4d72a1459ecd64,0x8020905ddecf579ec8e1,0x1800a9204000773d2060,0x17023b40503212040128,0xc00fc04879703003f602,0xcc0980990a0200017b88,0x9aa1b0100b210040480,0x41b2160200009b0d9080,0xd05682c0401682003]]
def g233H5 := limbs80 #[#[0xe3c8e383420eba271043,0x2a02c000001c71e30678,0x606883d00000000004c,0x20640000c920263,0xa4941000032800006b0,0x32334970c30004a9e,0xf1c380c0011830001004,0x30304b810e0140123878,0x491b0dd86260a3e187,0x2c4a00f8050f980,0x10158cb001e4090c20,0x3180000000,0xe000000000804000201a,0x400000000011c99e15b1,0xb98080001eb000000312,0x1a00000012370ce000c9,0x25078302000000303003,0xd]]
def g233D6 := limbs80 #[#[0xd4910549104c91048110,0x624484fefcf8dfdebf9f,0x163c6c705955a989532a,0x57aa2d5472c0e54cca18,0xc7358e3b1cd539ccab59,0x90c732f920782a0c801e,0xcce470e823bdb2c35827,0x84090e4b0610cce905a2,0xa13490a9f32904240e82,0x94010e8067802b9cd81d,0xa7c8253f046f920b6e18,0x67812147c4a79414be04,0x884a608b854340578086,0x39024f]]
def g233H6 := limbs80 #[#[0x602050b010000030200,0x2e1b0013158d011a0e01,0x2c0b031d195e170f1608,0x5400800009a290052686,0x62f3888000de280000da,0xc0130058000470c40218,0x27804018808c0c04190,0x57688a68d0000007000,0x1874338307134f140,0x60000d91800000000000,0xf0704740020001007e68,0xc04b004b0d161c1d90e9,0x140064d1c0002647010c,0x4f0c6401b0f038e0305,0x8b044d003a7850d0e0,0x301c0400a48700006048,0x7293e020004044844768,0x4c9e8c000000000c38b8,0x4b988f,0x18561850000000000,0x830203580004790803a0,0x8a30b92151e2e264009a,0x1276450000c029f32900,0x8007835f3c3a01966198,0x328c469000343d1690b,0x8730e5a0a00016005c02,0x41b20001020c00f120f9,0x6c0240000000160e2001,0x693e2c02083149a2f04,0x42813f1e4454800308,0x400e803d32180000004]]
def g233D7 := limbs80 #[#[0x7f52442faa4887e48110,0x3015007f54910fe99221,0x94301030ba6694235a3f,0xa5011a6690a20e30ba66,0x38da6690a3c8a142a70,0x4]]
def g233H7 := limbs80 #[#[0x808cd0a5444040300421,0x8a30287180003c680004,0x21878088000000000181,0x5c00000010108784011,0x74268400015120006,0x0,0x3c5a106808070e9c4000,0x24e00e00021c2000001e,0x140600004090017c0144,0x2687c0380120130019ca,0x190000400c00020061c1,0x11011ed04835600aa40a,0xa0000001984a01a00020,0x71070786080013c4e04,0x4f19c2621100058000,0x8000000000082100000,0x4043a0d6000601d1e,0xc8400000508610000000,0x1501220080004002821a,0x360e00001049a42f]]
def g233D8 (j : Nat) := if j=0 then 0x2d2720806fd10 else 0
def g233H8 := limbs80 #[#[0xc000021b08111003149,0x20000000000000008,0x2e00000000000000003,0x2120000000000c40000,0x82c00c03d00,0x880000000c0400810000,0x840000324000004]]
def g233D9 (j : Nat) := if j=0 then 0x219080bf else 0
def g233H9 := limbs80 #[#[0x20c00a10000000092f28,0x67800000000000000000,0x636b000000,0x4915400]]
def g233L : Nat → Packing
  | 3 => (2,6,4,0,0,5,0,g233D3)
  | 4 => (14,5,4,524296,51,7,1029,g233D4)
  | 5 => (38,4,4,917518,68,9,1043,g233D5)
  | 6 => (18,3,4,458756,50,9,1046,g233D6)
  | 7 => (5,2,4,0,0,8,0,g233D7)
  | 8 => (1,1,4,0,0,0,0,g233D8)
  | 9 => (1,0,4,0,0,0,0,g233D9)
  | _ => emptyPacking
def g233I : Nat → Nat → Option (Nat × Nat)
  | 4 => lookupShort 1 11 0 10 1 7 g233H4
  | 5 => lookupShort 16 101 4 13 4 7 g233H5
  | 6 => lookupShort 30 149 8 15 6 7 g233H6
  | 7 => lookupShort 17 107 5 14 5 7 g233H7
  | 8 => lookupShort 4 67 1 10 3 5 g233H8
  | 9 => lookupShort 2 29 3 9 0 7 g233H9
  | _ => fun _ => none
def g233 : Forest := ⟨233,9,fun i => g233Y[i]?.getD (0,0),g233C,g233A,g233L,g233I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g233P3_0 : block g233 3 0 2=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g233B3 : block g233 3 0 2=true := g233P3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g233P4_0 : block g233 4 0 14=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g233B4 : block g233 4 0 14=true := g233P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g233P5_0 : block g233 5 0 4=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g233P5_4 : block g233 5 4 34=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g233B5 : block g233 5 0 38=true := (@block_merge g233 5 0 4 34 g233P5_0 g233P5_4)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g233P6_0 : block g233 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g233P6_1 : block g233 6 1 6=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g233P6_7 : block g233 6 7 11=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g233B6 : block g233 6 0 18=true := (@block_merge g233 6 0 1 17 g233P6_0 (@block_merge g233 6 1 6 11 g233P6_1 g233P6_7))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g233P7_0 : block g233 7 0 3=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g233P7_3 : block g233 7 3 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g233B7 : block g233 7 0 5=true := (@block_merge g233 7 0 3 2 g233P7_0 g233P7_3)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g233P8_0 : block g233 8 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g233B8 : block g233 8 0 1=true := g233P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g233P9_0 : block g233 9 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g233B9 : block g233 9 0 1=true := g233P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g233T : checkedTables g233 9 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g233 0 0 0 = true)
  · exact (rfl : block g233 1 0 0 = true)
  · exact (rfl : block g233 2 0 0 = true)
  · exact g233B3
  · exact g233B4
  · exact g233B5
  · exact g233B6
  · exact g233B7
  · exact g233B8
  · exact g233B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g233G : graphValid g233 (boundsBefore K171) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low233 : Lower true (varsX 233) (graphGoal 233) 10 := lower_forest (g:=g233) (i:=0) (hints:=3) (before_sound K171 V171) g233G g233T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K233 := extendKnown K171 10 [(233,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V233 : Known true K233 := extend_ok (m:=233) V171 low233 (by decide +kernel)
def g125Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x1fffff87fff6a323,0xb48680000007f01fc07f])),(BitVec.ofNat 152 (word80 [0x9402801102206a022,0xa082850a142850a14285]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffe003ffffff0205ed,0x63cb000003f800003f80])),(BitVec.ofNat 152 (word80 [0x2184b08a010422056d,0x224b13264c993264c993]))),((BitVec.ofNat 152 (word80 [0xfffffc0007fffb1ad1,0x92518001fc000fe0007f])),(BitVec.ofNat 152 (word80 [0x200c02c20480912d1,0x12400a142850a142850a]))),((BitVec.ofNat 152 (word80 [0xfffffffff80008caba,0xcb8c00fe000000003f80])),(BitVec.ofNat 152 (word80 [0x4c090130027048ca92,0xc9842c58b162c58b162c]))),((BitVec.ofNat 152 (word80 [0x92d42,0x4c3f7f0000000fffc000])),(BitVec.ofNat 152 (word80 [0x700e01c04380800d00,0x4c3d3060c183060c1830]))),((BitVec.ofNat 152 (word80 [0x4d414,0x28607ffffffff0000000])),(BitVec.ofNat 152 (word80 [0x801002000400000000,0x4081020408102040]))),(0x0,0x0),(0x0,0x0)]
def g125C : List ColumnInfo := [(1,0,124,0,8),(4,0,121,0,8),(8,0,117,0,8),(16,0,109,0,8),(32,0,93,0,8),(20,0,105,0,7),(0,4,41,80,6),(0,16,41,68,6),(64,0,61,0,6),(5,0,120,0,5),(9,0,116,0,5),(12,0,113,0,5),(16,4,41,64,5),(33,0,92,0,5),(36,0,89,0,5),(40,0,85,0,5),(64,4,41,16,5),(64,16,41,4,5),(41,0,84,0,4),(68,0,41,0,4),(68,16,41,0,4)]
def g125A : List (List Nat) := [[],[83],[66],[66,83],[48],[48,80],[48,66],[48,66,80],[80,48],[80],[80,66,48],[80,66]]
def g125D4 := limbs80 #[#[0x50c8ae1192d915254110,0x30c4ae13925d152d41]]
def g125D5 := limbs80 #[#[0x19770509106117219510,0x997705091054b7050910,0x60b6454910d915254110,0x50951501205954250120,0x5d552501205515250120,0x549515412050b5150120,0xd5152541205515254120,0xdd15254120d915254120,0x2156154120d515454120,0x60b54541205497154120,0xdd372541205537254120,0x597735452061b5154520,0x6037655120e017655120,0x1d171595201d56558520,0xe0d7159520e017159520,0x6077459520dcb7059520,0xe0176d4520e037459520,0x5c970d512061f65d4520,0xdd37054950e0d71d5120,0x5d152d4150dcd6258550,0xe096458b505d364d4950,0xd4ba93d0f99d2b61f42f,0xaf13dcab3563aad53aa6,0x5568ed159ab2763ac5d8,0xf8ae95cab8d6e2da5b2b,0xd540a9c208b64849ec89,0x920c2cc02764c143240e,0x31d1c800edd050b301a1,0x279cb11ae5c6ab0c5638,0x86ca237e0cbcf2c4ef94,0x7cb19bdd0ce2c865f834,0x4b9dcdd0e97087f36435],#[0x92126115dee8a5b843d7,0x2e2e516e6c89d7644d8c,0x4651a79090839488bca,0xdd924d6c91c18265fc23,0x1d1d78e8e6b747a5c140,0x4dfaf05002986dbba3ad,0x256f09347849d3c94e5e,0x76e94ab90a0dc851161,0xe0300a020060100200,0xe2107c1c064160501204,0x6338c22e8b22a4a12608,0x246912414fd3d4ed394d,0xa57d5753d474fd374a92,0xa6c9aa6899a649825e96,0x37edf37ade376dd372db,0x2c03240128230342a020,0x9916430ac2d03a30354,0x0,0x14050100b213216020,0x7088025040000020,0x2d040000006820000,0x17108004d09808000000,0x5d08000000000]]
def g125H5 (j : Nat) := if j=0 then 0x19021020000 else 0
set_option maxRecDepth 16000 in
def g125D6 := limbs80 #[#[0x50910195424417219510,0x44175509105954244152,0x50950443705091099542,0x541105c9504415254110,0x44362545105095144362,0xd91524427654910dc951,0xd89105ca654437259510,0x48142501205d76244174,0x59540481525012054540,0x54120545504835150120,0x48161541205515048152,0x9955048174541205c550,0x54120d51504835154120,0x4837254120dc55048364,0x5d9514816554520dd150,0x54520d91514835154520,0x4837654520dd15148373,0x5d954481705512059554,0x55120dc5544835455120,0x48165585201d56148376,0x5d16548171595201d165,0x59520dc5654837059520,0x48171995205c26548374,0x5c35148165d452059351,0xd45205db5148174d4520,0x48365d4520d935148276,0x5c35448165d5120ddb51,0xd51205db5448171d5120,0x54152545505d76448364,0xd91525416454950d8951,0x58550549615437054950,0x5407458950d896154162],#[0x54b505437458950dc162,0xd41505cb5054162d4150,0x54362d45505cb5154362,0xd935254174d495059352,0xd85505cb6154162d8550,0x54764d89505c76254362,0x59162d4172d81515c351,0x5835158960d457458b50,0x9be3f8fa2fdc960d4572,0xaeeb7abe9fa3e7e9f677,0xbeaf6bbadeb6edaafabd,0xcfb3dcef37cbf2ec7efc,0xdeb6edaf5ed6f5ad5f4f,0xeebaeeab9ee6f9ae3f8e,0x2d4aca53eaf6bcef2fca,0x6c86a6590d3cba96b154,0x64d9109cc1217b74353,0x61652db24707805e0709,0x420c287bd520eb0e8e07,0x430843841146c822fdc8,0xb4784126d0e28d610550,0x841a630831add0629c00,0xcdcca19b194346a90615,0x604b6080daaa0219850,0x42e1c195c18309870253,0x878dc00409870a5b041,0x5438f09871ebee83cb6,0x2000b8426170a4886147,0x98420cf08019610005c,0x2309706570508a85c211,0x82a858d618c26c118c14,0x45e3e1cb46ba96c1842d],#[0xf548cb7c397ab842f5f0,0x8e26c120bd5240970666,0xea91d438538810a72f54,0x1abd52469706753e08ed,0xf64355ac86afd50d5eaa,0x357ae86af994d47ba1aa,0xae892fd5125eaa24bf74,0x6eed50da6c2248f74491,0xdd0ddec11b37863716e8,0xd5b2214d8243470c6ee,0xc11e36874556e88af609,0x85180509b047e3e092a7,0x6554c6c8a98591518c32,0xc130cad7dd14b1b2aa61,0x89c4e0d38dc02727844,0xe3e09fc6b93f1980581f,0x1de8dc23f6f647edac8f,0x13c23e0b8680130f0c26,0x41278482130f102e1df,0x5c8482df01043e1208dc,0x8a130f082e120afc241,0xaeead151d5a13c234198,0xc635c9706c233118366,0x5595822c030098662330,0x16d1c02d27845a4b0cc2,0x6c0326f805e6f00be5e1,0xc88f828f56c91e35ca3b,0x587944b0b297d92409c1,0x92df01265e12351c0462,0x6e8e23dc9c2fc24b5f84,0xe17e19d45c03a5f76751,0x611c55ba38a874715ee4],#[0xb2e3a362b836c6f00d8d,0xba395c74724f08d97dd1,0xaab80746f00dc9a1daaf,0x83791ae4ed7e05d2ec0b,0x87095e05d2bdfb15713,0xe7306e12cc6b95a4784b,0x46e02db2b95c63739aee,0x12931b9d27773a2fee54,0xb2b9622784c0c6e74c9e,0xa508154a15ec5402e130,0xbf62a0bee93c6612841a,0x4a106e94205d285fc150,0x3f053dcdd279fc14e418,0x97cfe0ae8dc05e5d74bf,0xe02f21c05e9574bee2e,0x2b43b9548b74ab10e956,0x7c1672b83c65b05922e0,0x691782ca170998de0341,0x280001309ac9e1351bc0,0x814810c0e20ac06a0420,0x2061ea1d41ba1a019016,0xa2292282264254236218,0x3343243142f82e82c02,0x3fe3da3b839a37036035,0xaa48e47a45e44e43641a,0x653051a50a4fa4e84c64,0x6205e65be59258256c55,0xe46c26a869067664e636,0xc7c479877675872470a6,0x8ca8a888e86a8348187f,0xb498c96493e9289128ec,0xea6ca52a3aa149fe9ec9],#[0xb32b08af4ae0ac6aa8a8,0xf0bcebb6b8eb7eb66b52,0x2c76c66c48c38c28c0cb,0xd22d10cf6cdcccacaec9,0xccdbcdacd92d82d66d4e,0xce62e50e34e12e02de6d,0xef0edeec6eb6e9ee8ee7,0xa2f8af64f46f2cf10f00,0xf041027014ffcfe4fbef,0x1191010df0a708906f05,0xd51bb1a118716914f13f,0x526b24523521b2031e51,0x30f2ff2ed2d72b729d28,0xcf3b539738737735332b,0x148146944f4374273fd3,0x50b4fb4e14d14b94a149,0xb75a758b57155753951d,0x76276175f95e95d95c75,0x6d16c16b169567965f63,0x6174d73d7257137036e9,0xf7f17d37b979d7897717,0x89787986985984783781,0x8140d72020018b98a9,0x856910164a0700258002,0x82d11028d420368c03c2,0x8d0021587428a07826c6,0x118f246104d498260041,0x588b0dc1f18454464626,0x6829f0c5c371b841d020,0x77ea226aaf849195790c,0x305bc85b5df722ef710f,0x2018d85808d07ac2002e],#[0xee0400005c0800b81070,0x15b0800016c20030e87,0xac18b3cc41c8800f0400,0x6140436100941cd87361,0xc4c04000003b8424d853,0x6f62131d0c0180b01ee8,0x19c643941a4324f4646a,0x587bc310c50aa4564234,0x660c7d162370316e8b25,0x3b24b032c0c6d11b25,0x316f50ba2c5d616e98b2,0x219bec14746220440ab9,0x593b152100ee74122ee2,0x16137039611d21548ac8,0xd41407790b6b48680a03,0xb096c3de62b214f66200,0x614d8536100a70200005,0x212cad8c02b415a0804b,0x1815a08000758401361b,0xad04038c0ae50803,0xa0a6c200000194100941,0x72620d86c8435b15e225,0x4100470356100ca0ca09,0x564233421fc1a4427023,0x4682341770234100f650,0xb41006584c851c080558,0xb01dc42cb09908d069,0x10000cf18ad860a18100,0x10002bc177ad63da0938,0x1a83a820001a82b4132,0x8334157021b080402682,0xa70200000100002d876],#[0x15b0d6c334117482000,0x808059080402683a8200,0xc78e066839b0a0364200,0x1bb4200000100321ef5a,0x602000]]
def g125H6 := limbs80 #[#[0xc0090126100200200001,0x44fd2400022200,0x55504e20d00051050e,0xb014c360000000000000,0x44100000000000002,0xc04000,0xd0d11541e0,0x80151b81f00000000000,0x81200000000042a108,0xe41b828000000e100000,0xc0500000a96700000015,0x133d4c000000000000,0x94f0000,0x91a000c0c00b00,0x14e00082e000021000,0xc00041952c00040e8230,0xe03000000c37072c4,0x825000000,0xd532818000000c220000,0xd12000000c5d03080,0x2000000000000000c11,0x17000000000c,0x41500000,0x1c000000120150c2f,0x900000d350000,0x0,0x0,0x600060811e000433c090,0x83145600000000015cc1,0x650c08,0x51f83200081ae830000,0xa4d00000000000000000],#[0x806024000000000,0xc290000000,0x83882600000000000000,0x3400043500000041d82d,0x9410000000235c278478,0x813444000000000d1,0xc07403020850c0f000,0x80000000000042c0]]
set_option maxRecDepth 16000 in
def g125D7 := limbs80 #[#[0x54110509104851019510,0x59510589105491054510,0x5012019520d891099510,0x58520551205452054120,0xd5120d45209952059520,0x5495054550d9120d8520,0xd4550d41505895058550,0xd4551d8950d8550d4950,0xd4b5058b5058750d8151,0xbebf3f9ecee6f2f58351,0xfefb7bafcfdfefd7dbbd,0xdfdfebefeff577fbddad,0x61dcc70ae60097203fdf,0x35c4a0ae6a4152326a11,0x54830ee708374400ba14,0xc846ec42376405db1071,0x4922e849374193b8048d,0xb22e4413721c8b90045d,0xb6e46595231cb2976548,0x6c863964323aa191550c,0xec9257048fb99a9dd0c7,0xc71176397329cb594e22,0x9ad654d9b22695c1326e,0x1b74413b82045d5522ec,0x374419ba20c1d1076e08,0x52688ba2245d914ae089,0x274fb9b07dcd64ae4d45,0x717b22f1dc174ee0b917,0xc8ba3c6dd192ae8e2f64,0xb83e45ca026e912d648,0xb90795c83ca841937291,0x284f1942baa416142133],#[0xaa5d427eca13e6509eb,0xaf1d8556e82bf64164aa,0x9544ccea25e5512df3b0,0xdc4ccae266561333a899,0xd0ccae866754332aa199,0xcdc2c26e35137332999d,0xd56e86bf6435eb21b5dc,0x56ec6a97635fb29af594,0x2e893f6449eb22595c12,0xec93d7649fb2a4f59525,0xa7bd653d5bb24f9d9252,0x72b713b2b81cadd4f50e,0xbf7639ebb1cf594ea6a8,0xd764deb2a6a5c53cae09,0x65429ba20adc50cee083,0x441eba20fdc507ae283e,0x6b2b134a5c51cae08bf7,0xe4a936fd89692a4b6762,0xeb1312549852e4dbf626,0xb13b2549d56e4c3f6261,0xa2f9dc1752e4ebf6275e,0x2f259177ec8bcb545e4a,0x92591c52e8e3f64725b2,0x7d899cee0cc974725b23,0xdd19a0e8cbf6465eb233,0xd1e7ec8f6770795ba334,0x1e7ae8f3f7179eb8bca5,0x27ae912b7489eb244fdd,0x7ae522b7291eb148fdd2,0xee05b01e8060000fdca4,0x8d83f41bc0ca05702640,0x3601970bf859c2961350],#[0x12308b042a1fb0f00724,0x5902ac14c8a204ce253,0x71c00d8068831c1828b9,0xb083e40b1f38f1475439,0xcd25692648f846c22710,0x5bcab454429294449da4,0x62730917c4b9c5aa2c29,0x9af8d526883349948c84,0xe7743ab9cdce2e6f936f,0xca0a101a7ec3e21ebcf1,0x5689f445a1d50b484841,0xa6a4cd23a8fe47223111,0x3889b94d1a6352ea95f4,0x531291945ea1a4ff2785,0x15c0ace55a2aa551aa7a,0x15aa2d05656b1e585abd,0x55792bbc5d02df16d4b6,0x5c61db091816bfe5f62f,0x321966c9e64431ed8d2c,0xd3768e3445a04cf5671b,0xb6c9b2cd866b83559a90,0x2e4e71db899c12def6e8,0x33b2dd66e9a74439d9cc,0x98f3e798bc85e24efc77,0xd73e75f06f737b43d69e,0x4900d7fbbf91fa4fc27,0x83f41ba0bd04a82040da,0xa0664c0865c2ee14908b,0x4406212a109a2c208100,0x213e4a48ac5a38007112,0x3e3e10b440301460d612,0x542e22382c10414000f6],#[0xa472f8427a5c4850c02e,0x18660268845214381a04,0x8a1b7458066838844204,0x7eb28a307074b26f59e0,0x96f50933c20190fa8481,0x1e64326f59e08bdc6001,0x1d7b431937b4324cc288,0xc4a7c90250fa8b1807a3,0xe0884f6612cf5e144bca,0x293af321cd053caa648b,0x3bc626b66463e422f3af,0x9c485e3222652fd8a64b,0x56fa0a64da5fd6284737,0x116d991af20449cff204,0xd1514330733c3050363b,0x18399e48289a0bbd4107,0xc86363a8455342123b11,0x503638808c3638808d3c,0x2f9db04f566485fcf200,0x608f13992139492f1025,0xe8411b777b1c11d2dff1,0x22464c91249f1ccb35f,0xbda808cfd9019d0127ea,0xf100a0e684857dcc0281,0x532e43e88c81847b197e,0xdcfa922b77a343287a65,0x7d414f0316236d7a344,0x8811a78465cacb682a67,0x1913862b2446f035e318,0xb199097c314748c79e1a,0x16b1b3644d4236654d17,0xc535d4a2570cc7075b8d],#[0xcf14873c648979512b78,0x8c08bdf92064a4379512,0x74e220cf10d7ef411071,0xc9b310f7b31126784114,0x40e48d7f344440458620,0x21ad05b2b12fe043b612,0x477e01002b413f047bd7,0x4073411f1b04558f18a0,0xbf2212cd047e42bb9848,0xc853415afde822decb24,0xf021a8e10d7d0439a08f,0x2d0126835a310d7c2441,0xa190361bd11f6b2064a4,0x53a80592550a394634e3,0x739128ea3c28b3d71151,0x889991ce0d0d3c728c97,0x110eb238cc8d798871c9,0xa90e7ea02217c031eeb2,0xe682aa09688e9d6255e,0x60322ea1521b48950354,0x4c589d0115750f7a851d,0xb4620d68c6bd521d9c23,0x8a69097012e309101406,0x215f11276d63978ec1d8,0xe]]
set_option maxRecDepth 16000 in
def g125H7 := limbs80 #[#[0x4076f0207113f04,0x60105004b04006e0003,0x6012b04101907a10052,0x1a163308080329070242,0x20b180605071d013201,0x72315001b0c00020a4e,0x1a000802040000010104,0x80401421a0809081202,0xa0403081c0022050d,0xca786f8335011b711931,0x7b2c94552303020ec0,0xa2c4410d883094bc0b,0x46c03513a0356055d2d,0x813003504080674319,0xe42eb0a0d01f01742d80,0x30dbc23812952634c,0x1011e4006b023a36b054,0xd504ac300000c5678cd5,0xa4028b1c0750003030c2,0x176433a401d0e143c039,0x6500024ead0e940590f7,0x1913807c837708100011,0x1406a87347482a42b,0x124000434d082830d243,0x510c51528000807781a8,0xe13ea1d3a1d917400003,0x58b04df05a00000d0031,0xaa43ac0cf825c0b8849e,0x500020a6417b096452b0,0xc2b52b209e9241a25715,0x39249a0250b400034cc,0x60000000308cc0e26466],#[0xe4aca37e00081be4bb41,0xb8264994816e492c18,0x794dd0ac4100016c335,0xe42fc020cad90d700000,0x683709500b881d41900d,0x700541f504fc8d60a4,0x9f12401e450001389968,0x7091c26b02282721bb80,0x48007146e41d1051405,0x5bc7000000002098c027,0x840e407f08ce02910d05,0x90418b89e80c408,0xadf042525400080f41d6,0xa300cd641163c1cd55a4,0x94092879013502901880,0xe002530d6c23f599009,0x1de0a715600000001,0x3838e49401b845700400,0x52004cd54d84a9471605,0x8560d9421000085518de,0xb0dcc2e4000057c03a8,0x448c039e08a803f46551,0x43cb27002827a471c39,0x3481d90c4583c00090fb,0x4400000903c0a8d6340,0x454c45ae24b9a,0xabf047955e1e900020e1,0x6711fc0c901bd0e70e80,0x1089015f816000000091,0x6cc41b58cc27d050d28,0x4401ed15259270cb8022,0x95114000434815dc2974],#[0x2c4000c2ec02152a80c,0x5b00da001103f41ab411,0x9a5cd030504dca1a1c19,0xc000984607801864ab05,0xaec28e0cc0002087c12,0xd1607a1ce822c083407c,0x663520ea917047ecabb0,0x720019925a059c1c603,0xdc4a4c0490868106a26,0xe406b14fa23fc14b4c39,0xa0804115136832b068d5,0x94e600ac17f044c0f,0x3bc79a1690000140c1b4,0xa55700e4458a48500005,0xe2d002ac19b02f028553,0xcc000000000081710b2,0x3f02d135000000010858,0x202b5030502000148e13,0x8d53540001564000009,0x8f840d0af852000082c1,0x2873714c02ad065c91b5,0x818343b44f20bcc07b0e,0x500000a6f0e951d4436,0xd40000003069d63b4648,0xbd000000052,0xb3117c0000003092000,0x970001003134e80d6868,0x200000000001449c37d5,0x8094446c0f01c6607307,0x27907ec45e0be85724d2,0x3907000008d342744ba1,0x382683224506064000a3],#[0x451000310d80dfa0e000,0xd880b300e026c4a604ed,0x1000003b01e8000c15b1,0x83b3006273400009b601,0x24e1db00030b7,0x159a00034d7017411a0,0x45e00]]
def g125D8 := limbs80 #[#[0xfbfb7d47505455048110,0x908aa801b1bfffefdf7d,0xb2823283b102b108a888,0xb09aa81aa013b2833282,0x3292b2923293b212b213,0xa924a923b0aba823b293,0xb032b145a942b0c3b125,0xa90ca102b057b1b9a8b3,0xaa1caa1cb09da89ca89c,0xb0ada8aca8ad329cb29d,0xb12cb12da92ca92db0ac,0xaa0f011000cb05cb14d,0x23c46d8ca17426c42871,0xdcd11892cc5349b92421,0x2e23e44e838fe1e63986,0xb025d8b45592954f89a9,0x17acef1cc3746a8ce58e,0x6124a3cc5c88d0ae083f,0x292228b16421026dccd9,0x1448284874b08206ca22,0x146801820b82080c7862,0x25b879f089c59302321a,0x2dff80128fc0110ff42,0x70053f92904f73112bb6,0x4b134ea4a25e844a7205,0x82a0793508e4a7388ef2,0x87dc0550fd04596e4ce2,0xa811ff0053fe089684e4,0xfb9c82673d40cfdc8077,0xe30932e71111c8063010,0x189778c222cc5e44462f,0x6e13865ff0455c9027b9],#[0x42ef9940a77a91011a09,0xe50262f6b0982ef9940a,0xe00f516d0a2f2cf81317,0xe40307f2009dff0056bf,0x40287f2009ccffc8097f,0xde3088a]]
set_option maxRecDepth 16000 in
def g125H8 := limbs80 #[#[0x1062142070606,0x500000121030c000007,0x4da07060606001585,0x100311304526b330a0d,0x8000501015e11082504,0x1b19020d701a02081000,0x77103d87c9300d190f,0x30d00032e222d510319,0x446522021b7900190000,0xb029eb00eb0d1b9bdc06,0x1614757ad074000c5b,0x400003117117d6960000,0xcc10e49289b108dc0c71,0x203e198c280000c00b45,0x680577a13a11e0000022,0x8c000015214900000350,0x20b14a35084c08f263c1,0x6ad26b0138456058819,0x7a00f3071091e017ca09,0x7424610b000006811ab0,0x406228a00ae29344f209,0x24604f89910a7003e098,0xe8042091857c42ce1509,0x505100004890abf49e10,0x25480b22590044048001,0xa106e0b2c4e207502b8,0xb063651f0968a4580106,0x1ff10c40a20a1e03909,0x1b7027c0000000197,0xf0056e93e12841ed0af0,0x529600020920001257c1,0xa4000100e000308f127],#[0x4009cf81c000026f464b,0xd629300c41c1891095b4,0x3268c2151b9413303,0x143b007e2940117076,0x21114045900921174770,0xa15b000307241670ab42,0xa4e10d0095c19f1218a1,0xd5e50a6c0b60550001,0x905b84f40e408750d80,0x548d0b80001113283e02,0x596a4940bd078d498000,0x871b809e204a00028431,0xe07dc67d100000352981,0x945f033903805b863,0x5880dd11f50c4053c2d0,0xd45fc00a8664836c4804,0xbc6790b7c2a610,0x30b6455a073c99c000,0xd407741ac040c0f80000,0x4000c0d0290c46807e42,0x57e01a501c503356d91f,0x6241d3443c12c000212e,0x2c55d05d81e72b012075,0xc1b4000c17b42b09b808,0x4d406c1080000401d417,0x4257b401914729300008,0x409d405106f549729801,0x36057749fc63b02a10e,0x274188000c23b0520075,0x4c06605a063001501720,0xca5d03f0579580c13419,0x253038865a162ca4a496],#[0xf066417c56040ed0890,0x9099c229080812408c82,0x1590000081828f19c013,0xb9024c026000101ac42a,0x6000328e628408bc51b0,0xda4b2744119025c26916,0x6e84c46eb0865028000,0x17516a0f504700005784,0xb0b0c56955b00e90218a,0x1345157258864e060c99,0x70c676456000217a0002,0xc09111b90b400000361,0x464010e404019102b000,0x489a5100c327e9468000,0x1909055f4426c04b41a1,0xc000c68e849007b144c8,0xad0023195827a0a8c9a,0xba057c58218b115e,0xe0002848d07203204ec0,0x306541110a5c48906,0xa3c15cc2580000288041,0x9570ba882b4544,0x109c400e45b800216a00,0x5b0aa292c00006a,0x1142c688]]
def g125D9 := limbs80 #[#[0xd51ffa87f543fa41fd10,0x51b0259b138a803fea3f,0x410202548526489000,0x101464648a50101a48a5,0x248a02051549228]]
def g125H9 := limbs80 #[#[0x21028126290084a0c081,0xb568d121881102004000,0x2cc22000070021ff8000,0x38268880004504010000,0x812c2f86e0008a1028c1,0x8a9c27000c5a06d1a0,0x8a9f00001dc2480ac090,0x40786286080e40f00090,0x22d4a890341042e000,0x105742d0000009160000,0x85944b000000000000c6,0x8c6a051e00042a86c000,0xe0700003001410ac87c,0xc00161920c4406f43100,0xaac19a1b000c05a1ec81,0x6402a1f00060310b015c,0xd6240481a90741802b21,0x1c000000823128565000,0x385181b05600040cd298,0x894408000000c0dca,0x176314986208ab04552d,0x841e000021000131c1f8,0x85504200062980bc2020,0x118a2025000829416d64,0x91ba28406c038848]]
def g125D10 (j : Nat) := if j=0 then 0x2080513f else 0
def g125H10 := limbs80 #[#[0x1815180308008,0xa800000000000000,0x2000002000142000c00,0x8000000000000000180,0x140000000300000011,0x50c0000000000000,0x1050000252,0x10900000019400008]]
def g125L : Nat → Packing
  | 4 => (2,6,5,0,0,3,0,g125D4)
  | 5 => (57,5,5,1900586,86,10,1039,g125D5)
  | 6 => (237,4,5,3211372,103,12,1080,g125D6)
  | 7 => (187,3,5,1703973,86,13,1089,g125D7)
  | 8 => (50,2,5,458758,51,11,1060,g125D8)
  | 9 => (6,1,5,0,0,8,0,g125D9)
  | 10 => (1,0,5,0,0,0,0,g125D10)
  | _ => emptyPacking
def g125I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupShort 1 11 0 6 1 3 g125H5
  | 6 => lookupShort 25 257 4 12 6 4 g125H6
  | 7 => lookupShort 111 521 8 14 8 4 g125H7
  | 8 => lookupShort 98 449 8 14 8 4 g125H8
  | 9 => lookupShort 28 149 7 12 6 4 g125H9
  | 10 => lookupShort 4 71 1 9 3 4 g125H10
  | _ => fun _ => none
def g125 : Forest := ⟨125,10,fun i => g125Y[i]?.getD (0,0),g125C,g125A,g125L,g125I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g125P4_0 : block g125 4 0 2=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g125B4 : block g125 4 0 2=true := g125P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g125P5_0 : block g125 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g125P5_1 : block g125 5 1 56=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g125B5 : block g125 5 0 57=true := (@block_merge g125 5 0 1 56 g125P5_0 g125P5_1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g125P6_0 : block g125 6 0 13=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g125P6_13 : block g125 6 13 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g125P6_109 : block g125 6 109 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g125P6_205 : block g125 6 205 32=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g125B6 : block g125 6 0 237=true := (@block_merge g125 6 0 109 128 (@block_merge g125 6 0 13 96 g125P6_0 g125P6_13) (@block_merge g125 6 109 96 32 g125P6_109 g125P6_205))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g125P7_0 : block g125 7 0 10=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g125P7_10 : block g125 7 10 59=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g125P7_69 : block g125 7 69 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g125P7_165 : block g125 7 165 22=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g125B7 : block g125 7 0 187=true := (@block_merge g125 7 0 69 118 (@block_merge g125 7 0 10 59 g125P7_0 g125P7_10) (@block_merge g125 7 69 96 22 g125P7_69 g125P7_165))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g125P8_0 : block g125 8 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g125P8_1 : block g125 8 1 30=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g125P8_31 : block g125 8 31 19=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g125B8 : block g125 8 0 50=true := (@block_merge g125 8 0 1 49 g125P8_0 (@block_merge g125 8 1 30 19 g125P8_1 g125P8_31))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g125P9_0 : block g125 9 0 6=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g125B9 : block g125 9 0 6=true := g125P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g125P10_0 : block g125 10 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g125B10 : block g125 10 0 1=true := g125P10_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g125T : checkedTables g125 10 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g125 0 0 0 = true)
  · exact (rfl : block g125 1 0 0 = true)
  · exact (rfl : block g125 2 0 0 = true)
  · exact (rfl : block g125 3 0 0 = true)
  · exact g125B4
  · exact g125B5
  · exact g125B6
  · exact g125B7
  · exact g125B8
  · exact g125B9
  · exact g125B10
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g125G : graphValid g125 (boundsBefore K233) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low125 : Lower true (varsX 125) (graphGoal 125) 11 := lower_forest (g:=g125) (i:=0) (hints:=132099) (before_sound K233 V233) g125G g125T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K125 := extendKnown K233 11 [(125,[]),(189,[118])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V125 : Known true K125 := extend_ok (m:=125) V233 low125 (by decide +kernel)
def g221Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x7fff007fffe3ffd33b,0x898c000003f00003f03f])),(BitVec.ofNat 152 (word80 [0x8a2502804844112b,0x89885145145145145145]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x87ffff803ffffe0c87,0xc35c0000fc0000fc0fc0])),(BitVec.ofNat 152 (word80 [0x102c060b0280088c83,0xc21c30c30c30c30c30c3]))),((BitVec.ofNat 152 (word80 [0x7ffffffc003ffebd4,0x9494003f00003f00003f])),(BitVec.ofNat 152 (word80 [0x2130080c0b10902ad4,0x1414a28a28a28a28a28a]))),((BitVec.ofNat 152 (word80 [0x7fffffffffc002136,0x6d700fc0000fc0000fc0])),(BitVec.ofNat 152 (word80 [0x41c030100c00e12134,0x2d60c30c30c30c30c30c]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xf800000000000014c0,0xc2bf000000ffffff000])),(BitVec.ofNat 152 (word80 [0x20040201001000000,0x10410410410410410]))),((BitVec.ofNat 152 (word80 [0x2829,0x3203fffffff000000000])),(BitVec.ofNat 152 (word80 [0x40080402002000000,0x20820820820820820]))),(0x0,0x0)]
def g221C : List ColumnInfo := [(1,0,220,0,8),(4,0,217,0,8),(8,0,213,0,8),(16,0,205,0,8),(64,0,157,0,8),(128,0,93,0,8),(9,0,212,0,7),(20,0,201,0,7),(5,0,216,0,5),(12,0,209,0,5),(65,0,156,0,5),(68,0,153,0,5),(129,0,92,0,5),(132,0,89,0,5)]
def g221A : List (List Nat) := [[],[118],[66],[66,118],[32,67],[32,67,118],[32,48,64],[32,48,64,118],[48],[48,118],[48,66],[48,66,118],[64,32,50],[64,32,50,118],[64,50],[64,50,118]]
def g221D4 := limbs80 #[#[0x10b88688965515150110,0x110aa86888660554501,0x2058c0aa468c86605545,0xb983b98]]
def g221D5 := limbs80 #[#[0x21954501105515150110,0x1d970551106055450110,0xe097655110e017655110,0x61e7655110e117655110,0x60554541406037655110,0xdc971595406077055140,0x60772595406077059540,0x6d1da1f43bdc96158154,0x71ad55a6a754da99ce69,0x4b078cd598f319e1ec1f,0xc98a5921790c50e5820,0x59c2a06983332667648d,0xe5cc0c039275f0acde0d,0xec7c9e0b93c27274ae4,0x8c8804003783e2f27ade,0xb7332f2b27231f199490,0x1364b2b9d2cecac4c0bc,0x180a020000010000d36,0x64200014840000000000]]
def g221H5 := limbs80 #[#[0x401c9ae20002880ac044,0x7]]
def g221D6 := limbs80 #[#[0x50110551404415150110,0x44076551105d54044165,0x5d954441705511059154,0x59110dd9544427655110,0x50154541405d56444165,0x55151503615414058550,0x545405d9515017054540,0x50370551405c55450276,0x5c565501655854055161,0x59540dc5655037059540,0x55361581545856055372,0x8fe3b8df61d81545c760,0xaf6bbadeafa7e7e9ee77,0xcbf1fbf2fabbae7b7abe,0xe3f8edf37ad3f3ecef37,0x287aaa03ecf3bcceebae,0x841c1f72aa383c11f2b,0x20b7c30764307cb287ec,0x30dfc10e1c08f7c209dc,0x89abc30efc10f1c08d7c,0x1135c2974b296a3b1b0b,0x1cfc21d3c11c543912c,0x21e9c11ebc01c9c11cbc,0x24ac0244c3a0ec2225c,0xa353c12d7c02cfc22aac,0xa43dc0b3cc0b19c2b7ca,0x1c53c1455c0c7dc03fca,0xad4cc2c94c0c8dc2c51c,0x4dcc0d23bad93c15adb,0x68ac0e2fb961bc1cddc,0x95d7c05f9b9616c0e2fc,0x6a9b9651c1dd3c15e9b],#[0x9729b96e9c0ea8c0eb9c,0x1f51c1f47c1f56c07a9b,0x60e61702103a0380027c,0xbc344648be16c2a84c88,0x55ca29332324207b8ec1,0xdb1ae34a664c59832d8,0x2174127ecf49dd3a871,0x894f498929a484628a51,0x592b015baae54ca794aa,0xac7587b005ecbb171adb,0x95cb3836e0d89a533b64,0x1bf37d6f75eabc975ae,0x40d0ac6080b0083d05a,0x1440d0e73202e10cb273,0x8a720366d40515201201,0x84e021e5f2b794a7b34c,0xe44ae6b1098ca6c57185,0x1910007ec8446df00445,0x853310ef7118179635f8,0x12d8668200c040250472,0x1a14f31a88be42d9a152,0x8045a9631f121e1e853,0x2015b42ed8400032839b,0x100cb029b0c5ac528,0x88023d8eb11b01bfc448,0x8401008040000032836c,0x14c0bb814050100806f4,0xed87205d8e1c0cf86860,0x582c8018e07db416b182,0xe4168a100630201a825e,0x860403d]]
def g221H6 := limbs80 #[#[0x6c06000091192a030006,0x50018780103f49458018,0x46200934488800004190,0x18370589800000040,0x581c84c000080a003080,0x10c177110]]
def g221D7 := limbs80 #[#[0xd9110591105511050110,0x58540551405454054140,0x58154d9540d854059540,0xef5f7fbf5ee7f3bd8154,0xf7f3f7eff773f9dbfdf6,0xb550395100dca25544f,0x6413dd40d7507d941d65,0x57531dd48776115d855,0xc1857595552695457d85,0x1dc61f7082dca0f708bd,0x5015c70b72b15c69b728,0x761c5907d701f5d43d6,0x86376189d85176185d86,0xdd4a17524dd4a16524dd,0x789d961765f5c17d6148,0x716c5c5937578595f154,0x21718ddca13718fdc233,0xc6e361b8586ff60b8dc6,0x85c71171c8d873772b4d,0x21b42d03703a002371c,0x3f0760dc1982e8538941,0xcc9872e4574a1925218,0x725347084cff9e03926d,0x65f6ba1672b053ca153,0x70edc9b034d678ca590b,0x5039f9be2798eddd7b98,0x1254c8f8ff1ae28c3f85,0x5550a7f47a85cef9b73,0x88d8c2f2676b5730ca82,0xf1af85337c0ce64a2ac9,0x549dc85222491a20b439,0x27e60450916b27404ca6],#[0xcf0177e360023ceb8a88,0x99e02b32066700c6620e,0x69046b034b044b045301,0x7cea12ef64e08c79c425,0x5f64bbc214e210d7e086,0x7119b289c02883e0430e,0x52164bc0e467944f8218,0xf7904bab81107fa92247,0x203f0910019bc4677012,0xaf2c400337091580f576,0x19dc091bc04d32866c23,0x15633b8120009f843bd1,0xc10bc5923a22b21388fa,0xe8a18e16a8958b10f810,0x630075e893e302268a10,0xb3b161891a2d32120572,0x116188b16c7080d18]]
def g221H7 := limbs80 #[#[0x81020d49f020d388,0x241548442064b049012,0x450a2ec138232020821a,0x801b81144a124b2173c7,0x60070230454164a2a06,0x2d10c91e221e02601d00,0x342a00010e02630,0xc00084f00940010200,0x823cad500a88300a8000,0xe44700c815a0b856c80a,0x4c0e6a1406410f00040d,0xe0433841144a0fc16680,0x464a00001424a4609ec0,0x697086910940800321b0,0x24401b050a271a050006,0x2078207286108610213b,0xc0898070003306044f5b,0x40d5091021c1f649c46,0x5f81f41eaa1c07693251,0x1e002f211a1b09d422b0,0x44998141560b40742880,0x811a05025594450118db,0xa269145d54c29701aa07,0xc24e0c3168a1a004c04,0x401e0174132aa800e81,0x33421040403308640c42,0x2300523541262880010,0x8278018821050000110e,0xe0690520000000000063,0x250c00008841c]]
def g221D8 := limbs80 #[#[0x9403fffbbefd5450110,0x16555513616541364059,0x617545d6435503608d95,0x842b0c003d82d60b595d,0xf1c4cf602ad368938168,0x775275489262a8128883,0x98d1051b3c655972ccd,0x3c68263e544aa501ef11,0xd808b4031f24096ef024,0xe780265280e141433248,0x49437e81cf7e018bd01a,0x5e]]
def g221H8 := limbs80 #[#[0x471b0000010c300302,0xf170e000707131b1211,0x50002038b290f1c490a,0x9030000304200177e09,0x845000c1688380cc4dc1,0x3888dc1c08416a49740a,0xf0330b9c37888c99c9f9,0x23419c898b8d70738c2,0x68c110ac84445ac3e000,0xd36ac140bb9438af8184,0xc2800000f16f00745,0x310000be770c3400648f,0x5438000145000c27f6f4,0x4004b0c3641b00000081,0x25c2d89c4a2506000848,0xd81f00b095429c3241ec,0x144408886d5ac2bcbc01,0x2e4b200ec24c3b40d8bd,0xcc9b8010000050000004,0x8e883548a80202256982,0x13c0342a83ac3d80441a,0xc51000012c21cc4426c,0x4cdf2f12f88703c0ad00,0xb400088e0a8c43000000,0xb11c9300b50004398b70,0x809730000d6]]
def g221D9 := limbs80 #[#[0x30bf3e07f553fa81fd10,0x5bd8822aa4b98545687]]
def g221H9 := limbs80 #[#[0xc0093800e41100201102,0x4c6001216140000000b3,0x80000000818480830bc5,0x40629440004160902,0xe2000c10009559500,0x30e3154f0adce7205000,0xa9cb04644586c200000,0x40706bd5000030370c00,0x450000040800d008f9a,0x12a380f00000c9]]
def g221D10 (j : Nat) := if j=0 then 0x547613f else 0
def g221H10 := limbs80 #[#[0x257d40144000000020,0x21404000000000000000,0x3c40000000000000,0x28400012000000000000,0x309a060000,0x9400000]]
def g221L : Nat → Packing
  | 4 => (3,6,4,0,0,5,0,g221D4)
  | 5 => (20,5,4,1114127,84,8,1029,g221D5)
  | 6 => (74,4,4,2097183,85,11,1071,g221D6)
  | 7 => (63,3,4,1048589,68,11,1067,g221D7)
  | 8 => (16,2,4,262147,34,9,1044,g221D8)
  | 9 => (3,1,4,0,0,6,0,g221D9)
  | 10 => (1,0,4,0,0,0,0,g221D10)
  | _ => emptyPacking
def g221I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupShort 2 11 3 7 2 3 g221H5
  | 6 => lookupShort 7 41 5 10 5 3 g221H6
  | 7 => lookupShort 36 163 7 13 7 4 g221H7
  | 8 => lookupShort 32 149 8 12 6 4 g221H8
  | 9 => lookupShort 12 73 4 10 4 4 g221H9
  | 10 => lookupShort 3 53 2 8 2 4 g221H10
  | _ => fun _ => none
def g221 : Forest := ⟨221,10,fun i => g221Y[i]?.getD (0,0),g221C,g221A,g221L,g221I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g221P4_0 : block g221 4 0 3=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g221B4 : block g221 4 0 3=true := g221P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g221P5_0 : block g221 5 0 20=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g221B5 : block g221 5 0 20=true := g221P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g221P6_0 : block g221 6 0 5=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g221P6_5 : block g221 6 5 69=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g221B6 : block g221 6 0 74=true := (@block_merge g221 6 0 5 69 g221P6_0 g221P6_5)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g221P7_0 : block g221 7 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g221P7_2 : block g221 7 2 24=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g221P7_26 : block g221 7 26 37=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g221B7 : block g221 7 0 63=true := (@block_merge g221 7 0 2 61 g221P7_0 (@block_merge g221 7 2 24 37 g221P7_2 g221P7_26))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g221P8_0 : block g221 8 0 9=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g221P8_9 : block g221 8 9 7=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g221B8 : block g221 8 0 16=true := (@block_merge g221 8 0 9 7 g221P8_0 g221P8_9)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g221P9_0 : block g221 9 0 3=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g221B9 : block g221 9 0 3=true := g221P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g221P10_0 : block g221 10 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g221B10 : block g221 10 0 1=true := g221P10_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g221T : checkedTables g221 10 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g221 0 0 0 = true)
  · exact (rfl : block g221 1 0 0 = true)
  · exact (rfl : block g221 2 0 0 = true)
  · exact (rfl : block g221 3 0 0 = true)
  · exact g221B4
  · exact g221B5
  · exact g221B6
  · exact g221B7
  · exact g221B8
  · exact g221B9
  · exact g221B10
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g221G : graphValid g221 (boundsBefore K125) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low221 : Lower true (varsX 221) (graphGoal 221) 11 := lower_forest (g:=g221) (i:=0) (hints:=132099) (before_sound K125 V125) g221G g221T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K221 := extendKnown K125 11 [(221,[]),(245,[83]),(252,[32,16,49,65,81])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V221 : Known true K221 := extend_ok (m:=221) V125 low221 (by decide +kernel)
def g235Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfffe00ffc3fe1fffe4,0x3bc9200000f801f003ff])),(BitVec.ofNat 152 (word80 [0x80140a028804400400,0x39c12084210842108421]))),((BitVec.ofNat 152 (word80 [0xc7ffff0003ffe1fe23,0xcba3c0001f0000007c00])),(BitVec.ofNat 152 (word80 [0x12588c4b11280488a3,0xcba3c5ad6b5ad6b5ad6b]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x7fffffffc0001ffcf,0x82947003e0003e0f801f])),(BitVec.ofNat 152 (word80 [0x2060100c003088100e,0x82144108421084210842]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x7fffffffffffe0002,0x447807c0007c00fffe0])),(BitVec.ofNat 152 (word80 [0x8020100040002000,0x210842108421084]))),((BitVec.ofNat 152 (word80 [0xf80000000000000039,0xec089f800007fff00000])),(BitVec.ofNat 152 (word80 [0x300c060218110c131,0x44089421084210842108]))),((BitVec.ofNat 152 (word80 [0x10,0x51304ffffff800000000])),(BitVec.ofNat 152 (word80 [0x40100800200010000,0x842108421084210]))),(0x0,0x0)]
def g235C : List ColumnInfo := [(2,0,233,0,10)]
def g235A : List (List Nat) := [[],[117],[99],[99,117],[48],[48,117],[48,96],[48,96,117],[96,48],[96,48,117],[96],[96,117]]
def g235D10 (j : Nat) := if j=0 then 0x7f else 0
def g235L : Nat → Packing
  | 10 => (1,0,1,0,0,0,0,g235D10)
  | _ => emptyPacking
def g235I (_ _ : Nat) : Option (Nat × Nat) := none
def g235 : Forest := ⟨235,10,fun i => g235Y[i]?.getD (0,0),g235C,g235A,g235L,g235I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P10_0 : block g235 10 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g235B10 : block g235 10 0 1=true := g235P10_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235T : checkedTables g235 10 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g235 0 0 0 = true)
  · exact (rfl : block g235 1 0 0 = true)
  · exact (rfl : block g235 2 0 0 = true)
  · exact (rfl : block g235 3 0 0 = true)
  · exact (rfl : block g235 4 0 0 = true)
  · exact (rfl : block g235 5 0 0 = true)
  · exact (rfl : block g235 6 0 0 = true)
  · exact (rfl : block g235 7 0 0 = true)
  · exact (rfl : block g235 8 0 0 = true)
  · exact (rfl : block g235 9 0 0 = true)
  · exact g235B10
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235G : graphValid g235 (boundsBefore K221) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low235 : Lower true (varsX 235) (graphGoal 235) 11 := lower_forest (g:=g235) (i:=0) (hints:=83) (before_sound K221 V221) g235G g235T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K235 := extendKnown K221 11 [(237,[33,101]),(249,[65,33,101])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V235 : Known true K235 := extend_ok (m:=235) V221 low235 (by decide +kernel)
def g253Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfe01f4201840c62510,0x4261c431e7e7cfeabb69])),(BitVec.ofNat 152 (word80 [0xa0a300200480c0002,0x48048010010342001109]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x1fe0040e00307c9e0,0x381f8ce0799ff00158c])),(BitVec.ofNat 152 (word80 [0x6269046a202168044,0x108d04c1dc85b20140c]))),((BitVec.ofNat 152 (word80 [0x1f7800183f80e00,0x83fe030ff81e0ff366d7])),(BitVec.ofNat 152 (word80 [0x141440840113500000,0x91a80104281c0c204010]))),((BitVec.ofNat 152 (word80 [0x1fe000101fc001000,0xfc0003f0001ff004c8d0])),(BitVec.ofNat 152 (word80 [0x3859600101dc001000,0xdc0003b00017a004c8d0]))),((BitVec.ofNat 152 (word80 [0xfe000801fe00001fff,0x3ffffe0001b731b])),(BitVec.ofNat 152 (word80 [0x20618801c200001074,0x2e85640001a2000]))),((BitVec.ofNat 152 (word80 [0xffe0000001fff,0xfffffc000000001c7c20])),(BitVec.ofNat 152 (word80 [0x408001080000000d88,0x22512400800000400020]))),((BitVec.ofNat 152 (word80 [0xfffffffffe000,0x1f803c])),(BitVec.ofNat 152 (word80 [0x810002301420a12000,0x1000000810000]))),(0x0,0x0)]
def g253C : List ColumnInfo := [(1,0,252,0,11),(4,0,249,0,11),(8,0,245,0,11),(16,0,237,0,11),(32,0,221,0,11),(64,0,189,0,11),(128,0,125,0,11),(20,0,233,0,10),(5,0,248,0,8),(9,0,244,0,8),(12,0,241,0,8),(17,0,236,0,8),(33,0,220,0,8),(36,0,217,0,8),(40,0,213,0,8),(65,0,188,0,8),(68,0,185,0,8),(72,0,181,0,8),(96,0,157,0,8),(129,0,124,0,8),(132,0,121,0,8),(136,0,117,0,8),(160,0,93,0,8),(0,4,41,208,7),(0,16,41,196,7),(21,0,232,0,7),(28,0,225,0,7),(41,0,212,0,7),(4,16,41,192,6),(16,4,41,192,6),(64,4,41,144,6),(64,16,41,132,6),(128,4,41,80,6),(128,16,41,68,6),(192,0,61,0,6),(13,0,240,0,5),(37,0,216,0,5),(68,16,41,128,5),(69,0,184,0,5),(73,0,180,0,5),(76,0,177,0,5),(80,4,41,128,5),(97,0,156,0,5),(100,0,153,0,5),(104,0,149,0,5),(133,0,120,0,5),(137,0,116,0,5),(140,0,113,0,5),(144,4,41,64,5),(161,0,92,0,5),(164,0,89,0,5),(168,0,85,0,5),(192,4,41,16,5),(192,16,41,4,5),(45,0,208,0,4),(105,0,148,0,4),(169,0,84,0,4),(196,0,41,0,4),(196,16,41,0,4),(208,4,41,0,4)]
def g253A : List (List Nat) := [[],[118],[83],[83,118],[66],[66,118],[66,83],[66,83,118],[48],[48,118],[48,80],[48,80,118],[48,66],[48,66,118],[48,66,80],[48,66,80,118],[80,48],[80,48,118],[80],[80,118],[80,66,48],[80,66,48,118],[80,66],[80,66,118]]
def g253D6 := limbs80 #[#[0xc0dc32dd655915250910,0x21b46c9655855150120b,0x9c32e5655897154120de,0xc42e5655897154120b64,0x42a5765957154120b629,0x689a05956154520b439c,0x89a05956454520ce63b4,0xdba8d53331300ce2bb46,0x3f81211c3318a161441c,0x6086022c87f027d82264,0x1c450728bf82f]]
set_option maxRecDepth 16000 in
def g253D7 := limbs80 #[#[0x54942441655915250910,0x44154589215411029d65,0x5494254110dd16248550,0x5411029d6550950441a6,0x5916254950441a259542,0x54950441945915254110,0x44374549615411068b74,0x595625411029d6558550,0x54110e917258950440a7,0x68b74589504416560962,0x59550441a225d6554110,0x440a7595825411025d91,0x595625491025d9059551,0x549106816558952440a7,0x5977458952443a759562,0x59552440a75956454910,0x441a5648875951069097,0x59542501206556561372,0x50120509615454048175,0x68965545404816558551,0x54940481765515250120,0x481a4595525012061564,0xe1152541205d16454950,0x54120619645515048196,0x65d65585504819854961,0x58550481985956154120,0x481a7595615412069165,0x6116154120e856558550,0x5412029d6558950483a2,0x6916558950481a159562,0x58950481a75956254120,0x483a45956254120e8565],#[0xdd16254120e9d6558950,0x54120597845895048165,0x689655915048394e1162,0x5c550481926456554120,0x480a9595715412059562,0x59571541205d9655c550,0x5412064d52dc55048196,0x68965e11504819358b71,0x58551481875956154520,0x481a4595615452068165,0x595615452069d6558551,0x54520e9d6558551483a4,0x6499059151481a059564,0x61951481926416554520,0x481a0595645512068391,0x6098059520e856559154,0x5c520e839461d6548394,0x2619059571480985d565,0x549605409865d655c520,0x541926456558150dd162,0x6456558150e459159560,0x5815068b915956054392,0x69165dc960541a1e4965,0xdc960543a15977258150,0x541a2e45655855059784,0x5958058950e4b9059562,0x585516499059561547a2,0x9dd46f9cf4e739264165,0xaced66ab2d55eaac5552,0xad9569cb2bd93ebad5ce,0x6b8a5c4ee1d70bb855b6,0x7ae3b71bb8d5c62e2f71],#[0x5abac5d5aea774eba5dc,0xe72f35798bcb5e3af1b7,0x95ac8de3aafb17d2be55,0x67e33b59d2ccee66b32d,0x5b5ada5ec6b61fb0ad2d,0x9707f795b9cdcd6e6371,0x15d9aec7747ba25c8ae2,0x8cfc63e17f0af4d787bc,0xf31f92fc57e27f11f1af,0x442b6444ab662cc3642f,0xc7023664c2b644c2366,0xb0cf63aec85b34c823b,0xd23b0c8e1acafa0f0cf6,0x68b4c362b612cad88f68,0x62ca0e7ac809b749448b,0x25af0c2652e81d0b642a,0x6431c2ca3dc2ca35772c,0xc36c409b6830b36630cb,0x756b4c68936850a36651,0x649d3364ae52ec8a7aca,0xdf48dc9f6e95c74ebc47,0x1e345059746e07f68fd,0x4535674931db45287761,0x7f47517f4748cf655d67,0x1183496c0761683f6759,0x6615136415fb48194f68,0xd36c262b2c2033721503,0x49136448e368329b6239,0x7041d36840f368490366,0x596e028362028b6001d3,0x5ceb6804fb66065f6e02,0x6851eb48566b625e7360],#[0xbb6660d36460d36858d3,0x7a032c6dbb6c65cb6464,0x66995f6299fb487e9b64,0x2768a8e76ea5eacab157,0xe63172e69b62e52f66a1,0x66e93f64f22152ee3772,0x4b62d48762905368e85b,0xc69766ba9f42ba4f62d6,0x62c13b62c93f62bd3b68,0xf349069b45053b62cd3f,0xd436110df6f09476905,0xcb1d4361151f690d4761,0x9f4921276919eb451a32,0x381b693da3452632ed21,0x612c1369406369386b67,0xe3696247636643636523,0x753b63700f695543654c,0x14008c0004b69798f49,0x5104804043842ec23c1c,0xb092c8a87f872c6805c8,0x8c1cbecb64af4acca349,0xf1cec0e38e08d90d30c8,0xed2791b110108d018fa4,0x95d150947d3f539535d2,0xa1d9898fd8817f17196b,0xa1c59c01be1b79b05a91,0xdf01e95e09da9d49ce9c,0x22e18e10208e02dfd5f7,0x2248e4163be3823622fa,0x277272e70e6ca66a5c65,0x9da9a29829228aa8327d,0xf6ca2bbeb6aa86a329fa],#[0xeedee62e2ade2da2d46c,0x2431af1070bf02afbef5,0x9344f4133cf37f2eb2a3,0xb66f6335d358f56f4f34,0x95793790382f7b371f6d,0xd008bbffbabb33a6f9ef,0x3f1f1140d486fe1f03c0,0xf0c08d83fb0606ff13e0,0x47a43fb08047b1b319,0xa03fe0af13025f1b43ce,0xe3f0ba1ca5e147826f0,0xe847c0003c04b71143c,0x288046783e07b250e08f,0x90b25607d14b2440df84,0x5770771a05505531b70b,0x3d1bd15e03515e0ae028,0x6fe04c25824448b09f1,0x25b11b0f60805805487b,0x7817b1660286c0e5f048,0xa571ab15f0bc1f61c86,0x3c87d3508a6867445c4e,0x6a56c3d44c75b845655c,0x82344d15683ca56b1ad1,0x1ec6ce640a0c64944022,0xb317f0ff06c0ac01b173,0x8907e444c6eb1d04c55,0x5544624ce6d04604f91e,0xf426c2704db08f112252,0x263180b47100b042351,0x44588440e9139b19079,0x4e21908850841039e0de,0x947145144444e1025ae0],#[0x1b04c31c32314718715,0xef0d82031a51425483f4,0x60804214990711a82586,0x4f911713d0594391b142,0x470b70e7040ccc22f040,0xc420ce26b1c6118c2b21,0x7bfa916d9b70a11be054,0x38f9988e05f0cf988ce3,0xa143bda732e432a43280,0x6702f86d68259c14f94b,0x1dffa5981be1b5a09,0xffc3e66004ffe484c4d0,0x386084cb4f848e840002,0x20063d3742e70c10997,0x8a044fb200c24599951a,0x4913df890206861e63c8,0xff840842039f0381176b,0xa051cbf8101087f20909,0xe1b3f080c95f8406403a,0xeffc3e19c00003de1,0x19a07c7a2d4687840a30,0xb38890849f82132a4b83,0xe9c1a43bfc1b0cc36787,0x8288430ba200cff008a,0xd9014f013e1000a7e3d0,0x73626602cf609480819f,0x51edd50a8eafa0547182,0x2378a08039cc28302efc,0xabc2a21be4a25e108784,0xc5041835ff1c8453daa2,0x58a31d628c75f945190d,0xa780a926f6b147664745],#[0xd7c9f30e4f82dfb90b36,0x504ae040016f98300000,0x40008f8548055ee51bbc,0xe3c82c0052f195460029,0xef0ae782016bc1015bc2,0x7ea353e17a8c062f0805,0xd8100f60402affa88aee,0x2bf033a1d404444658f,0x80067e0023f2d1115563,0xa4e857cc21ebac14bea0,0x1490987c2028ed818e58,0xb465f714907cb09852d1,0xa7434442528de8405f8c,0x6f18b8633090fb850148,0x8b38c4df8c4049c8d0a4,0xd7e60a8ec5570b38c51c,0x83074e06f5570a23c200,0x428d6fa862149234276b,0x5841aff981e2810f076b,0x31f81460004795d2006,0xf3d9a68c9ffe3400670c,0x1cabb85a78a2]]
def g253H7 := limbs80 #[#[0xc5000000000,0x8000000000004180102,0x30000043000014c00003,0x28000000000000000004,0x6091800024]]
set_option maxRecDepth 16000 in
def g253D8 := limbs80 #[#[0x5d565485105915448510,0x59152509105515250910,0x65952509105955250910,0x5d5655091025d6550910,0x64965509106416550910,0x54b8050910e5d6550910,0x55121541105492154110,0x59121541105892154110,0xdd121541105952154110,0x5494254110e512154110,0x59542541105894254110,0x58952541106094254110,0x5c952541105915254110,0x5d952541105d15254110,0x61952541106115254110,0x65952541106515254110,0xdd95254110dd15254110,0x5096154110e515254110,0x59561541105496154110,0xdc961541105c96154110,0x5956254110e496154110,0x5d162541105c96254110,0x66162541106096254110,0xe516254110dd16254110,0x5d9655411025d6554110,0x64965541106456554110,0xe517254110e5d6554110,0xe4586541105958254110,0x5977254110e5d8654110,0x653725411061b7254110,0x61942545105894254510,0x5d162545105956254510],#[0xe116254510dd16254510,0x25d6554510e516254510,0x64165545105d96554510,0xe5d65545106496554510,0xe5d8654510e517254510,0x65372545105977254510,0x5978254510e137254510,0x5516254910dd95454910,0x5d162549105956254910,0xdd162549106116254910,0x64964549105956454910,0x641655491025d6554910,0xe5d655491065d6554910,0x59774549106617654910,0x648875951064b7454910,0x21d8059510e497559510,0x21d81595106498059510,0x662875951061d8259510,0x261655c91065f8259510,0x59584dc91064165dc910,0x595425012065584dc910,0x50951501205d54250120,0x58951501205855150120,0x55152501205955150120,0x59552501205915250120,0xe5952501206155250120,0x64965501205d56550120,0x5915254120e456550120,0x5d952541205d15254120,0xdd152541206195254120,0xe115254120dd95254120,0x5915454120e195254120],#[0xe5954541205d95454120,0x59561541205496154120,0x61161541205c56154120,0x65d61541206516154120,0xdd161541206616154120,0xe516154120e116154120,0x59562541205516254120,0xdd162541205d16254120,0x5956454120e116254120,0x5d9655412025d6554120,0x64965541206456554120,0x65d65541206516554120,0xe516554120e456554120,0x5497154120e5d6554120,0x59571541205897154120,0x61971541205d97154120,0x54b71541206597154120,0x597715412058b7154120,0x597745412064f7154120,0x59561545205978454120,0x61d61545206116154520,0xe116154520dd16154520,0x61164545205956454520,0x5d965545206416454520,0x641655452061d6554520,0x65d65545206516554520,0xe516554520e456554520,0x5957154520e5d6554520,0x65971545206197154520,0xe4d8654520e458654520,0x64165551205956455120,0x6617655120e456555120],#[0xe1d75595205938155120,0x21d8059520e457559520,0x60980595206058059520,0xe118059520e058059520,0x5d58159520e458059520,0xe418759520e058159520,0x5d78159520e518759520,0x65381595206438159520,0x643845952065f8159520,0x261655c5206478759520,0x615655c5205d5655c520,0x645655c520641655c520,0xe61655c52065d655c520,0x64165dd120659755c520,0x5895258150e417654950,0x65952581506095258150,0xe115258150dd15258150,0x6456558150e515258150,0xe4565581506496558150,0x5957158150e496558150,0xe4572581505957258150,0x597715815058b7158150,0x64b715815060b7158150,0x64772581505977258150,0xe1372581506537258150,0x61d52585505d15258550,0xe4165585506496558550,0xe496558550e456558550,0x5d172585505957258550,0x5c98058550e517258550,0x5977258550e518258550,0x66372585506477258550],#[0x6438258550e137258550,0x65165589506456558950,0xe456558950e416558950,0x5958058950e516558950,0xe4580589506158058950,0x64b74589505977458950,0x6098159550e137458950,0xe418159550e058159550,0xe0b80595506478059550,0x645655c95064b8159550,0x64b815d950647805d950,0x60962dc550647825d950,0xe4565dc95065165dc950,0xe4165585516416558551,0x64980595516098059551,0x6438159551e098059551,0x59561dc151643815d951,0xe4961dc15160961dc151,0xe11725c165e09715c165,0x60971dc165647725c165,0xe87d87786f60981dc165,0x97d9779768fe8fd8f687,0xde9dd9da9d699e97f97e,0xe9fe9fc9fa9ef9ea9df9,0xa7ca7aa79a77a76a75a6,0xf6aefadfadeadaabaa7f,0xeb1db0fafeafcafaaf7a,0xb57b56b55b4fb4eb1fb1,0x5fb5eb5db5cb5bb5ab59,0xdb7cb7bb7ab79b77b6ab,0xb9eb9db9bb9ab96b7eb7,0xddbdcbdbbdabd7bcfb9f],#[0xebfcbfabf6bebbeabdeb,0xc7ec7dc7bc77c76c6fc6,0xdfcdecdacd7ccec9ec7f,0xdd1bcfecfdcfaceeceac,0xd5ad56d52d3ad1fd1ed1,0x7ad72d6ed5ed5dd5cd5b,0xed9dd9cd9ad7ed7cd7bd,0xddeddcddbddadcad9fd9,0x1be0fdfcdfadf5debdea,0xfe5ee5de5ae1fe1ee1de,0xe9de9ae8fe8ee7ce6ae5,0xdcedaed8ecaebae9fe9e,0xbf1af0ff0eefaeeaedee,0xf4bf4af1ff1ef1df1cf1,0x5df5cf5bf5af58f4ef4c,0xef8df8bf8af78f6af5ef,0xf9af99f98f97f96f8ff8,0xcafaafa9f9ef9df9cf9b,0xafd9fd8fd6fcefccfcbf,0x635b26a1feafe8fdcfd,0xcac5d81959ba032b174,0x1d35c3032698606566ec,0x42917608552e80dbb594,0x3d22ca26ac5c848f2cb0,0x5a429c4af2b28a291651,0xf28c305db59709d274e2,0x631860c99f48193369c2,0x99b442033e983319c306,0x6865c5344b28a8cda210,0x57d10c5bc97193432c39,0x25860098346303368860,0x4aec4d6765894cecb8fa],#[0x26888655d1111bc9722c,0x3d196a65540597b46433,0x1a43280b466500e90b40,0xd525f1968cbe38d117c0,0xaa4c230d19846da23081,0xba9a407a33180f466402,0xa6354830c6a3969cd350,0x2c6f7d658df50bb1bce7,0xd8e332c29c2d165383ef,0xb1c881a838ca30c71a25,0x6392f72c725e658e518b,0xca18a618e824d21cc83a,0xd44dacb286338650c630,0x291b16552512caa27364,0x3bb432ca355e1948aac3,0x7794618ef44bb1dea174,0xf719c31e231863c19b4e,0xee33863dc630c7b33684,0xeaf32c7d8c5d8fa66d31,0x933e84f240d31f57b963,0x467d39e8cda13e19f487,0x81a43f4674e7a20e90f,0xd12ca8e426991968b223,0x9459520c3ca242896547,0x4453a350ba4468fb4c90,0x49863fd02ec7fa2e9d1b,0x432e910e68902d0cb202,0xa5d94cd0cb294b7a452b,0x7d0a4da1764c87344998,0x5a4491ab42922be91265,0xf40bf29e9d7852d3af0b,0xaa5862ed230c75a16181],#[0xd1b494c946580748d003,0x746eb42caed6a649d403,0x28e120689c2d0cb3828b,0x89be85d137c31a6712e7,0x2bc5a1657786748df78e,0x37195f48ee68595e114b,0x6ff67595fc18d239907a,0x61710b2c5d6d658080f4,0xc41e3928243acb0c6659,0x8a02747145e64a221bd1,0x23895964403d1c581fa3,0x1d67ba03b25540733acb,0x36bf7606e32c80dc9694,0x7a5f4c0d80e581b39c30,0x191e18235eb2846fd650,0x6edbb04a0165093b72c1,0x2bf741257ae824c95484,0x9f748264be904901ca09,0xbf6884a7cd209ddb9413,0x5bbb04f118409e22c813,0xd640a24f4c139be1827,0xeac8179e6102d7ab2853,0xee502f5bba05eb5740bd,0x3d2066f5860ba4f48177,0x7a40cd6b0819ad590329,0x70c1aab5d0315ac3066b,0xe18406fd3069c7960d47,0xbb08927a20e38f2c208e,0xa10e9bb48215fe1844e3,0x4e1f37e9c3a93d10752f,0x94595aca8a8f3a4151bf,0x10ba996515cc30c2cbd5],#[0x114bdaca2fa65945c78d,0xe29a629c528bd20a6fda,0x86ae2b28d443a516d374,0x8e567861db8aca3b59e1,0x1b057523a37e90735ed0,0x328064864f7cb0da9976,0x62e3cb8ce997619a5f44,0xdcdda21a1bb443045e88,0xe5b2ca000a688702ad10,0xa55947f78b28f309641,0x52ab29069565201db444,0x297a71f5fb403e7a5948,0xc6aca4c58e1890e0b292,0xaf68094b1c312dc16525,0xc9116557626ce3404d,0xd9a221a274444a55d88d,0x4eec0209688926cd111c,0x3594a36ab213ed56501d,0x8d0942f5a02851aca53a,0xda7285194e5043e90a17,0x3444ea3e9ca147539428,0x688acafc3171b9652e1a,0xd3160b9a42b18b465634,0xa52eb4aec5e1ae8cc459,0xca6bbf594d99aa11b1b9,0x94db86b21b60b9635e22,0x21c6c9a734a774269bd5,0x53ac1328759b6a0e388d,0xa84c954908c6cc1d66d8,0xd04fccba09fb94415fac,0xa2e596545532ca897ee5,0x41deb4483bfe8506f6b2],#[0x9b14e890ef7cba0ded97,0x3737c326e6d864dd6aec,0x7a99764edeaca9c7ee59,0xcd6b4aa2ad619426fd2a,0xa49e9cf493d09e927a13,0xb7bd0a36f5a146cdf4e7,0x6f7a746def488dbd6911,0x4db44a6ad6894b7ad124,0x4968930fcc9261f9924a,0xfdca255f9944ad32ec98,0x25a24cd32ec9649e912a,0x2f42937e689334cbb265,0x55955492d126a9b9749a,0xac3a9efda053caacaaba,0xfa054d2d4ea795e1d4f2,0xb40b47e649634abb2dc9,0xe816116c3abe95765a25,0xd02f24d65600ab40ba21,0x925ed0f4ebca169d796e,0x44c624e8d88e8c936df9,0x499c4cd131d8f9462933,0xb3098d926883740d0636,0x465b1f24cb7225196d2b,0xaec45e89cec5d03318b9,0x5d293d0b7a99a275d32c,0x3ba9ba17753342ee7b59,0x71dff22e3a6e91dd4cd2,0xe345e89c6f7c938ded92,0xcaf7c9395ed9272dcf46,0x92f7927222f42e445689,0x322f48e47be51c8f6ca3,0x645691ccf7ca39915a17],#[0xcf6d2399efa1733db42e,0x5ed927ac5acb007be91c,0x22f40f444689ec8ad13d,0x5f61612f6b2c2441a16e,0xbec1440d3a28c22b4304,0x43a0892ef270d5f60a1e,0xd3251aa568a420dd0454,0x468a3689d1469eb928d3,0xdc9c9017a29007f451f4,0xb9393847472654e524aa,0xb4c13cc69048adc9ca15,0x5d82b96d105731a10ae5,0xca0632d940bd894e15c1,0x960f58b2c20c1658318e,0x48294de903e9bd206e05,0x846d62d20e5dda61de0b,0xa0cec4a71b60aec36cc6,0x60162aec0252e807b02c,0xc04ca6840996d0013159,0xb5dd3812b8a7025f2e,0x1e0d9404c2b24084fe9,0x31d346063d6880d4ebb,0x50be594a47ad102879a8,0xa982d0151fd952adf348,0x729fa72a5394e54c0684,0xbd83425bb1680b6ead31,0x738690b270d215a05942,0xeeca19969963447b2a6,0xb399635bab485d4de94c,0xe774269ce684d396d11b,0x51688ed97d09c72da138,0x96cba0b2d944165b0882],#[0x56542a8f4485cb66105,0xf4883c16910782b2a1b,0x1e9d0782d3a0f059741e,0x1d1a214ba14460b3083c,0xda54e65b2c9bcb61936a,0xb2c9dcb6893b98d0a772,0xe893f03d4a7604a94ee0,0xd0a472fa13d28f44a051,0xa1534eb42a6c1e852382,0x4694cb6492999c8a5277,0x893196c926305764a647,0xa5b05764c26b4898cb6,0x14d26f42974d685329bd,0x8a7c06914f80b2aa135a,0xd4f80d3a9f018753e074,0x2b94ba05c9ff4eb8c0e9,0x565c2caadc15955d0ac9,0xb1cb6496371d22b305a0,0x6582bb2c537a458c0b28,0xbe9d8757a6b40b538e9d,0xb23f48b34de81674fcba,0x684e85770cd02e935a05,0x960bab5d94986b42b24d,0x63f986a47930d4a7619a,0xad130d897619aa9bd035,0x28681b246d234c95a369,0x71d0af2e1a15e20740da,0x7d82634fb04c44d6817d,0x9340ca9f60990a2d131a,0x6e919d0ac933a9d7664a,0xdd03429d766685f4ecf1,0x5a1741c342c113e91a02],#[0xb24e5c1649c783d0ba30,0x595f783d0b9305a272e0,0xd1bcd33a179a5744f2c1,0xa07c3e2cafaa7595f291,0x28f47c595f94ed23f707,0x91ee8dd23d1f3947a3e3,0xc2307a183e0b4307466,0x18153f430aa7686153bd,0x303466920b75d1c0b039,0x2332fc344d19a1832374,0x46847a489263450e3869,0x8e607451ac068a3580c9,0x2046e9a3a44d24798394,0x8b00aa00d800032325,0x8809f011d02060350058,0x42c078c0e3019602f805,0x830b059c0aa4142024a0,0xc1e883af072c0d98197,0x9a2129823f844e085810,0x57e0aa614c428284f50,0x834886600c6017c42db,0xf2a1dd03a487270df61b,0x855105e20643fb87bf0,0x4849188f711a8229043c,0x42227a84e1099612cc25,0x8ae515642a4c5350a451,0xac5c30b5b16662c7c585,0x90431546160be717882e,0x8d761a7a340066e8cc11,0x207278e201c1037686d3,0xec03d0878b8eea1d583a,0x903420403f8c7d78f851],#[0x9087f10d12140422c82c,0x3c446d48ca917522aa44,0x12c5252c49a4919920a2,0x949bd1352264a4c1896d,0x8a850e8a1013ec27924e,0x953a2a2853b8a6314822,0x2caf315bc2b2055ccaab,0xdee5b1cb52166d2c7458,0x17e42f885e84bb897232,0x10c6c18b431086118c10,0x3da6700cd09964327864,0x9afb359e6a2cd291a1e3,0x9cdde9b9636da6d1cd95,0x92a71dce269c24381e6f,0x9d5b3a647438e701cbb3,0xbcf1d9e093ba276acec7,0xe927cbcf829eda3d4279,0x1ff53fa87e94fc71f773,0x9d05f209f40ec810500c,0x3c086c50b6a139423083,0xa29b44f8895d11e22114,0xe11aca33a46028b9d15d,0x89690591fb23d7474e8d,0x251949fc933524c24734,0xd12e4a5ae4b3495ad2a3,0xd949a9133526364c2e97,0x27ba4f429d45396a6f94,0x7944028645076a0493f5,0x310a55149328f35186a2,0xaa525452a7bd4e8a9b65,0x49595aaf855baaab1544,0x856afed5e7abae570aad],#[0xacf45992b2396392c545,0x29703adce5b18b559692,0xe98bc5d76f2eab5cf6b9,0x302b6000bf417d2af705,0xa588330c66146c1dd828,0x432c7a18d9317f6280c4,0x331165b2caa193c324e6,0xf99fe33c26746cde99a3,0xa52d415a66b4a968e4d0,0xb61b6bdad6d9ac435536,0xa9b94b6f26d8ad9e9b1b,0xc4e0a9bfeb7d86f68dd,0xb99072a2e405c63b8967,0x21d4c3a63745ae7f9ce5,0x810eef1dbe3b527620eb,0x3cf97996f27de313c387,0x75ef13da17af6f51de8d,0xe44fbe5f673e927ca4f8,0xc05e803eff99fdcbf707,0x660b2412281cd02c2041,0x5bf0aa2131422483bf06,0x43d387390dda1a6c31f8,0x26267c49188e310da20d,0xbdb171e2ca456d8a8914,0x46fa8dab1a4e338c6338,0xa40847d88f351d3e397,0x319259e491c8c090e921,0xcaad94ef292251149c49,0x4e5d1cb68968b2c6e572,0x93331a6625cc2097e32f,0x4d859ab7349a6774cc39,0xe747ce5e9c3137826d5],#[0xfcf3ee67b44f3c9df73b,0x50b2a125419281cd00d9,0x7e8bf515ea259440e86f,0x4af48e6907d1eba38746,0xd315a5e34b4a953527ca,0x2a9f4d3bfa7374dce99e,0x9995292a3bd45da87f50,0xd5c5ab35557ea96d4fea,0x4ab4fd66eacab58d6afe,0xec75cf6b8cd702adcd5b,0xd808afcb5f36bd7d78ca,0x82c77d8aeb1216182c18,0x3e566f6cc1d959b27564,0xdabbb53569cad2c5a27b,0xdedc5db65b6736c16d6f,0x90f7166e155befb7af6e,0xdd61ba837416e6cdcabb,0xe2f0fddfabba176aaec4,0xdd57b16f505e70bcab78,0xdf8fbedf7d36f98df14b,0x1b045e04fc01f7f9afdb,0x341862f0ae612ec20383,0x6272c49788830f5e1bfc,0x7f19d62ffc5bb8b0f14f,0x81f8faf1e6e3b4c7138d,0xe4e4c977921722ce42fc,0x7f2ee65aacb15959f28f,0xdff9aef34f6677cc9798,0xe81bcfb59e933b46739c,0x2f48ce8eed15fa22342b,0x471a7e74e4699cd2e9a5,0xeb22d5ebab2754bea68d],#[0x35eb6ba1d713ada75a4,0x9b7b2ef647ec66d85bb0,0x6dccdb5bb5fb6a5ed18d,0xc374b6e64dc85b89b701,0xf01bd23794eef7ddadba,0xf074e089c06f7f5efb2d,0xf8fb0b07f80f0e0d3849,0xaf19e203581f713e2022,0xae3037d0fb1b8001ee8,0x83a0f83743f63bc20477,0x91b61fe081d74602243f,0x107086fe0a1105de07e1,0xa3b140782d8a2141e1dc,0xf06a2a08d82854139130,0x4840d562614ba1645036,0x3411e82f1c0afc2c1105,0xc652b84ee3b08c230232,0xa11b1304a13388c25c04,0x407f428914a370c1c910,0x4884c13a3644689c9191,0x4d9523871156a0d44120,0x1760022ba0054f0a154,0x70591e2850905ec6c2b,0x8d7140c610820546615c,0x9b21345027d1c19c093,0x808452e10514c044618c,0xb389b04e214b8081ada0,0x9198ba00277c66847080,0xa8e23d2b495514657a22,0xd86c8a9126214004b90c,0x44c4b0c623600cdc5458,0x2a955c8894804f0f5294],#[0x21720ab09c38240400aa,0x1206284acc77089184b,0x28951a098222ed116228,0xa4aa3255840452c38051,0x962cd4ca245a0b82851e,0xdb9b428053016005a140,0x898285504931512724d4,0x310314a1581f0d81b028,0x20a7836c3e12d0ea0ac1,0x3c109973ac5584cd1023,0xe91fb10908ca2c313f2,0xc223276256b150015c6c,0xa393214e5190920a268a,0x1411815b83702c5ca710,0xa2110494e0252a0b4126,0x84d21943f65400556019,0xe85831e0ee2b41f85326,0x1e81883202a0506c2a42,0xcaa6650849be203120f1,0x4b1e82831e09c0a68302,0x44446525279430559bd1,0xe71c732464617427e2bc,0xc4a0a6a224938542c848,0x4727110670c2a89c4c2c,0xa048016686088838c339,0x70522c97204b34681d43,0x2a870a10c9428be4109a,0x648098915ca328291155,0xc051a7001934ab0a534c,0x8453bcba891b8c29f408,0x8f8ece08b084b446fd69,0x21c31e1701987e5043a],#[0x2e032ac0f089afe06926,0x16573045efe4960658fd,0x8456fffc000ce6795cc1,0x87c7ecf0493010e3c5c,0x4c10c00ca7f7ffb82498,0xe8005217f13031986fe9,0x8e5c7f6e84d3a006ac3e,0xffff7409c44d0bfc2724,0xda3c044affd4d3a00678,0xf965e102143affb9008,0x68e5e80194bffcc400cc,0x5f1f2008f97e0104000a,0xfcee4023c1fa46100a5d,0x9032e9fd20083529a826,0x180a7b3f6041014ad6c3,0xf24d20840883bf3a4984,0xe1ffdb90dd18274433fc,0xe6006129bbfe9c660819,0xc2a73b67b74806535989,0xf64d25090cb780075121,0xdf4b1ba24327d1204ca6,0xf5fe0d31133a7bd40994,0x87544cb27d21b01430d4,0x32f1fd26014979c1237,0x119e9f5030112183f2c1,0x50d33581d51a3fd7a0ea,0xcffeb53594cecf811061,0xa86e7b47ec58a8759543,0xa4b3fca30aa437c1be18,0x5fa92a03055305c8f98a,0xdf0827ba66a650135429,0x8dfd9510ca8708c234ca],#[0xb2a86b2a86dfe5235330,0xfe4242d4cf77f80c1548,0x292298e895d10931660,0x2bfe3f985ab5135616c,0x2760052f3fb840b21400,0x137f3a6396018a89bfd,0x20222eef0175237d18b2,0x20c823443bfff95c102,0xcd377ecb8098aa65777e,0x9e112880684f21dae024,0x327a22a0e029ae33095a,0xd2821183fb53ea44900d,0x67a7c936c88c411a267f,0xc7f1821950cdfbc7404a,0x333b6b5c7299871e6545,0x3f7fafc22ac9301fb063,0x5610c1fb3e04515f8d11,0xaf3804c043d61f1d6997,0x33c4d1724aa1c0ea860e,0xbfd9880666789b809543,0x61e9d3247edfcc92019d,0x4307e8dd3207e8dd323,0x8597ff6a408597ff6908,0xee8401908d112ffd1180,0xe34468625bee80d5431b,0xfa874a1a6703aa1abfe1,0xf67e250d33d3a34a848,0x7cba8240672f08736a66,0x1dbc3b203287f239332a,0x44df98112df6721b011a,0x80a9f7fc3582121b7e60,0xf11ca8523ff6cb2a2040],#[0x5ec20217917b08085e7f,0xaa8aa57388a0fe4083e4,0x892951f9081a12190f4,0xe2950d5e8499066d3231,0x452af370100887b7c06f,0x72c21a905f2f0ca88234,0x91100cfb7e288810d4de,0xf29813ff084480d91dfe,0x3032dbe05726234327ff,0xd2a6aa23b2d02196b5fa,0x6a86ffc9821971c20e7f,0x5e021a9b0fdc4aef8418,0xe5112180fbc602928d9a,0x160fd5f5cb84229c576c,0xa83dfca6aa215e2e4282,0xbf10c0297ca3e551abc8,0x88087fbf2d2308053355,0xdfee5ac186a7d6dd5f21,0xd26ef0295cb5830d5204,0xede6a61d0c293ed28890,0x34bfe55010befa23074f,0x347bd2ec067cf4f2626b,0x703c62001895ff4f4303,0x4303343fd90702140f08,0xd0b3033479f684d5ff4f,0x9cc03421b3fb0cd0cd9f,0x1ec0c166b7f41c08587d,0x1be4c9ff3d1040b2d19f,0x31084b442ffa05368f49,0xf2e9fd8102943e3f175,0xe69812d4c2ff808020ad,0x4871bd7f20082b4441b1],#[0x71e0ed48033eefe2b218,0x491c348a7003467864c,0x19bf6ec004359f024b3e,0x19e6ccc015247eec0196,0x3fc284700053746bf880,0x7afdc44cb1d3ce2e2676,0x1ff37a744cfd14f4e226,0xf63890005325fef0114b,0xe58be4a2a94024154a5f,0x4f4e8019c3fae70d8033,0xf401145ff8040042a53f,0x87ff4809b3f97800cab,0x506c9fea8184ce4f5505,0x4593ff1234318153cb04,0x84221aff390134f5f4a,0xc4d2ff92843850d8ffe5,0x2482a65f8cd245bcccc,0xcd1e97d400ce87fc81,0x35190f95760022139c6a,0x339933a2667fe2988004,0xc49d3ac2660fe45b200,0x8a2457ec04d7d38f4181,0xff148a12ef88108152cf,0xfe8186102a6d8fa008d0,0x9995fd9a261088288eb,0x43c3ff7534c086cf8d99,0x4ff55912323f57120800,0xabeb8b8c06e113504146,0x8597f961b38086ce1931,0xa1e18cc0067f7f02480,0x449193bc49929fe1d205,0xe751350c9ffd4226599c],#[0xa546dfd4015850f6c5f,0xf7a15eda6a988fffb008,0x4fc9045c3d4e27402946,0xfc0cb20c3014f664ec93,0x32544874fe9b1103331,0x21121bbb79b0328bd3f1,0xc61121e7e4822985ffa2,0x48878ebf2cd0cccecff0,0x507f8f8e44283fc7c308,0x4cefc00c9810c5c33606,0xbb7c4420cd111c973611,0xc4884e2b0648f7ee098,0x1eba3c624333e0fc48e0,0x6280043facfa144a121d,0x2a1f8be98740087f6cf3,0xa7859d8ae4e27300a,0x9ead112051247e568280,0x4c55ff7efa006747e380,0x48f000010f15d8336101,0x10e0f877b2b65028847d,0xf0aff002131c10fdb000,0xff800336b9bd5b2600a1,0xa1bbf3f8698099d305,0x3311bfe6c04caef9e12,0x10817e88c0054b330bd,0xa03143dec2080a8c7cb8,0x89aa2fe9124de4000a4c,0x1c38a5f4c01dee8b100f,0x218006767cbe9887036b,0x7727ea8ec381dd9f2fa6,0x6c19a9aed92d2eea546d,0x53e7fe00dd04d9c0aab7],#[0xcf0125305f0b30033d3,0x474406fd7a141870bfe0,0x188cce906cbbfc3750f,0x22cec88229df755dabc2,0x1bfdd6082aea6859fa83,0x690e42d7be10a24a0369,0x75233cbe2241426447b4,0x194d11e9cb98332d9191,0x4d7d75041a04fd0e7247,0x10e438573e5c40a30692,0x4b0a2d60d8eac9ae1ba4,0x2a4152c08b4ff6ecc45d,0xcf1e84418b3bbfbbdb24,0x45183507f0c2d8883169,0x8980099c8a8f86f6f1e8,0x59a3c6e2ed9adffff244,0x88f7e71284ec3574424c,0xbca1128827fc9ca65a9c,0x112efc06f424087f79c0,0xf18500466b9701bd0040,0x16f926356bfcb00bc303,0x5fec1838041a6bff0d4c,0x818495c738c3f030939e,0x5a538307008348e71b78,0xde94a1e1b1f64c04a0d2,0xdbef3ae643381ac9bb80,0x47fa933a540c1322b3ff,0xeb31d85aa33ad654667,0x53b10154c2022fbff428,0x99d7471af5981259f17f,0xfba8b076506aa0ec05c5,0xeca0d038817acc0928df],#[0x2f4067c17aac23775160,0x8e5f4510f7880d31cb5c,0x51e1af7e2644af97acc0,0x421d8e419a5080a7b706,0x192440890710dd772564,0xab83a6c264887757974b,0xce4d428dbb101dda5366,0xb3ddf99a2cf1248b6787,0xff6e8cebd2ac8022b5e5,0x31e84a7d6cfaa526437b,0x6aaf4b1924912b7ea33a,0xf3f1350ca54cde0a487c,0x88d7f8468d11021c9c9,0x95ee206a17ffe00cc164,0x2737aae1021c3ffcfe4c,0x497d3cc8d1140200548b,0x1a22d87829d5c7d54811,0x80c106a976bff8b90819,0x7e358121a9ecf8962031,0xd0eafe75824610113e68,0x7eda01d42b3b0df64b50,0x27a903921f1e0924085f,0x6fa1e30814012d52487f,0xdef0a0096a7c783a8300,0x2d00446ae80d618057,0xf37e28425a1114ff57c7,0x59984ffd6018328053f3,0x229a9f21c5042a669d3a,0x4d347e510cc07e0e1088,0x811357fb635c00040c05,0x53e700618bfc26740041,0x832b3f27ece990632112],#[0x4a7e828bc19e87e0fc35,0x8c4ebcc6099162bbf808,0xfe8e8423e84c88b7ff54,0x641a0b0d3535ee071ab5,0x1f57a41180872c3184fc,0xe3f71fe89de215c335b1,0xdf2101e600aa0c09023,0xc2eaa3fd38c4c09beffc,0x49e00902225f447010a3,0x9c6fa6e20c09023ade93,0x19e9f6a1a085003fbbff,0xbf980ec810edf52fd063,0x443a70a63f4102834a3d,0xbb7f05410a4f357efb66,0x77d5ce31222dfc150423,0xac8cc705b52b90eef87,0x10294466b8540062b70e,0x710352b7ac20c9715c2a,0x594b845e85405295fa1e,0x3abd248e080a7e2556e8,0x123cccb7e4f10c128a6f,0x22106997aa14b42d70ff,0x8147d342a029fbccfaa6,0x633aba5b8cc86023aa50,0xfe8a0bcd14743150a80a,0x504ffe39ee449d0ec52f,0x63229408385e15d02c1d,0xb4ecfb113d5a22c2f0b6,0x10babf28048a628bec51,0x5295f0c5b6e52cb8390a,0xa7da5a93021c0fc181a0,0x4663f069688627836084],#[0x1e5fe051410af6a7088a,0x49adfe845e7e94102482,0x39889efcbc0ca6303e08,0x6814a9c4ede0caa3e23e,0x81814976edcd1d5dab8,0xc7a886ca42797959aad,0x657ed832a299728437f0,0x6779dec5352e52d44623,0x868148ee9f06c10a000b,0x4877e1f007ad0394bb71,0x7b94603180d7f17aa628,0x95dbde814a01ec7138e,0xf063f1ce1ba427bc0311,0x2065307e9b72a1c67666,0xfb8159516234f07ea2d4,0x4c1b04387e9b733c665b,0xdc0d9b8284053ebfe7dc,0xa40a60b7831f9f36051c,0x32c4f0056b4d47f4284,0xd2737063bbc2aa3cfc62,0x194a261e1e05275f4796,0x3cd4724cec3293cd0f56,0x3125fe7b0420007d155a,0xa9fec890624316f9214a,0x8bb59ce8c0ba07b7c629,0xbc34c035e0555a76c2da,0xf2f0c38ed5b880aaa403,0x22f0e31127925294d282,0x2399e85bb6b530a298dd,0x864b70f9d5a3f0f60368,0x8fbc38a59ca67885407e,0x8de17d20cb23d499c38a],#[0x9acbb87b5b471e03b814,0x2947042c9f78e90652e7,0x23381860845dbe630c0b,0xb4e30e2b6e0d23381847,0x4266c34b1a878795874c,0xdb20cf1ca1db6cb0c5f3,0x6442b245b7cac3417c0b,0xda2c46c253bbfe2055b8,0x8567158ac2731d3713c2,0xa4f3c05bc0297997ce00,0x807868e27ad8427b92cc,0x683847dabc19edab641c,0xa5a26f24fb2e85c76f21,0x94d1c6ddf192cccc6f8c,0xc8cd2f90923c120e1dd8,0x5e32300398ae9736d790,0x6379289518e62b6bc86f,0xc326707808111979528b,0x48877ced8455f88110cf,0xa95062433b0e047d8c92,0xdc1316c2c147c408627f,0xa27668e8c1ab0413ea19,0xf63792894c55eda91034,0x820188f78b53902976ea,0xcc0a4378b9c6008685db,0xe934d55e1bbc0707b2dc,0xce40a47bfd54f0109894,0x384052e5e6592094a67d,0x49497a242631d60c8e4a,0x5894a23458186b7b9c81,0x53d9f1ae7d052f5a105,0x5f4b72c90ab6cc51ae7d],#[0xd491507debc777a4129e,0xc3209490edb95fcc8149,0xa67151c4a6a8fe036473,0xb0edb81fc32bb5122481,0x7e84a3094b37e84a3094,0x1256a69a347a220f70b3,0x3094e087f4f1782d8881,0xcbaeec364300b7ac142e,0x32980a3f17012d8029f9,0x5e0c106a84bec05a7cc,0xc1f65df131191167ea73,0x5a512916ecd9c86194c6,0x687033cb2f1a31912b78,0xcd12586243fbd5c24568,0xe9df6a17270c4b09884f,0xa25129b4fec8141297df,0xfdd2629b550044a5a70b,0xd99c19cdff8d225ca1b5,0x4315fe290df194c1dbca,0x17d4e87c04343f491bd6,0x51edf80e51e6fd7d28c4,0x90f7245335ee5101fa44,0x60294d469d95086c3f69,0x599bca5c5004415f4ee4,0xc99b58d4a83e64510c45,0xa8a80094f9b84018676,0x4d07da2c2c4029800bff,0xdf64201c563338521e5b,0x4646844b1bb63786180b,0x17c8683a0b5ff284c5c2,0x3d7272991a98537c8084,0x3840786d202163f40637],#[0x618421077c3534ded0bb,0x88ddf68a8b4129fc7646,0xae505287a2059f597029,0x894bcb4c04198b657fff,0x24f20ee03151641d751,0xeb4f446e788e10]]
set_option maxRecDepth 16000 in
def g253H8 := limbs80 #[#[0x46042000140004041002,0x30c004a3411401101840,0x4a08d1c900200004e04,0x134010202e046201006,0x30c314b4420520cc3520,0xa800000040024230d30,0x404600c191a33,0x2000000010bd8000c094,0x605c00000000000432,0xadd80006480802091a40,0x8437014100300000001,0x401d000121f8081000,0x31370000000101c00,0x2000000010822039c46e,0xb02a7e0000000102bc82,0x810c018000080e200000,0x25800000000c4b1,0x1880004272003c000000,0x805c0000000420000010,0x6a21190024e85384a7,0x39606800008066035000,0x81f501c2036404400020,0x980df11df004634e80a8,0x33e080447e804d438621,0x108000000054de00010,0xc405684e102780000000,0x4348423b2027036811,0x103c0006247800115500,0x428e000109b286d442c,0xb2001f00000000000000,0x15a591005b000000014,0x488ba8853439ea07544d],#[0x8236000300a806,0xc10f516628140550a080,0x2120ce8000000c0001,0xf230700f300b8000000,0x8d400002b75000008720,0x92be00000006154c08a,0x68000e08880850ac000,0xa5640004a7042b200020,0xd014000000000000000,0x20607580eca01d536800,0x4016a5630,0xc0660000235d1060000,0x40d036d0c20cbc000000,0x212d0144059000000020,0x6c0bb095c00e08291249,0x39898480b18903102508,0x80df01d800000f804f40,0x4004e0131825800040bf,0x38000d26880fe029403,0x1bb00b2248901901e80,0xa7019a1090000c26e,0x27007700580003016800,0x8061002e20210f581ff0,0x101ae02ac01b00b5,0x6014009601e0000000,0x8090000093c846021dc0,0xa6018a58e02080001247,0x36cb74845000002bb811,0x91fd001f4460000ac1c1,0x4105019703088710001,0x1a800000000000000000,0x940041a11100c605f30],#[0x30000000000041410000,0x14800000018095404691,0xf40002103000000020,0x810a00000000000c2c2,0xbbc1052886081c000000,0x810d88f50,0xe00008038231e961d0c0,0x80c885c8a80000000615,0x1100007b000000020,0x98229802a5298000d266,0xaf0929c07d15d401e206,0x804a4830854000000034,0x108bc000002080a2,0x26800000010113142800,0x800400002150000808e0,0x7c00921881c0c0480035,0x2f0119000180c9625e34,0xd0d8000000040fd512f0,0x40d80003511682b0001,0xba823b008e0000000000,0xbc1188000007400030,0x60000004503a0000100c,0x104]]
set_option maxRecDepth 16000 in
def g253D9 := limbs80 #[#[0x48510595214415448510,0x44374485105d52144174,0x595424415250910dd521,0x50910615424417550910,0x4438050910dd54244187,0x54950441425411048550,0x54110589504416154110,0x44176541105c95044165,0xdc950441865411060950,0x54510509514437654110,0x44172545105955144162,0x6195144182545105d951,0x54510dd9514437254510,0x4415454910e195144382,0x59552441645491058952,0x549105d1524417254910,0x44186549106115244176,0xdd152442875491061d52,0x54910e11524437654910,0x4408759510e1d5244386,0x6056544180595105d565,0x5951061d654418259510,0x4438759510e096544287,0x5d572441745c91059572,0x5c910e1172441855c910,0x441825d5105d97544385,0xe1975443825d51061975,0xdc9106137244165dc910,0x48186dd51060b7544185,0x54940481515012050940,0x541205d5404816550120,0x48161541205515048152],#[0x59550481645412058950,0x541205d1504817154120,0x48184541206055048176,0xdd150483715412061950,0x54120e11504837654120,0x48164545205855148386,0x5d951481715452059551,0x54520619514818454520,0x4837454520a1d5148187,0xe19514838454520dd951,0x55120591544838754520,0x48176551205d55448165,0x61d54481865512060154,0x59520e19544838155120,0x48180595205d56548087,0x61d65481845952060565,0x59520e05654828759520,0x481655c520e1d6548384,0xe1571481855c5205d571,0x5d5205d975481655d120,0x481865d5206117548181,0xe1975483845d520e0575,0xdc52060f7148165dc520,0x48181dd1205977448185,0x61b7548181dd52061774,0x549505d1525416454950,0x5437654950dd15254176,0x5c560541655815054960,0x58150dc5605417258150,0x54165585505496154372,0x6016154172585505c561,0x5855061d615418258550],#[0x5438258550dc96154287,0x601625416558950e1d61,0x5895061d625418558950,0x5418159550dd16254287,0xe0565543805955060965,0x5c550549715438259550,0x541655c9505d97154165,0x60576543815c9505d972,0x5d950e0176541825d950,0x54162dc550e097654381,0x61b7154182dc55059771,0xdc9506077254165dc950,0x54181dd95061b7254184,0x60165545655855160b76,0x5c151e05655478059551,0x545765c1515957054561,0xe0576547805d95160176,0xdc15158770547835d951,0x54586dc15160b7054565,0x5c970595715c16560376,0x5c16560970595815c165,0x597725c165dc57059770,0xdc571597825c165e0570,0xdc1655c770597805c565,0x59771dc16560b7059581,0xe0b7059781dc165dcb70,0x3bc6fe037159580dc565,0xcff9fd3f67bcef9bf1fe,0xeafb5eebbd76adf57e9f,0xbb76eebdbeb3f67abfd7,0x7eafcdf7beb7beefddeb,0xf2fe3fbff7fafedfcbf7],#[0xee9fcff9fb3ee7bcef9b,0xf5ddfb7f6f6dddb7b6b5,0xe3bbff7f6fddf9bef7d6,0xdd77adf5ae9fcfb8ff1e,0xe7bbf75edfdbbb575feb,0xc7f7fefddf7be77bef5d,0x7bdf3fe7bcef9cf37e6b,0xbfb5f63ebfcef97f2bdf,0xdbfaff57dffbdf77ee7d,0xff3fdffaff3fe3fbfeff,0x1f516510bca906ffeffb,0x33976bb0dbc5d84a02e4,0xc2a7da5513e2aea9a079,0x5d1486326bd01525e5c,0xa02eca4bb845281ba294,0xaabb86525cc32940dd94,0x5a101ca3fbc5d95e92ca,0xb2d11265a7692c53af16,0x1e4fa9dacbb24b929e78,0x66ae81b85540dd4b1068,0x1a83940d40ca06cddd03,0x60d9bbb06cd5d8370aca,0xcb06a065835bf0c1add8,0xddc8426ae42185521041,0x8c32a1d7d520e41c9084,0x1f7d620fc2c8879065c3,0x40f87ba07c35d03efae4,0xc307c3dd83e1aec1e639,0x8e583cc32c1ec7860f62,0xc832e2359651196b9089,0x270d651321ca0998e544,0x61355c309aa6184e1f2a],#[0xc30bc35945c83282e439,0xe4454832c2eab861754,0xab2ec24639212c2c8892,0x2863951487cb894325c4,0x11620c90c43e54508724,0xcb8b37e4458872e2c839,0xae4808ef24043d970055,0x7f2a04a7850252c2814,0x23d950453c282296141,0x2033bc9018f65c0612ea,0xc301a96180c7f28072b9,0x9e18147b280a3f960353,0x87b2e328390191ecb02a,0x385f951c1ecb8d555946,0x51c84b28e0fe50714f08,0xcb0e29e18714b0c390b9,0x2594807b2840a784201f,0x87b2c40a7862052c3104,0x44c165220cca1120e407,0x1b0ccb1129dd8894aec,0xcb8dc225c6eaaec37859,0x2e54747f243a5f951d85,0xcdf263e83901f1ec910c,0x3e1b921f6fc80f8fe5c7,0x20c0cc911a9e5c7da726,0xcc045b550183b2a18d55,0x7e40241330160b980804,0x95720141f900a05cb848,0x5e0b9829a6b29282e542,0x7310cc89882660bc7324,0xcc152561c9deaec4e099,0x2660c07324600b982a04],#[0x4132e6419913205cb960,0x5a1f902d15ca968ee48b,0x42d53c896aae40b43722,0xc91702e58b52f2a5a0b9,0x7640cc13305c29952e1c,0xc77247e3b923e0cc8998,0x7a08983d04caa0a5e14f,0x4421fc8a002e60f41530,0xc2a402e5524132c84099,0x2e51281730900998484a,0xd510e6cdd813605cb250,0x7619913b0ec81da921cd,0x63515c91abd5d8d4132e,0x4c1a0d64cd0732468f79,0x7e40e4572a7237933905,0x55720721793390dc89c8,0x729f933905c91ca9e44e,0x3c04cc1d0a654e92f2a,0xc89e2a640f03322781d9,0xe4110572a8609923c52,0x4132c8c0994461fc8a21,0x8e3793451fc8a290e411,0x24c05cb2582e512c1324,0xb227e5595372a849c0b9,0xb5d93efaca9f95944fca,0xf72c9e79964f6ac327c,0xa31b945120cba8435d54,0x554bea92a10e5945530c,0xb12f18e5562faa4b1596,0xae1979530cbd0d655e96,0x8f724b77d525b20cb2f2,0xa57d7652bec2295f5914],#[0x45596ba2adf55156fb0c,0xc929df65555af08ab2f7,0x16194e1aeca7716453be,0x8c72ca661965363c329b,0xb24197567cbb2b565955,0x15f55c32caa619661aca,0xc32faa6197e1acabe419,0x159584f724b841965f55,0xefb24ae1d966154bb30b,0xaf0c9757acbb2b98e515,0x45a21c8ad18e556a1f2e,0xc92e90645821f2ab4439,0x7e5175af24ba43975d3d,0x2aacac61d946255cbae8,0xca09976e04cc360f645b,0x86d1ec8b682e619deaec,0xcbb782e5da42f26d2099,0x7e41a8572ad43f916a04,0x532ad635936b1ec8b58,0x229d65914bc2c287641c,0x8904ac2c827e56453b2b,0xc13a82e5a48173120099,0x1595c4132ef01d90786a,0x92b0ee4f576727ebab8d,0xe6ff947315cbb90a65dc,0x87415cb39a5e19cd2b0c,0xc83c82e5dd81730e8099,0xae41dc5f28ee0997790e,0x1731100b967705c8bba,0x2695859317ca4982e565,0x69505c8ca82e624c1331,0xc840aa21df1ab04f80b9],#[0x55d6083b21040997810e,0xc5722f6f5767b04cbc12,0xf43d917a7bcb3d8ae51e,0x57f17ca3f82a61e85b28,0xc83f84e51fc3f20fe2b9,0x6e51fd3128fe0b917f55,0x532b0097957f05ca3fa,0x6a990830ec841826620,0x8a15cac4826520c1323,0xc8458265a3413291a439,0xe4230132d1c09918e21,0x813291e09918f17ca461,0x3f59659f05c8cb82e5a5,0x29d20c950be58a84a72d,0xc24ec3dd276b2c93b7d8,0x659682b32d3a63949d63,0x95709444191a229cb505,0x3d5b919eacc8cf106528,0x5a5acb2d3d6e4a7ab325,0xcc55bd596ac7b2357556,0x265eb162cb581d90ac04,0x47f23535791a4adc8520,0x521f90a913cb548de4ea,0x6aa1ec8d503e56a42f27,0xc15c83656b43b215a259,0x860b11270d76b386ba5f,0x81331889186c47ab2e22,0x8e0b96c64ab2e302e531,0x69b2dc94cbd5da601725,0xc84d0a65a6d2f0d36958,0x1e4a6a1f21345b929a31,0xeb2cb5e29949c15ca4d4],#[0x669b84b31cc959b1616b,0xae04cc598965acdeacb,0xc95896e4ac09f295d5b9,0xe64ac84f2d622f94b11d,0x5270d7ab386bc12cb590,0x940b96c94ab2e482e532,0x4c805cb6525597281723,0xc8db02e532c1723962b9,0x864ad98f056cc582b630,0xc7216a5793b431c85a1,0x821d91c106ca5c31e42e,0xbf20c96090647043b25,0xc8600264b086f277e439,0x26530c1323862f94c021,0x817299a0b91cd05c9660,0xa8b386d35bc369555974,0x2d952c16ca4e1b506f27,0xcb6da55976c1729b63f9,0x5e433aab219c0b92dc05,0xda707ae5d90d12fc8e7d,0xaa3f91d569c8ec066435,0x2d64fc1eb0de4f553f07,0xc8ec48e0f5c7b21ae099,0x2e4b753f21b09d90d891,0x8321d83793e91bc9ef0,0xd44190ed0bc9f529607b,0x1eb4fc9f502e4ba86f27,0xb20682e4bc01729d60b9,0xe50843730c1bb9840ddc,0xb63041db1620edcc1086,0x1ee7860e9fbb07635943,0x40fc6c207e35d03f1ac8],#[0xcb07e36183f1aec1f8d9,0x9590476304238d970fc6,0x51728233f74119eba08d,0x22899811b2c308e36544,0x4139ec209a2e504d1730,0xc30bcf6105e7b0c273f9,0x35945517282ae584159e,0x5cb0c2b3f76159ebb0ae,0x2c8b9214c6c90922e585,0x4009fcb8b22e485b7722,0xcb004edd80312ca019d6,0x1e500e730a0939650443,0x676ec33896519d6b10ca,0x3539741ab0b20d38e186,0x41c43ca0d38e106a76e8,0xc2104ee50710f2838e38,0x85d8890f283d3986209c,0x90f243e87921dc4c90db,0xd337606c0b283665901,0x425c0aa1291e5c1cff2c,0xaa1436e109666e84b317,0x2e189226ec487f9428c0,0x55f0c53116529aeb2933,0x56af862f88b29791e58a,0x2757bb18b2594c51720,0xbb1399e509f13224f8d9,0x4a5c9e232e4f109727ae,0x48f2e5845943089cb93c,0x7e21954156baa088e50b,0x54122caa0ab615048f28,0xb2a491e51015b2a82ad6,0xe645227b2090ad954956],#[0xdcb046cad984823ca244,0x7111753843c91bb8608d,0x23433c91aabe1ce15b0e,0xc91e08e48e48f2472459,0xb5d91843288cad923c22,0xb62c49db9614e10cb232,0xa08b915045cb27635953,0x454dcb8aa4f65d436324,0xca2a39e11527ee8a98d5,0xc58961172ea889975445,0x1cb0cb13d7658c6b2ac6,0xaf3d865e45cb2c39e196,0x457c6ca2be3e455f1b22,0xc8aea2e456b1f2eaf8f9,0xedd18dcf2eba8b975d45,0x9c70ec6e1876371c231c,0xcce386669cbb33625959,0x66c88b2b657595910f2c,0xc8b2e36419592cadcaf8,0x2e1d95930ecb5d7665c5,0x50f22d2ad8767894bb2b,0xd4e7906a10cbb79ce4da,0x88422cbc2445d610472c,0xc84311e5a155f0d0a239,0x2595e19ac8f021968745,0xe272ee5119772c6c8393,0xf8ad989323c8c9cf6424,0x27cd8c13e39e05f1cb02,0xca3e39e11f1cb08f9b39,0x45d60513210273937d45,0x48b2f02ae878156c3c0c,0x221978156cbc0b96420],#[0x77e56c3bf445d5f95d2f,0xbac122642088f2efcaf8,0x9642088b2f04ad878288,0xe270ef667917b56cbc13,0xfeaf877f35ca3fa2e41f,0x47f8fca3fc7251fe7f20,0xc8bfb9e41fe272afe479,0x26420c8b3100cf947f11,0x95b2906e5908322ca41a,0x1821968d56bb46a2e422,0x2a110c8c791e5e311721,0xc251c4dd28d1723413d8,0x764a915f09575d65a665,0xccf23351192c5afc9525,0x5d5f91aeaec8d722e46b,0x5be23c8d8d7e52babb29,0xc8de8865af95aed7cc96,0x4653222723911191c823,0x31b256d8d82b689ca644,0x68cb82b464c15a62e06d,0x2b764c15bdde4ed0cf25,0xc8dae3e42d4cb256ecb8,0x2e12d593096b8382b533,0x19709706591b833ca5ab,0x70cb91b864c8dc19652e,0x2c144c8e0b2e52e19329,0xc96d4f64b04432584e59,0x260b3f17239f8b81cf88,0x4cb25a06792cf65c167b,0xc53990d770c86be26434,0x3de9db8ef2264b8a7ae5,0xc96f2be0b7a7703bc739],#[0x164b8d5f05c72793de23,0x55ae5ca6795e039c9f01,0xbf3f90df45c86f8864b9,0x4e457c27211647915f09,0xca7319e5784d729c2459,0x164bb15b05d8ad82e910,0x95b05d42394eb56c2769,0xd6ad84eb22c9772b60bb,0x2e822ca7791e53ad5f09,0xc17808e4bc10b21ce219,0x164bc48f25e0af82f056,0x77aec33c17615e0bb071,0xdb57606deca0d6f6186,0x207dec883f06401f6b2c,0xcb83d025c1f22ea0fb59,0x45d8936b084b417608a1,0xf232a4db59226c8c3126,0x4ee9862bc8b295d0618b,0x44847ca1623e50ab2328,0xcb273a610e383246d419,0x611538722a1c19150e0,0x38330a9c19754e0ca2a7,0xc7c3915de0cb2c706196,0x666dec3336f61d8f7b08,0xb2b468611938320c9bd9,0x4651951f2cd0e98668c8,0x7232ecb918765c9ca32e,0xce8d9867a0c3b3e4e5d9,0x469d3c9b4efe45a51f30,0xcb3523e5da5d30ed28f9,0x4616137b2309c1908447,0x5d73108e89884a0cbc26],#[0xe4e98686a0cb42d061a1,0x17ce0c0be64e45cb2322,0xc9beefe05f78722f9c38,0x36520783210391757dd3,0x91f22fc8d9781c8bac0a,0x4e8d918347c8bfa36460,0x7a3c8c251e45d28f82e5,0xca5423e529a82e94d918,0x4646f327236193919a47,0xf2305694391bdc9c8de6,0x859391b5c8c95be460ad,0x2c246c9613ae0b09d305,0xc967e460b3dd72386e99,0x5cb8e82e5bd9392cfc8,0x11b25cb4172e546c971d,0xeb92f074c9783a60bc,0x2a01ac013a00ca006600,0xbc037c032202dc028a02,0x6004f604b60466042403,0x2e06c4065c060e05a405,0xec0892082607c2075e07,0xe40a6a0a0209a4094a08,0x820c420be20b9a0b240a,0xde0d940d5c0d160ccc0c,0xca0f680ef40ea60e300d,0x9c113810d6108e10140f,0x92130812c4126c11f411,0x4c1502149a145013ea13,0xee16a4166a15fc159e15,0x3e17f817cc1764171e16,0xc0196a193618f018b018,0x3c1afc1a8e1a6019f619],#[0xb01c681c161bc01b761b,0x61dc61d821d341cfe1c,0x8c1f381f021e961e3e1e,0x2a20ec20bc204e1ffe1f,0x8a223c21f82182215621,0xca236e233a22f422c422,0x3c24ca2494245e240023,0xa82664260a25de25ae25,0x5027d62782271e26da26,0xe8299229362904289428,0xa02b3a2afe2aa42a6229,0x6c2d202cae2c702c0c2b,0xc42e8a2e362de22dae2d,0x6830062fc22f882f182e,0x31be3176313c30d030,0x7c333a32fa32ba327232,0x48350234b63456340433,0xcc368a363c35f2358035,0x50380237bc376e372436,0x66393238fe38ca389038,0x943a5c3a1239e039a239,0xea3bb63b6e3b243ada3a,0x4a3d1a3ca23c4a3c183b,0x983e463dfe3dd23d983d,0xfa3fbc3f743f323ede3e,0x904142412440e240643f,0x2642e64284423c41e041,0xca4476441a43aa437e43,0x52462045ca4576452244,0xe04786475a46fc46c646,0x2248ec48ba4864483847,0x6c4a1849d2498a495649],#[0xe04bb04b664b1c4ac24a,0x8e4d4c4cf44c904c224b,0x264ee84e944e2e4dcc4d,0x9250584ff64fb84f704f,0x80522851de5172511250,0xde536e5336530052b852,0xc4555a54f05496542053,0xa257505700568e562255,0x52592858ce585657fe57,0xe05a805a1e59d259a859,0x585bfe5bb65b725b245a,0xfe5dc85d825d1a5cc05c,0xa85f565f125e945e5e5d,0x1260ac606060185fe85f,0x98622661f8619a615a61,0x4063f46364631a62d662,0xce6580654c64d4647a64,0x48670e66c6668e660c65,0x62683267ea67b2677e67,0xca698c694a68f468a068,0xda6aa46a6e6a3e6a0269,0xac6c406bc26b506b186a,0x786e166dcc6d5e6d006c,0xe06f886f3e6edc6ea26e,0x44710470bc706c702a6f,0xa27248720671d8718671,0x7273e073967356730472,0xc75c2757e753074d274,0xce7780772076d8766476,0x3e78f278947852781a77,0xa67a507a0479d4798879,0x87bbc7b687b327ad87a],#[0x647d1c7ce47c907c627c,0xc47e807e387df07db87d,0x9a8058800c7f867f227e,0x2081d08186810a80d280,0xf4839c833c82d2826c82,0x9a8550851284a0844483,0xb2873686d0864e85d485,0x9e893c88ee887a882087,0x648b1e8acc8a5889ec89,0x8cc28c888c328bd28b,0xa48e5a8e0a8daa8d668d,0x308fea8f988f3e8eee8e,0xa29166912690e2909490,0x2292b89270921891ce91,0xee9478942093be936293,0xbe965c95ee95c4955e94,0x78981897c2975a972296,0x669a1699ac994298ea98,0xc89b929b509af89a9a9a,0x3c9ccc9c8c9c589c0e9b,0xb49e689e109dc29d989d,0x96a01a9fd69f629f309e,0x46a1e0a1a8a14aa11aa0,0xd8a39ca316a2dca28aa2,0x62a524a4caa47ca420a3,0x4a6aaa65aa5dea592a5,0x96a84ca802a796a756a7,0x4aa9daa966a92ca8eaa8,0x32abcaab68ab08aa98aa,0xf0ad9ead5cacfcac86ac,0x1cafbcaf66aee6ae6cad,0xc0b15ab11ab0e0b05ab0],#[0x3eb2e0b2a6b26cb22eb1,0x1ab4a4b43ab3ecb390b3,0x14b6dab67eb5fcb574b5,0xb6b85ab7fab7b0b75eb7,0xe2ba7aba20b994b920b8,0xdebc92bc20bba6bb42ba,0xaabe5cbdf8bd96bd38bc,0x7ac01cbfc2bf6ebefebe,0x58c1cac162c10cc0bac0,0x36c3dcc378c32ac2bac2,0xe4c586c522c4dec484c4,0x92c750c6e6c684c61ec5,0xaec936c8d2c866c7fac7,0xa4cb3acac0ca60c9fec9,0x70cd20ccaecc36cbfccb,0x40cec4ce7cce2ccde2cd,0xf2d06ed014cfd6cf7ecf,0xd2d294d228d1bed14cd0,0xccd46ed406d38cd334d2,0x72d616d5b8d56cd506d4,0x3ad7ded77ad71cd6c2d6,0xfad9c0d958d90ed8aad8,0xa6db3adb04da9eda4ad9,0x28dceadc9adc42dc0cdb,0xf8deb8de4cddecdd94dd,0xfee09ae02cdfc2df4cde,0xe294e226e1eae174e0,0xace438e3f8e3c6e35ce3,0x84e62ae5c2e570e502e4,0x68e802e78ae73ae6dee6,0x14e9c0e94ee902e8cce8,0x48ec06eb7ceaf2ea7eea],#[0x30edc0ed64eceaeca8ec,0xccef7eef20eec6ee78ee,0xe8f188f110f0a4f026ef,0x58f3d6f35cf2f0f25cf1,0x5ef5ecf586f526f4ccf4,0x6af7eaf796f730f6caf6,0x64f9fcf9b0f952f8d2f8,0x9afc1cfbaefb66fae6fa,0x94fe20fdc4fd5cfce6fc,0xa50032ffdeff6eff08fe,0x3f02b3023301a5012f00,0x5f04fb049703f303a303,0x6506f70699060d05cb05,0x830927088307fd07bb07,0xc70b550ac50a6b0a1709,0xb90d430cd90c790c0f0b,0x30f9f0f450ec50e430d,0xfb117b112310bd107710,0xcb139b133312c1125311,0x91153d14dd1489141513,0x75171516a5165715fd15,0x8f192b18af183917eb17,0xbf1b411ab71a4519fb19,0x771d4d1ce91cbf1c671b,0x7f1f351eab1e511ded1d,0x63211720a3204f1feb1f,0x6d22f92295221b21b921,0xef255524bd245923fb23,0xf727a1270926c9267725,0xc5296f292b28c5286327,0x872b392ab72a612a1d29,0xa92d492ce52c732bff2b],#[0xf52f6f2ef32e692e092d,0x2331bb313d30b5304f2f,0x4133c13379331f328d32,0xf7368d35d7354d34c334,0xab393538e93861379f36,0xff3b5f3adf3a733a0939,0xc13d653cf13cb73c533b,0xcd3f553ecf3e5f3e253d,0xbf414740f140a340273f,0xc3436342f5428b422341,0xc5455b44f1447f442143,0xb9475b46f946a3463745,0x9f493148e3487d480947,0x474ae34a934a5b49eb49,0x3b4cdf4c714c154bad4b,0x514edb4e754e0b4dab4d,0x3350c950634ff54fb14f,0x4952e552755201519551,0x4554df5479540b53a953,0xe1568b564f55ed55a355,0xb5584b5801579b573956,0xfb5a755a09599b592b58,0xe95c715c1b5bbd5b4f5a,0xd75e7b5e315dd95d5f5c,0xad60675fff5fb55f495e,0xd3626961ff6171611160,0xc16465640763a3633762,0x83660765b96563651d64,0x3b67ed6793672b66d966,0xa96971691f68d5688968,0xab6b356ae56a736a0d69,0xdd6d636d096c9f6c176b],#[0x3e8bc3f89c00696e4d6d,0xbf856338d07e8ce2585e,0xf06e1aa1fc1385a10400,0x478da3e1fc2d8963e0e0,0x181e1168162a261d04f0,0x9a3628c3684783e184c1,0x205c0dd0f8438f801370,0x40702a5822822216809a,0x98500c3824782108c200,0x81aac3f0c2a8a408d818,0xca26238648b8bc0b128,0x303e44310c003a04c8ba,0x49a9440278d914aa9260,0x32124a92961d1f448ad0,0x498d488434007384ca12,0x2aa88aa8ea8d0b4db364,0x82841b42ae04a9239aca,0xaa288502b2aa8cab1878,0x2428cac142712188ca54,0x2d2945028652a017e04c,0xbb261530415e14228480,0x918f4980067328096084,0x960a0521861052a510c6,0xb7812b70801804a91a08,0x109b43288c8993834884,0x9b1f02c4e0b100362014,0x4124a0b06c0a2c230761,0x2039cdf100622f24a872,0x809024c5d8af1262a9c2,0x1c244632cc9292251834,0x83ad6a405005a0811322,0x710886a0a438170330a1],#[0x6b0d27299a1ca7213184,0x54313a8d2a68af4242e6,0x81abbf42d3452068afa3,0x53d28081a8219ec5de80,0xbf6f619e52800357343d,0xcf76699c2dcfd98809a3,0xf1cee2a1831e79d3285b,0xd8c895443c67109b29bf,0x3d322a666e69b5329be2,0x79eb0644696e7b3a65ed,0xa32a8543b43e0d4cad86,0xb8543f53fa58a6657fa2,0xb73ebf32234cbf6e850,0x15fcd0a4840873c86250,0x73404469cfe2f9cd911a,0x233abf34a02121b3f8be,0x17d7a899519d3dfe3e32,0x445d1021eb81ec312a34,0xdb0fd103094032251fca,0xfa6b28a81434a7785032,0x8145521a24c7f0a11abf,0x1f19ed11f7fde4116bf1,0x22f5f790469efefc8234,0xb206683e33da23f76d03,0x4fcff8f90a028d35f48f,0x3dc4461234c1f1111c47,0xf91fbf8d221a48d19ffd,0xffe64d966aa335259e64,0x7d0f226b4997fec80840,0x1033cfd61fe14209338,0x3e74fd10084044b7cbbd,0xb3cf5b2327e29902333f],#[0x19dbff8f50a5208808d6,0xfc7cbfa041253f9c1101,0xff12041287dd7a408f3,0xf9810332ceeb9811e7eb,0x802444fd0ffb81048497,0x22947dc4028f5fa28920,0xabe5c8084be48253e3bf,0x8db902213ffab1002043,0xfc188900806881fdf020,0x4527ef602507ef4904e0,0x34106a3fef9011227ba6,0xd904b4ff437230408767,0x8a22363c3e2450040883,0xbfe28c4469f8a22289f,0xabfe28c4471fc4464089,0x6afc20588cc3eb1c208c,0x5111ab87a610331e5612,0x614267451a903a465cfc,0xee26030287b7e2033028,0xde1500014b1efc0961fe,0x99854fe81cf82c0cb4f,0x27bc924d2501588a7274,0x63ef658e7292d234ae02,0x8e5fffe22b0aa89a7bd9,0xe9165fd1d8142c9ca834,0x975fb15042575831ce40,0x1898ddbf850a8862ccf8,0x1c62613f9fef800915ef,0x97af3b0209a644eca29f,0x44effe1a0d012134c7f,0x87f85189099f3d963dc4,0x643196f78c4b9ff74132],#[0x8819e177f0550a887efe,0xfebe581462246aefe359,0x7f3311234f7f1ad8cb9,0xff082a9986d6ee41f7fd,0x28cc04d53cff7b001201,0xc124c69b5b196bff954c,0x21021d75ad0459d78f76,0x3f4e1c2900510807f265,0x30388d2ff870a40143f,0x4a8cd5ff0fa42c202699,0x9785c44cfa22c32d0780,0x7fc600c2472e5f804099,0xebd9e2941248c617117,0x4f03c44e8ffdbc0c1005,0xebb449bc26872fd14499,0x8c14d0eafee893784d0e,0xe6d6655e269228bfe8bb,0x9a8c58d115ed20065efc,0x259977af13491b1f80d,0x557b480197bd025997bd,0x342fbf06e2b5d800004,0x28af5f859b066707ebe8,0x944ddd32c49943e9e7ca,0x215a58f7bda0000d4797,0x19967fd290923ebec200,0x92353577c02043067a4,0x22932cffa5212479ff0b,0xb1f888b3fe948491fbd7,0xd5c8357a1a0eece8d462,0x9289eaf29ca357a1a0d9,0x24ff858491ac3f44a7f5,0x584918563f0123779003],#[0xb824885cffa28332cff8,0xc3f44bda598e4cd245f5,0x5613e9a253e160b4899e,0xbd2d491cbd018d5955aa,0xc2266bd80962e539463e,0xb4208e0fc03ec6850fa8,0xdfb491478afda024893f,0x1fb9c6332e7f9f3332cf,0x1800244e3fea0c8c102,0x99025794001971feb064,0xc3ff148248f5fe089099,0x2fe8800239bf9f000810,0x9fb002468e5cbb081034,0x220ee10753fb0e084a5,0xf4e001021b5d5f7b8400,0xc198919e9fe282448557,0x8244854b7fd98919bb5f,0xdc20f5fc1988099e9fe2,0xc22607f02798c200a21b,0x3b841c1ff800000431f4,0xfe0cc48cf5ff06600467,0x1ebf833101339dc60dda,0x8357a1a0cf2e11337b84,0xc80091ef3ff2289d9d5c,0x610133d3fc504890bbf,0xb0923053fc308099ebf8,0xa5e80c7dfd7406655ff4,0x872ffd108761c2bda0cc,0xb285430007cafc4154c0,0x7f78a646f3ecd329bee2,0xc2b8a68cf3f0979c533e,0x14c85f3c39c53337d212],#[0xc4354cc9fba1aa66cfef,0xde3724654acd1674cbd4,0x4444465a24bcb14c939,0xda7a85ff800c19edffe6,0x9c06213668fdf15e0884,0x8e9c160c9efc24c2910c,0xc730644e392c8b1a3aa2,0x63b6587e48980411188c,0x86c7feeb7250195101d1,0xd209d60d4d26ffc73b8a,0xa54303ff35a482121e3c,0xffe1f3a8181a25cbe0d8,0x2950b5fc7fce62060692,0xe2a19bfb8ee34cd2f836,0x6a5746180ca86e7dfa6e,0x6550a862facbb7ecc06a,0xafafa032a1962a866fd4,0xd086894bddc2a1562a86,0xddc21e0b410d094e5e58,0x119638d118244f8d1108,0x88067cf6b7b0659f1a22,0xf1ffd01d00c0d31ff80e,0xb9226021a63ff01d100c,0x8a2f14c8f7b2c2a9213c,0x355178a64efb7ecc06a6,0xeac211b3f6fed03f1340,0xa3d6308ad2fe4f6a661f,0xa388fae4ee150b5cf04b,0xa17bcbc3531043481f1c,0x232a1a6e75ed1694cbc2,0x31180888ae78488fe006,0xb650464f5410ca4fe200],#[0x4efc00458df40a2a917e,0xc8c7e5244283a514f3a0,0x35afeb124789224c5c48,0xa1f9c31a47baad0e5c81,0x144a752c865b78313110,0xcebd264062fc828ba984,0x748aafd5c839fae2e246,0x7292dfef20d526d835d0,0xfc50ce19538e58daff7e,0xb6eaf2f8337738c206ec,0xb592472aa61e28574e12,0x9640f37634d5665943a2,0x607c4a28f3ecd326692,0x45ba1f5d5198510af223,0xcd511a27f9b1014a30a2,0x15ffdd25533424f0e97c,0xf2aa600682f81e954c4d,0x506a670cbeecd3307ff2,0x51796299162a87dff1d6,0x50cfe0866991ff325112,0x6fa051548beffc944491,0x2365f2ced3367f0aa994,0x4532c6748932ebfddc54,0xae60c6baf5fb7247cfe2,0xab3fcfa954cfaf554a84,0x7afdb923ae27c1f25c92,0x95cc348a668ce912655d,0x21b3ca1fca05ca080c0d,0xcbfe9a1a19e5ff04b280,0xa7f3830469fd479048f1,0x4ffe70c11242d7e97151,0xf0010b1f9a6aa51b3135],#[0x7150b1b7ff7b494cf8f9,0xe58191b0e5058660793f,0xff08102133c69afa9953,0x9faf40865a2beb82a16b,0xd1239e4892f3e401050a,0x626dff83084490b3fe1,0x8b3aa0d7ffe108449079,0x187c2043337ff7b494cd,0x50b1fe0913e9d280c0cf,0x63aa32ff26044bffa358,0xf22307dfdf0849b365ef,0xdaff7715093fac5c48ca,0x7fd67411124efcc5c48,0x6100828aeffc82a8091a,0xcab3fe53123d3fa8fc14,0xa38619132861933f8554,0x5466e2fff264a49481aa,0xb82cd9fc39988cd9d052,0x9a03ea36f9b223407c51,0x3db800533e613ffcc802,0x80153327ff990053357c,0x88d3abf9f73d22435bf,0x8cccf6e2a113db8fb36a,0x534cfa0151636d7cc,0x815534c206b0fe3e1f5d,0x894c7f42e6988d1dc7f4,0x19081a65fdd28b161884,0xa43ebbe4a40ce9efe5d3,0xba04c850d7f088cb9481,0x50a4715a9d5a26243c39,0x100ff9ad1126243cfd6c,0x87ac12423fed69913005],#[0xea12813497a652065dfc,0xa1b9c5d81200a1e311fe,0x951923f5e44cef9f1200,0x54655716def32890e5e9,0x91f9c5d81200a1cadf2,0x523357d05a919b7f534b,0x520670cb94323662f6cb,0x3597bf4e4a40cd1cba72,0x336bc1e1630810e1fe16,0xae8431f2748a03f0b732,0xa4695cd0cf7d3026e721,0x5080fa6eee150d3f4343,0x51fff60801950f4ff771,0x8451faa542a1bbd41a99,0x37011950ddffd066a806,0x2880fcbf86cd4840d36f,0x7f8994a87f76fc623100,0x81c459104a71aaa1c2d2,0xa4a686b7e864f7d344df,0x92a1e12faa0d3ae9f45,0x930f587092a181f0f587,0xd7d8a840d23fe2068664,0x1a01a22dd9aa183cfd,0x1fba408014437cf5fd50,0x9d1f8a8307cf34c28516,0xfecd20050c1fefc50589,0xdccb2fe2a0f193f1509c,0x7832c95ffd50065cff3d,0x9c7f55b453466508932e,0xed564bef9b888854307e,0xbff5a596490b3eb49691,0x7a6022103587a69840cc],#[0x3011081a89cf04ac5e7c,0xa00a243e3454652f3e3d,0x242010408af7f9bd630c,0x34522a18bf60969f96d8,0x9808840d0b1c988b8e1f,0x9224412579f25046affe,0x14c328028a03aae22ef5,0xf830531c9d913c3fe9e8,0x28523cffc0f0064907b2,0xe0b2afff6200c92167f6,0x98f0e00a99adb420fb9c,0xe9711f9fe4a684ac8408,0xa3367e5d840819c4f7d,0xa204881cd0c4462edeb0,0x342dbb7850615df36bc2,0x19957fc1fd0447845d26,0xa94840896d321b255bef,0xdcbc5f9321021c9e4dcb,0xc86c4d48d305fd94819a,0x48ce6fe51732890c9fed,0x9bd01e65121d3fdb1e0d,0x3c19448888fb41a919fd,0x213fb314122437bff086,0x8d59f41e80467972f224,0xe0ca244a69fed4e9a0d4,0x6f437c194489776ea351,0xca243c3e7c194486c7f6,0xc9122bb5f43328bda5e0,0x1a795a08a6ff451d7014,0x2fddc2c09121e0c5571,0xe37904637de5e1890811,0x4890cda643649e568228],#[0x4d0dd542dcc6787ebd10,0xa593e41aa3360785b401,0x8c244744a7a523848281,0x3657cbab58819f12a7d6,0x4373597e3e9acf214144,0x67da04068ef977ed8721,0x91b9ee90241470d99039,0x286e7ba409027f444204,0x2ffaa2021b7adcf08481,0x6cd2ef1fec8498687e7,0x294810233587ff3a28e0,0x2a7fa4fd020921fffb48,0x4ecd901a27eb29fc2841,0x406a4a7a8b73901a63f2,0xc4021010e5fa728d3020,0x406689f948219229ffea,0x689fac3f9c209196e715,0xe78e48cc935a7ced4020,0x11d901993b74c82334cf,0x66b0b57f0910c6884fe,0x377fab500819d3fa6964,0x964f74111d1ff8488634,0x6bea251b333f585e201a,0x541119b1bfc55559101a,0xa6aa088cd089fe2bd70f,0x1999bf8b15559101a9bf,0x38ff90fe5420935f5997,0xd70f4c2066cdba7988b3,0xd73f14446dedf114a224,0x26680086e74f1d9a0021,0xb3668008763d4051a3fe,0xd968a7274099c043abdf],#[0x1a34c815a8e9fd039f05,0x36e35a81a43fa74ef9aa,0x1a0bf98d3e6628692fc7,0xa7ec02426a2fb7b7399b,0x82149dffd90a247c2fd3,0x5bff73b30149338fcfd9,0xb031a03fb51a9c34884d,0x2f7fe7601433c7f97af3,0x7cdff6c7300c889f660a,0x104cf9febe581440c699,0xebff954c28818d21dfd8,0x2b70fa40c3329ea35011,0x9d9d26584044b7f94693,0xf873c40671bfcc08b2fd,0xfea59173338dfe6045a2,0x2189e1c18fa6308008a2,0xd45bfb20334a3e3cc200,0x1101febc746622680cf,0xa1d57fd022e315389b31,0x1fa46080529baade0861,0x8767f5e0985840044a,0x307e88800864707f0b08,0x6df3e18c4068fb88051a,0x640e380d4cad3f4c342d,0x95b19993fa656c2267ab,0xa8033d7bf1b40819e9bf,0x717fdb8c20021eb0a43f,0xd9b610a21ad9f6ed406,0x6507e2eec20021e107e,0x7083c1cdb0850f51fed4,0x199b3f9780099bee2014,0x63ecc180286876ffc310],#[0xc7ff3680c31a1e31a032,0xe31a03263eef00504287,0x3e1642d9993f10b48019,0xf1a910430d10bc4e4919,0xb6810346be5cb163436b,0x8b5f9cbf8b8903447ef8,0x352f057ec2090bff740,0x9786801a0bb57e3e1202,0x1e5f07cb08000441760f,0xfcb420069e7c91482002,0xb1fe7c925a1134b73f4d,0xfb7a6d0002685fd18115,0x8cedf0eb68000034a7,0x2edfd3680013427fe90c,0x10d10bd1c4c8cdee107,0x2cfdc7083529b9bf8484,0x496290d25785c9eecd22,0x521a1fbc8f2fc521fdcf,0x7f2383f15b437bc8f2fc,0x7c1471ed1cbc7b0556d6,0x65a1fbfd93c3c4e721a7,0x7fe4984490d18fed4444,0x869efcb44e19638c6b24,0xe5a1070cc9ff7fb128dc,0xc50694f1faf5475434f7,0xc222126a1b2ba7ff1d51,0xff2a540653035f67ff0a,0x252350d03aa3b346ec3f,0x688b01ad6347668c9e9c,0x39fe25d11733a53e10ed,0xfd4308f5fb7606f8820d,0x57603867c37a54309186],#[0xa18486e9e9da88acf9fb,0x486a8a5ffae3a15e1bd2,0x56c521441700fbd53f26,0x18fede065884d48c29c,0xe4c200d20863db14850e,0xff141eea52136a7d5fdb,0x4a7d5fdbe4c24d018275,0x94008a377401dda54414,0xe3f21592d3eea26a1375,0x8707b79246a4327af3,0x5b2f84b49068071ea0c0,0x97269f707aa290921443,0xfdbc4e9401a3923d1e03,0xe09686acfe03c50a4d11,0x34e7ff0e277109a9ced3,0x5000a27dc1eecc290a1d,0xf4269e90a1cd6f8aab3d,0x5d21d2134561c206ecc2,0xcfff7b198914293584bf,0x42856fffa42512a4526a,0x4a6bfc322061269f757a,0x20dd9b9d1fc996203014,0x3d34cb14ca060289ed18,0xdf108033bbff1c471014,0x25f7cbf6040f920d21e2,0x62f0010ebf91c4f09560,0x6ac76c42abc906af61f1,0x1a14812b5aa5d1c34568,0xf91fe95af0023036773c,0x4826974fa14be00486a6,0xc1891a970fffe6237ac6,0xc0b941981ae3ecdff015],#[0x37de17eb1b049efc7fd6,0x38184000234085fd1852,0xf062079449f7ec5164ec,0x88288acbd0400709a67f,0x14573fc32213dfe00a81,0xc48d1affe5558a81840,0x67fe7f416202684e7f4d,0x573fc322139f920c4143,0x1b49ff250090024e04,0xc0860efff8f917b01059,0xaf0ca305909b31fbf4f0,0xa125448e17b0498f97f5,0x15a5050c6045ad44f017,0xdff789e083d12581dfe3,0xe27143d004a51be7b047,0xc48094dfd25d7800cebf,0xabd3503932223783f79a,0x5d27fce056002105142f,0x2244cfefaabbcd0f4013,0x7c1891248bf2e3c0ac0c,0x4892f3f8561044268de2,0x483cd03b84dff785e20c,0xd3e19099a3ea80310b43,0x9dd27fce0e40420a273f,0x512385ec12abf405c5a1,0x127d9bf8a442001113ff,0x4d9abec0967fea37a1ec,0xe3d3cd3310144f75288,0x802d0a6b427fe05824cc,0xc4c851143cfd77814c7d,0x66efdb0e61733b3e26c9,0xf086c8000653b636f541],#[0xacb2354298f3408143ed,0xd26e3cd03215b1d7d4f4,0x82800894ff937d385400,0x7abd1826021cc6c7fe7c,0x3082141e84e951852885,0x6bae7fa43ed15134dbb3,0x285131f2a532fc5ba2a2,0xca128008d17edd703aa1,0x9a580286f6df9511e034,0x9a1c6893014d3784387d,0xbedbaa019852899bc21e,0x6109d0ccf7c19842743f,0x1ff80d31842602285f06,0x8f4cc20691bf64a42431,0x852f3e3d33081a18bcf,0xff41f033b09aadfab840,0x3782e499f3fd99006688,0x3b09a951737b08010e9c,0xd3e90cc93457ed3f1a43,0x35f79438c299d84d458,0xe001a13ff97cc1b02931,0x693f1b0100010e52ceb6,0x3737cabe7d48ee580413,0x6cefdf3ea477c480400,0xb800670fe5cc23890080,0x40011873e0604fd0e1,0xc30f000cd4f3f5c18650,0x7021c3f3f886908268cf,0xbff02804003443ea01b4,0xd7ff4cc20665e7c94119,0xebf93282347fa1475233,0x413a708c894ca5a643cc],#[0x406a82fe9840cc8fff42,0xb3e3200882c7f54c7c08,0xe7f0f1ca02011a41043f,0x2614890f6ff1a879e043,0x890fcf86c032890fcfe0,0xe6a88c130115cf86c032,0x6afcd5118c102245eb57,0x243bdaad1f89753808ad,0xf26ed4840879ffa16568,0x4c3c9cf7701309424533,0x4e41a09effd78922240c,0x3fddc04cd121eb4ff53e,0x817fc11e140e00980c5d,0x3de28a40cd3ff42cad04,0x8112ac94c1fe8c83011,0x5035881b0dffc53204cd,0xcca06b1036170f97866,0x784f7c14d0a0702e1f2f,0xfea690dd034217db972e,0xfffe784f7c14d0a06e0f,0xf0fd309fc14d0a070042,0x6204380281915982643f,0x1c4a5ef1bc2f08d8ff4,0xfb3c9cf02197afbc08f,0x50c829e1abf82406030f,0xb3fe0ab014089a3fa880,0x95914581103680c8c07b,0xc83a1f3fd321c06647f,0x9a140d6272bc4557f048,0x2cffe580a04367dddd86,0x89f61422aff0235d8509,0xc48408a741f123543448],#[0x9a98a1a244bbf12207a3,0x4e89d3ff4362ea4189fa,0x9f20d51995fcd4c40711,0x50944888d3ff439388ec,0x9ef2e284ac87d7e147f,0x977209a339ff2a14f31a,0xa983831552c74417f8af,0x8ad69821a554d2ff7d21,0xb9069cd634e2f20d0efe,0xd588240c10f5e1c87f8b,0x5f443bd1e5a5935a1cdf,0xb7b610be88378f17db08,0x93410f8e0a0516a1b1ea,0xcca9a5e8fa521b8ee86d,0x36540e6981109aae9f60,0xf82159f659ee1c043dbd,0x503f319c593014ea9ac4,0x5b518cf0022202f31a08,0xdb45eff0199b5d79939f,0x7c24606886ac7fa56021,0x435bf0663c46043d797c,0x5c9cf031711ef0b8aefa,0xbb2623c2c9e418b86f78,0xedcbb2e33a989c063825,0xa22c3ca0bb19392da23,0xfc77f4484581a51ec2d2,0xdf820cb2ba0f7c76b0f5,0xb49a09e3db7cb7614446,0xa2c8adf58511df4a6181,0x1d82c3a22f671d68a1e9,0x178edf1dc511ad9f743,0x61438bc9c3fce701439a],#[0x4e1f9734050d8c593b29,0xcfe801a03ca2e7f400d0,0x9d5ce7899eb4925ff79d,0xc8ff803386170e136a26,0x9676143ef91e96919330,0x15bb0a194f582a3155c7,0x52850caf081fd850d247,0xad6c3ae9f109a25f413f,0x7d70c6e909a703fc8a4c,0x1a73d42df7dda483562,0xeb30990a21bc7ccbbddc,0x45761e9a058b44d20eae,0x590a18d67b65b6a12b21,0x3a3f612c636c28897d99,0x4031fe8a192987d79d13,0xc5112ffb2232ba80110e,0x1b7e8606ac78bf36c0a2,0xcc1e3297d10ceddb5fb,0x69af9565c5099e36fd0c,0x2bcb84d35d26fc3f1400,0x48288cd2a010b3274c00,0x134d75e5c265e7dae99e,0xd7aafe800cf0dd5618b2,0x907ff19ad82360905141,0x378684d11f5ae2164006,0xa73bd43b798829b3c7e1,0x536da3a9ac8264ccda4c,0xd6434ba4164b8c870bd4,0x2776aebda5cce4cd0d1d,0xa2e8eaa802195fb7a74,0x5f518bfe006af726b801,0xc9fd0b8c80c914a183d2],#[0xe18bea7620f9c1a29d94,0x17d06244dc2ea2f91226,0x429de4649d49ee4d7002,0xb06c9ee5ee0672797de0,0x43fb9a49712810e8d1a,0x21c5826022342fe1ae70,0x2a1044043c7c083303fc,0x5a20fc10961e1eed2cf2,0x887f96d4640e04018a16,0xf80f7091cfe290832008,0x42aed32784e5006266ab,0x19900c4a24f2798e1074,0x189f2873]]
set_option maxRecDepth 16000 in
def g253H9 := limbs80 #[#[0x2301050e10005141008b,0x42902a04480102c2830,0x8005040801b02004810a,0x800008081001c482000,0x830e085800a247322808,0x14c0008322006111a0ca,0x2c10e0a002800a0000,0xec80011a081021e00101,0x2800b0004e061c106021,0x830e000828002080000c,0x1030e081802430204020,0x2040420d66046aa0001,0xa0000014120cd0000082,0x300000800080041800,0x60410202083800058401,0x18383023810e0e144810,0x118002140800c5d80564,0x90010700070014b07080,0x12d038102201091010,0x1081d282024000e78181,0x4181811804002382cb8,0x1039d00148280008080,0x683003c00616001420,0x2810074004063038008,0x602481054630381040,0xc0c89612241811200,0x202100000068012063ca,0x3400a891218009060038,0x6102850c00684100cb01,0x20405007000404000391,0xc180000c0010c0158000,0x3b00a649833e44801000],#[0x1430104046028f0288,0x2006b20c0c10000100,0x14a3f04280110a58a8,0x6008010435888102402b,0x4002340478002480010,0x40820024081060400112,0x200003c4071010007462,0xd2983b00c6644822a18,0xc0de4024803e8000085,0x85a6c01b0086c0000000,0x72e09cc,0x4322e4802380bb209c80,0x626e1817a2604c428e85,0x7478d23508523412b,0xc31111a0329021784b50,0x11450b98494e435f00,0x35188b6c046a2309836,0x69f12b18056c02380001,0x92043124060000000051,0x900542090000008ee010,0x561a261404bd1ac58197,0xea08d412ba98420160a,0xe8a1f427dc041085f102,0x44e0069a22490d80950,0x55a014113a28203444de,0xfd003209bf03d2253fe0,0x42613384083e0242926,0xc0b019c0327855d4095d,0x80000a560000aa11414,0x15ac000105ce491b947,0xc00451812e0a8710000,0x25082492317837800004],#[0x30526152708438131ca2,0x407b81e1151c4481e00f,0x490da05f0,0x50000000000000811000,0x10207d2a,0x222000061230035c0000,0x8,0x942ec00000000248d000,0x85f64aca81845497a4a0,0xebe46634ab3017da8ed8,0x4a93c0000040982,0x247d717eb0db11fc000,0x8c40810e283381209,0x1a0c80092e929c0,0x100a5003a00000000000,0xb5258ec03ff86440000,0x23c1138000302ae00000,0x41683c0e9c010f09ce12,0x529823e00002410,0x863b40e6482d8,0xdc8432049621f6c01b80,0x4b1ee04b05c2c0683523,0xf955305026001eb,0x788545d470e24ca22880,0x7136c0000c4066070824,0x218f,0x40383822d009a00000,0x7079d450205e300,0x509a8f4e0a07409a000,0x25100d50000012c2032b,0x240489635825de11e80,0x22e704c385050115800],#[0xb0a18d680ac8a840000,0x6e000062435029f208e8,0xf8146949aa06ac000046,0xae0000000000054e8cd,0x1d800010dd90000092a0,0xfe88e021980000000041,0x1297246764a83d0bdc02,0xd310800014c0609cf,0x1851042104082000000,0x186e296b800,0x667033708b358648000,0x208180000008100006,0x8d34225203f6a50400,0x4076414ee000,0x8ab15722a6100698048c,0x348ea11490000222f41,0x2038000041d384b1000,0x4098900ba00004093,0x80b7f02cd016881550,0x40000851a81278000000,0x1045884e14981d036,0x59b046480080000226a4,0x8839023e010ec53000,0xbf380be000,0x92fc492e05a24ab68c41,0x5330c7233e2805a04628,0x1028800f900000000203,0x24c358072d11d8000,0x54f0759447a0000c5008,0xec89d428800000000084,0x59403d000021250801,0x179802fe667a273000aa],#[0x740000000088d08894c1,0x1bd5822a1420704,0x283429f00000000012b3,0x41397030e01230,0xac0bc050b00000000000,0x426400c8c062a4122136,0x6b10ba50a548937004e5,0x5c2420017f907c529f40,0x805b409b8487001b688c,0x2750535406dc23a58102,0x2255f840c6162701e90,0xd43140000c0662937b41,0x234e53ed88aa9256a16f,0x50a451548e80156c10f4,0x800004a4d803d1502980,0x216100004943c000108f,0x1ec899380890000248e0,0x927000001,0xa375f419284640000000,0x220091f4034e01a0849a,0x1f0896403d5a22d81490,0x24505197921,0x94b400000000,0x629623a00001223e0098,0x1a88c400000000530341,0xa7aa46ae4c3f24ea00d,0x460940e298f13d80000,0x1a67182bac00eb03ab8,0x32281905f00000a8dc00,0x3919968000000000000,0x9fc05a583ca000004cbc,0xcc0a0496a102e701f044],#[0x408dc860d0495a0a,0xa480244c0fb000035088,0x101c225a740fba02ee1,0x51312118906120000000,0xeb80000000000000000,0x5900000066a5c5d81aa4,0x14500004a1f8000121,0xc4f70831c000,0x79608919240000000000,0x2e357101b80911000063,0x900de2036027d01ead25,0xc138623980001255a,0xa00000c30b0000201ee0,0x2136001e044860065048,0x2500000000000000000,0x2fa91ad02dc0000c8c4c,0x5c2610000050cc010f81,0x84000000000104b7121,0x1410fc0180000322de,0x580118cc72d258ab0f80,0x12583b40000442a347,0x35c2e8066483d,0x682a140ad926d0,0xe00000000609b5010000,0xc05010444b08000223e,0x3fc817e21ae54ba80000,0x80000004a610f5441b60,0x849b0000002060568012,0x9f680dda882c14c209a6,0x10a004b1b818808a050,0x90c6f81e744d78000000,0x19731368254000006902],#[0x3ae37e5219d89cae85e0,0x5806d20160031481b990,0xa55e50b4a0481437e80b,0xa4386220000000000001,0x40000000000000000031,0x820c52c69a8460938004,0x30e000001b1ea15b86f5,0x3f808e61076507800000,0x2803e8214218d1025ba0,0x181f988e6099cb042,0xa0913b40000812000000,0xfe15911084a21a523e25,0xd259000010d0540acc92,0x390000409a3401080fc,0x9220b040,0x3622185c8ad0000000,0x8ba019e08f1812a8000,0xe1621134267a16644d9e,0xd0071491eb00a4000042,0x2640000000000001027,0x4c8000000002404401e5,0x192170000000022,0x58f0000092500000000,0x426eb029a44740000,0x7850de00000000190d50,0xe0c72100480000000112,0x19d0e5dc6c6200d742b,0x1d80324063cc063426dc,0x4082800010218c8d529,0xa9888a76000,0x8fb617e800000000,0xcb065d80e00000000000],#[0x400000000003200003a3,0x25401480000c61f847e,0x308200000c0166,0xc0000429a740fb817a00,0x885600000000150e4095,0x27c0000a0f2000000001,0x9c02b8000000006285d1,0x101be933e409,0x53fab33f44a4191750a3,0x4030283a8000101000,0x80b7943fe4957143800,0xa16a21f000060770000,0x2012e,0x493000000a5dc44500,0x40b20000000000000000,0x20ee8000140e60000,0xc6801714bb049b000000,0xc11ab017ec8fe009b101,0x63004b4098940f18093,0xfe542fe407c003112aea,0x90000046280001a505c0,0x821d40b16486004a504f,0x10781cd004d80001507e,0x25d6190b0,0x8048c022800,0x12324811a0000,0x5a000000000000089a70,0xa22f0000298340000a1,0x4c360000000000000000,0x893a00002,0x980000000089d0404e80,0x6062e2b04007f802],#[0x2154109e908e8,0xa841c03de031f421e0,0x759680c7090588071c00,0x1017100004816,0x9aa80e00001864300fc0,0x84c3a110c0000000040,0xa0b7c11ca15080000000,0x8098800020078,0x242bd12720000427700,0x6245d098b81bada72000,0x4600003032600005274,0xf4444000004ce7c11f5,0x20000887b08017020226,0x4e28c21423cc4630041,0x7891bdb214bc077f0772,0xf21239037a0d71c8a6a0,0x4130609335469121d027,0xd0559046e0c2e9152,0x1800300002080504b80,0x4865c800400,0x21c80a58152cc40f8000,0x8f380602,0x24456000021a5080fa00,0x24367812,0xf89245c92f002b60b98,0x1c000082260b40c27644,0x14900000a1345309216,0x127e4204000000000000,0x48280001430008d21,0x28f200000000000,0xa48944c780000000,0x5e40001841cc12880000],#[0xc610ed02f60681c04e01,0x825,0xdc601fa1bf40000,0x1261602620000103ba0,0x122c981a250480000000,0x41840000000052ab8000,0x100104119a,0x42a800000000914b00,0xc45f407e80000000,0xa8ee800010024,0xb900138defc111800000,0x80000000100f60000201,0x2eb429cc000000000699,0xcc7080000000000004,0x1016000000000000d800,0x4c04920b447e2861958e,0x1070819956f80ec40893,0xd0a1ce014e8259c92e22,0x4c62209d1217856fc86,0x7b4081e0000,0x188370000109f34c400,0x949c934e684df0000000,0x229001960000a0f6a143,0x36022fe013f88cb93114,0x89402e4a27c63,0xa180000481240000000,0x22000086c6800000000,0x1701a08e5e6060000015,0x8b8c7544f81654438602,0x4f16065b0174217b410c,0x690000000860a5f82580,0x6865e802e0484a2a5f89],#[0x42ba61c10202074603b,0x10c2210db000000002,0x5c20ee4ac98277000000,0xc4938310b003ea08f912,0x11d2846b42ba8dc6,0xf4000068ee0000000000,0x29790000409e204,0x22600000c8488000,0xb87a03cd4fc8,0x7823900000048484c100,0xaa2644bf0082c0001958,0x8a401b000005446d13af,0xeb04ed254c00212886f1,0xe28d3547e90f2486f423,0x6640096402b8a5e493c,0xd06e0054021d0019e9,0x8470d0705227a00,0x61880000000000000000,0x311cf8512409ec001c,0x10000000000000000000,0x635098c0000c93,0x195000000002009a0000,0x42000088a74028a244a9,0x1005744de8000004,0x1092400000000,0x208000152ee0000425c8,0x900000000164a629fbc1,0x30966009,0x1927a0000000000000,0x2f441e80270afb000000,0x313240000c46d800,0xda00001028fa0440ac4],#[0x2400000036d407400004,0xe05f6405c602954c3d81,0xa92818f84e700002088,0x4b035e81c40000207f6,0x4d0000000008919cc,0x4210e84d8000024e6000,0xa64c0770000202d72837,0x8270a010603de0,0x92035848a40488000000,0x461c0000000000000884,0x8ffc0d9c,0x32282a09340000000000,0xa6740000000000001845,0xb1800000074030d80001,0xca3da8096c107000020,0x80000000000000000028,0x1162e408a,0x5e04ae8073e83aa00000,0xc00000000418b801bd80,0x408b614f,0x808000021570000603e0,0x54003000000000e86060,0x37580001224192d,0xf00088000000560000,0x1284520f36037400018,0x44adc4fca810800,0x1892100000000,0x40186319e254200000,0xb00002132098e1080a00,0x9062427ac103c006,0x523440000,0xd0000001d6c09b000000],#[0x108c000000000000605,0x1816c0000,0x1e000000000000002380,0xd807000004888211cb12,0x623e2479530b800025aa,0x81182266f,0x296cc00000000892680,0x51110000000300000000,0x48156481284ef,0x420228a060,0x20312023f4135c041400,0x3583002600000000622d,0x80ec13f6801900006,0xb910e000680000000000,0x8a744088a079243f20c8,0xc069823bd0c4c,0x103600a600e0880480,0x80000000000000000000,0x4136122400000000a0d9,0xe284d280003131a811d8,0x84,0x0,0x6740000a4a6c8d03075c,0x6800000000000028ed20,0x40101497100acc20,0x730000203bc0000,0x208904c88000323040,0xf115d8a1900000000000,0x2031c08e200002052,0x39800000000000000000,0xe000000003081ca97840,0x80f32233d0117823],#[0x614e00000,0x8623405e800000,0x800034100801b0000000,0x2a80002104400001021,0x5740cc0000003d9027f6,0x804f0000013d911ee10,0x481901c9000000000000,0x203e7882e0000685d2,0x20000000000000c29e00,0x6098e09fb0845031,0x1adc036e00a5000120aa,0x50000028ea906d450e10,0x30147009396288056601,0x443c000000000000,0xffc03ce22ea00f094fd0,0x806b6a1080000000050,0x817f8038800000000000,0x85aa3cc,0xc4000106254016d07a40,0xc255b0ab98178c49ec07,0x1a634400000000001e,0x80c0f280000526600005,0x448471b19f5010e40,0x8b600000403ac87f2120,0xc06bc2620,0x6006fe08362611000000,0x29ac138d48f10188807,0x24384bdc452811b00000,0x98000049002483400008,0x4000185d800006072922,0x8948e4820000000939,0x1c40242428bccc500006],#[0x84cb000000000841f49,0x856e00000000101a2000,0xac5891000004025c0c3b,0xfa0848008a0000231e40,0xa02100435ae30c52bc07,0x4b026316800201a14073,0xedd11f0000091a400000,0x48ac80000000089,0x9ff0504524cf02a0000,0x1d4902e80003,0x0,0xd1823b000,0x1242c0000,0x9a8a7b000060028026e0,0x140e280c91a748000008,0xcc0000858d00000000,0xe2c29e50b11020c00004,0x6202469c0000080,0x8fb012700003047a000,0x45368240444b5,0xc8000008d1c019000000,0x68162014009df0084c34,0x54ba50740000c017,0x481405dc0a5ca5490,0x985c448a46a96002f200,0x13f4000088d7405c1209,0x200fb8273c11ae00ee,0xd0000001e20000000000,0xc0020046400000205402,0xa23408ba927d0b71c5b3,0x10a7840938000000000,0x1029588d900000083400],#[0x42770000,0x80816f13de31ed80a70,0xb8b19c01e1135c00ea01,0x14684003609c8015,0x1b209330033a8476022c,0x1126a9421e45700,0xc2480000000008027000,0x322a02e4000180768498,0x630000404e10c1d0405c,0x81c881354958e096d89,0x108af027ac44f0000,0x22782340000046282888,0x9c18cf02bf9631000000,0x1909f0002a048,0x11e40ac0000215000000,0x901510000287ea03078,0xe04d280240000000000c,0x85b40000000000baa02c,0x35622d70c620000c047a,0xc00fa800034b63057200,0x44fd843cc81900001013,0x109f2029f800020a01,0xd902641273c13d800000,0x647e0000106298692c08,0x21840000086050000,0x5d000000002449885cd0,0xc805114c080003132a02,0x49d382140072e04ea020,0x29080aec0e721582,0x402c4000124e0000000,0x2176800000000000,0x4484e03dc80df],#[0x8000000000,0x221e200000000485c000,0xa04e00000000,0x77c0000000000000,0xfc2a560619088580c100,0x249010f800000000a52,0xc80b00002019b,0x1a21100b3800000,0x48ed03a189b9c693000,0x512961bb125ab0000,0x770000000020b82a83b0,0x2000000000000322a388,0x12e3282b28000124e,0x17302b444fe8454402a4,0x6848f7409025ac08d4e8,0xe03a00003084a027e407,0x40930081e1446c925d,0xbf812a0099a43980304a,0x3042e20534487487b669,0x19b408c60000c25be21a,0xb8c210e4b5e122200005,0xc020f6058e24a22a4d02,0x80691311a11ed0283807,0x1a98422c055494e00000,0x301a50190421b2a4c50,0x437b000000000461f000,0x617cd038c81290000,0x5e000000003050100880,0x9042792d8025d1623201,0x14438929e288b6096,0x24aada0468086a0308,0x2084c000011ac00c280],#[0x48d723e680fd000,0x247e903038501,0x1a62400cf8095050ce0,0xc04f34115020a8000000,0x18860041208540473030,0x95135cc00006,0x8031680000000008ad00,0x2a284301800020a83003,0x9e601430000228fd0386,0x3a1bdc08118043684ac0,0x20311150241e35312c36,0xb70a0800010266406c,0xe108d2ec35c034a209f8,0x809d690bf0000024b24c,0x603ae4ab,0x0,0xae11d704588005c90200,0x447c820e9013d8284c47,0x620000608130ad4814c,0xa0811880c88000183840,0x4ec002d8000231,0x4230028121900000000,0xeaa13a3448c006f00002,0x2c01fc46580000000004,0x841e2906c0001a56,0xc3b80fe000000003027e,0xfc000009a450b1c06d74,0x221e3046e0054813a210,0xa3e830d,0x930a0091701d306070,0xe0000000000000015600,0x1a9320000023d049b],#[0x4c00018234427b800a0,0x44,0x604ec00000000000,0x24d08ca58e243638503,0xca00b200004074800004,0xa095ba44dc245a18e100,0x14f844a8000090dae0a0,0x422ec00000dda00002,0xc0974007383b7010a00,0x82830057e24481928000,0x4287a0262107f,0x200ee1015161fc483c0,0x12b1200000000000,0xed000000000804c0000,0x284487a87ee0a2200020,0x105d90000000010be082,0x2a5022f8238211d0000,0x3232300bcc095803ed,0x4629d5001c08a38b1d00,0xe260e488600e98a5f829,0x2831d228121b8e0000,0xf888d010568314c0000a,0x102bba041941b011f404,0x46360095a13544528000,0x1e2181902da25ccc12f6,0x500002835c2036000081,0x25a540a10c3200000026,0x45200000000000031358,0x55135b04ea911a000020,0x3a18701540000144,0x60690000004550000]]
set_option maxRecDepth 16000 in
def g253D10 := limbs80 #[#[0x54510541105091048510,0x5d5105c9105951054910,0x5412050120dd510dc910,0x5c520595205512054520,0xdd120dc5205d5205d120,0x585505815054950dd520,0x5c9505c5505955058950,0xdd950dc950dc5505d950,0x5d9515c1515955158551,0x5c5655c165dd951dc151,0xbdedf9fe77dc565dc165,0xdff7edf777d7effbfafd,0xfabdff7bddf6b9fe7b9d,0xffffeff7fcfeffafdfef,0xacab018349ea9173508a,0xc216121081c1c6c59606,0xa12b72094b90515482c2,0x11586095bb04a5d828ac,0x2575013ba0095d002f0c,0x3820d3b90695c834eea0,0x860d3bb0695d8382ca19,0x7102c3825e001270c191,0x202c2101e1460f083058,0xc3c38a161c53aea28585,0x2c312160890f0c387821,0xb116adc4b52ea5595228,0x216add0b52e85c5542ec,0x16add8b52ec5c5652cbc,0xa75d4d0b0a917862cac3,0x75d4e0b0a985814c2c39,0xe1110f0288787382c39c,0xc560b0ca0581503c3221],#[0x9d72cabab725a2a92cad,0x53ee8a858674eb2ba160,0xb02f396560fbb2a75d9,0xf00c858678eb2bc1611e,0x2e2b8070bc0382e0998,0x3205827c2c0be1e09c0f,0x858690eb2c8160a44ac,0x87808c7c1c64e0638703,0x581a02c04a8e0e34f031,0x42082c0523e0e70b0540,0x60b4c105a5c82d2c4169,0x32ba0195500d30c1697,0xf2b10795083caea06565,0x2c30795d83cb041e5720,0xc282bdd415aea0dd5207,0x90975884cb022198704c,0x8bdd045ae82495412eb,0x8bdd845aec2496510dc2,0x661c45b0e21b8610cc30,0xe1065ae831b871174388,0x1065b0831b85196ba8c6,0x485f0a32d85196b28cbe,0x537042e581174c00ab59,0x330e2ad87156438b25d4,0x70439b87157c38aba1c5,0x43ad821cdc30eb5d873,0xa56951297c30eb61875f,0x5e9812f4b897a584bd2c,0x69862f4bb17a610bd2c8,0xf74316ba1995c4ccac26,0x76316bb192594c370862,0x7316c3986e18c330c62f],#[0x3d6ba9e6e1cc5d0e6198,0x4dc09ba600d5aca91b85,0xcc31ab5d8d92ca6d1643,0xb2a6b59505b0e69b8634,0xa9c6e10e370276980396,0x9c661ce5b0e72c873a4b,0x26e051370e72f8739743,0xbe0515b0289b86456bb2,0xe1915b0c8af84456c222,0xc57d300be9725b4b8acb,0xd73704baf725e4a92f95,0xa370ebae875ccc3aeb61,0x92cad1b82696b9352549,0x2c8aad6274dc334b5d9a,0xe8c6980624bb2b25d159,0x2dae87616c3b1261585e,0xdc9656cdc236b5d1b370,0xcb81664c0b26e19b5aec,0xb81735c0392e0999304c,0x82717c0b8b605c3704e1,0x2896b945958625f04e2d,0x84dc344b5da292cb11b8,0xf3c0c66e02397010c980,0x5b84cbe0235b011d7838,0xb94c6e0665ee332d719b,0x8d0b5c68370532f72996,0xd0660a85ee541981a17b,0xebe0a85b0542f81a16c0,0x66029af073e7719cdc04,0x5d41daca0af80a56c052,0xd84db0826d74136b209b,0xcdb042ed87136c309b5],#[0xcdb0c66d76336c219b59,0xdb0276d853f6b29fb61c,0xb0e76f843b6c21dbe04e,0xe4bed86476c0a3be1ced,0x336f719b6b8cdbe05cda,0x36f729b6b94dbe066db0,0x6d80a76c151be0a6db05,0x19c05200ec02b0058000,0x880d702f60ac025207b0,0xa13a84a8116842e0f283,0x1c086b81968602167054,0x38889820f87ee1e40746,0x8a6228589c625e89362,0xbe62e90b6c2cd0b002b,0xd963580d1c3370c7a30b,0x23b20e963970e263790,0xe41390103f58f903d68f,0x48a91d445e913043910a,0xf8939e4d8130a4b11268,0xc956854694b051c14224,0x172e5b1968858c15e856,0x8ee623184e60817d05de,0x6e68899e066c997c64b1,0xa6ff1ba66d81b146b01a,0x7879dce7561cfc72c1c4,0xb9fbc7dc9f2c7ab9e6a,0xfa21c866a15083920948,0xa43c8fb23728c622ce89,0x62497a258494da4e4923,0x469fd27a69cca6ce9a6a,0xea97a9e0a60a92ea3428,0xb1fac42afaab7eac9aab],#[0x832dd8b63ad56b412cc8,0xfaf76bccaee2baaae5eb,0x3118c3bb080c0fb014be,0x2a0c9a322cc7b3196c56,0x30cf5338ecd5b31acb8b,0x6d7e359ad5334f0d20b4,0xe04b7badd536deda7364,0x9039d0e64b916e2b3870,0x4bbacedc3b3cebb3a9ce,0x3d9ef4bbceef283c62f0,0xf90fd4bf20fb7be7cf7d,0xb104e40f10264034ff9b,0x50ce42f50a8c26508541,0x13ec4c9126c4310fa438,0xbf46af195c5ef16bc541,0xf48ed226c82f1f347691,0x4ac32a04a19270c98324,0xcd531ccc012e9cb652c2,0xcf3a4ce3b37c4d8f34ac,0x9413cfeb3e3cf4f3c14e,0x484d1c74625131438d08,0xf0d3794cb52df4a45251,0xd553353ed493515d41f4,0x57315b1567158c55c955,0x92f639587560157bf5df,0x356b85a9f6965a036635,0x5727dc51703dbcd6dbdb,0x7a4de4977c5d7f747dcd,0x37e0738055f897c95edd,0x962f58a0e20d86ae14d8,0xe567940e4a790fe3cf8d,0x7d39de67159ad6647977],#[0x1da6ce949a40e88da0be,0x7b0bebadad1ead5aa36a,0x8d30f45e160389b3a6c9,0xc2c3c10c2a303f8cc6e3,0xc5105018817638428547,0x101e1322012370d8d704,0xe91e5109a6e0f1308c6e,0x18a8148808ca186138,0x7889492a0a1124d23c06,0x7c14222529c517620aa8,0xd2114140102405a242b8,0x11ea2450aa2a1256c266,0x6a8e48c2d270330341a8,0x8006c031249245520844,0x48246a310c36618750a,0xa848020025887061c35a,0xd482cd4683487625828,0x2cb198564daa90b1e834,0xb0844ffe0c0b19833f8f,0x7411eb87c74620677518,0x60498f8f6e2066dfa73e,0x77ebc0e0824afefd7810,0xf20140080d323e86c11c,0x8251ffe8a09c6e6078f,0xf404149ec40ebf95e060,0xeb3631341ffe8a09ecff,0xd3404a59fefb61a3c63f,0x250ff1d9db4240ff1c08,0x3af7c41811c6bd558d40,0xae9fef88051a759202,0x54b5d63820905e3fce74,0x35bcef300a0fd3fafa00],#[0x23d79c610cb14e5f1b43,0x90bc7fb7448f3f5d840,0x387f4fb333433afb3ba0,0x7fbe0077a72026676d82,0x800507fcd20277fbe007,0x10342f3c4c2048b9fc,0x5c29472e992c656fe9c2,0x55fc7c84c8fa22391644,0x22a6461c54c8b9c302c6,0x890248e742514785289b,0x39d0991c751322af5e9a,0x14939a71699473a128a2,0xb1a660bd4c8bbfd449c2,0x88202437ac64b198238c,0x501407f564200679fd6b,0x512475ffe2cb14920bfa,0xb4f916be81821133afdb,0x38fd1282337a608ccb3f,0x1a77c08a1187ef81142,0xebed6200b335bfc1eb00,0xb198f71c136fea94411,0x4251847fe5010122bdb0,0x308edeedf789000d3339,0x819a3ffdb00b19a7ee52,0x3f84304e78b094bff082,0x3f84304f1fff20680067,0xe0316dc0273f3f421829,0x5fe8026331f2e1e09d9d,0xfda919819e2bd8b040cf,0x1bf2e2411e0fcb890488,0x6efea75047183f8cea09,0xff2a411cbafdc37f1034],#[0xdb881af72afa9b504a1c,0x91bf465520900d88f71d,0x40d6bf3054232de86da0,0xefc6d0462d36f7085a5a,0xcf0320204a0cfc0d294c,0x32928ff20140c0d2bfff,0x7afe57818904a3d0e7c5,0x72333613659ffe8a0a2,0x9118fe024cd168efea9b,0x4a8fc894de513c79b4e4,0x796223640261e53f8c27,0x455a489faab46e48dffd,0x200481a1f23820933d6d,0x6e14aafa132d0cf31e96,0xda24dcb3b851b7fcc0ba,0x80943978a26f1e5fbda6,0x7c67e804025cfb7d5b1c,0xfdba248dd627c608e3e0,0x13ebffc47a60249b97c,0xf13b44905fc05b9819a0,0x201357c578d08024afc,0xc4428080d13be73e21c7,0x2009007e7f0a0100965f,0x97f742f60800d2bf3f14,0xcab1fd822c7f8ca68333,0xe01471adb891bbf2e170,0x1c1610cc5df204cbc7ee,0x8ebc7eee01471cbc510a,0xe40a3977c8132fe66200,0xe00208e79cf8a13ac78c,0x507cc06daffb4000903f,0x1f6c47c00001a6f9ca50],#[0xff0209af3ec209df800f,0xbcfb082711ffd0000917,0xf1a0a1ffd801e7a1b046,0xf3d0d8231f390135ce,0x9225087b9998d052ffec,0x53334fb9e5e0321b5ee7,0x6f4fa01a19a2bff92354,0xff8b102333ce2aac0348,0xfb1d44c911f00c0b19b3,0x9bc52f2498239d094655,0x33d728607682269903f8,0x38f8116433407e591643,0x7fef95ab24acaf30996,0xb230fc583f8a5b9009a2,0xa00ffa0f876e49317a5b,0xafac59526700feb07a89,0x99679de440857e45248,0x5240f98b566cca4bcaf3,0xc0b19ba5e2d32af6bd9a,0xa60844d3de4b84cb1f00,0x26c4e7b2e104ce1fe673,0x42268c97ca0291c3042,0x5ea513b2e104ca1d7d97,0x258f9740299f56e02a30,0xfffc23652492f97e12a5,0x6f88291c7fdcf8249200,0x12813e8f0dad6c99a86,0x6de33fd12471bfe17c12,0x2471f827a40246e7c164,0x1124b8e1c97099b73e09,0x1ab46fa0291f293dc75,0xea5106b1a1d79d2a2208],#[0xcd2a22012f576614a385,0xaa1a2094a17a128cbf3f,0xa0903e46e0450923ff1d,0x23f821182e206ad53bc5,0x6cc050688fb43b00401a,0x2437fe1e085c00d05fe4,0x46d189c750481ff01900,0x901a4f0789032e8fe1d0,0x9c755d491c80d2f7a8b5,0x4412a3fae8c149fc4370,0xd80ce7f13382795d4ea9,0x7fdd59188209a9a9fe44,0x7282848b60e31402643e,0xd8cf5fb645af50340afe,0x24374de00199bf2fb6d4,0xc688d97d03265bd7fa20,0xabbb528cdfe9e2c6591a,0xfe7284a4d7f1384140d1,0x8d060012946f128abd8a,0xe86101237f8cd0023ccf,0xf388220917e2940a17e3,0xa57d0ca118719a8230,0x30293fe84c80527fd099,0x428249ff914c0a0ff645,0xf43608c1c9e84cbfe90c,0x673413e7fb423011034c,0x36efc609049bde634144,0x3b3c8195387185bd081a,0x84e1e2069dcabea74120,0xf220659fc72a411f32fb,0x5e61b104c1e63a208e18,0x8dffcf57984d04ad8fa5],#[0xc3d5e42150943e61d104,0x1861577fc56c0280806b,0x3a40cbbe2cc411ef7d39,0x4e6cc265df041c41243d,0xbe0f1046c35fa6081095,0x4abf4c1021203d3a40cb,0x2840d1177e6d047b7d98,0x3a6f71dc2840d45ed5d0,0xefe1b411c4983f1b4127,0xa0d9cf83289dfc36823c,0x7868049377fcc0ba6e14,0x157fc3908675ff1f9f30,0x8e60943fe5fa94ef0a50,0x81f5afa100499fcd7d43,0xa002006a1fe418df1824,0xf0f2cce73113567f194b,0xb924a0affc70b6cc269a,0xb2070dd400d5beb072bf,0x564923f84333c8a494df,0x7be10c0f665256fec0f7,0x8400d3bfff41eba29009,0x803dfb9c524969e9af5d,0x75e524a007fdce292499,0x52485ff738a49200eec4,0x3b71ef5549238439c46,0x18823efe3e543df0584b,0x34ee7d57986c412c78c,0x5460e4206a6fa7546049,0x212884dbf34b98280ff5,0xeff8adc5500d22787abd,0x10973f8dfd5e0a12884d,0x34ff4c5109037f57a425],#[0x1163f1b412]]
set_option maxRecDepth 16000 in
def g253H10 := limbs80 #[#[0x24168280615138480600,0xa06008080c100607002,0x506a5c0c8c8d0001201c,0x503c0230000940c271b0,0x80211c000b0100400000,0x200028102403068580a0,0x41221000200208008383,0x83e0280c24000785,0x1d8281c18000100c080e,0x17008013a2b02848804c,0x12000290854010202ce6,0x28342a2a004480105040,0x60081a001a020e405030,0x1018241c010003002310,0xe1701064000b08800320,0x47c1d01814c600009200,0x81c3c01008f4000b0080,0x88080a021f810070c,0x53702810190f8080000,0x2090125c06090493c02,0xc5493080045c290b10c,0x20012388804090a8,0x70001414030100034030,0xa198047e0444044d20,0xa32010181622049600,0x80c78330000008040c00,0x1583a00000a0a60c01,0x160a0088e00408000401,0x421e1880c400f0c8d434,0x442402000241c0d080f4,0x78706c251701c2203008,0x3273b4000f0b02880542],#[0x200021805e0101800564,0x4260b0082c4413002cc2,0x8346c080082816420290,0x3806c8c0a2e3041c0603,0x33240a0080e0702c5a6a,0xe000601806010b29000,0x34220b000cd6a020000c,0x999804050082c0a1b0f0,0x40b9dca8010e804021c1,0xe0f018ec000003004601,0x80a4b0080014300596c6,0x80006219c8080a0d0081,0x1181c00001d91c06032f,0x20390c4c0c0f804820c,0x6000000022091881402,0x4002b0a000220807038,0x894d8050100c5602010,0x401028ba0a00070022d0,0x826008b00a04090180a5,0xc26230603c0000010082,0x61c10330c07800211882,0x2782c06031c0040a0001,0x105028001d2c0083806,0xd02a0880038040c0244a,0x18189c060964c290a814,0xa83450907c87c00088a8,0xc058d40804030200c020,0x47a0c9d81c05332f46e2,0x40200010242a072d0c00,0x1801e0423848103c0000,0x18004a2124060105f0b,0x96e96c5654000580a00],#[0xc202561d41e000b87800,0xdc000808014101f060bc,0xb900615010a8027e0d0,0x90623400380000c16130,0x62819814001b0cb048a0,0x80211030782604008383,0x9589c4d1c9d03612641f,0x208186e24390049b721a,0x100868008f118049c28,0xa80000138aaaf2f1500e,0x812da5b890280013108,0xa6202f000c4010e376f8,0x1a10da000030127802,0xc5b02c6fd8151213508,0x7d30d40c937509a5244c,0x1c1ad4a230000040,0xeb081f928b4a00d18a06,0x9b6802c141162214220,0x6024ef81130811144083,0x1018ca20568044e07,0x38276b013a4a2c6014a8,0x90bc007e81b76022d105,0x4919a2018690dc4070a0,0x7142011a5346816fa12c,0xc000a008a0047a817c02,0xec206c891c56922d80be,0x5dea95a88144e479688,0x820181904ff8566c01f2,0x3d8022c064e81e2344,0x68a5dc85422980001b66,0x9f5c21860064287ea057,0x7a0feb0535c1130a2b8a],#[0x14e4041000000199045a,0xb45241819e0504817ae2,0x16e203dc1d1025aa1203,0xa1cb0021995b6316a521,0x8581df023f405e28811f,0x583817d800010dd7426,0xb033b411ee2055f20934,0x9c6061d00a8000c1886,0xa00004209304ca3412f8,0x48400002958d09690d07,0x404d6818a00000c04b28,0xb40025ea1b4800000000,0x80210000105e05180201,0x160000205748446607c3,0x742885ee23998118a03,0x2035209336207021dce,0x14b613dc0455a0594000,0x40057014e806e24,0x36929e5c06c5212a8000,0xf07fe81d1a06760a0880,0x91812372499684acb14a,0x41b1a00678084815ac40,0x623f3806a03142,0x5c00000108d919b800,0x78012e88dbc06c28149d,0x4c8111701c30869ea01,0xe0202421f90117c977b8,0x104752a7ab511fa02e,0x614d8000000001452580,0x6032091b26820e9205,0x7164777a8032061600,0x4189472959b895b80000],#[0x18026281678102815,0x56023b003e48043094e0,0x1d800001a157600d3117,0x5faa7ce8961d06bc4,0x42400002862e0000404a,0x802410935e01ad116670,0xdc8000025aa605a181b9,0x24b0000009781a4,0xcc0c7d403389092e04b6,0x74ac13d606142021a02,0xa61391f8e448480df9,0x20161040a80000000,0x18400e158a00001450e0,0x418066003cc41a88000,0x6b78cc5ff655cf8113c0,0xd9647f4055f647bc0569,0x93c623a800000000001,0x73093f0000091f4a0441,0x48454881ee46,0x140033112e0000081408,0x68a24882161a01dd211,0xb0024c803480a7800012,0x4da00004467e0000607d,0xc8636a5ac4123e854d20,0xfa0c56600c3207808007,0x70122a11d2081781,0xac0162826dc0000485a6,0x81f3815b000008134495,0xb80148a185043ed09d62,0x40d4832a0000604e3812,0xa0946ea2f4955fe1343c,0xe45145804fd81d9a071],#[0x8032401bba048aa562e2,0x8d2a63414a1880610903,0x81e480000c017c04be20,0xfc11a0a455c0000703a6,0x9021a20bf8198027,0x201be887ac23b8a04a0,0x97ec234e043980000000,0x604a1402df01e3c247a2,0x73e881b106df8983c245,0xca23b806370331a5b0a0,0x78a43434114c2619111a,0x28adc057e84aee8124a1,0xff40470479f88e8495a4,0x58c081f20653a5ab247,0x24690883b415d1c4022,0x10680443088a00000000,0xc0173c10a8248fe00108,0x59080ea07d885980173,0x8421304b89056481ade2,0x700019802bc06430053,0x928cc4858149420b482,0xb6843c00567001700768,0x81f48193403720d4b000,0xbd06d001a40000000004,0xd04021400bfe124d81c,0x400000147a812c806b99,0x774808b805c011b0ea78,0x6460615e66152a004de8,0x1a483108429c804a2160,0x81cd8967641cf904da01,0x63206900000000061427,0x4b000004024b00fd682],#[0xf0000000e80000111b68,0x500803a98d893fd803,0xec51ea45830050c44c82,0x35589776271711638011,0xe006a01ad047f2d14261,0x578859d8c53016d7c1b4,0x1334b23e81e62208880,0xc08955620b7000a60667,0x405b803d22604814da12,0x6a032fa15ec00a000001,0xe4b16b5802e802be88e,0xc045548560202e7055e8,0x3120a06d13cf51d62476,0x88818c1418c55dc1bc20,0x6237501132056b094c,0xa1f26969e8a01c251600,0xa6005e40770a0ed00001,0x112a1603e07f28815225,0x280000a17e602ae00000,0x6048a5fca0104019a00e,0x8405bc805a000010,0x5f20574c0370a4930000,0xe15e6803680000916760,0x683368889,0x0,0xe48804206ea805500000,0xa1c0493fa0000421,0x2108000000209a88408,0x2038000195e5e45c8000,0xda1a6800a600fa411908,0x61781268235601e5803b,0x80000287c80082000004],#[0xbb80000000000395c031,0x28000000405d591,0x1c0000245db05b570526,0x15c40147f32410071800,0xa85620c1c101089166a,0x40779c10de01a080e,0x910dbc865e89b9e07440,0x4a9087ea020500a6ea5f,0x19200e01810025e8,0xbd8841f81c7a03b80c0c,0x4fe10c40000706aa00,0xd101eb2009c807f61281,0x2814883de86c089874a2,0x49015d4056e86eb81186,0xb621739042280001898,0x1011045ffd04340,0x64f8037f450408828000,0x62074060448,0x9602a4a014e881b01ee,0x15e3001c80000224f200,0xc04080000899a80001,0x2736000010454c5b1800,0xbc000f00c3800018569a,0x9ffc24e2000004816005,0xfa98a510de947b603fd8,0x81094ba055490bf485f,0xa0651117980000a07ee9,0x6ee31450813402cf80e3,0x600ca09f3e041700,0x181bd6353980c188448,0x16bc80450821289f5000,0x602c5a1a9006fa096c7],#[0x64e0569007e00000000,0x2091a80774112002878,0x7690027a066200000000,0xa049c00004053d001150,0xee06a700ed281f78056,0x5013790856324141,0xa2898c0003a202168664,0x825e917bc10620000316,0xaf076220315475a00002,0x103c280a8539000a3810,0x40000201ef00f3a02ca8,0x64a201b295a681aee042,0x207bf01960039c2422e0,0xc2888028131e1743899e,0xa0306870500,0xff8565005990819a0486,0x579f91fb000005141a00,0xb224d381b7e015880008,0x1e0c12bc0088e23eba98,0xa000028472808e0466d9,0xb0013e047d880972351,0x205220812201d38527a0,0xa5c255e0000004b8a8ac,0x3412a00006a62b20,0xa680ada312a009dc13f8,0x36400000002a0000601,0x6006018cee0802e00006,0x92b603dac0402079e818,0x40039e0340208ec15a18,0x1ffa041605ecd1d12062,0x602812018c0782005348,0x22e203100f2a06a1807a],#[0x12f63351901cc214721,0x8437001340000200ab,0x6498803d8126341af800,0xdd44fe11ae9053800006,0xf2126c81808021b099,0xf8c036d1017a26d1a,0x63a0000604a321348000,0x800c4000020100ac0324,0xcc000000154204b5a1ab,0x8450000011220431381,0x4aa5657052e041d603d8,0x820600000000121f2c03,0x8810bd01126030400002,0x1ff00000000000001249,0x6054dc1113019f80001a,0x4cd09cb8000000004a5f,0xc15c8080c55c6813ce1,0x8b800018021c026d09ab,0x247481c82057801,0xb4480f407bbd04b00000,0x166a00004049981b1e07,0x100001a1240000000002,0x10de1009a962804f0900,0x8108000000000611f6a,0x9a84afc01d401030000,0x6926c25684a60d15b6c0,0x6e01940000201eb81f9,0x8031c0251101b2a1f732,0x6a00000000181ca8479d,0x1400000012860000207,0x624ea8100106b600007,0x13fc86d0000050732000],#[0x8176814ed81b6ea5858,0x80184028b00a10000,0x2271e0000001d8000000,0x25ca5b808f26830c0000,0x1792281281f70079055,0x621d3807800000,0x476181a68000080a5000,0x6353281168000000005,0x40820732892363152000,0xd41a9e06210a05c22578,0x454083a4969a11f36247,0xd06a1413f607a8857600,0x1d8038c0981c149a0089,0xc1aef056328ad0000130,0x268484a806b00948051c,0x86e325fd000010004c10,0x626148046a041c818de,0x17d00001a0fd00000000,0x5810e2004a853be00b31,0x25f014b40410a1b62070,0x195722028d81f341,0x22802450087a448e8067,0xa092a83fe00001075db1,0xae0000000014107c06f3,0x1c14f0033d51d2e03,0xd0000080a38047e81d00,0x465111f0496c111b,0xa0000420d5a1c1800000,0x5ce000060256095b0068,0x80000000000000000002,0x40800008959c2026887d,0x53500000c1b84268680],#[0xa005b4a02098d4c0034d,0xee81a64105e01c1846,0x78256180d6c03f645aae,0x8322053857d000010a0,0x1462043b91fb800009,0x2ec08af80431880fe01d,0x10f84c1a4001080,0xec407f789c8000018167,0x10de6c06308416c15800,0xf5805d280b2000000001,0x538801cc819e455,0x9f050000000000000000,0x191c05d2000000000240,0x100f76352e047e6061e8,0x68125a96949580c78103,0x692131082a017221bc82,0x1c2075e0000000018444,0x2022b0105014cf89,0x67002300398816e0925e,0x280441aca010a0dd0f05,0x30000001a5e074800000,0x4ed32067819700000014,0xca020c261780d7c01fa8,0x2d428ae8100680fc4834,0x1288529e243380f120,0x1be10a20000012b81186,0x31246049e0000005f988,0x9401aa2080b01f24060a,0x11b504980905f802b400,0xeb081800002109990a06,0x2a1fc042fa861e848,0xb89d96460029e54272a0],#[0x4b600004007000002128,0x500c401b00000015e702,0x698020000,0x84d28000000ad2207200,0x9f816680001255f4a793,0x121ff805c90490e03,0xae923a80496004784308,0x1984937601798000180b,0x78068c03d70096d04f81,0x58680b8002674490226f,0xa079b8150a126724f10a,0x210e991fea02f98124,0x8846000008152a079d42,0x4600c77547b04c700773,0x51941d2646c080f7e15,0x46a067a056082d7811f7,0x1b580576000024324893,0xb0564211ff040fa012d1,0x25f01bb4261001912067,0x1405c899f4c534000042,0xd8c06e5010be05efa95f,0x8544c80bf049a20538d1,0xbea113401318170c013b,0x10ce90618037d8079f16,0x1e017c09a5f137b052aa,0xea0204f301ac97fd00f,0xca183817402498407fa0,0x80bca125381edc071,0x1bd0a03c96ae000000,0x5400001001ea803b01a7,0x921805481204c45e900,0x219004c056100e15003d],#[0x20e9e86a22490825,0xc6121890fc420bd287d0,0x564200dc00006817b808,0x705b73011e940aa21a82,0x428459e205fe0c7e247f,0x8208e0000502d6813ea2,0xa128599a0110041201d6,0x10c8860c81f9e02468c,0x44521498000020819,0x13f5c507e9266c11f000,0xf084520000000e0015c8,0x58c60452000000552843,0x429ea033560000000000,0x10f814b80001400ee073,0x8112c1086907650090e1,0x26010a00171b16b680dd,0xc1aa0000128a36220089,0x688032516ba8117202aa,0x3fa00000164cb053092,0x6203d400002236789238,0x2005860558e02b1003,0x601380073b0096402c24,0x2322410a24f8203fe016,0x206bc4053247c8002920,0x215bf8415000000000,0xb5a82790543e925200,0x981ef201f081a7893fe,0x6eb12044820088e7204,0xfe26a2013b016d990221,0x1c5a9a03c1c10,0x981a3631578130202f00,0x656a486026b6288f414e],#[0x2269191c194768001b68,0x8894aac5d0646760000,0xa17c6114f80012922720,0xf481fe415ae093ea45eb,0x10b200003452608fdc93,0xa24333d04e64773094d6,0x8ac8040684dee2556112,0x3525682f5c5a8000002,0x111c7000010420806e,0xe225b89338853589dd80,0x41241a049800003086,0x8142a2621811c2080600,0x2c504d8281181ec00001,0x267580eee07a42490215,0xda05fd89db4073c04534,0x188c0164008580000912,0xa0000001520000600e48,0xa4150028800fb4458,0x44bf811b0032b813780,0xe6c26a1892f015bb8003,0xa8be207cb04256110d00,0x18020601b3155f682f1,0x852c41b0805284069000,0xc20692014c231f6011e2,0x201c084d1a0293c5f,0x80000490c58589800000,0x3cf01d40000081b3e46a,0x70128814ca20d208d969,0x290269d0107ca2be0405,0x8471440a080000a2c588,0xb90460401ab8562106ac,0x1a2256bc256b09e0c15],#[0x815c0437a0722a88c9,0x13ba174d09b360804000,0x62151088de26828,0x58121b78000091bf0000,0x3105f810f00000002380,0x1a0066f81dd00001842e,0x2c56424e6210a508,0x44000000000a16d60254,0x7a0912b601888140504,0x31072cc5ace459e00000,0x94aa05ab09c64002221e,0x48158a82440427e031a0,0x1040411283aa11018056,0x402e8811bc075d80f4c0,0x630070e85a9e06ae0430,0x223478178a100d91,0x500899615d489d280656,0x57a09a6c0689012e804,0x84407d41ac2103c2003e,0x14b800002420c054d808,0xe0000000018824644b2d,0xa5624528581c9a97f,0xc06480dd9423c101d380,0x9cc248505efb070bc0fe,0xc04942573088fe04c401,0xdb85e18000184384a2c0,0x271d0939440780000214,0xae07550075845f600000,0x174007c001ddc901521a,0xd4137805a881296020c8,0x7160121285830168806f,0xa06742048c029dc60020],#[0x9aa1f800426a6380177,0x197b1374a1817076e01,0x3c806e015398c3380000,0x5006841c107462de3816,0x8c4415ac7d88323a0470,0x8da1289852702629211,0xf093da25108c51c56d7a,0xa0d2824cb21bd9069,0x5075581160200d882080,0x908000041c1a066a0000,0x8a3d06d9a07f20686c4,0x4481a3800010919a42d9,0x24b801ba000000573c90,0x7800018155c035c00002,0x627a9a4106014791c,0xd0502017aa0fc800000,0x367900ac055c0dd9e90d,0x8109d80d10078c8d4860,0xe96019625664949c81e9,0xca6242b81b5e841008,0xab25a8e25a881c92130a,0x477f89022063e8099426,0x88581200001014a41582,0x49ba04ce00004159881a,0x481d8c0800841e800010,0x216112f0043601374079,0xf00da000061368892ba4,0xb6147609a96528a0145,0x44dda228c01d5a050f81,0x19942b06f2298b80001,0x27cd1164c03c3089e800,0x3806840000047f980846],#[0x1d74074c81f460511096,0x388bcf06b9055fe04055,0x480426e26fe81f16115,0xc55d309cd70149917621,0x890426880d8047df883e,0x21ba20055009e8000000,0xbb45aa4016a2528a0037,0x1010fe05,0x5a179809282012aa9e40,0x116604940000001cf805,0xe453a0824e000000000a,0x3228204c02bb80498855,0xe002da9f1603be000020,0xebe00910100e85642013,0x4d26000002196e26ce01,0x88d2005e880ae0926e,0x2569c092000000000000,0x3a06d41159240b08072a,0x15fc84d480eb4018f816,0x89aa424e6805280000a,0x41811f2814e0009f3450,0x287b200d5293cb049aa0,0xa0e00b5049fe0140857e,0x5374139401a54823028,0xed0077827e58005c8225,0x60e0060e86440841a00,0xd805d6004628771051f8,0x604003d00030c067188b,0x6816b0000109f2083551,0x245c5ac4076d0006c80c,0x2829f82040000000c9c1,0x2031805e58000141d4],#[0x801680296104c2468a00,0x71889e6261f81cb6037b,0x1099ec4775a414014,0xee06cb0134a04d9008f0,0x2020b9240d01532053,0x205faa8b3c06a48,0x88041f00001842e8250,0x8000180d422591082a20,0x6880001909b827e681f8,0x5f48843b89b90000191,0x980c2013f7414902044,0x1ff015f403001203207,0x316c291a2102458c09c,0x38e178c8070a002e000,0x301aca8108116bc45970,0x139412084693a0084440,0x4028221aee00f100d210,0xc0c12cc8119000010145,0x21f9a020608f1007d701,0x8811a8c076ec5ab00000,0x400a977a825d80b9a05,0x6a03340130a0299241f1,0x92642087404bca5d1a05,0x20186a05a41084635352,0x10201233451808ebc033,0x6036fa1c62065b11ecc8,0x1c204c9912d286a60000,0x17a253602034005925,0x9f8962e04eb2044216fa,0x14e7803ec229129e9e01,0x1e27f7801f01501208cf,0x1f1213799131c0546218],#[0x1057f0926b81f7e02e41,0x12980136a79800e58436,0x77a437a352b80b6e2,0x9e004d4017d400270983,0x159aa0048907b0159200,0xac280409245047b00558,0x258589bba03b601ca402,0x9e4398a9f7b050e800d6,0x414800008603807ec288,0xf012a01530053e201708,0x4718183314e000000246,0x6833001ab0141e011c88,0x3ac071220202d4a3b527,0x8125807ab00bd5167780,0x4ec51c00000a87fe27f3,0x24c184fc046dd006bc00,0xaa044b004f2a1fb89bc0,0x56f601f48525a20c6a5a,0x5a7612a921616062c8,0x7c78190601b000000071,0xe04a6c5a7f047e81e880,0xf22405a0346148080fc,0x812b286a081b3616de4c,0x2700dd4866f801900001,0x124a0000106c48482806,0x4e161680336036a01aae,0x9bc20c40208407e0001,0xb08516052081d2824a98,0x41ea075a456310ba0409,0x55b0550a06f11001a9,0xd880001216ae21ff8171,0x29f4001da80acd476400],#[0x930000000006920b,0x14c2a89f093f285e7800,0xe20738a0bb804460c7fa,0x11f2056e44fee86b2001,0x420c3256488733d,0x6800000415768167e06b,0xffb051700e420,0x20591a48bc06fe0000,0x119ec46d804410000000,0x4d200200001095664694,0x600d7013dc81,0x4800000000002a288378,0x1d4624c2000fe0331816,0x100d3a078b015c20784d,0x699840d60509001b8000,0x420ee11a3222f1009802,0x4e027240000005b408f3,0x89b2c033f95760000121,0xfb80fa8000180a42924a,0x6c10816c84cf00d5e27,0x4e94a115768225990547,0x2d398000000073855,0x4a16a005d800e1827300,0x73301c6116b8011ac01e,0x45a50848c2,0xa900000012ae204b8552,0x80c0a25640000003e184,0xe02050107160033e81a1,0x7fd0172a880091c4e86,0x3706a5000e48074084ac,0x95880001848c803e6883,0x50936203588122206110],#[0x880000210f6811d286e,0x800008150226fc019f48,0xf1800010069603158108,0x887f6169f09a4894a529,0xf20880244a018ac11c6,0x16da0000205b704fea02,0x4aa23581dfe00f385f66,0x9c4802748942817b781d,0x5002fc23aa9106a22540,0x51da13f402d20181423b,0xa04762411a1502889c86,0xac2273a20d4908029127,0x8120486fc01d6214c111,0x3d90820081e2173d0509,0x375a04d5b005a00486c5,0xe502420165e32ba08380,0x173646799186e02bca59,0xa24ef706f60058c15ed8,0x14cad71c826501afc077,0xc04670177403ef850e05,0xd64201685d56266e0169,0x88ee8082281be00123c1,0xcbc116803428926a0483,0x2c6919f417c42080a27,0xde1057008d8a5cd8139c,0x9fa0630a48cc907b095,0xcc51dc27f80a022063d0,0xac0041c15fa00e24015,0xa24720977a350081c564,0x5d8a5f48974226d8a0ac,0x9a202490044606d28d,0x44404f0937ba5aea00bc],#[0x120850863f80ec801,0xea00680989e02fd895f0,0x491026d7007d8925c80c,0x40000421f5813280000c,0x456a0b46801100c43003,0x8000021aa0227651d520,0xf2c053e00006255d9206,0x2880106e31173a86f008,0x7821094023425a9c1779,0x15c6850ee84f80572224,0x3b476f00b8e04e414d0e,0x206f07fc2006914d8241,0x10423a22343528547470,0x2a800000257181bd896a,0x9204806d00000857000,0x6070088f1c07870870,0x1848804c0d4e8566000,0x37a14f0023f047d00177,0x47e0a05f6024e01fbc35,0x4615ab80188000011a02,0x1aac267180de6823d001,0xa0045f06e980b40433b9,0x38001a0a021cc5005012,0xc0434814d612a781fa80,0xf90813cc0342118e115f,0x30684048f0005485ac80,0xe90146e852a8047247fc,0x7b24141607cf91f1800,0xc20185044fe033685530,0x62e042990d8a86b1a07,0x78082e03f94056412040,0x2f705e1605e10411a27a],#[0xc282109bd0407b009cc1,0x6c20608a086e47dd202e,0x91f9e054ea159a110a11,0xf589c2227d0809884071,0x158c899ca010d8416117,0xe402c900352204709064,0x80cac14000e9c131a088,0xc082cc3485056a043e58,0x7d510d68050615b70227,0x80490016be04f480a980,0x8d0263204ed824c7892e,0xd47ec07480b7217c701,0x79a1b0a8703007b20668,0x95ab21692d4a48205097,0xeb16c58078a03c9a1ab2,0x10ff075b816c403ab818,0x725ac80001918124302a,0x545094b0016c0195001b,0x2179d816109008000002,0xe8a007484b7820d80c03,0x80e9405b391e64032d00,0x8000040346210d0807c,0x414b20140967f883c825,0xe2281d85c3a651b09c11,0x19b4020121c5e0638314,0x800004013820ff0026b0,0x7d481ffca7dd81fd220f,0x28321043d200b9849948]]
def g253D11 := limbs80 #[#[0xdfdefdfd655455048110,0x5c82544248435407fff,0xb540b5008dd405d40dc8,0xdd485d48dd085d08dc4,0x15950dc915490dc53581,0x9595a5858dc18dd905d9,0x45080dc60dc20dd985d9,0xc544c5d4459445c84548,0x458545d4c594c550c5c4,0xc5c1c5d945c9458945c5,0x4dc645c64dc245c245d9,0xa1322183805106204400,0xc25349690f1f6398658a,0x861031e738e6c8cb17f2,0x16e2c3552a4539a53464,0x3dc776e49b6b4b64abf,0x89d730e4b47489508e0,0xb1b12e2d9faef56296d,0xa14411914221e003f1f,0x285100461827011c6f15,0x6c808c149a201cd04e08,0x49494145101008ea3e12,0xa01c88d45cdc5555509c,0xe04dfe2201453c3a8140,0x61c03208093cf019ee78,0x817e243ee944c17c2d24,0x3aff62048fe5a48a5f44,0x73f004a7f18413d9d12,0x517fe8104efe4057efc4,0x828bed0099e2053fa810,0xde374107f61b04e66607,0xe29f04d1ee413586c133],#[0x155fb9e8140a8fc0c389,0x401557f00305264e8618,0xbac5070fb8e362a37fc1,0xf770d4a04fd62491ee70,0x3fbb5282adf158024901,0xfbff2a042a3f32600a2f,0xa8fe6104dbf43a100901,0xa075c544c8249bde4a00,0xf055be2a742091639c20,0x1bfa186823df4c52]]
set_option maxRecDepth 16000 in
def g253H11 := limbs80 #[#[0x9220a2400c30030c1180,0x32053424830400440001,0x14100000114008529408,0x8800b002001015002000,0x50800010430451831410,0x10440004600528708024,0x83044041001001402001,0x40903020020490430401,0x50400000c02c051604,0x30811830462020000c0,0x10000ce0013820c04031,0x3c71850c94031090d800,0x810801401c100400530b,0x412cc00514604034d1,0x2080481c394008c1c100,0x421c4143361051585040,0xd92021090251450410,0x80000000000000000700,0x103e8000212100002854,0x8000009ad03f80090000,0x18481014a50ad402240a,0xf0290000014dc0000000,0x309e0000000000000244,0xb02d20ab50a480000000,0xc000000001ae56229822,0x1016622b7096c147,0x31262083501e40000000,0x10240433a02444bdc000,0xf0348000000000000000,0xa81ff044e04ec000269a,0xd0272191800000001016,0x3004a10a913cd0ab],#[0xb805c0178126e0ce8000,0xc496e02e40000048400f,0xb04d0053c000101dd153,0xe44d4000003040003550,0x800010a30440d241a21a,0x1891c0000000310f,0x222780002852904f,0x4000001ef045700b0000,0xf042c00030108846000a,0x9111600ac0003119d844,0x2815244a7208c03e6022,0x20402416c00000002448,0xc000103d2848723ca02a,0x4027404cc11cc000080b,0x40c3210a43d,0x100a000000000000,0x0,0xa0120000208bc0000000,0x302b71b20105,0xd1434000000020444000,0xa4c68be04175026,0x5340000821c0000000,0xf050d18ac00000003211,0x1238610d502dd004,0x40000000311d803b8000,0xc000212ec00000002532,0x49510a000000002422,0xe054a822e015c0000000,0x201f2091800000001022,0xd246f049c00000000000,0x42341a41545003808e,0x1032a444da26f18cca20],#[0x80002444000000000000,0x63b22030000008f3847,0x341cf448400004ab,0x52470000000000000000,0xb2ae8154000000000209,0xe44de11d5491d84a619e,0x10ac504520354421c12c,0xc0000000103b40000000,0x184c710d80002028,0x94268023204ac0000000,0x9532d8c332c4b04e3532,0x123213fb00bf20fd0b8,0x49cc000150e24091252,0x348d38ba0443,0x20e12e0000,0x4233c000000000000000,0xc00fe54fc00000001252,0xc0003040f133c00005ab,0x162000002626c0002252,0x3016d00c60b8f4194000,0x101c582001056003c102,0x103c2443c018401cb11b,0x400000002826d804a4be,0x28c0c000000000a0,0x14c30000281ec000,0x54818000303fc0000000,0x500f749d402bb0aea10f,0x181e40000000104bc014,0xc0000000101762ae0000,0xd215380003816,0xc00031cc800010004000,0x2117211ac000104eb035],#[0x80000000209eb0c4b404,0x120b000000100000248c,0x424fd421b109a0ba0000,0x9c05ce0000140ba012,0x1817412b,0xc0066042508500000000,0x201d4000000000003621,0x2211f000853200000000,0x32370000000035500000,0x10b1c00000000000,0x805813b0000,0xc0000000202c80000000,0xe2494000000000003025,0x2405088e44100001085,0x2846a13d105081028000,0x1253141dd251c0000037,0x4000000000002a070000,0x60ae0116a00440001009,0x6081e0b8442a94bdb21b,0x40003406f05380001125,0x8000000000000000084b,0x254e40001113b207,0x1fc000,0x30ab0000240240000000,0xe09f5037c00001398000,0x84b11410000112264c0,0xc000312bc52f00000000,0x10156104000020081129,0xc0336011d116213d4000,0x80000000000000003097,0x708552ad90a5c8860037,0x5139f21be08d3052613b],#[0x30b44003540d,0x800ec03f303e24538000,0x143b201ad051e84b,0x10252084e03c6844901e,0xb8071a4cd48c00001013,0x40000048853400002142,0x904281cd00002808e828,0xeb846f531,0x0,0x309f320920c040003049,0x1d814ec412c000,0x3112302fc00032484000,0x800010a5b09b30072236,0x30360000008800003418,0x81a033800000002086,0xe0410000008880000000,0xb236c00000001026813f,0xc22a9a4d604fc000311e,0x7c0000000303d,0x10ad8029400001044000,0x400000002013702c1806,0x109a908ca2314008f04d,0x160220235013a01d,0xc4548052800000000000,0x284cc0351047400012c4,0x200f302a9010c000,0x4ba0087b2394000,0x704a844bb0300000204a,0xc10cd202004620405440,0xb04b74116021d14a1041,0x209d7111a22d400030c0,0x428709cc00032074000],#[0x9000c000000015310000,0x1149c000101b,0xad2840c000,0x3226704b2845c0864000,0xc00000003104a0085406,0x48c10000140b0021a03c,0xc0389041423b00002038,0xd01800cd2012b11dd142,0x500180cc004e401b2215,0x203a80002818b422,0x4000201f902d70501291,0xa10e0000014c8000264d,0x9225701900003039500c,0x10c4c0c30000284d6406,0x21050000202380000000,0x8dd01c201a94524000,0x3a208000222f80000000,0x402580001031c0000000,0x4000009ba01f40003010,0x40000413352ee2a1e03a,0x9a4df2421143a440942b,0x239800022468051,0xf040b006c0000000311c,0x80000000224880001112,0xd104c000203d808c1030,0x504a404dc0001045e151,0x3193002f202e80003153,0x42280000000,0x0,0x80000000000000000000,0x100980002283300a,0xd52cc000000000000000],#[0xd41ff827b00780001047,0x2405c844149a,0xb13dc0000820b1478000,0x2202c00008b9e249,0xc000000000000027c000,0x212b8000122e,0x8038c4c13023c0000000,0x752e0000000020257107,0x205040000000264df2b8,0x80cf8039a84df2124000,0xc01a113cb0b0a102750b,0xf4824a4be452b404d23b,0xca21504640170004103a,0xb41c4000012c0533e032,0x140bd826,0x14044000301ce2514000,0x301b6044200e70380000,0x20117415284300000000,0x203400002242500c,0xb8c0710f000000000000,0x21a0c0002140ca21,0x8094c843c04780000000,0x4c00002027,0x14bc811cb029d0344000,0x10298000108e412c8000,0x30afa043400000000000,0xb0011129800000000000,0x184bc00000000041,0x113880002115181a7093,0x21a194453036c000,0x43301bf89d6896c026,0x182140000000],#[0x0,0x0,0x46800000000000,0xc000042ac00000000000,0x2043c0002035800004b9,0x80003447800000000000,0x8014c000000000001621,0x80000000200880001821,0x1019841340001135,0x78096039c00000b0643d,0x104d88c080003049824f,0x300cd23ed03c90540000,0x19c00000000000,0x301180001149303a0841,0x81a11244812460374000,0x8000000020368000304f,0x203ec000000000002006,0x5030d0217445c0003032,0x8000000030151213f00d,0x10318000181de08ae10b,0xb4c0700e000000000000,0x22ae702ee20e,0xc0000044818a80001011,0x248cc00000001426f806,0x60000248b0845,0x40000000281964048000,0x133b4be4000042008be,0x8000100205505046c000,0xb1a1c000000000001045,0x4047014fc5bcc000202f,0x804c944b4018e0a1841e,0x22e144b00003091ea1a],#[0x90b230051020a0910248,0x502cd05470266052f252,0xd80003113104f5409,0xa082513b954ef23b4000,0x203f40002005e2027484,0x4000122b288bc0203028,0x6228400000000052001a,0x1916320c000200b811b,0x24ab60ae400006bc9895,0xea1f6082f02e02038000,0x100b400000003009,0x80000000185380000000,0x9148c033f02ac0003405,0x800012ce0216704c44c0,0x80000000000002aab043,0x112f6012c000102f4427,0x323c310c54abc000,0xe446800010a4503b0000,0x80310003052dc0001a1e,0x2bc0002024f81a808a,0x222b9622c1137128d1a2,0x8017d150303640001014,0xd09da81d000022502084,0x2a2240001203c001,0x310cb531c00000000000,0xc147650a900550a70000,0x32198082a051410a,0x502b0000000000001021,0x7002709ed00000001531,0xb034c134da1eb8405022,0xb0a1e002f81f40002240,0x9033000000003141d1b8],#[0xc00010ce1028b09d2018,0xd0315007400022ad7120,0xd02a480900000000248b,0x800014862016303d6048,0xaaa121905124be,0x0,0x22da0206444a12f0000,0x400020058000240ac000,0x8000000030830000202c,0x7446c053009154953a22,0x36226024b00dc000123a,0x51397408c013f4018000,0x80001022382250017032,0x80000000000000391101,0x800020158000108b340c,0x6230400020480000302d,0x8484d2ce908cf04bb114,0x401e800000002806a81e,0x10028000211c60ad,0x30287230d01944461431,0x10a20000000008408000,0x40000000203bc0000000,0x78130000000000000852,0x14ac]]
def g253D12 := limbs80 #[#[0x65ff547fd50ff483fd10,0x9080071f7295b8dc03fd,0x91a282011cd8e223458,0x50e38f8d121058e007,0x2242801a38518846890a]]
def g253H12 := limbs80 #[#[0x40001009000003000001,0x1000146111660,0x20000000000000004000,0x1860000000383e92,0x4174030001807c8280,0x14982581c02468480000,0x45d0400000007,0x51980000000000000000,0x809000,0x10b800,0x42d000000000000000,0x681500600000000000,0x11000000000000000000,0xc0700000000000002176,0x40008010002018000161,0x687,0x104a00000050ac00000,0x1e098682020000080f80,0x80b604e4340,0x4a8e1520000000,0x380584c0138000000,0xdc930000000000000,0x409000,0x82f000008924e21f00,0x8e084c00000000000000,0x40d80000528212,0x90a80000590150000000,0x3548000000643c050118,0x0,0x0,0x1a40a4a840000000ab80,0xac0008],#[0xa400000020ca909c230,0x812e8e8000000,0x1002429,0x628603a00020d000000,0x26000033294800009d00,0x21bb08400000008,0xc282a000000223e2660,0x10170140000000004245,0x163a000,0xa3f41c000000,0x23c90e02b40e00,0x1b40b800145680483180,0x382a00000000000001,0x48180000000000000,0x40b545c0000000000000,0x98f8098017042000,0x20c000000000000000,0x30a48000620400000000,0xc800202200060e80010,0x8a00000000000000000,0xc0022a31200004080003,0x9b88c00068b501e000,0x2014000000018000,0x10af92f000000313d84]]
def g253D13 (j : Nat) := if j=0 then 0x30a20400e37f else 0
def g253H13 := limbs80 #[#[0x1820000000280,0x0,0x0,0x22300040,0x0,0x22b4a000000000000000,0x0,0x0,0x3a000000,0x251c080000000c1000,0x11000000000000000,0x20a0000000360,0x0,0x0,0x30300000,0xc0000000000000000020,0x4ac42,0xc2c0000000,0x0,0x0,0x10100000]]
def g253L : Nat → Packing
  | 6 => (7,7,6,0,0,8,0,g253D6)
  | 7 => (135,6,6,5505119,119,12,1234,g253D7)
  | 8 => (645,5,6,13566249,137,15,1424,g253D8)
  | 9 => (1042,4,6,7405810,120,16,1290,g253D9)
  | 10 => (339,3,6,1835050,86,14,1161,g253D10)
  | 11 => (49,2,6,327685,51,11,1075,g253D11)
  | 12 => (5,1,6,0,0,8,0,g253D12)
  | 13 => (1,0,6,0,0,0,0,g253D13)
  | _ => emptyPacking
def g253I : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupShort 3 47 0 9 3 4 g253H7
  | 8 => lookupShort 71 431 6 15 8 5 g253H8
  | 9 => lookupShort 451 2671 7 17 10 5 g253H9
  | 10 => lookupShort 669 3061 9 18 11 5 g253H10
  | 11 => lookupShort 229 1471 6 16 9 5 g253H11
  | 12 => lookupShort 33 337 4 13 6 5 g253H12
  | 13 => lookupShort 5 167 0 10 3 5 g253H13
  | _ => fun _ => none
def g253 : Forest := ⟨253,13,fun i => g253Y[i]?.getD (0,0),g253C,g253A,g253L,g253I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P6_0 : block g253 6 0 7=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g253B6 : block g253 6 0 7=true := g253P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P7_0 : block g253 7 0 18=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P7_18 : block g253 7 18 35=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P7_53 : block g253 7 53 82=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g253B7 : block g253 7 0 135=true := (@block_merge g253 7 0 18 117 g253P7_0 (@block_merge g253 7 18 35 82 g253P7_18 g253P7_53))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P8_0 : block g253 8 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P8_1 : block g253 8 1 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P8_97 : block g253 8 97 68=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P8_165 : block g253 8 165 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P8_261 : block g253 8 261 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P8_357 : block g253 8 357 90=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P8_447 : block g253 8 447 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P8_543 : block g253 8 543 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P8_639 : block g253 8 639 6=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g253B8 : block g253 8 0 645=true := (@block_merge g253 8 0 261 384 (@block_merge g253 8 0 97 164 (@block_merge g253 8 0 1 96 g253P8_0 g253P8_1) (@block_merge g253 8 97 68 96 g253P8_97 g253P8_165)) (@block_merge g253 8 261 186 198 (@block_merge g253 8 261 96 90 g253P8_261 g253P8_357) (@block_merge g253 8 447 96 102 g253P8_447 (@block_merge g253 8 543 96 6 g253P8_543 g253P8_639))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P9_0 : block g253 9 0 28=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P9_28 : block g253 9 28 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P9_124 : block g253 9 124 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P9_220 : block g253 9 220 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P9_316 : block g253 9 316 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P9_412 : block g253 9 412 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P9_508 : block g253 9 508 60=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P9_568 : block g253 9 568 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P9_664 : block g253 9 664 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P9_760 : block g253 9 760 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P9_856 : block g253 9 856 68=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P9_924 : block g253 9 924 96=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P9_1020 : block g253 9 1020 22=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g253B9 : block g253 9 0 1042=true := (@block_merge g253 9 0 508 534 (@block_merge g253 9 0 220 288 (@block_merge g253 9 0 28 192 g253P9_0 (@block_merge g253 9 28 96 96 g253P9_28 g253P9_124)) (@block_merge g253 9 220 96 192 g253P9_220 (@block_merge g253 9 316 96 96 g253P9_316 g253P9_412))) (@block_merge g253 9 508 252 282 (@block_merge g253 9 508 60 192 g253P9_508 (@block_merge g253 9 568 96 96 g253P9_568 g253P9_664)) (@block_merge g253 9 760 164 118 (@block_merge g253 9 760 96 68 g253P9_760 g253P9_856) (@block_merge g253 9 924 96 22 g253P9_924 g253P9_1020))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P10_0 : block g253 10 0 6=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P10_6 : block g253 10 6 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P10_102 : block g253 10 102 4=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P10_106 : block g253 10 106 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P10_202 : block g253 10 202 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P10_298 : block g253 10 298 5=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P10_303 : block g253 10 303 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g253B10 : block g253 10 0 339=true := (@block_merge g253 10 0 106 233 (@block_merge g253 10 0 6 100 g253P10_0 (@block_merge g253 10 6 96 4 g253P10_6 g253P10_102)) (@block_merge g253 10 106 192 41 (@block_merge g253 10 106 96 96 g253P10_106 g253P10_202) (@block_merge g253 10 298 5 36 g253P10_298 g253P10_303)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P11_0 : block g253 11 0 28=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P11_28 : block g253 11 28 21=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g253B11 : block g253 11 0 49=true := (@block_merge g253 11 0 28 21 g253P11_0 g253P11_28)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P12_0 : block g253 12 0 5=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g253B12 : block g253 12 0 5=true := g253P12_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P13_0 : block g253 13 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g253B13 : block g253 13 0 1=true := g253P13_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253T : checkedTables g253 13 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g253 0 0 0 = true)
  · exact (rfl : block g253 1 0 0 = true)
  · exact (rfl : block g253 2 0 0 = true)
  · exact (rfl : block g253 3 0 0 = true)
  · exact (rfl : block g253 4 0 0 = true)
  · exact (rfl : block g253 5 0 0 = true)
  · exact g253B6
  · exact g253B7
  · exact g253B8
  · exact g253B9
  · exact g253B10
  · exact g253B11
  · exact g253B12
  · exact g253B13
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253G : graphValid g253 (boundsBefore K235) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low253 : Lower true (varsX 253) (graphGoal 253) 14 := lower_forest (g:=g253) (i:=0) (hints:=132099) (before_sound K235 V235) g253G g253T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K253 := extendKnown K235 14 [(253,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V253 : Known true K253 := extend_ok (m:=253) V235 low253 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255R : Impossible true graph 14 sevenInputs.toFinset := by
  change Impossible true (graphGoal 255) 14 sevenInputs.toFinset
  exact cut_root (m:=255) (before_sound K253 V253) (2, 0, 253, 0, 14) (by decide +kernel) (by decide +kernel)

end PEqualNP.Outside.L_meta_52322

open PEqualNP.Outside.L_meta_52322 in
theorem PEqualNP.Outside.L_meta_52322 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o fit _ correct
  exact replaceShort g255R gates o fit correct

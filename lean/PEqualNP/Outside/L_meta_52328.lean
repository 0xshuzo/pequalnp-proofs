import PEqualNP.Defs

-- The two-mode live-state and cofactor checker follows L_meta_1674 and L_meta_670.
-- The graph, restrictions and all search certificates below are for L_meta_52328.

-- Shared forest and cofactor certificates from L_meta_1674 and PR 11111 for L_meta_1677.
-- The original credit line is retained below. The two root certificates here cover the unpinned graph.

-- The checker and the bound certificates are adapted from PEqualNP/Outside/L_meta_1667.lean (Apache-2.0).
-- Two modes: u=false are monotone runs (AND, OR); u=true are runs up to complement, where negation is free.
namespace PEqualNP.Outside.L_meta_52328
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
def graph : Sig := (BitVec.ofNat 512 (word80 [0xffffffff,0xffffffffffffffffffff,0xfffefffffffefffffffe,0xfffffefefefaeca0ffff,0xffffffffffffffffffff,0xfffffffefffffffeffff,0xfffefffffefefefaeca0]))
def sample (r : Row) (j : Fin 9) := bit r (inputs.getD j.val zero)
def edge (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 2) || (x 1 && x 3) || (x 0 && x 4) || (x 2 && x 4) || (x 0 && x 5) || (x 1 && x 5) || (x 2 && x 5) || (x 4 && x 5) || (x 0 && x 6) || (x 1 && x 6) || (x 2 && x 6) || (x 3 && x 6) || (x 4 && x 6) || (x 0 && x 7) || (x 1 && x 7) || (x 2 && x 7) || (x 3 && x 7) || (x 4 && x 7) || (x 5 && x 7) || (x 6 && x 7)
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
  (x 0 &&& x 2) ||| (x 1 &&& x 3) ||| (x 0 &&& x 4) ||| (x 2 &&& x 4) ||| (x 0 &&& x 5) ||| (x 1 &&& x 5) ||| (x 2 &&& x 5) ||| (x 4 &&& x 5) ||| (x 0 &&& x 6) ||| (x 1 &&& x 6) ||| (x 2 &&& x 6) ||| (x 3 &&& x 6) ||| (x 4 &&& x 6) ||| (x 0 &&& x 7) ||| (x 1 &&& x 7) ||| (x 2 &&& x 7) ||| (x 3 &&& x 7) ||| (x 4 &&& x 7) ||| (x 5 &&& x 7) ||| (x 6 &&& x 7)
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
  (x 0 &&& x 2) ||| (x 1 &&& x 3) ||| (x 0 &&& x 4) ||| (x 2 &&& x 4) ||| (x 0 &&& x 5) ||| (x 1 &&& x 5) ||| (x 2 &&& x 5) ||| (x 4 &&& x 5) ||| (x 0 &&& x 6) ||| (x 1 &&& x 6) ||| (x 2 &&& x 6) ||| (x 3 &&& x 6) ||| (x 4 &&& x 6) ||| (x 0 &&& x 7) ||| (x 1 &&& x 7) ||| (x 2 &&& x 7) ||| (x 3 &&& x 7) ||| (x 4 &&& x 7) ||| (x 5 &&& x 7) ||| (x 6 &&& x 7)
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



def target (x : Fin 8 → Bool) : Bool := decide (∃ i < ([0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)
def smallCircuit : Circuit := ⟨[⟨.or,[5,6]⟩,⟨.or,[7,8]⟩,⟨.or,[0,1]⟩,⟨.or,[2,4]⟩,⟨.or,[3,8]⟩,⟨.or,[1,7]⟩,⟨.or,[0,9]⟩,⟨.and,[13,12]⟩,⟨.and,[6,3]⟩,⟨.and,[14,11]⟩,⟨.and,[4,2]⟩,⟨.and,[9,10]⟩,⟨.or,[15,16]⟩,⟨.or,[20,17]⟩,⟨.or,[21,18]⟩,⟨.or,[22,19]⟩], 23⟩

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

def lowRow (i : Fin 8) : Row := Fin.ofNat 512 (1 <<< ([2, 3, 0, 1, 0, 0, 0, 0] : List Nat).getD i.val 0)
def highRow (i : Fin 8) : Row := Fin.ofNat 512 ((1 <<< i.val) ||| (1 <<< ([2, 3, 0, 1, 0, 0, 0, 0] : List Nat).getD i.val 0))

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
def g21Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x3ff63ff63ff63ff63f,0xf63ff63ff63ff63ff63f])),(BitVec.ofNat 152 (word80 [0x492049204920492049,0x20492049204920492049]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xc7fbc7fbc7fbc7fbc7,0xfbc7fbc7fbc7fbc7fbc7])),(BitVec.ofNat 152 (word80 [0x924092409240924092,0x40924092409240924092]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xf8fdf8fdf8fdf8fdf8,0xfdf8fdf8fdf8fdf8fdf8])),(BitVec.ofNat 152 (word80 [0x248124812481248124,0x81248124812481248124]))),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g21C : List ColumnInfo := []
def g21A : List (List Nat) := [[],[66],[32],[32,64],[64,32],[64]]
def g21D3 (j : Nat) := if j=0 then 0x7 else 0
def g21L : Nat → Packing
  | 3 => (1,0,1,0,0,0,0,g21D3)
  | _ => emptyPacking
def g21I (_ _ : Nat) : Option (Nat × Nat) := none
def g21 : Forest := ⟨21,3,fun i => g21Y[i]?.getD (0,0),g21C,g21A,g21L,g21I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g21P3_0 : block g21 3 0 1=true := by
  apply cellsBlock (ar:=3) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g21B3 : block g21 3 0 1=true := g21P3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g21T : checkedTables g21 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g21 0 0 0 = true)
  · exact (rfl : block g21 1 0 0 = true)
  · exact (rfl : block g21 2 0 0 = true)
  · exact g21B3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g21G : graphValid g21 (boundsBefore []) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low21 : Lower true (varsX 21) (graphGoal 21) 4 := lower_forest (g:=g21) (i:=0) (hints:=2) (before_sound [] baseKnown) g21G g21T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K21 := extendKnown [] 4 [(21,[]),(37,[84]),(49,[66,50,83]),(52,[32,16,65,49,83]),(69,[100,84]),(74,[16,50,100,84]),(133,[116,84,101]),(138,[16,50,116,84,101]),(145,[66,50,115,83,101]),(148,[32,16,65,49,115,83,101]),(161,[82,50,116,100]),(164,[32,16,81,49,116,100]),(176,[64,16,82,49,115,99]),(200,[48,16,98,116,82,84])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V21 : Known true K21 := extend_ok (m:=21) baseKnown low21 (by decide +kernel)
def g39Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfdf00fff81fc7e3ffb,0xe01fff03f8fc7ff7c03f])),(BitVec.ofNat 152 (word80 [0x45c09245142904808b,0x81248a28520901170249]))),((BitVec.ofNat 152 (word80 [0xe6a8703ffe007fc7cd,0x50e07ffc00ff8f9aa1c0])),(BitVec.ofNat 152 (word80 [0x96a9b6d618b228112d,0x536dac316450225aa6db]))),((BitVec.ofNat 152 (word80 [0xfbb781ffffff8007f7,0x6f03ffffff000feede07])),(BitVec.ofNat 152 (word80 [0x235249820c0312204,0x6a49304180624408d492]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x64ffe3ffffffff80c,0x9ffc7ffffffff0193ff8])),(BitVec.ofNat 152 (word80 [0x249204100400400,0x4924082008008000924]))),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g39C : List ColumnInfo := [(2,0,37,0,4)]
def g39A : List (List Nat) := [[],[32]]
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
theorem g39G : graphValid g39 (boundsBefore K21) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low39 : Lower true (varsX 39) (graphGoal 39) 5 := lower_forest (g:=g39) (i:=0) (hints:=82) (before_sound K21 V21) g39G g39T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K39 := extendKnown K21 5 [(39,[]),(71,[101]),(75,[16,50,101]),(77,[49,101]),(78,[16,32,48,101]),(89,[49,66,101]),(90,[16,64,50,32,101]),(92,[32,49,64,16,101]),(106,[48,81,98,66]),(139,[16,50,117,101]),(141,[49,117,101]),(142,[16,32,48,117,101]),(169,[49,82,66,116,100]),(232,[48,81,98,65,116])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V39 : Known true K39 := extend_ok (m:=39) V21 low39 (by decide +kernel)
def g43Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x2fc38ff01fff1ff02,0xfc38ff01fff1ff02fc38])),(BitVec.ofNat 152 (word80 [0x42ccdb2a5451240242,0xccdb2a5451240242ccdb]))),((BitVec.ofNat 152 (word80 [0xfdcbc7fffe07fe3ffd,0xcbc7fffe07fe3ffdcbc7])),(BitVec.ofNat 152 (word80 [0x1448490c1860408414,0x48490c18604084144849]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xece607fffff8003fec,0xe607fffff8003fece607])),(BitVec.ofNat 152 (word80 [0x8a7b6b06085892808,0xa7b6b06085892808a7b6]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x1b3df8ffffffffc01b,0x3df8ffffffffc01b3df8])),(BitVec.ofNat 152 (word80 [0x893124c08106003089,0x3124c081060030893124]))),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g43C : List ColumnInfo := []
def g43A : List (List Nat) := [[],[48,81]]
def g43D3 (j : Nat) := if j=0 then 0xf else 0
def g43L : Nat → Packing
  | 3 => (1,0,1,0,0,0,0,g43D3)
  | _ => emptyPacking
def g43I (_ _ : Nat) : Option (Nat × Nat) := none
def g43 : Forest := ⟨43,3,fun i => g43Y[i]?.getD (0,0),g43C,g43A,g43L,g43I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g43P3_0 : block g43 3 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g43B3 : block g43 3 0 1=true := g43P3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g43T : checkedTables g43 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g43 0 0 0 = true)
  · exact (rfl : block g43 1 0 0 = true)
  · exact (rfl : block g43 2 0 0 = true)
  · exact g43B3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g43G : graphValid g43 (boundsBefore K39) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low43 : Lower true (varsX 43) (graphGoal 43) 4 := lower_forest (g:=g43) (i:=0) (hints:=4149) (before_sound K39 V39) g43G g43T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K43 := extendKnown K39 4 [(43,[]),(46,[32]),(58,[48,81,32,66]),(105,[48,16,33,82,66,100]),(108,[48,33,16,81,65,100]),(120,[48,65,32,82,98])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V43 : Known true K43 := extend_ok (m:=43) V39 low43 (by decide +kernel)
def g53Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xdf7ec03c3ffe0fbefd,0x80787ffc1f7dfb00f0ff])),(BitVec.ofNat 152 (word80 [0x820404444444210408,0x8888888420810111111]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x1fbf43c3c3fff03f7e,0x878787ffe07efd0f0f0f])),(BitVec.ofNat 152 (word80 [0x40808888888420810,0x11111110841020222222]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xe03fbc03fc3fffc07f,0x7807f87fff80fef00ff0])),(BitVec.ofNat 152 (word80 [0x81011111110841020,0x22222221082040444444]))),((BitVec.ofNat 152 (word80 [0xffc03ffc003fffff80,0x7ff8007fffff00fff000])),(BitVec.ofNat 152 (word80 [0x102022222221082040,0x44444442104080888888]))),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g53C : List ColumnInfo := [(1,0,52,0,4),(4,0,49,0,4),(16,0,37,0,4),(32,0,21,0,4)]
def g53A : List (List Nat) := [[],[84],[66],[66,82],[82,66],[82],[32],[32,84],[32,64],[32,64,80],[32,80,64],[32,80],[64,32],[64,32,82],[64],[64,80],[64,82],[64,82,32],[80,32,66],[80,32],[80,64],[80],[80,66,32],[80,66]]
def g53D3 := limbs80 #[#[0x23ea6a1221e12148110,0x8028]]
def g53D4 := limbs80 #[#[0x2fd0910bd42443e48110,0x609085870]]
def g53H4 (j : Nat) := if j=0 then 0x7540 else 0
def g53D5 (j : Nat) := if j=0 then 0xd1027d10 else 0
def g53H5 := limbs80 #[#[0x110000000,0x8a000000000009308400,0x70000000600000000001,0x20800cc0]]
def g53D6 (j : Nat) := if j=0 then 0x3904f else 0
def g53H6 := limbs80 #[#[0x25003d0003100001a4,0xe00000000002800000]]
def g53L : Nat → Packing
  | 3 => (2,3,2,0,0,5,0,g53D3)
  | 4 => (3,2,2,0,0,5,0,g53D4)
  | 5 => (1,1,2,0,0,0,0,g53D5)
  | 6 => (1,0,2,0,0,0,0,g53D6)
  | _ => emptyPacking
def g53I : Nat → Nat → Option (Nat × Nat)
  | 4 => lookupWord 1 5 0 5 1 0 g53H4
  | 5 => lookupWord 2 31 0 9 2 3 g53H5
  | 6 => lookupWord 1 17 0 9 0 5 g53H6
  | _ => fun _ => none
def g53 : Forest := ⟨53,6,fun i => g53Y[i]?.getD (0,0),g53C,g53A,g53L,g53I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g53P3_0 : block g53 3 0 2=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g53B3 : block g53 3 0 2=true := g53P3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g53P4_0 : block g53 4 0 3=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g53B4 : block g53 4 0 3=true := g53P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g53P5_0 : block g53 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g53B5 : block g53 5 0 1=true := g53P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g53P6_0 : block g53 6 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g53B6 : block g53 6 0 1=true := g53P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g53T : checkedTables g53 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g53 0 0 0 = true)
  · exact (rfl : block g53 1 0 0 = true)
  · exact (rfl : block g53 2 0 0 = true)
  · exact g53B3
  · exact g53B4
  · exact g53B5
  · exact g53B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g53G : graphValid g53 (boundsBefore K43) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low53 : Lower true (varsX 53) (graphGoal 53) 7 := lower_forest (g:=g53) (i:=0) (hints:=2) (before_sound K43 V43) g53G g53T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K53 := extendKnown K43 7 [(53,[]),(85,[101]),(149,[117,101]),(165,[84,116,100]),(177,[66,50,83,115,99]),(180,[32,16,65,49,83,115,99]),(197,[100,117]),(202,[16,50,100,117])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V53 : Known true K53 := extend_ok (m:=53) V43 low53 (by decide +kernel)
def g101Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xf3e58e3ffc1ffcff3e,0x58e3ffc1ffcff3e58e3f])),(BitVec.ofNat 152 (word80 [0x200012490842080200,0x1249084208020001249]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfcfa71c7ffe0ff3fcf,0xa71c7ffe0ff3fcfa71c7])),(BitVec.ofNat 152 (word80 [0x400024921084100400,0x2492108410040002492]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xff0e81f8ffff003ff0,0xe81f8ffff003ff0e81f8])),(BitVec.ofNat 152 (word80 [0x804ec924a108a2a804,0xec924a108a2a804ec924]))),((BitVec.ofNat 152 (word80 [0x19fe00ffffffc001,0x9fe00ffffffc0019fe00])),(BitVec.ofNat 152 (word80 [0xa99c924c210c030a9,0x9c924c210c030a99c924]))),(0x0,0x0),(0x0,0x0)]
def g101C : List ColumnInfo := [(32,0,69,0,4)]
def g101A : List (List Nat) := [[],[101],[32],[32,101]]
def g101D4 (j : Nat) := if j=0 then 0x1f else 0
def g101L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,g101D4)
  | _ => emptyPacking
def g101I (_ _ : Nat) : Option (Nat × Nat) := none
def g101 : Forest := ⟨101,4,fun i => g101Y[i]?.getD (0,0),g101C,g101A,g101L,g101I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g101P4_0 : block g101 4 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g101B4 : block g101 4 0 1=true := g101P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g101T : checkedTables g101 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g101 0 0 0 = true)
  · exact (rfl : block g101 1 0 0 = true)
  · exact (rfl : block g101 2 0 0 = true)
  · exact (rfl : block g101 3 0 0 = true)
  · exact g101B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g101G : graphValid g101 (boundsBefore K53) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low101 : Lower true (varsX 101) (graphGoal 101) 5 := lower_forest (g:=g101) (i:=0) (hints:=2) (before_sound K53 V53) g101G g101T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K101 := extendKnown K53 5 [(101,[]),(163,[80,33,113,97]),(170,[16,114,50,83,101]),(201,[96,114,50,80,83]),(204,[96,16,114,49,82]),(225,[114,50,67]),(226,[16,114,50,67]),(228,[32,16,113,49,67])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V101 : Known true K101 := extend_ok (m:=101) V53 low101 (by decide +kernel)
def g31Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xc00fff0ffffffc00ff,0xfff0fffeea3a5303f03f])),(BitVec.ofNat 152 (word80 [0x84a08a210802284a02,0x80220882200a53145145]))),((BitVec.ofNat 152 (word80 [0xfff0000ffc3fffff00,0x3fffffc009adfd000fc0])),(BitVec.ofNat 152 (word80 [0xc42c405090b10c4b,0x11404108092d994d34d3]))),((BitVec.ofNat 152 (word80 [0xfffffff0003fffffff,0xc000fffd77e88afc003f])),(BitVec.ofNat 152 (word80 [0x90130026104c0100c,0x584120152a08828a28a]))),((BitVec.ofNat 152 (word80 [0x3fffffff,0xffff00012697f4000fc0])),(BitVec.ofNat 152 (word80 [0x2e09c08b8227026090,0x26009c11269264b2cb2c]))),((BitVec.ofNat 152 (word80 [0xffffffffffc0000000,0x39d530dfff000])),(BitVec.ofNat 152 (word80 [0x300e000c00380380e0,0x3808e0208d5104c30c30]))),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g31C : List ColumnInfo := [(0,2,21,8,5)]
def g31A : List (List Nat) := [[],[66],[49],[49,66],[32],[32,64],[32,49],[32,49,64],[64,32],[64],[64,49,32],[64,49]]
def g31D5 (j : Nat) := if j=0 then 0x3f else 0
def g31L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,g31D5)
  | _ => emptyPacking
def g31I (_ _ : Nat) : Option (Nat × Nat) := none
def g31 : Forest := ⟨31,5,fun i => g31Y[i]?.getD (0,0),g31C,g31A,g31L,g31I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g31P5_0 : block g31 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g31B5 : block g31 5 0 1=true := g31P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g31T : checkedTables g31 5 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g31 0 0 0 = true)
  · exact (rfl : block g31 1 0 0 = true)
  · exact (rfl : block g31 2 0 0 = true)
  · exact (rfl : block g31 3 0 0 = true)
  · exact (rfl : block g31 4 0 0 = true)
  · exact g31B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g31G : graphValid g31 (boundsBefore K101) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low31 : Lower true (varsX 31) (graphGoal 31) 6 := lower_forest (g:=g31) (i:=0) (hints:=4146) (before_sound K101 V101) g31G g31T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K31 := extendKnown K101 6 [(31,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V31 : Known true K31 := extend_ok (m:=31) V101 low31 (by decide +kernel)
def g47Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xf003ff87fe1fffc01f,0xfff87fffe474a4007c1f])),(BitVec.ofNat 152 (word80 [0xa12845108440228940,0xa01108826014a45294a5]))),((BitVec.ofNat 152 (word80 [0xfffc0007ffe1ffffe0,0xfffffc0335be20f83e0])),(BitVec.ofNat 152 (word80 [0xc030162028040b0182,0xc0a00108225922318c63]))),((BitVec.ofNat 152 (word80 [0xfffffff80001ffffff,0xf0007ffccfd11df0001f])),(BitVec.ofNat 152 (word80 [0x240980130884c0203,0x2c2120087c108a5294a]))),((BitVec.ofNat 152 (word80 [0x1ffffff,0xffff80004d2fe80003e0])),(BitVec.ofNat 152 (word80 [0xb82e045c111702c14,0xb005c104d26c9ce739c]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffffffffe000000,0x33aa61bfffc00])),(BitVec.ofNat 152 (word80 [0xc0300060001803018,0xc046021182211084210]))),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g47C : List ColumnInfo := [(0,8,37,2,5),(8,0,39,0,5),(1,0,46,0,4),(2,8,37,0,4),(4,0,43,0,4)]
def g47A : List (List Nat) := [[],[32]]
def g47D4 (j : Nat) := if j=0 then 0x5bd4940 else 0
def g47D5 := limbs80 #[#[0x240d140ff40fd40fd20,0x2012]]
def g47H5 (j : Nat) := if j=0 then 0xf else 0
def g47D6 (j : Nat) := if j=0 then 0x18989f else 0
def g47H6 (j : Nat) := if j=0 then 0x10dd000005a6c02800 else 0
def g47L : Nat → Packing
  | 4 => (1,2,3,0,0,0,0,g47D4)
  | 5 => (3,1,3,0,0,5,0,g47D5)
  | 6 => (1,0,3,0,0,0,0,g47D6)
  | _ => emptyPacking
def g47I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 2 0 4 0 0 g47H5
  | 6 => lookupWord 1 11 0 7 2 1 g47H6
  | _ => fun _ => none
def g47 : Forest := ⟨47,6,fun i => g47Y[i]?.getD (0,0),g47C,g47A,g47L,g47I⟩
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
theorem g47P5_0 : block g47 5 0 3=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g47B5 : block g47 5 0 3=true := g47P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g47P6_0 : block g47 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g47B6 : block g47 6 0 1=true := g47P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g47T : checkedTables g47 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g47 0 0 0 = true)
  · exact (rfl : block g47 1 0 0 = true)
  · exact (rfl : block g47 2 0 0 = true)
  · exact (rfl : block g47 3 0 0 = true)
  · exact g47B4
  · exact g47B5
  · exact g47B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g47G : graphValid g47 (boundsBefore K31) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low47 : Lower true (varsX 47) (graphGoal 47) 7 := lower_forest (g:=g47) (i:=0) (hints:=4146) (before_sound K31 V31) g47G g47T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K47 := extendKnown K31 7 [(47,[]),(59,[66]),(62,[32,64])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V47 : Known true K47 := extend_ok (m:=47) V31 low47 (by decide +kernel)
def g55Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfe1ff00ff87f87ffc0,0x7fc7ffffd3b94000f0ff])),(BitVec.ofNat 152 (word80 [0x1440a0a05101100285,0x2902008418941111111]))),((BitVec.ofNat 152 (word80 [0x1ffff0007ff87fff,0x8007f1fc231ee00f0000])),(BitVec.ofNat 152 (word80 [0x588ac4c5622a012b06,0x2b214491231ee7777777]))),((BitVec.ofNat 152 (word80 [0x1fffffff80007fff,0xfff801ff9c1f30f00f0f])),(BitVec.ofNat 152 (word80 [0x61030101800c220c08,0xc0188201c1602222222]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffe000000000007fff,0xfffffe000be4bf000ff0])),(BitVec.ofNat 152 (word80 [0x800c06060430443010,0x300200c20260b4444444]))),((BitVec.ofNat 152 (word80 [0xffffffffffffff8000,0x6442cffff000])),(BitVec.ofNat 152 (word80 [0x1008080040004020,0x40040100000008888888]))),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g55C : List ColumnInfo := [(2,0,53,0,7)]
def g55A : List (List Nat) := [[],[66],[32],[32,64],[64,32],[64]]
def g55D7 (j : Nat) := if j=0 then 0x3f else 0
def g55L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g55D7)
  | _ => emptyPacking
def g55I (_ _ : Nat) : Option (Nat × Nat) := none
def g55 : Forest := ⟨55,7,fun i => g55Y[i]?.getD (0,0),g55C,g55A,g55L,g55I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g55P7_0 : block g55 7 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g55B7 : block g55 7 0 1=true := g55P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g55T : checkedTables g55 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g55 0 0 0 = true)
  · exact (rfl : block g55 1 0 0 = true)
  · exact (rfl : block g55 2 0 0 = true)
  · exact (rfl : block g55 3 0 0 = true)
  · exact (rfl : block g55 4 0 0 = true)
  · exact (rfl : block g55 5 0 0 = true)
  · exact (rfl : block g55 6 0 0 = true)
  · exact g55B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g55G : graphValid g55 (boundsBefore K47) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low55 : Lower true (varsX 55) (graphGoal 55) 8 := lower_forest (g:=g55) (i:=0) (hints:=82) (before_sound K47 V47) g55G g55T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K55 := extendKnown K47 8 [(55,[]),(87,[101]),(93,[49,101]),(173,[49,84,116,100])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V55 : Known true K55 := extend_ok (m:=55) V47 low55 (by decide +kernel)
def g79Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xffc01ff87fc3fff00,0xffff1ffed2e680007c1f])),(BitVec.ofNat 152 (word80 [0x222894451108808a4a,0xa02444252268a5294a5]))),((BitVec.ofNat 152 (word80 [0xffffe0007ffc3ffff,0xffffe11773400f83e0])),(BitVec.ofNat 152 (word80 [0x40b018162050082c0c,0x2c140089146346318c63]))),((BitVec.ofNat 152 (word80 [0xffffffff80003ffff,0xff001ffce8f541f0001f])),(BitVec.ofNat 152 (word80 [0x84c120980261113010,0x30588900a8d154a5294a]))),((BitVec.ofNat 152 (word80 [0xf0000000000003ffff,0xffffe0005f98fe0003e0])),(BitVec.ofNat 152 (word80 [0x701c0e0438221c060,0x40600e104b9898c6318c]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffffffffffc0000,0x3280bbffffc00])),(BitVec.ofNat 152 (word80 [0x80201000400020080,0x80801000000021084210]))),(0x0,0x0),(0x0,0x0)]
def g79C : List ColumnInfo := [(1,0,78,0,5),(2,0,77,0,5),(4,0,75,0,5),(8,0,71,0,5),(5,0,74,0,4),(10,0,69,0,4)]
def g79A : List (List Nat) := [[],[49],[16,50],[16,32,48],[32],[32,49],[48,16,33],[48,33]]
def g79D4 := limbs80 #[#[0x9bd89544426d6215110,0x31825f635474]]
def g79D5 := limbs80 #[#[0x7c54443f280885bd4940,0xfea8885f95110beaa221,0xbd4940bfa8a81fb40502,0xcc8d018160c02faa3a07,0x882188201141080d176b,0xc110204810001]]
def g79H5 := limbs80 #[#[0xe800d9000000b10000,0x2200b0]]
def g79D6 := limbs80 #[#[0x540a0380ff40fd40fd10,0x3140cc503]]
def g79H6 := limbs80 #[#[0x309910020725c81002d3,0x18300000001c000000,0x78645a100071bc800000,0x3d99500000289]]
def g79D7 (j : Nat) := if j=0 then 0x1605f else 0
def g79H7 := limbs80 #[#[0x7e95999005c85540,0xa20000000c0000040882,0x6900000000000002,0x3d00000120]]
def g79L : Nat → Packing
  | 4 => (3,3,3,0,0,4,0,g79D4)
  | 5 => (10,2,3,0,0,7,0,g79D5)
  | 6 => (3,1,3,0,0,6,0,g79D6)
  | 7 => (1,0,3,0,0,0,0,g79D7)
  | _ => emptyPacking
def g79I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 13 0 8 2 2 g79H5
  | 6 => lookupWord 4 29 0 10 4 2 g79H6
  | 7 => lookupWord 3 31 3 9 2 3 g79H7
  | _ => fun _ => none
def g79 : Forest := ⟨79,7,fun i => g79Y[i]?.getD (0,0),g79C,g79A,g79L,g79I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g79P4_0 : block g79 4 0 3=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g79B4 : block g79 4 0 3=true := g79P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g79P5_0 : block g79 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g79P5_1 : block g79 5 1 9=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g79B5 : block g79 5 0 10=true := (@block_merge g79 5 0 1 9 g79P5_0 g79P5_1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g79P6_0 : block g79 6 0 3=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g79B6 : block g79 6 0 3=true := g79P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g79P7_0 : block g79 7 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g79B7 : block g79 7 0 1=true := g79P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g79T : checkedTables g79 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g79 0 0 0 = true)
  · exact (rfl : block g79 1 0 0 = true)
  · exact (rfl : block g79 2 0 0 = true)
  · exact (rfl : block g79 3 0 0 = true)
  · exact g79B4
  · exact g79B5
  · exact g79B6
  · exact g79B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g79G : graphValid g79 (boundsBefore K55) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low79 : Lower true (varsX 79) (graphGoal 79) 8 := lower_forest (g:=g79) (i:=0) (hints:=4146) (before_sound K55 V55) g79G g79T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K79 := extendKnown K55 8 [(79,[]),(91,[66]),(94,[16,32,48,64]),(143,[118])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V79 : Known true K79 := extend_ok (m:=79) V55 low79 (by decide +kernel)
def g103Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfffc03fe1fe1fff00f,0xf87f87ffff856420703f])),(BitVec.ofNat 152 (word80 [0x50282814404400a0a0,0x51011002098064049249]))),((BitVec.ofNat 152 (word80 [0x7fffc001ffe1ffff0,0x7ff87f01c9c9c381c0])),(BitVec.ofNat 152 (word80 [0x60b03058828042c0c1,0x620a01042181c98db6db]))),((BitVec.ofNat 152 (word80 [0x7ffffffe0001fffff,0xff80007ff233d69c0e07])),(BitVec.ofNat 152 (word80 [0x80c040600308830101,0x800c2208021380892492]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xf800000000001fffff,0xffffff80013c2ae00ff8])),(BitVec.ofNat 152 (word80 [0x50282811411140a0a,0x500050402c02724924]))),((BitVec.ofNat 152 (word80 [0xffffffffffffe00000,0xce2917ff000])),(BitVec.ofNat 152 (word80 [0x60303001800180c0c,0x4604460846010724924]))),(0x0,0x0),(0x0,0x0)]
def g103C : List ColumnInfo := [(2,0,101,0,5)]
def g103A : List (List Nat) := [[],[101],[32],[32,101]]
def g103D5 (j : Nat) := if j=0 then 0x3f else 0
def g103L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,g103D5)
  | _ => emptyPacking
def g103I (_ _ : Nat) : Option (Nat × Nat) := none
def g103 : Forest := ⟨103,5,fun i => g103Y[i]?.getD (0,0),g103C,g103A,g103L,g103I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g103P5_0 : block g103 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g103B5 : block g103 5 0 1=true := g103P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g103T : checkedTables g103 5 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g103 0 0 0 = true)
  · exact (rfl : block g103 1 0 0 = true)
  · exact (rfl : block g103 2 0 0 = true)
  · exact (rfl : block g103 3 0 0 = true)
  · exact (rfl : block g103 4 0 0 = true)
  · exact g103B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g103G : graphValid g103 (boundsBefore K79) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low103 : Lower true (varsX 103) (graphGoal 103) 6 := lower_forest (g:=g103) (i:=0) (hints:=82) (before_sound K79 V79) g103G g103T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K103 := extendKnown K79 6 [(103,[]),(115,[66,50]),(118,[32,64,48])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V103 : Known true K103 := extend_ok (m:=103) V79 low103 (by decide +kernel)
def g107Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xff003fe1ff0fffc01f,0xfff0fff0d97f0000f0f0])),(BitVec.ofNat 152 (word80 [0x2a0a814412200a8541,0x41220022993600333333]))),((BitVec.ofNat 152 (word80 [0xffffc001fff0ffffe0,0x1fff0fff3c14bb0f0f0f])),(BitVec.ofNat 152 (word80 [0xc0301880402030181,0x80402040180413111111]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffffe0000ffffff,0xe0000fff23b566f0000f])),(BitVec.ofNat 152 (word80 [0xb02c0a0058442c0602,0x5844280213164666666]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffff,0xfffff000134bf8000ff0])),(BitVec.ofNat 152 (word80 [0xc0b02c116088b02814,0x16000b040249e8cccccc]))),((BitVec.ofNat 152 (word80 [0xffffffffffff000000,0xcea8c5fff000])),(BitVec.ofNat 152 (word80 [0xc030018000c03018,0x18088c08468880888888]))),(0x0,0x0),(0x0,0x0)]
def g107C : List ColumnInfo := [(1,0,106,0,5)]
def g107A : List (List Nat) := [[],[80,97]]
def g107D5 (j : Nat) := if j=0 then 0x3f else 0
def g107L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,g107D5)
  | _ => emptyPacking
def g107I (_ _ : Nat) : Option (Nat × Nat) := none
def g107 : Forest := ⟨107,5,fun i => g107Y[i]?.getD (0,0),g107C,g107A,g107L,g107I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g107P5_0 : block g107 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g107B5 : block g107 5 0 1=true := g107P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g107T : checkedTables g107 5 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g107 0 0 0 = true)
  · exact (rfl : block g107 1 0 0 = true)
  · exact (rfl : block g107 2 0 0 = true)
  · exact (rfl : block g107 3 0 0 = true)
  · exact (rfl : block g107 4 0 0 = true)
  · exact g107B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g107G : graphValid g107 (boundsBefore K103) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low107 : Lower true (varsX 107) (graphGoal 107) 6 := lower_forest (g:=g107) (i:=0) (hints:=4149) (before_sound K103 V103) g107G g107T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K107 := extendKnown K103 6 [(107,[]),(110,[32]),(122,[64,32])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V107 : Known true K107 := extend_ok (m:=107) V103 low107 (by decide +kernel)
def g109Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xff007fc3ff0fffc03f,0xfff0fffff1de0200f0ff])),(BitVec.ofNat 152 (word80 [0x120900881220048480,0x81220020908602111111]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffff8003fff0ffffc0,0x3fff0fff2435bb0f0f0f])),(BitVec.ofNat 152 (word80 [0x240205102402090105,0x2402040203111222222]))),((BitVec.ofNat 152 (word80 [0xfffffffc0000ffffff,0xc0000ff01bb564f00000])),(BitVec.ofNat 152 (word80 [0xb82c1600b8442e0606,0xb84428219b560777777]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffff,0xfffff000134bf8000ff0])),(BitVec.ofNat 152 (word80 [0xc0b05822c088b02828,0x2c000b040348e8cccccc]))),((BitVec.ofNat 152 (word80 [0xffffffffffff000000,0xcea8c5fff000])),(BitVec.ofNat 152 (word80 [0xc060030000c03030,0x30088c08460884888888]))),(0x0,0x0),(0x0,0x0)]
def g109C : List ColumnInfo := [(0,8,37,64,5),(8,0,101,0,5),(32,0,77,0,5),(1,0,108,0,4),(4,0,105,0,4),(64,8,37,0,4)]
def g109A : List (List Nat) := [[],[32]]
def g109D4 (j : Nat) := if j=0 then 0x57d4d10 else 0
def g109D5 (j : Nat) := if j=0 then 0xc8404fd10 else 0
def g109H5 (j : Nat) := if j=0 then 0x8 else 0
def g109D6 (j : Nat) := if j=0 then 0x232a8bf else 0
def g109H6 (j : Nat) := if j=0 then 0x9 else 0
def g109L : Nat → Packing
  | 4 => (1,2,3,0,0,0,0,g109D4)
  | 5 => (1,1,3,0,0,0,0,g109D5)
  | 6 => (1,0,3,0,0,0,0,g109D6)
  | _ => emptyPacking
def g109I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 2 0 4 0 0 g109H5
  | 6 => lookupWord 1 2 0 4 0 0 g109H6
  | _ => fun _ => none
def g109 : Forest := ⟨109,6,fun i => g109Y[i]?.getD (0,0),g109C,g109A,g109L,g109I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g109P4_0 : block g109 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g109B4 : block g109 4 0 1=true := g109P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g109P5_0 : block g109 5 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g109B5 : block g109 5 0 1=true := g109P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g109P6_0 : block g109 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g109B6 : block g109 6 0 1=true := g109P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g109T : checkedTables g109 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g109 0 0 0 = true)
  · exact (rfl : block g109 1 0 0 = true)
  · exact (rfl : block g109 2 0 0 = true)
  · exact (rfl : block g109 3 0 0 = true)
  · exact g109B4
  · exact g109B5
  · exact g109B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g109G : graphValid g109 (boundsBefore K107) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low109 : Lower true (varsX 109) (graphGoal 109) 7 := lower_forest (g:=g109) (i:=0) (hints:=24578) (before_sound K107 V107) g109G g109T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K109 := extendKnown K107 7 [(109,[]),(121,[66]),(124,[32,16,65])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V109 : Known true K109 := extend_ok (m:=109) V107 low109 (by decide +kernel)
def g117Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfe07ffc07f3f9ff01,0xfcfe7fc7f4800f00f0ff])),(BitVec.ofNat 152 (word80 [0x204104081020100204,0x8040080000111111111]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfff81fff803fe7ffe,0xff9ff8e150f00f0f0f])),(BitVec.ofNat 152 (word80 [0x408208102040200408,0x10080100000222222222]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xf00001fffffc007fff,0xff001fff0a2f00f00ff0])),(BitVec.ofNat 152 (word80 [0x810410204080400810,0x20100200000444444444]))),((BitVec.ofNat 152 (word80 [0xfffffe000000007fff,0xffffe0001e5000fff000])),(BitVec.ofNat 152 (word80 [0xa082142850a8550a1,0x40a014125e5888888888]))),((BitVec.ofNat 152 (word80 [0xffffffffffffff8000,0x19bfff000000])),(BitVec.ofNat 152 (word80 [0xc10418306030060c1,0x82c1582499b888888888]))),(0x0,0x0),(0x0,0x0)]
def g117C : List ColumnInfo := [(32,0,85,0,7)]
def g117A : List (List Nat) := [[],[101],[66],[66,101],[32],[32,101],[32,64],[32,64,101],[64,32],[64,32,101],[64],[64,101]]
def g117D7 (j : Nat) := if j=0 then 0x3f else 0
def g117L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g117D7)
  | _ => emptyPacking
def g117I (_ _ : Nat) : Option (Nat × Nat) := none
def g117 : Forest := ⟨117,7,fun i => g117Y[i]?.getD (0,0),g117C,g117A,g117L,g117I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g117P7_0 : block g117 7 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g117B7 : block g117 7 0 1=true := g117P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g117T : checkedTables g117 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g117 0 0 0 = true)
  · exact (rfl : block g117 1 0 0 = true)
  · exact (rfl : block g117 2 0 0 = true)
  · exact (rfl : block g117 3 0 0 = true)
  · exact (rfl : block g117 4 0 0 = true)
  · exact (rfl : block g117 5 0 0 = true)
  · exact (rfl : block g117 6 0 0 = true)
  · exact g117B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g117G : graphValid g117 (boundsBefore K109) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low117 : Lower true (varsX 117) (graphGoal 117) 8 := lower_forest (g:=g117) (i:=0) (hints:=2) (before_sound K109 V109) g117G g117T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K117 := extendKnown K109 8 [(117,[]),(229,[116])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V117 : Known true K117 := extend_ok (m:=117) V109 low117 (by decide +kernel)
def g167Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xff0ff01fe3f8ffe0,0x3fc7f1ffd675000f00ff])),(BitVec.ofNat 152 (word80 [0xa0a20a14148120142,0x82902402163411111111]))),((BitVec.ofNat 152 (word80 [0xff000fffe003ff1fff,0xc007fe3f317a00f00f00])),(BitVec.ofNat 152 (word80 [0x2c2c42c18590a04583,0xb214084b17a33333333]))),((BitVec.ofNat 152 (word80 [0xffffffc001fff,0xfff8003fede10f00f00f])),(BitVec.ofNat 152 (word80 [0x303083020600c48604,0xc01890829c122222222]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffff0000000001fff,0xffffffc01388f000fff0])),(BitVec.ofNat 152 (word80 [0x404004040801000808,0x10020010000044444444]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffffffffffe000,0x2816ffff0000])),(BitVec.ofNat 152 (word80 [0x808008081002001010,0x20040020000088888888]))),(0x0,0x0)]
def g167C : List ColumnInfo := [(2,0,165,0,7)]
def g167A : List (List Nat) := [[],[117],[32],[32,117]]
def g167D7 (j : Nat) := if j=0 then 0x3f else 0
def g167L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g167D7)
  | _ => emptyPacking
def g167I (_ _ : Nat) : Option (Nat × Nat) := none
def g167 : Forest := ⟨167,7,fun i => g167Y[i]?.getD (0,0),g167C,g167A,g167L,g167I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g167P7_0 : block g167 7 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g167B7 : block g167 7 0 1=true := g167P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g167T : checkedTables g167 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g167 0 0 0 = true)
  · exact (rfl : block g167 1 0 0 = true)
  · exact (rfl : block g167 2 0 0 = true)
  · exact (rfl : block g167 3 0 0 = true)
  · exact (rfl : block g167 4 0 0 = true)
  · exact (rfl : block g167 5 0 0 = true)
  · exact (rfl : block g167 6 0 0 = true)
  · exact g167B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g167G : graphValid g167 (boundsBefore K117) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low167 : Lower true (varsX 167) (graphGoal 167) 8 := lower_forest (g:=g167) (i:=0) (hints:=82) (before_sound K117 V117) g167G g167T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K167 := extendKnown K117 8 [(167,[]),(199,[101]),(203,[16,50,101]),(205,[49,101]),(206,[16,32,48,101]),(234,[48,81,98,66])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V167 : Known true K167 := extend_ok (m:=167) V117 low167 (by decide +kernel)
def g171Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfe1ff007f87f87ffc0,0x3fff8ffc48be5000f0f0])),(BitVec.ofNat 152 (word80 [0x5442a1505109100a8a,0x85092009489a53333333]))),((BitVec.ofNat 152 (word80 [0x1ffff8007ff87fff,0xc07ff1ffbb19600f0f0f])),(BitVec.ofNat 152 (word80 [0x1880c0606202010303,0x6020410290941111111]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x1fffffff80007fff,0xff8001ff941fb0f0000f])),(BitVec.ofNat 152 (word80 [0x610b0582802c222c0c,0x82c48a01416b6666666]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffe000000000007fff,0xfffffe000be4bf000ff0])),(BitVec.ofNat 152 (word80 [0x800c06030430443010,0x103000c20264a4444444]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffffffffff8000,0x6442cffff000])),(BitVec.ofNat 152 (word80 [0x1008040040004020,0x20400100000008888888]))),(0x0,0x0)]
def g171C : List ColumnInfo := [(1,0,170,0,5),(2,0,169,0,5),(8,0,163,0,5),(32,0,139,0,5)]
def g171A : List (List Nat) := [[],[48,81]]
def g171D6 (j : Nat) := if j=0 then 0x4689f else 0
def g171L : Nat → Packing
  | 6 => (1,0,2,0,0,0,0,g171D6)
  | _ => emptyPacking
def g171I (_ _ : Nat) : Option (Nat × Nat) := none
def g171 : Forest := ⟨171,6,fun i => g171Y[i]?.getD (0,0),g171C,g171A,g171L,g171I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g171P6_0 : block g171 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g171B6 : block g171 6 0 1=true := g171P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g171T : checkedTables g171 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g171 0 0 0 = true)
  · exact (rfl : block g171 1 0 0 = true)
  · exact (rfl : block g171 2 0 0 = true)
  · exact (rfl : block g171 3 0 0 = true)
  · exact (rfl : block g171 4 0 0 = true)
  · exact (rfl : block g171 5 0 0 = true)
  · exact g171B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g171G : graphValid g171 (boundsBefore K167) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low171 : Lower true (varsX 171) (graphGoal 171) 7 := lower_forest (g:=g171) (i:=0) (hints:=4149) (before_sound K167 V167) g171G g171T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K171 := extendKnown K167 7 [(171,[]),(174,[32]),(186,[48,81,32,66]),(233,[48,16,33,82,66,100]),(236,[48,33,16,81,65,100]),(248,[48,65,32,82,98])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V171 : Known true K171 := extend_ok (m:=171) V167 low171 (by decide +kernel)
def g181Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xc0fc0fc0fdf81fbf7f,0x3f7efec0007c00f83ff])),(BitVec.ofNat 152 (word80 [0x820820820810410202,0x8204040210842108421]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xff000fff01ffe03fbf,0xfc07f7f400f801f07c1f])),(BitVec.ofNat 152 (word80 [0x41041041020820404,0x10408080421084210842]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffff00001ffffc03f,0xfff807f81f003e007fe0])),(BitVec.ofNat 152 (word80 [0x82082082041040808,0x20810100842108421084]))),((BitVec.ofNat 152 (word80 [0xfffffffffe0000003f,0xfffff803e0003fff8000])),(BitVec.ofNat 152 (word80 [0x104104104082081010,0x41020201084210842108]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffffffffffffc0,0x3ffffc0000000])),(BitVec.ofNat 152 (word80 [0x208208208104102020,0x82040402108421084210]))),(0x0,0x0)]
def g181C : List ColumnInfo := [(1,0,180,0,7),(4,0,177,0,7),(16,0,165,0,7),(32,0,149,0,7),(128,0,53,0,7),(5,0,176,0,4),(17,0,164,0,4),(20,0,161,0,4),(33,0,148,0,4),(36,0,145,0,4),(48,0,133,0,4)]
def g181A : List (List Nat) := [[],[117],[84],[84,116],[116,84],[116],[66],[66,117],[66,82],[66,82,114],[66,114,82],[66,114],[82,66],[82,66,116],[82],[82,114],[82,116],[82,116,66],[114,66,84],[114,66],[114,82],[114],[114,84,66],[114,84],[32],[32,117],[32,84],[32,84,116],[32,116,84],[32,116],[32,64],[32,64,117],[32,64,80],[32,64,80,112],[32,64,112,80],[32,64,112],[32,80,64],[32,80,64,116],[32,80],[32,80,112],[32,80,116],[32,80,116,64],[32,112,64,84],[32,112,64],[32,112,80],[32,112],[32,112,84,64],[32,112,84],[64,32],[64,32,117],[64,32,82],[64,32,82,114],[64,32,114,82],[64,32,114],[64],[64,117],[64,80],[64,80,112],[64,112,80],[64,112],[64,82],[64,82,114],[64,82,32],[64,82,32,112],[64,82,112,32],[64,82,112],[64,114,82],[64,114],[64,114,32,80],[64,114,32],[64,114,80],[64,114,80,32],[80,32,66],[80,32,66,116],[80,32],[80,32,114],[80,32,116],[80,32,116,66],[80,64],[80,64,116],[80],[80,112],[80,116],[80,116,64],[80,66,32],[80,66,32,114],[80,66],[80,66,112],[80,66,114],[80,66,114,32],[80,114,64,66],[80,114,64],[80,114,66],[80,114,66,64],[80,114],[80,114,32],[112,32,66,84],[112,32,66],[112,32,82],[112,32],[112,32,84,66],[112,32,84],[112,64,84],[112,64],[112,80],[112],[112,84,64],[112,84],[112,66,32,82],[112,66,32],[112,66,80],[112,66],[112,66,82,32],[112,66,82],[112,82,64],[112,82,64,66],[112,82,66,64],[112,82,66],[112,82,32],[112,82]]
def g181D3 := limbs80 #[#[0x887805915350d2148110,0x4180360709aa26498a40,0x2]]
def g181D4 := limbs80 #[#[0x48110f415350d2148110,0x54d2148110b618550d21,0xe636454d2148110e6164,0x48110b638454d2148110,0xd4d2148110e6364d4d21,0xf41544c93148110b6184,0x48110f43544c93148110,0xd913148110f814350931,0xcb374d913148110ad183,0x4c91087b805d9544c910,0x82a4854300c3874dc165,0x808103df5df82d4b78d9,0x4002820a04000000120,0x1]]
def g181H4 := limbs80 #[#[0x330000000000000,0xd0d9c40000010000]]
def g181D5 := limbs80 #[#[0xa4290221d854d2148110,0x4887c1324c520443b1a9,0x850d214811087ee8b2a6,0xc520443f0a9a4290221f,0x10fc2e498a40887e1424,0xaa26290221dc55131481,0xa40886f1644c520443b9,0x15e5d54348110de6c898,0x254d20442f5b92a69022,0x8110cf2c8a9a408876b7,0xbdba2a6902219ed91534,0xa9a408867b64d4d20442,0x221bc585604c910af2e9,0xf76551324423ebb2a899,0x44c910adae5aa2648847,0x423ebb6a8992218fd935,0xe8b2a648856f72595324,0x992219edc1654c910a7e,0x63f74595324431e3a2ca,0xa654c9108fee8b2a6488,0x24423ebb4ca992215b5c,0x7ee8b1aa48856f7254d5,0xc7a92211f5d36354910a,0xb62007a1502e0023fba2,0x364a11a43106400e2370,0xbe681926317e5e16a531,0x16821fa7b1e6781d2711,0x669825a9323e8c22a872,0xc19cc144090805739216,0x7381801800a090605101,0x300242048144070605,0x8202041810904000241d],#[0x3481002410805020c200,0xc1d2040d221200c0810,0x404000074810204000,0x41010204]]
def g181H5 := limbs80 #[#[0xb978a00c211192d10084,0xd0f4a00a0398032,0x31e38000e3c1630400,0x10649ca0cbc800180,0x4800030e00002803b003,0x38f57000005009892ac0,0x230141f32017c,0x2a940000080294c16892,0x30656852020400038c,0x10d7a1a0000424790c00,0x5830db6c600008f800c3,0x23033d312c1c9200346,0x63c3078c0005006354f4,0x8000f26ec036f060000,0x9238308000b307a92d00,0x2,0x900a0000000248d,0x800000000000000,0xb1c346320c6d48c00000,0x3d78c334600000]]
def g181D6 := limbs80 #[#[0xfc4c520443e12148110,0x10ded4d2044379534811,0x9109fd8d524427d654c9,0x8110fe50d204427d63d4,0x4c910fe58132443f9534,0x54c910dfd51324437d54,0x5354910df995324437d6,0xd6354910bfd8d524437d,0x40600dc00dfd8d524437,0xf1935a94847d0436cb22,0x414795e43886067e5de6,0x12199d20a2870d03a732,0x333a414412202b3c3486,0x5d30e0662d3a58700414,0x4467083058228466143a,0x14288a42836114488241,0x2520ca5214144294a0c0,0x7c019989809920e90215,0x1c305662346610]]
def g181H6 := limbs80 #[#[0x1101c410c01400c0145,0x1281c50410011104090,0x830035e9a0d201e51810,0x5700de808e4045818ca3,0x8007864398605c790c01,0x218a00a90e2800016518,0x8a811c60241046c0006c,0x8000000000000d0c5106,0x3c5f044c0001c00ecc47,0x1c0000300440001e0088,0x1e68a1051100100000ac,0x304348400948640000,0x2c02f001f600600002,0x2835b0615a019000000,0x53c84bc51002c8000f05,0x7c0b022fed28400c0000,0x1600000000000034f0a0,0x20e230d11000030743d2,0x9a1b4082000006460000,0x10006000000000000004,0x6000038c000000c185b0,0x23e0800400000ec8,0x99400000000000000000,0x2dcf14a021202480001f,0xa0030000107,0x7d32380382668d91c0,0x118345b1c30000060252,0xfc09a7006b34334317a1,0x304bf83674d0,0x10c9f004f000004870,0xd9f140001868e838980,0x20e07242bc0120000f3c],#[0xc185800738091a4c8,0x44478700003804fa6180,0xe403b2907200289e00cf,0x8050c034e548c0201002,0x5b22b8c396002e0e57]]
def g181D7 := limbs80 #[#[0x7f52442faa4887e48110,0x3015007f54910fe99221,0x94301030ba6694235a3f,0xa5011a6690a20e30ba66,0x38da6690a3c8a142a70,0x4]]
def g181H7 := limbs80 #[#[0x8004021200c020208180,0x35800033c5d700162800,0x38000000040617005a8,0x2120414000800051a47c,0x7284408245860a00000,0x1163c621e15802586458,0x6841c0,0x7583b010e007d81700,0xc6e81320718843800000,0xc0ebc4d802e3213801cb,0x44b80541c464a111a190,0x3426000038710011ed,0x1239c100708006f3c500,0x11e0b00849a1000028,0x35984f804da40800000,0x12c01781c1d003c81470,0x6000050741818b008b8,0xb41000021c3800010,0x4506180001424801800,0x35000000004821800048,0x40010000000058]]
def g181D8 (j : Nat) := if j=0 then 0x2d2720806fd10 else 0
def g181H8 := limbs80 #[#[0x0,0xa0b0000,0x71200000000,0x114000000000e20ae0,0x904000000f243020000,0x0,0x200000000000,0x110103000000cc06d00,0x81100000012201b00,0x1000000000621000]]
def g181D9 (j : Nat) := if j=0 then 0x219080bf else 0
def g181H9 := limbs80 #[#[0x248005aa0000004f586,0xa9e65a24800000000d0,0x38c0013]]
def g181L : Nat → Packing
  | 3 => (2,6,4,0,0,5,0,g181D3)
  | 4 => (14,5,4,0,0,7,0,g181D4)
  | 5 => (38,4,4,0,0,10,0,g181D5)
  | 6 => (18,3,4,0,0,10,0,g181D6)
  | 7 => (5,2,4,0,0,8,0,g181D7)
  | 8 => (1,1,4,0,0,0,0,g181D8)
  | 9 => (1,0,4,0,0,0,0,g181D9)
  | _ => emptyPacking
def g181I : Nat → Nat → Option (Nat × Nat)
  | 4 => lookupWord 1 13 0 12 1 7 g181H4
  | 5 => lookupWord 16 101 5 15 4 7 g181H5
  | 6 => lookupWord 30 163 6 17 6 7 g181H6
  | 7 => lookupWord 17 97 7 16 5 7 g181H7
  | 8 => lookupWord 4 67 0 12 3 5 g181H8
  | 9 => lookupWord 2 17 0 11 0 7 g181H9
  | _ => fun _ => none
def g181 : Forest := ⟨181,9,fun i => g181Y[i]?.getD (0,0),g181C,g181A,g181L,g181I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g181P3_0 : block g181 3 0 2=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g181B3 : block g181 3 0 2=true := g181P3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g181P4_0 : block g181 4 0 14=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g181B4 : block g181 4 0 14=true := g181P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g181P5_0 : block g181 5 0 4=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g181P5_4 : block g181 5 4 34=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g181B5 : block g181 5 0 38=true := (@block_merge g181 5 0 4 34 g181P5_0 g181P5_4)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g181P6_0 : block g181 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g181P6_1 : block g181 6 1 6=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g181P6_7 : block g181 6 7 11=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g181B6 : block g181 6 0 18=true := (@block_merge g181 6 0 1 17 g181P6_0 (@block_merge g181 6 1 6 11 g181P6_1 g181P6_7))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g181P7_0 : block g181 7 0 3=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g181P7_3 : block g181 7 3 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g181B7 : block g181 7 0 5=true := (@block_merge g181 7 0 3 2 g181P7_0 g181P7_3)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g181P8_0 : block g181 8 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g181B8 : block g181 8 0 1=true := g181P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g181P9_0 : block g181 9 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g181B9 : block g181 9 0 1=true := g181P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g181T : checkedTables g181 9 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g181 0 0 0 = true)
  · exact (rfl : block g181 1 0 0 = true)
  · exact (rfl : block g181 2 0 0 = true)
  · exact g181B3
  · exact g181B4
  · exact g181B5
  · exact g181B6
  · exact g181B7
  · exact g181B8
  · exact g181B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g181G : graphValid g181 (boundsBefore K171) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low181 : Lower true (varsX 181) (graphGoal 181) 10 := lower_forest (g:=g181) (i:=0) (hints:=2) (before_sound K171 V171) g181G g181T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K181 := extendKnown K171 10 [(181,[]),(213,[101])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V181 : Known true K181 := extend_ok (m:=181) V171 low181 (by decide +kernel)
def g227Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x1fe1fe01fe1fc3ffc,0x7ffe3ff1ecd460071c7])),(BitVec.ofNat 152 (word80 [0x141441414144088028,0x50a04802424506249249]))),((BitVec.ofNat 152 (word80 [0xfe001fffe001ffc3ff,0xf80ffc7fe17493038e38])),(BitVec.ofNat 152 (word80 [0x181881818188100830,0x60c08104095412249249]))),(0x0,0x0),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x1ffffffe0003ff,0xfff0007ffcc2f51c003f])),(BitVec.ofNat 152 (word80 [0xa0a10a0a0a00a11140,0x810512280082e1492492]))),((BitVec.ofNat 152 (word80 [0xffffe00000000003ff,0xffffff80003b4be00fc0])),(BitVec.ofNat 152 (word80 [0xc0c00c0c0c10c22181,0x2060030902a49492492]))),((BitVec.ofNat 152 (word80 [0xfffffffffffffffc00,0x30628fff000])),(BitVec.ofNat 152 (word80 [0x10010101001000202,0x4080040000000924924]))),(0x0,0x0)]
def g227C : List ColumnInfo := [(1,0,226,0,5)]
def g227A : List (List Nat) := [[],[101],[16],[16,101],[80,97],[80,97,16],[96,81,16],[96,81]]
def g227D5 (j : Nat) := if j=0 then 0x3f else 0
def g227L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,g227D5)
  | _ => emptyPacking
def g227I (_ _ : Nat) : Option (Nat × Nat) := none
def g227 : Forest := ⟨227,5,fun i => g227Y[i]?.getD (0,0),g227C,g227A,g227L,g227I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g227P5_0 : block g227 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g227B5 : block g227 5 0 1=true := g227P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g227T : checkedTables g227 5 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g227 0 0 0 = true)
  · exact (rfl : block g227 1 0 0 = true)
  · exact (rfl : block g227 2 0 0 = true)
  · exact (rfl : block g227 3 0 0 = true)
  · exact (rfl : block g227 4 0 0 = true)
  · exact g227B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g227G : graphValid g227 (boundsBefore K181) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low227 : Lower true (varsX 227) (graphGoal 227) 6 := lower_forest (g:=g227) (i:=0) (hints:=85) (before_sound K181 V181) g227G g227T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K227 := extendKnown K181 6 [(227,[]),(230,[16,32]),(242,[16,64,32,50])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V227 : Known true K227 := extend_ok (m:=227) V181 low227 (by decide +kernel)
def g63Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x3fffffc1ffff60ac8,0x4caee8000007f01fc07f])),(BitVec.ofNat 152 (word80 [0x280280084044060880,0x400ce80a142850a14285]))),((BitVec.ofNat 152 (word80 [0xfc003ffffffe021c2c,0x13d9d30003f800003f80])),(BitVec.ofNat 152 (word80 [0x304b04500208221c28,0x3c941264c993264c993]))),((BitVec.ofNat 152 (word80 [0xffffc0001ffffbf0cb,0x81210b01fc000fe0007f])),(BitVec.ofNat 152 (word80 [0x400c0160809009404a,0x12103142850a142850a]))),((BitVec.ofNat 152 (word80 [0xffffffffe0000824f7,0x691ab200000000003f80])),(BitVec.ofNat 152 (word80 [0x8290298014e04820d7,0x6812b2d9b366cd9b366c]))),((BitVec.ofNat 152 (word80 [0x93710,0xa28774fe00000fffc000])),(BitVec.ofNat 152 (word80 [0xe00e010700803700,0xa2821060c183060c1830]))),((BitVec.ofNat 152 (word80 [0x4c917,0x7e4005fffffff0000000])),(BitVec.ofNat 152 (word80 [0x30030021801008015,0x1c000481020408102040]))),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g63C : List ColumnInfo := [(0,8,53,2,8),(8,0,55,0,8),(1,0,62,0,7),(2,8,53,0,7),(4,0,59,0,7),(16,0,47,0,7),(32,0,31,0,6),(5,0,58,0,4),(17,0,46,0,4),(20,0,43,0,4)]
def g63A : List (List Nat) := [[],[66],[32],[32,64],[64,32],[64]]
def g63D4 (j : Nat) := if j=0 then 0x1a2b6460b5454120 else 0
def g63D5 := limbs80 #[#[0x50940483aa5954250120,0x483ca5515250120eab65,0x5915254120d697554940,0x54120e6b64549504839a,0xb6982d51504835add152,0x5d9544838ed935454120,0x4832ed9170d51208fb80,0x1d37059520a3d85d9354,0x8d01d345ca0d141c032e,0x8080002836294c]]
def g63H5 (j : Nat) := if j=0 then 0xc0e else 0
def g63D6 := limbs80 #[#[0x3b4a92a0907a94250120,0xfd2a4a02412fdd16548,0x837db2a80906f9655012,0x20fd6e4a8241fa549504,0x483bdaa2a09077954541,0x120df6c8a8241be59150,0x44833eb2aa8905fb7454,0x51209feecaa2413f5d95,0x544835fb26a8905f970d,0x591209faedaa2419f597,0x1654827ebaec8904ff75,0x59520b7ee8b2a417edc,0xd1654835e3a2ca906fb7,0x70995209fee8b2a41afd,0x5d3654827ebb4ca905f9,0xb7054950bf6e0a92a13f,0xfd93525433fb22a4a877,0xbf7458950afae9a92a19,0x3fdd162d427eba6c4a85,0x78a8431e4d85f258a401,0x5610fb7aba1b6d564309,0x75a2b74ea0cee5d288dc,0xee46ef5da1cde3b037bb,0x8178f049085f3f6ba9c,0x82141100f1e010649ce1,0x810000808205c7806102,0x80101c4080141c80801,0x400e0e2043820700400a,0x8604002005041020050,0x35040000a8]]
def g63H6 := limbs80 #[#[0xe544b00000000081803,0x22e98005940000000000,0x60800000002000000004,0x1c2800001,0x30d6100000002600,0x35380c003b0000a400,0x240000000000000,0xe12400009000000005b3,0x2c0000034e003946a242,0x40c00000000000000a,0x7b15140008380051008c]]
def g63D7 := limbs80 #[#[0xf59120fe54120fe50120,0xd9520bf59520bfd9120b,0x8950dfd4950df54950bf,0x120ff55120bf58b50bfd,0x20ff59520ff59120ffd5,0xff58950ff54950ff995,0x90ba2585a0c000ffd895,0xc9ce691865a144481023,0xb1c159079aa528ba107,0x648b3242c461f3906207,0x3186c55cc7149207c465,0x522105c731c4c4792217,0x54d62cc51e2cd41851b3,0x51c6185887105506cc4c,0x88710920789516245019,0xf1c065221624501c4195,0x60940c75540]]
def g63H7 := limbs80 #[#[0x4450429e3e01c138310e,0x3130a2e8416453c0300b,0x40006035451011035088,0x6266fa84001012012c82,0x4d108811521e87fc4260,0x61e01206000024d00050,0x91259000034860929a60,0xe98368283ac19c1b0006,0x9272410000205b85c000,0xc00040a000103b8a0806,0x4a2650aa83000712603,0x2b00780b000140000000,0x4065838cc3211a8288,0x92d44cd62003c000acf0,0x189ca4610700b42a,0xe057243c8e53ea22]]
def g63D8 := limbs80 #[#[0xc79aa407fd43faa1fd20,0x98d13568298d131ea414,0x1ad046]]
def g63H8 := limbs80 #[#[0xcf4,0xf47000e31000e6ab0e00,0x29000000008e21000000,0x9f010410000000000000,0xd28f02000f26000c0,0xe0b000e3010c000,0x540f000000000000,0x2f56b00000031000,0xd24000000706,0xb030000000000000000,0x687b2720400000,0x1140d80f000707000,0x10ae050]]
def g63D9 (j : Nat) := if j=0 then 0x1542317f else 0
def g63H9 := limbs80 #[#[0xf00000000a4803a200,0x99aa000000000b200000,0x2c9852100000]]
def g63L : Nat → Packing
  | 4 => (1,5,4,0,0,0,0,g63D4)
  | 5 => (13,4,4,0,0,7,0,g63D5)
  | 6 => (39,3,4,0,0,9,0,g63D6)
  | 7 => (18,2,4,0,0,10,0,g63D7)
  | 8 => (3,1,4,0,0,7,0,g63D8)
  | 9 => (1,0,4,0,0,0,0,g63D9)
  | _ => emptyPacking
def g63I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 2 0 6 0 2 g63H5
  | 6 => lookupWord 7 79 3 11 4 3 g63H6
  | 7 => lookupWord 18 89 6 13 6 3 g63H7
  | 8 => lookupWord 8 83 2 12 5 3 g63H8
  | 9 => lookupWord 2 23 0 9 2 3 g63H9
  | _ => fun _ => none
def g63 : Forest := ⟨63,9,fun i => g63Y[i]?.getD (0,0),g63C,g63A,g63L,g63I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P4_0 : block g63 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g63B4 : block g63 4 0 1=true := g63P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P5_0 : block g63 5 0 13=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g63B5 : block g63 5 0 13=true := g63P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P6_0 : block g63 6 0 3=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P6_3 : block g63 6 3 36=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g63B6 : block g63 6 0 39=true := (@block_merge g63 6 0 3 36 g63P6_0 g63P6_3)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P7_0 : block g63 7 0 10=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P7_10 : block g63 7 10 8=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g63B7 : block g63 7 0 18=true := (@block_merge g63 7 0 10 8 g63P7_0 g63P7_10)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P8_0 : block g63 8 0 3=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g63B8 : block g63 8 0 3=true := g63P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P9_0 : block g63 9 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g63B9 : block g63 9 0 1=true := g63P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63T : checkedTables g63 9 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g63 0 0 0 = true)
  · exact (rfl : block g63 1 0 0 = true)
  · exact (rfl : block g63 2 0 0 = true)
  · exact (rfl : block g63 3 0 0 = true)
  · exact g63B4
  · exact g63B5
  · exact g63B6
  · exact g63B7
  · exact g63B8
  · exact g63B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63G : graphValid g63 (boundsBefore K227) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low63 : Lower true (varsX 63) (graphGoal 63) 10 := lower_forest (g:=g63) (i:=0) (hints:=4146) (before_sound K227 V227) g63G g63T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K63 := extendKnown K227 10 [(63,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V63 : Known true K63 := extend_ok (m:=63) V227 low63 (by decide +kernel)
def g95Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x1fffff87fff6a323,0xb48680000007f01fc07f])),(BitVec.ofNat 152 (word80 [0x9402801102206a022,0xa082850a142850a14285]))),((BitVec.ofNat 152 (word80 [0xffe003ffffff0205ed,0x63cb000003f800003f80])),(BitVec.ofNat 152 (word80 [0x2184b08a010422056d,0x224b13264c993264c993]))),((BitVec.ofNat 152 (word80 [0xfffffc0007fffb1ad1,0x92518001fc000fe0007f])),(BitVec.ofNat 152 (word80 [0x200c02c20480912d1,0x12400a142850a142850a]))),((BitVec.ofNat 152 (word80 [0xfffffffff80008caba,0xcb8c00fe000000003f80])),(BitVec.ofNat 152 (word80 [0x4c090130027048ca92,0xc9842c58b162c58b162c]))),((BitVec.ofNat 152 (word80 [0x92d42,0x4c3f7f0000000fffc000])),(BitVec.ofNat 152 (word80 [0x700e01c04380800d00,0x4c3d3060c183060c1830]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x4d414,0x28607ffffffff0000000])),(BitVec.ofNat 152 (word80 [0x801002000400000000,0x4081020408102040]))),(0x0,0x0),(0x0,0x0)]
def g95C : List ColumnInfo := [(1,0,94,0,8),(2,0,93,0,8),(4,0,91,0,8),(8,0,87,0,8),(16,0,79,0,8),(10,0,85,0,7),(0,2,21,72,6),(0,8,21,66,6),(64,0,31,0,6),(3,0,92,0,5),(5,0,90,0,5),(6,0,89,0,5),(8,2,21,64,5),(17,0,78,0,5),(18,0,77,0,5),(20,0,75,0,5),(64,2,21,8,5),(64,8,21,2,5),(21,0,74,0,4),(66,0,21,0,4),(66,8,21,0,4)]
def g95A : List (List Nat) := [[],[66],[49],[49,66],[32],[32,64],[32,49],[32,49,64],[64,32],[64],[64,49,32],[64,49]]
def g95D4 := limbs80 #[#[0x50c8ae1192d915254110,0x30c4ae13925d152d41]]
def g95D5 := limbs80 #[#[0xa8221a2b6460b5454120,0x6454950442cd325b22a4,0x94aa2a5b82848868ee13,0x12214e9921977050910e,0x5dc1424429b32632ee0a,0x4c94cbb82848843e6606,0x2210f9989977050910a7,0x5c86544315ee8c16c8a9,0xc1a84a8a809053ae4184,0x41aa98650b5150120dc5,0x49404839572eb2a84a02,0xa2eaa92809078ae59545,0x1c6b965d55250120e95c,0x55048369706a92a2a824,0xaa4b8aa0904ce6508558,0xe29645515254120da5c1,0x50483a56e8aa2a4a8241,0xa8a92a09059ae5954549,0xab84dd15254120f15b26,0x483c56e9b22a4a82419,0x8a92a09059aa5f645495,0xb745537254120d95c26e,0x48335309ba6e4a8241d2,0xaa2a0905ca64b5455150,0x6460b5454120d55b2305,0x8256f28c36a2a8a41e2b,0x2ea290527e5165dcd514,0x4e0176d452085fca30fb,0x287b283aacab0a418b88,0x2a89062ee13805d95448,0x5c970d5120c74c1301bb,0x13ec9c1ae3aa241cab64],#[0xca9066ae0b80dd165483,0x17159520e55ba6e5b82,0x38e9c1ae2b2a418b874e,0xa90627dd3835c5654831,0x3745952085f4c0e8b8ac,0xf26c0ee8b2a41aab82e0,0xa855ae497454b5054293,0x6258550c9dc22e8a96a0,0x9ba6e0a92a189f84dcd,0x852ee4174d9352543273,0x458b50b1dc82e9b26a4a,0x9018030018af74e096,0x8210781b060150480f03,0x5c16451124410f8360b,0xc88214821d4721a86719,0x4aa29c9f270992588e22,0x8db338cb2f8b62ccb02b,0xfd3e8f73a8e7390e137,0x431094190340,0x8080d05400400000000,0x814003a103a1020648,0x28540040600080050,0x1d182000001a0800,0x11801016168011800800,0x1322c81000000006]]
def g95H5 (j : Nat) := if j=0 then 0xa0a10099 else 0
set_option maxRecDepth 16000 in
def g95D6 := limbs80 #[#[0x54940483aa5954250120,0x4835a5d55250120f2954,0xd915254120e696454950,0x54120d6b74549504839a,0xe3b64d5150482da60b54,0x5d9544822fe1176d4520,0x4832ed9170d51208fb80,0x1d37059520a3d85d9354,0x54110f6952509504432e,0xf6b7254950442de61542,0x549504439ed915254110,0x4439e2195254110b7b84,0xa1f6254110af984d8950,0x54510bbb845c950442be,0xcf774d8951442fce0142,0xdc951442bd6136254510,0x4437a54b70509109f584,0x9977050910cf865dc142,0x509109f985dc1424433e,0xaed8219542443cb55152,0x19542442b760c6550910,0x442b7e0d65509108fd87,0x60a65509108ff8759542,0x509108fd8799542442bb,0xaed82d91524427ee0175,0xd91524432fdd36454910,0x4423fa1f64549108fd87,0xe1574d8910a7d859d952,0x195108ff845d7624423f,0xced845c8654423fe1172,0xdc9654433be117219510,0x4823fe1172995108fd84],#[0xe0d5150120fa94254540,0x50120fa942d4540482f6,0xaf986d4540482fa60b51,0x54940483ea5515250120,0x4837a5d55250120fa984,0xe096550120deb8754940,0x50120ebb8459540483ba,0xf6952545504833ee1d65,0xd4550482f6e0d5154120,0x482fa60b5154120f6952,0x2156154120f695258550,0x54120b7b8558550482de,0xbeb825c550483da54971,0xdc550482f6e0d7154120,0x483da5515254120f6952,0x5915254120f6b5454950,0x54120eeb6454950483ba,0xf6a65549504837add152,0x54950483da5d15254120,0x483da5537254120f6b74,0x5d37254120f6b54dc950,0x54120deb74dc9504837a,0xf3b5455150482fa61372,0x551504836edd15454120,0x483da6095454120afb86,0xe195454120f3b7455150,0x54120be982d51504839e,0xf6982d5150483aed9354,0xd9150483aedd36454120,0x482fae097454120afa87,0x60a6554120deb82dd150,0x54520bf180d4551482fa],#[0xcdd64dcd51482bd61b51,0xdcd5148337d937354520,0x48337d977354520cdd65,0x61b7454520cbf74d9151,0x54520abf84595514823f,0x9df835d9514827ee0176,0xdd9514826fe117654520,0x4837a5c970d45209f980,0x59170d4520deb825c351,0xd4520cfb645c3514833e,0x8fd87593514827ee1170,0x5d3514823f61f64d4520,0x482afe1165d45208ff86,0x61f65d45208ff8759751,0xd4520abf845db514823f,0x9bf845db514827ee0176,0x5db514833ee0176d4520,0x4832fe1176d4520cbc84,0x61e76d45208ff845db51,0x585209f980ddb514823f,0xc7c7559561482afe1165,0x1d5614831fdd56558520,0x4826f61075585209dd83,0x6037155120de9725c154,0x551208fd86dc5544827e,0xe3d65d5154482ee60354,0x59554482af61b5455120,0x4839ee016555120abf84,0xe017655120e3f8459554,0x55120cfb805d954482be,0xde9725c3544833e60376,0x5c354483aed9170d5120],#[0x48277e0d71d5120deb82,0x61764d5120cbf645c754,0xd5120abd87d9354482af,0xe3f84597544839ee0165,0x5db544833ee0176d5120,0x4832fe1175d9120cbf84,0xdd37059520deb72dc165,0x59520cbf76dd1654836e,0xcbf86dd1654836ee0374,0xdc165483badcb7059520,0x483aedd37059520eb874,0xe017159520af984dc165,0x59520adf835c565482be,0xcbf745c5654832f1d171,0xdc565482afe117159520,0x4832fdd37159520cbc74,0xe017459520abe871d165,0x59520ebb80dd165482be,0xcbf81dd1654832f60774,0x5c6654837a5c97099520,0x543dad8952d41509df83,0xe1152d4150d797454b50,0xd4150bbb8458b50542de,0x9fb845cb505437a5cb62,0xd895154357dcd5254550,0x5433b5cb62d4550cdf73,0xdc952585509fb805cb51,0x58550d5f73549615435b,0xabf845896154337dcd62,0x58b6154337dcf6258550,0x5433b5cb62d8550abf84,0xd8b70549508ff845cb61],#[0x54950d7954dc152543ba,0x9f984dc1525435ed5370,0xdc1525432fdd36454950,0x543dae0b7054950f6b62,0xdd37054950d7974dc152,0x54950b7984dc1525435e,0xd3f74d9152542dbe0964,0xd93525439be0b6454950,0x5427ee0174d4950cbd74,0x5d364d4950b6f8259352,0xd4950e3d74d93525434f,0xd7b805d352542dee0174,0xdc1625436e1d37058950,0x5436bdc87458950dbb74,0x60b64d8950dbb80dd162,0x58b50adf835c762542bb,0xafb805d162d42bbe0964,0x5c3515463fe1172d8151,0xd46bee0162583519f782,0x6137258351abf845c960,0x2b821012009c0600023f,0x5851c4e04c846840833c,0x869c68464860c5d05945,0x81c7e07c87447086f06d,0x789188b88a088884c834,0xb04aecab0a74a389d89,0xca8c90c54bf4bb8b7cb4,0x70decdd4d98d5ccfccc0,0x50f90bd038ffcfc0ed0e,0x3753392912551f519513,0x8162157953d5014593d5,0xd89d83d7dd77d71d6bd6],#[0xb85b25ae9aad9e195d8f,0x71d35cf9cbdc81c21bc1,0x1f21f09ecde91e31dadd,0xc60ae09605a01dfbdf8,0x4620a1ce19215611a102,0xe3d23ba37e3422be2822,0x52e4ce4b647a43e42640,0x8a67263661e5e25a656a,0xa7aa76e73271a7026c66,0x9ba97e9428e28a686a80,0xa6afeac2a86a6ea329f6,0xed32cf6cbaca2c42c06b,0xeb2e76e3adfede6daad6,0x7b03efdefa2f66f2aeca,0xb1e31cb16b10b0cf0b70,0x3ab36f3572f72732371f,0xe34cb48f45343b4233e7,0x36275eb5af57353751f4,0x73b72370b6cf6b769f66,0xbb87f8438077a778f777,0x39b797b9639278eb8d38,0xb13ad7a9ba5fa47a0b9f,0xb7c9fc63c4bc0fb8bb4f,0x415240bd5fd47d0bccfc,0x31d8c08181ba4a106120,0x28363b1814e4101e0d05,0x82450441b64080a0f724,0x10903c2040f1e84206f0,0x200401630200068c0b90,0x40d1805001f041000080,0x21161820002002001a30,0x881d10002d16002c0010],#[0x3020804020800407440e,0x40400000080400101810,0x4006039017202e46004e,0x520ac2801b09820ac682,0xd05508302020d041e0d0,0x2b481034041008109020,0x9d1ac680134808294810,0x40020ac21d1900160810,0x244048209068d6105824,0x305c2041202082763210,0x4040500040542c00480a,0x7028005007204087204e,0xa043928500141ae4a10,0x20804083c84103410002,0x1c1030a061408081a0,0xc209056404060804100a,0x2041ac2080c00208041b,0x8080068c1d18282c0040,0x10003a3040c08181018,0x20485a120060007800f0,0x841e002001c204003020,0x78008001d08204008406,0x81010008080000,0x211002047002e0020604,0x20204051408080208081,0x424080a40748080010,0x40f0a80102348c2a008c,0x120648084810309c0080,0x14082815202069010902,0x50a041408481b2308202,0xc2b182000017202e4850,0xc80b0010000258420758],#[0x502038dc2122ac8640e,0x40c0038004003000f001,0xd0010982010400081400,0x1010000002001a306c80,0x24006800a8a8010003,0x40800102800e0010002,0x7440820101020020100,0x4005028ab21903510340,0x720200001e182000000]]
def g95H6 := limbs80 #[#[0x60c3001a18581280080f,0x4b80022031e1004ad90,0xe5d07708005a0000c02,0x4a5841a9883880700c6,0x2005601d026e8f300200,0x5948d8a214143019207,0x9c99326a000400fa0be,0x1417a01ae04a0a0a19c8,0x4a75833a1252cf21c000,0xaf00000006865299ec1a,0x9202440c0057e11122b6,0x30adc1b3a104000001c3,0x49a000023e0004ab8487,0x55222683c414f0200901,0x7e13b03f701c810e8d70,0x1c10a0ec02a692583,0x2ef817689208fc0b0000,0x6835807b815c08c46ae,0x800068ce0982a6000000,0x610d0694132a9f227,0x1c1180000000,0x88273aabb283a1ac1000,0x30600000000017302,0x12c2a0000506e2028062,0x14]]
set_option maxRecDepth 16000 in
def g95D7 := limbs80 #[#[0x26eb98ca884ed7219510,0xf5284a024137dcd6544,0x826eb9ec290769525412,0x2097ae832a413d5c4654,0x4426fb9ac3a84bf74595,0x510df6c4a8221de54950,0x14437bb12a2886f76448,0x8910bf6e0a12217ddc95,0x624427eba6c4884ff745,0x595109fae432a213f5d7,0x9404827eb94ca884ff72,0x254120df2caa0241fa54,0x5150483f5b92a0907e95,0x6454120ef6a8a8241de5,0xdd1504837db22a0906f9,0x970d4520bbee6a8a417e,0xf595544827ebb6a2905f,0xfd7655120cfccaaa2419,0x7e5c3544827fbb2a8904,0x67d65d5120d7ec9aa241,0x13f5d7644827ebb6a890,0x5bf7459520bf6e0b2a4,0x41af1d1654837db82ca9,0x904ff7459520d7ee8b2a,0xa413f5da65482fcb84ca,0xa877952d41509fae932,0xaa177dcd51542fcb96a,0xa4a84fd72d8550bbee6b,0xa92a1dedc152542fdb82,0x6a4a867f64d4950cfec8,0x9b12a16fdd162542beba,0xa2c5a867d64d4b509fae],#[0xe1a8aa33f5cb605467fb,0xa12a0884ff7258351bea,0x6e4a8221fe5c950443fc,0x6a9284887f54254510ff,0xfacaa1221bf19542443f,0x7fb2a84886fe6550910d,0xefaa8a92217f5d542443,0x2ffba2a4886ff6454910,0xdfceca9221bf1d95244,0x83fda8a80907f9515012,0x20ff6a2a8241fe545504,0x483fcb8aa0907f961541,0x120ff2a8a8241fedc550,0x483fcba2a0907fb5454,0x4520ff4caa8241fedd15,0x51483fab0aa2907f7515,0x54520dfac8a8a41f7dcd,0x551482ffba2a2906ff64,0x654520dfecaa8a41bf59,0xc351482ffbb2a2905fd7,0x64d4520dfac9a8a41fe5,0x59751482feba6a2906ff,0xd76d4520dfecba8a41bf,0xf9db51482febb6a2906f,0xfd6558520bfeeda8a41b,0x7fdd561482fe3aac2906,0x5ff7155120ff2e0aa241,0x1bf59554483dfaa2a890,0x6ff7655120dfaecaa24,0x417f5c754483fcb86a89,0x906fd76d5120dfacbaa2,0xa417fdc565483fdb82ca],#[0xa906fe6559520f7ee8b2,0x2a41bfdc5654837eb8ac,0xca906ff7459520dfae8b,0xa82a17f5c665483fcb84,0x2a2a87fb62d4150ff2c5,0x5a8aa1bfd8951543bea9,0x96a2a86ff62d4550efaa,0xc4b0aa1df54961542feb,0xb92c2a86ff6258550dfa,0xac5b0aa1df54b61542ff,0xeb96c2a86ff62d8550df,0xfaa8a92a1fedc152542f,0x7fb22a4a877f5454950e,0xefec8a92a1df59152543,0x2feba6a4a86ff64d4950,0xefec9a92a1df5935254,0x43fdb82c4a877d74d495,0x50dfac8b12a1fbd89625,0x543de3a2c4a86ff64589,0x950bfee8b12a1efdd162,0x25437fb26c4a87fb70d8,0x8950dfae3b12a17f5d36,0x625437eba6c4a86ff71d,0x58b50dfac8b16a1bfdd3,0x162d437eba2c5a85ff74,0x258351dfac4b06a3bfdd,0xc960d477eb92c1a8dff7,0x816008a02e0098001bfd,0xa0da06182b0132086039,0xb850026212208984001d,0x8a1be0d5866030216e0a,0x1d88a041a1fe0f987503],#[0x5822ae14b8a104ca2521,0x19b8cc064a30a1738b40,0x7823a61cb8e006ea35a,0xe22d91208624121ff8f7,0x109e24de26392b091a46,0xa62c195c0a9a53228b94,0x880c1a5f62ef9720b6a5,0x69e34799f0cca64631d9,0x9ba0dc26d63639ad0d52,0xa75a3a39ce0e4270e37b,0x79ef0f6a79e3c79df0ec,0x8a83240da020ff27e63e,0x53a25110a872433a1510,0x1da8e646ba3211828b64,0x4a9a51127a926483a3d1,0x13729a24c7a5e12e2966,0x24ffa7c13c29d24e5a70,0x814a2a3e51ba89143aa1,0xbe553aa51512a7a533a9,0xca163ab0e57fabb15aaa,0xb8a5bbada16aab4659ba,0xafa17b2bd25dfaec1732,0x2c32613b051812c025fb,0xbb2318fac6e62fb15188,0xc2cd6665b2e194ac9e64,0x930023144d0a67fb3c19,0xf00405e4e2c00708451b,0x944860200e5121393881,0x407c2c0101108444203,0x28511c2c010130b00203,0xe4e207c01015930b0396,0x4c562100910018b14404],#[0x85030985100c08261440,0x3159040540c52f0c001,0x4402446408c5a209168b,0x40462e4c008c514131,0x40c4810408c562139317,0x47938f860040287c20aa,0x64c2184440483800a08,0xa151d1820484110d8a1,0x1e02299308408474664,0x22970840c8807c4c2a1c,0xb029040ac2c004a51500,0x180c044851110120c2b0,0x807060301c2c0a4201c,0x1244a092845004293086,0xac2c007060301a42048,0x54012081c180c042a906,0x6e4c20a0f8f0b870228,0x1c08a641b0b022b8f859,0x1c1b8f0b8701908e3c2e,0x80c04487111040121028,0x4c2c0116410170b001c1,0x7801162101044298840,0x1c0101c309f130a87004,0x8b00101a9462763e4e2a,0x1028842726c440a21429,0x1928840f64c0a210444,0xb0060a11a21064c0182b,0x301c064a22229938f868,0xa2204702884040d07060,0x280503080706640301c0,0x8b931680508066085101,0x91b04562812f09101421],#[0x24186c18046091029918,0x1003c7248608528d8a00,0xf43a2810614210e89060,0x42a210090c1a8a003c40,0xc900840244221008182,0x8e083100704402440906,0xe084c484610d0a821611,0x2c283094261468215198,0x2151b082130963c21024,0xc3593082040a640880c,0xa04282192030850d64c2,0xa3c0090a141a8c870040,0x4a313060c8f004c1840b,0xa0644c01314928c4c18,0x4a306a10d128c1a844,0x4001b08406c0084c908f,0xc18928428406a1120e8,0x12843a1051284244c00a,0x844c0068410624c00c29,0x82423c0090a1d93001a,0x28312068700402c2450b,0x42a90224c0088a101b00,0x40081028230b02905120,0x21206108f004c185a4c2,0x8a0f001984312042a90,0x664636112930028324c,0x42b0b01904120419842,0x164620a0c8f00198440a,0xa8c2c183a34010141200,0x92214250a8488440080,0x11450428c882450842a1,0xc2c1a8c8440664a322a],#[0x30b640a8500403130962,0x2890031062a10c188a84,0x1208230034424a2c0102,0xa21435928830f64a2c0,0x864102a899030864804,0x282030a08640c481a20a,0x88424a2082810aa20990,0x228928838aa2083c9302,0xc0a20c890020ac0a2641,0x8420663610c359288324,0x40824c0a211901640419,0xc2190240640823019288,0x64620b0401883c122200,0x19882]]
set_option maxRecDepth 16000 in
def g95H7 := limbs80 #[#[0x50130500b8c101530011,0x9221010062002001420,0x5001021111100000101,0x52811143212300001000,0x1909310100d608012,0x845f000000002232081,0x905260e39434000,0xb4cf145d00000000000,0x54010000309d0000000,0xe018200f703781e9000,0xe0023401e00009011000,0x280,0x0,0x6140000000000000000,0x101300002019000,0x90000c02700000000000,0xf0000000000000000d40,0x50b,0x2000000000000d43b000,0x90be00000000244,0x1074b4d4000,0xa3485000070ec0000000,0xb4cdd48c0000055,0xa025703e000054a0000,0x4015707c00000000000,0xc000000000000801d000,0xcf11a0051d0a40000f0a,0x53a8044b0abb81,0x80000000000000000000,0x4a00000000903db1c,0x91060000000,0x140700000000000],#[0xa4bc34b570dba450000,0x9000092410000000070c,0x600122b6f55,0x10570000000,0x400000000249e0000000,0x679a0d09130e90000b06,0x8094d00cc026753,0xe59a61e4000,0x913ed816c11f000,0xdf0d6000000000000000,0x6110000627ac08e181,0x0,0x0,0x0,0xc000000009406081a000,0x343,0x90000f07100000000000,0xc4abd05520880000480,0xd246f00900003159c11,0x3148000,0x321570cf24390000000,0x0,0x68d40000000,0x10000000051620000000,0xa03b000020eb40c,0xe0000a2c700000000000,0xb075a0de0000844,0xf10d700d800000000000,0x800000000d090a474302,0xb05b00000000349,0x18df19cd00000000000,0x904],#[0x0,0x864900000000000,0x85020000c492000,0x58ce82b1000,0xf0000000000000000000,0xf0dd000040c50000005,0x6000010bca0ba0000000,0x10620000000045cdf03,0x930aa404e905d0000000,0x80000000061290000f4a,0x5000000000000c437f55,0x43eb09700000000023,0x81e600000000000,0xda1ed8cd000,0x608b00000000000,0x0,0x31690000000,0x0,0x704c000054450000000,0x1000040d400000000000,0x70000000091370000d0d,0x5021d153aa26c0bdb08,0x0,0x30000000000000000000,0x206,0x0,0xf000000004041d464000,0xa56c0000715,0x10c80000000,0xe43d0000408f0000000,0x758c000,0xb436000051520000000],#[0xa0000000000000000000,0xac00e00000000040524e,0xf0e14475107a514ac4b,0xd13b60485165b0e2203,0x0,0x440ad08000000000000,0x102400000000000,0x7495000000000000000,0xa089b0a0d0700000000,0x50d0000000000000000,0x4d3000,0x9260f0000201b0000000,0x9f0580000e8190000e05,0x200d100600005117e02,0x558bc4d20000e480000,0x701ca2afc005000,0x8a0d000,0x50500000d0bb000,0x709e00000000000,0x1c6000000000000000,0xa30200000000094bb000,0xe153ee58d0000214ce02,0x3607e00000000e444958,0x7000021550000c08de8d,0x8a00000000000022b,0x60000f00328b4d446000,0x104dc06900000000a01,0xd0e5c0b650d2000,0x90000309ca5370000000,0x57457c0a390b800af753,0xe906600610000b008508,0x747e0000205e402],#[0xb124803cb0a10000000,0x40000000000000000400,0x8e04f80310000000044b,0x3b0350000000010ccc02,0x8000000000000c4c3d07,0x202c00000000409,0x0,0xf05c000,0x5d0c4000020540000000,0x500000000e895e100b0a,0x909,0x2127000,0x30ce00000000000,0x199690b2000,0x200000000000068da000,0x48077017670b7381e109,0xb0780000d10d908,0xb43a000000000000000,0x0,0xa03f40dc0000e0e4000,0xe00008065e09a0000000,0x1500f1c,0x826000030b00000000,0x40a9a89e0000000,0xc060816600000000000,0xf440000040cb000,0x706d0000000,0x8000000000000e067000,0x10e7a103000011d,0x71cd000090c60000000,0x30a600000000458f000,0x9004b06a0000903a000],#[0xf0000115c55790000000,0x2892209,0x9b0b3000062430000000,0x8046501450d5323f224,0x3e646d496e411253b000,0x660b40000b00ba54a604,0xa0073034807,0xf04740e8000,0x76451000000000000000,0xd026de08c00000000301,0x7c096f2c9a557ba0ed0c,0x80000a0b90000328650c,0x60000500a74a4000020a,0x70d30000807dc05a308,0x30820000000091c0000,0x0,0xc597000000000000000,0xd000000e000000000000,0xc46e000000000000e80,0xf02d000,0x0,0x30dad07b00000000000,0x506f00000000000,0x740c00000000a154000,0x3402d55b00000000000,0xaf0c2000000000000000,0x64d5c8740000a13,0xab2aee1db00000000000,0xb0000000014651033a45,0xc0930000b0327994909,0xc0000000000000449d59,0x80c32599413cd06],#[0x84042000010220000000,0x80d98068c07fc43,0x0,0xe0000000000000000000,0x90000000000000000a48,0x2e4cc000000001136b07,0x445990a7100,0x0,0x0,0x20100000aa1d0000000,0xe0530000000,0x947100000000a233000,0x90b5806e9a1a10ae000,0x60000b08100009012000,0xfa1c000030e,0xb0ea0000000,0x0,0x70720000000,0x0,0x661c53049e0df0000000,0xc0000929b00000000c4a,0xb0000f06b62b20000a55,0x15d00000000000071b,0xe01fe04500000000000,0xa0000805634d781d6000,0x845e0000d1c1301,0xad4aad038000004ce000,0xc9a0b10000000060c,0xb0a2d16300000000000,0x7039000,0x0,0x0],#[0x224ac000000000000000,0x545c002bf0830000210,0x504b000000000000000,0x0,0xe040fb0ad00000000000,0x549430990000000038d]]
def g95D8 := limbs80 #[#[0xd48510fe54110b7d8d51,0xd8910bf58910fd54510f,0x9510bf59510bf19510bf,0x120fe50120bfd9510bf9,0x20bf59120bfd8520fe54,0xbf59520bf19520bfd91,0xfed4150bfd9520bf9952,0xfd4950df54950bfd8550,0xd4b50bf58750bfd8950d,0x4551bfd8151bf58b50df,0x910bf58351f7d8d51fdd,0x20ff54520ff54910ff50,0xff55120ff58520ffd45,0xff99520ff59520ffd512,0xf58550ffd4550ff54550,0xd4950ff54950ffd8550f,0x8b50ffd8950ff58950ff,0x2060037000ff58351ff5,0x18615d1340fd0d40ab08,0xb327524521c2011d11af,0x73b038e36533c31a2f12,0x4eb4bb4994694474173e,0x496195e25a456d54451b,0x87a17637337036d368e6,0x90d8e48ad8688388017d,0x145202900e33262c1047,0x500290151400a4040193,0x228a245088a045202e4c,0x405c808262802228e432,0x917262802228b931408a,0x890c1016524264c51480,0xca4854a4090600890cb0],#[0x91020386ca9050c20386,0x2140ca40708080800640,0x10242804480a10386159,0x80b93100224050e1b292,0x5007c995140132628094,0xd911658030ac8472904,0x14020264078834028307,0x480a09908c0219510c45,0x626364c5804050c364c,0x48511931208a283c98b0,0x825222811480e884908a,0x251c5444818a42809488,0xb129490d1120a110a0,0x48848706010468491242,0x24311090e0c046848122,0x121031e12430885031e1,0xa0084a423890a0102831,0x27262809480e91109890,0x1208a00f931404a40528,0x8981905114440623931e,0x8a00e9089015931e1808,0xb911118040522431e1c8,0x3262402228]]
set_option maxRecDepth 16000 in
def g95H8 := limbs80 #[#[0x3a07804fa020102c7c03,0x804060002c430001436,0xc80400020086c0711000,0x30101e04010005a08091,0x94e85c04081d00004f22,0x445810002d2f990003,0x5100a010e810040b0000,0x8000e1a130082a387a83,0x79c9020020303c082e26,0x2902806240c13ddf480d,0x4a2b0200c2831831a414,0x106bd17d42b646e6c2a8,0x400dc0cd89b982978157,0x81efd03846739152c07c,0x456609cf003ce0d8c962,0xc95f0a6040a18093816d,0x23800014501949bd56d,0x220c14e516dd1dd8579,0xd10f8189d07446540003,0x77409a82d195e00003,0xc1680001ca4c00029497,0x414ac18e10d922900003,0x40605080c24a84500001,0x4273863bc01cd05d422c,0x4299d4590010000302bf,0x9100000001d4c1fa4126,0x1c680c8946800020572,0xd0d090b5845d8633d4a7,0x4175e2476133c4796138,0xc15c00010a3f867fc2a3,0x829151f5c180148e801a,0x688020d8455c96855b7],#[0x4a12071c4ecc2c3419a,0xc575915d45ff4a4085aa,0xc5b881f784d5210c095b,0x44034a18443a127d0265,0x50afc219c4d0c04700c4,0x292e019540be005c41be,0x269310677c1d1,0x44c891cc0815249899c,0x5a58c543c229803481e2,0xff843080e740e06947,0xa08e13f855b00d100ab,0xc00542258137526a41b5,0xc6e8864f40940003147f,0x90e7427fc0b4c1115058,0x4818c275c67810e889d1,0x3011dc043c09d80ef,0x8152c48400035207d588,0xc56c109841ca2114,0x847d8637412e15810024,0x825401c2c10a4203c28a,0x8166d1735073906f06df,0x802f86604ac0c2128105,0xc2e495e9851c0170c06e,0xd5f701388070862c0243,0x4a382284a12000f5c2dd,0x4a4aa939548982d78569,0x4a14e0f6915741ea0a29,0x41b1c2c500a509ae41df,0x1001595820b425dc050,0x42858469603e859980ad,0x4118582ac9180000c2a7,0x98f8648404c01f381d9],#[0x50c7502ac2cf40e94683,0xb80000612f55e401cd,0x458a826b421682040003,0x9a042d811aac459c143,0x408d06e2c26ec956c29d,0xa12400028033811486a1,0x89fb49e3018609654a5d,0x41b8000102b00002d161,0xc1af292700b000014436,0x1a186588829c0d40001,0x1798583899bd602c251,0x4f1c42bc68e403b8000,0x80dc0002515a293e855e,0x1019e407ac25a442e,0x899180d80089413e1a48,0x8640828c0001024c0001,0x81e40001c0540132,0x283c246c0f000030028,0xc52481aa42794512c50a,0x1614650d45f103295df,0x848086640000863f6914,0x92240000603a00488488,0x821cc06515f80001005b,0x644ca5bc1a6c4e142ca,0xc23f815b55efc5e8c009,0x41200001c0fac46c0015,0x85c34a5082e2810cc952,0x10262865f0a36,0xcabf81ffd0ec00848518,0x814455f31276c23349bc,0x406b1244002349b042e9,0xe14782aea83f1259017c],#[0x52790192c235c0c0c2ba,0x2012b]]
def g95D9 := limbs80 #[#[0xd51ffa87f543fa41fd10,0x51b0259b138a803fea3f,0x410202548526489000,0x101464648a50101a48a5,0x248a02051549228]]
def g95H9 := limbs80 #[#[0x84c0051e081030404100,0x1e9833c44009040089a1,0xd81500010aa022ca0112,0x207800004b7004f07,0x20f047c2d00000005048,0x2d28402a215f05a88c79,0xb0880000003028000086,0x1c087928d2070003870,0xa0e9f3180c562428000c,0x7131780c04400bec6eb4,0x4037140a290000da0415,0x6d807045900000000002,0x700010ab000210bb00b8,0xa1ef1b040f285b01,0x24a2508dc100000094,0x51b4881488809d44b0,0xd161000380bc0af62d00,0x54780000000421a86,0x60360610003c060000,0xc004000000201450c00,0x3142972a3962306800,0x230000502400090c4000,0x93045508222850009088,0x68980000000110981bb5,0xc258206565006101644a,0x300000000000000da80,0xe80380004093c8498201,0x801680a0098d07445ac2,0x1051207661f32a5813,0x1c0851bc819000042c0]]
def g95D10 (j : Nat) := if j=0 then 0x2080513f else 0
def g95H10 := limbs80 #[#[0xc21b0247a8950714980,0x480000090ec1800001d4,0x50a0a8810000009,0xa0450000589e20002828,0x580]]
def g95L : Nat → Packing
  | 4 => (2,6,5,0,0,3,0,g95D4)
  | 5 => (57,5,5,0,0,10,0,g95D5)
  | 6 => (237,4,5,0,0,12,0,g95D6)
  | 7 => (187,3,5,0,0,13,0,g95D7)
  | 8 => (50,2,5,0,0,12,0,g95D8)
  | 9 => (6,1,5,0,0,8,0,g95D9)
  | 10 => (1,0,5,0,0,0,0,g95D10)
  | _ => emptyPacking
def g95I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 5 0 8 1 3 g95H5
  | 6 => lookupWord 25 127 7 14 6 4 g95H6
  | 7 => lookupWord 111 1123 4 16 8 4 g95H7
  | 8 => lookupWord 98 431 9 16 8 4 g95H8
  | 9 => lookupWord 28 157 7 14 6 4 g95H9
  | 10 => lookupWord 4 31 3 11 3 4 g95H10
  | _ => fun _ => none
def g95 : Forest := ⟨95,10,fun i => g95Y[i]?.getD (0,0),g95C,g95A,g95L,g95I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95P4_0 : block g95 4 0 2=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g95B4 : block g95 4 0 2=true := g95P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95P5_0 : block g95 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95P5_1 : block g95 5 1 56=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g95B5 : block g95 5 0 57=true := (@block_merge g95 5 0 1 56 g95P5_0 g95P5_1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95P6_0 : block g95 6 0 13=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95P6_13 : block g95 6 13 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95P6_109 : block g95 6 109 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95P6_205 : block g95 6 205 32=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g95B6 : block g95 6 0 237=true := (@block_merge g95 6 0 109 128 (@block_merge g95 6 0 13 96 g95P6_0 g95P6_13) (@block_merge g95 6 109 96 32 g95P6_109 g95P6_205))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95P7_0 : block g95 7 0 10=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95P7_10 : block g95 7 10 59=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95P7_69 : block g95 7 69 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95P7_165 : block g95 7 165 22=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g95B7 : block g95 7 0 187=true := (@block_merge g95 7 0 69 118 (@block_merge g95 7 0 10 59 g95P7_0 g95P7_10) (@block_merge g95 7 69 96 22 g95P7_69 g95P7_165))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95P8_0 : block g95 8 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95P8_1 : block g95 8 1 30=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95P8_31 : block g95 8 31 19=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g95B8 : block g95 8 0 50=true := (@block_merge g95 8 0 1 49 g95P8_0 (@block_merge g95 8 1 30 19 g95P8_1 g95P8_31))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95P9_0 : block g95 9 0 6=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g95B9 : block g95 9 0 6=true := g95P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95P10_0 : block g95 10 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g95B10 : block g95 10 0 1=true := g95P10_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95T : checkedTables g95 10 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g95 0 0 0 = true)
  · exact (rfl : block g95 1 0 0 = true)
  · exact (rfl : block g95 2 0 0 = true)
  · exact (rfl : block g95 3 0 0 = true)
  · exact g95B4
  · exact g95B5
  · exact g95B6
  · exact g95B7
  · exact g95B8
  · exact g95B9
  · exact g95B10
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95G : graphValid g95 (boundsBefore K63) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low95 : Lower true (varsX 95) (graphGoal 95) 11 := lower_forest (g:=g95) (i:=0) (hints:=4146) (before_sound K63 V63) g95G g95T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K95 := extendKnown K63 11 [(95,[]),(159,[118])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V95 : Known true K95 := extend_ok (m:=95) V63 low95 (by decide +kernel)
def g111Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xc007ffffe0ffff7226,0xa10bae00000fc003f03f])),(BitVec.ofNat 152 (word80 [0x82500a004204403202,0x21032a05145145145145]))),((BitVec.ofNat 152 (word80 [0xfff800ffffffe0395a,0x8666308003f000fc0fc0])),(BitVec.ofNat 152 (word80 [0x602c02800082390a,0x844210030c30c30c30c3]))),((BitVec.ofNat 152 (word80 [0xffffff0000ffffad84,0xb0d842c0fc003f00003f])),(BitVec.ofNat 152 (word80 [0x80300b0409000984,0x905800ca28a28a28a28a]))),((BitVec.ofNat 152 (word80 [0xffffffffff0000804d,0x6956a9ff000000000fc0])),(BitVec.ofNat 152 (word80 [0xb01402c002e048044,0x2914a9dc71c71c71c71c]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x9171,0x18b1dc0000003ffff000])),(BitVec.ofNat 152 (word80 [0x2c0580b008b0088071,0x8a0c430c30c30c30c30]))),((BitVec.ofNat 152 (word80 [0x4e93,0x4f80057fffffc0000000])),(BitVec.ofNat 152 (word80 [0x300600c010c0104411,0x42800420820820820820]))),(0x0,0x0),(0x0,0x0)]
def g111C : List ColumnInfo := [(32,0,79,0,8)]
def g111A : List (List Nat) := [[],[32]]
def g111D8 (j : Nat) := if j=0 then 0x7f else 0
def g111L : Nat → Packing
  | 8 => (1,0,1,0,0,0,0,g111D8)
  | _ => emptyPacking
def g111I (_ _ : Nat) : Option (Nat × Nat) := none
def g111 : Forest := ⟨111,8,fun i => g111Y[i]?.getD (0,0),g111C,g111A,g111L,g111I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P8_0 : block g111 8 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g111B8 : block g111 8 0 1=true := g111P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111T : checkedTables g111 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g111 0 0 0 = true)
  · exact (rfl : block g111 1 0 0 = true)
  · exact (rfl : block g111 2 0 0 = true)
  · exact (rfl : block g111 3 0 0 = true)
  · exact (rfl : block g111 4 0 0 = true)
  · exact (rfl : block g111 5 0 0 = true)
  · exact (rfl : block g111 6 0 0 = true)
  · exact (rfl : block g111 7 0 0 = true)
  · exact g111B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111G : graphValid g111 (boundsBefore K95) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low111 : Lower true (varsX 111) (graphGoal 111) 9 := lower_forest (g:=g111) (i:=0) (hints:=4146) (before_sound K95 V95) g111G g111T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K111 := extendKnown K95 9 [(111,[]),(123,[66]),(126,[32,64])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V111 : Known true K111 := extend_ok (m:=111) V95 low111 (by decide +kernel)
def g119Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x7fff803ff83ffffffe,0xc00f44693000f000f0ff])),(BitVec.ofNat 152 (word80 [0x502805080400100,0xc00b0009111111111111]))),((BitVec.ofNat 152 (word80 [0x83ffffc0003fe0ff81,0xca6953a4400f000f0000])),(BitVec.ofNat 152 (word80 [0x85603056102821208,0xca2953a0477777777777]))),((BitVec.ofNat 152 (word80 [0x3ffffffffc000fffc,0x85b0769090f000f00f0f])),(BitVec.ofNat 152 (word80 [0x101804018003040400,0x7690822222222222]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x3ffffffffffff0000,0x32aaa8e24f000f000ff0])),(BitVec.ofNat 152 (word80 [0x206008060004001810,0x12a00860444444444444]))),((BitVec.ofNat 152 (word80 [0xfc0000000000000000,0x4154991e60000ffff000])),(BitVec.ofNat 152 (word80 [0x2805028022808a020,0x1548006288888888888]))),((BitVec.ofNat 152 (word80 [3,0x3f0502078ffff0000000])),(BitVec.ofNat 152 (word80 [0x43006030043010c043,0x25040006088888888888]))),(0x0,0x0),(0x0,0x0)]
def g119C : List ColumnInfo := [(2,0,117,0,8)]
def g119A : List (List Nat) := [[],[101],[66],[66,101],[32],[32,101],[32,64],[32,64,101],[64,32],[64,32,101],[64],[64,101]]
def g119D8 (j : Nat) := if j=0 then 0x7f else 0
def g119L : Nat → Packing
  | 8 => (1,0,1,0,0,0,0,g119D8)
  | _ => emptyPacking
def g119I (_ _ : Nat) : Option (Nat × Nat) := none
def g119 : Forest := ⟨119,8,fun i => g119Y[i]?.getD (0,0),g119C,g119A,g119L,g119I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g119P8_0 : block g119 8 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g119B8 : block g119 8 0 1=true := g119P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g119T : checkedTables g119 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g119 0 0 0 = true)
  · exact (rfl : block g119 1 0 0 = true)
  · exact (rfl : block g119 2 0 0 = true)
  · exact (rfl : block g119 3 0 0 = true)
  · exact (rfl : block g119 4 0 0 = true)
  · exact (rfl : block g119 5 0 0 = true)
  · exact (rfl : block g119 6 0 0 = true)
  · exact (rfl : block g119 7 0 0 = true)
  · exact g119B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g119G : graphValid g119 (boundsBefore K111) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low119 : Lower true (varsX 119) (graphGoal 119) 9 := lower_forest (g:=g119) (i:=0) (hints:=82) (before_sound K111 V111) g119G g119T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K119 := extendKnown K111 9 [(119,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V119 : Known true K119 := extend_ok (m:=119) V111 low119 (by decide +kernel)
def g125Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xf801fffff83ffffeca,0xde0a4140007c00f83ff])),(BitVec.ofNat 152 (word80 [0x9024010090800102c2,0x8400014210842108421]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffe007fffc1fffd95,0xb101548c00f801f07c1f])),(BitVec.ofNat 152 (word80 [0x20080a012004020110,0xa1014400421084210842]))),((BitVec.ofNat 152 (word80 [0xffffff800001ff80d7,0xc57643401f0000000000])),(BitVec.ofNat 152 (word80 [0xc1304c15c1085408d7,0xc5764201ef7bdef7bdef]))),((BitVec.ofNat 152 (word80 [0xfffffffffffe000021,0x2e5c7a23e0003e007fe0])),(BitVec.ofNat 152 (word80 [0x4010060000181021,0x4043a00842108421084]))),((BitVec.ofNat 152 (word80 [0x44,0x90bf89b000003fff8000])),(BitVec.ofNat 152 (word80 [0x58160580211602004,0x10ba81a318c6318c6318]))),((BitVec.ofNat 152 (word80 [0x33a,0x528a034bffffc0000000])),(BitVec.ofNat 152 (word80 [0x60180600421804008,0x1288014a108421084210]))),(0x0,0x0),(0x0,0x0)]
def g125C : List ColumnInfo := [(0,8,53,64,8),(8,0,117,0,8),(32,0,93,0,8),(1,0,124,0,7),(4,0,121,0,7),(16,0,109,0,7),(64,8,53,0,7),(5,0,120,0,4),(17,0,108,0,4),(20,0,105,0,4)]
def g125A : List (List Nat) := [[],[66],[32],[32,64],[64,32],[64]]
def g125D6 := limbs80 #[#[0x25fba2c6887d1314c110,0xd7ee8b1a216fdd16344,0x820bc527287d86bf1180,0x171e01e3e3c03e3d]]
def g125D7 := limbs80 #[#[0xfd8d10bf58d10fe4c110,0x690884603600ff58d10b,0x2481f1cb61881c3c7257,0x78d2571c08571cb61c5,0x92]]
def g125H7 (j : Nat) := if j=0 then 0x3e040c3f000 else 0
def g125D8 (j : Nat) := if j=0 then 0xf1a9072b0ffd10 else 0
def g125H8 := limbs80 #[#[0x31a300000000b2000000,0xe0a8]]
def g125D9 (j : Nat) := if j=0 then 0x5413261bf else 0
def g125H9 (j : Nat) := if j=0 then 0x2d12f else 0
def g125L : Nat → Packing
  | 6 => (4,3,4,0,0,7,0,g125D6)
  | 7 => (4,2,4,0,0,8,0,g125D7)
  | 8 => (1,1,4,0,0,0,0,g125D8)
  | 9 => (1,0,4,0,0,0,0,g125D9)
  | _ => emptyPacking
def g125I : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 1 7 0 6 2 0 g125H7
  | 8 => lookupWord 1 13 0 8 2 2 g125H8
  | 9 => lookupWord 1 3 0 6 0 2 g125H9
  | _ => fun _ => none
def g125 : Forest := ⟨125,9,fun i => g125Y[i]?.getD (0,0),g125C,g125A,g125L,g125I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g125P6_0 : block g125 6 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g125P6_2 : block g125 6 2 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g125B6 : block g125 6 0 4=true := (@block_merge g125 6 0 2 2 g125P6_0 g125P6_2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g125P7_0 : block g125 7 0 3=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g125P7_3 : block g125 7 3 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g125B7 : block g125 7 0 4=true := (@block_merge g125 7 0 3 1 g125P7_0 g125P7_3)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g125P8_0 : block g125 8 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g125B8 : block g125 8 0 1=true := g125P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g125P9_0 : block g125 9 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g125B9 : block g125 9 0 1=true := g125P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g125T : checkedTables g125 9 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g125 0 0 0 = true)
  · exact (rfl : block g125 1 0 0 = true)
  · exact (rfl : block g125 2 0 0 = true)
  · exact (rfl : block g125 3 0 0 = true)
  · exact (rfl : block g125 4 0 0 = true)
  · exact (rfl : block g125 5 0 0 = true)
  · exact g125B6
  · exact g125B7
  · exact g125B8
  · exact g125B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g125G : graphValid g125 (boundsBefore K119) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low125 : Lower true (varsX 125) (graphGoal 125) 10 := lower_forest (g:=g125) (i:=0) (hints:=24578) (before_sound K119 V119) g125G g125T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K125 := extendKnown K119 10 [(125,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V125 : Known true K125 := extend_ok (m:=125) V119 low125 (by decide +kernel)
def g175Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xff801ffffe1fff9ae2,0x181cf000000fc003f03f])),(BitVec.ofNat 152 (word80 [0x450940500441101ac2,0x800f145145145145145]))),((BitVec.ofNat 152 (word80 [0xffffe007fffff8390b,0xb483500003f000fc0fc0])),(BitVec.ofNat 152 (word80 [0x160181602800213803,0xb40140c30c30c30c30c3]))),((BitVec.ofNat 152 (word80 [0xfffffff8001fffd03d,0x39712000fc003f00003f])),(BitVec.ofNat 152 (word80 [0x98020180b082400039,0x3171028a28a28a28a28a]))),((BitVec.ofNat 152 (word80 [0xffffffffffe000462a,0x8bc7903f000000000fc0])),(BitVec.ofNat 152 (word80 [0xe02c0a02c00b824628,0xbc6971c71c71c71c71c]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x4984,0x67ac8fc000003ffff000])),(BitVec.ofNat 152 (word80 [0x300c03010c044104,0x428c0410410410410410]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x2651,0x42404fffffffc0000000])),(BitVec.ofNat 152 (word80 [0x4010040010000000,0x820820820820820]))),(0x0,0x0)]
def g175C : List ColumnInfo := [(2,0,173,0,8),(8,0,167,0,8),(32,0,143,0,8),(1,0,174,0,7),(4,0,171,0,7),(128,0,47,0,7),(5,0,170,0,5),(129,0,46,0,4),(132,0,43,0,4)]
def g175A : List (List Nat) := [[],[32]]
def g175D6 := limbs80 #[#[0xe3c1243e437695254120,0x5]]
def g175D7 := limbs80 #[#[0xf54950bf59520fe54120,0x42a00ff58950bfd8950d,0xc32187c70572186ae8a5,0x481c5c705328c82071b1,0x81c60d4c70c871]]
def g175H7 (j : Nat) := if j=0 then 0xa0 else 0
def g175D8 := limbs80 #[#[0xa38c2461a403faa1fd20,0x1e851c6121c]]
def g175H8 := limbs80 #[#[0x1453,0x1112000000a800,0x70]]
def g175D9 (j : Nat) := if j=0 then 0x5431021bf else 0
def g175H9 (j : Nat) := if j=0 then 0x2824b else 0
def g175L : Nat → Packing
  | 6 => (1,3,4,0,0,0,0,g175D6)
  | 7 => (5,2,4,0,0,8,0,g175D7)
  | 8 => (2,1,4,0,0,6,0,g175D8)
  | 9 => (1,0,4,0,0,0,0,g175D9)
  | _ => emptyPacking
def g175I : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 1 2 0 4 0 0 g175H7
  | 8 => lookupWord 1 23 0 8 3 1 g175H8
  | 9 => lookupWord 1 3 0 6 1 1 g175H9
  | _ => fun _ => none
def g175 : Forest := ⟨175,9,fun i => g175Y[i]?.getD (0,0),g175C,g175A,g175L,g175I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g175P6_0 : block g175 6 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g175B6 : block g175 6 0 1=true := g175P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g175P7_0 : block g175 7 0 4=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g175P7_4 : block g175 7 4 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g175B7 : block g175 7 0 5=true := (@block_merge g175 7 0 4 1 g175P7_0 g175P7_4)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g175P8_0 : block g175 8 0 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g175B8 : block g175 8 0 2=true := g175P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g175P9_0 : block g175 9 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g175B9 : block g175 9 0 1=true := g175P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g175T : checkedTables g175 9 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g175 0 0 0 = true)
  · exact (rfl : block g175 1 0 0 = true)
  · exact (rfl : block g175 2 0 0 = true)
  · exact (rfl : block g175 3 0 0 = true)
  · exact (rfl : block g175 4 0 0 = true)
  · exact (rfl : block g175 5 0 0 = true)
  · exact g175B6
  · exact g175B7
  · exact g175B8
  · exact g175B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g175G : graphValid g175 (boundsBefore K125) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low175 : Lower true (varsX 175) (graphGoal 175) 10 := lower_forest (g:=g175) (i:=0) (hints:=4146) (before_sound K125 V125) g175G g175T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K175 := extendKnown K125 10 [(175,[]),(187,[66]),(190,[32,64])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V175 : Known true K175 := extend_ok (m:=175) V125 low175 (by decide +kernel)
def g183Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xf87ffe01ff8fffffe4,0x13c7300000f8000f83ff])),(BitVec.ofNat 152 (word80 [0x110014140520200420,0x11c13084210842108421]))),((BitVec.ofNat 152 (word80 [0xff87fffe000ff1fe09,0x4badd0001f0001f00000])),(BitVec.ofNat 152 (word80 [0xa01158185641444889,0x4badd39ce739ce739ce7]))),((BitVec.ofNat 152 (word80 [0x7fffffff001ffc7,0xaa986003e0003e007c1f])),(BitVec.ofNat 152 (word80 [0xc22060201801881007,0x82184108421084210842]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x7fffffffffe0012,0x6c4f807c0007c0007fe0])),(BitVec.ofNat 152 (word80 [0x44180406002006110,0x6c068210842108421084]))),((BitVec.ofNat 152 (word80 [0xfff800000000000029,0x84009f800007ffff8000])),(BitVec.ofNat 152 (word80 [0x200808004008000,0x421084210842108]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x10,0x51304ffffff800000000])),(BitVec.ofNat 152 (word80 [0x401010008010000,0x842108421084210]))),(0x0,0x0)]
def g183C : List ColumnInfo := [(2,0,181,0,10)]
def g183A : List (List Nat) := [[],[117],[66],[66,117],[32],[32,117],[32,64],[32,64,117],[64,32],[64,32,117],[64],[64,117]]
def g183D10 (j : Nat) := if j=0 then 0x7f else 0
def g183L : Nat → Packing
  | 10 => (1,0,1,0,0,0,0,g183D10)
  | _ => emptyPacking
def g183I (_ _ : Nat) : Option (Nat × Nat) := none
def g183 : Forest := ⟨183,10,fun i => g183Y[i]?.getD (0,0),g183C,g183A,g183L,g183I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g183P10_0 : block g183 10 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g183B10 : block g183 10 0 1=true := g183P10_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g183T : checkedTables g183 10 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g183 0 0 0 = true)
  · exact (rfl : block g183 1 0 0 = true)
  · exact (rfl : block g183 2 0 0 = true)
  · exact (rfl : block g183 3 0 0 = true)
  · exact (rfl : block g183 4 0 0 = true)
  · exact (rfl : block g183 5 0 0 = true)
  · exact (rfl : block g183 6 0 0 = true)
  · exact (rfl : block g183 7 0 0 = true)
  · exact (rfl : block g183 8 0 0 = true)
  · exact (rfl : block g183 9 0 0 = true)
  · exact g183B10
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g183G : graphValid g183 (boundsBefore K175) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low183 : Lower true (varsX 183) (graphGoal 183) 11 := lower_forest (g:=g183) (i:=0) (hints:=82) (before_sound K175 V175) g183G g183T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K183 := extendKnown K175 11 [(183,[]),(215,[101]),(221,[49,101])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V183 : Known true K183 := extend_ok (m:=183) V175 low183 (by decide +kernel)
def g189Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfffc01ffffe1ffffba,0xc261b0000007c00f83ff])),(BitVec.ofNat 152 (word80 [0x482402024400209a,0x42011004210842108421]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x1ffffe00fffe1fff25,0x3c4b188000f801f07c1f])),(BitVec.ofNat 152 (word80 [0x409008140480404021,0x1c420808421084210842]))),((BitVec.ofNat 152 (word80 [0x1fffffff00001ff058,0xf5694e001f0000000000])),(BitVec.ofNat 152 (word80 [0x8ae1309857088a8258,0xf5694e3def7bdef7bdef]))),((BitVec.ofNat 152 (word80 [0x1fffffffffffe00010,0xaa846f83e0003e007fe0])),(BitVec.ofNat 152 (word80 [0x30040201800030400,0xa0046390842108421084]))),((BitVec.ofNat 152 (word80 [0xe0000000000000000e,0x11ba877c00003fff8000])),(BitVec.ofNat 152 (word80 [0xc0180c060110c0804,0x1b88421084210842108]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xc1,0x4514407fffffc0000000])),(BitVec.ofNat 152 (word80 [0x100201008000100000,0x42108421084210]))),(0x0,0x0)]
def g189C : List ColumnInfo := [(8,0,181,0,10)]
def g189A : List (List Nat) := [[],[84],[66],[66,82],[82,66],[82],[32],[32,84],[32,64],[32,64,80],[32,80,64],[32,80],[64,32],[64,32,82],[64],[64,80],[64,82],[64,82,32],[80,32,66],[80,32],[80,64],[80],[80,66,32],[80,66]]
def g189D10 (j : Nat) := if j=0 then 0x7f else 0
def g189L : Nat → Packing
  | 10 => (1,0,1,0,0,0,0,g189D10)
  | _ => emptyPacking
def g189I (_ _ : Nat) : Option (Nat × Nat) := none
def g189 : Forest := ⟨189,10,fun i => g189Y[i]?.getD (0,0),g189C,g189A,g189L,g189I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g189P10_0 : block g189 10 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g189B10 : block g189 10 0 1=true := g189P10_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g189T : checkedTables g189 10 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g189 0 0 0 = true)
  · exact (rfl : block g189 1 0 0 = true)
  · exact (rfl : block g189 2 0 0 = true)
  · exact (rfl : block g189 3 0 0 = true)
  · exact (rfl : block g189 4 0 0 = true)
  · exact (rfl : block g189 5 0 0 = true)
  · exact (rfl : block g189 6 0 0 = true)
  · exact (rfl : block g189 7 0 0 = true)
  · exact (rfl : block g189 8 0 0 = true)
  · exact (rfl : block g189 9 0 0 = true)
  · exact g189B10
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g189G : graphValid g189 (boundsBefore K183) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low189 : Lower true (varsX 189) (graphGoal 189) 11 := lower_forest (g:=g189) (i:=0) (hints:=28674) (before_sound K183 V183) g189G g189T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K189 := extendKnown K183 11 [(189,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V189 : Known true K189 := extend_ok (m:=189) V183 low189 (by decide +kernel)
def g207Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x7fff007fffe3ffd33b,0x898c000003f00003f03f])),(BitVec.ofNat 152 (word80 [0x8a2502804844112b,0x89885145145145145145]))),((BitVec.ofNat 152 (word80 [0x87ffff803ffffe0c87,0xc35c0000fc0000fc0fc0])),(BitVec.ofNat 152 (word80 [0x102c060b0280088c83,0xc21c30c30c30c30c30c3]))),((BitVec.ofNat 152 (word80 [0x7ffffffc003ffebd4,0x9494003f00003f00003f])),(BitVec.ofNat 152 (word80 [0x2130080c0b10902ad4,0x1414a28a28a28a28a28a]))),((BitVec.ofNat 152 (word80 [0x7fffffffffc002136,0x6d700fc0000fc0000fc0])),(BitVec.ofNat 152 (word80 [0x41c030100c00e12134,0x2d60c30c30c30c30c30c]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xf800000000000014c0,0xc2bf000000ffffff000])),(BitVec.ofNat 152 (word80 [0x20040201001000000,0x10410410410410410]))),((BitVec.ofNat 152 (word80 [0x2829,0x3203fffffff000000000])),(BitVec.ofNat 152 (word80 [0x40080402002000000,0x20820820820820820]))),(0x0,0x0)]
def g207C : List ColumnInfo := [(1,0,206,0,8),(2,0,205,0,8),(4,0,203,0,8),(8,0,199,0,8),(64,0,143,0,8),(128,0,79,0,8),(5,0,202,0,7),(10,0,197,0,7),(3,0,204,0,5),(6,0,201,0,5),(65,0,142,0,5),(66,0,141,0,5),(129,0,78,0,5),(130,0,77,0,5)]
def g207A : List (List Nat) := [[],[118],[49],[49,118],[16,50],[16,50,118],[16,32,48],[16,32,48,118],[32],[32,118],[32,49],[32,49,118],[48,16,33],[48,16,33,118],[48,33],[48,33,118]]
def g207D4 := limbs80 #[#[0x10b88688965515150110,0x110aa86888660554501,0x2058c0aa468c86605545,0xb983b98]]
def g207D5 := limbs80 #[#[0xa0221e30965515150110,0x8155140443c672caa2a2,0x54c910caa280886ac219,0xa221699932195450110b,0x65c1544429d3243b2e0a,0xd4c0ecb82a88853664c7,0x22187b85e01765511087,0x5d95444319f07c12ecaa,0xc930f3b2a88860fe1784,0x818f1816037655110877,0xc154502e3726c0aa8a82,0x9b03b82caa04e6e4d81d,0x12db9360770595408edc,0x96550319f07b92e2b2a8,0xee4b0ac0aa533e4d81dc,0x53627211b0c0600c67c1,0x3847e7869635d57514b4,0x56408005cc10009f999,0x81000c202000000001b2,0x69]]
def g207H5 := limbs80 #[#[0xea000000000f1610028,0x806cb2409d]]
def g207D6 := limbs80 #[#[0x55140443cc5515150110,0x5023be097655110e3965,0xe0d71d8154e3954d8550,0x50110fb1815514044237,0xeb88655140443ce59554,0x59540443aee195450110,0x443aee116550110bbb84,0xe097550110bf3815d540,0x50110afb865d540442fa,0xdeb825d5404437ce0575,0x5c1544433ee197550110,0x4433e1d97055110df171,0xe156455110e3d6559154,0x55110aed821d9544438f,0xaef825d9544423fa1c76,0x5d954442afe117655110,0x4427be0976551109fb80,0xe097655110cfb805d954,0x55110cbf845d9544433b,0x8fd879d954442af61276,0xdd9544427e6037655110,0x442afe116559110cf980,0xe097559110afb805d564,0x54140f395458550502bb,0xf398155150502dee1561,0x5c151503cee055454140,0x503cee015454540f3954,0xe097654540af7815d951,0x54540adf835d951502bb,0xaf5819d9515029fe1576,0x551615029f6167654540,0x502bbe096558540d3f75],#[0x6077055140c7f7559561,0x55140bbb805c554502ee,0xdeb72dc165502e7e0d71,0xdc9655027e6077059540,0x502be6077059540deb80,0xe017159540eeb72dc165,0x59540cef725c565502be,0xadf835c565502bbe0971,0xdc9655033bdcb7159540,0x5033b6077259540eeb80,0xdc96158154cef81dc965,0xd8154cef72d85605533b,0x9df835c760552be60361,0x5c760552b7e0d71d8154,0x70900d419017000cdf83,0x28244450871001d43305,0x374690bf1682a45109b1,0x48f117220424830f71d0,0xd1532985049d13325048,0xa3328614bf16b2d0584a,0x3a0724e11bf3786d4d71,0x804fd1f33d8794f11d7,0x35212374608850d20b41,0x3f27b4e89c5352574a89,0xd0a08a7c61697528a25,0x2adc4003430231b9e506,0xc2dcd003e5f2d00f1834,0x80400404110020c14080,0x84b842c604041e10400,0x2b22009cec884804c601,0x353878030b0a050c5450,0x2099810000104075010],#[0x8112040c0820404001e7,0x42c2054284000010005c,0x427185840dcc342c3080,0x100040000010404303,0xc10b04001002c1420004,0x60532c8c8302281c5042,0x10826cc2660631ca283a,0x305312ac8c840398102b,0x3934020a32080b30407,0xc1]]
def g207H6 := limbs80 #[#[0xf000000000000a040a2,0x7a40000000000000009,0x510a8b00900,0x0,0x3080000000000000000,0xa11000000a0200,0x5000000601000,0xb000000,0x0,0xe00000042e50ce06,0xe0d482a070000000,0x60b000000000a0a00,0xb84000000,0xb03513000f23c880000,0x61200000000000000000,0x586000000000000000]]
def g207D7 := limbs80 #[#[0x277b92caa07395454140,0xf72a8a0221fc5454044,0x437db2a80886f9655011,0x10bf6eaa02217e5d5404,0x4427ebb2a8886bd64551,0x1109feeab22213fdd954,0x15037db0aa0a04fd75d9,0x8540d7aa9b0a81cf5515,0x65503ddb82a8a04fd75d,0x59540bdee4b2a817edc1,0x9655027fb8acaa06fb70,0x2581549fae3b2a81bbdc,0x95404427eb8ec0aa5ef7,0x7055110ff2eaa0221fe5,0x1d954443deb22a8887f9,0xd7655110dfaecaa221bf,0xfdd9544437f3b2a8885f,0xfd6559110bfeecaa221b,0xbf5d564442ffbaac8886,0x7f96154140dfeeab2221,0x1bf5d951503fcb82a2a0,0x7bd5458540dfceca8a8,0x817fdd5615037eb2ac2a,0xa07bf7155140f7ae2aa2,0xa817fdc565503fdb82ca,0xaa06fd7159540fdee4b2,0x2a9fed81605537fb8ac,0xc0aa6ff6158154dfac2b,0xb02a9fbdc960552ffb8a,0xec0aa5fd71d8154dfec3,0x52001bfdc7605537eb8,0xd62842241c4156104096],#[0xa48a4383f43be37a3362,0x6586225d05a857253c4e,0x9685280e7ca74e71869c,0x4a129f89d098c92c8e88,0xb8cb48b04acea98a70a6,0xf8cb4c7ec48c04bf8bc2,0xe3ce14dded9ad72d3cc,0x18fb8f90f3eefaec4e8,0x93be01050c49de30b041,0x6ce28d1421ad44f187ab,0xd1821ae78d5071029ac,0xd6a46ce30a6b9e354103,0x7cd54610d63671428c14,0xf35512ad4cf984162056,0xb533e610254cf983a99,0xaa41a2abe618646aadc5,0x60c566ae18dccd6b8a14,0xe673e35650a293055452,0x32c0455c999b88305260,0x908ccdc50757273e3325,0x995bd61264a65cf8e5a1,0x4518c85611068c28204c,0xa830b1422a8832a32158,0x90422a234422344170e0,0xa040080b8705416a024c,0x86a23364d431629a8654,0xc6081a18b10545082c50,0x48862c41514200291a20,0x882d9a01a20b10d43645,0x102b1086261418440c62,0x26662133ccc439928955,0x2201b3a4448083325214],#[0x25642540519905311045,0x84345e426c680c448053,0x1882cd8]]
def g207H7 := limbs80 #[#[0x4308010e281040246043,0x3420011827a00400001,0xb000001704600a2c700,0x62208130000310241148,0xb000000000003110605c,0x48340000a043016301,0x2087f0420001604c0,0x800000003c1cd01d0000,0x1e0000000068d8000720,0xa004000000000000695c,0x3810ce01001ed8430000,0x9d681900006050886e82,0x2034000481fb16600024,0x6080000000000002c6c,0x114a1700000000000000,0xd13dc0944,0x9063401800018176514,0x8620870000e0c949c000,0xc8859448000000000010,0xf041e295c17e0980000,0x550942a01ec04bd23083,0x3d03a8b4b46b2078d,0xa0000202800019818436,0x112b6d5020024024b83,0x6873c013836f09105015,0x4f088000081490460000,0x300c604fa072908594,0xa0ef5440000f40ba0140,0x60000e4200007a230001,0x416b6613be864893928,0x489000018380001c0f98,0x4000080fc00000000001],#[0x7000040340000000202,0xe4cb4818000a43400008,0x4b307600e95ab8334054,0x1a8000855320dd110513,0xe0ac0a1f0a20001ca1e0,0x1c02dd1e6000e24a,0x41da12b02a0000000000,0x3942d88af42aa910c,0x8000184a0816d93d4254,0x448000528b411c000781,0x20820002c,0x1700ea406c0880000000,0x100a0000002]]
def g207D8 := limbs80 #[#[0xfd9110bf59110fe50110,0x55140bfd8540fe54140b,0x8154bfd9540bf59540ef,0x540ff59110ff55110bfd,0x54ff59540ff58540ff54,0x85a0a800ffd8154ff581,0x17454132450ea318a81f,0x355069c694a227e1ce69,0x798814b288d549e61ca2,0x99728430add590618552,0xa564de61842b7566145,0x7985925dd6115de62843,0x98650bd4a9e620721552,0x862c8d665ca18d295917,0xc2b3c659161e4cf13262,0x33c6591614]]
def g207H8 := limbs80 #[#[0xc5000a007c1800000a80,0x1cf000c4810202180801,0x50128008004482548000,0xccd0003c2412a0000111,0x448211cbd00018883046,0xde07f8b790dc408bdc09,0x3a140a4cbcc3110b5c0,0x7000000000000000000,0x3c25a0e7848e2c8086b,0x3c1800a6c19423ac2800,0x8200000c4d70f4c0f000,0xe0e148a0000000e27e,0x9b2e0000c0db4ace0300,0x3c2fd05dc2c000216,0x5c10af40c3c27f516c15,0x94708879014000a,0x9cb9000376f010d89b00,0x48d620cc0e70844b0e0e,0x2aa17706815ad4a23041,0x4625e89974c000000028,0x123e826e024000d50d00,0x56b01dd0d005a0002903,0x230002c060000432d,0xc0b0000451000000000,0xc9cf004000a0d4000a00,0x89408b81664e181e0003,0xed2d28c430af16fbce38,0x22fa52fa0f0000000043,0x45a8000b0ec000,0xef407c053c1a00000000,0x41b20098ad82,0x42e1cc1c95941800092f],#[0x504d8b54110000100e,0xa0001033000000000000,0x136]]
def g207D9 := limbs80 #[#[0x30bf3e07f553fa81fd10,0x5bd8822aa4b98545687]]
def g207H9 := limbs80 #[#[0xce65308d026288143010,0xa0020d820c4fd853952,0x42c02901521200285584,0x8c6904845bd56c8209,0xf3a9000c080000002860,0x88800000050c0001691c,0x46000000000c8e000000,0x60f0000000110c5421d,0x206000a0728f00,0x3705a2421080b148b2b,0x40a74e650c0e501f1a2]]
def g207D10 (j : Nat) := if j=0 then 0x547613f else 0
def g207H10 := limbs80 #[#[0x120000002,0xc2d47e200001ec000000,0x1100000000000004,0x40032a00000004ca000,0x11aa820042362a]]
def g207L : Nat → Packing
  | 4 => (3,6,4,0,0,5,0,g207D4)
  | 5 => (20,5,4,0,0,8,0,g207D5)
  | 6 => (74,4,4,0,0,11,0,g207D6)
  | 7 => (63,3,4,0,0,12,0,g207D7)
  | 8 => (16,2,4,0,0,10,0,g207D8)
  | 9 => (3,1,4,0,0,6,0,g207D9)
  | 10 => (1,0,4,0,0,0,0,g207D10)
  | _ => emptyPacking
def g207I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 2 13 3 9 2 3 g207H5
  | 6 => lookupWord 7 107 0 12 5 3 g207H6
  | 7 => lookupWord 36 223 6 15 7 4 g207H7
  | 8 => lookupWord 32 179 7 14 6 4 g207H8
  | 9 => lookupWord 12 67 6 12 4 4 g207H9
  | 10 => lookupWord 3 37 1 10 2 4 g207H10
  | _ => fun _ => none
def g207 : Forest := ⟨207,10,fun i => g207Y[i]?.getD (0,0),g207C,g207A,g207L,g207I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g207P4_0 : block g207 4 0 3=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g207B4 : block g207 4 0 3=true := g207P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g207P5_0 : block g207 5 0 20=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g207B5 : block g207 5 0 20=true := g207P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g207P6_0 : block g207 6 0 5=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g207P6_5 : block g207 6 5 69=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g207B6 : block g207 6 0 74=true := (@block_merge g207 6 0 5 69 g207P6_0 g207P6_5)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g207P7_0 : block g207 7 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g207P7_2 : block g207 7 2 24=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g207P7_26 : block g207 7 26 37=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g207B7 : block g207 7 0 63=true := (@block_merge g207 7 0 2 61 g207P7_0 (@block_merge g207 7 2 24 37 g207P7_2 g207P7_26))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g207P8_0 : block g207 8 0 9=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g207P8_9 : block g207 8 9 7=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g207B8 : block g207 8 0 16=true := (@block_merge g207 8 0 9 7 g207P8_0 g207P8_9)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g207P9_0 : block g207 9 0 3=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g207B9 : block g207 9 0 3=true := g207P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g207P10_0 : block g207 10 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g207B10 : block g207 10 0 1=true := g207P10_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g207T : checkedTables g207 10 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g207 0 0 0 = true)
  · exact (rfl : block g207 1 0 0 = true)
  · exact (rfl : block g207 2 0 0 = true)
  · exact (rfl : block g207 3 0 0 = true)
  · exact g207B4
  · exact g207B5
  · exact g207B6
  · exact g207B7
  · exact g207B8
  · exact g207B9
  · exact g207B10
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g207G : graphValid g207 (boundsBefore K189) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low207 : Lower true (varsX 207) (graphGoal 207) 11 := lower_forest (g:=g207) (i:=0) (hints:=4146) (before_sound K189 V189) g207G g207T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K207 := extendKnown K189 11 [(207,[]),(219,[66]),(222,[16,32,48,64])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V207 : Known true K207 := extend_ok (m:=207) V189 low207 (by decide +kernel)
def g231Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xe1fff803ff0ff87fff,0xaf10e1310000f00f00ff])),(BitVec.ofNat 152 (word80 [0x440050280a20110010,0x2310a120111111111111]))),((BitVec.ofNat 152 (word80 [0xfe1ffffc000fff87f8,0x538a2745000f00f00f00])),(BitVec.ofNat 152 (word80 [0x804160302c40a01021,0x530a2305333333333333]))),((BitVec.ofNat 152 (word80 [0x1ffffffff00007ff,0xc42c382f00f00f00f00f])),(BitVec.ofNat 152 (word80 [0x88180403000c22040,0x4428080d222222222222]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x1ffffffffffff800,0x22bd4d20f000000fff0])),(BitVec.ofNat 152 (word80 [0x110a02814005000282,0x154d2444444444444]))),((BitVec.ofNat 152 (word80 [0xffe000000000000000,0x29c4568cf0000fff0000])),(BitVec.ofNat 152 (word80 [0xc03018086044304,0x8c45480444444444444]))),(0x50510980fffff0000000,(BitVec.ofNat 152 (word80 [0x1004020008000400,0x888888888888]))),(0x0,0x0)]
def g231C : List ColumnInfo := [(2,0,229,0,8)]
def g231A : List (List Nat) := [[],[101],[32],[32,101]]
def g231D8 (j : Nat) := if j=0 then 0x7f else 0
def g231L : Nat → Packing
  | 8 => (1,0,1,0,0,0,0,g231D8)
  | _ => emptyPacking
def g231I (_ _ : Nat) : Option (Nat × Nat) := none
def g231 : Forest := ⟨231,8,fun i => g231Y[i]?.getD (0,0),g231C,g231A,g231L,g231I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g231P8_0 : block g231 8 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g231B8 : block g231 8 0 1=true := g231P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g231T : checkedTables g231 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g231 0 0 0 = true)
  · exact (rfl : block g231 1 0 0 = true)
  · exact (rfl : block g231 2 0 0 = true)
  · exact (rfl : block g231 3 0 0 = true)
  · exact (rfl : block g231 4 0 0 = true)
  · exact (rfl : block g231 5 0 0 = true)
  · exact (rfl : block g231 6 0 0 = true)
  · exact (rfl : block g231 7 0 0 = true)
  · exact g231B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g231G : graphValid g231 (boundsBefore K207) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low231 : Lower true (varsX 231) (graphGoal 231) 9 := lower_forest (g:=g231) (i:=0) (hints:=82) (before_sound K207 V207) g231G g231T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K231 := extendKnown K207 9 [(231,[]),(243,[66,50]),(246,[32,64,48])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V231 : Known true K231 := extend_ok (m:=231) V207 low231 (by decide +kernel)
def g235Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfffc00ffffe1fff0da,0x8649a9000007c00f83e0])),(BitVec.ofNat 152 (word80 [0xa82a0502440022da,0x8649000c6318c6318c63]))),((BitVec.ofNat 152 (word80 [0x1fffff007ffe1fff7d,0x28c3108000f801f07c1f])),(BitVec.ofNat 152 (word80 [0x40300c060080404059,0x8031004210842108421]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x1fffffff80001fff20,0xf4695e001f003e00001f])),(BitVec.ofNat 152 (word80 [0x82c030080b08828020,0xe4684a18c6318c6318c6]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x1fffffffffffe00010,0xab846f83e00000007fe0])),(BitVec.ofNat 152 (word80 [0xb0140502c000b0400,0x21846fb18c6318c6318c]))),((BitVec.ofNat 152 (word80 [0xe0000000000000000e,0x11ba877c00003fff8000])),(BitVec.ofNat 152 (word80 [0xc01806030110c0804,0x11908521084210842108]))),((BitVec.ofNat 152 (word80 [0xc1,0x4514407fffffc0000000])),(BitVec.ofNat 152 (word80 [0x100200804000100000,0x42108421084210]))),(0x0,0x0)]
def g235C : List ColumnInfo := [(1,0,234,0,8),(32,0,203,0,8),(2,0,233,0,7),(33,0,202,0,7),(64,0,171,0,7),(8,0,227,0,6),(128,0,107,0,6),(3,0,232,0,5),(9,0,226,0,5),(10,0,225,0,5),(34,0,201,0,5),(65,0,170,0,5),(66,0,169,0,5),(72,0,163,0,5),(96,0,139,0,5),(129,0,106,0,5),(160,0,75,0,5),(35,0,200,0,4),(74,0,161,0,4),(97,0,138,0,4),(130,0,105,0,4),(192,0,43,0,4)]
def g235A : List (List Nat) := [[],[80,97]]
def g235D4 := limbs80 #[#[0xa0a21393985954350510,0x7550d41442b232f32a86,0x89caac8a1aa288760e49,0x8a2171194a154354510b,0x750d51442b2728c3a86a,0x81c6564cb0c05646528,0x5282000014a094a]]
def g235D5 := limbs80 #[#[0x50d51443645d54350510,0x442f8e0965c8510f1154,0x60a65c8510bd38359721,0x505109f18799721442f8,0xf926550d41443e459543,0x55141443cc5955450510,0x442f4e0d6550510f3265,0x6126550510bb38459541,0x505109f18799541442ec,0xf61625495144378e0975,0x50d51442dce156254510,0x443e45914354510f9154,0x6154354510f917450d51,0x54510f528550d51443d4,0xdd28750d514437461d43,0x59151443cc5915454510,0x442f8e097454510b7385,0xe0d76549109f3815d952,0x549109bb845d95244276,0x9db835db524427c60776,0x5c543443745d57150d10,0x44276e1d6550d10bd385,0x6126550d10bd18199543,0x55110e396559154442e6,0x9f3815d954442dc60665,0x5d9544427ae097655110,0x4427c60776551109db83,0x61373595109db835db54,0x782d1388436150780276,0xc5328a3d9d4de6931950,0xcca5914873d9bcc65ba,0x9bd5d2dd5facd4e9b47a],#[0x1b9d9eb74fa1cde571f8,0x10b8100000000240f3b9,0x822504000000480a1c48,0x40b43858204013408212,0x295001003043840c448,0x2000000400000001302,0x94100000000000005]]
def g235H5 := limbs80 #[#[0x96009c0000f2001500,0x84dbb3002d812e]]
def g235D6 := limbs80 #[#[0x3f0a9642887914350510,0xf62a8a0a217c5d72144,0x43b8a92a2885f1755051,0x10fa286a8a21dcd49514,0x443b9aa2a28877154545,0x910be6e2a92217cdd151,0x4443e8b8a86885f171d4,0x9510bb6e6b2a217c5c75,0x51507b2a92a290df1719,0xc85109dee4b2a83cd551,0x541443f932e42887f165,0x254510fe4caa0a21fc59,0xc951443f8b12a2887f15,0x6454510fe2a8a8a21fc5,0xdc552443f8ba2a2887f1,0x97654910fd2c4a9221fc,0xe5db52442fdbb2a4885f,0xfb7558910df2cab12217,0xf699543443ecb2a86885,0x7f17155110fb2eca1a21,0x1de59554443dcb22a888,0x85f97655110ef4caaa22,0x21de59754442fdbb2a88,0x886f96559110bf2edaa2,0xa217edc965442fdbaac8,0xa885fb7459510fb6e6b2,0x8a437e5d265442fcb94c,0xca90fe77154921fcaa4a,0xb2a83ed551515077bb8a,0xaa4a8df77154951ddee4,0x260017bdc964547bbb8,0xe2303e86a0ae1101a826],#[0x80888fe1ce350628b213,0xca9822ee590ac9462664,0x9ea3b6730e09ba356680,0x246e8b10ea1241e810fa,0x1ea1140a764d697126a4,0xb3160ab6556a914ca925,0x182afe5eebc174ae25b6,0xb44432e8712131a626c3,0xf8448307e12d0c501f84,0x501f844841400e112101,0x211861c48307e1261210,0x12101f84984841407e11,0x1001210038448307e114,0x1210b8291e0c48526e,0x507e114123f0308326e1,0x6e1e01213801b844842,0x1c9420725610f1313082,0x625081c9020f07612410,0x60e0850209041c982032,0x8325420850302430b072,0x830f21080242108209a0,0x24093cb8208020b09849,0x982142d0c0c4e0c44347,0xf04025210800f24082c,0xf02082c08224043c842,0x2040810f02210e3c842,0x414106042410504181,0x1810]]
def g235H6 := limbs80 #[#[0xcf38901908980601b080,0xe0008fa400155c005aa0,0xae33e073aa1c001a0aa8,0x1c93c3589ec480073de4,0x28e072a75298b00ab491,0xb1e07e14d2d804d67,0x1eacce7320029321b,0x1b110001054380019c53,0x158970006280075362ae,0x70d000002c849f2c355a,0x10840018c109a2000]]
def g235D7 := limbs80 #[#[0xc54510fc50510fcc8510,0x58452be58052f650d10f,0x4910fe54910dbd4a52bd,0x110fe55110fe58910fed,0x10fe59510fe59110fed5,0x1fb54921fd54521fe995,0xbf59721fb54b21bf5952,0xf54951bf59541fd54541,0x55151bfd8951dfd4951d,0x4b51bfd9151dfd5151df,0x552bf59351bf58b51df5,0x51bf58752bf59652bfd8,0x1ff55151ff58951ff549,0xffd8552ff58552ff5915,0xc330550880be0d80d800,0x50f21bb3245a4a01171d,0x882ee598a8d40a5f47a8,0x41a7f0f59d33846c4ce5,0xca1139a6249b90117a1e,0x24187c2b43adb5669bd1,0x747242c0281c961143e1,0x18689130861a2444301,0xc00e9b092170061a244c,0x21307c24850f030a6242,0x78185312160074d8490a,0x520fc21c616983e12428,0x2984908952610e985809,0x294c1849098036124260,0x2130e08434429830c21a,0x490a54a61c0485298309,0x28484c18431210a06c18,0x31210a940d870121b0e0],#[0x1b092130e028484c380,0x830d8701210361c0484c,0xc04840d8700d122e1c04,0x503282420c1611410361,0x1065048454a09182422a,0xc15]]
def g235H7 := limbs80 #[#[0x9e364532d22100177401,0x292000904c6d501,0x246000000f5e0011b800,0xb80030a70000001d81f7,0x6,0x53000000155621534000,0xc03f65096800001ea000,0x958000018c80043,0x7a000415001920000000,0x73d0018f800723000,0x689c1cc2fc79a500000,0xe5a66ed8000000000000,0x59d31000026001449d39,0xa76d8ed29226003c44b5,0x400031cb448ef0880019,0x43098d0512d0,0x8ba158ad38bf06000000,0x7dcc0030200d000ae221,0x31e8ce8]]
def g235D8 := limbs80 #[#[0xd51fea0ffc87fa43f910,0xa5fe52fea97f14bfea3f,0x4d257210cc4212003fe,0x8214840070a1485a2482,0x861a18121060a180d146,0x91c28214861540868214,0x2451a181210408636084,0x218121841a180d]]
def g235H8 := limbs80 #[#[0x4117d5151108702041,0x80092a40e4990b000f14,0x38a00000210,0x15714a4262204000000,0x3eb000001e18006520,0xd110e2f3663ec4116000,0x2ba380b2600030d00191,0x1c8a20024d512001c665,0xda80036f824b94000004,0xf87d0eb8e7c200220800,0x52d11700119800000fa,0x73b9e001e33416480016,0x189d8200000032f,0x75a08800034471200000,0x50]]
def g235D9 (j : Nat) := if j=0 then 0x2082013f else 0
def g235H9 := limbs80 #[#[0xb08000000748000e3e,0xd00a0940800e450800,0x8c00f200382620000000,0x3ea00b33]]
def g235L : Nat → Packing
  | 4 => (7,5,5,0,0,6,0,g235D4)
  | 5 => (45,4,5,0,0,9,0,g235D5)
  | 6 => (63,3,5,0,0,11,0,g235D6)
  | 7 => (40,2,5,0,0,11,0,g235D7)
  | 8 => (10,1,5,0,0,9,0,g235D8)
  | 9 => (1,0,5,0,0,0,0,g235D9)
  | _ => emptyPacking
def g235I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 2 17 0 8 3 1 g235H5
  | 6 => lookupWord 14 71 6 11 6 1 g235H6
  | 7 => lookupWord 18 127 4 11 6 1 g235H7
  | 8 => lookupWord 15 97 4 11 6 1 g235H8
  | 9 => lookupWord 3 29 3 9 4 1 g235H9
  | _ => fun _ => none
def g235 : Forest := ⟨235,9,fun i => g235Y[i]?.getD (0,0),g235C,g235A,g235L,g235I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P4_0 : block g235 4 0 7=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g235B4 : block g235 4 0 7=true := g235P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P5_0 : block g235 5 0 2=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P5_2 : block g235 5 2 43=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g235B5 : block g235 5 0 45=true := (@block_merge g235 5 0 2 43 g235P5_0 g235P5_2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P6_0 : block g235 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P6_1 : block g235 6 1 19=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P6_20 : block g235 6 20 43=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g235B6 : block g235 6 0 63=true := (@block_merge g235 6 0 1 62 g235P6_0 (@block_merge g235 6 1 19 43 g235P6_1 g235P6_20))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P7_0 : block g235 7 0 7=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P7_7 : block g235 7 7 27=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P7_34 : block g235 7 34 6=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g235B7 : block g235 7 0 40=true := (@block_merge g235 7 0 7 33 g235P7_0 (@block_merge g235 7 7 27 6 g235P7_7 g235P7_34))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P8_0 : block g235 8 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P8_1 : block g235 8 1 9=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g235B8 : block g235 8 0 10=true := (@block_merge g235 8 0 1 9 g235P8_0 g235P8_1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P9_0 : block g235 9 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g235B9 : block g235 9 0 1=true := g235P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235T : checkedTables g235 9 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g235 0 0 0 = true)
  · exact (rfl : block g235 1 0 0 = true)
  · exact (rfl : block g235 2 0 0 = true)
  · exact (rfl : block g235 3 0 0 = true)
  · exact g235B4
  · exact g235B5
  · exact g235B6
  · exact g235B7
  · exact g235B8
  · exact g235B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235G : graphValid g235 (boundsBefore K231) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low235 : Lower true (varsX 235) (graphGoal 235) 10 := lower_forest (g:=g235) (i:=0) (hints:=4149) (before_sound K231 V231) g235G g235T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K235 := extendKnown K231 10 [(235,[]),(238,[32]),(250,[64,32])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V235 : Known true K235 := extend_ok (m:=235) V231 low235 (by decide +kernel)
def g237Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfffc01ffffe1ffffb2,0xd241b1000007c00f83ff])),(BitVec.ofNat 152 (word80 [0x4824020244002092,0x52011004210842108421]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x1ffffe00fffe1fff25,0x2ccb188000f801f07c1f])),(BitVec.ofNat 152 (word80 [0x409008140480404021,0xc4a0808421084210842]))),((BitVec.ofNat 152 (word80 [0x1fffffff00001ff058,0xf4694e001f003e000000])),(BitVec.ofNat 152 (word80 [0x82e030181708828258,0xf4494a1ce739ce739ce7]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x1fffffffffffe00010,0xab846f83e00000007fe0])),(BitVec.ofNat 152 (word80 [0xb0140a058000b0400,0xa18467b18c6318c6318c]))),((BitVec.ofNat 152 (word80 [0xe0000000000000000e,0x11ba877c00003fff8000])),(BitVec.ofNat 152 (word80 [0xc0180c060110c0804,0x1b08521084210842108]))),((BitVec.ofNat 152 (word80 [0xc1,0x4514407fffffc0000000])),(BitVec.ofNat 152 (word80 [0x100201008000100000,0x42108421084210]))),(0x0,0x0)]
def g237C : List ColumnInfo := [(8,0,229,0,8),(32,0,205,0,8),(64,0,173,0,8),(1,0,236,0,7),(4,0,233,0,7),(128,0,109,0,7),(0,8,37,192,6),(5,0,232,0,5),(9,0,228,0,5),(128,8,37,64,5),(129,0,108,0,4),(132,0,105,0,4)]
def g237A : List (List Nat) := [[],[32]]
def g237D5 (j : Nat) := if j=0 then 0x2f2e0d7154120 else 0
def g237D6 := limbs80 #[#[0x26fb9aca887715154110,0xdd6c2a8241da5455048,0x43f4b8aa0906df735951,0x391eda88440177dcd615,0xb931f2e0209e3c838961,0x41e2d047211a0ae22790,0xc43840]]
def g237H6 (j : Nat) := if j=0 then 0x4 else 0
def g237D7 := limbs80 #[#[0xbd8520fa54120bb58910,0x54520bf59510fe54110b,0x8550bfd8550df54550fb,0xd3918096361384800ff5,0xe98e448d2478e448b3e8,0x4a938e438d8a99102141,0xa631e448a59580f96231,0x6391429650b863929190,0x59488e2298]]
def g237H7 := limbs80 #[#[0xee9c1581248000314020,0x2874]]
def g237D8 := limbs80 #[#[0x88a4b807f543fa21ed20,0x1ca3846471808356838c,0x2a851c612]]
def g237H8 := limbs80 #[#[0x2,0x0,0x0,0x660000000000,0x0,0x4a000000,0x0,0x0,0x0,0x0,0x36a00000000000000,0x0,0x0,0xe7000000,0x0,0x0,0xa400000c600000000000,0x1,0x38c0000000,0x2400000722c200710]]
def g237D9 (j : Nat) := if j=0 then 0x5431201bf else 0
def g237H9 := limbs80 #[#[0x6c00000d400000,0x800e7e000]]
def g237L : Nat → Packing
  | 5 => (1,4,4,0,0,0,0,g237D5)
  | 6 => (7,3,4,0,0,8,0,g237D6)
  | 7 => (9,2,4,0,0,9,0,g237D7)
  | 8 => (3,1,4,0,0,7,0,g237D8)
  | 9 => (1,0,4,0,0,0,0,g237D9)
  | _ => emptyPacking
def g237I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 2 0 4 0 0 g237H6
  | 7 => lookupWord 2 11 3 8 3 1 g237H7
  | 8 => lookupWord 2 179 1 9 4 1 g237H8
  | 9 => lookupWord 1 19 0 7 2 1 g237H9
  | _ => fun _ => none
def g237 : Forest := ⟨237,9,fun i => g237Y[i]?.getD (0,0),g237C,g237A,g237L,g237I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P5_0 : block g237 5 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g237B5 : block g237 5 0 1=true := g237P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P6_0 : block g237 6 0 4=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P6_4 : block g237 6 4 3=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g237B6 : block g237 6 0 7=true := (@block_merge g237 6 0 4 3 g237P6_0 g237P6_4)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P7_0 : block g237 7 0 3=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P7_3 : block g237 7 3 5=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P7_8 : block g237 7 8 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g237B7 : block g237 7 0 9=true := (@block_merge g237 7 0 3 6 g237P7_0 (@block_merge g237 7 3 5 1 g237P7_3 g237P7_8))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P8_0 : block g237 8 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P8_1 : block g237 8 1 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g237B8 : block g237 8 0 3=true := (@block_merge g237 8 0 1 2 g237P8_0 g237P8_1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P9_0 : block g237 9 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g237B9 : block g237 9 0 1=true := g237P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237T : checkedTables g237 9 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g237 0 0 0 = true)
  · exact (rfl : block g237 1 0 0 = true)
  · exact (rfl : block g237 2 0 0 = true)
  · exact (rfl : block g237 3 0 0 = true)
  · exact (rfl : block g237 4 0 0 = true)
  · exact g237B5
  · exact g237B6
  · exact g237B7
  · exact g237B8
  · exact g237B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237G : graphValid g237 (boundsBefore K235) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low237 : Lower true (varsX 237) (graphGoal 237) 10 := lower_forest (g:=g237) (i:=0) (hints:=24578) (before_sound K235 V235) g237G g237T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K237 := extendKnown K235 10 [(237,[]),(249,[66]),(252,[32,16,65])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V237 : Known true K237 := extend_ok (m:=237) V235 low237 (by decide +kernel)
def g245Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x9fe7fe01fe7f9ff8fe,0x90000003e007c00f83ff])),(BitVec.ofNat 152 (word80 [0x4004040401001000,0x21084210842108421]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x1ff9fffe007fe7ff1c,0x6040007c00f801f07c1f])),(BitVec.ofNat 152 (word80 [0x8008080802002000,0x42108421084210842]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xe001ffffff8007ffe0,0xb000f801f003e007fe0])),(BitVec.ofNat 152 (word80 [0x10010101004004000,0x84210842108421084]))),((BitVec.ofNat 152 (word80 [0x1fffffffff80003,0xa9c1f00000003fff8000])),(BitVec.ofNat 152 (word80 [0x4a14a0a0a02802824b,0xa9d08421084210842108]))),((BitVec.ofNat 152 (word80 [0xfffe00000000000003,0x773e00001fffc0000000])),(BitVec.ofNat 152 (word80 [0xc00c0c0c130530493,0x77108421084210842108]))),((BitVec.ofNat 152 (word80 [1,0x4bfffffe00000000000])),(BitVec.ofNat 152 (word80 [0x100101010040040000,0x210842108421084210]))),(0x0,0x0)]
def g245C : List ColumnInfo := [(32,0,213,0,10)]
def g245A : List (List Nat) := [[],[101],[116],[116,101],[66],[66,101],[66,114],[66,114,101],[114,66],[114,66,101],[114],[114,101],[32],[32,101],[32,116],[32,116,101],[32,64],[32,64,101],[32,64,112],[32,64,112,101],[32,112,64],[32,112,64,101],[32,112],[32,112,101],[64,32],[64,32,101],[64,32,114],[64,32,114,101],[64],[64,101],[64,112],[64,112,101],[64,114],[64,114,101],[64,114,32],[64,114,32,101],[112,32,66],[112,32,66,101],[112,32],[112,32,101],[112,64],[112,64,101],[112],[112,101],[112,66,32],[112,66,32,101],[112,66],[112,66,101]]
def g245D10 (j : Nat) := if j=0 then 0x7f else 0
def g245L : Nat → Packing
  | 10 => (1,0,1,0,0,0,0,g245D10)
  | _ => emptyPacking
def g245I (_ _ : Nat) : Option (Nat × Nat) := none
def g245 : Forest := ⟨245,10,fun i => g245Y[i]?.getD (0,0),g245C,g245A,g245L,g245I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g245P10_0 : block g245 10 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g245B10 : block g245 10 0 1=true := g245P10_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g245T : checkedTables g245 10 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g245 0 0 0 = true)
  · exact (rfl : block g245 1 0 0 = true)
  · exact (rfl : block g245 2 0 0 = true)
  · exact (rfl : block g245 3 0 0 = true)
  · exact (rfl : block g245 4 0 0 = true)
  · exact (rfl : block g245 5 0 0 = true)
  · exact (rfl : block g245 6 0 0 = true)
  · exact (rfl : block g245 7 0 0 = true)
  · exact (rfl : block g245 8 0 0 = true)
  · exact (rfl : block g245 9 0 0 = true)
  · exact g245B10
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g245G : graphValid g245 (boundsBefore K237) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low245 : Lower true (varsX 245) (graphGoal 245) 11 := lower_forest (g:=g245) (i:=0) (hints:=2) (before_sound K237 V237) g245G g245T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K245 := extendKnown K237 11 [(245,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V245 : Known true K245 := extend_ok (m:=245) V237 low245 (by decide +kernel)
def g127Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x4a3d875d4009000000,0xff000000ff00ff00ff])),(BitVec.ofNat 152 (word80 [0x4810831d0009050505,0x5050505050505050505]))),((BitVec.ofNat 152 (word80 [0x40c0068aefcb000000,0xff000000ff000000ff00])),(BitVec.ofNat 152 (word80 [0x40c00608cf41131313,0x13131313131313131313]))),((BitVec.ofNat 152 (word80 [0x17000858ec200000ff,0xff0000ff0000ff])),(BitVec.ofNat 152 (word80 [0x3000040ec200a0a0a,0xa0a0a0a0a0a0a0a0a0a]))),((BitVec.ofNat 152 (word80 [0x4f78b000b0be00ff00,0xff00])),(BitVec.ofNat 152 (word80 [0xf38b00030be6c6c6c,0x6c6c6c6c6c6c6c6c6c6c]))),((BitVec.ofNat 152 (word80 [0xa022fe2403b0ff0000,0xff000000ffff0000])),(BitVec.ofNat 152 (word80 [0x20222c000390303030,0x30303030303030303030]))),((BitVec.ofNat 152 (word80 [0xbc0950031552000000,0xffffffff00000000])),(BitVec.ofNat 152 (word80 [0x940950021002c0c0c0,0xc0c0c0c0c0c0c0c0c0c0]))),((BitVec.ofNat 152 (word80 [0x919621a01a05ffffff,0xffff0000000000000000])),(BitVec.ofNat 152 (word80 [0x900400a00000808080,0x80808080808080808080]))),(0x0,0x0),(0x0,0x0)]
def g127C : List ColumnInfo := [(32,0,95,0,11)]
def g127A : List (List Nat) := [[],[66],[32],[32,64],[64,32],[64]]
def g127D11 (j : Nat) := if j=0 then 0xff else 0
def g127L : Nat → Packing
  | 11 => (1,0,1,0,0,0,0,g127D11)
  | _ => emptyPacking
def g127I (_ _ : Nat) : Option (Nat × Nat) := none
def g127 : Forest := ⟨127,11,fun i => g127Y[i]?.getD (0,0),g127C,g127A,g127L,g127I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P11_0 : block g127 11 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g127B11 : block g127 11 0 1=true := g127P11_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127T : checkedTables g127 11 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g127 0 0 0 = true)
  · exact (rfl : block g127 1 0 0 = true)
  · exact (rfl : block g127 2 0 0 = true)
  · exact (rfl : block g127 3 0 0 = true)
  · exact (rfl : block g127 4 0 0 = true)
  · exact (rfl : block g127 5 0 0 = true)
  · exact (rfl : block g127 6 0 0 = true)
  · exact (rfl : block g127 7 0 0 = true)
  · exact (rfl : block g127 8 0 0 = true)
  · exact (rfl : block g127 9 0 0 = true)
  · exact (rfl : block g127 10 0 0 = true)
  · exact g127B11
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127G : graphValid g127 (boundsBefore K245) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low127 : Lower true (varsX 127) (graphGoal 127) 12 := lower_forest (g:=g127) (i:=0) (hints:=4146) (before_sound K245 V245) g127G g127T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K127 := extendKnown K245 12 [(127,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V127 : Known true K127 := extend_ok (m:=127) V245 low127 (by decide +kernel)
def g191Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x58d09da10900000000,0xff000000ff00ff00ff])),(BitVec.ofNat 152 (word80 [0x50009c810105050505,0x5050505050505050505]))),((BitVec.ofNat 152 (word80 [0xc15b781b8400000000,0xff000000ff000000ff00])),(BitVec.ofNat 152 (word80 [0xc15258180413131313,0x13131313131313131313]))),((BitVec.ofNat 152 (word80 [0x2e3a418000000000ff,0xff0000ff0000ff])),(BitVec.ofNat 152 (word80 [0x2c1a4100000a0a0a0a,0xa0a0a0a0a0a0a0a0a0a]))),((BitVec.ofNat 152 (word80 [0x7b8f8007aa0000ff00,0xff00])),(BitVec.ofNat 152 (word80 [0x3a8d8007aa6c6c6c6c,0x6c6c6c6c6c6c6c6c6c6c]))),((BitVec.ofNat 152 (word80 [0x80e48a4a1300ff0000,0xff000000ffff0000])),(BitVec.ofNat 152 (word80 [0x80e0020a1230303030,0x30303030303030303030]))),((BitVec.ofNat 152 (word80 [0x920562644eff000000,0xffffffff00000000])),(BitVec.ofNat 152 (word80 [0x20520644840404040,0x40404040404040404040]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x2400141c70ffffffff,0xffff0000000000000000])),(BitVec.ofNat 152 (word80 [0x80808080,0x80808080808080808080]))),(0x0,0x0)]
def g191C : List ColumnInfo := [(2,0,189,0,11)]
def g191A : List (List Nat) := [[],[66],[32],[32,64],[64,32],[64]]
def g191D11 (j : Nat) := if j=0 then 0xff else 0
def g191L : Nat → Packing
  | 11 => (1,0,1,0,0,0,0,g191D11)
  | _ => emptyPacking
def g191I (_ _ : Nat) : Option (Nat × Nat) := none
def g191 : Forest := ⟨191,11,fun i => g191Y[i]?.getD (0,0),g191C,g191A,g191L,g191I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191P11_0 : block g191 11 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g191B11 : block g191 11 0 1=true := g191P11_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191T : checkedTables g191 11 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g191 0 0 0 = true)
  · exact (rfl : block g191 1 0 0 = true)
  · exact (rfl : block g191 2 0 0 = true)
  · exact (rfl : block g191 3 0 0 = true)
  · exact (rfl : block g191 4 0 0 = true)
  · exact (rfl : block g191 5 0 0 = true)
  · exact (rfl : block g191 6 0 0 = true)
  · exact (rfl : block g191 7 0 0 = true)
  · exact (rfl : block g191 8 0 0 = true)
  · exact (rfl : block g191 9 0 0 = true)
  · exact (rfl : block g191 10 0 0 = true)
  · exact g191B11
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191G : graphValid g191 (boundsBefore K127) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low191 : Lower true (varsX 191) (graphGoal 191) 12 := lower_forest (g:=g191) (i:=0) (hints:=4146) (before_sound K127 V127) g191G g191T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K191 := extendKnown K127 12 [(191,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V191 : Known true K191 := extend_ok (m:=191) V127 low191 (by decide +kernel)
def g223Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x816503d90000000000,0xff00000000ff00ff00ff])),(BitVec.ofNat 152 (word80 [0x810003d80505050505,0x5050505050505050505]))),((BitVec.ofNat 152 (word80 [0xb5aeb36000000000ff,0xff000000ff00])),(BitVec.ofNat 152 (word80 [0xb5ae12401313131313,0x13131313131313131313]))),((BitVec.ofNat 152 (word80 [0x6a68840b000000ff00,0xff0000ff0000ff])),(BitVec.ofNat 152 (word80 [0x626884030a0a0a0a0a,0xa0a0a0a0a0a0a0a0a0a]))),((BitVec.ofNat 152 (word80 [0x80c9ed360000ff0000,0xff0000000000ff00])),(BitVec.ofNat 152 (word80 [0x41ed362c2c2c2c2c,0x2c2c2c2c2c2c2c2c2c2c]))),((BitVec.ofNat 152 (word80 [0x181518f400ff000000,0xff00000000ffff0000])),(BitVec.ofNat 152 (word80 [0x181518243030303030,0x30303030303030303030]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x12020206ff00000000,0xffffffffff00000000])),(BitVec.ofNat 152 (word80 [0x4040404040,0x40404040404040404040]))),((BitVec.ofNat 152 (word80 [0x65105c00ffffffffff,0xff000000000000000000])),(BitVec.ofNat 152 (word80 [0x8080808080,0x80808080808080808080]))),(0x0,0x0)]
def g223C : List ColumnInfo := [(1,0,222,0,11)]
def g223A : List (List Nat) := [[],[118],[66],[66,118],[49],[49,118],[49,66],[49,66,118],[32],[32,118],[32,64],[32,64,118],[32,49],[32,49,118],[32,49,64],[32,49,64,118],[64,32],[64,32,118],[64],[64,118],[64,49,32],[64,49,32,118],[64,49],[64,49,118]]
def g223D11 (j : Nat) := if j=0 then 0xff else 0
def g223L : Nat → Packing
  | 11 => (1,0,1,0,0,0,0,g223D11)
  | _ => emptyPacking
def g223I (_ _ : Nat) : Option (Nat × Nat) := none
def g223 : Forest := ⟨223,11,fun i => g223Y[i]?.getD (0,0),g223C,g223A,g223L,g223I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P11_0 : block g223 11 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g223B11 : block g223 11 0 1=true := g223P11_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223T : checkedTables g223 11 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g223 0 0 0 = true)
  · exact (rfl : block g223 1 0 0 = true)
  · exact (rfl : block g223 2 0 0 = true)
  · exact (rfl : block g223 3 0 0 = true)
  · exact (rfl : block g223 4 0 0 = true)
  · exact (rfl : block g223 5 0 0 = true)
  · exact (rfl : block g223 6 0 0 = true)
  · exact (rfl : block g223 7 0 0 = true)
  · exact (rfl : block g223 8 0 0 = true)
  · exact (rfl : block g223 9 0 0 = true)
  · exact (rfl : block g223 10 0 0 = true)
  · exact g223B11
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223G : graphValid g223 (boundsBefore K191) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low223 : Lower true (varsX 223) (graphGoal 223) 12 := lower_forest (g:=g223) (i:=0) (hints:=4146) (before_sound K191 V191) g223G g223T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K223 := extendKnown K191 12 [(223,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V223 : Known true K223 := extend_ok (m:=223) V191 low223 (by decide +kernel)
def g239Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x8d240884da46000000,0x3f800003f8001fc07f])),(BitVec.ofNat 152 (word80 [0x81200004d846142850,0xa142850a142850a14285]))),((BitVec.ofNat 152 (word80 [0x502036d521d2000000,0x1fc00001fc000fe03f80])),(BitVec.ofNat 152 (word80 [0x4020149520120c1830,0x60c183060c183060c183]))),((BitVec.ofNat 152 (word80 [0x61d785d0120000000f,0xe00000fe0007f000007f])),(BitVec.ofNat 152 (word80 [0x601785d002002850a1,0x42850a142850a142850a]))),((BitVec.ofNat 152 (word80 [0x113d8c68ace80007f0,0x7f00000000003f80])),(BitVec.ofNat 152 (word80 [0x111588488ce870e1c3,0x870e1c3870e1c3870e1c]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x5cc0cb23850c03f800,0x7ffffc000])),(BitVec.ofNat 152 (word80 [0x1cc04a220508c18306,0xc183060c183060c1830]))),((BitVec.ofNat 152 (word80 [0xaa493022092bfc0000,0x7ffffff800000000])),(BitVec.ofNat 152 (word80 [0xa4820220100810204,0x8102040810204081020]))),((BitVec.ofNat 152 (word80 [0x212401e4411ffffff,0xffff8000000000000000])),(BitVec.ofNat 152 (word80 [0x1020408,0x10204081020408102040]))),(0x0,0x0)]
def g239C : List ColumnInfo := [(32,0,207,0,11)]
def g239A : List (List Nat) := [[],[32]]
def g239D11 (j : Nat) := if j=0 then 0xff else 0
def g239L : Nat → Packing
  | 11 => (1,0,1,0,0,0,0,g239D11)
  | _ => emptyPacking
def g239I (_ _ : Nat) : Option (Nat × Nat) := none
def g239 : Forest := ⟨239,11,fun i => g239Y[i]?.getD (0,0),g239C,g239A,g239L,g239I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g239P11_0 : block g239 11 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g239B11 : block g239 11 0 1=true := g239P11_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g239T : checkedTables g239 11 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g239 0 0 0 = true)
  · exact (rfl : block g239 1 0 0 = true)
  · exact (rfl : block g239 2 0 0 = true)
  · exact (rfl : block g239 3 0 0 = true)
  · exact (rfl : block g239 4 0 0 = true)
  · exact (rfl : block g239 5 0 0 = true)
  · exact (rfl : block g239 6 0 0 = true)
  · exact (rfl : block g239 7 0 0 = true)
  · exact (rfl : block g239 8 0 0 = true)
  · exact (rfl : block g239 9 0 0 = true)
  · exact (rfl : block g239 10 0 0 = true)
  · exact g239B11
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g239G : graphValid g239 (boundsBefore K223) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low239 : Lower true (varsX 239) (graphGoal 239) 12 := lower_forest (g:=g239) (i:=0) (hints:=4146) (before_sound K223 V223) g239G g239T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K239 := extendKnown K223 12 [(239,[]),(251,[66]),(254,[32,64])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V239 : Known true K239 := extend_ok (m:=239) V223 low239 (by decide +kernel)
def g247Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfffff6023894443520,0xf8000f8000f83ff])),(BitVec.ofNat 152 (word80 [0x806001890401501,0x8421084210842108421]))),((BitVec.ofNat 152 (word80 [0xffc0e781a25d8a840,0x1f0001f0001f00000])),(BitVec.ofNat 152 (word80 [0x20904678182558a847,0x39ce739ce739ce739ce7]))),((BitVec.ofNat 152 (word80 [0xfffe430c54d1841a0,0x3e0003e0003e007c1f])),(BitVec.ofNat 152 (word80 [0x402000308505084022,0x10842108421084210842]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xf000018d901934a240,0x7c0007c0007c0007fe0])),(BitVec.ofNat 152 (word80 [0xc08089000814a244,0x21084210842108421084]))),((BitVec.ofNat 152 (word80 [0x22e6302a11a80,0xf80000000007ffff8000])),(BitVec.ofNat 152 (word80 [0x850100066202a10088,0x42108421084210842108]))),((BitVec.ofNat 152 (word80 [0x19d422404344df,0x7ffff800000000])),(BitVec.ofNat 152 (word80 [0x60219042240030088,0x42108421084210842108]))),((BitVec.ofNat 152 (word80 [0x10ca20b801f,0xffffff80000000000000])),(BitVec.ofNat 152 (word80 [0x80000000000000010,0x84210842108421084210]))),(0x0,0x0)]
def g247C : List ColumnInfo := [(2,0,245,0,11)]
def g247A : List (List Nat) := [[],[101],[66],[66,101],[32],[32,101],[32,64],[32,64,101],[64,32],[64,32,101],[64],[64,101]]
def g247D11 (j : Nat) := if j=0 then 0xff else 0
def g247L : Nat → Packing
  | 11 => (1,0,1,0,0,0,0,g247D11)
  | _ => emptyPacking
def g247I (_ _ : Nat) : Option (Nat × Nat) := none
def g247 : Forest := ⟨247,11,fun i => g247Y[i]?.getD (0,0),g247C,g247A,g247L,g247I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P11_0 : block g247 11 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g247B11 : block g247 11 0 1=true := g247P11_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247T : checkedTables g247 11 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g247 0 0 0 = true)
  · exact (rfl : block g247 1 0 0 = true)
  · exact (rfl : block g247 2 0 0 = true)
  · exact (rfl : block g247 3 0 0 = true)
  · exact (rfl : block g247 4 0 0 = true)
  · exact (rfl : block g247 5 0 0 = true)
  · exact (rfl : block g247 6 0 0 = true)
  · exact (rfl : block g247 7 0 0 = true)
  · exact (rfl : block g247 8 0 0 = true)
  · exact (rfl : block g247 9 0 0 = true)
  · exact (rfl : block g247 10 0 0 = true)
  · exact g247B11
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247G : graphValid g247 (boundsBefore K239) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low247 : Lower true (varsX 247) (graphGoal 247) 12 := lower_forest (g:=g247) (i:=0) (hints:=82) (before_sound K239 V239) g247G g247T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K247 := extendKnown K239 12 [(247,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V247 : Known true K247 := extend_ok (m:=247) V239 low247 (by decide +kernel)
def g253Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfcca50a08819ca0000,0x3f00003f000fc0fff])),(BitVec.ofNat 152 (word80 [0x4c2100008180a0410,0x41041041041041041041]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xf9940e632089310000,0xfc0000fc003f03f03f])),(BitVec.ofNat 152 (word80 [0x1100a620081100820,0x82082082082082082082]))),((BitVec.ofNat 152 (word80 [0x2d799f2fa20040000,0x3f00003f000000000000])),(BitVec.ofNat 152 (word80 [0x12d799f2aa20043cf3,0xcf3cf3cf3cf3cf3cf3cf]))),((BitVec.ofNat 152 (word80 [0x213396247460000f,0xc0000fc0000fc003ffc0])),(BitVec.ofNat 152 (word80 [0x202121802060601041,0x4104104104104104104]))),((BitVec.ofNat 152 (word80 [0x245cc1d91c48203f0,0xffffc0000])),(BitVec.ofNat 152 (word80 [0x4204c41d9104806186,0x18618618618618618618]))),((BitVec.ofNat 152 (word80 [0x53a8400572681fc00,0xffffff000000000])),(BitVec.ofNat 152 (word80 [0x800804005506814104,0x10410410410410410410]))),((BitVec.ofNat 152 (word80 [0x200214809021cffff,0xfffff000000000000000])),(BitVec.ofNat 152 (word80 [0x8208,0x20820820820820820820]))),(0x0,0x0)]
def g253C : List ColumnInfo := [(8,0,245,0,11)]
def g253A : List (List Nat) := [[],[66],[32],[32,64],[64,32],[64]]
def g253D11 (j : Nat) := if j=0 then 0xff else 0
def g253L : Nat → Packing
  | 11 => (1,0,1,0,0,0,0,g253D11)
  | _ => emptyPacking
def g253I (_ _ : Nat) : Option (Nat × Nat) := none
def g253 : Forest := ⟨253,11,fun i => g253Y[i]?.getD (0,0),g253C,g253A,g253L,g253I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P11_0 : block g253 11 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g253B11 : block g253 11 0 1=true := g253P11_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253T : checkedTables g253 11 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g253 0 0 0 = true)
  · exact (rfl : block g253 1 0 0 = true)
  · exact (rfl : block g253 2 0 0 = true)
  · exact (rfl : block g253 3 0 0 = true)
  · exact (rfl : block g253 4 0 0 = true)
  · exact (rfl : block g253 5 0 0 = true)
  · exact (rfl : block g253 6 0 0 = true)
  · exact (rfl : block g253 7 0 0 = true)
  · exact (rfl : block g253 8 0 0 = true)
  · exact (rfl : block g253 9 0 0 = true)
  · exact (rfl : block g253 10 0 0 = true)
  · exact g253B11
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253G : graphValid g253 (boundsBefore K247) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low253 : Lower true (varsX 253) (graphGoal 253) 12 := lower_forest (g:=g253) (i:=0) (hints:=24578) (before_sound K247 V247) g253G g253T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K253 := extendKnown K247 12 [(253,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V253 : Known true K253 := extend_ok (m:=253) V247 low253 (by decide +kernel)
def g255Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x1ff0000001ff007,0xfc01ff01140310319ecf])),(BitVec.ofNat 152 (word80 [0x140a05028140a05028,0x140a0501100100108e42]))),((BitVec.ofNat 152 (word80 [0x3fe0000003fe00000,0x3fe0008580c04cde7d0])),(BitVec.ofNat 152 (word80 [0x4c26130984c2613098,0x4c2613085004044da3c0]))),((BitVec.ofNat 152 (word80 [0xfc0000007fc0000ff8,0x1ff0260302b0e78c9])),(BitVec.ofNat 152 (word80 [0x28140a05028140a050,0x28140a02401009047080]))),(0x3fe00138300b3f07f02,(BitVec.ofNat 152 (word80 [0xb0d86c361b0d86c361,0xb0d86c130100b3b05c02]))),((BitVec.ofNat 152 (word80 [0xff8000000fff,0xfc00001c00c0c3ff800c])),(BitVec.ofNat 152 (word80 [0xc06030180c06030180,0xc0603018004042e90000]))),((BitVec.ofNat 152 (word80 [0xfffffffff000,0x200300fc000037])),(BitVec.ofNat 152 (word80 [0x180c06030180c0603,0x180c0000300b0000035]))),((BitVec.ofNat 152 (word80 [0xffffff000000000000,0xc003ff00000000])),(BitVec.ofNat 152 (word80 [0x10080402010080402,0x100804002aa00000000]))),(0xfffc0000000020,(BitVec.ofNat 152 (word80 [0x20100804020100804,0x20100a4ac0000000000]))),(0x0,0x0)]
def g255C : List ColumnInfo := [(1,0,254,0,12),(2,0,253,0,12),(4,0,251,0,12),(8,0,247,0,12),(16,0,239,0,12),(32,0,223,0,12),(64,0,191,0,12),(128,0,127,0,12),(10,0,245,0,11),(33,0,222,0,11),(34,0,221,0,11),(36,0,219,0,11),(40,0,215,0,11),(48,0,207,0,11),(66,0,189,0,11),(72,0,183,0,11),(96,0,159,0,11),(160,0,95,0,11),(0,8,53,194,10),(3,0,252,0,10),(5,0,250,0,10),(6,0,249,0,10),(17,0,238,0,10),(18,0,237,0,10),(20,0,235,0,10),(65,0,190,0,10),(68,0,187,0,10),(80,0,175,0,10),(130,0,125,0,10),(192,0,63,0,10),(9,0,246,0,9),(12,0,243,0,9),(24,0,231,0,9),(128,8,53,66,9),(129,0,126,0,9),(132,0,123,0,9),(136,0,119,0,9),(144,0,111,0,9),(0,2,21,232,8),(21,0,234,0,8),(1,8,52,194,7),(4,8,49,194,7),(7,0,248,0,7),(16,8,37,194,7),(19,0,236,0,7),(22,0,233,0,7),(69,0,186,0,7),(81,0,174,0,7),(84,0,171,0,7),(128,2,21,104,7),(131,0,124,0,7),(134,0,121,0,7),(146,0,109,0,7),(193,0,62,0,7),(196,0,59,0,7),(208,0,47,0,7),(13,0,242,0,6),(25,0,230,0,6),(129,8,52,66,6),(132,8,49,66,6),(133,0,122,0,6),(137,0,118,0,6),(140,0,115,0,6),(145,0,110,0,6),(148,0,107,0,6),(152,0,103,0,6),(160,2,21,72,6),(23,0,232,0,5),(29,0,226,0,5),(85,0,170,0,5),(149,0,106,0,5),(135,0,120,0,4),(150,0,105,0,4),(197,0,58,0,4),(209,0,46,0,4),(212,0,43,0,4)]
def g255A : List (List Nat) := [[],[66],[32],[32,64],[64,32],[64]]
def g255D6 := limbs80 #[#[0x75dd461965649905d120,0x3d0e7a102dc0a]]
def g255D7 := limbs80 #[#[0x32fc4f0bb56a19750910,0x53b6c32caba2e4a02419,0x75d96595a45c940483f0,0xa30cb2b44ba2e0907d0a,0x71186689745c120fc14e,0x3344d02e8b2241e8a9a6,0x6e58759564483d153aec,0xcb0eb2ac8906c9af0bc0,0x6616559120e935e1780d,0x9320ba241b26bc2f01b7,0x64174483e453a8c32cac,0x82e8907c1a75d8659592,0x5d120f854ea30cbb324c,0xa241b1a9c77118664990,0x48370738ee230cb2b20b,0x6c9af0bc06e58659574,0xd935e1780db330b2ae89,0x9abc2f03b468d875d120,0xd785e076ad0b30ba2419,0xf0bc06d1a85d96548326,0x17c8e361608806006a9a,0x71b819ebe53238ec6c31,0xbc02e6294403b1d2e6,0x52c87098a50592304036,0x45040886a2197210348,0x40e11a8465e870c04504,0x1a84656870e11a8465e8,0xe873a1023a1ce840a1]]
def g255H7 (j : Nat) := if j=0 then 0x0 else 0
set_option maxRecDepth 16000 in
def g255D8 := limbs80 #[#[0x83e0a61d765954250120,0x120ba29c85d965509404,0x40483c8a65d865954250,0x250120ba2bc761965509,0x58940483c2a65d865d94,0xd16250120d8a9b761d64,0x57458940483e0a61d655,0x965d16250120ec29a759,0x76597458940483c2a61d,0x69d975956250120e4a9a,0x2986595745c94048391a,0xd1a725765957250120f8,0xf06997619655c940482,0x483c2a65d845d1625812,0x8120f82965611745c960,0x960483c1a65d65611725,0x7258120e46997597a45c,0x45c970482d1af1197595,0xe51725c120d869b85956,0x97945c970483c1a61965,0x186595725c120d469b65,0xc76196550940482e1af1,0xa719875954250120fa29,0xe29ba5957458940483e8,0x3e2a61db65d16250120e,0x20fa2bc461d655894048,0x483b8a711a759562501,0x50120f8abc461d765894,0xc940483f0a699655d172,0x17250120f8a9b6619745,0xa45c940483f0a5d96569,0x56917250120fa2986595],#[0x595a45c940483d8a6596,0x19766917250120ee29a6,0x9965d9a45c940483e2a6,0xaa699966917250120f4a,0xf469c7659655c9404839,0x83d1a65da65957250120,0x120f469c665d655c9404,0x40482d6af11b365d7250,0x550120f83bc461d76595,0x5954048368ef11b85d96,0x1d6550120ba3bc46dd86,0x1875954048368e6dbb46,0xb661d6550120ba39c6ed,0x461d7458960482e8ef11,0xf11b85d16258120f8abc,0xabc46e17458960482eaa,0xd2a65da45917258120da,0xf8a9a6611745c960483,0x483d1a6e5655d1725812,0x8120f46997595a45c960,0x160483d1a71197595725,0x6458120f4a9976c97459,0x25d160482eaaf09b461d,0x6897458120f46997595a,0x1d655d16048399a6a565,0x1a85957458120f83bc46,0xc26a1655d160482e8ef1,0xef11a85d97458120ea6b,0x8ebc26a1765d160482e2,0x2e9af09b461d6558120e,0x20b66bc26d1975956048,0x482e3af09b461d76581],#[0x5c120fc2965651645c97,0xc970483e2a6199459172,0x1725c120f4a996651645,0x845c97048371a6e56559,0x5651725c120f86996595,0x595945c970483e1a6196,0x9965e51725c120f46996,0x9c4619655c970483d1a6,0xa595b25d1645c120f86,0xf8a9866c97459170483f,0x8378a597b2651645c120,0x120dca976ec994591704,0x704835aa65bb2651645c,0x45c120ec69c269d65591,0x5d170482b9af09a95956,0x89745c120f86986595a2,0x9a25d170483b1a699656,0x86595745c120e8e9a661,0x6597a265170483e0e711,0x65965e89945c120ec697,0x69b6597a26517048399a,0xb8a595a26817459120ce,0xeca976689a05d164483,0x483aaa619a2681745912,0x9120ba3bc06d18759564,0x564482c9ef01b961d655,0x6559120d27bc06e58759,0x75956448359a6c9b065d,0x6616559120b23fc46e19,0xd1875d964482c9ef01b7,0x965649905d120b8bbc06,0x865959264174483d1a5d],#[0xa61976649905d120f269,0x83fc46617659574483c3,0x3c1ef01985d9655d120b,0x20d83fc46e1765957448,0x448360f6ddb4619655d1,0x5d120b27bc06e5865957,0x957448268ff11b961965,0x9655d120b279c0ae5865,0x865957448249f72eb961,0x9619655d1209a3dc4ee5,0xed1875957448261f71fb,0x1bb461d655d120d83db6,0xfc46d98759574482e0f7,0x8f71bb4661655d120b83,0xb279c6ec198595744826,0x82c9ef01b6661655d120,0x520b87bc06d1875d9654,0x65482a9ef01b46a17659,0x25c1609a79c6ec1a461d,0x5c97058372aed1746496,0xd1905c960dc6965ec994,0x17464172583b0e597a45,0x98595745c960e4b996e9,0x26d18759572582e0ff11,0x61965e89845c970b86fc,0x6db6597a2611725c3a1b,0x8faf09a8e819750910cc,0xe37bc56a3a065d42443,0x4434ebed3b26a1975091,0x910d36fb5ec9a865d42,0x9404834dbf0bb56a1975,0x7250120f9a9cb619745c],#[0x55c940483d6a71d96691,0x68d8750120f669ca6596,0x1974591704836eaf0bb4,0x186689745c120f8b9cb6,0xca619655d170483e6a71,0xe699b4619745c120f879,0x8b9c7619a05d164483e2,0x3c9ef01b961d6559120f,0x20f23fc46e1975956448,0x4483c9ef01b766165591,0x59120d3ebb2ec1a961d6,0x61644838faecbb06a587,0x9905d120d3ebb2ec1a76,0x9264174483cea7118664,0x6595905d120f1e9c7619,0x6196564174483e8e7118,0x11865d9905d120f879c7,0x9966d18664174483e2e7,0x6e6ddb4619905d120f2b,0xf27bc06e586595744836,0x8368ff11b9619655d120,0x120f27bc06d998595744,0x744834faecbb06a5865d,0x85d120d9bbc0ed1a361d,0x661744834faecbb06859,0x85985d120d37bb5ec1a1,0x1a6661744834def03b56,0xb46a17659520d3ebb2ec,0x6d1a761965483a9ef01,0xf01b46998759520ba7bc,0xebb2ec1a466176482e9e,0x2faecbb0e919361d20d3],#[0xba6fc26d19859572583,0x2e9ef01b4689875956,0xb824d074817e040c07b0,0x44fb12344050e2831c0a,0x7a91cec6da19b05e415a,0xfc26d4954239886b205c,0x92fecbc12d4cae529dc9,0x3904de035c8d1e32c0c6,0x3890744018fb23cdceaf,0xcd27948fd20546c51504,0x143d4f7136e4cd12fa4a,0x6c459595e855b54f2521,0xfd62a58555f697795cc9,0x368e59f266ad97e64dd8,0x72cdc456f5db4f6b51a7,0xc19eb27945de37609d21,0x620aa818dff57e51f4d7,0x633e8baa29688a21a084,0x59e952a50391ee3f38e1,0xd79d727159b3a68797ca,0x1a6be95ba4ba8e7a17e7,0xaf6eb87ac9aaf9aa96a5,0x64ad65b47acd7b242c3c,0xc2f1cbaeee74b84edccb,0xb17cc4070adc0fefd1bd,0x263c90f230c8ab217c7a,0x98cde3331cc472cacaab,0x9d21b459d0e7419cfb33,0xd47f50cd34b4bfd27f49,0x7b35ccd6b357fd57f53f,0x7f67fd97f632d8b3619d,0xb74cdc7f6f2db4b6bfda],#[0x88e0b4e409dde3758dd4,0x8c844c149c7ce3b831f,0x3b8317879c87e2382c51,0x2720480d806a02e9c7ce,0x69c7ce3a234f87e0c7e2,0x9c87e21f0e02e1994ac1,0xc4e3e71de092671f38e,0x48ec16a0a229570f11ae,0x3791ad0b505331f98ef0,0xf58ea8d7e2342d590211,0xf88ac868588411b052b1,0x92406c51aac7d63b829,0x48d70f51a84dd63eb1de,0x5b829f88f049541960a2,0x1aa0ca48d70f58fac748,0xfcc77053f11990b0b105,0xfc41e4342c4188923598,0xa138a5cc39e3cf1c42e,0x45f38f9c77a12721f88e,0x1df8870b4e40a01b80d4,0x52b08a432d8788d4e3e7,0xef06a231c8fe47782486,0x3a3dd1ce901d83341444,0xa3b2304661e42ce19a0a,0x619d0b605093b690b47d,0x8e491ee12d21f88e0a10,0x5d487e21a30300bed1f6,0x9c84e3e71c4ea3f51c03,0x3c0013011780bb90fb84,0xf1e78e3c87e237098222,0x28790fc4646070171864,0x802e9c70a6193c79e3b8],#[0x38ee0b00b899c84e3df0,0x706006c0357c3ce4271f,0xd405cb8f5c72e4382c4,0x38061590e0a11c1801b0,0x3c12400dc06da16ac7d6,0x300dd46b42d58fac7305,0x2c46469d09990a0a0882,0xa00db31f98e0186641c,0x13a13235e09a0a0a037e,0x1e3cf1dc143c86858881,0xe3bc128a51b04a51a01b,0x38f21a162085d4143c79,0x87412b61f0308233c79e,0x8ec39e3cf1c42e3c8685,0x3c76060f20619c919181,0xc39e4342c508bf82878f,0xa35818e0a1e39f06036e,0x1e78ed0b1867c124e094,0x31231804a414c0c561cf,0xe0920c3278f1179e3bc1,0x8cf1e78eec3986604f,0xe3806b390e8108bc828d,0x6a720e162006ed239c7c,0x7612b08b82938f9c744,0x701a88bd71eb8e5c8705,0xd0a05ba05e09bc78c03,0xa24889d09990b0a08825,0x7876468999081ac0b991,0x2e24db6434282e64206b,0x441aa0b9b2148d1106a8,0x13c192206b02eac83a10,0x47f23a047022e0d2e13c],#[0xcf23f70fc8e5c278247e,0xfc04fc8ef048bc1ae0,0xa6f51f118d4778248020,0x59d1de092503aa19e0a4,0x1d80a306b30ee19747c8,0x4b47da3806b690e0a120,0x491e460801b80bf247b8,0x83bc1430cda42d1f68e,0xf09a90d47ea3806bc142,0x1d118c4df824801b88bd,0x7e0915044c19b0a723f9,0x690c8c0e03c50a723a93,0x1825246435b47da3b429,0xa3ed1d923217e852d219,0x66845a906c20c03721ad,0x9b09a90f810da8fd4768,0x51da9022309a19d47ea3,0x37a8fd475853c122909f,0x242f082ea3bc120460c0,0xbef08d0b14478a14e477,0x8079e09bc209c90e4740,0x71eb8e1cdae438283f23,0x34b8f5c77824990b4095,0x850095033216e438e6d2,0xcc85971eb8ef048e6f82,0x80d78284409404481d50,0x37117ce4271f38e9c6,0x8143c79e3893a790c8c1,0x903c7685b0444186702d,0xe0a0f8a520c9e3ca347,0x1f04ba163c79e3806a79,0x304478f3c76460f21c14],#[0x71f38e7c2721c05c400c,0x1cd90b0a0e130117ce42,0x30a51a0310254cdb63db,0x6141583242e6c7b63bc1,0x2f048ad8e4cde059b21,0x6f43f82474cda059b1d7,0x70a1011a60cd851b1d81,0x233603701b664331f98e,0x31d02fcc86635c28280c,0x467903c79e38c338a523,0xc59b3c86850a117708b0,0x1f08893b81801b9e3cf1,0x1e3cf1c025ec27824ac1,0x8b88c11f08893a21910a,0xca5017ce4271f38ee438,0x163c76c08f21d8418060,0x918d6850f21c161bc018,0x2179e43b09a1414f1c61,0x12f61d936e9098a1078e,0xa326f6125506302ce8e8,0x1ee8e012a08a83181698,0x2c9bec380976125108dd,0x2d06302ce8f747086843,0x8419645c8ea4dac53920,0x519645c8efc1ac53921e,0x2fd09f02e473427f0604,0xf91c037dc3f243d08714,0xa122a0da06a830817f23,0xe04515137c8fe477c0b,0xd49b7848bc8eec2fe0ef,0xc163c86450901e248b91,0x288d84478f3c72094d3b],#[0xe382341193c87a1f82c5,0x13a125688f845a183c79,0x9d3c79e38234119012fa,0xbcc76642e282c88e8446,0x1a3663b3202460f31e89,0xe6664331f98e81b40d59,0x8663f31df02b427425d0,0xc83641ac0c205e02ecc,0xc919cc77e0da13e87f42,0xf83cc86639d09f02f800,0x44060451d233e87f4207,0xd0e30127235919cc7001,0x83e64331ce84f817c03,0xc8663f31ce87f817c03d,0x7b63906c8356c8126c6c,0xb63906c8356c8523456c,0x16b1d03681ad641d082,0x12306d906c75a13e05f0,0xc77e0eb2024611b1cd90,0x384f1245c8ee485e105a,0xa0d505dc8e704fe0ef08,0x489d1d5147486e105024,0x6b832784e87f43bc123d,0x5e1d5827886e106811e4,0xe1f2a57877a087787b86,0x1dd09f411182268cbc41,0x444a9704411b50ebc3de,0x240d7621b0e652ec27d0,0xf43a06f7846458db0f6c,0xa68f21f00ec213d10e87,0x8e12e88cc3a78f3c70,0x8221b9e40f1da23ec27c],#[0x8608118087b090cf1fa,0x8c2a10cf0a15c00102,0x4e0460806c02f017505,0x404901bc867a0404516,0xc005d4190250a044b42,0xe4381246013a294201e0,0xa521c302500c194b219,0x49022840354528402f5,0xa1000450409604a02286,0x6a232e871008a0811808,0xa100bd94a101181013c4,0x9ed0e180bd14a100d594,0x2481142343c09c2017c0,0xc00228204b025011430,0xc1109c04c11a13707f02,0x808c0a10cf0a1509c04,0x21a0d409282e0c092045,0x4170124200041aa0b809,0x83541701243]]
def g255H8 := limbs80 #[#[0xe200101c0020a1400e60,0xd1200000000000003147,0x760982c92a5fac400000,0x8403000e1630c0000080,0x4701822f370070e31aa,0x990001a3000000282000,0x1e2000e1fc10d3]]
set_option maxRecDepth 16000 in
def g255D9 := limbs80 #[#[0xc0907a29865954250120,0x55c970483a34cbacab92,0x308b9242b8221e1a6196,0x879b1845d1215c110f3c,0x9704434f4d42e4a12e08,0xd4b0ea122167aed1825c,0x2976595425012086ff6a,0x483d94c3acaa1280907e,0x84a0241eaa6197650940,0x85d94250120f3530ebb2,0x9d4cbb0ca1280905ba9b,0x2416eaedd8650940483,0x16250120b7576cc3a84a,0xd3ac8b1280907aa98759,0x1f8a5957458940483754,0x50120f952ecba2c4a024,0xe8b12809076a9965d162,0xa69d7458940483cd4c3a,0x20f4d30eb2ac4a0241b6,0x12809076699759562501,0xd7658940483734d3acab,0x9d32ebb2c4a0241e3a61,0x9056e9b95d96250120e,0x58940483974c3b2cb128,0x6ecb2c4a02419ba69d96,0x65e9a765d6250120add7,0x40483e94b2ae8b928090,0xa2e4a0241e6a619745c9,0x9765957250120db574cb,0x83d34c32cab9280907c6,0x4a0241d9a659655c9404,0x5d97250120ead32eb2ae],#[0x74cb2ecb92809078e986,0x24157a6e5765c940483a,0x7250120e3d32ec32e4a0,0xbf4cb9280904fa9b4e99,0x57aed9975c9404832f4c,0x120f0f30ebb2caa0241,0xcb2a80905a79b85d9655,0xedd865954048393ccbb0,0xe1f32ec32eca024169e,0x2c0907aa9845d1625812,0x7458960483c74c3ae8b1,0xd370ba2c4b0241d3a65d,0x9072e9976116258120b5,0x8960482d75da30eb12c0,0x8b22e4b02415baed1975,0x4e9975917258120f952e,0x482e74dbac8b92c0907,0x2e4b0241e6a611745c96,0x656117258120f8d2caba,0x3c74bb308b92c0907a69,0xb0241c7a65d845c96048,0x917258120dcd2cbd22e4,0x4db748b92c0906ce976e,0x4197a65fa45c96048277,0x458120abd768cbae4b02,0xae8b22c09078b9875d16,0x3e69d8759160483a5ccb,0x120f0f30eb2ae8b0241a,0xba2c0907479975957458,0xa1765d16048353cd42ca,0xe4f32eb2b08b0241a3e6,0xc0905a7bb461d6558120],#[0x75d960482b3dda32eb2a,0x2cab22e4b824163eed18,0x78e986591725c120f8d,0x970482cf4dc2c8b92e09,0xc22e4b8241e5a595845c,0x6965e51725c120e3d72c,0x4838f4c3728b92e09075,0xe4b824197ae9b945c970,0x6595725c120abd36dca2,0xcf5da30cb92e0907c699,0x824157a6d3965c970482,0x1645c120f872caba2c8b,0xd3acab22e09078b9865d,0x1a9e6a1655917048363c,0x5c120d1f350bb2c8b824,0xcaba2e09068f9a761964,0xa6cba65d170483c3cc32,0x20f0f2ecb2b08b824137,0xa2e090747976597945c1,0x965e517048393cc32cbc,0x1f30cbb728b824199e69,0x905a7bb4619655c120e,0x5d164482c7dda30cbb2e,0x70bb2e8b2241e0f61d65,0x707d9761d6559120b17b,0x6448293edcb0eb2ac890,0xb2caba24149fedd98595,0xdb85d9655d120e0fb30b,0x82c3fda30ebb2ca90587,0xcb2a4129fed1a85d9654,0xe9d865952094fb6fd230,0x3edb748c3aca904a7db4],#[0x2c167a6cb845c9704c25,0x625c160e9d728b92c4b8,0x3f28b12e0b056e9b2e51,0x33eed1a75897058327cd,0xc160e8f2cbca2e4b82c1,0x8b92e0b06c7965e91725,0x595a4e497058267cdb74,0xc9f2ecd2724b82c199e,0x2e4b0667965683945c96,0x65e517258327cbb341ca,0xfb50b2f28b92c1c1f61d,0xb0587fb461d655c960c4,0x11725c253eda744c3aca,0xcb2b29c12e1a1f69965e,0xde1945c9215c110e0fae,0x4436f8dd2e890ae0887,0x284b82217f8ec9944857,0x945c9425c110fbc362b9,0x3bd4ca324a12e0887da9,0xb8221b7c6c5a75097044,0x85725c110f3e308d0ae4,0x4ca304b92e0886df1a46,0x2177aec9945c970443cf,0x250910b7d764ca304b82,0x2e8b9284887da5746857,0xebed1a85c942443cd6d4,0x910cfe343d032ea12216,0xcba848863f9a8e819750,0xc9a865d424433f8d8f40,0xa6ff6ad432ea12214fbe,0xe48857f3b0651915c910,0x961172442cdfda330ba2],#[0xf6ad4b08b92212fbec9a,0x849fdb7ea5845c91096f,0x9404831fccc740ca2e48,0xc3a84a0241eea6dd8650,0xa9b361d4250120f75362,0x483dd4db30ea1280907b,0xc4a0241faa6d97458940,0x76596250120df5374ba2,0xdd5da30eb12809076e9b,0x241dba6d99758940483,0x57250120df5368d3ac4a,0xd2342b9280907da97468,0x1d7a65da15c9404837d4,0x50120fb52e8d1ae4a024,0x46b9280906fa9a468d72,0xa699745c940483af4cbb,0x20fe52cad22e4a0241f6,0x9280907da97669172501,0x9a45c940483dd4c3348b,0xf534cd22e4a0241dea65,0x907e69a65957250120d,0x5c940483b74d332cb928,0x2ed32e4a0241d7a6dd96,0x75e9b165d7250120ebd3,0x40483af4d9b2eb928090,0x32caa0241d7a6d9975c9,0xbb461d6550120f4f36ec,0x83d3cdb30eb2a80907b3,0xca0241e6eed1875d9404,0x69d8650120d77768d42e,0xddda342c3a80905bbbb4,0x2416faec9a361d40482d],#[0x8750120b77768d1b0ea0,0xb748c3a80906bb9a6e91,0x6eeed1a661d40482ddcd,0x8120f5d370ba2c4b0241,0xeb12c09076e9b95d1625,0xed18758960483d74da30,0xedd368cbac4b0241eba,0x2c0907ea9a4591725812,0x745c960482f74dd2c8b9,0xd36cba2e4b0241f3a699,0x9075e9b95d17258120f9,0xc960483d74d3308b92c0,0xcd22e4b0241f9a595a45,0xee9a66917258120f9d2e,0x483af4cbb48b92c0906,0x2c8b0241d7a6d1975c96,0xb85d16458120fd5364ba,0x3d5cda30eb22c0907ab9,0xb0241bba6c9a75916048,0x897458120fcd2cad12e8,0x4d3344ba2c0907ce9766,0x41d7a65da25d16048377,0x458120cfd352d12e8b02,0xacaba2c0907a79a85957,0x3e6a1765d160483b3cd4,0x120f1f30ed32e8b0241e,0xba2c0906af9a86997458,0xd1a85d160483cddda30e,0xd7d764d42e8b02416eee,0xc0907a79b461d6558120,0x759560483d3dda30eb2a,0x368c3aecb0241d9e6d19],#[0x78fbb461d7658120f1f,0xd60482df5d9348c3ac09,0xb9322b82415faec9a465,0xe9945c9915c120f3d308,0x482ef5da2e4c8ae09075,0xe4b824177aee5435c970,0x464d725c120f3d308c9a,0x6f5d2326b92e09075e99,0x824177aed1935c970483,0x1725c120fb5328b22e4b,0xdcac8b92e0907ce99659,0x1e7a659845c970482ef4,0x5c120fad2caca2e4b824,0x28b92e09079e98665172,0xa69b945c970483af4cb3,0x20f3d368c32e4b8241d7,0x1ae0907da9b25d1435c1,0x3a264d704826fcdbf52a,0xfd329d1326b8241b7a5d,0x904fe9b4e89935c120c,0x591704836ddd22e8c9ae,0x2cba2c8b8241f6a6c974,0x5fabb2651645c120f973,0x70483f1cb2b28b22e090,0xa2c8b8241f2e5d994591,0x996651645c120f5730cc,0x8373cd4acab22e09076b,0x8b8241b7a6c9a7591704,0x685745c1209fd764d4ac,0xf4d1b44ba2e0906de9a2,0x241f5a595a25d1704836,0x745c120f3d30cd12e8b8],#[0xb2caba2e0906de9a6689,0xf1e699655d170483e3cc,0xc120f37368c32e8b8241,0xac22e09078f9a6619745,0x597a265170483d3ccb2c,0xdbd2edd1328b8241bda,0x2e09067e996e89945c12,0x65651704827f4db744ca,0xf30cb2b28b8241f1e5d9,0x90767996595945c120f4,0x9570483c7cc32ecca2e0,0x8c32ecb8241e9e6d1865,0xfa9a26817450d20f1f36,0x44828fedbd52c3a86906,0x2e8b2241bea689a05d16,0x766817459120fc72cad0,0x3d5cc3340ba2c8907cb9,0xb2241e8f6a1655d16448,0x197459120f17b50bb2e8,0xedb30eba2c89078bdb76,0x41e8f6d18759564483c5,0x559120e4fb72c3acab22,0x32eb2ac8907679b065d6,0x9f6dd985956448393edc,0x120f17b68c3aecb2241c,0xc32c8906abfb46a17659,0xc1a461d64482d5fda34e,0xd57b4cd230eb22416eee,0xc89053fbb06a58759120,0x65d644831fdd8352c3a,0xf68d432eb22419fa689a,0x53fbb069d9859120a77],#[0x174483bb4b2b24c82e89,0xc9320ba241d7a5d99264,0x7976595905d120e7d30c,0x483d3cc32cac82e8907c,0x20ba241d9e6596564174,0x6619905d120f1f30cbb3,0x9dfda330c8ae89072f99,0xa241e1f6617659574482,0x9655d120f47b68c32cab,0xdcb0cb2ae890787db761,0x169f6e5865957448393e,0x5d120e4fd72c32caba24,0x2cb2ae8905a7fb961965,0xf6619659574483c3ec3b,0x20f27f68c3acaba241c9,0x2ae890787db661d655d1,0x19859574482d9fda330b,0x4fb6ccc2caba241cdeec,0x89078bdb4619765d120e,0x5d974482cdfda330bb2e,0x68d42ecba241c7eec198,0x69bda7691865d120d37f,0x744829fdd8352c32e890,0x4b0cba2412efed1a9619,0xdb6aa5865d120a7f3615,0x821fedd552c32e89052f,0xcba2412ef6d3a9619744,0x685875d12093fb6fd4b0,0xfdd8346c3ae89059bfb4,0x24166fed1a361d74482c,0x875d120b37b63d230eba,0xb748c3ae89069bda6e91],#[0x66fed1a661d74482cded,0xd120977b6dd2330ba241,0x2cc2e89053f9b6e81985,0xed5a1661744829fdd834,0xa7f760d1b30ba2414df,0x2ca9053fbb0699985d12,0x875d965483c3eda30ebb,0xfb68d42ecb2a41e1fed1,0x906a7fb46a17659520d4,0x196548353ed3b48c32ca,0xd230eb2a4169fed1a76,0xa7da66918759520b6f76,0x548353ed3748c3aca906,0x30eb2a4169f6dba461d6,0xb46998759520d4fb6dd2,0x2cfdd8348c3aec905a7f,0xc3a414feec1a46617648,0x819461d2097f369d0326,0x5d9328b92e0984bf9b6e,0xc127fed1a7a61724c2ef,0x25c160f9d328b92c4b82,0x324b12e0b07ce9746496,0xbaed19258970583b74ca,0x160f9d364ba2c4b82c17,0xb12e0b06cf9ba5d1625c,0xd1a75897058367cd3b28,0xbbd764ca2e4b82c1b3e6,0xe0b07c7965651725c160,0x45c970583a7cd3728b92,0x34cd22e4b82c1f1e595a,0x767965651925c160d9f,0x970583a7cbb328c92e0b],#[0xd2324b82c1b9e597a464,0xe9a26817458960d9f2ed,0x583a7ccbb40ba2c4b06e,0xeb12c19be6a5a05d162,0x45d1905c960b5df64d23,0xe3cb2ae8c82e4b06dbba,0x92c1d3e6597464172583,0x1905c960ecf2caca320b,0xb2f48c82e4b074f97665,0x1b3e5dba46417258373c,0x5c960cdf32dd2320b92c,0x30ba2e4b0787d9859574,0xf61d6565172582cdfda3,0x60e4fb30b2b28b92c1e1,0x2ae4b0787db461d655c9,0x9a461d72582d3fda330b,0x4fb48d130eb2ac167bec,0x4b85a7fb46898759560d,0x60d725c34f6c2744c1ae,0x63d1308b92e137b6d3a2,0x6d6d65e89845c9709bdb,0x725c34f6c3744c22e4b8,0x2b08b92e137b6dba2611,0xd96597845c970f0fb0cb,0xc3c3ebb2cac2304b8787,0x8c12e1d1f5d965e51825,0x5979460970e4fb0cb2f2,0x3ed32caca704b8667da6,0x221cfbec9a865d424439,0x7250120e6ff6ad432ea1,0xd30cba2e09077e9ba659,0xeaf6e9865d164483cfcd],#[0x9120e7f760d4b0eb2241,0xecc2c89073bfb46a1975,0x6d186641744839fdd834,0xf3f36ec3320ba241eee,0x2e8907a7db9619655d12,0xa961974483d5ecb348c3,0x7f68d4b0cba241cfeec1,0x9073fbb0685985d120d7,0x61744839bfdab42cc2e8,0x8d3b0cb2a41cfeec1a66,0xa7db46998759520f4fb6,0x64839fdd8348cc2ec907,0x322c3a416feec1a465d8,0xb56919161d20b7f760d2,0x35fdd8748c9b0e905b7f,0xb92c16feec1a46598748,0x91985c960f4fb68cc2ca,0xeda344c3acab05befb26,0x16feec1a464987583d3,0xcc0330024c018000cc00,0x98069c05e8054c049803,0x940ae009fc0918084c07,0x480eac0de00ce40be80b,0x74129011ac10e010140f,0x48174c1620153c145813,0x5c1b781aac19e0194418,0x401f741e781dc41cf81c,0x3c2388228c21c020f420,0x38273c2640255c250824,0x342b802a8429d028bc28,0xd02f342e982de42d182c,0xc327031bc3138306c2f],#[0xf03624355834bc33d833,0x7439a8390c384037bc36,0xf83d2c3c483bc43b283a,0x440683fcc3f303eac3d,0x8843bc4308425441d041,0xf44740468c45d8452444,0x384b3c4a58498c48a847,0x44f684eb44e004d1c4c,0xa052ec5250516c50e850,0x6c56e856045538545453,0xd85a5459885904582057,0x5c5d905cdc5c285b745a,0xb060fc60605fc45f405e,0x34646863b46300624c61,0x10677466f0665465d065,0xac6b286a7469c068f468,0x386f546e706d746ca86b,0x4472d8720c717070bc70,0x3875847500746473f873,0x4478a8780c778876ec76,0x707cbc7bd87af479f879,0xcc80e880347f387e547d,0x5885748490839482b081,0x3c89b889048820873c86,0x388d6c8cb88c1c8b388a,0x4c919890b48fe88f048e,0x48959494e093e4933092,0x9c98e898349798971496,0x809c9c9ba09aec9a5099,0xdca128a02c9f489e4c9d,0x20a53ca488a3bca2c0a1,0x7ca998a8b4a7d0a6eca6],#[0xd8adacacc8abfcab18aa,0xecb250b16cb0d0afbcae,0x28b5a4b508b46cb3a0b2,0x7cb8e0b85cb778b6acb6,0x48bc7cbbc8bae4ba18b9,0x8cc090bfc4bec8bde4bd,0x70c4a4c3c0c2dcc240c1,0x6cc888c7bcc6f0c654c5,0x78cbf4cb58cad4ca20c9,0x14cf30ce4ccd98ccfccc,0x40d3a4d2c0d1dcd110d0,0x6cd7d0d6ecd638d53cd4,0x20db84daa0d9bcd908d8,0x8cdea8de0cdd58dcbcdc,0xa0e2bce208e124e070df,0x84e688e5bce520e484e3,0xe0eafcea18e91ce868e7,0x94ef10ee2ced60ec7ceb,0xd0f204f180f0ccf018ef,0x6cf5e8f54cf420f36cf2,0x80f99cf8d0f7a4f708f6,0x4cfdc8fd2cfc30fb4cfa,0x3101ad00b0fffcff18fe,0x9d04b90405036902cd02,0xa9080d072906a5062105,0x150b910add09c9091508,0x810ee50e490d7d0cc90c,0x35128111cd10e9101d0f,0xe115751509148513e913,0x7517c1173d16d1164d15,0x291bbd1b091a3d197118,0xd1f291ea51dd91cf51c],#[0x61229521f9217520a920,0x8d26c125c524e123fd23,0xb92b352a51296d287127,0xe52f012e1d2d512c852b,0x41335d3231316530b12f,0x9d37a136a53609355534,0x113c2d3b613a95399938,0x6d40893f8d3ea93e0d3d,0x8144e5443142ed423941,0x54851479d4701463545,0x194c654bb14a9d49e949,0xdd4f414eed4e814dfd4d,0x4152055199514550914f,0x8d543953cd52e9529552,0x7955f555b9554d54f954,0xc5584157bd575156e556,0xc95a455a095985591958,0x381760c1c87c460b115a,0x2151f51d82839c79c77c,0xc81c79c710a47f0806b5,0xa1c4e11e11643fc20171,0x2685914722ba10a2fc13,0x16684687704e8a8ca4c8,0x4f50fe11c13e1c45438,0x784704f870e05425a858,0x1e11e1c30118113c2015,0x860a1ce8fd09d05b0fe0,0x2d720560c60b1c79c71c,0x482971f71d830f0ff118,0xb1c79c75c3f048e84684,0x1e08dc1371c401760c60,0x235c71204604583182d7],#[0xb01ae0c01760b5c7f048,0x34f0f83171fc1371c481,0xc3f048170e82d02894b2,0xf1c08c180c00b5c7dc73,0x50b3c3fc4704c4d95c12,0xdc12501e20a4c7cc748d,0x31f31d137828f0ff1142,0x28d2c85c3e0a1006c235,0xeb1dc1232c7ac750b7c4,0xa5c3f0490a3542d828b1,0x1c42c7ac7017a8d7c460,0x6029a3542db1e08dc13b,0xd60a6c7d0b704ec71004,0xff11321c2c481b091a8,0x8d1284682931f31d234f,0x7cc760a3c3fc430b4c84,0x29f10f0f321c2c4b114c,0x4f0b1206c23531f31d8,0x18110cea0a48d4c7cc77,0x1d828c2df11c13234481,0xc460a7049807e44531f3,0xa817cc7cc748d5c3f427,0xff11c13136501f81b81,0x5032828a4731f31d234f,0x7cc760a3c3fc450b7049,0xfc1205e308d40ca91cc,0xb704ec711235829f10f,0xf20409191128d60a6c7d,0x4b046f1ef1df1142d828,0x52a1750b3c7f04bc7130,0xc12246f1c3012a0a4c3c,0x7c41c870b1002d828f1f],#[0xfc2c3a119c79c70cee0a,0x39471e71c05df10721b0,0x9c7117e0a7c47421c86c,0xdf11829720469190c9c7,0x4f0b0e84a84571f71cc2,0x4e41c79c70177c40cef0,0xe43205f24671e71dc128,0xae0a5c7f048235c71045,0x1ec2dc1371c501b91781,0xe84543302894ab0f2357,0x1b0b6c3dc7e0a704dc70,0x29d0971e247c1371c401,0xc4f04bc70230605e8458,0x31f31c33ac29f11321c2,0xf817c44c870b14446445,0x4501b01a8174c7cc75c3,0x31f31cf0ff10c2d32123,0x3c3f0b0170ad4ac45033,0xcc2df11c132345fc44c8,0x84503342894ab0f31f31,0x60ce47e475c3f048138e,0x583391f91d709c12560d,0x27048e04604470e82983,0x1c4e0d01ae47e4760a5c,0xf83583370e04f91fc139,0xee47e47704c8c1008007,0x1cf09c123a0cc0a60d24,0x481a8d70f83583391f9,0x51dc123647e477c428c7,0x704d4d8c53743382951f,0xd829c12401ad47d4760a,0x70a06e13b43253751f51],#[0x98283f0cf47813f04f4,0x138d246c32d20d1ed1d7,0x93a46c3b47b4730cb484,0x4f028c3342cd1ed1dc12,0xa24ef47f04c8c747120,0xd21709246321130cd0b4,0x14d891f0491828c33f10,0x9c124347b4730ce0a7c4,0x46c33829b0ed1ed1d70,0x91dc2747e0a704f4710,0xfd1ca31c1206a2817a11,0xcb0a647e47704c4d91d1,0x1dc13137c28301e11160,0x47e4724df049006b91f9,0x521b08391104ee0cd0a6,0x70a0c845432c2951f51d,0x84e281ad48547d476c2,0x7f04d471343351f51d52,0x20013c4ed0cec278154,0xd82853b52151f51da304,0xce47e476483c20e43382,0x20f09c2806a2dc3f8160,0xa647e47704a4d8df119,0x71e71c721828736360cd,0x8171c79c77049cd8d80e,0xe04f90f71fc1371c4643,0x7bc7413bc80a05c26045,0x2cf1e845c12f1c3c03bc,0x117c448c3c80e04f0294,0xf1fc12f1c460a3c7bc74,0xbc70c05cc32829045230,0x2f1c3c1148c3c7a11f04],#[0xa8e044c33828f1f231c1,0xfc222360a1c79c71c801,0x6044f0971f71dc1205c3,0xd60a5c7b0b704dc70e04,0x36b1eb1cb21c28381148,0xa2c7ac77049304b4443,0xc28420cd438cda17452b,0x6ec4413a33732131f31d,0xc24c7cc84c7743822920,0x31d13bc1250178177816,0x5e05c04e261e05b0931f,0x4e8cdcc7cc750a704920,0x71c635b084c8d40ca528,0xf94a43384445c71e720,0x12d0cb0a5c7a8c704dc7,0x82871e71c53a721a3038,0xa110cdfc41c870a0d82d,0xde05f10721b09844494e,0x270a01a8a05c43271e71,0x37f10c29c124fc41c86c,0x170c05c43271e71d0443,0x5c3f43cc7cc84c73c20,0xe04403b31ef0931dc12,0x91a91547d4744dd4838a,0x45de0551f51d137e124a,0x64824dd8a1007806c06a,0x8a499199104ee47e47,0xe05e0191f91d70f921f1,0xe48647e473c38228bd09,0xbd09e05e0131f31d3203,0x87817804c7cc76469313,0x1d921628281b01a8974c],#[0x817807c43469093791f9,0x51a05c2e48647e476c3f,0x7c45c38170d92191f91d,0xed1dc137083e47e47648,0x2704f878ed21b0fe04d1,0x1dc123a8fe1110f7845c,0x490035832444331a1fa,0x128d60cf43e87dc26877,0x4445709a1fa1dc12481,0xb70481b0a06083b833b,0xe1cc32e213303687e873,0x387b8750b4518d044e1e,0x4e1ee1dc1342c3b0cb88,0x7b876c14110c046c32a3,0x1ee1dc12a343b0cb8838,0x873886c20e044c3342ce,0x612a36398cf43f41387b,0xa5190046633428e1ee1d,0x1790ed88587d876c2584,0x61f61d621f11b0806c30,0x6a3688687e8701ab4c0b,0x4c0bc1fc1dc21f115160,0x721a2c31c81c79c701ae,0x30b48a9284453471e71c,0x1181f911609e84704e87,0x708a2ba10063a1dc1244,0x28af04d0b6870e067445,0x7c12e1c08c3e09f43e84,0x4f870230b130c26e1006,0xfc12331e1c50c178470,0x82d029c2607fe10079d,0x6b09b8401a019b877049],#[0x2d611c1361d146502001,0x199245864d844427038c,0x2a4c3c2584509d877048,0x10845c12c2de1c482025,0x870230b02902694b22be,0xc1342de1c3f09f84704f,0x7848198c829d0ff06855,0xde131304589d8424c587,0x488078066064855e11e1,0x10e1d6123c1578724c78,0x84f870886886685a626e,0xb0ee11612e1c30218235,0x251a4c7877848bd09d05,0x7087931e10e13e1c3860,0xe5c2684384e870f94b94,0x64b09e1de12360aa89e0,0xc23417877848a94be110,0xe11b09e01e1c08437846,0x343ec27417877848dd05,0x8464455b09613e1c3f84,0x7dc7704e0b0171408e07,0x1c4e0c02301b01abc3dc,0x6064078054f11c1382cf,0x4704e0b3c79d09383006,0x1c08c3e0c02201f01ebc,0x49205c06c06af1fc12f,0xdd0b28d2c7dc3ac760a7,0x1f828061b1dc12481b84,0xa0179408006e06d42db,0xf81b81acc7cc73c3f04e,0x1cc2dc13a340783c8d01,0xc7ac7704a8d12029b1fb],#[0xc12481be0a01f81a817a,0x2808c06c061b1ec2db1d,0xa5c4704b0b5c71206f8,0x71dc125212c8a819891e,0x2b828080066247710c2d,0xc448af04b0b5c7128312,0xc2d71e4a12a1160a091d,0x4b23e07c343829711c12,0x1f5c430b4d0dc7f04928,0xc12c2d71e4a12a0c60a0,0x1284a84434323f829711,0x1b091e0a3c7f04d0b3c7,0xf1ef1cf2108c3c12a8d0,0xf04bc70230b04703142c,0xdb0f42dc12c325011bc7,0x19285c04a829030f1ef1,0x60a30cc0c3c7bc7704c9,0xcf1fc12f1c08c311790b,0x79c71c870b09b0ea3406,0x1d04fc12a46408d60a1c,0x49179045e43223471e7,0x481b81adc7dc7023413f,0x2824771f71cc2dc13234,0xc4704e0a3c71084a8458,0x828f1e481f81a1160193,0x44083d08088f10343c13,0x1b817bc7f04bc70230f0,0x31f31d321c2c05c481a8,0x6c811e0e09206c06af0f,0x1c2c511110a6c77c1b0b,0x6a05c093428b1eb1cb2,0xb0b704ec701e0e06d70e],#[0xdb1dc12d08381110a6c7,0x4b4260c91b1e08d06b05,0x1c2ec7ec702341adc3f0,0x481e8d065055c12d097,0xc1371e3a0a01e7425c7f,0x14d8e07b844d09e04089,0x83a1aa173c7bc770481e,0xf1f50886a85dc12f1c07,0xdc7c1ac17704b425c70c,0xf83591f91d833c1208c3,0x760d01adc2704e0a1404,0x4f91c481f81b817e47e4,0x7f83583207991fc120,0xce47e47704bc201e1008,0x1dc1382806a500a60d60,0x383407e06e05ef0991f9,0xa14d88c547d4750cf049,0x1f51c06dc1250206c3e0,0xe08006f82943206142d5,0xa30cb47b475c270481b0,0x32536d1ed1dc138284e0,0x4e0a7471406f24613ac,0xf81b817c91dc201af47f,0x34c32d1ed1dc1304e401,0x4734830cc918e03bb0e8,0xc12246c324e0a48c347b,0x9083a081829230d1ed1d,0xa48c347b4770481b30c,0x247d1fc13d1d23048206,0xe0a01a9284483b828c32,0x2301b917bc2747f47704,0x91f91cc29137c1383248],#[0x13f04c4d9208170e231,0xc302001f81e60ce47e47,0x49204e93791f91dc1208,0x81b81b018647e4730a70,0xd428d20c3334a402060c,0xc704b0c93247230d1ed1,0x2024e891d0a347b4748,0xed1c93b428c33c1382c6,0xc9208006f246937230d1,0x91d0a747f4748c704b0,0xfb0fd1dc132305a1aa11,0x7e06e86b24685f429d1,0xa13d0cd47d475482230c,0xb51f51c05f521c28b4a4,0x7d477048230db0809406,0x1f51dc1208c3c4ed0cd4,0x477048231003613b4335,0x8c344ec4dd0ce0b547d,0x1e0c045c33d1fc13d1c,0xc08c2f0c8d2f47f04f47,0x76481230a04fd1fc13d1,0x1d920f084784113e47e4,0x1af0a1244442983391f9,0x501b817bc2648647e470,0xcf0991fc1391c08c282,0xe3011647e47704a4d81e,0xc90829d1e079c13d1c07,0x823417f475c2704b8160,0x5b10631c13b1d1384f47,0xa6c70190e42c42982704,0x29b1c43c201fec4704d0,0xc058447045b10f09c134],#[0x4e815c4704dc79d001d0,0x29149710a31c1371f142,0x4e0a5c7c509543c82c8,0x421281150f20b3c25c47,0x46f09711829c1371f142,0x125c4704dc7a8c140728,0x8c3c1140f60a1c910f4,0xc02c04a73771fc1371c,0xa49cd9c79c770481a823,0x45e73771f71dc1382806,0xbc748c704a4e9207e06e,0x108c430cc0b40a2113c7,0x4b04542d828f1ef1cf2,0xd0b3c7bc7704c1128d13,0xdc1206a08c320ca0a452,0x7c8c3c770491204f1ef1,0xe05c460a018411211bc,0x226045f71f71c04fc139,0x2012ec430a450f04ec79,0x9c13b1fc283c1100c4c,0xc7f0481e8fb10444051b,0xc1207a2850ec450a18c6,0x704ec781d8cc2c631b1f,0xbc13b1e08c281cd0a3c2,0x2ec7f04ec70230bb1007,0x36b1eb1dc1206a08c301,0xb6c7b0a704ec701f8e3,0xb1eb1cb21445c284e0c8,0x11170a1307f04b02c336,0x12a4e81f8cdac7f04ac7,0xd0e336b1eb1dc12a3450,0xf0a01a9085c04a83302d],#[0x84c0b01fac7ac70cdf04,0x5f32131f31d31a06bc2,0x6c7b0a6c77049209406e,0xcc2830184cd82301b81b,0x770495b1f05fb09c13b1,0x4cb82001a052dc430a5c,0x8f10942f1fc125211c4e,0x30f046b41030083429b0,0xc12c11d003c7bc73c842,0x8c33046f1ef1dc1314a4,0x7f04bc70230c45d84442,0x1c72006a88c324e81bbc,0xc71c870a05b8f82871e7,0x90fc1245c484ee111c79,0x9206094a05e04f71f71d,0xc84ed0a1c79c7704a52,0x71e71c72184e31176111,0xbc750a3c841f8c43253a,0xf429c12f1c07e340b7c1,0x7bc770498d01f8f02cf1,0x29c12f1c07e330cd0a3c,0xc71c821170a12f1e85f4,0x8444a1fa1294ee0b1c79,0x4a43271f82c71c720635,0xc79c71c801af0a0e45d9,0x71dc130446344a1fe0b1,0x8228e43242914b82c71e,0xc48178174c7cc74c8743,0x26131f31cf09c1313a05,0x98a747d84e509205e04e,0x3d1e320c40b744643812,0xd8230ca4610ea45d09e1],#[0x4b6284181747f47584e4,0x507f02cd1e936d1cd211,0xb347b47584852a4dd8a1,0x3561314a481fa4e81140,0xe45c93643302cd1ed1cc,0x21fc4dd47d475482138,0x78e2951f51de13136522,0x849171208007f13a04e0,0xe25281b01ad47d476427,0x6c06ad1ed1de12936481,0x4de481230c05d6280780,0x8b92191a4913e47e472,0x9009364764562991f91c,0x1a817e47e4764838a05b,0x8b92191f91ce2848250,0xe470228a09609513bd08,0xf91de1208c2bc3e48647,0xac176473427848e93791,0x1d70ed09e123c1b647c1,0x84d4d8230b06d91f06b9,0xd1ed1de1208c4747f473,0x384f470c86c86a85c536,0xfd1ce123a9128a747f42,0xa58499d09e0408c08bd1,0x82301bf47ec3f4274718,0x5d1de12321b41aa18417,0x3b848228a94a937d1fe0,0x1d228f2108c3747f475c,0xc7e84bc70230dd08f1ef,0xd0fa1382ca32634ec813,0x4543022804af1ef1c635,0xc79c71c8252e8a114478],#[0x82c63594a4a1fa1114e9,0x9025c23384471e71c721,0x1160b1c79c71c868a05b,0x71e71c635a1314a4a1fe,0xe84c139425c53a233044,0x4d88c8129c79c718d14e,0x92fb11629e13b1c36111,0x44ecc7cc74c81230a14a,0xed4b31f31d321d0e08a4,0x701acc87420971206005,0x1c08a3824b5281b4c7cc,0x5294092d4bd0f32131f3,0x27817804c7cc7022cc83,0x1f31c25cd4a282582574,0xc7cc74c80973528d3213,0x3731f31d32048c37424,0xc4dcc7cc74c81230c13a,0x4409b1fb1db2048c3c4e,0x7ac758a2c87421244644,0x20478282481b09701aac,0xc71236c80bb1e54bb1db,0xb1eb1cb2048c2913fc1e,0xcc7cc7643f848971208a,0x3b1c0783013a52818017,0x4ec70230814bb1e937e1,0x1f06bb1c08de123ec7b8,0x43ec7784c1397e0506db,0x321b21ac184178176c7b,0x29b1fd0fd09b1ce12382,0xc7f813426c77848aa32a,0xb1fb1dd0fd08a32e123e,0xac7ac7743f427848ea29],#[0x808bb1fb1de12428d28c,0x7743f848c093a35a33a2,0x1dd09e1233427816c7ec,0x42784dc70db1ed0fe05b,0x71ee1207c45c4419c193,0xf8492844143710079d09,0x1ee11e115c47813425c7,0xf10865e12f1c078381f0,0xbc778494d81e0f508866,0xfe12f1c0783a1b21abc7,0x2784dc70d50886c86af1,0x12f1c0782c1b5c7c1ab4,0xc7d84bc702308f1f509e,0x74230884ee1208d71c23,0x10e1208d71e2c21dc45c,0xc2dc7b84dc70230884f7,0xd89e0ef0991f91d92028,0x85091891647e4764824,0x3921e0408b91f91dc12f,0x7e473468249106d06a09,0xe08a401b01a81764864,0xe09286c86b92191f91cf,0xb01ae48647e473468248,0xa311f07d1dd2028c201,0x24a1b21aa17347b47348,0x536d1ed20d1d51a27848,0x34754689e1086c86a85c,0x2782a1b21aa17347b48,0x4d480a313708d1ed1cd2,0x1b01a8173c2547d4702,0x845d1e078e13d1c0803,0x321aa17747f475c23849],#[0x28074f09b1f612282482,0x1150a3c7d84bc70200d4,0x305e11c13709e1f84245,0x543f87814f848d04a846,0xfa1dc124452344f843c2,0x21111304607f832c2da1,0x60cc0a48d687f04e873c,0x5a1fa1cc2dc13234501e,0x701e1102807e07983244,0x80a48d60ce87f04bc268,0x6a35a1fa1c331c138324,0x7e8701bf049408144414,0x82001851160c81b60a68,0x2445a1fa1dc12a3542c4,0x7e8701b7049284683b83,0x8c2e0c82001b8983c268,0x116c111c33e1fc13e1c0,0x441fb0cb87b8750b3884,0x4483ac32e1ee1d331c12,0x87b8838730cccc100610,0xc1206cc324e11452c51b,0x1314b844081330e1ee1d,0x1130cb87b8750b38860a,0xc1342ce1d828441fc1e4,0x5c241e0ec3207e078e1f,0xc078440a30cb87b88387,0x237028c32e1fc13708e1,0xf07f0750cd84b0d48b18,0x4482001fa51c9124c6c3,0x24543322dc1fc1d612c3,0xf0701bd84c8b1686c83a,0x2021b49121850cf41707],#[0x5fc1fc1d708d05e1238,0x68cf87e84f870230d06f,0x2e1ee1ce217091465011,0x201b1507954b045828a3,0xc1160a28cb87b87684dc,0xee1ce20a33530501e552,0xc9507954b845829146e1,0x82001e387b87684d4c28,0xce217090784152a1130e,0x201e11045828e1ea32e1,0x81130ea8cb87b87684dc,0x4a32e1ee1d709a120784,0x7584ec201b14c3a236c3,0x24e5281a917588587d8,0x294b06be1eb09e1de123,0x2a51d88587d8718ce4c1,0x1d620633930511a90ea5,0x209246a45d94a06d61f6,0x7bc2688687e8774101a9,0x1da20f08092402501b89,0x877848e06bd0405da1fa,0x704682341bf87dc23417,0x5dc2006bc1fc1dc12f09,0x248e09409286f06c85f0,0x301b017708707f073468,0x8ec4bb10531b1fe1207a,0x208416c43c26c7f8481d,0xf11b09504062f1de1240,0x3c7bc73c84230c069446,0xef1de1253407e3c12c01,0x7f84bc701f8f446c3af1,0x21d0406a4d11a1bd413c],#[0xe87f84bc47a2c71e71c7,0x810e9c79c71c864c6110,0x4471e71da2c721c28581,0x1e0e87e878a4ac4663a8,0x3a1198e9c79c71c86c22,0x3a63271e71c720336878,0xc79c714d1c86c2711126,0xd0472006a2f8011b1171,0x824023021f848871e71d,0x23022c138d08660b6261,0x90e09208c382481bd0c8,0x250228e094061433429,0xc08a182581e50d50ce42,0x10258250230228809208,0x8c1817813a528608c08a,0x43f423528229304e06a0,0x50e2025825024c8d48cf,0x248230228606005f04f,0x218230609609408c08a2,0x30404c70b70308623848,0x9306d06a74a08a282282,0xb7082024c1b41a822880,0x321a824a170809208c08,0x8a86485404db0208e282,0x57081e19e196150136c0,0x2824a1aa170230808807,0x248409609306bd0408a,0x809506d06a09208a2a17,0x23217024a1a8]]
set_option maxRecDepth 16000 in
def g255H9 := limbs80 #[#[0x20400400600048000,0x82006084502212891280,0x64b6c3090080010000a4,0x25000808b400c01008,0x46100002d2b80,0x1e620000000000000000,0x0,0x0,0x0,0x0,0xcad8000000060e000000,0x0,0x0,0x130dc250000109500,0x7c0f000000000000a018,0x10d8c800000000000b08,0x307800000002a0712,0x20000000000000000000,0x908200035491062f28,0x0,0xa8c,0x0,0x8c48000d68a000000000,0xe00030cb800000000001,0x10aa80003a3be8f,0x323f00,0x0,0x883d91f000,0x0,0x60001433000000000000,0x401866a,0x293b0000000000000],#[0x2412800000000000,0x0,0xe64ba15800000,0x3c9000000000000160a4,0x540000ec67cc38000d04,0x2b,0xc87c000490d0000214c,0x540000000000,0xd2fb058104c000000000,0x0,0x3a8e000,0xc4200000001ec9000000,0x2d9ca25800000003,0x1c8e40000000000,0x510146a1046745400,0xe6080000,0x0,0x0,0xa0000000000000000000,0x39100000c0b,0xf488000000000,0x535d00000000,0x0,0x4080000001a261c1b80,0x497d16500003,0x6f0001444c0000000000,0x5090000089b68,0x60c8,0x7446000,0x1200000042f80,0x342a000000000000,0x0],#[0x1c5300,0x0,0x4b07000,0x8820a81400000,0x60000000400c0001e424,0x8344b6270c,0xc4900000000000000000,0x146029f82780000,0xc8740000000000,0x82b80000000000000000,0x9e1cf045dc6a14980002,0xea092000284eaa6ad05,0x8550000e06800000001a,0x855f122909eb5520003,0x0,0x786c0000000000000,0xd4a58a4c214b15c,0x2237000,0x232a0001605c00000,0x0,0x2011000,0x408682b000065a000000,0x3,0x3118f000000005807000,0x58,0xae44c20000,0x0,0x89d000036396891c0500,0x1,0x960,0x30d4000000000,0x69c0007a7a00000000],#[0x312c0000000124a000,0x4876027ee05061a80,0x503f00000000,0x25306000018260000000,0xda4502700000003c00e2,0xe0080001,0xab000168d00000000000,0x70,0x0,0x6612000080d0000000,0xd490000000000,0x8438,0x66cd01fca078000000,0x0,0xfa09c62c,0x8e000000000003982000,0xe20aa50e81130,0xa00000007b2214a60000,0x3e0000000000000006ac,0xa208000000000028827a,0xe938000000000008d3a,0x48b25230000000,0x49980000000000000000,0x18518000000000000000,0x54c,0x0,0x149bc000000000000000,0xc27c5850321000,0x0,0x1e850,0x2b0f621d2c4e0000000,0x7b],#[0x20000000122b00008254,0x5c000022a4511eaa5749,0xc487808c8f6000000068,0x16d70121000000000000,0xb90922500000000000,0x6408aa1344600,0x0,0x2a4352a8000000,0x0,0x0,0x0,0x123d00,0x0,0xa0c264900000000000,0x108c000000,0xe8f4000000000000000,0x126100000000000,0x5140000000000,0xe0000000000012b20000,0xa1e80000000c01,0xd4ee9550001e1f000000,0x30ce0001,0x0,0x3a1bf53dd157c2580,0x6ea8504d80000000c0b4,0x1d1d0000371,0x120a800000,0x20320000,0x449e00000000000000,0x0,0x80000000000000000000,0xe47],#[0x0,0x0,0x29000000000000000000,0x29,0x4d3c0002167000020ec,0x0,0x0,0xc0000000408600000000,0xc54,0x0,0xe4200000622100014178,0x1356311,0x823905984da0002c3000,0x3c111022800000004015,0x8f000000000000000b12,0xf11400000000a,0x0,0x60740005840000,0x3d1300,0xc000000000000001a888,0x534800025af38a210f,0x642da64a0e20003c0100,0x750a0003,0x8ac000000000000000,0xe41800000,0xc0000000403900000000,0xc13a5208000a43,0x4a48000000180b94c180,0x40000000000000000002,0x6067e16e84bc0350a0,0x8024000000000,0x0],#[0x2846d04a000,0xeaf80000000000000000,0xb70fc000485100016409,0x7000000000000000b45,0x851a00000006a,0x611000000000,0x740c202c0000000000,0x1e5300,0x8000000f000000000000,0x853,0x28850001a03400000,0x124a00000000a024,0xd14600030140000000,0x4d00000001815745080,0xa653c083,0x0,0xe020000415a000000000,0x600c000000000000000,0x7144000,0x7404000000000,0xb184000000000000000,0x604621180005016000,0x0,0xe8da093800000000000,0x0,0x609b407000000,0x0,0x0,0x21210000865800000,0xe4500000,0x1301000,0x21080000000000000],#[0xfc1b4000000000008568,0x323400000000000410,0xa9b0000613c00000,0x191dc000000000000000,0x0,0xe52d2790000000000000,0x418000000028b9,0x5050000000,0x3d9180,0x9843000000000000e1a4,0x10c7c000000010c,0x1404c00000,0x553c000408900000000,0x101f4000420b000,0x4935114a000000000,0x702f00000000,0xda38000000,0x0,0x2b1a00000000,0x0,0x5a090000000000000,0x2585800000000000,0xb048000000070ac000,0xa82343700,0x10a44,0x79000000000000000000,0x48f00000000000000040,0x3c35800050b42994,0x10c140000000000,0xd3c6a5600000003c2100,0x660c0003,0x0],#[0xd838a26a380f800000,0x1c24d,0xf2f9ac9c0000000000,0x0,0x143b800000000000,0x38538000000,0x0,0x0,0x29a90000311,0x91f80000000000000000,0xa8f20002,0x0,0x0,0x12864,0x0,0xd3e63260001e19400000,0x620d00018149,0x28385050000,0x81d7a89e2160003c3900,0xa0000108800000000001,0x2c3000044a150e,0x10e00000001acd000000,0x1,0x953400000000000000,0x0,0x0,0xe8300001a2f000,0x195400,0xc80,0x203d000,0x0,0x1201000000000000],#[0x218f0000f00,0xe24a21a0001e509cc080,0x380f900e00000001,0x3836000,0x826584100]]
set_option maxRecDepth 16000 in
def g255D10 := limbs80 #[#[0x725c110f785c9215c110,0xfca5954250120e7a609,0xd4250120eea619425012,0x20faa5916250120eea61,0x596250120f9a59562501,0x120f6a5d17250120dba6,0x6196550120d7a65d7250,0x8120eba6116258120e9e,0xa65d6258120eba61d625,0x58120f9a5957258120db,0x7a65d7258120f3a5d972,0x558120e9e5958458120d,0xd9e65d6558120e9e61d6,0x725c120e3e61d7658120,0xd7ae51725c120e7a611,0x9725c120f5a595725c12,0x20d7ae59725c120e7a61,0x19655c120f1e5d9655c1,0x120e3e619765c120e9e6,0x61d7659520c9f6616559,0x9520a9f6a17659520e1f,0xfe9d8659520a9fe91865,0x5c160f3a5c9625c160a9,0x1e595725c160b3e69d62,0x25c160d9e597925c160f,0xe1f61d655c960d3e5db9,0x65e0970a9fe898759560,0xc9f65965e0970e1f5d9,0x1215c110f7c5d1215c11,0x10bfc691215c110efc61,0x9d425c110f7a5c9425c1,0x110afe6a1425c110b7e6],#[0x611725c110f7c685725c,0xc110b7ee91725c110e7e,0xce85925c110afee91825,0x48510afd6a17448510bf,0xfde9d8448510cfd65d84,0x25c510afde918748510a,0xafde91825c510afd6a14,0x8750910f6b5d17250910,0x9fee8197509108ff6a5,0xd98509108ffea1975091,0x109fd687945c9108ffe9,0x85985c9108ff6a3945c9,0x9108ffe91985c910cfde,0xe8597609108ff69f9460,0x1d108ff6939760910afd,0xf6939261d10afde85926,0x50120fea50971501208f,0xea5d94250120fea5cd42,0x250120fea5d16250120f,0xefa61d6250120fba5d96,0x6250120dfa65d6250120,0xfea6917250120bfa69d,0x97250120fda595725012,0x20efa6197250120f7a5d,0x997250120dfa65972501,0x120f9e5d96550120bfae,0x6197650120ede61d6550,0x120e7e61d7650120ebe,0xe65d8650120afe6a1765,0x50120afee9d8650120cf,0xfee998750120eeee9187,0x258120fba5d16258120a],#[0xf7a5d17258120fba5917,0x7258120efa6117258120,0xfba6997258120bfae91,0xd6458120fae5d1645812,0x20dbe65d6458120ebe61,0x957458120bbe69d64581,0x120f3e5d97458120f9e5,0x65d7458120e7e61d7458,0x8120afe6a17458120d7e,0xe65d8458120ebe5d9845,0x58120afee918758120cf,0xfee919758120ebee9987,0x25c120f7a5c9915c1209,0xf7a64d725c120f7a50d7,0x725c120f7a591725c120,0xf7a659725c120f7a651,0x9935c120f6e5d1435c12,0x20f6e5d1645c120bfae8,0xd9645c120f9e595645c1,0x120ebe619645c120f3e5,0x6a1645c120b7e69d645c,0xc120f7a689745c120afe,0xe619745c120f5e595745,0x5c120d7ee59745c120e7,0xde595845c120b7ee9974,0x45c120e7e5d9845c120e,0xbfae89945c120cfee598,0x945c120dde597945c120,0xcfe61b945c120d7e5db,0x9655c1209fe69b945c12,0x20afee91865c120f9e65,0x1d7450d209fe693965c1],#[0xd208ffea19750d20e6f6,0x59574591208ff6a3945c,0x9120f2f5d97459120f8f,0xf61d7459120eaf619745,0x59120e9f61d6559120e6,0x3f61d7659120d9f65d65,0x659120cbf6617659120e,0xcbf65d8659120abf6a17,0x8759120abfe9d8659120,0x8ff6a58759120c7f65d,0xd98591208ffea5875912,0x20dfa649905d1208ffe9,0xa3915d1209fe683915d1,0x1209fe683935d1208ff6,0x5d9655d1208ff6a3935d,0xd120e9f619655d120f1f,0xf661655d120e5f61d655,0x5d120e3f619765d120cd,0x7f6a1765d120c7f66176,0x65d1209fe683965d120a,0x8ff6a3965d120c7f61f9,0x875d120e6fe91875d120,0xaefe91985d120a7fe99,0x5985d120cfee81985d12,0x208ffe99985d1208ffe8,0x918659520e9f5d965611,0x520e9f69d8659520e9f6,0x6998759520adfe918759,0xd920abfe91865d920e9f,0xfe99875d920a7fe91875,0x5d9208ffe91985d920e3,0xff69f9461920cbfe9998],#[0x761920abfe9997619208,0x8ff6939161d208ff6939,0x9361d20afee819361d20,0xafee819461d20a7fe9d,0xb9461d208ff6879461d2,0x308ff6939661d208ff69,0x91725c130e7ee11725c1,0x930afe693825c130b7ee,0x6a7845c930afb68b845c,0x930a7f69e985c9308ff,0x7e9173e0930cf765173e,0xe09308ffe9d94e0930af,0xf7693925cd308ffe9197,0x25c1608ff6939261d309,0xf3e5d1625c160fba6496,0x725c160dbee51625c160,0xb7ee91725c160d7ee51,0x5925c160f3e699725c16,0x60f3e5d9925c160f9e59,0x93925c160bbee99925c1,0x960e3f61d74589609fe6,0x595905c960abfe918758,0xc960f3e5d9905c960f9e,0xf595745c960dbe659905,0x5c9609fe683945c960f1,0x3f5db945c960d9f59794,0x45c9609bf69b945c960d,0x8ff6a3945c960c7f61f9,0x875c960e9f661655c960,0xe9f6898759560a7fe91,0x39261d60abfe999261d6,0x708ffe9192e05708ff69],#[0x89845c970b7be89835c9,0x970e5f597845c970b7be,0x69b845c970c7fe5b845c,0xc970f1f619655c970a7f,0xf5d96560970a7f693865,0x60970e9f6196560970f1,0xffe8594e0970d3fe5976,0x4e0970cdf59594e09708,0x8ffe9994e0970c7f5d99,0x92e19708ffe9192e0d70,0x8ffe9192e01738ffe91,0x9425c110ffc651215c11,0x10bfe6a5425c110ffa64,0x91725c110f7e651725c1,0x110efe651825c110f7e6,0xe91925c110dfe651925c,0x910efd6a17448510bfe,0xb6a17250910ff9685725,0x50910dfee819750910ef,0xff6a19750910dfd68597,0x15c910f7d5d1915c910c,0xdfd651915c910efd6119,0x845c910e7f661745c910,0xaffea5845c910aff6a5,0x1945c910bfee81945c91,0x10affe91985c910cff66,0x919760910cffe91985c9,0x120affe919261d10affe,0x68d7250120ffa6857250,0x120ffa6997250120ffa,0xe6858750120efe69d865,0x50120efe68d8750120ef],#[0xfa6917258120efe69987,0x458120ffa6897458120f,0xefe6a17458120fbe6997,0x8758120dfe6a57458120,0xefee918758120efe691,0x1915c120dfe691975812,0x20efe611915c120f7e5d,0xa5435c120dfe651915c1,0x120f7e5d1935c120bfee,0x651935c120efe611935c,0xc120bfee91935c120dfe,0xe659645c120fee651645,0x5c120bfe6a5645c120fb,0x7e68d745c120f7e68574,0x45c120f7e659745c120f,0xefe659845c120f7e6997,0x945c120fde595945c120,0xefe619945c120f7e5d9,0x1865c120dfe659945c12,0x20fee6817450d20efe69,0xa58750d20eef6a17450d,0x120fee6817459120cffa,0x69d8659120eef6a17459,0x9120eef6918759120ebf,0xf6a58759120ebf699875,0x59120dfe6819759120cf,0xff69d9859120cff6a197,0x5d120dfe645905d120c,0xfde595905d120dfe64d9,0x905d120f7e5d9905d120,0xdfe659905d120efe619,0x1915d120e7f61d915d12],#[0x20e7f61d935d120cff66,0x59655d120cff661935d1,0x120edf661655d120f9f6,0x691865d120e7f661765d,0xd120ebf659865d120eef,0xf6a5865d120e7f69d865,0x5d120aff6a5865d120cf,0xffea5865d120cffaa586,0x65d120e7f61d965d120a,0xe7f685875d120cff6619,0x875d120e7f68d875d120,0xcff685985d120e7f699,0x9985d120cff68d985d12,0x20edf6918759520cff69,0x91865d920edfe9187595,0x920e7f691875d920ebf6,0x691985d920e7fe91875d,0x1920cffe91985d920cff,0xfe919761920cff65d946,0x61d20ebfe999761920af,0xffe519161d20cff65191,0x361d20affe919161d20c,0xcffe519361d20cff6519,0x9461d20affe919361d20,0xaff6879461d20cff659,0xb9461d20cff65b9461d2,0x20cff6879461d20aff69,0x9b9461d20cff68f9461d,0x130affe919661d20cff6,0x691725c130f7e651725c,0xc130efe653825c130f7e,0xee91925c130dfe651925],#[0x5c930e7fa61745c930bf,0xffa61945c930aff6a784,0x25c160fbe651625c160c,0xf7e691725c160f7e6517,0x925c160dfe651925c160,0xfbe6817458960bfee91,0x18758960ebf6a1745896,0x60f7e5d1905c960ebf69,0x91905c960dfe651905c9,0x960f3f659745c960bfee,0x595945c960e7f661745c,0xc960f3f5d9945c960f9f,0xf61d945c960dbf659945,0x5c960cff661945c960e7,0xffe91985c960e7f69187,0x261d60cff6519261d60a,0xebfe999261d60affe919,0x7260570e7f6117260570,0xaffe918260570b7fe91,0x1835c970e7f611835c97,0x70b7fe91835c970d7fe5,0x19845c970f5f595845c9,0x970e7f65b845c970e7f6,0xe918360970cffe518360,0x970bfee819360970aff,0xf5958460970b7fe9d936,0x60970e7f5d98460970ed,0xdf59794609709ff68794,0x460970d7f5db9460970d,0x9ff69b9460970cff61b9,0x94e0970f9f6596560970,0xcff68d94e0970cff685],#[0x39260d70cff69994e097,0x20eff6a5865d1209ff69,0x919161d20eff69197619,0x960eff6919661d20eff6,0x6919261d60eff691985c,0x3012500d2005e0000eff,0xb033d02c9026b0202018,0x2052904b5046d0404039,0x706e906ac064e05f0059,0xd08ca086c080e07a5074,0xe0a950a2c09d90986091,0xa0ca20c650be60b880af,0xa0e570e0f0db10d480ce,0xe0feb0fa30f5b0f130ea,0x411cc11631110109c103,0xf13a2134f12fc1272121,0xe152b14e3149b143213d,0xd16ca1677162415c6157,0xc1869181617c31770171,0xd19b01973193618f918b,0xc1b391ae61a931a4019e,0x81d1a1cc71c5e1bf51b8,0x71ecf1e921e1e1dcb1d7,0xf20bb20471fde1f801f1,0x82265220721d52177212,0x7240423a62353230b22b,0x225cf257c251e24c0245,0xc2763271b26d32680262,0x290228ba2872282a27c,0x22b042aa62a2729c9296,0xc2cae2c5b2c082bb52b6,0x82e792e262dd32d752d0],#[0xa2ff72faf2f722f2a2ef,0xe3196313830e5309d304,0xe334b32d73284323131d,0x4350b3497344433e6339,0x1370d3699363035d2357,0xb38ee389b383237ea378,0xd3a2a39f839a5395d392,0x33c0b3bb83b393adb3a7,0x93dcb3d783d0f3cc73c5,0x83f803f223ee53e7c3e2,0xc40e8407f404240103fc,0x142c94281423941af415,0x3442643e943ac4359431,0xc4599455c450944ab446,0xc473846f04687463f45e,0x548d74884484747ff47a,0xe4a554a0d49c5497d493,0x84bff4bac4b644b114ab,0x34de04d824d3a4cc64c6,0x44fab4f4d4ee44e7b4e3,0x8514a510d50ba5072501,0x7530a52a1526451f051a,0xa547d541f53c15384534,0x455fb55a8553f550254b,0x857a55752570a56c2566,0xb590258ba587d583557f,0xc5acd5a6f5a1159c9596,0x75cae5c5b5c085bb55b4,0x35e845e265dde5d5f5d1,0xe608660335fe05f6c5f0,0xa6267621461c1614d60c,0x2645363df6381631862b],#[0x36655660265af654664d,0xe680a67ac676f66fb66b,0x269b4696c691968c6687,0x26b7f6b166ac36a656a1,0x96d6b6d236caf6c466bd,0x46f4c6ed86e7a6e1c6dc,0xa710c70ae70506ff26f9,0xf72d7726e722671b2716,0xc74c3744473fc7388731,0x776af765c75e8758a752,0x5783877da7792774a76f,0xb79f8798f791b78b2787,0xe7b767b2e7ae67aa97a4,0x47d4c7d0f7ca67c327bb,0x77eca7e6c7e0e7dd17d9,0xe80a080377fce7f5a7f0,0x88260820281ba815180f,0xe842083c2836482fb82a,0xc859e8561852484dc847,0x88795872c86ce866585f,0x8894a88ec8899884687e,0x88aff8aa18a4e89fb89a,0x38ce08c828c3a8bdc8b6,0xa8eb68e638e058da78d3,0xe9110907b901d8fa98f2,0x992c5927d921f91c1916,0x9949b945393f59397933,0x2963a95e7959f954c94f,0xc97d99786973396d5968,0x5996d992598dd987f982,0x49b0c9ab99a7c9a1399b,0xc8ad08c1343889b9c9b5],#[0xc2304f0e2851a22f0904,0xc188a3844053c202a90f,0xe3dc741882de220a3901,0xe0ba0c38fc13059c710,0xe70f05bc460908c5814f,0x6092411822029e3e0c78,0xf31de1c4da16829e208d,0x78782846bc4190c2c418,0x8d216f118260a1463cc7,0x530490064c798ef0e0bc,0xc4f8f14a48fc778842d0,0x8bc7f8e42d053c460908,0xe0bbc4702321858904a0,0x91d824138c064c798ef0,0x8791f826471506a0cc8f,0xa1208c11014f0906a0cb,0x8406b069c3c8f91d8260,0x3a8f51ca410cc14200cf,0x60a28f51d8248a47e12c,0x8260a68e23c212313a86,0x1d09c524608bc2035d1f,0x491f23a48108654828f5,0xc8ec284222f08e1e0ca1,0x4712067c203570f24247,0x822f082760ca1491f826,0x11c22f1de23048272011,0x50117882318248625e3e,0xee3a0a3901fc7c23f1d0,0x71f825c71308e1178471,0x8e1e11c22029e1017487,0xa0e0681141471f824233,0xc9f088884e98f31c6430],#[0xc82ef0863c8d19031da1,0x8d18f31d8244e938880,0x243c4045321101905de1,0xc17787d09c0b8048f91d,0x27647c8e920c5080600b,0xfc0bc46092c91922f08,0xd81a82ef0923e47490b,0x82e1a4848f91ca34170a,0x876092247c8e921e21c3,0x24914688bc241923543e,0xe836f090648d50fa1d8,0x1187b0e6216090c90888,0xc3d8758284434a3845e,0x44c3d8711ac123a1962,0x10a1f43a84e82250ea19,0x428b06a32a303be101ad,0xcc709a444360fc1d843c,0x643c468206a311d32063,0x10e1287609a2a398f31c,0x822f43b04d152111413a,0x92da1d824a0260b343d0,0x724d04f1111522f42343,0xa22c2628f84609331c38,0x51a22e1182787198c264,0x2304f0e04e0c46080294,0xc84d8430ec120cc800fc,0xe10c5f04f0e321101c08,0x90890b2130620b251d82,0x27c210b609e1c28c745,0x87e10e1304f0e0543c22,0x3a136118258704614116,0x6c258704d82307615e12],#[0xa8d0aa1cc1145b077092,0xfc27076150583417826,0x6c1161f07615e1236087,0x58204d82307709c38382,0x13608e1383b0e5141ac2,0x8c43f08e13c384c71320,0x409ac3f08e1dc24704a0,0xd0561f84309e1c3e84d0,0x8b0e09b84f0e1d89e84,0x170870fc27870fa13417,0x343b0e04dc24704da134,0xc22c2709e1c3d84d04c2,0x4dc25870461f41026d0f,0x8709c27870e0cc1902a0,0x709e1c0a8504da1f4170,0xc182ae12c38230bc22c2,0x8c2f08b0fc278702a14,0x9e1c0c856100cb84b0e,0x3d88431826c70fc22c17,0xdc4418c12e3c742c852c,0xe3a0c60973a3c16828e1,0x1ce1f04d1a1e0b41471e,0xec13858ce8e85a0a58fb,0x609c2d4689235050c798,0x8d1208c0a04670f63ec7,0xa22828e1d0b58fb1d826,0xa387b1f826c7616241f,0x3bc460908c383624646a,0x1051c8616200c78f047e,0xc2c6747846e3dc7587f1,0x8ec2c3923828e3dc7609,0x4b8e280a02e71f61f04b],#[0x1905f48e0a38f42d61f0,0x3414c13859c71231517a,0x20498f31c6430b19dc28,0x88ac7d8e70fe210a616b,0x2863cc7609c2c6748446,0xfb1d8270b19d240c82e4,0xd8ec2c50460460890a58,0x606c0d417587e0563f04,0xb8742d63ec7609a34504,0x4e1605c322283305152,0x210b609078458fb1ce1f,0x2e3823080880a78ff1de,0x91f23b04b848284004c1,0x8eb0f8254d8ee1e0d419,0x2609829864782886547a,0xb04e1904e3123d1fa39c,0xe1304e8e2463d87d1fa3,0x1ea3b04836230cc14d1e,0x991d8507035e110cc145,0x609936489b832e1e47e0,0x807888a0cb8742923e47,0xb8706b23e47609c2926c,0x4d89d91f23b04e14200c,0x3948219b09850706f064,0xf05b04a8ec283d8751ea,0xb098242368e204ea1951,0x9d1d85070458650a68f,0x4827d1c302206ba3ec26,0xb04a9d84e3046b0fa3f0,0xa3b04d1853a4a1951ea3,0x79a3884448660b414d1f,0x61ac3f02c33a3dc26090],#[0x35181101451ea3b0484,0xc70321b47e8e7098270a,0x25c78a12023214b11826,0xc284904608a0a3887098,0x901121e828e21c7e0908,0x501dc7b8e829825cd900,0xa05e3bc460908c582304,0x352012822842287c7a16,0x45e102341471ee3b048,0x8444562304d8fc282848,0xf58842963f0483d1c129,0xac7d8ec13850cd8e2840,0x63cc7190337850714a88,0x1e63b04e143363e22d0e,0xf31c46b0499b211109d3,0xe09b1d85090320bb4398,0x13900dc52a2213a66ec7,0x82f05c116c7e09d0f638,0x12823f1fe3bc460908c3,0x961138f71d611c86141c,0xd295c7b8eb098258d170,0x71c118445c8650a42205,0x8fc13851c70a519c7e09,0x368771ee39c842716113,0x443a2253ae3f04b8e84e,0xf1c13c16828e3f04b8e4,0xc05bc7f8ef108530483,0x4e8ee3bc4584844e430a,0x888045611c7b8ec13851,0x17219428e3ec260971d0,0x1dc7b8eb098270a03518,0xe067c218f31c6430a035],#[0x45a1ec7d8e709824170,0x3f70963c11609b1d8507,0x484d10c5050f09d1e50,0xf42709d1e383c2464881,0xa3f8482b1814828d1161,0x1c26d487142381688d0f,0x9137c507e01096c3a8f5,0x28ee12502513aa3d4770,0xa43226d174a5b0ea3d8a,0x922629a3f477099364a1,0x4749062926c807829491,0x404df142191b2270f23e,0x326c9e000dc4ec8f91d2,0xf09192213ac5247c8ee1,0x9c0822c8f91dc264e940,0x91dc264d940c01782ed0,0x20f01b03505d61f8148f,0x54a26c4ec8f91dc268a1,0x8f91dc264d82e1a0d419,0xed14d1fa3b84a9b25c3c,0xb47e8ee1238a52464884,0xc274703c174270208a11,0xda3f4770908a2684d1f,0xc70fe3d0c78ef1142423,0x184d0fa12c403f612c52,0xc278158f1ec4709b1c1,0xb11c26c7900a343e84b1,0x8de284029051a1f42702,0x217c011289d32063cc74,0x2e321a1cc798e2354274,0x7684629640705da948c9,0xbc4227b20322344563ec],#[0x63cc770944e5687b1f63,0x1c312e2344644e82e94a,0xee124e84e0563c23709b,0x8c0d81a92ee0563f4258,0x7d0963c1fb09b1cc5070,0xa22e0563ec770914a468,0x42040b1fc26c70e0b911,0x13c7788e12118907fa1f,0x2e38230a08c110a1f1e0,0xf102978483c21c7804e1,0x88612118606244bc7f8e,0x1388e12e38604fe3fc77,0x5c7f0971c1184d0809b8,0x808a498f31c640cee271,0x600bc1748f91de1e4878,0xf91de11c3c90f100b8a0,0xe8e709a4070920d81ac8,0xc429028c6587e05c0347,0xf8406c0d41728f51d453,0x47c8ee13274170c126c3,0xf28a68fd1dc254d8ce12,0xc08c1128f51dc24230c0,0x30fa1f8168f709a3b848,0x8506c0d41728f51dc242,0xc24230b61347e8ee120b,0x1fa3b8482e1547a8e05d,0x6d0fc0ac4709b1c3587d,0xa1b1011ac7b0907c402,0x50d88e1363c220e8890a,0x3fc77886121185446888,0xdc0b43b88b09c25c70fe,0xd0fc09c7d8471dc24704],#[0x3cd0fc0ac7f09b1c303c,0xa1e709c22c1609e1e48,0x10b609e1e28c60470881,0xc2343d82c13c3ca843c2,0x1e47872520781ce22709,0x90563038e11c2743d84e,0xf090522e87d05c2387f0,0x41508a1fc247e1028f87,0x5a8450fe12401e82561f,0x9c3f848d07809587d04c,0xb0fc3f848c0a741708b0,0x8b0583f848c0a741708,0x4687e1fc24148d048126,0x82350fc134391112e138,0xe1304d1a1fc201483246,0x13469110e88a0cd0fa1c,0x9331864683343e87384c,0x6091478647045c3f8760,0x8760906c4c22e1fc390b,0x888844077c2046432c3d,0x237844330518830f61d0,0x641141461f8242330e2a,0xec3b048461811a1df088,0xe1d826c1619210c81461,0x84e13868707ee101170f,0x4e1a06a301d06b83f075,0xd873109464b84c1f83b8,0x28c9f0908a0a446232c3,0x1121d23211987d0961c,0x1188cb0f61d4241b11e1,0x1cc42c26826324c22828,0x9078c64894b28e43b0f6],#[0xca31b43e82e1fc3ac230,0x848a31ec230f61cc418c,0x241b0a8758cb0f61c46f,0x828f877092187b0eb09c,0xe120d8605e8890ef0fb0,0xea120d8a079c3f87584,0x93a081af8405d44287d,0x81a93c3f877095300d45,0x483605de11c1610c1f83,0x6a2b0f61c0d784846142,0x9d1c0f05e1fc3ac17090,0xd88b1fc241e90e134470,0xc470908c402404211911,0x424c0a094c978f005e3b,0xee3b84c9819c7b8e844e,0x71dc264c0351511c2271,0x4631e63b4119006a4b8f,0x7d8ee132687c46077c22,0xcc7190c28483f044c5ac,0xd4848c88c8ea22f0863,0xb11a46f09850c798e320,0xe181191d31fc24c70461,0x3901dc4682e0e09b84b8,0x4d0f611c7b8ef11a0a11,0xfc507e08a8b38f71dc25,0xfc24148ce3f4170971c0,0xe13a381e0ae1344707d1,0x8b05c1f87e8919c268f,0xb508a1d8251151524147,0x787198444423f07f04d0,0xc38230d84c0a03ce1182,0x13c38231184c13f08c13],#[0xe08c402230584d0b708c,0x9629451998c27c2304f0,0x354a85b8470ec1288a8a,0xa16829c38947f0aa0a41,0x1e0f84c1f83c045c2304,0xc4702984f84384c13c38,0x638320598234160ee120,0x240ab13610c3a4c70906,0x80c815708067c3b84c98,0x627c2184f0e180304707,0x486272618430ee125898,0x484618135870680cc168,0xb848332024043e11c3b8,0x28cb54a07289d0870943,0xc89c1c82b4218b50ee13,0xc2687033a26492c24c45,0x120cca180a9420298a11,0xf252832455c2387584e,0x1161151f0ee120c4708e,0x1e11c27872a32583843e,0x313e10c27870c01b4103,0x19a2ae11c3a4c7092e4c,0x4e519411c6003c465294,0x41432854e1384709e1d4,0xb84384e1dc24130e0c7,0x161dc270ee120987d0fa,0xe11c39c270904c3e82e1,0x88c1248dc76162343d82,0x49a171f85890664560a3,0x89b100f88f9237110530,0x5123235051c7b8ec1385,0x81ab87b1f63b04e1605c],#[0xe2304b8ec2c584908c0d,0x823d870660c81503c828,0xf20a388c12685c7e162,0x1f825c7046242203e844,0x908c3849d080d4170367,0x8461c91918d1fa3b04e1,0x5b9048c8c68fd1d8270c,0x9d13686547a8ec13850,0xa5027c33a3f04e8e08c3,0x281a82fd1f8274761434,0xfa3f04e8e08c283fb081,0xc33a3f04b84d1c0f0804,0x8fd1d8270a0352811014,0x9046182504606e0bdc26,0x6c72271d0a588c136381,0x850190e07209d8884582,0x400e8607e85ac4609b1d,0x9b1e1188b118270a58f3,0xa271c1201e428286c460,0x50900920f588c1363e50,0x82207f6210b609b1f852,0xf58870963f04e1407a3,0xfec7d8ec13850cda2224,0xd8270a19b06a382502c0,0xb1d8270a035280c98f31,0x14242503f06e0bccdd8f,0x690884e388c12295c76,0xa171182452b8fc285197,0x483508c3041148682110,0xb04e1416e441471ee3b0,0xe3a138e2944ec2271ee3,0x21118803a8651138fc12],#[0x62212c16a05089c7b8e7,0x4aa768102271f825c704,0x582ce3dc7609844c68a0,0x60906a118645c8650a4a,0xc7609d0e1148a04e3dc7,0x3d8a0a5201782e04f63e,0x3a3c807e05b444a1613a,0x202003f90fa2013f0994,0x80eec383ad11a3f84aa0,0x936c5347b09d1c1188a2,0x9bd1fc27470461812816,0x3c8f91dc264d82e2813c,0x54d846182483c06c0d5c,0xc254d8462413e8fd1dc2,0x8c304906c0d41728f51d,0x416e484908ba3f84e8e0,0x941181a82fd1fa3984b1,0x408c11747b14d1dc24a0,0x387e12114609612a4ee8,0x52d0971d450b08da3f47,0xc22538a5e0b03f068e20,0x1fb8882d42550b8fa284,0x3dc75147211188083088,0xf425c70462212c2282ce,0x635294a04a0894ed1471,0xc4648a42282ce3dc7509,0xa04e3dc750916e118725,0x9c02f62384d8e08c3684,0x3c9c92f62384d8e08c38,0x852020b11c26c7846191,0x72113ca1b11c26c78461,0x3bc004d98f31c6438a0b],#[0x230a89ec7d8eb2091851,0x2743845264ed8fe13638,0xa503005e09d52d8fb1dc,0x644e89b31e63a13f0954,0xc0d784c2725c492e2344,0xe1211470920d82358fb1,0x8e08c404908da1ec7d8e,0x28a12c2568408b63f84d,0x55292e1ac7d8ee124b95,0xc26c70461b4258fb1dc2,0x1fc26c7046184e81bb1f,0x2711c25c76842a4ec9bb,0xe842823f020780cc9503,0x384411381388143c25c7,0x82e71fc25c7046241e42,0x84b8e08c2849d080d81a,0x85c470971e1186086e23,0xa115c7f0971c1185088a,0x813c2093e8fd1da40a30,0x482464888a68fd1ce134,0x802f05d23e4770993a11,0x783b84d1fc2747046141,0x92811822d1fa3b84a9b0,0x93c0823045d1fa39c270,0xfd1dc25c2049261b4350,0xf0908a483c06c0d41768,0x80921191b235d1fa39c3,0x3606ba3f47709708124,0x1aa8f51c0bb848461c1e,0xa913d88e1363823120d8,0xfc26c70471823c338650,0xe13639c2047201358832],#[0x9b1e11860660c815588,0x4ca1b1e0f0744f286c47,0x384d8f08c48207096238,0x118807c0f4c938408962,0x24a3646a8b9c7f0971c,0x8c915388b09c25c703c2,0x5ce3dc770907866c8466,0xfb09c25c703c211b2354,0x70971c11c646c8d51738,0xc470971e0f0504d611c4,0x22c238fe12e381e0b611,0xc0d41758fb1dc25c2049,0xe11826c142142dc3c906,0x9e1e28e10920fe11822,0x170f221104014a663846,0xc907f0790b708b058251,0xe022e118250b414c43c3,0x304f08c43c3c1e0e0fc1,0x61384f0f63c0ec8028e1,0x1161387f091e52821e11,0x9e1ec781d8fa081e838e,0x609a34118894b2638470,0x87046211141942d43e87,0x18702d864c1022e1f827,0xc38a5147c3f87609c321,0x1f0c984b05c3f04f0e08,0x530cf0fc12e138703c,0x22c86707e0e613868231,0x2fc1f83b84e1a06e4922,0x7709c340d4ab081281a8,0x880940fc1b82f70983f0,0x101414746787d09e1c11],#[0x34170fe1d4268c846181,0x528cf0f7094278703c2,0x32c3d8770906c1187045,0xee1fc3b84d8406c501d6,0x31988c40490792941aa2,0x231129651c9861ec3988,0x8a514687587b0ee12c64,0x4103661ec3b84b1908c3,0x9451f0fe1dc264c3192b,0xdc258cc982d1aa2243a2,0x241e23545d2941b70fe1,0xee1387f0ee13a081a941,0xe12e1024901282303725,0x9b046835d040bb87f0e,0x45f0b823035e1ee13877,0x970812480941251bc36,0x48461c1e03605dc3f877,0x819100d81703561ec3b8,0x41257080ff44709d1d60,0x20e422d10e1384e8e246,0xa214bf09d1c0f2190c0b,0x7ee12c4709b1fa0a1095,0x1e1363d11908941151e0,0xa9807a4424072e12c442,0x231009311821b1163f84,0x42582d20a1138f71ce42,0x2448271ee3b8483508c3,0xc10ec2271f611c7223e1,0xe1384d88b1f4841e0e0,0xc29622c7f095300f4704,0x1407562184d8f08c3623,0x1a22b11c26c783c0883a],#[0xe4261471ee39c8446191,0xc764268271fc25c70461,0x55611c438e52bc241890,0x471ee3ac239087838330,0xb8fe13611c703c1e11e1,0xc7b8ee1266c1e0e08d8e,0x3ec270971c0f0763ac65,0xc63cc719048c423645ce,0xe12e381f8dc001b03505,0x8271fc25908c0c9c4682,0x7b8ed05c241a8c0f5c46,0x1c2709d1f8881d900fdc,0xa1e1384608a4841073a2,0x8c114509612824d1aa33,0x708c10ccb8e1261b4350,0x84608a66c68670c9c284,0x1ae8208c11460930da1a,0xda1a84608a6607096126,0x4a0930]]
set_option maxRecDepth 16000 in
def g255H10 := limbs80 #[#[0x200001088001e00000,0x80100000010002080000,0x1b00000000400020000,0x600000080040448202,0x2881812086080100042,0x4010000d141320884004,0x8408200881401600040,0x2410000902410100000,0x40044800800940224,0x4009602001048608a00,0x22,0x0,0x0,0x1c3380,0x0,0x0,0x8c98000000000,0x32b8cb1680,0x0,0x421780,0x39ce8000000000,0x0,0xe800000000000000000,0x58,0x0,0x0,0x55800000000000607b80,0x84000000000000000029,0x2b,0x0,0x5085800000,0x0],#[0x259224e503080,0x714f00,0x6f80000000731371d800,0x3f8000000000005a,0x0,0x0,0x0,0x1ad000000000000000,0x36c8e6c0398000000000,0x4ae680000000000032,0x10b980,0x4698cc80000000000000,0x22,0x18af8000000000,0x4a7a800000,0x38e500000000000000,0x3ae5000000,0x70320862800000,0x10b280006cb480,0x22208000000000,0x0,0x0,0x605a000000,0x6ba100,0x50012ada135a80,0x4881800060c7000000,0x46000000000000000000,0x80800000000000603eb8,0xea000000000000000020,0x30,0x1200800000,0x9800000000000000000],#[0x13,0x0,0x484a800000,0x7852000000,0x284f800000,0x0,0x68dd00000000011f80,0x0,0x4b128000000000,0x22c9581d8000000000,0x19800000000389000000,0x68823b,0x0,0x6b0f800000,0x0,0x6c488000207900,0x58a07084800000,0x2a6e80005aa000,0x10b780000000000000,0x0,0x63000000000000000000,0x68,0x0,0x0,0xc800032d18000191800,0x2b,0x0,0x6000007ae18000000000,0xc2eac1e2588000000059,0x40a7800049,0x0,0xe180000000000000],#[0x175000000,0x1a66800000,0x0,0x72818000000000,0x5a1880007a2780,0x4c06e246000000,0x0,0x5c5060188000000000,0x61910000000000,0x0,0xc4526c4b0f000000,0x4a800000000000000000,0x40a1f2,0x0,0x0,0x186b994980c500,0x1c000000000000000000,0x71,0x5c438000000000,0x3da0000000,0x82000032810863800000,0x12,0xb8000000000000000000,0x7096800000001c,0x89d0000622b800000,0x5822000000,0x48aa000000,0xc4b8ba98416055000000,0x39,0x3a7b8000000000,0x8d00000000000050cd00,0x2],#[0x6c7b9700000000000000,0x58,0x28a900,0x225e000030b480,0x6b8780,0x0,0x1216000000,0x1b1200,0x2c4200,0x2432800000,0xa000000000000786d00,0x30,0x0,0x0,0x482c00,0x0,0x5f000032c6228d800000,0x5a6849,0x0,0x0,0x10d6504d000000,0xea800000000000000000,0x62730000000048,0x0,0x3b14800000,0x0,0x0,0x386c800000,0x0,0x332240083b0000000000,0xbb800000000000000078,0x682c800040],#[0x3cbd80,0x586e00000000190a80,0x8190000000000,0x0,0xcc000000000000612400,0x352a2300000000000061,0x1a61800072bdb0ad90,0x412b00000000000000,0x405a8000000000,0x0,0x0,0x0,0x30840000000000,0x28b580000000000000,0x84800000004117000000,0x9200000000293078e41b,0x60,0x4810f04a0000000000,0x94c000078c2000000,0x77800000000000000000,0x3c,0x0,0x0,0x220200000000000000,0x42b4800000,0x0,0x0,0x1a5e8000000000,0x7831000000,0x0,0x14000000000000000000,0x13],#[0x0,0x0,0x681100,0xe7d82ee23380,0x0,0x0,0x0,0x5a8e00,0x0,0x317a80b00,0x8c00000000684d800000,0x62,0x91780000000000000,0x4000000000000000000,0x4920000008,0x2876800000,0x0,0x53028000000000,0x0,0x8ae0000408800,0x720bf83c00,0x0,0x0,0x0,0x253200000000000000,0x0,0x221980000000400380,0x0,0x283780,0x19800000000000000000,0x1c0000000028,0x28050000299180],#[0x0,0x6b15030c00,0x0,0x133800,0x0,0x0,0x8b800000000000000000,0x1b,0xc4800000000000000000,0x2680001360f2801a73c8,0x70,0x494700000000720880,0x39000000000000000000,0x28,0x30000000000000000000,0x21000000000000000075,0x8c800000c0000000001c,0x715ffba4000000001b,0x6041800038e600,0x22d380,0x118980,0x795938d70000000000,0x4268000000000,0x0,0x86000,0x20266337210b00,0x0,0x0,0x0,0x3ccf30230000344e80,0x306500000000000000,0x74428000000000],#[0x6d800000000000000000,0x4115800000001c90c0,0x7b8e00000000000000,0x0,0x57800000000000000000,0x57ba700000000000053,0x3,0x0,0x0,0x0,0x0,0x0,0x6a0e800000,0xa3e800000,0x4e08000000000,0x0,0x0,0x0,0xa9500000000000000,0x9c40000000072c480,0x0,0x0,0xa2241c04c0800030a200,0x20e380000000000032,0x87000000000000000000,0x4b,0x0,0x630600,0xb03ac0802f8000000000,0x46800048d3c0ab000038,0x69,0x0],#[0x0,0x1080004a778000000000,0xe8800000000000000042,0x5a3d990e00001a,0x504780000000000000,0x0,0xce800000000000000000,0x5280000000000064ccf0,0x50420446d8062a,0x0,0x96000000000000000000,0x70d0f8,0x0,0x203000000000244e00,0x0,0x48b18000209a800000,0x540000000000,0x0,0x40318000000000,0x70eb0000621100,0x63610000000000,0x508a8000000000,0x0,0xd7800000000000000000,0x626600000000083869,0x0,0x400a8000000000,0xe5000000000000000000,0x7868c10000000000002c,0x31c5eac1000068,0x40d850cf0000000000,0x0],#[0x0,0x0,0x408f0000000000,0x58ba19d8d0d180,0x20989380005aba000000,0x383b91,0x0,0x0,0x4a09580080,0x76907e00000000000000,0xd705778dc8000789b4a,0x72e370e3000030a73a,0x8bf80000000000000,0x1102000000,0x2c6c8000000000,0x0,0x0,0x0,0x0,0x609000000000000000,0x0,0x0,0x85673308000000000,0x4b0d80000000000000,0x0,0x3b1169c78000000000,0x0,0x70828000000000,0x0,0x82b0000000000,0x0,0x0],#[0x3827000000,0x0,0x0,0x13800000000000000000,0x928000000000001226aa,0x20,0x0,0x0,0x0,0x0,0x783a80001b0b00,0x4ac980,0x0,0x432fa2714c27000000,0x308f8000000000,0x49cc800000,0x0,0x0,0x0,0x0,0x0,0x574a1580006a21000000,0x11,0x5e000028000000000000,0x68,0x18c28000000000,0x6c0874c1480000000000,0x51de50549b5e59,0x0,0x0,0x507f800000,0x0],#[0x4080000000420a000000,0x5316000018c3800030,0x0,0x0,0x102000002324800000,0x186e80,0x4aa4800000,0x137d395c80,0x849000000,0x50a480005295800000,0x320c0000121f899200,0x0,0x3b5e8000000000,0x0,0x0,0x60e900000000000000,0xcd2308e2e900002b8a80,0x38569023800009,0x0,0x0,0xc6f84380000000000000,0x72,0x64000000000000000000,0x430b80000186b0,0x34800000000000000000,0x72ad00006a5798,0x490b80000000000000,0x721c00005ba5000000,0x0,0x0,0x184280000000030000,0x4800000000000000000],#[0x9,0x38d1000000006a3f00,0x610600,0x0,0x30000000000000000000,0x78b80000000000003b,0x0,0x228c8000000000,0x710000000000007a7f80,0x9300000000630e800043,0xc3800000000000000040,0x7116c2,0x690e80,0x6817800000,0x0,0x0,0x5bab01a48000000000,0x2b9780000000000000,0x280680,0x3079800000,0x50b68000000000,0x0,0x0,0xa78000000,0x0,0x0,0x784c80000000000000,0x6c99130000703e609480,0x8360000000000003a,0x2a570bb000000,0x9800000000000000000,0x3e000000000000000012],#[0x8a54baac09d800021,0x68a88000000000,0x0,0xa8700000000000000,0x0,0x0,0x52c580000000000000,0x8e280002b9900,0x61a62b5500,0x6921087e80,0x0,0x2971800000,0x0,0x0,0xd6a2a600000000000000,0x6a58,0x0,0x5a800000000000000000,0x6a1ea8a64829b9,0x0,0x0,0x183d8000000000,0x303f00000000000000,0x6b17a80000000000000,0x588e85,0x7e80000000000019cd80,0x5a270000000000007a,0x6a8300,0xbc000000000000000000,0x10,0x687a80,0x0],#[0x0,0x0,0x0,0xb98000682a0000097280,0x12,0x0,0x5a9c00,0x850910f800000,0x26480,0x1e000023988000000000,0x9f0000000000002adeaa,0x72a4000023567a,0x5007000000,0x0,0xa4000000000000000000,0x78,0x0,0x0,0x510c80000000000000,0x0,0x0,0x0,0x0,0x0,0x848800000,0x50a800000000000000,0x58208000000000,0x4066800000,0xa5800000000000000000,0x4b88000785992,0x403400,0x28d40000000000],#[0x18a580,0x3869dd9f00007a0d80,0x0,0xc4300,0x710f000000,0x0,0x0,0x0,0x580c213a000000,0x0,0x300e000000,0x0,0x6b8c00000000607400,0xd000000000000000000,0x4ca48b,0x7b8000006035800000,0x3aaf00,0x110d00,0xc81002280,0x0,0x0,0x44d300,0x785151058000147b80,0x0,0x99000000000000000000,0x507d7a0870,0x0,0x115b0000000000,0x0,0x0,0x0,0x1958000000],#[0xb9000000000000000000,0x4112000038,0x24a2000000,0x8380007ae40000000000,0x78,0x2ca600000000102e00,0xa5800000000000000000,0x28258000000049,0x739800,0x59c60000000000,0x723280000000000000,0xb1282800006111000000,0x40,0x527980000000000000,0x791b800000,0x0,0x26000000000000000000,0x32,0x39dd61148000000000,0x2b8f00005036800000,0x3837000000,0x0,0x1b330000705b80,0x2e780,0x6c800000000000000000,0xd2800000000000000011,0x4a677b13d0,0x0,0x0,0x24f39980005055800000,0x11d900000000000028,0x0],#[0x406180,0x0,0x4e000000000000717200,0x6a0b58,0x0,0x0,0x0,0x105cb0db0c31000000,0x21050000000000,0x0,0x75988000000000,0x0,0x0,0x505d800000000cd380,0x0,0x4cba1086800028da00,0x0,0x0,0x1e800000000000000000,0x43,0x3876000000,0x70dda0946975800000,0x58589845000000,0x2a2280000000000000,0x0,0x0,0x78aa8000000000,0x0,0x7d000000000000000000,0x42,0x0,0xb080000000000010b080],#[0x319068d8800012,0x2a30800054cd000000,0x30b300,0x50c300000000000000,0x0,0x607c000000,0x0,0x0,0x706b0000000000,0x131d800000,0x0,0x7cc58000000000,0x0,0x0,0x0,0x2500000000000000,0x3b7f80000000000000,0x6012f315800000,0x0,0x4a3200,0x88000000000000000000,0x3b,0x38c7a857800000,0x88a00c80000000000000,0x693400,0x0,0x0,0x344900001115290c00,0x0,0x425b800000,0x78a00d80000a65800000,0x344d9b558000302120],#[0x4f0000601a6804800000,0x531070708000414c98,0xac800028750000000000,0x4cce00006b183960e8,0x14a59002000000,0x521001928000000000,0x2740000304980,0x6b9c69a38000188d00,0x0,0x2b1a0898000000000,0x4028a1930000000000,0x18b600000000000000,0xb5b000000,0x0,0x2f0000625c9145000000,0x2d89b899800010,0x484017000013580cc100,0x62180000726258,0x0,0x808cb980000000000000,0x4cc17d80000000000022,0x2b2504,0x0,0x388d80000000000000,0x0,0x0,0x58448000000000,0x1b800000000000000000,0x8,0x0,0x0,0x687b00],#[0x0,0x1f000000000000000000,0x70294a2594,0x0,0x0,0x0,0x74ad00004a2800,0x22d0000400fa18100,0x330a8000000000,0x3a7d800000,0x0,0x240000381b000079a900,0x718000385c000000007b,0x20,0xcd800000000000000000,0x40,0x188000604c0000000000,0x39,0x55000000000000000000,0x12,0x0,0x3a5d00,0x0,0x0,0x630680,0x329780000000000000,0x286a80000000000000,0x0,0xc2000000000000715500,0x389780005c,0x543180,0x5f800000000000000000],#[0x30,0x78da80000000000000,0x4401fb5b800000,0x601680000000000000,0x5255800000,0x0,0x183d497300,0x0,0xc1b859000028bd800000,0x191a000000,0x98800000000000000000,0x30bc80000000000052,0xc2b80,0x596500338000000000,0x1d8961708e000048a680,0x5898da763b081a,0x0,0x794b6877800000,0x866788c000000,0x1b5d0000000000,0x1111800000002b6a80,0x13500,0x81200000000000000,0x0,0x0,0xac4000000,0x6a3e0000000000,0x2800000000000000000,0x71,0xac50000000000,0x0,0x214b80000000000000],#[0x0,0x21,0x5a128000000000,0x58e2000060d2000000,0x587c800000005a6280,0x5cd2126d0000000000,0x0,0x1400006a6a8000000000,0xb800000000000000028,0x28b88000000038,0x2225000000,0x206100,0x0,0x0,0x3d0000488911d9800000,0x68d1,0x1926000000,0x5e800000001284000000,0xdba93fd47d8000710d80,0x1e0a5c00000000000010,0x5a6b8000000070,0x7872e87a00,0x0,0x385f0000488b300580,0x29b0ae80000000000000,0x4278800058be53,0x735c8000000000,0x7080005959f452e2d300,0x75000000000000000012,0x52314a,0x0,0x38bd000000],#[0x70e580000000000000,0x0,0x0,0x0,0x60a28000000000,0x587f61c800,0x38738000000000,0x3a63000000,0xcb000000000000000000,0x321360,0x535d80000000000000,0x62e10000000000,0x0,0x528b28b20000000000,0x59db58a09c8000000000,0x2b600000000068e142,0x503c80000000000000,0x0,0x0,0x0,0x5e000028d90000000000,0xa380000000000041,0x12cd000000,0x0,0x0,0x0,0x0,0x6087800000,0x3caf12290000000000,0x95000000000000000000,0x28,0x398dd07100],#[0x225b0000000000,0x189e0000000000,0x0,0x6872000000,0x12800000000000000000,0x11,0x5a638000615e800000,0x1198000000000,0x32348000000000,0x133780000000000000,0xd200004a718000517480,0x11,0x206800000000000000,0x0,0x0,0x10a1000000,0x98000000000000000000,0x11d500007a,0x0,0x980000000000,0x0,0x38a08000019400,0x2b0480003aa080,0x0,0x435c00000000000000,0x2198d580000000000000,0x3e800000005801800012,0x38b401,0x0,0x9a000000000000000000,0x70c080004125800058,0x0],#[0x10468000000000,0x0,0x0,0x1b5f00,0x0,0xb118000000000,0x0,0x6800002120000000000,0x4a,0x5280000932f38b000000,0x87d8000000060,0x0,0x8000000000000000000,0x39c6e1,0x0,0x6243000000,0x5ae87000000000000000,0x481faa,0x0,0x0,0x0,0x212500005a19185380,0x0,0x0,0x14792a80000000000000,0x22,0x0,0x0,0x9000000005a6de88100,0x2f800000000000000010,0x5a,0xd00],#[0x32000013170000000000,0x69,0xa5f80000000000000,0x48bf00000000000000,0x0,0x0,0x0,0x49d680000000000000,0x2a1b00000000000000,0x0,0x0,0x0,0x53598000302400,0x0,0x0,0xa7a00007a30000000,0x0,0x720a800000,0x72800000000000000000,0x2b80001a318000000022,0x39,0x3a248000000000,0x7803000000,0x0,0x602780000a01817b00,0x4370000000,0xa3000000000000000000,0x28,0x7265393480,0x0,0x0,0x7a14a8cb800000],#[0x44000000000000000000,0x64800000000000000051,0xca000000000000000028,0x8f0000000002d0800028,0x5600000000000000001a,0x188b800049,0x20c880000000000000,0x0,0x726b30df8000000000,0x53522e000032df800000,0x52330000000008,0x0,0x0,0xb7000000000a5a00,0x719380,0x3ccf80000000000000,0x0,0x75b80280002886000000,0x70,0x95800000000000000000,0xa280005a150000000070,0x3a9000007b,0x0,0x1c4780000000000000,0x0,0xde0000201e8000000000,0x288a10,0x442059140000000000,0x0,0x0,0x5d800018e70000000000,0x7a359ae76a],#[0x0,0x6f000000000000127200,0x3b9c80000000000068,0x5f800000000000000000,0x8800000000000000043,0x5a7498e0490969,0x0,0x7c07300006843000000,0x138000000000004b5900,0x6b800000000000000008,0x601500000000000021,0x303880000000000000,0x5d0cf80000000000000,0x73,0x388c80000000398580,0x938a8f80000000000000,0x220000085d117b80001a,0xc700000000000000005a,0x42,0x0,0x0,0x0,0x690a00,0x1acc800000,0x0,0x77000000000000000000,0x2815e0,0x28ad0000620e00,0x2808800000,0x38400000000000,0x7867800000,0x0],#[0x6810000000,0x201600000000000000,0x50608000000000,0x0,0x136f80000000000000,0x0,0x0,0x28800000000000000000,0x6a568000000070ce41,0x0,0x70208700000000000000,0xa,0x0,0xc5d18e80000000000000,0x68,0x539600000000000000,0x80000000000000000000,0x40b50000000028,0x0,0x2113d80980,0x7067000000,0x6b0e000000,0x0,0x0,0x0,0x1a800000000000000000,0xd4581300000000000040,0x47000000003091004ea1,0x20,0x77c01c80000000000000,0x69,0x0],#[0x0,0x0,0x0,0x3a28ab8000304b800000,0x18,0x0,0x522400000000000000,0x0,0x0,0x48d480,0xe99b5a00000000000000,0x0,0x854490000000,0xdc00003a118000691e00,0x484b000008,0x0,0x0,0x286fe8830000000000,0x358000380f0000000000,0x3a47620c81,0x48de80000000000000,0x182d00,0x0,0x0,0x582d80,0x4ad170ca8000000000,0x680004a4bf27c800000,0x1,0x0,0x4acf800000,0x9b800000006236000000,0x28],#[0x39738000000000,0x0,0x0,0x424a00,0x399480000000000000,0x28d980,0x604584d0000000,0x408000009c00003a6e00,0x32,0x522000,0x4b6a00,0x43a30000000000,0x1275800000,0x309f00,0x402a8000000000,0x4ce400,0x0,0x49800000000000000000,0xc20c5,0x0,0x685b00,0x430900000000000000,0x0,0x11800000000000000000,0x30658000000018,0x0,0x0,0x791078c81109800000,0x0,0x705800001c48000000,0x0,0x0],#[0x1f6b1880000000338880,0x11790000000010,0x0,0x18d000,0x0,0x0,0xa00000051e294800000,0xc6000000000000000063,0xdf0cce822c635700006c,0x2be0,0x6212585a0f1a6a000000,0x818242798,0x0,0x4b8d23de40082b8080,0x50d300000000000000,0x221680000000000000,0x69000000000000000000,0x38,0xc6800000e4800070af00,0x58,0x27700,0x317410328000000000,0x10ac00000000000000,0x138a00000000000000,0x0,0x222c80000000000000,0xbe800000000000000000,0x484410,0x1d000000000000000000,0x609f80000000000058,0x0,0x485000000000000000],#[0x0,0xa0800000000000000000,0x2c,0x60a980,0x409e80,0x20c900,0x8e8592a000000,0x98500,0xb3800000000000000000,0x264689748,0x0,0xcc000000000000000000,0xc630,0x1176048d800000,0x21800008e08000644c00,0xae088,0x30d7f0d550e8800000,0x7891a01480,0x0,0x0,0x0,0x189080000000000000]]
set_option maxRecDepth 16000 in
def g255D11 := limbs80 #[#[0xdd2c4b0241fa94250120,0xf4b92e09079e59560483,0xf2cab82c1a7d8659520e,0xec3acab073e5d970583c,0x242b8221c7d7659570d3,0xc12e08877e5c970443fe,0xe90a21bf58448510dfc,0xc284886fd609714437eb,0x8c12213fd985c9109fec,0x30e884ffe5d824427ff2,0xa0241fe962501209ffc9,0x80907de59540483fd2e4,0x241bf98750120dfcc32,0x907be59160483fd2e4b,0x241ef97658120dfcc22c,0x905fe65d604837f30eb0,0x41bf9845c120efcba2e0,0x7de59570482ff728b82,0x1bf9865c120efcbb2e09,0x4ffe5183482ff72cb824,0xafd8659120f3eb2ac890,0x7f61d744827fb30b2241,0x7d65611209fecc2e8906,0xf61d65483cfaecb2a41b,0xd875d920d7ec32ec906d,0xe51864827fb30bb2419f,0x9161d209ffcbb0c904ff,0x59874827ff28c3a413ff,0x25c130efcb92e0984ffe,0xf824c37bf0899261bfb8,0xe09309feca704986f75c,0x874c2fbf24b9a613fd97],#[0xc160f7cb12e0b04ffe49,0x2582ff724b82c1df9725,0x960f3eb2ae4b06bf61d6,0x5833fb0eb92c1cfd765c,0x709fec9702b84ffe4987,0xc3afacab92e19ff845c9,0x9fec8f04b867fe19725,0x36facbc12e13fd94e097,0x9fecb704b867f5db825c,0xcfb0cb2ae13fd92e0d70,0xfec9700b9cff64b865c3,0xf324b8221ff9425c1109,0xaa12e2887fd5d121443f,0xb0ea1221fed7250910ff,0xc8ae4885ff65d424437f,0x8b9221dfd745c910ffa,0xc2e4885ffe51724437fb,0xec1221bfd9460910dfec,0xa80906ff649874437fb2,0xa0241ff97350120ffcb8,0xe0907fe5d160483ff2ec,0x8241ff9435c120ffcc8a,0x907fe59170483ff326b,0xa41ff9965c120ffcca2e,0x907f75cd434837fb08b8,0x41bfd8750d20fdeba286,0x5ffe5d43482ffb2ea1a,0x17ff945cd20dfec22e69,0x7bf5d964483f7ae8b224,0x7fd9759120dfec3ac890,0xffe4574483ff320ba241,0x7d655d120bffc9ae8905],#[0xf61974483bfaecba241f,0xd985d120bffcb2e8906f,0x651864837faecc2241bf,0x9161d20dfecbb0c906ff,0x4d874837ff22c3a41bfd,0x461d20dffc9b0e906ff6,0x9874837ff28c3a41bfd9,0x5c130dffcb30e906ff65,0x724c3bfae8b9261ff992,0xc930bffca2e4986ffe11,0x2583ff324b82c1bfe985,0x960ffcc82e4b07bf5d16,0x582fff28b92c1dfd745c,0x60dfecc2e4b07bf65972,0xc3bfae4c0ae1bfd9261d,0xefec1ae4b86ff609815,0x3bfb0cb92e1dfd845c97,0xdfec1b04b85ffe45825c,0xfff28c12e1bfd8460970,0xfebb304b87df595825c2,0xff2cc12e1bfd8660970e,0xeca2e4885ffe49835c2f,0xb26ba241ffd915d120ff,0xca2e4987ff65974483ff,0x22c12e1ffd945c960ffe,0xb304b87ff64d825c3ffb,0x5803e00ac0158000ffec,0xc682c4099020e06e01,0x15184e6124043a0f1837,0xc606d61a5065218405a6,0x208c621c08061ec076e1,0xaa229089e2260894024],#[0xc7e3118bdc2e40b442be,0x783888dc23588d0232d8,0xc4070fc63d98f063ae8e,0x47e11ac453110042f907,0xfc93924cc92e64ab9258,0x6158255014ea52514344,0x177c5cc16ee5a1162e57,0x94e64098a2618181e5f2,0x206b29a7e68a19d26641,0x472e9c6e7089bd66dd9b,0x7bc1eae78c1dda7611d2,0x3fa0bc81ea01a7ee9f64,0x6a28488921d886321408,0xa49c90f23dc8e9234e8b,0x68c98da5ea967a552941,0x68a0727e49e1272e9b3a,0xea85a9caa64a914a2fa8,0xb042bb0ae0ab0eaabaa4,0x852dbeb5cacfeb252c48,0x12fb8bd62f0cbb02e6ab,0x31d0c59b110c33b064c0,0x41acec3346cb73286c8c,0x28d723572d44b4b2d14b,0x6df5b776dc836c0d9fb6,0xe7e398ee50b8ece23383,0xfe1f8e05814e20188248,0x84068190508f23a09238,0xf842401923c8e8507e1f,0x8c22e138ee20148249e1,0x6819243880b890878f0,0xf065104388e1f8423c8e,0xe824192222e1382a1d0],#[0xe0e824908b84e081d43d,0x24806435e13828401d83,0x2122e13820749023c8e8,0xe122204e874210e82515,0x3e102260b088270e84c8,0x2ae1115c2209a1f0e2ca,0x20ec261520318881404c,0x3b09854804c260b01782,0xc261c241309832072088,0x7241504c260a9148220e,0xd0b02a0c787c2309c382,0x26a1f84a0b08c270e282,0x308c270e0a860cc320a8,0x1187c2309c382a180761,0xa180460b08c270e0c860,0x9858863d8e052098591,0x2141b8f48f8e61f88052,0x258e858863d8ee221664,0x826162819e1c2e0518f8,0x8c22e3f8e61c14e2046,0x448d87a3e8e052098648,0xc50648f23a098509b1b8,0x261427468668f8268e09,0x528f8268e241923c8e8,0x9a3a14242308b8486587,0x142422067840d587a3e0,0x21e3ca5e3822e2184826,0xb8f88b8ee22878242720,0x3f8ee218482422850744,0xe1222a1d8f639908507e,0xae102263d8e826142747,0x140bb8463d8ea1e09468],#[0x58f8242263a141622064,0x26f141e88c0821c268f1,0xec249b2707c008f23890,0x27241a067870b91423c8,0x450c02f0bb87a3f09a38,0xc22e3846e2309a111424,0x1b8ea1f88c24272023e3,0x63d8ee219089c6e3c121,0x4c008f23890277141e07,0x84a3e8e61f8845290270,0x91423c8ec249d252348b,0x528fc268e201a067840b,0xa3e8ec24908c22e109d4,0x90b860d8350bb84a1f02,0x8ec242e18076128fa3b0,0x98811b09638701187a3e,0x383ce2184c249a1c04c0,0x11b096387e3c12a1f02e,0x88270f084901287c098f,0x21c3c828c2308b8460b0,0x70917848881e60b08824,0x1d0843f091e828220f08,0xc2282c270f2682078126,0x1c270f24390a41ee1d84,0x24183d0a41ea0b84c202,0xf09c3c960a0804a0fc24,0x6880f42904b8460b08a1,0x238488819a1d0f43a094,0x28f8408b0fc398282619,0x1a230fc3982824228646,0x48067840d41d83e0ec26,0x2a3e128743d0e4428246],#[0x10a3a081d43d0ec25192,0xd784c3f0ec2682464ae,0x2c3f0ec243518a30881d,0x408a8811b09a3870118,0xe23e3822e2098c247608,0x8b8463d8ea0b006408e3,0x898f6384626b091a238,0x9240462282c258e0c86,0x8f0483fe398408b88a0b,0xa0463d8ea0b88642221f,0xd46a082263d8ec251d1,0x6c268f2004a098f63b09,0x900d48c1d8201012a204,0x68e1c1d06784e088f238,0x3e89218201022a3c46c2,0x66080f82860b8409308c,0xe258288a13c22878270e,0x36121311814c220908b0,0x8461e0884e0e857091c2,0xd8284e0883a1cc25981d,0x28a361f08c270e263131,0x44e820c91cc230ec2698,0x7c2309c3898c4c909922,0x843b090cc8100a528d8,0x70ea0b13201ce101544d,0xb09c38c294a3c2184c2,0x5d134b0230c516a1f08a,0x61308c270ec4ca3182c4,0x20c82ae1308c3b090ccb,0x9c38270c4811c3c0c68,0x70e0982a242d0b02ac23,0x983224330c984c2187c2],#[0x18330a98460b08c270e0,0xf850661d888261663a14,0x168519d1987622098598,0x98482614864763d8e826,0x220963a140c8761e8fa3,0x6120963e14284704d846,0x26220963e14284988988,0x8e8261466c80901e6102,0xb88824462e2208a8763d,0x25884a105b8f40b8e08,0x8819e118f63a09850352,0x2c509a2309a3a9c49c50,0x909020a1088c258723c9,0x2021c84a2309a3f14284,0x114a2284a3f09284a094,0x2309a3f141c3c48d2208,0xc268fc50a01d8724a84a,0x7a2309a3d271c21a2187,0x84a3f09c50a41c2404a8,0xe8fa3b0926f142012a21,0x3b092749bc5062942561,0x61d14a3e8ec269b248f2,0xba3f09a3b14203c48d22,0x8ee21091189294372749,0xb14294509422e3c16453,0x1188c258fc5076230963,0x63d8ea1190c508a1c92a,0xf63b0927714230089687,0x8fa118ec24c29425a118,0x2ea951a4652e09514a1d,0x24461d8fc258ec50a514,0x676271512e3c27e3b88c],#[0x7a3e8ec2445258f63b09,0x8ec242e24300bc2ee1c2,0x58e2c490d835e1187a3e,0xf840cc320aa1462046c2,0x284962309638461047a1,0x88e22e12141198863f09,0x9118704988c258f1185,0x5840f0a2878f09f8ee23,0xc23088a10538fe3b88c2,0xd8350ba1463c46c258e2,0x63f09638461c49a1f840,0x882446c3e21202308814,0x82c3f090848610220530,0xf090851e20a528d84c22,0x8f09884708e8261308c3,0xc3f090ec707984c230f2,0xf82422c38947b8408708,0x1a864708f84864460530,0x70e28c961e0f83984c26,0x64ae1022050464670f42,0x8ca528f0fc3b0961282c,0x6130fc3b0928f1918250,0xde101a4650f43b090d88,0x350bb84c3f0ec2436281,0xb0fc3b090d491243ca08,0x268e0c88124360bb8460,0xa3832212307046a2182c,0x1c24a48d8445046a2309,0x488c2247a826204663c2,0x8f20822e3b88c2446282,0x98f63b090d4a0942105b,0x384616230881de1046a0],#[0x6218fc25212423623096,0x8c2446262308846e1214,0x3c26214878f21282e3b8,0x2324b8f0538ee2309610,0xa23e121463d8e6422220,0x77840898fc2614638991,0x1198f63b090d4808c464,0x463f09638461a23a1214,0x84a228fc25820f4908c1,0xf08c270e11880902107b,0x258e2971424a528c98c4,0x2971424310d09c25d88c,0x72041290a028588c258f,0x92949d26d8f63b09c50b,0xa347898c2309c3e21118,0xc98c3f0ec27191188294,0xc82a62309638461ca528,0x851216230963c4628330,0xfc258e11870f6238889f,0xd8350b98]]
set_option maxRecDepth 16000 in
def g255H11 := limbs80 #[#[0x583817e581800200f0e,0xb81000030004003800,0x10600205040479302,0x1000614b040400e87040,0x700049000c00d040000,0x808047030054d802e084,0x23c3821c08004000000,0x40870e502802808100,0x34102040408432504841,0x848804ac6031c783020e,0x80024045881425021001,0xd145420300480bb3e01,0x50e05d86041c0b206043,0x224982000028a140068,0xca820d022819a101538f,0x509160004f8fb2000010,0x1031a181096a000870e,0x601021ee021000087162,0xb020801a300160a0238,0x10b46c09141c20e1a003,0x458d5187f44177849f0,0x50b82a0d000078cf48,0x31800058df69cc6b2980,0xa9c19080b91037000042,0xdc3acb723daba8800000,0xa000001886f242800000,0x1825001e72413b4b21,0x4aa248d13475309280,0x2b205fa915a090000000,0xd7000000000000000002,0x76800000000000000011,0x37071939c5112000074],#[0x407b70646054f00cf0,0xb6000048418000000000,0x83c814000018de000038,0x22088000028ad33a2d8,0x918000000050c1800028,0xa1380000b4d59,0x1ca02ff4ce80007c8c00,0x5069c06df0,0x92a80,0x2148c072a958e0800000,0x2c68da008c48c5125bac,0x28b8962067f81ad415c8,0xaa356433eaa3794ccea,0x9100001c326064800060,0x2a80007baa000060934b,0x78bc2a3294cd00002b,0x53748b80000000000000,0x7b4c486eaa,0x7d8000120a0000000000,0x960274000000002028a8,0x783033ea94800042c792,0x16619b985bd8df98227c,0x23885e00000000409ba9,0x530000339d8000592b10,0x8550be8000300fec8463,0xd3d82d80000000000020,0x129b3389cae27dd07618,0xa008d5c9a1b146dad631,0xd430a7eb3c089d800000,0x9b010f68162040182f68,0x6e089560cd717d000059,0x2a717f4898eb547970a0],#[0x99a8bda075491b000050,0x483e8a8600007ad523,0x8ca540002178c8588880,0x3ccb00001851e1,0x18700498da8780,0x320000000040b6a09f00,0x4b59b2088000603e01,0x7103087800,0x7891eb340000713a00,0x9020ac9e0c900,0x4acb800000,0x1a282743314c8d9c9f80,0x6011d578798000123480,0x521c88f08ef898000020,0xddb01900000822a32690,0x78e028877c8a88,0x1f0000484c18be20b380,0x4936000010db000070,0x4b50f00b1516401800,0x87c84e006a918a800000,0x6b885d20863cce20d6a1,0x69391700000000309d58,0x30aea02bf90570,0x37b820000000003b4380,0xaf9b048000580d423fac,0x17b06c68ac1a068a6fa0,0x4842c6e837a041247660,0x947327b241a042d19ec8,0xa88000582e381fe238e2,0x95786d00003092105a32,0x131157181bd045619a71,0x9080510000203d80b328],#[0x659824d00a1b05322852,0xc77a929a48c90d6089e0,0x554967708f7aaa389b00,0x958b0c4cae172d8b9b8,0x2ddd196c18581b480782,0x839afd0b44075b885b9,0x5020cec88df0e168a432,0x8a5a7c28a1c219dbac08,0x26e9704aab2296c28e68,0xb2480578a2482ca1460a,0x3751d4eba98b90a391b8,0x4dd194c8c58956000012,0x74408239484c41500288,0x2a9243b465285f004378,0xbca0af19c3c029d03d7a,0xdd09a158c68000405410,0xcb518500000000603b98,0x319641958000124490,0x1b800039d5f08b63a300,0x2c208b80006a2fc9d39a,0x4770717033118b44cc12,0x8d9b12a936a38406c80,0x118a3d1caa8894292770,0xa523021890c8011c8828,0x771850c489b408985920,0x738000580380003a07f4,0x4cb8828000000008c8a8,0x4a2ed07a800043,0x2a3300000000000000,0x7240a29240907d40aa80,0xe00000000105e88a80a,0xd0eb4a31c6a32b6178e2],#[0x125a2b80002baeb90a88,0xb53935b9580000226e0a,0x842800320ca8231a3638,0x2d0000384d405b283ca8,0x6080001475800044c931,0x4f210f93ab622f207900,0x18b8800020ae000048,0x2de09c181c0000323f00,0x63006f800023a9000022,0x63a1c9b3ab88a718,0x420000411c8000792b80,0x558000000000006a3551,0x19eaa9a0c600000a1581,0x5013a827e2a7007718,0x235500000000000000,0x918c7a92ca0a5800000,0x7945d16a8b01f8a3c0,0x723b0300007829210a00,0x5c292a22a1588e13ad8c,0x60cc485868,0x4f0000532d20dba0b000,0x2d20ba38075005800011,0x6096d093d8810b5480,0x7a859812e0c080,0x30000297de33d824400,0x3c20f03ff8a680007a,0x3fd8bf2099f183800000,0xc73091500bea16000013,0x6832b80e8000000031,0x396a0480000000241f80,0x609cd184027772,0x56741f00006c38792880],#[0x4204105d80000c13b8,0x74e06a00000000081d80,0x1a3433528000203044,0x28380000117c526500,0xa11b9f3b9c8000222e00,0x48488026324238,0x3a88a92b9e0061e0dc80,0x2e0484987358bb3b592a,0xccb21198bffa926825d9,0x3047b0833859aa0720,0x29580000000000000,0x97d8654044984b800000,0x9a8b3b60c38000481d49,0xae3a03c0a6309f800040,0x800ba4588d586118c41b,0x14b32e00000000481270,0xba920519695836793719,0xbb80002903a00673a7b0,0x3c45423c8a35800028,0x28000058d60000700980,0x4077c043e053f02429,0x36ec1e00000828700080,0x9824708b70000000029,0x520d922c807ef86f61,0x3500007b9d2874a12680,0x9e8000310e0000000028,0x60d918acfa18e0,0x6c44f09a00,0x34929e00000000110900,0x49732700004a67800051,0x1c5b80000000531959,0x5105807c80],#[0x42c94040fa1b00,0x529c178000587b9a3680,0x77c0d798d2312e800008,0x68d2b227100e2b4f4c,0x997a6d39ca0947000000,0x4180003c38b0d0013459,0x81929800058bd697bbb,0x7200006329001ec880f8,0x423b80001a54000069,0x0,0x3f00004a2a0000000000,0x570000303940b4a82b60,0x704e800000003a91f0,0x791c50684a9120c280,0x158000033f3ace800000,0x1128cf8000000048b7b8,0x1558340000000000a4a8,0x79865881b16e50,0x1d046d88cd884a91400,0x73d487c078d006d057b1,0x58827853ad5239800062,0x95800043b30000000048,0x2b91794aa45031404fc0,0x42532eea971b2dd004c3,0x27987289aaa0d3220b1b,0x5ad04ab04448a88a6d89,0x8904c9807e58b1000010,0x2a000029a0800000006c,0xdee83c0894800010aa73,0xca00004a2d207c782ab0,0x16d08fc34bf991084b00,0x7ec86762cf796880c118],#[0xd80000000000005a02d1,0xd28000483588cb800030,0xc50001b9cfe0ab30627a,0x2680001a93b942800021,0x28bb4d80006198685cf8,0x66727ce01050893087c3,0x31c90000000048,0x6042004a60ad800000,0xdd0c200000000000000,0xc4800050d89931800021,0x3158ab80005a29389928,0x13a03200005c446a3042,0xb58000134e587fb866d1,0x11b11bf845b2169b53b8,0x316e923e984c800029,0xd70834f0dad29dd83680,0x2c30000000058a310,0x49800040b1c416616d80,0x6a4000000000114063,0x3a000de442f0b2800000,0x1bb2b2641ccdc97e60,0x1770d1c0722bac93a700,0xaaa2a2800000004068d8,0x4897fc8a4340e03aa2,0x58d020d0318000007a00,0xccb8ce7303ea9f026f4a,0x7131000000003a2991,0xd26c8e12326055800000,0x3b634ae02ef947f32849,0x18c021ea33fb4f800040,0x586280004a1a785360,0x798c38c33ba480],#[0x197209c046000068cd80,0x3080002070bc40391301,0x6da049409e08a0b227a8,0xd4e94330caba83b0d98c,0x180000527304cf405698,0x6b42957876d8389b350a,0x39a3588014d1c2c904a8,0x68c9880c3c9ac08a90,0x2ca89700000000280f00,0x12d40b]]
def g255D12 := limbs80 #[#[0x5c110e7d765979f59560,0x443fd5c510ff521443fe,0xff940482ff61d10bfd82,0x60d20ff970483fe58120,0x483df59520bfd84482ff,0xff9704c2ff61d20bfd86,0x5cd30bff824c3f74c930,0x582ffe1d30bfd874c3f7,0xefd76583bf58960ff970,0x5c970bff815c2ff61d60,0x5c2ffe0d70bff825c37f,0xbff865c37f5d970f7d65,0x5c910ffd42442ffe0173,0x483ff50d20ffd71483ff,0xffd74483ff59120ffd73,0x5c960ffd724c3ff5d920,0x5c3ff60970ffd815c3ff,0x28114003ff61970ffd83,0x89548406e45884743602,0x1dd05cf00dc8cb4bc4a6,0x6983171d6094f53e1315,0x204df15dddcedb91a7d9,0x7fe6a258e49e3ae29a16,0x86f4ee5ecdebeea6e8ee,0xc1c191f61b4bf33f1e30,0x78383a3e1f09820803,0x4d0f0804c388c260b001,0x13040382b091f0982110,0x608260807424383e1f08,0x62ac3e10290884c389c2,0x9613041c844261c48542,0xf8ec40242c141c44131],#[0xc3e111e8e04850323e3f,0x71f841163b1087048509,0x4e3812048847c2442308,0x4845080963f0f8ec4424,0xd1d09260187c223d1d88,0x884941a0c8bb0f840a23,0x231163c2584c721c298,0x281c4584c1026110f109,0x43e121e1d040807c2442,0xe080784a123e1f088284,0x121e101284c3c7c26090,0x98284c221e210f0f84c,0xc2608448787c38121923,0xc8f87c203c1d090d0647,0x1d092709820783a121d0,0x110c220c8d709820ec3e,0xb1082849184c1222128e,0x2c442444463c4622c263,0x491109478e12c7e131c8,0x747a3a0090230982838,0x891e8e8487479161305,0xd84c123e128e110d84c1,0x98898f84c14221e89120,0x4261d13250587844261c,0xd144e0ca311e110f0841,0x2222128f8a1584444251,0x128f8a14a04908025874,0x4d8ca449090258443a22,0x109098a158747a3a1314,0x44e8c2510e3d4b8e43e2,0x221f0910918447a3a131,0xe84a0a324a8c3d84414],#[0x4251c32254623c221e1f,0x1091114220e04f098244,0x1138f11887098e230531,0x91207b0982444251e211,0x883a19c26091e8e848d4]]
set_option maxRecDepth 16000 in
def g255H12 := limbs80 #[#[0x2008c0208c0200842,0x3000050c2000003004a2,0x11511200000042009004,0x80c001064b800310565,0x840088e40844200000,0x5200000c0311c0008020,0xa4b8819502fc,0x560a800012dbe62f8000,0x31b,0xd438a284000000090160,0x80000000000254e9896,0xe2fd0a5c82,0x1a2b00000b7a00000,0xe468000,0x876826e000000,0xf0e0000391c800000000,0x1150b05a0000c090000,0x1d40000c960000000000,0x5136087ac288000d0496,0x0,0x0,0x60060000000089f00000,0x40b920a80000000,0x31b88b1fe65a000000,0x10800000000000000000,0xc51a3b0ca00000000000,0x8708a0000d03ba86202,0x69900000000d4888,0x9216000094e596c,0xe800000003440000000,0x228d2,0x1229c0006c08],#[0x0,0x1823c000000000000,0x62a0000,0x4a800000000000c59c00,0x8688122e9130001c,0x94a1600012c600005242,0x1412e90ec3,0xe0a600011bb800000000,0x1141,0x54800000000000000000,0x20af405000000014,0x2444000000000000000,0x4ebc9f00000000000000,0x70080000e,0x8000000000000000000,0x1430725f0000000280,0x4073224158d000000000,0x885f0f000000002115,0x244e80000000e4a000,0xa1cc00028a4a6dc0,0x3263503c0000000701a,0x19a001280f0000000000,0x364fd10f50df12306f0e,0x500000000000083a411c,0x11c00068579654826690,0xb5888c00000000001a,0x4836013400014230000,0x0,0x249560b091e8000210c0,0x684ef28a0002c2c8000,0x0,0x20d00000000000029560],#[0x6050,0x2091729b0000000000,0x0,0x20000000000031350000,0x1a40003222c338000208,0x86e569e6c190000205e8,0xc03e00000007ba9,0xd92a000000,0x709a0de40004013604c0,0xa8000024a02440000000,0xa51ba1880401a000010,0x60896dd4000108950792,0x680000000a2280000000,0x2018719b0000000203,0x34411445c3180,0x6442,0x48fe12,0x0,0x113822a80000000,0x24ab51400001c54c00,0x110e800000000,0x6f792518c968a0,0x46000000430000e15800,0x80ee00018249c5e0001a,0x20000470000000006011,0xcc0000000205c000009,0x184f40000000042e2,0x46fa53800011a6,0x0,0xe150000000000000,0x188ee095e67f02aa815,0x5980006a0c0000000000],#[0x81480000000f28e0,0x1b17000040800000000,0x1b0000283d6242000000,0x16474000000000010,0x145c000000000000000,0x1baa0000c42800,0x8060000e12a0,0x3a2d394d,0x60a50000000000,0x1d03800000000,0x7000980e200000000000,0xfb9d4288d000041f545,0xc37119d54342,0x37a02d12e00019328000,0xc5001a18670000f15f93,0x5330e,0x291fb10800025b40000,0x4a0b0000000000,0x10300,0x3864000000034ccd898,0x1f000050ab304e000000,0xd25b8,0xc886f000000000000000,0xca0d2400000001e053c3,0x3a5b72c5a,0x60ba0000000505e,0x815fa89000,0x0,0x33480002c518000,0x140e0000b047a05800,0x1821000000000,0x9703790fecdf41bb0000],#[0xa4fd8a80000000000204,0xe,0x1e4340003a19,0x0,0x1ac0007131e3340,0x5cac000000014880000,0x1020400,0x28a2b0d40,0xd505bf288a0880000000,0xdf260d8000000080c648,0xa15220d4000718e00000,0x18000b27200034860000,0x525fc03a04,0x506300000,0x10000000000000000000,0x820000000000002dc34a,0x1c03800000006,0xc8000d04a00000000000,0xdfcd0a185f9287e52662,0x81eb8c8cc0700010,0x522e0000000083f,0x65380000000c56000,0x204800000,0x18b0c4c00000000,0xc200000000000,0x72940000444000000000,0x4006a2046a64000391e,0x829800,0x0,0x68000313c00000000000,0x18800070ad7071c12ce0,0xe21d8],#[0x216b000161300000000,0x13fcae8000000020ec00,0x141a0002c84812e00014,0x0,0x413f0001455400,0x200a0000000000000000,0x3c3d000000000000000,0x18400000000000000000,0x2814126800014,0x316930fc8013043c88b,0x140d80000000000000,0x0,0x78000000000014498000,0x501052700000e4,0x14228000c43e0,0xa0000000000000000000,0x688c00000001c4,0x303dca9628b60]]
def g255D13 := limbs80 #[#[0xffa41ff443bf32f7d65,0x73ffae3ff5c3feb07fd3,0x3c0b21d03e003febb7fd,0x100f0e1e467e1ba5d136,0x42c28241830687848280,0x50787848209080e131c3,0x8090f223e1e123a2024,0x83c38246471e12878482,0x284828e078809221e120,0x26120a002820387078f2,0x472412848280070c080f,0x2120a00403c387]]
def g255H13 := limbs80 #[#[0xa1e2810bc00870001188,0x40100120c19b22281830,0x3e2481400be18d6a000,0x740498bcd3ce500000,0x2807c0b14c1890c240,0x64a8800c2db088,0x3ba300be01000239c000,0x8020d2dfc88026887d25,0x8d94e6913686c85,0x98410810b06750dc2a00,0x44800204b8e3b905aaa1,0xc0d822954e48400180e8,0xe0d739000184e1288a7a,0xa82a209489d9a8001688,0xa702324e43c000000124,0xa3cca81d92b687f8a120,0xf801000390880d21480,0x127a3d89d68b8002cb5c,0x20c626a88c85ce080004,0x3c0260c0007340002d44,0xf01654bc07389000058c,0x5b28263a304213e90d40,0x1818422c130000b2901]]
def g255D14 := limbs80 #[#[0x3c60a223868b1220aff,0x2]]
def g255H14 := limbs80 #[#[0x180000000240a226d160,0x8498a90949f02100a1d8,0x689c15030a598d825d30,0x1091c4233]]
def g255L : Nat → Packing
  | 6 => (1,8,7,0,0,0,0,g255D6)
  | 7 => (19,7,7,0,0,9,0,g255D7)
  | 8 => (175,6,7,0,0,14,0,g255D8)
  | 9 => (471,5,7,0,0,16,0,g255D9)
  | 10 => (451,4,7,0,0,16,0,g255D10)
  | 11 => (176,3,7,0,0,14,0,g255D11)
  | 12 => (47,2,7,0,0,12,0,g255D12)
  | 13 => (10,1,7,0,0,10,0,g255D13)
  | 14 => (1,0,7,0,0,0,0,g255D14)
  | _ => emptyPacking
def g255I : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 1 2 0 4 0 0 g255H7
  | 8 => lookupWord 7 47 4 11 5 2 g255H8
  | 9 => lookupWord 104 1543 3 15 8 3 g255H9
  | 10 => lookupWord 269 5501 3 16 9 3 g255H10
  | 11 => lookupWord 225 1229 7 16 9 3 g255H11
  | 12 => lookupWord 91 919 5 15 8 3 g255H12
  | 13 => lookupWord 26 127 7 13 6 3 g255H13
  | 14 => lookupWord 5 23 4 11 4 3 g255H14
  | _ => fun _ => none
def g255 : Forest := ⟨255,14,fun i => g255Y[i]?.getD (0,0),g255C,g255A,g255L,g255I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P6_0 : block g255 6 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B6 : block g255 6 0 1=true := g255P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P7_0 : block g255 7 0 19=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B7 : block g255 7 0 19=true := g255P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P8_0 : block g255 8 0 23=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P8_23 : block g255 8 23 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P8_119 : block g255 8 119 13=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P8_132 : block g255 8 132 43=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B8 : block g255 8 0 175=true := (@block_merge g255 8 0 119 56 (@block_merge g255 8 0 23 96 g255P8_0 g255P8_23) (@block_merge g255 8 119 13 43 g255P8_119 g255P8_132))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_0 : block g255 9 0 3=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_3 : block g255 9 3 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_99 : block g255 9 99 41=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_140 : block g255 9 140 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_236 : block g255 9 236 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_332 : block g255 9 332 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_428 : block g255 9 428 14=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_442 : block g255 9 442 29=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B9 : block g255 9 0 471=true := (@block_merge g255 9 0 236 235 (@block_merge g255 9 0 99 137 (@block_merge g255 9 0 3 96 g255P9_0 g255P9_3) (@block_merge g255 9 99 41 96 g255P9_99 g255P9_140)) (@block_merge g255 9 236 192 43 (@block_merge g255 9 236 96 96 g255P9_236 g255P9_332) (@block_merge g255 9 428 14 29 g255P9_428 g255P9_442)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_0 : block g255 10 0 43=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_43 : block g255 10 43 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_139 : block g255 10 139 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_235 : block g255 10 235 28=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_263 : block g255 10 263 96=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_359 : block g255 10 359 86=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_445 : block g255 10 445 6=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B10 : block g255 10 0 451=true := (@block_merge g255 10 0 235 216 (@block_merge g255 10 0 43 192 g255P10_0 (@block_merge g255 10 43 96 96 g255P10_43 g255P10_139)) (@block_merge g255 10 235 124 92 (@block_merge g255 10 235 28 96 g255P10_235 g255P10_263) (@block_merge g255 10 359 86 6 g255P10_359 g255P10_445)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P11_0 : block g255 11 0 9=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P11_9 : block g255 11 9 75=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P11_84 : block g255 11 84 83=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P11_167 : block g255 11 167 9=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B11 : block g255 11 0 176=true := (@block_merge g255 11 0 84 92 (@block_merge g255 11 0 9 75 g255P11_0 g255P11_9) (@block_merge g255 11 84 83 9 g255P11_84 g255P11_167))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P12_0 : block g255 12 0 2=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P12_2 : block g255 12 2 31=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P12_33 : block g255 12 33 14=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B12 : block g255 12 0 47=true := (@block_merge g255 12 0 2 45 g255P12_0 (@block_merge g255 12 2 31 14 g255P12_2 g255P12_33))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P13_0 : block g255 13 0 2=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P13_2 : block g255 13 2 8=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B13 : block g255 13 0 10=true := (@block_merge g255 13 0 2 8 g255P13_0 g255P13_2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P14_0 : block g255 14 0 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B14 : block g255 14 0 1=true := g255P14_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255T : checkedTables g255 14 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g255 0 0 0 = true)
  · exact (rfl : block g255 1 0 0 = true)
  · exact (rfl : block g255 2 0 0 = true)
  · exact (rfl : block g255 3 0 0 = true)
  · exact (rfl : block g255 4 0 0 = true)
  · exact (rfl : block g255 5 0 0 = true)
  · exact g255B6
  · exact g255B7
  · exact g255B8
  · exact g255B9
  · exact g255B10
  · exact g255B11
  · exact g255B12
  · exact g255B13
  · exact g255B14
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255G : graphValid g255 (boundsBefore K253) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255R : Impossible true graph 14 sevenInputs.toFinset := by
  rw [show graph = targetOf g255 by decide +kernel]
  exact root_index (g:=g255) (top:=14) (i:=0) (before_sound K253 V253) g255G g255T (by decide) (by decide +kernel)

end PEqualNP.Outside.L_meta_52328

open PEqualNP.Outside.L_meta_52328 in
theorem PEqualNP.Outside.L_meta_52328 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o fit _ correct
  exact replaceShort g255R gates o fit correct

import PEqualNP.Defs

-- The two-mode live-state and cofactor checker follows L_meta_1674 and L_meta_670.
-- The graph, restrictions and all search certificates below are for L_meta_52586.

-- Shared forest and cofactor certificates from L_meta_1674 and PR 11111 for L_meta_1677.
-- The original credit line is retained below. The two root certificates here cover the unpinned graph.

-- The checker and the bound certificates are adapted from PEqualNP/Outside/L_meta_1667.lean (Apache-2.0).
-- Two modes: u=false are monotone runs (AND, OR); u=true are runs up to complement, where negation is free.
namespace PEqualNP.Outside.L_meta_52586
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
def graph : Sig := (BitVec.ofNat 512 (word80 [0xffffffff,0xffffffffffffffffffff,0xffeefffffffefffffffe,0xfefefefcfefaee00ffff,0xffffffffffffffffffff,0xffffffeefffffffeffff,0xfffefefefefcfefaee00]))
def sample (r : Row) (j : Fin 9) := bit r (inputs.getD j.val zero)
def edge (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 3) || (x 1 && x 3) || (x 0 && x 4) || (x 2 && x 4) || (x 1 && x 5) || (x 2 && x 5) || (x 0 && x 6) || (x 1 && x 6) || (x 2 && x 6) || (x 3 && x 6) || (x 4 && x 6) || (x 0 && x 7) || (x 1 && x 7) || (x 3 && x 7) || (x 4 && x 7) || (x 5 && x 7) || (x 6 && x 7)
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
  (x 0 &&& x 3) ||| (x 1 &&& x 3) ||| (x 0 &&& x 4) ||| (x 2 &&& x 4) ||| (x 1 &&& x 5) ||| (x 2 &&& x 5) ||| (x 0 &&& x 6) ||| (x 1 &&& x 6) ||| (x 2 &&& x 6) ||| (x 3 &&& x 6) ||| (x 4 &&& x 6) ||| (x 0 &&& x 7) ||| (x 1 &&& x 7) ||| (x 3 &&& x 7) ||| (x 4 &&& x 7) ||| (x 5 &&& x 7) ||| (x 6 &&& x 7)
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


structure QuotientSpec where
  a : Nat
  b : Nat
  rev : Bool
  z : Nat
  o : Nat
  extra : Nat
  fl : Nat
  sw : List Nat
  single : Nat

def quotSpec : Nat → QuotientSpec
  | 0 => ⟨1,4,false,64,0,0,0,[113, 114, 67],0⟩
  | 1 => ⟨2,3,false,64,0,0,0,[114],0⟩
  | 2 => ⟨1,6,true,32,0,0,2,[48, 80, 98, 116],1⟩
  | 3 => ⟨1,6,true,33,0,0,2,[48, 65, 98, 116],1⟩
  | 4 => ⟨1,6,true,36,0,0,2,[48, 64, 97, 116],1⟩
  | 5 => ⟨3,6,true,3,0,0,8,[114, 67, 100],0⟩
  | 6 => ⟨0,5,false,10,0,0,0,[66, 100, 118],0⟩
  | 7 => ⟨1,6,true,40,0,0,2,[80, 98, 116],0⟩
  | 8 => ⟨3,6,true,2,0,0,8,[114, 67, 100],1⟩
  | 9 => ⟨3,6,true,1,0,0,8,[16, 114, 67, 100],1⟩
  | 10 => ⟨3,6,true,0,0,0,8,[114, 67, 100],3⟩
  | 11 => ⟨2,6,true,34,0,0,4,[64, 98, 115],1⟩
  | 12 => ⟨1,4,false,65,0,0,0,[113, 66, 83, 101],0⟩
  | 13 => ⟨1,4,false,8,0,0,0,[64, 113, 114],0⟩
  | 14 => ⟨5,6,false,0,0,0,0,[48, 65, 82, 117],0⟩
  | 15 => ⟨2,6,true,32,0,0,4,[64, 80, 97, 98, 115],1⟩
  | 16 => ⟨1,4,false,0,0,0,0,[113, 114, 67],0⟩
  | 17 => ⟨1,4,false,72,0,0,0,[80, 113, 66, 101],0⟩
  | 18 => ⟨4,6,true,5,0,0,16,[113, 67, 100],0⟩
  | 19 => ⟨0,5,false,64,0,0,0,[112, 113, 114, 67, 84],0⟩
  | 20 => ⟨2,6,true,48,0,0,4,[80, 97, 98, 115],0⟩
  | 21 => ⟨2,3,false,80,0,0,0,[80, 65, 114, 101],0⟩
  | 22 => ⟨1,4,false,4,0,0,0,[113, 67],0⟩
  | 23 => ⟨1,4,false,9,0,0,0,[114],0⟩
  | 24 => ⟨2,3,false,2,0,0,0,[114],0⟩
  | 25 => ⟨2,6,true,33,0,0,4,[64, 16, 98, 115],1⟩
  | 26 => ⟨1,4,false,5,0,0,0,[113, 67],0⟩
  | 27 => ⟨4,6,true,0,0,0,16,[33, 113, 67, 100],3⟩
  | 28 => ⟨1,4,false,68,0,0,0,[64, 113, 99],0⟩
  | 29 => ⟨2,3,false,0,0,0,0,[114],0⟩
  | 30 => ⟨2,3,false,17,0,0,0,[114],0⟩
  | 31 => ⟨4,6,true,4,0,0,16,[113, 67, 100],1⟩
  | 32 => ⟨4,6,true,1,0,0,16,[32, 113, 67, 100],1⟩
  | 33 => ⟨2,3,false,3,0,0,0,[114],0⟩
  | 34 => ⟨2,3,false,66,0,0,0,[64, 114, 100],0⟩
  | 35 => ⟨2,3,false,16,0,0,0,[64, 114],0⟩
  | 36 => ⟨2,3,false,65,0,0,0,[65, 114, 84, 101],0⟩
  | 37 => ⟨0,5,false,72,0,0,0,[112, 81, 66, 100],0⟩
  | 38 => ⟨0,5,false,20,0,0,0,[65, 99, 118],0⟩
  | _ => ⟨0,0,false,0,0,0,0,[],0⟩

def quotDom (b : QuotientSpec) : Sig :=
  let d := (inputs.getD b.a zero) ^^^ (inputs.getD b.b zero)
  subcube b.z b.o &&& (if b.rev then d else ~~~d)

def quotSteps (b : QuotientSpec) : List Move :=
  let a := inputs.getD b.a zero
  let dest := inputs.getD b.b zero
  let want := if b.rev then ~~~a else a
  let move : Move := (want &&& ~~~dest, dest &&& ~~~want, Fin.ofNat 512 (1 <<< b.b))
  let flips := (List.range 9).filterMap fun i =>
    let w := inputs.getD i zero
    if b.fl.testBit i then some ((~~~w, w, Fin.ofNat 512 (1 <<< i)) : Move) else none
  b.sw.map swapRows ++ flips ++ fixRows (b.z ||| b.extra) b.o ++ [move]

def phaseFree (roots : List Sig) (w : Sig) := freeWord roots w || roots.contains (neg w)

theorem phaseFree_ok {xs w} (h : phaseFree xs w = true) :
    Available true (xs.map observe) (observe w) := by
  simp only [phaseFree,Bool.or_eq_true,List.contains_eq_mem,decide_eq_true_eq] at h
  rcases h with h | h
  · exact freeWord_ok h
  · refine Or.inr (Or.inr ⟨rfl, ?_⟩)
    rw [← obs_neg]
    exact List.mem_map_of_mem h

def signedMap (ms : List Move) (raw : List Sig) (base : List Sig) :=
  raw.all (fun a => phaseFree base (movedWord ms a))

theorem signedSlice {ms raw T base d L} (h : signedMap ms raw base = true)
    (all : movedWord ms d = one) (pr : proper (movedWord ms T))
    (low : Lower true base (movedWord ms T) L) : Slice true raw T d L := by
  have he : restrictRows (movedRow ms) (observe T) = observe (movedWord ms T) := by
    rw [moved_eq_rename, observe_rename]
  refine ⟨movedRow ms,base,?_,?_,?_,?_⟩
  · intro r
    rw [← bit_moved, all, bit_one]
  · intro a ha
    rw [← observe_rename, ← moved_eq_rename]
    exact phaseFree_ok (List.all_eq_true.mp h a ha)
  · rw [he]
    exact observe_proper pr
  · rw [he]
    exact low

def quotientCheck (u : Bool) (raw : List Sig) (T : Sig) (b : QuotientSpec) (q L P : Nat) : Bool :=
  let ms := quotSteps b
  let G := movedWord ms T
  let bs := varsX (q ||| b.single)
  let xs := supportPairs 0 b.single
  u && signedMap ms raw bs && (movedWord ms (quotDom b) == one) &&
    properB G && properB (graphGoal q) &&
    checkLift (fixRows b.single 0) G bs (varsX q) (graphGoal q) xs &&
    decide (L ≤ P+(xs.map Prod.fst).toFinset.card)

theorem quotientSound {u raw T b q L P}
    (low : Lower u (varsX q) (graphGoal q) P)
    (ok : quotientCheck u raw T b q L P = true) : Slice u raw T (quotDom b) L := by
  simp only [quotientCheck,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at ok
  obtain ⟨⟨⟨⟨⟨⟨hu,hm⟩,hd⟩,pg⟩,pq⟩,lift⟩,hle⟩ := ok
  subst u
  apply signedSlice hm hd (proper_of _ pg)
  intro p bank reach hit
  exact hle.trans (lift_ok lift (proper_of _ pg) (proper_of _ pq) low p bank reach hit)

def fieldDomain (z o : Nat) : Sig :=
  if o < 512 then subcube z o else quotDom (quotSpec (o-512))

def fieldCheck (u : Bool) (m : Nat) (c : ColumnInfo) (prior : Nat → Nat) : Bool :=
  if c.2.1 < 512 then colCheck m c prior else
    let q := c.2.2.1
    quotientCheck u (varsX (rawMask m c)) (chartGoal m) (quotSpec (c.2.1-512)) q c.2.2.2.2 (prior q)

theorem fieldSound {u m} (c : ColumnInfo) (prior : Nat → Nat)
    (low : ∀ q, Lower u (varsX q) (graphGoal q) (prior q))
    (ok : fieldCheck u m c prior = true) :
    Slice u (varsX (rawMask m c)) (chartGoal m) (fieldDomain c.1 c.2.1) c.2.2.2.2 := by
  by_cases h : c.2.1 < 512
  · simpa only [fieldDomain, h, if_true] using
      col_sound c prior low (by simpa only [fieldCheck, h, if_true] using ok)
  · simpa only [fieldDomain, h, if_false] using
      (quotientSound (low c.2.2.1) (by simpa only [fieldCheck, h, if_false] using ok) :
        Slice u (varsX (rawMask m c)) (chartGoal m) (quotDom (quotSpec (c.2.1-512))) c.2.2.2.2)

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
  (x 0 &&& x 3) ||| (x 1 &&& x 3) ||| (x 0 &&& x 4) ||| (x 2 &&& x 4) ||| (x 1 &&& x 5) ||| (x 2 &&& x 5) ||| (x 0 &&& x 6) ||| (x 1 &&& x 6) ||| (x 2 &&& x 6) ||| (x 3 &&& x 6) ||| (x 4 &&& x 6) ||| (x 0 &&& x 7) ||| (x 1 &&& x 7) ||| (x 3 &&& x 7) ||| (x 4 &&& x 7) ||| (x 5 &&& x 7) ||| (x 6 &&& x 7)
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
    materialize g.mode (varsX (rawMask g.mask ci)) (chosenSteps bank ops paid d) (fieldDomain ci.1 ci.2.1) ci.2.2.2.2

theorem buildRule_sound (g : Forest)
    (cols : ∀ ci ∈ g.cols, Slice g.mode (varsX (rawMask g.mask ci)) (targetOf g) (fieldDomain ci.1 ci.2.1) ci.2.2.2.2)
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
    (cols : ∀ ci ∈ g.cols, Slice g.mode (varsX (rawMask g.mask ci)) (targetOf g) (fieldDomain ci.1 ci.2.1) ci.2.2.2.2)
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
  g.cols.all (fun c => fieldCheck g.mode g.mask c prior) &&
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
      (fun x hx => fieldSound _ prior lower (geometry.1.2 x hx)) geometry.2 (by omega)
    exact block_at (rows 0 hk) i (by omega) (by omega)
  | succ k ih =>
    intro hk i hi
    apply nodeVerified_sound g _ i (chart_pairs geometry.1.1.1 geometry.1.1.2)
      (fun x hx => fieldSound _ prior lower (geometry.1.2 x hx)) geometry.2
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
    (ok : fieldCheck u m ci prior = true)
    (cut : (decide ws.Nodup && poolCut u (fieldDomain ci.1 ci.2.1) ci.2.2.2.2 cap 0 (varsX (rawMask m ci)) ws)=true) :
    Impossible u (graphGoal m) cap ws.toFinset := by
  simp only [Bool.and_eq_true,decide_eq_true_eq] at cut
  exact poolCut_sound (fieldSound ci prior low ok) [] rfl cut.1 cut.2

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



def target (x : Fin 8 → Bool) : Bool := decide (∃ i < ([0, 3, 1, 3, 0, 4, 2, 4, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)
def smallCircuit : Circuit := ⟨[⟨.or,[7,6]⟩,⟨.or,[2,7]⟩,⟨.or,[6,4]⟩,⟨.or,[1,0]⟩,⟨.or,[11,4]⟩,⟨.or,[0,9]⟩,⟨.or,[3,12]⟩,⟨.and,[3,11]⟩,⟨.and,[8,14]⟩,⟨.or,[1,9]⟩,⟨.and,[17,5]⟩,⟨.and,[10,13]⟩,⟨.or,[18,19]⟩,⟨.or,[16,20]⟩,⟨.or,[21,15]⟩], 22⟩

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

def lowRow (i : Fin 8) : Row := Fin.ofNat 512 (1 <<< ([3, 3, 4, 0, 0, 1, 0, 0] : List Nat).getD i.val 0)
def highRow (i : Fin 8) : Row := Fin.ofNat 512 ((1 <<< i.val) ||| (1 <<< ([3, 3, 4, 0, 0, 1, 0, 0] : List Nat).getD i.val 0))

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
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low9 : Lower true (varsX 9) (graphGoal 9) 1 := by
  have q := @lower_count true (vars 9) (graphGoal 9) (proper_of _ (by decide +kernel)) (graphPairs 9 3) (by decide +kernel)
  exact q
def K9 := extendKnown [] 1 [(36,[32,16,83,67])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V9 : Known true K9 := extend_ok (m:=9) baseKnown low9 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low11 : Lower true (varsX 11) (graphGoal 11) 2 := by
  have q := @lower_count true (vars 11) (graphGoal 11) (proper_of _ (by decide +kernel)) (graphPairs 11 51) (by decide +kernel)
  exact q
def K11 := extendKnown K9 2 [(52,[64,81,32,50,49]),(100,[80,97,32,50,65])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V11 : Known true K11 := extend_ok (m:=11) V9 low11 (by decide +kernel)
def g73Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x3ff63ff63ff63ff63f,0xf63ff63ff63ff63ff63f])),(BitVec.ofNat 152 (word80 [0x492049204920492049,0x20492049204920492049]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xc7fbc7fbc7fbc7fbc7,0xfbc7fbc7fbc7fbc7fbc7])),(BitVec.ofNat 152 (word80 [0x924092409240924092,0x40924092409240924092]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xf8fdf8fdf8fdf8fdf8,0xfdf8fdf8fdf8fdf8fdf8])),(BitVec.ofNat 152 (word80 [0x248124812481248124,0x81248124812481248124]))),(0x0,0x0),(0x0,0x0)]
def g73C : List ColumnInfo := []
def g73A : List (List Nat) := [[],[99],[48],[48,96],[96,48],[96]]
def g73D3 (j : Nat) := if j=0 then 0x7 else 0
def g73L : Nat → Packing
  | 3 => (1,0,1,0,0,0,0,g73D3)
  | _ => emptyPacking
def g73I (_ _ : Nat) : Option (Nat × Nat) := none
def g73 : Forest := ⟨73,3,fun i => g73Y[i]?.getD (0,0),g73C,g73A,g73L,g73I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g73P3_0 : block g73 3 0 1=true := by
  apply cellsBlock (ar:=3) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g73B3 : block g73 3 0 1=true := g73P3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g73T : checkedTables g73 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g73 0 0 0 = true)
  · exact (rfl : block g73 1 0 0 = true)
  · exact (rfl : block g73 2 0 0 = true)
  · exact g73B3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g73G : graphValid g73 (boundsBefore K11) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low73 : Lower true (varsX 73) (graphGoal 73) 4 := lower_forest (g:=g73) (i:=0) (hints:=3) (before_sound K11 V11) g73G g73T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K73 := extendKnown K11 4 [(73,[]),(74,[16]),(81,[67]),(84,[32,16,67]),(137,[118]),(193,[99,67,84,117]),(200,[48,16,33,98,66,84,117]),(208,[64,16,33,99,83,117])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V73 : Known true K73 := extend_ok (m:=73) V11 low73 (by decide +kernel)
def g27Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xf71fc7ff03fffff8f7,0x1fc7ff03fffff8f71fc7])),(BitVec.ofNat 152 (word80 [0x710490a2850401207,0x10490a28504012071049]))),((BitVec.ofNat 152 (word80 [0xbe838fffc07e3ff0b,0xe838fffc07e3ff0be838])),(BitVec.ofNat 152 (word80 [0x4368db4c3260892043,0x68db4c326089204368db]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xeee63ffffff803ffee,0xe63ffffff803ffeee63f])),(BitVec.ofNat 152 (word80 [0x88724904085124008,0x87249040851240088724]))),((BitVec.ofNat 152 (word80 [0x193dc0fffffffc0019,0x3dc0fffffffc00193dc0])),(BitVec.ofNat 152 (word80 [0x982db6e08306038498,0x2db6e083060384982db6]))),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g27C : List ColumnInfo := []
def g27A : List (List Nat) := [[],[48,65]]
def g27D3 (j : Nat) := if j=0 then 0xf else 0
def g27L : Nat → Packing
  | 3 => (1,0,1,0,0,0,0,g27D3)
  | _ => emptyPacking
def g27I (_ _ : Nat) : Option (Nat × Nat) := none
def g27 : Forest := ⟨27,3,fun i => g27Y[i]?.getD (0,0),g27C,g27A,g27L,g27I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g27P3_0 : block g27 3 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g27B3 : block g27 3 0 1=true := g27P3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g27T : checkedTables g27 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g27 0 0 0 = true)
  · exact (rfl : block g27 1 0 0 = true)
  · exact (rfl : block g27 2 0 0 = true)
  · exact g27B3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g27G : graphValid g27 (boundsBefore K73) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low27 : Lower true (varsX 27) (graphGoal 27) 4 := lower_forest (g:=g27) (i:=0) (hints:=51) (before_sound K73 V73) g27G g27T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K27 := extendKnown K73 4 [(27,[]),(29,[33,67]),(43,[16,84]),(46,[16,32,83,67]),(53,[32,16,67,83]),(54,[32,83]),(99,[16,99,84,67]),(101,[32,16,99,84,67]),(108,[32,49,97,84,65]),(114,[16,64,32,99,82]),(150,[64,32,115,83,101]),(156,[112,33,16,67,81,101])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V27 : Known true K27 := extend_ok (m:=27) V73 low27 (by decide +kernel)
def g75Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfe7d01c7fc0fc7cfe7,0xd01c7fc0fc7cfe7d01c7])),(BitVec.ofNat 152 (word80 [0x51d124928a290a051,0xd124928a290a051d1249]))),((BitVec.ofNat 152 (word80 [0x3f8b8e38fff007f3f8,0xb8e38fff007f3f8b8e38])),(BitVec.ofNat 152 (word80 [0x884b924930c3210884,0xb924930c3210884b9249]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x3fe7703ffffff803fe,0x7703ffffff803fe7703f])),(BitVec.ofNat 152 (word80 [0x100024924104020100,0x2492410402010002492]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xc018ffc0fffffffc01,0x8ffc0fffffffc018ffc0])),(BitVec.ofNat 152 (word80 [0x200049248208040200,0x4924820804020004924]))),(0x0,0x0),(0x0,0x0)]
def g75C : List ColumnInfo := [(1,0,74,0,4)]
def g75A : List (List Nat) := [[],[99],[16],[16,99]]
def g75D4 (j : Nat) := if j=0 then 0x1f else 0
def g75L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,g75D4)
  | _ => emptyPacking
def g75I (_ _ : Nat) : Option (Nat × Nat) := none
def g75 : Forest := ⟨75,4,fun i => g75Y[i]?.getD (0,0),g75C,g75A,g75L,g75I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g75P4_0 : block g75 4 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g75B4 : block g75 4 0 1=true := g75P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g75T : checkedTables g75 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g75 0 0 0 = true)
  · exact (rfl : block g75 1 0 0 = true)
  · exact (rfl : block g75 2 0 0 = true)
  · exact (rfl : block g75 3 0 0 = true)
  · exact g75B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g75G : graphValid g75 (boundsBefore K27) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low75 : Lower true (varsX 75) (graphGoal 75) 5 := lower_forest (g:=g75) (i:=0) (hints:=51) (before_sound K27 V27) g75G g75T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K75 := extendKnown K27 5 [(75,[]),(85,[33,67]),(89,[48,65,33]),(139,[118]),(212,[32,113,67,49,83]),(216,[48,65,32,98,82,117]),(226,[80,97,32,49,66,67,116])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V75 : Known true K75 := extend_ok (m:=75) V27 low75 (by decide +kernel)
def g77Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfdf00fff81fc7e3ffb,0xe01fff03f8fc7ff7c03f])),(BitVec.ofNat 152 (word80 [0x45c09245142904808b,0x81248a28520901170249]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xe6a8703ffe007fc7cd,0x50e07ffc00ff8f9aa1c0])),(BitVec.ofNat 152 (word80 [0x96a9b6d618b228112d,0x536dac316450225aa6db]))),((BitVec.ofNat 152 (word80 [0xfbb781ffffff8007f7,0x6f03ffffff000feede07])),(BitVec.ofNat 152 (word80 [0x235249820c0312204,0x6a49304180624408d492]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x64ffe3ffffffff80c,0x9ffc7ffffffff0193ff8])),(BitVec.ofNat 152 (word80 [0x249204100400400,0x4924082008008000924]))),(0x0,0x0),(0x0,0x0)]
def g77C : List ColumnInfo := [(4,0,73,0,4)]
def g77A : List (List Nat) := [[],[48]]
def g77D4 (j : Nat) := if j=0 then 0x1f else 0
def g77L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,g77D4)
  | _ => emptyPacking
def g77I (_ _ : Nat) : Option (Nat × Nat) := none
def g77 : Forest := ⟨77,4,fun i => g77Y[i]?.getD (0,0),g77C,g77A,g77L,g77I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g77P4_0 : block g77 4 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g77B4 : block g77 4 0 1=true := g77P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g77T : checkedTables g77 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g77 0 0 0 = true)
  · exact (rfl : block g77 1 0 0 = true)
  · exact (rfl : block g77 2 0 0 = true)
  · exact (rfl : block g77 3 0 0 = true)
  · exact g77B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g77G : graphValid g77 (boundsBefore K75) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low77 : Lower true (varsX 77) (graphGoal 77) 5 := lower_forest (g:=g77) (i:=0) (hints:=1539) (before_sound K75 V75) g77G g77T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K77 := extendKnown K75 5 [(77,[]),(78,[16]),(83,[33,67]),(86,[32,16,67]),(90,[16,66]),(92,[32,16,49,65]),(106,[48,16,82,97,66]),(116,[64,16,82,99,50]),(166,[16,115,67,84,101]),(178,[16,66,83,118]),(240,[64,16,82,99,115])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V77 : Known true K77 := extend_ok (m:=77) V75 low77 (by decide +kernel)
def g201Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xdf7ec03c3ffe0fbefd,0x80787ffc1f7dfb00f0ff])),(BitVec.ofNat 152 (word80 [0x820404444444210408,0x8888888420810111111]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x1fbf43c3c3fff03f7e,0x878787ffe07efd0f0f0f])),(BitVec.ofNat 152 (word80 [0x40808888888420810,0x11111110841020222222]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xe03fbc03fc3fffc07f,0x7807f87fff80fef00ff0])),(BitVec.ofNat 152 (word80 [0x81011111110841020,0x22222221082040444444]))),((BitVec.ofNat 152 (word80 [0xffc03ffc003fffff80,0x7ff8007fffff00fff000])),(BitVec.ofNat 152 (word80 [0x102022222221082040,0x44444442104080888888]))),(0x0,0x0)]
def g201C : List ColumnInfo := [(1,0,200,0,4),(8,0,193,0,4),(64,0,137,0,4),(128,0,73,0,4)]
def g201A : List (List Nat) := [[],[118],[99],[99,115],[115,99],[115],[48],[48,118],[48,96],[48,96,112],[48,112,96],[48,112],[96,48],[96,48,115],[96],[96,112],[96,115],[96,115,48],[112,48,99],[112,48],[112,96],[112],[112,99,48],[112,99]]
def g201D3 := limbs80 #[#[0x23ea6a1221e12148110,0x8028]]
def g201D4 := limbs80 #[#[0x2fd0910bd42443e48110,0x609085870]]
def g201H4 (j : Nat) := if j=0 then 0x37c0 else 0
def g201D5 (j : Nat) := if j=0 then 0xd1027d10 else 0
def g201H5 := limbs80 #[#[0xb20000000000000000,0xc500580017c8c003cc,0x688016100000]]
def g201D6 (j : Nat) := if j=0 then 0x3904f else 0
def g201H6 := limbs80 #[#[0x280000000,0x8800002c4000000000,0x582880000528]]
def g201L : Nat → Packing
  | 3 => (2,3,2,0,0,5,0,g201D3)
  | 4 => (3,2,2,0,0,5,0,g201D4)
  | 5 => (1,1,2,0,0,0,0,g201D5)
  | 6 => (1,0,2,0,0,0,0,g201D6)
  | _ => emptyPacking
def g201I : Nat → Nat → Option (Nat × Nat)
  | 4 => lookupWord 1 5 0 5 1 0 g201H4
  | 5 => lookupWord 2 23 0 9 2 3 g201H5
  | 6 => lookupWord 1 23 0 9 0 5 g201H6
  | _ => fun _ => none
def g201 : Forest := ⟨201,6,fun i => g201Y[i]?.getD (0,0),g201C,g201A,g201L,g201I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g201P3_0 : block g201 3 0 2=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g201B3 : block g201 3 0 2=true := g201P3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g201P4_0 : block g201 4 0 3=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g201B4 : block g201 4 0 3=true := g201P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g201P5_0 : block g201 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g201B5 : block g201 5 0 1=true := g201P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g201P6_0 : block g201 6 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g201B6 : block g201 6 0 1=true := g201P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g201T : checkedTables g201 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g201 0 0 0 = true)
  · exact (rfl : block g201 1 0 0 = true)
  · exact (rfl : block g201 2 0 0 = true)
  · exact g201B3
  · exact g201B4
  · exact g201B5
  · exact g201B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g201G : graphValid g201 (boundsBefore K77) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low201 : Lower true (varsX 201) (graphGoal 201) 7 := lower_forest (g:=g201) (i:=0) (hints:=3) (before_sound K77 V77) g201G g201T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K201 := extendKnown K77 7 [(201,[]),(202,[16]),(209,[67])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V201 : Known true K201 := extend_ok (m:=201) V77 low201 (by decide +kernel)
def g31Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xe003ffc07ffffffe00,0x3fffff80ffd386b20f0f])),(BitVec.ofNat 152 (word80 [0x41a8128d052280541a,0x82502916291304a21111]))),((BitVec.ofNat 152 (word80 [0xfffc00007ff01fffff,0xc007ffff01a37d4800f0])),(BitVec.ofNat 152 (word80 [0x81311b160644c89893,0x136232244d835c485555]))),((BitVec.ofNat 152 (word80 [0xffffffff80001fffff,0xfff80000003f407df000])),(BitVec.ofNat 152 (word80 [0x5c05c18178702e01c,0x380bc38703340753333]))),((BitVec.ofNat 152 (word80 [0x1fffff,0xfffffffffe663f7600ff])),(BitVec.ofNat 152 (word80 [0x160260205808130120,0x2404c00000642314aaaa]))),((BitVec.ofNat 152 (word80 [0xffffffffffffe00000,0x19dd38dff00])),(BitVec.ofNat 152 (word80 [0x1803800060001c01c0,0x38070040808c9308cccc]))),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g31C : List ColumnInfo := []
def g31A : List (List Nat) := [[],[33,67]]
def g31D4 (j : Nat) := if j=0 then 0x1f else 0
def g31L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,g31D4)
  | _ => emptyPacking
def g31I (_ _ : Nat) : Option (Nat × Nat) := none
def g31 : Forest := ⟨31,4,fun i => g31Y[i]?.getD (0,0),g31C,g31A,g31L,g31I⟩
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
theorem g31T : checkedTables g31 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g31 0 0 0 = true)
  · exact (rfl : block g31 1 0 0 = true)
  · exact (rfl : block g31 2 0 0 = true)
  · exact (rfl : block g31 3 0 0 = true)
  · exact g31B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g31G : graphValid g31 (boundsBefore K201) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low31 : Lower true (varsX 31) (graphGoal 31) 5 := lower_forest (g:=g31) (i:=0) (hints:=1075) (before_sound K201 V201) g31G g31T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K31 := extendKnown K201 5 [(31,[]),(47,[16,84]),(55,[32,16,67,83]),(59,[48,65,82]),(61,[64,49,82,16,33]),(62,[80,49,66])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V31 : Known true K31 := extend_ok (m:=31) V201 low31 (by decide +kernel)
def g79Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xffc00ffc07fe03fff,0xe00ffffe07f469d401c7])),(BitVec.ofNat 152 (word80 [0xa0a86a128d0a458a05,0x46a250a4b29029d49249]))),((BitVec.ofNat 152 (word80 [0xfffff00007fffc07f,0xfff007fff813a68c0e38])),(BitVec.ofNat 152 (word80 [0xc1304c1b160c891309,0x84c360c924d1a28c9249]))),((BitVec.ofNat 152 (word80 [0xfffffffff8000007f,0xfffff800000bc8b47000])),(BitVec.ofNat 152 (word80 [0x5c1705c182f0e1c2e,0x70382f1c70bc8b5b6db]))),((BitVec.ofNat 152 (word80 [0xf0000000000000007f,0xffffffffffe6fe67803f])),(BitVec.ofNat 152 (word80 [0x60180602030102030,0x8040300000654212492]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffffffffffff80,0x1911bbffc0])),(BitVec.ofNat 152 (word80 [0x80200800040000040,0x10080400000000024924]))),(0x0,0x0),(0x0,0x0)]
def g79C : List ColumnInfo := [(1,0,78,0,5)]
def g79A : List (List Nat) := [[],[16]]
def g79D5 (j : Nat) := if j=0 then 0x3f else 0
def g79L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,g79D5)
  | _ => emptyPacking
def g79I (_ _ : Nat) : Option (Nat × Nat) := none
def g79 : Forest := ⟨79,5,fun i => g79Y[i]?.getD (0,0),g79C,g79A,g79L,g79I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g79P5_0 : block g79 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g79B5 : block g79 5 0 1=true := g79P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g79T : checkedTables g79 5 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g79 0 0 0 = true)
  · exact (rfl : block g79 1 0 0 = true)
  · exact (rfl : block g79 2 0 0 = true)
  · exact (rfl : block g79 3 0 0 = true)
  · exact (rfl : block g79 4 0 0 = true)
  · exact g79B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g79G : graphValid g79 (boundsBefore K31) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low79 : Lower true (varsX 79) (graphGoal 79) 6 := lower_forest (g:=g79) (i:=0) (hints:=1587) (before_sound K31 V31) g79G g79T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K79 := extendKnown K31 6 [(79,[]),(87,[33,67]),(199,[115,67,84])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V79 : Known true K79 := extend_ok (m:=79) V31 low79 (by decide +kernel)
def g91Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfc3fe00ff87f87ffc0,0x7fffffe3dba15000ff0f])),(BitVec.ofNat 152 (word80 [0x288140a05101100285,0x502004842a141111111]))),((BitVec.ofNat 152 (word80 [0x3ffff0007ff87fff,0x807f1ffc2adc600f00f0])),(BitVec.ofNat 152 (word80 [0x310984c26212011306,0x260444812acc43333333]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x3fffffff80007fff,0xff801fff949db0f000ff])),(BitVec.ofNat 152 (word80 [0x421209048024222408,0x82889001410b4444444]))),((BitVec.ofNat 152 (word80 [0xffc000000000007fff,0xffffe0000b66bf000f00])),(BitVec.ofNat 152 (word80 [0x801c0e070438443810,0x30300e120946b6666666]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffffffffff8000,0x6442cffff000])),(BitVec.ofNat 152 (word80 [0x2010080040004020,0x40401000000008888888]))),(0x0,0x0),(0x0,0x0)]
def g91C : List ColumnInfo := [(1,0,90,0,5),(2,0,89,0,5),(8,0,83,0,5),(16,0,75,0,5)]
def g91A : List (List Nat) := [[],[48,65]]
def g91D6 (j : Nat) := if j=0 then 0x6c09f else 0
def g91L : Nat → Packing
  | 6 => (1,0,2,0,0,0,0,g91D6)
  | _ => emptyPacking
def g91I (_ _ : Nat) : Option (Nat × Nat) := none
def g91 : Forest := ⟨91,6,fun i => g91Y[i]?.getD (0,0),g91C,g91A,g91L,g91I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g91P6_0 : block g91 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g91B6 : block g91 6 0 1=true := g91P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g91T : checkedTables g91 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g91 0 0 0 = true)
  · exact (rfl : block g91 1 0 0 = true)
  · exact (rfl : block g91 2 0 0 = true)
  · exact (rfl : block g91 3 0 0 = true)
  · exact (rfl : block g91 4 0 0 = true)
  · exact (rfl : block g91 5 0 0 = true)
  · exact g91B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g91G : graphValid g91 (boundsBefore K79) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low91 : Lower true (varsX 91) (graphGoal 91) 7 := lower_forest (g:=g91) (i:=0) (hints:=51) (before_sound K79 V79) g91G g91T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K91 := extendKnown K79 7 [(91,[]),(93,[33,67]),(155,[118]),(214,[64,32,115,83]),(220,[112,33,16,67,81]),(227,[16,99,84,67,116]),(242,[16,64,32,99,82,115])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V91 : Known true K91 := extend_ok (m:=91) V79 low91 (by decide +kernel)
def g94Y : Array (Bits × Bits) := #[(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffc01ff87fc3fff00,0xffff1ffed2e680007c1f])),(BitVec.ofNat 152 (word80 [0x222894451108808a4a,0xa02444252268a5294a5]))),((BitVec.ofNat 152 (word80 [0xffffe0007ffc3ffff,0xffffe11773400f83e0])),(BitVec.ofNat 152 (word80 [0x40b018162050082c0c,0x2c140089146346318c63]))),((BitVec.ofNat 152 (word80 [0xffffffff80003ffff,0xff001ffce8f541f0001f])),(BitVec.ofNat 152 (word80 [0x84c120980261113010,0x30588900a8d154a5294a]))),((BitVec.ofNat 152 (word80 [0xf0000000000003ffff,0xffffe0005f98fe0003e0])),(BitVec.ofNat 152 (word80 [0x701c0e0438221c060,0x40600e104b9898c6318c]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffffffffffc0000,0x3280bbffffc00])),(BitVec.ofNat 152 (word80 [0x80201000400020080,0x80801000000021084210]))),(0x0,0x0),(0x0,0x0)]
def g94C : List ColumnInfo := [(2,0,92,0,5),(4,0,90,0,5),(8,0,86,0,5),(16,0,78,0,5),(10,0,84,0,4),(20,0,74,0,4)]
def g94A : List (List Nat) := [[],[66],[33,67],[33,49,65],[49],[49,66],[65,33,50],[65,50]]
def g94D4 := limbs80 #[#[0x9bd89544426d6215110,0x31825f635474]]
def g94D5 := limbs80 #[#[0x7c54443f280885bd4940,0xfea8885f95110beaa221,0xbd4940bfa8a81fb40502,0xcc8d018160c02faa3a07,0x882188201141080d176b,0xc110204810001]]
def g94H5 := limbs80 #[#[0x88c900000010000032,0x21]]
def g94D6 := limbs80 #[#[0x540a0380ff40fd40fd10,0x3140cc503]]
def g94H6 := limbs80 #[#[0x5b44010868781100d023,0x4e244800357d0fc2b1a0,0x1138641]]
def g94D7 (j : Nat) := if j=0 then 0x1605f else 0
def g94H7 := limbs80 #[#[0x14a0000f88039460,0x52000000000005200000,0xc1000033400007e7,0x4153001d4000]]
def g94L : Nat → Packing
  | 4 => (3,3,3,0,0,4,0,g94D4)
  | 5 => (10,2,3,0,0,7,0,g94D5)
  | 6 => (3,1,3,0,0,6,0,g94D6)
  | 7 => (1,0,3,0,0,0,0,g94D7)
  | _ => emptyPacking
def g94I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 13 0 8 2 2 g94H5
  | 6 => lookupWord 4 17 4 10 4 2 g94H6
  | 7 => lookupWord 3 31 3 9 2 3 g94H7
  | _ => fun _ => none
def g94 : Forest := ⟨94,7,fun i => g94Y[i]?.getD (0,0),g94C,g94A,g94L,g94I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g94P4_0 : block g94 4 0 3=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g94B4 : block g94 4 0 3=true := g94P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g94P5_0 : block g94 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g94P5_1 : block g94 5 1 9=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g94B5 : block g94 5 0 10=true := (@block_merge g94 5 0 1 9 g94P5_0 g94P5_1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g94P6_0 : block g94 6 0 3=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g94B6 : block g94 6 0 3=true := g94P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g94P7_0 : block g94 7 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g94B7 : block g94 7 0 1=true := g94P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g94T : checkedTables g94 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g94 0 0 0 = true)
  · exact (rfl : block g94 1 0 0 = true)
  · exact (rfl : block g94 2 0 0 = true)
  · exact (rfl : block g94 3 0 0 = true)
  · exact g94B4
  · exact g94B5
  · exact g94B6
  · exact g94B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g94G : graphValid g94 (boundsBefore K91) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low94 : Lower true (varsX 94) (graphGoal 94) 8 := lower_forest (g:=g94) (i:=0) (hints:=16913456) (before_sound K91 V91) g94G g94T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K94 := extendKnown K91 8 [(94,[]),(179,[32,16,67,83,118])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V94 : Known true K94 := extend_ok (m:=94) V91 low94 (by decide +kernel)
def g103Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xe003ff80ffe03ffff0,0x1ff80ffc0009ede81c0])),(BitVec.ofNat 152 (word80 [0x45a8a51a2a458a12a2,0xd4251a148b009e8eb6db]))),((BitVec.ofNat 152 (word80 [0xfffc0000ffffc07fff,0xfe0000fffff8da218e07])),(BitVec.ofNat 152 (word80 [0x8130362c0c891304c0,0x98362c191248d2019249]))),((BitVec.ofNat 152 (word80 [0xffffffff0000007fff,0xffffff00000ff10e7038])),(BitVec.ofNat 152 (word80 [0x1c038300f0e1c0700,0xe038301e1c0ad10a1249]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x7fff,0xffffffffff99af6d003f])),(BitVec.ofNat 152 (word80 [0x1602c040b01020580b,0x14000a000112c646db6]))),((BitVec.ofNat 152 (word80 [0xffffffffffffff8000,0x6754f2ffc0])),(BitVec.ofNat 152 (word80 [0x18030000c00000600c,0x18040c0202500704924]))),(0x0,0x0),(0x0,0x0)]
def g103C : List ColumnInfo := [(2,0,101,0,4)]
def g103A : List (List Nat) := [[],[33]]
def g103D4 (j : Nat) := if j=0 then 0x3f else 0
def g103L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,g103D4)
  | _ => emptyPacking
def g103I (_ _ : Nat) : Option (Nat × Nat) := none
def g103 : Forest := ⟨103,4,fun i => g103Y[i]?.getD (0,0),g103C,g103A,g103L,g103I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g103P4_0 : block g103 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g103B4 : block g103 4 0 1=true := g103P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g103T : checkedTables g103 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g103 0 0 0 = true)
  · exact (rfl : block g103 1 0 0 = true)
  · exact (rfl : block g103 2 0 0 = true)
  · exact (rfl : block g103 3 0 0 = true)
  · exact g103B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g103G : graphValid g103 (boundsBefore K94) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low103 : Lower true (varsX 103) (graphGoal 103) 5 := lower_forest (g:=g103) (i:=0) (hints:=1049942) (before_sound K94 V94) g103G g103T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K103 := extendKnown K94 5 [(103,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V103 : Known true K103 := extend_ok (m:=103) V94 low103 (by decide +kernel)
def g107Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfe007fe1ff0fffc01f,0xffe1ff0ff92b0a00f00f])),(BitVec.ofNat 152 (word80 [0x942509442220128941,0x4044222099220a333333]))),((BitVec.ofNat 152 (word80 [0xffff8001fff0ffffe0,0x1ffffff01c56b90f0ff0])),(BitVec.ofNat 152 (word80 [0x180601880402030181,0x80800402084609111111]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffffe0000ffffff,0xe001ffff239766f000ff])),(BitVec.ofNat 152 (word80 [0x204812004844240202,0x5084800201164444444]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffff,0xfffe00001369f8000f00])),(BitVec.ofNat 152 (word80 [0xc1705c117088b82c14,0x160170441329f0eeeeee]))),((BitVec.ofNat 152 (word80 [0xffffffffffff000000,0xcea8c5fff000])),(BitVec.ofNat 152 (word80 [0x18060018000c03018,0x18118088468880888888]))),(0x0,0x0),(0x0,0x0)]
def g107C : List ColumnInfo := [(0,32,73,2,5),(1,0,106,0,5),(32,0,75,0,5),(2,32,73,0,4),(8,0,99,0,4),(64,0,43,0,4)]
def g107A : List (List Nat) := [[],[99]]
def g107D4 (j : Nat) := if j=0 then 0x5ed4142 else 0
def g107D5 (j : Nat) := if j=0 then 0x108404fd42 else 0
def g107H5 (j : Nat) := if j=0 then 0xb0 else 0
def g107D6 (j : Nat) := if j=0 then 0x2c458bf else 0
def g107H6 (j : Nat) := if j=0 then 0x3 else 0
def g107L : Nat → Packing
  | 4 => (1,2,3,0,0,0,0,g107D4)
  | 5 => (1,1,3,0,0,0,0,g107D5)
  | 6 => (1,0,3,0,0,0,0,g107D6)
  | _ => emptyPacking
def g107I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 2 0 4 0 0 g107H5
  | 6 => lookupWord 1 2 0 4 0 0 g107H6
  | _ => fun _ => none
def g107 : Forest := ⟨107,6,fun i => g107Y[i]?.getD (0,0),g107C,g107A,g107L,g107I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g107P4_0 : block g107 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g107B4 : block g107 4 0 1=true := g107P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g107P5_0 : block g107 5 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g107B5 : block g107 5 0 1=true := g107P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g107P6_0 : block g107 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g107B6 : block g107 6 0 1=true := g107P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g107T : checkedTables g107 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g107 0 0 0 = true)
  · exact (rfl : block g107 1 0 0 = true)
  · exact (rfl : block g107 2 0 0 = true)
  · exact (rfl : block g107 3 0 0 = true)
  · exact g107B4
  · exact g107B5
  · exact g107B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g107G : graphValid g107 (boundsBefore K103) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low107 : Lower true (varsX 107) (graphGoal 107) 7 := lower_forest (g:=g107) (i:=0) (hints:=1048627) (before_sound K103 V103) g107G g107T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K107 := extendKnown K103 7 [(107,[]),(117,[33,67]),(157,[48,65,33,82,118])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V107 : Known true K107 := extend_ok (m:=107) V103 low107 (by decide +kernel)
def g109Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xf003ff87fe1fffc01f,0xfff87fffe474a4007c1f])),(BitVec.ofNat 152 (word80 [0xa12845108440228940,0xa01108826014a45294a5]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffc0007ffe1ffffe0,0xfffffc0335be20f83e0])),(BitVec.ofNat 152 (word80 [0xc030162028040b0182,0xc0a00108225922318c63]))),((BitVec.ofNat 152 (word80 [0xfffffff80001ffffff,0xf0007ffccfd11df0001f])),(BitVec.ofNat 152 (word80 [0x240980130884c0203,0x2c2120087c108a5294a]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x1ffffff,0xffff80004d2fe80003e0])),(BitVec.ofNat 152 (word80 [0xb82e045c111702c14,0xb005c104d26c9ce739c]))),((BitVec.ofNat 152 (word80 [0xfffffffffffe000000,0x33aa61bfffc00])),(BitVec.ofNat 152 (word80 [0xc0300060001803018,0xc046021182211084210]))),(0x0,0x0),(0x0,0x0)]
def g109C : List ColumnInfo := [(0,32,73,4,5),(32,0,77,0,5),(1,0,108,0,4),(4,32,73,0,4),(8,0,101,0,4)]
def g109A : List (List Nat) := [[],[48]]
def g109D4 (j : Nat) := if j=0 then 0x5bd4940 else 0
def g109D5 := limbs80 #[#[0x240d140ff40fd40fd20,0x2012]]
def g109H5 (j : Nat) := if j=0 then 0xe else 0
def g109D6 (j : Nat) := if j=0 then 0x18989f else 0
def g109H6 := limbs80 #[#[0x1580001a010007200000,0x44000000]]
def g109L : Nat → Packing
  | 4 => (1,2,3,0,0,0,0,g109D4)
  | 5 => (3,1,3,0,0,5,0,g109D5)
  | 6 => (1,0,3,0,0,0,0,g109D6)
  | _ => emptyPacking
def g109I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 2 0 4 0 0 g109H5
  | 6 => lookupWord 1 19 0 7 2 1 g109H6
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
theorem g109P5_0 : block g109 5 0 3=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g109B5 : block g109 5 0 3=true := g109P5_0
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
theorem low109 : Lower true (varsX 109) (graphGoal 109) 7 := lower_forest (g:=g109) (i:=0) (hints:=2098435) (before_sound K107 V107) g109G g109T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K109 := extendKnown K107 7 [(109,[]),(115,[33,67]),(158,[16,66,82,118])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V109 : Known true K109 := extend_ok (m:=109) V107 low109 (by decide +kernel)
def g110Y : Array (Bits × Bits) := #[(0x0,0x0),((BitVec.ofNat 152 (word80 [0xff007fe1ff0fffc03f,0xfff0fffff95e0200f0ff])),(BitVec.ofNat 152 (word80 [0xa0501440220028281,0x40220020980602111111]))),((BitVec.ofNat 152 (word80 [0xffff8001fff0ffffc0,0x1fff0ff01c35b90f0f00])),(BitVec.ofNat 152 (word80 [0x2c06058814020b0305,0x81402042183511333333]))),((BitVec.ofNat 152 (word80 [0xfffffffe0000ffffff,0xe0000fff23b566f0000f])),(BitVec.ofNat 152 (word80 [0xb028160058442c0406,0x5844280213164666666]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffff,0xfffff000134bf8000ff0])),(BitVec.ofNat 152 (word80 [0xc0b058116088b02828,0x16000b040348e8cccccc]))),((BitVec.ofNat 152 (word80 [0xffffffffffff000000,0xcea8c5fff000])),(BitVec.ofNat 152 (word80 [0xc060018000c03030,0x18088c08468880888888]))),(0x0,0x0),(0x0,0x0)]
def g110C : List ColumnInfo := [(4,0,106,0,5)]
def g110A : List (List Nat) := [[],[97,82]]
def g110D5 (j : Nat) := if j=0 then 0x3f else 0
def g110L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,g110D5)
  | _ => emptyPacking
def g110I (_ _ : Nat) : Option (Nat × Nat) := none
def g110 : Forest := ⟨110,5,fun i => g110Y[i]?.getD (0,0),g110C,g110A,g110L,g110I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g110P5_0 : block g110 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g110B5 : block g110 5 0 1=true := g110P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g110T : checkedTables g110 5 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g110 0 0 0 = true)
  · exact (rfl : block g110 1 0 0 = true)
  · exact (rfl : block g110 2 0 0 = true)
  · exact (rfl : block g110 3 0 0 = true)
  · exact (rfl : block g110 4 0 0 = true)
  · exact g110B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g110G : graphValid g110 (boundsBefore K109) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low110 : Lower true (varsX 110) (graphGoal 110) 6 := lower_forest (g:=g110) (i:=0) (hints:=17831216) (before_sound K109 V109) g110G g110T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K110 := extendKnown K109 6 [(110,[]),(118,[33,67]),(229,[16,112,48,67]),(236,[113,65])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V110 : Known true K110 := extend_ok (m:=110) V109 low110 (by decide +kernel)
def g122Y : Array (Bits × Bits) := #[(0x0,0x0),((BitVec.ofNat 152 (word80 [0xc007ff01ffe03fffff,0xffffffffff9ceb9d01ff])),(BitVec.ofNat 152 (word80 [0x809002040240800120,0x8090000800403851249]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfff80001ffffc07ff0,0x3ff80fffff19e0b0e07])),(BitVec.ofNat 152 (word80 [0xa215458548a150a43,0x50921a290a51980a2492]))),((BitVec.ofNat 152 (word80 [0xfffffffe0000007fff,0xfc0000ffc00f8a66f000])),(BitVec.ofNat 152 (word80 [0xcc198906713261382,0x60dc2c32130d8a46b6db]))),((BitVec.ofNat 152 (word80 [0x7fff,0xffffff000009f56c0038])),(BitVec.ofNat 152 (word80 [0x2f05e0e1781c385c0b,0x82e030bc1c09f4686db6]))),((BitVec.ofNat 152 (word80 [0xffffffffffffff8000,0x6754f2ffc0])),(BitVec.ofNat 152 (word80 [0x30060001800000600c,0x30040c0202244304924]))),(0x0,0x0),(0x0,0x0)]
def g122C : List ColumnInfo := [(16,0,106,0,5)]
def g122A : List (List Nat) := [[],[97,84]]
def g122D5 (j : Nat) := if j=0 then 0x3f else 0
def g122L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,g122D5)
  | _ => emptyPacking
def g122I (_ _ : Nat) : Option (Nat × Nat) := none
def g122 : Forest := ⟨122,5,fun i => g122Y[i]?.getD (0,0),g122C,g122A,g122L,g122I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g122P5_0 : block g122 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g122B5 : block g122 5 0 1=true := g122P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g122T : checkedTables g122 5 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g122 0 0 0 = true)
  · exact (rfl : block g122 1 0 0 = true)
  · exact (rfl : block g122 2 0 0 = true)
  · exact (rfl : block g122 3 0 0 = true)
  · exact (rfl : block g122 4 0 0 = true)
  · exact g122B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g122G : graphValid g122 (boundsBefore K110) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low122 : Lower true (varsX 122) (graphGoal 122) 6 := lower_forest (g:=g122) (i:=0) (hints:=18223152) (before_sound K110 V110) g122G g122T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K122 := extendKnown K110 6 [(122,[]),(124,[33,67]),(151,[48,65,82,118])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V122 : Known true K122 := extend_ok (m:=122) V110 low122 (by decide +kernel)
def g203Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x7f01fc7f01fc7e7fc,0x7f1f9fe7ea000f00f0f])),(BitVec.ofNat 152 (word80 [0x50a14290a142905028,0x50a414051ea111111111]))),((BitVec.ofNat 152 (word80 [0x7ffe007ffe007f9ff,0xf801fe7f8b700f00f0f0])),(BitVec.ofNat 152 (word80 [0x60c18320c183208430,0x60c821084b7111111111]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xf8000007fffff801ff,0xfffe007fe640f00f00ff])),(BitVec.ofNat 152 (word80 [0x810204010204010040,0x81004010000222222222]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffff800000001ff,0xffffff8001af000fff00])),(BitVec.ofNat 152 (word80 [0x20408020408020081,0x2008020000444444444]))),((BitVec.ofNat 152 (word80 [0xfffffffffffffffe00,0x181ffff00000])),(BitVec.ofNat 152 (word80 [0x40810040810040102,0x4010040000888888888]))),(0x0,0x0)]
def g203C : List ColumnInfo := [(1,0,202,0,7)]
def g203A : List (List Nat) := [[],[118],[99],[99,115],[115,99],[115],[16],[16,118],[16,99],[16,99,115],[16,115,99],[16,115]]
def g203D7 (j : Nat) := if j=0 then 0x3f else 0
def g203L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g203D7)
  | _ => emptyPacking
def g203I (_ _ : Nat) : Option (Nat × Nat) := none
def g203 : Forest := ⟨203,7,fun i => g203Y[i]?.getD (0,0),g203C,g203A,g203L,g203I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g203P7_0 : block g203 7 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g203B7 : block g203 7 0 1=true := g203P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g203T : checkedTables g203 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g203 0 0 0 = true)
  · exact (rfl : block g203 1 0 0 = true)
  · exact (rfl : block g203 2 0 0 = true)
  · exact (rfl : block g203 3 0 0 = true)
  · exact (rfl : block g203 4 0 0 = true)
  · exact (rfl : block g203 5 0 0 = true)
  · exact (rfl : block g203 6 0 0 = true)
  · exact g203B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g203G : graphValid g203 (boundsBefore K122) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low203 : Lower true (varsX 203) (graphGoal 203) 8 := lower_forest (g:=g203) (i:=0) (hints:=51) (before_sound K122 V122) g203G g203T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K203 := extendKnown K122 8 [(203,[]),(217,[48,65,33])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V203 : Known true K203 := extend_ok (m:=203) V122 low203 (by decide +kernel)
def g205Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfe1ff01ff1ffffc03f,0xe1fe1fffd19d300f00ff])),(BitVec.ofNat 152 (word80 [0x1440a140a408028281,0x44044008018931111111]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x1fffe001fc7fffc0,0x1ffe1fc4d3aa0000f00])),(BitVec.ofNat 152 (word80 [0x5892c192c8514b2325,0x892805114d3aabbbbbbb]))),((BitVec.ofNat 152 (word80 [0x1ffffffe007fffff,0xfe0001ffbe1b40f0f00f])),(BitVec.ofNat 152 (word80 [0x6103020300620c0406,0x3088203e1002222222]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffe0000000007fffff,0xfffffe000be08f00fff0])),(BitVec.ofNat 152 (word80 [0x800404040080100808,0x400040000004444444]))),((BitVec.ofNat 152 (word80 [0xffffffffffff800000,0x6446ffff0000])),(BitVec.ofNat 152 (word80 [0x1808180100603030,0x118111824046c8888888]))),(0x0,0x0)]
def g205C : List ColumnInfo := [(4,0,201,0,7)]
def g205A : List (List Nat) := [[],[115],[48],[48,112],[112,48],[112]]
def g205D7 (j : Nat) := if j=0 then 0x3f else 0
def g205L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g205D7)
  | _ => emptyPacking
def g205I (_ _ : Nat) : Option (Nat × Nat) := none
def g205 : Forest := ⟨205,7,fun i => g205Y[i]?.getD (0,0),g205C,g205A,g205L,g205I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g205P7_0 : block g205 7 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g205B7 : block g205 7 0 1=true := g205P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g205T : checkedTables g205 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g205 0 0 0 = true)
  · exact (rfl : block g205 1 0 0 = true)
  · exact (rfl : block g205 2 0 0 = true)
  · exact (rfl : block g205 3 0 0 = true)
  · exact (rfl : block g205 4 0 0 = true)
  · exact (rfl : block g205 5 0 0 = true)
  · exact (rfl : block g205 6 0 0 = true)
  · exact g205B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g205G : graphValid g205 (boundsBefore K203) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low205 : Lower true (varsX 205) (graphGoal 205) 8 := lower_forest (g:=g205) (i:=0) (hints:=1539) (before_sound K203 V203) g205G g205T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K205 := extendKnown K203 8 [(205,[]),(206,[16]),(233,[82,66,118]),(241,[82,67,50,118])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V205 : Known true K205 := extend_ok (m:=205) V203 low205 (by decide +kernel)
def g211Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xff0ff01fe3f8ffe0,0x3fc7f1ffd675000f00ff])),(BitVec.ofNat 152 (word80 [0xa0a20a14148120142,0x82902402163411111111]))),((BitVec.ofNat 152 (word80 [0xff000fffe003ff1fff,0xc007fe3f317a00f00f00])),(BitVec.ofNat 152 (word80 [0x2c2c42c18590a04583,0xb214084b17a33333333]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffc001fff,0xfff8003fede10f00f00f])),(BitVec.ofNat 152 (word80 [0x303083020600c48604,0xc01890829c122222222]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffff0000000001fff,0xffffffc01388f000fff0])),(BitVec.ofNat 152 (word80 [0x404004040801000808,0x10020010000044444444]))),((BitVec.ofNat 152 (word80 [0xffffffffffffffe000,0x2816ffff0000])),(BitVec.ofNat 152 (word80 [0x808008081002001010,0x20040020000088888888]))),(0x0,0x0)]
def g211C : List ColumnInfo := [(2,0,209,0,7)]
def g211A : List (List Nat) := [[],[118],[64],[64,118]]
def g211D7 (j : Nat) := if j=0 then 0x3f else 0
def g211L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g211D7)
  | _ => emptyPacking
def g211I (_ _ : Nat) : Option (Nat × Nat) := none
def g211 : Forest := ⟨211,7,fun i => g211Y[i]?.getD (0,0),g211C,g211A,g211L,g211I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g211P7_0 : block g211 7 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g211B7 : block g211 7 0 1=true := g211P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g211T : checkedTables g211 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g211 0 0 0 = true)
  · exact (rfl : block g211 1 0 0 = true)
  · exact (rfl : block g211 2 0 0 = true)
  · exact (rfl : block g211 3 0 0 = true)
  · exact (rfl : block g211 4 0 0 = true)
  · exact (rfl : block g211 5 0 0 = true)
  · exact (rfl : block g211 6 0 0 = true)
  · exact g211B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g211G : graphValid g211 (boundsBefore K205) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low211 : Lower true (varsX 211) (graphGoal 211) 8 := lower_forest (g:=g211) (i:=0) (hints:=100) (before_sound K205 V205) g211G g211T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K211 := extendKnown K205 8 [(211,[]),(213,[33,116,100]),(218,[16,64,32,50]),(234,[48,81,32,100,65])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V211 : Known true K211 := extend_ok (m:=211) V205 low211 (by decide +kernel)
def g230Y : Array (Bits × Bits) := #[(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfc3fe01ff0fffff00f,0xfff0fff0fe542f0071c7])),(BitVec.ofNat 152 (word80 [0x28814140a20400a0a0,0xa0220022081425049249]))),((BitVec.ofNat 152 (word80 [0x3fffe000fe1ffff0,0xfff0fff015971c00e38])),(BitVec.ofNat 152 (word80 [0x31218190c40850c8c8,0xc840284020587156db6d]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x3fffffff001fffff,0xf0000ffff2a37683803f])),(BitVec.ofNat 152 (word80 [0x420a0a050050850101,0x284428002a102892492]))),((BitVec.ofNat 152 (word80 [0xffc0000000001fffff,0xfffff000013c8afc0fc0])),(BitVec.ofNat 152 (word80 [0x800c0c060861060202,0x300030441208a892492]))),((BitVec.ofNat 152 (word80 [0xffffffffffffe00000,0xce2917ff000])),(BitVec.ofNat 152 (word80 [0x3010180080180c0c,0xc088c08844210724924]))),(0x0,0x0)]
def g230C : List ColumnInfo := [(4,0,226,0,5)]
def g230A : List (List Nat) := [[],[101],[113],[113,101]]
def g230D5 (j : Nat) := if j=0 then 0x3f else 0
def g230L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,g230D5)
  | _ => emptyPacking
def g230I (_ _ : Nat) : Option (Nat × Nat) := none
def g230 : Forest := ⟨230,5,fun i => g230Y[i]?.getD (0,0),g230C,g230A,g230L,g230I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g230P5_0 : block g230 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g230B5 : block g230 5 0 1=true := g230P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g230T : checkedTables g230 5 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g230 0 0 0 = true)
  · exact (rfl : block g230 1 0 0 = true)
  · exact (rfl : block g230 2 0 0 = true)
  · exact (rfl : block g230 3 0 0 = true)
  · exact (rfl : block g230 4 0 0 = true)
  · exact g230B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g230G : graphValid g230 (boundsBefore K211) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low230 : Lower true (varsX 230) (graphGoal 230) 6 := lower_forest (g:=g230) (i:=0) (hints:=286262608) (before_sound K211 V211) g230G g230T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K230 := extendKnown K211 6 [(230,[]),(244,[65,82,49,118])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V230 : Known true K230 := extend_ok (m:=230) V211 low230 (by decide +kernel)
def g63Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xe0001ffffffff001ff,0xc7447c36a8a740007c1f])),(BitVec.ofNat 152 (word80 [0x420d42094205202c05,0x740543288a21294a529]))),((BitVec.ofNat 152 (word80 [0xffffe0001ffffffe00,0x18dfc238d4e081f003e0])),(BitVec.ofNat 152 (word80 [0x8049804d8046404809,0x88c4c230d0608a5294a5]))),((BitVec.ofNat 152 (word80 [0xffffffffe000000000,0x2761e3d10b58be0f8000])),(BitVec.ofNat 152 (word80 [0xe000e001780700e,0x5416390085886318c63]))),((BitVec.ofNat 152 (word80 [0xffffffffffffffffff,0xe819257c4e4f400003ff])),(BitVec.ofNat 152 (word80 [0x1490149014980500a0,0x2019214c060d65294a52]))),(0x24569a07773c000ffc00,(BitVec.ofNat 152 (word80 [0x18e018e018e0098130,0x201688057704294a5294]))),(0x13aa5dc49781bff00000,(BitVec.ofNat 152 (word80 [0x1f001f001f000e01c0,0x122a1c440781318c6318]))),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g63C : List ColumnInfo := [(8,0,55,0,5),(9,0,54,0,4),(10,0,53,0,4),(17,0,46,0,4),(20,0,43,0,4),(34,0,29,0,4),(36,0,27,0,4)]
def g63A : List (List Nat) := [[],[33,67],[16,84],[16,32,83,67],[32,16,67,83],[32,83],[48,65,82],[48,81,66,16,32],[64,49,82,16,33],[64,81,50],[80,49,66],[80,65,50]]
def g63D5 (j : Nat) := if j=0 then 0xb7d8d10 else 0
def g63D6 (j : Nat) := if j=0 then 0x683faa1fd10 else 0
def g63H6 (j : Nat) := if j=0 then 0xf0 else 0
def g63D7 (j : Nat) := if j=0 then 0x335611bf else 0
def g63H7 := limbs80 #[#[0xc9000012e00003c4002,0x1650029941e900486580]]
def g63L : Nat → Packing
  | 5 => (1,2,3,0,0,0,0,g63D5)
  | 6 => (2,1,3,0,0,4,0,g63D6)
  | 7 => (1,0,3,0,0,0,0,g63D7)
  | _ => emptyPacking
def g63I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 2 0 4 0 0 g63H6
  | 7 => lookupWord 2 17 2 9 1 4 g63H7
  | _ => fun _ => none
def g63 : Forest := ⟨63,7,fun i => g63Y[i]?.getD (0,0),g63C,g63A,g63L,g63I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P5_0 : block g63 5 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g63B5 : block g63 5 0 1=true := g63P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P6_0 : block g63 6 0 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g63B6 : block g63 6 0 2=true := g63P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P7_0 : block g63 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g63B7 : block g63 7 0 1=true := g63P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63T : checkedTables g63 7 := by
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
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63G : graphValid g63 (boundsBefore K230) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low63 : Lower true (varsX 63) (graphGoal 63) 8 := lower_forest (g:=g63) (i:=0) (hints:=1049651) (before_sound K230 V230) g63G g63T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K63 := extendKnown K230 8 [(63,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V63 : Known true K63 := extend_ok (m:=63) V230 low63 (by decide +kernel)
def g95Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xffffe001ffffff01fc,0x5eab85c0600001f07c1f])),(BitVec.ofNat 152 (word80 [0x500540d40940522c50,0x5e8300c0610842108421]))),((BitVec.ofNat 152 (word80 [0x3fffffe001ffffe01,0x9993613740003e0003e0])),(BitVec.ofNat 152 (word80 [0x988984984d84644899,0x9993013545294a5294a5]))),((BitVec.ofNat 152 (word80 [0x3ffffffffe0000002,0x54dc3874c007c00f8000])),(BitVec.ofNat 152 (word80 [0xe02e00e00e017870e0,0x548c3874c318c6318c63]))),((BitVec.ofNat 152 (word80 [0x3fffffffffffffffe,0xa08ef66320f8000003ff])),(BitVec.ofNat 152 (word80 [0x13009009009800002,0x200cf6020a5294a5294a]))),((BitVec.ofNat 152 (word80 [0xfc0000000000000002,0x4970938fdf00000ffc00])),(BitVec.ofNat 152 (word80 [0x1c00e00e00e008102,0x170830b0c6318c6318c]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [1,0x37050a181ffffff00000])),(BitVec.ofNat 152 (word80 [0x20010010010000000,0x108421084210]))),(0x0,0x0),(0x0,0x0)]
def g95C : List ColumnInfo := [(1,0,94,0,8),(2,0,93,0,7),(4,0,91,0,7),(8,0,87,0,6),(16,0,79,0,6),(6,0,89,0,5),(9,0,86,0,5),(10,0,85,0,5),(12,0,83,0,5),(18,0,77,0,5),(20,0,75,0,5),(64,0,31,0,5),(11,0,84,0,4),(14,0,81,0,4),(22,0,73,0,4),(66,0,29,0,4),(68,0,27,0,4)]
def g95A : List (List Nat) := [[],[33,67]]
def g95D4 := limbs80 #[#[0x32a87993746007154d43,0x81dc16550f1c304c0ae0,0x75c830db92a921e38e0b,0xaa74e39259170185538,0xf624c3021e730b22e03]]
def g95D5 := limbs80 #[#[0x5d9544c7955915354531,0x4c63de0576551318fb80,0xe0576d51318ef825d954,0x507318ef825d2654c63d,0x9e7825d351cc67560e75,0xdc554cc67560f7155331,0xcc63ee017655331cb564,0xe0974997318ef825d954,0xd4d41f155350d515063b,0xa9f8654d43d063be0976,0xdc553d073558f7154f41,0xd07275d163d4f419b584,0xe095458f41a5f8558f53,0x58f41ad9801d563d07a3,0xacd821d563d06b560475,0x9d563d06b5e057558f41,0x54679e0974d4551c5f75,0x54f7150f518ef825d363,0x50f51cd563dc543d4755,0x97585dc543d472d59371,0x5d943d463ee017650f51,0x50f0fd977454d438ef82,0x6046554d43a798019553,0x54d438fb805d95350e9d,0xd97741c55350ef460071,0x1955350f351db7154d43,0x50ed56046554d43b5980,0xe1d6519543c79655c065,0x59543cf1815c06550e1f,0xcf371dc16550f3c1c770,0xdc16550f3c2077059543,0x50f39dc87159543cf381],#[0xdd37359543ce772dc565,0x58a43ec78154d6290f27,0x8ed86dc95490eb360f54,0x5516014fb4e055358053,0x14f35e1d5358453aeb82,0xe055358853ae78255161,0x54c538ef875516214fb1,0xcd776dc55314fa559371,0x5c06154f35e077654c53,0x54f3cd917018553cf164,0xe096418553af38059061,0xd85538f7875906154eb9,0xae7825936154ebce0164,0x5d36154e3ee0174d8553,0x54eb9e0954d85538ef82,0x60c74d8553e375495361,0xd8553cb5741d36154eb5,0xae7825d36154ebce0174,0x5906454e73e0974d4d53,0x94e73e0974d4e538bf87,0xe0576d4e53b4f825d353,0x3c00ae9801c964d4f95,0xfc390cc2d09c2106c15,0x1e0721b06615c5112c45,0x2a0a2270962408a2107e,0x360d2330c6300ba2d0ae,0x4450b414f63c0ea390de,0x5053b4d52f4a52347517,0x5c56b5955f5655353547,0x6859b6558f625835f577,0x7b1e6781da751ce721b9,0x872168420a811fe7e1f2],#[0x2418d22e8a222,0x1020800000000000,0x0,0x90400000000000,0x0,0xe2300400000000000000,0x6182]]
def g95H5 := limbs80 #[#[0x1e0000,0x6a0000000000000,0xe2,0x500000000980000,0x168]]
set_option maxRecDepth 16000 in
def g95D6 := limbs80 #[#[0x67bb8aca98f555354531,0x1baae7a8e63d554f51cc,0x677b92caa0e7565d473,0x439dee4b26a3a755163d,0x50e7ab88caa1cf970195,0xa439eee2b2a873edc165,0x114f6ca9ac029ecd5358,0x4c53d9aa6b10a7b554d6,0x6154e6fbb2a629e9d645,0x59353cbaeda9ca77c5c0,0xd514c7f2a92a290cef72,0x154d31deac8a8a63f554,0xc9544c76eb22a698fd77,0x7655131d7ac8aa2637bd,0x5c7544c67fbb2a898cfd,0xd76d5131bbae7aa2637d,0xfdd5644c77bb8ac898cf,0xff7459531deee2b2a633,0xf554d41cc67eba4ca98c,0xef56550731f6aa8a0e63,0x3f554f51cc6fb3aa8398,0x8df574d4731faae7a8e6,0x63bd5db51cc77ab2ea39,0x98edd6454f31faee2a9e,0x6637bdc954cc6fbb8aa9,0x998cfd7655331d7ac8aa,0xa663775cf54cc67fbb2a,0xcb98cff75593319faeda,0x32e633fdd165cc77bb8a,0xaa2a0fb543545419fae9,0x8a8a83ddd4d51507baa9,0x9a86a0fb77150d41f6aa],#[0xeaa1a83af59543507cea,0xb8aa6a0dbf7550d41b7a,0xae3a9a833fdd953506fb,0xebb6a6a0dbd74d4d41be,0x5ee4aa283eddc5545067,0x7bb8acaa0dbf7355141f,0x9fee6b2a83bbdc965507,0x7cea9a87a0cfd7399541,0x1b7aeaa1e83af59543d0,0x6fbb8aa7a0dbf7550f4,0x419faeca9e83b758d53d,0xd076eb1ea7a0cff7654f,0xf419faeda9e836f5d353,0x3d067fbaac7a0ebd5458,0x8f41dbaeab1e83b71d56,0x54d076fbaac7a0ede755,0x59741b7ee6aa683ebdc9,0xf515467eb9ccba0cff73,0x4d4551beae7a8aa3dd54,0x8d43547aea9a86a8df57,0x7154d519feeca1aa3b7d,0x5d363547bbb8aa6a8df7,0xf7255151beee2aa2a33f,0xf5cf64546f7b92c8a8de,0x5d5350f51beee2a1ea33,0xaf59143d476eb1a87a8f,0xcff7650f519faeca1ea3,0x3bddc563d47bbb8aa7a8,0x8def72553519fee8b1ea,0xa3bbdc964d46f7b92c9a,0xa1edd53d85439fee6b26,0xa873f5d76150f5eaa6c2],#[0x6a1dbf7454d43beee2a9,0x9a879fd955350f3e32aa,0xa6a1fd47154d439faeca,0xa9a8777dc95350febb8a,0x2a6a1f9e5454d43f3aa8,0xaa9a87e7dd15350fce3a,0xb2a6a1f5f6554d43eb8c,0xeb29a87e79525350f6e3,0xba6a6a1dde7694d43bba,0x2e032a879fd975350ede,0xeb28caa1df57119543bf,0xf6e0b2a873f9d86550f3,0x3fb2acaa1df77159543b,0xde8e2b2a87bedc16550f,0xe7fb8acaa1ef77159543,0x39fee6b2a87b7dcd6550,0xe7eb9ccaa1e7f659954,0x43ddaa8b14873f5c7655,0x90febb8aa721eef5458a,0x243bdee4aa487b7dd953,0x490f3eb2aa921ddf7355,0x5243bbae7aa4879f9955,0x6014f7caa2c029e7d65d,0x58453deaa8b08a7be951,0x16214f76aa2c429ef654,0x454c53faee2a98a7bb95,0xc95414f6fbb2a629edd6,0x64950539feecaa0a77bd,0x5906154e7ebb4a829ebd,0x67618553deec830aa7bd,0xdd8b6154f7ab16c2a9df,0xf763d8553faea7b0aa7b],#[0xbd1936154febb9ec2a9e,0xef664d8553deac9b0aa7,0x73f5d36154f7bb26c2a9,0x9ef772d8553deae5b0aa,0xa7bd5536154f7bb9ec2a,0xa9ef754d8553deca9b0a,0xaa7bd5d36154f7a3a6c2,0x4a9ef774d8553dece9b0,0x9aa73f5d36254efbb8ac,0xa8a9ddf7355153bbae9a,0x2a2a7cfd525454eeeb9c,0x2c8a9ebd6419153d7ec9,0x4b22a77ddc56454efdb8,0x24c8a9df57199153bdee,0xe5b22a73f5c76454f5fb,0xba6a729f5e54d4e539fa,0xce9a9ca7d75d35394eee,0x7b92c9a9ddd7395253eb,0xd8e4b26a73fdc564d4ef,0x7fb92c9a9eef7259353d,0x101d81801280b0078002,0x83c03883703182c02682,0x6685d05785204c847041,0x508187c07887506f86c0,0x89809489108f88a08688,0xaa8a70a38a209e89d099,0xf0bb8ba0b68b30b18b00,0x8d40ce8cd0cb8c80c28b,0xe68e50e18e00de8db0d9,0xf0fb8f80f48f10ed8ea0,0x91210e90d1099081048f,0x2a92712191e11a919115],#[0xd13993813493112d92c1,0x95415094f14b94614293,0x6c96b169966162959155,0x317f97e17897316f96e1,0x99a19699318d98a18698,0xb09a91a59a21a099d19b,0x71c39c01be9bb1b79b61,0x9d81d69d51d19ce1ca9c,0xf29ef1eb9e81e09dd1db,0x9205a04202a011ff9fa1,0xa2221ea1b217a1220ca0,0x30a2d229a28226a25223,0x7243a42240a3d23ba362,0xa5c258a55251a4c248a4,0x74a7126da6a264a6325f,0x9285a84282a7f27ba782,0xaa62a2a9d299a98292a8,0xbcabb2b5ab22aeaad2a9,0x32cface2ccac72c5ac42,0xae42e2add2d9ad82d6ad,0xf6af32efaec2eaae92e5,0x7305b02300afd2fbafa2,0xb1a316b1330fb0c30ab0,0xe00d0f27b24322b1f31d,0x83f8020f07e00f8010b,0xb078020ae00b80107e0,0x7e00b80103802c2100f,0xe0081f80207e0081c182,0x8020f090d0c101f80207,0x82c10b0408042e0041f,0x400200082c1002410341,0x81001c1001c100041030],#[0x4107040001004209040,0x81043d04281041c102,0x10400200080e8820,0x10904241230408101041,0x41034209041410424,0x4100081010410100101,0x504100002043c2420107,0x4104810a0c100041030,0x101000c100101030108,0x4105041046260071,0x41002d0c20b430804100,0x2042d042830410104050,0xc1014104001040003c10,0x1041c100080020342c10,0x21040410207041c10404,0x4003000400004002841,0x8a842c30404841090408,0x20b0424100000004a109,0x2c103048810321081084,0x17802000400100000000,0x1000410000004001e008,0x6101030484144030820,0x588104040c8420000103,0xb048810b058810b0,0xc0828442c1c0101c1,0x14160050c16260080c1,0x89803010c84243050c10,0x2041c100002000800025,0x8410006260090c10006,0x4000101c107041000400,0xc10b0400304021040210,0x400304003042c162040],#[0x2]]
def g95H6 := limbs80 #[#[0x1c380062c0861c1800b,0x58002084023c2651c0,0x621e4424eb2a5543a82e,0x8004088b092963f,0xf000850b27806d112450,0x4db17e410000000008a,0x52637c4ba828b1b15000,0x8043c32305000c040123,0xd01000a2bf36b4900011,0x31b14000000d1010e81c,0x8b48835007000953000b,0x74a00072f00033ac0f33,0x28cad000e4c024519d88,0xcc3d902c0c484703c097,0x31ed55342a1f34682293,0x3902dcb211a0004a3913,0x14f00a000f231511a2a,0x4333348a942000023b00,0x90d000f40b1b000c3e,0x511d72cd3010b0000000,0xe2ed26fae000000047c2,0x16]]
set_option maxRecDepth 16000 in
def g95D7 := limbs80 #[#[0xb58a43b798f41b758f41,0x58453be58053e7d0e43b,0x9053af59053bb58853bd,0x521d7d4e53bdd8553af9,0x31bf99521bf59521fd54,0x1bf59131f754d31fd545,0xfd50731bf99531bf5953,0xf59331f754f31fdd4731,0x54541bf99731bf59731b,0x9541ef55141ef50d41fd,0xf41ef50f41bf99541bf5,0x41bf59741ef55341bf58,0x1bfd8951fdd4551bf997,0xbfd8d51dfd4d51df54d5,0xf54f51bf58b51bfd9151,0x59351bf58f51dfd4f51d,0x8543bf99443bf59443bf,0x543f794d43f754d43bfd,0x43bf99543bf59543bf19,0x3bf59243f754e43bfd95,0xf754c53bf99643bf5964,0xd18553bf99453bf59053,0xd8953bfd8553fdd8553f,0x4e53bfd9153f7d4d53bf,0x753bf59653bf59253f7d,0x31bf59353bf58b53bf58,0x1ff55331ffd5131ff551,0xffd4d41ff54d41ffd533,0xf54951ffd4f41ff54f41,0x54d51ff50d51ff58951f,0x9151ff55151ff58d51ff,0xf51ff54f51ff50f51ff5],#[0x43ff59351ff55351ff58,0x3ff54d43ffd8543ff585,0xff59543ff19543ffd4d4,0xf55243ffd9543ff99543,0x95053ff55053ffd5243f,0x8953ffd8553ff58553ff,0x153ffd4d53ffd8953ff5,0x53ffd5153ff95153ff55,0x3ff99153ff59153ff191,0xffd5253ff95253ffd915,0x1b000ff99353ff59353,0x90e70c50a308105f03d,0x1d51b318a16814612b1,0x2a728c27124f22d20b1f,0x8e37335833630d2eb2c9,0xc45343140f3ed3d23b03,0x53a5184f64db4c049e47,0x1a5f85d65b459257755c,0xb7026e76cc69566c63c6,0x8137ea7c879f77d75472,0x18d88b689b88085e83c,0x69db9b299096e9459239,0xa98a7da62a4ea33a119f,0x55b33b1fb0bae9aceab3,0x4bf0bd5bbaba6b92b70b,0xcb4ca7c85c55c3ac18c0,0x94d79d65d3cd13cf1ccf,0x5e21e0ddf2dd0dbcda8d,0xec2ea7e9ae86e6be57e3,0x803890426010241c0283,0xb101c308202600e24411,0xe20b11803882c4600e20],#[0xc8c018809803882c4600,0x1478ec03441623007110,0x6863b00b1a2101e3b00d,0x82c4e01a20bc03431f80,0x64061300d1620f098068,0x83f04110201c1203c02,0x2058a130411020bc0244,0x12343463f00e10241c0,0xc2c41e0f00e105e01c1e,0xbc028389805070c1e01,0x162838380509047e0142,0xe12181c0404070700a,0xd107e01a18fc03431e37,0x80d1018ec03c4083f00,0xd105e00e18bc03431d8,0x1300710583c038416130,0x6162700d10404c01c410,0x588c01c5c42d0830980,0x38032004104078078e1,0x28202101e0148601e182,0x82c208c01c516104600e,0xc4082300716284118038,0x16284162300714588c01,0x1e010789c034408203e0,0xf102601a184c0343c486,0x5880808b07805200f00,0x118038a103e0102080f8,0x26020344098078d10584,0x70c2220e18104105e014,0x85890618444041882c48,0x307042062c3890c1890,0x88407850e0901e18b0e1],#[0x1e20f0e10f0e10407047,0x203170441e8848611141,0x4862d1090c5870858708,0x1080c4068420e2421688,0xd121401018c0c5840c5a,0xb080c31608b44850082,0x802c2161018812122062,0x3842c242830050909141,0x21634220342160d0863c,0x5042030d141080c4820c,0x210444850080c4850458,0x618b0420308584061a11,0xb042221]]
def g95H7 := limbs80 #[#[0x80520914050946f1a8c7,0x8c4c2ba632026403043,0x5405bc8001ada219037,0x58001980814002038494,0x6d6f3216602c2458401,0x2346fd80000001e9400,0x791e70a74000889e0400,0xfa10000000a,0xa4e000000148692f8,0x20c4000c300000000000,0x66ac196870000000108,0x3a04b5a1d1cb21964d17,0x9a542c2c15ecdca1763,0x22bc4e08e9b61625db,0x868e4d00a989916c0910,0xba9c9bcd080001740003,0x2d80000000000098f680,0xda000000,0xe8000000000000371f40,0x92255f28b8000461d1,0x87800000064400000000,0x1eb00007,0xf83c000a1a7701c24000,0xc19f151966cd88ecd51,0x3c80001c2b3d043a800,0x2b5400135400,0x6f86190a4c460004a500,0x15a0000000000c,0x45de328,0xb5b2c091720000000000,0xff140e6258c000f1122f,0x1f3e3d9bc800023573a],#[0xc1b6e3000000016d80,0x2ec7e6d000784c0000,0x6e6628603b56200061f0,0x1324b4be58d414032f4c,0x4a10000003b76000167,0x65cfbac00,0xc79430007004000aa900,0x3a58b400000044c0b150,0x5ac00043b2add5ce6373,0x2478001c627038b46,0x2599a95146800377be1d,0xd6ee20f4e200044f000,0x27866a1f9451dc3ac400,0x4e0007aa33226648b589,0x38460007562b87e176,0x28be203090d5a44ab4b0,0xb9de52744b83f8c74001,0x162700000001828bff39,0xfc1d691c681000013000,0x88000dce4155a6cc0201,0x3de896adecaa9572ccaa,0x10de0004968001edc4,0x48d5687cd00000002c7c,0xb8c4535c846858595,0x5af409581a991bf50398,0x19a488f3dd1a7c8cbae,0x38d17da8b298c7ca2780,0x1151b1c1b0003d363440,0x63c20b52d7262835743a,0x32c9d4c000000738fcc3,0x524324a99e00a000,0x880038ba83d355d80c00],#[0x1a69669800104000002,0x70e800027850a00000,0xb42ca970b64990,0x54d306000000035d68ec,0x30fc0002c080b89212a4,0xfa5800,0x588086a710681794e400,0x67598000000000710de,0x106c172390331b2c0008,0x4b5c0007e4e4de,0xd91fb58abd55e714c452,0x2464389fb52cd93e,0x1242076800000]]
def g95D8 := limbs80 #[#[0xf41fea0ffcc7fa63fd21,0x87fd43fe21ffd47faa3f,0x3fea7fe53fea9ff14ffc,0x3a998a8421989c300c00,0x3433a0343cc5eab92c84,0xa10780e0c9060204260,0x3a034504f3a03451c18,0x1c528980d1081201c405,0x4410204b2201c7084220,0x43e03451088071011203,0x40]]
def g95H8 := limbs80 #[#[0x2000131e0c4850801702,0xc1871e00c0e00141002,0x98000058281025802812,0xc74dc000000003c59080,0xc5a42b0f00031dd90fa,0x58c5cc0024d,0x10dd38a000000114d4fc,0xc0035e40034bc3a26404,0xc012b08742477a6cad9,0x2800307db99850001ca4,0xa9314e698904a17e0797,0x8c8ced04001539d11c1,0x945bc000ced035472da3,0x677ce3b640000020,0xb73800db4780881d8000,0x27271cb53311b0cd815f,0x61217a584446b1c31639,0x4f8cb0002093c1780995,0x43b9f35d6c0000857350,0xb77de6de69e8240f72ed,0xd4a03e4c753d95000355,0xa952c0027c54b8001e7a,0x5cf78380019a40740994,0xd039a8000003d87dbbd3,0x8559b85d9c400042dbc0,0xd685d800000201f089b,0x2dadc20d679e357000,0x77465c4d3ddd1c443334,0x7060002d95cd5d6f516d,0xc6f03149fd90508000d4,0xad62f9d44e95cac04002,0x38c800000257bd180034]]
def g95D9 (j : Nat) := if j=0 then 0x8200ff else 0
def g95H9 := limbs80 #[#[0x326c56d958009378021,0x3940db4b1ddd684003b0,0xbf9000038174c1a730cf,0xcc001ab2247b214a2]]
def g95L : Nat → Packing
  | 4 => (6,5,5,0,0,5,0,g95D4)
  | 5 => (86,4,5,0,0,10,0,g95D5)
  | 6 => (238,3,5,0,0,12,0,g95D6)
  | 7 => (122,2,5,0,0,12,0,g95D7)
  | 8 => (14,1,5,0,0,9,0,g95D8)
  | 9 => (1,0,5,0,0,0,0,g95D9)
  | _ => emptyPacking
def g95I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 53 0 7 3 0 g95H5
  | 6 => lookupWord 24 127 7 12 7 1 g95H6
  | 7 => lookupWord 74 443 5 13 8 1 g95H7
  | 8 => lookupWord 38 191 7 12 7 1 g95H8
  | 9 => lookupWord 6 31 5 9 4 1 g95H9
  | _ => fun _ => none
def g95 : Forest := ⟨95,9,fun i => g95Y[i]?.getD (0,0),g95C,g95A,g95L,g95I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95P4_0 : block g95 4 0 6=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g95B4 : block g95 4 0 6=true := g95P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95P5_0 : block g95 5 0 86=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g95B5 : block g95 5 0 86=true := g95P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95P6_0 : block g95 6 0 21=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95P6_21 : block g95 6 21 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95P6_117 : block g95 6 117 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95P6_213 : block g95 6 213 25=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g95B6 : block g95 6 0 238=true := (@block_merge g95 6 0 117 121 (@block_merge g95 6 0 21 96 g95P6_0 g95P6_21) (@block_merge g95 6 117 96 25 g95P6_117 g95P6_213))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95P7_0 : block g95 7 0 11=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95P7_11 : block g95 7 11 63=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95P7_74 : block g95 7 74 48=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g95B7 : block g95 7 0 122=true := (@block_merge g95 7 0 11 111 g95P7_0 (@block_merge g95 7 11 63 48 g95P7_11 g95P7_74))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95P8_0 : block g95 8 0 14=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g95B8 : block g95 8 0 14=true := g95P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95P9_0 : block g95 9 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g95B9 : block g95 9 0 1=true := g95P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95T : checkedTables g95 9 := by
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
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95G : graphValid g95 (boundsBefore K63) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low95 : Lower true (varsX 95) (graphGoal 95) 10 := lower_forest (g:=g95) (i:=0) (hints:=1075) (before_sound K63 V63) g95G g95T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K95 := extendKnown K63 10 [(95,[]),(187,[48,65,82,118])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V95 : Known true K95 := extend_ok (m:=95) V63 low95 (by decide +kernel)
def g111Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfff0007ffffff00ff5,0xb361d03e280001f0001f])),(BitVec.ofNat 152 (word80 [0x42a135092845216141,0xb261d01428294a5294a5]))),((BitVec.ofNat 152 (word80 [0xffffff8003fffff002,0x16e8554587003e007fe0])),(BitVec.ofNat 152 (word80 [0x4c02601b006424262,0x10605505810842108421]))),((BitVec.ofNat 152 (word80 [0xfffffffffc00000009,0xd8c2c299d107c00f8000])),(BitVec.ofNat 152 (word80 [0x17003801c017838381,0x98c24019d118c6318c63]))),((BitVec.ofNat 152 (word80 [0xfffffffffffffffffa,0x4fe283ab8f8000003ff])),(BitVec.ofNat 152 (word80 [0x980240120098000008,0x48a282a105294a5294a]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [9,0x1711a3877600000ffc00])),(BitVec.ofNat 152 (word80 [0xe00b805c02e0040408,0x711a28226e739ce739c]))),((BitVec.ofNat 152 (word80 [4,0xe9177e4005fffff00000])),(BitVec.ofNat 152 (word80 [0xc00600300080804,0x41140240048421084210]))),(0x0,0x0),(0x0,0x0)]
def g111C : List ColumnInfo := [(2,0,109,0,7),(4,0,107,0,7),(0,32,73,6,6),(1,0,110,0,6),(32,0,79,0,6),(8,0,103,0,5),(33,0,78,0,5),(64,0,47,0,5),(10,0,101,0,4),(65,0,46,0,4)]
def g111A : List (List Nat) := [[]]
def g111D5 := limbs80 #[#[0x31fb2aa8987595354130,0xeb2a7a86613edc1654c,0x4f3cb2ea1985d973d433,0x53d72a9b02a77c5c4605,0xe35cafb299a06ba54d81,0x183b]]
def g111D6 := limbs80 #[#[0xb58853bd58453be58053,0x54130d7d4e53bed8153b,0x5130f794d30f754d30fe,0x330bfd9530bf59530ef5,0x30ef55330f754f30fed4,0xdf54f50df54d50bf597,0xfed8153fe18153bf58f5,0xf95153ef55153bfd8153,0x95253ef55253bf58253e,0x481e0a83000bf59653ef,0x509c4b241147e3c1b0c0,0xf1d4e46c34998c05a2b9,0x39010b80e1c9a350e843,0x608e08a3e01e008f804,0x60860800060800003820,0x38204608f18400608000,0x182382]]
def g111H6 := limbs80 #[#[0x2100000000000000002,0x8300000065000000000,0x87000,0x921866000000c400000,0xe00]]
def g111D7 := limbs80 #[#[0xd50ff987f4c37ca9bd54,0xa7fe53fea9ff14ffea1f,0xd0bf4d9f0ba3e0f803fe,0x478c0c291228c059d445,0x82453c60628a72c60614,0x828c1239451818e314d1,0x8a3028e410ce58c07194,0xa41460918e41]]
def g111H7 := limbs80 #[#[0x800e0c2334000020420c,0xc6002e65af1ba,0x6b80000d600000000000,0xccd4800b4000000000,0x93122ebd0f2cbc00,0x388880001c900000,0x179dd600000000000000,0x708000000000000000d,0x29c0]]
def g111D8 (j : Nat) := if j=0 then 0x3421017f else 0
def g111H8 := limbs80 #[#[0x10003d80000007,0x2162401c400cc000001a,0x21c00000000014b9]]
def g111L : Nat → Packing
  | 5 => (9,3,4,0,0,6,0,g111D5)
  | 6 => (27,2,4,0,0,9,0,g111D6)
  | 7 => (10,1,4,0,0,9,0,g111D7)
  | 8 => (1,0,4,0,0,0,0,g111D8)
  | _ => emptyPacking
def g111I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 2 47 2 8 4 0 g111H6
  | 7 => lookupWord 6 71 4 9 5 0 g111H7
  | 8 => lookupWord 2 29 3 8 4 0 g111H8
  | _ => fun _ => none
def g111 : Forest := ⟨111,8,fun i => g111Y[i]?.getD (0,0),g111C,g111A,g111L,g111I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P5_0 : block g111 5 0 9=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g111B5 : block g111 5 0 9=true := g111P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P6_0 : block g111 6 0 5=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P6_5 : block g111 6 5 22=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g111B6 : block g111 6 0 27=true := (@block_merge g111 6 0 5 22 g111P6_0 g111P6_5)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P7_0 : block g111 7 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P7_2 : block g111 7 2 8=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g111B7 : block g111 7 0 10=true := (@block_merge g111 7 0 2 8 g111P7_0 g111P7_2)
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
  · exact g111B5
  · exact g111B6
  · exact g111B7
  · exact g111B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111G : graphValid g111 (boundsBefore K95) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low111 : Lower true (varsX 111) (graphGoal 111) 9 := lower_forest (g:=g111) (i:=0) (hints:=1049907) (before_sound K95 V95) g111G g111T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K111 := extendKnown K95 9 [(111,[]),(119,[33,67])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V111 : Known true K111 := extend_ok (m:=111) V95 low111 (by decide +kernel)
def g123Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x1ffffffffffff00ff5,0x30e690b8f80001f07c1f])),(BitVec.ofNat 152 (word80 [0x408502080010202001,0x30241090c8294a5294a5]))),((BitVec.ofNat 152 (word80 [0xe0007ffc03fffff00a,0x6a955c7c2003e0f83e0])),(BitVec.ofNat 152 (word80 [0x802600100802400022,0xa05506c018c6318c63]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffff800003fffffffb,0x497889211e07c00003ff])),(BitVec.ofNat 152 (word80 [0x50814a0b0a4828288,0x9588821124210842108]))),((BitVec.ofNat 152 (word80 [0xfffffffffc00000008,0x94d06b1ab3f800007c00])),(BitVec.ofNat 152 (word80 [0x63018c120c704c4c8,0x84d04b0a325294a5294a]))),((BitVec.ofNat 152 (word80 [9,0x1717a2877400000f8000])),(BitVec.ofNat 152 (word80 [0x17c05f01c2f8070709,0x1717a28134e739ce739c]))),((BitVec.ofNat 152 (word80 [4,0xe9177e4005fffff00000])),(BitVec.ofNat 152 (word80 [0x180060020300080804,0x40032040058421084210]))),(0x0,0x0),(0x0,0x0)]
def g123C : List ColumnInfo := [(8,0,115,0,7),(16,0,107,0,7),(32,0,91,0,7),(0,32,89,2,6),(1,0,122,0,6),(2,0,89,0,5),(2,32,89,0,5),(64,0,59,0,5)]
def g123A : List (List Nat) := [[]]
def g123D5 := limbs80 #[#[0x26fb9aca884ef7259510,0xd3aa9b1aa1a7d8e4154,0x26fb9ac1a8cbd769075,0xf624c3]]
def g123D6 := limbs80 #[#[0xe54110af59641b7d8d50,0xd9510bf59510fd54510f,0x8d50bfd8550ef90550bf,0x750ef90750ef55150f7d,0xbf58351bfd8151bf58,0xaa9a8f7f74644a352010,0x7a49c32e02d602d0caba,0x4144118821882010c450,0x4100620a830a9108208c]]
def g123H6 := limbs80 #[#[0xd80,0x74000000000000009000,0x2c01000360000]]
def g123D7 := limbs80 #[#[0xf50fea87f4437aa9be41,0x38291a0b007fd47faa3f,0xc33964c30d930a25849,0xa69350e3bad24c0ce953,0x8530ec33a54c30c]]
def g123H7 := limbs80 #[#[0x32c00000001280000030,0xd7400025002800001f00,0x400d40000000000025b4,0x35c03a286c802a]]
def g123D8 (j : Nat) := if j=0 then 0x685017f else 0
def g123H8 := limbs80 #[#[0x78000000000d8580,0x29000,0x40000000011000020000,0x13]]
def g123L : Nat → Packing
  | 5 => (6,3,3,0,0,5,0,g123D5)
  | 6 => (14,2,3,0,0,8,0,g123D6)
  | 7 => (7,1,3,0,0,8,0,g123D7)
  | 8 => (1,0,3,0,0,0,0,g123D8)
  | _ => emptyPacking
def g123I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 31 0 7 3 0 g123H6
  | 7 => lookupWord 3 37 2 8 4 0 g123H7
  | 8 => lookupWord 1 37 0 7 3 0 g123H8
  | _ => fun _ => none
def g123 : Forest := ⟨123,8,fun i => g123Y[i]?.getD (0,0),g123C,g123A,g123L,g123I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P5_0 : block g123 5 0 6=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g123B5 : block g123 5 0 6=true := g123P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P6_0 : block g123 6 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P6_2 : block g123 6 2 12=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g123B6 : block g123 6 0 14=true := (@block_merge g123 6 0 2 12 g123P6_0 g123P6_2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P7_0 : block g123 7 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P7_2 : block g123 7 2 5=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g123B7 : block g123 7 0 7=true := (@block_merge g123 7 0 2 5 g123P7_0 g123P7_2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P8_0 : block g123 8 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g123B8 : block g123 8 0 1=true := g123P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123T : checkedTables g123 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g123 0 0 0 = true)
  · exact (rfl : block g123 1 0 0 = true)
  · exact (rfl : block g123 2 0 0 = true)
  · exact (rfl : block g123 3 0 0 = true)
  · exact (rfl : block g123 4 0 0 = true)
  · exact g123B5
  · exact g123B6
  · exact g123B7
  · exact g123B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123G : graphValid g123 (boundsBefore K111) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low123 : Lower true (varsX 123) (graphGoal 123) 9 := lower_forest (g:=g123) (i:=0) (hints:=1048627) (before_sound K111 V111) g123G g123T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K123 := extendKnown K111 9 [(123,[]),(125,[33,67]),(159,[48,65,82,118])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V123 : Known true K123 := extend_ok (m:=123) V111 low123 (by decide +kernel)
def g126Y : Array (Bits × Bits) := #[(0x0,0x0),((BitVec.ofNat 152 (word80 [0x7fffffe01fffff7,0x22ca982eb80001f07c1f])),(BitVec.ofNat 152 (word80 [0x25002800404022003,0x2080180ca8294a5294a5]))),((BitVec.ofNat 152 (word80 [0xfff8003ffffffff00b,0x942915d9c2003e0f83e0])),(BitVec.ofNat 152 (word80 [0x600b002800004023,0x802815094018c6318c63]))),((BitVec.ofNat 152 (word80 [0xffffffc00001fffffa,0xd9dc81211e07c000001f])),(BitVec.ofNat 152 (word80 [0x28814c0ab058548288,0x995c8121125294a5294a]))),((BitVec.ofNat 152 (word80 [0xfffffffffffe000008,0x4f46b1ab3f8000003e0])),(BitVec.ofNat 152 (word80 [0x3301900cc0906704c8,0x4d40a12b36318c6318c]))),((BitVec.ofNat 152 (word80 [9,0x1713a2877400000ffc00])),(BitVec.ofNat 152 (word80 [0xbc05e02f00e1780708,0x1713a28214c6318c6318]))),((BitVec.ofNat 152 (word80 [4,0xe9177e4005fffff00000])),(BitVec.ofNat 152 (word80 [0xc00600300101800804,0x40036040048421084210]))),(0x0,0x0),(0x0,0x0)]
def g126C : List ColumnInfo := [(32,0,94,0,8)]
def g126A : List (List Nat) := [[],[33,67]]
def g126D8 (j : Nat) := if j=0 then 0x7f else 0
def g126L : Nat → Packing
  | 8 => (1,0,1,0,0,0,0,g126D8)
  | _ => emptyPacking
def g126I (_ _ : Nat) : Option (Nat × Nat) := none
def g126 : Forest := ⟨126,8,fun i => g126Y[i]?.getD (0,0),g126C,g126A,g126L,g126I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P8_0 : block g126 8 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g126B8 : block g126 8 0 1=true := g126P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126T : checkedTables g126 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g126 0 0 0 = true)
  · exact (rfl : block g126 1 0 0 = true)
  · exact (rfl : block g126 2 0 0 = true)
  · exact (rfl : block g126 3 0 0 = true)
  · exact (rfl : block g126 4 0 0 = true)
  · exact (rfl : block g126 5 0 0 = true)
  · exact (rfl : block g126 6 0 0 = true)
  · exact (rfl : block g126 7 0 0 = true)
  · exact g126B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126G : graphValid g126 (boundsBefore K123) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low126 : Lower true (varsX 126) (graphGoal 126) 9 := lower_forest (g:=g126) (i:=0) (hints:=17962032) (before_sound K123 V123) g126G g126T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K126 := extendKnown K123 9 [(126,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V126 : Known true K126 := extend_ok (m:=126) V123 low126 (by decide +kernel)
def g207Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x807ffff800fffffe03,0xfc8f2a513a000f000f0f])),(BitVec.ofNat 152 (word80 [0xb0a01506a0940a458,0xa48b0a50321111111111]))),((BitVec.ofNat 152 (word80 [0xff807fffff001ffffc,0x39b89984500f000f0f0])),(BitVec.ofNat 152 (word80 [0x121302604c0d80c891,0x339b8810411111111111]))),((BitVec.ofNat 152 (word80 [0x7fffffffe00000,0x6b760e4a500000f0000])),(BitVec.ofNat 152 (word80 [0x1c1c4b84708e12f0e1,0xc6b760e4a5bbbbbbbbbb]))),((BitVec.ofNat 152 (word80 [0x7fffffffffffff,0xf9627987230f00f000ff])),(BitVec.ofNat 152 (word80 [0x20200c008010030000,0x207183002222222222]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffff80000000000000,0x98c46290f000ffff00])),(BitVec.ofNat 152 (word80 [0x10010020040000,0x4444444444]))),(0x665163c4cffff000000,(BitVec.ofNat 152 (word80 [0x4040600600c0180102,0x44042c0c8888888888]))),(0x0,0x0)]
def g207C : List ColumnInfo := [(1,0,206,0,8)]
def g207A : List (List Nat) := [[],[115],[16],[16,115]]
def g207D8 (j : Nat) := if j=0 then 0x7f else 0
def g207L : Nat → Packing
  | 8 => (1,0,1,0,0,0,0,g207D8)
  | _ => emptyPacking
def g207I (_ _ : Nat) : Option (Nat × Nat) := none
def g207 : Forest := ⟨207,8,fun i => g207Y[i]?.getD (0,0),g207C,g207A,g207L,g207I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g207P8_0 : block g207 8 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g207B8 : block g207 8 0 1=true := g207P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g207T : checkedTables g207 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g207 0 0 0 = true)
  · exact (rfl : block g207 1 0 0 = true)
  · exact (rfl : block g207 2 0 0 = true)
  · exact (rfl : block g207 3 0 0 = true)
  · exact (rfl : block g207 4 0 0 = true)
  · exact (rfl : block g207 5 0 0 = true)
  · exact (rfl : block g207 6 0 0 = true)
  · exact (rfl : block g207 7 0 0 = true)
  · exact g207B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g207G : graphValid g207 (boundsBefore K126) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low207 : Lower true (varsX 207) (graphGoal 207) 9 := lower_forest (g:=g207) (i:=0) (hints:=1587) (before_sound K126 V126) g207G g207T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K207 := extendKnown K126 9 [(207,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V207 : Known true K207 := extend_ok (m:=207) V126 low207 (by decide +kernel)
def g215Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x807ffff800fff01fff,0xfd8f23511a000f000f0f])),(BitVec.ofNat 152 (word80 [0xb0a01506a04a34148,0xa58b2250121111111111]))),((BitVec.ofNat 152 (word80 [0xff807fffff00001ffc,0x3bbc1984500f000f000])),(BitVec.ofNat 152 (word80 [0x12130a604c16c58191,0x33bbc190413333333333]))),((BitVec.ofNat 152 (word80 [0x7fffffffffe000,0x69728e4a500000f00f0])),(BitVec.ofNat 152 (word80 [0x1c1c438470870611e1,0xc6972864859999999999]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x7fffffffffffff,0xf9627987230f00f000ff])),(BitVec.ofNat 152 (word80 [0x20200c008018000200,0x205183202222222222]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffff80000000000000,0x98c46290f000ffff00])),(BitVec.ofNat 152 (word80 [0x10010020000400,0x4444444444]))),(0x665163c4cffff000000,(BitVec.ofNat 152 (word80 [0x4040600600c0081802,0x44042c0c8888888888]))),(0x0,0x0)]
def g215C : List ColumnInfo := [(2,0,213,0,8)]
def g215A : List (List Nat) := [[],[33,116]]
def g215D8 (j : Nat) := if j=0 then 0x7f else 0
def g215L : Nat → Packing
  | 8 => (1,0,1,0,0,0,0,g215D8)
  | _ => emptyPacking
def g215I (_ _ : Nat) : Option (Nat × Nat) := none
def g215 : Forest := ⟨215,8,fun i => g215Y[i]?.getD (0,0),g215C,g215A,g215L,g215I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g215P8_0 : block g215 8 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g215B8 : block g215 8 0 1=true := g215P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g215T : checkedTables g215 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g215 0 0 0 = true)
  · exact (rfl : block g215 1 0 0 = true)
  · exact (rfl : block g215 2 0 0 = true)
  · exact (rfl : block g215 3 0 0 = true)
  · exact (rfl : block g215 4 0 0 = true)
  · exact (rfl : block g215 5 0 0 = true)
  · exact (rfl : block g215 6 0 0 = true)
  · exact (rfl : block g215 7 0 0 = true)
  · exact g215B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g215G : graphValid g215 (boundsBefore K207) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low215 : Lower true (varsX 215) (graphGoal 215) 9 := lower_forest (g:=g215) (i:=0) (hints:=1124) (before_sound K207 V207) g215G g215T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K215 := extendKnown K207 9 [(215,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V215 : Known true K215 := extend_ok (m:=215) V207 low215 (by decide +kernel)
def g219Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xf87ffe01fffffff1e6,0x3147300000f8000ffc1f])),(BitVec.ofNat 152 (word80 [0x110014140a02002420,0x11463084210842108421]))),((BitVec.ofNat 152 (word80 [0xff87fffe00ff1ffe1a,0xfec10001f0001f003e0])),(BitVec.ofNat 152 (word80 [0x201098184c0442409a,0x5ec118c6318c6318c63]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x7ffffff001fffc4,0xead8a003e0003e0003ff])),(BitVec.ofNat 152 (word80 [0x422120201028848004,0xea108210842108421084]))),((BitVec.ofNat 152 (word80 [0x7ffffffffe00013,0x6c0fc07c0007c0007c00])),(BitVec.ofNat 152 (word80 [0x8441c0406030070913,0x6c09c318c6318c6318c6]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfff800000000000029,0x84009f800007ffff8000])),(BitVec.ofNat 152 (word80 [0x200808040080000,0x421084210842108]))),((BitVec.ofNat 152 (word80 [0x10,0x51304ffffff800000000])),(BitVec.ofNat 152 (word80 [0x401010080100000,0x842108421084210]))),(0x0,0x0)]
def g219C : List ColumnInfo := [(1,0,218,0,8),(2,0,217,0,8),(8,0,211,0,8),(16,0,203,0,8),(64,0,155,0,7),(128,0,91,0,7)]
def g219A : List (List Nat) := [[],[118],[48,65],[48,65,118]]
def g219D8 (j : Nat) := if j=0 then 0x2a5cd40dfd54 else 0
def g219D9 (j : Nat) := if j=0 then 0x2c6501bf else 0
def g219H9 (j : Nat) := if j=0 then 0x7 else 0
def g219L : Nat → Packing
  | 8 => (1,1,3,0,0,0,0,g219D8)
  | 9 => (1,0,3,0,0,0,0,g219D9)
  | _ => emptyPacking
def g219I : Nat → Nat → Option (Nat × Nat)
  | 9 => lookupWord 1 2 0 4 0 0 g219H9
  | _ => fun _ => none
def g219 : Forest := ⟨219,9,fun i => g219Y[i]?.getD (0,0),g219C,g219A,g219L,g219I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P8_0 : block g219 8 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g219B8 : block g219 8 0 1=true := g219P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P9_0 : block g219 9 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g219B9 : block g219 9 0 1=true := g219P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219T : checkedTables g219 9 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g219 0 0 0 = true)
  · exact (rfl : block g219 1 0 0 = true)
  · exact (rfl : block g219 2 0 0 = true)
  · exact (rfl : block g219 3 0 0 = true)
  · exact (rfl : block g219 4 0 0 = true)
  · exact (rfl : block g219 5 0 0 = true)
  · exact (rfl : block g219 6 0 0 = true)
  · exact (rfl : block g219 7 0 0 = true)
  · exact g219B8
  · exact g219B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219G : graphValid g219 (boundsBefore K215) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low219 : Lower true (varsX 219) (graphGoal 219) 10 := lower_forest (g:=g219) (i:=0) (hints:=51) (before_sound K215 V215) g219G g219T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K219 := extendKnown K215 10 [(219,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V219 : Known true K219 := extend_ok (m:=219) V215 low219 (by decide +kernel)
def g221Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfffc01ffffe1ffff32,0x82cb330000f8000f83ff])),(BitVec.ofNat 152 (word80 [0x2814050044002012,0x28b1004210842108421]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x1ffffe007ffe1ff059,0x29c78a80000001f07c00])),(BitVec.ofNat 152 (word80 [0x50b219164280504259,0x9c78a4e739ce739ce73]))),((BitVec.ofNat 152 (word80 [0x1fffffff80001fffed,0xb0415c001f003e00001f])),(BitVec.ofNat 152 (word80 [0x82c020180b0882802d,0xb0404c18c6318c6318c6]))),((BitVec.ofNat 152 (word80 [0x1fffffffffffe00010,0xfe246883e007c0007fe0])),(BitVec.ofNat 152 (word80 [0x30040200c00030400,0xf0206090842108421084]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xe0000000000000000e,0x1132807c0007ffff8000])),(BitVec.ofNat 152 (word80 [0x40080401000040000,0x21084210842108]))),((BitVec.ofNat 152 (word80 [0xc1,0x459c477ffff800000000])),(BitVec.ofNat 152 (word80 [0x1803018060111808c0,0x5140342108421084210]))),(0x0,0x0)]
def g221C : List ColumnInfo := [(4,0,217,0,8),(8,0,213,0,8),(16,0,205,0,8),(1,0,220,0,7),(64,0,157,0,7),(128,0,93,0,7),(0,4,137,80,6),(5,0,216,0,5),(64,4,137,16,5),(129,0,92,0,5),(65,0,156,0,4),(192,0,29,0,4)]
def g221A : List (List Nat) := [[],[112]]
def g221D5 (j : Nat) := if j=0 then 0x2f8e097550110 else 0
def g221D6 := limbs80 #[#[0x379b2a80887b15450110,0x9dee4b2a81ce5515050,0x2f7b92caa07f1755011,0x471eda965201bbdc9655,0x2d43f211a8ae22390b53,0x42ab8f97010471e4244e,0x1040622]]
def g221H6 (j : Nat) := if j=0 then 0x90 else 0
def g221D7 := limbs80 #[#[0xdd9510bd59510fc50110,0x55140fe54140fd55110b,0x9540bfd9540bf59540ef,0xa3a9688a331205400ff5,0xc79102141eb8e440d388,0x232b8c79102e2ae4388a,0x50986392b19054846391,0xe18e450a595813962316,0x16522488a]]
def g221H7 := limbs80 #[#[0x4518600d250d30000658,0x83]]
def g221D8 := limbs80 #[#[0x88aeb807f543fa81f510,0x2aa41c6121c07356838c,0x10708c923]]
def g221H8 := limbs80 #[#[0xd00000908000000,0x0,0x18400d980c00e6c3800,0xc5000000000000,0x0,0x2480,0x21000200000]]
def g221D9 (j : Nat) := if j=0 then 0x5431201bf else 0
def g221H9 := limbs80 #[#[0x20006200036000000000,0x1a000700]]
def g221L : Nat → Packing
  | 5 => (1,4,4,0,0,0,0,g221D5)
  | 6 => (7,3,4,0,0,8,0,g221D6)
  | 7 => (9,2,4,0,0,9,0,g221D7)
  | 8 => (3,1,4,0,0,7,0,g221D8)
  | 9 => (1,0,4,0,0,0,0,g221D9)
  | _ => emptyPacking
def g221I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 2 0 4 0 0 g221H6
  | 7 => lookupWord 2 11 2 8 3 1 g221H7
  | 8 => lookupWord 2 59 0 9 4 1 g221H8
  | 9 => lookupWord 1 19 0 7 2 1 g221H9
  | _ => fun _ => none
def g221 : Forest := ⟨221,9,fun i => g221Y[i]?.getD (0,0),g221C,g221A,g221L,g221I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g221P5_0 : block g221 5 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g221B5 : block g221 5 0 1=true := g221P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g221P6_0 : block g221 6 0 4=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g221P6_4 : block g221 6 4 3=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g221B6 : block g221 6 0 7=true := (@block_merge g221 6 0 4 3 g221P6_0 g221P6_4)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g221P7_0 : block g221 7 0 3=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g221P7_3 : block g221 7 3 5=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g221P7_8 : block g221 7 8 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g221B7 : block g221 7 0 9=true := (@block_merge g221 7 0 3 6 g221P7_0 (@block_merge g221 7 3 5 1 g221P7_3 g221P7_8))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g221P8_0 : block g221 8 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g221P8_1 : block g221 8 1 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g221B8 : block g221 8 0 3=true := (@block_merge g221 8 0 1 2 g221P8_0 g221P8_1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g221P9_0 : block g221 9 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g221B9 : block g221 9 0 1=true := g221P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g221T : checkedTables g221 9 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g221 0 0 0 = true)
  · exact (rfl : block g221 1 0 0 = true)
  · exact (rfl : block g221 2 0 0 = true)
  · exact (rfl : block g221 3 0 0 = true)
  · exact (rfl : block g221 4 0 0 = true)
  · exact g221B5
  · exact g221B6
  · exact g221B7
  · exact g221B8
  · exact g221B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g221G : graphValid g221 (boundsBefore K219) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low221 : Lower true (varsX 221) (graphGoal 221) 10 := lower_forest (g:=g221) (i:=0) (hints:=1027) (before_sound K219 V219) g221G g221T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K221 := extendKnown K219 10 [(221,[]),(235,[48,33,81,65,118])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V221 : Known true K221 := extend_ok (m:=221) V219 low221 (by decide +kernel)
def g222Y : Array (Bits × Bits) := #[(0x0,0x0),((BitVec.ofNat 152 (word80 [0xff801ffffe1fff94a6,0x1d94b00003f00003f03f])),(BitVec.ofNat 152 (word80 [0x450940500441101486,0xc80b145145145145145]))),((BitVec.ofNat 152 (word80 [0xffffe007fffff83a0a,0x978b5000000000fc0fc0])),(BitVec.ofNat 152 (word80 [0x164191642810213a02,0x978948e38e38e38e38e3]))),((BitVec.ofNat 152 (word80 [0xfffffff8001ffff968,0x38516000fc003f00003f])),(BitVec.ofNat 152 (word80 [0x98020180b082406928,0x3051028a28a28a28a28a]))),((BitVec.ofNat 152 (word80 [0xffffffffffe000063f,0xa863103f000fc0000fc0])),(BitVec.ofNat 152 (word80 [0xe00c0200c00382043c,0x2862130c30c30c30c30c]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x984,0x66280fc0000ffffff000])),(BitVec.ofNat 152 (word80 [0x1004010004000000,0x410410410410410]))),((BitVec.ofNat 152 (word80 [0x6651,0x43c4cffffff000000000])),(BitVec.ofNat 152 (word80 [0x6018060118040241,0x43044820820820820820]))),(0x0,0x0)]
def g222C : List ColumnInfo := [(4,0,218,0,8),(16,0,206,0,8),(128,0,94,0,8),(2,0,220,0,7),(8,0,214,0,7),(64,0,158,0,7),(10,0,212,0,5),(66,0,156,0,4),(72,0,150,0,4)]
def g222A : List (List Nat) := [[],[49]]
def g222D6 := limbs80 #[#[0xe3c1243e437a94250120,0x5]]
def g222D7 := limbs80 #[#[0xf50940bf59120fe50120,0x42a00ff58940bfd8940e,0xc32187c70572186ae8a5,0x481c5c705328c82071b1,0x81c60d4c31c871]]
def g222H7 (j : Nat) := if j=0 then 0x20 else 0
def g222D8 := limbs80 #[#[0xa38c2461a403fa81fd20,0x1e851c6121c]]
def g222H8 (j : Nat) := if j=0 then 0x44f3f1e00092000000f8 else 0
def g222D9 (j : Nat) := if j=0 then 0x5431021bf else 0
def g222H9 (j : Nat) := if j=0 then 0x653 else 0
def g222L : Nat → Packing
  | 6 => (1,3,4,0,0,0,0,g222D6)
  | 7 => (5,2,4,0,0,8,0,g222D7)
  | 8 => (2,1,4,0,0,6,0,g222D8)
  | 9 => (1,0,4,0,0,0,0,g222D9)
  | _ => emptyPacking
def g222I : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 1 2 0 4 0 0 g222H7
  | 8 => lookupWord 1 11 0 8 3 1 g222H8
  | 9 => lookupWord 1 3 0 6 1 1 g222H9
  | _ => fun _ => none
def g222 : Forest := ⟨222,9,fun i => g222Y[i]?.getD (0,0),g222C,g222A,g222L,g222I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g222P6_0 : block g222 6 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g222B6 : block g222 6 0 1=true := g222P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g222P7_0 : block g222 7 0 4=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g222P7_4 : block g222 7 4 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g222B7 : block g222 7 0 5=true := (@block_merge g222 7 0 4 1 g222P7_0 g222P7_4)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g222P8_0 : block g222 8 0 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g222B8 : block g222 8 0 2=true := g222P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g222P9_0 : block g222 9 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g222B9 : block g222 9 0 1=true := g222P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g222T : checkedTables g222 9 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g222 0 0 0 = true)
  · exact (rfl : block g222 1 0 0 = true)
  · exact (rfl : block g222 2 0 0 = true)
  · exact (rfl : block g222 3 0 0 = true)
  · exact (rfl : block g222 4 0 0 = true)
  · exact (rfl : block g222 5 0 0 = true)
  · exact g222B6
  · exact g222B7
  · exact g222B8
  · exact g222B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g222G : graphValid g222 (boundsBefore K221) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low222 : Lower true (varsX 222) (graphGoal 222) 10 := lower_forest (g:=g222) (i:=0) (hints:=285348912) (before_sound K221 V221) g222G g222T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K222 := extendKnown K221 10 [(222,[]),(243,[32,16,81,67,49,118])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V222 : Known true K222 := extend_ok (m:=222) V221 low222 (by decide +kernel)
def g231Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfffff8003ffc03ffc0,0x28e1a490ae7000f00f00])),(BitVec.ofNat 152 (word80 [0x1409505a8128681485,0xa841a4908e5333333333]))),((BitVec.ofNat 152 (word80 [0xffffffc00003ffff,0xdb59298254c00f00f00f])),(BitVec.ofNat 152 (word80 [0x2602601301b0b01909,0x1941088054c111111111]))),((BitVec.ofNat 152 (word80 [0xfffffffffffc0000,0x7638e0d9940000f00f0])),(BitVec.ofNat 152 (word80 [0x3883841c21c0c21e0e,0x3638e08914999999999]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffffffffffff,0xc8137847ab90f00000ff])),(BitVec.ofNat 152 (word80 [0x402c01600a0000a000,0x1070072a1666666666]))),((BitVec.ofNat 152 (word80 [0xff0000000000000000,0x45c463c762f000fff00])),(BitVec.ofNat 152 (word80 [0x3001800c0100c010,0x41c4004202444444444]))),(0x33a4d3e0015ffff00000,(BitVec.ofNat 152 (word80 [0x80c006003002030020,0x2a00360010888888888]))),(0x0,0x0)]
def g231C : List ColumnInfo := [(4,0,227,0,7)]
def g231A : List (List Nat) := [[]]
def g231D7 (j : Nat) := if j=0 then 0x7f else 0
def g231L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g231D7)
  | _ => emptyPacking
def g231I (_ _ : Nat) : Option (Nat × Nat) := none
def g231 : Forest := ⟨231,7,fun i => g231Y[i]?.getD (0,0),g231C,g231A,g231L,g231I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g231P7_0 : block g231 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g231B7 : block g231 7 0 1=true := g231P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g231T : checkedTables g231 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g231 0 0 0 = true)
  · exact (rfl : block g231 1 0 0 = true)
  · exact (rfl : block g231 2 0 0 = true)
  · exact (rfl : block g231 3 0 0 = true)
  · exact (rfl : block g231 4 0 0 = true)
  · exact (rfl : block g231 5 0 0 = true)
  · exact (rfl : block g231 6 0 0 = true)
  · exact g231B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g231G : graphValid g231 (boundsBefore K222) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low231 : Lower true (varsX 231) (graphGoal 231) 8 := lower_forest (g:=g231) (i:=0) (hints:=1049942) (before_sound K222 V222) g231G g231T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K231 := extendKnown K222 8 [(231,[]),(252,[48,65,82,118])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V231 : Known true K231 := extend_ok (m:=231) V222 low231 (by decide +kernel)
def g237Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xc007ffffe0ffff7224,0xa70baa00000fc003f03f])),(BitVec.ofNat 152 (word80 [0x82500a004204403200,0x25032a05145145145145]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfff800ffffffe03d48,0x8e6630c0000000fc0fc0])),(BitVec.ofNat 152 (word80 [0x20642c828080823d08,0x8e4210638e38e38e38e3]))),((BitVec.ofNat 152 (word80 [0xffffff0000ffffad86,0xb058468003f03f00003f])),(BitVec.ofNat 152 (word80 [0x80300b0409000506,0x9058048a28a28a28a28a]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffffff0000804d,0x6156adc0fc0000000fc0])),(BitVec.ofNat 152 (word80 [0xb01402c002e048045,0x2114ad9c71c71c71c71c]))),((BitVec.ofNat 152 (word80 [0x9171,0x18b1d83f00003ffff000])),(BitVec.ofNat 152 (word80 [0xc0180300830088071,0x20c010410410410410]))),((BitVec.ofNat 152 (word80 [0x4e93,0x4f80057fffffc0000000])),(BitVec.ofNat 152 (word80 [0x300600c010c0104880,0x4a800060820820820820]))),(0x0,0x0)]
def g237C : List ColumnInfo := [(4,0,233,0,8)]
def g237A : List (List Nat) := [[],[82,118],[48],[48,82,118]]
def g237D8 (j : Nat) := if j=0 then 0x7f else 0
def g237L : Nat → Packing
  | 8 => (1,0,1,0,0,0,0,g237D8)
  | _ => emptyPacking
def g237I (_ _ : Nat) : Option (Nat × Nat) := none
def g237 : Forest := ⟨237,8,fun i => g237Y[i]?.getD (0,0),g237C,g237A,g237L,g237I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P8_0 : block g237 8 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g237B8 : block g237 8 0 1=true := g237P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237T : checkedTables g237 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g237 0 0 0 = true)
  · exact (rfl : block g237 1 0 0 = true)
  · exact (rfl : block g237 2 0 0 = true)
  · exact (rfl : block g237 3 0 0 = true)
  · exact (rfl : block g237 4 0 0 = true)
  · exact (rfl : block g237 5 0 0 = true)
  · exact (rfl : block g237 6 0 0 = true)
  · exact (rfl : block g237 7 0 0 = true)
  · exact g237B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237G : graphValid g237 (boundsBefore K231) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low237 : Lower true (varsX 237) (graphGoal 237) 9 := lower_forest (g:=g237) (i:=0) (hints:=2098435) (before_sound K231 V231) g237G g237T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K237 := extendKnown K231 9 [(237,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V237 : Known true K237 := extend_ok (m:=237) V231 low237 (by decide +kernel)
def g238Y : Array (Bits × Bits) := #[(0x0,0x0),((BitVec.ofNat 152 (word80 [0xf801fffff83fffffc8,0xd40ac1c0007c00f83ff])),(BitVec.ofNat 152 (word80 [0x5014028010800103c0,0x8400014210842108421]))),((BitVec.ofNat 152 (word80 [0xfffe003fffc1ff81d7,0x214153a8000001f07c00])),(BitVec.ofNat 152 (word80 [0x64190b20a0050209d6,0x2141430a739ce739ce73]))),((BitVec.ofNat 152 (word80 [0xffffffc00001fffc97,0xc5b4444400f83e00001f])),(BitVec.ofNat 152 (word80 [0x80200c02c108140007,0x45a44400c6318c6318c6]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffffffffe000021,0x2edc7a201f0000007fe0])),(BitVec.ofNat 152 (word80 [0x140500b0000581021,0x49c38218c6318c6318c]))),((BitVec.ofNat 152 (word80 [0x44,0x903f89b3e0003fff8000])),(BitVec.ofNat 152 (word80 [0x180600c0210602000,0x901888a1084210842108]))),((BitVec.ofNat 152 (word80 [0x33a,0x528a034bffffc0000000])),(BitVec.ofNat 152 (word80 [0x60180300421804018,0x202034a108421084210]))),(0x0,0x0)]
def g238C : List ColumnInfo := [(4,0,234,0,8)]
def g238A : List (List Nat) := [[],[113]]
def g238D8 (j : Nat) := if j=0 then 0x7f else 0
def g238L : Nat → Packing
  | 8 => (1,0,1,0,0,0,0,g238D8)
  | _ => emptyPacking
def g238I (_ _ : Nat) : Option (Nat × Nat) := none
def g238 : Forest := ⟨238,8,fun i => g238Y[i]?.getD (0,0),g238C,g238A,g238L,g238I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g238P8_0 : block g238 8 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g238B8 : block g238 8 0 1=true := g238P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g238T : checkedTables g238 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g238 0 0 0 = true)
  · exact (rfl : block g238 1 0 0 = true)
  · exact (rfl : block g238 2 0 0 = true)
  · exact (rfl : block g238 3 0 0 = true)
  · exact (rfl : block g238 4 0 0 = true)
  · exact (rfl : block g238 5 0 0 = true)
  · exact (rfl : block g238 6 0 0 = true)
  · exact (rfl : block g238 7 0 0 = true)
  · exact g238B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g238G : graphValid g238 (boundsBefore K237) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low238 : Lower true (varsX 238) (graphGoal 238) 9 := lower_forest (g:=g238) (i:=0) (hints:=286266672) (before_sound K237 V237) g238G g238T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K238 := extendKnown K237 9 [(238,[]),(245,[16,64,82,48,118])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V238 : Known true K238 := extend_ok (m:=238) V237 low238 (by decide +kernel)
def g246Y : Array (Bits × Bits) := #[(0x0,0x0),((BitVec.ofNat 152 (word80 [0xf800fffff83fff83ce,0xd40e8180007c00f83e0])),(BitVec.ofNat 152 (word80 [0x502a02809080010bc6,0xd4000106318c6318c63]))),((BitVec.ofNat 152 (word80 [0xffff003fffc1fffdd1,0x214117ac000001f07c1f])),(BitVec.ofNat 152 (word80 [0x640c832020050201d0,0x2041030e318c6318c631]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffc00001fffc97,0xc5b4444400f83e00001f])),(BitVec.ofNat 152 (word80 [0x80300402c108140007,0x45a44400c6318c6318c6]))),((BitVec.ofNat 152 (word80 [0xfffffffffffe000021,0x2edc7a201f0000007fe0])),(BitVec.ofNat 152 (word80 [0x140280b0000581021,0x9c78218c6318c6318c]))),((BitVec.ofNat 152 (word80 [0x44,0x903f89b3e0003fff8000])),(BitVec.ofNat 152 (word80 [0x180300c0210602000,0x901888a1084210842108]))),((BitVec.ofNat 152 (word80 [0x33a,0x528a034bffffc0000000])),(BitVec.ofNat 152 (word80 [0x600c0300421804018,0x202034a108421084210]))),(0x0,0x0)]
def g246C : List ColumnInfo := [(4,0,242,0,7),(32,0,214,0,7),(16,0,230,0,6),(20,0,226,0,5),(68,0,178,0,5),(80,0,166,0,5),(130,0,116,0,5),(96,0,150,0,4),(132,0,114,0,4)]
def g246A : List (List Nat) := [[],[65,82,118]]
def g246D5 := limbs80 #[#[0x7cab2286a8f155450d51,0x232080d18179dc96454]]
def g246D6 := limbs80 #[#[0xd55151f550d51e750d40,0xf0f00fd59151fd58951d,0x22304ca883e02cc266b4,0x890418246232a]]
def g246H6 (j : Nat) := if j=0 then 0x40000720068a else 0
def g246D7 := limbs80 #[#[0xf80feaa7f503fa41f551,0x91818a201158985a6e4,0x11818a246053]]
def g246H7 := limbs80 #[#[0x1ac4000000000000,0x88005200006100007000,0x730000]]
def g246D8 (j : Nat) := if j=0 then 0x651013f else 0
def g246H8 := limbs80 #[#[0x600a00f2000000000000,0x6000cbb007]]
def g246L : Nat → Packing
  | 5 => (3,3,4,0,0,5,0,g246D5)
  | 6 => (5,2,4,0,0,7,0,g246D6)
  | 7 => (4,1,4,0,0,7,0,g246D7)
  | 8 => (1,0,4,0,0,0,0,g246D8)
  | _ => emptyPacking
def g246I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 7 0 7 2 1 g246H6
  | 7 => lookupWord 1 29 0 8 3 1 g246H7
  | 8 => lookupWord 1 17 0 7 2 1 g246H8
  | _ => fun _ => none
def g246 : Forest := ⟨246,8,fun i => g246Y[i]?.getD (0,0),g246C,g246A,g246L,g246I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g246P5_0 : block g246 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g246P5_1 : block g246 5 1 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g246B5 : block g246 5 0 3=true := (@block_merge g246 5 0 1 2 g246P5_0 g246P5_1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g246P6_0 : block g246 6 0 3=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g246P6_3 : block g246 6 3 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g246B6 : block g246 6 0 5=true := (@block_merge g246 6 0 3 2 g246P6_0 g246P6_3)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g246P7_0 : block g246 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g246P7_1 : block g246 7 1 3=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g246B7 : block g246 7 0 4=true := (@block_merge g246 7 0 1 3 g246P7_0 g246P7_1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g246P8_0 : block g246 8 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g246B8 : block g246 8 0 1=true := g246P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g246T : checkedTables g246 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g246 0 0 0 = true)
  · exact (rfl : block g246 1 0 0 = true)
  · exact (rfl : block g246 2 0 0 = true)
  · exact (rfl : block g246 3 0 0 = true)
  · exact (rfl : block g246 4 0 0 = true)
  · exact g246B5
  · exact g246B6
  · exact g246B7
  · exact g246B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g246G : graphValid g246 (boundsBefore K238) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low246 : Lower true (varsX 246) (graphGoal 246) 9 := lower_forest (g:=g246) (i:=0) (hints:=286393424) (before_sound K238 V238) g246G g246T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K246 := extendKnown K238 9 [(246,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V246 : Known true K246 := extend_ok (m:=246) V238 low246 (by decide +kernel)
def g127Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x1c000007c0000fc0fc,0x60d11cb9824fcfa43c93])),(BitVec.ofNat 152 (word80 [0x1414a5290924924924,0x20101cb9806483c41082]))),((BitVec.ofNat 152 (word80 [0x440000f800fc003f00,0x8111e301ed8c30c04359])),(BitVec.ofNat 152 (word80 [0x40463088514514514,0x8810d500858c90c00110]))),((BitVec.ofNat 152 (word80 [0x80801f003f03f00000,0x61e005e11f03f008366])),(BitVec.ofNat 152 (word80 [0xc2118430c30c30c,0x23c184810f03a000140]))),((BitVec.ofNat 152 (word80 [0x6a83e0000000003fff,0x7e000601e003ff7049d])),(BitVec.ofNat 152 (word80 [0x68a908525249249248,0x26800401a002c110405]))),((BitVec.ofNat 152 (word80 [0x91fc00000003ffc003,0xf80003801fffc01800e6])),(BitVec.ofNat 152 (word80 [0x80a14a429451451450,0x880083000f0900180024]))),((BitVec.ofNat 152 (word80 [0xc10000003ffc000000,0x3ffe000001ff704])),(BitVec.ofNat 152 (word80 [0xc1739ce738e38e38e0,0x2b32000001ff604]))),((BitVec.ofNat 152 (word80 [0x277fffffc000000003,0xfffffc000000001ff800])),(BitVec.ofNat 152 (word80 [0x34210842082082082,0x5581000440020022e000]))),(0x0,0x0),(0x0,0x0)]
def g127C : List ColumnInfo := [(32,0,95,0,10),(1,0,126,0,9),(2,0,125,0,9),(4,0,123,0,9),(8,0,119,0,9),(16,0,111,0,9),(33,0,94,0,8),(64,0,63,0,8),(0,32,89,6,7),(10,0,117,0,7),(12,0,115,0,7),(18,0,109,0,7),(20,0,107,0,7),(34,0,93,0,7),(36,0,91,0,7),(2,32,89,4,6),(3,0,124,0,6),(4,32,89,2,6),(5,0,122,0,6),(8,32,81,6,6),(9,0,118,0,6),(16,32,73,6,6),(17,0,110,0,6),(40,0,87,0,6),(48,0,79,0,6),(6,0,89,0,5),(6,32,89,0,5),(10,32,81,4,5),(11,0,116,0,5),(12,32,81,2,5),(18,32,73,4,5),(21,0,106,0,5),(24,0,103,0,5),(41,0,86,0,5),(65,0,62,0,5),(66,0,61,0,5),(68,0,59,0,5),(72,0,55,0,5),(80,0,47,0,5),(96,0,31,0,5),(13,0,114,0,4),(14,0,81,0,4),(14,32,81,0,4),(16,8,36,67,4),(19,0,108,0,4),(22,0,73,0,4),(22,32,73,0,4),(26,0,101,0,4),(28,0,99,0,4),(73,0,54,0,4),(74,0,53,0,4),(81,0,46,0,4),(84,0,43,0,4),(98,0,29,0,4),(80,8,36,3,3),(19,8,36,64,2),(27,0,100,0,2),(75,0,52,0,2),(82,8,36,1,2),(0,512,179,0,8),(0,513,179,0,8),(0,514,226,1,6),(0,515,208,1,5),(0,516,208,1,5),(0,517,240,0,5),(0,518,209,0,7),(0,519,226,0,5),(0,523,208,1,5),(0,524,240,0,5),(0,525,242,0,7),(0,526,187,0,10),(0,529,240,0,5),(0,530,240,0,5),(0,531,179,0,8),(0,532,226,0,5),(0,533,240,0,5),(0,534,241,0,8),(0,535,226,0,5),(0,536,241,0,8),(0,537,208,1,5),(0,538,240,0,5),(0,540,240,0,5),(0,542,226,0,5),(0,545,240,0,5),(0,546,240,0,5),(0,547,242,0,7),(0,548,240,0,5),(0,549,240,0,5),(0,550,209,0,7)]
def g127A : List (List Nat) := [[],[33,67]]
def g127D5 := limbs80 #[#[0x21e305d98358d2148110,0x443a60bb326b1a42902,0x2e8985459b325b955c96,0x8158d61b0e362432cbc0,0xe564c98189c597a0653,0x30404608]]
set_option maxRecDepth 16000 in
def g127D6 := limbs80 #[#[0x20443661965952148110,0xd21481109d82a565485,0x86a54348520443bc1835,0x443bc18358d21481109f,0x2148110df064d6348520,0x9d6348520443ce17658d,0x3ce176d8d2148110b78e,0x48110b7869f634852044,0x6348520442be1a8d8d21,0xe17660d21481109f86a7,0x110cf865983485204439,0x48520442be3a660d2148,0x96e0d2148110e785db83,0xaf869b83485204433e1,0x5204435e17664d214811,0x64d2148110cf86199348,0x585d965485204433e386,0x443d63765952148110f,0x52148110dd8659654852,0xddb9548520443d6176e5,0x4376196e552148110f58,0x148110bd869b95485204,0x17648520442fc3a35d92,0xde1a4dd92148110b78e9,0x81109f8e8d9648520442,0x250520443cd17658d314,0x1645894148110fe050d3,0x10ee460d4350520443ea,0x8520443ab18659141481,0x358d6148110f98595625,0xcf4e4f8358520443ad18,0x204427e1a2e4d6148110],#[0x956148110e9c61965585,0x65d98358d20443a73865,0x443cd17658d214c110e3,0x414c110fc45954350530,0x194350530443d917650d,0x37919650d414c110ee46,0x4c110be4e99435053044,0x4358530443cd17658d41,0x516558d614c110f94595,0x110fb058d3248560443e,0x48560443e61655892158,0xa2e0d2158110db464d63,0xf2c5d16448560442be1,0x5604436b194591215811,0x5952158110d9c6596548,0xb4651634c560442770a9,0x4436b1945913158110d,0x94158110bb468f644c56,0x5937250560443cb1645c,0x43ab164e094158110f2c,0x158110fa458d43505604,0x57258560442eb3a35914,0xc7165dc96158110f1c59,0x8110e9c5978258560443,0x35856044367165e49615,0x393e0d6158110f345cd6,0x10d3665d634c9604433d,0xc9604434db93d8d72581,0x32597258110d1e25b955,0xd2e65164dc960442cd9a,0x604438b9745938258110,0x8d4358110f265d16350d],#[0x65937350d604434d9975,0x4434b9975914358110f2,0x7358110d3665373d8d60,0x5164dcd60442cd9a3d91,0x34b974e4d6458110d2e6,0x58110b2ee89745916044,0x434c921442cbba35d164,0xc57658d3248510f615d1,0x510f295d16458921443c,0x58921443aa5845916248,0x765956248510f195d965,0xe355d98358d21443c67,0x9414438d576611634c51,0x5c96250510f6150d724c,0x255d96350d41443ca564,0x14434d59758d3258510f,0xd7258510f19595725896,0x2a5655c9614434d793d8,0x42cd5a32597258510b1d,0x358510db458f9050d614,0x16350d6144367165e414,0x4d59758d4358510f255d,0x8510f155977350d61443,0x550d61443c35655d1435,0x5655cd6358510d1d65d6,0x10f1559783dcd61443c5,0x91614434756565373585,0x5e4d7458510d9c597905,0xb17e8d76595624434756,0x7244295fa361d6558910,0x1b855c910a57e8d76e15,0xf65886e157244295da32],#[0x44295fa361b855c910c1,0x6550d1083fea58621972,0x8d97e116344287fa661d,0x3cd163dc52158130877e,0x58130d96e5563485604c,0x63dc5604c34d96364b71,0xb9945937158130d36651,0x130f2659143dc9604c34,0xdc9604c34d99458f7258,0x9458d8258130d2e65164,0xf865956450d604c369b,0xd604c365996595435813,0x5916358130ba66929650,0x165957458d604c3c9974,0x4c2cdba15d16358130f,0x16358130b36e897458d6,0x68b7458d604c38d8a85d,0xc3e156550d6150530b36,0x4d8530e365d163603614,0x965613714c307f985957,0x46d6564b7458930c1fe5,0xd30ea659143603624c3,0x6591434c2e99a0219645,0x9866408650d30ba36888,0x30b35684965d1634c32d,0x95644c297ba061d65591,0x6597805d130a1fe99875,0xa7c68486e01744c38788,0x744c30f99621b805d130,0x19655d130b1d68486595,0xee8186219744c287da1e,0x4c20ffa9618865d130a3],#[0x8548560877e8d91e1176,0x8d97e152158295fa361f,0x36b164e417150560a57e,0x50d60c67e53835c97158,0x90e0543582ad9a3a1980,0xb9646438150d60cb658d,0xd60da65939058d435832,0xdcd6358259fa464b7358,0x65e5182dcd609a7e9192,0x1d3658f9050d71d8313d,0x941487d857650d325052,0x50d3250521ee1619434c,0xe1e99434c941486f85a6,0x14876a564e416250521b,0xf8058521e9959562e016,0x58f9250d614878d57358,0x874d59758d4358521db1,0x158d21a5ee8186dd5434,0x163e01614c63f3a06538,0xcd7a05d16358531e355d,0x8531b35e897458d614c6,0x5d1614c7c55655d3835,0x565e4d8058541d1d5979,0x41ea558d43e016150765,0xf70587e1565e0d43585,0x36478050d61d3658f905,0xc9d59591e01435872d56,0x435872d5636478250d61,0x538158d61a9ee8186595,0xd59594e05635863f3a06,0xd861bfa464b835c361c9,0x635c14387ee8193e0974],#[0x8164e016350ecd5a11d9,0xf699a46407658d43ae6e,0x1d943d1ee58905d96550,0x766007650f8d97664d80,0xfba95d9801d943c3e2a5,0x943c3ee60905d87650f0,0x5d87650f0fb98e41761d,0xa0e61761d943c3e28398,0xc5e597906137158f0fb,0xfc0ea0d80ba09c04e00,0x6e15c14a13813212010e,0x41c21b01aa1981861801,0x23422e21c20a1f81da1d,0x9a28828227c276264252,0x82e22dc2ca2b82a62a02,0x34833632431230c2fa2e,0x9639037e37836636035a,0x43c63c03ba3a83a239c3,0x43843242040e4084023e,0x6e46846245c44a44443e,0xc4b64a449e4984864804,0x4f84f24e04da4c84c24b,0x5254052e52852251c50a,0x58e58857657055e5585,0x5dc5d65d05be5ac5a65a,0x1260c6066005fa5e85e2,0x864263c63663062a6246,0x66c66666065a65464e64,0xa269c69669067e678672,0x46de6cc6c66b46ae6a86,0x72071a71470e7086f66e,0x4a74473e73873272c726],#[0x476e76876275c7567507,0x79879278c78678077a77,0xce7c87c27b07aa7a479e,0x88167f87f27ec7e67e07,0x84c84684083a83482e82,0x8287c87687086a86485e,0xc8a68a089a89488e8888,0x8d08ca8c48be8b88b28a,0xfa8f48ee8e88e28dc8d6,0xe000a8691290c9069008,0x1800191809008c0bb806,0xa040a14204303fe85f04,0xc101810060401a851800,0x18004a14100c101d8004,0xa8130404002a04c101,0x103f70408068504c1010,0x18064201c101180040fc,0x4101000036001019047,0x1000d020421410850400,0x4810100a04068504600,0x1040010040000801810,0x118008000a141000000a,0x9810100400010c600240,0x7040000027040000000,0x100003e0010000070400,0x70401c10001c10001c,0x404000410100a040000,0x1c100002004000a0407,0x2008100000002704,0x27040,0xa010400000000,0x401c101004102804100],#[0x7,0x0,0x2204000004100000,0xa040a88142000,0x1c10000]]
def g127H6 := limbs80 #[#[0xc05b0000497400e200,0x510a00002800000000,0xc30000]]
set_option maxRecDepth 16000 in
def g127D7 := limbs80 #[#[0x90a40886f860d2148110,0x217e193485204437c706,0x552148110fb0b2a42902,0x443bc2ec90a40887d8e,0xcb24290221de3764852,0xa40885f8e592148110bf,0xf914350530443ce2cab0,0x614c110f68b1ac298221,0x439b2ecb1a608879c595,0x2282b0221ed1634c5604,0x8879c5956158110f58b,0xb73d8d604439b2e6b1ac,0x48510e5cba2c8b0221cd,0x4eb0cb2a428879959562,0xc698a213749859521443,0x879c5978058510e6abb2,0x5dc9614438eacab92c28,0x510d3ab2f04b0a21c756,0xee7b1ac2887355cd6358,0xb0a21c75655cd614439a,0x1d5957458510e3ab2ee6,0x1d624438eacbba2c2887,0xd3ab2b03b12211df936,0xdc2ae488477e4d87d891,0x2211df9361d634422fb2,0xe4d87d91108efc9b0eb2,0x604c2abf26bb2ca88477,0x6cb1f02b0261cd963dc5,0x1ac09873658f7258130d,0x16d99650d604c3d32c8a,0x16358130f2cb2ac6b026,0x4c39b6e8b1ac0987365d],#[0xc9ec8b02616db9458d60,0xc8986b658d80d8530b6c,0x7f86595744c23f720c3a,0x2dcd60e3ab2ee2b0ac18,0x22fb2fc2a43b046fe518,0xf00a1ec1cd5635c531d8,0x90fe150d3250521d6cb1,0x6558961487d4ac8b1282,0x8521f32b2f04b0a43e65,0xfb31baec690f355cd635,0xcb2a4317d96e15734862,0xc5f65a8759521e3bc8ae,0xe01614c62fb313b6ea90,0x31f2ab2ac6b0a63ad563,0xcbc1ac298f355d163585,0x2263c75655d1614c7caa,0x558d43585418fdc830eb,0xd70587c6acaa1ac2a0fa,0xd3ab2f02b12c3a5d65e0,0xc3a87b0e9d5978158d61,0x876d9901d96350e3f720,0x417659543b6ac88ecb1a,0x650f1f2ecc00eca1d5ee,0xdc8309b8ac70ff985d87,0xa40887f850d21481108f,0xfe36348520443fc2c690,0x2148110ff0c1a4290221,0x43fc4ec90a40887f85d9,0xb24290221fe196485204,0x887f85093148110ff14,0x1634c520443fc2c498a4,0x48110bf8ca26290221fd],#[0x7e30c98a408877c5d931,0x6290221bf3864c520443,0x87f84c94148110bf8cb2,0x350520443fc2c4a0a408,0x110df8c1a8290221fb14,0x2eca0a40887ec5914148,0x90221df37650520443be,0xf85896148110df8c3282,0x8520443de2c6b0a40887,0xdf8c1ac290221ef3635,0x6b0a40886fce0d614811,0x221df17458520442fe72,0x5956148110ef9ba2c290,0x204437e30cb0a40887dc,0xecc1a8690221bf386585,0x1a40886f660d6348110d,0x15fb9758d204439f2ecb,0xb6348110bf8c8ec69022,0x4439f2edb1a40885fa64,0xcc6c6902215f997d8d20,0x408867e5d983481109fc,0xf976e0d204427f72cc1a,0x5481109fccb706902219,0x3af6ecb2a408875e5d96,0x2ec902217f3915d92044,0x885f6e4d7648110bf5c9,0x919d920442bf728bb240,0x8110bf4c94ec902217f1,0xc2c490a608857e653764,0x298221fd14348530443f,0x5fc651214c110fe8b1a4,0x48530443be2ec90a6088],#[0x10bf8cb24298221bf186,0xc8a0a60887f458d414c1,0x8221f716550530443f62,0xc619414c110ef8bb2829,0x530442fe32ca0a60886f,0xfe8a1ac2982217f39258,0xb0a60887f458d614c110,0x21bf18658530443ee2ca,0x4f624c110bf8c8ec4982,0x442bf32fb1260885f66,0x8c8a86982213f998d893,0xa60887e6591434c110fe,0xdd97650d30443eb2caa1,0x434c110decc328698221,0x42fb728b1a60885f6e59,0xb2c698221f596558d304,0x884fee61644c110eecb,0x993d9130442fe323b226,0x4c110afccbec8982217d,0x7f724c3260884fe66364,0x42b0221fe13248560442,0x87f86092158110ff0b12,0x348560443de2c690ac08,0x110df9c1a42b0221ef36,0x2c890ac0885fc64d2158,0xb0221ef36448560443de,0x7cdd12158110ef8ba242,0x8560442fe32890ac0887,0xfb9caa42b0221f71654,0xc90ac0885fc659215811,0x221bf3824c560442fe72,0x5913158110fe8b1a62b0],#[0x60443de6c898ac0887bc,0xf8cb262b02217f1944c5,0xac08877c5c94158110b,0x1bf38250560443be6e4a,0xd4158110fd8a1a82b022,0x4437e706a0ac0887bc58,0xb92c2b0221df17258560,0xc0886fce096158110ef9,0xf16358560442fe724b0a,0x158110ef8b9ac2b0221e,0x37e706b0ac08877cdcd6,0x2c2b02217f3935856044,0x886fc60b8158110f78b2,0x634c960442fe325c0ac0,0x8110eedb9a64b0221ed9,0xf530992c08857e65d325,0x4b0221eb964509604427,0x5dee557258110f3cb2ac,0x5c960442df72cb92c088,0x10e7db1ae4b0221cf963,0xcab92c08857ee4d72581,0x221d7b955c960443af2,0xee597258110e7c4b2e4b,0x9604439f2c9b92c08873,0xafcca6e4b0221cfb64dc,0xc12c08875e5977258110,0x217bb9460960442fe722,0x9382581109fcc9f04b02,0x4435f6c9c12c0886be5,0xcb2f04b02219f974e096,0xac0887b658d4358110db,0xeb96450d60443bb6e6a1],#[0x4358110edcba286b0221,0x43bb2e6b1ac08857e65d,0xa2c6b0221cf97458d604,0x885be6536358110b7dc,0xb645cd604439f2c8b9ac,0x58110afcc96e6b0221cf,0x9f2c9b9ac088776e0f73,0xe6b0221cfb64dcd60443,0x84fe64b8358110afcca6,0x359160443cf2cab22c08,0x110f5cba2c8b02216fb9,0x327b22c0887aee116458,0xb02215fb925d160442df,0x7e64b7458110afdc9ae8,0xc921443ee722b2ac0885,0xfe2b1a6490a21fc5434,0xc99242887795d1324851,0xa21be5864c921443bcae,0x5916248510df2c1ac490,0x21443dcec8b1242887b9,0xf3ba2c490a21de574589,0x1242886f96116248510e,0x1f678558921443ecacab,0x96248510ef2bb2c490a2,0x442fe720a1a4288779dd,0xba28690a217e79250d21,0x42884fd6614348510eda,0xf57658d214437ab06b1a,0x348510afbcbac690a21c,0x2fcb25b1a42885fc6436,0xec690a21cf576d8d2144,0x884fd6636348510afacb],#[0x90591214433eaecc1a42,0x8510bf3c92c890a217f3,0x6b08b22428876d5d1644,0x890a217f190d91214437,0x57d65f6448510bf2c96c,0x5d1214427eb31b224288,0x10afbcb2e890a219f586,0x2dba2428867d61b74485,0xa219f57661121442beb,0xd5d96548510cfbbb3089,0x521443aeeecb2a428875,0xebabb70a90a21b758659,0xc2a428875dddb8548510,0x2177596e15214436eb0d,0x497648510bf9c82ec90a,0x1442faf26bb242885f9e,0x8c84ec90a215f7945d92,0x242885f964a7648510bf,0x7f39061921442beb29bb,0x8648510bf3c930c90a21,0x427ef28c3242884fde4d,0x950c90a217f190a19214,0x2885fc643624c510bf2c,0x597d8931442fab27b126,0x4c5109facc6c498a215f,0xeaacab1a62886f561163,0xc898a21dd57658d31443,0x86ed611644c510bf9c82,0x3d9131442fe321b22628,0x510afacbec898a217d59,0xf24c2262884fd663644c,0x98a21b7565611314427e],#[0xfde59844c510cfabb308,0x19314436eb0cb2a62884,0x9fbca30c98a213f7926,0x699282887795c9325051,0xa21de57258941443f2a8,0x50d7250510f5ab22c4a0,0x41443b6ac8b92828876d,0xdab26e4a0a215f7965c9,0x1a828857d65b7250510e,0x1f356550d41443f2ac6a,0x94350510edabb286a0a2,0x442f6f2ca1a82886ed61,0xc82c8a0a21cf57658d41,0x82885ede4d6450510fd9,0xd7935d941442fe720bb2,0x650510ef9c82eca0a217,0x3ba926bb2828857de497,0x6eca0a21dd7935d94144,0x884fde4d8650510afac9,0x734c961443daac6992c2,0x8510afacba64b0a21dd7,0xeb2ea12c2884fda61325,0x4b0a21de57258961442b,0x79d5957258510f3ab2ac,0x5c961442eef2ab92c288,0x10e7bb1ae4b0a21cf563,0x28b92c28857de4d72585,0xa21d75655c961442bef,0xd2597258510ebbcaae4b,0x9614439ef2cb92c28873,0xebab2ee4b0a215f594dc,0xc12c28879d5978258510],#[0x219f574e09614427eb27,0x978258510cfbba704b0a,0x1442fe720a1ac2886dd5,0xbb9a86b0a21ed56350d6,0xac2886f5e0d4358510ee,0xe756550d61443b6ae8a1,0x6358510afacba86b0a21,0x43ceacab1ac2887755cd,0x2ae6b0a21cf57458d614,0x28857d64b7358510ebab,0x594dcd61443baf07b9ac,0x58510ebab2ee6b0a215f,0x7eb25c1ac28879d59783,0xc8b0a21b7565e0d61442,0x879d5956458510bf9c82,0x25d161443ceacaba2c28,0x510afbc9ae8b0a215f79,0xee6b12648857d64b7458,0x992215ef9758932443b9,0x375d9634c910eceba286,0xcd324433bb0eb1a64887,0xaeeca6e6992219dd84d,0x6ba2648857765b734c91,0x2211fd985d132442bbf2,0xe4d764c9109fdc830899,0x324423ff30bb26488577,0xffcb30e992211ff9461d,0x9a84887ab59162509108,0x15df935d9424423fb31b,0x186509108fecc6eca122,0x443cdacab92c4884fee4,0xba2c8b12215ed92dcd62],#[0xc48857b64b7458910e5e,0xf990e116244337f09ba2,0x5589109fac8f08b12213,0x38feecb2ac48871f5d96,0xaecb122197d875956244,0x884fee418758910aefc9,0x9461d624427ef22c3ac4,0x89108ffcb30eb12213bf,0xf6e6c06c48867e5cd80d,0x1b12213fb93603624433,0x67d5cd81d8910d7cb230,0x607624433eee6c0ec488,0x10ceec1ae7b12213f793,0x20c26c48847f66373d89,0x12213df9361f624427f7,0xf5db855c9108ffc9b0fb,0x5724432fcedc2ae48865,0xaf7c92ecb922137d96e1,0x3b2e488577e4d765c910,0x215f5919d972442bf321,0x1a765c910af6c94ecb92,0x2442bf720a1ae48863fe,0xcc86c6b92219df8350d7,0xae48857d647635c910af,0x9df83d8d72442bdb25b1,0x835c9108ff4c6c6b9221,0x432ff0cb2ae48847f653,0x370ab922157c98595724,0x48865f61b855c910cbe4,0xf86e15724432fd0dc2ae,0x5c910abecb70ab922197,0x1fb0c432e48857764c86],#[0xcb92215fb9061972443,0x857e642865c910aefc9b,0x3e19724431ff0d432e48,0x910cbfcaf0cb92211fd9,0x321b26e48866f61164dc,0xb92215f591d9372442bf,0x5f61965dc9108fecc6c9,0x1434427f325c0286886,0xddcb2700a1a21bd963e,0x3c1286886de5978050d1,0xa219df73e09434427eb2,0x5d16350d108fecbf04a1,0x434439baecb1a8688767,0xeec96e6a1a219dd8758d,0x9a86887675937350d10a,0x15dd96dcd43443abacbb,0xd6450d10bddc82c8a1a2,0x443a7acaba2868866f61,0xcb2e8a1a219bf865d143,0x868865f61d6550d10adf,0xf591e1943442bbf26bb2,0x750d108fecbf0ca1a213,0x23ff2cc3a868847fe498,0x708b1a21d5d655cd6344,0x884fd6478458d109fcc8,0x9461d634423fb2fc22c6,0x8d109fdc9301b1a211ff,0xbee6c16c6884fde4981d,0x9b1a219dd84dcf634433,0x47fe4987d8d109fdc830,0xd9173442bf321b22e688,0x10aeec9ec8b9a215f591],#[0x2cc16e68847f663645cd,0x9a219bd84593734423ff,0xd64764dcd10afcc86c9b,0x3734423fb31b26e68857,0x8ffc930db9a2197d6561,0xc02c88876e5d38059110,0x21b7965e01644427f325,0xdb8059110cfcbb700b22,0x444337ae9c1ac88867ed,0xfc9ae8b22215bf925d16,0x2c88871f5d96559110ad,0x3fb9061d64442bbf26bb,0x80d91109fdc9301b2221,0x427ef24c0ec8884fee4d,0x9b0fb22213f793607644,0x88847fe4987d91109efc,0xf9361f644433b926c3ec,0x5d1108ffc9b0fb22219d,0x3fb27c12e888577e4d76,0x6ba2211fd92e0d74442,0x857ee41865d110cbeb2f,0x2e1974442bbf26c32e88,0x5108fec9f0cba2211fd9,0xeedc0aca8875d5db8159,0xb2a2175f935d965443ae,0x57e4d7659510abfc92ec,0x176442afb25bb2ca887,0xdedc1f00bb221bf381e,0x7c0aec884fe64b805d91,0x2213f592e05764437af0,0xe47835d910dedc8706bb,0x764433bf0841aec886f5],#[0xefc9706bb2219df84e0d,0x22ec88677e53835d910c,0x13fb92602764423fb27c,0x582dd9109fbc93033b22,0x4c3be6e290ac09865fe5,0xcaa42b0261ed96348560,0xc0987e650d4158130bbd,0xb964505604c3db2c6a0a,0x158130f6cb1ac2b0261e,0x39f2c9b8ac09857e64b7,0xb02b02615f994dc5604c,0x986f6e0d8158130f6cb1,0x43e05604c2fb726c0ac0,0x8130f6cb1a84b0261bd9,0xb2c6b12c0987ae591425,0x4b0261e7965589604c3d,0x77650f7258130f6cb1ae,0xdc9604c39f2c9b92c098,0x30f6cb1b04b02615f994,0xc8a1ac0985eee5182581,0x261f998450d604c3f32,0x66594358130facb2a86b,0xd604c2fb32ca1ac0987b,0xbedcb286b0261eda9650,0xb1ac0987b65916358130,0x61ed97458d604c3bb2e8,0x956458130f6cc22c6b02,0x4c3d72e8b22c09879e5,0xdc8ae8b02616fb965d16,0x2c09875e5957458130af,0xcfb965d1604c39f12cba,0x7458130cfc4c2e8b0261],#[0xc3f2a86a0a429857e64b,0x16e290a61ed563585214,0x29877558f7148530ef2b,0x596dc5214c2beb29b8a4,0x48530dafc2a8690a615f,0xbef22ba242986d7e1563,0xa90a6197f855d1214c2,0x84df65b8548530cbebb7,0x3585414c2bef22bb2429,0x530f6ab1ac2a0a61f954,0xacaa1a829879d5956150,0xa0a61d9d7650d414c3e3,0xe7e594350530dcec3286,0x9614c23ff2ec3282985,0xf2eb2a86b0a613f990e,0xab1ac298677e1d435853,0xa61cdd7458d614c3cbac,0x64b8758530e3eb2ae8b0,0x614c37b286c06c29847f,0xcec2287b0a619f974603,0x1ec29879759543d8530d,0x13df9850f614c33bb0ea,0x183d8530e6eba2c7b0a6,0x4c337b08ba6c2986775d,0xcc2e9b0a61c7d655d361,0xe29847f66142dc5308ff,0xdd6360b714c33db04b16,0x4dc530ceec22c7b8a619,0x32facac26e29866f6116,0x2c4a12611ff96613714c,0x9879b5956250930f56b2,0x655c9624c23fb31bb284],#[0x8930f4eb2286b1261e6d,0xbacaa1ac4986e7e11435,0x8b1261e5d6558d624c3c,0x66fe137458930af6c96e,0x595624c38facbba2c498,0x30e3fbb2cab1261c7d76,0x28c3ac4984fee4187589,0x1261bd943603624c277f,0x759143d8930d7cb2301b,0xf624c373b08a1ec4987a,0xceec3a87b1261e5d6550,0xbb2e4984f7e6143d8930,0x61d9d6450f724c2bf720,0x1943dc930eaeb2a87b92,0x24c2bbf2ca1ee4986776,0xec22c9b92619dd8458f7,0x2869865f59584dc930cd,0xf5965e01434c3f32c9c0,0x8050d30decc3700a1a61,0xc3e3acab2286985f665b,0xb2c8a1a61d9d76591434,0x6987a72196450d30ecfb,0xd76595434c3d3f0cb228,0x50d30eafbb2caa1a61d5,0x6bf0cb2a86986d761965,0xeca1a617db905d9434c3,0x8577e497650d30eedc82,0x49d9434c2fb3213b2869,0xd30aeecbceca1a6179d9,0x320432869857764b7650,0xa1a617d591219434c2fb,0xb76188650d30be6c910c],#[0x19434c27bd3043286986,0xbecc850ca1a617db906,0xf43286985e76528650d3,0xa61d9d74591634c2bbb2,0xe417458d30bedc82e8b1,0x634c2bbf22ba2c698776,0xaeb2ae8b1a615df925d1,0xa2c6987372597458d30e,0x15dd92dd1634c39bf2cb,0xd6559130bddc82e8b226,0x4c27f720c3ac89865f61,0xc870eb22611ff9661d64,0xe8986de597805d1309fc,0xf996e01744c33f4edc02,0x65d130d3fc32caba2613,0x2bbb273b2e89857e6427,0x4ecba2615bd949d9744c,0x9875e597805d130c7fc3,0x86e01744c33f10dc02e8,0xd130afccb700ba2619fa,0xfacbc0ae89847f64b815,0xaba261c7c86595744c32,0x65fe19655d130e3fc32c,0x219744c2beb22432e898,0x30afdc830cba2618fd86,0xd432e89857e642865d1,0xa2611fd91e19744c31ff,0xf6537659530cbeb2b05b,0x1215823fb23c22ec9855,0xf5ab228290ac1b7b8560,0xb0a42b05fce416148560,0xc1de5725c521583ceaca],#[0x156348560d6ec1ac690a,0x15834ff0bb1a42b069fe,0x6c96e690ac15f591dcd2,0xa42b065fe177348560af,0xa7d86595215826ff2ac1,0x65485609be4c2ca90ac1,0x832fb0fc2a42b04dfa61,0x870a90ac197e87e15215,0x2b04df65b8548560dbcc,0xe97e15215832fb2fc2a4,0x485609fdc830c90ac197,0x7f321c3242b04dfe5586,0xe90ac15f79161d21582,0x4f7e4d8748560aefc9b,0x661d215826ff2ac3a42b,0x560f6ab1ac298ac12ff9,0xb23b9262b07b558d714c,0x98ac1add8458d31582be,0xb764f644c560d5ec22c8,0xd131582beb23ba262b05,0x9efc9b0e98ac11fd98d,0xb8a82b047f64a874c56,0xac1eb5645c541582fe72,0x5937250560afac8ee4a0,0x41583d3ac6a1a82b072f,0x5dc82c8a0ac15f591dcd,0x3a82b05afe4d6450560f,0x13df9361d415827f720c,0xb80585608fec950ea0ac,0x5835f2c9c02c2b04fe64,0xb2f04b0ac1c7d65dc961,0xc2b0677e0f7358560d3e],#[0x7791595615838facbba2,0x25c560dedc1f00b8ac1e,0x33bf07b92e2b0677e0d7,0x706b8ac1adf83d8d7158,0xb06b7593835c560dedc8,0x74e0d715835bec9c1ae2,0xc560cefba706b8ac19dd,0xff28c16e2b06d7597835,0x7b8ac197d6560b715823,0x67760d43dc560e6eb1a8,0x6014358337b08a1ee2b0,0x60d7cc3300a1ac1ed963,0x21c0a86b06bea198050d,0x1ac1add63e05435827f3,0x6e416350d60d5eb2702a,0xd43583d3ac8b1a86b05f,0xf6dc82c6a1ac1e5d6558,0xb9a86b07a75d16350d60,0xc1a7d8659543583b3ae8,0x418650d60cbfc3acaa1a,0x3582dbb2743286b04fee,0xdc830ea1ac13f990e194,0xa86b04bfe598750d60af,0x1fd91a1d43582bbb2743,0x8058d60d7cb2700b1ac1,0x82bbb25b9ac6b04fe653,0x96e6b1ac1e5f93595635,0x6b04efe5182dcd60b6ec,0xf9460b735823ff24c0ee,0xdcd608ffc8b05b9ac15b,0x37f28c16e6b066f25182,0x5b9ac11ff9460b73583],#[0x75764d65dcd60cbeb2b,0x35c521d82eef22c1acab,0x760ebbc2ae290ec1cf56,0xf22b9a43b069fe156348,0x90ec197f855cd21d82be,0x5f65f8548760cbec3f0a,0xd71d832fb2fc2a43b05,0xe6eb1a86b8ec15fb905,0x5c1ae3b0677e0d435c76,0xec1ed963e0143d823fb2,0x61b8050f60eecb9f00a1,0x43d833f30fc0287b06be,0xfccbf00a1ec1af996e01,0xaae090f5ddd5615c121c,0x357d96dd5704872ff0db,0xa765c121afac8cecb824,0x487bcac4b0ee090e3fe1,0xbb264a0a43fc5634c941,0x8290ef96193250521ef2,0xa54358941486fcf20b12,0x350521fcab1a86a0a43f,0x776b0ca1a8290f6d5d94,0x286a0a437b59650d4148,0x90cfde616350521bdbcb,0x9359141487f4f24b2282,0x8521afbc82eca0a437b7,0xcac5c02c290f9d597805,0xb0a43af563e01614877,0xe7d5cf8058521d7bb1f0,0xe01614873eae9c02c290,0x21dbbbaf00b0a43b7565,0xeab12c290fb958d62585],#[0xa43f6775e0961487ece,0x558d4358521bf3c9286b,0xd61486beb2ea1ac290fb,0xe7aba2c6b0a43ed78358,0xc028690df9e496458521,0x431fd97e01434872feeb,0x8f8150d219fac8702a1a,0x348776ac9c0a8690ef55,0xfbaac6a1a433f596e054,0xa8690e7761d6350d21ea,0x97f86dd5434872fb0dba,0x7650d21abecb6eaa1a43,0x867f720c328690d77e4d,0xbf0ca1a433f791619434,0x690c7fe418750d218fec,0xf75e01634863ff2cc3a8,0x58d21eeab9f02b1a4397,0x7eb29c0ac690cfd64381,0xeab1a4397f75e1163486,0xe5fdd580d8d21abecb6,0x60b634867ef20c0ec69,0xd219f7c9309b1a433ef9,0xf20c3ec690e5fdd584d8,0xbaa4357f905d9654863f,0x5de4576dd521abfc82ed,0x1b75486afb213b6ea90f,0x1cbec3301baa43b77916,0xc36ea90d5fe5980dd52,0x24357d90a1b75486aff2,0x643815d921df3c1702bb,0x614c67ef20c0cec90cfd,0x6ab1a84b0a639f574e01],#[0x1ac298fb558d6258531f,0x3dd574e0d614c7daac8b,0x17458531f3ab2ac8b0a6,0x4c6bef24ba2c298d7de4,0xc82e8b1a63cbd7459162,0xc898d77e497458d31aef,0xbf925d1644c6b7f20ba2,0x5d1318fec9700ba2635,0x63fb21c12e898e5f5978,0xb0cba2635fb90619744c,0x98c7f643865d131aefc9,0x90e11764c63fb25c32e8,0x8541bebc9b00b0a831fd,0xeacbc02c2a0f9d595805,0xb0a833f592e0161507c,0xebd58f8058541ddaa1f0,0x4c961507f2a86992c2a0,0x419fac8704b0a83ed563,0x6a1ac2a0eed50f82585,0xa83ed78358d61507f2f,0xd5978358541f3ab2b06b,0xd32507b3aeca1a64a0f9,0xbcfcb2869928379d9650,0xc02c4a0c7fe61764c941,0x83abd64e01625067eb23,0x496458941cdfc3a86b12,0x35063fb21c3ac4a0fabe,0xfc82eca1a8379f9058d4,0x286a0deee418650d41ad,0x7bb9060d64506f3f26c3,0x845c161daeb2f06b82c3,0x878facab16e0b0e9f597],#[0x8287b82c397d6560b705,0xb0f3758d43dc161afdc,0xf93603725878facab26e,0x50d61cbeb2b01b92c31f,0x5bac7c0286b0cfd64780,0x2a1ac3a7d65e0143587,0xf9d5958150d61f6ab1b,0x3e09435867eb23c1286b,0xd61f4eb22c6a1ac3add6,0xf22b1a86b0f975956350,0xa1ac3e5d65dcd43587da,0x7764b7350d61aeec86e6,0xcd43587b3ac9b9a86b0d,0x1cefc36e6a1ac3d5d65d,0xcb2a86b0f8f5956450d6,0xac3a7f86595435874fb0,0xe418750d619fdc830ca1,0x63586bbf26c3a86b0d7e,0xffc9301b9ac33f594e05,0x16e6b0c7fe4182dcd618,0x3a7d65e01645873bac6c,0x1825c361d3eb2f06b22c,0xd879bac6a1ae1b0d6fe5,0xc9708b86c31fd92e0d70,0xe5b0e6fe11435cb618fe,0xdd63e0143d863fb21c22,0x50f61ceeb9f00a1ec3a,0x74facbc0287b0e6f5d38,0x2e8a1ec35df905cd43d8,0xb0d7ee418750f61adfc8,0x93e0974d863fb21c3a87,0xc143afdc8306ba6c31fd],#[0xbeecb1ae0a1f371d9635,0xab8287adf8658d7050f9,0xd7d644765c143d3fc32c,0x9d97050e3fd303b2e0a1,0x43c7fc34ecb82875dd93,0x273b6e0a1df6e4163dc1,0x82879dd636077050ebbb,0xf59581dc143cdeb2303b,0xf7050fbb720b1ee0a1e5,0xeaeb2ac7b8287d9d6458,0x436e0a1e5f61965dc143,0x875fb905d97150ebbb27,0x4176dc5439efcc2c7b8a,0x150f3bac6c06e2a1d7ee,0xeb2b01b8a879bd646037,0x6e2a1e7758d82dc543cb,0xb9d64e016350f37ac8c1,0x8258d43daeb2f00b1a87,0xef3f28c12c6a1ee7e11,0xb708b1a87e9f76591635,0x6a1f97dd96558d43f4fb,0xe981d96350edbb203b2c,0x59543b6ec86ecb1a876d,0x8feecbb2caa1ddee4176,0xecb2a87d78905d96550f,0x1d5fe417659543ebdc82,0x66007650eafb21bb2caa,0x943decc9b003b2878fd7,0x720bb0eca1f3e241761d,0x3b2878ff985d87650f9f,0xf6e0f805d9438fec850e,0x17650f7b727c02eca1e],#[0x3dcfc2706bb2879fb76e,0xdc02eca1e7ee18805d94,0x2873df9060e7650f3f72,0xe4164dc163a7ec86ed3b,0x7158f2facac26e0b1d7e,0xbcb2f00ba2c797d65613,0xae1b1e9fe19655d163d,0x71fd92e0570d8ebbf26c,0x7825c363adfca304b86c,0xd8e3fb23c22e1b1c7f64,0xc9700b8ec71fd92e1170,0xe5b1c7f643825c7638fe,0xfd91e0172d8eb7f28c02,0x45cb638fec8702b96c71,0x23fb23c22e5b1c7f6438,0x4c03d006100850090000,0x257043407740d5816e02,0xc1a3031f05da0aec14a0,0xfa112c20183e707960e0,0x5820aa014d027b84af08,0x322861e0c0417982d48,0x61bc836586ba0d2619b,0x7790ea41d0439807140e,0x42908200fdc1ef03d00,0x8e24ac48208e8116c221,0x9d3138426984bf895812,0xc5560a8514bc28b05080,0xa82d0c58e0b0b15f42b4,0xc0c17e02ef85c60b7016,0x466d0ca8190231106198,0x7236746b58d391a50340,0xe921cc0388c7038df61b],#[0x7f20fa71ea83c3076d0,0x44424483a9064209040b,0x10221cc435485c90b321,0x88a0913b226a44908899,0x38462c8bd116922c6454,0x1f123aa47108d991a223,0xc9289240245e48788fb9,0x6e4a98945127924d0495,0x2f625e04b5096712bd25,0x9a5933a26524c609839,0xa44f049d2937e26c44d7,0x448286e5098a0513e327,0x8a38946028b45150a271,0xda5370a6594ba293c520,0x54d2a625480a8794fe29,0x4ad695912b1655e8aaf1,0x3c5834afe15eb2bca572,0x67e2cda5918b1a96242c,0xcb7496d82d785aacb479,0x725c74b8617062dea5bb,0x78e2f105ddcba8174a2e,0xcbe117bc2f6c5ec0bca1,0x246030c0317f52fc85f4,0x87d30c26114c14981830,0x4c7998e231a262d4c4c9,0x8664c8c8b1910321463e,0x998330e65d8cb2995432,0x4ceb99d1339666e8cd49,0x386858d0299f433dc677,0xa66349468e4d141a2234,0x4d6e1ac035326a20d3b9,0x846cc4d901b0f35fc6bb],#[0xba2370c6dd4db21b5336,0xce011bfc37d66f68dd99,0xe67188e289c353848704,0xcc8396e7298e4a9c8438,0xce999d223a0c73d4e6c9,0x8a76a4ec69d713aaa753,0xe253c28780cef39dd63b,0xf481e743cc6791cf1b1,0xd67b3cf649eb83d647ab,0xf4b3e747ca4f919f073d,0x8fdb1f9a3f127d88fae1,0x7a80b10081fff3fb07f4,0x9d412e8219035205940,0xd089a0f741cc835505ca,0xdc85a10aba146426a84b,0x1c3437a86dd0d3218a42,0x9106a1fc43ec87950ea2,0xd0895d12322404448887,0x2b245428a41145227944,0xd17322d5459e8b25161a,0x568c9518a230e45fa8bd,0x35f469c8d211a1233146,0x51d4a39847248e051b82,0xa290a9201a3e747968f1,0x4a6492a9211239a46d48,0x128e250b49f493a5266a,0x5c961d2bb25654aa894e,0x6034bfa97852eda5ca4b,0xd342267e4cae98c130fa,0x2c9be9369a6cd4d789aa,0x78c4ee09d253a1a7274e,0x53f627db4f7e9eb93cea],#[0xa4a105418281f501c9ff,0x8b25158a26d445286350,0xd483a90151caa35145c2,0x32a5f54b629505268a48,0xa1a53fca75d4dda9aa53,0x953d2a7454c6a9495262,0xd6ab3d55f2aad554eaa5,0xb40565eac79586aafc55,0x15bfab7956baad315a32,0xb4af515e1abb25742ae4,0xc2f583cb0355fe2beb57,0xd647ac7e58dab1716202,0xb0b51d695ad0f59fcb35,0xd975b22b6016b7ad5e5a,0xd6f0addb5baab7116d9a,0x4cb855707adf35bdab79,0xe705cbeb9657242e375c,0x17682eca5d72ba75740a,0x6cbc6978a2f0e5dfabbb,0xf965ef4bdd17ac2f475e,0xd800affb5fa8bf0d7d92,0x76c0d580cb013601ac01,0xa66114c1b982eb04c60,0x5867b0c96186c2f585bb,0x3ec46587eb0ec61ccc35,0x15e62b0c4f189b312562,0xd8ceb18c630cc5d58b7b,0x98c7198e031af6352c68,0x22c644cc855907b1e863,0x995132916500c9919243,0x3ccc61983b2f6659ecaf,0x35d66aecd1999ab32f66],#[0x19c3338066f4cdd19b1b,0xd8cf6d9e533a3673ace3,0x45768a2d12da12341367,0xda6c34d2696cd269a343,0xd4d565a93b5166a0ad3f,0x5e06b9ed6cdac0b57b6a,0xdb2b36456c52d809afe3,0x54dc65b73b6b56d1cd99,0x7956ef2dda1bb137466e,0xdbf537e46fa6df09bde3,0x74e0a5c0c38127002dfe,0x87970bae15dc28b84b70,0x1c51389c712ce215c3fb,0xe4e385c62b8b4715ce2a,0x93c726ce4c1c8a390e71,0x5cbdb97572c8e54dca6b,0x96e6e9cda39a37324e60,0xa2b741ee7f9cfc39e773,0xdd4b3a7a74bce935d18b,0xeebd9d72bad47570ea9,0xb517696ece9d94bb1876,0xddbd3b6976c6ed75dabb,0xaaef11dd9bba27722ee2,0xc1f781cefc9df0bbdb77,0x9e3a3c5878a4f105e12b,0x88f2cde513c917900f1e,0xd0e7a10f3dde733cd579,0x9ea6bd3c7a56f495e8a3,0xef605ebdbd6a7ac8f57,0xdf27bd8f741eda3d987b,0xdf133e207c1ef825efc3,0xecf995f2a3e4e7c7af8d],#[0xeb57d48fa4df46be877c,0x5f903f0f7dd0fb5df633,0xe0fda9facbf537e6efcc,0xfaf7f3cfe35fbe3f767e,0xe012c0097fc4ff45fe5b,0x43024203fc04d806300a,0xf681cb037e061c0b281,0x60c6c17c82ab05120894,0xfd07b60ee41d6837506a,0x253848508c6110420f83,0x616a42ce857b0a5a1324,0x5f0ca618c42fc85d70b9,0x36e86d10d5e1a3433586,0xa1dc43a7872d0e421bfc,0x3d10361f8c3e087890ef,0x46888c51146220442f88,0xe25ec4b7894d125623cc,0x1b13f227b44da89a9130,0x5838ae515862a2c51e8a,0x62ec45c78b6d166a2c4c,0x9318e2313c6168bf517a,0x6888cef199a330464f8c,0xa36ec6cc8d8d1ad63474,0x2f1c46385c7058dff1bb,0x76c8eb71cfe39747288e,0xe3db47b08f291e3a3bec,0x231fd63f247de8fb11f1,0x85b909520e6419c82d90,0xa463489f9107219e430c,0x9b24f2490490f91e7238,0x9ad932325d64b2495392,0xa4f649e693ab27124df4],#[0x6328ae512ca1f941d27c,0xa8694eb2966529ca3794,0x25734ad595732aa254bc,0x6d2c9658fcb0395fb2bb,0xb7596c92d4e5a14b3c96,0xe5dfcba397252e065bdc,0x4b3052601cbfd97c32f6,0xc4e9891310a61e4c3698,0xe646cc7c98ed31c262a4,0xfd338a65dccaa9949324,0xd3d9a6f34c668acd0f99,0x26d9cda29b0d35aa6a1c,0x737f66f64ddb9b95371,0xe379c6338ae712ce149c,0x67464e869cd5393a71ec,0xe53bb27734ee09d893a7,0xf3c9e573c6a78a4f039d,0x27c34f809edf3d7a7a6c,0xad3f167da4fa39f253e3,0x15a01f3ffa7f6cfdc9f,0xa83ad064a09140de8135,0xa142fe851d09da119421,0x13ba23f440e873d0d6a1,0xe8d8d195a30945a28a65,0x2f47ee8fad1d9a3a746d,0x26ca4b74956927d23ea4,0xa94ad284a4fd49e29395,0xcb4b52961d2b2a5594a9,0x319a6274c36983d2f6a5,0xa9ac5347a6834cee9955,0xf4e069bdd375a6c94d7,0x3dca7974eea9d4d398a7],#[0xea13540aa7f34fce9f15,0x1951eea2fd459a89150d,0x4cba98b52d2a4c5492a9,0x6a9054f9a9e753b6a6e5,0xf755d6ab25553aa8554c,0x5baab53568eac9558caa,0xeafcd5f3abdb579eaeb5,0x6758b6b13d621ac2157f,0x667acc35942b255639ac,0x2b5356a0ad355a26b41d,0xab5b3eb64d6b8ad655ab,0xa86adf15b9eb70d6dbad,0x40a8508004bc02850380,0xf00070150a07142f8002,0x447010041702a101f685,0xc100183f18c060105a0a,0x240ffc001c16a74cc020,0x150a068c000107c24cc0,0x401502e140903ef000b8,0x83c010b038283e0470,0x2c1c0542025046070308,0x381831047e000e0808f4,0x440980810b14128220,0x27301a14220bb282304,0xb00e301490e10070381,0x202e054204002c043810,0x5230800540f8170810c1,0x1812284307fe14407010,0xa8407c0c820640880870,0xa08c1741c0e0802e00e0,0x381c081f02a047c04170,0x601c1541c0c04c87080],#[0xc1c1000e0b8304704015,0x70230541f800411c1c05,0xec1483e0020100c87041,0x80a07c07404870e43832,0x30380c44062070204760,0x404c08810014102458,0xe5045e03112c28480021,0x281c101001602801c404,0x780c4370a0c4204a089c,0xa0003f0008bc03815851,0x2780081983f062184307,0x780538093b1122b07074,0x107804160a84028c1c22,0xe0b815060981202e0c,0x7c2807054183f0460a83,0x82a07c0b830100a870,0xa84b020c8241e61c2d0,0x1201fc002f12208bb064,0x60c0b00e0a8304710420,0x50609411820f0102c597,0xc21681e040fc404702c1,0x10460c415060b81f02a0,0x5e2025f07e00178941c,0x3c00ba024384097c1f80,0xd0417800413025e0bc1,0x405d6001802f0542f8,0x9601c001a1808304b001,0x256000a00a100901060,0x87046089c25801060406,0x284307e0f80858070006,0x68604808d00f80034,0x250b41020860fc1f201f],#[0x202a140084040107c0a8,0xa42820f800840285048,0x848110a0a12041f02e,0x82a040d0205020442820,0x5a0c105c082e0400540,0x100608085404180a1401,0x24101a0808000c12080c,0x8202000a044280208018,0x1044082204060880c200,0xa08007c083e074183808,0x42c0056000802a0c2002,0x820002b001a0404c0020,0x80084004151800,0x1c08087800900820a810,0x20204010540c410620c,0x80a08058081038080204,0x80400100442a02081003,0x818100105e0220851060,0x82100100010201010200,0x8006c002049c28220f00,0x1b00e1423000d4eb0015,0xc004600100c002001600,0x941021e00303c002004,0x400002820042000402,0x100000038342c1080084,0x450643845040384100,0x848045d8450420045042,0x3820210041102089c2,0x4100e0c1006080430800,0x2068104e080704038209,0xc1000382000000707c00,0x9080210c100000080381],#[0x601c10800f020417c870,0x4010800942f00504038,0x8201c100e081c045d82,0x8428201c150e0840070,0x40b087020184006008bb,0x100e0cbb04002008220,0x8080a050802841c28460,0x10340b850415020a8120,0x1f0108170209017040b8,0xbf400403040061019042,0x44004411018400817840,0x803d00110406080200,0x110010030482034101d0,0x5a002005a002014080,0x1001104006101a001000,0x803041702002e02c1001,0x81f820fd822030c00180,0x2c043018220308407010,0x8c1047a00203208c603,0x421e800b41838074004,0x8208c0d0408fc0040043,0x430341043f0017010780,0x41080002080404080200,0x80060407c04410a084,0x10030041000082010102,0x140a0801040482804200,0x50413020801001702840,0x8020020060802000000,0x85040034282000214100,0x40a810380820141d0a0e,0x100e102e00e1000a8038,0x260801a0c1250109e1f0],#[0x20a8103408003f00843,0x206a090560f808270c17,0x200fc04205c081a040d0,0x182e041702040107c08c,0x58504012010827f01b06,0xe0d8582010161680840,0x20825a021f01f0001c30,0x80810540f0100f104302,0x7808230a20f0150e181,0xb4045d8607018821080,0x2e065d820b8182102c2b,0x5020281008082405410,0x304018200c1018080704,0x60802040400707a180,0x2000042301011e002000,0x35048200408080001000,0x20b80384090105401c20,0x440618011001002041e8,0x15020001021a030821b0,0x8000008000400108,0xe10bb07810200070404,0x87040383c041054082a0,0xf54184e1010000040a,0x803040383a00100008,0x38201c100a081904000,0xc1010000207a080704,0x15c2180034300806c002,0x3d0413b857081a12420e,0xf00083d300103db0010,0x800010001c1f00080004,0xe10000000001c107a080,0x1b060801060102011060],#[0x420028401c100808000c,0xc09c0820202820144204,0x40402708002020201c1,0x8001000020020805,0x300208020403c410804,0x104000000000800800,0x8038201c100e08181,0x7040400008040,0xc100105008100428200,0x40c022ec200038200,0x8080001c04103810200,0x8008000300400420000,0x2010000200000200,0x30b8083a001608020201,0x42180801c1904042190,0x581020410040b000810,0x10000007060800301,0x800e07040a201b00180,0x208c308008400288043,0x40200c440440800031c,0x3000860708049040811b,0x20bc045e020014b06804,0x4804240204805087028,0x7e081024b0a41009080,0x8200c002c0882f000e,0x1840042002007c0040c5,0x8e17c00070c18d0404c,0xc2816a08202002c21c0a,0xb007080b0140a0a02099,0x5003860580a0401c1000,0x2a040906080704002c0,0x306808340410001820],#[0x2058200000f40040000,0x28380a80840101000000,0x7a08c20220d01080,0x3820000141a0208001c1,0xe100104000e0807040,0x7802100704000e082a,0x8040000a060203041840,0x74042a020a83060940a0,0x18060abc0403822f01d0,0x20000000000045e020c4,0xa0826040182000506808,0x25007080382000014180,0x20010020808084002004,0x5050282080100000be00,0xe85074283c0414020e8,0xc041602080014100000a,0x20020800301040038083,0x4005820408042f0001c,0x1404004008001c1000,0x400400020001000002,0xdc6040002014100e080,0x4108008167000503000,0x382003d00e1004,0x800015c60403820001,0xa8384020020000dc2820,0x820c410808b018400001,0x306808340410440b85b0,0x2010b80820105004100,0x7c041e022002183f104,0x202183840f41092c1582,0x808200410182b040b808,0x1078083e001000080107],#[0xc19082e0208840020f0,0x8008810002020c811089,0x82001c04101000020080,0x4c080504001608050445,0x460582000e0208010400,0x2206808380a008408810,0x5404102c283404104e08,0x20800301058082841838,0x2020141001fc02080e0,0x38241c8084050838200c,0x4116050ac1020007040,0x88408110209410440822,0x20800041e020a010442,0x40b3050c000008010400,0x104120209c100008209,0x42140504000a08000007,0x20201824f01e020b820,0xc10002000827040007a0,0x2000020000401680848e,0xc101990e100002204110,0xd001081ea8710c183d90,0x142806081a00e120f040,0x8580c105408002810548,0xc100010221101840a802,0x8106c082308000428200,0x85e040035b0210000005,0x40a810540819040c8280,0x1000b810011820a8038,0xe0c85040001502000800,0x1700040282000a04100,0x23c00400080001003e0,0x183c001108080],#[0x2080e041000005c00200,0x1081e987302181904003,0x1e000d040381041ed8,0x9010bc0804d83404180,0x82a0401760c0206010bb,0x1c19760812ec10480,0x8040000800020000,0xc2b081111d87c1410004,0x40c16082a040000b0208,0x2304190208c1404082a0,0x1016080504000001408,0x207420382c100130201,0x780820880b0707038207,0x61004ec1031d83a04104,0x9040140204000e084f80,0xb06082a00e140b812100,0x40941a044ec2a044ec2,0x68104010800a10121681,0x1ea812761f0227610101,0x81000000000080013b04,0x17060805040011d8209,0x74282000030705c08201,0x80100000208006840,0xa8106e30200410020800,0x187094082000704030e0,0x410061c130e098707c0,0xc107c01c2000d0408881,0x60206001c141f0008001,0x80820040383414100f01,0x2010104004a0800801c0,0x3050782f0409c08,0x38282000000604170008],#[0x1282040280210181010,0x80000000e0c10000000,0x100002702]]
set_option maxRecDepth 16000 in
def g127H7 := limbs80 #[#[0x3000a108000800008800,0x118030000000500,0x28230808118084180a1,0x40100c000000d20004,0xd75a3080202c48001c80,0xc55580010fbd97000628,0x572a448ca9d8a0400029,0x28000000000000025bdb,0xea20000002ab78562,0xcc14218000ca30d10000,0x14ae0000000001,0x196e0000002f30000000,0x42c000000000,0x3e0000001db4000f0200,0x3629dee,0xe0f8000ef40000,0xd1f80000000000000000,0x597800031bda47908000,0x6b8999b4000000687166,0x10be000000490617fa5,0x112830e00,0x79f0007c140000,0x0,0x0,0x208781a224000000,0x45e3674000000000000,0xd6000000000000000,0x0,0x0,0xd2680000000000000000,0x1fa48140003640000000,0xe1c8000d9400010c800],#[0xc7a181734a800000000,0xb3790,0x181c0,0xc5d000395c001a110000,0x2a5c00000000032376bd,0x2d2e948000000000000,0x6edc00,0x1280000054000000000,0x4cd4000da166c5d7c0,0x31f05581710,0x1ee00000000000,0x9198000000a0f,0x1434000000000000,0x253d835000000000000,0x0,0xb50000000a84c9000000,0x62c9c0e0010000,0x0,0xb14f854000000000,0x3e28f89000000000,0x540000004990000f9a00,0x449a0c1250e0280037,0x49480000000,0xa2100000000000000000,0x4156444000,0xc8a8000000000461fee,0x20000e3400019d400000,0x590000000000d4000004,0x1c,0x19e80000007100,0x0,0x400000000f45520002a7],#[0x129adae6b8d90000234,0x9169b00049ba85c00000,0x6a6660973924c00030,0x0,0x0,0x331d8ca000,0x86b25c44036569000143,0x64b1b6a229504180019c,0x55780000008d300054,0x4889340000006af80000,0xcba0003,0x9ad2ce800000052c0000,0x137c00011a4001acc55c,0x2eba000727a98400,0x4000f358002989a8600,0x2c0000000a0a00011e78,0x160914900039776461,0x5040000e0e25a0000000,0x18a80000000888000,0x69fc00000002599c,0x41ecc2c80,0x138000000c1200000,0x0,0xc1e7076c4c000b4b0,0x8db91c,0xa540007ac4000000000,0x58000b4e472e17949c00,0x70494000000000000094,0x94878a309e6d80,0x62da22000044c0,0x69e00000018040000198,0x0],#[0x0,0x0,0x3e000000000000000000,0x1f5400010b40018,0x4280000000000,0x79cc000000b9b2e98000,0xba28000000000000,0x59f8154468000000000,0x10b5fa596e800063100,0x38b94b6c8800000,0x992b88000486b4940000,0x59bc898ae0000,0x8506000fb30002c8a20d,0xdd2ab2c000cc2000113,0x263c5382f400000,0x230003a08b6600084f80,0x35b20000002b200001,0xe457b16cce63a0000,0x7214000,0x442f2b000,0x2b56f08f230943800000,0xbd8938120002c54000b1,0xc5f2cc0008780004078c,0xa0580029a00001,0x12954ec0004e48000,0x800046a000000299e000,0x29486a82248a9d00000c,0x58000000ac780018a646,0x5b901de4,0x60600000,0xc23485800000080c7248,0x0],#[0x119300000000000002ac,0x5a8419c000000000000,0x643c00127100,0x8c000000000000000000,0x5631a3c000cc09]]
set_option maxRecDepth 16000 in
def g127D8 := limbs80 #[#[0xe756558510fe12148110,0x9df835d91097f855c910,0xe756558521ed96358130,0xc7d765952197f855cd21,0x97e875952197c8759521,0x97f855d92197d86dd521,0xe756558531ed56358531,0xc7d65dc961e756558541,0xc7d655cb61e778159561,0xb77815cd659fb805d943,0xff13148110a7f865cd65,0xff16148110ff14148110,0xbfb8348110bf98348110,0xdf97648110f796548110,0xff1214c110dfb7648110,0xff1614c110ff1414c110,0xfd9634c110fd9434c110,0xdf9764c110f79654c110,0xff12158110bf9864c110,0xff14158110ff13158110,0xff38158110ff16158110,0xdfb7258110df97258110,0xef96358110bfb8258110,0xdf97358110efb6358110,0xbfb8358110dfb7358110,0xefb6458110ef96458110,0xdfb7458110df97458110,0xfe53248510f796558110,0xbf58348510fe56248510,0xdf77448510df57448510,0xf756548510bf58448510,0xdf57648510f778548510],#[0xbf58648510df77648510,0xfd5634c510bf78648510,0xf75654c510bf5844c510,0xbf5864c510df5764c510,0xdf77250510df57250510,0xfb56450510fb54350510,0xdf57650510f756550510,0xbf58650510df77650510,0xdf57258510ff38058510,0xbf78258510df77258510,0xef76358510ef56358510,0xdf77358510df57358510,0xdf57458510bf78358510,0xf756558510df77458510,0x9fd874c910ddf734c910,0x9fd8758910e7d6558910,0xbf980d89109ff8758910,0xe7d65d8910bf581d8910,0xb7f855c9109fd87d8910,0xd7d655c9109ff835c910,0x9ff865c910d7f855c910,0xd7d65dc9109fd84dc910,0xbfb8050d109fd86dc910,0xdbd7450d10ddf7350d10,0xddd7358d109fd8750d10,0x9fd8758d10cfd7658d10,0xbf980d8d109ff8758d10,0xddf73d8d10bf581d8d10,0x9fd87d8d10cfd76d8d10,0x9fd82dcd10d7d655cd10,0xd7d65dcd109fd84dcd10,0xbfb80591109fd86dcd10],#[0x9fd8759110dbd7459110,0xbf581d9110bf980d9110,0x9ff825d1109fd87d9110,0xd7d655d1109ff835d110,0x9fd82dd1109ff865d110,0x9fd86dd110d7d65dd110,0xd7d7659510f778159510,0xbfb805d910d7f7659510,0xbdf835d910bf7815d910,0xdf7815d910dfb805d910,0xddc835d9109ff825d910,0x9ff835d910ddf835d910,0xbf9809d9109ff845d910,0x9fd879d910bf5819d910,0x9fd84dd9109fd82dd910,0xbfb8158130dfb7158130,0xfd94358130dfb7258130,0xfdb8358130fd96358130,0xefb6458130ef96458130,0xdfb7458130df97458130,0xdf77148530f796558130,0xf9d4350530b7f8548530,0xe7d6558530edd6358530,0xbf980d85309ff8758530,0xbdd83d8530edd63d8530,0x9fd87d8530e7d65d8530,0xddd63dc5309fd82dc530,0xd7d65dc5309fd84dc530,0xe7d65589309fd86dc530,0xbdd83d8930bf980d8930,0x9fd87d8930e7d65d8930,0xddd63dc930ddd43dc930],#[0xd7d65dc9309fd84dc930,0xfdb8050d309fd86dc930,0xf5d6550d30f9d6450d30,0xddf7650d30ddd7650d30,0xbdf8650d30bdd8650d30,0xddd7458d30fdb8058d30,0xbdf8458d30ddf7458d30,0x9fd8759130f5d6558d30,0xbf980d91309ff8759130,0x9fd87d9130bdd83d9130,0xdfb805d130bfb805d130,0xd7d655d1309ff815d130,0x9fd82dd1309ff865d130,0x9fd86dd130d7d65dd130,0xd7f7659530d7d7659530,0xbdf835d930bfb805d930,0x9ff815d930dfb805d930,0xddf835d9309ff825d930,0xbf9809d9309ff845d930,0x9fd879d930bdd839d930,0x9fd84dd9309fd82dd930,0x9fe8748560b7f8548560,0x9fe874c560edd634c560,0x9fe8750560ebd6450560,0xdf77158560bfb8058560,0xbdf835c560e7d6558560,0xcfd63dc5609fd82dc560,0x9fd83dc560cff63dc560,0xd7d65dc5609fd84dc560,0xafd8650d60edd6350d60,0x9fe8750d609fc8750d60,0xbfb8058d609ff8750d60],#[0xe7d6558d60ddf7358d60,0xedf7358d60efb8058d60,0xafd84d8d60aff8458d60,0x9fd82dcd609fd81dcd60,0xd7d65dcd609fd84dcd60,0xb7f8548760df57148760,0xdf5714c7609fd8748760,0xddd734c760edd634c760,0x9ff825c7609fd874c760,0x9ff835c760cfd635c760,0xedd6350f60bfb8050f60,0xafd8650f60ddd7350f60,0x9ff8750f609fd8750f60,0x9ff815cf60aff8458f60,0xd7f755c1219ff845cf60,0x9fd86dc121df561dc121,0xfe56250521fe53250521,0xfb56450521fb54350521,0xbf58650521df57650521,0xfe56258521bf78058521,0xef56358521fe78258521,0xdf57358521ef76358521,0xf756558521df57458521,0xbf78150d21f777558521,0x9fd8750d21d7f7550d21,0xddd7358d21bf78158d21,0x9fd8758d21d7f7558d21,0xbed82d8d21bf581d8d21,0x9fd87d8d21d7f75d8d21,0xd7d76dd521d7d7659521,0xb7d86dd521d7e76dd521,0xd7d86dd521d7d80dd521],#[0xbf7815d921d7e86dd521,0xdf7815d9219ff805d921,0xd7f855d9219ff835d921,0x9fd879d921bf5819d921,0xbf780585319fd80dd921,0xfd78358531fd56358531,0xf756558531df57458531,0xbdd83d8931bf581d8931,0xfd78158d319fd87d8931,0xf5d6558d31ddd7458d31,0x9fd8759131dbd7459131,0xbdd83d9131bf581d9131,0x9ff805d1319fd87d9131,0xd7d655d1319ff825d131,0xd7d76595319ff865d131,0xdf7815d9319ff805d931,0xddf835d9319ff825d931,0xbf780585419ff845d931,0xfb54358541bf78258541,0xf9d434c941ef56358541,0x9ff8758941ebd6458941,0xf3d6550d41f9d6350d41,0xbbd8650d41dbd7650d41,0x9ff8758d41bbf8650d41,0x9ff805d941bbf8359141,0x9ff835d9419ff825d941,0xe7d655c161bdf835c161,0x9fd82dc161e7d65dc161,0xcff63dc161cfd63dc161,0xd7d65dc1619fd83dc161,0xe7d6558961bf78158961,0xb7f855c961e7d655c961],#[0x9fd80dc961e7d65dc961,0xd7d65dc9619fd83dc961,0xddf7350d61edd6350d61,0xbf78158d61e7d6550d61,0xe7d6558d61ddf7358d61,0xedf7358d61ef78158d61,0xe7d65dcd61e7d655cd61,0x9fd82dcd619fd80dcd61,0xe7d6559161d7d65dcd61,0xf778159561e7d655d161,0xcfd635c3619ff825c361,0x9ff845c3619ff835c361,0x9ff845cb619ff805cb61,0xddd7350f61edd6350f61,0xe7d6550f61dbd7450f61,0x9ff8750f619fd8750f61,0x9ff845cf619ff805cf61,0x9ff825d3619ff805d361,0x9fd81dc1439ff835d361,0xd7d65dc143ddd63dc143,0x9fd80dc5439fd86dc143,0xddd63dc5439fd82dc543,0xd7d65dc543dbd64dc543,0xbdf8058d439fd86dc543,0xf9f8458d43f9d6458d43,0xedc7658d43f5d6558d43,0xd7d7659543edf7658d43,0xd7c8759543d7f7659543,0xbf9801d943d7f8759543,0xcfd761d943bf5811d943,0xbfb805d9439fe871d943,0xcff765d943bdf835d943],#[0xdfb805d943df8805d943,0x9ff815d9439ff805d943,0xbdd839d943ddf835d943,0x9fd879d943cff769d943,0x9fd81dd9439fd80dd943,0x9fd84dc1639fd81dc163,0x9fd80dc563d7d65dc163,0xd7d65dc5639fd84dc563,0xbfb805d163bdf8359163,0x9fd80dd163aff865d163,0xd7d65dd1639fd81dd163,0x9ff815c363f5f8359563,0x9ff845c3639ff825c363,0x9ff825c7639ff805c763,0x9ff815cb639ff805cb63,0x9ff805d3639ff845cb63,0xb7f805c5659ff825d363,0xb7f865cd65b7f805cd65,0xff94348110d7f74dcd65,0xffb6348110ff96348110,0xff97648110ff98348110,0xff9424c110ffa7648110,0xffb624c110ff9624c110,0xffb644c110ff9644c110,0xff94258110ff93258110,0xff97258110ff96258110,0xffb8258110ff98258110,0xff96358110ff94358110,0xffb8358110ff98358110,0xff97458110ff96458110,0xffb8458110ff98458110,0xff56348510ff54348510],#[0xff56448510ff76348510,0xff57448510ff76448510,0xff67648510ff57648510,0xff68648510ff58648510,0xff5624c510ff5424c510,0xff5644c510ff7624c510,0xff53250510ff7644c510,0xff57250510ff56250510,0xff57650510ff56350510,0xff54258510ff53258510,0xff57258510ff56258510,0xff54358510ff78258510,0xff78358510ff56358510,0xff57458510ff56458510,0xfdd434c910fed624c910,0xdfd744c910fdd634c910,0xdfd764c910bfd844c910,0xdfd7350910fed6250910,0xfbd6450910dff7350910,0xdff7650910dfd7650910,0xbfd8750910bfd8650910,0xdfd7358910fed7258910,0xefd6458910dff7358910,0xdfd7458910eff6458910,0xbff8458910dff7458910,0xdfd7658910f7d6558910,0xbfd8758910dff7658910,0xdfd73d8910bff8758910,0xbfd83d8910dff73d8910,0xbfd84d8910efd64d8910,0xdfd745c910bfd87d8910,0xf7d655c910bff845c910],#[0xdfd765c910f7f855c910,0xbff865c910dfe765c910,0xdfd635c910dfd435c910,0xdfd835c910dff635c910,0xdfc865c910dff835c910,0xdfe865c910dfd865c910,0xdfd64dc910dff865c910,0xff58150d10dff64dc910,0xfdd6350d10bff8250d10,0xf7d6550d10fbd6450d10,0xbff8650d10dfd7650d10,0xdfd7458d10dfd8750d10,0xf7d6558d10bff8458d10,0xbfd82d8d10dfd7658d10,0xdfd645cd10bfd84d8d10,0xdfd64dcd10dff645cd10,0xffb8059110dff64dcd10,0xbff8359110bff8259110,0xf7d6559110fbd7459110,0xdff7659110dfd7659110,0xbfd82d9110bfd8759110,0xbfd87d9110bfd83d9110,0xdfd765d110f7d655d110,0xdfd835d110dfd825d110,0xf7d7659510dfd865d110,0xff7815d910ffb805d910,0xfdf835d910bff825d910,0xdff845d910bff845d910,0xbfd849d910bfd829d910,0xff94158130ff92158130,0xff98158130ff96158130,0xff96258130ff94258130],#[0xff98258130ff97258130,0xff97458130ff96458130,0xff54148530ff98458130,0xfed6248530ff56148530,0xfdd6348530fdd4348530,0xbfd8448530dfd7448530,0xbfd8648530dfd7648530,0xfdd6350530ff56150530,0xf7d6550530fbd6450530,0xbfd8650530dfd7650530,0xfdd4358530bff8258530,0xdfd7458530fdd6358530,0xdfd7658530f7d6558530,0xfdd43d8530bfd82d8530,0xbfd84d8530dfd74d8530,0xdfd62dc530dfd42dc530,0xfed6250930dfd64dc530,0xfbd6450930fdd6350930,0xdfd7650930f7d6550930,0xbfd8650930dff7650930,0xbff8158930bfd8750930,0xfdd4358930fed7258930,0xefd6458930fdd6358930,0xdff7458930eff6458930,0xf7d6558930bff8458930,0xdff7658930dfd7658930,0xbfd81d8930bfd8758930,0xefd64d8930fdd43d8930,0xfdd435c930bfd84d8930,0xdfd745c930fdd635c930,0xdfd765c930f7d655c930,0xfdd8150d30dfd64dc930],#[0xfdd8250d30fdf8150d30,0xfdd7650d30fdf8250d30,0xfdc8650d30fde7650d30,0xfde8650d30fdd8650d30,0xfdd6458d30fdf8650d30,0xbff8259130fdd7458d30,0xf7d6559130fbd7459130,0xdff7659130dfd7659130,0xbff8759130bfd8759130,0xbfd82d9130bfd81d9130,0xbff825d130ffb805d130,0xdfd765d130f7d655d130,0xbff865d130dfe765d130,0xdff815d130dfd815d130,0xdfd865d130dfc865d130,0xdff865d130dfe865d130,0xbfd829d930f7f8459530,0xff98048560bfd849d930,0xff56148560ff54148560,0xefd6348560ff57148560,0xdff7348560eff6348560,0xf7d6548560bfd8348560,0xbfd8648560f7f8548560,0xdfd8748560bff8648560,0xdfe8748560bfd8748560,0xff5614c560bff8748560,0xdff724c560ff5714c560,0xefd644c560fdd634c560,0xdff744c560eff644c560,0xbfd864c560bfd844c560,0xff57150560bfd874c560,0xfbd4350560dff7250560],#[0xdff7350560efd6350560,0xdff7258560bfd8750560,0xefd6358560bff8258560,0xbff8358560dff7358560,0xdff7458560efd6458560,0xdfd725c560ffb805c560,0xbff825c560dff725c560,0xeff635c560efd635c560,0xdff735c560dfd735c560,0xfdf835c560fdc835c560,0xefd645c560bff835c560,0xdfd745c560eff645c560,0xf7d655c560dff745c560,0xdfd82dc560bfd82dc560,0xff98050d60dfd43dc560,0xfdd6350d60bff8150d60,0xf7d6550d60fdd7350d60,0xbfd8650d60efd8650d60,0xbff8650d60efe8650d60,0xbfd8750d60dfd8750d60,0xbff8750d60dfe8750d60,0xefd7458d60efd6458d60,0xbfd81dcd60dfd745cd60,0xdfd81dcd60bfd82dcd60,0xf7d8159560dfd82dcd60,0xf7d8359560f7f8159560,0xefd6348760f7f8359560,0xf7f8548760dfd7348760,0xdfd724c760dfd8748760,0xdfd744c760efd644c760,0xffb8050f60dfd435c760,0xdfd8750f60efd8650f60],#[0xdfd765c121ff5615c121,0xbff865c121dfe765c121,0xff78058521ff56350521,0xff56358521ff54358521,0xff56458521ff78358521,0xfdd6350d21bff8050d21,0xbfd8650d21dfd7650d21,0xdfd8750d21bff8650d21,0xff78158d21bff8058d21,0xbff8458d21dfd7458d21,0xbfd80d8d21dfd7658d21,0xbff805d921bfd84d8d21,0xbfd809d921ff7815d921,0xff56258531ff54258531,0xfdd6350931ff56458531,0xbff8058931dfd7650931,0xefd6458931fdd6358931,0xdfd7458931eff6458931,0xdfd7658931bff8458931,0xefd64d8931bfd80d8931,0xfdd6458d31bfd84d8931,0xbff8259131bff8059131,0xdfd7659131f7d6559131,0xbfd82d9131bfd80d9131,0xdfd825d131dfd805d131,0xff58058541dfd865d131,0xff53258541ff78058541,0xff78258541ff58258541,0xff78358541ff58358541,0xdfd764c941fdd634c941,0xfbd4358941bff8058941,0xfbd8250d41fbd8050d41],#[0xbff8058d41fbd8650d41,0xfbf8059141fbd8059141,0xfbf8259141fbd8259141,0xfbf8359141fbd8359141,0xf7d655c161bff845c161,0xdfd43dc161dfd62dc161,0xefd6358961dfd64dc161,0xbff845c961dff7358961,0xdfd43dc961f7d655c961,0xbff8050d61dfd64dc961,0xbff8250d61ff58150d61,0xfdf7350d61fdd6350d61,0xf7d6550d61fbd6450d61,0xbff8650d61bfd8650d61,0xefd6458d61dfd8750d61,0xbff8059161dfd64dcd61,0xbff8359161bff8259161,0xdfd435c361dfd825c361,0xbff8050f61dfd435cb61,0xdfd835d361dfd8750f61,0xdff715c143dfd715c143,0xfdd635c143bff815c143,0xdfc765c143f7d655c143,0xdfe765c143dfd765c143,0xbff865c143dff765c143,0xf7d65dc143fdd63dc143,0xdfe76dc143dfd76dc143,0xdfd86dc143bfd86dc143,0xdfd725c543dfe86dc143,0xfbd645c543fdd635c543,0xdfd765c543f7d655c543,0xfdd63dc543bfd80dc543],#[0xf7d65dc543fbd64dc543,0xbfd86dc543dfd76dc543,0xfdf8058d43fdd8058d43,0xfdf8158d43fdd8158d43,0xfdf7658d43fdd8258d43,0xf7f7659543f7d7659543,0xf7f8759543f7c8759543,0xff8805d943bfd801d943,0xbff805d943ffb805d943,0xfdf835d943bff815d943,0xbfd809d943dff765d943,0xbfd879d943bfd819d943,0xdfd80dd943bfd80dd943,0xdfd64dc563dfd64dc163,0xbff845c963dff745c963,0xf7d655d163bff825d163,0xdfd82dd163bff865d163,0xdfd815c363f7f8459563,0xdfd805cb63dfd825c363,0xa200560000dfd815cb63,0x1be0186013000da00,0x4a030802bc027a022e02,0x9e0448041003e203a003,0xd4059c056e052204e004,0x1e06dc06ae0662060c05,0x1807e007bc078e075607,0x1c08e408c00888086408,0x520a2409e209aa097209,0x740b460b180acc0a9e0a,0xbe0c720c1c0bda0ba20b,0x300dbc0d840d380d0a0c,0x3e0f060ed80eb40e680e],#[0x881050100e0fcc0f760f,0x821154112610ee10b610,0x9a126c123411fc11ce11,0xbc135c1342131412e612,0xf214ce148c145413fe13,0x6415f015b81576152a14,0xe0179e173e16f2169c16,0xc18de189c186e182217,0x881a4619dc199a194e19,0xd21b681b1c1ae41ab61a,0x81cda1ca21c6a1c461b,0xf81db61d921d781d401d,0x561f0a1ec81e861e3a1d,0xa0206820301fe41f981f,0x821d021982156210a20,0x4822f222b0226e224a22,0x4c242823d223ae238023,0xa0254a24fe24c6247a24,0xd6268a265c262e25ec25,0xbc277a274c2732270e26,0xde28922864281827fe27,0xf629aa29722944290c28,0x42ae02ab22a662a2429,0xd62bbc2b7a2b602b322b,0xee2cc02c7e2c5a2c362b,0xfc2dce2d8c2d402d1c2c,0x462ee62eb82e762e482d,0x9a306230202fe82f922f,0x6c313e3124310030be30,0x703238321431e631a431,0xe2338c331832cc329432,0x2234ea34b23470342433],#[0x835bc35983574355035,0xee36d436a63678363636,0x2437ec37aa375e372636,0x3c390e38d6389e385c38,0x723a4e3a3439e8399239,0xbc3b703b243ad83a8c3a,0x63ce23caa3c723c303b,0x283ddc3dae3d763d483d,0xae3f443f163ed43e743e,0xc40ca408840463ffa3f,0x56422841dc4186414441,0xc84390434e431642b642,0xd6449e445c441a43f643,0xa8458e45604528450444,0xf246d8466e45fa45cc45,0xd84796477c4758472a46,0x448cc486c482a480647,0xf449c64998496a492849,0x204af24ac44a784a3649,0x6a4c464bfa4bae4b624b,0x784d4a4d1c4cee4cc04c,0x7c4e584e024dde4da64d,0x6c4f524f1a4ef64eb44e,0x7a502e4ff64fc84f904f,0xa65164512250ea50b250,0xa05272524e521651de51,0x72534e532052de52ba52,0xb25466542453ec53aa53,0xb6559255645536550854,0xce5696565e562655f855,0xe657c257765748571056,0xf458a8587a5838581e57],#[0xf859d459885950592258,0x425b0a5abe5a7c5a2659,0x1e5bfa5bcc5ba85b665b,0x5e5d305cee5cac5c605c,0x8a5e525e065dce5d8c5d,0xf25fa65f505f045ec25e,0xa60dc60a4606260345f,0x4a620861d0618e614c61,0xe463ac6360631462a062,0xf26492646e6440640863,0x50662265f4658a655264,0xc2678a6752671066b066,0x268c06874683c67fa67,0x1069ec69a0695e692669,0x6e6b0e6acc6a9e6a3e6a,0x906c6c6c166bca6ba66b,0x9e6d706d2e6d006cdc6c,0xd46e9c6e786e226de06d,0x1e6fe66f9a6f4e6f0c6e,0x4a711c70da7098705670,0x26720271d471a6717871,0x2072f272ba728c726872,0x1073e273aa7372734473,0xa74e6749a7462743e74,0xfa75cc759e757a754c75,0xcc769e76667642761e75,0xf877c07792775a770e76,0xf278ce78a07868783a77,0xce79a0797c794e791678,0xd27a907a587a2a7a1079,0xa47b767b3e7b247af67a,0x627c347c1a7bf67bd27b],#[0x2a7d1a7cec7cc87c9a7c,0xfc7dd87da07d907d627d,0xe27eaa7e727e4e7e207d,0xa07f727f447f167efc7e,0x72805880167ffc7fd87f,0x448120810680e280b480,0x1681e881ba81a0816881,0x2e830082c88286824482,0x5a841883cc83a8837a83,0x36851284e484ca848884,0x30860285ca8588855a85,0xda86b6869c8682864a86,0xd48792875a872c86fe86,0x92886e88548830880287,0x648940891288e488c088,0x1889ea89c689a2898889,0x88af88ac08a9c8a5a8a,0x948b7a8b608b3c8b188b,0x3e8c108bf68bd28bb88b,0xfc8cc48ca08c908c6c8c,0xba8da08d7c8d588d2a8c,0x788e4a8e268e028dde8d,0x408f1c8ef88ede8ea68e,0xf48fc68f988f7e8f5a8f,0xa89084906a903c90228f,0xac917e915a913690ea90,0x4c9228920e91ea91d091,0x1e92f092c2929e927a92,0xb4939a93769366934293,0x5e9444942a93fc93d893,0x1294f894e894a6947894,0xd095ac9588955a953695],#[0x70964c9632960495ea95,0x6a973c970e96c2968a96,0x1497fa97e097bc978e97,0x96987c986c9852982e98,0x2c98fe98e498ca98b098,0x1299ee99b6997e994699,0xc9ae89ab09a829a5e9a,0xde9bba9b789b409b269b,0xe29caa9c5e9c3a9c0c9b,0xaa9d729d4e9d2a9d069c,0x869e4e9e2a9e109de29d,0x589f349f109ee29eb49e,0x209ffc9fce9faa9f869f,0xf2a0cea0aaa086a062a0,0xbaa196a168a13aa116a0,0xb4a286a258a20ca1dea1,0x86a34ea320a306a2e2a2,0x80a452a424a3f6a3bea3,0x66a542a51ea4dca4a4a4,0x60a632a604a5cca594a5,0x14a6faa6e0a6bca68ea6,0xa0a786a762a73ea72ea7,0x72a84ea834a7fca7c4a7,0x58a934a906a8cea8a0a8,0x16a9fca9d8a9aaa986a9,0xdeaabaaa82aa68aa3aaa,0xaabdcab90ab4eab16aa,0xaaac86ac6cac48ac24ac,0xaead80ad48ad10ace2ac,0x94ae70ae38ae14adf0ad,0x70af56af28aefaaeccae,0x6afe2afc8afaeaf9eaf],#[0xceb0aab07cb062b034b0,0x82b168b13ab120b0fcb0,0x40b21cb1eeb1cab1a6b1,0x26b2e4b2a2b27eb25ab2,0xe4b3b6b392b378b34ab3,0xa2b474b446b422b408b3,0x56b528b50eb4e0b4c6b4,0xb5dcb5c2b59eb57ab5,0xe6b6b8b676b65cb638b6,0x90b776b75cb72eb714b6,0x58b834b810b7ecb7c8b7,0x2ab8f2b8ceb8aab87cb8,0xfcb9c4b996b97cb958b9,0xbaba96ba68ba4eba2ab9,0x8cbb68bb3abb16badeba,0x72bc26bbf8bbcabba6bb,0x4ebd2abcf2bccebc96bc,0x20bdfcbdcebd96bd72bd,0xe8bec4bea0be7cbe58be,0xb0bf96bf72bf4ebf16be,0x78c05ec030c00cbfdebf,0x36c112c0e4c0c0c09cc0,0xfec1dac1b6c17ec15ac1,0xbcc2a2c27ec250c236c1,0x98c356c332c304c2d6c2,0x42c414c3fac3d6c3bcc3,0x1ec4f0c4c2c494c470c4,0x8041ce001f0a88c54cc5,0x90fa1c4182e1d4e3302e,0x83c0815c041314bb0a8c,0xb01a1f85e0c428438022,0x7e1783073800c48c0],#[0x5183f01f810b82a16011,0x2e0a84af381a1303c081,0xe87e04000b4291e800f8,0x1f8105703c081318430f,0x2187128420fb03c087a,0x92287e07030570204c6,0x8601f85e0c420c840e00,0x42e100710832e17810a,0xfc23e042a0b850ef84e,0x90f435e06800781a06c8,0x610c2401f810b82a184,0x440f1e8712304c178010,0x5c0f1307c0381056840,0x504b80a141c0a8505411,0xf800408123800401f0b8,0x702a1c3e6ec23a1448a0,0x7c2a10400a012e00850,0x2841808042e0a8607380,0x1c141041003c083f161,0x17800702a103f04a83e0,0x3a17800705e010b0703e,0x20e0e02e018507076ec2,0x61c0a85e00400703100,0x11005904420703a15809,0x8560f80040805085e024,0x78004141154e73022067,0x1822043802ed0b1422a1,0xc441128580780040bb,0x83c081001f801c100cf8,0x8760c22e001c1012069,0x70410c851101060f80c,0x408b802ec1c1031e0040],#[0x28750410154101f80070,0x82221440e01411822e0,0x10087e00100cf026148c,0x204016e0302614871c48,0x10c082c05b80614bb1c2,0x10bb5047e01850704410,0xe141c0a8509d80842851,0x410385e0301068b10380,0x1c0a85938cc10dbc0930,0x2c413010b870fb85e00,0xb84e001c0b830fc10e0,0x603010b82a143ee0301,0x43f2210203010b429161,0x70693acce141041003c0,0xa0c3e1acce143fa0f800,0xab010b85e148006801,0x1c17851038007040fb8,0x2418702a143e0bc0be0,0x90f840430110a4113856,0x10c0448e002e1f850040,0x705123800702e1050128,0xc040b2ec51002f02f800,0xb1e10c04bb0b8410380,0xc1c104a04044e03012ee,0xb8002cbb120482f802e,0x260f0104007e0090f832,0x8308f800706122bb0681,0xc2304183e03012048aed,0x1432e00400705e144f2e,0xc0dc608f85e00bb0706e,0x23a1f80610101407e001,0xb852ec2361380103011c],#[0x1105043010b38002cbb1,0xf603012ecb08c1c61780,0x51102384384e0c27e140,0x7800a88a1f85e01100a8,0xb82a1c530f4280700701,0x12842244321c24c044f0,0x4180801404a0f02c0400,0x22ec60f004c0b01e003,0xf80c04bb1c8511283e03,0x42e21c2a1044e1423a0,0x104401302c04bb0fc6c,0x5e00530a8607a8306e1,0x301600490b82a1c4201c,0x4a10c05800b82a1a1284,0xf40501301a0f02e00a8,0x7e001c0b82c184810008,0x3f10076021c0b840fc0,0x307e001c0bc51100507,0xbc84e0e87e028544071,0xf0582c40f01e000ba10a,0x8501c03e001c2c421002,0xc1c0c4d0f4380bc2c022,0x14320c780a1040178001,0x100251008016410703f,0x508885e00bb0705e178,0xd10a1c208f85e00bb07,0x3c0b012ec4218bb1081c,0x7815809042a87061100,0x8501081001c05e002a1c,0xa861080700f80a102c1,0x3040421e056024161e10,0x80a17021844905870140],#[0x2c02f012ec710304123,0xb012ec420fc710016e0,0x8a85e030221c5a1404c,0x80a14a08e85e030121c5,0x4a08c2200c8701302c07,0x83f0dc07013800b02e1c,0xb8510803aed84e002c1,0x32ef800b0585a10810bb,0x4810f8001c1c0b860100,0x285070441a1c1102e0c,0x7a8006b0106c610c03e,0xa004440f012ed412110,0xc402103a00bb470508d1,0x2380070330c85e001c08,0x10b83c0b01a1f85e0210,0x330003f0c440003f0c83,0x40501302c04431103f1c,0xfc421e10e17015043f1,0x1504422210e1404c0702,0x8511071128710385e0f0,0xf80070612804c0b83e01,0x14bb0f81c1043404852e,0x3e001c1c442ec1c0fc4e,0x1c2ec2c1448020430158,0x8310900608310c03e00,0x6141419834001c0c446,0x82e00bc0c46e0c220838,0xc4336147050330b85e0f,0x2f1850c4412014c03040,0x5814e0185c10071f00,0x1410c454001c61431102,0x1785e01140a8409d802f],#[0x22c1c1f07c168304e1c,0x310c81c10451002fa0f8,0xc2321f059061c0a86108,0x103b01403c1380c04231,0x4094bc070308b002f01c,0x42a21e1c10402f01c0c4,0x17800a82818400c42c1,0x800528226820c4210007,0x42a0c521002f6140700f,0xc042a1b80100310e050c,0x4a0f000c4421c4309305,0x42a0c431228300431100,0x2005a0c02e003f0c47c1,0x110480c283e018507061,0x7e02830707122830703,0xa058701d0c4412848614,0xc0412005e001ca0c311,0x221414e0301242f05380,0x13c06851dbb8102660f0,0x301e02852214e0f02600,0x1780070512b830c50205,0x8138012001100608383a,0x310f8008040a17011685,0x78005814c04071804100,0x111850c426141c0c4361,0x412380100509d802f03,0x3b00b04e03010d06a17,0xa14bc0c43c00bca14311,0x300703008bca17800c45,0x347058140c3800bc5e00,0x9cb10007a140360b801,0x1c08a170480e02c0580],#[0x3c0704a1780100885a14,0x707285e002818430f40,0xc08a16036021c0c4710c,0x141c00f8010e850c4609,0x2f11c1505a00bc50431,0x3e17800941c1008e168,0xc43000400c43e003307,0xf0158300b800c47e0040,0x311833050400c441203,0xbc07041298500b83e0,0xc42100bc070311101e,0x1c1405e001c2f028144,0x1283a0b011c4a61448e0,0xa0833e00311808c1f05c,0x5e00320c701224502283,0xf0122c6a1003a0b800cc,0xe82e0031144041f800c,0x1103b08901e003216850,0x30ef0130480cc000fc3,0xf80a0b01202220035c17,0xfc5610c784184c1f85e0,0x20e820c420140460f010,0x2820cc7100310a826102,0xce820c4710c4001003e0,0xc685c04703603805800,0x5a1001100741f83e0020,0x30e00220bcb41f801228,0x860200700c0200455114,0x2f1685a1383e0b8008,0xc143ce00311440c1c30e,0x3c304311b800cc400c32,0x407004400c4412601200],#[0x614311007e0033100311,0x9a8408985c04700780,0x500f01100c110870ef8,0x802c040560f80a109110,0xe84e0b800cc61082204,0x34eca80d803043310420,0xeb33854f02341301e028,0x5c1008a0e82c07071cc,0x808000541453c4ec3e1f,0x22464f023c07804ec891,0x4ec89193c09414c053b,0x3be03010c854f025c078,0x560e3bc07800c864f1,0xf03be002309701612822,0xec0500d84e030108c70,0x47c053b2700a1684c1c4,0x53b244b4f02005383e00,0x44be0d0211d3ce0301a1,0x4f0401a85a10014f0401,0xe03010bc512285a1380,0x250e3c61701094441c3,0x14038f380c04321b8010,0xa1612842872182d0a466,0x2ea042a1281e00220b82,0x10bb0b85e020b0a83e00,0xe0b800bc0b0a846f024a,0xc480b842ec4a0b832ec2,0x488493981e03032c842e,0x68bb2b4c0fc23e14bb0,0x9394ce0585a12022f380,0x4021f850c82a143f0c82,0x14bc0a8308f852ec2a10],#[0x3e042e21c2a18bb0b82e,0x2a0c3fa1c2d0a440fc2,0x1e81a1703c08131b800c,0xbc2d01e85007800a89a,0x3103850f7800a850f430,0x681c0f0204c6e14bc0a8,0xa840004a0a83e1287a1,0x6090852ec2a1023e14bb,0x82a1a85a0703c0813a1c,0x42e0a8714401000bb10,0xb182d0a440902321e80e,0x2d0a466042d0a5871181,0x415a00131c43e05870fc,0x415a00131f03c098760,0x548004d871f03c0987e,0x3e202e0902a0f03c0981,0x84150190140414702c0c,0x4421502a1042000340f,0xe0fc2a10000b82a0f84e,0x82a14000b82a0f8421c2,0x2181e00320c3d607800b,0x2f385e0c02e07802ec32,0x2f027802ec508c420243,0xf85e06412ec2a0c8602c,0xa0f802ed0914bb0c82a0,0xc5e00090c430fc320825,0x94bb0a841142fe00092e,0xe1d450bf8002cbb16410,0x321685c13020043f2ec3,0x7802f10914bca1404e00,0x18012f285e00321425a1,0xf0a860f803aed81e002f],#[0x12ec2a143f01c01e002,0x403004bbe002f164582e,0xf8320d01504bb0a8321,0x3f0c820f431e00321385,0xc01e003218000f8320c,0xe0d81e023b82c4129850,0x20e000b6123b144a8ec2,0xa85100870cb806120b18,0xe028342c60c02fe010b0,0x200705e00241c4a21c34,0x3117804ee0b203c0130,0x24582d3b0a846f02f097,0xa113b100440d3b02c421,0x2e00311b804ec2f0f80,0x440e020b8ec40f30500f,0x1202e1705e13808ec481,0x3c0b818ec42143a0123b,0xc5cef850fe81c0842180,0x43e0c844ee85a05410f,0x6405013021503e1c07a,0x80610231780a04320c51,0xd6810c860f832093ba07,0x3e10834120580d3b0,0x40902301f01a042e0a87,0xa830f81b10800b83e0a8,0xfc70b8070fc230a8507,0xf0c830140413c4460702,0x70223810a8230b840083,0x14610907e0c20e0032a1,0xa142a1f8310840e0302a,0x1e00321507c0823a0442,0x82a183b100320c3d0f03],#[0x1c400c830ee85a06410c,0xa0f8320c4001c420c840,0x87a16410ef8108c2a182,0xa861100500d819044010,0x8c2a185101401000420,0x4a043b0b840ee0590781,0x81b0d460ec420f82e128,0xc702e00331781a001e06,0xe002209702612811d830,0x31158400f80c0833143c,0x302e00341985c0b83e00,0x1702e03810907011818f,0xe0e85e00094f080f0046,0x5e0302a153c1c4b09420,0x4be0302a113c184be0c2,0xf0401a81a15070a8440c,0xe03020c05a140112f804,0x311b85e0040094400507,0x3020d06614038f302e00,0xf02e0033184060780e1,0x61034e03020cc50d8046,0x81203d01c03e02810bc6,0x4b12c4508b8061c20c16,0xf040220380980c15c9a0,0x1048c1780100712e4509,0xc1403e0282134708187c,0x301f80100300a8510007,0xd05a0b8011c5e028211c,0x11c400e82804470a8408,0xc05a0420981e03052780,0x8212e04e00bb2425e0cb,0xc32e00311447414bc60e],#[0x9e822f013c14bb290560,0xe0f800bc412f83600470,0xbc2ec921c30e002f1025,0xc902305c104b11d01a00,0xd4502304e0705a00bc2e,0x1449415010741b09c612,0x21c2f14494041d06c27,0x810c38021c2f15810c38,0xbc509825c1704e00871b,0xc1780c107004870c3800,0x20d3800cc6e0a87e0c40,0x4014000c0400c204108,0x780120401b05c138012,0xc1048c17801007c17040,0x400cc4e004011c308287,0x8472f380c14bb2434000,0xc38021c2f104b0838320,0x244800704e00bc10060,0xf0f82000f0460780c144,0x83e0c03007802ec2f144,0x170412025e00401f850c,0x80d8044f85a043220206,0x801007e00400c430f006,0x4310a83080030044b097,0xc10401834000400cc481,0x400bc4cf383a1780,0x861280300b80a1431183,0xc831204a00c01e02850c,0x6c306285812036013c0,0x500d82e03040cc507427,0xf80088660c02c13800cc,0xef04e00231d8500b04e0],#[0x8ef04e00231c0500d818,0x260704e0034140560c01,0x24198200780c1034140,0x3040d0661402e0381c1,0x60f04e0033183b00981e,0x57101504c110d440ec02,0x150440f084403c11054,0xc08300bc40741506c271,0x26001a1904040400e83,0x404050120a0304810412,0xfd800401a1423610830,0x140a8360d02232041043,0x52041414041800a84100,0x41808101b1440215020,0x8c81c410183042071014,0x1c10170210c240d83040,0x81d8560f021c19049802,0x2f184360c220c4309012,0x42510041001081c87c08,0x100221040050310f8050,0x2c0f02e00852ec4c0a01,0x14220c16614330c16040,0x1030a002e0402a14016,0x80600100686412800404,0xa01a001a041851d04806,0x1201a01800401a143f0f,0x4a008304050428002c2c,0x3f0fa806001006860898,0x780068509101e001a10,0xa0c0960d8c81040fc3e4,0x60415800402a0c3e4042,0x108101b103e0258540],#[0xa0f8100b8460d0182c36,0x20781a0418014285184,0x4050418411285110110,0x60e010b860f82a60e01,0x810130113c240c3e2ec1,0x80410143e08c2068870f,0x44078009440103e2ed85,0xd85404bb0c408083e08c,0xa0c41082a081002c2c0,0x721d100288315106161,0xc3004030dc2ca0c0a11,0xc142e06028040a1084a,0x84a0c0c101c04683400,0xf504a0c440305230104,0xc40d03e0403032830403,0x141a048100c2d03c8007,0xa824143d071000a824,0x1a80c280d850842af01,0x90100b840f42e0902c1,0x10090509301128101043,0xc241043a0c321f02c06,0x1002403c85210801843a,0x7a01000a81c18430f82,0x94100e800a810a1c40fc,0x3614102ec3614bb083f0,0x1ea02830b0508c84088,0x326128401a1050614214,0x3d21e831212840800684,0x83d06807a0180a0c6610,0x805064012000fa0c3e1,0x38002510041401340600,0x42406006001301c1a1c1],#[0x2a14c30a053e002a10,0x480761584043800687e,0x80103d0680761584e006,0x8070438006860f41a01f,0x1d80040409848083d04,0x830402f0c0b0242f0c1a,0x1084c086115074428511,0x81302a161016451093b8,0x100bc211042c08201245,0x9440082f0b0134001c14,0x400c25842410c2504020,0xec410a04090101380904,0x7015800261585810102,0x406c1501e006001c183d,0xd8004187104221040098,0xcbb040221501120306,0xc30588702c1012852ec4,0x1044410102ec4a16102e,0x3100840cc3a1601e00bb,0x10220c25040212824040,0x41102c12168420b0c232,0x500b42c0798007c6a158,0x1031342f0b01e6001c18,0x8d84c042244056102c1,0x40308c2260c307010701,0x30144408446142a1c848,0x2070cbb614210c3e60c,0x10c60108c40520708146,0x18381c308c1081c31114,0x6c105048140a032f0105,0x8009b0421c404a076145,0x59850cc30801621c1413],#[0x2a0d140a8280c8345030,0x6800d01a002a0c404f0,0x320014104da00190c144,0x2a1431a004006440b41,0x404302c8508540f48005,0x1482c21000b21c310014,0x5040f414083d0c40b0e,0x42160240414103f0a823,0x7040f4230b8008f0121c,0x42f030c641082321e418,0xc6100854068005060a81,0xec61008581201a00071e,0x4101460c0c0c40098140,0x421001409831002a0502,0x30830814a0d010c0c21,0x400c6830304852838303,0x10400d0140c14a0c0c0c,0xc0a81409040c0132001f,0x485a0c4a0c120500a0cb,0x3074bc090580c830cbc0,0xf04414bc050321443090,0x32f020c6830a14c13012,0x83f0a8230504214560a8,0x4141122c621501a00141,0x8280c14028280c261202,0x828314a830c028101402,0x261202a0c310a0385212,0x9102170111440242f08,0x140c42c060560c302830,0x14141dc6101800508514,0x9b0111c660d82c05802,0x200dc610180c04410031],#[0x503813800c4261040810,0x20581408261202100870,0x22850b800c6850c26850,0x208c140b0410020cc11,0x5105260c20581408142f,0x28514400c4285a1421e8,0x1001a144015c61000760,0x20c4d0b0380bc1c14200,0x8360980058141c4d0bd8,0x1d8010400cc310dc601d,0x1002001c160505718400,0x18508832f02614270543,0x68604907e0010064510,0x10881a0c4a0fc0b20f01,0x68061046128304022130,0xa00191e01406800e0140,0xc042916ce1082221282,0x4190f010881a0c3d0888,0xe03010c19203010c80c0,0x80142203d0541380143d,0xc0f0ff80101921484c04,0x914220c8c10f010f8210,0x22a0809103208810c048,0x5011022e010730440fc,0x20243a0a014043216828,0xb010c3dc042f088408a8,0xc048b10320e41c0cc10c,0x102c60fc2202c308810,0xc84101010c421010420b,0x20c84c042c0c4208a8b0,0x8400c12208230c194042,0x304410282088c110310c],#[0x220e014043b0c2310301,0x870f4220c810100b404,0xc04410c3d61684c0483a,0x410f0108d831019a1022,0x8230881c0c320c410100,0x2142210282c044100310,0x84c068214320c610c068,0x23a0b0110184143d840,0x8e84404411085a10101,0x84088311284a0833102c,0x8608e84c0422840502e,0x89830c3f09022c0583a,0x7050201040088200c3f,0x1c508182c04400885059,0xc041408840138008a854,0x20c04481604c04221285,0x4308107e030110330c4,0x20cc310840c04210020c,0xf07c04400c400420c04,0x330c43614330a840cc31,0x88510023c04100885a10,0x30c22608209085c04120,0x40d5822370110226158,0x118208649140f60827a0,0x4f0304d8409e8010574,0x190d84a00194f046128,0x4f030900f08f80130720,0x9a093b0e824ec202682,0x17070042a09010823b10,0x6c04250c260942041f01,0xa811410e00870fc1a142,0x18006a8119800f48706],#[0xe81e00100fc70f407a,0x23088480d0302c410c0f,0x2a2f030b8300a830fc,0x1915850b8bb0c230a82e,0x485c002a1030407000bc,0x6451443d4002a080511,0xc002f064411c3d20700,0x430b413400300a42f183,0x945c00400a83c00bc06,0x5c00bc06430f42d04d00,0x2206441003d2f1000a8,0x604461700064bb1042c0,0x3f6044e001a0824e0023,0x2ec22f02a082a0443e00,0x32a0c0c1009a0d020e04,0xf02a08bc0270209040f4,0xac08bc0d0580c83c0842,0x8bc02430f42f0a824101,0xff020880910320a82c0,0xbb0c09c08bb0f022ec2,0xd80913022ef090e02e0,0x32a142827022ec3c08bb,0x1809c08bc0f02088090c,0xf0c061342f0b01b6001c,0x810bc470c2d0a41b6002,0xd8108c2041841123b11,0x3129801442e102a60e0b,0x8230c090c821282e08c,0x30284c2c870288311848,0xc2a083e0900b0c3d0ea8,0x303008166044dc08402,0x251030b0c2f60447c084],#[0x805604260c16604330c,0x478ec501583098303034,0x1021018409831002f604,0x8c2284107a128119851,0x28ec20101280a8108c4,0xa024083c10164ec2207,0x8006851442e08230a821,0xb830aa3b08030902341c,0x908034043d08c31293b0,0x1024ec40f42a08c302c0,0xc093b0c04408420e85e0,0x3b1245a1702a113b1604,0xc82813024ec3204400f5,0x208c5102042103b11010,0x10215010984100202120,0x60c41023b08430982e0c,0x3c0c40088200c2408985,0xf461030008307142a082,0x9825605841026404250,0x5820c106082136810bc3,0xa04405087a0416102f13,0x220580415041e1685087,0x281144021e810dc660d8,0x1422083040dc61000760,0x4a04200c4001e8105814,0x422082810e05812810c0,0x828111c610020601871,0x87080501c81080309825,0xbc30c1830bc371840601,0xb82439140b0bc3114090,0x6821682604470bc49160,0xe05080450c200504560],#[0x81a084916820820a0a45,0xc431142508282124508d,0x20b05011810944051810,0x9052f030118209430243,0x958121c4e020421c302,0x27054130d05410870c26,0x5007604201427054130c,0xa1c810c400cc310c160,0xd820826c170409581144,0x97800c4008033600411,0x10410bb6082101810826,0xc400581408044148108,0x42078005825184008181,0xc0c410202e0409436160,0x1a14460c4b0840091850,0xc309780a150710260968,0x101561427a0040ac2560,0x40898560c408c2241182,0x58060850902261581102,0x902307]]
set_option maxRecDepth 16000 in
def g127H8 := limbs80 #[#[0x70401f018410000f,0x40114802390542d000,0x12004030103f07407,0x480f028011a42000011,0x701b01005020000ec00,0x409084140101d02c05,0x20080100300c1405857,0x38050001f4280001000,0x17c070002d1480002000,0x340200c0100c140c810,0x4037090150041100002,0x3000c0d0e03100036,0xc270003607c000442c,0x10081700f0001000401,0x2805048000fc1505467,0x80c000001d42000822,0x300a0a04e16c000080f,0x81d18c000600308c11,0x7c051141807c0a0483d,0x30000410c030d029,0x15c05050010f8090a429,0x3423118010087a00c9d,0x164182001004c010100f,0x10720303100c2a17c02,0x6c0401c001a4b303cf7,0x900d18cbb074002dc06,0xf4021a8260047f00002,0x2940740c0003c101d400,0x7b004d40f06800846,0x670e0030202221035,0xb833194b4064b200c04,0xb816144011740601416],#[0x45813c120196b00803,0x540001810018182888e,0x18819058180800602c3f,0x400008180080000400,0x388311102d02a422701a,0x5403004020846a01c77,0x843c0a4450840f02802,0x84609d421840a13411,0x70f1150030c40600c5b,0x90320dc821d00d07c0a,0x10100080905443039bc,0x791840202c0000c0e,0xd4130240a210000241d,0x6e2400cf00780511822,0x4982b0482052ecc00407,0x3780002c593fc2560503,0x438031480b0101719433,0x5b18167220200fe46aa8,0xce203d6aeee2f4c8ffc0,0x30708cb13a39a502fa,0x17f47ce90894abfd09c0,0xb3c03d8d2564e530e1bf,0x135437b11bec2520e264,0x9e981be8de44e140001d,0xea1ca2c0d3789bfc86b0,0xc3d8fbfa4cc5084907d6,0x52d07a52be2c1ccb0480,0x48e60f5453651644d824,0xbf6801603654fe80003e,0xb47e6335195c927cb830,0xcdd09ca86502845c9acc,0x1ab26dfe4c40000b15a0],#[0xd7dc9e130aecce724c0c,0x34c2ac53ca4fc08148,0x9c691a60d022f0290080,0xacf1cd4ff98c5250d0e,0x5af0e4febc3890248a6c,0x6c44b828f60bd360edc,0x426e8c400034a94213e4,0xeffc3fd4875524105f4c,0xc93a7eb903be38b05178,0xa9b8d394cd61258a84bc,0x6e16d00666d8840c657a,0x3ee4ecb0373866205bb8,0x7f486a30d71413dc823e,0xd44c1a68ef800014,0x4d8b77496cc56a83540,0x6bcc75c4919823d40431,0xd6c280d0953cd48470e2,0x125380fa20a8b4cf0c,0xb7312626e978d3f82440,0x2a5500d49f242b9ae5de,0xdc2ccb7910a8def83f70,0xe48cc61219886428be2e,0x14b05ebc274c90782b26,0x50c8d5cf07545efa45ac,0x6bc58030de51c900d80,0x20da2159024a6350e975,0x1cfd122818aa1d12d0b8,0x42d01134b3acb41ab929,0xf02c3df455ec2e68cf48,0x5d1b12746ef47930e5f8,0x6bc4fe144e2cbb844f20,0xb1925f913dee8a3141c],#[0x17d06cd8aae0e68c0efd,0x1b748a9ef8ac2d80bf95,0x393cb350d65924601926,0x1e54c8a2a020781cd6ac,0x82b08aecc03cfc3a6f2e,0xa9d4c484ee24004cc1f0,0x472827f04b7c55549e64,0x4d0fc77047028bed310,0x4aac8b7ae5ac07186caa,0xb2742902d1cca60ce058,0x1f090ecd0f7458fc10bc,0xb9b24f1c33e444206b36,0x63d13803b84b8aeb30c,0xa60097cc88cc6c50ea98,0xcaa2beba10e0e4bc4782,0xbc846866cd811a04f6c8,0xf99c281033169f5cf86a,0x83e01ca123c24cb6bb58,0x18647c6893c6f20c2000,0xea49ce05c348a0436ca,0x6c64dcb808d121c6508d,0xbf44e58319522901bb6,0x30c652f004589a706815,0xe7e4353467130378d9c2,0x1df4e89412a86148cede,0xc34ae8c0b4491391428,0xd930e80d1ec318400019,0xbece1ff831c0000cf0d4,0x314c5448c2ee3d3e47be,0x6f50a25ccd1cf438fe4a,0xbcfe81784958618ed624,0x3c2cb4f099c4e1e4a7a6],#[0x41aa16f116cc880c73cc,0xa43440c898e81180c9dc,0x376c8308a19514eedd58,0xac831aa85c78c69aaab8,0xdfc0001d1f40001245da,0x48a11020d0e0b1c52384,0x47d0e5b42d590c8c5ca8,0xac4863f4b560c5407c2a,0x1dceb7b644e918d1153c,0xac01031e8c2c80670daa,0xf82abc40002515ba77e2,0xea05188a852f0d78be74,0x6e42cdc00000002c8590,0x3d3aa07c88aee71cf21c,0x1272af144ed402c07214,0x5014464e0bbc928c53ad,0xf63015f44694c9b00380,0xc11e4ea10cd419c864cc,0x3982b65cb8400018b0c4,0x3308f5f21ad4bed0fb1c,0x71f91dc916207e88ae1e,0xe340ea5b01bc1500000a,0xf2c000190a4000289d04,0x24cfc00000f31a5994,0x247a308dc0c1400000,0x6b0f0b07f800000f340,0x190a0916a07d10af00,0x67848d3674803f800000,0x4d400034085cf2b02cfc,0x45180ebd84d067642,0x14ed0e7eb07808ba0080,0x2ef38434c0003ca120],#[0x4ec49e8730000084d40,0x5080458000387140003c,0x3f147980000000205240,0x3b28586c0222b1b09386,0xed50fa550f810b40ba08,0x2468c00034ad88,0xc000024011cab400000,0x16c0002412c48bf11072,0x9f36c866ac5072885faf,0x2308ab34eddeb3c46352,0x8ca872c819505637051c,0x3842a057d00e24b7c4,0x3b7c4340a8f01af50b80,0x1b8856e90a851e74e474,0x74fc86fc7e30c0a0add9,0x4a0000302214c43e6c38,0xb12b8000c8111e0483c,0x12c11d3c8da221c61694,0x30a67448c0001c99a1,0xcc8d09f850230dc40,0xebfed56ca1771ee432c0,0x98fce2a283d6a546eb8e,0x147efacc8c301354d17e,0x22c0002cfcbccfacf943,0xe808262759a49103075,0x1ea0738908dac4541c40,0x7e07630e78704f8b615,0x316b09bd175e4344c7dc,0xbd00aba0476c77488704,0xee68f38c8b2abbfc30fe,0x75a03630b53c8f212214,0xa5547072534262e6c960],#[0xd790213ec2961a54ec50,0x5f5d1fbc6dac9622dbb4,0xdd800004408920920172,0xd9a0ba68553c1850c640,0x81c000187bf05a9483b6,0x69de0000000826588942,0x5058ff7cf4400002083c,0x5a9826f4934000286756,0x6696a1e90e2eb7570a7e,0x20779cc6dcb6800034,0x6263ea4f2742c82ed00,0xaf85206080e88e904161,0x4695cbaecb9c0003c,0x1ac000284c886d448000,0x31184000000035,0x99480c1c2df267b49d80,0x11e41ec000201fc00034,0x208fa6ded91458764c,0xeeee78c00022606e4300,0x6f041780d58e820661c0,0x5108c70a6d851d495ac,0x474ce64a2e08dd6c0e58,0xe0981f148eca5978dba2,0xda2c54c4a0b0db2c8e1c,0xb1aa70c0002601b50074,0x21400000001262a8e70c,0x20641d1505ae21042059,0xb07094e4347c4b10a04e,0xe2da8108c3a21edc1984,0xc7847fecac8909748d4c,0x2ff6fca7202a9e64f92c,0xb08d19cd24b495f8acf4],#[0x2708c4c0e3c0000ab2f8,0x44400018a3142fa435b4,0x520c0f01d4863a44f70,0x20260c25da0cc4755a,0x5b49410fd486d024280,0x2dd856400010f5043c5e,0x6eba1f8c498085f8809e,0x462c79c0003ee3aca3dc,0x1780003caa4810240a48,0x15b0bbc21cb9113c2a21,0xd984a2b8a47c7d4022a0,0x2024fdb4847cfb6d1b4c,0x10dce8a3605a440f59,0xac0c45446984324c2a80,0xf64c67ee3c4e34909700,0xe9f4c34800d252800020,0x49150fe50400c3221ce4,0x485010ea7230cc04c214,0x78645e105048018c7716,0xda540d40000c07549b08,0x1e189c0f225fca0648,0xef40000ac55cf4f8d500,0x8b90c58c45f51d74ca32,0x593c5bf0eb58ed8620e8,0x3646402bc0002ac7dc,0x7d030d352670234906c0,0x196f19187b80b3308f52,0x8a2448c240639f49c6e,0x46a833a0448e47090ad6,0x41c62fe0f044c1ba2f82,0x97a82ae8fcec5330c864,0xf16c59f8144c6df03ee4],#[0x10cc3bc8853e9c92307c,0xb2c000206880002a8f19,0x6b98d25004845b5a2228,0xa0d444c0003cfd00002e,0x84b4898e1e987dfcd600,0x5590b7931c48608036bc,0x30ba4fb4eb185f0835d8,0x6188ad5e60e04ce664a0,0x79cf7de62621d62bf3a,0xc06c664e9eb90dce7184,0xb8400020de9ee318ad10,0x8e1c9b42d0548e400032,0x152d018000028d62173e,0x6450b94cd97c62d4c817,0xd8ba166882f2378253d0,0x9fb4285a79f2ca140974,0x1914d100001cd860aa8e,0xaa8a84c17e218df0fd1,0x4c9707ac6b38c,0x14001392a11d0daaa9c0,0xc900cda1044e1e0cf8d4,0x9e00001c9166309e799a,0x78986fc00028a9206912,0x1489818ddf8cbb46a40,0x8fe3148e4d30dae8d1a3,0xd0501e4ce76842285120,0x3449ee12354f100aa24,0x4afeb420727123384078,0x1766175005f631104840,0xbf008874ec340080ee90,0x1f99156cb6e2f1c43f38,0x3000cd0bfc83366abd8],#[0x5a8a7691c6c389d1fec,0x7884dbc46dc2c44a5d8,0xa4d4769c5ffd131caee9,0x3cec1b74caecece4bb3c,0x9ff00f9c879ab350b16c,0x16845950c45081c8a98c,0xce242ec29bc8e0cc6b64,0x2c36c8e474b4f1b0a518,0xc52903a5ab690cb08,0xdc00e2203814154066c0,0xce927a21071c1b149464,0x2403ab0f700279409e4,0x1150faf02b70602115c6,0x95720548cbcc62ae4558,0xd1c41c3498925a106104,0x94bc5d412274f748f9f4,0xed15077d05d68296d2d4,0xd48ee2ec752c5d821f44,0x6c3914a4d408dab02e32,0xa3946bad050ce6f520f4,0xd8e20b6038400026daf0,0x172499082f581a2c9870,0x2f3cbc300c7b18800021,0x90ee8430a8342e8cc74c,0x254c977b0ab8f1dc8340,0x248e80623de0dbe50c58,0x794ca1d877c8e8686fac,0x1d9a4dbae93425bf0f80,0x488219e07368df68522e,0x8ce2ee34969c1db04e92,0x74c71738e9ba85fcb036,0x64000381f64df94746a],#[0x3810f560bda024e50284,0xa6a8a23812323fa80022,0x1d0866e22700bda9c20,0x38604c4834b88902de58,0x1bf832011f04126cef7e,0xd00003e3cc65a761c7a,0xaee0a5800030e01c6068,0x4fbab2a8a7e871800016,0xe9210132bd650d400034,0x58b31c38ae78d740000c,0x28d6efe090b029c89660,0x224716400000002c7014,0x23a83438b4a41e800010,0xe3a4f3dc4bc8de26d23c,0xbc98b9183e7476fcdf1c,0x214c294aeafce568bde8,0xd299091111b63d423d98,0x4be0a01d1da091dc3a10,0x65c89de84dd4f5a07c86,0x397610089a208ce439d4,0x3ea22da83c80001cb730,0x1aa04104b5c501e60044,0x1711057c7d9860e061ce,0xcfee8cad03fc098912b0,0x3dc4fdd003c18311172,0xe9ba6662afec056a4ba4,0xca4d2500f79af82454ba,0x38c0000c5a3c47d86230,0x8011ab8cc88d2d6191c,0xaec4071ccd2045e68,0x1b26b8bc649e38f8ef00,0x821b67df03102],#[0x5754fee40dc802800000,0x741440000014b8eeea74,0x5780001878c00000003c,0x9f40001508367a400000,0x59b6219c43c000142d14,0xf28b66d181c9d66f5cc,0xb21ce8f4bb6a7028fdc1,0x1e323c9d04a8c27ceb84,0x7e6a08e0e12c18f8fbb9,0x9a80003eed480934faa8,0x7110930645186af10674,0x1e14e40ec6a0cc72cf60,0x3a3c302ce7fcd4f07b48,0x219d0158627cc732425e,0x3708a71660028f800015,0xf33cccc05dd087eef152,0x631c4a70a49cff0cc5f2,0xeb78e600002c20a4d0b8,0x9c2ab6c0855422c91c3a,0x47b2484c889fcbe9c,0x451865a8bc7c32ac8600,0xaf4000000010afdc7f00,0x19bce3140a21098a8ed0,0x13107ab092fadeb69dd9,0xa4fc9bb45ce50374f494,0x1630f8a7060cbaa0bd7a,0x4c00000eb95cb5ad2124,0x3e2a4600000c37e45704,0x14b826ae2f551b04eadc,0x205ea5f0d324bccc0b92,0xb03c3ad429a4f6a47edf,0x4312ea829ec0024eb0be],#[0x6bc1070d556bf44db48,0xdd00003c54108120921b,0x16c88192208524d821f4,0x30b28a9ff8]]
set_option maxRecDepth 16000 in
def g127D9 := limbs80 #[#[0xd65d873eb2ac35fdd521,0x221fe4c110ff2408867,0x10fea62887f521443fcb,0x5fd72443fab0a21fd505,0xfb9a217f5cd10bfee488,0x9510bfee8885fd74442f,0x985ff76442febb221df5,0x2ffb92617fdc530ff2c0,0xf5d130fbac6987dd434c,0xec9877d654c2ffba2617,0x582ffb8ac17fdd930bfa,0x17fdcd60dfec6b06fd63,0xfac7b05fd71d83beb2ac,0x41486ffb82437f5cf60d,0xa437f5cd21feac290ff5,0x1bfaec90f7f75487beb2,0xdd634c7fab0a637fdd92,0xbb263df59531bfae898f,0x141f7a86a0ff561506fe,0xdfd76507beb2a83ef59,0x7eb1ac37fdc961bfee0b,0x59561bfee6b0eff63587,0x7b0dfd72d86feb86c3df,0xefeba6c37f5cf61dfac,0xf758d43bfee2a1dff705,0xeeca1dfd7650fbeb2a87,0x458effb8ac77fdc163bf,0xc77f5c363efacab1dff7,0xbfae9b1dfd72d8efeb8e,0xf71597beb8acbdf5c165,0x9221dfdcd65efae6b2f7,0x10ffac4887fd42443fe9],#[0x7fd43443feb9221ffd89,0xeb2221ffd8d10ffac688,0xd910ffae8887ff64443f,0x987fd214c3ff3b221ff5,0x3ffb0a61ff58530ffa82,0xfd8930ffac4987fd424c,0xc8987fd644c3feb9261f,0x4c3febb261ff5d130ffe,0x1ff4c560ffa42b07fe76,0xfae2b07fd61583fea0ac,0x63583fea1ac1ffdc560f,0xec1ffdcd60ffae6b07fd,0x1ffa87b07fd31d83fe90,0xfd63487fea1a43ff5c12,0x3b243ff5d921ffec690f,0x931ffac498ffd424c7ff,0xfff644c7feb2263ffd8,0xfeb1a83ff58941ffa64a,0x58961ffee0b0ffd70587,0x6b0fff72587feb92c3ff,0x87feb9ac3ff58d61ffa8,0xff5d161ffac8b0fff735,0xee0a1ffd7050ffea1ec3,0x650fffb8a87ff5c543ff,0x87ff9d943ffaeca1ffc7,0xffee0b1ffd7058fffbb2,0xd7258fffb8ac7ff5c563,0xa2c7ff5d163ffac8b1ff,0x3e40b401e00330003ffb,0x3824008101d105e812c0,0xc3e70e403540c842ee0a,0x5a0156c50d1368471108],#[0x621c2c6cf19e06211770,0xb235888820e87ec1ee47,0x2b14a9228c89d225c891,0x18cbfa2f40b942d84b01,0x4dbc35dcd293390c963,0xcf483bc4ec73a2ce3d38,0x14943ed0a44134ff63e7,0x534ba929348f11f74681,0xb53d148b50d13e64e853,0x5bf96a759655f9568954,0x2dd869606d7d65e8d74c,0x5a7c684d99865058fc6,0xdcaa7105bcf6e05b2a6b,0xe5177c5dac75c1d3473b,0x6d8011fbf7d7def67a59,0x1878617884f210083120,0x901a3a68d863018a6224,0x8665a795424e7928a454,0x278d9d2270c9afa65e9,0xe961a42a8b3a1ba80e9f,0xb47ab9eabda9bea0fa6b,0xeeb2cac88b0c6bbfae56,0xdba3ee4ab7aad81b53ac,0xc267054bf8af8bbc8aed,0x807198c597129c4230c3,0x50f810ac0c270217246c,0x922a18923b406045d021,0x816003e1c1c1b02c08b8,0x983c2e00382a160883,0x9038070687c2c0b001c2,0x39982e0e6150780808a8,0x380b180983c2e003829],#[0x35dc07001c21778380e0,0xe058080868a010fb0b8,0x83c00705090400f85c22,0x180f85c1e0038281f0a,0x7000b240f85c1e01081,0x800e0c16080b17784c1c,0xc0a031c17104403e0d0b,0x980814047e5925002a64,0x70521010061043e170,0x61c8260062421f0b83c,0xc2e0d05800a0e0103e17,0xc6207c2a0f001c180e31,0x624812058380e010a1c1,0x2408070e617064080e00,0x160a01f078242c120380,0x115123103e0d0b800e0c,0xc4964c72088024e16023,0x28500501826170640c00,0xe010431210f85c1e0038,0x980808c4802812038319,0xde010833200f85c19010,0x580420cc70a60b07011,0x80b05b03124920580e0f,0xb00821f0eca1e0ec6680,0xc808c8a1e6140901c18c,0xf0a200ec2983c2a13003,0xd897060280e150980200,0xe105c301f0081170a851,0x2bb818fc54500f00bbc0,0xe14542d305c4ec06170,0xe8003e045c2a1b00bcc,0x7021f068b006045a2911],#[0x50a4a210050f80c2e120,0x232c0024843e03022e1,0x1910300091c0e42c2e0f,0xf078105e0012401f0b83,0x24021f0b81150e4517ae,0xf70b83c08cb00091e830,0x16461307811de001630,0xb058c459d8bf03834260,0x13023b170984c1e07003,0x4800e1307801d8f8164e,0x8130b838120700322484,0x98581605078019123e1d,0x11010902c00c891f8ec0,0x781c00ec12481f0b832,0xc088f0084258c4211e17,0x7023b15103b216170702,0xcc04086248c9002e810d,0xc863c246604c1e15023,0x3c048e05c240b0234c02,0x600803c248183c28c700,0x102199225c1806058542,0x8bcb1a0070983428f30,0x52281c06028241461804,0x1c8f83c0c15058022905,0x880260f03825e6020a38,0x242b82404119381828a,0x6480121c038382417004,0x80090f04c1e060b80179,0x983c2e01023224aa451,0xc2e0f00821892401e00a,0xc6580428c49200f00304,0x5188f05450f004018260],#[0x10664124763280a02098,0x421d9205c160d023bc04,0xd0811e160983c0e0104,0x3b240b8241e04778082,0x78a34c10050b8319c130,0x2a134104470985422060,0xc0c003c1b0d110706e04,0x702840a8441e41260e82,0xc2e06921d0d8e828052,0x20e87c0614382a1d090,0x8441e020f04084045c49,0x8430abc816020283350e,0x1015d964f20210490421,0xd8c44420430b048120f0,0x3858682487c2a0f001c1,0x20e04810bd0f8342e00,0x34181f0b80200709229,0x40d0785c02ec3842f009,0x485de0204858098c602,0x4050e59004d044220c2,0x76321106108240e0485c,0xe0e1605e0d77800e0b0,0x1761c1a050143e0f0b80,0x7c0614382a198d85c1e0,0x1d0f0341e01161c1e0e8,0x858180884835de003854,0x4150a83c02f038388e0a,0x41483c0a098080a30a63,0xa2f2098080a0cb43a0d0,0x78018942482a1504430,0x140ec603c150b0241051,0x202852c24bcc282b001c],#[0xa084c838105090bbc041,0xc8381209781442e00624,0x31182c87c1a17001c198,0xe01781c180f85c1e0038,0xb8441e0105012d8c83c2,0x40582533998220d41f0,0x1648890a83414160707c,0x2c448441c12063bc0405,0x5822120683c00ed0501,0x617098380e0104508c45,0x78019a08623a120e4408,0x1e0b008542404a03c070,0x23cc00c48038884107c,0xc1e0b0031200983c2e08,0x70580420cc70a4070a84,0x44140507809d9607c1c0,0x1133b259ccc9e614358,0x849d981b82c0d053c80e,0x8f46104f3058342e0202,0x90410f80408b854392c,0x20f0117a1d0380170a8a,0x740e00803cc28a88228c,0x1e0281c2e01762a19088,0xc542c0e0487c0e005c2a,0x140e01182a2303801721,0x1d0a811e0a8a83a1e050,0x805d8a8721c160501c02,0x21f00858492858140502,0xb8084af09810ed068124,0x42c54406d070280a050,0x23b17150743a0e0281c,0x8594bc12410070125211],#[0xbc12c0d068120601083b,0x4ed0810c2c087e812110,0x1063c811407408f8642,0x8321102411a16083bc0e,0x8fc6424ed001ac2c087c,0x5839da17008481180741,0xde00644914762080a048,0x7c321079850260f03021,0x380b02841190861f824,0x2068380a050b02c00eca,0x7858ec7e3e0590858221,0x184101c1a050b02c0212,0x8782e0b0704c0204a25d,0x8106180408bc71005828,0x6bbc0827078017908702,0x3a1f0245c02086039141,0x205022046087c00bcb2,0xc1e0a0b04c012c641a0b,0x70704c02ecc408830287,0xf1c9647630817982c0c1,0x6220150f81820c3002,0x85026010240190e14409,0x4110062302480320c0f,0x2c1585c00f080281c098,0x8381405023cc02147704,0x2070704c02148038984a,0x1e60f0032428c469e]]
set_option maxRecDepth 16000 in
def g127H9 := limbs80 #[#[0x301020f080206100404,0x1010a010442000c1f12,0x3070005000b00050700,0x5020d00010505030212,0x3000206010002050100,0x5000018070a00001003,0x2e05050505001001,0x41a01050b0600000a,0x804071c0c18000a0009,0x60d1c15010616250302,0x107010f23000a051501,0x2014e0504070f000206,0x202020f2b0e02121104,0x5a052205040202000001,0x1115070101000001020f,0x2071102000701000f00,0x4000d18070523010d00,0x23060002050207080207,0x4110000250111071c02,0x5302109070005070603,0x13040402230514370701,0xc33292a04010c0000,0x14050a03010503240919,0x306002103061f080002,0xf12070a1b2e09150000,0x409060714023f00292d,0x50b0203004e1901240d,0x321000c69052605030e,0x2d00048f140200071e0b,0x100104001a0116100828,0x9054800010707030817,0x5180000010930001b],#[0x21812064c0f0c020508,0x9a2a000d02031a032c18,0x4d9d98c5c463c04,0x6602568486f15000000,0x9a7000034e9b2902,0x5864c2940000000,0x2d8000312d8000000000,0x261e00006,0xaeb103b07e0de00028fe,0xe4d0c61662df03cba,0x3040d0ebef2086800000,0x61b110330840000000,0x27b30f8a5df82df61600,0x533d000107c0c0a1a07e,0x145d84658ab900d,0x6c4780810ada022d5306,0x1e1f0078dccac41bbba5,0x265c800069ac0000000,0x5540000edf0000000000,0x4740000000000009,0x5c83f41ff92e00c58132,0x60c00021e70000402168,0x490df2e3d4d317980006,0x1dceab958bfa24a913e,0x43200024f0eb0ed1ce00,0x80000000c0ca584aa57c,0x1575bba90001d98b068,0x13dd400007d3000000,0x482f00006b7a96a00000,0x60d6b29c0000000,0xdd68000438c00,0x21746cc6292c00000000],#[0x3ede3800000000ab5863,0x43b84bc6464dd49b5,0x7a01c82fe028a8f23d10,0xf1992d41c68c00000000,0xace30b30000114d5d,0x2ebc00000000,0x7a728197694ab7c83262,0x7b7e3f80000000462a82,0x31f10f934f3000038999,0x70000513f96c22cf8000,0x474c4715baeacf0000ce,0xbb7700008ecc0000000e,0xb8bac00000000ab7d9df,0x23d8ae40004e66000149,0x4c25070ac2c80000000e,0x2cce80000001a504cbf,0x17507100000000000000,0x1133231b5da982180000,0xa774680000001a403d52,0x9f5885000000004052a9,0x40170001d64400058a27,0xfec4202245163db49c04,0x735999735805b2a33701,0xca4ddcbda940007021e,0x9d380000000,0x2180001b98d85b734600,0x80002702000000005166,0x45439ada60000a747d7d,0x33996b000030680000ea,0x7cd1552970640000af0a,0x975be4b520001f34352b,0x3e7c9df4817262e1152b],#[0x4f17c15a3490d6ea2358,0xcf9951d43f461121c975,0x3ce261bcb5425ace3d02,0x5094146f62240001656a,0x7a5cfa80001aaa0000,0xd4267d9539fa508ebe00,0x53910001fab98853a5e1,0x1acf1990000a074000,0x6e800005760000000000,0x8000f3a5c5bc0003aa12,0x3ad75e8a0481e0bd13,0x71204640000000dc7200,0xf3320001a38c0000a6ca,0xbf5d3b35f02b363cf848,0xf77e9989bb00000000ec,0x3f64c229051800000008,0x5a5d6223ebfc000,0xf88400,0x3122000000020da00000,0x63e5a70c0001224,0x0,0x29bb92a5f81c0006e330,0x345bcd4dc00000000000,0x580b2800000000001e8,0xea80c6b5c44000053cd1,0x2879000124d822c,0x7165c64af4d762822600,0x2bab000132e9300c8815,0x21885006ee57460c000,0x57114e4c8f4b5b000,0x170200001f68000204d0,0x5c6090eabbd445f42ab],#[0xbb6c0005a8ec1254d,0x828dce74c3a1591cafa0,0x2c00011ea0000e296c8d,0xbeaf948c1b5e250eda2f,0x550b60a87c86b591299,0x7d25e9bbb61ed0606f46,0x20d055742e7a84f61802,0x822483b75a206322,0x6d23fb1a501f0c70a4b1,0x872d18c00016b,0x717fc36f8ca00004ba10,0x7ce36a905c5aeca80000,0x539aac5ce6000000011e,0x800020b4d4d4c8b8000a,0xbe0d5eac992ac00018d3,0x188cda7c92895a2f3271,0xbf93e459091000013086,0xd1353a997b0f147e550d,0x12dc8abe3e8b0001d7,0x687d13d3da1c58cab4c0,0x8d03028239096fad4538,0x109951a0c2be7d,0x69fd0,0x6846033010e8000,0x7440000000000084b000,0x33cf0000e0e99c50000e,0xc54bdc3507da7404c000,0x1185283a000011aa89,0x431e086e0002de27b560,0x1c0000000000139f8597,0x7c5ab8b8443b4a327cae,0x7f825486b7300000],#[0x900e821282b740001cc1,0x1c00a5cc8d3886278162,0x24702a83e1c3daf56b78,0x62190571c000240e,0x11dc90c000792f959c00,0x80006411c878c010ef8c,0x10daddf2a4eb057,0x7100003f9cfec9355e45,0x3828d46983280005a7ec,0xafd07ccf22662000119d,0x6cf2de269100000491c7,0x963b00000003af3d247c,0x78000331300000dc3954,0x3cde1c4bb7a39f000181,0xc067a52d0d1485f7f40b,0x8bf5c301580,0x4eac75fdcb00003c4600,0xaa8775900001e551a7b9,0x8cd31bb48a06aebb93b2,0xefe215fd8dc279a6b7af,0x2f67e4b21ab40001b6f4,0x121a2d44ae8d25343c0,0x1c55e9bdd2d3356e00,0xc18aa38a9ba800000b80,0xbeaaa0000000000030cf,0xeb73818000046,0x3324487d6541a4a0,0x42abd9a75da70dc,0x5976d0281fc14851a400,0x800080dcec88af300003,0x15c65aa65afc400031b5,0xaed285aa261adf4e3],#[0xe9bc000529a0,0xe6db769fb47788c9c1e5,0x50c00035104d4e668c68,0x66d994cde0d1,0x228f89715f38cf00b4,0xd9000022fe00006cf400,0xd335a3558572fb0f61e9,0xddca380004b680000b65,0x3dd24ab54f37c4,0x85100e0c0004f7b0,0xcc4ef0000000000014aa,0x909a63800000000000dc,0x504cdfa58b3000018b4b,0x2d074053621180df561,0xe058000093b000000,0x294b000045a75818fab0,0xb599580000000e3d41c2,0x3e9e01387ef801f30b54,0xd34b02888a91,0x26628000469d68f8000,0x90c0000314000,0xfb4f0dfc000193b00000,0xac00031b30000000079a,0x7b663d59bd,0x1c3599b10,0xda172000006240000000,0x117857791e65f237834b,0x331f838048180000000d,0xcb040615e00002a98000,0x2a48ec6e86783b86781,0x2209423bad96528cabb0,0xaa88486cda5697c27914],#[0x1e4c3fc70000434942,0x40a8000063fe53fd0e40,0x9250d6d090000c4b7923,0x3b06116b444dad00008c,0x93b5821c00030f61bb89,0xa5510a1159061859e730,0x7af49e21ca7175762ff5,0x80000000a8a400000002,0x833cea9bc000086b1436,0x57e000000000000001dd,0xd4c600016088d5d0000a,0xd5700000001d99,0x5276f540000000247a00,0x2c106b8fd77b2c60,0x6f4337ae8b5d200029df,0xf9adf449ae621c2d687,0xc8c996a200000ff5f34d,0xa4b7bca7a3083d18db2b,0x2f86deafb60000332bdb,0x72da0edc0003b7ab85d7,0x13d400000000000,0xdb423c1f9db050411e00,0xece0000000389390583,0x5ebd28000000055b5990,0x14f6051c3d2c00008d,0x45680,0x38078000e14e0000000,0x3ac00000000000b0a400,0xf9e3d39b4c00bbf4161e,0xdf27b295f780003d5e,0x0,0x3b6391f6000029980000],#[0xde0c48000d4980000000,0xb8b2e340007a236a5d8e,0x9f9a00019b040000000e,0x9800046c66484917802f,0x28a000000000003256b8,0xcac0e288f51800028554,0xa800013ac000147df96c,0x762a3bc00011b5000080,0x5cc9c49234bf56b315b3,0xcd97c0000a7b36e6072a,0x185600000893558bad,0x9b90001c9acab800df0,0x1a1c92afc1172689b99a,0x344e982d8e00000000d6,0x399633bffa8c00029423,0x47917f0770f1a4b848ca,0x69bf70d358d0031cd4e5,0x9e2fa831e64fc4edfa03,0x3d3298b2c47cc00f54e5,0x3f52f840b2d29e948147,0x7ab3d10e628648270dd1,0xa63e11ac7f0c64754897,0x3d10894fd0d06a778a23,0x4160c516493fcc8d7668,0x44989ccba61aaaf9f09,0x394ab7049069bd75a4a9,0x33b2000000034b200006,0x181052f7f03e5a055ed,0x1a9d000052cd000000,0x800041efa668db6200e0,0x5ec2900e6bc8855,0xa4a09510c5a9ad154400],#[0x4a314247697e5db51f86,0x5279e21e49f380002dc0,0x9dc46c09b88c8d604f8d,0xa150164cfb169e81b3bf,0xb8f0e00002b67d81b59c,0x6a7453114eb795c5a1c5,0x73d20001a68601c5ab63,0x4d6c0000f8c4000,0x29a10000400000,0x322e5d8e000000000000,0x50e3f3903718b285759,0x16163e7381dac1ac91e4,0xf0acb74b0f5a823e4328,0x5a064164630563e130d4,0xe31520a9aebba3a9019c,0x870856612a3e07089f58,0x155dea17ad01b8c29940,0x9032c0917ee8399687e9,0x2a5210b32c68b8ffa721,0x9949c626893c14268c5b,0x101b0cc23a11d54be0,0xd267d05c184f7eb442c0,0xf80003082273c000340d,0xfd6db5c416391b797,0x4bc3000028cd9d3562e0,0xfb8c3e36a3ea8000343b,0x5ce023428adb3f6a0380,0xe07ac0c40000996bab80,0x48d53ef8a3dc0e0ec241,0xc8b8e66ce7522d4760aa,0xc831d457049331161c86,0xa35ee488ccefbce3c5c9],#[0x940a179aa9ee8810a0d,0xab36020e00000003a98a,0x540004819cebd637a066,0x1a9f1040006af40001cb,0x53e03f54000261ff98fa,0x3c00048c74c8e00004ed,0x401e1380000b8200016c,0xd06993b2d95487e54c86,0x5c00062fed588a9f4291,0xdcffde9dae2461a14683,0x7c1600014c6146c3a0a7,0x2ceeb0bd9755e5e5d1b,0xab722fe9688000000000,0x2e97853e2525c5bdd587,0x85087173a0c361211e1,0x187e3c439b53379a579a,0x1bc9a407c2b87b41a1c3,0x204400000000000,0x144b0f49e9de00,0xe358149c0002ef80bdd0,0x44000643d7f0cc153cf6,0x1b9000000000000ec,0x6684000000000001ae00,0x480007405e5860000000,0x42d439b87600000001e8,0x41be31e52a0f1827aac1,0x4f98e99b286c1e459545,0x2583c7157ab065b2eee5,0x5005c536643fc0943975,0xfe0d36a0caf5343e93cc,0x137f8a1deff0ce30220d,0x3dfe613e83d80562],#[0x2c00001c3ffb60000000,0x1809744e321d53de80,0x867f000166a000000000,0x540006c15d2db0bc75a3,0x38200000005ea2000175,0x8a22b47e34296619939c,0xd390298cfb216a937e52,0x6fcfe1f1e3000057a720,0xa5f144d400000001b21d,0x14cf280000beda50dee4,0x6db8788000234b34b9fe,0x18bbd2e4c94c0001295a,0x90b34cfc0a1b800011ef,0x17b2b564ed,0x8000141600030a7d3b90,0x7a89000183891a4,0x242def40003188dea400,0x52e6e560000194176b6d,0xe98df891f00008330000,0x8cc82f24f700000000b8,0xfe1da092000350980007,0xea9368000d409aa8f9cd,0x1bae8000e24d06,0x80000578426000000000,0x7000075a508360002475,0x279067821c3ba8f629c7,0xd9ae2979c3667861bae1,0x2d463aed19f24752069]]
def g127D10 := limbs80 #[#[0x60ff583fd30ff4437d65,0xfd61ff507fd31ff487ff,0x3ff63ff58ffd43ffd87,0xa1f26d156420ca2103e0,0x120e0a047ca2eaab2668,0x83850201801c20012616,0xc0a160c1006007080704,0xec9078584838280011c1,0x2a2d18f2160a120c0600,0x4e4c2e07848185030280,0xb181c0a160e0600247,0xe04ec0a0073b8483818,0x8483858102803c221612,0x41c1e060e08141200746,0x1200ec8838582813c800,0x11a160a0e04]]
set_option maxRecDepth 16000 in
def g127H10 := limbs80 #[#[0x8002040043400800201,0x140000080002c00001,0x1944,0x0,0x207400,0x221c00000000,0x383e00000000000,0x14580000,0x0,0x4000000b4800026ee000,0xd0000000000000000488,0x6250000000e5,0x0,0xcf400000000030480,0x29455360000000,0x89a,0x1f8f000,0x600400000080d800000,0xb0800000,0x18c584b24e00000,0x80e00000000000000000,0x36ce0000000000,0x728,0x1097c15800,0x187c0000003a3e00,0x446800000000052800,0x9400000000000000000,0xa2b7,0x34e80000000000000,0x8170000000000000,0x211b462000000000000,0x3a3587600],#[0xf56a02e1840,0x54880000000000,0x5408000,0x6460000000000,0xa0b800,0x0,0x39000000000000000000,0x1c840001a20000001e,0x9ca80000000000000,0x3e480000000000000,0x277000,0x328f8000000000000000,0x1a3a000d8,0x3e6cf3c00012940,0x57e000483990c0000,0x0,0x0,0x0,0x78000000000000000000,0x3cd000000000022,0x20d60001b500000000,0xb060,0x0,0x0,0x648800,0xf7200,0x3192840c3300000000,0x0,0xf20280000000000000,0x0,0x518000,0x12f4000387000000000],#[0x52000254000000000,0xc6e00000000000,0x15930000,0x39800000000000000000,0x1f7470d0000000000000,0xa80000000006ac000000,0xc4,0x13000000000000000,0x0,0x3c428200000000000000,0x74b800000000014e0000,0x5c0,0x0,0x164600000000,0x890000000000102a0,0xa120005a89f0c85a0000,0x0,0x836,0xc0000000000000000000,0x24d400000033,0x0,0x15550,0x2498000,0x4414000000,0x2208000000000000000,0x38a000000,0x4000000000000000000,0x14a90,0x1a5e0000,0x0,0x0,0x6e662acca799cc800000],#[0x12e274bd1,0x0,0x0,0x5810000,0x1e6d0000000000000,0x60e000,0x18000000000000170600,0x20,0x0,0x0,0x0,0x0,0x776c08000000,0x98d0600000,0x20fe00000000000,0x114300000000000000,0xc77c9fb97b4c0,0xf,0xdb490000000000000000,0x9f8f6000000000206be7,0x29,0x328c0000,0x0,0x40e0000,0x0,0x2380000000004c9c00,0x0,0x688800000000000000,0xd4e8000000d700,0x0,0x0,0xf8150000000000838800],#[0x1002000000000117,0x5e0000000001e5b00000,0x17,0x32200000000000000,0x9b40000000,0x1385000,0xd0000000000d42344400,0x2a,0x5a240,0xe3c00000000000000000,0x1,0x1b20,0x70000003cd1411000000,0x10120000000a6800184,0x0,0x245000006e0,0x38a40000000000,0x108b0000000000,0xa348000000000000,0x0,0x64000000000000000000,0x1ed8fc000000d27293c0,0x171300000000000008,0x21300000000000,0x0,0x1357000000,0xf47812400000,0x145700000,0x31b0001cde0,0x0,0x80000000000000000000,0x3498001694fb9],#[0x7a1400,0x0,0x32200,0x6bc00000015100,0x228000,0xce747e,0x1351864000000000000,0xbc000000000000000000,0xc4cb8,0x14c0004650000d4d4be0,0x2e2c0009a97,0x0,0x50000000000,0x0,0x0,0x0,0x90429603ae0340000000,0x19620000000,0x1e27,0xc1d2163e36000000000,0x302c00000,0x80faa0000001c1600000,0x10cc00000000000006,0xb2e3c0000,0x16430006d74000,0x6000000580e068000000,0x1c5200000018c,0x42000000000000000000,0x204f1,0x0,0x0,0x9200000000000],#[0x0,0xe55eb5800003000,0xfa880,0x344600073900000000,0x17330000]]
def g127D11 (j : Nat) := if j=0 then 0x5080c1010037f else 0
def g127H11 := limbs80 #[#[0xd538793e46e00b62346,0x8018da71400149450000,0x4180000ab003c68400d4,0xce2597601]]
def g127L : Nat → Packing
  | 5 => (5,6,7,0,0,6,0,g127D5)
  | 6 => (218,5,7,0,0,12,0,g127D6)
  | 7 => (1178,4,7,0,0,15,0,g127D7)
  | 8 => (999,3,7,0,0,16,0,g127D8)
  | 9 => (166,2,7,0,0,14,0,g127D9)
  | 10 => (13,1,7,0,0,10,0,g127D10)
  | 11 => (1,0,7,0,0,0,0,g127D11)
  | _ => emptyPacking
def g127I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 2 23 0 8 3 1 g127H6
  | 7 => lookupWord 77 787 5 13 8 1 g127H7
  | 8 => lookupWord 391 1693 10 16 11 1 g127H8
  | 9 => lookupWord 338 1847 8 15 10 1 g127H9
  | 10 => lookupWord 58 1201 3 13 8 1 g127H10
  | 11 => lookupWord 5 29 3 9 4 1 g127H11
  | _ => fun _ => none
def g127 : Forest := ⟨127,11,fun i => g127Y[i]?.getD (0,0),g127C,g127A,g127L,g127I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P5_0 : block g127 5 0 5=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g127B5 : block g127 5 0 5=true := g127P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P6_0 : block g127 6 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P6_2 : block g127 6 2 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P6_98 : block g127 6 98 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P6_194 : block g127 6 194 24=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g127B6 : block g127 6 0 218=true := (@block_merge g127 6 0 98 120 (@block_merge g127 6 0 2 96 g127P6_0 g127P6_2) (@block_merge g127 6 98 96 24 g127P6_98 g127P6_194))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7_0 : block g127 7 0 88=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7_88 : block g127 7 88 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7_184 : block g127 7 184 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7_280 : block g127 7 280 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7_376 : block g127 7 376 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7_472 : block g127 7 472 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7_568 : block g127 7 568 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7_664 : block g127 7 664 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7_760 : block g127 7 760 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7_856 : block g127 7 856 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7_952 : block g127 7 952 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7_1048 : block g127 7 1048 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7_1144 : block g127 7 1144 34=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g127B7 : block g127 7 0 1178=true := (@block_merge g127 7 0 568 610 (@block_merge g127 7 0 280 288 (@block_merge g127 7 0 88 192 g127P7_0 (@block_merge g127 7 88 96 96 g127P7_88 g127P7_184)) (@block_merge g127 7 280 96 192 g127P7_280 (@block_merge g127 7 376 96 96 g127P7_376 g127P7_472))) (@block_merge g127 7 568 288 322 (@block_merge g127 7 568 96 192 g127P7_568 (@block_merge g127 7 664 96 96 g127P7_664 g127P7_760)) (@block_merge g127 7 856 192 130 (@block_merge g127 7 856 96 96 g127P7_856 g127P7_952) (@block_merge g127 7 1048 96 34 g127P7_1048 g127P7_1144))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8_0 : block g127 8 0 21=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8_21 : block g127 8 21 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8_117 : block g127 8 117 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8_213 : block g127 8 213 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8_309 : block g127 8 309 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8_405 : block g127 8 405 80=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8_485 : block g127 8 485 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8_581 : block g127 8 581 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8_677 : block g127 8 677 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8_773 : block g127 8 773 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8_869 : block g127 8 869 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8_965 : block g127 8 965 34=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g127B8 : block g127 8 0 999=true := (@block_merge g127 8 0 485 514 (@block_merge g127 8 0 213 272 (@block_merge g127 8 0 21 192 g127P8_0 (@block_merge g127 8 21 96 96 g127P8_21 g127P8_117)) (@block_merge g127 8 213 96 176 g127P8_213 (@block_merge g127 8 309 96 80 g127P8_309 g127P8_405))) (@block_merge g127 8 485 288 226 (@block_merge g127 8 485 96 192 g127P8_485 (@block_merge g127 8 581 96 96 g127P8_581 g127P8_677)) (@block_merge g127 8 773 96 130 g127P8_773 (@block_merge g127 8 869 96 34 g127P8_869 g127P8_965))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P9_0 : block g127 9 0 3=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P9_3 : block g127 9 3 82=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P9_85 : block g127 9 85 81=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g127B9 : block g127 9 0 166=true := (@block_merge g127 9 0 3 163 g127P9_0 (@block_merge g127 9 3 82 81 g127P9_3 g127P9_85))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P10_0 : block g127 10 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P10_1 : block g127 10 1 12=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g127B10 : block g127 10 0 13=true := (@block_merge g127 10 0 1 12 g127P10_0 g127P10_1)
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
  · exact g127B5
  · exact g127B6
  · exact g127B7
  · exact g127B8
  · exact g127B9
  · exact g127B10
  · exact g127B11
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127G : graphValid g127 (boundsBefore K246) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low127 : Lower true (varsX 127) (graphGoal 127) 12 := lower_forest (g:=g127) (i:=0) (hints:=1049651) (before_sound K246 V246) g127G g127T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K127 := extendKnown K246 12 [(127,[]),(191,[48,65,82,118])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V127 : Known true K127 := extend_ok (m:=127) V246 low127 (by decide +kernel)
def g223Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x3fc173192150b20f50,0xfc000003f03f03f])),(BitVec.ofNat 152 (word80 [0x850172112040120e50,0x41041041041041041041]))),((BitVec.ofNat 152 (word80 [0xc0065d6176a84a1610,0x3f000000fc0000fc0])),(BitVec.ofNat 152 (word80 [0x986592174a00a1611,0x45145145145145145145]))),((BitVec.ofNat 152 (word80 [0x315879048f057d60,0x3f000fc0000])),(BitVec.ofNat 152 (word80 [0xe215859048d057d68,0xe38e38e38e38e38e38e3]))),((BitVec.ofNat 152 (word80 [0xffda8449ba143138a0,0xfc0000fc0000000fff])),(BitVec.ofNat 152 (word80 [0x1084488a102120a2,0x8a28a28a28a28a28a28a]))),((BitVec.ofNat 152 (word80 [0x3115a69573090090,0x3f00003f000000fff000])),(BitVec.ofNat 152 (word80 [0x101005a29132080083,0xc30c30c30c30c30c30c]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x4e802002006c0ef,0xc000003fffffff000000])),(BitVec.ofNat 152 (word80 [4,0x10410410410410410410]))),((BitVec.ofNat 152 (word80 [0x280294c88cc8e70f,0xffffffc0000000000000])),(BitVec.ofNat 152 (word80 [0x20280004000cc0c108,0x20820820820820820820]))),(0x0,0x0)]
def g223C : List ColumnInfo := [(1,0,222,0,10),(2,0,221,0,10),(4,0,219,0,10),(128,0,95,0,10),(8,0,215,0,9),(16,0,207,0,9),(64,0,159,0,9),(12,0,211,0,8),(0,4,139,80,7),(24,0,199,0,6),(72,0,151,0,6),(80,0,139,0,5),(80,4,139,0,5)]
def g223A : List (List Nat) := [[]]
def g223D8 := limbs80 #[#[0xfaf82551439ef825d543,0xdef825d543bef825d543,0xded73dc954bef825d153,0xfef825d543ded83dc954,0x54f1806000fef825d153,0x2e4e3cf80daac452a26d,0x7938104a4f1e7c058d5b,0x65c4673e0398cacb8d6e,0x730cb355e3939f022549,0xe9701042a525f88be7c0,0x1824a92486099b2b4e3c,0x12a492]]
def g223D9 := limbs80 #[#[0xd5450feea9a877bdc954,0xa2a77fdd543bfaeaa1fb,0x43bfee6aa7ef72552ffb,0x7fd73553feba2a7ff5d5,0xba5424cfc69288d83000,0x25248d26c65cf01fc1aa,0x4c73c0c20a2445b2c73c,0x24624acb1cf0307589ca,0xc6571cb3c0a196cb1cf0,0x9214c73c0c1740b1cf02,0xcb1cf028830a5b1cb3c0,0x50ac89c73c0c215309]]
def g223H9 := limbs80 #[#[0x610038000007000000,0x9200006300f50000,0xf000000000000000c4,0xf6]]
def g223D10 := limbs80 #[#[0x45c5c03fd54ff54ffd43,0xd524a338109b14928ce0,0x6a16519c18428]]
def g223H10 := limbs80 #[#[0xd6004974000057b2,0x9351,0x4a450000581000]]
def g223D11 (j : Nat) := if j=0 then 0xca842603ff else 0
def g223H11 (j : Nat) := if j=0 then 0x2d70 else 0
def g223L : Nat → Packing
  | 8 => (9,3,4,0,0,9,0,g223D8)
  | 9 => (11,2,4,0,0,9,0,g223D9)
  | 10 => (3,1,4,0,0,7,0,g223D10)
  | 11 => (1,0,4,0,0,0,0,g223D11)
  | _ => emptyPacking
def g223I : Nat → Nat → Option (Nat × Nat)
  | 9 => lookupWord 2 37 0 8 4 0 g223H9
  | 10 => lookupWord 2 29 0 8 4 0 g223H10
  | 11 => lookupWord 1 3 0 6 2 0 g223H11
  | _ => fun _ => none
def g223 : Forest := ⟨223,11,fun i => g223Y[i]?.getD (0,0),g223C,g223A,g223L,g223I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P8_0 : block g223 8 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P8_1 : block g223 8 1 6=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P8_7 : block g223 8 7 2=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g223B8 : block g223 8 0 9=true := (@block_merge g223 8 0 1 8 g223P8_0 (@block_merge g223 8 1 6 2 g223P8_1 g223P8_7))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P9_0 : block g223 9 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P9_1 : block g223 9 1 7=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P9_8 : block g223 9 8 3=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g223B9 : block g223 9 0 11=true := (@block_merge g223 9 0 1 10 g223P9_0 (@block_merge g223 9 1 7 3 g223P9_1 g223P9_8))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P10_0 : block g223 10 0 3=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g223B10 : block g223 10 0 3=true := g223P10_0
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
  · exact g223B8
  · exact g223B9
  · exact g223B10
  · exact g223B11
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223G : graphValid g223 (boundsBefore K127) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low223 : Lower true (varsX 223) (graphGoal 223) 12 := lower_forest (g:=g223) (i:=0) (hints:=1075) (before_sound K127 V127) g223G g223T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K223 := extendKnown K127 12 [(223,[]),(251,[48,65,82,118])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V223 : Known true K223 := extend_ok (m:=223) V127 low223 (by decide +kernel)
def g239Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xffcaa21f992a55c000,0x4000003f00003f00003f])),(BitVec.ofNat 152 (word80 [0x29ca2207902a458000,0x45145145145145145145]))),((BitVec.ofNat 152 (word80 [0xa02ac2b05023ba13,0x40000fc0000fc003ffc0])),(BitVec.ofNat 152 (word80 [0x4ca02042b04003a202,0x41041041041041041041]))),((BitVec.ofNat 152 (word80 [0x1fcf4d6808388026b,0x3f000fc0000])),(BitVec.ofNat 152 (word80 [0x71f8f4d68080880223,0x238e38e38e38e38e38e3]))),((BitVec.ofNat 152 (word80 [0xfe400d90dea41e102e,0x8003f000fc0000000fff])),(BitVec.ofNat 152 (word80 [0xd900e8010102c,0xa28a28a28a28a28a28a]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x112b6d083f8128ec,0xfc0000000000fff000])),(BitVec.ofNat 152 (word80 [0x80010b29083f00084c,0x1c71c71c71c71c71c71c]))),((BitVec.ofNat 152 (word80 [0x2e542b025400c554,0xbf000000ffffff000000])),(BitVec.ofNat 152 (word80 [0x400280014004150,0x90410410410410410410]))),((BitVec.ofNat 152 (word80 [0x191c1206588680781,0x7fffffff000000000000])),(BitVec.ofNat 152 (word80 [0x10c0004100280481,0x20820820820820820820]))),(0x0,0x0)]
def g239C : List ColumnInfo := [(4,0,235,0,10)]
def g239A : List (List Nat) := [[]]
def g239D10 (j : Nat) := if j=0 then 0xff else 0
def g239L : Nat → Packing
  | 10 => (1,0,1,0,0,0,0,g239D10)
  | _ => emptyPacking
def g239I (_ _ : Nat) : Option (Nat × Nat) := none
def g239 : Forest := ⟨239,10,fun i => g239Y[i]?.getD (0,0),g239C,g239A,g239L,g239I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g239P10_0 : block g239 10 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g239B10 : block g239 10 0 1=true := g239P10_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g239T : checkedTables g239 10 := by
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
  · exact g239B10
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g239G : graphValid g239 (boundsBefore K223) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low239 : Lower true (varsX 239) (graphGoal 239) 11 := lower_forest (g:=g239) (i:=0) (hints:=1049907) (before_sound K223 V223) g239G g239T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K239 := extendKnown K223 11 [(239,[]),(253,[48,65,82,118])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V239 : Known true K239 := extend_ok (m:=239) V223 low239 (by decide +kernel)
def g247Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xff8aa21f892a57d000,0x4000003f00003f00003f])),(BitVec.ofNat 152 (word80 [0x298a2217802a478000,0x45145145145145145145]))),((BitVec.ofNat 152 (word80 [0xa02ec2a0d023ba33,0x40000fc0000fc003f000])),(BitVec.ofNat 152 (word80 [0x4ca02cc2a0c003b202,0x430c30c30c30c30c30c3]))),((BitVec.ofNat 152 (word80 [0x1fcf0d6900388024b,0x3f000fc0fc0])),(BitVec.ofNat 152 (word80 [0x71b8f0569000880203,0x21861861861861861861]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfe400d90dea41e102e,0x8003f000fc0000000fff])),(BitVec.ofNat 152 (word80 [0x400d800e8010102c,0xa28a28a28a28a28a28a]))),((BitVec.ofNat 152 (word80 [0x112b6d083f8128ec,0xfc0000000000fff000])),(BitVec.ofNat 152 (word80 [0x80010329083f00086c,0x1c71c71c71c71c71c71c]))),((BitVec.ofNat 152 (word80 [0x2e542b025400c554,0xbf000000ffffff000000])),(BitVec.ofNat 152 (word80 [0x400280014004150,0x90410410410410410410]))),((BitVec.ofNat 152 (word80 [0x191c1206588680781,0x7fffffff000000000000])),(BitVec.ofNat 152 (word80 [0x10c0004100280481,0x20820820820820820820]))),(0x0,0x0)]
def g247C : List ColumnInfo := [(4,0,243,0,10)]
def g247A : List (List Nat) := [[]]
def g247D10 (j : Nat) := if j=0 then 0xff else 0
def g247L : Nat → Packing
  | 10 => (1,0,1,0,0,0,0,g247D10)
  | _ => emptyPacking
def g247I (_ _ : Nat) : Option (Nat × Nat) := none
def g247 : Forest := ⟨247,10,fun i => g247Y[i]?.getD (0,0),g247C,g247A,g247L,g247I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P10_0 : block g247 10 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g247B10 : block g247 10 0 1=true := g247P10_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247T : checkedTables g247 10 := by
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
  · exact g247B10
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247G : graphValid g247 (boundsBefore K239) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low247 : Lower true (varsX 247) (graphGoal 247) 11 := lower_forest (g:=g247) (i:=0) (hints:=1049684) (before_sound K239 V239) g247G g247T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K247 := extendKnown K239 11 [(247,[]),(254,[48,65,82,118])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V247 : Known true K247 := extend_ok (m:=247) V239 low247 (by decide +kernel)
def g255Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x1fc00001fc07,0xf21260612331974c84de])),(BitVec.ofNat 152 (word80 [0x244891224489122448,0x9210202023309208808e]))),((BitVec.ofNat 152 (word80 [0xfe0007f0003f8,0x438882c43a66b189c6])),(BitVec.ofNat 152 (word80 [0x142850a142850a1428,0x50408802401264208086]))),((BitVec.ofNat 152 (word80 [0x7f0003f80fe0000,0x10419c478c29217])),(BitVec.ofNat 152 (word80 [0xe1c3870e1c3870e1c,0x3000a104104438c28017]))),((BitVec.ofNat 152 (word80 [0x3f8000000000003ff,0xf01c11f81e0780fd4373])),(BitVec.ofNat 152 (word80 [0x489122448912244891,0x200001081c0500c14371]))),((BitVec.ofNat 152 (word80 [0xfc0000000000fffc00,0x601e00e007ff0267a0])),(BitVec.ofNat 152 (word80 [0x50a142850a142850a1,0x40600800c00344006720]))),((BitVec.ofNat 152 (word80 [0x3fff000000,0x3800000fff800007c28])),(BitVec.ofNat 152 (word80 [0xe1c3870e1c3870e1c3,0x82800008a7a800007c28]))),((BitVec.ofNat 152 (word80 [0xffffffffc000000000,0xc001fff00000000780c])),(BitVec.ofNat 152 (word80 [0x810204081020408102,0x40014d1000000001800]))),(0xfffe000000000038031,(BitVec.ofNat 152 (word80 [0x20408102040810204,0x9094000000000020000]))),(0x0,0x0)]
def g255C : List ColumnInfo := [(4,0,251,0,12),(32,0,223,0,12),(64,0,191,0,12),(128,0,127,0,12),(1,0,254,0,11),(2,0,253,0,11),(8,0,247,0,11),(16,0,239,0,11),(9,0,246,0,9),(10,0,245,0,9),(17,0,238,0,9),(18,0,237,0,9),(3,0,252,0,8),(24,0,231,0,8),(11,0,244,0,6),(19,0,236,0,6),(25,0,230,0,6),(26,0,229,0,6)]
def g255A : List (List Nat) := [[],[48,65,82,118]]
def g255D9 := limbs80 #[#[0x434c110fe450d414c110,0xaf768e9850d10ff4685,0x69850d10aef6929850d1,0x44135382adcae008ff6a,0xa0602c5b0cf0f83c7e2,0xa32ce0d04f87c1e3f142,0xdc5e2787c1e3f10b4805,0x3f1789e1f078fc42d214,0x23a7d3787c010f1f8885]]
def g255D10 := limbs80 #[#[0xfb28698221ff1414c110,0xdaa1a82885fd65131443,0xfb30a1a217fb9050d10f,0xeca706884ffe51834427,0xb27c22213ff93611109f,0xc2262887fe611304427f,0x22a1a21ff58350510ffa,0xc286886ff66143443feb,0x8c1a21bfd8460d10dff4,0x286886ff64d844437fb2,0xb1301c425023000ffecc,0x584a11272203d46f0b,0x9a52121f4087a4e319f3,0xb242c319f83878f8a208,0x4492d0d8c08e0e1e3e24,0x4826302c278313878f88,0x8b480c2d8c0be1e0e3e2,0xee3e22131131787838f8,0x878f8838511100fe1e00,0x83c5a6e1e0e3e20c1b83,0x7e0e1e3e20c1b87838f8,0xf1c2b87838f8a203c7a,0xf8a2c3870be0e1e3e289,0x1e0e3e28811242783878,0x3b87838f884480b094ce,0x86e1e0e3e24c2d183c40,0x1e3e20e2387838f883c3,0x87838f883c911100fe0e,0xe8b88110f199844403b,0x10]]
def g255H10 := limbs80 #[#[0x41000000,0xf40000003329000000,0x40000000020000000000]]
def g255D11 := limbs80 #[#[0x50510ff531443fe4c110,0x442ffe0d10bfd83443fd,0xffd43442ffe1110bfd84,0x50530ffd84443ff60d10,0x2e87c0f800ffd31503ff,0xb52969460c6c97b4d8ff,0x109206678b830e3c4208,0x7063c42c8199e260c38f,0x273e0c38f1082730c898,0xa243a6c18b1e11838e18,0xe21838f182f361c18f10,0xe0c7893cc30327c3831,0x7063c438918b46c54d13,0x2b0e0c78879230488cf8,0xb13061c78a42b2060bcc,0x12c4c3831e294a484]]
def g255H11 := limbs80 #[#[0x63bc0c4a48688a20600e,0x1300073c00345eea4ead,0x28a52c00e0e5000000,0x3140000289003c7d0400,0xa132f736e46800040986]]
def g255D12 := limbs80 #[#[0xffa83ff503fe987fd10,0x69c5121823889a8723c0,0x88a2049e58218e220832,0xa48608e22c8126961823,0x59]]
def g255H12 := limbs80 #[#[0x0,0x0,0x1e400000000000000,0x0,0x30000000000000000000,0x24a0000000001,0x0,0x0,0x12a0000,0x3a400000000000,0x0,0x16200000a00000000,0x0,0x0,0x0,0x126000000000000000,0x28400000000000000000,0x0,0x240000000,0x0,0x0,0x69c0000000,0x0,0x0,0x3ac0000000000,0xb880001090000,0x0,0x4a,0x4000000,0x860000000000000000]]
def g255D13 (j : Nat) := if j=0 then 0xe6290201888ff else 0
def g255H13 := limbs80 #[#[0x0,0x0,0x0,0x3c000000000004000,0xc1a80000000,0xb000000000000,0x0,0x79]]
def g255L : Nat → Packing
  | 9 => (5,4,5,0,0,9,0,g255D9)
  | 10 => (20,3,5,0,0,11,0,g255D10)
  | 11 => (12,2,5,0,0,10,0,g255D11)
  | 12 => (4,1,5,0,0,8,0,g255D12)
  | 13 => (1,0,5,0,0,0,0,g255D13)
  | _ => emptyPacking
def g255I : Nat → Nat → Option (Nat × Nat)
  | 10 => lookupWord 1 31 0 8 3 1 g255H10
  | 11 => lookupWord 6 37 5 10 5 1 g255H11
  | 12 => lookupWord 4 277 0 9 4 1 g255H12
  | 13 => lookupWord 1 97 0 7 2 1 g255H13
  | _ => fun _ => none
def g255 : Forest := ⟨255,13,fun i => g255Y[i]?.getD (0,0),g255C,g255A,g255L,g255I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_0 : block g255 9 0 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_1 : block g255 9 1 4=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B9 : block g255 9 0 5=true := (@block_merge g255 9 0 1 4 g255P9_0 g255P9_1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_0 : block g255 10 0 10=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_10 : block g255 10 10 9=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_19 : block g255 10 19 1=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B10 : block g255 10 0 20=true := (@block_merge g255 10 0 10 10 g255P10_0 (@block_merge g255 10 10 9 1 g255P10_10 g255P10_19))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P11_0 : block g255 11 0 7=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P11_7 : block g255 11 7 5=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B11 : block g255 11 0 12=true := (@block_merge g255 11 0 7 5 g255P11_0 g255P11_7)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P12_0 : block g255 12 0 4=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B12 : block g255 12 0 4=true := g255P12_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P13_0 : block g255 13 0 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B13 : block g255 13 0 1=true := g255P13_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255T : checkedTables g255 13 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g255 0 0 0 = true)
  · exact (rfl : block g255 1 0 0 = true)
  · exact (rfl : block g255 2 0 0 = true)
  · exact (rfl : block g255 3 0 0 = true)
  · exact (rfl : block g255 4 0 0 = true)
  · exact (rfl : block g255 5 0 0 = true)
  · exact (rfl : block g255 6 0 0 = true)
  · exact (rfl : block g255 7 0 0 = true)
  · exact (rfl : block g255 8 0 0 = true)
  · exact g255B9
  · exact g255B10
  · exact g255B11
  · exact g255B12
  · exact g255B13
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255G : graphValid g255 (boundsBefore K247) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255R : Impossible true graph 13 sevenInputs.toFinset := by
  rw [show graph = targetOf g255 by decide +kernel]
  exact root_index (g:=g255) (top:=13) (i:=0) (before_sound K247 V247) g255G g255T (by decide) (by decide +kernel)

end PEqualNP.Outside.L_meta_52586

open PEqualNP.Outside.L_meta_52586 in
theorem PEqualNP.Outside.L_meta_52586 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 3, 0, 4, 2, 4, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 3, 0, 4, 2, 4, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o fit _ correct
  exact replaceShort g255R gates o fit correct

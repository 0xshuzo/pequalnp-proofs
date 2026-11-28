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
def K73 := extendKnown K11 4 [(73,[]),(74,[16]),(81,[67]),(84,[32,16,67]),(137,[118]),(193,[99,67,84,117]),(200,[48,16,33,98,66,84,117])]
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
def K77 := extendKnown K75 5 [(77,[]),(78,[16]),(83,[33,67]),(86,[32,16,67]),(90,[16,66]),(92,[32,16,49,65]),(106,[48,16,82,97,66]),(116,[64,16,82,99,50]),(166,[16,115,67,84,101]),(178,[16,66,83,118])]
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
def K94 := extendKnown K91 8 [(94,[])]
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
def K205 := extendKnown K203 8 [(205,[]),(206,[16]),(233,[82,66,118])]
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
def K95 := extendKnown K63 10 [(95,[])]
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
def g127C : List ColumnInfo := [(32,0,95,0,10),(1,0,126,0,9),(2,0,125,0,9),(4,0,123,0,9),(8,0,119,0,9),(16,0,111,0,9),(33,0,94,0,8),(64,0,63,0,8),(0,32,89,6,7),(10,0,117,0,7),(12,0,115,0,7),(18,0,109,0,7),(20,0,107,0,7),(34,0,93,0,7),(36,0,91,0,7),(2,32,89,4,6),(3,0,124,0,6),(4,32,89,2,6),(5,0,122,0,6),(8,32,81,6,6),(9,0,118,0,6),(16,32,73,6,6),(17,0,110,0,6),(40,0,87,0,6),(48,0,79,0,6),(6,0,89,0,5),(6,32,89,0,5),(10,32,81,4,5),(11,0,116,0,5),(12,32,81,2,5),(18,32,73,4,5),(20,32,73,2,5),(21,0,106,0,5),(24,0,103,0,5),(41,0,86,0,5),(65,0,62,0,5),(66,0,61,0,5),(68,0,59,0,5),(72,0,55,0,5),(80,0,47,0,5),(96,0,31,0,5),(13,0,114,0,4),(14,0,81,0,4),(14,32,81,0,4),(19,0,108,0,4),(22,0,73,0,4),(22,32,73,0,4),(26,0,101,0,4),(28,0,99,0,4),(73,0,54,0,4),(74,0,53,0,4),(81,0,46,0,4),(84,0,43,0,4),(98,0,29,0,4),(100,0,27,0,4),(80,8,36,3,3),(19,8,36,64,2),(27,0,100,0,2),(75,0,52,0,2),(82,8,36,1,2)]
def g127A : List (List Nat) := [[],[33,67]]
def g127D5 := limbs80 #[#[0x219585d8a95952148110,0xc32b1bb152b2a42902]]
set_option maxRecDepth 16000 in
def g127D6 := limbs80 #[#[0x20443661965952148110,0xd21481109d82a565485,0x869b9548520443bc1835,0x4427e1a950d2148110bd,0x2148110ef060d6348520,0xd963485204437c19358d,0x2de3a758d2148110f385,0x48110af86a1634852044,0x63485204427e1a958d21,0xe1a7d8d2148110f385db,0x110af86a36348520442d,0x485204427e1a9d8d2148,0x9660d2148110e785d983,0xaf8e9983485204433e1,0x5204439e176e0d214811,0xe0d2148110cf865b8348,0x785d99348520442be1a6,0x4433e18664d2148110d,0xd2148110cf8e19934852,0x61b93485204435e176e4,0x433e386e4d2148110cf8,0x1481109f869b93485204,0x96548520443d61765952,0x761965952148110f58dd,0x8110f585db9548520443,0x548520443d6376e55214,0x3a35d92148110dd865b9,0x10f7028d7648520442fc,0x8520443dc3a35d921481,0x79d92148110b78e91764,0xaf86a27648520442de1a,0x204427e1a99d92148110],#[0x592148110b7869376485,0x8e9596485204427e3a36,0x4427e1a9a592148110dd,0x6148110f345d9634c520,0x58350d20443e6192595,0x3f116550d414c110ee45,0x4c110f645d9435053044,0x4350530443b918650d41,0x91a650d414c110de4659,0x110be4e994350530442f,0x58530443ad18258d614c,0x215d9634c110f9450d65,0xf345057658d30443cd1,0x5604438d9825d9634c11,0x58d3158110db4649634c,0x2c5c964505604436d194,0x443cb3725914158110f,0x14158110eac609645056,0x6496450560443ab38259,0x436b1935914158110dac,0x158110bac68d64505604,0x96558560442eb3a35914,0xc73725956158110f1c5c,0x8110e9c6096558560443,0x558560443a7382595615,0x3925956158110d9c6496,0x10f1c5cd655856044367,0x8560443c737359561581,0x35956158110e9c60d655,0xd9c64d6558560443a738,0x60443673935956158110,0x956158110f1c5d165585],#[0xc6516558560443c73745,0x443673945956158110d9,0x6258110d2e65d6450960,0x96558960443e6121595,0x2cd9a45cd6358110e9ae,0x58110d3665373d8d6044,0x7459160443cb1215d164,0xbba25d16458110e2ee09,0x110d2e64d7459160442c,0x591604434bb935d16458,0xa35d16458110b2e68d74,0xf615d1434c921442cbb,0x921443ca574591624851,0x5956248510ea96116458,0x19dd96558921443c6576,0x1442b64a85956248510f,0x96548510f98641655892,0xe898659521443a73a061,0x43371602616548510e99,0x548510c5d5d898595214,0x97658d31443177762616,0x8d5845d9634c510e3560,0x510fa84816458941443,0x5e0161443ca572591625,0x1925978058510e9c6096,0x10e9c61165e016144367,0x8961443e612059562585,0x25956258510f195c9655,0xb1d2a5655c961443a678,0x61442cd5a25cd6358510,0x957358510b356917358d,0x550d65dcd61443475945],#[0x443c57835977358510f1,0x7458510d1d65165dcd61,0x4d655d161443c3543595,0x315d65e4d8758910d1de,0x59110c575979361d6344,0x935d96544315d65e4d87,0xd37158d2158130d1758b,0x130d96e5563485604c3c,0xdc5604c34d99258f7158,0x9458f7258130d3665163,0xb3669163dc9604c34d9,0xd604c3c9972591435813,0x6594358130f26dc96450,0x165c56558d604c369941,0x4c3a59815956358130f,0x56358130f165c96558d6,0x6516558d604c3c597459,0xc2cdba15d16358130d96,0x358130b36e897458d604,0xb7458d604c38d8a85d16,0x4d97164f6458130b3668,0x8530d365c993d91604c3,0x3603614c38d97258d80d,0x965e418759130e365d16,0x30a1f68786595744c317,0xc56158287fa1e19655d1,0x3e5182dcd60d1d64965d,0xc4f5979460b7358319d6,0x31d838d58258d714c760,0x8f8050f60e35611635c5,0x15c1434c9414878d9715,0x487d857650d3250521f6],#[0x3250521ee1619434c941,0x99434c941486f85a650d,0x76a5905916250521be1e,0x58521da9e41645894148,0x65e0961487a678059562,0x65905978258521e99601,0x521db1e496350d614876,0x58d614874d59758d4358,0xa0e457659521e35e0173,0x1f19e4b915d965486c75,0x1614c717510e6176dd52,0x5956358531e355d163e0,0x956016558d614c7c5570,0x14c7c55745956358531e,0x16358531b35e817458d6,0x60165e0d614c6cd7a25d,0xc7c55745978358531e95,0x759131d1de41655d1614,0x16350d6150717965e418,0xa958058d4358541f255c,0x8541ea5e016350d61507,0x550d61507e1530595435,0x5705956458541f85e0d6,0x41e8d6016559161507c3,0x9161507a378059564585,0x35956458541f0d5cd655,0xd8de4d65591615076359,0x70587a35805978458541,0x97835c161e9548565e0d,0x5e4565e0d70587a55415,0x587a57a1597835c161e9,0x835c161e175c965e0d70],#[0x4165e056258785f72597,0x7275945978158d61c9d6,0x59161e8d50d65e056458,0x901d96350f2759359781,0x95406447658d43da6691,0x543d355c1911d96350f6,0x6007650f47961e417659,0xa95d9801d943e3664d76,0x3c3eea5766007650f0f8,0x87650f0f8a0e61761d94,0xe4184dc563c3ee83985d,0x7c587906137158f1f121,0x317965e4184dc563c,0xfc5c8b315a29c4b07a09,0x748e31ba35c688cb18a2,0x91321a41c808fb1ea3bc,0x327a4dc9892b24a47c8c,0xda59cb095b2aa53ca494,0x65cc898b30a5fcbc9732,0xce09bb36a6bcd49a333a,0x89eb3ca77cec9d339a71,0x1b42a83d04a033fa7dcf,0x48a8fd1ca3345a89d10a,0xa9bd34a634ba95d28a4b,0x7d4ca9351aa1d40a7b4e,0x64ac357aadd58aab54aa,0xaf35dab9d70adb5aab3d,0x363ac5d88b0b60abfd7c,0x9ad1da0b3b66acbd94b2,0xdddb8b6b6cad7dacb536,0xdd0b9b72ae3dc4b836fa,0x8bcb78aefddcbb375ae9],#[0xfb7eafbdf4be37baf5de,0x84b07e0cc1381b01e00b,0xb13e24c4387b0de18c2b,0xfe3cc738db19e30c5b8a,0x54ca393b25e48c8b90b1,0xcd399b31e60cbb96b2be,0x39fb3de78ceb9cb37e6c,0x5b49e90d1ba2b43e84d0,0x55ea8d4ba8b4fe9cd33a,0xec0d7baeb5beb4d63abb,0x8dabb4b67eccd93b1b61,0xb80dc005635c3b7b6ded,0xd17c20c003220250480b,0xc83040a285]]
def g127H6 (j : Nat) := if j=0 then 0x2f00af39 else 0
set_option maxRecDepth 16000 in
def g127D7 := limbs80 #[#[0x90a40886f860d2148110,0x217e193485204437c706,0x952148110bf1c9a42902,0x443ec72a90a40887d85,0x1bb24290221de1764852,0xa40885f86592148110ef,0xe716558520442fc72c90,0x614c110fc8a1a8298221,0x43ce2cab0a60887b458d,0x1a62b0221cd97658d304,0x887ac5914158110f68b,0x97358d60443ce2cab0ac,0x58110e6db9ec6b0221cd,0xccacab12428872e5d164,0xca90a21a758659521443,0x87355d9634c5109ba4c2,0x55c961443ce2cbc02c28,0x510e3ab2ee4b0a21c756,0xae6b1ac28869d5978258,0xb0a21cd773d8d614439a,0x1d5957358510b3acaec6,0xd1614438eacbb9ac2887,0xe3ab2ee8b0a21c75655,0xeb2ac28871d25d655851,0x2211df9361d624438ef2,0xe4d87d8910d3ab2b03b1,0x724422f930b2ae488477,0xefc9b0eb1a2117d96e15,0x3ec888477e4d87591108,0x155f935d9654423bf26c,0xf8158130e6cb1ee2b026,0x4c39b2c7b92c0986b658],#[0xcb286b0261e996450d60,0xc0987965956358130b6c,0xdb7458d604c39b2e8b1a,0x458130b6dca2c6b0261c,0x35b2c6c06c2985b664f6,0x2caba2611fb9061d644c,0xb071d5977158560c3fc3,0x9460b735823eb2243a86,0xc7608becbf0a90ec11bf,0xb2c7c0287b073558d714,0x4a0a43f85434c9414875,0xf995956258521f52b22c,0x58d61487ccacbc12c290,0x21aba4bacab0a43cd573,0x2dc2ae690c5f66375d8d,0x2a43c77915d9654862fb,0xfe6176dd5218becb50eb,0x1614c62fb313b6ea90c5,0xf2ab2ac6b0a63ad563e0,0xc1ac298f355d16358531,0x63c75655d1614c7caacb,0x8d43585418fdc830eb22,0x1507c6acaa1ac2a0fa55,0xab2f08b0a83e35655916,0xac4b0e97597835c161f1,0xa7565e05635874eacbc0,0x8750f61d3ab2f02b22c3,0xedb3203b2c6a1c7ee41,0x82ecb2a876d5911d9635,0xca1e3e5d9801d943abdc,0xb906137158e1ff30bb0e,0x48110ff0a1a42902211f],#[0xfc6c690a40887f858d21,0x4290221fe17648520443,0x87f86592148110ff13b2,0x24c520443fc52c90a408,0x110fe8b1a6290221fe14,0x306a1a40886fce193148,0x98221fe162485304437b,0xae5914258110fe8a1a42,0xc921443cf2cab12c0887,0xef2ba26490a21fc5434,0x8b1242887b9591624851,0xa21f656558921443dcec,0x5d14348510fb3c2ac490,0x21442fcb25b1a428876d,0xbacb70a90a217e592d91,0x1282885f964a8648510b,0x1e756558961443d6ac8b,0x16250910eceba2869922,0x4c3db2c690ac0987ab59,0xb1ac290a61f954350521,0x8290cdf2616548560f6a,0xa54358941487f8ac6992,0x358521bdbcb286a0a43f,0x7daac6a12c298fb558d4,0x28699283f95434c96150,0x887f860d2148110bcfcb,0x944c520443fc2c498a40,0x8110ef8bb262902217f1,0xe32c98a40886fc619314,0x290221fe13250520442f,0x7ec50d4148110ff0b128,0x505204437e306a0a4088],#[0x10ef8bb28290221fb164,0xca0a408877cdd941481,0x2217f196505204437e3,0x86496148110ff0b12c29,0x520443de2c6b0a40887f,0xdf8c1ac290221ef36358,0xb0a40886fce0d6148110,0x21df17458520442fe726,0x516148110ef9ba2c2902,0x443ee2cab0a40885fce,0x9c32c290221bf1865852,0xa40886f660d6348110df,0x5fb9758d204439f2ecb1,0x63481109fccc2c690221,0x42fd325b1a40885fc647,0xbec690221cf976d8d204,0x884fe6636348110afcc,0xb9660d204433f2ecc1a4,0x48110cfcbb706902213f,0xaf2ecb2a40884fe65b83,0xec90221d7b7659520443,0x85fae497648110bf9c8a,0x15d920442fb726bb2408,0x110ef5c92ec90221df39,0x726bb2408877624d7648,0x902215fb945d920443bb,0xfa64a7648110bf8c8cec,0xd920442bf32f3b240885,0xafcca6ec902213f9989,0x890a60887f458d214c11,0x221df17648530442fe32,0x659214c110df8c324298],#[0x30443fa2c6a0a60885fc,0xb8b2a8298221fb164505,0xa608877c5d9414c110f,0x17f196505304437e30ca,0xd614c110bf9c92c29822,0x443fa2c6b0a60887f450,0xb2ac2982217f39458530,0x60886fc619614c110fb8,0x996450d30443fa322a1a,0x34c110facb2a8698221f,0x37b30ca1a60887765d94,0x286982217d99650d3044,0x887f4645634c110bedcb,0x6558d30442fb728b1a60,0xc110eecbb2c698221f59,0xf30cb2a608875e5d9654,0xc98221ddb935d9304436,0x6f6e4d864c1109fdc930,0x48560443fc26490ac088,0x10ff0c1242b0221fe162,0xc690ac0887bc58d21581,0x221bf38348560443de6,0xce4d2158110bf8c9a42b,0x560443de2c890ac0885f,0xef8ba242b0221ef36448,0x90ac08877cdd12158110,0x217f39448560442fe328,0x552158110fb8b2a42b02,0x442fe32c90ac0887dce,0x9c1262b02217f3964856,0xac0887f458d3158110df,0xef3644c560443de2c898],#[0x3158110bf8ca262b0221,0x42fe32c98ac0887dc595,0x9282b0221df172505604,0x886fce094158110ef9b,0x16350560443f6286a0ac,0x58110f79b1a82b0221ef,0xf62c8a0ac0886fce0d41,0x82b0221f716550560443,0x877c5c96158110bf8cb2,0x258560443be6e4b0ac08,0x110bf9c92c2b0221bf38,0x2e6b0ac0887bc58d6158,0xb0221df37358560443be,0xfce4d6158110df9c1ac2,0x8560443de2c8b0ac0885,0xef9ba2c2b0221df1745,0x5c0ac0885fce51615811,0x2217f192e05604437e30,0xdcd3258110f6cb1a64b0,0x60442bf32e992c088776,0xf5c12c4b02213fa984c9,0x92c08873e58d7258110d,0x15fb935c9604439f6c6b,0x57258110ebcb2ae4b022,0x4439f12cb92c08875ee5,0xb26e4b0221cfb965c960,0xc08873ed937258110e7c,0x7965dc960442bf329b92,0x258110bf9c8b04b0221d,0x27f327c12c0885eee518,0x704b0221af964e096044,0x8867e5d38258110d7db2],#[0x65e09604433f6e9c12c0,0x8110f78c8ac6b0221b79,0xb706b1ac0887b650d635,0x6b0221cf97458d60443d,0x5bee516358110b7cca2c,0xd8d604439f2e9b1ac088,0x10eecb1ae6b02216f994,0xc8b9ac08873e59173581,0x2215f9945cd604439f6,0xe64b7358110ebcb2ae6b,0xd60443bb287b9ac08857,0xe7cb26e6b0221ddb83dc,0xb9ac08873ed937358110,0x21d7965dcd60442bf329,0x8f83581109fcc9706b02,0x4436f2cbc1ac0886f65,0xca1ac8b0221ef1915916,0x2c0885bee4d6458110f5,0xebb8459160443d72e8b2,0x7458110b7cc9ec8b0221,0x43b7286ba2c08857ee49,0x22e8b02215fb935d1604,0x8875e5957458110edcb,0x965dd160442bf325ba2c,0x58110fb9c8acab0221d7,0xcf2c8b2ac08879e58d65,0x6490a21fc5634c921443,0x86f96193248510ef2bb2,0x58921442fcb2c992428,0x510df2c1ac490a21fe19,0xf26b1242886f9e0d6248,0x90a21de57458921442fc],#[0xf96116248510ef3ba2c4,0x89214437cf08b1242886,0xef3bb2c490a21de5765,0x4a1a42885fce41434851,0xa213f59850d21442fcf2,0x5d96348510deac1ac690,0x21442bef2eb1a428873d,0xf8c86c690a213f59858d,0x1a428873d5db6348510b,0x13f598d8d21442beb2fb,0xb8348510cfabb30690a2,0x4427eb2dc1a428867d5d,0xc92c890a217f39059121,0x428876d5d16448510bf3,0xf5975912144376b08b22,0x4485109facc2c890a215,0x2beb2fb2242885fc6436,0x2e890a213f598d912144,0x8857de597448510cfac3,0x96dd1214433eb0dba242,0x8510cfabb30890a215f5,0xeaedc22428867ddd9844,0x890a219f776e11214433,0x75d5d965485109facb70,0x59521443aeeecb2a4288,0x10ebabb70a90a21b7586,0xdc2a428875dddb85485,0xa217f3905d9214436eb,0x5e4d7648510bf3c92ec9,0x921443be720bb242885f,0xeea49aec90a21de7925d,0xbb24288775e4d7648510],#[0x217f1909d921442bef28,0x5e7648510bf2c94ec90a,0x14427eb313b2428857d6,0x9c830c90a215f594dd92,0x242885f9e498648510bf,0xbe792619214437e720c3,0x86485109fbc9b0c90a21,0x436ef2ac3242884fde51,0xbd0c90a217f190a19214,0x2884fd6628648510afac,0x58458d31443fa320b1a6,0x4c510faab2ac698a21bd,0x7ef24c2262887755d963,0x898a21bb56461131442,0x867d5d9844c510dbab2b,0x6611314427eb2cc22628,0x510ebabb2ca98a213f79,0xf26bb262886dd619654c,0x98a213f79261931443ba,0xfde51864c510debc9b0c,0xc941443bcae499282884,0xef2b92c4a0a21f95434,0x6b92828857d65d625051,0xa21db5645c941443b6a8,0x6197250510edbca2e4a0,0x41442bef2cb92828867d,0xfac36e4a0a21db564dc9,0x1a828857d65b7250510c,0x1f356550d41443f2ac6a,0x94350510edabb286a0a2,0x442f6b2ca1a82886ed61,0xc82c8a0a217b79650d41],#[0x82887add896450510fd9,0x356559141442f6f26b22,0x450510edabb2c8a0a21f,0x3aeaecb2a828876ddd96,0x2caa0a21d77765954144,0x8877ce417650510dbac3,0x635d941442bef24bb282,0x510e7bb1aeca0a21cf5,0xaf26bb2828877524d765,0xca0a21db7945d941443b,0x57d65b7650510afac96e,0x619414437e720c328288,0x109fbc9b0ca0a213f792,0x5c02c2886ede5186505,0xa217f192e01614437e3,0x558d3258510df8c2700b,0x961443baee6992c2887b,0x9fb4c264b0a215f5974c,0xa12c28857d65d4258510,0x21de572589614427ed30,0x8d7258510df3c12c4b0a,0x14439eec6b92c28873d5,0xbc22e4b0a215f7935c96,0x2c28857de517258510cf,0xd77955c961443aeacab9,0x7258510e7a4b2e4b0a21,0x433ef09b92c28873de59,0x2ee4b0a215f594dc9614,0x2884fd64f8258510ebab,0x774e09614433eae9c12c,0x585109faca704b0a219f,0xde320b1ac2886dd59782],#[0xc6b0a21ed54358d61443,0x873d5d16358510f6bc1a,0x35cd614439eae9b1ac28,0x510afaca2e6b0a21dd56,0xb25b9ac28875d5957358,0xb0a21dd543dcd61442be,0x7d6537358510eebc1ee6,0xd61443aeacbb9ac2885,0xdeaa1f06b0a213f592e,0x9c1ac2886f558f835851,0xa213f794e0d614427eb2,0xe497458510dbab2f06b0,0x61443b6a86ba2c28857d,0xdab22e8b0a215f7935d1,0xa2c28875d5957458510e,0x1d7565dd161442beb25b,0xb8458510df8c8708b0a2,0x4427eb27c22c2884fd64,0xb2f08b0a21bb564e1161,0xc28879d58d6558510dba,0x757259561443ceac8b2a,0x558510f3ac12cab0a21e,0x3cea86b2ac28879de096,0xacab0a21e75835956144,0x8879d5d16558510f3bc1,0x8459561443ceb08b2ac2,0xc910f3bcbacab0a21e77,0xdf2eb126488773dcd624,0x699221cdd7658d32442b,0x677613734c910ceec3ac,0xdcd32442bbb29b9a6488,0x10aefc9ae8992215dd96],#[0x26c3a648847f661744c9,0x92211ff9461d324433bf,0xfe59874c9108fecb30e9,0x1624423fb31bb2848847,0xe3ebb2cab1221cbd7459,0xb2ac48871fdd96558910,0x21e7980595624432fb0e,0xc96558910f3ac0acab12,0x24438fb0eb2ac48879b5,0xdc830eb1221c7e875956,0xac48867de458758910cf,0x9df9361d624433b926c3,0x87589108ffc9b0eb1221,0x431ff2cc3ac48865fe55,0x9f0eb12211ff9661d624,0x4886fc4c580d89108fec,0x973603624437e282c06c,0xd8910cfdb9b01b12219f,0x7f726c06c4884fe64d80,0x1b1221af96460362442,0x867edd180d8910cfcba3,0x3607624437e260c0ec48,0x910cfbb9b03b12219f57,0xf26c0ec4884fd64d81d8,0xb12219f574607624427e,0xfd65181d8910cfbba303,0x1f624427ef28c0ec4884,0xcfa98b0fb12219f9306,0x6c3ec48867d50587d891,0x2211fd9361f624433b92,0xe4d87d8910cefc9b0fb1,0x624423fb28c3ec48847f],#[0xbcb070ab92211ff9461f,0x2ae4886dd587855c910d,0x197e76e15724432faedc,0xf835c9109becb70ab922,0x4433bec7c1ae48867750,0xca706b92211fd94e0d72,0xe48847f65b835c9108ff,0x7f86595724423ff2dc1a,0x55c910abe4c2cab92219,0x32fb0dc2ae48865f21b8,0x70ab922197e86e157244,0x8855f65b855c910cbfc3,0x95e19724423fb27c32e4,0xc9108fecb70cb922197f,0xfb2cc26e48866f59184d,0xdb922197d86597724423,0x6fc5878050d108ffca30,0xe01434433f2e5c028688,0x10decb1f00a1a213f992,0xcbc0286886ee5938050d,0x1a213f996e01434436f2,0x764b7350d10cefc16e6a,0xd43443b3ac9b9a868857,0xaeecb6e6a1a21d5d65dc,0xba2868876758d7450d10,0x219bd865d143443a7aca,0x597450d10cdfc32e8a1a,0x3442b7f2cba2868856f6,0xfc930ea1a219f79161d4,0xa868867758d8750d108f,0x97d6561d4344337ac8c3,0x8750d108fecb30ea1a21],#[0x433bac7c3a868847fe59,0x2f0ea1a219bd64e1d434,0x68847f65b8750d10cbeb,0xd435d963443abacab9ac,0x58d10e6fc9aecb1a21cd,0x3bf26c3ac68847fe4987,0xeb1a211ff9461d63443,0x847f64b8758d10cbeb2b,0x1603634423fb29c3ac68,0xd10cfcb9301b1a21bf14,0x2e8c06c6884fee4980d8,0xb1a219f572607634433f,0x7d5d181d8d109fbc9303,0x7634427eb28c0ec6886,0xcf6b9305b1a213f7946,0xec16c688677dcd82d8d1,0xa219dd84dcf634423fb2,0x50587d8d10e6fc9aedb1,0x634423ff24c3ec68867d,0xfeca30fb1a219df9361f,0x16e68847fe5187d8d108,0x11fd9460b734433dac4c,0x982dcd108ffca305b9a2,0x4423ff2cc16e68847f65,0xb2b09b9a219bd6461373,0xe68847f65984dcd10cbe,0xff9261b734432fb0cb2e,0x6dcd10cefc9b0db9a211,0x37e263c02c88847fe518,0xf00b2221bf161e016444,0x884fe64b8059110df8c8,0x93e016444377287c02c8],#[0x91109fdc9f00b22213f9,0xf2edc02c8886de597805,0xb22219fb76e01644433,0x76ee017459110cfccbf0,0x5d16444397ec4ba2c888,0x10cdfc1ae8b22215bf92,0xcaba2c88856fe4d74591,0x22219fb9061d64443a7a,0x724d87591108ffc930eb,0xd644433bf26c3ac88867,0xcdfca30eb22211ff9361,0xc3ac88865f5958759110,0x211fd93e1d6444337a87,0xc980d9110df898b01b22,0x44427f724c06c88867ed,0xdb9b01b22219f9736036,0x6c8884fe64d80d9110cf,0xbf130607644427f726c0,0x81d9110cfbb9303b2221,0x433eae6c0ec8884fde49,0x9b03b22219f773607644,0x8884fde4d81d91109fac,0x53161f644433f260c3ec,0xd91108ffc930fb22219f,0x3fb26c3ec88867724d87,0xfb22219df9361f64442,0x847f64f825d1108ffc9b,0x2e0d744423fb2dc12e88,0x110cefb1f06ba2211fd9,0xb2dc1ae88865f597835d,0xba22197f86595744423f,0x7f64f865d1108fec970c],#[0xb744423fb2dc32e8884,0x8fecb305ba2219ed626,0xcb2ee88847fe5982dd11,0xa211ff9261b744432fb0,0xddb8159510ebabb702b2,0x65442aff24bb2ca8875d,0xae49aecb2a21c7d635d9,0xb2ca88757e4d7659510e,0x1c7d645d965442aff26b,0xb7659510abfca2ecb2a2,0x442afb29bb2ca8855f64,0xc9700bb221bf141e0176,0xec884fd64b815d9109fc,0xdb90e0d764433dae5c12,0x35d910deaa0f06bb221b,0x33bae5c1aec886f5e478,0xf06bb2219dd74e0d7644,0x8877ce07805d910daeb2,0x83e0176442bf325c02ec,0xd910afac9702bb221ddb,0xdac5c12ec88775e0f815,0x4bb2211fd93e09764433,0x47f653825d9108ffc9f0,0x20d764423ff29c12ec88,0x10cefc1106bb2219dd82,0x841aec88677610835d9,0xb2215de9820d764433bf,0x5e47835d910eedc8706b,0xd764433bb05c1aec8877,0xceec2706bb2219df82e0,0xc1aec88677e13835d910,0x211fd92e0d764433ba65],#[0x8f835d910ceea1f06bb2,0x64423fb29c1aec886775,0xea1706bb2211ff94e0d7,0xaec8867758b835d910ce,0x9df92e0d764433bb25c1,0x835d910ceeb2706bb221,0x433bf29c1aec88677653,0x9f08bb2211fd92e11764,0xc8866f593845d9108fec,0x972602764437e282c04e,0x9d9109fdc93013b2219f,0x3eae4c0cec8867e5d180,0x33b2213f79260676443,0x84fd651819d910cfaba3,0x260a764427ef28c0cec8,0x9108ffc930f3b2219ed7,0xac4c16ec8847fe51879d,0xbb2211ff9460b764433d,0x6f59184dd910cbfcab05,0x85604c3be6e290ac0986,0xafcc96e2b026177b954,0x9b8ac09873e593715813,0x261bd943e05604c2bf32,0x5937258130eeca1ee4b0,0x604c2bf329b92c09873e,0xccb2286b0261f994150d,0x1ac0987e66114358130f,0x1ed99650d604c3eb2caa,0x94358130beccb286b026,0x4c2fb72ca1ac0987b6a5,0xb12c6b0261ed96158d60,0xc0987b65916358130f6c],#[0xd94158d604c3bb2e8b1a,0x358130f6cc0ac6b0261e,0x3db284b1ac0987b66456,0x2c6b0261ed97258d604c,0x987b66496358130f6cc1,0x8458d604c3db2e8b1ac0,0x8130f6cca2c6b0261ed9,0x7282b22c0986f6607835,0x8b0261eb942591604c3d,0x7ae5d16458130f6cc9ac,0x5d1604c2bf722ba2c098,0x30e7c4b2e8b0261d7965,0x30ba2c09873ee5974581,0x2615f992dd1604c33f1,0xe5896558130f3cb0acab,0x5214c3cf2c8b2ac09879,0xeeab1ee290a61de562dc,0xb8a429857d6537148530,0x615ef97589214c2beb2d,0x156348530dafc2a8690a,0x14c32fae9c2a42986d7e,0xecb70a90a6197d76e152,0xa82987e558543505309b,0xf1d6550d414c3f2f22a1,0x4350530ecebb286a0a61,0xc2f3b2ca1a82986e7619,0x2c6b0a6179f9650d414,0x2987b55056358530f6cc,0x980595614c39bae8b1ac,0x58530f3aa0acab0a61e7,0x8fae8b2ac29879750d65,0xeb0a61c7d87595614c3],#[0x867750f87585308fec97,0x3603614c23fb29c3ac29,0x530cfcba301b0a61bd94,0xae4c1ec2987375d163d8,0xb0a619dd7460f614c33b,0x9750d65d85309eeca307,0x17614c38fae8b2ec2987,0xcbeba30bb0a61b5d436,0x8c3ec29867750d87d853,0xa619ed6260b714c23fb2,0x65182dc530ceeb1b05b8,0x714c23fb2cc16e29847f,0xffc9309b8a619dd8458f,0x26e29866f59184dc5308,0x11fd96613714c32facac,0x965589308ffcb309b8a6,0x4c3cdae4b2ac49879b50,0xba2cab1261e5d4359562,0xc49871f61d6558930e3f,0xfd91e1d624c38fd0eb2a,0xd8930deca1b01b12611,0x37b220c1ec4986be5918,0x307b12619dd7160f624c,0x984f765183d8930ceeba,0x43617624c3cba86b2ec4,0xc930ceea1b0fb1261b5d,0xbacaa1ee49876759143d,0x7b92619dd8650f724c3a,0x577e5943dc930aeecb28,0x613724c33bb08b1ee498,0x30cbeb2b09b92619bd64,0x2cc26e49847f65984dc9],#[0x1a61f9964e01434c23ff,0x661b8050d30facb2f00a,0x1434c2fb32dc0286986f,0xf4eb12c8a1a6179f9159,0xb2286987a7d896450d30,0x61d9d76591434c3e3aca,0x196450d30ecfbb2c8a1a,0x34c3d3f0cb2286987a72,0xfbb2caa1a61d5d765954,0xa86986d76196550d30ea,0xddb905d9434c36bf0cb2,0x7650d30aefc92eca1a61,0xc2bbb2dbb2869857764b,0xb30ca1a61bdb90619434,0x6984f7e598650d30d6fc,0x984e01634c27bb2dc328,0x58d30eedc82e8b1a61bd,0xbbf24ba2c698577e4574,0xe8b1a61d9d645d1634c2,0x87372597458d30eaeb2a,0x2dd1634c39bf2cba2c69,0xd30f2eb0acab1a615dd9,0x720c3ac8987975896558,0xb22611ff9161d644c33f,0x3fe598759130cbeb2b0e,0x1d644c23ff2cc3ac8986,0xdec88307b22611fd91e,0x4c1ec8986775c583d913,0x261bd963e01744c33bae,0x597805d130ddcb2700ba,0x744c33f4edc02e8986de,0xbcb2f00ba2613f996e01],#[0x2e89867e21b805d130e,0x15f996e01744c33f50dc,0xb815d130cfa90f02ba26,0x4c23ff25c0ae89847f64,0xcb702ba26197d65e0574,0xe89847fe5b815d1308fe,0x7f86595744c38f90cb2a,0x65d130cbfc32caba261c,0x23fb2dc32e89847f6478,0xb05ba2619ed6260b744c,0x9847f65982dd130cbeb2,0x625d9654c38fac2bb2ca,0x9530e3eb16ecb2a61c7d,0xfb29bb2ca9855f64b765,0xeb2a6157d9421d654c2a,0x67e5cb805d930abeca70,0xe05764c37b287c02ec98,0x308fec9702bb2619f521,0x23c12ec9847f653815d9,0xb2611fd94e09764c23fb,0xf64b845d9308fec8f08b,0x2764c33f2e4c04ec9847,0xcfcba3013b261bd94360,0xc1cec986775c9839d930,0x613dd9460e764c33bae8,0xd1859d930daea1b0b3b2,0x64c33dac4c16ec9865f5,0xfc9309bb2611fd9460b7,0xa42b066f59184dd9308f,0x7f39058521583d6ac8a0,0x7148560f3ab2ac290ac1,0x835bb06b1a42b07795c9],#[0x2ec690ac1a7f8558d215,0x2b069f6196548560d3fc,0x980e15215826fd30b2a4,0x48560cbec3f0a90ac1b7,0x6f321c2a42b065fa1f85,0xa90ac197f73e1521583,0x65f65f85485609becb7,0x158d315832fd2fc2a42b,0x560d6ec22c698ac1ed57,0x720b2282b047f64a874c,0xa0ac1eb57159141583d7,0xaf60d6450560e5fb92c8,0x9141582d7b26b2282b06,0x8fec950ea0ac16bf935,0x5c02c2b06fc507805856,0xac1af964e01615827f32,0x64b71585609fcca700b0,0x61583cea62b2ac2b057d,0x3bc8acab0ac1e7541595,0x2ac2b071fdc96558560f,0x1c7f73595615834ff04b,0xd6558560d3ec1acab0ac,0x5838fee8b2ac2b069fe0,0xc22cab0ac1a7d8459561,0xe2b057de45725c560d3f,0xd940e0d715833bf06b92,0x35c560dedc8706b8ac1b,0x35bac9c1ae2b0677dcb8,0x706b8ac1adf64e0d7158,0xb0677dd3835c560ceeba,0x96e0d715836bacbc1ae2,0xc560cf699305b8ac1adc],#[0xfb26c16e2b067b50982d,0x5b8ac11ff9360b715823,0x47fe5182dc5608feca30,0x58f715832facac16e2b0,0x60ceea1b07b8ac1cdd43,0x86c26e2b047f65183dc5,0x1ac1ed98058d4358337a,0x75056350d60f6dc82c6a,0xd435835bf02b1a86b07a,0xf4eba2c6a1ac1adf8258,0x43a86b06bee418650d60,0xc197d65e1d435823fb23,0x4b8058d608fecb70ea1a,0x35837b287c02c6b04fe6,0xcca700b1ac1af964e016,0xac6b07375877358d609f,0x5dd92dcd63582bbb23b9,0x6558d60f3dc82cab1ac1,0x83cba64b2ac6b07974c5,0x9acab1ac1e5d43595635,0x6b069f6116558d60f2fc,0x984e0163582df325c02c,0x58d60b7cca700b1ac1af,0xdbb23b9ac6b07375c773,0x9b1ac16dd92dcd63582,0x6af50984d8d60d5ea0b,0x1607735833ea42c0ee6b,0xd608fec9303b9ac19f54,0xb28c0ee6b047fe4981dc,0xb9ac11ff94607735823f,0x7b48582dcd60cbeb2b03,0xb735823ff22c16e6b06],#[0xcde4a305b9ac19ed426,0x8c16e6b047f65182dcd6,0xac11ff9460b7358337f2,0x64d65dcd60cbeb2b05b9,0x655836f307c02cab0757,0xf2992e290ec177993e01,0x8a43b073d58d7148760e,0x19f7835c521d833eb06b,0x17148760cfac22e290ec,0xd82beb28b8a43b067de1,0xc2ae290ec15f7945c521,0x43b069f58f8548760ebb,0x7d97e1521d832fae7c2a,0x748760cfaa0b0e90ec19,0x23ff26c3a43b047f64d8,0x2e298ec197f9561d21d8,0xb06b7609634c760cfac2,0x825cd31d835bb08b1a63,0xc760ceec22e698ec19dd,0xef24b8a83b047f651874,0x2a0ec1db5435c541d82b,0x7ad4856450760e7ab1ae,0x59141d8397ae4b2283b0,0x60b5ec9ac8a0ec1abd83,0x42ba283b05afe4d64507,0xec19bd835d141d83b6a,0xfe4d7450760adec9ae8a,0xd41d823ff24c3a83b056,0x8ffc9b0ea0ec19bd4361,0xb1ae3b047f653825c760,0xc11fd92e0d71d839ba86,0x53835c760ceea1f06b8e],#[0x3d823fb25c22e3b047f6,0xccb700a1ec19f971e014,0xa87b067e65f8050f60d7,0xe9d4158d43d83db700b1,0x6350f60d6fc0ac6a1ec1,0x83bb700b9a87b06b7e09,0xae6a1ec1d9d415cd43d,0x7b0677e097350f60cefc,0xb9061943d82bbf24b9a8,0x50f60c7fcbb0ca1ec1af,0x3ff22c3a87b067ee4187,0x2b9ec19f521e0573d82,0x47f653815cf608fec97,0x2e1173d823fb29c12e7b,0x121ebab0eeab82431fd9,0xb2dbaae090e5fe1b755c,0xa0a43de56258770486af,0xf96193250521ef2bb264,0x8941486fcf20b128290e,0x1fd2b22c4a0a437e7935,0x6a1a8290ef9619625052,0xa43db57650d41487f2ac,0x6594350521ddac3286a0,0x414867ef30b1a8290ded,0xdbc9ac8a0a43fa792591,0xb28290f6d5d96450521b,0x3de7925d941486bef20b,0x18650521edbca2eca0a4,0x4877cf24c328290cfde4,0xb1700b0a43bb79461941,0xc290ebd58f8058521df2,0xf573e01614875eec7c02],#[0x58521cfbb9f00b0a439,0x73eee9c02c290e7d5d38,0xf00b0a433f594e016148,0x90edddd78058521dbab2,0x7358961487dcac6b12c2,0x8521ef3b9ac4b0a43de5,0xceeab12c290df9e4d625,0x4b0a43be580e0961487e,0xef96138258521bf2c870,0x50d61487eceebc12c290,0x21afacba86b0a437e792,0x6b1ac290fb964963585,0xa43cf57458d61487daf,0x558d7358521e7aba6c6b,0x161486beb21b9ac290f7,0xafac86e8b0a43db5645d,0xc22c290cfd6438458521,0x43bb564e11614877cb25,0x16558521f3ac02cab0a,0x3486eeb2dbaac290f9de,0xecbf00a1a4397f75e014,0xa8690cfd6438150d218f,0xbb564e05434877aac7c0,0x6350d219facb702a1a43,0x873bb0eb1a8690f57dd5,0x36eaa1a439df8758d434,0x690e5fe1b7550d21cbec,0xd97e1943486afb2dbaa8,0x50d218ffc830ea1a431f,0x3ff2cc3a8690c7f65987,0xea1a431fd90e1d43486,0xcfd6438158d218fecb7],#[0x2e05634877cac5c0ac69,0xd219faca702b1a43be59,0xb2fc0ac690e7d5db8158,0xb1a43dd7815cd634873e,0x5fe137558d21cbfc06ea,0x1d63486afb2dbaac690e,0x1cfbc8b0eb1a431ff906,0x8c3ac690e77e4d8758d2,0xa431fd94e1d634863ff2,0xe4181d8d21cbfbab01b1,0x634873eae8c0ec690cfd,0xfbca303b1a433f594607,0x16c690cfbe4182d8d219,0x39ed7460b634877ca82c,0x187d8d21cbec26ebb1a4,0x4873ea82c3ec690c7fe4,0xca30fb1a431fd9461f63,0xe690e5f583855cd218ff,0xf960603734872fec1c2a,0xdcd218fecb301b9a439,0x63ff20c36e690c7fe598,0x2ecb2a4357f905d96548,0x90f1fe417659521e3ec8,0x915db75486aff20bb6ea,0xd521cbfcc2edbaa43d77,0xef22c36ea90d5f64276d,0x1baa4397d86603754876,0xd5fe4186dd521abfcb30,0x61b754872fb20c36ea90,0x21cbec9b0dbaa4397f90,0x21436ea90e5fe4d86dd5,0xb2439f970e0176486afb],#[0xe583805d9219fac8702b,0x1764863fb27c02ec90e7,0xafac8702bb2431ff93e0,0xc0aec90f79e0b815d921,0x431fd90e0d76487aef0b,0x8f835d921ceea1f06bb2,0x64863fb29c1aec90e775,0xec070abb2431ff94e0d7,0xaec90e5fe03855d921cb,0x9f970602764872fac1c2,0x819d921cfab83033b243,0x863ff20c3cec90cfde41,0xa700b0a639f960603764,0x298fb55816358531cfab,0x56458d614c7daac4b1ac,0x58531eeaba2c6b0a63ed,0xdab00b1ac298fb550163,0xc6b0a63ed59058d614c7,0x8fb56496358531f6ac12,0x458d614c7dab08b1ac29,0x531deac0706b0a63ed59,0xf20ba2c298f755d38358,0xb0a635f7925d1614c6be,0x5d5957458531edab22e8,0x95614c7ceac8b2ac298f,0x1f3ac22cab0a63e75805,0x1c3ac498f2f5d1645893,0x2639f574607624c63fb2,0x5d183d8931dea88307b1,0x634c63fb28c3ec498e77,0xebc8ae8b1a635df905d1,0xa2c698d77e497458d31e],#[0x3d5d655d1634c7b3ac8b,0x57459131adfc82e8b226,0x4c797ec4ba2c898f6de4,0xb2ae8b22635bf925d164,0xc898e7e2418759131e9e,0xff9061d644c73f720c3a,0x759131cfbc8b0eb22631,0x73bf26c3ac898c7fe498,0x307b226397d6561d644c,0x98e775c983d9131dea88,0x60e01744c73f241c02e8,0xd1318fec9700ba2639fb,0xfb2dc02e898e5f597805,0x2ba2635f590e05744c63,0xd7d65b815d131ebab2f0,0xe09744c63fb21c12e898,0x31cbfc32caba2631fd96,0x25c32e898c7f643865d1,0xb2631fd96e19744c63fb,0xf64b805d931cfc90700b,0x9764c63fb29c02ec98c7,0x8feca704bb2631fd90e0,0xc22ec98e77613835d931,0x831fd92e11764c63fb21,0xf80585419fac9700b0a,0x15075eac7c02c2a0eed5,0xab2700b0a83af763e016,0x2c2a0edd5978058541dd,0x3f590e0961507daac699,0x8258541df2b1704b0a83,0x776ac9c12c2a0eed50f,0x1a86b0a83f956350d615],#[0x2a0fcd5954358541fcbc,0x79650d61506f6b2ca1ac,0x58541f6bc1ac6b0a837b,0xd6ac0b22c2a0fad65163,0xc8b0a83eb56259161507,0xdede4d6458541f5ab1a,0x2e116150776b01c22c2a,0x541f3ab1acab0a83bb58,0xf00b2ac2a0f9d6016558,0xb0a83e758359561507ce,0x675d9434c941f3bc1aca,0xd62506f3b2ca1a64a0f,0x1d5fc02c8b12839bf875,0x4b22c4a0fad605645894,0x2831fd90e1d62507d5f2,0xe4181d89418fec9f0eb1,0x6250776a86c0ec4a0cfd,0xda88309b1283abd80593,0x26c4a0e6f5cd84d8941d,0x33bf936136250677b26c,0xd87d89418ffc830fb128,0x5063ff26c3ec4a0e6f50,0xb1f02a1a837b590e0543,0x86a0fcd5978150d41fca,0xb596e054350776b0dc0a,0x350d41bcfc82c6a1a837,0x7e3acab1a86a0de7e496,0x2caa1a83d9d7658d4350,0xa0ecf6196550d41e9ebb,0x905d94350767f0cb2a86,0xd41edbc8aeca1a835bf,0x7120c3286a0f67e4d765],#[0xca1a83bbb90619435077,0xee7e4d8650d41ddbc8b0,0xe1d6350677b2dc3286a0,0x419fbc8303b1a831fd92,0x20c26c6a0cfde4981d8d,0x1a83bb5216136350776a,0xfe4987d8d418ffc830fb,0xd6450776b07c0ac8a0c7,0xd9eb2f06b2283b9d63e0,0xbb2caa0d5fe417659541,0x839f960e0176506aff26,0x4b805d9418fec9700bb2,0x65063fb27c02eca0c7fe,0xbc2702bb2831ff93e017,0x2eca0c7f643825d941ed,0x1fd93e09765073dac5c1,0x835d9418ffc9f04bb283,0x63fb25c1aeca0c7f643,0xf06b82c39dd63e0d765,0xb0ef5507835c161dea9,0xd72e0d705877af23c1ae,0x5c161cefb9706b82c39d,0x3bee9c1ae0b0e775d383,0x6b82c3b5d65e0d70587,0xf9de05655c161d6e4b7,0x259570587cef22b2ae0b,0x161e3fb92cab82c3c7d7,0xae6b2ae0b0e9fe09655c,0xb82c3c7f73595705878f,0x97e0d655c161f2e41aca,0x95705874ff06b2ae0b0f,0x1e3fba2cab82c3c7d745],#[0x4b2ee0b0e9fe11655c16,0x2c3a7d82597705878fae,0x61165dc161e3eba2cbb8,0x705873da64c16e0b0e9f,0xffc9b05b82c31fd9360b,0x16e0b0c7f65182dc1618,0x397d6560b705863ff28c,0x183dc161e6ea1ac7b82c,0x5863ff24c26e0b0c7f65,0xc9b09b82c39bd4361370,0xe0b0e5f59584dc1618ff,0x7d64597705878fac4b2e,0x1589619fac8702b12c3c,0x67eb27c0ac4b0ebd58f8,0xacab92c3a7f805957258,0xb0edd443855c961f3bc0,0x70e15725872fae1c2ae4,0xc961d3ec02cbb92c397f,0xfb26c06e4b0e7e4c180d,0x1b92c31ff93603725863,0xc7fe5180dc9618feca30,0x60f725872facac06e4b0,0x618ffc8309b92c31fd94,0x26c26e4b0e6f50d84dc9,0x1ac3c7d80597725863ff,0x56056350d61d6fc02c6a,0xd43587daf22b1a86b0fb,0xf4eba2c6a1ac3adf8258,0xb9a86b0f675037350d61,0xc35dd92dcd43586bbb21,0x537350d61eceb26e6a1a,0x3587abacbb9a86b0f676],#[0xfc36e6a1ac39dd86dcd4,0xa86b0e9fe016550d61ce,0xe5f7359543587ceb02b2,0x6550d61f1eba2caa1ac3,0x874ff0eb2a86b0e9f61d,0x850ea1ac31fd9021d435,0x6b0c7f64a8750d618fec,0xd65e1d435863fb21c3a8,0x58d618fecb70ea1ac397,0x7eb29c0ac6b0cfd64b81,0xe6b1ac3cdd60dcd63586,0xd7764b7358d61aeec86,0x359563586bbb29b9ac6b,0xd61d3ec22cab1ac3e5d4,0xb29c0ac6b0dbd64b8158,0xb1ac3cdd70dcd63586de,0xb764b7358d61b6ec86e6,0x1763586dbb29b9ac6b0d,0x1d3ec02cbb9ac3a7d706,0xc06e6b0e9f61165dcd6,0xac31fd92603735873f24,0x65180dcd618ffc9301b9,0x735863ff28c06e6b0c7f,0xf690305b9ac397d65603,0x16e6b0c7fe4182dcd61c,0x31ff9460b735863fb28c,0x984dcd618ffc8309b9ac,0x5872facac26e6b0c7fe4,0xb1f02b22c3bb543e0564,0xc8b0cfd64f8159161d7a,0xbd90dd16458797ac1ba2,0x459161e5eb16e8b22c35],#[0x74ff00b2ac8b0d6f64b7,0xacab22c3e3d435956458,0xb0e9fe01655d161d3fc1,0x8359574587cef02b2ae8,0xd161d3ec02cbba2c3a7f,0xf260c06e8b0e7e48180d,0x1ba2c31fd92603745873,0xc7f64d80dd1618ffc930,0x603745863ff26c06e8b0,0x61cf690305ba2c397d65,0x64c16e8b0c7fe4182dd1,0xa2c31fd9360b745873da,0x750d635c3618ffc9b05b,0x170d863fb25c1ae1b0f3,0x8fec9f00b96c31fd92e1,0xc22e5b0c7f643835cb61,0xc39bd43e1172d863fb21,0x1655cb618fec9f08b96,0x3d875bf00b1a87b0f1f6,0xea02e6a1ec3adf8258d4,0xa87b0e77e017350f61ec,0x9df825cd43d86bbf20b9,0x7450f61aefc92e6a1ec3,0x8737f00ba287b0f674c1,0x92e8a1ec35bf905d143d,0x7b0e6fe097450f61ece9,0xf805d543d874ff00b2a8,0x50f61cfc4830ea1ec397,0x3ff20c3a87b0e7ee4187,0xea1ec31ff9261d43d86,0xe6f5038750f61cee987,0xe0173d863fb21c3a87b],#[0xf618fec9700b9ec39f92,0xb29c12e7b0c7f653805c,0xba6c31fd92e1173d863f,0x7f64f825d3618fec9f00,0x77050f3eac2c0ee0a1c,0x3cdeb2303b82879dd636,0xcc0ee0a1e5f59581dc14,0x287ddb9058f7050e3fb2,0x59563dc143eceb22c7b8,0x7050faf720b2ee0a1f57,0xfdc830db828797d86597,0x6e2a1c7fe4586dc143c,0x71fd926037150f3f2c0c,0xd80dc5438ffc9301b8a8,0x50f37ac8c06e2a1e7758,0xcb301b8a8797d6560371,0xe2a1c7fe5980dc5438fe,0xed6260b7150f3da40c16,0x2dc543ceeb1b05b8a879,0xe3fb2cc16e2a1e6f5918,0xac7b8a87d9d6458f7150,0xa1d77e6163dc543eaeb2,0x865977150fa7acab26e2,0xc543c7eb030db8a8797d,0xff20c36e2a1e3fd8186d,0xb1a871ff9261b7150e3,0xcf764b8058d43dedb870,0xe016350f73ac9c02c6a1,0x439eec8704b1a87b5d65,0x29c12c6a1ee75938258d,0x1a87b5d65e096350f73b,0x75816458d43daecaf04b],#[0x16350fd3ac2b22c6a1fa,0xdcec1708b1a87e9f7659,0xb2ac6a1fa7ddb8458d43,0x87cdd701d96350fcbeec,0x607658d43b6ec80ecb1a,0x350f9bae1bb2c6a1db7a,0xec9f00b2a876dd90dd96,0x2caa1d5f65f8059543ba,0xd78905d96550eafd2fc0,0x7659543ebdc82ecb2a87,0xeaff22bb2caa1d5fe41,0x86ecb2a87c7f965d9655,0xaa1f1f5877659543abec,0xd9021d6550eafb23bb2c,0x1d943abec870eb2a8757,0x7aa60c08eca1ef664d80,0x23b287bb5406047650f,0x1ed74c1851d943cfab83,0x5d87650f2fae0c28eca,0x943c7ec02ec3b287cdd3,0x720bb0eca1f3e241761d,0x3b2878ff985d87650f9f,0xee507805d9438fec850e,0x17650f3f2e3c02eca1e,0x3dedc9f00bb2879fb71e,0xdc02eca1ede597805d94,0x287b9d41e0d7650f3f6e,0xe03765d943e7c406ecbb,0x7650e9fb21bb2eca1f3e,0xfcc0900bb287cdf83dd9,0x2eca1e7ee04805d943c,0x75fa982017650f3f70c4],#[0x7805d943cfcc0f00bb28,0x50fbb707c02eca1e7ee0,0xcb700bb287ddb93e0176,0xeca1e7e443805d943e7d,0xfd91e017650f3f2c1c02,0x5d9438ffc8f00bb2871,0xf3f2c3c02eca1e7e4878,0xf00bb2879f991e017650,0xa1e7ee5b805d943cfdc8,0x21e057650e3fb21c0aec,0xd943cfab0f02bb2879f5,0xff25c0aeca1c7f64b815,0x73b287d9f84e0d7650e3,0xeb7581839d943dcea030,0x60e7650f3bae0c1ceca1,0x439eec83073b2879df70,0x82c1ceca1cf7e41839d9,0xb2879dd7160e7650f73a,0x75c9839d943cefb8b073,0xe7650f3bee4c1ceca1e7,0x9efc93073b2873dd9260,0xc2ceca1ed74c1859d943,0x8797f706167650f2fae0,0x81879d943a7ec86ed3b2,0x650f3f120c3ceca1e3f5,0xfc8b0f3b2871ff9061e7,0x6eca1e7e58180dd9438f,0x1ff916037650e3fb22c0,0x81dd943cfa88303bb287,0x8e3fb24c0ee0b1e7d585,0xb05b82c71fd94607705,0xb1c7fe4582dc163cf69],#[0xf9460b7058e3fb28c16e,0xdc163cbeb2b05b82c71f,0x3ff22c26e0b1e6f50584,0x9b82c71ff926137058e,0x1c7f64980dc563cbeb2b,0x60b7158e3fb28c06e2b,0x5638ffc8305b8ac79ed2,0xf28c16e2b1c7f65182dc,0xb8ac79bd406137158e3f,0x7ee4184dc563cfc48309,0x137158e3ff20c26e2b1e,0x3cbeb2b09b8ac71ff926,0x8c2ee4b1ed750d85dc96,0x2c79f9106037258f2fae,0x65180dc9638fec8b01b9,0x7258f3ea20c0ee4b1c7f,0xdea0309b92c71fd94607,0x26e4b1c7fe4184dc963c,0x71ff916137258f37a82c,0x185dc963cbeb2b09b92c,0x58f5bac3c1ac8b1e5f61,0x98f00ba2c73dd91e0d64,0xe8b1ebe587805d163dec,0xf971e017458f5f6c3c02,0x5d163cfdb8f00ba2c79,0xf3f2e5c02e8b1ef64cb8,0xf00ba2c79fb72e017458,0xb1ede597805d163dedc9,0x96e017458f5f12dc02e8,0xd163d6e9870cba2c7afb,0xfb21c32e8b1eaf503865,0x1ba2c79f9106037458e5],#[0xc7f64980dd1638fec8b0,0x6077458f3ea20c0ee8b1,0x63cf690305ba2c71fd92,0x42c16e8b1c7fe4182dd1,0xa2c71ff9160b7458f3da,0xf64b815c363cbeb2b05b,0x170d8e3fb23c12e1b1c7,0x8fec9708b86c71fd91e1,0xc02e3b1c7f64b805c763,0xc71fd90e0971d8e3fb29,0x43845c7638feca704b8e,0x2d8e3fb25c22e3b1c7f6,0xec8702b96c71fd91e017,0x2e5b1c7f643845cb638f,0x9f910e0174d8e3fb23c2,0x825d3638fec8f00ba6c7,0x963fb23c12e9b1e7b487,0xa307b82cb97d84dcf705,0x6b2ede583805cd659bfc,0x1c003800036eac1c0ae,0x63816004780f0030809e,0xb027e096822c07f81c60,0x37e0d9032c0bf82da0a,0x49c11904360ff83d00e6,0x8815b855414985021350,0xe191862217f85da16d85,0x1c506fa1ba86c61ad867,0xe707781d507441cd0724,0x4886421008081f687b61,0x92824608fe23688c022,0x9ec26f89ae265096624e,0xc42a80a7c2960a342818],#[0x42d18b362c20af82ba0a,0x3028bf02f08ba82e38b7,0x338cb43268c7630f8c2e,0xc0d8235c8d4e34a8cfc3,0x8e5a3900e3037e0dde36,0xfb43df0f4e3c30eca3a4,0x3c40b10084008ff23f60,0xa42a909a420106641810,0x445110443a90da43290b,0x5d1164450113a44a911a,0xf11ec46f91b846a11844,0x12564919222484920c47,0x27a49d126e49a1262497,0x9e4a612924a312864a01,0x24af12b64ac12aa4a912,0x4b812da4b512ce4b212c,0xc112fe4be12f24bb12e6,0xa13224c713164c4130a4,0x13464d0133a4cd132e4c,0x36a4d9135e4d613524d3,0x8e4e213824df13764dc1,0x24eb13a64e8139a4e513,0x4f413ca4f113be4ee13b,0xfd13ee4fa13e24f713d6,0x61412503140650013fa4,0x143650c142a509141e50,0x45a515144e512144250f,0x7e51e147251b14665181,0x25271496524148a52114,0x53014ba52d14ae52a14a,0x3914de53614d253314c6,0x2150253f14f653c14ea5],#[0x1526548151a545150e54,0x54a551153e54e153254b,0x6e55a156255715565541,0x25631586560157a55d15,0x56c15aa569159e566159,0x7515ce57215c256f15b6,0xe15f257b15e657815da5,0x1616584160a58115fe57,0x63a58d162e58a1622587,0x5e596165259316465901,0x259f167659c166a59916,0x5a8169a5a5168e5a2168,0xb116be5ae16b25ab16a6,0xa16e25b716d65b416ca5,0x17065c016fa5bd16ee5b,0x72a5c9171e5c617125c3,0x4e5d217425cf17365cc1,0x25db17665d8175a5d517,0x5e4178a5e1177e5de177,0xed17ae5ea17a25e71796,0x617d25f317c65f017ba5,0x17f65fc17ea5f917de5f,0x81a605180e60218025ff,0x3e60e183260b18266081,0x26171856614184a61118,0x620187a61d186e61a186,0x29189e62618926231886,0x218c262f18b662c18aa6,0x18e663818da63518ce63,0x90a64118fe63e18f263b,0x2e64a192264719166441,0x26531946650193a64d19],#[0x65c196a659195e656195,0x65198e662198265f1976,0xe19b266b19a6668199a6,0x19d667419ca67119be66,0x9fa67d19ee67a19e2677,0x1e6861a126831a066801,0x268f1a3668c1a2a6891a,0x6981a5a6951a4e6921a4,0xa11a7e69e1a7269b1a66,0xa1aa26a71a966a41a8a6,0x1ac66b01aba6ad1aae6a,0xaea6b91ade6b61ad26b3,0xe6c21b026bf1af66bc1,0x26cb1b266c81b1a6c51b,0x6d41b4a6d11b3e6ce1b3,0xdd1b6e6da1b626d71b56,0x61b926e31b866e01b7a6,0x1bb66ec1baa6e91b9e6e,0xbda6f51bce6f21bc26ef,0xfe6fe1bf26fb1be66f81,0x27071c167041c0a7011b,0x7101c3a70d1c2e70a1c2,0x191c5e7161c527131c46,0x21c8271f1c7671c1c6a7,0x1ca67281c9a7251c8e72,0xcca7311cbe72e1cb272b,0xee73a1ce27371cd67341,0x27431d067401cfa73d1c,0x74c1d2a7491d1e7461d1,0x551d4e7521d4274f1d36,0xe1d7275b1d667581d5a7,0x1d967641d8a7611d7e75],#[0xdba76d1dae76a1da2767,0xde7761dd27731dc67701,0x277f1df677c1dea7791d,0x7881e1a7851e0e7821e0,0x911e3e78e1e3278b1e26,0xa1e627971e567941e4a7,0x1e867a01e7a79d1e6e79,0xeaa7a91e9e7a61e927a3,0xce7b21ec27af1eb67ac1,0x27bb1ee67b81eda7b51e,0x7c41f0a7c11efe7be1ef,0xcd1f2e7ca1f227c71f16,0x61f527d31f467d01f3a7,0x1f767dc1f6a7d91f5e7d,0xf9a7e51f8e7e21f827df,0xbe7ee1fb27eb1fa67e81,0x27f71fd67f41fca7f11f,0x8001ffa7fd1fee7fa1fe,0x9201e80620128032006,0x2204280f203680c202a8,0x2066818205a815204e81,0x8a821207e81e207281b,0xae82a20a282720968242,0x283320c683020ba82d20,0x83c20ea83920de83620d,0x45210e842210283f20f6,0xe213284b2126848211a8,0x2156854214a851213e84,0x17a85d216e85a2162857,0x9e866219286321868602,0x286f21b686c21aa86921,0x87821da87521ce87221c],#[0x8121fe87e21f287b21e6,0xa22228872216884220a8,0x2246890223a88d222e88,0x26a899225e8962252893,0x8e8a2228289f227689c2,0x28ab22a68a8229a8a522,0x8b422ca8b122be8ae22b,0xbd22ee8ba22e28b722d6,0x623128c323068c022fa8,0x23368cc232a8c9231e8c,0x35a8d5234e8d223428cf,0x7e8de23728db23668d82,0x28e723968e4238a8e123,0x8f023ba8ed23ae8ea23a,0xf923de8f623d28f323c6,0x224028ff23f68fc23ea8,0x2426908241a905240e90,0x44a911243e90e243290b,0x6e91a246291724569142,0x29232486920247a91d24,0x92c24aa929249e926249,0x3524ce93224c292f24b6,0xe24f293b24e693824da9,0x2516944250a94124fe93,0x53a94d252e94a2522947,0x5e956255295325469502,0x295f257695c256a95925,0x968259a965258e962258,0x7125be96e25b296b25a6,0xa25e297725d697425ca9,0x260698025fa97d25ee97,0x62a989261e9862612983],#[0x4e992264298f263698c2,0x299b2666998265a99526,0x9a4268a9a1267e99e267,0xad26ae9aa26a29a72696,0x626d29b326c69b026ba9,0x26f69bc26ea9b926de9b,0x71a9c5270e9c227029bf,0x3e9ce27329cb27269c82,0x29d727569d4274a9d127,0x9e0277a9dd276e9da276,0xe9279e9e627929e32786,0x227c29ef27b69ec27aa9,0x27e69f827da9f527ce9f,0x80aa0127fe9fe27f29fb,0x2ea0a2822a072816a042,0x2a132846a10283aa0d28,0xa1c286aa19285ea16285,0x25288ea222882a1f2876,0xe28b2a2b28a6a28289aa,0x28d6a3428caa3128bea2,0x8faa3d28eea3a28e2a37,0x1ea462912a432906a402,0x2a4f2936a4c292aa4929,0xa58295aa55294ea52294,0x61297ea5e2972a5b2966,0xa29a2a672996a64298aa,0x29c6a7029baa6d29aea6,0x9eaa7929dea7629d2a73,0xea822a02a7f29f6a7c2,0x2a8b2a26a882a1aa852a,0xa942a4aa912a3ea8e2a3,0x9d2a6ea9a2a62a972a56],#[0x62a92aa32a86aa02a7aa,0x2ab6aac2aaaaa92a9eaa,0xadaab52aceab22ac2aaf,0xfeabe2af2abb2ae6ab82,0x2ac72b16ac42b0aac12a,0xad02b3aacd2b2eaca2b2,0xd92b5ead62b52ad32b46,0x22b82adf2b76adc2b6aa,0x2ba6ae82b9aae52b8eae,0xbcaaf12bbeaee2bb2aeb,0xeeafa2be2af72bd6af42,0x2b032c06b002bfaafd2b,0xb0c2c2ab092c1eb062c1,0x152c4eb122c42b0f2c36,0xe2c72b1b2c66b182c5ab,0x2c96b242c8ab212c7eb1,0xcbab2d2caeb2a2ca2b27,0xdeb362cd2b332cc6b302,0x2b3f2cf6b3c2ceab392c,0xb482d1ab452d0eb422d0,0x512d3eb4e2d32b4b2d26,0xa2d62b572d56b542d4ab,0x2d86b602d7ab5d2d6eb5,0xdaab692d9eb662d92b63,0xceb722dc2b6f2db6b6c2,0x2b7b2de6b782ddab752d,0xb842e0ab812dfeb7e2df,0x8d2e2eb8a2e22b872e16,0x62e52b932e46b902e3ab,0x2e76b9c2e6ab992e5eb9,0xe9aba52e8eba22e82b9f,0xbebae2eb2bab2ea6ba82],#[0x2bb72ed6bb42ecabb12e,0xbc02efabbd2eeebba2ee,0xc92f1ebc62f12bc32f06,0x22f42bcf2f36bcc2f2ab,0x2f66bd82f5abd52f4ebd,0xf8abe12f7ebde2f72bdb,0xaebea2fa2be72f96be42,0x2bf32fc6bf02fbabed2f,0xbfc2feabf92fdebf62fd,0x5300ec023002bff2ff6,0xe3032c0b3026c08301ac,0x3056c14304ac11303ec0,0x7ac1d306ec1a3062c17,0x9ec263092c233086c203,0x2c2f30b6c2c30aac2930,0xc3830dac3530cec3230c,0x4130fec3e30f2c3b30e6,0xa3122c473116c44310ac,0x3146c50313ac4d312ec4,0x16ac59315ec563152c53,0x8ec623182c5f3176c5c3,0x2c6b31a6c68319ac6531,0xc7431cac7131bec6e31b,0x7d31eec7a31e2c7731d6,0x63212c833206c8031fac,0x3236c8c322ac89321ec8,0x25ac95324ec923242c8f,0x7ec9e3272c9b3266c983,0x2ca73296ca4328aca132,0xcb032bacad32aecaa32a,0xb932decb632d2cb332c6,0x23302cbf32f6cbc32eac],#[0x3326cc8331acc5330ecc,0x34acd1333ecce3332ccb,0x6ecda3362cd73356cd43,0x2ce33386ce0337acdd33,0xcec33aace9339ece6339,0xf533cecf233c2cef33b6,0xe33f2cfb33e6cf833dac,0x3416d04340ad0133fecf,0x43ad0d342ed0a3422d07,0x5ed163452d133446d103,0x2d1f3476d1c346ad1934,0xd28349ad25348ed22348,0x3134bed2e34b2d2b34a6,0xa34e2d3734d6d3434cad,0x3506d4034fad3d34eed3,0x52ad49351ed463512d43,0x4ed523542d4f3536d4c3,0x2d5b3566d58355ad5535,0xd64358ad61357ed5e357,0x6d35aed6a35a2d673596,0x635d2d7335c6d7035bad,0x35f6d7c35ead7935ded7,0x61ad85360ed823602d7f,0x3ed8e3632d8b3626d883,0x2d973656d94364ad9136,0xda0367ad9d366ed9a366,0xa9369eda63692da33686,0x236c2daf36b6dac36aad,0x36e6db836dadb536cedb,0x70adc136fedbe36f2dbb,0x2edca3722dc73716dc43,0x2dd33746dd0373adcd37],#[0xddc376add9375edd6375,0xe5378ede23782ddf3776,0xe37b2deb37a6de8379ad,0x37d6df437cadf137bede,0x7fadfd37eedfa37e2df7,0x1ee063812e033806e003,0x2e0f3836e0c382ae0938,0xe18385ae15384ee12384,0x21387ee1e3872e1b3866,0xa38a2e273896e24388ae,0x38c6e3038bae2d38aee2,0x8eae3938dee3638d2e33,0xee423902e3f38f6e3c3,0x2e4b3926e48391ae4539,0xe54394ae51393ee4e393,0x5d396ee5a3962e573956,0x63992e633986e60397ae,0x39b6e6c39aae69399ee6,0x9dae7539cee7239c2e6f,0xfee7e39f2e7b39e6e783,0x2e873a16e843a0ae8139,0xe903a3ae8d3a2ee8a3a2,0x993a5ee963a52e933a46,0x23a82e9f3a76e9c3a6ae,0x3aa6ea83a9aea53a8eea,0xacaeb13abeeae3ab2eab,0xeeeba3ae2eb73ad6eb43,0x2ec33b06ec03afaebd3a,0xecc3b2aec93b1eec63b1,0xd53b4eed23b42ecf3b36,0xe3b72edb3b66ed83b5ae,0x3b96ee43b8aee13b7eed],#[0xbbaeed3baeeea3ba2ee7,0xdeef63bd2ef33bc6ef03,0x2eff3bf6efc3beaef93b,0xf083c1af053c0ef023c0,0x113c3ef0e3c32f0b3c26,0xa3c62f173c56f143c4af,0x50702b17c7af1d3c6ef1,0x1c517c00482b1412f014,0x1c0b83d17c00702b10,0x10b42a11c08042e0ac4f,0x2408c1061243f0063030,0x6b01f00506412f001c10,0x4810f002e0ac5094240,0xc022c1c10248402b0b84,0x161c0ac4098240703087,0x307030c424f001c1024d,0xb01142309c1022c40982,0x91c201c1c08c0d1428a0,0x2b10160438202c071414,0x42bb03810b85e04250b8,0xe060917c5103810a8409,0x580a8170032143208c10,0x2e87038402e01c2b12c,0x1c1c082b093810b8409,0x30901e06a1c100991c2,0xb83092100ac301c2b87,0x1a44050921c0b8384007,0x1e0691006c50901e06c,0x291c10b8240ac3f001b0,0x707c007c00408041a0a0,0x824b08140f81d02470e4,0x10504b0c1c0c430c41c0],#[0x3109c21b1701142708c2,0x8416050071028804310c,0x371431082608dc507040,0x7c004070702006c50c4,0x230c040cc24034311000,0x124461c1d13c0094bf00,0xb0ac405187081401f81,0xb82b0c270942e0c21f01,0x501c2b0c2e0902b0c070,0x1008054707c50d42a0fc,0x82d004d0010ac25d002e,0xac10c8243cc7090fe0f,0x9080901fc00bc40c82b,0x82c5f00182c070ac3092,0x20920b0ac309824087c0,0x5c0e0840c82e08070b8,0x10ac30b8240942b1187d,0xbc4a1c10902e0cc30903,0x9bc3f002f1026f0fc00,0x2709b85e13c0174091c2,0xc02f0ac5f03420bc004,0x60681204184b0050bac0,0xc10181204184b01c0068,0x1c0068409023712c010,0xa0c2509101f001a1410b,0xc00401516840901f001,0xc00402b0c2b061011502,0x10281441c50a10c08202,0x440c20641e0410681714,0x250c0068106410284048,0x406c00c4c040a0702a04,0x703c0b81100402430414],#[0x6c340830ac1002b06030,0xac102]]
set_option maxRecDepth 16000 in
def g127H7 := limbs80 #[#[0x180060840100022000c0,0x11020094e00800300800,0x808800000002008080,0x90401a82111803024a0,0x41fac18ac64af9003,0x38e40f8000000,0xc00041d0000000000000,0x174b06e00062d4973e2,0xa100000000000d3800,0x1ed300000000000,0xe9ba0ff9200019550000,0x61692c6000f4d2d6c000,0xa2199003de0001671954,0x6197c00084d000000200,0xba000b358000000000b3,0xd400000084000000,0x1091d6580000000000,0x1b580000000008528000,0x305ec127340002884000,0x79d5acc00000070b800,0x2118003dba00,0x49000000000000000003,0x29141c00000000005620,0x4a9a84800052a2450003,0x9080003dab,0x0,0x0,0xad6000000000000000,0x64000000110700000000,0x1e041,0x3ccc0000004230,0x20e7c28c26],#[0xf2b8000000000000000,0x20000000000487bd9a00,0x78000000000000000030,0x5a5a220d0007972635c,0x2195c1198c9,0x78dc0000000000000000,0x147d000000000180b000,0xd8001c4506715769c800,0x5a800027ce1,0x311200000000000,0x98acb700000000000000,0x61a5,0xc64e6596816acbe174d9,0xcc67a91211a3455b08a2,0x13aca4c61c00000016d,0x3143aed88f95e40d80,0x3200000002bae0,0x441330fa5814c0000000,0xd5c0000d2000003c001,0x80000005327c5c000000,0x1cfe00070364a85a,0x5b480028a540700,0x1b3ab000000000072800,0x26fb,0x0,0x208171600e8000000000,0xa028f188001717000000,0x1c000000000055,0x0,0xc6000000038e80000,0x2250002cac0000000,0x200a53a],#[0xacca33000,0xf8000000860240f06000,0x21296c3c8,0xa660a8000e2300000,0x6ab0,0x33a80029680000000000,0x163d0f4000000,0x186d114800,0x0,0xdce0000000000fb200,0xa4859da5042a80000000,0x84b0000000001ec10006,0x120000000000010a,0x929c00000018ee000000,0x398,0xbc000d9780000004a700,0x258800000000000030,0x458b5f7210c640000,0x393c0000000000000,0x15d0000000001eaf,0xc9c000000000,0x1893000000140200,0x709c000a8a91e00,0x0,0x43d16d428001d9b0d50,0x1cf7e150000000001,0x10d70000000000000000,0x10000000000743000000,0xc8ebc9328002014000c5,0x6110870d4000f2d80024,0xe2b00078fe863cbf6,0x1a34e660894],#[0xc31800050ea2a,0xf1d000000,0x900000004867c4c00000,0x9508001d0600000040,0xc000000a39ba080000,0x8d8004800293192d0d95,0x1d760000003827,0xcad000000000000036f,0x286b155edae47000162,0xf20000000000000cb800,0x213c4b000000010,0x0,0x96800005460000000000,0x128f000794d97a000,0x653d5ae8000000000322,0x876000000253eab,0x0,0x4b80009b60]]
set_option maxRecDepth 16000 in
def g127D8 := limbs80 #[#[0xe756558510fe12148110,0x9df835d91097f855c910,0xe756558521ed96358130,0xc7d765952197f855cd21,0x97e875952197c8759521,0x97f855d92197d86dd521,0xe756558531ed56358531,0xc7d65dc961e756558541,0xe778159561a7d85d8d61,0x9fb805d943c7d655cb61,0xb77815cd6597d85dc963,0xff13148110a7f865cd65,0xff16148110ff14148110,0xbfb8348110bf98348110,0xdf97648110f796548110,0xff1214c110dfb7648110,0xff1614c110ff1414c110,0xfd9634c110fd9434c110,0xdf9764c110f79654c110,0xff12158110bf9864c110,0xff14158110ff13158110,0xff38158110ff16158110,0xdfb7258110df97258110,0xef96358110bfb8258110,0xdf97358110efb6358110,0xbfb8358110dfb7358110,0xefb6458110ef96458110,0xdfb7458110df97458110,0xfe53248510f796558110,0xbf58348510fe56248510,0xdf57448510bf78348510,0xbf58448510df77448510],#[0xf756548510bf78448510,0xdf57648510f778548510,0xbf58648510df77648510,0xfd5634c510bf78648510,0xf75654c510bf5844c510,0xbf5864c510df5764c510,0xdf77250510df57250510,0xfb56450510fb54350510,0xdf57650510f756550510,0xbf58650510df77650510,0xdf57258510ff38058510,0xbf78258510df77258510,0xef76358510ef56358510,0xdf77358510df57358510,0xdf57458510bf78358510,0xbf78458510df77458510,0xddf734c910f756558510,0xe7d65589109fd874c910,0x9ff87589109fd8758910,0xbf581d8910bf980d8910,0xb7d85d8910e7d65d8910,0xb7f855c9109fd87d8910,0xd7d655c9109ff835c910,0x9ff865c910d7f855c910,0xd7d65dc9109fd84dc910,0xbfb8050d109fd86dc910,0xdbd7450d10ddf7350d10,0x9ff8750d109fd8750d10,0xcfd7658d10ddd7358d10,0x9ff8758d109fd8758d10,0xbf581d8d10bf980d8d10,0xb7d85d8d10ddf73d8d10],#[0x9fd87d8d10cfd76d8d10,0x9fd82dcd10d7d655cd10,0xd7d65dcd109fd84dcd10,0xbfb80591109fd86dcd10,0x9fd8759110dbd7459110,0xbf980d91109ff8759110,0xb7d85d9110bf581d9110,0x9ff825d1109fd87d9110,0xd7d655d1109ff835d110,0x9fd82dd1109ff865d110,0x9fd86dd110d7d65dd110,0xd7d7659510f778159510,0xd7c8759510d7f7659510,0xbfb805d910d7f8759510,0xbdf835d910bf7815d910,0xdf7815d910dfb805d910,0xddc835d9109ff825d910,0x9ff835d910ddf835d910,0xbf9809d9109ff845d910,0xb7d859d910bf5819d910,0x9fd82dd9109fd879d910,0xdfb71581309fd84dd910,0xdfb7258130bfb8158130,0xfd96358130fd94358130,0xef96458130fdb8358130,0xdf97458130efb6458130,0xf796558130dfb7458130,0xb7f8548530df77148530,0xedd6358530f9d4350530,0x9ff8758530e7d6558530,0xedd63d8530bf980d8530,0xe7d65d8530bdd83d8530],#[0x9fd87d8530b7d85d8530,0xddd63dc5309fd82dc530,0xd7d65dc5309fd84dc530,0xe7d65589309fd86dc530,0xbf980d89309ff8758930,0xe7d65d8930bdd83d8930,0x9fd87d8930b7d85d8930,0xddd63dc930ddd43dc930,0xd7d65dc9309fd84dc930,0xfdb8050d309fd86dc930,0xf5d6550d30f9d6450d30,0xddf7650d30ddd7650d30,0xbdf8650d30bdd8650d30,0xddd7458d30fdb8058d30,0xbdf8458d30ddf7458d30,0x9fd8759130f5d6558d30,0xbf980d91309ff8759130,0xb7d85d9130bdd83d9130,0xbfb805d1309fd87d9130,0x9ff815d130dfb805d130,0x9ff865d130d7d655d130,0xd7d65dd1309fd82dd130,0xd7d76595309fd86dd130,0xd7c8759530d7f7659530,0xbfb805d930d7f8759530,0xdfb805d930bdf835d930,0x9ff825d9309ff815d930,0x9ff845d930ddf835d930,0xbdd839d930bf9809d930,0x9fd879d930b7d859d930,0x9fd84dd9309fd82dd930,0x9fe8748560b7f8548560],#[0x9fe874c560edd634c560,0x9fe8750560ebd6450560,0xdf77158560bfb8058560,0xbdf835c560e7d6558560,0xcfd63dc5609fd82dc560,0x9fd83dc560cff63dc560,0xd7d65dc5609fd84dc560,0xafd8650d60edd6350d60,0x9fe8750d609fc8750d60,0xbfb8058d609ff8750d60,0xe7d6558d60ddf7358d60,0xedf7358d60efb8058d60,0xafd84d8d60aff8458d60,0x9fd82dcd609fd81dcd60,0xd7d65dcd609fd84dcd60,0xdf57148760f7b8059560,0x9fd8748760b7f8548760,0xedd634c760df5714c760,0x9fd874c760ddd734c760,0xebd6450760df57150760,0x9fd8750760dbd7450760,0xcfd635c7609ff825c760,0x9ff845c7609ff835c760,0xedd6350f60bfb8050f60,0xd7d7550f60ddd7350f60,0x9fd8750f60afd8650f60,0xaff8458f609ff8750f60,0x9ff825cf609ff815cf60,0xd7f755c1219ff845cf60,0x9fd86dc121df561dc121,0xfe56250521fe53250521,0xfb56450521fb54350521],#[0xbf58650521df57650521,0xfe56258521bf78058521,0xef56358521fe78258521,0xdf57358521ef76358521,0xdf57458521df77358521,0xbf78458521df77458521,0xf777558521f756558521,0xd7f7550d21bf78150d21,0x9ff8750d219fd8750d21,0xddd7358d21bf78158d21,0x9fd8758d21d7f7558d21,0xbf581d8d219ff8758d21,0xd7f75d8d21bed82d8d21,0x9fd80dcd219fd87d8d21,0xd7d76595219fd86dcd21,0xd7e76dd521d7d76dd521,0xd7d80dd521b7d86dd521,0xd7e86dd521d7d86dd521,0x9ff805d921bf7815d921,0x9ff835d921df7815d921,0xbf5819d921d7f855d921,0x9fd80dd9219fd879d921,0xfd56358531bf78058531,0xdf57458531fd78358531,0x9ff8758931f756558531,0xbdd83d8931bf581d8931,0xfd78158d319fd87d8931,0xf5d6558d31ddd7458d31,0x9fd8759131dbd7459131,0xbf581d91319ff8759131,0x9fd87d9131bdd83d9131,0xdf7815d1319ff805d131],#[0xd7d655d1319ff825d131,0xd7d76595319ff865d131,0xdf7815d9319ff805d931,0xddf835d9319ff825d931,0xbf780585419ff845d931,0xfb54358541bf78258541,0xef76358541ef56358541,0xfb78458541fb56458541,0xf9d434c941f756558541,0x9ff8758941ebd6458941,0xebd64d8941bf581d8941,0x9fd87d8941bbd84d8941,0xf9d6350d41fb78150d41,0xdbd7650d41f3d6550d41,0xbbf8650d41bbd8650d41,0xbf581d8d419ff8758d41,0x9fd87d8d41bbd84d8d41,0xbbf8359141fb78159141,0xd7d7659541f3d6559141,0xdf7815d9419ff805d941,0x9ff835d9419ff825d941,0xbdf835c161dbf845d941,0xe7d65dc161e7d655c161,0xcfd63dc1619fd82dc161,0x9fd83dc161cff63dc161,0xd7d65dc1619fd84dc161,0xe7d6558961bf78158961,0xb7f855c961e7d655c961,0x9fd80dc961e7d65dc961,0x9fd84dc9619fd83dc961,0xedd6350d61d7d65dc961,0xe7d6550d61ddf7350d61],#[0x9fe8750d619fc8750d61,0xbf78158d619ff8750d61,0xe7d6558d61ddf7358d61,0xedf7358d61ef78158d61,0xe7d65dcd61e7d655cd61,0x9fd82dcd619fd80dcd61,0xd7d65dcd619fd84dcd61,0xdbf7459161bf78159161,0xe7d655d161e7d6559161,0x9fd80dd161e7d65dd161,0x9fd83dd1619fd82dd161,0xf778159561d7d65dd161,0x9ff825c361e7f8059561,0x9ff835c361cfd635c361,0x9ff805cb619ff845c361,0x9ff845cb619ff835cb61,0xddd7350f61edd6350f61,0xe7d6550f61dbd7450f61,0x9fd8750f61d7d7550f61,0x9ff805cf619ff8750f61,0x9ff845cf619ff825cf61,0x9ff825d3619ff805d361,0xe7f80597619ff835d361,0x9fd81dc143d7f805d761,0xd7d65dc143ddd63dc143,0x9fd80dc5439fd86dc143,0xddd63dc5439fd82dc543,0xd7d65dc543dbd64dc543,0xbdf8058d439fd86dc543,0xf9d6458d43bdf8258d43,0xf5d6558d43f9f8458d43,0xedf7658d43edc7658d43],#[0xd7f7659543d7d7659543,0xd7f8759543d7c8759543,0xbf5811d943bf9801d943,0xcfd761d943b7d851d943,0xbfb805d9439fe871d943,0xcff765d943bdf835d943,0xdfb805d943df8805d943,0x9ff815d9439ff805d943,0xbdd839d943ddf835d943,0xcff769d943b7d859d943,0x9fd80dd9439fd879d943,0x9fd81dc1639fd81dd943,0x9fd84dc1639fd82dc163,0x9fd80dc563d7d65dc163,0x9fd84dc5639fd82dc563,0xb7d85dc963d7d65dc563,0x9fd81dc9639fd80dc963,0xd7d65dc9639fd84dc963,0xbdf8359163d7d85dc963,0xaff865d163bfb805d163,0x9fd81dd1639fd80dd163,0xd7d65dd1639fd82dd163,0x9ff815c363f5f8359563,0x9ff845c3639ff825c363,0x9ff825c7639ff805c763,0x9ff805cb639ff845c763,0x9ff845cb639ff815cb63,0x9ff815d3639ff805d363,0xd7f805d7639ff825d363,0xd7d73dc165b7d81dc165,0xb7d83dc165d7f73dc165,0xb7f805cd65b7f805c565],#[0xd7f74dcd65b7f865cd65,0xff96348110ff94348110,0xff97648110ffb6348110,0xff9424c110ffa7648110,0xff93258110ff9624c110,0xff96258110ff94258110,0xff54348510ff98258110,0xff76348510ff56348510,0xff76448510ff56448510,0xff67648510ff57648510,0xff68648510ff58648510,0xff5624c510ff5424c510,0xff56250510ff53250510,0xff54258510ff53258510,0xfed624c910ff56258510,0xfdd634c910fdd434c910,0xfed6250910dfd744c910,0xdff7650910fbd6450910,0xeff6458910efd6458910,0xbfd82d8d10f7d6558910,0xbff825d910bfd82d9110,0xff92158130bfd829d910,0xff56148530ff54148530,0xfdd4348530fed6248530,0xf7f8459530fdd6348530,0xff56148560ff54148560,0xefd6348560ff57148560,0xf7d6548560eff6348560,0xdfd725c560f7f8548560,0xff54358521ff56350521,0xfdd6350d21bff8050d21,0xbfd80d8d21bff8650d21],#[0xbfd809d921bff805d921,0xfdd6350931ff54258531,0xff53258541efd6458931,0xfbd4358941fdd634c941,0xff98348110f7f8059543,0xff9644c110ffb624c110,0xff97258110ffb644c110,0xff94358110ffb8258110,0xff98358110ff96358110,0xff96458110ffb8358110,0xff98458110ff97458110,0xff57448510ffb8458110,0xff5644c510ff7624c510,0xff76250510ff7644c510,0xff56350510ff57250510,0xff57650510ff76350510,0xff57258510ff67650510,0xff78258510ff58258510,0xff56358510ff54358510,0xff78358510ff58358510,0xff57458510ff56458510,0xff78458510ff58458510,0xdfd764c910bfd844c910,0xdfd7350910bfd864c910,0xdfd7650910dff7350910,0xbfd8750910bfd8650910,0xff58158910ff98058910,0xdfd7358910fed7258910,0xbff8358910dff7358910,0xdff7458910dfd7458910,0xdfd7658910bff8458910,0xdfd8758910dff7658910],#[0xdfe8758910bfd8758910,0xdfd73d8910bff8758910,0xbfd83d8910dff73d8910,0xdfd74d8910efd64d8910,0xbfd84d8910dff74d8910,0xdfd745c910bfd87d8910,0xf7d655c910bff845c910,0xdfd765c910f7f855c910,0xbff865c910dfe765c910,0xdfd635c910dfd435c910,0xdfd835c910dff635c910,0xdfc865c910dff835c910,0xdfe865c910dfd865c910,0xdfd64dc910dff865c910,0xff58150d10dff64dc910,0xfdd6350d10bff8250d10,0xf7d6550d10fbd6450d10,0xbfd8650d10dfd7650d10,0xdfd8750d10bff8650d10,0xff58158d10ff98058d10,0xdfd7458d10bff8258d10,0xf7d6558d10bff8458d10,0xdfd8758d10dfd7658d10,0xbfd84d8d10dfd74d8d10,0xdff645cd10dfd645cd10,0xdff64dcd10dfd64dcd10,0xff58159110ffb8059110,0xbff8359110bff8259110,0xf7d6559110fbd7459110,0xdff7659110dfd7659110,0xbfd8759110dfd8759110,0xbff8759110dfe8759110],#[0xbfd87d9110bfd83d9110,0xdfd765d110f7d655d110,0xdfd825d110dfe765d110,0xdfd865d110dfd835d110,0xf7d7659510dfe865d110,0xffb805d910f7f8759510,0xfdf835d910ff7815d910,0xdfd825d910bff845d910,0xdfd835d910dff825d910,0xdfd845d910dff835d910,0xbfd849d910dff845d910,0xff96158130ff94158130,0xff94258130ff98158130,0xff97258130ff96258130,0xff96458130ff98258130,0xff98458130ff97458130,0xbfd8448530dfd7448530,0xbfd8648530dfd7648530,0xfdd6350530ff56150530,0xf7d6550530fbd6450530,0xbfd8650530dfd7650530,0xbff8258530ff98058530,0xfdd6358530fdd4358530,0xbff8458530dfd7458530,0xdfd7658530f7d6558530,0xbfd82d8530dfd8758530,0xdfd74d8530fdd43d8530,0xdfd42dc530bfd84d8530,0xdfd64dc530dfd62dc530,0xfdd6350930fed6250930,0xf7d6550930fbd6450930,0xdff7650930dfd7650930],#[0xbfd8750930bfd8650930,0xfed7258930bff8158930,0xfdd6358930fdd4358930,0xeff6458930efd6458930,0xbff8458930dff7458930,0xdfd7658930f7d6558930,0xdfd8758930dff7658930,0xdfe8758930bfd8758930,0xbfd81d8930bff8758930,0xefd64d8930fdd43d8930,0xfdd435c930bfd84d8930,0xdfd745c930fdd635c930,0xdfd765c930f7d655c930,0xdfd64dc930dfe765c930,0xfdf8150d30fdd8150d30,0xfdf8250d30fdd8250d30,0xfde7650d30fdd7650d30,0xfdd8650d30fdc8650d30,0xfdf8650d30fde8650d30,0xfdd8258d30fdd8158d30,0xfdd7458d30fdd6458d30,0xbff8159130fdd8458d30,0xfdd8359130bff8259130,0xf7d6559130fbd7459130,0xdff7659130dfd7659130,0xbfd8759130dfd8759130,0xbff8759130dfe8759130,0xbfd82d9130bfd81d9130,0xbff825d130ffb805d130,0xdfd765d130f7d655d130,0xbff865d130dfe765d130,0xdff815d130dfd815d130],#[0xdfd865d130dfc865d130,0xdff865d130dfe865d130,0xdfd815d930f7f8759530,0xdfd845d930dfd825d930,0xbfd849d930bfd829d930,0xdff7348560ff98048560,0xbff8348560bfd8348560,0xbff8648560bfd8648560,0xbfd8748560dfd8748560,0xbff8748560dfe8748560,0xff5714c560ff5614c560,0xfdd634c560dff724c560,0xeff644c560efd644c560,0xbfd844c560dff744c560,0xbfd864c560f7d654c560,0xff56150560bfd874c560,0xdff7250560ff57150560,0xefd6350560fbd4350560,0xdff7350560eff6350560,0xf7d6550560fbd6450560,0xbfd8750560bfd8650560,0xbff8258560dff7258560,0xdff7358560efd6358560,0xefd6458560bff8358560,0xbff8458560dff7458560,0xdff725c560ffb805c560,0xefd635c560bff825c560,0xdfd735c560eff635c560,0xfdc835c560dff735c560,0xbff835c560fdf835c560,0xeff645c560efd645c560,0xdff745c560dfd745c560],#[0xf7d655c560bff845c560,0xdfd82dc560bfd82dc560,0xff98050d60dfd43dc560,0xfdd6350d60bff8150d60,0xf7d6550d60fdd7350d60,0xbfd8650d60efd8650d60,0xbff8650d60efe8650d60,0xbfd8750d60dfd8750d60,0xbff8750d60dfe8750d60,0xefd8158d60efd6458d60,0xefd7458d60efd8258d60,0xdfd745cd60efd8458d60,0xbfd82dcd60bfd81dcd60,0xdfd82dcd60dfd81dcd60,0xf7f8159560f7d8159560,0xf7f8359560f7d8359560,0xefd6348760ff54148760,0xbfd8348760dfd7348760,0xf7f8548760bff8348760,0xdfd724c760dfd8748760,0xdfd744c760efd644c760,0xdfd7250760bfd844c760,0xefd6350760fbd4350760,0xdfd825c760dfd7350760,0xdfd845c760dfd435c760,0xbff8150f60ffb8050f60,0xdfd8750f60efd8650f60,0xefd8458f60efd8258f60,0xdfd845cf60dfd825cf60,0xdfd765c121ff5615c121,0xbff865c121dfe765c121,0xff58058521ff76350521],#[0xff56358521ff78058521,0xff78358521ff58358521,0xff58458521ff56458521,0xdfd7650d21ff78458521,0xdfd8750d21bfd8650d21,0xff78158d21bff8058d21,0xdfd7458d21fed8258d21,0xdfd7658d21bff8458d21,0xdfd74d8d21dfd8758d21,0xff7815d921bfd84d8d21,0xdff805d921dfd805d921,0xdff835d921dfd835d921,0xff56258531ff58058531,0xff56458531ff58258531,0xdfd7650931ff58458531,0xfdd6358931bff8058931,0xdfd7458931eff6458931,0xdfd7658931bff8458931,0xbfd80d8931dfd8758931,0xdfd74d8931efd64d8931,0xfdd8058d31bfd84d8931,0xfdd6458d31fdd8258d31,0xbff8059131fdd8458d31,0xf7d6559131bff8259131,0xdfd8759131dfd7659131,0xbfd82d9131bfd80d9131,0xdfd825d131dfd805d131,0xdfe865d131dfd865d131,0xdfd825d931dfd805d931,0xff58058541dfd845d931,0xff56258541ff78058541,0xff78258541ff58258541],#[0xff58358541ff56358541,0xdfd764c941ff78358541,0xff58158941bff8058941,0xfbd6458941bff8358941,0xdfd8758941dfd7658941,0xfbd43d8941bfd80d8941,0xfbd8050d41bfd83d8941,0xfbd8650d41fbd8250d41,0xbff8058d41fbe8650d41,0xfbd6458d41bff8258d41,0xf7d6558d41fbd8458d41,0xdfd8758d41dfd7658d41,0xbfd82d8d41bfd80d8d41,0xfbf8059141fbd8059141,0xfbf8259141fbd8259141,0xfbf8359141fbd8359141,0xdff805d941dfd805d941,0xdff825d941dfd825d941,0xdff835d941dfd835d941,0xdfd725c161ff7815c161,0xbff825c161dff725c161,0xeff635c161efd635c161,0xdff735c161dfd735c161,0xfdf835c161fdc835c161,0xdfd745c161bff835c161,0xbff845c161dff745c161,0xdfd72dc161f7d655c161,0xdfd74dc161bfd82dc161,0xdfd62dc161bfd84dc161,0xdfd43dc161dfd82dc161,0xdfd84dc161dfd64dc161,0xdff7358961efd6358961],#[0xbff805c961bff8358961,0xefd635c961ff7815c961,0xdfd735c961eff635c961,0xbff835c961dff735c961,0xdff745c961dfd745c961,0xf7d655c961bff845c961,0xbfd80dc961f7f855c961,0xbfd84dc961dfd74dc961,0xdfd43dc961dfd80dc961,0xdfd84dc961dfd64dc961,0xff58150d61bff8050d61,0xfdd6350d61bff8250d61,0xfbd6450d61fdf7350d61,0xf7d6550d61fbd7450d61,0xbff8650d61bfd8650d61,0xbfd8750d61dfd8750d61,0xbff8750d61dfe8750d61,0xefd8058d61efd6458d61,0xefd7458d61efd8258d61,0xefd74d8d61efd8458d61,0xbfd80dcd61dfd745cd61,0xdfd74dcd61bfd82dcd61,0xdfd80dcd61bfd84dcd61,0xdfd64dcd61dfd82dcd61,0xbff8059161dfd84dcd61,0xbff8359161bff8259161,0xff7815d161bff805d161,0xbff835d161bff825d161,0xbfd80dd161f7d655d161,0xdfd80dd161bfd82dd161,0xdfd825c361dfd82dd161,0xdfd805cb61dfd435c361],#[0xdfd835cb61dfd435cb61,0xbff8250f61bff8050f61,0xefd8258f61dfd8750f61,0xdfd825cf61efd8458f61,0xdfd835d361dfd845cf61,0xdff715c143dfd715c143,0xfdd635c143bff815c143,0xdfc765c143f7d655c143,0xdfe765c143dfd765c143,0xbff865c143dff765c143,0xf7d65dc143fdd63dc143,0xdfe76dc143dfd76dc143,0xdfd86dc143bfd86dc143,0xdfd725c543dfe86dc143,0xfbd645c543fdd635c543,0xdfd765c543f7d655c543,0xbfd80dc543dfe765c543,0xfbd64dc543fdd63dc543,0xdfd76dc543f7d65dc543,0xbfd86dc543dfe76dc543,0xdfd86dc543dfd80dc543,0xfdd8058d43dfe86dc543,0xfdd8158d43fdf8058d43,0xfdd8258d43fdf8158d43,0xfdf7658d43fdf8258d43,0xf7f7659543f7d7659543,0xf7f8759543f7c8759543,0xff8805d943bfd801d943,0xbff805d943ffb805d943,0xfdf835d943bff815d943,0xdfd805d943dff765d943,0xdfd815d943dff805d943],#[0xbfd809d943dff815d943,0xbfd879d943bfd819d943,0xdfd80dd943bfd80dd943,0xdfd725c163dfd715c163,0xdfd72dc163dfd745c163,0xdfd74dc163bfd82dc163,0xdfd82dc163bfd84dc163,0xdfd84dc163dfd64dc163,0xdfd745c563dfd725c563,0xbfd82dc563dfd72dc563,0xbfd84dc563dfd74dc563,0xdfd64dc563dfd82dc563,0xbff805c963dfd84dc563,0xfdf835c963bff815c963,0xdff745c963dfd745c963,0xf7d655c963bff845c963,0xbfd84dc963dfd74dc963,0xdfd84dc963dfd64dc963,0xffb805d163ff8805d163,0xbff815d163bff805d163,0xfdf835d163bff825d163,0xeff865d163f7d655d163,0xbfd82dd163bff865d163,0xf7f8059563dfd82dd163,0xdfd815c363f7f8459563,0xdfd805c763dfd825c363,0xdfd845c763dfd825c763,0xdfd815cb63dfd805cb63,0xf7d83dc165dfd815d363,0xe700a2006f003c0000,0x1e601b301890156012c,0x31b02e802a302670222],#[0x41a03e703ab036f0345,0x52b04f804ce04890456,0x63305f705cd05910555,0x70e06e406c30699066f,0x7fb07bf0795076b074a,0x8f108c70894086a0837,0x9f009c6099c09600936,0xb010abc0a800a440a11,0xc2d0be80bbe0b700b46,0xcf60cd50cb40c780c57,0xe070dd40d8f0d5c0d29,0xef40eca0ea00e760e43,0xfe10fb70f960f630f30,0x10bc10921071103e1014,0x11c411911155112b10e6,0x12c31287124b121811f7,0x13ef13b31380132012ed,0x150914cd1491145e1422,0x161a15e715bd15661533,0x173d171316e0169b165f,0x187b182417d617911767,0x19b01974192618d818b7,0x1a8b1a581a2e1a1619e3,0x1bae1b7b1b481b151ae2,0x1ce31ca71c591c1d1bea,0x1e0f1dd31d7c1d491d16,0x1f051edb1eb11e871e42,0x203120071fcb1f6b1f2f,0x210c20eb20a62085205b,0x2265221721d2217b2136,0x23882343231022dd22aa,0x24512427240f23ee23bb],#[0x2547251d24e124c9248d,0x263d260a25e025b6258c,0x2733270926cd269a2670,0x27f327c02796276c2754,0x28d728a42883283e2826,0x29a929882967293d290a,0x2a8d2a5a2a392a0629d3,0x2ba72b622b142aea2ab7,0x2caf2c8e2c5b2c1f2bec,0x2d782d452d1b2d0c2ceb,0x2e532e202ded2dd52dab,0x2f912f552eec2ea72e74,0x30ab306f303c30092fc4,0x3174314a312930ff30d5,0x3258322e320431d131a7,0x3333330932d632a33270,0x344d341a33e733b43378,0x3579352b34dd34aa3480,0x36663633360035df35c7,0x37e337a7373e36f036ab,0x38d0389d38733840380d,0x39fc39ae3960392438fa,0x3b1f3ada3a953a743a2f,0x3c4b3c183be53bb23b7f,0x3d653d323cdb3ca83c75,0x3e883e3a3e103ddd3da1,0x3fc63f933f3c3f003ecd,0x40ce4092405f40233fe7,0x41a04176414c412b4101,0x429f425a420c41e241c1,0x43714347431d42f342c9,0x4431441043dd43bc4392],#[0x4539451844dc448e4452,0x4638460e45d2459f4563,0x4740471646e3469e4662,0x4851480c47d947af4785,0x4962494148fc48db4896,0x4a464a1c49e049b6498c,0x4b334b004acd4aac4a67,0x4c054be44bb14b7e4b66,0x4d0d4cd14c8c4c594c38,0x4de84dc74d944d614d37,0x4ed54ea24e784e4e4e1b,0x4f8c4f6b4f414f204ef6,0x50675046500a4fd74fa4,0x515d512150ee50bb5088,0x525c523b51e451b1517e,0x532e531652e352b0528f,0x543f541553c753945361,0x5523550254bd54815460,0x5658560155b3559b5556,0x5760572d570356e25694,0x588c5850580b57e157ae,0x59a65973594958fb58c8,0x5ac95a8d5a515a1559d0,0x5b9b5b715b595b385b05,0x5c915c435c105be65bc5,0x5d875d665d335d095cc4,0x5ea15e6e5e205df65dc3,0x5fa95f765f315ef55ed4,0x60b1607e604b60185fe5,0x61d461aa616e613260ed,0x630962cd6291625e6207,0x641a63de63ab636f633c],#[0x6573652564ce6492645f,0x668d665a662765f465c1,0x67d467a16765672066d2,0x692468d66876684c6822,0x6a1a69e769b469816957,0x6b2b6b0a6ace6a896a56,0x6c696c486c036bb56b79,0x6d9e6d596d0b6ce16cae,0x6ee56ea06e526e046dd1,0x6fe46fba6f996f4b6f18,0x70e370b9708f70417017,0x71e271af717c7152710d,0x72fc72c9729672757230,0x741f73ec73b073747338,0x753074fd74c1748e7452,0x764a760575e475a87575,0x7737770d76e376b97674,0x781277e877c7779d7761,0x78d278967875784b782a,0x79da79a7797479387905,0x7aac7a827a617a377a0d,0x7b517b277afd7ae57ac4,0x7c087bde7bab7b817b72,0x7c777c5f7c477c267c17,0x7d137d047ce37ccb7caa,0x7d9d7d7c7d6d7d557d34,0x7e4b7e217e097ddf7dbe,0x7f0b7ed87eb77e967e75,0x7fd47faa7f897f567f35,0x806780468037801f7ff5,0x811e80f480dc80b28091,0x813c81368130812a8124],#[0x815a8154814e81488142,0x81788172816c81668160,0x81968190818a8184817e,0x81b481ae81a881a2819c,0x81d281cc81c681c081ba,0x81f081ea81e481de81d8,0x820e8208820281fc81f6,0x822c82268220821a8214,0x824a8244823e82388232,0x82688262825c82568250,0x82868280827a8274826e,0x82a4829e82988292828c,0x82c282bc82b682b082aa,0x82e082da82d482ce82c8,0x82fe82f882f282ec82e6,0x831c83168310830a8304,0x833a8334832e83288322,0x83588352834c83468340,0x83768370836a8364835e,0x8394838e83888382837c,0x83b283ac83a683a0839a,0x83d083ca83c483be83b8,0x83ee83e883e283dc83d6,0x840c8406840083fa83f4,0x842a8424841e84188412,0x84488442843c84368430,0x84668460845a8454844e,0x8484847e84788472846c,0x84a2849c84968490848a,0x84c084ba84b484ae84a8,0x84de84d884d284cc84c6,0x84fc84f684f084ea84e4],#[0x851a8514850e85088502,0x85388532852c85268520,0x85568550854a8544853e,0x8574856e85688562855c,0x8592858c85868580857a,0x85b085aa85a4859e8598,0x85ce85c885c285bc85b6,0x85ec85e685e085da85d4,0x860a860485fe85f885f2,0x86288622861c86168610,0x86468640863a8634862e,0x8664865e86588652864c,0x8682867c86768670866a,0x86a0869a8694868e8688,0x86be86b886b286ac86a6,0x86dc86d686d086ca86c4,0x86fa86f486ee86e886e2,0x87188712870c87068700,0x87368730872a8724871e,0x8754874e87488742873c,0x8772876c87668760875a,0x8790878a8784877e8778,0x87ae87a887a2879c8796,0x87cc87c687c087ba87b4,0x87ea87e487de87d887d2,0x8808880287fc87f687f0,0x88268820881a8814880e,0x8844883e88388832882c,0x8862885c88568850884a,0x8880887a8874886e8868,0x889e88988892888c8886,0x88bc88b688b088aa88a4],#[0x88da88d488ce88c888c2,0x88f888f288ec88e688e0,0x89168910890a890488fe,0x8934892e89288922891c,0x8952894c89468940893a,0x8970896a8964895e8958,0x898e89888982897c8976,0x89ac89a689a0899a8994,0x89ca89c489be89b889b2,0x89e889e289dc89d689d0,0x8a068a0089fa89f489ee,0x8a248a1e8a188a128a0c,0x8a428a3c8a368a308a2a,0x8a608a5a8a548a4e8a48,0x8a7e8a788a728a6c8a66,0x8a9c8a968a908a8a8a84,0x8aba8ab48aae8aa88aa2,0x8ad88ad28acc8ac68ac0,0x8af68af08aea8ae48ade,0x8b148b0e8b088b028afc,0x8b328b2c8b268b208b1a,0x8b508b4a8b448b3e8b38,0x8b6e8b688b628b5c8b56,0x8b8c8b868b808b7a8b74,0x8baa8ba48b9e8b988b92,0x8bc88bc28bbc8bb68bb0,0x8be68be08bda8bd48bce,0x8c048bfe8bf88bf28bec,0x8c228c1c8c168c108c0a,0x8c408c3a8c348c2e8c28,0x8c5e8c588c528c4c8c46,0x8c7c8c768c708c6a8c64],#[0x8c9a8c948c8e8c888c82,0x8cb88cb28cac8ca68ca0,0x8cd68cd08cca8cc48cbe,0x8cf48cee8ce88ce28cdc,0x8d128d0c8d068d008cfa,0x8d308d2a8d248d1e8d18,0x8d4e8d488d428d3c8d36,0x8d6c8d668d608d5a8d54,0x8d8a8d848d7e8d788d72,0x8da88da28d9c8d968d90,0x8dc68dc08dba8db48dae,0x8de48dde8dd88dd28dcc,0x8e028dfc8df68df08dea,0x8e208e1a8e148e0e8e08,0x8e3e8e388e328e2c8e26,0x8e5c8e568e508e4a8e44,0x8e7a8e748e6e8e688e62,0x8e988e928e8c8e868e80,0x8eb68eb08eaa8ea48e9e,0x8ed48ece8ec88ec28ebc,0x8ef28eec8ee68ee08eda,0x8f108f0a8f048efe8ef8,0x8f2e8f288f228f1c8f16,0x8f4c8f468f408f3a8f34,0x8f6a8f648f5e8f588f52,0x8f888f828f7c8f768f70,0x8fa68fa08f9a8f948f8e,0x8fc48fbe8fb88fb28fac,0x8fe28fdc8fd68fd08fca,0x90008ffa8ff48fee8fe8,0x901e90189012900c9006,0x903c90369030902a9024],#[0x905a9054904e90489042,0x90789072906c90669060,0x90969090908a9084907e,0x90b490ae90a890a2909c,0x90d290cc90c690c090ba,0x90f090ea90e490de90d8,0x910e9108910290fc90f6,0x912c91269120911a9114,0xc0100ac6913e91389132,0x8ac8f1c430b851740439,0xb03c01e87820ae04262,0xc30e700623c428fc5e1e,0x5140fc1170ac48081f8b,0x6802e1589c1a260f041,0xf04131a8fc1000b4542f,0x5e270707821e8fc10ae0,0x1f83830ae082630218fc,0xc503f1787c119700123d,0x7e27045c201c65c5e08a,0xf510343093822b17080,0x783400f0683630900fc1,0x9c0184a07e08b85628d,0x7d0c6215168fc3e1617,0x30f80e08568811078e17,0x81450e0ac50a8442e0f1,0x7c0080dc0080805c204b,0x97008a1c158c24095168,0x8b856307380201588290,0x84c170286344a20c080,0x1c158812a1f003820902,0x5e00704e022c381f1780,0xc43c3817018a1c18494],#[0xe09456047056209b801c,0x8a14a27030430c449c00,0x2288c33c561f002030c4,0x1f00208b104745e00411,0xf0062251603c00811c51,0x41a61e082007e00e1019,0xc3e060866188f801c102,0xc108fc01887041191420,0x80a07e0070311f008e1,0x620c4e0608611d1f80c4,0x723f002033c131461191,0x160e230805b81826291c,0x18a1c102c10c13178007,0x600a28b01c111c811f0,0xc08687e0714382b10471,0x7801c158825086138bc0,0x5884c08b86e00705c1f1,0x1811707c00e0b8308700,0x2e158a10e0317022b178,0xc408181168a858830302,0x70511f142084c0f02863,0x1aa1f030230678b43e00,0xc1021c015e045c28978a,0x105e0be0070413717801,0xc2181e04246e2b02382b,0x5c2f1465c004e0451908,0x82700382e0c2410c0f00,0x38438181058a2f05f003,0x607810b1620c0c08b841,0x178113810b0e062308,0xfc01d8a10e00c8413f,0x31270038206824c3c084],#[0xe0bc51230c21c0c08cc,0x38bc023870523f1465c0,0x8fc062040503f0038189,0x637144910e0313023092,0x2f00382043022c03f001,0x91ca810418bc0c08a246,0x1244389c3147141ec0c0,0x2f0056351f8bc0480ac5,0x8e25c08b85628a438070,0x34141143c101409c018,0x2d0f8182238c04c16078,0x89c51250f8181238c232,0x21ea191c362e045c4715,0x181702470260b8143270,0xe0456287a861b8808241,0x1816001c5c2b1f800702,0x3c4a2181600b856344a2,0xb05040140981a1e0b80,0x807604705c201f801c17,0x87e00705e201687c00e0,0x4205e44e1d1f8145480f,0x709178585883c0f00174,0x30e45e2c045140e03e00,0x1c38181c0b82c0f0060,0x4310811f8181c15108e0,0xd0c862080280c39c0206,0x870501f170581e009861,0x9c5e011c38288c8bc023,0x50f11c351c112147084,0x7c170288489047c02387,0x571c1448230280f024,0x50801c0bc0158a0782b],#[0x63c4056281c07c0a20b,0x158e0501f0021441a0ac,0x1607c08c81c27028b82,0xc01e0b0204e01016e00b,0x200982c0f006830ce8a2,0x30247144745e06088e28,0x9c086e8a470d0a24a2f0,0x904603238130581e0514,0x5828e00e04e00b05c30,0x16001e082e1c0e036270,0x17080401f0058245a218,0xe0807604705c27000e1c,0x3d400d60436300e8bc00,0x42a0d0981a011f045240,0x10a8323d013830904690,0x361a14081e0d86850202,0x1c198645e0070482078,0x1f0f0581a3f1781101f8,0x31c6610600c440870064,0x18848400a04c0e0b80c,0xc01c6431887178781c17,0xf0188471787106260705,0x3c0628e10a3f178782c0,0x3917801c142004e1e0b0,0x4405e2a088fc00e0a812,0x20501f0038387836470d,0x28200ac3e0070523e0b0,0x20184310c0a030e70058,0xa0cc340070622308621,0x80fc0188dc31188780c5,0x6233628c141985c5e1f0,0xe381f00c5188814c0610],#[0x28c441085829c062e100,0xac4143000e3111001c6,0xb87c2d0c271c178bc04a,0x3119070417d0f804b0e0,0x1120c2423e16382b1780,0x8f00470e080501e13818,0x3c7040e0c421311c3818,0xc45c28748f1c130a2b2,0xe05e00ac52281407c0a1,0x701f0029421e8431080,0xa10c45828c45618bd8a,0x148e25c2e0456281407c,0x28780188984016078034,0x8985158c43a180462181,0xa0301700622e16861b18,0x1c188630a1f018a1c140,0xd1888c503f02861c1686,0x100b43e0070622c16381,0x88a14e06048178538030,0x26004f03451e082761e0,0xc50414c0f028a3c53878,0x70230878745e00705e18,0x10d170228c44f04e051,0xa6040e301064310c29c,0x20c4162870621b178016,0x8c40602e00a2880b0062,0x1462200b09c0c08d0519,0x68a470d8a01188404c05,0x3818140602e00c45c087,0x438582830e00bc5e00c0,0xa0b0380e8b84c0f018,0x68a01c1145c240e05816],#[0x148a03016068b84e00d1,0x606c08e0c47038728bc0,0x5018728bc0188a280451,0xa011d3832150682a00c4,0x408850e86c50202107c5,0x7c5e00983822143a1b1,0xc451971780311380330e,0x50170062201406c2e00,0x3e00c441985385c0188a,0xe0c4240f008e1c1005c,0x70622f143a1b23c505,0x80501f003829140a03e,0xb84a1d0b02380d8bc00e,0x450e8433e00c460461f0,0x700662f006431c092450,0xa87e00cf024b168803a1,0x81e00c84a280e85c0188,0x2c090331210b80311446,0xb0241004785c260c6b4,0xc0a111106261f8bc3e05,0xd0862108c25810281187,0x1407c0a10c45a1310461,0xe84311c0803e05086628,0x118d170238360701600c,0x1f8145a2604843f0f802,0x118700462f2c663110a,0x7004630200e050200c04,0xb87187005e251689c3e1,0x42e00cc51961403c0188,0x2188a802040462209889,0x100fc0198c4403805803,0xe882362e046628078031],#[0xc081406c2e05108e009,0x48058102b0f814420461,0x866380e89c2e00cc5118,0x6408d430bc0e02c0a270,0x1f8a24426078143438e3,0x30256170808a1d0b0387,0x894480802812874243f0,0x50e49144981e021c922,0x85136078087248a260a6,0x4e021c96201407c0c08c,0x4392c51385b0287258a2,0x74243f0302489f03c0,0x561e078032144e24a281,0x120dc01209b02c4a10c0,0xf8181190a0501b138181,0x287230145a261c46280,0xa2a1c71308787c00a517,0x702870d8bc31320b8181,0x91389a8b4443e046a287,0x9c4d45a200c0487e0604,0x702260d0e30e06045e28,0x64301406c2c0f004c331,0xe06046428200ac3c0f00,0x62510a39185a2a198a03,0x822e158941e008c5c2b1,0xb44e00b84e042c561f02,0x27e00b83e00bc162b104,0x813f00882e104bc01706,0x1c49c50911204c1e060c,0x86427058b44817003447,0x56211f8a321588c5e006,0xc27178007158824e291c],#[0x2b1380071707c0123105,0x7158bc0220b83e00918a,0x158747168a83127045c4,0x28f41a2e0f04131b8030,0x6180bc5a07a2807802b2,0xe00ac30381403c015884,0x1e0826371780071589c5,0x640500f00562d1e8b41c,0xe2b101005c1e0b803118,0x47184a45238ac4127148,0x807802b1e8b41c1e0827,0x3c003d105c2894484702,0xc1170ac7e0006882e118,0x501822d1508251211e81,0x1e802d150ac1168a98e2,0x83c131d8215a004c7e0b,0x71f078263f042b40098f,0x94561e0f04c10a90026c,0x19028130782e03047170,0x4e0017822b1035c01a06,0x410b88e2b1382c0170ac,0x70ac4c1e0803c0170ac6,0xf00643b0780320d83c01,0xa24e00243e2f0c05c103,0xc1158c85058bc0fc0048,0xb0b098200f0068281f8b,0x190a26a1f008e8914642,0x48bc0048c430280687c0,0x8a26238ac3628bc0fc00,0xe0300f007c20bf800705,0x260869c0198d84c10c85,0x11d12251409c0190808c],#[0xbc50280c03c0190a26e0,0xc5187005e181c06c1e00,0xb03c0456281c03c0178a,0x158c8401807802f11810,0x90603e2b078032150a81,0xc830280456321063c01,0x216180c03c01909c100,0x42c4e002c5e00b8260f,0x8f0b188e32e031216289,0x41f008e0b0c481ee0024,0x289389c1238b8505f006,0x702868b14602fe022c56,0x604c10070bc0128c471a,0x27e00308e8b144847170,0x7e050c913d0f8047458a,0x60189c498502608024,0xc561e0c4c2fe042c505f,0x16289107c005d1056042,0x3117802f084c2fa2702,0x25138047458b8501e0b8,0x70288409e89c023a2c51,0x80b1988271200c0247c1,0x27238b8362702161f006,0x608e271211d0881170c,0xd016330c1603c2f1305c,0x780c41c77c0020045c28,0x4402c64102f0a03c170,0xa093106261f8bc3a0f03,0x862421c4945a1d118182,0x2e050481a81e8b43230c,0x282320c481902811878,0xf8141190b41e03104827],#[0xb628100782e050480280,0x1a0905818d6823214480,0xf81a08b856389105c0,0x64389181c1170ac61289,0x120ac56061f821ea186c,0x408c1c170286401f822e,0x5c2814022b1908240801,0xe08ac482e1049c002004,0x28c87e18878032a2e087,0x8345158c44e1d078182a,0x20078030120c87c1092,0x80b45a200c03c0120c07,0x431e00c8302e0803c01,0x642516823215894119,0x45632100fc019060718f,0x88401e8bc1120ac5a2d0,0x158a24086080a0360f02,0xf0401e051071201403c0,0x662c17822415880b1200,0xc309c8a320c682441700,0x25045c289c4807a25045,0x514803d04642e110e24a,0x22e1420240200f04c1e0,0x18068bc0190bc0120100,0x78341b1a8d01190b830,0x2860d003c1b0d0fc1a0,0xc4a08cc318e0b8033152,0xf8182198bc01189b04,0x682b1705c3e00c4562,0xc400f0304341408c1c17,0x9438e0462e0b81c1128c,0xa8a87184c21e1d17800],#[0x83e060a88871b8626e06,0x2438745a0d150e2b104e,0xd0f4400f03044d068b8,0x143f030430144e26a28,0x188c03e2e0983c0130c,0xf05c0188a0802b0f05c,0x66330781c4c10d05628,0x4e06086628dc08c3c170,0x1e1ac10f06e0e1a19883,0x45e2e0a0ec1088568013,0x638870b41180e03e050,0x220702600a30b412447c,0x21c280c05c0a090c7c20,0x80d8385c270284431f08,0x85038078030158a2103,0x24c270284289043c0c2d,0xa10ec003c070a2b150a,0x78185204385c200c03c,0xc3e061471370c2d04213,0x21609c0238c150641084,0x1c842b0c65c0188ac3a1,0x2f104dc3600a28413c29,0x288e30e00bc41370f80,0xe260420d0585c22048f4,0x420d0585e0d030847204,0x86c502215021d0d8a050,0xbc5608c38047178a810e,0x1d2386c422f0461c0238,0xf144e26c2e1380471b82,0xb0bc0c20e01238c3802,0x84210d38033198347e1f,0x3e17018240c1802f0c42],#[0x70b84e00c3318e1709c,0x85c270f85c06091c3e13,0xe17080300f018438868f,0xb8047c28e34600cc310,0xc1c28748e1b1443c3421,0x500e138040c380471789,0x709c0c28e21018088f8,0x301007802f144203013,0x2e0504801f178141190a,0x178141204c0a02e11860,0xc5a08c87130870803013,0x80f8142188a0681b0127,0x284409b8005008ac502,0x3115862610e118a0300f,0x3e00c45e2d0c3631120a,0xa19005008ac642014054,0xc6220844d84010058bc0,0x662714002b18880e828a,0xe1f0b8145c20e3413210,0xc45180990e2f118387,0x601e051464280c0545e,0x509b080200b0f814520,0xd8618a2c1206c0190c47,0x8a03617030833143a280,0x9c3e008c66180b09c019,0x280d8384e009066280b0,0x90602b0c0384e009060,0x384e00d056280c0384e0,0x25198401e06106828098,0xf030834158a02e070708,0xa08610d38184198c0260,0x15a003c70130f09c0198],#[0x878361a1a8b8483b0422,0xa03625042a220883c6a0,0x8014116821d0d8e1d0d8,0x16085470a84c2235102f,0x54220f110817c05101e1,0xf043017881d0a86c5020,0x4c00d0c848104820250,0x41891884308081208212,0x2b098682264104600403,0x3081320e230c21070c28,0x83b1587821b05011286c,0x80a30a00b8202b144a12,0x80c008068642406801a0,0x42c06801a08314542406,0x25008610160340600403,0xf0034250180100d08236,0xd99041103c00d062540,0x704c340c2c3408ac204b,0xc045c20ad87010808101,0xa1882b04058112861061,0x10e4748028862a418b10,0xc9808b811c0b2860a1,0xa286a06140d8a1032861,0x14104a100c8f82c0c404,0xe1b0c11208d86189420,0x29415850321a5030a302,0xc2881a00681a00ac3158,0x40b21e0434231450150,0x188231286101188230d,0x4461a0e0281a0070140d,0x898121908520604321e0,0xc3015864481a0c162316],#[0x8015863040e005e19145,0x118643186005e19108b,0x60f01821097802460898,0x858190f04202686820c5,0x2c591c14431056c38586,0x102151404c4058ac]]
set_option maxRecDepth 16000 in
def g127H8 := limbs80 #[#[0x120080000030501c4201,0x2040f00006030500408,0x18000020034060105030,0xc0480007010480a01040,0x5010000400090a000000,0x20108800020713874060,0x18000000802030a00c0,0x102a008006a050980,0x183470050703c021007,0x50780000060c01c0406,0x1a0c000002e031000424,0x804010180c2a0900840,0x71f002100187c0006080,0x20680c0a02000402e190,0x40a040281c110290c000,0x41401000440e060905c0,0x49a100c80008010000,0x2802000880c360001,0x101820040b028444800,0x1201008084a3e1483c00,0x28021e0000412000800c,0x68002a08038000809060,0x50080002000d018060c0,0x120401615020443e1,0xc000f090241405008185,0xc0a08008281e030180,0x18003e0f2c80c0c1308,0xa00804305b000344a01,0xa1e2100822030c06016,0x78080197c02040b078,0x4000062f04924020a238,0x3e0a0f82006210],#[0xe05138540c0102810020,0xc0206020400200120204,0x9acde151800c1c0d050a,0x180406010004c025c4a,0x1a010008002000341004,0x14140088c241b118781e,0x58000309820022203000,0x183c00030e8e0040d058,0x40000c340720830004c0,0x6062683c10071b084140,0x10090c84406010100c1,0x40aa71101462040080,0x1030000195850240108,0x200601c541f01010040b,0xc29178083801060a410,0x2c040203c0a0f01000,0x381810280a0442407080,0x40a87c4e1b1d004ae000,0x51102e8070a038042c0,0x680a08848083d1f8144,0x1022010680c2e040900,0x413c4a2e2c8002e0500,0x30990804012b8400606,0x18118c804240982c08,0xc5c00008141a0602010,0x8850000d0506c001d158,0x704000000d0001414140,0x60308010380007084060,0x3407000080e2f088840,0xec0a311300040099480,0x7806010300c827701,0x28048243408030408e28],#[0x3d0681808230307800,0xc8adf028480001078d8,0xaac06060483c1c76149,0xca4bcca8f3891035672a,0x3fcda800039ada9737d1,0x998f2f61909669c51b89,0x51c77faf7a454a18b249,0xbb92a1d5ec068f225f3a,0xcda09000029e7e8cb133,0x82a77000041ac18f0411,0x699daf93b9a1a28bb888,0x32d0000000039a8b00,0x3def644780002959000,0x29c4200da4bd5813800,0x55172934dc88f0000000,0x3a42832f349,0x61b1000031e73128800,0x1b0900000000000,0xd0b1b83ad00000000000,0x7a9bcebc00002b308a6,0x1db90b30481ff800029a,0xa0000624600004ae748c,0x3fdd6888a8b25fb96025,0xee9d3e025f07b01d1977,0xc000003296ee718c1203,0xa800000002c5a7310e2d,0x980007dc2800061aa99e,0x61a90000000022ca45c,0x109f800028a68000000,0xca027000000e6bc52800,0x2b036839d3e7839b890e,0xb8abc31c1d1ae2a85c06],#[0x68cddb383bba8000092,0x27b93a04533c6cc0d000,0x643c000021cc6918c32,0x7000062bbc369a11b800,0x6f2f47ae9ad4118dadb1,0x3800052fd496a5101fd3,0x58bc00ba895ec8ec18c,0xbbab4000000007008000,0xb80004677d5e214556e7,0x100006c2e800009a6c78,0xb00001a3800001130035,0xe830300000000307b936,0xb3ac880001bbea04d898,0x5800000007aa92c3dfbb,0x60173e22a318880005d5,0x82c565b058000303f085,0x778000000000000070b,0x5a151da0a80000000000,0x8bc3d000000006442f2b,0x1aed5f9c13a108319e02,0xa0f5ac2759a438000587,0xb0000584e8b1371706f8,0x11507355c6a689932c0,0x2a8c723a2de87a81800,0x70c3a12c64aa88000000,0x5e33a217a99c5305c7b3,0x8b8a0b111c3adcc00926,0xf19110b6d089a7b70077,0xb514df53c705dca4d7c4,0xbe0967c23619c62c5d8a,0xa297b0008aa62cb0ff64,0x74afdab046a1349ce407],#[0xc390e2b6d9d6c80007e8,0x34306b1d58000233ef18,0x260fc1e0e987673187af,0xfcaee3b61b27b3082706,0x363bc55e19c800068b,0x5d13e80006371e245000,0xd800000004a1f0000700,0x50000721a9329813b201,0x73a0097200001a90c27,0xf0000000018988b95000,0x2aed502071793cc,0x58b39e7d00000433000,0x3800000bcc08be350000,0x69dc7309925c77859ae,0x822ba3a9a80000000000,0xc273d760cb3b5800009b,0x8bac90170a3af05e79a9,0x680004515b9f5000032d,0x44975a7a98d7b001139,0x41b927256844d0b25000,0x705d59078f0ce48f9c28,0x3789b81287b728024f15,0xe509772d04a55510a615,0x3000000000511e376502,0x62eb0000000000001ad,0xe98c4804900000000000,0x99f87e3c5ca8415788a,0x1435300000a6d8b1e036,0xe1ee162af3392d977d1e,0x36af980006b5c3023aab,0x800066f090440000223,0x1b22ba9d250d15541884],#[0x7399f41660b99b3021b3,0x5bba000028e70000038,0x2b98b8000021d3885000,0xca917119180002b73bd5,0xbb1682c8de84e0000525,0x6a30a720e80000000790,0xcfa588000000078512f7,0x536e986fc850429526b,0x6584b00005e180000000,0xb6cf56ab0a25339b3938,0xf800001a9e395fd1761f,0x764da0a0f000029f0710,0x47b978000439e8000081,0xe62ae319d59a2912984a,0x4cc01a78971bee17545e,0x38000392e633dc9f6cb9,0x1bf8b00005081518fed2,0x79859336880007003096,0x2e09eeab82231fb28b14,0x68cab00000000580fa3c,0x3725efa63f80a144ef9e,0x80000000000054f191d,0x650254,0x58a66000049d50000000,0xf05dfa44721560a5b109,0xa40800073018b44d0a,0x50eb3e68a2680000000,0x596c8000726481e5000,0x2f3418000000059f5800,0x6a1580002d6aa9aea20,0x43e6bf1cb381678b7000,0xe8195731392ff80001a6],#[0x294a500005a927f1f188,0xa1c1ad4464e538815685,0xb711e800059a5b81442a,0xcaaeff1fd7ae941229c3,0xd69def0a38215404bf97,0xae36acf8df48ba200780,0xcab7d6178121b91441c9,0x4a2772eeca678000148,0xf822f906580007b85800,0x50e300003241000071e,0xebf9d609688e24348000,0xbd2228d6399dcee20935,0x1a7b80007106537,0x4299f8e830bf0000000,0x5ad90000198f000,0x75a100001ac6800,0x65c880003a7349f2000,0x80000000062833b2b800,0x502f66f290000000072f,0x28e1e33c5a1ce80ca35,0x369458000722f0000000,0xeea9ea67b0000000019c,0x9009b5a6c74531a3910d,0x8f1800000005cd,0x2c54712f890cc5b6c000,0x226e000000003ad9ab8,0x2403b01179c728843000,0x8c022cae52331634ae83,0xd9143d90d9ba232b3843,0xad2790c4a8000615f803,0x42ba5d8264b1568ef8aa,0x78356340739940fa82a],#[0x7a854ea45eaded96f800,0xa000000d811d4b03d528,0x47e5e254df75a0000139,0x2f1800b0000120b700,0x60000000028953a62000,0x2d6c6000038e4800009f,0x56296b2afb24b21d78b0,0x2542db236a8a280007d4,0x70ddf21370000000053b,0x9aad8000043246e36ab4,0xdc120926fa2576b429a1,0x9b499103419bf0000332,0x404218000000038c5991,0xda838c22ea207776e838,0x7328ac328210680005e0,0xf9cd9a,0x4d8c4001f78c72a9c800,0x3e967f9f371f9201c527,0xa43664b7f7b822a2e393,0x72348c0bb72021b9dc37,0xc166f0e1352da933057c,0xe12c86a46e4546965fcc,0x37851ccac90cf0476b83,0x2f810c6e51983d9fa041,0x111c943b14216d532c94,0x293c858e88000320e0a1,0x3c2e8731ed267000042f,0xcd5b63b5b811074ac52a,0x6b28ce8db91f1fb4a6b3,0xb24db7e692383608359c,0x3c1291087cae07ae5ea1,0xf232c0cff1e2f112334],#[0x44926a2fb800021c88ac,0x78b1c307200007ab6b93,0x35873d2c1db4352d4984,0xe80006c0a184d1aa5802,0xa80000000702da20d22c,0xdf3396443b2d0d622aae,0x9077d08ac8132800079c,0x9ea20800069bd216bab4,0x3aa17d00000000644,0x26697511a00000000000,0x45b9b7adf50af8000401,0xb4149a8c02b5df374585,0xe7ca5a3594cc3e24deb5,0x53b9f4956d369000028f,0xa0000478d22bb52810ec,0x780001a29fb714b050cb,0x50cd74191097de0fbab,0x7e0f8c9a26c0b98f5304,0x9feedf85e31034031613,0x7540129600000248185,0x88446804381a0b9fd800,0x991b0790248aa0b1d297,0x451bc000010e5d96490d,0x73a9fe4cb94f0634bf89,0x10686da77aab9eb0e710,0xbe545ade9d1325bb56c1,0xa79bc2141162af854a0,0xfc28b092ee05fc00f3a7,0x87eee430b2b67ba05eb9,0xf299b76ba4113fa883a0,0xc37888278c020a016c35,0x5a1bb543e56777828491],#[0x23a94d22b631cb804801,0xd10d5e72414b06b755cb,0xab16272068b16014750d,0xf699b937d9940183a438,0x52931c353d318f198b1d,0xd2e543e4c8a2c4105e06,0x7e2c9b6e8027068668a7,0x40690a95c992070ca801,0x36a34800031d9b086199,0x92b769bb472d20000636,0xa5b7801feb85afdebba5,0xf9b08d989b0d6c13150f,0xd800000004048f29298f,0x7dc56bba4312de3b8b8a,0x800000003ccd1cce945,0x2acb99029a6c932efb0,0xf70521976b560d72d800,0x5932b0000674b390aae9,0xda92735bbf2162a21605,0xac21db18314bb185cf18,0x42b7c093d9b369ad64a2,0x58991c4303aea11341b,0xed82181f7fae67069800,0xfb95f000050370000585,0x6aea3a185719dd3a4938,0x3c86660f7a4ae80002b6,0x72aa4b23102389a30300,0xca3c15aa7f10470e96dd,0xcc923acae79148644fa0,0xb79b0d4b3213caa2d69f,0x493178000000003c7f8f,0xe41db80000b5e477a43c],#[0x147980005ea7387,0x3875000000000000000,0xc62e4800004a6bc32800,0xfb8d622517a55b1abb21,0x760f6dc5e8a84b4,0x96ae1b290782b611f800,0x70e28b79d2099bc030d,0x12c561ac80004c2c800,0x15b6f9482b071ab2800,0x40802d3326a1e8a3e000,0xcf8b122c32bb705c6a8f,0x5c4aae30388e3d0b0f39,0x68000328fe3bce822113,0x2c844936ca5bb5b64f3a,0x93a015843ac804c115,0x6910c5ea8cf4b992000,0xfb29e692f69098a0d800,0x103989b5c96073b6e07,0xad0890000787d1185800,0xa95fbab3616e001c25,0x409b345f94af100006a8,0xa2950d1cf29a130b4395,0x2fe4f7c7353a90a19382,0xf6b4085ff78333b27a27,0x500a4800059da78410b1,0x6991900001311a6eed05,0xa00002b35e30c1268ca6,0x67f12c0b2b082b0ea799,0x137325d40000000031d,0x170f11b54000022ea000,0x511948000000052f9630,0x682eb15d00007d4f213],#[0xd93366cc30000000061d,0xf9389411829c0ab2e7b0,0xa71b9d17e30eee98964e,0x6ab3b6c35d94f345389a,0x59acc80000000564e46e,0x16138837ea38beb4e99c,0x28000717d912f80005c0,0x8e0f913c658741d28e04,0x35b23010b7201a1a618a,0x75a24023591998908207,0xf20670000094a4ba61b5,0x2e1253b5231ef1b9342c,0xd4241d1c228f24958818,0xef2564819fb5ae8ba4ee,0x3800041bdc9cd000078f,0x8cd64c9e656e62ba1d9e,0x77f7855e0b44ccbae63c,0xba1ff5aad5c9d581860f,0xfa9d8a927a4038221e1f,0xb90ddccf2f1e5b80ee82,0x8000000001d3cf8e5130,0x703981a3c3326d4322f8,0x280470000099fb86d199,0x1077c196ea9ec662151b,0x740e09781ebaa72b1332,0x301212e7fe2bf80007a8,0x5440732cc0ef3293c29,0xcba11d52322b271e2000,0x750a30000027ff377914,0xb00006a2ccb100000032,0x580c7942500000000014,0xf794d544800001653249],#[0x5ef780000000065b3b8,0x1d1a8000000,0x7800006cd797b8000000,0x32c0000050d8e06,0x521f800000000000000,0x107c800,0xbc9bcf9639b338000000,0x4924209d8000385,0x8200c0000400bb8002a5,0x3a8538dc80001090622,0x3000000002a4e08ed000,0xa00006070e82cb8cbd96,0xdd2edf85d32cf8000424,0x1269000000005b16dad,0xf5833800012760000000,0x365500002924da8b967,0xc30b2000076f2d174000,0x883604227c9a5427cebb,0x200000000383f80005a1,0x6a73d2ebd5683324f28,0xaa0a9e8a900000000000,0x8869e860000454ee39,0x3000071eeeb110000000,0xc34ca9b600006aa2bbb,0x48000639078d380004f5,0x8000000000003809871,0xb4af7486a5b5c800023c,0x7ca4f4a12f13c01afa8d,0x932f51a6e897f16e1c80,0xa91db373c80004562aa9,0x600003060a39bc0c2084,0x244a624a800023b],#[0xaf0cec84f7b3d19a1c07,0x523bdbc39f08d373dfc3,0x6000038a7f083eacb6ab,0x3a0c6192abab764f2000,0x9eb4f2339a24e9123032,0x280006ac78000564c4db,0x5089db8ce2746b3,0xc315e3aa70000516d800,0xfc949609c800039a4596,0x168f6800060c863bfdb1,0xb497619b578696b4d607,0x6b7958b941691b8,0xe3e56404a69bb8cb2cde,0x900007db952f39155d94,0xaa419c16550fcaa97b90,0x10000616d418143c362c,0x743969f7736200002dd,0x4aa5bdf984ac3cbc1800,0x15daadb1a62586879b8f,0xa01c0424f8298800068e,0x871a379be28b3785b028,0xd589309c77877c2a2118,0x9e06d80004242298ca0b,0x1a476a7c295ab085c24,0x6981aa34100e60000000,0x49128a79800030aa993,0x69283f09831053945000,0xb00004aec1a3d50bde82,0x8ea9f0acd705f614fa01,0x22d28adb1e850000701,0x2b9d7188880000000000,0x8afce5d21cf40000532],#[0x58b492c278ccd99,0x928d74652cbb4f405000,0xabb74c5fa43b7a91d945,0x1493818e7ab8df136023,0xc157002fb00004836010,0x7c030000496e1a3e82c,0x9a48f191e391ae991000,0xbc9410ad163352a5e2a3,0xda1a4ea3500002cbc54b,0x268f5c084c95bd51120f,0x6ca606f80c9bf9247ab4,0xd39f9d33ab87f12d5c85,0x498d014ecb70a9e190a,0x5800029e420b9c8e4000,0xba297a0fea7f4d1dcb1,0xc2877382c281bb6450b5,0x1ed47b8df009f3aa6a88,0xf8c942ac7a5dbc51767,0x81cb9e97ff9938000016,0x3bf6357b06b8b86f9d,0xd40c33857e2df9892000,0xd4081b94364d046c1d11,0x88000000051550000625,0x2c2e2b8b1f2894d626a0,0x168a60000000000002d2,0xea2079bb2e26bd1fc09f,0x40a6b118a13a86c3b986,0x4000059de789c5a7eec8,0x7f2063035987edd5f7b6,0x2ec339a343900ae55f1b,0xb8a630990224ca21725b,0x5dcc182618000205a7ca],#[0x9c4b0ba13b3ac6517f8a,0xeab5492d199a811c9b3a,0x188eb91140f87b2fa52f,0xfc84cfa9100002971d25,0xd9997a9749a5f80007b5,0x8412cd3c3c49625fc58e,0xe4cf9afe68dc3146186,0x2c48d7b80ca14f1d159f,0xf09963ab36383cabcbe8,0xb8abf09e715dc88a025,0x2adbe01d6c1e838c285,0xe7878103bff8c8000000,0x67063ec5b012621f440d,0xfa08e6b2fb0091b2aab0,0x6b1332ca780005892e43,0xb097700006d605a101a7,0x8427e233e1981a8e9d53,0x3a28e828d7260eb7fd83,0x22c100007ef100006ca,0x83cadcbc430615063000,0x9ed4d98683bd7b4e429,0x5561f15169f893a0eea,0x433f68ae00002195800,0x9cc38000000006072800,0xb7a9a1175e75c1db134d,0x94c36d3a3b88c8a32731,0x3ababfb12c8d3166869d,0xf63683a0080004d78d05,0x4384dbc2000028d1d2b,0x18300000327a5334800,0x5829dcb6289a3ab88000,0x1878126e40000424c711],#[0x7ca808000539c0aa1714,0xd5832929d31ec800038b,0xc599ef2785b58614ba38,0x6ade33b0f73a69421d1,0x6e3580004b5a000,0x4076ebbe0000393e000,0x4f7b162d55007328e000,0x6b09182a532d4000049c,0x19857034563855025014,0x458602103b38e00003ab,0x49bb8000050be8000196,0xc000072add1af00005a5,0x1436236f8000397,0x6c134d1e4e075c352800,0xf319a800001b4ca4340b,0x141df8286814af93ada6,0x8bec0a9e9b0d400005a7,0x6e84f9af6aa4440f66b8,0x8a0519ba0223a8395f6,0x885e402653a2371c7b25,0xa49b94f6aec940000335,0x519ca20290984564ab8c,0x700001baa800060b0711,0xc0944d36a62371caf4bc,0x82dd62181952526138a,0x714c00006064800050c,0x5b1d280001713c236000,0x79edd9799387d38153c,0xbd1dd80007a578000000,0xac8f32291e11b0b89f9e,0x20000200522da7a4bd2b,0x2bb802048386ab32a325],#[0x7ab7ce6991019581e3ee,0xfa829a0ead861c89ac03,0x43bb8bb940f39a69923,0xadb2c198721b20000000,0xfae4a456e2834e821540,0x8c98e59d6d0a42d518b3,0x22319587d9b6f74776a8,0x28113a20000078c8c18,0x545880000b342ab0000,0x4230d615b7248a0d5000,0x6e9848ba1155e4b7ad06,0x92f5e7346017a4140f11,0xa3f53200e188187f87,0x300007d4200000000000,0x400c2806b29049e17eaa,0x2b65f9f2812262ff1b1,0xb5ac4f2490204a8a7000,0xba169ba04399844ee79a,0x16be8381e4ef7a59a8f,0x9aaef410ec30a931d800,0xdf125a2a812ecb13d475,0x8a10c80005226520a428,0x2a8b50000315398be06a,0xfc254308ff80ac1ea4de,0x6dc13800000007dca8ee,0xc828980004d4480b5e22,0x3c5d6139f8a200002cd,0xce9b180000cce5159bee,0x16d6880002830a930886,0x4c814e9549af48000139,0x20000188449f4a88b08d,0xc29e95180fad70aa1f2e],#[0xab9c3d2e42321ae574af,0x980004d2ce347e3b3c45,0x100003e2f0000503cd34,0x2f1cae2bd095a18d0fae,0x3e91c19962cd8391ea8,0x9000062448000781e800,0x800053c5189d70dfc2b,0xf296f3849a9cff4c2609,0x921e8bae0b0b8b4948b0,0x1cc73b8d05f6c68da6d1,0xb010c2ac4619e543f112,0x6c4533a71b78b900534,0xdaaf0800000000000000,0x1800000004c4b748efa7,0xf7203686c11d471baabb,0x68000000028532de4a57,0x602a8000000071f3db4,0x6012b939136bc9cc800,0x28000222511488300000,0x2c1610b3314448000619,0xc000001fe5bb0123ddac,0x647a00000e6ee17e8a0,0xd22bebbafcdd65cb1218,0x72996a307b0a1000071a,0x4323bd29b000043a3116,0x289a7cae6800000f8739,0xc40ee2b8e9880800051c,0x6c9712099a3a7f1c6295,0x70000000030a5000031b,0x392d0398a07a9662aac,0xe96ad13f80001367000,0xe039e6622000004575cf],#[0x400001ab880000000637,0xc121212a9d1fa99c8282,0xd5e65c91600000000112,0x87cba800042b61b59f8f,0xb2ea402d3d3a28d26f45,0xe98873846690d09cbfaa,0x23b4326000071c,0x894e0105a17b02f000,0x2d3d19ee000,0x80006510da9448c5440,0xfab4fb771af009ed100,0x291f000020a1800071d,0x192f5f27180005b1ad24,0xb20a37b0000084,0xd00002f650968aaf2000,0xc93970f8603148000082,0xf0000766a336e52ce6aa,0x6c8130375bae78000190,0x8a98a920100004dd008c,0x900000000793f681a1b3,0x4ac7f3c20a2e3503c3f3,0x8c8e070a0281180003cc,0x2030800002a720aaeba2,0xe60d200005027c9eb0b7,0x7c1c00000afaa06,0xd3831d08000000000000,0x586f00005459a1d,0x6fa9732bda0b6223c800,0xda6a2a3080000345aad,0x63a84800060c9e5e1663,0x3b858933780000000398,0xbd12b10468a2200004a0],#[0xbeadc80001d19ab1212a,0x622db0020000582,0xb0000734c226abaa0000,0x1ebb9c9e8781c82d7896,0x49253e045d1b7381fdb5,0xb3a8b233ea1e0c8e3a2,0xd00000000000060ff71e,0x8fb65000061088000051,0xd7237ab61087c00007de,0x6eb8a000025f2880e235,0x78dd7c30efc23bc4b867,0x6f9e329e0334448d2e10,0x725298421a864ae8c35,0x4874f2a6030c808d800,0x61e18f0e858000]]
set_option maxRecDepth 16000 in
def g127D9 := limbs80 #[#[0xd65586bfbaa435f5d760,0xaec75f5d761cfacbb0e7,0x10ff260887f920442beb,0x7f531443fa90a21fe581,0xeb9221fd58510fea8288,0xcd10bfae6885ff72442f,0x885ff74442feba2217fd,0x2ffbb2217f5d910efaca,0xfdc930bfee2987f9604c,0xe8987dd634c3eea1a617,0x4c3beb2a617fdd130bfa,0x17fdc560bfeec985fd76,0xfee6b06ff635837eb1ac,0x63d82feb8ec1df59560b,0xa437fdc121bfae7b06fd,0x1bfae690ff561487faa0,0x7f75487beb2a437fdcd2,0xb0a637fdd921bfaec90f,0x531bfae898fdd634c7fa,0xff561506febb263df59,0xbeb2a83ef59141f7a86a,0xdc961bfee0b0dfd76507,0x6b0eff635877eb1ac37f,0x87beb2ac37fdd161bfee,0xbf58f61bfae5b0dfd70d,0xee0a1dfd74d86feb9ec3,0x550feeb1a877fdc543bf,0xc77fdd943bfaeca1f7d6,0xbfee4b1dff7158effb82,0xd70d8fbeb2ac77fdd163,0xa6c77f5cb63bfae3b1df,0x65efee0b2f7d70596feb],#[0xf7d73597bfb8acbdf5c5,0xea1221ff4c910efee6b2,0xc910ffec4887fd62443f,0x887fd63443fea1a21ff5,0x3ffb2221ff59110ffec6,0xf9d910ffaec887fd7444,0xc2987fd414c3fe90a61f,0x4c3fea1261ffd8530ffa,0x1ff5c930ffec4987fd62,0xfae8987ff644c3feb226,0x21583ff3b261ff5d930f,0xac1ff50560ffa62b07fd,0xffee2b07fd71583feb0,0xfd73583feb1ac1ff50d6,0x98ec1ff48760ffee6b07,0x121ffa87b07fd41d83fe,0xffd63487fea1a43ff5c,0xff3b243ff5d921ffec69,0xd8931ffac498ffd424c7,0x4a0fff644c7feb2263ff,0x7ffb1283ff58941ffa6,0xff5c161ffec6a0ffd635,0xae4b0ffd62587ffb82c3,0x3587fea1ac3ffdc961ff,0xc3ffdcd61ffae6b0ffd6,0xffee8b0ffd74587feb22,0xf7050ffeb8287ff50f61,0xb287ffdc543ffae2a1ff,0x43ffceca1ffd7650ffe3,0xfff7058ffeb82c7ffdd9,0xeb92c7ffdc563ffae2b1,0xd163ffac8b1fff7258ff],#[0x1b003e0003ffba2c7ff5,0xa017a04f010603600a20,0x2c60a2025a08b01ee06,0x42a0ff03ae0de034a0c7,0x9e15a052a13904b611a0,0x21bb06a619c062217705,0x21c08321fb07a61d8073,0x7b09be264094a24108be,0xc0aea2b10a8e2980a322,0xc4e3060bda2e70b5e2c,0xd8a3550d2633c0cba321,0x63b20e8a3930e063720,0xa41710163f80f9a3d30f,0x48211c245f113e43e10a,0xe9135e4c612d24a51256,0x14f2531147650c13ea4,0x1676590160256f157e55,0x8425fd17a65da171a5b1,0xde66c197264d18de6201,0x26cd1ade6a81a5268519,0x7401cca71f1c1e6f81b9,0xaf1e567821db27591d36,0xc20327fb1fa67d41f127,0x21de868215a84320b681,0x35a8c522e68aa227288b,0x3693a24a291323f68ec2,0xa9a7266698425c295d25,0xa14281a9f5277e9d226f,0x8529bea5c293aa3f2896,0xc2b6aac72ac6aa42a52a,0x2cdeb282c6ab0b2beeae,0x7811a1ee06b6e2d52b47],#[0x4560c4e0851f1d1e1b0,0x81cac60740c12e822b1b,0x6c11f07821d14360b04b,0xc0201c1c7f047a101c68,0x130f170070545844382,0xac70701c347c582c01c2,0xc5c01c14b873150f0204,0x1c1f0e0700702c504c3,0xb020468a02c3c54781c,0x43c01c1448401f17110e,0x410181f170f0070507c5,0x130e07002c907c5c3c04,0x7c345c01c1458401cb3,0x2c02500ad1e0a0670b87,0x705041047c5c4c3818,0xc5c31c84c031211f170f,0x81cc7170d0b005070107,0x1147073107c543c01c1,0xc31c81c03120120b0e07,0xf0f091612070090407c5,0x83107c345c01c1858501,0x3122701e11031604c4ac,0xf00705148481c5c3c2c0,0x481c333c04231211f170,0x1f170f09130204c48050,0xc714c3c28107c0443320,0x781312416070f0b0110c,0x204c88338440c5c3c20,0x7c081322013170d081f,0x30c1f0204c8814c5c344,0xb8507c0412e2b140b151,0xc547c0832b200f030710],#[0xe141f030714ac52e02c1,0x1f04b8ac607c0c1442,0x60b0068800c12d2a111d,0x7c0c12e2b151f17120f0,0x91c1f170f04cb002474,0x42f0024707c5c3c132c0,0x24047c5c12b181cbf0f0,0xc00b1b170f04cb002468,0xf070d13002c647c4c3c1,0x4b8547c4c3c1c00b18b,0x47c4c3c1c00b19011f13,0x321c13170e090700c87,0x120b00c8804c582c143c,0xc3c107c0091c1f170f05,0xf170e0b04930110724c5,0x1cac804c3c182c045321,0xc0823124c900d60b04b8,0xe0b00d083304c5c34107,0x307c031091817110f041,0x715130c1f0208c48c5c,0x340145c4c307c0823324,0x1c0c0a1214c30104bc9,0x14707038584c1c042302,0xc1852b2013070d1f0b02,0xb06161300815c2404784,0x4c3c185c02f24051f0f0,0x130f170104c873002478,0x480184c5c3c042311c0a,0x5312008061314cb010cc,0x1cc4ac8020184c332c04,0x7c0843320ca05031610,0xf06101f0108805c3c241],#[0x3c2c107c084342093170,0x5170f081f0210cc9054,0x504689131511060f14d0,0x342111c7c74da00786cd,0x600786c687870dc1151,0x4280c14415110f221d0b,0xb19121e031704746c787,0x104204b898747c0c51c2,0x82c08143291d110f021e,0xf02051c92584441047c5,0x543c01c1d10421316090,0xbd1f0d17007091a1247c,0x834347c5c01c261c1208,0x20d0f17011c707260704,0x483431047c08245812c1,0x120e091702051ca27844,0x470bc3c01c2c1d110c42,0xc160a051f0f170070716,0x1f031470ac6c3c5c0471,0x987478343c04b1c1e1d,0xc1c92160c09150d1f007,0x20530a85458343c0471,0x81432d1d0d08521e0a13,0x492585458242144784c0,0x91c1e15160908510f00c,0x120514b1247c50ac01c2,0x31249e0d0e0908511f02,0x70607834382421445c0,0x5c3c01c3118591f0d170,0x428127170f011c70507c,0x20524a231a87c5c443c0,0x14b248d150d0a160e1f0],#[0xa04c234443848387c08,0x908e151611120d0c1f01,0x238710c5c4c381c04228,0x1281e070f00cd08c4744,0x807232187c3c2c045448,0x31201f15130f0a0700c4,0x110cc71481c544c3c2c0,0x38142c087201f0e070b0,0xd0a07021d24a1ac5c44,0x4381c0874b246e15160d,0x9170205121c81e844483,0x21047c0412e2b1c870f0,0xc21e04bd1d0700b8ac91,0xc626814441c047c52b20,0x1c02e2b1e050703151ca,0x230700b91cac5838247c,0xcaca8747828141c04c2b,0xb2096140e0a070115051,0x1624a854582814140472,0x47289e0e0a050d051f01,0xc81b834382814145c089,0x72e261d1d0e0507022ca,0x1cb8725840381c044414,0x47c0448b261112050501,0x513011e2c92683814341,0x4c38241c0287a0d0e050,0xf0104c8644248710c5c,0x8444c107c043822c1f17,0x306090f0068925248545,0x7c5c1c0433218921f171,0x8605061f0d17011208a0,0x7c544c3c182c0322090],#[0x442423170f042700c86,0x1f011608c0702c5c3c1c,0xb1c9c9211120d0e0504,0x70114c862487c4c3c1c0,0x1c34582c04487241f0f0,0x1e170b0e130104a21814,0x50430c0412f1c845851,0x182d1f04270f00bc747,0xc11f00bca4704c1c0423,0x8584c0250d0b04141104,0x613011c84121c147c3c2,0x18430c02f1c87070f0a1,0x53170f090700c470547c,0xc860704c3c5c041321c,0x5c3c042311f170f04270,0x9a1f170b07002870704c,0x11610c07c5c032433118,0x49c9a0d0e090a05041f0,0x6412687c3c2c1c084452,0x1f0f00c914c4]]
set_option maxRecDepth 16000 in
def g127H9 := limbs80 #[#[0x50b8010440002810,0x10000d0040803023,0xb000020280b03403,0x9455010060140200000,0x382f058180982902020,0x34180340e0700b0501e,0x201e08c000100011000,0x1dc020003d0140515800,0x2800020300000000042,0x101400c38120000ec04,0xb0141800c7602415,0x14010d8020602507800,0xc25c362d40901c04,0x1981600445214020bc21,0xc0f0005300c190b812,0x124130900200c1a0c804,0x13ca302000000045a02e,0xa00302c001ac0200832,0x81202401050350640f,0x1c0802c0d03c0100452,0x942c0cc0203c050184c,0xa4030e0003940000003,0x680e08001048e80582f,0x8070c01a004610ac02,0x178920fc810981a00404,0x1201e034030140401c19,0x1641300c002540305c2f,0x2e000140a40461814,0x54160a8370c00a04c62,0x181a004d8034000bc07,0xd01c0340f04c1915d14,0xb601c030745c12c00],#[0x3c7b0301301c0b06805,0x4c15040010e8b908833,0x1519c0005c001a071,0x243a0002a1bc0002801,0x800493000af15c15,0x534000006710401,0x2a80101c0b0002f01044,0x24000380011816025a4,0x134d0030040d80d0a80d,0x27802088040040f31c3a,0x1a8110b01100400000a5,0xc170300a0000f0242d,0x4c60294da1005501c00,0x38562a41f00c0348802,0x18407050011340105417,0x40502806054060d1e7,0x802344070c44920c06,0x13413b6c1e0084812c06,0x4c281c02a669bb1f806,0x52c02030420000300014,0x1794b11ca60202b01401,0x8c002f02cbac4d4f403,0x204e7cc450002c12214,0xffe2d7731a080990f020,0x5de146e02453f368db40,0xa283f810be8be29382b2,0x61096463054ae9986892,0xc9842ad4a5c3cdd4d5c4,0x9c34a75ca2d4be8c5cb4,0x76d18300f194b1113f19,0x8fae5d3ac34c4206e18,0x2b793fe4fd0246fb64e3],#[0x295358fc4f51b483b8a4,0x9c00c84ccb2436e11c54,0xd3b37808c96af6fabfc4,0x983233185514228368e8,0x27680581b5828ff03813,0x9ea3799a87aa4b6ac529,0x13e4acf1fbc499702e83,0x1fa076b2ed9041f08811,0xf17362305413e832fdf5,0xc00502528682e5f52cf1,0x43c0585ccd194ad83973,0xe5f29b000042c67497c8,0x75b223205902db3ae11c,0xb144b2432694350000d1,0xa7090cce3d903d4aed3,0x55946a521f43aa94131a,0xf032ff404faa86f2222a,0xe3c38b9309f24c5c3378,0xc31404c31ed0aa02eb00,0x7440f063fa98b2e20522,0x3b38b1c271aaad144ad9,0xa083da906c33d671b78a,0x223265230ab00ec27e01,0x8791706996d26d4311cc,0x1e207833b4502b51ad91,0x6b52a7706ff3b700009c,0x3680196a5862804253f4,0xc9649231db2314641d28,0xf6000044bb1361f22aa2,0xcf63a60000351720bfe9,0xcf222f91ecc5333c2324,0xd251170000f2a6000092],#[0x8b000000000000ea5402,0x53706d2ac6824ac1b68b,0x7381de18d65ab40515dc,0x8dd1d4d1220000a955e2,0x2bfb4a00003322f336f8,0x9af40adbdf60c9d52423,0xa1f30c42a8cc1f000084,0xcd94ea61e280c740f792,0x7493ba249021c864c052,0xc900009a3aa4dae02d80,0xe48869a0e1634f14e081,0xeef0a9940ba2ae5aacf2,0x2e317cb221523800001a,0x2b0000d405e4bf60af62,0x79b496000000007247a5,0x800d2fc13033170000c4,0x3f94e991b91509b15271,0x7c000033abf434845313,0xc9b42da86380ee9906c3,0x93e3101bdc5b542282d3,0xa37231510b60c4615a79,0xdd0160033e163550740,0x2554c22459144c63850c,0xe0516eb393248ee8ae81,0x1f4a4db70633a34932c,0xa6e1a5c00c53ee102104,0xda89a1bbca4af530ab,0x788e0177bc94000000,0xa3f1f2942341e6f47f75,0x6b416000002aa00efb4,0xdc712c0000d4d863be54,0x52930ea248408ae399d2],#[0x87e32a4bc1a0b0b006c0,0x4940896a7b8144a40ee4,0x4c537722d014391057f3,0x9c17642ea0f591514c,0x2ac19ed210e458306200,0x95b4fb291da10af4ff20,0x290271daf3d931c6c3,0x73c9ef639692f2949f00,0x5a0000f07bc505415869,0xe3e197e468b463643f52,0x1db24b000010c00000d3,0xa70b9b434c0000ab22c5,0xa8636432a561d6094700,0x8b0000000042705c3150,0x669380b9d022cad38ca8,0x3d0000309ad94ce35938,0x97417460cb50d3e0f31b,0x6b541930ba21900beaa0,0x9c08b71afa93ffb137c0,0xe2b4a992f730e4637ddb,0x34b071d0082e645f32,0x1df39b82ab7026000000,0xf511250cec0fd10e0ab,0x260000a279c3d3d13851,0xb13c0000f88a511aec,0x1d010eba5c31a9410900,0x46bba9f3eadaafa23d5c,0x99c1c13446c2f47414e8,0xa0d166590e4106000062,0x32aa5e95385269a34ea4,0xf49cc2ea83308d14d170,0xca12976b7ec1ae353733],#[0x56367c33d0000e33933,0x65e0bb0000a055401af0,0xa4853958d9d1c4592f3b,0xeb000081c0348bb03bf3,0x1663ef6450c08f74d4d0,0xa5132a511c4d6a236d2,0x9493a3b449723f31d1a5,0x2220e9f0ccd4828a64,0x9452010000f0b1f0da00,0x6c3997bc5093ed322872,0x36cb5fb4e7f356385d51,0xffc2f32b1618691f045,0x26a17fd04800e6009f40,0x6ba45af34a01a6693e61,0xf002089283c0bcc07a7a,0x77f3dc83d7f37e2845fb,0xf3635b7306f16858347b,0xb6ea51dae0b2dd601434,0x275a4911b154eddc1160,0x1b06390ac2b232ae378,0xf31a66eb4961c5f2e120,0xddc25fc01e1512912862,0xed0532aa56e1f7a36b13,0xe6511d11313c5bd2eac0,0x65a01731924240f46edc,0x3ca448b51ab1d29261a1,0xfb717b894e8b4034f03a,0x1053db5bbf00e2316d3c,0xfba14861a7c0abe1a45a,0x17815f428ec4c8a0a470,0xe58023d1f4e14aaaf512,0x349066e81af52f0c4a83],#[0xa03b1c5000f1337c5ae1,0xf582fbc4e49119d38853,0xe1c0bd01d33172eb9ad3,0xba8129cbbedba1f2cb78,0x29722cc07231d9000094,0xe1337aeb45a2fe519352,0x43f1ac7518c05e000031,0x1d11076226821a921501,0x1fa12bf3a1b372723712,0x6ad1f89891d07522065b,0xd8281de20c3018730130,0xc9c4f7d0028a5043a272,0x7fe43d2c80dad501fc7a,0x68000059b422ac415eb0,0xcccccc329a43ecc23e82,0x4b3ad08b402890,0xbb0d396c245c20897d00,0x9c61ffb20bc535d12d52,0xc540ad9272a3bcdafc70,0x7893e23c7e7373a33082,0x1060a0e3160044616282,0x9227f203df096f13e54,0xbddd22826c2840e4f650,0xa291495526533e322b62,0x5b1c2d548dc41febe19b,0x4293e0e81890688a71da,0xb2c3cb90946b6b38ed60,0xc7429c73c700b331dfc0,0x7bf437e8e76b0003b221,0xe7f1980470852361b269,0x174be0e189d0de61a290,0x91f20493159ad6b23464],#[0x69e11e80368386150df3,0x4c4a7222f0f27b012fc0,0xa24101e3c59bec50c261,0x711bb0ea75d42c22bcc0,0x67b260119558e0ca6f50,0xe3d23992671307b30d88,0xc6f94951409348fa8441,0x35f2eeec5f326ff3b6bb,0xcc58d513fe4c9e648fb8,0x7a6979c18250ae88ca74,0x42a3d000092e930f8b2,0xeacbd509a523408b5175,0x4ef1a8cbc73b6da4b8c0,0x964491631db1bc094020,0xad2303ab72f3f9c0f271,0xd2a3203993b031eaf4,0xd9633b29a4743a24c600,0x65ac9683c2c0207a46c0,0xfca93386ac10ca2b9a3,0x352a22a4a9bfa3,0xc2559c3d2034d02900,0xd2906032c83c5d247e00,0xf47588c8689a5a4c13,0x6683cf0b530000b33c00,0xc7d1cbbd0e73bd4cb122,0x200ae24139118e41edfa,0xb56a110000a11ff3b9e3,0x3ba19f12e7821e101b93,0x9dd0b983421995607c0b,0x9d7a05322d4d02e29d1c,0x472486335d0000a9d8c1,0xf0a5f4b7d2756d17a4],#[0xc19421842513136000,0xe951cf429e0000211b00,0x84852081b08173e0fcb3,0xeb729f0b4d08b5f04a52,0x530000f3b321aff3d43b,0xd2808ee390000068e459,0x9d00000000f3cc003154,0x13d3e16a5ab408bb3c30,0x1b6fc0fe025864744c,0x82ba761c79627d416400,0xbe9a6878970000000094,0xb7b9ffe2880000834bc1,0xf3825423c8d0a6fa43b0,0x9632b41c2ee4cb0000bb,0xbc89815b5ec120c3ad0a,0x11aa5c3024b5042f0a,0xde24fcc136c431327600,0x6cc124199d000032f56c,0xdc0000000031e4fcb333,0x28504c9345d4f184d770,0xb2187c48c37bb5,0xd1d531e8e318d39c00,0x927401b8c49dba7d00,0xeaab2e889e30289e300,0x668cc3e521084ce35562,0xf67a4d79c284768103c4,0x56538771812992e2e3f3,0x300000697c81f5000080,0xb364e2230beab5a3fc70,0x1cb36d0000c4b4a0dd72,0x82cf1e841d1f610d7d5,0xe07a955202a47c51bf95],#[0xc06a1644f9e154d873e2,0xde84ef44ebbb52c51912,0xc4159b38a34f4b25e33,0x87518f000084d3841a34,0x9a797a3331023534a6c0,0x150000b93a2bddb45eb3,0x5b7013226bb4e5225b79,0x962f6a94df035846484,0x506994d452a0e91c0f52,0x81d4af0000644504ecc3,0xde3527acfa54deb48c64,0xc29015325002c29357d2,0xb219a7b1c3b049828b81,0x2200008116852561884c,0xda54bd550b0000ec1670,0x6041fa647350c6a3c4b2,0xde52d3b7f7430d32391,0xd8d369450c84db342611,0xbaf412e86532cce24351,0x4283761c9b7b476a610a,0xb3236eca0fb0f4922521,0x3dc4b9a4c730cd525c64,0x863888e28d63fbc959b1,0xae7245c3414244e38ee0,0x2f5af4341e30c552b2a3,0x116212b4570000a12a10,0x1bb392dfa36a804650,0xe37fe157345d23d500,0x3289edec27f81ec0d501,0x28810410107213242083,0x55f534432d6477805194,0xe91b46e262245c000061],#[0x2b0123001f60e5b0d1bb,0x44a0f6439d2371c3e6ec,0x4400004003617ed488bc,0xbaa38f0000ab4b94abca,0x1b0000d3f15327000011,0x49679293814734,0x2a251969000072b000,0x34a85522000000,0x54c33722d900004a8500,0xa300007008d2d60000a4,0x2478a43cc19af9,0x6077e26a0000c48500,0xf1e1e070e82211000000,0xf954f384107d0000f2,0x846fc04554ce611500,0x69ab968cfff114b1e900,0x982b63824f53f248d824,0x4e01691027b0dfbaaed0,0x5c0000a2b88a74f09122,0x89105bf3e7da62a16b80,0xa794aa94674c3222ef54,0x4b6bbca16f551421cc63,0x42b374d31bf8d41ad320,0x148495d503d35eb252d4,0x199a93ce41eea249f2,0x1b92968966708ccc4500,0x6cf93050ca9c47923b85,0xf20640000b81704eef4,0x9bcbbdfc5ed36f000004,0xfd321cf41c000024f2c4,0x3ec35c947a715c2346f1,0x2ee38d1a6e12a9546d14],#[0xa33333f34d68cb420071,0x44b4e3ba8fdbc849fd61,0x25d44e5bc403942838cb,0xd528c0000a18d3421dc,0x5de3e4c079418cb4b6c9,0xbd43df82903af90000fa,0x8455000020809516ea,0x50306739f7a00b90f900,0xb95b991ce484e86b4240,0x563b6c20a1000000003a,0x382334fb98f392731f42,0x897b1a725774410000f3,0x83527c00000000781bd3,0x6588620000c444609240,0xec0000f1530000f8cd10,0xa270820000b4d9b50ff0,0x63052eb53123fd10c139,0x2514329d35a410562,0xe8000074ca0000021b00,0xc1d76289fb,0x4546284980000a08400,0xe41503bbdbaa0000a3,0xca0000f0072978c03c00,0x9bfc2182c403f000008c,0x24486cf383cbfae07eb1,0xddb0b5f0d0e102b48474,0xfc0000e0855483309e0c,0x831dd1427713b04bc32,0x970000fb6253a80b68b1,0x6e44df02d3117a000073,0x99e819b418999bd33532,0xce035373a5b281014110],#[0xe472d5f02c7227cb3e61,0x951203083f7501a0612a,0x7742fa1c4e6c190b2150,0x1f8344a09b11769093c8,0x67425f4f5000084fea9,0x2f74e664386178b31c15,0x73f1bd8287fc7fd2f8c3,0x4dd23062d4f2a0f18b4a,0x292c4355107c4bd14f31,0xdef4dcf2b6a2412be479,0x2421a19a65ead411f9ba,0x4d83ebb4329073329183,0x47000049413a643b2e30,0x27000050d60be702cef3,0xdff11102af30b844dde1,0x210000e3af939f01eb5c,0x8d7d30f46052d18971c3,0x21801d6354c292ba5f2b,0x5163c131183053e92801,0xd2bafed009443e224a4,0x3a1037a88c420fe32810,0x2891851167c375205d62,0xc31bde521931efc0432c,0x9888e204713135814b94,0xc300fa44a11409d00a52,0x3dd2b5a9cf28750c9cd0,0x3e920df93dab76db8cd8,0x50ca8ed0d2820a7456b0,0x6574f87156ac5613d131,0xbf43198a820000c179e4,0x492be7480401cd24232,0x1278c70000347d63526c],#[0xd0413a2366dbe313d8b3,0x3c1c46e400e004b2bad3,0x87c8e3d285e1dcc44da2,0xc1d11052e6183ab31368,0x60a49e93634351c1f3d4,0x5958cca4e1918a52adba,0x405047a2775264b0d402,0x5f01e7917d2c494a45b4,0x43102572070ab1332cb0,0x5b6370048a140302f9e3,0xfe32ec000003a950cf01,0xa23972250e2081b0d821,0x917ba8847b0040123204,0x9900000000f325847281,0xca501224fa9b19f1b3bc,0x705411835f79fe203ae1,0xe8944f00006199a05a90,0x3549ce32b7a295f40d42,0xc1fba7b402a3c303811b,0x3b4161644bb529b19c92,0xb4743344d053c6000044,0x6af407b03fb842d4c550,0xab2300851ee32e10db11,0xbf92c7615d0af7f4cd01,0x45717121cd1c4d014e43,0x33f741e5124d81]]
def g127D10 := limbs80 #[#[0x60ff583fd30ff4437d65,0xfd61ff507fd31ff487ff,0x3ff63ff58ffd43ffd87,0x359d599213a8b31d4370,0x624385047aa6728ee047,0x1c2438a080c0384000f1,0x238705161840300e10,0x4384060071c3c5890e14,0x70789062830501593162,0x30058c1c14587060091d,0xf16243820a00e1e2438,0x284803c5890e082801c7,0xe2c385060041c3c18708,0x8b0e141090038e1]]
def g127H10 := limbs80 #[#[0x600160525000b13100c,0x15420107140d00080100,0x1117f08010e190a0500,0x20a0c60000d000707,0x10004913011ea3011602,0x80f5d03440511090406,0xe680004180958b133f01,0x784408e38be3d8003833,0xf3093058646e6e835000,0x29266550f5c0002a21c3,0x70423e1d09ea6efe69b0,0x2c5083881916a0d0001a,0xe7e2a98c801994b017b,0x728a09f47c1b2a039,0x2b021c00001684e221d,0xf3c368b08d4329d0a614,0x11830c10c8a6ce6f47f7,0x8f3af28e086c922316e8,0xab65280551571674741c,0x581b9190f68e80157ccd,0xf566cb9d8d5b894e96a2,0xec39b0385e8001b3353e,0x1f83156364b0006a6a53,0x1a00044ba2a8cc8000d0,0x88eaac000000a1080030,0x91808a78420b80000007,0x7b6800346200095371af,0x86b4000000222cc26028,0x7c3359376f3d2cac8715,0x3067a42040f21c526aa,0x340001058000e7700000,0xd8400102f313711b8242],#[0x27e318590d0692724ea,0xd28ccdca726c611062dc,0xc00000000020ec37edb7,0x6c7aafaa48000000191,0x1a6f000090fcdbc3f00,0x3e1c001678f07dca80,0x492a3b2aed1140018300,0x52711606a4e053a83,0x9e8316999280004a4749,0x1404215e43628024299f,0xdc000e02bc1380612049,0x5b04c1cd2a3aa5e13820,0x97cbf148f90b994cb3e,0x432750c57d095a869005,0x7abc00000053a897452b,0x617bf4d8000af1084722,0x490a48c342444178786b,0xf243e0497945a0726785,0xb9763b20524ed315951c,0x112a7ff04e48253c28d5,0x495a0f3c5742244b4499,0x66ca26114db48000]]
def g127D11 (j : Nat) := if j=0 then 0x28818408037f else 0
def g127H11 := limbs80 #[#[0xd538793e46e00b62346,0x8018da71400149450000,0x4180000ab003c68400d4,0xce2597601]]
def g127L : Nat → Packing
  | 5 => (2,6,6,0,0,3,0,g127D5)
  | 6 => (223,5,6,0,0,11,0,g127D6)
  | 7 => (1938,4,6,0,0,14,0,g127D7)
  | 8 => (1338,3,6,0,0,16,0,g127D8)
  | 9 => (178,2,6,0,0,14,0,g127D9)
  | 10 => (13,1,6,0,0,10,0,g127D10)
  | 11 => (1,0,6,0,0,0,0,g127D11)
  | _ => emptyPacking
def g127I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 5 0 6 1 1 g127H6
  | 7 => lookupWord 67 673 5 13 8 1 g127H7
  | 8 => lookupWord 595 2939 9 16 11 1 g127H8
  | 9 => lookupWord 444 1931 10 16 11 1 g127H9
  | 10 => lookupWord 62 293 8 13 8 1 g127H10
  | 11 => lookupWord 5 29 3 9 4 1 g127H11
  | _ => fun _ => none
def g127 : Forest := ⟨127,11,fun i => g127Y[i]?.getD (0,0),g127C,g127A,g127L,g127I⟩
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

private def wheelRows5Page0 : Array Nat := #[106863099273296,106738597519440]
private def wheelRows5 : Array (Array Nat) := #[wheelRows5Page0]
private def wheelRows6Page0 : Array Nat := #[16681857454642,43091962104860,25503820418092,90259039797313,71506927829064,71506927829064,72610751201352,90259039797313,25641260941633,16819297452353,16819297452610,25641260941633,16819297452610,43091962104860,25641260941633,72632226299976,43091962104860,25503820418092,16819297452353,25503820418092,25503820418092,71532697894984,25503820418092,25503820418092,107134739154707,107134739154707,108199890650891,25641263046977,78151295197264,108199890650891,10174798497864,25641260941633]
private def wheelRows6Page1 : Array Nat := #[25641260941633,19035567685953,25641260941633,16819297452353,16819297452610,90271925157960,11304492335682,16819297452610,16819297452610,99037952950337,48434547679266,30975507628835,48498972238115,30975507628835,10174798497864,29974631288912,30975507628835,30975507628835,83752065762083,48434547679266,90241859928073,84851578376754,21243214430473,83683345302291,83683345302289,15582344839971,15582344839971,14482834199090,14482834199090,15582345826866,15582345826866,30975507628835]
private def wheelRows6Page2 : Array Nat := #[30975507628835,14414112752403,14414112752403,48434547744803,48434547744803,48438842712099,48438842712099,14414112752403,14414112752403,48434547744803,48434547744803,48438842712099,48438842712099,55070372929572,55070372929572,55070372929572,55070372929572,30842361548817,106863636121110,55074667896868,84782856798481,71781809389833,38659555856922,14620274196753,30842361548817,31112948617233,31112948617233,30842361548817,30842361548817,54026947663882,38659555856922,15582345826866]
private def wheelRows6Page3 : Array Nat := #[24271164366913,24301229596744,106717137100872,107100379023117,15513624248593,118807586824226,107100380856842,106863099273296,123562990047761,55070373455916,85951090004530,14482834199090,83618919813649,16613135876369,14414112620817,48434547679266,108199890650381,30842361680403,113460705756180,30842361680403,30842361680403,30842361548817,30842361548817,48438842695971,30842227462675,48438842695971,48498972188706,30842361548817,30842361680403,30842227462675,30842227331089,30842227462675]
private def wheelRows6Page4 : Array Nat := #[15724080793609,54035000726038,84782856930067,84782856798481,48438842630178,48438842630178,48438842630178,48438842630178,31117243584592,14414112752403,55070372929572,48438842630178,14414112620817,48438842630178,84782856798481,84782856798481,84782856798481,84782857338905,84782856930067,48438842630178,48713720537122,84782856798481,14414112620817,30842361548817,30842361548817,30842361680403,28668940585997,28668940585997,31117239455761,31117239587347,79478508226569,33174530884387]
private def wheelRows6Page5 : Array Nat := #[33311971869250,21178538266704,33311971872848,79509509508106,83618919694401,28961266534409,30850951483409,24271164366913,106829275989518,99037953199117,30842361680403,31125829390353,15857226875426,30842361548817,108199892484618,31125829521425,30842361680403,55070372929572,30842361680403,85951089017635,30842361680403,40746438778914,14452655129122,48438842695971,14414112620817,83752065762083,30975507628835,30975507628835,48498972188706,48498972188706,125439117107236,125439117107236]
private def wheelRows6Page6 : Array Nat := #[125439117107236,30842361680403,48498973237298,48498973237298,39668385210402,30842227462675,28694947127361,11033773170753,11033773170753,30842227462675,30842227462675,48434547744803,48498973237298,30915382222882,30842361680403,71541287291972,71541287291972,31082879717393,14414112620817,74827122743322,74827122743322,74827122743322,72924283474498,74827122743322,71506911051848,73748918190160,14414112620817]
private def wheelRows6 : Array (Array Nat) := #[wheelRows6Page0,wheelRows6Page1,wheelRows6Page2,wheelRows6Page3,wheelRows6Page4,wheelRows6Page5,wheelRows6Page6]
private def wheelRows7Page0 : Array Nat := #[71541288091728,75111462994707,16681857454642,21243214430529,16819297452353,72610751201352,14482834199090,14482834199090,30975507628835,14482834199090,14482834199090,14482834199090,14482834199090,14482834199090,73748934836304,72878079608077,72878079608077,83752065762083,83752065762083,54035537991708,54035537991708,11304492335682,38659555856922,38659555856922,14482834199090,108199890650381,73977591235853,73977591235853,54035537991708,90241859928129,71506927829064,71506927829064]
private def wheelRows7Page1 : Array Nat := #[14620274197058,75111462994707,90241859928129,21243214430529,14620274196801,21243214430529,54035537991708,21243214430529,54035537991708,107134739153683,107134739153683,16681856401954,21105773380644,10174798497864,16681856401954,21105773380644,21243214430529,21243214430529,19035567685953,72878079608077,21243214431300,21243214430529,14620274196801,90271925157960,79509509505811,16681857454642,21243214430529,71506927829064,16819297452610,14482834199090,14482834199090,48434548715570]
private def wheelRows7Page2 : Array Nat := #[14482834199090,71506927829064,73748934836304,16819297452610,55070372929572,55070372929572,14482834199090,55070372929572,55070372929572,16681857454642,55070372929572,55070372929572,55070372929572,10174798497864,83683345186896,55070372929572,55070372929572,55070372929572,55070372929572,55070372929572,55070372929572,55070372929572,55070372929572,71506927829064,10174798497864,38693915593756,71778567980558,71778567980558,83683345302291,83683345302291,10204980707649,55070373455916]
private def wheelRows7Page3 : Array Nat := #[55070373455916,71778567980558,71778567980558,38659555856922,38659555856922,15582345826866,15582345826866,107100379022862,107100379022862,73977591236110,73977591236110,16819297452353,55070372929572,55070372929572,55070372929572,15582345826866,55070372929572,55070372929572,15582344839971,15582344839971,14482834199090,30975507628835,55070372929572,55070372929572,10204980707649,55070372929572,55070372929572,55070372929572,14414112752403,14414112752403,55074667896868,54044127399956]
private def wheelRows7Page4 : Array Nat := #[55070372929572,14414112752403,14414112752403,55070372929572,55070372929572,55070372929572,55070372929572,55070372929572,55070372929572,16681856401954,15582344774178,83683345302291,14413978534675,14414112752403,10204980707649,25503819891748,84782856930067,84782856930067,14414112752403,14414112752403,14414112752403,14414112752403,14414112752403,48438842695971,14414112752403,48438842695971,14414112752403,55070372995365,55070104559909,71506927829064,83618919694401,83618919694401]
private def wheelRows7Page5 : Array Nat := #[14620274196801,14620274196801,55074667896868,83683345302291,55070372929572,55070372929572,55070372929572,83683345186896,55070372929572,55070372929572,55070372929572,14414112752403,48438842695971,14414112752403,14414112620817,14414112752403,14414112752403,48438842695971,48438708478243,48438842695971,14414112752403,48438842695971,14414112752403,10204980707649,55070372929572,55070372929572,55070372929572,55070372929572,83683345186896,55070372929572,55070372929572,83683345302291]
private def wheelRows7Page6 : Array Nat := #[14414112620817,55070372929572,14414112620817,55070372929572,55070372929572,48438842695971,55070372929572,54035537465364,55070372929572,55070372929572,38693915593756,90241859928129,15719785824834,78129834508360,71778567980813,24404308790316,24404308790316,31164689548356,38659555856922,38659555856922,15582345826866,15582345826866,88241177039379,88241177039379,15719785824577,43298123154500,15582345826866,55070373455916,90241859928129,71506927829064,72610751201352,15719785824577]
private def wheelRows7Page7 : Array Nat := #[90241859928129,90241859928129,15719785824834,55070373455916,55070373455916,55070373455916,71541288091728,77060337844304,38659555856922,15582345826866,71541288091728,73748934836304,71778567980558,90241859928129,15719785824834,15719785824834,38659555856922,74861348274256,38659555856922,15582345826866,15582345826866,71549878157392,15582345826866,15582345826866,123562988081683,123562988081683,108199890650638,90241862033473,77051783569488,108199890650638,16613135876369,38693915067412]
private def wheelRows7Page8 : Array Nat := #[10174798497864,16613135876369,90241859928129,90241859928129,90241859928129,88034213183553,71778567980558,38900076643396,90241859928129,15719785824834,90271925157960,15513624248593,43091961578516,15513624248593,15719785824834,11304492335682,15582345826866,15719785824834,15719785824577,90241859928129,15719785824834,55070372929572,15582345826866,55070372929572,55070372929572,15582345826866,15582345826866,48438843682866,15582345826866,72610751201352,15582345826866,55070372929572]
private def wheelRows7Page9 : Array Nat := #[55070372929572,55070372929572,72610751201352,11278621870152,72610751201352,15582344839971,30975507628835,15582344839971,15582344839971,33174530884387,15582344839971,71506927829064,73748934836304,15582344839971,15582344839971,73748934836304,15582344839971,30975507628835,48498972238115,30975507628835,21178538266704,30975507628835,30975507628835,14482834199090,55345250836516,30975507628835,55070372929572,55070372929572,55070372929572,55070372929572,55070372929572,55070372929572]
private def wheelRows7Page10 : Array Nat := #[55070372929572,15582344839971,83752066748978,83752066748978,55070373455908,55070373455908,22144920650531,75922221318216,55070372929572,73748934836304,73748934836304,73748934836304,21178538266704,16613135876369,14414112620817,55070372929572,83752065762083,30842227462675,30842361680403,11304492335682,30842361548817,15582345826866,30842361680403,43091961578516,30842361680403,30842361680403,30842361680403,33041384804881,15582344839971,30842361680403,30842361680403,30842361680403]
private def wheelRows7Page11 : Array Nat := #[30842361680403,33041384804881,15582344839971,30842361680403,72610751201352,15719785824834,74861348274256,73748934836304,54044127399956,83752065762083,83752065762083,55070372929572,83752065762083,83752065762083,30842361680403,30842361548817,30842361680403,30842361680403,15582344839971,30842227462675,15582344839971,30842361680403,11304492335682,11304492335682,55070372929572,73748934836304,11304492335682,55070372929572,30842361548817,55070372929572,30842361548817,55070372929572]
private def wheelRows7Page12 : Array Nat := #[55070372929572,77060405084240,55070372929572,55070372929572,15582345826866,72610751201352,55070372929572,55070372929572,55070372929572,125439117107236,125439117173029,123575873180182,54035537465364,125439117107236,125439117107236,125439117107236,125439117107236,125439117107236,125439117107236,125439117173029,30842227462675,24404308329765,90241859928129,30842361680403,48438708478243,48438708478243,30842227462675,30842227331089,30842361548817,71541288091728,48438842695971,71506927829064]
private def wheelRows7Page13 : Array Nat := #[30842361680403,75922221318216,45230855428122,123562988081683,123562988081683,30842361680403,107100379022605,108199890650638,55070372995365,30842361680403,30842361680403,14414112752403,30842361680403,30842361680403,30842361680403,79203626205249,30842361680403,30842361680403,30842361680403,30842361548817,15719785824577,55070372929572,14414112752403,14414112752403,71506927829064,10204980707649,55345250836516,55070372929572,55070372929572,14620274197058,30842361680403,30842361680403]
private def wheelRows7Page14 : Array Nat := #[72610751201352,11304492335682,55070372929572,74852758339664,73748934836304,55070372929572,55070372929572,55070372929572,55070372929572,55070373455908,71506927829064,55070373455908,79203626205249,71541288091728,88034213183553,55070372929572,55070372929572,55070372929572,30842361680403,55070372929572,48438842695971,30842361680403,48438842695971,48438842695971,30842361680403,30842361680403,30842361680403,30842361680403,30842361680403,30842361680403,30842361680403,30842361680403]
private def wheelRows7Page15 : Array Nat := #[30842361680403,30842361680403,30842361680403,30842361680403,48438842695971,71541288091728,30842361680403,48438842695971,55070372929572,14414112752403,14620274196801,55070372929572,55070372929572,55070372929572,83683345186896,48438708478243,14590091987016,48438842695971,48438842695971,48438842695971,55070372929572,55070372929572,31112948617296,55070372929572,18970891522128,55070372929572,30842361548817,30842361548817,30842361548817,30842361548817,30842361548817,71506927829064]
private def wheelRows7Page16 : Array Nat := #[30842361548817,55070372929572,55070372929572,55070372929572,83683345186896,30842361680403,55070372929572,55070372929572,71506927829064,10174798497864,71506927829064,30842361680403,71506927829064,71506927829064,55070372929572,14414112752403,14620274196801,55070372929572,30842361680403,15719785824834,55070372929572,73748934836304,55070372929572,30842361680403,30842227462675,30842361680403,48438708478243,55070373455908,55070372929572,30842361680403,55070373455908,71541288091728]
private def wheelRows7Page17 : Array Nat := #[88034213183553,30842361680403,75922221318216,75922221318216,30842361680403,30842361680403,48438842695971,48438842695971,71541288091728,30842361680403,30842361680403,30842227462675,48438842695971,71541288091728,55070372929572,71541288091728,71541288091728,18970891522128,71541288091728,71541288091728,55070372929572,55070372929572,55070372929572,71541288091728,55070372929572,55345250836516,30842361548817,31112948617296,30842361548817,55070372929572,71541288091728,71541288091728]
private def wheelRows7Page18 : Array Nat := #[71541288091728,71541288091728,71541288091728,18970891522128,55070372929572,18970891522128,71541288091728,55070372929572,14414112752403,14620274196801,14414112752403,14414112752403,71506927829064,10204980707649,55070372929572,30842361680403,15719785824834,30842361680403,30842361680403,72610751201352,11304492335682,55070372929572,55070372929572,30842361680403,55070373455908,71506927829064,55070373455908,79203626205249,30842361548817,71541288091728,75922221318216,30842227331089]
private def wheelRows7Page19 : Array Nat := #[30842361548817,71541288091728,55070372929572,75922221318216,30842361548817,71541288091728,48438842695971,48438842695971,48438842695971,55070372929572,48438842695971,54035537465364,54035537465364,30842361680403,55070372929572,55070373455908,55070373455908,30842361680403,125439117107236,55070372929572,30842361680403,55070372929572,55070372929572,14414112620817,15582344774178,30842361680403,55070373455908,10174798497864,55070373455908,10174798497864,10174798497864,55070373455908]
private def wheelRows7Page20 : Array Nat := #[16613135876883,14414112620817,55070373455908,15582344774178,55070373455908,30842361680403,71506927829064,79203626205249,71541288091728,48438842695971,55070372995365,90241859928129,71541288616016,88034213183553,55070373455908,55070373455908,55070373455908,30842227462675,30842227462675,96864665944129,96864665944129,30842227462675,79203626205249,79203626205249,30842361680403,71541288091728,79203626205249,79203491987521,30842227462675,79203491987521,79203491987521,48438708478243]
private def wheelRows7Page21 : Array Nat := #[79203491987521,79203491987521,48438842695971,71506927829064,55070372929572,55070372929572,14414112752403,14620274196801,55070372929572,30842361680403,15719785824834,55070372929572,73748934836304,55070372929572,30842361680403,30842361680403,88034213183553,30842361680403,75922221318216,74852760313936,55070372929572,14414112752403,54035000726038,14414112752403,91371436769545,14414112620817,48443137597474,48438842630178,48438842630178,48438842630178,55070372929572,48438842630178]
private def wheelRows7Page22 : Array Nat := #[48438842630178,48438842630178,48438842630178,48438842630178,48438842630178,48438842630178,55070372929572,48438842630178,48438842630178,14414112620817,55070372929572,55070372929572,55070372929572,48438842630178,48438842630178,48438842630178,48438842630178,48438842630178,48438842630178,48438842630178,55070372929572,55070372929572,48438842630178,48438842630178,48438842630178,14414112620817,14414112620817,9938688688194,9938688688194,14414112620817,48438842630178,55070372929572]
private def wheelRows7Page23 : Array Nat := #[48438842630178,48438842630178,30842361680403,30842361680403,33041384804369,71506927829064,30842361548817,48438842630178,54035000726038,30842363654161,54035000726038,54035000726038,55070372929572,30975507563042,55070372929572,10174798497864,29974631288912,31112948617296,55070372929572,55070372929572,83752066748978,30842361548817,125439117107236,125439117107236,125439117107236,30842361548817,30842361680403,79207921238082,79207921238082,77060404953168,48438842630178,14414112620817]
private def wheelRows7Page24 : Array Nat := #[30842361548817,48438842630178,30842361548817,48438842630178,48438842630178,30842361548817,48438842630178,30842361548817,10174798497864,71506927829064,30842361680403,30842361680403,30842361548817,71506927829064,30842361548817,30842361548817,30842361548817,30842361548817,71506927829064,30842361548817,118807586807842,118807586807842,118807586807842,118807586807842,118807586807842,118807586807842,30842361548817,48438842630178,48438842630178,55070372929572,30842361680403,30842361548817]
private def wheelRows7Page25 : Array Nat := #[48438842630178,118807586807842,48438842630178,10174798497864,48438842630178,48438842630178,10174798497864,48438842630178,48438842630178,48438842630178,48438842630178,48438842630178,71506927829064,48438842630178,48438842630178,48438842630178,48438842630178,48438842630178,29974631288912,48438842630178,48438842630178,48438842630178,48438842630178,48438842630178,71506927424066,48438842630178,48438842630178,48438842630178,48438842630178,48438842630178,10174798497864,10174798497864]
private def wheelRows7Page26 : Array Nat := #[48438842630178,10174798497864,48438842630178,48438842630178,48438842630178,48438842630178,48438842630178,14414112620817,30842361548817,30842361548817,30842361548817,30842361548817,30842361548817,30842361548817,48438842630178,55070372929572,118807586807842,71506927829064,71506927829064,30842361548817,71506927829064,30842361548817,71541288091728,55070372929572,30842361680403,48438842630178,48438842630178,48438842630178,48438842630178,14414112620817,48438842630178,14414112620817]
private def wheelRows7Page27 : Array Nat := #[14414112620817,14414112620817,14414112620817,30842361548817,30842361548817,30842361548817,30842361548817,71506927829064,30842361548817,30842361548817,30842361548817,30842361548817,30842361548817,71506927829064,48438842630178,48438842630178,71506927829064,55070372929572,118807586807842,48438842630178,48438842630178,30842361548817,28669208758281,48438842695971,48438842630178,48438842630178,71506927829064,71506927829064,71506927829064,71506927829064,71506927829064,71506927829064]
private def wheelRows7Page28 : Array Nat := #[71506927829064,48438842630178,48438842630178,14414112620817,48438842630178,30842361548817,48438842630178,48438842630178,30842361548817,48438842630178,30842361548817,30842361548817,30842361548817,88271242397198,16613135876369,106829275989518,43298123155010,55070373455916,54035000726038,115599061945358,114771190221838,45230317767694,45230317767694,45230317767694,30842361680403,45230317767694,54035000726038,45230317767694,45230317767694,45230317767694,55070372929572,48438843682866]
private def wheelRows7Page29 : Array Nat := #[79203626205249,90271925141769,55070372929572,83618919694401,48438843682866,31112948617296,31112948617296,30842361680403,55070372929572,14414112620817,90271925141769,21002692591881,30842361680403,55070372929572,55070372929572,106829275726346,55070372929572,54310415372308,55070372929572,55070372929572,55070372929572,125439117107236,55070372929572,55070372929572,55070372995365,48438708478243,48438708478243,48438708478243,48438708478243,48438708478243,48438708478243,48438708478243]
private def wheelRows7Page30 : Array Nat := #[48438708478243,48438708478243,48438708478243,30842361680403,48438842630178,71506927829064,79203626205249,71541288091728,48438842630178,30842361680403,48713720537122,10174798497864,71506927829064,18970891522128,48438842630178,48438842630178,55070372929572,55070372929572,48438842630178,48438842630178,48438842630178,79203626205249,48438842630178,48438842630178,14414112620817,48438842630178,48438842630178,48438842630178,55070372929572,30842361680403,48438842630178,14414112620817]
private def wheelRows7Page31 : Array Nat := #[55070372929572,48438842630178,48438842630178,106803505530890,48438842630178,84782856798481,48438842630178,48438842630178,55070372929572,55070372929572,48438842630178,55070372929572,48438842630178,79203626205249,79203626205249,79203626205249,79203626205249,71541288091728,79203626205249,30842361680403,79203626205249,79203626205249,79203626205249,96864531726401,71541288091728,96864531726401,79203626205249,48438842630178,114525842006081,49598484709649,14414112620817,30842361548817]
private def wheelRows7Page32 : Array Nat := #[31117239455761,30842361548817,30842361548817,30842361680403,71541288222800,73748934836304,33041384804369,30842363654161,54035000726038,54035000726038,45230317767694,15719785824834,72610751201352,79207921238082,30842363654161,30842361680403,31117239455761,31117239587347,30842361548817,30842361680403,72610751201352,15719785824834,55070372929572,83752066748978,28944086665225,83618919813651,30842361680403,31112948617296,31112948617296,28669208758281,30842361680403,31112948617296]
private def wheelRows7Page33 : Array Nat := #[31112948617296,73748934836304,21178538266704,73748934836304,73748934836304,55070372929572,79207921238082,79207921238082,73748934836304,30842361548817,14414112620817,48438842695970,48438842695970,48438842695970,55070372929572,31117239587347,48438842630178,48438842695970,21178538264648,30842361680403,48438842630178,14590091987016,48438842695970,48438842630178,48438842695970,72610751201352,72610751201352,72610751201352,72610751201352,75922221318216,75922221318216,38659018196494]
private def wheelRows7Page34 : Array Nat := #[45230317767694,45230317767694,15582344839971,15719785824834,73748934836304,28686388627465,33067255269385,28669208758281,28669208758281,79445084017171,33311971869250,21178538266704,33311971872848,72610751201352,28669208758281,33311971872848,28669208758281,15582344839971,15719785824834,18730369943054,71541288091728,73748934836304,21178538266704,30850951483409,31125829390353,31125829390353,30850951483409,30850951483409,30850951614481,71549878157392,77060404953168,30850951483409]
private def wheelRows7Page35 : Array Nat := #[30850953588753,30842361548817,30842361548817,30842361548817,30842361548817,30842363654161,43091961578516,40892938322964,28669208758281,30842363654161,28669209021453,30842361680403,30842361548817,30842361548817,30842361680403,30842361680403,30842361548817,15582344839971,30842361680403,73748934967376,28965666292290,33041384804369,33041384804369,123562988081683,30842361548817,30842363654161,48438842630178,30842361680403,30850951483409,30842361680403,30842361680403,30842361680403]
private def wheelRows7Page36 : Array Nat := #[48438842630178,30842361680403,30842361680403,48438842630178,48438842630178,48438842630178,30842361680403,48438842695971,72610751201352,30842361680403,48438842630178,30842361680403,71506927829064,30842361548817,72610751201352,72610751201352,30842361548817,72610751201352,30842361548817,54035000726038,54035000726038,54035000726038,71506927829064,72610751201352,11278621870152,72610751201352,72610751201352,45230317767694,30850951483409,30842361680403,73748934836304,33041384804369]
private def wheelRows7Page37 : Array Nat := #[28686388627465,28669208758281,30842361680403,45230317767694,48438842695971,15719785824834,73748934836304,48438843682866,45230317504522,45230317504522,48438842695971,48438842695971,48438842695971,30842361548817,48438842695971,30842361680403,118807586824226,45230317767694,30842363654161,30842363654161,45230317767694,30842363654161,45230317767694,45230317767694,45230317767694,45230317767694,45230317767694,54035000726038,54035000726038,45230317767694,14414112752403,83627509628993]
private def wheelRows7Page38 : Array Nat := #[48438842695971,72610751201352,79207921238082,83627509760065,30842361548817,30842363654161,79207921238082,79207921238082,30842361548817,73748934836304,79207921238082,45230317767694,45230317767694,45230317767694,14414112752403,30842361680403,30850951483409,48438842695971,14414112752403,30850951614481,55070372929572,30842361548817,55070372929572,30842361680403,55070372929572,55070372929572,55070372929572,30842361548817,30842361548817,55070372929572,55070372929572,55070372929572]
private def wheelRows7Page39 : Array Nat := #[30842361680403,15582344839971,30842361680403,30842361680403,30842361680403,125439117107236,125439117107236,125439117107236,101211105858067,48438842630178,30842361680403,55070372929572,30842361680403,72610751201352,48438842695971,30842361680403,30842361680403,30842361680403,30842361680403,48438842695971,30842361680403,101211105858067,30842361680403,30842361680403,72610751201352,72610751201352,71506927829064,72610751201352,72610751201352,11278621870152,30842361680403,55070372929572]
private def wheelRows7Page40 : Array Nat := #[30842361548817,48438842695971,14414112620817,48438842695971,48438842695971,72610751201352,30850951614481,30842361680403,30842361680403,48438842695971,72610751201352,30842361680403,30842361548817,30842361680403,72610751201352,71506927829064,71506927829064,71506927829064,71506927829064,72610751201352,11278621870152,71506927829064,72610751201352,15582344839971,30975507628835,83752066748978,83752066748978,55070372929572,55070372929572,83752066748978,15582344839971,28669208758281]
private def wheelRows7Page41 : Array Nat := #[33311971869250,28669208758281,55070372929572,55070372929572,55070372929572,55070372929572,55070372929572,90241859913737,83752066748978,55070372929572,28669208758281,55070372929572,55070372929572,55070372929572,33041384804369,55070372929572,125439117107236,125439117107236,125439117107236,125439117107236,21178538266704,31112948617296,96877416824900,28944086665225,83618919813651,28669208758281,83618919694401,75922221318216,55070372929572,31112948613698,55345250836516,55070372929572]
private def wheelRows7Page42 : Array Nat := #[30842361680403,31112948617296,31112948617296,71541288091728,21178538266704,73748934836304,30975507563042,30975507563042,48498972172322,30975507563042,30975507563042,10174798497864,14590091987016,55070372929572,55070372929572,55070372929572,55070372929572,55070372929572,18970891522128,21178538266704,21178538266704,31112948617296,31112948617296,30975507563042,31112948617296,31112948617296,72610751201352,55070372929572,15719785824834,55070372929572,15719785828432,71541288091728]
private def wheelRows7Page43 : Array Nat := #[73748934836304,33174530818594,55070372929572,55070372929572,55070372929572,30842361680403,55070372929572,71541288091728,71541288091728,71541288091728,71541288091728,20929392939546,71541288091728,30842361680403,72610751201352,73748934836304,71541288091728,73748934836304,30842361680403,30842227462675,28669208758281,30842227462675,30842227462675,30842227462675,96868960976962,96868960976962,30842227462675,30842227462675,125439117107236,54035537465364,123562988081683,54310415372308]
private def wheelRows7Page44 : Array Nat := #[30842361680403,125439117107236,125439117107236,125439117633572,125439117633572,30842361680403,125439117107236,125439117107236,125439117107236,30842361548817,30842361548817,125439117107236,28669208758281,30842361548817,72610751201352,79207921238082,74852758208592,48438842695971,30842361548817,55070372929572,72610751201352,74852758208592,24490008383568,77060404953168,28669208758281,30842361548817,125439117107236,55070372995365,30842361548817,30842361548817,125439117173029,30842361548817]
private def wheelRows7Page45 : Array Nat := #[54035000726038,54035000726038,54035000726038,54035537465364,48438842695971,71506927829064,79203626205249,71541288091728,48438842695971,48438842695971,72610751201352,71541288091728,21178538266704,73748934836304,118807586824226,55070372929572,85951090004530,83752065696290,99037953199117,55070372929572,79207921238082,79207921238082,79207921238082,55070372929572,79207921238082,55070372929572,55070372929572,55070372929572,125439117107236,11033907388481,125439117107236,125439117107236]
private def wheelRows7Page46 : Array Nat := #[30842361680403,30842361680403,55070372929572,79207921238082,79207921238082,30842361548817,30842361680403,30842361680403,30842361548817,55070372929572,55070372929572,48438842695971,30842361548817,48438843682866,55070372929572,125439117107236,30842361548817,83752065696290,55070372929572,55070372929572,30842361548817,99037952935945,125439117107236,125439117107236,28669208758281,79207921238082,79207921238082,79207921238082,71541288091728,79207921238082,48438842695971,79207921238082]
private def wheelRows7Page47 : Array Nat := #[79207921238082,73748934836304,79207921238082,71541288091728,73748934836304,48438843682866,33174530818594,85951088951842,30842361680403,55070372929572,55070372929572,101211105726481,30842361548817,125439117107236,125439117107236,125439117107236,125439117107236,28669208758281,30842361680403,125439117107236,96869095194690,55070372929572,48438842695971,48438842695971,71506927829064,79203626205249,55070372929572,48438843682866,48438842695971,30842361548817,72610751201352,79207921238082]
private def wheelRows7Page48 : Array Nat := #[48713720537122,79203626205249,48438842630178,77026044690504,48438842630178,48438842630178,96877416824900,75922221318216,118807586807842,48713720537122,48713720537122,21178538264648,48438842630178,10174798497864,48438842630178,14590091987016,12382445244496,48438842630178,18970891522128,15693915361360,48438842630178,48438842630178,48438842630178,48438842695970,48438842695970,71506927829064,74852758208592,48438842630178,48438842630178,30842361548817,71506927829064,71506927829064]
private def wheelRows7Page49 : Array Nat := #[71506927829064,75922221318216,75922221318216,71541288091728,74852758208592,15582345826866,48438843682866,48438843682866,48438843682866,72610751201352,48438842695970,48438842630178,48438842630178,14414112620817,48438842630178,48438842695970,72610751201352,14414112620817,30842361548817,30842361548817,30842361548817,30842361548817,30842361548817,71506927829064,30842361548817,48438842630178,30842361680403,30842361680403,30842361680403,74852758208592,30842361680403,30842361680403]
private def wheelRows7Page50 : Array Nat := #[30842361680403,30842361680403,30842361680403,83683345186896,31117239587347,71506927829064,74852758208592,48438842695970,10174798497864,48438842630178,48438842630178,10174798497864,48438842630178,14590091991112,48438842630178,14590094092360,48438842630178,55070372929572,48438842630178,48438842630178,48438842630178,48438842630178,31082879717393,48438842630178,48438842630178,48438842630178,48438842630178,48438842695971,48438842695971,114771191011354,48438842695970,48438842695970]
private def wheelRows7Page51 : Array Nat := #[48438842630178,30842361680403,48438842630178,30842361548817,55070372929572,30842361680403,45230854375434,48438842695971,48438842630178,15582344774178,15582344774178,30842361548817,48438842630178,30842361548817,74827122743322,74827122743322,74827122743322,74827122743322,74827122743322,30842361548817,10204980707649,10204980707649,10204980707649,48438842695970,48438842695970,48438842695970,55070372929572,48438842695970,48438842695970,48438842630178,48438842630178,72610751201352]
private def wheelRows7Page52 : Array Nat := #[72610751201352,48438842695970,48438842695970,73714557796424,73714557796424,48438842695970,48438842695970,48438842695970,71506927829064,48438842630178,71506927829064,71506927829064,71506911051848,14414112620817,71506911051848,71506911051848,48438842695970,71506927829064,72610751201352,30842361680403,72610751201352,72610751201352,48438842630178,48438842630178,48438842630178,30842361548817,48438842630178,10174798497864,10174798497864,55070372929572,30842361680403,30842361680403]
private def wheelRows7Page53 : Array Nat := #[48438842630178,48438842630178,14590091987016,14590091987016,48438842630178,30842361548817,48438842630178,31117239455761,48438842630178,48438842695970,71506927829064,72610751201352,14414112620817,30842361548817,30842361548817,15582345826866,30842361680403,71506927829064,71506927829064,71506927829064,71506927829064,71506927829064,71506927829064,30842361548817,71506927829064,71506927829064,71506927829064,48438842630178,71506927829064,71506927829064,72610751201352,71506927829064]
private def wheelRows7Page54 : Array Nat := #[72610751201352,72610751201352,72610751201352,73714557796424,73714557796424,71506927829064,72610751201352,55070372929572,48438842630178,48438842630178,71506927829064,71506927829064,71506927829064,72610751201352,72610751201352,75922221318216,71506927829064,75922221318216,72610751201352,48438842630178,75922223423560,90241859913737,30842361680403,14414112620817,14414112620817,14414112620817,73714557796424,73714557796424,14414112620817,75922204541000,75922204541000,48438842695970]
private def wheelRows7Page55 : Array Nat := #[14414112620817,84782856798481,48438842695970,48438842630178,48438842630178,31117239455761,71506927829064,71506927829064,71506927829064,72610751201352,72610751201352,75922221318216,71506927829064,75922221318216,72610751201352,30842361548817,30842361680403,30842361680403,88034213183553,48438842630178,30842361548817,77060404953168,48438842695971,73748934836304,55070372929572,30842361548817,83623214727234,83618919694401,48438842630178,83623214727234,71541288091728,71541288091728]
private def wheelRows7Page56 : Array Nat := #[77060337844304,73748934836304,63853580847113,48438842695971,48438842695971,15582344774178]
private def wheelRows7 : Array (Array Nat) := #[wheelRows7Page0,wheelRows7Page1,wheelRows7Page2,wheelRows7Page3,wheelRows7Page4,wheelRows7Page5,wheelRows7Page6,wheelRows7Page7,wheelRows7Page8,wheelRows7Page9,wheelRows7Page10,wheelRows7Page11,wheelRows7Page12,wheelRows7Page13,wheelRows7Page14,wheelRows7Page15,wheelRows7Page16,wheelRows7Page17,wheelRows7Page18,wheelRows7Page19,wheelRows7Page20,wheelRows7Page21,wheelRows7Page22,wheelRows7Page23,wheelRows7Page24,wheelRows7Page25,wheelRows7Page26,wheelRows7Page27,wheelRows7Page28,wheelRows7Page29,wheelRows7Page30,wheelRows7Page31,wheelRows7Page32,wheelRows7Page33,wheelRows7Page34,wheelRows7Page35,wheelRows7Page36,wheelRows7Page37,wheelRows7Page38,wheelRows7Page39,wheelRows7Page40,wheelRows7Page41,wheelRows7Page42,wheelRows7Page43,wheelRows7Page44,wheelRows7Page45,wheelRows7Page46,wheelRows7Page47,wheelRows7Page48,wheelRows7Page49,wheelRows7Page50,wheelRows7Page51,wheelRows7Page52,wheelRows7Page53,wheelRows7Page54,wheelRows7Page55,wheelRows7Page56]
private def wheelRows8Page0 : Array Nat := #[71541288091728,55070372929572,55070372929572,55070372929572,55070372995365,55070372929572,55070372929572,55070372929572,55070372929572,55070372929572,55070372929572,55070372929572,55070372929572,55070372929572,71506927829064,55070372929572,55070372929572,55070372929572,55070372929572,71506927829064,55070372929572,55070372929572,55070372929572,55070372929572,55070372995365,88254062137878,54035537465364,55070372929572,55070372929572,55070372929572,55070372929572,55070372929572]
private def wheelRows8Page1 : Array Nat := #[55070372929572,55070372929572,55070372929572,55070373455916,90241859928129,75922221318216,48438842695971,48438842695971,90241859928129,74852758208592,71506927829064,71778567980301,72878079608334,24404308329765,30842361680403,30842361680403,96877685260356,45230855428122,45230855428122,88047098282052,88241177039379,88241177039379,30842361680403,55070372995365,30842361680403,55070372995365,30842361680403,30842361680403,55070372929572,55345250836516,55070372929572,55070372929572]
private def wheelRows8Page2 : Array Nat := #[55070372929572,55070372929572,71506927829064,71506927829064,55070372995365,71506929934408,55070372995365,30842361680403,55070372995365,48438842695971,30842361680403,30842361680403,71541288091728,71541288091728,30842361680403,30842361680403,30842361680403,30842361680403,48438842695971,30842361680403,15582345826866,106812095610948,55070372929572,55070372929572,55070372929572,55070372929572,83683345186896,55070372929572,48438842695971,55070372929572,55070372929572,75922221318216]
private def wheelRows8Page3 : Array Nat := #[55070372929572,55070372929572,55070372929572,55070372929572,30842361680403,55070372929572,55070372929572,48438842695971,30842361680403,48438842695971,30842361680403,55070372929572,55070372929572,74852758208592,83683345186896,55070372929572,55070372929572,55070372929572,55070372929572,55070372929572,71541288091728,55070372929572,71541288091728,55070372929572,55070372929572,55070372929572,55070372929572,55070372929572,71506927829064,88047098282052,55070372929572,55070372929572]
private def wheelRows8Page4 : Array Nat := #[55070372929572,55070372995365,55070372929572,55070372929572,55070373455908,55070372929572,55070372995365,90241859928129,55070372929572,55070372929572,55070372929572,55070372929572,55070372929572,55070372929572,55070372929572,55070372929572,48438842630178,48438842630178,48438842630178,48438842630178,48438842630178,48438842630178,48438842630178,30842361548817,48438843682866,71506927829064,83623214727234,55070372929572,55070372929572,55070372929572,55070372929572,71506927829064]
private def wheelRows8Page5 : Array Nat := #[73748934836304,55070372929572,83623214727234,55070372929572,55070372929572,30842361548817,55070372929572,55070372929572,55070372929572,30842361680403,48438842630178,48438842630178,30842361548817,48438842630178,28669208758281,30842361680403,28669208758281,48438842630178,48438842630178,48438842630178,48438842630178,71506927829064,48438842630178,74852758208592,79207921238082,90254745026628,48438842630178,48438842630178,48438842630178,48438842630178,48438842630178,48438842630178]
private def wheelRows8Page6 : Array Nat := #[48438842630178,48438842630178,48438842630178,48438842630178,48438842630178,48438842630178,48438842630178,48438842630178,55070372929572,48438842630178,48438842630178,48438842630178,79207921238082,48438842630178,79207921238082,48438842630178,48438842630178,48438842630178,48438842630178,48438843682866,88047098282052,79207921238082,79207921238082,48438842630178,48438842630178,48438842630178,48438842630178,48438842630178,48438842630178,55070372929572,48438842630178,48438842630178]
private def wheelRows8Page7 : Array Nat := #[48438842630178,48438842630178,73748934836304,74852758208592,48438842630178,48438842630178,48438842630178,48438842630178,48438842630178,48438842630178,71541288091728,48438842630178,71541288091728,55070372929572,48438842630178,79207921238082,79207921238082,48438842630178,48438842630178,30842361548817,48438842630178,30842361548817,30842361548817,30842361548817,30842361548817,30842361548817,30842361548817,48438842695971,71506927829064,71506927829064,71506927829064,48438842630178]
private def wheelRows8Page8 : Array Nat := #[48438842630178,14414112752403,79203626205249,55070373455916,55070373455916,79449379179534,79449379179534,30842361680403,48438842695971,30842361680403,48438842695971,55070372929572,55070372929572,83618919694401,55070372929572,55070372929572,55070372929572,88034213183553,48438843682866,55070372929572,55070372929572,48438842695971,55070372929572,55070372929572,83618919694401,55070372929572,55070372929572,55070372929572,79203626205249,55070372929572,55070372929572,55070372929572]
private def wheelRows8Page9 : Array Nat := #[55070372929572,55070372929572,54035537465364,55070372929572,55070372929572,55070372929572,55070372929572,55070372929572,55070372929572,55070372929572,55070372929572,48438842695971,55070372929572,55070372929572,55070372929572,55070372929572,55070373455908,55070373455908,48438842695971,55070372929572,55070372929572,55070372929572,55070372929572,55070372929572,55070372929572,48438842630178,48438842630178,48438842630178,48438842630178,55070372929572,48438842630178,48438842630178]
private def wheelRows8Page10 : Array Nat := #[48438842630178,48438842630178,48438842630178,48438842630178,48438842630178,79203626205249,48438842630178,79203626205249,48438842630178,48438842630178,55070372929572,48438842630178,48438842630178,48438842630178,48438842630178,55070372929572,48438842630178,79203626205249,79203626205249,54035537465364,54035537465364,54035537465364,54035537465364,28669208758281,31117239455761,30842361548817,30842361548817,30842361548817,30842363654161,30842361548817,30842361548817,55070372929572]
private def wheelRows8Page11 : Array Nat := #[55070372929572,30842361680403,28669208758281,55070372929572,55070372929572,55070372929572,30842361548817,55070372929572,28669208758281,48438842695970,30842361680403,48438842630178,48438842630178,31117239455761,48438842630178,30842361548817,48438842630178,30842361680403,30842361680403,30842361680403,30842361680403,28669208758281,88241177039379,30842361548817,30842361548817,30842361548817,30842361548817,28669208758281,28669208758281,30842361548817,83623214727234,83683345186896]
private def wheelRows8Page12 : Array Nat := #[79203626205249,71506927829064,30842361548817,30842361548817,30842361680403,90271925157960,30842361548817,30842361548817,30842361680403,28669208758281,30842361548817,30842361680403,83623214727234,30842361548817,30842361548817,55070372929572,30842361548817,30842361548817,55070372929572,55070372929572,72610751201352,106812095610948,30842361548817,101211105726481,30842361680403,88047098282052,30842361548817,30842361548817,55070372929572,55345250836516,30842361680403,55070372929572]
private def wheelRows8Page13 : Array Nat := #[55070372929572,30842361548817,55070372929572,55070372929572,71541288091728,74852758208592,55070372929572,55070372929572,48438843682866,55070372929572,30842361548817,30842361680403,79203626205249,30842361680403,30842361680403,72610751201352,72610751201352,72610751201352,55070372929572,55070372929572,28669208758281,28669208758281,28669208758281,55070372929572,55070372929572,55070372929572,73748934836304,28669208758281,28669208758281,28669208758281,28669208758281,28669208758281]
private def wheelRows8Page14 : Array Nat := #[30842361680403,55070372929572,55070372929572,55070372929572,88047098282052,79203626205249,55070372929572,55070372929572,71506927829064,75922221318216,55070372929572,55070372929572,55070372929572,55070372929572,30842361680403,55070372929572,28669208758281,55070372929572,55070372929572,28669208758281,28669208758281,55070372929572,55070372929572,73748934836304,73748934836304,73748934836304,73748934836304,73748934836304,73748934836304,55070372929572,88241177039379,54035537465364]
private def wheelRows8Page15 : Array Nat := #[30842361680403,55070372929572,55070372929572,55070372929572,55070372929572,55070373455908,55070373455908,30842361680403,55070372929572,55070372929572,55070372929572,55070372929572,30842361548817,30842361548817,55070372929572,28669208758281,30842361548817,30842361548817,55070372929572,55070372929572,55070372929572,30842361548817,30842361548817,30842361548817,55070372995365,30842361548817,30842361548817,30842361548817,30842361548817,30842361548817,30842361548817,28669208758281]
private def wheelRows8Page16 : Array Nat := #[30842361548817,28669208758281,30842361548817,30842363654161,54035537465364,28669208758281,28669208758281,83623214727234,83623214727234,28669208758281,83623214727234,55070372929572,15582345826866,28669209021453,55070372929572,55070372929572,55070372929572,55070372929572,55070372929572,55070372929572,55070372929572,79207921238082,30842361680403,79207921238082,30842361680403,55070372929572,55070372929572,30842361548817,55070372929572,55070372929572,99037952935945,55070372929572]
private def wheelRows8Page17 : Array Nat := #[55070372929572,30842361548817,55070372929572,28669208758281,79207921238082,79207921238082,55070372929572,79207921238082,55070372929572,28669208758281,55070372929572,55070372929572,28669208758281,30842361680403,30842361680403,28669208758281,55070372929572,30842361548817,55070372929572,30842361548817,48438842630178,48438842630178,48438842630178,48438842630178,30842361548817,48438842630178,48438842630178,48438842630178,30842361548817,48713720537122,30842361548817,48438842630178]
private def wheelRows8Page18 : Array Nat := #[48438842630178,30842361680403,30842361680403,88047098282052,48438842630178,48438842630178,30842361548817,48438842630178,30842361548817,48438842630178,48438842630178,48438842630178,48438842630178,48438842630178,48438842630178,48438842630178,48438842630178,48438842630178,79203626205249,48438843682866,48438843682866,48438843682866,48438843682866,30842361680403,88047098282052,55070372929572,55070372929572,55070372929572,55070372929572,30842361680403,55070372929572,88047098282052]
private def wheelRows8Page19 : Array Nat := #[30842361680403,30842361680403,48438842630178,48438842630178,55070372929572,55070372929572,48438842630178,48438842630178,48438842630178,48438842630178,48438842630178,114525976223809,48438843682866,48438842630178,48438842695970,48438842695970,48438842630178,55070372929572,48438842630178,48438842630178,48438842630178,48438842630178,48438843682866,83683345186896,48438842630178,55070372929572,48438842630178,48438842630178,48438842630178,73714574573640,75922221318216,48438842630178]
private def wheelRows8Page20 : Array Nat := #[75922221318216,30842361548817,48438842630178,48438842630178,71506927829064,48438842630178,71506927829064,77026044690504,55070372929572,77026044690504,30842361548817,55070372929572,55070372929572,72610751201352,55070372929572,72610751201352,48438842630178,30842361548817,30842361548817,48438842630178,48438842630178,48438842630178,30842361548817,48438842630178,48438842630178,48438842630178,75922221318216,48438842695970,48438842695970,48438842630178,30842361680403,48438842630178]
private def wheelRows8Page21 : Array Nat := #[48438842630178,48438842630178,48438842630178,48438842630178,30842361548817,48438842630178,30842361548817,30842361548817,55070372929572,48438842630178,55070372929572,30842361548817,28669208758281,48438842630178,30842361548817,28669208758281,30842361548817]
private def wheelRows8 : Array (Array Nat) := #[wheelRows8Page0,wheelRows8Page1,wheelRows8Page2,wheelRows8Page3,wheelRows8Page4,wheelRows8Page5,wheelRows8Page6,wheelRows8Page7,wheelRows8Page8,wheelRows8Page9,wheelRows8Page10,wheelRows8Page11,wheelRows8Page12,wheelRows8Page13,wheelRows8Page14,wheelRows8Page15,wheelRows8Page16,wheelRows8Page17,wheelRows8Page18,wheelRows8Page19,wheelRows8Page20,wheelRows8Page21]
def cubTag (k i : Nat) : Nat :=
  match k with
  | 5 => let j := i - 0; (wheelRows5[j / 32]?.getD #[])[j % 32]?.getD 0
  | 6 => let j := i - 4; (wheelRows6[j / 32]?.getD #[])[j % 32]?.getD 0
  | 7 => let j := i - 140; (wheelRows7[j / 32]?.getD #[])[j % 32]?.getD 0
  | 8 => let j := i - 649; (wheelRows8[j / 32]?.getD #[])[j % 32]?.getD 0
  | _ => 0
def cubRows (word : Nat) : SixRows := ⟨Fin.ofNat 512 ((word >>> 0) % 256),Fin.ofNat 512 ((word >>> 8) % 256),Fin.ofNat 512 ((word >>> 16) % 256),Fin.ofNat 512 ((word >>> 24) % 256),Fin.ofNat 512 ((word >>> 32) % 256),Fin.ofNat 512 ((word >>> 40) % 256)⟩
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


theorem lower_span {g prior i hints} (low : ∀ q, Lower g.mode (varsX q) (graphGoal q) (prior q))
    (geom : graphValid g prior = true) (blocks : ∀ k ≤ g.cap, spanOK g k 0 (g.levels k).1)
    (idx : indexedRoot g g.cap i (vars g.mask) = true) (hp : properB (targetOf g) = true)
    (ess : checkEssential (targetOf g) (vars g.mask) (graphPairs g.mask hints) = true)
    (all : (graphPairs g.mask hints).map Prod.fst = vars g.mask) :
    Lower g.mode (vars g.mask) (targetOf g) (g.cap+1) := by
  apply lower_impossible (proper_of _ hp) (essential_plain ess).1 (essential_plain ess).2 _ (root_span low geom blocks (Nat.le_refl _) idx)
  intro a ha
  apply essential_ok ess a
  rw [all]
  exact List.mem_toFinset.mpr ha


set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof5_0 : spanOK g127 5 0 2 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelLevel5 : spanOK g127 5 0 2 := wheelProof5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof6_0 : spanOK g127 6 0 2 := by
  apply spanOld
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof6_2 : spanOK g127 6 2 2 := by
  apply spanOld
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof6_4 : spanOK g127 6 4 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof6_36 : spanOK g127 6 36 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof6_68 : spanOK g127 6 68 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof6_100 : spanOK g127 6 100 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof6_132 : spanOK g127 6 132 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof6_164 : spanOK g127 6 164 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof6_196 : spanOK g127 6 196 27 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelLevel6 : spanOK g127 6 0 223 := (spanMerge (spanMerge (spanMerge wheelProof6_0 wheelProof6_2) (spanMerge wheelProof6_4 wheelProof6_36)) (spanMerge (spanMerge wheelProof6_68 wheelProof6_100) (spanMerge wheelProof6_132 (spanMerge wheelProof6_164 wheelProof6_196))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof7_0 : spanOK g127 7 0 96 := by
  apply spanOld
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof7_96 : spanOK g127 7 96 3 := by
  apply spanOld
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof7_99 : spanOK g127 7 99 41 := by
  apply spanOld
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof7_140 : spanOK g127 7 140 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof7_172 : spanOK g127 7 172 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof7_204 : spanOK g127 7 204 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof7_236 : spanOK g127 7 236 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof7_268 : spanOK g127 7 268 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof7_300 : spanOK g127 7 300 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof7_332 : spanOK g127 7 332 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof7_364 : spanOK g127 7 364 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof7_396 : spanOK g127 7 396 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof7_428 : spanOK g127 7 428 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof7_460 : spanOK g127 7 460 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof7_492 : spanOK g127 7 492 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof7_524 : spanOK g127 7 524 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof7_556 : spanOK g127 7 556 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof7_588 : spanOK g127 7 588 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof7_620 : spanOK g127 7 620 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof7_652 : spanOK g127 7 652 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof7_684 : spanOK g127 7 684 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof7_716 : spanOK g127 7 716 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof7_748 : spanOK g127 7 748 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof7_780 : spanOK g127 7 780 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof7_812 : spanOK g127 7 812 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof7_844 : spanOK g127 7 844 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof7_876 : spanOK g127 7 876 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof7_908 : spanOK g127 7 908 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof7_940 : spanOK g127 7 940 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof7_972 : spanOK g127 7 972 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof7_1004 : spanOK g127 7 1004 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof7_1036 : spanOK g127 7 1036 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof7_1068 : spanOK g127 7 1068 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof7_1100 : spanOK g127 7 1100 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof7_1132 : spanOK g127 7 1132 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof7_1164 : spanOK g127 7 1164 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof7_1196 : spanOK g127 7 1196 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof7_1228 : spanOK g127 7 1228 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof7_1260 : spanOK g127 7 1260 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof7_1292 : spanOK g127 7 1292 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof7_1324 : spanOK g127 7 1324 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof7_1356 : spanOK g127 7 1356 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof7_1388 : spanOK g127 7 1388 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof7_1420 : spanOK g127 7 1420 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof7_1452 : spanOK g127 7 1452 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof7_1484 : spanOK g127 7 1484 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof7_1516 : spanOK g127 7 1516 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof7_1548 : spanOK g127 7 1548 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof7_1580 : spanOK g127 7 1580 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof7_1612 : spanOK g127 7 1612 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof7_1644 : spanOK g127 7 1644 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof7_1676 : spanOK g127 7 1676 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof7_1708 : spanOK g127 7 1708 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof7_1740 : spanOK g127 7 1740 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof7_1772 : spanOK g127 7 1772 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof7_1804 : spanOK g127 7 1804 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof7_1836 : spanOK g127 7 1836 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof7_1868 : spanOK g127 7 1868 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof7_1900 : spanOK g127 7 1900 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof7_1932 : spanOK g127 7 1932 6 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelLevel7 : spanOK g127 7 0 1938 := (spanMerge (spanMerge (spanMerge (spanMerge (spanMerge wheelProof7_0 (spanMerge wheelProof7_96 wheelProof7_99)) (spanMerge (spanMerge wheelProof7_140 wheelProof7_172) (spanMerge wheelProof7_204 wheelProof7_236))) (spanMerge (spanMerge (spanMerge wheelProof7_268 wheelProof7_300) (spanMerge wheelProof7_332 wheelProof7_364)) (spanMerge (spanMerge wheelProof7_396 wheelProof7_428) (spanMerge wheelProof7_460 wheelProof7_492)))) (spanMerge (spanMerge (spanMerge wheelProof7_524 (spanMerge wheelProof7_556 wheelProof7_588)) (spanMerge (spanMerge wheelProof7_620 wheelProof7_652) (spanMerge wheelProof7_684 wheelProof7_716))) (spanMerge (spanMerge (spanMerge wheelProof7_748 wheelProof7_780) (spanMerge wheelProof7_812 wheelProof7_844)) (spanMerge (spanMerge wheelProof7_876 wheelProof7_908) (spanMerge wheelProof7_940 wheelProof7_972))))) (spanMerge (spanMerge (spanMerge (spanMerge wheelProof7_1004 (spanMerge wheelProof7_1036 wheelProof7_1068)) (spanMerge (spanMerge wheelProof7_1100 wheelProof7_1132) (spanMerge wheelProof7_1164 wheelProof7_1196))) (spanMerge (spanMerge (spanMerge wheelProof7_1228 wheelProof7_1260) (spanMerge wheelProof7_1292 wheelProof7_1324)) (spanMerge (spanMerge wheelProof7_1356 wheelProof7_1388) (spanMerge wheelProof7_1420 wheelProof7_1452)))) (spanMerge (spanMerge (spanMerge wheelProof7_1484 (spanMerge wheelProof7_1516 wheelProof7_1548)) (spanMerge (spanMerge wheelProof7_1580 wheelProof7_1612) (spanMerge wheelProof7_1644 wheelProof7_1676))) (spanMerge (spanMerge (spanMerge wheelProof7_1708 wheelProof7_1740) (spanMerge wheelProof7_1772 wheelProof7_1804)) (spanMerge (spanMerge wheelProof7_1836 wheelProof7_1868) (spanMerge wheelProof7_1900 wheelProof7_1932))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof8_0 : spanOK g127 8 0 23 := by
  apply spanOld
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof8_23 : spanOK g127 8 23 96 := by
  apply spanOld
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof8_119 : spanOK g127 8 119 96 := by
  apply spanOld
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof8_215 : spanOK g127 8 215 96 := by
  apply spanOld
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof8_311 : spanOK g127 8 311 96 := by
  apply spanOld
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof8_407 : spanOK g127 8 407 96 := by
  apply spanOld
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof8_503 : spanOK g127 8 503 75 := by
  apply spanOld
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof8_578 : spanOK g127 8 578 71 := by
  apply spanOld
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof8_649 : spanOK g127 8 649 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof8_681 : spanOK g127 8 681 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof8_713 : spanOK g127 8 713 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof8_745 : spanOK g127 8 745 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof8_777 : spanOK g127 8 777 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof8_809 : spanOK g127 8 809 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof8_841 : spanOK g127 8 841 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof8_873 : spanOK g127 8 873 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof8_905 : spanOK g127 8 905 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof8_937 : spanOK g127 8 937 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof8_969 : spanOK g127 8 969 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof8_1001 : spanOK g127 8 1001 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof8_1033 : spanOK g127 8 1033 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof8_1065 : spanOK g127 8 1065 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof8_1097 : spanOK g127 8 1097 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof8_1129 : spanOK g127 8 1129 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof8_1161 : spanOK g127 8 1161 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof8_1193 : spanOK g127 8 1193 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof8_1225 : spanOK g127 8 1225 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof8_1257 : spanOK g127 8 1257 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof8_1289 : spanOK g127 8 1289 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof8_1321 : spanOK g127 8 1321 17 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelLevel8 : spanOK g127 8 0 1338 := (spanMerge (spanMerge (spanMerge (spanMerge wheelProof8_0 (spanMerge wheelProof8_23 wheelProof8_119)) (spanMerge (spanMerge wheelProof8_215 wheelProof8_311) (spanMerge wheelProof8_407 wheelProof8_503))) (spanMerge (spanMerge (spanMerge wheelProof8_578 wheelProof8_649) (spanMerge wheelProof8_681 wheelProof8_713)) (spanMerge (spanMerge wheelProof8_745 wheelProof8_777) (spanMerge wheelProof8_809 wheelProof8_841)))) (spanMerge (spanMerge (spanMerge wheelProof8_873 (spanMerge wheelProof8_905 wheelProof8_937)) (spanMerge (spanMerge wheelProof8_969 wheelProof8_1001) (spanMerge wheelProof8_1033 wheelProof8_1065))) (spanMerge (spanMerge (spanMerge wheelProof8_1097 wheelProof8_1129) (spanMerge wheelProof8_1161 wheelProof8_1193)) (spanMerge (spanMerge wheelProof8_1225 wheelProof8_1257) (spanMerge wheelProof8_1289 wheelProof8_1321)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof9_0 : spanOK g127 9 0 6 := by
  apply spanOld
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof9_6 : spanOK g127 9 6 86 := by
  apply spanOld
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof9_92 : spanOK g127 9 92 86 := by
  apply spanOld
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelLevel9 : spanOK g127 9 0 178 := (spanMerge wheelProof9_0 (spanMerge wheelProof9_6 wheelProof9_92))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof10_0 : spanOK g127 10 0 1 := by
  apply spanOld
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof10_1 : spanOK g127 10 1 12 := by
  apply spanOld
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelLevel10 : spanOK g127 10 0 13 := (spanMerge wheelProof10_0 wheelProof10_1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof11_0 : spanOK g127 11 0 1 := by
  apply spanOld
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelLevel11 : spanOK g127 11 0 1 := wheelProof11_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelT : ∀ k ≤ 11, spanOK g127 k 0 (g127.levels k).1 := by
  intro k hk
  interval_cases k
  · intro i lo hi; change i<0 at hi; omega
  · intro i lo hi; change i<0 at hi; omega
  · intro i lo hi; change i<0 at hi; omega
  · intro i lo hi; change i<0 at hi; omega
  · intro i lo hi; change i<0 at hi; omega
  · exact wheelLevel5
  · exact wheelLevel6
  · exact wheelLevel7
  · exact wheelLevel8
  · exact wheelLevel9
  · exact wheelLevel10
  · exact wheelLevel11
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127G : graphValid g127 (boundsBefore K246) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low127 : Lower true (varsX 127) (graphGoal 127) 12 := lower_span (g:=g127) (i:=0) (hints:=1049651) (before_sound K246 V246) g127G wheelT (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
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

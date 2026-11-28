import PEqualNP.Defs

-- The two-mode live-state and cofactor checker follows L_meta_1674 and L_meta_670.
-- The graph, restrictions and all search certificates below are for L_meta_52682.

-- Shared forest and cofactor certificates from L_meta_1674 and PR 11111 for L_meta_1677.
-- The original credit line is retained below. The two root certificates here cover the unpinned graph.

-- The checker and the bound certificates are adapted from PEqualNP/Outside/L_meta_1667.lean (Apache-2.0).
-- Two modes: u=false are monotone runs (AND, OR); u=true are runs up to complement, where negation is free.
namespace PEqualNP.Outside.L_meta_52682
open PEqualNP.CircuitLowerBounds
private def w80 (xs : List Nat) : Nat :=
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

def inputs : List Sig := [(BitVec.ofNat 512 (w80 [0xaaaaaaaa,0xaaaaaaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaaaaaaa])),(BitVec.ofNat 512 (w80 [0xcccccccc,0xcccccccccccccccccccc,0xcccccccccccccccccccc,0xcccccccccccccccccccc,0xcccccccccccccccccccc,0xcccccccccccccccccccc,0xcccccccccccccccccccc])),(BitVec.ofNat 512 (w80 [0xf0f0f0f0,0xf0f0f0f0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f0f0f0])),(BitVec.ofNat 512 (w80 [0xff00ff00,0xff00ff00ff00ff00ff00,0xff00ff00ff00ff00ff00,0xff00ff00ff00ff00ff00,0xff00ff00ff00ff00ff00,0xff00ff00ff00ff00ff00,0xff00ff00ff00ff00ff00])),(BitVec.ofNat 512 (w80 [0xffff0000,0xffff0000ffff0000ffff,0xffff0000ffff0000,0xffff0000ffff0000ffff,0xffff0000ffff0000,0xffff0000ffff0000ffff,0xffff0000ffff0000])),(BitVec.ofNat 512 (w80 [0xffffffff,0xffffffff0000,0xffffffff00000000,0xffffffff00000000ffff,0xffff00000000ffffffff,0xffffffff0000,0xffffffff00000000])),(BitVec.ofNat 512 (w80 [0xffffffff,0xffffffff000000000000,0xffffffffffffffff,0xffff,0xffffffffffff00000000,0xffffffffffff,0xffff0000000000000000])),(BitVec.ofNat 512 (w80 [0xffffffff,0xffffffffffffffffffff,0xffff0000000000000000,0xffff,0xffffffffffffffffffff,0xffffffff000000000000,0])),(BitVec.ofNat 512 (w80 [0xffffffff,0xffffffffffffffffffff,0xffffffffffffffffffff,0xffffffffffffffff0000,0,0,0]))]
def graph : Sig := (BitVec.ofNat 512 (w80 [0xffffffff,0xffffffffffffffffffff,0xfffefffffffffffefffc,0xfffeffeefefaee00ffff,0xffffffffffffffffffff,0xfffffffefffffffffffe,0xfffcfffeffeefefaee00]))
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
  (x 0 &&& x 3) ||| (x 1 &&& x 3) ||| (x 0 &&& x 4) ||| (x 2 &&& x 4) ||| (x 0 &&& x 5) ||| (x 1 &&& x 5) ||| (x 3 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 6) ||| (x 3 &&& x 6) ||| (x 5 &&& x 6) ||| (x 0 &&& x 7) ||| (x 1 &&& x 7) ||| (x 2 &&& x 7) ||| (x 3 &&& x 7) ||| (x 4 &&& x 7) ||| (x 5 &&& x 7) ||| (x 6 &&& x 7)
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
  | 0 => (w80 [0x1000000000000,0x10000000000000001,0x10000,0x100000000,0x1000000000000,0x10000000000000001])
  | 1 => (w80 [0x10000000000000000,0x10000,0,0x1000000000000,1])
  | 2 => (w80 [1,0x10000,0,0,0x10000000000000001])
  | 3 => (w80 [0x10000,0,0,1])
  | 4 => (w80 [0x100000000,0x1000000000000,0x10000000000000001])
  | 5 => (w80 [0x1000000000000,1])
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
  | 0 => ⟨0,7,true,0,0,0,1,[48, 65, 80, 98, 118],3⟩
  | 1 => ⟨0,7,true,8,0,0,1,[64, 80, 98, 118],1⟩
  | 2 => ⟨3,7,true,1,0,0,8,[96, 82, 48, 116],1⟩
  | 3 => ⟨2,7,true,64,0,0,4,[64, 80, 98, 115],1⟩
  | 4 => ⟨0,6,false,8,0,0,0,[48, 82, 100],0⟩
  | 5 => ⟨6,7,true,4,0,0,64,[48, 80, 100, 118],1⟩
  | 6 => ⟨0,7,true,24,0,0,1,[80, 98, 118],0⟩
  | 7 => ⟨3,4,false,1,0,0,0,[50, 83],0⟩
  | 8 => ⟨0,2,false,16,0,0,0,[48, 83],0⟩
  | 9 => ⟨4,7,true,5,0,0,16,[83, 100, 118],0⟩
  | 10 => ⟨0,7,true,16,0,0,1,[48, 80, 98, 118],1⟩
  | 11 => ⟨4,7,true,4,0,0,16,[83, 100, 118],1⟩
  | 12 => ⟨4,7,true,1,0,0,16,[32, 83, 100, 118],1⟩
  | 13 => ⟨0,2,false,144,0,0,0,[80, 99, 118],0⟩
  | 14 => ⟨3,7,true,65,0,0,8,[82, 99, 116],0⟩
  | 15 => ⟨4,6,false,4,0,0,0,[48, 83, 100],0⟩
  | 16 => ⟨2,7,true,80,0,0,4,[80, 98, 115],0⟩
  | 17 => ⟨2,7,true,0,0,0,4,[64, 97, 80, 33, 115],3⟩
  | 18 => ⟨0,6,false,136,0,0,0,[80, 98, 116],0⟩
  | 19 => ⟨0,6,false,0,0,0,0,[96, 50, 84],0⟩
  | 20 => ⟨3,7,true,0,0,0,8,[97, 82, 49, 116],3⟩
  | 21 => ⟨0,2,false,0,0,0,0,[96, 66, 101],0⟩
  | 22 => ⟨0,2,false,128,0,0,0,[112, 83],0⟩
  | 23 => ⟨3,4,false,129,0,0,0,[82, 99, 118],0⟩
  | 24 => ⟨4,7,true,0,0,0,16,[33, 83, 100, 118],3⟩
  | 25 => ⟨2,3,false,64,0,0,0,[48, 82, 100],0⟩
  | 26 => ⟨0,6,false,12,0,0,0,[80, 100],0⟩
  | 27 => ⟨0,6,false,128,0,0,0,[112, 82, 67, 100],0⟩
  | 28 => ⟨3,4,false,5,0,0,0,[83],0⟩
  | 29 => ⟨3,6,false,1,0,0,0,[48, 82, 100],1⟩
  | 30 => ⟨2,3,false,65,0,0,0,[82, 100],0⟩
  | 31 => ⟨2,3,false,192,0,0,0,[80, 98, 116],0⟩
  | 32 => ⟨3,7,true,64,0,0,8,[82, 99, 116],1⟩
  | 33 => ⟨6,7,true,0,0,0,64,[32, 49, 80, 100, 118],3⟩
  | 34 => ⟨6,7,true,8,0,0,64,[32, 80, 100, 118],1⟩
  | 35 => ⟨0,2,false,24,0,0,0,[80],0⟩
  | 36 => ⟨0,2,false,80,0,0,0,[80, 99],0⟩
  | 37 => ⟨3,7,true,0,0,0,8,[82, 99, 116],15⟩
  | 38 => ⟨2,6,true,144,0,0,4,[32, 49, 82, 99, 117],0⟩
  | 39 => ⟨6,7,true,4,0,0,64,[16, 48, 82, 32, 100, 118],7⟩
  | 40 => ⟨3,7,true,32,0,0,8,[98, 82, 83, 116],7⟩
  | 41 => ⟨2,3,false,160,0,0,0,[114],0⟩
  | 42 => ⟨3,7,true,64,0,0,8,[82, 99, 116],7⟩
  | 43 => ⟨2,7,true,64,0,0,4,[65, 97, 50, 83, 117],2⟩
  | 44 => ⟨3,7,true,2,0,0,8,[81, 98, 33, 49, 116],7⟩
  | 45 => ⟨6,7,true,8,0,0,64,[16, 32, 80, 100, 118],7⟩
  | 46 => ⟨6,7,true,0,0,0,64,[16, 32, 48, 80, 100, 118],15⟩
  | 47 => ⟨5,7,true,8,0,0,32,[98, 82, 84, 117],7⟩
  | 48 => ⟨2,6,true,16,0,0,4,[112, 32, 49, 82, 99],1⟩
  | 49 => ⟨6,7,true,32,0,0,64,[16, 32, 48, 80, 100, 118],7⟩
  | 50 => ⟨2,5,false,136,0,0,0,[114],0⟩
  | 51 => ⟨6,7,true,6,0,0,64,[48, 81, 16, 100, 118],3⟩
  | 52 => ⟨4,7,true,0,0,0,16,[84, 101, 118],5⟩
  | 53 => ⟨5,7,true,0,0,0,32,[50, 98, 82, 84, 117],15⟩
  | 54 => ⟨6,7,true,12,0,0,64,[16, 80, 100, 118],3⟩
  | 55 => ⟨6,7,true,40,0,0,64,[16, 32, 80, 100, 118],3⟩
  | 56 => ⟨5,7,true,72,0,0,32,[82, 100, 117],3⟩
  | 57 => ⟨6,7,true,2,0,0,64,[32, 49, 80, 100, 118],7⟩
  | 58 => ⟨5,7,true,2,0,0,32,[49, 98, 82, 84, 117],7⟩
  | 59 => ⟨5,7,true,64,0,0,32,[50, 82, 100, 117],7⟩
  | 60 => ⟨4,7,true,32,0,0,16,[33, 49, 83, 100, 118],3⟩
  | 61 => ⟨4,7,true,64,0,0,16,[33, 49, 83, 100, 117],3⟩
  | 62 => ⟨3,7,true,96,0,0,8,[82, 99, 116],3⟩
  | 63 => ⟨6,7,true,36,0,0,64,[16, 48, 80, 100, 118],3⟩
  | 64 => ⟨4,7,true,8,0,0,16,[33, 49, 84, 101, 118],3⟩
  | 65 => ⟨2,3,false,96,0,0,0,[48, 33, 98, 84],0⟩
  | 66 => ⟨2,7,true,0,0,0,4,[65, 98, 33, 50, 83, 117],6⟩
  | 67 => ⟨2,7,true,66,0,0,4,[64, 48, 82, 99, 117],1⟩
  | 68 => ⟨1,4,false,64,0,0,0,[16, 97],0⟩
  | 69 => ⟨1,4,false,40,0,0,0,[32, 97, 50, 101],0⟩
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
  (x 0 &&& x 3) ||| (x 1 &&& x 3) ||| (x 0 &&& x 4) ||| (x 2 &&& x 4) ||| (x 0 &&& x 5) ||| (x 1 &&& x 5) ||| (x 3 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 6) ||| (x 3 &&& x 6) ||| (x 5 &&& x 6) ||| (x 0 &&& x 7) ||| (x 1 &&& x 7) ||| (x 2 &&& x 7) ||| (x 3 &&& x 7) ||| (x 4 &&& x 7) ||| (x 5 &&& x 7) ||| (x 6 &&& x 7)
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

def target (x : Fin 8 → Bool) : Bool := decide (∃ i < ([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 3, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 3, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 3, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)
def smallCircuit : Circuit := ⟨[⟨.or,[3,5]⟩,⟨.or,[1,2]⟩,⟨.or,[8,9]⟩,⟨.or,[0,1]⟩,⟨.or,[6,11]⟩,⟨.or,[0,2]⟩,⟨.or,[7,13]⟩,⟨.or,[7,8]⟩,⟨.or,[6,7]⟩,⟨.and,[14,4]⟩,⟨.and,[16,10]⟩,⟨.and,[15,12]⟩,⟨.and,[5,3]⟩,⟨.or,[17,18]⟩,⟨.or,[21,19]⟩,⟨.or,[22,20]⟩], 23⟩

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

def lowRow (i : Fin 8) : Row := Fin.ofNat 512 (1 <<< ([3, 3, 4, 0, 0, 0, 1, 0] : List Nat).getD i.val 0)
def highRow (i : Fin 8) : Row := Fin.ofNat 512 ((1 <<< i.val) ||| (1 <<< ([3, 3, 4, 0, 0, 0, 1, 0] : List Nat).getD i.val 0))

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
private abbrev sampleWord (n : Nat) : BitVec 152 := BitVec.ofNat 152 n
def g41Y : Array (Bits × Bits) := #[((sampleWord (w80 [0x3ff63ff63ff63ff63f,0xf63ff63ff63ff63ff63f])),(sampleWord (w80 [0x492049204920492049,0x20492049204920492049]))),(0x0,0x0),(0x0,0x0),((sampleWord (w80 [0xc7fbc7fbc7fbc7fbc7,0xfbc7fbc7fbc7fbc7fbc7])),(sampleWord (w80 [0x924092409240924092,0x40924092409240924092]))),(0x0,0x0),((sampleWord (w80 [0xf8fdf8fdf8fdf8fdf8,0xfdf8fdf8fdf8fdf8fdf8])),(sampleWord (w80 [0x248124812481248124,0x81248124812481248124]))),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
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
def K41 := extendKnown [] 4 [(41,[]),(42,[16]),(74,[16,101]),(98,[16,83,67,100]),(104,[48,16,33,82,66,100]),(137,[117,101]),(138,[16,117,101]),(145,[67,117,101]),(148,[32,16,67,117,101]),(162,[16,83,67,116,100]),(168,[48,16,33,82,66,116,100]),(194,[16,99,67,117]),(196,[32,16,99,67,117]),(200,[48,16,33,98,66,117]),(224,[80,16,33,99,66,116])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V41 : Known true K41 := extend_ok (m:=41) baseKnown low41 (by decide +kernel)
def g27Y : Array (Bits × Bits) := #[((sampleWord (w80 [0xf71fc7ff03fffff8f7,0x1fc7ff03fffff8f71fc7])),(sampleWord (w80 [0x710490a2850401207,0x10490a28504012071049]))),((sampleWord (w80 [0xbe838fffc07e3ff0b,0xe838fffc07e3ff0be838])),(sampleWord (w80 [0x4368db4c3260892043,0x68db4c326089204368db]))),(0x0,0x0),((sampleWord (w80 [0xeee63ffffff803ffee,0xe63ffffff803ffeee63f])),(sampleWord (w80 [0x88724904085124008,0x87249040851240088724]))),((sampleWord (w80 [0x193dc0fffffffc0019,0x3dc0fffffffc00193dc0])),(sampleWord (w80 [0x982db6e08306038498,0x2db6e083060384982db6]))),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
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
theorem g27G : graphValid g27 (boundsBefore K41) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low27 : Lower true (varsX 27) (graphGoal 27) 4 := lower_forest (g:=g27) (i:=0) (hints:=51) (before_sound K41 V41) g27G g27T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K27 := extendKnown K41 4 [(27,[]),(29,[33,67]),(51,[83]),(53,[33,67,83]),(77,[96,16,33,66,84]),(85,[32,16,67,99,83]),(86,[32,99,83]),(89,[48,65,33,98,82]),(92,[32,49,97,81]),(113,[80,65,33,48,98,50]),(116,[96,65,32,50,81])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V27 : Known true K27 := extend_ok (m:=27) V41 low27 (by decide +kernel)
def g43Y : Array (Bits × Bits) := #[((sampleWord (w80 [0xfe7d01c7fc0fc7cfe7,0xd01c7fc0fc7cfe7d01c7])),(sampleWord (w80 [0x51d124928a290a051,0xd124928a290a051d1249]))),((sampleWord (w80 [0x3f8b8e38fff007f3f8,0xb8e38fff007f3f8b8e38])),(sampleWord (w80 [0x884b924930c3210884,0xb924930c3210884b9249]))),(0x0,0x0),((sampleWord (w80 [0x3fe7703ffffff803fe,0x7703ffffff803fe7703f])),(sampleWord (w80 [0x100024924104020100,0x2492410402010002492]))),(0x0,0x0),((sampleWord (w80 [0xc018ffc0fffffffc01,0x8ffc0fffffffc018ffc0])),(sampleWord (w80 [0x200049248208040200,0x4924820804020004924]))),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g43C : List ColumnInfo := [(1,0,42,0,4)]
def g43A : List (List Nat) := [[],[83],[16],[16,83]]
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
theorem g43G : graphValid g43 (boundsBefore K27) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low43 : Lower true (varsX 43) (graphGoal 43) 5 := lower_forest (g:=g43) (i:=0) (hints:=51) (before_sound K27 V27) g43G g43T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K43 := extendKnown K27 5 [(43,[]),(105,[97,33,66]),(139,[117,101]),(149,[33,67,117,101]),(153,[48,65,33,117,101]),(163,[83,67,116,100]),(201,[97,33,66,117]),(204,[32,49,97,65,117]),(212,[64,97,32,50,49,117])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V43 : Known true K43 := extend_ok (m:=43) V27 low43 (by decide +kernel)
def g57Y : Array (Bits × Bits) := #[((sampleWord (w80 [0xfdb07fff83ffe7fffb,0x60ffff07ffcffff6c1ff])),(sampleWord (w80 [0x92410820400800,0x1248210408010000249]))),(0x0,0x0),(0x0,0x0),((sampleWord (w80 [0x3bcf81fffc0ff8fc77,0x9f03fff81ff1f8ef3e07])),(sampleWord (w80 [0x81c5248a1142821103,0x8a491422850422071492]))),((sampleWord (w80 [0xc6940e3ffff000ff8d,0x281c7fffe001ff1a5038])),(sampleWord (w80 [0x16976dac218b14a02d,0x2edb58431629405a5db6]))),((sampleWord (w80 [0x66ff03fffffff000c,0xdfe07ffffffe0019bfc0])),(sampleWord (w80 [0x262a4930420c00c24c,0x5492608418018498a924]))),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g57C : List ColumnInfo := [(16,0,41,0,4)]
def g57A : List (List Nat) := [[],[83]]
def g57D4 (j : Nat) := if j=0 then 0x1f else 0
def g57L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,g57D4)
  | _ => emptyPacking
def g57I (_ _ : Nat) : Option (Nat × Nat) := none
def g57 : Forest := ⟨57,4,fun i => g57Y[i]?.getD (0,0),g57C,g57A,g57L,g57I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g57P4_0 : block g57 4 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g57B4 : block g57 4 0 1=true := g57P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g57T : checkedTables g57 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g57 0 0 0 = true)
  · exact (rfl : block g57 1 0 0 = true)
  · exact (rfl : block g57 2 0 0 = true)
  · exact (rfl : block g57 3 0 0 = true)
  · exact g57B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g57G : graphValid g57 (boundsBefore K43) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low57 : Lower true (varsX 57) (graphGoal 57) 5 := lower_forest (g:=g57) (i:=0) (hints:=3) (before_sound K43 V43) g57G g57T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K57 := extendKnown K43 5 [(57,[]),(78,[96,16,66,49,83]),(108,[96,16,33,66]),(141,[112,66,48,83,101]),(142,[112,16,66,49,83,101]),(147,[112,33,49,16,65,84,101]),(150,[112,16,50,65,84,101]),(154,[112,16,49,83,101]),(156,[112,16,33,50,67,84,101]),(172,[112,16,33,66,100]),(178,[112,16,49,99]),(180,[112,16,33,50,84,99]),(184,[112,16,33,98]),(197,[112,50,64,101,84]),(209,[112,48,100,84,83]),(216,[112,16,33,101,82])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V57 : Known true K57 := extend_ok (m:=57) V43 low57 (by decide +kernel)
def g106Y : Array (Bits × Bits) := #[(0x0,0x0),((sampleWord (w80 [0xdf7ec03c3ffe0fbefd,0x80787ffc1f7dfb00f0ff])),(sampleWord (w80 [0x820404444444210408,0x8888888420810111111]))),(0x0,0x0),((sampleWord (w80 [0x1fbf43c3c3fff03f7e,0x878787ffe07efd0f0f0f])),(sampleWord (w80 [0x40808888888420810,0x11111110841020222222]))),(0x0,0x0),((sampleWord (w80 [0xe03fbc03fc3fffc07f,0x7807f87fff80fef00ff0])),(sampleWord (w80 [0x81011111110841020,0x22222221082040444444]))),((sampleWord (w80 [0xffc03ffc003fffff80,0x7ff8007fffff00fff000])),(sampleWord (w80 [0x102022222221082040,0x44444442104080888888]))),(0x0,0x0),(0x0,0x0)]
def g106C : List ColumnInfo := [(2,0,104,0,4),(8,0,98,0,4),(32,0,74,0,4),(64,0,42,0,4)]
def g106A : List (List Nat) := [[],[101],[83],[83,99],[99,83],[99],[49],[49,101],[49,81],[49,81,97],[49,97,81],[49,97],[81,49],[81,49,99],[81],[81,97],[81,99],[81,99,49],[97,49,83],[97,49],[97,81],[97],[97,83,49],[97,83]]
def g106D3 := limbs80 #[#[0x23ea6a1221e12148110,0x8028]]
def g106D4 := limbs80 #[#[0x2fd0910bd42443e48110,0x609085870]]
def g106H4 (j : Nat) := if j=0 then 0xc else 0
def g106D5 (j : Nat) := if j=0 then 0xd1027d10 else 0
def g106H5 := limbs80 #[#[0x24b894000,0x88000009800000020a00,0x70]]
def g106D6 (j : Nat) := if j=0 then 0x3904f else 0
def g106H6 := limbs80 #[#[0x14000000015008801100,0x5]]
def g106L : Nat → Packing
  | 3 => (2,3,2,0,0,5,0,g106D3)
  | 4 => (3,2,2,0,0,5,0,g106D4)
  | 5 => (1,1,2,0,0,0,0,g106D5)
  | 6 => (1,0,2,0,0,0,0,g106D6)
  | _ => emptyPacking
def g106I : Nat → Nat → Option (Nat × Nat)
  | 4 => lookupShort 1 2 0 3 1 0 g106H4
  | 5 => lookupShort 2 31 0 7 2 3 g106H5
  | 6 => lookupShort 1 17 0 7 0 5 g106H6
  | _ => fun _ => none
def g106 : Forest := ⟨106,6,fun i => g106Y[i]?.getD (0,0),g106C,g106A,g106L,g106I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g106P3_0 : block g106 3 0 2=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g106B3 : block g106 3 0 2=true := g106P3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g106P4_0 : block g106 4 0 3=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g106B4 : block g106 4 0 3=true := g106P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g106P5_0 : block g106 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g106B5 : block g106 5 0 1=true := g106P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g106P6_0 : block g106 6 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g106B6 : block g106 6 0 1=true := g106P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g106T : checkedTables g106 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g106 0 0 0 = true)
  · exact (rfl : block g106 1 0 0 = true)
  · exact (rfl : block g106 2 0 0 = true)
  · exact g106B3
  · exact g106B4
  · exact g106B5
  · exact g106B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g106G : graphValid g106 (boundsBefore K57) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low106 : Lower true (varsX 106) (graphGoal 106) 7 := lower_forest (g:=g106) (i:=0) (hints:=17829936) (before_sound K57 V57) g106G g106T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K106 := extendKnown K57 7 [(106,[]),(169,[16,118]),(170,[118]),(202,[101,117]),(226,[83,67,100,116]),(232,[49,33,82,66,100,116])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V106 : Known true K106 := extend_ok (m:=106) V57 low106 (by decide +kernel)
def g31Y : Array (Bits × Bits) := #[((sampleWord (w80 [0xe003ffc07ffffffe00,0x3fffff80ffd386b20f0f])),(sampleWord (w80 [0x41a8128d052280541a,0x82502916291304a21111]))),((sampleWord (w80 [0xfffc00007ff01fffff,0xc007ffff01a37d4800f0])),(sampleWord (w80 [0x81311b160644c89893,0x136232244d835c485555]))),((sampleWord (w80 [0xffffffff80001fffff,0xfff80000003f407df000])),(sampleWord (w80 [0x5c05c18178702e01c,0x380bc38703340753333]))),((sampleWord (w80 [0x1fffff,0xfffffffffe663f7600ff])),(sampleWord (w80 [0x160260205808130120,0x2404c00000642314aaaa]))),((sampleWord (w80 [0xffffffffffffe00000,0x19dd38dff00])),(sampleWord (w80 [0x1803800060001c01c0,0x38070040808c9308cccc]))),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
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
theorem g31G : graphValid g31 (boundsBefore K106) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low31 : Lower true (varsX 31) (graphGoal 31) 5 := lower_forest (g:=g31) (i:=0) (hints:=1075) (before_sound K106 V106) g31G g31T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K31 := extendKnown K106 5 [(31,[]),(55,[83]),(87,[32,16,67,99,83])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V31 : Known true K31 := extend_ok (m:=31) V106 low31 (by decide +kernel)
def g59Y : Array (Bits × Bits) := #[((sampleWord (w80 [0xfe007fe1ff0fffc03f,0xffffff0ff9621a00ff0f])),(sampleWord (w80 [0x140501440220028281,0x4040022088420a111111]))),((sampleWord (w80 [0xffff8001fff0ffffc0,0x1fe1fff01c1fa90f00f0])),(sampleWord (w80 [0x982609882402130309,0x80842402180f09333333]))),(0x0,0x0),((sampleWord (w80 [0xfffffffe0000ffffff,0xe001ffff239766f000ff])),(sampleWord (w80 [0x204812004844240402,0x5084800211064444444]))),((sampleWord (w80 [0xffffff,0xfffe00001369f8000f00])),(sampleWord (w80 [0xc1705c117088b8282c,0x160170441329f0eeeeee]))),((sampleWord (w80 [0xffffffffffff000000,0xcea8c5fff000])),(sampleWord (w80 [0x18060018000c03030,0x1811808846a080888888]))),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g59C : List ColumnInfo := [(0,16,42,1,5),(2,0,57,0,5),(16,0,43,0,5),(1,16,42,0,4),(8,0,51,0,4),(32,0,27,0,4)]
def g59A : List (List Nat) := [[],[83]]
def g59D4 (j : Nat) := if j=0 then 0x5dd4542 else 0
def g59D5 (j : Nat) := if j=0 then 0x108404fd42 else 0
def g59H5 (j : Nat) := if j=0 then 0x4 else 0
def g59D6 (j : Nat) := if j=0 then 0x2c458bf else 0
def g59H6 (j : Nat) := if j=0 then 0x2 else 0
def g59L : Nat → Packing
  | 4 => (1,2,3,0,0,0,0,g59D4)
  | 5 => (1,1,3,0,0,0,0,g59D5)
  | 6 => (1,0,3,0,0,0,0,g59D6)
  | _ => emptyPacking
def g59I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupShort 1 2 0 2 0 0 g59H5
  | 6 => lookupShort 1 2 0 2 0 0 g59H6
  | _ => fun _ => none
def g59 : Forest := ⟨59,6,fun i => g59Y[i]?.getD (0,0),g59C,g59A,g59L,g59I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g59P4_0 : block g59 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g59B4 : block g59 4 0 1=true := g59P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g59P5_0 : block g59 5 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g59B5 : block g59 5 0 1=true := g59P5_0
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
  · exact g59B4
  · exact g59B5
  · exact g59B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g59G : graphValid g59 (boundsBefore K31) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low59 : Lower true (varsX 59) (graphGoal 59) 7 := lower_forest (g:=g59) (i:=0) (hints:=51) (before_sound K31 V31) g59G g59T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K59 := extendKnown K31 7 [(59,[]),(109,[96,16,33,66]),(121,[97,33])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V59 : Known true K59 := extend_ok (m:=59) V31 low59 (by decide +kernel)
def g61Y : Array (Bits × Bits) := #[((sampleWord (w80 [0xf007ff0ffffff007ff,0xff87ffffd45c460f83ff])),(sampleWord (w80 [0xa0500a201000a05014,0x1100082401806108421]))),(0x0,0x0),((sampleWord (w80 [0xfff8000ff87ffff801,0xfff87fc05373b2007c00])),(sampleWord (w80 [0xc0622c40a122c46258,0x8a012108527132b5ad6b]))),((sampleWord (w80 [0xfffffff0007ffffffe,0x7ffcafd11df0001f])),(sampleWord (w80 [0x280b002c20b008060,0x2c220a00a541186318c6]))),((sampleWord (w80 [0x7fffffff,0xffff80004d2fe8007fe0])),(sampleWord (w80 [0xb04c08b044c090481,0x30004c100d06c94a5294]))),((sampleWord (w80 [0xffffffffff80000000,0x33aa61bff8000])),(sampleWord (w80 [0xc07000c00700e0701,0xc04470211aa6018c6318]))),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g61C : List ColumnInfo := [(0,4,41,16,5),(4,0,57,0,5),(8,0,53,0,4),(16,4,41,0,4),(32,0,29,0,4)]
def g61A : List (List Nat) := [[],[83]]
def g61D4 (j : Nat) := if j=0 then 0x4fd5120 else 0
def g61D5 := limbs80 #[#[0x480e140fd42fe20fd20,0x4088]]
def g61H5 (j : Nat) := if j=0 then 0x0 else 0
def g61D6 (j : Nat) := if j=0 then 0x18989f else 0
def g61H6 := limbs80 #[#[0x20000000000,0x5620,0x501800000]]
def g61L : Nat → Packing
  | 4 => (1,2,3,0,0,0,0,g61D4)
  | 5 => (3,1,3,0,0,5,0,g61D5)
  | 6 => (1,0,3,0,0,0,0,g61D6)
  | _ => emptyPacking
def g61I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupShort 1 2 0 2 0 0 g61H5
  | 6 => lookupShort 1 43 0 5 2 1 g61H6
  | _ => fun _ => none
def g61 : Forest := ⟨61,6,fun i => g61Y[i]?.getD (0,0),g61C,g61A,g61L,g61I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g61P4_0 : block g61 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g61B4 : block g61 4 0 1=true := g61P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g61P5_0 : block g61 5 0 3=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g61B5 : block g61 5 0 3=true := g61P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g61P6_0 : block g61 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g61B6 : block g61 6 0 1=true := g61P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g61T : checkedTables g61 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g61 0 0 0 = true)
  · exact (rfl : block g61 1 0 0 = true)
  · exact (rfl : block g61 2 0 0 = true)
  · exact (rfl : block g61 3 0 0 = true)
  · exact g61B4
  · exact g61B5
  · exact g61B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g61G : graphValid g61 (boundsBefore K59) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low61 : Lower true (varsX 61) (graphGoal 61) 7 := lower_forest (g:=g61) (i:=0) (hints:=1027) (before_sound K59 V59) g61G g61T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K61 := extendKnown K59 7 [(61,[]),(91,[48,33,65,16,101]),(94,[96,16,66,49,83]),(115,[80,33,65,49,48,99]),(118,[96,16,66,49]),(124,[96,16,66])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V61 : Known true K61 := extend_ok (m:=61) V59 low61 (by decide +kernel)
def g62Y : Array (Bits × Bits) := #[(0x0,0x0),((sampleWord (w80 [0xc00fff0ffffffc00ff,0xfff0fffeea3a5303f03f])),(sampleWord (w80 [0x84a08a210802284a02,0x80220882200a53145145]))),((sampleWord (w80 [0xfff0000ffc3fffff00,0x3fffffc009adfd000fc0])),(sampleWord (w80 [0xc42c405090b10c4b,0x11404108092d994d34d3]))),((sampleWord (w80 [0xfffffff0003fffffff,0xc000fffd77e88afc003f])),(sampleWord (w80 [0x90130026104c0100c,0x584120152a08828a28a]))),((sampleWord (w80 [0x3fffffff,0xffff00012697f4000fc0])),(sampleWord (w80 [0x2e09c08b8227026090,0x26009c11269264b2cb2c]))),((sampleWord (w80 [0xffffffffffc0000000,0x39d530dfff000])),(sampleWord (w80 [0x300e000c00380380e0,0x3808e0208d5104c30c30]))),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g62C : List ColumnInfo := [(0,4,42,16,5)]
def g62A : List (List Nat) := [[],[83],[66],[66,83],[49],[49,81],[49,66],[49,66,81],[81,49],[81],[81,66,49],[81,66]]
def g62D5 (j : Nat) := if j=0 then 0x3f else 0
def g62L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,g62D5)
  | _ => emptyPacking
def g62I (_ _ : Nat) : Option (Nat × Nat) := none
def g62 : Forest := ⟨62,5,fun i => g62Y[i]?.getD (0,0),g62C,g62A,g62L,g62I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g62P5_0 : block g62 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g62B5 : block g62 5 0 1=true := g62P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g62T : checkedTables g62 5 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g62 0 0 0 = true)
  · exact (rfl : block g62 1 0 0 = true)
  · exact (rfl : block g62 2 0 0 = true)
  · exact (rfl : block g62 3 0 0 = true)
  · exact (rfl : block g62 4 0 0 = true)
  · exact g62B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g62G : graphValid g62 (boundsBefore K61) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low62 : Lower true (varsX 62) (graphGoal 62) 6 := lower_forest (g:=g62) (i:=0) (hints:=1184816) (before_sound K61 V61) g62G g62T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K62 := extendKnown K61 6 [(62,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V62 : Known true K62 := extend_ok (m:=62) V61 low62 (by decide +kernel)
def g79Y : Array (Bits × Bits) := #[((sampleWord (w80 [0x7ff001ff80ffc07ff0,0x3ffffe03ff4b12b0007])),(sampleWord (w80 [0x42a8d4251a148b42a9,0xaa4a8a458a64b1235b6d]))),((sampleWord (w80 [0x7ffffe0000ffffffff,0xfc00ffffc068db9401f8])),(sampleWord (w80 [0x4c098362c191204c1,0x306c0c891340d3841249]))),((sampleWord (w80 [0x7fffffffff00007fff,0xffff0000000ff00e8e00])),(sampleWord (w80 [0x1702e0b8305e1c1701,0xc0702f0e1c0df00cb6db]))),((sampleWord (w80 [0x800000000000007fff,0xffffffffff99af6d703f])),(sampleWord (w80 [0x180300c04060201802,0x80300000190c082492]))),(0x0,0x0),(0x0,0x0),((sampleWord (w80 [0xffffffffffffff8000,0x6754f2ffc0])),(sampleWord (w80 [0x600c0100008000600c,0x300c010202200724924]))),(0x0,0x0),(0x0,0x0)]
def g79C : List ColumnInfo := [(1,0,78,0,5)]
def g79A : List (List Nat) := [[],[32,99]]
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
theorem g79G : graphValid g79 (boundsBefore K62) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low79 : Lower true (varsX 79) (graphGoal 79) 6 := lower_forest (g:=g79) (i:=0) (hints:=16778803) (before_sound K62 V62) g79G g79T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K79 := extendKnown K62 6 [(79,[]),(103,[83,67])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V79 : Known true K79 := extend_ok (m:=79) V62 low79 (by decide +kernel)
def g93Y : Array (Bits × Bits) := #[((sampleWord (w80 [0xf003ff0ff87ff007ff,0xff87fffcd47c560003ff])),(sampleWord (w80 [0xa4280a201120a45214,0x81102080501c1694a529]))),(0x0,0x0),((sampleWord (w80 [0xfffc000ffffffff801,0xfff87fc35353a20ffc00])),(sampleWord (w80 [0xc0302c40a002c06058,0xa01010a425122318c63]))),((sampleWord (w80 [0xfffffff0007ffffffe,0x7ffcafd11df0001f])),(sampleWord (w80 [0x140b002c20b008060,0x2c220a00a741086318c6]))),((sampleWord (w80 [0x7fffffff,0xffff80004d2fe8007fe0])),(sampleWord (w80 [0x982c08b044c090481,0x30004c100d22c94a5294]))),(0x0,0x0),((sampleWord (w80 [0xffffffffff80000000,0x33aa61bff8000])),(sampleWord (w80 [0xe03000c00700e0701,0xc044702118a6118c6318]))),(0x0,0x0),(0x0,0x0)]
def g93C : List ColumnInfo := [(1,0,92,0,4),(4,0,89,0,4),(8,0,85,0,4),(16,0,77,0,4),(64,0,29,0,4)]
def g93A : List (List Nat) := [[],[98,67],[32,99],[32,48,64,96],[48,100],[48,66,96,32],[64,50],[64,98,48,50],[96,32,50,67],[96,66]]
def g93D4 (j : Nat) := if j=0 then 0x57d4d10 else 0
def g93D5 (j : Nat) := if j=0 then 0xc1a0fd20fd10 else 0
def g93H5 (j : Nat) := if j=0 then 0x0 else 0
def g93D6 (j : Nat) := if j=0 then 0x23440bf else 0
def g93H6 := limbs80 #[#[0x7000000,0x330001400000,0x8400008806806c,0x16c00000000000000,0x0,0x0,0xb80]]
def g93L : Nat → Packing
  | 4 => (1,2,3,0,0,0,0,g93D4)
  | 5 => (2,1,3,0,0,4,0,g93D5)
  | 6 => (1,0,3,0,0,0,0,g93D6)
  | _ => emptyPacking
def g93I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupShort 1 2 0 2 0 0 g93H5
  | 6 => lookupShort 2 83 0 6 1 3 g93H6
  | _ => fun _ => none
def g93 : Forest := ⟨93,6,fun i => g93Y[i]?.getD (0,0),g93C,g93A,g93L,g93I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g93P4_0 : block g93 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g93B4 : block g93 4 0 1=true := g93P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g93P5_0 : block g93 5 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g93B5 : block g93 5 0 2=true := g93P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g93P6_0 : block g93 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g93B6 : block g93 6 0 1=true := g93P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g93T : checkedTables g93 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g93 0 0 0 = true)
  · exact (rfl : block g93 1 0 0 = true)
  · exact (rfl : block g93 2 0 0 = true)
  · exact (rfl : block g93 3 0 0 = true)
  · exact g93B4
  · exact g93B5
  · exact g93B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g93G : graphValid g93 (boundsBefore K79) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low93 : Lower true (varsX 93) (graphGoal 93) 7 := lower_forest (g:=g93) (i:=0) (hints:=33555459) (before_sound K79 V79) g93G g93T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K93 := extendKnown K79 7 [(93,[]),(117,[98,67,83])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V93 : Known true K93 := extend_ok (m:=93) V79 low93 (by decide +kernel)
def g107Y : Array (Bits × Bits) := #[((sampleWord (w80 [0xfe3fc03f8fcff00f,0xf0fe3ff1e57c00000f0f])),(sampleWord (w80 [0x8a14a2a28520a8a8a8,0xa2848424257c99999999]))),((sampleWord (w80 [0xff003fffc00ffffff0,0xffc7fe13ad00f0f0f0])),(sampleWord (w80 [0xc190303064100c0c0,0xc4081040932911111111]))),(0x0,0x0),((sampleWord (w80 [0x3ffffff00fffff,0xff0007ffc4330f0f00ff])),(sampleWord (w80 [0x102004040802010101,0x100080000022222222]))),(0x0,0x0),((sampleWord (w80 [0xffffc00000000fffff,0xfffff8002a48f00fff00])),(sampleWord (w80 [0x204008081004020202,0x200100000044444444]))),((sampleWord (w80 [0xfffffffffffff00000,0x3996fff00000])),(sampleWord (w80 [0xc080303020080c0c0c,0x8c12609289688888888]))),(0x0,0x0),(0x0,0x0)]
def g107C : List ColumnInfo := [(1,0,106,0,7)]
def g107A : List (List Nat) := [[],[83],[97],[97,83]]
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
theorem low107 : Lower true (varsX 107) (graphGoal 107) 8 := lower_forest (g:=g107) (i:=0) (hints:=16777267) (before_sound K93 V93) g107G g107T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K107 := extendKnown K93 8 [(107,[]),(185,[64,49,33,32,117,101]),(206,[32,99,117]),(236,[32,49,97,65,117,84])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V107 : Known true K107 := extend_ok (m:=107) V93 low107 (by decide +kernel)
def g110Y : Array (Bits × Bits) := #[(0x0,0x0),((sampleWord (w80 [0xfe1ff00ff87f87ffc0,0x7fc7ffffd3b94000f0ff])),(sampleWord (w80 [0x1440a0a05101100285,0x2902008418941111111]))),((sampleWord (w80 [0x1ffff0007ff87fff,0x8007f1fc231ee00f0000])),(sampleWord (w80 [0x588ac4c5622a012b06,0x2b214491231ee7777777]))),((sampleWord (w80 [0x1fffffff80007fff,0xfff801ff9c1f30f00f0f])),(sampleWord (w80 [0x61030101800c220c08,0xc0188201c1602222222]))),(0x0,0x0),((sampleWord (w80 [0xffe000000000007fff,0xfffffe000be4bf000ff0])),(sampleWord (w80 [0x800c06060430443010,0x300200c20260b4444444]))),((sampleWord (w80 [0xffffffffffffff8000,0x6442cffff000])),(sampleWord (w80 [0x1008080040004020,0x40040100000008888888]))),(0x0,0x0),(0x0,0x0)]
def g110C : List ColumnInfo := [(4,0,106,0,7)]
def g110A : List (List Nat) := [[],[83],[49],[49,81],[81,49],[81]]
def g110D7 (j : Nat) := if j=0 then 0x3f else 0
def g110L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g110D7)
  | _ => emptyPacking
def g110I (_ _ : Nat) : Option (Nat × Nat) := none
def g110 : Forest := ⟨110,7,fun i => g110Y[i]?.getD (0,0),g110C,g110A,g110L,g110I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g110P7_0 : block g110 7 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g110B7 : block g110 7 0 1=true := g110P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g110T : checkedTables g110 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g110 0 0 0 = true)
  · exact (rfl : block g110 1 0 0 = true)
  · exact (rfl : block g110 2 0 0 = true)
  · exact (rfl : block g110 3 0 0 = true)
  · exact (rfl : block g110 4 0 0 = true)
  · exact (rfl : block g110 5 0 0 = true)
  · exact (rfl : block g110 6 0 0 = true)
  · exact g110B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g110G : graphValid g110 (boundsBefore K107) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low110 : Lower true (varsX 110) (graphGoal 110) 8 := lower_forest (g:=g110) (i:=0) (hints:=17831472) (before_sound K107 V107) g110G g110T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K110 := extendKnown K107 8 [(110,[]),(173,[16,118]),(174,[118]),(186,[66,118]),(248,[49,66,81,33,98,114])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V110 : Known true K110 := extend_ok (m:=110) V107 low110 (by decide +kernel)
def g143Y : Array (Bits × Bits) := #[((sampleWord (w80 [0xffc00ffc07fe03fff,0xe00ffffe07f469d401c7])),(sampleWord (w80 [0xa0a86a128d0a458a05,0x46a250a4b29029d49249]))),((sampleWord (w80 [0xfffff00007fffc07f,0xfff007fff813a68c0e38])),(sampleWord (w80 [0xc1304c1b160c891309,0x84c360c924d1a28c9249]))),((sampleWord (w80 [0xfffffffff8000007f,0xfffff800000bc8b47000])),(sampleWord (w80 [0x5c1705c182f0e1c2e,0x70382f1c70bc8b5b6db]))),((sampleWord (w80 [0xf0000000000000007f,0xffffffffffe6fe67803f])),(sampleWord (w80 [0x60180602030102030,0x8040300000654212492]))),(0x0,0x0),(0x0,0x0),(0x0,0x0),((sampleWord (w80 [0xffffffffffffffff80,0x1911bbffc0])),(sampleWord (w80 [0x80200800040000040,0x10080400000000024924]))),(0x0,0x0)]
def g143C : List ColumnInfo := [(1,0,142,0,5)]
def g143A : List (List Nat) := [[],[16]]
def g143D5 (j : Nat) := if j=0 then 0x3f else 0
def g143L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,g143D5)
  | _ => emptyPacking
def g143I (_ _ : Nat) : Option (Nat × Nat) := none
def g143 : Forest := ⟨143,5,fun i => g143Y[i]?.getD (0,0),g143C,g143A,g143L,g143I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g143P5_0 : block g143 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g143B5 : block g143 5 0 1=true := g143P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g143T : checkedTables g143 5 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g143 0 0 0 = true)
  · exact (rfl : block g143 1 0 0 = true)
  · exact (rfl : block g143 2 0 0 = true)
  · exact (rfl : block g143 3 0 0 = true)
  · exact (rfl : block g143 4 0 0 = true)
  · exact g143B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g143G : graphValid g143 (boundsBefore K110) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low143 : Lower true (varsX 143) (graphGoal 143) 6 := lower_forest (g:=g143) (i:=0) (hints:=1843) (before_sound K110 V110) g143G g143T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K143 := extendKnown K110 6 [(143,[]),(151,[33,67]),(167,[83,67]),(199,[16,32,99,67,84])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V143 : Known true K143 := extend_ok (m:=143) V110 low143 (by decide +kernel)
def g155Y : Array (Bits × Bits) := #[((sampleWord (w80 [0xfc3fe00ff87f87ffc0,0x7fffffe3dba15000ff0f])),(sampleWord (w80 [0x288140a05101100285,0x502004842a141111111]))),((sampleWord (w80 [0x3ffff0007ff87fff,0x807f1ffc2adc600f00f0])),(sampleWord (w80 [0x310984c26212011306,0x260444812acc43333333]))),(0x0,0x0),((sampleWord (w80 [0x3fffffff80007fff,0xff801fff949db0f000ff])),(sampleWord (w80 [0x421209048024222408,0x82889001410b4444444]))),((sampleWord (w80 [0xffc000000000007fff,0xffffe0000b66bf000f00])),(sampleWord (w80 [0x801c0e070438443810,0x30300e120946b6666666]))),(0x0,0x0),(0x0,0x0),((sampleWord (w80 [0xffffffffffffff8000,0x6442cffff000])),(sampleWord (w80 [0x2010080040004020,0x40401000000008888888]))),(0x0,0x0)]
def g155C : List ColumnInfo := [(1,0,154,0,5),(2,0,153,0,5),(8,0,147,0,5),(16,0,139,0,5)]
def g155A : List (List Nat) := [[],[48,65]]
def g155D6 (j : Nat) := if j=0 then 0x6c09f else 0
def g155L : Nat → Packing
  | 6 => (1,0,2,0,0,0,0,g155D6)
  | _ => emptyPacking
def g155I (_ _ : Nat) : Option (Nat × Nat) := none
def g155 : Forest := ⟨155,6,fun i => g155Y[i]?.getD (0,0),g155C,g155A,g155L,g155I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g155P6_0 : block g155 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g155B6 : block g155 6 0 1=true := g155P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g155T : checkedTables g155 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g155 0 0 0 = true)
  · exact (rfl : block g155 1 0 0 = true)
  · exact (rfl : block g155 2 0 0 = true)
  · exact (rfl : block g155 3 0 0 = true)
  · exact (rfl : block g155 4 0 0 = true)
  · exact (rfl : block g155 5 0 0 = true)
  · exact g155B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g155G : graphValid g155 (boundsBefore K143) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low155 : Lower true (varsX 155) (graphGoal 155) 7 := lower_forest (g:=g155) (i:=0) (hints:=51) (before_sound K143 V143) g155G g155T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K155 := extendKnown K143 7 [(155,[]),(157,[33,67]),(179,[83]),(181,[33,67,83]),(205,[96,16,33,66,84]),(213,[32,16,67,99,83]),(214,[32,99,83]),(217,[48,65,33,98,82]),(220,[32,49,97,81]),(244,[96,65,32,50,81])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V155 : Known true K155 := extend_ok (m:=155) V143 low155 (by decide +kernel)
def g158Y : Array (Bits × Bits) := #[(0x0,0x0),((sampleWord (w80 [0xffc01ff87fc3fff00,0xffff1ffed2e680007c1f])),(sampleWord (w80 [0x222894451108808a4a,0xa02444252268a5294a5]))),((sampleWord (w80 [0xffffe0007ffc3ffff,0xffffe11773400f83e0])),(sampleWord (w80 [0x40b018162050082c0c,0x2c140089146346318c63]))),((sampleWord (w80 [0xffffffff80003ffff,0xff001ffce8f541f0001f])),(sampleWord (w80 [0x84c120980261113010,0x30588900a8d154a5294a]))),((sampleWord (w80 [0xf0000000000003ffff,0xffffe0005f98fe0003e0])),(sampleWord (w80 [0x701c0e0438221c060,0x40600e104b9898c6318c]))),(0x0,0x0),(0x0,0x0),((sampleWord (w80 [0xfffffffffffffc0000,0x3280bbffffc00])),(sampleWord (w80 [0x80201000400020080,0x80801000000021084210]))),(0x0,0x0)]
def g158C : List ColumnInfo := [(2,0,156,0,5),(4,0,154,0,5),(8,0,150,0,5),(16,0,142,0,5),(10,0,148,0,4),(20,0,138,0,4)]
def g158A : List (List Nat) := [[],[66],[33,67],[33,49,65],[49],[49,66],[65,33,50],[65,50]]
def g158D4 := limbs80 #[#[0x9bd89544426d6215110,0x31825f635474]]
def g158D5 := limbs80 #[#[0x3527f7bbf6f4050110,0x5f405d50654155045435,0x66ad0941001546b525d4,0xc08024050462b13e3bb,0x4040201642000001201]]
def g158H5 (j : Nat) := if j=0 then 0x421668032 else 0
def g158D6 := limbs80 #[#[0x540a0380ff40fd40fd10,0x3140cc503]]
def g158H6 := limbs80 #[#[0x4838602858100870091c,0xd70000004000c,0xd94914c8a1009300000]]
def g158D7 (j : Nat) := if j=0 then 0x1605f else 0
def g158H7 := limbs80 #[#[0xf40048040014510090a,0x9510d59d3b3]]
def g158L : Nat → Packing
  | 4 => (3,3,3,0,0,4,0,g158D4)
  | 5 => (10,2,3,262147,34,7,1030,g158D5)
  | 6 => (3,1,3,0,0,6,0,g158D6)
  | 7 => (1,0,3,0,0,0,0,g158D7)
  | _ => emptyPacking
def g158I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupShort 1 7 0 6 2 2 g158H5
  | 6 => lookupShort 4 29 1 8 4 2 g158H6
  | 7 => lookupShort 3 17 4 7 2 3 g158H7
  | _ => fun _ => none
def g158 : Forest := ⟨158,7,fun i => g158Y[i]?.getD (0,0),g158C,g158A,g158L,g158I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g158P4_0 : block g158 4 0 3=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g158B4 : block g158 4 0 3=true := g158P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g158P5_0 : block g158 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g158P5_1 : block g158 5 1 9=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g158B5 : block g158 5 0 10=true := (@block_merge g158 5 0 1 9 g158P5_0 g158P5_1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g158P6_0 : block g158 6 0 3=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g158B6 : block g158 6 0 3=true := g158P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g158P7_0 : block g158 7 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g158B7 : block g158 7 0 1=true := g158P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g158T : checkedTables g158 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g158 0 0 0 = true)
  · exact (rfl : block g158 1 0 0 = true)
  · exact (rfl : block g158 2 0 0 = true)
  · exact (rfl : block g158 3 0 0 = true)
  · exact g158B4
  · exact g158B5
  · exact g158B6
  · exact g158B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g158G : graphValid g158 (boundsBefore K155) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low158 : Lower true (varsX 158) (graphGoal 158) 8 := lower_forest (g:=g158) (i:=0) (hints:=268571696) (before_sound K155 V155) g158G g158T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K158 := extendKnown K155 8 [(158,[]),(182,[83]),(188,[33,49,65,81]),(211,[32,16,67,99,83])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V158 : Known true K158 := extend_ok (m:=158) V155 low158 (by decide +kernel)
def g171Y : Array (Bits × Bits) := #[((sampleWord (w80 [0x7f01fc7f01fc7e7fc,0x7f1f9fe7ea000f00f0f])),(sampleWord (w80 [0x50a14290a142905028,0x50a414051ea111111111]))),((sampleWord (w80 [0x7ffe007ffe007f9ff,0xf801fe7f8b700f00f0f0])),(sampleWord (w80 [0x60c18320c183208430,0x60c821084b7111111111]))),(0x0,0x0),((sampleWord (w80 [0xf8000007fffff801ff,0xfffe007fe640f00f00ff])),(sampleWord (w80 [0x810204010204010040,0x81004010000222222222]))),(0x0,0x0),((sampleWord (w80 [0xfffffff800000001ff,0xffffff8001af000fff00])),(sampleWord (w80 [0x20408020408020081,0x2008020000444444444]))),(0x0,0x0),((sampleWord (w80 [0xfffffffffffffffe00,0x181ffff00000])),(sampleWord (w80 [0x40810040810040102,0x4010040000888888888]))),(0x0,0x0)]
def g171C : List ColumnInfo := [(1,0,170,0,7)]
def g171A : List (List Nat) := [[],[117],[83],[83,115],[115,83],[115],[16],[16,117],[16,83],[16,83,115],[16,115,83],[16,115]]
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
theorem g171G : graphValid g171 (boundsBefore K158) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low171 : Lower true (varsX 171) (graphGoal 171) 8 := lower_forest (g:=g171) (i:=0) (hints:=51) (before_sound K158 V158) g171G g171T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K171 := extendKnown K158 8 [(171,[]),(233,[97,33,66])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V171 : Known true K171 := extend_ok (m:=171) V158 low171 (by decide +kernel)
def g234Y : Array (Bits × Bits) := #[(0x0,0x0),((sampleWord (w80 [0xc0fc0fc0fdf81fbf7f,0x3f7efec0007c00f83ff])),(sampleWord (w80 [0x820820820810410202,0x8204040210842108421]))),(0x0,0x0),((sampleWord (w80 [0xff000fff01ffe03fbf,0xfc07f7f400f801f07c1f])),(sampleWord (w80 [0x41041041020820404,0x10408080421084210842]))),(0x0,0x0),((sampleWord (w80 [0xfffff00001ffffc03f,0xfff807f81f003e007fe0])),(sampleWord (w80 [0x82082082041040808,0x20810100842108421084]))),((sampleWord (w80 [0xfffffffffe0000003f,0xfffff803e0003fff8000])),(sampleWord (w80 [0x104104104082081010,0x41020201084210842108]))),((sampleWord (w80 [0xffffffffffffffffc0,0x3ffffc0000000])),(sampleWord (w80 [0x208208208104102020,0x82040402108421084210]))),(0x0,0x0)]
def g234C : List ColumnInfo := [(2,0,232,0,7),(8,0,226,0,7),(32,0,202,0,7),(64,0,170,0,7),(128,0,106,0,7),(10,0,224,0,4),(34,0,200,0,4),(40,0,194,0,4),(66,0,168,0,4),(72,0,162,0,4),(96,0,138,0,4)]
def g234A : List (List Nat) := [[],[118],[101],[101,117],[117,101],[117],[83],[83,118],[83,99],[83,99,115],[83,115,99],[83,115],[99,83],[99,83,117],[99],[99,115],[99,117],[99,117,83],[115,83,101],[115,83],[115,99],[115],[115,101,83],[115,101],[49],[49,118],[49,101],[49,101,117],[49,117,101],[49,117],[49,81],[49,81,118],[49,81,97],[49,81,97,113],[49,81,113,97],[49,81,113],[49,97,81],[49,97,81,117],[49,97],[49,97,113],[49,97,117],[49,97,117,81],[49,113,81,101],[49,113,81],[49,113,97],[49,113],[49,113,101,81],[49,113,101],[81,49],[81,49,118],[81,49,99],[81,49,99,115],[81,49,115,99],[81,49,115],[81],[81,118],[81,97],[81,97,113],[81,113,97],[81,113],[81,99],[81,99,115],[81,99,49],[81,99,49,113],[81,99,113,49],[81,99,113],[81,115,99],[81,115],[81,115,49,97],[81,115,49],[81,115,97],[81,115,97,49],[97,49,83],[97,49,83,117],[97,49],[97,49,115],[97,49,117],[97,49,117,83],[97,81],[97,81,117],[97],[97,113],[97,117],[97,117,81],[97,83,49],[97,83,49,115],[97,83],[97,83,113],[97,83,115],[97,83,115,49],[97,115,81,83],[97,115,81],[97,115,83],[97,115,83,81],[97,115],[97,115,49],[113,49,83,101],[113,49,83],[113,49,99],[113,49],[113,49,101,83],[113,49,101],[113,81,101],[113,81],[113,97],[113],[113,101,81],[113,101],[113,83,49,99],[113,83,49],[113,83,97],[113,83],[113,83,99,49],[113,83,99],[113,99,81],[113,99,81,83],[113,99,83,81],[113,99,83],[113,99,49],[113,99]]
def g234D3 := limbs80 #[#[0x887805915350d2148110,0x4180360709aa26498a40,0x2]]
def g234D4 := limbs80 #[#[0x54d214811050d2148110,0x4c93148110d4d2148110,0xd9131481105093148110,0xdc1654c9105d9544c910,0xf83d0e632cc3ad8ad21e,0x5c21bb21ab214c28ca98,0xea1cdaa3caa34c22bb22,0x440063a71c069ba52c1d,0xaedcb668c676cd5a3364,0x10100800040a0a0480b,0x32100a42c04000000]]
def g234H4 := limbs80 #[#[0x40000000f1000,0x83530]]
def g234D5 := limbs80 #[#[0x481104c5204412148110,0x443534811054d2044143,0x59532441604c91055132,0x54910d5132442654c910,0x443635491058d5244153,0x3ef55eadd3e3f0f58f52,0x54c3f1f0ee76bb1bccf6,0xd50c03747c4c8675309,0x541b55075721d5087553,0xd772345d4a364185906f,0x91137437d90dd643adc8,0x1dd9457658585917447d,0x473dc9c57696d924d729,0x77476dd1d87477dc1cb7,0x30b74b3dca8576835ca0,0xa8fc6e2309800774d15d,0x25b2ad3e9546a14e46a2,0xf1b89bfde8ec703619cc,0xafd71b4d72a1459ecd64,0x8020905ddecf579ec8e1,0x1800a9204000773d2060,0x17023b40503212040128,0xc00fc04879703003f602,0xcc0980990a0200017b88,0x9aa1b0100b210040480,0x41b2160200009b0d9080,0xd05682c0401682003]]
def g234H5 := limbs80 #[#[0x4214094e640084243,0x8c3003a91c3e00000030,0x219648c00000373e6,0x18709e3b2366c6000d25,0x663349114146560140c,0x138014c900001813c800,0x224de00000000000020,0xa498300000300008080,0x18610000408,0xf0048e1cc280010170e4,0x2106730647a,0x4a618000035a30400000,0x4b00000020f4140553a2,0xd31b1e1970478e3c02,0xc0318080d00004052,0xa1cc3040000000003624,0x32000000361a000c71]]
def g234D6 := limbs80 #[#[0xd4910549104c91048110,0x624484fefcf8dfdebf9f,0x163c6c705955a989532a,0x57aa2d5472c0e54cca18,0xc7358e3b1cd539ccab59,0x90c732f920782a0c801e,0xcce470e823bdb2c35827,0x84090e4b0610cce905a2,0xa13490a9f32904240e82,0x94010e8067802b9cd81d,0xa7c8253f046f920b6e18,0x67812147c4a79414be04,0x884a608b854340578086,0x39024f]]
def g234H6 := limbs80 #[#[0x86d820d0002ece86258,0x14,0x80059520000418a4f820,0x980000000025c0000000,0x100680000029808038,0x8d14000301120d782220,0x1c00000,0x1800000000000,0xc0360000000000000000,0x3801d000180240000005,0xe2800000008080007234,0xc31600013c00000002b9,0xc01600000000000,0x4002000000,0x0,0x10080000,0x23c280000000871400,0x8688000000000000,0x61cb000000000000000,0x6711000f81053e,0x4033307000c000000000,0xf1600000006686,0x338300480001870400,0x180291e40000c11a0,0xd90c0003346cd0c,0x100647c50000000000,0x41440001007804f00000,0xe0000000000002640300,0x11a2d90,0x10108000c6140,0x4f14d21400006438000,0x1180000001863000],#[0x41400604000061c00000,0x3e1c0000073280000000,0x11000101143c,0x0,0x86400000000,0x0,0x8f0200000002c8c00000,0x580008006806a327830b,0x60000000000048,0x0,0x184300002025,0x100700009914000000,0x1a23004b009e00600000,0x0,0x601ec1ac000000,0x430a00020898d0643940,0xb0000cf2002680472348,0xd1c000300,0x0,0x48c8e000000000000000,0x2e000102,0x3d1090700000,0x788f,0x20e800000000000000,0xa5180000000070c00000,0xf8000000083659862008,0x4004c0486d2a00]]
def g234D7 := limbs80 #[#[0x7f52442faa4887e48110,0x3015007f54910fe99221,0x94301030ba6694235a3f,0xa5011a6690a20e30ba66,0x38da6690a3c8a142a70,0x4]]
def g234H7 := limbs80 #[#[0x41c40000009000300048,0x1a1,0x0,0x6110000000000000,0x11e08000000671,0x0,0xbc5e0620,0x0,0x12840000000000,0x1824000000000018030,0x0,0x10020000000000,0x1005e00000000006186,0x0,0x6018000000000,0x0,0x9106441c600000000000,0x40000000000218200066,0x4c8,0xa00000000000000,0x0,0xe7070358000000002000,0x4045841,0x84000000000000000000,0x7512000000107407,0x61c30018000000000,0x261200060460000000,0x3e086bc600000000d040,0x8068048d8,0x10088001804,0x700000000,0x0],#[0x4042803800,0xc0c04d03561040002014,0x180000000000bc4e7050,0x601e000000000000019a,0x500e0000000000,0x1018000000040160000,0xbc68000000205000000,0x82140000002184000000,0x2f14000405d,0x49020,0x8000000004a000401200,0x9c3f092843,0x1c260,0x400200000]]
def g234D8 (j : Nat) := if j=0 then 0x2d2720806fd10 else 0
def g234H8 := limbs80 #[#[0x80084800000004900020,0xc0,0x3c00001b001d048,0x10400,0x0,0x44400000000000000,0x0,0x885100000000,0xc000000000000000e0c0,0x82,0x14001010000000,0xc0c0000,0x22200]]
def g234D9 (j : Nat) := if j=0 then 0x219080bf else 0
def g234H9 := limbs80 #[#[0x46001,0x12400a100179a4950,0x300100000,0x36b3c0]]
def g234L : Nat → Packing
  | 3 => (2,6,4,0,0,5,0,g234D3)
  | 4 => (14,5,4,524296,51,7,1029,g234D4)
  | 5 => (38,4,4,917518,68,9,1043,g234D5)
  | 6 => (18,3,4,458756,50,9,1046,g234D6)
  | 7 => (5,2,4,0,0,8,0,g234D7)
  | 8 => (1,1,4,0,0,0,0,g234D8)
  | 9 => (1,0,4,0,0,0,0,g234D9)
  | _ => emptyPacking
def g234I : Nat → Nat → Option (Nat × Nat)
  | 4 => lookupShort 1 11 0 10 1 7 g234H4
  | 5 => lookupShort 16 97 6 13 4 7 g234H5
  | 6 => lookupShort 30 307 3 15 6 7 g234H6
  | 7 => lookupShort 17 263 3 14 5 7 g234H7
  | 8 => lookupShort 4 97 2 10 3 5 g234H8
  | 9 => lookupShort 2 29 1 9 0 7 g234H9
  | _ => fun _ => none
def g234 : Forest := ⟨234,9,fun i => g234Y[i]?.getD (0,0),g234C,g234A,g234L,g234I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g234P3_0 : block g234 3 0 2=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g234B3 : block g234 3 0 2=true := g234P3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g234P4_0 : block g234 4 0 14=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g234B4 : block g234 4 0 14=true := g234P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g234P5_0 : block g234 5 0 4=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g234P5_4 : block g234 5 4 34=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g234B5 : block g234 5 0 38=true := (@block_merge g234 5 0 4 34 g234P5_0 g234P5_4)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g234P6_0 : block g234 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g234P6_1 : block g234 6 1 6=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g234P6_7 : block g234 6 7 11=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g234B6 : block g234 6 0 18=true := (@block_merge g234 6 0 1 17 g234P6_0 (@block_merge g234 6 1 6 11 g234P6_1 g234P6_7))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g234P7_0 : block g234 7 0 3=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g234P7_3 : block g234 7 3 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g234B7 : block g234 7 0 5=true := (@block_merge g234 7 0 3 2 g234P7_0 g234P7_3)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g234P8_0 : block g234 8 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g234B8 : block g234 8 0 1=true := g234P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g234P9_0 : block g234 9 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g234B9 : block g234 9 0 1=true := g234P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g234T : checkedTables g234 9 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g234 0 0 0 = true)
  · exact (rfl : block g234 1 0 0 = true)
  · exact (rfl : block g234 2 0 0 = true)
  · exact g234B3
  · exact g234B4
  · exact g234B5
  · exact g234B6
  · exact g234B7
  · exact g234B8
  · exact g234B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g234G : graphValid g234 (boundsBefore K171) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low234 : Lower true (varsX 234) (graphGoal 234) 10 := lower_forest (g:=g234) (i:=0) (hints:=286265392) (before_sound K171 V171) g234G g234T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K234 := extendKnown K171 10 [(234,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V234 : Known true K234 := extend_ok (m:=234) V171 low234 (by decide +kernel)
def g63Y : Array (Bits × Bits) := #[((sampleWord (w80 [0xf8001fffffff00ff57,0xa021d7a224003f03f03f])),(sampleWord (w80 [0x500d40250052161413,0x8001d0a2201041041041]))),((sampleWord (w80 [0xffffe0007fffff0029,0x7e9bc066080fc0000fc0])),(sampleWord (w80 [0x604981360464242629,0x2419c066085145145145]))),((sampleWord (w80 [0xffffffff800000009d,0x8e48a9b5c00000fc0000])),(sampleWord (w80 [0x820e0838217838381d,0x8a4881b5c134d34d34d3]))),((sampleWord (w80 [0xffffffffffffffffa0,0x49c585ccf7f000000fff])),(sampleWord (w80 [0x9002400980000080,0x48800508d4a28a28a28a]))),((sampleWord (w80 [0x91,0x75383e5b400000fff000])),(sampleWord (w80 [0x4e013804e00404080,0x75302e4802cb2cb2cb2c]))),((sampleWord (w80 [0x4e,0x937660389bffff000000])),(sampleWord (w80 [0x7001c007000808044,0x13662010030c30c30c30]))),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g63C : List ColumnInfo := [(2,0,61,0,7)]
def g63A : List (List Nat) := [[],[83]]
def g63D7 (j : Nat) := if j=0 then 0x7f else 0
def g63L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g63D7)
  | _ => emptyPacking
def g63I (_ _ : Nat) : Option (Nat × Nat) := none
def g63 : Forest := ⟨63,7,fun i => g63Y[i]?.getD (0,0),g63C,g63A,g63L,g63I⟩
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
  · exact (rfl : block g63 5 0 0 = true)
  · exact (rfl : block g63 6 0 0 = true)
  · exact g63B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63G : graphValid g63 (boundsBefore K234) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low63 : Lower true (varsX 63) (graphGoal 63) 8 := lower_forest (g:=g63) (i:=0) (hints:=1075) (before_sound K234 V234) g63G g63T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K63 := extendKnown K234 8 [(63,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V63 : Known true K63 := extend_ok (m:=63) V234 low63 (by decide +kernel)
def g95Y : Array (Bits × Bits) := #[((sampleWord (w80 [0xf8001fffffff00ff1d,0x203397a2ac000003f03f])),(sampleWord (w80 [0x520d4825205216141d,0x2390a2a91451451451]))),((sampleWord (w80 [0xffffe0007fffff0063,0x7e8b807608003f000fc0])),(sampleWord (w80 [0x604981360464242623,0x36098066085145145145]))),((sampleWord (w80 [0xffffffff800000009d,0x8e48e9a5400fc0fc0000])),(sampleWord (w80 [0x800e00380178383815,0xa48c1a54030c30c30c3]))),((sampleWord (w80 [0xffffffffffffffffa0,0x49c585ccf7f000000fff])),(sampleWord (w80 [0x9002400980000080,0x48c0050854a28a28a28a]))),((sampleWord (w80 [0x91,0x75383e5b400000fff000])),(sampleWord (w80 [0x4e013804e00404080,0x75102e5802cb2cb2cb2c]))),(0x0,0x0),((sampleWord (w80 [0x4e,0x937660389bffff000000])),(sampleWord (w80 [0x7001c007000808048,0x81362010830c30c30c30]))),(0x0,0x0),(0x0,0x0)]
def g95C : List ColumnInfo := [(1,0,94,0,7),(2,0,93,0,7),(4,0,91,0,7),(0,16,74,5,6),(16,0,79,0,6),(8,0,87,0,5),(64,0,31,0,5)]
def g95A : List (List Nat) := [[],[32,99]]
def g95D5 (j : Nat) := if j=0 then 0x4f77159653 else 0
def g95D6 := limbs80 #[#[0xdd8553bd58453be58053,0x59653fdd8553d7d4e53b,0x4018a1141f3185b2c0bf,0x41082628]]
def g95H6 (j : Nat) := if j=0 then 0xc else 0
def g95D7 := limbs80 #[#[0x47888807f94ffaa7fc53,0x2a5474365a891d90ea61,0x190e]]
def g95H7 := limbs80 #[#[0x1020033000a00014000,0x358800000]]
def g95D8 (j : Nat) := if j=0 then 0x468817f else 0
def g95H8 (j : Nat) := if j=0 then 0x38120022000000 else 0
def g95L : Nat → Packing
  | 5 => (1,3,3,0,0,0,0,g95D5)
  | 6 => (6,2,3,0,0,6,0,g95D6)
  | 7 => (3,1,3,0,0,7,0,g95D7)
  | 8 => (1,0,3,0,0,0,0,g95D8)
  | _ => emptyPacking
def g95I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupShort 1 2 0 2 0 0 g95H6
  | 7 => lookupShort 1 19 0 6 3 1 g95H7
  | 8 => lookupShort 1 11 0 5 2 1 g95H8
  | _ => fun _ => none
def g95 : Forest := ⟨95,8,fun i => g95Y[i]?.getD (0,0),g95C,g95A,g95L,g95I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95P5_0 : block g95 5 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g95B5 : block g95 5 0 1=true := g95P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95P6_0 : block g95 6 0 4=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95P6_4 : block g95 6 4 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g95B6 : block g95 6 0 6=true := (@block_merge g95 6 0 4 2 g95P6_0 g95P6_4)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95P7_0 : block g95 7 0 3=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g95B7 : block g95 7 0 3=true := g95P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95P8_0 : block g95 8 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g95B8 : block g95 8 0 1=true := g95P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95T : checkedTables g95 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g95 0 0 0 = true)
  · exact (rfl : block g95 1 0 0 = true)
  · exact (rfl : block g95 2 0 0 = true)
  · exact (rfl : block g95 3 0 0 = true)
  · exact (rfl : block g95 4 0 0 = true)
  · exact g95B5
  · exact g95B6
  · exact g95B7
  · exact g95B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95G : graphValid g95 (boundsBefore K63) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low95 : Lower true (varsX 95) (graphGoal 95) 9 := lower_forest (g:=g95) (i:=0) (hints:=16778291) (before_sound K63 V63) g95G g95T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K95 := extendKnown K63 9 [(95,[]),(119,[83])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V95 : Known true K95 := extend_ok (m:=95) V63 low95 (by decide +kernel)
def g111Y : Array (Bits × Bits) := #[((sampleWord (w80 [0xfffff8007fffffc03f,0xd563031b84f000000f0f])),(sampleWord (w80 [0x148154354254148585,0x1163031904d999999999]))),((sampleWord (w80 [0xffffff8007ffffc0,0x3acb2d005c4000f0f0f0])),(sampleWord (w80 [0x260260260360190909,0xba4304004c4111111111]))),((sampleWord (w80 [0xfffffffff8000000,0x771cc8d99400f000000])),(sampleWord (w80 [0x382b813813815e0e0e,0x6714c8d994777777777]))),((sampleWord (w80 [0xffffffffffffffff,0xc8133847ab90f00f00ff])),(sampleWord (w80 [0x400c00400400600000,0x103802830222222222]))),(0x0,0x0),((sampleWord (w80 [0xff0000000000000000,0x45c463c762f000fff00])),(sampleWord (w80 [0x3001801801801010,0x40c4004302444444444]))),(0x33a4d3e0015ffff00000,(sampleWord (w80 [0x80c006006006002020,0x1808360001888888888]))),(0x0,0x0),(0x0,0x0)]
def g111C : List ColumnInfo := [(1,0,110,0,8)]
def g111A : List (List Nat) := [[],[83]]
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
theorem low111 : Lower true (varsX 111) (graphGoal 111) 9 := lower_forest (g:=g111) (i:=0) (hints:=16778803) (before_sound K95 V95) g111G g111T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K111 := extendKnown K95 9 [(111,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V111 : Known true K111 := extend_ok (m:=111) V95 low111 (by decide +kernel)
def g123Y : Array (Bits × Bits) := #[((sampleWord (w80 [0x3fffffffffc1f5dac,0x248f2200000000fff03f])),(sampleWord (w80 [0x290290101008405488,0x4852211451451451451]))),((sampleWord (w80 [0xfc003ff83fffe0f208,0xe460b98003f03f000fc0])),(sampleWord (w80 [0x30130020809002f008,0x204039030c30c30c30c3]))),(0x0,0x0),((sampleWord (w80 [0xffffc0003fffff20ce,0x935842c0fc0fc0000fff])),(sampleWord (w80 [0x400401410120000044,0x93080084104104104104]))),((sampleWord (w80 [0xffffffffc000000d45,0x6956a9c000000003f000])),(sampleWord (w80 [0x8258258025c0840945,0x695289eebaebaebaebae]))),((sampleWord (w80 [0x1171,0x18b1dc3f000ffffc0000])),(sampleWord (w80 [0x6006020601080120,0x830c408208208208208]))),((sampleWord (w80 [0xce93,0x4f80057ffff000000000])),(sampleWord (w80 [0x38038043802100e93,0x44800070c30c30c30c30]))),(0x0,0x0),(0x0,0x0)]
def g123C : List ColumnInfo := [(0,16,106,1,8),(16,0,107,0,8),(1,16,106,0,7),(2,0,121,0,7),(8,0,115,0,7),(32,0,91,0,7),(64,0,59,0,7),(66,0,57,0,5),(10,0,113,0,4),(34,0,89,0,4),(72,0,51,0,4),(96,0,27,0,4)]
def g123A : List (List Nat) := [[],[83],[97],[97,83]]
def g123D5 := limbs80 #[#[0x54521549414854250521,0x48576551215495148542,0xe6759c76e9b663ddc564,0xc284c28db28cb28f27a9,0xb232c2aeaa28ba9eaa15,0x54a1324448063ad1c0cb,0x206100b5a74676c,0x301404000000]]
def g123D6 := limbs80 #[#[0x54921545215092150521,0xd9121595215912155121,0x50951d854258542d9521,0xd9deeef3f7dbdd7e7f1f,0xab0a9152841f9f5fa7bb,0x2844fb283aca18a9006e,0xe6e22fb213ac852aa16,0xba89aea2db28b2ca36aa,0xa5baaa6e2a2bb236c867,0xeae3baaaeeaaa3aabee2,0x16eb23bb58ae903ba30a,0x2911876331384c002bad,0xb654a7524883e1c0c85a,0x17037bbbdcadd69b2d86,0x3700a238d4e7f2b8f44e,0x100d418786931d509c8,0x10060279e043b40adb2,0xa0328264264280806a0b,0x10100001a0c58750580,0x23ab0d21000032100404,0xb611e0432cf]]
def g123H6 := limbs80 #[#[0x1500c00000680000008,0x4300a7000000c50,0xd189000000000,0xc89000000000000,0xa9000000000000b7000,0x470000000000000,0xc1e0000,0xc4c6000000000,0x200008a0]]
def g123D7 := limbs80 #[#[0x49413fff7eefd5150921,0x1650d901641548542254,0x42b594d6435503614d94,0xe511e09c3000f617585d,0xa1ef3713457ea6479f0c,0x26294b46392ac98e4449,0x880c8a0a17b4ba8780c2,0x101d8f00ef6806600aff,0x135ec0253600e790247d,0x7263611b381278422ee1,0x19f982b6d2070bc8]]
def g123H7 := limbs80 #[#[0x9180000440000005304,0x400000000,0x0,0x0,0x0,0x31400000000000,0x16e0000000,0x3871bcd474000000000,0xc80060c0000000,0x1950000000000,0xa9de0000000000,0x13200480011a50000000,0x0,0x3280000000000000,0x21b9c85,0xe4380000000000000,0x60000047800,0x0,0x2004580000b30029e000,0x18900002012600000011,0x488000000810000,0x0,0x44000000000,0x30200000000000,0x12e9126,0x18018c0e000000045800,0x12e00160000000007]]
def g123D8 := limbs80 #[#[0x879aa407f50bfaa3fd21,0x90c3ac69238d145aa324,0x11b4ca4]]
def g123H8 := limbs80 #[#[0x10000000000000052644,0xc1720024002d0049619,0xd0000d60000808a71000,0x4000,0x700004b0000000,0xa28e8800c600030,0xc5eee8cc00c20]]
def g123D9 (j : Nat) := if j=0 then 0x1654321bf else 0
def g123H9 := limbs80 #[#[0xac000000600840500000,0x4]]
def g123L : Nat → Packing
  | 5 => (11,4,4,524294,51,7,1027,g123D5)
  | 6 => (30,3,4,851980,68,9,1042,g123D6)
  | 7 => (15,2,4,262147,34,9,1047,g123D7)
  | 8 => (3,1,4,0,0,7,0,g123D8)
  | 9 => (1,0,4,0,0,0,0,g123D9)
  | _ => emptyPacking
def g123I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupShort 4 97 1 8 4 2 g123H6
  | 7 => lookupShort 11 239 2 9 5 2 g123H7
  | 8 => lookupShort 6 67 2 8 4 2 g123H8
  | 9 => lookupShort 1 17 0 6 2 2 g123H9
  | _ => fun _ => none
def g123 : Forest := ⟨123,9,fun i => g123Y[i]?.getD (0,0),g123C,g123A,g123L,g123I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P5_0 : block g123 5 0 11=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g123B5 : block g123 5 0 11=true := g123P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P6_0 : block g123 6 0 3=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P6_3 : block g123 6 3 27=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g123B6 : block g123 6 0 30=true := (@block_merge g123 6 0 3 27 g123P6_0 g123P6_3)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P7_0 : block g123 7 0 9=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P7_9 : block g123 7 9 6=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g123B7 : block g123 7 0 15=true := (@block_merge g123 7 0 9 6 g123P7_0 g123P7_9)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P8_0 : block g123 8 0 3=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g123B8 : block g123 8 0 3=true := g123P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P9_0 : block g123 9 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g123B9 : block g123 9 0 1=true := g123P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123T : checkedTables g123 9 := by
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
  · exact g123B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123G : graphValid g123 (boundsBefore K111) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low123 : Lower true (varsX 123) (graphGoal 123) 10 := lower_forest (g:=g123) (i:=0) (hints:=16777267) (before_sound K111 V111) g123G g123T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K123 := extendKnown K111 10 [(123,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V123 : Known true K123 := extend_ok (m:=123) V111 low123 (by decide +kernel)
def g125Y : Array (Bits × Bits) := #[((sampleWord (w80 [0xffffff83fffff242e8,0x44f46d0000000fe03fff])),(sampleWord (w80 [0x80a4010808040240a0,0x4444d42850a142850a1]))),(0x0,0x0),((sampleWord (w80 [0xffffc1ffe06b488,0xfcbc20003f8001fc000])),(sampleWord (w80 [0x12c08a00410822b088,0x78b40162c58b162c58b]))),((sampleWord (w80 [0xfff000001ffffbd84e,0x91211a01fc07f000007f])),(sampleWord (w80 [0x3002c10805001804c,0x1121120c183060c18306]))),((sampleWord (w80 [0xffffffffe0000804f6,0x691ab3000000001fff80])),(sampleWord (w80 [0x240930001260480456,0x6810b2a952a54a952a54]))),((sampleWord (w80 [0x91711,0xa28774fe0007ffe00000])),(sampleWord (w80 [0x3801c0210380881601,0xa282203060c183060c18]))),((sampleWord (w80 [0x4e917,0x7e4005fffff800000000])),(sampleWord (w80 [0xc00e00421c01044912,0x484005c183060c183060]))),(0x0,0x0),(0x0,0x0)]
def g125C : List ColumnInfo := [(1,0,124,0,7),(4,0,121,0,7),(8,0,117,0,7),(16,0,109,0,7),(32,0,93,0,7),(64,0,61,0,7),(0,4,41,80,6),(0,16,104,5,6),(1,16,104,4,5),(4,16,104,1,5),(17,0,108,0,5),(20,0,105,0,5),(64,4,41,16,5),(68,0,57,0,5),(5,0,104,0,4),(5,16,104,0,4),(9,0,116,0,4),(12,0,113,0,4),(33,0,92,0,4),(36,0,89,0,4),(40,0,85,0,4),(72,0,53,0,4),(96,0,29,0,4)]
def g125A : List (List Nat) := [[],[83],[96,66],[96,66,83]]
def g125D5 := limbs80 #[#[0x50940483aa5954250120,0x483ca5514254120eab65,0x1d372595208ef825d954,0x10185b54f032b]]
def g125D6 := limbs80 #[#[0x50920505205012050910,0x59520591205512054120,0xd9121d8121d9520d9120,0x5895050950d814258542,0xbefd7bb7d7e7f2fd8950,0xa107f5ebf577b7dbbdbe,0x2b285f6302ee000dd0f6,0x94aa1377226a8449d943,0x6db20977424ec849590,0xd4c2bb163651c2ca3c55,0xdc8e7ba1d37238aea81d,0x15d123ba1db743b0e878,0xb15d142ba40f7478cece,0xc040005bab057568ae0,0x753416ca64b218ec6427,0x9ec55c2c1509f4b23102,0x8a2b0d813e9e4e970b5d,0x10b0a880440127532954,0x8007811919694170d9e0,0x56820000000001a43648,0x40000020140580990cd0,0x21000000802020080ed0,0x3210000008b0805]]
def g125H6 := limbs80 #[#[0x2080000280084205,0x320086ae4a]]
def g125D7 := limbs80 #[#[0xedd50509314c12148110,0x5aa05a8046c63fffbeef,0x8eca4aca4ec84ac85284,0x62840ec14ec88ec08ec5,0x62c862a862c262a26282,0x26c5a2c5a285a284e2ca,0x10c41b0022c362c16285,0x460fc364c0298851c05,0xd759c26b98f5ed695493,0xc4276976458c61b815e,0x21492585000944888187,0x8498e410f2002a1040c2,0x918dc6a22e54e0b0c6c4,0xc27b53096ceec928b145,0x273180497fe0c262ccc3,0x87db8039f0e0147ffa00,0x2f092ee82f22df3e1022,0xab2625bc4897cf32913d,0xc08de0c5352b69183c98,0x2ee3240f2463399848f3,0x6c252f42635d143be509,0x5e4bc4d7c]]
def g125H7 := limbs80 #[#[0x43c00380,0x0,0x448000000000000,0x1848000049c00000,0x0,0x980181000,0xe800000000f80000001,0x68800000000000d000,0x189000,0x1808000000000000,0x29600216,0xa0000000000000,0x0,0xc0010500000000,0xe5800000000000000000,0x0,0x0,0x23000000000a80000000,0x368680000409,0x102e1901800,0x4220021d90000,0x83800878000000000432,0x50963000000000010e,0x880000b8000000000000,0xc340c000000000000001,0x0,0xa280000000000000002c,0x3984001]]
def g125D8 := limbs80 #[#[0xd21fea87f4c3fa41fd10,0xd210c024007f50bfa63f,0x10882640e230f161cea5,0x2259222891464009648e,0x98c23071648a3221300,0x18040899222cc2059018,0x1c65258e]]
def g125H8 := limbs80 #[#[0x420000020014,0x78300000000000000000,0x49428000000564c,0xc0000000008bd1,0x11165800000000,0xad0c0030a00,0x3700000,0x0,0x1cc006400000000,0x304000000112000,0x4e00000005800400000,0x28000000,0x3800000000,0x9b000015300,0x8f10002800002880000,0x29986004c8000d,0x13260000003470b00000,0x1b50000001150b2,0x1f030f0680000000]]
def g125D9 (j : Nat) := if j=0 then 0xa4188201bf else 0
def g125H9 := limbs80 #[#[0x20004400000000403600,0xc40600001a4301400008,0x25000000000,0x48000000006400000000,0x1c000002600000000167]]
def g125L : Nat → Packing
  | 5 => (5,4,5,0,0,6,0,g125D5)
  | 6 => (33,3,5,917521,69,9,1037,g125D6)
  | 7 => (26,2,5,327687,51,10,1063,g125D7)
  | 8 => (7,1,5,0,0,9,0,g125D8)
  | 9 => (1,0,5,0,0,0,0,g125D9)
  | _ => emptyPacking
def g125I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupShort 2 17 3 7 3 2 g125H6
  | 7 => lookupShort 11 227 1 10 6 2 g125H7
  | 8 => lookupShort 11 167 2 9 5 2 g125H8
  | 9 => lookupShort 3 59 0 7 3 2 g125H9
  | _ => fun _ => none
def g125 : Forest := ⟨125,9,fun i => g125Y[i]?.getD (0,0),g125C,g125A,g125L,g125I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g125P5_0 : block g125 5 0 5=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g125B5 : block g125 5 0 5=true := g125P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g125P6_0 : block g125 6 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g125P6_2 : block g125 6 2 31=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g125B6 : block g125 6 0 33=true := (@block_merge g125 6 0 2 31 g125P6_0 g125P6_2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g125P7_0 : block g125 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g125P7_1 : block g125 7 1 11=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g125P7_12 : block g125 7 12 14=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g125B7 : block g125 7 0 26=true := (@block_merge g125 7 0 1 25 g125P7_0 (@block_merge g125 7 1 11 14 g125P7_1 g125P7_12))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g125P8_0 : block g125 8 0 7=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g125B8 : block g125 8 0 7=true := g125P8_0
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
  · exact g125B5
  · exact g125B6
  · exact g125B7
  · exact g125B8
  · exact g125B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g125G : graphValid g125 (boundsBefore K123) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low125 : Lower true (varsX 125) (graphGoal 125) 10 := lower_forest (g:=g125) (i:=0) (hints:=33555459) (before_sound K123 V123) g125G g125T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K125 := extendKnown K123 10 [(125,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V125 : Known true K125 := extend_ok (m:=125) V123 low125 (by decide +kernel)
def g126Y : Array (Bits × Bits) := #[(0x0,0x0),((sampleWord (w80 [0x3fffffc1ffff60ac8,0x4caee8000007f01fc07f])),(sampleWord (w80 [0x280280084044060880,0x400ce80a142850a14285]))),((sampleWord (w80 [0xfc003ffffffe021c2c,0x13d9d30003f800003f80])),(sampleWord (w80 [0x304b04500208221c28,0x3c941264c993264c993]))),((sampleWord (w80 [0xffffc0001ffffbf0cb,0x81210b01fc000fe0007f])),(sampleWord (w80 [0x400c0160809009404a,0x12103142850a142850a]))),((sampleWord (w80 [0xffffffffe0000824f7,0x691ab200000000003f80])),(sampleWord (w80 [0x8290298014e04820d7,0x6812b2d9b366cd9b366c]))),((sampleWord (w80 [0x93710,0xa28774fe00000fffc000])),(sampleWord (w80 [0xe00e010700803700,0xa2821060c183060c1830]))),((sampleWord (w80 [0x4c917,0x7e4005fffffff0000000])),(sampleWord (w80 [0x30030021801008015,0x1c000481020408102040]))),(0x0,0x0),(0x0,0x0)]
def g126C : List ColumnInfo := [(0,16,106,4,8),(16,0,110,0,8),(2,0,124,0,7),(4,16,106,0,7),(8,0,118,0,7),(32,0,94,0,7),(64,0,62,0,6),(10,0,116,0,4),(34,0,92,0,4),(40,0,86,0,4)]
def g126A : List (List Nat) := [[],[83],[49],[49,81],[81,49],[81]]
def g126D4 (j : Nat) := if j=0 then 0x1a2b6460b5454120 else 0
def g126D5 := limbs80 #[#[0x54120549404814250120,0x4817655120d515048152,0xd935448170d5120dc165,0xeab9ae3b5acbadaa3e3e,0x917530aa17d943aca3ca,0xec8c98269ba26d9132c8,0x4018e94585e7b260e022,0x1dba72e1bb66ad199222,0x8080000041017]]
def g126H5 (j : Nat) := if j=0 then 0xec else 0
def g126D6 := limbs80 #[#[0x59120551205412050120,0xd9120d51209952059520,0xd49505895054950d9520,0xeb7d7e7f2f58b50d8950,0x420fd7abbddadf6bf3f7,0x1d650b54803744854869,0x5065541bdc86d5217d94,0x5594937417d905d6419d,0x566d91917061dd885762,0x370415d5c775315d9956,0x11b74461d11f7043dd11,0xdc24574815d9517051dd,0xa25d2d764b5d92677094,0xc2207800774d15d30f74,0x10879389a4b44d220ec5,0x371a8cb61add54a24ca3,0x9d4ba4d1d8ac21f6ee73,0x95c4602f170b1d629743,0x3987c41124205c43700b,0xa8139b04280ad6a00c82,0x4000099104100201da0,0x100d411a0800062c200c,0x4016823415a080202000,0x96160356100009908000,0x3ac2000001]]
def g126H6 := limbs80 #[#[0x30000000001829040,0x8928000002000000,0x5300001970028c000,0x5000000010b83010180,0x1090000159070000,0x10b00,0x5293006a80000,0x4e0064acc0000c500102,0x47600098a40000000002,0xc26]]
def g126D7 := limbs80 #[#[0x9403fffb7eff5054120,0x5524d941650d90164254,0x643d50d54058a3625d49,0x3d89d627549e653594d,0x224f46b2d12476260a0,0x79a49622fc7736584b15,0x409c08085914571ce218,0x2ad0025640614e07d51,0x24ac01588239810c40c2,0x40a7f6019f008b5043e0,0x3c06f520a1f82460117b,0x4e23]]
def g126H7 := limbs80 #[#[0x3046404d489042b00c00,0x400108c0000000000042,0x72600ba0312c0000022,0x2308130001264441ad,0x68a51200185015032,0x3000322416d0a00,0xa00098b2901001da800,0x91601404000001824002,0xf3340000080400110000,0x8400000c232100000001,0x9fd8824000407c298,0x604da609b6400b5a0000,0xc43a00203200c1a33c24,0x24001228008368940009,0x48f26e1ec8680661c0c8,0x4a149908b0f800c39]]
def g126D8 := limbs80 #[#[0xc79aa407fd43faa1fd20,0x98d13568298d131ea414,0x1ad046]]
def g126H8 := limbs80 #[#[0x60000000000148602,0x2f00400000000,0x10d003400,0x40000321ca40082d020,0x15280c40000226000005,0xa80000010410470000e0,0x220700000c90001,0x20f000000031140e300,0xa002090,0x18700000003270,0x300dac0c000000]]
def g126D9 (j : Nat) := if j=0 then 0x1542317f else 0
def g126H9 := limbs80 #[#[0x3190a6200200418a0803,0x92]]
def g126L : Nat → Packing
  | 4 => (1,5,4,0,0,0,0,g126D4)
  | 5 => (13,4,4,589832,67,7,1026,g126D5)
  | 6 => (39,3,4,786446,68,9,1040,g126D6)
  | 7 => (18,2,4,262147,34,9,1040,g126D7)
  | 8 => (3,1,4,0,0,7,0,g126D8)
  | 9 => (1,0,4,0,0,0,0,g126D9)
  | _ => emptyPacking
def g126I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupShort 1 2 0 4 0 2 g126H5
  | 6 => lookupShort 7 79 3 9 4 3 g126H6
  | 7 => lookupShort 18 107 5 11 6 3 g126H7
  | 8 => lookupShort 8 83 3 10 5 3 g126H8
  | 9 => lookupShort 2 13 2 7 2 3 g126H9
  | _ => fun _ => none
def g126 : Forest := ⟨126,9,fun i => g126Y[i]?.getD (0,0),g126C,g126A,g126L,g126I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P4_0 : block g126 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g126B4 : block g126 4 0 1=true := g126P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P5_0 : block g126 5 0 13=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g126B5 : block g126 5 0 13=true := g126P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6_0 : block g126 6 0 3=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6_3 : block g126 6 3 36=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g126B6 : block g126 6 0 39=true := (@block_merge g126 6 0 3 36 g126P6_0 g126P6_3)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P7_0 : block g126 7 0 10=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P7_10 : block g126 7 10 8=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g126B7 : block g126 7 0 18=true := (@block_merge g126 7 0 10 8 g126P7_0 g126P7_10)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P8_0 : block g126 8 0 3=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g126B8 : block g126 8 0 3=true := g126P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P9_0 : block g126 9 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g126B9 : block g126 9 0 1=true := g126P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126T : checkedTables g126 9 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g126 0 0 0 = true)
  · exact (rfl : block g126 1 0 0 = true)
  · exact (rfl : block g126 2 0 0 = true)
  · exact (rfl : block g126 3 0 0 = true)
  · exact g126B4
  · exact g126B5
  · exact g126B6
  · exact g126B7
  · exact g126B8
  · exact g126B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126G : graphValid g126 (boundsBefore K125) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low126 : Lower true (varsX 126) (graphGoal 126) 10 := lower_forest (g:=g126) (i:=0) (hints:=17962032) (before_sound K125 V125) g126G g126T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K126 := extendKnown K125 10 [(126,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V126 : Known true K126 := extend_ok (m:=126) V125 low126 (by decide +kernel)
def g159Y : Array (Bits × Bits) := #[((sampleWord (w80 [0xff000ffffff80fe5f3,0xf07c7c000040675b])),(sampleWord (w80 [0x2a06a04a02916285f1,0x249108484000000211b]))),((sampleWord (w80 [0xfffff000fffff019b8,0xa00700038061898794a7])),(sampleWord (w80 [0x4c24c26c232244d9b0,0xab595294942008821407]))),((sampleWord (w80 [0xffffffff0000000545,0xb0380f8000020e3818c3])),(sampleWord (w80 [0x700700700bc3870545,0xb6cb318d8c020a1000c3]))),((sampleWord (w80 [0xffffffffffffffea2b,0x81c00003ff83f03fe0f5])),(sampleWord (w80 [0x804804804c0000020a,0x4a6a5292a8aa23cc0e0]))),((sampleWord (w80 [0x480,0x7e000ffc03fc003fff02])),(sampleWord (w80 [0x7007007004080000,0x4934c630332820a75e24]))),(0x0,0x0),(0x0,0x0),((sampleWord (w80 [0x1354,0x4ffff00003ffffc00008])),(sampleWord (w80 [0x8008008000000000,0x842405145400000]))),(0x0,0x0)]
def g159C : List ColumnInfo := [(1,0,158,0,8),(2,0,157,0,7),(4,0,155,0,7),(8,0,151,0,6),(16,0,143,0,6),(6,0,153,0,5),(9,0,150,0,5),(10,0,149,0,5),(12,0,147,0,5),(18,0,141,0,5),(20,0,139,0,5),(128,0,31,0,5),(11,0,148,0,4),(14,0,145,0,4),(22,0,137,0,4),(130,0,29,0,4),(132,0,27,0,4)]
def g159A : List (List Nat) := [[],[33,67]]
def g159D4 := limbs80 #[#[0x32a87993746007154d43,0x81dc16550f1c304c0ae0,0x75c830db92a921e38e0b,0xaa74e39259170185538,0xf624c3021e730b22e03]]
def g159D5 := limbs80 #[#[0x58053dd95314f7154c53,0x14d53584535516014d53,0x5516214d535885355161,0x995315d9544c55354531,0x50543545415db544c574,0x5c06550d65195435db53,0x54d431c55350c6554d43,0x50c7159543dc55350d76,0x5d3515477159543dc165,0x185535906154d74d8d51,0x54d74d4d535906454d70,0x5936154d54d85531d361,0x58a43dc95490d74d8553,0xcc574d4e53d516290d53,0x5d351cc574997315d954,0x58f411d563d055350f41,0xd4563d4f415d563d0554,0x1c964d4f7150f515d943,0xa76799ce3e8f63b8be1f,0xaf2baae6b6ad6b3a9e9e,0xcf339cd727c7af4b5ad5,0xf17b4ec7a5e8f95d9755,0x70448f81249c013a5908,0x129b829c5c1143e04b1,0x46fd53305c14c2e0a527,0x4ef82aa8ba589e1a8170,0xaf81ad4c152b60696301,0x380b70a9dc2e0983704b,0x8048ec0a086010170569,0x42a3b279dd119300893,0x3c1c39d3594f83028458,0x6e40ab7dc55b8e2add81],#[0xbc0c56dc96b6e4a5f815,0xc107ee042130d0a9838f,0x38fde0466f042d78711d,0x355e041aeec07164005c,0x2de0997f00cdf646aeb2,0x4e0206f04fbf807c7c3b,0xe0205b06eb782785c140,0xa40f0ed978271bc140f,0x841904409001cc05e5e,0x18c5b14449104390c429,0x28c9b24c8b20c7b1cc6b,0x390db34ccb30cbb2ccab,0x4911c4510c410fc3d0ec,0x5915c5514c5113c4d12c,0x6919c6518c6117c5d16c,0x7b1e4771d4731c46e1ac,0x8b22487214832047f1f4,0xb0dc4604082634,0x10100000000000000,0x0,0x400000000,0x0,0x0,0x1909810]]
def g159H5 (j : Nat) := if j=0 then 0xd5409002000016005000 else 0
set_option maxRecDepth 32000 in
def g159D6 := limbs80 #[#[0x58453580535505354c53,0x54531545219505358853,0x59531591315513154d31,0x5454150d41d513199531,0x99541595415514154d41,0x5954354d4319543d4d41,0xd8543d4d439954394d43,0x5515154d5150d51d9543,0xd9151d8d51d455159151,0x58953551531915318553,0xd4d53991539515359153,0x54e43d9153d8953d8553,0x95253d524358a4355243,0x5533154f3150731d4e53,0xd4731997315973159331,0x5534154f4150f41d5331,0xd4f41997415974158f41,0x58f515535154f5150f51,0xf9f4f677375935359351,0xfa7cfdfafb7cbdddedf3,0xfabbedeeef6fb6daecf5,0x5530ff9fafb7d7e7eef5,0x4801dc895553762dc45d,0xe25c4a8d702a1dca4315,0x54c13953622dc4b8f702,0x80316400e54c23d53070,0xf1520c1dca4a170480dd,0x6411bdc444d640fb54c3,0x1245d84b564127dc84c5,0x45d8699731a95c469376,0xd05cf71164dd454f7114,0xae9546bb54da9174184d],#[0xd7377b54dda6756b3595,0x16d35d9dcd657695d1de,0xe7dc9ba7716f1591b6f7,0x5cde13766e45d9bb5646,0x1ccf71724dd5c1176786,0xdd531fa50c79174744dd,0x531dadc4769541f7d4c7,0x205dd4715751cd594761,0x55d0a2571284dd882771,0xcc8e77223adc48917628,0x99373252dc894f71245d,0x5757ad595ee1537a45cc,0x67d158df27717c5dd5e9,0x655d21c563864dd9f117,0x1d60137580d552011768,0x9fc7758119d604575811,0x9173844dce097737f9dc,0x533a95d10a57343754d0,0x3c9dc4f13763b1d8ced9,0x7dc8fa7713e45d115f71,0x4e227718845cd19f7240,0x2117688d592245638965,0x3748f3dc63df718a4dda,0x3912dca41f72907dca31,0xc45d4db55437154cd937,0xd94b2c652c5dd0b27712,0x8b6f712db1c4b11762cb,0x60742d8950b61542c6dc,0x762d6d94b58652d8dd0b,0x3469d8c1975318950c44,0x95c4aa9702abd94d1574,0xc4bab702e49d8aad652a],#[0xbcc712f4dc0baf652e9d,0x3732f1dccb93712f3dc4,0x46245c4e117332bd94c9,0x11dd97ef715f2d518c95,0x99582d65606dcd81f726,0x1515404b5959197364b,0x49540939501cd5407495,0x7601159006f710129502,0xad59029376027dc80c7,0x99d924f6449359121176,0x8d66f53593d8964d6258,0x64d6459319166f73593d,0xd725845d164f64593991,0x459355164f73593dc964,0x935d164c74593d5164e5,0x5d16a7714f3dd164e745,0x149973526dcd31974564,0x277150adc1435644add9,0x715cdd9152571547dc94,0x9265cd999746845c9711,0x2dca4c872924dc649f72,0x1d81880f00a000137293,0xd84784283e83782e8268,0x87a86e86886285c85684,0xa40a009989208c08607f,0x88c30bf0ba8b48b08aa0,0x8e98e28dc0d60d20cc8c,0xb9079020fe0f70f18ed,0x693292c12311f11b1141,0x15114b14714313f13b13,0x8317a97416d96716095a,0x69a099c19619218c1879],#[0x1c51c11bb1b59b11aa9a,0xed9e51de1da1d59cf9c9,0x320d2092031ff1f91f21,0xa36a32a2ea2aa2421da1,0x5fa59a5324f24723f23a,0x7a83a7fa7a27426ca65a,0xaacaa629ca96a9028c28,0xceac8ac4abe2ba2b62b0,0x22ee2e8ae4ae0ad9ad32,0x31ab1130b304afe2f7af,0x3db39b3332f32b327323,0x4b60b5cb56b52b4bb453,0xb84b7bb76370b6cb68b6,0xa3b9fb9b39739338db89,0xbbc63c23bb3b73b0baab,0x3eb3e4be0bda3d63cfbc,0x14407c023fe3fa3f63ef,0x143a433c2d42541f41b4,0xc67c5e45a45244bc4544,0x8a483c7e47a47646fc6b,0xf4a8ca4ca0c98c9248e4,0x4cb4c74c34bccb74b34a,0xee4ea4e44e04d9cd5ccf,0xd0a5045004fa4f64f24,0x490a0858201810380700,0x186d0a140b007e0a1b10,0x411d1060308054202914,0x989013f44680ed521e00,0x90100b8893962da42cc,0x44502502502502cd9894,0x4d916a0ea0b80901d1d3,0x1b21005816a0804d0],#[0x2c229a09908052100602,0x8d0802908006c3484000,0x100581674c400001b0a,0x19a0e72c464200000000,0x403b5421a08d0668334,0x35610032100ca0804a08,0x6c846820000642c040,0x1282f0100572851b080,0x1a08d0699a4928201642,0x3a843a840100000000,0x99097228d86506504682,0x5439411a080004000180,0x100ab08000521005816d,0x8030100004d856820132,0x9da87282b419a0a80d80,0x5080268200000001b942,0xd4100ad856832,0xc0400028c98980b01000,0xb41b21e60400020000,0xda0802d0401808076c2,0x129080000056c201b410,0x2c3b685642007816ae5d,0x45a145862c2019b0f586,0x9080002c08000309a180,0x10000db428b080006d06,0x820000015616020000b4,0x80000000590802d04016,0x19080590]]
def g159H6 := limbs80 #[#[0x84ab2b880c8162000a0,0x4bd14400084ca3e015e4,0x660a24f42a8a3038c520,0x41c002081b00000,0x22507c004dc2704f21,0x1190b81e000110031c,0x50545854004614484aa4,0xd0045083b0b10a00033,0xc680000000000008ad3f,0x323c0b0ba7524cf306,0x84229000a70000000000,0x20e00039000a300000,0xa940049b3a0000000205,0x2090d79e0034000000,0xda17002840000008930,0x10c0010d00138c3c00,0x47416001a610f014b400]]
set_option maxRecDepth 32000 in
def g159D7 := limbs80 #[#[0x54d5150d414c52114c43,0xbb7afd4f51d073194e43,0x63bfffdf7efdfbfbebdb,0x4d611458049628198ec5,0x448f6170990416412588,0x854ce551359949565295,0x1a9506966535594d5643,0x665a55969564a854ea75,0x51565475511d43495451,0x596dd54b558edd43b599,0x6654d976269d459665b5,0x53c558b176465d8d9b53,0x1565055931563c6d4f19,0x9562535854d576155994,0x854e1765559955565551,0x41854c56658559615648,0x76179d85e46175994556,0x2635395d91e35375d89d,0x5935562d558755659559,0x4ad52a954aad50e95435,0x526ad4ee953bad4d2953,0xa9636a54da9436a589a9,0x8f2953ca50f29646a551,0xad8569615a5932954ca5,0x55a59568655ad4d69535,0x9541ad5229548ad956a6,0x9e9627ad85e9617a9506,0xd51ea547a551eb537ad8,0x9ad91ea647a591e8647a,0xa9936964dad526a54,0x8107206305403c024013,0xf0ef0df0cc0b70a40900],#[0x16b15a1461311211110f,0xee1db1c91b819f18e17d,0x526d25624022a2142011,0x2ef2db2c82b82a829828,0x5f34d33e32f31c30c2ff,0x3e13ca3b73a338a37b3,0x44a43b42c41d40e3ff3f,0xcd4be4a749348347345c,0x453752650f4fb4eb4dc4,0x5a959d58a57b56c55954,0x226115fe5f05e25d15bc,0xf67f66f65e64d6406336,0x6f56e96df6c86ae6a368,0x8177175f75173971f70b,0x67e07d17c27b179e78f7,0x5e083982881e8128067f,0x211c884c11a207870610,0x68903143412210214048,0x83d6088ba049d0861518,0xa8116022c045808bd448,0xb604958c25b1848bb086,0xe01168117c047c035e03,0x1bc044f0265c218c610d,0x8e3846ba88445c02ae81,0x493c10ef0125c424bc0,0xe70129cc848726121f2,0x8bc06bc0763092c3f09,0x8c037c03a9c24b8848b4,0x5f0115022a04bc048f00,0xc234fe903a8053cf0026,0x500aa0163e412dcc23af,0x22805500ab011402aa04],#[0x4247a037a031bb088af0,0x4500aa81160247e025bc,0x2b891d7c025b38245a0,0x1de22ba447e88e9c248d,0x4c123d4c666c8c40e622,0x88216c8d6d821e047813,0x33222f119788da04d027,0x4878e1131023c2241e42,0xbfa2399111040d013c7c,0xfa233c0846b110cf5925,0xcc0d79821d22b8897508,0x81c5a14ad8897488f113,0x406e446809810]]
def g159H7 := limbs80 #[#[0x1170601000001290c00,0x2f1b1e0500010d2a0306,0x14030c00072309010500,0x70e05000a1001023214,0x1600015c0907012b8e47,0x1f0a010e167320050011,0x4b3c0547255f1a04033a,0x6cee1197cbc5c6aa112d,0xa6cca2b6d61c47cdf5b5,0xac00c1c81e19826e4a,0x1a4e6b99e18fdb0a0ea,0x34e4eebd4e69500023a9,0x7781ccc05e6505e33f,0x1e0da0f170034c4835a6,0x69413aea3fca90ea0bd7,0xe091f6e29ac295318,0xb85b84cad80a6e800200,0xba5da071399373d21b1a,0xc18cdb1850268097efc8,0x835e66ada3e68219d943,0xb1726364b62576eeb051,0x194e044b3c5b00a8e22,0x3252162471c1c71662a0,0x872ce44d41e0d1000841,0xf801507ac800190cd691,0x6258aa4832ca2cae1934,0x816268007a387f9c850e,0xe96f1b360c700023b041,0x1b3dc280019fac9b920b,0x600ac2d00036ec740b12,0xb5f000001530d8e32001,0xf00193c004600253092e],#[0x880010500011784f0a0d,0x2bb0f800000ad0000000,0x15b83218c0021800056b,0x5800c632160c8d213c00,0x45550002dc0002340135,0x845460426e60000013b8,0x312d43ce0f961000000c,0xfe539e155ef58002a4d2,0x4628f91d93967e268234,0x800000eaac4d51842236,0xa9394a0c4c81781b530,0x950ee2ce1df2b267148b,0x87124090000304000000,0x68ea948200df370341a9,0x4000898b7313888d6205,0x9a28f5d4623db5ea6a,0xe8f9f6a8279a2f0cda50,0xe0020799dd1395400379,0x68ccd1bc782fb248434c,0x3808ad7e37a3412eb411,0x340800babe70]]
def g159D8 := limbs80 #[#[0x7a8aa3a0a8398a6290ff,0x7806a729aa629c86a188,0xe53c9c13a30a79f178f8,0x1e51271020e09b06be4d,0x36035a047c0378065848,0xe020c08ee015b8057902,0x518110087c2077c6053,0x1ec]]
def g159H8 := limbs80 #[#[0xe4070e0040305060d600,0xa8c80731029308541000,0x81083618a002205a8006,0xee8868009b1bc00041a0,0x13980009107f311bead,0xcd320000882c7cc45232,0x35c00646009ea000e157,0x80093e9123e34000cc00,0xa51a6000000412e0001e,0xbf9bc27b500083aa1cd,0x65e328000009a3422fb7,0x5b0f0011700120cd9a9,0x6b20061cb0000eaddc00,0xac1d0010886400,0x639818edf78018aa422a,0x6bca9d3cabdb885c924e,0xad673c569a001e941401,0x66b091131c07cb883f99,0x47200001b90013680000,0xc31a2aeb6d44a006c304,0x801a509ecd7921d99633,0x20d02c1fac1bb5869d2a,0x1cc000b46bc08988018a,0xf94f2d90a1689a180195,0xc3a002799251d3be8db9,0x496b7801a8c584ca368c,0x1c8ae8010b4018600013]]
def g159D9 (j : Nat) := if j=0 then 0x8200ff else 0
def g159H9 := limbs80 #[#[0xe90003500db6c2005084,0x864000653400000b8011,0x18b673020300016d136,0x7725172d9395]]
def g159L : Nat → Packing
  | 4 => (6,5,5,0,0,5,0,g159D4)
  | 5 => (70,4,5,2097200,86,10,1029,g159D5)
  | 6 => (231,3,5,1900618,87,12,1056,g159D6)
  | 7 => (120,2,5,720910,68,12,1051,g159D7)
  | 8 => (14,1,5,65537,0,8,1037,g159D8)
  | 9 => (1,0,5,0,0,0,0,g159D9)
  | _ => emptyPacking
def g159I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupShort 1 17 0 5 3 0 g159H5
  | 6 => lookupShort 20 127 5 10 7 1 g159H6
  | 7 => lookupShort 72 331 8 11 8 1 g159H7
  | 8 => lookupShort 37 191 7 10 7 1 g159H8
  | 9 => lookupShort 6 37 5 7 4 1 g159H9
  | _ => fun _ => none
def g159 : Forest := ⟨159,9,fun i => g159Y[i]?.getD (0,0),g159C,g159A,g159L,g159I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g159P4_0 : block g159 4 0 6=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g159B4 : block g159 4 0 6=true := g159P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g159P5_0 : block g159 5 0 70=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g159B5 : block g159 5 0 70=true := g159P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g159P6_0 : block g159 6 0 18=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g159P6_18 : block g159 6 18 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g159P6_114 : block g159 6 114 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g159P6_210 : block g159 6 210 21=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g159B6 : block g159 6 0 231=true := (@block_merge g159 6 0 114 117 (@block_merge g159 6 0 18 96 g159P6_0 g159P6_18) (@block_merge g159 6 114 96 21 g159P6_114 g159P6_210))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g159P7_0 : block g159 7 0 9=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g159P7_9 : block g159 7 9 63=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g159P7_72 : block g159 7 72 48=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g159B7 : block g159 7 0 120=true := (@block_merge g159 7 0 9 111 g159P7_0 (@block_merge g159 7 9 63 48 g159P7_9 g159P7_72))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g159P8_0 : block g159 8 0 14=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g159B8 : block g159 8 0 14=true := g159P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g159P9_0 : block g159 9 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g159B9 : block g159 9 0 1=true := g159P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g159T : checkedTables g159 9 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g159 0 0 0 = true)
  · exact (rfl : block g159 1 0 0 = true)
  · exact (rfl : block g159 2 0 0 = true)
  · exact (rfl : block g159 3 0 0 = true)
  · exact g159B4
  · exact g159B5
  · exact g159B6
  · exact g159B7
  · exact g159B8
  · exact g159B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g159G : graphValid g159 (boundsBefore K126) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low159 : Lower true (varsX 159) (graphGoal 159) 10 := lower_forest (g:=g159) (i:=0) (hints:=1075) (before_sound K126 V126) g159G g159T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K159 := extendKnown K126 10 [(159,[]),(183,[83]),(215,[32,16,67,99,83])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V159 : Known true K159 := extend_ok (m:=159) V126 low159 (by decide +kernel)
def g175Y : Array (Bits × Bits) := #[((sampleWord (w80 [0xe03ffff800fffffe03,0xfed3aa41320000f00f0f])),(sampleWord (w80 [0x458a01506a0940a458,0xa6530a40321111111111]))),((sampleWord (w80 [0xffc07fffff001ffffc,0x34e5bc281000f00f0f0])),(sampleWord (w80 [0x891302604c0d80c891,0x334e1a42011111111111]))),((sampleWord (w80 [0x7fffffffe00000,0xd372be2500f0000000])),(sampleWord (w80 [0xe1c2b82704e0af0e1,0xc0d372be257777777777]))),((sampleWord (w80 [0x7fffffffffffff,0xf922299d6b0f000f00ff])),(sampleWord (w80 [0x10200c008010030000,0x20218d082222222222]))),(0x0,0x0),((sampleWord (w80 [0xffff80000000000000,0x98c67ad8f0000fff00])),(sampleWord (w80 [0x300300600c0102,0x80c430c04444444444]))),(0x0,0x0),(0x665142404fffff00000,(sampleWord (w80 [0x40040080100000,0x8888888888]))),(0x0,0x0)]
def g175C : List ColumnInfo := [(1,0,174,0,8)]
def g175A : List (List Nat) := [[],[83],[16],[16,83]]
def g175D8 (j : Nat) := if j=0 then 0x7f else 0
def g175L : Nat → Packing
  | 8 => (1,0,1,0,0,0,0,g175D8)
  | _ => emptyPacking
def g175I (_ _ : Nat) : Option (Nat × Nat) := none
def g175 : Forest := ⟨175,8,fun i => g175Y[i]?.getD (0,0),g175C,g175A,g175L,g175I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g175P8_0 : block g175 8 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g175B8 : block g175 8 0 1=true := g175P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g175T : checkedTables g175 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g175 0 0 0 = true)
  · exact (rfl : block g175 1 0 0 = true)
  · exact (rfl : block g175 2 0 0 = true)
  · exact (rfl : block g175 3 0 0 = true)
  · exact (rfl : block g175 4 0 0 = true)
  · exact (rfl : block g175 5 0 0 = true)
  · exact (rfl : block g175 6 0 0 = true)
  · exact (rfl : block g175 7 0 0 = true)
  · exact g175B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g175G : graphValid g175 (boundsBefore K159) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low175 : Lower true (varsX 175) (graphGoal 175) 9 := lower_forest (g:=g175) (i:=0) (hints:=1843) (before_sound K159 V159) g175G g175T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K175 := extendKnown K159 9 [(175,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V175 : Known true K175 := extend_ok (m:=175) V159 low175 (by decide +kernel)
def g187Y : Array (Bits × Bits) := #[((sampleWord (w80 [0xfffc01ffffffff0ffa,0x8a08b0800007c00ffc1f])),(sampleWord (w80 [0x28140500800220ca,0x2003084210842108421]))),((sampleWord (w80 [0x1ffffe007fc3fff05d,0x22c7098000f801f003e0])),(sampleWord (w80 [0x413018260108240259,0x207098c6318c6318c63]))),(0x0,0x0),((sampleWord (w80 [0x1fffffff8003ffff20,0xf2615e001f003e0003ff])),(sampleWord (w80 [0x824020080a10480020,0xe0604210842108421084]))),((sampleWord (w80 [0x1ffffffffffc000010,0xad8c6f83e00000007c00])),(sampleWord (w80 [0xb8140b02c01704410,0xad8c4f39ce739ce739ce]))),((sampleWord (w80 [0xe0000000000000000e,0x11ba877c00003fff8000])),(sampleWord (w80 [0xc0180c03021808804,0x11988421084210842108]))),(0x0,0x0),((sampleWord (w80 [0xc1,0x4514407fffffc0000000])),(sampleWord (w80 [0x100201004002000000,0x42108421084210]))),(0x0,0x0)]
def g187C : List ColumnInfo := [(1,0,186,0,8),(2,0,185,0,8),(16,0,171,0,8),(8,0,179,0,7),(32,0,155,0,7),(128,0,59,0,7),(0,16,42,129,6),(24,0,163,0,5),(40,0,147,0,5),(128,16,42,1,5),(136,0,51,0,4),(160,0,27,0,4)]
def g187A : List (List Nat) := [[],[83]]
def g187D5 (j : Nat) := if j=0 then 0x2f1e057454932 else 0
def g187D6 := limbs80 #[#[0xb67b22a49974d5454932,0x29eee2b2a85cb5515250,0x4b7bb8acaa17cd745493,0x471eda9652017ddc5645,0x2d03f011a0ae22780b61,0x2c98f970104f1e0204e,0x41622]]
def g187H6 (j : Nat) := if j=0 then 0x3 else 0
def g187D7 := limbs80 #[#[0xfefdfcf7efedd5250932,0x55262a80d900b20d523f,0x226019648ec925522b2b,0x2a158e11cfcd0ae84684,0xf403222aa387a1791119,0x19f500c202de0241810,0x175248e00af28040e]]
def g187H7 := limbs80 #[#[0x60400000000001,0x1000003000000000010,0x896d400]]
def g187D8 := limbs80 #[#[0x8a4b807f54bfa85dd32,0x1ca3946081847356838c,0x2a851ca30]]
def g187H8 := limbs80 #[#[0xe4000001280431b18409,0x11c0000002174004]]
def g187D9 (j : Nat) := if j=0 then 0x5431201bf else 0
def g187H9 (j : Nat) := if j=0 then 0x17018001d9 else 0
def g187L : Nat → Packing
  | 5 => (1,4,4,0,0,0,0,g187D5)
  | 6 => (7,3,4,0,0,8,0,g187D6)
  | 7 => (9,2,4,458755,50,8,1039,g187D7)
  | 8 => (3,1,4,0,0,7,0,g187D8)
  | 9 => (1,0,4,0,0,0,0,g187D9)
  | _ => emptyPacking
def g187I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupShort 1 2 0 2 0 0 g187H6
  | 7 => lookupShort 2 31 1 6 3 1 g187H7
  | 8 => lookupShort 2 19 4 7 4 1 g187H8
  | 9 => lookupShort 1 11 0 5 2 1 g187H9
  | _ => fun _ => none
def g187 : Forest := ⟨187,9,fun i => g187Y[i]?.getD (0,0),g187C,g187A,g187L,g187I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187P5_0 : block g187 5 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g187B5 : block g187 5 0 1=true := g187P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187P6_0 : block g187 6 0 4=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187P6_4 : block g187 6 4 3=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g187B6 : block g187 6 0 7=true := (@block_merge g187 6 0 4 3 g187P6_0 g187P6_4)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187P7_0 : block g187 7 0 3=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187P7_3 : block g187 7 3 5=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187P7_8 : block g187 7 8 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g187B7 : block g187 7 0 9=true := (@block_merge g187 7 0 3 6 g187P7_0 (@block_merge g187 7 3 5 1 g187P7_3 g187P7_8))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187P8_0 : block g187 8 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187P8_1 : block g187 8 1 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g187B8 : block g187 8 0 3=true := (@block_merge g187 8 0 1 2 g187P8_0 g187P8_1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187P9_0 : block g187 9 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g187B9 : block g187 9 0 1=true := g187P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187T : checkedTables g187 9 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g187 0 0 0 = true)
  · exact (rfl : block g187 1 0 0 = true)
  · exact (rfl : block g187 2 0 0 = true)
  · exact (rfl : block g187 3 0 0 = true)
  · exact (rfl : block g187 4 0 0 = true)
  · exact g187B5
  · exact g187B6
  · exact g187B7
  · exact g187B8
  · exact g187B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187G : graphValid g187 (boundsBefore K175) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low187 : Lower true (varsX 187) (graphGoal 187) 10 := lower_forest (g:=g187) (i:=0) (hints:=51) (before_sound K175 V175) g187G g187T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K187 := extendKnown K175 10 [(187,[]),(237,[96,16,33,66]),(249,[97,33])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V187 : Known true K187 := extend_ok (m:=187) V175 low187 (by decide +kernel)
def g189Y : Array (Bits × Bits) := #[((sampleWord (w80 [0xe007ffffe1ffff91e0,0x9c1ae000000fc0fc0fff])),(sampleWord (w80 [0x40500a0044001010c0,0x8c006041041041041041]))),(0x0,0x0),((sampleWord (w80 [0xfff800fffe1ff8310f,0x7c85500003f00003f000])),(sampleWord (w80 [0x84612c228044213107,0x7c0542cb2cb2cb2cb2cb]))),((sampleWord (w80 [0xffffff00001fffda3d,0x31312000fc003f00003f])),(sampleWord (w80 [0x80300b0881400a3d,0x11110186186186186186]))),((sampleWord (w80 [0xffffffffffe000462a,0x8b87903f00000003ffc0])),(sampleWord (w80 [0x902404c0009824628,0x3829514514514514514]))),((sampleWord (w80 [0x4984,0x67ec8fc000003ffc0000])),(sampleWord (w80 [0xe038070110e044100,0x62ec8618618618618618]))),(0x0,0x0),((sampleWord (w80 [0x2651,0x42404fffffffc0000000])),(sampleWord (w80 [0x100400800010000000,0x820820820820820]))),(0x0,0x0)]
def g189C : List ColumnInfo := [(1,0,188,0,8),(4,0,185,0,8),(16,0,173,0,8),(8,0,181,0,7),(32,0,157,0,7),(128,0,61,0,7),(40,0,149,0,5),(136,0,53,0,4),(160,0,29,0,4)]
def g189A : List (List Nat) := [[],[83]]
def g189D6 := limbs80 #[#[0xe5c5243e0372d5454942,0x5]]
def g189D7 := limbs80 #[#[0xf55152bf59542fb54942,0x42a00ff59152bfd9152d,0xc70187cb1570186ae8a5,0x481c5cb15308c82071b2,0x81c60d4c72c071]]
def g189H7 (j : Nat) := if j=0 then 0x1 else 0
def g189D8 := limbs80 #[#[0xa3946061a403faa5fd42,0x1e851ca301c]]
def g189H8 := limbs80 #[#[0x872034000000000000,0x8c0e]]
def g189D9 (j : Nat) := if j=0 then 0x5432101bf else 0
def g189H9 (j : Nat) := if j=0 then 0x4000d000003 else 0
def g189L : Nat → Packing
  | 6 => (1,3,4,0,0,0,0,g189D6)
  | 7 => (5,2,4,0,0,8,0,g189D7)
  | 8 => (2,1,4,0,0,6,0,g189D8)
  | 9 => (1,0,4,0,0,0,0,g189D9)
  | _ => emptyPacking
def g189I : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupShort 1 2 0 2 0 0 g189H7
  | 8 => lookupShort 1 17 0 6 3 1 g189H8
  | 9 => lookupShort 1 11 0 4 1 1 g189H9
  | _ => fun _ => none
def g189 : Forest := ⟨189,9,fun i => g189Y[i]?.getD (0,0),g189C,g189A,g189L,g189I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g189P6_0 : block g189 6 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g189B6 : block g189 6 0 1=true := g189P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g189P7_0 : block g189 7 0 4=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g189P7_4 : block g189 7 4 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g189B7 : block g189 7 0 5=true := (@block_merge g189 7 0 4 1 g189P7_0 g189P7_4)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g189P8_0 : block g189 8 0 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g189B8 : block g189 8 0 2=true := g189P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g189P9_0 : block g189 9 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g189B9 : block g189 9 0 1=true := g189P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g189T : checkedTables g189 9 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g189 0 0 0 = true)
  · exact (rfl : block g189 1 0 0 = true)
  · exact (rfl : block g189 2 0 0 = true)
  · exact (rfl : block g189 3 0 0 = true)
  · exact (rfl : block g189 4 0 0 = true)
  · exact (rfl : block g189 5 0 0 = true)
  · exact g189B6
  · exact g189B7
  · exact g189B8
  · exact g189B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g189G : graphValid g189 (boundsBefore K187) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low189 : Lower true (varsX 189) (graphGoal 189) 10 := lower_forest (g:=g189) (i:=0) (hints:=1027) (before_sound K187 V187) g189G g189T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K189 := extendKnown K187 10 [(189,[]),(219,[48,33,65,16,101]),(222,[96,16,66,49,83]),(243,[80,33,65,49,48,99]),(246,[96,16,66,49]),(252,[96,16,66])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V189 : Known true K189 := extend_ok (m:=189) V187 low189 (by decide +kernel)
def g190Y : Array (Bits × Bits) := #[(0x0,0x0),((sampleWord (w80 [0x1fffff87fff2310000,0x7e03f80fe988a467cfe])),(sampleWord (w80 [0x402801102212012845,0x18a142850a08a2024874]))),((sampleWord (w80 [0xe003ffffff00c80000,0xf800007f002013999b3c])),(sampleWord (w80 [0x84b08a010420c01ad3,0x4a64c99326221289991c]))),((sampleWord (w80 [0xfffc0007ffe923003f,0x1fc000fec11c21e3cf])),(sampleWord (w80 [0xc02c20480920518a,0x2142850a140110808389]))),((sampleWord (w80 [0xfffffff800048807c0,0x7f0101e03e03f1])),(sampleWord (w80 [0x9013002704408e52c,0xb58b162c5901a03602e1]))),((sampleWord (w80 [0xa16f800,0x1fff8001fe003ffc01])),(sampleWord (w80 [0xe01c0438080168630,0xc60c18306122003d1000]))),(0x0,0x0),((sampleWord (w80 [0x1544ffff,0xffe0000001ffffc00000])),(sampleWord (w80 [0x100200040000000000,0x10204080d44d400000]))),(0x0,0x0)]
def g190C : List ColumnInfo := [(2,0,188,0,8),(4,0,186,0,8),(8,0,182,0,8),(16,0,174,0,8),(32,0,158,0,8),(20,0,170,0,7),(0,4,42,144,6),(0,16,42,132,6),(128,0,62,0,6),(6,0,184,0,5),(10,0,180,0,5),(12,0,178,0,5),(16,4,42,128,5),(34,0,156,0,5),(36,0,154,0,5),(40,0,150,0,5),(128,4,42,16,5),(128,16,42,4,5),(42,0,148,0,4),(132,0,42,0,4),(132,16,42,0,4)]
def g190A : List (List Nat) := [[],[83],[66],[66,83],[49],[49,81],[49,66],[49,66,81],[81,49],[81],[81,66,49],[81,66]]
def g190D5 := limbs80 #[#[0x19770509106117219510,0x997705091054b7050910,0x5954250120d915254110,0x55152501205095150120,0x50b51501205d55250120,0x55152541205495154120,0xd915254120d515254120,0xd515454120dd15254120,0x54971541202156154120,0x553725412060b5454120,0x61b5154520dd37254120,0x1d565585205977354520,0xe0171595201d17159520,0x6077459520e0d7159520,0xe0176d4520e037459520,0xe0d71d512061f65d4520,0xdcd6258550dd37054950,0x9d2b61f42f5d152d4150,0x72acd55aa754da93d0f9,0xb656aad1d9ab2762ec4f,0x6484f15d2b9571adc5b4,0x4c13b240d95409fc2089,0xc63f20005980c2cc0266,0x8bf2c3d797160c3133e0,0x1b2884b832a9cb116e50,0xf2c5db742eeb2172e0d1,0x2e6df7435dc21d7d90c4,0x47b98452dba271e10e4d,0xf1794585ca2b7d912532,0x2f647c8ca2ec211d0728,0xf746963a34c1d197704e,0x9288bc9b70e09c0530c2],#[0x1ac240be1216f09123,0x25900703014080301004,0xa04c23d0e7e3a1a8c456,0xe8e870361a0c85e2d150,0x26733194c863311823f1,0xce471381bcda6c359a8d,0x3542c032401282d0a80c,0x264590c2303a30,0x321a42808000000000,0x2c84000002000140501,0x4000350400000002504,0x179100000000000d,0xda10000]]
set_option maxRecDepth 32000 in
def g190D6 := limbs80 #[#[0x50910195424417219510,0x44175509105954244152,0x50950443705091099542,0x541105c9504415254110,0x44362545105095144362,0xd91524427654910dc951,0xd89105ca654437259510,0x48142501205d76244174,0x59540481525012054540,0x54120545504835150120,0x48161541205515048152,0x9955048174541205c550,0x54120d51504835154120,0x4837254120dc55048364,0x5d9514816554520dd150,0x54520d91514835154520,0x4837654520dd15148373,0x5d954481705512059554,0x55120dc5544835455120,0x48165585201d56148376,0x5d16548171595201d165,0x59520dc5654837059520,0x48171995205c26548374,0x5c35148165d452059351,0xd45205db5148174d4520,0x48365d4520d935148276,0x5c35448165d5120ddb51,0xd51205db5448171d5120,0x54152545505d76448364,0xd91525416454950d8951,0x58550549615437054950,0x5407458950d896154162],#[0x54b505437458950dc162,0xd41505cb5054162d4150,0x54362d45505cb5154362,0xd935254174d495059352,0xd85505cb6154162d8550,0x54764d89505c76254362,0x59162d4172d81515c351,0x5835158960d457458b50,0x9be3f8fa2fdc960d4572,0xaf6bbadeafa7e7e9f677,0xbf2fabdaeeb7adbb6abe,0xd3f3ecf73bcdf2fcbb1f,0xe3b7adbb6bd7b5bd6b57,0xf2bbaebbaae7b9be6b8f,0x550b50b294fabdaf3bcb,0xd4bb21a956434eaea5ab,0xc2418f64426b0485ddd0,0x7b9520ea8e8e01e01781,0x84113ec822edc841ec28,0x2650e28c61054e43083f,0x8319dd0627c00b43841,0x9a194344a90615841a5b,0x80d8aa0219850cd4ca1,0x93c1830987024b0604a6,0x409870a5304142e1c1,0x9871eb6e83ca60878dc,0x426170a487614705438f,0xc708018610005c2000b8,0x656f508a85c211098420,0xc618c24c118bd42308f0,0xcb44ba96bd842d7aa858,0x5c397a7842f57045e2e1],#[0x20b952408f0666e548cb,0xf8538790a72e548e24c1,0x468f06752e08edca91d3,0x2c86aed50d5caa1ab952,0x6ae994d45ba1aab64355,0xd5125caa24bb743572e8,0xda4c2248b744912e892e,0xc11b3386370ee86edd50,0x14982433f0c6eddd0ddc,0x87454ee88ae6090d3b22,0x93047e2e092a5c11e32,0xc8a97591516c3284d805,0xd6dd14afb2aa5d6554be,0xd38dc02723844c130ca,0xc4b93f1980581f089c4e,0x23f6b647ed2c8fe2e09f,0xb8680130f0c261de8dc,0x482130f102e1df11c23e,0xd701043e1208dc041238,0xf082e120adc241588482,0x41d5a11c23419808a130,0x9706c233118366a6ead1,0xc0300986623300c625c,0x2d23845a430cc2459582,0xb805e6700be4e116cfc0,0x8f4ec91e25ca3b4c0326,0x30b296d92409c1c88b82,0x264e1234fc0462187944,0xdc9c2dc24b5b8492d701,0xd43c03a5b76750ee8e22,0xba38a4747156e4e16e19,0x627836c6700d8c611c53],#[0x74724708d96dd1b2c3a3,0x46700dc8a1daadba3958,0xe4ed6e05d2cc0baa7807,0xdf5d2bddb15713837912,0x12cc4b95a4384b07f095,0xb0b95c5f739ae6e7306e,0x9d27373a2f6e5446e02d,0x2384c0bee74c8e1292fb,0x4a156c5402e130b0b962,0xb6e93c661283faa507d5,0x941f5d285dc150bb62a0,0xbdd279dc14e3d84a0fee,0xae8dc05e5974bf37053d,0xfc05e9174bedae97cee0,0x548774ab08e955fe02f1,0x783c65305921e02b41b9,0xca170998ce03415c1672,0x309ac8e13519c0691782,0xe0e20ac06a0420280001,0x1dc1c01aa19a17214c10,0x7826825823a22a20c1ee,0x23062f62e62cc2bc2962,0x3d03ac38a36c34233232,0x7a45e44a4304204083ec,0x65004ea4da4ca4b84964,0x5e85ae58655c54c53652,0xae68c67065863e6165fe,0xe79676a7467286f26d66,0x8a087c86083c8067ea7c,0x8e96693e9189008e88c2,0xaa4aa2ea169f09da9c89,0xb10ae4ad0abcaa2a84a6],#[0xd4bb2b9ab72b62b4ab36,0x2c56c46c28c18c08beeb,0xd00ceecd4cbaca8c8ec7,0xaed9ed8ed72d62d46d2e,0xce42e30e14df4de4dc8d,0xed0ebeea6e96e7ee6ee5,0x82f6af44f26f0cef0ee0,0xf021004ff2fdafc2f9cf,0xe90d10b708706904f03,0x9917d16314913911f10f,0xb2211fb1eb1d11b91a91,0x2c52b52a328d26d25323,0x8536b34d33d32d3092e1,0xb43b4234093ed3dd3b33,0x4c54b549b48b47345b44,0x6d55d54352950f4f14d7,0xd5dd5cd5af59f58f57d5,0x67d66d65d64162560b5e,0xd6f96e96d16bf6af695,0xb79d77f76574973571d7,0x8438258158057f37e37c,0x814e40682001865855,0xd9215404004b818002,0x634168a8da4a101881a3,0x8d00b0e87848a0790813,0x11498463b08278260041,0x588b0dc1f184648a2323,0x683df0c5c371b841d020,0x77e3222aafa09186f10d,0x8ba316d579c455c790d,0xc0838100c6c3484001d6,0xd343f70200002e04005],#[0x1e0800003610000eb080,0xb0d6c318315798839100,0x22d84b614072c2012835,0x100cecc5484000002b84,0x6d544666f621b9a18052,0x5642b415d443941603b,0xc5cd11b616f862cc3136,0x9a364eac18d734237023,0x9d314c0df4486061816e,0xa055c98a7a84b9a16302,0x459c44337d826ecc4a04,0x2b2102ec4c04023ae12,0x280cd04dc0c5866909b,0x8803505012e8c507d21a,0x1d61eb0e798ac853d1,0x403d612d84b610097020,0xb61b21c31e86011a08d0,0x1006b023410000c60400,0x94100008d0403ac0eca,0xe221a096c20000019410,0x6504b9316586c8421b11,0x702b41008702db080650,0xe6105643b412e52632,0x20000db0ad0568200b41,0x84c85683dd588022c264,0xbb05db080006908f2145,0xab1d5849c08000778c58,0x35046821b080015e0b35,0x100806d0403507504000,0x80007586ac3b41470396,0xd06dc080004b81000000,0xda0ea0800006c21b0e],#[0x6c280d90802020164201,0x400c8735ab1db81da0d,0x6ed080000]]
def g190H6 := limbs80 #[#[0x21200510002000a1250,0x8280008090000000,0x44b00000091600055b00,0x4ba4a000000d0b04c406,0x51200000000024d9,0x42300012000011c00,0x0,0xf00000020d0000000000,0x82b000c18000d0d90a40,0x2ac0281c000000805800,0x819c,0xc1382400,0x85a00081f,0xd52a000012c1d0000000,0xc0100000095200014,0x15000000827000000d4c,0x149000000000808c,0x22d000a0252d20a00b00,0xc0ec40000000010c21,0x80c0030110000000000,0xd000c2d00000,0x2bc14000000000000000,0x407000d,0x843c04d1b00000000,0x2990f000000000,0xc0a0,0x51842c81600000000,0x51704946ad5901e425,0x41742282641b0,0x5300000,0x60641a00000044d,0x4200000000],#[0xe8200000000052400,0x506000000000]]
set_option maxRecDepth 32000 in
def g190D7 := limbs80 #[#[0x54110509104851019510,0x59510589105491054510,0x5012019520d891099510,0x58520551205452054120,0xd5120d45209952059520,0x5495054550d9120d8520,0xd4550d41505895058550,0xd4551d8950d8550d4950,0xd4b5058b5058750d8151,0xbebf3f9ecee6f2f58351,0xfefb7bafcfdfefd7dbbd,0xdfdfebefeff577fbddad,0x61dcc70ae60097203fdf,0x35c4a0ae6a4152326a11,0x54830ee708374400ba14,0xc846ec42376405db1071,0x4922e849374193b8048d,0xb22e4413721c8b90045d,0xb6e46595231cb2976548,0x6c863964323aa191550c,0xec9257048fb99a9dd0c7,0xc71176397329cb594e22,0x9ad654d9b22695c1326e,0x1b74413b82045d5522ec,0x374419ba20c1d1076e08,0x52688ba2245d914ae089,0x274fb9b07dcd64ae4d45,0x717b22f1dc174ee0b917,0xc8ba3c6dd192ae8e2f64,0xb83e45ca026e912d648,0xb90795c83ca841937291,0x284f1942baa416142133],#[0xaa5d427eca13e6509eb,0xaf1d8556e82bf64164aa,0x9544ccea25e5512df3b0,0xdc4ccae266561333a899,0xd0ccae866754332aa199,0xcdc2c26e35137332999d,0xd56e86bf6435eb21b5dc,0x56ec6a97635fb29af594,0x2e893f6449eb22595c12,0xec93d7649fb2a4f59525,0xa7bd653d5bb24f9d9252,0x72b713b2b81cadd4f50e,0xbf7639ebb1cf594ea6a8,0xd764deb2a6a5c53cae09,0x65429ba20adc50cee083,0x441eba20fdc507ae283e,0x6b2b134a5c51cae08bf7,0xe4a936fd89692a4b6762,0xeb1312549852e4dbf626,0xb13b2549d56e4c3f6261,0xa2f9dc1752e4ebf6275e,0x2f259177ec8bcb545e4a,0x92591c52e8e3f64725b2,0x7d899cee0cc974725b23,0xdd19a0e8cbf6465eb233,0xd1e7ec8f6770795ba334,0x1e7ae8f3f7179eb8bca5,0x27ae912b7489eb244fdd,0x7ae522b7291eb148fdd2,0xf005c01e8060000fdca4,0x8e83f81be0cb05782680,0x3641990c085a429a1370],#[0x12388b442c1fd0f10728,0x45922ad14d0a244d0254,0x71c00d8068831c1830b9,0xac83c40a1f38f1875439,0xc925512588f246922610,0x5a8aaa54029014309d04,0x62330717b4b945a52c01,0x9ae8d4a6843329938c7c,0x67703a99ccce266f536d,0xaa0910127e83e01eacf1,0x4e89b443a1c50ac84441,0xa4a4bd2328fa47023011,0x37e9b44cea6212e495b4,0x52ea905454a154fca771,0x55b4ac95572a91510a75,0xa5a6ace9648b175822bb,0x39784bb55ccadd56c6b5,0x4f6173071804bf55f1af,0x2ed94cc9163db1b98b8c,0xd2a687b4119eace866b3,0xb699b14d7a6b23529a78,0xae42717b869bfade36e2,0xd3afdd4ee8e73e39a9ca,0x84f34793bc5de0eef076,0xd23e4def2f697af3d41e,0x350037f6bf69f90fb87,0x83b419a0ad04281bc0b2,0xa6406c086242d213b084,0x4406212a109a2c208100,0x213a4e48ac5a38007112,0x3e3e10b440301460d612,0x542e22382c10414000f6],#[0xa472f8427a5c4850c02e,0x18660268845214381a04,0x8a1c70580668fcc24204,0xfd651460e0e9641f19e0,0x2dea1267840321f50902,0x7990c83e33c1177c7c82,0x75ed0c64ded0c9330a20,0x494f9a0943ea2c605e4c,0xd0923d984b3d78512f22,0x5279e6439a0a7954c95f,0x77a24d6cc8c7c841fb5e,0xd110bc6408ca5fb14c96,0x56fa0a64da5fd628478b,0x916d991cf20449cff204,0xe1514331767940a06c46,0x262ecf30144d05dea0bb,0x990c6c7508aa6845ddfa,0x281b1f208c363e41197,0x52f9d3027ab3242fe790,0x8b04789cc909ca497a82,0xfea011b74798e08e96ff,0x2822464c91249f1ccb35,0x1bd8a08cfd8819c8127e,0xef100a0e684857dcc028,0x5532e43ec4c81847b197,0x4dcfa222b77a34329796,0x707d414f0325236d7a34,0x48811a7a265cacb682a6,0xa19138623c446f035e35,0x7b199097c314784c79e1,0xd16b1b3644d4236654d1,0x8c535d4a2570cc7075b8],#[0x4b3f4439e150ef2092b7,0x8c6045efe8032521bc82,0xa3b6910774865c600c83,0x64dd487bdd48933d008,0x890bc46bf82910022c31,0xae435a0b65625fc0876e,0x408efc020056837c08f7,0xd00e6823e3608ab1e31,0x233f91096682bf212e21,0x57e429a094b8c0196cb,0x222f810d470873e021cd,0x25216409341cc9886be1,0x4e3a190361b848fb9803,0x15153a80592550a3d263,0xc97739128ea3c28b3d71,0xdd1889991ce0d0d3c7a4,0xeb2110eb238cc8d7d486,0x55e310e7e282217c031e,0xd3039a0a9823981d3892,0x47580c8ba85486d224c0,0x8d3162720455d43dea1,0x1cc98839931af188767,0x6c0971096812e309180b,0xbe221c424edac72f1d83]]
set_option maxRecDepth 32000 in
def g190H7 := limbs80 #[#[0x600c8d06040000400080,0xa400b00001860,0x4180214182040c78514,0x60102546080400104100,0x9b065400e4264005264d,0xc023c18a00240052a280,0xe83400002344830810b8,0x6029003a540071800481,0xd988d2010c0400009093,0x25a1be5c28710301040a,0x90000a2d6050000210f0,0xc012c68ea6821a887945,0x92000000000000001874,0x7c000000183c08760006,0x1abbe0018b20001a00c2,0x1760ec0e60813871800,0xe18000156205e0000000,0x38000063800004300010,0xa09b04c027805d626983,0x614690076a6a806b832,0x8031e082000693da54e,0x80002a6a8e30001a2e20,0x867804f8ba447e885eb1,0x3c13a0001324861616a,0x49a3887248fc0600012,0x44802c2024892c00,0x1a0810000083fa0e4837,0x4c8e05f80240006,0x92cb819a135c15c00000,0x160000000089d06523a,0x21c3c400061180005048,0xc088881e606ea9ca914a],#[0xa132000087d162e9a146,0xae85b61a4062800183c,0x6001080000000000d062,0xa206d13806ac0b4070c1,0x82280010290000000023,0xd8044034a27209d21b6,0x20001816a1ac82ee13c4,0xb1304fcb15005e9a494,0x84000101382e2ab4000,0x2f84480f605541b40000,0x9047800000060d9909f0,0xa318001015299522000e,0x8b7b068000000222b,0xe4072071216451260220,0x2052000481e23960db03,0x43686753960000000000,0xcf829817c21d00002465,0x6aca8001c65800000003,0x3a0c3259000186b89a,0x65846621c4aaf838607b,0x26b1c000000000041baa,0xc11400040b2028000187,0x8f882c21bc00020f4055,0xcd04e533c000287284a0,0x884041d0000416800060,0xa4e2181873607407031b,0x66a0868a9409dc0d201c,0x93198000415884ae03ea,0xe1b9251211000000e3a1,0x1440310295a5401278b3,0x5101f812e405807ca316,0x6839ea70a23c2b425201],#[0x82b002825c61cab07a96,0x2a68040002197823a0ef,0x3689f040856181c29260,0x40d0000618905e20470a,0x230a1a4aab8195028000,0x9e80442a622c40c9881a,0xb28062700dfa972aac60,0x403a00f211,0x21b08050001009a116,0x7d416893e3b2156d0e40,0x410584208148df000083,0x17a82521ce0636899a03,0x1058c0050128000851e,0x105c8056963e47a00000,0x2600192812ab325d000,0xda90600000000003038,0x922013600061228,0xe1a829e603313c206200,0x2c6824215e0004152a1b,0x100c000095a80000002,0x1081006c000616f82200,0x85208e722ac1678eb000,0x4d0000120a2c0835480a,0x2c2af0ae802e806c0bd0,0xc2a00000000000000180,0x8200000000000780a,0xb2000211dd0e00000000,0x150d000114ca1,0x8640000c49800,0x2a400000004372,0x69838916a6f83031ba0,0x1402cc0183a2e800000],#[0x143a66655e019e003cca,0x1e000103001a01878534,0x3a5500000a880fd23660,0x105d8000000419,0xb1a00002900000000,0xe2c88aab220082d8ad40,0x3410a07568de00,0x569028a928000002c000,0x4a00040fa27400000ad8,0x1012000000021,0x8e2000000d0000892800,0xc48fc918800000023c9,0x3c15a000619983580015,0x88ae000086c0496b1785,0x2340bf25380008e5,0x600000002e580000000,0xa0000000000412d869a1,0x85c620c813000000040a,0x60eb868a924,0x6884008000109ae1200]]
def g190D8 := limbs80 #[#[0xfbfb7d47505455048110,0x908aa801b1bfffefdf7d,0xb2823283b102b108a888,0xb09aa81aa013b2833282,0x3292b2923293b212b213,0xa924a923b0aba823b293,0xb032b145a942b0c3b125,0xa90ca102b057b1b9a8b3,0xaa1caa1cb09da89ca89c,0xb0ada8aca8ad329cb29d,0xb12cb12da92ca92db0ac,0xaa0f011000cb05cb14d,0x23c46d8ca17426c42871,0xdcd11892cc5349b92421,0x2e23e44e838fe1e63986,0xb025d8b45592954f89a9,0x17acef1cc3746a8ce58e,0x6124a3cc5c88d0ae083f,0x292228b16421026dccd9,0x1448284874b08206ca22,0x146801820b82080c7862,0x25b879f089c59302321a,0x2dff80128fc0110ff42,0x70053f92904f73112bb6,0x4b134ea4a25e844a7205,0x82a0793508e4a7388ef2,0x87dc0550fd04596e4ce2,0xa811ff0053fe089684e4,0xfb9c82673d40cfdc8077,0xe30932e71111c8063010,0x189778c222cc5e44462f,0x6e13865ff0455c9027b9],#[0x42ef9940a77a91011a09,0xe50262f6b0982ef9940a,0xe00f516d0a2f2cf81317,0xe40307f2009dff0056bf,0x40287f2009ccffc8097f,0xde3088a]]
set_option maxRecDepth 32000 in
def g190H8 := limbs80 #[#[0xa0a0048c49080000010,0x60d0588406000580c06,0xac020b03004040a03004,0x106816090001d0802000,0x404040303412010,0x607020700400028c8001,0xc1c0f000781800018301,0x840ca071b83014010005,0x220208014060b02,0x61008545451048446c0e,0xc2009e01c00040300830,0x7fc511523611402fc6dc,0xf4134098863a120c1ed0,0x36920003443c09403,0x3039c51c002c9be47d,0x1a01f4104000224457a0,0xb06c0001434000257802,0x106d010c542294811,0x414626e00030728188,0xbc035192ca5c04382880,0x1210000836000200,0x14d298450000090b500c,0x1417017c25714960ab4,0xc04e82d708f000000000,0x81c824d2064565254c98,0x3455e4000845818b829c,0x384341a0000c6530,0x101d045d49f522400,0xc2bc292401c11a,0x7f20a0000000413157e0,0x257d0000000826c000c6,0x69440006924517002],#[0x8c0000073000215b41bc,0x100022470abe80f8a3a0,0x1096459b440c57a08,0xe8061c9a006d42e8063,0x2054515409d813f1a2c,0xe529001849e42e200e01,0x58843b0b480ec84ec21,0xadc2c402e0120023426b,0xb44f0000c11400080550,0x40f501b42aa2b0851902,0x178000c0a926b958100a,0xba41a4228000e0f54574,0xb255895841c096308502,0x5cc58013500dc0acc15,0x6ac1c210c046c273c23b,0x84d30a1011e80e81494,0x864f06e1033416855f1a,0x4e01131a58022c140431,0x86024c2c845b80f10208,0x219cc047075503925a62,0x4b857016a0005004c99,0xbac9fb0b940511b8005f,0xc06057c00d60a600e11,0x19081ea078000029,0xcc0004a14000ca3403e,0x3076d0e4019a93e1b98,0xc05d016717a028000000,0x18f40240050000094a12,0x2d0000000000151f06a2,0x425c099056ba4c805b0,0x847c000000006401f217,0x2cc10a00005808660000],#[0x452149827e026c,0x18a4404a1628108a4500,0x49650d92670001562000,0x55df07100000008223,0x981f745f000112200000,0x8d000000000000a,0x12000081f8196c20c09c,0x300015b526c0a4e849e,0x316e468c51a81ae08900,0x11500035651075128000,0x91442f492421210d0001,0x40c0055000e0,0x4a3e29695ee85141dc00,0xa0a07980b2516a92c000,0x956c00084004910,0x717f02dc000000019500,0x811048151dc00041a,0xf8180000ca2819e828c,0x2427b0360002a4e404ca,0x84ed095806a454c99908,0x576458c918000007000f,0x5e0490001029000204a0,0x40a000243bc22c18c46,0x90896628682a160a000,0x7450eb49a42010570001,0xe915b18d00030a400840,0x306a80a1191067401,0xd0ae067908211e,0x9d84c0000032424b0a50,0x6199016d522917315680,0x426d49849d02d914240c,0x74c168066e13d2788195],#[0x2c12]]
def g190D9 := limbs80 #[#[0xd51ffa87f543fa41fd10,0x51b0259b138a803fea3f,0x410202548526489000,0x101464648a50101a48a5,0x248a02051549228]]
def g190H9 := limbs80 #[#[0xe0838204040052028400,0x206be022411a2610a8e4,0x8008107021292000a0a,0xe80480b09400048c000e,0x82f42d0008150000a111,0xc05c18429c2e000c1f,0xb445c6d0424a2d20020c,0x129d62000e2daa006084,0x80fc81030807401,0xc000c0341b02286c8140,0x86fc8782680e831000c1,0x1b06181900000000041e,0x41662800085180cc5a9,0x8ab825503006a2000,0x2d00040a000565000000,0x6000c500624280000009,0x1dc56c13d0a4a3c88e1,0x1bc8416460702702a059,0x3c170a88704aad6102be,0x42cd0801012810b844c2,0x2485561f80d203e3169f,0x2000a1e0004091a00004,0x2290000004124a900,0x46e000531000000811,0xc5789891600001a0]]
def g190D10 (j : Nat) := if j=0 then 0x2080513f else 0
def g190H10 := limbs80 #[#[0x8,0xd1000000,0x80000000000143e00000,0x240000000120000000,0x3840000,0x8400250000000002a000,0x1400000000001,0x54e0d,0x21281000,0x8a80046000,0xc0000000000000]]
def g190L : Nat → Packing
  | 5 => (46,5,5,1572899,86,9,1037,g190D5)
  | 6 => (235,4,5,3145836,103,12,1080,g190D6)
  | 7 => (187,3,5,1703973,86,13,1089,g190D7)
  | 8 => (50,2,5,458758,51,11,1060,g190D8)
  | 9 => (6,1,5,0,0,8,0,g190D9)
  | 10 => (1,0,5,0,0,0,0,g190D10)
  | _ => emptyPacking
def g190I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupShort 21 223 4 12 6 4 g190H6
  | 7 => lookupShort 111 607 7 14 8 4 g190H7
  | 8 => lookupShort 98 487 9 14 8 4 g190H8
  | 9 => lookupShort 28 149 7 12 6 4 g190H9
  | 10 => lookupShort 4 97 1 9 3 4 g190H10
  | _ => fun _ => none
def g190 : Forest := ⟨190,10,fun i => g190Y[i]?.getD (0,0),g190C,g190A,g190L,g190I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g190P5_0 : block g190 5 0 46=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g190B5 : block g190 5 0 46=true := g190P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g190P6_0 : block g190 6 0 11=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g190P6_11 : block g190 6 11 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g190P6_107 : block g190 6 107 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g190P6_203 : block g190 6 203 32=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g190B6 : block g190 6 0 235=true := (@block_merge g190 6 0 107 128 (@block_merge g190 6 0 11 96 g190P6_0 g190P6_11) (@block_merge g190 6 107 96 32 g190P6_107 g190P6_203))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g190P7_0 : block g190 7 0 10=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g190P7_10 : block g190 7 10 59=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g190P7_69 : block g190 7 69 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g190P7_165 : block g190 7 165 22=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g190B7 : block g190 7 0 187=true := (@block_merge g190 7 0 69 118 (@block_merge g190 7 0 10 59 g190P7_0 g190P7_10) (@block_merge g190 7 69 96 22 g190P7_69 g190P7_165))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g190P8_0 : block g190 8 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g190P8_1 : block g190 8 1 30=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g190P8_31 : block g190 8 31 19=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g190B8 : block g190 8 0 50=true := (@block_merge g190 8 0 1 49 g190P8_0 (@block_merge g190 8 1 30 19 g190P8_1 g190P8_31))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g190P9_0 : block g190 9 0 6=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g190B9 : block g190 9 0 6=true := g190P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g190P10_0 : block g190 10 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g190B10 : block g190 10 0 1=true := g190P10_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g190T : checkedTables g190 10 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g190 0 0 0 = true)
  · exact (rfl : block g190 1 0 0 = true)
  · exact (rfl : block g190 2 0 0 = true)
  · exact (rfl : block g190 3 0 0 = true)
  · exact (rfl : block g190 4 0 0 = true)
  · exact g190B5
  · exact g190B6
  · exact g190B7
  · exact g190B8
  · exact g190B9
  · exact g190B10
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g190G : graphValid g190 (boundsBefore K189) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low190 : Lower true (varsX 190) (graphGoal 190) 11 := lower_forest (g:=g190) (i:=0) (hints:=269620272) (before_sound K189 V189) g190G g190T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K190 := extendKnown K189 11 [(190,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V190 : Known true K190 := extend_ok (m:=190) V189 low190 (by decide +kernel)
def g207Y : Array (Bits × Bits) := #[((sampleWord (w80 [0xffc07ff800fffffe03,0xfecb2a2ba20000f0000f])),(sampleWord (w80 [0x148b21526a4948a458,0xa6cb0a2aa25555555555]))),((sampleWord (w80 [0xffffffffff001ffffc,0x34edb8091000f000ff0])),(sampleWord (w80 [0x191202604c0d80c891,0x334e5a00111111111111]))),((sampleWord (w80 [0x7fffffffe00000,0xd372d62500f000f000])),(sampleWord (w80 [0x5e1c0b80700e02f0e1,0xc0c372d4253333333333]))),((sampleWord (w80 [0x7fffffffffffff,0xf922299d6b0f000f00ff])),(sampleWord (w80 [0x60200c008010030000,0x202195082222222222]))),(0x0,0x0),(0x0,0x0),((sampleWord (w80 [0xffff80000000000000,0x98c67ad8f0000fff00])),(sampleWord (w80 [0x8000300300600c0102,0x10842ac04444444444]))),(0x665142404fffff00000,(sampleWord (w80 [0x40040080100000,0x8888888888]))),(0x0,0x0)]
def g207C : List ColumnInfo := [(1,0,206,0,8)]
def g207A : List (List Nat) := [[],[32,99]]
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
theorem g207G : graphValid g207 (boundsBefore K190) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low207 : Lower true (varsX 207) (graphGoal 207) 9 := lower_forest (g:=g207) (i:=0) (hints:=16778803) (before_sound K190 V190) g207G g207T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K207 := extendKnown K190 9 [(207,[]),(231,[83,67])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V207 : Known true K207 := extend_ok (m:=207) V190 low207 (by decide +kernel)
def g221Y : Array (Bits × Bits) := #[((sampleWord (w80 [0xe007ffffe1ffff9164,0xdc16e000000fc0000fff])),(sampleWord (w80 [0x44510a204404101144,0xcc00e249249249249249]))),(0x0,0x0),((sampleWord (w80 [0xfff800fffe1ff8318b,0x3c89500003f000fff000])),(sampleWord (w80 [0x80602c028040213083,0x3c0140c30c30c30c30c3]))),((sampleWord (w80 [0xffffff00001fffda3d,0x31312000fc003f00003f])),(sampleWord (w80 [0x80300b0881400a39,0x31110186186186186186]))),((sampleWord (w80 [0xffffffffffe000462a,0x8b87903f00000003ffc0])),(sampleWord (w80 [0x902404c0009824628,0x3861514514514514514]))),(0x0,0x0),((sampleWord (w80 [0x4984,0x67ec8fc000003ffc0000])),(sampleWord (w80 [0xe038070110e044104,0x42ec8618618618618618]))),((sampleWord (w80 [0x2651,0x42404fffffffc0000000])),(sampleWord (w80 [0x100400800010000000,0x820820820820820]))),(0x0,0x0)]
def g221C : List ColumnInfo := [(1,0,220,0,7),(4,0,217,0,7),(8,0,213,0,7),(16,0,205,0,7),(64,0,157,0,7),(128,0,93,0,7),(5,0,216,0,5),(9,0,212,0,5),(12,0,209,0,5),(17,0,204,0,5),(20,0,201,0,5),(24,0,197,0,5),(65,0,156,0,5),(68,0,153,0,5),(72,0,149,0,5),(80,0,141,0,5),(21,0,200,0,4),(25,0,196,0,4),(73,0,148,0,4),(76,0,145,0,4),(84,0,137,0,4),(129,0,92,0,4),(132,0,89,0,4),(136,0,85,0,4),(144,0,77,0,4),(192,0,29,0,4),(0,512,224,3,6),(0,513,224,1,5),(0,514,224,1,5),(0,515,224,1,5),(0,516,232,0,7),(0,517,224,1,5),(0,518,224,0,4),(0,519,232,0,7),(0,520,232,0,7),(0,521,224,0,4),(0,525,224,0,4),(0,526,224,0,4),(0,527,232,0,7),(0,528,224,0,4),(0,530,224,0,4),(0,535,224,0,4),(0,537,232,0,7),(0,538,224,0,4),(0,540,224,0,4),(0,541,224,1,5),(0,542,224,0,4),(0,543,224,0,4),(0,546,224,1,5),(0,547,224,0,4),(0,548,224,0,4)]
def g221A : List (List Nat) := [[],[98,67],[32,99],[32,48,64,96],[48,100],[48,66,96,32],[64,50],[64,98,48,50],[96,32,50,67],[96,66]]
def g221D4 (j : Nat) := if j=0 then 0xd095539259171d4910 else 0
set_option maxRecDepth 32000 in
def g221D5 := limbs80 #[#[0x5d164d4c205d163d4c20,0x5495048110e0974d4c20,0x54d514c1104c9214c110,0xd51514c110551514c110,0x54921501104c92150110,0x21151501105d52150110,0xd4d51501109515150110,0xdcd5150110d895150110,0x5d55250110e095150110,0x54932541105487154110,0x549515411054d3254110,0xd8d52541105895254110,0x2156254110d915254110,0x2156454110d4d6254110,0x606425411054a4254110,0x58f525411054a5154110,0x60b53541105935254110,0xa0774541105d37154110,0x5d4755891060b6454910,0x551518c110549218c110,0x607548c110607528c110,0x5c550c81105515190110,0x54d51c81104c951c8110,0xe0964d49105cd51c8110,0x59171d491059170d4910,0x5c9521855054a3154120,0x55151506106077054950,0x60564542105d56450610,0x5d164d46206056454610,0x5d164d4e20e0974d4620,0xf51ba17c1f60b7358750,0x56a9d539a674ba95cf48],#[0x2e659ab2d63ac6d78ab9,0xb68dce997315e1bbd175,0x4ce95c6b786d8d99a6b4,0xf31e4bc6770ed1d63aa7,0x912a55bcbb07f83e87c8,0xf07742b9daef07652a9d,0xa23ac28922ea248ba08b,0x24c98f02e8342ba0aef0,0xc9d22727440ba4f12eb3,0x1512ea4d0aa135286409,0x8b286b6aa212aa8746a1,0x848a6c9168b2a62fc19e,0xf4eb12ab70f53cb122fa,0xdb1a66125138c1253ac4,0x338e2a4eb2c328d30c9c,0x8324ba1c9acd706b34c,0x324d21c940cb06fa0c93,0x4db3b1c27b26cb3c1b48,0x93c960aee9216cac6832,0xcaee07312aaba5e47258,0xc30bc0dc86c6f2da9d,0xd30d928b2842f2408fc9,0x2198bc9761b21d0bc972,0x28040000f29e05ca6853,0xba2a89420068160480e0,0x624e92a469023a8da328,0xf8779ce6f9ae679845c9,0x809c260942388a218821,0x8be2e8b62c8ae2a8a42,0x88de368d6348ce328c63,0x8fe3e8f63c8ee3a8e63,0x891e469164490e429064],#[0xb019622010852e4a9264,0x2e0408840d2048020000,0x590800810101,0x19410000000060201002,0x22c201000f7050000d4,0x90800000005584000000,0x190800000001]]
def g221H5 (j : Nat) := if j=0 then 0x8 else 0
set_option maxRecDepth 32000 in
def g221D6 := limbs80 #[#[0x54c20591530816354c20,0x837454c20dc15308176,0x9d5630817558c205d163,0xd4c20dcd650817359420,0x44174d4c205935308163,0x5d420441510811048420,0x109105d4424417010910,0x4415048110d944244176,0x5d520441654811054520,0x4c110485304417648110,0x441524c1105453044132,0x5d130441544c11054d30,0x4c110d4930441754c110,0x441764c9105913244354,0x541404412150110dc132,0x50110549404415150110,0x44265501109454044165,0xd49404435150110d4140,0x50910d95404436250110,0x44175509105954244152,0x109504436550910d8d42,0x541101c9504407154110,0x44143541105095044132,0x54d50441525411054550,0x54110589504415454110,0x44172541105c55044164,0x9095044176541105d150,0x54110949504425154110,0x44264541109895044254,0xd095044274541109c950,0x54110d4d504435254110,0x4436454110d8d5044362],#[0xdd1504437354110dc550,0x54910595524407054910,0x4436354910d515244176,0xdc5524437054910d9152,0x54d10dd9524437354910,0x44165589101d56244372,0x9d56244265589105d562,0x59510dd5624437358910,0x441218c110dcd6544370,0x55230441528c11054630,0x8c110d4a30441758c110,0x44154901105464044354,0x54a4244354901105d640,0x909105d6424417190910,0x4415494110d964244176,0x5c652441649411058a50,0xc81104c7204436594910,0x44151c81105432044132,0x5972044153c811054b20,0xc81105d72044171c8110,0x44353c8110d432044265,0x5c74044151d011054340,0xd41105935044162d4110,0x44164d491058f5244171,0x5d35244171d49105c352,0xd4d10d935244176d4910,0x44363d4d105cb5344170,0x1c55048172d8d105d762,0x54120545504813154120,0x48231541205855048152,0x94950482515412090550,0x54120d4d504826154120],#[0x4817654520dc55048361,0xdc1654826558520dd953,0x8c52059631481518c520,0x48365945205965148176,0xd875148170d452059661,0x185505486154176d4d20,0x54174185505c86154162,0xdc15154363545505c462,0x585501cd615437054950,0x54361945505c25154373,0x5c6625417194950d8a51,0xd85505cb6154162d8550,0x54274d855094b6154174,0x5d36254173d89505c762,0x50610551418415150610,0x84141542105d54184164,0x5c950841645421054950,0x54210d49508417454210,0x84164546105515184376,0xdc1528437254610d5151,0x58610dc5548437154a10,0x84175592105c56484352,0x5535184171596109d564,0xd46105935184162d4610,0x84171d4a105cb5184170,0x5495088171d52105c354,0x54220551508815354220,0x8815454620d4d5088161,0x5d951881645462058551,0x54e20dc5528837654620,0x8837155220dd15388176,0xdd9548837355220dc954],#[0x58620551618815258620,0x8815458e20d516188352,0x553518837459620d5163,0xd46205935188162d4620,0x88164d4e205d35188170,0x5c161d4174d4e205c353,0x587509c961d417258750,0xd437358750dc961d4274,0x9be3f8df7358b50dd161,0xa7e979fa7d9f27b9ea77,0xbbadeb6abeaf6bbadeaf,0xcbb2bc7f1ebf2fabdaf4,0xd6f58cfb3dcef37cdb2f,0xdd370dbb6ddb35ed775c,0xe6b96e3f7cdeb79de376,0xebbadeb3abe9f9ee779b,0xf53cef37ccf2fbceebb6,0xfe3f4fcbf0fb3dcf6bd6,0x962ea0d42ba8354ae60d,0xe46ba83932e80e54b983,0x6e3a641946c083c370e0,0x2827c19b58aca1d84a98,0xf80706460dc39cdfaa8,0x25463b19458ac63f64b1,0x1a6807069801c1969c68,0xc8ea64b13544b0a9c39b,0xb200ce2c60334b23b4d2,0x706a264a92a8baca0334,0x2b1bc08304a920c2a9c8,0xcac8fd08c03f40706f76,0x5ec083d7aea0e01c1b34,0x8faec1540bb05222a414],#[0x711c005c6706161bc105,0xd7ae28303c28603f021,0x8b4abaa0e22a4832dc0a,0xa2cab048b88a922cb302,0x4815aa92203f0e844aba,0x2a057aea8192a9a0652a,0xa68494a92125264842cc,0xc1a117ae6848ba9a122a,0x2ea8290a9a097aea842d,0xdc3a14af06855cb9a157,0xb3028c1fc32195ae6865,0x2bc121c430e8c2ac1230,0x8ab048a11c3a1ca70687,0x994a106447068910c3a2,0x657ae81992a986652a41,0x1b2dc2864b30a195eba8,0x6e4aa61b2dc106e4a64,0x81a5eba06e2ea81b8aaa,0x884470e1c56ba8695ae,0x41d10c3884a306212cc,0xc0879daca1d56ba074a7,0x306222cc088942e81e2d,0x1c2080470a1f10c3888a,0xb70a6c5eba9b252a46c1,0x8aaa1b64f066d2dc11b4,0x92aea6e5eba1b62ea86d,0x14aba9c4b3027111c39b,0xc942e86f2dc09bc430e7,0x2711c21c0430e722cc09,0x8aa02a8282cc08b4b702,0x42694990985f082a19c1,0xa899eeca267ab289a52a],#[0xc42825c20a20aa8285eb,0xa98a22aa6282dc10a1ee,0x2a8282dc18a17ee6288b,0xc420a22ea8288d2a0a23,0x7eea285eba8a23708288,0x24c20b8b30a2b5fba8ad,0xcb3022f11c38a52aea29,0xf1ec30bd2aea2f24c20b,0xa87b0a3040ba8c0430e2,0x2a1fc08a897082a29c18,0x1cc7b043124c20b07f04,0x2745eba9ce2ea8738aaa,0x9d52aea762cc09d8b70,0xa88e4abaa357ae28d5ec,0xc3a383b0e8e48baa3a02,0xac43e0ec11553aa88f0f,0xab10f62aa43d3db91059,0x2aa4482dc10f5eec43d7,0x7ab2120b304487ab1122,0xcb304388aa90e17ee848,0x55f391562aa45529c190,0xea22a43a5eba154b3045,0x371ec30e9dec63a86a98,0x8dc7b0c3722c28dcb302,0x83b88a90ec450e3710c3,0x911cb302471ec30ed42e,0xe84f1ec311c8b0a4788a,0x4393c430e4f1ec313d42,0x4c43e88b10f9e2c43e11,0xab18fa26e43e6bb10fa2,0xaac83e23c18f9aec63e6,0x2cc09252ee83e6bb20f9],#[0x7b0c4922c2925e2c449,0x6ab1941aec4506ab114,0x41aac85022c1941aec65,0x4123c29052ee8506bb21,0x905aaa64179b9105e0e4,0x84140ba1047f06416ba9,0x2905a90a411fc210506e,0x85241ba1488b0a4b6bc,0x420e49308392cc08e47b,0x7023c2cc0934b7024425,0x1438f15ee63c77b18f0b,0x8b045123c10fddac63f1,0x1ec214ddee6531ec114c,0x946e84a2dc0900430856,0x21fc11088f0a421ec312,0x508b0a4c6bc2909a90a4,0x452a41114b702451ec11,0x95cb302572cc0938af04,0xe7d10c195d7d02575ec0,0x1249070e7e2dc09f1070,0xe4903eb22483f04923eb,0xb2094570a9115c2a40f2,0xb0e231bc108c43082540,0x1b28400f0a2403c20900,0x2b001102c384cc2ea134,0x7caa0c80f0a123143045,0x80f0e3319c18cc0b0e35,0x85aa91e047003402c38d,0xe40b0e7b3cbb1dcfeca7,0x5e28c19600f0a7a11c01,0x17d06ca5e10c217906c4,0x5b0ec09806b045c10c0],#[0x1964dee85d1ac11748b0,0x6103c096817085a19c,0xb12546b04803fb29fc0b,0x7069541b1a5502c69541,0x1c225506c89540b22544,0xfec6963eb1a58fec4961,0x3fb2258fac8960fc1a58,0xdae8941bc1250eae693,0x80fc0a5c0b0e9903c3a5,0x906f046403c22601f069,0x6831ba9986b046619c19,0x994c2ea6318c198c0b08,0xa671cc099c6706651dc0,0x1880f089d02c19a4c6e,0x9b11c22683b026210c,0xb99a80f0a9e3bb1a6c47,0xf006b3bb99a95f006b57,0xbbb355e2c4d574b2350e,0xd302d61fc335daac2d96,0x1ec13687f0cd82bc1361,0x85f0cd172b234202a8d0,0xb30b2b784700d336bab4,0x7182c8dd15c336d82c8d,0xdc60c2b71cb02dc37ba3,0x3a8dd0edc36c3b71850a,0xeb3cb93a102c8ea40b1,0xa3a582c8e730b2bac470,0xe236c3ba5830ae936b,0xc038102cadf1cc0b887b,0x2caec30b2b80f2c4e010,0x6bab8cdac8ee36b2384c,0x5b02e517c0b905f0ae33],#[0x40b280d02c80319c1b98,0x5b3060137ba004eee800,0x202c3010c2ca04374380,0x2cdae80b3aba0280f080,0xc0bc1030db0e0b02c38,0x18670a053aba814c2ca,0x80802c202463080719c2,0x9a8222a4a014c2024570,0xca51ec329222a4a486a,0xa928e22a4a688a92847b,0x6e4aa78a92aa22a4a888,0x8a9a8a22a4ab88a927de,0xfaecb08843a8a2706a28,0x7c1ab00f0ab203c3ac4,0x906c2b61cc0ad07702b3,0xe14c2adc4308b64aa9ad,0xb40b02ad1dc0ad4c6eaa,0xaf5db92bc0f02b802c22,0x3c9aea4f26aa93c906e2,0x6f078b13bd06e8f240ba,0x13c5aac8f36ab23c1dac,0xa8f568aa3d4fee4f52bc,0xc23e0dee8f660b23d1a6,0x3090a40b242902c50a02,0x6ba42582c90702c3c204,0x7b01021fc04002f050b3,0x1ec040c7703011cc0c08,0x80b0cfb02c33e4730303,0xe36ba43102c90d03c23e,0x147b01051bc14102f050,0xfd10c03f00b0f0518c1c,0x3f8f2cafd0ac0bf5bac8],#[0x8bf02c1c180b02ff36b2,0x931106c8c33bb9af8430,0xe4b93cb93147304c468a,0xc02f04300bb03c3ae912,0xf00c83bb2308eec8c110,0x403247f00c902c3b2c7,0xde84ca36a13290700c94,0x1ec03300f06ca03c1328,0x4f6c4c610c0b00530acc,0xd3db131d7b00bd10c02f,0x3c0f08ce3ca93380f08c,0x1019c1c3c0f02cf3c90b,0xc4c73031117c24405909,0x31202c24500b051402c1,0x24580b031602c1c54730,0x603c016807801e00002c,0x582cc138078034816809,0x7e13308e84542080e006,0xc886182f016a0b1054c2,0x3ec1e20e7070c36c1a50,0x12e895448423010e0828,0x45782ac1500a44506270,0xd17a8bac5c02d81670b1,0xe466232318d8c446122f,0x721b50d886aa34d1a08c,0xec07443941c60e106f43,0x3f11f20f5c7903c01dc0,0x90e486242320b10207f2,0xc476235918c8b0449220,0x793849a84c125712588f,0x5e52728d944ca084f727,0xbc15c0ad055d2a614dca],#[0xb7e5b72d49668b165832,0x2fd17b4bc45da2e7971c,0x8c6862c3101860c1c606,0x43361990cb8654326190,0xf4d5e69e3499a2cd0667,0x193851becdb66d13649a,0xd88e9c74639d1cb8e427,0x7a53cc9e34efe7773b79,0x20210007f13ec9f20f66,0x485e42920f505c82240b,0xba2ad13a895444a1f90d,0x48f447423811a88c545,0xa424f926492a48e24352,0x31697f4bba5b52ca9504,0x4ec273d38c9b74d42655,0x9444a1550627fd3ec9e5,0xb531a95949ca4151928a,0xf5552a98547a9ed4e6a6,0x357d2bb95c2ad35632a,0xced664b2658eac4d616b,0xb8b5beada96b4b515a32,0x2f59792bba5d6ae81730,0x2c116042ff57e6bea5ef,0xab135880c37617b08583,0x2cc8e64331e58d8c5d62,0x69b32d97ecb3655b28d9,0xa44d15683b3d99c8cdb6,0x6ba3569a9ed4769fb4b9,0x1b60da46cdb631b08d7c,0xd6f23771ba6dcb6e036e,0xa5c42e13702b7f5beade,0x6e7333979ca4e4271bb8],#[0xac1d4ce9b746ba0dcf4e,0xefd77abb89da6ec875d3,0x3d01e70f2578cbc35e0a,0x4f7f7bbbdbdecef5f7a4,0xebed5f54fa27cd3e49f1,0xf2ff07f2bf75fa4fca7d,0x19c0ae047014805c00df,0xd706282d413a08d03b8,0x854427212308483dc1ce,0x61b70d286543061730b1,0xc88a44322050fa87943a,0x662a314589ec4ce25711,0x918c4c6062f11708b0c5,0x75a39d1b98d746923331,0x219905c80e3f71ec8ef4,0xc9924ad24391dc8ce44d,0x32b9957ca8651b279938,0x24bc65cf2df96bcb2658,0xa934c9a04ce263531298,0xc44e026ed36e9b34d7a6,0x7973c39d6ce967373909,0xa04cfde7d73e39edcf4e,0xe873431a14d086833411,0x4a3c51c28cd45ea2b510,0x329754aea53526a91d48,0x8a7e53d29d14dca6a53,0x52aa79533a955476a2b5,0x5afad15656b19578aae5,0x586ac25609af85772b89,0x9650b245902c6b62ab11,0x7da1ecff677b37d99ecb,0x9d6c6b5b5abad4969cb4],#[0x845bfade16e8b705b5ed,0xea1744b9d5cc2e41718b,0xbc6ddfaee976cbb25d62,0xef877b9bd8de9ef3b795,0xac015fd2fd57e2bed5f2,0x3071830c12607302580,0x82c3961ab0c5858c2761,0x3271838b2c51e2631158,0x904c7ce3c71d38dbc696,0x650b275932c936473219,0xf979cb5658b2b5952ca5,0x1e6ef3679a7ccfe65f31,0xfd9f0cf2e76f3a79cbce,0x400017441a18d08681b3,0x82307081018021081000,0x81140415400070201304,0x20106e06c140d1124505,0x54506a00010c42798008,0x12107542910036068109,0xd8342701608090302706,0x1948ac4a02051141f12,0xcea2881789883908a643,0x8629044140905c7943c0,0xb7216e42dc85b9098537,0x12999b7216e42dc85b90,0x1bb041e6cc7de598e386,0xdf02804f90a25e853198,0x85b61009c8529b04c046,0xa43341df21219a1d216d,0xc634213343a6682a6682,0x3b1002de431e10a5610,0x6650a504dc0c3020dd89],#[0x19080202c0401010080,0xb0804a0800006c200808,0x5819604000101000000c,0x10045862c28e04000002,0x80000006c2b41ed8699,0x63ccbe630060200c07dc,0xac0ac0838b106562cfa5,0x860001a8201ae072c201,0x200c04000180ec50a762,0x6020000001b0ab81b70,0x3504010100321cb0b010,0xe04000000000101d6040,0x6a0c6c35c6260200006,0x45a1d342092f58ca808,0xb418ef6200941d418b08,0x9051b0ea0ea0c6c20000,0x84019c0837a31c79891d,0xd41768c16c42321d418d,0x3db080190b01e7982321,0xd87504035061c0f303a8,0x101941004d866d0b014,0x31203a8200808033ba08,0xa10d0402018e440e0738,0xb810000cb08046820151,0xc9b04000001d6100eb09,0x6c2b0200d34416c50803,0x2100a020000013219a0e,0xcbd82994200b01602013,0xfda15a0ad0403ac3ec0,0x580a0201321009a,0x65c080004d040200db08,0x282000116100005a0e58],#[0xc32342a8588020001283,0x360200013a423211a0e6,0xc84022e040000031c808,0x4000200c040000,0xba16039b08066c39b080,0x3cc0a020194100009410,0x625702c06b614050160,0x3bc31590d9080000077,0x6020000000198258c00,0x301001a0803010000000,0x4e040200808058080,0x200000100b2100602000,0x800000750580cd040,0x4000101000000c302010,0x1c0800059080202000e0,0x13014058080000000400,0x200008e07b610000f724,0x816d6c40001d6170156c,0xdb0a75b1275b10075871,0x5b120200012c08000202,0xc8402dd41084000d85b,0x2c040001010000004040,0x200000000002f2410020,0x8000000000006f485a8,0x406c84010100002eec48,0x400033962b2100b21b21,0x1ab0805586c8402c86c8,0xb3c2b19135624d84020,0x58d9f905561cb0806d86,0xf7d898f1c2083b9,0xc06c84000180b01000,0xa10040402ac200000000],#[0x8501c604000002010033,0x8402c85014050e8400ee,0x28080004da14040002c,0x60501000057020080802,0xc6040002c8401010000a,0x6d81004ba1000040501,0x5b0201008059a1b342c,0xb214054e840180800,0x4f8415c2200000000000,0x20000000001642000000,0x2c8400010100e60580a0]]
def g221H6 := limbs80 #[#[0x2123500010020006501,0x51560006010052050a2,0x82481941,0x1412207000608f03c0,0x403a0d80000000000,0x18340000000000,0x6077488ba6000,0x6024000000000000420,0x0,0x880000,0x1c2ecc5c42c00010a0,0xc18e04800181bc47e0a8,0x8000000810646a07e000,0x81f2050001ba2000210,0x0,0x458c6c411691500000,0xf603180000000000000,0xa08000000000000040ca,0x40840590158508000000,0x1196112045d03800a486,0x80280dc00,0x502603400022700,0x400000000,0x0,0x11100070000,0x48fc00180c,0x30000002656000000000,0x1a0006242066a2,0x1f000000000000000000,0x102500041150800,0x20100000000000920180,0x42766040000cc000001e],#[0x80b0000000992000,0xba099334000000000000,0x3904a80000000004c,0x411000000000580000,0x1843000205d07883b0,0x0,0x0,0x14000000000000048a,0x27000000205a00,0xa30006e0c00000000000,0x304400000000000003,0x10000400d0528359030,0x2168e94001,0x20000000000000000,0x0,0x387e00000,0x28140,0x190300002cb7040000,0x1702390568380000464,0x800000049d000051983a,0x404c0108960006a2,0xeb00c000d06a25c00000,0xd16c0bc00000000046,0x122c0]]
set_option maxRecDepth 32000 in
def g221D7 := limbs80 #[#[0xd48105941054c1054810,0x5842054c2054420d4c10,0xd4420984205942058c20,0x81105885058450d4c20,0x4c110481101491010910,0x5411050910501104c910,0x595105891054d1054910,0x9411090910901108c110,0xc8110995109891094910,0xd4d10d4910d4110d0110,0x14520d9510d8d10d8910,0x54d2054520541204c520,0x941208c5205952058520,0xd4120995209852094520,0xd9520d8520d4d20d4520,0x54950545501895018550,0x94950945505895058550,0xd8550d49509895098550,0x546105421050610d8950,0x59210586105521054a10,0xd4a10d4610c821059610,0x54a205462054220d5210,0x58e20586205522054e20,0xd4e20d4a20d462059620,0xa7f3758b5058750d5220,0xdfafb7bbbddadf6eafd7,0xdfefb7bbbdbebf5d9fbf,0xf8fbfdbdfdfef777b7da,0x31ee2423ffdfdfe7eff5,0x6e66c25d4788ba0f197,0xa010588028a92d356494,0xc594183bb0005760062c],#[0x8098b2813d63020aec0c,0x2bb043165080eec0415d,0x8f7d511e0ee6081dc810,0xd31464ae28c15d8914ba,0x46eaa48dd4c91bea8a37,0xaa24df484994baa32973,0x4ca5d09b4a993693226f,0x544e3e909c29752692ca,0xa94ba9c49653852e871f,0xb1157e512afaa255f484,0xd7d513a96ca552594aa5,0x714852ea752594e94ba1,0xefaa25c15d8b93b89725,0xa45dfdc4bbe38977e512,0xd2d88ba4b1175f522eba,0x8cba4b1975f532ebaa65,0xa5b21749642e56e65d2d,0xa1f49643e92c47cadd0b,0x2b70284ae294a5d4f94b,0x5201aea40a5c0802bb14,0xaec7895c4f02bb100e7,0x84455d0892b891297022,0x15d8c15b8180576222ce,0x902ba9202571400eec60,0x2bb2625714c52e09815d,0xa80574500eea681dccd0,0x5763262ca64f58cc82ba,0x4e7ec69ca5c1383bb190,0xaeaa415c9482bb273165,0x6c1dc0da5b81b1f73360,0xdccd9fb99b3c73360ee4,0x514bad17552a20ae4a81],#[0xb24a496294bea529754a,0xb39649296ed28add2524,0x70a462cb2ce99259cb24,0x862cb48e99291cb25229,0xcb30e992620b14c2b709,0xca5c2983bb4c05769862,0x92682bb533165a674c94,0x14b85407769a0aed34e5,0xacf39719e0aed50e592a,0x774a00ee540e9d679cb,0x50a7cc614f58c2a2b085,0x8ac22c1dd8282bb05316,0xc2cc59459f318b3d6316,0x154c5233a8745750e0ae,0x31eb1862b700c8ea629,0x2bb0631650c74c818e59,0xc3964187ac6301dd830,0xd74100aec30c59461d32,0x120ee224f9d441eba883,0x2e624cdc4498b8890773,0xb48dc96aaa92d3373126,0x9496baa92d4b615a0aec,0x6bbb92d74725abea4b5d,0xbab32b745abea6b5754d,0xb2970560aecc885c9b94,0x51680eecb815d958eb9a,0x40aece0a5c1c02bb345b,0xe4e4a5c1c83bb2f05757,0x41dc18a5b83105767242,0x86a82b8bb0773620ee2c,0xaea9d55f52aabaa55525,0xa554964aa92c7557d4ea],#[0x576ac8ac3592ddaa95b,0xae0aed74a5c2e83bb56,0x62cb78a5c2f18b2d72b7,0xd6015dac18b2d83d63b0,0x15daf98b2df2970be0ee,0xac82bb593964b246e564,0x3b8dc0576c052e1801dd,0xd45721a0ee9701dcee0,0x9708456e0f905c4722ba,0x8038e7011585e23b0c22,0xae51c89ca210b9441f73,0x1c15ce399a9c731538e0,0x5c21afb83f2b707e0ae9,0xe86b9c60d758686c50ca,0xba3d1e737a4ce2f495c5,0x805719086c51459d1e8a,0x73c20ee58415d2402b9c,0x40ee7881dc7103ba6107,0xe40935940a6b2800774c,0xa0544942a8124d73049a,0x41196ba924d6524f2a44,0xbca9238151470ea08e15,0x2a38753470aa68cb5d51,0x8552270a844e19951c2b,0x2390ea84e15509c3a913,0xea8721550e43a91c855,0xa560544ac3a81585502b,0x15c4ac3a89585512a9ac,0x8ac3a91585522b0a6456,0x2aa1d86652b0aca56158,0x248151490aa0921d50ec,0x1522f02a25cb5d5232aa],#[0x2e5ee45d3588bb1a9176,0xee25e15c4b97ba174d64,0x5e1508bc2211785322f0,0x948bc2a91787422f0c84,0xbc2391786622f0ac45e1,0xa19787722f0ce45e15c8,0x787732f0ae65e154cbc2,0x642f0ac85e1950bc2aa1,0xf0ce85e15d0bc23a1786,0xa4961550fc2a91f87742,0x53591296b9254d624ac2,0xd4827b2904d64285ae89,0x26b19679522c5aec40b5,0xa964f652c9aca593d8cb,0x4f653cf2a478b5d8b16b,0x305aec44b5d8f16ba9e,0x5ee260bdc0c43b818847,0x6613d88c3d3118796230,0x8550c17b9984f63309ac,0xc27b2184d6430c6a861,0x6bb184f65309aca60bdd,0xa04f6540f2c480bdd8c1,0xd714c5ae098b5d9016ba,0x4c9ec699358d327b1262,0xae8993d91326b2262d73,0x68bdd0d26b21a2d764c5,0x5ccd17ba9a4e65349aca,0xd26ba9a4c75349ee6693,0xb9192d75429eea6939d4,0xb8770365ae49d3594c97,0x72449ee06dbdccd97b91,0x50ae52a154a542a0ca2d],#[0xa92605464c2ba4a85549,0xd358a596bac94d6592ca,0x925b1aa4b6154965ee52,0x26b1524d65965ee92d35,0xa524d64a4c2a948b5ca9,0x4d65985ee3313d4a716b,0x1a89acb34bdc6696b8d3,0x9ae94135ca826b8d02d7,0xa18bdd0326b2064d650a,0x35c4496ba0c4d64189ac,0x56bca92d2f715a9ae625,0x320ad85415b0c62b614c,0xad85615b0ca2b615456c,0x5535b0ee2b611c56c330,0x6f0aa2ce1dd16c2aa2d8,0xacaca0545926b2ac2d71,0xb8bdc1716bb2b2d75649,0x54d727b0ae82615d02c2,0x726b2ae2f735cc6a6b98,0xb0b42f765c5aecb93d95,0x42d75689ecad13595a40,0x53709ec2e0b5c1c16bb3,0x9acac0b5d9c16b9b861,0xead53595a97bab04e656,0x53595797ba2f2f715e5a,0xc58c3b8312d74725ae2e,0x96b8b64f716298e2c4bd,0xa558553ab0aa5561546a,0x6354acc2a958bdcab42a,0x2ba9acb58bdd2b26b256,0x9ac9758552e96b95d4d6,0x9693d4ad26a95a2d74ba],#[0x3596b97b8d74f54b49aa,0x6c17ba584d64b05ae379,0x6aa5b2d74be9ac97d359,0xd97b72b25ee3653d52da,0xd73c05ae3813596c97b9,0x7c9ec4f98549f17b83e2,0x2a5093d8df30a9be2f72,0x93d92116b9424f6284c,0x5c9e26b13c6152785ae9,0x217ba404f64805ae8f0b,0xb14761528e5ae9113d92,0x761538e5ae51d398a3a6,0x528e5ae91cb5ce3a6b1c,0xe9ce51d35ca3a729474d,0xc6fcbdc1fa73a474d748,0x4b5c5e96b8c360767e9e,0xc3096b8c52f74825ee30,0xa6b9e14e72c29ae58535,0x4400880009ce98535d30,0x40580104030808801980,0xa5826208b8200072819,0xeb037c0d303240bd02c4,0xe8488116043610383de0,0x85b415c854c14284dc12,0x7101ae06981960616176,0x5a20a87f21ea87781d00,0xe25d896024d08e822888,0x2b00a842940a2427a09b,0x18bd62e38b4e2c98af8,0x50d2433e8cb63268c3e3,0x8e5e3838dd43678d7035,0xf743d00f1c3bf0edc3a5],#[0xf242e90824100fee3eb0,0x647b11be464116044a10,0x4d913224b9928c497922,0x2f147050b94004f41396,0x795e6572159e55914fc5,0x96fe5b1969a59b164658,0x85060697f05ee17805cd,0xa465d993263d18cc6291,0x66a59a5468e9a0667319,0x6f59bb26e19b4a6c29ad,0x359cb87229c6470e1c04,0x99dba75d1d4e7481d027,0x1ebe7a29e5c7889e0277,0x167f79f9c7d89f287bd,0x3a844a0da82ba0888122,0x6887a1e686ea18e858a1,0x8d0a30a8b4a2a089ba24,0x25a46090923e88eca378,0xaa5b495e253c941a4cc9,0xa6fa9b0a69a998a62a97,0x7f29f627ba9e0a74a9c8,0xca33a8b2a21283aa082,0x4a6f29a2a5ea95ea4d29,0xab22a86a97aa36a83a9e,0x42bdaaeb2b56ac72af0,0xcad04b37acb4b1bac48b,0xae54b8eae12b74ada4b5,0xf36bbf2ee6bacae98b9f,0x78c11300ebf8afacbe12,0x8c43b0f4c3530bac2830,0xc8031d4c6b3190c59313,0xc5b2e0ca9b290c96b232],#[0xe340ecf733aacde333ec,0x3532d3b34acd1f3456d0,0x660d8eb626d7fb59cd5a,0x80dd5b736dc736e6dacb,0xee17383ce0237d4ded37,0xe6db96ce4e38fae2b388,0xb93ab8ea4ba62e8839e8,0x4bbaaede3b5aeccbb12e,0xbca2f21bc64f0f3c12ef,0xd8cf5abd42f443cf2f33,0x9af9c3e38f84bdecf6cb,0x8fddbf48fc6beecfb03e,0x26c05300c4002ff5bf9,0x71c193058413303c40c9,0x342e70adc28108fc1f90,0xc3f10f1438f0d7c33b0c,0x51513a44a711a444310b,0x5f188c5f517345a1156c,0x31d9c73b1c446e11a8c6,0x223c85720847f51f4c7a,0x7a49bd25fc93924148cd,0x4acf2a5ca73290ca1b2,0x4bf52f1cba32dccb372c,0xd053394cb53224c55308,0xd3764db53644d6334ac,0xf3b4cea93a04e5738dce,0x3f6cfb53e1cf613c9cef,0x4050c7426d05b40b5001,0x8d1bb465d16b45051194,0xd2b94a2d25b48e520d47,0x3d34ea53734cfd30d4ba,0xe352d548b515d4295005],#[0x956e558b557d52f54354,0x5ad56a159bd643586d5d,0xf0d7915d757375c156dd,0x358cb629d86560b58055,0xd9e166d5993658593364,0xadf6aeda976995a41683,0xfb6f65bad6e25b476c6d,0x97385cad71d5c5170c5b,0x77e5dd176e5d7f7545d1,0xb6dec57a75e757935e29,0x65f857d75f3b7c5def57,0x604b808e0097fb5fc77e,0x141845e0f3832e09d820,0x4f881e1eb86e618985be,0x38c4e2eb8b3629b89ce2,0x903e3dd8ee63958db634,0x3ce4d3928e473914e42d,0x9e5bf9656567950651d9,0x669599c665598b661397,0x78d9d8e7359c3e6eb9b1,0x7ba16682ba0267dd9f06,0x7a54691da3ae8bfa27e8,0xa9dea41a8569e5a6de98,0xe36b57ac9eaf1ab0ea9d,0x2ec69b10ec19afbebbda,0x6d7db516d0bb37ecb1b2,0xe7fb94ee2db846de5b6c,0x5dbcdef11bbd6ed7ba8e,0xdc0c7015bf8efbdbe26f,0xc48f0f5c317099c1c704,0x82f1c9c697191c5d714f,0x72cbcaaf283c95723bc],#[0xf3d7ce6f37bcd67329cc,0x4508818241508742dd01,0x26170f88c0e160286c38,0x10000104108181d0d080,0x2a013c440cc060002a28,0x404b10288201a8830811,0x4c5418360a2820c084e2,0xc5385a257a85818312e4,0x85091e178b2422b5090,0x18ba8c5a12f29b060e34,0xa170b64c6a1860b44de,0x176607c333c86d35a864,0xe830452216072d05899,0x5c212e1097084b842335,0x85124b86864ca52c3d64,0x3fa09107f94445fd0c95,0x9bf0a224724631fd0488,0x98cbd098ebb431efc288,0x3c218c3c218cbe188bd0,0x2119e1197a131cfa0910,0x1170847e5825b7b8255c,0x68b0650c0ff7368b22b9,0x32cf19e08b0650c0ff73,0x6798429fd2904664d708,0xc90644f90636fb2614d0,0xc9a6bfc508c67d825cf,0xb3f859808c9f20c75ca4,0x903aea1a666af2d208c,0x3c21e7d26db32a02b5f,0x2bc30633be090bb61064,0xefc043af92064f5bb021,0x32e403365ab9332ae421],#[0x4224adfe922578031e4,0x865f294332a2093ff551,0x227e063700eba418d780,0xc72c3336fab011673e02,0x8c3fcc0b32871803245b,0x114b3d026be08ee08ee0,0xe733033d778481977c02,0xc8395828adc3148658f7,0x5d8f14451edc28bdf610,0x919270a226e1444b7b12,0xd12270a2277d843277c0,0x518ca3aa1ca2ae7fd411,0x125ef812321f94495be6,0x2472eda0532ef0244b7b,0x6992fbfb1a19678fabb,0xde421ef8141157cfde0c,0x36b12e421a72c0325c22,0x2272c03201e1457f4093,0xed664afc913033272c03,0xfcd84b5dd246f85d64c4,0xe10d7210dbfe2a48267a,0x123790740cabc7a61154,0x41220f1a09177510eff1,0x920142170dc0995206bf,0xf08b3fb5a08b1d193243,0x2660220f084b5c218aaa,0x28887c08d6b843555e11,0xe94445606b58a1ab039d,0xad6286df0c80994f191c,0x99518c64f588a9608581,0xd8bf112de0141cccf889,0xb9d194a3e40c8be9c245],#[0x265bf31128773a32643,0xe172c8b5c21ddc238ed9,0xc21ad70867e0467e0461,0x9f8118785cb22d7086b5,0xec89f50634fa8319f811,0x6437d010750d4ec950d4,0x23c7b06493e7689d42ed,0x4fcc2245f7b444cba419,0x1ec192345832271ec192,0x20cb5ac019136f00648f,0x474d9e0c906ff68941f1,0x7e0467e046dd600c87e0,0x31608d5e00c906ff688,0x235e4048cc9031da8889,0xf88dbfa21321208be511,0x912074c904681db0c90c,0x19e6119e611d77092e44,0xc253cc23cfb906329e61,0x718f382aa467bd8992c2,0xae508649a1e289875110,0x1c69c917d2ac0a35c323,0xd061e621cb40025a8f19,0x449a3c7808b87511299a,0x488c03601de50912067c,0x3950330ecae914814fc0,0xf80875f9b0957210f38d,0x33e22487a120d4e6022e,0x63de421b00ed08d20690,0xe8afc08ce033e40933c8,0x1e388920e873e2c44520,0x11a9cc0459f4e122902d,0x40c6df20639f4e122df8],#[0x119c22955a1b7c818dbe,0x7596df630210bf018cf8,0x273f206397b01061c279,0x4015f811cf1f2f9c04d,0x438b507df09611166d6d,0x43b112b482240c7a11a2,0x2063cfc818ca4157fa24,0x491d581afc8910a4173f,0x6a3c445e97828b3c7d55,0xab454b8c2237ac48319a,0xac4b46288df328c65d3b,0x4c47c4515c98ebb2634e,0xaca39c86dfc6639c859e,0x6f9097590c62e8758070,0x763dc85332185fc86691,0x68a1d18b7c85ecd045d3,0xa7fe448e2c53190e5777,0x598f3516319c87079434,0x659f21067d240cfa49de,0xe420cfa485ee92569985,0xc4438826c74f0ee810b3,0x11e44de3087dc25c665d,0xfc80654b5f2261b8e89b,0x22539a68317ba804257b,0x266cc49cd98cb0b16f0f,0x6645e8d0f7f49224cd1a,0xf7da2665861040117e32,0xf5499977c443efeac032,0x590eef5246fb7baccbdf,0xc0032f7eb00c979d4917,0xa438d5b631f7cd28bdf8,0xd20c627d4422ce3c8717],#[0x324fe5644dc790eec475,0x30bc99913fe403247893,0x349322565ed06582d459,0x85ecc4b51e445999113e,0xf22465e0b24cc86bb468,0xc8b1edc0325a5e9835a8,0x34782097ee21ae685326,0x98c5e68247d060e4ee68,0x6ef54d0716d8b710a3c5,0x9d2c835cd0973429ebc8,0x5ce431cca1cca141e50d,0x463241c21cc6c890e682,0xc45e5897ee21d5f23af9,0x4b8cb3d790d3b5634ea,0x43941afd26b209f28758,0x86b9a12ccc89bd6435ce,0x886e0498d9107ca87be4,0xe6073c0c449fec86398c,0x669c9065ff1318fe1111,0x3b249a3439310894e482,0x97ee092947058e7041db,0x4e5925b8e92e8d0af704,0x44f8a468498429fec86,0x50c0265b0c1dfac490c1,0x11b4b14d755121660966,0x806fa8b09bd1a44487e9,0xcbd0a0612bc249909e20,0x68652d8867bb3a8c1391,0x3ada98f568431ab4458c,0x51d13b162dd0ba20f434,0xc69fe0ab245a49d8b145,0xc98fb1624ff41732d764],#[0xa423e22cf444c9ab42ea,0x37364aee35919fa8a0c7,0x50bb276936377ea2836b,0x3a626fa963cf26250269,0x82c041d2081d2081d20a,0x4dd208d6466a921ac8d6,0x6b41b88b9cc147086340,0xdc358eb61a65830765e4,0xe7524de4a18fc8565e46,0xdb02c1b763a610839a0d,0x7b6a8797a1070f802b2,0x6767648b9c861c8b5365,0x8fb2621f90acbc8e62a8,0x4c7b4859b58a0d097905,0x1066a862e08df82c6dd3,0x183da08ab4b1e6d6247c,0xd84dc20a683184b19979,0x74c52ca09be158e03620,0xb60c75a86a7e90e3d313,0xf487ab423eb492d81541,0x74e9209d086ac51d235e,0xfe3644df99912458e89,0x98cabcd8c3ce922e7b22,0x6dcd8b36b15712e642fa,0x32493ba256981648ae4c,0x95148b1d12b2858d031f,0xe6c5ab428e4c559d63b3,0x2607148bd8631e5fa436,0xf9e428307ada0cbc1319,0x157a4c6cdc12e22ec318,0x262b88b9c08ccc68887a,0x8bdf84838e158fdec137],#[0xb88e9818d8578548910d,0x90fbc018edcb82ef262b,0x901b88839312cf48627e,0x4dae4c76fd00084ac98,0x98c87a063ec86bf690da,0x857023ed8363a64826e9,0x32b1070831a7e940c996,0x2d05]]
set_option maxRecDepth 32000 in
def g221H7 := limbs80 #[#[0x48000200208000002042,0x4002010010030090,0x18480802c800100100,0x600001448080,0x14c022100024b4590,0x4824104048904100220,0x1000048201200041,0x80007002004200410,0xa0260144805001800020,0x800000092000000c1220,0x41990000000004f,0x0,0x418e0017000,0xa0000000080370000000,0xf,0xc9830000000,0x0,0xa018a000000000000000,0xc80a846,0x0,0xdd450000814e000,0x0,0x0,0x90000417f00000000000,0x414f000000000000009,0x0,0x10000000041ed0000000,0x64e,0x88898127000,0x90fd00e300009030000,0xc000080140000e423000,0x81034c6],#[0x80578126000,0x403a45350000000,0x5191241fa000041ac000,0xc5419,0x1b35dda000,0x0,0x2d1ce000000000000000,0x455c024,0x1a80000e458000,0x0,0xd1cc80770000000,0xb0000000050350000000,0x40,0x0,0x85d000,0x408300000000000,0x0,0x5c3e000,0x0,0x0,0x0,0xc1440000000080f8000,0x0,0x41b2000,0x164000,0x0,0x0,0xcd6a0000000,0x83f04b20000000,0x821989530000000,0x891b000000000000000,0x0],#[0x41750000c1850000000,0x8107503600000000447,0x90000000000000000000,0x401,0xd0000c1f500000000000,0xd146a000000000000c1c,0xc8aa0000d21,0x49800000000000,0x0,0x80000000000000000000,0xc20,0x815f91e21d490000000,0x0,0x0,0x50fc000,0x813081c1000,0xb8d5f00000000840d000,0xc0d,0xdcdc0000000,0x0,0xd0bf0000000,0x912d0000000,0x20c5421,0x40f5000000000000000,0x81e6000000000000000,0xd158810d000,0x0,0xc1e90000605a000,0x0,0x807f897108770000000,0xb819ddcde00000000000,0xe0000000e1cd600000d2],#[0x15,0x41570000811a0000000,0xc80d7000000000000000,0x985,0xb0000000000000000000,0x70000000000000000489,0x417302204c9b498,0x0,0x810b000000000000000,0x105b000,0x0,0x0,0x1cb0000000,0xc8058000000000000000,0x415,0x0,0x0,0xd104000,0x0,0x0,0x98458043000,0x0,0x0,0x0,0x80a30000000,0x0,0x0,0x9470000,0xc0000000000000000000,0x4cb,0x91ae00000000000,0xc8950000000],#[0x0,0x0,0x0,0x0,0x21dc000,0x0,0x81bc0000000,0x819f000010290000000,0x4c7482900000000000,0x30892000000000000000,0x9ff00000000c12,0x0,0x0,0x401a2000000000000000,0x9d4,0x0,0x0,0x40be0000000,0x0,0x8a0000000,0xa158000000000000000,0xbc95800b000000000000,0x11a,0x4d000024000000000000,0x851,0x5131000041a7000,0x403300000000000,0x50e8000000000000000,0x0,0x0,0x80000000000000000000,0x6615c214c17],#[0x300000000000064e3000,0x423,0x0,0x0,0x0,0xd1780000000,0xa1ce000,0x0,0x51d,0x0,0x80000000000000000000,0x700000000021c0000402,0x5cd,0x0,0x4151000000410000000,0x0,0x0,0xc98600000000000,0x480000000004066000,0x0,0x0,0x983a00000000000,0x0,0x813b000000000000000,0x44660000405d0000000,0x441221d4700000000000,0x8af0000000080065cd,0xc03e4990000,0x8121000000000000000,0x8d00000000000,0x60000000000000000000,0xc19],#[0x4186000,0x20000000000000000000,0x404,0xc0ab891f0000000,0x823b000000000000000,0x4100000000000000000,0x9000000000000c18b000,0x780dd000041db0000005,0x8c,0xc140000000000000000,0x40520000000,0xe000000d000000000000,0xb0000000000000000501,0x84f5000000000000c0f,0x90000000000000000000,0x10000000000000000418,0x401f824,0xc1a500008cab0000000,0x0,0xe40a4000000008005000,0x8c8,0x1403511d700000000000,0x9c1f9000000000000205,0xc1100000d05,0xc51d0000000,0x5170000,0x1170000000,0x0,0x546b000008cb4108000,0x811c807b00000000000,0x0,0x646c0000000],#[0x406800000000000,0xff1cd0842,0x0,0x0,0x0,0x0,0x0,0x80c2000000000000000,0x81110000000,0xc201000000000000000,0x852200000000000,0x18d0134000,0x40000000000000000000,0x98145000000390000809,0x600000000c0106029d46,0x4000000000000000000f,0xf0000000000000000c1d,0x9dd90000000084a,0xc1af000,0x0,0x0,0x0,0x0,0x1cdf00000000000,0x810600000000000,0x80000000000000000000,0xccb,0x146d0000ca1a0000000,0x0,0x0,0xc0230497000,0x0],#[0x0,0xc00000000011fc20e000,0x70000c0b,0x84b30000000,0x10000000000000000000,0xd0f1015d80c6c07,0x0,0x70000c13e00000000000,0xc0a,0xdd3f000,0xc85f00000000000,0x21d00000000000,0x80000000080f30993000,0x10000000000000000056,0xc2450000000001a,0x3000000000000c483000,0xc168000000000000c22,0x0,0xb0000000000000000000,0xad000001bb419,0x0,0x230000,0x0,0x0,0xe0000000004790000000,0x6,0xc0f7000,0xf0000000000000000000,0x8095000000000000416,0x70000000000000000000,0xc17b000040e,0x0],#[0x60000000000000000000,0x40368d6,0xc1dd404c0000000,0x4485913,0x0,0x0,0x514d00000128000,0x0,0xc58012e00000000000,0x195c0000000,0x0,0x407000000000000,0x0,0x0,0x760000000,0x0,0xc10f000a00000000000,0x884c00004222000,0x4400000000000,0x5d52000,0x8171000000000000000,0x0,0x598000000000000,0x0,0x0,0x81a40000000,0x0,0xcc05c000000000000000,0xd00881ab81fb0000400,0x0,0x60c00d092b0528000,0x40000000000000000000],#[0xdd3,0x88d7000,0xc1b100000000c213000,0x40f2000,0x0,0x1d242090000880c000,0x420a000000000000000,0x8158c1410000000,0x0,0xa0000d037c1130000000,0x91e40b,0xc1fc000000000000000,0x0,0x50000000000000000000,0x801bc07,0xc1f3000000000000000,0x0,0x9511816504ee8200000,0x0,0x0,0x8c00000000,0x905600000000000,0x0,0xa0000000000000093000,0x2030000498,0xc205d50e0000000,0x20000000000000000000,0x583d00000000c0a5819,0x0,0x0,0xc4a5c18f00008524000,0x402a00000000000],#[0x0,0xc49b000,0x42160000000,0x32000,0xc03100000000000,0x40000000084ab804b000,0x24,0x40b1000,0x0,0x0,0xa0000000008760991c02,0x44b005230000089,0x0,0x0,0x41310000000,0x0,0x0,0x90410000000,0x0,0x41c4000,0x1409000000000000000,0x20000000000000000000,0x88c,0x0,0x812cc46fd0420000000,0x90ff00000000000,0x30000000000000000000,0xc07,0x0,0xb0049000000000000000,0x8000000ae000040d8048,0x132d04],#[0x81dc00000000000,0x0,0xc0000000000000000000,0xc1470000c16,0x808c0000000,0x0,0xc16d000,0x1190000000,0x80000c14200000000000,0x884b000000000000801,0x0,0x239000000000000000,0x0,0xc92082a01a6000,0x0,0x0,0xdc1b4000000000000000,0x7,0x840a00000000000,0xc11d00000000000,0x0,0x90000000000000000000,0x4cb,0x0,0x0,0xb0000000000000000000,0x1c1e0000d0d,0xc87f0000000,0x0,0xc47f000000000000000,0x904b0000000,0x0],#[0x60000000000000000000,0x80b,0xdc1ce181000000000000,0xc0b,0x0,0xc1d300000000000,0x0,0xd0c0000,0x8870000000,0x0,0x0,0xd0000402ea0580000000,0x1f741694c9740ed817,0x0,0x40000000000000000000,0x80b38c9,0x0,0x0,0x0,0x146f0000000,0x0,0xd0000000000000000000,0x90114bd05408a,0xc0b400000000dd51000,0x413d000,0x583b000000000000000,0x6c12f01f200000000000,0x49945074000040a,0xc09c44620000000,0x0,0x0,0x0],#[0x0,0xc9800000000000,0x70000000000000000000,0x903800000d8,0x0,0xa0000000000000000000,0x20fe0000140,0x410500000000000,0xc180000,0xc8610000000,0x517b000000000000000,0x8d600000000000,0x0,0x0,0x0,0x24995000000000000000,0x597d00000000000040a,0xc488a0000000091ec000,0x51f,0x800000000dc460000000,0x80000000000000000807,0x97000000000000c0a,0x411b00000000000,0xc841000000000000000,0xd0000000042210000000,0x1e30000847,0xc1da000000008002000,0xc9a000,0x0,0xd04a000000000000000,0x14601d080120000000,0x206000000000000000],#[0xc0cb00000000000,0x4000000000000000000,0x0,0x0,0x0,0x0,0x0,0x300000000000001df000,0x90000000000000000849,0x81c7000081b9000089a,0xe0000000000000000000,0xc1b,0x80f00000dceb000,0x8cec11df000,0x449d000,0x41d5000,0x600000000c1e70000000,0xc02f0000423,0x404d00000000000,0x0,0x0,0x0,0x505a000,0x0,0x20000c15400004ca3000,0x90000000000000000c8b,0x40000000000000000903,0xc03f000bc98,0x805b000,0x80450000c0e2000,0x0,0x41250000d50f0000000],#[0x0,0x80cf00000000000,0xd04d605700000000000,0x0,0x4a000,0x0,0x80e0000040500000000,0x88c3000,0x50000000000000000000,0xc0fcd51000000000d17,0x0,0xcc99c2260000000,0x89f0000000000b8000,0xc084000084a1000,0xc51800000000000,0x0,0xc1ee000,0x4c8f000000000000000,0x0,0xd14f00000000000,0x0,0x0,0xc00000000c85e0000000,0x9000000000000000000c,0xc2180000414d007,0x13c000045120000000,0x44ec44760000000,0x494422800000000000,0x48d5000,0x0,0x84cf00000000000,0x4150000],#[0x0,0x902b00000000000,0x848e000000000000000,0x5d3c00000000000,0x0,0xd03f000,0xc2040000000,0x0,0x0,0x0,0x0,0x4850405600000000000,0x40da80bf608a0000000,0xc0000c0e4d512c1e5000,0x10000000000000000c23,0x8d35000008c,0x405e0000000,0x0,0x14680000000,0x0,0x813a023100000000000,0x4000000000000c1b6000,0x800,0x0,0x0,0xd102000000000000000,0xa0000000000000000000,0x60000000040aa0000421,0x403bc944d02,0x821e40ee00000000000,0x0,0x422cc191000],#[0xc0000000000000000000,0x40f1000000000000c19,0x0,0x900400000000000,0x8c9e0000000,0x808600000000000,0x1e0000,0x0,0x886b00000000000,0x183c000,0x0,0x41e80000000,0xc58d816a00000000000,0x495500000000000,0xc88e0000c104000,0xc0000000000000000000,0x4ca1000081c,0x0,0x885300004477000,0x8878000,0x0,0x0,0x0,0x0,0x945270000806d0000000,0xd0000813300000000022,0xc03,0xc0000000090320000000,0x200000000000008e1014,0xc16,0x0,0x20000000000000000000],#[0x10,0x0,0x915e000002320000000,0x90000000000000000000,0x10000000000000000002,0x22bc0ec448,0x0,0x82430000000,0xfc198000000000c61000,0x8881cd93d57,0xc051000,0x50270000000,0xc40e00000000000,0x0,0xc1388cb7c20d0000000,0xc1a000000000000,0xc14a00000000000,0x7000000000000c9a8000,0xcdb0000c23ac21,0x0,0x0,0x560e000,0xc1490000000,0x0,0x4c9540c3000,0x919e3000000000000000,0x8143848,0x0,0xc00009047c5260000000,0x800000c02,0x88b800004061000,0xc4b1000000000000000],#[0x0,0x88ab000,0x1e000000de0000000,0x176000,0x341cf000000000000000,0x507,0x0,0xc1fd0000000,0x80e9000,0x0,0x0,0x104c000,0x0,0x945d4022000,0x0,0xc912c1e40000000,0x0,0x81290074c12d41b7000,0x0,0x0,0xc52520c10000000,0x0,0x48110000000,0x80000000000000000000,0x1a000000000000485,0x30000000000000000000,0x90d,0x0,0x42270000000,0x8135000,0x422f889300000000000,0x10000000000000000000],#[0xc0000000000000000885,0x8b,0xa0000000000000000000,0xc83,0x0,0x7c182000000000000000,0x84b4c17,0xd07200000000000,0x851a0000000,0x0,0x0,0x508a000,0xe0000000000000000000,0x83,0x0,0x40a9017,0x88b000000000000,0xc188000000000000000,0xe6000,0x0,0x0,0xc07e00000000e072000,0x0,0x886a015a0000000,0x0,0x0,0x0,0x0,0x0,0xd0000000000000000000,0x8c9,0xc1aa0000020c91d9404],#[0xc072000000000000000,0x415255c3000,0x0,0x0,0x0,0x0,0x30000000000000000000,0x88b,0x0,0x89849520000000,0x80dc0030000,0x5a000000008062000,0x478000000000000000,0x901dec09b00000000000,0x10000000000002074052,0x60000000000000000c0a,0x41f6c0d,0xf00000000000001fe000,0x81ae420,0x44b500000000000,0x0,0x40b9000,0x84714024000041c,0xe0000000000000000000,0x90,0xe0000000000000000000,0x9,0x60000c11400000000000,0xc9a05,0xc4e9000000000000000,0x90000000000000ca2000,0xc9f00000000c17],#[0xc80b0000000,0x0,0x0,0xa40c00000406c0000000,0xc19,0x0,0x20000000000d10000000,0xc23f048,0x0,0x90c400000000000,0x70000000000000000000,0x898500000000c16,0x0,0x81000000000000000,0x0,0x0,0x0,0x40fe00000000000,0x8a90000000,0xe05b01360000810a000,0x50000c01500000000000,0x40b,0x0,0x9093c820200000000000,0x54452f8917015,0x0,0x0,0x90000000000000000000,0x817e413f0000446,0x17a0000000,0x809d00000000c235000,0xcc9c000],#[0x3cd94000000004860000,0x419,0xc85900000000000,0x80a0000000000000000,0x0,0x14153000000000000000,0x806f0000000000c,0x0,0xe0000000000000000000,0x597,0x50000000088150000000,0x41eb000080480000022,0x0,0xc1480000000,0x1103000000000000000,0x0,0x0,0xd471c0af0000000,0xc08b0000000,0x400000000000008c6000,0xc0f,0x422d000000000000000,0x486d0000000,0x0,0x41ad00008224000,0x502e0000cd69000,0xc1c900000000000,0x0,0x0,0xc0e10000000,0xa0000000000000000000,0x8932000040e],#[0xd50000000,0x0,0x888800000000000,0x90000000000000000000,0x63dcd,0x0,0x4101000,0x145f00000000000,0x20000000000000000000,0xb0000000041ff000081c,0x8212c15,0x1c5000,0x0,0x0,0x93900000000000,0x0,0x0,0x0,0x0,0x1b80cba00000000000,0x0,0x80000000000000000000,0x3000000000000c0d2c11,0x4183000000000c9,0x30000000000000000000,0x1bad04,0x0,0x40000002100000000000,0xd0be000000000000c8c,0x81c8000000000000000,0x808f8a0200000000000,0x49e00000000000],#[0x8046000,0x50000000000000000000,0x85c00000d190df,0x81875044000,0xc0b2000000000000000,0x0,0xc09100000000000,0x0,0x0,0x40c80000000080ce000,0x0,0x0,0x0,0x0,0x0,0x0,0x12a000,0x10c00000000000,0x0,0x464000,0x806700000000000,0x18e9000,0x1f8000,0x0,0x0,0x0,0x80010000000,0xc2370000000,0xc1d80000000,0x0,0x0,0x0],#[0xc0df00000000000,0xa059000081ea0000000,0xc1ca00000000000,0x41f0000000008034000,0x40000000000000000000,0x11d841f,0x1cddd9cc84fa0234000,0x409200000000000,0xb0000000000008065000,0x80000000000008181c21,0x819000000000808,0x0,0x0,0x0,0x0,0xd01c600000000c12b000,0x401,0xc0c700000000000,0x0,0x0,0x0,0x1f100000000000,0x30000000040250000000,0xc0d,0x4026000000000000000,0x91033000000000000000,0xc08,0xe51da000000000000000,0x19,0x1cd5000,0xc61a2000000000000000,0xd883bc12000000000403],#[0x3c04fc1a900000000002,0x0,0xc0ca41b000000000000,0x0,0x0,0x0,0x0,0x0,0x12310000c0e50000000,0x855f00000000000,0xc981000000000000000,0x889000000000000,0x0,0x810e00000000000,0x0,0xe8053000000000000000,0x82447,0x0,0x422e9172000,0x8112000000000000000,0xc1d6000000000000000,0x0,0xc809000000000000000,0x0,0x0,0x4410000000000000000,0x90011000010340000000,0x41970000000000d,0x0,0x0,0x4cb60000000,0x0],#[0x81b5000,0xc0f9000000000000000,0xd460000,0xd006000,0x414b000000004166000,0xb000009d000000000000,0x5d1ba0000000000008cb,0x70000046500000000087,0xc02,0x897c21f0000504e000,0x0,0x0,0x0,0xc00fd4100000000,0xca5000000000000000,0x0,0x80e8400900000000000,0x0,0x0,0x0,0xd8d3000000000000000,0x0,0x0,0x5161c184000,0x3000000000000c160000,0x44db00000000c86ee05,0xc05f000000000000000,0x6440550000000,0x1d00500000000a0ff000,0x41e,0x0,0x90000000000000000000],#[0x6,0x407a000,0xc008000000000000000,0x0,0xc211000000005049000,0x4215000000000000000,0x30000000000000000000,0x48990000016,0x0,0x0,0x0,0x23e0000804e0000000,0x809800000000000,0x0,0x0,0x60000d8f588d40000000,0x15,0x19330000000,0x40fd000000000000000,0x0,0x846c000008f1000,0x0,0xc06a0000000,0x47b00000000000,0x0,0x5000000b700000000000,0x916,0x0,0xc0000000000000000000,0x8087000000008155c0a,0xbc843000000000000000,0x482cc0b],#[0x809a0000d0310000000,0x81c3009600000000000,0x0,0x80ef0000000,0x0,0xc174886f0000000,0x0,0xdc139818c00000000000,0x84042074d1,0x447cc47a0000000,0x4896088f816b000,0x5007c1e2000,0x0,0x40000000050404475000,0xc06bc91c00000000812,0x130000000,0x0,0x416100001c450000000,0x400000000d9130000000,0x8e000000000000019,0xeb000,0x50fe10130000000,0x9cd8000000000000000,0x402b5cd300004c91000,0x19d9000000000000000,0xc0000000000000000000,0x41bd000000000000449,0x300000000546e0000000,0xcc484488600004115c56,0x492100000000007,0x0,0x0],#[0x0,0x0,0xcf800000000000,0x3000041d900000000000,0x8c88000001a,0x9f00000000000,0xd0000000000000000000,0x88ba000000000000082,0x0,0x0,0x0,0x80850000000021cf000,0x8467000,0x0,0xc0470000811e0000000,0xc810000000000000000,0x11050000000,0x401c81370000000,0xb0238000000000000000,0x451,0x80cd000,0x90f0e163000,0xc8c500000000000,0x2020b000000000000000,0xc49,0x28920000000000000000,0x80d40000d45ed8d,0x0,0x0,0x8891000000000000000,0xc0000416ec17c4172000,0x81e],#[0x9d6dc1bf0000000,0x919c1d70000889e000,0x0,0x0,0x0,0x0,0x83d000000c4822a000,0x0,0x80000000000000000000,0x650f30000492f01d1596,0x81ef0000401,0x411600000000000,0x0,0x0,0xd0000410900000000000,0xc038423]]
set_option maxRecDepth 32000 in
def g221D8 := limbs80 #[#[0x88210541204405008010,0xfdebfbdbbb7af9fd4250,0x451611199185646fffed,0x99441651298c49631498,0x839888d6224984916120,0x20355941563055881b50,0xe140388c0e13038c80e0,0x88d56238940e15038900,0x5d94d56535d8cd56335d,0x465589956168541a3206,0x5651558c556115595956,0x5156545d852250485411,0x58dd56275585e15075d9,0x55588956125595d56475,0x6185d895f52575495761,0x15629558655658558a15,0x80e7530954c275209548,0x9540e74039500e720394,0x239508e442394c8e7503,0x75239948e55239148e64,0x4e7533954ce66239588e,0xd45a55169505a6653959,0x19d51a55469d49a55269,0x5049d4c655319d446551,0x2451498c5253149d4125,0x85256149d45265149545,0x9995256549d4d2553499,0x379d49e55279d45e5517,0x55159d51e55479d4de55,0x56661595856461599456,0x589646259949655259d8,0x3c01f0009d89666259],#[0xe00c80b50a208907606,0x6514c13812811a1070f9,0x41f21d91b219f1871761,0x2ad28727125b24622821,0x5433a32230d2f62d92c5,0x63df3cc3b539237f3643,0x48447745c44542e41640,0x4e5305144ea4c04a949c,0xe5fa5e05bc5985795625,0x6a468066b65463e62a60,0x9777674c72a7066e56c8,0x38538338127fc7db7c27,0x92f90e8f68d28b289187,0xfd9e19c29b198f97294e,0x8a9ca6fa5ea49a31a1c9,0xb6fb55b3cb13af9ae1ab,0x2dc16bf7be2bc7baeb8b,0x4d25d00cd7cadc78c59c,0xe0ddf1dd4db1d99d69d4,0x15130144000545111210,0x61408841b8581424102,0x1d231a205e0422a11c82,0x17249e0ca22143831603,0x2a626625a6070d191e1f,0x4529288030182d26276a,0x8ea08460fe4c132f5f80,0x137a8a88b7812e6b245f,0x7e22269f004459c0ab78,0xd443690420156702900a,0x9c1297810fc067d12265,0x508833f585011cf811d9,0x80273e0249afe8811978],#[0xdfd0497f4123db014dfd,0x38486bcc0883f92f3023,0x12e444a7e40917f0c48b,0xd7044b423bfb40967c01,0xf8449357c0091c6f02af,0xdc41073d3e01241e224b,0x443fc449bc0111f7201,0xc448c037dd806601efe9,0x6c4209246bad8c30493f,0x8efba2228bece226de2,0x7047bfe9004e77c890fc,0xe6e2261e1788247de56d,0x967110d2d75116f0892,0xe680463f01207e0258f8,0x1be8e0451cecca0489f9,0xe89cff8b920a2bd3e005,0x1197fa42602480fcec,0x5f089aca49593d160f5c,0xda011afe0240f777d13d,0x35f6d9213d7b6ea140cf,0x9a01164fd6408cbc5902,0x918bc90962ee9ac1207f,0xc7e491f7eb0122efd1a0,0x91ff84213cc7e49150c,0x4506de484c66df509cec,0xc2495c904d5c225bfab0,0x643d08e7e8695bc016c,0x5f844b382d4466496f84,0x306df5b1182246fd0089,0x2146fd0122ddb844cd7b,0x96f17113dbc9096b87e1,0x493792096bf7d413d708],#[0x32d13d6a48c3a91b0fa,0x9f9ed24285573fe8f728,0xb3e488c94793e3201824,0x49539e4030488cc340c,0xb1c450af920e17f5d4a1,0x28b7d9e44a539be263fb,0xdc60]]
set_option maxRecDepth 32000 in
def g221H8 := limbs80 #[#[0x60381000020003c200b,0x1e010200002020386402,0x200e030a808700f00018,0x305804050105c0e0e058,0xc140143a1216008001a0,0xf004020113800020,0xc3000000000003000606,0x80010010383824010200,0x1089c40031603c000105,0xb020000a020109c0a02,0x4000906c1a010185454,0xa8020200004100607810,0x800041b0d0080005018,0x109210060309980180f0,0x228000141406048502e0,0x13c1004008060a0282c0,0x8800602198081205060c,0x2004340000000b80706,0x10109800070c000e61a,0x22244a8080a240000400,0xf4003817bd47c0d0000c,0x304c562b120400006038,0x112800180d01828202a0,0x80000008060112830601,0x501909008d052050000,0x68363f0081000170400,0x4800e606098081a3204,0x48080601018340000,0x20d070002212048a818,0x4000708004102a000f4,0x708659008ac004d068,0x58a01800000a81400190],#[0x40000034721c00818600,0xd202f0104c0fb0012910,0x7006e000062a1600904e,0x45138000208f800026d,0x1009900004d0ae0bd000,0x1812f800062fce01260b,0xca1230074e1100a37021,0x8310000010,0x605aa414c093c111e2c,0xc0484d1060a5c039800,0x40a624e2800040a,0x4022e4d3110b40b9800,0x940c660eda09760dd000,0x8286f800000006412c03,0xb212504a0608d611e10f,0x22b8630f8042082,0x74411612b8000682f000,0xc489a20cda079ac6d286,0x5802bc044489c011c206,0x94072000000988000607,0x6862a6bdc10fa06,0xce07c80000827049e000,0x520a90000602f800060f,0x824a966e8e2a0e9376af,0x468006ce80000000406,0xe00004029011b8000000,0xd290f8000232c8000410,0x607500000000083,0xd04e360e400f08000000,0xc401c27150cb0c10262f,0x5602d40ca409cc6a3810,0xa80be4057c82e40d0a50],#[0xe80f700004266602aa4a,0xb0000000000002c0ca0f,0x4a904c04ee4ce8000488,0xaa439a0ea00006f0fc0e,0xa84f88517c6f8a10880b,0xa8a0fa8000485,0x770e84416000060b8000,0xa610348ff00e5ca1244e,0xf80ee800062340000006,0x3c4c6c08e221be4e5a07,0xf082c80000000611888e,0x8e8fa285008f4c00780f,0x8a4e068bee856205680d,0x80000000685b60f260f,0x20cf200c40c680006eb,0x3800020d26002008c000,0x685360e320f7a03b813,0x48f620a8201a412ef10,0xf40be8080ca888000000,0x32417ae29a05d28ef003,0xaa32d8094623ff00fa42,0x6a10a204ae12aa06f213,0xf40fd608de831c09b40a,0xa8424ca34800060f1011,0x6000000000088004bc07,0x6000029112d0f80002ec,0xb00000000408ca217042,0x4800000006067c830a41,0x48000000000000000008,0x5e72262162e2a40a0003,0x1fecdf30cc0000443,0x5e1304ecf80510000000],#[0x88000004500ea800064d,0x36073800000590000612,0xc7039a09c000040a4813,0xe048ea9fae2c64e0807,0x3c05b6909f0d5e112044,0x460b6810600000000208,0x40b88fe403cc11,0x49115c10860ebc0b6000,0xb800026b92027800020f,0x5c05caec3609a602c06a,0x5646aa071046880e7c40,0x268478898e86ba28880a,0xc2aa0008bea3400caa03,0x7c411811ae0ae8000446,0xcc0f500c7a12200006e2,0xec0dee88ac0eb20c2e04,0x7800000000330c4c2805,0x622520008c0da42,0x16090a400413a2421800,0xdcecd0217a4fe69358eb,0x96ccc612142d5802640b,0x4086a09368f9404,0xb002180000863a870800,0x80000000001284010a0c,0xa8a20085b80002e29205,0x40089000020a18000061,0xa60bbacd5e89ae901810,0x320c90138800040aae43,0x3401862df821a2129c07,0xde0e80000000044bd80f,0xd62a7002e6132c6ec642,0x60e260b0612620a1680],#[0x2516727e249dc113800,0xc207600302ed30419007,0x78000412d00004070e13,0xc68f9a0c4c6f08000452,0xee025c018a04b000060a,0xa20318079643c0000400,0x512940910410489b20a,0x9d322eecde0600000000,0x4e05f64a484a9a46a00c,0xba2cc6138000040c0c0d,0x2280c0000000004ce60d,0xd24d0a01e0071c80e44e,0xbf323404a0009a879449,0x2000040870b308000401,0x8e0ee0000000020df641,0xd2a10000042a68861e08,0xa68c98000003b6b1f682,0x4fe2750716204d003,0x212da0cc4023a864000,0xba0c744b700000425800,0x60e2809e800048c9446,0xf0d00044a072c442800,0xe6aac035e0bc210ac13,0x9e0f00c6e6037c12e606,0x3a2a48216e096e617e4b,0xaa0dce22220bca0a7490,0x500fe604d80a7a05004d,0xb0019b0ebe93640e08a3,0xf4110c0e880004236c8f,0xd80042068a10e80d7e01,0x2ee2be8ca428cc6e3405,0x54139410582a3888bc05],#[0x6a07de2e50000000040b,0xcc2b8890aae286053011,0x9880140b3e10380ec402,0x9e616c615ac212b0fa4f,0x106e700e680a34526640,0x180000000012c80c5c04,0xe44d7c0cea092c4a1e00,0xe00abe0d3c054a0b0c07,0x3206bc49ae525209820a,0xa0eb18e28a006800062c,0x66fd40ba26e6205,0x60248a73000024da000,0x28000633602734114800,0x960476ec70ab78000204,0x58000612448d340c2086,0xec016800004228218812,0x38000008300000000207,0xd68fd40566878ace0622,0xea03700430000629fa00,0x90000603280006adfa08,0x480d8206a811764df44b,0x7a4ab22a4612484a882e,0xb2136a11562a964f9432,0xba07d642080000000602,0x4821844d622a00117813,0x9d119081e42bcee6fa13,0xa24af803842a7e0f5a2a,0x4e9e0000411a00b7212,0xa4020806562bb686f000,0x4e868ca6e8000691d208,0xd440480000289641cc6a,0x8ac88dbe4ea0057006],#[0x291d8516e074049c800,0xe8000461660c10000000,0x4e038c225a0b3608f080,0x480002212011de01af10,0xad0ff813200004420223,0xdcb0f2036c050e0d9a8f,0x34013ad0e800060f624e,0xafc08102206416c41,0x6c6ec4d2c4b2800028d,0x51a8000402d800,0x6e49c28f3012b0000000,0xc0053a8f8885e80d04c2,0x2807b411c882a80fc412,0x5acc0a8c8a526d126a0b,0x6c0918000609240acea3,0x2000aa0fbe12f200880d,0x6a8bd20080855a12020b,0xa4813000060a980000ed,0xfa4a82867e857e2d7600,0x7c013087200950858482,0x56040006760af0118204,0xf6484e07a2ec1c13400e,0x8e08660ef00cb80f3829,0x6a4ac202060ce6062602,0x9e09e20d400c300e6002,0xbcece600b40628034013,0x480002219e033c119089,0x6c86102b98000089c801,0x741096719a049e8dc012,0xda4d7605b800000000b2,0x13324e04c4ed800adc03,0x3ae26c13500004801c01],#[0xf80e9a00bc0550418a4a,0x8606d80f180d5a00508f,0x5052a0007001e811ec41,0xee3270b14e82ea0db608,0xf0054210124a22b20806,0x20000609f007be03f880,0xc800052b2c2cec022644,0x4e4198a6d0082e29ec0e,0xc401640036a65e724200,0x2107c0408000606684c,0xeae8d0000204f4508e0e,0x2c0fd80004109a00f402,0x420b88000490004e8893,0xcc11360f9609fc09a84a,0x64015aa1288b3000000c,0x580000a56c0fa6437a13,0x700d181296101a08ae00,0x5602800d9064b4059e07,0xe9103e4e166a76860821,0x5e0cd70ff031560c0492,0x14061e40428d4e00cc11,0x702af00806064a05e64d,0x16a11e0e700236031012,0xc441ac137a055e063ca1,0x3c4b7e052608b650182b,0x8a099a2668000229e627,0x5a33140f288240221405,0xec131a0d70314e0d3652,0x9c10b849fcd038017e03,0x8e2a8ea7ca1218ec5608,0xf82b7c0250000492aa85,0x106960ff80bfc06c811],#[0x2fd80140082680a800,0xb811b010f4899c6a6a10,0x5c0c80af3a0de240ce2b,0xf0000601d800060bb404,0x8c11280e166e4a4b1a07,0x1ca33800044c0aec2e07,0xa283cc11d2127e8be605,0x680e180cf8000000004b,0x9e123c8448000013140f,0x640f820b5c4390267632,0x600006cf780b1e8d44ca,0x291e60846496606,0x5a0b78914000020dc000,0x68000001740ab4041e08,0x5683002624094a120a10,0x40000280fe0c8c859603,0xaa11604a5c030c265e0b,0x14081c00148f740c524b,0xac0e3c80b000068adc11,0x9a13b60a226a5000020d,0x36afcecff001d02b9611,0x8043a015203aeeb2406,0x84a500dfe22080b9610,0xe00ed005fe81f602a110,0xb10c8e,0x760c440da090b0000000,0x4000000782ab70000013,0x7e03664eacec46006648,0x20ef8024249,0xda46b00000095800,0xb4e4d,0xd0000000000004027000],#[0x3a107000026ef800020a,0xf6640800064954215e21,0x1000000000000000020b,0x62a8000064cf0000606,0x300000000210560d5000,0xdae2f4065a0768000603,0x9c40a84988077e897c09,0xe6046c0f40000405c687,0x1800060c1e6aa6122a04,0x42a1e469c01,0x40f9e4ae80000000000,0x38000200380000000000,0x440d289902a2000060a,0x203e000,0x40f80002421000,0xd489824bfa84fe019000,0x7e09000000000606fc10,0x4306820640010409bc08,0x9a8f44135800020ddc6a,0x54477e0464102800e250,0x4a6d80000000000062a,0x4096683d82140904000,0x201cc0a2e852800,0x9000064b1000f8000000,0x160c3a002a860210b00e,0x9e09d24270000701340d,0x403c00000000602,0x9c6ab4e0de4e9006b000,0x60d60021201b0000606,0x3c03d0214a0978000000,0xde4cc800020a440d2a41,0x2212810]]
def g221D9 := limbs80 #[#[0x284409004108220087f,0xd34a91e1389806a1282a,0x1240018202142574ec5b,0x3b00093c4d126288481,0x2f4a021ec0087c803a72,0x80180012f00300024001,0x7]]
def g221H9 := limbs80 #[#[0x2020601390001040004,0x10100081d0512050002,0x131b0302cf024d4a02,0x6a003d010a220200030f,0x913131b10060a290724,0x30021805e2b1f0b580c,0x642766180604625393b9,0x4c44e0216c0a574d6c35,0x9091a058510703ac0310,0x45e06b0029355c1d504,0x132135c10304b1010180,0xd7211c1852771df624d5,0xc000c1b5019656e0540d,0x74b118826ec07c863093,0x4a04a103191f6016d97f,0x3099424a00d6459d1ac0,0x41e5442442501a010703,0xdc001b04b00740000000,0x6991c021240c37711,0xc148076847e01055,0x5bc0d0000c4a921540b,0x4ec448176c8f82565cd8,0x9000326f44da07a44ef2,0x3020c0e3267000000,0x7444e00000006568000,0x14000090401c415502d8,0xd0f4000000000009,0x139c08d243c118000000,0x118c000000107e84cf,0xe50a023d000001300000,0x4651280e4045407805,0x14e01511ab8564168066],#[0x35471049e67281082144,0x40328468077093105c51,0x3b0000000000073dc1c,0xd000000005ee0500003,0xb0000000146b17a00000,0x1ee748d0db134401110,0x9d66a0834067c0bf07d,0x1021418a43ea15c000d,0xa0175d27410099808000,0x44bc17c87784f141e5d2,0x6a418e028dcf955e803a,0x15d300004dd105d01a30,0xc45b072c11317c897055,0x4b0184190065c60406f,0x62025c1e024bc0f80260,0x786e01bb00fc138255d1,0x7f05fd07c40a9673451,0x70458556a518275819ae,0x4415d25d25d34611d390,0x94fd001000055f85f702,0x17f1320089000801a160,0x1357205e000045df405d,0x6425c85e411802c11c8d,0x86f0205264013d247086,0x3fc134000c00e07384de,0xe00000475d6701404570,0x15ae002c0dd027d54817,0x913051c95f2420003113,0x6102b484397540d910ac,0xc14681b2005d97805988,0x7117a03cc02103d95c,0x130d6d35a00030604940],#[0x880b9043415904845e42,0x10]]
def g221D10 (j : Nat) := if j=0 then 0x3f else 0
def g221H10 := limbs80 #[#[0x41b450c20c90050050cf,0xca5460d41150b10,0x322c9465e1b0544134,0xa5400c10000002800066,0xa1d3351f89c000000154,0x301c98750033114800,0x4c00008d060000000062,0x1551200000c081319d70,0x82785020000507200288,0x40f45d24002480000151,0x890481a371e0b3245553,0x89c5041e69]]
def g221L : Nat → Packing
  | 4 => (1,6,6,0,0,0,0,g221D4)
  | 5 => (70,5,6,2818109,102,10,1038,g221D5)
  | 6 => (582,4,6,4915479,121,13,1100,g221D6)
  | 7 => (633,3,6,2228323,103,14,1129,g221D7)
  | 8 => (130,2,6,655370,68,12,1083,g221D8)
  | 9 => (10,1,6,65537,0,8,1039,g221D9)
  | 10 => (1,0,6,0,0,0,0,g221D10)
  | _ => emptyPacking
def g221I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupShort 1 2 0 2 0 0 g221H5
  | 6 => lookupShort 32 331 4 13 7 4 g221H6
  | 7 => lookupShort 260 5309 3 16 10 4 g221H7
  | 8 => lookupShort 291 1433 9 16 10 4 g221H8
  | 9 => lookupShort 72 331 8 14 8 4 g221H9
  | 10 => lookupShort 15 83 6 10 4 4 g221H10
  | _ => fun _ => none
def g221 : Forest := ⟨221,10,fun i => g221Y[i]?.getD (0,0),g221C,g221A,g221L,g221I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g221P4_0 : block g221 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g221B4 : block g221 4 0 1=true := g221P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g221P5_0 : block g221 5 0 70=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g221B5 : block g221 5 0 70=true := g221P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g221P6_0 : block g221 6 0 2=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g221P6_2 : block g221 6 2 36=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g221P6_38 : block g221 6 38 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g221P6_134 : block g221 6 134 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g221P6_230 : block g221 6 230 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g221P6_326 : block g221 6 326 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g221P6_422 : block g221 6 422 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g221P6_518 : block g221 6 518 64=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g221B6 : block g221 6 0 582=true := (@block_merge g221 6 0 230 352 (@block_merge g221 6 0 38 192 (@block_merge g221 6 0 2 36 g221P6_0 g221P6_2) (@block_merge g221 6 38 96 96 g221P6_38 g221P6_134)) (@block_merge g221 6 230 192 160 (@block_merge g221 6 230 96 96 g221P6_230 g221P6_326) (@block_merge g221 6 422 96 64 g221P6_422 g221P6_518)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g221P7_0 : block g221 7 0 7=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g221P7_7 : block g221 7 7 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g221P7_103 : block g221 7 103 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g221P7_199 : block g221 7 199 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g221P7_295 : block g221 7 295 3=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g221P7_298 : block g221 7 298 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g221P7_394 : block g221 7 394 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g221P7_490 : block g221 7 490 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g221P7_586 : block g221 7 586 47=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g221B7 : block g221 7 0 633=true := (@block_merge g221 7 0 295 338 (@block_merge g221 7 0 103 192 (@block_merge g221 7 0 7 96 g221P7_0 g221P7_7) (@block_merge g221 7 103 96 96 g221P7_103 g221P7_199)) (@block_merge g221 7 295 99 239 (@block_merge g221 7 295 3 96 g221P7_295 g221P7_298) (@block_merge g221 7 394 96 143 g221P7_394 (@block_merge g221 7 490 96 47 g221P7_490 g221P7_586))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g221P8_0 : block g221 8 0 13=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g221P8_13 : block g221 8 13 48=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g221P8_61 : block g221 8 61 69=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g221B8 : block g221 8 0 130=true := (@block_merge g221 8 0 13 117 g221P8_0 (@block_merge g221 8 13 48 69 g221P8_13 g221P8_61))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g221P9_0 : block g221 9 0 10=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g221B9 : block g221 9 0 10=true := g221P9_0
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
theorem g221G : graphValid g221 (boundsBefore K207) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low221 : Lower true (varsX 221) (graphGoal 221) 11 := lower_forest (g:=g221) (i:=0) (hints:=33555459) (before_sound K207 V207) g221G g221T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K221 := extendKnown K207 11 [(221,[]),(245,[98,67,83])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V221 : Known true K221 := extend_ok (m:=221) V207 low221 (by decide +kernel)
def g235Y : Array (Bits × Bits) := #[((sampleWord (w80 [0xfe7fc01ff0ff1ffc75,0x77e00001f0000007c1f])),(sampleWord (w80 [0x5229148a242410905,0x77e94a5294a5294a529]))),((sampleWord (w80 [0xffffffe000ffe3ff83,0xf5420003e0003e0f83e0])),(sampleWord (w80 [0x8030180c404081023,0xb5401084210842108421]))),(0x0,0x0),((sampleWord (w80 [0x7fffffff0003fff2,0x1a4007c0007c1f003ff])),(sampleWord (w80 [0x100402010008002000,0x2108421084210842]))),(0x0,0x0),((sampleWord (w80 [0x7ffffffffffc000c,0x16000f8000f801fffc00])),(sampleWord (w80 [0x200804020010004000,0x4210842108421084]))),((sampleWord (w80 [0xff800000000000000d,0x6897f00000fffe000000])),(sampleWord (w80 [0x4030180c086091824c,0x48968421084210842108]))),(0x8859ffffff0000000000,(sampleWord (w80 [0x804020100080020000,0x10842108421084210]))),(0x0,0x0)]
def g235C : List ColumnInfo := [(1,0,234,0,10)]
def g235A : List (List Nat) := [[],[117],[83],[83,115],[115,83],[115],[97],[97,117],[97,83],[97,83,115],[97,115,83],[97,115]]
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
theorem low235 : Lower true (varsX 235) (graphGoal 235) 11 := lower_forest (g:=g235) (i:=0) (hints:=16777267) (before_sound K221 V221) g235G g235T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K235 := extendKnown K221 11 [(235,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V235 : Known true K235 := extend_ok (m:=235) V221 low235 (by decide +kernel)
def g238Y : Array (Bits × Bits) := #[(0x0,0x0),((sampleWord (w80 [0xf87ffe01ff8fffffe4,0x13c7300000f8000f83ff])),(sampleWord (w80 [0x110014140520200420,0x11c13084210842108421]))),((sampleWord (w80 [0xff87fffe000ff1fe09,0x4badd0001f0001f00000])),(sampleWord (w80 [0xa01158185641444889,0x4badd39ce739ce739ce7]))),((sampleWord (w80 [0x7fffffff001ffc7,0xaa986003e0003e007c1f])),(sampleWord (w80 [0xc22060201801881007,0x82184108421084210842]))),(0x0,0x0),((sampleWord (w80 [0x7fffffffffe0012,0x6c4f807c0007c0007fe0])),(sampleWord (w80 [0x44180406002006110,0x6c068210842108421084]))),((sampleWord (w80 [0xfff800000000000029,0x84009f800007ffff8000])),(sampleWord (w80 [0x200808004008000,0x421084210842108]))),((sampleWord (w80 [0x10,0x51304ffffff800000000])),(sampleWord (w80 [0x401010008010000,0x842108421084210]))),(0x0,0x0)]
def g238C : List ColumnInfo := [(4,0,234,0,10)]
def g238A : List (List Nat) := [[],[118],[83],[83,118],[49],[49,118],[49,81],[49,81,118],[81,49],[81,49,118],[81],[81,118]]
def g238D10 (j : Nat) := if j=0 then 0x7f else 0
def g238L : Nat → Packing
  | 10 => (1,0,1,0,0,0,0,g238D10)
  | _ => emptyPacking
def g238I (_ _ : Nat) : Option (Nat × Nat) := none
def g238 : Forest := ⟨238,10,fun i => g238Y[i]?.getD (0,0),g238C,g238A,g238L,g238I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g238P10_0 : block g238 10 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g238B10 : block g238 10 0 1=true := g238P10_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g238T : checkedTables g238 10 := by
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
  · exact (rfl : block g238 8 0 0 = true)
  · exact (rfl : block g238 9 0 0 = true)
  · exact g238B10
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g238G : graphValid g238 (boundsBefore K235) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low238 : Lower true (varsX 238) (graphGoal 238) 11 := lower_forest (g:=g238) (i:=0) (hints:=286266928) (before_sound K235 V235) g238G g238T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K238 := extendKnown K235 11 [(238,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V238 : Known true K238 := extend_ok (m:=238) V235 low238 (by decide +kernel)
def g250Y : Array (Bits × Bits) := #[(0x0,0x0),((sampleWord (w80 [0xfffc01ffffe1ffffba,0xc261b0000007c00f83ff])),(sampleWord (w80 [0x482402024400209a,0x42011004210842108421]))),(0x0,0x0),((sampleWord (w80 [0x1ffffe00fffe1fff25,0x3c4b188000f801f07c1f])),(sampleWord (w80 [0x409008140480404021,0x1c420808421084210842]))),((sampleWord (w80 [0x1fffffff00001ff058,0xf5694e001f0000000000])),(sampleWord (w80 [0x8ae1309857088a8258,0xf5694e3def7bdef7bdef]))),((sampleWord (w80 [0x1fffffffffffe00010,0xaa846f83e0003e007fe0])),(sampleWord (w80 [0x30040201800030400,0xa0046390842108421084]))),((sampleWord (w80 [0xe0000000000000000e,0x11ba877c00003fff8000])),(sampleWord (w80 [0xc0180c060110c0804,0x1b88421084210842108]))),((sampleWord (w80 [0xc1,0x4514407fffffc0000000])),(sampleWord (w80 [0x100201008000100000,0x42108421084210]))),(0x0,0x0)]
def g250C : List ColumnInfo := [(16,0,234,0,10)]
def g250A : List (List Nat) := [[],[101],[83],[83,99],[99,83],[99],[49],[49,101],[49,81],[49,81,97],[49,97,81],[49,97],[81,49],[81,49,99],[81],[81,97],[81,99],[81,99,49],[97,49,83],[97,49],[97,81],[97],[97,83,49],[97,83]]
def g250D10 (j : Nat) := if j=0 then 0x7f else 0
def g250L : Nat → Packing
  | 10 => (1,0,1,0,0,0,0,g250D10)
  | _ => emptyPacking
def g250I (_ _ : Nat) : Option (Nat × Nat) := none
def g250 : Forest := ⟨250,10,fun i => g250Y[i]?.getD (0,0),g250C,g250A,g250L,g250I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g250P10_0 : block g250 10 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g250B10 : block g250 10 0 1=true := g250P10_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g250T : checkedTables g250 10 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g250 0 0 0 = true)
  · exact (rfl : block g250 1 0 0 = true)
  · exact (rfl : block g250 2 0 0 = true)
  · exact (rfl : block g250 3 0 0 = true)
  · exact (rfl : block g250 4 0 0 = true)
  · exact (rfl : block g250 5 0 0 = true)
  · exact (rfl : block g250 6 0 0 = true)
  · exact (rfl : block g250 7 0 0 = true)
  · exact (rfl : block g250 8 0 0 = true)
  · exact (rfl : block g250 9 0 0 = true)
  · exact g250B10
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g250G : graphValid g250 (boundsBefore K238) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low250 : Lower true (varsX 250) (graphGoal 250) 11 := lower_forest (g:=g250) (i:=0) (hints:=286724144) (before_sound K238 V238) g250G g250T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K250 := extendKnown K238 11 [(250,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V250 : Known true K250 := extend_ok (m:=250) V238 low250 (by decide +kernel)
def g127Y : Array (Bits × Bits) := #[((sampleWord (w80 [0xdb5234b66000000000,0xff00ff00ff300801c])),(sampleWord (w80 [0x9b5034a06414141414,0x14141414141411000008]))),((sampleWord (w80 [0x8f6559482000000ff0,0xff000000ff0002105fb])),(sampleWord (w80 [0x8b6019482050505050,0x505050505050500005fa]))),((sampleWord (w80 [0x1b10894360000ff000,0xff0000000587a05])),(sampleWord (w80 [0x1b1089436131313131,0x31313131313130082a05]))),((sampleWord (w80 [0x226e4444800ff0000f,0xf00000000ffff8866347])),(sampleWord (w80 [0xe400480a0a0a0a0,0xa0a0a0a0a0a0a0026205]))),((sampleWord (w80 [0x75af08991000000000,0xffff00003187018])),(sampleWord (w80 [0x64af00181acacacaca,0xcacacacacacac2105010]))),((sampleWord (w80 [0x4899322a1ff000000f,0xfffff00000000c1f8c60])),(sampleWord (w80 [0x408102020303030303,0x30303030303001d8800]))),((sampleWord (w80 [0xa4808320fffffffff0,0xfe00f80])),(sampleWord (w80 [0x240000201c0c0c0c0c,0xc0c0c0c0c0c07e00000]))),(0x0,0x0),(0x0,0x0)]
def g127C : List ColumnInfo := [(1,0,126,0,10),(2,0,125,0,10),(4,0,123,0,10),(0,16,106,5,9),(8,0,119,0,9),(16,0,111,0,9),(32,0,95,0,9),(64,0,63,0,8),(0,4,43,80,7),(66,0,61,0,7),(40,0,87,0,5),(72,0,55,0,5),(96,0,31,0,5),(41,0,86,0,4)]
def g127A : List (List Nat) := [[],[83]]
def g127D6 := limbs80 #[#[0xe61761d953e45761d953,0x5d9811d9535d9801d953,0xe4f815d563e4f815d953,0xae3cd55d35cd5cb5c3d,0xac5cac1d091cc01d4bbd,0x1a606102003cb57cb49c,0x20000000064e7]]
def g127D7 := limbs80 #[#[0x1d9536007654d761d953,0x54d6558d531d96354d81,0xe0d7654f815d953e1563,0x5d563e0d6558d879d953,0x6b3f63ec3fe0d7558f81,0xadf3ee3fc7d8f6dbdb6b,0xfbaf57e7bcdf7aed7d7b,0x5d88ebb08d91323207e5,0x2dd965bb207918073006,0xcde0d91cc03f9102d307,0xcece15d3bb3379367eec,0x2ccfe59a3c9b4783676e,0x6eb29e4605c8c438574f,0x5f2d4de4e97c353783a9,0xb851228cc4210002b86b,0x2180b353a6922893e1bc,0x848a290b81bddd6df6b3,0xe017e7e36eb155a953e9,0x4c0f0d881833e41a62e1,0xe20a700b4803c848ccc9,0x3e4748500cf1056e014,0xd61321cb080402683561,0x100b21b213210086c201,0x90990990b6c29b096c20,0x590d]]
def g127H7 := limbs80 #[#[0x34d800000000c0000,0xb800000000200250,0x48000000000,0x5e1000000]]
def g127D8 := limbs80 #[#[0x9d9535d95358d531d953,0x9fe7dd95635d56359563,0xddf3fbfefebf6fbbdebf,0xff7f7f5fbfedf97dff7d,0xb17f0a5eb29070298b29,0x8c102b020cc006eec5a3,0xc87c1a2f028343842ec0,0x6ecc6c1b4f0695c0a46e,0xd150f9bc1c1f0702c3b4,0xc1a8f02a1bb1170d4bc0,0x61c1d8f034ec3b5eeca1,0x80460bc17000fc35770d,0x1528430f8358b82687a1,0x2df6755c469d935ed625,0x8ecdae6a5a3e7093a2c8,0xe4e7cb8f0ca719c26f8b,0x1629a224199ab0a17d4b,0x6460c8d669c9d70b4c21,0x440e7e40228c6ce1e383,0xf9c01dbf70073f2010f7,0x209eff002277bdbd8087,0x1dd5018bfd020293fe8,0x63c36013bdee8821ffb4,0x804eff008f7440f7b802,0x70073cfac01434018fa4,0x283ff30009cff36004ed,0xa7d4c6fff58022ff6608,0xba6495b73184f126d8a1,0x1d6a1d711d711cad0a]]
def g127H8 := limbs80 #[#[0x800068000000060f8448,0x2600006cf,0x59280b0,0x308018b000000000000,0xdc8828a8000025680000,0x400000006e158000040,0x6a2d004580000040800,0xe8380032c00000000078,0x50169274980448001802,0x6b8000006]]
def g127D9 := limbs80 #[#[0x9633fff7dfdff6358d53,0x758dd5765559537605d8,0x57595f7639d8d7631d81,0x82c91c6a250a803dd5d7,0xc7080b9d9cb852a48f46,0xd51842ca1d7996935cf2,0x10800e800ee60089cc4,0x6b002d8008000ec00430,0x60029ac0094801290024,0xb4012fbc004bd]]
def g127H9 := limbs80 #[#[0x4001a45454084000a000,0xc641d13c880188000001,0xcda7d2909c60033c8487,0x60400000b8000103,0x150e00001d0ec000a6,0x4a9e164800117984ef31,0x2e1cb5866a42a100006c,0x6800002e]]
def g127D10 := limbs80 #[#[0x45c5c03ff63ff58ffd53,0xd5992518107accc49460,0x6acc928c0e41e]]
def g127H10 := limbs80 #[#[0x26ba8a510010000262a,0x6e000a8380cb0f080014,0xb1]]
def g127D11 (j : Nat) := if j=0 then 0xc8a64203ff else 0
def g127H11 (j : Nat) := if j=0 then 0x58000a970000 else 0
def g127L : Nat → Packing
  | 6 => (8,5,4,393222,51,6,1025,g127D6)
  | 7 => (30,4,4,1245196,84,9,1044,g127D7)
  | 8 => (33,3,4,1179655,83,10,1058,g127D8)
  | 9 => (14,2,4,262147,34,9,1042,g127D9)
  | 10 => (3,1,4,0,0,7,0,g127D10)
  | 11 => (1,0,4,0,0,0,0,g127D11)
  | _ => emptyPacking
def g127I : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupShort 2 47 0 6 3 1 g127H7
  | 8 => lookupShort 9 97 3 8 5 1 g127H8
  | 9 => lookupShort 10 59 6 9 6 1 g127H9
  | 10 => lookupShort 4 23 2 7 4 1 g127H10
  | 11 => lookupShort 1 11 0 5 2 1 g127H11
  | _ => fun _ => none
def g127 : Forest := ⟨127,11,fun i => g127Y[i]?.getD (0,0),g127C,g127A,g127L,g127I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P6_0 : block g127 6 0 8=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g127B6 : block g127 6 0 8=true := g127P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7_0 : block g127 7 0 6=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7_6 : block g127 7 6 24=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g127B7 : block g127 7 0 30=true := (@block_merge g127 7 0 6 24 g127P7_0 g127P7_6)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8_0 : block g127 8 0 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8_2 : block g127 8 2 22=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8_24 : block g127 8 24 9=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g127B8 : block g127 8 0 33=true := (@block_merge g127 8 0 2 31 g127P8_0 (@block_merge g127 8 2 22 9 g127P8_2 g127P8_24))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P9_0 : block g127 9 0 7=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P9_7 : block g127 9 7 7=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g127B9 : block g127 9 0 14=true := (@block_merge g127 9 0 7 7 g127P9_0 g127P9_7)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P10_0 : block g127 10 0 3=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g127B10 : block g127 10 0 3=true := g127P10_0
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
  · exact g127B6
  · exact g127B7
  · exact g127B8
  · exact g127B9
  · exact g127B10
  · exact g127B11
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127G : graphValid g127 (boundsBefore K250) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low127 : Lower true (varsX 127) (graphGoal 127) 12 := lower_forest (g:=g127) (i:=0) (hints:=16778291) (before_sound K250 V250) g127G g127T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K127 := extendKnown K250 12 [(127,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V127 : Known true K127 := extend_ok (m:=127) V250 low127 (by decide +kernel)
def g191Y : Array (Bits × Bits) := #[((sampleWord (w80 [0x2af90d90ae18042800,0xfe0007f01fc07f])),(sampleWord (w80 [0x227801902608042810,0x20408102040810204081]))),((sampleWord (w80 [0x351561bb02231a3800,0x7f0003f800003f80])),(sampleWord (w80 [0x351121ba02011a2850,0xa142850a142850a14285]))),((sampleWord (w80 [0xc3ba79c203c0dd1000,0x3f800000000fe00000])),(sampleWord (w80 [0x83ba49c202c0dd1132,0x64c993264c993264c993]))),((sampleWord (w80 [0xc406c8995858acc000,0x1fc00001fc0000003fff])),(sampleWord (w80 [0xc006c8011810a080a1,0x42850a142850a142850a]))),((sampleWord (w80 [0x5215362ae9a4a1880f,0xe000000000000fffc000])),(sampleWord (w80 [0x50053628c9242082c5,0x8b162c58b162c58b162c]))),((sampleWord (w80 [0x9ca1724506341f7f0,0x1fffff0000000])),(sampleWord (w80 [0x88016044062415306,0xc183060c183060c1830]))),(0x0,0x0),((sampleWord (w80 [0xb020824406047207ff,0xfffffffe000000000000])),(sampleWord (w80 [0x408,0x10204081020408102040]))),(0x0,0x0)]
def g191C : List ColumnInfo := [(1,0,190,0,11)]
def g191A : List (List Nat) := [[],[83]]
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
theorem low191 : Lower true (varsX 191) (graphGoal 191) 12 := lower_forest (g:=g191) (i:=0) (hints:=1075) (before_sound K127 V127) g191G g191T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K191 := extendKnown K127 12 [(191,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V191 : Known true K191 := extend_ok (m:=191) V127 low191 (by decide +kernel)
def g223Y : Array (Bits × Bits) := #[((sampleWord (w80 [0x23b30db0ae1b440800,0xfe0000001fc07f])),(sampleWord (w80 [0x23b20590260b440912,0x24489122448912244891]))),((sampleWord (w80 [0x3c55619b02231b1800,0x7f000007f0003f80])),(sampleWord (w80 [0x3451219a02211a1850,0xa142850a142850a14285]))),((sampleWord (w80 [0xc3b879c203c09c3000,0x3f800003f80fe00000])),(sampleWord (w80 [0x82b049c202c09c3030,0x60c183060c183060c183]))),((sampleWord (w80 [0xc406c8995858acc000,0x1fc00001fc0000003fff])),(sampleWord (w80 [0xc004c8011850a080a1,0x42850a142850a142850a]))),((sampleWord (w80 [0x5215362ae9a4a1880f,0xe000000000000fffc000])),(sampleWord (w80 [0x50053228c9242182c5,0x8b162c58b162c58b162c]))),(0x0,0x0),((sampleWord (w80 [0x9ca1724506341f7f0,0x1fffff0000000])),(sampleWord (w80 [0x90a16244002414306,0xc183060c183060c1830]))),((sampleWord (w80 [0xb020824406047207ff,0xfffffffe000000000000])),(sampleWord (w80 [0x408,0x10204081020408102040]))),(0x0,0x0)]
def g223C : List ColumnInfo := [(2,0,221,0,11)]
def g223A : List (List Nat) := [[],[32,99]]
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
theorem low223 : Lower true (varsX 223) (graphGoal 223) 12 := lower_forest (g:=g223) (i:=0) (hints:=16778291) (before_sound K191 V191) g223G g223T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K223 := extendKnown K191 12 [(223,[]),(247,[83])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V223 : Known true K223 := extend_ok (m:=223) V191 low223 (by decide +kernel)
def g239Y : Array (Bits × Bits) := #[((sampleWord (w80 [0xfc03fed580945955ca,0xa0000003e00000007c1f])),(sampleWord (w80 [0x485852c580145855c2,0xa25294a5294a5294a529]))),((sampleWord (w80 [0xfffc01eb1610463481,0xd000007c00003e0f83e0])),(sampleWord (w80 [0x909099e90010043481,0xd0421084210842108421]))),((sampleWord (w80 [0x9dee9b8ce003,0x88000f800007c0000000])),(sampleWord (w80 [0xe0e0e099ee9b8ce003,0x81ce739ce739ce739ce7]))),((sampleWord (w80 [0xfffffc2064f72202eb,0x1f00000f801f003ff])),(sampleWord (w80 [0x64e1020208,0x842108421084210842]))),(0x0,0x0),((sampleWord (w80 [0x115b023d8614,0x303e00001f0001fffc00])),(sampleWord (w80 [0x10100101a02218014,0x1084210842108421084]))),((sampleWord (w80 [0x34ea124c08824,0xafc000001ffffe000000])),(sampleWord (w80 [0x20202060104400820,0x2a108421084210842108]))),((sampleWord (w80 [0x2800849007910,0x47ffffffe00000000000])),0x4210842108421084210),(0x0,0x0)]
def g239C : List ColumnInfo := [(1,0,238,0,11)]
def g239A : List (List Nat) := [[],[83]]
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
theorem low239 : Lower true (varsX 239) (graphGoal 239) 12 := lower_forest (g:=g239) (i:=0) (hints:=16778803) (before_sound K223 V223) g239G g239T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K239 := extendKnown K223 12 [(239,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V239 : Known true K239 := extend_ok (m:=239) V223 low239 (by decide +kernel)
def g251Y : Array (Bits × Bits) := #[((sampleWord (w80 [0x6764100472c4000000,0x3f800000000fffc07f])),(sampleWord (w80 [0x2240100470c4448912,0x24489122448912244891]))),((sampleWord (w80 [0x81081ecda070000000,0x1fc00001fc07f0003f80])),(sampleWord (w80 [0x100040da0700c1830,0x60c183060c183060c183]))),(0x0,0x0),((sampleWord (w80 [0x3087a5c03a0200000f,0xe00000fe03f800003fff])),(sampleWord (w80 [0x100621c00a00102040,0x81020408102040810204]))),((sampleWord (w80 [0x512dcc7a88e80007f0,0x1fc000])),(sampleWord (w80 [0x512dcc7a8828b972e5,0xcb972e5cb972e5cb972e]))),((sampleWord (w80 [0x5cd0cb21810c03f800,0x7f0003ffffe00000])),(sampleWord (w80 [0x4c90ca000008204081,0x2040810204081020408]))),((sampleWord (w80 [0xaa4930220d2bfc0000,0x7ffffc0000000000])),(sampleWord (w80 [0xa24910220502c18306,0xc183060c183060c1830]))),((sampleWord (w80 [0x212401e4411ffffff,0xffff8000000000000000])),(sampleWord (w80 [0x1020408,0x10204081020408102040]))),(0x0,0x0)]
def g251C : List ColumnInfo := [(1,0,250,0,11)]
def g251A : List (List Nat) := [[],[83],[97],[97,83]]
def g251D11 (j : Nat) := if j=0 then 0xff else 0
def g251L : Nat → Packing
  | 11 => (1,0,1,0,0,0,0,g251D11)
  | _ => emptyPacking
def g251I (_ _ : Nat) : Option (Nat × Nat) := none
def g251 : Forest := ⟨251,11,fun i => g251Y[i]?.getD (0,0),g251C,g251A,g251L,g251I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P11_0 : block g251 11 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g251B11 : block g251 11 0 1=true := g251P11_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251T : checkedTables g251 11 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g251 0 0 0 = true)
  · exact (rfl : block g251 1 0 0 = true)
  · exact (rfl : block g251 2 0 0 = true)
  · exact (rfl : block g251 3 0 0 = true)
  · exact (rfl : block g251 4 0 0 = true)
  · exact (rfl : block g251 5 0 0 = true)
  · exact (rfl : block g251 6 0 0 = true)
  · exact (rfl : block g251 7 0 0 = true)
  · exact (rfl : block g251 8 0 0 = true)
  · exact (rfl : block g251 9 0 0 = true)
  · exact (rfl : block g251 10 0 0 = true)
  · exact g251B11
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251G : graphValid g251 (boundsBefore K239) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low251 : Lower true (varsX 251) (graphGoal 251) 12 := lower_forest (g:=g251) (i:=0) (hints:=16777267) (before_sound K239 V239) g251G g251T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K251 := extendKnown K239 12 [(251,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V251 : Known true K251 := extend_ok (m:=251) V239 low251 (by decide +kernel)
def g253Y : Array (Bits × Bits) := #[((sampleWord (w80 [0x9b01000000001fc000,0x3fc03fffd056c3cc])),(sampleWord (w80 [0xb0142850a14284848,0x4848484848485042c10c]))),(0x0,0x0),((sampleWord (w80 [0xe08c0000000fe00000,0x3fc0003fc0000060fc8c])),(sampleWord (w80 [0xa088162c58b162c2c2,0xc2c2c2c2c2c2c040548c]))),((sampleWord (w80 [0x6220000007f000003f,0xc03fc000003fc18900d7])),(sampleWord (w80 [0x60200c183060c18181,0x818181818181808900c1]))),((sampleWord (w80 [0x70760003f800000000,0x3fffc0220e0f30])),(sampleWord (w80 [0x5076a952a54a951515,0x151515151515200c0a30]))),((sampleWord (w80 [0x956b01fc0000003fc0,0x3fffc000000400002b])),(sampleWord (w80 [0x904a3060c183060606,0x6060606060600000002]))),((sampleWord (w80 [0x506fe000000003fff,0xffc000000000380ff030])),(sampleWord (w80 [0x504c183060c181818,0x1818181818183006a030]))),((sampleWord (w80 [0x8d8ffffffffffc000,0x3ff00000])),(sampleWord (w80 [0x2020,0x2020202020200f300000]))),(0x0,0x0)]
def g253C : List ColumnInfo := [(8,0,245,0,11),(32,0,221,0,11),(1,0,252,0,10),(4,0,249,0,10),(16,0,237,0,10),(64,0,189,0,10),(128,0,125,0,10),(5,0,248,0,8),(65,0,188,0,8),(68,0,185,0,8),(80,0,173,0,8),(0,4,41,208,7),(0,16,104,133,7),(21,0,232,0,7),(84,0,169,0,7),(129,0,124,0,7),(132,0,121,0,7),(144,0,109,0,7),(192,0,61,0,7),(1,16,104,132,6),(16,4,41,192,6),(64,4,41,144,6),(128,4,41,80,6),(128,16,104,5,6),(69,0,184,0,5),(81,0,172,0,5),(129,16,104,4,5),(145,0,108,0,5),(192,4,41,16,5),(196,0,57,0,5),(133,0,104,0,4),(133,16,104,0,4)]
def g253A : List (List Nat) := [[],[83],[96,66],[96,66,83]]
def g253D8 := limbs80 #[#[0x59510595614416154110,0x541815815058d604c187,0x60375587835c56060576,0x1edbce71dcef7dabbc77,0x99856393e39351753565,0x72482200d75c793ab93,0xc248886f87c14304d0a,0x358b4dc245a342188d2f,0x3c963dc96309c1e1e0fe,0x4700344da48f35323465,0xff0031f9c063ce031fc0,0xff02800bf605007d8133,0x7]]
def g253D9 := limbs80 #[#[0x59510585105811054110,0x59530581305d9105d510,0x5855058150585315d930,0x5cd605c56058d605d950,0xdd560dcd60dc5605d560,0x9fe77dd561dc1615c161,0xdf777d7effbfafdbdedf,0xf7bbfefbbdedbb5dff7e,0x1a5ab1981c197ffffbfc,0x3014bb022b2824b0818b,0xa89cb288bc2854ba84ac,0x3102c38ceba8c9c08d2b,0xa83c2a03c2951c1943c,0x1b83c0b05c2adeb1a8bc,0x1cc2c0cc2c2c82c2c47c,0x2842c0582c2d47c1d02c,0x1aa6c0a96c39e6c29a6c,0xab56bab97c0b16c0b26c,0xc28c0c0dc0c16babe0b,0xe14c214328470480029c,0xd05249b91d21e3dc6b0b,0x868fb9e43946c0c897a2,0x1702ca54ca413d25a474,0x2bab720d9da8338640c0,0xba91f1de26c2880afa1e,0x35285c40e2686c6f070c,0x2b28b0a8433630d0607d,0x24383088a61478f8da47,0x499280726618e8c29318,0xc8b884851e2a2980992a,0x1deb8140f3214c889520,0x461efa0114723940239e],#[0x5cc04d3e3600469fd880,0xf700976b5d008cf7b00d,0xf00451b018fd60266012,0x839c0467cf00c36034f8,0x1dda029e3804c7c60130,0x2008a37fc008b3efa201,0xc02bef00abf99808a3ff,0x22add80c19f896052bf,0x313c812f6380032afdce,0x9f8f040120de012bdec0,0xfe10273f98096fe50130,0x36fd4f80463fc0813179,0x947d635600481feab002,0xf0a8806f03511d20fa40,0x48]]
def g253H9 := limbs80 #[#[0x14067000000001c0000,0x63238000000000000,0x414c00000840000000,0x44000]]
def g253D10 := limbs80 #[#[0xf7f7f58560541314c110,0xac222c022a03fffefefd,0x2ec52c662c042ec02ea1,0x6e70ac706e302ece2c0c,0xac746e142ec9ac286eb0,0xac2eaca6aca06eb46e74,0xae76ae16aeb2ae72ae32,0x6914c3608412002aeb6,0x11d418e8344bd2ac911e,0x9d26d59b6296c559454d,0x61a3277986468ae0b7a,0x8b253440e23953101e37,0x20c4c496cc68d8c4a14a,0x390067e010e9f6120e0,0x88033f0010179c0277c4,0xa03ba00c7f8804bfd601,0xff0053f84009dff8028e,0xf8025340332018cf012b,0x36fa008ae8053f86009e,0x1fdc802873dc06be8781,0x1f4073fe60117ff0004e,0xfe1a409dcd00eff0033f,0x1]]
def g253H10 := limbs80 #[#[0xc54403b83858c0020002,0x3a4ca10d0028b22400,0x101f21b0800393c7000,0x205000008840083e17,0x1870000086c008488a,0xc611900384655a349800,0x23000c9d2a0000000116,0x31449301030008a620,0x80b09c7400c40000001e,0x2e0e42b070011101a23,0x6b8d04d00000a088a25,0x40c00]]
def g253D11 := limbs80 #[#[0x31ff583fd50ff4c3fd10,0x5c6a272482400ff587fd,0x2069a58603459a582134,0x4f0a51a084d1e498d821,0xce1a180d1c680e84d1,0x1]]
def g253H11 := limbs80 #[#[0x38110007098001,0x1920000000000040000,0x100000000,0x5f8c000045a1c98000,0x2a82c00000,0x8000,0x40000a381000000021c0,0x339940026926000046,0x30300244018fe7,0x9ab000000000054001b,0xa88a4643401484280087,0x1960083001]]
def g253D12 (j : Nat) := if j=0 then 0x3148310023ff else 0
def g253H12 := limbs80 #[#[0x62018f013a0972210001,0x7522000]]
def g253L : Nat → Packing
  | 8 => (8,4,5,458760,51,8,1054,g253D8)
  | 9 => (43,3,5,1376279,85,11,1080,g253D9)
  | 10 => (29,2,5,393222,51,10,1054,g253D10)
  | 11 => (6,1,5,0,0,8,0,g253D11)
  | 12 => (1,0,5,0,0,0,0,g253D12)
  | _ => emptyPacking
def g253I : Nat → Nat → Option (Nat × Nat)
  | 9 => lookupShort 2 37 0 7 3 2 g253H9
  | 10 => lookupShort 14 83 5 10 6 2 g253H10
  | 11 => lookupShort 9 101 3 9 5 2 g253H11
  | 12 => lookupShort 2 17 1 7 3 2 g253H12
  | _ => fun _ => none
def g253 : Forest := ⟨253,12,fun i => g253Y[i]?.getD (0,0),g253C,g253A,g253L,g253I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P8_0 : block g253 8 0 4=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P8_4 : block g253 8 4 4=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g253B8 : block g253 8 0 8=true := (@block_merge g253 8 0 4 4 g253P8_0 g253P8_4)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P9_0 : block g253 9 0 3=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P9_3 : block g253 9 3 27=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P9_30 : block g253 9 30 11=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P9_41 : block g253 9 41 2=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g253B9 : block g253 9 0 43=true := (@block_merge g253 9 0 30 13 (@block_merge g253 9 0 3 27 g253P9_0 g253P9_3) (@block_merge g253 9 30 11 2 g253P9_30 g253P9_41))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P10_0 : block g253 10 0 20=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P10_20 : block g253 10 20 9=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g253B10 : block g253 10 0 29=true := (@block_merge g253 10 0 20 9 g253P10_0 g253P10_20)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P11_0 : block g253 11 0 6=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g253B11 : block g253 11 0 6=true := g253P11_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P12_0 : block g253 12 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g253B12 : block g253 12 0 1=true := g253P12_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253T : checkedTables g253 12 := by
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
  · exact g253B8
  · exact g253B9
  · exact g253B10
  · exact g253B11
  · exact g253B12
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253G : graphValid g253 (boundsBefore K251) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low253 : Lower true (varsX 253) (graphGoal 253) 13 := lower_forest (g:=g253) (i:=0) (hints:=33555459) (before_sound K251 V251) g253G g253T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K253 := extendKnown K251 13 [(253,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V253 : Known true K253 := extend_ok (m:=253) V251 low253 (by decide +kernel)
def g254Y : Array (Bits × Bits) := #[(0x0,0x0),((sampleWord (w80 [0x4c2000000001fc0000,0x3fc03fc03fc03049ccf])),(sampleWord (w80 [0x4c00a142850a141414,0x141414141414010008c5]))),((sampleWord (w80 [0xbe00000000fe000003,0xfc000003fc000c0b03f0])),(sampleWord (w80 [0x2e0264c993264c4c4c,0x4c4c4c4c4c4c04090150]))),((sampleWord (w80 [0x200000007f000003fc,0x3fc0003fc3030e30e])),(sampleWord (w80 [0x200142850a14282828,0x28282828282810102308]))),((sampleWord (w80 [0xc170003f8000000000,0x3fc00400303f1])),(sampleWord (w80 [0xc17d9b366cd9b1b1b1,0xb1b1b1b1b1b0000202a1]))),((sampleWord (w80 [0x46101fc0000003fc00,0x3fffc000180c3fc00])),(sampleWord (w80 [0x2160c183060c0c0c0,0xc0c0c0c0c0c080435000]))),((sampleWord (w80 [0xb1bfe000000003ffff,0xfffc0000000200fc0001])),(sampleWord (w80 [0x91a810204081010101,0x1010101010000a40000]))),((sampleWord (w80 [0xbcffffffffffc0000,0x3ff000000])),(sampleWord (w80 [0x20202,0x202020202036a000000]))),(0x0,0x0)]
def g254C : List ColumnInfo := [(4,0,250,0,11),(16,0,238,0,11),(64,0,190,0,11),(2,0,252,0,10),(8,0,246,0,10),(32,0,222,0,10),(128,0,126,0,10),(10,0,244,0,7),(34,0,220,0,7),(40,0,214,0,7),(130,0,124,0,7),(136,0,118,0,7),(160,0,94,0,7),(42,0,212,0,5),(138,0,116,0,4),(162,0,92,0,4),(168,0,86,0,4)]
def g254A : List (List Nat) := [[],[83],[49],[49,81],[81,49],[81]]
def g254D6 := limbs80 #[#[0x85e2a5d9746098059120,0x191321]]
def g254D7 := limbs80 #[#[0x65162501205916250120,0x5d180591206496458120,0xe4187591206098059120,0xe41845d920e41865d120,0xaaf2eeeaebae7ad7acfa,0xbb48ba4cba2cc31cd38f,0xc973c965c951c95abb36,0xf967b93dfb556787803,0x12830300b02007036449,0x4b91070430ca5d10875,0x180b018b089a1004012d]]
def g254H7 (j : Nat) := if j=0 then 0x4 else 0
def g254D8 := limbs80 #[#[0x50120589404814250120,0x48164581205896048176,0x5d964481745912061160,0x5912061d644818059120,0x481765d120e1d6448287,0x5d162581845d92061974,0xfab7d3f9fd1fd845c960,0x7d6bacfd7fafd5eeb775,0x77eedfdbbb573ae5fbfb,0xff5fbbf57bef75ebbd5,0x3530c19ac817eec07aec,0x1baec05708376e8372e8,0x38728237282ab0c1bb28,0x5a2e84ab244ab083aae8,0x96f2876aec65b0483f24,0xa1b28a4f2090f2091f28,0xe1f28c0b20b0330a132c,0x8b32e4cb3012f24f2720,0xd672098f289b2ec8c2e8,0x472109720e4720e9720,0xb83085007b0c010c1100,0x6e0ce1792bc4ec8e0fd1,0xd5f2a04fc941122013bc,0xd39d6fed719cb165f0b7,0x618a50f214c157f2f81d,0x88c1f83c3e292d20636c,0x4a0aa2025140e06e940e,0x324d07728b097c443c29,0x7a2e10087349787a6b28,0x9a184186a66259816490,0xfbd800a48f0c5242e128,0x80253efc0121fe640270],#[0xe660011cfd7e00052f9e,0xf00487de900a0f5c0265,0xbfe1f004eb79fa0256fd,0xfa020fd7e4014587c026,0xc92dc0293f929c00a4f9,0xa61d7bd00b2eee7e0139,0x7e2600463b0879e900b0,0x700c3afc00463c9f009b,0x3cc6bc00473c9f0099fe,0x8a3eaf0011e657e002,0xf23e0047bd96013cfc4,0x1838c12e68722ce0d914,0x8791ea09722cef98c2f9,0xb0f239c6a1d]]
def g254H8 := limbs80 #[#[0xd7a50200085,0x800000000a2498300000,0x8100714705c400c0469,0x800000000e0000]]
def g254D9 := limbs80 #[#[0x5d120591205812050120,0x58960dd920dd1205d920,0xcfeffbfa7fdc9605c960,0xfebeffabbfefbbadff7e,0x82d620658865420ffffe,0xdd05174175905376045d,0x50e18c187235d8878414,0x8493dd1c18460e110186,0xb1802c61071741c5d801,0x1c89872561ca1762a5d0,0x2e111586355d8cb8725a,0x4855d2217475e1115844,0x8c00d61235844d61c8b8,0xe0e7348bc274841a0470,0xa9905cd5e5253649d123,0x5680976438920a7a9cd6,0xcb4dcdb18c06eab1aada,0x70ae1e0e2fc3d5ecb9bd,0xb08a62ca50ec4c30d650,0x387098aa44b8b47660f0,0x94c0c4ae5e6481088448,0x14997de0014d23cf802,0x50dbe8076fae00939adc,0x3bf001ce8809be4c00,0xa015c0228e021ba70096,0x58ff0013bfa015cb00ef,0x5d0050fdbe78028ff002,0x380955bc025fd5b402ae,0x8be6828054d8b8053fc7,0xa6e9804d67804a5380,0x80a7aa0117d0096f93c5,0x2de37c0054f70021bfc1],#[0x1ca5ee4039998dd800b,0x122c94527a0e4d7c80]]
def g254H9 := limbs80 #[#[0x114c0031610181a00180,0x4c5e83f298478c7b8520,0x16940066432d19918566,0xd460000000000089d094,0x223b042250000180f000,0x9223800c281400000094,0x80000120000000a0010,0x20d001a20,0x9b600061800c2703c00,0x1712400000c4c0034a80,0x2940629a52c00160283d,0x28b000000b7a03e1c034,0x61800000302e9f00000,0xc4797400000e380000,0x11301800002a92100,0xda280e800842001200c1,0xa0da11c0410e9220ed9,0x422c172720225b000a,0x185f46841000000]]
def g254D10 := limbs80 #[#[0x581280ffffb7f7f58120,0x372ab14dd82ec3740ba2,0x89c2a00d72ebb35d1ac8,0x823a9a4b44da14d8591f,0xc2f2a64b1218a0f87062,0x2064758187051235208c,0xfa004c4e201650041cc0,0xcce4043fbc01840051,0xa27500a1ff8402dbfd,0x7678025f8c]]
def g254H10 := limbs80 #[#[0x41403d405f5010052c0,0x262284a002500009400,0x651d840690fa0a001850,0xc00121a44904a1000,0x3001d8300000020e0800,0x8096ba0b88502043820c,0x400000c3c00030000c90,0x8682c0000680004706,0x327008000000000,0x5258380000c400000000,0x60309f21400212,0x628005238850980000,0x12000c8a0010e4150920,0xa0f000000006d4022000,0x980a8740048f00000229,0x30d80082eb0e4a00]]
def g254D11 := limbs80 #[#[0x3860888d80ff583fd20,0x2a59060e08a12079a51]]
def g254H11 := limbs80 #[#[0x4db111600000000f2011,0x410000060000d,0xad721830400f8000,0xb45c9c8e047c2000]]
def g254D12 (j : Nat) := if j=0 then 0x3148310403ff else 0
def g254H12 := limbs80 #[#[0xd40002000c00,0x2400000000000260000,0x4]]
def g254L : Nat → Packing
  | 6 => (1,6,5,0,0,0,0,g254D6)
  | 7 => (10,5,5,458760,51,7,1037,g254D7)
  | 8 => (40,4,5,1703953,85,11,1070,g254D8)
  | 9 => (38,3,5,917514,68,10,1058,g254D9)
  | 10 => (12,2,5,262146,33,9,1046,g254D10)
  | 11 => (2,1,5,0,0,6,0,g254D11)
  | 12 => (1,0,5,0,0,0,0,g254D12)
  | _ => emptyPacking
def g254I : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupShort 1 2 0 2 0 0 g254H7
  | 8 => lookupShort 4 41 3 8 4 2 g254H8
  | 9 => lookupShort 20 127 5 11 6 3 g254H9
  | 10 => lookupShort 16 107 6 11 6 3 g254H10
  | 11 => lookupShort 5 37 4 8 4 2 g254H11
  | 12 => lookupShort 1 31 0 6 1 3 g254H12
  | _ => fun _ => none
def g254 : Forest := ⟨254,12,fun i => g254Y[i]?.getD (0,0),g254C,g254A,g254L,g254I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g254P6_0 : block g254 6 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g254B6 : block g254 6 0 1=true := g254P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g254P7_0 : block g254 7 0 10=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g254B7 : block g254 7 0 10=true := g254P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g254P8_0 : block g254 8 0 7=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g254P8_7 : block g254 8 7 23=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g254P8_30 : block g254 8 30 10=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g254B8 : block g254 8 0 40=true := (@block_merge g254 8 0 7 33 g254P8_0 (@block_merge g254 8 7 23 10 g254P8_7 g254P8_30))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g254P9_0 : block g254 9 0 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g254P9_2 : block g254 9 2 15=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g254P9_17 : block g254 9 17 18=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g254P9_35 : block g254 9 35 3=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g254B9 : block g254 9 0 38=true := (@block_merge g254 9 0 17 21 (@block_merge g254 9 0 2 15 g254P9_0 g254P9_2) (@block_merge g254 9 17 18 3 g254P9_17 g254P9_35))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g254P10_0 : block g254 10 0 8=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g254P10_8 : block g254 10 8 4=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g254B10 : block g254 10 0 12=true := (@block_merge g254 10 0 8 4 g254P10_0 g254P10_8)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g254P11_0 : block g254 11 0 2=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g254B11 : block g254 11 0 2=true := g254P11_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g254P12_0 : block g254 12 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g254B12 : block g254 12 0 1=true := g254P12_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g254T : checkedTables g254 12 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g254 0 0 0 = true)
  · exact (rfl : block g254 1 0 0 = true)
  · exact (rfl : block g254 2 0 0 = true)
  · exact (rfl : block g254 3 0 0 = true)
  · exact (rfl : block g254 4 0 0 = true)
  · exact (rfl : block g254 5 0 0 = true)
  · exact g254B6
  · exact g254B7
  · exact g254B8
  · exact g254B9
  · exact g254B10
  · exact g254B11
  · exact g254B12
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g254G : graphValid g254 (boundsBefore K253) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low254 : Lower true (varsX 254) (graphGoal 254) 13 := lower_forest (g:=g254) (i:=0) (hints:=286397488) (before_sound K253 V253) g254G g254T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K254 := extendKnown K253 13 [(254,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V254 : Known true K254 := extend_ok (m:=254) V253 low254 (by decide +kernel)
def g255Y : Array (Bits × Bits) := #[((sampleWord (w80 [0x3fe00ff80,0x3fe00080300008580001])),(sampleWord (w80 [0x482412090482412090,0x48200000100000080000]))),((sampleWord (w80 [0x1ff007fc0000007f,0xc0000100c08631b7fffe])),(sampleWord (w80 [0x40a05028140a050281,0x40a00000400200b1fffe]))),((sampleWord (w80 [0x3fe000000001ff0000,0x8a180d19f6260237])),(sampleWord (w80 [0xc26130984c26130984,0xc26088180c09e2040227]))),((sampleWord (w80 [0xc0000ff8000000007f,0xfff02c030e61c7c658cb])),(sampleWord (w80 [0x8140a05028140a0502,0x81402801082087440001]))),((sampleWord (w80 [0x1ffff80,0x93063f07e07f8ad48])),(sampleWord (w80 [0x158ac562b158ac562b,0x15892063e07605f0ad48]))),((sampleWord (w80 [0xffffffe000000,0x11c07c007ff801318c])),(sampleWord (w80 [0x6030180c06030180c,0x6018030005d28000000]))),((sampleWord (w80 [0xfffff0000000000000,0x1e007fff800001c1f0])),(sampleWord (w80 [0x180c06030180c06030,0x180a0046b38000000000]))),(0x1fff8000000001fe00,(sampleWord (w80 [0x201008040201008040,0x20045780000000000000]))),(0x0,0x0)]
def g255C : List ColumnInfo := [(1,0,254,0,13),(2,0,253,0,13),(4,0,251,0,12),(8,0,247,0,12),(16,0,239,0,12),(32,0,223,0,12),(64,0,191,0,12),(128,0,127,0,12),(20,0,235,0,11),(34,0,221,0,11),(65,0,190,0,11),(0,16,106,133,10),(6,0,249,0,10),(12,0,243,0,10),(18,0,237,0,10),(36,0,219,0,10),(40,0,215,0,10),(68,0,187,0,10),(72,0,183,0,10),(96,0,159,0,10),(132,0,123,0,10),(24,0,231,0,9),(48,0,207,0,9),(80,0,175,0,9),(128,16,106,5,9),(136,0,119,0,9),(144,0,111,0,9),(160,0,95,0,9),(0,4,43,208,8),(44,0,211,0,8),(129,16,106,4,8),(132,16,106,1,8),(192,0,63,0,8),(8,16,98,133,7),(32,16,74,133,7),(64,4,43,144,7),(64,16,42,133,7),(76,0,179,0,7),(100,0,155,0,7),(128,4,43,80,7),(140,0,115,0,7),(164,0,91,0,7),(196,0,59,0,7),(56,0,199,0,6),(88,0,167,0,6),(104,0,151,0,6),(112,0,143,0,6),(136,16,98,5,6),(152,0,103,0,6),(160,16,74,5,6),(176,0,79,0,6),(192,4,43,16,6),(192,16,42,5,6),(108,0,147,0,5),(168,0,87,0,5),(194,4,41,16,5),(200,0,55,0,5),(208,4,43,0,5),(224,0,31,0,5),(204,0,51,0,4),(228,0,27,0,4),(0,549,224,15,8),(0,550,236,0,8),(0,551,224,7,7),(0,552,224,7,7),(0,553,211,0,8),(0,554,224,7,7),(0,555,233,2,9),(0,556,224,7,7),(0,557,224,7,7),(0,559,224,7,7),(0,561,224,7,7),(0,562,211,0,8),(0,563,224,3,6),(0,564,234,5,12),(0,566,224,3,6),(0,567,224,3,6),(0,568,224,3,6),(0,570,224,7,7),(0,572,232,3,9),(0,573,232,3,9),(0,574,224,3,6),(0,575,224,3,6),(0,576,232,3,9),(0,579,232,1,8),(0,580,238,0,11),(0,581,236,0,8)]
def g255A : List (List Nat) := [[],[83]]
def g255D7 := limbs80 #[#[0xa57b6ed7a3e859761953,0xaf4ddaf67d0b2ec32a7c,0xedbc36cba165d8654f94,0xb76bd9f42cbb0ca9e2b5,0x6e04100080c180e52bd]]
set_option maxRecDepth 32000 in
def g255D8 := limbs80 #[#[0x595634c9975d56558d32,0x4c9b25d975595326c975,0x5d5655cd326597559573,0x5cd325d995595734c9b2,0xec5a9595734c99665565,0x5957350da5e89965cd32,0x50fb56a5655cd43ec5a9,0x61d6558d53ed9a959573,0x58d536d1975956354db4,0x6d1975d56354db45d975,0x5d96354db461d7658d53,0x54d87e917658d53ec9a4,0x6a17659153ec5a85d964,0x5cd536d1865d57354fb3,0xec9a45d97354db461976,0x6617654d98e89945d953,0x54db4e85985d953693a1,0xe85985d953ecfa166176,0x5d953edba16617654fb4,0xee987e517654db4e9998,0x6498654fb1663945d953,0x54fb365d9461953ec597,0xe8d9461953ed99765186,0x6195365fa66518654d97,0xec5a265d8654fa368997,0x65d8654fb36899761953,0x54fb16919761953ec1a4,0x6919761953ec9a465d86,0x6195368ba165d8654fb3,0x6cba165d8654da4e8597,0x65d8654db4e859761953,0x54fb2e859761953e8fa1],#[0xe8d9761953ecfa165d86,0x619536d3a365d8654da4,0x6d3a665d8654fa5e8d97,0x6598754d96e819461d53,0x58bb4e859661d53ecfa1,0x6897354d62ec9765cd53,0x54d626e7a25d95358976,0x6cd7654d72589b9e8987,0x5d973589ba5d9535c962,0x58db469d655cd636d7a2,0xe95765cd63ec9a45d973,0x5cd636d1766557358db4,0x6d176e557358fb45d995,0x6617558db45d9935d563,0x58fb4e85985d563e97a1,0xe95985d563ed7a166175,0x61d63657a26518758db4,0xed3a16558758fb3e8595,0x58d535cbb6e859561d63,0x5c9b9e897654d72ec976,0xe9176615736d7a25d963,0x96e657994fe53b93e6b9,0xaf6ab7a8fe8fca3e6733,0xd6af3ab76adbab5eabea,0xeb33ac5eafcabe6af6ab,0xd53b4ced17afc6b39acd,0x33bc4ee96b8dae17b64e,0x7c9d725dc8ff23dc3f6f,0xcaf72bbcadf2b5c9f727,0xcdf333cbd72d7cb572be,0xf73f1ce4f375cd5f353c,0xf4f9d3574b5d1f7475d0],#[0x713db576b5d8f7637d8c,0x13f64fd13eb57ab5ea5f,0xe1b660a3f84023b2e07f,0x2f5038aecbf83021b6af,0x38b442f87040782f8278,0x2f874c0f8d481f83490,0xe34e78434ef8e30ff803,0xf8c3cdf843d078438cf8,0xf78041f30e45b34a44c,0xc5d9b4a5cef8c54ef8a4,0xf6e74378260ef8a59f30,0x5cf6e6ddf6c6de76a6d1,0x69c76e743784643f806,0xf6ccd776acc3784683f8,0x9376ee5776ae43f82e14,0xb0cd7851ca78b08af850,0xf6f2caf85118f4b0d8b4,0x1376f394f6d383783352,0x4164f840e4b2c111f6f4,0x7701dbf641e47841a4b8,0xc7822187901dbf841d8,0x25af8e25af6e264b8af,0xf9649976e2da76e29819,0xdff6e52078e4e076e4df,0x79476e71177480438c7,0xf8485ef6485d76e705f8,0x44f8c90678a90878291e,0xe8d3f4e884f869457829,0x74ac4578cb48786b5274,0xe2f6cc6376ac62f4cc63,0xba0f6cce2f4cce176ac,0x78cb88786b89784b89f8],#[0x8578cbd676cbc8786bc5,0xc22f6cce376acd676cc,0x78cc08786c09784c09f8,0x97f6a99674c9d87469c5,0x2d08f80d1574ca1576c9,0xf8cd0678ad07f84d0878,0x96f4ca47f84d6274cd84,0xdd574cb15f4cad674ca,0x595190f8515476ee85f8,0xd476f287385250f8520b,0xd51476f3c6f853073852,0xec32c25417c0bc000138,0x86f46685fc57c4fc4583,0xb4ca989fc9488b07fc78,0xe0f4ceb0df8d40c8cbec,0x535d2d523d1d5145080f,0x60d5c95754dd49945d3d,0xa18e98417c574d70d689,0x9cf9c91bf9b71b19a4d9,0xfe1f85f11eb9e49df1d7,0x9e15e0ea0ca07a03e001,0x23463062b62762361fa1,0x5124ca48a4424223e23a,0x6e64e60e5ee5ce58e54e,0xe75e73e71e6e66ae68e6,0x97e95e93e8c68767fe7a,0x6adaa7ea52a1a9ee9b6,0x2c1abe2bb6b8ab5eb32b,0xd72d32cf2cb2c92c72c5,0x9ee66e2edf6dd2db2d92,0x705701ef82f2eef6ebee,0xc0fe0317313b0f70bf07],#[0x377880225e13033b81f,0xec3a06d02681934c2083,0x170338e21ab84390db08,0xb609f0400417087c01e0,0x1bb0a81280ce24fc06c1,0x2d41ab81fe0be8740876,0xa0f60de0880958358244,0x398c08012441b785f42f,0x66204019fe82e083024,0xde86c4c761370909f24c,0xbfc11c2b81330c9840d3,0x1ef08007ee0270319864,0x8964202921178190492,0x223035860c0b7b07a14d,0xd090e7c73c011b486453,0xb90e19e645306502f19f,0x8019e278c25f03343206,0x821e685d083e1493829,0x6e41c61b30b193706bc,0xa19d0de8464c386101b3,0xa852cb004970138c2c66,0xf80903fc4d7630123a0f,0x13ffa11b1809400ffd89,0x9ce0d03fe06d66160250,0xae110660fde04a00019e,0xa1de200ca087e81081f0,0x42c1b5eb8462f3e04,0x5fc0844ce11f0064053f,0x9e3200679ff12c011cbe,0xc3a00679bfe90808fde0,0xd0808e84fc7d008f5e15,0x4019dbfc03d800cf27d7],#[0x1c3be5f04226708ff285,0x11e7f3e6008d3ebe6c01,0x77b750e401a37f03d90,0x840ca0b7041f75e20033,0x1fe208ade3a1032b7ffd,0x10a7423fb429eba10328,0x40c874238764113f5208,0x40c943832fd040844fd2,0xcf6e801983eb903277ae,0xa20021b3ff90880067cf,0x242ff38007800d10c9d,0x1f7304085575700212e7,0x92064aa47206505b820f,0x4faa267eb483be6093bf,0x28e040009bd103de2e0e,0x74200157a30008f62570,0x111d091d0a381a237443,0x707a706695d115d0dbf4,0xae044f42f1c11ad0803b,0x674200006743eb82,0xc4de8c400011b0c6c200,0x753237a3137f5d4c8de8,0xb616031b0c6c20000dfd,0x602c0580b0153cd44c05,0x4000002b61ad8580b01,0x8040000010e850e87f7,0x869b0d6c2015b0d6c31b,0x1005a44047fcca2147ec,0x6f0536109e096c235a]]
def g255H8 := limbs80 #[#[0x60000b00000000004069,0x1a]]
set_option maxRecDepth 32000 in
def g255D9 := limbs80 #[#[0x5d563549325956354932,0x5d573549325d96354932,0x61976549325d97354932,0x5d973589325d57358932,0x69573589326157358932,0x61d76589325d97558932,0x695765893268d7658932,0x6156558d325d56558d32,0x69d6558d3265d6558d32,0x6157558d325d97558d32,0x6897558d3265d7558d32,0x61d7658d326997558d32,0x6957658d326897658d32,0xe899758d326959758d32,0x68975595325d97559532,0x68976595326a17559532,0x6a197595326a17659532,0x5d9635c932595635c932,0x5d9655c932615635c932,0x68d765c932619765c932,0x5d5655cd32695765c932,0x655655cd325d9655cd32,0x69d655cd32659655cd32,0x615755cd326a5655cd32,0x689755cd32659755cd32,0x619765cd32699755cd32,0x695765cd32689765cd32,0x659955cd325d9955cd32,0x695965cd32699955cd32,0x661765d532e89965cd32,0x6a1765d532689765d532,0x5d9925d532ea5865d532],#[0xaa197595435d97559543,0x655655cd435d5655cd43,0x69d655cd43659655cd43,0x659755cd436a5655cd43,0x5d9955cd43e19755cd43,0x699955cd43659955cd43,0x5db855cd43695965cd43,0x65d6558d5361d6558d53,0x65d7558d535d97558d53,0x6917558d536897558d53,0x61d7658d536997558d53,0x6917658d536897658d53,0xe897658d536957658d53,0x6898758d53e917658d53,0xe898758d536918758d53,0x6919758d536899758d53,0x68d765915361d7659153,0xaa587591536a17659153,0x5d9645cd535d5645cd53,0x659755cd53619755cd53,0x689765cd53619765cd53,0x695765cd53691765cd53,0xe91765cd53e89765cd53,0x5d5925cd53691865cd53,0x5d5945cd535d9925cd53,0xe95945cd535d9945cd53,0xaa5865d153691865d153,0x689875d953691865d953,0xe89875d953691875d953,0x661925d953e99875d953,0xe51935d953651935d953,0x661945d953e91935d953],#[0x689985d953e89945d953,0xe85985d953691985d953,0xe91985d953e8d985d953,0x61f925d953e99985d953,0x663925d95364f925d953,0x6a3925d95368f925d953,0x61f945d95361b945d953,0x6a3945d953663945d953,0x65d946195365d9261953,0xe999461953e8d9461953,0x69197619536899761953,0xe899761953e859761953,0xe919761953e8d9761953,0x65f9261953e999761953,0x6599261d5365f9461953,0xe819461d536599461d53,0xe599661d53e8d9461d53,0xe899661d53e859661d53,0xe919661d53e8d9661d53,0xe5b9261d5365b9261d53,0xe5b9461d5365b9461d53,0x5d57354d626939661d53,0x6897354d625d97354d62,0x65d7654d626a17354d62,0x6a57654d6268d7654d62,0xe898754d62e897654d62,0x5d9535c9626a19754d62,0x661755cd6268d765c962,0xe89765cd62695765cd62,0x655925cd625d9925cd62,0x5db955cd625d9955cd62,0x68f925d96268b955cd62],#[0x689875956368f9261d62,0xe8d87595636918759563,0x655655cd63e958759563,0x689755cd6369d655cd63,0x699755cd63691755cd63,0x691765cd63689765cd63,0xe89765cd63695765cd63,0xe95765cd63e91765cd63,0x5d5925cd63595925cd63,0x655925cd635d9925cd63,0x5d5945cd63595945cd63,0x655945cd635d9945cd63,0xe99945cd63e95945cd63,0xe91955cd635d9955cd63,0x5db925cd63597925cd63,0x5db955cd63697925cd63,0x691765d56368b955cd63,0x691875d563689875d563,0xe95875d563e8d875d563,0x661925d56364d925d563,0x651935d5635d9935d563,0xe91935d563659935d563,0xe8d965d563661945d563,0xe89985d563e85985d563,0xe91985d563e8d985d563,0xe99985d563e95985d563,0xe89945d96368f925d563,0x697925d963e8d945d963,0x6559261d63693955d963,0xe899461d636559461d63,0xe999461d63e8d9461d63,0xe859561d63e559561d63],#[0xe919561d63e8d9561d63,0x6579261d63e999561d63,0xe579261d636979261d63,0xe579361d636579361d63,0xe579461d636579461d63,0x655935d9646939561d63,0x5d96354d72695935d964,0x68d7654d726597654d72,0xe897654d726a57654d72,0x6957658d726a19654d72,0x68f925d972e897658d72,0xe8d76591736957659173,0x68f95591735d98559173,0xe95865d573e8d865d573,0xe8d945d973e89945d973,0x697945d973697925d973,0x5d98560973693955d973,0xe597661173e557561173,0x69176615735d98561173,0xe917661573e8d7661573,0x65b9461573e8d9661573,0x657926197369b9461573,0x65793619736979261973,0x6579461973e579361973,0x69176e15736979461973,0x69195e197369196e1573,0x6578460d76e898460d76,0x6579460d76e578460d76,0x65583e09766979460d76,0x69593e097665593e0976,0xe8994e0d76e8984e0d76,0x69593e117669195e0d76],#[0x65f72f795fc9fe3ef0fd,0xb9dbcdee6ef35f97fcbf,0xfe7ef3f59f9cf5e77f3b,0xfea7ed3ee9ef4dfa5fd1,0x5feafb57babbd57ea7f4,0x5f3aebd6feb7b5bbadbd,0xd8fec77637afed7debeb,0xf67fb3f59eecef65fb2b,0xfdaf6d776b7b57da7ed2,0xed6f5b79db9edbf6d7b5,0x8fdc5edfd6fdb7ddbded,0xee7757b9fdceee6f733b,0xbdededef67797bbdddde,0xf1ef8dfc5fdfd6fe77d7,0x7c9de4df1ff8fec7ee3e,0xdf3af9bbcdbe65f2f797,0x7dd3de9df4bfa3fd1be7,0xaff57babbd5bea7f4ffa,0xafdd7bebd75bfaddd6be,0xedcf6afb53d9decdf62f,0x7bd7ddbeecf72fb93dbb,0xbf17f8afc3fe1defd77e,0x7fcbde5bf25f8ffc7de3,0x8bf3f79f7cf7e7af35f9,0xae7d57e9ff4efa6fd33e,0xf0bf7cfbafdb7ed9f65f,0xfca7e3ff1df8dfc67e1f,0x7f5efadfd2fe93f39f95,0xdfe67f1bf8bfc4fdebed,0x97fc9fdcfeaff53f9dfc,0x17c69c0150c3803f67f,0x542c3809e1a700d72ec],#[0x11e3a601d2b0c039465c,0x341b2e05946580942c30,0x229ed41742bb02295850,0xc53da89a8576125430a2,0xe7d7609c532e0f9365c1,0xc2f2c2f28ed42f0acb84,0x2b6d490b6bb2f8a3b519,0x51d9154c7b22731b4c4d,0x3b14594764682bec8cc,0xaf6ac65a5d9bcbcd2b70,0x4ec996b4bb3810bb564b,0xedb00569768cad2ecf44,0x57604ccb7206b4698076,0xb500ab16cc1562da81ec,0x6d44746c3835f9a50651,0xc30a1e9a513d8b6625b1,0xb20854b700eb76c81d46,0x70117e6c82335da8426f,0x5c2afcd3056c5760ab5f,0x404ac5b20954b4c13996,0x50a4cf64146b6a02d44d,0xa1ba261c32fcd286263b,0x8523fdb06897b10d1236,0xaebd7615d7b2c29b46c,0x16bd3642db16c85534cb,0x31a76186221d88b99bb8,0x614ccb0bde9a618ccf2c,0xd8b7b8192476a3049ec8,0xabd34a3476e986d44c30,0xcb05d83a1eda8ea89861,0x940d4072bdb30e583641,0x1f9a30f9976c1ea06e03],#[0x8a76a2117ec44265da88,0x7a68c7946c30fc4fb610,0x4db8f8b3b51e9576c3b,0xdda55b3bb74b5b16cd6a,0x8aecadb45d55a8ddaad9,0xf6d55963d92b299a855d,0xccbac935b3591c76aaea,0x9b257beb4ab0206e5652,0x372b33b6cd6643d8ac65,0x5d9762bd9ad05fb15a0b,0xdaae65bb25e9676ab796,0xb5600676abf45ecd708c,0x6711af6d61b63d943417,0x961e38dcc46599688a4b,0xb44077b1884b3650e796,0x6890af671217ec62433d,0xb1545ece268cdac504fb,0x8875ebb10ebd96210576,0x91843b12333170459a65,0x203b74c4948ed48e13db,0x4e126dc83415c10282a8,0x9d52da13aa7b22754b64,0x3e6bb227cd3644fa9ed0,0x957aec529aed09f34da1,0x3af5d8a730cb949f5a62,0x15ed9142619729beb4c5,0x6bfb42857b6850afec8a,0xcc3685198ec8a330d914,0xa261cacfad295a63b428,0x44c396531b52cbeb4a59,0x89872bbeb4a574dec8af,0x130e5a4c6d4b4fad296a],#[0x26d0ab45d915689b22ad,0x9db16dafa62dd176855a,0x3b52e1ef605c6be98ba6,0xf6a5e2dedcb869db170e,0xed8be47da97c93b22f91,0xcb1be9986378df6e5f1f,0xa9325130c7048ed8df30,0x2c71a6618e35eda995e7,0xd8e691db1c5e7a638cc3,0x31c839b639b0b2c73795,0x233533646676e98e544c,0x467a6ed0cd4cda19a9bb,0x4d944c31a5e5a534a476,0x1aa8986362436a6c7969,0x36d130c6a79694d493d9,0x68a2618da90da9b5e5a5,0xd144da1a28bb23451364,0xb8d3b6371c76a6ea2ed0,0x3eb4a612dedcdccdd39,0x32aedcc46dd898a10b93,0xa67db1d0ebb33a0936e6,0x5fb13d89b6c75156cce,0x837628b17ec512c2d2a2,0x61ed514c2d2a280fb645,0xabd9a2d5fb1458bf628b,0xb1864011b6a7d24ec8f8,0xbf627f5666100cec3a01,0x4eccec07db23c5fb1470,0x9d31dcabb73b3274e763,0xfb03c3274c792aed8eec,0x3647a2aed8f05bd99e0b,0xed906d1d3a0db7a64195],#[0xd3a11afa6423476e836d,0xa241abb448364e9d0ccd,0x48838fecd071fd1a0d5f,0xd90719d320d5fa441abb,0x920e23b741c474e838ce,0x441abb688357ec906aed,0xc8115ecd022fd8a055fb,0xd0917d32123ba54209f6,0x2085fb1410c7608287e9,0x4109f6c8215ecd042dd9,0x9b17ec52109d3a184bb7,0x24d7d3249bfa5490bf62,0x705fb14881b6e93046dd,0xb36f4c9672e8d2c2fd8a,0x86fe9530dbdb259cbb34,0xe2fd8a985fb14eb5f4c9,0x163964fac32c9f536994,0x8bf62a817ec53c08db28,0x68e9d44e5d1a894da654,0xdfd2a91a3b75139766a2,0x93a750b374ea46be9948,0xd32ad0af5d5a031d82a9,0xfed9a72abb34d15b7684,0xebab5255b56ea2f6ad21,0x7a56aa2b6ed49a655a95,0xf4cd7955d9aeedd3355e,0x6d5b28bdab59d9766c2f,0xda319dbb2633b364c60b,0xa6643b34cc776ed18cec,0x64df956c9bf5fdab25d9,0x95952bda37e55b46fcaf,0x2b2d15b566bb34acd766],#[0x56722f6acb76e9596ecd,0x8cf45ec9988adab39d9a,0x98553d2b0ccbb560bb36,0xb08cbb5611a766c235ec,0x7354f66c4326c98855db,0xe8955d9d22fd8b9e5576,0xc22fd8bb26bb57557f6a,0xb50fb570a2f66e146ec9,0x1d374ae42ced5c4fbd2b,0x32ced5c65bd9b8cbbb27,0xd4dd9b94b1b2729576ce,0x9c3b5773474eee70e95d,0x3374ef06fe95e0d1dbbb,0x64e9de6cbd3bc9aba679,0xc1cabd581957a85f66f7,0x83b27c05b6af65f655ec,0xa34b0517ec6062fd8be4,0x4eda0c79d8c1813b3822,0xccabedbda58396f6f063,0xfb17d0236afc56e55f6a,0x34b0917ec61006dabf45,0xe9dfedbd33fdcba37faa,0xdbbfdb7b67fb9766ff68,0xa78035f4d006fe9600d1,0x4f0265e9dfcd5d33f99b,0x962ec9d34845bb285327,0x348917b38b22b6b17766,0x591c272d241a6da450cc,0x71b086ca36f3d2c6865b,0xa645dd94c65796933cf6,0xc7175958e04f671e16ec,0x8f84b6b1d5c6563abbca],#[0x2d01ece5839d948027b3,0x5c37dbcb47fb69692f63,0xe953a59c8c7613361696,0xb2b72b3417ec6762bd9c,0xe566567aaccacf151a59,0xd73d90b2e3b6158b7653,0x9ffb61740f642e82ec45,0x5b76430b665862e7dc0b,0x9eec86f65d30dad9b21b,0xa3d90e14bb11c4e74c37,0x45b51d40b4a3a3eee070,0x9b6aba4eed872a5d88e5,0x8ed48971db10ecfb25e5,0xfdb11a03b5234176246b,0xba624daf6a477bedc8cf,0x7624b9ce98953bda92ac,0xec49895db92d43b525a9,0xd91512bb7262776c4c52,0xb637dc76858b8ed0a971,0x6a72b56d8e36ada9c2d5,0xd0d76bda19ed7b233dab,0x898ae3b530dc34a61b5e,0x643d276e62aaeccc557d,0xc8da4edd193aca9fa93b,0x91d25d8a39a7ba46d276,0x23d67ba4744f6e8e8ded,0x42ba7688374e9106dddb,0x866e6c90cd3d3a15bba6,0x925da20e4ba441b7368,0x4227a742c6f4c8590e91,0x8487669091ec92125d8a,0xb90ecd3725d8a6e37b64],#[0x2dccba4dcd974946f6c9,0x4dfb6489f7669140ec52,0xc87669192ec522d3d3a4,0x90ecd3925d8a7237b648,0xe9d1259d1a24b46f6c9c,0xd1a44b56f6696ade8d2c,0x5f6c96abe992ce9d2259,0x46d12ce9d9259d1b24b5,0x7d1a5103b14a3a768967,0xfb64a3774c943eecd28e,0xb48986ee992ee7d1a5cd,0xe993159d2a61cfa44c39,0xd8a5507b04ab9b6898aa,0xa64a9f766953fec92a81,0x649a6ee99326fdb255bb,0xcd4c81d8a99b9b44d373,0x8aa243b35349762a63ee,0x1541876ea83eecd5081d,0x4a289edd5121d9aa24bb,0x144e9d9289d3a4513a74,0xa95cfa45239f46a374ed,0x6ad936ad2b26d9a2d3d3,0xc9b8ed18b64dab5ac9b6,0xb564bb36ecbb464d9764,0x6ac9b46d59764dab26c9,0x5d92ecebb2ed19965da3,0x8b2ec9d164d93a271967,0x539d93aacbb47459368e,0x9d3a4773a744ee9ced1d,0xb8f4aef74ed1dce9d93b,0x396c9e4d3d3bc5c7a578,0x7dd9c2103b18438b68f2],#[0x4bb1841876f0837eda10,0x4f6f088deda1121d9c22,0x3e9200e9da3fdd3a47fc,0x5d9c61a7a780b774d017,0xbb39493f6329b2ece2d6,0xf652511ece543ddbca49,0x6ca503d5cc9e5f9693a5,0xd9cb09bb39593f632b11,0xb197b17672c26ece5823,0x67301eede5e4dd9cbc9f,0xc61939d9c2d3bb38588f,0xb4d503b19aa3f6f0c4fe,0x19b83f753530ede6a6fd,0xd381eede6e45db4dc9fb,0x68005c00008bb69f86f6,0xac011301ce032004a80,0x209a811d81f603600644,0x7406840c2817702be052,0x22b042307e40f081d603,0x8153c29104ea09681208,0x510c4017f82f485b70b0,0x3b307310de01af834406,0x227442b88160fbc1e98,0xe0136225c04a0090511b,0x57e8acd1518290450689,0xc2fe05e08b9d16cc2cac,0x2619e433346520c66184,0x7070de51b7a36486aa8d,0xe3c3c7648e921cbc38d0,0x63203a3fa87df8f931eb,0x8c291412226431c84d10,0xe4a6c930123323ea46cc],#[0xd927404db099512f8259,0xa63949a28c850d49fd93,0x4572cace15632a6653cc,0x302dfe5b2cb38963f2c0,0xc1f98112fb25e88bb117,0x465acc9518eb317661e8,0xbc34ec68f8d0899de334,0xdf11bac36c06c8cd769a,0xa7444e6b1c9a38b27078,0x693c5e77dcee01d7b3a7,0xfc01f4b3e247b38f4e1e,0x282b103da0353ff87ef4,0xfd437686210aaa11c41c,0x194a2f1456489d511b21,0xe9171214a3e647528db1,0xcc4b34957528d24e2493,0x38226c74d16994d30a25,0x6a0bd3fea7ba4ee49d0d,0x8f52c2a455468a89950c,0x5662a8b5490a8414eda9,0xaae695bcab435640abe5,0xa058feb13d60eabee579,0x6d42d685a64b415662ac,0x8bbad74fae655c4ab77d,0x175fc4be897b5af4c5e3,0x8b0b10f61acc21582bb0,0xaca3592cb22763c8c675,0x1867a0ce759a9330a658,0xa9e351069aed219a2c34,0xd951b09b5d76b4ad599,0x9d6edadcd1b7e36c06d2,0xc4c386c7086dfedbe5b7],#[0x8e641ca9b92d7202e311,0x7758ae9f9d1d39f1737,0xe063bcd773aedc5d9abb,0xf471e6fbcb278fcf101,0x337c08f7a1ee03d7d7a9,0xf8dbed87d4af9e9f29be,0xcff19fd6bf7b7eb8fcf5,0xa080fd0132015c00c7fc,0xcf416a826103ca06740,0x9098a112c1e8839706d2,0x9686a70cda17a42c0851,0x23ec44b88390fb61df43,0x3156629dc50e89c512d6,0x578c6517da2e4c5a48b0,0x3aa47288deb1b2e348c6,0xd1fea3ecc7b68f2d1dea,0xf99193225e434484b903,0x4fd49cb933d259e49d48,0x92c32567ca9994cf28c6,0x47982b2f9a5cc4b76967,0x6c4cd4f9a1533166414c,0xf3aa673b4e499c25373e,0x199fb53e467a9cf149da,0x895d0e9a189423281cd0,0x7481a8eb51b6a30b457a,0x52a6094b5a9495261a45,0xa2c542ca7e74efe9c353,0x954b6a7cd4cda94351ee,0x4aac3b57b6ada5588aaa,0xb8b56f0ad935a9ab3456,0x16006be6d793aedb5cf6,0x1db1bd62e6c46585ab06],#[0xcffd9d6b35b6616ca6d9,0x56c92d78dac3b4f568d6,0xfeb7c56efedce5b77b69,0xe5d5c96b8db7132e12db,0x7755ae96dd10b9e7735e,0xa3bcd97912f075dd5bb4,0xfd75f76be697c02f6a5e,0xf83230476057c0677fc6,0x12c3b186a30afe122c1e,0x17962c2c52f899f12062,0x390cb1f9e3acc6eb8cdb,0x2fca13936f2636490c8c,0x2dde59acadd956f2a165,0x1999b31ee629cc2797bf,0x14cdff9b6736066a8cd0,0x3e0679acf019daf3a267,0xba18341be810cfd59f57,0x2fd219a38f46668a9d10,0x4f769c5d337a5c74a4e9,0x5aaef54aea68d46fa85b,0xb7d735adcf5a56b18d5e,0x6376c4bd847afef5eeeb,0x9b30f6536c9cd925b203,0x63da8bb4c7689ecf0d9b,0x6f0edcddb77b67f6c3ed,0x9b98f7286e3ddc35b7d7,0x17de01bb4f7536e91dcf,0x7d86f8fded3bd1f797ef,0x5c0637ff6ff4dfd5bf47,0xdbe171c28383c7055e06,0x8c57165e271c46387f70,0x3c84b8f8f1dee37bc6ab],#[0xb7e533c9ef936f240e45,0x9ae7333e615cb87965f2,0xfcf879e7f3c0e763ce23,0x5de89fd0eba13f40ee7e,0xa567498e91dd213a35f4,0x9d497a8bf507e9cbd303,0x7ebc5d6cbac17559ea6,0xb6876abecfbd933b1676,0x7debfbc3f764ee71dc37,0xd2f157e1f7c22f802efa,0xcb3794af253e3f3c7478,0x1e7cbceef9baf331e613,0x49f47fe8d7d0e7a0ef40,0xd537a97f513e99fd29fa,0xfecdfd907b08f5bdead7,0xeaf7b7eecbdc4fb64f69,0xe3cfc5ff87bf087e057b,0xdf3b7e69fcc0f951f247,0x9ffb1bf5efeb47d39fa2,0xf07fdfcfbc9f72bed97d,0x23c0fc22e23623e07e03,0xba1bc17a1f04a0640cde,0xa8083e138228480f584,0x15e16e0761de13613040,0xd411106d066e1606f6,0xc0a628358400e2842c2,0x6504c0d0c4ee1204ba14,0x886c101e0b619a63c180,0x81c0b58340da08306504,0x9fc122630340a3a21263,0x1246600e5c210801140,0xfc282e1a24f26084088],#[0x480b304e04064d24d448,0xda180cba0d0a80a5a148,0xe050d410a0a3c09e180e,0xac11943e44e61d26e26c,0x380fc1f83407644b6080,0xc400bb21c263056e0986,0x166600e84720a806e076,0x409408fa10e39865041c,0xa4706386204d61413544,0xc13aa15e010b560584c,0xe865054c4544c87283cc,0x86643c09aa1844d252e1,0xbd240483243422050048,0x4465e1c62fe09638c400,0x948960d664d07427c85,0x461a86124aa424448aa,0x1441268133840874e605,0xe05463461c0d86f44007,0x6583ca4d84461042d661,0x4c4804026c04545b0524,0xc1a265a1f24f214c7304,0x7c0c461741e452419a42,0x449a06a26a25125f2186,0xc0e28246e85665e64414,0x6dc1b06e65830684c006,0x1871094e3060708360e8,0x83443e44024d46cc5d05,0x440f3419071641619c34,0xa24b444a404fd26412ec,0x25cc3e45846d245c5724,0x1ca6a21d21e056618c5a,0x4a190a20a5068a7ea20a],#[0x63d85627a66a6520b707,0x3744884ec4b23e45ce3e,0xa07e461a2f0a9c4227d4,0xc18c08851c0a47ca17a0,0xd66965161140ea60c04,0x803d034448a0340ee003,0xc25fe1784604484489,0x1e036104104451046845,0x4fae0c49547326c0dd0,0x41c052c1cc52070a6e24,0x5c41d868860552c51452,0xc04ec1565c67861e244a,0x21d46735465c6442f962,0x1105c45411e474437244,0x2ca780310a4278d594,0xe5980e62f84b09b09563,0x5165a620e14a26a5945c,0xd45606040e4684a82168,0xa0c81f104c7d258c7887,0x3961c630e1d608c17415,0x901b22da5845da3c8686,0x21b25485c60dc1cc1ca5,0x9ed40a000a776cf6fc00,0x4004393c1e7c0021acf9,0x10dbe350116127fbc1,0xf6efccdfe00112c9bdde,0x22fdfe63b9700029f9e0,0xfac1affe7c002277c6a0,0x16f40e67da1c000a9003,0xf828008513ff1b80014b,0xf41006727db47800433b,0x68700088d8d404502e5f],#[0x20bf3c6f540068a7e7ef,0x877db0149edb24f44002,0x6ed4100087a7e8881000,0x862e11fe0e800d02f,0x1c0cfe06f40087a7be89,0xa84000a727efb22e4002,0x10eaf3a7b800862b81c7,0xc9e080021f5f89bed400,0xed0313a3f6d40010e4e8,0xf646800021f7e3a00461,0x21c5e3e1139c004433,0xfc1d908008702bff845e,0x4389f53ac03138002a19,0xc270000a8e7d99ff4000,0x7fe0f38280087932bc6d,0xa8849e0f38280088f,0x63be00114478887b911c,0x3dca0500053abf2efc44,0xc8034b7e72868019cef6,0xded186801a0bfbf68ce5,0x33bb67f889b71c00225b,0x7e72868019e3f5e10d00,0xe00055777ed0f050034b,0xf6e002276fe8886a0622,0x7a7f9220033c3f07d996,0x2cb400d29ede9bd00338,0x3ecb2bb2800884fc7efa,0xe6d2ac0044265fd00328,0xa86fb472a801a15e4,0x88100088bbf701c61b6,0x3327f1ba8019ddfe0fd,0x727f8ee2100087cff220],#[0x9b02200352797a70a006,0x3337daada00670ed3ff,0x669eb52fa02427f9220,0x87cdbc574019dbf1586,0xcf0d10008877c9b03b00,0x791f66aa4a200054831e,0xfffe906b8c36a2001163,0xb400cf4fc5e8050010f2,0xc0874f97e8800cc9b6bd,0xfad136c0045432f1d954,0x373c398d6801118cd838,0x1102001145e1b17a0067,0xe42ff800ce4ff77a7abd,0x38786e94b715b2003627,0xbec62001139a5a5fa003,0x4058e05b20035e3f17d0,0x100029fbfb55b400cf1f,0xff6b764200d077fe1144,0xc5880029b3f2e4c00cc5,0x1b38bfdb421000896317,0x4002209fe99c840021f,0x110cfde00422bfd3388,0xd5bcc004353fbb375650,0x67004f93f0060298df,0x515ddfdac00cf55efed6,0xb400d0021f17ac1c4001,0x8f99360080014f1fe315,0x6020010f012ffc10019c,0xf9a4fe7af0008877ff02,0x9800468167fcb80014c2,0x10eaf829fffb3510c13,0xfe1c7c0014deff9a21e0],#[0x2000a8c0beac7d0021e4,0xf9bc0087008fc7dcda,0x433dabd788200053ab83,0x3f145e80111a57fbd600,0xced6fe82ecf40089660f,0xc420011098cbc2d600d1,0xe34f2b3f006a0201ffff,0x88a3f17d0483014e5f9e,0xcf4008713317fc5a1400,0x87338dfa0c052d3f466,0x6559000a967eaff7af80,0x1157a640021c05bf3706,0x8011308793e9c20043e,0xa003240022e5e59f3398,0x163fc9d0021c9ffa79a4,0xa7c6ac7cff274008827,0x882000544dadc0eb1b00,0x83fc46b40088a320afd7,0x3380e7caef7e000a713b,0xffe5908004426b873b80,0xfe1858754c2001520d7a,0x1108ff15981b3021e2,0x868f9e3014e2fb98f372,0x21c557f6bfc00438177,0xf910c04008977fb5efe0,0x6ec27e2e9000882717f4,0x240022719bfd24e8010e,0x5d2b2c80044bbef5364b,0x4d7e19d617d001a45f83,0x810fa7e072b5d3a20005,0xff2c7100029a147932a9,0x2215fc796894800446d],#[0xdde200053039feb02a40,0x151a54f9d100029a091,0x91000441dff846120080,0xafc14f1200088c7c2aa3,0x89f7d80b7a9100044c3e,0x8c0034b3f03b8a012000,0x3b1636940035f7eb4e70,0xb3fd6222748002243f6e,0x8008967f8e91b0900044,0x4c2900342bfabcdf6c90,0xff2fb3832420022430ff,0x6997ff349ed92100112a,0xc90800892fcf30f85200,0xfe0370400356bffc8ce0,0x2a4ba7f901800688fe9,0x800224cff80a4c210200,0xe4184001110ffb6c1120,0x45e762c7cc5000d66ff4,0x8002243fa817fcc5000d,0xc7cb5900930fff134304,0x3fe94a026282000a99f,0x34bbffcd8b994880089,0xfd82510010e1fc151d10,0x34a397fb6b70010faf,0x806a840044e7e1c351d1,0x3990ab7040045fbffc9a,0x1553fd7635402453fecc,0x10ec7edfd1050190400,0xfc82200029c56fe8e440,0x6ff0db7100480022b0ee,0x21b1ff46c1402400112,0x291d353e004292ebb670],#[0x3dfec67201054d276400,0x623f4c32006897560042,0x3d85e7c008687be00420,0x570010e8e5ff2dc00432,0x7c801977bfd008b0c5db,0x3f3fed4349a80004497f,0xe597a00068ee90fb8003,0xb9ff6a1a4d4000226bcb,0x15202df8df000029,0x230c00044e9e1fed1245,0xf4425b7b8003513fe369,0xa725ed6e864500001551,0x1dc0019c31b4bee000d1,0xa018010f97fb01143fed,0xfc6d246180008927fc35,0x1126feab5180008727,0xe3740010caf8eea6e374,0x7fee0a2671c1000463be,0x116ef9ace38200088172,0x447bffafc58438a42400,0x2100054b3ffe41b18400,0xe6522002262fb3f03900,0xef8f42cfd0092efff362,0x8f600446bf85d2c40043,0xae1a0aa440045729fd80,0xcafa8720042000a947fe,0xbb7ffc34156e08008b8b,0x620022abf974dc900345,0xc6e800227ddbff521d00,0xc77dc6e80021adbbf09d,0x2f4ddf62532596a0008,0xa300219dfa64b2d40011],#[0xa8efc663c019a5d26,0xcb4d100340167f894282,0x122f2f5e3320801131e7,0x88029e48b3e4560db801,0xf2e0a7002186ff4ad452,0x29c0d385fc1500029dd,0x53d400029fcdef53d400,0x437bf249e0004325e47,0x23ee0a82018a8f249e00,0x8847fc96e21070000152,0xacee4ac20294f75b8201,0xf89c000222917dc00021,0x5263f40a000436b278b,0xffdb800820811167a384,0xf380029abfc0004019dd,0xec69c014100054f9f5e1,0x7562ecfee24000890bfc,0x475f180eaa7414000a9c,0x810d27fdc9a01430005,0xfc2fe9420405383dbe79,0xa790033d22fb80004355,0x10fffd78a84004437f8c,0x8002a03c2bf1e8801a0,0xf1b0c2000a6b3ded0ed1,0x41054fe27a38800860b,0x53aeffc801984ffd1805,0xa4000544037ede88801a,0xdbee3ea01982e6781138,0x92feebba9021a577820,0x8563fa6001492fb741,0x3afe538f0005313ffe78,0x184e67ff90000600802a],#[0x3b01611a7602c231ff0a,0x62fd03187fede10100cf,0x211bbf108806691c0884,0x18201a09ec741093b0a,0x202019cff850c276ff4c,0x88088dfe0408464fdbc,0x410010002201fff24004,0x250fff440860068f7fe,0x20a9e783808acff0168f,0x90284404461ffc200a08,0x21f76fa0b804997ffb0,0xee91460021c9fee88120,0x5f3fd3c200a18002a09f,0x1380b7d9e101513c1c04,0x7340086011bc100c4000,0x2189fe0b9a004373e41,0x581e9b40014c8e6f93a0,0x84052d3665f028820441,0x8697f604b0086d3ded3,0x8042ec2c708a237f04b0,0xac0197a9f580329bf825,0x4088bbf6bc04052b74f,0xe87d9000a4c7f9fc8041,0x200153a9fbd885080054,0x3bbedc18010aa7ef6214,0x2d0c202969f17ba88204,0x58c670640fe900019bac,0xd0424632a50662dba806,0x81000a50e9f1006527b1,0x7f9e0021a783808ac7ab,0x24eb57c0810850e4ff,0x4013aa400044858d75c7],#[0x14f31aeb1e004877ff,0xaf62a0c00869bfb50a00,0xc5000088b7fe8a00010c,0x39ff05bb8800349bfee4,0x3788003485f1edf1c009,0x4ffd1608800014f9ff70,0xca4001aa1e696800021c,0x22b0efe00460fd7a8b,0x67b7ec27fdbfd7a80,0x15fe2a588003457f4cb1,0x48006bf7fa3ee4440011,0xc09100045271fe5ae185,0x75505220008927fa79aa,0x5fc0a69040014e4fffa,0x114effd24805c4840045,0x20008867b49fe8442d00,0x8ef7259400341bfce8c1,0xeb940033f7fda9c28006,0x214ffd294f040014e1f7,0x4400d5cfffee65b82002,0xc8284004557fffb2303,0x6890282000a8c7ffe4f1,0xb704004597a7803231ff,0x142002209ffddbf93cd4,0x54478c200199d67fb4,0xaf70010f37ff93c80840,0xc004313d6ec008587753,0x200684cbf0064e7ff4e5,0x1105fdf200652ca65fa,0x370a7c0043d85fe64250,0x5b7d51d1ef7780008967,0x43208002a80e3dcf080a],#[0x615e8c00878bfc6a8742,0x14db7a2521b9000a7475,0x9dc320014e67f1892a10,0x210dc85930021b895d,0xc40043136ed8010bee8f,0x4393a4dd800434b037,0x275922e0042d3f9984cc,0x6362002187cfdabfd201,0x43c9fc7580200029c1f,0x9766096804333e3e5bc0,0xc0e011208029dc85c0a3,0xea7800527397ba08403f,0x9f81000a4b7f9e002144,0xf3c0042dbff573c00434,0x5301e5f2a32c0014fef,0x73f8980052b9eea18580,0x2c000087a55e8f002140,0x8823f5a9f5400297de3f,0x5fd6046204080a8de2f1,0x64080348bfdb17c00437,0x3355fe26c05247dff89,0x18d5fd02700666f2f138,0x6640c0044f2f89607000,0xa506206000a9b7ffe0aa,0x43e3fe5800010c011ffe,0x15d638011f1fb4964820,0x25fac00cc570b43080a5,0x83efc4620cbdf88c4196,0x4283357c928506627f20,0xff4004293d8e8212be49,0x73c1c0458ffa1006505d,0xf0701164fb808b6f8010],#[0xa88c000aa1077f1c0244,0xfa7260010ee7e4176b23,0x88e8ffe78c2e0034e38,0x30e2bc0199d8ff400940,0xa0014c4ff760aab0021e,0x21eb8715ec019f4fa2a2,0xe9820002a35e0cc5ec00,0x7e5dc74f8008803f37e0,0x5401c0337acf99000a83,0xff808c47ffde8840c800,0xa7aba1e99000014fb54,0xfc4c002966e07a561400,0xa7d80e460014a33d,0xbbc9000015337f530bb0,0xda729ea000314023f571,0x4d80a513f93792000029,0x8010d13f7000311ee57c,0xc593bd9c0014b8fedc14,0x1efaf800899dfa440102,0xffdecca78008800be9ff,0x2a5dfece9a26d043cbf,0x150f7fe853ea86980,0xfea13000a5cb83d0a588,0xa0003180ff5098005281,0xe4401d4ba61a29dbaea5,0x83ce4c47716376d249fe,0x97537bbda86ce4c54f22,0x6afd222b214cc3da10c3,0xb9c160f74407a5369483,0x31297a8c2b1a8ca54624,0x132ca0e67030a3707e0a,0x2843140af0587a162952],#[0xdb4523aad0971017f52e,0xa09ee7656da450b2e0ee,0xe17877bf02c4971414b8,0x6900b3c93694a497b13c,0x68c25dca61cd279e530e,0xdcdd99d30a37b689dea6,0x38c2d557ec6ef50bca12,0x3d0bcfbd604f435bfbf2,0xb85fb0742d652fbe3f43,0x5b4c4991478477e5485,0x2cbcca2591e1a6e219a1,0xff90d48d214c0e690384,0x7a999261cdd16a19853b,0xa45b8913cc16d2c44789,0x5caf48548c4dc2a3f598,0x4800274da98826768d18,0x162133be5549662781d5,0x8586142a34050180f843,0x87e60f2b292566083755,0x48050e4d1b67b158e2a9,0x795947d966c6c58c3d9,0x41bd24314143141464c5,0x98b39310afde02c32b20,0x587141438a0a1b8dc59c,0xd2fdeebd4bb7fb9191ea,0x71b33851b338477aa8a2,0x508c935ece42f8e8b618,0x88e37103ecc0a101f660,0x84ecd938b1a23e240501,0x393139fb00ec22bf821c,0xafe08721316b30a4756e,0x4ba8eb7b0c2e7ec03b08],#[0x8165255fe3c82b294eff,0x161f07623bcbeea3334b,0xa295ef0161f076295ef0,0x1c4bbc726962c0d14581,0x49e18932278624c99b0f,0x67c3930e428c74876b30,0xdfc986050befe4c30285,0xf930c0a178fa78cbc297,0x5c6e51560c526869c0fb,0x6aa2ce4c4338dc233234,0x901404771b855b0d6c35,0x25df062fa9256608df20,0x169c0e6c39383ef04acc,0x8717f481b742d2dbb036,0xf9380aaaa6d70ecef315,0x3fcf9baca6939750859b,0x5e8c6380ea9ba1c67597,0xcdf2214867f4e62c852d,0x852b1f5bfb08096429d6,0x95d37f028661bef9012c,0x14800b4a7a9895edc15d,0xa8fdf12d24218ab7b122,0x3485319ff9b482508690,0xa79bec490d285ff95a84,0x5660acc9a2a9b1b25988,0x83f656525943b952ee96,0x1b3d8b16c54c3434bba3,0x55161ebdaca4878bc8a1,0x9ee370ab61ad86b61ab,0xc1d4359492b30480a028,0x178b203e25381a7039b0,0xa8af6ab0b29c574a4a5e],#[0xb16690d4705835585c7a,0x240ac4e131e59e6241f7,0xadc263f8dca32703fbe3,0xdc4fbe656e1f1d4d51cc,0x6ab0b8f5515ed561477a,0x15412625557ec75d58b0,0xbbd21c62bbd42f284c9f,0xec525f0c97c2d9f87d62,0x6ab0a97aac2bdaac2c8,0xea47455d58b]]
set_option maxRecDepth 32000 in
def g255H9 := limbs80 #[#[0x1002000888143240001,0x10048a400880180,0x2968800000,0x934000000000000,0xae000000000000000000,0x1984100000001e327000,0x5c0000000000,0xb000000000002540000,0x1d6e,0x10c00000089000,0x2bb00000119c0000,0xd4000000,0x3358000009dc0042c000,0x6846540000000000000,0x65000000004150000000,0x418000000,0xdb1c000000,0x320000003ba46900,0x7c0000,0x282843000000,0x50400,0x9f8ec004090018740000,0x381000000000000004,0xc0000000020000000000,0x8b00000016e00006,0x0,0x228000404000,0x800318800000000a1800,0x4113922,0x3b48008c00,0xc4400000000000850,0x31380000146c00],#[0xec0010e0000740000000,0x1208000,0x0,0x5bd6800264cbe00,0xe23a1c000000000000,0x298,0x80021a0000e800000625,0x5a28945000000000004d,0x29b8000011,0xa5b00000000000a90000,0x19e93ca420c6000a8,0x720000000824e0000000,0x738000001018008,0x4dc,0x5b570010040000000000,0xafc860000022,0x2340011f800000000000,0x10280087800026000,0x4130000010880000,0x0,0x0,0x0,0x8e002108000000014180,0x15d9580000000000575c,0x340005a06f,0x268e8000,0x6000c30000000000000,0x21a0015ca180,0x30f80000000000000,0xe740023100000,0x3b16480000,0x191509000000000],#[0x0,0x0,0x0,0x0,0xce40000000000000,0x0,0x84c00000144658100000,0x17ba8000e2e00000000,0x1408000000010800000,0x44a0000000011fe000,0x37100000000000cfa000,0x2e000000002fb17400,0xab4ec000000000033a80,0x6000000000047e2,0xd1180021200000000000,0x678dc,0x50a000000000000000,0x15c0000003d8,0x42f,0x79220000000000000000,0xa9000a2c00000000000d,0x1a8,0x60160000000000000000,0x9bc0000066dd510123,0x0,0x70780000000000000000,0xaa2a00303c50032cf,0x88d0f4000000000000,0xeee0e0000,0x6124000000000022c800,0x3b2000c7d1980000046,0x2388000640],#[0x214804000000,0x50000000000000000000,0x25,0x1db0000000,0x41e001420c107f8e6,0x6320000000005600,0x62a4b90380]]
set_option maxRecDepth 32000 in
def g255D10 := limbs80 #[#[0x549325cd524c96354932,0x4c98754932619524c976,0x5d9624c975589325cd62,0x5893261d624c98558932,0x4c97558d32595634c997,0x61d634c98558d325d963,0x595325d5654c99758d32,0x4c9635c93265d654c976,0x615724c9765c93259572,0x5cd32595734c9865c932,0x4c9855cd325d9734c975,0x659734c9955cd3261973,0x5d532619754c9765d532,0x4c9985d532659754c992,0x61d764c9865d932e5975,0x5d93264d764c9925d932,0x4cb955d932661764c995,0xe55874cb9561932e6176,0x595435d96550d7559543,0x50d755cd435957350d97,0x6597350d955cd435d973,0x5d143e197350f855cd43,0x50f955d143e197450f85,0x6597550d765d543e5974,0xe15436557650f865d543,0x50d97e154365b8550d76,0x5956354d97e194365786,0x58d535d56354d7458d53,0x54d9758d5361d6354d76,0x5917354d87591535d964,0x5cd535d97354d755cd53,0x54d945cd536497354d86],#[0x6197654d865d15365973,0x5d9536497654d875d953,0x54d985d9536517654d93,0x6498654f945d953e4976,0x6195365d8654d9461953,0x54f9761953e518654f92,0x6598754d9461d5364987,0x61d53e518754f9261d53,0x5897654d625cd5358b96,0x54d725899754d6261d53,0x5cd625d573589765c962,0x589955cd626497358976,0x64d7658b955cd6266173,0x61d62e498758b925d962,0x58d655cd6361d6558f93,0x6497358d765cd635d573,0x5cd636557358d945cd63,0x58d765d563e557358f92,0x64d7558d925d56361d75,0x5d5636597558d945d563,0x58f945d563e497558d98,0x6557658d945d96364976,0x5d963e4d7658f925d963,0x58d9261d63e557658f94,0xe498758d9561d6365187,0x61d63e518758f9361d63,0x591935d964e4d7459395,0x5db8359174e0d64e4d76,0x54d7265f8359195e0d64,0x5c99654d725d9535c963,0xe49765c9935d9725d963,0x591735d9645cd7559173],#[0x5cf9559173e15645cd85,0x651765cd925d97361975,0x5d973e49765cd955d973,0x5cf955d973e51765cf93,0x615825cd76609735d582,0x611735d5845cd8660973,0x5cd8661173615845cd76,0x5d9855cf9661173e5584,0x61573651855cd8661573,0x5cd9461973e51855cd96,0xe4d865cf926197365586,0xe0973e55865cf9461973,0x5cd96e0973657825cd76,0x5db855cd96e117365784,0xe197365b855cd92e1573,0x5d196e0d74657835d195,0x611835d9836097664f86,0x60d76651835d98560d76,0x5db9260d76e11835d995,0x60f825db9361176e5183,0xe0d76613835d993e0976,0x3f593e1176657835d994,0xfe7fe7ee7de7be6fe3fe,0xabf6beebdebbeb7eafe9,0xdfedeedded7ecdebfebf,0xcef7ef5eefeeeeedee7e,0xf1feffeffaff6feefdef,0x4df3ff3f73ef3df3bf2f,0xdf65f5ff5df57f55f4ff,0xf7ff7ef7df7cf75f6ff6,0x9ef9df97f95f8ff8ef8d,0x5faffaefadfa7fa5f9ff],#[0xfbf7befbdfbcfbbfb7fb,0xcffcefcdfccfc7fc5fbf,0xffdefddfdcfd7fd5fd4f,0xfeefedfecfe7fe5fe4fd,0x403fdffcff6ff5ff4fef,0xe0f357605a2ba80d859,0x9850b6ec30b4d5d851bb,0x6cc30db961469b30e1af,0x4cb5d925732e8ef98747,0x941cb0ca0d9874a54cba,0xed0403a15c6cc328aae5,0x1768320d3be4b5d5f142,0xb6bb005f5d400874afca,0x9b69c01932e01198700,0x805932c03198601a8bb0,0x5004f1870282c3011be9,0x3a60419d381a565c0c63,0x9ebb034661416a2ea0a3,0x4db68c1d2b2e11057608,0x452daca2817a50a19d28,0x462cf176179ebb0ac661,0x1870bb2ba858ce9462a3,0x86c2861669c2d7b2e170,0x7405d839632e1939760c,0x43cb74a1b6da20d48cb8,0xec3349751965d1080be9,0xd861aa8d10d1269c6672,0x76bb0e12e9869672c34e,0xe92e946ea3443693961c,0xc4a62ec226fa21f17d28,0x444ae1862003d409b861,0x1a32c0ad1163264ca02b],#[0xfd29388e94980b50581,0x78169cb80b4a5a07a52b,0x5ae7b46e13d766f02d31,0xece6a5976c9cbb35d25d,0xfa27252bb3b05689da7a,0x2d2bd0c68de4bb46f13,0x2a965a8e72ed456565a2,0x8ce92ea664da3a79fd15,0x4c68ef863424d399ce5d,0xba53516d31c3b5d8e097,0x14d31d23e58e85b4a724,0xe8a694ec1b4c788f863c,0x9084b4a8131763006d29,0x4e8a07a64403d3a1a265,0x5a649b2b2a401e95180f,0x81d3258be892ecb4a956,0x7d25d53e92eaa6c7a54c,0x940cf4aa94975549cbb2,0x4ea42fa252a4d2a8d265,0x1a35d70c3a699e9555df,0x8d1af31655680b50ba1,0xc38e9d5c4744ae05a85e,0x9706f42b8e3a6580fd12,0x44b89ba15c0fd3ae08e9,0x7a75c45d32e24e8d700f,0x11d3300be8d800b4ec48,0x408e99845f46c237a161,0xd985f46cc3ba06602d33,0x4ece2fa3671bd0b387e9,0x1a5825eb2c14e5d9fc3f,0xb2cabe16e9a0272ed001,0x196e9a0672ed0339a67d],#[0x1fa7744fd39a27e08d14,0x4afd39a57e9dd23f4e69,0x1a38b7fd2bdc0e8dee77,0x2d4458269a2d4aed161,0x60468e317b2d0f397687,0x61277470805a88c04d34,0x4b0aefa3852bd2c4cce9,0xfa78a13d2c50de8629d7,0x2fd14716696457b2b221,0xc016965cb7471e5ba38e,0xa545f472a33a29516d2c,0x472c37a1960fd3ca88e9,0x5a29a0fd3cb08e9a585f,0x70bb5581e97310aed960,0xccee8ea54aed5811a3ac,0x7380f4d9aa796ba57cad,0x2d7e47a5ad25d1d681e9,0x195b203d168a15db414f,0x25d1d793e8abc934b64b,0xf2365678234b8e4ba3b0,0x6840f4f408976a015d2c,0x4ba807a6d306d2cd81e9,0x3a2d703d2f001e97540f,0x3d1718ce8b886745c23,0x36269417134c0207a5e4,0x45aeb4a0ed1a90690d40,0x501971a60cc4d1065669,0xfa51066d2885c694363b,0x38d48cdc65867032a32c,0xf4765872ab4c3555961a,0x8799b2c3d1d861eaabb0,0x4a3f8ba21faad28d9ce9],#[0x5a21288d408e168844e7,0x68d109c26a04ae346257,0x1565d8893f50269da813,0xc82b34440d1962290c31,0x5242f5a8207acc105568,0xfa6241fd411a76608c7f,0x84c31533654a5a32a503,0x58fe94ad3b3054f5872a,0xdb2ef44d91da86bc4d13,0x44dd23a26d60d4b65c68,0x19573acbab9a76a1b9a3,0x4ecc3a505d9d1eb30e2d,0xbdde89dc7f4aeb41a572,0xe8eb7454663a57760cab,0x5148d1a2a45ad4d1d568,0x595a6add15350696953b,0xb8cb19e0654cca74b4cb,0xc55698d2ab2c6871a933,0x8da3f0c6d5576368ecb1,0x4a6f55a53539d31b3365,0xca832855418c4aa0c0e7,0x7b541f3da60f93d50649,0xa76a5093d307e3da940,0x92b03489381a2494f4c2,0x489571a44ab9d1255c68,0xda44b8fd125c76892ee7,0x67d12633689323f48971,0x9d55d94d9f4898cda44c,0x950e7529ecd96538ec32,0x4ca8cd96548ec32a555d,0x5a451abd128d568944e7,0x8fd129476894aaf48a35],#[0xa9ce89563f48a51da452,0x53a13509b71a34dc1d2a,0x52ad15a4564f54a7272a,0x5875984c32cb364d653d,0x38d1aeb364d753b30b2f,0xea766175eb0ebb09865d,0x1693b50bacda35d1ed42,0x4ab581955a67ca2d3365,0x5875b84c32d9de896f07,0x84c32f1c68d793b30b6f,0xb8f6a1793b30bcf5875e,0x15e1348af0ba25784d12,0x48b0f7a2587ad12c42e9,0xfa35c93d0ae3de9161eb,0x4ed12e3de9d72174cb91,0xfa7e91713b48b89fa25c,0xd807b4ec49d97624ecba,0x2ec09d976085d33047e8,0xda7634ecbb18fe9d813f,0x8fd1b08fe89864f42c23,0x20f69192174cc23fa461,0x9953f2cca9d96654ed23,0x4cd09f96684ecb340fe9,0xfa6664fcb3327659987b,0x1ed334a7e59a53b2cd23,0x3c7e8d9c7f44cf27a167,0x9a87b44d4f7a76785cb3,0x48d49da46a4fd1352768,0xd957faababfdc595fd3f,0x66cac0555d602e2cb00c,0xd5691f6ab44fa73a580,0x1ee1744f709a27bb9d34],#[0xed0ccd938685d23dc269,0xd98867ac3c33065a1a82,0xa0bb445ce9a1d9b290e9,0x22766221eb0f10c19688,0x21283490943a284a0d14,0x450b6ba589b9d1c4d0e9,0x7a4857ad242bde8a15eb,0x8fd1c50fe8a2a4f4314f,0x6bde9e2a174d1513a58a,0x638c34b20c1959060cac,0x2b2463a58e61cac73065,0x3a38f31d147986964983,0x4ecaca48e4a518349277,0xba76565c7f4b289f9594,0x6613b4b2e3da5974fcac,0x2b2a9d95958fcacc4765,0xf95994ecacc8fe96553f,0x1fd14b49e86587b4b329,0xb42e9a5a272b2d1fa396,0xa6a3f47343da29a7bd3c,0x49349da49a4fd14d2768,0x576b729d35abd61ad53f,0x91d15c14e96d87f4d6ef,0x42769731eb4b943fa5b8,0x2b13f31554176aa5bcc5,0xd7343a5a9a0d2d4866a,0x576bb29d35cade5ae5eb,0x5abb5e8fe9aed3f2d76f,0xe14e96e8334d7a9d86bd,0x7393b4d9a19a5be1fd2d,0x4b5b57a3ad29d156a769,0x3a7c139d1e09fe83069f],#[0x1fd16050e5afeaf477e5,0x142e5b02274b811fa3c0,0xf08d74b8473a3c23dd0e,0x499ef7a2cf7ad16794e9,0xfa2d14ed168bde933deb,0x5acad727e93453b49a29,0x7ad656bca34b62b595b1,0x6cd6b2b6653a5af5bcad,0x496957a3b029d1581469,0xf95c766cae386697196b,0x39d1e21de8b10e34b8ec,0x29ce8f14f7438a53a7c4,0xf2433459253a7c531d36,0x49a49da4d24ed16933e8,0x3959c60cace426967d3f,0x91d16b1869674c74b38c,0xfe977d3b2bbe3fa5d6,0x7807f4bc09d95e00dd2f,0x4bb89d85dc4fd2f02769,0xfa5d74fcaeb9de8b5c33,0x3bd16c8f6976d3f2bb63,0xc1ce8f60a74fb263a6d9,0xf68c74db47ba1da8fd1e,0x45c69d95e24ecaf094e9,0xfa4e34ed271a7e8b8d3b,0x4ed2f206e9790334bbc9,0xb636947f1f4c3d8da61e,0x4df1b4a6f8fa636c6d31,0x48b58fa455c7d12ae3e9,0x9a26194cbb04ae91731f,0x95d230ca691865744c32,0x3cae899e532cd3299668],#[0xa271f490f8fa48195d23,0x49152ba28abdd244dee8,0xba49694caccdee923e57,0xaed35cd7696dabb4d6b2,0x1d7e92b6bf455b5da5ba,0xb0dab2d872986c3aebb6,0x497f5fa2bfaed15fa069,0xba4c095d16057e92febb,0x6acae357e92c10745852,0x43565721ab4b8c81a5c6,0x672f32b3883a2c540d2e,0xbbb2995dbbdd2ce5e69,0x5a5e440d2eeb56577653,0x1ae013e00d400660000d,0x39c033002dc0282021c0,0x5aa054a04f20486040a0,0x7c0077a06f0069606060,0x95a091208c00866080c0,0xb4a0aea0a840a1609be0,0xd3e0d020ca00c120ba20,0xf260eb60e5e0de40d7a0,0x10e10aa10560fea0f8c0,0x30a12ba1250120211921,0x50e14ae144e13ce13781,0x6da1680162c15cc15661,0x8c4185c17e81780172a1,0xa581a0a19b4195e19021,0xc121bb41b6a1b241ac61,0xdee1da41d4e1ce61c721,0xfcc1f701f141ed41e7c1,0x178212220e220b4205a1,0x2ca228a2242220421c22],#[0x518249e242e23b423562,0x73026b6264025e0257c2,0x97428ee287a27fa27aa2,0xbc62b4c2ad22a6429d62,0xdda2d862cf62c862c362,0xffe2f9a2f342ed02e6a2,0x1f43194312830c430602,0x3d43384332032be32583,0x5dc358a353834e4344e3,0x7e037843708369c36423,0x9e8399c393238cc384c3,0xbee3b8e3afa3ab03a5e3,0xe3a3d9a3d343cc23c5c3,0x6a40203fb03f523eb43,0x22c41ae4164412c40d44,0x42e43e2438e432a42ac4,0x65045e84570451044aa4,0x82a47b2474a46ec469c4,0xa4a49fc496e491048864,0xc104bc44b304ae44a9a4,0xdf64d964d3e4cda4c924,0xc4f864f084ea84e4c4,0x1dc5188513e50d2506e5,0x3f65370531a5278521e5,0x59a553c54dc548e542c5,0x75c570e5698565856085,0x94e58fe5886581657b45,0xae45a905a3859da598c5,0xcda5c785c185bc45b485,0xf225e885e0a5da05d3c5,0x14060ba605a5fe85f905,0x36a62f462906224619e6],#[0x580651e64b8645863f86,0x774671666a2664465e26,0x96068e86888682a67d26,0xb566ad46a8c6a3e69c66,0xd5a6cf26ca86c4c6bd46,0xf466ee06e826e2c6dc86,0x196713870ac70206fa66,0x378731872a8724c71ec7,0x57a751c74a4744873ea7,0x79c772876c8763475d07,0x9c0795c78f2787677fe7,0xbe27b707af27a847a187,0xe007d827d1a7c8e7c387,0x627fee7f687ede7e6c7,0x2bc822a81ac813480c68,0x4d684848422839883208,0x71686a4862685b485488,0x94288d0886687fc877c8,0xb388ac28a6489fc89a68,0xd388ce68c928c248baa8,0xf6e8f088e968e248db68,0x184912090ac90408fdc8,0x3ca934c92c4924e91ea9,0x5d0955a94dc948e94189,0x7dc978896fc969696349,0x9e69974992a98a6983e9,0xc0c9b969b3a9af49a689,0xe329dce9d6c9cfe9c709,0x88a01c9faa9f189ec09,0x2c6a24ea1cea15ea0eca,0x538a4aea43ca3c6a344a,0x752a6faa69aa62ea5baa],#[0x95ca8daa85aa7f2a7a2a,0xbb8ab5aaaccaa40a9baa,0xdbcad58acecac90ac1ca,0xffeaf8caf1cae90ae2ca,0x22ab1deb170b0eab070a,0x3bcb366b310b2bcb282b,0x560b506b4b6b45eb40cb,0x774b710b692b640b5bcb,0x986b91eb8b8b84ab7c0b,0xbb4bb1ebababa6eb9ecb,0xdc4bd68bd00bcc0bc38b,0xfe4bf76bf1ebeaebe3cb,0x1bcc184c132c0cec05cb,0x392c33ac2e4c2a4c24ec,0x59cc524c4acc44ec400c,0x7b0c740c6bec640c5e4c,0x9cac960c8fcc898c820c,0xbd4cb72cb14caa0ca3ac,0xdfecda8cd1cccb8cc2cc,0x8cfaacf38ceaece4cc,0x294d20ed194d114d08cd,0x44ad3f6d392d348d300d,0x62cd5d8d56ad4fcd496d,0x802d79cd750d6ced670d,0x9d8d97ad926d8aad868d,0xbd0db52dadedaa6da34d,0xdf6dd86dd12dcb4dc42d,0xfccdf86df0cdebade62d,0x15ee0d8e0a0e062e00ad,0x304e2ace256e220e1dee,0x520e4c4e438e3e2e374e,0x728e6b6e656e5dae582e],#[0x936e8dee880e814e7ace,0xb86eb26eaa2ea26e9bce,0xd9eed20ecbeec62ec00e,0xfd2ef54eee8ee7cee18e,0x202f186f128f0b6f042e,0x446f3e4f35ef2eef27cf,0x646f5faf5b2f528f4a2f,0x840f7faf7a4f720f6bef,0xa08f998f932f8daf87af,0xc4efbaefb52fb04fa80f,0xe5afde0fd8cfd1efcc2f,0x650010ffa6ff40fecaf,0x25f022101bf014700e10,0x465040d03ad036502db0,0x681061905c3055504ed0,0x88d082b07cd073b06e30,0xa890a0909d1096b09010,0xc990c450bed0b7b0b150,0xea70e370dd70d7f0d1f0,0x6710090fc90f670f0b0,0x20311a7114b110b10c51,0x3f113bb134b12e112651,0x5db1577151d14b9145f1,0x77316fd16c11671162f1,0x92d18c5188f181317bd1,0xa9f1a551a1119d5197d1,0xc191bcd1b911b4d1af51,0xdcb1d511cf91ca11c651,0xf771f271edd1e931e451,0x16d20e32093202b1fc71,0x30322b9226b220f21c12,0x4b5245123fb23b323552],#[0x671261925a9254924f92,0x4781f012787271326bd2,0x85d0e0ab81b88833c22c,0xb0ba201c0204240ce093,0xf8200e788c248640c834,0x401b03dd0c0ff42f84b0,0xc840b0ce184d89806b8,0xf06c1a8401403b82010b,0xb43744341827e0a64fc2,0x1124d4c03942744816c1,0x115c0b10224e101803e6,0x1281b1260e823043c30,0xd30d04604a4c49b14106,0x98056a4c8991b70fc1c0,0x2330801650803b036c21,0xc481783c0300550c20d,0x63c103106586f0991023,0x10a15082a4188c1d826c,0x80b82b60c14d18c0e11c,0xc1ee0947920855434c5,0x2921d08996a361341249,0xa04b82e098618258220,0x10ea9b020447c370462b,0x198f32e09989c8681645,0x1113384406c1442883d8,0x440a442204902f44f01d,0x3046c168452e2698792a,0x489291f0902a94381302,0x8cc1a87ca58c891d9221,0x5122ac504909021b852,0xad205054589f50a30543,0x6c2c4b190186a204a22],#[0x45d247872162fe49499a,0x220a2521e66e0bb0709c,0xd29493525141c2520c47,0x2933461cca10192f43d4,0x117854c2c961528a0c0c,0xa0150e226e052562191a,0x4a8a714707c46c8087e1,0x1081f13d0d655124244a,0x943a0f4189f20781e03e,0x20a2f82989122c14027,0xc4784298891e8a616f1,0xe0041b1b0072368ae481,0x443bc974354008742e,0x23f9f6801a30ae887a2a,0x442bf6b2cf94004417e,0x7c66a0021e1f48acf940,0x32011db44ff8400ce6f3,0xa25f9a7500800889fdff,0xd38200d55fb7e73d1001,0xe33d34868034f7b74b77,0x201200d11f4f81200ced,0x45e5fafcd180911f4d,0x81803393f08f0bbd8388,0x4760a2aa090008a0f8a6,0x7ea220047df23a508def,0xe4108033b7f12084019f,0x392008e1fe94900668b7,0x400433bd98faa8010ebf,0xddfe65722a00439be1da,0x7690010e6fc389150021,0x801106e1f690010c6fd8,0x993c0a801156aa5c5c0a],#[0xcdf1dfb6b00670739387,0xb000d06f998131be6604,0x96b9bf5500227bffb403,0x400053fb913aa0043120,0x9e837e9c0043d9fba040,0xf03400d14f3781500219,0x10f6f5da4004347f878,0xd1a35a400452b83b4088,0x1cff00304400110af8a0,0xe905d540087df003e809,0x3e5001111fdf3800cd6f,0x351babb48008667fa22,0x22004337fa7f1568c28,0x33b50397e100347bffd,0x1bc978290034e4a1fe10,0x60c8019b7bf5ff320122,0xd00903fdfe1c80486ff,0x20068b70e090010cbf50,0x460e022800888e1ff401,0xd01169fc190c20021d9f,0x740242f3c78160092bf3,0x90bc1fef2012178b9f,0xc85851bb9000888b9f79,0x17f3a011a1db1d880043,0xf97fb88019d6bfa1008f,0xc8800d209fc77a400d0d,0x3f9b20040043a7e3ea9e,0x63dd0019bbf08410033d,0x9c1cffe023bdc8400452,0x21aabf980a1a56fd8801,0x3ecad5c006807ecaea00,0xd09fffcfc57b01a801ae],#[0x8c0507780963ef55d800,0xf200650efe10400cf777,0xb77f1809ecfc8c0511fc,0x114bf1d008a5fe2400c,0x66a024abf978aee572b0,0xbfdfed4f820022178af8,0x4004493251fdc8400440,0x9989a8008701b83593e4,0x80086afcadebb001a25f,0xe9f9181d80088f0be4f8,0x8897f993800280044ab,0xe610010bcfff99386280,0x104f003fc82f1001106f,0x9c40044811feeef21001,0xf9fe7600218decfd3a30,0x25fbbf992e402c004513,0x2100112ef27c7b820022,0x4f8074200225de4f880d,0x33069ebd36810034b3c0,0x1ffd4429003487eb0900,0x63ff43b9097204004576,0xa408100115df97a90033,0x8fbff9d800d1affe82e2,0xe7001a21edec73000870,0x3cbe9d9240010fc5ffd6,0xf00a0008787e7c718004,0x87ce09ff10801a25fa,0x6ff28c8019cdfcded408,0x8008787f234820021f3,0x797f69104004393f8852,0x9fb58011e5f985208008,0x361bfe6a4b814002247],#[0x8019d3e5fe95d34e2008,0x921f64fb9029efdb65,0x2fe007600021d61e4d6,0xb2a8000222be267a000d,0xe597ac25cf00008ad7e2,0xb7044c04b8f4cb9c0019,0xbf2a57af8b1001ad7c79,0x28010e0d69fb660021f,0x895b79ac01211e1fcf,0xfaad00033f31e86fa2e8,0x46200117bf7ac00478,0x7fb6dd00033abf839b99,0x60021f32ffed93000345,0xc1fcd8e801100c3e2b6,0x4800db8e9f1d660021c1,0xc381115fdbe7f80d2072,0x456048002311fd3fe32c,0x7f6d128010c2932ff00a,0x18047a7e29acc094088d,0x124bd36c2a3800d3bd77,0x11e6df0114638a3a10,0xde6b3e9cc800044ef5df,0x8220dfa3f452e4000227,0x205200d10ffdd9361006,0x8008fbe960e602417f4f,0xaff4cde066201442fd75,0x43000680ff6aa86000d1,0x27c3b448961c0896f8d5,0xcabc047ce9f3249c0069,0x8400021b6fa88801237c,0xd48ff8a0c00010e2ffb,0x8ca000ce5f6f8e420a00],#[0x78bf02c51420004547c7,0x2a80045f5be21e400689,0x631ec01225f84181562,0xf7fc42008edfc8b200cc,0x3488010008b1ff044011,0x6b1ff044011c1ffe238,0xd5a808fdfa4bbda94440,0x6024a7aff00b400d0bd,0x3323f8f74000434f879b,0xcebf2e80019e3fd3c000,0x4040089b7eaee800086,0x7789c18800453bd9eeab,0x4387fd32e80019e1fea,0xff964c000d16fc511800,0x6ead4048cfe2d003375b,0xf1216a024469e801947c,0xf2ffecc80dec24006d5f,0xe20008ab3ea0b4014a1f,0x1a14fe0227b9ff31998,0x9a7fd98a02387f9fb128,0xeea340021a2fb3990002,0x48497d7c209800d24f,0x480088b9c890289f1c2c,0x237e5e6602393ff70018,0xf6a964001a07fb715801,0x2025d3fb41019ce04407,0xe6ced3814affdff55309,0xd3eba860122655e0231,0xffa480067a7079bd001,0x3c1a0021cbb0ff500664,0xabe9fb9e4018006a37a1,0x37b3f500688cb4c7c019],#[0x40010e5e623e550068ca,0x84fdbfe920019e5fd9b0,0x782800d69ff97805a006,0xa8190090008cefcb4b06,0x7eed9af00010eae3043f,0xc544006a0fedd0600675,0x129e9f8a8800d05b734f,0xb006757ffb5174954001,0xd6a9c24828036161cb6c,0x8747febba4a0021c397,0xed395900223dcf4e5640,0xf4e38bf458100114ef07,0x3200676ff88f12006797,0x383868d55400876ff88e,0xf50f200674f0f2f89003,0x8019e8ed9e110010e9e1,0xdd0770a480111df5f5eb,0x630021b5fc6ec200432b,0xce1f1986c00cfafe33,0x37ec3b4800874fafaf5c,0x40087d7822592c540089,0xffe23c0d0034d3e9b095,0x3dad011dbc6d28033461,0x4482de0e146ec9002257,0xc2002229fe0a7d418400,0xdfcfe84a01229fe2eac1,0x7e7854400d264fc2e029,0x8049368f243e1001105d,0x4a418fba01277f917d56,0xb9fc0804a1c9f500d009,0x44d7ffa009003389f8,0xae008008ab7779900f04],#[0xaaa02002299fc1351d,0x24e1c22bf0804a9737f9,0x3ebdda9001a22c7d4840,0x65000a7af09de8801a2,0x880f0fb3e20068e3d0d0,0x7eb50090cfd107b32800,0x801a721e78420068debf,0xa78f8801a23c3f1877da,0x420008762fbfc400cec5,0x50ebdcbd6f0022c5c45f,0x69462ab7c80087c64e,0x9f456a01253fb065f96a,0x448bfefdccb8400446ff,0x910010e0fe4fdc410400,0x7e7e165c20021d1bbf65,0xb75e88008866f10f2006,0xd528b55bcca0022059b,0x82000a72fdf5fae14040,0x67ac3e7c400ce77e8713,0x66e4a840045317dfe200,0xc9571618010f2f920e,0xc00878b8990e89940015,0xcd9bdc2002231d547c81,0x77fe2f05044440044eb5,0x354399547cade28008a,0x92510010fd5f72d32518,0x1a7d8e64e0dc0044122f,0x60a00227b5f5a7ede8c0,0xd541a91001176fffbc49,0x84e3ff8e08019f193251,0x8008af7dde157308008,0xcc450010de3787af03b5],#[0x400440fe3d0a011c1ff,0xe547c81c008727fab918,0x446b5c1fb1c2002221,0xab79002221ff93b70744,0x262d4ff01000535b278b,0x40021fde8f0135cc2002,0x6ffe05d1003413ff5b08,0x10e2fd9b2e60800884,0x1d31b7e900339be8dbe1,0xfd61a01205cdd1b62002,0x692fb7710e20400d4bf3,0x3c10011392ffe8441200,0xff888c40801a69c99740,0x63b90033b7ae82400cf1,0x3497dbb886c102006bcc,0xdd080029e3cf5fb05100,0x53f0d2b4100053a5e662,0xca90034272cbe9420068,0x8670f27420021f3cbf4f,0x32200223db24f0d08008,0x198bcbd08008737f9659,0x7a10010f9f72e5cc801a,0x75fa3c66f0c004433c59,0x2a0dffc936337860022,0xc70c00cc57dbe6008180,0x3307faca5e38600698f,0xe2e4e1b86002263f1c30,0x6836cff9420200110cf,0xe52e41001a1bfc32d960,0x1001af7f1595e2c02507,0xcae380484ffcbfd615a0,0x4397f0da01001a37a],#[0xfd0d70800044abfd86c4,0x29c561fc008e0f93,0xcc42c780004505f94cf8,0x83eadc4f9900008a3797,0xa768e000ceb3f28011c9,0x21e9b7fcd5008004447,0x1a11704006b27e394040,0x9f4c528080044271ffcb,0xa300053161c3ed1801a0,0x2b3e6d6a8300117a7c85,0x10008a6ec9f560067279,0x5080014eef0faff40ae0,0xb70605c56002234fe368,0x31a002205c7c0be80087,0x3d84f4c3400446ba3e2a,0x442199bf8094d80044b,0x2000044faccdfcc6f40,0xa41d3640002261eaeae4,0x215f76f83040004413ff,0x480004573fab46940002,0xd029000089a7cfe30e81,0x3f9ae9b2000110cffe9a,0x14c8fee830400043a,0xcc94a70e000cf478380,0xd09af0e000cc94fda00,0x99002001135fe83e48c0,0xbe0e696a2001122ffb11,0x1535eff9e90019cd8,0x66500008a9bcbbb63351,0x1dd80200022b5f13307b,0x68aed846c000d00f26cd,0x52e4000224ba7bd43000],#[0x12879e231e0048c7c40,0xfbc17000685ccfef5f70,0x2991f84174860022323,0xec81f86006bd3e42d180,0x1ffccc0e60021cbfdfba,0x8004463e5e4a32600222,0x86a2b06006aa707a3080,0xfffe45a1660800d5dff7,0xa00429de5ec120380a7c,0xf808ab1f43d08090697c,0xba18049de05dc6012456,0xc6011d73c2f8c0246f02,0x52b7e56c001997bd7,0x33d78cf800337df9a0,0x243c8be5000674f4e728,0x66d7fc9a8d54c0002,0xf6c007f496000d58ddbf,0xfc001946ff5340000a6c,0xeffe6764d4031a0894f6,0xa9006877ff708130010e,0x369ffc6cb003477e92c1,0x365801aebf28e0d48034,0xd09e1fb0032a6db683fe,0xcd2800045d7feb2b4000,0xea4540002259f98b27c0,0xfc20222300008a57e2f5,0x3037000681dde004617f,0x1a6bc6b3600068affa,0x66ce8001a8bffaf1acd8,0x30bfa8ae9800044365f3,0x881b80034cbe8b40004,0xaadfef2f4281702223fd],#[0xc1e003447f9416551801,0xf01141fc168010a9ff98,0xb07eafea768860022a6d,0x1747e01187175d0c024d,0xfaa130010cb1c5fc6012,0x20047a3bf3dc20001110,0x1a6bd134e000342d7e7,0x9070001a8bebfd2ff880,0x19f4fda8011cbf5d38,0x377f5c01000898f2fa70,0x7978cbc18e008004523b,0x426006a37ff821290008,0x3fe256426006aefde235,0x1801a1be1e35860068ee,0xef67ebe8000870fbfd1a,0x14d4791e84000014e,0xfcdd6200000a7a3c08d8,0x430010e1eded6c0019c0,0x22b9f94a40021a937fa,0xa0006897b3d08f07b800,0x67ab60b800022a03ebdf,0xac023f074fb0006797db,0x4527fcbbf98019d4fe7,0x18008807fe911acc38c0,0x4e7a4fda00cf6ff15387,0x2285ff04460e928008a,0x1001ac1ff2228480060,0xe6c6c1801a8bfd3ecf00,0xfeab2048008004507c3f,0x6006682ae06aeb0029ed,0xf600d1cab9c0085ace3,0xcd945f2b8033f7b629],#[0x239f9712000043b79676,0xf12000d22ddf94e80002,0x1967bff6a0047eff2dd,0x35d3f723240086ecfc0,0x9d2004724ff994fa3300,0x10f9da1f869801a37f,0x15155f6006517a0b57b,0x8e160024f9ffc4586140,0x80006877f24d00010dbc,0x1bf8a488c000223b8772,0xffd94028000445cce013,0x6967fd9c00460001130,0xec10800d21ff11d30840,0xd23ff7df3001203fe1b,0x4850003527f0feb68c00,0xc9fc3f3f3000347786c3,0xcfc9338053cfd0c00010,0xc023dbc9ff120ce70220,0xb6c0014b1f69c09d7e15,0x899b7c0458fb4e04f47e,0x8004483ffab990611800,0x69eb3c0235bffa84010a,0x2187d1f58c0245c7d02,0xfc80a6680029f1f8a060,0xa00cfefa333684002226,0x8fff2a1995006b8e14ee,0x86a7fb8840021bbcf,0x130f92cd0010d8ffd0ce,0x4a003383d6dabd482001,0xb62c46f834004437c7ed,0x21edfd8a82d1e68008a,0x472e0800222d8b2737a0],#[0xa0033c1fffa95004847c,0xfd58811034004494bf20,0x44b796de7bd401a0df,0x440d00112cfe12766c10,0xcbe86f740043e3ff4e60,0x50068f7e0d5804100044,0x407f35caa00ce5b79ae5,0x4a2200089cf78adba803,0xff59a51100044bb47b3c,0x6001a1b2f1f2ae0068e7,0x3f6ffa480068c4ffbed8,0xd59a7d1b1cf81001af1,0xc8080014e5f197809940,0xfbe36019c0015381fe35,0xd0400044527f68f00067,0xfc7d322080112effcde0,0x34d9fda432100029cd0,0x9e9c18035679ff05d820,0x33ffb501002198bfd3ec,0x458a841120fe0a020043,0xf630ca14008ae7ff727b,0x57808e35bdf808c6ffc4,0x39a5c7e488080044ef99,0x910100089efe7f182003,0x8f1fafc10019bdfc337c,0x800cf6e7d026df68f00,0x10f1ffc60800cc1fb7c6,0x4b3a000088e7e5c48000,0x9cfc13a876c0006a16ee,0x19a1ffb99924300008,0x45961f271e00ce5ecfc,0x3503fe68bc966621800],#[0xd714c00d018a7d43e300,0x19b1c5e9192c0044379,0xfd5d3d30000880fd57d8,0xd585ef97b70800d34f,0xfb3490049c2f7e87f108,0x8667fc00c240043afff,0xf0e28b800022319b0d00,0x80357b93a3841a08717f,0x100680043f43ff6a4602,0xc0044ccabc04647f,0xd5f70042a001148fe107,0xcc10019f6947e011fcaf,0x2293ffcc1001983f2f,0xd30801a11fd3ee232a22,0xe8ffb391820021dbf6a7,0xad9e5200682fe100400c,0x10defc3f6280086cfd,0xff9d80067001150f92cd,0x10ecff810e0021a1ff3,0x97cf023801aa9e8c80c0,0xd007fc020e000a6ef6,0x883877026efaf2db5c,0x3080008af7f92dfb3800,0x37e9c4c01a35cdf6063d,0x21bb9ff05978000d3dc,0x898ffe300019a5c91490,0x40043e3ffe2a80660000,0x33abf44800043626e2c2,0x3f7328004447fe72c800,0x410d0ff97eac00431372,0x27e281a80043bbe7f083,0x63fbb01c00863aeff026],#[0x3ff96011b1fdd80e0043,0xd7f91dec00cf9f4c00cb,0x1fb70010fd8fc77b0033,0x8bb9be1e8a38002a11ab,0x2950070f9a7d7d7ae006,0x28308a7886a6c92bbffc,0x87c4dc44b21c311fe304,0x6e2251d21b1203da8049,0x32910b8901c5dc0943e2,0x81fa86686fb5432e3fd9,0x19b334462230bf264ef1,0xac0a97abbfe05498fff0,0x9a391e42916055146273,0x9f876a840d61e5d7141e,0xf310528a195f6b1be615,0x19a0b2978658ad3c9939,0xd989860e7b74342145be,0x264c757c8a103f8426f2,0xc6fc8586e443161612bf,0x56466ae8682fe49939da,0x3234589d7868b4ce86d7,0x3e4e35ca8b13e271f243,0xb24910bafb2c22217c4e,0xe6dcd4c2e95ab436149e,0xbd1833b443c91127c2b3,0x10a0aaefe95a510e952c,0x4a334b4ea51156c5bc1d,0xb1c858720514a218dfcb,0x6b0a6fefb476e4300df8,0x2754b4ba46c585751ec1,0xb48af2f8015721acf80a,0x56803f8250274ad79958],#[0x85c7c585a12a59796890,0x1be2685754a607ed4c94,0xd212a5f3f89b644012a7,0xb84e97dcbb37c85dbe44,0x83fd1b8a4222510072b0,0x69d9867dd2]]
set_option maxRecDepth 32000 in
def g255H10 := limbs80 #[#[0x62c010d3b0600010102,0x11d0a10011204010316,0x51d021900000c030a04,0x1050000120507031101,0x11b1f0000000b0a0d01,0x20002040b1264000222,0x300081c1401010f0300,0x70f1604126901010c02,0xf2a0105000501001404,0x6100f080e0900030a01,0x40b00160705040b0f54,0x25100a01101707070e00,0xe04440e01190a0b0607,0x704560032071578010a,0x505a71d024702140d0e,0x628000c4000532e075f,0x4d1c4e10021911120000,0x101c013b0118100c5a4a,0x8e0803760f3402000910,0x75d050f210005020619,0x7003f01031e02030310,0x4c550b0b0005034a001a,0x3502000501102d28a815,0x1012a0025000000d101,0xc322e1c031124,0x3c3000038765179f6144,0x38a7871b0366a239,0x2c000b1098664a194f00,0x83f58400020de9c47c3b,0x613402e0008,0x47d89b295f68a061e568,0xc00000083cf5dfc2c02a],#[0xd15105872dbc0913a251,0x12d400082600ee28a9d,0xf3f3080023df0be52080,0x337749711980003039,0xceb26107f62bc0004670,0x8000001126000209a989,0x38f104544100019d010b,0xf95d28c7039000562152,0xa8000d536328000000c0,0x5a832748b2108c34652a,0x2d3a7d012e72e4f2e5e0,0x82800909fedf373dc415,0x5b66000874c92c001549,0xf00022ca4dbce0c8b0a1,0xf46043481a885b8419c,0xdc4bf31dc0011ccc5e22,0x8400105c12fa7d40fa9,0x5cfeb50000b4f8700002,0x43fbd0200046580033a4,0xa2ec29f8d18f6000,0x6c8d4066000303aa28a5,0x450a26269d89a2c7ae,0x24f3e0c9b9e56b480000,0xa1a0a1e28c977244000f,0x7a4189790860472b6,0x41f125c907b323c4a,0x3c6e853681f09ace8e3a,0xaf040a4648738eb82528,0x1c12c25dcbb402ece426,0xa7910c8608b7d65fa492,0xa2e6a93cf0a7a0103e0,0x4ab047c2a3a0281d6335],#[0x21ba2fa058154253d83a,0x569aa19e615c2545a2be,0x6ee3f24ae437962abaad,0xf641bb2bac0121aca4e2,0x8ac8b5aac0ccc000c,0x903e1b0a961880114864,0x356594200000021919b0,0x53929fead191d557a9e,0x8105321eceb86f740600,0x8287ae863d790fdc93c9,0x46106522ae0388bdaea6,0x88346ca6832a42f8d0a,0x95c800090caf903b4001,0x696793f242c1e4cc5a94,0x7810000828000655227,0x1cbd833c7ea54b98048,0xa1a350a88089113a2fc0,0xa658728003498492c,0x1113333851cab6775938,0xc401a4200024f24c8000,0x6c59854f98e940aefca7,0x23be04e49911a535e1b,0x262cd03df80600000000,0x87422509807144281fe2,0x6a9d6307fd56644f431c,0xc194171535a2482303cf,0xf67a6d6e1a409220e54e,0xca8f0a46a5543533b113,0x68b0d2d17c000c1602,0x9a0c136724093402740,0x5120c0b2ce17800143a8,0x51380001f22d37211],#[0x6109ddd61f056351aa2d,0x4d1eb08b340cb20002b1,0x7307c08052e000211785,0xa66c7a63d0000d3e50,0x11212c1430800238a0,0x993150000147e0000000,0x186f000610c2a1,0x29104c74aa00fc439000,0x580014341a3c3b39d353,0x7c2aacedb053915862cf,0xa5da3a3058dacade8a62,0x9e24021404648000000c,0x30346bb0bc0003,0x23380000002310000838,0xc4e500021cc000542425,0xc00002be0fb800352498,0xae66e49ae537842eaf62,0x6fa4dca0c4daf454000c,0x1060dcead480811e877c,0xc44c00180d000630b299,0xc9830c50003bde9eac51,0x8293b15f08f897647016,0x8185423781f39a9ef,0x4771f422200072f80000,0x203ce966324b49a72565,0x9cc1ea27e00007e79b7,0x1ac0d800047d0001133,0x2104ea064632ab494e9c,0x204228c13e25b85264,0x44f1ac9139d0a5284e00,0x2069a2b65d00033701,0x97a88488d233c94a1338],#[0x202d1ae8bb66580001a6,0x3ac0ccf80025735928ba,0x189bc3454748e9e94d08,0x6280c0cee4c2c8d18b88,0x2c08963830e790510b85,0x1413000488310f0527,0x4c6a1fd06e9cea870000,0x40000000000001b1e000,0x4cb2d0cd01f2c4c9625f,0xc75d54c0440011b,0x3d46fc92ab3000000000,0x18b900005ba4160,0x62953d63db9e05388,0x75000140a00060b0080,0x60000000598b2a55d14e,0xba70a0a2931e59a01047,0x86000ca7651925468f02,0x57a115787bc18b1535,0xb8a0000,0x26180033c29480000000,0xc4369c304ca9501831a6,0x5a438614d80e10222d,0x40bacf0000088523600,0xbfcf333b74a2938caae5,0x382b59d91527884f0002,0x1e427941214108f486dc,0x515c001915b0a40da333,0x311a68240eb50ca97152,0xf0317a3842ac5488154c,0xfcbe09d7304bb90bdcf,0x56c01f9611b2c2223903,0xb15cf64c2e06392997b1],#[0x664364001ac20001327,0x19380aa8d8871d4ef2bd,0xa346026c2a58106ac670,0x8c007d73d3da348b4bcc,0xbc51c189384702b34889,0x12c001008d2f225d3adc,0xeb000431e0f0000c906,0x401a148845d3ae6ba459,0x900100059700cd00a275,0x9ef4d9239a15942,0xc260d5000000021f00,0x782749096c31ec4940,0x6a322e08cd0,0x26bd2ee32f1280000000,0x607e00051ce3a80009fb,0x43b8000000000903052,0x60124e17000000149200,0x1940e4547b5200000026,0x71b08f17f0000aee49a1,0x29542ae8eb2b9173887a,0x1358000e83d07c21422f,0xa94046976c0002b7509,0xd00033c6000890a7f21f,0x92451bc05308c60587,0x2f47bb1aa4f90db80000,0x336893cec37d40011ad2,0x240000000002a1f,0x13121bc0000000001a8f,0xb2c9f217036a2ea64000,0x20b786bc0f73bfbc15a,0x1200b00010c8ab400000,0x1431e00020375680000],#[0x82f84ac966a185630ece,0xa4bc001176519280b03a,0xce6800326c000e36,0x66418180004eae2ba57,0x794616d7e05626b8ba00,0xafb4e63592764be33015,0x9b148865fa6101dc0008,0x64cc3c1122164e560001,0xa2c6576e402779521956,0x8df813cc100c60004a5,0x1d8000c7189a580000,0xf30000000000c898fc80,0x5890b4e6f0f135e1b398,0x834484400188e036d,0x47d44993483980021a0,0xd4c0001032000000,0x1c2b54c4c2d0002a9c00,0xc4000e73e45005a460d2,0x4f2ab800093d00042962,0x32c15700000034ae0008,0x696c00085f0000001,0x6ce203c0000003937c71,0x46e48d884f82300042c,0x994e600000065c756c00,0x2394150452f39f805029,0x56493054e10ae1cb3491,0x9c4523e5cb446cb88ed6,0x50d92564aa4ba89699e8,0x68800000008213d,0x54050b]]
set_option maxRecDepth 32000 in
def g255D11 := limbs80 #[#[0x5953258d325893254932,0x5d9325d5325cd325c932,0x5514361d326193261532,0x5d1435cd435954359143,0x61943615435d9435d543,0x5915358d53e1943e1543,0x619535d9535d1535cd53,0x5cd625c96254d6261d53,0x5cd635956361d625d962,0x61d635d9635d5635d163,0x54d72e0d645d9645d164,0x5d573591735d97258d72,0x6157361173609735d973,0xe1573e1173e097361973,0x60976e1974e0d74e1973,0xe0d76e09766117660d76,0xddf7bdf6febfcffe1176,0xffdf7bdf77ebfcff7fef,0xeffdefbbf57e7fcef9be,0x7fbfeffd7f7feefdbf97,0x594b39763dffffdff7fe,0xc06d6300d5d91c175314,0xed7302b61c02d8601b5c,0x9702b61c0d97602b6140,0x925d822d8509b58c215,0x55d81298505559412d86,0x142c5750a465c1298705,0x193960aa6182c5760aa6,0xd870e8618381980c0660,0x7120e54483980e066039,0xf5d8f8396140e545039,0x5d96039342be490db924],#[0x872b851d15d474b925af,0x2785189e185ab861d15d,0x861e3e547a7851e3e546,0x280658a0396243e587a7,0x65ca81952a0e5498197,0x5cb29872d55d8b61752c,0xd139630a618c45763046,0x398340660d1d87348618,0x6380e48e0397360e48d8,0x715d51d565464e491839,0x61d2bd764a861d113954,0xd383924e2e55357934c7,0x9d766a0655a83954eae4,0x966c0655b3d765c0659a,0x6e75d9b81926e7e19781,0x4e4da0795611e4d80196,0x5552574540655c019270,0xc8f9350065d521765406,0x1937c064dd0196720655,0x3805e49e81957e0649f8,0x5d5942757503d5d80019,0x6582f1950bc5942f1750,0xc1b1870775d81e57507c,0x31860d35d8375920c665,0x920ec5d8431980c6e583,0x3cc66039b950fc64c3f5,0xc61cedd763bc5ccef553,0x54fcd753fd648f99973a,0x5f16357764d031983e6e,0xd935b7595619965735d9,0x51fc658771951dc59474,0xace1c6dd761b95d46e96],#[0xe58833862135d8819971,0x89b9522c5d8a3298206,0x716431c648c71742cca6,0x762fa5d0bf19631c650c,0x32c618c9b972ec61cbdd,0x6e50d7193346e48d1b96,0x50db39236c648db19834,0xe339736c65cdb39436c6,0x39438c650e339238c648,0x447c6491b39638c658e3,0xa6e5525d6549c6551f19,0x65929b944bc64d29b924,0x135f924d7649331984b7,0xdf954d765535f944d765,0x944ec6513b3924ec6493,0x6335d58b3954ec6553b3,0x35d5731866335d98b185,0xd591b985c6e55733855d,0x94d76646e55931856535,0xd7667361979b9664c619,0x261364981b9666c6199c,0x1365584f9461365184f9,0xe55a7393686e49a4f956,0xdf3183777e4d4dd93526,0x1b9278c64df19937cc60,0x8578c615e338478c611e,0x7e6655fb1847e6e55e33,0x664e01b937ac655fb194,0x58879953fe6543f9960c,0xd7b9235e648d799523e6,0x9944be6492fb9435e650,0x467e6519f99267e61577],#[0x9e649a7b9667e6599fb9,0x655a7b9469e651a7b926,0x1e7b9279e649e7b9569e,0x798579ee51e799479e61,0x2d805e0007b9579e655e,0x25a07d819605181080,0x847e10783c60dc03200b,0x64217e05b815b8520133,0xf61eb07581c306c01a30,0xc260891c23688a021787,0x2df0b302be0aa229589e,0x5b8d103310c6c3048bb4,0xb0eec3aa0e5e3868dc63,0x107640d8ff23ec0f683c,0x28848311d045e910242f,0x4250113c44db132e4b79,0xa58295a255514ec52c94,0x60c18085e697505b6166,0x7c19aa65298ee6301884,0x51b8a6cb9ae469e1a306,0x1dda75b1cfe7259c346f,0xf8e7d11efa7ab9e74788,0xae853a0d281fa0167f79,0x48da23128ae225e88221,0x9662542935a47290423c,0xea27569c0a69e994a5f8,0xf299aa4ba8cea19a80a9,0x2bf0ae42b1caa9aa52a7,0xe3cb74ad72b402ca4b16,0x90c0cafdabdeaf1cbaa2,0x8c9e3222c6cb144c39b0,0xd28b45ecfa33a4cd5b2e],#[0xa3b64ad793594d5234e8,0x5b846e0337aadda36fad,0xba70e803984e48b8d8e2,0xce4f1a3c14eeabb28eb2,0x4afbe3e76f893daef4eb,0xd047c0cb01bc016fedbf,0xdb42f70aac253078c17,0x63c535136c46510643b9,0x447131b9466f19045f11,0xc961242c8b1213c7df1e,0xb672c04ac129b4a1926c,0xa9354cce131dcc132f04,0x93eacf513b94e893854d,0x489d1a3454d101423501,0x28d4414f6535b4c2d293,0x8d68f58e55c1559d50d5,0x58d761dd8075e557315b,0xaed6a4da4d67e599f651,0x9b745dc9970adbd16d75,0x57f3df597bdde777835d,0x896e1d785e60ff82c604,0x2de4478fc637f8c9e2b5,0xd66df99b65ed961650d9,0x1c2e11c0f019ff679f9c,0x1096061f432157100cb1,0x143b0e21d10c330a0c04,0x1c302508017430684dc1,0xa892300d1270c1300a85,0x68807e1d86741f0942c1,0x1c02e12a320a0850d83,0x68681b880828db060e82,0xa1ce0e0280dc38222011],#[0xe4b921832268407a1b61,0xe09f068a8a0279328888,0xb888a62460a4942908c1,0xc4d3261aa164390d8905,0x94812309a28038381808,0x81140611874229550ae2,0x6e50a503853498421384,0x5c112c501284a91a1789,0xa07c400f85c020561660,0x2cc04d6511018c16c843,0x8d22f24064479522698,0x25db800676f29e2c400d,0x3f39404fa3d79180486d,0x58f08300682f9e530066,0x4c01a0bad831d300682e,0xc9cadcb2400d11cba53e,0x5feea790091dc3d3a00c,0xa7b1a0068af4e9810067,0xe9e00666f9e530066efc,0x97e00659ee3b900901e1,0x37fa8c008d977c008c9f,0xc005259e0135f73f400a,0x1400907d9cf20145f7b3,0x8200683ffbd00142ff56,0xc00c83eb800464976ff0,0x5f931003437e400195bf,0x346782f9580001a429e,0xa3f2e000664ffe978870,0xcddfc00c95fa7b40019,0x344e70022b7d5a00,0x33a425f848019c2bfbb,0xce9cfc000332439fb10],#[0x4f69e1200670fbfec000,0xa8fc3b00a07ac8d80049,0x235fc66005073c1e002,0xfcc1808cb27602368e76,0x273edd3c09ce867e04eb,0xd00239f4ccf0273a5bf0,0x9cb6fe97eac4001a97d4,0x351e1b804f94fea4001,0xf52000ce5b7865f41680,0x7bb30278bfe444047cb7,0x7bb28146afc288c0248,0x6cbe140a001aaf8b2814,0xbc3c2a40034de79409bb,0x412001a46f598c02447,0x1a79fbe88a0021fbf83,0x1809000d71c3feb0210,0x2001ababf4800cc1efe1,0x25000cef980bdfe08a01,0x676f380cfcbce0457f1,0xbf957b2001a33ffcd060,0x8fbd3a808c979c6011c,0x47afc2100400d3bfb808,0x3f886680068bf4ff5014,0xff09110033f77d040198,0x2200690fff0291003397,0x7f9e9c4c10069aff7448,0xc60118bf2ff046100348,0xf8c022cfc73c6008e3af,0xdfcfba80a0fcfb250285,0x55fde758047df3802023,0x70ff0a4e06006998f004,0x8a43b4001aa34e683006],#[0x671f35fea000492dba7,0x74e30b2600ce1f31e900,0xf72e2000ce5f3a6d0006,0xff0d009194c79c0019c3,0xd2880925fba200334ed7,0x69033c15e20021e67f3a,0x6ec54019e3f8dafd1200,0x3c00ce1ff4812200d0df,0x68bfc24f00a1a5ff5,0x29db8d7e00122bf8650a,0x7f738364009477df9e00,0xa1900068dfeb8d080123,0x88dff3834200496ff9c,0xef96880128907b58d940,0x440019d632beba0246fc,0x4f7f48b40bc0006acfb1,0xff90092dfff992260003,0xcc3c05d7940009639b91,0x2b1ec7780024d7f90000,0x70001a33f0ce5e9dc00d,0x4d7af8e930001a62ddf8,0x8364009689ebeb940003,0xa2a294c3900340f97cff,0xdfe300019e39e5e34001,0xfd40055bf1f9eb201223,0x34c710ff9000670fe7,0x2fe7b0001a903feb2428,0x4000951e7f5c0019bb11,0xa7f9768000d23ff8df5a,0x67ff00138fe5f80047ce,0xa0047b60f34010800112,0xe12000cf5f7d700a14e7],#[0x8ae01544e1fb80535f9f,0xa06ff95f5300249fcb,0xa75c46faa000088af677,0xebdb80515cbf59014001,0x9998023017f0940001a0,0x52779e90275fe2e70047,0x2fe301d46012896fbc20,0x200d4dffa60658e08035,0x508f333809211f8dd588,0x613200d6be7fd4830120,0x987f040401a63f6e3f10,0x940c00d6bff4a5802427,0xaa2ffc358024353fd2b9,0xf840069ac7e041b46001,0x6b8f5fc2003307e5e56e,0x6800cdd9718f5e11c400,0x682fbbff322001a63e7b,0x2bc6cf0049ae7ab78300,0x43f4012471fd0fd00489,0x420256fcf10fd004913c,0x589c574a101307f38ae9,0xfcd840a57f1ea0201207,0x330ffaa1c4f11804b21,0xcb55cff8a200d11fd4c8,0xff875c830034f7f86800,0xcc003387e65e50019c3b,0x8ed1fead4800680fbf5,0xc02006a4fd80dbffcd20,0x82001ad3f60347f0d0b0,0xc1913f280901fcf88279,0xf01202b1fd1c7a940804,0x1267fd9cc1009279ffe],#[0x12f73191080923fb3982,0xcf13438091be73142210,0x57cbd4050b9389ce0246,0x9420c0491fd666079009,0x20e01250fd943809123f,0x49f94fe8520068d3fff4,0x39e0126bfae9241cc00d,0x3537fb12481a00d239bd,0xd6690092dff4d0171100,0x92dfed102290034aff0,0xf53d6a46012b7d4bf230,0x25cf1fac459e300973f,0xfd0810091bc6b8deb942,0xc258201327ffd82011c7,0xff0226020069dfebff5a,0x123bfed4d0802001a83,0xfea080180801ac771885,0x80953c7dba74900975f,0x7ff8a840001a04f9fa11,0xff3d602a8b9f1ea60241,0x929ff4ac4d82400d5659,0x20d7f8680488b33f0d00,0xfd7c4c100927ffb8c80a,0x404c6ffe7823010034af,0xfb73814049598fb27888,0x80242d6785fc88404bdf,0xce1f43b9a0068dfa823f,0x1206fb2a023b78ae0400,0xd77400900348f87ef5a0,0x90deede96940003567f,0x8cc3b70001ab7fb31ac0,0x6c6a61f80413c000d716],#[0x9001a73e79402012e000,0xaf2f8d2003416c1f875e,0x676e61c54f91a4006c2f,0xbfdb0800d3dfe9dba400,0xd79eb3f843400690ad3f,0xf7e008e21791decce025,0x931c3f506c364006a92b,0x18b03c006bdf9ca1fa00,0x354f8deb990122b8fe1f,0x404080498fb7a2992200,0x925ea15e9464006adff,0xfdd8a34c00691fb9cc10,0x1a200356f9fa1240488f,0x7fa63a32003417e9f81b,0x34857fc21f9a3200356,0xdce6080494fc31f4a320,0x240491e3ed278920258f,0x27fcfd0920246efed3f]]
set_option maxRecDepth 32000 in
def g255H11 := limbs80 #[#[0x11c0401000112020402,0x5310c0700000004000a,0x60005000300000e0c07,0x10804040201010206,0x1060209040707330005,0xa220210110006130700,0x200000800100c070000,0x104000b06190c070609,0x3900110804031002004c,0x107090002040f030401,0x3000000220107011000,0x2e010309010c0a010a0c,0xa06030000111a0b0001,0x70c0000040004041611,0x220a071b0307054c0721,0x201010f1c0107011402,0x1340d000a020a010500,0x4f140208130005040001,0x20610280a05140a40,0x3170d02000341050203,0x14021c000b05000e1202,0x1b13052a040f4c2c0000,0x4030a00120e01110f2e,0x15440000010103041093,0x4107020500031d01030f,0x90000000000000198ca,0xad9d5b00031ae0000006,0x214a0008c20000000,0xd22d0000146c04000c91,0x12400027d279fa4,0x1b232c1c54a8000861ed,0x64e1401a9dfd88749999],#[0x22abb914a4c12e4809f,0x161731f1fa03585527fb,0x34e34cf0fa34c2065936,0x78c1d85f8d1078c45246,0x8a15c000d0b800000048,0x1100037902ddd58c2dc2,0x250b1c10ded080000001,0xcb546b7a733860002146,0x17401e8dd819a1cd,0x1277c3dcaa12e6000cee,0x23800006b2fe000000,0xf60c59468733b14a2300,0xf300012b892b8bfa5d93,0x15e96054008d40000008,0x55a2774001a0120e8001,0xd12a04e935e8e4a37cd1,0xc66768364712a24ec28b,0xc02628484ba62995aeac,0xd4e285f954a00000035,0x10400092690e0197d0c4,0xab7a6201a70998a34a88,0x800333213ba9683bd835,0x2ebfc3680000001f2c19,0xe800033e000000016089,0xd149c0ff1553b4df483,0xa4f3c0064304aafe1,0xc1eaaccbe80032d20000,0x53080001ce8e83425b8c,0x8d30000115e31206e08f,0xb00001c31f78c0c53952,0x34000d1900037e0000df,0x319e49900029],#[0xb32000a0c57b31fe0,0x4aa338a85c6e8,0x2b12ad30007367478,0xac08002b0c192000,0xd02221eb1b6722a69000,0x899b0c60864451200081,0xa931113f116c00000022,0x40c9940006876aef55c0,0x44e417e3bc0638ede7b2,0xd0d19f3a5583d15a9439,0x87d06df49000000065a,0x5b440000000412c00000,0x64865c55c001211463a0,0x2b0f119e1220080001,0x91400003cf992000b068,0x814c000cd742000034ea,0x9a3446e355949692c3c,0x33222aae3e5c94e000,0x19e44e2000033400000,0x4566836e6dcf0c9580,0xc2a000b0b6b340e9a6a0,0xdaeb588cf48944d8000,0x23fa0000000003518000,0x234c000000000,0xe7ab5c224b7800000055,0xb215332c240000002a,0x4c91a1588d3900032ea0,0xa1800000000009fa0026,0x63e02215e789f00004ec,0x27c0004b0e8a4d28000,0x9c1042028545c5e189,0x69d48d500000018a800],#[0xbc22f08c9b800008850,0xaaae38b440000000c,0xe9641cc0012a7cc5299c,0x85e9ce2ee710bce19ee,0x7c91807400127dafb000,0xda1234c8012e961b305f,0x6c23e8000001104c8b01,0x22c001cdb2858000057e,0x971e01f9bcc828c90749,0x1f60006700001,0x127c00000000115dc58,0xa248199445f00002d400,0x9e300029e00018300d,0xfb80000012af02484cc0,0x1d4000884847ba0f27b4,0x50956a000000000062df,0x1168d6514731f2000,0x4b8a0400042183a800,0xd8000000d28011406c89,0x73c03000119400006423,0x3bea0000002558001c,0x14f236d2e84f4000d1d0,0x97af32e000d04c724001,0x7ab201a238c492022297,0xc28c40008540001b6029,0x9694cd3f706630dc2940,0x2269398df082525e2643,0x26a166360e392216a0b0,0x8968b6e281067d48886f,0xb40a00000009cfbffadf,0xa00028dc00010700053a,0xb8000000edb000000195],#[0xb00fc8b400011120e7a3,0xaaf87918723d8001085a,0xadda0700012262cb41c8,0x626916c1c788e4b3a203,0x2000000215d40e00086f,0xc027b9d600012f638a31,0x10a945fc037a1b43115,0x2b7a9e40,0xd6945940000000,0x923431a53b117f000000,0x228b1c2c30315c3ab106,0xe0ac0b8514269000000,0x60000585470800000000,0x674443352e8e0ea,0x2f600000000000000,0xcd2407a54d0b587a6b90,0x39400118844c03464b9,0x89c81200001187a10562,0x6a6553e3c90531d15a41,0x498fcc0e058f04e43895,0x46098a8a8bd501690c2,0x1a8f00065a94a32849,0x4361552d73c9774c4,0x53b3a1300000038a6000,0x11ac996000532497,0xa04029220517800,0x120dc800307a0004df80,0x82aaca06bebe40,0x6110dd04328460002218,0x5920316ba40422c2,0xc2be000089d43e170459,0xf44de1be00000000008c],#[0xf8a82a9d038000019e4d,0xce80000000000004ae93,0x4a6055000000186da4a8,0x22d0336c8e00da77f,0x20b9a6da062b2315b903,0x70000057a4fa9cd30000,0xc13411280002b7142aa5,0x8096aa0500000006bb08,0x11210a0b1298418,0x9a88160a90000a1ac100,0x3a2d0e36107352403272,0xcaa600074de300ac5292,0xf474a0df085c588001b3,0x161412101fca0ddc982,0xd0e4a400125200046380,0xefc85184149e84,0xca1eaf0000000000724c,0x7094000266c01686a11d,0xf24467345321ed0000a8,0xca8e11d0107aaba85ca9,0x4fb09e6b9b160004d603,0xa4a8170b9b39a8912350,0xd34de8000001a444bba,0xaa7892307228743aea64,0xc83f000050a2580b38e9,0x464c0009c6d27800217,0xb4967cac000052900700,0x63a52888b0ec89d00035,0x29da59d4d80003c4486b,0x244bd39294c8ed,0xa1419b3959aa224014fd,0x1ab7000217193cc4611b],#[0xc5a6b9a252f8b4729080,0x9d8418001b092c195066,0xb1119c0000c2e8f71e3e,0x4d23080020275340007,0x10f897a4f50001113,0x4000c697a58000d2be49,0x775d75cca5be28000103,0x8c000d51800125f99093,0x58800335b1f0014d0455,0x46c00000020200004109,0x4460004b94,0x32bedfe000427e5c4a34,0xac05036f5c066b0aa000,0x3a811ff00040efd819c,0x23e0f800000000013a00,0x7c00000000000008,0x33ea0000000,0x643c27a80bd4180011da,0xc0001678000000000000,0x398f705a4e3000096b44,0x19e9227a9140018a196,0xcb24e0a3000000000000,0x4d0000d266428a1f9a74,0x861018b9f0a0e94d4275,0x400145100075c4001a62,0x24c102ec43da86a59641,0x6f23e000523800000196,0xcd000000237800004264,0x2bf480c33880033180,0xa16c840000001c300000,0x8b840000009155a52cd2,0xe000532d0792bc955cd5],#[0xc9494302000254236431,0xdccf68a805f0000000cb,0x1dc12d85990a00020,0xd4000000000208e0000,0x20e00010ba0000002159,0xf58187e6f9f340c16d3b,0xfb3917005bc90215a821,0x5c459019eaa751d84ea3,0x5055c56d31a8f04d294,0x758001043a3f67944d84,0x60112a275c52a93f2bec,0x262c29a92500026ca5b1,0x7a90c7f59ba15800046e,0xb9157a9eb13fd56712,0x43dccc20bc450c9600,0x26a4000a8e00000000,0x1d96d81e00003de0000,0x119e2904de0000000001,0xc268a87307000000022e,0x546d68880d98f7f1ae51,0x1a03000000152da5,0x347dcaf14b80]]
set_option maxRecDepth 32000 in
def g255D12 := limbs80 #[#[0x5cd72591635895350d32,0xfeff7fbfbfdfeff5d974,0x22c615720ab1055483ff,0x5c8c30e018600c2845cc,0xa0c5cc4aecc18734bb1d,0x11c2886145ae82d6416a,0x17328b190e1c470c2186,0xec896548b9a061c830c5,0x5caeae38471c13861d12,0xb5d14706a38672bb38e1,0xc148e1a0707038754bb2,0x60cba865940709238391,0x39636ca9b65ccf2a6797,0x2e859642cbb0e5d472ca,0x91f304f9754cba265d8b,0x4e60a730cf9857cc23e5,0xdc24e612770739839dc1,0xb709307a061044026000,0x11941771501301120e40,0x27524d23120f1f51db1c,0x513393162f02ce2af292,0x83fc3db3b83a238a3723,0x4d74b549147245043941,0xc559f57e55b5375154f6,0xb6b668365e63960d5e95,0x7e47b878e76673e7086d,0xe28c18a288a85b83a80c,0x88461703809599349058,0xbc1e1e0687c40670c1,0xc2a14428a8100d092191,0xc1c36100388034118320,0x98a07d104dc340cca0b],#[0x250e83e24348a2422293,0x174a8ac2d24990280c86,0x71fc28e011f08488ca5d,0x3df803b3ff601ce5dc02,0x943fe29008cfe9008,0x27988f9700012a6b9a36,0x3dc00a6ce4c00a29b3c0,0x8f8000012576fe0107f6,0x66c0437bd80d5cc8134f,0x23c79d013dfde6404ef,0xf000273d380138ff8884,0x122ff8010283f33604d7,0x140417fa0502998f1450,0x38087e6807df18a0233f,0xa0507f86900a1f98066e,0x9f9c500a1fbc701efbe0,0x86c0283ef9c009d79c03,0xf7fce0013ddfce001459,0x1e0141f37002727fc004,0xde07805072d9980534df,0x40779f34052bbf280463,0x2489fb94023dfed9801,0x461bc7a4023ce7aea00,0x90bf3fe7c5c056bdff00,0x2ff3399800557f5f4202,0xe10d02a0ffe87f845c0b,0x8ca0049b77cc0902aa7b,0xe100a5722e624012879d,0x8029df8f18500126ffa4,0x28079fc0f80200936e70,0x290df1e01458e3c0287f,0xa878f8cba0024df37280],#[0xfe3c013995f1e00]]
set_option maxRecDepth 32000 in
def g255H12 := limbs80 #[#[0xc0000004100800218182,0x18508001c28000186860,0x2840a585051e4018700,0x2090a0c384020460c400,0x1a122021d08000220024,0xc08000800860e20343,0xc0000e38600001c00,0x47018028043010410329,0x3428e5810b800200c8b1,0xc00338341c00337b1eb4,0xba43de0304008f721846,0xe8cf8c51730afbd22a8,0x3a6e3f31c282c00209cc,0xbf02d8a682d134000000,0x23200012c4000000,0xb48511d474002c380000,0xbbb2b72e1b36a7e9d29a,0x12442979980000220e9,0x1b0002a780078aeac80,0x117400035000000000,0xdd25e2680020c22ec000,0x2408001a70001bd80039,0xc1400020c0011f813400,0xf616f2fe0910e4003a47,0x202985d214000003c742,0x4380010a294609800200,0x2e410000002058003234,0x30f80009a00000000002,0x21ab14400000000,0x700003000033081f128c,0xbaa193c0000000031972,0x222400000214004],#[0x238800243c000,0xf28800208340400238c0,0x12200018161101c,0x83e87eb39260b14,0x8003a9135d4411581bc0,0x7000035800000000047,0x1c1c0001dc000001422,0x29353874600000000,0x22800000015c00337505,0xc99b734407d23c0d4010,0x442c36118a0ce06b9063,0x44c07b1d50b606c2f12d,0x1933444a052879c8002,0xc0018f80013e014e2e40,0x18472b303af0f0003b5,0x5a1ee849b3c0028a4096,0x98a39540e2,0x230c0032c80001d,0x53183c358ff9e8bcb088,0x40b90d00023569032774,0x483a1012a8780340029d,0x14c0905f3353980001e3,0x800139c9b80020440604,0x89400000385b117b18a5,0x38000b970669fe9f4bdf,0xf46a812be43e405703c0,0x26531f04fb219eda0901,0xeb3cc3060b20432a3bac,0x82ac3c7240b7db2c0ed2,0x4540030a80000023170c,0x14003326121430000206,0x40000000000000032a50],#[0x252b43bcd0741261b736,0x28000b1f0842553b0002,0x3db19d1993f800336ab,0x12d4652b13e800000,0x8208000000000000000,0x30d80000002780009f01,0x1050de2398a331b3fc00,0xa127d1c62111adbfb34f,0x42df16116b2bc16542b3,0x24fa192f89f833a37015,0x1311130000002a5c001,0x841c131e41852331780,0xbeb29800314a1a0000bb,0xaa24847ec20001328943,0x13d73913,0x87400000015000283000,0xfe1000000001a510f34b,0x33013c0001ca0,0x11d80000000a400,0xc000000096826e8bc000,0xa3b700a81c2810f40002,0x8184240030bca4800213,0xfe0263efbb40000031f7,0x3883844003bd41,0x119320245f8d400000,0x29c00133c00100cba8,0x69752bb29000117c0000,0x18c0000000000000003a,0x2828000000,0x1a242cc3d00033c18f2a,0xa1d3f5a9844800000000,0x18000003a8732d0c40e2],#[0x337d11800000108c4884,0x194f36c00302c00000,0xb821c000003b273bc000,0x245b1b8000b753]]
def g255D13 := limbs80 #[#[0x2e6b1aa6a1ae4b1265ff,0x4f0bc8a5a2c00bb2e8b2,0x70f0c110b0301bd975d2,0xa28221a0c160e0710950,0xfc803bf800e2e3224202,0xcfe6603bd50029fe801d,0x7f388053fc3404de4804,0x51c0432008]]
def g255H13 := limbs80 #[#[0x61c00018180820018007,0x38226001460300c81893,0x9b98f400c18270012380,0xda1c0021ab44411c80,0x61b01643003190023186,0x8400012400000c8bc2d1,0x4008f33a45f15a5725e0,0x83947e28c982e4cd204a,0xa14aa82a673354c236c5,0xc00827a72f3210012b0f,0x20f4052f68c4402,0x681ec9aeec000828378b,0x80e00000cfd120011e68,0x1346b000e6c0080db5d0,0x311a3907002ba8209281,0x1adcec000001d0000043,0xe964cb13400000022d00,0x8ff0f1a904000e0006c]]
def g255D14 (j : Nat) := if j=0 then 0x70c1418802007ff else 0
def g255H14 := limbs80 #[#[0x4b84030ea4db000085,0xc400000ce000,0x119444008c000000248]]
def g255L : Nat → Packing
  | 7 => (4,7,7,0,0,6,0,g255D7)
  | 8 => (137,6,7,4849749,119,12,1156,g255D8)
  | 9 => (712,5,7,12190016,137,15,1463,g255D9)
  | 10 => (743,4,7,6553829,120,16,1333,g255D10)
  | 11 => (291,3,7,2031681,87,14,1180,g255D11)
  | 12 => (70,2,7,458762,52,12,1086,g255D12)
  | 13 => (10,1,7,65537,0,8,1045,g255D13)
  | 14 => (1,0,7,0,0,0,0,g255D14)
  | _ => emptyPacking
def g255I : Nat → Nat → Option (Nat × Nat)
  | 8 => lookupShort 1 17 0 5 2 1 g255H8
  | 9 => lookupShort 49 733 3 11 8 1 g255H9
  | 10 => lookupShort 245 1213 8 13 10 1 g255H10
  | 11 => lookupShort 249 1361 8 13 10 1 g255H11
  | 12 => lookupShort 102 607 7 12 9 1 g255H12
  | 13 => lookupShort 24 127 7 10 7 1 g255H13
  | 14 => lookupShort 3 37 3 7 4 1 g255H14
  | _ => fun _ => none
def g255 : Forest := ⟨255,14,fun i => g255Y[i]?.getD (0,0),g255C,g255A,g255L,g255I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P7_0 : block g255 7 0 4=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B7 : block g255 7 0 4=true := g255P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P8_0 : block g255 8 0 54=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P8_54 : block g255 8 54 83=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B8 : block g255 8 0 137=true := (@block_merge g255 8 0 54 83 g255P8_0 g255P8_54)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_0 : block g255 9 0 40=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_40 : block g255 9 40 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_136 : block g255 9 136 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_232 : block g255 9 232 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_328 : block g255 9 328 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_424 : block g255 9 424 71=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_495 : block g255 9 495 96=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_591 : block g255 9 591 96=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_687 : block g255 9 687 25=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B9 : block g255 9 0 712=true := (@block_merge g255 9 0 328 384 (@block_merge g255 9 0 136 192 (@block_merge g255 9 0 40 96 g255P9_0 g255P9_40) (@block_merge g255 9 136 96 96 g255P9_136 g255P9_232)) (@block_merge g255 9 328 167 217 (@block_merge g255 9 328 96 71 g255P9_328 g255P9_424) (@block_merge g255 9 495 96 121 g255P9_495 (@block_merge g255 9 591 96 25 g255P9_591 g255P9_687))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_0 : block g255 10 0 24=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_24 : block g255 10 24 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_120 : block g255 10 120 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_216 : block g255 10 216 51=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_267 : block g255 10 267 96=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_363 : block g255 10 363 96=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_459 : block g255 10 459 96=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_555 : block g255 10 555 96=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_651 : block g255 10 651 31=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_682 : block g255 10 682 61=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B10 : block g255 10 0 743=true := (@block_merge g255 10 0 363 380 (@block_merge g255 10 0 120 243 (@block_merge g255 10 0 24 96 g255P10_0 g255P10_24) (@block_merge g255 10 120 96 147 g255P10_120 (@block_merge g255 10 216 51 96 g255P10_216 g255P10_267))) (@block_merge g255 10 363 192 188 (@block_merge g255 10 363 96 96 g255P10_363 g255P10_459) (@block_merge g255 10 555 96 92 g255P10_555 (@block_merge g255 10 651 31 61 g255P10_651 g255P10_682))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P11_0 : block g255 11 0 4=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P11_4 : block g255 11 4 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P11_100 : block g255 11 100 15=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P11_115 : block g255 11 115 96=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P11_211 : block g255 11 211 49=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P11_260 : block g255 11 260 31=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B11 : block g255 11 0 291=true := (@block_merge g255 11 0 115 176 (@block_merge g255 11 0 4 111 g255P11_0 (@block_merge g255 11 4 96 15 g255P11_4 g255P11_100)) (@block_merge g255 11 115 96 80 g255P11_115 (@block_merge g255 11 211 49 31 g255P11_211 g255P11_260)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P12_0 : block g255 12 0 44=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P12_44 : block g255 12 44 26=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B12 : block g255 12 0 70=true := (@block_merge g255 12 0 44 26 g255P12_0 g255P12_44)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P13_0 : block g255 13 0 10=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B13 : block g255 13 0 10=true := g255P13_0
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
  · exact (rfl : block g255 6 0 0 = true)
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
theorem g255G : graphValid g255 (boundsBefore K254) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255R : Impossible true graph 14 sevenInputs.toFinset := by
  rw [show graph = targetOf g255 by decide +kernel]
  exact root_index (g:=g255) (top:=14) (i:=0) (before_sound K254 V254) g255G g255T (by decide) (by decide +kernel)

end PEqualNP.Outside.L_meta_52682

open PEqualNP.Outside.L_meta_52682 in
theorem PEqualNP.Outside.L_meta_52682 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 3, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 3, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 3, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 3, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 3, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 3, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o fit _ correct
  exact replaceShort g255R gates o fit correct

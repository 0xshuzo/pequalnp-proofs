import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4813_aux.Certificate
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
def graph : Sig := 0xfffffffffffffffffffffffffffafff8ffffffffffffffffffffffffffeaffc8fffffffffffefcfcfffffffffffaf8f8ffeefeeeffeefcccffeafaeaffeaf8c8
def seed : Sig := inputs.getD 0 zero ||| inputs.getD 6 zero
def sample (r : Row) (j : Fin 9) := bit r (inputs.getD j.val zero)
def edge (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
  (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) ||
  (x 6 && x 8) || (x 8 && x 5)
theorem edge_table : ∀ r : Row, bit r graph = edge (sample r) := by decide +kernel
theorem seed_table : ∀ r : Row, bit r seed = (sample r 0 || sample r 6) := by decide +kernel
theorem graph_proper : proper graph := by unfold proper; decide +kernel
theorem seed_nonzero : seed ≠ zero := by decide +kernel
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

theorem exec_extends (gs : List Gate) (ws : List Sig) : ∃ l, execute gs ws = ws ++ l := by
  induction gs generalizing ws with
  | nil => exact ⟨[],by simp [execute]⟩
  | cons g gs ih =>
    obtain ⟨l,hl⟩ := ih (ws++[gv ws g])
    exact ⟨gv ws g::l,by simpa [execute,List.append_assoc] using hl⟩

theorem raw_signed (C : Circuit)
    (legal : PEqualNP.MetaComplexity.FanInTwo C) (small : C.gates.countP (fun g => !isNot g) ≤ 14)
    (computes : ∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = edge x) :
    ∃ k S, k ≤ 14 ∧ Live true graph k S ∧ ∀ a ∈ S, a ∈ inputs := by
  let result := (execute C.gates inputs).getD C.output zero
  have goalEq : result = graph := by
    apply bit_ext
    intro r
    rw [table_eval C legal, edge_table]
    exact computes (sample r)
  have rep := get_rep (u := true) (execute C.gates inputs) C.output
  change nrm true result ∈ _ ∨ ¬proper (nrm true result) at rep
  have pg : bit 0 graph = false := by decide +kernel
  rw [goalEq, nrm_id pg] at rep
  have targetIn := rep.resolve_right (fun hn => hn graph_proper)
  obtain ⟨k, S, hk, run, hs⟩ := extract C.gates inputs legal (by simp) graph_proper targetIn
  have ns : inputs.all plainWord = true := by decide +kernel
  rw [nrm_map ns] at hs
  exact ⟨k, S, hk.trans small, run, hs⟩

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
  (x 0 &&& x 1) ||| (x 1 &&& x 2) ||| (x 2 &&& x 3) ||| (x 3 &&& x 4) |||
    (x 4 &&& x 0) ||| (x 0 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 7) |||
    (x 3 &&& x 8) ||| (x 5 &&& x 7) ||| (x 6 &&& x 8) ||| (x 8 &&& x 5)
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
    let hi := ((mask/512-1) >>> (4*i)) &&& 15
    let r := if mask >= 512 then (if hi = 0 then 0 else 1 <<< (hi-1)) else if t/81==2 && i==t/9 % 9 then 1 <<< (t % 9) else if t/81==2 && i==t % 9 then 1 <<< (t/9 % 9) else 0
    (a,Fin.ofNat 512 r,Fin.ofNat 512 (r ||| (1 <<< i)))

def graphPairs (m hints : Nat) : List (Sig × Row × Row) :=
  (selected m).map fun (i,a) =>
    let r := 1 <<< ((hints >>> (4*i)) &&& 15)
    (a,Fin.ofNat 512 r,Fin.ofNat 512 (r ||| (1 <<< i)))

def properB (T : Sig) := T != zero && T != one
theorem proper_of (T : Sig) (h : properB T = true) : proper T := by
  simpa only [properB,proper,Bool.and_eq_true,bne_iff_ne] using h
def assertSize (m hints L : Nat) :=
  let xs := graphPairs m hints
  properB (graphGoal m) && checkEssential (graphGoal m) (vars m) xs &&
    decide (L ≤ (xs.map Prod.fst).toFinset.card-1)
theorem size_of {u m hints L} (h : assertSize m hints L = true) :
    Lower u (vars m) (graphGoal m) L := by
  simp only [assertSize,Bool.and_eq_true,decide_eq_true_eq] at h
  intro p bank hr ha
  exact h.2.trans (lower_count (proper_of _ h.1.1) _ h.1.2 p bank hr ha)

abbrev ColumnInfo := Nat × Nat × Nat × Nat × Nat
def colFree (m z o : Nat) := m ^^^ (m &&& (z ||| o))
def hardSeed : Sig := inputs.getD 0 zero &&& inputs.getD 2 zero
def chartGoal (m : Nat) : Sig := if m=1023 then graphGoal m &&& ~~~hardSeed else graphGoal m
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

abbrev Bits := BitVec 768
abbrev Signals := Bits × Bits
abbrev Decor := Sig × Signals

def ofRows {n : Nat} (r : Fin n → Row) (v : Sig) : BitVec n :=
  (BitVec.ofBoolListLE (List.ofFn (fun i => bit (r i) v))).cast List.length_ofFn
theorem ofRows_bit {n : Nat} (r : Fin n → Row) (v : Sig) (i : Fin n) :
    (ofRows r v).getLsbD i.val = bit (r i) v := by
  simp only [ofRows,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [i.isLt]
def pairSig (r s : Fin 768 → Row) (a : Sig) : Signals := (ofRows r a,ofRows s a)
def properPairs (T : Sig) (r s : Fin 768 → Row) :=
  ∀ i, bit (r i) T = true ∧ bit (s i) T = false
theorem pair_sep {T r s} (h : properPairs T r s) : Sep T 768 r s (pairSig r s) := by
  exact ⟨h,fun a i => ⟨ofRows_bit _ _ _,ofRows_bit _ _ _⟩⟩
def faithful (r s : Fin 768 → Row) (x : Decor) := x.2 = pairSig r s x.1
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

def asRow (cols : Nat → Bits) (i : Fin 768) : Row :=
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
theorem asRow_bit (cols : Nat → Bits) (i : Fin 768) (j : Fin 9) :
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
  (x 0 &&& x 1) ||| (x 1 &&& x 2) ||| (x 2 &&& x 3) ||| (x 3 &&& x 4) |||
    (x 4 &&& x 0) ||| (x 0 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 7) |||
    (x 3 &&& x 8) ||| (x 5 &&& x 7) ||| (x 6 &&& x 8) ||| (x 8 &&& x 5)
theorem bit_vertex (m : Nat) (v : Nat → Bits) (i : Fin 768) (j : Fin 9) :
    bit (asRow v i) (vertex m j.val) =
    ((if m.testBit j.val then v j.val else 0) : Bits).getLsbD i.val := by
  by_cases hh : m.testBit j.val = true
  · simpa [vertex,hh] using asRow_bit v i j
  · simp [vertex,hh,bit_zero]
theorem bit_liftGoal (m : Nat) (v : Nat → Bits) (i : Fin 768) :
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
  let n := v.toNat % 2305843009213693951
  (n*(n+971)) % 2305843009213693951
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
    if (rs ||| column d z.2) != BitVec.allOnes 768 then true else
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
  have be : ((restCov (coverage (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 768) = false := by
    simpa using sep
  change (if (restCov (coverage (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 768 then true else if !properB z.1 || ws.any (fun v => v.1==z.1) then true else _) = true at test
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
  let prod := dbin 0 (ws.getD 0 defaultDecor) (ws.getD 2 defaultDecor)
  if g.mask=1023 then ws.map (fun w => dbin 2 w prod) else ws

theorem wires_faithful (g : Forest) : ∀ a ∈ wiresOf g,
    faithful (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2) a := by
  have base := raw_faithful g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)
  intro a ha
  unfold wiresOf at ha
  split at ha
  · obtain ⟨w,hw,rfl⟩ := List.mem_map.mp ha
    exact faithful_bin 2 (base w hw) (faithful_bin 0 (faithful_get base 0) (faithful_get base 2))
  · exact base _ ha

def targetOf (g : Forest) := chartGoal g.mask
def chartSamples (m : Nat) (v : Nat → Bits) :=
  if m=1023 then liftGoal m v &&& ~~~(v 0 &&& v 2) else liftGoal m v
theorem chart_bit (m : Nat) (v : Nat → Bits) (i : Fin 768) :
    bit (asRow v i) (chartGoal m) = (chartSamples m v).getLsbD i.val := by
  by_cases e : m=1023
  · have u := asRow_bit v i (0 : Fin 9)
    have w := asRow_bit v i (2 : Fin 9)
    have h := bit_liftGoal m v i
    change (inputs.getD 0 zero).getLsbD (asRow v i).val = (v 0).getLsbD i.val at u
    change (inputs.getD 2 zero).getLsbD (asRow v i).val = (v 2).getLsbD i.val at w
    have seedEq : hardSeed = inputs.getD 0 zero &&& inputs.getD 2 zero := by decide +kernel
    simp only [chartGoal,chartSamples,e,ite_true,bit,seedEq,BitVec.getLsbD_and,
      BitVec.getLsbD_not,(asRow v i).isLt,i.isLt,decide_true,Bool.true_and,u,w] at h ⊢
    rw [h]
  · simpa only [chartGoal,chartSamples,e,ite_false] using bit_liftGoal m v i
theorem chart_pairs {m : Nat} {p q : Nat → Bits}
    (hp : chartSamples m p = BitVec.allOnes 768) (hq : chartSamples m q = 0) :
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

def storedDepth (_g : Forest) (depth : Nat) := depth
def readNode (g : Forest) (k i : Nat) : Nat × List Decor × List Decor :=
  let raw := wiresOf g
  let (_,depth,_,_,_,_,_,data) := g.levels k
  let len := 10*storedDepth g depth
  let width := len+raw.length+depth
  let recp := packedAt data (i*width) width
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
  let start := num*(10*storedDepth g depth+raw.length+depth)
  let pos := start+num*offw+packedAt data (start+i*offw) offw
  let nr := packedAt data pos 5
  let nl := packedAt data (pos+5) lw
  let st := pos+5+lw
  let rules := (getPairs data cw depth nr st).filterMap (fun (a,b) => buildRule g ops depth bank a b)
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
  (chartSamples g.mask (fun j => (g.samples j).1) == BitVec.allOnes 768) &&
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

theorem lower_discard {g prior ci hints} (low : ∀ q, Lower g.mode (varsX q) (graphGoal q) (prior q))
    (ok : colCheck g.mask ci prior = true)
    (hp : properB (targetOf g) = true)
    (ess : checkEssential (targetOf g) (vars g.mask) (graphPairs g.mask hints) = true)
    (all : (graphPairs g.mask hints).map Prod.fst = vars g.mask)
    (nd : (vars g.mask).Nodup)
    (cut : poolCut g.mode (subcube ci.1 ci.2.1) ci.2.2.2.2 g.cap 0 (varsX (rawMask g.mask ci)) (vars g.mask)=true) :
    Lower g.mode (vars g.mask) (targetOf g) (g.cap+1) := by
  apply lower_impossible (proper_of _ hp) (essential_plain ess).1 (essential_plain ess).2 _ (poolCut_sound (col_sound ci prior low ok) [] rfl nd cut)
  intro a ha
  apply essential_ok ess a
  rw [all]
  exact List.mem_toFinset.mpr ha

def Known (u : Bool) (entries : List (Nat × Nat)) := ∀ e ∈ entries, Lower u (varsX e.1) (graphGoal e.1) e.2
def extendKnown (old : List (Nat × Nat)) (L : Nat) (carries : List (Nat × List Nat)) :=
  carries.map (fun v => (v.1,L)) ++ old
theorem extendKnown_ok {u old L m carries} (previous : Known u old)
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
def lanePlace (v : Nat) (upper : Nat) := 2^769*upper+v
def combineLanes {α : Type} (f : α → Bits) : List α → Nat
  | [] => 0
  | x::xs => lanePlace (f x).toNat (combineLanes f xs)
def units : Nat → Nat
  | 0 => 0
  | n+1 => lanePlace 1 (units n)
theorem laneSmall (x : Bits) : x.toNat < 2^769 :=
  lt_trans x.isLt (by decide +kernel)
theorem place_and (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u &&& lanePlace b.toNat v = lanePlace (a &&& b).toNat (u &&& v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_and,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<769 <;> simp only [h,ite_true,ite_false,BitVec.toNat_and,Nat.testBit_and]
theorem place_or (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u ||| lanePlace b.toNat v = lanePlace (a ||| b).toNat (u ||| v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_or,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<769 <;> simp only [h,ite_true,ite_false,BitVec.toNat_or,Nat.testBit_or]
theorem place_xor (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u ^^^ lanePlace b.toNat v = lanePlace (a ^^^ b).toNat (u ^^^ v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_xor,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<769 <;> simp only [h,ite_true,ite_false,BitVec.toNat_xor,Nat.testBit_xor]
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
theorem broadcast {α} (a : Bits) (xs : List α) :
    units xs.length * a.toNat = combineLanes (fun _ => a) xs := by
  induction xs with
  | nil => simp [units,combineLanes]
  | cons v xs ih => simp only [List.length_cons,units,combineLanes,lanePlace,Nat.add_mul,Nat.mul_assoc,ih,Nat.one_mul]

def fullMarks (r packed : Nat) := ((packed+r) >>> 768) &&& r
theorem unit_bit (n i : Nat) (hi : i<n) : (units n).testBit (769*i) = true := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
    rw [units,lanePlace,Nat.testBit_two_pow_mul_add _ (by decide +kernel : 1 < 2^769)]
    cases i with
    | zero => simp
    | succ i =>
      have di : 769*(i+1)-769=769*i := by omega
      have ge : ¬769*(i+1)<769 := by omega
      simp only [ge,ite_false,di]
      exact ih _ (by omega)
set_option maxRecDepth 8192 in
theorem guardBit (a : Bits) : (a.toNat+1).testBit 768 = (a==BitVec.allOnes 768) := by
  by_cases h : a=BitVec.allOnes 768
  · subst a
    decide +kernel
  · have lim := a.isLt
    have ne : a.toNat ≠ 2^768-1 := by
      intro eq
      apply h
      apply BitVec.eq_of_toNat_eq
      simpa only [BitVec.toNat_allOnes] using eq
    have lt : a.toNat+1<2^768 := by omega
    rw [Nat.testBit_eq_false_of_lt lt]
    exact (beq_eq_false_iff_ne.mpr h).symm

set_option maxRecDepth 8192 in
theorem mark_at {α} (f : α → Bits) (xs : List α) (i : Nat) (hi : i<xs.length) :
    (fullMarks (units xs.length) (combineLanes f xs)).testBit (769*i) =
      (f xs[i]==BitVec.allOnes 768) := by
  simp only [fullMarks,Nat.testBit_and,Nat.testBit_shiftRight,unit_bit _ _ hi,Bool.and_true]
  induction xs generalizing i with
  | nil => simp at hi
  | cons a xs ih =>
    simp only [combineLanes,List.length_cons,units,lanePlace]
    have sum (u v x : Nat) : 2^769*u+x+(2^769*v+1)=2^769*(u+v)+(x+1) := by omega
    rw [sum,Nat.testBit_two_pow_mul_add _ (show (f a).toNat+1<2^769 from by have := (f a).isLt; omega)]
    have hi' : i < xs.length+1 := hi
    cases i with
    | zero => simpa using guardBit (f a)
    | succ i =>
      have ge : ¬769*(i+1)+768<769 := by omega
      have di : 769*(i+1)+768-769=769*i+768 := by omega
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
    ((mask &&& 1 == 0) || f x) && onMarks f (mask >>> 769) xs
theorem marked_ok {α} (f : α → Bool) (mask : Nat) (xs : List α) (i : Nat) (hi : i<xs.length)
    (bitOn : mask.testBit (769*i)=true) (ok : onMarks f mask xs=true) : f xs[i]=true := by
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
      apply ih (mask:=mask >>> 769) (i:=i) (by simpa using hi) _ ok.2
      simpa only [Nat.testBit_shiftRight,Nat.mul_succ,Nat.add_comm] using bitOn

abbrev Batch := Nat × Nat × Nat × List PackedSig × PackedCov
def makeBatch (k n : Nat) (xs : List NodeContext) : Batch :=
  (k,n,units xs.length,(List.range n).map (fun i => packedSig (fun c => (contextWire c i).2) xs),
    packedCov (fun c => c.2.2.2.1.1) xs)
def laneWire (b : Batch) (i : Nat) := b.2.2.2.1.getD i (0,0)
theorem laneWire_at (k n) (xs) {i : Nat} (h : i<n) :
    laneWire (makeBatch k n xs) i = packedSig (fun c => (contextWire c i).2) xs := by
  simp [laneWire,makeBatch,List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_range,h]

def availableMasked (u : Bool) (p : BoundPool) (m : Sig) :=
  m==zero || m==p.domain || (p.wires.map (masked p.domain)).any (fun v => v==m) ||
    (u && (p.wires.map (masked p.domain)).any (fun v => v==(p.domain ^^^ m)))
theorem masked_comp (d x : Sig) : masked d (neg x) = d ^^^ masked d x := by
  apply bit_ext
  intro r
  simp only [masked,neg,bit,BitVec.getLsbD_and,BitVec.getLsbD_not,BitVec.getLsbD_xor,r.isLt,decide_true,Bool.true_and]
  cases d.getLsbD r.val <;> cases x.getLsbD r.val <;> rfl
theorem available_mask (u) (p : BoundPool) (x : Sig) :
    availableB u p.domain p.wires x = availableMasked u p (masked p.domain x) := by
  simp only [availableB,availableMasked,masked_comp]

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

abbrev QuickPool := BoundPool × Nat × Bool
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
  let n := v % 2305843009213693951
  (n*(n+971)) % 2305843009213693951
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
  if g.mask = 1023 then ((stateSet g k i).map (movedWord (perm.map swapRows).reverse)).map BitVec.toNat else
    let raw := (selected g.mask).map fun e => (inputs.getD (idxOf perm e.1) zero).toNat
    let (_,depth,_,_,_,_,_,data) := g.levels k
    let len := 10*depth
    force (packedAt data (i*(len+(selected g.mask).length+depth)) (len+(selected g.mask).length+depth)) fun rec =>
    selectLive (rec >>> len) (decodeN depth (rec &&& ((1 <<< len)-1)) raw)

theorem fastState_eq (g : Forest) (k i : Nat) {perm : List Nat} (ok : perm.all validSwap=true) :
    fastState g k i perm = ((stateSet g k i).map (movedWord (perm.map swapRows).reverse)).map BitVec.toNat := by
  by_cases isClip : g.mask = 1023
  · simp only [fastState,if_pos isClip]
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
    simp only [wiresOf,if_neg isClip,rawDecor,List.map_map]
    apply List.map_congr_left
    rintro ⟨j,a⟩ hm
    obtain ⟨hj,rfl⟩ := selected_entry hm
    exact congrArg BitVec.toNat (idx_move ok hj)
  have len : (wiresOf g).length = (selected g.mask).length := by simp [wiresOf,isClip,rawDecor]
  unfold fastState
  rw [if_neg isClip]
  unfold stateSet readNode
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
      if len>k then true else if combField xs[q] (!u) ka kb op i j != BitVec.allOnes 768 then true
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
    by_cases hit : combField xs[q] (!u) ka kb op i j = BitVec.allOnes 768
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
  let start := num*(10*storedDepth g depth+raw.length+depth)
  let pos := start+num*offw+packedAt data (start+i*offw) offw
  let nr := packedAt data pos 5
  let nl := packedAt data (pos+5) lw
  let st := pos+5+lw
  let rules := (getPairs data cw depth nr st).filterMap (fun (a,b) => buildRule g ops depth bank a b)
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

noncomputable def forceSignals {β : Type} (sigs : List PackedSig)
    (cont : List PackedSig → β) : β :=
  match sigs with
  | [] => cont []
  | (pos, neg)::tail =>
    force pos fun pos => force neg fun neg =>
    forceSignals tail fun rest => cont ((pos, neg)::rest)

theorem forceSignals_eq {β : Type} (sigs : List PackedSig)
    (cont : List PackedSig → β) : forceSignals sigs cont = cont sigs := by
  induction sigs generalizing cont with
  | nil => rfl
  | cons sig sigs ih =>
    obtain ⟨pos, neg⟩ := sig
    simp only [forceSignals, force_eq, ih]

noncomputable def forceBatch {β : Type} (b : Batch) (cont : Batch → β) : β :=
  let (k,n,count,sigs,any,once,twice) := b
  force count fun count => forceSignals sigs fun sigs =>
    force any fun any => force once fun once => force twice fun twice =>
    cont (k,n,count,sigs,any,once,twice)

theorem forceBatch_eq {β : Type} (b : Batch)
    (cont : Batch → β) : forceBatch b cont = cont b := by
  obtain ⟨k,n,count,sigs,any,once,twice⟩ := b
  simp only [forceBatch, force_eq, forceSignals_eq]

noncomputable def rowCut (g : Forest) (k start n ar lo len : Nat) :=
  let xs := contexts g k start n
  forceBatch (makeBatch k ar xs) fun b =>
    forceLanes xs fun ys => (List.range len).all (fun d =>
      let i := lo+d
      batchRow (flOf g k) g.mode b ys i (List.range' (i+1) (ar-(i+1))))
theorem rowCut_at {g k start n ar lo len} (h : rowCut g k start n ar lo len=true)
    (i : Nat) (l : lo ≤ i) (r : i < lo+len) :
    batchRow (flOf g k) g.mode (makeBatch k ar (contexts g k start n)) ((contexts g k start n).map laneOf)
      i (List.range' (i+1) (ar-(i+1)))=true := by
  simp only [rowCut,forceBatch_eq,forceLanes_eq] at h
  have ha := List.all_eq_true.mp h (i-lo) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le l] using ha

theorem rowCut_merge {g k start n ar lo a b}
    (h : rowCut g k start n ar lo a=true) (t : rowCut g k start n ar (lo+a) b=true) :
    rowCut g k start n ar lo (a+b)=true := by
  simp only [rowCut,forceBatch_eq,forceLanes_eq]
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
theorem listPieces_all {α f xs d} (h : @listPieces α f xs d) : xs.all f=true := by
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
    (cut : (decide ws.Nodup && poolCut u (subcube ci.1 ci.2.1) ci.2.2.2.2 cap 0 (varsX (rawMask m ci)) ws)=true) (hm : m ≠ 1023 := by decide) :
    Impossible u (graphGoal m) cap ws.toFinset := by
  simp only [Bool.and_eq_true,decide_eq_true_eq] at cut
  simpa only [chartGoal,if_neg hm] using poolCut_sound (col_sound ci prior low ok) [] rfl cut.1 cut.2

theorem index_root {u} {g : Forest} {m cap i : Nat} {prior : Nat → Nat} {ws : List Sig}
    (hm : g.mask=m) (hu : g.mode=u) (low : ∀ q, Lower u (varsX q) (graphGoal q) (prior q))
    (geom : graphValid g prior = true) (blocks : checkedTables g cap)
    (idx : indexedRoot g cap i ws = true) (ordinary : m ≠ 1023 := by decide) : Impossible u (graphGoal m) cap ws.toFinset := by
  subst hm
  subst hu
  simpa only [targetOf,chartGoal,if_neg ordinary] using root_index low geom blocks (Nat.le_refl _) idx

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

def witPairs (m : Nat) (rs : List Nat) : List (Sig × Row × Row) :=
  ((selected m).zip rs).map fun x => (x.1.2,Fin.ofNat 512 x.2,Fin.ofNat 512 (x.2 ||| (1 <<< x.1.1)))
def fullOK (m : Nat) (rs : List Nat) : Bool :=
  let xs := witPairs m rs
  checkEssential (graphGoal m) (varsX m) xs && (xs.map Prod.fst == vars m) &&
    properB (graphGoal m) && decide (varsX m = vars m ++ [typeWord (m/512-1)])
theorem full_split {u} {m : Nat} {rs : List Nat} (ok : fullOK m rs = true) {k : Nat} {S : Finset Sig}
    (h : Live u (graphGoal m) k S) (sub : ∀ v ∈ S, v ∈ varsX m) :
    S=(vars m).toFinset ∨ S=(varsX m).toFinset := by
  simp only [fullOK,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at ok
  obtain ⟨⟨⟨ess,alls⟩,_⟩,hX⟩ := ok
  have rest : ∀ v ∈ vars m, v ∈ S := by
    intro v hv
    rw [←alls] at hv
    obtain ⟨r,s,hd,hi⟩ := essential_ok ess v (List.mem_toFinset.mpr hv)
    exact raw_required h (varsX m) v sub r s hd hi
  have mem : ∀ v, v ∈ varsX m ↔ v ∈ vars m ∨ v=typeWord (m/512-1) := by
    intro v; rw [hX]; simp
  by_cases hs : typeWord (m/512-1) ∈ S
  · refine Or.inr ?_
    ext v
    rw [List.mem_toFinset]
    refine ⟨sub v,fun hv => ?_⟩
    rcases (mem v).mp hv with hv | rfl
    · exact rest v hv
    · exact hs
  · refine Or.inl ?_
    ext v
    rw [List.mem_toFinset]
    refine ⟨fun hv => ?_,rest v⟩
    rcases (mem v).mp (sub v hv) with hv | rfl
    · exact hv
    · exact absurd hv hs
theorem strong_full {u} {m q cap : Nat} {rs : List Nat} (ok : fullOK m rs = true)
    (e : graphGoal m = graphGoal q) (ev : vars m = vars q)
    (a : Impossible u (graphGoal q) cap (vars q).toFinset)
    (b : Impossible u (graphGoal q) cap (varsX m).toFinset) :
    Lower u (varsX m) (graphGoal m) (cap+1) := by
  have ok' := ok
  simp only [fullOK,Bool.and_eq_true] at ok'
  intro p bank hr ha
  obtain ⟨k,S,hk,run,hs⟩ := reach_live (proper_of _ ok'.1.2) (essential_plain ok'.1.1.1).1 (essential_plain ok'.1.1.1).2 hr ha
  by_contra! small
  rcases full_split ok run hs with h | h
  · rw [ev] at h; rw [e,h] at run; exact a k (by omega) run
  · rw [e,h] at run; exact b k (by omega) run
def g15d3 (i : Nat) : Nat := 0xf
def g15l3 : Packing := (1,0,1,0,0,0,0,g15d3)
def g15samples : Array (Bits × Bits) := #[((-0x1b8b8d),0x173652),((-0x168581),0x8c829),(0x1f8f9c,0x21714),(0x168de0,0x1de8e0),(0,0),(0,0),(0,0),(0,0),(0,0)]
def g15columns : List ColumnInfo := []
def g15autos : List (List Nat) := [[],[48,33]]
def g15levels : Nat → Packing
  | 3 => g15l3
  | _ => emptyPacking
def g15index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g15 : Forest := ⟨15,3,fun j => g15samples[j]?.getD (0,0),g15columns,g15autos,g15levels,g15index⟩
set_option maxHeartbeats 0 in
theorem geomg15 : graphValid g15 (boundsBefore []) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
def spanChecks (g : Forest) (k : Nat) : Nat → List (Nat × Nat × Nat) → Prop
  | _, [] => True
  | i, (n,a,d)::xs => cells g k i n a 0 d ∧ spanChecks g k (i+n) xs

theorem spansBlock (g : Forest) (k i : Nat) (xs : List (Nat × Nat × Nat))
    (ok : spanChecks g k i xs := by
      simp only [spanChecks,cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
      repeat' apply And.intro
      all_goals first | exact True.intro | decide +kernel) :
    block g k i (xs.map Prod.fst).sum = true := by
  induction xs generalizing i with
  | nil => rfl
  | cons x xs ih =>
    obtain ⟨n,a,d⟩ := x
    exact block_merge (cellsBlock ok.1) (ih (i+n) ok.2)

set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem tablesg15 : checkedTables g15 3 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · exact spansBlock g15 3 0 [(1,4,0)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low15 : Lower true (vars 15) (graphGoal 15) 4 := plain_low (hints:=8449) (by decide +kernel) (index_root (g:=g15) (i:=0) rfl rfl (before_sound [] baseKnown) geomg15 tablesg15 (by decide +kernel))
def known15 := extendKnown [] 4 [(15,[]),(23,[64,48,32,16]),(27,[66,16]),(29,[50,65]),(30,[50,33,16,64]),(39,[80,64,48,32,16]),(57,[32,82,64,16]),(78,[96,80,64]),(83,[99,83,64,32,16]),(99,[48,96,83,64,32,16]),(135,[115,99,83,67]),(156,[112,96,48,50,33,81,64]),(163,[115,50,98,83,66,16]),(165,[114,33,97,82,50,65]),(166,[114,98,83,33,16,64]),(172,[114,50,99,48,33,81,64]),(177,[115,99,82,64,16]),(198,[115,96,83,64]),(281,[131,115,99,50,82,65]),(291,[131,115,50,98,83,66,16]),(300,[130,114,98,49,32,81,64]),(305,[131,115,99,82,64,16]),(312,[130,114,49,98,81,64]),(323,[131,115,98,83,66]),(326,[131,115,98,83,32,64]),(330,[130,114,97,82,16,64]),(332,[130,50,115,98,49,32,81,64]),(344,[130,50,115,49,98,81,64]),(353,[130,33,113,99,82,65]),(354,[130,33,50,113,99,82,16,64]),(396,[48,128,115,96,50,33,81,64]),(424,[129,33,115,48,98,81,64]),(480,[32,50,128,115,98,81,64])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid15 : Known true known15 := extendKnown_ok (m:=15) baseKnown low15 (by decide +kernel)
def g31d6 (i : Nat) : Nat := 0x11a20bf
def g31l6 : Packing := (1,0,3,0,0,0,0,g31d6)
def g31h6 (i : Nat) : Nat := 0x30be670208000065000016357504004755c084
def g31d5 (i : Nat) : Nat := 0x40828fd20fd10
def g31l5 : Packing := (2,1,3,0,0,3,0,g31d5)
def g31h5 (i : Nat) : Nat := 0x300
def g31d4 (i : Nat) : Nat := 0x5dd4520
def g31l4 : Packing := (1,2,3,0,0,0,0,g31d4)
def g31samples : Array (Bits × Bits) := #[((-0x2ea2e99cf4d8d),0x11525c6a12412),((-0x16f3d79b9b181),0x2c2d009524869),(0x18c06d986cd9c,0x1290662058794),(0x27e6c59e90980,0x2166995b04820),(0x3ebbb2079b000,0xe892284e92c0),(0,0),(0,0),(0,0),(0,0)]
def g31columns : List ColumnInfo := [(1,0,30,0,4),(16,0,15,0,4),(8,0,23,0,4),(4,0,27,0,4),(2,0,29,0,4)]
def g31autos : List (List Nat) := [[],[65,50],[16,66],[16,32,48,64],[32,67],[32,49,64,16],[48,33],[48,65,32,33],[64,16,33,50],[64,49]]
def g31levels : Nat → Packing
  | 6 => g31l6
  | 5 => g31l5
  | 4 => g31l4
  | _ => emptyPacking
def g31index : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 5 15 3 9 1 4 g31h6
  | 5 => lookupWord 1 3 1 9 1 4 g31h5
  | _ => fun _ => none
def g31 : Forest := ⟨31,6,fun j => g31samples[j]?.getD (0,0),g31columns,g31autos,g31levels,g31index⟩
set_option maxHeartbeats 0 in
theorem geomg31 : graphValid g31 (boundsBefore known15) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,listPieces_all (d:=1) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem tablesg31 : checkedTables g31 6 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · exact spansBlock g31 4 0 [(1,5,0)]
  · exact spansBlock g31 5 0 [(2,6,0)]
  · exact spansBlock g31 6 0 [(1,5,0)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low31 : Lower true (vars 31) (graphGoal 31) 7 := plain_low (hints:=8449) (by decide +kernel) (index_root (g:=g31) (i:=0) rfl rfl (before_sound known15 valid15) geomg31 tablesg31 (by decide +kernel))
def known31 := extendKnown known15 7 [(31,[]),(167,[115,67,100,83]),(313,[131,115,65,50,98,81]),(334,[131,115,100,50,33,16,80]),(355,[131,50,66,116,99,82]),(428,[130,50,116,49,32,97,80])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid31 : Known true known31 := extendKnown_ok (m:=31) valid15 low31 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low47 : Lower true (vars 47) (graphGoal 47) 5 := plain_low (hints:=8449) (by decide +kernel) (cut_root (prior:=boundsBefore known31) (before_sound known31 valid31) (8,0,39,0,4) (by decide +kernel) (by decide +kernel))
def known47 := extendKnown known31 5 [(61,[50,65]),(91,[101,66,16]),(94,[101,50,33,16,64]),(181,[114,81,98,50,65]),(227,[83,82,114,99,66,16]),(230,[83,114,99,33,16,64])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid47 : Known true known47 := extendKnown_ok (m:=47) valid31 low47 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low55 : Lower true (vars 55) (graphGoal 55) 5 := plain_low (hints:=257) (by decide +kernel) (cut_root (prior:=boundsBefore known47) (before_sound known47 valid47) (16,0,39,0,4) (by decide +kernel) (by decide +kernel))
def known55 := extendKnown known47 5 [(55,[]),(59,[50,65]),(103,[82,98,66,16])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid55 : Known true known55 := extendKnown_ok (m:=55) valid47 low55 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low63 : Lower true (vars 63) (graphGoal 63) 8 := plain_low (hints:=8449) (by decide +kernel) (cut_root (prior:=boundsBefore known55) (before_sound known55 valid55) (32,0,31,0,7) (by decide +kernel) (by decide +kernel))
def known63 := extendKnown known55 8 [(63,[]),(95,[101,66,16]),(159,[117,101,67,32]),(359,[131,67,116,99,82,16]),(377,[128,81,67,112,97,32]),(462,[83,133,115,67,32,96]),(483,[83,80,132,115,96,32,16]),(492,[80,84,132,49,113,96])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid63 : Known true known63 := extendKnown_ok (m:=63) valid55 low63 (by decide +kernel)
def g111d6 (i : Nat) : Nat := 0x7213f
def g111l6 : Packing := (1,0,2,0,0,0,0,g111d6)
def g111h6 (i : Nat) : Nat := 0x8000
def g111d5 (i : Nat) : Nat := 0x17e51
def g111l5 : Packing := (1,1,2,0,0,0,0,g111d5)
def g111samples : Array (Bits × Bits) := #[((-0x52af9237396d7c609ad),0xf04d190d4828112652),((-0x655c481ac6e81d9b781),0xa02a6201004224829),(0x544c503731eb1c38f9c,0x1449d09c60531818514),(0x6d8c223200ec1fc0fc0,0x6bb62f6391ac07c0ac0),(0,0),(0x71d0482cce001fff020,0x70fb0c6f2b181eed020),(0x7fe3c2000ee7f040020,0x7f5fd599feffb040000),(0,0),(0,0)]
def g111columns : List ColumnInfo := [(1,32,78,0,4),(12,0,99,0,4),(96,0,15,0,4),(0,8,99,4,5)]
def g111autos : List (List Nat) := [[],[32,83]]
def g111levels : Nat → Packing
  | 6 => g111l6
  | 5 => g111l5
  | _ => emptyPacking
def g111index : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 3 1 6 1 1 g111h6
  | _ => fun _ => none
def g111 : Forest := ⟨111,6,fun j => g111samples[j]?.getD (0,0),g111columns,g111autos,g111levels,g111index⟩
set_option maxHeartbeats 0 in
theorem geomg111 : graphValid g111 (boundsBefore known63) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem tablesg111 : checkedTables g111 6 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact spansBlock g111 5 0 [(1,6,0)]
  · exact spansBlock g111 6 0 [(1,6,0)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low111 : Lower true (vars 111) (graphGoal 111) 7 := plain_low (hints:=16785665) (by decide +kernel) (index_root (g:=g111) (i:=0) rfl rfl (before_sound known63 valid63) geomg111 tablesg111 (by decide +kernel))
def known111 := extendKnown known63 7 [(111,[]),(123,[101,66,16]),(187,[117,80,66,96,16]),(190,[114,83,48,33,97,64]),(215,[115,83,67]),(222,[101,117,50,33,16,64]),(238,[83,114,99,33,16,64]),(243,[82,98,115,66,16]),(311,[131,115,99,67,82,16]),(318,[128,112,96,49,64]),(343,[131,115,83,67,98]),(349,[128,80,117,32,16,98,65,48]),(365,[129,113,82,65,48]),(378,[129,33,97,81,16,114,49,64]),(437,[134,81,114,50,65]),(455,[83,133,115,67,32,96]),(476,[82,50,133,98,49,32,113,64]),(485,[80,81,129,114,50,65,96]),(490,[81,33,80,128,97,114,49,64]),(497,[98,99,81,131,114,65]),(504,[49,50,83,48,130,113,64])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid111 : Known true known111 := extendKnown_ok (m:=111) valid63 low111 (by decide +kernel)
def g189d7 (i : Nat) : Nat := 0x163441bf
def g189l7 : Packing := (1,0,3,0,0,0,0,g189d7)
def g189h7 (i : Nat) : Nat := 0x42f9f28c08140000000020f801630c00d0
def g189d6 (i : Nat) : Nat := 0x420a3fa41fd10
def g189l6 : Packing := (2,1,3,0,0,3,0,g189d6)
def g189h6 (i : Nat) : Nat := 0x18000
def g189d5 (i : Nat) : Nat := 0xb7d8d20
def g189l5 : Packing := (1,2,3,0,0,0,0,g189d5)
def g189samples : Array (Bits × Bits) := #[(0x1da64108012bd832f47c,0x1d85960021199906a42c),(0,0),((-0x53ba7568affbd0d237b1),0x4c61e4544061425c84a),((-0x66a71be859ffde31f071),0x1909e00a3a18e18a0685),(0x67780400a62f50f10f70,0x627201f4c42600710950),(0x52c2796909d080fbf080,0x4042684f5e8240f95000),(0,0),(0x7b3dbae059d52e010080,0x3b3981b0a179ab000080),(0,0)]
def g189columns : List ColumnInfo := [(160,0,29,0,4),(24,0,165,0,4),(132,0,57,0,4),(33,0,156,0,4),(17,0,172,0,4),(12,0,177,0,4)]
def g189autos : List (List Nat) := [[],[115,84],[32,67,117],[32,83,116],[48,82],[48,82,112,66],[64,114,50,48,80],[64,114,83],[80,50,116],[80,50,66,32,114],[112,66,48,82],[112,66]]
def g189levels : Nat → Packing
  | 7 => g189l7
  | 6 => g189l6
  | 5 => g189l5
  | _ => emptyPacking
def g189index : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 9 13 2 9 1 4 g189h7
  | 6 => lookupWord 1 3 1 9 1 4 g189h6
  | _ => fun _ => none
def g189 : Forest := ⟨189,7,fun j => g189samples[j]?.getD (0,0),g189columns,g189autos,g189levels,g189index⟩
set_option maxHeartbeats 0 in
theorem geomg189 : graphValid g189 (boundsBefore known111) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=1) ?_⟩,listPieces_all (d:=2) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem tablesg189 : checkedTables g189 7 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact spansBlock g189 5 0 [(1,6,0)]
  · exact spansBlock g189 6 0 [(2,7,0)]
  · exact spansBlock g189 7 0 [(1,6,0)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low189 : Lower true (vars 189) (graphGoal 189) 8 := plain_low (hints:=536879876) (by decide +kernel) (index_root (g:=g189) (i:=0) rfl rfl (before_sound known111 valid111) geomg189 tablesg189 (by decide +kernel))
def known189 := extendKnown known111 8 [(189,[]),(303,[135,50,65]),(347,[130,50,98,82,115,33,65]),(486,[115,83,82,130,99,66,16])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid189 : Known true known189 := extendKnown_ok (m:=189) valid111 low189 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low127 : Lower true (vars 127) (graphGoal 127) 9 := plain_low (hints:=16785665) (by decide +kernel) (cut_root (prior:=boundsBefore known189) (before_sound known189 valid189) (32,0,95,0,8) (by decide +kernel) (by decide +kernel))
def known127 := extendKnown known189 9 [(127,[]),(382,[128,100,49,112]),(478,[99,132,84,48,33,112]),(508,[48,84,100,49,129,112])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid127 : Known true known127 := extendKnown_ok (m:=127) valid189 low127 (by decide +kernel)
def g191d10 (i : Nat) : Nat := 0x8201ff
def g191l10 : Packing := (1,0,5,0,0,0,0,g191d10)
def g191h10 (i : Nat) : Nat := 0x99090000b500000001a152f05d5c000e4006080015749fa60141c73802b0a68137976081bca199eaaa3d961388c0f3a0002328c00084a05000089c2a
def g191d9 (i : Nat) : Nat := 0x288616180c48a1166c008c818588a2e004e68c2c214019ce18588b2410102944c300431c508936018138408051218b0c0328614b0a030139610c0803944862a8614888704038c28424018278d600745a25b53e43cce27c5e0bc00ff483fe30ff4c3fd10ff54ffe10ff903fe20ff4c7fc20ff58ffd40
def g191l9 : Packing := (12,1,5,0,0,10,0,g191d9)
def g191h9 (i : Nat) : Nat := 0x140000000000000198cb0000a04e08a520001a51c20000531e80b64388d00078963d80a7524800343b41a670800007a7cc632d75239502d607286400000000060840000002a100028a67e35dbbd50001a6c315cd7a0d113ac27000121800052568158594ec000682af90000f6880000010b6fab800321ac31374a97c0018068243a2b09f06ef8c8000c984c7fad8000732e29d36fd3c9ba4660000003c50a43a2e72f0000037c5c484413000060966343d567081fd24000161fd8fb857db1616c2d70bc0001da504981c000a8cb68709baa54393350153817e93b2ee08a0b35c971e4812648c40cf0c890074a5b901b85c19b060f0f30f9c6d46f822909e468ae58b600010460007b00142a8dc0d2c800031c60005ad28d4a60000000000000046100000000000000005978000750c07fc419a5a33000612dc38451b04000033fe570000002d76000244c429f180a5d34b0ba1360001a731afd48a565b2f860060014b1d8111aaaac600056d800000000026c2da68678cd5b803ae00010d91906c6000000173ec82c4200058c80000000001b509c9847ce37e90001c466a9e954000000c99484d7ca82a800f93447182024f80000c48dc000596030083ad05a1c75006c10817410814060062c35820051841c00801071c96460c20000020c70c01c908b0c0000080000041016
def g191d8 (i : Nat) : Nat := (if i<1 then 0x50b30a062068860c1071620828188001141c88038918b140c61c40b1a0821c49040b10a18885a12900e2468610b144063043858908b143122d10c2a20e20596046182c82c608322160c8246088071094438590503146400c68a00c1a1022c6305831c01630640389281160c82460840710c140c6090090e404803892100e1864038618c162401c48c60b160180d111103182838b1239014302141c48b3a5181c5091708320507124c195160c316314389160c90448d187120c6110890e34514481802c80858c1c1041c48b281142c624708082122c8246892c61458c2b0610e2c48e44a0c1c5a2065c02c60d3011630900487244022858c10714310040020e2cc1c4884930e0c81c48b280ca8848b18a062002438c50b10c1620e2470c62616044871e70a1c08a2250e2c5421260c1d08b262102c626102022859800f12308301250228a0048b18c1621898487020210b4051306022161ce1858a1930e0c61c00d160ca0458a1c1121c1920890e0c8083a1122ca0500b0624a0a007244181c482424459c607122c82c087120cb00007164140c48060a1240e251001628c306c54c090413820f044901871630c3c38c2458d8309030a1a24597160142c9badb87b53b11aebaa9a75a41a0d9cb9a59559218df8b989385f82b7db79977373170b6e56a367d6496155e15ad5795535114eb4c549144f40d3d93a537f34b3252e32691fd1831330e30a106d02afdaf98f64f14ee0ebae78e52e2cd96d46d12cd0c8ec5ac26bc8ba2b60b10adcab6a82a5ca36a029969548f68b48808227e079075c7366bc65061c5e85985645224e04904403fe3923503002be2982561f818c14a1160d4092042001ff54930ffaa0a07fd71483feb1c21ff50120ffcc5207fd52503fe98221ff58e20ffac0987fd1058ffeb9a41ff58640ffa60907fd72443fe882a7ff50910ffee2907fd2058ffe98c41ff54131ffa20907fd21903feb1281ff48153ffa42a07fe72443fe90c41ffdcd20ffa65087fd32883feb0c61ff8ca10ffa43187fd2158ffeb9a21ff54931ffac098ffd62903feb1461ff58931ffac0a07fd204c7fa38a417f5c520bfae5107f920842ffb9281fddc520ff221105fd75902feb88417fdd110fba60b1fdd324c6feb94617f5ce10bfee0a9dfd7054efebac61fdc8610bfee2907f910482ffb9263fd48531bfee2b1fbf744c2ffbb2617f5c163bfaed185ff71502ffb92217f5c553bfae9105fd76902feb9c417f5cc20bfee2a9dff704c7dea14817f5ca10ff260905ff7258fee982637fdd531fea63087dd3054efeb92637f5c131bfae2b1dff724c2ffbb2817fdcd10ff261105fd718c2feb8c817fdcd20bfeeaa05ff7058efeb9a41fe48230bfae3107dd3258efeba4217fdd530bfee2987f5514c6feb94817f5c963bfeec98df771482eeb9c416fdd130 else 0x10410e24)
def g191l8 : Packing := (113,2,5,0,0,12,0,g191d8)
def g191h8 (i : Nat) : Nat := 0x38d5055793c3679268754bc6188000001bef920589c626a6500070140c8d5de5f1d7a21d0344d98ee800183ee488000001119701a189f7ac18d073c41c5a460f2f6dbb0d3e90a06b82f5bcc02928e3aa852e880000109c34616429775d57a00841de8968c753cd4f7779436ba625de899899071c11166c07285d4158b1c40cba3819701ff1ed4e0000001d75e386545f25c03c4e3ccfe7905e2217770000000a100005011f8991186d800000144100008f313025a433c0cd88dae660be94000121c0000002c88000000655b0af52342fd8c3fbe11d039049a5a1e7325180004d4e9a308f4f4000000ef1802b07e014cea170acb800000009b4c4008e61bc79a059a0f70fccb137f85b2554dc0000000f21e93d1260001258003490000000000283ab340000000b1c0000000003185023a5319608aa0001913478000000000000000046621400000000000005b0dc8e000000426e6c726f99d415a6c3045000127023e070c8d80b889403631ef964fdd2196b35879ca860c0656093c9b66e604e1a08c20003c8494d7228964094caf59a8139a149ac000c151050440002c01002420821110471482078810951470800420470000020001001c02830c50400010400800405400402040000c00080070800c100000d0040151000c0040141188000004000
def g191d7 (i : Nat) : Nat := 0x23042421610002c21610208008384100000005848830400208084004181081508808200a81105842c340108081882c400010401610060400004128800006508824200028421410000c0162410800007085060424a100000220d0042c200002c20410018408210b0d0840000384082c412109080006109020848e84200508408200000000601881c2121000008bf14a22c388670ba10c1480f009fabe87c6f79ecbd479ef09d6ba8736e39c4b7c6ded69a6b48666c998cb0c5febe972ae05b6b3964abc56eaa952aa0536a1940a7c4ee9892aa504969191ca2c44e8890ea083f67d8f89ec3be748e29b83666b8d49a432e628be9782e65b8b095429e5089e9302464588890c20e3e8728d8196318608bc15e248428800f61b83085c0ae148268480860b81081401e02802800df4815ca209fd879c9109fd82dc163df5215c620aff8654931ff38148230fe92054930df7715c5209fd82dd530b7f8558140bf7815c520bbf844c1209ff815c163df771501209ff815c1539fd81dc163fe92048630df920dc530ff210dc5209fd825c640f755154131bf78148131df7815ca10df7815ca40ddf714c163bf7815cd209fd8798a409ff815ca20fd5514c131df97244220bf9809c910dbf74549309ff805c5639fd81dd930ded20dc963cfd764c620df4815ca40bf9808ca10b7f85581319fd82dc530df9205c630ff210481319fd80dc5539fd81dd530bbd849c910bf58158e109ff805c963aff8654940ddf714c963df7715cd209fd80dd9319fd82dc563df551dc131ddd215ce20df7714c120fe92050910df5315ca10df783dc5209fd825c630ded52dc931dbd425d640df610dd9319ff815cd20bf78148163df5515c1319fd82dc540ddf764c1319fd878ca109fd81dcd209fd80dc5639ff815ca40dbd54dc940ff110dc520dbf7458130ded215ca30df5615d210bbf844c110ff081482309fd82dd1109fd82dd540df471dcd20df77144120bbf845cd20dbd425c640bf7814ca10ff3714c120bdf8350910bf78148153df7215d210bf78158131fe52048531bf78154131ded7248640cfd764ca209ff815c963bbf845cd10df583dc520edd6358130df4715cd20df771dcd20ddf714c153ff0714c120fd5314ca109f7815c5209f7815cd209bf845c1539ef825c5639bf845c1639bf845ce10fe120c861097f855da408fd86dd5319bf845cd209bf845c1319f7815ca409f581dc163
def g191l7 : Packing := (116,3,5,0,0,11,0,g191d7)
def g191h7 (i : Nat) : Nat := 0x30450ac641c0062400b2c00a0c8100000001c50000042a883a
def g191d6 (i : Nat) : Nat := 0xdf2b688de6543ca1408fb4c102b944193f85dd1604c23ef22c16eaa062fe1b7454930cdbc26e2982411f79161e6290336f0838ae69056de5183dc5208fb4c0e2b9a419b784dc5734823ef22c16ea9847de4582dd110
def g191l6 : Packing := (12,4,5,0,0,6,0,g191d6)
def g191samples : Array (Bits × Bits) := #[((-0x25717f105ceccb07488eef5d6b05d3ebfeedb891de8d9d),0x1a8204e622010a10823154424006181028000900212202),((-0x1aaf9ec211b94e8e1afe7bdff1ecfffe9c5dc8333bb7c1),0x2550c011dc22916965caaa243f59e4c1d3e726bcc44879),(0xb8767821ad46b844808258e2a3253cf6ea13881040d8c,0x287218002942c96181045804080031c00109841008504),(0x2669d07e8c08ca07a98c101ac024d2c2804ca411f909a0,0x2428c05eec0a4201a424385293645c4328c32710b10ae0),(0x1554139111eda5cf49d49289dc948100804cc031fe5240,0x154130111e4b5ce49ca82ad2c98a38c923cd0654ed000),(0x253ba84144b4c40e1226cad10169ac341018648a03a410,0x2509e8114094c4ae18468a9400a0a6cc00bdf6de028450),(0,0),(0x38f01e2cfde810414683fb572913092a5d010800038410,0x1870162cbd68114126a930633d5f5823ff420120010200),(0,0)]
def g191columns : List ColumnInfo := [(160,0,31,0,7),(24,0,167,0,7),(2,0,189,0,8),(19,0,172,0,4),(0,16,166,9,6),(4,0,187,0,7),(1,0,190,0,7),(36,128,27,0,4),(136,0,55,0,5),(129,32,30,0,4),(9,16,166,0,4),(20,8,163,0,4),(14,0,177,0,4),(35,0,156,0,4),(56,0,135,0,4),(26,0,165,0,4),(134,0,57,0,4),(162,0,29,0,4),(152,0,39,0,4),(25,0,166,0,4),(168,0,23,0,4)]
def g191autos : List (List Nat) := [[],[115,84],[32,67,117],[32,83,116]]
def g191levels : Nat → Packing
  | 10 => g191l10
  | 9 => g191l9
  | 8 => g191l8
  | 7 => g191l7
  | 6 => g191l6
  | _ => emptyPacking
def g191index : Nat → Nat → Option (Nat × Nat)
  | 10 => lookupWord 16 41 5 10 4 2 g191h10
  | 9 => lookupWord 67 277 6 13 7 2 g191h9
  | 8 => lookupWord 100 251 6 13 7 2 g191h8
  | 7 => lookupWord 4 19 2 10 4 2 g191h7
  | _ => fun _ => none
def g191 : Forest := ⟨191,10,fun j => g191samples[j]?.getD (0,0),g191columns,g191autos,g191levels,g191index⟩
set_option maxHeartbeats 0 in
theorem geomg191 : graphValid g191 (boundsBefore known127) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=3) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem tablesg191 : checkedTables g191 10 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact spansBlock g191 6 0 [(12,7,2)]
  · exact spansBlock g191 7 0 [(13,7,2),(36,8,3),(36,8,3),(31,8,3)]
  · exact spansBlock g191 8 0 [(3,7,0),(36,8,3),(31,8,3),(36,9,3),(7,9,1)]
  · exact spansBlock g191 9 0 [(12,8,2)]
  · exact spansBlock g191 10 0 [(1,7,0)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low191 : Lower true (vars 191) (graphGoal 191) 11 := plain_low (hints:=536879361) (by decide +kernel) (index_root (g:=g191) (i:=0) rfl rfl (before_sound known127 valid127) geomg191 tablesg191 (by decide +kernel))
def known191 := extendKnown known127 11 [(191,[]),(319,[135,50,65]),(351,[133,117,101,33,48]),(367,[128,16,64,100,80,113,33,48]),(379,[130,50,81,115,98,65]),(431,[113,129,97,82,32,65,48]),(445,[129,82,97,48]),(487,[115,83,82,130,99,66,16]),(494,[64,132,49,96])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid191 : Known true known191 := extendKnown_ok (m:=191) valid127 low191 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low251 : Lower true (vars 251) (graphGoal 251) 8 := plain_low (hints:=1358970881) (by decide +kernel) (cut_root (prior:=boundsBefore known191) (before_sound known191 valid191) (128,0,123,0,7) (by decide +kernel) (by decide +kernel))
def known251 := extendKnown known191 8 [(251,[])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid251 : Known true known251 := extendKnown_ok (m:=251) valid191 low251 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low255 : Lower true (vars 255) (graphGoal 255) 12 := plain_low (hints:=553656577) (by decide +kernel) (cut_root (prior:=boundsBefore known251) (before_sound known251 valid251) (64,0,191,0,11) (by decide +kernel) (by decide +kernel))
def known255 := extendKnown known251 12 [(255,[]),(479,[118,133,33,48]),(503,[115,82,98,131,66,16]),(507,[99,81,115,130,65]),(509,[82,129,48])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid255 : Known true known255 := extendKnown_ok (m:=255) valid251 low255 (by decide +kernel)
def g383d12 (i : Nat) : Nat := 0x1840804ff
def g383l12 : Packing := (1,0,6,0,0,0,0,g383d12)
def g383h12 (i : Nat) : Nat := 0x2e190000e44028954b00129713b90021c5c400a24a286e030000000000d800006790000005048cec0c584c000029410000109
def g383d11 (i : Nat) : Nat := 0x1c1800c080840a80c160880850c1604287044044070d0e04282102a03050f061043070d0a08508680361365e17803fe087fc30ffa61ff443ff187fe10
def g383l11 : Packing := (6,1,6,0,0,9,0,g383d11)
def g383h11 (i : Nat) : Nat := 0x605ec8c0000001117d3d8e632bfc434126a560a0c97cd1c2e0006879dce0130002029832241d31f89848e70800000000019dd990a81d83401050198b41ca520a2f40adbada290270002212000f0240555b3c62d0c010b44640b0000000000a02000000274e000193000140ac0e19590854ad62490de02102d21d6156142944000d8a4082dc48550007f7944400014100014220513068000058000991281875380f661504984eda4b2e787cc39625232a002653d245061c2fea2000000680400000024e94b1850b1ad217010100600b00017050301c050070e260404451400410
def g383d10 (i : Nat) : Nat := 0x2e1d818587821e221614a130f091146478584c0c3c2c10b0a7088561608c040207a04c442860211d1a16112300a10082e1c61311850b0a4746c2c1058458988a3028223838785a5041d141418442a102d2088a0a12225460ac2c10805040f40583c282820b0a1c4c45191c1c4824e230c8c09820a901e8c30705040d0e3618222878514342c181c14442810482548c140e0b08166420584040b0a30885c282a3030203e08a072c1610102428b860a11821e1464106058707110b382838984902d1c1d18284824e230c8c0e201c1670947074642040a0f0b4e183a3022286871d083210102c28c861e0f818409821c149061607c10ac2110440306e0e102e1e00585261c18170708242c1100c140a08406050d0ac1080438303848582821818242f042010c0f840a23821408711c2060407c3c0c10a0f503606183e08206e10587291c1814370b04281108e0d878209840b801412a07050418804020c561f04108080a20504121e003e160821ac3aa6695281e74a5d64a236e2ba1a60b1fbdea9dd5d21bcdaf9a258b17fd7296355a14ad3b92851910bcf88e74d40c2cb98aa49d08fc8086b456044c2f828421017c1280d4003ff5c530ffd73443ff5c130ffd73043ff1cc10ffd73843ffa0d10ffd718c3ff9c430ffd30443ff1ce10ffc83443ffcc110fff814c3ffa0530ffe718c3ff4c610ffd318c3ff9ce10ffe318c3ff60530ffd710c3ff1c430fff83443ffcc610ffd83443ff20530fff718c3efe1130ff9708c2ff60d10bfd818c2ff60c10bfd838c2ff60610bfd810c2ff61e30ff9704c2ffe0530bfd83842ffe0d10bde83042bf61830bed828c2fb60810bdd83042efe1130
def g383l10 : Packing := (47,2,6,0,0,12,0,g383d10)
def g383h10 (i : Nat) : Nat := 0x71198115833604b01a0000606e88fc000242d7c1fb0faad280000000907200000000000000000011a60000c095e07a03c80000000207200b0000f0374218000083d74340000000000010fe000191d800038c8000000000050001a19c0000000f0d80002417105f0001002bc08ec1b0001e12c0000000f0e7e92d81a6801000081e2997c07b60460002f86e047b093591c0b42863642440b4814a40900000001016701f80992cbb0308000c10b416439d943b147aae0000000140000000051cc437e4b4604d43368120000516302b9f1000004067d0c8043000061b56b100000c580000000783f104c0003fbb80009070d07382c4f54000000014a410460001715080ea8740833a5880002404721a41d7010e870e0a6000041e7802d68a0000000000000016605c32d9336823a9a000d7e20d86d416e10a400828f5440c813b83e60a220d8fa1581020e4099e8197842301210c9aa808357404e01fd304041e1023c6482e6b2cf063e21e71a6056370a003201825400056b139c293c35f0f8311d9031132ca772115827b06218a0203561cf86910f5a5f4b8b233b382b58ee49dec3300d7802d8c0502fd10109b0c0a907ee0a0fc274022d3a10d5060b108505d001d3c31732301838cca1790204071480aad97c1b8000509cd0a402a9482901e3171c30000064ac78e80004854e040ddec841106f32a0420d715820cb2810092535383b24a5005e83218280109ecf40006a47e0540003c1d6c17800c84f7001b077b0900001c268000e088000143b221e2f0000390d00040c17340800211f04000c3852005c082b04030102880201024c3d0e17000f0511410100573e04001200070500016400040b010407000d00010204010004000a010e07000000003720
def g383d9 (i : Nat) : Nat := (if i<1 then 0xb102c382e18141e0b0515081b05844813238441e0b28448e13e08641e68382b080b205c2c0a1814320a1f08220f1817080b05100a17058c081a0c8c160a1210200b0890220a14101e2a30128a0e230b820f0510240a048f81c10782c145e083b0a0a0214100fe082808592d490e4231f18e446c63231688a8c4ea2230fa871c33216b09e843c15606b0037f63ee9f46f8c7b63d0de34ef1768baa1d10e6871fb8a1c10ddf6dfb6a1afed5f6a4347d9fecd665b327d8fec6861fb0a1822bf15e8aee9710b685a8ac7d5fead655faa354c8a294fba75d35c98e4bba53926e920484a35d15c897437213905c7fc3ee1f14f1476139c1bd0da86b434a1964c846102f39740b4e5902b39540a6051927c934096049023390f883c3e31e60eb072a37e1af0d1c6602fe16a8a8c4d023f10f87fc3be1b60cb05d82be13608f84201be0b604b0190064000dfeb8b07186ff60573843f7f08b8a61bfc7360610bfecb902986ff606738437fb0fc1a21bff874c110bffcbb06885ffe5d304437fb0e98c217fd9720d10bffcba63085ff65f30442ffb2fc1a217fd97a0d10bfecbe63084ff66173443bf2e1b8c613fd981cc109fe4c2e6884ffe61730427fb30388613fc985c530ddfca307184ffe45878c27fb30b9821bed828c6309ffcbb06085fbe4983442efb2a40a61fd9315c130deec1a63085fe64073842dff2cb88613fd985c130dfb38b02187dee55708c27fb2fc0a61bf581e0530def41f06884ff66173842f7f28c0a61bf57160430bdeca502986f7e0f304427fb3039c21afd91618309fecc6e3185fee41318c27ff2ec1a21bee7360810ddfca307085fee41318437bb2ec18217df935c1309ffcbb07086ef247844c37bb07c1a2177d959c430bfcc8463186fb60a718c27fb3138c61bdd835cc10bfcc80e6084ffa61734427fd30b8a613ff9760630df6cbb05185bf65b318437dd22c1461fd8935c130df6c8b05186f725d830437dae6c10213ff985c630df6c10e6086fbdcd82042feb2398221bed825c630ddf48f08986efe47844c377f08c0a617f5911ce10fddc22e0986efe11704c35fb0cb8861bed9360a30bdeca0e2186efe11714c37f730b84616ff965c630df6c16e3186fda07814c35fb0d38861bdf9760c10bf7c9302986f760c834427fb3138861bf581205309fecc4e7084ff65d810c27ff30b9c217f990dc630dfcc1ae1186fd605318c27ff2ec08617bf944c110ddfc2702985fee41834427fb3198c21bdd83cc610ddfc2502985fe643318435fd22c3061bef9260d109fecc2e3185df65683442efb2b982217ef924c610def4bb06086fb609318c3fb662b82617ef924c6309ffcc2e2186fba5d828c3faa63c0a619fd875c6309fecbf06886f7e0d3044377f0840a61bbd91e11309fecc463184fbe498344277f28c1c213bf9460e30 else 0x730608110514260a15041e8407028a0f1182c7c30505c2240382841342a1060e054102240482c411050a0a840b04480b04881e0410241620582440905881e04103c0a0405828a0b05058605040102e0e284c12202828082509942609105c1c202038143058142c0a203c16110511080404828804050447470503c164e18381e3e083c14342010160a203c2c2c204416308810140f211412111844342e1090220f2010160a182416208810140f2010420a1c10081105900821050c160f101c1c0f182416202858160a202c142088284c6070646040703c60a058a0b040e0581450203c14305038407050118a0e2810160a19140a090890120a102c140411864a090882824442a10081c0b028c0a0c0202e0f28441409183c0a0b07101211090c141910470c0e0590162210441e20902c505020142c0a2c1042208290161c1014080e0b918e1a0b8c2304058e8219420281656283c1430785041fa17068a0f05188c060702c9c1038281e4e17040e0aa28101e70805c163040501430284c123e07081dc107828c13088a0c0508e101650ad60140b20281e202114121120281c2e1f041e0a211c162048442430503c404070287040d8441640f04c1e34202c143e081c140f2210080b05101211090f85c18e810140f303c282020641630785040f0a0a8a0f050c1e0)
def g383l9 : Packing := (136,3,6,0,0,13,0,g383d9)
def g383h9 (i : Nat) : Nat := 0xa16f054972c28000915083d009e0b000184b4aa00070df9a0000000103800000000040895c7d1f430452c83b41000000066c401a931403589000181590e60c4006e970739878c268f4319a8a1e8a227410f80515a000677800202f029915b907440e6c7f8b08b068a9c416408c84be1fb32f040001432000000000000000000001daa0990d58b4800e1d917e01640581811720991cb65f653999ed0240cf0c80400004d08a6610820084081054000400010000a42100804
def g383d8 (i : Nat) : Nat := 0xa10200000e0858408185082e10440a10000c840000161001e1030a10000000000504000000000141001e10108102819120810282002820c8400001e10283e0edf5ba3ccdeebb539ac5dcadb68acd529f4a9dcda4f2289c3a13047fbe9eaf070b71aed266b2186be57aa93696439b8be50258f05a28118781e00dafe5b845c530cefe1f944c110aef69c91e1130afb68f7360810cefe119720530cef5c79460e30cfb61f924c610adfe9587e0d10cef5c79460e10cdb655821cc10f745c5315c1308fdea581205308efe91985c1308fb689981cc10caf619941c4308fbe89985cd108bf69a985c530afa6829760a30cafe5b845c530ccfe119520530cdb655829c630cfa609901cc10cebe539260d10aebe8991e1130af66809760c10cbbe59825c6308fb68b9161e308efe91989ce108bfe999760430af36889760c10ceb651828c6308efe91985ce108fb6a582dc6308bfe9b985c4308bfe99985c630c9f655869c430cebe139260530ad76949760c108bf6a3965c430acf69491e11308f7ea58320d10cfa609908c630af9a869760a30add6967160430aeb6929760a30af96869760a308ef6a784a0530ceb651821cc108dfe9597e0530aebe919360a30ccfe57845c130cee611901cc108fb6a3924c630
def g383l8 : Packing := (53,4,6,0,0,9,0,g383d8)
def g383h8 (i : Nat) : Nat := 0x834601a000
def g383d7 (i : Nat) : Nat := 0xa295fdb2e3ca3070852bfb65c79460e30
def g383l7 : Packing := (2,5,6,0,0,3,0,g383d7)
def g383samples : Array (Bits × Bits) := #[((-0x1c7c0abe5eb0b5b794deac53933ddf265b3fbd77debbbff7ed3e5fc7dbfeb5c1de09ad),0x3835041a0c802027c003361601060690134460c209508104109022004008a24212652),((-0x38674d2c70fe63326aa5fdf75df7c25df7ffedf3fef5e2aba91da3790bdf73739b7e1),0x1c288328053019888301081491048f8080c08110c302d0c88414008862440588c44809),(0x7f70482928ec6864892a7808c5443041003000306a901d5cd20440308a310f1078f9c,0x3d70482108ec6035cd2a7ca2c536061530706a304a029342b68660288a31871038514),(0x80a735fca4439b2e3869d91109444066714241006ab062288005b03d09cb601f80f80,0x8003b598a4030a023055011412c961ea430201c00594401409011095010a200b00a80),(0x167c86b44125c70c20a80cbc7ec00400020c06c00546400210005cf480fbe001fff020,0x147c84a44125c50d00a80c8e1ec30880424881e00722b16ebe406cd4a0ef45014ed020),(0x183c3ab81e2a648807c2c202060a2405bc40004ff800180a32b78004109b53fe000020,0x18382ab81e02648903c2c012072c9614fe40a0d2916af00796b6a00c309b74da000000),(0x119338998a1ec23330ce50600f619822183bd9200010a002102fddf75f600000000040,0x11338919a0e423320c650636e78101b5b3e708c0079280753abfc771d20a800000000),(0,0),(0xfc4c4e66431b5758c1c33431509592059bbf857fc041ea02010020410640500000060,0x6c4c406603181449c382f0c900368e000810f216e8403f82840020080440100000060)]
def g383columns : List ColumnInfo := [(32,0,351,0,11),(64,0,319,0,11),(4,0,379,0,11),(16,0,367,0,11),(49,0,334,0,7),(70,0,313,0,7),(256,0,127,0,9),(24,0,359,0,8),(28,0,355,0,7),(83,0,300,0,4),(276,8,99,0,4),(69,2,312,0,4),(260,0,123,0,7),(2,1,332,48,6),(57,0,326,0,4),(50,1,332,0,4),(65,0,318,0,7),(104,256,23,0,4),(39,0,344,0,4),(300,0,83,0,4),(29,0,354,0,4),(5,0,378,0,7),(321,32,30,0,4),(262,64,57,0,4),(352,0,31,0,7),(74,4,305,0,4),(305,0,78,0,4),(80,0,303,0,8),(290,64,29,0,4),(72,0,311,0,7),(328,0,55,0,5),(18,0,365,0,7),(273,32,78,0,4),(41,16,326,0,4),(26,4,353,0,4),(51,0,332,0,4),(36,0,347,0,8),(344,0,39,0,4)]
def g383autos : List (List Nat) := [[],[98,131,84],[16,66,101],[16,82,131,100],[48,129,82],[48,129,98,16,66,84],[128,49,100],[128,49,66,16,82,98]]
def g383levels : Nat → Packing
  | 12 => g383l12
  | 11 => g383l11
  | 10 => g383l10
  | 9 => g383l9
  | 8 => g383l8
  | 7 => g383l7
  | _ => emptyPacking
def g383index : Nat → Nat → Option (Nat × Nat)
  | 12 => lookupWord 8 37 4 10 3 3 g383h12
  | 11 => lookupWord 48 123 4 13 6 3 g383h11
  | 10 => lookupWord 79 299 8 15 8 3 g383h10
  | 9 => lookupWord 39 99 5 13 6 3 g383h9
  | 8 => lookupWord 1 5 1 8 1 3 g383h8
  | _ => fun _ => none
def g383 : Forest := ⟨383,12,fun j => g383samples[j]?.getD (0,0),g383columns,g383autos,g383levels,g383index⟩
set_option maxHeartbeats 0 in
theorem geomg383 : graphValid g383 (boundsBefore known255) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=3) ?_⟩,listPieces_all (d:=1) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem tablesg383 : checkedTables g383 12 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact spansBlock g383 7 0 [(2,8,0)]
  · exact spansBlock g383 8 0 [(36,8,3),(8,8,1),(9,9,1)]
  · exact spansBlock g383 9 0 [(3,8,0),(36,9,3),(36,9,3),(36,9,3),(8,9,1),(17,10,2)]
  · exact spansBlock g383 10 0 [(6,8,1),(13,9,2),(28,10,3)]
  · exact spansBlock g383 11 0 [(6,9,1)]
  · exact spansBlock g383 12 0 [(1,8,0)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low383 : Lower true (vars 383) (graphGoal 383) 13 := plain_low (hints:=12901687553) (by decide +kernel) (index_root (g:=g383) (i:=0) rfl rfl (before_sound known255 valid255) geomg383 tablesg383 (by decide +kernel))
def known383 := extendKnown known255 13 [(383,[]),(447,[98,118,81,130,50,65]),(495,[116,83,32])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid383 : Known true known383 := extendKnown_ok (m:=383) valid255 low383 (by decide +kernel)
def rootLookup (nb slots sw vw iw pw : Nat) (data : Nat → Nat) (h : Nat) : Option (Nat × Nat) :=
  let a := h % nb
  let sh := packedAt data (a*sw) sw
  let row := (h/nb+sh) % slots
  let word := packedAt data (nb*sw+row*vw) vw
  if (word >>> (iw+pw)) == h/(nb*slots) % 2 then
    some (word &&& ((1 <<< iw)-1),(word >>> iw) &&& ((1 <<< pw)-1))
  else none

def rootSSamples : Array (Bits × Bits) := #[((-0x3b3efc6733ff4e7fef7f80e79e776fc59bfefbdf1499ede4cb986d7fe38e077c08c79),0x4c10098c400b1801080251c4088901a6401042029620009142392800010908115182),((-0x1ef5ad9ef3fbfdf9bcfa6f9f807fff3c7899e73b6c79d39b3f67e00995b1bcf377c01),0x210a526108040206430490602b000040816618c492840420400804162a444304c8254),(0x1c01f2583c181c09e1807e41030c788020071cf9318708e1e308738f840f0fcf8,0x40052583c181c49618054410100288020010029308708e0a348508b840b014a0),(0x600607e0080c000600e01ff800e1c0f8007c0f81f01c1f80f01fc0f83f007f00ff00,0x600002a0080c00060000029000e140f8007c0681f00417805015c02837001900eb00),(0x380c7f80031f001f800ffe0000701ff000f800ffe001fe000ffe000ffc0007fff0000,0x380c7f00031f001f800fda0000700be000f80097c001be000adc000d7c00066ee0000),(0xf800003e0001ffff00000007fe00000ffff000001fffff000000ffffff80000000,0x3e0000ae51000000053200000aa69000001fff6e000000fffed600000040),(0x3ff0000003ffffe000000000007fffffff0000000001fffffffffff00000000000000,0xe50000003e9d4a000000000007fffbf7e0000000001fbdfbff7fbe00000000000000),(0x3ffffffffc00000000000000007ffffffffffffffffe0000000000000000000000000,0x3ffffbffac00000000000000002cdeffd75596feffd60000000000000000000000000),(0x3fffffffffffffffffffffffff8000000000000000000000000000000000000000000,0x31afffd5fc162b551aeffdd6598000000000000000000000000000000000004000000)]
def rootSCols : List ColumnInfo := [(0,1,332,412316861106,8),(0,2,312,824633721541,8),(0,4,305,77309412042,8),(0,8,99,824633721748,8),(0,16,486,521,10),(0,32,30,17179870145,8),(0,64,189,770,10),(0,128,347,548,10),(0,256,23,412316861160,8),(1,0,494,134218256,12),(1,2,312,824633721540,7),(1,16,486,520,9),(1,32,30,17179870144,7),(1,64,156,4294968098,7),(1,128,330,134218292,7),(2,0,445,77309411904,12),(2,1,332,412316861104,7),(2,4,305,77309412040,7),(2,16,480,1049101,7),(2,64,189,768,9),(3,0,428,77443629648,9),(3,16,480,1049100,6),(3,64,156,4294968096,6),(3,128,344,548,6),(4,0,379,824633721472,12),(4,2,312,824633721537,7),(4,8,99,824633721744,7),(4,64,57,824633721730,7),(4,128,347,544,9),(5,0,378,824633721472,8),(5,2,312,824633721536,6),(5,16,354,824633721480,6),(5,128,330,134218288,6),(6,0,313,901943132864,9),(6,16,480,521,6),(6,64,57,824633721728,6),(6,128,281,77309411936,6),(7,0,504,512,7),(8,0,487,33554960,12),(8,4,305,77309412034,7),(8,16,486,513,9),(8,64,165,33555218,7),(8,256,23,412316861152,7),(9,0,486,512,8),(9,16,486,512,8),(10,0,437,77309411904,8),(10,4,305,77309412032,6),(10,64,165,33555216,6),(11,0,480,1049092,5),(12,0,355,824667275920,9),(12,64,177,770,6),(13,0,354,824633721472,5),(14,0,497,512,7),(16,0,495,512,13),(16,1,332,412316861090,7),(16,2,424,581,7),(16,4,353,650,7),(16,32,78,897,7),(16,64,165,6292234,7),(16,256,135,616,7),(17,0,494,512,11),(17,2,424,580,6),(17,32,78,896,6),(18,0,428,77309414977,9),(18,1,332,412316861088,6),(18,4,353,648,6),(19,0,428,77309411904,8),(20,0,355,824652595848,9),(20,2,424,577,6),(20,8,99,824633721728,6),(21,0,490,512,7),(24,0,487,512,11),(24,4,353,642,6),(24,256,135,608,6),(25,0,486,512,8),(28,0,355,824633721472,8),(32,0,351,412316861056,12),(32,1,332,412316861074,7),(32,16,198,15393162789641,7),(32,256,23,412316861128,7),(33,0,334,412451078800,9),(33,128,330,134218260,6),(34,0,349,412316861056,8),(34,1,332,412316861072,6),(35,0,476,512,7),(36,0,347,512,8),(36,128,347,512,8),(37,0,330,134218256,5),(38,0,281,77309411904,5),(40,0,215,15393162789632,8),(40,256,23,412316861120,6),(48,0,334,412316862081,9),(48,1,332,412316861058,6),(48,256,135,584,6),(49,0,334,412316861056,8),(52,0,330,1537,5),(56,0,455,512,7),(64,0,447,512,13),(64,1,396,562,7),(64,2,312,824633721477,7),(64,16,166,13194139534089,7),(64,32,30,897,7),(64,256,23,412316861096,7),(65,0,428,134242834,9),(65,2,312,824633721476,6),(65,32,30,896,6),(66,0,445,512,11),(66,1,396,560,6),(66,4,305,648,6),(67,0,428,134218256,8),(68,0,313,824633729666,9),(68,2,312,824633721473,6),(68,8,163,784,6),(70,0,313,824633721472,8),(72,0,167,13194173088528,9),(72,4,305,642,6),(72,256,23,412316861088,6),(73,0,166,13194139534080,5),(74,0,437,512,7),(80,0,431,512,11),(80,1,396,546,6),(80,2,424,517,6),(80,8,163,772,6),(80,256,135,552,6),(82,0,428,3585,8),(88,0,167,13194139534080,8),(96,0,31,9208409883520,9),(96,1,396,530,6),(96,128,27,8796093022980,6),(96,256,23,412316861064,6),(100,0,27,8796093022976,5),(128,0,383,512,13),(128,1,332,562,7),(128,2,312,581,7),(128,4,305,77309411914,7),(128,8,99,788,7),(128,256,23,616,7),(129,0,334,4966056496,9),(129,2,312,580,6),(129,32,30,17179870016,6),(130,0,313,77309936196,9),(130,1,332,560,6),(130,4,305,77309411912,6),(131,0,312,77309936196,6),(132,0,379,512,11),(132,2,312,577,6),(132,8,99,784,6),(133,0,378,512,7),(134,0,313,77309411904,8),(136,0,355,33817108,9),(136,4,305,77309411906,6),(136,256,23,608,6),(140,0,355,33554960,8),(144,0,367,512,11),(144,1,332,546,6),(144,4,353,522,6),(144,32,78,769,6),(145,0,334,4831838752,8),(148,0,355,18874888,8),(152,0,355,262660,8),(160,0,351,512,11),(160,1,332,530,6),(160,64,29,770,6),(160,256,23,584,6),(161,0,334,134218256,8),(164,0,347,512,8),(176,0,334,1537,8),(192,2,312,517,6),(192,4,305,522,6),(192,32,30,769,6),(192,256,23,552,6),(193,0,318,512,7),(194,0,313,524804,8),(196,0,313,8706,8),(224,0,31,8796093022976,8),(256,0,191,17179869760,12),(256,8,99,824633721492,7),(256,16,166,17179869769,7),(256,32,30,17179869889,7),(256,64,189,514,9),(257,0,190,17179869760,8),(257,32,30,17179869888,6),(258,0,189,512,8),(258,64,189,512,8),(259,0,156,4294967840,5),(260,0,187,17179869760,8),(260,8,99,824633721488,6),(264,0,167,17213424208,9),(265,0,166,17179869760,5),(266,0,165,33554960,5),(268,0,243,512,7),(272,0,167,17186161224,9),(272,8,99,824633721476,6),(272,32,78,641,6),(273,0,238,512,7),(274,0,165,6291976,5),(280,0,167,17179869760,8),(288,0,31,429496730304,9),(288,16,198,521,6),(289,0,222,512,7),(292,0,27,17179869760,5),(296,0,215,512,7),(320,0,191,512,11),(320,8,163,532,6),(320,32,30,641,6),(321,0,190,512,7),(322,0,189,512,8),(324,0,187,512,7),(328,0,167,33554960,8),(336,0,167,6291976,8),(352,0,31,412316861056,8),(384,8,99,532,6),(384,32,30,17179869761,6),(416,0,31,17179869760,8),(448,0,31,536871456,8)]
def rootSAutos : List (List Nat) := [[],[81,130,118],[16,82,131,100],[16,32,48,128,100,80,116],[32,83,116],[32,49,128,81,116,100],[48,33,133,118],[48,129,82],[80,16,33,50,116,131,100],[80,129,50,116],[128,49,100],[128,81,32,49,100,116]]
def rootSD14 (i : Nat) : Nat := 0x20d84d72a811e41a8f13ff
def rootSH14 (i : Nat) : Nat := 0x2f0000014edb20106622b8c2510416615140348080
def rootSD13 (i : Nat) : Nat := 0x32898903572a99181643c4d83b08f1aca26098d5caa649a1f61480f16ca2609921caa649a3014c19a878cd97100ffd30ffd20ffd10
def rootSH13 (i : Nat) : Nat := 0x310815207a1a1856a8d3a40000372b480e2304301249142c9b9e8e8724b382c72589335c8f91509a2e05557399451794c982231d89f1adcc108500900e8182cfc5d029a6cccbb35d8b2e2b723c552840469a5a860000cd0048e03402020002888800380004010010c20407400825c0
def rootSD12 (i : Nat) : Nat := 0x931180b34c253186dca48b0ce72a26e0cc48f16a8795a6630251882f4780a321c197450ad41638afd3326c3da051c2514e900b9ca8f192644c1669993148db88c6703ce55211e2d4e72a6af28c90970f49a90d844b6823c64122f69987b94167944c04bb08a74828ed09bca025ca930b7d30a407876095470ba905aa3c83942f24c4a7942169993520b547812b0bb0974ca80a46ef18850be051479ab8372a3c78a01614a216999317c12b951e32135301431431f28ce12b265594c294548f26a641c1897c5b8a1e514ba60daa384a1a47935320ed331814dca0b190f28541b526e0c6f109ae524da6043e564c2a3203688412adca14031f2842d332624e3c5a82558a0e5795a6131b0d20a384a92bc50d304ac98938f1ca09521e6c20c699e5059b5520a3a414063cad3326084250f1909a942d92ba664c3e61ee55211e24350b014f2b4c3489ec6126e0e6a8f1810829e5699931aa3e84ac84d51e2fca3434c29718e0d6a0b1016795a664c6a8f80ed211e2d4a0b3ca357261506d6404244125df95a614c38ec212d20a3a8b7f28a515025e0d261b4424879c1ec3e5741c86d415a0ca1434cc98ac31025a423c7295c1ec313413e5741c86d415a74e72a30aee6ac76a5a7c65d2366171f2dce9acd9017355b943d2c111cfa0dacbe0a8c8e87945f047432017c003ffb02987ff64530ffecc241ffd81483ffaa6907ff64d20ffe98a41ffd91483ffb06887ff60910ffea9221ffd32443ffb26887ff64910fff0ca41ffe39483ffd12907fe4c120ffc902217fd98482ffb26885ff64910bff0ca617fe19482ffc52885ff8e520bff1ca21fbe494c2ffd12905ef92530
def rootSH12 (i : Nat) : Nat := 0x509ba7d9f513e4c102bd116f3216b00c00280ba0c760c00002db7a105d14d91f218702129e92bc0bc0610445a6c0839a293611cec5bb4d8624148066437a119aea21e4c2a4800000014b420210148c644e86850889460795e892a20a2ac0d1bab4a18b89b008114b73f0491ec812978109d50f493537c992a3f819a0aba590bcc194001239d0c1dac837aa8ab00216912a7c95710d40a974383912b455b07184d2b128ccbbf5cdc06680d0a780a066c5279d75bc99700dd034c496e61630796ca380c20249d3d1c5c3092893c2438aae0da416958013002a05c3acd66113f0d9a22ecf610c090a4a8002c7c2a2948831963c05a85e0a58000000242834603b43e23d823813eadba23d10b3ad9745be59653a8281935008017003933caf3a81101f9629b2601a022b1098801980c1a1642bc0fe7b931d8a94156a09214d2f8027476566e024000048232043335a2b4204deb4f89046c8542861aa492135a2988d36138511c3c95856c843882354e48c83212e01140b3941018af6044895be6ecf400b4852003d66e07e03542a412d080d84001c8ea496ce1290cdb24a581241f602da83386c9c3250ba803581ea05e068d0742ca94c082856819d131000858017c8ef0ba1cdd8ea8e9a6bd33d0700d900b5c2514458c48ba6a972000129e5e52f6a1620008425a1e82646800c6a62d330b9db3a0e2f6e01753353600f14b28574302948b0396617160c1a9fdeceac2c4f02681547644bc40a822c04691b60d81b012c127b5859151c811f24082dd87e88c000961800213670e20cc33e0b0000a5dc994590a97b22c15b05a797b406d94338478ad1411216e4b54ec08fe562896b07521a5074030160de6ca305382b983c15806f21c8b100630aa1da41ce87f02589ed0a889bad026a02f60650bf063914d40794f247d06a07410d39e111352da40b2ea62749c0c8d5ba13a59c25080e10785975b120112dd06f1b6200800410002383072904441030000184045060500547950111882400401d0a9c0000004285041894408449886e005091c000100a0800e0200380088400502a038008000821614002001421008000002a29003120d28e305420d164820002a00800c0028000081a217200210014c0006e8003003c0a70c00206000038000140820000b93000004000000011c30685062c01f160090c00ac80000345810000482
def rootSD11 (i : Nat) : Nat := (if i < 2 then (if i < 1 then 0x3ffd5386520fffa6982443ffe3a60910fff96982443ffea954d20fffa2993483ffe8a64d10fff54e89483ff9a04c520ffe6a130483ff9984c120ffe60530483ff9a54c120ffe65530483ff9514c120ffe68530483ff9914c120ffe61520443ff98348110ffe6a120443ff99848110ffe54d20443ff9a548110ffe65520443ff9a348110ffe64d204437fda166120dff6a5824437fda960520dff6a5524437fd9864d20dff655934837fd8564d10dff6a1934437fd9864530dff609934437fd9864d10dff695934437fd9564530dff549934437fda264d10dff649914c37fd984c520bff6a1914c37fd8364910dff6a1924437fd9864520dff661924437fd5364910dff655924437fda364910dff64d914837fd9364910eff66181482ffda864520bff6a219482ffda88e520bff69593482ffda58e520bff68d91482ffda386520bff68e89483fed8254910bff6a193442ffda864910bff69592442ffda364910ffe82998483ffa0a64530ffe829934437fe1a66120bff86998482ffe1a64d20dff54a194c3ffa194c120ffd606194837fd9886520dff6a2194837fd5386520dff64e194837fda386520bffa6982442ffe9a54910dff8a993442ffe2a64530bff8a9934437fd858a510dff60e294437fd538a510bffa6981482ffe3a66120bff8e982442ffe3a60520bff8e9524437fd988e520dff8e5814837fda88e520dff696394837fd858e510dff60a394437fd528e510dffaa5314837fea94c910fef92993483fbe4a64d10fef925814c2ffe5a60910bff969934837fe5a64d10bff969914c2ffe5a64d10ffe965304837fe5964d20dff965314837fea954910dffaa553483efe6a60520f7f9e952442ffe8a64d20dffa2993442ffe8a64530bffa2993443ffa894c120dff54e894837fe8964d20dffa25314837fda3a2520dffaa5814c37fea960520dffaa5824437fea960d10ffc54520443fe9524c120dfe66130483fd9534c120ff64c5304837f99348110ffa549204427fda864d109ff6a1924427fda8865309ff6a2194827fda88a5109ff6a2394827fda88e5109ff696194c27fda58a5109ff696394827fda58e5109ff68d924427fda3865209ff68e294427fda3a2520bbf69a894827fca954d209ff2a5314827fda2865309ff68a394427fda18e5209ff68689482ffa0a66120dfe82993442ffa0a64530bfe829934427fe1a66120bfe86930483ff21a48110dfd606194837f61a64910bfd869924427fe9a609109ff8a9934427fe3a64910ff68e5304837fa39481109ff8ea19482fbe4a64d20def92993442fbe4a64d10fee929304837be4960530def925914c37bda1925309ff969934427fe5a8e520bbf9a981482dfe7a549109ffa29934427fe8a64910dfea25304836fda6a2520cffa25984827fe8a865209bf69a894827be4a64d10 else 0x612672b1e02538130ce3244986004a6f942dfa60ac0ac24c2307604a9f94078638ac0a6e42b502c40b417427c2a7830db51c12a3e574c1aa1f74836aa8e0951d33930ae189a431e5ca04a8ed414c12809479a403f84017c94780bfc18141960b05385c06891a6286b502c0685f95e0c50e6a0840d0c0ac170a4b941f029e90c78da93f2812853d20da8161be502e0a76413543c04a721fd33931b71660074863c7949029f2817053b218f13502547cae4c14ec863c0da094e0a0678a6b219ab1e0be3f4c04a09c6909e1759ab1e3904f4c19a2c053590cd4d1c12a05d025059d844985308c71741533559068e094dd30280b01a35a849b4704a883bd3387fcaec214f4802c47cae99c60217831742873502c4f83f95e83c802c8da60662ebb0853d200acd463a64a4e316dc15e26c1372bc1a2bad4cb9553021590f062e850d6a056918812c602a40b808bc1b6a0569e3013468d2614a2cb3563c7409126347b0ba0a8e094d9331374ce4d43c5b5af03c6db4863c5cc5863f2b9305502f5328c155cd58f17e4044d260ad83c688ba1478f1e528558600b56431e3ca04a78582e85f05a04af2aa3e904061e99c983a05a3958f34808109209560102d01f395a404084904a87942dc2807212616ab5046474ce4da431e0b72f83f95e83c866a05869a5b331662ecc00975d2d7257a4aa294a128264dbc9659253238a44848338fc31e123a9c7178db71a26313c6588c4f17562d2455d8a43133e244444187f50ea21a5c2f984f7087a0db414e81cd02aa0213fc47ecefc81f513e457c28f6b1ea7bd13796cf139dedbb73762cea35d1839de72ece465c5e386a6fc2dde5b93b6bf6caed791aceb5616a34d245a35b42467a4ce2d9a232e7652ac90d8e831896242c33d833afe95f02bcbd7742e965c9eb7f56db2d645a0eb2a9626ac065752ad5d582aa71543ea7614ce296b521ca299424a7ec4f1e9c9d370266d4bf4967529524d848ca90d11f6a39046508b2d152a25e445a87f10bf210b411a8094fe41f6b3e747bccf459e393bce7654e911caf388e6f50db09aee34ca67c8cba192231a061ccc2118112f265c28b5c16452ba455a8a811484284e4f289bc131b2566495890211a72252433082c8fe61f123c847678e881c40370c6b30d09195831105ee0ba016b22bc45550a5813e0264c4a088ef110e20a83ec07910e681b5c33786280bc21560278048808400f641ad82dd04d408600dd813d01c0020c0238000fff6a5814c3ffd5260530fff549914c3ffd5366120fff54d81483ffda954d20fff64d81483ffd5364520fff2a553483ffda960d10fff69582443ffda360910fff6a582443ffd5360910fff60d52443ffda354910fff6a552443ffd854c910fff6a532443ffd8564d10fff60993443ffd5264d10fff61592443ffd8364910fff54d9244) else (if i < 3 then 0x250de60166fc9a83414e0942e1c0ea091721fc4b0403014478248380ba058170ff281623c1221b42e180408d0800941736a0a6717382429b0f1680502001e403161f8242982c0281000f202a0cc14a73ab502c7210b1002446b6a0a6100129ba67260426bf4863c79407902d81282e11af282305338af7940b84685308c1ace074db85ac1234c1706f0e01802a3a0ad4d1da6dc1a0460a61ac4984039b7068234298460d660840b0538250b8537629c1285c27a04a00d05d63c0e0e4022203863c1481d85d3900570b022a4168b405869837b9004a0790e80548c988452ec83ca0a88154a9064b47b20095e5442405a56e34c3046d35b641a385449afa1e1370481e08060b58602832619e258255cac780b94c98439d60b41705f590cd40971e285085a64c1185be3cd206dd0c985a0340d02c02166a0ad8f0ab292f0be0e611b0c09305c78a0a2412e9033e175a38cead407942f80e8ba05c40982c0398461260b8c0324f0d2296e82a3bca0a880a82f83d4a47211b621025174916030452c6d2fb51dd0025456a05c0786940128b00f40d047182582c11c0cc8108160530604e99c62dba3c067e0e5250f05772915ac5d5183301e0518becd4151d063c50b5022d305a5261421fc16046c7814d63078c2b7c781503866a74017138f0dbba01261b41642c0a68168171d007f33c0b02a05340147401701290608591261fc2305330ba04aa74ead470ece82b501e4d90148158660482ac22ce0940f5264282a4228b5385a2d5a431e0b636c078ff2b9345432025864055cd58f0aaab8784fc12078d704017d51f483ca505d15f83d2803d1a6f2b1e0ba482d1a78f1e50a41741b415c2c180a17413c1580af06740d302579510940cc2d42c17c14c2589379551c12a80f0c99122a9a3dca88532812e3cd2016980ce166184bc2045f3ca12751c12a85f3af16e097482a614751c3b56a03cb17d7283a0461260942d1c36d6a16e28c221b70d07ad42dc36825146124db86840251362041711368a33a01149f2b930256981539aa6a03c1b42e5905c3c063da92b02c85815be507f05ce82a3b21e0be04da4029bcaa8e7e6a0742cb4cec22ebbb82c0a7a4150f05d05304a0d00f040059a41b5281a0180582e812853cd4d1ec827e51560ac14c1282e8799a9d02403004c1fe0e9307e13c16848bcac78b00c0945307d0b56431e66a41b7f06293c80711475a81620648930f816b4863cad4716f8f05204b0b4126c806d402ec122903e85a04ba41e55474c2c1a5e0c4c0ba146f2821238c0d50e2e806a56a0587169c985a8980da10ac80544056c300bb048cdec227c6602574151d62d05a89f04be0c36d470a880080d0128d10a62985d590cd58f1402c0ee091743543e053d20d1eb5282a0b405c294210c0b201b5006b048a41a216812b47d21729244fa672 else 0x2b16c6ddbba2c07a1ace6ddc1cb74ad8d4ab42c4595a93cd40d4142ac0ac2582e85828536bc2d0b504f8240e8ba09a864d826b505a36f2dc0f1c2b01d058165cc84d01874586dc2150fc128c41281e0d6904f05287e09842094269e9305903ad8400003c1270282dc160bb3a0908c55a8c2147407145c802393164d460dd80217c2e8e2dc5c8004da094ac9a8c05404a2e82d18ddd83577158ab2148287f066950a00c262154ab011405534a5582a00c142094ed30e2d1858b0c498a1482880589081a02521c58850b0000542c428580b80002529568840661602e04a284f0521080004a404b084000542053c3102610d0f03a0b8e0019a81104a4b5e6ed93027172094d6bce2b4c09e2e4b4980e81a04e1642680c38338582f85d54700060610b0dd8b0a8e000cc9b04caf0b57280e980a50f05c2481603403c717d51c5d04b1241fc1604040b924d061d787f12c100e0ae0c42c794a941284017da42a3b6a58590a02342587f1740b02020dd9260a1499d00560fe25820245d034741061b504bd2151c29a41a01487823425b6a1740b02e240a30f14209420155b82e04b0621e0780a99a9d0260a41856ea32048250fe0d2c866a68eb1730601760f1081e012853413116c2101286d0b868130615b825a300d035e6a0a8d1dd02c2805659c0bb353a004a10101400a0780a8456ed1f0782c1080c43f82508097940b42102c1080943685c40256d42a02005a28b31a16bc12e090822a02d20098d003c096e508a0ba6dc3a240e0980a9640088250d2304ab09651caa8f824933af17c1fc4b04048c13761341385e1302a020221a8398580ac2a0c093c078693a0c78f2980b19a8afc78f286987f0888174108160c411a1fc229c2a87f19e2782163c7219a85d26a3bca19c108160850b81bd00b19ab4cc78150508cb088809a1081605e1a61ac229c21c2c05d1b56704a1839a8298a5a8ee4180b19a825c78c601a0d30fe11120b0258421081ac5d05c3d2654c7583b6908bcf2b1e02e480b16d8f05d17711a1fe160454c14c1f25040d9014231012b47794a15ef284207f04a120c2f85405c04a0b8a3089886d1340943f982a05a56f4624a0cbcd41fc30025740d1d8150128781bca68e0d0538250b8636ed1c1a0840fe094201de504206829c1285c30afd215a81282e03c62ee2db0c50f1501701282e40cfc795a8298c21260b8f4983985ec7833c4982e381c016164db8bac126643f896080a0e78f0e88561260b8c02cdf935c300d04207f04a10138245f06b0a60b02308e385a17d824281d1b9424da3825495616e1545f094c78f28240c7b419a9604c058bba8ef28bb8a18841bd204cbb92617229c1285c39990aa6ec4d))
def rootSH11 (i : Nat) : Nat := (if i < 1 then 0xb2454e0049e98c89400d0c69400010924e7cca0000a00a5a001841758020969018a52981460cd82d4103a250106ada229583d6e1425be94a002414101bc17dce74ea623a0179d0b009401c812c062819a82941360060974502882322c4420125ec3e8cf2519d5ca0ef82be2ed06821395c8377c817941495c457c01b654ca21e0788103723060c00b445a07c153e119828286d0434cf68470123391604d5d6267381cc08f1c880d631940b000d4131853e06386408801488927809693602b64da22648f8c8073a104ed615043b53722d2100857417805b4171015d5a5cdbe160107a0cad054041a614e33855c89a803200ec3c54af245b381025e197065010c13c005f40a8075815a99c558a01f06712e782320fb3a1a15f2cd336c4e26f7283a603fb3fe0843e740f0828e0b210ba4d483e80ae80f88a3a082105187002c05004e485626e8044c052be8055a04440b9ce1c0f4851a13305ba8fc948218c84d60aab1468c38086023a4200d43be6f3bb5aa1662d80048862c0b1b6940c205e80f280e4152836449e80f4251a3ba9638071310a3920ea22c20e120a97a5226d71ba4cc0dfa3748e1841206c0000fa4051454e80f209fd00082b0000991268958382f8087852d6a0024403401a69124cf498b001af3da4996ac832571e063753f85548d73dbe51e0396080120cb37433200785240b6258a80e91660380012d3c058ec1f01a212992128c0000e0aba2ca07e22840d201aa04323ef347108404789c605402e171a549a89e03708615aaf79a855935b00000c60002c8e0002830539617edcd410784c08b35338000817400081245a7145000085bcba3a57842da35815e02436c4058ae6683b64144d440e7568201485da80b50980e6b3c6042803532added52902fc558a22698803fb55fb92f3a301b882181c1486028961fc28e02eb2a101fd11480ca2db56780db39eb15216cbdc682211250000050405120002010240e700005b0003030119000a020602044d07000c000001e20b173702000c031000136f00293b060102090a00070d0400000100001600033701000106003400030864001809010318370a031f003d3002000204000000011f041600150132050900000003280f340502000009fb0066050001010006270b0414760518072b1a000005216c1a0a03000003030000110d000031070a0b0e080003000d00005700080b0000000137745e001a024f00000b23071e0628010d010211390b08000a16021900032a020603133108240e04002f00000a001900130209c2030201070003000008070e04781f0c00960603130256010c0d00001c0a04134f022400071311030c000905120200243a0f12010a032e0200010004b706020612681b00141b31005700090033280000020015000205100f0701072b0000050000032504020389 else 0x97355c4e4f838f4ac005a8b50000122ddfed2282f60d1a3bc13a065842c0000000cc5c000008a0a733ae8a004bc15086560e439b807bd66c94d59c68e90406ea922200b420b28e28248482835411a20ca15a5dda0ba10080e2a1a9650009c12d433a0e0824c09d8180d3b046c06b95ba11283af3a483f4170011003ace4a09c005e14e02f0473833e169042e16a0534144032e120816051c04baaeca20601023154a5b27e61fbcf871aa03f51f04f211791bd0a2a39d60a853257784853155c860a68564132c0ae87425980db4db7122850eced21aef9f816d3655e48108857207d83bb4a183c50e3d66207602ec19ba22e015519a19d5e61352b29c0b30522e4c5d74e4a031f4cc80de083811a182d3b292952988fa143e572429e082431241b24ac0f9c662898014e0a186880d72078872a34c88282165a603dee263ce373d4292e9da5865113c5c15b90684dbb310164107e142068e07abb7b46780b5316a22a102054e0e8817338fa59682f81e608d1c8617b8322114946c177016687f20a441d539a01b53b410f15fe96e022cc4e05c80f3816b77d82388c40638517882d0b75d70c0da330913a0c413426120da55c2019ba1682882628515d2c0d802b2cb789f006425909a5bd01111cc440960044191ce94f3fa4968c185a2fa184276aab2fee0ebce614a8256f3aa462193364b799147556b842811e02780de22372f5201552401df192a29282723c24f524d2081029001384984a58156154d87098680ed667859c180d69a89c32428e35c888f9004816b)
def rootSD10 (i : Nat) : Nat := (if i < 3 then (if i < 1 then 0x6a581482bfb0db50c92213fd86da864910bfe436cc2408847fe1b6a239482bfb0db4ac9a217fc86da5481108ffc36d2c72905ff21b68d204433fb0db46c92215fd86da264d10afec36d1b24884ff61b68d924437f4a9434982411ff86da3a2520ffc2a50d2408873f598606194839fac0b510ca419fd6a21a64910cfeb310d3248847fe2b6a193442ff515b50982417fa8ad9848110afdc56d4b048857ee2b66192442ff515b30982417fa8ada848110dfd455053309047fe2b6a2194c23ff15b511ca217fa8ada54c1208ffc56d2c329877ea2b64d20442ff515b42982417fa8ad9348110cfdaa5153268857ee2b64d924427f715b46c8a415fda6d8186520aff536a8a609047fe3b6a192443bed1db30982417f68ed984c120afbc76cc326885fda3b6a1304823ff1db510ca411ff8eda88a510bfb476caa60907fca3954930483beccc47298241dfa54a39481108ffd56cc2629067be4b6a1934433df25b46c92215ef92da364910bf7496d1a408867be4a661934833df2532ac9a415ef92d9364520af7c96c9c329077ba4b64d20442fdd25b26902219ef6164a64d10cf7b51253268867be4a609934433df25330c9a219ef6964a64d10cf7c94a93268867be4a68993442bdf25b26c9221dee92a0a64d10df7495053268867be4a8a993443fd5252a498241dee929984c120ff3494a9a60907f9a4a4c5304837dd25342982419ef6a24964530cf7b7524b029867beba925814c3bdd24c14c8a619ef9262a64530af7c56d0c92987f9a4a8e5304833df4d492c0a619ef92da386520af7c96d1c329047fe5b6a2194c23ff2db5114a211ff96da88e5208ffcb6d44728847fe5b68d924433df2d494c9a219ef96a49645308ffcb6d1c329047fe5b68e294423ff2db4744a419ef92a5964d208ffcb6d14329857be5b686494c23ff2dc54c9a215bf9ada864d109dfcd6d43229866fe6b6a192442b7f35b42cc2415bf9ada8649109dfcd6d4322905efa6b66120442b7f35b30c92217be9ad814c120cdfcd4d4b029066fdb99a98148337f5ccd4c0a41dbd9ad8186520cdfcd51cb02906ebe6a925814c337f35b5114a2137f9eda564910bbf4f6caa60905dfa7b69520443ef53daa49022197f9e9a954910abfcf6a93268865fdb99e9524432ff5ccf4a922157f9ed5286530abfcf6a94728865fe7aaa5524432ff3db4b1ca4157f9eda58e5208ffd16d2c329847fe8b696394831ff45330c9a418ffa29a864d10cf7d15253268867be8a925914c23ff45b470ca411ffa2da38a510efd512a92609077d953a2530483bed44a6298241dbe6da894c120e7f512cc2609073fa89829984833df25512c9a41dee92a894c1208ffd16d14329857be8b686494c337f35552c0a411ffa2e2a64d108ffd172d326887f615254520443fa4a9aa4982419af9aa4960530 else (if i < 2 then 0x217fe96d814c120cffcb51cb02904ffe5b6a2394833ff2d304c9a219ff96a2a64d109ffcb6d1d129057fe5b8a9934427ff2dc54c8a613ff96e2a64d109ffd74a9b309067fe9aaa553483f7d35b0298241bbf9a95360520ddfcd4c9b02906efdb39a98148377edccd4c0a41faf9aa4960530bbfcf6d2b048875fe7b54993442eff3daa4c8a61f7b9e98254910dbfcf4c1aa4886dfe7a68d524436ff3d352a922177f9ed5264d10dbfb673d2a48875fe7b54a194c3aff3daa51ca213ffa2da564d20bff516a9a408857fe8b54d92442bff45aa70ca415ffa2d538a510bff516caa60905ffa8b69520442bff45aa4c9a215ffa2d5286530affd16a9472884ffe8b69639482bff45b4b1ca415ffa2da3649109ffd16d1b22904ffe8b68d92442ffd45b46902219ffa299564d20affd16c9b229057fe8b64e194833ff454b2c9a417fea2d9348110cffd14a93268857fe8b64d924437fd45414c9a219ffa2a5a64d10cffd152ca62904ffe8b68e19482bff45b470ca41ffaa25524c120eff512caa609077fa8954530483feca9d12982419ff6968964d20cffcb544b269067fe5aa25314827ff55aa6c12213ffa2e2a64d10affd172d326884ffe8b96993443fe8c0a6298241ff86c95148110bfe36b0d2408877e95264d20443beccc26298241cfe661814c1209ff37105322985fd9b58e530482f7cdb512982415fe2e5514c120fed2a6a9240884ff9b1829984827fcd8534c12213fe6c29a549109ff3614d3029067f58168e194827fadac34c92213fd6c69a60910afeb6354a629057f5b1aa5814c2bfad8d52c0a415fb6caa94c910afdb6554aa48857edb2aa582442beed9d5298a415f76cea94c910afbb6754aa69057ddb396531482beed9d1298a415f76cea960d10a7fb7154b029053fdb8aa5824429fedc472c0a411ff6e1a58a5108ffb70d2c728847fda9aa5834423fedc34714a211ff6a6a9609108ffb70d14728847fdba8e5814823fedc454c9a211ff6e23a649108ffb711d4329047fdb8969934423fedc4b51ca411ff6d5a3649108ffb6ad1c329047fdb568e294423fedab4744a419bf54da6a25208ffb6a54a629047fdb568a194c23fedab451ca211ff6d69a609108ffb6b153268847fdb58e9924423fedac750ca411ff6d68a64d108ffb5354a648856fdb6a25934823fedd4b298a411ff6ea894c5208ffb670d3309047fdb3a299244337ed334744a411ff6ce8a865208ffb731d3029047fdb2969934423fed9514c9a211ff6e63a609108ffb731d2a48847fdb9969824433ded434324a619ef689a192530aff416d4326884ffa0b6a1914c27fd05b50c9a219fe82da8649109ff416d4322904ffa0b6a192442dfd05b30c0a413fe82da564d20aff416d2b26884ffa0b69592442bfb0db50c9a217fc86da848110cfec36d43248857f61b else 0xc6c9d5844ec13b06bf9ac95729aa0697da1267759a865fd9566485904630d63462095ca61058185f5d78a5d257145b1d6925975634579d5ca5685584553d53253f545453514b7526947d515142b4fd93cd4ec136f4ce927e4c452dc4a6d27e332924948811d3464914543e10c341d90414090fef3f18fa93dd0f3f3c28ee13ab0e6b3848ddd36a0d8b3588d453470ce73328cad3240c7331ccc562d50b5430e4bec2eacb8e2dc4b542c1cad22aa4a7428fca2227e49d026cc95a24948d8222c85620247a41dec75e1c746e81a9c67218045e4165c55614244e012dc49a11f446010dc40e07f81fe0fc43d40eac3820d6430c0bbc2c60a14268086c1fe07241ac05ac0fa01c4000ffe302a8a60907ff18354520443ff4a930298241ff654d814c120eff30ac9a40885ff9b5a2530483fec5caa698241ffa60d5248110ffb306a9a40887f798554d20442ffcdc2a690221bfd605a386520bfeb634d3048877ed82549934433fed2b3098a419ff6a15264d10cffaa4d44329867fd526a2394433fec1b4b14a215ff6d63960520cffb04d2c728867fd8568d92442bfedad12c9a415ff6d6a94c910affb70a93268857fcba61593442bfe5d2a4c9a215ff6e2594c520affb6b44a629067fd8568e29442bfedc2a6c92213ff6d5a3a2520bdfb6c54aa6906efd5369a894827fe5d2a6cc2413ffaad53a25209ffb6b1d302904ffdb5a29934833fe54b52a9a419ff615a28e510fedaa6c12a4885fbdb4a69824427fedc474a92213ff2e953609109ffb6b1d304884ffdb5a29934427fe5d304c9a213ff6ce9a609109ffb674d2a4884ffdb3969824427fed9514c9a215ff6c6a954d20cffaa6d0d12905ffa0b6a5814c2ffd05b52c1a217fe82da960910bff416d4aa6905ffa0b6a552443bfcc2c14c9a21bfe6160a64d10bfec36d4b04885ff61b6a532443ff8c0c3298241ffc6161a48110ffe3070d240887ff15386920443bfaa9b030ca41dfd64d8186520efeb02d1c329077f58386992443bfaa9c34c9221bfd6161a64910dfeb070d324886ff55386992442bff4db4ac12215ffa6da354910affc56c2b26885fee2b6a5824433ff15b510ca617fb8ada354910cffc56d2c329877ed528a9934437f6a9454c8a619ff6162a64d10dfdaa515326885ffa3b61520442bff1db0b14a213ff8eda864910bff476cc2408857fe3b6619244377f1db4d44a413ff8eda564910dfdc74c12a48867fd858e992443bfcc2c7290221dfb609528e510affc56c2c72885fbe4b64d81483bdec2c94c9a21def9295264d10df7b0b25326886fbe4a609934437df252a4c9a21fee929814c120ef7b5324b029877bdba925814c3bdf24aa4c0a61def9255264530ef7b6524b02985ffa5b60d20442bff2db06c92215ff96d838a510affcb6cc2629057fe5b66239483fb72db04a92)) else (if i < 4 then 0xfe605b05c0d306f20320637350182165c81810c11034c1fc904a0b8204283402c030240a01e8180c2440c055200568560a6482605c0ba040201585d0298229014c2e810060a743012408045610b00400a10702a3386002004d02e02283c1c2681701156dc8085068056060409203013c80228180c14c0cc40b8124b6e30b004603306c20358198814c22c409e16a204f0ba10028298814c2d441120ac16415207c05c602b06802303e097282e0198814c07840b806020890560b20a803e02e371e06983f822138f014f0b060c256e142090406609a07f02e24128398b86017007860ff08403c3825078158781560c6a3f4861600f1c06420422812480de0d014e1020f20e860a7081e3c6a607401e30b545780c83413a402ced1c1ec288078df07e99479f21a1fb5eb6d456806d0b801e1e0a02e0b498284070258100bc1e0380b904a4055c3c02e15508e28088458660241210f0b00b805f9a83502a38f017d202e12c20d409666d6d009c42530176b506a0416161749b1b435020310a094c1a80e7484309305702e184b02b880202d4416a0b420530be02e18020150050c0202e8416005c2a90c3c05a1f9a82d05d0fcd40782e860661263a004a08c0b4604605310540248298c13a24e096f280cca17406620b706708808104901e30600180818c28c124078817405c202e08a02407403e281282b05af9ad352c802a01700f27cd41540741640b02d50b3d86a401140b97f07b5fa1fc4dc13f41f20b6d4569fc5b35cfbb7ec4fa9fe96f9e7e68f92fe22bb83df9f773db3f62bd3df453cf7f36bca5f223c5ff10bc19eff3bdfeedbb99edf35fd572bb5fecabaf5ead3a7fcaff322e8fb69fcd734f1e70f9fde7839c3e70edc3b70f9c3e70f99ae5c7948e00b8e5c79b91fe40b7f1e3978e5e3235eccd738b7e20b84de0c3802e04f7f1e00b7f1df2379fdddb765dd2372bdc3b6e5daf369fda0aee0bb0edc3d9c7654d8aedc3d86b5fdd7b35dbd6fb589d58352bd43b4f1d32349fd17b41dcfa33b3cdfaee0cd86ec3315ae26cd72ee0ccff322cc172e8caff296c95722cc80f1e6c6f7188c51f11ec3a70b4c1ff056c056ff8bf6efb2be26f60bd0ef1abc6aef1bb82d3eb9b2ec3ba9ada6ba26e6cb90c47db89ae09b782dc3b69ad89b4facadb442d78b56ed3eb4b6d10b3ceccab2b6c84b16ec32b056bc8aeaeb76ad66b59acf2b13ab7aaa9aa02a3fa82a9d5a6e298fa4da901a3628a36a81aa0a1ea839a0727f39f5a79597be76c9d0e71a9bc66c89a7e66a98d660c97be5c6967655c946e12a933a12a06b248d91003d40f52423901a3ad8d823378c6a2c18a3224b87f8c56872617c84ecc9084aa0b981e20377fa947d7ea5f8c7d5df167b55e88791ddfa7685d6c5351d377439cf17321c0c727dc7670d5c0c53515846f8dba25729b795611b5 else (if i < 5 then 0x6c0788b6d46b456ad44d180028b901721c182f8170fcd70531280bb0b0a16a2aa2abba1410010cad0a0c15c23c160785805d884308601711c182a8170c2d407400078301019002160c015082c80ec402000220b2008003180181388094000417403a0003014000160c707882c0220417410b00a31058004082c0200a09a204d005105d00e8080c00404050ac0e603a30ba093856180f12902d0c0741fc4838817c136c2192b32607f0b51044032817810102e8008418a06020000140051be561e05d00f100949e4150078809a03a08030a105c05602e053281681705d020101d00b810016881740922025048053181983a61602d7486a38129c0a80b011814c987874005c30530b904001e201284b00f0c2dc2cb8255a82e8a04a080202508d01e18340128813c0780501241a0a00604a05c302702508b18440128170c0941a00b8600606805c30310d40531da60658128229021c1e80942e881660340923025068104701282d0c0780941d060260ce15209203c502701d0a9054049280980f04385582e837982dc19c28c1a0120a02601c15603c10208a60b205c10040658801c01001426404434c1e0e03801613a15217408060d407a01e182d06009c9a04da7805ba438f0168e0d213806816a40560890d4073040282b04485a85401f017182d41c0270078803811216a15207c05c60560690c109302e2d04840cc0ef0b30c424c72828b51c095214201619614c03c505000c0a703d0ba281e0058468298658209816811824c0941d0a054124208407405c02e202785a0540240299400022c1441b0300a00c0dc00212e0fe090602a0b908507f048280303700005382202d18c3c11417002c3101e8100e61e09606c044400904d0ba0402004a3680f0c094078404a0b803c301101e053180e02e0170fcd40501340680f4a00004a03c366a02501e1fb080980c82d034140941ac078605c1742b4c00302c01e206581280f0c2c00501e8078802004a03c3f8305584a05302e285b83382d05380f024996400b811814c816c0d603c05c40af0110681857be500f0df282d00941ac800403c201d0ba02e092040280004b059840817140ac2d02341700b8a04a0b805c30b920907f0960402806f0485a84084d817181400302a0094300a03a05c124080405a0c7e3c0a803e02e301284681700f100ac0b8248100802204a03c304f04c39004d01a08e30000128802417007860b803c202a0260480532013822882f80a812014c802818003c30c70401015022880a82e8404e1740803093048053185f013812820121096400b8605c03c2e6a0350490a106f281a82086983f93060172094603e1500b805c40b189807f04808d2c128240814c0b364011090280b904a37a00910307ca82c0c633e505f86005083794190170056e439a82e8d0dba4c134060088 else 0xf029890b2da80b876d40a6174374c818100e841fc1c05028134cc1811d799360c0c0420742e8617204a20b93af038181700f0298d01ae0d0101940e0154cf0600a0aa30880ba100282a0881c2d821433080a8164204d0c6039182e81c8b4600c40086108070200503010010268180c2c80a8400a0b4205a00c102ce9300ef0491c9816b824074836604fc1203a0fe5002e0900001d201000f839dcc83494058028740054100a10802e200001416930168018dc98004094617a0d601430580a100c1ba640a08094008503a0d6202e0db09d7b93058101ac0b51182c0806e0d62726003100184150200404a0323025011091180006301c0c0642030010200c156100c0028bcd40d0284603409014230020ba100c850880682054006210606603218ab0409c2c04e9813af08018010b43f8260941ac906a06009a3b184350300a1200022a08002094403302814230bae1806b18182dbbb085e6b5140497382c75a96dcb36f7072adad4403043f9560a1210203c0112db9013c014400270031027806081342c84004032200001d00c182a8180508c0c05580ac2840f8a02202e122301d04d00c1826806080a8da8078764c0b5c1203c4b47a2ce0901ea3128830148340c0341a)))
def rootSH10 (i : Nat) : Nat := 0x900018000000a4e43205624f00f03371b215070b38a5e938490a5343b42a75c29620466a21fa50662a9402a404825b4245a72208b05570d401b8106a91705998589966171606075407a993708524a4a41c00198d29400003d97d85e04200041393440678842196e03fa4c06c04000384b74ea2504463b42c92c75106f06604e05b04795db4400000106548386000006902e03763778600107e62800000148b978b4a07400000120b027137030a1178d42745e98f048072698b3a001976900080038000004448140280260183f700a62806103c0a1880408a805582018ae0
def rootSD9 (i : Nat) : Nat := 0x202812166da805c0b52615803a281601cc0d23061f5a8402000fee646c1c605b664602e00f014c60300f49bc1229d7840f004010210206b080b8342c0c81e5062f0487c30106181d4403a0c8102a040d01a8094771ae0c34350d0ac3d6a0d0fc3b610080905801d0398c174101680780a6300f00b84036080ac174053215828408a600b840c4102ac0941163002e816a05a18e60591f6224257f20b01602c7b4eb9c13566880b01602c64a0b1683133acb897a2e25a00b0162be5580b01628d4f69a52523844c850f402c0580b0161d63880b0d91a031c5bc1602c05850c9882c0584141602c0583986a02c1021bc2e82c0580b01602c0580c416000ffc152605314c120d7f0b9605514c120ff61835495148110ff4953549814c120bee9c6a25524c120ff48c954d524c120bed9c62e5534c120ded9536da894c120ff498354d524811097bebc6a64960530a6fdc62a5a954d20c6fda56da8964d2087fccb695984c52095fdc796e2a64d1087fcca6e15264d1087feca8ad8564d1087fdca8ad858e51087fecb2a5a954d20c7be4a6d68964d20b7b64c64d8186520e7ae4a6095264d10c7bdb89295264d10e7ae4a54a2a64d10b7b61c6ca4960530e7ae4954a2a64530d7b64b605a386520c6fe5a6da8964d2087fdcb96a894c520dfd25b605314c120deea6b549814c120deda6b54d814c120e6f66c605a386520c6fe6a6d63960520cebe6a92d9360520deba6b929814c120e6be6a6a64960530e6bdc99aa4960530e6be6a6ca4960530e6bdcb9aa4960530c5fe7b6a15264d10a5fe7c549a886530a5fe7c549a88e510c5fe7aa6da354910a5fe9c6ce7a54910e5be7b9295264d10d5be7b9295264d10cdbe7b9295264d10fdaa7b929524c120d5be7b9255260530d5be7b9255264530b3f68c54d8186520c7be8b9299564d20c7be8b9295264d10c5fe7ba295264d10ff4953a25524c120f7aa4aa25524c120d7da5ba25314c120d5fa7ba25954c120f3d198605314c12087bebc6a2496453086fecb9a9a96052085fecb9e9a95491087f5caa6d818652087bdcba6a4960530c6be4a6da8964d20ff0a4a54d524c12085fdcb9eaa95491086fdcb9aaa960520c6be6b92da864d10a6be6c6a24a64d10a6be6c6a24964530c6be6b9299864d10a6be6c6ea4960530c5be7b9299564d20fd627c5495148110c5be7b9295264d10f74953a25524c120
def rootSH9 (i : Nat) : Nat := 0x1934800019a01960194b04
def rootSD8 (i : Nat) : Nat := 0x6058160b032160642b083ead800502fc93ac64aa6a9260906f9254dc6a25524c120ef2535aa6a93029824145be7d6e24a54993443fa14f7252a6a926090712f9aa7b9255260530
def rootSLevel : Nat → Packing
  | 14 => (1,0,8,0,0,0,0,rootSD14)
  | 13 => (3,1,8,0,0,8,0,rootSD13)
  | 12 => (30,2,8,0,0,12,0,rootSD12)
  | 11 => (220,3,8,0,0,15,0,rootSD11)
  | 10 => (424,4,8,0,0,14,0,rootSD10)
  | 9 => (77,5,8,0,0,11,0,rootSD9)
  | 8 => (6,6,8,0,0,6,0,rootSD8)
  | _ => emptyPacking
def rootSIndex : Nat → Nat → Option (Nat × Nat)
  | 14 => rootLookup 11 19 3 7 2 4 rootSH14
  | 13 => rootLookup 37 67 6 10 5 4 rootSH13
  | 12 => rootLookup 181 431 7 13 8 4 rootSH12
  | 11 => rootLookup 331 719 8 14 9 4 rootSH11
  | 10 => rootLookup 53 127 5 12 7 4 rootSH10
  | 9 => rootLookup 5 11 1 8 3 4 rootSH9
  | _ => fun _ => none
def rootS : Forest := ⟨511,14,fun j => rootSSamples[j]?.getD (0,0),rootSCols,rootSAutos,rootSLevel,rootSIndex⟩

def rootGroups (g : Forest) (k : Nat) : Nat → List (Nat × Nat) → Prop
  | _, [] => True
  | first, (ar,n)::xs =>
    (header g k first n ar = true ∧ rowCut g k first n ar 0 ar = true) ∧
      rootGroups g k (first+n) xs

theorem rootGroupsBlock (g : Forest) (k first : Nat) (xs : List (Nat × Nat))
    (checked : rootGroups g k first xs) : block g k first (xs.map Prod.snd).sum = true := by
  induction xs generalizing first with
  | nil => rfl
  | cons x xs ih =>
    obtain ⟨ar,n⟩ := x
    obtain ⟨⟨hd,hr⟩,rest⟩ := checked
    exact block_merge (cutsBlock hd hr) (ih (first+n) rest)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma rootSb8_0 : block rootS 8 0 6 = true := by
  apply rootGroupsBlock rootS 8 0 [(9,6)]
  simp only [rootGroups]
  repeat' apply And.intro
  all_goals first | exact True.intro | decide +kernel
lemma rootSlevel8 : block rootS 8 0 6=true := rootSb8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma rootSb9_0 : block rootS 9 0 77 = true := by
  apply rootGroupsBlock rootS 9 0 [(9,16),(9,3),(10,16),(10,16),(10,16),(10,10)]
  simp only [rootGroups]
  repeat' apply And.intro
  all_goals first | exact True.intro | decide +kernel
lemma rootSlevel9 : block rootS 9 0 77=true := rootSb9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma rootSb10_0 : block rootS 10 0 83 = true := by
  apply rootGroupsBlock rootS 10 0 [(9,3),(10,16),(10,16),(10,16),(10,16),(10,16)]
  simp only [rootGroups]
  repeat' apply And.intro
  all_goals first | exact True.intro | decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma rootSb10_83 : block rootS 10 83 96 = true := by
  apply rootGroupsBlock rootS 10 83 [(10,16),(10,16),(10,16),(10,16),(10,16),(10,16)]
  simp only [rootGroups]
  repeat' apply And.intro
  all_goals first | exact True.intro | decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma rootSb10_179 : block rootS 10 179 95 = true := by
  apply rootGroupsBlock rootS 10 179 [(10,16),(10,16),(10,16),(10,15),(11,16),(11,16)]
  simp only [rootGroups]
  repeat' apply And.intro
  all_goals first | exact True.intro | decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma rootSb10_274 : block rootS 10 274 96 = true := by
  apply rootGroupsBlock rootS 10 274 [(11,16),(11,16),(11,16),(11,16),(11,16),(11,16)]
  simp only [rootGroups]
  repeat' apply And.intro
  all_goals first | exact True.intro | decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma rootSb10_370 : block rootS 10 370 54 = true := by
  apply rootGroupsBlock rootS 10 370 [(11,16),(11,16),(11,16),(11,6)]
  simp only [rootGroups]
  repeat' apply And.intro
  all_goals first | exact True.intro | decide +kernel
lemma rootSlevel10 : block rootS 10 0 424=true := (@block_merge rootS 10 0 179 245 (@block_merge rootS 10 0 83 96 rootSb10_0 rootSb10_83) (@block_merge rootS 10 179 95 150 rootSb10_179 (@block_merge rootS 10 274 96 54 rootSb10_274 rootSb10_370)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma rootSb11_0 : block rootS 11 0 80 = true := by
  apply rootGroupsBlock rootS 11 0 [(9,2),(10,16),(10,16),(10,16),(10,14),(11,16)]
  simp only [rootGroups]
  repeat' apply And.intro
  all_goals first | exact True.intro | decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma rootSb11_80 : block rootS 11 80 96 = true := by
  apply rootGroupsBlock rootS 11 80 [(11,16),(11,16),(11,16),(11,16),(11,16),(11,16)]
  simp only [rootGroups]
  repeat' apply And.intro
  all_goals first | exact True.intro | decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma rootSb11_176 : block rootS 11 176 44 = true := by
  apply rootGroupsBlock rootS 11 176 [(11,11),(12,16),(12,16),(12,1)]
  simp only [rootGroups]
  repeat' apply And.intro
  all_goals first | exact True.intro | decide +kernel
lemma rootSlevel11 : block rootS 11 0 220=true := (@block_merge rootS 11 0 80 140 rootSb11_0 (@block_merge rootS 11 80 96 44 rootSb11_80 rootSb11_176))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma rootSb12_0 : block rootS 12 0 30 = true := by
  apply rootGroupsBlock rootS 12 0 [(9,1),(10,12),(11,16),(11,1)]
  simp only [rootGroups]
  repeat' apply And.intro
  all_goals first | exact True.intro | decide +kernel
lemma rootSlevel12 : block rootS 12 0 30=true := rootSb12_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma rootSb13_0 : block rootS 13 0 3 = true := by
  apply rootGroupsBlock rootS 13 0 [(10,3)]
  simp only [rootGroups]
  repeat' apply And.intro
  all_goals first | exact True.intro | decide +kernel
lemma rootSlevel13 : block rootS 13 0 3=true := rootSb13_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma rootSb14_0 : block rootS 14 0 1 = true := by
  apply rootGroupsBlock rootS 14 0 [(9,1)]
  simp only [rootGroups]
  repeat' apply And.intro
  all_goals first | exact True.intro | decide +kernel
lemma rootSlevel14 : block rootS 14 0 1=true := rootSb14_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem rootSGeom : graphValid rootS (boundsBefore known383)=true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=6) ?_⟩,by decide +kernel⟩
  simp only [listPieces]
  repeat' apply And.intro
  all_goals decide +kernel
theorem rootSTables : checkedTables rootS 14 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact rootSlevel8
  · exact rootSlevel9
  · exact rootSlevel10
  · exact rootSlevel11
  · exact rootSlevel12
  · exact rootSlevel13
  · exact rootSlevel14
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem rootSImpossible : Impossible true graph 14 inputs.toFinset := by
  have result := index_root (g:=rootS) (m:=511) (cap:=14) (i:=0) (ws:=inputs) rfl rfl (before_sound known383 valid383) rootSGeom rootSTables (by decide +kernel)
  exact (show graphGoal 511=graph by decide +kernel) ▸ result

def orbitWire (i : Fin 9) : Sig := inputs.getD i.val zero

theorem orbitWireMem (a : Sig) : a ∈ inputs ↔ ∃ i : Fin 9, orbitWire i = a := by
  rw [← input_list, List.mem_ofFn]
  rfl

def orbitEssentialRows (i : Fin 9) : Row × Row :=
  ([(3,2),(3,1),(6,2),(12,4),(24,8),(33,1),(66,2),(132,4),(264,8)] :
    List (Row × Row)).getD i.val (0,0)

theorem orbitEssentialChecked : ∀ i : Fin 9,
    witnessB graph inputs (orbitWire i) (orbitEssentialRows i) = true := by decide +kernel

theorem orbitAllInputs {u k s} (run : Live u graph k s) (raw : ∀ a ∈ s, a ∈ inputs) :
    s = inputs.toFinset := by
  ext a
  constructor
  · exact fun ha => List.mem_toFinset.mpr (raw a ha)
  · intro ha
    obtain ⟨i,rfl⟩ := (orbitWireMem a).mp (List.mem_toFinset.mp ha)
    obtain ⟨p,n,diff,isolated⟩ := witnessB_sound (orbitEssentialChecked i)
    exact raw_required run inputs (orbitWire i) raw p n diff isolated

abbrev TransportEntry := Nat × Nat × Nat × List Nat
def moveEntries (rows : List TransportEntry) (base : List (Nat × Nat)) :=
  rows.map (fun e => (e.1,e.2.1)) ++ base
def transportValid (base : List (Nat × Nat)) (e : TransportEntry) :=
  (boundsBefore base e.2.2.1 == e.2.1) && carryOK e.1 e.2.2.1 e.2.2.2
theorem movedKnown {u base rows} (h : Known u base)
    (cert : rows.all (transportValid base) = true) : Known u (moveEntries rows base) := by
  intro e he
  rcases List.mem_append.mp he with hm | hb
  · obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hm
    have hh := List.all_eq_true.mp cert r hr
    simp only [transportValid,Bool.and_eq_true,beq_iff_eq] at hh
    exact carry_of hh.2 (hh.1 ▸ before_sound base h r.2.2.1)
  · exact h e hb

def clipEntries : List TransportEntry := [(179,5,55,[81,114,50,65,99]),(188,5,61,[112,16,66,97]),(254,8,251,[32,113,67,81,101]),(422,5,61,[80,16,33,50,116,131,99]),(433,5,55,[80,16,66,49,114,131,98,99]),(440,5,61,[80,16,66,130,113,97,98]),(444,8,63,[48,33,113,80,132,64,96]),(446,9,127,[32,49,128,81,116,100,96]),(454,5,61,[96,16,114,50,65,133,67]),(499,9,127,[81,130,99,65,115,50]),(510,12,255,[128,49,100])]
def clipKnown := moveEntries clipEntries known383
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem clipValid : Known true clipKnown := movedKnown valid383 (by decide +kernel)
def ecY : Array (Bits × Bits) := #[(0xffffffffffffffffffffffffffffffffffffffffffffffff800080201e00000000000080000000180f800000000003fff0000000000000001d0000fc03807e00e0001800000000807f8001ffffff808000000ffff0000003fff0000003ffffff,0x880201f820111000000c1008022080fe111202200013e50800000000010001d00807402806e00a0000c00100100807580013fc609000000000ee63081008afc5800004296b012),(0xffffffffffffffffffffffffffffffffffffffffffffffff858080002000000060803f00000000a3f000000000fffffff008fc60fe00000801c000fc8c7f801f007fffffffffe100007fffe000007f000003fc000f000003ffffffffffffffff,0x59000002104000262803d4200148483d042200444a856c1a008bc70f742a158000000888467801b0073d79c06b268000010aad000226f520a5510000680011103ad50298b610564),(0x31003c00000000007c000000000240000000000fffc000007000100000000e2ffff00700000001f8060000000017f807ffe00000000000003f0000ffffffc000ffffffc000000,0x11003c12802440407c05405210824004400410857a8000005000000000000e2d83f00500000801d8024002004016d806f5410104400000082e00089f65620000a8d5212000200),(0x41fc203c0000000000f80000000000c7ffffffffff0000000618007e0000000f030000037f8001e01fff800000007e7fff80000000007ffffffc00000ffffffffff0000000000000,0x40bc243c0500241800e8084028063001e3c07d8670001014c608107e2c08c580010500112f920820021f040a431832123f008892a488150053180404268989c06ac80220e2022438),(0x41c0000000007f000000000000f80000000000000000081007800000000ffc000003800001ffe000000000007f800000000000007ffffffffffff00000000000000000000000,0x100049c2013088007f049058103800f00048020800612080091027804193000fe0101202c04401df4400051084204d240049101000006afface3f119c0d21200000b044302400040),(0x6007e00000000007fffffffffffff0000000000000000000fe007fffffffff000000003fffffe000000000000007fffffffffffffff800000000000000000000000000000000000,0x7e08810030602ff1de401e3fc0008040040f8005c001022000260e0007e000402403fd1f1002080a040307c07f3f0a0de0d038f01c00cf004011049c1c000308087c02004780),(0x78007fffffffffff800000000000000000000000000000000ffff8000000000000000003ffffffffffffffffffff8000000000000000000000000000000000000000000000000000,0x58207efcc700ff80084100405fc00000014047f0000600060ff34105081c0602480638237b983de46f0c2c23f80010382c0e00133f001084f000805e009fe0004c080f8002047800),(0x7fff800000000000000000000000000000000000000000000ffffffffffffffffffffffc000000000000000000000000000000000000000000000000000000000000000000000000,0x7ffe809011c0c00000000060600000010a707800008003180ddaffd9f1fff80f1d27c0fc020021080050063c000000003000001bc00020670000026000800002700c100003878000),(0x7ffffffffffffffffffffffffffffffffffffffffffffffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x2743810339ff0000500620ff800000fe0c7f800000f803e00004820081e0000492b800c000604010906057c0000000c04070011c0000407800030b8008e00003800fe00003f80000)]
def ecC : List ColumnInfo := [(1,0,510,0,12),(4,0,507,0,12),(17,0,494,0,11),(132,0,379,0,11),(1,16,486,8,9),(3,0,508,0,9),(4,128,347,32,9),(12,0,499,0,9),(33,0,478,0,9),(65,0,446,0,9),(257,0,254,0,8),(9,16,486,0,8),(36,128,347,0,8),(67,0,444,0,8),(1,2,440,68,7),(1,32,94,384,7),(1,64,188,258,7),(4,8,227,272,7),(14,0,497,0,7),(35,0,476,0,7),(268,0,243,0,7),(289,0,222,0,7),(321,0,190,0,7),(3,64,188,256,6),(12,64,177,258,6),(65,2,440,4,6),(65,32,30,384,6),(68,8,163,272,6),(257,32,94,128,6),(257,64,188,2,6),(260,8,227,16,6),(259,0,188,0,5),(14,64,177,256,5),(35,64,156,256,5),(41,16,454,0,5),(73,16,422,0,5),(78,0,433,0,5),(259,64,188,0,5),(268,64,177,2,5),(289,64,156,2,5),(321,32,30,128,5),(323,0,188,0,5),(324,8,163,16,5),(332,0,179,0,5),(270,0,177,0,4),(291,0,156,0,4),(102,128,281,0,4),(270,64,177,0,4),(291,64,156,0,4),(297,16,198,0,4),(355,0,156,0,4)]
def ecA : List (List Nat) := [[],[32,83,116]]
def ecD9 (j : Nat) : Nat := (if j<1 then 0x802f07c0102de081a3f07c01033e082e3f07c0178282881b058541f822a834306f0535062af820d0c1ac14d41c2615082ac1416f0c1a2c24140828c174206c1628370982d090345068891507e0f80244828105142f840d82c50a185f081606ca0da260b2240d17c1f0056095d75cd5c35b95af5a559b57d57356955f5415375054fb4f14d34c94ab48d46f43d41f4013e33d93a739d37f3753573252df2992672351ef1a91631090c307d04b018fe6fb4f82f50f1eeecebae88e2edd4da2d70d3ed0ccdaca8c76c44c12be0baeb68b22adcaaaa64a32a009ce99c96a9248f28c088e85c82a7f87c678074e71c6ea6b868665460e5dc5965645324ec4a646041a3d43a23343022942261e01ae17c10e0a00320019bfe999560731b7ef70a9b0330faf78654d8198677edd70ca9cc37b76cf8654e61bdeb63c32a730f2fd98e1953986d7e5c34ca9cc38ffea19854e61adfb6b51f2cc0e6ff9669693606deed9d0b41b03cbf25a85a0d81cdff2cd2d06c0eaffa8e595360737fd472ca9b039bf6a39654d8197fd75c32a6c0f6df96a0d53607daf42d06a9b03db7e598354d8197fd74542a6c0dafdb62a153606dfcd8150a9b03abfea09654d81b7ef70a9b02b0d6ffb6661535869ffdc32dc8aa73bfed9a1e0d53c7ff30d0f06a9ceffb66869854f1ffcc3434c2a70ffee1a954f618dff74cb6a398c6fdb9e9981cc637edb742cad071bf6dba954e819deb63d330730cef4ba58d8198677ad8d50b1cc339f6d4a858e619deb62542c730cafcb86995398637fdb3434c4a71bfed9a1e5583adeb6251f2cc0e6f7966866360727ed3f2d29b031bfed9a994d81c9fb4e4b4a6c0c6febae599360637f5d12cc9b031bf6dba954d8195fb6c542a6c0cbf9b02a15360717fd412ca9b031f7ee99324d818dff75cb106c0e4fda7e588360733fcb54a41b0399fe59a520d81cd7f2cd2106c0e6ef966888360737dcb34041b031bfed9a914d81cde92cd08a6c0daf5b12618658ede6d9130c1ac79bded9a12616387ff74cc130b1c77fba6549558f0ffcc34e42ac78bfe61a621563c7bf30d190ab1e3fb986808558e37fdb3434c2a74bf6db98a1953b79b644c306a9c3ffb86a56354e1ffdd3304c2a71bfee996259538fef74c8922a9e3df9868c8654f1fbcc342432a74bf6e396e1931cdef2cd0f0c98c6ffb66a7854c637fdb3434c2631bf6dba1655318dff6cd4b0a98e6f4a9e99814c797bcb70cc0a631bfed9a960531f5ab0cb1b0298c3ffb86a5654c737bd4f4cc09038bf661a3e1861adf36bc332030d6f9b3e1990186b7ddb30ac80c35beed98364061adf766b2b2030f6798559590186b7ddaac6c80c3db660d6364061adf36ca9b2030e2fd98e998318736fd3326c18c38bf663a558c61e5bb66cc2c630f2dd9860d6318717ecc34ca98c31bfed9a1a6053 else 0x4861220000000010080000a020a2505100144840140648083410681c103814143848400849220492104921f07c0102fe0e0a305fc1c147e078228481d101de0b0a383612074607782c28d93e17c3128807782c28f85f044a1f83e00bc0f045e0f802f07c01783e00bc1f005e0d122f041917800c0bc1f0040b82a0a02c407c16050152783448bc1f005e0a142f07c01783e00bc18285e048e291fc21415e18bc1f005e0b1220641484060e8280b0d89f07c01f83e0081bf00181f83240bc0f045e07822f06481783e00810f05491f840a0bc1f005e0f802f041c1783e00bc19345e0c9a2067c10407e081c2f03c11783e00bc1f005e0f)
def ecD10 (j : Nat) : Nat := (if j<4 then (if j<2 then (if j<1 then 0xe7ffa6661539ffe859854f3ff9866153cffea19654ebffa8659539ffea19654f7dfa3659539ffe8d9654e7ffa165953dbfe599654f3fca865953aff2a19654e7fea9619539ff6a58654f6fd9661953ef7e618354f3ff9860d53df7e598354ff5e8560d539ff6a58354f7dd9660d53fd76158354fbdc9860d53bdfe956354f6ff9658d539ff6a56354e7fea926153bbfa989854eff6a126153bbf6989854eff5a1261539ff6849854eff9a026153cff6609854e7fea925953dbf6589654f7f59124553cffe608654e7fea921953bfda848654e7fda921953bf768c8654eff5a121953bfe6808654e7fda6e61319ff697984c67fda8e59319ff697964c67fda8e55319ff69b954c76ff96e19319ff6a7864c6ff5a1e19319ff6a7854c6ff5a1e1531bfd687834c6fdda3e0531bfd687534c6efda6d4531bf768f514c67fda1a6131bbf69a954c6feda2a55319ff6a6854c6ff5a8a0531dfd656814c67fda999531bfd686654c77dd9898d31dbfe99984c6effa6661319ffe99984c67ffa566131df7e8d984c67ffa366131dbf299984c67ffa8659319ffe95964c77f7a1659319ffea1954c67ffa665531dfde85954c67ffa1655319ff6a5864c67fda961531fbde99814c6effa660531ff5e8d814c6fdfa360531dfde59814c77f79560531efde19814c7fd663605319ff6a5814c77f59660531dfd655814c7bf58660531ff558d814c77f4a960531fbd299814c7fd4a3605319ffea5654c76ff96595319ff6a5654c7fd7a158d31bfde85634c77df9858d31df7661634c7edd8658d31bfde85534c67fda9545319ff6a4854c6dfda721531bbf698854c6fdda321531bfb688854c6ff5a121531bfe680854c77dda564c86dbf6959620f6fda165883ddf6999520f77da165483dfd6999120f7f5a564483dfdea581207ef7a6604819ffea5532067fda954c81df764d532067fda9a1463ddf6568518e7ffa8654639ff6a58518f77d9561463bbf68f861873fda366061df76a1931877dda564c61dfe615901877f98364061dfe54d90186effa660c61ddfa55831867fda960c61cff661831875fd9760c61ddf655831877dd9360c61dbfea563186effa558c61dbf66163187edd8358c619ffea5531873fe9854c619ff6a553186efda654c61cff661531877dd9354c619ff6869814e7fda9a1853dbf65a8614e7ffa8658539ffe859614e7fda961853dbf6598614e7fda961431ddf655850c66ffa664783bbd687869872fd98e1a61ebde198198677da5261639fb6889858e7f5a1261639fe6809858e6ffa6661619bf69b9154e3ffa8659538ff2a19654e6fda6261539fd6849854e7f9a0261539bfe99984c76dd8664c869bfea58621a7dfa960c83db76598320f75d9560c839fdea5812072fd98e1861dbee19901876f96564061dbe58d901872fd9858c61 else 0x39ff6979160efdda3a1983bf768e8560eeffa664583bbf2999160f6ffa3e5981fbde87966076ffa1e5981dbfa8f966076fda3e59819ff68f966076fda1e5981dbf28f966076ff96e4d819ff69b936067fda5e4d81dbf25b93607aff96e1981dbfe5b83607ef796e0581dbfe5b816076ff96a4d81df7e4e93606efda6a4d81dbf25a936076ff96a0d81df7e4e83606ff5a1a0d81dbf25a836076ff9698d819ffaa6636067fda998d81bfd686636076ff9694d819ffaa6536067fda994d81b7f69e53606ff5a194d81dbf25a53606effa664d81dbfe59936076fc9664d81ebfe59866076ff9661981ebfe19866076ff9660d81df7e4d836076fc9660d819ffea5636076ff9658d819ffaa563607afd8658d819ff2a5636067ffa954d81affea1536076ff9654d819ffaa5536067fca954d81aff2a1536076fc9654d81bbfaa4966076ff9624d81df764c936076fc9624d81dbfe58836067fea920d81bdfa9483606dfda720d81bbf69883606f7da520d81bef69083606feda220d81bfe680836076ff9614d819ffaa4536067fda914d81bfd684536076fc9614d819ff6979858e7fda1e6163dbfa1b9558e7fda8e55639ff6879558f6fd86e55639ff6a39158e7fda5e4563cffe638658efdda3e19639ffaa78558e7fda9e1563bbf69b8558efdda3e1563cffe638358eefda6e0d63cffe629858e7fda1a6163ddfe569558eefda8a1963cffe628558e7fea9a15639ff6a68558f7df95a0d63fb7a1a8358efdda8a0d63bf76868358fedd86a0d63ddfe566558efdda3995639ffe959858e7ffa166163cffe619858ebffa865563aff2a19558faff9861963cffe618658fafc98619639ffaa58558efdfa160d63ef7e618358f3ff9860d63df7e558358fede8660d639ff6a58358fedd8660d63ef72618358efdfa3595639ffaa49858ef7ea526163b7f69c9858ef7da526163bfb6889858eff5a1261639ff6849858eff9a026163cff6609858f77d9525563cffe608558e7fea9215639ff6a48558edfda721563bbf6988558efdda321563bfb6888558eff5a121563bfe6808558e7fda9e0d61bfd687835867fda9a0d619ff6a653586dfda794d61dbfe99985867ffa366161fbde99815867ffa954d61bdfa94835867fda920d61b7f69c83586efda620d61bdf69483586fbda420d61bfb68883586ff5a120d61bfe680835867fda914d619ff69b9854e7fda1e61539ff6a39654e7fda1e5953dbfa9b9154eefea6e45539ff6a39154f6fda6e4553bbf69b9154e7fda6e45539ffaa78654e7fda9e1953bf768f8654f3ff98e0d53bdf6978354f6ff96d8d53bdf6976354f3ff98a61539ff6869854f6ff96a5953dfde469154ebfea8a4553aff6a29154f3ff98a19539ffaa68654e7fda9a1953dbf65a8654f7df96a0d53fd7a168354efdda8a0d53df765a8354) else (if j<3 then 0x6ffda594d81effea153606fffa854d81fbfe59536077ff9654d81effe1953607fde8354d81bff6a153607bfd8654d81ff760d53607bfca854d81fbf25953606ffda5a0d61bff69653587ff55360561bffea153587fde8354d61bff6a1535877fd9854d61ff760d53586ffda6e4553dff65b9154f7fd86e4553dff58f9154effda1e1953bff6878354effda1a6153bffe859654efffa158d53bff6849854effda5e1931bff697834c6ffda5e0531bff6a3514c6ffda5a6131dffe62854c6ffda8a1531dff662854c7ff585a0531dffe61854c77fd9861531ffda15814c7ff58560531dff655831867ffa364786dbfe9991e0eeffa6647839ffe9991e0e7ffa564783dbf29991e0e7ffa958f819ff6a563e076fd9658f81df764d63e07afd8658f819ffea553e06bffa854f819ff6a553e077dd9354f819ff6a685d8f77d95a17639ffea195d8f6fd86657639ff6a585d8f77d9561763cff66183d8e7fda9a0f61df764e83d867fda994f61b7f69e53d867ffa864f619ffe9593d867fda960f61df764d83d867ffa954f619ff6a553d867fda914f61bfd68453d86fdda3d4731dbf65b51cc76fe96a17319ff6a685cc76fd96a1731ddf65685cc67fda999731dbf65a65cc76ffa865b319ffea196cc76ffa565b319ffe9596cc76ffa165b31dbfa9596cc76fda865b31dbf69596cc76fda165b31dbf29596cc67ffa8657319ffe9995cc67fda961b31dbf65986cc76fe96617319ff6a585cc76fd9661731ddf65585cc6effa660731bf7e8d81cc73fe9860731cff66181cc76fd96607319ffea565cc67fda959731dbf65965cc77dd9858f31fb761963cc67ffa564e86bf768e86a0f6fd96a1a83bf768e85a0e7ffa565a839ffe8596a0e7ffa6656839ffe8595a0f6fd9661a83df764d83a067ffa954e819ff6a553a067fda1a62639ff6a68598f77d95a1663bf768e6598e7ffa8656639ffe859598f3fd9861a639ff6a58598f77d9561663df76558398f6fda9e1a61bbf68f86987ef5a1e1a61dbf663869867fda9e0e61bfd687839876ffa6662619ffe8d98986effa660e619ff6a583987ef7a660661fbde19819877f59360661fbd58d81986effa558e61fbde8563986efea858e61dbf66163987edd8358e61bbf2a1639867ffa954e619ff6a553986efda654e61bf768f6594f6fd96d96539ff6869894e7fda9a1a53d7f65e8694f6fd96a1a539ffea19694e7ffa165a539ff6a58694f5fd9761a53dbf6598694f3fd9861653df76598394efdfa359653dbf6596594e7fda9e1631bfd687858c6ff5a1e0e31cff663838c67ffa566231defe15948c77bd85652319ff6a5858c73fd9860e31fbde99818c77f59560631bfde85538c777d9554e319ff6979361a7fda1e4d869ff68f9161a7fda5e59839ff6879660e7fda6e55839ff6879560e7fda6e458 else 0xeea3dd0cb9d972c6e445c5fb86d7012de4dba0b6ef6cf2d89dad8b55f69aed25da2bb3f36742cd3d97eb2996446c6b58b6b11b61b6c22581bafc15edebcbd765ae9d5c4eb70d6c1ad3159beb15d614aba1567aab1d54caa35540ea68d4baa935517ea1b5416a7c94f129cdd357a6154b62957d286a485488a8ead1aca307454689450f6a16541ba81e50019f8d3e0a7a84f1e9db53a7e736ce3b9c4937ca6d2cd6a9a5f343e6614c75983f2f6e5c74b5c96552c2a5754ab89531299a5114a0b93d7270a4c84967928f240e46d48ba90ed215a41247e98f931e823b2c7218dcd1b1a345c6598c4f178e2e1c57f8a651396250c478888d107620343b987210d9e19f42fa85910aa212dc22083a706860aec12b81cf026a026c0247fe4feddfcbbf6e7eaefc4df67be947cb2f89def63db17adaf4c9e7bbcb378ccf089df83bbe76d0ecb5d7dbaae751ce9b9d1539f8738ce651ca8390371b4e2a1c3b38327000df15bce376a6e82dc19b65b6a26cf2d91db0f35fe6baad6b1aafb52469f6d2dda39b44a6830d0059da339466e8cce5983b2d56522c9a191b320d63a4c6a58c4b157625cc41586530aa6102c18581c2ff45f4ebdf97a62f235df4bafd74b2e5b5c76b8016ebadc05b1cb5b96a72d2559d4b2bd63eac545820afc15e82bb05720ad9d5962adf5536a9ed52daa3b53dca7154c9a973525ea3d146a28a250cea11d40aa7e34f3e9d913a227124dc09add34ba6654c7898712f9a5d34b5496292ac253849fa9309243a45e486a90551f623ba47348d5918922e945928aa5144a257441487610d3217d4284846506f209a40d080d90069fed3f647e48fbd9f643e767c6cf791ec03d1c7970f151df83b8c762ce9a9d1539b47258e369c5638126f38dc09b58365e6c3cd731ac6354c69acd259a2b33e0671ccd3997532aa64d4c8a98f5317461b4c2698002fd25e94bb517412dd65b08b4c96792c6a57c4aed15ba2b1055a0aa4151f29fe537ca4d9469286e5080a0013c5274a4e389ae132a25de4b3c953128624cc491890a11e2233c456888f90ed215241dc81990011f9e3e2c7b10f1e1db43aa07368e4d1c4837c86e00d851ab834846778cab1904316460a8be317742e445af8b3f161a2b245500a77147827e04ec09c1131e252c49108f0117c225443188310fda1ec83bb872a0e141b1834a06590c2a17442c2054009e61304247845d08560fe41df037a065a0bec164829704a608840f781bd0316056409380e3013e01b40190000dff65581cc7bfe86a1683dffa1591a0f7fd9560e81bffea153a06ffda854e81ff760d53a077fd9560e61ffd54d81986fffa854e61fbfe1953986ffda854e61fbf699539877fd9854e61ff760d539877fd8564653dff655838c6ffda1a5583bff6969160effda1a1583bff69693607bfe85a0d81bff696836)) else (if j<6 then (if j<5 then 0x83811c2e18710120c8446100782411c343f08228070b041107887850de1874e1103f0b870d0e181c0de085c8100401c220f0763787c24a3782100c90221ce083888de18c461107c3411c2e1874e110803813c2e1870e0e16082e0e890d0f05e1704325868382430c8483a3160542428207028191f082419183c11c3e1434240e3870140de0838a130902b82192864402e10783230af0f841609038c16070b06140c8811c3e14343c5088201bc30e94220ae1437861c306422171c1f841e0693841e868f841e868f841e0b8c1f07e10383c543f0a1bc30e142009e1f082813089c3a14c491b84130f1c2c17e1f082614370f84140986ca1d0a62587c209878e48e1f08281928742889e1b08261e3f0f841486844b07e10578617287191c3e105824103f0b8615101030c9e170c2a12079c9ac80e70f8412071c2bc3e10483250ff0f84150a034d158a07c7c3e10511a4e1f091a14079787c24684c285078210fc2e1a34dc2468509040403e0fc2e1c34dc3e1234280f282891c2e1a350e0f386f8054491013c20d8bc81a6470e1212e1044f09e1f08261e2827861a181285090d8bc809e1d0824282868a9851f0d13c209054a0f0470d1212e1044e05e106c5e4e10482c8c204c1fc3097083660d52113c3097082274286c463890a0416e1f08243028a0280bc2f082c1b3868121b111113c3e104c28544f0f84120e142d1389094809e1f0824282a2787c209878a1004c2387c209038e100421f85c326981145e1f08284930241c050842387c283a20e0e0b8c1c054470f8414081f87c2440502e509a1f848de183cc0a247090e8de183ce108ad143314e1f08e160b838aa5442f0f8480e864aa54e170c1a70b1541a540c87f87c240538415e1858b8de130c2815285429c2e1858a8de1b082a14289f8426e1834a27a28644dc3e118220fc461c4bc3e11c220fa6e230fc2e1859015e1f082c1428582bc3e1050a16e1b082a14289c22198a08787c2385787c206850a1506f0f841428582bc3e1050a160af0f841428582bc3e1050a15e1f081a1428a1269242f0b861638a22712a14178616385a842fe184ca1604d0b863009182dc318708245e249c41387270bbe137c1ef82df044e049bfef7f6efd6df6dbe7f7c8ef71de91bcc778d6efaddb5bb0f751ee71dca3b8c7708edfadba3b6c76c8ed68daa3b4c768d6d03d9d9b30f6566ca7d921b1c36316c4bd845b02f5f5ebd4d733adc35a86b30d621abc356ceac2d557aa5353eea66d48da8e3510ea01d3c3a7074cc6954d257a3c3451e856d0379f5f3c9e761ce719c6336a66abccbd98d730665e3cb5196232ab6524c9f792df247646ec8af904f1ec6394c6c58ce717f62dec57d8a7b136623ac3db86a70c06157c23983f305c6098c0cd811b00a5febbf4f7dd6fa1def6bd9b7a26f275e1cbb9f762 else 0x70c31c208941245e10702307081c2348e170c3a50782385c346838c210d8743040e7081a1408143c1de1d2080ee114c91c30e181c53e1f08301c306225070e13868d8389c81c090478414287b84120c903816100c350d0c07480886f0c3a40701422100470b861c403c11c2e1a341c608d238610203e91c3e10743617383e91c3e105c22163852121810902348e1c342050b85041c0701c0a1ee170c348e10511a30e844463085238707e1044d07e10a3822728718a14e106ca0f040511bc2e1840e1ce10504a40b02f84110e941e1d8686080f0770c43c20a1b87c20a08481d0f08c6210ef0c3c232875861e119033c10e88c80f0470b860e46983a1e118d91c3080508480e8606110ef0e9040770c2853e11203c70883891c329f082810411b8414109091c3e10502e5e1f082821230f8414109091c30c94f8414370d841410901e08e1237860e303b828d183c11c246f0c1c6e1237861d26344c20686385c3109780110c0c1dc1068f848de187484823f082dc3c6981e08e1237860e311f841626634a16238411a40a83f87c20b11f1a70b0631a30b0631a3e08391a30b234303e1237861d20440fc20e70c2e6088401c0903f0b861c40401c05e1f08361a3f041c1719378631186836221840121e0e0380bc3e1201c4de18c48100713786312f04201918401c05a4f0f841438380bc3e10503460df08283a4f0f841c08941408e10460e1a307834181f0f844d0c070a11a4f0b861c28441e05e105b860e386823c262f0c386e1888383e1f089a1407949bc3e1048385a6870361a2024361d1847844de1870a0aa286c3840e074303e1f0a0e28206f84141c4814180e13821a0b8c200e04f0c625000446230570f84170c070c1008d3785c30e1823870e70b8625305c00180e103dc00d8609c10705c6c500060384e1f082e180e143411188c38080d70f84180b9c22100701785c30e1c14170c0709c20e06c7c2088507c20d87461de1f08381428401c090285385c307a0380ae106c3a50ef0f841c0a14220be1050810e1f0a25070e181f070e86c80a83f089bc30e18200e02f0c35c20a1f11c3e1134285c470f844d0a1435c30e0889c30e0886160af0f8414071b861c110c2231106c3a224d14221c2114221c184439c1a69311c3e113428524f0f84130a1787c2268501e5e1f08284d08949bc3e10503454470d844d0a141e08e170d1a103044200e0481c0bc2e18713c10c87461103f0839c30c9820090403f87c2091d1bc10e8689141088241107823850de18391c20e01c1bc10718200f040278614e104500fe105032408f081c1224341c121844260e09102e0e890e1a0e090c1e08e170d1a0e30441d121844240e18401213e170c386e10341c122434241c192387c286878a070708060909064609070b06110744860f0470b868d0818200908) else (if j<7 then 0xd0609c10e0847c246f0c4e4e14350e1020380bc3e1050346e1f083414206f8414195787c242950b852a082c55e1f090a54370f845506950bc10c8746190b0483a482f043a19203c1012e1f0a1a1139504220903c11c3e12342278285b82190e942dc3e11541a5430483220f8642c1213962427170f841d09084b122a8b8412138c2847e14378227302787122a911bc3188c23c246f0c38589c483a3e18710e2125150bc3e10710e1a38401e0804f0f841207209bc3e1050345e1051194d251784140d10200e02c1f85c30d1e0e0e0b8c1c080287387c20a04101446708404e10702817201f8508e183ca120e7082844942386180e161145e104038870d1c1e1103d2385c3469c3e0fe12342850f873841446844c12a470d1bc20898220709f0a1bc3079c2704e1c352854a43617c30994220709f091bc3079e91c383f091a11303b0fc2e18b4a2d06f04261c28883c2e1f091b070e141c07028478416e183d00f0470b868d07181e080b70b870d370434211848220f047089bc307201c080283f87c20a041012088401e09e1023860e483c11c3e11342810384012050770f841407a03887e11342250470d0fc20d9784118a0f84118a0f87c20e8604254a8352834af0f840d4a141cc84286387c24a1c301910461a181a17820e0b910bc3e12504250770b862d2700361818382207e106b861c383b85c3169033c1068c200e8a83787c28a1e2a0d8a0e2bc3e14162858a03a91c3e1060c250906460de08384a40d45291c346d2cc0ea441629c3e1060e1c23f0c41c00f1b84120c8e9028e170d1b14341787c28a084a09e1f088e30283c11c3e1434240e38388e25183a91050c70f8514385020090407387c20920200f0402787c20903902c106244c4ce1048e0fe104832446f0b87140d141bc10709480e16083512075211bc3e106d105e08642e40e7002c1820541a140b103b480cc1787c28a1c380e23f08365e14503630b83c1007e170e1a0e401f87c20e8604260883c1408e1f0a1a184078420de0894a0f0502013c31288ce10070278631285f121e02f07801c384215050cd228fc3e1202210050240bc2e187100ae18944440b0142a1412942c1b46f0b862837041c1f1d1f85c31690241910682d48e1f0a288d38401d47e10378715387f87c20a8482c60ff0f844809058c1fe10489816287f85c30a8482c60ff0b861509058c1f0230b861509058e1fe130c2a120b183ec2e18542416303a0a18a470f851438280a100492387c223a020092470f8412071c11c3e1048325a470f851446942210070240e05e170c3890782385c346838cc50d873821a28380a1e0e82385c30e20100e120f821c108c3c0f0702385c3869c23c286f0c385a406e1bc308140e1ce08421a5078380b48e1f08287078381005e18538411403f84170a10280f0e8442c5a4 else 0x868541c31409c4c3090381030983c0e1120380a1c18380a3118c42248184c1e2848643a30a040338d212821908085c24110c321d10742120703c6130781c2242284444808882411070c3448070e0a851068260e188814050d038a1a0507060e028a06890707c6190808320a44c14822050a061a07014619428582e40d89441a4287060e0f881c0d10381a20b0381b09203b1a200381a21103c1c32404204d10c4200d24902c101044200d185c1c20983c144942838c0a249141e4110389a30384c923110701c38483c423090384120708240e11201c20e0204120709121c108c2a1078204890789c6120741c6120741c6130903c3640782029c3e143422704f041c1f20662b45e1f0a2860883c1408e170c9a104044200902f082bc307a03515e170c1c4d30400e0f0470b870d383c1014e1f0a1a113873841006850bc20e0521a40e0502e3080381205e1f08287c485c281c20401c0902f0f841407a01dc20d8509c3e123430446923821c207b0fc286f0c386068602c30b23787c20c143c8d07f0c2c583f091a1120440e0f0470b868d38711a470b13821a128f122010441f0de1087861638440fc286f0c3860b03c11c3e12342272387384114694421b0d080811057091bc30e1b8217118c0f89100e1bc3188d0f05e170c4e5e1f091a14a4141e0e080250fc2e19211050e86787c20a520e1d2421c38403920301a252387c206a1c3a6e08743230782387c286c1c3a7e086442303f0a1bc30e17820e0b8e0fc20ef0d265e1f08282120659107e107786173837841de1884a1983f0b862728401c090403f87c283a11bc10e86880f0470f850d0a040e0a24f0f8487109a91c2e1a34285080381205e1f08280f45220a1d0cf0f841438381448e170d0e1a3e2229c3e14143060721c4a30501f850de0838dc286a1c1c40b7041c25270f850d13110fc286f0c385047090e0de1874c23e10521a40b708281720440fc286f0c38626f0d0e27270f841a10924286438638615203a25c3e10720e1a3c1c1c171f043a1a18401c09e18c4a1ce10502e44684b8411270d1a1218911bc3e10483850782385c346838c0e02f0d0fc20d9890870e0c901b0)))
def ecH10 (j : Nat) : Nat := 0xe04000c8aa2e000d6351982c002d7092782b000dba606368c34000000a0bb37522a1d00000000055e00000d93f000869000000852641303e53b48000000000000a1886e633d1214906074242a311859e00f6f8e505d00025092f000a17c4c35c00000011b913a4dd54464b0f83600089eea7000a4b53ba47b0ee67c1edde000000000000956940a0700000066100072381631a3098a8a2d000e6d114000505945c62000508e44f58b0c34ec65f55931f28e30c4a5d904f23806603e36b04362073c79013ac3533d424125a5f38f321bdc96cd5a287d5bb8b351d6a80a2577157101262a331c146601c32f1f529aec00073928d00001ec00e1c1c30536d490a580030102144820aa040101cc40e0000100
def ecD11 (j : Nat) : Nat := (if j<2 then (if j<1 then 0x86ffec8b0dffe9660fffd2ac1fffa4583fff43307ffe8560fffb2cc1fff65583ffec8b07ffd8660fffb0ac1fffe5981fffc9b03fff86607fff06c0fffe0581fff49b03ffe83607ffcc6c0fff94d81ffecb303ffd93607ffb0cc0fff60d81ffeb1b03ffd53607ff926c0fff20d81ffe29b03fff9858ffff2ab1fffe4563fffc32c7fff8558ffff06b1fffa6163fff4aac7ffe8558fffccab1fff66163ffecaac7ffd9158fffb0cb1fff61563ffec1ac7ffd6558fff930b1fff25563ffe42ac7fff83587ffd06b0fff94d61ffec1ac3ffd53587ff906b0fff14d61fffcc2a7fff9654ffff22a9fffe1953fffc1aa7fff6354fffd30a9fffa5953fff48aa7ffe8654fffb30a9fff65953ffec8aa7ffd8654fffb06a9fff58d53ffe4c2a7ffc9654fff922a9fff21953fffc3263fff854c7fff0698fffe0531fffa9a63fff514c7ffd3098fffa5531fff42a63ffe654c7ffb3098fff65931ffecaa63ffd864c7ffb0a98fff60d31ffec0a63ffd654c7ffac698fff54d31ffea8a63ffc854c7ffaa640fffa1463ffec28c7ffd83187ffaa630fffa1853ffec30a7ffd850c6ffb27c35ff64786bfecb7077fd95e0effb23c1effe1b81bfecb7037fd93e077fb0dc0dffa6363bfecc6c77fd95d8fdfb0db1dffa6361bfecc6c37fd93d86ffd3198dff66331bfecb6637fd95cc7fbac798fbfe1a86bfecc50d7fd93a1bfbf0741dff66283bfecb5077fd95a0effb2341ffde0681bfecc5037fd93a06ffd3131dff66263bfecb4c77fd9598effb2331ff760e63f7fc34c37fe98986ffb3130dff64e61ffac0cc3efd63986ffd3129dff66253bfecb4a77fd9594effb2329ff760e53bff4c4637fd988c6ffb2b18dff64e31ffac0c637ff9361afff22c37bfe1986bffcb3077ff9560efff22c1ff7e0d83f7fcb3037ff96606fff26c0effe1981ffbc0b03bfd86607df92cc0dffe6163bffcaac77ff9158effd30b1fbfa1963fef41ac77fd9858fdfb0cb1ff760d63bfe4c2c77fe98586ffb30b0ffd60561bffcc2a77ff9654efff22a9dffa6153fef41aa77fd9854effb2ca9ff760d53bfe4c2a77ff984c6fff2c98dffe5531bff4c263ff6814c7fbcc698dff66131bfecb2637fd954c7feb0298ff758d31bfe4c2637fe9821affb26437bf61886bff4c1077fd9620effb2a41dff64483feec19077fe98206ffb2640ffd60481bff4c0c77fd9818effb2a31fbfe1861bff4c0c37fd98186ffb2630fbf58c61bff4c0a77fd9814effb2c29dff64453bff4c0637fd980c6ffb2a18dbfa5b31b7ecb6635fd9794ef7b2918dbfe5981b7e4b3037de9321afed22435ef65086beec990d7f59121aff320435bfa5883bbf4a9077f69120ebfb2e41dbf65883bbeca9077bd9420efdb2441dfd64483bfcc81077bd942067fd3030df7a4c619fecc0c37bd94186fbb2630dfe64061 else 0xa1187841a2850a1cc3c2070d31449c96142e18b1c2414570f0850c501226240b85862c8161309c3c2123058b619861091814201f0b0c58c564c12258784102880a1207c208c3253900a268461e1091c1f08370c54a1187841a2850a0d07c2c31330a03e161869452141f0f08a28240f84185130dc30b206e1e10c5b0b0c3482a0f85861a515140905c3c230a86e1859054530b0c34a2a2985861a5151442c30d28a83e161869448581c230f08c2a0f85861a5121607c20c2890b0a83e1e1184858541f0f08c242c2b860e0861216154307c23090b0a83e1e1184858570c2ca2a1b8616415090514c3c230a098482e183e11c584c48170b0c24e2c26120b861661613120905c3c238b09892102e1849e2d6457f8a8514362644483886d10261e6439786d50cf618442db852d098610a41af82e504d607c40a380cd00e60023fbf7f24fd75f983f037d9cfa45f223e0f7bc4f6b5eb83d337a0cf345e4a3c577834efb5de03b8b76ccecc5d7a3ac774e4e915d1039f3738ce5c5ca2390771a4e235c2c381b6fbcdec5b9e37076db4da95b3436336b8cd665aae34ef6954d1f5a28341b67bcce859be333f65f4caf5940324b642cc7858d231676244c3558543073607cc0257ea2f9f5e94bc757782eb35d1cb9857122def5b64b5f56a82d1359bcb2e56422c3f57e4af155bc2b33560caba55562a5753e4a6f54c02943520ca36544e284750349fb53e427934ecc9be536a26a74cd498d530025db4afc950528a24d74924915521423f3476c8e051a222ff458489f512c221b43cc86a50be213f41f4831504c204b400c7f44fca1f573e347bb4f601e833c8c7864eee1d8f3a947434e701ca338dc70e4e021bc737246d54d941af3358c6a24d261a0733a46674cac1913318c6224c2a18272fd45eb4bbc17432dfc5ac4b3e16472c045714acc156b2a5c53a4a56147728644ff49d81353261c4b64952126f243447148c4112b21fc42e483a101f1f843dd47a00f031d6c39a47120dc71b1435346840cdb194c31e46160be717342d345880acb153c29c45220a0f13a426544ac092b11fc23444520877109420543ec07a30ebc1ca437a06bf0cf418f430005d30b4c15c42a2051709d41314254048308ac10841fe03cf07440dd41a4031305cc0ae4142024f043407940d8018302bc04a407600af00f400f40007ff64786fff48f07ffd91e0fffac7c0fff54f81fff42ec7ffd85d8fffb07b1fffa0f61fff29ec3ffd83d87ffaa7b0fff14f61fffa8e63ffe85cc7ffccb98fff61b31ffec2e63ffd81cc7ffacb98fffa1a83fff42d07ffd86a0ffff0740fff60e81ffea9d03ffe8598fffccb31fff61a63ffec2cc7fff83987ffb0730fff54e61fffb2ca7ffe8694fffb0d29fff61653ffeb2ca7fff858c7fff0718fff61631ffec1c63ffd538c7ffd26c37ff64d) else (if j<3 then 0x7884530b0c4d4258784905e50d14120e2f28906871210644f0f084878c2c25845440515120e89490f48871e302fc3c26e1090a089028344838bca1e10241b87845e71207c20d1e243040de1e1090f18344c48388403a282512161b8784263cb0c0b8dc3c2121c3e1e146a40a143d20570b0e3450e171036291387845e8090c0bc3c212283e1e144268a1458530f0a2080c1e2b851b862826718158dc3c21430b870a8a6161869c20146e1c870b0c5900a2d0e6185862a70509151914c2c325461e1068a10a0545308370c58e4c2b1b8784286281514c20dc31638ae1e1068a14207a1f08370c58e0e1e1491844d861a81e87c20dc31630ae1e1068a14a084201c8308370c5928e14103d8461861a8168d07c2c315318841346e1e10a1c201c509f0b0c34e151a0f845186447c20730c30d2e1e10a868a14a0545308370c58e221029844f861a715c3c207162930b0a8961e10a1c9c242048970f081c8521210240f8451864480820144dc3c21238ae1e1068a14943854530b0c34e2827861b842460515c3c2071630446e198610a1828201f089f0c34e151b87840e6060a080dc330c212384e198610a14255709530e14c2b87841a28527071326c2c30d38f0509e1e106891c9464589c9b0b0c350120f864f842460516c3c207153130489441461e10a2028684a230c97081d044141210240e518784920144d88c3c212393441461e10a1b08570c3450a610e263d85861a71c0a87c20dc31338a09e186e10918785308c30c34c100a228e6585862c828210807200dc2c3164c2e10a8a618b1820170c870850c120a4c9035878428808260e4dc3c2143e18b0ae10a1434b70f08b0a100e4e4d85861a70508118d14c2c3304128c8a8a6161869c170854530c58c4a322c424185861a8162d2cc2c30d304838f04468a61619824ac903c241c2a361f0b0cc160e1410578461861a8051415c2c31630d8a6113e18698485b0f081cc0c4e4a22100a2c29858642a2725071e0d1416c2c32150388848a6161981c24201c18101454530b0c5962b87841a2851608072726c2c30d41287051393616186a01c241478205308a30c894100e36140b0f103585864ab090a080719c24dc3314828a8b61e10a188848570f081ca0e2a28120a22518586629880a87111c4d25c3c248388840a14616198a024201c18101458570f085161028411b87842470a0827c3c20d123850310468e61e10920505b0b0c54a262987841a24630c3c20d1228a090884048ce1e117a44428204b089f0c350221c151a26258586509071e050a1912c3c22f4838889611861869c1c18105b0f08544902b87841a28515c3c20d142e10a868a0b1414581f0b0c54c422a240f85862c727161207c2c315390028b0ae1e1091f0f08585450a2b87841a28508c3c20d142e1e10a868a141f08370c54 else 0x6e1e10a8a0b9b0d37084854a3e8b87842a282c707c3c20d14273070403c2e1e10a1420847a1e370b0d205904e3c2b0e2d851b86349c214118d262a41403e1e10b101c241f0b0c80a0d842912365e51b8dc2c328295e1e124469018201c370cc4b12924c438784262880748c3c20d263140b4403e1e10c0695a624543c3925201498c30f085191187841a0e1c5e70f0807c3c20d263c41403e161a6931c9e25251498870f0920515100e5187842c407c38dc212152c42461e1468a188870504e370f084901187842842548c3c20d871d303e1618b1094570b0e1cc0a14138784244e6148848c3c28d263910a078b09e1e14689260e1f09343070d849b862834507c216c3282030603c2e1618a8d1e0c241f08307080f1b8784282650b05c3c2143030a8f4382e161981c2e230e37085044e1f0411871a163c7c3c216142128a61618b109460370b0c5884c2984224c40b45c3c2141b305a426e1e10a089f0851246c98a4f12928a4c4387849028a1614c2112b28a8a089890504b0844bcb8428542c5e5894985452726c3c2151450560868c9294381478530b0cc0e3f87842a1a2861f0e12c3c215141640a8a616186871835201f0f0838bcf10900e0b87845e70dc3c247302930724829612c4900e240961e10a385834a43b0c94c281a241c5e50dc3c230162f3442402e18a61179c781c370b0cc0c0a4512924a3c1c910a38298784d05c3c2473028b06a38ae161929c98392414b0962480530f092049a423a1586120e3c4682708c121232928386901194241f0f085084c120e4f8784284a7070927c3c214253e1e10a10902d230c5f086c74f123d0e2b844f864281107c248c30d1d38b0a0ee1e10d909c230f08746c84c25843a1b864260907c2c316213448f438ae161981c48241f085044ace221e100f85861a3a8240a420b270dc31e2348413e1909194342f0f085084c144f87851a4c64807c3c28d2632403e161c6931851230f0a3498c4428222c1e908f85871aa47c2c38d272e1e1244693146828201f0c7088e3412364440f0e4dc33128403a2851461989d142b0c206cc4c0e103587849a3c70a451ac31131308e126e18e14302d370f084870e2c37849b865061514113120d08a6e1618e18883848684f0b0c711110a8a3d0e2d85865090807141131288078489046183e10f24291508302f0ca089186509a364454dc33118605a6e1e10a0d1e483920704a230f0834514403a1e1d129290242987843cc4814c3c2121b3052461e10689071c2c206f0f084878e281187841a241c748c3c2121928c8586e1e1090f1c492624bc))
def ecH11 (j : Nat) : Nat := (if j<1 then 0xa22d82a763240f239aa0001814a08b2918767080d00000000000000029a7ec7ed17c0000000510308ab0ed80000000b28800018f3f363e768000000000000001087800080be0000000501eb343734f91a80009158415e85278910001646800000970000b3ec52784f7000153d601e8000a18c05764b9020e00000001102f1920000a88000038c3e3900001d03920a000000010802651000172ac5206160000102ad86cb93682280001a46887b914e69738784248634c00034d6c983f02ee0e161b800000ee000000061540001a263517f858000000000230000911000018556061c0dc00000001221517e000000031cb000000000004946f8de96c0000000041a5455887710b5147a8484e626a49533788561126615421be230c361940930031b306d750b5349489c00000000000d1e000000004147a010d21696700000002618c89f0000e81110d561f186023ad872ba2dc3ca621f03e942f8b07268f41b0c8e00000003ecf38950001491cc59300e1abf23b6ac8fa46602a000000041323b1630d4ce1a9380000a95c104d06d311cd66f8d6711ee960a442236a1510000000381379e90001e87ac255c4f82fcd54f29200000001606290cfd751173e83f81989470001838e4e050dc5967697b0c7d1150404a28ac91ac4db08e00038ea8000000081e80712a5600018960c384c330000a940000000029f2c52bc3e00000000c62c000000000000000858694d0000d0e844958ef248200010dc9a45000082a0000119300004268ce3793f2c4148334eb4835f219246ca7b587fb29158e0000797f0000003400000000000a3f9c97712ce46980eec1d780a23a2c2f80000000000003db0ac318a5a3523e0000623001ba636c000198c803a46a5c5361c2f091c668c420000d1c362f507baa030000c10e0a1203484a8a464529393c3ac844932dfaa2ed8a340c000010d3b8180003cee20faf3e6e13945c6859407204940286181019046c12db9255745200030e200004c3b43394a20000000001008d0585e00000001ceb896ee3f865546bc50f100018660000624bb19b63b2c27d8520000094fc9388cb00000003008b07100018170000112652e80001c57e05b000182c748b80000000825a2a90000d238000000000000000c2700000c83000127be45718860000000072e000063fe000186ba901e3b0b5b60c1394ee0ea06e800404a030a00a20068f3a30eec10b023468c1c0000e00380060a2cf9a0a2cb8902529cc08108180830200b40c702702c4009c0c08000300320c78d080024091020870c001c58d000c1092e080141600e8426207020408d8100240800a08b0302207ab02043010004e0312380072238182146c08018009030408088040d2810204f2a040008602000000400285005548a1c000090c0c200668c18014086ac0048100020c281 else (if j<2 then 0x3cf500000001b8a93120000833800000003831000021a4000223f000027780005054c175e53c00040c0747d78c4000000000000000c890000b403c4dc0006cd40001e0a8aa3748f0000000000040992245c6ac000713160320000000399e232b76cc85d84f8000000000000000741000000000000203fa549f1a80002958e4acc145e1e6333612c0000000a0192643c56f9bbb3ea00b800059b442c200028d152510000d5c0431c85a516f95e5081b87898a6f090000000000016308000000050aca7e40001825e2de00036b4c9d013238624000684c033bc79c4bb800050c89227cc20000000185db82ecc2b000000034e6800000000000899ad7db394256c0003841f00463630efee0e6ae600028b1d89b41bc28ee4624149000101cc518997b136715a10cf92285c4e4355ca181c720462050c82a54822d7c7f80ba925b0001020c0003508d0a3502babe3daf798d43f0690d81061f2000180dd159d804a6aa4229222a19e0003d22323c038ae09f01264fa621777e808c482d41920001261995fc471c240000425d132ec7c8000423ae422000086fe9f8f11be3d207d989e72cc0000000387e0000a96ae284239f1ea20f08e97020fad8e7ef0eca0ea38cba5a8000792a000148d889ee0e733c4448209a8000400dc42a03cbcbb7268a7c6c59e206c27c884c8e4f1114cb162db0f76226f32c0001826f82bc46668738fea8010000b3b9097f9080000a8750af000073a696d0449e1ec890106354db216d0c85a04bc680000b0cfc97c4b40000502762294478e120001886000054d298ce00000005894000000000000000a30fa6bf8da800000000003cb178c1a807202fd26000000000002e95917800012786f00000061a8963ecf37005cab866ff4a5f985000000020b4ee14b0d400008e0ba2350cb68dd850a43bbaac5157d0b39f4188200000000000520928400005049b0840001c8759b80001a329e2900000001c0de010a05581fe3174474f17cc04421994b2394c531000020a2c0e6fbc000008018000000142f124c8000496402970bd38081374663a4ca0000707c0002466106be456f222004fc320000889400000000000000000011a54487a92aac700007400a61b6d4f853b01ef2f02956d580000486c000715ce2a626f00beba12125000028982032a37b57e58b824d1323a0002f1448fd5962620000055d3000150010dba14134280001b260885e0ec000000014ae0c4667ddc37b8720000244f48ff9730000987364108d643c120b2cf2393900000002083f55da2d800010300000a49bc22509d80c530e9c82fc4100000001e6a050fa8687b8f09676438000b46400010fd615053a905974e610d16aa8855c4f47906020407ac0000000d18e00008df04aac13a85e7c5040624b32d189cd70000fc44925c0007a0d22e2f6e510b8000 else 0xd3bbb97747461e353ec00018f681b252b40002894ed453af660fd870582f0b0000010e7112d000000000004044a3e0a01d516644e649c000080e0000c168000072c80000000000180b113af212d4b023fc9cf0001a39))
def ecD12 (j : Nat) : Nat := 0x2c2039528361c241412202960e561c2496101ca941b0e1204160f0a18d3080e5a1431a610506c3841cc20396850c6984880a50943841d020393250a18d38828361c20e6101c992850c69c4852848443841d020987850c6984072c361c230910143948708e2038d8708a2038d8708a203c28634a242880f0e11840724361c23080e54a428634e244052458ac3841d220395290a18d388281e1431a6101cb1324161431291214a12110e107414104c3c28634f54a874d19451ce224157b0e89b9b3d600b455126c488870fa1c532c5808e0e616e1cc1b000fff86fff83fff81fff63fff61fff31ffe86ffe83ffe81ffe63ffe61ffe53ffe31ffd86ffd83ffd81ffd63ffd61ffd53ffd31ffc86ffc83ffc81ffc63ffc61ffc53ffc31
def ecH12 (j : Nat) : Nat := 0x385004b54a482ba4b790e80009bd951f000000000006d3d0272d4e3b49290002c519007898fcbb85cf482d1d285050e6373c82533a0bfd2140007b86808a060c3343eb922807c70f4b77c1d41e048160a693208073266a9b6d7a0734e9b3080000000000000346500000370434000d115cbc33ffc8ad0a88320cab8d023c3117d2c8322299c00052ced1500026febcaca9602ee82f23646ed20b6447d89000000000dd6adc000a0d000002c10d180656bb80999214c4400093fbeb6c407c5e130747c0000ccc7cb0000d43cd1a7ae330ab251c8c00014e10315449b058000a1e70b624422d5d4a1321a1b348094199186950ead8379d1b134c00043534e28c6189f219dcb5e2b24a1c976adcac96424017f2e7794ac1b01fc41510f38c3b48d216231ac1714d2d19c39380e00b80063008c0b2150cd8413800041d8a00e18046b1095864000202cc134000e8fa0e7f8468120c7a852abe645d34acf16f3f5c710002caf000000021224e800018db904c000c4466ece06971c025d524c42a43eac4204b40349167a8b09293e785300014fc626c0000000000ec5c0002819490c1b408b0000000fcbeea30000000a49690c2297c6e000012a0000459108285829c8000784f068689746162e9f2400000000000000bc4b4a00000c6a00014a62bec8f6a1989268b4408ed427cfb31e98f823120f7e1c88f30003041949e6cb41f8000e084a040001cf2aae94e3dab800033286e69b5b83841ee7091357e55c911cdf000349c22af4c7640827400014b9415c533112b00440a1891832d043e40089de398811a336c5bb03c00041cd8052b2aae2ac30000d2208b814ba410e25ba3b00020d69079eab0000000721c0003acd6917c80000732244fd35d03dd3973132a1a90b90c40000000000c09c0009417c3b4003aefdc8e48362fbb3198f0d1253b8cb100008036278000e4500000001530000151c00000000000000c8e412c8bddc390001ca210d7c07b0ac070f2364620003f0200033153bc3ca334100f57324e020001c6f321b046040e8efa2d0e4782f7493a4c40000000c55000328eebd1aa800002b20000000a11284c329dc5adc7407d7254c8f0000000000000053d3c36438212fa2a800060fd30800034f10002ea4e033635208c4a8015b6c0d210251930251e941c0eb71010d200030750000000926bc69c05070e236bcad8a76eaa0003c63002ac89d33fb1a508a074fbcba9e344d8ec000126622650ea2bd4ac149f9d08f1098a90001830c8b6477a8fc303020609220000080208610127032d04171302083e0335070545000002360f106000f804000100000a3402000f0a113f0b01049e110e00064a2d001825630515230100131b2e000001180e2c0d4b060f07010f000b00000006000c06000104020124053c000100030602
def ecD13 (j : Nat) : Nat := 0x3085ff
def ecH13 (j : Nat) : Nat := 0x287c6800000000000000000003050010a0000000000000000000000000c4e6e05000bc40000b8d000000000002c005b00000309ee400f40000000000141001d9000005a800b9c00002ef0018e000000000000000002b5000000000000000000000000000015adc000000000000a4800610cf75c0000000000000000000000000000000000000003e0d96b300000000000000000000000005022310c0053000e4400f2000160000000000000001c60000000000001560000000010
def ecLevels : Nat → Packing
  | 9 => (113,4,6,0,0,12,0,ecD9)
  | 10 => (608,3,6,0,0,15,0,ecD10)
  | 11 => (309,2,6,0,0,15,0,ecD11)
  | 12 => (27,1,6,0,0,11,0,ecD12)
  | 13 => (1,0,6,0,0,0,0,ecD13)
  | _ => emptyPacking
def ecIndex : Nat → Nat → Option (Nat × Nat)
  | 10 => lookupWord 32 163 7 12 7 1 ecH10
  | 11 => lookupWord 191 1049 7 15 10 1 ecH11
  | 12 => lookupWord 105 521 8 14 9 1 ecH12
  | 13 => lookupWord 10 149 1 10 5 1 ecH13
  | _ => fun _ => none
def ec : Forest := ⟨1023,13,fun i => ecY[i]?.getD (0,0),ecC,ecA,ecLevels,ecIndex⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ecP9_0 : block ec 9 0 81=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ecP9_81 : block ec 9 81 32=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem ecB9 : block ec 9 0 113=true := (@block_merge ec 9 0 81 32 ecP9_0 ecP9_81)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ecP10_0 : block ec 10 0 27=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ecP10_27 : block ec 10 27 96=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ecP10_123 : block ec 10 123 96=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ecP10_219 : block ec 10 219 96=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ecP10_315 : block ec 10 315 96=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ecP10_411 : block ec 10 411 96=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ecP10_507 : block ec 10 507 34=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ecP10_541 : block ec 10 541 67=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem ecB10 : block ec 10 0 608=true := (@block_merge ec 10 0 315 293 (@block_merge ec 10 0 123 192 (@block_merge ec 10 0 27 96 ecP10_0 ecP10_27) (@block_merge ec 10 123 96 96 ecP10_123 ecP10_219)) (@block_merge ec 10 315 192 101 (@block_merge ec 10 315 96 96 ecP10_315 ecP10_411) (@block_merge ec 10 507 34 67 ecP10_507 ecP10_541)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ecP11_0 : block ec 11 0 29=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ecP11_29 : block ec 11 29 96=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ecP11_125 : block ec 11 125 33=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ecP11_158 : block ec 11 158 96=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ecP11_254 : block ec 11 254 55=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem ecB11 : block ec 11 0 309=true := (@block_merge ec 11 0 125 184 (@block_merge ec 11 0 29 96 ecP11_0 ecP11_29) (@block_merge ec 11 125 33 151 ecP11_125 (@block_merge ec 11 158 96 55 ecP11_158 ecP11_254)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ecP12_0 : block ec 12 0 27=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem ecB12 : block ec 12 0 27=true := ecP12_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ecP13_0 : block ec 13 0 1=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem ecB13 : block ec 13 0 1=true := ecP13_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ecT : checkedTables ec 13 := by
  intro k hk
  interval_cases k
  · exact (rfl : block ec 0 0 0 = true)
  · exact (rfl : block ec 1 0 0 = true)
  · exact (rfl : block ec 2 0 0 = true)
  · exact (rfl : block ec 3 0 0 = true)
  · exact (rfl : block ec 4 0 0 = true)
  · exact (rfl : block ec 5 0 0 = true)
  · exact (rfl : block ec 6 0 0 = true)
  · exact (rfl : block ec 7 0 0 = true)
  · exact (rfl : block ec 8 0 0 = true)
  · exact ecB9
  · exact ecB10
  · exact ecB11
  · exact ecB12
  · exact ecB13
def clippedInputs := inputs.map (fun a => a &&& ~~~hardSeed)
def clippedGraph := graph &&& ~~~hardSeed

def clippedPairs : List (Sig × Row × Row) := List.ofFn fun i : Fin 9 =>
  let l := [2,1,2,4,1,1,2,4,8].getD i.val 0
  (clippedInputs.getD i.val zero, Fin.ofNat 512 l, Fin.ofNat 512 (l+2^i.val))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem clipLower : Lower true clippedInputs clippedGraph 14 := by
  apply lower_impossible (by unfold proper; decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro a ha
    apply essential_ok (show checkEssential clippedGraph clippedInputs clippedPairs=true by decide +kernel) a
    rw [show clippedPairs.map Prod.fst = clippedInputs by decide +kernel]
    exact List.mem_toFinset.mpr ha
  · rw [show clippedGraph = targetOf ec by decide +kernel]
    exact root_index (g:=ec) (top:=13) (k:=13) (i:=0) (before_sound clipKnown clipValid)
      (by decide +kernel) ecT (by decide) (by decide +kernel)
def clipBy (m : Sig) (r : Row) : Row := if bit r m then 0 else r
def clipRow := clipBy hardSeed
theorem clip_general (a m : Sig) (origin : bit 0 a = false) :
    rename (clipBy m) a = a &&& ~~~m := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  let r : Row := ⟨j,hj⟩
  change bit r (rename (clipBy m) a) = _
  rw [bit_rename]
  have e : (a &&& ~~~m).getLsbD j = (bit r a && !(bit r m)) := by
    simp only [bit,r,BitVec.getLsbD_and,BitVec.getLsbD_not,hj,decide_true,Bool.true_and]
  rw [e]
  by_cases h : bit r m=true
  · simp only [clipBy,h,ite_true,origin,Bool.not_true,Bool.and_false]
  · have v := Bool.eq_false_iff.mpr h
    simp only [clipBy,v,Bool.false_eq_true,ite_false,Bool.not_false,Bool.and_true]
theorem clip_word (a : Sig) (origin : bit 0 a = false) :
    rename clipRow a = a &&& ~~~hardSeed := clip_general a hardSeed origin
theorem seedSlice (lower : Lower true clippedInputs clippedGraph 14) : Slice true inputs graph (~~~hardSeed) 14 := by
  have gg := clip_word graph (by decide +kernel)
  have go : restrictRows clipRow (observe graph)=observe clippedGraph :=
    (observe_rename _ _).symm.trans (congrArg observe gg)
  refine ⟨clipRow,clippedInputs,?_,?_,?_,?_⟩
  · intro r
    by_cases h : bit r hardSeed=true
    · rw [clipRow,clipBy,if_pos h]
      decide +kernel
    · have e : bit r hardSeed=false := Bool.eq_false_iff.mpr h
      rw [clipRow,clipBy,if_neg h]
      simpa only [bit,BitVec.getLsbD_not,r.isLt,decide_true,Bool.true_and,Bool.not_false] using congrArg Bool.not e
  · intro a ha
    have orig : inputs.all (fun w => !(bit 0 w))=true := by decide +kernel
    have z : bit 0 a=false := by simpa using (List.all_eq_true.mp orig a ha)
    rw [←observe_rename,clip_word a z]
    exact Or.inl (List.mem_map_of_mem (List.mem_map_of_mem ha))
  · rw [go]
    exact observe_proper (by unfold proper; decide +kernel)
  · rw [go]
    exact lower

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem fullInitialImpossible : Impossible true graph 14 (inputs++[hardSeed]).toFinset := by
  apply poolCut_sound (seedSlice clipLower) [] rfl
  · decide +kernel
  · decide +kernel

end PEqualNP.Outside.L_meta_4813_aux.Certificate

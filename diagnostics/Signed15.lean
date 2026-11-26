import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_9825
namespace Engine
open PEqualNP.CircuitLowerBounds
abbrev Sig := BitVec 1024
def zero : Sig := 0
def one : Sig := BitVec.allOnes 1024
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
def bit (i : Fin 1024) (a : Sig) : Bool := a.getLsbD i.val
theorem bit_zero (i) : bit i zero = false := by simp [bit,zero]
theorem bit_one (i) : bit i one = true := by unfold bit one; rw [BitVec.getLsbD_allOnes]; simp
theorem bit_neg (i) (a : Sig) : bit i (neg a) = !(bit i a) := by simp [bit,neg,i.isLt]
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
theorem get_rep {u} (w : List Sig) (i : Nat) : Repr u (w.map (nrm u)) (w.getD i zero) := by
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
theorem extract {u target} (gs : List Gate) (w : List Sig)
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
abbrev Row := Fin 1024
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
def inputs : List Sig := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000]
def graph : Sig := 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0c0fffffffffffffffffffffffffffffffffffffffffffffffffffffaeafffff0c0fffffffffffffffffffffffffffaf0f0ffffffffffffffffffffffffffeaf0c0fffffffffffefcfcfffffffffffaf0f0ffeefeeeffeefcccffeafaeaffeaf0c0
def sample (r : Row) (j : Fin 10) := bit r (inputs.getD j.val zero)
def edge (x : Fin 10 → Bool) : Bool :=
  (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 6 && x 9) || (x 6 && x 8) || (x 5 && x 8)
theorem edge_table : ∀ r : Row, bit r graph = edge (sample r) := by decide +kernel
theorem graph_proper : proper graph := by unfold proper; decide +kernel
theorem input_list : List.ofFn (fun j : Fin 10 => inputs.getD j.val zero) = inputs := rfl
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
abbrev Move := Sig × Sig × Row
def shifted (d r : Row) : Row :=
  if h : r.val < 1024-d.val then ⟨d.val+r.val,by omega⟩ else ⟨r.val-(1024-d.val),by omega⟩
def backwards (d : Row) : Row := Fin.ofNat 1024 (1024-d.val)
def rowMove (m : Move) (r : Row) : Row :=
  if bit r m.1 then shifted m.2.2 r else if bit r m.2.1 then shifted (backwards m.2.2) r else r
def mux (m a b : Sig) := (m &&& a) ||| (~~~m &&& b)
def wordMove (m : Move) (a : Sig) :=
  mux m.1 (a.rotateRight m.2.2.val) (mux m.2.1 (a.rotateRight (backwards m.2.2).val) a)
theorem bit_shift (d r : Row) (a : Sig) : bit r (a.rotateRight d.val) = bit (shifted d r) a := by
  unfold bit
  rw [BitVec.getLsbD_rotateRight_of_lt d.isLt]
  by_cases h : r.val < 1024-d.val <;> simp [shifted,h,r.isLt]
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
  (List.range 10).filterMap fun i => if m.testBit i then some (i,inputs.getD i zero) else none
def vars (m : Nat) := (selected m).map Prod.snd
def varsX (m : Nat) := vars m
def vertex (m j : Nat) := if m.testBit j then inputs.getD j zero else zero

def graphGoal (m : Nat) : Sig :=
  let x := vertex m
  (x 1 &&& x 2) ||| (x 2 &&& x 3) ||| (x 3 &&& x 4) ||| (x 0 &&& x 4) ||| (x 0 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 7) ||| (x 4 &&& x 9) ||| (x 5 &&& x 7) ||| (x 7 &&& x 9) ||| (x 6 &&& x 9) ||| (x 6 &&& x 8) ||| (x 5 &&& x 8)
def subcube (z o : Nat) : Sig :=
  if z &&& o != 0 then zero else
    (List.range 10).foldl (fun w i => if z.testBit i then w &&& ~~~(inputs.getD i zero)
      else if o.testBit i then w &&& inputs.getD i zero else w) one
def fixRows (z o : Nat) : List Move :=
  (List.range 10).filterMap fun j =>
    let x := inputs.getD j zero
    let step := Fin.ofNat 1024 (1 <<< j)
    if z.testBit j then some (zero,x,step)
    else if o.testBit j then some (~~~x,zero,step) else none
def swapRows (v : Nat) : Move :=
  let i := v &&& 15
  let j := v >>> 4
  let a := inputs.getD i zero
  let b := inputs.getD j zero
  let d := (1 <<< j)-(1 <<< i)
  (a &&& ~~~b,b &&& ~~~a,Fin.ofNat 1024 d)
def supportPairs (_t mask : Nat) : List (Sig × Row × Row) :=
  (selected mask).map fun (i,a) => (a,0,Fin.ofNat 1024 (1 <<< i))
def graphPairs (m hints : Nat) : List (Sig × Row × Row) :=
  (selected m).map fun (i,a) =>
    let r := 1 <<< ((hints >>> (4*i)) &&& 15)
    (a,Fin.ofNat 1024 r,Fin.ofNat 1024 (r ||| (1 <<< i)))
def properB (T : Sig) := T != zero && T != one
theorem proper_of (T : Sig) (h : properB T = true) : proper T := by
  simpa only [properB,proper,Bool.and_eq_true,bne_iff_ne] using h
abbrev ColumnInfo := Nat × Nat × Nat × Nat × Nat
def colFree (m z o : Nat) := m ^^^ (m &&& (z ||| o))
def chartGoal (m : Nat) : Sig := graphGoal m
def rawMask (m : Nat) (c : ColumnInfo) : Nat := m % 1024+1024*(c.1/1024)
def colCheck (m : Nat) (c : ColumnInfo) (prior : Nat → Nat) : Bool :=
  let (z,o,q,s,L) := c
  let ms := fixRows z o
  let raw := rawMask m c
  let free := colFree raw (z % 1024) o
  let G := movedWord ms (chartGoal m)
  let xs := supportPairs (z/1024+80) s
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
  let free := colFree raw (z % 1024) o
  let G := movedWord ms (chartGoal m)
  let xs := supportPairs (z/1024+80) s
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
abbrev Bits := BitVec 320
abbrev Signals := Bits × Bits
abbrev Decor := Sig × Signals
def ofRows {n : Nat} (r : Fin n → Row) (v : Sig) : BitVec n :=
  (BitVec.ofBoolListLE (List.ofFn (fun i => bit (r i) v))).cast List.length_ofFn
theorem ofRows_bit {n : Nat} (r : Fin n → Row) (v : Sig) (i : Fin n) :
    (ofRows r v).getLsbD i.val = bit (r i) v := by
  simp only [ofRows,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [i.isLt]
def pairSig (r s : Fin 320 → Row) (a : Sig) : Signals := (ofRows r a,ofRows s a)
def properPairs (T : Sig) (r s : Fin 320 → Row) :=
  ∀ i, bit (r i) T = true ∧ bit (s i) T = false
theorem pair_sep {T r s} (h : properPairs T r s) : Sep T 320 r s (pairSig r s) := by
  exact ⟨h,fun a i => ⟨ofRows_bit _ _ _,ofRows_bit _ _ _⟩⟩
def faithful (r s : Fin 320 → Row) (x : Decor) := x.2 = pairSig r s x.1
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
    let a := ws.getD (bits &&& 31) defaultDecor
    let b := ws.getD ((bits >>> 5) &&& 31) defaultDecor
    decodeBank k (bits >>> 12) (ws++[dbin ((bits >>> 10) &&& 3) a b])
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
def asRow (cols : Nat → Bits) (i : Fin 320) : Row :=
  (BitVec.ofBoolListLE (List.ofFn (fun j : Fin 10 => (cols j.val).getLsbD i.val))).toFin.cast
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
theorem coordinate9 : ∀ r : Row, bit r (inputs.getD 9 zero) = r.val.testBit 9 := by decide +kernel
theorem input_coords : ∀ (j : Fin 10) (r : Row), bit r (inputs.getD j.val zero) = r.val.testBit j.val := by
  intro j
  fin_cases j
  · exact coordinate0
  · exact coordinate1
  · exact coordinate2
  · exact coordinate3
  · exact coordinate4
  · exact coordinate5
  · exact coordinate6
  · exact coordinate7
  · exact coordinate8
  · exact coordinate9
theorem asRow_bit (cols : Nat → Bits) (i : Fin 320) (j : Fin 10) :
    bit (asRow cols i) (inputs.getD j.val zero) = (cols j.val).getLsbD i.val := by
  rw [input_coords]
  change (BitVec.ofBoolListLE (List.ofFn (fun h : Fin 10 => (cols h.val).getLsbD i.val))).getLsbD j.val = _
  simp only [BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [j.isLt]
def rawDecor (m : Nat) (p q : Nat → Bits) : List Decor :=
  (selected m).map (fun (j,a) => (a,p j,q j))
theorem selected_entry {m j a} (h : (j,a) ∈ selected m) :
    j<10 ∧ a=inputs.getD j zero := by
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
  (x 1 &&& x 2) ||| (x 2 &&& x 3) ||| (x 3 &&& x 4) ||| (x 0 &&& x 4) ||| (x 0 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 7) ||| (x 4 &&& x 9) ||| (x 5 &&& x 7) ||| (x 7 &&& x 9) ||| (x 6 &&& x 9) ||| (x 6 &&& x 8) ||| (x 5 &&& x 8)
theorem bit_vertex (m : Nat) (v : Nat → Bits) (i : Fin 320) (j : Fin 10) :
    bit (asRow v i) (vertex m j.val) =
    ((if m.testBit j.val then v j.val else 0) : Bits).getLsbD i.val := by
  by_cases hh : m.testBit j.val = true
  · simpa [vertex,hh] using asRow_bit v i j
  · simp [vertex,hh,bit_zero]
theorem bit_liftGoal (m : Nat) (v : Nat → Bits) (i : Fin 320) :
    bit (asRow v i) (graphGoal m) = (liftGoal m v).getLsbD i.val := by
  have pos (j : Nat) (hj : j<10) : (vertex m j).getLsbD (asRow v i).val = ((if m.testBit j then v j else 0) : Bits).getLsbD i.val := bit_vertex m v i ⟨j,hj⟩
  simp only [bit,graphGoal,liftGoal,BitVec.getLsbD_and,BitVec.getLsbD_or]
  simp only [pos 0 (by decide),pos 1 (by decide),pos 2 (by decide),pos 3 (by decide),pos 4 (by decide),pos 5 (by decide),pos 6 (by decide),pos 7 (by decide),pos 8 (by decide),pos 9 (by decide)]
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
    if (rs ||| column d z.2) != BitVec.allOnes 320 then true else
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
  have be : ((restCov (coverage (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 320) = false := by
    simpa using sep
  change (if (restCov (coverage (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 320 then true else if !properB z.1 || ws.any (fun v => v.1==z.1) then true else _) = true at test
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
  by_cases hj : j<10
  · let i : Fin 10 := ⟨j,hj⟩
    have hm : inputs.getD i.val zero ∈ inputs := by
      rw [← input_list]
      exact List.mem_ofFn.mpr ⟨i,rfl⟩
    exact (input_coords i r).symm.trans ((h _ hm).trans (input_coords i s))
  · have le : 1024 ≤ 2^j := by
      change 2^10 ≤ 2^j
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
abbrev Forest := Nat × Nat × (Nat → Bits × Bits) × List ColumnInfo × List (List Nat) ×
  (Nat → Packing) × (Nat → Nat → Option (Nat × Nat))
def Forest.mask (g : Forest) : Nat := g.1
def Forest.mode (g : Forest) : Bool := !(g.1.testBit 12)
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
theorem chart_bit (m : Nat) (v : Nat → Bits) (i : Fin 320) :
    bit (asRow v i) (chartGoal m) = (chartSamples m v).getLsbD i.val := by
  exact bit_liftGoal m v i
theorem chart_pairs {m : Nat} {p q : Nat → Bits}
    (hp : chartSamples m p = BitVec.allOnes 320) (hq : chartSamples m q = 0) :
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
def forestRecord (tab : Packing) (_raw i : Nat) :=
  let (_,_,_,_,_,_,_,words) := tab
  words (2*i)
def storedDepth (_g : Forest) (depth : Nat) := depth
def readNode (g : Forest) (k i : Nat) : Nat × List Decor × List Decor :=
  let raw := wiresOf g
  let (_,depth,_,_,_,_,_,data) := g.levels k
  let len := 12*storedDepth g depth
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
    let more := chosenSteps bank (ops >>> 12) (paid >>> 1) n
    if paid &&& 1 == 0 then more else
      (getFieldV ops 10 2,(bank.getD (ops &&& 31) defaultDecor).1,
        (bank.getD (getFieldV ops 5 5) defaultDecor).1) :: more
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
def decodeHints (cw d : Nat) : Nat → Nat → List (Nat × Nat)
  | 0,_ => []
  | n+1,x => (x % (1 <<< cw),(x >>> cw) % (1 <<< d)) ::
      decodeHints cw d n (x >>> (cw+d))
def forestHints (tab : Packing) (_raw i : Nat) :=
  let (_,depth,cw,_,_,_,_,words) := tab
  let data := words (2*i+1)
  decodeHints cw depth (data % 256) (data >>> 8)
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
  (chartSamples g.mask (fun j => (g.samples j).1) == BitVec.allOnes 320) &&
  (chartSamples g.mask (fun j => (g.samples j).2) == 0) &&
  g.cols.all (fun c => colCheck g.mask c prior) &&
  g.autos.all (fun p => autoOK (targetOf g) (p.map swapRows))
def indexedRoot (g : Forest) (k i : Nat) (ws : List Sig) :=
  decide (i < (g.levels k).1) && sameWords (stateSet g k i) ws
def Known (u : Bool) (entries : List (Nat × Nat)) := ∀ e ∈ entries, Lower u (varsX e.1) (graphGoal e.1) e.2
theorem baseKnown : Known true [] := by simp [Known]
theorem known_down {u es} (h : Known true es) : Known u es := fun e he => lower_down (h e he)
def lanePlace (v : Nat) (upper : Nat) := 2^321*upper+v
def combineLanes {α : Type} (f : α → Bits) : List α → Nat
  | [] => 0
  | x::xs => lanePlace (f x).toNat (combineLanes f xs)
def units : Nat → Nat
  | 0 => 0
  | n+1 => lanePlace 1 (units n)
theorem laneSmall (x : Bits) : x.toNat < 2^321 :=
  lt_trans x.isLt (by decide +kernel)
theorem place_and (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u &&& lanePlace b.toNat v = lanePlace (a &&& b).toNat (u &&& v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_and,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<321 <;> simp only [h,ite_true,ite_false,BitVec.toNat_and,Nat.testBit_and]
theorem place_or (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u ||| lanePlace b.toNat v = lanePlace (a ||| b).toNat (u ||| v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_or,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<321 <;> simp only [h,ite_true,ite_false,BitVec.toNat_or,Nat.testBit_or]
theorem place_xor (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u ^^^ lanePlace b.toNat v = lanePlace (a ^^^ b).toNat (u ^^^ v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_xor,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<321 <;> simp only [h,ite_true,ite_false,BitVec.toNat_xor,Nat.testBit_xor]
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
def fullMarks (r packed : Nat) := ((packed+r) >>> 320) &&& r
theorem unit_bit (n i : Nat) (hi : i<n) : (units n).testBit (321*i) = true := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
    rw [units,lanePlace,Nat.testBit_two_pow_mul_add _ (by decide +kernel : 1 < 2^321)]
    cases i with
    | zero => simp
    | succ i =>
      have di : 321*(i+1)-321=321*i := by omega
      have ge : ¬321*(i+1)<321 := by omega
      simp only [ge,ite_false,di]
      exact ih _ (by omega)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem guardBit (a : Bits) : (a.toNat+1).testBit 320 = (a==BitVec.allOnes 320) := by
  by_cases h : a=BitVec.allOnes 320
  · subst a
    decide +kernel
  · have lim := a.isLt
    have ne : a.toNat ≠ 2^320-1 := by
      intro eq
      apply h
      apply BitVec.eq_of_toNat_eq
      simpa only [BitVec.toNat_allOnes] using eq
    have lt : a.toNat+1<2^320 := by omega
    rw [Nat.testBit_eq_false_of_lt lt]
    exact (beq_eq_false_iff_ne.mpr h).symm
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem mark_at {α} (f : α → Bits) (xs : List α) (i : Nat) (hi : i<xs.length) :
    (fullMarks (units xs.length) (combineLanes f xs)).testBit (321*i) =
      (f xs[i]==BitVec.allOnes 320) := by
  simp only [fullMarks,Nat.testBit_and,Nat.testBit_shiftRight,unit_bit _ _ hi,Bool.and_true]
  induction xs generalizing i with
  | nil => simp at hi
  | cons a xs ih =>
    simp only [combineLanes,List.length_cons,units,lanePlace]
    have sum (u v x : Nat) : 2^321*u+x+(2^321*v+1)=2^321*(u+v)+(x+1) := by omega
    rw [sum,Nat.testBit_two_pow_mul_add _ (show (f a).toNat+1<2^321 from by have := (f a).isLt; omega)]
    have hi' : i < xs.length+1 := hi
    cases i with
    | zero => simpa using guardBit (f a)
    | succ i =>
      have ge : ¬321*(i+1)+320<321 := by omega
      have di : 321*(i+1)+320-321=321*i+320 := by omega
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
    ((mask &&& 1 == 0) || f x) && onMarks f (mask >>> 321) xs
theorem marked_ok {α} (f : α → Bool) (mask : Nat) (xs : List α) (i : Nat) (hi : i<xs.length)
    (bitOn : mask.testBit (321*i)=true) (ok : onMarks f mask xs=true) : f xs[i]=true := by
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
      apply ih (mask:=mask >>> 321) (i:=i) (by simpa using hi) _ ok.2
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
def validSwap (v : Nat) : Bool := and (Nat.ble ((v &&& 15)+1) (v >>> 4)) (Nat.ble ((v >>> 4)+1) 10)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem swap_table : ∀ v : Fin 160, validSwap v.val=true → ∀ t : Fin 10, swapIdx v.val t.val<10 ∧
    wordMove (swapRows v.val) (inputs.getD t.val zero) = inputs.getD (swapIdx v.val t.val) zero := by decide +kernel
theorem swap_input {v t : Nat} (hv : validSwap v=true) (ht : t<10) : swapIdx v t<10 ∧
    wordMove (swapRows v) (inputs.getD t zero) = inputs.getD (swapIdx v t) zero := by
  have lt : v<160 := by
    simp only [validSwap,Bool.and_eq_true,Nat.ble_eq,Nat.shiftRight_eq_div_pow] at hv
    omega
  exact swap_table ⟨v,lt⟩ hv ⟨t,ht⟩
def idxOf (perm : List Nat) (t : Nat) : Nat := perm.foldl (fun t v => swapIdx v t) t
theorem idx_move {perm : List Nat} (ok : perm.all validSwap=true) {t : Nat} (ht : t<10) :
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
  | n+1,bits,ws => force (zN ((bits >>> 10) &&& 3) (ws.getD (bits &&& 31) 0) (ws.getD ((bits >>> 5) &&& 31) 0))
      fun z => decodeN n (bits >>> 12) (ws++[z])
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
  let len := 12*depth
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
      if len>k then true else if combField xs[q] (!u) ka kb op i j != BitVec.allOnes 320 then true
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
    by_cases hit : combField xs[q] (!u) ka kb op i j = BitVec.allOnes 320
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

structure KWRooms (S : Finset Sig) (T : Sig) where
  owns : Sig → Row → Row → Prop
  total : ∀ p n, bit p T=true → bit n T=false → ∃ v, owns v p n
  valid : ∀ {v p n}, owns v p n → v∈S ∧ bit p v=true ∧ bit n v=false
  unique : ∀ {v w p n}, owns v p n → owns w p n → v=w
  rect : ∀ {v p n p' n'}, owns v p n' → owns v p' n → owns v p n
def kwLeaf (T : Sig) : KWRooms {T} T where
  owns v p n := v=T ∧ bit p T=true ∧ bit n T=false
  total p n hp hn := ⟨T,rfl,hp,hn⟩
  valid := by rintro v p n ⟨rfl,hp,hn⟩; exact ⟨by simp,hp,hn⟩
  unique := by rintro v w p n ⟨rfl,_,_⟩ ⟨eq,_,_⟩; exact eq.symm
  rect := by rintro v p n p' n' ⟨e,hp,_⟩ ⟨_,_,hn⟩; exact ⟨e,hp,hn⟩
def kwFork {U : Finset Sig} {T a b : Sig} {d : Nat} (d01 : d=0 ∨ d=1)
    (ha : a∉U) (hb : b∉U) (hz : bin d a b∉U)
    (H : KWRooms (insert (bin d a b) U) T) : KWRooms (insert a (insert b U)) T := by
  let z := bin d a b
  let sel := fun p n : Row => if d=0 then (if bit n a then b else a)
    else (if bit p a then a else b)
  have pick (p n) : sel p n=a ∨ sel p n=b := by
    dsimp only [sel]; split <;> split <;> simp
  have outside (p n) : sel p n ∉ U := by
    rcases pick p n with eq | eq
    · simpa only [eq] using ha
    · simpa only [eq] using hb
  have separates (p n) (hp : bit p z=true) (hn : bit n z=false) :
      bit p (sel p n) = true ∧ bit n (sel p n) = false := by
    have b0 (r : Row) : bit r (bin 0 a b) = (bit r a && bit r b) := by simp [bin,bit]
    have b1 (r : Row) : bit r (bin 1 a b) = (bit r a || bit r b) := by simp [bin,bit]
    rcases d01 with e | e <;> cases pA : bit p a <;> cases nA : bit n a <;>
      simp_all [sel,z]
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
      exact ⟨inS,separates p n (H.valid hv).2.1 (H.valid hv).2.2⟩
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
      by_cases h : d=0
      · simpa only [sel,h,ite_true] using we
      · simpa only [sel,h,ite_false] using ve
theorem kwWidth {u T k S} (h : Live u T k S) : S.card ≤ k+1 := by
  induction h using Live.ind with
  | stop hp => simp
  | @binary k U a b d hd ha hb hab hf tail ih =>
    have hu : bin d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1 := Finset.card_insert_le (a:=a) (insert b U)
    have h2 := Finset.card_insert_le (a:=b) U
    omega
theorem kwTight {T k S} (run : Live false T k S) (tight : S.card=k+1) :
    Nonempty (KWRooms S T) := by
  induction k generalizing S with
  | zero =>
    obtain ⟨rfl,_⟩ := run
    exact ⟨kwLeaf T⟩
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
    have d01 : d=0 ∨ d=1 := by rcases hd with h | ⟨h,_⟩ <;> simp_all <;> omega
    exact ⟨kwFork d01 ha hb fresh H⟩
def onlyWire (S : Finset Sig) (T v : Sig) (p n : Row) :=
  bit p T=true ∧ bit n T=false ∧ ∀ w∈S, bit p w=true → bit n w=false → w=v
theorem kwOwn {S T v p n} (H : KWRooms S T) (one : onlyWire S T v p n) : H.owns v p n := by
  obtain ⟨w,hw⟩ := H.total p n one.1 one.2.1
  have eq := one.2.2 w (H.valid hw).1 (H.valid hw).2.1 (H.valid hw).2.2
  exact eq ▸ hw
theorem kwCross {S T k a b p n pa pb na nb} (size : k+1=S.card) (different : a≠b)
    (A : onlyWire S T a p na) (B : onlyWire S T b p nb)
    (C : onlyWire S T a pa n) (D : onlyWire S T b pb n) : Impossible false T k S := by
  intro j hj run
  have lb := kwWidth run
  have tight : S.card=j+1 := by omega
  obtain ⟨H⟩ := kwTight run tight
  exact different (H.unique (H.rect (kwOwn H A) (kwOwn H C)) (H.rect (kwOwn H B) (kwOwn H D)))
def kwWireB (ws : List Sig) (T v : Sig) (p n : Row) : Bool :=
  bit p T && !bit n T && ws.all (fun w => !bit p w || bit n w || w==v)
theorem kwWireB_sound {ws T v p n} (h : kwWireB ws T v p n=true) :
    onlyWire ws.toFinset T v p n := by
  simp only [kwWireB,Bool.and_eq_true,Bool.not_eq_true',List.all_eq_true] at h
  refine ⟨h.1.1,h.1.2,?_⟩
  intro w hw hp hn
  simpa only [hp,hn,Bool.not_true,Bool.false_or,beq_iff_eq] using
    h.2 w (List.mem_toFinset.mp hw)
def kwWord (T : Sig) (ws : List Sig) (k value : Nat) : Bool :=
  let a := ws.getD (value % 16) zero
  let b := ws.getD ((value >>> 4) % 16) zero
  let row := fun i : Nat => Fin.ofNat 1024 ((value >>> (8+10*i)) % 1024)
  decide (k+1=ws.toFinset.card) && decide (a≠b) &&
    kwWireB ws T a (row 0) (row 2) && kwWireB ws T b (row 0) (row 3) &&
    kwWireB ws T a (row 4) (row 1) && kwWireB ws T b (row 5) (row 1)
theorem kwWord_sound {T ws k v} (h : kwWord T ws k v=true) : Impossible false T k ws.toFinset := by
  simp only [kwWord,Bool.and_eq_true,decide_eq_true_eq] at h
  exact kwCross h.1.1.1.1.1 h.1.1.1.1.2 (kwWireB_sound h.1.1.1.2)
    (kwWireB_sound h.1.1.2) (kwWireB_sound h.1.2) (kwWireB_sound h.2)
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
def kwTest (g : Forest) (k a n : Nat) (data : Nat → Nat) :=
  (List.range n).all fun j => kwWord (targetOf g) (stateSet g k (a+j)) k (data j)
theorem mixedCut {g k a n data} (mode : g.mode=false) (h : kwTest g k a n data=true) :
    CutRow g k a n := by
  intro j lo hi
  right
  rw [mode]
  have hh := List.all_eq_true.mp h (j-a) (List.mem_range.mpr (by omega))
  have sum : a+(j-a)=j := by omega
  change kwWord _ (stateSet g k (a+(j-a))) k _=true at hh
  rw [sum] at hh
  exact kwWord_sound hh
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
structure FreeRooms (S : Finset Sig) (T H : Sig) where
  owns : Sig → Row → Row → Prop
  total : ∀ p n, bit p T=true → bit n T=false →
    (bit p H=true ∧ bit n H=false) ∨ ∃ v, owns v p n
  valid : ∀ {v p n}, owns v p n → v∈S ∧ bit p v=true ∧ bit n v=false
  unique : ∀ {v w p n}, owns v p n → owns w p n → v=w
  rect : ∀ {v p n p' n'}, owns v p n' → owns v p' n → owns v p n

structure SingleFactor (S : Finset Sig) (T : Sig) where
  inner : Finset Sig
  outer : Finset Sig
  pivot : Sig
  cover : inner ∪ outer = S
  apart : Disjoint inner outer
  inside : KWRooms inner pivot
  outside : FreeRooms outer T pivot
def freeFrom {S T} (D : KWRooms S T) (h : Sig) : FreeRooms S T h where
  owns := D.owns
  total p n hp hn := Or.inr (D.total p n hp hn)
  valid := D.valid
  unique := D.unique
  rect := D.rect
def freeHide {S T h} (D : FreeRooms S T h) : FreeRooms (S.erase h) T h where
  owns v p n := v≠h ∧ D.owns v p n
  total := by
    intro p n hp hn
    rcases D.total p n hp hn with yes | ⟨v,hv⟩
    · exact Or.inl yes
    · by_cases eq : v=h
      · exact Or.inl (eq ▸ (D.valid hv).2)
      · exact Or.inr ⟨v,eq,hv⟩
  valid := by
    rintro v p n ⟨ne,hv⟩
    exact ⟨Finset.mem_erase.mpr ⟨ne,(D.valid hv).1⟩,(D.valid hv).2⟩
  unique := fun h1 h2 => D.unique h1.2 h2.2
  rect := fun a b => ⟨a.1,D.rect a.2 b.2⟩
def factorOfTree {S T} (D : KWRooms S T) : SingleFactor S T where
  inner := S
  outer := ∅
  pivot := T
  cover := by simp
  apart := by simp
  inside := D
  outside := {
    owns := fun _ _ _ => False
    total := fun p n hp hn => Or.inl ⟨hp,hn⟩
    valid := fun h => h.elim
    unique := fun h _ => h.elim
    rect := fun h _ => h.elim }
def freeFork {h : Sig} {U : Finset Sig} {T a b : Sig} {d : Nat} (d01 : d=0 ∨ d=1)
    (ha : a∉U) (hb : b∉U) (hz : bin d a b∉U)
    (H : FreeRooms (insert (bin d a b) U) T h) : FreeRooms (insert a (insert b U)) T h := by
  let z := bin d a b
  let sel := fun p n : Row => if d=0 then (if bit n a then b else a)
    else (if bit p a then a else b)
  have pick (p n) : sel p n=a ∨ sel p n=b := by
    dsimp only [sel]; split <;> split <;> simp
  have outside (p n) : sel p n ∉ U := by
    rcases pick p n with eq | eq
    · simpa only [eq] using ha
    · simpa only [eq] using hb
  have separates (p n) (hp : bit p z=true) (hn : bit n z=false) :
      bit p (sel p n) = true ∧ bit n (sel p n) = false := by
    have b0 (r : Row) : bit r (bin 0 a b) = (bit r a && bit r b) := by simp [bin,bit]
    have b1 (r : Row) : bit r (bin 1 a b) = (bit r a || bit r b) := by simp [bin,bit]
    rcases d01 with e | e <;> cases pA : bit p a <;> cases nA : bit n a <;>
      simp_all [sel,z]
  refine { owns := fun v p n => (v∈U ∧ H.owns v p n) ∨ (v=sel p n ∧ H.owns z p n)
           total := ?_
           valid := ?_
           unique := ?_
           rect := ?_ }
  · intro p n hp hn
    rcases H.total p n hp hn with closed | ⟨v,hv⟩
    · exact Or.inl closed
    right
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
      exact ⟨inS,separates p n (H.valid hv).2.1 (H.valid hv).2.2⟩
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
      by_cases h : d=0
      · simpa only [sel,h,ite_true] using we
      · simpa only [sel,h,ite_false] using ve
theorem supportSide {A B U : Finset Sig} {a b z : Sig}
    (e : A∪B=insert z U) (disj : Disjoint A B) (za : z∈A)
    (freshA : a∉insert z U) (freshB : b∉insert z U) (freshZ : z∉U) :
    (insert a (insert b (A.erase z))) ∪ B=insert a (insert b U) ∧
    Disjoint (insert a (insert b (A.erase z))) B ∧ a∉A.erase z ∧ b∉A.erase z := by
  have hb : z∉B := fun h => Finset.disjoint_left.mp disj za h
  have allmem (w : Sig) : w∈A∨w∈B ↔ w=z∨w∈U := by
    rw [←Finset.mem_union,←Finset.mem_insert,e]
  have aout : a∉A ∧ a∉B := by
    have h : a∉A∪B := by rw [e]; exact freshA
    simpa using h
  have bout : b∉A ∧ b∉B := by
    have h : b∉A∪B := by rw [e]; exact freshB
    simpa using h
  refine ⟨?_,?_,fun h => aout.1 (Finset.mem_of_mem_erase h),fun h => bout.1 (Finset.mem_of_mem_erase h)⟩
  · ext w
    have m := allmem w
    by_cases eq : w=z
    · subst w; simp [freshZ,hb]
    · simp only [Finset.mem_union,Finset.mem_insert,Finset.mem_erase] at *
      tauto
  · apply Finset.disjoint_left.mpr
    intro w hw hwB
    rcases Finset.mem_insert.mp hw with rfl | hw
    · exact aout.2 hwB
    rcases Finset.mem_insert.mp hw with rfl | hw
    · exact bout.2 hwB
    exact Finset.disjoint_left.mp disj (Finset.mem_of_mem_erase hw) hwB
def factorExpand {U T a b d} (hd : d=0 ∨ d=1)
    (freshA : a∉insert (bin d a b) U) (freshB : b∉insert (bin d a b) U)
    (freshZ : bin d a b∉U) (F : SingleFactor (insert (bin d a b) U) T) :
    SingleFactor (insert a (insert b U)) T := by
  classical
  let z := bin d a b
  by_cases inn : z∈F.inner
  · obtain ⟨eq,apart,ha,hb⟩ := supportSide F.cover F.apart inn freshA freshB freshZ
    have old : KWRooms (insert z (F.inner.erase z)) F.pivot := by
      rw [Finset.insert_erase inn]; exact F.inside
    exact ⟨_,F.outer,F.pivot,eq,apart,kwFork hd ha hb (by simp [z]) old,F.outside⟩
  · have out : z∈F.outer := by
      have m : z∈F.inner∪F.outer := by rw [F.cover]; exact Finset.mem_insert_self _ _
      exact (Finset.mem_union.mp m).resolve_left inn
    obtain ⟨eq,apart,ha,hb⟩ := supportSide ((Finset.union_comm _ _).trans F.cover) F.apart.symm out freshA freshB freshZ
    have old : FreeRooms (insert z (F.outer.erase z)) T F.pivot := by
      rw [Finset.insert_erase out]; exact F.outside
    exact ⟨F.inner,_,F.pivot,(Finset.union_comm _ _).trans eq,apart.symm,F.inside,
      freeFork hd ha hb (by simp [z]) old⟩
def factorKeep {U T a b d} (hd : d=0 ∨ d=1) (ab : a≠b) (hb : b∉U)
    (fresh : bin d a b∉insert a (insert b U)) (H : KWRooms (insert (bin d a b) U) T) :
    SingleFactor (insert a (insert b U)) T := by
  let z := bin d a b
  have za : z≠a := by
    intro eq
    apply fresh
    exact Finset.mem_insert.mpr (Or.inl eq)
  have zU : z∉U := fun h => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
  have set0 : (insert z U).erase a = insert z (U.erase a) := by
    ext v
    simp only [Finset.mem_erase,Finset.mem_insert]
    by_cases eq : v=z
    · subst v; simp [za]
    · tauto
  have H0 : FreeRooms (insert z (U.erase a)) T a := set0 ▸ freeHide (freeFrom H a)
  have H1 := freeFork hd (show a∉U.erase a by simp)
    (fun m => hb (Finset.mem_of_mem_erase m)) (fun m => zU (Finset.mem_of_mem_erase m)) H0
  have eq : insert a (insert b (U.erase a))=insert a (insert b U) := by
    ext v
    simp only [Finset.mem_insert,Finset.mem_erase]
    tauto
  have H1' : FreeRooms (insert a (insert b U)) T a := eq ▸ H1
  refine ⟨{a},(insert a (insert b U)).erase a,a,?_,?_,kwLeaf a,freeHide H1'⟩
  · ext v; simp only [Finset.mem_union,Finset.mem_singleton,Finset.mem_erase,Finset.mem_insert]; tauto
  · simp
theorem oneShare {T k S} (r : Live false T k S) (budget : k≤S.card) :
    Nonempty (SingleFactor S T) := by
  induction k generalizing S with
  | zero =>
    obtain ⟨rfl,_⟩ := r
    exact ⟨factorOfTree (kwLeaf T)⟩
  | succ k ih =>
    obtain ⟨U,a,b,d,hd,rfl,_,_,ab,fresh,tail⟩ := r
    let z := bin d a b
    have zU : z∉U := fun m => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem m))
    have size := kwWidth tail
    have zcard : (insert z U).card=U.card+1 := Finset.card_insert_of_notMem zU
    change (insert z U).card ≤ k+1 at size
    have hd01 : d=0 ∨ d=1 := by rcases hd with q | ⟨q,_⟩ <;> simp_all <;> omega
    by_cases ain : a∈U
    · rw [Finset.insert_eq_of_mem (Finset.mem_insert_of_mem ain : a∈insert b U)] at budget
      by_cases bin' : b∈U
      · rw [Finset.insert_eq_of_mem bin'] at budget; omega
      · rw [Finset.card_insert_of_notMem bin'] at budget
        obtain ⟨H⟩ := kwTight tail (by change (insert z U).card=k+1; omega)
        exact ⟨factorKeep hd01 ab bin' fresh H⟩
    · by_cases bin' : b∈U
      · rw [Finset.insert_eq_of_mem bin',Finset.card_insert_of_notMem ain] at budget
        obtain ⟨H⟩ := kwTight tail (by change (insert z U).card=k+1; omega)
        have comm : bin d b a=z := by
          rcases hd01 with eq | eq <;> subst d <;> simp [z,bin,BitVec.and_comm,BitVec.or_comm]
        have H' : KWRooms (insert (bin d b a) U) T := by simpa only [comm] using H
        have fr : bin d b a∉insert b (insert a U) := by simpa only [comm,Finset.insert_comm] using fresh
        have F := factorKeep hd01 ab.symm ain fr H'
        exact ⟨by simpa only [Finset.insert_comm] using F⟩
      · have an : a∉insert b U := by simp [ain,ab]
        rw [Finset.card_insert_of_notMem an,Finset.card_insert_of_notMem bin'] at budget
        obtain ⟨F⟩ := ih tail (by change k≤(insert z U).card; omega)
        have neA : a≠z := fun e => fresh (Finset.mem_insert.mpr (Or.inl e.symm))
        have neB : b≠z := fun e => fresh (Finset.mem_insert_of_mem (Finset.mem_insert.mpr (Or.inl e.symm)))
        have fa : a∉insert z U := fun h => (Finset.mem_insert.mp h).elim neA ain
        have fb : b∉insert z U := fun h => (Finset.mem_insert.mp h).elim neB bin'
        exact ⟨factorExpand hd01 fa fb zU F⟩
theorem factorForced {S : Finset Sig} {T : Sig} (F : SingleFactor S T) (p n : Row)
    (hp : bit p T=true) (hn : bit n T=false)
    (none : ∀ v∈F.outer, bit p v=true → bit n v=false → False) :
    bit p F.pivot=true ∧ bit n F.pivot=false := by
  rcases F.outside.total p n hp hn with h | ⟨v,hv⟩
  · exact h
  · exact False.elim (none v (F.outside.valid hv).1 (F.outside.valid hv).2.1 (F.outside.valid hv).2.2)
theorem factorOuterOwn {S : Finset Sig} {T : Sig} (F : SingleFactor S T) {a p n} (ao : a∈F.outer)
    (one : onlyWire S T a p n) : F.outside.owns a p n := by
  rcases F.outside.total p n one.1 one.2.1 with hpivot | ⟨w,hw⟩
  · obtain ⟨w,hw⟩ := F.inside.total p n hpivot.1 hpivot.2
    obtain ⟨wi,wp,wn⟩ := F.inside.valid hw
    have ws : w∈S := F.cover ▸ Finset.mem_union_left _ wi
    have eq := one.2.2 w ws wp wn
    rw [eq] at wi
    exact False.elim (Finset.disjoint_left.mp F.apart wi ao)
  · obtain ⟨wo,wp,wn⟩ := F.outside.valid hw
    have ws : w∈S := F.cover ▸ Finset.mem_union_right _ wo
    have eq := one.2.2 w ws wp wn
    exact eq ▸ hw
theorem outerCannotCross {S : Finset Sig} {T : Sig} (F : SingleFactor S T) {a b p n pa pb na nb}
    (aout : a∈F.outer) (bout : b∈F.outer)
    (different : a≠b) (A : onlyWire S T a p na) (B : onlyWire S T b p nb)
    (C : onlyWire S T a pa n) (D : onlyWire S T b pb n) : False :=
  different (F.outside.unique (F.outside.rect (factorOuterOwn F aout A) (factorOuterOwn F aout C))
    (F.outside.rect (factorOuterOwn F bout B) (factorOuterOwn F bout D)))
theorem innerCannotCross {S : Finset Sig} {T : Sig} (F : SingleFactor S T) {a b p n pa pb na nb}
    (different : a≠b) (A : onlyWire F.inner F.pivot a p na) (B : onlyWire F.inner F.pivot b p nb)
    (C : onlyWire F.inner F.pivot a pa n) (D : onlyWire F.inner F.pivot b pb n) : False :=
  different (F.inside.unique (F.inside.rect (kwOwn F.inside A) (kwOwn F.inside C))
    (F.inside.rect (kwOwn F.inside B) (kwOwn F.inside D)))
theorem innerSource {S : Finset Sig} {T : Sig} (F : SingleFactor S T) {v p n}
    (hv : v∈F.inner) (only : onlyWire S T v p n) : onlyWire F.inner F.pivot v p n := by
  have h : bit p F.pivot=true ∧ bit n F.pivot=false := by
    apply factorForced F p n only.1 only.2.1
    intro w wo hp hn
    have ws : w∈S := F.cover ▸ Finset.mem_union_right _ wo
    have eq := only.2.2 w ws hp hn
    exact Finset.disjoint_left.mp F.apart hv (eq ▸ wo)
  refine ⟨h.1,h.2,?_⟩
  intro w wi hp hn
  exact only.2.2 w (F.cover ▸ Finset.mem_union_left _ wi) hp hn
theorem hornRule {S : Finset Sig} {T : Sig} (F : SingleFactor S T) {a b c p n pa na}
    (ar : onlyWire S T a p na) (br : onlyWire S T b pa n) (cr : onlyWire S T c p n)
    (ia : a∈F.inner) (ib : b∈F.inner) : c∈F.inner := by
  have ah := innerSource F ia ar
  have bh := innerSource F ib br
  obtain ⟨w,hw⟩ := F.inside.total p n ah.1 bh.2.1
  obtain ⟨wi,wp,wn⟩ := F.inside.valid hw
  have ws : w∈S := F.cover ▸ Finset.mem_union_left _ wi
  exact (cr.2.2 w ws wp wn) ▸ wi
theorem parityRule {S : Finset Sig} {T : Sig} (F : SingleFactor S T) {a b p n pa pb na nb}
    (hs : a∈S) (ht : b∈S) (ne : a≠b)
    (h1 : onlyWire S T a p na) (h2 : onlyWire S T b p nb)
    (h3 : onlyWire S T a pa n) (h4 : onlyWire S T b pb n) :
    ((a∈F.inner ∧ b∈F.inner) ∨ (a∉F.inner ∧ b∉F.inner)) → False := by
  rintro (⟨ia,ib⟩ | ⟨oa,ob⟩)
  · exact innerCannotCross F ne (innerSource F ia h1) (innerSource F ib h2)
      (innerSource F ia h3) (innerSource F ib h4)
  · rw [←F.cover,Finset.mem_union] at hs ht
    exact outerCannotCross F (hs.resolve_left oa) (ht.resolve_left ob) ne h1 h2 h3 h4
def colorPoint (v : Fin 10 → Bool) : Row :=
  (BitVec.ofBoolListLE (List.ofFn v)).toFin.cast (by simp [List.length_ofFn])
theorem color_bit (v : Fin 10 → Bool) (i : Fin 10) :
    bit (colorPoint v) (inputs.getD i.val zero) = v i := by
  rw [input_coords]
  change (BitVec.ofBoolListLE (List.ofFn v)).getLsbD i.val = _
  simp only [BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [i.isLt]
def colorField (d j : Nat) : Fin 10 := Fin.ofNat 10 ((d >>> (1+4*j)) % 16)
def colorRow (d j : Nat) : Row := Fin.ofNat 1024 ((d >>> (13+10*j)) % 1024)
def colorWire (ws : List Sig) (names : Nat) (j : Fin 10) : Sig :=
  ws.getD ((names >>> (4*j.val)) % 16) zero
def colorRule (ws : List Sig) (T : Sig) (names d : Nat) : Bool :=
  let a := colorWire ws names (colorField d 0)
  let b := colorWire ws names (colorField d 1)
  let c := colorWire ws names (colorField d 2)
  let r := colorRow d
  if d.testBit 0 then
    (decide (a ∈ ws) && decide (b ∈ ws) && decide (a ≠ b)) &&
    (kwWireB ws T a (r 0) (r 2) && kwWireB ws T b (r 0) (r 3) &&
      kwWireB ws T a (r 4) (r 1) && kwWireB ws T b (r 5) (r 1))
  else kwWireB ws T a (r 0) (r 2) && kwWireB ws T b (r 3) (r 1) &&
    kwWireB ws T c (r 0) (r 1)
def constraintWord (d : Nat) : Sig :=
  let x := fun j => inputs.getD (colorField d j).val zero
  if d.testBit 0 then x 0 ^^^ x 1 else ~~~(x 0 &&& x 1) ||| x 2
def colorTruth {ws : List Sig} {T : Sig} (F : SingleFactor ws.toFinset T)
    (names : Nat) (i : Fin 10) := decide (colorWire ws names i ∈ F.inner)
theorem parity_bit {A B : Prop} [Decidable A] [Decidable B]
    (h : ¬ ((A ∧ B) ∨ (¬A ∧ ¬B))) : (decide A ^^ decide B) = true := by
  by_cases a : A <;> by_cases b : B <;> simp_all
theorem horn_bit {A B C : Prop} [Decidable A] [Decidable B] [Decidable C]
    (h : A → B → C) : (!(decide A && decide B) || decide C) = true := by
  by_cases a : A <;> by_cases b : B <;> simp_all
theorem bit_xor (r : Row) (a b : Sig) : bit r (a ^^^ b) = (bit r a ^^ bit r b) :=
  BitVec.getLsbD_xor
theorem rule_valid {ws T names d} (F : SingleFactor ws.toFinset T)
    (h : colorRule ws T names d = true) :
    bit (colorPoint (colorTruth F names)) (constraintWord d) = true := by
  have bits (i) := color_bit (colorTruth F names) (colorField d i)
  by_cases flag : d.testBit 0 = true
  · simp only [colorRule,flag,ite_true,Bool.and_eq_true,decide_eq_true_eq] at h
    have rule := parityRule F (List.mem_toFinset.mpr h.1.1.1) (List.mem_toFinset.mpr h.1.1.2) h.1.2
      (kwWireB_sound h.2.1.1.1) (kwWireB_sound h.2.1.1.2) (kwWireB_sound h.2.1.2) (kwWireB_sound h.2.2)
    simp only [constraintWord,flag,ite_true]
    rw [bit_xor,bits,bits]
    exact parity_bit rule
  · simp only [colorRule,if_neg flag,Bool.and_eq_true] at h
    have rule := hornRule F (kwWireB_sound h.1.1) (kwWireB_sound h.1.2) (kwWireB_sound h.2)
    simp only [constraintWord,if_neg flag]
    change bit _ (prime true (neg (prime false _ _)) _) = true
    rw [bit_prime,bit_neg,bit_prime]
    change (!(bit _ _ && bit _ _) || bit _ _) = true
    rw [bits,bits,bits]
    exact horn_bit rule
def colorSet : List Nat → Sig
  | [] => one
  | d::ds => constraintWord d &&& colorSet ds
theorem color_set {ws T names} (F : SingleFactor ws.toFinset T) (ds : List Nat)
    (h : ds.all (colorRule ws T names) = true) :
    bit (colorPoint (colorTruth F names)) (colorSet ds) = true := by
  induction ds with
  | nil => exact bit_one _
  | cons d ds ih =>
    simp only [List.all_cons,Bool.and_eq_true] at h
    change bit _ (prime false _ _) = true
    rw [bit_prime,rule_valid F h.1,ih h.2]
    rfl
def colorCheck (ws : List Sig) (T : Sig) (k names : Nat) (ds : List Nat) :=
  decide (k ≤ ws.toFinset.card) && ds.all (colorRule ws T names) && (colorSet ds == zero)
theorem color_sound {ws T k names ds} (h : colorCheck ws T k names ds=true) :
    Impossible false T k ws.toFinset := by
  simp only [colorCheck,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq] at h
  intro n le run
  obtain ⟨F⟩ := oneShare run (le.trans h.1.1)
  have ok := color_set F ds h.1.2
  rw [h.2,bit_zero] at ok
  contradiction
def colorRange (g : Forest) (k a n : Nat) (ds : Nat → Nat × List Nat) :=
  (List.range n).all fun i =>
    colorCheck (stateSet g k (a+i)) (targetOf g) k (ds i).1 (ds i).2
theorem colorCut {g k a n ds} (mode : g.mode=false)
    (h : colorRange g k a n ds=true) : CutRow g k a n := by
  intro j lo hi
  right
  rw [mode]
  have hh := List.all_eq_true.mp h (j-a) (List.mem_range.mpr (by omega))
  have eq : a+(j-a)=j := by omega
  change colorCheck (stateSet g k (a+(j-a))) _ _ _ _=true at hh
  rw [eq] at hh
  exact color_sound hh
def neighbor670 (i : Fin 10) : Nat := [4, 2, 1, 2, 0, 0, 1, 2, 5, 4].getD i.val 0
def absentRow670 (i : Fin 10) : Row := Fin.ofNat 1024 (1 <<< neighbor670 i)
def presentRow670 (i : Fin 10) : Row := Fin.ofNat 1024 ((1 <<< i.val) ||| (1 <<< neighbor670 i))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem requiredInputs :
    (∀ i : Fin 10, bit (absentRow670 i) graph ≠ bit (presentRow670 i) graph) ∧
    (∀ i j : Fin 10, i ≠ j →
      bit (absentRow670 i) (inputs.getD j.val zero) =
      bit (presentRow670 i) (inputs.getD j.val zero)) := by decide +kernel
theorem twoRoots (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (computes : PEqualNP.MetaComplexity.circuitFun 10 C = edge) (small : C.size ≤ 16) :
    ∃ (u : Bool) (k : Nat), k ≤ (if u then 15 else 16) ∧ Live u graph k inputs.toFinset := by
  have goalEq : (execute C.gates inputs).getD C.output zero = graph := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    exact (table_eval C legal C.output r).trans ((congrFun computes (sample r)).trans (edge_table r).symm)
  have len : C.gates.length ≤ 16 := small
  have mode : ∃ u : Bool, (u=false → ∀ g ∈ C.gates, isNot g=false) ∧ C.gates.countP (fun g => !isNot g) ≤ (if u then 15 else 16) := by
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
  have idx (a : Sig) (ha : a ∈ inputs) : ∃ i : Fin 10, inputs.getD i.val zero = a := by
    rw [←input_list] at ha
    exact List.mem_ofFn.mp ha
  have eq : S = inputs.toFinset := by
    ext a
    constructor
    · exact fun h => List.mem_toFinset.mpr (sub a h)
    · intro ha
      obtain ⟨i,rfl⟩ := idx a (List.mem_toFinset.mp ha)
      apply raw_required run inputs (inputs.getD i.val zero) sub (absentRow670 i) (presentRow670 i)
        (requiredInputs.1 i)
      intro v hv hn
      obtain ⟨j,rfl⟩ := idx v hv
      apply requiredInputs.2 i j
      rintro rfl
      exact hn rfl
  exact ⟨u,k,hk.trans count,eq ▸ run⟩
theorem directSplit
    (m : ∀ k, k ≤ 16 → ¬Live false graph k inputs.toFinset)
    (s : ∀ k, k ≤ 15 → ¬Live true graph k inputs.toFinset) :
    ¬ PEqualNP.MetaComplexity.HasCircuitSize 10 edge 16 := by
  rintro ⟨C,legal,small,computes⟩
  obtain ⟨mode,k,hk,run⟩ := twoRoots C legal (funext computes) small
  cases mode
  · exact m k hk run
  · exact s k hk run
def orderLaw (S : Finset Sig) (T : Sig) (f : Sig → Nat) :=
  (∀ {a b p n na nb pa pb}, a ≠ b →
    onlyWire S T a p na → onlyWire S T b p nb →
    onlyWire S T a pa n → onlyWire S T b pb n → f a ≠ f b) ∧
  (∀ {a b c p n na pb}, onlyWire S T a p na → onlyWire S T b pb n →
    onlyWire S T c p n → f a = f b → f c ≤ f a)
theorem only_value {k S T v p n} (run : Live false T k S) (h : onlyWire S T v p n) :
    v∈S ∧ bit p v=true ∧ bit n v=false := by
  obtain ⟨w,hw,hp,hn⟩ := mono_row_difference run rfl h.1 h.2.1
  exact h.2.2 w hw hp hn ▸ ⟨hw,hp,hn⟩
def gateList (a b : Sig) (U : Finset Sig) := [a,b].filter fun t => decide (t∈U)
def gateMap (a b z v : Sig) := if v=a ∨ v=b then z else v
def gateColor (a b z : Sig) (U : Finset Sig) (f : Sig → Nat) (v : Sig) :=
  let kept := gateList a b U
  if v∈kept then kept.idxOf v else kept.length+f (gateMap a b z v)
theorem gate_kept {a b v U} :
    v∈gateList a b U ↔ (v=a ∨ v=b) ∧ v∈U := by simp [gateList]
theorem gate_mem {a b z v : Sig} {U : Finset Sig} (h : v∈insert a (insert b U)) :
    gateMap a b z v ∈ insert z U := by
  by_cases eq : v=a ∨ v=b
  · simp [gateMap,eq]
  · simp_all [gateMap]
theorem mono_bin_bit {d} (hd : allowed false d) (a b : Sig) (r : Row) :
    bit r (bin d a b) = if d=0 then bit r a && bit r b else bit r a || bit r b := by
  rcases allowed_four hd with rfl | rfl | ⟨h,_⟩ | ⟨h,_⟩
  · simp [bit,bin]
  · simp [bit,bin]
  · contradiction
  · contradiction
theorem gate_only {a b d U T v p n} (hd : allowed false d)
    (unused : v∉gateList a b U) (h : onlyWire (insert a (insert b U)) T v p n) :
    onlyWire (insert (bin d a b) U) T (gateMap a b (bin d a b) v) p n := by
  refine ⟨h.1,h.2.1,?_⟩
  intro w hw hp hn
  rcases Finset.mem_insert.mp hw with rfl | hw
  · rw [mono_bin_bit hd] at hp hn
    have sep : (bit p a=true ∧ bit n a=false) ∨ (bit p b=true ∧ bit n b=false) := by
      by_cases op : d=0 <;> cases u : bit p a <;> cases v : bit n a <;> cases x : bit p b <;>
        cases y : bit n b <;> simp_all
    have eq : v=a ∨ v=b := by
      rcases sep with ⟨x,y⟩ | ⟨x,y⟩
      · exact Or.inl (h.2.2 a (by simp) x y).symm
      · exact Or.inr (h.2.2 b (by simp) x y).symm
    simp [gateMap,eq]
  · obtain rfl := h.2.2 w (by simp [hw]) hp hn
    have ne : ¬(w=a ∨ w=b) := fun eq => unused (gate_kept.mpr ⟨eq,hw⟩)
    simp [gateMap,ne]
theorem gate_share_eq {a b z U f v w} (hv : v∈gateList a b U)
    (eq : gateColor a b z U f v = gateColor a b z U f w) : v=w := by
  have bound := List.idxOf_lt_length_of_mem hv
  by_cases hw : w∈gateList a b U
  · simp only [gateColor,if_pos hv,if_pos hw] at eq
    exact (List.idxOf_inj hv).mp eq
  · simp only [gateColor,if_pos hv,if_neg hw] at eq
    omega
theorem gate_cross {a b d U T k p n na nb pa pb} (hd : allowed false d) (hab : a≠b)
    (run : Live false T k (insert (bin d a b) U)) (prev : Live false T (k+1) (insert a (insert b U)))
    (ua : a∉gateList a b U)
    (A : onlyWire (insert a (insert b U)) T a p na) (B : onlyWire (insert a (insert b U)) T b p nb)
    (C : onlyWire (insert a (insert b U)) T a pa n) (D : onlyWire (insert a (insert b U)) T b pb n) : False := by
  have Zp := (only_value run (gate_only hd ua C)).2.1
  have Zn := (only_value run (gate_only hd ua A)).2.2
  simp only [gateMap,true_or,ite_true,mono_bin_bit hd] at Zp Zn
  by_cases op : d=0
  · simp [op] at Zp
    exact hab (C.2.2 b (by simp) Zp.2 (only_value prev D).2.2).symm
  · simp [op] at Zn
    exact hab (A.2.2 b (by simp) (only_value prev B).2.1 Zn.2).symm
theorem order_live {k S T} (h : Live false T k S) :
    ∃ (count : Nat) (f : Sig → Nat), count+S.card ≤ k+2 ∧ (∀ v∈S, f v<count) ∧ orderLaw S T f := by
  induction k generalizing S with
  | zero =>
    obtain ⟨rfl,properT⟩ := h
    refine ⟨1,fun _ => 0,by simp,by simp,?_,by simp⟩
    intro a b p n na nb pa pb ne A B C D
    have e := (only_value (Live.stop (u:=false) properT) A).1
    have j := (only_value (Live.stop (u:=false) properT) B).1
    simp only [Finset.mem_singleton] at e j
    exact (ne (e.trans j.symm)).elim
  | succ k ih =>
    obtain ⟨U,a,b,d,hd,rfl,ha,hb,hab,fresh,tail⟩ := h
    let z := bin d a b
    let kept := gateList a b U
    have prev := Live.binary hd ha hb hab fresh tail
    obtain ⟨count,f,mass,bound,law⟩ := ih tail
    have hzu : z∉U := fun m => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem m))
    rw [Finset.card_insert_of_notMem hzu] at mass
    have size : kept.length + (insert a (insert b U)).card = U.card+2 := by
      by_cases x : a∈U <;> by_cases y : b∈U <;>
        simp [kept,gateList,x,y,hab,Finset.card_insert_of_notMem] <;> omega
    refine ⟨kept.length+count,gateColor a b z U f,by omega,?_,?_,?_⟩
    · intro v hv
      by_cases u : v∈kept
      · have m := List.idxOf_lt_length_of_mem u
        change (if v∈kept then kept.idxOf v else _) < _
        rw [if_pos u]
        omega
      · have m := bound _ (gate_mem (z:=z) hv)
        change (if v∈kept then kept.idxOf v else _) < _
        rw [if_neg u]
        exact Nat.add_lt_add_left m _
    · intro v w p n na nb pa pb vw A B C D eq
      have uv : v∉kept := fun u => vw (gate_share_eq u eq)
      have uw : w∉kept := fun u => vw (gate_share_eq u eq.symm).symm
      have same : f (gateMap a b z v) = f (gateMap a b z w) := by
        change (if v∈kept then _ else kept.length+_) = (if w∈kept then _ else kept.length+_) at eq
        rw [if_neg uv,if_neg uw] at eq
        omega
      by_cases ne : gateMap a b z v ≠ gateMap a b z w
      · exact law.1 ne (gate_only hd uv A) (gate_only hd uw B)
          (gate_only hd uv C) (gate_only hd uw D) same
      · have vS := (only_value prev A).1
        have wS := (only_value prev B).1
        have vz : v≠z := fun e => fresh (show z∈_ from e ▸ vS)
        have wz : w≠z := fun e => fresh (show z∈_ from e ▸ wS)
        have pair : (v=a ∧ w=b) ∨ (v=b ∧ w=a) := by
          by_cases va : v=a ∨ v=b <;> by_cases wa : w=a ∨ w=b <;> simp_all [gateMap] <;> grind
        rcases pair with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
        · exact gate_cross hd hab tail prev uv A B C D
        · exact gate_cross hd hab tail prev uw B A D C
    · intro v w t p n na pb A B C eq
      have ident (e : v=w) : t=v := by
        subst w
        exact (C.2.2 v (only_value prev A).1 (only_value prev A).2.1 (only_value prev B).2.2).symm
      by_cases uv : v∈kept
      · rw [ident (gate_share_eq uv eq)]
      by_cases uw : w∈kept
      · rw [ident (gate_share_eq uw eq.symm).symm]
      have same : f (gateMap a b z v) = f (gateMap a b z w) := by
        change (if v∈kept then _ else kept.length+_) = (if w∈kept then _ else kept.length+_) at eq
        rw [if_neg uv,if_neg uw] at eq
        omega
      change (if t∈kept then kept.idxOf t else kept.length+_) ≤ (if v∈kept then _ else kept.length+_)
      rw [if_neg uv]
      by_cases ut : t∈kept
      · rw [if_pos ut]
        have lim := List.idxOf_lt_length_of_mem ut
        omega
      · rw [if_neg ut]
        exact Nat.add_le_add_left (law.2 (gate_only hd uv A) (gate_only hd uw B) (gate_only hd ut C) same) _
def rankRule (d : Nat) (f : Fin 10 → Nat) : Prop :=
  let v := fun j => f (colorField d j)
  if d.testBit 0 then v 0 ≠ v 1 else v 0=v 1 → v 2≤v 0
theorem rank_rule {ws T names d f} (h : colorRule ws T names d=true)
    (law : orderLaw ws.toFinset T f) :
    rankRule d (fun i => f (colorWire ws names i)) := by
  by_cases flag : d.testBit 0=true
  · simp only [rankRule,colorRule,flag,ite_true,Bool.and_eq_true,decide_eq_true_eq] at h ⊢
    exact law.1 h.1.2 (kwWireB_sound h.2.1.1.1) (kwWireB_sound h.2.1.1.2)
      (kwWireB_sound h.2.1.2) (kwWireB_sound h.2.2)
  · simp only [rankRule,colorRule,if_neg flag,Bool.and_eq_true] at h ⊢
    exact law.2 (kwWireB_sound h.1.1) (kwWireB_sound h.1.2) (kwWireB_sound h.2)
def layerCovers (lo : Nat) (f : Fin 10 → Nat) (t : Nat) :=
  ∀ i, f i<t → lo.testBit i.val=true
def layerBits (lo : Nat) (f : Fin 10 → Nat) (t : Nat) (i : Fin 10) :=
  !lo.testBit i.val && decide (f i=t)
def layerRule (lo d : Nat) : Sig :=
  let x := fun j => inputs.getD (colorField d j).val zero
  let pair := neg (prime false (x 0) (x 1))
  if d.testBit 0 then pair else
    if lo.testBit (colorField d 2).val then one else prime true pair (x 2)
theorem layer_rule {lo d f t} (h : rankRule d f) (cov : layerCovers lo f t) :
    bit (colorPoint (layerBits lo f t)) (layerRule lo d)=true := by
  have eval (j) := color_bit (layerBits lo f t) (colorField d j)
  by_cases flag : d.testBit 0=true
  · simp only [rankRule,flag,ite_true] at h
    simp only [layerRule,flag,ite_true,bit_neg,bit_prime,Bool.false_eq_true,ite_false,eval]
    cases x : layerBits lo f t (colorField d 0) <;> cases y : layerBits lo f t (colorField d 1) <;> simp_all
    simp only [layerBits,Bool.and_eq_true,decide_eq_true_eq] at x y
    exact h (x.2.trans y.2.symm)
  · simp only [rankRule,if_neg flag] at h
    simp only [layerRule,if_neg flag]
    by_cases old : lo.testBit (colorField d 2).val=true
    · rw [if_pos old,bit_one]
    · rw [if_neg old]
      simp only [bit_prime,ite_true,bit_neg,Bool.false_eq_true,ite_false,eval]
      cases x : layerBits lo f t (colorField d 0) <;> cases y : layerBits lo f t (colorField d 1) <;> simp_all
      simp only [layerBits,Bool.and_eq_true,decide_eq_true_eq] at x y
      have le := h (x.2.trans y.2.symm)
      have ge : ¬ f (colorField d 2)<t := by
        intro lt
        have hit := cov _ lt
        simp [old] at hit
      simp [layerBits,old,show f (colorField d 2)=t by omega]
def layerWords (lo : Nat) : List Nat → Sig
  | [] => one
  | d::ds => prime false (layerRule lo d) (layerWords lo ds)
theorem layer_words {lo f t} (ds : List Nat) (h : ∀d∈ds, rankRule d f) (cov : layerCovers lo f t) :
    bit (colorPoint (layerBits lo f t)) (layerWords lo ds)=true := by
  induction ds with
  | nil => exact bit_one _
  | cons d ds ih =>
    rw [layerWords,bit_prime,layer_rule (h d (by simp)) cov,ih (fun e he => h e (by simp [he]))]
    rfl
def cubeParts (mask : Nat) : List (Fin 10) → Sig
  | [] => one
  | i::is => if mask.testBit i.val then cubeParts mask is else
      prime false (neg (inputs.getD i.val zero)) (cubeParts mask is)
theorem cube_parts {x : Fin 10 → Bool} (mask : Nat) (is : List (Fin 10))
    (h : bit (colorPoint x) (cubeParts mask is)=true) :
    ∀ i∈is, x i=true → mask.testBit i.val=true := by
  induction is with
  | nil => simp
  | cons j js ih =>
    by_cases hm : mask.testBit j.val=true
    · rw [cubeParts,if_pos hm] at h
      intro i hi hx
      rcases List.mem_cons.mp hi with rfl | hi
      · exact hm
      · exact ih h i hi hx
    · rw [cubeParts,if_neg hm,bit_prime,bit_neg,color_bit] at h
      simp only [Bool.false_eq_true,ite_false,Bool.and_eq_true,Bool.not_eq_true'] at h
      intro i hi hx
      rcases List.mem_cons.mp hi with rfl | hi
      · simp_all
      · exact ih h.2 i hi hx
def cubeWord (mask : Nat) := cubeParts mask (List.finRange 10)
def layerUpper (lo : Nat) : List Nat → Sig
  | [] => zero
  | a::as => if lo &&& a = lo then prime true (cubeWord a) (layerUpper lo as) else layerUpper lo as
theorem upper_choice {lo f t} (as : List Nat) (cov : layerCovers lo f t)
    (ok : bit (colorPoint (layerBits lo f t)) (layerUpper lo as)=true) :
    ∃ a∈as, layerCovers a f (t+1) := by
  induction as with
  | nil => rw [layerUpper,bit_zero] at ok; contradiction
  | cons a as ih =>
    have follow (h : bit (colorPoint (layerBits lo f t)) (layerUpper lo as)=true) : ∃ v∈a::as, layerCovers v f (t+1) := by
      obtain ⟨v,hv,cv⟩ := ih h
      exact ⟨v,List.mem_cons_of_mem _ hv,cv⟩
    by_cases sub : lo &&& a=lo
    · rw [layerUpper,if_pos sub,bit_prime] at ok
      rcases Bool.or_eq_true_iff.mp ok with hit | tail
      · refine ⟨a,by simp,?_⟩
        intro i hi
        by_cases old : lo.testBit i.val=true
        · have z := congrArg (fun v : Nat => v.testBit i.val) sub
          simpa only [Nat.testBit_and,old,Bool.true_and] using z
        · have ge : ¬ f i<t := fun lt => old (cov i lt)
          have yes : layerBits lo f t i=true := by simp [layerBits,old,show f i=t by omega]
          exact cube_parts a (List.finRange 10) hit i (by simp) yes
      · exact follow tail
    · rw [layerUpper,if_neg sub] at ok
      exact follow ok
def layerStep (ds : List Nat) (lo : Nat) (hi : List Nat) :=
  (prime false (layerWords lo ds) (neg (layerUpper lo hi)) == zero)
theorem layer_step {ds lo hi f t} (laws : ∀d∈ds,rankRule d f) (cov : layerCovers lo f t)
    (ok : layerStep ds lo hi=true) : ∃ a∈hi, layerCovers a f (t+1) := by
  have eq := beq_iff_eq.mp ok
  have chk := congrArg (bit (colorPoint (layerBits lo f t))) eq
  rw [bit_prime,bit_neg,bit_zero,layer_words ds laws cov] at chk
  apply upper_choice hi cov
  simpa using chk
def finalPair (lo d : Nat) := d.testBit 0 && !lo.testBit (colorField d 0).val && !lo.testBit (colorField d 1).val
def layerScan (ds lo : List Nat) : List (List Nat) → Bool
  | [] => lo.all fun a => ds.any (finalPair a)
  | hi::tail => (lo.all fun a => layerStep ds a hi) && layerScan ds hi tail
theorem layer_scan {ds f} (laws : ∀d∈ds,rankRule d f) (ls : List (List Nat))
    {lo t} (covered : ∃a∈lo,layerCovers a f t) (bound : ∀i, f i<t+ls.length+1)
    (ok : layerScan ds lo ls=true) : False := by
  induction ls generalizing lo t with
  | nil =>
    obtain ⟨a,ha,ca⟩ := covered
    obtain ⟨d,hd,yes⟩ := List.any_eq_true.mp (List.all_eq_true.mp ok a ha)
    simp only [finalPair,Bool.and_eq_true,Bool.not_eq_true'] at yes
    have top (i : Fin 10) (no : a.testBit i.val=false) : f i=t := by
      have small : f i<t+1 := by simpa using bound i
      have big : ¬ f i<t := by intro lt; have hh := ca i lt; simp [no] at hh
      omega
    have diff := laws d hd
    simp only [rankRule,yes.1.1,ite_true] at diff
    exact diff ((top _ yes.1.2).trans (top _ yes.2).symm)
  | cons l ls ih =>
    obtain ⟨a,ha,ca⟩ := covered
    have both := Bool.and_eq_true_iff.mp ok
    apply ih (t:=t+1) (layer_step laws ca (List.all_eq_true.mp both.1 a ha)) _ both.2
    intro i
    have z := bound i
    simp only [List.length_cons] at z
    omega
abbrev OrderPage := Nat × List Nat × Nat × List (List Nat)
def orderCheck (ws : List Sig) (T : Sig) (k : Nat) (book : OrderPage) :=
  let (names,ds,start,ls) := book
  decide (k+2 ≤ ws.toFinset.card+ls.length+1) &&
    (List.finRange 10).all (fun i => decide (colorWire ws names i ∈ ws)) &&
    ds.all (colorRule ws T names) && layerScan ds [start] ls
theorem order_sound {ws T k page} (ok : orderCheck ws T k page=true) : Impossible false T k ws.toFinset := by
  rcases page with ⟨names,ds,start,ls⟩
  simp only [orderCheck,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true] at ok
  intro n le run
  obtain ⟨count,f,mass,bound,law⟩ := order_live run
  apply layer_scan (f:=fun i => f (colorWire ws names i)) (fun d hd => rank_rule (ok.1.2 d hd) law)
    ls (t:=0) (lo:=[start]) ⟨start,by simp,by simp [layerCovers]⟩ _ ok.2
  intro i
  have use := (ok.1.1.2 _ (List.mem_finRange i))
  have less := bound _ (List.mem_toFinset.mpr use)
  have size := ok.1.1.1
  omega
def orderRange (g : Forest) (k a n : Nat) (pages : Nat → OrderPage) :=
  (List.range n).all fun i => orderCheck (stateSet g k (a+i)) (targetOf g) k (pages i)
theorem orderCut {g k a n pages} (mode : g.mode=false) (ok : orderRange g k a n pages=true) :
    CutRow g k a n := by
  intro j lo hi
  right
  rw [mode]
  have hh := List.all_eq_true.mp ok (j-a) (List.mem_range.mpr (by omega))
  have eq : a+(j-a)=j := by omega
  change orderCheck (stateSet g k (a+(j-a))) _ _ _=true at hh
  rw [eq] at hh
  exact order_sound hh
def padColumn (n v : Nat) : Bits :=
  BitVec.ofNat 320 (v + if v % 2=1 then (1 <<< 320)-(1 <<< n) else 0)
theorem lowerHint {u raw T a b} (h : Lower u raw T a) (le : b ≤ a) : Lower u raw T b :=
  fun p bank hr hit => le.trans (h p bank hr hit)
def treeData (p n v : Nat) :=
  let row := fun base i => (base >>> (10*((v >>> (8+5*i)) % 32))) % 1024
  v % 256 + (row p 0 <<< 8) + (row n 1 <<< 18) + (row n 2 <<< 28) +
    (row n 3 <<< 38) + (row p 4 <<< 48) + (row p 5 <<< 58)
def ruleData (p n v : Nat) :=
  let row := fun base i => (base >>> (10*((v >>> (13+5*i)) % 32))) % 1024
  v % 8192 + (row p 0 <<< 13) + (row n 1 <<< 23) + (row n 2 <<< 33) +
    (row (if v.testBit 0 then n else p) 3 <<< 43) + (row p 4 <<< 53) + (row p 5 <<< 63)
theorem countFace {u m L} (hints : Nat)
    (hp : properB (graphGoal m)=true)
    (ess : checkEssential (graphGoal m) (varsX m) (graphPairs m hints)=true)
    (enough : L ≤ (List.map Prod.fst (graphPairs m hints)).toFinset.card - 1) :
    Lower u (varsX m) (graphGoal m) L :=
  lowerHint (lower_count (proper_of _ hp) (graphPairs m hints) ess) enough
theorem dropFace {u m q a L} (fixed hints : Nat) (prior : Lower u (varsX q) (graphGoal q) a)
    (mapped : checkLift (fixRows fixed 0) (graphGoal m) (varsX m) (varsX q) (graphGoal q) (graphPairs fixed hints)=true)
    (hm : properB (graphGoal m)=true) (hq : properB (graphGoal q)=true)
    (enough : L ≤ a + (List.map Prod.fst (graphPairs fixed hints)).toFinset.card) :
    Lower u (varsX m) (graphGoal m) L :=
  lowerHint (lift_ok mapped (proper_of _ hm) (proper_of _ hq) prior) enough
abbrev Face (u : Bool) (m L : Nat) := Lower u (varsX m) (graphGoal m) L
def tableWord (xs : Array Nat) (i : Nat) := xs.getD (i%8) 0
def tablePair (xs : Array (Nat × Nat)) (i : Nat) := xs.getD (i%8) (0,0)
def tableBits (xs : Array (Bits × Bits)) (i : Nat) := xs.getD (i%8) (0,0)
def readRules (pos neg width : Nat) (rules : Nat → Nat) : Nat → Nat → List Nat
  | 0,_ => []
  | n+1,v => ruleData pos neg (rules (v % (1 <<< width))) :: readRules pos neg width rules n (v >>> width)
def readPanel (pos neg rw pw : Nat) (rules programs : Nat → Nat) (rec : Nat) :=
  let program := programs (rec % (1 <<< pw))
  (rec >>> pw,readRules pos neg rw rules (program % 16) (program >>> 4))
theorem consFace {u m L es} (h : Face u m L) (tail : Known u es) : Known u ((m,L)::es) := by
  intro e he
  rcases List.mem_cons.mp he with rfl | h'
  · exact h
  · exact tail e h'
def smallSlot (h buckets slots iw pw : Nat) (disp slotsAt : Nat → Nat) : Option (Nat × Nat) :=
  let slot := (h/buckets+disp (h%buckets))%slots
  let val := slotsAt slot
  if val=0 || (val >>> (iw+pw)) != (h/(buckets*slots))%8 then none
  else some (val % (1 <<< iw)-1,(val >>> iw)%(1 <<< pw))
def variableSlot (blocks : Nat → Nat × Nat) (i : Nat) :=
  let b := blocks (i/16)
  let offsets := b.1 >>> (12*(i%16))
  let start := offsets % 4096
  (b.2 >>> start) % (1 <<< ((offsets >>> 12)%4096 - start))
def bookData (d fw mw : Nat) (fronts masks codes costs : Nat → Nat) (j : Nat) :=
  let i := j/2
  if j%2=1 then costs i else
    let code := codes i
    fronts (code % (1 <<< fw)) + ((code >>> (fw+mw)) <<< (12*(d-1))) +
      (masks ((code >>> fw)%(1 <<< mw)) <<< (12*d))
noncomputable def bandTest (g : Forest) (k a n ar : Nat) :=
  header g k a n ar && rowCut g k a n ar 0 ar
theorem bandTest_sound {g k a n ar} (ok : bandTest g k a n ar=true) :
    block g k a n=true :=
  cutsBlock (Bool.and_eq_true_iff.mp ok).1 (Bool.and_eq_true_iff.mp ok).2
noncomputable def bandCells (g : Forest) (k a n ar : Nat) (splitBand : Bool) :=
  if splitBand then bandTest g k a (n/2) ar && bandTest g k (a+n/2) (n-n/2) ar
  else bandTest g k a n ar
theorem bandCut {g k a n} (ar : Nat) (splitBand : Bool) (ok : bandCells g k a n ar splitBand=true) :
    CutRow g k a n := by
  apply checkedRow
  cases splitBand
  · exact bandTest_sound ok
  · have both := Bool.and_eq_true_iff.mp ok
    have all := block_merge (bandTest_sound both.1) (bandTest_sound both.2)
    simpa only [Nat.add_sub_of_le (Nat.div_le_self n 2)] using all
def readGroup (n pad : Nat) : Nat → Nat → List Nat
  | 0,_ => []
  | s+1,x => (pad+x % (1 <<< n)) :: readGroup n pad s (x >>> n)
def readGroups (n pad : Nat) : Nat → Nat → List (List Nat)
  | 0,_ => []
  | s+1,x =>
    let len := x % 64
    readGroup n pad len (x >>> 6) :: readGroups n pad s (x >>> (6+n*len))
def orderPage (pos neg w : Nat) (bank : Nat → Nat) (n q names clauses groups : Nat) : OrderPage :=
  let pad := 1024-(1 <<< n)
  (names,readRules pos neg w bank (clauses % 128) (clauses >>> 7),pad,readGroups n pad (q-1) groups)

theorem h6_1 : Face true 6 1 := countFace 288 (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem h12_1 : Face true 12 1 := carry_of (swaps:=[33,49]) (by decide +kernel) h6_1
theorem h14_2 : Face true 14 2 := countFace 8480 (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem h17_1 : Face true 17 1 := carry_of (swaps:=[66,50,16]) (by decide +kernel) h6_1
theorem h24_1 : Face true 24 1 := carry_of (swaps:=[66,49]) (by decide +kernel) h6_1
theorem h28_2 : Face true 28 2 := carry_of (swaps:=[50,33,65]) (by decide +kernel) h14_2

namespace B29_4
def entries : List (Nat × Nat) := []
theorem prior : Known true entries := (known_down baseKnown)
def samples : Nat → Bits × Bits := (fun i => (if i<8 then tableBits #[(padColumn 20 0xe0ef0,padColumn 20 0xabad0),(padColumn 20 0x0,padColumn 20 0x0),(padColumn 20 0x7dc3,padColumn 20 0x75d81),(padColumn 20 0x1f3cf,padColumn 20 0x8a246),(padColumn 20 0xf8f3c,padColumn 20 0x54528),(padColumn 20 0x0,padColumn 20 0x0),(padColumn 20 0x0,padColumn 20 0x0),(padColumn 20 0x0,padColumn 20 0x0)] i else tableBits #[(padColumn 20 0x0,padColumn 20 0x0),(padColumn 20 0x0,padColumn 20 0x0)] i))
def cols : List ColumnInfo := []
def data3 : Nat → Nat := (fun i => tableWord #[0xf,0x0] i)
def levels : Nat → Packing
  | 3 => (1,0,1,0,0,0,0,data3)
  | _ => (0,0,0,0,0,0,0,fun _ => 0)
def index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def book : Forest := ⟨29,3,samples,cols,[[],[32,67]],levels,index⟩
theorem geometry : graphValid book (boundsBefore entries) = true := by decide +kernel
set_option maxRecDepth 16000 in
theorem row3_0 : CutRow book 3 0 1 := bandCut 4 false (by decide +kernel)
theorem band3 : CutRow book 3 0 1 := row3_0
theorem checked : mixedTables book 3 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact band3
end B29_4
theorem h29_4 : Face true 29 4 :=
  mixedLower (g:=B29_4.book) (i:=0) (hints:=8964)
    (before_sound B29_4.entries B29_4.prior) B29_4.geometry B29_4.checked
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem h30_4 : Face true 30 4 := carry_of (swaps:=[66,16]) (by decide +kernel) h29_4
theorem h33_1 : Face true 33 1 := carry_of (swaps:=[82,66,50,16]) (by decide +kernel) h6_1
theorem h49_2 : Face true 49 2 := carry_of (swaps:=[83,65,16,32]) (by decide +kernel) h14_2
theorem h57_4 : Face true 57 4 := carry_of (swaps:=[82,48]) (by decide +kernel) h29_4

namespace B63_7
def entries : List (Nat × Nat) := [(29,4),(30,4),(57,4)]
theorem prior : Known true entries := (consFace h29_4 (consFace h30_4 (consFace h57_4 (known_down baseKnown))))
def samples : Nat → Bits × Bits := (fun i => (if i<8 then tableBits #[(padColumn 82 0x93fffe00003ff8460fc0,padColumn 82 0x1caaa0860ea50460d40),(padColumn 82 0x17fc000001fc31981fc03,padColumn 82 0x7fc186308b4319815801),(padColumn 82 0x3a4400007ffcc603ffc0f,padColumn 82 0x380061843348c602ca406),(padColumn 82 0x24fc001ffe03007fe103c,padColumn 82 0xfd8209cc13005521018),(padColumn 82 0x3f8807ff80000ffc860f0,padColumn 82 0x3f02055610600aa8860a0),(padColumn 82 0x3ff3f8000003f86318300,padColumn 82 0x3fe354186181586318200),(padColumn 82 0x0,padColumn 82 0x0),(padColumn 82 0x0,padColumn 82 0x0)] i else tableBits #[(padColumn 82 0x0,padColumn 82 0x0),(padColumn 82 0x0,padColumn 82 0x0)] i))
def cols : List ColumnInfo := [(1,32,30,0,4),(4,2,57,0,4),(34,0,29,0,4)]
def data6 : Nat → Nat := (fun i => tableWord #[0x3f,0x603] i)
def levels : Nat → Packing
  | 6 => (1,0,2,0,0,0,0,data6)
  | _ => (0,0,0,0,0,0,0,fun _ => 0)
def index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def book : Forest := ⟨63,6,samples,cols,[[],[32,81,67]],levels,index⟩
theorem geometry : graphValid book (boundsBefore entries) = true := by decide +kernel
set_option maxRecDepth 16000 in
theorem row6_0 : CutRow book 6 0 1 := bandCut 6 false (by decide +kernel)
theorem band6 : CutRow book 6 0 1 := row6_0
theorem checked : mixedTables book 6 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact band6
end B63_7
theorem h63_7 : Face true 63 7 :=
  mixedLower (g:=B63_7.book) (i:=0) (hints:=8484)
    (before_sound B63_7.entries B63_7.prior) B63_7.geometry B63_7.checked
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem h66_1 : Face true 66 1 := carry_of (swaps:=[98,82,66,50]) (by decide +kernel) h6_1
theorem h70_2 : Face true 70 2 := carry_of (swaps:=[99,83,67,33]) (by decide +kernel) h14_2
theorem h78_4 : Face true 78 4 := carry_of (swaps:=[98,82,66,48,16]) (by decide +kernel) h29_4
theorem h95_7 : Face true 95 7 := carry_of (swaps:=[101,66,16]) (by decide +kernel) h63_7
theorem h132_1 : Face true 132 1 := carry_of (swaps:=[114,98,82,66,33,49]) (by decide +kernel) h6_1
theorem h164_2 : Face true 164 2 := carry_of (swaps:=[114,98,83,33,65]) (by decide +kernel) h14_2
theorem h165_4 : Face true 165 4 := carry_of (swaps:=[115,67,100,83]) (by decide +kernel) h29_4
theorem h166_4 : Face true 166 4 := carry_of (swaps:=[115,50,98,83,66,16]) (by decide +kernel) h29_4
theorem h156_4 : Face true 156 4 := carry_of (swaps:=[114,98,32,66,50,80,16]) (by decide +kernel) h29_4
theorem h172_4 : Face true 172 4 := carry_of (swaps:=[115,50,98,48,66,80,16]) (by decide +kernel) h29_4
theorem h177_4 : Face true 177 4 := carry_of (swaps:=[114,50,99,82,64]) (by decide +kernel) h29_4

namespace B189_8
def entries : List (Nat × Nat) := [(29,4),(57,4),(156,4),(165,4),(172,4),(177,4)]
theorem prior : Known true entries := (consFace h29_4 (consFace h57_4 (consFace h156_4 (consFace h165_4 (consFace h172_4 (consFace h177_4 (known_down baseKnown)))))))
def samples : Nat → Bits × Bits := (fun i => (if i<8 then tableBits #[(padColumn 84 0xe4003ffc00007ff8430f0,padColumn 84 0xe010e55410c07a9043050),(padColumn 84 0x0,padColumn 84 0x0),(padColumn 84 0x3c0fc0000fc3e3183f303,padColumn 84 0x1c2a430c2343431816101),(padColumn 84 0xe8000003ffcc0c07ff00f,padColumn 84 0xe0c10c115c8c0c0569006),(padColumn 84 0x5c0000fff03180ffc403c,padColumn 84 0x1f0610aaa131806a84028),(padColumn 84 0x9ff03f00003e1f2198cc0,padColumn 84 0x1d681a20c62a052198480),(padColumn 84 0x0,padColumn 84 0x0),(padColumn 84 0xf3ffc000003ff0c620f00,padColumn 84 0xe295a0c30814b0c620a00)] i else tableBits #[(padColumn 84 0x0,padColumn 84 0x0),(padColumn 84 0x0,padColumn 84 0x0)] i))
def cols : List ColumnInfo := [(12,0,177,0,4),(17,0,172,0,4),(24,0,165,0,4),(33,0,156,0,4),(132,0,57,0,4),(160,0,29,0,4)]
def data7 : Nat → Nat := (fun i => tableWord #[0x3f,0x171506] i)
def data6 : Nat → Nat := (fun i => tableWord #[0x7f420,0x0,0x7f440,0x201] i)
def data5 : Nat → Nat := (fun i => tableWord #[0xb7cc3440,0x0] i)
def levels : Nat → Packing
  | 5 => (1,2,3,0,0,0,0,data5)
  | 6 => (2,1,3,0,0,0,0,data6)
  | 7 => (1,0,3,0,0,0,0,data7)
  | _ => (0,0,0,0,0,0,0,fun _ => 0)
def index : Nat → Nat → Option (Nat × Nat)
  | 6 => fun v => (if v=7502621870530246385 then some (0,0) else none)
  | 7 => fun h => smallSlot h 4 14 2 4 (fun i => ((fun i => tableWord #[0x2000] i) (i/16) >>> (4*(i%16))) % 16) (fun i => ((fun i => tableWord #[0xa200000010346416663cd6000009cca] i) (i/16) >>> (9*(i%16))) % 512)
  | _ => fun _ => none
def book : Forest := ⟨189,7,samples,cols,[[],[115,84],[32,67,117],[32,83,116],[48,82],[48,82,112,66],[64,114,50,48,80],[64,114,83],[80,50,116],[80,50,66,32,114],[112,66],[112,66,48,82]],levels,index⟩
theorem geometry : graphValid book (boundsBefore entries) = true := by decide +kernel
set_option maxRecDepth 16000 in
theorem row7_0 : CutRow book 7 0 1 := bandCut 6 false (by decide +kernel)
theorem band7 : CutRow book 7 0 1 := row7_0
set_option maxRecDepth 16000 in
theorem row6_0 : CutRow book 6 0 2 := bandCut 7 false (by decide +kernel)
theorem band6 : CutRow book 6 0 2 := row6_0
set_option maxRecDepth 16000 in
theorem row5_0 : CutRow book 5 0 1 := bandCut 6 false (by decide +kernel)
theorem band5 : CutRow book 5 0 1 := row5_0
theorem checked : mixedTables book 7 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact band5
  · exact band6
  · exact band7
end B189_8
theorem h189_8 : Face true 189 8 :=
  mixedLower (g:=B189_8.book) (i:=0) (hints:=536879876)
    (before_sound B189_8.entries B189_8.prior) B189_8.geometry B189_8.checked
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem h198_4 : Face true 198 4 := carry_of (swaps:=[114,96,82,50,64,16]) (by decide +kernel) h29_4
theorem h231_7 : Face true 231 7 := carry_of (swaps:=[83,82,114,99,66,16]) (by decide +kernel) h63_7
theorem h183_7 : Face true 183 7 := carry_of (swaps:=[115,84,99]) (by decide +kernel) h63_7

namespace B190_7
def entries : List (Nat × Nat) := [(30,4),(156,4),(166,4)]
theorem prior : Known true entries := (consFace h30_4 (consFace h156_4 (consFace h166_4 (known_down baseKnown))))
def samples : Nat → Bits × Bits := (fun i => (if i<8 then tableBits #[(padColumn 80 0x0,padColumn 80 0x0),(padColumn 80 0xfcfe000001f86030fc03,padColumn 80 0xfc7e0c20c3586030d401),(padColumn 80 0x279203e03ff81c0ffccf,padColumn 80 0x38012810ca018052846),(padColumn 80 0x5d2e001ffe0183ff043c,padColumn 80 0x1c0e604a720982aa0418),(padColumn 80 0xebf4001fc0060ff11830,padColumn 80 0xe3f1819584360d511820),(padColumn 80 0x93fffc000007f0c66300,padColumn 80 0x3feb60618c550c66100),(padColumn 80 0x0,padColumn 80 0x0),(padColumn 80 0xfe49ffe00007ff0883c0,padColumn 80 0xfc0149782102a7088280)] i else tableBits #[(padColumn 80 0x0,padColumn 80 0x0),(padColumn 80 0x0,padColumn 80 0x0)] i))
def cols : List ColumnInfo := [(8,16,166,0,4),(24,0,166,0,4),(34,0,156,0,4),(128,32,30,0,4),(160,0,30,0,4)]
def data6 : Nat → Nat := (fun i => tableWord #[0x3f,0x4cc05] i)
def data5 : Nat → Nat := (fun i => tableWord #[0x7ec20,0x0] i)
def levels : Nat → Packing
  | 5 => (1,1,3,0,0,0,0,data5)
  | 6 => (1,0,3,0,0,0,0,data6)
  | _ => (0,0,0,0,0,0,0,fun _ => 0)
def index : Nat → Nat → Option (Nat × Nat)
  | 6 => fun v => (if v=7689521405595769300 then some (0,0) else none)
  | _ => fun _ => none
def book : Forest := ⟨190,6,samples,cols,[[],[115,84]],levels,index⟩
theorem geometry : graphValid book (boundsBefore entries) = true := by decide +kernel
set_option maxRecDepth 16000 in
theorem row6_0 : CutRow book 6 0 1 := bandCut 6 false (by decide +kernel)
theorem band6 : CutRow book 6 0 1 := row6_0
set_option maxRecDepth 16000 in
theorem row5_0 : CutRow book 5 0 1 := bandCut 6 false (by decide +kernel)
theorem band5 : CutRow book 5 0 1 := row5_0
theorem checked : mixedTables book 6 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact band5
  · exact band6
end B190_7
theorem h190_7 : Face true 190 7 :=
  mixedLower (g:=B190_7.book) (i:=0) (hints:=544416032)
    (before_sound B190_7.entries B190_7.prior) B190_7.geometry B190_7.checked
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem h222_7 : Face true 222 7 := carry_of (swaps:=[101,113]) (by decide +kernel) h190_7
theorem h238_7 : Face true 238 7 := carry_of (swaps:=[84,100,49,113]) (by decide +kernel) h190_7

namespace B255_11
def entries : List (Nat × Nat) := [(29,4),(30,4),(57,4),(63,7),(78,4),(95,7),(166,4),(177,4),(183,7),(189,8),(190,7),(198,4),(222,7),(231,7),(238,7)]
theorem prior : Known true entries := (consFace h29_4 (consFace h30_4 (consFace h57_4 (consFace h63_7 (consFace h78_4 (consFace h95_7 (consFace h166_4 (consFace h177_4 (consFace h183_7 (consFace h189_8 (consFace h190_7 (consFace h198_4 (consFace h222_7 (consFace h231_7 (consFace h238_7 (known_down baseKnown))))))))))))))))
def samples : Nat → Bits × Bits := (fun i => (if i<8 then tableBits #[(padColumn 248 0xf8787c3f888447fe210f80000001ffffe0000000000c03ffffc02060303c0,padColumn 248 0x78783c3f800003fe0007802030074aaaa0080c06000c03d55280206030140),(padColumn 248 0x1088fffc7910888425fff80000ffe0000000003fe0603ff0180c0c01ff0c03,padColumn 248 0x7ffc7800000001fff80c0455201806030125a0602aa0180c0c01560401),(padColumn 248 0x211108448f813fcbfe210801ff00000000007fffe01fc000603001ffff300f,padColumn 248 0x7803fc3fe000010d10080601804165a40168000603000aca91006),(padColumn 248 0x47f813ff8227d13c484ff8000000000001ffffc0018000c18003fffe04003c,padColumn 248 0x7f803ff8007c03c000ff8600803018020a9e980818000c18002ab52040018),(padColumn 248 0xfa227c8917fa03d09ff2100000000007ffff80000603030007fffe081800f0,padColumn 248 0xf8007c0007f803c01ff00180300c0205555602030603030002d554081800a0),(padColumn 248 0x8444211227fffc211fffa7fe00001ff8000000001fe40c0ff840303060c300,padColumn 248 0x7fffc001fff82b440300b5040180c0c15440c02a8403030604200),(padColumn 248 0xffffc22047ffffffe084400000ffe0000000000018183ff60180c0c0800c00,padColumn 248 0xffff800007ffffffe000060180aacc0180603010181815560180c0c0800800),(padColumn 248 0xfffffffffc442202110807ffff000000000000001ffff0080603010100f000,padColumn 248 0xfffffffff80000000000054b2ec01006018040200aa970080603010100a000)] i else tableBits #[(padColumn 248 0x0,padColumn 248 0x0),(padColumn 248 0x0,padColumn 248 0x0)] i))
def cols : List ColumnInfo := [(2,64,189,0,8),(66,0,189,0,8),(17,0,238,0,7),(24,0,231,0,7),(33,0,222,0,7),(65,0,190,0,7),(72,0,183,0,7),(160,0,95,0,7),(192,0,63,0,7),(41,16,198,0,4),(56,1,198,0,4),(57,0,198,0,4),(73,16,166,0,4),(78,0,177,0,4),(89,0,166,0,4),(176,1,78,0,4),(177,0,78,0,4),(193,32,30,0,4),(198,0,57,0,4),(225,0,30,0,4),(226,0,29,0,4)]
def data10 : Nat → Nat := (fun i => tableWord #[0xff,0x220ce106] i)
def data9 : Nat → Nat := (fun i => (if i<16 then (if i<8 then tableWord #[0x1ff440,0x2a014f04,0x1ff460,0xe038f04,0x1ff462,0xf44c40d05,0x1ff482,0x115200cc05] i else tableWord #[0x1ff4a3,0x202d103,0x1ff4e3,0xa48c80f18707,0x1ff4a4,0x53202d105,0x1ff862,0x83d14930cd08] i) else tableWord #[0x1ff882,0x321224d06,0x1ffc40,0x31c529206] i))
def data8 : Nat → Nat := (fun i => (if i<16 then (if i<8 then tableWord #[0x2efd04460,0x306102,0x2f7d03482,0x306102,0x2fed004a4,0x306102,0x2ef504c40,0x1201] i else tableWord #[0x3f7862460,0x18e02,0x3f74e3462,0x1401,0x2ff507462,0x0,0x2ffd07482,0x0] i) else tableWord #[0x2ffd024e3,0x6001] i))
def levels : Nat → Packing
  | 8 => (9,2,5,0,0,0,0,data8)
  | 9 => (10,1,5,0,0,0,0,data9)
  | 10 => (1,0,5,0,0,0,0,data10)
  | _ => (0,0,0,0,0,0,0,fun _ => 0)
def index : Nat → Nat → Option (Nat × Nat)
  | 9 => fun h => smallSlot h 5 17 4 1 (fun i => ((fun i => tableWord #[0x380c4] i) (i/16) >>> (5*(i%16))) % 32) (fun i => ((fun i => tableWord #[0xe502d4612369a708e6e4760000000000,0x0] i) (i/16) >>> (8*(i%16))) % 256)
  | 10 => fun h => smallSlot h 8 25 4 1 (fun i => ((fun i => tableWord #[0x10400180c1] i) (i/16) >>> (5*(i%16))) % 32) (fun i => ((fun i => tableWord #[0xd800000000e15265440043e92600a2,0x338a008708191594] i) (i/16) >>> (8*(i%16))) % 256)
  | _ => fun _ => none
def book : Forest := ⟨255,10,samples,cols,[[],[115,84]],levels,index⟩
theorem geometry : graphValid book (boundsBefore entries) = true := by decide +kernel
set_option maxRecDepth 16000 in
theorem row10_0 : CutRow book 10 0 1 := bandCut 8 false (by decide +kernel)
theorem band10 : CutRow book 10 0 1 := row10_0
set_option maxRecDepth 16000 in
theorem row9_0 : CutRow book 9 0 10 := bandCut 9 true (by decide +kernel)
theorem band9 : CutRow book 9 0 10 := row9_0
set_option maxRecDepth 16000 in
theorem row8_0 : CutRow book 8 0 4 := bandCut 8 false (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row8_4 : CutRow book 8 4 5 := bandCut 9 false (by decide +kernel)
theorem combine8_0_9 : CutRow book 8 0 9 := @joinRow book 8 0 4 5 row8_0 row8_4
theorem band8 : CutRow book 8 0 9 := combine8_0_9
theorem checked : mixedTables book 10 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact band8
  · exact band9
  · exact band10
end B255_11
theorem h255_11 : Face true 255 11 :=
  mixedLower (g:=B255_11.book) (i:=0) (hints:=553656612)
    (before_sound B255_11.entries B255_11.prior) B255_11.geometry B255_11.checked
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem h305_4 : Face true 305 4 := carry_of (swaps:=[130,114,50,99,82,64]) (by decide +kernel) h29_4
theorem h326_4 : Face true 326 4 := carry_of (swaps:=[130,50,115,98,83,32,64,16]) (by decide +kernel) h29_4
theorem h352_2 : Face true 352 2 := carry_of (swaps:=[130,33,113,99,82,65]) (by decide +kernel) h14_2
theorem h353_4 : Face true 353 4 := carry_of (swaps:=[131,50,66,116,99,82]) (by decide +kernel) h29_4
theorem h354_4 : Face true 354 4 := carry_of (swaps:=[131,67,116,99,82,16]) (by decide +kernel) h29_4
theorem h359_7 : Face true 359 7 := carry_of (swaps:=[131,67,116,99,82,16]) (by decide +kernel) h63_7
theorem h366_7 : Face true 366 7 := carry_of (swaps:=[128,64,116,49,96]) (by decide +kernel) h63_7
theorem h371_7 : Face true 371 7 := carry_of (swaps:=[131,84,115,98]) (by decide +kernel) h63_7
theorem h377_7 : Face true 377 7 := carry_of (swaps:=[128,80,84,66,16,114,97,48]) (by decide +kernel) h63_7
theorem h317_7 : Face true 317 7 := carry_of (swaps:=[133,117,80,48,50,33,97,64]) (by decide +kernel) h63_7
theorem h350_7 : Face true 350 7 := carry_of (swaps:=[133,117,50,65,96]) (by decide +kernel) h63_7

namespace B383_11
def entries : List (Nat × Nat) := [(57,4),(63,7),(78,4),(95,7),(317,7),(326,4),(350,7),(353,4),(354,4),(359,7),(366,7),(371,7),(377,7)]
theorem prior : Known true entries := (consFace h57_4 (consFace h63_7 (consFace h78_4 (consFace h95_7 (consFace h317_7 (consFace h326_4 (consFace h350_7 (consFace h353_4 (consFace h354_4 (consFace h359_7 (consFace h366_7 (consFace h371_7 (consFace h377_7 (known_down baseKnown))))))))))))))
def samples : Nat → Bits × Bits := (fun i => (if i<8 then tableBits #[(padColumn 248 0x87c3ffe22111ffc421f00000003ffffc0000000000180fffff0080c0303c0,padColumn 248 0x3c3ffe00000ffc000f0040300e955540100c03000180f554a0080c030140),(padColumn 248 0x17ffc03e44222084bfff00000ffc0000000003ff03007fc060303003ff0c03,padColumn 248 0x7ffc01e000000003fff01804aa40300c060112d03006a8060303002560401),(padColumn 248 0xf88447e3e04ff17fc421000000000000000fffff0c06000180c007ffff000f,padColumn 248 0xf80003e1e00ff07fc000060180100c03008566d20c06000180c00559a90006),(padColumn 248 0x213ffc4089f44f8909ff0000000000003ffffc0030180306000ffffc04003c,padColumn 248 0x3ffc0001f00f8001ff180600603004153a980430180306000aaaa4040018),(padColumn 248 0xffc88885fe80f213fe420000000000fffff00000c0600c001ffff8101800f0,padColumn 248 0xffc00001fe00f003fe006018018040aaaac02018c0600c000b5550101800a0),(padColumn 248 0x42111109ffff0423fff4ffc00003ff0000000000ff80303fe100c06060c300,padColumn 248 0x1ffff0003fff0aaa006016a080300c060aa80300aa100c060604200),(padColumn 248 0x84222211fffffffc1088003ffffc00000000000000ffffd806030180803c00,padColumn 248 0x1fffffffc0000802a955980300c03008000d5155806030180801800),(padColumn 248 0x0,padColumn 248 0x0)] i else tableBits #[(padColumn 248 0xffffffff110888422100fffff000000000000000ffffc020180c060300f000,padColumn 248 0xfffffffe0000000000005555680200c0300c0300552ac020180c060300a000),(padColumn 248 0x0,padColumn 248 0x0)] i))
def cols : List ColumnInfo := [(6,0,377,0,7),(12,0,371,0,7),(17,0,366,0,7),(24,0,359,0,7),(33,0,350,0,7),(66,0,317,0,7),(288,0,95,0,7),(320,0,63,0,7),(22,8,353,0,4),(29,0,354,0,4),(56,1,326,0,4),(57,0,326,0,4),(304,1,78,0,4),(324,2,57,0,4)]
def data10 : Nat → Nat := (fun i => tableWord #[0xff,0x1256034708] i)
def data9 : Nat → Nat := (fun i => tableWord #[0x1ff420,0x14d02,0x1ff440,0x12a02,0x1ff460,0x1b10b04] i)
def data8 : Nat → Nat := (fun i => tableWord #[0x2efd04460,0x0] i)
def levels : Nat → Packing
  | 8 => (1,2,4,0,0,0,0,data8)
  | 9 => (3,1,4,0,0,0,0,data9)
  | 10 => (1,0,4,0,0,0,0,data10)
  | _ => (0,0,0,0,0,0,0,fun _ => 0)
def index : Nat → Nat → Option (Nat × Nat)
  | 9 => fun v => (if v=9836245588253958792 then some (0,0) else none)
  | 10 => fun h => smallSlot h 13 44 2 4 (fun i => ((fun i => tableWord #[0xc0000000001000] i) (i/16) >>> (6*(i%16))) % 64) (fun i => ((fun i => tableWord #[0x23003de000051c9400000000061,0x96c760d27c1eb801320000000019e,0x23c00662d0039600f38018511] i) (i/16) >>> (9*(i%16))) % 512)
  | _ => fun _ => none
def book : Forest := ⟨383,10,samples,cols,[[],[98,131,84],[16,66,101],[16,82,131,100],[32,81,67,134],[32,81,128,99,65,67,64],[48,129,98,16,66,84],[48,129,82],[64,97,33,50,48,80,133],[64,97,130,83],[80,33,49,65,16,129,97],[80,33,99,132],[96,65,50,133],[96,65,32,83,129,49,50],[128,49,100],[128,49,66,16,82,98]],levels,index⟩
theorem geometry : graphValid book (boundsBefore entries) = true := by decide +kernel
set_option maxRecDepth 16000 in
theorem row10_0 : CutRow book 10 0 1 := bandCut 8 false (by decide +kernel)
theorem band10 : CutRow book 10 0 1 := row10_0
set_option maxRecDepth 16000 in
theorem row9_0 : CutRow book 9 0 3 := bandCut 9 false (by decide +kernel)
theorem band9 : CutRow book 9 0 3 := row9_0
set_option maxRecDepth 16000 in
theorem row8_0 : CutRow book 8 0 1 := bandCut 8 false (by decide +kernel)
theorem band8 : CutRow book 8 0 1 := row8_0
theorem checked : mixedTables book 10 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact band8
  · exact band9
  · exact band10
end B383_11
theorem h383_11 : Face true 383 11 :=
  mixedLower (g:=B383_11.book) (i:=0) (hints:=21491622180)
    (before_sound B383_11.entries B383_11.prior) B383_11.geometry B383_11.checked
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem h486_8 : Face true 486 8 := carry_of (swaps:=[115,83,82,130,99,66,16]) (by decide +kernel) h189_8
theorem h503_11 : Face true 503 11 := carry_of (swaps:=[115,82,98,131,66,16]) (by decide +kernel) h255_11
theorem h480_4 : Face true 480 4 := carry_of (swaps:=[32,48,132,115,98,80,16]) (by decide +kernel) h29_4
theorem h497_7 : Face true 497 7 := carry_of (swaps:=[113,82,129,98,16,48]) (by decide +kernel) h190_7
theorem h509_11 : Face true 509 11 := carry_of (swaps:=[82,48,66,129,112]) (by decide +kernel) h255_11
theorem h510_11 : Face true 510 11 := carry_of (swaps:=[84,100,49,113,128]) (by decide +kernel) h255_11

namespace B511_13
def entries : List (Nat × Nat) := [(29,4),(30,4),(63,7),(78,4),(95,7),(177,4),(189,8),(222,7),(231,7),(255,11),(305,4),(353,4),(371,7),(377,7),(383,11),(480,4),(486,8),(497,7),(503,11),(509,11),(510,11)]
theorem prior : Known true entries := (consFace h29_4 (consFace h30_4 (consFace h63_7 (consFace h78_4 (consFace h95_7 (consFace h177_4 (consFace h189_8 (consFace h222_7 (consFace h231_7 (consFace h255_11 (consFace h305_4 (consFace h353_4 (consFace h371_7 (consFace h377_7 (consFace h383_11 (consFace h480_4 (consFace h486_8 (consFace h497_7 (consFace h503_11 (consFace h509_11 (consFace h510_11 (known_down baseKnown))))))))))))))))))))))
def samples : Nat → Bits × Bits := (fun i => (if i<8 then tableBits #[(padColumn 320 0x3e1f0fe108210fff0820f800000000000003fffff8000000000000c0003007fffff00201803003c0,padColumn 320 0x3e0f0fe0000007ff0000780100300200c00f4aaaa8008030060000c0003007d554a0020180300140),(padColumn 320 0x43fff1e21042104117fff800000000003ffc00000000000ffe060000600ffe0180300c007ff00c03,padColumn 320 0x1fff1e00000000007fff80600400c012aa40180180300465a060000600d540180300c0055600401),(padColumn 320 0x8421123f009ff8bff8410800000001ffc000000000007ffffe1803001ff0000600c001fffff0300f,padColumn 320 0x1f001ff83ff8000018018010b44010060060042599a418030015a0000600c0012b2a901006),(padColumn 320 0xc04ffe0427e427c2209ff800000000000000000007fffff000600c0180001818000fffff8040003c,padColumn 320 0xc00ffe0007e007c0001ff860060060020060180082a9da6008600c0180001818000aaad480400018),(padColumn 320 0x9f2245ff900f904ffe21000000000000000007fffff80000180300600c060007ffffe02018000f0,padColumn 320 0x1f0001ff800f800ffe001801801800c01802055555600803180300600c060002b555402018000a0),(padColumn 320 0x1084489fffff0208ffffa7ff000ffe000003ff800000000001fe403fe10181ff8100300c060cc300,padColumn 320 0x1fffff0000ffff82aa2002b4100600b50100180300c15440154101802a8100300c06044200),(padColumn 320 0xff08811fffffffff01044000fff000003ffc0000000000000001ffd8060ffe600600c03008030c00,padColumn 320 0xfe00001fffffffff000002006a9600601558c00600600c0100016a980602aa600600c03008010800),(padColumn 320 0xffffffe84208401042080000000fffffc0000000000000000001803ffff60080180300401000f000,padColumn 320 0xffffffe00000000000000400c00d4b4b98010018018010020001802aaa560080180300401000a000)] i else tableBits #[(padColumn 320 0x2000001084108420841007fffff00000000000000000000001ffffe018080100600c0180600f0000,padColumn 320 0x55595680180200200600600600c00aa956018080100600c0180600a0000),(padColumn 320 0x0,padColumn 320 0x0)] i))
def cols : List ColumnInfo := [(1,0,510,0,11),(2,0,509,0,11),(8,0,503,0,11),(128,0,383,0,11),(256,0,255,0,11),(9,16,486,0,8),(25,0,486,0,8),(258,64,189,0,8),(322,0,189,0,8),(14,0,497,0,7),(134,0,377,0,7),(140,0,371,0,7),(280,0,231,0,7),(289,0,222,0,7),(416,0,95,0,7),(448,0,63,0,7),(31,0,480,0,4),(154,4,353,0,4),(202,4,305,0,4),(334,0,177,0,4),(401,32,78,0,4),(418,64,29,0,4),(449,32,30,0,4)]
def data12 : Nat → Nat := (fun i => tableWord #[0x1ff,0x1142438cc809] i)
def data11 : Nat → Nat := (fun i => tableWord #[0x3ff0a2,0x72051a7a0d24e09,0x3ff4a2,0x730f8248a18ce2a54560d,0x3ff8a2,0x528c3e090d9d058b0b] i)
def data10 : Nat → Nat := (fun i => tableWord #[0x57fd274a2,0x32601d9c89606,0x7dbca28a2,0xb2a4c80e05,0x77fd274a2,0x3c91403,0x5ff5258a2,0x3c91403] i)
def data9 : Nat → Nat := (fun i => tableWord #[0x97fd475258a2,0x0] i)
def levels : Nat → Packing
  | 9 => (1,3,5,0,0,0,0,data9)
  | 10 => (4,2,5,0,0,0,0,data10)
  | 11 => (3,1,5,0,0,0,0,data11)
  | 12 => (1,0,5,0,0,0,0,data12)
  | _ => (0,0,0,0,0,0,0,fun _ => 0)
def index : Nat → Nat → Option (Nat × Nat)
  | 10 => fun v => (if v=11369311757800862412 then some (0,0) else none)
  | 11 => fun v => (if v=11369311757800862412 then some (0,0) else (if v=11458423956265286981 then some (1,0) else (if v=12322638194242191766 then some (3,0) else (if v=12698024304231822181 then some (2,0) else none))))
  | 12 => fun v => (if v=11787858522310454322 then some (2,1) else (if v=12115950459901266192 then some (2,0) else (if v=12322638194242191766 then some (1,0) else (if v=13136768276869170638 then some (0,0) else none))))
  | _ => fun _ => none
def book : Forest := ⟨511,12,samples,cols,[[],[48,129,82],[16,82,131,100],[128,49,100]],levels,index⟩
theorem geometry : graphValid book (boundsBefore entries) = true := by decide +kernel
set_option maxRecDepth 16000 in
theorem row12_0 : CutRow book 12 0 1 := bandCut 9 false (by decide +kernel)
theorem band12 : CutRow book 12 0 1 := row12_0
set_option maxRecDepth 16000 in
theorem row11_0 : CutRow book 11 0 3 := bandCut 10 false (by decide +kernel)
theorem band11 : CutRow book 11 0 3 := row11_0
set_option maxRecDepth 16000 in
theorem row10_0 : CutRow book 10 0 2 := bandCut 9 false (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row10_2 : CutRow book 10 2 2 := bandCut 10 false (by decide +kernel)
theorem combine10_0_4 : CutRow book 10 0 4 := @joinRow book 10 0 2 2 row10_0 row10_2
theorem band10 : CutRow book 10 0 4 := combine10_0_4
set_option maxRecDepth 16000 in
theorem row9_0 : CutRow book 9 0 1 := bandCut 9 false (by decide +kernel)
theorem band9 : CutRow book 9 0 1 := row9_0
theorem checked : mixedTables book 12 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact band9
  · exact band10
  · exact band11
  · exact band12
end B511_13
theorem h511_13 : Face true 511 13 :=
  mixedLower (g:=B511_13.book) (i:=0) (hints:=22028493092)
    (before_sound B511_13.entries B511_13.prior) B511_13.geometry B511_13.checked
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem h528_1 : Face true 528 1 := carry_of (swaps:=[146,130,114,98,33,81,66,49]) (by decide +kernel) h6_1
theorem h576_1 : Face true 576 1 := carry_of (swaps:=[146,130,33,113,98,81,66,49]) (by decide +kernel) h6_1
theorem h593_4 : Face true 593 4 := carry_of (swaps:=[147,131,50,114,99,82]) (by decide +kernel) h29_4
theorem h599_7 : Face true 599 7 := carry_of (swaps:=[147,131,67,116,66,99,82,16]) (by decide +kernel) h63_7
theorem h606_8 : Face true 606 8 := carry_of (swaps:=[151,135,101,66,16]) (by decide +kernel) h189_8
theorem h657_4 : Face true 657 4 := carry_of (swaps:=[147,131,114,99,82]) (by decide +kernel) h29_4
theorem h540_4 : Face true 540 4 := carry_of (swaps:=[146,130,114,98,67,32,80,16]) (by decide +kernel) h29_4
theorem h652_4 : Face true 652 4 := carry_of (swaps:=[146,130,115,98,48,66,80,16]) (by decide +kernel) h29_4
theorem h660_4 : Face true 660 4 := carry_of (swaps:=[147,131,116,66,99,32,80,16]) (by decide +kernel) h29_4
theorem h664_4 : Face true 664 4 := carry_of (swaps:=[147,50,130,115,48,98,80,16]) (by decide +kernel) h29_4

namespace B668_7
def entries : List (Nat × Nat) := [(156,4),(540,4),(652,4),(660,4),(664,4)]
theorem prior : Known true entries := (consFace h156_4 (consFace h540_4 (consFace h652_4 (consFace h660_4 (consFace h664_4 (known_down baseKnown))))))
def samples : Nat → Bits × Bits := (fun i => (if i<8 then tableBits #[(padColumn 45 0x0,padColumn 45 0x0),(padColumn 45 0x0,padColumn 45 0x0),(padColumn 45 0x1e1e3e3c33,padColumn 45 0x2742a3c2411),(padColumn 45 0x1ff81fc0f,padColumn 45 0xc8355819806),(padColumn 45 0x1e1e077c4cc,padColumn 45 0x112ca2664448),(padColumn 45 0x0,padColumn 45 0x0),(padColumn 45 0x0,padColumn 45 0x0),(padColumn 45 0x1e1e01cecb30,padColumn 45 0x150ac542c920)] i else tableBits #[(padColumn 45 0x0,padColumn 45 0x0),(padColumn 45 0x1fe001f933c0,padColumn 45 0xad118993280)] i))
def cols : List ColumnInfo := [(4,0,664,0,4),(8,0,660,0,4),(16,0,652,0,4),(128,0,540,0,4),(512,0,156,0,4)]
def data6 : Nat → Nat := (fun i => tableWord #[0x1f,0x29c05] i)
def data5 : Nat → Nat := (fun i => tableWord #[0x3f420,0x0,0x3f440,0x101] i)
def data4 : Nat → Nat := (fun i => tableWord #[0x5dca1440,0x0] i)
def levels : Nat → Packing
  | 4 => (1,2,3,0,0,0,0,data4)
  | 5 => (2,1,3,0,0,0,0,data5)
  | 6 => (1,0,3,0,0,0,0,data6)
  | _ => (0,0,0,0,0,0,0,fun _ => 0)
def index : Nat → Nat → Option (Nat × Nat)
  | 5 => fun v => (if v=5239425270783651293 then some (0,0) else none)
  | 6 => fun h => smallSlot h 5 16 2 4 (fun i => ((fun i => tableWord #[0x50050] i) (i/16) >>> (4*(i%16))) % 16) (fun i => ((fun i => tableWord #[0x2085400000025800000051505ca6e9199d0d] i) (i/16) >>> (9*(i%16))) % 512)
  | _ => fun _ => none
def book : Forest := ⟨668,6,samples,cols,[[],[115,148],[50,116],[50,66,146,114],[66,151],[66,147,114,50],[114,50,67,148],[114,147],[146,67],[146,115,66,67]],levels,index⟩
theorem geometry : graphValid book (boundsBefore entries) = true := by decide +kernel
set_option maxRecDepth 16000 in
theorem row6_0 : CutRow book 6 0 1 := bandCut 5 false (by decide +kernel)
theorem band6 : CutRow book 6 0 1 := row6_0
set_option maxRecDepth 16000 in
theorem row5_0 : CutRow book 5 0 2 := bandCut 6 false (by decide +kernel)
theorem band5 : CutRow book 5 0 2 := row5_0
set_option maxRecDepth 16000 in
theorem row4_0 : CutRow book 4 0 1 := bandCut 5 false (by decide +kernel)
theorem band4 : CutRow book 4 0 1 := row4_0
theorem checked : mixedTables book 6 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact band4
  · exact band5
  · exact band6
end B668_7
theorem h668_7 : Face true 668 7 :=
  mixedLower (g:=B668_7.book) (i:=0) (hints:=275414983424)
    (before_sound B668_7.entries B668_7.prior) B668_7.geometry B668_7.checked
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem h679_7 : Face true 679 7 := carry_of (swaps:=[145,129,49,99,48,114,81,64]) (by decide +kernel) h190_7
theorem h685_7 : Face true 685 7 := carry_of (swaps:=[145,129,97,83,114,16,64]) (by decide +kernel) h190_7
theorem h689_7 : Face true 689 7 := carry_of (swaps:=[116,83,16,32]) (by decide +kernel) h668_7
theorem h561_4 : Face true 561 4 := carry_of (swaps:=[146,130,114,32,48,99,82,64]) (by decide +kernel) h29_4
theorem h646_4 : Face true 646 4 := carry_of (swaps:=[146,130,115,98,83,66,16]) (by decide +kernel) h29_4
theorem h663_7 : Face true 663 7 := carry_of (swaps:=[147,131,116,66,99,32,80,16]) (by decide +kernel) h63_7
theorem h694_7 : Face true 694 7 := carry_of (swaps:=[151,114,130,81,98,50,65]) (by decide +kernel) h190_7

namespace B695_10
def entries : List (Nat × Nat) := [(165,4),(166,4),(183,7),(561,4),(646,4),(660,4),(663,7),(679,7),(689,7),(694,7)]
theorem prior : Known true entries := (consFace h165_4 (consFace h166_4 (consFace h183_7 (consFace h561_4 (consFace h646_4 (consFace h660_4 (consFace h663_7 (consFace h679_7 (consFace h689_7 (consFace h694_7 (known_down baseKnown)))))))))))
def samples : Nat → Bits × Bits := (fun i => (if i<8 then tableBits #[(padColumn 146 0x47fc7c440000001fffe0030000ffff80c03c,padColumn 146 0x3fc3c001810106cb4a0330000ed6500c014),(padColumn 146 0xbc7ffcbc00000000001ffc18300181ffc003,padColumn 146 0x3c3ffc3c60606080606d5c18300181da8001),(padColumn 146 0x3cbc487c800000fe0001ff000cfc6067fc0c3,padColumn 146 0x3c3c003c080818d218192a000ce8606254042),(padColumn 146 0x0,padColumn 146 0x0),(padColumn 146 0x1108bcbfc000ff0001fe00067f3007f83030c,padColumn 146 0x3c3fd030aa3020b40c066a3001a830108),(padColumn 146 0x3fd1113fc07f0001fe00000fb043f880c0c30,padColumn 146 0x3fc0003fe05a60413420300d30412880c0420),(padColumn 146 0x0,padColumn 146 0x0),(padColumn 146 0x22223fd13fff00fe000000ffc0fc830103cc0,padColumn 146 0x3fc012a5802c40c040a2c014830101880)] i else tableBits #[(padColumn 146 0x0,padColumn 146 0x0),(padColumn 146 0x3fffe2223f80ff00000000f87f83040603300,padColumn 146 0x3fffc0002d405581810180581583040602200)] i))
def cols : List ColumnInfo := [(1,0,694,0,7),(16,0,679,0,7),(32,0,663,0,7),(512,0,183,0,7),(4,2,689,0,7),(6,0,689,0,7),(35,0,660,0,4),(48,1,646,0,4),(134,0,561,0,4),(513,16,166,0,4),(529,0,166,0,4),(530,0,165,0,4)]
def data9 : Nat → Nat := (fun i => tableWord #[0x7f,0x40123506] i)
def data8 : Nat → Nat := (fun i => (if i<8 then tableWord #[0xff460,0xa552a04,0xff480,0x50e603,0xff4a0,0x282582a706,0xff4c0,0x140d4ea05] i else tableWord #[0xff4a4,0x282424f506,0xff4c4,0x5043454e907,0xffca0,0x242ace807,0xffca4,0x810a93a84808] i))
def data7 : Nat → Nat := bookData 2 3 3 (fun i => ((fun i => tableWord #[0xca44c44a4ca04c04a0] i) (i/16) >>> (12*(i%16))) % 4096) (fun i => ((fun i => tableWord #[0x1efdfdfeef6f] i) (i/16) >>> (9*(i%16))) % 512) (fun i => ((fun i => tableWord #[0x139954e64b3954ce64d39934c48e3159ce64138cace3273900] i) (i/16) >>> (18*(i%16))) % 262144) (fun i => (if i<8 then tableWord #[0xd3502,0xd3502,0x801,0x0,0x84a02,0xb01,0x0,0x0] i else tableWord #[0x3401,0x0,0x0] i))
def levels : Nat → Packing
  | 7 => (11,2,4,0,0,0,0,data7)
  | 8 => (8,1,4,0,0,0,0,data8)
  | 9 => (1,0,4,0,0,0,0,data9)
  | _ => (0,0,0,0,0,0,0,fun _ => 0)
def index : Nat → Nat → Option (Nat × Nat)
  | 8 => fun h => smallSlot h 6 20 4 1 (fun i => ((fun i => tableWord #[0x18100] i) (i/16) >>> (5*(i%16))) % 32) (fun i => ((fun i => tableWord #[0x2529a38400817588000007008a000016,0x2286008b] i) (i/16) >>> (8*(i%16))) % 256)
  | 9 => fun h => smallSlot h 7 22 4 1 (fun i => ((fun i => tableWord #[0x86020403] i) (i/16) >>> (5*(i%16))) % 32) (fun i => ((fun i => tableWord #[0xc16288c35300000038d4a5b207a655d7,0x400000000] i) (i/16) >>> (8*(i%16))) % 256)
  | _ => fun _ => none
def book : Forest := ⟨695,9,samples,cols,[[],[64,149]],levels,index⟩
theorem geometry : graphValid book (boundsBefore entries) = true := by decide +kernel
set_option maxRecDepth 16000 in
theorem row9_0 : CutRow book 9 0 1 := bandCut 7 false (by decide +kernel)
theorem band9 : CutRow book 9 0 1 := row9_0
set_option maxRecDepth 16000 in
theorem row8_0 : CutRow book 8 0 8 := bandCut 8 true (by decide +kernel)
theorem band8 : CutRow book 8 0 8 := row8_0
set_option maxRecDepth 16000 in
theorem row7_0 : CutRow book 7 0 3 := bandCut 7 false (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row7_3 : CutRow book 7 3 8 := bandCut 8 true (by decide +kernel)
theorem combine7_0_11 : CutRow book 7 0 11 := @joinRow book 7 0 3 8 row7_0 row7_3
theorem band7 : CutRow book 7 0 11 := combine7_0_11
theorem checked : mixedTables book 9 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact band7
  · exact band8
  · exact band9
end B695_10
theorem h695_10 : Face true 695 10 :=
  mixedLower (g:=B695_10.book) (i:=0) (hints:=275414778148)
    (before_sound B695_10.entries B695_10.prior) B695_10.geometry B695_10.checked
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem h573_7 : Face true 573 7 := carry_of (swaps:=[145,129,66,16,112]) (by decide +kernel) h190_7
theorem h673_4 : Face true 673 4 := carry_of (swaps:=[146,50,131,66,116,99,82]) (by decide +kernel) h29_4
theorem h688_4 : Face true 688 4 := carry_of (swaps:=[148,132,66,64,115,98,80,16]) (by decide +kernel) h29_4

namespace B701_11
def entries : List (Nat × Nat) := [(29,4),(57,4),(156,4),(165,4),(172,4),(177,4),(189,8),(540,4),(561,4),(573,7),(652,4),(657,4),(660,4),(664,4),(668,7),(673,4),(685,7),(688,4),(689,7)]
theorem prior : Known true entries := (consFace h29_4 (consFace h57_4 (consFace h156_4 (consFace h165_4 (consFace h172_4 (consFace h177_4 (consFace h189_8 (consFace h540_4 (consFace h561_4 (consFace h573_7 (consFace h652_4 (consFace h657_4 (consFace h660_4 (consFace h664_4 (consFace h668_7 (consFace h673_4 (consFace h685_7 (consFace h688_4 (consFace h689_7 (known_down baseKnown))))))))))))))))))))
def samples : Nat → Bits × Bits := (fun i => (if i<8 then tableBits #[(padColumn 145 0x23ffe20000001fffc00018001fffc10300f0,padColumn 145 0x1ffe00c08106cb5408198001dac81030050),(padColumn 145 0x0,padColumn 145 0x0),(padColumn 145 0x5e3e3e00000fe000007f8007f830c0ff0303,padColumn 145 0x1e1e1e10106d2060c1268007d030c0960101),(padColumn 145 0x1e5e3e400000000003fffe0c000c03fff000f,padColumn 145 0x1e1e1e060608081812ad960c000c035690006),(padColumn 145 0x88445e0007f0001fff80033e600fff040c3c,padColumn 145 0x1e818523020a9502033460034a040428),(padColumn 145 0x1fe889e03f8001fe0000007d887f1061830c0,padColumn 145 0x1fe001f02b3041342060c0698825106181080),(padColumn 145 0x0,padColumn 145 0x0),(padColumn 145 0x11111e9fff80fe00000007fe1f9061820f300,padColumn 145 0x1e0a54c02c40c18105160290618206200)] i else tableBits #[(padColumn 145 0x0,padColumn 145 0x0),(padColumn 145 0x1ffff11fc07f0000000007c3f060820c0cc00,padColumn 145 0x1fffe015a02d8181020602c0b060820c08800)] i))
def cols : List ColumnInfo := [(512,0,189,0,8),(16,0,685,0,7),(128,0,573,0,7),(12,0,689,0,7),(33,0,668,0,7),(13,0,688,0,4),(20,8,673,0,4),(28,0,673,0,4),(37,0,664,0,4),(41,0,660,0,4),(44,0,657,0,4),(48,1,652,0,4),(49,0,652,0,4),(129,32,540,0,4),(136,4,561,0,4),(140,0,561,0,4),(161,0,540,0,4),(524,0,177,0,4),(529,0,172,0,4),(536,0,165,0,4),(545,0,156,0,4),(644,0,57,0,4),(672,0,29,0,4)]
def data10 : Nat → Nat := (fun i => tableWord #[0x7f,0x6403] i)
def data9 : Nat → Nat := (fun i => (if i<16 then (if i<8 then tableWord #[0xff0a3,0x49604310e18c4c20b,0xff420,0x20108b80e0c408,0xff440,0x108980b0c407,0xff460,0x422e348407] i else tableWord #[0xff4a0,0x10a040b8c407,0xff4c0,0x108b02348407,0xff4a3,0x200428e406,0xff4c3,0x10928c091307] i) else tableWord #[0xff8a3,0x31062c24e39010a,0xff8c3,0x218b8e400107,0xffc60,0x864e304407,0xffca0,0x138b56310208] i))
def data8 : Nat → Nat := bookData 2 4 4 (fun i => ((fun i => tableWord #[0xca0c608c34c34c04604404200a38a34a34a0] i) (i/16) >>> (12*(i%16))) % 4096) (fun i => ((fun i => tableWord #[0x7ffefbff7f7ffd7febdf67f6f] i) (i/16) >>> (9*(i%16))) % 512) (fun i => ((fun i => tableWord #[0x4e6454e5454e3454a05546055ce644ce3444e6444e3444a0544e6434e043ca3324e122ce611ce400,0xca360ce240ce1404e6404a3604c050ce646ce546ce246ce1464e6464e5464c056ce645ce545ce345,0xce641ce0418c3914e6414c3910e681ce547ce347ce247ce1478c5874c3874c187ce640ce470ce340,0x4e24a4e14a4a05a8c5894e5494e1494e0494e6424e5424c3924e1424e042ce548ce148ce048ce681,0x4a1a6461a6ca3a58c5a54c5a54c3a54a3a54c3a44a3a44e64b4e34b4a36b4e24b4e14b4e64a4e54a,0x4c3a04a3a04c2a04a2a04c1a0461a0ca3a6ca2a6ca1a68c5a64c5a64a3a64c2a64a2a6462a64c1a6,0xca1aa8c5aa4c5aa4c1aa4c5a28e5a84e5a84e1a8ce6a1ce0a14e6a14c3a14e0a1ca3a74a3a74c5a0,0x4c3ab4c2ab] i) (i/16) >>> (20*(i%16))) % 1048576) (fun i => (if i<64 then (if i<32 then (if i<16 then (if i<8 then tableWord #[0xc18c59004,0x830b1e404,0x8b0c3071306,0x2654581043439608,0x59202,0x245499604,0xc70b03,0x65858e04] i else tableWord #[0x2058e03,0x58802,0x1870803,0x1a18b03,0x2c1218b04,0x18a8b03,0x4125a18b05,0x10e2012c8030b07] i) else (if i<24 then tableWord #[0x18048b03,0x3830904,0xa3830904,0x459203,0x30e251088b07,0x90b02,0x3071203,0x231a5890605] i else tableWord #[0x30b1c4461206,0x61c3079205,0xe084100b05,0xc4220b04,0x401030e284480b08,0x464c80e04,0x5831003,0x1059003] i)) else (if i<48 then (if i<40 then tableWord #[0x859003,0x1080b03,0x10061c4459006,0x39028551c406,0x84059204,0x42d04a1005,0x64871404,0x5831403] i else tableWord #[0x18c59203,0x81858e204839408,0x142a4cb2005,0x11a4c72005,0x401858d1c5890a08,0x843470616580a008,0x64838a8b05,0x20c2c79030e16345200a] i) else (if i<56 then tableWord #[0x20c7920c205,0xe263c59205,0xd2c4871305,0xd1c4841305,0x59202,0x38e02,0x1a4871304,0x41000c3458e07] i else tableWord #[0x68e2a5891306,0x59202,0xc38e03,0x110d1c185c006,0x20a202,0x41070b04,0xc38e03,0x11031303] i))) else (if i<96 then (if i<80 then (if i<72 then tableWord #[0x3834404,0xe2b1099205,0x71502,0x30f02,0xc4870b04,0x20c5470b05,0x6122ca9605,0x402c40e04] i else tableWord #[0x2071303,0x20021848b05,0x48b02,0x2459603,0xc8058904,0x1848b03,0x8c70703,0x71502] i) else (if i<88 then tableWord #[0x71502,0x31302,0x8c78603,0x98602,0x459203,0x2c91603,0x2c91603,0x462c91604] i else tableWord #[0x462c91604,0x8c59203,0x23171038e05,0x885459004,0x471079004,0x882c81304,0x411059004,0x11080b03] i)) else (if i<112 then (if i<104 then tableWord #[0x2c81603,0xa0b02,0x4640a0b04,0x20164092405,0x4004b1304,0x8099603,0x120b02,0x4cb2003] i else tableWord #[0x5439303,0x99602,0x10491303,0x4ca9603,0x881c71504,0x11099603,0x41164091605,0x38b1c4091506] i) else tableWord #[0x11031303,0xb1202] i))))
def data7 : Nat → Nat := bookData 3 7 5 (fun i => ((fun i => tableWord #[0x4a04204e5c604e1c604a0c608c58c34e18c38c34a30e64a3ce14c08c54c04e64a04e5460ce54404e64404e54404e3420,0xca3460ce24608c54604a34604a24604c14604614604c0460ce64408c54404e34404a34404a0440460440ce64204a3420,0xca34c0ce24c04a34c04c14c0ce64a0ce44a0ce24a0ce14a04c34a04a34a04c24a04a24a04c14a04614a04c04a0ce6460,0xca1c608c5c604c5c604e08c34e58a34c58a34c38a34e18a3ce04c38e54c34e14c3ce64a3ce04a34e64a34c34a34e04a3,0x4c3ca04a3ca0] i) (i/16) >>> (24*(i%16))) % 16777216) (fun i => ((fun i => tableWord #[0xcff77feafe9febfdfaf6adf97c7e6f8fe779f67b,0xdf6f7bbfb7d7f9fb7f6ff5efdbefbe] i) (i/16) >>> (10*(i%16))) % 1024) (fun i => ((fun i => tableWord #[0xd0618ed0200dd0340c50338bd0200a8c5309907188502007ce5286d04205d06184d04204506183d03102d01081d02000,0x5035834e6796d05582d06581d06595d05595d06514ce3714ce64934a2693ce6492d05612503591d06580d06510ce648f,0xd026214c18215055a050289f50559ece679dd06584d0651cd0191bce679ad028998c58184c1818505597503597506583,0x5035a8ce4a27d06b26d06526ce6ba6ce4a264c39a6106b26ce67a5ce4a25d01924d05aa3ce4a234e67a3d028a24a39a2,0xd04cb00e67b09075085028af8c57ae5055ae503506501506d0652d8c5b2d4c3c2dd0352c5035ab4c5a2a5065a95065a8,0x5055b7503d36500636d028b5d007b45037b45007b4ce67b35065b30e67b3ce6c09d067b2ce6c31ce67b1d06530ce67b0,0x5075be4e5bbed0678ed0658e10678e5075bd4e5bbd4e648c4e248c8c57bcd065bb1067bb5075ba4e67ba4e57394c5db8,0x5075c14e3741d06b404e6bc04c39c0106b405075bf] i) (i/16) >>> (24*(i%16))) % 16777216) (fun i => (if i<64 then (if i<32 then (if i<16 then (if i<8 then tableWord #[0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x101402] i else tableWord #[0xe01,0x0,0x131602,0x0,0x1601,0xb01,0xe01,0x0] i) else (if i<24 then tableWord #[0x0,0x0,0x0,0x0,0x0,0x0,0x43841603,0x901] i else tableWord #[0xa01602,0x0,0x0,0x0,0x0,0x901,0x410902,0x1601] i)) else (if i<48 then (if i<40 then tableWord #[0x0,0x0,0x0,0x1501,0x1601,0x0,0x1501,0x0] i else tableWord #[0x0,0x0,0xb01,0x1601,0x0,0xb01,0x841002,0x1401] i) else (if i<56 then tableWord #[0xe01,0xc401,0x1501,0x0,0xc401,0xc401,0x0,0x1301] i else tableWord #[0x1401,0xb01,0xa001,0xb01,0xc401,0x8101,0x0,0x1601] i))) else (if i<96 then (if i<80 then (if i<72 then tableWord #[0x0,0x0,0x0,0xb01,0x0,0xb1402,0x1401,0x1401] i else tableWord #[0x0,0x0,0x1601,0x0,0x0,0x1601,0x1601,0x0] i) else (if i<88 then tableWord #[0xa41402,0x2001,0x1301,0x8201,0x131602,0x421602,0x0,0x0] i else tableWord #[0x0,0x6401,0x4201,0x0,0x0,0x0,0x4101,0x1601] i)) else (if i<112 then (if i<104 then tableWord #[0x0,0x1601,0x1601,0x0,0x0,0x0,0x0,0x8401] i else tableWord #[0x8401,0x1601,0x0,0x0,0x0,0x1601,0x1601,0x4101] i) else tableWord #[0x1601,0x0,0x0,0x0,0x0,0x1601,0x0] i))))
def data6 : Nat → Nat := bookData 4 4 3 (fun i => ((fun i => tableWord #[0x507ca1c605074c5c605074c58a3500ce64a3d044e04a30e64e04a3503ce14a0ce44a34a0d014a24a0d024614a0505ce2460ce68c54604e68c5440] i) (i/16) >>> (36*(i%16))) % 68719476736) (fun i => ((fun i => tableWord #[0x297e2fcdb9ae1fd1f] i) (i/16) >>> (11*(i%16))) % 2048) (fun i => ((fun i => tableWord #[0x3498e6931bd2635a496739a4073489282fa4c5b41a2e7234ce447a4c494940e9280] i) (i/16) >>> (19*(i%16))) % 524288) (fun i => (if i<8 then tableWord #[0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0] i else tableWord #[0x0,0x0,0x0,0x0,0x0,0x0] i))
def levels : Nat → Packing
  | 6 => (14,4,5,0,0,0,0,data6)
  | 7 => (119,3,5,0,0,0,0,data7)
  | 8 => (114,2,5,0,0,0,0,data8)
  | 9 => (12,1,5,0,0,0,0,data9)
  | 10 => (1,0,5,0,0,0,0,data10)
  | _ => (0,0,0,0,0,0,0,fun _ => 0)
def index : Nat → Nat → Option (Nat × Nat)
  | 7 => fun h => smallSlot h 7 22 4 2 (fun i => ((fun i => tableWord #[0x100210000] i) (i/16) >>> (5*(i%16))) % 32) (fun i => ((fun i => tableWord #[0x29704000038709e40000000e08021985,0x1c4de10280ec6] i) (i/16) >>> (9*(i%16))) % 512)
  | 8 => fun h => smallSlot h 98 313 7 2 (fun i => ((fun i => tableWord #[0x180000000000e00008000001000180600,0x80404000000c0802000000000000000000,0x100000010080004000000c02000280c0600,0x81c0000018000000050000801000000009,0x1000040c09000000002028000401,0x18000402000080205008040000000000201,0x0] i) (i/16) >>> (9*(i%16))) % 512) (fun i => ((fun i => (if i<16 then (if i<8 then tableWord #[0x443e32c04d5e5cfa3bfd185bc62000000000f0281e000000,0x2db000e72000d3e9366c88d4294339ac9a47a21000452460,0x812c69006a4c875e496d921801b8298a6c56cd7,0xe6885c026c310d6000814a7664dd61cb2000e2a,0x26a00063f0006dc000a5a0000000000001ad000ab3000000,0xc1fc36c0d663c74e0146c63a348227416ec7e0c4ca,0xa655c8000bdae25000a1a00000000000002c000000000728,0xf670000000006be01dc35264845ed3a6fcb9a4644e000000] i else tableWord #[0x2d83c2a9359a8d00067140b957000000000e6e33da6ba13,0xa5e3d96bdf4fa670009d705400000025000afdce66e28,0xbf5d5ae051f200000020fdc70003cace7000441000951000,0x531be00062e4392e21187b9238b732402d10000006338cf,0x45d000000000a150001290000a40000000000003a9cb5e3e,0xa42c020000da0000590000004afe5f65700007722ba44000,0xa51e7304fa2f00080733aa340030001bd000000000d5c000,0xc48000000000f160000000000000005e78c5a19000000] i) else tableWord #[0xa10000c30655000e9a000cf50002f2f4600e000,0xc24ee397200044b00000000000000000047000000000086d,0xd12000e08a1c1cd00000000043d000a1763740937504a891,0xa20a22e11000c58a61000a23] i)) (i/16) >>> (12*(i%16))) % 4096)
  | 9 => fun h => smallSlot h 122 422 7 2 (fun i => ((fun i => tableWord #[0x40000000000000000000001000000000,0x18000602018040000008000000,0x40200000000200000040001,0x2000000201000000000000000001,0x80002000040000018000001000080000,0x8000400010000200000001400,0x8000600000040200010000600008000001,0x603000080201038000602] i) (i/16) >>> (9*(i%16))) % 512) (fun i => ((fun i => (if i<16 then (if i<8 then tableWord #[0x26245b4050000000003d7d36000000000559000000d15b2f,0xa1c000903000221a55000000000849000c3b0004cf016,0xe4e000000b0d0007e3000762000000e3113a636,0x266def8270e2000835ee481b41000000064d000560000,0x22439d73325d0023df0000000004dae08,0x954d14dc63a0007c50006ac87008784a000e71,0xc50000c4f62c2c942d226,0xe0dccc372000000000000b16e1d4c5000000000000] i else tableWord #[0xa2b000014000000000000a6e00000000000049d000c465a0,0xa53000c4100080f00000000000000043835e000000000,0x8ae000000f48ee7000e12cee7e2000023260011818,0xc174d54df1d600000000020921a00000000000030ce06000,0x2220af000c6dbe400000000043faceb05c47000613a19,0x1714a664800000000086460b00000060c000b53,0xd950007850006d7000000859000000042000000000204c6f,0xa152456a035f000c0300043dc61bee] i) else (if i<24 then tableWord #[0xe3c000000000000a67000aed000169a33fda59cc07000000,0x26a45eb54000000232000000000843258000000335000,0xc2f0000008ece2a43e3e1252000000000000c6cb32000,0xe3400000000000000000000006b00084be5c000000,0xd8000000000000000ba6456000839c1e000aca269,0x62ea6820e000000b1c000265,0x20a00000000000000000000005f000000000ee3000000425,0xb55000e1f000a72c300009250000007e7c5469cb3b000ccd] i else tableWord #[0xa28000663000437285651f4924c00000096448a767000fd5,0x4d64014e1945cefe5a9af044e88000000000840a29000000,0x657ce5e20] i))) (i/16) >>> (12*(i%16))) % 4096)
  | 10 => fun h => smallSlot h 20 69 4 2 (fun i => ((fun i => tableWord #[0xa0c001001828004000000200000,0x14001] i) (i/16) >>> (7*(i%16))) % 128) (fun i => ((fun i => tableWord #[0xe3a5a2a488dbb0344ca52ec0034,0x19800000021000002a0000000208027800,0x20c4a35a164f30b6000000000000000000,0xe5f714800000000a00000000000559640049,0x4600002c400] i) (i/16) >>> (9*(i%16))) % 512)
  | _ => fun _ => none
def book : Forest := ⟨701,10,samples,cols,[[],[32,83,116],[48,82],[80,50,116]],levels,index⟩
theorem geometry : graphValid book (boundsBefore entries) = true := by decide +kernel
set_option maxRecDepth 16000 in
theorem row10_0 : CutRow book 10 0 1 := bandCut 7 false (by decide +kernel)
theorem band10 : CutRow book 10 0 1 := row10_0
set_option maxRecDepth 16000 in
theorem row9_0 : CutRow book 9 0 12 := bandCut 8 true (by decide +kernel)
theorem band9 : CutRow book 9 0 12 := row9_0
set_option maxRecDepth 16000 in
theorem row8_0 : CutRow book 8 0 4 := bandCut 7 false (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row8_4 : CutRow book 8 4 12 := bandCut 8 true (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row8_16 : CutRow book 8 16 12 := bandCut 8 true (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row8_28 : CutRow book 8 28 12 := bandCut 8 true (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row8_40 : CutRow book 8 40 12 := bandCut 8 true (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row8_52 : CutRow book 8 52 12 := bandCut 8 true (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row8_64 : CutRow book 8 64 7 := bandCut 8 false (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row8_71 : CutRow book 8 71 12 := bandCut 9 true (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row8_83 : CutRow book 8 83 12 := bandCut 9 true (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row8_95 : CutRow book 8 95 12 := bandCut 9 true (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row8_107 : CutRow book 8 107 7 := bandCut 9 false (by decide +kernel)
theorem combine8_0_16 : CutRow book 8 0 16 := @joinRow book 8 0 4 12 row8_0 row8_4
theorem combine8_16_24 : CutRow book 8 16 24 := @joinRow book 8 16 12 12 row8_16 row8_28
theorem combine8_40_24 : CutRow book 8 40 24 := @joinRow book 8 40 12 12 row8_40 row8_52
theorem combine8_64_19 : CutRow book 8 64 19 := @joinRow book 8 64 7 12 row8_64 row8_71
theorem combine8_83_24 : CutRow book 8 83 24 := @joinRow book 8 83 12 12 row8_83 row8_95
theorem combine8_0_40 : CutRow book 8 0 40 := @joinRow book 8 0 16 24 combine8_0_16 combine8_16_24
theorem combine8_40_43 : CutRow book 8 40 43 := @joinRow book 8 40 24 19 combine8_40_24 combine8_64_19
theorem combine8_83_31 : CutRow book 8 83 31 := @joinRow book 8 83 24 7 combine8_83_24 row8_107
theorem combine8_0_83 : CutRow book 8 0 83 := @joinRow book 8 0 40 43 combine8_0_40 combine8_40_43
theorem combine8_0_114 : CutRow book 8 0 114 := @joinRow book 8 0 83 31 combine8_0_83 combine8_83_31
theorem band8 : CutRow book 8 0 114 := combine8_0_114
set_option maxRecDepth 16000 in
theorem row7_0 : CutRow book 7 0 12 := bandCut 7 true (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row7_12 : CutRow book 7 12 4 := bandCut 7 false (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row7_16 : CutRow book 7 16 12 := bandCut 8 true (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row7_28 : CutRow book 7 28 12 := bandCut 8 true (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row7_40 : CutRow book 7 40 12 := bandCut 8 true (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row7_52 : CutRow book 7 52 12 := bandCut 8 true (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row7_64 : CutRow book 7 64 12 := bandCut 8 true (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row7_76 : CutRow book 7 76 12 := bandCut 8 true (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row7_88 : CutRow book 7 88 12 := bandCut 8 true (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row7_100 : CutRow book 7 100 12 := bandCut 8 true (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row7_112 : CutRow book 7 112 7 := bandCut 8 false (by decide +kernel)
theorem combine7_0_16 : CutRow book 7 0 16 := @joinRow book 7 0 12 4 row7_0 row7_12
theorem combine7_16_24 : CutRow book 7 16 24 := @joinRow book 7 16 12 12 row7_16 row7_28
theorem combine7_40_24 : CutRow book 7 40 24 := @joinRow book 7 40 12 12 row7_40 row7_52
theorem combine7_64_24 : CutRow book 7 64 24 := @joinRow book 7 64 12 12 row7_64 row7_76
theorem combine7_88_24 : CutRow book 7 88 24 := @joinRow book 7 88 12 12 row7_88 row7_100
theorem combine7_0_40 : CutRow book 7 0 40 := @joinRow book 7 0 16 24 combine7_0_16 combine7_16_24
theorem combine7_40_48 : CutRow book 7 40 48 := @joinRow book 7 40 24 24 combine7_40_24 combine7_64_24
theorem combine7_88_31 : CutRow book 7 88 31 := @joinRow book 7 88 24 7 combine7_88_24 row7_112
theorem combine7_0_88 : CutRow book 7 0 88 := @joinRow book 7 0 40 48 combine7_0_40 combine7_40_48
theorem combine7_0_119 : CutRow book 7 0 119 := @joinRow book 7 0 88 31 combine7_0_88 combine7_88_31
theorem band7 : CutRow book 7 0 119 := combine7_0_119
set_option maxRecDepth 16000 in
theorem row6_0 : CutRow book 6 0 12 := bandCut 7 true (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row6_12 : CutRow book 6 12 2 := bandCut 7 false (by decide +kernel)
theorem combine6_0_14 : CutRow book 6 0 14 := @joinRow book 6 0 12 2 row6_0 row6_12
theorem band6 : CutRow book 6 0 14 := combine6_0_14
theorem checked : mixedTables book 10 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact band6
  · exact band7
  · exact band8
  · exact band9
  · exact band10
end B701_11
theorem h701_11 : Face true 701 11 :=
  mixedLower (g:=B701_11.book) (i:=0) (hints:=275414786820)
    (before_sound B701_11.entries B701_11.prior) B701_11.geometry B701_11.checked
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem h710_7 : Face true 710 7 := carry_of (swaps:=[116,100,84,49,33]) (by decide +kernel) h668_7
theorem h723_7 : Face true 723 7 := carry_of (swaps:=[146,33,114,129,50,99,32,81,64]) (by decide +kernel) h190_7
theorem h727_10 : Face true 727 10 := carry_of (swaps:=[151,101,66,16]) (by decide +kernel) h695_10
theorem h730_7 : Face true 730 7 := carry_of (swaps:=[146,50,131,113,83,98,65]) (by decide +kernel) h190_7
theorem h734_11 : Face true 734 11 := carry_of (swaps:=[151,101,66,16]) (by decide +kernel) h701_11
theorem h743_10 : Face true 743 10 := carry_of (swaps:=[100,82,16]) (by decide +kernel) h695_10
theorem h582_4 : Face true 582 4 := carry_of (swaps:=[146,130,50,115,98,83,32,64,16]) (by decide +kernel) h29_4
theorem h627_7 : Face true 627 7 := carry_of (swaps:=[147,131,115,98]) (by decide +kernel) h63_7
theorem h633_7 : Face true 633 7 := carry_of (swaps:=[151,135,84,66,98,16,48]) (by decide +kernel) h190_7
theorem h639_11 : Face true 639 11 := carry_of (swaps:=[151,135,101,66,16]) (by decide +kernel) h255_11
theorem h706_4 : Face true 706 4 := carry_of (swaps:=[147,50,67,130,116,99,82,16]) (by decide +kernel) h29_4
theorem h739_7 : Face true 739 7 := carry_of (swaps:=[148,32,132,115,98,80,16]) (by decide +kernel) h63_7
theorem h755_10 : Face true 755 10 := carry_of (swaps:=[151,84,98,50]) (by decide +kernel) h695_10
theorem h594_4 : Face true 594 4 := carry_of (swaps:=[147,131,67,116,66,99,82,16]) (by decide +kernel) h29_4

namespace B759_12
def entries : List (Nat × Nat) := [(165,4),(166,4),(177,4),(183,7),(198,4),(231,7),(582,4),(593,4),(594,4),(599,7),(627,7),(689,7),(695,10),(710,7),(727,10),(743,10),(755,10)]
theorem prior : Known true entries := (consFace h165_4 (consFace h166_4 (consFace h177_4 (consFace h183_7 (consFace h198_4 (consFace h231_7 (consFace h582_4 (consFace h593_4 (consFace h594_4 (consFace h599_7 (consFace h627_7 (consFace h689_7 (consFace h695_10 (consFace h710_7 (consFace h727_10 (consFace h743_10 (consFace h755_10 (known_down baseKnown))))))))))))))))))
def samples : Nat → Bits × Bits := (fun i => (if i<8 then tableBits #[(padColumn 244 0x87ff0fc3f1111f8840000000000000fffff0003180000301fffff00c003c,padColumn 244 0x3ff07c1f0000f8000606010080c03696a500c3180000301dab4a00c0014),(padColumn 244 0x17c3f107ff2222097c00000000003ff00000ffc06030300ff80c03ffc00c3,padColumn 244 0x7c1f003ff0000007c08180603012a900c0365406030300d500c03aa80041),(padColumn 244 0xf8be120841f0ffff88000000007fc0000000ffcc0000cff000300cffc0303,padColumn 244 0xf83e000000f0ffff803020080c5a4040300c9a8c0000cda000300c5540102),(padColumn 244 0x0,padColumn 244 0x0),(padColumn 244 0x21042f93e2ff0f17fc000000ff80000003ff000000cff0c06003ff0300c0c,padColumn 244 0xf83e0ff0f07fc404030d5060180415a030000cea0c06000b50300408),(padColumn 244 0xffc8442084fff027fc0001ff0000000ffc00003007f3010187fc100c03030,padColumn 244 0xffc0000000fff007fd80815a3008060968100c3006a301018254100c01020),(padColumn 244 0x42108ffd08fffff813fe000000003ff00000003f8304060ff8c06010300c0,padColumn 244 0xffc00fffff802d300c0403015618060102a83040602a8c0601010080),(padColumn 244 0x84210fffff4444422001ffff007fc00000000000fff80ff6010180200f300,padColumn 244 0xfffff00000002014aa58025980201802000d15802560101802006200)] i else tableBits #[(padColumn 244 0x0,padColumn 244 0x0),(padColumn 244 0xfffff8421088888443fffe00ff8000000000003ffc0ff808060200c03cc00,padColumn 244 0xfffff00000000000012cb5002ac0200c0200c0152c015808060200c028800)] i))
def cols : List ColumnInfo := [(4,0,755,0,10),(16,0,743,0,10),(32,0,727,0,10),(64,0,695,0,10),(132,0,627,0,7),(160,0,599,0,7),(528,0,231,0,7),(576,0,183,0,7),(48,1,710,0,7),(49,0,710,0,7),(68,2,689,0,7),(70,0,689,0,7),(145,32,582,0,4),(162,4,593,0,4),(165,0,594,0,4),(177,0,582,0,4),(560,1,198,0,4),(577,16,166,0,4),(580,2,177,0,4),(594,0,165,0,4)]
def data11 : Nat → Nat := (fun i => tableWord #[0xff,0x89001a92b08] i)
def data10 : Nat → Nat := (fun i => tableWord #[0x1ff0e6,0x518a22a2d32443c70b,0x1ff4e6,0xaa38288a1147a6b0a,0x1ff8e6,0x263a84a0e1e1ac50a] i)
def data9 : Nat → Nat := (fun i => tableWord #[0x2fb5020e6,0x11241471305,0x33fce68e6,0x8920a1c71306,0x2ff5078e6,0x811243068706] i)
def levels : Nat → Packing
  | 9 => (3,2,5,0,0,0,0,data9)
  | 10 => (3,1,5,0,0,0,0,data10)
  | 11 => (1,0,5,0,0,0,0,data11)
  | _ => (0,0,0,0,0,0,0,fun _ => 0)
def index : Nat → Nat → Option (Nat × Nat)
  | 10 => fun h => smallSlot h 3 11 2 2 (fun i => ((fun i => tableWord #[0x0] i) (i/16) >>> (4*(i%16))) % 16) (fun i => ((fun i => tableWord #[0x546ae9e6f4000] i) (i/16) >>> (7*(i%16))) % 128)
  | 11 => fun v => (if v=8846553226619420952 then some (2,0) else (if v=9083563835880407257 then some (1,0) else (if v=9967659315218139993 then some (2,1) else (if v=10268309250932263832 then some (0,0) else none))))
  | _ => fun _ => none
def book : Forest := ⟨759,11,samples,cols,[[],[98,84,151],[16,66,101,151],[16,82,100]],levels,index⟩
theorem geometry : graphValid book (boundsBefore entries) = true := by decide +kernel
set_option maxRecDepth 16000 in
theorem row11_0 : CutRow book 11 0 1 := bandCut 8 false (by decide +kernel)
theorem band11 : CutRow book 11 0 1 := row11_0
set_option maxRecDepth 16000 in
theorem row10_0 : CutRow book 10 0 3 := bandCut 9 false (by decide +kernel)
theorem band10 : CutRow book 10 0 3 := row10_0
set_option maxRecDepth 16000 in
theorem row9_0 : CutRow book 9 0 2 := bandCut 8 false (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row9_2 : CutRow book 9 2 1 := bandCut 9 false (by decide +kernel)
theorem combine9_0_3 : CutRow book 9 0 3 := @joinRow book 9 0 2 1 row9_0 row9_2
theorem band9 : CutRow book 9 0 3 := combine9_0_3
theorem checked : mixedTables book 11 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact band9
  · exact band10
  · exact band11
end B759_12
theorem h759_12 : Face true 759 12 :=
  mixedLower (g:=B759_12.book) (i:=0) (hints:=275431555364)
    (before_sound B759_12.entries B759_12.prior) B759_12.geometry B759_12.checked
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

namespace B767_14
def entries : List (Nat × Nat) := [(6,1),(14,2),(29,4),(30,4),(57,4),(63,7),(78,4),(95,7),(166,4),(177,4),(183,7),(189,8),(198,4),(231,7),(255,11),(561,4),(582,4),(593,4),(599,7),(606,8),(627,7),(633,7),(639,11),(668,7),(673,4),(689,7),(701,11),(706,4),(710,7),(734,11),(739,7),(743,10),(755,10),(759,12)]
theorem prior : Known true entries := (consFace h6_1 (consFace h14_2 (consFace h29_4 (consFace h30_4 (consFace h57_4 (consFace h63_7 (consFace h78_4 (consFace h95_7 (consFace h166_4 (consFace h177_4 (consFace h183_7 (consFace h189_8 (consFace h198_4 (consFace h231_7 (consFace h255_11 (consFace h561_4 (consFace h582_4 (consFace h593_4 (consFace h599_7 (consFace h606_8 (consFace h627_7 (consFace h633_7 (consFace h639_11 (consFace h668_7 (consFace h673_4 (consFace h689_7 (consFace h701_11 (consFace h706_4 (consFace h710_7 (consFace h734_11 (consFace h739_7 (consFace h743_10 (consFace h755_10 (consFace h759_12 (known_down baseKnown)))))))))))))))))))))))))))))))))))
def samples : Nat → Bits × Bits := (fun i => (if i<8 then tableBits #[(padColumn 320 0xf07fc210421ffe1043e0000000000000001fffffc00000000060c00000600fffffe0080600c003c0,padColumn 320 0xf07fc000000ffe0001e00c0300200806006d2b55400803006060c00000600ed56940080600c00140),(padColumn 320 0xff87c4208420822fffe0000000000001ffe00000000000ffe0030060601ffc0180603001ffc00c03,padColumn 320 0xff87c0000000000fffe0100c00c0300955200600c0300465a0030060601aa8018060300155800401),(padColumn 320 0x10887e013ff17ff084200000000007fe000000000007ffffe18000019fe00006018007ffffc0300f,padColumn 320 0x3e003ff07ff0000060100100c5a2008018030042599a418000019b400006018004acaa401006),(padColumn 320 0xfff8084fc84f84413fe0000000000000000000003fffff00060c018000003018001ffffe0100003c,padColumn 320 0xfff8000fc00f80003fe1806006010010030060042a9da600860c018000003018001aab5201000018),(padColumn 320 0x2110bff201f209ffc8400000001ff800000001fffff800000000061fe180c0007ffff8080600c0f0,padColumn 320 0x3ff001f001ffc0020080181a50600c0080aa956008030000061d4180c00016a55008060040a0),(padColumn 320 0x42213ffffe0411fffe800000ffe00000001ffe000000000018003fe6020303ff8200c03018030300,padColumn 320 0x3ffffe0001fffe0c0100ab4600803012d4080180300c180035460203012a8200c03018010200),(padColumn 320 0x84023ffffffffe02111ffc0000000001ffe00000000000001ff018080c1ffc600c0300c020300c00,padColumn 320 0x3ffffffffe000016a60060080300aac300300600c010155018080c0554600c0300c020100800),(padColumn 320 0xffffd08410802084200003ffffe007fe0000000000000000001ffff01fec0080300c0100400f3000,padColumn 320 0xffffc00000000000001002a554b0025cc00400c018010020001a8ab004ac0080300c010040062000)] i else tableBits #[(padColumn 320 0x0,padColumn 320 0x0),(padColumn 320 0x844210821084108001fffff001ff80000000000000000001fffe01ff010030040100601803cc000,padColumn 320 0x9595a8005ac0100180100200600c00aa56002b01003004010060180288000)] i))
def cols : List ColumnInfo := [(8,0,759,0,12),(128,0,639,0,11),(512,0,255,0,11),(33,0,734,0,11),(66,0,701,0,11),(12,0,755,0,10),(24,0,743,0,10),(129,32,606,0,8),(514,64,189,0,8),(578,0,189,0,8),(20,8,739,0,7),(28,0,739,0,7),(134,0,633,0,7),(140,0,627,0,7),(168,0,599,0,7),(536,0,231,0,7),(584,0,183,0,7),(672,0,95,0,7),(704,0,63,0,7),(57,0,710,0,7),(76,2,689,0,7),(78,0,689,0,7),(99,0,668,0,7),(52,9,706,0,4),(60,1,706,0,4),(92,2,673,0,4),(94,0,673,0,4),(170,4,593,0,4),(185,0,582,0,4),(202,4,561,0,4),(553,16,198,0,4),(585,16,166,0,4),(590,0,177,0,4),(646,64,57,0,4),(657,32,78,0,4),(689,0,78,0,4),(705,32,30,0,4),(708,2,57,0,4),(710,0,57,0,4),(738,0,29,0,4),(216,544,6,1,2),(240,513,14,0,2)]
def data13 : Nat → Nat := (fun i => tableWord #[0x1ff,0x421460c407] i)
def data12 : Nat → Nat := (fun i => tableWord #[0x3ff482,0x2e0c20b0e20607,0x3ff4e2,0x85180c40a3219408,0x3ff502,0xa0c60a2219407,0x3ff507,0x25022818c0a1c408] i)
def data11 : Nat → Nat := bookData 2 2 3 (fun i => ((fun i => tableWord #[0x5075024e2482] i) (i/16) >>> (12*(i%16))) % 4096) (fun i => ((fun i => tableWord #[0x3ffefffef7fffddf7] i) (i/16) >>> (11*(i%16))) % 2048) (fun i => ((fun i => tableWord #[0x504aa93d141e9a44bd2756922941e5a509d244a9425408ba4e8d236293a14089a460,0x522be93db492ca4f6524b272594a2aa495] i) (i/16) >>> (17*(i%16))) % 131072) (fun i => (if i<16 then (if i<8 then tableWord #[0x506c1c20bc3c407,0xb15c442c3861e1d08,0x410d120bc485c31b1f09,0x15c1c2c3c40b06,0x1241c4c30b05,0xd2605c48142c31d08,0x4212810dc685c425c31d0a,0x4612c3c41f0d06] i else tableWord #[0x1342c4c30d05,0xc609122641c485c31d09,0x828512c4c3462607,0x1d82c685c441c32008,0x13c445c31b1206,0x410b121d0d42c3c48609,0x860a0d0b1b1f06,0x1d1f81420d0f1285c4c3460b] i) else tableWord #[0x21c30b260d1b06,0xd12261b04,0x23261d1f418246c4c3850a,0xf0b46c31d05,0x410d12261d05,0x12c3462604,0xc3121541261b06,0xd12c645c32606] i))
def data10 : Nat → Nat := bookData 3 5 5 (fun i => ((fun i => tableWord #[0x522507d27502d245025075025245024e4502d284e2d244e25284e25244e25024e2d27482d23482507482502482527482,0xd22507] i) (i/16) >>> (24*(i%16))) % 16777216) (fun i => ((fun i => tableWord #[0xbffff7dffe7fd7fb7fbf7f7bdf7bfb9ffff3dfbefbfeb9f7,0xeff] i) (i/16) >>> (12*(i%16))) % 4096) (fun i => ((fun i => tableWord #[0x54829151ce352738d41ce3d4828350ce0d42183508c054928b49c61d4408748c8152718541c414e408750c00,0x5442b951cadd2763350d2b9492a941d8a1492a9510a95482a351d67d4751f510a7d4349b508c6d4741749065,0x5246bd5120cd4879941dc3949689525a25442c351d4f] i) (i/16) >>> (22*(i%16))) % 4194304) (fun i => (if i<32 then (if i<16 then (if i<8 then tableWord #[0xa0f0f880a04,0x361f02,0x1d1487c421b05,0x483e1b03,0x4c3e1b03,0x4c1b02,0x161b02,0x5054361f04] i else tableWord #[0x2c3e1b03,0x34161e03,0x543a1e03,0x2839412064361f06,0xc8e1864361f05,0x38361f03,0x2c361f03,0x120603c1d04] i) else (if i<24 then tableWord #[0x3c2602,0x4c1b02,0x8c1a1b03,0x1a1b02,0x3c2602,0x1a1b02,0x90981a1b04,0x3c2602] i else tableWord #[0x7c181e03,0xe080b048382606,0x440743fc3a3614422208,0x3c2602,0x70c141d03,0x3a2602,0x1205c3c2604,0x5054361f04] i)) else tableWord #[0xe187c222604,0x461f02,0x201a02,0x3a1f02,0x8074341f04,0x4c1d02,0x3c4c2303,0x3a2602] i))
def data9 : Nat → Nat := (fun i => tableWord #[0x1e6b5074e4502482,0x280981f03,0x15f7d63549507482,0x0,0x157fd67549507482,0x2701] i)
def levels : Nat → Packing
  | 9 => (3,4,6,0,0,0,0,data9)
  | 10 => (40,3,6,0,0,0,0,data10)
  | 11 => (24,2,6,0,0,0,0,data11)
  | 12 => (4,1,6,0,0,0,0,data12)
  | 13 => (1,0,6,0,0,0,0,data13)
  | _ => (0,0,0,0,0,0,0,fun _ => 0)
def index : Nat → Nat → Option (Nat × Nat)
  | 10 => fun v => (if v=9173731893560143937 then some (1,0) else (if v=9817994258469878493 then some (0,0) else (if v=11282382653361050149 then some (2,0) else (if v=13146079884629819533 then some (2,1) else none))))
  | 11 => fun h => smallSlot h 24 76 6 1 (fun i => ((fun i => tableWord #[0x40400a000000006040010000000,0x22c0010604004] i) (i/16) >>> (7*(i%16))) % 128) (fun i => ((fun i => tableWord #[0xf0021e0a08400000b7094001026542068d88,0xc2dc564299002180740042903000229280004800,0x634000000019f96000a443887003819109c09ba7,0x30cd3e9a0000085d8900000000008141100000,0x84ea1219a5d3b1f00000003c30039b] i) (i/16) >>> (10*(i%16))) % 1024)
  | 12 => fun h => smallSlot h 25 92 5 1 (fun i => ((fun i => tableWord #[0x8000000000000000800400000,0x2000000000000] i) (i/16) >>> (7*(i%16))) % 128) (fun i => ((fun i => tableWord #[0xac0000003aa004528d0200,0xa403d4a00088028400005180000,0xda380050f981469000000026b600000,0x7122c00004981c0190000000000000025400,0x4125e00002140000000031d67000000009,0x157] i) (i/16) >>> (9*(i%16))) % 512)
  | 13 => fun h => smallSlot h 3 11 3 1 (fun i => ((fun i => tableWord #[0x0] i) (i/16) >>> (4*(i%16))) % 16) (fun i => ((fun i => tableWord #[0x480310002da30128064] i) (i/16) >>> (7*(i%16))) % 128)
  | _ => fun _ => none
def book : Forest := ⟨767,13,samples,cols,[[],[16,66,101,151]],levels,index⟩
theorem geometry : graphValid book (boundsBefore entries) = true := by decide +kernel
set_option maxRecDepth 16000 in
theorem row13_0 : CutRow book 13 0 1 := bandCut 9 false (by decide +kernel)
theorem band13 : CutRow book 13 0 1 := row13_0
set_option maxRecDepth 16000 in
theorem row12_0 : CutRow book 12 0 4 := bandCut 10 false (by decide +kernel)
theorem band12 : CutRow book 12 0 4 := row12_0
set_option maxRecDepth 16000 in
theorem row11_0 : CutRow book 11 0 1 := bandCut 9 false (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row11_1 : CutRow book 11 1 12 := bandCut 10 true (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row11_13 : CutRow book 11 13 11 := bandCut 11 true (by decide +kernel)
theorem combine11_0_13 : CutRow book 11 0 13 := @joinRow book 11 0 1 12 row11_0 row11_1
theorem combine11_0_24 : CutRow book 11 0 24 := @joinRow book 11 0 13 11 combine11_0_13 row11_13
theorem band11 : CutRow book 11 0 24 := combine11_0_24
set_option maxRecDepth 16000 in
theorem row10_0 : CutRow book 10 0 1 := bandCut 9 false (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row10_1 : CutRow book 10 1 12 := bandCut 10 true (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row10_13 : CutRow book 10 13 12 := bandCut 10 true (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row10_25 : CutRow book 10 25 9 := bandCut 10 true (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row10_34 : CutRow book 10 34 6 := bandCut 11 false (by decide +kernel)
theorem combine10_0_13 : CutRow book 10 0 13 := @joinRow book 10 0 1 12 row10_0 row10_1
theorem combine10_13_21 : CutRow book 10 13 21 := @joinRow book 10 13 12 9 row10_13 row10_25
theorem combine10_0_34 : CutRow book 10 0 34 := @joinRow book 10 0 13 21 combine10_0_13 combine10_13_21
theorem combine10_0_40 : CutRow book 10 0 40 := @joinRow book 10 0 34 6 combine10_0_34 row10_34
theorem band10 : CutRow book 10 0 40 := combine10_0_40
set_option maxRecDepth 16000 in
theorem row9_0 : CutRow book 9 0 1 := bandCut 9 false (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row9_1 : CutRow book 9 1 2 := bandCut 10 false (by decide +kernel)
theorem combine9_0_3 : CutRow book 9 0 3 := @joinRow book 9 0 1 2 row9_0 row9_1
theorem band9 : CutRow book 9 0 3 := combine9_0_3
theorem checked : mixedTables book 13 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact band9
  · exact band10
  · exact band11
  · exact band12
  · exact band13
end B767_14
theorem h767_14 : Face true 767 14 :=
  mixedLower (g:=B767_14.book) (i:=0) (hints:=275431563556)
    (before_sound B767_14.entries B767_14.prior) B767_14.geometry B767_14.checked
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
end Engine
end PEqualNP.Outside.L_meta_9825
namespace PEqualNP.Outside.L_meta_9822.Bound
open PEqualNP.Outside.L_meta_9825.Engine
open PEqualNP.CircuitLowerBounds
set_option maxRecDepth 16000
set_option maxHeartbeats 0
def target : Sig := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc0ffffffffffffffffffffffffffffffffffffffffffffffffffffeaeaffffc0c0fffffffffffffffffffffffffffafff0ffffffffffffffffffffffffffeaffc0fffffffffffefcfcfffffffffffaf0f0ffeeeeeeffeeccccffeaeaeaffeac0c0
def func (x : Fin 10 → Bool) : Bool := (x 1 && x 2) || (x 3 && x 4) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 6 && x 9) || (x 6 && x 8) || (x 5 && x 8)
theorem truth : ∀ r : Row, bit r target = func (sample r) := by decide +kernel
theorem properTarget : proper target := by unfold proper; decide +kernel
def moves := ([128,81,130,83,100,118]:List Nat).map swapRows ++ fixRows 1 0
def witnesses : List (Sig × Row × Row) := [(inputs.getD 0 zero,16,17)]
theorem lifted : Lower true inputs target 15 := by
  have chk : checkLift moves target inputs (varsX 767) (graphGoal 767) witnesses = true := by decide +kernel
  have b := lift_ok chk properTarget (proper_of _ (by decide +kernel)) h767_14
  change Lower true inputs target (14+(witnesses.map Prod.fst).toFinset.card) at b
  have cnt : (witnesses.map Prod.fst).toFinset.card = 1 := by decide +kernel
  rw [cnt] at b
  exact b
theorem physical (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (computes : PEqualNP.MetaComplexity.circuitFun 10 C = func) :
    15 ≤ C.gates.countP (fun g => !isNot g) := by
  classical
  have eq : (execute C.gates inputs).getD C.output zero = target := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    exact (table_eval C legal C.output r).trans ((congrFun computes (sample r)).trans (truth r).symm)
  have out := get_rep (u:=true) (execute C.gates inputs) C.output
  rw [eq] at out
  unfold Repr at out
  have pg : bit 0 target = false := by decide +kernel
  rw [nrm_id pg] at out
  obtain ⟨k,S,hk,run,sub⟩ := extract C.gates inputs legal (by simp) properTarget
    (out.resolve_right (fun h => h properTarget))
  have ns : inputs.all plainWord=true := by decide +kernel
  rw [nrm_map ns] at sub
  have run' := list_run run S.toList (Finset.nodup_toList S) (by simp)
  have supp : supply true (inputs.map observe) (S.toList.map observe) := by
    intro v hv
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hv
    exact Or.inl (List.mem_map_of_mem (sub _ (Finset.mem_toList.mp ha)))
  obtain ⟨q,bank,reach,hit,paid⟩ := contraction (observe_proper properTarget) run' (inputs.map observe)
    (p:=0) Reach.start supp
  have bound := lifted q bank reach hit
  omega
end PEqualNP.Outside.L_meta_9822.Bound

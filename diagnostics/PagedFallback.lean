import PEqualNP.Defs

-- Shared forest and cofactor certificates from L_meta_1674 and PR 11111 for L_meta_1677.

-- The checker and the bound certificates are adapted from PEqualNP/Outside/L_meta_1667.lean (Apache-2.0).
namespace PEqualNP.Outside.L_meta_4813_aux.Certificate
open PEqualNP.CircuitLowerBounds

def mask72 : Nat := 0xffffffffffffffffff

def limbs (xs : List Nat) : Nat := xs.foldl (fun a n => (a <<< 80) + n) 0
def word {n : Nat} (xs : List Nat) : BitVec n := BitVec.ofNat n (limbs xs)

def stripe4813 {n : Nat} (s : Nat) : BitVec n :=
  BitVec.ofNat n (((((1 : Nat) <<< n)-1)/(((1 : Nat) <<< s)+1)) <<< s)

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

def inputs : List Sig := [(stripe4813 1),(stripe4813 2),(stripe4813 4),(stripe4813 8),(stripe4813 16),(stripe4813 32),(stripe4813 64),(stripe4813 128),(stripe4813 256)]
def graph : Sig := (word [0xffffffff,0xfffffffffffffffffffa,0xfff8ffffffffffffffff,0xffffffffffeaffc8ffff,0xfffffffefcfcffffffff,0xfffaf8f8ffeefeeeffee,0xfcccffeafaeaffeaf8c8])
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
  | 0 => (limbs [0x1000000000000,0x10000000000000001,65536,4294967296,0x1000000000000,0x10000000000000001])
  | 1 => (limbs [0x10000000000000000,65536,0,0x1000000000000,1])
  | 2 => (limbs [1,65536,0,0,0x10000000000000001])
  | 3 => (limbs [65536,0,0,1])
  | 4 => (limbs [4294967296,0x1000000000000,0x10000000000000001])
  | 5 => (limbs [0x1000000000000,1])
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
  (x 0 &&& x 1) ||| (x 1 &&& x 2) ||| (x 2 &&& x 3) ||| (x 3 &&& x 4) |||
    (x 4 &&& x 0) ||| (x 0 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 7) |||
    (x 3 &&& x 8) ||| (x 5 &&& x 7) ||| (x 6 &&& x 8) ||| (x 8 &&& x 5)
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
  let n := v.toNat % 2305843009213693951
  (n*(n+971)) % 2305843009213693951
def keySet (xs : List Sig) := xs.foldl (fun v x => v+keyWord x) 0

def closeChild (u : Bool) (pools : List BoundPool) (links : Nat → List (List Sig)) (k : Nat)
    (rest : List Sig) (op : Choice) :=
  let ws := choiceVal op::rest
  pools.any (fun p => scalarPoolCut u p k rest op) || (links (keySet ws)).any (sameWords ws)

theorem closeChild_sound {u raw T pools links k rest op}
    (pValid : ∀ p ∈ pools, ValidPool u raw T p)
    (lValid : ∀ tag xs, xs ∈ links tag → Impossible u T k (List.toFinset xs))
    (nd : (choiceVal op :: rest).Nodup)
    (h : closeChild u pools links k rest op = true) :
    Impossible u T k (choiceVal op :: rest).toFinset := by
  simp only [closeChild,Bool.or_eq_true,List.any_eq_true] at h
  rcases h with ⟨p,hp,ok⟩ | ⟨xs,hx,ok⟩
  · exact scalarPoolCut_sound (pValid _ hp) nd ok
  · rw [sameWords_sound ok]
    exact lValid _ _ hx

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
def page (xs : Array Nat) (i : Nat) : Nat := xs.getD (i%103) 0
def gather4813 (w : Nat → Nat) (i : Nat) : Nat → Nat
  | 0 => 0
  | n+1 => w i ||| (gather4813 w (i+1) n <<< 80)
def pick4813 (w : Nat → Nat) (b p n : Nat) :=
  let i := 103*b+p/80
  let s := p%80
  let a := if s+n ≤ 80 then w i else if s+n ≤ 160 then
    w i ||| (w (i+1) <<< 80) else gather4813 w i ((s+n+79)/80)
  (a >>> s) &&& ((1 <<< n)-1)
def packedAt (word : Nat → Nat) (pos len : Nat) :=
  let b := pos/8192
  let s := pos % 8192
  let left := 8192-s
  if len ≤ left then pick4813 word b s len else
    pick4813 word b s left ||| (pick4813 word (b+1) 0 (len-left) <<< left)

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
theorem chart_bit (m : Nat) (v : Nat → Bits) (i : Fin 152) :
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
    getPairs data cw d (packedAt data pos 5) (pos+5+marker)
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
def g15d3 (i : Nat) : Nat := (if i%103=0 then 15 else 0)
def g15l3 : Packing := (1,0,1,0,0,0,0,g15d3)
def g15samples : Array (Bits × Bits) := #[((word [mask72,0xfffffffffffffffffff3]),0x62),((word [mask72,0xffffffffffffffffffbf]),(word [mask72,0xffffffffffffffffff99])),(0x4c,0x4),(0x70,0x70),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
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
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem tablesg15 : checkedTables g15 3 := by
  intro k hk
  interval_cases k <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low15 : Lower true (vars 15) (graphGoal 15) 4 := plain_low (hints:=8449) (by decide +kernel) (index_root (g:=g15) (i:=0) rfl rfl (before_sound [] baseKnown) geomg15 tablesg15 (by decide +kernel))
def known15 := extendKnown [] 4 [(15,[]),(23,[64,48,32,16]),(27,[66,16]),(29,[50,65]),(30,[50,33,16,64]),(39,[80,64,48,32,16]),(57,[32,82,64,16]),(78,[96,80,64]),(83,[99,83,64,32,16]),(99,[48,96,83,64,32,16]),(135,[115,99,83,67]),(156,[112,96,48,50,33,81,64]),(163,[115,50,98,83,66,16]),(165,[114,33,97,82,50,65]),(166,[114,98,83,33,16,64]),(172,[114,50,99,48,33,81,64]),(177,[115,99,82,64,16]),(198,[115,96,83,64]),(281,[131,115,99,50,82,65]),(291,[131,115,50,98,83,66,16]),(300,[130,114,98,49,32,81,64]),(305,[131,115,99,82,64,16]),(312,[130,114,49,98,81,64]),(323,[131,115,98,83,66]),(326,[131,115,98,83,32,64]),(330,[130,114,97,82,16,64]),(332,[130,50,115,98,49,32,81,64]),(344,[130,50,115,49,98,81,64]),(353,[130,33,113,99,82,65]),(354,[130,33,50,113,99,82,16,64]),(396,[48,128,115,96,50,33,81,64]),(424,[129,33,115,48,98,81,64]),(480,[32,50,128,115,98,81,64])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid15 : Known true known15 := extendKnown_ok (m:=15) baseKnown low15 (by decide +kernel)
def g31d6 (i : Nat) : Nat := (if i%103=0 then 18489535 else 0)
def g31l6 : Packing := (1,0,3,0,0,0,0,g31d6)
def g31h6 := page #[0x16357504004755c084,0x30be67020800006500]
def g31d5 (i : Nat) : Nat := (if i%103=0 then 0x40828fd20fd10 else 0)
def g31l5 : Packing := (2,1,3,0,0,3,0,g31d5)
def g31h5 (i : Nat) : Nat := (if i%103=0 then 768 else 0)
def g31d4 (i : Nat) : Nat := (if i%103=0 then 98387232 else 0)
def g31l4 : Packing := (1,2,3,0,0,0,0,g31d4)
def g31samples : Array (Bits × Bits) := #[(0x2e44,0x2c52),(0x5a8a,0x5208),((word [mask72,0xffffffffffffffffb4f7]),(word [mask72,0xffffffffffffffffa0c7])),((word [mask72,0xffffffffffffffffcf79]),0x4f30),(0x718c,0x108c),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
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
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem tablesg31 : checkedTables g31 6 := by
  intro k hk
  interval_cases k <;> decide +kernel
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
def g111d6 (i : Nat) : Nat := (if i%103=0 then 467263 else 0)
def g111l6 : Packing := (1,0,2,0,0,0,0,g111d6)
def g111h6 (i : Nat) : Nat := (if i%103=0 then 32768 else 0)
def g111d5 (i : Nat) : Nat := (if i%103=0 then 97873 else 0)
def g111l5 : Packing := (1,1,2,0,0,0,0,g111d5)
def g111samples : Array (Bits × Bits) := #[((word [mask72,0xffffffffffffffffed93]),0x2d12),((word [mask72,0xffffffffffffffff9467]),(word [mask72,0xffffffffffffffff9025])),(0x6e38,0x6618),(0x1bd8,0x19c0),(0x0,0x0),(0x63e4,0x42e4),(0x7e44,0x6e40),(0x0,0x0),(0x0,0x0)]
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
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem tablesg111 : checkedTables g111 6 := by
  intro k hk
  interval_cases k <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low111 : Lower true (vars 111) (graphGoal 111) 7 := plain_low (hints:=16785665) (by decide +kernel) (index_root (g:=g111) (i:=0) rfl rfl (before_sound known63 valid63) geomg111 tablesg111 (by decide +kernel))
def known111 := extendKnown known63 7 [(111,[]),(123,[101,66,16]),(187,[117,80,66,96,16]),(190,[114,83,48,33,97,64]),(215,[115,83,67]),(222,[101,117,50,33,16,64]),(238,[83,114,99,33,16,64]),(243,[82,98,115,66,16]),(311,[131,115,99,67,82,16]),(318,[128,112,96,49,64]),(343,[131,115,83,67,98]),(349,[128,80,117,32,16,98,65,48]),(365,[129,113,82,65,48]),(378,[129,33,97,81,16,114,49,64]),(437,[134,81,114,50,65]),(455,[83,133,115,67,32,96]),(476,[82,50,133,98,49,32,113,64]),(485,[80,81,129,114,50,65,96]),(490,[81,33,80,128,97,114,49,64]),(497,[98,99,81,131,114,65]),(504,[49,50,83,48,130,113,64])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid111 : Known true known111 := extendKnown_ok (m:=111) valid63 low111 (by decide +kernel)
def g189d7 (i : Nat) : Nat := (if i%103=0 then 372523455 else 0)
def g189l7 : Packing := (1,0,3,0,0,0,0,g189d7)
def g189h7 := page #[0x20f801630c00d0,0x42f9f28c081400]
def g189d6 (i : Nat) : Nat := (if i%103=0 then 0x420a3fa41fd10 else 0)
def g189l6 : Packing := (2,1,3,0,0,3,0,g189d6)
def g189h6 (i : Nat) : Nat := (if i%103=0 then 98304 else 0)
def g189d5 (i : Nat) : Nat := (if i%103=0 then 0xb7d8d20 else 0)
def g189l5 : Packing := (1,2,3,0,0,0,0,g189d5)
def g189samples : Array (Bits × Bits) := #[((word [mask72,0xfffffffffffffff55417]),(word [mask72,0xfffffffffffffff46453])),(0x0,0x0),((word [mask72,0xfffffffffffffffc60f7]),0x44076),((word [mask72,0xfffffffffffffff0bbcb]),(word [mask72,0xfffffffffffffff03a89])),(0xf8724,0xb8124),(0x21bb8,0x1ba0),(0x0,0x0),(0xbec28,0xba408),(0x0,0x0)]
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
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem tablesg189 : checkedTables g189 7 := by
  intro k hk
  interval_cases k <;> decide +kernel
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
def g191d10 (i : Nat) : Nat := (if i%103=0 then 8520191 else 0)
def g191l10 : Packing := (1,0,5,0,0,0,0,g191d10)
def g191h10 := page #[0x28c00084a05000089c2a,0xaa3d961388c0f3a00023,0xa68137976081bca199ea,0x15749fa60141c73802b0,0x52f05d5c000e40060800,0x99090000b500000001a1]
def g191d9 := page #[0x20ff4c7fc20ff58ffd40,0xfd10ff54ffe10ff903fe,0xe0bc00ff483fe30ff4c3,0x745a25b53e43cce27c5,0x4038c28424018278d60,0xc0803944862a86148887,0xc0328614b0a030139610,0x936018138408051218b0,0x410102944c300431c508,0x68c2c214019ce18588b2,0x66c008c818588a2e004e,0x288616180c48a11]
def g191l9 : Packing := (12,1,5,0,0,10,0,g191d9)
def g191h9 := page #[0x8b0c0000080000041016,0x60c20000020c70c01c90,0x51841c00801071c964,0x817410814060062c3582,0x30083ad05a1c75006c10,0x24f80000c48dc0005960,0xd7ca82a800f934471820,0x66a9e954000000c99484,0x509c9847ce37e90001c4,0x4200058c80000000001b,0x1906c6000000173ec82c,0x8678cd5b803ae00010d9,0x56d800000000026c2da6,0x14b1d8111aaaac6000,0x731afd48a565b2f86006,0x180a5d34b0ba1360001a,0x2d76000244c429f,0xc38451b04000033fe570,0xc07fc419a5a33000612d,0x5978000750,0x461000000,0x31c60005ad28d4a6000,0x7b00142a8dc0d2c800,0x9e468ae58b600010460,0x60f0f30f9c6d46f8229,0xc890074a5b901b85c19b,0x35c971e4812648c40cf0,0x50153817e93b2ee08a0b,0xa8cb68709baa543933,0x2d70bc0001da504981c0,0x161fd8fb857db1616c,0x60966343d567081fd240,0x37c5c4844130000,0x60000003c50a43a2e72f,0x732e29d36fd3c9ba46,0x6ef8c8000c984c7fad80,0x97c0018068243a2b09f0,0xb6fab800321ac31374a,0x682af90000f688000001,0x800052568158594ec000,0x5cd7a0d113ac27000121,0xa67e35dbbd50001a6c31,0x60840000002a100028,0x39502d60728640000000,0x670800007a7cc632d752,0x63d80a7524800343b41a,0x531e80b64388d000789,0x4e08a520001a51c2000,0x198cb0000a,81920]
def g191d8 := page #[0x58d53501314c12044020,0xfbfdf6ef6f9023088210,0x42b9c86e87ffff7f7efe,0xa286b959ae4e7bb216e2,0xaa64e6ba41eea67b89b2,0xaa9ee0e6b993a4146b8c,0xe9849ae346b8d9ee647b,0x86b8b9ee467bb29ee62,0xeea8c98c2a60c6b921ae,0x59ae50e9811ee4ea9821,0xb9c9ae607b8b1ee088a1,0xa7b909ae2c6ba49aed66,0xe867bb19ae0e6bb51ee2,0x3a2047b92324287b8ba6,0x831ae0c6bad364307b89,0xa983aa6486b951ae707b,0x24e8849aeb66b881ee82,0xae246b94ba4107b92b6e,0x542c490b02c2408c3891,0xb98c2a490b0242c570b1,0x30b0d44651090d4242f0,0xe43090cc6e6509944265,0x424370b12c240d090ac4,0x894240f098cc2a090881,0x98142e430883428431b,0x730b01c220f0b9942c37,0x28051315c2a4b0980c2c,0x42a470a82c2e250b1c4,0x4203883182501880d00,0x8407d87606b86505b851,0x18ca0c08b70ab8a20950,0x91590f1000f10e88dd8d,0x6815a14f94493712b11e,0xa1a399a99498e1839741,0x9e61de9d29cd1c09b21a,0x33a2aa192102069fa9ed,0xa66a5ea54a4d24423c2,0x2b02a2294a8da83a7ca7,0xfcaf62edae72dc2ce2bf,0xab3432bb24b1b311b072,0x373369b6035934fb46b3,0xae3a7b9eb9838f383b7d,0x43e8be1bd8bcf3c73b9b,0x42cc25c1bc12409bfebf,0xc5c5ec5844fc4543ec35,0x414019102020c60a121,0x45209610e8c370084300,0x78110a11258898fc2153,0xbc62448287a25ec8251c,0xf0062ec24c9e99123806,0x860143e0495227c608e,0x68147aaa443fce6009d0,0xd80ec912592247ef00ae,0xc027b211cfe48667a04a,0x2df046e02b7ba00a2fc6,0x319f848269f5444bf229,0xc49103fc0098ee0495c8,0x13808784866ffa009e7,0x4fe00116e08ea457911b,0xed11b79e031029f8122,0x77821af58220f98488d8,0x88527a1372fef00a3701,0x1bbc02b6031f108e8127,0x88648213e1129ec12370,0x27d009160ad1a2b008a3,0xfb0022ff500273ff7802,0x21b80ae446e02b90c91f,0x81b79046f2083ea431f5,0x719314e04222c0974843,0x5433a6477b08ce033e84,0x22c0a32623f7049522d1,0x35cc808a67d091c046f0,0x70221e053c214e043b82,0xc892708574212ef090d6,0x159a24b911ac077e0465,0x1f80354899e077b024a9]
def g191l8 : Packing := (113,2,5,589836,68,12,1057,g191d8)
def g191h8 := page #[0xc0040141188000004000,0xc100000d0040151000,0x402040000c000800708,0xc5040001040080040540,0x70000020001001c02830,0x20788109514708004204,0xc0100242082111047148,0x49ac000c151050440002,0x28964094caf59a8139a1,0x4e1a08c20003c8494d72,0xa860c0656093c9b66e60,0x1ef964fdd2196b35879c,0x23e070c8d80b88940363,0x99d415a6c30450001270,0xdc8e000000426e6c726f,0x621400000000000005b0,0x78000000000000000046,0x23a5319608aa00019134,0xb1c00000000031850,0x283ab340000,0xe93d1260001258003490,0xf85b2554dc0000000f21,0xbc79a059a0f70fccb137,0xb800000009b4c4008e61,0xf1802b07e014cea170ac,0x4d4e9a308f4f4000000e,0x39049a5a1e732518000,0xb0af52342fd8c3fbe11d,0xc0000002c88000000655,0xcd88dae660be94000121,0x4100008f313025a433c0,0x11f8991186d80000014,0x2217770000000a100005,0x5f25c03c4e3ccfe7905e,0xed4e0000001d75e38654,0x58b1c40cba3819701ff1,0x99071c11166c07285d41,0x4f7779436ba625de8998,0x57a00841de8968c753cd,0x109c34616429775d,0xf5bcc02928e3aa852e88,0xf2f6dbb0d3e90a06b82,0x89f7ac18d073c41c5a46,0x3ee488000001119701a1,0xd7a21d0344d98ee80018,0xa6500070140c8d5de5f1,0x8000001bef920589c626,0x5793c3679268754bc618,3724549]
def g191d7 := page #[0x9f7815ca409f581dc163,0x9bf845cd209bf845c131,0x97f855da408fd86dd531,0x9bf845ce10fe120c8610,0x9ef825c5639bf845c163,0x9f7815cd209bf845c153,0xfd5314ca109f7815c520,0xddf714c153ff0714c120,0xdf4715cd20df771dcd20,0xdf583dc520edd6358130,0x9ff815c963bbf845cd10,0xded7248640cfd764ca20,0xfe52048531bf78154131,0xdf7215d210bf78158131,0xbdf8350910bf78148153,0xbf7814ca10ff3714c120,0xbbf845cd20dbd425c640,0xdf471dcd20df77144120,0x9fd82dd1109fd82dd540,0xbbf844c110ff08148230,0xded215ca30df5615d210,0xff110dc520dbf7458130,0x9ff815ca40dbd54dc940,0x9fd81dcd209fd80dc563,0xddf764c1319fd878ca10,0xdf5515c1319fd82dc540,0x9ff815cd20bf78148163,0xdbd425d640df610dd931,0x9fd825c630ded52dc931,0xdf5315ca10df783dc520,0xdf7714c120fe92050910,0xdf551dc131ddd215ce20,0x9fd80dd9319fd82dc563,0xddf714c963df7715cd20,0x9ff805c963aff8654940,0xbbd849c910bf58158e10,0x9fd80dc5539fd81dd530,0xdf9205c630ff21048131,0xb7f85581319fd82dc530,0xdf4815ca40bf9808ca10,0xded20dc963cfd764c620,0x9ff805c5639fd81dd930,0xbf9809c910dbf7454930,0xfd5514c131df97244220,0x9fd8798a409ff815ca20,0xddf714c163bf7815cd20,0xdf7815ca10df7815ca40,0xf755154131bf78148131,0xff210dc5209fd825c640,0xfe92048630df920dc530,0x9ff815c1539fd81dc163,0x9ff815c163df77150120,0xbf7815c520bbf844c120,0x9fd82dd530b7f8558140,0xfe92054930df7715c520,0xaff8654931ff38148230,0x9fd82dc163df5215c620,0xdf4815ca209fd879c910,0x60b81081401e02802800,0xb83085c0ae1482684808,0x608bc15e248428800f61,0x90c20e3e8728d8196318,0x429e5089e93024645888,0x2e628be9782e65b8b095,0x748e29b83666b8d49a43,0x90ea083f67d8f89ec3be,0xaa504969191ca2c44e88,0xa0536a1940a7c4ee9892,0x5b6b3964abc56eaa952a,0x6c998cb0c5febe972ae0,0x39c4b7c6ded69a6b4866,0xecbd479ef09d6ba8736e,0xc1480f009fabe87c6f79,0x8bf14a22c388670ba10,0x601881c21210000,0x848e842005084082000,0x82c41210908000610902,0x408210b0d08400003840,0x42c200002c20410018,0x85060424a100000220d,0x410000c0162410800007,0x6508824200028421,0x4016100604000041288,0x2c340108081882c40001,0x81508808200a8110584,0x48830400208084004181,0x2080083841000000058,0x23042421610002c2161]
def g191l7 : Packing := (116,3,5,0,0,11,0,g191d7)
def g191h7 := page #[0x1c50000042a883a,0xc0062400b2c00a0c8100,0x30450ac641]
def g191d6 := page #[0xc16ea9847de4582dd110,0x419b784dc5734823ef22,0x5183dc5208fb4c0e2b9a,0x290336f0838ae69056de,0xbc26e2982411f79161e6,0x6eaa062fe1b7454930cd,0x93f85dd1604c23ef22c1,0x43ca1408fb4c102b9441,0xdf2b688de65]
def g191l6 : Packing := (12,4,5,0,0,6,0,g191d6)
def g191samples : Array (Bits × Bits) := #[((word [0xfffffffffffffffda8,0xe81df4649a4aea03f353]),(word [424,0x209cc44085084a802052])),((word [0xfffffffffffffffe55,0x627bdd1589ea381610f]),(word [0xfffffffffffffffe55,0xc023b884896b1415109])),((word [184,0x76f0435535c500a8ea8c]),(word [40,0x72300045166108a00a84])),((word [614,0x9d0fd182653b341a80c0]),(word [578,0x8c0bdd82211a84129140])),((word [341,0x4172223bd2f53d4f48e0]),(word [21,0x416022395ae5314d4aa0])),((word [595,0xba08288d622045549630]),(word [592,0x9e022805626105509220])),(0x0,0x0),((word [911,0x1c59fba0814d3746c20]),(word [391,0x1c597ba0892d2056500])),(0x0,0x0)]
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
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem tablesg191 : checkedTables g191 10 := by
  intro k hk
  interval_cases k <;> decide +kernel
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
def g383d12 (i : Nat) : Nat := (if i%103=0 then 6510085375 else 0)
def g383l12 : Packing := (1,0,6,0,0,0,0,g383d12)
def g383h12 := page #[0xc584c000029410000109,0x6790000005048cec0,0xa286e030000000000d80,0x29713b90021c5c400a24,0xe190000e44028954b001,2]
def g383d11 := page #[0xffa61ff443ff187fe10,0x361365e17803fe087fc3,0x61043070d0a08508680,0x70d0e04282102a03050f,0x80850c16042870440440,0xc1800c080840a80c1608,1]
def g383l11 : Packing := (6,1,6,0,0,9,0,g383d11)
def g383h11 := page #[0x70e260404451400410,0x600b00017050301c05,0x4e94b1850b1ad2170101,0xea200000068040000002,0x232a002653d245061c2f,0x984eda4b2e787cc39625,0x991281875380f661504,0x1422051306800005800,0x550007f7944400014100,0x142944000d8a4082dc48,0x62490de02102d21d6156,0x140ac0e19590854ad,0xa02000000274e000193,0xc010b44640b000000000,0x12000f0240555b3c62d0,0x2f40adbada2902700022,0x83401050198b41ca520a,0x19dd990a81d,0x9832241d31f89848e708,0xe0006879dce013000202,0x434126a560a0c97cd1c2,0x1117d3d8e632bfc,0x605ec8c0]
def g383d10 := page #[0xbbebf8c2104c1100c010,0x83c23ffffefbeffbeef7,0xa54180c316c156c104c1,0x98c3dcb839c0b8c1c9c1,0xa8c0d8c188c1d8c0c8c0,0xae40bfb8dbc23cb858c1,0xbeb89e389fc1af98cec1,0xde98ce98df39cf18dec0,0xce41af982fc0bf40bf38,0xcf41aeb8df389e982e39,0xbeb9aeb83eb98e398eb9,0x43084b06209c0e800eb8,0x60f91c23445d09f1081b,0xd2366648b895627049c8,0x532a053124b45a834f71,0x8d81a3b2d618bd16c2b1,0x461a4187eaf6de1ba270,0xe140a0933257c918e31,0x8f861e128c0d84221782,0x850e8b0a261b081c1180,0x2a2e28830c2c20863024,0xc1100200b730408c9018,0x1029a02900f738439af,0x801d311052ae460a7bcd,0x46fdd00eb5019eb3818,0x20a1d72484df882050f8,0xd771046be348414dff08,0x2549ef82c4149a9b213c,0x5139e7a243e4b049e3e7,0x80acf700959fa41af7f1,0x57b044d77c804c7e9c80,0x53e0263c3e095f7f5201,0x139d909a4f77fc62051,0x8a4fd3025756808373fd,0xbba1216fab28127d3e20,0xa0a0caa9a4a646170118,0xff45022545810b0ebed2,2]
def g383l10 : Packing := (47,2,6,524294,51,11,1060,g383d10)
def g383h10 := page #[0xa010e07000000003720,0xd0001020401000400,0x500016400040b010407,0x410100573e0400120007,0x1024c3d0e17000f0511,0x5c082b040301028802,0x340800211f04000c3852,0x1e2f0000390d00040c17,0xc268000e088000143b22,0xc84f7001b077b0900001,0x47e0540003c1d6c17800,0x83218280109ecf40006a,0x10092535383b24a5005e,0x6f32a0420d715820cb28,0x4854e040ddec84110,0xe3171c30000064ac78e8,0x509cd0a402a9482901,0x204071480aad97c1b80,0xd3c31732301838cca179,0x3a10d5060b108505d001,0xc0a907ee0a0fc274022d,0x7802d8c0502fd10109b0,0x3b382b58ee49dec3300d,0x61cf86910f5a5f4b8b23,0x72115827b06218a02035,0x35f0f8311d9031132ca7,0x1825400056b139c293c,0x3e21e71a6056370a0032,0x41e1023c6482e6b2cf06,0xaa808357404e01fd3040,0x4099e8197842301210c9,0x3e60a220d8fa1581020e,0x10a400828f5440c813b8,0x3a9a000d7e20d86d416e,0x16605c32d933682,0x41e7802d68a000000000,0xa41d7010e870e0a60000,0x740833a5880002404721,0x4a410460001715080ea8,0xd07382c4f5400000001,0x3f104c0003fbb8000907,0x6b100000c58000000078,0x4067d0c8043000061b5,0x120000516302b9f10000,0x51cc437e4b4604d43368,0xaae00000001400000000,0xc10b416439d943b147,0x16701f80992cbb03080,0x440b4814a40900000001,0x47b093591c0b42863642,0x997c07b60460002f86e0,0x7e92d81a6801000081e2,0x1b0001e12c0000000f0e,0x417105f0001002bc08ec,0x1a19c0000000f0d80002,0x38c800000000005000,0x10fe000191d80,0x74218000083d74340000,0x207200b0000f03,0x1a60000c095e07a03c80,0x20000000000000000001,0x1fb0faad280000000907,0x606e88fc000242d7c,0x71198115833604b01a0]
def g383d9 (j : Nat) : Nat := (if j<103 then (page #[0x60c10608105cc101cc10,0x61830604305c4301c430,0x5cd104c11020d109c430,0xe0d10cc110a0d1060d10,0x605305c5305c13020530,0x1ce10e1130e0530a0530,0x60e10606105ce104c610,0x5c2304c630cc6109ce10,0x60e3060a30606305c630,0xdc6309c6308c63061e30,0x77def7ddfb7f3fe7dcef,0xdf77ebfcff7feff5fdbf,0xf77deefdbff7f6fddf7b,0x80e51b07291ff6febfbf,0xde1106b22b0998943c91,0x4c555b0f009973ddc194,0xc513f24f0b9815f4bc57,0x4e3f24c3a970dec13d8c,0x77f2460998808ca9a465,0x7306eb784512c83aca44,0xf2853784553c8182661d,0x213c5837e0c0bc2e5c62,0x280998704cb8c2e6194b,0x19f924dcc19226608830,0x3d829e140aac6188772e,0x59411bc2251e61f1f2d0,0x8445bc222c61857b2711,0x159bc8acde1134322bd7,0x1fb9848644e7b050369,0x9c4b86f5cc2173103d82,0x6cb3afa462c1268bd918,0x4c162a612172f0bd9788,0x14c2662673060a590005,0xace60cf232a4259095ec,0xe65c3372688b976da48,0x2e5cc7ce6137946d3c83,0x66176322389989d3c83c,0x51382e23159451dc19c2,0xd58302aba833c4cc325e,0x513308c2711a9cabe265,0xc2628b983612c82e3e58,0xb0528b970cfc91846550,0x30937948c5c8c8266017,0x8982c5cc022660411,0x6a997744cc1735c27133,0xab97614cb9ca65cf532e,0xb97315cb95261d8532e4,0x97424c0b9261cf970e52,0x18e4c0b36e11290e6d29,0x4083302901a80c000497,0x187906e06905c05604e0,0x8c70b88aa8a109788d88,0x109080fd8f80ef0e18d4,0x894e14513b92b1229191,0x18f98618097996c96115,0xdc1cc9be1b89ac1a5199,0x9a1f211a061fb9f29e39,0xa74a6ba5d251a49237a2,0xbcab6aae2a129328a280,0x7af72efae7ade2d5ac72,0xb4ab4433833132231730,0x8c37fb78b73b6635fb58,0x23b73b1ba83a13973923,0xbf9beb3e4bddbd73cc3c,0x37c2fc26c1ec1440dc02,0x7c70c66c60c57c514424,0xcb4cab49f497c8747fc7,0xe5cdecd84d14ca4c34bc,0x7d1c513d084fe4f74f14,0x441e0b05549d41d33d2,0xb05c2684e0814120e02,0x84a282029c2038483304,0x21c0109148e1a8287387,0x1e8cc2c288d0b416286c,0xfd088c0683056b01e8ec,0x5a38918c18c308840c70,0x22efe0c114fda095822,0x843247a20643ec231f50,0xc021f5491180a7108bc,0x6b88877f60496e239ac5,0x30932fde02207c239908,0x804abea9226f20245bf6,0x6f1097a08640ab2623f9,0xe3c9046de215e623de21,0xb811dee091ec041cc873,0xd011c06bd692267e463,0x911e02bfb8240e4c4399,0xd7c922807c0191010fa1,0x864391ec72208d390a7,0x7b82425ed04f3d690c2f,0xbc4213fdaa08c1dec4c9,0xb1df4473c74045ae40c7,0xad93564ac98ac1927756,0x4171411812e90b633045,0x6b2083990d70859f2226,0x49ce0e08c5fc120656c0,0x89912c221f5c0114f242,0x95406f016f31822b00f7,0x80bbc34c65818045e5f0,0x32053910ce223b024009,0x44204dfc10cf28937f04,0x321d6cc55f504646019c,0x90c4083f] j) else (page #[0x7c8877046f6022e212f4,0x200235c08603afc00190,0x46065d28576447019d81,0x29f023bd8325d2859f4,0x12c08e223888e2258134,0xef1090e22602dc5c8871,0xe04c73d81137085d8158,0x3fc480cb7845bfa208a1,2] j))
def g383l9 : Packing := (136,3,6,1638440,86,12,1083,g383d9)
def g383h9 := page #[0x400010000a42100804,0x8a66108200840810540,0x9ed0240cf0c80400004d,0x1811720991cb65f65399,0x8b4800e1d917e0164058,0x1daa0990d5,0xf0400014320000000000,0x8a9c416408c84be1fb32,0x5b907440e6c7f8b08b06,0x5a000677800202f02991,0x19a8a1e8a227410f8051,0x6e970739878c268f43,0x403589000181590e60c4,0xb41000000066c401a931,0x40895c7d1f430452c83,0xa0000000103800000000,0xb000184b4aa00070df9,0x972c28000915083d009e,0xa16f054]
def g383d8 := page #[0x901cc108fb6a3924c630,0xccfe57845c130cee611,0x597e0530aebe919360a3,0x30ceb651821cc108dfe9,0x869760a308ef6a784a05,0x430aeb6929760a30af96,0xa869760a30add6967160,0xd10cfa609908c630af9,0xf69491e11308f7ea5832,0x60c108bf6a3965c430ac,0xebe139260530ad769497,0x85c630c9f655869c430c,0x8bfe9b985c4308bfe999,0x985ce108fb6a582dc630,0xceb651828c6308efe91,0x99760430af36889760c1,0x308efe91989ce108bfe9,0x59825c6308fb68b9161e,0x130af66809760c10cbbe,0xe539260d10aebe8991e1,0xc630cfa609901cc10ceb,0xfe119520530cdb655829,0x60a30cafe5b845c530cc,0xbf69a985c530afa68297,0x41c4308fbe89985cd108,0x8fb689981cc10caf6199,0x81205308efe91985c130,0xf745c5315c1308fdea5,0x79460e10cdb655821cc1,0x10adfe9587e0d10cef5c,0xc79460e30cfb61f924c6,0x810cefe119720530cef5,0x69c91e1130afb68f7360,0xc530cefe1f944c110aef,0x28118781e00dafe5b845,0x3696439b8be50258f05a,0x71aed266b2186be57aa9,0x9c3a13047fbe9eaf070b,0x8acd529f4a9dcda4f228,0x3ccdeebb539ac5dcadb6,0x400001e10283e0edf5ba,0x819120810282002820c8,0x141001e10108102,0xa100000000005040000,0xc840000161001e103,0x58408185082e10440a10,0xa10200000e08]
def g383l8 : Packing := (53,4,6,0,0,9,0,g383d8)
def g383h8 (i : Nat) : Nat := (if i%103=0 then 0x834601a000 else 0)
def g383d7 := page #[0x70852bfb65c79460e30,0xa295fdb2e3ca3]
def g383l7 : Packing := (2,5,6,0,0,3,0,g383d7)
def g383samples : Array (Bits × Bits) := #[((word [0xffffffffffffffd8fd,0x630dda8e8aa61c90014d]),(word [0xffffffffffffffd8d4,0x2304082801a102900145])),((word [10082,0xdfc636db2d3474067090]),(word [8480,0xd82a34960818c4045090])),((word [16065,0x918c681557416c0816]),(word [7873,0x818829154701680800])),((word [412,0xee55353e34c9ba0a86e6]),(word [14,0xea5424062a80ba0284c6])),((word [14113,0x940b48c0c06e80091ef8]),(word [10017,0x140b40c0c04e00091a38])),((word [782,0x98f28487160298718700]),(word [778,0x98f08487160298418600])),((word [0xffffffffffffffcace,0xa51892172a62383f801]),(word [2766,0x2d1892132a62281a800])),(0x0,0x0),((word [0xfffffffffffffffc31,0x35226350618b47fd9801]),(word [0xfffffffffffffff431,0x5024250c159053c1001]))]
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
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem tablesg383 : checkedTables g383 12 := by
  intro k hk
  interval_cases k <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low383 : Lower true (vars 383) (graphGoal 383) 13 := plain_low (hints:=12901687553) (by decide +kernel) (index_root (g:=g383) (i:=0) rfl rfl (before_sound known255 valid255) geomg383 tablesg383 (by decide +kernel))
def known383 := extendKnown known255 13 [(383,[]),(447,[98,118,81,130,50,65]),(495,[116,83,32])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid383 : Known true known383 := extendKnown_ok (m:=383) valid255 low383 (by decide +kernel)
theorem validF : Known false known383 := known_down valid383
def x31d6 (i : Nat) : Nat := (if i%103=0 then 0x1a230180fd10fc20 else 0)
def x31l6 : Packing := (2,1,2,0,0,4,0,x31d6)
def x31h6 := page #[0x202082101c0c0071400,0x104451000a020]
def x31d5 := page #[0x7d53082faa4885f54420,0xe3d4507e48110bea9a21,0x613110000]
def x31l5 : Packing := (5,2,2,0,0,5,0,x31d5)
def x31samples : Array (Bits × Bits) := #[((word [mask72,0xfffffffffffffffffc47]),0xa86),((word [mask72,0xfffffffffffffffff09b]),(word [mask72,0xfffffffffffffffff531])),(0x29c,0x8cc),((word [mask72,0xfffffffffffffffff327]),(word [mask72,0xfffffffffffffffff303])),(0xd78,0x478),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def x31columns : List ColumnInfo := [(1,0,30,0,4),(16,0,15,0,4),(8,0,23,0,4),(4,0,27,0,4)]
def x31autos : List (List Nat) := [[],[65,50],[16,66],[16,32,48,64],[32,67],[32,49,64,16],[48,33],[48,65,32,33],[64,16,33,50],[64,49]]
def x31levels : Nat → Packing
  | 6 => x31l6
  | 5 => x31l5
  | _ => emptyPacking
def x31index : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 8 11 1 11 3 4 x31h6
  | _ => fun _ => none
def x31 : Forest := ⟨1055,6,fun j => x31samples[j]?.getD (0,0),x31columns,x31autos,x31levels,x31index⟩
set_option maxHeartbeats 0 in
theorem geomx31 : graphValid x31 (boundsBefore known383) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,listPieces_all (d:=1) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem tablesx31 : checkedTables x31 6 := by
  intro k hk
  interval_cases k <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem pl31 : Impossible false (graphGoal 1055) 6 (vars 1055).toFinset := plainA (q:=31) (prior:=boundsBefore known383) (before_sound known383 validF) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low1567 : Lower false (varsX 1567) (graphGoal 1567) 7 :=
  strong_full (q:=1055) (rs:=[2, 1, 2, 4, 1]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl31
    (index_root (g:=x31) (i:=0) rfl rfl (before_sound known383 validF) geomx31 tablesx31 (by decide +kernel))
def known1567 := extendKnown known383 7 [(1567,[]),(2079,[50,65]),(6687,[50,33,16,64]),(7199,[66,16]),(1703,[115,67,100,83]),(4263,[114,33,97,82,50,65]),(7847,[115,50,98,83,66,16]),(12455,[113,97,82,32,65,48]),(2361,[131,115,65,50,98,81]),(6990,[131,115,100,50,33,16,80]),(4963,[130,33,113,99,82,65]),(9571,[130,33,50,113,99,82,16,64])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid1567 : Known false known1567 := extendKnown_ok (m:=1567) validF low1567 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low42527 : Lower false (varsX 42527) (graphGoal 42527) 7 :=
  strong_full (q:=1055) (rs:=[2, 1, 2, 4, 1]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl31
    (index_root (g:=x31) (i:=1) rfl rfl (before_sound known383 validF) geomx31 tablesx31 (by decide +kernel))
def known42527 := extendKnown known1567 7 [(42527,[]),(44063,[50,65]),(47647,[50,33,16,64]),(52767,[33,32,65,48]),(57887,[16,64,49,32]),(42663,[115,67,100,83]),(44711,[114,33,97,82,50,65]),(47783,[114,98,83,33,16,64]),(54951,[113,97,82,32,65,48]),(68775,[113,16,96,81,49,64]),(44345,[131,115,65,50,98,81]),(60217,[129,113,33,98,81,48]),(53070,[130,114,99,49,32,65,80]),(60238,[129,113,98,16,66,49,80]),(42851,[131,50,66,116,99,82]),(44899,[130,33,113,99,82,65]),(50019,[130,33,50,113,99,82,16,64]),(53164,[130,50,116,49,32,97,80]),(60332,[129,50,114,48,66,97,80]),(69548,[129,116,50,97,80])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid42527 : Known false known42527 := extendKnown_ok (m:=42527) valid1567 low42527 (by decide +kernel)
def x111d6 (i : Nat) : Nat := (if i%103=0 then 0x1040a3fa21fd51 else 0)
def x111l6 : Packing := (2,1,1,0,0,3,0,x111d6)
def x111h6 (i : Nat) : Nat := (if i%103=0 then 262144 else 0)
def x111d5 (i : Nat) : Nat := (if i%103=0 then 69489475856 else 0)
def x111l5 : Packing := (1,2,1,0,0,0,0,x111d5)
def x111samples : Array (Bits × Bits) := #[((word [mask72,0xfffffffffffffffff9b5]),0xe94),((word [mask72,0xfffffffffffffffff0db]),(word [mask72,0xfffffffffffffffff10b])),(0x602,0xa80),(0x614,0x514),(0x0,0x0),(0x964,0x160),(0x78,0xef0),(0x0,0x0),(0x0,0x0)]
def x111columns : List ColumnInfo := [(96,0,15,0,4),(1,32,78,0,4)]
def x111autos : List (List Nat) := [[],[32,83]]
def x111levels : Nat → Packing
  | 6 => x111l6
  | 5 => x111l5
  | _ => emptyPacking
def x111index : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 3 1 6 1 1 x111h6
  | _ => fun _ => none
def x111 : Forest := ⟨1135,6,fun j => x111samples[j]?.getD (0,0),x111columns,x111autos,x111levels,x111index⟩
set_option maxHeartbeats 0 in
theorem geomx111 : graphValid x111 (boundsBefore known42527) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem tablesx111 : checkedTables x111 6 := by
  intro k hk
  interval_cases k <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem pl111 : Impossible false (graphGoal 1135) 6 (vars 1135).toFinset := plainA (q:=111) (prior:=boundsBefore known42527) (before_sound known42527 valid42527) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low49775 : Lower false (varsX 49775) (graphGoal 49775) 7 :=
  strong_full (q:=1135) (rs:=[2, 64, 2, 4, 1, 2]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl111
    (index_root (g:=x111) (i:=0) rfl rfl (before_sound known42527 valid42527) geomx111 tablesx111 (by decide +kernel))
def known49775 := extendKnown known42527 7 [(42683,[117,80,66,96,16]),(47806,[114,83,48,33,97,64]),(69498,[129,33,97,81,16,114,49,64]),(69557,[134,81,114,50,65])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid49775 : Known false known49775 := extendKnown_ok (m:=49775) valid42527 low49775 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low42607 : Lower false (varsX 42607) (graphGoal 42607) 7 :=
  strong_full (q:=1135) (rs:=[2, 1, 2, 4, 1, 2]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl111
    (index_root (g:=x111) (i:=1) rfl rfl (before_sound known42527 valid42527) geomx111 tablesx111 (by decide +kernel))
def known42607 := extendKnown known49775 7 [(44155,[99,83,64,32,16]),(44219,[115,50,32,83,66,96,16]),(44731,[117,80,66,96,16]),(52926,[114,83,48,33,97,64]),(54974,[112,48,50,33,97,64]),(42711,[115,83,67]),(47838,[101,117,50,33,16,64]),(52958,[99,115,83,48,33,64]),(42739,[82,98,115,66,16]),(44787,[83,80,96,115,64,32,16]),(53054,[130,114,98,49,32,81,64]),(60253,[128,80,117,32,16,98,65,48]),(60282,[129,33,97,81,16,114,49,64]),(44981,[134,81,114,50,65]),(48071,[83,133,115,67,32,96]),(53212,[82,50,133,98,49,32,113,64]),(60408,[49,50,83,48,130,113,64]),(69624,[81,80,48,50,130,113,64])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid42607 : Known false known42607 := extendKnown_ok (m:=42607) valid49775 low42607 (by decide +kernel)
def x63d7 (i : Nat) : Nat := (if i%103=0 then 0x344640ac3f865fc10 else 0)
def x63l7 : Packing := (2,1,2,0,0,4,0,x63d7)
def x63h7 := page #[0xf391436008009b010,0x5d46b7171000680020c0,5670730200]
def x63d6 := page #[0xb58810af59010b758c10,0x580329f59410bd58432b,0x8c10bf590109f59432be,0x32fd4c410bf58032bf5,0xe4b74a0b44658480fb48,0x23211880840401f7cb4,0x1108482000804c8462]
def x63l6 : Packing := (12,2,2,0,0,7,0,x63d6)
def x63h6 (i : Nat) : Nat := (if i%103=0 then 0x24f9400060ba8030352 else 0)
def x63d5 := page #[0xb5a98ac8086e53158810,0x2cea62b2821b54c1610c,0x3e498240196e5205843,0x8421184210872a1e50a,1]
def x63l5 : Packing := (6,3,2,0,0,6,0,x63d5)
def x63h5 (i : Nat) : Nat := (if i%103=0 then 537083904 else 0)
def x63d4 (i : Nat) : Nat := (if i%103=0 then 0x3b04813058432 else 0)
def x63l4 : Packing := (1,4,2,0,0,0,0,x63d4)
def x63samples : Array (Bits × Bits) := #[((word [mask72,0xffffffffffffffff209f]),0xd8096),((word [mask72,0xfffffffffffffff19c61]),(word [mask72,0xfffffffffffffff03861])),(0x97be,0x2c69c),((word [mask72,0xfffffffffffffff04b47]),(word [mask72,0xfffffffffffffffd3903])),(0x44c78,0x24468),(0xa2f80,0x27f00),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def x63columns : List ColumnInfo := [(1,32,30,0,4),(6,0,57,0,4),(40,0,23,0,4),(24,0,39,0,4)]
def x63autos : List (List Nat) := [[],[65,50]]
def x63levels : Nat → Packing
  | 7 => x63l7
  | 6 => x63l6
  | 5 => x63l5
  | 4 => x63l4
  | _ => emptyPacking
def x63index : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 7 21 2 9 4 1 x63h7
  | 6 => lookupWord 2 9 1 8 3 1 x63h6
  | 5 => lookupWord 1 5 1 6 1 1 x63h5
  | _ => fun _ => none
def x63 : Forest := ⟨1087,7,fun j => x63samples[j]?.getD (0,0),x63columns,x63autos,x63levels,x63index⟩
set_option maxHeartbeats 0 in
theorem geomx63 : graphValid x63 (boundsBefore known42607) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem tablesx63 : checkedTables x63 7 := by
  intro k hk
  interval_cases k <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem pl63 : Impossible false (graphGoal 1087) 7 (vars 1087).toFinset := plainA (q:=63) (prior:=boundsBefore known42607) (before_sound known42607 valid42607) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low6719 : Lower false (varsX 6719) (graphGoal 6719) 8 :=
  strong_full (q:=1087) (rs:=[2, 1, 2, 4, 1, 1]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl63
    (cut_root (prior:=boundsBefore known42607) (before_sound known42607 valid42607) (6688,0,6687,0,7) (by decide +kernel) (by decide +kernel))
def known6719 := extendKnown known42607 8 [(2143,[101,66,16]),(2425,[128,80,84,66,16,114,97,48])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid6719 : Known false known6719 := extendKnown_ok (m:=6719) valid42607 low6719 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low1087 : Lower false (varsX 1087) (graphGoal 1087) 8 :=
  strong_full (q:=1087) (rs:=[16, 4, 2, 4, 1, 1]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl63
    (index_root (g:=x63) (i:=0) rfl rfl (before_sound known42607 valid42607) geomx63 tablesx63 (by decide +kernel))
def known1087 := extendKnown known6719 8 [(1087,[]),(2623,[50,65]),(1119,[101,66,16]),(6303,[117,101,67,32]),(11423,[117,101,33,32,65,48]),(6319,[116,100,83,32]),(13487,[113,97,82,32,65,48]),(1207,[115,84,99]),(3255,[114,81,98,50,65]),(1255,[83,82,114,99,66,16]),(18749,[129,113,82,97,48]),(11614,[132,116,84,48,33,96]),(18782,[129,33,114,82,16,66,49,96]),(18798,[128,64,116,49,96]),(1395,[131,84,115,98]),(18809,[128,80,84,66,16,114,97,48]),(11708,[132,67,84,48,33,113,96]),(3555,[83,80,132,115,96,32,16])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid1087 : Known false known1087 := extendKnown_ok (m:=1087) valid6719 low1087 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low11327 : Lower false (varsX 11327) (graphGoal 11327) 8 :=
  strong_full (q:=1087) (rs:=[2, 1, 2, 16, 1, 1]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl63
    (index_root (g:=x63) (i:=1) rfl rfl (before_sound known42607 valid42607) geomx63 tablesx63 (by decide +kernel))
def known11327 := extendKnown known1087 8 [(2719,[117,101,67,32]),(13495,[115,84,99]),(3389,[132,116,65,48,80,97,32]),(8542,[132,116,84,48,33,96])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid11327 : Known false known11327 := extendKnown_ok (m:=11327) valid1087 low11327 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low1599 : Lower false (varsX 1599) (graphGoal 1599) 8 :=
  strong_full (q:=1087) (rs:=[2, 1, 2, 4, 1, 1]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl63
    (cut_root (prior:=boundsBefore known42607) (before_sound known42607 valid42607) (1568,0,1567,0,7) (by decide +kernel) (by decide +kernel))
def known1599 := extendKnown known11327 8 [(1599,[]),(12463,[113,97,82,32,65,48]),(1719,[115,84,99]),(2365,[132,116,65,48,80,97,32]),(9582,[128,16,113,65,49,33,96]),(4979,[130,50,81,115,98,65])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid1599 : Known false known1599 := extendKnown_ok (m:=1599) valid11327 low1599 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low47679 : Lower false (varsX 47679) (graphGoal 47679) 8 :=
  strong_full (q:=1087) (rs:=[2, 4, 2, 4, 1, 1]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl63
    (cut_root (prior:=boundsBefore known42607) (before_sound known42607 valid42607) (47648,0,47647,0,7) (by decide +kernel) (by decide +kernel))
def known47679 := extendKnown known1599 8 [(47679,[]),(44127,[101,66,16]),(52831,[101,50,33,16,64]),(42671,[116,100,83,32]),(68783,[113,97,82,32,65,48]),(47799,[115,84,99]),(68791,[114,81,98,50,65]),(44349,[132,116,65,48,80,97,32]),(60366,[82,50,133,115,49,32,65,96])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid47679 : Known false known47679 := extendKnown_ok (m:=47679) valid1599 low47679 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low42559 : Lower false (varsX 42559) (graphGoal 42559) 8 :=
  strong_full (q:=1087) (rs:=[2, 1, 2, 4, 1, 1]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl63
    (cut_root (prior:=boundsBefore known42607) (before_sound known42607 valid42607) (42528,0,42527,0,7) (by decide +kernel) (by decide +kernel))
def known42559 := extendKnown known47679 8 [(42559,[]),(42591,[101,66,16]),(47791,[116,100,83,32]),(54959,[113,97,82,32,65,48]),(42679,[115,84,99]),(44727,[114,81,98,50,65]),(60270,[128,64,116,49,96]),(60281,[128,80,84,66,16,114,97,48]),(69497,[128,81,67,112,97,32]),(48078,[83,133,115,67,32,96]),(69603,[81,80,128,113,98,49,64])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid42559 : Known false known42559 := extendKnown_ok (m:=42559) valid47679 low42559 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low52799 : Lower false (varsX 52799) (graphGoal 52799) 8 :=
  strong_full (q:=1087) (rs:=[2, 1, 8, 4, 1, 1]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl63
    (cut_root (prior:=boundsBefore known42607) (before_sound known42607 valid42607) (52768,0,52767,0,7) (by decide +kernel) (by decide +kernel))
def known52799 := extendKnown known42559 8 [(44719,[116,100,83,32]),(54967,[115,84,99]),(60239,[131,115,100,50,33,16,80]),(50014,[132,116,84,48,33,96])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid52799 : Known false known52799 := extendKnown_ok (m:=52799) valid42559 low52799 (by decide +kernel)
def x189d7 := page #[0xd30fe887f0c3f821fc20,0x90c808420380cd31101f,0x81511080]
def x189l7 : Packing := (5,1,3,0,0,7,0,x189d7)
def x189h7 := page #[0x24814000001004000000,0x38579507803705e04820,0x8c06fa80010259096700,0x800000a71f0200000082,0x15c76e77000000818435,7614597]
def x189d6 := page #[0xf59420bb58830bd58430,0x48110bf58930bf594209,0x8910bf58430fe54030fe,0xf19283c280fe48130bf5,0x421000040820b764a0,1082400]
def x189l6 : Packing := (10,2,3,0,0,7,0,x189d6)
def x189h6 := page #[0xddd0800002,0x70000904]
def x189d5 := page #[0x36698ac4186f15058430,0x104208141ba541620c]
def x189l5 : Packing := (3,3,3,0,0,5,0,x189d5)
def x189samples : Array (Bits × Bits) := #[((word [mask72,0xfffffffffffffff1880f]),(word [mask72,0xfffffffffffffffe600d])),(0x0,0x0),((word [mask72,0xfffffffffffffff2619f]),0x2a10e),((word [mask72,0xfffffffffffffff60271]),(word [mask72,0xfffffffffffffffc5851])),(0x507e6,0x187a2),(0x89c78,0x9870),(0x0,0x0),(0x87780,0xd4680),(0x0,0x0)]
def x189columns : List ColumnInfo := [(33,0,156,0,4),(24,0,165,0,4),(12,0,177,0,4),(132,0,57,0,4),(17,0,172,0,4),(160,0,29,0,4)]
def x189autos : List (List Nat) := [[],[115,84],[32,67,117],[32,83,116],[48,82],[48,82,112,66],[64,114,50,48,80],[64,114,83],[80,50,116],[80,50,66,32,114],[112,66,48,82],[112,66]]
def x189levels : Nat → Packing
  | 7 => x189l7
  | 6 => x189l6
  | 5 => x189l5
  | _ => emptyPacking
def x189index : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 23 29 4 12 4 4 x189h7
  | 6 => lookupWord 2 11 1 10 2 4 x189h6
  | _ => fun _ => none
def x189 : Forest := ⟨1213,7,fun j => x189samples[j]?.getD (0,0),x189columns,x189autos,x189levels,x189index⟩
set_option maxHeartbeats 0 in
theorem geomx189 : graphValid x189 (boundsBefore known52799) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=1) ?_⟩,listPieces_all (d:=2) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem tablesx189 : checkedTables x189 7 := by
  intro k hk
  interval_cases k <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem pl189 : Impossible false (graphGoal 1213) 7 (vars 1213).toFinset := plainA (q:=189) (prior:=boundsBefore known52799) (before_sound known52799 valid52799) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low2237 : Lower false (varsX 2237) (graphGoal 2237) 8 :=
  strong_full (q:=1213) (rs:=[16, 8, 4, 1, 1, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl189
    (index_root (g:=x189) (i:=0) rfl rfl (before_sound known52799 valid52799) geomx189 tablesx189 (by decide +kernel))
def known2237 := extendKnown known52799 8 [(2237,[]),(18109,[82,48,66,112]),(2395,[130,114,98,33,81]),(12774,[66,114,50,132,99,32,80,16])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid2237 : Known false known2237 := extendKnown_ok (m:=2237) valid52799 low2237 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low1725 : Lower false (varsX 1725) (graphGoal 1725) 8 :=
  strong_full (q:=1213) (rs:=[16, 8, 4, 1, 1, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl189
    (index_root (g:=x189) (i:=1) rfl rfl (before_sound known52799 valid52799) geomx189 tablesx189 (by decide +kernel))
def known1725 := extendKnown known2237 8 [(1725,[]),(17085,[82,48])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid1725 : Known false known1725 := extendKnown_ok (m:=1725) valid2237 low1725 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low2749 : Lower false (varsX 2749) (graphGoal 2749) 8 :=
  strong_full (q:=1213) (rs:=[32, 8, 4, 8, 1, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl189
    (index_root (g:=x189) (i:=2) rfl rfl (before_sound known52799 valid52799) geomx189 tablesx189 (by decide +kernel))
def known2749 := extendKnown known1725 8 [(2749,[]),(11453,[117,67,32]),(1371,[130,50,98,82,115,33,65]),(6630,[115,83,82,130,99,66,16]),(13798,[66,114,50,132,99,32,80,16])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid2749 : Known false known2749 := extendKnown_ok (m:=2749) valid1725 low2749 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low43197 : Lower false (varsX 43197) (graphGoal 43197) 8 :=
  strong_full (q:=1213) (rs:=[20, 9, 4, 1, 1, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl189
    (index_root (g:=x189) (i:=3) rfl rfl (before_sound known52799 valid52799) geomx189 tablesx189 (by decide +kernel))
def known43197 := extendKnown known2749 8 [(43197,[]),(58557,[82,48]),(64189,[83,114,64]),(43823,[135,50,65]),(46427,[130,50,98,82,115,33,65]),(48475,[135,101,50,33,16,64]),(49638,[115,83,82,130,99,66,16]),(55782,[117,130,99,32,64,16])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid43197 : Known false known43197 := extendKnown_ok (m:=43197) valid2749 low43197 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low44221 : Lower false (varsX 44221) (graphGoal 44221) 8 :=
  strong_full (q:=1213) (rs:=[16, 8, 4, 1, 1, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl189
    (index_root (g:=x189) (i:=4) rfl rfl (before_sound known52799 valid52799) geomx189 tablesx189 (by decide +kernel))
def known44221 := extendKnown known43197 8 [(44221,[]),(44733,[84,115]),(52925,[117,67,32]),(54973,[116,83,32]),(58045,[82,48]),(60207,[132,65,48,80,113,32]),(42843,[130,50,98,82,115,33,65]),(44379,[130,114,98,33,81]),(58203,[133,117,101,33,48]),(48102,[115,83,82,130,99,66,16]),(55270,[66,114,50,132,99,32,80,16]),(69606,[80,132,99,112,32,16])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid44221 : Known false known44221 := extendKnown_ok (m:=44221) valid43197 low44221 (by decide +kernel)
def x251d7 (i : Nat) : Nat := (if i%103=0 then 0x60bfd31 else 0)
def x251l7 : Packing := (1,1,1,0,0,0,0,x251d7)
def x251samples : Array (Bits × Bits) := #[((word [mask72,0xfffffffffffffffffc91]),(word [mask72,0xfffffffffffffffffc01])),(0xe,0x2ee),(0x0,0x0),(0x64,0x2a4),(0x72,0x152),((word [mask72,0xffffffffffffffffff8d]),0x1ac),(0x16,0x110),(0x318,0x250),(0x0,0x0)]
def x251columns : List ColumnInfo := [(88,0,163,0,4),(8,0,243,0,7)]
def x251autos : List (List Nat) := [[],[115,84],[65,99],[65,115,81,99],[81,118],[81,99,65,115]]
def x251levels : Nat → Packing
  | 7 => x251l7
  | _ => emptyPacking
def x251index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def x251 : Forest := ⟨1275,7,fun j => x251samples[j]?.getD (0,0),x251columns,x251autos,x251levels,x251index⟩
set_option maxHeartbeats 0 in
theorem geomx251 : graphValid x251 (boundsBefore known44221) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,listPieces_all (d:=1) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem tablesx251 : checkedTables x251 7 := by
  intro k hk
  interval_cases k <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem pl251 : Impossible false (graphGoal 1275) 7 (vars 1275).toFinset := plainA (q:=251) (prior:=boundsBefore known44221) (before_sound known44221 valid44221) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low48891 : Lower false (varsX 48891) (graphGoal 48891) 8 :=
  strong_full (q:=1275) (rs:=[2, 80, 16, 10, 1, 2, 32]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl251
    (index_root (g:=x251) (i:=0) rfl rfl (before_sound known44221 valid44221) geomx251 tablesx251 (by decide +kernel))
def known48891 := extendKnown known44221 8 [(59646,[116,100,49,81,32]),(43479,[115,83,133,99,50,66,16]),(55773,[99,132,84,48,33,112]),(46581,[67,80,100,131,112,32,16]),(58874,[84,100,49,128,113,32])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid48891 : Known false known48891 := extendKnown_ok (m:=48891) valid44221 low48891 (by decide +kernel)
def x127d8 (i : Nat) : Nat := (if i%103=0 then 0x1948817fd30 else 0)
def x127l8 : Packing := (1,1,3,0,0,0,0,x127d8)
def x127h8 (i : Nat) : Nat := (if i%103=0 then 36480 else 0)
def x127d7 := page #[0x243a037eb0261df54530,2409065]
def x127l7 : Packing := (2,2,3,0,0,5,0,x127d7)
def x127samples : Array (Bits × Bits) := #[((word [mask72,0xffffffffffffffff22a7]),(word [mask72,0xffffffffffffffffa027])),((word [mask72,0xffffffffffffffff4759]),0x4258),(0x942e,0x8424),((word [mask72,0xffffffffffffffff99d3]),(word [mask72,0xffffffffffffffff3bd3])),(0x81c,0x4408),(0x21a0,0x5f80),(0x41c0,0xbd80),(0x0,0x0),(0x0,0x0)]
def x127columns : List ColumnInfo := [(20,8,99,0,4),(96,0,31,0,7),(16,0,111,0,7),(66,0,61,0,5),(34,64,29,0,4),(1056,0,1119,0,8),(49,0,78,0,4)]
def x127autos : List (List Nat) := [[],[16,66,101]]
def x127levels : Nat → Packing
  | 8 => x127l8
  | 7 => x127l7
  | _ => emptyPacking
def x127index : Nat → Nat → Option (Nat × Nat)
  | 8 => lookupWord 1 3 1 6 1 1 x127h8
  | _ => fun _ => none
def x127 : Forest := ⟨1151,8,fun j => x127samples[j]?.getD (0,0),x127columns,x127autos,x127levels,x127index⟩
set_option maxHeartbeats 0 in
theorem geomx127 : graphValid x127 (boundsBefore known48891) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=1) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem tablesx127 : checkedTables x127 8 := by
  intro k hk
  interval_cases k <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem pl127 : Impossible false (graphGoal 1151) 8 (vars 1151).toFinset := plainA (q:=127) (prior:=boundsBefore known48891) (before_sound known48891 valid48891) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low2175 : Lower false (varsX 2175) (graphGoal 2175) 9 :=
  strong_full (q:=1151) (rs:=[2, 1, 2, 4, 1, 1, 2]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl127
    (cut_root (prior:=boundsBefore known48891) (before_sound known48891 valid48891) (2080,0,2143,0,8) (by decide +kernel) (by decide +kernel))
def known2175 := extendKnown known48891 9 [(2429,[129,82,113,48]),(7038,[129,98,82,16,66,49,112]),(9598,[128,100,49,112])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid2175 : Known false known2175 := extendKnown_ok (m:=2175) valid48891 low2175 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low1151 : Lower false (varsX 1151) (graphGoal 1151) 9 :=
  strong_full (q:=1151) (rs:=[16, 4, 2, 4, 1, 1, 2]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl127
    (cut_root (prior:=boundsBefore known48891) (before_sound known48891 valid48891) (1056,0,1119,0,8) (by decide +kernel) (by decide +kernel))
def known1151 := extendKnown known2175 9 [(18814,[129,98,82,16,66,49,112]),(11742,[82,133,99,49,32,65,112])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid1151 : Known false known1151 := extendKnown_ok (m:=1151) valid2175 low1151 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low52863 : Lower false (varsX 52863) (graphGoal 52863) 9 :=
  strong_full (q:=1151) (rs:=[2, 1, 8, 4, 1, 1, 2]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl127
    (cut_root (prior:=boundsBefore known48891) (before_sound known48891 valid48891) (52768,0,52831,0,8) (by decide +kernel) (by decide +kernel))
def known52863 := extendKnown known1151 9 [(44925,[129,82,113,48]),(50046,[129,98,82,16,66,49,112])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid52863 : Known false known52863 := extendKnown_ok (m:=52863) valid1151 low52863 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low44159 : Lower false (varsX 44159) (graphGoal 44159) 9 :=
  strong_full (q:=1151) (rs:=[16, 1, 2, 4, 1, 1, 2]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl127
    (cut_root (prior:=boundsBefore known48891) (before_sound known48891 valid48891) (44064,0,44127,0,8) (by decide +kernel) (by decide +kernel))
def known44159 := extendKnown known52863 9 [(44159,[]),(47743,[101,66,16]),(69501,[128,84,66,16,98,113,48]),(74110,[128,100,49,112]),(48094,[82,133,99,49,32,65,112])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid44159 : Known false known44159 := extendKnown_ok (m:=44159) valid52863 low44159 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low43647 : Lower false (varsX 43647) (graphGoal 43647) 9 :=
  strong_full (q:=1151) (rs:=[10, 1, 2, 5, 1, 1, 2]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl127
    (index_root (g:=x127) (i:=0) rfl rfl (before_sound known48891 valid48891) geomx127 tablesx127 (by decide +kernel))
def known43647 := extendKnown known44159 9 [(43647,[]),(46455,[131,84,115,98]),(51063,[131,100,115,82,16]),(43901,[129,82,113,48]),(46461,[128,84,66,16,98,113,48]),(48510,[129,98,82,16,66,49,112]),(51070,[128,100,49,112]),(43423,[134,117,33,32,65,48]),(58811,[84,133,80,66,114,96,16]),(59900,[82,48,66,129,112])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid43647 : Known false known43647 := extendKnown_ok (m:=43647) valid44159 low43647 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low42623 : Lower false (varsX 42623) (graphGoal 42623) 9 :=
  strong_full (q:=1151) (rs:=[2, 1, 2, 4, 1, 1, 2]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl127
    (cut_root (prior:=boundsBefore known48891) (before_sound known48891 valid48891) (42528,0,42591,0,8) (by decide +kernel) (by decide +kernel))
def known42623 := extendKnown known43647 9 [(42623,[]),(60285,[129,82,113,48]),(60286,[129,98,82,16,66,49,112])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid42623 : Known false known42623 := extendKnown_ok (m:=42623) valid43647 low42623 (by decide +kernel)
def x191d10 := page #[0x40ff0c3fc53ff18ffc31,0xfd43ff54ffd10ff083fc,0x7a82ec539c87a00ff503,0x282018100801fbb98bdd,0xe0060b0a090807003030,0x3c3844400101e1c1a180,0x8c0b8b0a888028504c48,0x403e3031e1d18e0d8d0c,0xf8e91910020841c00602,0x28270019312920]
def x191l10 : Packing := (10,1,7,0,0,9,0,x191d10)
def x191h10 := page #[0x10000400000000001011,0x20010100011040000000,0x1500010010002007,0x60020020100100240030,0x10000000a00201300900,0x2106107000030130,0x6da15030000002500000,0x3000000046100000,0xd043607013300102070,0x313d41fc131606bb107a,0x75b693b0000000c7511c,0xd671818d8a3e1049165c,0x20000004d29b7e000c0,36980,0x38985d121316f8741ed0,0x1cb4c5e7110001,0xc0011c561f0148000b8c,0x81727cae660c1200068b,0xc8986beae000000185,0x6d0ec800000000072b80,0x5dd992be81c8003761a,0x42ba11a4fe5868276298,0x898f806a2a5df5d43e1d,0x12280375062865214c24,0xc564cb39a6900028ec00,0x79430db52928c52c5193,0x18eef1419c646e0a9a00,0xb5800000010d202243f3,0x11650170cee09f0f01bc,0x7486866b2610135be1dd,0xb354401d8907a8d08616,0x54814054a5d5892c4d40,0xbf948ee3ac9600036e00,0x470c01e16716e074d6b0,0x72b06ecfafc98375010,0xc9a800000031700028c3,0xc665c070000000000b3b,0x3881a8be81b938018248,0x80b152f0f95a89a255e2,0x452c001633e0e551fc,0xcb8000000000204a0000,0x13a78dac3f26c00039c5,0x996000090c91cf0a0000,0x2e10c1e4000235000513,0x49b3289cfee0003c11e6,10]
def x191d9 (j : Nat) : Nat := (if j<103 then (page #[0x5011018c53100310c020,0xbeff7dbdddebf3f54d43,0x192e660bb0ffffdfdfbf,0xb8a1ae462ba9a2e260bb,0x2caa3aaea2ababaae048,0xe26abac2ae4eab822ae4,0x3a612aba32ae6cabb1aa,0x83aaea6ab913a610ab8a,0xab982aea4abb128e1329,0x4aa3932ae0aab8caae2a,0xa40cabb0c282cab91aae,0x83282eab84aae22a393c,0xb8c32846eb1caae10ab8,0xf498bd24014a002ae4ca,0xa474b84d282d4a8bd2c0,0xd0e4d4a0352a434a9152,0x9b52e61498052c054384,0x4ba4d2e8d4aa3528334b,0x2f4b08d2c114a84d2613,0x2407498b522014a8c52e,0x3d2403499352e334b09d,0xb13d0e4f4b01d24134a1,0xf490352c734b1bd2a274,0xa614b0bd2c13498852ea,0xd284d4aa3d26334a0bd2,0x2d242d4b93524094884,0x498352c034b1852c6d49,0x4f4bb3d2e6f4b24d2813,0x240f4b93d2a234983d2a,0x524114a83d264f4b885,0x4c0f9066025c0c403500,0x5076437c19a0bf05442,0x5f42df15609f849e22e1,0x1f88ef472036519c0c60,0x49b64b1247919c87c416,0x52d89660ad254f29413e,0xd0d0066031e1840bdc5d,0x8e3c09da0e727113711a,0x19908c8224009f80f6c7,0x906477a3591928ae4442,0xa72935296e4a92505254,0x4a8d52fa8ed41e9ef4eb,0xcad9566ab10570ab2553,0x8cc2b606af8d78aba05b,0x8533b5996cb263d31998,0xb5ad886b9b591a7ed1d6,0x73db929c58e0c6f43739,0xde64f0b778bb55d82e9e,0xe7fcbfa1f92fab7c5bdd,0x87c010b2846416a08101,0x148944900150b4582b17,0x30838cc0801088b84e07,0x40108fc04381b1a08440,0xc881288b0503b15130a2,0x8c9c0a1707c9404221c0,0x30948a42161f9088a031,0x20c0a8e62006815047c2,0x86b128212494478f1108,0x8e86f1d841349848218d,0x258208d1b924507a3c1d,0xf30e05400fe351d6404a,0x250f9f5818890128f270,0x38798702a5ebf9031120,0xcb8019cf270f30e05479,0x299142fbf18650920df8,0x953e381127d8e0211e7f,0xa7f861011d78f7002c80,0x97c7e2140124af7ee811,0xd4941804bdf236041012,0x652ffe289a4fc122aff8,0x903ffe01040482fca44,0x6bf0781268499f1f0200,0x47d4208fbfe370010109,0x7f807b0a67cf1f4d91f6,0x5f928a32dffc2d0614d2,0x90fdb8d0417f449000ce,0xafe94c94489efffa8300,0x443c9c3c6580589afe03,0x54c1e8977ea4a053be12,0x651f5f0228486f4f0a19,0x704adc7e20451ffc4244,0x799d428024a1e7ce7ac1,0x5f860055bc6ff42c4127,0xa60f4453fb885004944e,0x121c0ac4fc46a1120e04,0xf7c60a504f0c8428b9e9,0x1973f508195bdbb50994,0xc116be4b20866cfc818,0x9993d531d8dc499a05bd,0x91678851c118ebe79ab,0x8c37effc18880013340f,0x641407a231b409789c24,0xd4232d7f49221033d272,0xa0e059e352b5153447cb,0x849566e24b9fb14c8811,0x89036fde2547dcf8012e,0x4e848fbc887bfd7bf914,0xcae8c8db6fde254791fe,0x2553e54c93f89481224c,0x2a9ac91478d191b210c3,0x4c78518d7ffe317a0001,0x33d10c75e8c8b5847871,0x4670b125] j) else (page #[0x663e5120b04991818324,0x7089a62f4408edf4ca44,0x6af3c9e651e04e8247ae,0x2ae0e4e3d3a92ab09fe2,0xa249bf13a091bbf9e4f3,0x6c01485ee44d9b654c87,0xfc6068f40910413efe1f,0x382938e31a32317b310f,0xb1c08e6b231fc5008b7c,0xb13ca8643f53090a16b2,0xbe52268663fe3f325000,0x2a514f996] j))
def x191l9 : Packing := (122,2,7,720906,68,13,1115,x191d9)
def x191h9 (i : Nat) : Nat := (if i<103 then (page #[0x2081091e001882208203,0x88182438100401040,0xc1810804080000440006,0x2800c1808804104021e0,0x820600003002c0042e00,0xd2a44b0600006020a004,0x10080080004291040029,0x60008e000c00e000c787,0x18103000008132040040,0xd0071a10080281008102,0x18f100c0150e04008001,0x865c18400103801404,0x2023011024280ba02540,0x4080045614003044160,0x401a0204c8b1a0000181,0xa8681003000e00140330,0xeaabb506cd2c00000502,0x255e0000d1f600034a,331488,0xa800000012236482a88a,0x34f4b950b30000428604,0x456a0000c079b0200000,0xa491b0a46e5c4126684e,0xa3599f78a280094d6254,0xf06045e8559b8202a28a,0xdd56a4e1cbce14a,0xc12c482812e2f0e3ac00,0x65b6ec4f892fb1b00c5d,0x24ae092a2000251800e3,0x92d9b9923c131846484,0xa091557c001e97ce0ab2,0x9cd5e90d481580b63f30,0x5a2ca9e67f39dc94eff5,0x31636558089d34762836,0x8c1179277c579c8b7675,0x67c961c1421cdc60948,0x12de04508900000b134e,0x50bf517da340801104c,0x23385c8000b199fa7000,0xf08fe41a48e86705255e,0x120d5b0c303bf0199866,0x8a2c6b8000311dd8c356,0xd17805980000000115f9,0x403f0001612c0000000,0x79550001828000,0x52040000000000000000,0xff1596e576499887e93d,0x148179e57ec06e29fd94,0x405720e2070800051e58,0x20e0b2c1c36d592581d,0xb606a4018e2c7c29000,0x1f43ac0db05dc2c38,0x5f95a52ee000384b9909,0x27b440214710bd222cc5,0x259c4890f3613a2,0xda0cb8046d9e082a6aa4,0x570000523a41e200014b,0x96518be8037c8c662106,0x3fab29decc4b4cb3f149,0x41047b1299605400e8ea,0x6afc2d7193f6fb00018,0xb0000a17600000003008,0x90187128de904f03084b,0xa10ac3148761ac934514,0x774286a09c1800006874,0x31ed5c5ec7000063d08b,0x60c0e1904,0xb1876f302c105aa78000,0x3d7d8af0df90eba87909,0x3a02817f18688f76221a,0xe994bc50c000024e8000,0x4907608000e55761ca05,0x70ffe195659f02531b06,0x7013432ca00034b58022,0x209844215f52428c1cc6,0xa20e09dc8435154e1a3a,0xf585868e0660223a8000,0x19a69eb0a0e0430e88,0x40168a70089713c725c0,0x10ac718343a800b5169,0x15c9baeb4c41fa947800,0xa18c000390100014,0x781ec09a000246b324e,0x3fe87f00000001a1b800,0x153c0000000217ef0d08,0x6ec3000060efc281810,0xa8dc8ad2baca48000000,0xf668000000008cd0000c,0x585b4e2b828d9a9b073,0x280500000000000000,0x10e20001c2208b800000,0x6b0f032194d578998000,0x43a17450c9f98641eb8a,0x6de2a4c593260928,0x7f81c0000a2dd89140da,0x2b3da039c601254b5a,0x1258a89ff00992fe0,0x30000000000000002900,0x286640b140,0x4eb400028745174e28a0,0x1bc698a2be56e421c83e,0x42d555274bd2a0000016,0x8d2114ec] i) else (page #[0xa054f61f393ca2d000fd,0x39a26f84e6069a63962c,0x1313029e144400d939d9,0xc5737045411fc4dc83c5,0x27cce6836cb09b02f9c9,0x144eac4c90ba01,0x200d009f000000010a20,0x84291da000,0x32b82150298cb54f6700,0x4985c7752fb3484c946,0xe1639ec13384f0000000,0xa15c1ea832e2,0x40006015000000021b68,0x10bf800016ed000074c,0x4d6a0001094d53200,0x987ce83cb1f000003198,0x42e11bfb571400000a50,0x46b502a1432594f80,0x3c2d6831f0269d1e3b60,0x2532f204a38c452e6452,0x14c125e79dcb032d7fa5,0xa47e4e380c952035c3c9,0xf619f11a0a6c8001a2d,0xd53e0a64b7917a78aa30,0xf843873f929c843749a8,0x2964af86cfc2179248c7,0x6b110702c1017c118ae,0x33b16092dd50a395c365,0x68ec0c87758a5e2ae000,0x87dc8f05b1242c8cbf30,0xc802b87e000000020204,0xdae49dca328dd0000a33,0xc89e400018b2000032,0xc3e4692000000000003,0x23e0d6a8e255930f6000,0x14331d200000002c3090,0x4000005ceede82b68ac1,0xa60000000191fd235ab9,0xec7a54fe07d532f9e,0x718e4000169580000,0x3812ad92800041b8000,0xd1120470000302ea1,0xd09f665ca19400010148,0x500001d9fb975a15d240,1788496] i))
def x191d8 (j : Nat) : Nat := (if j<103 then (page #[0x4c4204c0204802044020,0x5cc2058c2054c2050020,0x58030548305443048030,0x5d4305c8305c43058430,0x5c03158031548315d830,0x480405d8315d4315c831,0x58440580405484054440,0x5d4405cc405c8405c440,0x5c4535c053480535d840,0x5c8635c4635c06348063,0x4c11048510481101c910,0x50510501104c9104c510,0x5c91058d105511050910,0x481401c9405d1105cd10,0x505404c9404c5404c140,0x54940545405414050940,0x58940585405814055140,0x481435d5405c94058d40,0x5c14358143545434c143,0x441531c1535d5435c543,0x501534c5534c15348153,0x5915358d535815350553,0xbbebf9fe3f5c5535c153,0xd9f5fd3f3fcbeffbf6f7,0xedf7fdfb7ddef77dbf6d,0xfbbedfafe7f7fd7f3fbf,0xffbfdff3fbfebf7fdbef,0x240030d389508f98a11c,0x8a40881604796a11e1d4,0x60ca580f9ea89d29522a,0xd4c5c20b88929813e72e,0x600243b121204042a441,0xa904804878452a27c360,0x17418538090ec0854483,0x5822a0b0ef0d5c9db2a1,0xa70a82a41604810c0a00,0x2a471358ebb4a12f5554,0x70e4c268243ad4186388,0x580f20b8830487a68240,0x81cb09e05818c6ae500e,0xc3835954ac52a23c8480,0x805859882c0701606702,0x71307ae429a505c9cb1d,0x82a2d0a480fba985041,0xc6e1654ab34a0ae21514,0x16013bea12935423eea,0x1d91aa11c4d63aaaaa50,0x1aa12005849c130d3812,0xa861429052a538121e8,0x21524042c0801605b20a,0x18a52c27ce548f02c14e,0x8ae6a5b505c02c3ba408,0x741604f9ca89e3d7232,0x858081c985904879e7ac,0x878243b94572707b0a74,0xec01d05823e53047ca54,0xb105802ceaa6e1048119,0x1602c0b0ad8e4c260ac0,0xa4302408585002c2282,0xa4094160a314a94d0587,0x70d50a6b4a0c20581408,0x20e282c14d05836682c2,0x890b09039730a230754e,0xaa380580b20b0ec98212,0x75952a27ac274e480f36,0x821e0b06a0e5cc30243d,0xe090efd5551e8243be05,0xe18161e182c33629523,0xd2614e82c1220487860b,0x2a46c1a98d2034f2615,0x24b0cb19855e92e42dc5,0x88279537092407dc5517,0x4976583306a525c8424b,0x3511102dc6619a3cb1d4,0x110341e4c27a4b035198,0xa52614a24a0598d2071,0x25465bc982c4971871a6,0x63a4b954498244330ce1,0x6900b49406692e4f6220,0xb4198224a2c03125ca7c,0xd845292e6cd248118cc2,0x66330539261d244a8ad8,0x2e8cd25d4224a8b64963,0xe1e4c2a24ba834973029,0x5d820cc2b55d52a91ac2,0x8a4c28e79317092e4292,0xb0d4714236e2a8d86600,0x749204d1ac0e125825c4,0x727c92a44de58dc44409,0x8910f412482ca4b09d49,0x82f524812a4b9398d206,0x1c508d249035714182e2,0x119c4a8b94954511aa4e,0xa4bb2b5160ad12a2b066,0x94249760e92407125d43,0x49204ef2a521754a9a4b,0x64f2c6e9261e3aea93e,0xe285512442340a129793,0x4d525c84a4901d496028,0x2580e3841401982aa92a,0xa546a02949804e92e601,0x4904d89415292e2f4660,0x6525d9a2] j) else (if j<206 then (page #[0x549a44408189516892e2,0x138904081207e3303112,0xc30d49202092c13125d8,0xa89516a92e46521ca324,0x609033012525cd50cc2b,0xe92e4312548a28b09a79,0x5246601946902d49765,0xde4c5d46a8b849709e33,0x59bc9932198074930c4,0x24a9b35d529f12a20e25,0x88b4920b092e22125ca2,0x89515d1a41046608da4b,0x191a4129754a4a4ba82,0xe240edc551ca4bb2e198,0x4dd25d5a0cc2b689525e,0x2204438a0c449529692e,0x50a4b013893154e284c6,0x4b94171423292c074660,0x9f493066baa501e4c24a,0x1418712a2ac6605224b0,0x5a92e22925cd48cc2297,0x30269c549dc4a8d24976,0x84660d9a4b8814983663,0x486324bb038d42531102,0x4440a45161831a413d2,0xc10c492096f241212481,0xc71422ef2415925c8c0c,0x8086910518660670cc32,0x2f26142254578cc33619,0x4963481aa490228d206,0xd2618e38a1188d20aa93,0xc6ba4904c71425e92403,0x24b88549208c92ead525,0x3a1198262a2c111261e8,0x71429292e21a3481924c,0x33031d25c9fc4b0bb,0x79839016c08e03080cc,0x42f81680aa84d424a10b,0x2101079c3a21b20d2063,0xc4e425e12788fc45621,0x1c1830bb05a42bd1508a,0xe507043611a38ce864e3,0x42e2098fe07c43cf1d20,0x92dc94e494242117c87c,0x654229a9450a024ee269,0xc16b8b445922be1574aa,0x94637311981cbe85d42d,0x659ad0d3869033f19acc,0xe8c7383901c34df46db3,0x3ef1f1cf5e79b3bd1d80,0x90cc85341c20910207f4,0xe46a231d1688a744821d,0xb92b894749ea4892068e,0xda4e026c534c98c4bf25,0x98d480a26503a7cd3cc9,0xae456a2af5556a9a53ca,0x2d3566ab28586ac0d5e8,0xebd25e12ec5740b8d5b6,0xf312186cc186052ffd7c,0xa4cb6655b27190ec6c62,0x9a34a1a2cd0a67933999,0xb18d776b5b579aa4d476,0x6f5377dba2dc56dd3689,0x1c8ae39711b855c12df2,0x97513a4dcfce7272f394,0x55e14efc7773b51d8ceb,0x827b83d89e9af367943c,0xf55f8efb77d5be7df2af,0x1d807400dff6fee7f03,0x421e0e506282b410e067,0xb0f486b43261830ae84b,0x2c5b22b514289d448220,0x51e38e3c6ba34518e8c,0x34c97a49923a912c8624,0x5a52c29554a7650f27d9,0x99fccce63b30d97a4b9a,0x27953ac9cace1a6f135a,0xa12503e8013f39f44f6,0xbe94f491a3cd19a88343,0x53a9dd482a0b4eea6552,0x6d2b41595abed5d6adb5,0x62fb0ad80ebe75dbae75,0xda62cff673b2ed93ac89,0x36ecb70db42d836b3b53,0xcddaeebb73eb925c2edf,0xc77d5be45ecaf3178dbb,0x27e10b06d81fc065fdef,0x1898b1c4f625b101868c,0xc9c64b72258fac6fe34f,0x3333987cbc65b32bb94c,0xfd10e8273fb9e3ce566b,0x174f7a6ad2de93b47ba2,0xf6d6ceb0f569a9fd4aea,0xde76c1b4bd966c7761fa,0xbd4ddceeb7743b8ddc2e,0x70a3833c0bdfe6fc77c5,0xfc90e4271bb8b3c3fe18,0xcf4179efcdae64f2cf94,0xbc2deb07517a69d25e8,0x87d000a6000b8000b02b,0x111f8940107c110cc07,0x1002a0fd070f4380c427,0x91681d01] j) else (page #[0xd154a02409604480450c,0x4e071228552789d4186,0x30042241c581bc543084,0x6168d1128a0020412308,0x44b4961d804214084207,0x91013c28058419134148,0x30c6f1a092a21088340e,0xca0824053cbfe7c454be,0x3e22a9c6fd08248df7fc,0xc0c7b59288708829e5ff,0x2f91187e1d0321f01b7e,0x26780b3a1319b810cb09,0x39f5a089b2b221f790c,0xc467c0679c46be80443e,0x3227ca48c8bc4232c24a,0x21127c08449ac21d7292,0x96223e446808af9249f0,0xad5245fd0202367340c,0x434ecc45fb1482819e69,0x8428f448c990e81917c2,0x133ca8100ccbfa040469,0xc85fa44c97c44fb010b8,0x309195f6021f023c8740,0xedf16138047e0370147d,0xa0910023023e03ada98c,0x8508bd0d8b035c91977f,0x9dbe08655bc09b50863c,0x11bc218cc0b78424ecc4,0xfa230fe404c97845b655,0xc402678083e018ee2121,0xc904bfa04046ce68192f,0x93b3263ce48c75e24c72,0xe8190cb090cb0923c101,0x18cbf80639a424ecc590,0xe68191c057109120798c,0xd509453b7c584f35843c,0xe029a42be08e62a86016,0x9f021107021024fc218d,0x4edb498cb6e848c03403,0x2f848796c3d05967c084,0xe219c84766235fd02023,0x312a023810f888f88a78,0xedf1613b79231b00efcc,0x11e6989f6022fe810118,0x40590e2c735843be223b,0x4c495ba625fd08115503,0x8e06e1848ef10a0ee22a,0x6360213a43af36264204,0x26708d80bb262602ef80,0xe18d7c486a05b4150260,0xa43ec0a81521cf6663e2,0x133c492c0a8147286300,0x243d41da143b88a90981,0x8de02581278463a3433d,0x6eb91d21ac8ab222fc89,0x108b61677416403630d8,0x50684604c040147262de,0xb8140400d02388980dc4,0x236020e0c4c7433e221e,0xf232f2863a703ba14336,0x21ec0f3a78064581005a,0x8fe26300e70020d7d792,0x2cf06200c7ca18cf223,0xe000c8bfd44885f4a633,0x78421d6a1d5867f443cf,0xf5886012d7219028958b,0x19e0431942af60636810,0x5730922f2153c2a0cb6,0x2c6073a780648790506c,0xcb036fe60190bc0319c2,0x84f486748b682409780,0xd65625ffab00233cc0d8,0x1f810880159731d7a031,0x7e8220fd0436fdb42265,0x7f00c7de40c60f0020f4,0x127810e9087b43180004,0xc4bc06dec8c6e021b3e9,0xa234057a887dfd531a78,0x3b90a7f0488c046f0415,0x5585808f90aad09a45a8,0x6417d1a0f6f8489bc21,0xd80ad4a19e0559147cba,0x87591588b5e282f71020,0x2dfc0867848d7a886ba8,0x90e3e018ddc2106b4160,0x421c8b2da1d9923005f1,0x4be0640f4a63c9700c86,0x8c84e116c50b5450d014,0xff70992f091d6cc5310,0xa03199093c85065f4063,0xa3435615f2106c359147,0x877788680cc210053a42,0xf2863ef912326700c746,0xe1045fae0190e111e05d,0x814e2218030127c898cd,0x908722a6065d5041b011,0xc88708802c913c053686,0x18d808de0829e121cf18,0x4064dca108c686c049ec,0x8f112816314116c3de5,0x340a25a5322c5] j)))
def x191l8 : Packing := (387,3,7,2359386,103,13,1105,x191d8)
def x191h8 := page #[0x4110500d38b50100a080,0xaa5695d0a75510140010,0x5700a404048b3520eb08,0x7c7cb044000701386651,0xb5a6c4444144b2c2c014,0x24e00c00014dc05d0000,0xf0001b45b17c01611c54,0x11e000081cc00059ff03,0x11600150a80000000000,0x3f51d0003c61000342b2,0xc0000002043000145c20,0x40d0002025706b864214,0x44000041c0000000500a,0x70b948101a6f5f22228,0xf20986a315ec62200000,0x84ec36f1c287a81ef449,0xc1ff08410380004,0xc483404304d4074c3300,0x85800014600000000307,0x5b000286710ca054a1b0,0xce444000812a82800f10,0x1c0444660f4c1561b5c0,0xe0f51a123465808c85a,0xdd01e10ec84011cbc52b,0xf08741ac0000003c0b40,0x85606fc212022422905,0x80d14000061f544fe9a2,0x5318e5361509868521b4,0xe1e603900c583a64be43,0xa68070018000312ec6e,0x8207790bc000d109d3bd,0xdf1a00000003098000c0,0xc76b1d2c3080d1a07c04,0x2161bfc05f1f9c566d19,0xc0002c1800020759179d,0x104ef11dc59702504,0x427c0b6c0ae0f8000,0x4048000b050c190]
def x191d7 (j : Nat) : Nat := (if j<103 then (page #[0x5d8305cd31081714c420,0x1008148040549760c120,0x5096110142580405c551,0x5c440481711018258440,0x101855c4405817110152,0x58572101605c84061971,0x5cc4048173101805c840,0x101605cc405497310151,0x54575101205d44058573,0x5d44058175101525d440,0x101825d4406057510161,0x54576101425d84048176,0x480532052014d525d840,0x14d825c0534817014d87,0x4817018d874806348171,0x1c9106017218d205c463,0x441404811060c7244154,0x5cd20441424811050520,0x505105d9404418448110,0x44087551105494144142,0x60954441815511050954,0x48140549734408758d10,0x501524c1404c53050081,0x58d30501614c14058130,0x4c54054531500874c540,0x50172505404c53250154,0x5c954501525454021d51,0x58d40505625016158140,0x50c81481432057250181,0x5493050d424c14361d20,0x1c1536107054d811c153,0x54d204415321d1054d86,0x21d2054c814815354910,0x4c15361d2054d3048153,0x54c87501535493054c84,0x5014154d545015354940,0x5915321d6454d5458d53,0xbf1fe3ec3f4817154d63,0x97f1be1fbf95f6bdd77a,0xb76e7ecfb9df3ae6fccf,0xef3be6fcbf95f1fdf9be,0x69ecfd8faf75de9fd2f9,0xef9debbcf76eebdb7b5f,0x5f6be97cef8dedbd6f87,0xb3f57e9fd1f9bf2fe4fc,0xd30bd028427fc7f4fe5f,0x96f284470505d9643daa,0x13080921f134a1163483,0xc1261290a952b520b60,0x48192aa11dbd209c0130,0x6489014b952a942c9833,0xaa408942123930b784c2,0x7b154787b0eea2508518,0x876ab2847cf206cc8985,0x6bac251858471e40a230,0x303d9244164a0bfe5206,0x5b508b70984189710e2b,0x44588c91545419519224,0x98a11b7d730faa40d466,0x95c6d422e2b243cf5455,0x19921b12c3136505704c,0x11d324039c545ccc9039,0x7ae22275457b6ba87159,0x475b508dbea114516132,0xf5088c4a0b128878cb28,0xf4e48a38d510312e219,0x4c9533c984a1324d2148,0xdd6d4238c92274264a28,0x99501128433450821443,0x1213235e250829e48a91,0x2a54195806b2b08b8542,0x8dc244b7098566d42305,0x21ec0ccba19d60121131,0x69e40a6d94158510f54e,0xc91ad9417cfa844e2508,0x50991c3ba413cf245206,0x30be52a544f206b8ccc2,0x8790335f508906c899c9,0x30252481b8cc8a511912,0x1b508ce49842a9637a79,0x6420903475203329224,0xea90069c914e9a40da95,0x94785422c1330a026430,0xc541874ac3246645536a,0x1330942649c6ca0b0,0x170268420660940d00f,0xd85309b1242183e8710d,0x8e10b1f43c86f8d71922,0x9772de570aa142268490,0xf38e6fcd91a933863cc3,0x768bd13a0d40a7d4ef1c,0xa293f2744d09812aa464,0x5792e65acb0d5baaf538,0x1b4f684cdd9331961ac0,0xb775ee8dcab8d6f6dadb,0x7f4fc9f53da7a4f1ddfb,0x911e1d42e84d06608c05,0xce52c8d8f91d23645c8a,0x804f49c9362684c39772,0xd39a634a690d19a21422,0x8b015e2b6560ab1536a0,0xf579aec5c2b756a2cd58,0xcf10e13b] j) else (page #[0x4e689ced99f28e46c7d8,0x2905e0ad0002dd73ac7,0x662d4548002c43e0b800,0x4ec020b004a828120fd1,0x4620e00c830008f9012,0x4271200030d019507a00,0x992206610100a2784ed0,0x23244c04c91260748690,0xc0e90804c8402c040160,0x8034c218058442710ce,0xe9093613e2200dd2168d,0x2701004e210003762005,0xf090ee910000548802e0,0x990802c7a4880134853,0xac8501b210020574898,0x108be314a080073625f9,0x909c056432837488c866,0x14d2100078314584812e,0x808000004a0c3020152b,0x82016424080000f88801,0x3e2200701380b504016,0x26c21860c6f603000,0x5023e22502001a08,0x204642000000000001,0x626c097a420000b21321,0x113c18a9815e610c03b2,0xc040101078c50c0aaf41,0x3e6105ac2095c0d7b8c6,10868] j))
def x191l7 : Packing := (137,4,7,3801188,103,11,1064,x191d7)
def x191h7 := page #[0x80000000000042841210,0x8b44d01001a1400000c0,0xc1b90725c1d40191e050,0x10c00000272000f1bc2e,0xa1c00085000a0de22d6,149376]
def x191d6 := page #[0x6354e07ca9549861c153,0x81525cd10b0729d64551,0x25092058173103d61514,0x1039d1302048748153f6,0x205c440f295089148176,0x9302052050f9a542261,0x3d8542245205cc40fe05,0x5d4409dc694985052044,0x4258175103d254224520,0xa92021d4255110f4a481,0x153f6848171509601039,0x50520443f40a1481524c,0x636408759153de850898,0x38fc2a520605544430dd,0xe84403d49524c0874815,0x722e19d5c1ad9985712c,0x181687ab67230efab6,0x3504205c102f02d8,0xe410815871042002c080,0x2c08168400]
def x191l6 : Packing := (19,5,7,0,0,8,0,x191d6)
def x191h6 (i : Nat) : Nat := (if i%103=0 then 530688 else 0)
def x191d5 := page #[0x21e50549302048748153,0xa3390a134a4c282902]
def x191l5 : Packing := (2,6,7,0,0,3,0,x191d5)
def x191samples : Array (Bits × Bits) := #[(0x9017721c30,0x14b5bd0008),(0x500e080936,0x634240ff36),((word [mask72,0xffffffffff4ca8886101]),(word [mask72,0xffffffffff8c0d9a00c9])),(0xdc001a04a,0x12b065ab12),((word [mask72,0xffffffffff815101844f]),(word [mask72,0xffffffffffe94a0254e5])),(0x2200761284,0xca4842b0f4),(0x0,0x0),((word [mask72,0xffffffffff2220844287]),0x31b2254f02),(0x0,0x0)]
def x191columns : List ColumnInfo := [(24,0,167,0,7),(2,0,189,0,8),(6816,0,6687,0,7),(1538,0,1725,0,8),(43010,0,43197,0,8),(44546,0,44733,0,8),(54786,0,54973,0,8),(160,0,31,0,7),(17922,0,18109,0,8),(1664,0,1599,0,8),(42624,0,42559,0,8),(47744,0,47679,0,8),(16898,0,17085,0,8),(1544,0,1719,0,8),(42504,0,42679,0,8),(47624,0,47799,0,8),(2208,0,2079,0,7),(1,0,190,0,7),(2050,0,2237,0,8),(44552,0,44727,0,8),(54792,0,54967,0,8),(2688,0,2623,0,8),(2562,0,2749,0,8),(12304,0,12463,0,8),(42512,0,42671,0,8),(44560,0,44719,0,8),(47632,0,47791,0,8),(54800,0,54959,0,8),(68624,0,68783,0,8),(1560,0,1703,0,7),(1696,0,1567,0,7),(42520,0,42663,0,7),(42656,0,42527,0,7),(58370,0,58557,0,8),(58016,0,57887,0,7),(57858,0,58045,0,8),(44568,0,44711,0,7),(47640,0,47783,0,7),(54808,0,54951,0,7),(44192,0,44063,0,7),(44034,0,44221,0,8),(35,0,156,0,4),(4,0,187,0,7),(9,16,166,0,4),(19,0,172,0,4),(129,32,30,0,4),(36,128,27,0,4),(20,8,163,0,4),(42500,0,42683,0,7),(47617,0,47806,0,7),(25,0,166,0,4),(14,0,177,0,4),(44036,0,44219,0,7),(13320,0,13495,0,8),(68616,0,68791,0,8),(64002,0,64189,0,8),(56,0,135,0,4),(7704,0,7847,0,7),(12312,0,12455,0,7),(68632,0,68775,0,7),(11296,0,11423,0,8),(26,0,165,0,4),(52738,0,52925,0,8),(54785,0,54974,0,7),(134,0,57,0,4),(2592,0,2719,0,8),(52896,0,52767,0,7),(13328,0,13487,0,8),(3080,0,3255,0,8),(168,0,23,0,4),(4120,0,4263,0,7),(1152,0,1087,0,8),(6160,0,6319,0,8),(47776,0,47647,0,7),(44548,0,44731,0,7),(152,0,39,0,4),(1032,0,1207,0,8),(6176,0,6303,0,8),(162,0,29,0,4),(164,0,27,0,4)]
def x191autos : List (List Nat) := [[],[115,84],[32,67,117],[32,83,116]]
def x191levels : Nat → Packing
  | 10 => x191l10
  | 9 => x191l9
  | 8 => x191l8
  | 7 => x191l7
  | 6 => x191l6
  | 5 => x191l5
  | _ => emptyPacking
def x191index : Nat → Nat → Option (Nat × Nat)
  | 10 => lookupWord 177 223 4 13 7 2 x191h10
  | 9 => lookupWord 185 697 7 15 9 2 x191h9
  | 8 => lookupWord 39 199 6 14 8 2 x191h8
  | 7 => lookupWord 11 35 3 11 5 2 x191h7
  | 6 => lookupWord 1 3 1 7 1 2 x191h6
  | _ => fun _ => none
def x191 : Forest := ⟨1215,10,fun j => x191samples[j]?.getD (0,0),x191columns,x191autos,x191levels,x191index⟩
set_option maxHeartbeats 0 in
theorem geomx191 : graphValid x191 (boundsBefore known42623) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=4) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem x191Chunk7_0 : block x191 7 0 68 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem x191Chunk7_1 : block x191 7 68 69 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem x191Chunk8_0 : block x191 8 0 129 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem x191Chunk8_1 : block x191 8 129 129 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem x191Chunk8_2 : block x191 8 258 129 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem tablesx191 : checkedTables x191 10 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · decide +kernel
  · decide +kernel
  · exact (@block_merge x191 7 0 68 69 x191Chunk7_0 x191Chunk7_1)
  · exact (@block_merge x191 8 0 258 129 (@block_merge x191 8 0 129 129 x191Chunk8_0 x191Chunk8_1) x191Chunk8_2)
  · decide +kernel
  · decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem pl191 : Impossible false (graphGoal 1215) 10 (vars 1215).toFinset := plainA (q:=191) (prior:=boundsBefore known42623) (before_sound known42623 valid42623) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low6847 : Lower false (varsX 6847) (graphGoal 6847) 11 :=
  strong_full (q:=1215) (rs:=[2, 1, 2, 4, 1, 1, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl191
    (index_root (g:=x191) (i:=0) rfl rfl (before_sound known42623 valid42623) geomx191 tablesx191 (by decide +kernel))
def known6847 := extendKnown known42623 11 [(6847,[]),(1887,[133,117,101,33,48]),(14175,[131,67,99,116,50,33,16,80]),(8059,[128,64,116,81,96,49,32]),(17275,[130,114,98,81]),(17390,[66,114,132,49,32,81,96])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid6847 : Known false known6847 := extendKnown_ok (m:=6847) valid42623 low6847 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low18111 : Lower false (varsX 18111) (graphGoal 18111) 11 :=
  strong_full (q:=1215) (rs:=[2, 1, 2, 4, 1, 1, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl191
    (index_root (g:=x191) (i:=1) rfl rfl (before_sound known42623 valid42623) geomx191 tablesx191 (by decide +kernel))
def known18111 := extendKnown known6847 11 [(14143,[135,50,65])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid18111 : Known false known18111 := extendKnown_ok (m:=18111) valid6847 low18111 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low17087 : Lower false (varsX 17087) (graphGoal 17087) 11 :=
  strong_full (q:=1215) (rs:=[2, 1, 2, 4, 1, 1, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl191
    (index_root (g:=x191) (i:=2) rfl rfl (before_sound known42623 valid42623) geomx191 tablesx191 (by decide +kernel))
def known17087 := extendKnown known18111 11 [(17087,[]),(9535,[133,117,16,64,49,32]),(4959,[133,117,101,33,48]),(2415,[128,16,64,100,80,113,33,48])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid17087 : Known false known17087 := extendKnown_ok (m:=17087) valid18111 low17087 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low2239 : Lower false (varsX 2239) (graphGoal 2239) 11 :=
  strong_full (q:=1215) (rs:=[2, 1, 2, 4, 1, 1, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl191
    (index_root (g:=x191) (i:=3) rfl rfl (before_sound known42623 valid42623) geomx191 tablesx191 (by decide +kernel))
def known2239 := extendKnown known17087 11 [(2239,[]),(4927,[131,65,50,114,81]),(6975,[133,117,16,64,49,32]),(2399,[133,117,101,33,48]),(9567,[131,67,99,116,50,33,16,80]),(4975,[128,16,64,100,80,113,33,48]),(7023,[130,33,113,98,66,16,80]),(2427,[130,114,98,81]),(9595,[128,64,116,81,96,49,32]),(9703,[67,132,99,82,16]),(12782,[66,114,132,49,32,81,96])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid2239 : Known false known2239 := extendKnown_ok (m:=2239) valid17087 low2239 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low2751 : Lower false (varsX 2751) (graphGoal 2751) 11 :=
  strong_full (q:=1215) (rs:=[2, 1, 2, 4, 8, 1, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl191
    (index_root (g:=x191) (i:=4) rfl rfl (before_sound known42623 valid42623) geomx191 tablesx191 (by decide +kernel))
def known2751 := extendKnown known2239 11 [(2751,[]),(1343,[135,50,65]),(18751,[132,65,48,80,113,32]),(1375,[135,101,50,33,16,64]),(18783,[132,67,100,84,48,33,112]),(1391,[130,50,97,115,82,16,64]),(18799,[128,97,65,49,33,112]),(1403,[130,50,81,115,98,65]),(18811,[128,80,81,67,96,113,32]),(28135,[80,132,99,112,32,16]),(6638,[50,117,131,49,32,65,96]),(28142,[80,84,132,49,113,96])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid2751 : Known false known2751 := extendKnown_ok (m:=2751) valid2239 low2751 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low1727 : Lower false (varsX 1727) (graphGoal 1727) 11 :=
  strong_full (q:=1215) (rs:=[2, 1, 2, 4, 1, 1, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl191
    (index_root (g:=x191) (i:=5) rfl rfl (before_sound known42623 valid42623) geomx191 tablesx191 (by decide +kernel))
def known1727 := extendKnown known2751 11 [(1727,[]),(2367,[135,50,65]),(7007,[135,101,50,33,16,64]),(9583,[130,50,97,115,82,16,64]),(4987,[130,50,81,115,98,65]),(17341,[129,82,97,48]),(14318,[50,117,131,49,32,65,96])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid1727 : Known false known1727 := extendKnown_ok (m:=1727) valid2751 low1727 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low42687 : Lower false (varsX 42687) (graphGoal 42687) 11 :=
  strong_full (q:=1215) (rs:=[2, 1, 2, 4, 1, 1, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl191
    (index_root (g:=x191) (i:=6) rfl rfl (before_sound known42623 valid42623) geomx191 tablesx191 (by decide +kernel))
def known42687 := extendKnown known1727 11 [(42687,[]),(44351,[135,50,65]),(47967,[135,101,50,33,16,64]),(53087,[133,117,101,33,48]),(44923,[130,50,81,115,98,65]),(69499,[128,64,116,81,96,49,32]),(60349,[129,82,97,48]),(69565,[129,80,48,50,114,97,64]),(42983,[115,83,82,130,99,66,16]),(45031,[84,117,80,132,96,48,32,16]),(53230,[50,117,131,49,32,65,96]),(60398,[64,132,49,96])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid42687 : Known false known42687 := extendKnown_ok (m:=42687) valid1727 low42687 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low58559 : Lower false (varsX 58559) (graphGoal 58559) 11 :=
  strong_full (q:=1215) (rs:=[2, 1, 2, 36, 1, 9, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl191
    (index_root (g:=x191) (i:=7) rfl rfl (before_sound known42623 valid42623) geomx191 tablesx191 (by decide +kernel))
def known58559 := extendKnown known42687 11 [(58559,[]),(64191,[117,67,32]),(51007,[133,117,16,64,49,32]),(54079,[135,50,65]),(46431,[133,117,101,33,48]),(43887,[128,16,64,100,80,113,33,48]),(54127,[128,97,65,49,33,112]),(48507,[128,64,116,81,96,49,32]),(43951,[113,129,97,82,32,65,48]),(43453,[129,82,97,48]),(64445,[129,80,48,50,114,97,64]),(49646,[64,132,49,96])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid58559 : Known false known58559 := extendKnown_ok (m:=58559) valid42687 low58559 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low58047 : Lower false (varsX 58047) (graphGoal 58047) 11 :=
  strong_full (q:=1215) (rs:=[2, 1, 2, 16, 8, 1, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl191
    (index_root (g:=x191) (i:=8) rfl rfl (before_sound known42623 valid42623) geomx191 tablesx191 (by decide +kernel))
def known58047 := extendKnown known58559 11 [(58047,[]),(47935,[133,117,16,64,49,32]),(69439,[132,65,48,80,113,32]),(44383,[133,117,101,33,48]),(74079,[132,67,100,84,48,33,112]),(50043,[128,64,116,81,96,49,32]),(58235,[130,114,98,81]),(69102,[66,114,132,49,32,81,96])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid58047 : Known false known58047 := extendKnown_ok (m:=58047) valid58559 low58047 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low44223 : Lower false (varsX 44223) (graphGoal 44223) 11 :=
  strong_full (q:=1215) (rs:=[16, 1, 2, 4, 1, 1, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl191
    (index_root (g:=x191) (i:=9) rfl rfl (before_sound known42623 valid42623) geomx191 tablesx191 (by decide +kernel))
def known44223 := extendKnown known58047 11 [(44223,[]),(44735,[84,115]),(52927,[117,67,32]),(54975,[116,83,32]),(42815,[135,50,65]),(44863,[131,65,50,114,81]),(53055,[133,117,16,64,49,32]),(60223,[132,65,48,80,113,32]),(42847,[135,101,50,33,16,64]),(50015,[131,67,99,116,50,33,16,80]),(58207,[133,117,101,33,48]),(60255,[132,67,100,84,48,33,112]),(42863,[130,50,97,115,82,16,64]),(47983,[130,33,113,98,66,16,80]),(60271,[128,97,65,49,33,112]),(69487,[128,16,64,100,80,113,33,48]),(42875,[130,50,81,115,98,65]),(44411,[130,114,98,81]),(60283,[128,80,81,67,96,113,32]),(74107,[128,64,116,81,96,49,32]),(44989,[129,80,48,50,114,97,64]),(69095,[84,117,80,132,96,48,32,16]),(69607,[80,132,99,112,32,16]),(48110,[50,117,131,49,32,65,96]),(55278,[66,114,132,49,32,81,96]),(69614,[80,84,132,49,113,96])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid44223 : Known false known44223 := extendKnown_ok (m:=44223) valid58047 low44223 (by decide +kernel)
def x255d11 := page #[0x8f1a284060808057fc10,1224]
def x255l11 : Packing := (1,1,6,0,0,0,0,x255d11)
def x255h11 := page #[0x170108490827828b80af,0xc8280a80000001288072,0x3800e3000c4814a28004,8]
def x255d10 := page #[0x60810bbd84042f760c10,0x42ff61010afd86042fb,0xffd42042ff60810bfd83,0x5cc10ffd30043ff55010,0x7f9a15910f2e85d003ff,0xd06080200bbeabda425b,0x10040161a18161413918,0x80283c30342c27180a0c,0x50c640685848241c100,0x7480d0b4609048382010,0x504d78c021e1c040008,0x2c260c58342c0854480,0x40685c1c10c04820d808,0x22e20502128000111036,0x6a241064060040e1d000,0x45e30d8a0c81814020]
def x255l10 : Packing := (11,2,6,0,0,10,0,x255d10)
def x255h10 := page #[0x40004082000000144000,0x200108200000514a0433,0x57834001c1c40e912986,0xc00110950282796c1628,0x1704d44505c06907602,0x10000003d1e537c6746e,0x7140c721300030500034,0x2c8c93c003182c4b15,0x1c3285b90ec41920000,0x3c8700800082947f1180,0x1800297152608243b40,0x380606397c47943e489,538968064]
def x255d9 := page #[0x608105cc10550104c010,0xffcff618106101060c10,0xca3ffdbff7def7ddfafe,0xa146a956aa58aa46985a,0xc95a9836b9d0c958b9c8,0xb846cad4986aa134b9e6,0xa15aaa38cbc0cbc4a168,0xcad8a94ab9b89846b856,0xc11eb80cca3ca134aa60,0xc92cc12c983ca94cb84c,0x487719c4f0f42b054002,0x4d414ad153dcdf324ab2,0x19f3761bf6b59860d6e5,0x8e8a9f66f9864f8f6258,0x70642100bd2d8b0ab2a,0x14020482f090886c0001,0x3e0241874390b4107834,0x8116988c51b8c1680a00,0xd4057d0116e807bd8120,0x8879e449669080ff091,0xc0916e8073ee9209c7a8,0xba01ef5025bee9209cfe,0x492f60487f42099e4055,0x31fd4095e405a6492532,0x243f74904e6f88cfe841,0xb08ac2279015e40503fc,0x80d3485b10aff144a303,0x5e531855aca28df]
def x255l9 : Packing := (36,3,6,524295,51,10,1055,x255d9)
def x255h9 := page #[0x50390014553e041769a0,0x42001180600]
def x255d8 := page #[0x73610108f72a54260c10,0xcfb649825cc10aef689,0x13060810eee5c1306101,0x10ebe5c13061810efa5c,0x897361810afb6a573608,0x9b9673502d1e1900abf6,0x6401038600041800202,0x190040e18320081c3]
def x255l8 : Packing := (8,4,6,0,0,8,0,x255d8)
def x255samples : Array (Bits × Bits) := #[((word [mask72,0xffffffffffffa8c12191]),0x7c002100),(0x100d1cae,0x38d1cac),((word [mask72,0xffffffffffffc4146207]),(word [mask72,0xffffffffffffec000203])),(0x5308cf8,0x139088f0),((word [mask72,0xffffffffffffa160574f]),(word [mask72,0xffffffffffff806f560f])),(0xa82987e,0x390807e),(0x1008e070,0x7c72e050),(0x4202ff80,0x106f7d80),(0x0,0x0)]
def x255columns : List ColumnInfo := [(2,64,189,0,8),(33,0,222,0,7),(1048,0,1255,0,8),(1184,0,1119,0,8),(17,0,238,0,7),(52800,0,52927,0,11),(54848,0,54975,0,11),(58432,0,58559,0,11),(64064,0,64191,0,11),(43010,64,43197,0,8),(11266,64,11453,0,8),(52738,64,52925,0,8),(57858,64,58045,0,8),(58370,64,58557,0,8),(145,32,78,0,4),(64002,64,64189,0,8),(73,16,166,0,4),(162,64,29,0,4),(41,16,198,0,4),(1096,0,1207,0,8),(148,8,99,0,4),(160,0,95,0,8),(12,0,243,0,7),(177,0,78,0,4),(54786,64,54973,0,8),(59393,0,59646,0,8),(52801,0,52926,0,7),(78,0,177,0,4),(193,32,30,0,4),(90,0,165,0,4),(84,8,163,0,4),(54849,0,54974,0,7),(0,128,91,36,7)]
def x255autos : List (List Nat) := [[],[115,84],[32,67,117],[32,83,116]]
def x255levels : Nat → Packing
  | 11 => x255l11
  | 10 => x255l10
  | 9 => x255l9
  | 8 => x255l8
  | _ => emptyPacking
def x255index : Nat → Nat → Option (Nat × Nat)
  | 11 => lookupWord 5 23 3 10 4 2 x255h11
  | 10 => lookupWord 27 69 6 12 6 2 x255h10
  | 9 => lookupWord 2 13 4 9 3 2 x255h9
  | _ => fun _ => none
def x255 : Forest := ⟨1279,11,fun j => x255samples[j]?.getD (0,0),x255columns,x255autos,x255levels,x255index⟩
set_option maxHeartbeats 0 in
theorem geomx255 : graphValid x255 (boundsBefore known44223) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=3) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem tablesx255 : checkedTables x255 11 := by
  intro k hk
  interval_cases k <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem pl255 : Impossible false (graphGoal 1279) 11 (vars 1279).toFinset := plainA (q:=255) (prior:=boundsBefore known44223) (before_sound known44223 valid44223) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low2303 : Lower false (varsX 2303) (graphGoal 2303) 12 :=
  strong_full (q:=1279) (rs:=[2, 1, 2, 4, 1, 1, 2, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl255
    (cut_root (prior:=boundsBefore known44223) (before_sound known44223 valid44223) (2112,0,2239,0,11) (by decide +kernel) (by decide +kernel))
def known2303 := extendKnown known44223 12 [(27127,[67,80,100,131,112,32,16])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid2303 : Known false known2303 := extendKnown_ok (m:=2303) valid44223 low2303 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low17151 : Lower false (varsX 17151) (graphGoal 17151) 12 :=
  strong_full (q:=1279) (rs:=[2, 1, 2, 4, 1, 1, 2, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl255
    (cut_root (prior:=boundsBefore known44223) (before_sound known44223 valid44223) (16960,0,17087,0,11) (by decide +kernel) (by decide +kernel))
def known17151 := extendKnown known2303 12 [(17151,[])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid17151 : Known false known17151 := extendKnown_ok (m:=17151) valid2303 low17151 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low2815 : Lower false (varsX 2815) (graphGoal 2815) 12 :=
  strong_full (q:=1279) (rs:=[2, 1, 2, 4, 8, 1, 2, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl255
    (cut_root (prior:=boundsBefore known44223) (before_sound known44223 valid44223) (2624,0,2751,0,11) (by decide +kernel) (by decide +kernel))
def known2815 := extendKnown known17151 12 [(18911,[99,132,84,48,33,112]),(28151,[67,80,100,131,112,32,16])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid2815 : Known false known2815 := extendKnown_ok (m:=2815) valid17151 low2815 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low6911 : Lower false (varsX 6911) (graphGoal 6911) 12 :=
  strong_full (q:=1279) (rs:=[2, 1, 2, 4, 1, 1, 2, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl255
    (cut_root (prior:=boundsBefore known44223) (before_sound known44223 valid44223) (6720,0,6847,0,11) (by decide +kernel) (by decide +kernel))
def known6911 := extendKnown known2815 12 [(17403,[118,130,81])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid6911 : Known false known6911 := extendKnown_ok (m:=6911) valid2815 low6911 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low1791 : Lower false (varsX 1791) (graphGoal 1791) 12 :=
  strong_full (q:=1279) (rs:=[2, 1, 2, 4, 1, 1, 2, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl255
    (cut_root (prior:=boundsBefore known44223) (before_sound known44223 valid44223) (1600,0,1727,0,11) (by decide +kernel) (by decide +kernel))
def known1791 := extendKnown known6911 12 [(17405,[82,129,48])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid1791 : Known false known1791 := extendKnown_ok (m:=1791) valid6911 low1791 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low1279 : Lower false (varsX 1279) (graphGoal 1279) 12 :=
  strong_full (q:=1279) (rs:=[16, 4, 2, 4, 1, 1, 2, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl255
    (index_root (g:=x255) (i:=0) rfl rfl (before_sound known44223 valid44223) geomx255 tablesx255 (by decide +kernel))
def known1279 := extendKnown known1791 12 [(3579,[99,81,115,130,65]),(18941,[82,129,48]),(11774,[117,99,49,32,65,128]),(18942,[100,49,128])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid1279 : Known false known1279 := extendKnown_ok (m:=1279) valid1791 low1279 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low58623 : Lower false (varsX 58623) (graphGoal 58623) 12 :=
  strong_full (q:=1279) (rs:=[2, 1, 2, 36, 1, 9, 2, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl255
    (cut_root (prior:=boundsBefore known44223) (before_sound known44223 valid44223) (58432,0,58559,0,11) (by decide +kernel) (by decide +kernel))
def known58623 := extendKnown known1279 12 [(58623,[]),(46559,[118,133,33,48]),(43517,[82,129,48])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid58623 : Known false known58623 := extendKnown_ok (m:=58623) valid1279 low58623 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low58111 : Lower false (varsX 58111) (graphGoal 58111) 12 :=
  strong_full (q:=1279) (rs:=[2, 1, 2, 16, 8, 1, 2, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl255
    (cut_root (prior:=boundsBefore known44223) (before_sound known44223 valid44223) (57920,0,58047,0,11) (by decide +kernel) (by decide +kernel))
def known58111 := extendKnown known58623 12 [(68863,[116,83,32])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid58111 : Known false known58111 := extendKnown_ok (m:=58111) valid58623 low58111 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low44287 : Lower false (varsX 44287) (graphGoal 44287) 12 :=
  strong_full (q:=1279) (rs:=[16, 1, 2, 4, 1, 1, 2, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl255
    (cut_root (prior:=boundsBefore known44223) (before_sound known44223 valid44223) (44096,0,44223,0,11) (by decide +kernel) (by decide +kernel))
def known44287 := extendKnown known58111 12 [(44799,[84,115]),(42975,[118,101,133,50,33,16,64]),(58335,[118,133,33,48]),(60383,[99,132,84,48,33,112]),(48119,[115,82,98,131,66,16]),(69623,[67,80,100,131,112,32,16]),(45053,[80,48,50,114,129,64]),(58365,[82,129,48])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid44287 : Known false known44287 := extendKnown_ok (m:=44287) valid58111 low44287 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low42751 : Lower false (varsX 42751) (graphGoal 42751) 12 :=
  strong_full (q:=1279) (rs:=[2, 1, 2, 4, 1, 1, 2, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl255
    (cut_root (prior:=boundsBefore known44223) (before_sound known44223 valid44223) (42560,0,42687,0,11) (by decide +kernel) (by decide +kernel))
def known42751 := extendKnown known44287 12 [(42751,[]),(47871,[117,67,32]),(42999,[115,82,98,131,66,16]),(60413,[82,129,48]),(69629,[80,48,50,114,129,64])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid42751 : Known false known42751 := extendKnown_ok (m:=42751) valid44287 low42751 (by decide +kernel)
def x383d12 := page #[0xffa81ff54bfe087fc30,0xf1294761d803fe887fd3,0x63014080301004006f6,0xc1c0d065c160a048200e,0x5402080a04c24110803,0xf074381b0d06430170b,0x2251208c44210334401f,0x3c484150a450271300c1,0x5a2c1286c92b884]
def x383l12 : Packing := (6,1,8,0,0,9,0,x383d12)
def x383h12 := page #[0xc35410032cc082000283,0x71001400820430050b11,0x3e89f81470c204504134,0x2ddb960a713a47c0008c,0x4c0000001045e02d0750,0xb445d640f035b100019,0xf12fa0743b0039c1d,0x712145fe1b30b939f002,0x356660ac43d82820ca83,0x3b15a259e00915b38a81,0xcdc24b299c6cd4889ec3,0x92e08c0009128422147c,0x32807502389b83e000b,0x20b2031241808c49c,0x1c40021b720000000000,0xb90b0000000c28928113,0x7aed45560ed2,0xdc14911063a64efd100,0x83709a00000028a80019,0x68bfa4c0000000000,0x504c00050a76d4868c10,0x9b14e320002839810909,0xf6183e06000a8c0b07e4,0xbaed31538440c1ffdeb0,0x146100000004]
def x383d11 := page #[0xbdebf549404c1100c010,0xffffefeff7fbfbfbfefb,0xc107482830c498202c18,0x62641a8481c2e0d5418e,0xc8126c3c36199b02518,0xa40d98306c1a32059b06,0x89cb06a48172c0994c04,0x59605cae2647132a8b95,0x2c189609ca6325703298,0x60729829619cae324835,0x6253032c3c90c14ae125,0x4ae2e57352b8391cd48e,0xc0c60720490230009041,0x2151e51b618713f11d0d,0x563403132e32b02a526c,0x44aa44941c3e83ca39b3,0x6616155e458355352550,0xe378274c7106d06b169b,0x58e38c58a386e83a81a7,0x348900001c0697a94f91,0x100d43b0f8371270f0b8,0x4a88a210da2550438caf,0xa0bd2b11e2c86d20440,0x24cd324c51488e03812,0x18260882e2d96540436,0x3d4084844d304b51c082,0xb1303c1762a1695855d,0x12872188442d0320f834,0x6289d565552c42c24876,0x6490464743a41c6518c,0x170520e0086017c5e16e,0x2809c090941f0c00486a,0x511404f1394b0a82900c,0x3981c641855454d52428,0x184211b10d424450f4fc,0x148820c8404551112469,0x6819c66172268a04d84e,0x85538033003cfc0464a8,0x138ffe14e3f504e40cc1,0x4cbbc09000001f000000,0x40ec8c00004fe7ff6178,0xff5f0360058d98227afe,0xfea8819f3f0e0085a338,0x24a93c6a8dbca09400df,0x4c004ff0178007139c92,0xf404a0073c6fbb087000,0x378275f91338fb400f3,0xcaef024afe86504434,0xd63033dff85f00ccb9c8,0x22685f554114bff14,0xaf597d0ca8a688f6fe3,0xfe7f00184005c1562000,0x3ff3fc7f8990414d7,0xa85702d1ae1e9c840000,0x2aaffec8001025157a,0x5ffd7000400fcfea2,0xa20000dc5fff81aae067,0xa5ec0085e09fb70ef058,0xec7062909778125ffe0c,0x82f1cf1be89c1b0004,0xf703c5804a327e1f3e4c,0x17139c88000001547eb,0x9fff785350254fffe02f,0xff0144081a63d8b81940,0x32d22ffc68564541281b,0xe40a032481e0294604de,0x4b7f64e130f024d2bfaf,0xff64904012a7fcc02022,1791]
def x383l11 : Packing := (48,2,8,655366,67,12,1166,x383d11)
def x383h11 (i : Nat) : Nat := (if i<103 then (page #[0x10000c0000000000,0x1c00000000030410,0x4000200000,17302016,0x60000002000800,0x8400000000000000,0x1002000000003140,0x800000040020071,0x304000000000000100,0x100000c002000008080,0x10000cd0000000000,0xa08000000000008000,0xc00800000000030800c0,0x20000050400c00030000,0x10000000d14000000100,0xd000007001084,0x100000000000000b0,0x490c900000004000004,0x440000802800000c1001,0x2040c10010800800,0xc000108300404200018,0x20001c0003000080002,0x440520401810000000,0x2800800c700068100,0x7000001000000240000,0xc10000000000000c03,0x40001200000,0x21c0080200000281004,0xe1800000060060820015,0x4000008000000b00130,0x1c0140005000000000,0xc33002800420000000,0xc0130001800000c400,0xc20c000a01b000,0x4021000008902a0400,0x886d2d792212a9b0415c,0x692e0b6f05aa0c0c8b1c,0xf0c4589e9,0x60cf0000206e0,0x83208d10700000f6960,0xf0bd9618b04e5021b,0x2c00000000000000000,0x68a30000001d00006,0x830486896dbb05500000,0x27e09a204ba836c0589,0x5de0b00000e0120849a,0xac5064d065c528fe25c2,0x2f80d040aaca6c00bae,0x8b3e03a70307609e226a,0xd00b08f9222642768622,0xed2d02356216076e0042,0xc0eb026303500e92005b,0xa030dbe866b816ec277,0xe0d87c282e5658a038d,0x85a000020abc8c670505,0x84180000dec500003,0x8bec065d016e013104a0,0x14ca280300008079a,0x31020000b03e0,0x410b8d8006240fab0ac0,0x15302d30201025d010f,0x361a000048375,0xf071e0570,0x47000000000000904d0,0x884f07a0000a0890000e,0x825a090d0e8da83f0699,0xc790c3606a22c5a2e2d,0xbf207fa08b00007072c,0xc8609500a9701428e87,0x22500437409000090bed,0x98e03754c58ced60681,0x67fa66306cc042f0f26,0x756088e429327e20294,0xd4d0ef8e90501120aec,0xec6220b200110e47053b,0x6d3084b0a4205624eb3,0xc223a4bc702a3026cd5d,0x242041520ed982788a5f,0xeac65e48cd88655081d,0xb0000000000003018c,0x2a02cd80f500009039d,0xb8b0b9e0e320cb00d9e,0x7882b700cd901988f07,0x89a508ad0a1146feefc0,0x9000000d5000008cb7,0x87ea25b007a092e05b2,0xe720fca88a06d5d26d8,0x28302eb0e1687968e54,0x3bd8fe000072fc2033a,0xd60b0000b0321898c,0x4190000208e000062400,0xe000020f098d178281,0xbcc2981008505200007,0xfe0000e07300005,0x421a0f450b5000000000,0x81340b4e400a0ec00008,0xa0101c8f8501720d37,0x8a4109c785902e500e5a,50668,0x1f00000000000000000,0x54c6c4bb48ca6097d,0xe6207b000048f900000,0x46d2ef6d] i) else (page #[0x848000020b7f0a810031,0x760e70d15,0xb3b045205120da80640,0xe885e046285120c28,0x1c203600000000a8f70,528100,0x8f49006b8920000b8580,0x7e21dacd0000e,0xb1c077f8d5000000000,0x78330000000020442,0x1b808c30ad00a2841e0,0x8038290000d0b2cc837,0x876442c203c60662086b,0x40682ca869c0af64205,0xebd82140f7f682e06b1,0x86fd08508d65094d8c1e,0xa64061e09d0000600c8,0xafc08f12b00e0ddb0c14,0x54b09314e2c0a3f0e24,0x8faa0f9d0ff0059fae56,0x10240000e0f1e,0x894a897407c9c2168da2,0x287b84b2860626600001,0xeeb80c5dcf8c05c40dc1,0xfd0000804c229b70cab,0x6f00000000000000008,0x5e50d24290903474052,0xf3540190cc407e5048b,0x502da98a6da24e7f8b4a,0x96d0fb70f644fc28531,0xfe252de2c9049a8316,0xd7e041f8f3383da2101,0x820a90e890040b84d76,0x1ef05ffe6fe490bc928,0x422e0630cd022391e9be,0x60c6f87031929ca074f,0xe09e2091c2acc,0x82df0f80000000000000,0x6e70a21b0c9e03d820c8,0xa5a60fc01a40df507d2,0xc6c489f80bb08350000f,0x875220e5622802ba8a0e,0x29400000000d47a00008,0xa764c760c6304f0000c,0x2992cda18eb909bb49b0,0x3811109f8,0x809908f2000000000,0x21022603fd43900000,0x4eec100e44c70cef0de2,0xd000010d80000a0d68,0xc2d40000e85f9] i))
def x383d10 (j : Nat) : Nat := (if j<103 then (page #[0x60c10608104c0101cc10,0x5c0304c030204301c430,0x411061830604305c430,0x4c11020d101cd100c110,0x481302053060d105cd10,0x5c130589305813054530,0x6193060930605305c530,0x5c5405c140505404c540,0x6fc7f4c1524815261d40,0xdf7bdf77edfcff9f73de,0x7d7faef3fe77bff7fafd,0xf7bdf79eefdd7b7f6ded,0xfb7edfbfeffbff7f6fdd,0x7ffffeff7febfbff6fdf,0x64d2398609560830d921,0xc3059548165454585082,0x19715061434d8408c61,0x9180466223d86049648b,0x20f244a59700d2614111,0x461017553844649b1198,0xc5d49850c465d2893085,0x23d8621d54611d9411e4,0xd820c42614119039764c,0x205625c3259235760805,0xca640051877595c1b5d8,0x65c3119548a640d89724,0x53618120f644a59900d6,0x3d8618464e0159631960,0x861cf604a81534c464d2,0x4a04c571197384660f3d,0x4660d259784465c51995,0x60421932d765c2109860,0x11198004261035870c46,0x16555a61c391814c465d,0x131a61c7699852459537,0xe365e191514da66182d9,0x245b69874e35c9a90814,0x927d4181a6095698559a,0x69826e35c962d916cb64,0x718646593698704b644f,0x89f64dd69816da21da8d,0x421d3698569a24602d91,0x4d3698121a604769706e,0x7697180b646068874a15,0x99381a4c112d98724485,0x169a6622689871a61556,0x9a262269916da481b688,0x65d32d9169a61da69815,0x5a7d4179a615369534a4,0x689862324992d9649a60,0x926da21d985313db5c5e,0x6da65c969875a45c132d,0xb2614689744b65ce6881,0x55291315e45c1a698750,0x391706da6608912060b6,0x1725cb65cc7d7174b659,0x15da5c112d976a460579,0xa154da91935da6094908,0x649b699181a65d169811,0x1f2d977235c9391206da,0x7d9775a661669814da26,0x985da24e0688746364e1,0x2634c21716356164d490,0xb641c91874e154d56897,0x61691604cb64cb68970c,0x12d9179a6055698744b2,0xd974a45c0f69516e45c0,0x83645897698724b65d12,0x9f4c5d698305a4c602d9,0x26102d9034b662271655,0xd9688739a5cd169970da,0x949772558d394937da61,0x87565641894874652610,0x6a5662295656a55c0e94,0x5589795985a5641f9571,0x5d495987256056953182,0x195515a55c9495315e56,0x4918a55c5c95935255cd,0x18254c5595987e554d39,0xa52618959072564df957,0x61d695654e55c4f94875,0x629597725641695724a5,0x95313e55c9595714e564,0x973e525d195317a56610,0x4255c6295717a5661894,0x4600cc02000340009530,0xa031c0b4028406601640,0x6b417a053c118039c0d,0xb4c29309a022507f01d1,0xd83d40e4037d0d102f70,0x44ce128c480117842b0f,0x5bc162455014a050a138,0xc21a9467a198461f17d8,0x21e947751d3c7121bb86,0x233c89b218c82b20607d,0x6f4992261496024dc8fa,0x50a812994a3427f09d62,0xcb622d3cb392c18ada2a,0xc563090c122ff0be22e5,0x2233fccd432b8c9b31e8,0x93768dc436c0d91359cd,0x3c28eb83a90e78393ce2,0x53d58f2b] j) else (if j<206 then (page #[0x413901e402cfe43efcf8,0x55112744210ea430108b,0x9120c47b91ce46bd18e4,0xd2ee4b052a149c524948,0x3d74ead37c4d3d3384c4,0x9851f145651054165001,0xf559d51e53ad4d2529d4,0x598962858455e256a558,0xd2d7275c216be5a8567e,0x1981b5fd17d85eb57775,0x991363e18c8625987861,0xa3267699c26695979652,0x46b9dac76aa1a8a69c1,0xb6f8db9f6dfdb596ccdb,0x728dc83718dc4870b9c0,0x601d607501d0e73d1ccf,0x59e2c7871dfa7741da57,0x1f357c11ef47b11ea879,0xf7fc9fd57ecdf9e7e2,0xb682ba09281f205780ae,0x5854e13484520f9833a0,0x88aa204874a1ba866e17,0xc462db8aca27f895e23f,0x223ad8e4e3788d5a32f8,0x246e917643e908e4048f,0x523942e4f4936a4c0925,0xe997565c39642569950a,0xd9a72682994e633984a5,0xac4801c0004c00c0ba6c,0xd40f81d83606a0bc2683,0x5043f30f06e0d2881070,0xe0307c8499649f206621,0x5a070700e43604a0d216,0xac461ff0584347c1769,0xa661a310878401481906,0x813f0686165689024b11,0xe0385108e88686e0fc0,0x8a70f0bc1ea0a42d0918,0xd08a490d1a151cc378b2,0x681383b00e220c8188a0,0x1a4c89017184ac703384,0x4af12e2d12b4c795a021,0x134400c041dc3ab410e6,0x800f0dc18d0622c43623,0x8710c116154208188740,0xca4084731d22819a8e8,0xe9652489681782445850,0x81a022281e0f2a006d41,0xb8d0fa8491844c10c398,0xc4700420840a0a125175,0x810b1861861dc22c9108,0x6719d05a6686b1984442,0x82201446440244481302,0x3786b6b0562abd2aa65,0xc6140189d9240742621c,0x6487c211c18800fa1ed3,0xec47281403617444454,0x4cc4ab92ce2024c96913,0x3c2e3080f21c82d0944b,0xf6821ed04281c0e41a2,0xfa1e10d25033da087b41,0xb410f6821ed040efce05,0x1346fc66140c0128a067,0xf282e30219bffe705d07,0xd46a479fea3fe0240932,0xf743c2871a470e26782b,0x7fcb0c8f4880466b0029,0x8f48d5aaf7fb0e40152,0x1b60af51a91d3e015c3,0x34400017c0bbe142f95,0x9a3359ed0427c0af2080,0x2e1078c2057cbebd8aa4,0x91431a4bbe9cd63940d2,0x64452011fdd108586047,0x53da088ff1343221a0f7,0x852e1c8ad47cc58b8f08,0x7fb855000c14449c5d78,0xb0203547ec9e82420690,0xabdb383b610b5f13eba1,0xe90630ef8780361ff911,0x174c4a3c749363910d1,0x206189cd483f27d44849,0x1881981af92c46490191,0x20672ff8fda88267aebe,0xa6d123c1044da94fef42,0xc33a15081a8f482827f7,0x9a11fd4cfa8410a203b8,0xdfc218819dbe3fb48968,0x8198bf837d44a8044d40,0xe503bbfd64a14479ebd0,0x14551e90632fde35400c,0x730485f341944407c3d2,0x40b978a3df8cc2818025,0x19f4978ffef011359ed0,0xff0000d08c5060b310c0,0x10e7b410dc82500e01,0x5d3009081b01d1fd4e2,0x55d1318fe00895fff0e1,0x40ca037fc0042243d78c,0xcc7d08e32d5a4ca1d3e2,0x129ffd080042d275fc88,0x9e18125a4c0d94ff1102,43300989] j) else (page #[0xd9a924df302a3bbec500,0x150dba624048da7c412,0x610217de28040850fffc,0xf4120e0af50952483fd0,0x1ff67a58611f58220371,0x5fe564c819b9f4009080,0x541840888b876c06054c,0x33698595029012ff94,0x7c54440093b110c3e368,0xa1e9ff6e9016358512bd,0xe184a8033f3ff4214410,0xa194fc88518f58c28b9,0x7c7d86cc024403fc5642,0x8bb9e8091a5dd5410807,0xd61ab1a8fe008b97fa80,0x657b3a1c08577de82042,0x6cfd42065dbea0a2100a,0xb1e1050cc027924e708,0x10219fec02de721f20a,0x21adfcfcc2a1437bfa24,0x28bfc82002175fe9da00,0x798240ffe02840cc6e41,0xc0253e904197a409b4cc,0x1a17fb00de7c02061295,0x8000440da5ff8420250,0x125d9df21a1483f1fded,0xe5fc1be9a60a06959f41,0x445cd025064fff4c40c,0xcb5ff104ccfcff920800,0x804d75e700646fe1268,0x32a943297ffffd619000,0x71f44c041257e97c411b,0x2a428517fc9ba8410a1f,0xfd2c68238d7c222ebfff,0xa090010e1ff850001986,0x1200010e3fa8822a3a7a,0x12ede01555805373f06,0x8cfdb7f8547a889a4efe,0x3be040300a502e0cffc2,0x8804df7f90499f42064,0xd411ff87d00ad07f7,0x8a3437a247fe881e00c,0x13760a107c56322af8e4,0x193ffd31033c7db4992,0x133aacb806633f2003a9,0x7b0dd44fa02228de1002,0xed48a13dfa9b0021400d,0xbe1159fe903cc780896f,0xe140a09234f15091b7a4,0xd0bd62a22ffcc0411b7f,0x2cfaa80230379971f140,0x488bfa10023cf83f02,0x8511ff95848330f73e74,0x1fe7da913334029feb11,0x3e1da8c958204200811a,0xd8fe7e60441647c50324,0x206d53f4482041535911,0xd2197fffc5a3080e0854,0xc4a3578cfd210bcc0c3e,0x1251f09a0f6b1888a174,0x1269f5983a927e8501b4,0xcffb7184019ca08c8732,0x8051aff1044a87d89218,0x47e100211bfe003255f9,0xcc70e2c3a137e3d91047,0x40429bfca5410010e5d2,0x199718110f88498f250,0xaefea20a20021c3a7c2c,0xfc4d185021e1eaea8810,0xded86c01980f500a327f,0x70913be00324f1dc2c8d,0xc88b000204443891835f,0x8bd9571903cb803233ff,0x69f84009499a625fde08,0x84c4f4813469ff920033,0x7d114b9618fbd23190f8,0xa252847172f00810a97f,0xbc08c9d1ec34420438ff,0x881084fe013a08547682,0x8145081a23fe881901ef,0xbc14abdfc307b7cc69f3,49292039] j)))
def x383l10 : Packing := (259,3,8,2490403,102,14,1251,x383d10)
def x383h10 (i : Nat) : Nat := (if i<103 then (page #[0x1000000000000000,0x10000000000000000,0x108000600000100,0x40000000041000000040,0x50800800800010000000,0x20000000004204004000,0x40005082000080001000,0xc60800800000400020,0x8000000000004,0x41006000100003087000,0x10000000000430000000,0x4000000010304000,0x4002000001000000000,0x20c000000000000000b0,0x200000000104000,0x140000000001009,0x400400000041430010,0x4100010d0801800c200,0x810000000e040,0x50003830000400010000,0x20200600000000000108,0x2030000000c00430c0,0x261020800c000824d0,0x1450c615320100028,0x80000000100181002000,0x6be4c4639a02e0003040,0x83346af14c70608008d9,0xc44550ab000000035183,0xc7412d064b8c8000142f,0xc7520f4801bc1df04718,0xb80e38a5b0ca72a4841b,0x48015abd1424360e4221,0x9fe0b0531d0591863ad,0x64000079818df30e02fa,0x44e037053e073a08b90a,0x848f089b0acc252897c0,0xd4428041e866819fd861,0xd60a563100bab4d2307,0x69f1019400433e11227d,0x1437c85278ed02f98473,0xa08c449853210ebbae,0,0x6aa2590a10aa00000000,0x9202d9807d850c16ac01,0xbc2107f6240000782c29,0x40000000000000000347,0x400000007c65112471b,0x4517189001e802484621,0xf62d08a9000085080001,0x3778dcc2648bd60afae8,0x6e46fd880104d7081c1,0xf8ada8b3748400025036,0x787ab3655c4281941fae,0xcb87943ad3ec2048a828,0x5e1c12bbd05e0184c438,0x620eec85cb8165902a0d,0x45e5148000044038c3e0,0xec2f0000804902c4e426,0x8f8301a3a00000000f1e,0xba6b88be028658167151,0xb0317108901300f1ca26,0xa3d0b69457501415540f,0x10742430000604d10,0x40000000f29800000000,0x1006d63651b4110921c,0x82a50f0631740ab29500,0xcc50a20cf77192b6d10e,0x2c62370304c35b963604,0x132000000000004c1711,0x89b88095c8fb40600003,0x3ba28f13bb09e00016c9,0x17177c2d800071,0x83a461b0000000361c8,0x5e41db244ea872034000,0x87c50cc0003014000061,0x3c8b402b30923252c21f,0x540003456d853a85c000,0x38214461a9a16103679,0x941e80006b680002444e,0xe26380880000000413,0x80e051ead51985400,0x6246c696615920d28070,0xfc00000000000c2fc006,0x122194e0c0000287fd0,0xa03edc80b16922440004,0xa2dfe230820e832a09,0xbb434220000000000,0x681fc17870980000,0xb8427000000000000000,0x2d0000804382d35bc90,0xad3f3a040001ae400004,0x6ee07884c906413302cb,0x141af8c80100a0,0xd18472f34d40,0x72000000008140000000,0xc9d214d30d8000000070,0x5027bc12c0b20000c016,0x7b882043dd877c927e07,0x279141156dc2ea0bbe9,0x2801908bb4a800000001,0x3800020581025c55122e,0x6c402f82ba83696c9af,0xa087405c] i) else (page #[0x2490a80c8847a92012c1,0x34fba781186efec4a184,184448] i))
def x383d9 (j : Nat) : Nat := (if j<103 then (page #[0x1cc1064073041821cc10,0x41854c0106093004198,0x64d82041874c01061930,0x1c43025d830419760810,0xc09760430619710c194,0x65c83441916183024586,0x5cd105c530440974c110,0x4c17360d105c18344098,0x5c8814c1532053021c81,0x48130205204c19520530,0x4c15348130545204c087,0x595204c1634813058120,0x481305c5204c17048130,0x4c18548130605204c172,0x261514c1964813061d20,0x58130609514c17254530,0x4c18258130595604c087,0x261624c0875893061560,0x58930595624c15158930,0x4c18558930605624c172,0x485704c0815c13061d62,0x5c530589704c1315c130,0x4c1985c530641714c098,0x21d824c0816093021d81,0x61930205864c17260930,0x4c15161930481864c091,0x25d3150192619305c186,0x4c5405c531500984c540,0x501315054065d3150190,0x5057050187505405c541,0x5c54024d71501715c140,0x5009161d4064d7150098,0x645875013161d4024d87,0x4815254d205495148152,0x548914c15265d2054971,0x64530549714c15226130,0xe7fa3fe3ee2fd984c152,0xb5eafeaeeabea7e8fe7f,0xf6beebdebdabcebbeb7e,0xef7af6eefedfabfebfab,0xffaff2feefeafdafbef7,0xeb3bf3bb3af37f36f2be,0xf77b75f5ff3ff3f73ef3,0xaf79ff9fb7ef7eb7b777,0xd7bbfbb7b7fb7baffafb,0x3bfbbf7befbebbdfbdbb,0xe7fdfbdf7df3defdebdd,0x6ff6bf5ff5bf4ff4befb,0x7ff3febfdbfcffb7f7bf,0x4342b4e351328011b080,0xb44243b4834534a24434,0x642a470734024334a346,0x22c0b4408fb0c292b040,0x15359032a0202e2e0015,0x9e2a48de2e48c9341541,0xa9daae0105b4b0a0ae28,0x34e9cd342705b4af90ac,0x4a34ed81352cc1353141,0xa259ae01592e238db446,0x34c9d534661d263145b4,0xc5b4b04b34761ba83201,0x47013509891511552a69,0xaa38252a271e241764aa,0xa1ae2e0834424bb4ad90,0x4f4834021ca630982e01,0xb470972616d0aa69c834,0x12350290b2a588344547,0x60bb4a644b4e390b2b1,0x3440863483049522d594,0xdb44686349516a83293,0x665332e1c19526c13438,0x3475d394318894318d34,0x2626160e942981352d01,0xd544b4e341353110b466,0x1503c135255ba63384b4,0xc13524c13449c1344e81,0x48dda635692e48272a27,0x150e423525e3ac079eae,0xe5aa7709b4af57b245cf,0x17d41312c9b42fdeb4e0,0x2a2d1c30f30234e9d415,0x4f34268e344a89b4751b,0xf354130d669536692e47,0x302c4f34c68234c9dc30,0xcf150dd62ca9cf34a69a,0x4409b4375432ea54b2e5,0x2604941317e12e300e34,0x54130a02352b89b51714,0x50cab46ad634460f34e6,0x342ca7a831e12e485eae,0x8f34cd8f152ddeae490e,0xa5c9b4748215244f344d,0x1512c234ebe2ae0e9632,0x67a633e32a2c54130ed4,0xed1a346149b4f20f3414,0xb511e6aa4717ae4989b4,0xc34b454330e5eae4cc9,0x2e0cb491c9950529240a,0xaa76942a4e8cb494622e,0xc9b4afc2152e1f2e2a66,0x4709b5145eb04a292e47,0x344b82353242352c282e,0x5a2c6b4e] j) else (page #[0xcfdeae4949b4355b14ad,0x24178c34b714152d49b4,0xa2263428952709b4efa9,0x3814130f1eae4d18ae0e,0xae2729ae26deae4b142e,0x141314d634e609b4cf68,0x57d433049fb027d634c6,0x400c80600002353797ae,0x3b43402e82802181b81,0x76c7046505c85504dc47,0x9493c8e888083c7f87a0,0x8b34ae4aa0a58a2c9cc9,0xd04ca0c54c28bd0b88b5,0x24eb8e64e20dccd8cd48,0x90e90bd061024fc0f64f,0x3112e52591f11ad18112,0x154c547d4293f53b934d,0x17516f56a563d5d55955,0x9719358f98b98698197c,0x75b21acda91a65a259c5,0xdd39d09cd9c8dc59bcdb,0xf8df51f01ea1e45db9d7,0x561160c2086051ff5fb5,0x23062ae2522161e61aa1,0x4ba4824463ee3b638e34,0xce67262a5ea59655a50a,0x68b286282e7ea79672a6,0xb0eab6a529ee98294e91,0xfacb2c8ac52c1abc2b6e,0xeebee42e02db2d76d36c,0x10f0d304eff6fc2f52f0,0x172e72a72371ef1ab13f,0xf49345f4273d33a335f3,0x68b6476135ab55f52b4d,0xc788382f7e378b73b6fb,0x3a53a079e39a79538fb8,0xc77c23bb3b73b43af3aa,0xbbe2fdd3d87d57ce7cab,0xf8901f81f01a81300bc0,0x5060181340e81fc01801,0x901b344081825016c003,0xc2079640e40f813e19f0,0xc3c25749010c0d501824,0x780c17119a25e1755c6,0x46741d4c444314402178,0x25823e0d20001d023017,0x50c3dc381a4a5e26c278,0x2c81d0747281a1981194,0x17891a0d54742281b648,0xe8874ac26092b884202,0xc20266c458909250d2e,0xcad880270dc441c26b48,0xdcfb45df7c91013c18d,0x39aa643fe2240373ed14,0xe7f081932f1432f4d18f,0xc93f1c110003813ff024,0xe90c6650ff58992bf5c4,0x5bef922003ffe3641203,0x1a0e384719239fc10ce0,0x4859147c0c63a843c72,0xe30411f80c9b234047fc,0x119028f818f734260200,0xe0733429aa12fec110fc,0x40835e821bf00c4f086c,0x1172c18eb8031da118bc,0x3e0631c422051e818c99,0x446265d68920dec0680a,0x13221798506e80d0127f,0x32cf021d52c5bc143681,0xd5070ea9419d91579400,0x7f311117f8218f421cb2,0x7a03b66826fc0477920b,0x1d795318f350dd01ba03,0xcd550c7b8864c89013b0,0xac5622cfe9244cb3f121,0x416538447e035025020f,0x350dbae58d7e021a7f93,0x809617a19e1120378896,0x30704135d0af090ef113,0xbd9053f810ce11201bc0,0xbdd050c0a029f98a7213,0x229c443187434d85e01b,0xc018cfa233c22ea4d147,0x21704153cc4838e04c75,0x910fd81107a90d807384,0xa0dbca8c60e8e20d8076,0x6b88720e689161514304,0xd910c023488b22f7a20b,0xae845fa09e01cca15e22,0x20f2e850c1058f0f0212,0xd068cb760514584df01,0x72b4246af90680678883,0xb1081edd0b3e0241dec4,0x47018f390d40b2e8594,0x4b9847522ee8c4dc189c,0xafe64645d2134087bd14,0x46648f7d2431b843c342,0x90f0c6a2601ae5091c10,0x87710ef811806dc08f4,0x1020ef08ac84e1493586,0x8313259a16018b360a9f,0x36285bf610c3eb16a0f7] j))
def x383l9 : Packing := (203,4,8,5505121,119,12,1118,x383d9)
def x383h9 := page #[0x224001208c05149e1,0xefa5404820000a12000,0x68ec35400191ca260002,0x62803620c233810023c0,0x1c3062c000c03a18,0xe0013ac0000002080000,0x182e001301e1c617a1,0xe441400000002b21a460,0x23520a6010]
def x383d8 := page #[0x2986f49526855348130,0x654814c2bb4d9140ca9,0x36854aa29026155e6dca,0x8636da5689981cc108f7,0x13054a3bc5cb4a40ae09,0xa8aa690261ed254d2026,0x39b42819520530aeb172,0x431b6cab44439029857,0xa2902a58eb691a266073,0x64c49361d40fec2e2982,0xfa4982a6b8a40a96adda,0x8a61ad754da12613054b,0x985c530afd172902e4a,0xdb152a9a40987dd1315c,0x1f78545715c9204c2f6c,0x4c540cfe152b8aa29026,0xa2b2a40986bb5a750498,0x95c971609514c2bbc5ca,0x30cebaa6d3930a8a61e7,0x92a2985779b728195205,0xa954d2054bfa4a9a40b,0xcdb6c54aa6902a5fd24c,0x64ad238891a83104800b,0x45a561967521434f9053,0x52358c21e86607809e37,0x17080981adaa4a4a739,0x70a33be2400300b88006,0x600b87e2401708002f01,0xb8804d00300bc7d2402,0x13005c200233ae240030,0xb8604c035080fc02f10,0x3a83e24100bc3d240030,0x3f01a84000004004c08,0x350405c07c1001805c2,394528225]
def x383l8 : Packing := (28,5,8,0,0,10,0,x383d8)
def x383h8 := page #[0x5bb4200000707b100030,0x2022120a0048183]
def x383d7 := page #[0xc31c654db42a55148130,0x53083b8c86d0a9545204,0x204c35d254cb94817254,0x3481309739c42e551595,0x545204c3792549b62a55,0xc57248130e5e1722a571,0xeb5c2b99303f5054d515,956827073]
def x383l7 : Packing := (7,6,8,0,0,6,0,x383d7)
def x383h7 (i : Nat) : Nat := (if i%103=0 then 0x78001b2d178400008 else 0)
def x383d6 := page #[0x748da54cb94817254530,0x71b0e2172a8aca902614,0x54d722a571545204c226,0x35073407950]
def x383l6 : Packing := (3,7,8,0,0,5,0,x383d6)
def x383h6 (i : Nat) : Nat := (if i%103=0 then 480 else 0)
def x383d5 := page #[0x5c4da54cb94817254530,0xd41d150]
def x383l5 : Packing := (1,8,8,0,0,0,0,x383d5)
def x383samples : Array (Bits × Bits) := #[(0x840a108bec0006,0xd3584ac0e0a004),((word [mask72,0xffffff24640550c50029]),(word [mask72,0xffffff2c85b1021f1821])),((word [mask72,0xffffff61200154008957]),0x503a0ef580c546),(0x4301e824009e18,0x874541086a3a18),((word [mask72,0xffffff000b70212005e1]),(word [mask72,0xffffff28a2b4371545e1])),((word [mask72,0xffffff8880028a0a427f]),(word [mask72,0xffffff04a7252e0a5a3b])),(0x105404001123be,0xd362442c60629e),(0x0,0x0),(0x1a908a001273c0,0x28189ad1958540)]
def x383columns : List ColumnInfo := [(28,0,355,0,7),(2080,0,2399,0,11),(2112,0,2367,0,11),(2064,0,2415,0,11),(2052,0,2427,0,11),(1,0,382,0,9),(49,0,334,0,7),(70,0,313,0,7),(1056,0,1375,0,11),(1040,0,1391,0,11),(1088,0,1343,0,11),(1028,0,1403,0,11),(36,0,347,0,8),(53824,0,54079,0,11),(53776,0,54127,0,11),(32,0,351,0,11),(4,0,379,0,11),(47648,0,47967,0,11),(52768,0,53087,0,11),(44548,0,44923,0,11),(69124,0,69499,0,11),(1568,0,1887,0,11),(4640,0,4959,0,11),(6688,0,7007,0,11),(9248,0,9567,0,11),(13856,0,14175,0,11),(18464,0,18783,0,11),(42528,0,42847,0,11),(46112,0,46431,0,11),(59936,0,60255,0,11),(7684,0,8059,0,11),(16900,0,17275,0,11),(48132,0,48507,0,11),(44096,0,44351,0,11),(44036,0,44411,0,11),(44064,0,44383,0,11),(43536,0,43887,0,11),(42512,0,42863,0,11),(4624,0,4975,0,11),(6672,0,7023,0,11),(9232,0,9583,0,11),(18448,0,18799,0,11),(59920,0,60271,0,11),(64,0,319,0,11),(42560,0,42815,0,11),(42500,0,42875,0,11),(50,1,332,0,4),(13,16,354,0,4),(4612,0,4987,0,11),(49668,0,50043,0,11),(59908,0,60283,0,11),(73732,0,74107,0,11),(43522,0,43901,0,9),(18433,0,18814,0,9),(59905,0,60286,0,9),(50689,0,51070,0,9),(9217,0,9598,0,9),(57,0,326,0,4),(69,2,312,0,4),(42524,0,42851,0,7),(42752,0,42623,0,9),(52800,0,53055,0,11),(352,0,31,0,7),(13888,0,14143,0,11),(47680,0,47935,0,11),(50752,0,51007,0,11),(49696,0,50015,0,11),(34,0,349,0,7),(73760,0,74079,0,11),(9244,0,9571,0,7),(2400,0,2079,0,7),(2050,0,2429,0,9),(50696,0,51063,0,9),(43776,0,43647,0,9),(46088,0,46455,0,9),(9220,0,9595,0,11),(276,8,99,0,4),(104,256,23,0,4),(6657,0,7038,0,9),(72,0,311,0,7),(49665,0,50046,0,9),(73729,0,74110,0,9),(4672,0,4927,0,11),(6720,0,6975,0,11),(9280,0,9535,0,11),(18496,0,18751,0,11),(44608,0,44863,0,11),(59968,0,60223,0,11),(69184,0,69439,0,11),(16,0,367,0,11),(44288,0,44159,0,9),(83,0,300,0,4),(65,0,318,0,7),(1036,0,1395,0,8),(18449,0,18798,0,8),(59921,0,60270,0,8),(9233,0,9582,0,8),(6705,0,6990,0,7),(46082,0,46461,0,9),(59906,0,60285,0,9),(69122,0,69501,0,9),(48129,0,48510,0,9),(1312,0,1119,0,8),(18498,0,18749,0,8),(42848,0,42527,0,7),(321,32,30,0,4),(74,4,305,0,4),(59909,0,60282,0,7),(262,64,57,0,4),(18,0,365,0,7),(44572,0,44899,0,7),(52801,0,53054,0,7),(44098,0,44349,0,8),(18436,0,18811,0,11),(71,0,312,0,4),(43600,0,43823,0,8),(53,0,330,0,4),(272,0,111,0,7),(44384,0,44063,0,7),(305,0,78,0,4),(44102,0,44345,0,7),(51,0,332,0,4),(52785,0,53070,0,7),(5,0,378,0,7),(273,32,78,0,4),(2114,0,2365,0,8),(290,64,29,0,4),(26,4,353,0,4),(80,0,303,0,8),(2118,0,2361,0,7),(8225,0,8542,0,8),(47632,0,47983,0,11),(47872,0,47743,0,9),(41,16,326,0,4),(18438,0,18809,0,8),(59910,0,60281,0,8),(4620,0,4979,0,8),(11297,0,11614,0,8),(4636,0,4963,0,7),(280,0,103,0,5),(260,0,123,0,7),(59953,0,60238,0,7),(59974,0,60217,0,7),(324,0,59,0,5),(49692,0,50019,0,7),(49697,0,50014,0,8),(44546,0,44925,0,9),(40,0,343,0,7),(102,0,281,0,4),(300,0,83,0,4),(344,0,39,0,4),(1344,0,1087,0,8),(78,0,305,0,4),(354,0,29,0,4),(92,0,291,0,4),(18465,0,18782,0,8),(284,0,99,0,4),(3138,0,3389,0,8),(326,0,57,0,4)]
def x383autos : List (List Nat) := [[],[98,131,84],[16,66,101],[16,82,131,100],[48,129,82],[48,129,98,16,66,84],[128,49,100],[128,49,66,16,82,98]]
def x383levels : Nat → Packing
  | 12 => x383l12
  | 11 => x383l11
  | 10 => x383l10
  | 9 => x383l9
  | 8 => x383l8
  | 7 => x383l7
  | 6 => x383l6
  | 5 => x383l5
  | _ => emptyPacking
def x383index : Nat → Nat → Option (Nat × Nat)
  | 12 => lookupWord 35 135 6 13 6 3 x383h12
  | 11 => lookupWord 470 589 6 16 9 3 x383h11
  | 10 => lookupWord 338 423 6 15 8 3 x383h10
  | 9 => lookupWord 9 55 5 12 5 3 x383h9
  | 8 => lookupWord 3 13 3 10 3 3 x383h8
  | 7 => lookupWord 4 7 1 9 2 3 x383h7
  | 6 => lookupWord 1 3 1 8 1 3 x383h6
  | _ => fun _ => none
def x383 : Forest := ⟨1407,12,fun j => x383samples[j]?.getD (0,0),x383columns,x383autos,x383levels,x383index⟩
set_option maxHeartbeats 0 in
theorem geomx383 : graphValid x383 (boundsBefore known42751) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=4) ?_⟩,listPieces_all (d:=1) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem x383Chunk9_0 : block x383 9 0 101 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem x383Chunk9_1 : block x383 9 101 102 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem x383Chunk10_0 : block x383 10 0 129 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem x383Chunk10_1 : block x383 10 129 130 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem tablesx383 : checkedTables x383 12 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact (@block_merge x383 9 0 101 102 x383Chunk9_0 x383Chunk9_1)
  · exact (@block_merge x383 10 0 129 130 x383Chunk10_0 x383Chunk10_1)
  · decide +kernel
  · decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem pl383 : Impossible false (graphGoal 1407) 12 (vars 1407).toFinset := plainA (q:=383) (prior:=boundsBefore known42751) (before_sound known42751 valid42751) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low2431 : Lower false (varsX 2431) (graphGoal 2431) 13 :=
  strong_full (q:=1407) (rs:=[2, 1, 2, 4, 1, 1, 2, 8]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl383
    (index_root (g:=x383) (i:=0) rfl rfl (before_sound known42751 valid42751) geomx383 tablesx383 (by decide +kernel))
def known2431 := extendKnown known42751 13 [(9599,[100,131,82,16]),(17343,[114,67,84,48,33,97,128]),(9711,[100,131,116,50,33,16,80])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid2431 : Known false known2431 := extendKnown_ok (m:=2431) valid42751 low2431 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low1407 : Lower false (varsX 1407) (graphGoal 1407) 13 :=
  strong_full (q:=1407) (rs:=[16, 4, 2, 4, 1, 1, 2, 8]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl383
    (index_root (g:=x383) (i:=1) rfl rfl (before_sound known42751 valid42751) geomx383 tablesx383 (by decide +kernel))
def known1407 := extendKnown known2431 13 [(28143,[33,80,112,97,130,49,64])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid1407 : Known false known1407 := extendKnown_ok (m:=1407) valid2431 low1407 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low54143 : Lower false (varsX 54143) (graphGoal 54143) 13 :=
  strong_full (q:=1407) (rs:=[2, 1, 34, 4, 1, 5, 2, 8]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl383
    (index_root (g:=x383) (i:=2) rfl rfl (before_sound known42751 valid42751) geomx383 tablesx383 (by decide +kernel))
def known54143 := extendKnown known1407 13 [(54143,[]),(64447,[117,80,66,130,96,16]),(44015,[116,83,32])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid54143 : Known false known54143 := extendKnown_ok (m:=54143) valid1407 low54143 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low44415 : Lower false (varsX 44415) (graphGoal 44415) 13 :=
  strong_full (q:=1407) (rs:=[16, 1, 2, 4, 1, 1, 2, 8]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl383
    (index_root (g:=x383) (i:=3) rfl rfl (before_sound known42751 valid42751) geomx383 tablesx383 (by decide +kernel))
def known44415 := extendKnown known54143 13 [(44927,[84,131,98]),(47999,[101,66,16]),(53119,[98,82,16,66,49,128]),(58239,[82,129,48]),(69503,[84,66,16,98,129,48]),(58303,[118,133,33,48]),(60351,[114,67,84,48,33,97,128]),(69567,[117,80,66,130,96,16]),(42991,[83,114,99,33,16,64]),(60399,[80,81,114,66,50,129,96]),(69103,[116,50,129,80])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid44415 : Known false known44415 := extendKnown_ok (m:=44415) valid54143 low44415 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low43903 : Lower false (varsX 43903) (graphGoal 43903) 13 :=
  strong_full (q:=1407) (rs:=[10, 1, 2, 5, 1, 1, 2, 8]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl383
    (index_root (g:=x383) (i:=4) rfl rfl (before_sound known42751 valid42751) geomx383 tablesx383 (by decide +kernel))
def known43903 := extendKnown known44415 13 [(43903,[]),(46463,[84,131,98]),(48511,[101,66,16]),(51071,[100,131,82,16]),(43455,[98,118,81,130,50,65]),(43967,[118,130,81]),(54207,[116,100,49,32,81,128]),(58815,[114,67,84,48,33,97,128]),(49647,[83,114,99,33,16,64]),(51183,[100,131,116,50,33,16,80]),(54255,[116,83,32]),(55791,[83,133,115,67,32,96])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid43903 : Known false known43903 := extendKnown_ok (m:=43903) valid44415 low43903 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low42879 : Lower false (varsX 42879) (graphGoal 42879) 13 :=
  strong_full (q:=1407) (rs:=[2, 1, 2, 4, 1, 1, 2, 8]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl383
    (index_root (g:=x383) (i:=5) rfl rfl (before_sound known42751 valid42751) geomx383 tablesx383 (by decide +kernel))
def known42879 := extendKnown known43903 13 [(42879,[]),(60287,[82,129,48]),(44991,[98,118,81,130,50,65]),(69615,[33,80,112,97,130,49,64])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid42879 : Known false known42879 := extendKnown_ok (m:=42879) valid43903 low42879 (by decide +kernel)
def xdd14 := page #[0xb16a4a0e629062082fff,0x16ad2728c1ee6]
def xdl14 : Packing := (1,0,5,0,0,0,0,xdd14)
def xdsamples : Array (Bits × Bits) := #[((word [mask72,0xfffffffffffff8278ca9]),(word [mask72,0xfffffffffffffe078829])),(0x8c5796,0x1884792),((word [mask72,0xfffffffffffff819b865]),0x31b824),((word [mask72,0xfffffffffffffe1200db]),(word [mask72,0xfffffffffffffec400d9])),(0x4205b12,0x1385302),(0x140617c,0xf06154),(0x808260,0x6740060),(0x430380,0x70e0280),(0x303fc00,0x10b9c00)]
def xdcolumns : List ColumnInfo := [(128,0,383,0,13),(16,0,495,0,13),(64,0,447,0,13),(32,0,479,0,12),(2,0,509,0,12),(256,0,255,0,12),(17,0,494,0,11),(4,0,507,0,12),(42624,0,42879,0,13),(43648,0,43903,0,13),(44672,0,44927,0,13),(46208,0,46463,0,13),(47744,0,47999,0,13),(48256,0,48511,0,13),(50816,0,51071,0,13),(52864,0,53119,0,13),(53888,0,54143,0,13),(60032,0,60287,0,13),(69248,0,69503,0,13),(49168,0,49647,0,13),(55312,0,55791,0,13),(43072,0,43455,0,13),(58432,0,58815,0,13)]
def xdautos : List (List Nat) := [[],[81,130,118],[16,82,131,100],[16,32,48,128,100,80,116],[32,83,116],[32,49,128,81,116,100],[48,33,133,118],[48,129,82],[80,16,33,50,116,131,100],[80,129,50,116],[128,49,100],[128,81,32,49,100,116]]
def xdlevels : Nat → Packing
  | 14 => xdl14
  | _ => emptyPacking
def xdindex : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def xd : Forest := ⟨1535,14,fun j => xdsamples[j]?.getD (0,0),xdcolumns,xdautos,xdlevels,xdindex⟩
set_option maxHeartbeats 0 in
theorem geomxd : graphValid xd (boundsBefore known42879) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=3) ?_⟩,listPieces_all (d:=2) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem tablesxd : checkedTables xd 14 := by
  intro k hk
  interval_cases k <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem caseFA : Impossible false (graphGoal 511) 14 (vars 511).toFinset := by
  have h : Impossible false (graphGoal 1535) 14 (vars 1535).toFinset :=
    index_root (g:=xd) (i:=0) rfl rfl (before_sound known42879 valid42879) geomxd tablesxd (by decide +kernel)
  have e1 : graphGoal 1535=graphGoal 511 := by decide +kernel
  have e2 : vars 1535=vars 511 := by decide +kernel
  rw [e1,e2] at h
  exact h
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low511 : Lower false (vars 511) (graphGoal 511) 15 := plain_low (hints:=13438558465) (by decide +kernel) caseFA
def known511 := extendKnown known42879 15 [(511,[])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid511 : Known false known511 := extendKnown_ok (m:=511) valid42879 low511 (by decide +kernel)

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
def transported : List TransportEntry := [(151,5,94,[48,33,133,118]),(185,5,91,[81,130,118]),(188,5,91,[32,49,128,81,116,100]),(223,9,478,[80,16,33,50,116,131,100]),(239,9,127,[32,83,116]),(247,9,478,[48,33,133,118]),(254,8,251,[32,83,116]),(339,5,91,[16,82,131,100]),(346,5,91,[128,49,100]),(350,8,95,[128,49,100]),(369,5,94,[16,82,131,100]),(371,8,95,[16,82,131,100]),(375,9,127,[16,82,131,100]),(381,9,127,[48,129,82]),(413,7,123,[48,33,133,118]),(440,5,94,[81,130,118]),(444,8,95,[32,49,128,81,116,100]),(446,9,127,[32,49,128,81,116,100]),(454,5,91,[16,32,48,128,100,80,116]),(460,5,94,[16,32,48,128,100,80,116]),(463,9,127,[16,32,48,128,100,80,116]),(471,8,251,[16,82,131,100]),(477,8,251,[48,33,133,118]),(482,5,91,[128,81,32,49,100,116]),(484,5,91,[80,129,50,116]),(491,9,127,[128,81,32,49,100,116]),(493,9,127,[80,129,50,116]),(499,9,478,[32,83,116]),(501,8,251,[80,16,33,50,116,131,100]),(505,9,478,[16,82,131,100]),(506,8,251,[128,49,100]),(510,12,255,[32,49,128,81,116,100]),(1279,12,3579,[81,130,118]),(1407,13,28143,[32,49,128,81,116,100]),(1503,12,18911,[128,49,100]),(1527,12,3579,[16,32,48,128,100,80,116]),(1531,12,18911,[48,129,82]),(1791,12,17405,[48,129,82]),(1967,11,4927,[32,49,128,81,116,100]),(1983,13,17343,[48,129,82]),(2015,12,17403,[48,129,82]),(2039,12,17403,[80,129,50,116]),(2045,12,17151,[48,129,82]),(2431,13,9599,[16,82,131,100]),(2493,11,2239,[48,129,82]),(2495,13,9599,[32,49,128,81,116,100]),(3263,11,1375,[80,16,33,50,116,131,100]),(3391,11,1343,[81,130,118]),(3519,13,28143,[16,32,48,128,100,80,116]),(3571,9,11742,[32,83,116]),(4955,8,1725,[81,130,118]),(4991,13,17343,[16,32,48,128,100,80,116]),(5053,11,6847,[48,129,82]),(5111,12,17403,[16,32,48,128,100,80,116]),(5115,12,17405,[16,32,48,128,100,80,116]),(5117,12,17403,[48,33,133,118]),(6511,11,1343,[16,32,48,128,100,80,116]),(6606,8,1119,[16,32,48,128,100,80,116]),(6639,13,28143,[81,130,118]),(6654,12,18911,[80,129,50,116]),(7039,13,17343,[81,130,118]),(7150,11,6847,[128,49,100]),(7166,12,17403,[128,81,32,49,100,116]),(8167,11,1727,[16,82,131,100]),(8175,13,17343,[32,49,128,81,116,100]),(8183,12,17405,[32,49,128,81,116,100]),(8190,12,17151,[32,49,128,81,116,100]),(8679,11,2751,[16,82,131,100]),(9702,8,2237,[16,82,131,100]),(9710,11,2239,[128,49,100]),(11710,9,18814,[81,130,118]),(11711,13,28143,[16,82,131,100]),(11773,12,18911,[81,130,118]),(12716,7,2079,[32,49,128,81,116,100]),(12719,11,2367,[32,83,116]),(12733,11,2239,[80,129,50,116]),(12735,13,9599,[81,130,118]),(12781,9,2429,[32,83,116]),(12783,13,9599,[16,32,48,128,100,80,116]),(13310,12,27127,[48,129,82]),(13806,11,2751,[32,49,128,81,116,100]),(14191,11,4927,[128,81,32,49,100,116]),(14269,11,6847,[80,129,50,116]),(14303,12,17403,[16,82,131,100]),(14310,8,1725,[32,49,128,81,116,100]),(14319,13,17343,[16,82,131,100]),(14333,12,17403,[80,16,33,50,116,131,100]),(14334,12,17405,[16,82,131,100]),(17342,9,7038,[81,130,118]),(17406,12,17403,[32,83,116]),(18429,12,27127,[128,81,32,49,100,116]),(18779,8,11453,[81,130,118]),(18815,13,28143,[32,83,116]),(18939,12,18911,[16,82,131,100]),(18940,9,11742,[81,130,118]),(27623,11,2751,[80,16,33,50,116,131,100]),(28079,11,1343,[80,129,50,116]),(28134,8,11453,[16,82,131,100]),(28155,12,3579,[128,49,100]),(28157,12,3579,[80,16,33,50,116,131,100]),(28158,12,18911,[16,32,48,128,100,80,116]),(32750,11,2751,[128,49,100]),(37374,12,27127,[48,33,133,118]),(42719,9,48094,[80,16,33,50,116,131,100]),(42727,8,42679,[16,82,131,100]),(42867,8,42591,[16,82,131,100]),(42943,13,44927,[81,130,118]),(42951,7,42683,[16,82,131,100]),(42995,9,48094,[32,83,116]),(43003,12,44799,[81,130,118]),(43447,9,46455,[81,130,118]),(44287,12,58335,[48,33,133,118]),(44415,13,58239,[48,129,82]),(44479,13,58239,[48,33,133,118]),(44511,12,68863,[16,32,48,128,100,80,116]),(44539,12,58335,[48,129,82]),(44541,12,68863,[80,129,50,116]),(44791,9,48094,[128,81,32,49,100,116]),(44915,8,42679,[81,130,118]),(45039,13,44927,[80,129,50,116]),(45041,7,42711,[81,130,118]),(45047,12,42751,[80,16,33,50,116,131,100]),(45051,12,42751,[81,130,118]),(48063,13,44927,[32,49,128,81,116,100]),(48079,9,42623,[16,32,48,128,100,80,116]),(48095,12,42751,[16,32,48,128,100,80,116]),(48111,13,42879,[16,32,48,128,100,80,116]),(48126,12,44799,[32,49,128,81,116,100]),(48635,12,58623,[81,130,118]),(49403,8,43479,[16,82,131,100]),(49643,9,46455,[80,129,50,116]),(49662,12,58623,[32,49,128,81,116,100]),(50047,13,58239,[128,49,100]),(50143,12,58335,[128,49,100]),(50158,11,58047,[128,49,100]),(50159,13,58239,[128,81,32,49,100,116]),(50167,12,58335,[128,81,32,49,100,116]),(50174,12,68863,[32,49,128,81,116,100]),(51135,13,54143,[81,130,118]),(51151,9,43647,[16,32,48,128,100,80,116]),(53086,8,42679,[48,33,133,118]),(53183,13,42879,[32,49,128,81,116,100]),(53198,8,42679,[32,49,128,81,116,100]),(53215,12,42751,[48,33,133,118]),(53229,9,44925,[32,83,116]),(53231,13,44927,[32,83,116]),(53244,9,48094,[16,32,48,128,100,80,116]),(53245,12,44799,[48,129,82]),(53246,12,42751,[32,49,128,81,116,100]),(54206,9,43647,[32,49,128,81,116,100]),(54253,9,43647,[80,129,50,116]),(55039,12,58335,[80,16,33,50,116,131,100]),(55231,13,58239,[80,16,33,50,116,131,100]),(55279,13,58239,[80,129,50,116]),(55287,12,68863,[16,82,131,100]),(55294,12,58335,[80,129,50,116]),(55789,9,46455,[128,81,32,49,100,116]),(55799,12,58623,[16,82,131,100]),(58111,12,68863,[32,83,116]),(58301,11,44223,[48,129,82]),(58363,12,68863,[128,81,32,49,100,116]),(58814,9,46455,[48,33,133,118]),(60251,8,44733,[48,33,133,118]),(60380,7,42711,[128,49,100]),(60382,9,48094,[80,129,50,116]),(60396,8,42679,[128,49,100]),(60409,9,48094,[32,49,128,81,116,100]),(60411,12,44799,[128,81,32,49,100,116]),(60414,12,42751,[128,49,100]),(63871,13,64447,[81,130,118]),(69053,11,44223,[80,129,50,116]),(69055,13,58239,[32,49,128,81,116,100]),(69094,8,44221,[80,16,33,50,116,131,100]),(69111,12,58335,[32,83,116]),(69118,12,68863,[128,49,100]),(69561,8,42679,[80,129,50,116]),(69617,7,42711,[128,81,32,49,100,116]),(69619,9,48094,[48,129,82]),(69627,12,42751,[128,81,32,49,100,116]),(69628,9,48094,[81,130,118]),(69630,12,44799,[128,49,100]),(73703,11,64191,[16,82,131,100]),(73710,11,64191,[32,49,128,81,116,100]),(74214,8,44221,[128,49,100]),(74218,7,44155,[128,81,32,49,100,116]),(74222,11,44223,[128,49,100]),(74223,13,58239,[16,32,48,128,100,80,116]),(74238,12,58335,[16,32,48,128,100,80,116])]
def pri := moveEntries transported known511
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem vpri : Known false pri := by
  apply movedKnown valid511
  apply listPieces_all (d:=6)
  simp only [listPieces]
  repeat' apply And.intro
  all_goals decide +kernel
def signedTransports : List TransportEntry := [(151,5,94,[48,33,133,118]),(173,5,61,[32,83,116]),(185,5,91,[81,130,118]),(188,5,91,[32,49,128,81,116,100]),(247,9,478,[48,33,133,118]),(339,5,91,[16,82,131,100]),(346,5,91,[128,49,100]),(369,5,94,[16,82,131,100]),(422,5,61,[32,49,128,81,116,100]),(440,5,94,[81,130,118]),(454,5,91,[16,32,48,128,100,80,116]),(460,5,94,[16,32,48,128,100,80,116]),(482,5,91,[128,81,32,49,100,116]),(484,5,91,[80,129,50,116])]
def spri := moveEntries signedTransports known383
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem vspri : Known true spri := by
  apply movedKnown valid383
  apply listPieces_all (d:=6)
  simp only [listPieces]
  repeat' apply And.intro
  all_goals decide +kernel
def moY : Array (Bits × Bits) := #[((word [0xffffffffffffffff02,0x47102040c820c0830c11]),0x3f03f81ff800001f8000),((word [0xffffffffffffffff04,0xc1040881096109041123]),(word [mask72,0xc000000007e000007fff])),((word [8,0x882c5902104218288106]),0xfff800001ff81f8000),((word [17,0x1008902432803260820c]),(word [0xffffffffffffffff00,0x1fffe007e000ff])),((word [3,0x2102060608060410608]),(word [255,0xc0fc07e0001ff8007f00])),((word [160,0x48202088414848268d0]),(word [0xffffffffffffffff00,0x1fffe07fff])),((word [68,0x20410491010901141020]),0x7fff81fffff8000),((word [40,0x820430a040604082040]),(word [255,0xff0007ffffe000000000])),((word [208,0x30c38414021802104080]),(word [255,0xfffff800000000000000]))]
def moC : List ColumnInfo := [(43072,0,43455,0,13),(43010,0,43517,0,12),(256,0,255,0,12),(32,0,479,0,12),(64,0,447,0,13),(2,0,509,0,12),(128,0,383,0,13),(42512,0,42991,0,13),(16,0,495,0,13),(43536,0,44015,0,13),(8,0,503,0,12),(42624,0,42879,0,13),(4,0,507,0,12),(42560,0,42943,0,13),(0,1,460,50,8),(1,0,510,0,12),(43648,0,43903,0,13),(42528,0,42975,0,12),(59905,0,60414,0,12),(1152,0,1407,0,13),(42504,0,42999,0,12),(42752,0,42751,0,12),(49153,0,49662,0,12),(5,2,440,64,6),(42500,0,43003,0,12),(32,1,460,18,7),(50704,0,51183,0,13),(17,0,494,0,11),(48256,0,48511,0,13),(53776,0,54255,0,13),(10,4,369,128,6),(34,1,460,16,6),(69121,0,69630,0,12),(0,4,369,138,8),(66,0,445,0,11),(55305,16,55782,0,8),(52737,0,53246,0,12),(48132,0,48635,0,12),(1056,0,1503,0,12),(9,16,486,0,8),(36,128,347,0,8),(50816,0,51071,0,13),(3,0,508,0,9),(2180,0,2427,0,11),(1600,0,1983,0,13),(11265,0,11774,0,12),(24,0,487,0,11),(1,32,94,384,7),(43584,0,43967,0,13),(132,0,379,0,11),(53824,0,54207,0,13),(1032,0,1527,0,12),(1280,0,1279,0,12),(0,2,440,69,8),(47617,0,48126,0,12),(40,256,151,64,6),(2,1,460,48,7),(8,4,369,130,7),(6145,0,6654,0,12),(43266,64,43197,0,8),(5,0,506,0,8),(58373,0,58874,0,8),(260,8,227,16,6),(55312,0,55791,0,13),(13825,0,14334,0,12),(1028,0,1531,0,12),(7,0,504,0,7),(58624,0,58623,0,12),(52753,0,53230,0,11),(18433,0,18942,0,12),(0,8,227,276,8),(2,4,369,136,7),(12305,0,12782,0,11),(49168,0,49647,0,13),(47633,0,48110,0,11),(49161,16,49638,0,8),(69136,0,69615,0,13),(6657,0,7166,0,12),(59920,0,60399,0,13),(44676,0,44923,0,11),(2112,0,2495,0,13),(1538,0,2045,0,12),(4,8,227,272,7),(58432,0,58815,0,13),(46208,0,46463,0,13),(1792,0,1791,0,12),(13841,0,14318,0,11),(68624,0,69103,0,13),(1568,0,2015,0,12),(160,0,351,0,11),(1,2,440,68,7),(55304,0,55799,0,12),(258,64,189,0,8),(27649,0,28158,0,12),(43048,0,43479,0,8),(18560,0,18815,0,13),(6153,16,6630,0,8),(257,32,94,128,6),(47744,0,47999,0,13),(60032,0,60287,0,13),(1544,0,2039,0,12),(1,16,486,8,9),(8,256,151,96,7),(16897,0,17406,0,12),(46084,128,46427,32,9),(256,8,227,20,7),(4740,0,4987,0,11),(69127,0,69624,0,7),(27664,0,28143,0,13),(53888,0,54143,0,13),(57984,0,58239,0,13),(2208,0,2399,0,11),(0,128,347,36,10),(55297,16,55782,8,9),(40,0,471,0,8),(47648,0,48095,0,12),(0,256,151,104,8),(42532,128,42843,0,8),(47632,0,48111,0,13),(7681,0,8190,0,12),(9,0,486,0,8),(46116,128,46427,0,8),(15,16,480,0,4),(4,128,347,32,9),(0,32,94,385,8),(44608,0,44991,0,13),(12297,16,12774,0,8),(4,2,440,65,7),(54800,0,55279,0,13),(2176,0,2431,0,13),(3076,0,3579,0,12),(296,0,215,0,7),(9232,0,9711,0,13),(57920,0,58303,0,13),(42628,0,42875,0,11),(0,16,486,9,10),(0,64,189,258,10),(2,64,189,256,9),(264,0,247,0,9),(268,0,243,0,7),(52800,0,53183,0,13),(6161,0,6638,0,11),(44164,0,44411,0,11),(52739,0,53244,0,9),(8,16,486,1,9),(47625,16,48102,0,8),(44096,0,44479,0,13),(44548,0,45051,0,12),(18,0,493,0,9),(10,0,501,0,8),(6784,0,7039,0,13),(13826,0,14333,0,12),(44546,0,45053,0,12),(7704,0,8167,0,11),(288,0,223,0,9),(42764,0,42739,0,7),(12304,0,12783,0,13),(52752,0,53231,0,13),(4736,0,4991,0,13),(69248,0,69503,0,13),(69122,0,69629,0,12),(47624,0,48119,0,12),(69128,0,69623,0,12),(73233,0,73710,0,11),(33,0,478,0,9),(35,0,476,0,7),(41,16,454,0,5),(3136,0,3519,0,13),(52738,0,53245,0,12),(58370,64,58557,256,9),(12,0,499,0,9),(59923,0,60396,0,8),(2084,128,2395,0,8),(48164,128,48475,0,8),(58626,64,58557,0,8),(59911,0,60408,0,7),(47680,0,48063,0,13),(59968,0,60351,0,13),(69184,0,69567,0,13),(1216,0,1343,0,11),(32,128,347,4,9),(36,0,347,0,8),(256,32,94,129,7),(13840,0,14319,0,13),(54785,0,55294,0,12),(27650,0,28157,0,12),(59906,0,60413,0,12),(69124,0,69627,0,12),(27656,0,28151,0,12),(57888,0,58335,0,12),(47872,0,47871,0,12),(32273,0,32750,0,11),(54801,0,55278,0,11),(73745,0,74222,0,11),(2114,0,2493,0,11),(144,0,367,0,11),(42508,0,42995,0,9),(46090,0,46581,0,8),(42532,0,42843,0,8),(260,0,251,0,8),(42552,0,42951,0,7),(136,4,369,2,6),(50752,0,51135,0,13),(54848,0,55231,0,13),(58112,0,58111,0,12),(68674,0,69053,0,11),(2368,0,2239,0,11),(21,0,490,0,7),(7696,0,8175,0,13),(9344,0,9599,0,13),(73729,0,74238,0,12),(4612,0,5115,0,12),(44552,0,45047,0,12),(42520,0,42983,0,11),(2240,0,2367,0,11),(320,0,191,0,11),(49160,16,49638,1,9),(256,64,189,2,9),(257,0,254,0,8),(69134,0,69617,0,7),(13,16,482,0,5),(26,4,353,128,5),(37,128,346,0,5),(64064,0,64447,0,13),(63616,0,63871,0,13),(68616,0,69111,0,12),(46112,0,46559,0,12),(68632,0,69095,0,11),(64066,0,64445,0,11),(59910,0,60409,0,9),(13833,16,14310,0,8),(69129,16,69606,0,8),(258,0,189,0,8),(39,128,344,0,4),(49680,0,50159,0,13),(68672,0,69055,0,13),(27652,0,28155,0,12),(9240,0,9703,0,11),(4800,0,4927,0,11),(69123,0,69628,0,9),(48160,128,48475,4,9),(59940,128,60251,0,8),(42776,0,42727,0,8),(32,256,151,72,7),(18,1,460,32,6),(11328,0,11711,0,13),(49792,0,50047,0,13),(16898,0,17405,0,12),(18436,0,18939,0,12),(44036,0,44539,0,12),(69144,0,69607,0,11),(12354,0,12733,0,11),(1616,0,1967,0,11),(48,0,463,0,9),(65,0,446,0,9),(55305,0,55782,0,8),(27657,16,28134,0,8),(54793,16,55270,0,8),(1060,128,1371,0,8),(43266,0,43197,0,8),(49412,0,49403,0,8),(262,64,185,0,5),(0,0,511,0,15),(6160,0,6639,0,13),(12352,0,12735,0,13),(16960,0,17343,0,13),(44160,0,44415,0,13),(18434,0,18941,0,12),(13329,0,13806,0,11),(27160,0,27623,0,11),(1156,0,1403,0,11),(6288,0,6511,0,11),(42688,0,42815,0,11),(64320,0,64191,0,11),(42496,128,42843,36,10),(46116,0,46427,0,8),(42636,0,42867,0,8),(52897,0,53086,0,8),(14,0,497,0,7),(16,1,460,34,7),(44812,0,44787,0,7),(53025,0,52958,0,7),(24,4,353,130,6),(130,1,332,48,6),(44,128,339,0,5),(259,64,188,0,5),(141,16,354,0,4),(300,128,83,0,4),(44672,0,44927,0,13),(52864,0,53119,0,13),(68609,0,69118,0,12),(11266,0,11773,0,12),(4616,0,5111,0,12),(59936,0,60383,0,12),(17152,0,17151,0,12),(9233,0,9710,0,11),(1168,0,1391,0,11),(9360,0,9583,0,11),(47760,0,47983,0,11),(58016,0,58207,0,11),(60064,0,60255,0,11),(43008,64,43197,258,10),(58368,64,58557,258,10),(50817,0,51070,0,9),(58624,64,58557,2,9),(272,0,239,0,9),(42784,0,42719,0,9),(384,0,127,0,9),(19,0,492,0,8),(18468,128,18779,0,8),(134,0,377,0,8),(2306,0,2237,0,8),(44558,0,45041,0,7),(44700,0,44899,0,7),(168,0,343,0,7),(272,32,78,129,6),(11,16,484,0,5),(21,2,424,64,5),(152,4,353,2,5),(292,128,91,0,5),(44560,0,45039,0,13),(4610,0,5117,0,12),(44034,0,44541,0,12),(57860,0,58363,0,12),(49672,0,50167,0,12),(13856,0,14303,0,12),(18464,0,18911,0,12),(44064,0,44511,0,12),(52768,0,53215,0,12),(44288,0,44287,0,12),(6673,0,7150,0,11),(49681,0,50158,0,11),(73240,0,73703,0,11),(80,0,431,0,11),(6800,0,7023,0,11),(52896,0,53087,0,11),(44544,64,44733,258,10),(47617,16,48102,8,9),(18435,0,18940,0,9),(6,0,505,0,9),(52754,0,53229,0,9),(55314,0,55789,0,9),(11297,0,11742,0,9),(59937,0,60382,0,9),(50736,0,51151,0,9),(53825,0,54206,0,9),(58433,0,58814,0,9),(136,0,375,0,9),(43264,64,43197,2,9),(44808,0,44791,0,9),(9225,16,9702,0,8),(34,0,477,0,8),(59940,0,60251,0,8),(69190,0,69561,0,8),(140,0,371,0,8),(1794,64,1725,0,8),(17154,64,17085,0,8),(44802,64,44733,0,8),(52771,0,53212,0,7),(59939,0,60380,0,7),(133,0,378,0,7),(48,1,460,2,6),(160,1,332,18,6),(50,1,460,0,5),(133,2,312,64,5),(168,256,23,64,5),(321,32,30,128,5),(270,64,177,0,4),(73744,0,74223,0,13),(12801,0,13310,0,12),(36865,0,37374,0,12),(49665,0,50174,0,12),(17922,0,18429,0,12),(59908,0,60411,0,12),(7688,0,8183,0,12),(26632,0,27127,0,12),(54792,0,55287,0,12),(49696,0,50143,0,12),(55040,0,55039,0,12),(68864,0,68863,0,12),(68625,0,69102,0,11),(8216,0,8679,0,11),(27672,0,28135,0,11),(4674,0,5053,0,11),(13890,0,14269,0,11),(43074,0,43453,0,11),(57922,0,58301,0,11),(12368,0,12719,0,11),(27728,0,28079,0,11),(57988,0,58235,0,11),(4752,0,4975,0,11),(13968,0,14191,0,11),(18576,0,18799,0,11),(42640,0,42863,0,11),(18592,0,18783,0,11),(47776,0,47967,0,11),(3264,0,3391,0,11),(18624,0,18751,0,11),(44736,0,44863,0,11),(1856,0,1727,0,11),(3392,0,3263,0,11),(42816,0,42687,0,11),(55104,0,54975,0,11),(55296,16,55782,9,10),(52736,64,52925,258,10),(46080,128,46427,36,10),(54785,16,55270,8,9),(44546,64,44733,256,9),(55304,16,55782,1,9),(3084,0,3571,0,9),(69132,0,69619,0,9),(12306,0,12781,0,9),(53778,0,54253,0,9),(20,0,491,0,9),(49172,0,49643,0,9),(47664,0,48079,0,9),(11329,0,11710,0,9),(16961,0,17342,0,9),(43080,0,43447,0,9),(129,0,382,0,9),(48257,0,48510,0,9),(130,0,381,0,9),(47625,0,48102,0,8),(49161,0,49638,0,8),(68617,16,69094,0,8),(73737,16,74214,0,8),(4644,128,4955,0,8),(44068,128,44379,0,8),(57892,128,58203,0,8),(6193,0,6606,0,8),(52785,0,53198,0,8),(67,0,444,0,8),(4748,0,4979,0,8),(44684,0,44915,0,8),(161,0,350,0,8),(58626,0,58557,0,8),(2306,64,2237,0,8),(52994,64,52925,0,8),(58114,64,58045,0,8),(47944,0,47799,0,8),(416,0,95,0,8),(73749,0,74218,0,7),(26,0,485,0,7),(47672,0,48071,0,7),(74,0,437,0,7),(12371,0,12716,0,7),(98,0,413,0,7),(289,0,222,0,7),(18,4,353,136,6),(272,8,227,4,6),(384,8,99,20,6),(138,4,369,0,5),(266,64,181,0,5)]
def moA : List (List Nat) := [[],[81,130,118],[16,82,131,100],[16,32,48,128,100,80,116],[32,83,116],[32,49,128,81,116,100],[48,33,133,118],[48,129,82],[80,16,33,50,116,131,100],[80,129,50,116],[128,49,100],[128,81,32,49,100,116]]
def moD7 := page #[0x341986d552605314c120,0x403fd087f003f4127f4d]
def moD8 := page #[0x4c1206d552605314c120,0x605514c120661b560531,0x750b9605514c12074cb9,0xf4d0d5e4d5acd4f494f4,0x275b2ec4dd481dac660,0x3ff412003c002f8d309e,0x60b7c219fe84bf80000,0x38880000740308]
def moH8 (j : Nat) : Nat := 0
def moD9 := page #[0x54920440ba5495148110,0x4419854d524811032953,0x605314c12054d5260120,0x4c1202d5814c530480a5,0x661814c5304815260531,0x4c530481b5605314c120,0x481c32e5514c120661b5,0x2e5514c120710b954530,0x4c1202e58154530481c6,0x2e5b3545304818260551,0x54930480ba54d524c120,0x481c154d524c12032553,0x2e1a54c52030d9860530,0x5c1206a5b62a553480b9,0x2e98455170480cb5cd42,0xad3ee9fb51dea2fb41ff,0x74ae7a57f4afb557daaf,0xbfb17f4afe45f9abf257,0xb65eecbcd96fb2d75ff0,0x7d3af674fce9e9c6bf2f,0xb9b67db6a66ba80efa1d,0x8b8cb9b88a09b89bb308,0x13a364ba3351b325bad1,0x39b6319b8263ac17ba60,0x41b6729b6783a4583a44,0xd3a6d9390ca390bab90a,0x73a3033b0fc172ecba8d,0x23a37b1a9503b9473a31,0x9a439c4b0431b88c1a00,0x4d1b86be9e4ea7130562,0x471180b657aad49a0cce,0x3fe82400bf3f83b1d1e,0xfc00006fe84001e801e0,0x9dd04fc0b019fd007a12,0x439f813b0d059e00c246,0x10232a24180c01e704ad,0xde0090cfc803c05bf83,0xc70805da0903cccec7b,0x23099c122e4411009ce0,0x264803bcc44672410336,0xb610acc4000000005fc8,0xb0201341008604683487,0x3c604d8030080027314,0x3398b58128]
def moH9 := page #[0x48040c200000,0xa4000000018000022000,16897]
def moD10 (j : Nat) : Nat := (if j<206 then (if j<103 then (page #[0x64d825481054d8254810,0x68d925481068d8254810,0x6a1935481068d9354810,0x651a3548106d59354810,0x64d53608102e95360810,0x54d92608106515360810,0x6c995608106d59360810,0x655a3608106cd9560810,0x66153604202e99854c20,0x6c553604206a55360420,0x6a552604306595260430,0x54930481105499160430,0x54951481102e95148110,0x54d52481106c95148110,0x66153481102e95348110,0x54980481106a15348110,0x695934811054d8048110,0x54d524c1106a19348110,0x2e5534c110609524c110,0x549804c1104c5804c110,0x6a5854c91054d824c110,0x64d8254910661a54c910,0x2e583549106c18254910,0x2e993549106e58354910,0x54d52601106e19354910,0x6d4a9609102e95360110,0x2e953609102a55360910,0x65593609102e99360910,0x6cd95609102e99560910,0x2a5a1609102a5a060910,0x684954c1206999524d20,0x6d0954c1206cc954c120,0x684984c1206d8954c120,0x255314c1206c4a54c120,0x2d5314c120295314c120,0x549314c1202e5314c120,0x661314c120605314c120,0x261514c1206d5314c120,0x54d514c1202e5514c120,0x609514c120605514c120,0x6c9514c120661514c120,0x6e1514c1206cd514c120,0x2a1524c120261524c120,0x54d524c1202e9524c120,0x2e5534c1206c1524c120,0x4c5804c1206c5534c120,0x255814c120605804c120,0x2e5814c120295814c120,0x661814c120549814c120,0x54d824c1206d5814c120,0x2cd984c120549914c120,0x6c5984c1202d5984c120,0x2a1a14c120295a14c120,0x661a14c120549a14c120,0x6c4954c520660954c520,0x6d8954c5206cc954c520,0x6e0a54c5206e0954c520,0x6d8a94c5206d4a94c520,0x261954c5202e9944c520,0x2e9954c5202a5954c520,0x2a1a04c520295a04c520,0x2a5a54c5202a5a04c520,0x2e5a54c5202e1a54c520,0x61d8450520661a54c520,0x2e995505206558450520,0x6a4a954d206558450d20,0x6d8a954d206c4a954d20,0x5cd425c1202a5a054d20,0x2e9545c120551535c120,0x6549360520611545c120,0x6dc93605206c49360520,0x6c553605202e55360520,0x65593605202a59360520,0x2e995611202e5a360520,0x66153645202e55364520,0x69ca3661206c49864d20,0x28da1661206d8a366120,0x2cda466120691a166120,0x69492605306549260530,0x6e092605306d49260530,0x2a552605306c8a960530,0x2e992605302a59260530,0x2a542505606559260530,0x61d42505605954250560,0x2a573505602a56350560,0x3ee87fe1fd61d7350560,0xfd97ee5f793fe3ff8ffa,0x69efa77a9bfa5ff97fa5,0xa6fe97f9ffa7fb9fde7f,0x7fe9fda7ee9f7a7be9df,0xeabeeaf7ebdeaefab7ea,0xedbfb6fadb7b5debfeaf,0xdfeb7f6df7b7dadefb76,0xecbf9afdebefafb6bbfa,0xcbfeaff6bfd2ff2bfbaf,0xc77f1bfc5ff13fc3feff,0x7ff1fec7f71fbc7df1ef,0xfb3fccfdb3eecefb2ffc,0xb57fd3ff4fed3f747fcf,0x5f7d7db5f5d7bb5dbd6f,0xd7df4f5fed7f75fcd7ef,0xee3ef7fadfe37f4dfcb7,0x7fe5ef8f] j) else (page #[0xfe7af9dbe75f9bbe6bf9,0xf3d7cf4efebbdbe7cf9e,0x75fdd3f72fd5bf3ebcf6,0xf3ef4f7f3df5f7cfddbf,0x3fdaff63fd6ff4ffd2fb,0x70443ff8ffd3ff1ffc,0xce1b7736a6612008ca3f,0x6f65001c193000c32e1,0x539b900646a401b9970,0x11772805c1c5016768c,0x80991950265650099dca,0x9025d660097d97026265,0x2c1459c804177200cf9b,0xb807636a01859cb05017,0x2e828f4ba090172420f1,0x9b30d16328305cca0b3c,0xb6e83850ca0e2570c353,0x14cb110170440edcb0f3,0x5064c4c05cb12376e844,0x4e9ba143f6a44d259813,0x87854c5c61ca160172c5,0x65ed83197b2e864c1c41,0x197b6cc65eda3197b64c,0xc69eda51a7b72465edc3,0xb220172c85e1831b5b6c,0x2ca5d981260932c8804c,0xca2d0732cac04cb2a017,0x72cd051c5341670cd005,0x5c53601724d40dc03501,0x56ccf519b13d3a6e0f00,0x45983e436d8f511b43d4,0x337050c39c3424d66101,0x39cb432c7190cbdc443,0x62271918c9c245327091,0x215db5472171d18b1c64,0x487666121ad98487d549,0x5289cc94a0632d2569b5,0x34c0e70d3145984a5132,0x193035c64c4f7113145c,0xb94e512e53425c84c4d7,0x2e54965b3510932d4150,0xc957782e95de0a95751,0x854d61e1c957787055de,0x9cc95a2c7196489c6597,0x7854d8129b95c766056c,0x178ca616c30d85b59860,0x62770d989dc1657854d9,0xa87dc268402e99c8dc66,0x723a6a5bc24cb6b7854d,0x1d0e9a973396ddc8e9b6,0x2791f709e04dc6760172,0x19e869c7791e711e47dc,0xc77a1271de86dc67a137,0x6a61404cb7e01721f469,0xdc1891c32a204dc6863a,0x86623525988c442ea280,0x5ca8e0870638e5a98d4,0x1271e64e9a798406c25c,0x42dc09f3d69e6c58c39a,0x8612a69855c5a50172e8,0x6e01831a3670c604dc2a,0x1b726606df0ca1b7c324,0x6df1c01b686a06df198,0xb1d2d71871f1c91b7c72,0x2c81f1531f1132c7844c,0xb823716608dc4c923113,0x54c9ca1c2257954c9161,0xccb2b1032cac3ccb287a,0x9720bd04ca2e532e4b14,0x11c2321d328c504ba301,0x19714d811c536416a4cc,0x864ca39416e8e104ba37,0x1476e0f465c53b19714e,0x14d1c844347210d1db54,0x463471518a1c54634721,0x521fca548732e51ca1c8,0x8487f65521f952487f2d,0x52d71b24b7f66121d19,0xc84c1172d2cb9c54b367,0x2e53959c84c2a7213045,0x8b94f806c939dd824e75,0xc6e14571b351562e5455,0x58b9532a3254958b9525,0x3570d50d5c1542a3254d,0x8d5c555357055571b155,0x92870564d5c856357055,0x75fd815b776056cd1c15,0x5d3171174d1c35d36705,0x978d9c15e1172d74adc8,0x55f0a7157c45cb5e3570,0x2589e553605c2e58045c,0xc56920721a03ccb632a3,0x6e9b1a4ca6a692a1a881,0x5a97052661b955986d41,0x16e1c905a972416a5c50,0x65ca752870dd4a5c1754,0x20721e011c87719721d8,0x881c57a19715e881c579,0xc19721ec81c87a19721e,0xf465c97c20701f104b97,0x7e0a32df865c87d0a721,0x20198ca8026725fd04cb,0xc8812672] j)) else (if j<309 then (page #[0x6a61198c483267060865,0xdb88b4c6de2c65c18641,0x93263d55958c416ea2d2,0x29c5920a72e4465c5902,0xa32e5491c6941970e4c,0x505ba9c4b6e27105a596,0x416a67811cb9d426e27,0x9011c5a3416ea8905a9a,0xaa19716a598a9a7412ea,0x780a201c4032000180a9,0x81df06c817c054412603,0x2d30ac828a0988232082,0xcd0e983780d3831d0bd0,0x11234463110841b0fd03,0x159453714604f913404b,0x98863917f45d416b458e,0x607261bfc6e01ae06881,0x85120a47f81ec07891d,0x99d259492823e48cb225,0x7c2964a2527f89d92708,0xc2e04b442c68ad22ae4a,0x32c0c5e30acc062f5cba,0x678d903590d323418cd4,0xfce6e3910e1837b4dc33,0xf363c1cef43af0e9e39,0xfd33eccf913df8f703d3,0x90415d03a408500e3fc8,0x8459513a43f10db42e90,0x4a31241482d1e146d919,0xec93964dbd3364be12c4,0xdd49151f946950453d84,0x1599558954054794f352,0x6bd5a1d64a588160a573,0xe75ef179a5d9d72e5bc1,0xf632d8a361a983c60297,0x6975a1e67959ac658190,0xd75b266c09ac96a85a92,0xa5c7d70e5bff6f69b9b6,0x5da57675d5874cdce572,0xe0077cdde5770ddb576b,0x7d796de4078c9e1b784d,0x17c11ef47b6decc7a61e,0x7db1f5f7d5df357c85f1,0xfd9fdd7f09fac7e45f7e,0x1a075818204780b20137,0xe0fd836e0cb82ee09d82,0x19c85c21588502129844,0x1188021e5873a1c086d2,0x789fa268894223588862,0x8cca30c8bc22d68aaa29,0xf423b08e5637a8d8e353,0x3a43e90764048fd23e48,0x24ea931a4b4926e47691,0x5b5964e575951252a941,0x6a9946644988a5fb9796,0x39bae6dc9b1e6af9a466,0x9e4a7709d567499c8e70,0xf281aa00a7e99f4e7b7,0x3e8baa272887a1e285da,0xe968a552918a4028f1a3,0xa08a7969cda6d299aa5e,0xc2aa66a87a98aa3da86a,0x7ae2ab65acf6b11ab96a,0xb18ac4fb0d2c0faf6abb,0x5aed3fb44ece7b2d2c88,0xeee20b7faddeb70ed97b,0xfc00f04c017e826e7db8,0x3df01fc0b007ba10007,0xfe8c9e0800bf4010064,0xe0039e04e005c1200dd8,0x187016e873c0d701403,0x17c2c00f2e08d0d3604,0x6f606d821603780805ad,0x8017800201c806bd0,0x40fb01740c781a603e06,0x1ab03e0ae01e3412e877,0x339cc0050010006002ba,0x1808066b811e05208ce0,0x4a20c10ef482300f80f,0x8c00fe05400c010a023b,0xb825b81b602212d00f00,0x95c183c012808e43982,0x35703120c000e203d868,0x3a03fe0401fc04702940,0x20ec82ad05341100e060,0x8180c50181a0aa032c01,0x30052b096e0200e4a0af,0x5a0838150d808288ad90,0x455d0c7c09e811602281,0x28b00283b0d63858e193,0x428310230086c33c1280,0xf207c50703fa29e8ff83,0x53824c0e80c6c03fc04,0x1455fe0304f012a42fdb,0x603b11e520a10a1027b8,0x868009f2d5d80c85cabb,0x200a80650cb5c0421c1,0x51813a083014860a828e,0x2532840378c02980960,0x80d2044816605d13cc06,0xfe03c069807098300e82,0x305616741a862b7a2e03,0xd507b01a] j) else (if j<412 then (page #[0xac1b50d0915708920302,0x4727146c22d08a19842b,0x803f9206e156c0c1220,0xa40a804b20a3c02b0292,0xe0538a8c1dfc06f021e0,0x8b80bbd0574ba0412c15,0x883699cd06559cf82ba,0x55c412c0cfe0d845cb2,0xe4350300d8121e401024,0xa1590c6437094530e04a,0x302a5c00d120e1db80ca,0xa18095c01f34f98241e0,0xc2caedabdc40faa65825,0xa1827021c0f323c0138a,0xae4eb9db02822a493060,0x259e0c41ad069039fe81,0x68680ea2940a019699db,0xe79b5e293812e6db8a68,0xd87607121c4e0a21e4e2,0x56b2498196625f0c044b,0x25870d82b24cc87729d2,0xb805e938955c8bb40082,0x912080dc15a80c512c04,0x93b3e0605d094c0c7044,0x1c1020607007f0622405,0x42a429a702220501e940,0xbb20a2196c4f82b604b,0xbb243882aa053818ec30,0x6a0268b80b6101840814,0x20ca8100a60575a0614b,0x458116083831a040810,0x5997c15b203fc53c822c,0x1858800012fb3d461980,0x400cb3801ef8c5f71,0x89003c16c00eee887efe,0x16500000f06321be635,0x299b0fe328432b61fc65,0xd48e10885022f3412228,0xab520658c3f8ca10cb8f,0x510658bd1735110a5edb,0x72045edbab51065edbab,0xf51c12291466e208aa33,0x5843a4a3e5102391d2cd,0x34517e2a38412140fc4,0xc81140f5fb81a281ebf7,0x5416403d7ee408a07afd,0x1e24d189f0ab0994819e,0x9e04913690d272341a1a,0x210a69391a0cd272341f,0x8343cb822452021f2752,0x132908ab8224521a4e46,0x3e00025f67a743a1ddcd,0xec0b3e4a401efa5f1522,0x2f9f8a916eec0b3e4296,0x8205543d498e2f660d6e,0x60596a940008fd8150a5,0x384a240cb2a2a5235819,0xe78e2a9418f043f75c20,0x70834a7fd81c23289f85,0x7454e2e1d3f00ad3f4b0,0xb3857fcd571acd0860f,0xf861010e061fbc35411c,0xc213fff8a021c0c30bff,0xe4070c241d143223e874,0x259d2834054a38d06527,0x78b221e1dc280c274002,0xe21899c6ca1801ef2634,0xf10eca40005ff74e8f00,0x2811fe8f6f00e221e6da,0x8fa6c0e72171f4d81ce4,0xa64f02848fde3c871acd,0xe198b04fde3c8722ce0,0xea670d9ff0145e105258,0x188563ff42100829400a,0x72d88007520a5562f540,0xe40984740958bd500621,0x35215ff3185d48ced,0x1293d161c4252160fe2,0x63045ecd06c6037be96d,0xc0e3122f200129b3fa01,0x6623b76fc400330af180,0x2bc903680afbca0409ee,0x403068f98030779fc009,0xf84a1870621cc0344474,0xbf843043394cba181441,0xf530225f3bbc60069006,0xe740a00061dbe1204c97,0x1d28dfea1004a4b7f83,0x1a4d1f62d100ec7a450,0xacf95ff1009b295fee00,0x8400024487979f29202,0x3c3660011a01efffc0a3,0x2a213f8f9cc80099d30e,0x188020a6a600039bb100,0x83445fcec0308c01de0f,0x41000a9bdf90006841c1,0xb8220044000c600a7f90,0x226b040ca02abf04ba7f,0xb3e794800d102fd8030c,0x1801a32bfe2300349cc1,0xed10a18a6d75903613af,0x6234f13944001d2d5f88,0xae0a1001] j) else (page #[0x3d5e8c2e90bc92396036,0x46ce05dfa41488c1aa73,0x4702b04c52b270fcadd3,0xa60008bf55aa06129d2f,0x4ff8234a031fd6290494,0x62322916f88c8a300003,0xdac11a5cdb1ba98637fa,0x9a6e366988c42964e079,0xd1ff0dd08a7f6094891a,0x15afff1494006adf911e,0x261ffeec111082b00cc3,0xa980cffb3c1b0a4b0986,0x911de15300061fc0d926,0x1c791434e3a7000cbb,0x21c22000000f43e45280,0xff87868c8536bc5fc30c,0x8b7df688776a6184030,0x107f5dca74653a64830,0x4c300043d2f668d174e0,0x10781e9194414c031786,0x6200f7b99545944d2d40,0x30296fc40001b3c42,0x137e5839954e38a,0x9e498ea1f629f6986000,0x69b080000000000055ff,0x1a98a682db081ff28d4,0x94621c2789361f7e9040,0x44094316b7c0e165eb18,0x787060653854e0606ab0,0x46cc2cd1d69b10dd0cd0,0x310f1642629cf8468201,0xcbe85100506e227aa0a3,0x258878b2fa345e94d883,0x378261e0d26a098e8f45,0x947638363820dd6c4183,0xf412bb3051715149f484,0xa0b711ae1689ce668806,0xa2680a5076ef28b76ba0,0x13dd0def048386715d72,0xca0bafe68a9b0271472b,0xd09985ab6c4c7c1a237,0x30da5f618e78a843b7e2,0x52382cc9fe1830033cf5,0x8e8783e14863ce283994,0xaae86ae863958b0c1786,0xa4aba122441b51c09eb0,0x5856f7d00484b3472002,0xe29dfcd18c3b4f86e43,0xa7e224361f080930f3bd,0x6cf210c1abfd27a42521,0x49c4e4000252d5fc0514,0x528a3abfdd005484ed41,0xc1029a4ad92612d07cea,0x8d05a38585ae214c1e1e,0x717e14346835f45ee068,0x8eeb02f1190b2f840498,0x51074301b36c3d246cc6,0x32aa249cae12aed05ef7,0xf119825528e4f8281a3b,0x406e60e1b105ee06133c,0x8bdc0e5c3231470d982f,0x8000effc8982629b6e12,0x84376dab306b600c3918,0x18d1df1891ce2910c77a,0x6180065f8a3caf840a39,0x97c202b7db4c3a5caaca,0x8d7914a3135b02d2526,0xeb50414e248e33c41162,0xdcd6e261d1dd06165258,0xbc01b3460127c42a9c4b,0xb0d38602d6134aa1ac5d,0x94c31ea85abf1f0af7e,0xa4317760203b4710060f,0x9bb859051389bbfd3b83,0x394be513880387f40b38,0x98a34989d31135b4d89d,0xa353fa89a300fadc5cbb,0x86b34f5154f888ff7a4,0x3e6cf4e200001c7faf] j))))
def moH10 := page #[4329575424,0x60000008400028a00000,0x23001034000000010780,0x20a800000824006,0x1a640000000000000000,262912,0x20e000000000004240,0,0x12180000000000000,0x4050003ec0000,0x246000000000000000,0xca00000145a9d000,0x10ecd200000,0xcea003976e10000000,0x3015c08861000000000,0x10200000000000000000,0x20000103c0000000,0x856000003890000260,0xb4000000000001,0x120c8400000000,0x850000000000000000,0x122607000000000000,0x44d83800000000000,0x51015200149e0400000,0x744140f80064b0000000,0x4049603980000000242e,0,0x60b0000027d00000,68550656,0x21b00000000000000000,0,0x2e00000000c0c0000046,0x680000000000000000c,0xc800658198000cf000,0,110738]
def moD11 (j : Nat) : Nat := (if j<721 then (if j<309 then (if j<103 then (page #[0x54810649520418254810,0x41a35481065d5204193,0x6498204153608106a552,0x60810651820419360810,0x41a56081068d8204195,0x6a192041a5648106a582,0x54c2064d53081a564c10,0x81a854c206855308198,0x64d8108153604206a553,0x644206a581081a360420,0xc152604306859808153,0x659810c1926043064581,0x60430689810c19760430,0x44130481106a1910c1a9,0x54920441514811054120,0x48110601204415348110,0x44193481106152044183,0x68d20441984811065520,0x4c1106a120441a548110,0x441534c1105493044131,0x60930441814c11060130,0x4c9102a532441a54c110,0x441a54c9106553244185,0x2a55244182541106a532,0x5491060d524418254910,0x441a3549106815244193,0x54d8044152601104c580,0x60910689804419360110,0x441936091054d82440a9,0x68582441a06091065582,0x6091069582441a360910,0x441a960d102a583441a9,0x68993441a36491060d92,0x24d2025493481a564d10,0x481a124d206609348195,0x69c93481a624d2069493,0x4c12025530481a824d20,0x480a84c1202953048098,0x54530481314c1202a530,0x4c12054d30481524c120,0x481824c1206053048180,0x66130481954c12064530,0x4c12068930481a14c120,0x480954c5206a130481a5,0x55131480a94c52029531,0x4c52065531481944c520,0x481a94c52069531481a0,0x61141481735052054d41,0x50520651414818750520,0x481a7505206614148195,0x695434819550d2061143,0x54d2065153480a954d20,0x481a954d2068553481a0,0x54570481425c12050570,0x5c12055170481535c120,0x481845c1205cd7048171,0x61173481985c12064d70,0x5d12066174481935cd20,0x481a2601204c580481a8,0x54d81480a96052024d81,0x6112068d814819360520,0x48198611206558448187,0x54d91480986452024d91,0x64d20295934809864d20,0x4819564d2061d93480a8,0x66194481a564d2065d93,0x6612068598480a366120,0x4c19524530648914c1a4,0x694914c1a22453066091,0x605302a5814c09260530,0x4c1a060530649814c152,0x2a1914c0a56453028991,0x505602a5415819264530,0x581735056058d4158142,0x5c570581635c16059542,0x7f17f69573581425c560,0xdfd5fe7ff3fe9fbc7fe3,0xdff5ffaff57f6bf75f7a,0xbfb5fbefdd7bfbdf5dfe,0xefff7febfedfeeff57f7,0xbcfbe7bf3bf9bfcbfe3f,0xdf77fb7fcffe7fb3fb9f,0xffe7f73ef7ffbfedfdef,0x76fbafdbfeddf5ffaf7c,0xdf7efb77cfbdfdebeeff,0xfbfbbffdfeefef7efbf5,0xff7ffbf7debed5f3ff7f,0xd7f63faffd3fe97efff5,0xdffeeff57f7ffbdfdbfe,0xfc7fdffedff5ffa7fcff,0x407ffeffefff3ff7ffaf,0x536894a913012e87c017,0x2ba47016da200b6ced1d,0x3265401a32800d993008,0x1533000b597005ecb00,0x281a30112dc80206a4,0xb5023ed4011f68c09035,0xcca021f6e808137404c5,0x2068c1cdb2e087196043,0x28fb741009ba083ed184,0xa1679940b3add05326c8,0x980b36cb859c6582ceb2,55581801] j) else (if j<206 then (page #[0x421b81012d987896e039,0x1304dd091a6a04811742,0x88d1a6606013742e7d93,0x694750b443a09ba1a14d,0xe32c4209ba1e40d10f21,0xf2d5327aed9131b65c84,0x3b04da9c826e4e1cb264,0xaa5026cd2813667e09ba,0x6c94c11749a08ba4c04d,0xe34cb409ba5938d32c82,0x26d985f38cc2f1b69d68,0x631edb30916d1849b66c,0xcb3936d59a9b02cc55b2,0x661ac5b72d5215368165,0x136aec88ba6f6e59b7ab,0x19b77638db3b076d9d8,0x87045cc2022e5ec1174f,0xb44076da2013631008b9,0x2ea4612e71d3d428d38d,0x3b6d4a09b39e045ccd04,0x41db6b004dd56066de94,0xc004d95c836cedc41676,0x4e1026cf0413658209ba,0x64c0262a60070a9c33c5,0xd37200e9a9004ed1803a,0x4e9b80174d400ba68c05,0x270d401236a009c3460,0xd01236e808637404cdb5,0x6a411832c08d5940470d,0x1b660a8db9040adc0223,0xcd5940670c983052e819,0x774a983a36a419732e0,0x1843a6d41dd34a0ee9a3,0x6e821c36a10e1a50870d,0x997414d5a50970dd040c,0x4cdb30a74d9053369429,0xb66dd05236e82863741,0xb05b36542d1b2a16d594,0x6a42d633016b9970b60c,0x732e18c1960c46dc85a3,0xa8db30d46d4862c66031,0xe74d407236a0391b6a1,0xa87ba6cc3dd3701ce9b3,0x6a045c37020e1b21074d,0x1b742431ba1258d40938,0x68da91346cc09b864c4d,0x1546dc8a236a4511b722,0xc0b3864c591b702a8db1,0x6e458bb622c8da91658c,0x63742e8da5170add0b0c,0x8da91858cc0c236e85c,0x1a76d88d236cc651b723,0x98da36e86863743431b8,0x6e8711b5238c1961c18d,0xdb4a3aeda21d76a90e85,0xc31ba1e46d28f3a68879,0x215ccb90ae6e8811b743,0x911a36c8891b72428da9,0x66092aaa64961522418d,0xe3264a61b52450d4123c,0xd68ba2650d412bc66095,0x26b4d1935a64c9ad3064,0x193cc54c9ed3744d69b3,0x6609ec3264ee99327b0c,0x3b504f61a327b0cc13ba,0xf61b827b0d993d86a09d,0x28aac194586e49dd3724,0xc940c6e4a0c370513585,0x548a4c3745015ba2830d,0xc3745461b92a78c994d8,0x8f1852c30dd15986e4ac,0x2c46d2963c660b1e32a5,0xa963c6a0b11b5058f1a5,0x660b5e3705831b82c78d,0x1b3060a1a82f18da973c,0x415b3310adc18286a0c1,0x3392a999946d4c9c3306,0xc9a38660d1c1726831b9,0x604d6aaa66b55313570d,0x2b62708cb93818dc9bbe,0x68da93a46dc9c056e0e0,0x3b0add1da36a4ed1b507,0xc1e232e4f11b747631ba,0x6d4f51b72788da93c46c,0xd32681315340745ca023,0x230b94174dca03a6a501,0x4246d4a1232e90863728,0xca2236a50d1b748431ba,0x6c92029748e8da944185,0x636a948da94a18dca48c,0x88da94b0a5d25a32a52c,0x4c46d4a6232e93029749,0xd26a36a5351b749831ba,0x6a53919529c8dba4d18d,0x1952a28da9504654a7a3,0x88db35246d4a88c2e545,0x5646d2ab0c6e5551b64a,0x42c236a15d1b4aae8da8,0x69d692b4cb48da55a46d,0x1b50b631b85a46d42d24,0xc8d985d46cc2e2365571,0x6178cc30a46617d2b30b,0x62c2a1a1] j) else (page #[0x1a16230dc30986cd84c3,0x30dab1186cd88c362c4a,0x2186e18cc364c661b163,0x194c36ac861b26430d8b,0x6acd54a566aa4ab3186e,0x95266aa5cb3382e59aa9,0x70cc33556559aa302cd4,0x3556d598a36acd55a566,0xd9de172ce60b967aadcb,0x30cf359567b4c0b3d554,0x1b967aad9b3d86c99de3,0xb0543458261a0c374ce6,0x44954da2c174d160a968,0x1a2c330d149536898a9b,0x66d059b168b0d834586a,0x1ba684edd34056e9a2c3,0xaa5cb4b82e5a6a952d36,0x4d56c9a6ab62d355b069,0x5aaaa62d555b96918dcb,0x72d630b96b30d9353e60,0x9826baaa9b5d8549acc1,0x30dcb5be661ad6330d6f,0x6a8685b1e330d861ba6b,0x9b9e330db55536db0a93,0x6adf54b36f78cc37282e,0x1b36f78d8b7a82e9bde1,0x785cb8282a1c1414ae0f,0x83c661c2aaa6e1615270,0x5c9e330e2a1a87050d2b,0x72e6a0a97350d4393c2e,0x1b3742ed8ba236a5d1e1,0xadd3a106d9d09368e85,0xa966c9d4c360ea8da975,0x5d8636aec8da97618dcb,0x50f031b87620db3b236d,0xda9790a5d3ca32a5e51b,0x50543d28295e82b74f28,0xd5564de94152f48ca97a,0x5ed1952f6a1a87a50d2b,0x52f68d987b465cbd8c2e,0x1b97d6a5a3e236e5ed1b,0x6acac08c6e601ab2afe3,0x1a36ea086371048cba82,0x21863630cd59585465d4,0x63108da98846dd430c6e,0xca98a46d4c4906da2063,0x185cc5a32a62d1b53148,0x6c35ce35a969188da98b,0x23ac2a71c61b38da0c24,0x612135549030dc47d866,0xd8492a0c248986e640c3,0x86c9c9c36124e1b27250,0xabc662561aeb2a61b994,0x65863632c61b89530d8c,0x2f30b9879818d9cb186c,0xb99b18d8cc8c6e26173,0x58cc4e856c6702975363,0xe8e6de74bb633a8da99d,0x67c2b673c15ba9d1adc4,0x5340b198a04654d00c2e,0x198a246d4d08c2e6851b,0x18d8d1a32ea8d1b5344b,0x30c6e294636b4a8dbaa3,0x6a11b4b5031b9a718d9d,0x735614baab18dad40c6c,0x1b1af46d456a3686b463,0x20db580c6c6c11b4f603,0x8a368ec519476239b7b0,0xacd1b4f6450b3b246d25,0x4b688da8b346d2d9a368,0xd95b646d45aa36a2d11b,0x4cd9dba3662dd1b316c8,0xc856eae06b71708da9b8,0x6ec2975768ca9ba46d4d,0x638a8ca9c48ab2e1236a,0x163c720d8e3405cf1883,0xad864a36632602cb8f0,0xb3d6542deb7414f5b30a,0x69eb6a2ef5a5177adc8,0x5238f5ba1a7adc0d3d6a,0x5b827b2d993bd6d479eb,0x7acc145c2e8a2e172516,0x45c6a0a14b5051719828,0x4a2e3705065b828b8d81,0x7450a5ba28b8dc943d6e,0x1a52ab8ca955c54ca6e3,0xb8dd155c6e4aae36a557,0x65c6e8aee3725771b32b,0x8cab2a46571852fb8c29,0x6266f59833b2c119d660,0x5ba337adc99996e0cccb,0xacdc1a566c8d2b36268a,0xb996c8d9fb046d715235,0x4dee3606ea5a537aca99,0x3076f5a93a52dd1bbd6e,0x5b83b7ad49da96a0edeb,0x7acc1e3d6e8eccb7476f,0xf296e4f14b7078a5a93c,0x501eb727c65b33eb8d81,0x528165a340b2c9a0592e,0x5b340b2d8a0596c102cb,0x7ad4a0a96a506cb72816,0x84f5b941] j))) else (if j<515 then (if j<412 then (page #[0x8427ad4a13d6a109eb30,0xa9a1bd6e908cb7484f5b,0xd6610deb26876582439c,0x14b5088a5a84352d1a1b,0x8d39534652d122a96a51,0x34632d8a35c6c119eb26,0xdd23dc6c11d4b748c65b,0x96c92d4b529665b54a52,0x1eb4a98f5954c52dd25d,0x9af4a94d32dd263d6a53,0xa4d7ad9a6bd6a535e974,0xc9a73d2e539eb749a65b,0x9695394b469ca5a14e7a,0xd4b469ef5934f32d8a72,0xa0a5a5507acaa8296953,0x9557acaaaa96a5454b52,0xcc2ea96a1694b74aaf5b,0xd6559adb02cca5b16052,0xee364cf718267b84c33b,0xd164b868b8dc33dc6cd9,0x368b2d8b429685a2b2a6,0xd8b4d96e1a2cb66d065b,0xc4c5aab370d359b269ac,0xee12ad771826ab8c0b55,0xd765526bb854b5dc295a,0x86bb8cab5bf609aeb2a6,0xd2b5dc689aee330d6f59,0x96c9aee360d771a86bb8,0xccb6ad771b36bb8d9359,0xd771b96b7adcb5dc6d5a,0x56c52d0b65654db2e374,0x5c375c2a1bae130dca5a,0x96e1d4cb70e8f59874b8,0x54b50eef5957732dabb1,0xf6a4b87b7acc3d3d261e,0x77e7adcbebd655f5eb30,0xcc4051655fe8b0eff118,0x165615e97104a5a3807a,0x94b4314f5a98932d8c45,0x1665b28a52d3c52968a2,0x38da25a46296a62de973,0xd8485c64e42e30921715,0x461e5ee3312971b990b8,0xccb6b3771b09b88c3cc4,0x3a65b59d7acacebd6e66,0x99fb6d8cfa96a67ccb71,0xd4d03d66281eb2b40f5b,0x96c6914b5344fd98a27a,0xdeb314ef593a77a5cd39,0x5265b5a852dd53bd6e69,0x1ab7acc55996d6a8cb71,0x54563d262b14b5156a5a,0x96d6d8cb6b60a4a8ae7a,0x14b4b70f595b852d95ba,0x7065b8b832dadc196c6e,0x9bb7ad4dd196cae4cb75,0xd4ddbd656eed96376f4a,0x968af149457865babb7a,0x4cb6778a5a5bc52d1de2,0x8465b5bf32dc5f196d6f,0x5c88cb1e44461f128b0f,0x228012c0002230f91196,0x838065c0530041003440,0xd980ca40bcc0a5409640,0x3bc129c112010300ef80,0x970182c170815fc14d01,0xed41db01c8c1b941a641,0x4882378224c210c1fe81,0x9882894278426c8259c2,0xe742d6c2c782b742a7c2,0x404331431c430902f8c2,0x9d038a837583640350c3,0x3e803d6c3c1c3ac83,0x56444684378423c41284,0xac849d84884478c466c4,0xf744ea04dd84cc44ba84,0x4e453e852dc51bc50c84,0xb2459fc58a8577056005,0x158602c5f005d9c5c485,0x6e865a864d4639062446,0xd406bd46a0c6930681c6,0x308724c719070206ef06,0x9e078807718750473fc7,0x1a880847eec7d3c7b607,0x6e8861c852883e482ec8,0xbf88b208a2c892088288,0xc08fe08f008e0c8d288,0x564949c936c925c91909,0xae899ac9850975c965c9,0x489f3c9e849da49bf89,0x4a0a3a4a2d4a1eca144a,0x958a810a72ca650a554a,0xe10acb8abecab24aa14a,0x27cb180b0b4afdcaf10a,0x674b5b8b4e8b3f0b338b,0xac4b9f4b900b80cb754b,0xf24be18bd38bc88bba8b,0x36cc2b4c1bcc0d8bff0b,0x780c6c0c5e8c52cc470c,0xc48cb44ca50c920c850c,0x204d108cfeccec8cd6cc,0x734d634d544d42cd330d,0x948d82cd] j) else (page #[0xe9cdd2cdc28db18da2cd,0x3f0e2fce1f8e114dfd0d,0x8c8e7c0e6c8e5ace4d0e,0xe30ecdcebc0eadce9f8e,0x3e4f260f164f05cef80e,0x8e8f7b4f694f584f4d0f,0xdf8fcc8fb2cfa0cf97cf,0x38d029901950068ff34f,0x7e107210659056904dd0,0xcd90b890a75097508750,0x1f910e90fa90eed0da50,0x5e914cd140d134512a51,0xb391a1918fd17b517051,0xf691ee11e4d1d411c411,0x455231522a9213d20b91,0xaed2991280d26f525c92,0xfb52ea12da92cc12bc52,0x61d34d9335131f930c52,0xc693b493a2538cd372d3,0x1c540cd3f553e653d753,0x6fd45c14495436142a94,0xc7d4b354995489947d54,0x1b950cd4fa14eb14da14,0x79556bd5569540552b15,0xd495be55afd59a158b15,0x285616560795f655e315,0x7c166c16581649d63ad6,0xca16bc96af569a168dd6,0x139702d6f656ea56d796,0x63d7561749d734572417,0xb397a497965786177617,0xf657e4d7d917cf17c2d7,0x5518421831d819d807d7,0xac189e588f187b986698,0x558f4d8e4d8d318c198,0x4dd94399371927991719,0x89597e1970d9635959d9,0xc919bc59ad999f5993d9,0xada0459f919e8d9dd59,0x529a47da399a299a199a,0xb2da9dda965a7e1a641a,0x2daec1adadacc9ac11a,0x45db385b2b1b1b1b119b,0x9b1b915b7a1b691b5bdb,0xf59be89bd69bbf5baedb,0x489c391c2c9c211c0bdb,0x975c881c7ddc655c565c,0xdbdcd21cc49cb65ca91c,0x27dd171d0c9d015ced9c,0x7add6a9d5c5d469d375d,0xb69dac5d9e5d921d86dd,0x8ddf71deb1dda1dc85d,0x58de471e395e259e195e,0xb31ea39e8f5e7b1e679e,0x7def7dee45ed45ebf1e,0x609f4fdf421f311f19df,0xb2df9e1f8d9f7bdf70df,0xee0015ff01fd35fc21f,0x6ae05c6046a036602660,0xb3a0a22093e086a075a0,0x1ca10760ef20de60cae0,0x76616561566144212ce1,0xdca1c961b8e1a1e19061,0x372229e219e20a61f3a1,0x95e282626b225ca24aa2,0xf7a2e4a2cd22bbe2a962,0x51e33c232be315e307e2,0xb4239a638e6375a363e3,0x7a3f5a3e7e3da63c623,0x5ea44f643ee42e641f24,0xb1249e648f647e246de4,0x13e502a4ece4e164c2e4,0x6f6561654be53b252865,0xd925c3e5a96591e58225,0x336626a615a603e5eb25,0x91e67b2665e655663f66,0xfea6e7a6d4a6bf66aa26,0x67a7552741a72be71326,0xbba7a2e78f677f276fa7,0xea7f2e7e9a7d6e7c8a7,0xb1688ee86c684ea82668,0xf8a8ede8e4e8dca8bd68,0x30e928a91f6910e90368,0x6c6962e959a9476936e9,0x942988697e6973e970a9,0xc169b469b029a3e998a9,0xf8e9eda9de29d629c9e9,0x1baa176a122a086a0429,0x4d6a43aa37ea286a242a,0x8a2a7daa71ea62ea596a,0xbceab4eaabaaa5aa97ea,0xf66ae9eae02ad56acdaa,0x2deb1f6b13ab0b6afeaa,0x5eeb556b496b3e2b346b,0x922b86ab7c6b732b6a2b,0xc0abb3ebadeba9eb9feb,0xeaabe4ebdcebd3ebca6b,0x332c276c162c042bf56b,0x766c65ec5aec4dec3f6c,0xb1aca5ec9a2c8e2c822c,0xeface12cd82ccbacc2ac,0x302d24ed17ed0aacfd6c,0x3ded39ad] j)) else (if j<618 then (page #[0x70ed652d5aad50ad486d,0x956d8cad8aad852d7aed,0xb82daf2dab6da6ed9e2d,0xe4eddaadd4adc9adc06d,0x156e0d6e01edfc2defed,0x47ee3f6e352e2a6e1e6e,0x77ae72ae65ae5aee4eae,0x9fee956e912e8d6e836e,0xddeed3aec7eeb8aeaa6e,0x18ef072efe6ef5eeebee,0x592f4baf412f32ef296f,0x96ef85ef78ef6f6f646f,0xd6efcc2fbd2fae2fa26f,0xa3002aff46fecefe36f,0x407034302ab0213018b0,0x76306a705fb054f04cb0,0xb330a4b098b0913082f0,0xeef0deb0d4b0c630bc30,0x30b126b1163107f0f970,0x62f15771537149313e31,0x9c31923185f177716d71,0xdc71d171c0b1b031a631,0x10b20531f5f1efb1e531,0x5b724a723a322f3220f2,0x9ff28f727d7271f265f2,0xcf32c7b2be32b932ae32,0xfb72ef72e6b2ddf2d372,0x33f3287319f30f330472,0x65335c73513345733cb3,0xa7f39a338e3381737433,0xf333e373d673ca33b7f3,0x2cf4247416340533fc73,0x72b4653454f448b439f4,0xb634a77498b48bf47e34,0x600ee03f0034d934c874,0xe840033c13e06e82781,0x8e06f02782002f80101,0x1ad00407201f0178079c,0x8fe06d0d0118c074110,0xc0c6870071603b015818,0x2c0803ca02b014c04e02,0xcc0db823813a08a07981,0x2807ac0ce00814806fc2,0x30701d03346403eb0418,0x8fe824a0ad1481d343bc,0x7c303505302ca02011e,0xe10701e80f0348198084,0x620ae137055802c12013,0xd714386982602f70400d,0x1ec2260430100f182d02,0x7e13682d422d0248298,0x854403501d82805008be,0x205190c107811e19b06c,0x3407825814409cc0ac02,0x650460e9054402039508,0x16c0ac25c15e05283701,0x15015604b044c16a2da8,0x15c1560c03099cc0778,0xb6a24601701807f6031,0x825645cc14d01502a866,0xec31213c180404e05057,0x2080d4180a621df0178d,0x63426619d0ea406428c1,0x3d01e782342bd02f1568,0x16b845c3bd13f0894250,0xd0348081374156088830,0x3063c5106dd0b40e346a,0x6b0d02a781804ba41608,0x18818e0c601e831408a0,0xac1b610380d03a41403,0x2901e30ace0a4a65015a,0x61dd2a28bb0a3c58a321,0x297809c02c050014c19,0x60064201418f20ce04,0xf0225c87445312e9b4c1,0xb0088c1a039586943483,0x3f20ad07749800100328,0x541a6e062a08d04e0910,0x605316f0aa89404a0325,0x41ba0de145403e06d045,0x303a8a6a8ada62043e92,0xbe89ac20616d19e8ba42,0x578226a781d307523db1,0x3fd84d653811ea00015a,0x4d308fb05423b85d06d0,0xc2360ca890902d24d097,0xeab954b840d0d0a1c08b,0xc836790225c43ae2e240,0xcc104215e30826a10008,0x3b02aa57a0d807801701,0x49c0e7900ca5ecaf649b,0x81063390b80e808281c3,0xf151418007c03022680c,0x335f2a854280f3d17023,0x208b902d08b410040ae7,0x1d60021ef40f2d543290,0x45243925972739db00ce,0x66dc2521c60774448340,0x85651884f2c69112e0e3,0xca543267c1825c150800,0x8e1630c9455e20c1040a,0x5692f6205103856c2ba2,75515393] j) else (page #[0xd6480dc3a29c94e8caa2,0x8046995f417acc0a8c12,0xbac9da5f825415ad0832,0x530abca80dc2024961d8,0x490e1a9ce2985516461,0x4aa09bd1bc26c0a46127,0x70610ef04da01059a0ba,0xe82041b1d2297606508e,0xbaa644100cf848124f0c,0x868b420300b9c12aed57,0x2244390ac83a0b4613f4,0xd4413bb2a6a074262594,0xa4290882ce6e2b049af0,0x18612542669222800744,0xa299404a0540b3629b2c,0x119f140809fa0589342a,0xf47208a066724352fca,0x65219d0c20d1a2ce6553,0xa0b54f1868c92a590278,0xc40989a8a44130128218,0xac770dbb0e988aca308a,0x562e81df01821acaf9a1,0xf21bc0cb824edc45020d,0x27e964372130b2659b29,0x15da8417e86b00d002b4,0xb5b846ce1a74c0b28590,0x337cd700182f82ad680,0xa0d0868036da4c0aa867,0x324af23f94048764d815,0x412d705bdca70ae48149,0x19e0ee4b4e0531558b0c,0xc5140a550600a4114074,0x10582254ba04d350509a,0x80c401b2af091e4ab24c,0xb2ed5a84ad269a10264,0x2882d23cd3b24b6c8215,0x5d260481e4240aeb34e4,0x1e853127ec82050e13d0,0x96605aee14c4f20204e4,0x691c41821b2b30235249,0xc37d18b8c3a4c372642b,0x8a4dc04833b4cad03616,0x96536a989caf02b74249,0x6fc27019583ceb0e6f1a,0x69fb1491a06b680103d8,0x621826337a401db46d3d,0xc879c475872cc54861dc,0xfdc843522ae985ac2dc5,0xbfa9d3bc93665c7663b2,0x4651f6925430a06d14e9,0x9d74cad9029b96154b1a,0xb705b4318cb2658b1f6,0x12c6cd2d7b4b844e013a,0x245223e11f0c409e26d,0xe82bc08a855c3c902216,0x70c46a21c15a1690dd0a,0xb0dcdb20999484d18d44,0x7bc2b06cd04877e34c9,0xa22610f3076771be09a9,0xf4a36281b80cbfc92ca5,0x688aaf51089a7e2b4461,0x2cf0ac3c6b3ffef49818,0xcdaa9841040d4000588e,0xb5057e8461804695eff7,0xc35500159df4b57304a4,0x4002affb8456e606517e,0x1d70006bfabed0,0xfee64960b8a614448000,0x6ac2becd3c28f05da5df,0x4fff7b0f241a442831c,0x48331b3dc9d728f06680,0x48850644d576fc5c4192,0xd246484555fff8587483,0xe3698e0d26ff0b2e24c4,0xc30d16c21813599f26c9,0x85b48c07897bfba681f5,0x985c0ac0889e7f3b349,0xff0630a6d180f128f824,0x7fd31e2db8ac086997e1,0xa8f387a4362dba620351,0x26fe6e0e80985c0ac408,0x301e2630e28d34d3810d,0x24857189ffec03840cba,0x105910c74a9f5e3b6c19,0x828b3b158eb1376ca354,0x5505166723216245edea,0x7b7aa0a2cec563ac4e3e,0x78cbe1d0580da2c048a1,0x53ecfd1552810ec05892,0xe5453fe9eb08074592c4,0x2c75893a97e189623419,0x1bcce2025ff0f84591a,0xff0f8458caecf62007cf,0x143ab04bef4848c76225,0x9b232287c7b397dcd919,0x6672e888c6a9f1ead5cd,0x753016c8f53731d365ec,0x8ea0083fb1e89b4e5aa,0x6ac1aa701efec7bb51ab,0x449132a251401dfdaabd,0x121a8c862a4004737a7,0xbc0baa869f8ff8000df,0x8623acac] j)))) else (if j<1030 then (if j<824 then (page #[0x1aa78a91420645fe0755,0xc8d55d5167fba407df79,0x428e690ad559eef24cc7,0x79cca93c4d1d5ed34f31,0x384bf99398c0fe0d53df,0xec032029fe59bd480b9f,0xb94660208213a9008f01,0x7fba902108c883bfff36,0x2945081041052b564ff9,0x2e8110840b13f7f5bd2f,0xeb8d81020436382dffd6,0x1279d0110002208a99fd,0x441ffe9cec10c2d30bff,0x421622181dfc0910842c,0xb082087a827c04f47688,0x8e0082085a78b4bfe6e3,0x84759c60820882a76f11,0x4e853229c3a46351ffd0,0x4d35421e688e99808d34,0xf0007b1f4e37c13998b4,0x33072f764316f60faf04,0x52ab0038ac8204b4de9,0x343f5fb7891d87401060,0x421da847fffa9ce380,0xbc84e034a7d3f99ec06f,0x7eda64318064455a191f,0x6fbf8b13086300d22412,0x27fc4998490c3007154,0xfa3e2f60021806f14379,0xe334e5e4250400254fb9,0xdffa442718c0848943ff,0xdf89f4404861802ea31e,0xf8b8367402430c049d56,0x8ad92cab98248065aadb,0x33e2b52d5ccc6b50a7fe,0xf89a5132260453bc8e3f,0x8ea4ed0e952eb0165354,0xd52001c7e47c1e3cfe00,0xa192f81d2e4851049000,0xf76001bd4dbf2cb0e406,0x2d2c0025481568666752,0x49362631c702ef4034bc,0x1fb99d61a298b0b59b44,0x82438985abe198082ae5,0xe5b41008ea802bc0000b,0x1f01975a011e00017f2b,0xde00000067ede027c,0x5447ac17ff9659600655,0x4785d0f2b9d1a0602f,0x8c00de416e990d1d9c80,0x4301af765601653a1755,0x1e456ffc5762a0c9aba7,0xe7f0c8deac7711925807,0x90c0b83a550010fffc00,0xa0a42d549781e603557f,0x9c435697fdd1e9c2e23c,0x5e97bdf4b20be051c706,0xc0fb01e81d79fc990071,0x7f1010b039ad00000043,0x421ac000018f0bede85c,0x7be2ff9cccb27,0x4b5c685b01fc40745aa0,0x72bf6341ad3186b06045,0x3022a4efceb24428306a,0x181d395fb1a0d7a0cd44,0xf0e82b0367d3f4c05005,0xeb568b700208600d484b,0x11aff779a602981c391f,0x3038857fe6c2aa80a677,0xc657460b0d2f17948c05,0xd072a4d011019d642bfc,0x168c32bce2aa192d366f,0xf4b80b4cdfb4bfec1130,0x2fb79180a6070f570016,0xc5604cec1b7f2b6604cf,0x3c364f1b4c016a2e37f2,0x9f02fca4dac8c058a6c2,0x8c062393fcc1130167b6,0x6ca2a32ac697d85dd010,0x7fb6928ba322a729ee86,0xecff240f5966c980917f,0x8584e2d8f69a084a9e60,0xd1f5212d029d1955455f,0xbd99c680194412860256,0x182293908ca61f2fed62,0x405333880ff6bcaca99b,0x1ad005191d3809fff755,0x321a6e8740ac0d9bcfe2,0x2d3f44ca59d8fc28083d,0xbe7f10d68028c0e9e83,0xc04f90c77195f0c8c605,0x5b3f8080146074c3bef5,0xc98491413facb27831cc,0x9595337bfef678dc5839,0xfd7f6b85d4c8e203fa53,0x332677bf10028c0e941c,0xae288d06245536689fd7,0x4b40146674f27b0a7c13,0xc52c513fcd604ce07fca,0xf50ac8d9e17d924e804b,0xf7c9f685a24653119a27,0xead581330473faa16066,0xc454c1df] j) else (if j<927 then (page #[0xadba98d436dff9ce6200,0xca61e80d71e18cc373c0,0xff6bcaca99b182293908,0x650faf07fcbca6332870,0x66c8c061b5e0ff9794c6,0x3b3969e0a14c0a1d5fb9,0x2e190c2e057edede990b,0x53a4ffe9b4c18562ebed,0x1e66198ff008f0105191,0xf67acc0c550e0f2cf7e,0x918767db29f45350c3b3,0x276fa46161fb67d93f9e,0xa7773e803d7ce63a7e59,0xd9f76918514d93a79a30,0x234bcc35af2b42c43e95,0x7967f4d230c36acda8d,0xca2b14cfbc7e54d330c0,0x232950feb71fdc7b50c8,0x5d0804650a20dfe2e840,0xaabf77c44cac244cbf94,0xffa647f110115638bf6a,0xaabf77c44ca9244f3fd0,0xafc5608e280ca95c7f6a,0xc6265ffdc91c44310c42,0xc27104978ff0791a2b60,0xe41953089b7cd2dbd1ba,0x8cc6a218661fdf145d0d,0x9f67e48e221886209ff,0xc0cc765de2dfa9818ea2,0xebb48c3a8fc102d40050,0x5013fd1a69187d42dece,0x3a9d8b266d0155c9d401,0x284ab62e7d6b58e744ed,0xa81bcd809a3416b1c659,0xd53878de6cbd8d6c6aa2,0x61d4e5b3f182a58c344e,0x4c8310d3f3d71f336186,0xd56005a60ac6abfd8f8f,0x30fe7ad008cb9234d13d,0x1d604a0a84618f99b0c3,0x7a0a7c646633dfe6116c,0x5e60be880b6c154fc3cc,0x59e2145ccca40d51854e,0x8619876b8d98268308d3,0x9f88412a8113cf5c7ccd,0x2f2e410842038bf78e6e,0xf9b6085040354ed102bf,0x1a7648a1030f57024000,0x20d01bfd72e4509188f5,0x40356067fc510b80206,0x980bbe6fd1f6651054c0,0xc01230ae7479de600246,0xfff1408c2082d29ddfd9,0x25fa7aba70421088226e,0x372fd45e961c40302372,0xea8dec5c8a4613e1e41a,0x217acd3f88c758e40608,0xdffdee25a8886cc20208,0x4b93f6d1620842108455,0x51e0ddab0c390c212145,0x4cbf172f2790861080a2,0xa215f07f50c390c21214,0xa4423423ddfdc8218420,0x110608212aaafffcb231,0x41c3369527bb89d5680e,0x845c3730fb10cb08464,0x8c8821f7e3030c8fd40b,0x516202082969f6a36916,0x9efe26c202082ae9e4ff,0xc5c7fd784b60800811a,0xa43305be2f4de0880010,0xc40008062c7f153de840,0x8b7808167173949ba0f5,0xeb5767c0830410154c78,0x5df265111085040d451f,0x3d74a205963e669440b3,0xbd091471fb99ef420522,0xfc9b281000207891fb5f,0x1fe2805019c0100c4b81,0x806a67af1a2a051e,0x380201890bffd0f5d202,0x81041041d42be4e29203,0x8803085040d3a5fce9d8,0x4ff805019c010310f7fc,0x14677affef2084210711,0x100c5cf7a1028abc68a8,0x14b2330520fa328f8800,0xe99c7508000231aa2fa5,0x8062f7a14a245ffc5e,0x806af9e3cb42f35c40,0xa4481fdcc0b6e03d4200,0x6231e5f76ebbb3d78610,0x8210abf9f7412611c61,0x317e7fdbfd0a364ca282,0x707ff756402782200040,0x4d420622d283f2210858,0x2adb86a1050eceee2467,0x5076602e5bf0040d3b3f,0x20a9eaf301739f1c0103,0x82080ea64fe055b5d818,0xa00100d4c1ead2022c20,0x40356065e069ffeab0,0x701ea100] j) else (page #[0xb8800100c5adfff13213,0x98500081a7b64c79681e,0x47608000230acdbffad4,0x2088b0bfd0fa0b21ca,0x806245d5b7f2fbf0610,0x100c4abddfaa374400,0x3141045544b1f922e0c8,0xfe4f90002061f8fa22c0,0xeae2ade37c2082729a5e,0xbc9024fa5d8182000088,0x2a1f83fdb9b622213692,0x7ca0040b373a24f32842,0xfd638cd3e041042b539b,0xded9fc09ffd488a05aa6,0x7203b68fc4210840314,0xdd6a5981f801eef18186,0xe4674e610846c40601ff,0x6948eae182000080ab3d,0x3b7840008162d6fff88c,0x8dd10002018917feaa51,0x32967ed44424d24f87fc,0x130fb327c8001030f9fe,0xda6e7fe46f63a2000443,0xb11109b48df945708209,0xcadac81044f521dfedcd,0x8fc40008062eeffe9f1c,0x4480100c5ab83c3f6bde,0xe210958697fda87b15f2,0x7eb302081024f1edfca6,0x55c97e02044217d1002e,0xabf30cf760acf040088f,0x95a2cbff56d48888668,0x2c3e3fa3c35793b78400,0x2000403158fe0fc20004,0xcc21080e275b3ec9bc3c,0x79fd120040c3f39c1b89,0x5bbef2e1c40008c62719,0x746eff0f514861180a27,0x10ae87c33e3fd8201108,0x44c200046314ce4a3c22,0x9de010412b4fef0fcdea,0xdde662261084471307ec,0xc4f529c7f0c888c66f7,0x22d9c083fffec937f401,0x1fd120048c307fb17522,0xc57987d02001034c6d,0x20520c8f661e2f08001,0x811e23f402052178aaf4,0x40c423ffd0a144000818,0x80010311affd54422000,0xc8c878010aa4df4fec28,0x2e292360865bfffec00a,0x1ea8f9eb1d2f00454d2e,0xa04d4e16df038466e0b0,0x2b29605d4f47e4b5612d,0xde77e4a6809698affb00,0x11444acc5e233781cc42,0xc19136086c125674dd64,0xbd8668f84d9981349ae5,0x4f2f06a18602ba8938fe,0xedfc20df048700ab1ecd,0xacb387f6b40060d233a8,0xfe3064b14134004180b1,0x1344cff06a18600da7d3,0x950afff46d0f3c31802b,0x135561fdad0710b4847,0x3cc55913f128a3d0c104,0x4454c693ffd6b6b10c60,0x3a98c0d21e4ffe95c70c,0x2c0a070e0e008d9308bd,0xf089c4a061156388f89b,0x3f66225c8a1c04d519bf,0x3a7abf03218284204a71,0x380eea06ffdd30418602,0xc30c0174f77c6e720c56,0xd2020c3011d3ddf13139,0x11b2a7ffc233046cd67f,0x46d7fc86300b850ff88d,0x7a23cbf48a61b7402c44,0xc113891fdbba0160567c,0x414746f12c8119927c60,0xc72b656608da27d78124,0x2e18effba90c3005d357,0x18431800316efe2918c0,0x41fc8c80a155fc7d96b2,0x70a8ffd9889c6300c88f,0x2018899c3912dfc8c601,0x51cc1100c403f18a3982,0xf1fb9c306005e32baffc,0x8ea4fb87d4a87006d300,0x12fa830601ae3d1fd218,0xa3e4e54431802d1bf3ee,0x12070031570ff5f3fec1,0x93860d6ff9ae7cc0f5d8,0xbfff6d18440088148a97,0x68f2ff0a08c320387f7a,0x1b9a43111536fe722709,0x57ff9d88030620ba763e,0xc1c964c58be610804316,0xa30be2f067284028757f,0x7eb3ac104238c3c09c21,0x3921bf867a3301cce02d,0xe26ff9b0] j))) else (if j<1236 then (if j<1133 then (page #[0xfadc26a400c10805aa5f,0x74e1d03858b20668024f,0x435717fe6e63202440,0xd970ff4b554905bc3041,0xdee90c3002752de80580,0xc01bf68600aa7038d233,0xf524e1941860056a80d3,0x27c7a3c3103541dfe17f,0x458bfb91d990ec37dfde,0x77ff57974d2670086008,0xfe9710d2722918c0018c,0xd1010d28bfb8c60470b4,0xb0fea10ac601711772bd,0x88061c1f8c4dc1100c38,0x66506200aad5d7fe26e0,0x188ea4014fff2f2643a0,0x3f96901209026d2e7ce,0x2d107fb548039810806a,0x8881888e98bf36ce8a42,0x4e5f9b3246901b435f3b,0x89c1a0c032c789eec9bc,0x418280081cf6406ffdc,0x233079f0c488599e7fc1,0xa3338c601f119fa1890,0xc9c1ff2ec630168777fe,0x400e4dbfedea62888c61,0x1926b7f40c6406080010,0x8ec1100c42f53cc60f04,0x75dd71130414827fe099,0xcc91a406cf55e0312016,0xd99bf00ae212431a13e,0xf5860504100e3d27dd48,0xff08054608080f1d37f4,0xb0fdc4f8b129d05d10b3,0x30500438f0edfa340390,0x4aa16a03988b1fc8568e,0xc4c3023f50352171fbbf,0x69a1fff247f2542d4018,0x34080458e571a2f0300a,0xfc102f0018799f9ed69e,0xd0b9601c63c000d4fbdb,0xf4e0b485e4500a314b7f,0xf2255e1a57e015aa51ff,0x9574a27e42900753fdb9,0x73e008b938de3c102c3c,0xd080771907d486c8d50a,0xa0461e00c6a6f60067c8,0x980aa3c021c683ff0060,0xc7af18d13e20416ac1fb,0x155a10a000430450ab4f,0x5fff8e1d040574fc7f43,0x1888df553c780438a00,0xa018d383fe3c51005a0,0xb7c3c4582858bfaddcf1,0xd38dfd4dc39a99a006a8,0x6ce11437f536804ad002,0xda7675fabfc1251841,0xe201400310278454ba14,0xc71a39200c2bb5fdbffe,0xe2d6c7fe069f158b3064,0x6114d9dba3ded0a42460,0xf814c8a0001aa0f9b0fa,0x498ad10f1806be00417f,0xd262a94900ab18000f5f,0xb000484fc1e00025480f,0x423f8b11e01c8a9aeffe,0xa7cd8002d401d777c0ba,0x83e66887b4cd28002546,0x80298ebbf67cc64014c5,0x98c024d50055fc173b31,0x13c8b3e079d95c7bd4a,0x4829f7643e408c0af0c,0xd25000d1d17b4f50f8d5,0x10b245e5e2180dc66248,0xd5380ddd0f4b4b97c720,0x8071aafbe88785186ac,0x2d50b7fff7ac01c8a474,0x40a6218fed768adb66c0,0xe4e0500a69f93635eca4,0x2828421600deb18fe478,0x2dc1d9ab0fd9c36ffc40,0x808a1a61ca04fdb4aa36,0x2a751a701cb91b9cae65,0x1d7f82847232f0bae4ef,0xf90b0943b5574f100000,0x3080136569f022b3c1fa,0x5e3a9e97d5ddd0844d82,0x701cc015c67381855c71,0x69fcbc9ac8a589f220,0x478c7791822911002419,0x862818933d71b4081bf5,0xa9300a75400054ff9c6a,0x1e6723cf8057018ff955,0x793c8f980806be9210f,0x14096a0002f3233e7309,0x40eba9a82bc9ecfe2638,0xe92551ca155072337c16,0x742405480001fb5f2b1f,0x91b1d053d4e15ab03a13,0xe5bf42e399a6b3714fcc,0x8707ca338a908071aae2,0x3624afdf5a0ba5a700af,553706324] j) else (page #[0x103ca800af8777e0c715,0x4a4029a8082d0fa71449,0x15edc038d58da1e2e0d1,0xc027900bbfbd73f89830,0xa60ea8a6020ab003f358,0xb600598e57ffabeb1129,0x9b6080031600012fe2b8,0x1057560a1f1c07af7105,0xe3bbaa882b080287633d,0x15552ff9420d0d1400c,0x57ffabf73334c340240,0x86245f81d4e8120451,0x212cca2a7c75e076b1aa,0x58a346a00969daffe1ad,0xa7f399a5410060753e9b,0x80631237fc4302292023,0x5a500a6999f651e51c70,0xdca20c880062a2ff9a3,0x8677be01b04458fef9b8,0xf65a34f3b2e8097af59d,0x7603b1000000005bf73e,0x8119850ac0047c909ee7,0xf34d81aa0945420e7305,0x9fa9c0b2eb0074a983fb,0xe4fd4ea60240cea002bc,0xc38b4326c05805950015,0x7aa0dd170f10010071c9,0x212270fae910ac0aa9b6,0x805d4f0fd3d1914aecc8,0x8d0a0057ca6b87001e1d,0x201c6b000089fe248c02,0xcbfe0723a0565180e9a0,0x21fb5e4c0d03408081aa,0x6e7ed656300a48077505,0xdb1fcb6b027c50101035,0xfe9fe2b1a04032c74bfb,0x2dbff96c6339780cc41a,0xf90188a140faa544b0e5,0x6d4838a0c04001726987,0xec1d52ab48005a837f9b,0x32e7408e29608031aa2f,0x59bdc1919c509611947f,0x8b68e74e809aace7f0ca,0xc013252154573bc3c1cb,0x342b6622f2f77f424f38,0x31e31d4b3aadff474867,0xd09a5255b0055b3f218e,0xd94c55167e9f80d8cb38,0x82757057c7f97140ca1a,0xbffc093fd6c934138c7,0x9f665ffd219c8432388b,0x2037ece430069691d488,0xd500affd790c7168f501,0xd1745cb62c4458110d1,0x64f13f559a7169d4f6d5,0xbb24f639b59a72aa99ea,0xf8388ea597201a63c31a,0x1e2ce89cd78251e285ff,0x182b020a97df4bced0ad,0xd6c73e8c61e1c693a327,0x5fad03bde82ebbdfc83a,0xfe2f09bda83550000007,0x397f5516540000d3f006,0x3ffe004ba3823d56ff5e,0x4b4868d5700000000006,0x8fe00012dfd84e8c3,0x22a8d5fb26d4a090a6c4,0x509b1002fe00000002dd,0xe71a4551abea75282,0x30bfe679001bf80000,0x210dc449ea848006ebc0,0xacfecd18000047ff708f,0xd708ff6ca423f61c9a37,0xed82a07150e47725e527,0xc939d6a240c20e59d9d8,0x6a208ef1451baf147a70,0xf472b1ad7618a82c77ab,0x4226fce7840924412831,0x8f05dddba628477778e3,0x8112932b5e5f88659a0a,0xce844be670839312423d,0x58d110a5e9fd23a46e22,0xf37b1f2242954782f6c5,0x754ce119a590eec528e0,0xf07102218dbf5a788906,0x9c489d222c226216ce14,0xdf8786914783dbe18704,0x211ef251a8f045d10521,0x39eca5137204231b4c85,0xfd44b4420eff507049c4,0x49b8e12a3f44985b3911,0x869767618748bb088c78,0x6ad2ec824340529534dd,0x81a664bff645a3030d04,0xe1423d5b5115b1ca76e1,0xc388a77b2709a3f64f2,0x21629b6f325df43d4c3b,0xa560f081c9c701731435,0x2e43711a8e08599cd108,0x7d374a28ec71b14e081e,0xc18040b94040fd349262,0xca8b138e9708c2bcfa30,0x80898945] j)) else (if j<1339 then (page #[0x70fbbad570b1b91e6e39,0x983ff9212cc479f7470,0x938eb78a0c987cfe5331,0x8ba217c4647623f7d401,0x8b2c46a421f785404203,0x5fe182a5f9b0c2b9c183,0x4c8a13a4bd0e65225fd2,0x63f2283e7bd52784765f,0x714662684246279bda27,0x15b00d8ec3ffd04cf060,0xfc56e739101bf514d8d0,0xa0307f301a713947fcf5,0x8e282369bdffcd663070,0x48bbbf49a188a51bfef8,0x11c20e08c6f5e181024c,0x4b55fcbbb6219877fe05,0x649943094ac704d94309,0x44848676bc3489090d76,0xfdc3a0242390d3bb5e1a,0x9532c8d2b377ae14251f,0xd07314dc6121e34777b3,0x7ee882e0c0e2f1dbd881,0x88c5285fc6284c44e97d,0x9b1ce5c181c533e00d89,0x790611c713f63f04ec4c,0xd20e146d0848c4f5e0f1,0x2215249ad6786522b613,0x6a40193f882518877dc9,0x1455787b213a4d3b855e,0xa41130d0f98f0d18071b,0x72e044f42d622b3309fb,0x8a10cf93c34717cda514,0x1510bccca241c28bcd6c,0x56c81858beaf4965209a,0x49445fe459c142661788,0xa3f860e5fc57448285e3,0xd0cf0107939ea6786119,0x6a84dc687f5227a6932b,0x2659b4636e991cd910bd,0xc86ad49c46af95160f17,0x536c1501d1062c29c306,0xaf48d2d9447e3b290662,0xadc08838f136c85e687b,0xa07912969ae7d6e38dc4,0xfbf603604820a538dc3e,0xcc932e32f3d1a5d90b85,0x5465dbe06c090405a60f,0x72cd929e49c384ed33d3,0x9e87817abb382278fda6,0xb8c008affcc19e794a7d,0xf9300a2658387e0e7551,0x627b1933fae244107894,0x86141e12224b10b9edf8,0xd8650bf4f6e121f64596,0xe210efa8a8151f65c0f0,0x162a3b24a10a5a302966,0x6521ded10e4d5f43bd8e,0x4ffe6a3a9e4110e6fe7e,0xd89592b86decf7cc108c,0x1e808839796b83211983,0x40441ebc1ec42349821f,0x64211c2f72a780074d8f,0x4b471cfdf38028b2e140,0x2a962f164aa2154b79a4,0x9c49237c451c5e2c9544,0x142fdbb884522ef0a138,0xae25cb314b2e5fcd9646,0x107d1c4c7bd8820e57bc,0x462987ca4a461727b603,0x63d870586fbc67f281a2,0xb350b218acfe5829b08,0x16ce32bf568b64258fff,0xa9e1f02a4f1fc42588a5,0xd4e50002ea561e823962,0x163ce398dd9f8860c78,0x5e2f87d439cf1eee038c,0x2eb09667895aeaa3eb10,0x71f11ee8713c62393c6f,0x692293bebc846e1f7832,0xff92c41662b17af5b472,0x245b48d7e213c89ca5a5,0x7a63c736fc93b48db7ec,0xaffe2aa01d9a918c91e0,0xf1047e08008f9c6a4630,0x149f2436270c97f24361,0xe04ac62dea6179d0c6a1,0x8f34e7d4389795719646,0x1a6c5efbf3c5402c1e31,0xc3727db89a7426798c5a,0x9fee17dad1288b474e9b,0x462164ffeb1543401466,0xc4cbb53563a1a5e54adb,0x18716251b1f87d6465e3,0xf5a015584a29fd7d1fbc,0x89e7fe14629518a6fb85,0xbf8387ac70453e91400f,0x405944c8571f50f164e1,0x6a44237e14e6640fc71e,0x762120d8fc29666961ea,0x918922838c123139cdc,0xf371c3030e08e59141c6,0x1e9c46a388e23d010b93,0xc3588c21] j) else (page #[0x3070389676281780e971,0x209318dcc9b3a611e7c8,0xfe87908e174b03ebde70,0x56834ba503f2ae316188,0x838929ed554b4d64ab2f,0xb2c7f9ff5269bd5583c6,0x16a74a93fd362920a595,0xfccaccee2d6a966f0da7,0xd4586376fba889eb8729,0x31f1150eeb6f76123788,0x1085953b4d1657dc6308,0x91104a5e796f66138fee,0xbe1cfec4ef9d87c343f1,0x4ef9a88db9d8573d152d,0x677e69f534dadbe1cfec,0x2038b63fa822b0e214b,0xdfa1ea1101a545c07bd4,0xb07940000022bc368f2a,0x47eff4358e00000055fb,0x19359f371847800001,0x26fd4f51b58c2bc00] j)))))
def moH11 (j : Nat) : Nat := (if j<103 then (page #[0x123100210001000100,0x320131000c21101004,0x11030010013302000510,0x3104517172001202230,0x810011081501011510,0xe705900001140a202300,0x23300842450433001019,0x738000041c073040311,0xd2000000040d70000000,0xd260ab477013c84e51,0x882024f03080002,0,70338478080,6467060448,0x5483ec0000000c0b8000,0x5bc04c0475179800042,0x325800000000000102f5,0,0x8318000000000,0x79800081b191740000,0xbc0300a000001e8000,39680,0x400060af000000000000,0x760002092a086000052a,0x1c3e28458000e0,0x13f00013cb00000,0x8400000000000801e000,0x293960c49e,0x292280000001818d0690,0x1824000000000000000,0x40d70ad9668c27b00,0x425600010048,0xad02f474e207d01ac000,0xe60002065000000,0x105ce630000000000000,0x8a000000000008104000,0x209d002e00,0x520480a80000,0x11b8400000000000000,0,0x12ac6e0e00000000,0xa0000000000000000000,0x123e11901400002120c1,0x12a008e7816f803821d6,0x28000000000000000029,0x2f9c193b0b4000000041,0x120ac804c11b80d00002,0x8000000066680000000,0x32550023d1,0x20108000000000000000,0x5d034400008e2909a000,0x1342c000006aa5,4306501632,0,0x1001c000000000,0x20790000000000033310,0x6e241800000000000000,0x420000000009c00009e,0xc22000000000,0x93a8000000008c2000,95644881664,0xc0000000000000000000,71,0x4070000207e000000,0,0x104a00000043806a000,0x3e0000000346b000000,0x4000443241e023dc0000,0xea00000000000095a826,0x9f402600032a22f05c5,0xc9410414000000022542,0x6ee50ea243,0x843c000000000,0xd64560e551d9814f69d8,0x5c00000000000000183d,0x101dc0006039c1,0x40000000000000000000,0x3439000049cb807,0xe3ac83e243966b807500,0xc000000050e7846a207c,0xb600000006a7b0001836,0x1030089210d84,0x61e07a000000000000,1941504,0x4b740ce0001074483800,0xeb2000000000000,0xb7328d00c8145825ea45,0x84b4000408140,0x208e4040817734fa04d0,0x14000000000008178000,0x86100000455800041,0x761e0000000000000000,0x60000000049130000bb1,0xd800000002008800001,0x60e0000000000005,0x740000000000001b4000,0x181ca43600005a,0x705380000000000277f8,0xa0000209ee7c811f038,0xf07c0e29b80000000000,0x435c0fe097a00000004,0x181380004c91804882e,0x3c614300] j) else (if j<206 then (page #[0x80db09b8000000000030,1,0x6ce4b198a892e341a800,0x308732b418ae093e4,0x20000000382ea41b0000,33571520,0xb4580000000000000000,0x60000000213b8cd94a7e,0x1d230a0001a3c0000604,0x20860000415501f21,442,50487296,0x308bec8d40a200000,0x2001c08b40cc,0x93627a00000000000000,0x144a8000915e00014,0,0xb000000000001072000,0xbaf40000000000000020,0x39f86d48dd19a4,0x958000d0500000000000,0x12ee95c0000000000034,0x826190e0000290b0001,0,0,0x107400000000000,0x83000000000000000000,0xa40006126d15000030,0,0x182a3486800,0x816c01a00,0x610b0000,0x43800000012be6081800,0x486d824800026,0xc66de0000,20480,0x80010756064000000000,0xb000000022030000d266,1034,0x202d0000000000000,0x102fc00000000000,0xbec1eb82c4024000,0x100e022b000000000,0x10c20000000206f0276,0x23841051fa83d837a52b,0x26e9000000020,0x81520002098e281c22c,1304576,0,0x24b012cd100000,0x6a0000c0c20000000000,0x380000000000000,0x199ac0006e5d0000,0x40cd19b80000000000,0x91f600000,0x8258000000000000000,0x3680000001b9b4000000,0x287f0001005e9,0x30000000000070d90000,0x6a000000000001a41e6e,0x1e00018be36,0x50000000014000000000,1032,0x84b80000000000000000,0x84230000207c00000001,0x7faccf0000000000042b,0x1495290a109c28000010,0x1a2a000000000000001,0x2f808e015a84e4077800,0x9080000001c1db0,0x590c00004746e721066,0x214200003ce0000000,0,0x40e60000,0x5d000080b00000000711,7790243504,0x1e00000952,0x24a63700000000000401,0x5400032abc19dbae20,0x264580000001,0x1041000000000203f000,0xa2cb33380000001b4660,0x9000000000000000812c,0x41110000028221a012,0x2d547f0000000000000,0x50000000000000004867,0x84000000000000000410,0x760000000000020,0x103680000000,0x40fe0000000000,0x1784a06291ed03e40,0x3121889d802c80005a22,0x5a000000000000026c08,48,0,0x19046481800,0x83b90560860413800000,0x3b00000001,0x6040c80000013c000000,16,0x5808000006380009d68,0x25000098760000000000,141440] j) else (page #[0x405a9b7c27360600,0xd6689e0f180560000475,0xe020000000011ed9f1ca,0xe9ca000000001021,0x200000000a3e8000,0,0x8542000000000000,0xcc0000000000092cc09e,0x30348000006582,0,0xf0000000000000000000,0x215820211ee46a00018a,0xc2680002846c6364,0x282f000000000000000,0x88b08b516d8c55c1c600,12,0xbc000000000000000000,0x419000018,0x367e1c62000104e80000,0x8220000,0x4ef7411800,0xc27d046400040d30,0x88000000041d700c647e,0xdda000104f0000000090,0x20d9c12e000000004e48,0,0x2089506800,0xdf0000000249680000,0x50000000000000000000,0x28800000000000894a81,0x41140000835437569158,13,0xf2000002a8000000000,0x18e800020de4,0x243a000000000000000,0x1a2b2482c409803600,0x89c46706640b20,0x45065a412000080f5082,0x14b84d4257a4ae000002,0x4974000000004208,0x4000000040ae0000000,0xe910d40005246000105,4,0x362e000000000000000,0x4298000000,0xc85e000000044050,0x6962000000000000000,0x242d0000807784,0x80000000812c00040280,26818092,0xc600000002033591800,0x1a19800600005,268451840,0x7e00000000000000000,0x606c8131150e25600008,0x304a800080a4033c000,0x4400000000000000000,0xd185240000209900008,0,0x10508000000000,0x80e800041150,0x2053000021b80000000,0,0x80000000000000000000,0x6000042f20000000334b,179,0,59457536,0x4041000000,0x8266000000000000,0x170512665405e3452959,0x1c4000000040fac10e83,0x54f4000000000008,0x13d80dc041e09b,0x1d16c000400b000000,8859813456,0x609340f6000020e,0x1108c0000000000000,4427612160,0x4c5e00000000000,8507904,0x40058bc605180000,12944,0x6e000000fc012000000,0xc0060000000000000000,9333,0x31500000010800,0x80600000000011b0,273186926] j)))
def moD12 (j : Nat) : Nat := (if j<309 then (if j<103 then (page #[0x64c10648106081054810,0x644206042054c2065c10,0x64430604306602064c20,0x4c9104c1104811065830,0x60910601105491054110,0x24d2064d106491060d10,0x505204c5204c12026120,0x5cd205c12054d2050d20,0x6112060520601205d120,0x661206512064d2064520,0x50560645306053024530,0x5c5605c1605916050960,0xcffbffbbfb7f9ff5cd60,0xfddfbdf7defddfdbfd7f,0xffaff7ff7eeffdffdfed,0xffcffbffaff7ff6feffb,0x94012c980a6480fffffe,0x3054c90206a402b2e021,0x4ccb027654143280a59,0x94d28406a41233009597,0x2c98a568c44b4a1a9a80,0xc89406a462330301a915,0x11806a4a2b2e51996296,0x9ec64cdb2a46e15134cd,0x602a530152881a93c054,0x269970352a00a9500d4a,0x54d9b2a4cd131642d3ae,0xa5d4328d80a9698cc334,0x1e7ae6f3d717aca13c02,0x10352f95977debabcf5d,0x153481a98c054c406a6,0xb09681a9b22b25602a6b,0x2605d82000d4e0565ef8,0xa0b59305ad480368c06b,0x135a509ad482368c16b2,0x8da115acc0ad69436b50,0xda319ac98cd6a451b502,0xa521ad40ed54c76b5230,0x9286d114d648a6b424b5,0x372a81b94c0d6b505b5a,0x72c19b9600dcaa66dd52,0x2ca9b964cd6b266e5853,0xd29b968cdcb306b59837,0x89d96a0d1b506e5a5346,0x9cd660ecb00755533aa9,0x2d6a4f1b4a7b5953c6d2,0xd6a511b528b59346ec12,0x65536b269b4a94dac9a4,0x4d56b52a35a94c6d4a6d,0x156b46ab59855acaaad6,0x66b4ab35a259acc2cd6a,0x6b30bb5955da4aaed6a1,0xb42c0da85c6d2ae36857,0x4ace4986724ab2368d81,0x2cd53167254b392a19c9,0xce58066aa9b375499caa,0xe595672c8b396099cb02,0x5a2672d0b3966196b30c,0x9469a54b596a19cb4ace,0x46dad4b43695acb40d35,0x6dacc36d655b9b28dcd8,0x1acc38d655c9b08e0da7,0x2a0bcd6a5d6952e8da57,0xb8bd9551ecaa6f65517b,0xc3d964decb08f41737a0,0xbf061df82e8fe59879ac,0xd66201b52fc1977dac9,0xe6622195310da2846d44,0x6a636b2b1b5a9886d4c4,0x6246b272349891a49c83,0x256b2f2b59595a4c4ad6,0x76b433b4a39dacc4cd66,0x6b3143595a1ac950d692,0xb5348da8a06d2d0368a8,0x855b598a9acad4d64aa6,0x374963ba4b2d9258eb9a,0x7c187be4b2df258ef82e,0xe953074d180369706b31,0x9a8174d08ba6941d3460,0xa22b4a915a68c6d2a636,0x5374cc1ba64cdd2a66e9,0x3b4c09da548ed3506e9a,0xf4c29fa694ed33076982,0x4c121a6a4fd34a7e9953,0xc9a3a60d1d3448699343,0x8a5a6a51d3468e9a0474,0x25a64d2d2a6969524b49,0x7a64d3d2a69e8a94f4d1,0xa68d3d3429e9a04f4caa,0x60d5d352a69a94f4d2a7,0x8d5d330ae995574c9aba,0x96d330b69a8574d2aba6,0x7d32abe9a85b4d2ada68,0xd2a6ce95267498b3a661,0x330ce995674c133a6059,0x4ad68956b4d2b3a6859d,0xad69946b4aa35a2a5ad1,0xde9a96b4d2b5a681ad32,0xe9956f4c3b7a5cdbd2a6,0x8a9774cc39a655cd330d,0xa1774d03ba651dd2e8ee,0x47f4cc3da54ded352ee9,0xd308fe95] j) else (if j<206 then (page #[0x2630e998834cc3fa64df,0x27169a2874d0c3a60a1d,0x1169988b4c9c5a54e2d1,0x1e9878f4d4c5a68e2d34,0x6998934c9c9a54e4d331,0x8a59744c4ba6a24d3472,0x97974cacba61e5d1512e,0x7974d2cba6865d3312e9,0x9f451cfa6626d3512e9a,0x744953a6927d3473e9a1,0x4d053a64a9d2a54e8a9a,0x5455a296ad145569a9a7,0x155a662ad32b56992ab4,0xd9a5cebd351569a5ab4d,0x1a6970d3097e942bf4c3,0x3880284011000034d4e,0x8d407d006e805a40494,0xe3c0d540c6c0b180a30,0x13681244117c10440f30,0x18a817e816b015881460,0x1dcc1ce41c501b501a1c,0x22242160208c1f6c1e7c,0x27c8262424e023a422e0,0x2cd42bb02aa029782864,0x354433a4321c2fb02de4,0x3c603b28399c386036bc,0x438c429c40ac3f643dc0,0x4a2848e04790469c44d8,0x50684edc4df84cec4ba4,0x561c54cc53c8529051a8,0x5c545ac859a858945780,0x628c616c60345eb85da4,0x690867b86684655c63e0,0x6ff06e2c6d706c146a68,0x7510746c73b072b87154,0x791c7878777876bc75f0,0x803c7e647cbc7abc79f0,0x86dc85b4843482a48160,0x8c588b608a50894087d8,0x92009104901c8ed08d84,0x96249564949893f49338,0x9ab899d098e497e096f8,0xa0b49f009db89cec9ba4,0xa7b8a670a50ca364a25c,0xadf8acc4abb0a9e0a8f8,0xb5d8b430b2b8b0f4af90,0xbbd8babcb95cb804b6e4,0xc2c4c0f0bf94be40bd20,0xc954c7ecc65cc4f0c3d8,0xd180cffcce6cccfccb40,0xda30d7a4d5e8d49cd32c,0xe388e184dffcddbcdc04,0xeb6cea40e8d4e790e5f4,0xf334f22cf070eed0ed20,0xf8e4f7d8f700f628f48c,0xff68fe70fd78fba8f9fc,0x5dd041502f501dd00a0,0xddd0c010a71090d0799,0x145d130d11d510a90f55,0x1ac919b1188d16e11595,0x26f5241d21291e5d1d0d,0x31dd2f9d2dd92b452959,0x378536a135b534a932cd,0x3db93cd93b5d3a4d3881,0x43e942e541a9408d3f85,0x4bc54a51496947cd4601,0x533d514950654ef54da5,0x5abd59b9581956355481,0x630561255ef95d015bfd,0x694167b56641655d6451,0x70b96f496ded6c256a91,0x76197505742972b971e9,0x7b0579f178fd78217731,0x7f417e857d897cad7be5,0x88d9874185258369811d,0x8df98cf18be18ae189d5,0x939d92b1916d8fb98ee9,0x9b4d991196c595b194b1,0xa3a9a24da1019f919df5,0xab3da9dda825a64da489,0xb4adb259b0a9ae91acc1,0xbd5dbaddb89db77db62d,0xc3f1c23dc0ddbf91bead,0xcac1c7c5c6edc635c561,0xd0bdcfadce9dcd6dcc45,0xd6b9d475d395d2b5d1cd,0xdaf5d9d9d961d899d7a9,0xdfeddf21de01dc9ddbe5,0xe5e5e489e36de23de101,0xed21ec11eb11e949e77d,0xf2f1f211f0e5efbdee3d,0xfd8dfa61f7b1f4c5f3d9,0x2f03701f002028a0041,0x781a06180d80b00403b,0x284008c06686b0570460,0x8a704e09287282705381,0x182904904604a87605a,0x30b206e0db0260b410a1,0x605409f0c205105382,0x580e105405f042809081,0xa0800a21050930cf03d0,0x6109407c8280f80dc07,336783403] j) else (page #[0x983211280e0e80d40870,0x8a81e1141a00aa12b00,0x168ba9520ae81709a8fd,0x30d10148148080ec1e98,0xe50628302469329240f,0xfb0331411228c913d030,0xc1c613612295d8698741,0x82e0960441d50ac1701e,0x6818698c87097e9ba966,0x31602d209a98819480c1,0x11a93898d93992590c85,0x9a08906c23ea581e40f4,0x403c0aca871bf1450cd0,0x6c0bea008a49898b801,0xc17998d1a81a524d0ab,0xa882ac22516f15581b0,0x11c87714d9301581282b,0xb282100d2ed20a15a174,0x43718209c221a13ea119,0x2341481fc26cb8e8c71f,0xbd0db2071921921620d2,0xc11020c240180af22a03,0x81e9b090e0c4406a7995,0x4805a0a91930c41cb088,0x13b201526219c0900800,0x8429b690eb403d1824b5,0xc70c9a7d87181d128324,0x800c02822a2fe30b0ad0,0x9d89642198fc93123800,0x3c31029436831f21439e,0xc320be83988561a88b90,0x96511115847aa7c2b697,0x7e3372302cd00329d8a5,0x89b00301c128c2918119,0xa72a76a702502381a89b,0x442a914515704b058364,0x19cc3a40d80b4afa1561,0x21c120b55008a6609e03,0x58cb223846ab30af6af4,0xdadd9b630046c4f8c44a,0x28a80ae4804a5cbee03,0xdc2988c523121514d223,0x9708a109c1991c03761,0x2ea16d2e11be33b1050d,0x1b84438300430588c36,0x724b2c49242bab880213,0x16d1603a03945870e82d,0x284621d53dc11413419f,0x50202544f431602934ca,0xb40cada104544e495c23,0xd85a921902ab0cb84b45,0x6c1e3f8830402a5da019,0x1432c89523490ca2e230,0xd93072c132d2490c0391,0x822c5490a04144e8d3eb,0x1ad2a04f12ea260470a6,0xcc4d0ca4d3833d1702bc,0xa35a2ceba919d12d9883,0x4bc4d917510111513640,0x5866401806c688d31488,0xc6d4594591dec9b413c5,0x9da034c1eb8035db8335,0xb52926021f600229e0b0,0x142d4c93cb1746685bf0,0xa8841223e3101741dc05,0x1af9c94268c9824c062,0x71036c4e096d0edb881,0xb305ae196528bb53e436,0x247087050186ee50c824,0xcbf46ac5b0e2c408ca0e,0x4ec8206c44506c0e1882,0xa470c465c99a89af04c4,0xc2fc352beea82ae41d05,0x60e28c8fca00adc30428,0x5a43137d29c6103f2adc,0x92c10b12c53d4636c803,0xc80a78a053352c93ad32,0x2c6953396483b91f4334,0x594f3282203f8e285bb3,0x2812e525c3184dc58f09,0xac44d48c58122926a2a9,0x870040cdd83783c84fd2,0x458e22a0684d84301a81,0x1d9b9b468120ed5d53e0,0xab908c8ed8951eccce2,0x3f1951c853585790b617,0xf2390c3d3b8e1d644e16,0xd21eb45a71a76440ca93,0xb44cc0daa3b85b53f92f,0x418104b12aadb942bc0a,0x7759843489ffec900446,0xea0dd04caaa7ab728479,0x28479156899983501f7f,0xff8006401cf15622d4b7,0x19a4838070359d0769b3,0x156235567f20e01ddace,0xcd19a50fbdf8180001cf,0xbb884aa000e01dda,0xeed668cd287f0ecfe0b,0x1c03bb59a33480070,0x2a7aa023fef0c2c15e6d,0x301531d4bdffde204060,85046304] j))) else (if j<515 then (if j<412 then (page #[0xc2448b42ebf16170cf7e,0xe8f187c60cd30be2b9d8,0x39c8968d62ad8019a6b7,0x94e7225a538a678b9b65,0xe3023a018d0e299e2e6d,0xab13654a324aa5960266,0x15c0000d2b9d55a8c941,0x58099b8c08faac687140,0x209d8ee7405d314cb29e,0x1ffc3458004fb41f74c2,0x200010d0f7ff84613050,0x58008800042112cffed2,0x99d5c9fc90020b0ceffc,0xbf304040a407f6580021,0x10854b6346f002199c7,0xf89ea4effd0230e1c00,0x8016470007fea8189124,0x6bf966d10022141f04a,0xc901200e4427da741a65,0xabe4809003489a7fbbf8,0xf57c80801000e209f8b8,0x29d3f0bb8329005a245f,0xc7d4e400ac3b9200d638,0xac0076acd06b47ab9018,0x19f7351000525c00c7fe,0xfe58006c0034506800a0,0x5cd68d948c0471aefc12,0x22fa8001c7a3c0097f9b,0x41460006d1f80dad035a,0xaaffa301a2e39ea22e80,0xf82dc3805d7367a01251,0x451c051c80212a40cfe9,0x827cf44e201311b17e43,0x41220004a917f46037d8,0xa4ad2681eaacf23ead14,0x59a002dc00008ed69781,0xc5e007f47fdf62827f2b,0x22c37fce5a0490221f0b,0xf9a6e63a922d825e90db,0xa1f8869118dcffc00503,0xef06b72f97a4ed17733d,0x9f0fe0ddfcb508e26396,0x862d58c00000000010fd,0x243e8854d6ab0515d640,0x5ad04b19ea881333a666,0x182119258c92065e0ec3,0x9604d50bfff06d900593,0x6660d577ea41b2592dc0,0x7b59d70696e50ef255a2,0x6000073c5590d5855a00,0x32fac27a923fca6e160,0xeeb356694bfe6a3e0b,0x5c1c810180a8e2a40236,0x15ffe20600a95a723fd,0xf8bf815cc5e602bcd114,0xc3cc4f39b4e7632d19a,0x5cc001400e591caa1d83,0x89839804a024f7239d44,0x5bacc60cd3239f73b184,0x5cee2f4cad628e38849a,0x8127a655046c24d14d53,0xc678b9a676b12d124489,0x5f0091ef1f24d0429618,0xa4219b51602983b54bbc,0xf7fbd9baa3c25a6551f7,0xfc33f56e234101432516,0x6cd174023e9098d1a31d,0xf689ec50aed4d50ef37e,0xcdc604742ab1aa4535cc,0xc4cecd46c5ca1978aa64,0xe50004600002058ce7f0,0xe084600002578e0029ff,0x113c6019e2f800afff,0x810a61ffda0128c2130,0x1084000040d1e7a7fa3,0x926a80ef07c0002bffe,0x25565fff48c980088000,0xbd3fff00c81c11000010,0x810a475ebf016002104,0x4b0fbaa0408537ff854,0x8580085126ff724e5408,0x2254cbffc2a040a52bfc,0xdd50225295ff84aa9600,0x81526fff672a040a547,0x2441400101522bfc8580,0xb8fe5ff0757071598c54,0x94654600b04800004095,0x4e409800010247b1ffa7,0x420d8017f578be0173fe,0x8422fbf90c150b8000,0x105d633e5f750ce3800,0x5f9f42166fa8b3831000,0xf1bc6ac5203100001515,0xf6ffd70038001044485f,0xaab02ff295f20042ed32,0xb0f8bf5198c862000020,0x99a83f0c3e998000809a,0xa0131be70d07d04008,0x3bb00008ea892becb1e4,0xa92200010445c1ece972,0x84900008862f9b7fee81,0xfccc00402942f4dffddc,0xbb50f1e] j) else (page #[0x842a73f0507e7001,0xe15020429dbf5ba1e70e,0x241493eea810214dff,0x955bff0a8108152ff216,0xf9002104abfbf9ca8100,0xda9c30000841a87707b,0x41294dbbf3e80103a5d7,0xa6fc831871dc1efe4008,0x80029391403a54839f69,0x920e5c39405ccfb7e6fd,0x90ffa46d426756f0071a,0xc0daa03a949d0802f2b,0x6a2704a80264775f5b07,0xc1f118ecfe0b321b541b,0x5459004956fee9648ce3,0xb5427e6408aa506d50a,0xa7ef85fd018d88120401,0xaabd1cef53d9611e01a2,0x857f77370c8070900478,0x4000a42d9728b7440158,0xf003811a024c19299012,0xe61c202c16af42a5ae5f,0xef7ffbb30ae924a032c4,0xa20644611044141002d8,0x59512121060125bb1fff,0x7e22800c00a5737eabff,0x3aab036e7604180000d,0xb6eea6f7e8680aa11030,0x81d512221d1004880096,0xfe3f7b8a428394ba3fe0,0xa7feb404af42d01b352d,0xdfffeb66248000c001b6,0xfe022b201c0020093161,0xf01fef6858140aed76ff,0xc3cff605de810a0466c6,0x91ffa844ec92500d6243,0xdfed5420474440c00d6a,0x30f37eed1f304c003d57,0xdea436451d6602b2bc00,0xa49012d400065c04b020,0x28654c0356b33ff36088,0x6ac09f29000e2c3b778b,0xf202280691b6f37faa48,0x8105180d71f39b862f67,0x3c84a8c04e1939f9ddcc,0xb8fec1d1a81077908c07,0xb488010034eb808fff21,0xe6ddd7fb6089a3d1922,0x591f5fd408344ddfee4a,0xf168bd42335326e400e7,0xc834c05d57200c91a051,0xd28a3880216b40016bfe,0x10f1857e219fa100086,0xf5201757fe04f0ccea72,0xaecbf9564aa1c14a800a,0x134fd24ec505d520039,0x403dd937812b4c00079c,0x3e1f4410d800345031cc,0x59f8a80a01f2bc00ff32,0x3c780075fc013168a87,0x380d83fbd622dfd0a80,0x61a067f880025290f0,0xa037f83df2fe590006e1,0xbe2f35a36710504408d1,0x5b34680d044042c8e3f9,0x159647fcbd9f27d1ad03,0xa2818c0028067dcd4400,0x574783ffffc0a8ac001,0x8e56414e8e7564c0008,0x3c187ec430240301e62c,0x5ec8213875134a05cc6c,0x8fff51d1b4008e2516c,0xd681ad1179020009204c,0xc4708022ab446c527c06,0x4a38000afd38877b8301,0x8c527c06d69d65117403,0x258a2268470802d6b9de,0xae11c5354ed7fd1cb690,0xe181f8d55145a58197f,0x115201812f1d4ffc707c,0x96a28667fddf9f4ad209,0xec5eca850b1a0dc5c40f,0xd437cfcd7820850056a4,0x6f5ba7ff7d19b24c012,0x6fc8ef644a0108b51c40,0xe36b86f58c6401e59103,0x5478019c604bffc10681,0xf8ae265e000718052fe8,0xffe2c5ce7640a0a96b25,0xffc3b527e590282a1aeb,0x594fc500d8062002b8e5,0xdc817ae5046d780404c3,0x13d073f9f59038cc0807,0x9ec400200b31f0f270,0x900b58cb7c3ecffe1008,0x27548fffc08271c80050,0xb26fbdf37e225250c401,0x34bf97236271aa8c0026,0x36c02020880296bd8f6,0x13d0956b7809624ddaf4,0x2d500b7a9f9d343da519,0xa8014d0f2fc2214644f1,0xbf6227bc] j)) else (if j<618 then (page #[0xabec44f2054b1eb7e52a,0xf7fb113c615200000097,0x6fb113c815347e000001,0x600a30289d50000002de,0x2a50312e3b4f9b8ae30,0x2cd9effffe4060253008,0xf45932be1692e808c4f8,0x98008394903d0d68acaf,0xf83cfb2929b9780ddfa2,0xf08bcf24a554000000c7,0x11ec694293727e2e6a48,0x12fcccadf271d020800,0x6519c000000001ff678,0x4097064f5f013403a8c6,9661580092,0xf220f402fbf9d0331380,0xc0016b1a45960860656b,0x231e0a2914a8000d7f,0x6778012e077cdf1,0xdf12463c144e291063fe,0x824c000005bc14e077dc,0xa4c1b930ae074bdc88c0,0x4ae06bfea063b4586002,0xade01993019b3080de8a,0x835fd19e2015d26001e7,0x1cff800227e4f1c30,0x175f5e6de908e998cd00,0x4af440a18b4600009f58,0xd47c16065b3ca813f36a,0x69a6aa17615c58153c5c,0x4f723553c5cca42e1918,0x4ea612689eba0e65202,0x2950059f812a010d6070,0xbb42d5737a655046c24d,0xaa6bbfb00ab454dcf942,0x800080b7123c0ba6156a,0x27ffdbff865b20207488,0x9125f4f2ca120614235,0x12b24ed7fe2071005005,0x7141b52ffe1ff4066604,0x808b12fc7d46a30,0x9ff628082f825800a208,0xc818c3848801022b8aff,0x8091a00057d2ff2e9,0x4957c1ffb3ecd30e41c4,0x4409963141ff2bc64273,0x857f3fff8a021bd255c,0xfe503cf9a0b14c100001,0xdb8630000104458067ce,0x94820000114d5821fddf,0x880004343a1fcbf56ce,0x490440400008109127f8,0x523162e0fedfe7ab0cd2,0xb4a395f94d87db104410,0x8fe0e8f560a686504010,0x3692531000010157c3e,0x2028d00afc5b3f5148,0x747a7fff7821a3744640,0x40d5217e005b9000086a,0x10d1117fad83c6480000,0xa001026c01f17e614000,0x63dc3e2a12760018618a,0x1e04014a8000848922be,0xb9abfffffecbf8230888,0x97e891ab332056000404,0x6d67122150b687bb75ff,0xc8b5238809af3ffc93b5,0x6679380e002298b1cab7,0x4da3f078d42500008423,0x8da08300000108567bb,0x91800008062defe061c,0x7118000805bc58b97ff9,0x100c7d7ffc7ff754ea9,0x13ff36afb7c0e81d6380,0xff80da08400004035426,0xc1c41220000212aa398f,0xb08600002018a3bf37ff,0xab7eedae01058601bd7f,0xfffa748c98418000408a,0x48b54ffec421a20149a3,0x202926aec7ffe8420321,0xa10805a6bf8cbfc206,0x35fe108e02209a23e7b6,0xa49aa397f848440404d,0x843100a4d7f1c76dca08,0x9237fac60c40a46d3ff8,0x678025c6c37ffa890404,0xea4dff780ab37afe6816,0xafca9818820040a0126b,0x4246b0490ef87ffbae90,0x7e1197f16878a23c2262,0x3b344025808b728ffff8,0x33c887ce21f49db0db,0xfcf0fb6230a0a1104483,0x37662864085c25ff9bff,0x2d9784bcf90475fc1a1e,0x6416482cb350f98f4348,0x3e78489213209a83c348,0x9e7f7e3d0d28325e12d9,0x23a6fbb593e774980ae,0x96a36c23677303ff4466,0x331971b0a3807690287,0x76e1675e] j) else (page #[0x1995a9799233004f5224,0xb1297ff8600280769a6a,0x40162350fe45aa994806,0x88050196251fe2c81c01,0xa8c83280244a43f1e54c,0xffff96dde671b8fb6a3d,0x328f724118043a4c0097,0x6fff1ff1747c6722207d,0x3eceb2667d52260390f9,0xf0c7fdca180de1ec813d,0x431e1b894014025d6f7f,0x8a08030e6ac2f37c547,0x3640126aa2fc6e1fd44e,0x6014f51780167d2306b5,0x982c87233ffe14b29c46,0x252d7808f907422fdd3,0xab216ff88182ff103b06,0xc03111f8e20862f20181,0x1d3c49806004c853ff06,0xc016b196b7e6b79e8cef,0x80de8fccbb169e29956,0x33f3b2c2c3edfab670d0,0xff550608b01b52503ea4,0xa292108582c59e2e0360,0x2fff751c972450044200,0x1b6ccd9328ef80298f03,0xacc0e00ce9466cff2097,0xf9304a6b046ba282ee0d,0x37cfa020151198fffbb,0x4aa014f1154ff2b4dfcc,0x819c54d510fe4fd537af,0x4688601d72696065fe02,0x5fc9fd43e0aaa06700c6,0x85442321100072caffff,0xff678741c02269e2121d,0x6e2081c4400c516077ff,0x7ebc437056ce930ffd91,0x7fa888ac89e1120012ab,0xdc26f4a5c90890041569,0x144524208600055b77c,0xa48a3856a9afffb1a715,0xac0f5a20f81d2fe99998,0xd01fecb58163327d1745,0x5300f94e87cba2a2607c,0x810e2e52a862204cd4a,0x40037fffe08ea372f2ae,0x6cff4c0f211842402963,0x36f4c44908604b457bf4,0xff8fb0da2400908112ef,0x5177e33068550843150e,0x4315177e3306dc004431,0xc2a02d0f77e330685508,0x9e1d203681153315671f,0x43d9f1f794aa5016535,0x9024ec0455ba3348030,0x6e50c7469026fa943920,0xbfddaa1b68aaa7af8c96,0x43f0a0e74f7f8327c489,0x3427ff64cf7e20c746af,0x99a33e6ec815b09101e,0xee318400011211999ee9,0xf20b433018e249ff1436,0x135f9567010599e9f407,0x9caa6dfc5339d622242d,0x11d91b7f4a379d842062,0x21478fa3b06bfcae1432,0x864210c90003568bf143,0x5710c714e6a000462de2,0xdeffeaef74840b006032,0x3d64b20831464861c475,0x914c258e328fc3e27837,0xae9f5f1019ff01336aec,0xc91c129dafb3f8c14605,0x3028642cf1ccffe22128,0xb79c2009121184bacfbc,0xbc850c0d9cffffa6a361,0xeef124283636be178db7,0xeb3f1112a61cbf801947,0xe87360ffdf384e9a1c5e,0x4081924e1bfcb6128231,0xb106c4a9314c37c1ca31,0x640097ff66a0073eba15,0x8d589be1a989de0aead2,0x31ffe12fa3d085479,0x2d21b426b45111bda7c0,0xff941fb53318d473b36b,0x208e0f3200000000000f,0x2f3485a80a06a4cc685b,0x822ce5ffec474fe66350,0x68a00cf6e84a19b46080,0xc1846caf012fee000c3f,0xf7bdd528e4200c611ae7,91] j))))
def moH12 (j : Nat) : Nat := (if j<206 then (if j<103 then (page #[0x4c16054000080408805,0x82200802004010b827,0x3007040000680006000,0x600003c2400c0f0d018,0xc2e078010000c00000,0x1c01004520140601c02,0x1d4000780201000,0xc16254010280f01804,0x12400124040502705400,0x342c044210080910026,0x1b048170041d00006,0x442004080100100000,0x7016018180200f00c0e,0x44020000f1282d16810,0x909802010000583b,0x2025004190080903c15,0x40902202c2400005,0x1282f750450344c0240b,0x380b004030285b07c46,0x3c6f00c0c0841700000,0x1001024070101c078ca,0x24022503a028000d00c,0x117c090008b1980c,0x2c06044010080005c02,0x8120040a01c0207003,0x40b0043706c560bc71,0x10112300000c060e867,0x500201c2a1381201967,0x888294041040012417,0x24162c8000181a07001,0x40400c410300b00002,0xb1600c0183503415,0xa011000070145b0000a,0x40000006368a00cc21,0x2c02065fa0a01908400,0x24097008010500c35c29,0x14060282400c2d,0x14450008401cd500408,0x781f358013643c00821,0xb014310210c99a17c2e,0x2c2600024020831b419,0x44230243d0ac1e1041d,0xd82803c031543d1798f,0x8040201d28cd759016,0x3c0a1240001c4e0c033,0x582a068170201a00003,0x100030400aa0064f002,0x9c63000ef0600a03827,0xbc110041c8a0e92104a,0x14022f0221f0063c805,0x128000dc1303c4849801,0xa4072442d0243f29405,0x7b003000281480906c3b,0x242b3e8280145c23c13,0xb4d908a40f1300008405,0x1371c1f09e5210710ec,0x1150065138f14588131,0x73e0a350c9e084d04f8,0x13920b53430c0a460203,0x8ff00cc000300999b03,0x299c805f0000309f0,0x90a90df097409d523a8,0x1508a3ba4455084b69b7,0x45c3092b4bdf5a1a00b7,0x5910b28096bb7230dd8,0xc306bf05b40c8b8c8b,0x38201e7088a14630ab9,0xdd4166b256324f4ba89,0x50808180a6b020807d8,0x8ddc010400030c8323cb,0x70d000000a09469e20dc,0xb9201031394000306ba,0x23dc1a5f0846037521cf,0x8300c952dba7c3c0aea,0x85e8c7443114889,0xad9f01ec202b0b0156b4,0x4be8063b09b59bd300d1,0x6788615809f673a00002,0x74e02b57c54768c7cc9,0x73037e013e0616ac2c,0x735800be466949bd09fd,0xc0000000003222546b2,0xd6e7c1246c505290a5d,0x23b52c44473a02d50786,0x5dd40002251d99d4ab67,0x6010000207a3298c0001,0x97946e205dc00010b10,0x2a120583064471340001,0xc2802b10a0108cc0000,0x2e648410d3c6d050b15,0x1c35d9b1aa37daa0982,0x2dbe221c5cac000004ac,0x7ce424b80002114503c2,0x660b01be009400000003,0x9d15900001646749c8,0x8380b3643bd034405b0,0x4142006aa63399e00003,0x7d7e04db02c279d50584,0x15c40dc9ae8,0x3da07ce0bf000010c18,0x2553afcbbcf48e62534,0x31a08f50c8f0543ab6f,0x6d60935] j) else (page #[0x45e6a80062f897c0000,0x3492a7415ceaa66094b,0xb970063f4cb5679e9cc8,0x16f4cbd033a03530817,0x1277812bbf05f80566,0x48a87bdd07b1015107ed,0x1c930653069e06604bfc,0x67f20f002f0769008c7,0x79e148ac75e1073b0a95,0x7661b21001905690a90,0x757191001a000000001,0x18a2e033f07e50063,0xc4a749b474400023bc8,0xd7500e6052d25390501,0xbae748e7d1821ab740d,0x43d20bc70d9705e1499e,0x329bd035d0d4002b9,0xd47a40c019446aa0798,0x891ba6609970dcd6a70,0x74680c1c000204590158,0x2349a061a0dc70d83,0x510050d0998676907d4,0xa850bdf0003034d066e,0x3119ab4d73bbcbaba,0x342088f16a000000bc0,0x811015700fd04d20c61,0xbbe00cb06410578,0x201ac000207590128,0x7600003067928167d48,0x14ee06811883736c21b5,0x102ee464b4c6c048d,0x64c7b9c000302a702dc,0x2c800014c9806fc0570,0x65bc091d0462203c6a76,0xbbbd171661800c852ab1,0x29d00002075d0d4a00e9,0x76762b5a2a5f079203ca,0x35bf80001043903f7,0x8ef03a843276d7d0778,0x43e31431003d05b80d5d,0x31b1000030c6e0574,0x116a40002080009bc,0x4e143d800000003b860,0x46e70bd94d090c540ab5,0xac1799d30440024c94cd,0xb21091802fc09df043c,0xb559a3f10a9db4d02514,0x2772964036f16f84749,0x980001330bea3bba7611,0xcd90c7a7beb049530ee,0x313a55450b1d0270488c,0x134b11864c1a08250768,0x85105abbabf45b506e8,0x7f1039d46c805fc9519,0xde200a1051e483d,0x72d49016c82643543cc,0xa49695500fb09914c13,0x37323ad090701d60045,0x115442a7d24fd04dc,0xce678df49e413854838,0xcb909242b3509521718,0x2976a2d056000000001,0xa1f0c726b112b30bb84,0x147e01b234b1634b79cb,0x10ac000030ccf0747,0x20391bf4000207e30abc,0xa96501b40b5967734c63,0x1f7a0000018bb00160,0x6cf7cb804a51486057c,0x47cb049c000224270881,0x30bc800022a560479,0xac0c021702230a8048b0,0x22070afe4122ab42070d,0x3828361c64310a2d23e0,0xa04a94f205f07d00000,0x4bbd9a6c04b800014743,0x46f243c643aa4c20101b,0x4c4602650d167a442a44,0x42c50420041c00013781,0xad067004cb03d10145,0x26327d465b2328b80303,0x9c665f1660e026e026b,0x879d874d07b547fe085b,0x3bc008265fd5414,0x62b06940356296c0000,0x64806d30ad002456800,0x694e667214ae26cc09ab,0xcec9b0d0d220ce001e0,0x60eb147609cf02292203,0x67900361294e2ad64915,0xbd00000032b05e70d57,0x204605540003011ba142,0x667a46eb08290400767b,0x6bf4029a00b3bb3a19c8,0xa5b09b0468805d0020c,0x48208c80000146c0900,0x4c4cbb3464c77d9c0db6,0xabfd0b4a6bb20a2845bb,0x6c8b0dbc06b305c0300b,0x30c5070d4000215d4,0x12dd20a41071f941c,0x7ada52c440403a0,910118052] j)) else (if j<309 then (page #[0x6c860cdd06c68de109fb,0x8755674c0002b4bf3186,0xd650b2c45fc0db0017e,0x47000014be72b240002,0x4d6006e04bc20283002c,0x4c0d48f82a2561346757,0x34ff0182a8b94d248ad5,0x5bd08970d9936980aa8,0x88bb05a200ef7d14477e,0x6d8fa6d0167d0da447fb,0x87b0751c07110d510c77,0x9ad4ca3207b079500d4,0x42b0aad087529d853f3,0x3639007e09ef64ef253f,0x13902f60124768000de,0x4509247997f906e708b5,0x773203079403016809db,0x6c24740490aca30c47,0x44f5096616b709d0263b,0x77f829ef112f03a4771c,0x44eac50021909600c39,0xc7c04b4913d09410078,0x167908dcba2b00a47400,0x469743ae7a0642d4baee,0x58bbb8d0bb566160dc9,0x449e0bbb025866070143,0xb887ace00d908627c51,0x541c0c0d04c67cc2183f,0xc93080f0bfe0c120445,0x6be34180019908d20c14,0xc6602626953091404ec,0x6890d1c6c90a567053a,0x6560172078399f30cd6,0x14d8db409e2852d79d1,0x14490be406f448c175d8,0x61205220cc702bd7a4b,0x20868000148da2b3c,0x3c400030b9f2a4006a4,0x3627464d02ac5c0d395d,0x19cbe01c5b4c22a39,0x2b2b6a8d0c2f0d2d07dc,0x4d2b06ab0958b8036610,0x225e74747171008d56c2,0x6300659029c4d3129e4,0x97c9afc06a323e40001,0xacb0d021a39017b0d3b,0xb65456d0af202843637,0x24b30ba7677e07eb7832,0x95eaa078b7d03e464af,0x21b040d8772867b30621,0x30a20e746fb6a890840,0x1fa736a09382b0608f1,0xbb7104360930087eab86,0x7cd5aa2d011e028c01bb,0xbb43202f0a1b73baac49,0xcada9fe02f9bdd007c5,0xd7c079c03119bf0aa01,0x3afaa412b4fd0b566a6e,0x13f4339f000f491b0c69,0xba606c6c01aa678479f2,0xb6f10cb70aa5032c1428,0xcd12db4204200750d8f,0x6ca1725431e0a727656,0x362e04a16d8565ea9c98,0x46c2b3b221004b0133c,0x970000101490599061e,0x160b4d5b083f068d967a,0xdde245376b620ed49f2,0x9bb0c9946712ba333b1,0x35b207416c337b7036a,0x1f71a2d0b99056d07fc,0x5f40dbb0da90c245a12,0x45321f30507247200f5,0x6ef0a621cfd05a708e4,0xa9905d5249e0b3b0175,0xb327a590b6208874bd0,0x673633f743b446ac23f4,0x8a9a6c023a4040a0024,0x7834082e750376952058,0x20501481066804e86776,0x8ae469320255a2dbb69,0x487bdd97cdd078b8b09,0x45cb846248b89c0d0253,0x17201bf833e2030c34ae,0x67764a77cea0234b3d1,0xf2058f02a32444bab4,0x4680a3829cb19f40835,0x217f5a0c0003089824ec,0x4fe14e001a44d3e21d9,0x4bd400010a500acd2a53,0xd070516b52e3bc21664,0x170100ba08d400036c9f,0x76dc2b9c072a092e05cb,0x549c03670b0c02794c6b,0x247c46dc1503089f4cc3,0x249b48f265ed00596764,0xaf708bf046716982af7,0x2dae7cec433b07f47c2a,0x94c20320ad9078d04d5,0x2040001713e0b79183a,0xa7f081d29e0ac3b149a,0x7c2038849b927c60b87,0x4c857c0d] j) else (if j<412 then (page #[0xb3c0c3d43dd0da3080a,0x3330956467a2b0b0b7c,0xc2208640003039921b8,0x53509c80b1b29e80cfd,0x53c0741052402434c38,0x615142f74c005a1d0cbc,0xac57d3a082305ec0391,0xa7167d1c00001d9a0bf4,0x9eb072729fa00082bc8,0x55d73740dd3148b70c4,0x4100001a55b2a23418c,0x7ce170cd134001cd0720,0x11919264145b22229,0xbcf19060b5e40e11800,0x4157acb03230ae3ab9c,0x34f42bc6367f0aed7bec,0x40ae1af1076ebc0f01fc,0x4bd0af9acf74685038f,0xbf940b66a78032703ff,0xaa510a2502cf5dd12048,0x91c10b42780302933642,0x87904a884ec165315d1,0xc092d9a734b2a700d69,0xab83ba6b21ca17e60c4f,0x22070456a548e8195d,0x4128588102d20d0f047f,0x30adf1b290ca60913,0xadb70085921687580288,0x473d03f14bd800564c49,0x1c99a2c1b26010a0805,0xd5836b4000103de0035,0x48a10b2708e32c8c099d,0x24ea4bcf041b2da8abbf,0x5a6f04cc0b0b003319b1,0xaa0a07bb197b07020600,0x7624470d67992b200635,0xa3000014d4d6c78486e,0x77be3429031401d14737,0x242302aa2a0623f8090c,0x2d960d08000000010a3c,0x2eaaa6321ea2a6d9836,0xab727d3d613345a8ba6c,0x1af4000008b000010a75,0x69305300001bc5606de,0xd700594ada800020c58,0x4a2c0000860b0bd70233,0x24a9735034e3021d541a,0xbaaf0ce90a130a4f0ca9,0x21be7464000000017cbc,0x3bc61729055934ec0c34,0x93eab7d413b098a,0x208e9878977070090,0x2afc03e32ada29cc0870,0x347a780d0b6d3c0f2468,4525786865,0x2061ba934c701a4ca844,0x308c006da03370c42,0x2a4943d7bde3010c0000,0x1a3e06ad9cec252a0112,0x3a2f0ba10bee031f8dda,0xbe0000105cf085699c6,0xd84037b06c18b1005eb,0xb8cbb74038638020b06,0x86c09a61d068db3054e,0x410802d803cc000120da,0x2c50018816ab48103a3a,0x4bc66c0d0d9146b8070a,0x226400022aeb0b4c8c0c,0x23d9b2ae0023e,0x24a4001707cb4d6b0038,0x14080003735e0a0e0d4c,0x9c13098e059d09a00003,0x316492a2f08bb8432,0x7a4204240003221b0b74,0x1027c000000000002,0x1df47c6ab68021164bc,0xad7431900e000014623,0x413423c40a1405440002,0x5b1209c304e51da70c07,0xa2308f86af1096c0002,0xd37465a06fb0d3175de,0x6250c5d675b66000002,0xab04bed0cb2004203ef,0xdaf0d9c0001860304f4,0xcc07bf00000000007bf,0xd27782000030d8b0737,0xcf0a54c0b8000030609,0xd134cd827b609230475,0x1687f688140b26d8b,0xd794124060ebbe57c04,0x2a5805ac00005a160baa,0xca10549248779c46a27,0x60e664a803d600530a65,0xbc5c004d4637019c0bb3,0xb940aa3b54c8d040001,0x8b6a03b503940cf40164,0x22e0cf81389485004f3,0x1200000000303b10d61,0xb6b23b8670cbafb4cec,0x946b04c2049a93b57cc4,0x49ee0a8f463b417d6750,0xcc929c18881bad60d28,610339653] j) else (page #[0xba2c0001018f0048,0xaa68069801f307ab0730,0x1c0c0000008b7d420771,0x1074aadb000014910,0x3ad747a07f907140774,0x119e065e281e05db0227,0xa5503b84c7c00030404,0x7a64d9b05520947,0x49c4000304495dbd05c4,0x1d90a880003018726b4,0x3ea025e5de10a7802c4,0x44fc00000a6c06840607,0x71b040e80e5455e225b,0x6da3550a69651c890248,0x4cf4012c098503f808da,0x28193bd92b0d06b6413c,0x75305187965a6cd0d1b,0x20c33045521e7005d,0x466548037710000200a8,0xae62035002b04323652,0x6a2075642c0d06650192,0x6a3f077f00c400067ac4,0x4be1ab8901ea023b1b16,0x7a2d24d508a0042f2d9c,0xb706bb602e2048a4af6,1] j))))
def moD13 (j : Nat) : Nat := (if j<103 then (page #[0x581404c1204403008010,0xfefeffdfbbef7bedfd7f,0x4ca0364c23243ffffefd,0x912ac9856480b2c81970,0x4e1206ac8a5660ab2655,0x2b29217090984564dab2,0x597b2c9d963eea0e5662,0x9954ccb0425520acbf6,0x7299394c1ca40e58152c,0x58372c139601caa4e550,0x6124989249c964dcb24e,0x24aa7254392a0c94c64a,0x96064b01257492b9c95c,0xcc496524b27259192c24,0x2f2a0f9646cb036491b2,0xe584f2b9f95c7cae1e54,0x5881d80760009663cb2f,0x5182410fb06a42ce1010,0x1f90ed470e3531918b5c,0x4c845bc29e937094444c,0xc425a010f7a7773969b0,0x654069b84ada42d19688,0xf65d2ad4d64aaf155029,0x891b34d6167d31dd858b,0x628143f19eecf1974f3,0xc7ee36f15b8884386123,0xf587a75d14a771327944,0x604900606812041002b9,0x2a1141b21a45d02e0381,0x19c1101b43a931272498,0x12c8018a6872088480ba,0xc04005b04e18203c0c9b,0x3f404110252544208240,0x4bf82207c180290b051a,0xa1de3ea5740f0c82b229,0x4444318369b90541409,0x128bf88309a462318443,0xd653a9da4926311c13c,0x10820ea40c330cb01659,0xda9883502b10d0322883,0x14c4280001a29c1629f4,0xa582ea56ea717007d060,0x108a02b04a0b11096332,0x8990aa0204c1018100c2,0xa216c691272442e2658,0x35c4380a18415432455,0x2858108162248848f50a,0x770b21d637c658321183,0xc0a5a2a592182a022338,0x69bf29c724d704e83102,0x665f4b99712ee5d0b92f,0x51e7c942a145280180c0,0x2703f03a27424809a93,0xa4248680991918e29a13,0x5b891162324258401601,0xea260550a811f1be15c,0xcaf9512a1428af05d0ab,0xd422d011b0084d21564,0x3da9e50284d05acc57a5,0xa9701ebec1183b5c4b0c,0xc30452cde85c5408055c,0x9b140bf8b33646bcbe0f,0x3d4c818f1b2444383211,0x1c2cc09512a75d09a11,0x691ff98016604a894bfc,0x20122b6463d241140243,0x104d538817c33f00fde6,0x960001f002f846b5b40b,0x12a358f5fe00e16604a8,0x2936cefff8f48005620,0x3014a36027f3506f64d6,0xa980a51b1be194f98155,0x40b10536d91f0ca7cc0a,0xe38b11b1a91045f04f5b,0x1b02913e38b506c02933,0x7af1541e980d4400beb1,0x4e06d602c2e6fc00d537,0x413aa80182181f5bc000,0xe1bbc06a3301887aff5a,0x7dbfb7fc09b,0xdfe79ebde01ad8000,0xaa96800000000005fe00,0x5e1557d71a0060b,0xcf3d7bc035b9ffffe000,0xbfc00001bf,0xb824009295d200ea1b90,0x2905ef828ac56787c001,0xa49a23320605120073c1,0xf00b0c2007190c4805f,0xbc82e3a85d04e240,0x95cb80000392ada6fa91,0x881054a5d7ff1cdf1020,0xb4900108c51165e1ffe7,0x480004004badc007bff2,0x500318662b3feffe92f8,0x1000804bea0ce0e7e965,0xdc83308350ff9f0b1f8d,0xaf006010662c3e1f5a5a,0x8e2d41b00a483df013c0,0x180851602fac46c0a44f,0x603945800007e0761dd4,0x880a0e00018eec0cbbe6,0x99ff8fe7] j) else (page #[0xeeeff1c8da185c800822,0x41204c02680006008018,0x60860c27000efff6f4e0,0x438037ffffe44113000,0x602008d79c7c02c54181,0xc33e70094ab048205212,0x28151b60039d0002bf,0x14750ffff800006401a5,0x6d01241398a000182180,0xd040010000436a7fff1f,0x137a401a8b4ffffff60c,0x301c00f54b7cbb71810,0x70cda37fcfc21a124288,0x5e16bfc03472f5cb20b1,0xef53135440180e0b7a8c,0x19fcca2425f35fe1423e,0x520722f1a00000001bf8,0x7231120f800066015b0d,0x600822cf2003b043cd20,0xbe9f0048400a0926e000,0x1340182c13f2f8077fc0,0x4ffc2e04fe0a2068989a,0xa141005d05e4f43ffffc,0x3ff64f4a800270048252,0xa27100b9c86f8d657400,0x4fffffa81fe04c2cc7d,0x850640b0b901f81125d0,0xa37ffffc2fbf9c6df106,0x30b02684d0060b0726b,0x13bfffff9ff85c09f851,0x6b1ccffb7406a1e14a4f,0x25fe2067259934a] j))
def moH13 (j : Nat) : Nat := (if j<206 then (if j<103 then (page #[0x6000220001001100210,0x12500013001001002010,0x40101030010301001203,0x56011014402310003150,0x640280245200101200,0x10000000c00001610001,0x1113130020210b810430,0x45132070000005072a30,0x2273302020132127400,0xd3400412246035106000,0x2d2880f4000600,0xbd100000000d1a112a80,0x460000303b00000000,0x7a207708da9084000409,0x392815b8000000000010,0,0x3a8959000034c745d800,0x9c0d0550000000012c71,0x27c41000001,0x409124f8b0a009000,0xbcdc00000000000bbb80,640745472,0x54800000000003288800,0x25f21f4f714d6800000,0xb01900419a3d00008006,0x2c120d914,0x844c45680000001056c0,16529,0,0x808c04d0000000100540,0x6e0e0000000011984da,0x5a010ac15e0000000000,0x83080006039000000000,1,0xc1be0000000000,0xb00000000015f00,0xa19c00060d20000,307200,0xb2840000000000000000,0x8000005f000000000000,0x606c00000002021814,0x82d40000000000106000,0x104f000000000000,0,0,0x494e0000,0x408a00000000000000,0x82ac00000,0xc1105be8000692a0000,0x10330000000,1068160,0x985f051c00000000000,0xa00000ca360000000000,0x242d4f40c80400030,4252,0x98c046d26600000006f7,20,4294974054,0x8100000000,0x82060108000511c00000,0x401c040400000000001,0x868000e9f59a52014800,1788913,0x95730720000,0,0xa2c874b8000000133540,0x6099c0cd,0x2dfe000145e000,0x23275730000000000000,0x70a800081fc,0,4670357504,0x40001022400061240000,17028097,0x2800000000816381700,0x4000131bc05680000000,0x39c2b444c4000000060e,0x344600000000857d0,0,0xd551263000,0x9538c4e23200,0x184b400000008150,0,0x307e80000001525c0,0,0x33800000000000000000,0xa5e00011186b,0x1824800000000000,0x70e600000138000000,801130368,0x488e4000000020740000,1905,0x833e0a08000012a00000,0xba9e1317f16b00000001,0xae80000000000000054e,0x85c00042fcc1fe00030,0xa000180fc000204c49b7,0xd05054a506a80f,0xa2f9110b467000184ac0,0xd8ea0001041a14ad94b,0,0x1c40000000516800000,0x8ae0000] j) else (page #[0xa000000000000000344e,0xaa2925,0x80000001142eb3976710,0x1c06e2d3500000000465,0x21818000000001,0x610f0000000000000000,0xfa02b800000018298000,0xd1b00006107822e45,0xe13000010412048cf420,2199,0x1b0000029800,0xa8f0a88518500000,0xfc0002084821c0000000,0x221a51055e0000407501,0x28bf000139aa00304790,0x40e40000000,0,0x269700000,0x62000000000001235,0x8c44baa086e034000000,4,0xb80000000d26f88b4000,0x4800010a78000000184,0x818400000000,0x2b600000000000,0x94680a80000000000000,0xbd0000000000000005,0xfc000616742460000000,0x94483c800020e0000110,0x8e7b81580515a8c00005,0x340000000c25e840a098,0x171000000012c,0xe03000012b0875980000,0x10000245dd2ae000207b,0x119300000001cd,0x42c6000000040a20,0xb000000000001db85002,0x29200000000000000139,0x829c0000000c,0xb80006b5600010178000,0x1f7225400000000001ba,267576,0x685b00000000000,0,0,0x2495800000000000000,0,0xa1281ca8000000780000,0xe40006267000000030ab,0x493a00012c,0xe6f8c9e6000000060980,0x51350000000102e,0x1b1b80002897000000,0x4254000000016ec0,0x1b15c14d00ac0000000,0x120b805fe923000000,0x5864000000e00000,0xac00000000000000130d,0x2a000000000000009382,0xc11f000184cc00000000,0x60500001821d03c,0x8de00200000939407c00,0xc07d00000000000217ac,12303,0x6017268200,0x41140000a26000001460,0xac0000000e1e40000000,1076233,0xc296000000000ea0,0xda22d800002ed004c000,0x3a66b68000000084,9717153792,0x365e40056ae20d2c000,0x23498000022c00,0x202f822a29d70b500000,0xfc000000000000000000,0x84dc00000000000b3,0x217b000082939a000000,0xd60001102c000,0x2d000016b80000c8dc00,133204,0x60cd00000000000,0x256c0000000000000,45216,0xad300000000,0x83012a9e09b000000,0x80000001807b419600c0,0x30a8e0dd0000000006c,0xeb000024798000000000,0x80f60000000341480005,0x140840000d9d18966468,0xd48000233766b2000094,0xc2c2000000000004,0xb974431,0x899000000,0,0x9d480000000,0x24a007c0000917400,0xc2e30000048400060a10,0x2a000000000002022,0x8a3c0000000000000,0x516a5be369900000,536883372] j)) else (if j<309 then (page #[0x42c800000000000827,0x28528330000db7c00000,0xa00000002960c0b20002,43337741,0x41880000000000000000,0x50a59708000004f04e2,0x2540a424f0000029f81b,0x4b4f45d0000000264920,0x5cc494c16e00000002,0x20618000000,0x444e00024b580,0x374aa26eddf20000,0x4b423804880220000000,0x4300000000000160e00,0xa3da0008000020a0001,0x46000002e6b190000000,1667751,0,0x94ce00000000000000,0x85ac0670000000000000,0x3a5ce493013a13d4,4456448,0x4600000000000000000,0x10aaa0d000000003,0xd5520000000606b000,0x60eb82d680ad0b600,0x81460000,0x8f00010564000600b000,0x3ac20c0a0,0xc000000000002ae00000,0x3841b40000000000002b,12768,0x10059089530f86040000,0x244deeaf000,0x6962000183b220400,0x3634f6b90000814c,0x98a9cbcc0000000000,0xaa0051c0b0000000000,0x8000000000000001d299,0x44d800032318000894,0x294581c7027800000,0x1806d02a800000000000,0x2ed10c00000198000000,0x1d80000000000376be2,0x2f0b88ca0002,0x83980000000000,0x9a80b30000000000000,0x301e0a94095d5277c1df,0x4180b6000000020f1d28,0x66740000000277980,0xa00030bbe89400000000,0x28400000004cfe20e,0x5d200327abf80,0xa000123649240001022c,0x13bca0310000614,0x52800088bc000229c80,0xd8183049b2b300000001,0x3c000000000000000d93,0xb340372a8e000000070,2,0xd381dea5240000000000,96,0x8003a80,0xf800000000000211a000,34,0xa05700000000ae2a0000,0x1068e0bba1c,0x180000000103a80,0x80000000608200000000,42371103,0x2ac1017c81f843f80,0x180760ba000000000000,0x20000000000,0x948000000182e000000,0x20003639000000000000,0x8a0e0000000000080d,0x650000000000000,0x41d000000000000,0xfe00018129a89a064de3,0x221e0ce000181a811944,0x102f800000000001,43433984,0xdb0000000000000,0xc00000000000ccca0000,0xadd200020380000c05,0x4152416e808800000,0x4c700001ad2c,0,3292160,0xc02c900500000000a044,0x92c684600000000c1d,0x20c70000000000000,0,0,2144384,0xe00000000000ddda0000,0x9800000000000007c81a,0xc61732da46934,0xa000201ac0b600018238,0x829c839e169800042d,0,0x184b66e00000000,1053] j) else (page #[0x105e0d80000184ec00,786976,0x68000000083780000000,0x53f49e8103c286000144,0xd1e00003393000000002,0xa800009c000000000000,0x209f6cbb000000010b,0,0x400000001838769c0000,121,0x1063000040340,0x41a92d340000518,0xb4c00008f70000000000,0x105a4000000000012,0x58223000000000000000,0xc00000000c1ca000206,0x4ae391f800036770001a,16393,0xb000000002ada000000,24,0,0x27f003800041c5a33c00,8,0x409e00000000000,0x25000000000000000000,0x85680004f6d00013,3812,0x9811e00000000a2e400,0x1c38f200a56d48e28,273302540,0x49400000001dc48cb400,0xc85785e4000166f82cb8,0xc402880dc00b40000000,103,0x119b23c7274a8a985280,0x24fa24c07c8000,0x413f0000000000,0x185c00000000418a0,0x80000413800000000000,0xa54770000042fa000307,0x1a501018895100004,0x20c10000a07a443d02e,0xbac00000009a96000000,0x10960672815c5,0x68000c94c0001777ad7c,0x5c800000000000000342,0x3383000000000,0x16f455284440000000,0xca400000000000000000,5,0xb80000000000309a0000,9447843,0x103b40000000c27a0,0x6f63a000000000000080,0x3d449700000a5013ec1a,0x4ae00002084800000008,0xb1f4272,0x109d25060000000000,0xc96c0000032c11a0,0x100000001842c00010e4,0x3037a17f009a000202,0x8064000000000000,0xc8000000000000000000,0x1b8900000000000270,0x18bf800000000,0x6020000090400000000,0xb4000000,0x9caa0ad712e422f02180,0xc0000d135004146a0000,0x172dc12082c485110b,0x84ca937c08d8000c23a0,0xd0000007800000006b09,0x1a603de0f30000000205,0x266f832a755e4975a689,0x48b4049aa4dc81b,0x44a7a0967a00d0000000,5] j)))
def moD14 := page #[0x50130481100c020043ff,0xb1eeca4d188600059160,0xe100ba11037d1bac,0xb05818824228ce49012,0xa0060010060501e068a0,0x2609c1f83a4e834248ec,0x9384a28848208262990a,0x58901b0803b8742d902,0x600a080020a8220a030,0x6bc0d04292a39f2a1214,0x4619458212841ea3e94e,0x7029a591d66f96265864,0x2054b81d43616e4e05c,0x17fe00190c05617fe060,0x26242400007ff2f09a16,0x499fc055100a38000fe,0xbf2a0c06404fe000b95,0x97991d6494e800fff000,0xe010944e400000002fff,0x7ffffe000017]
def moH14 := page #[0x81c0084222500080020,0x8000114000100510020,0x244800181f00c6008805,0x62e000088d000,0,0x91a800000000000,0x103503d10cc0b00000,0x24800008d80035340000,0x4c380000006c860bc,0x2060e8000000,0xe0000000000000000406,0xa315e000105800208308,304087106,0xaf05a0000002cdc0000,464226304,0x6040b30037c07c002262,0x206c000014407,0x16e101000000105,0x6000001480006151a065,0x17000102f03900064534,0x69160ca1363b70,84413668,38,4730880,0xc5114000000000000000,0xb9000000000000000020,0xc5cc274000b,0,0x10580000009140000000,0,0x63b836000000000,0x3a000000000245600000,0x98003078000c8d00020,0x536000516e8a80000000,0x20c00000000000000,0x3750000000000145c000,0x40c8000001905490800,0xac65c000811808800000,0x401c000000e990c,0xfc00000001f00000000,0x20000248000a290006,0x8000a300004020000000,0xc19c474108000801,0xa1c0cb968800,0x4800000000000,20447232,0x60d20238200,0xc028000,0x8000000000000300c232,227,0x9800010be8a000000000,0x48c228720400000028,0xf400000000000020420,0xc3d45680010760000006,0,0x40004478000000000000,0xb8002410000000000205,0x8155ca08d000081c24,0x2201800088e6a840,0x65000000000010160000,0xa24021bab10120000,0x173a92a812c0b102511f,0xf1074e2801b30d892800,9793122970,0xa000000000000000000,16,0xb8d00060d400000041c0,0x800000000010b16ef035,3335]
def moD15 (j : Nat) : Nat := (if j%103=0 then 0x4030301011ff else 0)
def moH15 := page #[0x66000000000000000400,3,0,0x9800000,0,0,0x3080000000000000,0xc040000000000,0x3510000000000000,0x1860000000000000,0x21002530000000000000,0x1740000000000001,0,0,0xc0c00000,0x24600000000,469958656,0,0x3a70000000000000,0,0xe98000000000000000,1248,0,0,0,0,0x5dc000000000000000,0xd1c000000000318000,0x540000000000000000,0x29300000000,0x85c0000000000,0x24000000000000000edc,0xc440000000000,0,0x10000000000000000000,0x900000000000001,0,0x894000000000000000,0x7300000000004dc00000,0x14000000000000000003,0x27000000000000000001,1,0x61c000000000000000,0x84c0000000000,1331200,0x5c40000000000000d0,0x6002310000000000000,0x951970000095f,0x500000000008cc00000,2,0x6700107c08,0x22000000000000042000,3162114]
def moLevels : Nat → Packing
  | 7 => (1,8,9,65537,0,0,4099,moD7)
  | 8 => (5,7,9,327684,50,6,4104,moD8)
  | 9 => (31,6,9,1835032,85,9,4128,moD9)
  | 10 => (326,5,9,8454315,136,14,4486,moD10)
  | 11 => (889,4,9,6095050,120,16,4887,moD11)
  | 12 => (386,3,9,1769521,86,16,4753,moD12)
  | 13 => (66,2,9,655368,67,13,4360,moD13)
  | 14 => (9,1,9,65537,0,9,4180,moD14)
  | 15 => (1,0,9,65537,0,0,4099,moD15)
  | _ => emptyPacking
def moIndex : Nat → Nat → Option (Nat × Nat)
  | 8 => lookupShort 1 2 0 2 0 0 moH8
  | 9 => lookupShort 1 29 0 7 3 2 moH9
  | 10 => lookupShort 17 257 2 11 5 4 moH10
  | 11 => lookupShort 152 1523 4 15 9 4 moH11
  | 12 => lookupShort 437 1901 10 16 10 4 moH12
  | 13 => lookupShort 199 1993 4 15 9 4 moH13
  | 14 => lookupShort 40 409 5 13 7 4 moH14
  | 15 => lookupShort 12 431 1 10 4 4 moH15
  | _ => fun _ => none
def mo : Forest := ⟨1535,15,fun i => moY[i]?.getD (0,0),moC,moA,moLevels,moIndex⟩
def sgY : Array (Bits × Bits) := #[((word [0xf4e2669a6837f02708,0x1c0f22055df808222736]),(word [0x40209409843f00700,0xc0720001df800000733])),((word [0x601c324b0690105978,0x3f9010a2609fbe0181f]),(word [0x2080a02e2690001878,0x1f800000000fbe0180c])),((word [0x250f0dd0188027ef80,0x24025e13c1fd105e4930]),(word [0x22808d1092003e780,0xe03c1fd001e4031])),((word [0xc9c0d9068740409012,0x40ffc4fc1e1027e41fc0]),(word [0xc0c0010ec000000000,0x7fc0fc1e0003e01fc0])),((word [0x1028d4b1279c83fa01,0xf1902f20e021fc806260]),(word [0x1028d4b1279c03f801,0xf1800f00e001fc006000])),((word [0x869100254921090024,0x81248fff0841ffff8000]),(word [0x9100a343a0000000,0xfff0001ffff8000])),((word [0x81412a020041,0xfe000ffffffe01001009]),(word [0x814120000001,0xfe000ffffffe00000001])),((word [0x28004905ffc0481,0xfffff04000804208c000]),(word [0x28004905ffc0001,0xfffff000000000000000])),((word [0x3a518020b05fffffff,0x8400880910680110480]),(word [0x20aa0103c5ffffffe,0]))]
def sgC : List ColumnInfo := [(64,0,447,0,13),(128,0,383,0,13),(256,0,255,0,12),(32,0,479,0,12),(4,0,507,0,12),(8,0,503,0,12),(2,0,509,0,12),(17,0,494,0,11),(7,0,504,0,7),(16,0,495,0,13),(3,0,508,0,9),(32,1,460,18,7),(16,2,424,69,7),(9,16,486,0,8),(0,32,94,385,8),(16,4,353,138,7),(4,8,227,272,7),(0,8,227,276,8),(2,1,460,48,7),(256,8,227,20,7),(14,0,497,0,7),(8,4,369,130,7),(5,2,440,64,6),(16,256,135,104,7),(10,4,369,128,6),(258,64,189,0,8),(34,1,460,16,6),(28,0,483,0,8),(0,16,486,9,10),(260,8,227,16,6),(0,64,189,258,10),(9,0,486,0,8),(36,128,347,0,8),(260,0,251,0,8),(35,0,476,0,7),(256,32,94,129,7),(4,2,440,65,7),(0,128,347,36,10),(56,0,455,0,7),(32,256,151,72,7),(1,32,94,384,7),(40,256,151,64,6),(11,16,484,0,5),(15,16,480,0,4),(36,0,347,0,8),(2,4,369,136,7),(258,0,189,0,8),(64,1,396,50,7),(268,0,243,0,7),(8,256,151,96,7),(13,16,482,0,5),(33,0,478,0,9),(11,0,484,0,5),(134,0,377,0,8),(13,0,482,0,5),(8,16,486,1,9),(273,0,238,0,7),(264,0,247,0,9),(44,128,339,0,5),(1,16,486,8,9),(352,0,159,0,8),(289,0,222,0,7),(2,16,484,9,7),(39,128,344,0,4),(256,64,189,2,9),(128,32,94,257,7),(3,128,344,36,6),(20,8,227,256,6),(48,1,460,2,6),(32,128,347,4,9),(37,128,346,0,5),(259,64,188,0,5),(265,16,230,0,5),(2,64,189,256,9),(4,128,347,32,9),(16,8,227,260,7),(296,0,215,0,7),(64,2,440,5,7),(64,256,151,40,7),(72,256,151,32,6),(96,256,151,8,6),(257,32,94,128,6),(41,16,454,0,5),(44,0,339,0,5),(69,2,440,0,5),(266,64,181,0,5),(19,0,492,0,8),(49,0,462,0,8),(152,0,359,0,8),(128,1,332,50,7),(256,16,230,9,7),(4,16,482,9,7),(8,128,339,36,7),(16,64,173,258,7),(6,16,480,9,6),(136,4,369,2,6),(272,8,227,4,6),(384,32,94,1,6),(73,0,422,0,5),(262,64,185,0,5),(265,0,230,0,5),(274,0,173,0,5),(274,64,173,0,5),(276,8,227,0,5),(292,128,91,0,5),(39,0,344,0,4)]
def sgA := moA
def sgD8 := page #[0x5493048198edda54c910,0x483a454d524c12032553,0x549814c120f055354930,0x9513fe9b94549814c153,0x588f587f42ef25c4befc,0x2edebeda1759cedd17,0x1000090fd30b281]
def sgD9 := page #[0x54d52481105495148110,0x64d8254910edda54c910,0xe9d9354910e9d8354910,0xed19354910ec99354910,0x6a7a754910e9f9354910,0xed1a960d10aa7a754910,0xec5a564d10ec1a564d10,0x6a3a464d10663a464d10,0x605514c120605314c120,0xe61524c12054d524c120,0x2e5534c120e91524c120,0x549814c120ec5534c120,0xe91814c12054d814c120,0x661a54c520edd954c120,0x6d8a954d206a4a954d20,0xed193605206dba154d20,0x64f916052054f9160520,0xea791605206cf9160520,0x6a7a6605206d79360520,0x657a464d20aa7a660520,0xe515260530e63a464d20,0xec59260530e519260530,0x6a794605306d79260530,0x6eb94605306cb9460530,0xea79460530e9b9460530,0x5be1ff87f61ef86fe17f,0xdadedb7aecfda7be9afa,0xf1afc5ff16fbf4afbabe,0x3afcdbf1efc77b1ddc6f,0xfcd7b75ebd6f757ed5bf,0xfe5bf7f4deeb7b6debb5,0xff0bf6afd63deaf3d39a,0xe9c797c703ff0ff63fd2,0x4c43b62c072ca03cb24e,0x1bc63c6f18e4ba5353e9,0xcb8cdf0529fa44a36610,0xa05f1e705cb981f2e50d,0x6f1af0bcbb46f1ad19c6,0x602a18306960c009cbc4,0x63fb814f6e4427c40cf6,0x7a71d7e9c757a71daed0,0x542a54903db8214ea078,0xe8f052a0c949c2e5183b,0x71959bb7524e61431c64,0x987fb65e854d72dc658b,0x10cb6d8e61a77b665eed,0xa67d16a5e45a9744f2dc,0x899e9a22bc4848f2205b,0x771681fc89d1e9a42bc4,0x9ac6f94ae2e9aa8ba6a4,0x89a9c0af06e8ba6b91e,0x9c1f05c0089cbc22727,0x2307317054130440f034,0x3b0e4370d4330be2d89d,0x5494a4b9204490a408f4,0x6b9a5669926297c5b966,0x87e1783e007d1e072db6,0xa667a9ca619664a90a3a,0xc971dc22f3baed6b06b9,0xe8f8dddf68d834bcf32d,0xe040680a3a00058063b2,0x66021c94099e01470075,0xc023e00267e0487c0481,0x47940142720dc000300b,0x7f60f012425a06a0fa05,0x5c25881835e27c136028,0x407a0b20804d9158ddc0,0x88a0ae1220a46f606496,0x2c200001d60901741941,0x70497c248c0000000002,0x1b6100007a21b040cbc,0x6b6100008d8400000000,0x10004e6200037d944cd8,0x12300009020000d60718,0xe06504339883a8461d,0x8013810000ee00cc6000,0x67a320057a164006081,0x9104010c882ef4310000,0x50687dc08000035a0a5,0x4741039105268403991,0xd41b342]
def sgH9 := page #[0,0,0xc50000000000004402,0,256,0,0,0,0,0x800000000000c3,0xbb000000000000000000]
def sgD10 (j : Nat) : Nat := (if j<206 then (if j<103 then (page #[0x48110549204415148110,0x441854811060d2044153,0x68d20441984811064d20,0x481106a120441a548110,0x441854c910e852044393,0x6a532441a54c91065532,0x4c910e5532442a94c910,0x441835491060952443a5,0x6a552441a35491064d52,0x54910e4d52442a954910,0x443a954910e9d52443a3,0x65582441936091054d82,0x609106a582441a560910,0x4439560910e4d82442a9,0xea582443a560910e8d82,0x64910aa583441a960d10,0x441a3649106619244193,0xe8d92443a1649106a192,0x64d1066193443a864910,0x441a864d1069593441a2,0xe9193443a264d10e8193,0xe4910ea193443a564d10,0x441a8e491068f9244183,0x54530481314c1206a393,0x4c12054d30481524c120,0x481984c1206553048181,0x6a130481a54c12068530,0x4c120e6130483934c120,0x480a94c520e9130483a1,0xaa531481a94c52069531,0x54d20e9531483954c520,0x481a954d2068553480a9,0x54d81483a154d20aa553,0x60520661814819360520,0x4839160520aa581481a9,0xe9981483a360520e4d81,0x64d2064d91483a960520,0x4839864d206619348195,0x68598483a864d20e9193,0xe4520e8598483a066120,0x481a3e452064f9148153,0x6979348198e4d206a391,0x6053068f98481a8e4d20,0x4c1a960530649814c152,0xe51814c39260530aa581,0x64530e81914c39464530,0x4c1a5e453068b914c3a2,0xf9bfc7fda1e51306a391,0xfeaff4ff9ffcffa7fb3b,0xffaff57f6bf75f7af7d6,0xfbaf7f7bebbfddfadfd5,0x7fdbfe5feeff57f6bf7d,0xe7bf37f9afcbfe3feffd,0xdbbfdd7edff3ff9fecfe,0xff3fb9fbbfddfdefeb7d,0xeddefef776ffb7ddbdeb,0xbdfdebbfddfdefdf7ebb,0xfb7fdafec7f4bf7dfaff,0xffa7fcbfddfeaff37f7b,0x7aa900ffe7febff1ff6,0x9818ed9003dd37778a9c,0x1db8169c98168c9817ca,0x529da0569d9052fd9057,0xb062fd90633d88663da0,0x3d88829da0733d88725d,0xb2fd90933d88921db883,0xb8e00dd0d32da8b8ea90,0x7d90f43d88f01dc8e03d,0x16d91001da8f41da0f1,0xc9200dd1100dd1014d99,0x3da1517d9153bd39500d,0x803db9709d81701dd151,0xc9a3bd39900dd1916d91,0xb549b3adc9b3ad49b00d,0xe13da1e08d81c3b5c9b3,0x8a145d82109d82101dd1,0x1d9a117d92143d8a107d,0x20cdc2216d9223fdb210,0xca500dd2400dd2300dd2,0x6d8a708d82700dca600d,0x801d92845d82800daa70,0xd2914d9a941da2815d9a,0x7d92b13da2a17d92a00d,0xd13da2c19d8ac11db2b1,0x42e42cc2e11db2d19d8a,0xdc2f00daaf06daae42d,0x241d23215d9b100d9b00,0x83419d8b31bd83319d8b,0xfd23511db3419d8b41bd,0x600dc3600dab663d2354,0x43740d2b740cc3741d23,0xd93841d43741d2b740d,0xa00dab900d93900dc380,0x9bc01dc3b01dabb00dd3,0x1d93d3fdb3c01dabc01d,0xe2cdabe8ac0be01dabd0,0xcbf1a5cbf2ddabe83d23,0x5d24069cc4089c9c01bd,0x258cc422dd8c183d2418,0xc4421dbc32dd9c325db4,0x7d9c42dd9c42fd94459c,0x72fd9462fd9454fd2456,0x9c72fd94] j) else (page #[0x3d2482cdac866cc482dd,0xb50a94a5edb4924db498,0xccd00dacc63cc4b62cc4,0x4d9cf18d8cf19d8ce01d,0x14d9d000dc4f00dacf1,0x9d400dcd108d85100dd5,0x4db5600dc5514d9d515d,0xa09d85a1fd85900dcd60,0x9db18d8db05db5a19d8d,0x8d9dc56cc5c0cdc5b00d,0xd43d4dc5dd35c56dc5c1,0xcde3fd35d00dd5d0cdc5,0xf54df3edcdf3ed4df00d,0x313da6108d8603f5cdf3,0xc6540cae510db6439d46,0x1db6741cc6541cae540c,0x951d16859cc6808d8e81,0xa6c13da6b00dd6a00d9e,0x1dc6c01daec41da6c13d,0xf0fdbef01d8ef01d9ed0,0xaf001d8f001dc6f3bdbe,0x1daf101d8f13ed37101d,0x618d8f513da7419d8f40,0xd7740d4f73fd37600dd7,0x1d4f74bd377415d7740d,0x908dc7941d47841d2f84,0xc7b01dafb41ca7a63ca7,0x1d97d01dc7c01d97c01d,0xe40d47e40d17e01dafd0,0x18013dc7e13dafe13d97,0xc2828cc18290c18192c,0x437da8337dc0236dc028,0x28a37d9866ec28537d98,0x2c28b92c18b92a98b6ec,0xd47d40d46d40d46d48c9,0xc0e1ddc0d6fd80d37d80,0x3d90e31d90e47cc0e46c,0xbdc0e49db8e23db8e5,0x9930adc121cdc111cda9,0x3d1936bc9936ac9937ea,0x41cdc947fda9373d3935,0x4155bd39549d39549d39,0xbda156bd91531d91547d,0x649d3961ddc1565da152,0x99b0adc1a1cdc1931d91,0xb5d1d0a5d1d0ad99c48d,0xf37d81f1dda9e2bda1e0,0x9a135d8a123dba06fd81,0xadaa546caa51cdaa30bd,0x734d8a70ad9a647caa50,0x1ae1dd9ab2ada270ad9a,0xddaba46d2ba0adab954c,0x191cc406fcc3f92c0bf1,0x9c290a9428dd8c18c5cc,0x7dac287d24293c8c28ca,0x937dc436fcc4377db423,0xc500bdc4d46cc4d36dac,0x6db5246d4d20adc511cd,0x51dd8d41ddcd31c5cd32,0xb5646d4d647d4d51cd8d,0xd5cd61cdcd60adc5626d,0xc2bda584dd3584dd3571,0x9dc34d9dc6cc9dc6ca9d,0xadade47d2dd1cdadd6cd,0xa0adae61cdae447d4620,0xa720bdaf01ddaee1ddc6,0x5d8f34dd37365ca7365c,0x761d37647d2f61cdaf63,0x37764dd7764d97764d4f,0xfb033c08c011c00075d,0xd706d41990584142046c,0xa0a50275096422d07ec1,0xdf835c0cf03170b7c2b,0x1ac44e109c3ef0ee439d,0x2051113dc4de12e848d1,0x65118645ea16a457d15,0x7621c906f11b406af1a1,0x5e20d48061f547be1e30,0x24948f423748b422388,0x27c89d526e0993259894,0xc30ae42ab0a7d2940a2a,0xf4bd12eb8b7f2da4b342,0xc993200c6d3178c1e2f,0xd0d33bccdc3338cbb32b,0xeb3740da73604d4e34b0,0xa3a44e753974e423880d,0x3db4f3f3c20ef03b40ea,0x17104740c8fff3f08f8a,0xe914744610e242e50834,0x125648b51fe47251a045,0x3294bf52e54b212ad4a3,0xf74f713bf4e613744d49,0x152f94a751d945250713,0x562156b553151d53f54e,0x99962a58355f057415ae,0x657325c316f65b0969a5,0xd8025f457a65e217765d,0x8f4633d8ae6209858608,0xdf66e99a366159566479,0x66a01a5968f5a0d67ed9,0x6df5b536ca1b036b45ab,0x285c74710dc116f71bb6,0x732dcb87] j)) else (if j<309 then (page #[0x721d8b75d5d4a747dce6,0x65ea779c5e427859df17,0x9f867d81f3b7c35ef37b,0xab81c20338021ff57ee,0xd786ca188852e11c83a2,0x28b3629e899e22d87fa1,0x8e8a3828db63588cae2f,0x2a2472910e40b8f563b8,0xbe59095b2542946a4e49,0xe61097e25e097625d096,0x66a997664c98f662e987,0xdd9b066919a2668199ca,0x79d467299c4a7029bca6,0x9f9a7d19ec27979e1e77,0x17a84ea0ba826a0467fa,0xa8d5a2f6886a1fa866a,0xa9aea63296ba53a92aa4,0xa66a946a33a8729f4a75,0x27ac22af1ab72aa2aa36,0xaae2eb76ad82b47acdeb,0xb0cec1db022becaf1aba,0x302ca4b246c80b17ac48,0x56d37b466cffb3aacd5b,0xedd8b722da6b626d6bb5,0xe7eb9bae52b8eee1bb7e,0x42bc8eef1bb6eeabba6e,0xbf42fbabe12f70bd66f,0xc1d7056c0a300fbfd2fe,0x50f12fc3e70d6c313097,0x971ccc6cb19ec5f7157c,0xf29dc9fb258c8a3200c7,0x383cd6b329cbe72d9cae,0xf0601003007707f01e07,0xbd05c134201002203fc4,0xb60c01812d0ba180b80,0x8f41b83b0404e04002b,0x80d01e030059c060702a,0x10250500934000ae0b61,0x1460e0730302205a0c5c,0xd02015c2d0a05e0d00e8,0xa09ac001fb0809e06804,0x70208380584248550d07,0xc4a0805c0841b01b8144,0xf8341a0f94c844086e19,0x4052a15c230a828109c0,0x134264c806060a0306d0,0xa7bc2051141607024831,0x8528aca04c180699c06a,0xfe890a013c5704da0721,0x810a72041d03c09747c8,0x50746e42c82b12478800,0x4c964251ca0e483c1785,0x103085f137c0a19a0ac1,0x6040760887c15857876a,0x18430c17827189064264,0xb60087104c0430a60c30,0x382084285c1b0a061841,0xc251018081260a1089e1,0x9290150513122a37602,0x52ae0b416c3306423728,0x15a803d3f84143b0039b,0x8813b497c71e746e1801,0xd02d806a1403c230fe34,0x81d3cc04d95de4e660f9,0x1dd5c92462875fa1068,0x6123ec50d6484fa4630,0x850fff406a0a99b9dd87,0xe66484fa463668a5188b,0x8398d0833e0f4ca2f61c,0x699402c5f94242721d9f,0xefd632456194b267895c,0x42bd9a58445fa11a890d,0x451942361eeffc763402,0x184688b5dfa10c26dcde,0xf5c110354753c24268c7,0x70151f280b4f7b0644e3,0x2155ffe6d8900252b6bc,0xfa19c03247bffe3b1a01,0x68fd970d6e7a102216ad,0xae2880030691fea3ac85,0x4e335ff2e9900232aceb,0x40522a7f109d90bafb88,0xb34dff2e9900732a9f1,0x74f00c6525f0db9a2b51,0x80ed451ff856c045b319,0x3ea1350bdc7f08e8ac66,0x1acf5f62000d6605b9,0x4ea32fad612a1519571c,0xe4d44ab3473423dfe854,0x4f8ea51944788225cff6,0x9c0f0851b7fad640688f,0x28954ab2c268c98892a,0x3afbd610a12bf3ea1000,0xd71c00842adff313009a,0x51b2afaf290a0039a51f,0x392497af884632975f88,0xad9b491435fc749640,0xb479e6c1468ddfe982,0x4a953c8a9a459fe261,0x1271623e05bff5e71e80,0x449c588f812716293ca5,0x7814441e1d451138b15a,0xe4f6b20c] j) else (if j<412 then (page #[0x2809bfe5d3200e6559f,0xda1225de240214a57f5b,0x813322631e5e80071a27,0x96445ec1435c12c891f5,0x1d9fb6c164f3ec1439e0,0x41a491d4d123e4134,0x835fefec00511e7fc50e,0x1afc8c93000150f2e406,0x402d239f062d19000171,0x4db0e095f3053dc7fd8,0xff83500009d256bf5c3a,0xa8000e69371f10085295,0xcca8fbbc48032950ffd1,0x4afeb6050137fcba6401,0xcea40007349bbc480429,0x85298f63d64814cebf,0x326fe31a8000e69371f1,0xa78dc41a07e9634c3d17,0x366eb4305c4a66dd8dc2,0x3424f284428a985de38,0xc6e20fae91206d2039f5,0xb40738a28d9503f331d3,0xd1b12d089fd25511813,0xc87ac88d1f90808c450d,0xa76245d3cdd448cf961a,0x7ac4a2772f5b142166d3,0xc95db3930b2c3750a0e6,0x52e227759543227b7930,0xeb8a50042d2ce1c6839e,0x34845b7c03c02ace14b7,0x4ff08082c270c17c8080,0xa6127cb780b13dd3744,0xa931ac065c3e66358fdf,0x28495d2eb004a8f49c4,0x1cd2adb793a4dbf34500,0xfbe30a811a3afd612480,0x1a6d68468bbf43320648,0xfbad6b019238cdad08d,0x3d8106534ff092242063,0x44eb7a4139c034833cce,0x483580f5e4060e9f2f10,0x1a4b789425dff314003c,0x9e1fb34a041b3c9d86a4,0x23ff2c38919663f0dc49,0x33e18a04eb33be4401a1,0xa4bab00c683fafc208ca,0x441133adbde1081209ff,0x80efcd2101c864ffdefc,0x67b00d42c317c8d80521,0x1d3dc9321b12de90404b,0x40111d9d3e611a801d0e,0xf9821f88b204a8e3f40e,0xa239bfaa01878003a23d,0x270a6eed00d841538591,0xaef9f4d0046cc4fc0c00,0x58009926f9ff61b00842,0x6611e990c47a64355fb6,0x4d7dbc0b89dbe96a401c,0xfe68a0010892b76f8410,0x76625fff8a9a8010693b,0x9da6bf82e045b2d,0xf947000004234d7fd238,0x64377f863800001cda63,0xeb2e002a152bf5dd1200,0xd13c7ff83800001cda4f,0x4518dfa104f0879fc7c4,0x683f924e00485231d0e2,0x40002a1c13f84e5a4415,0x8400ff468018cd4fc402,0x195aff4882ed00003e07,0x8257cc163f340008a17a,0x3419bd3054d87ccc96c3,0x12b7e751b00023499720,0x87b018ca77e4f06c0025,0xa348f8fda2000c4927fa,0x880031a4d7e5a7400002,0x916ca00067ae3483f35e,0xd5cc1909f50742057e27,0xde61000049d5f1a8c58,0x81f703ee07dc0f2de617,0x50000170201341a9e0fb,0x828fa616306347f51998,0x4a407c904474247434cc,0x57040cf9f2d8462055d2,0x202ee9251c8c930a5706,0x5f16207c904196c45f16,0x9d4401338329be110600,0xc205392c0e83170e0031,0x211496d9b0356085e1d8,0x287107cc3265908a71b8,0xcbe065e6c2607cba5919,0x30d2581e050698af46a2,0x2b2b9a20f6a5d13d5392,0xfae582bb91eba5485f16,0x22f8b10000d7fe0b4030,0x8e848e84de83441a3d18,0x20f5cb056ee415cc8708,0x1e2d03091f4c2c66f41a,0xaddc822f8b105b2931f3,0xc5daa6d462e8c16b960,0x2cf3147d30b1c7162e5e,0x1832eea18f40f0481e62,302783028] j) else (page #[0x483b480ca0f51782068d,0xcd1cee0b43ea26c98f0a,0x81a0a8fca33668daf580,0xc66c44401e8c6c7a68a2,0xf895ef70614d88a93ca2,0x12fa25142286a75208d,0x133e58267cb0505e2b99,0xf0400031fe5d4543734c,0x93d3331d32c11b117a0,0x72c8427d312ac42d0d73,0x416a2e172f7304a3ec10,0x386ef8e342c91a3133e3,0xd508db298808feae8ea0,0xc4e59c62a382b6c7d210,0xa9632bc6d10d6a886186,0xae601d2ed91b4e9d275b,0x254cc8afa7e714205ee1,0x4836ff1a18d5bbe2838d,0x185024fe49088a527183,0x28e045843494f16eb6ec,0x35dc301da9] j))))
def sgH10 := page #[0xe6819a12007908005916,0x7428a14542800e000810,0x5800103100000009828e,0x24807ec5f04100a8c060,0x83e00020940280,0x889ca0606606e59780a8,0x40350218034a1e8e8001,0xd19900060af06a00cc1b,0x8a4b3060008802a03b04,0x51040c198025a80bbd40,0x489c03ba2d40580001,0x5000081def000440000,0x81380b008934101d0010,0x617800281ccc88717bb3,0x6088800275c000000010,0xb903701281ee06104780,0x17956201f74b02a99f60,0x132821414a8a707e0,0x237c1e000361303240f8,0x4eaa05fa2f400a0d0001,0x1422c16800008701a000,0x5482944203880e207a35,0xc00610b72b81351]
def sgD11 (j : Nat) : Nat := (if j<103 then (page #[0x60910549104c91048110,0xe491064d106491060d10,0x54d204c5204c120e4d10,0x6612064d206452060520,0x60530e6120e4d20e4520,0xef9bfe5130e453064530,0xfbfebfdbefbbfb7f9ff9,0xdffdfedfddefdbfcffbf,0xfaff6feffeefbff7feff,0xf486fffffeffdffcffbf,0xb260aaa40baa20034d20,0xf4e213521bf4206f2606,0x74251352417523135231,0xf4061750517465674253,0xf4862f486174466f4063,0x34a71346717506174a65,0x3508134a813448135071,0xb309a2a69aaa49a26291,0x74893f4296f309a72696,0x552b1152b1552a1152a9,0xf48e274cc6722c1552c1,0x34701742f3f40f4f30f2,0x3511134b113431135101,0x34d2234d213472134321,0x34553f4145f2945f2935,0xaa605b43613515134b51,0xb2a0cb260cb0a0cb060c,0xb500cb4a0cb460cb300c,0x552173521434a1732a1c,0x3262b3042474a1772a17,0x72627552273522435227,0x326347522874e2474627,0x55237352343523732a37,0x74a347463772a3772637,0x32657552473524475234,0x35057346573305732a57,0x3506734a673446733067,0xf4867744647446cf4067,0x750647506774a6474a69,0xb229cb029caa29730677,0xb4a9cb429cb309cb2a9c,0xf309cf2a9cf229cb509c,0x552a7352a434aacb40ac,0x552b7352b474aa772aa7,0x352c4352c7b30c4742b7,0x746c7726cc722c7552c7,0x330d7326d4752c8f4cc4,0x730e772ae7330e732ae7,0x750e474ae9f48e4742e7,0x742f4742fcf40f7342f4,0x33107327072a704746f7,0x35104351073470434707,0x3511734b1434b1733117,0x35337347243472735114,0x32549f29377253755337,0x7454cf41473314732b47,0x32a1d30a147514474b44,0x3462d3262d3062d34a1d,0x3463d32a3d3263d2a63d,0x74a3d7463d3523d34a3d,0x152bd3065d3524d7523d,0x742bd552bd352bd342bd,0x2a70d2a6dd326cd2a6cd,0xd3533d3253d2a53d,0x12a042c0e0028c06c00e,0x7d08d4206073018e053c,0x60d083130b982c70a882,0x1208442101c3d20e7436,0x65455914b851513784b5,0x646a019e464418345cb1,0x7cf1e747841cfc70b1b,0x91c23e08b521e08341ff,0x4728149ec26e097b2520,0x2db8b2a2bb0aac2a1ca,0x337cca03180c262fccbb,0x8b8e0b378cda43594d26,0x10f3f3bd4eca3a64e703,0x908140f900b3f60fae3e,0x1d0467115f44c90fa433,0x2c4bd12bb49a1234481d,0x2518541a4f4938a4d553,0x55bd542549d503535149,0x9e965358915ed5705595,0x857435c8d6f65b316a15,0x185060557ee5e997895d,0x980652d90f634d8ab61c,0x91699da2b67fd9bf668d,0x86e69b646c79ae06ab1a,0x7359c9f71c1c397011bd,0x805dd576c5d86753dd12,0x1dedd7ac5e73791de257,0x9fd97ea1f7a7d41f287c,0x11583a20b5822a035801,0x3388221d4869e17f8502,0x88c3e2df8ada28889a22,0x90f24158f8e3b48dd233,0x49250193424af9236463,0xe660f97ae5bd960654c9,0xa7169baa6b89a1a65c98,0x8189fa27c09e6a7589cd,0x4ca46e8dba2ba88ca17e,0x408e0381a80a9c2a5fe9,0xbe0f07e2] j) else (if j<206 then (page #[0xdc128260b82a170660c0,0x502a8604813a11850500,0x94281007607e14210301,0x20ac99060290582a0698,0x782805e118603e832802,0x66103000c020901f2082,0xc6041b8350d0cb050442,0xf08d0726d800782d0702,0x34103b20d03c09020b82,0xa0b9214370e9330fc3,0xe12031e1836480170968,0x911c46c0e81204844240,0x41452a649e150060104,0x98d455064bc0e2891284,0xc138c0820861304246e1,0x3224341a6060f8671591,0x4f21b47e02200ae1160,0x801849c2604080631a22,0xffb4301831671de3fc09,0x4925cf63660c00324b8,0x7c5d40892a1f8e274060,0xa61fce00689df7a0d038,0x90a05a47dfc294020039,0x8f1e400634a0fcfe7b09,0x2499313ffd00551d795,0x700144ebfea7fef02020,0xdf7a0d039fce00289cfe,0x510c01a33cae7f000891,0x104024929b3fb454233f,0xae7f43fc6c01c91b1d78,0x280212547e4fed141d8,0xf1fca10401892a7caff0,0x2c8fbf106d20159247f,0xebcac7cba0151247d994,0xcd23bf0a80751ce8340,0x9c004e591fad02c4401,0x5fbe3dc202053a5df9f4,0x87499fc385c000d095b,0x4abfa7006451bf1534b4,0x30004c923f903a520078,0x3597c32d02012b3cf888,0x41a070ed79f831000009,0xd23bbeb80000550c7,0xa5e56be300052495cfea,0x1769affd2450c0400826,0xcc00ced41dff8c0c060,0xc669fc002245ef98f968,0xff5b0e10922aec71c001,0x6349def9a522a0049a61,0x10696741a0795af23400,0x820029a52f5febf02880,0x36a3f3c00d13affff8a5,0x2021698fcf40c020005,0xc70808185a833c3f1c2,0x3db1cfb1801e1a80bff7,0x467fe3c48a0600786a4f,0xc4401492e381f10c01e3,0x8d1467d400396a9848fa,0xb5c7c21267d400396acf,0x11d2c03ff113dcd30024,0x804008e963f9e3030080,0x78c0c0200744b1fcf181,0xba7b4b248f21b23238fe,0x664ff587950000099a7b,0x3a05d3c32ccf9e768b04,0xc1a00849c7eff1005ca0,0xb0c48001272fbb11e3d8,0x99718c9f10a85d5deeee,0x73e862800568c0fc3006,0x400992e312f6b4006343,0x4da00e4a1bff38138f3,0xb0f3eb22d957d7a4fb36,0x95997f1baf9001e124,0xf0a1f860910bb4d70cb4,0x88e67a4e4bc4488f684,0x86fe2d5648b317a7c7e7,0x90027505fe3cdf40154,0xa344ebcffc1a9230,0xffdd5880035684d3f968,0x41f4058903e67a02346e,0xffed4918b201a5317fcd,0x7e7ff8030db40189377f,0xcf3f5cf8161c2400c93b,0x45900215ab33f9a10046,0x2d7961c802b662e4de5e,0x511f31a0b1ccefe85a,0x2a8f332078ea32ff5c0,0x894bfea2802c8f3f1be0,0xdb09027299ff02a48006,0x61fab89efc9a20b945f7,0xfb81c46c3c7ae0468c7d,0x86132019fe5cc0e147f0,0x2bf5c0388c3f133a2743,0xdc21988015dac77dd689,0x1349667f570b89f3fe98,0x693f9219251fbcaa4840,0x1303b14a434fce22a254,0xa54ff9d546c4023a546f,0xc4033a489fdf9a32a01a,0xc84a20ef8022451fe210,0x238ebf7ff5900019256f,0x1e6b0001ba52f32a1711,0x8542afd7] j) else (page #[0x8802e480f2ccc78c64f8,0xf949be800056699ff97e,0x86f84bf5c048000d5abb,0x4001152d3fccc0500146,0x86e9100d0b669f32a37d,0x90005ed03ffd2f000164,0x3457cb1ac01d66af9730,0xc000592b3ffa3844007,0x5f0da0488095a64ff23f,0x311c08e9b3a901543f6,0x2a8f34efe348b35f781,0x62e10f8ad85013bfde00,0x13b4b393d9885c2bead,0x186ad82cd9fc363b400,0x87df3b2574eb8c98cac,0x7ef000354795fae01c46,0x208342861fe3c000d51f,0xa0a674f18005c900eac,0xb89168800e69c7ee4384,0x13f9e1c2751a7ffff8de,0x871d0b66dffb7e8002c9,0x27699fce2e13a8dd40,0xedfa000b23d7fdb18300,0x1ef6d0d675fe78800aa3,0x112433962690c854a57,0x16476edd4664dfcfa9e0,0x242e7f00051187dfe600,0x8bdfe00ea3484bdfe00f,0x18698388e3e6cc0174a,0x5b6202548eed6ff3ec60,0x5e50bffd5a740f240ff,0xc0e231cdb982328bd933,0xedce22cd713188a3e3bd,0x53a3080979abed48861d,0x52d5087ad577bd965970,0xe12e1054384cd36f5eb1,0xd968c235503e7852cdd,0x7053a3085c82bba53323,0xd17aeaa181e521051859,0x41971d13a6892886c51c,0xef5902b0fa5903fcca83,0x2bc9cbc82839626a2f0a,0x48473d1c6577aa891a10,0x4ab9476bced6888f6667,0xe5ebac8ab347f659b6ea,0xa2e200b4216d680b684c,0x1b307b7ad10a01a00b4f,0xf3214290c86effccaac8,0xa63c740e409a479934f3,0x8959a83db84618641099,0x6793eb68864] j)))
def sgH11 (j : Nat) : Nat := (if j<103 then (page #[0xf80407010100048,0xfa73060a400040f00000,0x120e080241c2f00884,0x48183a0a0001c0246048,0x180812011500c0e0b1,0xc1604804642b010193a0,0xc0a120501474200301c1,0x8a04411148088e3c0500,0xa818668714800160802,0xe0b0dc0208010f4441c,0x2a20068497e8d02c8402,0x84160807080000804008,0x280d404b0409016b9100,0x7191205e731200418002,0xa480700004040484c160,0x1800004502617008408,0x4800181b03410380781,0x2e02401130900028132a,0x988e08b8135822635b96,0x5176000aa22a139807c,0x2e806e0156002db93800,0x82286822130ae662bdb0,0x6805c911840ae4f3e96c,0x8d416d087e53cf047c0d,0xa0170420124480621e38,0x8c2e0043105cf56c01fc,0x70495f02d181830ab094,0x29c01ee00641b9008d2,0x841e3985c441e08d95f5,0xb3294280bc820c000085,0xdc3d779c112021da1ef0,0xdd2801cf677c68a7e621,0x34c076ee1004571a0ee8,0x825e20bae8e009501560,0x7c143316d062e8ac0230,0x79494c5cf1113409a202,0x3d1001fc0f251aa043c7,0xc81f601e707480004099,0x5ac8c5019704c922c972,0x3c04104146c1c4a5194,0xe0bcbd7776c6100025c,0x58c039c13a0120086953,0x857cb0c6052d941d3700,0x48a0600020666b002e2a,0x172af9000000027a8e0b,0x3e407380000100015b3,0x700015c6545788030001,0x97cf72ca579504000507,0xa204000014e01e6911d0,0xc0c20003020c0b2e5ee,0x64c2869025a27d47ee90,0x83470ad8000000048130,0xd0a0a256e76d2d6d0008,0x516008000b831caa3062,0xa0110914172402dbd604,0x182ca22a3202000089c2,0xb780bcc9bb8168000012,0x5c26681370b41c801fd0,0xd89ef5c2b2904c7fc9b9,0x3a16101e98441048813,0x2db210887f081d82de2,0x1d2cb821609be13f418d,0x57a0ff415a1c1209de11,0xdc8d30040ec829b5c900,0xd42b4903204fa0400001,0x116525c81a0001028211,0x1f1080e067c2c80002b,0x4892829841aa14ac05f,0x212c403100ce81ad72,0x8258077e0d0c04a80ec0,0xc42a685a462f00378175,0xa2cc23003785603a0828,0x15160310e5f028881b40,0xc9d4c224a004a0495e97,0x6ce16e001c2214031e01,0x8564241a148e88091140,0xc1a0e52540002f412143,0x54609952d40001b86406,0xc08c0004943412680520,0x96f913938c80cf8213,0xbe431803e824b68c800,0x21f70a1e00c406c85a91,0x302ae84a8449c0e81eab,0x206136c1c182f488ce07,0xdcc4233613e02400001b,0x5416684f00006894c0f5,0x3ea0464207ad0400060e,0x346776bd00e391200,0x7413c0003b160029d8ee,0x3294fe8079a28da44e52,0x3c03420dd023d02890,0x1b7817007c6f400001,0x6842901a8000160d000,0x49800000001c8a00000,0x20a3400000002022117f,0x25e03495f80002ab8015,0x16b94095ca3294130,0x10027941c054eef74e2c,0x84a03880fc040b33d800,0xa580092e0644ad55c4d2,0x182e205d00b1c0aa0a6e,0x9fe42bc283841e02d972,0x93182804] j) else (page #[0x403a412000030850000c,0x500004098d83a82d6046,0x494805506414f6eac601,0x407b80400c5a40b6945c,0x21091a0a3884f00840a6,0x194bd5a0aaa0c1006002,0xa070ae0500a30aa60750,0x9207e0000c0e8d2f706b,0x22d31e800064b841b182,0xc6200009a6203c612dc,0x16b11971a5ad6022c027,0x18484c60756081800e81,0x481402c1b36c0a88000c,0x740ae216b4024258a05f,0x2800003094d32692c880,0x609a510c00022920c944,0xb80004003404982e345f,0x28494020432114c0d682,0x683900013a05022402ac,0xfda7c467c4022a31d28a,0x28e520e01360ce029782,0xe52a52bd038c4a38f578,0x13082a119229b15c4026,0xc82002a07741084059a2,0x801941bd95b3b8892fa6,0xab44f015e0000325c066,0xe283a9407b457082a081,0xc0eb01a700c6027c12be,0x44000002b806b810b03b,0x2ce097502fe128405a20,0x2057c20c837d061a4fb8,0x1c23e609b40e4023a09d,0x4fe80c8b0cc10480a701,0x80004159853f57faca10,0xd404e60fa002f83b4099,0xe82c308de546029383,0x162c1ee221e0ae81385,0x6b7b5805942d981bd141,0x1cd0313008642381fa83,0x40c0c176b1e000d25188,0x534a4c0e1023f0470000,0xcd01614b420434a1d02,0xa0d5414a141a409c0828,0x2c000484dc1120146043,0x3d05cc0690127823504,4] j))
def sgD12 := page #[0xffff7efbff7bd3048110,0x3c905930b2434801ca5f,0x9e4d3c8a5985a609e4c,0x8222a444c85ca47918f3,0x8a9b131632646488c191,0x6ce458cc31936322c605,0xe0b00046468c0d398672,0xb0870f119c2d04a87309,0x2b2243e6708cc1782a44,0xb9d6f2d318c2e255ca29,0x7012b63b45b865015eb,0x24110a0ac28220f82c1e,0x5038350906c32190589c,0x2990b06214830d81a0a3,0x4403f158243e1c020683,0xc3464260a09054395c88,0x128147eb4e000c520b0e,0xa60040a67f00a40b4fe2,0x2b849387810f730d4217,0x2ec02a04ada80c20de78,0xeff6c42184bff980a81,0x51597fd3800c50edf80c,0xf397220392bbf61c2002,0xc051961fdc2650006565,0x4a15b7b883a0517e79a0,0x2fd08004a1607ffb2280,0x146197fcf3084026557f,0x2f0b5f5c41d0287ff9b1,0xffad88930b3f9cc98400,0x4c016141fe7000114a5d,0xe695c049961e62b073fe,0x1fffd8340260acff0]
def sgH12 := page #[0xc1c03010b1c0102002c,0x600011f08024b050907,0xe08010c020113020107,0x3200f01000009006d0c,0x3b161e3d02160e02040c,0xe1a181d066513000500,0x3202613702520603112a,0x342351a2a0311000006,0x39b3e122e323b18a501,0x2921771400253a01a1,0xc15f4d68149990c50104,0x6035702e02d568382479,0x96464968033020ac2868,0x90607aca0a1a0d2a400f,0xc000409800659300b72,0xc09c59280000322067c8,0xad82e301bc0aead600c,0xc700016b2896a1500000,0x641ee0af00030a341930,0xc14a0c3418f0aa804706,0x2840000d4852f0b58000,0x1040c2a42440293000c,0x4000012eb5501a000000,0x77548e624000030b1c4b,0xcd437cddcfd08d0002,0x82b1071c4910228b0c0,0x800c00000000001e0800,0x93c0001d8848f49da077,0x2bc4107c080000205d4,0x104e621b7d6534a05500,0xb4f8329073c16263a000,0xb2a1610290124498d847,0xc08f02ac23c447c2db0,0xd903102acb6000000a,0x226728d01c05a000249e,0xf201ca1432490214b50c,0xb479000002c40ec1499a,0x8830003a7581ae789415,0x6351230ae11e86850342,0x719240bf015eb5841c97,0x5e2327701c109d40f0bc,0x29e24d01b106580e97d0,0x2c19d5285bbd40603490,0x204641f107429dc019ab,0x8eeb12a58806831e000,0x4d03057cb84be2bf0002,0x40fdb5fdc93bc8919f6,0x30258184000413c00,0x9800000030cd8248000,0x107880fb04800e30d1d,0xaa40908d8fc02800,0x420c82701d0001008c17,0x770c0804d45f10960001,0x943010c6c1fea5f9d044,0x810d07942c164b8acb05,0xb1e0860c2200d989b485,0xba08280060a802d30396,0x97a20b00000c1d6076c1,0x275003b59d524c05490b,0x1510d9356c9641b30000,0xe14b50c4011743002ce0,0x402d77dc325956447b07,0x1b4ee82a4970a300bb,0xde0d7c914476ed246bd0,0xa016412b4aec95213a40,0xbe0003422c1f4000c18,0xb980f506d5a1002f5943,0x70228017034b02d9ddf0,0xd509009404f13fa50102,0xecb10bd28f0bdc27b098,0xd604c428a0699e1e4afd,0x20d39f3f5a0920010940,0xbc51242010000306f000,0x50c08508880140cf9295,0xe405309f8093a598e090,0x22f478c4e5a20593801,0x242b4a41aa2b0c2ea7d4,0x290c28180030000322b4,0xe0bcc294000ed6f05e09,0x503b250000000011f,0x5f9d0109981104a6820c,0x1c028000026d08c41050,0x4af1255010873a14ad05,0x8b2fab200000d4,0x68000589140600032b10,0xb034c2060d69b5a09782,0x47e00014030212032800,0x5b0dd801f0a44000d425,0x4024e007811fbc091020,0x4298000832c095c01260,0xace241c14ea5b890b0ce,0x1094021e25e00490cc0]
def sgD13 := page #[0x6001f36804c120443ff,0x341410281a1a16120a0e,0xe802012c810082004024]
def sgH13 := page #[0xc44362122d0052001005,0x397000d961100,0xc0c00000000000000,0x5038a780041200205000,0x640b00800125c0061bc0,0x2280000084c002050008,0x5bc000008348ac,0x18500000000000000,0x3448000000000000,0x1480009a001074000000,0x500c0b00000000000001,0x800000000000000c19ad,0x3c0848f4000000000020,16834700,0xa002370009ba00000000,0x127e00caa0700000089,0x83f4000000000,2188,0x130d6300090c00000,0x2e001030000000000000,0x8540000090200000000c,0x606e07dcc000000001c6,0x7e26ca224c0000042410,80608]
def sgD14 := page #[0x90e08185081808013ff,16]
def sgH14 := page #[0x8c00000000009200,0x8d0000000000d400,0,0,0x45004a5c00c9005500,0xc1009de4c000028400]
def sgLevels : Nat → Packing
  | 8 => (6,6,7,327686,51,6,4097,sgD8)
  | 9 => (69,5,7,2818098,102,10,4151,sgD9)
  | 10 => (373,4,7,4849791,119,14,4299,sgD10)
  | 11 => (216,3,7,1769495,85,14,4244,sgD11)
  | 12 => (30,2,7,327683,50,11,4144,sgD12)
  | 13 => (3,1,7,65537,0,6,4109,sgD13)
  | 14 => (1,0,7,65537,0,0,4105,sgD14)
  | _ => emptyPacking
def sgIndex : Nat → Nat → Option (Nat × Nat)
  | 9 => lookupShort 1 113 0 8 3 3 sgH9
  | 10 => lookupShort 26 127 7 13 7 4 sgH10
  | 11 => lookupShort 159 691 9 15 9 4 sgH11
  | 12 => lookupShort 102 467 8 14 8 4 sgH12
  | 13 => lookupShort 16 163 4 11 5 4 sgH13
  | 14 => lookupShort 3 59 0 8 2 4 sgH14
  | _ => fun _ => none
def sg : Forest := ⟨511,14,fun i => sgY[i]?.getD (0,0),sgC,sgA,sgLevels,sgIndex⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem monoGeometry : graphValid mo (boundsBefore pri) = true := by
  simp only [graphValid, Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=6) ?_⟩,listPieces_all (d:=3) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem signedGeometry : graphValid sg (boundsBefore spri) = true := by
  simp only [graphValid, Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=6) ?_⟩,listPieces_all (d:=3) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem moChunk10_0 : block mo 10 0 108 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem moChunk10_1 : block mo 10 108 109 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem moChunk10_2 : block mo 10 217 109 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem moChunk11_0 : block mo 11 0 111 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem moChunk11_1 : block mo 11 111 111 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem moChunk11_2 : block mo 11 222 111 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem moChunk11_3 : block mo 11 333 111 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem moChunk11_4 : block mo 11 444 111 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem moChunk11_5 : block mo 11 555 111 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem moChunk11_6 : block mo 11 666 111 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem moChunk11_7 : block mo 11 777 112 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem moChunk12_0 : block mo 12 0 128 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem moChunk12_1 : block mo 12 128 129 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem moChunk12_2 : block mo 12 257 129 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem moTables : checkedTables mo 15 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact (@block_merge mo 10 0 217 109 (@block_merge mo 10 0 108 109 moChunk10_0 moChunk10_1) moChunk10_2)
  · exact (@block_merge mo 11 0 444 445 (@block_merge mo 11 0 222 222 (@block_merge mo 11 0 111 111 moChunk11_0 moChunk11_1) (@block_merge mo 11 222 111 111 moChunk11_2 moChunk11_3)) (@block_merge mo 11 444 222 223 (@block_merge mo 11 444 111 111 moChunk11_4 moChunk11_5) (@block_merge mo 11 666 111 112 moChunk11_6 moChunk11_7)))
  · exact (@block_merge mo 12 0 257 129 (@block_merge mo 12 0 128 129 moChunk12_0 moChunk12_1) moChunk12_2)
  · decide +kernel
  · decide +kernel
  · decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem sgChunk10_0 : block sg 10 0 124 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem sgChunk10_1 : block sg 10 124 124 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem sgChunk10_2 : block sg 10 248 125 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem sgChunk11_0 : block sg 11 0 108 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem sgChunk11_1 : block sg 11 108 108 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem sgTables : checkedTables sg 14 := by
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
  · decide +kernel
  · decide +kernel
  · exact (@block_merge sg 10 0 248 125 (@block_merge sg 10 0 124 124 sgChunk10_0 sgChunk10_1) sgChunk10_2)
  · exact (@block_merge sg 11 0 108 108 sgChunk11_0 sgChunk11_1)
  · decide +kernel
  · decide +kernel
  · decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem monoRoot : Impossible false graph 15 inputs.toFinset := by
  rw [show graph = targetOf mo by decide +kernel]
  exact root_index (g:=mo) (top:=15) (i:=0) (before_sound pri vpri) monoGeometry moTables (by decide) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem signedRoot : Impossible true graph 14 inputs.toFinset := by
  rw [show graph = targetOf sg by decide +kernel]
  exact root_index (g:=sg) (top:=14) (i:=0) (before_sound spri vspri) signedGeometry sgTables (by decide) (by decide +kernel)

theorem rootSImpossible : Impossible true graph 14 inputs.toFinset := signedRoot
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

def clipEntries : List TransportEntry := [(179,5,55,[81,114,50,65,99]),(188,5,61,[112,16,66,97]),(254,8,251,[32,113,67,81,101]),(422,5,61,[80,16,33,50,116,131,99]),(433,5,55,[80,16,66,49,114,131,98,99]),(440,5,61,[80,16,66,130,113,97,98]),(444,8,63,[48,33,113,80,132,64,96]),(446,9,127,[32,49,128,81,116,100,96]),(454,5,61,[96,16,114,50,65,133,67]),(499,9,127,[81,130,99,65,115,50]),(510,12,255,[128,49,100])]
def clipKnown := moveEntries clipEntries known383
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem clipValid : Known true clipKnown := movedKnown valid383 (by decide +kernel)
def ecY : Array (Bits × Bits) := #[((word [0x108380004061f0c00,0xdc0661804078f001f]),(word [0x908380004021f0400,0xd40260804078b004f])),((word [0xc10040c83828e03c27,0xde85c999e1ffc070cf1f]),(word [0xd00046c82aa0a0a825,0xde80888161318020e310])),((word [0x6078001c009003018,0x120600060878700fe0]),(word [0x2078001c009001008,0x100200060878500c80])),((word [0xf888000e0031ffc1e0,0x18e437e007f1bf80f1fc]),(word [0x5888100a0100c701a1,0x180515f000e083021178])),((word [0x3000f0003e000240,0x60f83801f801c000fe00]),(word [0x3400f0003c000240,0x60f02801f0014000ee00])),((word [0xc000ffffc0000380,0x7f003ffe0001ffff0000]),(word [0xc1005cf180800080,0xb003fd84481f0644400])),((word [0xffff0000000003ff,0x80003ffffffe00000000]),(word [0xd9980080000203da,0x377c9ecc22080001])),((word [0xff00000000000003ff,0xffffc000000000000000]),(word [0xfd0000000000140377,0xf4efc000000000000000])),((word [0xfffffffffffffffc00,0]),(word [0xa72664a1063f18a804,0x20400001010004008882]))]
def ecC : List ColumnInfo := [(1,0,510,0,12),(4,0,507,0,12),(17,0,494,0,11),(132,0,379,0,11),(1,16,486,8,9),(3,0,508,0,9),(4,128,347,32,9),(12,0,499,0,9),(33,0,478,0,9),(65,0,446,0,9),(257,0,254,0,8),(9,16,486,0,8),(36,128,347,0,8),(67,0,444,0,8),(1,2,440,68,7),(1,32,94,384,7),(1,64,188,258,7),(4,8,227,272,7),(14,0,497,0,7),(35,0,476,0,7),(268,0,243,0,7),(289,0,222,0,7),(321,0,190,0,7),(3,64,188,256,6),(12,64,177,258,6),(65,2,440,4,6),(65,32,30,384,6),(68,8,163,272,6),(257,32,94,128,6),(257,64,188,2,6),(260,8,227,16,6),(259,0,188,0,5),(14,64,177,256,5),(35,64,156,256,5),(41,16,454,0,5),(73,16,422,0,5),(78,0,433,0,5),(259,64,188,0,5),(268,64,177,2,5),(289,64,156,2,5),(321,32,30,128,5),(323,0,188,0,5),(324,8,163,16,5),(332,0,179,0,5),(270,0,177,0,4),(291,0,156,0,4),(102,128,281,0,4),(270,64,177,0,4),(291,64,156,0,4),(297,16,198,0,4),(355,0,156,0,4)]
def ecA : List (List Nat) := [[],[32,83,116]]
def ecD9 (j : Nat) : Nat := (if j<103 then (page #[0x4ca98c31bfed9a1a6053,0xf2dd9860d6318717ecc3,0xa558c61e5bb66cc2c630,0x736fd3326c18c38bf663,0xa9b2030e2fd98e998318,0x3db660d6364061adf36c,0x59590186b7ddaac6c80c,0x1adf766b2b2030f67985,0x30ac80c35beed9836406,0xd6f9b3e1990186b7ddb,0x1a3e1861adf36bc33203,0xc737bd4f4cc09038bf66,0xcb1b0298c3ffb86a5654,0x631bfed9a960531f5ab0,0x9e99814c797bcb70cc0a,0x318dff6cd4b0a98e6f4a,0xb3434c2631bf6dba1655,0x98c6ffb66a7854c637fd,0xe396e1931cdef2cd0f0c,0x54f1fbcc342432a74bf6,0x74c8922a9e3df9868c86,0x2a71bfee996259538fef,0xb86a56354e1ffdd3304c,0x953b79b644c306a9c3ff,0xdb3434c2a74bf6db98a1,0xab1e3fb986808558e37f,0xe61a621563c7bf30d190,0x558f0ffcc34e42ac78bf,0xf74cc130b1c77fba6549,0x1ac79bded9a12616387f,0x5b12618658ede6d9130c,0x4d81b1fb6e4c30cb1daf,0xfdb35229b039bd259a11,0x6c0e6fb966808360637,0xfe59a420d81cddf2cd11,0x8360733fcb34a41b039a,0xfb4fcb106c0e67f96a94,0x49b031bfeeb9620d81c9,0xffa8259536063efdd326,0x54d8197f360542a6c0e2,0x7edb752a9b032bf6d8a8,0x326c0c6feba259936063,0x3f69c9694d818dfd75cb,0xa5360637fdb35329b039,0xdef2cd0cc6c0e4fda7e5,0x3cab075bd6c4a3e5981c,0x6ffb66869894e37fdb34,0x858e6195f970d32a730c,0x73eda950b1cc33bd6c4a,0x1b0330cef5b1aa163986,0x3bd6c7a660e619de974b,0x8595a0e37edb752a9d03,0x8dfb73d330398c6fdb6e,0x52a9ec31bfee996d4731,0xe3ff986869854e1ffdc3,0xa1e0d539dff6cd0d30a9,0xe77fdb343c1aa78ffe61,0xcc2a6b0d3ffb865b9154,0x36fdee15360561adff6c,0x2a15360757fd412ca9b0,0x1b5fb6c542a6c0dbf9b0,0x306a9b032ffae8a854d8,0xfb5e85a0d53607b6fcb,0xb8654d81edbf2d41aa6c,0x737ed472ca9b032ffae,0x1cb2a6c0e6ffa8e59536,0x39bfe59a5a0d81d5ff5,0x3a168360797e4b50b41b,0x81cdff2cd2d26c0dbddb,0x4330a9cc35bf6d6a3e59,0x30dafcb8699539871ffd,0xc78654e61e5fb31c32a7,0x986f6ed9f0ca9cc37bd6,0xca9b0330cefdbae1953,0xe636fdee15360661f5ef,0xc14006400337fd332ac0,0x62c55044c3c035c2f821,0x789ec9608d48207946b8,0xcd48cbcc58bccb68b04a,0x2cfa0f3ced8e74e10da,0x112852211bd1590f5091,0xd59152d4c946540139d3,0x8ed88982579970d68161,0xf9b95b31acda419b5951,0xdf19eb5dd9d25cc1c5db,0x1d617210e0aa045fe1f7,0x824f646a3b632a29e23a,0x687a81678a6fe69a60e5,0x9ce99297e91a9068ca8b,0x72b5eb22ae6aaaa46a0a,0xec8ac4ec3abd6bc2baeb,0xd3ed2ad16d02cc6cb2c9,0x2f83e00added7ad66d52,0x102c0d941b44c164481a,0xa285f081b058a1430be,0xd1122a0fc1f004890502,0xb141b84fc305a12068c0,0xf0e120a061460ba10360,0x84c2a18558282de18345,0xf0c1a1835e1e0a6a13c3,0xf0c5506860de0a6a0c55,0xf802f050510360b0a83,0x7c105c7e] j) else (page #[0x80205bc10347e0f80206,0x7c01783e00bc1f005e0f,0x82080fc10385e07822f0,0x7c01783268bc193440cf,0x83e00bc1f005e08382f0,0x408782a48dc3f08141f,0x822f03c11783240bc1f0,0x40df800c0fc19205e07,0x4140586c4f83e00fc1f0,0x1220521710320a420307,0xfc21c15e18bc1f005e0b,0xbc3828523f81e18ec391,0x5e1a142f07c01783e00,0xc16050152783448bc1f0,0x7c0102a0a02fe182c507,0x83448bc10645e00302f0,0xbc1f005e0f802f07c017,0x87e0f802f03c11783e00,0xc4a201de0b0a3e17c112,0x81d181de0b0a364f85f0,0x7c3074607782c28e0d84,0xa305fc1c147e07822a1,0x92104921f07c0102fe0e,0x38141438484008492204,0x40140648083410681c10,0xa020a25051001448,0x486122000000001008] j))
def ecD10 (j : Nat) : Nat := (if j<412 then (if j<206 then (if j<103 then (page #[0xbe58d901872fd9858c61,0xee19901876f96564061d,0xea5812072fd98e1861db,0x598320f75d9560c839fd,0xd8621a7dfa960c83db76,0x9321a6ffa961886d3f65,0x854e6ffa666131db7619,0x54e7f5a1261539fe6809,0x4e3fca8659539bf69898,0x66fda6e45538ffea1965,0x7f9a0261639bfe999858,0xeda2261639fd6849858e,0x786606619df6949858e7,0xa1e1a61cbf66386987af,0x5614319bfe9991e0eef5,0x618539ff6a5850c777d9,0x58539ff6a58614f6fd96,0x8539ffea19614e7ffa16,0x539ff6a68614f6fd96a1,0x1df764d531867fda1a60,0xbbf699531873fd9854c6,0xffa61531867fda954c61,0x760d631867ffa954c61c,0xe95631876fd9858c61fb,0x4d831876ffa958c61bbf,0xd8318777d9560c61df76,0x831873fd9860c61d7f65,0x318777e9560c619ff6a5,0x1877f95364061bbfe998,0x877f98564061dfe60d90,0x77dda864c61df7695931,0xefda3e1861cff68d9818,0xfda961463ddf6558518e,0xd95a14639ffea19518e7,0x9354c819ff6a68518f77,0x954c819ff6a5532077dd,0x60481fbde99812067ffa,0x4483dfd6959120f7f7a9,0x483ddf6859520f7f5a66,0x83dbf6859620f77da665,0x1df76959321b6fda5658,0xbfd684854c6ff9a02153,0xf768c854c6feda221531,0xf69c854c6efda621531b,0x6a5514c67fda921531b7,0x19634c6ff7a154d319ff,0x1634c77dd9858d31fb76,0x634c6ff7a158d31df7e6,0x54c67fda959531ff5e85,0x4c67ffa959531dbfe596,0xc7ef4a660531ff528d81,0x7fd56360531dfd2a5814,0x7f59560531efd619814c,0xfda960531dfd659814c7,0x78660531ff598d814c67,0x9660531dfde55814c7bf,0x360531bf7e8d814c77f7,0x60531bbfe99814c7fd7a,0x19319ff6a5854c7ef7a6,0x5319ffe85954c67fda96,0x319ffe99954c77f7a165,0x1dfde85964c67ffa8655,0x9ffea1964c67ffa56593,0xffe8d984c76fca666131,0xfe95984c77dfa3661319,0xe99984c67ffa6661319f,0x62634c76ffa666131bbf,0x6654c6ff5a199531df76,0x814c77f595a05319ff6a,0x54c67fda9a1531bfd6a2,0x4c6efda6a5531bfb68a9,0xc6fdda3d45319ff68698,0x6ff5a1d4d31bbf69b514,0xff5a1e0d31bf768f814c,0xfda9e1531bfd687854c6,0xda9e1931bfd687864c67,0xa6e5531dbfe5b864c67f,0x5e59319ff6a3954c67fd,0xe61319ff6a3964c67fda,0x19539ff69b984c67fda5,0x953bfd6848654eff9a02,0x539ff6a48654efdda321,0x39ffaa48654eff6a1219,0xdfd6449154f3ff982195,0xffaa49654f6fd9625953,0xe6809854f3fd98261539,0x6849854e7fda126153bf,0x849854eefda626153bfd,0x49854eefea626153bfda,0x6354e7fda958d539ffaa,0x354ef7fa558d53dbfe59,0x54ff5d8560d53ef72618,0x4e7fda960d53df765983,0xf7df9660d53fd7a15835,0xbdf9860d53cffe618354,0xfda961953dbf6598654f,0xca8659539ffaa58654e7,0x9665953cff2a19654ebf,0x3659539ffe859654f6ff,0x65953df7e8d9654e7ffa,0x5953affea19654e7ffa8,0x153cffe619854f3ffa86,0xe7ffa166] j) else (page #[0x7dd96a0d539ffe999854,0x5e85a0d53bf76a28354f,0xd96a1953df7e5a8354ff,0xa9a19539ff6a68654f6f,0x8a4553cffe628654e7fe,0xa4553affaa29154ebfda,0x6153dbfe5a9654f7f791,0xd53cffe629854e7fda1a,0x53dbfe5b6354ef7da5d8,0x3cffe638354ef7da5e0d,0x9ff6a78654efdda3e195,0xff69b9154e7fea9e1953,0xf69b9154eefda6e45539,0xa9b9154e7fda8e4553db,0x879654f6fea6e4553bbf,0x79854e7fda8e59539ff6,0x535867fda6e61539ff68,0x3586ff9a020d619ff6a4,0x586feda220d61bfd6848,0x86f7da520d61bef69083,0x6dfda720d61bbf698835,0xf7ea520d619ff6a48358,0xf7a6605619ffea553586,0xfa6661619ffe8d98587e,0xa994d61b7f69e535876f,0x1e0d619ff6a6835867fd,0x215639ff6a783586ff5a,0x1563bfd6848558eff9a0,0x563bf768c8558efeda22,0x63b7f69c8558eefda621,0x39ffaa48558e7fda9215,0xddf6549558f3ff982156,0xfe6809858f3fd9826163,0xd6849858e7fda126163b,0x6949858efeda226163bf,0x949858edfda726163bdf,0xd6558e7fea926163bdfa,0x8358fbdc9860d63bf7e8,0x358e7fda960d63fb7619,0x58f7df9560d63fb7a198,0x8fbdf9860d63cffe6183,0xe7fea961563bf7e85835,0x3ff9861963ebf2618658,0xfca865563ebfe618658f,0xf9866163affea19558eb,0xa5661639ffe859858f3f,0x599563bf768e6558e7ff,0xa0d63fb761a8358f77f9,0xd63bf76a28358efdda1,0x563df7e568358fede86a,0x639ffaa68558e7fda9a1,0x3bbf6a28658f3ff98a15,0x9ff6869858f77f95a556,0xbf69b8358f3ff98a6163,0x768f8558f3ff98e0d63b,0x6a78558eefda6e1563bf,0x8f8658e7fea9e15639ff,0x79158f3ff98e1963bf76,0x9558e7fda8e45639ff69,0x558e7fda1e5563dbf61b,0x58f6fe86e55639ff6a39,0x67fda5e61639ff68798,0x6ff5a114d81dbf258536,0x7fea914d819ff6a45360,0xf9a020d81dbfe5853606,0xda420d81bfb68883606f,0xa620d81bdf69483606fb,0x520d81b7f69c83606efd,0x20d819ffaa483606f7ea,0x4d81dbf258936076ff96,0x981dbfe58936077dd932,0x81dbf25953606efea925,0x19ff2a553606bfca854d,0xdbfe59536067fea954d8,0xffea553606bffa854d81,0xf619636067fca958d819,0xe59636067fea958d81eb,0x59836067ffa958d81dbf,0x9836077df9360d81dbf2,0x86607aff8661981dbfe5,0x3607aff9661981dbfe59,0x6076ff9664d81dbf2599,0x76fc9694d81bbfe9993,0x6dfda794d81bfd686536,0x7fea994d819ff6a65360,0xf5a198d81dbfe5a53606,0xea998d819ff6a663606f,0x96a0d81dbfe5a636067f,0x3a0d81bfd686836076fc,0xa4d81dbfe5a836077df9,0x4d81bbf69a936076fc96,0x581dbfe5a936077df93a,0x81fbde5b816076ff96e0,0x1ebfe5b866076ff96e0d,0x9ff697936076fc96e4d8,0xbfe5b936067fda6e4d81,0xf687966076fca3e5981d,0x68f966067fda3e5981db,0x87966076fea3e5981dbf,0xf96607ef7a1e5981dbfe,0x9160eefca664583dbfe8,0x660efdda3a1583bbfe99,0x3bf768e8] j)) else (if j<309 then (page #[0x9ff69b9160e7fda5e458,0xff69b9560e7fda1e5583,0xf6979660e7fda1e59839,0x6879361a7fda3e45869f,0x55538c67fda5e4d869ff,0x5818c6ff7a154e31ddf6,0x838c7ef7a660631dfd65,0x48c67fda961631cff661,0x8c77bf8565231def6159,0xc73fd98e0e319ffe9598,0x6ff5a1e1631bfd687838,0x6fd96596539ff6a7858c,0xdd9660e53bf7e8d6594f,0xd9661a53cff6618594f7,0xa961a53d7f65d8694f6f,0x865a539ffe859694e7fd,0xa1a53dbf65a8694e7ffa,0x62539ff6a68694f5fd97,0x653dbf65b6594e7fda1a,0x61bbf69953986fdda3d9,0x19ffea5539867fda954e,0xfb760d63986efca858e6,0xbfaa1639876fd9858e61,0xfe9563987ef7a158e61b,0x64d81987ef56360661bb,0x9981987ef78660661dfd,0x9839867fda960e61fbde,0x989867ffa366261bbfe9,0x3986ff5a1e0e61dbfe99,0x9876fd98e1a619ff6a78,0x86efda3e1a61fbd68786,0xf7dd9560e63dbf6a7869,0x7fda961663ddf6558598,0xffa165663cff6618698e,0xda3996639ffea19598e7,0xa9a1663ddf6568598efd,0x954e819ff6869898e7fd,0x60e819ffea553a067fda,0x5683dbf65986a0f7dd93,0xa839ffe9995a0e7ffa16,0x839ffe9596a0e7ffa165,0x3dbf65a86a0efdda3a16,0x9ffe9593a1afdda3a1a8,0xf766163cc7edd8658f31,0xf6a565cc76fd9659731d,0x65981cc67ffa9597319f,0x6181cc73fd9860731dbf,0x981cc6fdfa360731cffa,0x85cc777d9561731bbfe9,0x5cc67fda961731dbf659,0xcc76fd9661b31dbfa598,0xc67ffa6657319ff6a586,0x76fca565b319ffea195c,0x6fda565b31dbf68596cc,0xfea565b31dbf6a196cc7,0xfa565b31dbfe8596cc76,0xa865b31dbfe9596cc67f,0x699731dbfea196cc67ff,0xa17319ff6a665cc76fd9,0x1731dbf65a85cc777d95,0x731dbfa5a85cc67fda9a,0x61bf768f51cc76fd96d4,0x19ff6a453d86ff5a114f,0x9ffea553d867fda954f6,0xff6a583d877dd9360f61,0xfea193d867ffa564f619,0x6a653d86dfda794f619f,0xa683d877dd93a0f619ff,0x585d8f3fd9860f639ff6,0x95d8e7fda961763ddf65,0x5d8e7ffa865763dbf619,0xe067fda9a1763ddf6568,0x67fda954f81df764d53,0x67ffa954f81affea153e,0x7dd9358f81ebf61963e0,0xfda958f81dbf65963e07,0xca6647839ffea563e067,0xa6647839ffe9591e0f6f,0x664783bbfe9991e0e7ff,0x60c619ffe8d91e1b6ffa,0x531ffd615814c77fd95,0x531dff661854c7ff6856,0x31ffd616814c77ff9861,0x1bff6a2854c77fd98a15,0xbff696984c77ff98a153,0xff697814c6ffda8d4531,0xf697864c6ffda5e0d31b,0xe856354effda126153bf,0x869854efffa165953bff,0x78654effda1e0d53bff6,0x9154f7fd63e4553bff68,0x154f7fd96e4553dff61b,0x587fdd8354d61bff69b9,0x86ffda854d61dff66153,0x6fffa854d61ff7a0d535,0xffda594d61ffd54d8158,0xfc9654d81bff69683586,0xd8354d81eff2a153607e,0xa854d81eff61953607fd,0x654d81ff7a0d53606ffd,0x54d81dffe5953607bff8,0x4d81bffea153607eff96,0x7bffa85] j) else (page #[0x6ffda5a0d81bff696536,0xffda5a4d81effa168360,0xfda5a4583bff6868560e,0xd9560e31bff6869560ef,0x8354e61dff6159194f7f,0x654e61dff66153987fdd,0x54e61bff6a153987efda,0x661bffea153987eff86,0xe81dff65583987ff5536,0x81bff6a153a07fdd8354,0x3dff65583a06fffa854e,0xeffa1a85a0f7fe856468,0x6d006400037fd9560731,0xc58159024e038c04f80,0x9f0125021803de06f4,0xe707460d5819202f2058,0x27504b8090c115021103,0x418f82fd05ad0ad21470,0xa00ea61ccc37786bd0d0,0x45f088c10b420583ed87,0x627044be8954124423c0,0xdb156429dc5198a1313e,0x5ea8ba316f42d205820a,0xc331864e8c59184e2ff8,0x41b92365c6ae0d2a19c,0x7760eb11d2239a071b0e,0xa404c7e78fa61ec43c78,0x63226243b485d9077208,0x9451258244c47888cf11,0x4d1499292fc25a64acc,0x5628364fec9f213b2270,0xa9a94f1297e5234a3b14,0x5778adf159e2aea5554,0xef2d9e5a2cb2396302c2,0xbfd97c02f2e5d04b8c16,0x66440c6198a330ac60fc,0xfd339666accc5996b329,0xd651aaa3514693cd1319,0xe6e38db71b45364a6c14,0xd5396a71a0e169be0376,0xef99d9d3afa7508e7f1c,0x7bd8f621e923cc078b8,0xec3faa7eb0fc61f5a3e5,0x53a07e40bc808d0019f,0xc86cd0c5214f42168365,0xfa459089ed124a21743d,0x1eca39546c68ce918d22,0x292e124c246f487a9075,0xdb4b7696012a2a50a49c,0x354267f4cbe98b5306a5,0x29e1d3aaa7354e069b45,0xbc5114a119405a7eb4f7,0x4d2298452a4a43947728,0x6aa7953aaa435446a77d,0xdc571ead2d595ab0b55d,0x654ac8058c0b10160bab,0xeb6b16b8ad3f5a2cb349,0x995d04b9417182e105bc,0x7c0af585e3abbf57612e,0xcc1a5820300e5fcabef1,0x8c62d8c50d891b0fa616,0x935b24b6432c7c18e3b1,0xcd7199532f8659eca51,0x7f68bed0fda0233d2674,0xaca35506a3cd3b1a6634,0x6dac9b44b63c6c02d761,0xba6f10dd7db96b7046db,0xc5eb89470b2e0c1bfab7,0xae76dcd4b9777254e3e1,0x347604eb41d4f3a5a741,0xe1bbc057770ee61dbc3b,0xaf5c1e963cfa7990f1c9,0xf67d76f9ddf1e3e017b7,0xebfd97f3cfd8df98be,0xf03f2060c0a180f10186,0x70847d07ea0d6c160826,0x1ddc36e86670b9a15a42,0xb12b2241c451881b0f6e,0xbd8b29158a29cc52289a,0x37fc6df8d37193a300c5,0xb200a3f147a78eeb1d0e,0x40920b239645e4881907,0x50fc9f693ad264a4b949,0xf2c1e56f4aac9507298e,0x697a92ed25c14b3e964,0x67bccaa98f1311a6134c,0xd392e715cdde9b2334ee,0x899eaf3d027874ec19d0,0x84f506ca0753fda7ddcf,0x5473a8c55158a23b438a,0xfaa5a34a7e936d244a42,0xa0353dda7574d9e9a3d2,0xb546ea7954c9a90b50e2,0x23ac07576aacfd56daa9,0xb8156c7ad6159d6b2ad6,0xd6016bee5798aef15cd2,0xdb1b762eec40584eb05,0xcf659c3b323655ac96d9,0xd6b52d4cda5eb46b6832,0xdcb7796e2adac5b2fb60,0xe66dca4b8d37102dfe5b,0x57766ed3dd6cba757422,0xede2bbc0] j))) else (if j<618 then (if j<515 then (page #[0xdeef9bdef3bd717a62f2,0xc14581e701adffabf917,0x961c0c32f854f090e0ef,0xb231546264c489884b0f,0xc7df8e8b1af632cc6078,0x764b3c92791cf229e421,0x8332e4658dca93945f27,0xcdd79ae733ae643cc479,0x2e7dccf679de33a7e71d,0x46b478e8add0f7a0bb40,0xd483a81b4e1697ed287a,0x66b83d67fac5b56dea8e,0xc7611ec0cd7d9af335d,0xd95bb25b63fec68d8a3b,0xded3bda37b3ef66decc4,0x8376fb6dd6db7fb6136a,0xdd25b9ef72dee4ddc6db,0xe6f05ddddbb5f7576e97,0xef37ce6f7cdea7bcf378,0xe0b9c0f380e6ffcdfcbb,0xe7105e1cbc317857708e,0x6878c5717ce2b9c4cf88,0xe45fc83f8f371d8e383c,0x7f2cfe54dca1b9337246,0x305b8630e1048bcc3f97,0xfc309942c09a170c6012,0x4e254282f0c2c70b5085,0x1424d2485e170c2c7144,0x87c20a142bc3e1034285,0xa142c15e1f082850b057,0xc20a0351840b05787c20,0x81a1428541bc3e1050b,0x88662821e1f08e15e1f,0x8414285b86c20a850a27,0x5785c30b050a160af0f,0x70883e9b88c3f0b86164,0xf8460883f118712f0f84,0x109b860d289e8a191370,0x6162a3786c20a850a27e,0x3784c30a054a150a70b8,0xfe1f09014e105786162e,0x85c3069c2c5506950321,0x9510bc3e1203a192a953,0x50cc5387c238582e0e2a,0x91c243a37860f38422b4,0xb942687e1237860f3028,0xc20a70c207e122386140,0x23868838382e30701511,0xa124c09070142107e14,0x87e170c9a60451785c3,0x401308e1f08240e38401,0x2090a0a89e1f08261e28,0xa1689c4b8625282787c,0x1f0826142a2787c20907,0x4160d9c34090d888889e,0xf84121814501405e178,0x74286c463e1c485030b7,0x83660d52113c30970822,0x10482c8c204c1fc30970,0x212e1044e05e106c5e4e,0xd13c209054a0f0470d1,0x2e18485050d70ca98527,0xc3430250a121b1790134,0x89e13c3e104c3c504f0,0x41b179034c8e1c2425c2,0xa37860f3e14a81b18278,0x20a237860f282891c243,0x9050403e0fc2e1c34dc,0x421f85c3469b848de185,0x80f2f0f848d09850a0f0,0x8f85c30a2349c3e12342,0xfe1f082a14069a2b140f,0x8240e385787c209064a1,0x1854240f3935901ce1f0,0x7e170c2a20206193c2e,0xc2e50e32385c30b0482,0xe1f08290d08960fc20af,0x3250e85113c36104c3c7,0xb0f84130f1c91c3e1050,0x6e1f0828130d943a14c4,0x8261e38582fc3e104c28,0x10502611387429892370,0x87e1437861c284013c3e,0x83c17203e0fc207078a,0x3e107a1a4e107a1a3e1f,0x832110b8e0fc20f0349c,0xe1874a110570a1bc30e1,0x408e1f0a1a1e2844100d,0xb0481c60b0385830a064,0x22017083c19185787c20,0xf041c50984815c10c943,0x8e1f0a1a12071c380a06,0x38140c8f84120c8c1e0,0x21f04321d18b02a12141,0x868782f0b82192c341c1,0xe170c387070b04170744,0xa08e170c3a7088401c09,0x7041c446f0c6230883e1,0xc2e1a51bc1080648110e,0x42e4080200e110783b1b,0x881f850de1870c0e06f0,0x820883c43c286f0c3a70,0x41140385] j) else (page #[0x642230803c1208e1a1f8,0x48441c08e170c388090,0x2430782385c346840c10,0x4848323048385830883a,0x1c3e14343c5038384030,0x341c12243786120e109,0xe18401213e170c386e1,0xd1a0e30441d12184424,0xe890e1a0e090c1e08e17,0x41c121844260e09102e0,0xe105032408f081c12243,0xf040278614e104500f,0x8391c20e01c1bc107182,0x4108c241107823850de1,0xf84123a37821d0d13871,0x107386193040120807f0,0x5c30e2782190e8c2207e,0x34206088401c09038178,0xe1b089a14283c11c2e1a,0x9a11293787c20a068a88,0xf0f844d0a03cbc3e1050,0xc226850a49e1f0826142,0x7061186073874d2e2387,0xb0e88934508870845088,0x501c6e1870443088c441,0xc270c382218582bc3e10,0x11c3e11342850d70c441,0x1f08287c470f844d0a17,0xc226f0c386080380a1ae,0x1c38607c1c3a1b202a0f,0x58478414204387c2894,0x841b0e943bc3e1070285,0x240a14e170c1e80e02b,0x1d187787c20e050a1007,0x8381b270822141f0836,0x30e1c1417e1860385e1f,0x31c30b9c22100701785c,0xe143411188c38080d708,0xc500060384e1f082e180,0x103dc00d8609c10705c6,0x70e70b8625305c00180e,0xc1008d3785c30e18238,0x446230570f84170c07,0x21a0b8c200e04f0c6250,0xf082838902b86180e178,0xc3838749c2e1c1c5040d,0xc38505517861b0e1439,0x30d14121b0e8c23c226f,0x9bc3e1048385a687037c,0x1888383e1f089a140794,0x60e386823c262f0c386e,0xb861c28441e05e105b8,0x81f0f844d0c070a11a4f,0x1408e170e0e1a3878341,0x1050749e170c38112844,0x870701787c20a068c1be,0x40323080380b49e1f082,0x31890200e26f0c625e08,0x3c1c0701785c340389bc,0x6f0c6230d06c44308024,0xbc3e106c347e08382e32,0x381207e170c388080380,0x881f841ce185cc11080,0x4616468607c246f0c3a4,0xc6902cc30c6349c10723,0xe47e105b878d385b8618,0x1331a50b70c208d20541,0xf047091bc307188fc20b,0xc3a42411f8416e1e34c0,0x886060ee08347c246f0,0x1a26103431c2e1884bc0,0x1237860e37091bc30e93,0xbc307181dc1468c1e08e,0x1b86c20a08480f047091,0x20a084848e1864a7c20a,0x828172f0f8414109187c,0x8208dc20a084848e1f0,0x1e38441c48e194f8414,0x778748203b861429f089,0x8e184028424074303088,0x385c307234c1d0f08c6c,0xf08c819e08744640782,0x46310877861e11943ac3,0x1050dc3e10504240e878,0xf0ec343040783b8621e,0x82825285817c208874a,0x40511bc2e1840e1ce1f,0x822728718a14e106ca0f,0x5238707e1044d07e10a3,0x48e10511a30e84446308,0x5061c0701c0a1ee170c3,0x12846910de1840bc30b8,0x841708858e180a427862,0x70f841d0d85ce0fa470f,0x8d07182348e184080fa4,0x11c2e187100f0470b86,0x20221bc30e901c050884,0x81ce18584040d434301d,0x4823c20a143dc209064,0x1283870bc346c1c4e40e,0x81c53e1f08301c306387,0xe1d2080ee114c91c30e1,0x8183c1d] j)) else (if j<721 then (page #[0x21b0e86081ce170c1a14,0x874a0f0470b868d07184,0x20e0460e10404691c2e1,0x91c30c7082250491787c,0x185c2850a03c3a110b16,0x802f0c29c208a01fc2e,0xc1c05a470f8414383c1c,0xe1840a070e704210d283,0xe11e1437861c2d20370d,0x8461e0783811c2e1c34,0xc2e1871008070907c30e,0xc39c30d141c050f07411,0x483c11c2e1a341c66286,0x1108038120702f0b861c,0x824192d2387c28a234a,0x492387c209038e08e1f,0x4050802491c3e111d010,0x181d050c52387c28a1c1,0x509058c1f6170c2a120b,0x85c30a8482c70ff09861,0x7f85c30a8482c60f811,0x4c0b143fc2e185424163,0xf87c2240482c60ff0824,0x8a9c3fc20af0c2416307,0x514469c200ea3f081bc3,0x8b48120c883416a470f8,0xc3141b820e0f8e8fc2e1,0x786150a094c160da3785,0xe187100ae18944440b01,0xfc3e1202210050240bc2,0x17861c384215050cd228,0x70278631285f121ee00,0xa0f0502013c31288ce10,0xf0a1a184078420de1894,0x20e8604260883c1408e1,0x1007e170e1a0e401f87c,0x3f08365e14503630b83c,0x480cc1787c28a1c380e2,0x583040af0c1a140b143b,0x20da20bc30c85c81ce18,0x1c2c106a240ea423787c,0x170e281a2837820e1290,0x9c2091c1fc20906488de,0xf841207205820c48989,0xe70f841240401e0804f,0xa18e1f0a2870a0401208,0x8481c70711c4a3075220,0x3e111c6050782387c286,0x628682f0f8514109413c,0x370824191d2051c2e1a3,0x7c28a1c3847e1883801e,0x23868da5981d48828638,0x20c8c1bc10709481a8a5,0xb140752387c20c184a1,0x3c541b141c5787c282c5,0x60d18401d1506f0f8514,0x70c3870770b862d20678,0x4e006c303070440fc20d,0x787c24a084a0ee170c5a,0x8c3430342f041c17221,0x90850c70f84943860322,0x6a50695e1f081a942839,0x3141f0f841d0c084a950,0xa1f841b2f0823141f082,0xf40710fc226844a08e1,0x207080240a0ee1f0828,0x470c1c90782387c22685,0x14082024110803c13c20,0x7860e4038100507f0f84,0x868423090441e08e113,0xa0e303c1016e170e1a6e,0x82dc307a01e08e170d1,0xe12360e1c28380e0508f,0x5a0de084c385110785c3,0x12342260761f85c31694,0x13e1237860f3d238707e,0x50a9486c2f861328440e,0xe1437860f384e09c386a,0x548e1a37841130440e13,0x850a1f0e708288d08982,0x7a470b868d387c1fc246,0x8bc2080710e1a383c220,0x10508928470c301c2c22,0xe503f0a11c30794241ce,0x5119c21013841ce18502,0x70200a1ce1f08281040,0xb07e170c347838382e3,0x6928bc3e105034508038,0x4de1f08281a2f08288ca,0xc200f0402787c2090390,0x10928a85e1f0838870d1,0x38589f0e241d270c3887,0xa951bc3188c23c246f0c,0xc286f044e60491b87122,0x48aa3e1f08242720508f,0x2138f87c20e848425e1c,0x441f0c85b8612139b871,0x285b8455e1834a860906,0x7c246844f050b704321d,0x844fc32a084612078238,0x10e86480f0404b87c286,0x4321d182782190e920bc,0xc1a542f0] j) else (page #[0xb15785c342950dc22af0,0xbc2e1a14a85e1e14a830,0x70b86140d1037c20a0ca,0xc308141c05e1f08281a3,0x847c246f0c4e403f0a1b,0x70e10901b0d0609c30e0,0x1c05e1a1f841b370c908,0x9070a0f0470b868d0718,0x2446f0c2431223787c20,0x7385c30a05ca8d097082,0x30e86861007027863128,0x83907e1868f070705c7c,0xa190e18e185480e8970,0xbc34389c9c20d0878649,0x5ca1103f0a1bc30e189,0x3e1f08290d285b87c20a,0xc385047090e0de1874c2,0x270f850d13110fc286f0,0x7c286a1c1c50b7041c25,0x89460a03f0a1bc3071b8,0x7c445387c282860c0e43,0x82870702891c243f0c34,0xa70c1e8a44143a19e1f0,0xc346850a10070240bc20,0xc1449e121f8621352385,0xd101e08e170e1a14081,0x20807f0f85074237821d,0x943307e170c4e5080381,0x20ef0c2e706f083bc310,0xcbc2e18504240cb220fc,0x2f041c171c1f841de1a4,0xfc10c884607e1437861c,0x86460f0470f850d83874,0x4a470f840d43874dc10e,0x7864843870a072406034,0x44143a19e170c2948387,0x507838200943f0b8648,0x1785c3139785c3468529,0x303e2440386f0c62343c,0x415c246f0c386e085c46,0xe10451a51086c3420204,0xc0f0470f848d089c8e1c,0x858e1103f0a1bc30e182,0x3c488041107c378421e1,0xf861c4691c2c5e08684a,0x89422070782385c3469,0xc8d07f0c2c5e1c1f848d,0x8602c446f0b86160c143,0x40f61f850de1870dc306,0x387c24686088d2470c38,0xe1f08280f403b841b0a1,0x3890bf0c385080381205,0x10200e0481787c20a1c2,0x6e1070290d207386170b,0xa1a11387387c20684028,0x470b870d383c1014e1f0,0x15e170c1c4d30400e0f0,0x4200902f082bc307a035,0x883c1408e170c9a10404,0xc1f20662b45e1f0a2860,0x2029c3e143422704f041,0x20741c6130903c364078,0x204890789c6120741c61,0x120709121c108c2a1078,0x708240e11201c20e0204,0x1c38483c423090384120,0x10389a30384c92311070,0x44942838c0a249141e41,0x44200d185c1c20983c1,0x4d10c4200d24902c101,0x381a21103c1c324042,0x81a20b0381b09203b1a2,0xa4287060e0f881c0d103,0x14619428582e40d89441,0xa44c14822050a061a070,0xa06890707c6190808320,0x50d038a1a0507060e028,0xe0a851068260e1888140,0x808882411070c3448070,0x3c6130781c2242284444,0x24110c321d1074212070,0x40338d212821908085c,0x248184c1e2848643a30a,0x380a1c18380a3118c42,0xc3090381030983c0e112,0x868541c31409c4] j))))
def ecH10 := page #[0xaa04010178e0e0000100,0x9540a2e003020214b820,0xda0b3cdc00e261c36137,0xc33f1f529aed00073a28,0x157101262a331c147601,0x7d5cb8b352d6b80a0447,0xb3838f321f2896dd5b28,0x3d790a6035d33e424125,0x23906703f36c5059467,0xf56932258bddc4b5da05,0x3b508e45f59b0c34fc66,0xe6e114e3142f642c631,0x72300d31a309000a2d00,0x941a070000006628a8,0x8c1ec36000000000c350,0xea7d64a4c53c251b0ee6,0xd55465b0f83789e957,0xc4dddf00000011ba4e0,0x5ea48000930a1700,0x6174342a31185ae00f70,0xa1886f63400014a0,0x620303e54b4900000000,0x86ad12000853,0x2a1d0009408e655f0000,0x36900000000091300052,0x2d7192782b000dbb606,0x6c8aa2e00000051982c0,918657]
def ecD11 (j : Nat) : Nat := (if j<206 then (if j<103 then (page #[0x94186fbb2630dfe64061,0xdf7a4c619fecc0c37bd,0xcc81077bd942067fd303,0x20efdb2441dfd64483bf,0xbf65883bbeca9077bd94,0xa9077f69120ebfb2e41d,0xaff320435bfa5883bbf4,0x65086beec990d7f59121,0x37de9321afed22435ef,0x7b2918dbfe5981b7e4b3,0xb31b7ecb6635fd9794ef,0x7fd980c6ffb2a18dbfa5,0x2c29dff64453bff4c063,0x1bff4c0a77fd9814effb,0xd98186ffb2630fbf58c6,0x31fbfe1861bff4c0c37f,0xff4c0c77fd9818effb2a,0x8206ffb2640ffd60481b,0xdff64483feec19077fe9,0x4c1077fd9620effb2a41,0x1affb26437bf61886bff,0x758d31bfe4c2637fe982,0x2637fd954c7feb0298ff,0xfbcc698dff66131bfecb,0x5531bff4c263ff6814c7,0x77ff984c6fff2c98dffe,0xb2ca9ff760d53bfe4c2a,0x53fef41aa77fd9854eff,0xff9654efff22a9dffa61,0xb0ffd60561bffcc2a77,0xbfe4c2c77fe98586ffb3,0x9858fdfb0cb1ff760d63,0x1fbfa1963fef41ac77fd,0xfcaac77ff9158effd30b,0x607df92cc0dffe6163bf,0xffe1981ffbc0b03bfd86,0xb3037ff96606fff26c0e,0xefff22c1ff7e0d83f7fc,0xe1986bffcb3077ff9560,0x637ff9361afff22c37bf,0xfb2b18dff64e31ffac0c,0xe53bff4c4637fd988c6f,0x7fd9594effb2329ff760,0x3129dff66253bfecb4a7,0x1ffac0cc3efd63986ffd,0xe98986ffb3130dff64e6,0x31ff760e63f7fc34c37f,0xfecb4c77fd9598effb23,0x3a06ffd3131dff66263b,0xffde0681bfecc5037fd9,0xcb5077fd95a0effb2341,0x1bfbf0741dff66283bfe,0xfe1a86bfecc50d7fd93a,0x6637fd95cc7fbac798fb,0xffd3198dff66331bfecb,0x6361bfecc6c37fd93d86,0x77fd95d8fdfb0db1dffa,0xb0dc0dffa6363bfecc6c,0x81bfecb7037fd93e077f,0xfd95e0effb23c1effe1b,0x7c35ff64786bfecb7077,0xffec30a7ffd850c6ffb2,0x83187ffaa630fffa1853,0xfffa1463ffec28c7ffd,0xea8a63ffc854c7ffaa64,0x4c7ffac698fff54d31ff,0xff60d31ffec0a63ffd65,0xaa63ffd864c7ffb0a98f,0x7ffb3098fff65931ffec,0xa5531fff42a63ffe654c,0x63fff514c7ffd3098fff,0xff0698fffe0531fffa9a,0x953fffc3263fff854c7f,0xffc9654fff922a9fff21,0x6a9fff58d53ffe4c2a7,0x3ffec8aa7ffd8654fffb,0xe8654fffb30a9fff6595,0xa9fffa5953fff48aa7ff,0xffc1aa7fff6354fffd30,0x654ffff22a9fffe1953f,0xfff14d61fffcc2a7fff9,0xc1ac3ffd53587ff906b0,0x87ffd06b0fff94d61ffe,0xf25563ffe42ac7fff835,0xac7ffd6558fff930b1ff,0xffb0cb1fff61563ffec1,0x6163ffecaac7ffd9158f,0x7ffe8558fffccab1fff6,0xf06b1fffa6163fff4aac,0x63fffc32c7fff8558fff,0xff9858ffff2ab1fffe45,0x6c0fff20d81ffe29b03f,0xffeb1b03ffd53607ff92,0x93607ffb0cc0fff60d81,0xfff94d81ffecb303ffd,0xf49b03ffe83607ffcc6c,0x607fff06c0fffe0581ff,0xffe5981fffc9b03fff86,0x8b07ffd8660fffb0ac1f,0xfffb2cc1fff65583ffec,0xa4583fff43307ffe8560,0xdffe9660fffd2ac1fff,0x86ffec8b] j) else (page #[0xfd538c7ffd26c37ff64d,0x718fff61631ffec1c63f,0xffeb2ca7fff858c7fff0,0x8694fffb0d29fff61653,0xfff54e61fffb2ca7ffe,0xec2cc7fff83987ffb073,0x98fffccb31fff61a63ff,0xff60e81ffea9d03ffe85,0x2d07ffd86a0ffff0740f,0x7ffacb98fffa1a83fff4,0x61b31ffec2e63ffd81cc,0x63ffe85cc7ffccb98fff,0xfaa7b0fff14f61fffa8e,0xf61fff29ec3ffd83d87f,0xffd85d8fffb07b1fffa0,0xc7c0fff54f81fff42ec7,0x6fff48f07ffd91e0fffa,0xaf00f400f40007ff6478,0xd8018302bc04a407600,0xc0ae4142024f04340794,0xcf07440dd41a4031305c,0x254048308ac10841fe03,0xc15c42a2051709d41314,0xbf0cf418f430005d30b4,0x3ec07a30ebc1ca437a06,0xc2344452087710942054,0xf13a426544ac092b11f,0x5880acb153c29c45220a,0xc31e46160be717342d34,0xc71b1435346840cdb194,0x7a00f031d6c39a47120d,0xc42e483a101f1f843dd4,0x6f243447148c4112b21f,0x9d81353261c4b6495212,0xc53a4a56147728644ff4,0x472c045714acc156b2a5,0xbbc17432dfc5ac4b3e16,0xc6224c2a18272fd45eb4,0x733a46674cac1913318,0xd941af3358c6a24d261a,0xc70e4e021bc737246d54,0x8f3a947434e701ca338d,0xf601e833c8c7864eee1d,0xc7f44fca1f573e347bb4,0x3f41f4831504c204b400,0x12c221b43cc86a50be21,0xc8e051a222ff458489f5,0xd74924915521423f3476,0x30025db4afc950528a24,0xc9be536a26a74cd498d5,0x4f50449fd53e8279b4ec,0x4c4294b521ca38545228,0xcabc555a2a5f53f4a715,0x4757f4af355c02b3b561,0x6ac2d1b59ccb3056462c,0xcb9a57162df75b74b615,0xa75ea4bc9577c2ebb5d2,0x858307b608cc0457ee2f,0xcc7a58d6316f6254c375,0x476604cb159443253643,0xa2c342367cccea59c233,0xcd685ab234f76964d215,0xf6dc4dab5b38363b6b9,0xc3038236fccdee5ba237,0xce5e5ca6390f71b4e255,0xd77504e955d183a03739,0xde83b9b76eced05d823a,0xcf365e4e3c5f7844eff5,0x177bd4f6d5ebc3d3b7a1,0xf9c3f0b7dacfa65f263e,0xd01060063fc77f34fd95,0xb782f504f608040ab80d,0x18842e3853d09a610e41,0xd10461ea439f86e50d16,0x878a951456268448b887,0xb09892102e1849e2da45,0x61661613120905c3c238,0x48170b0c24e2c26120b8,0xa098482e183e11c584c,0x1b8616415090514c3c23,0x3e1e1184858570c2ca2a,0x1216154307c23090b0a8,0x1f0f08c242c2a0e09866,0x890b0a83e1e118485854,0xf85861a5121607c20c2,0x1869448581c230f08c2a,0xa5151442c30d28a83e16,0x54530b0c34a2a2985861,0x40905c3c230a86e18590,0xb0c3482a0f85861a5151,0x130dc30b206e1e10c5b0,0x141f0f08a28240f84185,0x2c31330a03e161869452,0x4a1187841a2850a0d07c,0x68461e1091c1f08370c5,0xa1207c208c3253900a2,0x58c564c1225878410288,0x619861091814201f0b0c,0x2c8161309c3c2123058b,0xf0850c501226240b8586,0x9c96142e18b1c2414570,0xa2850a1cc3c2070d3144,0xa1187841] j)) else (if j<309 then (page #[0xe10a868a141f08370c54,0x841a28508c3c20d142e1,0x1091f0f08585450a2b87,0x7c2c315390028b0ae1e,0x22a240f85862c7271612,0xe18b1414581f0b0c54c4,0x28515c3c20d1428a8a06,0x5b0b0c544902b85861a,0x38889611861869c1c181,0x71e050a1912c3c22f48,0x221c151a26258586509,0x17a44428204b089f0c35,0xd1228a090884048ce1e1,0x262985861a24630c3c20,0xe61e10920505b0b0c54a,0x27c2c30d123850310468,0x61028411b87842470a08,0x201c18101458570f0851,0x8388840a14616198a024,0x9880a87111c4d25c3c24,0xe2a28120a2251858662,0x1e10a188848570f081ca,0x719c24dc3314828a8b6,0xb0f103585864ab090a08,0x5308a30c894100e36140,0x93616186a01c24147820,0x72726c2c30d412870513,0xc5962b87841a28516080,0xc24201c18101454530b0,0xc32150388848a6161981,0x642a2725071e0d1416c2,0xc0c4e4a22100a2c29858,0x6113e18698485b0f081c,0x1a8051415c2c31630d8a,0xb0cc160e141057846186,0x824ac903c241c2a361f0,0xd304838f04468a61619,0x24185861a8162d2cc2c3,0x170854530c58c4a322c4,0x3304128c8a8a6161869c,0x85861a70508118d14c2c,0x434b70f08b0a100e4e4d,0x4dc3c2143e18b0ae10a1,0xa4c9035878428808260e,0x8b1820170c870850c120,0xdc2c3164c2e10a8a61,0x8e6585862c8282108072,0x8785308c30c34c100a22,0xdc31338a09e186e1091,0xe263d85861a71c0a87c2,0xe10a1b08570c3450a610,0x44d88c3c212393441461,0x141210240e5187849201,0x28684a230c97081d044,0x153130489441461e10a2,0xf864f842460516c3c207,0x9464589c9b0b0c350120,0x30d38f0509e1e106891c,0x87841a28527071326c2c,0x10a14255709530e14c2b,0x80dc330c212384e1986,0xc34e151b87840e6060a,0xe198610a1828201f089f,0x2460515c3c2071630446,0x4530b0c34e2827861b84,0x1238ae1e1068a1494385,0x451864480820144dc3c2,0x941f0b0c8521210240f8,0xa8961e10a1c9c242048,0x861a715c3c207162930b,0x308370c58e221029844f,0xd2e10ae1868a14a0545,0xa0f845186447c20730c3,0x1c201c509f0b0c34e151,0x2c315318841346e1e10a,0x103d8461861a8168d07c,0x4201c8308370c5928e14,0xc31630ae161868a14a08,0x491844d861a81e87c20d,0x207a1f08370c58e0e1e1,0x20dc31638ae161868a14,0x4c2b1b8784286281514c,0x68a10a0545308370c58e,0x9151914c2c325461618,0x5900a2d0e6185862a705,0x61869c20146e1c870b0c,0x58dc3c21430b870a8a61,0xc1e2b851b8628267181,0x461a68a1458530b0e208,0xe8090c0bc2c312283e14,0x3450e171036291387845,0x61c6a40a143d20570b0e,0x3cb0c0b8dc2c3121c3e1,0x403a282512161b878426,0xde1e1090f18344c48388,0x45e71207c20d1e243040,0x344838bca1e10241b878,0x2fc2c36e1090a089028,0x615120e89490f48871e3,0xf084878c2d8625845440,0xe2f28906871210644f0,0x4d4258784905e50d1412,0x84530b0c] j) else (page #[0xe1e1090f1c492624bc78,0x1c748c3c2121928c8586,0xf084878e281187841a24,0x461e10689071c2c206f0,0x43cc4814c3c2121b3052,0x3a1e1d1292902429878,0x3920704a230f08345144,0x118605a6e1e10a0d1e48,0x8a1186509a364454dc33,0x3e10f24291508302f0c8,0x14113128807848904618,0xa8a3d0e2d85865090807,0x883848684f0b0c711110,0x4113120d08a6e1618e18,0x870e2c37849b86506151,0x126e18e14302d370f084,0xa3c70a451ac31131308e,0xc206cc4c0e103587849,0x8403a2851461989d142b,0x3412364440f0e4dc3312,0x693146828201f0c7088e,0xaa47c2c38d272e1e1244,0xc4428222c1e908f85871,0x61c6931851230f0a3498,0x64807c2c38d2632403e1,0xf085084c144f87851a4c,0x2348413e1909194342f0,0xa3a8240a420b270dc31e,0x5044ace221e100f85861,0x438ae161981c48241f08,0x4260907c2c316213448f,0xf08746c84c25843a1b86,0x38b0a0ee1e10d909c230,0xf864281107c248c30d1d,0x5f086c74f123d0e2b844,0x4253e1e10a10902d230c,0x8784284a7070927c3c21,0x4241f0f085084c120e4f,0x8c12123292838690119,0xa423a1586120e3c46827,0x14b0962480530f092049,0x6a38ae161929c983924,0x298784d05c3c2473028b,0xa4512924a3c1c910a38,0xa61179c781c370b0cc0c,0xc3c230162f3442402e18,0x3b0c94c281a241c5e50d,0xe240961e10a385834a4,0x7302930724829612c490,0x900e0b87845e70dc3c24,0x71835201f0f0838bcf10,0xc215141640a8a6161868,0xf87842a1a2861f0e12c3,0x9294381478530b0cc0e3,0x726c2c3141550560868c,0x8428542c5e6894985452,0xa089890504b0844bcb87,0x49028a1614c2112b28a8,0x6c98a4f12928a4c43878,0xa426e1e10a089f085124,0x224c40b45c3c2141b305,0x9460370b0c5884c2984,0xc7c2c3162120a61618b1,0x85044e1f0411871a163,0x4382e161981c2e230e37,0x2650b05c3c2143030a8f,0x41f08307080f1b878428,0x30603c2e1618a8d1e0c2,0xb862834507c216c32028,0x89260e1f09343070d849,0xd263910a078b09e1e146,0x8784244e6148848c3c28,0xb1094570b0e1cc0a1413,0x48c3c20d871d303e1618,0x370f0849011858628425,0x2461e1468a188870504e,0x862c4078dc3c212152c4,0x8870b0d20515100e5185,0x3e161a6931c9e2525149,0xf0807c3c20d263c4140,0x85191187841a0e1c5e7,0x24543c3925201498c30f,0x140b4403e1618c0695a6,0x86262880748c3c20d263,0x1c370cc4b12924c4385,0xc328295e1e1244690182,0xa0d842912365e51b8dc2,0xe1618b101c241f0b0c80,0x349c214118d262a41403,0x5904e3c2b0e2d851b86,0x10a1420847a1e370b0d2,0xc20d14273070403c2e1e,0xa3e8b87842a282c707c3,0xae18a0b9b0d37084854,1761] j)))
def ecH11 (j : Nat) : Nat := (if j<103 then (page #[0x4086ac0048100020c301,0x90c0c200668c1801,0x400285005548a1c,0x2810204f2a0400086020,0x8018009030408088040d,0x312381072238182146c0,0x2207ab02043010004e0,0x408d8100240800a08b03,0x80141600e8426207020,0x870c001c58d000c1092e,0x320c78d080024091020,0x2702c4009c0c0800030,0xc08108180830200b40c7,0xa2cf9a0a2cb8902529c,0x23468c1a0000e0038006,0xa20068f3a30eec10b0,0x4fe0ec06e800404a030a,0x86c2902e3b2b5ba0c1b9,0x72e800064000001,0x84000127c24579887000,0xc2740000c,0x825e2a98000d23a0000,0x5cc164000348c0000000,0x112752ea0001c5860,0x3009307200018174,0x5300000953c9408cc000,0x624cb19d63b6c2858,0xa65586bcd0f200018664,0x5f00000001cec096fe3f,0x4a28000000001048d0d8,0x400030e280004c3d433d,0x82019246c52dc1256745,0x45ce85a40740498028e1,0xa0003ceea0fbf3e8e13d,0x2fd8a540c400010d4b81,0x529b93d3aca44972e02a,0xc1120a1a03584aaa468,0xd1c562f907c2a04000,0xc53e1c3f093c66cc4280,0xc6370000198d803c46a9,0x8b5a3723e4000623101b,0x3df0acb1,0xb80f2c1df80b23a4c2fc,0xa3fdc97f12de46,0x804f9800000003800000,0xb2470a7bd880b29358e5,0x402c4348374ebc836f21,0x11940000426cce3f9,0x400010dd1a46000082a4,0x4e0000d0ec449d8f0248,547049,0x4c52fc3e80000000c630,0x340000a944000000029f,0x71aa5700018964c38cc,0x38eb0000000081ec,0x160406a28ec922c4eb09,0x4e0d0dd5969697f0c851,0x5e84381a094800018392,0x1606690d7d76117,0xc25dc5082fed55329280,0x3813f9ea0001e87e,0x1fe962a4462372152000,0x105506e311ed6738d6f1,0x830d8ce229390000a960,0x47602c000000041333b1,0xc59b00f1ac123baac97a,0x3ecfb89600014920,0x308b09269341b8c8f000,0x8733a2ec3cc622303f14,0xe81510dd620186223b1,0x680000000261948a0000,0x4149a010d21e9,0xb48a000000000000d1e4,0x41930231b706df50c534,0x112e616421de234c3699,0xc8488e62ea4a5339885a,0x41a7455c87790b6147,0x4947f8e096c400000,0x31cc00000000,0x62c0de00000001222518,0x23800091120001855e0,0x1a267518785900000000,0xf000000006155000,0x4d74984f030e0e561c00,0x6977878c249634e0003,0x37822a0001a47087c915,0x520e161000102b186d39,0x1080a652000172b0,0xc4e3920001d04120b000,0x10371930000a88400038,0xe057a4b9820f00000001,0xf8000153da01f0000a18,0x980000b3f052804,0xa4162852f8920001646c,0x1fb345735391b0000915,0x88000080c0000000050,0x5e76c000000000000001,0xb28c00018f4f36,0x510508af0ee00,0x29a8ec80d180,0x8c291a767480d8000000,0x632c0f339ac000181520,0xa22f82ab] j) else (if j<206 then (page #[0x7a0e22e4f6e910c0000,0x18dcd7fe230000926000,0xc13c85ebc50c0634b34d,0xd19000008df84ab,0x5604f4f907020607b000,0x53ab059b4e690d26aaa8,0x40000b46600010fde151,0x6a451028697b91096b64,0x30ebc833c4180000001e,0x8000a49dc22909e00c6,0x2084755ea2da000103,0x43c320b6cf2b93a00000,0x79740000987764188d7,0x7e1c3838730000245349,0xe0ee000000014af0c486,0xc2142342a0001b268886,0x20400055d4000150010d,0x323c0002f14c8fe59646,0x8a033a37d57e98b8a4d2,0x6f40bf3a131252000289,0x4870000715de2a82,0x57854b020f2f4295ed59,0x92eac780007402a61f6d,0x112211a60001a,0x57c33000088980000000,0x2466906ce458f22600,0x1376663e4ca8000707e0,0xd00004966029b0bdb808,0x8018000000142f524,0x531200020a340e7fbc20,0x5717dc046219d4b2b94d,0xe201120568200317847,0x1a32de2980000001c,0x504ab0860001c87d9b9,0x520b284400,0xbaae515bd0bb9f518840,0x13a2450cd68e1851243c,0x20b56e15b0d600008e,0xcaba67034a6798600000,0x800061aa9642cf3f005,0x2e9611790001278af0,0xa8072033d26800000000,0xb000000000003cb1f8c2,0xa311a6c38d,0x98d00000000589500000,0x80e130001886400054d3,0x9804b480005029622d44,0xc87a04fc688000b0d1c,0xa61ed890306394dba16e,0x57d50f000073a896d444,0xb3bd098790900008,0x7782cc46868778ff2801,0x2df0f7e227f32e000182,0xc27e88508e571124cb36,0xd3cbc726aa7cac5a6207,0x48609b0000400dc42e03,0x148dc89f60e833c64,0xd20eb38cda5ac000792b,0xf48e9f021fadae7f30e,0xa96ee28c23af1ec2,0xe189f72ce0000000387f,0x87069f9f11de3d607,0x1330c7cc000423be4240,0x21960c473c244000425e,0x7ec08cc82e4194000126,0x38ce0a3012e4fb62197,0x31223a1a00003d22b23d,0x180e515ad804a6ae42,0x798f43f4691581161f40,0x3509d0a5502fabebdb0,0x7fc0bb125c0001021000,0x20482054c83254922d9c,0x12295c504359ca201c8,0x1d0519197c136915a50d,0x41be28f2462c14a00010,0x6e0f6ae800028b2589c,0x5700003842f00463670f,0x89a2d7eb3962,0xf4c2c0000000000069ce,0x22bcc28000000185df82,0x33dc7a04bc000050ca9,0x549d113258628000684d,0x7e80001826e2e000036b,0x1630c000000050aea,0x2387998a8f0940000000,0x5c4432485b517195e908,0x42c400028d1d2520000d,0x779bcb3ec00bc00059b5,0x1300000000a01b2647c5,0x295ae4b0c14de1f63356,0x2041a54df1b0000,0x7412000000,0x232d76d085e04f900000,0x713260340000000399f,0x409a2247c6b000,0x1e0acaa3f49000000,0x98000b405c4e00006cd5,0x8c8000000000000000c8,0xc177e54000040c1747f7,0x22400000277c0005055,0x3832000021a800,0x1b8ad3128000833a0,0x7cf58000] j) else (page #[0x14d4b424049d00001a39,0x180b913bf2,0x80e8000c16a000072d0,0x8aa01d516e44f649e000,0x12e000000028f8800080,0x1870d8300b0200010e79,0xb600028956d463af8610,0x1e453ee00018f701b352,0xd3bdb97b474e] j)))
def ecD12 := page #[0xffc63ffc61ffc53ffc31,0xffd31ffc86ffc83ffc81,0xffd81ffd63ffd61ffd53,0xffe53ffe31ffd86ffd83,0xffe83ffe81ffe63ffe61,0xfff63fff61fff31ffe86,0x1b000fff86fff83fff81,0x1c532c5808e0e616e1cc,0xd600b455126c488870fa,0x451ce224157b0e89b9b3,0x4c3c28634f54a874d19,0x291214a12110e1074141,0x431a6101cb1324161431,0x20395290a18d388281e1,0x34e244052458ac3841d2,0x724361c23080e54a4286,0x28634a242880f0e11840,0xd8708a2038d8708a203c,0x330910143948708e2038,0x987850c6984072c3614,0xc69c4852848443841d02,0x28361c20e6101c992850,0x841d020393250a18d388,0x396850c6984880a50943,0x1431a610506c3841cc20,0x1204160f0a18d3080e5a,0xe561c2496101ca941b0e,0x95283614341412202960,180739]
def ecH12 := page #[0x124053c000100030602,0x6000c0600010402,0xd4b060f07010f000b00,0x131b2e000001180e2c,0x4a2d0018256305152301,0x113f0b01049e110e0006,0x100000a3402000f0a,0x2360f106000f804,0x171302083e0335070545,0x80208610127032d04,0x477a8fc3030206092200,0x8f1098a90001830c8b6,0x622650ea2bd4ac149f9d,0xfbcba9e344d8ec000126,0x2ac89d33fb1a508a074,0x6bcad8a76eaa0003c630,0x926bc69c05070e23,0xeb71010d20003075000,0xc0d210251930251e941c,0x4e033635208c4a8015b6,0x60fd30800034f10002ea,0x3d3c36438212fa2a8000,0x54c8f000000000000005,0x284c329dc5adc7407d72,0xaa800002b20000000a11,0xc55000328eebd1,0xfa2d0e4782f7493a4c40,0x1c6f321b046040e8e,0xbc3ca334100f57324e02,0x364620003f0200033153,0x1ca210d7c07b0ac070f2,0xc8e412c8bddc39000,0x30000151c00000000000,0x36278000e45000000015,0x98f0d1253b8cb1000080,0x3aefdc8e48362fbb31,0xc09c0009417c3b4,0x73132a1a90b90c400000,0x732244fd35d03dd39,0x721c0003acd6917c80,0xb00020d69079eab00000,0xd2208b814ba410e25ba3,0x1cd8052b2aae2ac30000,0x98811a336c5bb03c0004,0x1891832d043e40089de3,0x4b9415c533112b00440a,0x9c22af4c764082740001,0x91357e55c911cdf00034,0x33286e69b5b83841ee70,0x1cf2aae94e3dab8000,0x9e6cb41f8000e084a040,0x20f7e1c88f3000304194,0x8ed427cfb31e98f8231,0xa62bec8f6a1989268b44,0xbc4b4a00000c6a00014,0x62e9f240000000000000,0x9c8000784f0686897461,0x12a000045910828582,0xa49690c2297c6e00,0x8b0000000fcbeea3000,0xec5c0002819490c1b4,0x300014fc626c00000000,0x40349167a8b09293e785,0x25d524c42a43eac4204b,0x4c000c4466ece06971c0,0x21224e800018db90,0xf16f3f5c710002caf000,0x120c7a852abe645d34ac,0xcc134000e8fa0e7f8468,0xe18046b1095864000202,0x150cd8413800041d8a00,0x9380e00b80063008c0b2,0xd216231ac1714d2d19c3,0xc1b01fc41510f38c3b48,0xdcac96424017f2e7794a,0xf219dcb5e2b24a1c976a,0x134c00043534e28c6189,0x4199186950ead8379d1b,0x422d5d4a1321a1b34809,0x5449b058000a1e70b624,0x30ab251c8c00014e1031,0xcc7cb0000d43cd1a7ae3,0x6c407c5e130747c0000c,0x80999214c4400093fbeb,0xd000002c10d180656bb,0x9000000000dd6adc000a,0xe82f23646ed20b6447d8,0xd1500026febcaca9602e,0x17d2c8322299c00052ce,0xad0a88320cab8d023c31,0x434000d115cbc33ffc8,0x34650000037,0x9b6d7a0734e9b3080000,0x48160a693208073266a,0x922807c70f4b77c1d41e,0x7b86808a060c3343eb,0xe6373c82533a0bfd2140,0xfcbb85cf482d1d285050,0x3b49290002c519007898,0x6d3d0272d4e,0xa4b790e80009bd951f00,0x385004b54a482b]
def ecD13 (j : Nat) : Nat := (if j%103=0 then 3180031 else 0)
def ecH13 := page #[0x1560000000010,476053504,0x53000e4400f200016000,0x5022310c00,0xd96b3000000000000000,992,0,0xa4800610cf75c00,0x15adc0000000,0,693,0x5a800b9c00002ef0018e,0x141001d900000,0x5b00000309ee400f4000,0xb8d000000000002c00,0xc4e6e05000bc400,0,810549514,0x287c680000000]
def ecLevels : Nat → Packing
  | 9 => (114,4,6,0,0,12,0,ecD9)
  | 10 => (609,3,6,0,0,15,0,ecD10)
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
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem ecChunk10_0 : block ec 10 0 121 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem ecChunk10_1 : block ec 10 121 122 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem ecChunk10_2 : block ec 10 243 122 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem ecChunk10_3 : block ec 10 365 122 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem ecChunk10_4 : block ec 10 487 122 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem ecChunk11_0 : block ec 11 0 103 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem ecChunk11_1 : block ec 11 103 103 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem ecChunk11_2 : block ec 11 206 103 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem ecT : checkedTables ec 13 := by
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
  · rfl
  · decide +kernel
  · exact (@block_merge ec 10 0 487 122 (@block_merge ec 10 0 243 244 (@block_merge ec 10 0 121 122 ecChunk10_0 ecChunk10_1) (@block_merge ec 10 243 122 122 ecChunk10_2 ecChunk10_3)) ecChunk10_4)
  · exact (@block_merge ec 11 0 206 103 (@block_merge ec 11 0 103 103 ecChunk11_0 ecChunk11_1) ecChunk11_2)
  · decide +kernel
  · decide +kernel
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

theorem nineMonotone : Lower false inputs graph 16 := by
  intro k bank path hit
  obtain ⟨j,S,hj,run,raw⟩ := reach_live graph_proper (by decide +kernel) (by decide +kernel) path hit
  rw [orbitAllInputs run raw] at run
  by_contra! small
  exact monoRoot j (by omega) run
namespace Extended
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

def plainWord (a : Sig) : Bool := !(bit 0 a)
theorem nrm_map {u} {w : List Sig} (h : w.all plainWord=true) : w.map (nrm u)=w := by
  have e : w.map (nrm u) = w.map id := by
    apply List.map_congr_left
    intro a ha
    exact nrm_id (by simpa [plainWord] using List.all_eq_true.mp h a ha)
  rw [e,List.map_id]
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

def pins : List Sig := [(stripe4813 512),(stripe4813 128),(stripe4813 32),(stripe4813 256),(stripe4813 64),(stripe4813 16),(stripe4813 4),(stripe4813 1),(stripe4813 8),(stripe4813 2)]
def initial : List Sig := pins
def target : Sig := (word [0xffffffffffffffff,0xffffffffffffffffffff,0xffffffffffffffffffff,0xffffffc8ffffffffffff,0xffffffffffffffffffff,0xffffffffffffffffffff,0xfaeafffff8c8ffffffff,0xfffffffffffffffffffa,0xfff8ffffffffffffffff,0xffffffffffeaffc8ffff,0xfffffffefcfcffffffff,0xfffaf8f8ffeefeeeffee,0xfcccffeafaeaffeaf8c8])
def assign (r : Row) (j : Fin 10) := bit r (pins.getD j.val zero)
def f10 (x9 : Fin 10 → Bool) := (x9 (0 : Fin (10 : ℕ)) && x9 (1 : Fin (10 : ℕ)) || x9 (1 : Fin (10 : ℕ)) && x9 (2 : Fin (10 : ℕ)) || x9 (2 : Fin (10 : ℕ)) && x9 (3 : Fin (10 : ℕ)) || x9 (3 : Fin (10 : ℕ)) && x9 (4 : Fin (10 : ℕ)) || x9 (4 : Fin (10 : ℕ)) && x9 (0 : Fin (10 : ℕ)) || x9 (0 : Fin (10 : ℕ)) && x9 (5 : Fin (10 : ℕ)) || x9 (1 : Fin (10 : ℕ)) && x9 (6 : Fin (10 : ℕ)) || x9 (2 : Fin (10 : ℕ)) && x9 (7 : Fin (10 : ℕ)) || x9 (3 : Fin (10 : ℕ)) && x9 (8 : Fin (10 : ℕ)) || x9 (4 : Fin (10 : ℕ)) && x9 (9 : Fin (10 : ℕ)) || x9 (5 : Fin (10 : ℕ)) && x9 (7 : Fin (10 : ℕ)) || x9 (7 : Fin (10 : ℕ)) && x9 (9 : Fin (10 : ℕ)) || x9 (9 : Fin (10 : ℕ)) && x9 (6 : Fin (10 : ℕ)) || x9 (6 : Fin (10 : ℕ)) && x9 (8 : Fin (10 : ℕ)) || x9 (8 : Fin (10 : ℕ)) && x9 (5 : Fin (10 : ℕ)))
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem rowTarget : ∀ r : Row, bit r target = f10 (assign r) := by decide +kernel

end Extended
theorem nineFloor : Lower true inputs graph 15 := by
  intro k bank path hit
  have plain : plainWord graph = true := by decide +kernel
  have init : inputs.all plainWord = true := by decide +kernel
  obtain ⟨j,S,hj,run,raw⟩ := reach_live graph_proper plain init path hit
  rw [orbitAllInputs run raw] at run
  by_contra! small
  exact rootSImpossible j (by omega) run

end PEqualNP.Outside.L_meta_4813_aux.Certificate

namespace PEqualNP.Outside.L_meta_4813_aux.Bound
open PEqualNP.Outside.L_meta_4813_aux.Certificate
def pin (i : Fin 10) := Extended.initial.getD i.val Extended.zero
def idxData : Array Nat := #[9,7,5,8,6,4,2,0,3,1,7,9,6,8,5,2,4,1,3,0,5,7,9,6,8,0,2,4,1,3,8,3,4,9,6,5,2,0,7,1,7,2,3,4,9,5,1,8,0,6,7,5,8,3,2,9,0,6,4,1,1,6,8,5,0,2,9,3,7,4,8,3,4,0,5,6,2,9,1,7,3,8,5,7,2,4,6,0,9,1,5,8,3,2,7,0,6,4,1,9]
def morphIndex (i x : Nat) : Nat :=
  match i with
  | 0 => (x &&& 511)
  | 1 => ((x &&& 132) <<< 2) ||| ((x &&& 66) >>> 1) ||| (x &&& 264) ||| ((x &&& 33) <<< 1) ||| ((x &&& 16) >>> 2)
  | 2 => ((x &&& 33) <<< 4) ||| (x &&& 132) ||| ((x &&& 66) <<< 2) ||| ((x &&& 264) >>> 2) ||| ((x &&& 16) >>> 4)
  | 3 => ((x &&& 272) <<< 1) ||| ((x &&& 8) <<< 4) ||| (x &&& 71) ||| ((x &&& 32) >>> 1) ||| ((x &&& 128) >>> 4)
  | 4 => ((x &&& 136) <<< 2) ||| ((x &&& 4) <<< 5) ||| ((x &&& 16) <<< 4) ||| ((x &&& 32) >>> 1) ||| ((x &&& 2) <<< 1) ||| ((x &&& 256) >>> 8) ||| ((x &&& 1) <<< 3) ||| ((x &&& 64) >>> 5)
  | 5 => ((x &&& 161) <<< 2) ||| ((x &&& 256) >>> 3) ||| ((x &&& 8) <<< 5) ||| ((x &&& 4) <<< 4) ||| ((x &&& 64) >>> 6) ||| ((x &&& 16) >>> 1) ||| (x &&& 2)
  | 6 => ((x &&& 2) <<< 8) ||| ((x &&& 64) <<< 1) ||| ((x &&& 280) >>> 3) ||| ((x &&& 32) <<< 3) ||| ((x &&& 1) <<< 6) ||| ((x &&& 4) <<< 2) ||| ((x &&& 128) >>> 4)
  | 7 => ((x &&& 304) <<< 1) ||| ((x &&& 8) <<< 4) ||| ((x &&& 1) <<< 8) ||| ((x &&& 64) >>> 2) ||| (x &&& 4) ||| ((x &&& 2) <<< 2) ||| ((x &&& 128) >>> 6)
  | 8 => ((x &&& 8) <<< 6) ||| ((x &&& 256) >>> 1) ||| (x &&& 51) ||| ((x &&& 128) <<< 1) ||| ((x &&& 4) <<< 4) ||| ((x &&& 64) >>> 4)
  | _ => ((x &&& 33) <<< 4) ||| ((x &&& 384) >>> 1) ||| ((x &&& 10) <<< 2) ||| ((x &&& 4) <<< 6) ||| ((x &&& 80) >>> 4)
def witnessData : Array Nat := #[0,0,0,0,16,128,128,16,16,48,48,16,16,272,272,16,16,64,64,16,64,16,16,64,16,20,20,16,16,65,65,16,16,72,72,16,16,18,18,16,4,512,512,4,0,0,0,0,4,32,32,4,4,260,260,4,4,68,68,4,4,20,20,4,32,4,4,32,4,5,5,4,4,40,40,4,4,34,34,4,1,513,513,1,1,128,128,1,0,0,0,0,1,256,256,1,1,65,65,1,1,144,144,1,1,5,5,1,128,1,1,128,1,9,9,1,1,130,130,1,8,520,520,8,8,136,136,8,8,32,32,8,0,0,0,0,8,64,64,8,8,48,48,8,8,36,36,8,8,9,9,8,32,8,8,32,8,10,10,8,2,512,512,2,2,130,130,2,2,34,34,2,2,256,256,2,0,0,0,0,2,18,18,2,2,260,260,2,2,257,257,2,2,10,10,2,256,2,2,256,1,512,512,1,1,129,129,1,1,40,40,1,1,257,257,1,1,65,65,1,0,0,0,0,1,5,5,1,8,1,1,8,1,8,8,1,1,10,10,1,2,514,514,2,2,128,128,2,2,34,34,2,2,258,258,2,2,72,72,2,2,18,18,2,0,0,0,0,2,9,9,2,2,8,8,2,8,2,2,8,2,514,514,2,2,130,130,2,2,32,32,2,2,258,258,2,2,80,80,2,2,16,16,2,2,20,20,2,0,0,0,0,2,10,10,2,16,2,2,16,4,516,516,4,4,144,144,4,4,36,36,4,4,256,256,4,4,68,68,4,4,16,16,4,16,4,4,16,4,5,5,4,0,0,0,0,4,18,18,4,1,513,513,1,1,129,129,1,1,36,36,1,1,257,257,1,1,64,64,1,1,20,20,1,1,4,4,1,4,1,1,4,1,9,9,1,0,0,0,0]
def masks : Array Nat := #[512,128,32,256,64,16,4,1,8,2]
def morph (i : Fin 10) (r : Row) : Extended.Row := Fin.ofNat 1024 (morphIndex i.val r.val)
def dest (i j : Fin 10) := inputs.getD (idxData.getD (i.val*10+j.val) 9) zero
def separating (i j : Fin 10) (d : Fin 4) : Extended.Row × Extended.Row :=
  let r := witnessData.getD ((i.val*10+j.val)*4+d.val) 0
  (Fin.ofNat 1024 r, Fin.ofNat 1024 (r+masks.getD i.val 0))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem morphGoal0 : ∀ r : Row, Extended.bit (morph 0 r) Extended.target = bit r graph := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem morphGoal1 : ∀ r : Row, Extended.bit (morph 1 r) Extended.target = bit r graph := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem morphGoal2 : ∀ r : Row, Extended.bit (morph 2 r) Extended.target = bit r graph := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem morphGoal3 : ∀ r : Row, Extended.bit (morph 3 r) Extended.target = bit r graph := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem morphGoal4 : ∀ r : Row, Extended.bit (morph 4 r) Extended.target = bit r graph := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem morphGoal5 : ∀ r : Row, Extended.bit (morph 5 r) Extended.target = bit r graph := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem morphGoal6 : ∀ r : Row, Extended.bit (morph 6 r) Extended.target = bit r graph := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem morphGoal7 : ∀ r : Row, Extended.bit (morph 7 r) Extended.target = bit r graph := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem morphGoal8 : ∀ r : Row, Extended.bit (morph 8 r) Extended.target = bit r graph := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem morphGoal9 : ∀ r : Row, Extended.bit (morph 9 r) Extended.target = bit r graph := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem morphGoal : ∀ (i : Fin 10) (r : Row), Extended.bit (morph i r) Extended.target = bit r graph := by
  intro i
  fin_cases i <;> first | exact morphGoal0 | exact morphGoal1 | exact morphGoal2 | exact morphGoal3 | exact morphGoal4 | exact morphGoal5 | exact morphGoal6 | exact morphGoal7 | exact morphGoal8 | exact morphGoal9

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem morphPin0 : ∀ (j : Fin 10) (r : Row), Extended.bit (morph 0 r) (pin j) = bit r (dest 0 j) := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem morphPin1 : ∀ (j : Fin 10) (r : Row), Extended.bit (morph 1 r) (pin j) = bit r (dest 1 j) := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem morphPin2 : ∀ (j : Fin 10) (r : Row), Extended.bit (morph 2 r) (pin j) = bit r (dest 2 j) := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem morphPin3 : ∀ (j : Fin 10) (r : Row), Extended.bit (morph 3 r) (pin j) = bit r (dest 3 j) := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem morphPin4 : ∀ (j : Fin 10) (r : Row), Extended.bit (morph 4 r) (pin j) = bit r (dest 4 j) := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem morphPin5 : ∀ (j : Fin 10) (r : Row), Extended.bit (morph 5 r) (pin j) = bit r (dest 5 j) := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem morphPin6 : ∀ (j : Fin 10) (r : Row), Extended.bit (morph 6 r) (pin j) = bit r (dest 6 j) := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem morphPin7 : ∀ (j : Fin 10) (r : Row), Extended.bit (morph 7 r) (pin j) = bit r (dest 7 j) := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem morphPin8 : ∀ (j : Fin 10) (r : Row), Extended.bit (morph 8 r) (pin j) = bit r (dest 8 j) := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem morphPin9 : ∀ (j : Fin 10) (r : Row), Extended.bit (morph 9 r) (pin j) = bit r (dest 9 j) := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem morphPin : ∀ (i j : Fin 10) (r : Row), Extended.bit (morph i r) (pin j) = bit r (dest i j) := by
  intro i
  fin_cases i <;> first | exact morphPin0 | exact morphPin1 | exact morphPin2 | exact morphPin3 | exact morphPin4 | exact morphPin5 | exact morphPin6 | exact morphPin7 | exact morphPin8 | exact morphPin9

theorem destMem : ∀ (i j : Fin 10), dest i j = zero ∨ dest i j ∈ inputs := by decide +kernel
theorem destSelf : ∀ i : Fin 10, dest i i = zero := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem separates : ∀ (i j : Fin 10) (d : Fin 4), i ≠ j →
    let p := separating i j d
    Extended.bit p.1 Extended.target ≠ Extended.bit p.2 Extended.target ∧
    Extended.bit p.1 (Extended.bin d.val (pin i) (pin j)) = Extended.bit p.2 (Extended.bin d.val (pin i) (pin j)) ∧
    ∀ l : Fin 10, l ≠ i → Extended.bit p.1 (pin l) = Extended.bit p.2 (pin l) := by decide +kernel
theorem pinOfMem {w} (h : w ∈ Extended.initial) : ∃ j : Fin 10, pin j = w := by
  rw [show Extended.initial = List.ofFn pin by decide +kernel] at h
  exact List.mem_ofFn.mp h
theorem restrictPin (i j : Fin 10) :
    restrictRows (morph i) (Extended.observe (pin j)) = observe (dest i j) := funext (morphPin i j)
theorem restrictSelf (i : Fin 10) : Constant (restrictRows (morph i) (Extended.observe (pin i))) := by
  rw [restrictPin, destSelf]
  exact ⟨false, funext fun r => by simp [observe,bit,zero]⟩
theorem availPin {u : Bool} (i j : Fin 10) :
    Available u (inputs.map observe) (restrictRows (morph i) (Extended.observe (pin j))) := by
  rw [restrictPin]
  rcases destMem i j with h|h
  · rw [h]; exact Or.inr (Or.inl ⟨false, funext fun r => by simp [observe,bit,zero]⟩)
  · exact Or.inl (List.mem_map.mpr ⟨_,h,rfl⟩)
theorem binaryFloorOf {u : Bool} {L : Nat} (floor : Lower u inputs graph L) {k S} (run : Extended.Live u Extended.target k S) (raw : ∀ w ∈ S, w ∈ Extended.initial) :
    L+2 ≤ k := by
  classical
  cases k with
  | zero =>
    obtain ⟨eq,_⟩ := run
    have h := raw Extended.target (eq.symm ▸ Finset.mem_singleton_self _)
    exact False.elim ((by decide +kernel : Extended.target ∉ Extended.initial) h)
  | succ k =>
    obtain ⟨U,a,b,d,hd,rfl,_,_,hne,_,ht⟩ := run
    obtain ⟨i,rfl⟩ := pinOfMem (raw a (by simp))
    obtain ⟨j,rfl⟩ := pinOfMem (raw b (by simp))
    have hij : i ≠ j := by rintro rfl; exact hne rfl
    have hdl : d < 4 := by rcases hd with h|⟨_,h⟩ <;> omega
    let p := separating i j ⟨d,hdl⟩
    have wh := separates i j ⟨d,hdl⟩ hij
    obtain ⟨w,hw,hchange⟩ := Extended.live_row_difference ht wh.1
    have member : pin i ∈ U := by
      rcases Finset.mem_insert.mp hw with rfl|hu
      · exact False.elim (hchange wh.2.1)
      · obtain ⟨l,rfl⟩ := pinOfMem (raw w (by simp [hu]))
        by_cases he : l = i
        · simpa [he] using hu
        · exact False.elim (hchange (wh.2.2 l he))
    let V := insert (Extended.bin d (pin i) (pin j)) U
    have ha : pin i ∈ V := Finset.mem_insert_of_mem member
    let front := pin i :: (V.erase (pin i)).toList
    have nd : front.Nodup := List.nodup_cons.mpr ⟨by simp,Finset.nodup_toList _⟩
    have eqV : front.toFinset = V := by
      simp only [front,List.toFinset_cons,Finset.toList_toFinset,Finset.insert_erase ha]
    have hr := Extended.list_run ht front nd eqV
    have goalEq : restrictRows (morph i) (Extended.observe Extended.target) = observe graph := funext (morphGoal i)
    have supplyRoots : supply u (inputs.map observe) ((front.map Extended.observe).map (restrictRows (morph i))) := by
      intro z hz
      obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hz
      obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hm
      have hm : w ∈ V := eqV ▸ List.mem_toFinset.mpr hw
      rcases Finset.mem_insert.mp hm with rfl|hm
      · rw [Extended.obs_bin, restrict_comb]
        obtain ⟨op,x,y,eq,hx,hy,hcx,_⟩ := comb_prime (u:=u) (a:=restrictRows (morph i) (Extended.observe (pin i))) (b:=restrictRows (morph i) (Extended.observe (pin j))) hd (availPin i i) (availPin i j)
        rw [eq]
        apply from_constant op (Or.inl ?_) hx hy
        by_contra hn
        have hc := restrictSelf i
        simp only [cost, ite_eq_right hn, ite_eq_left hc] at hcx
        omega
      · obtain ⟨l,rfl⟩ := pinOfMem (raw w (by simp [hm]))
        exact availPin i l
    have need := projected_bound (morph i) hr (goalEq ▸ observe_proper graph_proper) Reach.start supplyRoots (L:=L) (goalEq ▸ floor)
    have charge : 1 ≤ mass ((front.map Extended.observe).map (restrictRows (morph i))) := by
      change 1 ≤ mass (restrictRows (morph i) (Extended.observe (pin i)) :: _)
      rw [mass_cons]
      simp only [cost, ite_eq_left (restrictSelf i)]
      omega
    omega
theorem binaryFloor {k S} (run : Extended.Live true Extended.target k S)
    (raw : ∀ w ∈ S, w ∈ Extended.initial) : 17 ≤ k := binaryFloorOf nineFloor run raw
end PEqualNP.Outside.L_meta_4813_aux.Bound
open PEqualNP.Outside.L_meta_4813_aux
namespace PEqualNP.Outside.L_meta_4813_aux.PetersenProductFloor
open PEqualNP.Outside.L_meta_4813_aux.Certificate
open PEqualNP.Outside.L_meta_4813_aux.Bound

def tap (i : Fin 3) : Sig :=
  let a := if i.val=2 then 4 else 0
  let b := if i.val=0 then 2 else 6
  inputs.getD a zero &&& inputs.getD b zero

def rep (i : Fin 3) := inputs ++ [tap i]
def projectedInputs (v : Fin 10) := inputs ++ [dest v 0 &&& dest v 2]
def swaps : List (List Nat) := [[], [81, 130, 118], [16, 82, 131, 100], [16, 32, 48, 128, 100, 80, 116], [32, 83, 116], [32, 49, 128, 81, 116, 100], [48, 33, 133, 118], [48, 129, 82], [80, 16, 33, 50, 116, 131, 100], [80, 129, 50, 116], [128, 49, 100], [128, 81, 32, 49, 100, 116]]
def moves (p : Fin 12) := ((swaps.getD p.val []).map swapRows)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem projectedMaps : ∀ v : Fin 10, v≠6 → ∃ j : Fin 3, ∃ p : Fin 12,
    checkMap (moves p) (projectedInputs v) graph (rep j) graph = true := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem easilyCut (i : Fin 3) (nonzero : i ≠ 0) : Impossible true graph 14 (rep i).toFinset := by
  have h (j : Fin 3) (hj : j ≠ 0) : Impossible true (graphGoal 511) 14 (rep j).toFinset := by
    apply cut_root (m:=511) (cap:=14) (before_sound known383 valid383) (64,0,447,0,13)
    · decide +kernel
    · revert hj j
      decide +kernel
  exact (show graphGoal 511 = graph by decide +kernel) ▸ h i nonzero

def neighbors : List Nat := [2, 1, 2, 4, 1, 1, 2, 4, 8, 2, 1, 2, 4, 1, 1, 2, 4, 8, 2, 1, 2, 4, 1, 1, 2, 4, 8]

def tests (i : Fin 3) : List (Sig × Row × Row) := List.ofFn fun j : Fin 9 =>
  let low := neighbors.getD (9*i.val+j.val) 0
  (inputs.getD j.val zero,Fin.ofNat 512 low,Fin.ofNat 512 (low+2^j.val))

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem testsOK : ∀ i : Fin 3, checkEssential graph (rep i) (tests i) = true ∧
    (tests i).map Prod.fst = inputs := by decide +kernel

theorem repFloor (i : Fin 3) (difficult : Impossible true graph 14 (rep 0).toFinset) :
    Lower true (rep i) graph 15 := by
  intro p bank path hit
  have ct : plainWord graph = true := by decide +kernel
  have rt : ∀ t : Fin 3, (rep t).all plainWord = true := by decide +kernel
  obtain ⟨k,S,hk,run,sub⟩ := reach_live graph_proper ct (rt i) path hit
  have pick : ∀ a ∈ inputs, a ∈ S := by
    intro a ha
    have member : a ∈ ((tests i).map Prod.fst).toFinset := by
      rw [(testsOK i).2]
      exact List.mem_toFinset.mpr ha
    obtain ⟨r,s,neq,iso⟩ := essential_ok (testsOK i).1 a member
    exact raw_required run (rep i) a sub r s neq iso
  by_contra! small
  by_cases used : tap i ∈ S
  · have same : S = (rep i).toFinset := by
      ext a
      rw [List.mem_toFinset]
      refine ⟨sub a,?_⟩
      intro h
      rcases List.mem_append.mp h with before|extra
      · exact pick a before
      · have ha : a = tap i := by simpa using extra
        exact ha.symm ▸ used
    rw [same] at run
    by_cases z : i=0
    · subst i
      exact difficult k (by omega) run
    · exact easilyCut i z k (by omega) run
  · have raw : ∀ w ∈ S, w ∈ inputs := by
      intro w hw
      rcases List.mem_append.mp (sub w hw) with h|h
      · exact h
      · have eq : w=tap i := by simpa using h
        exact (used (eq ▸ hw)).elim
    rw [orbitAllInputs run raw] at run
    exact rootSImpossible k (by omega) run

theorem projectedFloor (v : Fin 10) (avoid : v ≠ 6)
    (difficult : Impossible true graph 14 (rep 0).toFinset) :
    Lower true (projectedInputs v) graph 15 := by
  obtain ⟨j,p,ok⟩ := projectedMaps v avoid
  have plain : ∀ w : Fin 10, (projectedInputs w).all plainWord = true := by decide +kernel
  exact lower_map ok graph_proper (by decide +kernel) (plain v) graph_proper (repFloor j difficult)

end PEqualNP.Outside.L_meta_4813_aux.PetersenProductFloor
namespace PEqualNP.Outside.L_meta_4813_aux.Certificate.Extended
open PEqualNP.CircuitLowerBounds
def supplied := PEqualNP.Outside.L_meta_4813_aux.Bound.pin 0 &&&
  PEqualNP.Outside.L_meta_4813_aux.Bound.pin 2
def extraInitial := initial ++ [supplied]

end PEqualNP.Outside.L_meta_4813_aux.Certificate.Extended

namespace PEqualNP.Outside.L_meta_4813_aux.PetersenSignedHint
open PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_4813_aux.Certificate
open PEqualNP.Outside.L_meta_4813_aux.Bound

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem binary_bound {k S} (run : Extended.Live true Extended.target k S)
    (raw : ∀ z ∈ S, z ∈ Extended.extraInitial) : 17 ≤ k := by
  classical
  by_cases hh : Extended.supplied ∈ S
  · have diff : Extended.bit 128 Extended.target ≠ Extended.bit 640 Extended.target := by decide +kernel
    obtain ⟨a,ha,ne⟩ := Extended.live_row_difference run diff
    have checked : Extended.extraInitial.all (fun a =>
        (Extended.bit 128 a == Extended.bit 640 a) || (a == pin 0)) = true := by decide +kernel
    have h := List.all_eq_true.mp checked a (raw a ha)
    simp only [Bool.or_eq_true,beq_iff_eq] at h
    have eq := h.resolve_left ne
    have h0 : pin 0 ∈ S := eq ▸ ha
    have different : pin 0 ≠ Extended.supplied := by decide +kernel
    let rest := (S.erase (pin 0)).erase Extended.supplied
    let front := pin 0 :: Extended.supplied :: rest.toList
    have nd : front.Nodup := by
      simp [front,rest,different,Finset.nodup_toList]
    have hs : front.toFinset = S := by
      ext z
      simp only [front,rest,List.toFinset_cons,Finset.toList_toFinset,Finset.mem_insert,Finset.mem_erase]
      by_cases h₀ : z = pin 0
      · simpa [h₀] using h0
      · by_cases h₁ : z = Extended.supplied
        · simpa [h₁] using hh
        · simp [h₀,h₁]
    have hrun := Extended.list_run run front nd hs
    have same : restrictRows (morph 0) (Extended.observe Extended.target) = observe graph := funext (morphGoal 0)
    have hzero : restrictRows (morph 0) (Extended.observe Extended.supplied) = fun _ => false := by
      funext r
      change Extended.bit (morph 0 r) Extended.supplied = false
      have bf := morphPin 0 0 r
      rw [destSelf] at bf
      have b : Extended.bit (morph 0 r) (pin 0) = false := by simpa [bit,zero] using bf
      have hbit : (Extended.bit (morph 0 r) (pin 0) && Extended.bit (morph 0 r) (pin 2)) = false := by simp [b]
      simpa [Extended.supplied,Extended.bit] using hbit
    have supplyRoots : supply true (inputs.map observe) ((front.map Extended.observe).map (restrictRows (morph 0))) := by
      intro z hz
      obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hz
      obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hm
      have hr := raw w (hs ▸ List.mem_toFinset.mpr hw)
      change w ∈ Extended.initial ++ [Extended.supplied] at hr
      rcases List.mem_append.mp hr with un | bonus
      · obtain ⟨l,rfl⟩ := pinOfMem un
        exact availPin 0 l
      · obtain rfl : w = Extended.supplied := by simpa using bonus
        exact Or.inr (Or.inl ⟨false,hzero⟩)
    have need := projected_bound (morph 0) hrun (same ▸ observe_proper graph_proper)
      Reach.start supplyRoots (L:=15) (same ▸ nineFloor)
    have c₁ := restrictSelf (0 : Fin 10)
    have c₂ : Constant (restrictRows (morph 0) (Extended.observe Extended.supplied)) := ⟨false,hzero⟩
    have charge : 2 ≤ mass ((front.map Extended.observe).map (restrictRows (morph 0))) := by
      change 2 ≤ mass (restrictRows (morph 0) (Extended.observe (pin 0)) ::
        restrictRows (morph 0) (Extended.observe Extended.supplied) :: _)
      simp only [mass_cons,cost,if_pos c₁,if_pos c₂]
      omega
    omega
  · apply binaryFloor run
    intro a ha
    have h := raw a ha
    change a ∈ Extended.initial ++ [Extended.supplied] at h
    rcases List.mem_append.mp h with h | h
    · exact h
    · have eq : a = Extended.supplied := by simpa using h
      exact (hh (eq ▸ ha)).elim

end PEqualNP.Outside.L_meta_4813_aux.PetersenSignedHint
namespace PEqualNP.Outside.L_meta_4813_aux.Certificate.Extended
open PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_4813_aux.Bound

def tapVal (p : Fin 13) : Sig :=
  if h : p.val < 10 then pin ⟨p.val,h⟩
  else if p.val = 10 then supplied else if p.val = 11 then zero else one

def product (p q : Fin 13) := tapVal p &&& tapVal q
def normProduct (p q : Fin 13) := nrm true (product p q)

def physicalBank (p q : Fin 13) := extraInitial ++ [product p q]
def liveBank (p q : Fin 13) := extraInitial ++ [normProduct p q]

theorem physicalRun (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (p q : Fin 13) (correct : ∀ r : Row, C.eval ((physicalBank p q).map (bit r)) = bit r target) :
    ∃ k S, k ≤ C.gates.countP (fun g => !isNot g) ∧ Live true target k S ∧
      ∀ w ∈ S, w ∈ liveBank p q := by
  have he : (execute C.gates (physicalBank p q)).getD C.output zero = target := by
    apply bit_ext
    intro r
    rw [←b_read,execute_bits _ _ _ (fun g hg => (legal g hg).1)]
    exact correct r
  have hp : proper target := by unfold proper; decide +kernel
  have out := get_rep (u:=true) (execute C.gates (physicalBank p q)) C.output
  rw [he] at out
  unfold Repr at out
  rw [nrm_id (show bit 0 target=false by decide +kernel)] at out
  obtain ⟨k,S,hk,run,sub⟩ := extract C.gates (physicalBank p q) legal (u:=true) (by simp) hp
    (out.resolve_right (fun h => h hp))
  have plain : extraInitial.all plainWord = true := by decide +kernel
  simp only [physicalBank,List.map_append,List.map_cons,List.map_nil,nrm_map plain] at sub
  exact ⟨k,S,hk,run,sub⟩

theorem nonzeroLive {k S} (run : Live true target k S) : zero ∉ S := by
  intro h
  exact (live_proper run zero h).1 rfl

end PEqualNP.Outside.L_meta_4813_aux.Certificate.Extended

namespace PEqualNP.Outside.L_meta_4813_aux.PetersenProduct4813Full
open PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_4813_aux.Certificate
open PEqualNP.Outside.L_meta_4813_aux.Bound
open PetersenProductFloor

def nineTap (v : Fin 10) (p : Fin 13) : Sig :=
  if h : p.val < 10 then dest v ⟨p.val,h⟩
  else if p.val = 10 then dest v 0 &&& dest v 2 else if p.val = 11 then zero else one

theorem tapBit (v : Fin 10) (p : Fin 13) (r : Row) :
    Extended.bit (morph v r) (Extended.tapVal p) = bit r (nineTap v p) := by
  by_cases h : p.val < 10
  · simpa [Extended.tapVal,nineTap,h] using morphPin v ⟨p.val,h⟩ r
  · by_cases hs : p.val = 10
    · simp only [Extended.tapVal,nineTap,dif_neg h,if_pos hs,Extended.supplied,
        Extended.bit,bit,BitVec.getLsbD_and]
      change (Extended.bit (morph v r) (pin 0) && Extended.bit (morph v r) (pin 2)) =
        (bit r (dest v 0) && bit r (dest v 2))
      rw [morphPin,morphPin]
    · by_cases hx : p.val=11
      · simp [Extended.tapVal,nineTap,h,hs,hx,Extended.bit,bit,Extended.zero,zero]
      · simp [Extended.tapVal,nineTap,h,hs,hx,Extended.bit,bit,Extended.one,one,(morph v r).isLt,r.isLt]

def projectedProduct (v : Fin 10) (p q : Fin 13) :=
  let word := nineTap v p &&& nineTap v q
  if Extended.bit 0 (Extended.product p q) then ~~~word else word

theorem productBit (v : Fin 10) (p q : Fin 13) (r : Row) :
    Extended.bit (morph v r) (Extended.normProduct p q) = bit r (projectedProduct v p q) := by
  have eq : Extended.bit (morph v r) (Extended.product p q) = bit r (nineTap v p &&& nineTap v q) := by
    change ((Extended.tapVal p &&& Extended.tapVal q).getLsbD (morph v r).val) = _
    simp only [bit,BitVec.getLsbD_and]
    exact congrArg₂ Bool.and (tapBit v p r) (tapBit v q r)
  cases h : Extended.bit 0 (Extended.product p q) with
  | false => simpa [Extended.normProduct,Extended.nrm,projectedProduct,h] using eq
  | true => simpa [Extended.normProduct,Extended.nrm,projectedProduct,h,Extended.neg,
      Extended.bit,bit,BitVec.getLsbD_not,(morph v r).isLt,r.isLt] using congrArg Bool.not eq

def anchorData : Array (Nat × Nat × Nat) := #[(0,0,0),(0,64,576),(0,128,640),(0,128,640),(0,128,640),(0,128,640),(0,128,640),(0,128,640),(0,128,640),(0,128,640),(0,0,0),(0,0,0),(0,0,0),(0,64,576),(0,0,0),(1,512,640),(1,512,640),(1,512,640),(1,512,640),(1,512,640),(1,512,640),(1,512,640),(1,512,640),(0,128,640),(0,0,0),(0,0,0),(0,128,640),(1,512,640),(0,0,0),(2,128,160),(2,128,160),(2,128,160),(2,128,160),(2,128,160),(2,128,160),(2,128,160),(0,0,0),(0,0,0),(0,0,0),(0,128,640),(1,512,640),(2,128,160),(0,0,0),(3,32,288),(3,32,288),(3,32,288),(3,32,288),(3,32,288),(3,32,288),(0,128,640),(0,0,0),(0,0,0),(0,128,640),(1,512,640),(2,128,160),(3,32,288),(0,0,0),(4,512,576),(4,512,576),(4,512,576),(4,512,576),(4,512,576),(0,128,640),(0,0,0),(0,0,0),(0,128,640),(1,512,640),(2,128,160),(3,32,288),(4,512,576),(0,0,0),(5,512,528),(5,512,528),(5,512,528),(5,512,528),(0,128,640),(0,0,0),(0,0,0),(0,128,640),(1,512,640),(2,128,160),(3,32,288),(4,512,576),(5,512,528),(0,0,0),(7,32,33),(8,256,264),(9,64,66),(0,128,640),(0,0,0),(0,0,0),(0,128,640),(1,512,640),(2,128,160),(3,32,288),(4,512,576),(5,512,528),(7,32,33),(0,0,0),(7,32,33),(7,32,33),(0,128,640),(0,0,0),(0,0,0),(0,128,640),(1,512,640),(2,128,160),(3,32,288),(4,512,576),(5,512,528),(8,256,264),(7,32,33),(0,0,0),(8,256,264),(0,128,640),(0,0,0),(0,0,0),(0,128,640),(1,512,640),(2,128,160),(3,32,288),(4,512,576),(5,512,528),(9,64,66),(7,32,33),(8,256,264),(0,0,0),(0,128,640),(0,0,0),(0,0,0),(0,0,0),(0,128,640),(0,0,0),(0,128,640),(0,128,640),(0,128,640),(0,128,640),(0,128,640),(0,128,640),(0,128,640),(0,0,0),(0,0,0),(0,0,0),(0,0,0),(0,0,0),(0,0,0),(0,0,0),(0,0,0),(0,0,0),(0,0,0),(0,0,0),(0,0,0),(0,0,0),(0,0,0),(0,0,0),(0,0,0),(0,0,0),(0,0,0),(0,0,0),(0,0,0),(0,0,0),(0,0,0),(0,0,0),(0,0,0),(0,0,0),(0,0,0),(0,0,0),(0,0,0),(0,0,0)]
def data (p q : Fin 13) := anchorData.getD (13*p.val+q.val) (0,0,0)
def vertex (p q : Fin 13) : Fin 10 := Fin.ofNat 10 (data p q).1
def rowLo (p q : Fin 13) : Extended.Row := Fin.ofNat 1024 (data p q).2.1
def rowHi (p q : Fin 13) : Extended.Row := Fin.ofNat 1024 (data p q).2.2

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem anchorFacts : ∀ p q : Fin 13,
    Extended.normProduct p q ∈ Extended.extraInitial ∨ Extended.normProduct p q = Extended.zero ∨
    (vertex p q ≠ 6 ∧ pin (vertex p q) ≠ Extended.normProduct p q ∧
     projectedProduct (vertex p q) p q = zero ∧
     Extended.bit (rowLo p q) Extended.target ≠ Extended.bit (rowHi p q) Extended.target ∧
     (Extended.liveBank p q).all (fun a =>
       (Extended.bit (rowLo p q) a == Extended.bit (rowHi p q) a) || (a == pin (vertex p q))) = true) := by
  decide +kernel

theorem twoProductFloor (p q : Fin 13) {k S} (run : Extended.Live true Extended.target k S)
    (sub : ∀ a ∈ S, a ∈ Extended.liveBank p q)
    (difficult : Impossible true graph 14 (rep 0).toFinset) : 17 ≤ k := by
  classical
  let b := Extended.normProduct p q
  have base (notnew : b ∉ S ∨ b ∈ Extended.extraInitial) : 17 ≤ k := by
    apply PetersenSignedHint.binary_bound run
    intro a ha
    rcases List.mem_append.mp (sub a ha) with l|r
    · exact l
    · have e : a=b := by simpa [b] using r
      subst a
      exact notnew.resolve_left (fun h => h ha)
  by_cases live : b ∈ S
  · rcases anchorFacts p q with duplicate|z|facts
    · exact base (Or.inr duplicate)
    · exact (Extended.nonzeroLive run (z ▸ live)).elim
    · obtain ⟨avoid,distinct,dead,diff,check⟩ := facts
      let v := vertex p q
      obtain ⟨a,ha,neq⟩ := Extended.live_row_difference run diff
      have h := List.all_eq_true.mp check a (sub a ha)
      simp only [Bool.or_eq_true,beq_iff_eq] at h
      have hv : pin v ∈ S := (h.resolve_left neq) ▸ ha
      let rest := (S.erase (pin v)).erase b
      let front := pin v :: b :: rest.toList
      have nd : front.Nodup := by simp [front,rest,distinct,v,b]
      have hs : front.toFinset = S := by
        ext w
        simp only [front,rest,List.toFinset_cons,Finset.toList_toFinset,Finset.mem_insert,Finset.mem_erase]
        by_cases h0 : w=pin v
        · simpa [h0] using hv
        · by_cases h1 : w=b
          · simpa [h1] using live
          · simp [h0,h1]
      have hrun := Extended.list_run run front nd hs
      have same : restrictRows (morph v) (Extended.observe Extended.target) = observe graph := funext (morphGoal v)
      have zeroB : restrictRows (morph v) (Extended.observe b) = fun _ => false := by
        funext r
        change Extended.bit (morph v r) (Extended.normProduct p q) = false
        rw [productBit,dead]
        simp [bit,zero]
      have avail : supply true ((projectedInputs v).map observe)
          ((front.map Extended.observe).map (restrictRows (morph v))) := by
        intro x hx
        obtain ⟨_,hw,rfl⟩ := List.mem_map.mp hx
        obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hw
        have mem := sub w (hs ▸ List.mem_toFinset.mpr hw)
        change w ∈ (Extended.initial ++ [Extended.supplied]) ++ [b] at mem
        rcases List.mem_append.mp mem with before|last
        · rcases List.mem_append.mp before with raw|bonus
          · obtain ⟨j,rfl⟩ := pinOfMem raw
            rw [restrictPin]
            rcases destMem v j with z|r
            · rw [z]
              exact Or.inr (Or.inl ⟨false,funext fun a => by simp [observe,bit,zero]⟩)
            · exact Or.inl (List.mem_map.mpr ⟨_,List.mem_append_left _ r,rfl⟩)
          · obtain rfl : w=Extended.supplied := by simpa using bonus
            have e : restrictRows (morph v) (Extended.observe Extended.supplied) =
                observe (dest v 0 &&& dest v 2) := by
              funext r
              exact (tapBit v 10 r)
            rw [e]
            exact Or.inl (List.mem_map.mpr ⟨_,List.mem_append_right _ (by simp),rfl⟩)
        · obtain rfl : w=b := by simpa using last
          exact Or.inr (Or.inl ⟨false,zeroB⟩)
      have bound := projected_bound (morph v) hrun (same ▸ observe_proper graph_proper)
        Reach.start avail (L:=15) (same ▸ projectedFloor v avoid difficult)
      have c1 := restrictSelf v
      have c2 : Constant (restrictRows (morph v) (Extended.observe b)) := ⟨false,zeroB⟩
      have charge : 2 ≤ mass ((front.map Extended.observe).map (restrictRows (morph v))) := by
        change 2 ≤ mass (restrictRows (morph v) (Extended.observe (pin v)) ::
          restrictRows (morph v) (Extended.observe b) :: _)
        simp only [mass_cons,cost,if_pos c1,if_pos c2]
        omega
      omega
  · exact base (Or.inl live)

end PEqualNP.Outside.L_meta_4813_aux.PetersenProduct4813Full
namespace PEqualNP.Outside.L_meta_4813_aux.Certificate.Extended
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_4813_aux.Bound

def quietTap (p : Fin 13) : Sig :=
  if h : p.val < 10 then pin ⟨p.val,h⟩ else if p.val=12 then one else zero

def quietProduct (p q : Fin 13) := quietTap p &&& quietTap q
def quietBank (p q : Fin 13) := initial ++ [zero,quietProduct p q]

theorem quietRun (C : Circuit) (legal : FanInTwo C) (mono : Monotone2 C)
    (p q : Fin 13) (correct : ∀ r, C.eval ((quietBank p q).map (bit r)) = bit r target) :
    ∃ k S, k ≤ C.gates.countP (fun g => !isNot g) ∧ Live false target k S ∧
      ∀ w ∈ S, w ∈ quietBank p q := by
  have he : (execute C.gates (quietBank p q)).getD C.output zero = target := by
    apply bit_ext
    intro r
    rw [←b_read,execute_bits _ _ _ (fun g hg => (legal g hg).1)]
    exact correct r
  have hp : proper target := by unfold proper; decide +kernel
  have out := get_rep (u:=false) (execute C.gates (quietBank p q)) C.output
  rw [he] at out
  have hn : ∀ g ∈ C.gates, isNot g=false := by
    intro g hg
    have op := (mono g hg).1
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at op
    rcases op with h|h <;> simp [isNot,h]
  obtain ⟨k,S,hk,run,sub⟩ := extract C.gates (quietBank p q) legal (u:=false) (fun _ => hn) hp
    (out.resolve_right (fun h => h hp))
  exact ⟨k,S,hk,run,fun w hw => by simpa [nrm] using sub w hw⟩

theorem excludesConstants {k S} (run : Live false target k S) (w) (hw : w ∈ S) : w ≠ zero ∧ w ≠ one := live_proper run w hw
end PEqualNP.Outside.L_meta_4813_aux.Certificate.Extended

namespace PEqualNP.Outside.L_meta_4813_aux.Bound
open PEqualNP.Outside.L_meta_4813_aux.Certificate
end PEqualNP.Outside.L_meta_4813_aux.Bound

namespace PEqualNP.Outside.L_meta_4813_aux.PetersenQuiet4813
open PEqualNP.Outside.L_meta_4813_aux.Certificate PEqualNP.Outside.L_meta_4813_aux.Bound
open PetersenProduct4813Full

def quietProjectedTap (v : Fin 10) (p : Fin 13) : Sig :=
  if h : p.val < 10 then dest v ⟨p.val,h⟩ else if p.val=12 then one else zero

theorem quietBit (v : Fin 10) (p : Fin 13) (r : Row) :
    Extended.bit (morph v r) (Extended.quietTap p) = bit r (quietProjectedTap v p) := by
  by_cases h : p.val < 10
  · simpa [Extended.quietTap,quietProjectedTap,h] using morphPin v ⟨p.val,h⟩ r
  · by_cases h1 : p.val=12 <;> simp [Extended.quietTap,quietProjectedTap,h,h1,Extended.bit,bit,
      Extended.one,one,Extended.zero,zero,(morph v r).isLt,r.isLt]

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem quietFacts : ∀ p q : Fin 13,
    Extended.quietProduct p q ∈ Extended.initial ∨ Extended.quietProduct p q = Extended.zero ∨
    Extended.quietProduct p q = Extended.one ∨
    (pin (vertex p q) ≠ Extended.quietProduct p q ∧
     quietProjectedTap (vertex p q) p &&& quietProjectedTap (vertex p q) q = zero ∧
     Extended.bit (rowLo p q) Extended.target ≠ Extended.bit (rowHi p q) Extended.target ∧
     (Extended.quietBank p q).all (fun a =>
       (Extended.bit (rowLo p q) a == Extended.bit (rowHi p q) a) || (a == pin (vertex p q))) = true) := by
  decide +kernel

theorem quietFloor (p q : Fin 13) {k S} (run : Extended.Live false Extended.target k S)
    (sub : ∀ a ∈ S, a ∈ Extended.quietBank p q) (floor : Lower false inputs graph 16) : 18 ≤ k := by
  classical
  let b := Extended.quietProduct p q
  have base (absent : b ∉ S ∨ b ∈ Extended.initial) : 18 ≤ k := by
    apply binaryFloorOf floor run
    intro w hw
    rcases List.mem_append.mp (sub w hw) with raw|last
    · exact raw
    · have e : w=Extended.zero ∨ w=b := by simpa [b] using last
      rcases e with rfl|rfl
      · exact ((Extended.excludesConstants run _ hw).1 rfl).elim
      · exact absent.resolve_left (fun h => h hw)
  by_cases live : b ∈ S
  · rcases quietFacts p q with dup|z|one|facts
    · exact base (Or.inr dup)
    · exact ((Extended.excludesConstants run b live).1 z).elim
    · exact ((Extended.excludesConstants run b live).2 one).elim
    · obtain ⟨distinct,dead,diff,check⟩ := facts
      let v := vertex p q
      obtain ⟨a,ha,neq⟩ := Extended.live_row_difference run diff
      have h := List.all_eq_true.mp check a (sub a ha)
      simp only [Bool.or_eq_true,beq_iff_eq] at h
      have hv : pin v ∈ S := (h.resolve_left neq) ▸ ha
      let rest := (S.erase (pin v)).erase b
      let front := pin v :: b :: rest.toList
      have nd : front.Nodup := by simp [front,rest,distinct,v,b]
      have hs : front.toFinset = S := by
        ext w
        simp only [front,rest,List.toFinset_cons,Finset.toList_toFinset,Finset.mem_insert,Finset.mem_erase]
        by_cases h0 : w=pin v
        · simpa [h0] using hv
        · by_cases h1 : w=b
          · simpa [h1] using live
          · simp [h0,h1]
      have hrun := Extended.list_run run front nd hs
      have same : restrictRows (morph v) (Extended.observe Extended.target) = observe graph := funext (morphGoal v)
      have zeroB : restrictRows (morph v) (Extended.observe b) = fun _ => false := by
        funext r
        change (Extended.quietTap p &&& Extended.quietTap q).getLsbD (morph v r).val = false
        rw [BitVec.getLsbD_and]
        change (Extended.bit (morph v r) (Extended.quietTap p) && Extended.bit (morph v r) (Extended.quietTap q)) = false
        rw [quietBit,quietBit]
        change ((quietProjectedTap v p).getLsbD r.val && (quietProjectedTap v q).getLsbD r.val) = false
        rw [←BitVec.getLsbD_and,dead]
        simp [zero]
      have avail : supply false (inputs.map observe) ((front.map Extended.observe).map (restrictRows (morph v))) := by
        intro t ht
        obtain ⟨_,hw,rfl⟩ := List.mem_map.mp ht
        obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hw
        have member := hs ▸ List.mem_toFinset.mpr hw
        rcases List.mem_append.mp (sub w member) with raw|last
        · obtain ⟨j,rfl⟩ := pinOfMem raw
          exact availPin v j
        · have e : w=Extended.zero ∨ w=b := by simpa [b] using last
          rcases e with rfl|rfl
          · exact ((Extended.excludesConstants run _ member).1 rfl).elim
          · exact Or.inr (Or.inl ⟨false,zeroB⟩)
      have bound := projected_bound (morph v) hrun (same ▸ observe_proper graph_proper)
        Reach.start avail (L:=16) (same ▸ floor)
      have c1 := restrictSelf v
      have c2 : Constant (restrictRows (morph v) (Extended.observe b)) := ⟨false,zeroB⟩
      have charge : 2 ≤ mass ((front.map Extended.observe).map (restrictRows (morph v))) := by
        change 2 ≤ mass (restrictRows (morph v) (Extended.observe (pin v)) ::
          restrictRows (morph v) (Extended.observe b) :: _)
        simp only [mass_cons,cost,if_pos c1,if_pos c2]
        omega
      omega
  · exact base (Or.inl live)

end PEqualNP.Outside.L_meta_4813_aux.PetersenQuiet4813
namespace PEqualNP.Outside.L_meta_4813_aux.Monotonicity

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl step x := rfl

theorem and_mono (a a' b b' : Bool) (h1 : a ≤ a') (h2 : b ≤ b') : (a && b) ≤ (a' && b') := by
  revert h1 h2
  cases a <;> cases a' <;> cases b <;> cases b' <;> decide

theorem or_mono (a a' b b' : Bool) (h1 : a ≤ a') (h2 : b ≤ b') : (a || b) ≤ (a' || b') := by
  revert h1 h2
  cases a <;> cases a' <;> cases b <;> cases b' <;> decide

theorem all_mono (l : List ℕ) (f f' : ℕ → Bool) (h : ∀ i, f i ≤ f' i) :
    (l.map f).all id ≤ (l.map f').all id := by
  induction l with
  | nil => exact le_refl _
  | cons a l ih =>
    simp only [List.map_cons, List.all_cons, id]
    exact and_mono _ _ _ _ (h a) ih

theorem any_mono (l : List ℕ) (f f' : ℕ → Bool) (h : ∀ i, f i ≤ f' i) :
    (l.map f).any id ≤ (l.map f').any id := by
  induction l with
  | nil => exact le_refl _
  | cons a l ih =>
    simp only [List.map_cons, List.any_cons, id]
    exact or_mono _ _ _ _ (h a) ih

theorem getD_snoc (W : List Bool) (v : Bool) (i : ℕ) :
    (W ++ [v]).getD i false = if i < W.length then W.getD i false else if i = W.length then v else false := by
  split_ifs with h1 h2
  · exact List.getD_append _ _ _ _ h1
  · subst h2
    simp
  · rw [List.getD_eq_default]
    simp
    omega

def R (W W' : List Bool) : Prop :=
  W.length = W'.length ∧ ∀ i, W.getD i false ≤ W'.getD i false

theorem step_R (W W' : List Bool) (g : Gate) (hg : g.op = GateOp.and ∨ g.op = GateOp.or)
    (h : R W W') : R (step W g) (step W' g) := by
  obtain ⟨hl, hle⟩ := h
  have hv : g.op.eval (g.inputs.map fun i => W.getD i false) ≤
      g.op.eval (g.inputs.map fun i => W'.getD i false) := by
    rcases hg with hg | hg <;> rw [hg] <;> simp only [GateOp.eval]
    · exact all_mono _ _ _ hle
    · exact any_mono _ _ _ hle
  refine ⟨by simp [step, hl], fun i => ?_⟩
  simp only [step, getD_snoc, hl]
  split_ifs
  · exact hle i
  · exact hv
  · exact le_refl _

theorem fold_R (gs : List Gate) (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ W W' : List Bool, R W W' → R (gs.foldl step W) (gs.foldl step W') := by
  induction gs with
  | nil => intro W W' h; exact h
  | cons g gs ih =>
    intro W W' h
    simp only [List.foldl_cons]
    exact ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg')) _ _
      (step_R W W' g (hgs g List.mem_cons_self) h)

theorem R_append {l1 l1' l2 l2' : List Bool} (h1 : R l1 l1') (h2 : R l2 l2') :
    R (l1 ++ l2) (l1' ++ l2') := by
  obtain ⟨hl1, h1⟩ := h1
  obtain ⟨hl2, h2⟩ := h2
  refine ⟨by simp [hl1, hl2], fun i => ?_⟩
  by_cases hi : i < l1.length
  · rw [List.getD_append _ _ _ _ hi, List.getD_append _ _ _ _ (hl1 ▸ hi)]
    exact h1 i
  · have hi' : l1.length ≤ i := by omega
    rw [List.getD_append_right _ _ _ _ hi', List.getD_append_right _ _ _ _ (hl1 ▸ hi'), hl1]
    exact h2 _

theorem R_ofFn {n : ℕ} (f g : Fin n → Bool) (h : ∀ i, f i ≤ g i) :
    R (List.ofFn f) (List.ofFn g) := by
  refine ⟨by simp, fun i => ?_⟩
  by_cases hi : i < n
  · rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getD_eq_getElem _ _ (by simpa using hi)]
    simp only [List.getElem_ofFn]
    exact h ⟨i, hi⟩
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

theorem eval_mono (C : Circuit) (hm : PEqualNP.MetaComplexity.Monotone2 C) (l l' : List Bool)
    (h : R l l') : C.eval l ≤ C.eval l' := by
  have hops : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or := by
    intro g hg
    have := (hm g hg).1
    simpa using this
  show (C.wires l).getD C.output false ≤ (C.wires l').getD C.output false
  rw [wires_eq, wires_eq]
  exact (fold_R C.gates hops _ _ h).2 C.output

end PEqualNP.Outside.L_meta_4813_aux.Monotonicity
namespace PEqualNP.Outside.L_meta_4813_aux.Petersen7217
abbrev V := Fin 10
def nums : List ℕ := [1,12,23,34,40,5,16,27,38,49,57,79,96,68,85]
def pet (x : V → Bool) := nums.any fun e => x (Fin.ofNat 10 (e/10)) && x (Fin.ofNat 10 (e%10))
end PEqualNP.Outside.L_meta_4813_aux.Petersen7217
namespace PEqualNP.Outside.L_meta_4813_aux.PetersenMonotoneHint
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_4813_aux.Petersen7217
open PEqualNP.Outside.L_meta_4813_aux.Monotonicity

abbrev Point := V → Bool
def frame (x : Point) (b : Bool) := List.ofFn x ++ [b]

private theorem oneRel {a b : Bool} (h : a ≤ b) : R [a] [b] := by
  refine ⟨rfl, ?_⟩
  intro i
  cases i with
  | zero => exact h
  | succ i =>
    rw [List.getD_eq_default _ _ (by simp), List.getD_eq_default _ _ (by simp)] <;> exact le_refl _

private theorem smaller (C : Circuit) (hm : Monotone2 C) {x y : Point} {a b : Bool}
    (xy : ∀ i, x i ≤ y i) (ab : a ≤ b) :
    C.eval (frame x a) ≤ C.eval (frame y b) :=
  eval_mono C hm _ _ (R_append (R_ofFn x y xy) (oneRel ab))

private def ends (e : ℕ) (i : V) :=
  decide (i = Fin.ofNat 10 (e/10) ∨ i = Fin.ofNat 10 (e%10))

private theorem edgeFacts : ∀ i : Fin nums.length,
    pet (ends (nums.get i)) = true ∧
      (ends (nums.get i) 0 && ends (nums.get i) 2) = false := by
  decide +kernel

/-- Every minimal positive assignment is an edge, so the free product
can be fixed to false throughout a monotone circuit for Petersen. -/
theorem remove_product (C : Circuit) (hm : Monotone2 C)
    (hc : ∀ x : Point, C.eval (frame x (x 0 && x 2)) = pet x) :
    ∀ x : Point, C.eval (frame x false) = pet x := by
  intro x
  cases hp : pet x with
  | false =>
    have order := smaller C hm (x:=x) (y:=x) (a:=false) (b:=x 0 && x 2)
      (fun _ => le_refl _) (Bool.false_le _)
    rw [hc,hp] at order
    exact le_antisymm order (Bool.false_le _)
  | true =>
    obtain ⟨e,he,hon⟩ := List.any_eq_true.mp hp
    obtain ⟨i,rfl⟩ := List.mem_iff_get.mp he
    obtain ⟨hy,hz⟩ := edgeFacts i
    have hxy : ∀ k, ends (nums.get i) k ≤ x k := by
      intro k
      simp only [Bool.and_eq_true] at hon
      obtain ⟨ha,hb⟩ := hon
      unfold ends
      by_cases h : k = Fin.ofNat 10 (nums.get i/10) ∨ k = Fin.ofNat 10 (nums.get i%10)
      · rcases h with rfl | rfl <;> simp [ha,hb]
      · simp [h]
    have low := hc (ends (nums.get i))
    rw [hz,hy] at low
    have order := smaller C hm (a:=false) (b:=false) hxy (le_refl _)
    rw [low] at order
    exact Bool.eq_true_of_true_le order

end PEqualNP.Outside.L_meta_4813_aux.PetersenMonotoneHint

namespace PEqualNP.Outside.L_meta_4813_aux.PetersenProductMono4813
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_4813_aux.Petersen7217
open PEqualNP.Outside.L_meta_4813_aux.Certificate
def base (x : Fin 10 → Bool) := List.ofFn x ++ [x 0 && x 2]
def extra (ls : List (Fin 12)) (x : Fin 10 → Bool) :=
  GateOp.and.eval (ls.map fun a => (base x).getD a.val false)

def quietBase (x : Fin 10 → Bool) := List.ofFn x ++ [false]
def quietExtra (ls : List (Fin 12)) (x : Fin 10 → Bool) :=
  GateOp.and.eval (ls.map fun a => (quietBase x).getD a.val false)

def quietPort (p : Fin 12) : Fin 13 := ⟨p.val,by omega⟩

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem portValue : ∀ j : Fin 12, ∀ r : Extended.Row,
    Extended.bit r (Extended.quietTap (quietPort j)) = (quietBase (Extended.assign r)).getD j.val false := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem fullBank : ∀ r : Extended.Row, (Extended.initial ++ [Extended.zero]).map (Extended.bit r) =
    quietBase (Extended.assign r) := by decide +kernel

theorem quietLayout (ls : List (Fin 12)) (sz : ls.length ≤ 2) : ∃ p q : Fin 13, ∀ r : Extended.Row,
    (Extended.quietBank p q).map (Extended.bit r) = quietBase (Extended.assign r) ++ [quietExtra ls (Extended.assign r)] := by
  have glue (p q : Fin 13) (r : Extended.Row) :
      (Extended.quietBank p q).map (Extended.bit r) =
        quietBase (Extended.assign r) ++ [Extended.bit r (Extended.quietTap p) && Extended.bit r (Extended.quietTap q)] := by
    change ((Extended.initial ++ [Extended.zero]) ++ [Extended.quietProduct p q]).map (Extended.bit r) = _
    simp only [List.map_append,fullBank,List.map_cons,List.map_nil,
      Extended.quietProduct,Extended.bit,BitVec.getLsbD_and]
  have neutral (r : Extended.Row) : Extended.bit r (Extended.quietTap 12) = true := by
    simp [Extended.quietTap,Extended.bit,Extended.one,r.isLt]
  cases ls with
  | nil =>
    refine ⟨12,12,fun r => ?_⟩
    rw [glue,neutral]
    rfl
  | cons a l =>
    cases l with
    | nil =>
      refine ⟨quietPort a,12,fun r => ?_⟩
      rw [glue,portValue,neutral]
      simp [quietExtra,GateOp.eval]
    | cons b l =>
      have empty : l=[] := by
        apply List.length_eq_zero_iff.mp
        simp only [List.length_cons] at sz
        omega
      subst l
      refine ⟨quietPort a,quietPort b,fun r => ?_⟩
      rw [glue,portValue,portValue]
      simp [quietExtra,GateOp.eval]

theorem afterMonotone (floor : Lower false inputs graph 16) (C : Circuit) (ls : List (Fin 12)) (hlen : ls.length ≤ 2)
    (hm : Monotone2 C) (legal : FanInTwo C) (small : C.size ≤ 17)
    (correct : ∀ x, C.eval (base x ++ [extra ls x]) = pet x) : False := by
  let g : Gate := ⟨.and,ls.map Fin.val⟩
  let B : Circuit := ⟨g::C.gates,C.output⟩
  have mono : Monotone2 B := by
    intro a ha
    rcases List.mem_cons.mp ha with rfl|ha
    · exact ⟨by simp [g],by simpa [g] using hlen⟩
    · exact hm a ha
  have original (x) : B.eval (PetersenMonotoneHint.frame x (x 0 && x 2)) = pet x := by
    change C.eval (base x ++ [g.op.eval (g.inputs.map fun i => (base x).getD i false)]) = _
    simpa only [g,extra,List.map_map,Function.comp_def] using correct x
  have reduced := PetersenMonotoneHint.remove_product B mono original
  have after (x : Fin 10 → Bool) : C.eval (quietBase x ++ [quietExtra ls x]) = pet x := by
    have hh := reduced x
    change C.eval (quietBase x ++ [g.op.eval (g.inputs.map fun i => (quietBase x).getD i false)]) = _ at hh
    simpa only [g,quietExtra,List.map_map,Function.comp_def] using hh
  have agrees (x : Fin 10 → Bool) : pet x = Extended.f10 x := by
    simp [pet,nums,Extended.f10,List.any_cons,Bool.or_assoc]
  obtain ⟨p,q,hrow⟩ := quietLayout ls hlen
  have correctRows (r : Extended.Row) : C.eval ((Extended.quietBank p q).map (Extended.bit r)) = Extended.bit r Extended.target := by
    rw [hrow,after,agrees,Extended.rowTarget]
  obtain ⟨k,S,cap,run,sub⟩ := Extended.quietRun C legal hm p q correctRows
  have bound := PetersenQuiet4813.quietFloor p q run sub floor
  have len : C.gates.countP (fun g => !Extended.isNot g) ≤ C.gates.length := List.countP_le_length
  change C.gates.length ≤ 17 at small
  omega

end PEqualNP.Outside.L_meta_4813_aux.PetersenProductMono4813
namespace PEqualNP.Outside.L_meta_4813_aux.PetersenProduct4813Finish

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_4813_aux.Certificate
open PetersenProductMono4813

def port (p : Fin 12) : Fin 13 := ⟨p.val,by omega⟩

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem portValue : ∀ j : Fin 12, ∀ r : Extended.Row,
    Extended.bit r (Extended.tapVal (port j)) = (base (Extended.assign r)).getD j.val false := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem fullBank : ∀ r : Extended.Row, Extended.extraInitial.map (Extended.bit r) =
    base (Extended.assign r) := by decide +kernel

theorem layout (ls : List (Fin 12)) (sz : ls.length ≤ 2) : ∃ p q : Fin 13, ∀ r : Extended.Row,
    (Extended.physicalBank p q).map (Extended.bit r) = base (Extended.assign r) ++ [extra ls (Extended.assign r)] := by
  have glue (p q : Fin 13) (r : Extended.Row) :
      (Extended.physicalBank p q).map (Extended.bit r) =
        base (Extended.assign r) ++ [Extended.bit r (Extended.tapVal p) && Extended.bit r (Extended.tapVal q)] := by
    simp only [Extended.physicalBank,List.map_append,fullBank,List.map_cons,List.map_nil,
      Extended.product,Extended.bit,BitVec.getLsbD_and]
  have neutral (r : Extended.Row) : Extended.bit r (Extended.tapVal 12) = true := by
    simp [Extended.tapVal,Extended.bit,Extended.one,r.isLt]
  cases ls with
  | nil =>
    refine ⟨12,12,fun r => ?_⟩
    rw [glue,neutral]
    rfl
  | cons a l =>
    cases l with
    | nil =>
      refine ⟨port a,12,fun r => ?_⟩
      rw [glue,portValue,neutral]
      simp [extra,GateOp.eval]
    | cons b l =>
      have empty : l=[] := by
        apply List.length_eq_zero_iff.mp
        simp only [List.length_cons] at sz
        omega
      subst l
      refine ⟨port a,port b,fun r => ?_⟩
      rw [glue,portValue,portValue]
      simp [extra,GateOp.eval]

theorem compulsoryMono (C : Circuit) (ls : List (Fin 12)) (legal : FanInTwo C) (small : C.size ≤ 17)
    (sz : ls.length ≤ 2) (correct : ∀ x, C.eval (base x ++ [extra ls x]) = Extended.f10 x)
    (difficult : Impossible true graph 14 (PetersenProductFloor.rep 0).toFinset) : Monotone2 C := by
  obtain ⟨p,q,rows⟩ := layout ls sz
  have works (r : Extended.Row) : C.eval ((Extended.physicalBank p q).map (Extended.bit r)) =
      Extended.bit r Extended.target := by rw [rows,correct,Extended.rowTarget]
  obtain ⟨k,S,budget,run,sub⟩ := Extended.physicalRun C legal p q works
  have floor := PetersenProduct4813Full.twoProductFloor p q run sub difficult
  have split := List.length_eq_countP_add_countP (l:=C.gates) Extended.isNot
  change C.gates.length ≤ 17 at small
  have z : C.gates.countP Extended.isNot = 0 := by omega
  intro g hg
  obtain ⟨op,arity⟩ := legal g hg
  refine ⟨?_,arity⟩
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at op ⊢
  rcases op with h|h|h
  · exact Or.inl h
  · exact Or.inr h
  · have pos : 0 < C.gates.countP Extended.isNot :=
      List.countP_pos_iff.2 ⟨g,hg,by simp [Extended.isNot,h]⟩
    omega

theorem contradiction (C : Circuit) (ls : List (Fin 12)) (legal : FanInTwo C) (small : C.size ≤ 17)
    (sz : ls.length ≤ 2) (correct : ∀ x, C.eval (base x ++ [extra ls x]) = Extended.f10 x)
    (difficult : Impossible true graph 14 (PetersenProductFloor.rep 0).toFinset) : False := by
  have mono := compulsoryMono C ls legal small sz correct difficult
  apply PetersenProductMono4813.afterMonotone nineMonotone C ls sz mono legal small
  intro x
  rw [correct]
  simp [Extended.f10, PEqualNP.Outside.L_meta_4813_aux.Petersen7217.pet,
    PEqualNP.Outside.L_meta_4813_aux.Petersen7217.nums,List.any_cons,Bool.or_assoc]

end PEqualNP.Outside.L_meta_4813_aux.PetersenProduct4813Finish
theorem PEqualNP.Outside.L_meta_4813 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : List (Fin (12 : ℕ))),   PEqualNP.MetaComplexity.FanInTwo x1 →     x1.size ≤ (17 : ℕ) →       x2.length ≤ (2 : ℕ) →         ∃ (x6 : Fin (10 : ℕ) → Bool),           have x7 : List Bool := List.ofFn x6 ++ [x6 (0 : Fin (10 : ℕ)) && x6 (2 : Fin (10 : ℕ))];           x1.eval (x7 ++ [PEqualNP.CircuitLowerBounds.GateOp.and.eval (List.map (fun (x8 : Fin (12 : ℕ)) => x7.getD (↑x8) Bool.false) x2)]) ≠ (fun (x8 : Fin (10 : ℕ) → Bool) => x8 (0 : Fin (10 : ℕ)) && x8 (1 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (2 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (3 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (4 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (0 : Fin (10 : ℕ)) || x8 (0 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (5 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (7 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (9 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (6 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (8 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ))) x6 := by
  classical
  intro C ls legal small sz
  by_contra! correct
  exact PetersenProduct4813Finish.contradiction C ls legal small sz correct
    PEqualNP.Outside.L_meta_4813_aux.Certificate.fullInitialImpossible
